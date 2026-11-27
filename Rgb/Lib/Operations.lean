import Rgb.Lib.Refresh

/-!
# Inflate, burn and link

Single-asset operations of the IFA and BFA schemas. Each spends the wallet's own
state and needs no counterparty: it is broadcast at its end and settles with
confirmations.
* **inflate** (IFA): spends inflation rights, issues new supply to new colored
  outputs of the witness, and keeps the remaining allowance as change;
* **burn** (IFA, BFA): destroys an amount, recorded as `burnedAsset`; with change,
  a side transition first splits the inputs so that the burn spends exactly the
  burned amount;
* **link** (IFA, BFA): spends the link right and records the linked contract.

Allocations of other assets on the spent UTXOs move to change, as in a send.
-/

namespace Rgb.Lib

namespace Wallet

/-- The main transition of a single-asset operation (`MainTransition`). -/
inductive MainTransition where
  | inflate (amounts : List Nat)
  | burn (amount : Nat) (reason : Option Bytes)
  | link (linkedTo : String)
  deriving DecidableEq, Repr, Inhabited

/-- Build, commit, broadcast and record a single-asset operation. -/
def runOperation (w : Wallet) (world : World) (assetId : String) (need : AssignmentsCollection)
    (main : MainTransition) (feeRate minConfirmations : Nat) : Result (Wallet × World × Txid) := do
  let now := world.now
  let some cid := w.contractIdOf? assetId | throw (.assetNotFound assetId)
  let selected ← w.selectInputs assetId need w.inputUnspents
  let mut w := w
  -- inflation outputs: new colored addresses (never reused)
  let mut newOuts : List TxOut := []
  if let .inflate amounts := main then
    let btcIn := (selected.map (·.btcAmount)).sum
    for _ in amounts do
      let (s, w') := w.newColoredAddress
      w := w'
      newOuts := newOuts ++ [⟨(max (btcIn / amounts.length) (dustLimit s)).toUInt64, s⟩]
  let (changeScript, w') := w.coloredOutputAddress
  w := w'
  let (tx0, selected) ← w.buildColoredTx selected (⟨0, .opReturn none⟩ :: newOuts) changeScript feeRate
  let spent := selected.map (·.outpoint)
  let changeVout := if tx0.outputs.length > 1 + newOuts.length then some (1 + newOuts.length) else none
  let slot (k : Nat) : Result GraphSeal :=
    match changeVout with
    | some v => .ok (GraphSeal.witnessVout v.toUInt32 (now.toUInt64 * 17 + k.toUInt64))
    | none => match w.availableAllocations spent with
      | (t, _, _) :: _ => .ok (GraphSeal.ofOutpoint t.outpoint (now.toUInt64 * 17 + k.toUInt64))
      | [] => .error .insufficientAllocationSlots
  let states := spent.flatMap fun op => w.stashState cid op
  let amountOf (ty : AssignmentType) : Nat :=
    ((states.filter (·.1.ty == ty)).filterMap (·.2.amount?)).foldl (· + ·.toNat) 0
  let ofType (ty : AssignmentType) := (states.filter (·.1.ty == ty)).map (·.1)
  let mut ts : List Transition := []
  match main with
  | .inflate amounts =>
    let total := amounts.sum
    let left := amountOf Schemas.osInflation - total
    let s0 ← slot 0
    ts := [{ contractId := cid, transitionType := Schemas.tsInflation, inputs := ofType Schemas.osInflation
             metadata := OrdMap.ofList [(Schemas.msAllowedInflation, ⟨.amount left.toUInt64⟩)]
             globals := OrdMap.ofList [(Schemas.gsIssuedSupply, [⟨.amount total.toUInt64⟩])]
             assignments := OrdMap.ofList
               ([(Schemas.osAsset, .fungible (amounts.zipIdx.map fun (a, i) =>
                   (.revealed (GraphSeal.witnessVout (i + 1).toUInt32 (now.toUInt64 + i.toUInt64)), ⟨a.toUInt64⟩)))] ++
                (if left > 0 then [(Schemas.osInflation, .fungible [(.revealed s0, ⟨left.toUInt64⟩)])] else [])) }]
  | .burn amount reason =>
    let total := amountOf Schemas.osAsset
    let globals : GlobalState := OrdMap.ofList
      ([(Schemas.gsBurnedAsset, [⟨.amount amount.toUInt64⟩])] ++
       (reason.map fun r => (Schemas.gsBurnReason, [⟨.burnReason ⟨r⟩⟩])).toList)
    if total == amount then
      ts := [{ contractId := cid, transitionType := Schemas.tsBurn, inputs := ofType Schemas.osAsset, globals }]
    else
      -- split: the burned amount to a seal on the first spent outpoint, the rest to change
      let s0 ← slot 0
      let split : Transition :=
        { contractId := cid, transitionType := Schemas.tsTransfer, inputs := ofType Schemas.osAsset
          assignments := OrdMap.ofList [(Schemas.osAsset, .fungible
            [(.revealed (GraphSeal.ofOutpoint (spent.headD default) (now.toUInt64 * 3)), ⟨amount.toUInt64⟩),
             (.revealed s0, ⟨(total - amount).toUInt64⟩)])] }
      ts := [split, { contractId := cid, transitionType := Schemas.tsBurn, inputs := [⟨split.id, Schemas.osAsset, 0⟩]
                      globals }]
  | .link linkedTo =>
    ts := [{ contractId := cid, transitionType := Schemas.tsLink, inputs := ofType Schemas.osLink
             globals := OrdMap.ofList [(Schemas.gsLinkedToContract, [⟨.contractId (Digest.of "asset-id" [linkedTo])⟩])] }]
  -- same-asset state the main transition does not spend, and other contracts'
  -- allocations on the spent UTXOs, move to change
  let used := ts.flatMap (·.inputs)
  let mut k := 1
  for (opout, st) in states do
    if !used.contains opout then
      let s ← slot k
      k := k + 1
      let tt := ((w.stock.genesis? cid).bind fun g => (w.stock.rules? g.schemaId).bind fun r =>
        r.schema.defaultTransitionFor? opout.ty).getD Schemas.tsTransfer
      ts := ts ++ [{ contractId := cid, transitionType := tt, inputs := [opout]
                     assignments := OrdMap.ofList [(opout.ty, typedAssigns [(.revealed s, st)])] }]
  let mut bundles : List (ContractId × List Transition) := [(cid, ts)]
  for g in w.stock.geneses do
    if g.contractId != cid then
      let others := spent.flatMap fun op => w.stashState g.contractId op
      let mut moves : List Transition := []
      for (opout, st) in others do
        let s ← slot k
        k := k + 1
        let tt := ((w.stock.rules? g.schemaId).bind fun r => r.schema.defaultTransitionFor? opout.ty).getD Schemas.tsTransfer
        moves := moves ++ [{ contractId := g.contractId, transitionType := tt, inputs := [opout]
                             assignments := OrdMap.ofList [(opout.ty, typedAssigns [(.revealed s, st)])] }]
      if !moves.isEmpty then bundles := bundles ++ [(g.contractId, moves)]
  let fascia ← (commitBundles tx0 (bundles.map fun (c, ts) => (c, TransitionBundle.ofTransitions ts)) now.toUInt64).mapError
    fun e => .internal (reprStr e)
  let tx := fascia.sealWitness.tx
  let kind : TypeOfTransition := match main with
    | .inflate _ => .inflate | .burn .. => .burn | .link _ => .link
  let op : PendingOp := { txid := tx.txid, tx, fascia := some fascia, kind := some kind, minConfirmations }
  w := { w with pending := w.pending ++ [op] }
  w := saveTransfers w op [] .initiated
  -- the operation's own transfer row and asset transfer kind
  let bi := (w.db.batchByTxid? tx.txid false).map (·.idx) |>.getD 0
  let requested : Option Assignment := match main with
    | .burn a _ => some (.fungible a.toUInt64)
    | .link _ => some .linkRight
    | .inflate _ => none
  let setKind (a : DbAssetTransfer) : DbAssetTransfer :=
    if a.batchTransferIdx == bi && a.assetId == some assetId then { a with transitionType := some kind } else a
  w := { w with db := { w.db with assetTransfers := w.db.assetTransfers.map setKind } }
  if let some ra := requested then
    let ati := ((w.db.assetTransfersOf bi).find? (·.assetId == some assetId)).map (·.idx) |>.getD 0
    let (ti, db) := w.db.fresh
    w := { w with db := { db with transfers := db.transfers ++ [{ idx := ti, assetTransferIdx := ati, requestedAssignment := some ra }] } }
  -- inflation outputs are issued allocations of the wallet
  if let .inflate amounts := main then
    let newOps := (List.range amounts.length).map fun i => tx.outpoint (i + 1)
    let newIdx := (w.db.txos.filter fun t => newOps.contains t.outpoint).map (·.idx)
    let toIssue (c : DbColoring) : DbColoring :=
      if newIdx.contains c.txoIdx && c.type == .change then { c with type := .issue } else c
    w := { w with db := { w.db with colorings := w.db.colorings.map toIssue } }
  let (w2, world2) ← w.broadcastBatch world bi
  -- record the effects on the asset row
  let upd (a : DbAsset) : DbAsset :=
    if a.id != assetId then a else match main with
      | .inflate amounts => { a with knownCirculatingSupply := some ((a.knownCirculatingSupply.getD a.initialSupply) + amounts.sum) }
      | .link to => { a with linkedToContract := some to }
      | .burn .. => a
  return ({ w2 with db := { w2.db with assets := w2.db.assets.map upd } }, world2, tx.txid)

/-- `inflate`: issue more of an IFA asset by spending inflation rights. -/
def inflate (w : Wallet) (world : World) (o : Online) (assetId : String) (amounts : List Nat)
    (feeRate : Nat := 1) (minConfirmations : Nat := 1) : Result (Wallet × World × Txid) := do
  if w.keys.watchOnly then throw .watchOnly
  w.checkOnline o
  let a ← w.asset? assetId
  w.checkSchemaSupport a.schema
  if !a.schema.supportsInflation then throw (.unsupportedInflation a.schema)
  let total ← totalInflationAmount amounts (a.knownCirculatingSupply.getD a.initialSupply)
  if total == 0 then throw .noInflationAmounts
  checkFeeRate feeRate
  w.runOperation world assetId { inflation := total } (.inflate amounts) feeRate minConfirmations

/-- `burn`: destroy an amount of an IFA or BFA asset, with an optional 32-byte reason (hex). -/
def burn (w : Wallet) (world : World) (o : Online) (assetId : String) (amount : Nat)
    (reason : Option String := none) (feeRate : Nat := 1) (minConfirmations : Nat := 1) :
    Result (Wallet × World × Txid) := do
  if w.keys.watchOnly then throw .watchOnly
  w.checkOnline o
  let a ← w.asset? assetId
  w.checkSchemaSupport a.schema
  if !a.schema.supportsBurn then throw (.unsupportedBurn a.schema)
  if amount == 0 then throw .noBurnAmount
  let r ← match reason with
    | none => pure none
    | some h =>
      if !h.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) || h.length % 2 != 0 then
        throw (.invalidBurnReason s!"not a hex string: {h}")
      else if h.length != 64 then throw (.invalidBurnReason s!"expected 32 bytes, got {h.length / 2}")
      else pure (some (Bytes.ofString h |>.take 32))
  checkFeeRate feeRate
  w.runOperation world assetId { fungible := amount } (.burn amount r) feeRate minConfirmations

/-- `link`: spend the link right of an IFA or BFA asset, recording the linked contract. -/
def link (w : Wallet) (world : World) (o : Online) (assetId linkedTo : String) (skipContractChecks : Bool := false)
    (feeRate : Nat := 1) (minConfirmations : Nat := 1) : Result (Wallet × World × Txid) := do
  if w.keys.watchOnly then throw .watchOnly
  w.checkOnline o
  let a ← w.asset? assetId
  w.checkSchemaSupport a.schema
  if !a.schema.supportsLink then throw (.unsupportedLink a.schema)
  if !linkedTo.startsWith assetIdPrefix then throw (.invalidContractId linkedTo)
  if linkedTo == assetId then throw .cannotLinkToItself
  if !skipContractChecks then
    let some other := w.db.asset? linkedTo | throw (.unknownLinkedContract linkedTo)
    if other.linkedFromContract != some assetId then
      throw (.invalidLinkedContract linkedTo s!"it has not been issued linked from contract {assetId}")
  checkFeeRate feeRate
  w.runOperation world assetId { link := true } (.link linkedTo) feeRate minConfirmations

end Wallet

end Rgb.Lib
