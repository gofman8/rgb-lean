import Rgb.Lib.Refresh

/-!
# Inflate, burn, link and the begin of a mint

Single-asset operations of the IFA and BFA schemas. Each spends the wallet's own
state. A begin builds the witness transaction and saves the operation as
initiated, its inputs reserved; inflate, burn and link need no counterparty and
are broadcast at their end, then settle with confirmations.
* **inflate** (IFA): spends inflation rights, issues new supply to new colored
  outputs of the witness, and keeps the remaining allowance as change;
* **burn** (IFA, BFA): destroys an amount, recorded as `burnedAsset`; with change,
  a side transition first splits the inputs so that the burn spends exactly the
  burned amount;
* **link** (IFA, BFA): spends the link right and records the linked contract;
* **mint** (BFA): spends one mint right and assigns the minted amount to a
  recipient; its begin and end are in `Rgb.Lib.Mint`.

Allocations of other assets on the spent UTXOs move to change, as in a send; a
change destination takes at most one mint right of an asset.
-/

namespace Rgb.Lib

namespace Wallet

/-- The main transition of a single-asset operation (`MainTransition`). -/
inductive MainTransition where
  | inflate (amounts : List Nat)
  | burn (amount : Nat) (reason : Option Bytes)
  | link (linkedTo : String)
  /-- Mint the recipient's amount; its lock has to be included before bridge block `beforeBlock`. -/
  | mint (beforeBlock : Nat) (recipient : LocalRecipient)
  deriving DecidableEq, Repr, Inhabited

/-- The kind the operation's asset transfer records (`transition_type`). -/
def MainTransition.kind : MainTransition → TypeOfTransition
  | .inflate _ => .inflate
  | .burn .. => .burn
  | .link _ => .link
  | .mint .. => .mint

/-- Prepare a single-asset operation spending `selected` (`prepare_single_asset_psbt`) and save
it as initiated, its inputs reserved. Only a mint has a counterparty, hence a sender endpoint and
an operation key; none has an expiration. A change destination takes at most one mint right of
an asset. -/
def beginOperation (w : Wallet) (now : Nat) (assetId : String) (selected : List DbTxo)
    (main : MainTransition) (feeRate minConfirmations : Nat)
    (senderEndpoint : Option String := none) (opKey : Option ProxyCrypto.SecretKey := none) :
    Result (Wallet × PendingOp) := do
  let some cid := w.contractIdOf? assetId | throw (.assetNotFound assetId)
  let mut w := w
  -- outputs the operation creates: inflation outputs on fresh colored addresses (never reused),
  -- a mint's witness recipient
  let mut newOuts : List TxOut := []
  match main with
  | .inflate amounts =>
    let btcIn := (selected.map (·.btcAmount)).sum
    for _ in amounts do
      let (s, w') := w.newColoredAddress
      w := w'
      newOuts := newOuts ++ [⟨(max (btcIn / amounts.length) (dustLimit s)).toUInt64, s⟩]
  | .mint _ lr =>
    if let .witnessVout s := lr.beneficiary then newOuts := [⟨lr.amountSat.toUInt64, s⟩]
  | _ => pure ()
  let (changeScript, w') := w.coloredOutputAddress
  w := w'
  let (tx0, selected) ←
    w.buildColoredTx selected (⟨0, .opReturn none⟩ :: newOuts) changeScript feeRate (some now)
  let spent := selected.map (·.outpoint)
  let changeVout :=
    if tx0.outputs.length > 1 + newOuts.length then some (1 + newOuts.length) else none
  -- change destinations: the bitcoin change output, then UTXOs with room
  let dests : List (Option Outpoint) := (if changeVout.isSome then [none] else []) ++
    (w.availableAllocations spent (now := some now)).map fun (t, _, _) => some t.outpoint
  let sealAt (d : Option Outpoint) (k : Nat) : GraphSeal :=
    match d with
    | none => GraphSeal.witnessVout (changeVout.getD 0).toUInt32 (now.toUInt64 * 17 + k.toUInt64)
    | some o => GraphSeal.ofOutpoint o (now.toUInt64 * 17 + k.toUInt64)
  let slot (k : Nat) : Result GraphSeal :=
    match dests.head? with
    | some d => .ok (sealAt d k)
    | none => .error .insufficientAllocationSlots
  -- a mint right of asset `aid` moved to a destination with none of the asset yet
  let rightSlot (aid : String) (taken : List (String × Option Outpoint)) (k : Nat) :
      Result (Option Outpoint × GraphSeal) := do
    let d ← w.mintRightDest dests aid taken
    return (d, sealAt d k)
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
    let issuedSeal (i : Nat) : GraphSeal :=
      GraphSeal.witnessVout (i + 1).toUInt32 (now.toUInt64 + i.toUInt64)
    let allowance := if left > 0 then
        [(Schemas.osInflation, .fungible [(.revealed s0, ⟨left.toUInt64⟩)])]
      else []
    ts := [{ contractId := cid, transitionType := Schemas.tsInflation
             inputs := ofType Schemas.osInflation
             metadata := OrdMap.ofList [(Schemas.msAllowedInflation, ⟨.amount left.toUInt64⟩)]
             globals := OrdMap.ofList [(Schemas.gsIssuedSupply, [⟨.amount total.toUInt64⟩])]
             assignments := OrdMap.ofList
               ([(Schemas.osAsset, .fungible (amounts.zipIdx.map fun (a, i) =>
                   (.revealed (issuedSeal i), ⟨a.toUInt64⟩)))] ++ allowance) }]
  | .burn amount reason =>
    let total := amountOf Schemas.osAsset
    let globals : GlobalState := OrdMap.ofList
      ([(Schemas.gsBurnedAsset, [⟨.amount amount.toUInt64⟩])] ++
       (reason.map fun r => (Schemas.gsBurnReason, [⟨.burnReason ⟨r⟩⟩])).toList)
    if total == amount then
      ts := [{ contractId := cid, transitionType := Schemas.tsBurn, inputs := ofType Schemas.osAsset
               globals }]
    else
      -- split: the burned amount to a seal on the first spent outpoint, the rest to change
      let s0 ← slot 0
      let split : Transition :=
        { contractId := cid, transitionType := Schemas.tsTransfer, inputs := ofType Schemas.osAsset
          assignments := OrdMap.ofList [(Schemas.osAsset, .fungible
            [(.revealed (GraphSeal.ofOutpoint (spent.headD default) (now.toUInt64 * 3)),
                ⟨amount.toUInt64⟩),
             (.revealed s0, ⟨(total - amount).toUInt64⟩)])] }
      ts := [split, { contractId := cid, transitionType := Schemas.tsBurn
                      inputs := [⟨split.id, Schemas.osAsset, 0⟩], globals }]
  | .link linkedTo =>
    let linked : RevealedData := ⟨.contractId (Digest.of "asset-id" [linkedTo])⟩
    ts := [{ contractId := cid, transitionType := Schemas.tsLink, inputs := ofType Schemas.osLink
             globals := OrdMap.ofList [(Schemas.gsLinkedToContract, [linked])] }]
  | .mint beforeBlock lr =>
    -- one mint right is spent and not assigned again; the amount goes to the recipient
    let some (right, _) := states.find? (·.1.ty == Schemas.osMint)
      | throw (.insufficientAssignments assetId 0)
    let amount := lr.assignment.mainAmount.toUInt64
    let bound : RevealedData := ⟨.blockNumber ⟨beforeBlock.toUInt64⟩⟩
    ts := [{ contractId := cid, transitionType := Schemas.tsMint, inputs := [right]
             metadata := OrdMap.ofList [(Schemas.msBeforeBlock, bound)]
             globals := OrdMap.ofList [(Schemas.gsIssuedSupply, [⟨.amount amount⟩])]
             assignments := OrdMap.ofList
               [(Schemas.osAsset, .fungible [(lr.builderSeal, ⟨amount⟩)])] }]
  -- same-asset state the main transition does not spend, and other contracts'
  -- allocations on the spent UTXOs, move to change
  let used := ts.flatMap (·.inputs)
  let mut k := 1
  let mut rightsTaken : List (String × Option Outpoint) := []
  for (opout, st) in states do
    if !used.contains opout then
      let s ← if opout.ty == Schemas.osMint then do
          let (d, s) ← rightSlot assetId rightsTaken k
          rightsTaken := rightsTaken ++ [(assetId, d)]
          pure s
        else slot k
      k := k + 1
      let tt := ((w.stock.genesis? cid).bind fun g => (w.stock.rules? g.schemaId).bind fun r =>
        r.schema.defaultTransitionFor? opout.ty).getD Schemas.tsTransfer
      let moved := OrdMap.ofList [(opout.ty, typedAssigns [(.revealed s, st)])]
      ts := ts ++ [{ contractId := cid, transitionType := tt, inputs := [opout]
                     assignments := moved }]
  let mut bundles : List (ContractId × List Transition) := [(cid, ts)]
  for g in w.stock.geneses do
    if g.contractId != cid then
      let others := spent.flatMap fun op => w.stashState g.contractId op
      let mut moves : List Transition := []
      for (opout, st) in others do
        let aid := toString g.contractId
        let s ← if opout.ty == Schemas.osMint then do
            let (d, s) ← rightSlot aid rightsTaken k
            rightsTaken := rightsTaken ++ [(aid, d)]
            pure s
          else slot k
        k := k + 1
        let tt := ((w.stock.rules? g.schemaId).bind fun r =>
          r.schema.defaultTransitionFor? opout.ty).getD Schemas.tsTransfer
        let moved := OrdMap.ofList [(opout.ty, typedAssigns [(.revealed s, st)])]
        moves := moves ++ [{ contractId := g.contractId, transitionType := tt, inputs := [opout]
                             assignments := moved }]
      if !moves.isEmpty then bundles := bundles ++ [(g.contractId, moves)]
  let committed := bundles.map fun (c, ts) => (c, TransitionBundle.ofTransitions ts)
  let fascia ← (commitBundles tx0 committed now.toUInt64).mapError fun e => .internal (reprStr e)
  let tx := fascia.sealWitness.tx
  let kind := main.kind
  -- the sender endpoint is read as the transfer rows are saved
  if let some e := senderEndpoint then discard (TransportEndpoint.new e)
  let (beforeBlock, recipients) := match main with
    | .mint bb lr => (some bb, [(assetId, [lr])])
    | _ => (none, [])
  let op : PendingOp :=
    { txid := tx.txid, tx, fascia := some fascia, kind := some kind, minConfirmations, recipients
      senderTransportEndpoint := senderEndpoint, operationSecretKey := opKey.map (·.seed)
      createdAt := now, beforeBlock }
  w := { w with pending := w.pending ++ [op] }
  w := saveTransfers w op .initiated
  -- the operation's own transfer row and asset transfer kind
  let bi := (w.db.batchByTxid? tx.txid false).map (·.idx) |>.getD 0
  let requested : Option Assignment := match main with
    | .burn a _ => some (.fungible a.toUInt64)
    | .link _ => some .linkRight
    | .inflate _ | .mint .. => none
  -- the operation's own asset is user driven, as `list_transfers` shows it
  let setKind (a : DbAssetTransfer) : DbAssetTransfer :=
    if a.batchTransferIdx == bi && a.assetId == some assetId then
      { a with transitionType := some kind, userDriven := true }
    else a
  w := { w with db := { w.db with assetTransfers := w.db.assetTransfers.map setKind } }
  let ati := ((w.db.assetTransfersOf bi).find? (·.assetId == some assetId)).map (·.idx) |>.getD 0
  if let some ra := requested then
    let (ti, db) := w.db.fresh
    let row : DbTransfer := { idx := ti, assetTransferIdx := ati, requestedAssignment := some ra }
    w := { w with db := { db with transfers := db.transfers ++ [row] } }
  -- inflation outputs are issued allocations of the wallet, each a witness recipient of its own
  if let .inflate amounts := main then
    let newOps := (List.range amounts.length).map fun i => tx.outpoint (i + 1)
    let newIdx := (w.db.txos.filter fun t => newOps.contains t.outpoint).map (·.idx)
    let toIssue (c : DbColoring) : DbColoring :=
      if newIdx.contains c.txoIdx && c.type == .change then { c with type := .issue } else c
    w := { w with db := { w.db with colorings := w.db.colorings.map toIssue } }
    for ((o, a), i) in (newOuts.zip amounts).zipIdx do
      let (ti, db) := w.db.fresh
      let row : DbTransfer :=
        { idx := ti, assetTransferIdx := ati, requestedAssignment := some (.fungible a.toUInt64)
          recipientId := some ((Beneficiary.witnessVout o.script).recipientId w.chainNet)
          recipientType := some (.witness (some (i + 1).toUInt32)) }
      w := { w with db := { db with transfers := db.transfers ++ [row] } }
  return (w, op)

/-- Build, commit, broadcast and record a single-asset operation with no counterparty. -/
def runOperation (w : Wallet) (world : World) (assetId : String) (need : AssignmentsCollection)
    (main : MainTransition) (feeRate minConfirmations : Nat) : Result (Wallet × World × Txid) := do
  if (w.contractIdOf? assetId).isNone then throw (.assetNotFound assetId)
  let selected ← w.selectInputs assetId need (w.inputUnspents (some world.now))
  let (w, op) ← w.beginOperation world.now assetId selected main feeRate minConfirmations
  let bi := (w.db.batchByTxid? op.txid false).map (·.idx) |>.getD 0
  let (w2, world2) ← w.broadcastBatch world bi
  -- record the effects on the asset row
  let upd (a : DbAsset) : DbAsset :=
    if a.id != assetId then a else match main with
      | .inflate amounts =>
        let known := a.knownCirculatingSupply.getD a.initialSupply
        { a with knownCirculatingSupply := some (known + amounts.sum) }
      | .link to => { a with linkedToContract := some to }
      | .burn .. | .mint .. => a
  let w2 := { w2 with db := { w2.db with assets := w2.db.assets.map upd } }
  return (w2.updateBackupInfo world.now, world2, op.txid)

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
      match Hex.toBytes? h with
      | none => throw (.invalidBurnReason s!"not a hex string: {h}")
      | some b =>
        if b.length != 32 then throw (.invalidBurnReason s!"expected 32 bytes, got {b.length}")
        else pure (some b)
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
