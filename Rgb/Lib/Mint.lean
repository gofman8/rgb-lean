import Rgb.Lib.Operations

/-!
# Mints

A BFA asset is minted against a lock on its bridge, an EVM contract the genesis names. The
lock holds the minted amount under a lock id that commits to the mint operation and to its
witness transaction, and it must be included before a bridge block the mint commits to.

1. `mint_begin` (the minter) checks the operation in rgb-lib's order, then prepares the witness
   transaction: the mint transition spends one mint right (not assigned again), assigns the
   amount to the recipient's seal, records it as `issuedSupply` and commits to `beforeBlock`;
   the other state on the spent UTXOs moves to change. The transfer is saved as initiated, and
   the consignment is posted to the recipient's proxy before the transaction is signed. The
   operation is not registered on the sender proxy: the recipient does not ACK a mint.
2. The recipient's `refresh` checks the mint and saves what has to be locked
   (`get_received_mint`); its consignment then waits for the lock.
3. Someone makes the lock on the bridge. Once the bridge records it as of a finalized block,
   `mint_end` broadcasts and the recipient accepts the mint; both settle with confirmations.

A lock not included before its block expires the mint: `mint_end` fails it, as does
`fail_transfers`, and the recipient refuses it. `beforeBlock` must lie from the chain's
`min_mint_lock_blocks` to its `max_mint_lock_blocks` blocks after its latest block, leaving a
block for the lock.
-/

namespace Rgb.Lib

namespace Wallet

/-- What `mint_begin` gives (`MintBeginResult`): the prepared operation (its PSBT), its batch
transfer and the mint operation the lock commits to (`MintDetails.opid`). -/
structure MintBeginResult where
  op : PendingOp
  batchTransferIdx : Nat
  opid : OpId
  deriving Repr, Inhabited

/-- `mint_begin`: mint `recipient`'s amount of a BFA asset, the lock included before bridge
block `beforeBlock`. Checks in rgb-lib's order; the consignment is posted before signing. -/
def mintBegin (w : Wallet) (world : World) (o : Online) (assetId : String) (recipient : Recipient)
    (beforeBlock feeRate minConfirmations : Nat) (senderEndpoint : String) :
    Result (Wallet × World × MintBeginResult) := do
  w.checkOnline o
  let now := world.now
  let a ← w.asset? assetId
  w.checkSchemaSupport a.schema
  if !a.schema.supportsMint then throw (.unsupportedMint a.schema)
  if !recipient.assignment.isFungible then throw .invalidAssignment
  let (opKey, w) := w.newOperationKey now
  checkFeeRate feeRate
  -- the wallet keeps a mint right to mint again
  let cands := w.inputUnspents (some now)
  let rights := (cands.flatMap (·.2)).filter fun al =>
    al.assetId == some assetId && al.status == .settled && al.assignment == .mintRight
  if rights.length == 1 then throw .lastMintRight
  let selected ← w.selectInputs assetId { mint := 1 } cands
  -- a mint recipient is always a proxy one
  if recipient.transportEndpoints.isEmpty then
    throw (.invalidTransportEndpoints "no valid transport endpoints")
  let lr ← w.parseRecipient now a.schema recipient 1 0 opKey (mint := true)
  let lr := lr.markUsable (usableEndpoints world [lr])
  checkUsableEndpoints [lr]
  -- the latest block of the bridge's chain, through the endpoint checked to be on it
  let some cid := w.contractIdOf? assetId | throw (.assetNotFound assetId)
  let some g := w.stock.genesis? cid | throw (.assetNotFound assetId)
  let bridge ← match NoWallet.bridgeLocation g with
    | .ok (.evm b) => pure b
    | .error e => throw (.internal e)
  let chainId := bridge.chainId.toNat
  let some url := w.evmRpcUrls.lookup chainId | throw (.noEvmRpcUrl chainId)
  let some chain := w.evmChains.lookup chainId | throw (.noEvmRpcUrl chainId)
  let latest ← (world.evmNet url).blockNumber
  Evm.checkMintBeforeBlock beforeBlock latest chain
  let (w, op) ← w.beginOperation now assetId selected (.mint beforeBlock lr) feeRate
    minConfirmations (some senderEndpoint) (some opKey)
  -- the consignment, posted to the recipient's proxy before the transaction is signed
  let some fascia := op.fascia | throw (.internal "missing fascia")
  let (outs, secrets) := match lr.beneficiary, lr.vout with
    | .blindedSeal s, _ => ([], [s])
    | .witnessVout _, some v => ([op.tx.outpoint v], [])
    | .witnessVout _, none => ([], [])
  let c ← (w.stock.transferFromFascia cid outs secrets [] fascia).mapError
    fun e => .internal (reprStr e)
  let hash := (ProxyCrypto.Payload.consignment c).hash
  let (posted, world) :=
    (postTransferData [lr] c opKey (some senderEndpoint) hash false).exec world
  discard posted
  let op := { op with consignments := [(assetId, c)] }
  let some b := w.db.batchByTxid? op.txid false | throw (.internal "missing batch transfer")
  let some opid := mintOpid? fascia cid | throw (.internal "mint transition missing from fascia")
  let info := { w.db.backupInfo with lastOperationTimestamp := now }
  let w := { w with pending := w.pending.map fun p => if p.txid == op.txid then op else p
                    db := { w.db with backupInfo := info } }
  return (w, world, ⟨op, b.idx, opid⟩)

/-- `mint_end` as a step: an initiated mint whose lock the bridge records as of a finalized
block, included in time, is broadcast; the known circulating supply becomes the bridge's. A mint
that ended or failed cannot end again. -/
def mintEndStep (w : Wallet) (txid : Txid) : Net (Wallet × OperationResult) := do
  if let some b := w.db.batchByTxid? txid false then
    if b.status != .initiated then throw (.cannotEndTransfer (toString txid))
  let some op := w.pending.find? (·.txid == txid) | throw (.unknownTransfer (toString txid))
  if op.kind != some .mint then throw (.wrongOperation (toString txid))
  let world ← get
  let m ← Net.ofResult (w.sentMint op)
  let node ← Net.ofResult (Evm.checkMintLock world.evmNet w.evmRpcUrls m)
  -- the bridge accounts the minted amount too
  let supply := match m.bridgeLocation with
    | .evm c => Evm.readCirculatingSupply node c.address
  let w := w.setKnownSupply (toString m.contractId) supply
  -- the consignment was posted by the begin; the `used` flags of its endpoints are not written
  let hashes := op.consignments.map fun (a, c) => (a, (ProxyCrypto.Payload.consignment c).hash)
  let w := w.updateOrSaveTransfers op .waitingConfirmations hashes world.now (syncUsed := false)
  let some b := w.db.batchByTxid? txid false | throw (.internal "missing batch transfer")
  let w ← w.broadcastOp b.idx
  let info := { w.db.backupInfo with lastOperationTimestamp := world.now }
  let entropy := (op.fascia.map (·.sealWitness.mpcTree.entropy)).getD 0
  return ({ w with db := { w.db with backupInfo := info } }, ⟨txid, b.idx, entropy⟩)

/-- `mint_end`: a lock not confirmed yet gives `mintLockNotFound` and leaves the mint initiated;
one that expired fails the mint, releasing its inputs, and gives `mintLockExpired`. -/
def mintEnd (w : Wallet) (world : World) (o : Online) (txid : Txid) :
    Wallet × World × Result OperationResult :=
  match w.checkOnline o with
  | .error e => (w, world, .error e)
  | .ok () =>
    match (w.mintEndStep txid).exec world with
    | (.ok (w', r), world') => (w', world', .ok r)
    | (.error (.mintLockExpired opid bb), world') =>
      let w' := match w.db.batchByTxid? txid false with
        | some b =>
          let f := w.failBatch world.now b.idx
          let info := { f.db.backupInfo with lastOperationTimestamp := world.now }
          { f with db := { f.db with backupInfo := info } }
        | none => w
      (w', world', .error (.mintLockExpired opid bb))
    | (.error e, world') => (w, world', .error e)

/-- `get_received_mint`: the mints this wallet checked that pay `recipientId`, of its incoming
transfers that did not fail: what each needs locked. -/
def getReceivedMint (w : Wallet) (recipientId : String) : List Evm.ReceivedMint :=
  w.db.transfers.filterMap fun t =>
    let receiving := (w.db.batchOfAssetTransfer? t.assetTransferIdx).any fun b =>
      b.incoming && b.status != .failed
    if t.recipientId == some recipientId && receiving then w.receivedMints.lookup t.idx else none

end Wallet

end Rgb.Lib
