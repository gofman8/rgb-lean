import Rgb.Lib.Wallet

/-!
# Bitcoin-only operations

`create_utxos` moves bitcoin from the vanilla keychain to new colored outputs
that can hold allocations; `send_btc` pays from the vanilla keychain only;
`drain_to` sweeps everything. Each has a `_begin` that builds the unsigned
transaction (and reserves its inputs unless it is a dry run) and an `_end` that
broadcasts the signed one.

Fees use a fixed size model (`vsize`); dust limits are those of the output type.
-/

namespace Rgb.Lib

/-- Fee rate check (`check_fee_rate`): at least 1 sat/vB, and `rate * 250` fits `u64`. -/
def checkFeeRate (rate : Nat) : Result Unit :=
  if rate < minFeeRate then .error (.invalidFeeRate "value under minimum 1")
  else if rate * 250 > Bound.u64 then .error (.invalidFeeRate "value overflows")
  else .ok ()

/-- Virtual size of a transaction in the model: 11 + 58 per input + 43 per output. -/
def vsize (inputs outputs : Nat) : Nat := 11 + 58 * inputs + 43 * outputs

/-- Smallest relayable output value of a script. -/
def dustLimit : Script → Nat
  | .p2tr _ => 330
  | .opReturn _ => 0
  | _ => 294

/-- Map a chain refusal to the wallet error (`FailedBroadcast`). -/
def broadcastError (e : BroadcastError) : Error := .failedBroadcast (reprStr e)

/-- After a broadcast: the transaction's inputs are spent, its outputs exist. -/
def Db.markBroadcast (db : Db) (tx : Tx) : Db :=
  let upd (t : DbTxo) : DbTxo :=
    if tx.spends t.outpoint then { t with spent := true }
    else if t.outpoint.txid == tx.txid then { t with exists_ := true } else t
  { db with txos := db.txos.map upd
            reserved := db.reserved.filter fun r => !(r.forColored.isSome && tx.spends r.outpoint) }

namespace Wallet

/-- Build a transaction spending `inputs` to `outputs`, with change to `change`
when above dust (`InsufficientBitcoins` when the inputs cannot pay outputs and fee). -/
def buildTx (inputs : List (Outpoint × Nat)) (outputs : List TxOut) (change : Script) (feeRate : Nat) :
    Result Tx := do
  for o in outputs do
    if o.value.toNat < dustLimit o.script then throw .outputBelowDustLimit
  let available := (inputs.map (·.2)).sum
  let feeNoChange := feeRate * vsize inputs.length outputs.length
  let needed := (outputs.map (·.value.toNat)).sum + feeNoChange
  if available < needed then throw (.insufficientBitcoins needed available)
  let feeWithChange := feeRate * vsize inputs.length (outputs.length + 1)
  let rest := available - (outputs.map (·.value.toNat)).sum
  let outs := if rest ≥ feeWithChange + dustLimit change then outputs ++ [⟨(rest - feeWithChange).toUInt64, change⟩]
    else outputs
  return mkTx (inputs.map (·.1)) outs

/-- Vanilla change address: #0 with vanilla reuse, else the next one. -/
def vanillaChange (w : Wallet) : Script × Wallet := w.getAddress

/-- `create_utxos_begin`: how many colored outputs to make and the unsigned transaction. -/
def createUtxosBegin (w : Wallet) (world : World) (upTo : Bool) (num : Option Nat := none)
    (size : Option Nat := none) (feeRate : Nat) (dryRun : Bool := false) : Result (Wallet × Tx) := do
  checkFeeRate feeRate
  let mut n := num.getD utxoNum
  if upTo then
    let free := (w.availableAllocations w.db.reservedColored).length
    if free ≥ n then throw .allocationsAlreadyAvailable
    n := n - free
  let inputs := (w.vanillaUtxos world.chain).filter fun (o, _) => !w.db.reservedVanilla.contains o
  let usable := (inputs.map (·.2)).sum
  let sz := size.getD utxoSize
  if sz == 0 then throw .invalidAmountZero
  let k := min n (min (usable / sz) 255)
  let mut w := w
  let mut addrs : List Script := []
  for _ in List.range k do
    let (a, w') := w.coloredOutputAddress
    addrs := addrs ++ [a]
    w := w'
  let (chg, w1) := w.vanillaChange
  w := w1
  -- drop one output at a time until the transaction is affordable
  let mut result : Option Tx := none
  let mut lastErr : Error := .insufficientBitcoins (sz * n + 1000) 0
  let mut count := addrs.length
  while count > 0 && result.isNone do
    match buildTx inputs ((addrs.take count).map (⟨sz.toUInt64, ·⟩)) chg feeRate with
    | .ok tx => result := some tx
    | .error .outputBelowDustLimit => throw .outputBelowDustLimit
    | .error e => lastErr := e; count := count - 1
  let some tx := result | throw lastErr
  if !dryRun then
    let (i, db) := w.db.fresh
    w := { w with db := { db with
      walletTransactions := db.walletTransactions ++ [⟨i, tx.txid, .createUtxos⟩]
      reserved := db.reserved ++ tx.inputs.map fun inp => ⟨inp.prevout, some i, none⟩ } }
  return (w, tx)

/-- End a vanilla operation: drop its reservations, register colored outputs,
broadcast, mark the spent colored inputs. Returns the colored outputs made. -/
def vanillaEnd (w : Wallet) (world : World) (tx : Tx) (type : WalletTransactionType) :
    Result (Wallet × World × Nat) := do
  let txid := tx.txid
  if w.pending.any (·.txid == txid) then throw (.wrongOperation (toString txid))
  if let some wt := w.db.walletTransactions.find? (·.txid == txid) then
    if wt.type != type then throw (.wrongOperation (toString txid))
  let mut db := w.db
  match db.walletTransactions.find? (·.txid == txid) with
  | some wt => db := { db with reserved := db.reserved.filter (·.forVanilla != some wt.idx) }
  | none =>
    let (i, d) := db.fresh
    db := { d with walletTransactions := d.walletTransactions ++ [⟨i, txid, type⟩] }
  let colored := tx.outputs.zipIdx.filter fun (o, _) => w.isColored o.script
  for (o, i) in colored do
    db := (db.setTxo (tx.outpoint i) o.value.toNat (exists_ := false)).2
  let chain ← (world.chain.broadcast tx).mapError broadcastError
  db := db.markBroadcast tx
  return ({ w with db }, { world with chain }, colored.length)

/-- `create_utxos`: begin, sign, end. A watch-only wallet cannot sign. -/
def createUtxos (w : Wallet) (world : World) (o : Online) (upTo : Bool) (num : Option Nat := none)
    (size : Option Nat := none) (feeRate : Nat := 1) : Result (Wallet × World × Nat) := do
  if w.keys.watchOnly then throw .watchOnly
  w.checkOnline o
  let (w, tx) ← w.createUtxosBegin world upTo num size feeRate (dryRun := true)
  w.vanillaEnd world tx .createUtxos

/-- `send_btc`: pay `amount` sats to `script` from the vanilla keychain only. -/
def sendBtc (w : Wallet) (world : World) (o : Online) (script : Script) (amount feeRate : Nat) :
    Result (Wallet × World × Txid) := do
  if w.keys.watchOnly then throw .watchOnly
  w.checkOnline o
  checkFeeRate feeRate
  let inputs := (w.vanillaUtxos world.chain).filter fun (op, _) => !w.db.reservedVanilla.contains op
  let (chg, w) := w.vanillaChange
  let tx ← buildTx inputs [⟨amount.toUInt64, script⟩] chg feeRate
  let (w, world, _) ← w.vanillaEnd world tx .sendBtc
  return (w, world, tx.txid)

/-- `drain_to`: sweep every UTXO of both keychains to `script`; colored UTXOs
are spent too, so their allocations are lost. -/
def drainTo (w : Wallet) (world : World) (o : Online) (script : Script) (feeRate : Nat) :
    Result (Wallet × World × Txid) := do
  if w.keys.watchOnly then throw .watchOnly
  w.checkOnline o
  checkFeeRate feeRate
  let inputs := w.vanillaUtxos world.chain ++
    ((w.db.txos.filter fun t => !t.spent && world.chain.isUnspent t.outpoint).map fun t => (t.outpoint, t.btcAmount))
  let total := (inputs.map (·.2)).sum
  let fee := feeRate * vsize inputs.length 1
  if total < fee + dustLimit script then throw (.insufficientBitcoins (fee + dustLimit script) total)
  let tx := mkTx (inputs.map (·.1)) [⟨(total - fee).toUInt64, script⟩]
  let (w, world, _) ← w.vanillaEnd world tx .drain
  return (w, world, tx.txid)

end Wallet

end Rgb.Lib
