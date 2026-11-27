import Rgb.Bitcoin.Tx

/-!
# A Bitcoin chain for scenarios

A minimal ledger: confirmed blocks, a mempool and the set of unspent outputs.
It answers what RGB asks layer 1: is a witness transaction mined, at which
height, with how many confirmations, and is an outpoint still unspent. Blocks
carry no proof of work; reorganisations are modelled by `rollback`.
-/

namespace Rgb

/-- Position of a mined witness transaction (`WitnessPos`). -/
structure WitnessPos where
  height : Nat
  timestamp : Int
  deriving DecidableEq, Ord, Repr, Inhabited

/-- Consensus status of a witness transaction (`WitnessOrd`), ordered as in RGB:
mined before tentative before ignored before archived. -/
inductive WitnessOrd where
  | mined (pos : WitnessPos)
  | tentative
  | ignored
  | archived
  deriving DecidableEq, Ord, Repr, Inhabited

/-- Witness state other than `archived` takes part in contract state. -/
def WitnessOrd.isValid : WitnessOrd → Bool
  | .archived => false
  | _ => true

structure Block where
  height : Nat
  timestamp : Int
  txs : List Tx
  deriving Repr, Inhabited

/-- Why the chain refuses a transaction. -/
inductive BroadcastError where
  | missingInput (o : Outpoint)
  | inputSpent (o : Outpoint)
  | conflictInMempool (o : Outpoint)
  | noInputs
  | noOutputs
  | valueExceedsInputs (inputs outputs : Nat)
  deriving DecidableEq, Repr

structure Chain where
  blocks : List Block := []
  mempool : List Tx := []
  /-- Time of the next block. -/
  clock : Int := 1700000000
  deriving Repr, Inhabited

namespace Chain

def height (c : Chain) : Nat := c.blocks.length

def minedTxs (c : Chain) : List (Tx × Block) :=
  c.blocks.flatMap fun b => b.txs.map (·, b)

def findMined? (c : Chain) (t : Txid) : Option (Tx × Block) :=
  c.minedTxs.find? fun (tx, _) => tx.txid == t

def findMempool? (c : Chain) (t : Txid) : Option Tx := c.mempool.find? (·.txid == t)

def findTx? (c : Chain) (t : Txid) : Option Tx :=
  (c.findMined? t).map (·.1) <|> c.findMempool? t

/-- Confirmations of a transaction: 0 while in the mempool or unknown. -/
def confirmations (c : Chain) (t : Txid) : Nat :=
  match c.findMined? t with
  | some (_, b) => c.height - b.height + 1
  | none => 0

/-- What an indexer answers for a witness id (`WitnessStatus::witness_ord`). -/
def witnessOrd (c : Chain) (t : Txid) : WitnessOrd :=
  match c.findMined? t with
  | some (_, b) => .mined ⟨b.height, b.timestamp⟩
  | none => if (c.findMempool? t).isSome then .tentative else .archived

/-- All transactions the chain knows, mined first. -/
def allTxs (c : Chain) : List Tx := c.minedTxs.map (·.1) ++ c.mempool

/-- An output exists when a known transaction created it. -/
def output? (c : Chain) (o : Outpoint) : Option TxOut :=
  (c.findTx? o.txid).bind (·.outputAt? o.vout)

/-- The transaction that spends `o`, if any (mined or in the mempool). -/
def spender? (c : Chain) (o : Outpoint) : Option Tx := c.allTxs.find? (·.spends o)

def isUnspent (c : Chain) (o : Outpoint) : Bool := (c.output? o).isSome && (c.spender? o).isNone

/-- Add a transaction to the mempool, refusing double spends. -/
def broadcast (c : Chain) (tx : Tx) : Except BroadcastError Chain := do
  if tx.inputs.isEmpty then throw .noInputs
  if tx.outputs.isEmpty then throw .noOutputs
  let mut inValue := 0
  for i in tx.inputs do
    match c.output? i.prevout with
    | none => throw (.missingInput i.prevout)
    | some out =>
      inValue := inValue + out.value.toNat
      if (c.mempool.find? (·.spends i.prevout)).isSome then throw (.conflictInMempool i.prevout)
      if (c.spender? i.prevout).isSome then throw (.inputSpent i.prevout)
  if tx.totalOut > inValue then throw (.valueExceedsInputs inValue tx.totalOut)
  return { c with mempool := c.mempool ++ [tx] }

/-- Mine the whole mempool into a new block. -/
def mine (c : Chain) : Chain :=
  { c with
    blocks := c.blocks ++ [⟨c.height + 1, c.clock, c.mempool⟩]
    mempool := []
    clock := c.clock + 600 }

/-- Mine `n` blocks. -/
def mineN (c : Chain) : Nat → Chain
  | 0 => c
  | n + 1 => (c.mine).mineN n

/-- Fund an address out of thin air (a coinbase), mined at once. -/
def fund (c : Chain) (script : Script) (value : Sats) (salt : Nat := 0) : Chain × Outpoint :=
  let tx : Tx := { inputs := [], outputs := [⟨value, script⟩], lockTime := salt.toUInt32 }
  let c' := { c with mempool := c.mempool ++ [tx] }.mine
  (c', tx.outpoint 0)

/-- Drop the last `n` blocks; their transactions return to the mempool. -/
def rollback (c : Chain) (n : Nat) : Chain :=
  let keep := c.blocks.length - n
  let dropped := (c.blocks.drop keep).flatMap (·.txs)
  { c with blocks := c.blocks.take keep, mempool := dropped ++ c.mempool }

/-- Remove a transaction from the mempool (it was replaced or evicted). -/
def evict (c : Chain) (t : Txid) : Chain := { c with mempool := c.mempool.filter (·.txid != t) }

end Chain

end Rgb
