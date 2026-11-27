import Rgb.Consensus.Ids

/-!
# Single-use seals

An RGB seal is a Bitcoin output. State assigned to a seal is spent by spending
the output: the transaction that spends it (the *witness*) is the only place
where the next state can be committed. A seal is *blinded* with a random 64-bit
value so that its outpoint can be hidden behind a `SecretSeal`.

Two seal forms exist:
* a genesis seal names a known output (`BlindSeal<Txid>`);
* a graph seal, used by transitions, names either a known output or an output
  of the witness transaction itself (`BlindSeal<TxPtr>` with `TxPtr::WitnessTx`):
  the receiver of a *witness* transfer gets state on an output of the very
  transaction that moves it.
-/

namespace Rgb

/-- Transaction pointer of a graph seal. -/
inductive TxPtr where
  /-- The witness transaction that closes the inputs of the operation. -/
  | witnessTx
  | txid (t : Txid)
  deriving DecidableEq, Ord, Hashable, Inhabited, Repr

instance : Encode TxPtr := ⟨fun
  | .witnessTx => "~"
  | .txid t => "#" ++ encode t⟩

/-- A seal of a transition output (`GraphSeal = BlindSeal<TxPtr>`). -/
structure GraphSeal where
  txptr : TxPtr
  vout : UInt32
  blinding : UInt64
  deriving DecidableEq, Ord, Hashable, Inhabited, Repr

/-- A seal of a genesis output (`GenesisSeal = BlindSeal<Txid>`). -/
structure GenesisSeal where
  txid : Txid
  vout : UInt32
  blinding : UInt64
  deriving DecidableEq, Ord, Hashable, Inhabited, Repr

/-- A seal of an output with a known transaction (`ExplicitSeal<Txid>`, `OutputSeal`). -/
abbrev OutputSeal := Outpoint

namespace GraphSeal

/-- Concealment: the tagged hash of the blinded seal. -/
def conceal (s : GraphSeal) : SecretSeal :=
  ⟨Digest.of Tag.secretSeal [encode s.txptr, encode s.vout, encode s.blinding]⟩

/-- Outpoint of the seal when its transaction is known. -/
def outpoint? (s : GraphSeal) : Option Outpoint :=
  match s.txptr with
  | .txid t => some ⟨t, s.vout⟩
  | .witnessTx => none

/-- Outpoint of the seal, taking `witness` for a witness-output seal. -/
def outpointOr (s : GraphSeal) (witness : Txid) : Outpoint :=
  match s.txptr with
  | .txid t => ⟨t, s.vout⟩
  | .witnessTx => ⟨witness, s.vout⟩

/-- Seal on an output of the witness transaction (`BlindSeal::with_blinded_vout`). -/
def witnessVout (vout : UInt32) (blinding : UInt64) : GraphSeal := ⟨.witnessTx, vout, blinding⟩

/-- Seal on a known output (`BlindSeal::with_blinding`). -/
def ofOutpoint (o : Outpoint) (blinding : UInt64) : GraphSeal := ⟨.txid o.txid, o.vout, blinding⟩

end GraphSeal

namespace GenesisSeal

/-- The same seal as a graph seal (`transmutate`). -/
def toGraph (s : GenesisSeal) : GraphSeal := ⟨.txid s.txid, s.vout, s.blinding⟩

def conceal (s : GenesisSeal) : SecretSeal := s.toGraph.conceal

def outpoint (s : GenesisSeal) : Outpoint := ⟨s.txid, s.vout⟩

end GenesisSeal

/-- Seal types usable in assignments. -/
class SealKind (σ : Type) where
  conceal : σ → SecretSeal
  toGraph : σ → GraphSeal

instance : SealKind GraphSeal := ⟨GraphSeal.conceal, id⟩
instance : SealKind GenesisSeal := ⟨GenesisSeal.conceal, GenesisSeal.toGraph⟩

/-- A seal in an operation: revealed, or concealed behind its hash (`BuilderSeal`). -/
inductive BuilderSeal (σ : Type) where
  | revealed (s : σ)
  | concealed (secret : SecretSeal)
  deriving DecidableEq, Ord, Hashable, Inhabited, Repr

namespace BuilderSeal
variable {σ : Type} [SealKind σ]

def toSecret : BuilderSeal σ → SecretSeal
  | .revealed s => SealKind.conceal s
  | .concealed c => c

def revealed? : BuilderSeal σ → Option σ
  | .revealed s => some s
  | .concealed _ => none

def isRevealed (b : BuilderSeal σ) : Bool := b.revealed?.isSome

/-- Reveal a concealed seal when `seal` matches its hash; otherwise unchanged. -/
def reveal (b : BuilderSeal σ) (s : σ) : BuilderSeal σ :=
  match b with
  | .concealed c => if c == SealKind.conceal s then .revealed s else b
  | .revealed _ => b

def conceal (b : BuilderSeal σ) : BuilderSeal σ := .concealed b.toSecret

def toGraph : BuilderSeal σ → BuilderSeal GraphSeal
  | .revealed s => .revealed (SealKind.toGraph s)
  | .concealed c => .concealed c

end BuilderSeal

/-- Why a witness does not close a seal (`seals::txout::VerifyError`, without DBC errors). -/
inductive SealCloseError where
  /-- The seal points to the witness transaction, so it has no outpoint to spend. -/
  | noWitnessTxid
  /-- The witness transaction does not spend the seal's outpoint. -/
  | witnessNotClosingSeal (o : Outpoint)
  deriving DecidableEq, Repr

/-- A witness closes a seal exactly when one of its inputs spends the seal's
outpoint (`Witness::verify_seal`, step 1). -/
def closesSeal (witness : Tx) (s : GraphSeal) : Except SealCloseError Unit :=
  match s.outpoint? with
  | none => .error .noWitnessTxid
  | some o => if witness.spends o then .ok () else .error (.witnessNotClosingSeal o)

end Rgb
