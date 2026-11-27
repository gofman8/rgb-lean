import Rgb.Consensus.Schema

/-!
# The validation VM

Schema validation routines are AluVM code: the AluVM base instructions plus the
RGB contract opcodes. The model interprets the instructions the standard schemas
use, with their exact semantics:

* registers `a8`, `a16`, `a32`, `a64` hold numbers or nothing, `s16` holds bytes;
  every register starts empty and the status flag `st0` starts true;
* RGB opcodes that fail stop the VM at once with `st0 = false`;
* the routine's result is `st0`, and its error code is whatever `a8[0]` holds at
  the end (`ScriptFailure(opid, a8[0], None)`).

Code addresses are byte offsets, computed from each instruction's encoded size,
so the routines below keep the entry offsets and jump targets of `rgb-schemas`.
-/

namespace Rgb

/-! ## Claims -/

/-- A statement about an external system that consensus cannot check
(`Claim::Lock`): the bridge holds a lock of exactly `amount` for operation
`opid` in witness `witnessId`, recorded before bridge block `beforeBlock`.
Claims are ordered by these fields in turn, as rgb-consensus derives `Ord`. -/
inductive Claim where
  | lock (opid : OpId) (witnessId : Txid) (amount : UInt64) (beforeBlock : UInt64)
  deriving DecidableEq, Ord, Repr, Inhabited

/-- Tag of lock ids. -/
def lockTag : String := "urn:lnp-bp:rgb:lock#2026-11-04"

/-- Id under which a bridge records a lock: tagged hash of opid and witness txid. -/
structure LockId where
  d : Digest
  deriving DecidableEq, Repr, Inhabited

def LockId.of (opid : OpId) (witness : Txid) : LockId := ⟨Digest.of lockTag [encode opid, encode witness]⟩

namespace Claim

def opid : Claim → OpId
  | .lock opid _ _ _ => opid

def witness : Claim → Txid
  | .lock _ w _ _ => w

def amount : Claim → UInt64
  | .lock _ _ a _ => a

def beforeBlock : Claim → UInt64
  | .lock _ _ _ b => b

def lockId (c : Claim) : LockId := LockId.of c.opid c.witness

end Claim

/-! ## Contract-state order -/

/-- Consensus order of operations for global state (`OpOrd`): genesis first,
then transitions by type, nonce and id. -/
inductive OpOrd where
  | genesis
  | transition (ty : TransitionType) (nonce : UInt64) (opid : OpId)
  deriving DecidableEq, Ord, Repr, Inhabited

/-- Order of a global value: its operation's order, then its index (`GlobalOrd`). -/
structure GlobalOrd where
  opOrd : OpOrd
  idx : UInt16
  deriving DecidableEq, Ord, Repr, Inhabited

/-- A global value with its order and the witness of its operation. -/
structure GlobalEntry where
  ord : GlobalOrd
  value : RevealedData
  witness : Option Txid
  deriving DecidableEq, Repr, Inhabited

def Operation.opOrd : Operation → OpOrd
  | .genesis _ => .genesis
  | .transition t => .transition t.transitionType t.nonce t.id

/-- Global entries an operation adds. -/
def Operation.globalEntries (op : Operation) (witness : Option Txid) :
    List (GlobalStateType × GlobalEntry) :=
  op.globals.toList.flatMap fun (ty, vals) =>
    vals.zipIdx.map fun (v, i) => (ty, ⟨⟨op.opOrd, i.toUInt16⟩, v, witness⟩)

/-! ## What a routine sees -/

/-- The VM context of one operation (`VmContext`, `OpInfo`). -/
structure VmContext where
  contractId : ContractId
  opid : OpId
  op : Operation
  /-- Witness of a transition; none for genesis. -/
  witnessId : Option Txid
  /-- States the operation spends, by type, in input order. -/
  prevState : OrdMap AssignmentType (List RevealedState)
  /-- Contract global state before this operation, latest first, per type;
  none when the schema has no such type. -/
  contractGlobal : GlobalStateType → Option (List RevealedData)

/-! ## Instructions -/

/-- Register banks. -/
inductive Bank where
  | a8 | a16 | a32 | a64
  deriving DecidableEq, Repr, Inhabited

def Bank.bits : Bank → Nat
  | .a8 => 8 | .a16 => 16 | .a32 => 32 | .a64 => 64

inductive Instr where
  /-- `put aN[i],v` -/
  | put (b : Bank) (i v : Nat)
  /-- `test`: continue if `st0`, else fail. -/
  | test
  /-- `ret`: stop with `st0`. -/
  | ret
  | jmp (off : Nat)
  /-- `jif off`: jump if `st0`. -/
  | jif (off : Nat)
  /-- `ifz aN[i]`: `st0 := aN[i] = 0` (set and zero). -/
  | ifz (b : Bank) (i : Nat)
  /-- `inv st0` -/
  | inv
  /-- `eq.n aN[i],aN[j]`: `st0 :=` both set and equal. -/
  | eqn (b : Bank) (i j : Nat)
  /-- `cpy aN[i],aN[j]` -/
  | cpy (b : Bank) (i j : Nat)
  /-- `add.uc aN[s],aN[d]`: `aN[d] := aN[s] + aN[d]`, checked. -/
  | addUc (b : Bank) (s d : Nat)
  /-- `sub.uc aN[s],aN[d]`: `aN[d] := aN[s] - aN[d]`, checked. -/
  | subUc (b : Bank) (s d : Nat)
  /-- `extr s16[k],aN[d],a16[o]`: read a little-endian number at offset `a16[o]`. -/
  | extr (k : Nat) (b : Bank) (d o : Nat)
  /-- `cnp t,a16[r]`: number of inputs of type `t`. -/
  | cnp (t : AssignmentType) (r : Nat)
  /-- `cns t,a16[r]`: number of outputs of type `t`. -/
  | cns (t : AssignmentType) (r : Nat)
  /-- `cng t,a8[r]`: number of global values of type `t` in this operation. -/
  | cng (t : GlobalStateType) (r : Nat)
  /-- `cnc t,a32[r]`: number of contract global values of type `t`. -/
  | cnc (t : GlobalStateType) (r : Nat)
  /-- `ldp t,a16[i],s16[s]`: structured input state. -/
  | ldp (t : AssignmentType) (i s : Nat)
  /-- `lds t,a16[i],s16[s]`: structured output state. -/
  | lds (t : AssignmentType) (i s : Nat)
  /-- `ldf t,a16[i],a64[d]`: fungible output state. -/
  | ldf (t : AssignmentType) (i d : Nat)
  /-- `ldg t,a8[i],s16[s]`: global state of this operation. -/
  | ldg (t : GlobalStateType) (i s : Nat)
  /-- `ldc t,a32[i],s16[s]`: contract global state at a depth. -/
  | ldc (t : GlobalStateType) (i s : Nat)
  /-- `ldm t,s16[s]`: metadata. -/
  | ldm (t : MetaType) (s : Nat)
  /-- `svs t`: inputs and outputs of type `t` sum to the same amount. -/
  | svs (t : AssignmentType)
  /-- `sas t`: outputs of type `t` sum to `a64[0]`. -/
  | sas (t : AssignmentType)
  /-- `sps t`: inputs of type `t` sum to `a64[0]`. -/
  | sps (t : AssignmentType)
  /-- `vts s16[s]`: the transition is signed by the public key in `s16[s]`. -/
  | vts (s : Nat)
  /-- `plc a64[a],a64[b]`: push a lock claim of `a64[a]` before block `a64[b]`. -/
  | plc (a b : Nat)
  /-- A reserved or unknown opcode: fail. -/
  | fail
  deriving DecidableEq, Repr, Inhabited

/-- Encoded size in bytes. -/
def Instr.size : Instr → Nat
  | .put .. => 4 | .test | .ret | .inv | .fail => 1 | .jmp _ | .jif _ => 3 | .ifz .. => 2
  | .eqn .. | .cpy .. | .addUc .. | .subUc .. | .extr .. => 3
  | .cnp .. | .cns .. | .cng .. | .cnc .. => 4
  | .ldp .. | .lds .. | .ldf .. | .ldg .. | .ldc .. | .ldm .. => 4
  | .svs _ | .sas _ | .sps _ => 3
  | .vts _ | .plc .. => 2

/-- An AluVM library: id and code. -/
structure Lib where
  id : String
  code : List Instr
  deriving DecidableEq, Repr, Inhabited

/-- Byte offset of each instruction. -/
def Lib.offsets (l : Lib) : List Nat :=
  (l.code.foldl (fun (acc : List Nat × Nat) i => (acc.1 ++ [acc.2], acc.2 + i.size)) ([], 0)).1

def Lib.byteLen (l : Lib) : Nat := (l.code.map Instr.size).sum

/-! ## Machine state -/

structure VmState where
  a8 : Nat → Option Nat := fun _ => none
  a16 : Nat → Option Nat := fun _ => none
  a32 : Nat → Option Nat := fun _ => none
  a64 : Nat → Option Nat := fun _ => none
  s16 : Nat → Option Bytes := fun _ => none
  st0 : Bool := true
  claims : List Claim := []

namespace VmState

def get (s : VmState) : Bank → Nat → Option Nat
  | .a8, i => s.a8 i | .a16, i => s.a16 i | .a32, i => s.a32 i | .a64, i => s.a64 i

def set (s : VmState) (b : Bank) (i : Nat) (v : Option Nat) : VmState :=
  let upd (f : Nat → Option Nat) : Nat → Option Nat := fun j => if j == i then v else f j
  match b with
  | .a8 => { s with a8 := upd s.a8 } | .a16 => { s with a16 := upd s.a16 }
  | .a32 => { s with a32 := upd s.a32 } | .a64 => { s with a64 := upd s.a64 }

def setS (s : VmState) (i : Nat) (v : Bytes) : VmState :=
  { s with s16 := fun j => if j == i then some v else s.s16 j }

end VmState

/-- Result of one instruction: continue at an offset, or stop with the state. -/
inductive Step where
  | next (s : VmState)
  | jump (s : VmState) (off : Nat)
  | stop (s : VmState)

/-- Fail: `st0 := false` and halt. -/
def VmState.halt (s : VmState) : Step := .stop { s with st0 := false }

/-- Checked sum of `u64` values. -/
def sumU64 (l : List Nat) : Option Nat :=
  l.foldl (fun acc x => acc.bind fun a => if a + x ≤ Bound.u64 then some (a + x) else none) (some 0)

/-- Fungible amounts of a state list; none if a state is not fungible. -/
def fungibleAmounts (l : List RevealedState) : Option (List Nat) :=
  l.foldr (fun st acc => match st, acc with
    | .fungible v, some xs => some (v.v.toNat :: xs)
    | _, _ => none) (some [])

namespace VmContext

def prev (c : VmContext) (t : AssignmentType) : List RevealedState := (c.prevState.find? t).getD []

def own? (c : VmContext) (t : AssignmentType) : Option (TypedAssigns GraphSeal) := c.op.assignments.find? t

def ownStates (c : VmContext) (t : AssignmentType) : List RevealedState :=
  ((c.own? t).map fun ta => ta.items.map (·.2)).getD []

def glob (c : VmContext) (t : GlobalStateType) : List RevealedData := (c.op.globals.find? t).getD []

/-- Output amounts of `t`, refusing a non-fungible kind or a zero amount. -/
def outAmounts (c : VmContext) (t : AssignmentType) : Option (List Nat) :=
  match c.own? t with
  | none => some []
  | some (.fungible l) => let xs := l.map (·.2.v.toNat); if xs.contains 0 then none else some xs
  | some _ => none

end VmContext

/-- Execute one instruction. -/
def exec (ctx : VmContext) (s : VmState) : Instr → Step
  | .put b i v => if v < 2 ^ b.bits then .next (s.set b i (some v)) else .next { s with st0 := false }
  | .test => if s.st0 then .next s else s.halt
  | .ret => .stop s
  | .jmp off => .jump s off
  | .jif off => if s.st0 then .jump s off else .next s
  | .ifz b i => .next { s with st0 := s.get b i == some 0 }
  | .inv => .next { s with st0 := !s.st0 }
  | .eqn b i j => .next { s with st0 := match s.get b i, s.get b j with
      | some x, some y => x == y
      | _, _ => false }
  | .cpy b i j => .next { (s.set b j (s.get b i)) with st0 := true }
  | .addUc b src d =>
    let r := match s.get b src, s.get b d with
      | some x, some y => if x + y < 2 ^ b.bits then some (x + y) else none
      | _, _ => none
    .next { (s.set b d r) with st0 := r.isSome }
  | .subUc b src d =>
    let r := match s.get b src, s.get b d with
      | some x, some y => if y ≤ x then some (x - y) else none
      | _, _ => none
    .next { (s.set b d r) with st0 := r.isSome }
  | .extr k b d o =>
    let w := b.bits / 8
    match s.s16 k, s.a16 o with
    | some bytes, some off =>
      if off ≥ bytes.length then .next { (s.set b d none) with st0 := false }
      else
        let v := Bytes.leValue ((bytes.drop off).take w)
        .next { (s.set b d (some v)) with st0 := off + w ≤ bytes.length }
    | _, _ => .next { (s.set b d none) with st0 := false }
  | .cnp t r => .next (s.set .a16 r (some (ctx.prev t).length))
  | .cns t r => .next (s.set .a16 r (some (ctx.ownStates t).length))
  | .cng t r =>
    let n := (ctx.glob t).length
    if n < 256 then .next (s.set .a8 r (some n)) else s.halt
  | .cnc t r => .next (s.set .a32 r (some ((ctx.contractGlobal t).map List.length |>.getD 0)))
  | .ldp t i k =>
    match s.a16 i with
    | none => s.halt
    | some idx => match (ctx.prev t)[idx]? with
      | some (.structured d) => .next (s.setS k d.v.toBytes)
      | _ => s.halt
  | .lds t i k =>
    match s.a16 i, ctx.own? t with
    | some idx, some (.structured l) => match l[idx]? with
      | some (_, d) => .next (s.setS k d.v.toBytes)
      | none => s.halt
    | _, _ => s.halt
  | .ldf t i d =>
    match s.a16 i, ctx.own? t with
    | some idx, some (.fungible l) => match l[idx]? with
      | some (_, v) => .next (s.set .a64 d (some v.v.toNat))
      | none => s.halt
    | _, _ => s.halt
  | .ldg t i k =>
    match s.a8 i with
    | none => s.halt
    | some idx => match (ctx.glob t)[idx]? with
      | some d => .next (s.setS k d.v.toBytes)
      | none => s.halt
  | .ldc t i k =>
    match ctx.contractGlobal t, s.a32 i with
    | some vals, some depth =>
      if depth > Bound.u24 then s.halt
      else match vals[depth]? with
        | some d => .next (s.setS k d.v.toBytes)
        | none => s.halt
    | _, _ => s.halt
  | .ldm t k =>
    match ctx.op.metadata.find? t with
    | some d => .next (s.setS k d.v.toBytes)
    | none => s.halt
  | .svs t =>
    match fungibleAmounts (ctx.prev t) |>.bind sumU64, ctx.outAmounts t |>.bind sumU64 with
    | some i, some o => if i == o then .next s else s.halt
    | _, _ => s.halt
  | .sas t =>
    match s.a64 0, ctx.outAmounts t |>.bind sumU64 with
    | some v, some o => if v == o then .next s else s.halt
    | _, _ => s.halt
  | .sps t =>
    match s.a64 0, fungibleAmounts (ctx.prev t) |>.bind sumU64 with
    | some v, some i => if v == i then .next s else s.halt
    | _, _ => s.halt
  | .vts k =>
    match ctx.op, s.s16 k with
    | .transition tr, some pk =>
      if pk.length != 33 && pk.length != 65 then s.halt
      else match tr.signature with
        | some sig => if sig.verify pk ctx.opid.d then .next s else s.halt
        | none => s.halt
    | _, _ => s.halt
  | .plc a b =>
    match s.a64 a, s.a64 b, ctx.witnessId with
    | some amt, some bb, some w =>
      if amt == 0 then s.halt
      else .next { s with claims := s.claims ++ [.lock ctx.opid w amt.toUInt64 bb.toUInt64] }
    | _, _, _ => s.halt
  | .fail => s.halt

/-- Result of a routine: `st0`, the error code in `a8[0]` and the pushed claims. -/
structure VmResult where
  ok : Bool
  errno : Option UInt8
  claims : List Claim
  deriving DecidableEq, Repr, Inhabited

/-- Run a library from a byte offset. Running off the end acts as `ret`; a jump
to an offset that is not an instruction boundary fails. -/
def Lib.run (lib : Lib) (entry : Nat) (ctx : VmContext) (init : VmState := {}) : VmResult :=
  let offs := lib.offsets
  let finish (s : VmState) : VmResult := ⟨s.st0, (s.a8 0).map Nat.toUInt8, s.claims⟩
  let rec go (fuel pc : Nat) (s : VmState) : VmResult :=
    match fuel with
    | 0 => finish { s with st0 := false }
    | fuel + 1 =>
      if pc ≥ lib.byteLen then finish s
      else match offs.idxOf? pc with
        | none => finish { s with st0 := false }
        | some i => match lib.code[i]? with
          | none => finish s
          | some instr => match exec ctx s instr with
            | .next s' => go fuel (pc + instr.size) s'
            | .jump s' off => go fuel off s'
            | .stop s' => finish s'
  go (4 * lib.code.length + 4) entry init

end Rgb
