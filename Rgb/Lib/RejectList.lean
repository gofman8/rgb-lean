import Rgb.Consensus.Ids
import Rgb.Stl.Types

/-!
# Reject lists

An issuer of an IFA or BFA asset may publish a list of decisions about single
opouts: *reject* or *allow*. A wallet refuses a consignment whose history reaches
a rejected opout that no allowed opout shields. IFA publishes the list at a URL;
BFA at a URL or in an EVM contract.
-/

namespace Rgb.Lib

/-- Where the list is published (`RejectListSource`). -/
inductive RejectListSource where
  | url (u : String)
  | evm (c : EvmContract)
  deriving DecidableEq, Repr, Inhabited

/-- Most entries of a URL list. -/
def maxRejectListEntries : Nat := 100000
/-- Longest line: `!`, 64 hex chars, `/`, a `u16`, `/`, a `u16`, CRLF. -/
def maxRejectListLineSize : Nat := 1 + 64 + 1 + 5 + 1 + 5 + 2
/-- Largest URL list body accepted. -/
def maxRejectListSize : Nat := maxRejectListEntries * maxRejectListLineSize

/-- Rejected and allowed opouts; an opout is in at most one set (`RejectList`). -/
structure RejectList where
  reject : List Opout := []
  allow : List Opout := []
  deriving DecidableEq, Repr, Inhabited

namespace RejectList

def rejects (l : RejectList) (o : Opout) : Bool := l.reject.contains o
def allows (l : RejectList) (o : Opout) : Bool := l.allow.contains o

/-- Record a decision; the latest decision for an opout wins. -/
def insert (l : RejectList) (o : Opout) (allow : Bool) : RejectList :=
  let r := l.reject.filter (· != o)
  let a := l.allow.filter (· != o)
  if allow then { reject := r, allow := a ++ [o] } else { reject := r ++ [o], allow := a }

/-- Parse a URL list body: one opout per line, `!` marks an allowed opout, blank
lines are skipped, a line that is not an opout is counted and ignored. Returns
the list and the number of invalid lines. `parseOpout` reads `<opid>/<ty>/<no>`. -/
def parse (parseOpout : String → Option Opout) (body : String) : RejectList × Nat :=
  (body.splitOn "\n").foldl (fun (acc : RejectList × Nat) line =>
    let t := line.trimAscii.toString
    if t.isEmpty then acc
    else
      let (allow, rest) := if t.startsWith "!" then (true, (t.drop 1).toString) else (false, t)
      match parseOpout rest with
      | some o => (acc.1.insert o allow, acc.2)
      | none => (acc.1, acc.2 + 1)) ({}, 0)

end RejectList

/-- Why a published list is refused (`RejectListService`, `InvalidRejectList`). -/
inductive RejectListError where
  | unsupportedScheme (scheme : String)
  | tooLarge
  | notAscii
  | httpStatus (code : Nat)
  | finalizedOutOfRange (finalized len : Nat)
  | invalidOpout (s : String)
  deriving DecidableEq, Repr

/-- Checks of a fetched URL list body (`get_reject_list`): 2xx status, at most
`maxRejectListSize` bytes, ASCII. -/
def checkRejectListBody (status : Nat) (body : String) : Except RejectListError String :=
  if status < 200 || status ≥ 300 then .error (.httpStatus status)
  else if body.utf8ByteSize > maxRejectListSize then .error .tooLarge
  else if !body.toList.all (·.toNat < 128) then .error .notAscii
  else .ok body

/-- An entry of an EVM-hosted list, in append order. -/
structure EvmRejectListEntry where
  opout : String
  reject : Bool
  deriving DecidableEq, Repr, Inhabited

/-- The EVM list: entries and how many leading entries are in finalized blocks. -/
structure EvmRejectList where
  entries : List EvmRejectListEntry
  finalized : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Read an EVM list (`RejectList::from_evm`): finalized entries decide by the last
one per opout; a pending *reject* counts at once, a pending *allow* is ignored. -/
def RejectList.fromEvm (parseOpout : String → Option Opout) (l : EvmRejectList) :
    Except RejectListError RejectList := do
  if l.finalized > l.entries.length then
    throw (.finalizedOutOfRange l.finalized l.entries.length)
  let mut parsed : List (Opout × Bool) := []
  for e in l.entries do
    match parseOpout e.opout with
    | some o => parsed := parsed ++ [(o, e.reject)]
    | none => throw (.invalidOpout e.opout)
  let fin := parsed.take l.finalized
  let pending := parsed.drop l.finalized
  let lastFin (o : Opout) : Option Bool := (fin.filter (·.1 == o)).getLast?.map (·.2)
  let opouts := (parsed.map (·.1)).eraseDups
  let pendingReject (o : Opout) : Bool := pending.any fun (p, r) => p == o && r
  let reject := opouts.filter fun o => lastFin o == some true || pendingReject o
  let allow := opouts.filter fun o => lastFin o == some false && !pendingReject o
  return { reject, allow }

/-- An operation as the reject-list check sees the consignment DAG: the opouts
it spends, each with the operation that created it. -/
structure DagNode where
  opid : OpId
  spent : List (Opout × OpId)
  deriving DecidableEq, Repr, Inhabited

/-- `histRej(n)`: some opout spent by `n` is not allowed and is rejected or has a
rejected history. An allowed opout shields everything above it. -/
def historyRejected (dag : List DagNode) (l : RejectList) : Nat → OpId → Bool
  | 0, _ => false
  | fuel + 1, n =>
    match dag.find? (·.opid == n) with
    | none => false
    | some node => node.spent.any fun (s, p) =>
        !l.allows s && (l.rejects s || historyRejected dag l fuel p)

/-- Whether an origin opout is rejected (`rejected_opouts`). -/
def opoutRejected (dag : List DagNode) (l : RejectList) (o : Opout) : Bool :=
  if l.allows o then false
  else if l.rejects o then true
  else historyRejected dag l (dag.length + 1) o.op

/-- The rejected origins; a non-empty result refuses the consignment (`ConsignmentRejected`). -/
def rejectedOpouts (dag : List DagNode) (l : RejectList) (origins : List Opout) : List Opout :=
  origins.filter (opoutRejected dag l)

end Rgb.Lib
