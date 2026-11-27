import Rgb.Lib.RejectList

/-!
# Reject list scenarios

The decisions of rgb-lib's reject-list tests on a small history: genesis `g`
issues opout `gi`; transition `t1` spends it into a change opout `c` and an
output `p`; transition `t2` spends `p` into the terminal output `t`.
-/

namespace Rgb.Examples.RejectListScenario

open Rgb Rgb.Lib

def mkOp (n : String) : OpId := ⟨Digest.of Tag.operation [n]⟩
def g : OpId := mkOp "genesis"
def t1 : OpId := mkOp "t1"
def t2 : OpId := mkOp "t2"
def gi : Opout := ⟨g, ⟨4000⟩, 0⟩
def c : Opout := ⟨t1, ⟨4000⟩, 0⟩
def p : Opout := ⟨t1, ⟨4000⟩, 1⟩
def t : Opout := ⟨t2, ⟨4000⟩, 0⟩

def dag : List DagNode := [⟨g, []⟩, ⟨t1, [(gi, g)]⟩, ⟨t2, [(p, t1)]⟩]

/-- Lines name opouts as `gi`, `c`, `p`, `t` in this scenario. -/
def parseName : String → Option Opout
  | "gi" => some gi | "c" => some c | "p" => some p | "t" => some t | _ => none

def list (body : String) : RejectList := (RejectList.parse parseName body).1

/-- Origins of a consignment ending in `t2`: its input and its output. -/
def origins : List Opout := [p, t]

-- a rejected terminal output is refused
#guard rejectedOpouts dag (list "t") origins == [t]
-- the latest decision wins: reject, then allow, accepts it
#guard rejectedOpouts dag (list "t\n!t") origins == []
-- and allow, then reject, refuses it
#guard rejectedOpouts dag (list "!t\nt") origins == [t]
-- a rejected issuance taints everything built on it
#guard rejectedOpouts dag (list "gi") [gi, c, p, t] == [gi, c, p, t]
-- an allowed opout shields what is built on it, not its siblings or ancestors
#guard rejectedOpouts dag (list "gi\n!t") [gi, c, p, t] == [gi, c, p]
-- blank lines are skipped, unknown lines are counted as invalid
#guard (RejectList.parse parseName "  t \n\nnonsense\n!c").2 == 1
#guard (list "  t \n\nnonsense\n!c").allows c

-- EVM list: pending rejects count at once, pending allows are ignored
def evm : EvmRejectList :=
  { entries := [⟨"t", true⟩, ⟨"t", false⟩, ⟨"c", false⟩, ⟨"p", true⟩], finalized := 2 }
#guard (RejectList.fromEvm parseName evm).map (fun l => (l.rejects t, l.allows t, l.allows c, l.rejects p))
  == .ok (false, true, false, true)
#guard (RejectList.fromEvm parseName { evm with finalized := 9 }) matches .error (.finalizedOutOfRange 9 4)

-- a URL body must be ASCII and at most 7900000 bytes
#guard maxRejectListSize == 7900000
#guard checkRejectListBody 200 "t" == .ok "t"
#guard checkRejectListBody 302 "t" == .error (.httpStatus 302)
#guard checkRejectListBody 200 "é" == .error .notAscii

end Rgb.Examples.RejectListScenario
