import Rgb.Ops.Witness
import Rgb.Examples.Validation

/-!
# PSBT coloring scenarios
-/

namespace Rgb.Examples.PsbtScenario

open Rgb Rgb.Schemas Rgb.Examples.NiaValidation

def base : RgbPsbt := { tx := mkTx [utxoA] [⟨9000, .p2wpkh "issuer"⟩] }

-- a transition pushed twice is added once
#guard ((base.pushTransitions [t1, t1]).map (·.2)) == .ok 1
-- two transitions spending the same opout: a double spend, nothing is pushed
#guard ((base.pushTransitions [t1, t1b]).map (·.2)) matches .error .doubleSpend
-- with no OP_RETURN output, the host is a new output at index 0
#guard base.setOpretHost.opretHost == some 0 && base.setOpretHost.tx.outputs.length == 2
-- committing needs transitions, a close method and a host; then it is final
def pushed : RgbPsbt := ((base.pushTransitions [t1]).toOption.get!).1
#guard ({ tx := base.tx } : RgbPsbt).commit matches .error .noContracts
#guard pushed.commit matches .error .noCloseMethod
#guard ({ pushed with closeMethod := some .opretFirst } : RgbPsbt).commit matches .error (.noHostOutput .opretFirst)
def ready : RgbPsbt := { pushed.setOpretHost with closeMethod := some .opretFirst, mpcEntropy := some 5 }
#guard ({ ready with modifiable := true } : RgbPsbt).commit matches .error .txOutputsModifiable
#guard (ready.commit.bind fun (p, _) => p.commit) matches .error .finalized
-- the committed witness carries the bundle's commitment: a valid transfer
#guard (ready.commit.map fun (_, f) => (f.witnessBundle? cid).isSome) == .ok true

end Rgb.Examples.PsbtScenario
