import Rgb.Consensus.Ids

/-!
# Type numbers of the standard schemas

Global state, owned state, transition and metadata type numbers, and the error
codes that the schema scripts report (`rgb-schemas`).
-/

namespace Rgb.Schemas

/-! ## Global state types -/
def gsNominal : GlobalStateType := ⟨2000⟩
def gsTerms : GlobalStateType := ⟨2001⟩
def gsIssuedSupply : GlobalStateType := ⟨2010⟩
def gsMaxSupply : GlobalStateType := ⟨2011⟩
def gsRejectListUrl : GlobalStateType := ⟨2012⟩
def gsLinkedFromContract : GlobalStateType := ⟨2013⟩
def gsLinkedToContract : GlobalStateType := ⟨2014⟩
def gsBurnedAsset : GlobalStateType := ⟨2015⟩
def gsBurnedInflation : GlobalStateType := ⟨2016⟩
def gsTokens : GlobalStateType := ⟨2102⟩
def gsEngravings : GlobalStateType := ⟨2103⟩
def gsAttach : GlobalStateType := ⟨2104⟩
def gsArt : GlobalStateType := ⟨3000⟩
def gsName : GlobalStateType := ⟨3001⟩
def gsDetails : GlobalStateType := ⟨3004⟩
def gsPrecision : GlobalStateType := ⟨3005⟩
def gsPubkey : GlobalStateType := ⟨3006⟩
def gsBridgedSupply : GlobalStateType := ⟨3007⟩
def gsBridgeLocation : GlobalStateType := ⟨3008⟩
def gsBurnReason : GlobalStateType := ⟨3009⟩
def gsRejectList : GlobalStateType := ⟨3010⟩
def gsTicker : GlobalStateType := ⟨3011⟩

/-! ## Owned state (assignment) types -/
def osAsset : AssignmentType := ⟨4000⟩
def osInflation : AssignmentType := ⟨4010⟩
def osLink : AssignmentType := ⟨4012⟩
def osMint : AssignmentType := ⟨4013⟩

/-! ## Transition types -/
def tsInflation : TransitionType := ⟨8000⟩
def tsBurn : TransitionType := ⟨8010⟩
def tsLink : TransitionType := ⟨8012⟩
def tsMint : TransitionType := ⟨8013⟩
def tsPropagate : TransitionType := ⟨8014⟩
def tsTransferInflation : TransitionType := ⟨8015⟩
def tsTransferLink : TransitionType := ⟨8016⟩
def tsTransfer : TransitionType := ⟨10000⟩

/-! ## Metadata types -/
def msAllowedInflation : MetaType := ⟨1000⟩
def msBeforeBlock : MetaType := ⟨1003⟩

/-! ## Script error codes (`ERRNO_*`) -/
def errnoNonEqualInOut : UInt8 := 0
def errnoIssuedMismatch : UInt8 := 1
def errnoNonFractional : UInt8 := 10
def errnoMissingPubkey : UInt8 := 20
def errnoInvalidSignature : UInt8 := 21
def errnoInflationMismatch : UInt8 := 30
def errnoInflationExceedsAllowance : UInt8 := 31
def errnoBurnMismatch : UInt8 := 40
def errnoBurnZero : UInt8 := 41

end Rgb.Schemas
