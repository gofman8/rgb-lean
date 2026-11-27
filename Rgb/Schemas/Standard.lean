import Rgb.Consensus.Validation
import Rgb.Schemas.Numbers

/-!
# The standard schemas

The six schemas of `rgb-schemas`, with their validation scripts written out
instruction by instruction (entry offsets and jump targets as in the source).

| schema | what it is |
|---|---|
| NIA | non-inflatable fungible asset: fixed supply, issued at genesis |
| CFA | collectible fungible asset: NIA with name/details/precision as separate globals |
| UDA | unique digital asset: one token, fraction 1, moved whole |
| IFA | inflatable fungible asset: inflation rights, burns, a reject list URL, contract links |
| BFA | bridged fungible asset: supply minted against locks on an EVM bridge |
| PFA | permissioned fungible asset: every transfer signed by the issuer key |

rgb-lib issues and accepts NIA, UDA, CFA, IFA and BFA; PFA exists in rgb-schemas only.
-/

namespace Rgb.Schemas

open Rgb

/-! ## Scripts -/

/-- Shared by NIA and CFA. Transfer at offset 0, genesis at offset 9. -/
def niaLib : Lib where
  id := "alu:q~CZ0ovt-UN9eBlc-VMn86mz-Kfd3ywu-f7~9jTB-k6A8tiY#japan-nylon-center"
  code :=
    [ .put .a8 0 errnoNonEqualInOut.toNat, .svs osAsset, .test, .ret
    , .put .a8 0 errnoIssuedMismatch.toNat, .put .a8 1 0, .put .a16 0 0
    , .ldg gsIssuedSupply 1 0, .extr 0 .a64 0 0, .sas osAsset, .test, .ret ]

def niaTransferSite : LibSite := ⟨niaLib.id, 0⟩
def niaGenesisSite : LibSite := ⟨niaLib.id, 9⟩

/-- UDA: transfer at 0, genesis at 11, shared check at 23. -/
def udaLib : Lib where
  id := "alu:NhZxdclE-0421s28-MHR~kz~-SadRGjv-iUElfKp-6DiE1KU#metal-coral-charter"
  code :=
    [ .put .a16 0 0, .ldp osAsset 0 0, .jmp 23
    , .put .a16 0 0, .put .a8 1 0, .ldg gsTokens 1 0
    , .put .a8 0 errnoNonEqualInOut.toNat, .extr 0 .a32 0 0, .put .a16 1 0, .lds osAsset 1 1
    , .extr 1 .a32 1 0, .eqn .a32 0 1, .test
    , .put .a8 0 errnoNonFractional.toNat, .put .a16 2 4, .extr 1 .a64 0 2, .put .a64 1 1
    , .eqn .a64 0 1, .test ]

def udaTransferSite : LibSite := ⟨udaLib.id, 0⟩
def udaGenesisSite : LibSite := ⟨udaLib.id, 11⟩

def ifaGenesisLib : Lib where
  id := "alu:ifa-genesis"
  code :=
    [ .put .a8 1 0, .put .a16 0 0, .put .a8 0 errnoIssuedMismatch.toNat
    , .ldg gsIssuedSupply 1 0, .extr 0 .a64 0 0, .sas osAsset, .test
    , .put .a8 0 errnoInflationMismatch.toNat, .ldg gsMaxSupply 1 1, .extr 1 .a64 1 0
    , .subUc .a64 1 0, .test, .sas osInflation, .test, .ret ]

def ifaTransferLib : Lib where
  id := "alu:ifa-transfer"
  code := [ .put .a8 0 errnoNonEqualInOut.toNat, .svs osAsset, .test, .ret ]

def ifaTransferInflationLib : Lib where
  id := "alu:ifa-transfer-inflation"
  code := [ .put .a8 0 errnoNonEqualInOut.toNat, .svs osInflation, .test, .ret ]

def ifaInflationLib : Lib where
  id := "alu:ifa-inflation"
  code :=
    [ .put .a8 1 0, .put .a16 0 0, .put .a8 0 errnoIssuedMismatch.toNat
    , .ldg gsIssuedSupply 1 0, .extr 0 .a64 0 0, .sas osAsset, .test, .cpy .a64 0 1
    , .put .a8 0 errnoInflationMismatch.toNat, .ldm msAllowedInflation 0, .extr 0 .a64 0 0
    , .sas osInflation, .test
    , .put .a8 0 errnoInflationExceedsAllowance.toNat, .addUc .a64 1 0, .test
    , .sps osInflation, .test, .ret ]

/-- One 42-byte burn check: `burned` absent with inputs fails with 41; present,
zero or not the input sum fails with 40. `skip` is the offset of the `sps`. -/
def burnCheck (burned : GlobalStateType) (skip : Nat) : List Instr :=
  [ .put .a8 0 errnoBurnZero.toNat, .put .a64 0 0, .cng burned 1, .ifz .a8 1, .jif skip, .inv
  , .put .a8 0 errnoBurnMismatch.toNat, .put .a8 1 0, .ldg burned 1 0, .put .a16 0 0
  , .extr 0 .a64 0 0, .test, .ifz .a64 0, .inv, .test ]

def ifaBurnLib : Lib where
  id := "alu:ifa-burn"
  code := burnCheck gsBurnedAsset 42 ++ [.sps osAsset, .test]
    ++ burnCheck gsBurnedInflation 88 ++ [.sps osInflation, .test, .ret]

def bfaTransferLib : Lib where
  id := "alu:bfa-transfer"
  code := [ .put .a8 0 errnoNonEqualInOut.toNat, .svs osAsset, .test ]

def bfaMintLib : Lib where
  id := "alu:bfa-mint"
  code :=
    [ .put .a8 0 errnoIssuedMismatch.toNat, .put .a8 1 0, .put .a16 0 0
    , .ldg gsIssuedSupply 1 0, .extr 0 .a64 0 0, .sas osAsset, .test
    , .ldm msBeforeBlock 1, .extr 1 .a64 1 0, .test, .plc 0 1, .test, .ret ]

def bfaBurnLib : Lib where
  id := "alu:bfa-burn"
  code := burnCheck gsBurnedAsset 42 ++ [.sps osAsset, .test]

def pfaGenesisLib : Lib where
  id := "alu:pfa-genesis"
  code :=
    [ .put .a8 0 errnoIssuedMismatch.toNat, .put .a8 1 0, .put .a16 0 0
    , .ldg gsIssuedSupply 1 0, .extr 0 .a64 0 0, .sas osAsset, .test, .ret ]

def pfaTransitionLib : Lib where
  id := "alu:pfa-transition"
  code :=
    [ .put .a8 0 errnoNonEqualInOut.toNat, .svs osAsset, .test
    , .put .a8 0 errnoMissingPubkey.toNat, .put .a32 0 0, .ldc gsPubkey 0 0
    , .put .a8 0 errnoInvalidSignature.toNat, .vts 0, .test, .ret ]

/-! ## Schema helpers -/

def global (sem : SemId) (name : String) (many : Bool := false) : GlobalDetails :=
  ⟨if many then .many sem else .once sem, name⟩

def asset : AssignmentDetails := ⟨.fungible .unsigned64Bit, "assetOwner", tsTransfer⟩
def inflationAllowance : AssignmentDetails := ⟨.fungible .unsigned64Bit, "inflationAllowance", tsTransferInflation⟩
def linkRight : AssignmentDetails := ⟨.declarative, "linkRight", tsTransferLink⟩
def mintRight : AssignmentDetails := ⟨.declarative, "mintRight", tsPropagate⟩

def transferOf (t : AssignmentType) (occ : Occurrences) (site : Option LibSite) : TransitionSchema :=
  { inputs := OrdMap.ofList [(t, occ)], assignments := OrdMap.ofList [(t, occ)], validator := site }

/-! ## NIA -/

def nia : Schema where
  name := "NonInflatableAsset"
  globalTypes := OrdMap.ofList
    [ (gsNominal, global .assetSpec "spec"), (gsTerms, global .contractTerms "terms")
    , (gsIssuedSupply, global .amount "issuedSupply") ]
  ownedTypes := OrdMap.ofList [(osAsset, asset)]
  genesis :=
    { globals := OrdMap.ofList [(gsNominal, .once), (gsTerms, .once), (gsIssuedSupply, .once)]
      assignments := OrdMap.ofList [(osAsset, .onceOrMore)]
      validator := some niaGenesisSite }
  transitions := OrdMap.ofList [(tsTransfer, ⟨transferOf osAsset .onceOrMore (some niaTransferSite), "transfer"⟩)]
  defaultAssignment := some osAsset

/-! ## CFA -/

def cfa : Schema where
  name := "CollectibleFungibleAsset"
  globalTypes := OrdMap.ofList
    [ (gsArt, global .article "art"), (gsName, global .name "name"), (gsDetails, global .details "details")
    , (gsPrecision, global .precision "precision"), (gsTerms, global .contractTerms "terms")
    , (gsIssuedSupply, global .amount "issuedSupply") ]
  ownedTypes := OrdMap.ofList [(osAsset, asset)]
  genesis :=
    { globals := OrdMap.ofList
        [ (gsArt, .noneOrOnce), (gsName, .once), (gsDetails, .noneOrOnce), (gsPrecision, .once)
        , (gsTerms, .once), (gsIssuedSupply, .once) ]
      assignments := OrdMap.ofList [(osAsset, .onceOrMore)]
      validator := some niaGenesisSite }
  transitions := OrdMap.ofList [(tsTransfer, ⟨transferOf osAsset .onceOrMore (some niaTransferSite), "transfer"⟩)]
  defaultAssignment := some osAsset

/-! ## UDA -/

def uda : Schema where
  name := "UniqueDigitalAsset"
  globalTypes := OrdMap.ofList
    [ (gsNominal, global .assetSpec "spec"), (gsTerms, global .contractTerms "terms")
    , (gsTokens, global .tokenData "tokens"), (gsAttach, global .attachmentType "attachmentTypes") ]
  ownedTypes := OrdMap.ofList [(osAsset, ⟨.structured .allocation, "assetOwner", tsTransfer⟩)]
  genesis :=
    { globals := OrdMap.ofList [(gsNominal, .once), (gsTerms, .once), (gsTokens, .once), (gsAttach, .noneOrOnce)]
      assignments := OrdMap.ofList [(osAsset, .once)]
      validator := some udaGenesisSite }
  transitions := OrdMap.ofList [(tsTransfer, ⟨transferOf osAsset .once (some udaTransferSite), "transfer"⟩)]
  defaultAssignment := some osAsset

/-! ## IFA -/

def ifa : Schema where
  name := "InflatableFungibleAsset"
  metaTypes := OrdMap.ofList [(msAllowedInflation, ⟨.amount, "allowedInflation"⟩)]
  globalTypes := OrdMap.ofList
    [ (gsNominal, global .assetSpec "spec"), (gsTerms, global .contractTerms "terms")
    , (gsIssuedSupply, global .amount "issuedSupply" true), (gsMaxSupply, global .amount "maxSupply")
    , (gsRejectListUrl, global .rejectListUrl "rejectListUrl")
    , (gsLinkedFromContract, global .contractId "linkedFromContract")
    , (gsLinkedToContract, global .contractId "linkedToContract")
    , (gsBurnedAsset, global .amount "burnedAsset" true)
    , (gsBurnedInflation, global .amount "burnedInflation" true)
    , (gsBurnReason, global .burnReason "burnReason" true) ]
  ownedTypes := OrdMap.ofList [(osAsset, asset), (osInflation, inflationAllowance), (osLink, linkRight)]
  genesis :=
    { globals := OrdMap.ofList
        [ (gsNominal, .once), (gsTerms, .once), (gsIssuedSupply, .once), (gsMaxSupply, .once)
        , (gsRejectListUrl, .noneOrOnce), (gsLinkedFromContract, .noneOrOnce) ]
      assignments := OrdMap.ofList [(osAsset, .noneOrMore), (osInflation, .noneOrMore), (osLink, .noneOrOnce)]
      validator := some ⟨ifaGenesisLib.id, 0⟩ }
  transitions := OrdMap.ofList
    [ (tsTransfer, ⟨transferOf osAsset .noneOrMore (some ⟨ifaTransferLib.id, 0⟩), "transfer"⟩)
    , (tsTransferInflation,
        ⟨transferOf osInflation .noneOrMore (some ⟨ifaTransferInflationLib.id, 0⟩), "transferInflation"⟩)
    , (tsTransferLink, ⟨transferOf osLink .once none, "transferLink"⟩)
    , (tsInflation, ⟨{ metadata := OrdSet.ofList [msAllowedInflation]
                       globals := OrdMap.ofList [(gsIssuedSupply, .once)]
                       inputs := OrdMap.ofList [(osInflation, .onceOrMore)]
                       assignments := OrdMap.ofList [(osAsset, .onceOrMore), (osInflation, .noneOrMore)]
                       validator := some ⟨ifaInflationLib.id, 0⟩ }, "inflate"⟩)
    , (tsBurn, ⟨{ globals := OrdMap.ofList
                    [(gsBurnedAsset, .noneOrOnce), (gsBurnedInflation, .noneOrOnce), (gsBurnReason, .noneOrOnce)]
                  inputs := OrdMap.ofList [(osAsset, .noneOrMore), (osInflation, .noneOrMore), (osLink, .noneOrOnce)]
                  validator := some ⟨ifaBurnLib.id, 0⟩ }, "burn"⟩)
    , (tsLink, ⟨{ globals := OrdMap.ofList [(gsLinkedToContract, .once)]
                  inputs := OrdMap.ofList [(osLink, .once)] }, "link"⟩) ]
  defaultAssignment := some osAsset

/-! ## BFA -/

def bfa : Schema where
  name := "BridgedFungibleAsset"
  metaTypes := OrdMap.ofList [(msBeforeBlock, ⟨.blockNumber, "beforeBlock"⟩)]
  globalTypes := OrdMap.ofList
    [ (gsTicker, global .unicodeTicker "ticker"), (gsName, global .name "name")
    , (gsDetails, global .details "details"), (gsPrecision, global .precision "precision")
    , (gsTerms, global .contractTerms "terms"), (gsIssuedSupply, global .amount "issuedSupply" true)
    , (gsBurnedAsset, global .amount "burnedAsset" true), (gsRejectList, global .rejectListLocation "rejectList")
    , (gsLinkedFromContract, global .contractId "linkedFromContract")
    , (gsLinkedToContract, global .contractId "linkedToContract")
    , (gsBridgeLocation, global .bridgeLocation "bridgeLocation")
    , (gsBurnReason, global .burnReason "burnReason" true) ]
  ownedTypes := OrdMap.ofList [(osAsset, asset), (osMint, mintRight), (osLink, linkRight)]
  genesis :=
    { globals := OrdMap.ofList
        [ (gsTicker, .once), (gsName, .once), (gsDetails, .noneOrOnce), (gsPrecision, .once)
        , (gsTerms, .once), (gsRejectList, .noneOrOnce), (gsLinkedFromContract, .noneOrOnce)
        , (gsBridgeLocation, .once) ]
      assignments := OrdMap.ofList [(osMint, .onceOrMore), (osLink, .noneOrOnce)] }
  transitions := OrdMap.ofList
    [ (tsTransfer, ⟨transferOf osAsset .noneOrMore (some ⟨bfaTransferLib.id, 0⟩), "transfer"⟩)
    , (tsTransferLink, ⟨transferOf osLink .once none, "transferLink"⟩)
    , (tsPropagate, ⟨{ inputs := OrdMap.ofList [(osMint, .once)]
                       assignments := OrdMap.ofList [(osMint, .onceOrMore)] }, "propagate"⟩)
    , (tsMint, ⟨{ metadata := OrdSet.ofList [msBeforeBlock]
                  globals := OrdMap.ofList [(gsIssuedSupply, .once)]
                  inputs := OrdMap.ofList [(osMint, .once)]
                  assignments := OrdMap.ofList [(osAsset, .onceOrMore)]
                  validator := some ⟨bfaMintLib.id, 0⟩ }, "mint"⟩)
    , (tsBurn, ⟨{ globals := OrdMap.ofList [(gsBurnedAsset, .noneOrOnce), (gsBurnReason, .noneOrOnce)]
                  inputs := OrdMap.ofList [(osAsset, .noneOrMore), (osMint, .noneOrMore), (osLink, .noneOrOnce)]
                  validator := some ⟨bfaBurnLib.id, 0⟩ }, "burn"⟩)
    , (tsLink, ⟨{ globals := OrdMap.ofList [(gsLinkedToContract, .once)]
                  inputs := OrdMap.ofList [(osLink, .once)] }, "link"⟩) ]
  defaultAssignment := some osAsset

/-! ## PFA -/

def pfa : Schema where
  name := "PermissionedFungibleAsset"
  globalTypes := OrdMap.ofList
    [ (gsNominal, global .assetSpec "spec"), (gsTerms, global .contractTerms "terms")
    , (gsIssuedSupply, global .amount "issuedSupply"), (gsPubkey, global .pubkey "pubkey") ]
  ownedTypes := OrdMap.ofList [(osAsset, asset)]
  genesis :=
    { globals := OrdMap.ofList [(gsNominal, .once), (gsTerms, .once), (gsIssuedSupply, .once), (gsPubkey, .once)]
      assignments := OrdMap.ofList [(osAsset, .onceOrMore)]
      validator := some ⟨pfaGenesisLib.id, 0⟩ }
  transitions := OrdMap.ofList
    [(tsTransfer, ⟨transferOf osAsset .onceOrMore (some ⟨pfaTransitionLib.id, 0⟩), "transfer"⟩)]
  defaultAssignment := some osAsset

/-! ## Rules -/

def niaRules : SchemaRules := ⟨nia, [niaLib]⟩
def cfaRules : SchemaRules := ⟨cfa, [niaLib]⟩
def udaRules : SchemaRules := ⟨uda, [udaLib]⟩
def ifaRules : SchemaRules :=
  ⟨ifa, [ifaGenesisLib, ifaTransferLib, ifaTransferInflationLib, ifaInflationLib, ifaBurnLib]⟩
def bfaRules : SchemaRules := ⟨bfa, [bfaTransferLib, bfaMintLib, bfaBurnLib]⟩
def pfaRules : SchemaRules := ⟨pfa, [pfaGenesisLib, pfaTransitionLib]⟩

def all : List SchemaRules := [niaRules, cfaRules, udaRules, ifaRules, bfaRules, pfaRules]

/-- Rules of a schema id, among the standard schemas. -/
def rulesOf? (id : SchemaId) : Option SchemaRules := all.find? (·.schema.schemaId == id)

/-- Name of the burned-amount global of an assignment type (`burn_global_by_assignment`). -/
def burnGlobalByAssignment? (t : AssignmentType) : Option GlobalStateType :=
  if t == osAsset then some gsBurnedAsset
  else if t == osInflation then some gsBurnedInflation
  else none

end Rgb.Schemas
