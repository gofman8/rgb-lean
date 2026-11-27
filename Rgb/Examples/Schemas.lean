import Rgb.Schemas.Standard
import Rgb.Ops.Witness

/-!
# Schema scenarios

The rules of each standard schema, checked on small histories: what its scripts
accept and the error code of each refusal.
-/

namespace Rgb.Examples.SchemaScenarios

open Rgb Rgb.Schemas

/-! ## Support -/

def coin (n : Nat) : Outpoint := ⟨⟨Digest.of Tag.txid ["coin", encode n]⟩, 0⟩
def cfg : ValidationConfig := { chainNet := .bitcoinRegtest }

def gseal (n : Nat) : BuilderSeal GenesisSeal := .revealed ⟨(coin n).txid, 0, n.toUInt64⟩
def wseal (vout : Nat) : BuilderSeal GraphSeal := .revealed (GraphSeal.witnessVout vout.toUInt32 vout.toUInt64)

/-- A witness bundle spending `spend`, committing the transitions of one contract. -/
def witness (cid : ContractId) (spend : List Outpoint) (ts : List Transition) : WitnessBundle :=
  let tx := mkTx spend [⟨0, .opReturn none⟩, ⟨546, .p2wpkh "a"⟩, ⟨546, .p2wpkh "b"⟩, ⟨546, .p2wpkh "c"⟩]
  ((commitBundles tx [(cid, TransitionBundle.ofTransitions ts)] 1).toOption.bind
    (·.witnessBundle? cid)).getD default

/-- Validate genesis plus witness bundles, resolving witnesses as tentative. -/
def check (rules : SchemaRules) (g : Genesis) (wbs : List WitnessBundle) : Except ValidationError Status :=
  let c : Consignment := { transfer := !wbs.isEmpty, genesis := g, bundles := wbs }
  let r := (Chain.resolver {} .bitcoinRegtest).withConsignmentTxes (wbs.map (·.tx))
  (c.validate (!wbs.isEmpty) rules r cfg).map (·.status)

def failsWith (r : Except ValidationError Status) (opid : OpId) (errno : UInt8) : Bool :=
  r == .error (.invalidConsignment (.scriptFailure opid (some errno)))

def spec : AssetSpec := ⟨⟨"TKN"⟩, ⟨"Token"⟩, none, .indivisible⟩
def terms : ContractTerms := ⟨⟨""⟩, none⟩
def amt (n : UInt64) : RevealedData := ⟨.amount n⟩

/-! ## IFA: inflation, burn, link -/

def ifaGenesis (issued maxS allowance : UInt64) : Genesis :=
  { schemaId := ifa.schemaId, timestamp := 1713261744, chainNet := .bitcoinRegtest
    globals := OrdMap.ofList
      [ (gsNominal, [⟨.assetSpec spec⟩]), (gsTerms, [⟨.contractTerms terms⟩])
      , (gsIssuedSupply, [amt issued]), (gsMaxSupply, [amt maxS]) ]
    assignments := OrdMap.ofList
      [ (osAsset, .fungible [(gseal 1, ⟨issued⟩)]), (osInflation, .fungible [(gseal 2, ⟨allowance⟩)])
      , (osLink, .declarative [gseal 3]) ] }

def ig : Genesis := ifaGenesis 600 1000 400
def icid : ContractId := ig.contractId

-- genesis: issued 600 of at most 1000, so the inflation allowance is 400
#guard check ifaRules ig [] matches .ok _
-- an allowance that does not equal max - issued is refused (error 30)
#guard failsWith (check ifaRules (ifaGenesis 600 1000 300) []) (ifaGenesis 600 1000 300).id 30
-- issued above the max supply is refused (error 30)
#guard failsWith (check ifaRules (ifaGenesis 1100 1000 1) []) (ifaGenesis 1100 1000 1).id 30

/-- Inflate: spend the 400 allowance, issue `issued`, keep `left` as allowance. -/
def inflate (issued outAsset left allowedMeta : UInt64) : Transition :=
  { contractId := icid, transitionType := tsInflation, inputs := [⟨ig.id, osInflation, 0⟩]
    metadata := OrdMap.ofList [(msAllowedInflation, amt allowedMeta)]
    globals := OrdMap.ofList [(gsIssuedSupply, [amt issued])]
    assignments := OrdMap.ofList
      [(osAsset, .fungible [(wseal 1, ⟨outAsset⟩)]), (osInflation, .fungible [(wseal 2, ⟨left⟩)])] }

def inflW (t : Transition) : WitnessBundle := witness icid [coin 2] [t]

-- inflation rights are conserved: 400 = 100 issued + 300 left
#guard check ifaRules ig [inflW (inflate 100 100 300 300)] matches .ok _
-- the new asset must equal the issued supply of the inflation (error 1)
#guard failsWith (check ifaRules ig [inflW (inflate 100 90 300 300)]) (inflate 100 90 300 300).id 1
-- the remaining allowance must equal the declared one (error 30)
#guard failsWith (check ifaRules ig [inflW (inflate 100 100 300 200)]) (inflate 100 100 300 200).id 30
-- issued plus allowed may not exceed the spent allowance (error 31)
#guard failsWith (check ifaRules ig [inflW (inflate 200 200 300 300)]) (inflate 200 200 300 300).id 31
-- an inflation needs its metadata
def inflNoMeta : Transition := { inflate 100 100 300 300 with metadata := {} }
#guard check ifaRules ig [inflW inflNoMeta]
  == .error (.invalidConsignment (.schemaNoMetadata inflNoMeta.id msAllowedInflation))

/-- Burn the 600 asset allocation with a declared burned amount. -/
def burn (burned : Option UInt64) : Transition :=
  { contractId := icid, transitionType := tsBurn, inputs := [⟨ig.id, osAsset, 0⟩]
    globals := match burned with
      | some b => OrdMap.ofList [(gsBurnedAsset, [amt b])]
      | none => {} }

def burnW (t : Transition) : WitnessBundle := witness icid [coin 1] [t]

-- a burn declares exactly what it destroys
#guard check ifaRules ig [burnW (burn (some 600))] matches .ok _
-- a burn without the burned amount is refused (error 41)
#guard failsWith (check ifaRules ig [burnW (burn none)]) (burn none).id 41
-- a wrong or zero burned amount is refused (error 40)
#guard failsWith (check ifaRules ig [burnW (burn (some 500))]) (burn (some 500)).id 40
#guard failsWith (check ifaRules ig [burnW (burn (some 0))]) (burn (some 0)).id 40

/-- Link: spend the link right and name the linked contract. -/
def other : ContractId := ⟨Digest.of "contract" ["other"]⟩
def link : Transition :=
  { contractId := icid, transitionType := tsLink, inputs := [⟨ig.id, osLink, 0⟩]
    globals := OrdMap.ofList [(gsLinkedToContract, [⟨.contractId other.d⟩])] }
#guard check ifaRules ig [witness icid [coin 3] [link]] matches .ok _
-- the link right is spent by the link: linking twice needs a second right
def link2 : Transition := { link with nonce := 7 }
#guard check ifaRules ig [witness icid [coin 3] [link], witness icid [coin 3] [link2]]
  == .error (.invalidConsignment (.noPrevState link2.id ⟨ig.id, osLink, 0⟩))

/-! ## UDA: one token, moved whole -/

def udaGenesis (index : UInt32) (fraction : UInt64) : Genesis :=
  { schemaId := uda.schemaId, timestamp := 1713261744, chainNet := .bitcoinRegtest
    globals := OrdMap.ofList
      [ (gsNominal, [⟨.assetSpec spec⟩]), (gsTerms, [⟨.contractTerms terms⟩])
      , (gsTokens, [⟨.tokenData { index := ⟨0⟩ }⟩]) ]
    assignments := OrdMap.ofList [(osAsset, .structured [(gseal 4, ⟨.allocation ⟨index⟩ fraction⟩)])] }

def ug : Genesis := udaGenesis 0 1
#guard check udaRules ug [] matches .ok _
-- the allocation names the token of the contract (error 0) with fraction 1 (error 10)
#guard failsWith (check udaRules (udaGenesis 1 1) []) (udaGenesis 1 1).id 0
#guard failsWith (check udaRules (udaGenesis 0 2) []) (udaGenesis 0 2).id 10

def udaMove (index : UInt32) (fraction : UInt64) : Transition :=
  { contractId := ug.contractId, transitionType := tsTransfer, inputs := [⟨ug.id, osAsset, 0⟩]
    assignments := OrdMap.ofList [(osAsset, .structured [(wseal 1, ⟨.allocation ⟨index⟩ fraction⟩)])] }

#guard check udaRules ug [witness ug.contractId [coin 4] [udaMove 0 1]] matches .ok _
#guard failsWith (check udaRules ug [witness ug.contractId [coin 4] [udaMove 1 1]]) (udaMove 1 1).id 0
#guard failsWith (check udaRules ug [witness ug.contractId [coin 4] [udaMove 0 2]]) (udaMove 0 2).id 10

/-! ## BFA: mints against bridge locks -/

def bridge : EvmContract := ⟨1, ⟨List.replicate 20 7⟩⟩
def bg : Genesis :=
  { schemaId := bfa.schemaId, timestamp := 1713261744, chainNet := .bitcoinRegtest
    globals := OrdMap.ofList
      [ (gsTicker, [⟨.unicodeTicker ⟨"₿TC"⟩⟩]), (gsName, [⟨.name ⟨"Bridged"⟩⟩])
      , (gsPrecision, [⟨.precision .indivisible⟩]), (gsTerms, [⟨.contractTerms terms⟩])
      , (gsBridgeLocation, [⟨.bridgeLocation (.evm bridge)⟩]) ]
    assignments := OrdMap.ofList [(osMint, .declarative [gseal 5, gseal 6])] }
def bcid : ContractId := bg.contractId

-- a BFA genesis issues nothing: it grants mint rights and has no script
#guard check bfaRules bg [] matches .ok _

def mint (issued outAsset : UInt64) : Transition :=
  { contractId := bcid, transitionType := tsMint, inputs := [⟨bg.id, osMint, 0⟩]
    metadata := OrdMap.ofList [(msBeforeBlock, ⟨.blockNumber ⟨1000⟩⟩)]
    globals := OrdMap.ofList [(gsIssuedSupply, [amt issued])]
    assignments := OrdMap.ofList [(osAsset, .fungible [(wseal 1, ⟨outAsset⟩)])] }

def mintW : WitnessBundle := witness bcid [coin 5] [mint 500 500]
def bfaTransfer : Consignment := { transfer := true, genesis := bg, bundles := [mintW] }
def bfaResolver : Resolver := (Chain.resolver {} .bitcoinRegtest).withConsignmentTxes [mintW.tx]

/-- The claim a mint pushes: a bridge lock of the minted amount, for this
operation in this witness, recorded before block 1000. -/
def mintClaim : Claim := .lock (mint 500 500).id mintW.tx.txid 500 1000

-- a mint cannot be accepted without confirming its claim
#guard (bfaTransfer.validate true bfaRules bfaResolver cfg).map (·.status) == .error (.pendingClaims 1)
-- once the bridge lock is confirmed, the mint is valid
#guard (bfaTransfer.validateWithClaims true bfaRules bfaResolver cfg (· == mintClaim)) matches .ok _
-- an unconfirmed lock refuses it, naming the mint
#guard (bfaTransfer.validateWithClaims true bfaRules bfaResolver cfg (fun _ => false))
  matches .error (.inr _)
-- the minted amount equals the issued supply (error 1)
#guard failsWith (check bfaRules bg [witness bcid [coin 5] [mint 500 400]]) (mint 500 400).id 1

/-- Propagate: one mint right becomes three. -/
def propagate : Transition :=
  { contractId := bcid, transitionType := tsPropagate, inputs := [⟨bg.id, osMint, 1⟩]
    assignments := OrdMap.ofList [(osMint, .declarative [wseal 1, wseal 2, wseal 3])] }
#guard check bfaRules bg [witness bcid [coin 6] [propagate]] matches .ok _

/-! ## PFA: issuer-signed transfers -/

def pg : Genesis :=
  { schemaId := pfa.schemaId, timestamp := 1713261744, chainNet := .bitcoinRegtest
    globals := OrdMap.ofList
      [ (gsNominal, [⟨.assetSpec spec⟩]), (gsTerms, [⟨.contractTerms terms⟩])
      , (gsIssuedSupply, [amt 100]), (gsPubkey, [⟨.pubkey (pubkeyOf "issuer")⟩]) ]
    assignments := OrdMap.ofList [(osAsset, .fungible [(gseal 7, ⟨100⟩)])] }

def pfaMove : Transition :=
  { contractId := pg.contractId, transitionType := tsTransfer, inputs := [⟨pg.id, osAsset, 0⟩]
    assignments := OrdMap.ofList [(osAsset, .fungible [(wseal 1, ⟨100⟩)])] }
def signedBy (k : String) : Transition := { pfaMove with signature := some (Signature.sign k pfaMove.id.d) }

#guard check pfaRules pg [] matches .ok _
-- a transfer signed by the issuer key is valid
#guard check pfaRules pg [witness pg.contractId [coin 7] [signedBy "issuer"]] matches .ok _
-- unsigned or signed by another key: refused (error 21)
#guard failsWith (check pfaRules pg [witness pg.contractId [coin 7] [pfaMove]]) pfaMove.id 21
#guard failsWith (check pfaRules pg [witness pg.contractId [coin 7] [signedBy "mallory"]]) pfaMove.id 21

/-! ## Script layout -/

-- entry offsets and lengths match the rgb-schemas assertions
#guard udaLib.offsets.contains 11 && udaLib.offsets.contains 23
#guard ifaBurnLib.byteLen == 93 && ifaBurnLib.offsets.contains 42 && ifaBurnLib.offsets.contains 88
#guard bfaBurnLib.byteLen == 46
-- every standard schema's rules are consistent
#guard all.all fun r => (SchemaRules.make r.schema r.scripts).toOption.isSome

end Rgb.Examples.SchemaScenarios
