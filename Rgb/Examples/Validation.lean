import Rgb.Schemas.Standard
import Rgb.Ops.Witness

/-!
# Consensus validation scenarios (NIA)

An issuer creates a non-inflatable asset on one of its outputs and transfers
600 of 1000 units to a receiver's concealed seal, keeping 400 as change on an
output of the witness transaction. Each check below states what consensus
accepts or refuses, and why.
-/

namespace Rgb.Examples.NiaValidation

open Rgb Rgb.Schemas

def fundA : Chain × Outpoint := Chain.fund {} (.p2wpkh "issuer") 10000 0
def fundB : Chain × Outpoint := fundA.1.fund (.p2wpkh "receiver") 1000 1
def chain : Chain := fundB.1
def utxoA : Outpoint := fundA.2
def utxoB : Outpoint := fundB.2

def spec : AssetSpec := ⟨⟨"USDT"⟩, ⟨"Tether USD"⟩, none, .centiMicro⟩
def terms : ContractTerms := ⟨⟨"terms"⟩, none⟩

def mkGenesis (issued : UInt64) (assigned : UInt64) : Genesis :=
  { schemaId := nia.schemaId, timestamp := 1713261744, chainNet := .bitcoinRegtest
    globals := OrdMap.ofList
      [ (gsNominal, [⟨.assetSpec spec⟩]), (gsTerms, [⟨.contractTerms terms⟩])
      , (gsIssuedSupply, [⟨.amount issued⟩]) ]
    assignments := OrdMap.ofList [(osAsset, .fungible [(.revealed ⟨utxoA.txid, utxoA.vout, 1⟩, ⟨assigned⟩)])] }

def genesis : Genesis := mkGenesis 1000 1000
def cid : ContractId := genesis.contractId
def cfg : ValidationConfig := { chainNet := .bitcoinRegtest }

def contractOf (g : Genesis) : Consignment := { transfer := false, genesis := g }

-- the schema rules are consistent: every routine's library is present
#guard (SchemaRules.make nia [niaLib]) matches .ok _
#guard (SchemaRules.make nia []) matches .error (.scriptAbsent _)
-- the NIA script keeps the rgb-schemas offsets: genesis routine at byte 9, 33 bytes in total
#guard niaLib.byteLen == 33 && niaLib.offsets.contains 9
-- the issuance is valid
#guard ((contractOf genesis).validate false niaRules .dumb cfg) matches .ok _
-- genesis must assign exactly the issued supply (script error 1)
#guard ((contractOf (mkGenesis 1000 999)).validate false niaRules .dumb cfg)
  == .error (.invalidConsignment (.scriptFailure (mkGenesis 1000 999).id (some 1)))
-- a contract consignment is validated against its own chain network
#guard ((contractOf genesis).validate false niaRules .dumb { chainNet := .bitcoinMainnet })
  == .error (.invalidConsignment (.contractChainNetMismatch .bitcoinMainnet))
-- and against the schema it names
#guard ((contractOf genesis).validate false cfaRules .dumb cfg)
  == .error (.invalidConsignment (.schemaMismatch nia.schemaId cfa.schemaId))
-- a contract consignment cannot carry bundles, and a transfer is not a contract
#guard ((contractOf genesis).validate true niaRules .dumb cfg)
  == .error (.invalidConsignment (.custom "invalid consignment type"))

/-! ## A transfer -/

def bobSeal : GraphSeal := GraphSeal.ofOutpoint utxoB 42
def changeSeal : GraphSeal := GraphSeal.witnessVout 1 7
def spendGenesis : Opout := ⟨genesis.id, osAsset, 0⟩

def mkTransfer (toBob change : UInt64) (inputs : List Opout := [spendGenesis]) : Transition :=
  { contractId := cid, transitionType := tsTransfer, inputs
    assignments := OrdMap.ofList [(osAsset, .fungible
      [(.concealed bobSeal.conceal, ⟨toBob⟩), (.revealed changeSeal, ⟨change⟩)])] }

def witnessTx (spend : List Outpoint := [utxoA]) : Tx :=
  mkTx spend [⟨0, .opReturn none⟩, ⟨546, .p2wpkh "issuer"⟩, ⟨9000, .p2wpkh "issuer-btc"⟩]

def wbOf (t : Transition) (tx : Tx := witnessTx) : WitnessBundle :=
  ((commitBundles tx [(cid, TransitionBundle.ofTransitions [t])] 5).toOption.bind
    (·.witnessBundle? cid)).getD default

def transferOf (bundles : List WitnessBundle) : Consignment := { transfer := true, genesis, bundles }

def t1 : Transition := mkTransfer 600 400
def wb1 : WitnessBundle := wbOf t1
/-- The receiver validates before the witness is broadcast: the consignment's
witness resolves as tentative. -/
def resolver : Resolver := (chain.resolver .bitcoinRegtest).withConsignmentTxes [wb1.tx]

def validateT (bundles : List WitnessBundle) (r : Resolver := resolver) (c : ValidationConfig := cfg) :=
  (transferOf bundles).validate true niaRules r c

-- the transfer is valid, with the witness tentative
#guard (validateT [wb1]).map (·.status.txOrdMap) == .ok [(wb1.tx.txid, .tentative)]
-- the receiver finds its allocation by its concealed seal
#guard ((transferOf [wb1]).assignmentsTo [bobSeal.conceal] []).map (·.opout) == [⟨t1.id, osAsset, 0⟩]
-- inputs must equal outputs (script error 0)
#guard validateT [wbOf (mkTransfer 600 500)]
  == .error (.invalidConsignment (.scriptFailure (mkTransfer 600 500).id (some 0)))
-- a zero-amount output is refused by the same check
#guard validateT [wbOf (mkTransfer 1000 0)]
  == .error (.invalidConsignment (.scriptFailure (mkTransfer 1000 0).id (some 0)))
-- an input must be a known, revealed, unspent output
def bogus : Opout := ⟨genesis.id, osAsset, 1⟩
#guard validateT [wbOf (mkTransfer 600 400 [bogus])]
  == .error (.invalidConsignment (.noPrevState (mkTransfer 600 400 [bogus]).id bogus))
-- the witness must spend the input seal
#guard validateT [wbOf t1 (witnessTx [utxoB])]
  == .error (.invalidConsignment (.sealsInvalid (TransitionBundle.ofTransitions [t1]).bundleId
      (wbOf t1 (witnessTx [utxoB])).tx.txid (.witnessNotClosingSeal utxoA)))
-- the witness must carry the commitment
def uncommitted : WitnessBundle := { wb1 with tx := witnessTx }
#guard (transferOf [uncommitted]).validate true niaRules
    ((chain.resolver .bitcoinRegtest).withConsignmentTxes [uncommitted.tx]) cfg
  == .error (.invalidConsignment (.sealsInvalid wb1.bundle.bundleId uncommitted.tx.txid (.dbc .invalidOpretScript)))
-- spending the same output twice is a double spend
def t1b : Transition := { mkTransfer 600 400 with nonce := 1 }
def wb1b : WitnessBundle := wbOf t1b (witnessTx [utxoA, utxoB])
#guard (transferOf [wb1, wb1b]).validate true niaRules
    ((chain.resolver .bitcoinRegtest).withConsignmentTxes [wb1.tx, wb1b.tx]) cfg
  == .error (.invalidConsignment (.noPrevState t1b.id spendGenesis))
-- a transition type the schema does not define is refused
def burnT : Transition := { t1 with transitionType := tsBurn }
#guard validateT [wbOf burnT] == .error (.invalidConsignment (.schemaUnknownTransitionType burnT.id tsBurn))
-- state of the wrong kind is refused
def voidT : Transition := { t1 with assignments := OrdMap.ofList [(osAsset, .declarative [.revealed changeSeal])] }
#guard validateT [wbOf voidT]
  == .error (.invalidConsignment (.stateTypeMismatch voidT.id osAsset .fungible .void))
-- a transfer may not add global state
def globT : Transition := { t1 with globals := OrdMap.ofList [(gsIssuedSupply, [⟨.amount 5⟩])] }
#guard validateT [wbOf globT]
  == .error (.invalidConsignment (.schemaUnknownGlobalStateType globT.id gsIssuedSupply))
-- a witness the resolver cannot find makes the consignment invalid
#guard validateT [wb1] (chain.resolver .bitcoinRegtest)
  == .error (.invalidConsignment (.sealNoPubWitness wb1.bundle.bundleId wb1.tx.txid))
-- a resolver on another network is refused
#guard validateT [wb1] ((chain.resolver .bitcoinMainnet).withConsignmentTxes [wb1.tx])
  == .error (.resolverError .wrongChainNet)

/-! ## Confirmation and safe height -/

def mined : Chain := ((chain.broadcast wb1.tx).toOption.getD chain).mine
-- once mined, the witness resolves with its height
#guard (validateT [wb1] (mined.resolver .bitcoinRegtest)).map (·.status.txOrdMap)
  == .ok [(wb1.tx.txid, .mined ⟨3, 1700001200⟩)]
-- with a safe height below the witness, it is reported as unsafe history (a warning)
#guard (validateT [wb1] (mined.resolver .bitcoinRegtest) { cfg with safeHeight := some 2 }).map
    (·.status.warnings) == .ok [.unsafeHistory [(3, [wb1.tx.txid])]]
#guard (validateT [wb1] (mined.resolver .bitcoinRegtest) { cfg with safeHeight := some 3 }).map
    (·.status.validity) == .ok .valid
-- an SPV proof shipped with the bundle gives the position without the indexer
def wbSpv : WitnessBundle := { wb1 with spvProof := mined.spvProof? wb1.tx.txid }
#guard (validateT [wbSpv] (mined.resolver .bitcoinRegtest)).map (·.status.txOrdMap)
  == .ok [(wb1.tx.txid, .mined ⟨3, 1700001200⟩)]

end Rgb.Examples.NiaValidation
