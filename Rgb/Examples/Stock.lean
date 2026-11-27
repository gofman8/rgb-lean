import Rgb.Ops.Stock
import Rgb.Examples.Validation

/-!
# Stash scenarios

The issuer's and the receiver's stashes through one transfer: import, fascia,
composition, acceptance, and what a reorganisation does to visible state.
-/

namespace Rgb.Examples.StockScenario

open Rgb Rgb.Schemas Rgb.Examples.NiaValidation

/-- The issuer imports the schema and its own issuance. -/
def issuer0 : Stock := (Stock.importSchema {} niaRules).consumeGenesis genesis

-- the issuance is visible on the issuer's output
#guard issuer0.allocationsAt cid [utxoA] == [(utxoA, spendGenesis, .amount 1000)]
#guard issuer0.globalValues cid gsIssuedSupply == [⟨.amount 1000⟩]

/-- The sender's fascia of the transfer, consumed with the witness tentative. -/
def fascia : Fascia := (commitBundles (witnessTx) [(cid, TransitionBundle.ofTransitions [t1])] 5).toOption.get!
def issuer1 : Stock := (issuer0.consumeFascia fascia .tentative).toOption.get!
def wtxid : Txid := fascia.witnessId

-- the change is visible on output 1 of the witness; the receiver's share is concealed
#guard issuer1.allocations cid == [(utxoA, spendGenesis, .amount 1000), (⟨wtxid, 1⟩, ⟨t1.id, osAsset, 1⟩, .amount 400)]
-- the consignment for the receiver: genesis plus the transfer bundle, found by the concealed seal
def toBob : Consignment := (issuer1.consign cid [] [bobSeal.conceal] [] true).toOption.get!
#guard toBob.bundles.length == 1 && toBob.genesis == genesis
-- the same consignment built from the fascia before consuming it
#guard ((issuer0.transferFromFascia cid [] [bobSeal.conceal] [] fascia).map (·.bundles.length)) == .ok 1
-- an output with no state of the contract cannot be requested
#guard (issuer1.consign cid [utxoB] [] [] true) == .error (.inconsistency (.outpointUnknown utxoB cid))

/-- The receiver knows its seal, imports the schema, validates and accepts. -/
def bob0 : Stock := (Stock.importSchema {} niaRules).storeSecretSeal bobSeal
def resolverT : Resolver := (chain.resolver .bitcoinRegtest).withConsignmentTxes [fascia.sealWitness.tx]
def valid : ValidConsignment := (toBob.validate true niaRules resolverT cfg).toOption.get!
def bob1 : Stock := (bob0.consumeConsignment valid resolverT).toOption.get!

-- the receiver sees its 600 on its own output: the seal was revealed with its secret
#guard bob1.allocationsAt cid [utxoB] == [(utxoB, ⟨t1.id, osAsset, 0⟩, .amount 600)]
-- a stash without the schema refuses the consignment
#guard (({} : Stock).consumeConsignment valid resolverT) matches .error (.schemaNotImported _)
-- a consignment whose witness the chain does not know is stale
#guard (bob0.consumeConsignment valid (chain.resolver .bitcoinRegtest)) matches .error .absentValidWitness

/-! ## Reorganisation -/

def chainMined : Chain := ((chain.broadcast fascia.sealWitness.tx).toOption.getD chain).mine
def bob2 : Stock := (bob1.updateWitnesses (chainMined.resolver .bitcoinRegtest)).1
-- once mined, the witness status follows the chain
#guard bob2.ord? wtxid == some (.mined ⟨3, 1700001200⟩)
-- the block is dropped and the transaction evicted: the witness is archived and the state disappears
def chainGone : Chain := (chainMined.rollback 1).evict wtxid
def bob3 : Stock := (bob2.updateWitnesses (chainGone.resolver .bitcoinRegtest)).1
#guard bob3.ord? wtxid == some .archived
#guard bob3.allocationsAt cid [utxoB] == []
#guard bob3.invalidOps.contains t1.id
-- mined again: the state comes back
def bob4 : Stock := (bob3.updateWitnesses (chainMined.resolver .bitcoinRegtest)).1
#guard bob4.allocationsAt cid [utxoB] == [(utxoB, ⟨t1.id, osAsset, 0⟩, .amount 600)]
#guard !bob4.invalidOps.contains t1.id

end Rgb.Examples.StockScenario
