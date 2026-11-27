import Rgb.Consensus.Bundle
import Rgb.Schemas.Numbers

/-!
# Operation and bundle scenarios

Checks of ids, seal concealment and bundles on hand-built operations.
-/

namespace Rgb.Examples.Ops

open Rgb Rgb.Schemas

def fundTx : Tx := { inputs := [], outputs := [⟨10000, .p2wpkh "issuer"⟩, ⟨10000, .p2wpkh "issuer"⟩] }
def utxo0 : Outpoint := fundTx.outpoint 0
def utxo1 : Outpoint := fundTx.outpoint 1

def gseal0 : GenesisSeal := ⟨utxo0.txid, utxo0.vout, 11⟩
def schemaId : SchemaId := ⟨Digest.of Tag.schema ["example"]⟩

def genesis : Genesis :=
  { schemaId, timestamp := 1713261744, chainNet := .bitcoinRegtest
    globals := OrdMap.ofList [(gsIssuedSupply, [⟨.amount 1000⟩])]
    assignments := OrdMap.ofList [(osAsset, .fungible [(.revealed gseal0, ⟨1000⟩)])] }

def cid : ContractId := genesis.contractId
def gop : Operation := .genesis genesis

/-- Spend the genesis allocation: 600 to a concealed receiver seal, 400 back to a
witness-output seal of the sender. -/
def receiverSeal : GraphSeal := GraphSeal.ofOutpoint utxo1 77
def changeSeal : GraphSeal := GraphSeal.witnessVout 1 99

def transfer : Transition :=
  { contractId := cid, transitionType := tsTransfer
    inputs := [⟨genesis.id, osAsset, 0⟩]
    assignments := OrdMap.ofList [(osAsset, .fungible
      [(.concealed receiverSeal.conceal, ⟨600⟩), (.revealed changeSeal, ⟨400⟩)])] }

def transferRevealed : Transition :=
  { transfer with assignments := OrdMap.ofList [(osAsset, .fungible
      [(.revealed receiverSeal, ⟨600⟩), (.revealed changeSeal, ⟨400⟩)])] }

-- the contract id is the genesis id
#guard cid.d == genesis.id.d
-- genesis creates one opout; the transfer creates two
#guard gop.opouts.length == 1
#guard (Operation.transition transfer).opouts.length == 2
-- revealing or concealing a seal does not change the operation id
#guard transferRevealed.id == transfer.id
-- any change to committed data changes the id
#guard ({ transfer with nonce := 1 } : Transition).id != transfer.id
#guard ({ transfer with transitionType := tsBurn } : Transition).id != transfer.id
-- the signature is not committed
#guard ({ transfer with signature := some ⟨List.replicate 64 7⟩ } : Transition).id == transfer.id

def bundle : TransitionBundle := TransitionBundle.ofTransitions [transfer]

-- the bundle maps the spent opout to the transfer
#guard bundle.inputMap.find? ⟨genesis.id, osAsset, 0⟩ == some transfer.id
#guard bundle.checkOpidCommitments == .ok ()
-- the bundle id commits to the input map only: hiding the transition keeps it
#guard ({ bundle with knownTransitions := [] } : TransitionBundle).bundleId == bundle.bundleId
-- revealing a transition the input map does not reference is refused
def stranger : Transition := { transfer with nonce := 5 }
#guard (bundle.revealTransition stranger) matches .error (.unrelatedTransition _)
-- revealing an already known transition changes nothing
#guard (bundle.revealTransition transfer).map (·.2) == .ok false
-- a receiver who knows its seal reveals it in the bundle
#guard (bundle.revealSeal receiverSeal).knownTransitions.head?.map (·.transition.assignments)
  == some transferRevealed.assignments

/-- A second transition of the same bundle that spends the first one's change. -/
def chained : Transition :=
  { contractId := cid, transitionType := tsTransfer
    inputs := [⟨transfer.id, osAsset, 1⟩]
    assignments := OrdMap.ofList [(osAsset, .fungible [(.revealed (GraphSeal.witnessVout 2 5), ⟨400⟩)])] }

-- known transitions are sorted so that a parent precedes its child
#guard ((TransitionBundle.ofTransitions [chained, transfer]).sortKnown.knownTransitions.map (·.opid))
  == [transfer.id, chained.id]

end Rgb.Examples.Ops
