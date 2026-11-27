import Rgb.Bitcoin.Chain

/-!
# Chain scenarios

Checks of the simulated chain that the RGB scenarios rely on.
-/

namespace Rgb.Examples.ChainScenario

open Rgb

def alice : Script := .p2wpkh "alice"
def bob : Script := .p2wpkh "bob"

def funded : Chain × Outpoint := (Chain.mk [] [] 1700000000).fund alice 100000
def c0 : Chain := funded.1
def coin : Outpoint := funded.2

def pay : Tx := { inputs := [⟨coin, 0xFFFFFFFD⟩], outputs := [⟨60000, bob⟩, ⟨39000, alice⟩] }
def payAgain : Tx := { inputs := [⟨coin, 0xFFFFFFFD⟩], outputs := [⟨99000, bob⟩] }

def c1 : Chain := (c0.broadcast pay).toOption.getD c0

-- the funding transaction is mined at height 1
#guard c0.height == 1
#guard c0.confirmations coin.txid == 1
#guard c0.isUnspent coin

-- a payment enters the mempool: tentative, unconfirmed, the coin is spent
#guard c1.witnessOrd pay.txid == .tentative
#guard c1.confirmations pay.txid == 0
#guard !c1.isUnspent coin

-- a double spend of the same coin is refused
#guard (c1.broadcast payAgain) matches .error (.conflictInMempool _)

-- mining confirms the payment; more blocks add confirmations
#guard (c1.mine.witnessOrd pay.txid) matches .mined _
#guard (c1.mineN 6).confirmations pay.txid == 6

-- an unknown transaction is archived
#guard c1.witnessOrd payAgain.txid == .archived

-- spending more than the inputs hold is refused
#guard (c0.broadcast { inputs := [⟨coin, 0xFFFFFFFD⟩], outputs := [⟨200000, bob⟩] })
  matches .error (.valueExceedsInputs _ _)

-- a rollback returns mined transactions to the mempool
#guard ((c1.mine).rollback 1).witnessOrd pay.txid == .tentative

end Rgb.Examples.ChainScenario
