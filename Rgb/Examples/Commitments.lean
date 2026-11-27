import Rgb.Commit.Dbc

/-!
# Commitment scenarios

Multi-protocol commitments, opret and tapret anchoring, and SPV proofs.
-/

namespace Rgb.Examples.CommitScenario

open Rgb Rgb.Mpc

def cid (n : Nat) : ContractId := ⟨Digest.of "contract" [encode n]⟩
def bid (n : Nat) : BundleId := ⟨Digest.of Tag.bundle [encode n]⟩

def messages : OrdMap ContractId BundleId := OrdMap.ofList ((List.range 5).map fun i => (cid i, bid i))
def tree : MerkleTree := (MerkleTree.tryCommit messages 42).toOption.get!

-- the tree has at least the minimal depth, room for every contract, and distinct positions
#guard tree.depth ≥ minimalDepth && 2 ^ tree.depth ≥ 5
#guard MerkleTree.fits messages tree.cofactor tree.depth
-- every contract's proof yields the tree commitment
#guard (List.range 5).all fun i =>
  ((tree.proof? (cid i)).map fun pr => pr.convolve (cid i) (bid i)) == some (.ok tree.commitment)
-- a proof of contract 0 does not commit to another bundle
#guard ((tree.proof? (cid 0)).map fun pr => pr.convolve (cid 0) (bid 1) == .ok tree.commitment) == some false
-- a proof claiming another position is refused
#guard ((tree.proof? (cid 0)).map fun pr =>
  ({ pr with pos := pr.pos + 1 }.convolve (cid 0) (bid 0)) matches .error _) == some true
-- an empty tree needs a positive minimal depth
#guard (MerkleTree.tryCommit {} 1 0) == .error .empty

def c : Digest := tree.commitment
def spend : TxIn := ⟨⟨⟨Digest.of Tag.txid ["coin"]⟩, 0⟩, 0xFFFFFFFD⟩
def payTx : Tx := { inputs := [spend], outputs := [⟨1000, .p2wpkh "bob"⟩, ⟨0, .opReturn none⟩] }
def committed : Tx := payTx.withOpretCommitment c

-- opret: the first OP_RETURN output carries the commitment
#guard DbcProof.opret.verify c committed == .ok ()
#guard dbcOutput? committed == some (1, .opretFirst)
#guard DbcProof.opret.verify c payTx == .error .invalidOpretScript
#guard DbcProof.opret.verify (bid 9).d committed == .error .commitmentMismatch
-- a transaction with no OP_RETURN output gets one at index 0
#guard (({ payTx with outputs := [⟨1000, .p2wpkh "bob"⟩] } : Tx).withOpretCommitment c).outputs.head?
  == some ⟨0, .opReturn (some c)⟩

-- tapret: the first taproot output key commits through the tapret leaf
def tapTx : Tx := { inputs := [spend], outputs := [⟨1000, tapretScript "ikey" c⟩] }
#guard (DbcProof.tapret { internalKey := "ikey" }).verify c tapTx == .ok ()
#guard (DbcProof.tapret { internalKey := "other" }).verify c tapTx == .error .commitmentMismatch
#guard (DbcProof.tapret { internalKey := "ikey" }).verify c committed == .error .impossibleMessage
-- a partner that is itself a tapret leaf is refused
#guard (DbcProof.tapret { internalKey := "ikey", partner := some (.rightLeaf (.tapret c 1)) }).verify c tapTx
  == .error .impossibleMessage

-- SPV: a mined transaction's proof validates against its block header
def chain : Chain := ((Chain.mk [] [] 1700000000).fund (.p2wpkh "a") 5000).1
def fundTxid : Txid := chain.blocks.head!.txs.head!.txid
#guard ((chain.spvProof? fundTxid).bind fun p => (chain.header? p.blockHeight).map fun h =>
  p.validate fundTxid h) == some (.ok ())
#guard ((chain.spvProof? fundTxid).bind fun p => (chain.header? p.blockHeight).map fun h =>
  ({ p with pos := 4 } : SpvProof).validate fundTxid h) == some (.error .positionOutOfBounds)

end Rgb.Examples.CommitScenario
