import Rgb.Bitcoin.Chain

/-!
# Block merkle trees

Bitcoin's transaction merkle tree: pairs of nodes are hashed upward and a layer
with an odd number of nodes repeats its last node. A merkle branch proves that a
transaction sits at a position in a block.
-/

namespace Rgb

def merkleParent (a b : Digest) : Digest := Digest.of "bitcoin:merkle-node" [encode a, encode b]

/-- One layer up: pair nodes, repeating the last one of an odd layer. -/
def merkleLayerUp : List Digest → List Digest
  | [] => []
  | [a] => [merkleParent a a]
  | a :: b :: rest => merkleParent a b :: merkleLayerUp rest

/-- Root of a non-empty list of leaves. -/
def merkleRoot (leaves : List Digest) : Digest :=
  let rec go (fuel : Nat) (layer : List Digest) : Digest :=
    match fuel, layer with
    | _, [] => default
    | _, [r] => r
    | 0, r :: _ => r
    | fuel + 1, l => go fuel (merkleLayerUp l)
  go leaves.length leaves

/-- Sibling hashes from the leaf at `pos` to the root. -/
def merkleBranch (leaves : List Digest) (pos : Nat) : List Digest :=
  let rec go (fuel : Nat) (layer : List Digest) (pos : Nat) : List Digest :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      if layer.length ≤ 1 then []
      else
        let sib := if pos % 2 == 0 then (layer[pos + 1]?.getD (layer[pos]?.getD default))
          else layer[pos - 1]?.getD default
        sib :: go fuel (merkleLayerUp layer) (pos / 2)
  go leaves.length leaves pos

/-- Root computed from a leaf, its position and its branch. -/
def rootFromBranch (leaf : Digest) (pos : Nat) (branch : List Digest) : Digest :=
  (branch.foldl (fun (acc, p) sib =>
      (if p % 2 == 0 then merkleParent acc sib else merkleParent sib acc, p / 2)) (leaf, pos)).1

/-- Header data an SPV check reads. -/
structure BlockHeader where
  height : Nat
  merkleRoot : Digest
  time : Int
  deriving DecidableEq, Repr, Inhabited

def Block.header (b : Block) : BlockHeader := ⟨b.height, merkleRoot (b.txs.map (·.txid.d)), b.timestamp⟩

/-- Header at a height of the best chain. -/
def Chain.header? (c : Chain) (height : Nat) : Option BlockHeader :=
  (c.blocks.find? (·.height == height)).map Block.header

/-- Position and branch of a mined transaction. -/
def Chain.merkleProof? (c : Chain) (t : Txid) : Option (Nat × Nat × List Digest) :=
  (c.blocks.find? (·.txs.any (·.txid == t))).bind fun b =>
    let ids := b.txs.map (·.txid.d)
    (ids.idxOf? t.d).map fun pos => (b.height, pos, merkleBranch ids pos)

end Rgb
