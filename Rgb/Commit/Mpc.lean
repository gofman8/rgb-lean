import Rgb.Consensus.Ids

/-!
# Multi-protocol commitments (LNPBP-4)

One witness transaction commits to the bundles of many contracts with a single
32-byte value. Each contract (protocol) gets one leaf of a merkle tree of
`2^depth` leaves, at the position its id takes modulo `2^depth - cofactor`; free
leaves hold entropy. A contract's proof is its leaf position, the cofactor and
the sibling hashes up to the root; the commitment hashes the depth, the cofactor
and the root.

The model reads the position from the low 64 bits of the id (`Digest.fingerprint`)
in place of the id's 256-bit little-endian value.
-/

namespace Rgb.Mpc

/-- Smallest tree depth (`MPC_MINIMAL_DEPTH`). -/
def minimalDepth : Nat := 3
/-- Cofactors tried per depth (`COFACTOR_ATTEMPTS`). -/
def cofactorAttempts : Nat := 500
/-- Largest depth (`u5`). -/
def maxDepth : Nat := 31

/-- Numeric value of a protocol id (model of `le256(id)`). -/
def protocolValue (p : ContractId) : Nat := p.d.fingerprint.toNat

/-- Leaf position of a protocol (`protocol_id_pos`): `id mod max(1, 2^depth - cofactor)`. -/
def protocolIdPos (p : ContractId) (cofactor depth : Nat) : Nat :=
  protocolValue p % max 1 (2 ^ depth - cofactor)

def leafInhabited (p : ContractId) (m : BundleId) : Digest :=
  Digest.of Tag.merkleNode ["\x10", encode p, encode m]

def leafEntropy (entropy : UInt64) (pos : Nat) : Digest :=
  Digest.of Tag.merkleNode ["\x11", encode entropy, encode pos]

/-- Branch node at `level` of a tree of `width` leaves. -/
def node (level width : Nat) (a b : Digest) : Digest :=
  Digest.of Tag.merkleNode ["\x02", encode level, encode width, encode a, encode b]

/-- Root of the `2^h` leaves `xs`, built at `level`. -/
def rootAux (width level : Nat) : (h : Nat) → List Digest → Digest
  | 0, xs => xs.headD default
  | h + 1, xs =>
    node level width (rootAux width (level + 1) h (xs.take (2 ^ h)))
      (rootAux width (level + 1) h (xs.drop (2 ^ h)))

/-- Sibling hashes from the root down to the leaf at `pos`. -/
def pathAux (width level : Nat) : (h : Nat) → List Digest → Nat → List Digest
  | 0, _, _ => []
  | h + 1, xs, pos =>
    if pos < 2 ^ h then
      rootAux width (level + 1) h (xs.drop (2 ^ h)) :: pathAux width (level + 1) h (xs.take (2 ^ h)) pos
    else
      rootAux width (level + 1) h (xs.take (2 ^ h)) :: pathAux width (level + 1) h (xs.drop (2 ^ h)) (pos - 2 ^ h)

/-- Root from a leaf, its position and its path; `path[0]` is just below the root. -/
def rootFromPath (leaf : Digest) (pos : Nat) (path : List Digest) : Digest :=
  let d := path.length
  let width := 2 ^ d
  (List.range d).reverse.foldl (fun h k =>
    let sib := path[k]?.getD default
    if (pos >>> (d - 1 - k)) % 2 == 1 then node k width sib h else node k width h sib) leaf

/-- The commitment: depth, cofactor and root (`mpc::Commitment`). -/
def commitment (depth cofactor : Nat) (root : Digest) : Digest :=
  Digest.of Tag.mpcCommitment [encode depth, encode cofactor, encode root]

/-- A contract's proof of inclusion (`MerkleProof`): path of at most 31 hashes. -/
structure MerkleProof where
  pos : Nat
  cofactor : Nat
  path : List Digest
  deriving DecidableEq, Repr, Inhabited

/-- The proof puts the protocol elsewhere than its id says (`InvalidProof`). -/
structure InvalidProof where
  protocolId : ContractId
  expected : Nat
  actual : Nat
  width : Nat
  deriving DecidableEq, Repr

/-- The commitment a proof yields for `(protocol, message)` (`MerkleProof::convolve`):
the only check is that the position is the protocol's position. -/
def MerkleProof.convolve (pr : MerkleProof) (p : ContractId) (m : BundleId) :
    Except InvalidProof Digest :=
  let d := pr.path.length
  let expected := protocolIdPos p pr.cofactor d
  if expected != pr.pos then .error ⟨p, expected, pr.pos, 2 ^ d⟩
  else .ok (commitment d pr.cofactor (rootFromPath (leafInhabited p m) pr.pos pr.path))

/-- Why a tree cannot be built (`mpc::Error`). -/
inductive MpcError where
  | empty
  | tooManyMessages (n : Nat)
  | cantFitInMaxSlots (n : Nat)
  deriving DecidableEq, Repr

/-- A full commitment tree (`MerkleTree`): one leaf per contract. -/
structure MerkleTree where
  depth : Nat
  cofactor : Nat
  entropy : UInt64
  messages : OrdMap ContractId BundleId
  deriving DecidableEq, Repr, Inhabited

namespace MerkleTree

def posOf (t : MerkleTree) (p : ContractId) : Nat := protocolIdPos p t.cofactor t.depth

def leaves (t : MerkleTree) : List Digest :=
  (List.range (2 ^ t.depth)).map fun pos =>
    match t.messages.toList.find? (fun (p, _) => t.posOf p == pos) with
    | some (p, m) => leafInhabited p m
    | none => leafEntropy t.entropy pos

def root (t : MerkleTree) : Digest := rootAux (2 ^ t.depth) 0 t.depth t.leaves

def commitment (t : MerkleTree) : Digest := Mpc.commitment t.depth t.cofactor t.root

/-- The proof of one contract (`into_merkle_proof`); `none` if it is not in the tree. -/
def proof? (t : MerkleTree) (p : ContractId) : Option MerkleProof :=
  if t.messages.contains p then
    some ⟨t.posOf p, t.cofactor, pathAux (2 ^ t.depth) 0 t.depth t.leaves (t.posOf p)⟩
  else none

/-- Positions are distinct under a cofactor and depth. -/
def fits (messages : OrdMap ContractId BundleId) (cofactor depth : Nat) : Bool :=
  let ps := messages.keys.map fun p => protocolIdPos p cofactor depth
  ps.eraseDups.length == ps.length

/-- Build the smallest tree that places every message (`MerkleTree::try_commit`):
from `minDepth`, try cofactors `0 ..= min(previous width, 500)` at each depth with
enough leaves. -/
def tryCommit (messages : OrdMap ContractId BundleId) (entropy : UInt64)
    (minDepth : Nat := minimalDepth) : Except MpcError MerkleTree := do
  let n := messages.size
  if minDepth == 0 && n == 0 then throw .empty
  let rec go (fuel depth prevWidth : Nat) : Except MpcError MerkleTree :=
    match fuel with
    | 0 => .error (.cantFitInMaxSlots n)
    | fuel + 1 =>
      if depth > maxDepth then .error (.cantFitInMaxSlots n)
      else
        let found := if 2 ^ depth ≥ n then
            (List.range (min prevWidth cofactorAttempts + 1)).find? fun c => fits messages c depth
          else none
        match found with
        | some c => .ok ⟨depth, c, entropy, messages⟩
        | none => go fuel (depth + 1) (2 ^ depth)
  go (maxDepth + 2) minDepth 1

end MerkleTree

end Rgb.Mpc
