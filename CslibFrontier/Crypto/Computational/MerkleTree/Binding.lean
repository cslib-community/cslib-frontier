/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MerkleTree
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT
import CslibFrontier.Crypto.Game.Order
import Mathlib.Data.List.GetD

/-!
# Merkle trees as authenticated data structures: verification and position binding

`Cslib.Crypto.merkleRoot` hashes a list of leaves and `Cslib.Crypto.merklePath` opens one position.
This module adds the verifier and the security notion of an authenticated data structure scheme
([BonehShoup2023], Section 8.9.1): a verifier `merkleVerify` with completeness, binding and a
polynomial-time certificate, the game of Attack Game 8.2, and Theorem 8.8: under collision
resistance of the hash on its domain, Merkle trees are position binding, with no loss.

* **The verifier.** `merkleVerify H k d root i leaf path` accepts when `path` has `d` labels,
  `i < 2 ^ d`, every label has the length of `root`, and the root recomputed from `leaf` at
  position `i` along `path` is `root` (the `V` of [BonehShoup2023], Definition 8.3). The first two
  are the checks that the module documentation of `CslibFrontier.Crypto.Computational.MerkleTree`
  requires of a verifier, under "What a verifier must check"; without them binding fails. The
  third makes the path a list of digests, as a Merkle proof is in the source (Section 8.9,
  p. 321); without it, binding needs collision resistance beyond the hash's domain. Honest
  openings are accepted when all digests of `H k` have one length (`merkleVerify_merklePath`,
  `merkleVerify_merklePath_of_clog_eq`), the correctness requirement of Definition 8.3.
* **Binding of the verifier.** Two openings of one position to different leaves, both accepted at
  the same depth, give a collision of `H k`, found by `extractMerkleCollision`
  (`isCollision_of_merkleVerify`). When the leaves lie in a leaf space and the digests of `H k`
  have `n` bits, the collision lies in the hash's domain `merkleHashDomain leafSpace n`: the leaf
  space and the pairs of `n`-bit digests, the source's `X ∪ Y²` (Section 8.9, p. 320)
  (`isCollision_merkleHashDomain_of_merkleVerify`).
* **The game.** In `merkleBindingGame` the adversary receives the security parameter and a uniform
  key `k`, and outputs a root, a position and two `MerkleOpening`s (`MerkleBindingOutput`). It
  wins when both leaves lie in the leaf space, both openings are accepted at the depth of the
  first path, and the leaves differ (`merkleBreaksBinding`). `MerklePositionBinding H leafSpace`
  asks that every uniform strict PPT adversary win with negligible probability.
* **The reduction.** `merkleCollisionFinder` runs the adversary and applies
  `extractMerkleCollision` to its two openings. Every win yields a collision on the hash's domain,
  so the binding advantage is at most the collision advantage at every parameter
  (`succProbability_merkleBindingGame_le`), and the reduction is strict PPT
  (`isPPT_merkleCollisionFinder`). Hence collision resistance of `H` on
  `merkleHashDomain leafSpace` gives position binding (`CollisionResistantOn.merklePositionBinding`,
  Theorem 8.8). Collision resistance on all words implies it
  (`merklePositionBinding_of_hashFamily`).

**Differences from [BonehShoup2023].** Attack Game 8.2 is stated for a scheme over `(X^n, Y)`
with a fixed number `n` of items; here:
* the hash is a keyed family with a uniform `n`-bit key, and adversaries are uniform strict PPT
  programs, as in `CollisionResistant`; footnote 1 on p. 290 identifies a random key given to
  the adversary with the source's system parameter;
* digests have exactly `n` bits, so `Y = {0, 1}ⁿ`;
* the leaf space is any predicate on words, of which the source's finite, efficiently
  recognizable leaf spaces of polynomially bounded words (Definition 2.9, p. 30) are instances;
* the adversary chooses the depth `d`, the length of its first path, and must open both leaves at
  that depth, which makes the game stronger than one with a fixed depth;
* positions are `0 ≤ i < 2 ^ d`, the padding positions included, rather than `1 ≤ i ≤ n`;
* the adversary writes its position in unary (`encMerkleBindingOutput`), so the game covers
  polynomially bounded positions: enough for trees with polynomially many leaves, but not for
  trees whose leaves are indexed by superpolynomially many positions.

**Kilian's construction.** Kilian's succinct arguments commit to a PCP proof with a hash tree and
open the queried positions ([Barak and Goldreich][BarakGoldreich2001], Construction 3.4, steps
P1.3 and V3). That tree differs from this one, which is [BonehShoup2023]'s Figure 8.12: its leaf
labels are the proof bits themselves, not their hashes, and an internal label hashes the plain
concatenation `ℓ_γ0 ℓ_γ1` of its children's labels, not their `encPair` pairing. Its prover sends
both child labels at every level of a path rather than only the siblings, and the verifier checks
the same hash equations along the path. Barak and Goldreich's hashing family resists non-uniform
circuits.

## Main definitions

* `Cslib.Crypto.merkleVerify`: accepting an opening at a given depth.
* `Cslib.Crypto.MerkleOpening`, `Cslib.Crypto.MerkleOpening.verify`,
  `Cslib.Crypto.encMerkleOpening`: an opening as a record of a leaf and its path, its verifier for
  leaves under an encoding into bit strings, and the encoding of openings with bit-string leaves.
* `Cslib.Crypto.merkleHashDomain`: the domain `X ∪ Y²` of the tree's hash.
* `Cslib.Crypto.MerkleBindingOutput`, `Cslib.Crypto.encMerkleBindingOutput`,
  `Cslib.Crypto.MerkleBindingAdversary`: the adversary's output, its encoding (the grouped tuple
  `(root, position), first, second`), and adversaries.
* `Cslib.Crypto.merkleBreaksBinding`, `Cslib.Crypto.merkleBindingGame`,
  `Cslib.Crypto.MerklePositionBinding`: the position-binding game and security notion.
* `Cslib.Crypto.merkleCollisionFinder`: the reduction to collision finding.

## Main results

* `Cslib.Crypto.merkleVerify_merklePath`, `Cslib.Crypto.merkleVerify_merklePath_of_clog_eq`:
  honest openings are accepted.
* `Cslib.Crypto.length_of_mem_merkleLevel`, `Cslib.Crypto.length_merkleRoot`,
  `Cslib.Crypto.length_of_mem_merklePath`, `Cslib.Crypto.length_le_of_mem_merklePath`: tree
  nodes, the root and honest labels are digests, and the labels of any opening are short.
* `Cslib.Crypto.computableInPolyTime_merkleVerify`: verification takes polynomial time.
* `Cslib.Crypto.isCollision_of_merkleVerify`, `Cslib.Crypto.isCollision_of_merkleVerify_merklePath`,
  `Cslib.Crypto.isCollision_merkleHashDomain_of_merkleVerify`: two accepted openings of one
  position to different leaves yield a collision, on the hash's domain when the leaves lie in the
  leaf space.
* `Cslib.Crypto.isCollision_of_merkleBreaksBinding`,
  `Cslib.Crypto.succProbability_merkleBindingGame_le`,
  `Cslib.Crypto.isPPT_merkleCollisionFinder`: the certified reduction, with no loss.
* `Cslib.Crypto.MerklePositionBinding.negligible`,
  `Cslib.Crypto.MerklePositionBinding.of_negligible`: position binding as negligible success.
* `Cslib.Crypto.CollisionResistantOn.merklePositionBinding`: [BonehShoup2023], Theorem 8.8.
* `Cslib.Crypto.merklePositionBinding_of_hashFamily`: the same under collision resistance on all
  words.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Definition 2.9, footnote 1 on p. 290, Section 8.9, and Section 8.9.1 with Definitions 8.3
  and 8.4, Attack Game 8.2 and Theorem 8.8.
* [B. Barak, O. Goldreich, *Universal Arguments and their Applications*][BarakGoldreich2001],
  Construction 3.4.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-! ### Verifying openings -/

section Verify

variable (H : List Bool → List Bool → List Bool) (k : List Bool)

/-- Accept `path` as an opening of position `i` of a depth-`d` tree with root `root` to `leaf`:
the path has `d` labels, `i < 2 ^ d`, every label has the length of `root`, and the recomputed
root is `root`. This is the verifier `V` of the Merkle tree as an authenticated data structure
([BonehShoup2023], Definition 8.3), with the depth as an explicit argument. The length check
makes the path a list of digests, as a Merkle proof is in the source (Section 8.9, p. 321): an
accepted root is a digest, so the labels are too. -/
def merkleVerify (d : ℕ) (root : List Bool) (i : ℕ) (leaf : List Bool)
    (path : List (List Bool)) : Bool :=
  path.length == d && decide (i < 2 ^ d) && path.all (fun s => s.length == root.length) &&
    merkleRootOfPath H k leaf i path == root

/-- An opening of one position of a Merkle tree: the claimed leaf and its authentication path,
one label per level from the leaf up. -/
@[ext]
structure MerkleOpening (Leaf : Type) where
  /-- The claimed leaf. -/
  leaf : Leaf
  /-- The authentication path of the leaf. -/
  path : List (List Bool)
  deriving DecidableEq, Repr, Inhabited

/-- Accept the opening `o` of position `i` of a depth-`d` tree with root `root`, whose leaves are
the encodings `encLeaf` of the claimed values (`merkleVerify` on `encLeaf o.leaf`). -/
def MerkleOpening.verify {Leaf : Type} (encLeaf : Leaf → List Bool) (d : ℕ) (root : List Bool)
    (i : ℕ) (o : MerkleOpening Leaf) : Bool :=
  merkleVerify H k d root i (encLeaf o.leaf) o.path

@[simp]
theorem MerkleOpening.verify_mk {Leaf : Type} (encLeaf : Leaf → List Bool) (d : ℕ)
    (root : List Bool) (i : ℕ) (leaf : Leaf) (path : List (List Bool)) :
    (⟨leaf, path⟩ : MerkleOpening Leaf).verify H k encLeaf d root i =
      merkleVerify H k d root i (encLeaf leaf) path := rfl

@[simp]
theorem MerkleOpening.verify_id (d : ℕ) (root : List Bool) (i : ℕ)
    (o : MerkleOpening (List Bool)) :
    o.verify H k id d root i = merkleVerify H k d root i o.leaf o.path := rfl

/-- The encoding of an opening with bit-string leaves: the leaf, then the path. -/
enc_structure encMerkleOpening : MerkleOpening (List Bool) where
  leaf : encBits, path : (encList encBits)

variable {H k}

/-- The checks of `merkleVerify`, as propositions. -/
theorem merkleVerify_eq_true_iff {d : ℕ} {root : List Bool} {i : ℕ} {leaf : List Bool}
    {path : List (List Bool)} :
    merkleVerify H k d root i leaf path = true ↔
      path.length = d ∧ i < 2 ^ d ∧ (∀ s ∈ path, s.length = root.length) ∧
        merkleRootOfPath H k leaf i path = root := by
  simp only [merkleVerify, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    and_assoc]

/-- Every node of the tree has `ℓ` bits when every digest of `H k` does. -/
theorem length_of_mem_merkleLevel {ℓ : ℕ} (hlen : ∀ x, (H k x).length = ℓ)
    {leaves : List (List Bool)} {j : ℕ} {y : List Bool} (hy : y ∈ merkleLevel H k leaves j) :
    y.length = ℓ := by
  cases j with
  | zero => exact length_of_mem_merkleLeafLevel hlen hy
  | succ j =>
    rw [merkleLevel_succ] at hy
    exact length_of_mem_merkleParents hlen hy

/-- The root has `ℓ` bits when every digest of `H k` does. -/
theorem length_merkleRoot {ℓ : ℕ} (hlen : ∀ x, (H k x).length = ℓ) (leaves : List (List Bool)) :
    (merkleRoot H k leaves).length = ℓ := by
  have hpos : 0 < (merkleLevel H k leaves (Nat.clog 2 leaves.length)).length := by
    rw [length_merkleLevel, Nat.div_self (Nat.two_pow_pos _)]
    exact Nat.one_pos
  rw [merkleRoot, List.headD_eq_head?_getD, List.head?_eq_getElem? ,
    List.getElem?_eq_getElem hpos, Option.getD_some]
  exact length_of_mem_merkleLevel hlen (List.getElem_mem hpos)

/-- The labels of an honest authentication path have `ℓ` bits when every digest of `H k` does:
below the root, every sibling of a position inside the tree is a node of the tree. -/
theorem length_of_mem_merklePath {ℓ : ℕ} (hlen : ∀ x, (H k x).length = ℓ)
    {leaves : List (List Bool)} {i : ℕ} (hi : i < 2 ^ Nat.clog 2 leaves.length) {s : List Bool}
    (hs : s ∈ merklePath H k leaves i) : s.length = ℓ := by
  rw [merklePath_eq] at hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  rw [List.mem_range] at ht
  set d := Nat.clog 2 leaves.length
  have hlevel : (merkleLevel H k leaves t).length = 2 * 2 ^ (d - t - 1) := by
    rw [length_merkleLevel, ← pow_succ', show d - t - 1 + 1 = d - t by omega,
      Nat.pow_div (by omega) (by norm_num)]
  have hpos : i / 2 ^ t < 2 * 2 ^ (d - t - 1) := by
    rw [← pow_succ', show d - t - 1 + 1 = d - t by omega, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _),
      ← pow_add, show d - t + t = d by omega]
    exact hi
  have hsib : merkleSibling (i / 2 ^ t) < (merkleLevel H k leaves t).length := by
    rw [hlevel]
    generalize i / 2 ^ t = p at hpos ⊢
    generalize 2 ^ (d - t - 1) = f at hpos ⊢
    unfold merkleSibling
    split <;> omega
  rw [List.getD_eq_getElem _ _ hsib]
  exact length_of_mem_merkleLevel hlen (List.getElem_mem hsib)

/-- **Honest openings are accepted**: when every digest of `H k` has the same length, every
position `i < 2 ^ Nat.clog 2 leaves.length` of the tree over `leaves`, opened by its
authentication path, is accepted against the root (the correctness requirement of
[BonehShoup2023], Definition 8.3). -/
theorem merkleVerify_merklePath {ℓ : ℕ} (hlen : ∀ x, (H k x).length = ℓ)
    (leaves : List (List Bool)) {i : ℕ} (hi : i < 2 ^ Nat.clog 2 leaves.length) :
    merkleVerify H k (Nat.clog 2 leaves.length) (merkleRoot H k leaves) i (leaves.getD i [])
      (merklePath H k leaves i) = true :=
  merkleVerify_eq_true_iff.mpr ⟨length_merklePath leaves i, hi, fun _ hs => by
    rw [length_of_mem_merklePath hlen hi hs, length_merkleRoot hlen],
    merkleRootOfPath_merklePath leaves hi⟩

/-- Honest openings are accepted at any depth `d` equal to the tree's depth, for instance
`d = Nat.clog 2 N` for `N` leaves, when every digest of `H k` has the same length. -/
theorem merkleVerify_merklePath_of_clog_eq {ℓ : ℕ} (hlen : ∀ x, (H k x).length = ℓ)
    {leaves : List (List Bool)} {d i : ℕ} (hd : Nat.clog 2 leaves.length = d) (hi : i < 2 ^ d) :
    merkleVerify H k d (merkleRoot H k leaves) i (leaves.getD i [])
      (merklePath H k leaves i) = true := by
  subst hd
  exact merkleVerify_merklePath hlen leaves hi

/-- **Openings are short**: the labels of an authentication path have at most `k.length` bits
(a sibling outside the tree reads as `[]`), so an opening of the tree over `leaves` has at most
`Nat.clog 2 leaves.length * k.length` bits of labels. -/
theorem length_le_of_mem_merklePath (hlen : ∀ k x, (H k x).length = k.length)
    {leaves : List (List Bool)} {i : ℕ} {s : List Bool} (hs : s ∈ merklePath H k leaves i) :
    s.length ≤ k.length := by
  rw [merklePath_eq] at hs
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hs
  rw [List.getD_eq_getElem?_getD]
  cases h : (merkleLevel H k leaves t)[merkleSibling (i / 2 ^ t)]? with
  | none => simp
  | some y => exact (length_of_mem_merkleLevel (hlen k) (List.mem_of_getElem? h)).le

/-- **Binding of the verifier**: two openings of position `i` to different leaves, both accepted
against `root` at depth `d`, contain a collision of `H k`, which `extractMerkleCollision` finds.
The length check makes the two paths equally long, as `isCollision_extractMerkleCollision`
requires. -/
theorem isCollision_of_merkleVerify {d : ℕ} {root : List Bool} {i : ℕ}
    {leaf₁ leaf₂ : List Bool} {path₁ path₂ : List (List Bool)}
    (h₁ : merkleVerify H k d root i leaf₁ path₁ = true)
    (h₂ : merkleVerify H k d root i leaf₂ path₂ = true) (hne : leaf₁ ≠ leaf₂) (n : ℕ) :
    isCollision H (fun _ _ => true) n k (extractMerkleCollision H k leaf₁ leaf₂ i path₁ path₂).1
      (extractMerkleCollision H k leaf₁ leaf₂ i path₁ path₂).2 = true := by
  obtain ⟨hlen₁, -, -, hroot₁⟩ := merkleVerify_eq_true_iff.mp h₁
  obtain ⟨hlen₂, -, -, hroot₂⟩ := merkleVerify_eq_true_iff.mp h₂
  exact isCollision_extractMerkleCollision n (hlen₁.trans hlen₂.symm) hne (hroot₁.trans hroot₂.symm)

/-- **Binding against an honest tree**: an opening of position `i` of the tree over `leaves`,
accepted against its root at its depth, to a leaf other than leaf `i`, together with the honest
path of `i`, contains a collision of `H k`. Unlike `isCollision_of_merkleVerify`, this needs no
hypothesis on the lengths of the digests of `H k`. -/
theorem isCollision_of_merkleVerify_merklePath {leaves : List (List Bool)} {d i : ℕ}
    {leaf : List Bool} {path : List (List Bool)} (hd : Nat.clog 2 leaves.length = d)
    (h : merkleVerify H k d (merkleRoot H k leaves) i leaf path = true)
    (hne : leaf ≠ leaves.getD i []) (n : ℕ) :
    isCollision H (fun _ _ => true) n k
      (extractMerkleCollision H k leaf (leaves.getD i []) i path (merklePath H k leaves i)).1
      (extractMerkleCollision H k leaf (leaves.getD i []) i path (merklePath H k leaves i)).2 =
        true := by
  obtain ⟨hlen, hi, -, hroot⟩ := merkleVerify_eq_true_iff.mp h
  subst hd
  exact isCollision_extractMerkleCollision n (by rw [hlen, length_merklePath]) hne
    (by rw [hroot, merkleRootOfPath_merklePath leaves hi])

/-- The domain of the hash of a Merkle tree with leaf space `leafSpace`, at parameter `n`: the
leaves `x` with `leafSpace n x`, and the pairs of `n`-bit digests (`isDigestPair n`). This is
`X ∪ Y²` for `Y = {0, 1}ⁿ` in [BonehShoup2023], Section 8.9 (p. 320): "The input to `h` is either
a single element in `X`, or a pair of elements in `Y`." -/
def merkleHashDomain (leafSpace : ℕ → List Bool → Bool) (n : ℕ) (x : List Bool) : Bool :=
  leafSpace n x || isDigestPair n x

/-- **Binding of the verifier on the hash's domain**: two openings of position `i` to different
leaves of `leafSpace n`, both accepted against `root` at depth `d`, contain a collision of `H k`
on `merkleHashDomain leafSpace` at `n`, when every digest of `H k` has `n` bits. The verifier's
length check makes every label a digest, so the collision lies in the leaf space or among the
pairs of digests. -/
theorem isCollision_merkleHashDomain_of_merkleVerify {leafSpace : ℕ → List Bool → Bool} {n : ℕ}
    (hlen : ∀ x, (H k x).length = n) {d : ℕ} {root : List Bool} {i : ℕ}
    {leaf₁ leaf₂ : List Bool} {path₁ path₂ : List (List Bool)}
    (h₁ : merkleVerify H k d root i leaf₁ path₁ = true)
    (h₂ : merkleVerify H k d root i leaf₂ path₂ = true) (hleaf₁ : leafSpace n leaf₁ = true)
    (hleaf₂ : leafSpace n leaf₂ = true) (hne : leaf₁ ≠ leaf₂) :
    isCollision H (merkleHashDomain leafSpace) n k
      (extractMerkleCollision H k leaf₁ leaf₂ i path₁ path₂).1
      (extractMerkleCollision H k leaf₁ leaf₂ i path₁ path₂).2 = true := by
  have hcol := isCollision_of_merkleVerify h₁ h₂ hne n
  rw [isCollision_eq_true_iff] at hcol ⊢
  obtain ⟨-, -, hne', hH⟩ := hcol
  obtain ⟨hmem₁, hmem₂⟩ := mem_merkleInputs_of_extractMerkleCollision hne'
  have hvalid {leaf : List Bool} {path : List (List Bool)} (hleaf : leafSpace n leaf = true)
      (h : merkleVerify H k d root i leaf path = true) {x : List Bool}
      (hx : x ∈ merkleInputs H k leaf i path) : merkleHashDomain leafSpace n x = true := by
    obtain ⟨-, -, hlabels, hroot⟩ := merkleVerify_eq_true_iff.mp h
    have hroot_len : root.length = n := by rw [← hroot, merkleRootOfPath, hlen]
    rcases eq_or_isDigestPair_of_mem_merkleInputs hlen
      (fun s hs => (hlabels s hs).trans hroot_len) hx with rfl | hpair
    · simp [merkleHashDomain, hleaf]
    · simp [merkleHashDomain, hpair]
  exact ⟨hvalid hleaf₁ h₁ hmem₁, hvalid hleaf₂ h₂ hmem₂, hne', hH⟩

/-- Verifying an opening takes polynomial time: the key, the depth in unary, the root, the
position in unary, the leaf and the path. -/
@[program_certificate]
theorem computableInPolyTime_merkleVerify
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length) :
    ComputableInPolyTime
      (fun p : (List Bool × ℕ) × (List Bool × ℕ) × (List Bool × List (List Bool)) =>
        merkleVerify H p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2)
      (encPair (encPair encBits encUnary)
        (encPair (encPair encBits encUnary) (encPair encBits (encList encBits)))) encBool := by
  let T := (List Bool × ℕ) × (List Bool × ℕ) × (List Bool × List (List Bool))
  let E := encPair (encPair encBits encUnary)
    (encPair (encPair encBits encUnary) (encPair encBits (encList encBits)))
  have hroot : ComputableInPolyTime
      (fun p : T => merkleRootOfPath H p.1.1 p.2.2.1 p.2.1.2 p.2.2.2 == p.2.1.1) E encBool :=
    ComputableInPolyTime.beq ((computableInPolyTime_merkleRootOfPath hH hlen).comp
      (g := fun p : T => (p.1.1, p.2.2.1, p.2.1.2, p.2.2.2)) (by dsimp only [E]; fun_prop))
      (by dsimp only [E]; fun_prop)
  have hd : ComputableInPolyTime (fun p : T => p.1.2) E encUnary := by dsimp only [E]; fun_prop
  have hrange : ComputableInPolyTime (fun p : T => decide (p.2.1.2 < 2 ^ p.1.2)) E encBool :=
    ComputableInPolyTime.binary_lt'
      (ComputableInPolyTime.unary_to_binary.comp (by dsimp only [E]; fun_prop))
      (ComputableInPolyTime.binary_two_pow.comp hd)
  have hlength : ComputableInPolyTime (fun p : T => p.2.2.2.length == p.1.2) E encBool :=
    ComputableInPolyTime.beq (encB := encUnary) (by dsimp only [E]; fun_prop) hd
  have hlabels : ComputableInPolyTime
      (fun p : T => p.2.2.2.all fun s => s.length == p.2.1.1.length) E encBool :=
    ComputableInPolyTime.allWithInput (by dsimp only [E]; fun_prop)
      (ComputableInPolyTime.beq (encB := encUnary) (by dsimp only [E]; fun_prop)
        (by dsimp only [T, E]; fun_prop))
  exact ComputableInPolyTime.bool_and.comp
    ((ComputableInPolyTime.bool_and.comp
      ((ComputableInPolyTime.bool_and.comp (hlength.prod hrange)).prod hlabels)).prod hroot)

end Verify

/-! ### Position binding -/

/-- The output of a position-binding adversary: a root and a position, then two openings of that
position. The depth is the length of the first path. -/
structure MerkleBindingOutput where
  /-- The claimed root. -/
  root : List Bool
  /-- The opened position. -/
  position : ℕ
  /-- The first opening of `position`. -/
  first : MerkleOpening (List Bool)
  /-- The second opening of `position`. -/
  second : MerkleOpening (List Bool)
  deriving DecidableEq, Repr, Inhabited

/-- The encoding of `MerkleBindingOutput`: the root and the position as a pair, then the two
openings, which is the grouping of the tuple this record replaced. Bit strings are encoded as
themselves and the position in unary, as in `computableInPolyTime_extractMerkleCollision`, so an
efficient adversary outputs only polynomially bounded positions. -/
def encMerkleBindingOutput : MerkleBindingOutput ↪ List Bool :=
  encOfEquiv
    { toFun out := ((out.root, out.position), out.first, out.second)
      invFun | ((root, position), first, second) => ⟨root, position, first, second⟩
      left_inv _ := rfl
      right_inv | ((_, _), _, _) => rfl }
    (encPair (encPair encBits encUnary) (encPair encMerkleOpening encMerkleOpening))

@[simp]
theorem encMerkleBindingOutput_apply (out : MerkleBindingOutput) :
    encMerkleBindingOutput out =
      encPair (encPair encBits encUnary) (encPair encMerkleOpening encMerkleOpening)
        ((out.root, out.position), out.first, out.second) := rfl

section Fields

variable {γ : Type} {encIn : γ ↪ List Bool} {g : γ → MerkleBindingOutput}

private theorem encMerkleBindingOutput_fields_polyTime :
    ComputableInPolyTime
      (fun out : MerkleBindingOutput => ((out.root, out.position), out.first, out.second))
      encMerkleBindingOutput
      (encPair (encPair encBits encUnary) (encPair encMerkleOpening encMerkleOpening)) :=
  ComputableInPolyTime.of_eq fun _ => rfl

@[scoped fun_prop]
theorem encMerkleBindingOutput_root_polyTime
    (h : ComputableInPolyTime g encIn encMerkleBindingOutput) :
    ComputableInPolyTime (fun a => (g a).root) encIn encBits :=
  encMerkleBindingOutput_fields_polyTime.fst'.fst'.comp h

@[scoped fun_prop]
theorem encMerkleBindingOutput_position_polyTime
    (h : ComputableInPolyTime g encIn encMerkleBindingOutput) :
    ComputableInPolyTime (fun a => (g a).position) encIn encUnary :=
  encMerkleBindingOutput_fields_polyTime.fst'.snd'.comp h

@[scoped fun_prop]
theorem encMerkleBindingOutput_first_polyTime
    (h : ComputableInPolyTime g encIn encMerkleBindingOutput) :
    ComputableInPolyTime (fun a => (g a).first) encIn encMerkleOpening :=
  encMerkleBindingOutput_fields_polyTime.snd'.fst'.comp h

@[scoped fun_prop]
theorem encMerkleBindingOutput_second_polyTime
    (h : ComputableInPolyTime g encIn encMerkleBindingOutput) :
    ComputableInPolyTime (fun a => (g a).second) encIn encMerkleOpening :=
  encMerkleBindingOutput_fields_polyTime.snd'.snd'.comp h

/-- A binding output assembled from polynomial-time fields is polynomial-time. -/
@[scoped fun_prop]
theorem encMerkleBindingOutput_mk_polyTime {r : γ → List Bool} {i : γ → ℕ}
    {o₁ o₂ : γ → MerkleOpening (List Bool)} (hr : ComputableInPolyTime r encIn encBits)
    (hi : ComputableInPolyTime i encIn encUnary)
    (ho₁ : ComputableInPolyTime o₁ encIn encMerkleOpening)
    (ho₂ : ComputableInPolyTime o₂ encIn encMerkleOpening) :
    ComputableInPolyTime (fun x => MerkleBindingOutput.mk (r x) (i x) (o₁ x) (o₂ x)) encIn
      encMerkleBindingOutput :=
  ComputableInPolyTime.of_enc_eq ((hr.prod hi).prod (ho₁.prod ho₂)) fun _ => rfl

end Fields

/-- A position-binding adversary receives the unary security parameter `n` and the hash key, and
outputs a root, a position and two openings. -/
abbrev MerkleBindingAdversary := ℕ → List Bool → ProbComp MerkleBindingOutput

section Binding

variable (H : List Bool → List Bool → List Bool) (leafSpace : ℕ → List Bool → Bool)

/-- `out` breaks position binding under the key `k` at parameter `n`: both leaves lie in the leaf
space `leafSpace n`, both openings are accepted at the same position of the same root, at the
depth of the first path, and the leaves differ. -/
def merkleBreaksBinding (n : ℕ) (k : List Bool) (out : MerkleBindingOutput) : Bool :=
  leafSpace n out.first.leaf && leafSpace n out.second.leaf &&
    out.first.verify H k id out.first.path.length out.root out.position &&
      out.second.verify H k id out.first.path.length out.root out.position &&
        out.first.leaf != out.second.leaf

/-- The position-binding experiment ([BonehShoup2023], Attack Game 8.2, p. 324, for a keyed hash
and leaf space `leafSpace`): sample a uniform `n`-bit key `k`, run the adversary on `(n, k)`, and
accept when its output breaks binding under `k` at `n`. -/
noncomputable def merkleBindingGame (adversary : MerkleBindingAdversary) (n : ℕ) :
    ProbComp Bool := do
  let k ← BitString.sampleList n
  let out ← adversary n k
  return merkleBreaksBinding H leafSpace n k out

/-- Position binding of Merkle trees over `H` with leaf space `leafSpace`, a notion novel to this
library: every uniform strict PPT adversary breaks binding with negligible probability. As in
[BonehShoup2023], Definition 8.4 and Attack Game 8.2 (p. 324), the two leaves lie in the leaf
space and `merkleVerify` accepts only paths of digests. It is stronger than Definition 8.4 in one
respect: the adversary chooses the depth of the tree, where the source's scheme has a fixed number
of leaves. It follows from collision resistance of `H` on `merkleHashDomain leafSpace`, the
assumption of Theorem 8.8 (`CollisionResistantOn.merklePositionBinding`). Adversaries write
positions in unary, so this covers polynomially bounded positions. -/
def MerklePositionBinding : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (merkleBindingGame H leafSpace adversary n))
    (fun _ _ => PMF.pure false) (IsPPT encMerkleBindingOutput)

/-- The collision finder built from a position-binding adversary: run it, and extract a collision
from its two openings with `extractMerkleCollision`. -/
def merkleCollisionFinder (adversary : MerkleBindingAdversary) : CollisionFinder := fun n k => do
  let out ← adversary n k
  return extractMerkleCollision H k out.first.leaf out.second.leaf out.position out.first.path
    out.second.path

variable {H leafSpace}

/-- **A binding break yields a collision on the hash's domain**: if `out` breaks position binding
under an `n`-bit key `k`, and `H k` returns `n`-bit digests, then `extractMerkleCollision` finds
two different words of `merkleHashDomain leafSpace n` with the same hash under `k`. -/
theorem isCollision_of_merkleBreaksBinding (hlen : ∀ k x, (H k x).length = k.length) {n : ℕ}
    {k : List Bool} (hk : k.length = n) {out : MerkleBindingOutput}
    (h : merkleBreaksBinding H leafSpace n k out = true) :
    let col := extractMerkleCollision H k out.first.leaf out.second.leaf out.position
      out.first.path out.second.path
    isCollision H (merkleHashDomain leafSpace) n k col.1 col.2 = true := by
  simp only [merkleBreaksBinding, MerkleOpening.verify_id, Bool.and_eq_true, bne_iff_ne,
    ne_eq] at h
  exact isCollision_merkleHashDomain_of_merkleVerify (fun x => (hlen k x).trans hk) h.1.1.2
    h.1.2 h.1.1.1.1 h.1.1.1.2 h.2

/-- **The reduction loses nothing**: at every security parameter, a position-binding adversary
succeeds at most as often as its collision finder finds a collision on the hash's domain, when
`H k` returns `k.length`-bit digests. -/
theorem succProbability_merkleBindingGame_le (hlen : ∀ k x, (H k x).length = k.length)
    (adversary : MerkleBindingAdversary) (n : ℕ) :
    Game.succProbability (ProbComp.eval (merkleBindingGame H leafSpace adversary n)) ≤
      Game.succProbability (ProbComp.eval
        (collisionGame H (merkleHashDomain leafSpace) (merkleCollisionFinder H adversary) n)) := by
  apply Game.succProbability_mono
  simp only [pmf_norm, merkleBindingGame, collisionGame, merkleCollisionFinder]
  apply PMF.bind_apply_mono_on_support
  intro k hk
  have hklen : k.length = n := by
    rw [BitString.eval_sampleList] at hk
    exact BitString.length_of_mem_support_uniformList hk
  apply PMF.bind_apply_mono_on_support
  intro out _
  cases hbreak : merkleBreaksBinding H leafSpace n k out
  · simp
  · rw [isCollision_of_merkleBreaksBinding hlen hklen hbreak]

/-- **The reduction is efficient**: the collision finder of a strict PPT binding adversary is
strict PPT, for a polynomial-time `H` that returns `k.length` bits. -/
theorem isPPT_merkleCollisionFinder
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length) {adversary : MerkleBindingAdversary}
    (hadversary : IsPPT encMerkleBindingOutput adversary) :
    IsPPT (encPair encBits encBits) (merkleCollisionFinder H adversary) := by
  have hpost := (computableInPolyTime_extractMerkleCollision hH hlen).comp
    (show ComputableInPolyTime
      (fun p : (ℕ × List Bool) × MerkleBindingOutput =>
        (p.1.2, (p.2.first.leaf, p.2.second.leaf), p.2.position, p.2.first.path,
          p.2.second.path))
      (encPair (encPair encUnary encBits) encMerkleBindingOutput) _ by fun_prop)
  exact hadversary.bind_with hpost.isPPTOn

/-- Position binding gives negligible success probability to every strict PPT adversary. -/
theorem MerklePositionBinding.negligible (h : MerklePositionBinding H leafSpace)
    (adversary : MerkleBindingAdversary) (hadversary : IsPPT encMerkleBindingOutput adversary) :
    Negligible fun n =>
      Game.succProbability (ProbComp.eval (merkleBindingGame H leafSpace adversary n)) := by
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Establish position binding by bounding every strict PPT adversary's success probability. -/
theorem MerklePositionBinding.of_negligible
    (h : ∀ adversary, IsPPT encMerkleBindingOutput adversary →
      Negligible fun n =>
        Game.succProbability (ProbComp.eval (merkleBindingGame H leafSpace adversary n))) :
    MerklePositionBinding H leafSpace := by
  intro adversary hadversary
  simpa only [Game.advantage_pure_false] using h adversary hadversary

end Binding

/-- **Merkle trees are position binding under collision resistance of the hash on its domain**
([BonehShoup2023], Theorem 8.8, Section 8.9.1, p. 324): if `H` is collision resistant on the
leaf space and the pairs of digests (`merkleHashDomain leafSpace`, the source's `X ∪ Y²`,
Section 8.9, p. 320), then no uniform strict PPT adversary opens a position of a Merkle tree over
`H` to two different leaves of `leafSpace` except with negligible probability. `H` is a
polynomial-time keyed hash with digests of the key's length.

This is Theorem 8.8 for keyed hashes and uniform adversaries, with these differences:
* the hash takes a uniform `n`-bit key, given to the adversary; footnote 1 on p. 290 says that
  this keyed form is the same as the source's system parameter;
* digests have exactly `n` bits, so `Y = {0, 1}ⁿ`;
* the leaf space is any predicate `leafSpace`, of which the source's finite, efficiently
  recognizable and polynomially bounded leaf spaces (Definition 2.9, p. 30) are instances;
* the adversary chooses the depth of the tree, which makes the game stronger than the source's,
  whose scheme has a fixed number of leaves; positions are `0 ≤ i < 2 ^ d`, the padding positions
  included, and written in unary, which covers polynomially bounded positions.

The reduction is `merkleCollisionFinder`, with no loss (`succProbability_merkleBindingGame_le`),
and it is strict PPT (`isPPT_merkleCollisionFinder`). -/
theorem CollisionResistantOn.merklePositionBinding {H : List Bool → List Bool → List Bool}
    {leafSpace : ℕ → List Bool → Bool} (hCR : CollisionResistantOn H (merkleHashDomain leafSpace))
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length) : MerklePositionBinding H leafSpace :=
  MerklePositionBinding.of_negligible fun adversary hadversary =>
    negligible_of_le (hCR.negligible _ (isPPT_merkleCollisionFinder hH hlen hadversary))
      (succProbability_merkleBindingGame_le hlen adversary)

/-- A collision-resistant `HashFamily`, collision resistant on all words, gives position binding
for every leaf space. This is `CollisionResistantOn.merklePositionBinding` through
`CollisionResistantOn.mono`: collision resistance on all words implies it on
`merkleHashDomain leafSpace`. -/
theorem merklePositionBinding_of_hashFamily {H : List Bool → List Bool → List Bool}
    (hH : HashFamily H) (leafSpace : ℕ → List Bool → Bool) : MerklePositionBinding H leafSpace :=
  (CollisionResistantOn.mono hH.collisionResistant
    (.of_forall fun _ _ _ => rfl)).merklePositionBinding hH.polyTime hH.length_eq

end Cslib.Crypto
