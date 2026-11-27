/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.MerkleDamgard
import CslibFrontier.Crypto.Computational.MerkleTree.Binding
import CslibFrontier.Tactic.PPT
import CslibFrontierTests.Crypto.MerkleTestHash

/-!
# Tests for Merkle-tree verification and position binding

Under a sixteen-bit hash with no collisions on the words involved, the three-leaf tree's honest
openings are accepted, while a wrong leaf, a short path, an out-of-range position and a label
that is not a digest are rejected, and the depth check rejects a pair of child labels posing as a
leaf one level up. Under a toy XOR hash, which reads only a prefix of its input, an honest path
also opens a position to a wrong leaf; this binding break yields a collision on the hash's domain
through the reduction. Under a hash that ignores its message, an efficient adversary breaks
position binding with one-bit leaves at every parameter, so `MerklePositionBinding` is not vacuous.
A break that needs labels which are not digests, whose collision would lie outside the leaf and
child-pair domain of [BonehShoup2023], Section 8.9, is rejected by the verifier, and so is a break
whose leaves lie outside the leaf space.
-/

namespace CslibFrontierTests.Crypto.MerkleBinding

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open CslibFrontierTests.Crypto.MerkleTestHash

/-- Three leaves of different lengths, in a tree of depth two. -/
abbrev leaves : List (List Bool) := [[true], [false, true], [true, true]]

/-- The key at security parameter `2`. -/
abbrev key : List Bool := [false, true]

/-! ### Verification under a collision-free hash -/

/-- A keyed hash with sixteen-bit digests and no collisions among the words below, so only honest
openings are accepted. -/
def idHash (_ x : List Bool) : List Bool := polyHash x

-- All four positions of the padded depth-two tree are accepted with their computed paths.
example : ∀ i : Fin 4,
    merkleVerify idHash key 2 (merkleRoot idHash key leaves) i (leaves.getD i [])
      (merklePath idHash key leaves i) = true := by decide +kernel

-- A wrong leaf at position `1` is rejected.
example : merkleVerify idHash key 2 (merkleRoot idHash key leaves) 1 [true, true]
    (merklePath idHash key leaves 1) = false := by decide +kernel

-- A truncated path is rejected (its recomputed root differs too; `pairLeaf` below isolates the
-- length check).
example : merkleVerify idHash key 2 (merkleRoot idHash key leaves) 1 [false, true]
    (merklePath idHash key leaves 1).tail = false := by decide +kernel

-- A position outside the depth-two tree is rejected, though its path recomputes the root.
example : merkleRootOfPath idHash key [true] 4 (merklePath idHash key leaves 0) =
    merkleRoot idHash key leaves := by decide +kernel

example : merkleVerify idHash key 2 (merkleRoot idHash key leaves) 4 [true]
    (merklePath idHash key leaves 0) = false := by decide +kernel

-- A label that is not a sixteen-bit digest is rejected, even when the rest of the path is honest.
example : merkleVerify idHash key 2 (merkleRoot idHash key leaves) 1 [false, true]
    ((merklePath idHash key leaves 1).set 0 []) = false := by decide +kernel

/-- The pair of the two leaf labels of the tree over `[[true], [false]]`, as one word. -/
abbrev pairLeaf : List Bool := encPair encBits encBits (idHash key [true], idHash key [false])

-- Leaves and internal nodes share the hash, so this pair, as a leaf with the empty path,
-- recomputes the root of the depth-one tree over `[[true], [false]]`.
example : merkleRootOfPath idHash key pairLeaf 0 [] = merkleRoot idHash key [[true], [false]] := by
  decide +kernel

-- The length check rejects it at depth one, the depth of that tree.
example : merkleVerify idHash key 1 (merkleRoot idHash key [[true], [false]]) 0 pairLeaf [] =
    false := by decide +kernel

/-! ### A binding break and its collision -/

/-- A toy keyed hash, the XOR of the first two `k.length`-bit blocks of its input (each padded or
truncated to `k.length` bits). It ignores the rest of its input. -/
def xorHash (k x : List Bool) : List Bool :=
  (padOrTake k.length (x.take k.length)).zipWith Bool.xor
    (padOrTake k.length (x.drop k.length))

theorem length_xorHash (k x : List Bool) : (xorHash k x).length = k.length := by
  simp [xorHash]

theorem computableInPolyTime_xorHash :
    ComputableInPolyTime (fun p : List Bool × List Bool => xorHash p.1 p.2)
      (encPair encBits encBits) encBits := by
  unfold xorHash padOrTake
  polytime

/-- Position `1` of the tree over `leaves` under `xorHash`, opened by its honest path both to its
leaf `[false, true]` and to `[true, true]`. -/
abbrev breakOut : MerkleBindingOutput :=
  { root := merkleRoot xorHash key leaves, position := 1,
    first := ⟨[false, true], merklePath xorHash key leaves 1⟩,
    second := ⟨[true, true], merklePath xorHash key leaves 1⟩ }

/-- The leaf space of two-bit words. -/
abbrev twoBitLeaves (_ : ℕ) (x : List Bool) : Bool := x.length == 2

example : merkleBreaksBinding xorHash twoBitLeaves 2 key breakOut = true := by decide

-- The same break with the leaf `[true]`, outside the leaf space, does not count.
example : merkleBreaksBinding xorHash twoBitLeaves 2 key
    { breakOut with second := ⟨[true], merklePath xorHash key leaves 1⟩ } = false := by decide

-- The two openings first differ in the hash inputs one level below the root.
example : extractMerkleCollision xorHash key [false, true] [true, true] 1
    (merklePath xorHash key leaves 1) (merklePath xorHash key leaves 1) =
      ([true, true, true, false, false, false, true],
        [true, true, true, false, false, true, true]) := by decide

-- Both are pairs of two-bit digests, so the collision lies in the hash's domain.
example : isCollision xorHash (merkleHashDomain twoBitLeaves) 2 key
    (extractMerkleCollision xorHash key [false, true] [true, true] 1
      (merklePath xorHash key leaves 1) (merklePath xorHash key leaves 1)).1
    (extractMerkleCollision xorHash key [false, true] [true, true] 1
      (merklePath xorHash key leaves 1) (merklePath xorHash key leaves 1)).2 = true :=
  isCollision_of_merkleBreaksBinding length_xorHash (k := key) rfl (out := breakOut) (by decide)

/-! ### Position binding is not vacuous -/

/-- A keyed hash that ignores its message. -/
def constHash (k _ : List Bool) : List Bool := k

/-- The adversary that opens position `0` of the depth-zero tree with root `k` to `[false]` and to
`[true]`. -/
def constBreaker : MerkleBindingAdversary := fun _ k =>
  pure { root := k, position := 0, first := ⟨[false], []⟩, second := ⟨[true], []⟩ }

theorem isPPT_constBreaker : IsPPT encMerkleBindingOutput constBreaker := by
  unfold constBreaker
  ppt

-- Encoded words unchanged: the binding output keeps the grouped layout of the former tuple
-- `(root, position), (leaf₁, path₁), (leaf₂, path₂)`.
example (out : MerkleBindingOutput) :
    encMerkleBindingOutput out =
      encPair (encPair encBits encUnary)
          (encPair (encPair encBits (encList encBits)) (encPair encBits (encList encBits)))
        ((out.root, out.position), (out.first.leaf, out.first.path),
          (out.second.leaf, out.second.path)) := rfl

-- The reduction applies to this adversary for an efficient length-preserving hash.
example : IsPPT (encPair encBits encBits) (merkleCollisionFinder xorHash constBreaker) :=
  isPPT_merkleCollisionFinder computableInPolyTime_xorHash length_xorHash isPPT_constBreaker

/-- The leaf space of one-bit words. -/
abbrev oneBitLeaves (_ : ℕ) (x : List Bool) : Bool := x.length == 1

/-- Merkle trees over `constHash` with one-bit leaves are not position-binding: `constBreaker`
wins at every parameter. -/
theorem not_merklePositionBinding_constHash : ¬ MerklePositionBinding constHash oneBitLeaves := by
  intro h
  have hwin (n : ℕ) : 1 ≤ Game.succProbability
      (ProbComp.eval (merkleBindingGame constHash oneBitLeaves constBreaker n)) := by
    have hbne : ([false] != [true]) = true := rfl
    have heval : ProbComp.eval (merkleBindingGame constHash oneBitLeaves constBreaker n) =
        PMF.pure true := by
      simp only [merkleBindingGame, constBreaker, merkleBreaksBinding, MerkleOpening.verify_id,
        merkleVerify, merkleRootOfPath, constHash, pure_bind,
        ProbComp.eval_bind, BitString.eval_sampleList, ProbComp.eval_pure]
      simp [oneBitLeaves, hbne]
    rw [Game.succProbability, heval, PMF.pure_apply_self, ENNReal.toNNReal_one]
  exact not_negligible_const one_ne_zero
    (negligible_of_le (h.negligible constBreaker isPPT_constBreaker) hwin)

/-! ### Path labels must be digests -/

/-- A toy hash with digests of the key's length: it returns words of the key's length and maps
every other word to zeros. -/
def keyLengthHash (k x : List Bool) : List Bool :=
  if x.length = k.length then x else List.replicate k.length false

/-- Under the one-bit key `[true]`, position `0` of a depth-one tree opened to the one-bit leaves
`[false]` and `[true]`, each with the two-bit label `[true, true]`. -/
abbrev labelBreak : MerkleBindingOutput :=
  { root := [false], position := 0, first := ⟨[false], [[true, true]]⟩,
    second := ⟨[true], [[true, true]]⟩ }

-- Both openings recompute the root: a verifier without the label-length check would accept them.
example : merkleRootOfPath keyLengthHash [true] [false] 0 [[true, true]] = [false] ∧
    merkleRootOfPath keyLengthHash [true] [true] 0 [[true, true]] = [false] := by decide

-- The reduction would extract the two root inputs, five-bit words: neither a one-bit leaf nor a
-- pair of one-bit digests, which has `3 * 1 + 1 = 4` bits, so not a collision on the leaf and
-- child-pair domain of [BonehShoup2023], Section 8.9.
example : extractMerkleCollision keyLengthHash [true] [false] [true] 0 [[true, true]]
    [[true, true]] =
      (encPair encBits encBits ([false], [true, true]),
        encPair encBits encBits ([true], [true, true])) := by decide

example : merkleHashDomain oneBitLeaves 1 (encPair encBits encBits ([false], [true, true])) =
    false := by decide

-- The verifier rejects the two-bit label, so the openings do not break binding.
example : merkleVerify keyLengthHash [true] 1 [false] 0 [false] [[true, true]] = false := by
  decide

example : merkleBreaksBinding keyLengthHash oneBitLeaves 1 [true] labelBreak = false := by decide

/-! ### Theorem 8.8 -/

-- Compression families give position-binding Merkle trees for every leaf space, and PPT
-- collision finders, through Merkle–Damgård.
example {h : List Bool → List Bool → List Bool} (hh : CompressionFamily h)
    (leafSpace : ℕ → List Bool → Bool) :
    MerklePositionBinding (merkleDamgard h) leafSpace ∧
      IsPPT (encPair encBits encBits)
        (merkleCollisionFinder (merkleDamgard h) constBreaker) :=
  ⟨merklePositionBinding_of_hashFamily hh.hashFamily_merkleDamgard leafSpace,
    isPPT_merkleCollisionFinder hh.hashFamily_merkleDamgard.polyTime
      hh.hashFamily_merkleDamgard.length_eq isPPT_constBreaker⟩

-- A hash collision resistant on all words is collision resistant on the domain of the tree's hash,
-- so Theorem 8.8 applies to it.
example {H : List Bool → List Bool → List Bool} (hH : HashFamily H) :
    MerklePositionBinding H oneBitLeaves :=
  (CollisionResistantOn.mono hH.collisionResistant (.of_forall fun _ _ _ => rfl)
    (valid₁ := merkleHashDomain oneBitLeaves)).merklePositionBinding hH.polyTime hH.length_eq

end CslibFrontierTests.Crypto.MerkleBinding
