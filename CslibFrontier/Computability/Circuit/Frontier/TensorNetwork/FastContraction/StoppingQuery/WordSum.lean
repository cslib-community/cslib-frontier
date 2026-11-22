/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import
  CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.StoppingQuery

/-!
# Completing the stopping sum from product words

Each assignment path names a ring product. Its selected representative coefficient supplies
the first word of a carry-save leaf, while the second word is zero. A complete tree of height
`L` enumerates exactly the assignments below `2 ^ L`, so the leaf definition needs no range
guard. The existing compressor and finishing-adder semantics identify its output with the
coefficient bit of the actual sum of products.
-/

public section

namespace Cslib.Circuits.Frontier.FastContraction.StoppingQuery.WordSum

open BitString Boolean Boolean.CarrySaveQuery GaloisRingArith InterpolationGrid

/-- A raw path requests one product word, paired with zero. There is no padding test:
complete-tree paths already enumerate the intended assignment interval. -/
@[expose] noncomputable def leaves (m p vertices : ℕ)
    (entry : ℕ → ℕ → Ring p (modulus m)) (coefficient : ℕ)
    (path : List Bool) : BitString (p + p) :=
  residuePair p ((representative m p (∏ vertex ∈ Finset.range vertices,
    entry (binaryValue path) vertex)).coeff coefficient)

/-- A leaf reads the selected product bit, or the constant false second word. This holds
for every raw path, with only the precision-bit bound required by the continuation. -/
theorem component_leaves (m p vertices : ℕ)
    (entry : ℕ → ℕ → Ring p (modulus m)) (coefficient : ℕ)
    (path : List Bool) (carry : Bool) (bit : Fin p) :
    component (leaves m p vertices entry coefficient path) carry bit =
      if carry then false else
        ((representative m p (∏ vertex ∈ Finset.range vertices,
          entry (binaryValue path) vertex)).coeff coefficient).val.testBit bit.val :=
  component_residuePair p _ carry bit

/-- The complete native word-sum tree has the same output as the selected representative
coefficient bit of the full assignment sum of vertex products. -/
theorem bit_sum (m p L vertices : ℕ)
    (entry : ℕ → ℕ → Ring p (modulus m)) (coefficient : ℕ) (bit : Fin p) :
    (carryLookaheadAdd p).eval interpretation
      (tree (leaves m p vertices entry coefficient) L []) bit =
      ((representative m p (∑ assignment ∈ Finset.range (2 ^ L),
        ∏ vertex ∈ Finset.range vertices, entry assignment vertex)).coeff
          coefficient).val.testBit bit.val := by
  let rows (assignment : ℕ) :=
    (representative m p (∏ vertex ∈ Finset.range vertices, entry assignment vertex)).coeff
      coefficient
  have hcast : ((∑ assignment ∈ Finset.range (2 ^ L), (rows assignment).val : ℕ) :
      ZMod (2 ^ p)) = (representative m p (∑ assignment ∈ Finset.range (2 ^ L),
        ∏ vertex ∈ Finset.range vertices, entry assignment vertex)).coeff coefficient := by
    simp [rows, representative]
  have hval := congrArg ZMod.val hcast
  simp only [ZMod.val_natCast] at hval
  rw [← testBit_equivFin ((carryLookaheadAdd p).eval interpretation
    (tree (leaves m p vertices entry coefficient) L [])) bit,
    val_eval_carryLookaheadAdd_pair, pairVal_tree_mod]
  change (leafSum (fun path => (fun j => residuePair p (rows j)) (binaryValue path))
    L [] % 2 ^ p).testBit bit.val = _
  rw [leafSum_binaryValue (fun j => residuePair p (rows j)) L []]
  simp only [binaryValue, List.foldl_nil, Nat.zero_mul, Nat.zero_add, residuePair, pairVal_append,
    Equiv.apply_symm_apply, val_equivFin_false, Nat.add_zero]
  rw [hval]

end Cslib.Circuits.Frontier.FastContraction.StoppingQuery.WordSum
