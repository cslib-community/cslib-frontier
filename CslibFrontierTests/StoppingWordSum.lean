/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import
  CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.StoppingQuery.WordSum

/-!
Word-sum leaves remain defined on arbitrary raw paths. Complete-tree evaluation visits exactly
the intended assignment interval, handles modular overflow, and agrees with the described
network's contraction without materializing either assignment products or entry tables.
-/

namespace CslibFrontierTests.StoppingWordSum

open Cslib Cslib.BitString Cslib.Circuits.Boolean CarrySaveQuery
open Cslib.Circuits.Frontier Cslib.Circuits.Frontier.FastContraction
open StoppingQuery GaloisRingArith

private noncomputable def sparseEntry (assignment _ : ℕ) : Ring 3 (modulus 0) :=
  if assignment = 5 then 1 else 0

-- This raw leaf remains meaningful even outside the paths of a height-one tree.
example : component (WordSum.leaves 0 3 1 sparseEntry 0 [true, false, true]) false
    ⟨0, by decide⟩ = true := by
  rw [WordSum.component_leaves]
  simp only [Bool.false_eq_true, ↓reduceIte, Finset.prod_range_one]
  change ((representative 0 3 1).coeff 0).val.testBit 0 = true
  simpa [InterpolationGrid.factorBit, InterpolationGrid.factor] using
    (InterpolationGrid.factorBit_eq 0 3 0 0 0 ⟨0, by decide⟩ ⟨0, by decide⟩).symm

-- The same raw path has a zero second word, regardless of its product value.
example (carryBit : Fin 3) :
    component (WordSum.leaves 0 3 1 sparseEntry 0 [true, false, true]) true carryBit = false :=
  WordSum.component_leaves 0 3 1 sparseEntry 0 [true, false, true] true carryBit

-- Only assignments zero and one are visited at height one; assignment five is excluded.
example (bit : Fin 3) : (carryLookaheadAdd 3).eval interpretation
    (tree (WordSum.leaves 0 3 1 sparseEntry 0) 1 []) bit = false := by
  rw [WordSum.bit_sum]
  norm_num [sparseEntry, representative, Finset.sum_range_succ]

-- Eight empty products sum to zero modulo the three-bit precision.
example (bit : Fin 3) : (carryLookaheadAdd 3).eval interpretation
    (tree (WordSum.leaves 0 3 0 sparseEntry 0) 3 []) bit = false := by
  have hz : (8 : Ring 3 (modulus 0)) = 0 := by
    have h : (8 : ZMod (2 ^ 3)) = 0 := by decide
    simpa only [map_ofNat, map_zero] using
      congrArg (algebraMap (ZMod (2 ^ 3)) (Ring 3 (modulus 0))) h
  rw [WordSum.bit_sum]
  simp only [Finset.prod_range_zero, Finset.sum_const, Finset.card_range, nsmul_one]
  change ((representative 0 3 (8 : Ring 3 (modulus 0))).coeff 0).val.testBit bit.val = false
  rw [hz]
  simp [representative]

-- The bridge composes directly with the actual described-network semantics.
example {T : Type} (m p : ℕ) (d : DescribedNetwork T)
    (eval : T → List Bool → Ring p (modulus m)) (coefficient : ℕ) (bit : Fin p) :
    (carryLookaheadAdd p).eval interpretation
      (tree (WordSum.leaves m p d.vertices.length (networkEntry d eval) coefficient)
        d.numEdges []) bit =
      ((representative m p (d.contraction eval)).coeff coefficient).val.testBit bit.val := by
  rw [WordSum.bit_sum, sum_prod_networkEntry]

end CslibFrontierTests.StoppingWordSum
