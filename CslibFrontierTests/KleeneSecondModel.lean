/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module

public import CslibFrontier.Languages.CombinatoryLogic.KleeneSecondModel

/-! Clients of Kleene's second model `K₂` and of the continuity theorem, under module
encapsulation. The element running `joinRight` returns its argument, as `s ⬝ k ⬝ k` does; the
element running `joinRight` after the successor computes the shift; the indicator of `x = 0` is
discontinuous, so no element of `K₂` and no oracle code computes it; the identity element lies in
the computable sub-pca `K₂^rec`. -/

public section

namespace CslibFrontierTests.KleeneSecondModel

open Nat.RecursiveIn Nat.RecursiveIn.Code Cslib Cslib.PartialCombinatoryAlgebra

/-- The element running `joinRight` with any parameter returns its argument. -/
theorem app_kleeneTwoCode_joinRight (p x : ℕ → ℕ) :
    kleeneTwo.app (kleeneTwoCode joinRight p) x = Part.some x :=
  kleeneTwo_app_eq_some_iff.2 (by rw [kleeneTwoEval_kleeneTwoCode, eval_joinRight])

/-- The completion criterion of #6831: the element representing the identity behaves as
`s ⬝ k ⬝ k`. -/
example (x : ℕ → ℕ) :
    kleeneTwo.app (kleeneTwoCode joinRight fun _ => 0) x = kleeneTwo.app kleeneTwo.i x := by
  rw [app_i, app_kleeneTwoCode_joinRight]

/-- The shift `x ↦ (n ↦ x (n + 1))` is computed by reading the input at `n + 1`. -/
theorem app_shift (x : ℕ → ℕ) :
    kleeneTwo.app (kleeneTwoCode (comp joinRight Code.succ) fun _ => 0) x =
      Part.some fun n => x (n + 1) := by
  refine kleeneTwo_app_eq_some_iff.2 ?_
  rw [kleeneTwoEval_kleeneTwoCode]
  funext n
  change (Nat.succ : ℕ →. ℕ) n >>= Code.eval _ joinRight = _
  rw [eval_joinRight]
  exact Part.bind_some _ _

/-- The shift is continuous, by the continuity theorem. -/
example : Continuous fun (x : ℕ → ℕ) (n : ℕ) => x (n + 1) :=
  continuous_iff_exists_kleeneTwo_app.2 ⟨_, app_shift⟩

open Classical in
/-- The indicator of `x = 0` is discontinuous: no element of `K₂` represents it. -/
example : ¬ ∃ a, ∀ x, kleeneTwo.app a x = Part.some fun _ => if x = 0 then 1 else 0 := by
  rw [← continuous_iff_exists_kleeneTwo_app, continuous_iff_forall_exists_cylinder]
  intro h
  obtain ⟨k, hk⟩ := h 0 0
  have := hk (Function.update 0 k 1) (PiNat.update_mem_cylinder _ _ _)
  simp at this

open Classical in
/-- The indicator of `x = 0` is not computable relative to any oracle. -/
example : ¬ ∃ (p : ℕ → ℕ) (c : Code), ∀ (x : ℕ → ℕ) n,
    Code.eval (Partrec.join p x) c n = Part.some (if x = 0 then 1 else 0) := by
  intro ⟨p, c, h⟩
  obtain ⟨k, hk⟩ := continuous_iff_forall_exists_cylinder.1 (continuous_of_eval h) 0 0
  have := hk (Function.update 0 k 1) (PiNat.update_mem_cylinder _ _ _)
  simp at this

/-- The identity element is computable, and in `K₂^rec` it returns its argument. -/
example (x : {a : ℕ → ℕ // Computable a}) :
    (kleeneTwoRec.app ⟨kleeneTwoCode joinRight fun _ => 0,
      computable_kleeneTwoCode _ (Computable.const 0)⟩ x).map Subtype.val = Part.some x.1 := by
  rw [map_val_kleeneTwoRec_app, app_kleeneTwoCode_joinRight]

end CslibFrontierTests.KleeneSecondModel
