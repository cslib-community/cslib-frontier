/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF.Uniform

/-!
# Fixed patterns in uniform finite functions

A uniform function to a finite alphabet agrees with a prescribed pattern on a set of `r`
coordinates with probability `|alphabet|⁻ʳ`. Restriction to those coordinates is uniform;
the agreement event is one point of that function space. Unrestricted coordinates contribute
no extra conditions, even when the prescribed pattern outside the set is arbitrary.
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

/-- Agreement with a fixed pattern on a finite set has inverse alphabet-size power probability. -/
theorem toOuterMeasure_uniformOfFintype_pi_eqOn {ι α : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    (I : Finset ι) (pattern : ι → α) :
    (uniformOfFintype (ι → α)).toOuterMeasure {f | ∀ i ∈ I, f i = pattern i} =
      ((Fintype.card α : ℝ≥0∞) ^ I.card)⁻¹ := by
  classical
  have hevent : {f : ι → α | ∀ i ∈ I, f i = pattern i} =
      (fun f : ι → α => I.restrict f) ⁻¹' {I.restrict pattern} := by
    ext f
    change (∀ i ∈ I, f i = pattern i) ↔ I.restrict f = I.restrict pattern
    constructor
    · intro h
      funext i
      exact h i i.property
    · intro h i hi
      exact congrFun h ⟨i, hi⟩
  rw [hevent, ← PMF.toOuterMeasure_map_apply, uniformOfFintype_pi_map_restrict,
    PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply]
  simp only [Fintype.card_fun, Fintype.card_coe, Nat.cast_pow]

end Cslib.Probability.PMF
