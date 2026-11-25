/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.CircleGaps

/-!
# Real representatives of a finite directed circular order

A finite clockwise enumeration admits real angle representatives in one open turn,
in reverse linear order. The argument cut is chosen in the prescribed gap before the
last clockwise entry. Singleton enumerations are included.
-/

public section

namespace Cslib.Polygonal

/-- Choose one open turn of real representatives for a finite clockwise enumeration.
Only the circular order at its specified last entry is needed. -/
theorem exists_reverse_ordered_angle_lift (n : ℕ) (dir : Fin (n + 1) → Real.Angle)
    (hinj : Function.Injective dir)
    (horder : ∀ i j, i ≠ Fin.last n → j ≠ Fin.last n → i ≠ j →
      (sbtw (dir (Fin.last n)) (dir i) (dir j) ↔ j.val < i.val)) :
    ∃ cut : ℝ, ∃ L : Real.Angle → ℝ,
      (∀ i, L (dir i) ∈ Set.Ioo cut (cut + 2 * Real.pi)) ∧
      (∀ φ, (L φ : Real.Angle) = φ) ∧
      (∀ i j, L (dir i) < L (dir j) ↔ j.val < i.val) := by
  classical
  let : Fact ((0 : ℝ) < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  let base := (dir (Fin.last n)).toReal
  let L : Real.Angle → ℝ := fun φ => (AddCircle.equivIco (2 * Real.pi) base φ).val
  have hcoe (φ : Real.Angle) : (L φ : Real.Angle) = φ := AddCircle.coe_equivIco
  have hmem (φ : Real.Angle) : L φ ∈ Set.Ico base (base + 2 * Real.pi) :=
    (AddCircle.equivIco (2 * Real.pi) base φ).property
  have ho : L (dir (Fin.last n)) = base := by
    conv_lhs => rw [← Real.Angle.coe_toReal (dir (Fin.last n))]
    exact AddCircle.equivIco_coe_of_mem (p := 2 * Real.pi)
      (a := base) ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hstrict (i : Fin (n + 1)) (hi : i ≠ Fin.last n) : base < L (dir i) :=
    lt_of_le_of_ne (hmem _).1 fun heq => hi (hinj (by
      rw [← hcoe (dir i), ← hcoe (dir (Fin.last n)), ho, heq]))
  let M := Finset.univ.sup' Finset.univ_nonempty fun i => L (dir i)
  have hM : M < base + 2 * Real.pi :=
    (Finset.sup'_lt_iff _).mpr fun i _ => (hmem (dir i)).2
  let ε := (base + 2 * Real.pi - M) / 2
  refine ⟨base - ε, L, fun i => ?_, hcoe, fun i j => ?_⟩
  · have hMi : L (dir i) ≤ M := Finset.le_sup' (fun i => L (dir i)) (Finset.mem_univ i)
    have hlo := (hmem (dir i)).1
    constructor <;> dsimp only [ε] <;> linarith
  · by_cases hij : i = j
    · subst hij
      simp
    by_cases hi : i = Fin.last n
    · subst hi
      rw [ho]
      exact iff_of_true (hstrict j (Ne.symm hij)) (Fin.lt_last_iff_ne_last.mpr (Ne.symm hij))
    by_cases hj : j = Fin.last n
    · subst hj
      rw [ho]
      exact iff_of_false (not_lt.mpr (hmem _).1) (not_lt.mpr (Fin.le_last i))
    have h := sbtw_angle_cut_iff_lt
      ⟨hstrict i hi, (hmem _).2⟩ ⟨hstrict j hj, (hmem _).2⟩
    rw [hcoe, hcoe, ← ho, hcoe] at h
    exact h.symm.trans (horder i j hi hj hij)

end Cslib.Polygonal
