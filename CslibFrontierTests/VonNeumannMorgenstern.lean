/-
Copyright (c) 2026 Matthew Doty, Vinicius de Padua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Vinicius de Padua
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.GameTheory.VonNeumannMorgenstern
public import Mathlib.Data.Fin.VecNotation

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Checked clients for the von Neumann–Morgenstern expected utility theorem

This test module exercises `Cslib.GameTheory.VonNeumannMorgenstern` on concrete finite outcome
spaces (`Fin 3`):

1. **Concrete 3-outcome vNM representation and affine uniqueness**: explicit utility `![0, 1, 3]`
   on `Fin 3`, verifying the vNM axioms (including Archimedean), positive affine invariance,
   cardinal uniqueness once two anchor values are fixed, and the degenerate all-indifferent case.
2. **Allais-type independence violation**: a rational preference on `PMF (Fin 3)` exhibiting the
   classic Allais choices (`L₁ ≻ L₂` alongside `L₄ ≻ L₃`), proved to violate `IsIndependentOn`
   and hence to admit no vNM utility representation.
3. **Lexicographic preference violating continuity**: a preference on `PMF (Fin 3)` proved to be
   both rational and independent yet neither continuous nor Archimedean, and hence admitting no
   vNM utility representation.
-/

public section

namespace CslibFrontierTests.VonNeumannMorgenstern

open Cslib.GameTheory.VonNeumannMorgenstern
open scoped unitInterval

abbrev X₃ : Finset (Fin 3) := Finset.univ

private theorem mem_lotteriesOn_univ (p : PMF (Fin 3)) : p ∈ lotteriesOn (X₃ : Set (Fin 3)) := by
  simp only [X₃, Finset.coe_univ, mem_lotteriesOn, Set.subset_univ]

/-! ### Client 1: 3-outcome vNM representation, affine uniqueness, and degenerate case -/

/-- Explicit utility function on `Fin 3`: outcomes `0, 1, 2` have utilities `0, 1, 3`. -/
@[expose] def u₃ : Fin 3 → ℝ := ![0, 1, 3]

/-- Expected-utility preference on `Fin 3` induced by `u₃`. -/
@[expose] def rel₃ (p q : PMF (Fin 3)) : Prop :=
  expectedUtility X₃ u₃ q ≤ expectedUtility X₃ u₃ p

theorem isVNMUtility_rel₃ : IsVNMUtility X₃ rel₃ u₃ :=
  fun _ _ _ _ => Iff.rfl

theorem axioms_rel₃ :
    IsRationalOn (X₃ : Set (Fin 3)) rel₃ ∧
    IsIndependentOn (X₃ : Set (Fin 3)) rel₃ ∧
    IsContinuousOn (X₃ : Set (Fin 3)) rel₃ ∧
    IsArchimedeanOn (X₃ : Set (Fin 3)) rel₃ := by
  have hR := isVNMUtility_rel₃.isRationalOn
  have hI := isVNMUtility_rel₃.isIndependentOn
  have hC := isVNMUtility_rel₃.isContinuousOn
  exact ⟨hR, hI, hC, (isContinuousOn_iff_isArchimedeanOn hR hI).mp hC⟩

theorem isVNMUtility_rel₃_posAffine :
    IsVNMUtility X₃ rel₃ (fun x => 2 * u₃ x + 7) :=
  isVNMUtility_rel₃.posAffine (by norm_num) 7

/-- Fixing two distinct anchor values pins down the remaining utility value uniquely. -/
theorem rel₃_unique_anchor {w : Fin 3 → ℝ} (hw : IsVNMUtility X₃ rel₃ w)
    (h0 : w 0 = 0) (h2 : w 2 = 3) : w 1 = 1 := by
  obtain ⟨a, b, _, haff⟩ := isVNMUtility_rel₃.exists_posAffine_eq hw
  have e0 := haff 0 (Finset.mem_univ (0 : Fin 3))
  have e1 := haff 1 (Finset.mem_univ (1 : Fin 3))
  have e2 := haff 2 (Finset.mem_univ (2 : Fin 3))
  simp only [u₃, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at e0 e1 e2
  linarith

/-- The all-indifferent preference relation on `Fin 3` is represented by the constant zero utility,
and any vNM utility representing it is constant. -/
theorem degenerate_indiff_unique {v : Fin 3 → ℝ}
    (hv : IsVNMUtility X₃ (fun _ _ => True) v) (x y : Fin 3) : v x = v y := by
  have h0 : IsVNMUtility X₃ (fun _ _ => True) (fun _ => 0) := by
    intro p _ q _
    simp [expectedUtility]
  obtain ⟨a, b, _, haff⟩ := h0.exists_posAffine_eq hv
  have hx := haff x (Finset.mem_univ x)
  have hy := haff y (Finset.mem_univ y)
  linarith

/-! ### Client 2: Allais-type preference violating independence -/

/-- Nonlinear certainty-effect score on `Fin 3` lotteries reproducing the Allais choices. -/
@[expose] noncomputable def allaisScore (p : PMF (Fin 3)) : ℝ :=
  2 * (p 2).toReal + (p 1).toReal ^ 2

/-- Preference relation induced by `allaisScore`. -/
@[expose] def allaisRel (p q : PMF (Fin 3)) : Prop :=
  allaisScore q ≤ allaisScore p

theorem isRationalOn_allaisRel : IsRationalOn (X₃ : Set (Fin 3)) allaisRel where
  complete _ _ _ _ := le_total _ _
  trans _ _ _ _ _ _ h1 h2 := le_trans h2 h1

/-- Weight `10/11` used in the Allais paradox gamble. -/
@[expose] noncomputable def w10_11 : I := ⟨10 / 11, by norm_num, by norm_num⟩

/-- Weight `11/100` used to form the four Allais paradox lotteries. -/
@[expose] noncomputable def w11_100 : I := ⟨11 / 100, by norm_num, by norm_num⟩

/-- Auxiliary gamble paying outcome `2` with probability `10/11` and outcome `0` otherwise. -/
@[expose] noncomputable def allaisGamble : PMF (Fin 3) :=
  mix w10_11 (PMF.pure 2) (PMF.pure 0)

/-- The four Allais lotteries satisfy `L₁ ≻ L₂` and `L₄ ≻ L₃` under `allaisRel`. -/
theorem allais_choices :
    strictPref allaisRel (mix w11_100 (PMF.pure 1) (PMF.pure 1))
      (mix w11_100 allaisGamble (PMF.pure 1)) ∧
    strictPref allaisRel (mix w11_100 allaisGamble (PMF.pure 0))
      (mix w11_100 (PMF.pure 1) (PMF.pure 0)) := by
  have h12 : allaisScore (mix w11_100 allaisGamble (PMF.pure 1)) <
      allaisScore (mix w11_100 (PMF.pure 1) (PMF.pure 1)) := by
    simp only [allaisScore, allaisGamble, mix_apply_toReal, w11_100, w10_11,
      PMF.pure_apply, Fin.reduceEq, ↓reduceIte, ENNReal.toReal_one, ENNReal.toReal_zero]
    norm_num
  have h34 : allaisScore (mix w11_100 (PMF.pure 1) (PMF.pure 0)) <
      allaisScore (mix w11_100 allaisGamble (PMF.pure 0)) := by
    simp only [allaisScore, allaisGamble, mix_apply_toReal, w11_100, w10_11,
      PMF.pure_apply, Fin.reduceEq, ↓reduceIte, ENNReal.toReal_one, ENNReal.toReal_zero]
    norm_num
  exact ⟨⟨le_of_lt h12, not_le.mpr h12⟩, ⟨le_of_lt h34, not_le.mpr h34⟩⟩

/-- `allaisRel` violates the independence axiom. -/
theorem not_isIndependentOn_allaisRel : ¬ IsIndependentOn (X₃ : Set (Fin 3)) allaisRel := by
  intro hI
  obtain ⟨h12, h43⟩ := allais_choices
  have hw : 0 < (w11_100 : ℝ) := by dsimp [w11_100]; norm_num
  have h1q : strictPref allaisRel (PMF.pure 1) allaisGamble :=
    (hI.mix_strictPref_left_iff (mem_lotteriesOn_univ _) (mem_lotteriesOn_univ _)
      (mem_lotteriesOn_univ _) hw).mpr h12
  have hq1 : strictPref allaisRel allaisGamble (PMF.pure 1) :=
    (hI.mix_strictPref_left_iff (mem_lotteriesOn_univ _) (mem_lotteriesOn_univ _)
      (mem_lotteriesOn_univ _) hw).mpr h43
  exact h1q.2 hq1.1

/-- `allaisRel` has no von Neumann–Morgenstern utility representation. -/
theorem not_exists_isVNMUtility_allaisRel : ¬ ∃ u : Fin 3 → ℝ, IsVNMUtility X₃ allaisRel u :=
  fun ⟨_, hu⟩ => not_isIndependentOn_allaisRel hu.isIndependentOn

/-! ### Client 3: Lexicographic preference violating continuity -/

/-- Lexicographic preference on `PMF (Fin 3)`: maximize the probability of outcome `2`, breaking
ties by maximizing the probability of outcome `1`. -/
def lexRel (p q : PMF (Fin 3)) : Prop :=
  (q 2).toReal < (p 2).toReal ∨ ((p 2).toReal = (q 2).toReal ∧ (q 1).toReal ≤ (p 1).toReal)

theorem isRationalOn_lexRel : IsRationalOn (X₃ : Set (Fin 3)) lexRel where
  complete p _ q _ := by
    rcases lt_trichotomy (p 2).toReal (q 2).toReal with h | h | h
    · exact Or.inr (Or.inl h)
    · rcases le_total (q 1).toReal (p 1).toReal with h1 | h1
      · exact Or.inl (Or.inr ⟨h, h1⟩)
      · exact Or.inr (Or.inr ⟨h.symm, h1⟩)
    · exact Or.inl (Or.inl h)
  trans p _ q _ r _ h1 h2 := by
    rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
    · exact Or.inl (lt_trans h2 h1)
    · exact Or.inl (e2 ▸ h1)
    · exact Or.inl (e1.symm ▸ h2)
    · exact Or.inr ⟨e1.trans e2, le_trans h2 h1⟩

theorem isIndependentOn_lexRel : IsIndependentOn (X₃ : Set (Fin 3)) lexRel := by
  intro p _ q _ r _ a ha
  simp only [lexRel, mix_apply_toReal]
  have hmul_lt :
      (a : ℝ) * (q 2).toReal + (1 - a) * (r 2).toReal <
        (a : ℝ) * (p 2).toReal + (1 - a) * (r 2).toReal ↔ (q 2).toReal < (p 2).toReal := by
    constructor <;> intro h <;> nlinarith
  have hmul_eq :
      (a : ℝ) * (p 2).toReal + (1 - a) * (r 2).toReal =
        (a : ℝ) * (q 2).toReal + (1 - a) * (r 2).toReal ↔ (p 2).toReal = (q 2).toReal := by
    constructor <;> intro h <;> nlinarith
  have hmul_le :
      (a : ℝ) * (q 1).toReal + (1 - a) * (r 1).toReal ≤
        (a : ℝ) * (p 1).toReal + (1 - a) * (r 1).toReal ↔ (q 1).toReal ≤ (p 1).toReal := by
    constructor <;> intro h <;> nlinarith
  rw [hmul_lt, hmul_eq, hmul_le]

/-- `lexRel` violates the continuity axiom (at `PMF.pure 2 ≻ PMF.pure 1 ≻ PMF.pure 0`). -/
theorem not_isContinuousOn_lexRel : ¬ IsContinuousOn (X₃ : Set (Fin 3)) lexRel := by
  intro hC
  let p2 : PMF (Fin 3) := PMF.pure 2
  let p1 : PMF (Fin 3) := PMF.pure 1
  let p0 : PMF (Fin 3) := PMF.pure 0
  have h21 : lexRel p2 p1 := by
    left
    simp only [p2, p1, PMF.pure_apply, Fin.reduceEq, ↓reduceIte, ENNReal.toReal_one,
      ENNReal.toReal_zero]
    norm_num
  have h10 : lexRel p1 p0 := by
    right
    simp only [p1, p0, PMF.pure_apply, Fin.reduceEq, ↓reduceIte, ENNReal.toReal_one,
      ENNReal.toReal_zero]
    norm_num
  obtain ⟨a, ha⟩ := hC (mem_lotteriesOn_univ p2) (mem_lotteriesOn_univ p1)
    (mem_lotteriesOn_univ p0) h21 h10
  have hm2 : (mix a p2 p0 2).toReal = (a : ℝ) := by
    simp only [p2, p0, mix_apply_toReal, PMF.pure_apply, Fin.reduceEq, ↓reduceIte,
      ENNReal.toReal_one, ENNReal.toReal_zero]
    ring
  have hm1 : (mix a p2 p0 1).toReal = 0 := by
    simp only [p2, p0, mix_apply_toReal, PMF.pure_apply, Fin.reduceEq, ↓reduceIte,
      ENNReal.toReal_zero]
    ring
  have hq_2 : (p1 2).toReal = 0 := by
    simp only [p1, PMF.pure_apply, Fin.reduceEq, ↓reduceIte, ENNReal.toReal_zero]
  have hq_1 : (p1 1).toReal = 1 := by
    simp only [p1, PMF.pure_apply_self, ENNReal.toReal_one]
  rcases eq_or_lt_of_le a.2.1 with ha0 | ha0
  · rcases ha.1 with hlt | ⟨_, hle⟩
    · rw [hm2, hq_2] at hlt
      linarith
    · rw [hm1, hq_1] at hle
      linarith
  · rcases ha.2 with hlt | ⟨heq, _⟩
    · rw [hm2, hq_2] at hlt
      linarith
    · rw [hm2, hq_2] at heq
      linarith

/-- `lexRel` also violates the Archimedean axiom. -/
theorem not_isArchimedeanOn_lexRel : ¬ IsArchimedeanOn (X₃ : Set (Fin 3)) lexRel := fun hA =>
  not_isContinuousOn_lexRel
    ((isContinuousOn_iff_isArchimedeanOn isRationalOn_lexRel isIndependentOn_lexRel).mpr hA)

/-- `lexRel` has no von Neumann–Morgenstern utility representation. -/
theorem not_exists_isVNMUtility_lexRel : ¬ ∃ u : Fin 3 → ℝ, IsVNMUtility X₃ lexRel u :=
  fun ⟨_, hu⟩ => not_isContinuousOn_lexRel hu.isContinuousOn

end CslibFrontierTests.VonNeumannMorgenstern
