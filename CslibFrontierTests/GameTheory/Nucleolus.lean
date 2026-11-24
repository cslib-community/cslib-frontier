/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.GameTheory.Cooperative.Nucleolus
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Nucleolus, prenucleolus, and Kohlberg's criterion

Checked non-vacuous examples exercising `CslibFrontier/GameTheory/Cooperative/Nucleolus.lean`
([Schmeidler1969], [Kohlberg1971]):

1. **Facility-location `example15_2`**: `CostSharingGame.nucleolus` equals `![4, 3 / 2, 5 / 2]` and
   lies in `InCore` (certified via `isPrenucleolus_iff_kohlberg` and
   `prenucleolus_eq_nucleolus_of_mem_imputations`), whereas `shapleyValue` lies outside the core.
2. **Symmetric 3-player majority game with empty core**: `¬ NonemptyCore`, yet
   `nucleolus = prenucleolus = fun _ => 1 / 3` by `AreSymmetric` and efficiency.
3. **Separation between `nucleolus` and `prenucleolus`**: 3-player game where player `0` has high
   standalone value `v({0}) = 10` (`v(univ) = 14`), forcing `nucleolus = ![10, 2, 2]` (tight
   individual rationality on player `0`, certified via `isNucleolus_iff_kohlberg` with `u 0 = 1`),
   whereas `prenucleolus = ![7, 7 / 2, 7 / 2]` strictly reduces the maximum excess from `6` to `3`.
4. **Dummy player and positive affine covariance**: explicit instances exercising
   `nucleolus_isDummyAgent`, `prenucleolus_isDummyAgent`, `nucleolus_mapAffine`, and
   `prenucleolus_mapAffine`.
-/

public section

namespace CslibFrontierTests.GameTheory.Nucleolus

open Cslib.GameTheory

/-! ### 1. Facility-location Example 15.2: nucleolus in core vs Shapley outside core -/

example :
    FacilityLocationInstance.example15_2.toCostSharingGame.nucleolus = ![4, 3 / 2, 5 / 2] ∧
    FacilityLocationInstance.example15_2.toCostSharingGame.prenucleolus = ![4, 3 / 2, 5 / 2] ∧
    FacilityLocationInstance.example15_2.toCostSharingGame.InCore ![4, 3 / 2, 5 / 2] := by
  set C := FacilityLocationInstance.example15_2.toCostSharingGame
  set G := C.toCooperativeGame
  let x : Fin 3 → ℝ := ![-4, -(3 / 2), -(5 / 2)]
  obtain ⟨hc0, hc1, hc2, hc01, hc12, hc02, hcuniv⟩ := FacilityLocationInstance.example15_2_cost
  have hc0' : C.cost {0} = 4 := hc0
  have hc1' : C.cost {1} = 3 := hc1
  have hc2' : C.cost {2} = 3 := hc2
  have hc01' : C.cost {0, 1} = 6 := hc01
  have hc12' : C.cost {1, 2} = 4 := hc12
  have hc02' : C.cost {0, 2} = 7 := hc02
  have hcuniv' : C.cost Finset.univ = 8 := hcuniv
  have hP : CooperativeGame.properNonemptyCoalitions (Fin 3) =
      ({({0} : Finset (Fin 3)), {1}, {2}, {0, 1}, {1, 2}, {0, 2}} :
        Finset (Finset (Fin 3))) := by decide
  have hx_pre : x ∈ G.preimputations := by
    simp only [CooperativeGame.preimputations, Set.mem_ofPred_eq, G,
      CostSharingGame.toCooperativeGame_val, Fin.sum_univ_three]
    rw [hcuniv']
    norm_num [x]
  have hx_imp : x ∈ G.imputations := by
    refine ⟨hx_pre, fun i => ?_⟩
    rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) i with rfl | rfl | rfl <;>
      simp only [G, CostSharingGame.toCooperativeGame_val]
    · rw [hc0']; norm_num [x]
    · rw [hc1']; norm_num [x]
    · rw [hc2']; norm_num [x]
  have he0 : G.excess ({0} : Finset (Fin 3)) x = 0 := by
    simp only [CooperativeGame.excess, G, CostSharingGame.toCooperativeGame_val,
      Finset.sum_singleton]
    rw [hc0']; norm_num [x]
  have he1 : G.excess ({1} : Finset (Fin 3)) x = -(3 / 2) := by
    simp only [CooperativeGame.excess, G, CostSharingGame.toCooperativeGame_val,
      Finset.sum_singleton]
    rw [hc1']; norm_num [x]
  have he2 : G.excess ({2} : Finset (Fin 3)) x = -(1 / 2) := by
    simp only [CooperativeGame.excess, G, CostSharingGame.toCooperativeGame_val,
      Finset.sum_singleton]
    rw [hc2']; norm_num [x]
  have he01 : G.excess ({0, 1} : Finset (Fin 3)) x = -(1 / 2) := by
    simp only [CooperativeGame.excess, G, CostSharingGame.toCooperativeGame_val,
      Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1)]
    rw [hc01']; norm_num [x]
  have he12 : G.excess ({1, 2} : Finset (Fin 3)) x = 0 := by
    simp only [CooperativeGame.excess, G, CostSharingGame.toCooperativeGame_val,
      Finset.sum_pair (by decide : (1 : Fin 3) ≠ 2)]
    rw [hc12']; norm_num [x]
  have he02 : G.excess ({0, 2} : Finset (Fin 3)) x = -(1 / 2) := by
    simp only [CooperativeGame.excess, G, CostSharingGame.toCooperativeGame_val,
      Finset.sum_pair (by decide : (0 : Fin 3) ≠ 2)]
    rw [hc02']; norm_num [x]
  have hf0 : (Finset.univ.filter fun S : Finset (Fin 3) => (0 : Fin 3) ∈ S) =
      ({({0} : Finset (Fin 3)), {0, 1}, {0, 2}, Finset.univ} :
        Finset (Finset (Fin 3))) := by decide
  have hf1 : (Finset.univ.filter fun S : Finset (Fin 3) => (1 : Fin 3) ∈ S) =
      ({({1} : Finset (Fin 3)), {0, 1}, {1, 2}, Finset.univ} :
        Finset (Finset (Fin 3))) := by decide
  have hf2 : (Finset.univ.filter fun S : Finset (Fin 3) => (2 : Fin 3) ∈ S) =
      ({({2} : Finset (Fin 3)), {1, 2}, {0, 2}, Finset.univ} :
        Finset (Finset (Fin 3))) := by decide
  have hkohl : G.IsPrenucleolus x := by
    refine (G.isPrenucleolus_iff_kohlberg hx_pre).2 fun t ⟨S₀, hS₀⟩ => ?_
    by_cases ht0 : 0 < t
    · exfalso
      have hS₀' := Finset.mem_filter.1 hS₀
      rw [hP] at hS₀'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hS₀'
      rcases hS₀'.1 with rfl | rfl | rfl | rfl | rfl | rfl
      · linarith [hS₀'.2, he0]
      · linarith [hS₀'.2, he1]
      · linarith [hS₀'.2, he2]
      · linarith [hS₀'.2, he01]
      · linarith [hS₀'.2, he12]
      · linarith [hS₀'.2, he02]
    · by_cases ht1 : -(1 / 2 : ℝ) < t
      · let w : Finset (Fin 3) → ℝ := fun S => if S = {0} ∨ S = {1, 2} then 1 else 0
        refine ⟨w, fun S hS => ?_, fun S hS => ?_, fun j => ?_⟩
        · have hS' := Finset.mem_filter.1 hS
          rw [hP] at hS'
          simp only [Finset.mem_insert, Finset.mem_singleton] at hS'
          rcases hS'.1 with rfl | rfl | rfl | rfl | rfl | rfl
          · simp [w]
          · exfalso; linarith [hS'.2, he1]
          · exfalso; linarith [hS'.2, he2]
          · exfalso; linarith [hS'.2, he01]
          · simp [w]
          · exfalso; linarith [hS'.2, he02]
        · have hmem : S = {0} ∨ S = {1, 2} → S ∈ G.upperLevel x t := by
            rintro (rfl | rfl)
            · exact Finset.mem_filter.2 ⟨by rw [hP]; decide, by linarith [he0]⟩
            · exact Finset.mem_filter.2 ⟨by rw [hP]; decide, by linarith [he12]⟩
          have hn : ¬ (S = {0} ∨ S = {1, 2}) := fun h => hS (hmem h)
          simp [w, hn]
        · rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) j with rfl | rfl | rfl <;>
            (first | rw [hf0] | rw [hf1] | rw [hf2]) <;>
            (repeat rw [Finset.sum_insert (by decide)]) <;>
            rw [Finset.sum_singleton] <;>
            dsimp only [w] <;>
            (repeat
              (first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])) <;>
            norm_num
      · by_cases ht2 : -(3 / 2 : ℝ) < t
        · let w : Finset (Fin 3) → ℝ := fun S =>
            if S = {0} ∨ S = {2} ∨ S = {0, 2} then 1 / 4
            else if S = {0, 1} ∨ S = {1, 2} then 1 / 2 else 0
          refine ⟨w, fun S hS => ?_, fun S hS => ?_, fun j => ?_⟩
          · have hS' := Finset.mem_filter.1 hS
            rw [hP] at hS'
            simp only [Finset.mem_insert, Finset.mem_singleton] at hS'
            rcases hS'.1 with rfl | rfl | rfl | rfl | rfl | rfl
            · norm_num [w]
            · exfalso; linarith [hS'.2, he1]
            · dsimp only [w]
              rw [ite_eq_left (by decide)]
              norm_num
            · dsimp only [w]
              repeat (first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
              norm_num
            · dsimp only [w]
              repeat (first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
              norm_num
            · dsimp only [w]
              rw [ite_eq_left (by decide)]
              norm_num
          · have ht_le : t ≤ -(1 / 2 : ℝ) := not_lt.1 ht1
            have hn1 : ¬ (S = {0} ∨ S = {2} ∨ S = {0, 2}) := by
              rintro (rfl | rfl | rfl)
              · exact hS (Finset.mem_filter.2 ⟨by rw [hP]; decide, by linarith [he0]⟩)
              · exact hS (Finset.mem_filter.2 ⟨by rw [hP]; decide, by linarith [he2]⟩)
              · exact hS (Finset.mem_filter.2 ⟨by rw [hP]; decide, by linarith [he02]⟩)
            have hn2 : ¬ (S = {0, 1} ∨ S = {1, 2}) := by
              rintro (rfl | rfl)
              · exact hS (Finset.mem_filter.2 ⟨by rw [hP]; decide, by linarith [he01]⟩)
              · exact hS (Finset.mem_filter.2 ⟨by rw [hP]; decide, by linarith [he12]⟩)
            simp [w, hn1, hn2]
          · rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) j with rfl | rfl | rfl <;>
              (first | rw [hf0] | rw [hf1] | rw [hf2]) <;>
              (repeat rw [Finset.sum_insert (by decide)]) <;>
              rw [Finset.sum_singleton] <;>
              dsimp only [w] <;>
              (repeat
              (first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])) <;>
              norm_num
        · let w : Finset (Fin 3) → ℝ := fun S =>
            if S ∈ CooperativeGame.properNonemptyCoalitions (Fin 3) then 1 / 3 else 0
          refine ⟨w, fun S hS => by simp [w, (Finset.mem_filter.1 hS).1],
            fun S hS => ?_, fun j => ?_⟩
          · have ht_le : t ≤ -(3 / 2 : ℝ) := not_lt.1 ht2
            have hn : S ∉ CooperativeGame.properNonemptyCoalitions (Fin 3) := by
              intro hSP
              rw [hP] at hSP
              apply hS
              refine Finset.mem_filter.2 ⟨by rw [hP]; exact hSP, ?_⟩
              simp only [Finset.mem_insert, Finset.mem_singleton] at hSP
              rcases hSP with rfl | rfl | rfl | rfl | rfl | rfl
              · linarith [he0]
              · linarith [he1]
              · linarith [he2]
              · linarith [he01]
              · linarith [he12]
              · linarith [he02]
            simp [w, hn]
          · rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) j with rfl | rfl | rfl <;>
              (first | rw [hf0] | rw [hf1] | rw [hf2]) <;>
              (repeat rw [Finset.sum_insert (by decide)]) <;>
              rw [Finset.sum_singleton] <;>
              dsimp only [w] <;>
              rw [hP] <;>
              (repeat
              (first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])) <;>
              norm_num
  have hpre_eq : G.prenucleolus = x := (G.isPrenucleolus_iff_eq_prenucleolus.1 hkohl).symm
  have hnuc_eq : G.nucleolus = x := by
    rw [← G.prenucleolus_eq_nucleolus_of_mem_imputations (hpre_eq ▸ hx_imp), hpre_eq]
  have hnegx : -x = ![4, 3 / 2, 5 / 2] := by
    ext i
    rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) i with rfl | rfl | rfl <;> norm_num [x]
  have hC_nuc : C.nucleolus = ![4, 3 / 2, 5 / 2] := by
    rw [CostSharingGame.nucleolus_eq, show C.toCooperativeGame = G from rfl, hnuc_eq, hnegx]
  have hC_pre : C.prenucleolus = ![4, 3 / 2, 5 / 2] := by
    rw [CostSharingGame.prenucleolus_eq, show C.toCooperativeGame = G from rfl, hpre_eq, hnegx]
  have hC_core : C.NonemptyCore := ⟨![4, 2, 2],
    FacilityLocationInstance.example15_2_inCore_four_two_two⟩
  refine ⟨hC_nuc, hC_pre, ?_⟩
  simpa only [hC_nuc] using C.nucleolus_inCore_of_nonemptyCore hC_core

/-! ### 2. Symmetric 3-player majority game with empty core -/

/-- Three-player simple majority cooperative game: `v(S) = 1` iff `|S| ≥ 2`. Its core is empty,
while symmetry and efficiency force `nucleolus = prenucleolus = (1 / 3, 1 / 3, 1 / 3)`. -/
def majorityGame : CooperativeGame (Fin 3) where
  val S := if 2 ≤ S.card then 1 else 0
  val_empty := by simp

example :
    ¬ majorityGame.NonemptyCore ∧
    majorityGame.nucleolus = (fun _ => 1 / 3) ∧
    majorityGame.prenucleolus = (fun _ => 1 / 3) := by
  have hnocore : ¬ majorityGame.NonemptyCore := by
    rintro ⟨y, hy⟩
    have heff : y 0 + y 1 + y 2 = 1 := by
      simpa [Fin.sum_univ_three, majorityGame] using hy.1
    have h01 : 1 ≤ y 0 + y 1 := by
      simpa [majorityGame, Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1)] using hy.2 {0, 1}
    have h12 : 1 ≤ y 1 + y 2 := by
      simpa [majorityGame, Finset.sum_pair (by decide : (1 : Fin 3) ≠ 2)] using hy.2 {1, 2}
    have h02 : 1 ≤ y 0 + y 2 := by
      simpa [majorityGame, Finset.sum_pair (by decide : (0 : Fin 3) ≠ 2)] using hy.2 {0, 2}
    linarith
  have hsym : ∀ i j : Fin 3, majorityGame.AreSymmetric i j := by
    intro i j S hi hj
    simp only [majorityGame, Finset.card_insert_of_notMem hi, Finset.card_insert_of_notMem hj]
  have hle : ∑ k : Fin 3, majorityGame.val {k} ≤ majorityGame.val Finset.univ := by
    simp [majorityGame]
  have hn_const : majorityGame.nucleolus = fun _ => 1 / 3 := by
    have h01 := CooperativeGame.nucleolus_eq_of_areSymmetric (hsym 0 1)
    have h12 := CooperativeGame.nucleolus_eq_of_areSymmetric (hsym 1 2)
    have heff : majorityGame.nucleolus 0 + majorityGame.nucleolus 1 +
        majorityGame.nucleolus 2 = 1 := by
      have hm := (majorityGame.nucleolus_mem_imputations hle).1
      change ∑ i : Fin 3, majorityGame.nucleolus i = majorityGame.val Finset.univ at hm
      simpa [Fin.sum_univ_three, majorityGame] using hm
    ext i
    rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) i with rfl | rfl | rfl <;> linarith
  have hp_const : majorityGame.prenucleolus = fun _ => 1 / 3 := by
    have h01 := CooperativeGame.prenucleolus_eq_of_areSymmetric (hsym 0 1)
    have h12 := CooperativeGame.prenucleolus_eq_of_areSymmetric (hsym 1 2)
    have heff : majorityGame.prenucleolus 0 + majorityGame.prenucleolus 1 +
        majorityGame.prenucleolus 2 = 1 := by
      have hm := majorityGame.prenucleolus_mem_preimputations
      change ∑ i : Fin 3, majorityGame.prenucleolus i = majorityGame.val Finset.univ at hm
      simpa [Fin.sum_univ_three, majorityGame] using hm
    ext i
    rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) i with rfl | rfl | rfl <;> linarith
  exact ⟨hnocore, hn_const, hp_const⟩

/-! ### 3. Separation between the nucleolus and the prenucleolus -/

/-- Three-player game with active individual rationality at player `0`:
`v(univ) = 14`, `v({1}) = v({2}) = 0`, and `v(S) = 10` for every other nonempty proper `S`.
Its nucleolus is `(10, 2, 2)` (with IR multiplier `u 0 = 1` at level `t = 6`), whereas its
prenucleolus is `(7, 7 / 2, 7 / 2)` (reducing maximum excess from `6` to `3`). -/
def irSepGame : CooperativeGame (Fin 3) where
  val S := if S = Finset.univ then 14 else if (0 : Fin 3) ∈ S ∨ 2 ≤ S.card then 10 else 0
  val_empty := by
    rw [ite_eq_right (by decide), ite_eq_right (by decide)]

example :
    irSepGame.nucleolus = ![10, 2, 2] ∧
    irSepGame.prenucleolus = ![7, 7 / 2, 7 / 2] ∧
    irSepGame.nucleolus ≠ irSepGame.prenucleolus := by
  have hP : CooperativeGame.properNonemptyCoalitions (Fin 3) =
      ({({0} : Finset (Fin 3)), {1}, {2}, {0, 1}, {1, 2}, {0, 2}} :
        Finset (Finset (Fin 3))) := by decide
  have hf0 : (Finset.univ.filter fun S : Finset (Fin 3) => (0 : Fin 3) ∈ S) =
      ({({0} : Finset (Fin 3)), {0, 1}, {0, 2}, Finset.univ} :
        Finset (Finset (Fin 3))) := by decide
  have hf1 : (Finset.univ.filter fun S : Finset (Fin 3) => (1 : Fin 3) ∈ S) =
      ({({1} : Finset (Fin 3)), {0, 1}, {1, 2}, Finset.univ} :
        Finset (Finset (Fin 3))) := by decide
  have hf2 : (Finset.univ.filter fun S : Finset (Fin 3) => (2 : Fin 3) ∈ S) =
      ({({2} : Finset (Fin 3)), {1, 2}, {0, 2}, Finset.univ} :
        Finset (Finset (Fin 3))) := by decide
  have hle : ∑ k : Fin 3, irSepGame.val {k} ≤ irSepGame.val Finset.univ := by
    simp [irSepGame]
    norm_num
  have hnuc : irSepGame.nucleolus = ![10, 2, 2] := by
    let x : Fin 3 → ℝ := ![10, 2, 2]
    have hx_imp : x ∈ irSepGame.imputations := by
      refine ⟨?_, fun i => ?_⟩
      · simp only [irSepGame, ↓reduceIte, Fin.sum_univ_three]
        norm_num [x]
      · rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) i with rfl | rfl | rfl <;>
          simp [irSepGame, x]
    have hx_nuc : irSepGame.IsNucleolus x := by
      refine (irSepGame.isNucleolus_iff_kohlberg hx_imp).2 fun t ⟨S₀, hS₀⟩ => ?_
      have he0 : irSepGame.excess ({0} : Finset (Fin 3)) x = 0 := by
        simp [CooperativeGame.excess, irSepGame, x]
      have he1 : irSepGame.excess ({1} : Finset (Fin 3)) x = -2 := by
        simp [CooperativeGame.excess, irSepGame, x]
      have he2 : irSepGame.excess ({2} : Finset (Fin 3)) x = -2 := by
        simp [CooperativeGame.excess, irSepGame, x]
      have he01 : irSepGame.excess ({0, 1} : Finset (Fin 3)) x = -2 := by
        simp only [CooperativeGame.excess, irSepGame,
          Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1)]
        norm_num [x, show ¬ (({0, 1} : Finset (Fin 3)) = Finset.univ) by decide]
      have he12 : irSepGame.excess ({1, 2} : Finset (Fin 3)) x = 6 := by
        simp only [CooperativeGame.excess, irSepGame,
          Finset.sum_pair (by decide : (1 : Fin 3) ≠ 2)]
        norm_num [x, show ¬ (({1, 2} : Finset (Fin 3)) = Finset.univ) by decide]
      have he02 : irSepGame.excess ({0, 2} : Finset (Fin 3)) x = -2 := by
        simp only [CooperativeGame.excess, irSepGame,
          Finset.sum_pair (by decide : (0 : Fin 3) ≠ 2)]
        norm_num [x, show ¬ (({0, 2} : Finset (Fin 3)) = Finset.univ) by decide]
      by_cases ht6 : 6 < t
      · exfalso
        have hS₀' := Finset.mem_filter.1 hS₀
        rw [hP] at hS₀'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hS₀'
        rcases hS₀'.1 with rfl | rfl | rfl | rfl | rfl | rfl
        · linarith [hS₀'.2, he0]
        · linarith [hS₀'.2, he1]
        · linarith [hS₀'.2, he2]
        · linarith [hS₀'.2, he01]
        · linarith [hS₀'.2, he12]
        · linarith [hS₀'.2, he02]
      · by_cases ht0 : 0 < t
        · let w : Finset (Fin 3) → ℝ := fun S => if S = {1, 2} then 1 else 0
          let u : Fin 3 → ℝ := ![1, 0, 0]
          refine ⟨w, u, fun S hS => ?_, fun S hS => ?_, fun j => by
              rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) j with rfl | rfl | rfl <;>
                norm_num [u],
            fun j hj => ?_, fun j => ?_⟩
          · have hS' := Finset.mem_filter.1 hS
            rw [hP] at hS'
            simp only [Finset.mem_insert, Finset.mem_singleton] at hS'
            rcases hS'.1 with rfl | rfl | rfl | rfl | rfl | rfl
            · exfalso; linarith [hS'.2, he0]
            · exfalso; linarith [hS'.2, he1]
            · exfalso; linarith [hS'.2, he2]
            · exfalso; linarith [hS'.2, he01]
            · simp [w]
            · exfalso; linarith [hS'.2, he02]
          · have hn : S ≠ {1, 2} := fun heq =>
              hS (Finset.mem_filter.2 ⟨heq ▸ by rw [hP]; decide, heq ▸ by linarith [he12]⟩)
            simp [w, hn]
          · rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) j with rfl | rfl | rfl
            · simp [irSepGame, x] at hj
            · simp [u]
            · simp [u]
          · rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) j with rfl | rfl | rfl <;>
              (first | rw [hf0] | rw [hf1] | rw [hf2]) <;>
              (repeat rw [Finset.sum_insert (by decide)]) <;>
              rw [Finset.sum_singleton] <;>
              dsimp only [u, w] <;>
              (repeat
              (first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])) <;>
              norm_num
        · by_cases ht2 : -2 < t
          · let w : Finset (Fin 3) → ℝ := fun S => if S = {0} ∨ S = {1, 2} then 1 else 0
            refine ⟨w, 0, fun S hS => ?_, fun S hS => ?_, fun _ => le_rfl, fun _ _ => rfl,
              fun j => ?_⟩
            · have hS' := Finset.mem_filter.1 hS
              rw [hP] at hS'
              simp only [Finset.mem_insert, Finset.mem_singleton] at hS'
              rcases hS'.1 with rfl | rfl | rfl | rfl | rfl | rfl
              · simp [w]
              · exfalso; linarith [hS'.2, he1]
              · exfalso; linarith [hS'.2, he2]
              · exfalso; linarith [hS'.2, he01]
              · simp [w]
              · exfalso; linarith [hS'.2, he02]
            · have hmem : S = {0} ∨ S = {1, 2} → S ∈ irSepGame.upperLevel x t := by
                rintro (rfl | rfl)
                · exact Finset.mem_filter.2 ⟨by rw [hP]; decide, by linarith [he0]⟩
                · exact Finset.mem_filter.2 ⟨by rw [hP]; decide, by linarith [he12]⟩
              have hn : ¬ (S = {0} ∨ S = {1, 2}) := fun h => hS (hmem h)
              simp [w, hn]
            · simp only [Pi.zero_apply, zero_add]
              rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) j with rfl | rfl | rfl <;>
                (first | rw [hf0] | rw [hf1] | rw [hf2]) <;>
                (repeat rw [Finset.sum_insert (by decide)]) <;>
                rw [Finset.sum_singleton] <;>
                dsimp only [w] <;>
                (repeat
              (first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])) <;>
                norm_num
          · let w : Finset (Fin 3) → ℝ := fun S =>
              if S ∈ CooperativeGame.properNonemptyCoalitions (Fin 3) then 1 / 3 else 0
            refine ⟨w, 0, fun S hS => by simp [w, (Finset.mem_filter.1 hS).1],
              fun S hS => ?_, fun _ => le_rfl, fun _ _ => rfl, fun j => ?_⟩
            · have ht_le : t ≤ -2 := not_lt.1 ht2
              have hn : S ∉ CooperativeGame.properNonemptyCoalitions (Fin 3) := by
                intro hSP
                rw [hP] at hSP
                apply hS
                refine Finset.mem_filter.2 ⟨by rw [hP]; exact hSP, ?_⟩
                simp only [Finset.mem_insert, Finset.mem_singleton] at hSP
                rcases hSP with rfl | rfl | rfl | rfl | rfl | rfl
                · linarith [he0]
                · linarith [he1]
                · linarith [he2]
                · linarith [he01]
                · linarith [he12]
                · linarith [he02]
              simp [w, hn]
            · simp only [Pi.zero_apply, zero_add]
              rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) j with rfl | rfl | rfl <;>
                (first | rw [hf0] | rw [hf1] | rw [hf2]) <;>
                (repeat rw [Finset.sum_insert (by decide)]) <;>
                rw [Finset.sum_singleton] <;>
                dsimp only [w] <;>
                rw [hP] <;>
                (repeat
              (first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])) <;>
                norm_num
    exact ((irSepGame.isNucleolus_iff_eq_nucleolus hle).1 hx_nuc).symm
  have hprenuc : irSepGame.prenucleolus = ![7, 7 / 2, 7 / 2] := by
    let x : Fin 3 → ℝ := ![7, 7 / 2, 7 / 2]
    have hx_pre : x ∈ irSepGame.preimputations := by
      simp only [CooperativeGame.preimputations, Set.mem_ofPred_eq, irSepGame, ↓reduceIte,
        Fin.sum_univ_three]
      norm_num [x]
    have hx_opt : irSepGame.IsPrenucleolus x := by
      refine (irSepGame.isPrenucleolus_iff_kohlberg hx_pre).2 fun t ⟨S₀, hS₀⟩ => ?_
      have he0 : irSepGame.excess ({0} : Finset (Fin 3)) x = 3 := by
        simp [CooperativeGame.excess, irSepGame, x]; norm_num
      have he1 : irSepGame.excess ({1} : Finset (Fin 3)) x = -(7 / 2) := by
        simp [CooperativeGame.excess, irSepGame, x]
      have he2 : irSepGame.excess ({2} : Finset (Fin 3)) x = -(7 / 2) := by
        simp [CooperativeGame.excess, irSepGame, x]
      have he01 : irSepGame.excess ({0, 1} : Finset (Fin 3)) x = -(1 / 2) := by
        simp only [CooperativeGame.excess, irSepGame,
          Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1)]
        norm_num [x, show ¬ (({0, 1} : Finset (Fin 3)) = Finset.univ) by decide]
      have he12 : irSepGame.excess ({1, 2} : Finset (Fin 3)) x = 3 := by
        simp only [CooperativeGame.excess, irSepGame,
          Finset.sum_pair (by decide : (1 : Fin 3) ≠ 2)]
        norm_num [x, show ¬ (({1, 2} : Finset (Fin 3)) = Finset.univ) by decide]
      have he02 : irSepGame.excess ({0, 2} : Finset (Fin 3)) x = -(1 / 2) := by
        simp only [CooperativeGame.excess, irSepGame,
          Finset.sum_pair (by decide : (0 : Fin 3) ≠ 2)]
        norm_num [x, show ¬ (({0, 2} : Finset (Fin 3)) = Finset.univ) by decide]
      by_cases ht3 : 3 < t
      · exfalso
        have hS₀' := Finset.mem_filter.1 hS₀
        rw [hP] at hS₀'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hS₀'
        rcases hS₀'.1 with rfl | rfl | rfl | rfl | rfl | rfl
        · linarith [hS₀'.2, he0]
        · linarith [hS₀'.2, he1]
        · linarith [hS₀'.2, he2]
        · linarith [hS₀'.2, he01]
        · linarith [hS₀'.2, he12]
        · linarith [hS₀'.2, he02]
      · by_cases ht_half : -(1 / 2 : ℝ) < t
        · let w : Finset (Fin 3) → ℝ := fun S => if S = {0} ∨ S = {1, 2} then 1 else 0
          refine ⟨w, fun S hS => ?_, fun S hS => ?_, fun j => ?_⟩
          · have hS' := Finset.mem_filter.1 hS
            rw [hP] at hS'
            simp only [Finset.mem_insert, Finset.mem_singleton] at hS'
            rcases hS'.1 with rfl | rfl | rfl | rfl | rfl | rfl
            · simp [w]
            · exfalso; linarith [hS'.2, he1]
            · exfalso; linarith [hS'.2, he2]
            · exfalso; linarith [hS'.2, he01]
            · simp [w]
            · exfalso; linarith [hS'.2, he02]
          · have hmem : S = {0} ∨ S = {1, 2} → S ∈ irSepGame.upperLevel x t := by
              rintro (rfl | rfl)
              · exact Finset.mem_filter.2 ⟨by rw [hP]; decide, by linarith [he0]⟩
              · exact Finset.mem_filter.2 ⟨by rw [hP]; decide, by linarith [he12]⟩
            have hn : ¬ (S = {0} ∨ S = {1, 2}) := fun h => hS (hmem h)
            simp [w, hn]
          · rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) j with rfl | rfl | rfl <;>
              (first | rw [hf0] | rw [hf1] | rw [hf2]) <;>
              (repeat rw [Finset.sum_insert (by decide)]) <;>
              rw [Finset.sum_singleton] <;>
              dsimp only [w] <;>
              (repeat
              (first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])) <;>
              norm_num
        · by_cases ht72 : -(7 / 2 : ℝ) < t
          · let w : Finset (Fin 3) → ℝ := fun S =>
              if S = {0} then 1 / 2
              else if S = {0, 1} ∨ S = {0, 2} then 1 / 4
              else if S = {1, 2} then 3 / 4 else 0
            refine ⟨w, fun S hS => ?_, fun S hS => ?_, fun j => ?_⟩
            · have hS' := Finset.mem_filter.1 hS
              rw [hP] at hS'
              simp only [Finset.mem_insert, Finset.mem_singleton] at hS'
              rcases hS'.1 with rfl | rfl | rfl | rfl | rfl | rfl
              · norm_num [w]
              · exfalso; linarith [hS'.2, he1]
              · exfalso; linarith [hS'.2, he2]
              · dsimp only [w]
                repeat (first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
                norm_num
              · dsimp only [w]
                repeat (first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
                norm_num
              · dsimp only [w]
                repeat (first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
                norm_num
            · have ht_le : t ≤ -(1 / 2 : ℝ) := not_lt.1 ht_half
              have h0 : S ≠ {0} := fun heq =>
                hS (Finset.mem_filter.2 ⟨heq ▸ by rw [hP]; decide, heq ▸ by linarith [he0]⟩)
              have h012 : ¬ (S = {0, 1} ∨ S = {0, 2}) := by
                rintro (rfl | rfl)
                · exact hS (Finset.mem_filter.2 ⟨by rw [hP]; decide, by linarith [he01]⟩)
                · exact hS (Finset.mem_filter.2 ⟨by rw [hP]; decide, by linarith [he02]⟩)
              have h12 : S ≠ {1, 2} := fun heq =>
                hS (Finset.mem_filter.2 ⟨heq ▸ by rw [hP]; decide, heq ▸ by linarith [he12]⟩)
              simp [w, h0, h012, h12]
            · rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) j with rfl | rfl | rfl <;>
                (first | rw [hf0] | rw [hf1] | rw [hf2]) <;>
                (repeat rw [Finset.sum_insert (by decide)]) <;>
                rw [Finset.sum_singleton] <;>
                dsimp only [w] <;>
                (repeat
              (first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])) <;>
                norm_num
          · let w : Finset (Fin 3) → ℝ := fun S =>
              if S ∈ CooperativeGame.properNonemptyCoalitions (Fin 3) then 1 / 3 else 0
            refine ⟨w, fun S hS => by simp [w, (Finset.mem_filter.1 hS).1],
              fun S hS => ?_, fun j => ?_⟩
            · have ht_le : t ≤ -(7 / 2 : ℝ) := not_lt.1 ht72
              have hn : S ∉ CooperativeGame.properNonemptyCoalitions (Fin 3) := by
                intro hSP
                rw [hP] at hSP
                apply hS
                refine Finset.mem_filter.2 ⟨by rw [hP]; exact hSP, ?_⟩
                simp only [Finset.mem_insert, Finset.mem_singleton] at hSP
                rcases hSP with rfl | rfl | rfl | rfl | rfl | rfl
                · linarith [he0]
                · linarith [he1]
                · linarith [he2]
                · linarith [he01]
                · linarith [he12]
                · linarith [he02]
              simp [w, hn]
            · rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) j with rfl | rfl | rfl <;>
                (first | rw [hf0] | rw [hf1] | rw [hf2]) <;>
                (repeat rw [Finset.sum_insert (by decide)]) <;>
                rw [Finset.sum_singleton] <;>
                dsimp only [w] <;>
                rw [hP] <;>
                (repeat
              (first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])) <;>
                norm_num
    exact (irSepGame.isPrenucleolus_iff_eq_prenucleolus.1 hx_opt).symm
  have hsep : irSepGame.nucleolus ≠ irSepGame.prenucleolus := by
    rw [hnuc, hprenuc]
    intro heq
    have h0 := congrFun heq 0
    norm_num at h0
  exact ⟨hnuc, hprenuc, hsep⟩

/-! ### 4. Dummy agent and positive affine covariance checks -/

/-- Three-player cooperative game where player `2` is a dummy agent and `{0, 1}` shares surplus `4`:
`v({0}) = 1, v({1}) = 1, v({0, 1}) = 4` (with `2` contributing `0` to every coalition). -/
def dummyGame : CooperativeGame (Fin 3) where
  val S :=
    let S' := S.erase 2
    if S' = {0, 1} then 4 else if S' = {0} ∨ S' = {1} then 1 else 0
  val_empty := by
    dsimp only
    rw [Finset.erase_empty]
    split_ifs with h1 h2
    · exact absurd h1 (by decide)
    · rcases h2 with h2 | h2 <;> exact absurd h2 (by decide)
    · rfl

example :
    dummyGame.IsDummyAgent 2 ∧
    dummyGame.nucleolus = ![2, 2, 0] ∧
    dummyGame.prenucleolus = ![2, 2, 0] ∧
    (dummyGame.mapAffine 2 ![1, 3, -2]).nucleolus = ![5, 7, -2] := by
  have hd2 : dummyGame.IsDummyAgent 2 := by
    intro S h2S
    simp only [dummyGame, Finset.erase_insert h2S, Finset.erase_eq_self.2 h2S]
  have hsym01 : dummyGame.AreSymmetric 0 1 := by
    intro S h0S h1S
    simp only [dummyGame]
    have he0 : (insert (0 : Fin 3) S).erase 2 = insert 0 (S.erase 2) := by
      ext a
      simp only [Finset.mem_erase, Finset.mem_insert]
      refine ⟨fun ⟨hne2, ha⟩ => ?_, ?_⟩
      · rcases ha with rfl | haS
        · left; rfl
        · right; exact ⟨hne2, haS⟩
      · rintro (rfl | ⟨hne2, haS⟩)
        · exact ⟨by decide, Or.inl rfl⟩
        · exact ⟨hne2, Or.inr haS⟩
    have he1 : (insert (1 : Fin 3) S).erase 2 = insert 1 (S.erase 2) := by
      ext a
      simp only [Finset.mem_erase, Finset.mem_insert]
      refine ⟨fun ⟨hne2, ha⟩ => ?_, ?_⟩
      · rcases ha with rfl | haS
        · left; rfl
        · right; exact ⟨hne2, haS⟩
      · rintro (rfl | ⟨hne2, haS⟩)
        · exact ⟨by decide, Or.inl rfl⟩
        · exact ⟨hne2, Or.inr haS⟩
    rw [he0, he1]
    by_cases h01 : 0 ∈ S.erase 2 ∨ 1 ∈ S.erase 2
    · exfalso
      rcases h01 with h | h
      · exact h0S (Finset.mem_of_mem_erase h)
      · exact h1S (Finset.mem_of_mem_erase h)
    · have hS_eq : S.erase 2 = ∅ := by
        ext a
        fin_cases a <;> simp_all
      rw [hS_eq]
      simp [show ({0} : Finset (Fin 3)) ≠ {0, 1} by decide,
        show ({1} : Finset (Fin 3)) ≠ {0, 1} by decide,
        show ({0} : Finset (Fin 3)) ≠ {1} by decide,
        show ({1} : Finset (Fin 3)) ≠ {0} by decide]
  have hle : ∑ k : Fin 3, dummyGame.val {k} ≤ dummyGame.val Finset.univ := by
    simp only [dummyGame, Fin.sum_univ_three]
    have h_univ : (Finset.univ : Finset (Fin 3)).erase 2 = {0, 1} := by decide
    have h_s0 : ({0} : Finset (Fin 3)).erase 2 = {0} := by decide
    have h_s1 : ({1} : Finset (Fin 3)).erase 2 = {1} := by decide
    have h_s2 : ({2} : Finset (Fin 3)).erase 2 = ∅ := by decide
    rw [h_univ, h_s0, h_s1, h_s2]
    norm_num [show ({0} : Finset (Fin 3)) ≠ {0, 1} by decide,
      show ({1} : Finset (Fin 3)) ≠ {0, 1} by decide,
      show (∅ : Finset (Fin 3)) ≠ {0, 1} by decide,
      show (∅ : Finset (Fin 3)) ≠ {0} by decide,
      show (∅ : Finset (Fin 3)) ≠ {1} by decide]
  have hnuc2 : dummyGame.nucleolus 2 = 0 := CooperativeGame.nucleolus_isDummyAgent hle hd2
  have hp2 : dummyGame.prenucleolus 2 = 0 := CooperativeGame.prenucleolus_isDummyAgent hd2
  have hn01 : dummyGame.nucleolus 0 = dummyGame.nucleolus 1 :=
    CooperativeGame.nucleolus_eq_of_areSymmetric hsym01
  have hp01 : dummyGame.prenucleolus 0 = dummyGame.prenucleolus 1 :=
    CooperativeGame.prenucleolus_eq_of_areSymmetric hsym01
  have h_univ : dummyGame.val Finset.univ = 4 := by
    simp [dummyGame, show (Finset.univ : Finset (Fin 3)).erase 2 = {0, 1} by decide]
  have hn_eq : dummyGame.nucleolus = ![2, 2, 0] := by
    have heff : dummyGame.nucleolus 0 + dummyGame.nucleolus 1 + dummyGame.nucleolus 2 = 4 := by
      have hm := (dummyGame.nucleolus_mem_imputations hle).1
      change ∑ i : Fin 3, dummyGame.nucleolus i = dummyGame.val Finset.univ at hm
      rw [Fin.sum_univ_three, h_univ] at hm
      exact hm
    ext i
    rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) i with rfl | rfl | rfl
    · change dummyGame.nucleolus 0 = 2; linarith
    · change dummyGame.nucleolus 1 = 2; linarith
    · change dummyGame.nucleolus 2 = 0; exact hnuc2
  have hp_eq : dummyGame.prenucleolus = ![2, 2, 0] := by
    have heff : dummyGame.prenucleolus 0 + dummyGame.prenucleolus 1 +
        dummyGame.prenucleolus 2 = 4 := by
      have hm := dummyGame.prenucleolus_mem_preimputations
      change ∑ i : Fin 3, dummyGame.prenucleolus i = dummyGame.val Finset.univ at hm
      rw [Fin.sum_univ_three, h_univ] at hm
      exact hm
    ext i
    rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) i with rfl | rfl | rfl
    · change dummyGame.prenucleolus 0 = 2; linarith
    · change dummyGame.prenucleolus 1 = 2; linarith
    · change dummyGame.prenucleolus 2 = 0; exact hp2
  have haff : (dummyGame.mapAffine 2 ![1, 3, -2]).nucleolus = ![5, 7, -2] := by
    rw [dummyGame.nucleolus_mapAffine (by norm_num) ![1, 3, -2] hle, hn_eq]
    ext i
    rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) i with rfl | rfl | rfl <;> norm_num
  exact ⟨hd2, hn_eq, hp_eq, haff⟩

end CslibFrontierTests.GameTheory.Nucleolus
