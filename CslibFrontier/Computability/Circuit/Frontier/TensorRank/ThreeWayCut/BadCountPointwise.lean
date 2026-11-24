/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
-- `import all`: reads private planar sector/ray-crossing helpers from `PlanarGeometry`,
-- `BlockSample` / `blockMeasure` from `SampleSpace`, and `edgeVec2` / `blockColor` / `cutAnyEvent`
-- from `QuotientColoring`.
import all CslibFrontier.Computability.Circuit.Frontier.TensorRank.ThreeWayCut.PlanarGeometry
import all CslibFrontier.Computability.Circuit.Frontier.TensorRank.ThreeWayCut.SampleSpace
import all CslibFrontier.Computability.Circuit.Frontier.TensorRank.ThreeWayCut.QuotientColoring
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.EdgeScores
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith

/-!
# Pointwise degree-`3` half-edge mismatch combinatorics

Defines `badCount` and proves its integrability (`integrable_badCount`), the pointwise degree-`3`
ray-crossing + origin-in-triangle inequality `four_mul_badCount_le`, and the bichromatic-edge to
half-edge mismatch bound `sum_cutAny_le_sum_badCount`.
-/

-- This proof-only companion is intentionally private; sibling ThreeWayCut modules use import all.
set_option linter.privateModule false

open MeasureTheory ProbabilityTheory Real Set

namespace Cslib.Circuits.Frontier.TensorRank

open Cslib.Circuits.Frontier.Multigraph

attribute [local instance]
  instIsProbabilityMeasure_gauss2
  instIsProbabilityMeasure_gaussTie
  instIsProbabilityMeasure_blockMeasure

section BadCountPointwise

variable {W F : Type*} [Fintype W] [Finite F]

open Classical in
/-- Number of incident edges at `B` whose `2`D vector does *not* lie in `B`'s chosen open sector. -/
private noncomputable def badCount (Q : Multigraph W F) (q : ℝ) (R : ℕ)
    (ω : W → BlockSample) (B : W) : ℕ :=
  ((@Set.toFinset F (Q.incidenceSet B) (Fintype.ofFinite _)).filter fun e =>
    ¬inOpenSector (blockColor Q q R ω B) (edgeVec2 Q q R ω e)).card

open Classical in
private theorem integrable_badCount {Q : Multigraph W F} (hdeg : Q.MaxDegreeLE 3)
    (q : ℝ) (R : ℕ) (B : W) :
    Integrable (fun ω => (badCount Q q R ω B : ℝ))
      (Measure.pi fun _ : W => blockMeasure) := by
  have := Fintype.ofFinite F
  have hfn : (fun ω : W → BlockSample => (badCount Q q R ω B : ℝ)) =
      fun ω => ∑ e ∈ (Q.incidenceSet B).toFinset,
        if ¬inOpenSector (blockColor Q q R ω B) (edgeVec2 Q q R ω e) then (1 : ℝ) else 0 := by
    funext ω
    unfold badCount
    rw [toFinset_eq_of_fintype (Q.incidenceSet B) _]
    rw [Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl fun e _ => by split_ifs <;> simp
  have hm_bad : Measurable (fun ω : W → BlockSample => (badCount Q q R ω B : ℝ)) := by
    rw [hfn]
    refine Finset.measurable_sum _ fun e _ => ?_
    have hm_in : MeasurableSet
        {ω : W → BlockSample | inOpenSector (blockColor Q q R ω B) (edgeVec2 Q q R ω e)} := by
      have hsplit : {ω : W → BlockSample |
          inOpenSector (blockColor Q q R ω B) (edgeVec2 Q q R ω e)} =
          ⋃ c : Fin 3, {ω | blockColor Q q R ω B = c} ∩
            {ω | inOpenSector c (edgeVec2 Q q R ω e)} := by
        ext ω
        simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
        exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨_, hc, h⟩ => hc ▸ h⟩
      rw [hsplit]
      refine MeasurableSet.iUnion fun c => (measurableSet_blockColor_eq Q q R B c).inter ?_
      exact measurableSet_inOpenSector_edgeVec2 Q q R e c
    exact Measurable.ite hm_in.compl measurable_const measurable_const
  refine Integrable.of_bound hm_bad.aestronglyMeasurable 3
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have hle : badCount Q q R ω B ≤ 3 := by
    unfold badCount
    rw [toFinset_eq_of_fintype (Q.incidenceSet B) _]
    exact (Finset.card_filter_le _ _).trans (by rw [← Set.ncard_eq_toFinset_card']; exact hdeg B)
  exact_mod_cast hle

open Classical in
/-- **Pointwise degree-`3` mismatch inequality.** Suppose `s = {e₀, e₁, e₂}` has size `3`, equals
`Q.incidenceSet B`, `(ω B).2` is injective, every `e ∈ s` avoids the three sector boundary lines,
and edges in distinct open sectors are non-collinear (`det2 ≠ 0`). Then `4 * badCount Q q R ω B` is
at most the sum of `rayCross` indicators over `s.offDiag × Fin 3` plus `2` times the
origin-in-triangle indicator `(0, 0) ∈ conv(z_{e₀}, z_{e₁}, z_{e₂})`. -/
private theorem four_mul_badCount_le [Fintype F] {Q : Multigraph W F} {q : ℝ} {R : ℕ}
    {ω : W → BlockSample} {B : W} {e₀ e₁ e₂ : F}
    (h01 : e₀ ≠ e₁) (h12 : e₁ ≠ e₂) (h02 : e₀ ≠ e₂)
    (hinc : ({e₀, e₁, e₂} : Finset F) = (Q.incidenceSet B).toFinset)
    (hinj : Function.Injective (ω B).2)
    (hray : ∀ e ∈ ({e₀, e₁, e₂} : Finset F), ∀ c : Fin 3,
      dot2 (normVec c) (edgeVec2 Q q R ω e) ≠ 0)
    (hdet : ∀ a ∈ ({e₀, e₁, e₂} : Finset F), ∀ b ∈ ({e₀, e₁, e₂} : Finset F),
      ∀ c₁ c₂ : Fin 3, inOpenSector c₁ (edgeVec2 Q q R ω a) →
        inOpenSector c₂ (edgeVec2 Q q R ω b) → c₁ ≠ c₂ →
        det2 (edgeVec2 Q q R ω a) (edgeVec2 Q q R ω b) ≠ 0) :
    4 * badCount Q q R ω B ≤
      (∑ p ∈ ({e₀, e₁, e₂} : Finset F).offDiag, ∑ c : Fin 3,
        if rayCross c (edgeVec2 Q q R ω p.1) (edgeVec2 Q q R ω p.2) then 1 else 0) +
      2 * (if ∃ w₀ w₁ w₂ : ℝ, 0 ≤ w₀ ∧ 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ w₀ + w₁ + w₂ = 1 ∧
        w₀ * (edgeVec2 Q q R ω e₀).1 + w₁ * (edgeVec2 Q q R ω e₁).1 +
          w₂ * (edgeVec2 Q q R ω e₂).1 = 0 ∧
        w₀ * (edgeVec2 Q q R ω e₀).2 + w₁ * (edgeVec2 Q q R ω e₁).2 +
          w₂ * (edgeVec2 Q q R ω e₂).2 = 0 then 1 else 0) := by
  set s : Finset F := {e₀, e₁, e₂}
  let fn (p : F × F) : ℕ :=
    ∑ c : Fin 3, if rayCross c (edgeVec2 Q q R ω p.1) (edgeVec2 Q q R ω p.2) then 1 else 0
  have fn_swap (x y : F) : fn (x, y) = fn (y, x) := by
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : rayCross c (edgeVec2 Q q R ω x) (edgeVec2 Q q R ω y)
    · have h' := (rayCross_comm c _ _).mp h; simp only [h, h', ↓reduceIte]
    · have h' := mt (rayCross_comm c _ _).mpr h; simp only [h, h', ↓reduceIte]
  have two_mul_sum_le (U : Finset (F × F)) (hU : U ⊆ s.offDiag)
      (hasym : ∀ p ∈ U, (p.2, p.1) ∉ U) :
      2 * ∑ p ∈ U, fn p ≤ ∑ p ∈ s.offDiag, fn p := by
    let sw : F × F ↪ F × F := ⟨Prod.swap, Prod.swap_injective⟩
    have hmap_sub : U.map sw ⊆ s.offDiag := by
      intro q_p hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hq
      obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.mp (hU hp)
      exact Finset.mem_offDiag.mpr ⟨h2, h1, hne.symm⟩
    have hdisj : Disjoint U (U.map sw) := by
      refine Finset.disjoint_right.mpr fun q_p hq hqU => ?_
      obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hq
      exact hasym p hp hqU
    have hmap_eq : ∑ p ∈ U.map sw, fn p = ∑ p ∈ U, fn p := by
      rw [Finset.sum_map]
      exact Finset.sum_congr rfl fun p _ => fn_swap p.2 p.1
    calc 2 * ∑ p ∈ U, fn p = ∑ p ∈ U, fn p + ∑ p ∈ U.map sw, fn p := by rw [hmap_eq]; ring
      _ = ∑ p ∈ U ∪ U.map sw, fn p := (Finset.sum_union hdisj).symm
      _ ≤ ∑ p ∈ s.offDiag, fn p := Finset.sum_le_sum_of_subset (Finset.union_subset hU hmap_sub)
  have hs_card : s.card = 3 := by
    dsimp [s]
    rw [Finset.card_insert_of_notMem (by simp [h01, h02]), Finset.card_pair h12]
  have he₀ : e₀ ∈ s := by simp [s]
  have he₁ : e₁ ∈ s := by simp [s]
  have he₂ : e₂ ∈ s := by simp [s]
  obtain ⟨s₀, hs₀⟩ := exists_inOpenSector_of_ne_zero (hray e₀ he₀)
  obtain ⟨s₁, hs₁⟩ := exists_inOpenSector_of_ne_zero (hray e₁ he₁)
  obtain ⟨s₂, hs₂⟩ := exists_inOpenSector_of_ne_zero (hray e₂ he₂)
  have hsec_eq (c : Fin 3) :
      secCount Q q R ω B c = (s.filter fun e => inOpenSector c (edgeVec2 Q q R ω e)).card := by
    unfold secCount
    rw [toFinset_eq_of_fintype (Q.incidenceSet B) _, ← hinc]
  have hbad_eq : badCount Q q R ω B =
      (s.filter fun e => ¬inOpenSector (blockColor Q q R ω B) (edgeVec2 Q q R ω e)).card := by
    unfold badCount
    rw [toFinset_eq_of_fintype (Q.incidenceSet B) _, ← hinc]
  have hbad_compl : badCount Q q R ω B + secCount Q q R ω B (blockColor Q q R ω B) = 3 := by
    rw [hbad_eq, hsec_eq, add_comm, Finset.card_filter_add_card_filter_not, hs_card]
  have case_two_one {a₁ a₂ b : F} (ha₁ : a₁ ∈ s) (ha₂ : a₂ ∈ s) (hb : b ∈ s)
      (ha12 : a₁ ≠ a₂) (ha1b : a₁ ≠ b) (ha2b : a₂ ≠ b)
      {c₀ c₁ : Fin 3} (hc01 : c₀ ≠ c₁)
      (h_a₁ : inOpenSector c₀ (edgeVec2 Q q R ω a₁))
      (h_a₂ : inOpenSector c₀ (edgeVec2 Q q R ω a₂))
      (h_b : inOpenSector c₁ (edgeVec2 Q q R ω b)) :
      4 * badCount Q q R ω B ≤ ∑ p ∈ s.offDiag, fn p := by
    have hs_perm : s = {a₁, a₂, b} := by
      refine (Finset.eq_of_subset_of_card_le (s := {a₁, a₂, b}) (t := s) ?_ ?_).symm
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      · rw [hs_card, Finset.card_insert_of_notMem (by simp [ha12, ha1b]),
          Finset.card_pair ha2b]
    have hcnt_c₀ : secCount Q q R ω B c₀ = 2 := by
      rw [hsec_eq, hs_perm]
      have hnb : ¬inOpenSector c₀ (edgeVec2 Q q R ω b) := fun h => hc01 (inOpenSector_unique h h_b)
      simp only [Finset.filter_insert, h_a₁, h_a₂, Finset.filter_singleton, hnb, ↓reduceIte]
      exact Finset.card_pair ha12
    have hcnt_lt : ∀ c' : Fin 3, c' ≠ c₀ → secCount Q q R ω B c' < 2 := fun c' hc' => by
      rw [hsec_eq, hs_perm]
      have hn1 : ¬inOpenSector c' (edgeVec2 Q q R ω a₁) :=
        fun h => hc' (inOpenSector_unique h h_a₁)
      have hn2 : ¬inOpenSector c' (edgeVec2 Q q R ω a₂) :=
        fun h => hc' (inOpenSector_unique h h_a₂)
      simp only [Finset.filter_insert, hn1, hn2, ↓reduceIte]
      exact (Finset.card_filter_le _ _).trans_lt (by simp)
    have hcol : blockColor Q q R ω B = c₀ :=
      blockColor_of_strict_majority hinj fun c' hc' => by rw [hcnt_c₀]; exact hcnt_lt c' hc'
    have hbad1 : badCount Q q R ω B = 1 := by
      rw [hcol, hcnt_c₀] at hbad_compl; omega
    rw [hbad1]
    have hadj : c₁ = c₀ + 1 ∨ c₀ = c₁ + 1 := by
      fin_cases c₀ <;> fin_cases c₁ <;> (try exact absurd rfl hc01) <;> decide
    rcases hadj with rfl | hrev
    · have hp1 : (a₁, b) ∈ s.offDiag := Finset.mem_offDiag.mpr ⟨ha₁, hb, ha1b⟩
      have hp2 : (a₂, b) ∈ s.offDiag := Finset.mem_offDiag.mpr ⟨ha₂, hb, ha2b⟩
      have hp_ne : (a₁, b) ≠ (a₂, b) := fun h => ha12 (Prod.mk.inj h).1
      have hr1 := (one_or_two_le_sum_rayCross c₀ h_a₁ h_b
        (hdet a₁ ha₁ b hb c₀ (c₀ + 1) h_a₁ h_b (by fin_cases c₀ <;> decide))).1
      have hr2 := (one_or_two_le_sum_rayCross c₀ h_a₂ h_b
        (hdet a₂ ha₂ b hb c₀ (c₀ + 1) h_a₂ h_b (by fin_cases c₀ <;> decide))).1
      have hsub : ({(a₁, b), (a₂, b)} : Finset (F × F)) ⊆ s.offDiag := by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl <;> assumption
      have hasym : ∀ p ∈ ({(a₁, b), (a₂, b)} : Finset (F × F)),
          (p.2, p.1) ∉ ({(a₁, b), (a₂, b)} : Finset (F × F)) := by
        rintro p hp hsw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp hsw
        rcases hp with rfl | rfl <;> rcases hsw with h | h
        · exact ha1b (Prod.mk.inj h).1.symm
        · exact ha2b (Prod.mk.inj h).1.symm
        · exact ha1b (Prod.mk.inj h).1.symm
        · exact ha2b (Prod.mk.inj h).1.symm
      have hU := two_mul_sum_le _ hsub hasym
      rw [Finset.sum_pair hp_ne] at hU
      change 1 ≤ fn (a₁, b) at hr1
      change 1 ≤ fn (a₂, b) at hr2
      omega
    · subst hrev
      have hp1 : (b, a₁) ∈ s.offDiag := Finset.mem_offDiag.mpr ⟨hb, ha₁, ha1b.symm⟩
      have hp2 : (b, a₂) ∈ s.offDiag := Finset.mem_offDiag.mpr ⟨hb, ha₂, ha2b.symm⟩
      have hp_ne : (b, a₁) ≠ (b, a₂) := fun h => ha12 (Prod.mk.inj h).2
      have hr1 := (one_or_two_le_sum_rayCross c₁ h_b h_a₁
        (hdet b hb a₁ ha₁ c₁ (c₁ + 1) h_b h_a₁ (by fin_cases c₁ <;> decide))).1
      have hr2 := (one_or_two_le_sum_rayCross c₁ h_b h_a₂
        (hdet b hb a₂ ha₂ c₁ (c₁ + 1) h_b h_a₂ (by fin_cases c₁ <;> decide))).1
      have hsub : ({(b, a₁), (b, a₂)} : Finset (F × F)) ⊆ s.offDiag := by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl <;> assumption
      have hasym : ∀ p ∈ ({(b, a₁), (b, a₂)} : Finset (F × F)),
          (p.2, p.1) ∉ ({(b, a₁), (b, a₂)} : Finset (F × F)) := by
        rintro p hp hsw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp hsw
        rcases hp with rfl | rfl <;> rcases hsw with h | h
        · exact ha1b (Prod.mk.inj h).1
        · exact ha1b (Prod.mk.inj h).1
        · exact ha2b (Prod.mk.inj h).1
        · exact ha2b (Prod.mk.inj h).1
      have hU := two_mul_sum_le _ hsub hasym
      rw [Finset.sum_pair hp_ne] at hU
      change 1 ≤ fn (b, a₁) at hr1
      change 1 ≤ fn (b, a₂) at hr2
      omega
  by_cases hs01 : s₀ = s₁
  · subst hs01
    by_cases hs02 : s₀ = s₂
    · subst hs02
      have hcnt3 : secCount Q q R ω B s₀ = 3 := by
        rw [hsec_eq]
        have hall : s.filter (fun e => inOpenSector s₀ (edgeVec2 Q q R ω e)) = s := by
          refine Finset.filter_eq_self.mpr fun e he => ?_
          dsimp [s] at he
          simp only [Finset.mem_insert, Finset.mem_singleton] at he
          rcases he with rfl | rfl | rfl <;> assumption
        rw [hall, hs_card]
      have hcnt0 : ∀ c' : Fin 3, c' ≠ s₀ → secCount Q q R ω B c' = 0 := fun c' hc' => by
        rw [hsec_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro e he hsec
        dsimp [s] at he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · exact hc' (inOpenSector_unique hsec hs₀)
        · exact hc' (inOpenSector_unique hsec hs₁)
        · exact hc' (inOpenSector_unique hsec hs₂)
      have hcol : blockColor Q q R ω B = s₀ :=
        blockColor_of_strict_majority hinj fun c' hc' => by rw [hcnt3, hcnt0 c' hc']; omega
      rw [hcol, hcnt3] at hbad_compl
      have hb0 : badCount Q q R ω B = 0 := by omega
      rw [hb0]; omega
    · exact (case_two_one he₀ he₁ he₂ h01 h02 h12 hs02 hs₀ hs₁ hs₂).trans (Nat.le_add_right _ _)
  · by_cases hs02 : s₀ = s₂
    · subst hs02
      exact (case_two_one he₀ he₂ he₁ h02 h01 h12.symm hs01 hs₀ hs₂ hs₁).trans
        (Nat.le_add_right _ _)
    · by_cases hs12 : s₁ = s₂
      · subst hs12
        exact (case_two_one he₁ he₂ he₀ h12 h01.symm h02.symm (Ne.symm hs01) hs₁ hs₂ hs₀).trans
          (Nat.le_add_right _ _)
      · have hex_sec (c : Fin 3) : ∃ u ∈ s, inOpenSector c (edgeVec2 Q q R ω u) := by
          have himg : ({s₀, s₁, s₂} : Finset (Fin 3)) = Finset.univ := by
            refine Finset.eq_univ_of_card _ ?_
            rw [Finset.card_insert_of_notMem (by simp [hs01, hs02]), Finset.card_pair hs12,
              Fintype.card_fin]
          have hmem : c ∈ ({s₀, s₁, s₂} : Finset (Fin 3)) := by rw [himg]; exact Finset.mem_univ c
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with rfl | rfl | rfl
          · exact ⟨e₀, he₀, hs₀⟩
          · exact ⟨e₁, he₁, hs₁⟩
          · exact ⟨e₂, he₂, hs₂⟩
        obtain ⟨u₀, hu₀, hsec_u₀⟩ := hex_sec 0
        obtain ⟨u₁, hu₁, hsec_u₁⟩ := hex_sec 1
        obtain ⟨u₂, hu₂, hsec_u₂⟩ := hex_sec 2
        have hu01 : u₀ ≠ u₁ := fun h => by
          subst h; exact absurd (inOpenSector_unique hsec_u₀ hsec_u₁) (by decide)
        have hu12 : u₁ ≠ u₂ := fun h => by
          subst h; exact absurd (inOpenSector_unique hsec_u₁ hsec_u₂) (by decide)
        have hu20 : u₂ ≠ u₀ := fun h => by
          subst h; exact absurd (inOpenSector_unique hsec_u₂ hsec_u₀) (by decide)
        have hs_u : s = {u₀, u₁, u₂} := by
          refine (Finset.eq_of_subset_of_card_le (s := {u₀, u₁, u₂}) (t := s) ?_ ?_).symm
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl <;> assumption
          · rw [hs_card, Finset.card_insert_of_notMem (by simp [hu01, hu20.symm]),
              Finset.card_pair hu12]
        have hcnt1 (c : Fin 3) : secCount Q q R ω B c = 1 := by
          rw [hsec_eq, hs_u]
          rcases c with ⟨_ | _ | _ | _, hlt⟩
          · change (({u₀, u₁, u₂} : Finset F).filter
              fun e => inOpenSector 0 (edgeVec2 Q q R ω e)).card = 1
            have hn1 : ¬inOpenSector 0 (edgeVec2 Q q R ω u₁) := fun h =>
              absurd (inOpenSector_unique h hsec_u₁) (by decide)
            have hn2 : ¬inOpenSector 0 (edgeVec2 Q q R ω u₂) := fun h =>
              absurd (inOpenSector_unique h hsec_u₂) (by decide)
            simp only [Finset.filter_insert, hsec_u₀, hn1, Finset.filter_singleton, hn2,
              ↓reduceIte]
            exact Finset.card_singleton u₀
          · change (({u₀, u₁, u₂} : Finset F).filter
              fun e => inOpenSector 1 (edgeVec2 Q q R ω e)).card = 1
            have hn0 : ¬inOpenSector 1 (edgeVec2 Q q R ω u₀) := fun h =>
              absurd (inOpenSector_unique h hsec_u₀) (by decide)
            have hn2 : ¬inOpenSector 1 (edgeVec2 Q q R ω u₂) := fun h =>
              absurd (inOpenSector_unique h hsec_u₂) (by decide)
            simp only [Finset.filter_insert, hn0, hsec_u₁, Finset.filter_singleton, hn2,
              ↓reduceIte]
            exact Finset.card_singleton u₁
          · change (({u₀, u₁, u₂} : Finset F).filter
              fun e => inOpenSector 2 (edgeVec2 Q q R ω e)).card = 1
            have hn0 : ¬inOpenSector 2 (edgeVec2 Q q R ω u₀) := fun h =>
              absurd (inOpenSector_unique h hsec_u₀) (by decide)
            have hn1 : ¬inOpenSector 2 (edgeVec2 Q q R ω u₁) := fun h =>
              absurd (inOpenSector_unique h hsec_u₁) (by decide)
            simp only [Finset.filter_insert, hn0, hn1, Finset.filter_singleton, hsec_u₂,
              ↓reduceIte, Finset.card_singleton]
          · omega
        have hbad2 : badCount Q q R ω B = 2 := by
          rw [hcnt1] at hbad_compl; omega
        rw [hbad2]
        have hd01 := hdet u₀ hu₀ u₁ hu₁ 0 1 hsec_u₀ hsec_u₁ (by decide)
        have hd12 := hdet u₁ hu₁ u₂ hu₂ 1 2 hsec_u₁ hsec_u₂ (by decide)
        have hd20 := hdet u₂ hu₂ u₀ hu₀ 2 0 hsec_u₂ hsec_u₀ (by decide)
        obtain ⟨hr0_1, hr0_2⟩ := one_or_two_le_sum_rayCross 0 hsec_u₀ hsec_u₁ hd01
        obtain ⟨hr1_1, hr1_2⟩ := one_or_two_le_sum_rayCross 1 hsec_u₁ hsec_u₂ hd12
        obtain ⟨hr2_1, hr2_2⟩ := one_or_two_le_sum_rayCross 2 hsec_u₂ hsec_u₀ hd20
        let T : Finset (F × F) := {(u₀, u₁), (u₁, u₂), (u₂, u₀)}
        have hT_sub : T ⊆ s.offDiag := by
          intro p hp
          simp only [T, Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl | rfl
          · exact Finset.mem_offDiag.mpr ⟨hu₀, hu₁, hu01⟩
          · exact Finset.mem_offDiag.mpr ⟨hu₁, hu₂, hu12⟩
          · exact Finset.mem_offDiag.mpr ⟨hu₂, hu₀, hu20⟩
        have hT_asym : ∀ p ∈ T, (p.2, p.1) ∉ T := by
          rintro p hp hsw
          simp only [T, Finset.mem_insert, Finset.mem_singleton] at hp hsw
          rcases hp with rfl | rfl | rfl
          · rcases hsw with h | h | h
            · exact hu01 (Prod.mk.inj h).2
            · exact hu20 (Prod.mk.inj h).2.symm
            · exact hu12 (Prod.mk.inj h).1
          · rcases hsw with h | h | h
            · exact hu20 (Prod.mk.inj h).1
            · exact hu12 (Prod.mk.inj h).2
            · exact hu01 (Prod.mk.inj h).2.symm
          · rcases hsw with h | h | h
            · exact hu12 (Prod.mk.inj h).2.symm
            · exact hu01 (Prod.mk.inj h).1
            · exact hu20 (Prod.mk.inj h).2
        have hT_sum : (∑ p ∈ T, fn p) = fn (u₀, u₁) + (fn (u₁, u₂) + fn (u₂, u₀)) := by
          dsimp [T]
          have hnot_mem : (u₀, u₁) ∉ ({(u₁, u₂), (u₂, u₀)} : Finset (F × F)) := by
            intro hm
            simp only [Finset.mem_insert, Finset.mem_singleton] at hm
            rcases hm with h | h
            · exact hu01 (Prod.mk.inj h).1
            · exact hu20 (Prod.mk.inj h).1.symm
          rw [Finset.sum_insert hnot_mem,
            Finset.sum_pair (by intro h; exact hu12 (Prod.mk.inj h).1)]
        have hT_two_le : 2 * ∑ p ∈ T, fn p ≤ ∑ p ∈ s.offDiag, fn p :=
          two_mul_sum_le T hT_sub hT_asym
        by_cases hall_pos : 0 < det2 (edgeVec2 Q q R ω u₀) (edgeVec2 Q q R ω u₁) ∧
            0 < det2 (edgeVec2 Q q R ω u₁) (edgeVec2 Q q R ω u₂) ∧
            0 < det2 (edgeVec2 Q q R ω u₂) (edgeVec2 Q q R ω u₀)
        · obtain ⟨w₀', w₁', w₂', hw₀', hw₁', hw₂', hsum', hx', hy'⟩ :=
            convex_zero_of_pos_det2 hall_pos.1 hall_pos.2.1 hall_pos.2.2
          have hex_conv : ∃ w₀ w₁ w₂ : ℝ, 0 ≤ w₀ ∧ 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ w₀ + w₁ + w₂ = 1 ∧
              w₀ * (edgeVec2 Q q R ω e₀).1 + w₁ * (edgeVec2 Q q R ω e₁).1 +
                w₂ * (edgeVec2 Q q R ω e₂).1 = 0 ∧
              w₀ * (edgeVec2 Q q R ω e₀).2 + w₁ * (edgeVec2 Q q R ω e₁).2 +
                w₂ * (edgeVec2 Q q R ω e₂).2 = 0 := by
            let wt (e : F) : ℝ :=
              (if e = u₀ then w₀' else 0) + (if e = u₁ then w₁' else 0) +
                (if e = u₂ then w₂' else 0)
            have hwt_nonneg (e : F) : 0 ≤ wt e := by
              dsimp [wt]
              refine add_nonneg (add_nonneg ?_ ?_) ?_ <;> split_ifs <;> linarith
            have hwt_u0 : wt u₀ = w₀' := by simp [wt, hu01, hu20.symm]
            have hwt_u1 : wt u₁ = w₁' := by simp [wt, hu01.symm, hu12]
            have hwt_u2 : wt u₂ = w₂' := by simp [wt, hu20, hu12.symm]
            have hsum_s : ∀ f : F → ℝ, f e₀ + f e₁ + f e₂ = f u₀ + f u₁ + f u₂ := fun f => by
              have h1 : ∑ x ∈ s, f x = f e₀ + (f e₁ + f e₂) := by
                dsimp [s]
                rw [Finset.sum_insert (by simp [h01, h02]), Finset.sum_pair h12]
              have h2 : ∑ x ∈ s, f x = f u₀ + (f u₁ + f u₂) := by
                rw [hs_u, Finset.sum_insert (by simp [hu01, hu20.symm]), Finset.sum_pair hu12]
              linarith only [h1, h2]
            refine ⟨wt e₀, wt e₁, wt e₂, hwt_nonneg e₀, hwt_nonneg e₁, hwt_nonneg e₂, ?_, ?_, ?_⟩
            · rw [hsum_s wt, hwt_u0, hwt_u1, hwt_u2, hsum']
            · rw [hsum_s (fun e => wt e * (edgeVec2 Q q R ω e).1), hwt_u0, hwt_u1, hwt_u2, hx']
            · rw [hsum_s (fun e => wt e * (edgeVec2 Q q R ω e).2), hwt_u0, hwt_u1, hwt_u2, hy']
          simp only [hex_conv, ↓reduceIte]
          change 4 * 2 ≤ (∑ p ∈ s.offDiag, fn p) + 2 * 1
          have h3 : 3 ≤ ∑ p ∈ T, fn p := by
            rw [hT_sum]; dsimp [fn]; omega
          omega
        · have h4 : 4 ≤ ∑ p ∈ T, fn p := by
            rw [hT_sum]
            dsimp [fn]
            rcases lt_or_gt_of_ne hd01 with hn0 | hp0
            · have := hr0_2 hn0; omega
            · rcases lt_or_gt_of_ne hd12 with hn1 | hp1
              · have := hr1_2 hn1; omega
              · rcases lt_or_gt_of_ne hd20 with hn2 | hp2
                · have := hr2_2 hn2; omega
                · exact absurd ⟨hp0, hp1, hp2⟩ hall_pos
          change 4 * 2 ≤ (∑ p ∈ s.offDiag, fn p) + _
          omega


open Classical in
/-- Every bichromatic edge contributes at least `1` mismatched endpoint half-edge (`badCount`). -/
private theorem sum_cutAny_le_sum_badCount [Fintype F] {Q : Multigraph W F}
    (hloop : Q.Loopless) (q : ℝ) (R : ℕ) {ω : W → BlockSample}
    (_hray : ∀ e : F, ∀ c : Fin 3, dot2 (normVec c) (edgeVec2 Q q R ω e) ≠ 0) :
    (Finset.univ.filter fun e : F => ω ∈ cutAnyEvent Q q R e).card ≤
      ∑ B : W, badCount Q q R ω B := by
  have h1 : (Finset.univ.filter fun e : F => ω ∈ cutAnyEvent Q q R e).card ≤
      ∑ e : F, ((if ¬inOpenSector (blockColor Q q R ω (Q.src e)) (edgeVec2 Q q R ω e)
          then 1 else 0) +
        (if ¬inOpenSector (blockColor Q q R ω (Q.tgt e)) (edgeVec2 Q q R ω e)
          then 1 else 0)) := by
    rw [Finset.card_filter]
    refine Finset.sum_le_sum fun e _ => ?_
    by_cases hcut : ω ∈ cutAnyEvent Q q R e
    · simp only [hcut, ↓reduceIte]
      by_contra! h0
      have hs : inOpenSector (blockColor Q q R ω (Q.src e)) (edgeVec2 Q q R ω e) := by
        by_contra h; simp only [h, not_false_eq_true, ↓reduceIte] at h0; omega
      have ht : inOpenSector (blockColor Q q R ω (Q.tgt e)) (edgeVec2 Q q R ω e) := by
        by_contra h; simp only [h, not_false_eq_true, ↓reduceIte] at h0; omega
      exact hcut (inOpenSector_unique hs ht)
    · simp only [hcut, ↓reduceIte]; omega
  refine h1.trans ?_
  have hbad_sum : (∑ B : W, badCount Q q R ω B) =
      ∑ B : W, ∑ e : F,
        if (Q.src e = B ∨ Q.tgt e = B) ∧
            ¬inOpenSector (blockColor Q q R ω B) (edgeVec2 Q q R ω e) then 1 else 0 := by
    refine Finset.sum_congr rfl fun B _ => ?_
    unfold badCount
    rw [toFinset_eq_of_fintype (Q.incidenceSet B) _, ← Finset.card_filter]
    congr 1; ext e; simp [Multigraph.mem_incidenceSet]
  rw [hbad_sum, Finset.sum_comm]
  refine Finset.sum_le_sum fun e _ => ?_
  have hsub : ({Q.src e, Q.tgt e} : Finset W) ⊆ Finset.univ := Finset.subset_univ _
  calc ((if ¬inOpenSector (blockColor Q q R ω (Q.src e)) (edgeVec2 Q q R ω e) then 1 else 0) +
        (if ¬inOpenSector (blockColor Q q R ω (Q.tgt e)) (edgeVec2 Q q R ω e) then 1 else 0))
      = ∑ B ∈ ({Q.src e, Q.tgt e} : Finset W),
          if (Q.src e = B ∨ Q.tgt e = B) ∧
            ¬inOpenSector (blockColor Q q R ω B) (edgeVec2 Q q R ω e) then 1 else 0 := by
        rw [Finset.sum_pair (hloop e)]
        simp
    _ ≤ ∑ B : W,
          if (Q.src e = B ∨ Q.tgt e = B) ∧
            ¬inOpenSector (blockColor Q q R ω B) (edgeVec2 Q q R ω e) then 1 else 0 :=
        Finset.sum_le_sum_of_subset hsub


end BadCountPointwise

end Cslib.Circuits.Frontier.TensorRank
