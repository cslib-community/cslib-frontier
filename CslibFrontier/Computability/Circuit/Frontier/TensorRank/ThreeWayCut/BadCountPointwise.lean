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
    rw [toFinset_eq_of_fintype (Q.incidenceSet B) _, Finset.card_filter, Nat.cast_sum]
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
      exact MeasurableSet.iUnion fun c => (measurableSet_blockColor_eq Q q R B c).inter
        (measurableSet_inOpenSector_edgeVec2 Q q R e c)
    exact Measurable.ite hm_in.compl measurable_const measurable_const
  refine Integrable.of_bound hm_bad.aestronglyMeasurable 3
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), badCount,
    toFinset_eq_of_fintype (Q.incidenceSet B) _]
  exact_mod_cast (Finset.card_filter_le _ _).trans
    (Set.ncard_eq_toFinset_card' (Q.incidenceSet B) ▸ hdeg B)

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
  set z := edgeVec2 Q q R ω
  let fn (p : F × F) : ℕ := ∑ c : Fin 3, if rayCross c (z p.1) (z p.2) then 1 else 0
  change 4 * badCount Q q R ω B ≤ ∑ p ∈ s.offDiag, fn p + 2 * _
  have fn_swap (x y : F) : fn (x, y) = fn (y, x) :=
    Finset.sum_congr rfl fun c _ => by simp only [rayCross_comm c (z x)]
  have hfn {c : Fin 3} {x y : F} (hx : inOpenSector c (z x)) (hy : inOpenSector (c + 1) (z y))
      (hd : det2 (z x) (z y) ≠ 0) : 1 ≤ fn (x, y) ∧ (det2 (z x) (z y) < 0 → 2 ≤ fn (x, y)) :=
    one_or_two_le_sum_rayCross c hx hy hd
  have hne {i j : Fin 3} {x y : F} (hx : inOpenSector i (z x)) (hy : inOpenSector j (z y))
      (hij : i ≠ j) : x ≠ y := by
    rintro rfl; exact hij (inOpenSector_unique hx hy)
  have hs_card : s.card = 3 := by
    dsimp only [s]
    rw [Finset.card_insert_of_notMem (by simp [h01, h02]), Finset.card_pair h12]
  have hs_eq {x y w : F} (hx : x ∈ s) (hy : y ∈ s) (hw : w ∈ s) (hxy : x ≠ y) (hyw : y ≠ w)
      (hxw : x ≠ w) : s = {x, y, w} :=
    (Finset.eq_of_subset_of_card_le (by simp [Finset.insert_subset_iff, hx, hy, hw]) (by
      rw [hs_card, Finset.card_insert_of_notMem (by simp [hxy, hxw]), Finset.card_pair hyw])).symm
  /- Each unordered pair of a three-element subset of `s` is counted twice in the off-diagonal. -/
  have hsum3 {x y w : F} (hx : x ∈ s) (hy : y ∈ s) (hw : w ∈ s) (hxy : x ≠ y) (hyw : y ≠ w)
      (hwx : w ≠ x) : 2 * (fn (x, y) + fn (y, w) + fn (w, x)) ≤ ∑ p ∈ s.offDiag, fn p := by
    refine le_of_eq_of_le ?_ (Finset.sum_le_sum_of_subset (s :=
      {(x, y), (y, x), (y, w), (w, y), (w, x), (x, w)}) (by
        simp [Finset.insert_subset_iff, hx, hy, hw, hxy, hyw, hwx, hxy.symm, hyw.symm, hwx.symm]))
    rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert,
      Finset.sum_pair, fn_swap y x, fn_swap w y, fn_swap x w]
    · ring
    all_goals simp [hxy, hyw, hwx, hxy.symm, hyw.symm, hwx.symm]
  have he₀ : e₀ ∈ s := by simp [s]
  have he₁ : e₁ ∈ s := by simp [s]
  have he₂ : e₂ ∈ s := by simp [s]
  obtain ⟨s₀, hs₀⟩ := exists_inOpenSector_of_ne_zero (hray e₀ he₀)
  obtain ⟨s₁, hs₁⟩ := exists_inOpenSector_of_ne_zero (hray e₁ he₁)
  obtain ⟨s₂, hs₂⟩ := exists_inOpenSector_of_ne_zero (hray e₂ he₂)
  have hsec_eq (c : Fin 3) :
      secCount Q q R ω B c = (s.filter fun e => inOpenSector c (z e)).card := by
    rw [secCount, toFinset_eq_of_fintype (Q.incidenceSet B) _, ← hinc]
  have hbad_eq : badCount Q q R ω B =
      (s.filter fun e => ¬inOpenSector (blockColor Q q R ω B) (z e)).card := by
    rw [badCount, toFinset_eq_of_fintype (Q.incidenceSet B) _, ← hinc]
  have hbad_compl : badCount Q q R ω B + secCount Q q R ω B (blockColor Q q R ω B) = 3 := by
    rw [hbad_eq, hsec_eq, add_comm, Finset.card_filter_add_card_filter_not, hs_card]
  have hadj : ∀ i j : Fin 3, i ≠ j → j = i + 1 ∨ i = j + 1 := by decide
  have case_two_one {a₁ a₂ b : F} (ha₁ : a₁ ∈ s) (ha₂ : a₂ ∈ s) (hb : b ∈ s)
      (ha12 : a₁ ≠ a₂) (ha1b : a₁ ≠ b) (ha2b : a₂ ≠ b) {c₀ c₁ : Fin 3} (hc01 : c₀ ≠ c₁)
      (h_a₁ : inOpenSector c₀ (z a₁)) (h_a₂ : inOpenSector c₀ (z a₂))
      (h_b : inOpenSector c₁ (z b)) : 4 * badCount Q q R ω B ≤ ∑ p ∈ s.offDiag, fn p := by
    have hs_perm := hs_eq ha₁ ha₂ hb ha12 ha2b ha1b
    have hcnt_c₀ : secCount Q q R ω B c₀ = 2 := by
      rw [hsec_eq, hs_perm]
      have hnb : ¬inOpenSector c₀ (z b) := fun h => hc01 (inOpenSector_unique h h_b)
      simp only [Finset.filter_insert, h_a₁, h_a₂, Finset.filter_singleton, hnb, ↓reduceIte]
      exact Finset.card_pair ha12
    have hcnt_lt (c' : Fin 3) (hc' : c' ≠ c₀) : secCount Q q R ω B c' < 2 := by
      rw [hsec_eq, hs_perm]
      have hn1 : ¬inOpenSector c' (z a₁) := fun h => hc' (inOpenSector_unique h h_a₁)
      have hn2 : ¬inOpenSector c' (z a₂) := fun h => hc' (inOpenSector_unique h h_a₂)
      simp only [Finset.filter_insert, hn1, hn2, ↓reduceIte]
      exact (Finset.card_filter_le _ _).trans_lt (by simp)
    have hcol : blockColor Q q R ω B = c₀ :=
      blockColor_of_strict_majority hinj fun c' hc' => by rw [hcnt_c₀]; exact hcnt_lt c' hc'
    obtain ⟨hr1, hr2⟩ : 1 ≤ fn (a₂, b) ∧ 1 ≤ fn (b, a₁) := by
      rcases hadj c₀ c₁ hc01 with rfl | rfl
      · rw [fn_swap b]
        exact ⟨(hfn h_a₂ h_b (hdet _ ha₂ _ hb _ _ h_a₂ h_b hc01)).1,
          (hfn h_a₁ h_b (hdet _ ha₁ _ hb _ _ h_a₁ h_b hc01)).1⟩
      · rw [fn_swap a₂]
        exact ⟨(hfn h_b h_a₂ (hdet _ hb _ ha₂ _ _ h_b h_a₂ hc01.symm)).1,
          (hfn h_b h_a₁ (hdet _ hb _ ha₁ _ _ h_b h_a₁ hc01.symm)).1⟩
    rw [hcol, hcnt_c₀] at hbad_compl
    have := hsum3 ha₁ ha₂ hb ha12 ha2b ha1b.symm
    omega
  by_cases hs01 : s₀ = s₁
  · subst hs01
    by_cases hs02 : s₀ = s₂
    · subst hs02
      have hcnt3 : secCount Q q R ω B s₀ = 3 := by
        rw [hsec_eq, Finset.filter_true_of_mem, hs_card]
        simp only [s, Finset.mem_insert, Finset.mem_singleton]
        rintro e (rfl | rfl | rfl) <;> assumption
      have hcol : blockColor Q q R ω B = s₀ := blockColor_of_strict_majority hinj fun c' hc' => by
        rw [hcnt3, hsec_eq]
        exact (Finset.card_lt_card (Finset.filter_ssubset.mpr
          ⟨e₀, he₀, fun h => hc' (inOpenSector_unique h hs₀)⟩)).trans_eq hs_card
      rw [hcol, hcnt3] at hbad_compl
      omega
    · exact (case_two_one he₀ he₁ he₂ h01 h02 h12 hs02 hs₀ hs₁ hs₂).trans (Nat.le_add_right _ _)
  · by_cases hs02 : s₀ = s₂
    · subst hs02
      exact (case_two_one he₀ he₂ he₁ h02 h01 h12.symm hs01 hs₀ hs₂ hs₁).trans
        (Nat.le_add_right _ _)
    · by_cases hs12 : s₁ = s₂
      · subst hs12
        exact (case_two_one he₁ he₂ he₀ h12 h01.symm h02.symm (Ne.symm hs01) hs₁ hs₂ hs₀).trans
          (Nat.le_add_right _ _)
      · have hcover : ∀ a b d c : Fin 3, a ≠ b → a ≠ d → b ≠ d → c = a ∨ c = b ∨ c = d := by
          decide
        have hex_sec (c : Fin 3) : ∃ u ∈ s, inOpenSector c (z u) := by
          rcases hcover s₀ s₁ s₂ c hs01 hs02 hs12 with rfl | rfl | rfl
          exacts [⟨e₀, he₀, hs₀⟩, ⟨e₁, he₁, hs₁⟩, ⟨e₂, he₂, hs₂⟩]
        obtain ⟨u₀, hu₀, hsec_u₀⟩ := hex_sec 0
        obtain ⟨u₁, hu₁, hsec_u₁⟩ := hex_sec 1
        obtain ⟨u₂, hu₂, hsec_u₂⟩ := hex_sec 2
        have hu01 := hne hsec_u₀ hsec_u₁ (by decide)
        have hu12 := hne hsec_u₁ hsec_u₂ (by decide)
        have hu20 := hne hsec_u₂ hsec_u₀ (by decide)
        have hs_u := hs_eq hu₀ hu₁ hu₂ hu01 hu12 hu20.symm
        have hcnt1 (c : Fin 3) : secCount Q q R ω B c = 1 := by
          have h {i : Fin 3} {u : F} (hu : inOpenSector i (z u)) : inOpenSector c (z u) ↔ c = i :=
            ⟨fun h => inOpenSector_unique h hu, fun h => h ▸ hu⟩
          rw [hsec_eq, hs_u]
          simp only [Finset.filter_insert, Finset.filter_singleton, h hsec_u₀, h hsec_u₁,
            h hsec_u₂]
          fin_cases c <;> simp
        rw [hcnt1] at hbad_compl
        have hd01 := hdet u₀ hu₀ u₁ hu₁ 0 1 hsec_u₀ hsec_u₁ (by decide)
        have hd12 := hdet u₁ hu₁ u₂ hu₂ 1 2 hsec_u₁ hsec_u₂ (by decide)
        have hd20 := hdet u₂ hu₂ u₀ hu₀ 2 0 hsec_u₂ hsec_u₀ (by decide)
        obtain ⟨hr0_1, hr0_2⟩ := hfn hsec_u₀ hsec_u₁ hd01
        obtain ⟨hr1_1, hr1_2⟩ := hfn hsec_u₁ hsec_u₂ hd12
        obtain ⟨hr2_1, hr2_2⟩ := hfn hsec_u₂ hsec_u₀ hd20
        have hT := hsum3 hu₀ hu₁ hu₂ hu01 hu12 hu20
        by_cases hall_pos : 0 < det2 (z u₀) (z u₁) ∧ 0 < det2 (z u₁) (z u₂) ∧
            0 < det2 (z u₂) (z u₀)
        · obtain ⟨w₀', w₁', w₂', hw₀', hw₁', hw₂', hsum', hx', hy'⟩ :=
            convex_zero_of_pos_det2 hall_pos.1 hall_pos.2.1 hall_pos.2.2
          rw [ite_eq_left]
          · omega
          -- Transport the convex combination from `u₀, u₁, u₂` to `e₀, e₁, e₂`.
          let wt (e : F) : ℝ :=
            (if e = u₀ then w₀' else 0) + (if e = u₁ then w₁' else 0) + (if e = u₂ then w₂' else 0)
          have hwt (e : F) : 0 ≤ wt e := by dsimp only [wt]; split_ifs <;> linarith
          have hw0 : wt u₀ = w₀' := by simp [wt, hu01, hu20.symm]
          have hw1 : wt u₁ = w₁' := by simp [wt, hu01.symm, hu12]
          have hw2 : wt u₂ = w₂' := by simp [wt, hu20, hu12.symm]
          have hsum_s (g : F → ℝ) :
              wt e₀ * g e₀ + wt e₁ * g e₁ + wt e₂ * g e₂ =
                w₀' * g u₀ + w₁' * g u₁ + w₂' * g u₂ := by
            have h1 : ∑ x ∈ s, wt x * g x = wt e₀ * g e₀ + (wt e₁ * g e₁ + wt e₂ * g e₂) := by
              dsimp only [s]
              rw [Finset.sum_insert (by simp [h01, h02]), Finset.sum_pair h12]
            rw [hs_u, Finset.sum_insert (by simp [hu01, hu20.symm]), Finset.sum_pair hu12, hw0, hw1,
              hw2] at h1
            linarith
          refine ⟨wt e₀, wt e₁, wt e₂, hwt e₀, hwt e₁, hwt e₂, ?_, ?_, ?_⟩
          · linarith [hsum_s fun _ => 1]
          · rw [hsum_s fun e => (z e).1, hx']
          · rw [hsum_s fun e => (z e).2, hy']
        · rcases lt_or_gt_of_ne hd01 with hn | hp0
          · have := hr0_2 hn; omega
          rcases lt_or_gt_of_ne hd12 with hn | hp1
          · have := hr1_2 hn; omega
          rcases lt_or_gt_of_ne hd20 with hn | hp2
          · have := hr2_2 hn; omega
          exact absurd ⟨hp0, hp1, hp2⟩ hall_pos


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
      by_cases hs : inOpenSector (blockColor Q q R ω (Q.src e)) (edgeVec2 Q q R ω e)
      · have ht : ¬inOpenSector (blockColor Q q R ω (Q.tgt e)) (edgeVec2 Q q R ω e) :=
          fun ht => hcut (inOpenSector_unique hs ht)
        simp [hs, ht]
      · simp [hs]
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
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)


end BadCountPointwise

end Cslib.Circuits.Frontier.TensorRank
