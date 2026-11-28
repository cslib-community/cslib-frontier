/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.Matching
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.PairBound.Majorant
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.WeightedMatching
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Switched.Coefficient
import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Unconditional matched-pair Gaussian layout bound below `5 / 36`

Combines the `7 / 8` vertex-coverage matching theorem on simple cubic multigraphs
(`Multigraph.exists_isMatching_seven_eighths`), the simultaneous Gaussian concentration framework
for matched-edge layouts (`Gaussian.cubicLayoutBound_of_matching_vec_mean`), and the certified
all-threshold Gaussian majorants on `rawEdgeVector` stars and matched pairs
(`Gaussian.PairBound.exists_radius_admissible`, `Gaussian.PairBound.starStraddleCost_le`,
`Gaussian.PairBound.pairCost_le`) to prove an unconditional cubic layout bound strictly below
`5 / 36 < Switched.switchedCoefficient`:

* Unpaired vertices (`|V \ V(M)| = |V| - 2 |M| ≤ |V| / 8`) straddle threshold `t` with probability
  at most `140367 / 1000000` (`starStraddleCost_le`).
* Matched edges (`|M| ≥ (7 / 16) |V|`) incur expected two-vertex cost at most `27735 / 100000`
  (`pairCost_le`), strictly less than `2 · (140367 / 1000000) = 280734 / 1000000`.
* Summing over `V` and `M` bounds `expectedMatchingCostVec` at every threshold `t` by
  `(|V| / 8) · (140367 / 1000000) + (7 |V| / 16) · (27735 / 100000) = (277773 / 2000000) |V|`,
  giving `CubicLayoutBound (277773 / 2000000)` (`cubicLayoutBound_pairBound`) and hence
  `CubicLayoutBound (5 / 36)` and `LayoutBound 3 (5 / 18)` (`layoutBound_five_div_eighteen`).

The matched-pair layout bound is original to this library.

## Main definitions

* `Cslib.Circuits.Frontier.Gaussian.PairBound.pairBoundCoefficient`: the certified cubic layout
  coefficient `277773 / 2000000` (`0.1388865 < 5 / 36`).

## Main results

* `Cslib.Circuits.Frontier.Gaussian.PairBound.pairBoundCoefficient_lt_five_div_thirty_six`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.five_div_thirty_six_lt_switchedCoefficient`:
  `pairBoundCoefficient < 5 / 36 < Switched.switchedCoefficient`.
* `Cslib.Circuits.Frontier.cubicLayoutBound_pairBound`,
  `Cslib.Circuits.Frontier.cubicLayoutBound_five_div_thirty_six`,
  `Cslib.Circuits.Frontier.layoutBound_pairBound`,
  `Cslib.Circuits.Frontier.layoutBound_five_div_eighteen`: unconditional cubic and degree-`3`
  layout bounds.

## References

* [S. Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster
  Exponential Algorithms*][Gaspers2026]
-/

public section

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

namespace Cslib.Circuits.Frontier.Gaussian.PairBound

/-! ### Certified rational cubic coefficient and numerical comparisons -/

/-- Certified cubic layout coefficient `(1 / 8) · (140367 / 1000000) + (7 / 16) · (27735 / 100000)
= 277773 / 2000000 = 0.1388865`. -/
@[expose] noncomputable def pairBoundCoefficient : ℝ := 277773 / 2000000

theorem pairBoundCoefficient_pos : 0 < pairBoundCoefficient := by
  norm_num [pairBoundCoefficient]

theorem pairBoundCoefficient_lt_five_div_thirty_six :
    pairBoundCoefficient < 5 / 36 := by
  norm_num [pairBoundCoefficient]

/-- Strict separation `5 / 36 < (3 / (4π)) arccos (5 / 6)` (`0.138888... < 0.139822...`). -/
theorem five_div_thirty_six_lt_switchedCoefficient :
    (5 / 36 : ℝ) < Switched.switchedCoefficient := by
  have cos_step : ∀ {x l v : ℝ}, 0 ≤ l → l ≤ cos x → v ≤ 2 * l ^ 2 - 1 → v ≤ cos (2 * x) := by
    intro x l v h0 hl hv
    rw [cos_two_mul]
    nlinarith [pow_le_pow_left₀ h0 hl 2]
  have hcos : 5 / 6 < cos (291 / 500 : ℝ) := by
    have hb := cos_bound (x := 291 / 4000) (by norm_num)
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 291 / 4000)] at hb
    have h0 : 997352259 / 1000000000 ≤ cos (291 / 4000) := by linarith [(abs_le.mp hb).1]
    have h1 := cos_step (by norm_num) h0 (v := 989423057 / 1000000000) (by norm_num)
    have h2 := cos_step (by norm_num) h1 (v := 957915971 / 1000000000) (by norm_num)
    have h3 := cos_step (by norm_num) h2 (v := 417603007 / 500000000) (by norm_num)
    have hval : (291 / 500 : ℝ) = 2 * (2 * (2 * (291 / 4000))) := by norm_num
    rw [hval]
    linarith
  have hangle : (291 / 500 : ℝ) < arccos (5 / 6) := by
    have hlt := arccos_lt_arccos (by norm_num) hcos (cos_le_one _)
    rwa [arccos_cos (by norm_num) (by linarith [pi_gt_three])] at hlt
  unfold Switched.switchedCoefficient
  have hpi : 0 < π := pi_pos
  have hpi_hi : π < 31416 / 10000 := by linarith [pi_lt_d4]
  have hrew : 3 / (4 * π) * arccos (5 / 6) = 3 * arccos (5 / 6) / (4 * π) := by ring
  rw [hrew, lt_div_iff₀ (by positivity)]
  linarith

theorem pairBoundCoefficient_lt_switchedCoefficient :
    pairBoundCoefficient < Switched.switchedCoefficient :=
  pairBoundCoefficient_lt_five_div_thirty_six.trans five_div_thirty_six_lt_switchedCoefficient

theorem one_add_inv_two_mul_pairBoundCoefficient :
    1 + 1 / (2 * pairBoundCoefficient) = 1277773 / 277773 := by
  norm_num [pairBoundCoefficient]

/-! ### Expected matching cost on simple cubic multigraphs -/

private def tuple3 {α : Type*} (a b c : α) : Fin 3 → α
  | 0 => a
  | 1 => b
  | 2 => c

private def tuple4 {α : Type*} (a b c d : α) : Fin 4 → α
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d

private theorem straddlesOn_of_image_eq {ι E : Type*} (score : E → ℝ) (t : ℝ)
    {f : ι → E} {idx : Set ι} {S : Set E} (himg : f '' idx = S) :
    StraddlesOn score t S ↔ StraddlesOn (fun i => score (f i)) t idx := by
  rw [← himg]
  simp only [StraddlesOn, Set.mem_image, exists_exists_and_eq_and]

private theorem image_tuple3_univ {α : Type*} (a b c : α) :
    tuple3 a b c '' Set.univ = {a, b, c} := by
  ext x
  simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩; fin_cases i <;> simp [tuple3]
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

private theorem image_tuple4_univ {α : Type*} (a b c d : α) :
    tuple4 a b c d '' Set.univ = ({a, b} : Set α) ∪ {c, d} := by
  ext x
  simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩; fin_cases i <;> simp [tuple4]
  · rintro ((rfl | rfl) | (rfl | rfl))
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

private theorem image_tuple4_01 {α : Type*} (a b c d : α) :
    tuple4 a b c d '' ({0, 1} : Set (Fin 4)) = {a, b} := by
  ext x
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl | rfl, rfl⟩ <;> simp [tuple4]
  · rintro (rfl | rfl)
    · exact ⟨0, Or.inl rfl, rfl⟩
    · exact ⟨1, Or.inr rfl, rfl⟩

private theorem image_tuple4_23 {α : Type*} (a b c d : α) :
    tuple4 a b c d '' ({2, 3} : Set (Fin 4)) = {c, d} := by
  ext x
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl | rfl, rfl⟩ <;> simp [tuple4]
  · rintro (rfl | rfl)
    · exact ⟨2, Or.inl rfl, rfl⟩
    · exact ⟨3, Or.inr rfl, rfl⟩

private theorem measurableSet_starStradSet {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] (u : Fin 3 → F) (t : ℝ) :
    MeasurableSet {x : F | StraddlesOn (fun i : Fin 3 => ⟪u i, x⟫) t Set.univ} := by
  have heq : {x : F | StraddlesOn (fun i : Fin 3 => ⟪u i, x⟫) t Set.univ} =
      (⋃ i : Fin 3, {x : F | ⟪u i, x⟫ < t}) ∩ (⋃ i : Fin 3, {x : F | t ≤ ⟪u i, x⟫}) := by
    ext x; simp [StraddlesOn]
  rw [heq]
  exact (MeasurableSet.iUnion fun i =>
      measurableSet_lt (by fun_prop : Measurable fun x : F => ⟪u i, x⟫) measurable_const).inter
    (MeasurableSet.iUnion fun i =>
      measurableSet_le measurable_const (by fun_prop : Measurable fun x : F => ⟪u i, x⟫))

/-- At the universal admissibility radius `R`, every finite simple cubic multigraph admits a
`7 / 8` vertex-coverage matching `M` whose expected matching cost under `rawEdgeVector G rawRatio R`
is at most `|V| * pairBoundCoefficient` at every threshold `t`. -/
theorem exists_radius_expectedMatchingCostVec_le :
    ∃ R : ℕ, ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E),
      G.Loopless → Function.Injective G.ends → (∀ v, (G.incidenceSet v).ncard = 3) →
      ∃ M : Set E, G.IsMatching M ∧
        ∀ t, expectedMatchingCostVec G M (rawEdgeVector G rawRatio R) t ≤
          Fintype.card V * pairBoundCoefficient := by
  obtain ⟨R, hR⟩ := exists_radius_admissible
  refine ⟨R, fun V E _ _ G hloop hinj h3 => ?_⟩
  classical
  have hdeg : G.MaxDegreeLE 3 := fun v => (h3 v).le
  obtain ⟨hstar, hpair⟩ := hR V E G hloop hdeg
  obtain ⟨M, hM, _, h78⟩ := G.exists_isMatching_seven_eighths hloop hinj h3
  set vec := rawEdgeVector G rawRatio R
  set P := Measure.pi fun _ : V => gaussianReal 0 1
  refine ⟨M, hM, fun t => ?_⟩
  have hstar_v (v : V) : P.real (unmatchedVecStraddleEvent G M vec t v) ≤
      if v ∉ G.matchedVertices M then (140367 / 1000000 : ℝ) else 0 := by
    unfold unmatchedVecStraddleEvent
    by_cases hv : v ∈ G.matchedVertices M
    · simp [hv]
    · simp only [hv, not_false_eq_true, ↓reduceIte]
      have hne : (G.incidenceSet v).Nonempty :=
        (Set.ncard_pos (Set.toFinite _)).mp (by rw [h3 v]; decide)
      obtain ⟨ea, hea⟩ := hne
      set eb := G.outerLow (fun _ => 0) v ea
      set ec := G.outerHigh (fun _ => 0) v ea
      have hbc := (G.outerLow_outerHigh_spec h3 (fun _ => 0) hea).2.1
      have hv_eq : G.incidenceSet v = {ea, eb, ec} := by
        rw [← Set.insert_sdiff_self_of_mem hea, hbc]
      set u : Fin 3 → EuclideanSpace ℝ V := fun i => vec (tuple3 ea eb ec i)
      have hev : {ω : V → ℝ | G.EdgeStraddles (vecScore vec ω) t v} =
          {ω : V → ℝ | WithLp.toLp 2 ω ∈
            {x : EuclideanSpace ℝ V | StraddlesOn (fun i : Fin 3 => ⟪u i, x⟫) t Set.univ}} := by
        ext ω
        simp only [Multigraph.EdgeStraddles, hv_eq,
          straddlesOn_of_image_eq _ _ (image_tuple3_univ ea eb ec), Set.mem_ofPred_eq, u]
        rfl
      rw [hev, ProbabilityTheory.measureReal_pi_gaussianReal_eq (measurableSet_starStradSet u t)]
      refine starStraddleCost_le (hstar v (tuple3 ea eb ec) fun i => ?_) t
      rw [hv_eq]
      fin_cases i <;> simp [tuple3]
  have hpair_e (e : E) :
      P.real (pairAnyVecEvent G M vec t e) + P.real (pairBothVecEvent G M vec t e) ≤
        if e ∈ M then (27735 / 100000 : ℝ) else 0 := by
    unfold pairAnyVecEvent pairBothVecEvent
    by_cases he : e ∈ M
    · simp only [he, ↓reduceIte]
      set ea := G.outerLow (fun _ => 0) (G.src e) e
      set eb := G.outerHigh (fun _ => 0) (G.src e) e
      set ec := G.outerLow (fun _ => 0) (G.tgt e) e
      set ed := G.outerHigh (fun _ => 0) (G.tgt e) e
      have hs_eq : G.incidenceSet (G.src e) \ {e} = {ea, eb} :=
        (G.outerLow_outerHigh_spec h3 (fun _ => 0) (Or.inl rfl : e ∈ G.incidenceSet (G.src e))).2.1
      have ht_eq : G.incidenceSet (G.tgt e) \ {e} = {ec, ed} :=
        (G.outerLow_outerHigh_spec h3 (fun _ => 0) (Or.inr rfl : e ∈ G.incidenceSet (G.tgt e))).2.1
      have hea : ea ∈ G.incidenceSet (G.src e) := (hs_eq ▸ Set.mem_insert ea {eb}).1
      have heb : eb ∈ G.incidenceSet (G.src e) :=
        (hs_eq ▸ Set.mem_insert_of_mem ea (Set.mem_singleton eb)).1
      have hec : ec ∈ G.incidenceSet (G.tgt e) := (ht_eq ▸ Set.mem_insert ec {ed}).1
      have hed : ed ∈ G.incidenceSet (G.tgt e) :=
        (ht_eq ▸ Set.mem_insert_of_mem ec (Set.mem_singleton ed)).1
      set u : Fin 4 → EuclideanSpace ℝ V := fun i => vec (tuple4 ea eb ec ed i)
      have hany_eq : {ω : V → ℝ | G.PairStraddlesAny (vecScore vec ω) t e} =
          {ω : V → ℝ | WithLp.toLp 2 ω ∈ anyStradSet u t} := by
        ext ω
        simp only [Multigraph.PairStraddlesAny, hs_eq, ht_eq,
          straddlesOn_of_image_eq _ _ (image_tuple4_univ ea eb ec ed), anyStradSet,
          Set.mem_ofPred_eq, u]
        rfl
      have hboth_eq : {ω : V → ℝ | G.PairStraddlesBoth (vecScore vec ω) t e} =
          {ω : V → ℝ | WithLp.toLp 2 ω ∈ bothStradSet u t} := by
        ext ω
        simp only [Multigraph.PairStraddlesBoth, hs_eq, ht_eq,
          straddlesOn_of_image_eq _ _ (image_tuple4_01 ea eb ec ed),
          straddlesOn_of_image_eq _ _ (image_tuple4_23 ea eb ec ed), bothStradSet,
          Set.mem_ofPred_eq, u]
        rfl
      rw [hany_eq, hboth_eq,
        ProbabilityTheory.measureReal_pi_gaussianReal_eq (measurableSet_anyStradSet u t),
        ProbabilityTheory.measureReal_pi_gaussianReal_eq (measurableSet_bothStradSet u t)]
      exact pairCost_le (hpair e (tuple4 ea eb ec ed) hea heb hec hed) t
    · simp [he]
  have hsum_V : ∑ v : V, P.real (unmatchedVecStraddleEvent G M vec t v) ≤
      ((Fintype.card V : ℝ) - 2 * (M.ncard : ℝ)) * (140367 / 1000000) := by
    refine (Finset.sum_le_sum fun v _ => hstar_v v).trans_eq ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hcoe : ((Finset.univ.filter (· ∉ G.matchedVertices M) : Finset V) : Set V) =
        (G.matchedVertices M)ᶜ := by ext v; simp
    have hcard_compl : (Finset.univ.filter (· ∉ G.matchedVertices M)).card =
        (G.matchedVertices M)ᶜ.ncard := by
      rw [← Set.ncard_coe_finset, hcoe]
    have htot := Set.ncard_add_ncard_compl (G.matchedVertices M)
    rw [G.ncard_matchedVertices_eq_two_mul hloop hM, Nat.card_eq_fintype_card, ← hcard_compl]
      at htot
    have htotR : (2 : ℝ) * M.ncard + (Finset.univ.filter (· ∉ G.matchedVertices M)).card =
        Fintype.card V := by exact_mod_cast htot
    linarith
  have hsum_E : (∑ e : E, P.real (pairAnyVecEvent G M vec t e)) +
      (∑ e : E, P.real (pairBothVecEvent G M vec t e)) ≤ (M.ncard : ℝ) * (27735 / 100000) := by
    rw [← Finset.sum_add_distrib]
    refine (Finset.sum_le_sum fun e _ => hpair_e e).trans_eq ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hcoe : ((Finset.univ.filter (· ∈ M) : Finset E) : Set E) = M := by ext e; simp
    rw [← Set.ncard_coe_finset, hcoe]
  have h78R : 7 * (Fintype.card V : ℝ) ≤ 16 * (M.ncard : ℝ) := by
    rw [Nat.card_eq_fintype_card] at h78
    exact_mod_cast h78
  change (∑ v : V, P.real (unmatchedVecStraddleEvent G M vec t v)) +
      (∑ e : E, P.real (pairAnyVecEvent G M vec t e)) +
      (∑ e : E, P.real (pairBothVecEvent G M vec t e)) ≤ _
  unfold pairBoundCoefficient
  linarith

end Cslib.Circuits.Frontier.Gaussian.PairBound

namespace Cslib.Circuits.Frontier

/-! ### Unconditional cubic and degree-`3` layout bounds -/

/-- **Unconditional matched-pair cubic layout bound (`277773 / 2000000 = 0.1388865`).** Every
sufficiently large simple cubic multigraph on `h` vertices has a layout of width at most
`(277773 / 2000000 + ξ) h`. -/
theorem cubicLayoutBound_pairBound :
    CubicLayoutBound Gaussian.PairBound.pairBoundCoefficient := by
  obtain ⟨R, hR⟩ := Gaussian.PairBound.exists_radius_expectedMatchingCostVec_le
  refine Gaussian.cubicLayoutBound_of_matching_vec_mean
    Gaussian.PairBound.pairBoundCoefficient_pos.le fun {ξ} hξ => ⟨R, ?_⟩
  intro V E _ _ G hloop hinj h3
  obtain ⟨M, hM, hm⟩ := hR V E G hloop hinj h3
  refine ⟨M, Gaussian.PairBound.rawEdgeVector G Gaussian.PairBound.rawRatio R, hM,
    Gaussian.PairBound.norm_rawEdgeVector Gaussian.PairBound.rawRatio_pos.le R,
    fun {_ _} he {_} hz => Gaussian.PairBound.rawEdgeVector_apply_eq_zero he hz,
    fun t => (hm t).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)

/-- **Unconditional `5 / 36` cubic layout bound** (`5 / 36 ≈ 0.138888...`). -/
theorem cubicLayoutBound_five_div_thirty_six : CubicLayoutBound (5 / 36) := by
  intro ξ hξ
  obtain ⟨N₀, hN₀⟩ := cubicLayoutBound_pairBound ξ hξ
  refine ⟨N₀, fun V E _ _ G hloop hinj h3 hN => ?_⟩
  obtain ⟨σ, hσ⟩ := hN₀ V E G hloop hinj h3 hN
  refine ⟨σ, hσ.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (by linarith [Gaussian.PairBound.pairBoundCoefficient_lt_five_div_thirty_six])
    (Nat.cast_nonneg _)

/-- **Unconditional matched-pair subcubic layout bound (`A = 277773 / 1000000`).** -/
theorem layoutBound_pairBound :
    LayoutBound 3 (2 * Gaussian.PairBound.pairBoundCoefficient) :=
  LayoutBound.of_cubic Gaussian.PairBound.pairBoundCoefficient_pos.le cubicLayoutBound_pairBound

/-- **Unconditional `5 / 18` subcubic layout bound.** -/
theorem layoutBound_five_div_eighteen : LayoutBound 3 (5 / 18) := by
  have h := LayoutBound.of_cubic (by norm_num) cubicLayoutBound_five_div_thirty_six
  norm_num at h
  exact h

end Cslib.Circuits.Frontier
