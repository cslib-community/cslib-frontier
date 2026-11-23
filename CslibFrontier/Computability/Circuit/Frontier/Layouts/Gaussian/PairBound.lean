/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Correlation
public import CslibFrontier.Computability.Circuit.Frontier.FanInTwo
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.Matching
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.PairBound.Majorant
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.WeightedMatching
public import CslibFrontier.Computability.Circuit.Frontier.Ledger.Unconditional
public import CslibFrontier.Computability.Circuit.Frontier.Linear.Unconditional
public import CslibFrontier.Computability.Circuit.Frontier.Nondeterministic
import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Unconditional matched-pair Gaussian layout bound (`< 5 / 36`) and `4.60n` / `2.80n` lower bounds

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

Plugging `layoutBound_pairBound` (`A = 277773 / 1000000 < 5 / 18`) into the general frontier
reductions yields unconditional fan-in-two lower bounds with gate-count coefficient
`1 + 1 / A = 1277773 / 277773 > 23 / 5 = 4.60` (`≈ 4.600062`) across deterministic, average-case,
nondeterministic, ledger/aggregate, and totally regular linear-map circuits, and quadratic-form /
`hardForm` correlation bounds below `(1 + L) / 2 = 777773 / 277773 > 14 / 5 = 2.80` (`≈ 2.800031`).
The matched-pair Gaussian layout bound and all resulting `4.60n` and `2.80n` lower bounds are
original to this library (note that `hardForm` selects a submatrix-robust matrix via
`Classical.choose`).

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
* `Cslib.Circuits.Frontier.multiaryLowerBound_pairBound`,
  `Cslib.Circuits.Frontier.multiaryLowerBound_23_div_5`,
  `Cslib.Circuits.Frontier.circuitLowerBound_pairBound`,
  `Cslib.Circuits.Frontier.circuitLowerBound_23_div_5`,
  `Cslib.Circuits.Frontier.multiaryAverageCaseBound_pairBound`,
  `Cslib.Circuits.Frontier.multiaryAverageCaseBound_23_div_5`,
  `Cslib.Circuits.Frontier.averageCaseBound_pairBound`,
  `Cslib.Circuits.Frontier.averageCaseBound_23_div_5`: bundled worst-case and average-case bounds
  above `4.60n`.
* `Cslib.Circuits.Frontier.eventually_pairBound_sub_mul_lt_innerSize_of_nondeterministicDecides`,
  `Cslib.Circuits.Frontier.eventually_pairBound_sub_mul_lt_card_of_ledger`,
  `Cslib.Circuits.Frontier.eventually_pairBound_sub_mul_lt_card_of_aggregates`,
  `Cslib.Circuits.Frontier.eventually_pairBound_sub_mul_lt_innerSize_of_isTotallyRegular`:
  unconditional nondeterministic, ledger, aggregate, and linear-map bounds above `4.60n`.
* `Cslib.Circuits.Frontier.eventually_abs_correlation_quadForm_le_pairBound_multiarySize`,
  `Cslib.Circuits.Frontier.exists_eventually_abs_correlation_hardForm_le_14_div_5_multiarySize`:
  unconditional quadratic-form and `hardForm` correlation bounds below `2.80n`.

## References

* [S. Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster
  Exponential Algorithms*][Gaspers2026]
-/

public section

open Filter Asymptotics MeasureTheory ProbabilityTheory Real Set Matrix
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

/-- The matched-pair gate-count coefficient `1277773 / 277773 ≈ 4.600062` strictly exceeds
`23 / 5 = 4.60`. -/
theorem circuitCoefficient_gt_23_div_5 : (23 / 5 : ℝ) < 1277773 / 277773 := by
  norm_num

theorem correlationThreshold_eq :
    1 + 1 / (2 * (2 * pairBoundCoefficient)) = 777773 / 277773 := by
  norm_num [pairBoundCoefficient]

/-- The matched-pair correlation threshold `777773 / 277773 ≈ 2.800031` strictly exceeds
`14 / 5 = 2.80`. -/
theorem correlationThreshold_gt_14_div_5 : (14 / 5 : ℝ) < 777773 / 277773 := by
  norm_num

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
    Gaussian.PairBound.norm_rawEdgeVector Gaussian.PairBound.rawRatio_nonneg R,
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

/-! ### Fan-in-two worst-case and average-case circuit lower bounds (`> 4.60n`) -/

section FanInTwo

universe u v

variable {U : Type u} [Finite U] [Nontrivial U] {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ}

/-- **Matched-pair Gaussian frontier lower bound for fan-in two (`> 4.60006n` multiary gates).**
Every circuit of fan-in at most two deciding a dense rectangle-free family `S_n ⊆ U^n` has more
than `(1277773 / 277773 - ε) n` multiary gates (`arity = 2`; constant and unary gates are free) for
all large `n`. -/
theorem eventually_pairBound_sub_mul_lt_multiarySize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (1277773 / 277773 - ε) * n < c.multiarySize := by
  have h := eventually_lt_multiarySize
    (mul_pos two_pos Gaussian.PairBound.pairBoundCoefficient_pos) layoutBound_pairBound hSK hε
  rwa [Gaussian.PairBound.one_add_inv_two_mul_pairBoundCoefficient] at h

/-- **Matched-pair Gaussian frontier lower bound for fan-in two (`> 4.60006n` inner gates).** -/
theorem eventually_pairBound_sub_mul_lt_innerSize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (1277773 / 277773 - ε) * n < c.innerSize := by
  filter_upwards [eventually_pairBound_sub_mul_lt_multiarySize.{u, v} hSK hε] with n hn
  intro σ I Acc c hfan hS
  exact (hn σ I Acc c hfan hS).trans_le (Nat.cast_le.mpr c.multiarySize_le_innerSize)

/-- **The `(23 / 5 - ε) n = (4.60 - ε) n` multiary gate lower bound for fan-in two.** -/
theorem eventually_23_div_5_sub_mul_lt_multiarySize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (23 / 5 - ε) * n < c.multiarySize := by
  filter_upwards [eventually_pairBound_sub_mul_lt_multiarySize.{u, v} hSK hε] with n hn
  intro σ I Acc c hfan hS
  refine lt_of_le_of_lt ?_ (hn σ I Acc c hfan hS)
  exact mul_le_mul_of_nonneg_right
    (by linarith [Gaussian.PairBound.circuitCoefficient_gt_23_div_5]) (Nat.cast_nonneg n)

/-- **The `(23 / 5 - ε) n = (4.60 - ε) n` inner gate lower bound for fan-in two.** -/
theorem eventually_23_div_5_sub_mul_lt_innerSize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (23 / 5 - ε) * n < c.innerSize := by
  filter_upwards [eventually_23_div_5_sub_mul_lt_multiarySize.{u, v} hSK hε] with n hn
  intro σ I Acc c hfan hS
  exact (hn σ I Acc c hfan hS).trans_le (Nat.cast_le.mpr c.multiarySize_le_innerSize)

/-- **Bundled worst-case multiary claim at `1277773 / 277773 ≈ 4.600062`.** -/
theorem multiaryLowerBound_pairBound : MultiaryLowerBound.{u, v} (1277773 / 277773) := by
  have h := multiaryLowerBound_of_layoutBound.{u, v}
    (mul_pos two_pos Gaussian.PairBound.pairBoundCoefficient_pos) layoutBound_pairBound
  rwa [Gaussian.PairBound.one_add_inv_two_mul_pairBoundCoefficient] at h

/-- **Bundled worst-case multiary claim at `23 / 5 = 4.60`.** -/
theorem multiaryLowerBound_23_div_5 : MultiaryLowerBound.{u, v} (23 / 5) :=
  multiaryLowerBound_pairBound.mono Gaussian.PairBound.circuitCoefficient_gt_23_div_5.le

/-- **Bundled worst-case inner-gate claim at `1277773 / 277773 ≈ 4.600062`.** -/
theorem circuitLowerBound_pairBound : CircuitLowerBound.{u, v} (1277773 / 277773) :=
  multiaryLowerBound_pairBound.circuitLowerBound

/-- **Bundled worst-case inner-gate claim at `23 / 5 = 4.60`.** -/
theorem circuitLowerBound_23_div_5 : CircuitLowerBound.{u, v} (23 / 5) :=
  multiaryLowerBound_23_div_5.circuitLowerBound

/-- **Bundled average-case multiary claim at `1277773 / 277773 ≈ 4.600062`.** -/
theorem multiaryAverageCaseBound_pairBound :
    MultiaryAverageCaseBound.{u, v} (1277773 / 277773) := by
  have h := multiaryAverageCaseBound_of_layoutBound.{u, v}
    (mul_pos two_pos Gaussian.PairBound.pairBoundCoefficient_pos) layoutBound_pairBound
  rwa [Gaussian.PairBound.one_add_inv_two_mul_pairBoundCoefficient] at h

/-- **Bundled average-case multiary claim at `23 / 5 = 4.60`.** -/
theorem multiaryAverageCaseBound_23_div_5 : MultiaryAverageCaseBound.{u, v} (23 / 5) :=
  multiaryAverageCaseBound_pairBound.mono Gaussian.PairBound.circuitCoefficient_gt_23_div_5.le

/-- **Bundled average-case inner-gate claim at `1277773 / 277773 ≈ 4.600062`.** -/
theorem averageCaseBound_pairBound : AverageCaseBound.{u, v} (1277773 / 277773) :=
  multiaryAverageCaseBound_pairBound.averageCaseBound

/-- **Bundled average-case inner-gate claim at `23 / 5 = 4.60`.** -/
theorem averageCaseBound_23_div_5 : AverageCaseBound.{u, v} (23 / 5) :=
  multiaryAverageCaseBound_23_div_5.averageCaseBound

/-! ### Nondeterministic fan-in-two circuit lower bounds (`> 4.60n`) -/

/-- **Matched-pair Gaussian lower bound for nondeterministic circuits of fan-in two.** -/
theorem eventually_pairBound_sub_mul_lt_innerSize_of_nondeterministicDecides
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost 2 → c.NondeterministicDecides I Acc (S n) →
        (1277773 / 277773 - ε) * n < c.innerSize := by
  have h := eventually_lt_innerSize_of_nondeterministicDecides
    (mul_pos two_pos Gaussian.PairBound.pairBoundCoefficient_pos) layoutBound_pairBound hSK hε
  rwa [Gaussian.PairBound.one_add_inv_two_mul_pairBoundCoefficient] at h

/-- **The `(23 / 5 - ε) n = (4.60 - ε) n` lower bound for nondeterministic circuits of fan-in
two.** -/
theorem eventually_23_div_5_sub_mul_lt_innerSize_of_nondeterministicDecides
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost 2 → c.NondeterministicDecides I Acc (S n) →
        (23 / 5 - ε) * n < c.innerSize := by
  filter_upwards
    [eventually_pairBound_sub_mul_lt_innerSize_of_nondeterministicDecides.{u, v} hSK hε] with n hn
  intro k σ I Acc c hfan hS
  refine lt_of_le_of_lt ?_ (hn k σ I Acc c hfan hS)
  exact mul_le_mul_of_nonneg_right
    (by linarith [Gaussian.PairBound.circuitCoefficient_gt_23_div_5]) (Nat.cast_nonneg n)

end FanInTwo

/-! ### Quadratic-form and `hardForm` correlation bounds (`< 2.80n`) -/

section Correlation

universe v

private theorem pairBound_rate_eq (c : ℝ) :
    (1 + 1 / (2 * (2 * Gaussian.PairBound.pairBoundCoefficient)) - c) /
        (2 * (1 + 1 / (2 * Gaussian.PairBound.pairBoundCoefficient))) =
      (777773 / 277773 - c) / (2 * (1277773 / 277773)) := by
  rw [Gaussian.PairBound.correlationThreshold_eq,
    Gaussian.PairBound.one_add_inv_two_mul_pairBoundCoefficient]

/-- **Exponentially small quadratic-form correlation below `(777773 / 277773) n` (`≈ 2.800031n`)
multiary gates.** -/
theorem eventually_abs_correlation_quadForm_le_pairBound_multiarySize {c γ : ℝ} (hc : 1 / 2 ≤ c)
    (hγ : γ < (777773 / 277773 - c) / (2 * (1277773 / 277773)))
    (Q : ∀ n, Matrix (Fin n) (Fin n) (ZMod 2)) (e : ℕ → ℝ)
    (he : e =o[atTop] fun n => (n : ℝ))
    (hQ : ∀ᶠ n in atTop, ∀ U : Set (Fin n), U.ncard = n / 2 →
      ((n / 2 : ℕ) : ℝ) ≤ (Q n + (Q n)ᵀ).cutRank U + e n) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (C : Circuit σ n 1), C.FanInAtMost 2 → (C.multiarySize : ℝ) ≤ c * n →
        |correlation {x | BitString.quadForm (Q n) x} {x | C.eval I x 0 ∈ Acc}| ≤
          (2 : ℝ) ^ (-γ * n) :=
  eventually_abs_correlation_quadForm_le_of_isLittleO_multiarySize
    (mul_pos two_pos Gaussian.PairBound.pairBoundCoefficient_pos) layoutBound_pairBound hc
    (by rwa [pairBound_rate_eq]) Q e he hQ

/-- **Exponentially small quadratic-form correlation below `(777773 / 277773) n` inner gates.** -/
theorem eventually_abs_correlation_quadForm_le_pairBound {c γ : ℝ} (hc : 1 / 2 ≤ c)
    (hγ : γ < (777773 / 277773 - c) / (2 * (1277773 / 277773)))
    (Q : ∀ n, Matrix (Fin n) (Fin n) (ZMod 2)) (e : ℕ → ℝ)
    (he : e =o[atTop] fun n => (n : ℝ))
    (hQ : ∀ᶠ n in atTop, ∀ U : Set (Fin n), U.ncard = n / 2 →
      ((n / 2 : ℕ) : ℝ) ≤ (Q n + (Q n)ᵀ).cutRank U + e n) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (C : Circuit σ n 1), C.FanInAtMost 2 → (C.innerSize : ℝ) ≤ c * n →
        |correlation {x | BitString.quadForm (Q n) x} {x | C.eval I x 0 ∈ Acc}| ≤
          (2 : ℝ) ^ (-γ * n) := by
  filter_upwards
    [eventually_abs_correlation_quadForm_le_pairBound_multiarySize.{v} hc hγ Q e he hQ]
    with n hn σ I Acc C hfan hsize
  exact hn σ I Acc C hfan ((Nat.cast_le.mpr C.multiarySize_le_innerSize).trans hsize)

/-- **Exponentially small correlation with `hardForm n` (chosen via `Classical.choose`) below
`(777773 / 277773) n` multiary gates.** -/
theorem eventually_abs_correlation_hardForm_le_pairBound_multiarySize {c γ : ℝ} (hc : 1 / 2 ≤ c)
    (hγ : γ < (777773 / 277773 - c) / (2 * (1277773 / 277773))) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (C : Circuit σ n 1), C.FanInAtMost 2 → (C.multiarySize : ℝ) ≤ c * n →
        |correlation {x | hardForm n x} {x | C.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) :=
  eventually_abs_correlation_quadForm_le_pairBound_multiarySize hc hγ hardMatrix _
    isLittleO_hardDeficiency (Eventually.of_forall half_le_cutRank_hardMatrix_add)

/-- **Exponentially small correlation with `hardForm n` (chosen via `Classical.choose`) below
`(777773 / 277773) n` inner gates.** -/
theorem eventually_abs_correlation_hardForm_le_pairBound {c γ : ℝ} (hc : 1 / 2 ≤ c)
    (hγ : γ < (777773 / 277773 - c) / (2 * (1277773 / 277773))) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (C : Circuit σ n 1), C.FanInAtMost 2 → (C.innerSize : ℝ) ≤ c * n →
        |correlation {x | hardForm n x} {x | C.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) := by
  filter_upwards [eventually_abs_correlation_hardForm_le_pairBound_multiarySize.{v} hc hγ]
    with n hn σ I Acc C hfan hsize
  exact hn σ I Acc C hfan ((Nat.cast_le.mpr C.multiarySize_le_innerSize).trans hsize)

/-- **Every multiary gate coefficient `c < 777773 / 277773` (`≈ 2.800031`).** -/
theorem exists_eventually_abs_correlation_hardForm_le_of_lt_pairBound_multiarySize {c : ℝ}
    (hc : c < 777773 / 277773) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool)
      (Acc : Set Bool) (C : Circuit σ n 1), C.FanInAtMost 2 → (C.multiarySize : ℝ) ≤ c * n →
        |correlation {x | hardForm n x} {x | C.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) := by
  set c' := max c (1 / 2)
  have hc' : c' < 777773 / 277773 := max_lt hc (by norm_num)
  have hc'_lo : 1 / 2 ≤ c' := le_max_right c (1 / 2)
  set r := (777773 / 277773 - c') / (2 * (1277773 / 277773))
  have hr : 0 < r := div_pos (by linarith) (by norm_num)
  refine ⟨r / 2, by positivity, ?_⟩
  filter_upwards [eventually_abs_correlation_hardForm_le_pairBound_multiarySize.{v}
    hc'_lo (γ := r / 2) (half_lt_self hr)] with n hn σ I Acc C hfan hsize
  exact hn σ I Acc C hfan
    (hsize.trans (mul_le_mul_of_nonneg_right (le_max_left c _) (Nat.cast_nonneg n)))

/-- **Every inner-gate coefficient `c < 777773 / 277773` (`≈ 2.800031`).** -/
theorem exists_eventually_abs_correlation_hardForm_le_of_lt_pairBound {c : ℝ}
    (hc : c < 777773 / 277773) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool)
      (Acc : Set Bool) (C : Circuit σ n 1), C.FanInAtMost 2 → (C.innerSize : ℝ) ≤ c * n →
        |correlation {x | hardForm n x} {x | C.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) := by
  obtain ⟨γ, hγ, hn⟩ :=
    exists_eventually_abs_correlation_hardForm_le_of_lt_pairBound_multiarySize.{v} hc
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [hn] with n hn' σ I Acc C hfan hsize
  exact hn' σ I Acc C hfan ((Nat.cast_le.mpr C.multiarySize_le_innerSize).trans hsize)

/-- **Exponentially small correlation with `hardForm n` at `14 / 5 * n = 2.80 n` multiary gates.**
-/
theorem exists_eventually_abs_correlation_hardForm_le_14_div_5_multiarySize :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool)
      (Acc : Set Bool) (C : Circuit σ n 1), C.FanInAtMost 2 →
        (C.multiarySize : ℝ) ≤ 14 / 5 * n →
          |correlation {x | hardForm n x} {x | C.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) :=
  exists_eventually_abs_correlation_hardForm_le_of_lt_pairBound_multiarySize
    Gaussian.PairBound.correlationThreshold_gt_14_div_5

/-- **Exponentially small correlation with `hardForm n` at `14 / 5 * n = 2.80 n` inner gates.** -/
theorem exists_eventually_abs_correlation_hardForm_le_14_div_5 :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool)
      (Acc : Set Bool) (C : Circuit σ n 1), C.FanInAtMost 2 →
        (C.innerSize : ℝ) ≤ 14 / 5 * n →
          |correlation {x | hardForm n x} {x | C.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) :=
  exists_eventually_abs_correlation_hardForm_le_of_lt_pairBound
    Gaussian.PairBound.correlationThreshold_gt_14_div_5

end Correlation

/-! ### Ledger and aggregate circuit lower bounds (`> 4.60n`) -/

section Ledger

universe u v w

variable {U : Type u} [Finite U] [Nontrivial U] {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ}

/-- **Matched-pair Gaussian frontier lower bound with a ledger (`> 4.60006n`).** -/
theorem eventually_pairBound_sub_mul_lt_card_of_ledger
    (hSK : DenseRectangleFree S K)
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1) (special : Fin c.size → Prop) [DecidablePred special] (M : Type w)
      [CommMonoid M] [Finite M],
        (∀ g, ¬special g → σ.Arity (c.program.lines g).op ≤ 2) →
        Ledger special c.program I M → Real.log (Nat.card M) ≤ β n → c.Decides I Acc (S n) →
          (1277773 / 277773 - ε) * n <
            (c.program.innerGates.filter fun g => ¬special g).card := by
  have h := eventually_lt_mul_card_of_ledger.{u, v, w} (r := 2) le_rfl
    (mul_pos two_pos Gaussian.PairBound.pairBoundCoefficient_pos) layoutBound_pairBound hSK hβ hε
  rw [Gaussian.PairBound.one_add_inv_two_mul_pairBoundCoefficient] at h
  filter_upwards [h] with n hn σ I Acc c special _ M _ _ hfan hled hM hdec
  simpa only [Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, one_mul] using
    hn σ I Acc c special M hfan hled hM hdec

/-- **Matched-pair Gaussian frontier lower bound with aggregate gates (`> 4.60006n`).** -/
theorem eventually_pairBound_sub_mul_lt_card_of_aggregates
    (hSK : DenseRectangleFree S K)
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1) (special : Fin c.size → Prop) [DecidablePred special] (T : Type w)
      [CommMonoid T] [Finite T],
        (∀ g, ¬special g → σ.Arity (c.program.lines g).op ≤ 2) →
        (∀ g, special g → Aggregates (I (c.program.lines g).op) T) →
        Nat.card {g // special g} * Real.log (Nat.card T) ≤ β n →
        c.Decides I Acc (S n) →
          (1277773 / 277773 - ε) * n <
            (c.program.innerGates.filter fun g => ¬special g).card := by
  have h := eventually_lt_mul_card_of_aggregates.{u, v, w} (r := 2) le_rfl
    (mul_pos two_pos Gaussian.PairBound.pairBoundCoefficient_pos) layoutBound_pairBound hSK hβ hε
  rw [Gaussian.PairBound.one_add_inv_two_mul_pairBoundCoefficient] at h
  filter_upwards [h] with n hn σ I Acc c special _ T _ _ hfan hagg hT hdec
  simpa only [Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, one_mul] using
    hn σ I Acc c special T hfan hagg hT hdec

/-- **The `(23 / 5 - ε) n = (4.60 - ε) n` frontier lower bound with a ledger.** -/
theorem eventually_23_div_5_sub_mul_lt_card_of_ledger
    (hSK : DenseRectangleFree S K)
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1) (special : Fin c.size → Prop) [DecidablePred special] (M : Type w)
      [CommMonoid M] [Finite M],
        (∀ g, ¬special g → σ.Arity (c.program.lines g).op ≤ 2) →
        Ledger special c.program I M → Real.log (Nat.card M) ≤ β n → c.Decides I Acc (S n) →
          (23 / 5 - ε) * n < (c.program.innerGates.filter fun g => ¬special g).card := by
  filter_upwards [eventually_pairBound_sub_mul_lt_card_of_ledger.{u, v, w} hSK hβ hε] with
    n hn σ I Acc c special _ M _ _ hfan hled hM hdec
  refine lt_of_le_of_lt ?_ (hn σ I Acc c special M hfan hled hM hdec)
  exact mul_le_mul_of_nonneg_right
    (by linarith [Gaussian.PairBound.circuitCoefficient_gt_23_div_5]) (Nat.cast_nonneg n)

/-- **The `(23 / 5 - ε) n = (4.60 - ε) n` frontier lower bound with aggregate gates.** -/
theorem eventually_23_div_5_sub_mul_lt_card_of_aggregates
    (hSK : DenseRectangleFree S K)
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1) (special : Fin c.size → Prop) [DecidablePred special] (T : Type w)
      [CommMonoid T] [Finite T],
        (∀ g, ¬special g → σ.Arity (c.program.lines g).op ≤ 2) →
        (∀ g, special g → Aggregates (I (c.program.lines g).op) T) →
        Nat.card {g // special g} * Real.log (Nat.card T) ≤ β n →
        c.Decides I Acc (S n) →
          (23 / 5 - ε) * n < (c.program.innerGates.filter fun g => ¬special g).card := by
  filter_upwards [eventually_pairBound_sub_mul_lt_card_of_aggregates.{u, v, w} hSK hβ hε] with
    n hn σ I Acc c special _ T _ _ hfan hagg hT hdec
  refine lt_of_le_of_lt ?_ (hn σ I Acc c special T hfan hagg hT hdec)
  exact mul_le_mul_of_nonneg_right
    (by linarith [Gaussian.PairBound.circuitCoefficient_gt_23_div_5]) (Nat.cast_nonneg n)

end Ledger

/-! ### Linear maps and Cauchy matrices (`> 4.60 N`) -/

section Linear

universe u v

/-- **Matched-pair Gaussian lower bound for totally regular linear maps (`> 4.60006 N`).** -/
theorem eventually_pairBound_sub_mul_lt_innerSize_of_isTotallyRegular {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] (σ : Signature.{v}) (I : Interpretation σ F)
      (M : Matrix (Fin N) (Fin N) F) (c : Circuit σ N N), M.IsTotallyRegular →
        c.FanInAtMost 2 → c.Computes I (fun x => M *ᵥ x) → c.LinearCapacity I →
          (1277773 / 277773 - ε) * N < c.innerSize := by
  have h := eventually_lt_mul_innerSize_of_isTotallyRegular.{u, v} (r := 2) le_rfl
    (mul_pos two_pos Gaussian.PairBound.pairBoundCoefficient_pos) layoutBound_pairBound hε
  rw [Gaussian.PairBound.one_add_inv_two_mul_pairBoundCoefficient] at h
  filter_upwards [h] with N hN F _ σ I M c hM hfan hc hcap
  simpa only [Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, one_mul] using
    hN F σ I M c hM hfan hc hcap

/-- **Matched-pair Gaussian lower bound for linear maps over finite fields (`> 4.60006 N`).** -/
theorem eventually_pairBound_sub_mul_lt_innerSize_of_isTotallyRegular_finite {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [Finite F] (σ : Signature.{v})
      (I : Interpretation σ F) (M : Matrix (Fin N) (Fin N) F) (c : Circuit σ N N),
        M.IsTotallyRegular → c.FanInAtMost 2 → c.Computes I (fun x => M *ᵥ x) →
          (1277773 / 277773 - ε) * N < c.innerSize := by
  have h := eventually_lt_mul_innerSize_of_isTotallyRegular_finite.{u, v} (r := 2) le_rfl
    (mul_pos two_pos Gaussian.PairBound.pairBoundCoefficient_pos) layoutBound_pairBound hε
  rw [Gaussian.PairBound.one_add_inv_two_mul_pairBoundCoefficient] at h
  filter_upwards [h] with N hN F _ _ σ I M c hM hfan hc
  simpa only [Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, one_mul] using
    hN F σ I M c hM hfan hc

/-- **Matched-pair Gaussian lower bound for linear maps over infinite fields (`> 4.60006 N`).** -/
theorem eventually_pairBound_sub_mul_lt_innerSize_of_isTotallyRegular_isPolynomial
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [Infinite F] (σ : Signature.{v})
      (I : Interpretation σ F), I.IsPolynomial → ∀ (M : Matrix (Fin N) (Fin N) F)
        (c : Circuit σ N N), M.IsTotallyRegular → c.FanInAtMost 2 →
          c.Computes I (fun x => M *ᵥ x) →
            (1277773 / 277773 - ε) * N < c.innerSize := by
  have h := eventually_lt_mul_innerSize_of_isTotallyRegular_isPolynomial.{u, v} (r := 2) le_rfl
    (mul_pos two_pos Gaussian.PairBound.pairBoundCoefficient_pos) layoutBound_pairBound hε
  rw [Gaussian.PairBound.one_add_inv_two_mul_pairBoundCoefficient] at h
  filter_upwards [h] with N hN F _ _ σ I hpoly M c hM hfan hc
  simpa only [Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, one_mul] using
    hN F σ I hpoly M c hM hfan hc

/-- **Arithmetic circuits for the Cauchy maps (`> 4.60006 N`).** -/
theorem eventually_pairBound_sub_mul_lt_innerSize_arith_cauchyNat {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [CharZero F] (c : Circuit (arithSignature F) N N),
      c.Computes (arithInterpretation F) (fun x => cauchyNat F N *ᵥ x) →
        (1277773 / 277773 - ε) * N < c.innerSize := by
  filter_upwards
    [eventually_pairBound_sub_mul_lt_innerSize_of_isTotallyRegular_isPolynomial.{u, u} hε] with
    N hN F _ _ c hc
  exact hN F _ _ isPolynomial_arithInterpretation _ c (isTotallyRegular_cauchyNat N)
    c.fanInAtMost_two_arith hc

/-- **The Cauchy maps over prime fields (`> 4.60006 N`).** -/
theorem eventually_pairBound_sub_mul_lt_innerSize_cauchyNat_zmod {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (q : ℕ) [Fact q.Prime], 2 * N ≤ q → ∀ (σ : Signature.{v})
      (I : Interpretation σ (ZMod q)) (c : Circuit σ N N), c.FanInAtMost 2 →
        c.Computes I (fun x => cauchyNat (ZMod q) N *ᵥ x) →
          (1277773 / 277773 - ε) * N < c.innerSize := by
  filter_upwards
    [eventually_pairBound_sub_mul_lt_innerSize_of_isTotallyRegular_finite.{0, v} hε] with
    N hN q _ hq σ I c hfan hc
  have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  exact hN (ZMod q) σ I _ c (isTotallyRegular_cauchyNat_zmod hq) hfan hc

/-- **The `(23 / 5 - ε) N = (4.60 - ε) N` lower bound for linear maps over finite fields.** -/
theorem eventually_23_div_5_sub_mul_lt_innerSize_of_isTotallyRegular_finite {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [Finite F] (σ : Signature.{v})
      (I : Interpretation σ F) (M : Matrix (Fin N) (Fin N) F) (c : Circuit σ N N),
        M.IsTotallyRegular → c.FanInAtMost 2 → c.Computes I (fun x => M *ᵥ x) →
          (23 / 5 - ε) * N < c.innerSize := by
  filter_upwards
    [eventually_pairBound_sub_mul_lt_innerSize_of_isTotallyRegular_finite.{u, v} hε] with
    N hN F _ _ σ I M c hM hfan hc
  refine lt_of_le_of_lt ?_ (hN F σ I M c hM hfan hc)
  exact mul_le_mul_of_nonneg_right
    (by linarith [Gaussian.PairBound.circuitCoefficient_gt_23_div_5]) (Nat.cast_nonneg N)

/-- **Arithmetic circuits for the Cauchy maps (`4.60 N`).** -/
theorem eventually_23_div_5_sub_mul_lt_innerSize_arith_cauchyNat {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [CharZero F] (c : Circuit (arithSignature F) N N),
      c.Computes (arithInterpretation F) (fun x => cauchyNat F N *ᵥ x) →
        (23 / 5 - ε) * N < c.innerSize := by
  filter_upwards [eventually_pairBound_sub_mul_lt_innerSize_arith_cauchyNat.{u} hε] with
    N hN F _ _ c hc
  refine lt_of_le_of_lt ?_ (hN F c hc)
  exact mul_le_mul_of_nonneg_right
    (by linarith [Gaussian.PairBound.circuitCoefficient_gt_23_div_5]) (Nat.cast_nonneg N)

/-- **The Cauchy maps over prime fields (`4.60 N`).** -/
theorem eventually_23_div_5_sub_mul_lt_innerSize_cauchyNat_zmod {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (q : ℕ) [Fact q.Prime], 2 * N ≤ q → ∀ (σ : Signature.{v})
      (I : Interpretation σ (ZMod q)) (c : Circuit σ N N), c.FanInAtMost 2 →
        c.Computes I (fun x => cauchyNat (ZMod q) N *ᵥ x) →
          (23 / 5 - ε) * N < c.innerSize := by
  filter_upwards [eventually_pairBound_sub_mul_lt_innerSize_cauchyNat_zmod.{v} hε] with
    N hN q _ hq σ I c hfan hc
  refine lt_of_le_of_lt ?_ (hN q hq σ I c hfan hc)
  exact mul_le_mul_of_nonneg_right
    (by linarith [Gaussian.PairBound.circuitCoefficient_gt_23_div_5]) (Nat.cast_nonneg N)

end Linear

end Cslib.Circuits.Frontier
