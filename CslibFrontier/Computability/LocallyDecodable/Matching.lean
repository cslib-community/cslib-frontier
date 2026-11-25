/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LocallyDecodable.Smoothing
public import CslibFrontier.Probability.PMF
public import Mathlib.Data.Fintype.Pi
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.Product
import Mathlib.Tactic.Linarith

/-!
# Hypergraph matching extraction from smooth decoders

Every non-adaptive `(q, c, ε)` smooth decoder for a code `C : (ι → Bool) → P → Γ` induces, for each
message bit `i`, a `q`-bounded hypergraph matching of pairwise-disjoint nonempty query sets whose
deterministic predictors each recover `x i` with advantage at least `ε / 2` over a uniformly random
message `x` [KatzTrevisan2000], [Yekhanin2012].

The argument filters the supported query plans of the decoder to the *good* plans whose average
decoding accuracy over uniform messages is at least `1 / 2 + η` (for `0 < η < ε`). By an averaging
bound, good plans occur with probability at least `2 (ε - η)`, and every good plan queries at least
one position (a zero-query plan has accuracy exactly `1 / 2` on a uniform bit). Any maximal
matching `M` in the resulting hypergraph of good query sets hits every good plan, so its vertex set
`V(M)` (of size at most `q |M|`) is hit with probability at least `2 (ε - η)`. Smoothness bounds
each vertex's query probability by `c / |P|`, yielding `2 (ε - η) |P| ≤ q c |M|`. Setting
`η = ε / 2` gives `ε |P| ≤ q c |M|`.

Combined with `Cslib.Code.isSmoothDecoder_mask_nonadaptivePlan` and
`Cslib.Code.IsLocalDecoder.isSmoothDecoder_adaptive`, this extracts linear-size decoding matchings
both from non-adaptive local decoders (with no advantage loss) and from arbitrary adaptive local
decoders (with the `|Γ| ^ -(q - 1)` reduction factor).

## Main definitions

* `Cslib.Code.DecodingMatching`: a pairwise-disjoint collection of nonempty subsets of `P` of size
  at most `q`, each equipped with a deterministic predictor for bit `i` of accuracy `1 / 2 + η`.

## Main results

* `Cslib.Code.exists_decodingMatching_of_nonadaptivePlan`: hypergraph matching extraction from a
  smooth distribution over non-adaptive query plans.
* `Cslib.Code.IsSmoothDecoder.exists_decodingMatching_of_nonadaptivePlan`,
  `Cslib.Code.IsSmoothDecoder.exists_decodingMatching_of_nonadaptive`: extraction from non-adaptive
  smooth decoders.
* `Cslib.Code.IsLocalDecoder.exists_decodingMatching_of_nonadaptivePlan`,
  `Cslib.Code.IsLocalDecoder.exists_decodingMatching`: extraction from non-adaptive and general
  adaptive local decoders.

## References

* [J. Katz, L. Trevisan, *On the efficiency of local decoding procedures for error-correcting
  codes*][KatzTrevisan2000]
* [S. Yekhanin, *Locally decodable codes*][Yekhanin2012]
-/

public section

open Finset
open scoped BigOperators ENNReal

namespace Cslib.Code

open Probability

variable {ι P Γ : Type}

/-- A decoding matching for message bit `i` of `C : (ι → Bool) → P → Γ`: a pairwise-disjoint
family `edges` of nonempty subsets of `P` of size at most `q`, together with a deterministic
predictor for each edge `e` that reads only `C x` restricted to `e` and recovers `x i` with
probability at least `1 / 2 + η` over a uniformly random message `x`. -/
structure DecodingMatching [Fintype ι] [DecidableEq ι] (C : (ι → Bool) → P → Γ) (i : ι) (q : ℕ)
    (η : ℝ) where
  /-- Pairwise-disjoint query sets (hyperedges). -/
  edges : Finset (Finset P)
  /-- The hyperedges are pairwise disjoint. -/
  pairwiseDisjoint : (edges : Set (Finset P)).PairwiseDisjoint id
  /-- Every hyperedge is nonempty. -/
  nonempty_of_mem : ∀ e ∈ edges, e.Nonempty
  /-- Every hyperedge has cardinality at most `q`. -/
  card_le_of_mem : ∀ e ∈ edges, e.card ≤ q
  /-- Deterministic predictor for each hyperedge, reading only the codeword on that edge. -/
  predict : (e : Finset P) → (e → Γ) → Bool
  /-- Each hyperedge predictor recovers bit `i` with probability at least `1 / 2 + η` on a
  uniformly random message. -/
  correct : ∀ e ∈ edges,
    1 / 2 + η ≤ ((PMF.uniformOfFintype (ι → Bool)).toOuterMeasure
      {x | predict e (e.restrict (C x)) = x i}).toReal

/-- **Maximal matching in a finite hypergraph**: every finite family `H` of nonempty finite sets
contains a pairwise-disjoint subfamily `M ⊆ H` such that every `e ∈ H` meets some vertex of
`M.biUnion id`. -/
private theorem exists_maximal_matching [DecidableEq P] (H : Finset (Finset P))
    (hne : ∀ e ∈ H, e.Nonempty) :
    ∃ M ⊆ H, (M : Set (Finset P)).PairwiseDisjoint id ∧
      ∀ e ∈ H, ∃ j ∈ M.biUnion id, j ∈ e := by
  classical
  let matchings : Finset (Finset (Finset P)) :=
    H.powerset.filter fun M => (M : Set (Finset P)).PairwiseDisjoint id
  have hmem0 : (∅ : Finset (Finset P)) ∈ matchings := by
    simp [matchings]
  obtain ⟨M, hM, hmax⟩ := matchings.exists_max_image Finset.card ⟨∅, hmem0⟩
  simp only [matchings, mem_filter, mem_powerset] at hM
  refine ⟨M, hM.1, hM.2, fun e he => ?_⟩
  by_contra hmiss
  push Not at hmiss
  have hdisj : ∀ e' ∈ M, Disjoint e e' := fun e' he' =>
    Finset.disjoint_left.mpr fun j hje hje' =>
      hmiss j (mem_biUnion.mpr ⟨e', he', hje'⟩) hje
  have heM : e ∉ M := by
    intro heM
    obtain ⟨j, hj⟩ := hne e he
    exact Finset.disjoint_left.mp (hdisj e heM) hj hj
  have hpd : ((insert e M : Finset (Finset P)) : Set (Finset P)).PairwiseDisjoint id := by
    rw [coe_insert]
    exact hM.2.insert fun e' he' _ => hdisj e' he'
  have hins : insert e M ∈ matchings := by
    simp only [matchings, mem_filter, mem_powerset]
    exact ⟨Finset.insert_subset he hM.1, hpd⟩
  have hle := hmax (insert e M) hins
  rw [Finset.card_insert_of_notMem heM] at hle
  omega

/-- A constant bit equals a uniformly random coordinate `x i` with probability `1 / 2`. -/
private theorem toReal_uniformOfFintype_eq_const [Fintype ι] [DecidableEq ι] (i : ι) (b : Bool) :
    ((PMF.uniformOfFintype (ι → Bool)).toOuterMeasure {x | b = x i}).toReal = 1 / 2 := by
  have hU : PMF.uniformOfFintype (ι → Bool) =
      Probability.PMF.pi fun _ : ι => PMF.uniformOfFintype Bool := by
    ext x
    simp [PMF.uniformOfFintype_apply, Probability.PMF.pi_apply, ENNReal.inv_pow]
  have hmap : (PMF.uniformOfFintype (ι → Bool)).map (fun x => x i) = PMF.uniformOfFintype Bool := by
    rw [hU, Probability.PMF.pi_map_eval]
  have hev : (PMF.uniformOfFintype (ι → Bool)).toOuterMeasure {x | b = x i} =
      ((PMF.uniformOfFintype (ι → Bool)).map fun x => x i) b := by
    rw [PMF.toOuterMeasure_apply, PMF.map_apply]
    refine tsum_congr fun x => ?_
    by_cases hx : b = x i <;> simp [hx]
  rw [hev, hmap, PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat, one_div]

/-- A non-adaptive plan with empty query set has accuracy exactly `1 / 2` on a uniform bit. -/
private theorem acc_eq_half_of_querySet_eq_empty [Fintype ι] [DecidableEq ι] [DecidableEq P]
    {C : (ι → Bool) → P → Γ} {q : ℕ} (i : ι) (plan : NonadaptivePlan P Γ q)
    (he : plan.querySet = ∅) :
    ((PMF.uniformOfFintype (ι → Bool)).toOuterMeasure {x | plan.eval (C x) = x i}).toReal =
      1 / 2 := by
  have hconst (x : ι → Bool) : plan.eval (C x) = plan.eval (C fun _ => false) :=
    plan.eval_eq_of_eqOn fun j hj => by rw [he] at hj; exact absurd hj (notMem_empty j)
  simp_rw [hconst]
  exact toReal_uniformOfFintype_eq_const i (plan.eval (C fun _ => false))

/-- **Hypergraph matching extraction from a smooth non-adaptive plan distribution**
[KatzTrevisan2000], [Yekhanin2012]: if a distribution `planLaw` over `q`-query non-adaptive plans
recovers bit `i` of a uniform message with probability at least `1 / 2 + ε` and queries each
position with probability at most `c / |P|`, then for every threshold `0 < η` there is a
`DecodingMatching` for bit `i` with accuracy `1 / 2 + η` and `2 (ε - η) |P| ≤ q c |M|`. -/
theorem exists_decodingMatching_of_nonadaptivePlan [Fintype ι] [DecidableEq ι] [Fintype P]
    [DecidableEq P] [Finite Γ] {C : (ι → Bool) → P → Γ} {q : ℕ} {c ε η : ℝ} (i : ι)
    (planLaw : PMF (NonadaptivePlan P Γ q)) (hη : 0 < η)
    (hacc : 1 / 2 + ε ≤ ∑' plan, (planLaw plan).toReal *
      ((PMF.uniformOfFintype (ι → Bool)).toOuterMeasure {x | plan.eval (C x) = x i}).toReal)
    (hsmooth : ∀ j : P, (planLaw.toOuterMeasure {plan | j ∈ plan.querySet}).toReal ≤
      c / Fintype.card P) :
    ∃ M : DecodingMatching C i q η,
      2 * (ε - η) * Fintype.card P ≤ q * c * M.edges.card := by
  classical
  let := Fintype.ofFinite (NonadaptivePlan P Γ q)
  let acc (plan : NonadaptivePlan P Γ q) : ℝ :=
    ((PMF.uniformOfFintype (ι → Bool)).toOuterMeasure {x | plan.eval (C x) = x i}).toReal
  let good : Set (NonadaptivePlan P Γ q) := {plan | 1 / 2 + η ≤ acc plan}
  -- Step 1: good plans have total probability at least `2 (ε - η)`.
  have hgood_prob : 2 * (ε - η) ≤ (planLaw.toOuterMeasure good).toReal := by
    rw [tsum_fintype] at hacc
    have hpt (plan : NonadaptivePlan P Γ q) :
        acc plan ≤ (1 / 2 + η) + (1 / 2) * (if plan ∈ good then (1 : ℝ) else 0) := by
      by_cases h : plan ∈ good
      · rw [ite_eq_left h, mul_one]
        have hle : acc plan ≤ 1 := by
          have := ENNReal.toReal_mono ENNReal.one_ne_top
            (Probability.PMF.toOuterMeasure_le_one (PMF.uniformOfFintype (ι → Bool))
              {x | plan.eval (C x) = x i})
          simpa only [ENNReal.toReal_one] using this
        linarith
      · rw [ite_eq_right h, mul_zero, add_zero]
        exact le_of_not_ge h
    have havg : ∑ plan, (planLaw plan).toReal * acc plan ≤
        (1 / 2 + η) + (1 / 2) * (planLaw.toOuterMeasure good).toReal := by
      calc ∑ plan, (planLaw plan).toReal * acc plan
          ≤ ∑ plan, (planLaw plan).toReal *
              ((1 / 2 + η) + (1 / 2) * (if plan ∈ good then (1 : ℝ) else 0)) :=
            Finset.sum_le_sum fun plan _ =>
              mul_le_mul_of_nonneg_left (hpt plan) ENNReal.toReal_nonneg
        _ = (1 / 2 + η) * (∑ plan, (planLaw plan).toReal) +
              (1 / 2) * (∑ plan, (planLaw plan).toReal * if plan ∈ good then (1 : ℝ) else 0) := by
            simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
            congr 1
            · ring
            · rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun plan _ => by ring
        _ = (1 / 2 + η) + (1 / 2) * (planLaw.toOuterMeasure good).toReal := by
            rw [Probability.PMF.sum_toReal, mul_one,
              ← Probability.PMF.toOuterMeasure_toReal_eq_sum_ite]
    change 1 / 2 + ε ≤ ∑ plan, (planLaw plan).toReal * acc plan at hacc
    linarith
  -- Step 2: form the hypergraph `H` of query sets of supported good plans.
  let goodPlans : Finset (NonadaptivePlan P Γ q) :=
    Finset.univ.filter fun plan => plan ∈ good ∧ plan ∈ planLaw.support
  let H : Finset (Finset P) := goodPlans.image NonadaptivePlan.querySet
  have hH_ne : ∀ e ∈ H, e.Nonempty := by
    intro e he
    obtain ⟨plan, hplan, rfl⟩ := mem_image.mp he
    simp only [goodPlans, mem_filter, mem_univ, true_and] at hplan
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hhalf := acc_eq_half_of_querySet_eq_empty (C := C) i plan hemp
    have hge : 1 / 2 + η ≤ acc plan := hplan.1
    change 1 / 2 + η ≤ _ at hge
    linarith
  have hH_card : ∀ e ∈ H, e.card ≤ q := by
    intro e he
    obtain ⟨plan, _, rfl⟩ := mem_image.mp he
    exact plan.card_querySet_le
  -- Step 3: extract a maximal matching `M ⊆ H`.
  obtain ⟨M, hMH, hMpd, hMhit⟩ := exists_maximal_matching H hH_ne
  -- Choose a witness good plan for each edge `e ∈ M`.
  let predict (e : Finset P) : (e → Γ) → Bool :=
    if h : e ∈ H then
      let plan := (mem_image.mp h).choose
      let heq : plan.querySet = e := (mem_image.mp h).choose_spec.2
      fun w => plan.restrictEval fun j => w ⟨j.1, heq ▸ j.2⟩
    else fun _ => false
  have hpredict_correct : ∀ e ∈ M,
      1 / 2 + η ≤ ((PMF.uniformOfFintype (ι → Bool)).toOuterMeasure
        {x | predict e (e.restrict (C x)) = x i}).toReal := by
    intro e heM
    have heH : e ∈ H := hMH heM
    let plan := (mem_image.mp heH).choose
    have hspec := (mem_image.mp heH).choose_spec
    have hgood_plan : 1 / 2 + η ≤ acc plan := (mem_filter.mp hspec.1).2.1
    have heval (x : ι → Bool) : predict e (e.restrict (C x)) = plan.eval (C x) := by
      simp only [predict, dite_eq_left heH]
      exact plan.restrictEval_restrict (C x)
    simpa only [heval] using hgood_plan
  refine ⟨⟨M, hMpd, fun e he => hH_ne e (hMH he), fun e he => hH_card e (hMH he),
    predict, hpredict_correct⟩, ?_⟩
  -- Step 4: bound `2 (ε - η) |P| ≤ q c |M|` via smoothness and the union bound on `V = ⋃ M`.
  rcases Nat.eq_zero_or_pos (Fintype.card P) with hP0 | hPpos
  · have hM0 : M = ∅ := by
      by_contra hne
      obtain ⟨e, heM⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      obtain ⟨j, _⟩ := hH_ne e (hMH heM)
      exact absurd (Fintype.card_pos_iff.mpr ⟨j⟩) (by omega)
    simp [hP0, hM0]
  · set V : Finset P := M.biUnion id
    have hV_card : V.card ≤ q * M.card := by
      calc V.card ≤ ∑ e ∈ M, e.card := Finset.card_biUnion_le
        _ ≤ ∑ _e ∈ M, q := Finset.sum_le_sum fun e he => hH_card e (hMH he)
        _ = q * M.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hhit_le : (planLaw.toOuterMeasure good).toReal ≤
        ∑ j ∈ V, (planLaw.toOuterMeasure {plan | j ∈ plan.querySet}).toReal := by
      simp only [Probability.PMF.toOuterMeasure_apply_toReal]
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun plan _ => ?_
      by_cases hp : plan ∈ good
      · rw [ite_eq_left hp]
        by_cases hsupp : plan ∈ planLaw.support
        · have heH : plan.querySet ∈ H :=
            mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, hp, hsupp⟩)
          obtain ⟨j₀, hj₀V, hj₀e⟩ := hMhit plan.querySet heH
          have hle := Finset.single_le_sum (f := fun j =>
              if j ∈ plan.querySet then (planLaw plan).toReal else 0)
            (fun j _ => by split_ifs <;> [exact ENNReal.toReal_nonneg; exact le_rfl]) hj₀V
          have hle' : (planLaw plan).toReal ≤
              ∑ j ∈ V, if j ∈ plan.querySet then (planLaw plan).toReal else 0 := by
            simpa only [hj₀e, ↓reduceIte] using hle
          refine hle'.trans (le_of_eq ?_)
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hj : j ∈ plan.querySet <;> simp [hj]
        · have hz : planLaw plan = 0 := (PMF.apply_eq_zero_iff _ _).mpr hsupp
          rw [hz, ENNReal.toReal_zero]
          exact Finset.sum_nonneg fun j _ => by split_ifs <;> simp
      · rw [ite_eq_right hp]
        exact Finset.sum_nonneg fun j _ => by
          split_ifs <;> [exact ENNReal.toReal_nonneg; exact le_rfl]
    have hc_nonneg : 0 ≤ c := by
      obtain ⟨j₀⟩ := Fintype.card_pos_iff.mp hPpos
      have h0 : (0 : ℝ) ≤ c / Fintype.card P := ENNReal.toReal_nonneg.trans (hsmooth j₀)
      have hn : (0 : ℝ) < Fintype.card P := by exact_mod_cast hPpos
      exact (div_nonneg_iff.mp h0).elim (fun h => h.1) (fun h => absurd hn (not_lt.mpr h.2))
    have hbound : 2 * (ε - η) ≤ (V.card : ℝ) * (c / Fintype.card P) :=
      hgood_prob.trans <| hhit_le.trans <| by
        calc ∑ j ∈ V, (planLaw.toOuterMeasure {plan | j ∈ plan.querySet}).toReal
            ≤ ∑ _j ∈ V, (c / Fintype.card P) := Finset.sum_le_sum fun j _ => hsmooth j
          _ = (V.card : ℝ) * (c / Fintype.card P) := by rw [Finset.sum_const, nsmul_eq_mul]
    have hn : (0 : ℝ) < Fintype.card P := by exact_mod_cast hPpos
    have hmul : 2 * (ε - η) * Fintype.card P ≤ (V.card : ℝ) * c := by
      have h := mul_le_mul_of_nonneg_right hbound hn.le
      have hcancel : (V.card : ℝ) * (c / Fintype.card P) * Fintype.card P = (V.card : ℝ) * c := by
        rw [mul_assoc, div_mul_cancel₀ _ hn.ne']
      linarith
    have hV_real : (V.card : ℝ) ≤ (q : ℝ) * M.card := by exact_mod_cast hV_card
    calc 2 * (ε - η) * Fintype.card P ≤ (V.card : ℝ) * c := hmul
      _ ≤ ((q : ℝ) * M.card) * c := mul_le_mul_of_nonneg_right hV_real hc_nonneg
      _ = q * c * M.card := by ring

/-- The probability that a non-adaptive plan queries position `j` is at most its expected number of
reads of `j`. -/
private theorem toReal_toOuterMeasure_mem_querySet_le_expectedReads [DecidableEq P]
    {q : ℕ} (planLaw : ProbComp (NonadaptivePlan P Γ q)) (y : P → Γ) (j : P) :
    ((ProbComp.eval planLaw).toOuterMeasure {plan | j ∈ plan.querySet}).toReal ≤
      (expectedReads (nonadaptivePlan planLaw) y j).toReal := by
  refine ENNReal.toReal_mono (expectedReads_ne_top (isQueryBounded_nonadaptivePlan planLaw) y j) ?_
  rw [Probability.PMF.toOuterMeasure_eq_tsum_mul_indicator, expectedReads_nonadaptivePlan]
  refine tsum_le_tsum fun plan => ?_
  gcongr
  by_cases hj : j ∈ plan.querySet
  · rw [Set.indicator_of_mem (show plan ∈ {plan | j ∈ plan.querySet} from hj), Pi.one_apply]
    obtain ⟨k, hk⟩ := (plan.mem_querySet_iff j).mp hj
    have hle := Finset.single_le_sum (f := fun k' : Fin q =>
        if plan.queries k' = some j then (1 : ℝ≥0∞) else 0)
      (fun _ _ => zero_le) (Finset.mem_univ k)
    simpa only [hk, ↓reduceIte] using hle
  · rw [Set.indicator_of_notMem (show plan ∉ {plan | j ∈ plan.querySet} from hj)]
    exact zero_le

/-- Average accuracy of a non-adaptive plan decoder on uniform messages. -/
private theorem average_acc_of_isSmoothDecoder [Fintype ι] [DecidableEq ι] [Fintype P]
    [DecidableEq P] [Finite Γ] {C : (ι → Bool) → P → Γ} {q : ℕ} {c ε : ℝ}
    {planLaw : ι → ProbComp (NonadaptivePlan P Γ q)}
    (hA : IsSmoothDecoder C q c ε fun i => nonadaptivePlan (planLaw i)) (i : ι) :
    1 / 2 + ε ≤ ∑' plan, (ProbComp.eval (planLaw i) plan).toReal *
      ((PMF.uniformOfFintype (ι → Bool)).toOuterMeasure {x | plan.eval (C x) = x i}).toReal := by
  classical
  let := Fintype.ofFinite (NonadaptivePlan P Γ q)
  let U := PMF.uniformOfFintype (ι → Bool)
  rw [tsum_fintype]
  have hswap : ∑ plan, (ProbComp.eval (planLaw i) plan).toReal *
      (U.toOuterMeasure {x | plan.eval (C x) = x i}).toReal =
      ∑ x : ι → Bool, (U x).toReal *
        (decodeLaw (nonadaptivePlan (planLaw i)) (C x) (x i)).toReal := by
    simp_rw [Probability.PMF.toOuterMeasure_toReal_eq_sum_ite, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [decodeLaw_nonadaptivePlan, Probability.PMF.map_apply_toReal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun plan _ => ?_
    by_cases hx : plan.eval (C x) = x i
    · simp [hx, eq_comm, mul_comm]
    · have hx' : x ∉ {x | plan.eval (C x) = x i} := hx
      simp [hx', Ne.symm hx]
  rw [hswap]
  calc 1 / 2 + ε = ∑ x : ι → Bool, (U x).toReal * (1 / 2 + ε) := by
        rw [← Finset.sum_mul, Probability.PMF.sum_toReal, one_mul]
    _ ≤ ∑ x : ι → Bool, (U x).toReal *
          (decodeLaw (nonadaptivePlan (planLaw i)) (C x) (x i)).toReal :=
        Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (hA.correct x i) ENNReal.toReal_nonneg

/-- **Hypergraph matching extraction from a non-adaptive smooth decoder** [KatzTrevisan2000],
[Yekhanin2012]: a `(q, c, ε)` smooth decoder given by `nonadaptivePlan` yields, for every message
bit `i`, a `DecodingMatching` of accuracy `1 / 2 + ε / 2` and size satisfying
`ε |P| ≤ q c |M|`. -/
theorem IsSmoothDecoder.exists_decodingMatching_of_nonadaptivePlan [Fintype ι] [DecidableEq ι]
    [Fintype P] [DecidableEq P] [Finite Γ] {C : (ι → Bool) → P → Γ} {q : ℕ} {c ε : ℝ}
    {planLaw : ι → ProbComp (NonadaptivePlan P Γ q)}
    (hA : IsSmoothDecoder C q c ε fun i => nonadaptivePlan (planLaw i))
    (hε : 0 < ε) (i : ι) :
    ∃ M : DecodingMatching C i q (ε / 2),
      ε * Fintype.card P ≤ q * c * M.edges.card := by
  have h := Code.exists_decodingMatching_of_nonadaptivePlan (C := C) (c := c) (ε := ε) (η := ε / 2)
    i (ProbComp.eval (planLaw i)) (by linarith)
    (average_acc_of_isSmoothDecoder hA i)
    (fun j => (toReal_toOuterMeasure_mem_querySet_le_expectedReads (planLaw i)
      (C fun _ => false) j).trans (hA.smooth _ i j))
  obtain ⟨M, hM⟩ := h
  refine ⟨M, ?_⟩
  linarith

/-- Hypergraph matching extraction from a `Code.nonadaptive` smooth decoder. -/
theorem IsSmoothDecoder.exists_decodingMatching_of_nonadaptive [Fintype ι] [DecidableEq ι]
    [Fintype P] [DecidableEq P] [Finite Γ] [Nonempty Γ] {R : Type} {C : (ι → Bool) → P → Γ}
    {q : ℕ} {c ε : ℝ} {coins : ι → ProbComp R} {Q : ι → R → Fin q → P}
    {output : ι → R → (Fin q → Γ) → Bool}
    (hA : IsSmoothDecoder C q c ε fun i => nonadaptive (coins i) (Q i) (output i))
    (hε : 0 < ε) (i : ι) :
    ∃ M : DecodingMatching C i q (ε / 2),
      ε * Fintype.card P ≤ q * c * M.edges.card := by
  have hplan : IsSmoothDecoder C q c ε fun i =>
      nonadaptivePlan (nonadaptivePlanOf (coins i) (Q i) (output i)) :=
    { isQueryBounded := fun i => isQueryBounded_nonadaptivePlan _
      correct := fun x i => by
        rw [decodeLaw_nonadaptivePlanOf]
        exact hA.correct x i
      smooth := fun x i j => by
        rw [expectedReads_nonadaptivePlanOf]
        exact hA.smooth x i j }
  exact hplan.exists_decodingMatching_of_nonadaptivePlan hε i

/-- Hypergraph matching extraction from a non-adaptive `(q, δ, ε)` local decoder: smooths with no
advantage loss (`c = q / δ`) to obtain a matching with `δ ε |P| ≤ q ^ 2 |M|`. -/
theorem IsLocalDecoder.exists_decodingMatching_of_nonadaptivePlan [Fintype ι] [DecidableEq ι]
    [Fintype P] [Finite Γ] [DecidableEq Γ] {C : (ι → Bool) → P → Γ} {q : ℕ} {δ ε : ℝ}
    {planLaw : ι → ProbComp (NonadaptivePlan P Γ q)}
    (hA : IsLocalDecoder C q δ ε fun i => nonadaptivePlan (planLaw i))
    (hδ : 0 < δ) (hε : 0 < ε) (i : ι) :
    ∃ M : DecodingMatching C i q (ε / 2),
      δ * ε * Fintype.card P ≤ (q : ℝ) ^ 2 * M.edges.card := by
  classical
  have hs := isSmoothDecoder_mask_nonadaptivePlan hA hδ (C fun _ => false)
  obtain ⟨M, hM⟩ := hs.exists_decodingMatching_of_nonadaptivePlan hε i
  refine ⟨M, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hM hδ.le
  have hrhs : δ * ((q : ℝ) * ((q : ℝ) / δ) * M.edges.card) = (q : ℝ) ^ 2 * M.edges.card := by
    field_simp [hδ.ne']
  linarith

/-- **Hypergraph matching extraction from an arbitrary (possibly adaptive) `(q, δ, ε)` local
decoder**: reduces adaptivity with factor `|Γ| ^ -(q - 1)`, smooths heavy positions, and extracts
a decoding matching for bit `i` of accuracy `1 / 2 + ε / (2 |Γ| ^ (q - 1))` and size satisfying
`δ ε |P| ≤ q ^ 2 |Γ| ^ (q - 1) |M|`. -/
theorem IsLocalDecoder.exists_decodingMatching [Fintype ι] [DecidableEq ι] [Fintype P]
    [Fintype Γ] [Nonempty Γ] [DecidableEq Γ] {C : (ι → Bool) → P → Γ} {q : ℕ} {δ ε : ℝ}
    {A : LocalDecoder ι P Γ} (hA : IsLocalDecoder C q δ ε A)
    (hδ : 0 < δ) (hε : 0 < ε) (i : ι) :
    ∃ M : DecodingMatching C i q (ε / (2 * (Fintype.card Γ : ℝ) ^ (q - 1))),
      δ * ε * Fintype.card P ≤ (q : ℝ) ^ 2 * (Fintype.card Γ : ℝ) ^ (q - 1) * M.edges.card := by
  classical
  have hΓ : (0 : ℝ) < (Fintype.card Γ : ℝ) ^ (q - 1) :=
    pow_pos (by exact_mod_cast Fintype.card_pos) _
  have hε' : 0 < ε / (Fintype.card Γ : ℝ) ^ (q - 1) := div_pos hε hΓ
  have hs := hA.isSmoothDecoder_adaptive hδ (C fun _ => false)
  obtain ⟨M, hM⟩ := hs.exists_decodingMatching_of_nonadaptivePlan hε' i
  have hdiv : ε / (Fintype.card Γ : ℝ) ^ (q - 1) / 2 =
      ε / (2 * (Fintype.card Γ : ℝ) ^ (q - 1)) := by ring
  refine ⟨⟨M.edges, M.pairwiseDisjoint, M.nonempty_of_mem, M.card_le_of_mem, M.predict,
    fun e he => by rw [← hdiv]; exact M.correct e he⟩, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hM (mul_pos hδ hΓ).le
  have hlhs : δ * (Fintype.card Γ : ℝ) ^ (q - 1) *
      (ε / (Fintype.card Γ : ℝ) ^ (q - 1) * Fintype.card P) = δ * ε * Fintype.card P := by
    field_simp [hΓ.ne']
  have hrhs : δ * (Fintype.card Γ : ℝ) ^ (q - 1) * ((q : ℝ) * ((q : ℝ) / δ) * M.edges.card) =
      (q : ℝ) ^ 2 * (Fintype.card Γ : ℝ) ^ (q - 1) * M.edges.card := by
    field_simp [hδ.ne']
  linarith

end Cslib.Code
