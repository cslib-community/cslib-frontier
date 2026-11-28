/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LocallyDecodable.Matching
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Foundations.Analysis.BernoulliInequality
import CslibFrontier.Probability.Divergence
import CslibFrontier.Probability.Entropy.Fano
import CslibFrontier.Probability.Entropy.Pi
import CslibFrontier.Probability.PMF.Coin
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.Shearer
import CslibFrontier.Probability.StatisticalDistance
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Katz–Trevisan lower bound for locally decodable codes

This module proves the Katz–Trevisan information-theoretic length lower bound
`n = Ω(k ^ (q / (q - 1)))` for `q`-query locally decodable codes [KatzTrevisan2000], [Yekhanin2012],
both for non-adaptive decoders (with no adaptivity penalty) and for arbitrary adaptive `q`-query
decoders (via `Cslib.Code.nonadaptivize`, incurring the `|Γ| ^ (q - 1)` reduction factor).

The proof proceeds in two steps:

1. **Information-theoretic bit-recovery bound**
   (`Cslib.Code.card_mul_one_sub_binEntropy_le_logb_card`):
   if deterministic predictors `g i` recover each bit `i ∈ T` of a uniformly random message
   `x : ι → Bool` from `C x : R` with probability at least `1 / 2 + η`, then
   `|T| · (1 - h₂(1 / 2 + η)) ≤ log₂ |R|`, where `h₂(p) = Real.binEntropy p / Real.log 2`. This
   combines the chain rule, conditional-entropy subadditivity (`Shearer.lean`), and Fano's
   inequality (`Fano.lean`).
2. **Random restriction of decoding matchings (`Cslib.Code.DecodingMatching.pow_le_pow`)**:
   given a `DecodingMatching` family `M i` of size at least `α |P|` with accuracy `1 / 2 + η` for
   each message bit `i`, include each coordinate of `P` independently with probability `p`. For any
   sampled subset `S ⊆ P`, every bit `i` whose matching contains an edge `e ⊆ S` is predicted with
   accuracy `1 / 2 + η` from `C x|_S`, so step 1 bounds the number of recovered bits by
   `|S| · log₂ |Γ| / (1 - h₂(1 / 2 + η))`. Disjointness of `M i` makes the edges in `M i` hit `S`
   independently with probability at least `p ^ q`, giving an average recovery probability at least
   `α |P| p ^ q / (1 + α |P| p ^ q)`. Optimizing `p = (α |P|) ^ (-1 / q)` yields the unified
   polynomial inequality
   `α · (|ι| · (1 - h₂(1 / 2 + η))) ^ q ≤ (2 log₂ |Γ|) ^ q · |P| ^ (q - 1)`
   for every `q ≥ 1` (recovering the `log₂ |Γ|` upper bound on `|ι|` at `q = 1`, and raising to
   `1 / (q - 1)` gives `|P| ≥ c(q, δ, ε, |Γ|) · |ι| ^ (q / (q - 1))` for all `q ≥ 2` and `|Γ| ≥ 2`).

## Main results

* `Cslib.Code.card_mul_one_sub_binEntropy_le_logb_card`: information-theoretic decoding bound
  `|T| · (1 - h₂(1 / 2 + η)) ≤ log₂ |R|`.
* `Cslib.Code.DecodingMatching.pow_le_pow`: unified polynomial bound from a family of decoding
  matchings.
* `Cslib.Code.IsSmoothDecoder.pow_le_pow_of_nonadaptivePlan`: sharp bound for non-adaptive smooth
  decoders.
* `Cslib.Code.IsLocalDecoder.pow_le_pow_of_nonadaptivePlan`,
  `Cslib.Code.IsLocalDecoder.rpow_le_card_of_nonadaptivePlan`: sharp and `k ^ (q / (q - 1))` bounds
  for non-adaptive `q`-query local decoders.
* `Cslib.Code.IsLocallyDecodable.pow_le_pow`, `Cslib.Code.IsLocallyDecodable.rpow_le_card`:
  **Katz–Trevisan `Ω(k ^ (q / (q - 1)))` lower bound** for arbitrary (possibly adaptive) `q`-query
  locally decodable codes.

## References

* [J. Katz, L. Trevisan, *On the efficiency of local decoding procedures for error-correcting
  codes*][KatzTrevisan2000]
* [S. Yekhanin, *Locally decodable codes*][Yekhanin2012]
-/

public section

open Finset
open scoped BigOperators ENNReal unitInterval

namespace Cslib.Code

open Probability
open scoped Cslib.Probability.PMF

variable {ι P Γ R : Type}

/-! ### Information-theoretic bit-recovery bound -/

section InfoBound

/-- Conditioning on the first component commutes with mapping the second component. -/
private theorem conditionalSnd_map_snd {α β γ : Type*} [Finite α] [Finite β] [Finite γ]
    (joint : PMF (α × β)) (f : β → γ) {a : α} (ha : a ∈ (joint.map Prod.fst).support) :
    (PMF.conditionalSnd joint a).map f =
      PMF.conditionalSnd (joint.map fun p => (p.1, f p.2)) a := by
  classical
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  let := Fintype.ofFinite γ
  have hfst : (joint.map fun p => (p.1, f p.2)).map Prod.fst = joint.map Prod.fst := by
    rw [_root_.PMF.map_comp]; rfl
  ext c
  rw [_root_.PMF.map_apply, PMF.conditionalSnd_apply _ _ (hfst.symm ▸ ha), hfst]
  simp only [PMF.conditionalSnd_apply _ _ ha]
  have hdiv (b : β) : (if c = f b then joint (a, b) / (joint.map Prod.fst) a else 0) =
      (if c = f b then joint (a, b) else 0) * ((joint.map Prod.fst) a)⁻¹ := by
    split_ifs <;> simp [div_eq_mul_inv]
  simp_rw [hdiv, ENNReal.tsum_mul_right, div_eq_mul_inv]
  congr 1
  rw [_root_.PMF.map_apply, tsum_fintype, tsum_fintype, Fintype.sum_prod_type,
    Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun b _ => by by_cases hc : c = f b <;> simp [hc]
  · exact fun _ _ h => Finset.sum_eq_zero fun _ _ => by simp [Ne.symm h]
  · exact fun h => absurd (Finset.mem_univ a) h

/-- Subadditivity of conditional entropy across coordinates of a tuple. -/
private theorem conditionalEntropy_pi_le_sum {Ω κ : Type*} {α : κ → Type*}
    [Finite Ω] [Fintype κ] [∀ i, Finite (α i)] [Finite R]
    (ν : PMF Ω) (Y : Ω → R) (X : Ω → ∀ i, α i) :
    PMF.conditionalEntropy (ν.map fun ω => (Y ω, X ω)) ≤
      ∑ i, PMF.conditionalEntropy (ν.map fun ω => (Y ω, X ω i)) := by
  classical
  let := Fintype.ofFinite Ω
  let := Fintype.ofFinite R
  let : ∀ i, Fintype (α i) := fun i => Fintype.ofFinite (α i)
  let J := ν.map fun ω => (Y ω, X ω)
  have hfst (i : κ) : (ν.map fun ω => (Y ω, X ω i)).map Prod.fst = J.map Prod.fst := by
    simp only [J, _root_.PMF.map_comp]; rfl
  rw [PMF.conditionalEntropy_eq_sum]
  calc ∑ y, ((J.map Prod.fst) y).toReal * PMF.entropy (PMF.conditionalSnd J y)
      ≤ ∑ y, ((J.map Prod.fst) y).toReal *
          ∑ i, PMF.entropy ((PMF.conditionalSnd J y).map fun z => z i) :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
          (PMF.entropy_le_sum_entropy_map_eval _) ENNReal.toReal_nonneg
    _ = ∑ i, ∑ y, ((J.map Prod.fst) y).toReal *
          PMF.entropy ((PMF.conditionalSnd J y).map fun z => z i) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
    _ = ∑ i, PMF.conditionalEntropy (ν.map fun ω => (Y ω, X ω i)) :=
        Finset.sum_congr rfl fun i _ => by
          rw [PMF.conditionalEntropy_eq_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [hfst i]
          by_cases hy : y ∈ (J.map Prod.fst).support
          · have hmap : J.map (fun p => (p.1, p.2 i)) = ν.map fun ω => (Y ω, X ω i) := by
              simp only [J, _root_.PMF.map_comp]
              rfl
            rw [conditionalSnd_map_snd J (fun z => z i) hy, hmap]
          · simp [(_root_.PMF.apply_eq_zero_iff _ _).mpr hy]

/-- **Information-theoretic bit-recovery bound** [KatzTrevisan2000], [Yekhanin2012]: if
deterministic predictors `g i : R → Bool` recover each bit `i ∈ T` of a uniformly random message
`x : ι → Bool` from `C x : R` with probability at least `1 / 2 + η` (`0 ≤ η`), then
`|T| · (1 - h₂(1 / 2 + η)) ≤ log₂ |R|`, where `h₂(p) = Real.binEntropy p / Real.log 2`. -/
theorem card_mul_one_sub_binEntropy_le_logb_card [Fintype ι] [DecidableEq ι] [Fintype R]
    [Nonempty R] (C : (ι → Bool) → R) (T : Finset ι) (g : ι → R → Bool) {η : ℝ} (hη : 0 ≤ η)
    (hg : ∀ i ∈ T,
      1 / 2 + η ≤ ((PMF.uniformOfFintype (ι → Bool)).toOuterMeasure {x | g i (C x) = x i}).toReal) :
    (T.card : ℝ) * (1 - Real.binEntropy (1 / 2 + η) / Real.log 2) ≤
      Real.logb 2 (Fintype.card R) := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    exact Real.logb_nonneg one_lt_two (Nat.one_le_cast.mpr Fintype.card_pos)
  let U := PMF.uniformOfFintype (ι → Bool)
  -- Since `T` is nonempty, `1 / 2 + η ≤ 1`, so `η ≤ 1 / 2`.
  have hη_le : η ≤ 1 / 2 := by
    have h1 : (U.toOuterMeasure {x | g i₀ (C x) = x i₀}).toReal ≤ 1 := by
      simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top
        (Probability.PMF.toOuterMeasure_le_one U _)
    linarith [hg i₀ hi₀]
  -- `H(X_T) = |T|`.
  have hHXT : PMF.entropy (U.map T.restrict) = T.card := by
    rw [Probability.PMF.uniformOfFintype_pi_map_restrict (π := fun _ => Bool) T,
      PMF.entropy_uniform]
    simp [Real.logb_pow]
  -- `H(X_T) - H(X_T | C X) ≤ H(C X) ≤ log₂ |R|`.
  have hMI : (T.card : ℝ) - PMF.conditionalEntropy (U.map fun x => (C x, T.restrict x)) ≤
      Real.logb 2 (Fintype.card R) := by
    have hswap : PMF.entropy (U.map fun x => (C x, T.restrict x)) =
        PMF.entropy (U.map fun x => (T.restrict x, C x)) := by
      rw [← PMF.entropy_map_of_injective _ Prod.swap_injective, _root_.PMF.map_comp]; rfl
    have hnonneg : 0 ≤ PMF.conditionalEntropy (U.map fun x => (T.restrict x, C x)) :=
      PMF.conditionalEntropy_nonneg _
    have hfst1 : (U.map fun x => (C x, T.restrict x)).map Prod.fst = U.map C := by
      rw [_root_.PMF.map_comp]; rfl
    have hfst2 : (U.map fun x => (T.restrict x, C x)).map Prod.fst = U.map T.restrict := by
      rw [_root_.PMF.map_comp]; rfl
    rw [PMF.conditionalEntropy, hfst1, hswap]
    rw [PMF.conditionalEntropy, hfst2, hHXT] at hnonneg
    linarith [PMF.entropy_le_log_card (U.map C)]
  -- Bound each bit's conditional entropy via Fano's inequality.
  have hbit (i : T) : PMF.conditionalEntropy (U.map fun x => (C x, x i.val)) ≤
      Real.binEntropy (1 / 2 + η) / Real.log 2 := by
    have hfano :=
      PMF.conditionalEntropy_map_le_binEntropy_add_mul_logb U (fun x => x i.val) C (g i.val)
    rw [show Real.logb 2 ((Fintype.card Bool : ℝ) - 1) = 0 by norm_num, mul_zero, add_zero] at hfano
    refine hfano.trans (div_le_div_of_nonneg_right ?_ (Real.log_pos one_lt_two).le)
    set Pe := (U.toOuterMeasure {x | g i.val (C x) ≠ x i.val}).toReal
    have hcomp : (U.toOuterMeasure {x | g i.val (C x) = x i.val}).toReal + Pe = 1 := by
      simpa only [Set.compl_ofPred, ne_eq] using
        Probability.PMF.toOuterMeasure_toReal_add_compl U {x | g i.val (C x) = x i.val}
    have hPe_le : Pe ≤ 1 / 2 - η := by linarith [hg i.val i.property]
    have hmono := Real.binEntropy_strictMonoOn.monotoneOn
      ⟨ENNReal.toReal_nonneg, by linarith⟩ ⟨by linarith, by linarith⟩ hPe_le
    rw [one_div, ← Real.binEntropy_two_inv_add] at hmono
    rwa [← one_div] at hmono
  -- Sum over `i ∈ T` by subadditivity of conditional entropy.
  have hcond : PMF.conditionalEntropy (U.map fun x => (C x, T.restrict x)) ≤
      (T.card : ℝ) * (Real.binEntropy (1 / 2 + η) / Real.log 2) := by
    calc
      PMF.conditionalEntropy (U.map fun x => (C x, T.restrict x))
        ≤ ∑ i : T, PMF.conditionalEntropy (U.map fun x => (C x, x i.val)) :=
          conditionalEntropy_pi_le_sum U C T.restrict
      _ ≤ ∑ _i : T, (Real.binEntropy (1 / 2 + η) / Real.log 2) :=
          Finset.sum_le_sum fun i _ => hbit i
      _ = (T.card : ℝ) * (Real.binEntropy (1 / 2 + η) / Real.log 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  linarith

end InfoBound

/-! ### Bernoulli random restrictions on disjoint hypergraph matchings -/

section MatchingRestriction

/-- For `x ∈ [0, 1]` and `m : ℕ`, `m * x / (1 + m * x) ≤ 1 - (1 - x) ^ m`. -/
private theorem mul_div_one_add_le_one_sub_pow {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (m : ℕ) :
    (m : ℝ) * x / (1 + m * x) ≤ 1 - (1 - x) ^ m := by
  have hpos : 0 < 1 + (m : ℝ) * x := by positivity
  rw [div_le_iff₀ hpos]
  have h := Real.one_sub_pow_mul_one_add_mul_le_one hx1 m
  linarith

/-- Under independent `Bernoulli(p)` coordinate sampling on `P`, the probability that NO edge of a
pairwise-disjoint hyperedge family `E` is fully selected equals `∏ e ∈ E, (1 - p ^ e.card)`. -/
private theorem bernoulli_miss_all_eq_prod [Fintype P] [DecidableEq P] (p : I)
    (E : Finset (Finset P)) (hE : (E : Set (Finset P)).PairwiseDisjoint id) :
    ∑ s : P → Bool, (PMF.pi (fun _ : P => PMF.coin p) s).toReal *
      (∏ e ∈ E, if ∀ j ∈ e, s j = true then (0 : ℝ) else 1) =
        ∏ e ∈ E, (1 - (p : ℝ) ^ e.card) := by
  induction E using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, mul_one, Probability.PMF.sum_toReal]
  | insert e₀ E he₀ ih =>
    have hpdE : (E : Set (Finset P)).PairwiseDisjoint id :=
      hE.subset (Finset.coe_subset.mpr (Finset.subset_insert e₀ E))
    have hdisj : ∀ e ∈ E, Disjoint e₀ e := fun e he =>
      hE (Finset.mem_coe.mpr (Finset.mem_insert_self e₀ E))
        (Finset.mem_coe.mpr (Finset.mem_insert_of_mem he))
        (fun h => he₀ (h ▸ he))
    let equiv : (P → Bool) ≃ (∀ _ : {j // j ∈ e₀}, Bool) × (∀ _ : {j // j ∉ e₀}, Bool) :=
      Equiv.piEquivPiSubtypeProd (fun j : P => j ∈ e₀) (fun _ => Bool)
    let w1 (u : {j // j ∈ e₀} → Bool) : ℝ := ∏ j : {j // j ∈ e₀}, (PMF.coin p (u j)).toReal
    let w2 (v : {j // j ∉ e₀} → Bool) : ℝ := ∏ j : {j // j ∉ e₀}, (PMF.coin p (v j)).toReal
    have hw1_sum : ∑ u : {j // j ∈ e₀} → Bool, w1 u = 1 := by
      simpa only [w1, PMF.pi_apply, ENNReal.toReal_prod] using
        Probability.PMF.sum_toReal (PMF.pi (fun _ : {j // j ∈ e₀} => PMF.coin p))
    have hw_mul (u : {j // j ∈ e₀} → Bool) (v : {j // j ∉ e₀} → Bool) :
        (PMF.pi (fun _ : P => PMF.coin p) (equiv.symm (u, v))).toReal = w1 u * w2 v := by
      rw [PMF.pi_apply, ENNReal.toReal_prod,
        ← Fintype.prod_subtype_mul_prod_subtype (p := fun j : P => j ∈ e₀)]
      congr 1
      · refine Finset.prod_congr (by
            ext j
            simp) fun j _ => ?_
        simp [equiv, Equiv.piEquivPiSubtypeProd, j.property]
      · refine Finset.prod_congr (by
            ext j
            simp) fun j _ => ?_
        simp [equiv, Equiv.piEquivPiSubtypeProd, j.property]
    let f1 (u : {j // j ∈ e₀} → Bool) : ℝ := if ∀ j, u j = true then 0 else 1
    let f2 (v : {j // j ∉ e₀} → Bool) : ℝ :=
      ∏ e ∈ E, if ∀ j ∈ e, equiv.symm (fun _ => false, v) j = true then (0 : ℝ) else 1
    have hf1_eq (u : {j // j ∈ e₀} → Bool) (v : {j // j ∉ e₀} → Bool) :
        (if ∀ j ∈ e₀, equiv.symm (u, v) j = true then (0 : ℝ) else 1) = f1 u := by
      simp only [f1]
      congr 1
      exact propext ⟨fun h j => by
          simpa [equiv, Equiv.piEquivPiSubtypeProd, j.property] using h j.val j.property,
        fun h j hj => by simpa [equiv, Equiv.piEquivPiSubtypeProd, hj] using h ⟨j, hj⟩⟩
    have hf2_eq (u : {j // j ∈ e₀} → Bool) (v : {j // j ∉ e₀} → Bool) :
        (∏ e ∈ E, if ∀ j ∈ e, equiv.symm (u, v) j = true then (0 : ℝ) else 1) = f2 v :=
      Finset.prod_congr rfl fun e he => if_congr
        ⟨fun h j hj => by
            have hj' := Finset.disjoint_right.mp (hdisj e he) hj
            simpa [equiv, Equiv.piEquivPiSubtypeProd, hj'] using h j hj,
          fun h j hj => by
            have hj' := Finset.disjoint_right.mp (hdisj e he) hj
            simpa [equiv, Equiv.piEquivPiSubtypeProd, hj'] using h j hj⟩ rfl rfl
    have hfactor1 : ∑ u : {j // j ∈ e₀} → Bool, w1 u * f1 u = 1 - (p : ℝ) ^ e₀.card := by
      let uT : {j // j ∈ e₀} → Bool := fun _ => true
      have hterm (u : {j // j ∈ e₀} → Bool) :
          w1 u * f1 u = w1 u - (if u = uT then w1 uT else 0) := by
        by_cases hu : u = uT
        · subst hu
          simp [f1, uT]
        · simp only [f1, hu, show ¬ ∀ j, u j = true from fun h => hu (funext h),
            ↓reduceIte, mul_one, sub_zero]
      simp_rw [hterm]
      rw [Finset.sum_sub_distrib, hw1_sum, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ uT)]
      simp [w1, uT, PMF.coin_apply_toReal]
    have hfactor2 : ∑ v : {j // j ∉ e₀} → Bool, w2 v * f2 v = ∏ e ∈ E, (1 - (p : ℝ) ^ e.card) := by
      rw [← ih hpdE, ← Equiv.sum_comp equiv.symm, Fintype.sum_prod_type]
      simp_rw [hw_mul, hf2_eq]
      calc
        ∑ v, w2 v * f2 v
          = (∑ u, w1 u) * ∑ v, w2 v * f2 v := by rw [hw1_sum, one_mul]
        _ = ∑ u, ∑ v, (w1 u * w2 v) * f2 v := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun _ _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun _ _ => by ring
    rw [Finset.prod_insert he₀, ← hfactor1, ← hfactor2, ← Equiv.sum_comp equiv.symm,
      Fintype.sum_prod_type]
    simp_rw [Finset.prod_insert he₀, hw_mul, hf1_eq, hf2_eq]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring

/-- Under independent `Bernoulli(p)` coordinate sampling on `P`, the probability that at least one
edge of a `q`-bounded decoding matching `M` is fully contained in the sampled set is at least
`(|M| * p ^ q) / (1 + |M| * p ^ q)`. -/
private theorem bernoulli_hit_ge [Fintype ι] [DecidableEq ι] [Fintype P]
    {C : (ι → Bool) → P → Γ} {i : ι} {q : ℕ} {η : ℝ}
    (M : DecodingMatching C i q η) (p : I) :
    (M.edges.card : ℝ) * (p : ℝ) ^ q / (1 + M.edges.card * (p : ℝ) ^ q) ≤
      ((PMF.pi (fun _ : P => PMF.coin p)).toOuterMeasure
        {s | ∃ e ∈ M.edges, ∀ j ∈ e, s j = true}).toReal := by
  classical
  let μ := PMF.pi (fun _ : P => PMF.coin p)
  have hcomp : (μ.toOuterMeasure {s | ∃ e ∈ M.edges, ∀ j ∈ e, s j = true}).toReal +
      (μ.toOuterMeasure {s | ∀ e ∈ M.edges, ¬ ∀ j ∈ e, s j = true}).toReal = 1 := by
    simpa only [Set.compl_ofPred, not_exists, not_and] using
      Probability.PMF.toOuterMeasure_toReal_add_compl μ {s | ∃ e ∈ M.edges, ∀ j ∈ e, s j = true}
  have hmiss_eq : (μ.toOuterMeasure {s | ∀ e ∈ M.edges, ¬ ∀ j ∈ e, s j = true}).toReal =
      ∑ s : P → Bool, (μ s).toReal *
        (∏ e ∈ M.edges, if ∀ j ∈ e, s j = true then (0 : ℝ) else 1) := by
    rw [Probability.PMF.toOuterMeasure_toReal_eq_sum_ite]
    refine Finset.sum_congr rfl fun s _ => congrArg _ ?_
    simp only [Set.mem_ofPred_eq]
    by_cases hall : ∀ e ∈ M.edges, ¬ ∀ j ∈ e, s j = true
    · rw [ite_eq_left hall, Finset.prod_eq_one fun e he => ite_eq_right (hall e he)]
    · rw [ite_eq_right hall]
      push Not at hall
      obtain ⟨e, heM, hesub⟩ := hall
      exact (Finset.prod_eq_zero (f := fun e => if ∀ j ∈ e, s j = true then (0 : ℝ) else 1)
        heM (ite_eq_left hesub)).symm
  have hmiss_le : (μ.toOuterMeasure {s | ∀ e ∈ M.edges, ¬ ∀ j ∈ e, s j = true}).toReal ≤
      (1 - (p : ℝ) ^ q) ^ M.edges.card := by
    rw [hmiss_eq, bernoulli_miss_all_eq_prod p M.edges M.pairwiseDisjoint]
    calc
      ∏ e ∈ M.edges, (1 - (p : ℝ) ^ e.card)
        ≤ ∏ _e ∈ M.edges, (1 - (p : ℝ) ^ q) :=
          Finset.prod_le_prod₀ (fun _ _ => sub_nonneg.mpr (pow_le_one₀ p.property.1 p.property.2))
            fun e he => sub_le_sub_left
              (pow_le_pow_of_le_one p.property.1 p.property.2 (M.card_le_of_mem e he)) 1
      _ = (1 - (p : ℝ) ^ q) ^ M.edges.card := by rw [Finset.prod_const]
  linarith [mul_div_one_add_le_one_sub_pow
    (pow_nonneg p.property.1 q) (pow_le_one₀ p.property.1 p.property.2)
    M.edges.card]

/-- Expected size of a `Bernoulli(p)` subset of `P` is `p * |P|`. -/
private theorem bernoulli_expected_card [Fintype P] [DecidableEq P] (p : I) :
    ∑ s : P → Bool, (PMF.pi (fun _ : P => PMF.coin p) s).toReal *
      ((Finset.univ.filter fun j : P => s j = true).card : ℝ) = (p : ℝ) * Fintype.card P := by
  classical
  simp_rw [show ∀ s : P → Bool, ((Finset.univ.filter fun j : P => s j = true).card : ℝ) =
      ∑ j : P, if s j = true then (1 : ℝ) else 0 from fun _ => by simp [Finset.sum_boole],
    Finset.mul_sum]
  rw [Finset.sum_comm]
  have hj (j : P) : ∑ s : P → Bool, (PMF.pi (fun _ : P => PMF.coin p) s).toReal *
      (if s j = true then (1 : ℝ) else 0) = (p : ℝ) := by
    rw [Probability.PMF.sum_pi_mul_eval (fun _ : P => PMF.coin p) j
      (fun b => if b = true then (1 : ℝ) else 0), Fintype.sum_bool]
    simp [PMF.coin_apply_toReal]
  simp_rw [hj, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- Fixed-subset bound from a family of decoding matchings: for any subset `S ⊆ P`, the number of
message bits whose matching contains an edge inside `S` times `1 - h₂(1 / 2 + η)` is at most
`|S| · log₂ |Γ|`. -/
private theorem card_recovered_mul_le [Fintype ι] [DecidableEq ι] [DecidableEq P]
    [Fintype Γ] [Nonempty Γ] {C : (ι → Bool) → P → Γ} {q : ℕ} {η : ℝ} (hη : 0 ≤ η)
    (M : ∀ i : ι, DecodingMatching C i q η) (S : Finset P) :
    ((Finset.univ.filter fun i : ι => ∃ e ∈ (M i).edges, e ⊆ S).card : ℝ) *
        (1 - Real.binEntropy (1 / 2 + η) / Real.log 2) ≤
      (S.card : ℝ) * Real.logb 2 (Fintype.card Γ) := by
  classical
  let g (i : ι) (w : S → Γ) : Bool :=
    if h : ∃ e ∈ (M i).edges, e ⊆ S then
      (M i).predict h.choose fun j => w ⟨j.val, h.choose_spec.2 j.property⟩
    else false
  have hg : ∀ i ∈ Finset.univ.filter (fun i : ι => ∃ e ∈ (M i).edges, e ⊆ S),
      1 / 2 + η ≤ ((PMF.uniformOfFintype (ι → Bool)).toOuterMeasure
        {x | g i (S.restrict (C x)) = x i}).toReal := fun i hi => by
    have h : ∃ e ∈ (M i).edges, e ⊆ S := (Finset.mem_filter.mp hi).2
    have hge (x : ι → Bool) :
        g i (S.restrict (C x)) = (M i).predict h.choose (h.choose.restrict (C x)) := by
      simp only [g, dite_eq_left h]; rfl
    simpa only [hge] using (M i).correct h.choose h.choose_spec.1
  have hinfo := card_mul_one_sub_binEntropy_le_logb_card (fun x => S.restrict (C x)) _ g hη hg
  rwa [Fintype.card_fun, Fintype.card_coe, Nat.cast_pow, Real.logb_pow] at hinfo

/-- **Katz–Trevisan polynomial bound from decoding matchings** [KatzTrevisan2000], [Yekhanin2012]:
if every message bit `i : ι` has a `q`-bounded decoding matching of size at least `α |P|` and
accuracy `1 / 2 + η` (`1 ≤ q`, `0 < α`, `0 < η`, `P` and `Γ` nonempty), then
`α · (|ι| · (1 - h₂(1 / 2 + η))) ^ q ≤ (2 log₂ |Γ|) ^ q · |P| ^ (q - 1)`. -/
theorem DecodingMatching.pow_le_pow [Fintype ι] [DecidableEq ι] [Fintype P] [Nonempty P]
    [Fintype Γ] [Nonempty Γ] {C : (ι → Bool) → P → Γ} {q : ℕ} {α η : ℝ}
    (M : ∀ i : ι, DecodingMatching C i q η) (hq : 1 ≤ q) (hα : 0 < α) (hη : 0 < η)
    (hsize : ∀ i, α * Fintype.card P ≤ (M i).edges.card) :
    α * ((Fintype.card ι : ℝ) * (1 - Real.binEntropy (1 / 2 + η) / Real.log 2)) ^ q ≤
      (2 * Real.logb 2 (Fintype.card Γ)) ^ q * (Fintype.card P : ℝ) ^ (q - 1) := by
  classical
  set k : ℝ := (Fintype.card ι : ℝ)
  set n : ℝ := (Fintype.card P : ℝ)
  set H : ℝ := 1 - Real.binEntropy (1 / 2 + η) / Real.log 2
  set L : ℝ := Real.logb 2 (Fintype.card Γ)
  have hn : 0 < n := Nat.cast_pos.mpr (Fintype.card_pos (α := P))
  have hH0 : 0 ≤ H := sub_nonneg.mpr <|
    (div_le_one (Real.log_pos one_lt_two)).mpr Real.binEntropy_le_log_two
  have hL0 : 0 ≤ L := Real.logb_nonneg one_lt_two (by exact_mod_cast Fintype.card_pos (α := Γ))
  have hnq : n ^ q = n * n ^ (q - 1) := by rw [← pow_succ', Nat.sub_add_cancel hq]
  rcases lt_or_ge (α * n) 1 with hsmall | hlarge
  · -- Small regime `α n < 1`: every matching is nonempty, so evaluate at `S = Finset.univ`.
    have hfull := card_recovered_mul_le hη.le M (Finset.univ : Finset P)
    have hfilter : (Finset.univ.filter fun i : ι => ∃ e ∈ (M i).edges, e ⊆ Finset.univ) =
        Finset.univ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.subset_univ,
        and_true, iff_true]
      exact Finset.card_pos.mp (by exact_mod_cast (mul_pos hα hn).trans_le (hsize i))
    rw [hfilter, Finset.card_univ] at hfull
    have hpow := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hH0) hfull q
    have hq1 : (1 : ℝ) ≤ (2 : ℝ) ^ q := one_le_pow₀ (by norm_num)
    calc
      α * (k * H) ^ q ≤ α * (n * L) ^ q := mul_le_mul_of_nonneg_left hpow hα.le
      _ = (α * n) * (L ^ q * n ^ (q - 1)) := by rw [mul_pow, hnq]; ring
      _ ≤ (2 : ℝ) ^ q * (L ^ q * n ^ (q - 1)) :=
          mul_le_mul_of_nonneg_right (hsmall.le.trans hq1) (by positivity)
      _ = (2 * L) ^ q * n ^ (q - 1) := by rw [mul_pow]; ring
  · -- Main regime `1 ≤ α n`: sample each coordinate with probability `p = (α n) ^ (-1 / q)`.
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
    let p : I := ⟨(α * n) ^ (-(1 / (q : ℝ))),
      ⟨Real.rpow_nonneg (by linarith) _,
       Real.rpow_le_one_of_one_le_of_nonpos hlarge (neg_nonpos.mpr (by positivity))⟩⟩
    have hpq : (p : ℝ) ^ q = (α * n)⁻¹ := by
      change ((α * n) ^ (-(1 / (q : ℝ)))) ^ q = _
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ α * n),
        show -(1 / (q : ℝ)) * (q : ℝ) = -1 by field_simp [hqpos.ne'], Real.rpow_neg_one]
    let μ := PMF.pi (fun _ : P => PMF.coin p)
    -- Average the fixed-subset bound over `s ~ μ`.
    have havg : (∑ s : P → Bool, (μ s).toReal *
        ((Finset.univ.filter fun i : ι => ∃ e ∈ (M i).edges,
          e ⊆ Finset.univ.filter fun j => s j = true).card : ℝ)) * H ≤ (p : ℝ) * n * L := by
      calc
        (∑ s : P → Bool, (μ s).toReal *
            ((Finset.univ.filter fun i : ι => ∃ e ∈ (M i).edges,
              e ⊆ Finset.univ.filter fun j => s j = true).card : ℝ)) * H
          = ∑ s : P → Bool, (μ s).toReal *
              (((Finset.univ.filter fun i : ι => ∃ e ∈ (M i).edges,
                e ⊆ Finset.univ.filter fun j => s j = true).card : ℝ) * H) := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
        _ ≤ ∑ s : P → Bool, (μ s).toReal *
              (((Finset.univ.filter fun j => s j = true).card : ℝ) * L) :=
            Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
              (card_recovered_mul_le hη.le M (Finset.univ.filter fun j => s j = true))
              ENNReal.toReal_nonneg
        _ = (p : ℝ) * n * L := by
            simp_rw [← mul_assoc]
            rw [← Finset.sum_mul, bernoulli_expected_card p]
    -- Each bit `i` is recovered with probability at least `1 / 2`.
    have hrec_lower : k * (1 / 2) ≤ ∑ s : P → Bool, (μ s).toReal *
        ((Finset.univ.filter fun i : ι => ∃ e ∈ (M i).edges,
          e ⊆ Finset.univ.filter fun j => s j = true).card : ℝ) := by
      have hcard (s : P → Bool) :
          ((Finset.univ.filter fun i : ι => ∃ e ∈ (M i).edges,
            e ⊆ Finset.univ.filter fun j => s j = true).card : ℝ) =
            ∑ i : ι, if ∃ e ∈ (M i).edges, ∀ j ∈ e, s j = true then (1 : ℝ) else 0 := by
        rw [Finset.sum_boole]
        congr 2
        ext i
        simp [Finset.subset_iff]
      simp_rw [hcard, Finset.mul_sum]
      rw [Finset.sum_comm]
      have hbit (i : ι) : (1 / 2 : ℝ) ≤ ∑ s : P → Bool, (μ s).toReal *
          if ∃ e ∈ (M i).edges, ∀ j ∈ e, s j = true then (1 : ℝ) else 0 := by
        have hmeas_eq : (∑ s : P → Bool, (μ s).toReal *
              if ∃ e ∈ (M i).edges, ∀ j ∈ e, s j = true then (1 : ℝ) else 0) =
            (μ.toOuterMeasure {s | ∃ e ∈ (M i).edges, ∀ j ∈ e, s j = true}).toReal := by
          rw [Probability.PMF.toOuterMeasure_toReal_eq_sum_ite]
          simp only [Set.mem_ofPred_eq]
        rw [hmeas_eq]
        refine le_trans ?_ (bernoulli_hit_ge (M i) p)
        have hm : 1 ≤ (M i).edges.card * (p : ℝ) ^ q := by
          rw [hpq]
          simpa only [mul_inv_cancel₀ (by linarith : α * n ≠ 0)] using
            mul_le_mul_of_nonneg_right (hsize i) (inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ α * n))
        rw [le_div_iff₀ (by linarith)]; linarith
      calc
        k * (1 / 2) = ∑ _i : ι, (1 / 2 : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum fun i _ => hbit i
    -- Combine `k * H ≤ 2 * L * p * n` and raise to power `q`.
    have hlin : k * H ≤ (2 * L) * ((p : ℝ) * n) := by
      have := mul_le_mul_of_nonneg_right hrec_lower hH0
      linarith
    have hpow := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hH0) hlin q
    calc
      α * (k * H) ^ q ≤ α * ((2 * L) * ((p : ℝ) * n)) ^ q :=
        mul_le_mul_of_nonneg_left hpow hα.le
      _ = (2 * L) ^ q * n ^ (q - 1) := by
        simp only [mul_pow, hpq, hnq]
        have hαn : α * n ≠ 0 := (mul_pos hα hn).ne'
        field_simp [hαn]

end MatchingRestriction

/-! ### Auxiliary lemmas for code lower bounds -/

section Helpers

/-- Pinsker bound on binary entropy: for `0 ≤ η ≤ 1 / 2`,
`2 * η ^ 2 ≤ 1 - Real.binEntropy (1 / 2 + η) / Real.log 2`. -/
private theorem two_mul_sq_le_one_sub_binEntropy {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 2) :
    2 * η ^ 2 ≤ 1 - Real.binEntropy (1 / 2 + η) / Real.log 2 := by
  let q : I := ⟨1 / 2 + η, ⟨by linarith, by linarith⟩⟩
  let p := PMF.coin q
  let u := PMF.uniformOfFintype Bool
  have hpinsker := PMF.two_mul_dist_sq_le_sum_mul_log_div (p := p) (q := u)
    fun b _ => by simp [u, PMF.mem_support_iff, PMF.uniformOfFintype_apply]
  have hdist : dist p u = η := by
    rw [PMF.dist_uniformOfFintype_bool, PMF.coin_apply_toReal, ite_eq_left rfl]
    change |(1 / 2 + η) - 1 / 2| = η
    rw [add_sub_cancel_left, abs_of_nonneg hη0]
  have hkl : ∑ b : Bool, (p b).toReal * Real.log ((p b).toReal / (u b).toReal) =
      Real.log 2 - Real.binEntropy (1 / 2 + η) := by
    rw [Fintype.sum_bool, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    have hterm (x : ℝ) (hx : 0 ≤ x) :
        x * Real.log (x / (2 : ℝ)⁻¹) = -Real.negMulLog x + x * Real.log 2 := by
      rcases hx.eq_or_lt with rfl | hxpos
      · simp [Real.negMulLog_zero]
      · rw [div_inv_eq_mul, Real.log_mul hxpos.ne' two_ne_zero, Real.negMulLog]; ring
    simp only [p, q, u, PMF.uniformOfFintype_apply, PMF.coin_apply_toReal, Fintype.card_bool,
      Nat.cast_ofNat, ENNReal.toReal_inv, ENNReal.toReal_ofNat, ↓reduceIte, Bool.false_eq_true]
    rw [show 1 - (1 / 2 + η) = 1 / 2 - η by ring,
      hterm (1 / 2 + η) (by linarith), hterm (1 / 2 - η) (by linarith)]
    ring
  rw [hdist, hkl] at hpinsker
  have hlog_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [show 1 - Real.binEntropy (1 / 2 + η) / Real.log 2 =
      (Real.log 2 - Real.binEntropy (1 / 2 + η)) / Real.log 2 by field_simp [hlog_pos.ne'],
    le_div_iff₀ hlog_pos]
  nlinarith [sq_nonneg η, Real.log_two_lt_d9]

/-- Convert `A * k ^ q ≤ B * n ^ (q - 1)` into `(A / B) ^ (1 / (q - 1)) * k ^ (q / (q - 1)) ≤ n`
for `2 ≤ q` and `0 < B`. -/
private theorem rpow_le_of_pow_le_pow {q : ℕ} (hq : 2 ≤ q) {A B k n : ℝ}
    (hA : 0 ≤ A) (hB : 0 < B) (hk : 0 ≤ k) (hn : 0 ≤ n)
    (h : A * k ^ q ≤ B * n ^ (q - 1)) :
    (A / B) ^ (1 / ((q : ℝ) - 1)) * k ^ ((q : ℝ) / ((q : ℝ) - 1)) ≤ n := by
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hdiv : (A / B) * k ^ q ≤ n ^ (q - 1) := by rw [div_mul_eq_mul_div, div_le_iff₀ hB]; linarith
  have hexp_nn : 0 ≤ 1 / ((q : ℝ) - 1) := by positivity
  have hrpow := Real.rpow_le_rpow (by positivity) hdiv hexp_nn
  rw [Real.mul_rpow (div_nonneg hA hB.le) (pow_nonneg hk q),
    ← Real.rpow_natCast k q, ← Real.rpow_mul hk,
    ← Real.rpow_natCast n (q - 1), ← Real.rpow_mul hn, Nat.cast_sub (by omega), Nat.cast_one,
    show (q : ℝ) * (1 / ((q : ℝ) - 1)) = (q : ℝ) / ((q : ℝ) - 1) by ring,
    show ((q : ℝ) - 1) * (1 / ((q : ℝ) - 1)) = 1 by field_simp [hq1.ne'], Real.rpow_one] at hrpow
  exact hrpow

/-- Over an empty position set `P`, no code with nonempty messages admits a decoder achieving
advantage `ε > 0` on all codewords. -/
private theorem isEmpty_of_isEmpty_pos [Finite ι] [IsEmpty P]
    {C : (ι → Bool) → P → Γ} {A : LocalDecoder ι P Γ} {ε : ℝ} (hε : 0 < ε)
    (hcorr : ∀ x i, 1 / 2 + ε ≤ (decodeLaw (A i) (C x) (x i)).toReal) : IsEmpty ι := by
  classical
  let := Fintype.ofFinite ι
  refine ⟨fun i => ?_⟩
  let z : P → Γ := isEmptyElim
  have heq (x : ι → Bool) : C x = z := funext isEmptyElim
  let U := PMF.uniformOfFintype (ι → Bool)
  have havg : ∑ x : ι → Bool, (U x).toReal * (decodeLaw (A i) z (x i)).toReal = 1 / 2 := by
    have hU : U = PMF.pi fun _ : ι => PMF.uniformOfFintype Bool := by
      ext x; simp [U, PMF.uniformOfFintype_apply, PMF.pi_apply, ENNReal.inv_pow]
    rw [hU, Probability.PMF.sum_pi_mul_eval (fun _ : ι => PMF.uniformOfFintype Bool) i
      (fun b => (decodeLaw (A i) z b).toReal), Fintype.sum_bool]
    have hsum := toReal_decodeLaw_add_not z (A i) true
    simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat, ENNReal.toReal_inv,
      ENNReal.toReal_ofNat, Bool.not_true] at hsum ⊢
    linarith
  have hge : 1 / 2 + ε ≤ ∑ x : ι → Bool, (U x).toReal * (decodeLaw (A i) z (x i)).toReal := by
    calc
      (1 / 2 + ε : ℝ) = ∑ x : ι → Bool, (U x).toReal * (1 / 2 + ε) := by
        rw [← Finset.sum_mul, Probability.PMF.sum_toReal, one_mul]
      _ ≤ ∑ x : ι → Bool, (U x).toReal * (decodeLaw (A i) z (x i)).toReal :=
        Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (heq x ▸ hcorr x i) ENNReal.toReal_nonneg
  linarith

end Helpers

/-! ### Katz–Trevisan lower bounds for smooth and locally decodable codes -/

section Bounds

/-- **Katz–Trevisan bound for non-adaptive smooth codes** [KatzTrevisan2000], [Yekhanin2012]:
every non-adaptive `(q, c, ε)` smooth decoder (`1 ≤ q`, `0 < c`, `0 < ε`) satisfies
`ε · (|ι| · (1 - h₂(1 / 2 + ε / 2))) ^ q ≤ q · c · (2 log₂ |Γ|) ^ q · |P| ^ (q - 1)`. -/
theorem IsSmoothDecoder.pow_le_pow_of_nonadaptivePlan [Fintype ι] [Fintype P] [DecidableEq P]
    [Fintype Γ] [Nonempty Γ] {C : (ι → Bool) → P → Γ} {q : ℕ} {c ε : ℝ}
    {planLaw : ι → ProbComp (NonadaptivePlan P Γ q)}
    (hA : IsSmoothDecoder C q c ε fun i => nonadaptivePlan (planLaw i))
    (hq : 1 ≤ q) (hc : 0 < c) (hε : 0 < ε) :
    ε * ((Fintype.card ι : ℝ) * (1 - Real.binEntropy (1 / 2 + ε / 2) / Real.log 2)) ^ q ≤
      q * c * (2 * Real.logb 2 (Fintype.card Γ)) ^ q * (Fintype.card P : ℝ) ^ (q - 1) := by
  classical
  by_cases hP : Nonempty P
  · have hqc : (0 : ℝ) < (q : ℝ) * c := mul_pos (by exact_mod_cast hq) hc
    have hM (i : ι) : ∃ M : DecodingMatching C i q (ε / 2),
        (ε / ((q : ℝ) * c)) * Fintype.card P ≤ M.edges.card := by
      obtain ⟨M, hle⟩ := hA.exists_decodingMatching_of_nonadaptivePlan hε i
      exact ⟨M, by rw [div_mul_eq_mul_div, div_le_iff₀ hqc]; linarith⟩
    choose M hMsize using hM
    have hmul := mul_le_mul_of_nonneg_left
      (DecodingMatching.pow_le_pow M hq (div_pos hε hqc) (by linarith) hMsize) hqc.le
    have hlhs : (q : ℝ) * c * (ε / ((q : ℝ) * c) *
        ((Fintype.card ι : ℝ) * (1 - Real.binEntropy (1 / 2 + ε / 2) / Real.log 2)) ^ q) =
        ε * ((Fintype.card ι : ℝ) * (1 - Real.binEntropy (1 / 2 + ε / 2) / Real.log 2)) ^ q := by
      field_simp [hqc.ne']
    rw [hlhs] at hmul
    linarith
  · have : IsEmpty P := not_nonempty_iff.mp hP
    have : IsEmpty ι := isEmpty_of_isEmpty_pos hε hA.correct
    simp only [Fintype.card_eq_zero, Nat.cast_zero, zero_mul, zero_pow (by omega : q ≠ 0), mul_zero]
    have hL : 0 ≤ Real.logb 2 (Fintype.card Γ) :=
      Real.logb_nonneg one_lt_two (by exact_mod_cast Fintype.card_pos (α := Γ))
    positivity

/-- **Katz–Trevisan bound for non-adaptive locally decodable codes** [KatzTrevisan2000],
[Yekhanin2012]: every non-adaptive `(q, δ, ε)` local decoder (`1 ≤ q`, `0 < δ`, `0 < ε`) satisfies
`δ · ε · (|ι| · (1 - h₂(1 / 2 + ε / 2))) ^ q ≤ q ^ 2 · (2 log₂ |Γ|) ^ q · |P| ^ (q - 1)`. -/
theorem IsLocalDecoder.pow_le_pow_of_nonadaptivePlan [Fintype ι] [Fintype P]
    [Fintype Γ] [Nonempty Γ] [DecidableEq Γ] {C : (ι → Bool) → P → Γ} {q : ℕ} {δ ε : ℝ}
    {planLaw : ι → ProbComp (NonadaptivePlan P Γ q)}
    (hA : IsLocalDecoder C q δ ε fun i => nonadaptivePlan (planLaw i))
    (hq : 1 ≤ q) (hδ : 0 < δ) (hε : 0 < ε) :
    δ * ε * ((Fintype.card ι : ℝ) * (1 - Real.binEntropy (1 / 2 + ε / 2) / Real.log 2)) ^ q ≤
      (q : ℝ) ^ 2 * (2 * Real.logb 2 (Fintype.card Γ)) ^ q * (Fintype.card P : ℝ) ^ (q - 1) := by
  classical
  have hmul := mul_le_mul_of_nonneg_left
    ((isSmoothDecoder_mask_nonadaptivePlan hA hδ (C fun _ => false)).pow_le_pow_of_nonadaptivePlan
      hq (div_pos (by exact_mod_cast hq) hδ) hε) hδ.le
  have hrhs : δ * ((q : ℝ) * ((q : ℝ) / δ) * (2 * Real.logb 2 (Fintype.card Γ)) ^ q *
      (Fintype.card P : ℝ) ^ (q - 1)) =
      (q : ℝ) ^ 2 * (2 * Real.logb 2 (Fintype.card Γ)) ^ q * (Fintype.card P : ℝ) ^ (q - 1) := by
    field_simp [hδ.ne']
  rw [hrhs] at hmul
  linarith

/-- **Katz–Trevisan `Ω(k ^ (q / (q - 1)))` bound for non-adaptive `q`-query LDCs**
[KatzTrevisan2000], [Yekhanin2012]: for `2 ≤ q` and `2 ≤ |Γ|`, every non-adaptive `(q, δ, ε)`
local decoder satisfies `n ≥ c(q, δ, ε, |Γ|) · k ^ (q / (q - 1))` with explicit constant
`(δ · ε ^ (2q + 1) / (q ^ 2 · (4 log₂ |Γ|) ^ q)) ^ (1 / (q - 1))`. -/
theorem IsLocalDecoder.rpow_le_card_of_nonadaptivePlan [Fintype ι] [Fintype P]
    [Fintype Γ] [DecidableEq Γ] {C : (ι → Bool) → P → Γ} {q : ℕ} {δ ε : ℝ}
    {planLaw : ι → ProbComp (NonadaptivePlan P Γ q)}
    (hA : IsLocalDecoder C q δ ε fun i => nonadaptivePlan (planLaw i))
    (hq : 2 ≤ q) (hΓ : 2 ≤ Fintype.card Γ) (hδ : 0 < δ) (hε : 0 < ε) :
    (δ * ε ^ (2 * q + 1) / ((q : ℝ) ^ 2 * (4 * Real.logb 2 (Fintype.card Γ)) ^ q)) ^
        (1 / ((q : ℝ) - 1)) * (Fintype.card ι : ℝ) ^ ((q : ℝ) / ((q : ℝ) - 1)) ≤
      Fintype.card P := by
  have : Nonempty Γ := Fintype.card_pos_iff.mp (by omega)
  have hlog_pos : 0 < Real.logb 2 (Fintype.card Γ) :=
    Real.logb_pos one_lt_two (by exact_mod_cast (by omega : 1 < Fintype.card Γ))
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hB : 0 < (q : ℝ) ^ 2 * (4 * Real.logb 2 (Fintype.card Γ)) ^ q := by positivity
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hk0 | hkpos
  · have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
      have : (2 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    rw [hk0, Nat.cast_zero, Real.zero_rpow (div_pos hqpos hq1).ne', mul_zero]
    exact Nat.cast_nonneg _
  · obtain ⟨i₀⟩ := Fintype.card_pos_iff.mp hkpos
    have hε_le : ε ≤ 1 / 2 := by
      have hc := hA.correct (fun _ => false) (C fun _ => false) i₀
        (by simp [mul_nonneg hδ.le (Nat.cast_nonneg _)])
      linarith [Probability.PMF.toReal_apply_le_one
        (decodeLaw (nonadaptivePlan (planLaw i₀)) (C fun _ => false)) false]
    have hpinsker : ε ^ 2 / 2 ≤ 1 - Real.binEntropy (1 / 2 + ε / 2) / Real.log 2 := by
      linarith [two_mul_sq_le_one_sub_binEntropy (η := ε / 2) (by linarith) (by linarith),
        show 2 * (ε / 2) ^ 2 = ε ^ 2 / 2 by ring]
    have h1 := (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hpinsker (Nat.cast_nonneg _)) q)
      (mul_pos hδ hε).le).trans (hA.pow_le_pow_of_nonadaptivePlan (by omega) hδ hε)
    have h2 := mul_le_mul_of_nonneg_left h1 (pow_nonneg zero_le_two q)
    have hpoly : δ * ε ^ (2 * q + 1) * (Fintype.card ι : ℝ) ^ q ≤
        (q : ℝ) ^ 2 * (4 * Real.logb 2 (Fintype.card Γ)) ^ q * (Fintype.card P : ℝ) ^ (q - 1) := by
      have hlhs : (2 : ℝ) ^ q * (δ * ε * ((Fintype.card ι : ℝ) * (ε ^ 2 / 2)) ^ q) =
          δ * ε ^ (2 * q + 1) * (Fintype.card ι : ℝ) ^ q := by
        rw [mul_pow, div_pow, ← pow_mul, pow_add, pow_one]
        field_simp
      have h4 : (4 * Real.logb 2 (Fintype.card Γ)) ^ q =
          (2 : ℝ) ^ q * (2 * Real.logb 2 (Fintype.card Γ)) ^ q := by
        rw [← mul_pow]
        congr 1
        ring
      have hrhs : (2 : ℝ) ^ q * ((q : ℝ) ^ 2 * (2 * Real.logb 2 (Fintype.card Γ)) ^ q *
          (Fintype.card P : ℝ) ^ (q - 1)) =
          (q : ℝ) ^ 2 * (4 * Real.logb 2 (Fintype.card Γ)) ^ q *
            (Fintype.card P : ℝ) ^ (q - 1) := by
        rw [h4]
        ring
      rwa [hlhs, hrhs] at h2
    exact rpow_le_of_pow_le_pow hq (by positivity) hB (Nat.cast_nonneg _) (Nat.cast_nonneg _) hpoly

/-- **Katz–Trevisan bound for arbitrary (possibly adaptive) locally decodable codes**
[KatzTrevisan2000], [Yekhanin2012]: every `(q, δ, ε)` locally decodable code (`1 ≤ q`, `0 < δ`,
`0 < ε`) over a finite nonempty alphabet `Γ` satisfies
`δ · ε · (|ι| · (1 - h₂(1 / 2 + ε / (2 |Γ| ^ (q - 1))))) ^ q ≤
  q ^ 2 · |Γ| ^ (q - 1) · (2 log₂ |Γ|) ^ q · |P| ^ (q - 1)`.
For `q = 1` the factor `|Γ| ^ (q - 1)` is `1` and `|P| ^ (q - 1)` is `1`, giving an explicit
logarithmic-in-`|Γ|` upper bound on `|ι|`. -/
theorem IsLocallyDecodable.pow_le_pow [Fintype ι] [Fintype P] [Fintype Γ] [Nonempty Γ]
    [DecidableEq Γ] {C : (ι → Bool) → P → Γ} {q : ℕ} {δ ε : ℝ}
    (hC : IsLocallyDecodable C q δ ε) (hq : 1 ≤ q) (hδ : 0 < δ) (hε : 0 < ε) :
    δ * ε * ((Fintype.card ι : ℝ) *
      (1 - Real.binEntropy (1 / 2 + ε / (2 * (Fintype.card Γ : ℝ) ^ (q - 1))) /
        Real.log 2)) ^ q ≤
      (q : ℝ) ^ 2 * (Fintype.card Γ : ℝ) ^ (q - 1) *
        (2 * Real.logb 2 (Fintype.card Γ)) ^ q * (Fintype.card P : ℝ) ^ (q - 1) := by
  classical
  obtain ⟨A, hA⟩ := isLocallyDecodable_iff.mp hC
  have hΓ : (0 : ℝ) < (Fintype.card Γ : ℝ) ^ (q - 1) := by positivity
  have hbound := hA.nonadaptivize.pow_le_pow_of_nonadaptivePlan hq hδ (div_pos hε hΓ)
  rw [show ε / (Fintype.card Γ : ℝ) ^ (q - 1) / 2 =
      ε / (2 * (Fintype.card Γ : ℝ) ^ (q - 1)) by ring] at hbound
  have hmul := mul_le_mul_of_nonneg_left hbound hΓ.le
  have hlhs : (Fintype.card Γ : ℝ) ^ (q - 1) * (δ * (ε / (Fintype.card Γ : ℝ) ^ (q - 1)) *
      ((Fintype.card ι : ℝ) *
        (1 - Real.binEntropy (1 / 2 + ε / (2 * (Fintype.card Γ : ℝ) ^ (q - 1))) /
          Real.log 2)) ^ q) =
      δ * ε * ((Fintype.card ι : ℝ) *
        (1 - Real.binEntropy (1 / 2 + ε / (2 * (Fintype.card Γ : ℝ) ^ (q - 1))) /
          Real.log 2)) ^ q := by
    field_simp [hΓ.ne']
  rw [hlhs] at hmul
  linarith

/-- **Katz–Trevisan `Ω(k ^ (q / (q - 1)))` lower bound for arbitrary (possibly adaptive) `q`-query
locally decodable codes** [KatzTrevisan2000], [Yekhanin2012]: for `2 ≤ q`, `2 ≤ |Γ|`, `0 < δ`, and
`0 < ε`, every `(q, δ, ε)` locally decodable code satisfies
`n ≥ c(q, δ, ε, |Γ|) · k ^ (q / (q - 1))` with explicit constant
`(δ · ε ^ (2q + 1) / (q ^ 2 · |Γ| ^ ((q - 1)(2q + 1)) · (4 log₂ |Γ|) ^ q)) ^ (1 / (q - 1))`. -/
theorem IsLocallyDecodable.rpow_le_card [Fintype ι] [Fintype P] [Fintype Γ] [DecidableEq Γ]
    {C : (ι → Bool) → P → Γ} {q : ℕ} {δ ε : ℝ}
    (hC : IsLocallyDecodable C q δ ε) (hq : 2 ≤ q) (hΓ : 2 ≤ Fintype.card Γ)
    (hδ : 0 < δ) (hε : 0 < ε) :
    (δ * ε ^ (2 * q + 1) / ((q : ℝ) ^ 2 * (Fintype.card Γ : ℝ) ^ ((q - 1) * (2 * q + 1)) *
        (4 * Real.logb 2 (Fintype.card Γ)) ^ q)) ^ (1 / ((q : ℝ) - 1)) *
        (Fintype.card ι : ℝ) ^ ((q : ℝ) / ((q : ℝ) - 1)) ≤
      Fintype.card P := by
  classical
  have : Nonempty Γ := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨A, hA⟩ := isLocallyDecodable_iff.mp hC
  have hΓpos : (0 : ℝ) < (Fintype.card Γ : ℝ) ^ (q - 1) := by positivity
  have h := hA.nonadaptivize.rpow_le_card_of_nonadaptivePlan hq hΓ hδ (div_pos hε hΓpos)
  have hconst : δ * (ε / (Fintype.card Γ : ℝ) ^ (q - 1)) ^ (2 * q + 1) /
      ((q : ℝ) ^ 2 * (4 * Real.logb 2 (Fintype.card Γ)) ^ q) =
      δ * ε ^ (2 * q + 1) / ((q : ℝ) ^ 2 * (Fintype.card Γ : ℝ) ^ ((q - 1) * (2 * q + 1)) *
        (4 * Real.logb 2 (Fintype.card Γ)) ^ q) := by
    rw [div_pow, ← pow_mul]
    field_simp [hΓpos.ne']
  rwa [hconst] at h

end Bounds

end Cslib.Code
