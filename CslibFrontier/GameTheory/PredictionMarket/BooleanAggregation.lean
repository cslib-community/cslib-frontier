/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.GameTheory.MixedStrategy
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Distributed computation through Boolean prediction markets

This module formalizes the synchronous Shapley–Shubik Boolean prediction market model and its
information-aggregation characterization from [PennockSami2007, §26.5, pp. 666–670].

## Model and conventions

There are `n` agents (`i : Fin n`, with `0 < n`), each holding a private bit `x i : Bool` of the
true state `x : Fin n → Bool`, and a Boolean security `f : (Fin n → Bool) → Bool` paying `$1` if
`f x = true` and `$0` otherwise, evaluated under a common prior `P : (Fin n → Bool) → ℝ`
(`IsMixedStrategy P`).

* **Positive-mass initial support (`priorSupport P`):** We initialize the common-knowledge
  possibility set at `S⁰ = priorSupport P = {y | 0 < P y}` rather than `Finset.univ` when `P` has
  zero-probability states. Under Bayesian updating, zero-prior states carry zero posterior mass;
  restricting `S⁰` to positive-mass states guarantees that every agent's conditioning event
  `agentKnowledge Sʳ i y` has strictly positive prior mass for every `y ∈ Sʳ`, avoiding division by
  zero in conditional expectations (`0 / 0 = 0` in Lean). When `P` has full support,
  `priorSupport P = Finset.univ`.
* **Round indexing (`commonKnowledge f P x r`):** Following [PennockSami2007, §26.5.4, p. 668],
  `commonKnowledge f P x r` is the common-knowledge possibility set `Sʳ` *after `r` rounds of
  trading* (`S⁰ = priorSupport P`, `Sʳ⁺¹ = {y ∈ Sʳ | roundPrice f P Sʳ y = roundPrice f P Sʳ x}`).
  In particular, `roundPrice f P (S⁰) x` is the first-round clearing price `p¹`, and
  `roundPrice f P (Sʳ) x` is the clearing price formed from common knowledge after `r` rounds.
* **Equilibrium in at most `n` rounds:** On any `Sʳ`, each agent's bid depends only on her single
  bit, so `roundPrice f P Sʳ` is an affine function on `{0, 1}ⁿ ⊆ ℝⁿ`. Every strict refinement
  `Sʳ⁺¹ ⊂ Sʳ` strictly decreases the affine dimension `finrank ℝ (vectorSpan ℝ (embed '' Sʳ))`, so
  for *every* Boolean function `f` and positive-mass state `x`, the common-knowledge set stabilizes
  by round `n`: `Sⁿ⁺¹ = Sⁿ`. We therefore define `eqSet f P x := commonKnowledge f P x n` and
  `eqPrice f P x := roundPrice f P (eqSet f P x) x`, and prove they agree with any stabilizing
  round.

## Main definitions

* `Cslib.GameTheory.PredictionMarket.priorSupport`: positive-probability states `{y | 0 < P y}`.
* `Cslib.GameTheory.PredictionMarket.agentKnowledge`: agent `i`'s possibility set
  `{z ∈ S | z i = y i}`.
* `Cslib.GameTheory.PredictionMarket.condExpect`: conditional probability `P(f = true | A)`.
* `Cslib.GameTheory.PredictionMarket.agentBid`: myopic truthful bid
  `condExpect f P (agentKnowledge S i y)`.
* `Cslib.GameTheory.PredictionMarket.roundPrice`: unit-quantity Shapley–Shubik clearing price
  `(∑ i, agentBid f P S i y) / n` [PennockSami2007, §26.5.2, p. 666].
* `Cslib.GameTheory.PredictionMarket.commonKnowledge`: common-knowledge set `Sʳ` after `r` rounds
  [PennockSami2007, §26.5.4, p. 668].
* `Cslib.GameTheory.PredictionMarket.eqSet`, `Cslib.GameTheory.PredictionMarket.eqPrice`:
  equilibrium common-knowledge set `S^∞` and equilibrium price `p^∞`.
* `Cslib.GameTheory.PredictionMarket.IsWeightedThreshold`: weighted threshold functions
  `f x = true ↔ 1 ≤ w₀ + ∑ i, w i * x_i` [PennockSami2007, Definition 26.11, p. 669].
* `Cslib.GameTheory.PredictionMarket.carryChain`, `Cslib.GameTheory.PredictionMarket.carryPrior`:
  the `2n`-input nested carry-chain threshold function `Cₙ` and inductive prior `Pₙ` realizing the
  worst-case `n`-round lower bound [PennockSami2007, Theorem 26.15, p. 669].

## Main results

* `Cslib.GameTheory.PredictionMarket.orMarket_bids_and_eqPrice`: two-agent OR market under the
  uniform prior (`b₁ = 1/2`, `b₂ = 1`, `p¹ = 3/4`, `p^∞ = 1`) [PennockSami2007, Example 26.8,
  p. 667].
* `Cslib.GameTheory.PredictionMarket.eq_condExpect_and_agentBid_of_roundPrice_const`,
  `Cslib.GameTheory.PredictionMarket.equilibrium_commonKnowledge_of_aggregates`: common knowledge
  of aggregates at equilibrium, `P(f = 1 | S^∞) = p^∞` and `∀ i, P(f = 1 | Sᵢ^∞) = p^∞`
  [PennockSami2007, Theorem 26.9, Eqs. (26.1)–(26.2), p. 668].
* `Cslib.GameTheory.PredictionMarket.xorMarket_bids_and_eqPrice`,
  `Cslib.GameTheory.PredictionMarket.not_isWeightedThreshold_xor`: two-agent XOR non-revelation
  under the uniform prior (`p¹ = p^∞ = 1/2 ≠ f x`) [PennockSami2007, Example 26.10, pp. 668–669].
* `Cslib.GameTheory.PredictionMarket.eqPrice_eq_of_isWeightedThreshold`: sufficiency of weighted
  threshold functions for truthful equilibrium aggregation under every prior [PennockSami2007,
  Theorem 26.12, p. 669].
* `Cslib.GameTheory.PredictionMarket.exists_prior_eqPrice_eq_half_of_not_isWeightedThreshold`:
  necessity via Hahn–Banach separation of convex hulls, constructing a prior stuck at `p^∞ = 1/2`
  [PennockSami2007, Theorem 26.13, p. 669].
* `Cslib.GameTheory.PredictionMarket.isWeightedThreshold_iff_forall_eqPrice_eq`: necessary and
  sufficient characterization combining Theorems 26.12 and 26.13.
* `Cslib.GameTheory.PredictionMarket.commonKnowledge_succ_eq_self_at_n`,
  `Cslib.GameTheory.PredictionMarket.convergence_in_n_rounds_of_isWeightedThreshold`: convergence
  to equilibrium in at most `n` rounds by affine-dimension drop [PennockSami2007, Theorem 26.14,
  p. 669].
* `Cslib.GameTheory.PredictionMarket.carryChain_convergence_rounds`,
  `Cslib.GameTheory.PredictionMarket.exists_n_round_lower_bound`: `n`-round worst-case lower bound
  on `2n` inputs using the weighted threshold carry chain `Cₙ` and inductive prior `Pₙ`
  [PennockSami2007, Theorem 26.15, p. 669].

## References

* [D. M. Pennock, R. Sami, *Computational Aspects of Prediction Markets*, Chapter 26 of
  *Algorithmic Game Theory*, §26.5, pp. 666–670][PennockSami2007]
-/

public section

open Finset

namespace Cslib.GameTheory.PredictionMarket

/-! ### Boolean Market Model (§26.5.1–26.5.4) -/

section Model

variable {n : ℕ}

/-- The set of positive-probability states `{y | 0 < P y}` under prior `P`. -/
noncomputable def priorSupport (P : (Fin n → Bool) → ℝ) : Finset (Fin n → Bool) :=
  letI := Classical.decPred fun y : Fin n → Bool => 0 < P y
  Finset.univ.filter fun y => 0 < P y

@[simp]
theorem mem_priorSupport {P : (Fin n → Bool) → ℝ} {y : Fin n → Bool} :
    y ∈ priorSupport P ↔ 0 < P y := by
  classical
  simp [priorSupport]

/-- Agent `i`'s knowledge set `{z ∈ S | z i = y i}` at state `y` given common knowledge `S`
[PennockSami2007, §26.5.4, p. 668]. -/
def agentKnowledge (S : Finset (Fin n → Bool)) (i : Fin n) (y : Fin n → Bool) :
    Finset (Fin n → Bool) :=
  S.filter fun z => z i = y i

@[simp]
theorem mem_agentKnowledge {S : Finset (Fin n → Bool)} {i : Fin n} {y z : Fin n → Bool} :
    z ∈ agentKnowledge S i y ↔ z ∈ S ∧ z i = y i := by
  simp [agentKnowledge]

/-- Conditional expectation `P(f(z) = 1 | z ∈ A)` of the Boolean security `f` over `A`. -/
noncomputable def condExpect (f : (Fin n → Bool) → Bool) (P : (Fin n → Bool) → ℝ)
    (A : Finset (Fin n → Bool)) : ℝ :=
  (∑ z ∈ A, if f z then P z else 0) / ∑ z ∈ A, P z

@[simp]
theorem condExpect_apply (f : (Fin n → Bool) → Bool) (P : (Fin n → Bool) → ℝ)
    (A : Finset (Fin n → Bool)) :
    condExpect f P A = (∑ z ∈ A, if f z then P z else 0) / ∑ z ∈ A, P z := by
  rfl

/-- Myopic truthful bid of agent `i` at state `y` given common knowledge `S`:
`b_i(y) = P(f(z) = 1 | z ∈ S_i(y))` [PennockSami2007, §26.5.3–26.5.4, pp. 667–668]. -/
noncomputable def agentBid (f : (Fin n → Bool) → Bool) (P : (Fin n → Bool) → ℝ)
    (S : Finset (Fin n → Bool)) (i : Fin n) (y : Fin n → Bool) : ℝ :=
  condExpect f P (agentKnowledge S i y)

@[simp]
theorem agentBid_apply (f : (Fin n → Bool) → Bool) (P : (Fin n → Bool) → ℝ)
    (S : Finset (Fin n → Bool)) (i : Fin n) (y : Fin n → Bool) :
    agentBid f P S i y = condExpect f P (agentKnowledge S i y) := by
  rfl

/-- Unit-quantity (`q_i = 1`) Shapley–Shubik market clearing price
`p(y) = (∑ i, agentBid f P S i y) / n` [PennockSami2007, §26.5.2, p. 666]. -/
noncomputable def roundPrice (f : (Fin n → Bool) → Bool) (P : (Fin n → Bool) → ℝ)
    (S : Finset (Fin n → Bool)) (y : Fin n → Bool) : ℝ :=
  (∑ i : Fin n, agentBid f P S i y) / n

@[simp]
theorem roundPrice_apply (f : (Fin n → Bool) → Bool) (P : (Fin n → Bool) → ℝ)
    (S : Finset (Fin n → Bool)) (y : Fin n → Bool) :
    roundPrice f P S y = (∑ i : Fin n, agentBid f P S i y) / n := by
  rfl

/-- Common-knowledge possibility set `Sʳ` after `r` rounds of trading when the true state is `x`,
initialized at `S⁰ = priorSupport P` [PennockSami2007, §26.5.4, p. 668]. -/
noncomputable def commonKnowledge (f : (Fin n → Bool) → Bool) (P : (Fin n → Bool) → ℝ)
    (x : Fin n → Bool) : ℕ → Finset (Fin n → Bool)
  | 0 => priorSupport P
  | r + 1 =>
    letI := Classical.decPred fun y : Fin n → Bool =>
      roundPrice f P (commonKnowledge f P x r) y = roundPrice f P (commonKnowledge f P x r) x
    (commonKnowledge f P x r).filter fun y =>
      roundPrice f P (commonKnowledge f P x r) y = roundPrice f P (commonKnowledge f P x r) x

@[simp]
theorem commonKnowledge_zero (f : (Fin n → Bool) → Bool) (P : (Fin n → Bool) → ℝ)
    (x : Fin n → Bool) :
    commonKnowledge f P x 0 = priorSupport P := by
  rfl

theorem mem_commonKnowledge_succ {f : (Fin n → Bool) → Bool} {P : (Fin n → Bool) → ℝ}
    {x y : Fin n → Bool} {r : ℕ} :
    y ∈ commonKnowledge f P x (r + 1) ↔
      y ∈ commonKnowledge f P x r ∧
        roundPrice f P (commonKnowledge f P x r) y =
          roundPrice f P (commonKnowledge f P x r) x := by
  classical
  simp [commonKnowledge]

theorem commonKnowledge_succ_subset (f : (Fin n → Bool) → Bool) (P : (Fin n → Bool) → ℝ)
    (x : Fin n → Bool) (r : ℕ) :
    commonKnowledge f P x (r + 1) ⊆ commonKnowledge f P x r :=
  fun _ hy => (mem_commonKnowledge_succ.mp hy).1

theorem commonKnowledge_antitone (f : (Fin n → Bool) → Bool) (P : (Fin n → Bool) → ℝ)
    (x : Fin n → Bool) : Antitone (commonKnowledge f P x) :=
  antitone_nat_of_succ_le (commonKnowledge_succ_subset f P x)

theorem commonKnowledge_subset_priorSupport (f : (Fin n → Bool) → Bool) (P : (Fin n → Bool) → ℝ)
    (x : Fin n → Bool) (r : ℕ) :
    commonKnowledge f P x r ⊆ priorSupport P :=
  commonKnowledge_antitone f P x (Nat.zero_le r)

theorem mem_commonKnowledge_self {f : (Fin n → Bool) → Bool} {P : (Fin n → Bool) → ℝ}
    {x : Fin n → Bool} (hx : 0 < P x) : ∀ r, x ∈ commonKnowledge f P x r
  | 0 => mem_priorSupport.mpr hx
  | r + 1 => mem_commonKnowledge_succ.mpr ⟨mem_commonKnowledge_self hx r, rfl⟩

/-- Once `Sʳ⁺¹ = Sʳ`, common knowledge remains constant for all later rounds `k ≥ r`. -/
theorem commonKnowledge_eq_of_eq_succ {f : (Fin n → Bool) → Bool} {P : (Fin n → Bool) → ℝ}
    {x : Fin n → Bool} {r : ℕ}
    (hstab : commonKnowledge f P x (r + 1) = commonKnowledge f P x r) :
    ∀ k, r ≤ k → commonKnowledge f P x k = commonKnowledge f P x r := by
  intro k hk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => rfl
  | succ d ih =>
    have hprev : commonKnowledge f P x (r + d) = commonKnowledge f P x r :=
      ih (Nat.le_add_right r d)
    have hstep : commonKnowledge f P x (r + d + 1) = commonKnowledge f P x (r + 1) := by
      ext y
      simp only [mem_commonKnowledge_succ, hprev]
    rw [show r + (d + 1) = r + d + 1 by omega, hstep, hstab]

/-! ### Private helper lemmas for sums and affine dimension -/

private theorem sum_pos_of_subset_priorSupport {P : (Fin n → Bool) → ℝ}
    {A : Finset (Fin n → Bool)} (hA : A ⊆ priorSupport P) (hne : A.Nonempty) :
    0 < ∑ z ∈ A, P z :=
  sum_pos (fun _ hz => mem_priorSupport.mp (hA hz)) hne

private theorem condExpect_eq_const {f : (Fin n → Bool) → Bool} {P : (Fin n → Bool) → ℝ}
    {A : Finset (Fin n → Bool)} (hA : A ⊆ priorSupport P) (hne : A.Nonempty) {b : Bool}
    (hb : ∀ z ∈ A, f z = b) :
    condExpect f P A = if b then 1 else 0 := by
  have hpos := sum_pos_of_subset_priorSupport hA hne
  rw [condExpect_apply]
  cases b
  · have hnum : (∑ z ∈ A, if f z then P z else 0) = 0 :=
      sum_eq_zero fun z hz => by simp [hb z hz]
    simp [hnum]
  · have hnum : (∑ z ∈ A, if f z then P z else 0) = ∑ z ∈ A, P z :=
      sum_congr rfl fun z hz => by simp [hb z hz]
    simp [hnum, div_self hpos.ne']

private theorem condExpect_const_mul {f : (Fin n → Bool) → Bool} {P : (Fin n → Bool) → ℝ}
    {A : Finset (Fin n → Bool)} {c : ℝ} (hc : c ≠ 0) :
    condExpect f (fun z => c * P z) A = condExpect f P A := by
  simp only [condExpect_apply]
  have hnum : (∑ z ∈ A, if f z then c * P z else 0) = c * ∑ z ∈ A, if f z then P z else 0 := by
    rw [mul_sum]
    exact sum_congr rfl fun z _ => by split_ifs <;> ring
  rw [hnum, ← mul_sum, mul_div_mul_left _ _ hc]

private theorem agentBid_const_mul {f : (Fin n → Bool) → Bool} {P : (Fin n → Bool) → ℝ}
    {S : Finset (Fin n → Bool)} {c : ℝ} (hc : c ≠ 0) (i : Fin n) (y : Fin n → Bool) :
    agentBid f (fun z => c * P z) S i y = agentBid f P S i y :=
  condExpect_const_mul hc

private theorem roundPrice_const_mul {f : (Fin n → Bool) → Bool} {P : (Fin n → Bool) → ℝ}
    {S : Finset (Fin n → Bool)} {c : ℝ} (hc : c ≠ 0) (y : Fin n → Bool) :
    roundPrice f (fun z => c * P z) S y = roundPrice f P S y := by
  simp only [roundPrice_apply, agentBid_const_mul hc]

private theorem priorSupport_const_mul {P : (Fin n → Bool) → ℝ} {c : ℝ} (hc : 0 < c) :
    priorSupport (fun z => c * P z) = priorSupport P := by
  ext z
  simp only [mem_priorSupport, mul_pos_iff_of_pos_left hc]

private theorem commonKnowledge_const_mul {f : (Fin n → Bool) → Bool} {P : (Fin n → Bool) → ℝ}
    {c : ℝ} (hc : 0 < c) (x : Fin n → Bool) :
    ∀ r, commonKnowledge f (fun z => c * P z) x r = commonKnowledge f P x r
  | 0 => priorSupport_const_mul hc
  | r + 1 => by
    ext y
    simp only [mem_commonKnowledge_succ, commonKnowledge_const_mul hc x r,
      roundPrice_const_mul hc.ne']

/-- Embedding of Boolean states `{0, 1}ⁿ` into `ℝⁿ`. -/
private def boolEmbed (y : Fin n → Bool) : Fin n → ℝ :=
  fun i => if y i then 1 else 0

private theorem roundPrice_sub_eq_linear (f : (Fin n → Bool) → Bool) (P : (Fin n → Bool) → ℝ)
    (S : Finset (Fin n → Bool)) :
    ∃ L : (Fin n → ℝ) →ₗ[ℝ] ℝ, ∀ y z : Fin n → Bool,
      roundPrice f P S y - roundPrice f P S z = L (boolEmbed y - boolEmbed z) := by
  let c0 : Fin n → ℝ := fun i => condExpect f P (S.filter fun w => w i = false)
  let c1 : Fin n → ℝ := fun i => condExpect f P (S.filter fun w => w i = true)
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun v => (∑ i : Fin n, (c1 i - c0 i) * v i) / n
      map_add' := fun u v => by
        simp only [Pi.add_apply, mul_add, sum_add_distrib, add_div]
      map_smul' := fun r v => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_left_comm _ r, ← mul_sum,
          mul_div_assoc] }
  refine ⟨L, fun y z => ?_⟩
  have hbid (i : Fin n) (w : Fin n → Bool) :
      agentBid f P S i w = c0 i + (c1 i - c0 i) * boolEmbed w i := by
    cases hw : w i <;> simp [agentBid, agentKnowledge, c0, c1, boolEmbed, hw]
  simp only [roundPrice_apply, L, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, hbid,
    ← sub_div, ← sum_sub_distrib]
  congr 1
  exact sum_congr rfl fun i _ => by ring

private theorem finrank_vectorSpan_succ_lt {f : (Fin n → Bool) → Bool} {P : (Fin n → Bool) → ℝ}
    {x : Fin n → Bool} {k : ℕ} (hx : x ∈ commonKnowledge f P x k)
    (hneq : commonKnowledge f P x (k + 1) ≠ commonKnowledge f P x k) :
    Module.finrank ℝ
        (vectorSpan ℝ (boolEmbed '' (commonKnowledge f P x (k + 1) : Set (Fin n → Bool)))) <
      Module.finrank ℝ
        (vectorSpan ℝ (boolEmbed '' (commonKnowledge f P x k : Set (Fin n → Bool)))) := by
  set S := commonKnowledge f P x k
  set S' := commonKnowledge f P x (k + 1)
  have hsub : S' ⊆ S := commonKnowledge_succ_subset f P x k
  have hle : vectorSpan ℝ (boolEmbed '' (S' : Set (Fin n → Bool))) ≤
      vectorSpan ℝ (boolEmbed '' (S : Set (Fin n → Bool))) :=
    vectorSpan_mono ℝ (Set.image_mono (Finset.coe_subset.mpr hsub))
  obtain ⟨z, hzS, hzS'⟩ : ∃ z ∈ S, z ∉ S' := by
    by_contra! hall
    exact hneq (Subset.antisymm hsub hall)
  have hzp : roundPrice f P S z ≠ roundPrice f P S x := fun h =>
    hzS' (mem_commonKnowledge_succ.mpr ⟨hzS, h⟩)
  obtain ⟨L, hL⟩ := roundPrice_sub_eq_linear f P S
  have hker : vectorSpan ℝ (boolEmbed '' (S' : Set (Fin n → Bool))) ≤ LinearMap.ker L := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro v ⟨_, ⟨u, hu, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    dsimp only
    rw [vsub_eq_sub, ← hL u w]
    have hu' : roundPrice f P S u = roundPrice f P S x := (mem_commonKnowledge_succ.mp hu).2
    have hw' : roundPrice f P S w = roundPrice f P S x := (mem_commonKnowledge_succ.mp hw).2
    linarith
  have hmemV : boolEmbed z - boolEmbed x ∈
      vectorSpan ℝ (boolEmbed '' (S : Set (Fin n → Bool))) := by
    rw [← vsub_eq_sub]
    exact vsub_mem_vectorSpan ℝ ⟨z, hzS, rfl⟩ ⟨x, hx, rfl⟩
  have hnotmemV' : boolEmbed z - boolEmbed x ∉
      vectorSpan ℝ (boolEmbed '' (S' : Set (Fin n → Bool))) := fun h => by
    have h0 : L (boolEmbed z - boolEmbed x) = 0 := LinearMap.mem_ker.mp (hker h)
    rw [← hL z x] at h0
    exact hzp (sub_eq_zero.mp h0)
  exact Submodule.finrank_lt_finrank_of_lt
    (lt_of_le_of_ne hle fun heq => hnotmemV' (heq ▸ hmemV))

/-- **Affine-dimension stabilization bound** (generalizes [PennockSami2007, Theorem 26.14, p. 669]
to every Boolean function `f`): for any `f`, `P`, and state `x` with `0 < P x`, the common-knowledge
set stabilizes after at most `n` rounds (`Sⁿ⁺¹ = Sⁿ`). -/
theorem commonKnowledge_succ_eq_self_at_n {f : (Fin n → Bool) → Bool} {P : (Fin n → Bool) → ℝ}
    {x : Fin n → Bool} (hx : 0 < P x) :
    commonKnowledge f P x (n + 1) = commonKnowledge f P x n := by
  by_contra hneq
  have hstrict : ∀ k ≤ n, commonKnowledge f P x (k + 1) ≠ commonKnowledge f P x k :=
    fun k hk heq =>
      hneq ((commonKnowledge_eq_of_eq_succ heq (n + 1) (by omega)).trans
        (commonKnowledge_eq_of_eq_succ heq n hk).symm)
  let d : ℕ → ℕ := fun k =>
    Module.finrank ℝ (vectorSpan ℝ (boolEmbed '' (commonKnowledge f P x k : Set (Fin n → Bool))))
  have hstep : ∀ k ≤ n, d (k + 1) < d k := fun k hk =>
    finrank_vectorSpan_succ_lt (mem_commonKnowledge_self hx k) (hstrict k hk)
  have hbound : ∀ k ≤ n + 1, d k + k ≤ d 0 := by
    intro k
    induction k with
    | zero => intro _; omega
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := hstep k (by omega)
      omega
  have hd0 : d 0 ≤ n := by
    calc d 0 ≤ Module.finrank ℝ (Fin n → ℝ) := Submodule.finrank_le _
      _ = n := Module.finrank_fin_fun ℝ
  have := hbound (n + 1) le_rfl
  omega

/-- The equilibrium common-knowledge set `S^∞` for true state `x`, equal to
`commonKnowledge f P x n` since the market stabilizes in at most `n` rounds
(`commonKnowledge_succ_eq_self_at_n`). -/
noncomputable def eqSet (f : (Fin n → Bool) → Bool) (P : (Fin n → Bool) → ℝ)
    (x : Fin n → Bool) : Finset (Fin n → Bool) :=
  commonKnowledge f P x n

/-- The equilibrium clearing price `p^∞ = roundPrice f P (eqSet f P x) x`
[PennockSami2007, §26.5.4, p. 668]. -/
noncomputable def eqPrice (f : (Fin n → Bool) → Bool) (P : (Fin n → Bool) → ℝ)
    (x : Fin n → Bool) : ℝ :=
  roundPrice f P (eqSet f P x) x

theorem commonKnowledge_eq_eqSet_of_le {f : (Fin n → Bool) → Bool} {P : (Fin n → Bool) → ℝ}
    {x : Fin n → Bool} (hx : 0 < P x) {r : ℕ} (hr : n ≤ r) :
    commonKnowledge f P x r = eqSet f P x :=
  commonKnowledge_eq_of_eq_succ (commonKnowledge_succ_eq_self_at_n hx) r hr

theorem commonKnowledge_eq_eqSet_of_eq_succ {f : (Fin n → Bool) → Bool} {P : (Fin n → Bool) → ℝ}
    {x : Fin n → Bool} (hx : 0 < P x) {r : ℕ}
    (hstab : commonKnowledge f P x (r + 1) = commonKnowledge f P x r) :
    commonKnowledge f P x r = eqSet f P x := by
  rcases le_total r n with hrn | hnr
  · exact (commonKnowledge_eq_of_eq_succ hstab n hrn).symm
  · exact commonKnowledge_eq_eqSet_of_le hx hnr

theorem roundPrice_eq_eqPrice_of_mem_eqSet {f : (Fin n → Bool) → Bool} {P : (Fin n → Bool) → ℝ}
    {x y : Fin n → Bool} (hx : 0 < P x) (hy : y ∈ eqSet f P x) :
    roundPrice f P (eqSet f P x) y = eqPrice f P x := by
  have hy' : y ∈ commonKnowledge f P x (n + 1) := by
    rwa [commonKnowledge_succ_eq_self_at_n hx]
  exact (mem_commonKnowledge_succ.mp hy').2

end Model

/-! ### Theorem 26.9: Common Knowledge of Aggregates at Equilibrium (§26.5.4, p. 668) -/

section Theorem26_9

variable {n : ℕ}

private theorem sum_condExpect_orthog {f : (Fin n → Bool) → Bool} {P : (Fin n → Bool) → ℝ}
    {A : Finset (Fin n → Bool)} (hA : A ⊆ priorSupport P) :
    ∑ z ∈ A, P z * ((if f z then (1 : ℝ) else 0) - condExpect f P A) = 0 := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp
  · have hpos := sum_pos_of_subset_priorSupport hA hne
    have h1 : (∑ z ∈ A, P z * (if f z then (1 : ℝ) else 0)) = ∑ z ∈ A, if f z then P z else 0 :=
      sum_congr rfl fun z _ => by split_ifs <;> ring
    simp only [mul_sub, sum_sub_distrib, h1, ← sum_mul, condExpect_apply]
    rw [mul_div_cancel₀ _ hpos.ne', sub_self]

/-- **Common knowledge of aggregates at any fixed-point set** ([PennockSami2007, Theorem 26.9,
Eqs. (26.1)–(26.2), p. 668]): if `0 < n`, `S ⊆ priorSupport P` is nonempty, and the clearing price
`roundPrice f P S y` takes a constant value `p` on `S`, then:
1. `condExpect f P S = p` (Eq. 26.1), and
2. `agentBid f P S i y = p` for every agent `i` and every state `y ∈ S` (Eq. 26.2). -/
theorem eq_condExpect_and_agentBid_of_roundPrice_const (hn : 0 < n)
    {f : (Fin n → Bool) → Bool} {P : (Fin n → Bool) → ℝ} {S : Finset (Fin n → Bool)}
    (hS : S ⊆ priorSupport P) (hne : S.Nonempty) {p : ℝ}
    (hconst : ∀ y ∈ S, roundPrice f P S y = p) :
    condExpect f P S = p ∧ ∀ i : Fin n, ∀ y ∈ S, agentBid f P S i y = p := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  let fv : (Fin n → Bool) → ℝ := fun z => if f z then 1 else 0
  have horth (i : Fin n) :
      ∑ y ∈ S, P y * (agentBid f P S i y - p) * (fv y - agentBid f P S i y) = 0 := by
    rw [← sum_filter_add_sum_filter_not S (fun y => y i = true)]
    have hpart (b : Bool) :
        ∑ y ∈ S.filter (fun z => z i = b),
          P y * (agentBid f P S i y - p) * (fv y - agentBid f P S i y) = 0 := by
      let Sb := S.filter fun z => z i = b
      have hconst_b : ∀ y ∈ Sb, agentBid f P S i y = condExpect f P Sb := fun y hy => by
        simp only [agentBid_apply, agentKnowledge, Sb, (mem_filter.mp hy).2]
      calc ∑ y ∈ Sb, P y * (agentBid f P S i y - p) * (fv y - agentBid f P S i y)
          = ∑ y ∈ Sb, (condExpect f P Sb - p) * (P y * (fv y - condExpect f P Sb)) :=
            sum_congr rfl fun y hy => by rw [hconst_b y hy]; ring
        _ = (condExpect f P Sb - p) * ∑ y ∈ Sb, P y * (fv y - condExpect f P Sb) := by
            rw [← mul_sum]
        _ = 0 := by
            rw [sum_condExpect_orthog ((filter_subset _ _).trans hS), mul_zero]
    have hnot : (S.filter fun y => ¬ y i = true) = S.filter fun y => y i = false := by
      ext y; simp only [mem_filter, Bool.not_eq_true]
    rw [hnot, hpart true, hpart false, add_zero]
  have hsq (i : Fin n) :
      ∑ y ∈ S, P y * (agentBid f P S i y - p) ^ 2 =
        ∑ y ∈ S, P y * (agentBid f P S i y - p) * (fv y - p) := by
    have hdiff : ∑ y ∈ S, (P y * (agentBid f P S i y - p) * (fv y - p) -
        P y * (agentBid f P S i y - p) ^ 2) = 0 := by
      simpa only [← horth i] using sum_congr rfl fun y _ => by ring
    linarith [sum_sub_distrib (s := S)
      (f := fun y => P y * (agentBid f P S i y - p) * (fv y - p))
      (g := fun y => P y * (agentBid f P S i y - p) ^ 2)]
  have hsum_zero : ∑ i : Fin n, ∑ y ∈ S, P y * (agentBid f P S i y - p) ^ 2 = 0 := by
    calc ∑ i : Fin n, ∑ y ∈ S, P y * (agentBid f P S i y - p) ^ 2
        = ∑ i : Fin n, ∑ y ∈ S, P y * (agentBid f P S i y - p) * (fv y - p) :=
          sum_congr rfl fun i _ => hsq i
      _ = ∑ y ∈ S, ∑ i : Fin n, P y * (agentBid f P S i y - p) * (fv y - p) := sum_comm
      _ = ∑ y ∈ S, P y * (∑ i : Fin n, (agentBid f P S i y - p)) * (fv y - p) := by
          refine sum_congr rfl fun y _ => ?_
          rw [mul_sum, sum_mul]
      _ = 0 := by
          refine sum_eq_zero fun y hy => ?_
          have hpy : ∑ i : Fin n, agentBid f P S i y = (n : ℝ) * p := by
            have := hconst y hy
            rw [roundPrice_apply, div_eq_iff hn'] at this
            linarith
          have hsub0 : ∑ i : Fin n, (agentBid f P S i y - p) = 0 := by
            simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hpy,
              sub_self]
          rw [hsub0, mul_zero, zero_mul]
  have hbid : ∀ i : Fin n, ∀ y ∈ S, agentBid f P S i y = p := by
    intro i y hy
    have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin n)),
        0 ≤ ∑ z ∈ S, P z * (agentBid f P S j z - p) ^ 2 := fun j _ =>
      sum_nonneg fun z hz => mul_nonneg (mem_priorSupport.mp (hS hz)).le (sq_nonneg _)
    have hi0 : ∑ z ∈ S, P z * (agentBid f P S i z - p) ^ 2 = 0 :=
      (sum_eq_zero_iff_of_nonneg hnonneg).mp hsum_zero i (mem_univ i)
    have hy0 : P y * (agentBid f P S i y - p) ^ 2 = 0 :=
      (sum_eq_zero_iff_of_nonneg fun z hz =>
        mul_nonneg (mem_priorSupport.mp (hS hz)).le (sq_nonneg _)).mp hi0 y hy
    have hsq0 : (agentBid f P S i y - p) ^ 2 = 0 :=
      (mul_eq_zero.mp hy0).resolve_left (mem_priorSupport.mp (hS hy)).ne'
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq0)
  refine ⟨?_, hbid⟩
  let i₀ : Fin n := ⟨0, hn⟩
  have hpart_eq (b : Bool) :
      ∑ z ∈ S.filter (fun w => w i₀ = b), (if f z then P z else 0) =
        p * ∑ z ∈ S.filter (fun w => w i₀ = b), P z := by
    let Sb := S.filter fun w => w i₀ = b
    rcases Sb.eq_empty_or_nonempty with hEmpty | ⟨y, hy⟩
    · simp [Sb, hEmpty]
    · have hpos := sum_pos_of_subset_priorSupport ((filter_subset _ _).trans hS) ⟨y, hy⟩
      have hbi : condExpect f P Sb = p := by
        have hby := hbid i₀ y (mem_filter.mp hy).1
        simpa only [agentBid_apply, agentKnowledge, Sb, (mem_filter.mp hy).2] using hby
      rw [condExpect_apply, div_eq_iff hpos.ne'] at hbi
      exact hbi
  have hnot : (S.filter fun z => ¬ z i₀ = true) = S.filter fun z => z i₀ = false := by
    ext z; simp only [mem_filter, Bool.not_eq_true]
  have htot : (∑ z ∈ S, if f z then P z else 0) = p * ∑ z ∈ S, P z := by
    rw [← sum_filter_add_sum_filter_not S (fun z => z i₀ = true),
      ← sum_filter_add_sum_filter_not S (fun z => z i₀ = true), hnot,
      hpart_eq true, hpart_eq false, mul_add]
  rw [condExpect_apply, htot, mul_div_cancel_right₀ _ (sum_pos_of_subset_priorSupport hS hne).ne']

/-- **Theorem 26.9** ([PennockSami2007, p. 668, Eqs. (26.1)–(26.2)]): at equilibrium (`eqSet f P x`,
`eqPrice f P x`) for any `0 < n` and any prior `P` with `0 < P x`, the common-knowledge
expectation and every agent's conditional expectation equal the equilibrium price `p^∞`. -/
theorem equilibrium_commonKnowledge_of_aggregates (hn : 0 < n) {f : (Fin n → Bool) → Bool}
    {P : (Fin n → Bool) → ℝ} {x : Fin n → Bool} (hx : 0 < P x) :
    condExpect f P (eqSet f P x) = eqPrice f P x ∧
      ∀ i : Fin n, ∀ y ∈ eqSet f P x, agentBid f P (eqSet f P x) i y = eqPrice f P x :=
  eq_condExpect_and_agentBid_of_roundPrice_const hn
    (commonKnowledge_subset_priorSupport f P x n)
    ⟨x, mem_commonKnowledge_self hx n⟩
    fun _ hy => roundPrice_eq_eqPrice_of_mem_eqSet hx hy

end Theorem26_9

/-! ### Definition 26.11 and Theorems 26.12–26.13: Weighted Threshold Characterization -/

section WeightedThreshold

variable {n : ℕ}

/-- A Boolean function `f : (Fin n → Bool) → Bool` is a **weighted threshold function** iff there
exist real constants `w₀, w₁, …, wₙ` such that `f x = true ↔ 1 ≤ w₀ + ∑ i, w i * x_i`
[PennockSami2007, Definition 26.11, p. 669].

This is equivalent to `Cslib.Circuits.Boolean.WeightedThreshold.IsLTF` via `θ = 1 - w₀`; it is
defined directly here to match Definition 26.11 without importing the depth-two threshold-circuit
complexity stack. -/
def IsWeightedThreshold (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (w₀ : ℝ) (w : Fin n → ℝ), ∀ x : Fin n → Bool,
    f x = true ↔ 1 ≤ w₀ + ∑ i : Fin n, w i * (if x i then 1 else 0)

theorem isWeightedThreshold_iff {f : (Fin n → Bool) → Bool} :
    IsWeightedThreshold f ↔
      ∃ (w₀ : ℝ) (w : Fin n → ℝ), ∀ x : Fin n → Bool,
        f x = true ↔ 1 ≤ w₀ + ∑ i : Fin n, w i * (if x i then 1 else 0) := by
  rfl

/-- At equilibrium for a weighted threshold function `f`, common knowledge `eqSet f P x` already
determines `f x`: every state `y ∈ eqSet f P x` satisfies `f y = f x`. -/
theorem eq_of_mem_eqSet_of_isWeightedThreshold (hn : 0 < n) {f : (Fin n → Bool) → Bool}
    (hf : IsWeightedThreshold f) {P : (Fin n → Bool) → ℝ} {x : Fin n → Bool} (hx : 0 < P x) :
    ∀ y ∈ eqSet f P x, f y = f x := by
  obtain ⟨w₀, w, hw⟩ := hf
  set S := eqSet f P x
  set p := eqPrice f P x
  have hSsub : S ⊆ priorSupport P := commonKnowledge_subset_priorSupport f P x n
  have hxS : x ∈ S := mem_commonKnowledge_self hx n
  obtain ⟨hce, hbid⟩ := equilibrium_commonKnowledge_of_aggregates hn (f := f) hx
  suffices hconst : ∀ y₁ ∈ S, ∀ y₀ ∈ S, f y₁ = true → f y₀ = false → False by
    intro y hy
    cases hfy : f y <;> cases hfx : f x
    · rfl
    · exact (hconst x hxS y hy hfx hfy).elim
    · exact (hconst y hy x hxS hfy hfx).elim
    · rfl
  intro y₁ hy₁ y₀ hy₀ hf₁ hf₀
  let S₁ := S.filter fun y => f y = true
  let S₀ := S.filter fun y => f y = false
  let M₁ : ℝ := ∑ y ∈ S₁, P y
  let M₀ : ℝ := ∑ y ∈ S₀, P y
  have hM₁_pos : 0 < M₁ :=
    sum_pos_of_subset_priorSupport ((filter_subset _ _).trans hSsub)
      ⟨y₁, mem_filter.mpr ⟨hy₁, hf₁⟩⟩
  have hM₀_pos : 0 < M₀ :=
    sum_pos_of_subset_priorSupport ((filter_subset _ _).trans hSsub)
      ⟨y₀, mem_filter.mpr ⟨hy₀, hf₀⟩⟩
  have hS_split : ∑ y ∈ S, P y = M₁ + M₀ := by
    have hnot : (S.filter fun y => ¬ f y = true) = S₀ := by
      ext y; simp only [S₀, mem_filter, Bool.not_eq_true]
    rw [← sum_filter_add_sum_filter_not S (fun y => f y = true), hnot]
  have hS_f1 : (∑ y ∈ S, if f y then P y else 0) = M₁ := by
    simp only [M₁, S₁, sum_filter]
  have hp_eq : M₁ = p * (M₁ + M₀) := by
    rw [condExpect_apply, hS_f1, hS_split, div_eq_iff (by linarith)] at hce
    exact hce
  have hp_lt_one : p < 1 := by nlinarith
  have h1mp_pos : 0 < 1 - p := by linarith
  have hcross_M : (1 - p) * M₁ = p * M₀ := by linarith
  let X₁ : Fin n → ℝ := fun i => ∑ y ∈ S₁, P y * (if y i then 1 else 0)
  let X₀ : Fin n → ℝ := fun i => ∑ y ∈ S₀, P y * (if y i then 1 else 0)
  have hcross_X (i : Fin n) : M₀ * X₁ i = M₁ * X₀ i := by
    let Si := S.filter fun y => y i = true
    have hSi_eq : (∑ y ∈ Si, if f y then P y else 0) = p * ∑ y ∈ Si, P y := by
      rcases Si.eq_empty_or_nonempty with hEmpty | ⟨y, hy⟩
      · simp [hEmpty]
      · have hpos := sum_pos_of_subset_priorSupport ((filter_subset _ _).trans hSsub) ⟨y, hy⟩
        have hbi := hbid i y (mem_filter.mp hy).1
        simp only [agentBid_apply, agentKnowledge, (mem_filter.mp hy).2] at hbi
        rw [condExpect_apply, div_eq_iff hpos.ne'] at hbi
        exact hbi
    have hX₁_eq : X₁ i = ∑ y ∈ Si, if f y then P y else 0 := by
      simp only [X₁, S₁, Si, sum_filter]
      exact sum_congr rfl fun y _ => by cases f y <;> cases y i <;> simp
    have hX₀_eq : X₀ i = ∑ y ∈ Si, if f y then 0 else P y := by
      simp only [X₀, S₀, Si, sum_filter]
      exact sum_congr rfl fun y _ => by cases f y <;> cases y i <;> simp
    have hSi_tot : ∑ y ∈ Si, P y = X₁ i + X₀ i := by
      rw [hX₁_eq, hX₀_eq, ← sum_add_distrib]
      exact sum_congr rfl fun y _ => by cases f y <;> simp
    have hXi_rel : (1 - p) * X₁ i = p * X₀ i := by
      rw [← hX₁_eq, hSi_tot] at hSi_eq
      linarith
    have hmul : (1 - p) * (M₀ * X₁ i) = (1 - p) * (M₁ * X₀ i) := by
      calc (1 - p) * (M₀ * X₁ i) = M₀ * ((1 - p) * X₁ i) := by ring
        _ = M₀ * (p * X₀ i) := by rw [hXi_rel]
        _ = (p * M₀) * X₀ i := by ring
        _ = ((1 - p) * M₁) * X₀ i := by rw [← hcross_M]
        _ = (1 - p) * (M₁ * X₀ i) := by ring
    exact mul_left_cancel₀ h1mp_pos.ne' hmul
  have hlin (T : Finset (Fin n → Bool)) :
      ∑ y ∈ T, P y * (w₀ + ∑ i : Fin n, w i * (if y i then 1 else 0)) =
        w₀ * (∑ y ∈ T, P y) + ∑ i : Fin n, w i * ∑ y ∈ T, P y * (if y i then 1 else 0) := by
    calc ∑ y ∈ T, P y * (w₀ + ∑ i : Fin n, w i * (if y i then 1 else 0))
        = (∑ y ∈ T, P y * w₀) +
            ∑ y ∈ T, ∑ i : Fin n, P y * (w i * (if y i then 1 else 0)) := by
          simp only [mul_add, sum_add_distrib, mul_sum]
      _ = w₀ * (∑ y ∈ T, P y) + ∑ i : Fin n, w i * ∑ y ∈ T, P y * (if y i then 1 else 0) := by
          rw [← sum_mul, mul_comm _ w₀, sum_comm]
          congr 1
          refine sum_congr rfl fun i _ => ?_
          rw [mul_sum]
          exact sum_congr rfl fun y _ => by ring
  have hge : M₁ ≤ w₀ * M₁ + ∑ i : Fin n, w i * X₁ i := by
    have hsum_ge : ∑ y ∈ S₁, P y * 1 ≤
        ∑ y ∈ S₁, P y * (w₀ + ∑ i : Fin n, w i * (if y i then 1 else 0)) :=
      sum_le_sum fun y hy =>
        mul_le_mul_of_nonneg_left ((hw y).mp (mem_filter.mp hy).2)
          (mem_priorSupport.mp (hSsub (mem_filter.mp hy).1)).le
    have hlhs : ∑ y ∈ S₁, P y * 1 = M₁ := by simp [M₁]
    linarith [hlin S₁]
  have hlt : w₀ * M₀ + ∑ i : Fin n, w i * X₀ i < M₀ := by
    have hsum_lt : ∑ y ∈ S₀, P y * (w₀ + ∑ i : Fin n, w i * (if y i then 1 else 0)) <
        ∑ y ∈ S₀, P y * 1 := by
      refine sum_lt_sum_of_nonempty ⟨y₀, mem_filter.mpr ⟨hy₀, hf₀⟩⟩ fun y hy => ?_
      have hnot : ¬ 1 ≤ w₀ + ∑ i : Fin n, w i * (if y i then 1 else 0) := fun h => by
        have := (hw y).mpr h
        rw [(mem_filter.mp hy).2] at this
        exact Bool.false_ne_true this
      exact mul_lt_mul_of_pos_left (lt_of_not_ge hnot)
        (mem_priorSupport.mp (hSsub (mem_filter.mp hy).1))
    have hrhs : ∑ y ∈ S₀, P y * 1 = M₀ := by simp [M₀]
    linarith [hlin S₀]
  have h1 := mul_le_mul_of_nonneg_left hge hM₀_pos.le
  have h2 := mul_lt_mul_of_pos_left hlt hM₁_pos
  have heq_sums : M₀ * ∑ i : Fin n, w i * X₁ i = M₁ * ∑ i : Fin n, w i * X₀ i := by
    rw [mul_sum, mul_sum]
    exact sum_congr rfl fun i _ => by
      calc M₀ * (w i * X₁ i) = w i * (M₀ * X₁ i) := by ring
        _ = w i * (M₁ * X₀ i) := by rw [hcross_X i]
        _ = M₁ * (w i * X₀ i) := by ring
  linarith

/-- **Theorem 26.12** ([PennockSami2007, p. 669]): if `f : (Fin n → Bool) → Bool` (`0 < n`) is a
weighted threshold function, then for every prior `P` and every state `x` with `0 < P x`, the
equilibrium price equals `f x` (`1` if `f x = true`, `0` if `f x = false`). -/
theorem eqPrice_eq_of_isWeightedThreshold (hn : 0 < n) {f : (Fin n → Bool) → Bool}
    (hf : IsWeightedThreshold f) {P : (Fin n → Bool) → ℝ} {x : Fin n → Bool} (hx : 0 < P x) :
    eqPrice f P x = if f x then 1 else 0 := by
  have hce := (equilibrium_commonKnowledge_of_aggregates hn (f := f) hx).1
  rw [← hce]
  exact condExpect_eq_const (commonKnowledge_subset_priorSupport f P x n)
    ⟨x, mem_commonKnowledge_self hx n⟩
    (eq_of_mem_eqSet_of_isWeightedThreshold hn hf hx)

/-- Collapse a finite convex combination of embedded Boolean vectors from `{y | f y = b}` into a
mixed strategy supported on `{y | f y = b}`. -/
private theorem exists_mixedStrategy_of_mem_convexHull_boolEmbed
    {f : (Fin n → Bool) → Bool} {b : Bool} {u : Fin n → ℝ}
    (hu : u ∈ convexHull ℝ (boolEmbed '' {y : Fin n → Bool | f y = b})) :
    ∃ α : (Fin n → Bool) → ℝ, IsMixedStrategy α ∧ (∀ y, 0 < α y → f y = b) ∧
      ∀ i : Fin n, ∑ y : Fin n → Bool, α y * boolEmbed y i = u i := by
  classical
  obtain ⟨κ, _, c, z, hc0, hc1, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hu
  choose y hy_f hy_eq using hz
  let α : (Fin n → Bool) → ℝ := fun w => ∑ k ∈ Finset.univ.filter fun k => y k = w, c k
  have hα_nonneg (w : Fin n → Bool) : 0 ≤ α w := sum_nonneg fun k _ => hc0 k
  have hα_sum : ∑ w : Fin n → Bool, α w = 1 := by
    simp only [α]
    rw [sum_fiberwise_of_maps_to (fun _ _ => mem_univ _), hc1]
  have hα_supp (w : Fin n → Bool) (hw : 0 < α w) : f w = b := by
    have hne : (Finset.univ.filter fun k => y k = w).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      simp [α, h] at hw
    obtain ⟨k, hk⟩ := hne
    rw [← (mem_filter.mp hk).2]
    exact hy_f k
  refine ⟨α, isMixedStrategy_iff.mpr ⟨hα_nonneg, hα_sum⟩, hα_supp, fun i => ?_⟩
  have hcoord : u i = ∑ k : κ, c k * z k i := by
    rw [← hsum]
    simp [Finset.sum_apply, smul_eq_mul]
  rw [hcoord]
  calc ∑ w : Fin n → Bool, α w * boolEmbed w i
      = ∑ w : Fin n → Bool, ∑ k ∈ Finset.univ.filter (fun k => y k = w), c k * z k i := by
        refine sum_congr rfl fun w _ => ?_
        simp only [α, sum_mul]
        refine sum_congr rfl fun k hk => ?_
        rw [← (mem_filter.mp hk).2, hy_eq k]
    _ = ∑ k : κ, c k * z k i := sum_fiberwise_of_maps_to (fun _ _ => mem_univ _) _

/-- **Theorem 26.13** ([PennockSami2007, p. 669]): if `f : (Fin n → Bool) → Bool` is not a weighted
threshold function, then there exists a prior distribution `P` (`IsMixedStrategy P`) for which the
market immediately stabilizes at equilibrium price `p^∞ = 1 / 2` on every positive-probability state
(and therefore never reveals `f x ∈ {0, 1}`). -/
theorem exists_prior_eqPrice_eq_half_of_not_isWeightedThreshold
    {f : (Fin n → Bool) → Bool} (hf : ¬ IsWeightedThreshold f) :
    ∃ P : (Fin n → Bool) → ℝ, IsMixedStrategy P ∧ ∀ x, 0 < P x → eqPrice f P x = 1 / 2 := by
  have hn : 0 < n := by
    by_contra hn0
    have hn' : n = 0 := by omega
    subst hn'
    refine hf ⟨if f (fun i => i.elim0) then 1 else 0, 0, fun x => ?_⟩
    have hx : x = fun i => i.elim0 := funext fun i => i.elim0
    subst hx
    cases f (fun i => i.elim0) <;> simp
  let A : Set (Fin n → ℝ) := boolEmbed '' {y : Fin n → Bool | f y = true}
  let B : Set (Fin n → ℝ) := boolEmbed '' {y : Fin n → Bool | f y = false}
  have hnot_disj : ¬ Disjoint (convexHull ℝ A) (convexHull ℝ B) := by
    intro hdisj
    have hA_comp : IsCompact (convexHull ℝ A) := (Set.toFinite A).isCompact_convexHull ℝ
    have hB_closed : IsClosed (convexHull ℝ B) := (Set.toFinite B).isClosed_convexHull ℝ
    obtain ⟨φ, u, v, hA_lt, huv, hB_gt⟩ :=
      geometric_hahn_banach_compact_closed (convex_convexHull ℝ A) hA_comp
        (convex_convexHull ℝ B) hB_closed hdisj
    have hφ_eval (z : Fin n → ℝ) : φ z = ∑ i : Fin n, φ (Pi.single i 1) * z i := by
      have hz : z = ∑ i : Fin n, z i • Pi.single i (1 : ℝ) := by
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [hz]
      rw [map_sum]
      exact sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, mul_comm]
    refine hf ⟨1 + u, fun i => -φ (Pi.single i 1), fun x => ?_⟩
    have hlin : 1 + u + ∑ i : Fin n, (-φ (Pi.single i 1)) * (if x i then 1 else 0) =
        1 + u - φ (boolEmbed x) := by
      rw [hφ_eval (boolEmbed x)]
      simp only [boolEmbed, neg_mul, sum_neg_distrib, sub_eq_add_neg, add_assoc]
    rw [hlin]
    constructor
    · intro hfx
      have hlt := hA_lt (boolEmbed x) (subset_convexHull ℝ A ⟨x, hfx, rfl⟩)
      linarith
    · intro hge
      by_contra hfx
      have hfx' : f x = false := Bool.eq_false_iff.mpr hfx
      have hgt := hB_gt (boolEmbed x) (subset_convexHull ℝ B ⟨x, hfx', rfl⟩)
      linarith
  rw [Set.not_disjoint_iff] at hnot_disj
  obtain ⟨u, huA, huB⟩ := hnot_disj
  obtain ⟨α, hα, hα_supp, hα_mean⟩ := exists_mixedStrategy_of_mem_convexHull_boolEmbed huA
  obtain ⟨β, hβ, hβ_supp, hβ_mean⟩ := exists_mixedStrategy_of_mem_convexHull_boolEmbed huB
  let P : (Fin n → Bool) → ℝ := fun y => (1 / 2) * α y + (1 / 2) * β y
  have hP_nonneg (y : Fin n → Bool) : 0 ≤ P y :=
    add_nonneg (mul_nonneg (by norm_num) (hα.nonneg y)) (mul_nonneg (by norm_num) (hβ.nonneg y))
  have hP_sum : ∑ y : Fin n → Bool, P y = 1 := by
    simp only [P, sum_add_distrib, ← mul_sum, hα.sum_eq_one, hβ.sum_eq_one]
    norm_num
  have hP : IsMixedStrategy P := isMixedStrategy_iff.mpr ⟨hP_nonneg, hP_sum⟩
  have hα_zero_of_false {y : Fin n → Bool} (hy : f y = false) : α y = 0 := by
    rcases (hα.nonneg y).eq_or_lt with h0 | hpos
    · exact h0.symm
    · exact absurd ((hα_supp y hpos).symm.trans hy) Bool.false_ne_true.symm
  have hβ_zero_of_true {y : Fin n → Bool} (hy : f y = true) : β y = 0 := by
    rcases (hβ.nonneg y).eq_or_lt with h0 | hpos
    · exact h0.symm
    · exact absurd ((hβ_supp y hpos).symm.trans hy) Bool.false_ne_true
  have hP_if_true (y : Fin n → Bool) : (if f y then P y else 0) = (1 / 2) * α y := by
    cases hfy : f y
    · simp [hα_zero_of_false hfy]
    · simp [P, hβ_zero_of_true hfy]
  have hP_if_false (y : Fin n → Bool) : (if f y then 0 else P y) = (1 / 2) * β y := by
    cases hfy : f y
    · simp [P, hα_zero_of_false hfy]
    · simp [hβ_zero_of_true hfy]
  have hbid_half (i : Fin n) (y : Fin n → Bool) (hy : y ∈ priorSupport P) :
      agentBid f P (priorSupport P) i y = 1 / 2 := by
    set K := agentKnowledge (priorSupport P) i y
    have hK_pos : 0 < ∑ z ∈ K, P z :=
      sum_pos_of_subset_priorSupport (filter_subset _ _) ⟨y, mem_agentKnowledge.mpr ⟨hy, rfl⟩⟩
    have hsum_eq (g : (Fin n → Bool) → ℝ) (hg : ∀ z, P z = 0 → g z = 0) :
        ∑ z ∈ K, g z = ∑ z ∈ Finset.univ.filter (fun z : Fin n → Bool => z i = y i), g z := by
      have hK_sub : K ⊆ Finset.univ.filter (fun z : Fin n → Bool => z i = y i) := fun z hz =>
        mem_filter.mpr ⟨mem_univ _, (mem_agentKnowledge.mp hz).2⟩
      refine sum_subset hK_sub fun z hz hzK => hg z ?_
      have hnotpos : ¬ 0 < P z := fun hpos =>
        hzK (mem_agentKnowledge.mpr ⟨mem_priorSupport.mpr hpos, (mem_filter.mp hz).2⟩)
      exact le_antisymm (le_of_not_gt hnotpos) (hP_nonneg z)
    have hnum_eq : ∑ z ∈ K, (if f z then P z else 0) = ∑ z ∈ K, (if f z then 0 else P z) := by
      rw [hsum_eq (fun z => if f z then P z else 0) (fun z hz => by simp [hz]),
        hsum_eq (fun z => if f z then 0 else P z) (fun z hz => by simp [hz])]
      simp only [hP_if_true, hP_if_false, ← mul_sum]
      congr 1
      cases hyi : y i
      · have hcompl (μ : (Fin n → Bool) → ℝ) (hμ : ∑ z, μ z = 1) :
            ∑ z ∈ Finset.univ.filter (fun z : Fin n → Bool => z i = false), μ z =
              1 - ∑ z : Fin n → Bool, μ z * boolEmbed z i := by
          have h1 : ∑ z : Fin n → Bool, μ z * boolEmbed z i =
              ∑ z ∈ Finset.univ.filter (fun z : Fin n → Bool => z i = true), μ z := by
            simp only [boolEmbed, sum_filter]
            exact sum_congr rfl fun z _ => by cases z i <;> simp
          have h2 : ∑ z ∈ Finset.univ.filter (fun z : Fin n → Bool => z i = true), μ z +
              ∑ z ∈ Finset.univ.filter (fun z : Fin n → Bool => z i = false), μ z = 1 := by
            have hnot : (Finset.univ.filter fun z : Fin n → Bool => ¬ z i = true) =
                Finset.univ.filter fun z : Fin n → Bool => z i = false := by
              ext z; simp only [mem_filter, Bool.not_eq_true]
            rw [← hnot, sum_filter_add_sum_filter_not, hμ]
          linarith
        rw [hcompl α hα.sum_eq_one, hcompl β hβ.sum_eq_one, hα_mean i, hβ_mean i]
      · have htrue (μ : (Fin n → Bool) → ℝ) :
            ∑ z ∈ Finset.univ.filter (fun z : Fin n → Bool => z i = true), μ z =
              ∑ z : Fin n → Bool, μ z * boolEmbed z i := by
          simp only [boolEmbed, sum_filter]
          exact sum_congr rfl fun z _ => by cases z i <;> simp
        rw [htrue α, htrue β, hα_mean i, hβ_mean i]
    have hden_eq : ∑ z ∈ K, P z = 2 * ∑ z ∈ K, (if f z then P z else 0) := by
      have hsplit : ∑ z ∈ K, P z =
          (∑ z ∈ K, if f z then P z else 0) + ∑ z ∈ K, if f z then 0 else P z := by
        rw [← sum_add_distrib]
        exact sum_congr rfl fun z _ => by cases f z <;> simp
      linarith
    rw [agentBid_apply, condExpect_apply, hden_eq]
    have hnum_ne : (∑ z ∈ K, if f z then P z else 0) ≠ 0 := by linarith
    field_simp [hnum_ne]
    ring
  have hprice_half (y : Fin n → Bool) (hy : y ∈ priorSupport P) :
      roundPrice f P (priorSupport P) y = 1 / 2 := by
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    rw [roundPrice_apply, sum_congr rfl fun i _ => hbid_half i y hy, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp [hn']
  refine ⟨P, hP, fun x hx => ?_⟩
  have hstab : commonKnowledge f P x 1 = commonKnowledge f P x 0 := by
    ext y
    simp only [mem_commonKnowledge_succ, commonKnowledge_zero, and_iff_left_iff_imp]
    intro hy
    rw [hprice_half y hy, hprice_half x (mem_priorSupport.mpr hx)]
  have heq : eqSet f P x = priorSupport P :=
    (commonKnowledge_eq_eqSet_of_eq_succ hx hstab).symm
  rw [eqPrice, heq, hprice_half x (mem_priorSupport.mpr hx)]

/-- **Weighted threshold characterization of market-computable Boolean functions**
([PennockSami2007, §26.5.5, Theorems 26.12–26.13, p. 669]): for `0 < n`, `f : (Fin n → Bool) → Bool`
is a weighted threshold function iff the equilibrium price equals `f x` for every common prior `P`
and every positive-probability state `x`. -/
theorem isWeightedThreshold_iff_forall_eqPrice_eq (hn : 0 < n) (f : (Fin n → Bool) → Bool) :
    IsWeightedThreshold f ↔
      ∀ P : (Fin n → Bool) → ℝ, IsMixedStrategy P → ∀ x, 0 < P x →
        eqPrice f P x = if f x then 1 else 0 := by
  constructor
  · exact fun hf _ _ _ hx => eqPrice_eq_of_isWeightedThreshold hn hf hx
  · intro hall
    by_contra hf
    obtain ⟨P, hP, hhalf⟩ := exists_prior_eqPrice_eq_half_of_not_isWeightedThreshold hf
    obtain ⟨x, hx⟩ := hP.exists_pos
    have h1 := hall P hP x hx
    have h2 := hhalf x hx
    cases hfx : f x <;> norm_num [hfx] at h1 <;> linarith

end WeightedThreshold

/-! ### Examples 26.8 (OR) and 26.10 (XOR) -/

section Examples

private theorem agentBid_uniform_fin2 (f : (Fin 2 → Bool) → Bool) (i : Fin 2)
    (x : Fin 2 → Bool) :
    agentBid f (fun _ => (1 / 4 : ℝ)) (priorSupport (fun _ => (1 / 4 : ℝ))) i x =
      ((if f (Function.update x (1 - i) false) then (1 : ℝ) else 0) +
        (if f (Function.update x (1 - i) true) then (1 : ℝ) else 0)) / 2 := by
  let P : (Fin 2 → Bool) → ℝ := fun _ => 1 / 4
  have hsupp : priorSupport P = Finset.univ := by ext y; simp [P]
  let a := Function.update x (1 - i) false
  let b := Function.update x (1 - i) true
  have hne : a ≠ b := fun h => by
    have := congrFun h (1 - i)
    simp [a, b] at this
  have hK : agentKnowledge (priorSupport P) i x = {a, b} := by
    ext y
    simp only [mem_agentKnowledge, hsupp, mem_univ, true_and, mem_insert, mem_singleton]
    have h1i : 1 - i ≠ i := by fin_cases i <;> decide
    have heq_upd (v : Bool) (hyi : y i = x i) (hyo : y (1 - i) = v) :
        y = Function.update x (1 - i) v := by
      ext j
      by_cases hj : j = 1 - i
      · simp [hj, hyo]
      · have hji : j = i := by fin_cases i <;> fin_cases j <;> simp_all
        simp [hji, hyi, h1i.symm]
    constructor
    · intro hyi
      cases hyo : y (1 - i)
      · exact Or.inl (heq_upd false hyi hyo)
      · exact Or.inr (heq_upd true hyi hyo)
    · rintro (rfl | rfl) <;> simp [a, b, h1i.symm]
  rw [agentBid_apply, hK, condExpect_apply, sum_pair hne, sum_pair hne]
  cases f a <;> cases f b <;> norm_num [P]

/-- **Example 26.8** ([PennockSami2007, p. 667]): two-agent OR market `f(x₁, x₂) = x₁ ∨ x₂` under
the uniform prior on `{0, 1}²` at true state `x = (false, true)`. In round 1, agent 1 bids `1/2`,
agent 2 bids `1`, and the clearing price is `3/4`; at equilibrium, `p^∞ = 1 = f x`. -/
theorem orMarket_bids_and_eqPrice :
    let f : (Fin 2 → Bool) → Bool := fun y => y 0 || y 1
    let P : (Fin 2 → Bool) → ℝ := fun _ => 1 / 4
    let x : Fin 2 → Bool := ![false, true]
    agentBid f P (priorSupport P) 0 x = 1 / 2 ∧
      agentBid f P (priorSupport P) 1 x = 1 ∧
      roundPrice f P (priorSupport P) x = 3 / 4 ∧
      eqPrice f P x = 1 := by
  intro f P x
  have hf_wt : IsWeightedThreshold f := by
    refine ⟨0, fun _ => 1, fun y => ?_⟩
    simp only [f, Fin.sum_univ_two, zero_add, one_mul]
    cases y 0 <;> cases y 1 <;> norm_num
  have hbid0 : agentBid f P (priorSupport P) 0 x = 1 / 2 := by
    rw [agentBid_uniform_fin2]; norm_num [f, x]
  have hbid1 : agentBid f P (priorSupport P) 1 x = 1 := by
    rw [agentBid_uniform_fin2]; norm_num [f, x]
  have hprice : roundPrice f P (priorSupport P) x = 3 / 4 := by
    rw [roundPrice_apply, Fin.sum_univ_two, hbid0, hbid1]; norm_num
  have heq : eqPrice f P x = 1 := by
    simpa [f, x] using eqPrice_eq_of_isWeightedThreshold (by decide) hf_wt (P := P) (x := x)
      (by norm_num [P])
  exact ⟨hbid0, hbid1, hprice, heq⟩

/-- **Example 26.10** ([PennockSami2007, pp. 668–669]): two-agent XOR market
`f(x₁, x₂) = x₁ ⊕ x₂` under the uniform prior on `{0, 1}²`. In round 1, every agent bids `1/2` on
every state, the clearing price is `1/2`, and the market immediately reaches equilibrium at
`p^∞ = 1/2 ≠ f x`. -/
theorem xorMarket_bids_and_eqPrice :
    let f : (Fin 2 → Bool) → Bool := fun y => xor (y 0) (y 1)
    let P : (Fin 2 → Bool) → ℝ := fun _ => 1 / 4
    (∀ x i, agentBid f P (priorSupport P) i x = 1 / 2) ∧
      (∀ x, roundPrice f P (priorSupport P) x = 1 / 2) ∧
      (∀ x, eqPrice f P x = 1 / 2 ∧ eqPrice f P x ≠ if f x then 1 else 0) := by
  intro f P
  have hbid (x : Fin 2 → Bool) (i : Fin 2) : agentBid f P (priorSupport P) i x = 1 / 2 := by
    rw [agentBid_uniform_fin2]
    fin_cases i <;> cases hx0 : x 0 <;> cases hx1 : x 1 <;> norm_num [f, hx0, hx1]
  have hprice (x : Fin 2 → Bool) : roundPrice f P (priorSupport P) x = 1 / 2 := by
    rw [roundPrice_apply, Fin.sum_univ_two, hbid x 0, hbid x 1]; norm_num
  refine ⟨hbid, hprice, fun x => ?_⟩
  have hstab : commonKnowledge f P x 1 = commonKnowledge f P x 0 := by
    ext y
    simp only [mem_commonKnowledge_succ, commonKnowledge_zero, and_iff_left_iff_imp]
    intro _
    rw [hprice y, hprice x]
  have heq : eqPrice f P x = 1 / 2 := by
    rw [eqPrice, ← commonKnowledge_eq_eqSet_of_eq_succ (by norm_num [P]) hstab,
      commonKnowledge_zero, hprice x]
  refine ⟨heq, ?_⟩
  rw [heq]
  cases f x <;> norm_num

/-- Two-bit XOR is not a weighted threshold function (immediate from `xorMarket_bids_and_eqPrice`
and Theorem 26.12). -/
theorem not_isWeightedThreshold_xor :
    ¬ IsWeightedThreshold (fun y : Fin 2 → Bool => xor (y 0) (y 1)) := by
  intro hf
  have h1 := eqPrice_eq_of_isWeightedThreshold (by decide) hf
    (P := fun _ : Fin 2 → Bool => (1 / 4 : ℝ)) (x := ![false, false]) (by norm_num)
  have h2 := (xorMarket_bids_and_eqPrice.2.2 ![false, false]).2
  exact h2 h1

end Examples

/-! ### Theorem 26.14: Convergence in at Most `n` Rounds (§26.5.6, p. 669) -/

section Theorem26_14

variable {n : ℕ}

/-- **Theorem 26.14** ([PennockSami2007, p. 669]): for any weighted threshold function `f` on `n`
inputs (`0 < n`), any prior `P`, and any state `x` with `0 < P x`, after at most `n` rounds of
trading (`r ≥ n`), common knowledge `Sʳ` has reached equilibrium `S^∞` and both the clearing price
and the common-knowledge expectation equal `f x`. -/
theorem convergence_in_n_rounds_of_isWeightedThreshold (hn : 0 < n)
    {f : (Fin n → Bool) → Bool} (hf : IsWeightedThreshold f) {P : (Fin n → Bool) → ℝ}
    {x : Fin n → Bool} (hx : 0 < P x) {r : ℕ} (hr : n ≤ r) :
    commonKnowledge f P x r = eqSet f P x ∧
      roundPrice f P (commonKnowledge f P x r) x = (if f x then 1 else 0) ∧
      condExpect f P (commonKnowledge f P x r) = (if f x then 1 else 0) := by
  have hS : commonKnowledge f P x r = eqSet f P x := commonKnowledge_eq_eqSet_of_le hx hr
  have hp : eqPrice f P x = if f x then 1 else 0 :=
    eqPrice_eq_of_isWeightedThreshold hn hf hx
  have hce : condExpect f P (eqSet f P x) = eqPrice f P x :=
    (equilibrium_commonKnowledge_of_aggregates hn (f := f) hx).1
  exact ⟨hS, by rw [hS]; exact hp, by rw [hS, hce, hp]⟩

end Theorem26_14

/-! ### Theorem 26.15: Worst-Case `n`-Round Lower Bound on `2n` Inputs (§26.5.6, p. 669) -/

section Theorem26_15

/-- Helper splitting `i : Fin k` with `i.1 < 2` into `⟨0, _⟩` or `⟨1, _⟩`. -/
private theorem fin_lt_two_cases {k : ℕ} (hk : 2 ≤ k) (i : Fin k) (hi : i.1 < 2) :
    i = ⟨0, by omega⟩ ∨ i = ⟨1, by omega⟩ := by
  rcases i with ⟨v, hv⟩
  match v with
  | 0 => left; rfl
  | 1 => right; rfl
  | _ + 2 => dsimp at hi; omega

/-- Split a sum over `Fin (2 * (m + 1))` into indices `0`, `1`, and the tail `j + 2`. -/
private theorem sum_fin_two_mul_succ {m : ℕ} (g : Fin (2 * (m + 1)) → ℝ) :
    ∑ i : Fin (2 * (m + 1)), g i =
      g ⟨0, by omega⟩ + g ⟨1, by omega⟩ + ∑ j : Fin (2 * m), g ⟨j.1 + 2, by omega⟩ := by
  let e : Fin (2 * (m + 1)) ≃ Fin ((2 * m + 1) + 1) := finCongr (by omega)
  rw [Fintype.sum_equiv e g (fun i => g ⟨i.1, by omega⟩) (fun _ => rfl),
    Fin.sum_univ_succ, Fin.sum_univ_succ]
  have h0 : g ⟨(0 : Fin ((2 * m + 1) + 1)).1, by omega⟩ = g ⟨0, by omega⟩ := rfl
  have h1 : g ⟨((0 : Fin (2 * m + 1)).succ).1, by omega⟩ = g ⟨1, by omega⟩ := rfl
  have htail : ∑ j : Fin (2 * m), g ⟨((j.succ).succ).1, by omega⟩ =
      ∑ j : Fin (2 * m), g ⟨j.1 + 2, by omega⟩ :=
    sum_congr rfl fun j _ => congrArg g (Fin.ext (by simp [Fin.val_succ, add_assoc]))
  rw [h0, h1, htail, add_assoc]

/-- Canonical empty `2 * 0`-bit state. -/
private def emptyState : Fin (2 * 0) → Bool := fun i => i.elim0

private theorem eq_emptyState (y : Fin (2 * 0) → Bool) : y = emptyState :=
  funext fun i => i.elim0

/-- Tail map dropping the outermost pair `(x 0, x 1)` from a `2(n + 1)`-bit vector. -/
private def tailPair {n : ℕ} (x : Fin (2 * (n + 1)) → Bool) : Fin (2 * n) → Bool :=
  fun i => x ⟨i.1 + 2, by omega⟩

/-- Prepend a pair `(a, b)` in front of a `2n`-bit vector. -/
private def consPair {n : ℕ} (a b : Bool) (y : Fin (2 * n) → Bool) : Fin (2 * (n + 1)) → Bool :=
  fun i =>
    if h0 : i.1 = 0 then a
    else if h1 : i.1 = 1 then b
    else y ⟨i.1 - 2, by omega⟩

private theorem consPair_of_val_zero {n : ℕ} (a b : Bool) (y : Fin (2 * n) → Bool)
    (i : Fin (2 * (n + 1))) (hi : i.1 = 0) : consPair a b y i = a := by
  simp [consPair, hi]

private theorem consPair_of_val_one {n : ℕ} (a b : Bool) (y : Fin (2 * n) → Bool)
    (i : Fin (2 * (n + 1))) (hi : i.1 = 1) : consPair a b y i = b := by
  simp [consPair, hi]

private theorem consPair_zero {n : ℕ} (a b : Bool) (y : Fin (2 * n) → Bool) :
    consPair a b y ⟨0, by omega⟩ = a :=
  consPair_of_val_zero a b y ⟨0, by omega⟩ rfl

private theorem consPair_one {n : ℕ} (a b : Bool) (y : Fin (2 * n) → Bool) :
    consPair a b y ⟨1, by omega⟩ = b :=
  consPair_of_val_one a b y ⟨1, by omega⟩ rfl

private theorem consPair_add_two {n : ℕ} (a b : Bool) (y : Fin (2 * n) → Bool)
    (i : Fin (2 * n)) :
    consPair a b y ⟨i.1 + 2, by omega⟩ = y i := by
  have h0 : ¬ i.1 + 2 = 0 := by omega
  have h1 : ¬ i.1 + 2 = 1 := by omega
  simp only [consPair, h0, ↓reduceDIte, h1]
  exact congrArg y (Fin.ext (by dsimp; omega))

private theorem tailPair_consPair {n : ℕ} (a b : Bool) (y : Fin (2 * n) → Bool) :
    tailPair (consPair a b y) = y :=
  funext fun i => consPair_add_two a b y i

private theorem consPair_tailPair {n : ℕ} (x : Fin (2 * (n + 1)) → Bool) :
    consPair (x ⟨0, by omega⟩) (x ⟨1, by omega⟩) (tailPair x) = x := by
  funext i
  by_cases h0 : i.1 = 0
  · rw [consPair_of_val_zero _ _ _ i h0]
    exact congrArg x (Fin.ext h0.symm)
  · by_cases h1 : i.1 = 1
    · rw [consPair_of_val_one _ _ _ i h1]
      exact congrArg x (Fin.ext h1.symm)
    · have hi : 2 ≤ i.1 := by omega
      simp only [consPair, h0, ↓reduceDIte, h1, tailPair]
      exact congrArg x (Fin.ext (by dsimp; omega))

/-- For `i.1 < 2`, `(false, true)` and `(true, false)` hit each Boolean value `b` once at `i`. -/
private theorem ite_consPair_alt_add {n : ℕ} {i : Fin (2 * (n + 1))} (hi : i.1 < 2)
    (y : Fin (2 * n) → Bool) (b : Bool) (r : ℝ) :
    (if consPair false true y i = b then r else 0) +
      (if consPair true false y i = b then r else 0) = r := by
  rcases fin_lt_two_cases (by omega) i hi with h0 | h1
  · rw [h0, consPair_zero, consPair_zero]; cases b <;> simp
  · rw [h1, consPair_one, consPair_one]; cases b <;> simp

/-- Equivalence splitting a `2(n + 1)`-bit state into its outermost pair `(x 0, x 1)` and tail. -/
private def splitPairEquiv (n : ℕ) :
    (Fin (2 * (n + 1)) → Bool) ≃ (Bool × Bool) × (Fin (2 * n) → Bool) where
  toFun x := ((x ⟨0, by omega⟩, x ⟨1, by omega⟩), tailPair x)
  invFun := fun ((a, b), y) => consPair a b y
  left_inv x := consPair_tailPair x
  right_inv := fun ((a, b), y) => by
    ext
    · rfl
    · rfl
    · exact congrFun (tailPair_consPair a b y) _

/-- Sum over all `Fin (2 * (n + 1)) → Bool` decomposed by the first two bits `(a, b)`. -/
private theorem sum_splitPair {n : ℕ} (g : (Fin (2 * (n + 1)) → Bool) → ℝ) :
    ∑ x : Fin (2 * (n + 1)) → Bool, g x =
      (∑ y : Fin (2 * n) → Bool, g (consPair false false y)) +
      (∑ y : Fin (2 * n) → Bool, g (consPair false true y)) +
      (∑ y : Fin (2 * n) → Bool, g (consPair true false y)) +
      (∑ y : Fin (2 * n) → Bool, g (consPair true true y)) := by
  rw [← Equiv.sum_comp (splitPairEquiv n).symm]
  simp only [splitPairEquiv, Equiv.coe_fn_symm_mk, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

private theorem sum_fin_two_bool (g : (Fin (2 * 1) → Bool) → ℝ) :
    ∑ x : Fin (2 * 1) → Bool, g x =
      g (consPair false false emptyState) +
      g (consPair false true emptyState) +
      g (consPair true false emptyState) +
      g (consPair true true emptyState) := by
  rw [sum_splitPair]
  have h1 (a b : Bool) : ∑ y : Fin (2 * 0) → Bool, g (consPair a b y) =
      g (consPair a b emptyState) := by
    have huniv : (Finset.univ : Finset (Fin (2 * 0) → Bool)) = {emptyState} := by
      ext y
      exact ⟨fun _ => mem_singleton.mpr (eq_emptyState y), fun _ => mem_univ y⟩
    rw [huniv, sum_singleton]
  rw [h1, h1, h1, h1]

/-- The nested carry-chain Boolean function `Cₙ : (Fin (2 * n) → Bool) → Bool`
[PennockSami2007, Theorem 26.15, p. 669]:
`C₀ = false`, `C_{n+1}(a, b, y) = (a ∧ b) ∨ ((a ∨ b) ∧ Cₙ(y))`. -/
def carryChain : ∀ (n : ℕ), (Fin (2 * n) → Bool) → Bool
  | 0, _ => false
  | n + 1, x =>
    let a := x ⟨0, by omega⟩
    let b := x ⟨1, by omega⟩
    (a && b) || ((a || b) && carryChain n (tailPair x))

@[local simp]
private theorem carryChain_zero (x : Fin (2 * 0) → Bool) : carryChain 0 x = false := by
  rfl

private theorem carryChain_consPair {n : ℕ} (a b : Bool) (y : Fin (2 * n) → Bool) :
    carryChain (n + 1) (consPair a b y) = ((a && b) || ((a || b) && carryChain n y)) := by
  simp only [carryChain, consPair_zero, consPair_one, tailPair_consPair]

/-- `carryChain n` is a weighted threshold function with exponentially decaying pair weights
`w(2j) = w(2j + 1) = 2^(n - 1 - j)` and threshold `2^n`. -/
theorem isWeightedThreshold_carryChain (n : ℕ) : IsWeightedThreshold (carryChain n) := by
  let S : ∀ m, (Fin (2 * m) → Bool) → ℝ := fun m x =>
    ∑ i : Fin (2 * m), (2 : ℝ) ^ (m - 1 - i.1 / 2) * (if x i then 1 else 0)
  have hS_step (m : ℕ) (x : Fin (2 * (m + 1)) → Bool) :
      S (m + 1) x = (2 : ℝ) ^ m * ((if x ⟨0, by omega⟩ then 1 else 0) +
        (if x ⟨1, by omega⟩ then 1 else 0)) + S m (tailPair x) := by
    simp only [S]
    rw [sum_fin_two_mul_succ]
    have htail : ∑ j : Fin (2 * m), (2 : ℝ) ^ (m + 1 - 1 - (j.1 + 2) / 2) *
        (if x ⟨j.1 + 2, by omega⟩ then 1 else 0) = S m (tailPair x) := by
      refine sum_congr rfl fun j _ => ?_
      have hexp : m + 1 - 1 - (j.1 + 2) / 2 = m - 1 - j.1 / 2 := by omega
      rw [hexp]; rfl
    rw [htail]
    have h0 : m + 1 - 1 - 0 / 2 = m := by omega
    have h1 : m + 1 - 1 - 1 / 2 = m := by omega
    rw [h0, h1]
    ring
  have hS_bounds : ∀ m (x : Fin (2 * m) → Bool), 0 ≤ S m x ∧ S m x ≤ 2 * (2 : ℝ) ^ m - 2 := by
    intro m
    induction m with
    | zero => intro x; simp [S]
    | succ m ih =>
      intro x
      rw [hS_step m x]
      have ⟨hlo, hhi⟩ := ih (tailPair x)
      have hpow : (2 : ℝ) ^ (m + 1) = 2 * (2 : ℝ) ^ m := by ring
      cases x ⟨0, by omega⟩ <;> cases x ⟨1, by omega⟩ <;>
        simp only [Bool.false_eq_true, ↓reduceIte, add_zero, zero_add, mul_zero, mul_one] <;>
        constructor <;> linarith [pow_pos (by norm_num : (0 : ℝ) < 2) m]
  have hchar : ∀ m (x : Fin (2 * m) → Bool), carryChain m x = true ↔ (2 : ℝ) ^ m ≤ S m x := by
    intro m
    induction m with
    | zero => intro x; simp [S]
    | succ m ih =>
      intro x
      rw [hS_step m x]
      have ⟨hlo, hhi⟩ := hS_bounds m (tailPair x)
      have hpow : (2 : ℝ) ^ (m + 1) = 2 * (2 : ℝ) ^ m := by ring
      have hpos : (0 : ℝ) < (2 : ℝ) ^ m := pow_pos (by norm_num) m
      cases hx0 : x ⟨0, by omega⟩ <;> cases hx1 : x ⟨1, by omega⟩
      · simp only [carryChain, hx0, hx1, Bool.and_self, Bool.or_self, Bool.false_and,
          Bool.false_eq_true, ↓reduceIte, add_zero, mul_zero, zero_add, false_iff, not_le]
        linarith
      · simp only [carryChain, hx0, hx1, Bool.false_and, Bool.false_or, Bool.true_and,
          Bool.false_eq_true, ↓reduceIte, zero_add, mul_one, ih (tailPair x)]
        constructor <;> intro h <;> linarith
      · simp only [carryChain, hx0, hx1, Bool.and_false, Bool.false_or, Bool.true_or, Bool.true_and,
          Bool.false_eq_true, ↓reduceIte, add_zero, mul_one, ih (tailPair x)]
        constructor <;> intro h <;> linarith
      · simp only [carryChain, hx0, hx1, Bool.and_self, Bool.true_or, ↓reduceIte, true_iff]
        linarith
  refine ⟨1 - (2 : ℝ) ^ n, fun i => (2 : ℝ) ^ (n - 1 - i.1 / 2), fun x => ?_⟩
  rw [hchar n x]
  change (2 : ℝ) ^ n ≤ S n x ↔ 1 ≤ 1 - (2 : ℝ) ^ n + S n x
  constructor <;> intro h <;> linarith

/-- Compensating state `(a, a, !a, !a, b, …, b)` of length `2(m + 2)` (with `a = true` giving
`carryChain = true` and `a = false` giving `carryChain = false`). -/
private def compState (m : ℕ) (a b : Bool) : Fin (2 * (m + 2)) → Bool :=
  consPair a a (consPair (!a) (!a) (fun _ => b))

private theorem carryChain_compState (m : ℕ) (a b : Bool) :
    carryChain (m + 2) (compState m a b) = a := by
  rw [compState, carryChain_consPair]; cases a <;> rfl

private theorem compState_apply_lt_two {m : ℕ} (a b : Bool) {i : Fin (2 * (m + 2))} (hi : i.1 < 2) :
    compState m a b i = a := by
  rcases fin_lt_two_cases (by omega) i hi with h0 | h1
  · rw [h0, compState, consPair_zero]
  · rw [h1, compState, consPair_one]

private theorem compState_apply_add_two {m : ℕ} (a b : Bool) (j : Fin (2 * (m + 1))) :
    compState m a b ⟨j.1 + 2, by omega⟩ = if j.1 < 2 then !a else b := by
  rw [compState, consPair_add_two]
  by_cases hj : j.1 < 2
  · simp only [hj, ↓reduceIte]
    rcases fin_lt_two_cases (by omega) j hj with h0 | h1
    · rw [h0, consPair_zero]
    · rw [h1, consPair_one]
  · simp only [hj, ↓reduceIte]
    have h0 : ¬ j.1 = 0 := by omega
    have h1 : ¬ j.1 = 1 := by omega
    simp [consPair, h0, h1]

/-- Unnormalized inductive weights for `carryPrior`:
* `n = 0`: constant `1`;
* `n = 1`: `2` on `(true, true)`, `1` on `(true, false)` and `(false, true)`, `0` on
  `(false, false)` (total mass `4`);
* `n = m + 2`: `(1/2) * carryWeight (m + 1) (tailPair x)` whenever `x 0 ≠ x 1`, plus `1/2` on each
  of the four compensating states `compState m a b` (`a, b : Bool`). -/
private noncomputable def carryWeight : ∀ (n : ℕ), (Fin (2 * n) → Bool) → ℝ
  | 0, _ => 1
  | 1, x =>
    match x ⟨0, by omega⟩, x ⟨1, by omega⟩ with
    | true, true => 2
    | true, false => 1
    | false, true => 1
    | false, false => 0
  | m + 2, x =>
    (if x ⟨0, by omega⟩ ≠ x ⟨1, by omega⟩ then
      (1 / 2 : ℝ) * carryWeight (m + 1) (tailPair x)
    else 0) +
    (if x = compState m true false then 1 / 2 else 0) +
    (if x = compState m true true then 1 / 2 else 0) +
    (if x = compState m false false then 1 / 2 else 0) +
    (if x = compState m false true then 1 / 2 else 0)

/-- The explicit prior distribution `Pₙ` on `{0, 1}^{2n}` achieving the `n`-round worst-case lower
bound for `carryChain n` [PennockSami2007, Theorem 26.15, p. 669]. -/
noncomputable def carryPrior (n : ℕ) (x : Fin (2 * n) → Bool) : ℝ :=
  if n = 0 then 1 else carryWeight n x / (2 * n + 2)

private theorem carryWeight_one_consPair (a b : Bool) (y : Fin (2 * 0) → Bool) :
    carryWeight 1 (consPair a b y) =
      match a, b with
      | true, true => 2
      | true, false => 1
      | false, true => 1
      | false, false => 0 := by
  simp only [carryWeight, consPair_zero, consPair_one]

private theorem carryWeight_nonneg : ∀ (n : ℕ) (x : Fin (2 * n) → Bool), 0 ≤ carryWeight n x
  | 0, _ => by norm_num [carryWeight]
  | 1, x => by
    simp only [carryWeight]
    cases x ⟨0, by omega⟩ <;> cases x ⟨1, by omega⟩ <;> norm_num
  | m + 2, x => by
    simp only [carryWeight]
    have hrec : 0 ≤ carryWeight (m + 1) (tailPair x) := carryWeight_nonneg (m + 1) (tailPair x)
    have h1 : 0 ≤ if x ⟨0, by omega⟩ ≠ x ⟨1, by omega⟩ then
        (1 / 2 : ℝ) * carryWeight (m + 1) (tailPair x) else 0 := by
      split_ifs <;> linarith
    have hc (a b : Bool) : 0 ≤ if x = compState m a b then (1 / 2 : ℝ) else 0 := by
      split_ifs <;> norm_num
    linarith [hc true false, hc true true, hc false false, hc false true]

private theorem carryWeight_consPair_alt {m : ℕ} {a b : Bool} (hab : a ≠ b)
    (y : Fin (2 * (m + 1)) → Bool) :
    carryWeight (m + 2) (consPair a b y) = (1 / 2 : ℝ) * carryWeight (m + 1) y := by
  have hne (c d : Bool) : consPair a b y ≠ compState m c d := fun h => by
    have h0 := congrFun h ⟨0, by omega⟩
    have h1 := congrFun h ⟨1, by omega⟩
    rw [consPair_zero, compState_apply_lt_two c d (show (0 : ℕ) < 2 by decide)] at h0
    rw [consPair_one, compState_apply_lt_two c d (show (1 : ℕ) < 2 by decide)] at h1
    exact hab (h0.trans h1.symm)
  simp only [carryWeight, consPair_zero, consPair_one, tailPair_consPair,
    hne true false, hne true true, hne false false, hne false true, ↓reduceIte, add_zero]
  split_ifs
  rfl

private theorem sum_carryWeight_split {m : ℕ} (g : (Fin (2 * (m + 2)) → Bool) → ℝ) :
    ∑ x : Fin (2 * (m + 2)) → Bool, carryWeight (m + 2) x * g x =
      (1 / 2 : ℝ) * (∑ y : Fin (2 * (m + 1)) → Bool, carryWeight (m + 1) y *
        (g (consPair false true y) + g (consPair true false y))) +
      (1 / 2 : ℝ) * (g (compState m true false) + g (compState m true true) +
        g (compState m false false) + g (compState m false true)) := by
  have hexpand (x : Fin (2 * (m + 2)) → Bool) :
      carryWeight (m + 2) x * g x =
        (if x ⟨0, by omega⟩ ≠ x ⟨1, by omega⟩ then
          (1 / 2 : ℝ) * carryWeight (m + 1) (tailPair x) * g x else 0) +
        (if x = compState m true false then (1 / 2 : ℝ) * g x else 0) +
        (if x = compState m true true then (1 / 2 : ℝ) * g x else 0) +
        (if x = compState m false false then (1 / 2 : ℝ) * g x else 0) +
        (if x = compState m false true then (1 / 2 : ℝ) * g x else 0) := by
    simp only [carryWeight]
    split_ifs <;> ring
  simp only [hexpand, sum_add_distrib, sum_ite_eq', mem_univ, ↓reduceIte]
  have hrec : ∑ x : Fin (2 * (m + 2)) → Bool,
      (if x ⟨0, by omega⟩ ≠ x ⟨1, by omega⟩ then
        (1 / 2 : ℝ) * carryWeight (m + 1) (tailPair x) * g x else 0) =
      (1 / 2 : ℝ) * ∑ y : Fin (2 * (m + 1)) → Bool, carryWeight (m + 1) y *
        (g (consPair false true y) + g (consPair true false y)) := by
    rw [sum_splitPair]
    simp only [consPair_zero, consPair_one, tailPair_consPair, ne_eq, not_true_eq_false,
      ↓reduceIte, Bool.false_eq_true, not_false_eq_true, Bool.true_eq_false, sum_const_zero,
      zero_add, add_zero, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun y _ => by ring
  rw [hrec]
  ring

private theorem sum_carryWeight_ite_eq_mul {n : ℕ} (p : (Fin (2 * n) → Bool) → Prop)
    [DecidablePred p] :
    (∑ x : Fin (2 * n) → Bool, if p x then carryWeight n x else 0) =
      ∑ x : Fin (2 * n) → Bool, carryWeight n x * (if p x then 1 else 0) :=
  sum_congr rfl fun _ _ => by split_ifs <;> ring

private theorem sum_carryWeight_head_quad {m : ℕ}
    (hT : (∑ y : Fin (2 * (m + 1)) → Bool,
        if carryChain (m + 1) y = true then carryWeight (m + 1) y else 0) = (m : ℝ) + 2)
    (hF : (∑ y : Fin (2 * (m + 1)) → Bool,
        if carryChain (m + 1) y = false then carryWeight (m + 1) y else 0) = (m : ℝ) + 2)
    {i : Fin (2 * (m + 2))} (hi : i.1 < 2) (b c : Bool) :
    (∑ x : Fin (2 * (m + 2)) → Bool,
      if x i = b ∧ carryChain (m + 2) x = c then carryWeight (m + 2) x else 0) =
      ((m : ℝ) + 2) / 2 + (if b = c then 1 else 0) := by
  rw [sum_carryWeight_ite_eq_mul, sum_carryWeight_split]
  have hrec : (∑ y : Fin (2 * (m + 1)) → Bool, carryWeight (m + 1) y *
      ((if consPair false true y i = b ∧
          carryChain (m + 2) (consPair false true y) = c then (1 : ℝ) else 0) +
       (if consPair true false y i = b ∧
          carryChain (m + 2) (consPair true false y) = c then (1 : ℝ) else 0))) =
      (m : ℝ) + 2 := by
    have hstep : ∀ y : Fin (2 * (m + 1)) → Bool,
        carryWeight (m + 1) y *
          ((if consPair false true y i = b ∧
              carryChain (m + 2) (consPair false true y) = c then (1 : ℝ) else 0) +
           (if consPair true false y i = b ∧
              carryChain (m + 2) (consPair true false y) = c then (1 : ℝ) else 0)) =
        if carryChain (m + 1) y = c then carryWeight (m + 1) y else 0 := fun y => by
      rw [carryChain_consPair, carryChain_consPair]
      simp only [Bool.false_and, Bool.false_or, Bool.true_and, Bool.and_false, Bool.true_or]
      by_cases hcy : carryChain (m + 1) y = c
      · simp only [hcy, and_true, ↓reduceIte, ite_consPair_alt_add hi y b (1 : ℝ), mul_one]
      · simp only [hcy, and_false, ↓reduceIte, add_zero, mul_zero]
    rw [sum_congr rfl fun y _ => hstep y]
    cases c
    · exact hF
    · exact hT
  rw [hrec, carryChain_compState, carryChain_compState, carryChain_compState, carryChain_compState,
    compState_apply_lt_two true false hi, compState_apply_lt_two true true hi,
    compState_apply_lt_two false false hi, compState_apply_lt_two false true hi]
  cases b <;> cases c <;> simp <;> ring

/-- Core mass invariants of `carryWeight (m + 1)` (input length `2(m + 1)`):
1. Total `f = true` mass and `f = false` mass both equal `m + 2` (total mass `2m + 4`).
2. For level-0 agents `i ∈ {0, 1}`:
   `∑_{x_i = true, f = true} W - ∑_{x_i = true, f = false} W = 1` and
   `∑_{x_i = false, f = false} W - ∑_{x_i = false, f = true} W = 1`.
3. For all deeper agents `i ≥ 2`: `f = true` and `f = false` have equal weight on `{x_i = true}`
   and equal weight on `{x_i = false}`. -/
private theorem carryWeight_invariants :
    ∀ m : ℕ,
      (∑ x : Fin (2 * (m + 1)) → Bool,
          if carryChain (m + 1) x = true then carryWeight (m + 1) x else 0) = (m : ℝ) + 2 ∧
      (∑ x : Fin (2 * (m + 1)) → Bool,
          if carryChain (m + 1) x = false then carryWeight (m + 1) x else 0) = (m : ℝ) + 2 ∧
      (∀ i : Fin (2 * (m + 1)), i.1 < 2 →
        (∑ x : Fin (2 * (m + 1)) → Bool,
          if x i = true ∧ carryChain (m + 1) x = true then carryWeight (m + 1) x else 0) -
        (∑ x : Fin (2 * (m + 1)) → Bool,
          if x i = true ∧ carryChain (m + 1) x = false then carryWeight (m + 1) x else 0) = 1 ∧
        (∑ x : Fin (2 * (m + 1)) → Bool,
          if x i = false ∧ carryChain (m + 1) x = false then carryWeight (m + 1) x else 0) -
        (∑ x : Fin (2 * (m + 1)) → Bool,
          if x i = false ∧ carryChain (m + 1) x = true then carryWeight (m + 1) x else 0) = 1) ∧
      (∀ i : Fin (2 * (m + 1)), 2 ≤ i.1 →
        (∑ x : Fin (2 * (m + 1)) → Bool,
          if x i = true ∧ carryChain (m + 1) x = true then carryWeight (m + 1) x else 0) =
        (∑ x : Fin (2 * (m + 1)) → Bool,
          if x i = true ∧ carryChain (m + 1) x = false then carryWeight (m + 1) x else 0) ∧
        (∑ x : Fin (2 * (m + 1)) → Bool,
          if x i = false ∧ carryChain (m + 1) x = true then carryWeight (m + 1) x else 0) =
        (∑ x : Fin (2 * (m + 1)) → Bool,
          if x i = false ∧ carryChain (m + 1) x = false then carryWeight (m + 1) x else 0)) := by
  intro m
  induction m with
  | zero =>
    have hW (a b : Bool) : carryWeight (0 + 1) (consPair a b emptyState) =
        carryWeight 1 (consPair a b emptyState) := rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [sum_fin_two_bool]
      simp only [carryChain_consPair, hW, carryWeight_one_consPair]
      norm_num
    · rw [sum_fin_two_bool]
      simp only [carryChain_consPair, hW, carryWeight_one_consPair]
      norm_num
    · intro i hi
      rcases fin_lt_two_cases (by omega) i hi with h0 | h1
      · rw [h0]; constructor <;>
          (rw [sum_fin_two_bool, sum_fin_two_bool]
           simp only [carryChain_consPair, hW, carryWeight_one_consPair, consPair]
           norm_num)
      · rw [h1]; constructor <;>
          (rw [sum_fin_two_bool, sum_fin_two_bool]
           simp only [carryChain_consPair, hW, carryWeight_one_consPair, consPair]
           norm_num)
    · intro i hi; omega
  | succ m ih =>
    obtain ⟨ihT, ihF, ihL0, ihDeep⟩ := ih
    have hsplit_c (c : Bool) :
        (∑ x : Fin (2 * (m + 2)) → Bool,
          if carryChain (m + 2) x = c then carryWeight (m + 2) x else 0) =
          ((m + 1 : ℕ) : ℝ) + 2 := by
      have hsp : (∑ x : Fin (2 * (m + 2)) → Bool,
          if carryChain (m + 2) x = c then carryWeight (m + 2) x else 0) =
        (∑ x : Fin (2 * (m + 2)) → Bool,
          if x ⟨0, by omega⟩ = true ∧ carryChain (m + 2) x = c then carryWeight (m + 2) x
          else 0) +
        (∑ x : Fin (2 * (m + 2)) → Bool,
          if x ⟨0, by omega⟩ = false ∧ carryChain (m + 2) x = c then carryWeight (m + 2) x
          else 0) := by
        rw [← sum_add_distrib]
        exact sum_congr rfl fun x _ => by
          cases x ⟨0, by omega⟩ <;> cases carryChain (m + 2) x <;> cases c <;> simp
      rw [hsp, sum_carryWeight_head_quad ihT ihF (i := ⟨0, by omega⟩) (show (0 : ℕ) < 2 by decide),
        sum_carryWeight_head_quad ihT ihF (i := ⟨0, by omega⟩) (show (0 : ℕ) < 2 by decide)]
      cases c <;> (push_cast; norm_num; ring)
    refine ⟨hsplit_c true, hsplit_c false, fun i hi => ?_, fun i hi => ?_⟩
    · rw [sum_carryWeight_head_quad ihT ihF hi true true,
        sum_carryWeight_head_quad ihT ihF hi true false,
        sum_carryWeight_head_quad ihT ihF hi false false,
        sum_carryWeight_head_quad ihT ihF hi false true]
      norm_num
    · let j : Fin (2 * (m + 1)) := ⟨i.1 - 2, by omega⟩
      have hij : i = ⟨j.1 + 2, by omega⟩ := Fin.ext (by simp [j]; omega)
      have hrec_eval (b c : Bool) :
          (∑ y : Fin (2 * (m + 1)) → Bool, carryWeight (m + 1) y *
            ((if consPair false true y i = b ∧
                carryChain (m + 2) (consPair false true y) = c then (1 : ℝ) else 0) +
             (if consPair true false y i = b ∧
                carryChain (m + 2) (consPair true false y) = c then (1 : ℝ) else 0))) =
          2 * (∑ y : Fin (2 * (m + 1)) → Bool,
            if y j = b ∧ carryChain (m + 1) y = c then carryWeight (m + 1) y else 0) := by
        rw [mul_sum]
        refine sum_congr rfl fun y _ => ?_
        rw [hij, consPair_add_two, consPair_add_two, carryChain_consPair, carryChain_consPair]
        cases y j <;> cases b <;> cases carryChain (m + 1) y <;> cases c <;> simp <;> ring
      have hcs (a b : Bool) : compState m a b i = if j.1 < 2 then !a else b := by
        rw [hij]; exact compState_apply_add_two a b j
      have hdiff_step (b : Bool) :
          (∑ x : Fin (2 * (m + 2)) → Bool,
            if x i = b ∧ carryChain (m + 2) x = true then carryWeight (m + 2) x else 0) -
          (∑ x : Fin (2 * (m + 2)) → Bool,
            if x i = b ∧ carryChain (m + 2) x = false then carryWeight (m + 2) x else 0) =
          (∑ y : Fin (2 * (m + 1)) → Bool,
            if y j = b ∧ carryChain (m + 1) y = true then carryWeight (m + 1) y else 0) -
          (∑ y : Fin (2 * (m + 1)) → Bool,
            if y j = b ∧ carryChain (m + 1) y = false then carryWeight (m + 1) y else 0) +
          (if j.1 < 2 then (if b then -1 else 1) else 0) := by
        rw [sum_carryWeight_ite_eq_mul, sum_carryWeight_ite_eq_mul, sum_carryWeight_split,
          sum_carryWeight_split, hrec_eval, hrec_eval, carryChain_compState, carryChain_compState,
          carryChain_compState, carryChain_compState, hcs true false, hcs true true,
          hcs false false, hcs false true]
        by_cases hj : j.1 < 2 <;> cases b <;> simp [hj] <;> ring
      by_cases hj : j.1 < 2
      · obtain ⟨hL0_t, hL0_f⟩ := ihL0 j hj
        have ht := hdiff_step true
        have hf := hdiff_step false
        simp only [hj, Bool.false_eq_true, ↓reduceIte] at ht hf
        exact ⟨by linarith, by linarith⟩
      · obtain ⟨hD_t, hD_f⟩ := ihDeep j (by omega)
        have ht := hdiff_step true
        have hf := hdiff_step false
        simp only [hj, ↓reduceIte, add_zero] at ht hf
        exact ⟨by linarith, by linarith⟩

private theorem sum_carryWeight_total (m : ℕ) :
    ∑ x : Fin (2 * (m + 1)) → Bool, carryWeight (m + 1) x = 2 * ((m + 1 : ℕ) : ℝ) + 2 := by
  obtain ⟨hT, hF, _, _⟩ := carryWeight_invariants m
  have hsplit : ∑ x : Fin (2 * (m + 1)) → Bool, carryWeight (m + 1) x =
      (∑ x : Fin (2 * (m + 1)) → Bool,
        if carryChain (m + 1) x = true then carryWeight (m + 1) x else 0) +
      (∑ x : Fin (2 * (m + 1)) → Bool,
        if carryChain (m + 1) x = false then carryWeight (m + 1) x else 0) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun x _ => by cases carryChain (m + 1) x <;> simp
  rw [hsplit, hT, hF]
  push_cast; ring

/-- `carryPrior n` is a valid probability distribution (`IsMixedStrategy`) on `{0, 1}^{2n}` for
every `n : ℕ`. -/
theorem isMixedStrategy_carryPrior (n : ℕ) : IsMixedStrategy (carryPrior n) := by
  cases n with
  | zero =>
    refine isMixedStrategy_iff.mpr ⟨fun _ => by norm_num [carryPrior], ?_⟩
    simp [carryPrior]
  | succ m =>
    have hden : (0 : ℝ) < 2 * ((m + 1 : ℕ) : ℝ) + 2 := by positivity
    refine isMixedStrategy_iff.mpr ⟨fun x => ?_, ?_⟩
    · simp only [carryPrior, Nat.succ_ne_zero, ↓reduceIte]
      exact div_nonneg (carryWeight_nonneg (m + 1) x) hden.le
    · simp only [carryPrior, Nat.succ_ne_zero, ↓reduceIte, div_eq_mul_inv, ← sum_mul]
      rw [sum_carryWeight_total m, mul_inv_cancel₀ hden.ne']

/-- Lift a set `T ⊆ {0, 1}^{2n}` by prepending the two alternating pairs `(false, true)` and
`(true, false)`. -/
private def liftAlt {n : ℕ} (T : Finset (Fin (2 * n) → Bool)) :
    Finset (Fin (2 * (n + 1)) → Bool) :=
  Finset.univ.filter fun x => x ⟨0, by omega⟩ ≠ x ⟨1, by omega⟩ ∧ tailPair x ∈ T

private theorem mem_liftAlt {n : ℕ} {T : Finset (Fin (2 * n) → Bool)}
    {x : Fin (2 * (n + 1)) → Bool} :
    x ∈ liftAlt T ↔ x ⟨0, by omega⟩ ≠ x ⟨1, by omega⟩ ∧ tailPair x ∈ T := by
  simp only [liftAlt, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem sum_liftAlt {n : ℕ} (T : Finset (Fin (2 * n) → Bool))
    (g : (Fin (2 * (n + 1)) → Bool) → ℝ) :
    ∑ x ∈ liftAlt T, g x =
      (∑ y ∈ T, g (consPair false true y)) + ∑ y ∈ T, g (consPair true false y) := by
  rw [liftAlt, sum_filter, sum_splitPair]
  simp only [consPair_zero, consPair_one, tailPair_consPair, ne_eq, not_true_eq_false, false_and,
    ↓reduceIte, Bool.false_eq_true, not_false_eq_true, true_and, Bool.true_eq_false,
    sum_const_zero, zero_add, add_zero, ← sum_filter, filter_mem_eq_inter, univ_inter]

/-- Prefix-extension invariance: on `liftAlt T`, `condExpect` is unchanged, agents `0, 1` bid
`condExpect`, agents `j + 2` mirror agent `j` on `T`, and `roundPrice` is a strictly increasing
affine function of `roundPrice` on `T`. -/
private theorem liftAlt_condExpect_and_roundPrice {m : ℕ} {T : Finset (Fin (2 * (m + 1)) → Bool)} :
    condExpect (carryChain (m + 2)) (carryWeight (m + 2)) (liftAlt T) =
      condExpect (carryChain (m + 1)) (carryWeight (m + 1)) T ∧
    ∀ x : Fin (2 * (m + 2)) → Bool,
      roundPrice (carryChain (m + 2)) (carryWeight (m + 2)) (liftAlt T) x =
        (2 * condExpect (carryChain (m + 1)) (carryWeight (m + 1)) T +
          (2 * (m + 1) : ℝ) *
            roundPrice (carryChain (m + 1)) (carryWeight (m + 1)) T (tailPair x)) /
          (2 * (m + 2) : ℝ) := by
  have hce : condExpect (carryChain (m + 2)) (carryWeight (m + 2)) (liftAlt T) =
      condExpect (carryChain (m + 1)) (carryWeight (m + 1)) T := by
    rw [condExpect_apply, condExpect_apply, sum_liftAlt, sum_liftAlt]
    have hnum : (∑ y ∈ T, if carryChain (m + 2) (consPair false true y) then
          carryWeight (m + 2) (consPair false true y) else 0) +
        (∑ y ∈ T, if carryChain (m + 2) (consPair true false y) then
          carryWeight (m + 2) (consPair true false y) else 0) =
        ∑ y ∈ T, if carryChain (m + 1) y then carryWeight (m + 1) y else 0 := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun y _ => ?_
      rw [carryChain_consPair, carryChain_consPair,
        carryWeight_consPair_alt (by decide), carryWeight_consPair_alt (by decide)]
      cases carryChain (m + 1) y
      · simp
      · simp; ring
    have hden : (∑ y ∈ T, carryWeight (m + 2) (consPair false true y)) +
        (∑ y ∈ T, carryWeight (m + 2) (consPair true false y)) =
        ∑ y ∈ T, carryWeight (m + 1) y := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun y _ => ?_
      rw [carryWeight_consPair_alt (by decide), carryWeight_consPair_alt (by decide)]
      ring
    rw [hnum, hden]
  refine ⟨hce, fun x => ?_⟩
  have hbid0 (i : Fin (2 * (m + 2))) (hi : i.1 < 2) :
      agentBid (carryChain (m + 2)) (carryWeight (m + 2)) (liftAlt T) i x =
        condExpect (carryChain (m + 1)) (carryWeight (m + 1)) T := by
    rw [agentBid_apply, condExpect_apply, condExpect_apply, agentKnowledge, sum_filter, sum_filter,
      sum_liftAlt, sum_liftAlt]
    have hnum : (∑ y ∈ T, if consPair false true y i = x i then
          (if carryChain (m + 2) (consPair false true y) then
            carryWeight (m + 2) (consPair false true y) else 0) else 0) +
        (∑ y ∈ T, if consPair true false y i = x i then
          (if carryChain (m + 2) (consPair true false y) then
            carryWeight (m + 2) (consPair true false y) else 0) else 0) =
        (1 / 2 : ℝ) * ∑ y ∈ T, if carryChain (m + 1) y then carryWeight (m + 1) y else 0 := by
      rw [← sum_add_distrib, mul_sum]
      refine sum_congr rfl fun y _ => ?_
      rw [carryChain_consPair, carryChain_consPair,
        carryWeight_consPair_alt (by decide), carryWeight_consPair_alt (by decide)]
      simp only [Bool.false_and, Bool.false_or, Bool.true_and, Bool.and_false, Bool.true_or]
      cases carryChain (m + 1) y
      · simp
      · simpa only [↓reduceIte] using
          ite_consPair_alt_add hi y (x i) ((1 / 2 : ℝ) * carryWeight (m + 1) y)
    have hden : (∑ y ∈ T, if consPair false true y i = x i then
          carryWeight (m + 2) (consPair false true y) else 0) +
        (∑ y ∈ T, if consPair true false y i = x i then
          carryWeight (m + 2) (consPair true false y) else 0) =
        (1 / 2 : ℝ) * ∑ y ∈ T, carryWeight (m + 1) y := by
      rw [← sum_add_distrib, mul_sum]
      refine sum_congr rfl fun y _ => ?_
      rw [carryWeight_consPair_alt (by decide), carryWeight_consPair_alt (by decide)]
      exact ite_consPair_alt_add hi y (x i) ((1 / 2 : ℝ) * carryWeight (m + 1) y)
    rw [hnum, hden, mul_div_mul_left _ _ (by norm_num)]
  have hbid_tail (j : Fin (2 * (m + 1))) :
      agentBid (carryChain (m + 2)) (carryWeight (m + 2)) (liftAlt T) ⟨j.1 + 2, by omega⟩ x =
        agentBid (carryChain (m + 1)) (carryWeight (m + 1)) T j (tailPair x) := by
    rw [agentBid_apply, agentBid_apply, condExpect_apply, condExpect_apply, agentKnowledge,
      agentKnowledge, sum_filter, sum_filter, sum_filter, sum_filter, sum_liftAlt, sum_liftAlt]
    have hnum : (∑ y ∈ T, if consPair false true y ⟨j.1 + 2, by omega⟩ = x ⟨j.1 + 2, by omega⟩
          then (if carryChain (m + 2) (consPair false true y) then
            carryWeight (m + 2) (consPair false true y) else 0) else 0) +
        (∑ y ∈ T, if consPair true false y ⟨j.1 + 2, by omega⟩ = x ⟨j.1 + 2, by omega⟩
          then (if carryChain (m + 2) (consPair true false y) then
            carryWeight (m + 2) (consPair true false y) else 0) else 0) =
        ∑ y ∈ T, if y j = tailPair x j then
          (if carryChain (m + 1) y then carryWeight (m + 1) y else 0) else 0 := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun y _ => ?_
      rw [consPair_add_two, consPair_add_two, carryChain_consPair, carryChain_consPair,
        carryWeight_consPair_alt (by decide), carryWeight_consPair_alt (by decide)]
      change (if y j = tailPair x j then _ else 0) + (if y j = tailPair x j then _ else 0) = _
      by_cases hj : y j = tailPair x j
      · simp only [hj, ↓reduceIte]
        cases carryChain (m + 1) y
        · simp
        · simp; ring
      · simp [hj]
    have hden : (∑ y ∈ T, if consPair false true y ⟨j.1 + 2, by omega⟩ = x ⟨j.1 + 2, by omega⟩
          then carryWeight (m + 2) (consPair false true y) else 0) +
        (∑ y ∈ T, if consPair true false y ⟨j.1 + 2, by omega⟩ = x ⟨j.1 + 2, by omega⟩
          then carryWeight (m + 2) (consPair true false y) else 0) =
        ∑ y ∈ T, if y j = tailPair x j then carryWeight (m + 1) y else 0 := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun y _ => ?_
      rw [consPair_add_two, consPair_add_two, carryWeight_consPair_alt (by decide),
        carryWeight_consPair_alt (by decide)]
      change (if y j = tailPair x j then _ else 0) + (if y j = tailPair x j then _ else 0) = _
      split_ifs <;> ring
    rw [hnum, hden]
  rw [roundPrice_apply, sum_fin_two_mul_succ,
    hbid0 ⟨0, by omega⟩ (show (0 : ℕ) < 2 by decide),
    hbid0 ⟨1, by omega⟩ (show (1 : ℕ) < 2 by decide),
    sum_congr rfl fun j _ => hbid_tail j]
  have htail_sum : ∑ j : Fin (2 * (m + 1)),
      agentBid (carryChain (m + 1)) (carryWeight (m + 1)) T j (tailPair x) =
      (2 * (m + 1) : ℝ) *
        roundPrice (carryChain (m + 1)) (carryWeight (m + 1)) T (tailPair x) := by
    rw [roundPrice_apply]
    have hne : ((2 * (m + 1) : ℕ) : ℝ) ≠ 0 := by positivity
    have hcast : ((2 * (m + 1) : ℕ) : ℝ) = (2 * (m + 1) : ℝ) := by push_cast; ring
    rw [← hcast, mul_div_cancel₀ _ hne]
  rw [htail_sum]
  push_cast
  ring

private theorem sum_priorSupport_carryWeight_filter {n : ℕ}
    (p : (Fin (2 * n) → Bool) → Prop) [DecidablePred p] :
    (∑ z ∈ (priorSupport (carryWeight n)).filter p, carryWeight n z) =
      ∑ z : Fin (2 * n) → Bool, if p z then carryWeight n z else 0 := by
  rw [sum_filter]
  refine (sum_subset (subset_univ _) fun z _ hz => ?_).trans (sum_congr rfl fun _ _ => rfl)
  have h0 : carryWeight n z = 0 :=
    le_antisymm (le_of_not_gt (mt mem_priorSupport.mpr hz)) (carryWeight_nonneg n z)
  simp [h0]

private theorem sum_priorSupport_carryWeight_filter_f {n : ℕ}
    (p : (Fin (2 * n) → Bool) → Prop) [DecidablePred p] :
    (∑ z ∈ (priorSupport (carryWeight n)).filter p,
        if carryChain n z then carryWeight n z else 0) =
      ∑ z : Fin (2 * n) → Bool,
        if p z ∧ carryChain n z = true then carryWeight n z else 0 := by
  rw [sum_filter]
  refine (sum_subset (subset_univ _) fun z _ hz => ?_).trans
    (sum_congr rfl fun z _ => by cases carryChain n z <;> split_ifs <;> simp_all)
  have h0 : carryWeight n z = 0 :=
    le_antisymm (le_of_not_gt (mt mem_priorSupport.mpr hz)) (carryWeight_nonneg n z)
  simp [h0]

private theorem sum_carryWeight_coord_split {m : ℕ} (i : Fin (2 * (m + 2))) (b : Bool) :
    (∑ z : Fin (2 * (m + 2)) → Bool, if z i = b then carryWeight (m + 2) z else 0) =
      (∑ z : Fin (2 * (m + 2)) → Bool,
        if z i = b ∧ carryChain (m + 2) z = true then carryWeight (m + 2) z else 0) +
      (∑ z : Fin (2 * (m + 2)) → Bool,
        if z i = b ∧ carryChain (m + 2) z = false then carryWeight (m + 2) z else 0) := by
  rw [← sum_add_distrib]
  exact sum_congr rfl fun z _ => by cases carryChain (m + 2) z <;> split_ifs <;> simp_all

/-- In round 1 on `carryWeight (m + 2)`, every agent `i ≥ 2` bids `1/2` on any positive-mass
state. -/
private theorem carryWeight_round1_deep_bid {m : ℕ} {i : Fin (2 * (m + 2))} (hi : 2 ≤ i.1)
    {y : Fin (2 * (m + 2)) → Bool} (hy : y ∈ priorSupport (carryWeight (m + 2))) :
    agentBid (carryChain (m + 2)) (carryWeight (m + 2))
      (priorSupport (carryWeight (m + 2))) i y = 1 / 2 := by
  obtain ⟨hDt, hDf⟩ := (carryWeight_invariants (m + 1)).2.2.2 i hi
  have hKpos : 0 < ∑ z ∈ agentKnowledge (priorSupport (carryWeight (m + 2))) i y,
      carryWeight (m + 2) z :=
    sum_pos_of_subset_priorSupport (filter_subset _ _) ⟨y, mem_agentKnowledge.mpr ⟨hy, rfl⟩⟩
  rw [agentKnowledge, sum_priorSupport_carryWeight_filter] at hKpos
  rw [agentBid_apply, condExpect_apply, agentKnowledge,
    sum_priorSupport_carryWeight_filter_f, sum_priorSupport_carryWeight_filter,
    sum_carryWeight_coord_split]
  cases hyi : y i
  · rw [hyi, sum_carryWeight_coord_split] at hKpos
    rw [← hDf]
    have hne : (∑ z : Fin (2 * (m + 2)) → Bool,
        if z i = false ∧ carryChain (m + 2) z = true then carryWeight (m + 2) z else 0) ≠ 0 := by
      linarith
    field_simp [hne]; ring
  · rw [hyi, sum_carryWeight_coord_split] at hKpos
    rw [← hDt]
    have hne : (∑ z : Fin (2 * (m + 2)) → Bool,
        if z i = true ∧ carryChain (m + 2) z = true then carryWeight (m + 2) z else 0) ≠ 0 := by
      linarith
    field_simp [hne]; ring

/-- In round 1 on `carryWeight (m + 2)`, agents `i ∈ {0, 1}` bid `(m + 4)/(2m + 6)` on `true` and
`(m + 2)/(2m + 6)` on `false`. -/
private theorem carryWeight_round1_head_bid {m : ℕ} {i : Fin (2 * (m + 2))} (hi : i.1 < 2)
    (y : Fin (2 * (m + 2)) → Bool) :
    agentBid (carryChain (m + 2)) (carryWeight (m + 2))
      (priorSupport (carryWeight (m + 2))) i y =
      if y i then ((m : ℝ) + 4) / (2 * (m : ℝ) + 6)
      else ((m : ℝ) + 2) / (2 * (m : ℝ) + 6) := by
  obtain ⟨hT', hF', _, _⟩ := carryWeight_invariants m
  rw [agentBid_apply, condExpect_apply, agentKnowledge,
    sum_priorSupport_carryWeight_filter_f, sum_priorSupport_carryWeight_filter,
    sum_carryWeight_coord_split]
  have hne : (2 * (m : ℝ) + 6) ≠ 0 := by positivity
  cases hyi : y i
  · rw [sum_carryWeight_head_quad hT' hF' hi false true,
      sum_carryWeight_head_quad hT' hF' hi false false]
    simp only [Bool.false_eq_true, ↓reduceIte]
    field_simp [hne]; ring
  · rw [sum_carryWeight_head_quad hT' hF' hi true true,
      sum_carryWeight_head_quad hT' hF' hi true false]
    simp only [Bool.true_eq_false, ↓reduceIte]
    field_simp [hne]; ring

/-- Round-1 behavior on `carryWeight (m + 2)`: for any positive-mass state `x` with `x 0 ≠ x 1`,
`roundPrice = 1/2` and `S¹(x) = liftAlt (priorSupport (carryWeight (m + 1)))`. -/
private theorem carryWeight_round1_alt {m : ℕ} {x : Fin (2 * (m + 2)) → Bool}
    (hx01 : x ⟨0, by omega⟩ ≠ x ⟨1, by omega⟩) (hxpos : 0 < carryWeight (m + 2) x) :
    roundPrice (carryChain (m + 2)) (carryWeight (m + 2)) (priorSupport (carryWeight (m + 2))) x =
        1 / 2 ∧
      commonKnowledge (carryChain (m + 2)) (carryWeight (m + 2)) x 1 =
        liftAlt (priorSupport (carryWeight (m + 1))) := by
  have hprice_eval (y : Fin (2 * (m + 2)) → Bool) (hy : y ∈ priorSupport (carryWeight (m + 2))) :
      roundPrice (carryChain (m + 2)) (carryWeight (m + 2))
        (priorSupport (carryWeight (m + 2))) y =
        ((if y ⟨0, by omega⟩ then ((m : ℝ) + 4) / (2 * (m : ℝ) + 6)
          else ((m : ℝ) + 2) / (2 * (m : ℝ) + 6)) +
         (if y ⟨1, by omega⟩ then ((m : ℝ) + 4) / (2 * (m : ℝ) + 6)
          else ((m : ℝ) + 2) / (2 * (m : ℝ) + 6)) + ((m : ℝ) + 1)) /
          (2 * ((m : ℝ) + 2)) := by
    rw [roundPrice_apply, sum_fin_two_mul_succ,
      carryWeight_round1_head_bid (i := ⟨0, by omega⟩) (show (0 : ℕ) < 2 by decide) y,
      carryWeight_round1_head_bid (i := ⟨1, by omega⟩) (show (1 : ℕ) < 2 by decide) y]
    have hdeep_sum : ∑ j : Fin (2 * (m + 1)),
        agentBid (carryChain (m + 2)) (carryWeight (m + 2))
          (priorSupport (carryWeight (m + 2))) ⟨j.1 + 2, by omega⟩ y = (m : ℝ) + 1 := by
      rw [sum_congr rfl fun j _ => carryWeight_round1_deep_bid (show 2 ≤ j.1 + 2 by omega) hy,
        sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    rw [hdeep_sum]
    push_cast; ring
  have hprice_iff (y : Fin (2 * (m + 2)) → Bool) (hy : y ∈ priorSupport (carryWeight (m + 2))) :
      roundPrice (carryChain (m + 2)) (carryWeight (m + 2))
        (priorSupport (carryWeight (m + 2))) y = 1 / 2 ↔
        y ⟨0, by omega⟩ ≠ y ⟨1, by omega⟩ := by
    rw [hprice_eval y hy]
    have hne1 : (2 * (m : ℝ) + 6) ≠ 0 := by positivity
    have hne2 : (2 * ((m : ℝ) + 2)) ≠ 0 := by positivity
    cases hy0 : y ⟨0, by omega⟩ <;> cases hy1 : y ⟨1, by omega⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false, iff_false]
      intro h
      rw [div_eq_iff hne2] at h
      have : 2 * ((m : ℝ) + 2) = 2 * (m : ℝ) + 6 := by field_simp [hne1] at h; linarith
      linarith
    · simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, not_false_eq_true, iff_true]
      field_simp [hne1, hne2]; ring
    · simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, Bool.true_eq_false, not_false_eq_true,
        iff_true]
      field_simp [hne1, hne2]; ring
    · simp only [↓reduceIte, ne_eq, not_true_eq_false, iff_false]
      intro h
      rw [div_eq_iff hne2] at h
      have : 2 * ((m : ℝ) + 4) = 2 * (m : ℝ) + 6 := by field_simp [hne1] at h; linarith
      linarith
  have hpx : roundPrice (carryChain (m + 2)) (carryWeight (m + 2))
      (priorSupport (carryWeight (m + 2))) x = 1 / 2 :=
    (hprice_iff x (mem_priorSupport.mpr hxpos)).mpr hx01
  refine ⟨hpx, ?_⟩
  ext y
  rw [mem_commonKnowledge_succ, commonKnowledge_zero, mem_liftAlt]
  constructor
  · rintro ⟨hy, hpy⟩
    have hy01 : y ⟨0, by omega⟩ ≠ y ⟨1, by omega⟩ := (hprice_iff y hy).mp (hpy.trans hpx)
    refine ⟨hy01, mem_priorSupport.mpr ?_⟩
    have hyw := mem_priorSupport.mp hy
    rw [← consPair_tailPair y, carryWeight_consPair_alt hy01] at hyw
    linarith
  · rintro ⟨hy01, hytail⟩
    have hypos : 0 < carryWeight (m + 2) y := by
      rw [← consPair_tailPair y, carryWeight_consPair_alt hy01]
      linarith [mem_priorSupport.mp hytail]
    exact ⟨mem_priorSupport.mpr hypos,
      ((hprice_iff y (mem_priorSupport.mpr hypos)).mpr hy01).trans hpx.symm⟩

/-- Alternating `2n`-bit input `(true, false, true, false, …, true, false)` on which
`carryChain n = false`. -/
def carryInputFalse (n : ℕ) : Fin (2 * n) → Bool :=
  fun i => decide (i.1 % 2 = 0)

/-- Worst-case `2n`-bit input `(true, false, …, true, false, true, true)` on which
`carryChain n = true` (for `n > 0`). -/
def carryInputTrue (n : ℕ) : Fin (2 * n) → Bool :=
  fun i => decide (i.1 % 2 = 0 ∨ i.1 + 1 = 2 * n)

private theorem carryInputFalse_consPair (n : ℕ) :
    carryInputFalse (n + 1) = consPair true false (carryInputFalse n) := by
  funext i
  by_cases h0 : i.1 = 0
  · rw [consPair_of_val_zero _ _ _ i h0]; simp [carryInputFalse, h0]
  · by_cases h1 : i.1 = 1
    · rw [consPair_of_val_one _ _ _ i h1]; simp [carryInputFalse, h1]
    · have hi : 2 ≤ i.1 := by omega
      simp only [carryInputFalse, consPair, h0, ↓reduceDIte, h1, decide_eq_decide]
      omega

private theorem carryInputTrue_one :
    carryInputTrue 1 = consPair true true emptyState := by
  funext i
  rcases fin_lt_two_cases (by omega) i (by omega) with h0 | h1
  · rw [h0, consPair_zero]; rfl
  · rw [h1, consPair_one]; rfl

private theorem carryInputTrue_consPair (m : ℕ) :
    carryInputTrue (m + 2) = consPair true false (carryInputTrue (m + 1)) := by
  funext i
  by_cases h0 : i.1 = 0
  · rw [consPair_of_val_zero _ _ _ i h0]; simp [carryInputTrue, h0]
  · by_cases h1 : i.1 = 1
    · rw [consPair_of_val_one _ _ _ i h1]
      simp only [carryInputTrue, h1, decide_eq_false_iff_not]; omega
    · have hi : 2 ≤ i.1 := by omega
      simp only [carryInputTrue, consPair, h0, ↓reduceDIte, h1, decide_eq_decide]
      omega

private theorem carryChain_carryInputFalse : ∀ n, carryChain n (carryInputFalse n) = false
  | 0 => rfl
  | n + 1 => by
    rw [carryInputFalse_consPair, carryChain_consPair]
    simp [carryChain_carryInputFalse n]

private theorem carryChain_carryInputTrue :
    ∀ m, carryChain (m + 1) (carryInputTrue (m + 1)) = true
  | 0 => by rw [carryInputTrue_one, carryChain_consPair]; rfl
  | m + 1 => by
    rw [carryInputTrue_consPair, carryChain_consPair]
    simp [carryChain_carryInputTrue m]

private theorem carryWeight_carryInputFalse_pos :
    ∀ m, 0 < carryWeight (m + 1) (carryInputFalse (m + 1))
  | 0 => by
    rw [carryInputFalse_consPair, carryWeight_one_consPair]
    norm_num
  | m + 1 => by
    rw [carryInputFalse_consPair, carryWeight_consPair_alt (by decide)]
    linarith [carryWeight_carryInputFalse_pos m]

private theorem carryWeight_carryInputTrue_pos :
    ∀ m, 0 < carryWeight (m + 1) (carryInputTrue (m + 1))
  | 0 => by
    rw [carryInputTrue_one, carryWeight_one_consPair]
    norm_num
  | m + 1 => by
    rw [carryInputTrue_consPair, carryWeight_consPair_alt (by decide)]
    linarith [carryWeight_carryInputTrue_pos m]

/-- Evolution of `commonKnowledge` under `carryWeight (m + 2)` on an alternating-head input `x`:
for every `r`, `S^{r+1}(x) = liftAlt (S^r(tailPair x))`. -/
private theorem commonKnowledge_carryWeight_succ_eq_liftAlt {m : ℕ}
    {x : Fin (2 * (m + 2)) → Bool} (hx01 : x ⟨0, by omega⟩ ≠ x ⟨1, by omega⟩)
    (hxpos : 0 < carryWeight (m + 2) x) :
    ∀ r, commonKnowledge (carryChain (m + 2)) (carryWeight (m + 2)) x (r + 1) =
      liftAlt (commonKnowledge (carryChain (m + 1)) (carryWeight (m + 1)) (tailPair x) r)
  | 0 => (carryWeight_round1_alt hx01 hxpos).2
  | r + 1 => by
    have ih := commonKnowledge_carryWeight_succ_eq_liftAlt hx01 hxpos r
    set T := commonKnowledge (carryChain (m + 1)) (carryWeight (m + 1)) (tailPair x) r
    have hlift := (liftAlt_condExpect_and_roundPrice (T := T)).2
    ext y
    rw [mem_commonKnowledge_succ, ih, mem_liftAlt, mem_liftAlt, mem_commonKnowledge_succ]
    constructor
    · rintro ⟨⟨hy01, hyT⟩, hpy⟩
      rw [hlift y, hlift x] at hpy
      have hden : (2 * ((m : ℝ) + 2)) ≠ 0 := by positivity
      have hmul : (2 * ((m : ℝ) + 1)) ≠ 0 := by positivity
      have htail_eq :
          roundPrice (carryChain (m + 1)) (carryWeight (m + 1)) T (tailPair y) =
            roundPrice (carryChain (m + 1)) (carryWeight (m + 1)) T (tailPair x) := by
        have h1 : 2 * condExpect (carryChain (m + 1)) (carryWeight (m + 1)) T +
            (2 * ((m : ℝ) + 1)) *
              roundPrice (carryChain (m + 1)) (carryWeight (m + 1)) T (tailPair y) =
            2 * condExpect (carryChain (m + 1)) (carryWeight (m + 1)) T +
            (2 * ((m : ℝ) + 1)) *
              roundPrice (carryChain (m + 1)) (carryWeight (m + 1)) T (tailPair x) :=
          (div_left_inj₀ hden).mp hpy
        exact mul_left_cancel₀ hmul (by linarith)
      exact ⟨hy01, hyT, htail_eq⟩
    · rintro ⟨hy01, hyT, htail_eq⟩
      refine ⟨⟨hy01, hyT⟩, ?_⟩
      rw [hlift y, hlift x, htail_eq]

/-- Base case `m = 0` (`n = 1`, `2` inputs) of the `carryWeight` round-by-round analysis. -/
private theorem carryWeight_one_round0 :
    condExpect (carryChain 1) (carryWeight 1) (priorSupport (carryWeight 1)) = 1 / 2 ∧
    ∀ y : Fin (2 * 1) → Bool,
      roundPrice (carryChain 1) (carryWeight 1) (priorSupport (carryWeight 1)) y =
        match y ⟨0, by omega⟩, y ⟨1, by omega⟩ with
        | true, true => 2 / 3
        | true, false => 1 / 3
        | false, true => 1 / 3
        | false, false => 0 := by
  have hce : condExpect (carryChain 1) (carryWeight 1) (priorSupport (carryWeight 1)) = 1 / 2 := by
    have hnum : (∑ z ∈ priorSupport (carryWeight 1),
        if carryChain 1 z then carryWeight 1 z else 0) = 2 := by
      have := sum_priorSupport_carryWeight_filter_f (n := 1) (fun _ => True)
      simp only [filter_true, true_and] at this
      rw [this, sum_fin_two_bool]
      norm_num [carryChain_consPair, carryWeight_one_consPair]
    have hden : ∑ z ∈ priorSupport (carryWeight 1), carryWeight 1 z = 4 := by
      have := sum_priorSupport_carryWeight_filter (n := 1) (fun _ => True)
      simp only [filter_true, ↓reduceIte] at this
      rw [this, sum_fin_two_bool]
      norm_num [carryWeight_one_consPair]
    rw [condExpect_apply, hnum, hden]; norm_num
  refine ⟨hce, fun y => ?_⟩
  have hbid (i : Fin (2 * 1)) (b : Bool) (hbi : y i = b) :
      agentBid (carryChain 1) (carryWeight 1) (priorSupport (carryWeight 1)) i y =
        if b then 2 / 3 else 0 := by
    rw [agentBid_apply, condExpect_apply, agentKnowledge,
      sum_priorSupport_carryWeight_filter_f, sum_priorSupport_carryWeight_filter,
      sum_fin_two_bool, sum_fin_two_bool]
    rcases fin_lt_two_cases (by omega) i (by omega) with h0 | h1
    · rw [h0] at hbi ⊢
      rw [hbi]
      cases b <;>
        (simp only [carryChain_consPair, carryWeight_one_consPair, consPair]
         norm_num)
    · rw [h1] at hbi ⊢
      rw [hbi]
      cases b <;>
        (simp only [carryChain_consPair, carryWeight_one_consPair, consPair]
         norm_num)
  rw [roundPrice_apply, Fin.sum_univ_two]
  change (agentBid (carryChain 1) (carryWeight 1) (priorSupport (carryWeight 1))
      ⟨0, by omega⟩ y +
    agentBid (carryChain 1) (carryWeight 1) (priorSupport (carryWeight 1))
      ⟨1, by omega⟩ y) / 2 = _
  cases hy0 : y ⟨0, by omega⟩ <;> cases hy1 : y ⟨1, by omega⟩ <;>
    rw [hbid ⟨0, by omega⟩ _ hy0, hbid ⟨1, by omega⟩ _ hy1] <;> norm_num

/-- Inductive core of Theorem 26.15 on `carryWeight (m + 1)`: gives the exact closed-form clearing
price in every round `r < m + 1` (`1 / 2` for `r + 1 < m + 1`, and `(3(m+1) ∓ 1)/(6(m+1))` at the
final non-revealing round `r = m`) together with exact revelation at round `m + 1`. -/
private theorem carryWeight_rounds_core :
    ∀ m : ℕ,
      (∀ r < m + 1,
        commonKnowledge (carryChain (m + 1)) (carryWeight (m + 1)) (carryInputFalse (m + 1)) r =
          commonKnowledge (carryChain (m + 1)) (carryWeight (m + 1)) (carryInputTrue (m + 1)) r ∧
        condExpect (carryChain (m + 1)) (carryWeight (m + 1))
          (commonKnowledge (carryChain (m + 1)) (carryWeight (m + 1))
            (carryInputFalse (m + 1)) r) = 1 / 2 ∧
        roundPrice (carryChain (m + 1)) (carryWeight (m + 1))
          (commonKnowledge (carryChain (m + 1)) (carryWeight (m + 1))
            (carryInputFalse (m + 1)) r) (carryInputFalse (m + 1)) =
          (if r + 1 < m + 1 then 1 / 2
            else (3 * ((m + 1 : ℕ) : ℝ) - 1) / (6 * ((m + 1 : ℕ) : ℝ))) ∧
        roundPrice (carryChain (m + 1)) (carryWeight (m + 1))
          (commonKnowledge (carryChain (m + 1)) (carryWeight (m + 1))
            (carryInputTrue (m + 1)) r) (carryInputTrue (m + 1)) =
          (if r + 1 < m + 1 then 1 / 2
            else (3 * ((m + 1 : ℕ) : ℝ) + 1) / (6 * ((m + 1 : ℕ) : ℝ)))) ∧
      (∀ y ∈ commonKnowledge (carryChain (m + 1)) (carryWeight (m + 1))
          (carryInputFalse (m + 1)) (m + 1), carryChain (m + 1) y = false) ∧
      (∀ y ∈ commonKnowledge (carryChain (m + 1)) (carryWeight (m + 1))
          (carryInputTrue (m + 1)) (m + 1), carryChain (m + 1) y = true) := by
  intro m
  induction m with
  | zero =>
    obtain ⟨hce0, hp_eval⟩ := carryWeight_one_round0
    have h0_const (x y : Fin (2 * 1) → Bool)
        (hy : y ∈ commonKnowledge (carryChain 1) (carryWeight 1) x 1) :
        carryChain 1 y = carryChain 1 x := by
      obtain ⟨_, hpy⟩ := mem_commonKnowledge_succ.mp hy
      rw [commonKnowledge_zero, hp_eval, hp_eval] at hpy
      cases hy0 : y ⟨0, by omega⟩ <;> cases hy1 : y ⟨1, by omega⟩ <;>
        cases hx0 : x ⟨0, by omega⟩ <;> cases hx1 : x ⟨1, by omega⟩ <;>
        (rw [hy0, hy1, hx0, hx1] at hpy; norm_num at hpy) <;>
        (unfold carryChain; rw [hy0, hy1, hx0, hx1]; rfl)
    refine ⟨fun r hr => ?_,
      fun y hy => (h0_const _ _ hy).trans (carryChain_carryInputFalse 1),
      fun y hy => (h0_const _ _ hy).trans (carryChain_carryInputTrue 0)⟩
    have hr0 : r = 0 := by omega
    subst hr0
    refine ⟨rfl, hce0, ?_, ?_⟩
    · rw [commonKnowledge_zero, hp_eval, carryInputFalse_consPair, consPair_zero, consPair_one]
      norm_num
    · rw [commonKnowledge_zero, hp_eval, carryInputTrue_one, consPair_zero, consPair_one]
      norm_num
  | succ m ih =>
    obtain ⟨ih_lt, ih_f, ih_t⟩ := ih
    have hf01 : carryInputFalse (m + 2) ⟨0, by omega⟩ ≠ carryInputFalse (m + 2) ⟨1, by omega⟩ := by
      rw [carryInputFalse_consPair, consPair_zero, consPair_one]; decide
    have ht01 : carryInputTrue (m + 2) ⟨0, by omega⟩ ≠ carryInputTrue (m + 2) ⟨1, by omega⟩ := by
      rw [carryInputTrue_consPair, consPair_zero, consPair_one]; decide
    have hfpos := carryWeight_carryInputFalse_pos (m + 1)
    have htpos := carryWeight_carryInputTrue_pos (m + 1)
    have hftail : tailPair (carryInputFalse (m + 2)) = carryInputFalse (m + 1) := by
      rw [carryInputFalse_consPair, tailPair_consPair]
    have httail : tailPair (carryInputTrue (m + 2)) = carryInputTrue (m + 1) := by
      rw [carryInputTrue_consPair, tailPair_consPair]
    have hS_f (r : ℕ) :
        commonKnowledge (carryChain (m + 2)) (carryWeight (m + 2))
            (carryInputFalse (m + 2)) (r + 1) =
          liftAlt (commonKnowledge (carryChain (m + 1)) (carryWeight (m + 1))
            (carryInputFalse (m + 1)) r) := by
      simpa only [hftail] using commonKnowledge_carryWeight_succ_eq_liftAlt hf01 hfpos r
    have hS_t (r : ℕ) :
        commonKnowledge (carryChain (m + 2)) (carryWeight (m + 2))
            (carryInputTrue (m + 2)) (r + 1) =
          liftAlt (commonKnowledge (carryChain (m + 1)) (carryWeight (m + 1))
            (carryInputTrue (m + 1)) r) := by
      simpa only [httail] using commonKnowledge_carryWeight_succ_eq_liftAlt ht01 htpos r
    have hlift_val {T : Finset (Fin (2 * (m + 1)) → Bool)} {c : Bool}
        (hT : ∀ z ∈ T, carryChain (m + 1) z = c) :
        ∀ y ∈ liftAlt T, carryChain (m + 2) y = c := fun y hy => by
      rw [mem_liftAlt] at hy
      rw [← consPair_tailPair y, carryChain_consPair]
      have h1 := hT (tailPair y) hy.2
      cases hy0 : y ⟨0, by omega⟩ <;> cases hy1 : y ⟨1, by omega⟩
      · exact absurd (hy0.trans hy1.symm) hy.1
      · simp [h1]
      · simp [h1]
      · exact absurd (hy0.trans hy1.symm) hy.1
    refine ⟨fun r hr => ?_, by rw [hS_f (m + 1)]; exact hlift_val ih_f,
      by rw [hS_t (m + 1)]; exact hlift_val ih_t⟩
    · cases r with
      | zero =>
        obtain ⟨hT, hF, _, _⟩ := carryWeight_invariants (m + 1)
        have hce0 : condExpect (carryChain (m + 2)) (carryWeight (m + 2))
            (priorSupport (carryWeight (m + 2))) = 1 / 2 := by
          rw [condExpect_apply]
          have hnum : (∑ z ∈ priorSupport (carryWeight (m + 2)),
              if carryChain (m + 2) z then carryWeight (m + 2) z else 0) =
              ((m + 1 : ℕ) : ℝ) + 2 := by
            have := sum_priorSupport_carryWeight_filter_f (n := m + 2) (fun _ => True)
            simp only [filter_true, true_and] at this
            rw [this, hT]
          have hden : ∑ z ∈ priorSupport (carryWeight (m + 2)), carryWeight (m + 2) z =
              2 * (((m + 1 : ℕ) : ℝ) + 2) := by
            have := sum_priorSupport_carryWeight_filter (n := m + 2) (fun _ => True)
            simp only [filter_true, ↓reduceIte] at this
            rw [this, sum_carryWeight_total (m + 1)]
            push_cast; ring
          rw [hnum, hden]
          have hne : (((m + 1 : ℕ) : ℝ) + 2) ≠ 0 := by positivity
          field_simp [hne]
        have hpf := (carryWeight_round1_alt hf01 hfpos).1
        have hpt := (carryWeight_round1_alt ht01 htpos).1
        have hlt1 : 0 + 1 < m + 2 := by omega
        refine ⟨rfl, hce0, ?_, ?_⟩
        · rw [commonKnowledge_zero, hpf]; simp only [hlt1, ↓reduceIte]
        · rw [commonKnowledge_zero, hpt]; simp only [hlt1, ↓reduceIte]
      | succ r =>
        obtain ⟨hSeq, hce_r, hpf_r, hpt_r⟩ := ih_lt r (by omega)
        obtain ⟨hlift_ce, hlift_pf⟩ := liftAlt_condExpect_and_roundPrice
          (T := commonKnowledge (carryChain (m + 1)) (carryWeight (m + 1))
            (carryInputFalse (m + 1)) r)
        obtain ⟨_, hlift_pt⟩ := liftAlt_condExpect_and_roundPrice
          (T := commonKnowledge (carryChain (m + 1)) (carryWeight (m + 1))
            (carryInputTrue (m + 1)) r)
        have hce_t : condExpect (carryChain (m + 1)) (carryWeight (m + 1))
            (commonKnowledge (carryChain (m + 1)) (carryWeight (m + 1))
              (carryInputTrue (m + 1)) r) = 1 / 2 := by
          rw [← hSeq]; exact hce_r
        have hne1 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        have hne2 : ((m + 2 : ℕ) : ℝ) ≠ 0 := by positivity
        have hstep_price (s : ℝ) :
            (2 * (1 / 2) + 2 * ((m : ℝ) + 1) *
              (if r + 1 < m + 1 then (1 : ℝ) / 2
                else (3 * ((m + 1 : ℕ) : ℝ) + s) / (6 * ((m + 1 : ℕ) : ℝ)))) /
              (2 * ((m : ℝ) + 2)) =
            if r + 1 + 1 < m + 2 then 1 / 2
            else (3 * ((m + 2 : ℕ) : ℝ) + s) / (6 * ((m + 2 : ℕ) : ℝ)) := by
          by_cases hlt' : r + 1 < m + 1
          · have hlt'' : r + 1 + 1 < m + 2 := by omega
            simp only [hlt', hlt'', ↓reduceIte]
            have hd : (2 * ((m : ℝ) + 2)) ≠ 0 := by positivity
            field_simp [hd]; ring
          · have hlt'' : ¬ r + 1 + 1 < m + 2 := by omega
            simp only [hlt', hlt'', ↓reduceIte]
            push_cast at hne1 hne2 ⊢
            field_simp [hne1, hne2]; ring
        refine ⟨by rw [hS_f r, hS_t r, hSeq], by rw [hS_f r, hlift_ce, hce_r], ?_, ?_⟩
        · rw [hS_f r, hlift_pf _, hce_r, hftail, hpf_r]
          simpa only [sub_eq_add_neg] using hstep_price (-1)
        · rw [hS_t r, hlift_pt _, hce_t, httail, hpt_r]
          exact hstep_price 1

/-- Explicit round-by-round convergence profile for `(carryChain n, carryPrior n)` (`0 < n`):
for every `r < n`, the common-knowledge sets at `carryInputFalse n` (`Cₙ = false`) and
`carryInputTrue n` (`Cₙ = true`) coincide with conditional expectation `1 / 2` and exact clearing
prices `1 / 2` (for `r + 1 < n`) or `(3n ∓ 1) / (6n)` (at `r = n - 1`), all strictly in `(0, 1)`;
after `n` rounds, common knowledge reveals `Cₙ` and the clearing price equals `Cₙ(x)`. -/
theorem carryChain_convergence_rounds {n : ℕ} (hn : 0 < n) :
    0 < carryPrior n (carryInputFalse n) ∧
    0 < carryPrior n (carryInputTrue n) ∧
    carryChain n (carryInputFalse n) = false ∧
    carryChain n (carryInputTrue n) = true ∧
    (∀ r < n,
      commonKnowledge (carryChain n) (carryPrior n) (carryInputFalse n) r =
        commonKnowledge (carryChain n) (carryPrior n) (carryInputTrue n) r ∧
      condExpect (carryChain n) (carryPrior n)
        (commonKnowledge (carryChain n) (carryPrior n) (carryInputFalse n) r) = 1 / 2 ∧
      roundPrice (carryChain n) (carryPrior n)
        (commonKnowledge (carryChain n) (carryPrior n) (carryInputFalse n) r)
        (carryInputFalse n) =
        (if r + 1 < n then 1 / 2 else (3 * (n : ℝ) - 1) / (6 * (n : ℝ))) ∧
      roundPrice (carryChain n) (carryPrior n)
        (commonKnowledge (carryChain n) (carryPrior n) (carryInputTrue n) r)
        (carryInputTrue n) =
        (if r + 1 < n then 1 / 2 else (3 * (n : ℝ) + 1) / (6 * (n : ℝ)))) ∧
    ((∀ y ∈ commonKnowledge (carryChain n) (carryPrior n) (carryInputFalse n) n,
        carryChain n y = false) ∧
      roundPrice (carryChain n) (carryPrior n)
        (commonKnowledge (carryChain n) (carryPrior n) (carryInputFalse n) n)
        (carryInputFalse n) = 0) ∧
    ((∀ y ∈ commonKnowledge (carryChain n) (carryPrior n) (carryInputTrue n) n,
        carryChain n y = true) ∧
      roundPrice (carryChain n) (carryPrior n)
        (commonKnowledge (carryChain n) (carryPrior n) (carryInputTrue n) n)
        (carryInputTrue n) = 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hc_pos : (0 : ℝ) < (2 * ((m + 1 : ℕ) : ℝ) + 2)⁻¹ := by positivity
  have hP_eq : carryPrior (m + 1) =
      fun z => (2 * ((m + 1 : ℕ) : ℝ) + 2)⁻¹ * carryWeight (m + 1) z := by
    funext z
    simp [carryPrior, div_eq_inv_mul]
  obtain ⟨hlt, hf_done, ht_done⟩ := carryWeight_rounds_core m
  have hfpos : 0 < carryPrior (m + 1) (carryInputFalse (m + 1)) := by
    rw [hP_eq]; exact mul_pos hc_pos (carryWeight_carryInputFalse_pos m)
  have htpos : 0 < carryPrior (m + 1) (carryInputTrue (m + 1)) := by
    rw [hP_eq]; exact mul_pos hc_pos (carryWeight_carryInputTrue_pos m)
  have hck_eq (x : Fin (2 * (m + 1)) → Bool) (r : ℕ) :
      commonKnowledge (carryChain (m + 1)) (carryPrior (m + 1)) x r =
        commonKnowledge (carryChain (m + 1)) (carryWeight (m + 1)) x r := by
    rw [hP_eq]; exact commonKnowledge_const_mul hc_pos x r
  have hce_eq (A : Finset (Fin (2 * (m + 1)) → Bool)) :
      condExpect (carryChain (m + 1)) (carryPrior (m + 1)) A =
        condExpect (carryChain (m + 1)) (carryWeight (m + 1)) A := by
    rw [hP_eq]; exact condExpect_const_mul hc_pos.ne'
  have hrp_eq (A : Finset (Fin (2 * (m + 1)) → Bool)) (x : Fin (2 * (m + 1)) → Bool) :
      roundPrice (carryChain (m + 1)) (carryPrior (m + 1)) A x =
        roundPrice (carryChain (m + 1)) (carryWeight (m + 1)) A x := by
    rw [hP_eq]; exact roundPrice_const_mul hc_pos.ne' x
  have hdone_of (x : Fin (2 * (m + 1)) → Bool) (c : Bool)
      (hxpos : 0 < carryPrior (m + 1) x)
      (hw_done : ∀ y ∈ commonKnowledge (carryChain (m + 1)) (carryWeight (m + 1)) x (m + 1),
        carryChain (m + 1) y = c) :
      (∀ y ∈ commonKnowledge (carryChain (m + 1)) (carryPrior (m + 1)) x (m + 1),
        carryChain (m + 1) y = c) ∧
      roundPrice (carryChain (m + 1)) (carryPrior (m + 1))
        (commonKnowledge (carryChain (m + 1)) (carryPrior (m + 1)) x (m + 1)) x =
        if c then 1 else 0 := by
    have hconst : ∀ y ∈ commonKnowledge (carryChain (m + 1)) (carryPrior (m + 1)) x (m + 1),
        carryChain (m + 1) y = c := fun y hy => hw_done y (by rwa [← hck_eq])
    refine ⟨hconst, ?_⟩
    have hsub := commonKnowledge_subset_priorSupport (carryChain (m + 1)) (carryPrior (m + 1))
      x (m + 1)
    have hmem := mem_commonKnowledge_self (f := carryChain (m + 1)) hxpos (m + 1)
    have hbid (i : Fin (2 * (m + 1))) :
        agentBid (carryChain (m + 1)) (carryPrior (m + 1))
          (commonKnowledge (carryChain (m + 1)) (carryPrior (m + 1)) x (m + 1)) i x =
          if c then 1 else 0 := by
      rw [agentBid_apply]
      exact condExpect_eq_const
        (A := agentKnowledge
          (commonKnowledge (carryChain (m + 1)) (carryPrior (m + 1)) x (m + 1)) i x)
        ((filter_subset _ _).trans hsub)
        ⟨x, mem_agentKnowledge.mpr ⟨hmem, rfl⟩⟩
        fun z hz => hconst z (mem_agentKnowledge.mp hz).1
    rw [roundPrice_apply, sum_congr rfl fun i _ => hbid i, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have hne : ((2 * (m + 1) : ℕ) : ℝ) ≠ 0 := by positivity
    exact mul_div_cancel_left₀ _ hne
  refine ⟨hfpos, htpos, carryChain_carryInputFalse (m + 1), carryChain_carryInputTrue m, ?_,
    by simpa only [Bool.false_eq_true, ↓reduceIte] using
      hdone_of (carryInputFalse (m + 1)) false hfpos hf_done,
    by simpa only [↓reduceIte] using
      hdone_of (carryInputTrue (m + 1)) true htpos ht_done⟩
  · intro r hr
    obtain ⟨hSeq, hce, hpf, hpt⟩ := hlt r hr
    refine ⟨by rw [hck_eq, hck_eq, hSeq], by rw [hck_eq, hce_eq, hce],
      by rw [hck_eq, hrp_eq, hpf], by rw [hck_eq, hrp_eq, hpt]⟩

/-- **Theorem 26.15** ([PennockSami2007, p. 669]): for every `n > 0`, there exist a weighted
threshold function `Cₙ : (Fin (2 * n) → Bool) → Bool`, a prior distribution `Pₙ`
(`IsMixedStrategy Pₙ`), and positive-probability states `x₀, x₁` with `Cₙ x₀ = false` and
`Cₙ x₁ = true` such that for every round `r < n`, the common-knowledge sets `Sʳ(x₀) = Sʳ(x₁)` do
not distinguish `Cₙ x₀` from `Cₙ x₁` (with conditional expectation `1 / 2` and clearing prices
strictly between `0` and `1`), while after `n` rounds common knowledge reveals `Cₙ` and the
clearing price reaches `Cₙ(x)`. -/
theorem exists_n_round_lower_bound {n : ℕ} (hn : 0 < n) :
    ∃ (f : (Fin (2 * n) → Bool) → Bool) (P : (Fin (2 * n) → Bool) → ℝ)
      (x₀ x₁ : Fin (2 * n) → Bool),
      IsWeightedThreshold f ∧ IsMixedStrategy P ∧
      0 < P x₀ ∧ 0 < P x₁ ∧ f x₀ = false ∧ f x₁ = true ∧
      (∀ r < n,
        commonKnowledge f P x₀ r = commonKnowledge f P x₁ r ∧
        condExpect f P (commonKnowledge f P x₀ r) = 1 / 2 ∧
        roundPrice f P (commonKnowledge f P x₀ r) x₀ ≠ 0 ∧
        roundPrice f P (commonKnowledge f P x₁ r) x₁ ≠ 1) ∧
      ((∀ y ∈ commonKnowledge f P x₀ n, f y = false) ∧
        roundPrice f P (commonKnowledge f P x₀ n) x₀ = 0) ∧
      ((∀ y ∈ commonKnowledge f P x₁ n, f y = true) ∧
        roundPrice f P (commonKnowledge f P x₁ n) x₁ = 1) := by
  obtain ⟨hfpos, htpos, hff, hft, hlt, hf_done, ht_done⟩ := carryChain_convergence_rounds hn
  refine ⟨carryChain n, carryPrior n, carryInputFalse n, carryInputTrue n,
    isWeightedThreshold_carryChain n, isMixedStrategy_carryPrior n,
    hfpos, htpos, hff, hft, fun r hr => ?_, hf_done, ht_done⟩
  obtain ⟨hSeq, hce, hpf, hpt⟩ := hlt r hr
  have hn' : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  refine ⟨hSeq, hce, ?_, ?_⟩
  · rw [hpf]
    split_ifs
    · norm_num
    · exact (div_pos (by linarith) (by linarith)).ne'
  · rw [hpt]
    split_ifs
    · norm_num
    · exact (div_lt_one (by linarith)).mpr (by linarith) |>.ne

end Theorem26_15

end Cslib.GameTheory.PredictionMarket
