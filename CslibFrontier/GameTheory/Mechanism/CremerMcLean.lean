/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.Indirect
public import CslibFrontier.GameTheory.MixedStrategy
public import Mathlib.Analysis.Convex.Independent
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Farkas
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Crémer–McLean full surplus extraction under correlated types

Under independent private values, incentive compatibility forces a seller or social planner to
leave positive information rent to privately informed agents. Jacques Crémer and Richard P. McLean
[CremerMcLean1988] showed that stochastic correlation among finite agent types reverses this
conclusion: because an agent's true type shifts its conditional belief over the other agents'
types, opponent-contingent side transfers (`gᵢ(t₋ᵢ)`) or report-contingent lotteries (`hᵢ(rᵢ, t₋ᵢ)`)
allow the designer to extract the entire first-best social surplus while preserving incentive
compatibility and interim individual rationality.

For a finite set of agents `ι`, finite type spaces `T : ι → Type*`, an outcome space `Ω`,
quasilinear valuations `val : ∀ i, T i → Ω → ℝ`, and a common prior `P : CorrelatedPrior ι T` with
strictly positive marginals (`P.marginal_pos`), each agent `i` has conditional belief matrix
`P.condBelief i : Matrix (T i) (OppProfile T i) ℝ`. Direct-revelation mechanisms on `∀ i, T i` are
represented by `IndirectMechanism ι T Ω` (`CslibFrontier.GameTheory.Mechanism.Indirect`), bridged
to valuation-profile mechanisms `Mechanism ι Ω` (`CslibFrontier.GameTheory.Mechanism.VCG`) via
`Mechanism.toDirectMechanism`.

We establish both full-surplus-extraction characterizations of [CremerMcLean1988] together with
their converses and the independent-prior impossibility corollary (internal page, equation, and
theorem locators of the paywalled 1988 *Econometrica* article were not directly inspected and are
not claimed):

* **Dominant-strategy (`IndirectMechanism.IsTruthful`) full surplus extraction**: adding any
  opponent-only side transfer `g : ∀ i, OppProfile T i → ℝ`
  (`IndirectMechanism.withOpponentTransfer`) leaves `IndirectMechanism.IsTruthful` invariant while
  subtracting `(P.condBelief i *ᵥ g i) ti` from truthful interim utility. Linear independence of
  every agent's conditional belief rows (`P.HasFullBeliefRank`) is equivalent to solvability of all
  interim side-bet targets (`CorrelatedPrior.hasFullBeliefRank_iff_forall_exists_mulVec_eq`), and
  for `[Finite Ω] [Nontrivial Ω]` is both necessary and sufficient for universal ex-post efficient,
  dominant-strategy truthful, interim-IR full surplus extraction
  (`CorrelatedPrior.hasFullBeliefRank_iff_forall_exists_isTruthful`).
* **Bayesian (`IsBIC`) full surplus extraction**: convex independence of every agent's conditional
  belief rows (`P.HasConvexIndependentBeliefs`, via Mathlib's `ConvexIndependent`) is characterized
  through `CslibFrontier.Foundations.LinearAlgebra.Matrix.Farkas` by separating lotteries that have
  zero conditional expectation at the truthful type and strictly positive conditional expectation
  at every other type (`CorrelatedPrior.condBelief_notMem_convexHull_iff_exists_separating_lottery`,
  `CorrelatedPrior.HasConvexIndependentBeliefs.exists_separating_lottery`). Scaling these lotteries
  yields strict BIC, interim-IR full surplus extraction for any outcome rule, and for
  `[Finite Ω] [Nontrivial Ω]` convex independence is both necessary and sufficient for universal
  ex-post efficient, BIC, interim-IR full surplus extraction
  (`CorrelatedPrior.hasConvexIndependentBeliefs_iff_forall_exists_isBIC`).
* **Information-rent lower bound and independent-prior impossibility**: whenever a type's
  conditional belief lies in the convex hull of the other types' conditional beliefs, every BIC
  mechanism satisfies an explicit weighted interim-utility lower bound
  (`CorrelatedPrior.le_interimUtility_add_sum_of_convexComb`). For any product prior
  `CorrelatedPrior.product` with at least one nontrivial type space, conditional belief rows are
  identical across own types, refuting convex independence and ruling out universal BIC full
  surplus extraction (`CorrelatedPrior.not_hasConvexIndependentBeliefs_product`,
  `CorrelatedPrior.exists_nonneg_val_not_exists_isBIC_product`).

## Main definitions

* `OppProfile`, `oppProj`, `extendProfile`, `profileEquiv`: opponent type profiles `t₋ᵢ` and
  recombination `(tᵢ, t₋ᵢ) ≃ ∀ j, T j`.
* `Mechanism.toDirectMechanism`, `IndirectMechanism.withOpponentTransfer`: pullback of a
  valuation-domain `Mechanism ι Ω` to `IndirectMechanism ι T Ω` and opponent-only payment shifts.
* `IndirectMechanism.IsExPostEfficient`: ex-post welfare maximization on `∀ i, T i`.
* `CorrelatedPrior`, `CorrelatedPrior.marginal`, `CorrelatedPrior.condBelief`,
  `CorrelatedPrior.product`: correlated common priors with positive marginals, conditional belief
  matrices, and independent product priors.
* `CorrelatedPrior.interimUtility`, `CorrelatedPrior.IsBIC`, `CorrelatedPrior.IsInterimIR`,
  `CorrelatedPrior.ExtractsFullSurplus`: interim expected utility, Bayesian incentive
  compatibility, interim individual rationality, and ex-ante full surplus extraction.
* `CorrelatedPrior.HasFullBeliefRank`, `CorrelatedPrior.HasConvexIndependentBeliefs`: linear
  independence and convex independence of conditional belief rows.

## Main results

* `IndirectMechanism.isTruthful_iff`,
  `IndirectMechanism.isTruthful_withOpponentTransfer`: single-misreport characterization of
  `IndirectMechanism.IsTruthful` ([Nisan2007]) and invariance under opponent-only transfers.
* `CorrelatedPrior.sum_marginal_mul_interimUtility`,
  `CorrelatedPrior.extractsFullSurplus_iff_forall_interimUtility_eq_zero`: law-of-total-probability
  surplus accounting and equivalence between full surplus extraction and zero interim rents under
  `IsInterimIR`.
* `CorrelatedPrior.hasFullBeliefRank_iff_forall_exists_mulVec_eq`: row linear independence of
  `condBelief` is equivalent to solvability of all interim side-bet targets.
* `CorrelatedPrior.HasFullBeliefRank.exists_isTruthful_interimIR_extractsFullSurplus`,
  `CorrelatedPrior.exists_nonneg_val_not_exists_isTruthful_of_not_hasFullBeliefRank`,
  `CorrelatedPrior.hasFullBeliefRank_iff_forall_exists_isTruthful`: dominant-strategy full surplus
  extraction characterization ([CremerMcLean1988]).
* `CorrelatedPrior.condBelief_notMem_convexHull_iff_exists_separating_lottery`,
  `CorrelatedPrior.HasConvexIndependentBeliefs.exists_separating_lottery`,
  `CorrelatedPrior.HasFullBeliefRank.hasConvexIndependentBeliefs`: Farkas separating-lottery
  characterization of convex-independent beliefs.
* `CorrelatedPrior.HasConvexIndependentBeliefs.exists_outcome_eq_isBIC_extractsFullSurplus`,
  `CorrelatedPrior.HasConvexIndependentBeliefs.exists_isBIC_interimIR_extractsFullSurplus`,
  `CorrelatedPrior.le_interimUtility_add_sum_of_convexComb`,
  `CorrelatedPrior.exists_nonneg_val_not_exists_isBIC_of_not_hasConvexIndependentBeliefs`,
  `CorrelatedPrior.hasConvexIndependentBeliefs_iff_forall_exists_isBIC`: Bayesian full surplus
  extraction characterization and information-rent bound ([CremerMcLean1988]).
* `CorrelatedPrior.not_hasConvexIndependentBeliefs_product`,
  `CorrelatedPrior.exists_nonneg_val_not_exists_isBIC_product`: impossibility of universal full
  surplus extraction under independent priors.

## References

* [J. Crémer and R. P. McLean, *Full extraction of the surplus in Bayesian and dominant strategy
  auctions*][CremerMcLean1988]
* [E. H. Clarke, *Multipart pricing of public goods*][Clarke1971]
* [T. Groves, *Incentives in teams*][Groves1973]
* [N. Nisan, *Introduction to mechanism design (for computer scientists)*][Nisan2007]
* [W. Vickrey, *Counterspeculation, auctions, and competitive sealed tenders*][Vickrey1961]
-/

public section

open Finset Matrix

namespace Cslib.GameTheory

/-! ### Opponent type profiles and profile decomposition -/

/-- The type of opponent profiles `t₋ᵢ` excluding agent `i`. -/
abbrev OppProfile {ι : Type*} (T : ι → Type*) (i : ι) : Type _ :=
  ∀ j : {j : ι // j ≠ i}, T j

/-- Project a full type profile `t` onto the opponents `j ≠ i` of agent `i`. -/
def oppProj {ι : Type*} {T : ι → Type*} (i : ι) (t : ∀ j, T j) : OppProfile T i :=
  fun j => t j.1

@[simp]
theorem oppProj_apply {ι : Type*} {T : ι → Type*} (i : ι) (t : ∀ j, T j)
    (j : {j : ι // j ≠ i}) : oppProj i t j = t j.1 := by
  rfl

/-- Updating agent `i`'s own coordinate leaves `oppProj i` unchanged. -/
@[simp]
theorem oppProj_update {ι : Type*} {T : ι → Type*} [DecidableEq ι] (i : ι) (t : ∀ j, T j)
    (ti' : T i) : oppProj i (Function.update t i ti') = oppProj i t := by
  funext j
  simp only [oppProj_apply, Function.update_of_ne j.2]

/-- Combine agent `i`'s type `ti` with an opponent profile `t_opp : OppProfile T i` into a full
type profile `∀ j, T j`. -/
def extendProfile {ι : Type*} {T : ι → Type*} [DecidableEq ι] (i : ι) (ti : T i)
    (t_opp : OppProfile T i) : ∀ j, T j :=
  fun j => if h : j = i then h ▸ ti else t_opp ⟨j, h⟩

@[simp]
theorem extendProfile_self {ι : Type*} {T : ι → Type*} [DecidableEq ι] (i : ι) (ti : T i)
    (t_opp : OppProfile T i) : extendProfile i ti t_opp i = ti := by
  simp only [extendProfile, ↓reduceDIte]

@[simp]
theorem extendProfile_of_ne {ι : Type*} {T : ι → Type*} [DecidableEq ι] {i j : ι} (hj : j ≠ i)
    (ti : T i) (t_opp : OppProfile T i) : extendProfile i ti t_opp j = t_opp ⟨j, hj⟩ := by
  simp only [extendProfile, dite_eq_right hj]

@[simp]
theorem oppProj_extendProfile {ι : Type*} {T : ι → Type*} [DecidableEq ι] (i : ι) (ti : T i)
    (t_opp : OppProfile T i) : oppProj i (extendProfile i ti t_opp) = t_opp := by
  funext j
  exact extendProfile_of_ne j.2 ti t_opp

@[simp]
theorem extendProfile_oppProj {ι : Type*} {T : ι → Type*} [DecidableEq ι] (i : ι)
    (t : ∀ j, T j) : extendProfile i (t i) (oppProj i t) = t := by
  funext j
  rcases eq_or_ne j i with rfl | hj
  · exact extendProfile_self j (t j) (oppProj j t)
  · exact extendProfile_of_ne hj (t i) (oppProj i t)

@[simp]
theorem update_extendProfile {ι : Type*} {T : ι → Type*} [DecidableEq ι] (i : ι) (ti ti' : T i)
    (t_opp : OppProfile T i) :
    Function.update (extendProfile i ti t_opp) i ti' = extendProfile i ti' t_opp := by
  funext j
  rcases eq_or_ne j i with rfl | hj
  · simp only [Function.update_self, extendProfile_self]
  · simp only [Function.update_of_ne hj, extendProfile_of_ne hj]

theorem extendProfile_oppProj_eq_update {ι : Type*} {T : ι → Type*} [DecidableEq ι] (i : ι)
    (ti' : T i) (t : ∀ j, T j) :
    extendProfile i ti' (oppProj i t) = Function.update t i ti' := by
  conv_rhs => rw [← extendProfile_oppProj i t, update_extendProfile]

/-- Canonical bijection decomposing full profiles `∀ j, T j` into `(t i, oppProj i t)`. -/
def profileEquiv {ι : Type*} (T : ι → Type*) [DecidableEq ι] (i : ι) :
    (T i × OppProfile T i) ≃ ∀ j, T j where
  toFun p := extendProfile i p.1 p.2
  invFun t := (t i, oppProj i t)
  left_inv p := Prod.ext (extendProfile_self i p.1 p.2) (oppProj_extendProfile i p.1 p.2)
  right_inv t := extendProfile_oppProj i t

@[simp]
theorem profileEquiv_apply {ι : Type*} (T : ι → Type*) [DecidableEq ι] (i : ι)
    (p : T i × OppProfile T i) : profileEquiv T i p = extendProfile i p.1 p.2 := by
  rfl

@[simp]
theorem profileEquiv_symm_apply {ι : Type*} (T : ι → Type*) [DecidableEq ι] (i : ι)
    (t : ∀ j, T j) : (profileEquiv T i).symm t = (t i, oppProj i t) := by
  rfl

/-- Summing over all full profiles `t : ∀ j, T j` factors into summing over `ti : T i` and
`t_opp : OppProfile T i`. -/
theorem sum_profile_eq {ι : Type*} {T : ι → Type*} [Fintype ι] [DecidableEq ι]
    [∀ j, Fintype (T j)] (i : ι) (g : (∀ j, T j) → ℝ) :
    ∑ t : ∀ j, T j, g t = ∑ ti : T i, ∑ t_opp : OppProfile T i, g (extendProfile i ti t_opp) := by
  rw [← Fintype.sum_equiv (profileEquiv T i) (fun p => g (extendProfile i p.1 p.2)) g
    (fun _ => rfl), Fintype.sum_prod_type]

/-! ### Direct mechanisms, VCG pullback, and opponent-only transfers -/

namespace Mechanism

/-- Pull a valuation-domain direct mechanism `M : Mechanism ι Ω` back along agent valuations
`val : ∀ i, T i → Ω → ℝ` to a type-indexed direct mechanism `IndirectMechanism ι T Ω`. -/
def toDirectMechanism {ι Ω : Type*} {T : ι → Type*} (M : Mechanism ι Ω)
    (val : ∀ i, T i → Ω → ℝ) : IndirectMechanism ι T Ω where
  outcome t := M.outcome fun j => val j (t j)
  payment t := M.payment fun j => val j (t j)

@[simp]
theorem toDirectMechanism_outcome {ι Ω : Type*} {T : ι → Type*} (M : Mechanism ι Ω)
    (val : ∀ i, T i → Ω → ℝ) (t : ∀ i, T i) :
    (M.toDirectMechanism val).outcome t = M.outcome fun j => val j (t j) := by
  rfl

@[simp]
theorem toDirectMechanism_payment {ι Ω : Type*} {T : ι → Type*} (M : Mechanism ι Ω)
    (val : ∀ i, T i → Ω → ℝ) (t : ∀ i, T i) :
    (M.toDirectMechanism val).payment t = M.payment fun j => val j (t j) := by
  rfl

end Mechanism

namespace IndirectMechanism

variable {ι Ω : Type*} {T : ι → Type*}

/-- A direct mechanism `D : IndirectMechanism ι T Ω` is **ex-post efficient** for valuations `val`
if at every type profile `t`, `D.outcome t` maximizes total social welfare `∑ i, val i (t i) ω`. -/
@[expose] def IsExPostEfficient [Fintype ι] (D : IndirectMechanism ι T Ω)
    (val : ∀ i, T i → Ω → ℝ) : Prop :=
  ∀ (t : ∀ i, T i) (ω : Ω), ∑ i, val i (t i) ω ≤ ∑ i, val i (t i) (D.outcome t)

/-- Single-misreport characterization of `IndirectMechanism.IsTruthful` ([Nisan2007],
Definition 9.22): at every true type profile `t`, no agent `i` strictly gains by misreporting
`ti' : T i`. -/
theorem isTruthful_iff [DecidableEq ι] {D : IndirectMechanism ι T Ω}
    {val : ∀ i, T i → Ω → ℝ} :
    D.IsTruthful val ↔
      ∀ (t : ∀ i, T i) (i : ι) (ti' : T i),
        val i (t i) (D.outcome (Function.update t i ti')) -
            D.payment (Function.update t i ti') i ≤
          val i (t i) (D.outcome t) - D.payment t i := by
  constructor
  · intro h t i ti'
    have key := h i (t i) (Function.update t i ti')
    simpa only [toIncompleteInfoGame_utility, id_eq, Function.update_idem,
      Function.update_eq_self] using key
  · intro h i ti x
    have key := h (Function.update x i ti) i (x i)
    simpa only [toIncompleteInfoGame_utility, id_eq, Function.update_self, Function.update_idem,
      Function.update_eq_self] using key

/-- Shift each agent `i`'s payment by an opponent-contingent transfer `g i (oppProj i t)` that
depends only on the other agents' reported types ([CremerMcLean1988]). -/
def withOpponentTransfer (D : IndirectMechanism ι T Ω)
    (g : ∀ i, OppProfile T i → ℝ) : IndirectMechanism ι T Ω where
  outcome := D.outcome
  payment t i := D.payment t i + g i (oppProj i t)

@[simp]
theorem withOpponentTransfer_outcome (D : IndirectMechanism ι T Ω)
    (g : ∀ i, OppProfile T i → ℝ) :
    (D.withOpponentTransfer g).outcome = D.outcome := by
  rfl

@[simp]
theorem withOpponentTransfer_payment (D : IndirectMechanism ι T Ω)
    (g : ∀ i, OppProfile T i → ℝ) (t : ∀ i, T i) (i : ι) :
    (D.withOpponentTransfer g).payment t i = D.payment t i + g i (oppProj i t) := by
  rfl

@[simp]
theorem isExPostEfficient_withOpponentTransfer [Fintype ι]
    (D : IndirectMechanism ι T Ω) (g : ∀ i, OppProfile T i → ℝ) (val : ∀ i, T i → Ω → ℝ) :
    (D.withOpponentTransfer g).IsExPostEfficient val ↔ D.IsExPostEfficient val := by
  rfl

/-- Adding any opponent-only transfer `gᵢ(t₋ᵢ)` preserves `IsTruthful` identically, because
agent `i`'s report does not affect `oppProj i` ([CremerMcLean1988]). -/
@[simp]
theorem isTruthful_withOpponentTransfer [DecidableEq ι] (D : IndirectMechanism ι T Ω)
    (g : ∀ i, OppProfile T i → ℝ) (val : ∀ i, T i → Ω → ℝ) :
    (D.withOpponentTransfer g).IsTruthful val ↔ D.IsTruthful val := by
  rw [isTruthful_iff, isTruthful_iff]
  refine forall_congr' fun t => forall_congr' fun i => forall_congr' fun ti' => ?_
  simp only [withOpponentTransfer_outcome, withOpponentTransfer_payment, oppProj_update]
  constructor <;> intro h <;> linarith

private theorem exists_singleAgentVal [Fintype ι] [DecidableEq Ω] (i₀ : ι)
    {ω₀ ω₁ : Ω} (hω : ω₀ ≠ ω₁) (v₀ : T i₀ → ℝ) (hv₀ : ∀ ti, 1 ≤ v₀ ti) :
    ∃ val : ∀ i, T i → Ω → ℝ,
      (∀ i ti ω, 0 ≤ val i ti ω) ∧
      (∀ i ti, val i ti ω₀ = 0) ∧
      (∀ (ti : T i₀) (ω : Ω), val i₀ ti ω = if ω = ω₁ then v₀ ti else 0) ∧
      (∀ D : IndirectMechanism ι T Ω, D.IsExPostEfficient val → ∀ t, D.outcome t = ω₁) := by
  classical
  have hval_i₀ (ti : T i₀) (ω : Ω) :
      (if h : i₀ = i₀ then (if ω = ω₁ then v₀ (h ▸ ti) else 0) else 0) =
        if ω = ω₁ then v₀ ti else 0 := by simp only [↓reduceDIte]
  refine ⟨fun i ti ω => if h : i = i₀ then (if ω = ω₁ then v₀ (h ▸ ti) else 0) else 0,
    fun i ti ω => ?_, fun i ti => by simp only [ite_eq_right hω, dite_eq_ite, ite_self],
    hval_i₀, fun D hEff t => ?_⟩
  · by_cases h₁ : i = i₀
    · subst h₁
      by_cases h₂ : ω = ω₁ <;> simp [h₂, zero_le_one.trans (hv₀ ti)]
    · simp [h₁]
  · by_contra hne
    have hw (ω : Ω) :
        (∑ j, if h : j = i₀ then (if ω = ω₁ then v₀ (h ▸ t j) else 0) else 0) =
          if ω = ω₁ then v₀ (t i₀) else 0 := by
      rw [← add_sum_erase _ _ (mem_univ i₀), hval_i₀,
        sum_eq_zero fun j hj => dite_eq_right (ne_of_mem_erase hj), add_zero]
    have key := hEff t ω₁
    rw [hw, hw] at key
    simp only [↓reduceIte, ite_eq_right hne] at key
    linarith [hv₀ (t i₀)]

end IndirectMechanism

namespace Mechanism

/-- Pulling back a welfare-maximizing `Mechanism ι Ω` gives an `IsExPostEfficient` direct
mechanism. -/
theorem isExPostEfficient_toDirectMechanism {ι Ω : Type*} {T : ι → Type*} [Fintype ι]
    {M : Mechanism ι Ω} (hM : IsWelfareMaximizing M.outcome) (val : ∀ i, T i → Ω → ℝ) :
    (M.toDirectMechanism val).IsExPostEfficient val :=
  fun t ω => hM (fun j => val j (t j)) ω

/-- Pulling back a DSIC `Mechanism ι Ω` gives an `IsTruthful` direct mechanism. -/
theorem IsDSIC.isTruthful_toDirectMechanism {ι Ω : Type*} {T : ι → Type*} [DecidableEq ι]
    {M : Mechanism ι Ω} (hM : M.IsDSIC) (val : ∀ i, T i → Ω → ℝ) :
    (M.toDirectMechanism val).IsTruthful val := by
  rw [IndirectMechanism.isTruthful_iff]
  intro t i ti'
  have key := hM i (Function.update (fun j => val j (t j)) i (val i ti')) (val i (t i))
  have hupd : (fun j => val j (Function.update t i ti' j)) =
      Function.update (fun j => val j (t j)) i (val i ti') :=
    funext (Function.apply_update val t i ti')
  simpa only [utility, toDirectMechanism_outcome, toDirectMechanism_payment, hupd,
    Function.update_idem, Function.update_eq_self] using key

end Mechanism

/-! ### Correlated common priors and conditional belief matrices -/

/-- A common prior distribution over finite type profiles `∀ i, T i` with strictly positive
marginal probability on every individual type ([CremerMcLean1988]). -/
structure CorrelatedPrior (ι : Type*) (T : ι → Type*) [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (T i)] where
  /-- Joint probability `prob t` of type profile `t`. -/
  prob : (∀ i, T i) → ℝ
  /-- Joint probabilities are nonnegative. -/
  prob_nonneg : ∀ t, 0 ≤ prob t
  /-- Joint probabilities sum to `1`. -/
  sum_prob_eq_one : ∑ t, prob t = 1
  /-- Every agent `i` and type `ti : T i` has strictly positive marginal probability. -/
  sum_prob_extendProfile_pos : ∀ (i : ι) (ti : T i),
    0 < ∑ t_opp : OppProfile T i, prob (extendProfile i ti t_opp)

namespace CorrelatedPrior

variable {ι : Type*} {T : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, Fintype (T i)]

/-- The joint distribution `P.prob` is a probability vector (`IsMixedStrategy`). -/
theorem isMixedStrategy_prob (P : CorrelatedPrior ι T) : IsMixedStrategy P.prob :=
  isMixedStrategy_iff.2 ⟨P.prob_nonneg, P.sum_prob_eq_one⟩

/-- Marginal probability `Pr(tᵢ = ti)` of agent `i` having type `ti`. -/
def marginal (P : CorrelatedPrior ι T) (i : ι) (ti : T i) : ℝ :=
  ∑ t_opp : OppProfile T i, P.prob (extendProfile i ti t_opp)

theorem marginal_apply (P : CorrelatedPrior ι T) (i : ι) (ti : T i) :
    P.marginal i ti = ∑ t_opp : OppProfile T i, P.prob (extendProfile i ti t_opp) := by
  rfl

/-- Every individual type `ti` has strictly positive marginal probability. -/
theorem marginal_pos (P : CorrelatedPrior ι T) (i : ι) (ti : T i) : 0 < P.marginal i ti :=
  P.sum_prob_extendProfile_pos i ti

theorem marginal_ne_zero (P : CorrelatedPrior ι T) (i : ι) (ti : T i) : P.marginal i ti ≠ 0 :=
  (P.marginal_pos i ti).ne'

/-- Each agent `i`'s marginal distribution is a probability vector (`IsMixedStrategy`). -/
theorem isMixedStrategy_marginal (P : CorrelatedPrior ι T) (i : ι) :
    IsMixedStrategy (P.marginal i) := by
  refine isMixedStrategy_iff.2 ⟨fun ti => (P.marginal_pos i ti).le, ?_⟩
  simp only [marginal_apply, ← sum_profile_eq i P.prob, P.sum_prob_eq_one]

/-- Agent `i`'s conditional belief matrix `Pr(t₋ᵢ = t_opp | tᵢ = ti)` over opponent type profiles
([CremerMcLean1988]). -/
noncomputable def condBelief (P : CorrelatedPrior ι T) (i : ι) :
    Matrix (T i) (OppProfile T i) ℝ :=
  Matrix.of fun ti t_opp => P.prob (extendProfile i ti t_opp) / P.marginal i ti

theorem condBelief_apply (P : CorrelatedPrior ι T) (i : ι) (ti : T i)
    (t_opp : OppProfile T i) :
    P.condBelief i ti t_opp = P.prob (extendProfile i ti t_opp) / P.marginal i ti := by
  rfl

theorem condBelief_nonneg (P : CorrelatedPrior ι T) (i : ι) (ti : T i)
    (t_opp : OppProfile T i) : 0 ≤ P.condBelief i ti t_opp :=
  div_nonneg (P.prob_nonneg _) (P.marginal_pos i ti).le

@[simp]
theorem sum_condBelief_eq_one (P : CorrelatedPrior ι T) (i : ι) (ti : T i) :
    ∑ t_opp : OppProfile T i, P.condBelief i ti t_opp = 1 := by
  simp only [condBelief_apply, ← sum_div]
  exact div_self (P.marginal_ne_zero i ti)

/-- Each row `P.condBelief i ti` of agent `i`'s conditional belief matrix is a probability
distribution (`IsMixedStrategy`) on `OppProfile T i`. -/
theorem isMixedStrategy_condBelief (P : CorrelatedPrior ι T) (i : ι) (ti : T i) :
    IsMixedStrategy (P.condBelief i ti) :=
  isMixedStrategy_iff.2 ⟨P.condBelief_nonneg i ti, P.sum_condBelief_eq_one i ti⟩

@[simp]
theorem marginal_mul_condBelief (P : CorrelatedPrior ι T) (i : ι) (ti : T i)
    (t_opp : OppProfile T i) :
    P.marginal i ti * P.condBelief i ti t_opp = P.prob (extendProfile i ti t_opp) := by
  rw [condBelief_apply, mul_div_cancel₀ _ (P.marginal_ne_zero i ti)]

/-- Law of iterated expectation for agent `i`: any ex-ante expectation under `P` equals the
marginal-weighted sum of conditional expectations under `P.condBelief i`. -/
theorem sum_prob_mul_eq_sum_marginal_mul (P : CorrelatedPrior ι T) (i : ι)
    (g : (∀ j, T j) → ℝ) :
    ∑ t, P.prob t * g t =
      ∑ ti : T i, P.marginal i ti *
        ∑ t_opp : OppProfile T i, P.condBelief i ti t_opp * g (extendProfile i ti t_opp) := by
  rw [sum_profile_eq i]
  refine sum_congr rfl fun ti _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun t_opp _ => ?_
  rw [← mul_assoc, marginal_mul_condBelief]

/-! ### Interim utility, BIC, interim IR, and full surplus extraction -/

section MechanismProperties

variable {Ω : Type*}

/-- Interim expected utility of agent `i` with true type `ti` reporting `ti'` in direct mechanism
`D` when all other agents report truthfully, evaluated under `P.condBelief i ti`. -/
noncomputable def interimUtility (P : CorrelatedPrior ι T) (val : ∀ i, T i → Ω → ℝ)
    (D : IndirectMechanism ι T Ω) (i : ι) (ti ti' : T i) : ℝ :=
  ∑ t_opp : OppProfile T i, P.condBelief i ti t_opp *
    (val i ti (D.outcome (extendProfile i ti' t_opp)) -
      D.payment (extendProfile i ti' t_opp) i)

theorem interimUtility_apply (P : CorrelatedPrior ι T) (val : ∀ i, T i → Ω → ℝ)
    (D : IndirectMechanism ι T Ω) (i : ι) (ti ti' : T i) :
    P.interimUtility val D i ti ti' =
      ∑ t_opp : OppProfile T i, P.condBelief i ti t_opp *
        (val i ti (D.outcome (extendProfile i ti' t_opp)) -
          D.payment (extendProfile i ti' t_opp) i) := by
  rfl

/-- An opponent-only transfer `g` shifts agent `i`'s interim utility at true type `ti` by
`-(P.condBelief i *ᵥ g i) ti`, independent of the reported type `ti'`. -/
@[simp]
theorem interimUtility_withOpponentTransfer (P : CorrelatedPrior ι T) (val : ∀ i, T i → Ω → ℝ)
    (D : IndirectMechanism ι T Ω) (g : ∀ i, OppProfile T i → ℝ) (i : ι) (ti ti' : T i) :
    P.interimUtility val (D.withOpponentTransfer g) i ti ti' =
      P.interimUtility val D i ti ti' - (P.condBelief i *ᵥ g i) ti := by
  simp only [interimUtility_apply, IndirectMechanism.withOpponentTransfer_outcome,
    IndirectMechanism.withOpponentTransfer_payment, oppProj_extendProfile, mulVec, dotProduct]
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun t_opp _ => ?_
  ring

/-- **Bayesian incentive compatibility (`IsBIC`)**: for every agent `i` and true type `ti`,
truthful reporting `ti' = ti` maximizes `P.interimUtility val D i ti`. -/
@[expose] def IsBIC (P : CorrelatedPrior ι T) (val : ∀ i, T i → Ω → ℝ)
    (D : IndirectMechanism ι T Ω) : Prop :=
  ∀ (i : ι) (ti ti' : T i), P.interimUtility val D i ti ti' ≤ P.interimUtility val D i ti ti

/-- Every dominant-strategy truthful direct mechanism is Bayesian incentive compatible under any
correlated prior `P`. -/
theorem isBIC_of_isTruthful (P : CorrelatedPrior ι T) {val : ∀ i, T i → Ω → ℝ}
    {D : IndirectMechanism ι T Ω} (hD : D.IsTruthful val) : P.IsBIC val D := by
  rw [IndirectMechanism.isTruthful_iff] at hD
  intro i ti ti'
  refine sum_le_sum fun t_opp _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (P.condBelief_nonneg i ti t_opp)
  have key := hD (extendProfile i ti t_opp) i ti'
  simpa only [extendProfile_self, update_extendProfile] using key

@[simp]
theorem isBIC_withOpponentTransfer (P : CorrelatedPrior ι T) (val : ∀ i, T i → Ω → ℝ)
    (D : IndirectMechanism ι T Ω) (g : ∀ i, OppProfile T i → ℝ) :
    P.IsBIC val (D.withOpponentTransfer g) ↔ P.IsBIC val D := by
  refine forall_congr' fun i => forall_congr' fun ti => forall_congr' fun ti' => ?_
  simp only [interimUtility_withOpponentTransfer]
  constructor <;> intro h <;> linarith

/-- **Interim individual rationality (`IsInterimIR`)**: every agent `i` and true type `ti`
receives nonnegative interim expected utility under truthful reporting. -/
@[expose] def IsInterimIR (P : CorrelatedPrior ι T) (val : ∀ i, T i → Ω → ℝ)
    (D : IndirectMechanism ι T Ω) : Prop :=
  ∀ (i : ι) (ti : T i), 0 ≤ P.interimUtility val D i ti ti

/-- **Full surplus extraction (`ExtractsFullSurplus`)**: ex-ante expected total payments equal
ex-ante expected realized social welfare ([CremerMcLean1988]). When `D` is `IsExPostEfficient`,
this is the entire expected first-best welfare. -/
@[expose] def ExtractsFullSurplus (P : CorrelatedPrior ι T) (val : ∀ i, T i → Ω → ℝ)
    (D : IndirectMechanism ι T Ω) : Prop :=
  ∑ t, P.prob t * ∑ i, D.payment t i = ∑ t, P.prob t * ∑ i, val i (t i) (D.outcome t)

/-- Ex-ante total agent rent equals expected social welfare minus expected total payments. -/
theorem sum_marginal_mul_interimUtility (P : CorrelatedPrior ι T) (val : ∀ i, T i → Ω → ℝ)
    (D : IndirectMechanism ι T Ω) :
    ∑ i, ∑ ti : T i, P.marginal i ti * P.interimUtility val D i ti ti =
      (∑ t, P.prob t * ∑ i, val i (t i) (D.outcome t)) -
        ∑ t, P.prob t * ∑ i, D.payment t i := by
  have hagent : ∀ i : ι,
      ∑ ti : T i, P.marginal i ti * P.interimUtility val D i ti ti =
        ∑ t, P.prob t * (val i (t i) (D.outcome t) - D.payment t i) := fun i => by
    rw [P.sum_prob_mul_eq_sum_marginal_mul i]
    refine sum_congr rfl fun ti _ => ?_
    simp only [interimUtility_apply, extendProfile_self]
  simp only [hagent]
  rw [sum_comm, ← sum_sub_distrib]
  refine sum_congr rfl fun t _ => ?_
  rw [← mul_sum, sum_sub_distrib, mul_sub]

/-- Zero truthful interim utility at every agent and type implies `ExtractsFullSurplus`. -/
theorem extractsFullSurplus_of_forall_interimUtility_eq_zero (P : CorrelatedPrior ι T)
    {val : ∀ i, T i → Ω → ℝ} {D : IndirectMechanism ι T Ω}
    (h0 : ∀ i (ti : T i), P.interimUtility val D i ti ti = 0) :
    P.ExtractsFullSurplus val D := by
  have h := P.sum_marginal_mul_interimUtility val D
  simp only [h0, mul_zero, sum_const_zero] at h
  rw [ExtractsFullSurplus]
  linarith

/-- Under `IsInterimIR`, a mechanism extracts the full surplus if and only if every agent and every
type earns zero interim utility (`P.interimUtility val D i ti ti = 0`), because every marginal
probability `P.marginal i ti` is strictly positive. -/
theorem extractsFullSurplus_iff_forall_interimUtility_eq_zero (P : CorrelatedPrior ι T)
    {val : ∀ i, T i → Ω → ℝ} {D : IndirectMechanism ι T Ω} (hIR : P.IsInterimIR val D) :
    P.ExtractsFullSurplus val D ↔
      ∀ i (ti : T i), P.interimUtility val D i ti ti = 0 := by
  refine ⟨fun hExt i ti => ?_, P.extractsFullSurplus_of_forall_interimUtility_eq_zero⟩
  have hsum : ∑ j, ∑ tj : T j, P.marginal j tj * P.interimUtility val D j tj tj = 0 := by
    rw [P.sum_marginal_mul_interimUtility, hExt, sub_self]
  have hnonneg_outer : ∀ j ∈ (univ : Finset ι),
      0 ≤ ∑ tj : T j, P.marginal j tj * P.interimUtility val D j tj tj :=
    fun j _ => sum_nonneg fun tj _ => mul_nonneg (P.marginal_pos j tj).le (hIR j tj)
  have hj := (sum_eq_zero_iff_of_nonneg hnonneg_outer).1 hsum i (mem_univ i)
  have hti := (sum_eq_zero_iff_of_nonneg
    (fun tj _ => mul_nonneg (P.marginal_pos i tj).le (hIR i tj))).1 hj ti (mem_univ ti)
  exact (mul_eq_zero.1 hti).resolve_left (P.marginal_ne_zero i ti)

end MechanismProperties

/-! ### Dominant-strategy characterization: full belief row rank (`HasFullBeliefRank`) -/

/-- The correlated prior `P` satisfies the **full belief-rank condition** of [CremerMcLean1988] if
for every agent `i`, the rows `ti ↦ P.condBelief i ti` of `i`'s conditional belief matrix are
linearly independent over `ℝ`. -/
@[expose] def HasFullBeliefRank (P : CorrelatedPrior ι T) : Prop :=
  ∀ i : ι, LinearIndependent ℝ (fun ti => P.condBelief i ti)

private theorem sum_smul_row_eq_vecMul {m n : Type*} [Fintype m] (A : Matrix m n ℝ)
    (c : m → ℝ) : (∑ r, c r • A r) = c ᵥ* A := by
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecMul, dotProduct]

private theorem linearIndependent_rows_iff_forall_exists_mulVec_eq {m n : Type*} [Finite m]
    [Fintype n] (A : Matrix m n ℝ) :
    LinearIndependent ℝ (fun r : m => A r) ↔ ∀ target : m → ℝ, ∃ g : n → ℝ, A *ᵥ g = target := by
  have := Fintype.ofFinite m
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro hLI target
    let M : Matrix (m ⊕ m) n ℝ := Matrix.fromRows A (-A)
    let b : m ⊕ m → ℝ := Sum.elim target (-target)
    obtain ⟨g, hg⟩ := (Matrix.exists_mulVec_le_iff M b).2 fun y hy hyM => by
      set c : m → ℝ := y ∘ Sum.inl - y ∘ Sum.inr
      have hcA : ∑ r, c r • A r = 0 := by
        rw [sum_smul_row_eq_vecMul]
        funext k
        have hk := congr_fun hyM k
        simp only [M, vecMul_fromRows, vecMul_neg, Pi.add_apply, Pi.neg_apply,
          Pi.zero_apply] at hk
        simp only [c, sub_vecMul, Pi.sub_apply, Pi.zero_apply]
        linarith
      have hc0 : c = 0 := funext (hLI c hcA)
      have hdot : y ⬝ᵥ b = c ⬝ᵥ target := by
        rw [← Sum.elim_comp_inl_inr y]
        simp only [b, c, sumElim_dotProduct_sumElim, dotProduct_neg, sub_dotProduct]
        ring
      rw [hdot, hc0, zero_dotProduct]
    refine ⟨g, le_antisymm (fun r => hg (.inl r)) fun r => ?_⟩
    have hr := hg (.inr r)
    simp only [M, b, fromRows_mulVec, neg_mulVec, Sum.elim_inr, Pi.neg_apply,
      neg_le_neg_iff] at hr
    exact hr
  · intro hSurj c hc
    obtain ⟨g, hg⟩ := hSurj c
    have hcA : c ᵥ* A = 0 := by rwa [← sum_smul_row_eq_vecMul]
    have hcc : c ⬝ᵥ c = 0 := by
      calc c ⬝ᵥ c = c ⬝ᵥ (A *ᵥ g) := by rw [hg]
        _ = (c ᵥ* A) ⬝ᵥ g := dotProduct_mulVec c A g
        _ = 0 := by rw [hcA, zero_dotProduct]
    have hnonneg : ∀ r ∈ (univ : Finset m), 0 ≤ c r * c r := fun r _ => mul_self_nonneg (c r)
    intro r
    exact mul_self_eq_zero.1 ((sum_eq_zero_iff_of_nonneg hnonneg).1 hcc r (mem_univ r))

/-- `P.HasFullBeliefRank` holds if and only if every interim side-bet equation
`P.condBelief i *ᵥ g = target` is solvable. -/
theorem hasFullBeliefRank_iff_forall_exists_mulVec_eq (P : CorrelatedPrior ι T) :
    P.HasFullBeliefRank ↔
      ∀ (i : ι) (target : T i → ℝ), ∃ g : OppProfile T i → ℝ, P.condBelief i *ᵥ g = target :=
  forall_congr' fun i => linearIndependent_rows_iff_forall_exists_mulVec_eq (P.condBelief i)

namespace HasFullBeliefRank

/-- Upgrade any baseline direct mechanism `D₀` by opponent-only side transfers so that every type
receives zero truthful interim utility while preserving `D₀.outcome` (hence `IsExPostEfficient`
and `IsTruthful`). -/
theorem exists_withOpponentTransfer_extractsFullSurplus {P : CorrelatedPrior ι T}
    (hP : P.HasFullBeliefRank) {Ω : Type*} (val : ∀ i, T i → Ω → ℝ)
    (D₀ : IndirectMechanism ι T Ω) :
    ∃ g : ∀ i, OppProfile T i → ℝ,
      (∀ i (ti : T i), P.interimUtility val (D₀.withOpponentTransfer g) i ti ti = 0) ∧
      P.IsInterimIR val (D₀.withOpponentTransfer g) ∧
      P.ExtractsFullSurplus val (D₀.withOpponentTransfer g) := by
  have hSurj := P.hasFullBeliefRank_iff_forall_exists_mulVec_eq.1 hP
  choose g hg using fun i => hSurj i (fun ti => P.interimUtility val D₀ i ti ti)
  have hzero : ∀ i (ti : T i), P.interimUtility val (D₀.withOpponentTransfer g) i ti ti = 0 := by
    intro i ti
    rw [interimUtility_withOpponentTransfer, hg i, sub_self]
  exact ⟨g, hzero, fun i ti => (hzero i ti).ge,
    P.extractsFullSurplus_of_forall_interimUtility_eq_zero hzero⟩

/-- **Crémer–McLean dominant-strategy full surplus extraction** ([CremerMcLean1988]): under
`P.HasFullBeliefRank`, for any nonempty finite outcome space `Ω` and arbitrary valuations `val`,
adding opponent-only transfers to a VCG baseline yields a direct mechanism that is simultaneously
ex-post efficient, dominant-strategy truthful (`IsTruthful`), interim individually rational, and
extracts the full surplus. -/
theorem exists_isTruthful_interimIR_extractsFullSurplus {P : CorrelatedPrior ι T}
    (hP : P.HasFullBeliefRank) {Ω : Type*} [Finite Ω] [Nonempty Ω]
    (val : ∀ i, T i → Ω → ℝ) :
    ∃ D : IndirectMechanism ι T Ω,
      D.IsExPostEfficient val ∧
      D.IsTruthful val ∧
      P.IsInterimIR val D ∧
      P.ExtractsFullSurplus val D ∧
      ∀ i (ti : T i), P.interimUtility val D i ti ti = 0 := by
  have := Fintype.ofFinite Ω
  obtain ⟨f, hf⟩ := Mechanism.exists_isWelfareMaximizing (ι := ι) (Ω := Ω)
  let D₀ : IndirectMechanism ι T Ω := (Mechanism.vcg f).toDirectMechanism val
  obtain ⟨g, hzero, hIR, hExt⟩ := hP.exists_withOpponentTransfer_extractsFullSurplus val D₀
  refine ⟨D₀.withOpponentTransfer g, ?_, ?_, hIR, hExt, hzero⟩
  · rw [IndirectMechanism.isExPostEfficient_withOpponentTransfer]
    exact Mechanism.isExPostEfficient_toDirectMechanism hf val
  · rw [IndirectMechanism.isTruthful_withOpponentTransfer]
    exact (Mechanism.vcg_isDSIC hf).isTruthful_toDirectMechanism val

end HasFullBeliefRank

private theorem mulVec_condBelief_sub_const (P : CorrelatedPrior ι T) (i : ι)
    (g : OppProfile T i → ℝ) (c : ℝ) (ti : T i) :
    (P.condBelief i *ᵥ fun t_opp => g t_opp - c) ti = (P.condBelief i *ᵥ g) ti - c := by
  simp only [mulVec, dotProduct, mul_sub, sum_sub_distrib, ← sum_mul, P.sum_condBelief_eq_one,
    one_mul]

/-- **Converse to Crémer–McLean dominant-strategy extraction**: if `P.HasFullBeliefRank` fails and
`Ω` has at least two outcomes, there exists a nonnegative valuation profile (normalized to `0` on
a status-quo outcome) for which no ex-post efficient, dominant-strategy truthful (`IsTruthful`),
interim-IR direct mechanism extracts the full surplus. -/
theorem exists_nonneg_val_not_exists_isTruthful_of_not_hasFullBeliefRank
    {P : CorrelatedPrior ι T} (hP : ¬ P.HasFullBeliefRank) {Ω : Type*} [Nontrivial Ω] :
    ∃ val : (∀ i, T i → Ω → ℝ),
      (∀ i ti ω, 0 ≤ val i ti ω) ∧
      (∃ ω₀, ∀ i ti, val i ti ω₀ = 0) ∧
      ¬ ∃ D : IndirectMechanism ι T Ω,
          D.IsExPostEfficient val ∧
          D.IsTruthful val ∧
          P.IsInterimIR val D ∧
          P.ExtractsFullSurplus val D := by
  classical
  have hnotSurj := mt P.hasFullBeliefRank_iff_forall_exists_mulVec_eq.2 hP
  push Not at hnotSurj
  obtain ⟨i₀, c, hno_sol⟩ := hnotSurj
  obtain ⟨ti₀, -⟩ := Function.ne_iff.1 (show c ≠ 0 from fun hc0 => hno_sol 0 (by simp [hc0]))
  obtain ⟨ω₀, ω₁, hω⟩ := exists_pair_ne Ω
  let shift : ℝ := 1 + ∑ ti : T i₀, |c ti|
  have hpos_val (ti : T i₀) : 1 ≤ shift + c ti := by
    dsimp only [shift]
    linarith [single_le_sum (f := fun ti' => |c ti'|) (fun _ _ => abs_nonneg _) (mem_univ ti),
      neg_le_abs (c ti)]
  obtain ⟨val, hnn, h0, hval_i₀, hout_of_eff⟩ :=
    IndirectMechanism.exists_singleAgentVal (T := T) i₀ hω (fun ti => shift + c ti) hpos_val
  refine ⟨val, hnn, ⟨ω₀, h0⟩, ?_⟩
  rintro ⟨D, hEff, hTruth, hIR, hExt⟩
  rw [IndirectMechanism.isTruthful_iff] at hTruth
  have hzero := (P.extractsFullSurplus_iff_forall_interimUtility_eq_zero hIR).1 hExt
  have hout := hout_of_eff D hEff
  have hpay_const (ti : T i₀) (t_opp : OppProfile T i₀) :
      D.payment (extendProfile i₀ ti t_opp) i₀ =
        D.payment (extendProfile i₀ ti₀ t_opp) i₀ := by
    have h1 := hTruth (extendProfile i₀ ti t_opp) i₀ ti₀
    have h2 := hTruth (extendProfile i₀ ti₀ t_opp) i₀ ti
    simp only [update_extendProfile, hout] at h1 h2; linarith
  refine hno_sol (fun t_opp => D.payment (extendProfile i₀ ti₀ t_opp) i₀ - shift)
    (funext fun ti => ?_)
  rw [P.mulVec_condBelief_sub_const]
  have hu := hzero i₀ ti
  simp only [interimUtility_apply, hout, hval_i₀, ↓reduceIte, hpay_const ti] at hu
  have hu' := P.mulVec_condBelief_sub_const i₀
    (fun t_opp => D.payment (extendProfile i₀ ti₀ t_opp) i₀) (shift + c ti) ti
  have hsum0 : (P.condBelief i₀ *ᵥ fun t_opp =>
      D.payment (extendProfile i₀ ti₀ t_opp) i₀ - (shift + c ti)) ti = 0 := by
    simp only [mulVec, dotProduct, ← neg_sub (shift + c ti), mul_neg, sum_neg_distrib, hu,
      neg_zero]
  linarith

/-- **Crémer–McLean dominant-strategy characterization** ([CremerMcLean1988]): for any finite
outcome space `Ω` with at least two outcomes, `P.HasFullBeliefRank` holds if and only if every
nonnegative valuation profile admits an ex-post efficient, dominant-strategy truthful
(`IsTruthful`), interim-IR direct mechanism extracting the full surplus. -/
theorem hasFullBeliefRank_iff_forall_exists_isTruthful (P : CorrelatedPrior ι T)
    (Ω : Type*) [Finite Ω] [Nontrivial Ω] :
    P.HasFullBeliefRank ↔
      ∀ val : (∀ i, T i → Ω → ℝ), (∀ i ti ω, 0 ≤ val i ti ω) →
        ∃ D : IndirectMechanism ι T Ω,
          D.IsExPostEfficient val ∧
          D.IsTruthful val ∧
          P.IsInterimIR val D ∧
          P.ExtractsFullSurplus val D := by
  refine ⟨fun hP val _ => ?_, fun H => ?_⟩
  · obtain ⟨D, hEff, hTruth, hIR, hExt, -⟩ :=
      hP.exists_isTruthful_interimIR_extractsFullSurplus val
    exact ⟨D, hEff, hTruth, hIR, hExt⟩
  · by_contra hP
    obtain ⟨val, hnonneg, -, hno⟩ :=
      exists_nonneg_val_not_exists_isTruthful_of_not_hasFullBeliefRank (Ω := Ω) hP
    exact hno (H val hnonneg)

/-! ### Bayesian characterization: convex independence of beliefs (`HasConvexIndependentBeliefs`) -/

/-- The correlated prior `P` satisfies the **convex-independence belief condition** of
[CremerMcLean1988] if for every agent `i`, the family `ti ↦ P.condBelief i ti` of conditional
belief vectors is convex independent (`ConvexIndependent ℝ`). -/
@[expose] def HasConvexIndependentBeliefs (P : CorrelatedPrior ι T) : Prop :=
  ∀ i : ι, ConvexIndependent ℝ (fun ti => P.condBelief i ti)

/-- Convex independence of conditional beliefs means that no type `ti`'s conditional belief lies in
the convex hull of the conditional beliefs of types `ti' ≠ ti`. -/
theorem hasConvexIndependentBeliefs_iff (P : CorrelatedPrior ι T) :
    P.HasConvexIndependentBeliefs ↔
      ∀ (i : ι) (ti : T i),
        P.condBelief i ti ∉
          convexHull ℝ ((fun ti' => P.condBelief i ti') '' {ti' : T i | ti' ≠ ti}) := by
  refine forall_congr' fun i => ?_
  rw [convexIndependent_iff_notMem_convexHull_sdiff]
  constructor
  · intro h ti
    have hset : ({ti' : T i | ti' ≠ ti} : Set (T i)) = Set.univ \ {ti} := by
      ext ti'
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
    rw [hset]
    exact h ti Set.univ
  · intro h ti s hmem
    refine h ti (convexHull_mono (Set.image_mono fun ti' hti' => ?_) hmem)
    exact hti'.2

/-- Membership of `P.condBelief i ti` in the convex hull of the other types' conditional beliefs is
equivalent to the existence of a probability distribution `w` on `{ti' // ti' ≠ ti}` reproducing
`P.condBelief i ti`. -/
theorem condBelief_mem_convexHull_iff (P : CorrelatedPrior ι T) (i : ι) [DecidableEq (T i)]
    (ti : T i) :
    P.condBelief i ti ∈
        convexHull ℝ ((fun ti' => P.condBelief i ti') '' {ti' : T i | ti' ≠ ti}) ↔
      ∃ w : {ti' : T i // ti' ≠ ti} → ℝ,
        IsMixedStrategy w ∧
        ∑ ti' : {ti' : T i // ti' ≠ ti}, w ti' • P.condBelief i ti'.1 = P.condBelief i ti := by
  classical
  constructor
  · intro hmem
    obtain ⟨κ, _, w', z, hw'0, hw'1, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.1 hmem
    choose τ hτ_ne hτ_eq using hz
    let idx : κ → {ti' : T i // ti' ≠ ti} := fun k => ⟨τ k, hτ_ne k⟩
    let w : {ti' : T i // ti' ≠ ti} → ℝ :=
      fun ti' => ∑ k ∈ univ.filter (fun k => idx k = ti'), w' k
    refine ⟨w, isMixedStrategy_iff.2 ⟨fun ti' => sum_nonneg fun k _ => hw'0 k, ?_⟩, ?_⟩
    · simp only [w]
      rw [sum_fiberwise_of_maps_to (fun _ _ => mem_univ _), hw'1]
    · simp only [w]
      calc ∑ ti' : {ti' : T i // ti' ≠ ti},
            (∑ k ∈ univ.filter (fun k => idx k = ti'), w' k) • P.condBelief i ti'.1
          = ∑ ti' : {ti' : T i // ti' ≠ ti},
              ∑ k ∈ univ.filter (fun k => idx k = ti'), w' k • z k := by
              refine sum_congr rfl fun ti' _ => ?_
              rw [sum_smul]
              refine sum_congr rfl fun k hk => ?_
              have hk' : ti'.1 = τ k := congrArg Subtype.val (mem_filter.1 hk).2.symm
              exact congrArg (w' k • ·)
                ((congrArg (fun x => P.condBelief i x) hk').trans (hτ_eq k))
        _ = ∑ k : κ, w' k • z k := sum_fiberwise_of_maps_to (fun _ _ => mem_univ _) _
        _ = P.condBelief i ti := hsum
  · rintro ⟨w, hw, hsum⟩
    exact mem_convexHull_of_exists_fintype w (fun ti' => P.condBelief i ti'.1)
      hw.nonneg hw.sum_eq_one (fun ti' => ⟨ti'.1, ti'.2, rfl⟩) hsum

/-- **Farkas separating-lottery characterization** ([CremerMcLean1988]): type `ti`'s conditional
belief lies outside the convex hull of `{P.condBelief i ti' | ti' ≠ ti}` if and only if there is a
side-lottery fee schedule `h : OppProfile T i → ℝ` with zero conditional expectation under `ti`
and strictly positive conditional expectation under every `ti' ≠ ti`. -/
theorem condBelief_notMem_convexHull_iff_exists_separating_lottery (P : CorrelatedPrior ι T)
    (i : ι) (ti : T i) :
    P.condBelief i ti ∉
        convexHull ℝ ((fun ti' => P.condBelief i ti') '' {ti' : T i | ti' ≠ ti}) ↔
      ∃ h : OppProfile T i → ℝ,
        (P.condBelief i *ᵥ h) ti = 0 ∧
        ∀ ti' : T i, ti' ≠ ti → 0 < (P.condBelief i *ᵥ h) ti' := by
  let _ := Classical.decEq (T i)
  rw [P.condBelief_mem_convexHull_iff i ti]
  let A : Matrix (OppProfile T i) {ti' : T i // ti' ≠ ti} ℝ :=
    Matrix.of fun t_opp ti' => P.condBelief i ti'.1 t_opp
  constructor
  · intro hnot
    have hnoA : ¬ ∃ w : {ti' : T i // ti' ≠ ti} → ℝ, 0 ≤ w ∧ A *ᵥ w = P.condBelief i ti := by
      rintro ⟨w, hw0, hwA⟩
      have hcomb : ∑ ti' : {ti' : T i // ti' ≠ ti}, w ti' • P.condBelief i ti'.1 =
          P.condBelief i ti := by
        funext t_opp
        have ht := congr_fun hwA t_opp
        simp only [A, mulVec, dotProduct, Matrix.of_apply] at ht
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        simpa only [mul_comm] using ht
      have hw1 : ∑ ti' : {ti' : T i // ti' ≠ ti}, w ti' = 1 := by
        have htot := congrArg (fun b : OppProfile T i → ℝ => ∑ t_opp, b t_opp) hcomb
        simp only [P.sum_condBelief_eq_one i ti, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          at htot
        rw [sum_comm] at htot
        simpa only [← mul_sum, P.sum_condBelief_eq_one i, mul_one] using htot
      exact hnot ⟨w, isMixedStrategy_iff.2 ⟨hw0, hw1⟩, hcomb⟩
    obtain ⟨y, hyA, hyb⟩ := (Matrix.not_exists_nonneg_mulVec_eq_iff A (P.condBelief i ti)).1 hnoA
    let c : ℝ := y ⬝ᵥ P.condBelief i ti
    refine ⟨fun t_opp => y t_opp - c, ?_, fun ti' hne => ?_⟩
    · rw [P.mulVec_condBelief_sub_const]
      exact sub_eq_zero.2 (dotProduct_comm _ _)
    · rw [P.mulVec_condBelief_sub_const]
      have hy_ti' : 0 ≤ (y ᵥ* A) ⟨ti', hne⟩ := hyA ⟨ti', hne⟩
      simp only [A, vecMul, mulVec, Matrix.of_apply] at hy_ti' ⊢
      rw [dotProduct_comm] at hy_ti'
      have hc : c < 0 := hyb
      linarith
  · rintro ⟨h, h0, hpos⟩ ⟨w, hw, hcomb⟩
    have hdot_pos : 0 < w ⬝ᵥ fun ti' : {ti' : T i // ti' ≠ ti} => (P.condBelief i *ᵥ h) ti'.1 :=
      hw.dotProduct_pos fun ti' => hpos ti'.1 ti'.2
    have hdot_eq :
        (w ⬝ᵥ fun ti' : {ti' : T i // ti' ≠ ti} => (P.condBelief i *ᵥ h) ti'.1) =
          (P.condBelief i *ᵥ h) ti := by
      simp only [dotProduct, mulVec, mul_sum]
      rw [sum_comm]
      have hcomb_dot := congrArg (fun b : OppProfile T i → ℝ => b ⬝ᵥ h) hcomb
      simpa only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_mul,
        mul_assoc] using hcomb_dot
    linarith

/-- Full row rank of conditional beliefs implies convex independence of conditional beliefs. -/
theorem HasFullBeliefRank.hasConvexIndependentBeliefs {P : CorrelatedPrior ι T}
    (hP : P.HasFullBeliefRank) : P.HasConvexIndependentBeliefs := by
  classical
  rw [hasConvexIndependentBeliefs_iff]
  intro i ti
  rw [condBelief_notMem_convexHull_iff_exists_separating_lottery]
  obtain ⟨h, hh⟩ := P.hasFullBeliefRank_iff_forall_exists_mulVec_eq.1 hP i
    (fun ti' => if ti' = ti then 0 else 1)
  refine ⟨h, ?_, fun ti' hne => ?_⟩
  · simp only [hh, ↓reduceIte]
  · simp only [hh, ite_eq_right hne, zero_lt_one]

namespace HasConvexIndependentBeliefs

/-- Under `P.HasConvexIndependentBeliefs`, every agent `i` and reported type `r : T i` admits a
separating lottery `h : OppProfile T i → ℝ` with zero expectation under `r` and strictly positive
expectation under every true type `ti ≠ r`. -/
theorem exists_separating_lottery {P : CorrelatedPrior ι T}
    (hP : P.HasConvexIndependentBeliefs) (i : ι) (r : T i) :
    ∃ h : OppProfile T i → ℝ,
      (P.condBelief i *ᵥ h) r = 0 ∧
      ∀ ti : T i, ti ≠ r → 0 < (P.condBelief i *ᵥ h) ti :=
  (P.condBelief_notMem_convexHull_iff_exists_separating_lottery i r).1
    ((P.hasConvexIndependentBeliefs_iff.1 hP) i r)

/-- **Outcome-implementing Bayesian full surplus extraction** ([CremerMcLean1988]): under
`P.HasConvexIndependentBeliefs`, any outcome rule `f : (∀ i, T i) → Ω` on any outcome type `Ω` can
be paired with payments so that truthful reporting is strictly optimal in interim utility, every
type receives zero interim utility (`IsInterimIR`), and the full surplus of `f` is extracted. -/
theorem exists_outcome_eq_isBIC_extractsFullSurplus {P : CorrelatedPrior ι T}
    (hP : P.HasConvexIndependentBeliefs) {Ω : Type*} (val : ∀ i, T i → Ω → ℝ)
    (f : (∀ i, T i) → Ω) :
    ∃ D : IndirectMechanism ι T Ω,
      D.outcome = f ∧
      (∀ (i : ι) (ti ti' : T i), ti' ≠ ti →
        P.interimUtility val D i ti ti' < P.interimUtility val D i ti ti) ∧
      P.IsBIC val D ∧
      P.IsInterimIR val D ∧
      P.ExtractsFullSurplus val D ∧
      ∀ i (ti : T i), P.interimUtility val D i ti ti = 0 := by
  classical
  choose h hh using fun i r => hP.exists_separating_lottery i r
  have hh_zero : ∀ i r, (P.condBelief i *ᵥ h i r) r = 0 := fun i r => (hh i r).1
  have hh_pos : ∀ i r ti, ti ≠ r → 0 < (P.condBelief i *ᵥ h i r) ti := fun i r => (hh i r).2
  let gain : ∀ i, T i → T i → ℝ := fun i ti r =>
    ∑ t_opp : OppProfile T i, P.condBelief i ti t_opp *
      (val i ti (f (extendProfile i r t_opp)) - val i r (f (extendProfile i r t_opp)))
  let scale : ∀ i, T i → ℝ := fun i r =>
    1 + ∑ ti : T i, if ti = r then 0 else |gain i ti r| / (P.condBelief i *ᵥ h i r) ti
  let D : IndirectMechanism ι T Ω :=
    { outcome := f
      payment := fun t i => val i (t i) (f t) + scale i (t i) * h i (t i) (oppProj i t) }
  have hinterim : ∀ (i : ι) (ti r : T i),
      P.interimUtility val D i ti r =
        gain i ti r - scale i r * (P.condBelief i *ᵥ h i r) ti := fun i ti r => by
    simp only [interimUtility_apply, D, extendProfile_self, oppProj_extendProfile, gain, mulVec,
      dotProduct, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun t_opp _ => ?_
    ring
  have hzero : ∀ i (ti : T i), P.interimUtility val D i ti ti = 0 := fun i ti => by
    rw [hinterim, hh_zero i ti, mul_zero, sub_zero]
    simp only [gain, sub_self, mul_zero, sum_const_zero]
  have hstrict : ∀ (i : ι) (ti r : T i), r ≠ ti →
      P.interimUtility val D i ti r < P.interimUtility val D i ti ti := fun i ti r hne => by
    rw [hzero i ti, hinterim]
    have hti_ne : ti ≠ r := hne.symm
    have hpen_pos : 0 < (P.condBelief i *ᵥ h i r) ti := hh_pos i r ti hti_ne
    have hterm_nonneg : ∀ ti' ∈ (univ : Finset (T i)),
        0 ≤ (if ti' = r then 0 else |gain i ti' r| / (P.condBelief i *ᵥ h i r) ti') := by
      intro ti' _
      split_ifs with heq
      · exact le_rfl
      · exact div_nonneg (abs_nonneg _) (hh_pos i r ti' heq).le
    have hle_sum : |gain i ti r| / (P.condBelief i *ᵥ h i r) ti ≤
        ∑ ti' : T i, if ti' = r then 0 else |gain i ti' r| / (P.condBelief i *ᵥ h i r) ti' := by
      simpa only [ite_eq_right hti_ne] using single_le_sum hterm_nonneg (mem_univ ti)
    have hlt_scale : gain i ti r / (P.condBelief i *ᵥ h i r) ti < scale i r := by
      have habs : gain i ti r / (P.condBelief i *ᵥ h i r) ti ≤
          |gain i ti r| / (P.condBelief i *ᵥ h i r) ti :=
        div_le_div_of_nonneg_right (le_abs_self _) hpen_pos.le
      dsimp only [scale]
      linarith
    have hmul : gain i ti r < scale i r * (P.condBelief i *ᵥ h i r) ti :=
      (div_lt_iff₀ hpen_pos).1 hlt_scale
    linarith
  refine ⟨D, rfl, hstrict, fun i ti r => ?_, fun i ti => (hzero i ti).ge,
    P.extractsFullSurplus_of_forall_interimUtility_eq_zero hzero, hzero⟩
  rcases eq_or_ne r ti with rfl | hne
  · exact le_rfl
  · exact (hstrict i ti r hne).le

/-- **Crémer–McLean Bayesian full surplus extraction** ([CremerMcLean1988]): under
`P.HasConvexIndependentBeliefs`, for any nonempty finite outcome space `Ω` and arbitrary valuations
`val`, there exists a direct mechanism that is ex-post efficient, strictly Bayesian incentive
compatible, interim individually rational, and extracts the full surplus. -/
theorem exists_isBIC_interimIR_extractsFullSurplus {P : CorrelatedPrior ι T}
    (hP : P.HasConvexIndependentBeliefs) {Ω : Type*} [Finite Ω] [Nonempty Ω]
    (val : ∀ i, T i → Ω → ℝ) :
    ∃ D : IndirectMechanism ι T Ω,
      D.IsExPostEfficient val ∧
      (∀ (i : ι) (ti ti' : T i), ti' ≠ ti →
        P.interimUtility val D i ti ti' < P.interimUtility val D i ti ti) ∧
      P.IsBIC val D ∧
      P.IsInterimIR val D ∧
      P.ExtractsFullSurplus val D ∧
      ∀ i (ti : T i), P.interimUtility val D i ti ti = 0 := by
  have := Fintype.ofFinite Ω
  obtain ⟨f, hf⟩ := Mechanism.exists_isWelfareMaximizing (ι := ι) (Ω := Ω)
  obtain ⟨D, hOut, hstrict, hBIC, hIR, hExt, hzero⟩ :=
    hP.exists_outcome_eq_isBIC_extractsFullSurplus val fun t => f (fun j => val j (t j))
  refine ⟨D, fun t ω => ?_, hstrict, hBIC, hIR, hExt, hzero⟩
  rw [hOut]
  exact hf (fun j => val j (t j)) ω

end HasConvexIndependentBeliefs

/-! ### Information-rent lower bound, Bayesian converse, and independent priors -/

/-- **Convex-dependence information-rent bound**: if agent `i₀`'s conditional belief at `ti₀` is a
nonnegative combination `∑ ti', w ti' • P.condBelief i₀ ti'.1` of other types' conditional beliefs,
then in *every* `IsBIC` mechanism `D`, the weighted sum of truthful interim utilities at
`{ti' // ti' ≠ ti₀}` exceeds `P.interimUtility val D i₀ ti₀ ti₀` by at least the expected valuation
advantage of mimicking `ti₀`. -/
theorem le_interimUtility_add_sum_of_convexComb (P : CorrelatedPrior ι T) {Ω : Type*}
    {val : ∀ i, T i → Ω → ℝ} {D : IndirectMechanism ι T Ω} (hBIC : P.IsBIC val D)
    {i₀ : ι} [DecidableEq (T i₀)] {ti₀ : T i₀} {w : {ti' : T i₀ // ti' ≠ ti₀} → ℝ}
    (hw : ∀ ti', 0 ≤ w ti')
    (hcomb : ∑ ti' : {ti' : T i₀ // ti' ≠ ti₀}, w ti' • P.condBelief i₀ ti'.1 =
      P.condBelief i₀ ti₀) :
    P.interimUtility val D i₀ ti₀ ti₀ +
        (∑ ti' : {ti' : T i₀ // ti' ≠ ti₀}, w ti' *
          ∑ t_opp : OppProfile T i₀, P.condBelief i₀ ti'.1 t_opp *
            (val i₀ ti'.1 (D.outcome (extendProfile i₀ ti₀ t_opp)) -
              val i₀ ti₀ (D.outcome (extendProfile i₀ ti₀ t_opp)))) ≤
      ∑ ti' : {ti' : T i₀ // ti' ≠ ti₀}, w ti' * P.interimUtility val D i₀ ti'.1 ti'.1 := by
  have hcomb_pt : ∀ t_opp : OppProfile T i₀,
      ∑ ti' : {ti' : T i₀ // ti' ≠ ti₀}, w ti' * P.condBelief i₀ ti'.1 t_opp =
        P.condBelief i₀ ti₀ t_opp := fun t_opp => by
    have ht := congr_fun hcomb t_opp
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using ht
  have hdev : (∑ ti' : {ti' : T i₀ // ti' ≠ ti₀},
        w ti' * P.interimUtility val D i₀ ti'.1 ti₀) ≤
      ∑ ti' : {ti' : T i₀ // ti' ≠ ti₀},
        w ti' * P.interimUtility val D i₀ ti'.1 ti'.1 :=
    sum_le_sum fun ti' _ => mul_le_mul_of_nonneg_left (hBIC i₀ ti'.1 ti₀) (hw ti')
  have hident : P.interimUtility val D i₀ ti₀ ti₀ +
      (∑ ti' : {ti' : T i₀ // ti' ≠ ti₀}, w ti' *
        ∑ t_opp : OppProfile T i₀, P.condBelief i₀ ti'.1 t_opp *
          (val i₀ ti'.1 (D.outcome (extendProfile i₀ ti₀ t_opp)) -
            val i₀ ti₀ (D.outcome (extendProfile i₀ ti₀ t_opp)))) =
      ∑ ti' : {ti' : T i₀ // ti' ≠ ti₀}, w ti' * P.interimUtility val D i₀ ti'.1 ti₀ := by
    simp only [interimUtility_apply]
    have hti₀_expand :
        ∑ t_opp : OppProfile T i₀, P.condBelief i₀ ti₀ t_opp *
            (val i₀ ti₀ (D.outcome (extendProfile i₀ ti₀ t_opp)) -
              D.payment (extendProfile i₀ ti₀ t_opp) i₀) =
          ∑ ti' : {ti' : T i₀ // ti' ≠ ti₀}, w ti' *
            ∑ t_opp : OppProfile T i₀, P.condBelief i₀ ti'.1 t_opp *
              (val i₀ ti₀ (D.outcome (extendProfile i₀ ti₀ t_opp)) -
                D.payment (extendProfile i₀ ti₀ t_opp) i₀) := by
      simp_rw [← hcomb_pt, sum_mul]
      rw [sum_comm]
      refine sum_congr rfl fun ti' _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun t_opp _ => ?_
      ring
    rw [hti₀_expand, ← sum_add_distrib]
    refine sum_congr rfl fun ti' _ => ?_
    rw [← mul_add, ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun t_opp _ => ?_
    ring
  linarith

/-- **Converse to Crémer–McLean Bayesian extraction**: if `P.HasConvexIndependentBeliefs` fails and
`Ω` has at least two outcomes, there exists a nonnegative valuation profile (normalized to `0` on
a status-quo outcome) on which no ex-post efficient, BIC, interim-IR direct mechanism extracts the
full surplus. -/
theorem exists_nonneg_val_not_exists_isBIC_of_not_hasConvexIndependentBeliefs
    {P : CorrelatedPrior ι T} (hP : ¬ P.HasConvexIndependentBeliefs) {Ω : Type*}
    [Nontrivial Ω] :
    ∃ val : (∀ i, T i → Ω → ℝ),
      (∀ i ti ω, 0 ≤ val i ti ω) ∧
      (∃ ω₀, ∀ i ti, val i ti ω₀ = 0) ∧
      ¬ ∃ D : IndirectMechanism ι T Ω,
          D.IsExPostEfficient val ∧
          P.IsBIC val D ∧
          P.IsInterimIR val D ∧
          P.ExtractsFullSurplus val D := by
  classical
  rw [hasConvexIndependentBeliefs_iff] at hP
  push Not at hP
  obtain ⟨i₀, ti₀, hmem⟩ := hP
  obtain ⟨w, hw, hcomb⟩ := (P.condBelief_mem_convexHull_iff i₀ ti₀).1 hmem
  obtain ⟨ω₀, ω₁, hω⟩ := exists_pair_ne Ω
  obtain ⟨val, hnn, h0, hval_i₀, hout_of_eff⟩ := IndirectMechanism.exists_singleAgentVal (T := T)
    i₀ hω (fun ti => if ti = ti₀ then 1 else 2) (fun _ => by split_ifs <;> norm_num)
  refine ⟨val, hnn, ⟨ω₀, h0⟩, ?_⟩
  rintro ⟨D, hEff, hBIC, hIR, hExt⟩
  have hzero := (P.extractsFullSurplus_iff_forall_interimUtility_eq_zero hIR).1 hExt
  have hrent := P.le_interimUtility_add_sum_of_convexComb hBIC hw.nonneg hcomb
  simp only [hzero, mul_zero, sum_const_zero, zero_add, hout_of_eff D hEff, hval_i₀,
    ↓reduceIte] at hrent
  have h1 : (∑ ti' : {ti' : T i₀ // ti' ≠ ti₀}, w ti' *
      ∑ t_opp : OppProfile T i₀, P.condBelief i₀ ti'.1 t_opp *
        ((if ti'.1 = ti₀ then (1 : ℝ) else 2) - 1)) = 1 := by
    have hcongr : ∀ ti' : {ti' : T i₀ // ti' ≠ ti₀},
        (∑ t_opp : OppProfile T i₀, P.condBelief i₀ ti'.1 t_opp *
          ((if ti'.1 = ti₀ then (1 : ℝ) else 2) - 1)) = 1 := fun ti' => by
      simpa only [ite_eq_right ti'.2, show (2 : ℝ) - 1 = 1 by norm_num, mul_one] using
        P.sum_condBelief_eq_one i₀ ti'.1
    simpa only [hcongr, mul_one] using hw.sum_eq_one
  linarith

/-- **Crémer–McLean Bayesian characterization** ([CremerMcLean1988]): for any finite outcome space
`Ω` with at least two outcomes, `P.HasConvexIndependentBeliefs` holds if and only if every
nonnegative valuation profile admits an ex-post efficient, BIC, interim-IR direct mechanism
extracting the full surplus. -/
theorem hasConvexIndependentBeliefs_iff_forall_exists_isBIC (P : CorrelatedPrior ι T)
    (Ω : Type*) [Finite Ω] [Nontrivial Ω] :
    P.HasConvexIndependentBeliefs ↔
      ∀ val : (∀ i, T i → Ω → ℝ), (∀ i ti ω, 0 ≤ val i ti ω) →
        ∃ D : IndirectMechanism ι T Ω,
          D.IsExPostEfficient val ∧
          P.IsBIC val D ∧
          P.IsInterimIR val D ∧
          P.ExtractsFullSurplus val D := by
  refine ⟨fun hP val _ => ?_, fun H => ?_⟩
  · obtain ⟨D, hEff, -, hBIC, hIR, hExt, -⟩ :=
      hP.exists_isBIC_interimIR_extractsFullSurplus val
    exact ⟨D, hEff, hBIC, hIR, hExt⟩
  · by_contra hP
    obtain ⟨val, hnonneg, -, hno⟩ :=
      exists_nonneg_val_not_exists_isBIC_of_not_hasConvexIndependentBeliefs (Ω := Ω) hP
    exact hno (H val hnonneg)

/-! ### Independent product priors and impossibility of universal full extraction -/

omit [∀ i, Fintype (T i)] in
private theorem prod_extendProfile (μ : ∀ i, T i → ℝ) (i : ι) (ti : T i)
    (t_opp : OppProfile T i) :
    (∏ j, μ j (extendProfile i ti t_opp j)) =
      μ i ti * ∏ j : {j : ι // j ≠ i}, μ j.1 (t_opp j) := by
  rw [← mul_prod_erase _ _ (mem_univ i), extendProfile_self]
  congr 1
  rw [prod_subtype (p := fun j => j ≠ i) (univ.erase i)
    (fun j => by simp only [mem_erase, mem_univ, and_true])]
  refine prod_congr rfl fun j _ => ?_
  rw [extendProfile_of_ne j.2]

private theorem sum_oppProfile_prod {μ : ∀ i, T i → ℝ} (hμ : ∀ i, IsMixedStrategy (μ i))
    (i : ι) (ti : T i) :
    ∑ t_opp : OppProfile T i, (∏ j, μ j (extendProfile i ti t_opp j)) = μ i ti := by
  simp_rw [prod_extendProfile, ← mul_sum,
    ← Fintype.prod_sum (fun j : {j : ι // j ≠ i} => μ j.1)]
  have hprod1 : (∏ j : {j : ι // j ≠ i}, ∑ tj : T j.1, μ j.1 tj) = 1 :=
    prod_eq_one fun j _ => (hμ j.1).sum_eq_one
  rw [hprod1, mul_one]

/-- The independent product prior `∏ i, μ i (t i)` formed from strictly positive individual type
distributions `μ : ∀ i, T i → ℝ`. -/
def product (μ : ∀ i, T i → ℝ) (hμ : ∀ i, IsMixedStrategy (μ i))
    (hpos : ∀ i (ti : T i), 0 < μ i ti) : CorrelatedPrior ι T where
  prob t := ∏ i, μ i (t i)
  prob_nonneg t := prod_nonneg fun i _ => (hμ i).nonneg (t i)
  sum_prob_eq_one := by
    rw [← Fintype.prod_sum μ]
    exact prod_eq_one fun i _ => (hμ i).sum_eq_one
  sum_prob_extendProfile_pos i ti := by
    rw [sum_oppProfile_prod hμ i ti]
    exact hpos i ti

@[simp]
theorem product_prob (μ : ∀ i, T i → ℝ) (hμ : ∀ i, IsMixedStrategy (μ i))
    (hpos : ∀ i (ti : T i), 0 < μ i ti) (t : ∀ i, T i) :
    (product μ hμ hpos).prob t = ∏ i, μ i (t i) := by
  rfl

@[simp]
theorem product_marginal (μ : ∀ i, T i → ℝ) (hμ : ∀ i, IsMixedStrategy (μ i))
    (hpos : ∀ i (ti : T i), 0 < μ i ti) (i : ι) (ti : T i) :
    (product μ hμ hpos).marginal i ti = μ i ti :=
  sum_oppProfile_prod hμ i ti

/-- Under an independent product prior, agent `i`'s conditional belief `∏_{j ≠ i} μⱼ(tⱼ)` does not
depend on `i`'s own type `ti`. -/
@[simp]
theorem product_condBelief (μ : ∀ i, T i → ℝ) (hμ : ∀ i, IsMixedStrategy (μ i))
    (hpos : ∀ i (ti : T i), 0 < μ i ti) (i : ι) (ti : T i) (t_opp : OppProfile T i) :
    (product μ hμ hpos).condBelief i ti t_opp =
      ∏ j : {j : ι // j ≠ i}, μ j.1 (t_opp j) := by
  rw [condBelief_apply, product_marginal, product_prob, prod_extendProfile,
    mul_div_cancel_left₀ _ (hpos i ti).ne']

/-- When at least one agent `i₀` has two distinct types, an independent product prior fails
`HasConvexIndependentBeliefs` because all rows of `condBelief i₀` coincide. -/
theorem not_hasConvexIndependentBeliefs_product (μ : ∀ i, T i → ℝ)
    (hμ : ∀ i, IsMixedStrategy (μ i)) (hpos : ∀ i (ti : T i), 0 < μ i ti)
    {i₀ : ι} [Nontrivial (T i₀)] :
    ¬ (product μ hμ hpos).HasConvexIndependentBeliefs := by
  intro hConv
  obtain ⟨ti₀, ti₁, hne⟩ := exists_pair_ne (T i₀)
  have hrow : (product μ hμ hpos).condBelief i₀ ti₀ =
      (product μ hμ hpos).condBelief i₀ ti₁ := by
    funext t_opp
    simp only [product_condBelief]
  exact hne ((hConv i₀).injective hrow)

/-- Under an independent product prior, any agent with at least two types also refutes
`HasFullBeliefRank`. -/
theorem not_hasFullBeliefRank_product (μ : ∀ i, T i → ℝ)
    (hμ : ∀ i, IsMixedStrategy (μ i)) (hpos : ∀ i (ti : T i), 0 < μ i ti)
    {i₀ : ι} [Nontrivial (T i₀)] :
    ¬ (product μ hμ hpos).HasFullBeliefRank :=
  fun hRank => not_hasConvexIndependentBeliefs_product μ hμ hpos (i₀ := i₀)
    hRank.hasConvexIndependentBeliefs

/-- **Independent-prior impossibility corollary**: under an independent product prior with at least
one nontrivial type space and at least two outcomes, universal BIC + interim-IR + ex-post efficient
full surplus extraction is impossible. -/
theorem exists_nonneg_val_not_exists_isBIC_product (μ : ∀ i, T i → ℝ)
    (hμ : ∀ i, IsMixedStrategy (μ i)) (hpos : ∀ i (ti : T i), 0 < μ i ti)
    {i₀ : ι} [Nontrivial (T i₀)] {Ω : Type*} [Nontrivial Ω] :
    ∃ val : (∀ i, T i → Ω → ℝ),
      (∀ i ti ω, 0 ≤ val i ti ω) ∧
      (∃ ω₀, ∀ i ti, val i ti ω₀ = 0) ∧
      ¬ ∃ D : IndirectMechanism ι T Ω,
          D.IsExPostEfficient val ∧
          (product μ hμ hpos).IsBIC val D ∧
          (product μ hμ hpos).IsInterimIR val D ∧
          (product μ hμ hpos).ExtractsFullSurplus val D :=
  exists_nonneg_val_not_exists_isBIC_of_not_hasConvexIndependentBeliefs
    (not_hasConvexIndependentBeliefs_product μ hμ hpos (i₀ := i₀))

end CorrelatedPrior

end Cslib.GameTheory
