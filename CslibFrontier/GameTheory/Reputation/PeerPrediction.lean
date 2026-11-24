/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.GameTheory.MixedStrategy
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Peer-Prediction Feedback Elicitation

Formalizes the **Miller–Resnick–Zeckhauser peer-prediction mechanism** for eliciting honest
subjective ratings without objective ground-truth verification, from Section 27.4 (Equations
`(27.1)`–`(27.2)`, Proposition 1, Footnote 2, and Exercise 27.6, pp. 684–688, 697) of Eric
Friedman, Paul Resnick, and Rahul Sami, *"Manipulation-Resistant Reputation Systems"*, Chapter 27
of *Algorithmic Game Theory* [FriedmanResnickSami2007], and Nolan Miller, Paul Resnick, and
Richard Zeckhauser, *"Eliciting Informative Feedback: The Peer-Prediction Method"*
[MillerResnickZeckhauser2005, §2, Propositions 1–2, Eq. `(4)`].

## Model and source mapping

* **Common-prior Bayesian signal model (`PeerPredictionModel Θ S`):** finite product quality types
  `Θ` with strictly positive prior `prior : Θ → ℝ` (`IsMixedStrategy prior`) and finite signals `S`
  with conditionally i.i.d. strictly positive likelihoods `likelihood : Θ → S → ℝ`
  (`∀ θ, IsMixedStrategy (likelihood θ)`) [FriedmanResnickSami2007, §27.4.1, p. 685].
* **Bayesian updating (`signalProb`, `typePosterior`, `peerPosterior`) and stochastic relevance
  (`StochasticallyRelevant`):** rater `i`'s signal `s_i` induces posterior `peerPosterior s_i` over
  any other rater's signal `S^j` (`r(i) ≠ i`). Stochastic relevance requires `peerPosterior` to be
  injective (`s₁ ≠ s₂ → peerPosterior s₁ ≠ peerPosterior s₂`) [MillerResnickZeckhauser2005, §2.1,
  p. 6; FriedmanResnickSami2007, p. 687].
* **Simultaneous reporting game (`interimTransfer`, `IsBayesNashReporting`,
  `IsStrictBayesNashReporting`):** exact formalization of Equation `(27.1)`
  [FriedmanResnickSami2007, p. 685] over arbitrary finite rater sets `I` under the conditional
  distribution `condSignalProb` of all other raters' signals given `S^i = s_i`.
* **Logarithmic peer-prediction transfers (`logPeerTransfer`, `balancedLogPeerTransfer`):**
  * **Proposition 1** (`truthful_isStrictBayesNash_logPeerTransfer`, [FriedmanResnickSami2007,
    p. 687; MillerResnickZeckhauser2005, Proposition 1]): for any reference map `r : I → I` with
    `∀ i, r i ≠ i` and scaling `α > 0`, stochastic relevance makes `truthfulStrategy` a *strict*
    Bayes–Nash equilibrium of `logPeerTransfer M r α β`.
  * **Effort elicitation (`exists_scale_effort_incentive`, [MillerResnickZeckhauser2005,
    Proposition 2]):** when `S` has at least two signals, stochastic relevance implies a strictly
    positive expected log-score information gain over any uninformed constant report, so for every
    signal-acquisition cost `c > 0` some `α > 0` and shift `β` ensure both strict incentive to
    acquire and report the signal and ex-post nonnegative transfers.
  * **Ex-post budget balance (`sum_balancedLogPeerTransfer_eq_zero`,
    `truthful_isStrictBayesNash_balancedLogPeerTransfer`,
    [MillerResnickZeckhauser2005, Eq. `(4)`]):**
    subtracting another rater `b(i)`'s score (`b i ≠ i`, `r (b i) ≠ i`, feasible whenever `|I| ≥ 3`)
    achieves exact ex-post budget balance while preserving strict Bayes–Nash truthfulness.
  * **Uninformative constant equilibria and observed-peer manipulation
    (`constStrategy_isStrictBayesNash_logPeerTransfer`, `observedPeer_misreport_strict_gain`):**
    Footnote 2 (p. 688) and Exercise 27.6 (p. 697).

## Main definitions

* `Cslib.GameTheory.Reputation.PeerPredictionModel`,
  `PeerPredictionModel.signalProb`, `PeerPredictionModel.typePosterior`,
  `PeerPredictionModel.peerPosterior`, `PeerPredictionModel.StochasticallyRelevant`
* `Cslib.GameTheory.Reputation.PeerPredictionModel.jointSignalProb`,
  `PeerPredictionModel.condSignalProb`, `PeerPredictionModel.interimTransfer`,
  `PeerPredictionModel.IsBayesNashReporting`, `PeerPredictionModel.IsStrictBayesNashReporting`,
  `PeerPredictionModel.truthfulStrategy`
* `Cslib.GameTheory.Reputation.PeerPredictionModel.logPeerTransfer`,
  `PeerPredictionModel.balancedLogPeerTransfer`

## Main results

* `Cslib.GameTheory.Reputation.PeerPredictionModel.truthful_isStrictBayesNash_logPeerTransfer`:
  NRTV Proposition 1 / MRZ Proposition 1.
* `Cslib.GameTheory.Reputation.PeerPredictionModel.exists_scale_effort_incentive`: MRZ
  Proposition 2 (effort elicitation with ex-post participation).
* `Cslib.GameTheory.Reputation.PeerPredictionModel.sum_balancedLogPeerTransfer_eq_zero` and
  `PeerPredictionModel.truthful_isStrictBayesNash_balancedLogPeerTransfer`: MRZ Equation `(4)`
  budget-balanced peer prediction.
* `Cslib.GameTheory.Reputation.PeerPredictionModel.constStrategy_isStrictBayesNash_logPeerTransfer`:
  NRTV §27.4.2 Footnote 2 uninformative constant equilibrium.
* `Cslib.GameTheory.Reputation.PeerPredictionModel.observedPeer_misreport_strict_gain`:
  Exercise 27.6 sequential/observed-reference manipulation.

## References

* [E. Friedman, P. Resnick, and R. Sami, *Manipulation-Resistant Reputation
  Systems*][FriedmanResnickSami2007]
* [N. Miller, P. Resnick, and R. Zeckhauser, *Eliciting Informative Feedback: The Peer-Prediction
  Method*][MillerResnickZeckhauser2005]
-/

public section

open Finset

namespace Cslib.GameTheory.Reputation

open Cslib.GameTheory

/-! ### Private Gibbs inequality for strictly positive distributions -/

private theorem sum_mul_log_lt_of_ne {S : Type*} [Fintype S] {p q : S → ℝ}
    (hp : IsMixedStrategy p) (hq : IsMixedStrategy q)
    (hp_pos : ∀ s, 0 < p s) (hq_pos : ∀ s, 0 < q s) (hpq : p ≠ q) :
    ∑ s, q s * Real.log (p s) < ∑ s, q s * Real.log (q s) := by
  obtain ⟨s₀, hs₀⟩ := Function.ne_iff.mp hpq
  have hle : ∀ s : S, q s * (Real.log (p s) - Real.log (q s)) ≤ p s - q s := by
    intro s
    have hqs : 0 < q s := hq_pos s
    have hdiv : 0 < p s / q s := div_pos (hp_pos s) hqs
    rw [← Real.log_div (hp_pos s).ne' hqs.ne']
    calc q s * Real.log (p s / q s)
        ≤ q s * (p s / q s - 1) :=
          mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hdiv) hqs.le
      _ = p s - q s := by rw [mul_sub, mul_div_cancel₀ _ hqs.ne', mul_one]
  have hlt : q s₀ * (Real.log (p s₀) - Real.log (q s₀)) < p s₀ - q s₀ := by
    have hqs : 0 < q s₀ := hq_pos s₀
    have hdiv : 0 < p s₀ / q s₀ := div_pos (hp_pos s₀) hqs
    have hne1 : p s₀ / q s₀ ≠ 1 := fun h => hs₀ ((div_eq_one_iff_eq hqs.ne').mp h)
    rw [← Real.log_div (hp_pos s₀).ne' hqs.ne']
    calc q s₀ * Real.log (p s₀ / q s₀)
        < q s₀ * (p s₀ / q s₀ - 1) :=
          mul_lt_mul_of_pos_left (Real.log_lt_sub_one_of_pos hdiv hne1) hqs
      _ = p s₀ - q s₀ := by rw [mul_sub, mul_div_cancel₀ _ hqs.ne', mul_one]
  have hsum : ∑ s, q s * (Real.log (p s) - Real.log (q s)) < ∑ s, (p s - q s) :=
    Finset.sum_lt_sum (fun s _ => hle s) ⟨s₀, mem_univ s₀, hlt⟩
  simp only [mul_sub, sum_sub_distrib, hp.sum_eq_one, hq.sum_eq_one, sub_self] at hsum
  linarith

/-! ### Common-prior Bayesian peer-rating model -/

/-- Common-prior Bayesian signal model for peer prediction [FriedmanResnickSami2007, §27.4.1,
p. 685; MillerResnickZeckhauser2005, §2, p. 4]. -/
structure PeerPredictionModel (Θ S : Type*) [Fintype Θ] [Fintype S] where
  /-- Common prior distribution `Pr_0(t)` over product quality types `t : Θ`. -/
  prior : Θ → ℝ
  /-- The prior is a valid probability vector. -/
  isMixedStrategy_prior : IsMixedStrategy prior
  /-- Every product quality type has strictly positive prior probability. -/
  prior_pos : ∀ θ, 0 < prior θ
  /-- Conditional signal likelihood `f(s | t) = Pr(S^i = s | t)`. -/
  likelihood : Θ → S → ℝ
  /-- Each conditional signal likelihood is a probability vector on `S`. -/
  isMixedStrategy_likelihood : ∀ θ, IsMixedStrategy (likelihood θ)
  /-- Every signal has strictly positive probability under every product type. -/
  likelihood_pos : ∀ θ s, 0 < likelihood θ s

namespace PeerPredictionModel

variable {Θ S : Type*} [Fintype Θ] [Fintype S] (M : PeerPredictionModel Θ S)

/-- Unconditional marginal probability `Pr(S^i = s) = ∑_t Pr_0(t) f(s | t)` of observing signal `s`
[FriedmanResnickSami2007, §27.4.1, p. 685]. -/
@[expose] def signalProb (s : S) : ℝ :=
  ∑ θ, M.prior θ * M.likelihood θ s

theorem signalProb_pos (s : S) : 0 < M.signalProb s :=
  M.isMixedStrategy_prior.dotProduct_pos fun θ => M.likelihood_pos θ s

theorem isMixedStrategy_signalProb : IsMixedStrategy M.signalProb := by
  refine isMixedStrategy_iff.mpr
    ⟨fun s => sum_nonneg fun θ _ => mul_nonneg (M.prior_pos θ).le (M.likelihood_pos θ s).le, ?_⟩
  simp only [signalProb]
  rw [sum_comm]
  calc ∑ θ, ∑ s, M.prior θ * M.likelihood θ s
      = ∑ θ, M.prior θ * ∑ s, M.likelihood θ s := by
        refine sum_congr rfl fun θ _ => (mul_sum _ _ _).symm
    _ = ∑ θ, M.prior θ := by
        refine sum_congr rfl fun θ _ => by rw [(M.isMixedStrategy_likelihood θ).sum_eq_one, mul_one]
    _ = 1 := M.isMixedStrategy_prior.sum_eq_one

/-- Posterior probability `Pr(t | S^i = s)` over product quality types given signal `s`
[FriedmanResnickSami2007, §27.4.1, p. 686]. -/
@[expose] noncomputable def typePosterior (s : S) (θ : Θ) : ℝ :=
  M.prior θ * M.likelihood θ s / M.signalProb s

theorem typePosterior_pos (s : S) (θ : Θ) : 0 < M.typePosterior s θ :=
  div_pos (mul_pos (M.prior_pos θ) (M.likelihood_pos θ s)) (M.signalProb_pos s)

theorem isMixedStrategy_typePosterior (s : S) :
    IsMixedStrategy (M.typePosterior s) := by
  refine isMixedStrategy_iff.mpr ⟨fun θ => (M.typePosterior_pos s θ).le, ?_⟩
  simp only [typePosterior, div_eq_mul_inv, ← sum_mul]
  exact mul_inv_cancel₀ (M.signalProb_pos s).ne'

/-- Posterior distribution `Pr(S^j = s' | S^i = s)` of a peer rater's signal `s'` given one's own
signal `s` [FriedmanResnickSami2007, §27.4.1, p. 686; MillerResnickZeckhauser2005, §2.1, p. 6]. -/
@[expose] noncomputable def peerPosterior (s s' : S) : ℝ :=
  ∑ θ, M.typePosterior s θ * M.likelihood θ s'

theorem peerPosterior_pos (s s' : S) : 0 < M.peerPosterior s s' :=
  (M.isMixedStrategy_typePosterior s).dotProduct_pos fun θ => M.likelihood_pos θ s'

theorem isMixedStrategy_peerPosterior (s : S) :
    IsMixedStrategy (M.peerPosterior s) := by
  refine isMixedStrategy_iff.mpr ⟨fun s' => (M.peerPosterior_pos s s').le, ?_⟩
  simp only [peerPosterior]
  rw [sum_comm]
  calc ∑ θ, ∑ s', M.typePosterior s θ * M.likelihood θ s'
      = ∑ θ, M.typePosterior s θ * ∑ s', M.likelihood θ s' :=
        sum_congr rfl fun θ _ => (mul_sum _ _ _).symm
    _ = ∑ θ, M.typePosterior s θ :=
        sum_congr rfl fun θ _ => by rw [(M.isMixedStrategy_likelihood θ).sum_eq_one, mul_one]
    _ = 1 := (M.isMixedStrategy_typePosterior s).sum_eq_one

theorem signalProb_mul_peerPosterior (s s' : S) :
    M.signalProb s * M.peerPosterior s s' =
      ∑ θ, M.prior θ * M.likelihood θ s * M.likelihood θ s' := by
  have hpos := (M.signalProb_pos s).ne'
  simp only [peerPosterior, typePosterior, mul_sum]
  refine sum_congr rfl fun θ _ => ?_
  field_simp [hpos]

/-- **Stochastic relevance** [MillerResnickZeckhauser2005, §2.1, p. 6; FriedmanResnickSami2007,
Proposition 1, p. 687]: distinct signals `s₁ ≠ s₂` induce distinct posterior distributions over a
peer rater's signal. -/
def StochasticallyRelevant : Prop :=
  Function.Injective M.peerPosterior

theorem stochasticallyRelevant_iff :
    M.StochasticallyRelevant ↔
      ∀ s₁ s₂ : S, s₁ ≠ s₂ → ∃ s' : S, M.peerPosterior s₁ s' ≠ M.peerPosterior s₂ s' := by
  constructor
  · intro hinj s₁ s₂ hne
    exact Function.ne_iff.mp fun heq => hne (hinj heq)
  · intro h s₁ s₂ heq
    by_contra hne
    obtain ⟨s', hs'⟩ := h s₁ s₂ hne
    exact hs' (congrFun heq s')

/-! ### Simultaneous reporting game (Equation `(27.1)`) -/

/-- Joint prior-likelihood probability `Pr(S = s_prof)` of a full rater signal profile `s_prof`. -/
def jointSignalProb {I : Type*} [Fintype I] (s_prof : I → S) : ℝ :=
  ∑ θ, M.prior θ * ∏ i : I, M.likelihood θ (s_prof i)

/-- Conditional probability `Pr(S = s_prof | S^i = s_i)` of the full signal profile given rater
`i`'s realized signal `s_i` [FriedmanResnickSami2007, §27.4.1, p. 685]. -/
noncomputable def condSignalProb [DecidableEq S] {I : Type*} [Fintype I] (i : I) (s_i : S)
    (s_prof : I → S) : ℝ :=
  if s_prof i = s_i then M.jointSignalProb s_prof / M.signalProb s_i else 0

private theorem sum_prod_likelihood_compl {I : Type*} [Fintype I] [DecidableEq I]
    (P : I → Prop) [DecidablePred P] (θ : Θ) :
    ∑ g : {j : I // P j} → S, ∏ j : {j : I // P j}, M.likelihood θ (g j) = 1 := by
  rw [← Fintype.prod_sum fun (_ : {j : I // P j}) s => M.likelihood θ s]
  exact prod_eq_one fun _ _ => (M.isMixedStrategy_likelihood θ).sum_eq_one

/-- Marginalizing `condSignalProb` onto a distinct reference rater `r ≠ i` recovers
`peerPosterior s_i`. -/
theorem sum_condSignalProb_mul_ref [DecidableEq S] {I : Type*} [Fintype I]
    [DecidableEq I] {i r : I} (hri : r ≠ i) (s_i : S) (g : S → ℝ) :
    ∑ s_prof : I → S, M.condSignalProb i s_i s_prof * g (s_prof r) =
      ∑ s_r : S, M.peerPosterior s_i s_r * g s_r := by
  let Rest := {j : I // j ≠ i ∧ j ≠ r}
  let equiv : (I → S) ≃ S × S × (Rest → S) :=
    { toFun := fun f => (f i, f r, fun j => f j.1)
      invFun := fun ⟨si, sr, rest⟩ j =>
        if hji : j = i then si else if hjr : j = r then sr else rest ⟨j, hji, hjr⟩
      left_inv := fun f => by
        ext j
        dsimp only
        split_ifs with h₁ h₂
        · subst h₁; rfl
        · subst h₂; rfl
        · rfl
      right_inv := fun ⟨si, sr, rest⟩ => by
        refine Prod.ext (by simp) (Prod.ext ?_ ?_)
        · simp [hri]
        · ext ⟨j, hji, hjr⟩
          simp [hji, hjr] }
  rw [Fintype.sum_equiv equiv _ fun p =>
    M.condSignalProb i s_i (equiv.symm p) * g ((equiv.symm p) r)]
  · simp only [Fintype.sum_prod_type]
    have hsi : ∀ p : S × S × (Rest → S), (equiv.symm p) i = p.1 := fun _ => by simp [equiv]
    have hsr : ∀ p : S × S × (Rest → S), (equiv.symm p) r = p.2.1 := fun _ => by simp [equiv, hri]
    simp_rw [condSignalProb, hsi, hsr, ite_mul, zero_mul]
    rw [sum_eq_single s_i (fun a _ ha => sum_eq_zero fun _ _ =>
      sum_eq_zero fun _ _ => by simp [ha]) (by simp)]
    simp only [↓reduceIte]
    refine sum_congr rfl fun s_r _ => ?_
    rw [← sum_mul]
    congr 1
    have hprod_split : ∀ (θ : Θ) (rest : Rest → S),
        ∏ j : I, M.likelihood θ ((equiv.symm (s_i, s_r, rest)) j) =
          M.likelihood θ s_i * M.likelihood θ s_r * ∏ j : Rest, M.likelihood θ (rest j) := by
      intro θ rest
      let f := equiv.symm (s_i, s_r, rest)
      have h1 : ∏ j : I, M.likelihood θ (f j) =
          M.likelihood θ (f i) * ∏ j ∈ univ.erase i, M.likelihood θ (f j) := by
        rw [← mul_prod_erase univ (fun j => M.likelihood θ (f j)) (mem_univ i)]
      have hr_mem : r ∈ univ.erase i := mem_erase.mpr ⟨hri, mem_univ r⟩
      have h2 : ∏ j ∈ univ.erase i, M.likelihood θ (f j) =
          M.likelihood θ (f r) * ∏ j ∈ (univ.erase i).erase r, M.likelihood θ (f j) := by
        rw [← mul_prod_erase (univ.erase i) (fun j => M.likelihood θ (f j)) hr_mem]
      have h3 : ∏ j ∈ (univ.erase i).erase r, M.likelihood θ (f j) =
          ∏ j : Rest, M.likelihood θ (rest j) := by
        have hset : (univ.erase i).erase r =
            (univ : Finset Rest).map ⟨Subtype.val, Subtype.val_injective⟩ := by
          ext j; simp [Rest, and_comm]
        rw [hset, prod_map]
        refine prod_congr rfl fun ⟨j, hj⟩ _ => ?_
        simp [f, equiv, hj.1, hj.2]
      have hfi : f i = s_i := by simp [f, equiv]
      have hfr : f r = s_r := by simp [f, equiv, hri]
      rw [h1, h2, h3, hfi, hfr, mul_assoc]
    have hsum_joint : ∑ rest : Rest → S, M.jointSignalProb (equiv.symm (s_i, s_r, rest)) =
        ∑ θ, M.prior θ * M.likelihood θ s_i * M.likelihood θ s_r := by
      simp only [jointSignalProb, hprod_split]
      rw [sum_comm]
      refine sum_congr rfl fun θ _ => ?_
      calc ∑ x : Rest → S,
            M.prior θ * (M.likelihood θ s_i * M.likelihood θ s_r * ∏ j : Rest, M.likelihood θ (x j))
          = (M.prior θ * M.likelihood θ s_i * M.likelihood θ s_r) *
              ∑ x : Rest → S, ∏ j : Rest, M.likelihood θ (x j) := by
            rw [mul_sum]
            refine sum_congr rfl fun x _ => by ring
        _ = M.prior θ * M.likelihood θ s_i * M.likelihood θ s_r := by
            rw [M.sum_prod_likelihood_compl (fun j => j ≠ i ∧ j ≠ r) θ, mul_one]
    have hpos_ne := (M.signalProb_pos s_i).ne'
    simp only [div_eq_mul_inv, ← sum_mul]
    rw [hsum_joint, ← M.signalProb_mul_peerPosterior s_i s_r]
    field_simp [hpos_ne]
  · intro x; simp only [Equiv.symm_apply_apply]

/-- Interim expected transfer `E_{S^{-i}}[τ_i(report, σ_{-i}(S^{-i})) | S^i = s_i]` of rater `i`
in Equation `(27.1)` [FriedmanResnickSami2007, §27.4.1, p. 685]. -/
noncomputable def interimTransfer [DecidableEq S] {I : Type*} [Fintype I] [DecidableEq I]
    (τ : (I → S) → I → ℝ) (σ : I → S → S) (i : I) (s_i report : S) : ℝ :=
  ∑ s_prof : I → S, M.condSignalProb i s_i s_prof *
    τ (Function.update (fun j => σ j (s_prof j)) i report) i

/-- Announcement strategy profile `σ` is a **Bayes–Nash equilibrium** of the simultaneous reporting
game with transfers `τ` (Equation `(27.1)`, [FriedmanResnickSami2007, p. 685]). -/
@[expose] def IsBayesNashReporting [DecidableEq S] {I : Type*} [Fintype I] [DecidableEq I]
    (τ : (I → S) → I → ℝ) (σ : I → S → S) : Prop :=
  ∀ (i : I) (s_i report : S),
    M.interimTransfer τ σ i s_i report ≤ M.interimTransfer τ σ i s_i (σ i s_i)

/-- Announcement strategy profile `σ` is a **strict Bayes–Nash equilibrium** of the simultaneous
reporting game with transfers `τ` [FriedmanResnickSami2007, §27.4.1, p. 686]. -/
@[expose] def IsStrictBayesNashReporting [DecidableEq S] {I : Type*} [Fintype I] [DecidableEq I]
    (τ : (I → S) → I → ℝ) (σ : I → S → S) : Prop :=
  ∀ (i : I) (s_i report : S), report ≠ σ i s_i →
    M.interimTransfer τ σ i s_i report < M.interimTransfer τ σ i s_i (σ i s_i)

theorem IsStrictBayesNashReporting.isBayesNashReporting [DecidableEq S] {I : Type*} [Fintype I]
    [DecidableEq I] {τ : (I → S) → I → ℝ} {σ : I → S → S}
    (h : M.IsStrictBayesNashReporting τ σ) :
    M.IsBayesNashReporting τ σ := by
  intro i s_i report
  by_cases hne : report = σ i s_i
  · subst hne; exact le_rfl
  · exact (h i s_i report hne).le

/-- Truthful signal announcement strategy `x_m^i = s_m` for every rater `i`
[FriedmanResnickSami2007, §27.4.1, p. 686]. -/
def truthfulStrategy (I : Type*) : I → S → S :=
  fun _ s => s

/-! ### Logarithmic peer-prediction mechanism (Proposition 1, effort scaling, budget balance) -/

/-- Positive-affine logarithmic peer-prediction transfer
`τ_i^*(x) = α * ln Pr(S^{r(i)} = x^{r(i)} | S^i = x^i) + β` (Equation `(27.2)` with affine
parameters `α, β`, [FriedmanResnickSami2007, §27.4.2, pp. 687–688;
MillerResnickZeckhauser2005, §2.1–2.3]). -/
noncomputable def logPeerTransfer {I : Type*} (r : I → I) (α β : ℝ) (x : I → S) (i : I) : ℝ :=
  α * Real.log (M.peerPosterior (x i) (x (r i))) + β

theorem interimTransfer_logPeerTransfer [DecidableEq S] {I : Type*} [Fintype I]
    [DecidableEq I] {r : I → I} (hr : ∀ i, r i ≠ i) (α β : ℝ) (σ : I → S → S) (i : I)
    (s_i report : S) :
    M.interimTransfer (M.logPeerTransfer r α β) σ i s_i report =
      ∑ s_r : S, M.peerPosterior s_i s_r *
        (α * Real.log (M.peerPosterior report (σ (r i) s_r)) + β) := by
  have hri : r i ≠ i := hr i
  simp only [interimTransfer, logPeerTransfer, Function.update_self,
    Function.update_of_ne hri]
  exact M.sum_condSignalProb_mul_ref hri s_i fun s_r =>
    α * Real.log (M.peerPosterior report (σ (r i) s_r)) + β

/-- **Proposition 1** ([FriedmanResnickSami2007, §27.4.2, p. 687];
[MillerResnickZeckhauser2005, Proposition 1, p. 7]): if `M` is stochastically relevant, every rater
`i` is scored against a distinct reference rater `r i ≠ i`, and `0 < α`, then truthful reporting by
all raters is a **strict Bayes–Nash equilibrium** of the simultaneous reporting game. -/
theorem truthful_isStrictBayesNash_logPeerTransfer [DecidableEq S] {I : Type*}
    [Fintype I] [DecidableEq I] {r : I → I} (hr : ∀ i, r i ≠ i) (hrel : M.StochasticallyRelevant)
    {α : ℝ} (hα : 0 < α) (β : ℝ) :
    M.IsStrictBayesNashReporting (M.logPeerTransfer r α β) (truthfulStrategy I) := by
  intro i s_i report hne
  rw [M.interimTransfer_logPeerTransfer hr α β (truthfulStrategy I) i s_i report,
    M.interimTransfer_logPeerTransfer hr α β (truthfulStrategy I) i s_i (truthfulStrategy I i s_i)]
  simp only [truthfulStrategy, mul_add, sum_add_distrib, ← sum_mul,
    (M.isMixedStrategy_peerPosterior s_i).sum_eq_one, one_mul]
  have hlt := sum_mul_log_lt_of_ne
    (M.isMixedStrategy_peerPosterior report) (M.isMixedStrategy_peerPosterior s_i)
    (M.peerPosterior_pos report) (M.peerPosterior_pos s_i)
    (fun heq => hne (hrel heq))
  have hmul : ∑ s_r : S, M.peerPosterior s_i s_r * (α * Real.log (M.peerPosterior report s_r)) <
      ∑ s_r : S, M.peerPosterior s_i s_r * (α * Real.log (M.peerPosterior s_i s_r)) := by
    have hpull : ∀ x : S,
        ∑ s_r : S, M.peerPosterior s_i s_r * (α * Real.log (M.peerPosterior x s_r)) =
          α * ∑ s_r : S, M.peerPosterior s_i s_r * Real.log (M.peerPosterior x s_r) := by
      intro x
      rw [mul_sum]
      exact sum_congr rfl fun s_r _ => by ring
    rw [hpull report, hpull s_i]
    exact mul_lt_mul_of_pos_left hlt hα
  linarith

/-- Ex-ante expected base log score `∑_s Pr(s) ∑_{s'} Pr(s' | s) ln Pr(s' | s)` when acquiring a
signal and reporting truthfully, assuming reference rater `r(i)` reports truthfully
[MillerResnickZeckhauser2005, §2.2, p. 9]. -/
noncomputable def informedExpectedLogScore : ℝ :=
  ∑ s : S, M.signalProb s *
    ∑ s' : S, M.peerPosterior s s' * Real.log (M.peerPosterior s s')

/-- Ex-ante expected base log score `∑_s Pr(s) ∑_{s'} Pr(s' | s) ln Pr(s' | s_0)` when skipping
signal acquisition and submitting a fixed uninformed report `s_0`
[MillerResnickZeckhauser2005, §2.2, p. 9]. -/
noncomputable def uninformedExpectedLogScore (s₀ : S) : ℝ :=
  ∑ s : S, M.signalProb s *
    ∑ s' : S, M.peerPosterior s s' * Real.log (M.peerPosterior s₀ s')

/-- **Effort elicitation and ex-post voluntary participation** ([MillerResnickZeckhauser2005,
Proposition 2 & §2.3, pp. 9–10]; [FriedmanResnickSami2007, §27.4.2, pp. 687–688]): when `S` has at
least two distinct signals and `M` is stochastically relevant, for every positive signal-acquisition
effort cost `0 < c` there exist `0 < α` and `β : ℝ` such that:
1. acquiring a signal at cost `c` and reporting truthfully strictly beats every uninformed fixed
   report `s₀ : S`, and
2. every ex-post transfer `logPeerTransfer M r α β x i` is nonnegative. -/
theorem exists_scale_effort_incentive [Nontrivial S]
    (hrel : M.StochasticallyRelevant) {c : ℝ} (hc : 0 < c) :
    ∃ α β : ℝ, 0 < α ∧
      (∀ s₀ : S, α * M.uninformedExpectedLogScore s₀ + β <
        α * M.informedExpectedLogScore + β - c) ∧
      ∀ {I : Type*} (r : I → I) (x : I → S) (i : I), 0 ≤ M.logPeerTransfer r α β x i := by
  classical
  have hgap_pos : ∀ s₀ : S, 0 < M.informedExpectedLogScore - M.uninformedExpectedLogScore s₀ := by
    intro s₀
    obtain ⟨s₁, hs₁⟩ := exists_ne s₀
    rw [informedExpectedLogScore, uninformedExpectedLogScore, ← sum_sub_distrib]
    refine sum_pos' (fun s _ => ?_) ⟨s₁, mem_univ s₁, ?_⟩
    · rw [← mul_sub]
      by_cases hs : s₀ = s
      · subst hs; simp
      · have hlt := sum_mul_log_lt_of_ne
          (M.isMixedStrategy_peerPosterior s₀) (M.isMixedStrategy_peerPosterior s)
          (M.peerPosterior_pos s₀) (M.peerPosterior_pos s)
          (fun heq => hs (hrel heq))
        exact mul_nonneg (M.signalProb_pos s).le (by linarith)
    · rw [← mul_sub]
      have hlt := sum_mul_log_lt_of_ne
        (M.isMixedStrategy_peerPosterior s₀) (M.isMixedStrategy_peerPosterior s₁)
        (M.peerPosterior_pos s₀) (M.peerPosterior_pos s₁)
        (fun heq => hs₁.symm (hrel heq))
      exact mul_pos (M.signalProb_pos s₁) (by linarith)
  obtain ⟨s_bar⟩ : Nonempty S := inferInstance
  let gapSet : Finset ℝ := univ.image fun s₀ : S =>
    M.informedExpectedLogScore - M.uninformedExpectedLogScore s₀
  have hgap_ne : gapSet.Nonempty := ⟨_, mem_image_of_mem _ (mem_univ s_bar)⟩
  let minGap : ℝ := gapSet.min' hgap_ne
  have hminGap : 0 < minGap := by
    obtain ⟨s₀, _, hmin_eq⟩ := mem_image.mp (min'_mem gapSet hgap_ne)
    linarith [hgap_pos s₀, show minGap = gapSet.min' hgap_ne from rfl]
  let α : ℝ := (c + 1) / minGap
  have hα : 0 < α := div_pos (by linarith) hminGap
  have hpair_mem : (s_bar, s_bar) ∈ (univ : Finset S) ×ˢ (univ : Finset S) :=
    mem_product.mpr ⟨mem_univ s_bar, mem_univ s_bar⟩
  let minLog : ℝ := ((univ ×ˢ univ).image fun p : S × S =>
    Real.log (M.peerPosterior p.1 p.2)).min'
      ⟨_, mem_image_of_mem _ hpair_mem⟩
  let β : ℝ := -α * minLog
  refine ⟨α, β, hα, fun s₀ => ?_, fun {I} r x i => ?_⟩
  · have hle : minGap ≤ M.informedExpectedLogScore - M.uninformedExpectedLogScore s₀ :=
      min'_le _ _ (mem_image_of_mem _ (mem_univ s₀))
    have hmul : c + 1 ≤ α * (M.informedExpectedLogScore - M.uninformedExpectedLogScore s₀) := by
      calc c + 1 = α * minGap := (div_mul_cancel₀ (c + 1) hminGap.ne').symm
        _ ≤ α * (M.informedExpectedLogScore - M.uninformedExpectedLogScore s₀) :=
          mul_le_mul_of_nonneg_left hle hα.le
    linarith
  · simp only [logPeerTransfer, β]
    have hmem : Real.log (M.peerPosterior (x i) (x (r i))) ∈
        (univ ×ˢ univ).image fun p : S × S => Real.log (M.peerPosterior p.1 p.2) :=
      mem_image.mpr ⟨(x i, x (r i)), mem_product.mpr ⟨mem_univ _, mem_univ _⟩, rfl⟩
    have hle : minLog ≤ Real.log (M.peerPosterior (x i) (x (r i))) := min'_le _ _ hmem
    have hmul := mul_le_mul_of_nonneg_left hle hα.le
    linarith

/-- **Budget-balanced peer-prediction transfer** (Equation `(4)` of
[MillerResnickZeckhauser2005, §2.3, p. 10]; [FriedmanResnickSami2007, §27.4.2, p. 688]):
rater `i` receives her own peer-prediction score minus the base score of rater `b i` under a
balancing bijection `b : I ≃ I`. -/
noncomputable def balancedLogPeerTransfer {I : Type*} (r : I → I) (b : I ≃ I) (α : ℝ)
    (x : I → S) (i : I) : ℝ :=
  M.logPeerTransfer r α 0 x i - M.logPeerTransfer r α 0 x (b i)

/-- Exact ex-post budget balance: for every announcement vector `x`, the sum of
`balancedLogPeerTransfer` across all raters is identically `0`
[MillerResnickZeckhauser2005, §2.3, Eq. `(4)`, p. 10]. -/
theorem sum_balancedLogPeerTransfer_eq_zero {I : Type*} [Fintype I] (r : I → I) (b : I ≃ I)
    (α : ℝ) (x : I → S) :
    ∑ i : I, M.balancedLogPeerTransfer r b α x i = 0 := by
  simp only [balancedLogPeerTransfer, sum_sub_distrib]
  rw [Equiv.sum_comp b fun j => M.logPeerTransfer r α 0 x j, sub_self]

/-- **Strict Bayes–Nash truthfulness of budget-balanced peer prediction**
([MillerResnickZeckhauser2005, §2.3, Eq. `(4)`, p. 10]): when `r i ≠ i`, `b i ≠ i`, and
`r (b i) ≠ i` for every rater `i` (satisfiable whenever `|I| ≥ 3`, e.g. by distinct cyclic shifts),
`truthfulStrategy` is a strict Bayes–Nash equilibrium of `balancedLogPeerTransfer`. -/
theorem truthful_isStrictBayesNash_balancedLogPeerTransfer [DecidableEq S]
    {I : Type*} [Fintype I] [DecidableEq I] {r : I → I} {b : I ≃ I} (hr : ∀ i, r i ≠ i)
    (hb : ∀ i, b i ≠ i) (hrb : ∀ i, r (b i) ≠ i) (hrel : M.StochasticallyRelevant)
    {α : ℝ} (hα : 0 < α) :
    M.IsStrictBayesNashReporting (M.balancedLogPeerTransfer r b α) (truthfulStrategy I) := by
  intro i s_i report hne
  have hsplit : ∀ a : S,
      M.interimTransfer (M.balancedLogPeerTransfer r b α) (truthfulStrategy I) i s_i a =
        M.interimTransfer (M.logPeerTransfer r α 0) (truthfulStrategy I) i s_i a -
          ∑ s_prof : I → S, M.condSignalProb i s_i s_prof *
            M.logPeerTransfer r α 0 (fun j => truthfulStrategy I j (s_prof j)) (b i) := by
    intro a
    simp only [interimTransfer, balancedLogPeerTransfer, mul_sub, sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun s_prof _ => ?_
    congr 1
    simp only [logPeerTransfer, Function.update_of_ne (hb i), Function.update_of_ne (hrb i)]
  rw [hsplit report, hsplit (truthfulStrategy I i s_i)]
  have hbase := M.truthful_isStrictBayesNash_logPeerTransfer hr hrel hα 0 i s_i report hne
  linarith

/-! ### Uninformative constant equilibria & sequential manipulation (Footnote 2 & Exercise 27.6) -/

/-- **Uninformative constant equilibrium** ([FriedmanResnickSami2007, §27.4.2, p. 688, Footnote 2]):
if signal `s₀` uniquely maximizes self-prediction `s ↦ peerPosterior s s₀` (which holds whenever
observing `s₀` strictly raises the posterior of `s₀` above every other signal's posterior of `s₀`),
then all raters constantly reporting `s₀` regardless of their signal is also a strict Bayes–Nash
equilibrium. -/
theorem constStrategy_isStrictBayesNash_logPeerTransfer [DecidableEq S]
    {I : Type*} [Fintype I] [DecidableEq I] {r : I → I} (hr : ∀ i, r i ≠ i) {s₀ : S}
    (hdiag : ∀ s : S, s ≠ s₀ → M.peerPosterior s s₀ < M.peerPosterior s₀ s₀)
    {α : ℝ} (hα : 0 < α) (β : ℝ) :
    M.IsStrictBayesNashReporting (M.logPeerTransfer r α β) (fun _ _ => s₀) := by
  intro i s_i report hne
  rw [M.interimTransfer_logPeerTransfer hr α β (fun _ _ => s₀) i s_i report,
    M.interimTransfer_logPeerTransfer hr α β (fun _ _ => s₀) i s_i s₀]
  simp only [← sum_mul, (M.isMixedStrategy_peerPosterior s_i).sum_eq_one, one_mul]
  have hlog : Real.log (M.peerPosterior report s₀) < Real.log (M.peerPosterior s₀ s₀) :=
    Real.log_lt_log (M.peerPosterior_pos report s₀) (hdiag report hne)
  linarith [mul_lt_mul_of_pos_left hlog hα]

/-- **Exercise 27.6** ([FriedmanResnickSami2007, p. 697]): if rater `i` observes reference rater
`r(i)`'s announcement `x (r i)` before submitting her own report and is still paid according to
`logPeerTransfer` (`0 < α`), then reporting `s_lie` yields strictly higher ex-post transfer than
reporting `s_true` whenever `peerPosterior s_true (x (r i)) < peerPosterior s_lie (x (r i))`. -/
theorem observedPeer_misreport_strict_gain {I : Type*} [DecidableEq I]
    {r : I → I} {i : I} (hri : r i ≠ i) {α : ℝ} (hα : 0 < α) (β : ℝ) (x : I → S)
    {s_true s_lie : S} (hlt : M.peerPosterior s_true (x (r i)) < M.peerPosterior s_lie (x (r i))) :
    M.logPeerTransfer r α β (Function.update x i s_true) i <
      M.logPeerTransfer r α β (Function.update x i s_lie) i := by
  simp only [logPeerTransfer, Function.update_self, Function.update_of_ne hri]
  have hlog := Real.log_lt_log (M.peerPosterior_pos s_true (x (r i))) hlt
  linarith [mul_lt_mul_of_pos_left hlog hα]

end PeerPredictionModel

end Cslib.GameTheory.Reputation
