/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.GameTheory.Reputation.RepeatedPD
public import CslibFrontier.GameTheory.Reputation.PeerPrediction
public import CslibFrontier.GameTheory.Reputation.Sybilproof
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Non-vacuous boundary tests for NRTV Chapter 27 (Reputation Systems)

Exercises the definitions, characterizations, and subtle model boundaries across:
* `CslibFrontier.GameTheory.Reputation.RepeatedPD` (§§27.2–27.3, Exercises 27.1–27.5),
* `CslibFrontier.GameTheory.Reputation.PeerPrediction` (§27.4, Proposition 1, Exercise 27.6), and
* `CslibFrontier.GameTheory.Reputation.Sybilproof` (§27.5, Theorems 27.5 & 27.7–27.9, Figure 27.2).
-/

public section

namespace CslibFrontierTests.ReputationNRTV

open Finset
open scoped ENNReal
open Cslib.GameTheory Cslib.GameTheory.Reputation

/-! ## 1. Repeated Prisoner's Dilemma, whitewashing, entry fees, and Pay-Your-Dues -/

/-- Exercise 27.1 witness: normalized constant stream `1` at `δ = 3 / 4` equals `1`. -/
theorem test_discountedPayoff_const :
    discountedPayoff (3 / 4 : ℝ) (fun _ => (1 : ℝ)) = 1 :=
  discountedPayoff_const (by norm_num) (by norm_num) 1

/-- Grim trigger SPNE boundary: `δ = 1 / 2` and `3 / 5` succeed, whereas `2 / 5` fails. -/
theorem test_grim_spne_boundaries :
    IsSPNE (1 / 2) grim grim ∧
    IsSPNE (3 / 5) grim grim ∧
    ¬ IsSPNE (2 / 5) grim grim := by
  refine ⟨?_, ?_, ?_⟩
  · rw [isSPNE_grim_iff (by norm_num) (by norm_num)]
  · rw [isSPNE_grim_iff (by norm_num) (by norm_num)]; norm_num
  · rw [isSPNE_grim_iff (by norm_num) (by norm_num)]; norm_num

/-- Exercise 27.2 knife-edge refinement: under NRTV's stage payoffs `(1, 2, 0, -1)`, `(TFT, TFT)`
holds at `δ = 1 / 2` and fails strictly below (`1 / 3`) and strictly above (`3 / 4`). -/
theorem test_titForTat_knife_edge :
    IsSPNE (1 / 2) titForTat₁ titForTat₂ ∧
    ¬ IsSPNE (1 / 3) titForTat₁ titForTat₂ ∧
    ¬ IsSPNE (3 / 4) titForTat₁ titForTat₂ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [isSPNE_titForTat_iff (by norm_num) (by norm_num)]
  · exact not_isSPNE_titForTat_of_ne (by norm_num) (by norm_num) (by norm_num)
  · exact not_isSPNE_titForTat_of_ne (by norm_num) (by norm_num) (by norm_num)

/-- Exercise 27.3 witness: Naive-Grim fails SPNE even at `δ = 99 / 100`. -/
theorem test_not_isSPNE_naiveGrim :
    ¬ IsSPNE (99 / 100) naiveGrim₁ naiveGrim₂ :=
  not_isSPNE_naiveGrim (by norm_num) (by norm_num)

/-- Exercise 27.5 witness: with `N = 9` opponents (`10` players), `δ = 9 / 10` sustains
Personalized-Grim while `δ = 4 / 5` does not. -/
theorem test_personalizedGrim_threshold :
    personalizedGrimDevPayoff (9 / 10) 9 ≤ 1 ∧
    ¬ (personalizedGrimDevPayoff (4 / 5) 9 ≤ 1) := by
  constructor
  · rw [personalizedGrim_incentive_iff (by norm_num) (by norm_num) (by omega)]
    norm_num
  · rw [personalizedGrim_incentive_iff (by norm_num) (by norm_num) (by omega)]
    norm_num

/-- Section 27.3 entry-fee threshold `f ≥ 1 / δ`: at `δ = 2 / 3`, fee `3 / 2` deters both one-shot
and perpetual whitewashing, whereas `7 / 5` fails both. -/
theorem test_entryFee_whitewashing_boundaries :
    oneShotWhitewashPayoff (2 / 3) (3 / 2) ≤ honestEntryPayoff (2 / 3) (3 / 2) ∧
    perpetualWhitewashPayoff (2 / 3) (3 / 2) ≤ honestEntryPayoff (2 / 3) (3 / 2) ∧
    ¬ (oneShotWhitewashPayoff (2 / 3) (7 / 5) ≤ honestEntryPayoff (2 / 3) (7 / 5)) ∧
    ¬ (perpetualWhitewashPayoff (2 / 3) (7 / 5) ≤ honestEntryPayoff (2 / 3) (7 / 5)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [entryFee_deters_whitewashing_iff (by norm_num) (by norm_num)]; norm_num
  · rw [entryFee_deters_perpetual_whitewashing_iff (by norm_num) (by norm_num)]; norm_num
  · rw [entryFee_deters_whitewashing_iff (by norm_num) (by norm_num)]; norm_num
  · rw [entryFee_deters_perpetual_whitewashing_iff (by norm_num) (by norm_num)]; norm_num

/-- Exercise 27.4 Pay-Your-Dues (`PYD`) boundaries: weak dominance at `δ = 1 / 2`, strict dominance
at `δ = 3 / 4`, failure at `δ = 1 / 3`, veteran–newcomer gap `= 2`, and newcomer welfare
`1 ∈ (0, 2)`. -/
theorem test_pyd_boundaries :
    (∀ s ∈ ({ReputationStanding.newcomer, .goodVeteran} : Set ReputationStanding),
      ∀ (partner : ReputationStanding) (a : PDAction) (w : Bool),
        (1 - (1 / 2 : ℝ)) * pdPayoff a (pydAction partner s) +
            (1 / 2) * pydContValue (1 / 2) (pydNextStanding s partner a w) ≤
          (1 - (1 / 2 : ℝ)) * pdPayoff (pydAction s partner) (pydAction partner s) +
            (1 / 2) * pydContValue (1 / 2)
              (pydNextStanding s partner (pydAction s partner) false)) ∧
    ¬ (∀ s ∈ ({ReputationStanding.newcomer, .goodVeteran} : Set ReputationStanding),
      ∀ (partner : ReputationStanding) (a : PDAction) (w : Bool),
        (1 - (1 / 3 : ℝ)) * pdPayoff a (pydAction partner s) +
            (1 / 3) * pydContValue (1 / 3) (pydNextStanding s partner a w) ≤
          (1 - (1 / 3 : ℝ)) * pdPayoff (pydAction s partner) (pydAction partner s) +
            (1 / 3) * pydContValue (1 / 3)
              (pydNextStanding s partner (pydAction s partner) false)) ∧
    ((1 - (3 / 4 : ℝ)) * pdPayoff .defect (pydAction .goodVeteran .newcomer) +
        (3 / 4) * pydContValue (3 / 4) (pydNextStanding .newcomer .goodVeteran .defect true) <
      (1 - (3 / 4 : ℝ)) * pdPayoff .cooperate (pydAction .goodVeteran .newcomer) +
        (3 / 4) * pydContValue (3 / 4)
          (pydNextStanding .newcomer .goodVeteran .cooperate false)) ∧
    (pdPayoff (pydAction .goodVeteran .goodVeteran) (pydAction .goodVeteran .goodVeteran) -
      pdPayoff (pydAction .newcomer .goodVeteran) (pydAction .goodVeteran .newcomer) = 2) ∧
    (pdWelfare .defect .defect <
        pdWelfare (pydAction .goodVeteran .newcomer) (pydAction .newcomer .goodVeteran) ∧
      pdWelfare (pydAction .goodVeteran .newcomer) (pydAction .newcomer .goodVeteran) = 1 ∧
      pdWelfare (pydAction .goodVeteran .newcomer) (pydAction .newcomer .goodVeteran) <
        pdWelfare .cooperate .cooperate) := by
  refine ⟨?_, ?_, ?_, pyd_goodVeteran_vs_newcomer_gap, pyd_newcomer_welfare_bounds⟩
  · rw [pyd_incentive_iff (by norm_num) (by norm_num)]
  · rw [pyd_incentive_iff (by norm_num) (by norm_num)]; norm_num
  · exact pyd_strict_incentive_of_gt_half (by norm_num) (by norm_num) .newcomer .goodVeteran
      (Or.inl rfl) rfl true

/-! ## 2. Peer prediction (NRTV §27.4.1–27.4.2, MRZ 2005) -/

/-- Exact binary Bayesian peer-prediction model from [FriedmanResnickSami2007, §27.4.1, pp. 685–686]
(`0 = H / h`, `1 = L / l`): uniform prior `1 / 2`, `f(h | H) = 17 / 20`, `f(h | L) = 9 / 20`. -/
noncomputable def nrtvPeerModel : PeerPredictionModel (Fin 2) (Fin 2) where
  prior _ := 1 / 2
  isMixedStrategy_prior := isMixedStrategy_iff.mpr ⟨fun _ => by norm_num, by simp⟩
  prior_pos _ := by norm_num
  likelihood
    | 0, 0 => 17 / 20
    | 0, 1 => 3 / 20
    | 1, 0 => 9 / 20
    | 1, 1 => 11 / 20
  isMixedStrategy_likelihood θ := isMixedStrategy_iff.mpr
    ⟨fun s => by fin_cases θ <;> fin_cases s <;> norm_num,
     by fin_cases θ <;> simp [Fin.sum_univ_two] <;> norm_num⟩
  likelihood_pos θ s := by fin_cases θ <;> fin_cases s <;> norm_num

/-- Checks the exact rational posteriors of [FriedmanResnickSami2007, §27.4.1, p. 686]:
`Pr(h) = 13/20`, `Pr(l) = 7/20`, `Pr(S^j = h | S^i = l) = 15/28` (`≈ 0.54`),
`Pr(S^j = h | S^i = h) = 37/52` (`≈ 0.71`), `Pr(S^j = l | S^i = l) = 13/28`, and
`Pr(S^j = l | S^i = h) = 15/52`. -/
theorem test_nrtvPeerModel_posteriors :
    nrtvPeerModel.signalProb 0 = 13 / 20 ∧
    nrtvPeerModel.signalProb 1 = 7 / 20 ∧
    nrtvPeerModel.peerPosterior 1 0 = 15 / 28 ∧
    nrtvPeerModel.peerPosterior 0 0 = 37 / 52 ∧
    nrtvPeerModel.peerPosterior 1 1 = 13 / 28 ∧
    nrtvPeerModel.peerPosterior 0 1 = 15 / 52 := by
  have heval : ∀ s s' : Fin 2, nrtvPeerModel.peerPosterior s s' =
      ∑ θ : Fin 2, (nrtvPeerModel.prior θ * nrtvPeerModel.likelihood θ s /
        (∑ θ' : Fin 2, nrtvPeerModel.prior θ' * nrtvPeerModel.likelihood θ' s)) *
          nrtvPeerModel.likelihood θ s' := fun _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [PeerPredictionModel.signalProb, nrtvPeerModel, Fin.sum_univ_two]; norm_num
  · simp [PeerPredictionModel.signalProb, nrtvPeerModel, Fin.sum_univ_two]; norm_num
  · rw [heval]; simp [nrtvPeerModel, Fin.sum_univ_two]; norm_num
  · rw [heval]; simp [nrtvPeerModel, Fin.sum_univ_two]; norm_num
  · rw [heval]; simp [nrtvPeerModel, Fin.sum_univ_two]; norm_num
  · rw [heval]; simp [nrtvPeerModel, Fin.sum_univ_two]; norm_num

theorem test_nrtvPeerModel_stochasticallyRelevant : nrtvPeerModel.StochasticallyRelevant := by
  rw [PeerPredictionModel.stochasticallyRelevant_iff]
  intro s₁ s₂ hne
  use 0
  have hpost := test_nrtvPeerModel_posteriors
  fin_cases s₁ <;> fin_cases s₂
  · exact absurd rfl hne
  · change nrtvPeerModel.peerPosterior 0 0 ≠ nrtvPeerModel.peerPosterior 1 0
    linarith [hpost.2.2.1, hpost.2.2.2.1]
  · change nrtvPeerModel.peerPosterior 1 0 ≠ nrtvPeerModel.peerPosterior 0 0
    linarith [hpost.2.2.1, hpost.2.2.2.1]
  · exact absurd rfl hne

/-- Proposition 1 instantiated on `nrtvPeerModel` with 3 raters and cyclic reference `r i = i + 1`.
-/
theorem test_nrtvPeerModel_strictBNE :
    nrtvPeerModel.IsStrictBayesNashReporting
      (nrtvPeerModel.logPeerTransfer (fun i : Fin 3 => i + 1) 1 0)
      (PeerPredictionModel.truthfulStrategy (Fin 3)) :=
  nrtvPeerModel.truthful_isStrictBayesNash_logPeerTransfer
    (fun i => by fin_cases i <;> decide)
    test_nrtvPeerModel_stochasticallyRelevant zero_lt_one 0

/-- Effort elicitation + ex-post individual rationality instantiated on `nrtvPeerModel`
(`c = 1 / 10`). -/
theorem test_nrtvPeerModel_effort_scaling :
    ∃ α β : ℝ, 0 < α ∧
      (∀ s₀ : Fin 2,
        α * nrtvPeerModel.uninformedExpectedLogScore s₀ + β <
          α * nrtvPeerModel.informedExpectedLogScore + β - 1 / 10) ∧
      (∀ (r : Fin 3 → Fin 3) (x : Fin 3 → Fin 2) (i : Fin 3),
        0 ≤ nrtvPeerModel.logPeerTransfer r α β x i) := by
  obtain ⟨α, β, hα, heff, hexpost⟩ :=
    nrtvPeerModel.exists_scale_effort_incentive test_nrtvPeerModel_stochasticallyRelevant
      (c := 1 / 10) (by norm_num)
  exact ⟨α, β, hα, heff, fun r x i => hexpost r x i⟩

/-- Budget-balanced peer prediction on `Fin 3` (`r i = i + 1`, `b = Equiv.addRight 1`):
ex-post transfers sum to `0` and truthful reporting remains a strict Bayes–Nash equilibrium. -/
theorem test_nrtvPeerModel_budget_balanced_fin3 :
    let r : Fin 3 → Fin 3 := fun i => i + 1
    let b : Fin 3 ≃ Fin 3 := Equiv.addRight 1
    (∀ x : Fin 3 → Fin 2,
      ∑ i : Fin 3, nrtvPeerModel.balancedLogPeerTransfer r b 1 x i = 0) ∧
    nrtvPeerModel.IsStrictBayesNashReporting
      (nrtvPeerModel.balancedLogPeerTransfer r b 1)
      (PeerPredictionModel.truthfulStrategy (Fin 3)) := by
  intro r b
  refine ⟨fun x => nrtvPeerModel.sum_balancedLogPeerTransfer_eq_zero r b 1 x, ?_⟩
  exact nrtvPeerModel.truthful_isStrictBayesNash_balancedLogPeerTransfer
    (fun i => by fin_cases i <;> decide)
    (fun i => by fin_cases i <;> decide)
    (fun i => by fin_cases i <;> decide)
    test_nrtvPeerModel_stochasticallyRelevant zero_lt_one

/-- Boundary witness (`|I| ≥ 3` necessity for MRZ Equation `(4)`): on `Fin 2`, no reference map `r`
and balancing bijection `b` can simultaneously satisfy `r i ≠ i`, `b i ≠ i`, and `r (b i) ≠ i`. -/
theorem test_no_balanced_pairing_fin2 :
    ¬ ∃ (r : Fin 2 → Fin 2) (b : Fin 2 ≃ Fin 2),
      (∀ i, r i ≠ i) ∧ (∀ i, b i ≠ i) ∧ (∀ i, r (b i) ≠ i) := by
  rintro ⟨r, b, hr, hb, hrb⟩
  have hb0 : b 0 ≠ 0 := hb 0
  have hb0_eq : b 0 = 1 := by
    have hx : b 0 = 0 ∨ b 0 = 1 := by generalize b 0 = z; fin_cases z <;> simp
    exact hx.resolve_left hb0
  have hr1 : r 1 ≠ 1 := hr 1
  have hrb0 : r (b 0) ≠ 0 := hrb 0
  rw [hb0_eq] at hrb0
  have hy : r 1 = 0 ∨ r 1 = 1 := by generalize r 1 = z; fin_cases z <;> simp
  exact hy.elim hrb0 hr1

/-- Footnote 2 & Exercise 27.6 witnesses on `nrtvPeerModel`: both constant profiles (`0` and `1`)
are strict Bayes–Nash equilibria, and observing peer report `0` (`h`) when one's private signal is
`1` (`l`) makes misreporting `0` strictly profitable. -/
theorem test_nrtvPeerModel_uninformative_and_ex27_6 :
    nrtvPeerModel.IsStrictBayesNashReporting
      (nrtvPeerModel.logPeerTransfer (fun i : Fin 2 => i + 1) 1 0)
      (fun _ _ => 0) ∧
    nrtvPeerModel.IsStrictBayesNashReporting
      (nrtvPeerModel.logPeerTransfer (fun i : Fin 2 => i + 1) 1 0)
      (fun _ _ => 1) ∧
    nrtvPeerModel.logPeerTransfer (fun i : Fin 2 => i + 1) 1 0
        (Function.update (fun _ : Fin 2 => (0 : Fin 2)) 0 1) 0 <
      nrtvPeerModel.logPeerTransfer (fun i : Fin 2 => i + 1) 1 0
        (Function.update (fun _ : Fin 2 => (0 : Fin 2)) 0 0) 0 := by
  have hpost := test_nrtvPeerModel_posteriors
  refine ⟨?_, ?_, ?_⟩
  · refine nrtvPeerModel.constStrategy_isStrictBayesNash_logPeerTransfer
      (r := fun i : Fin 2 => i + 1) (fun i => by fin_cases i <;> decide)
      (fun s hs => ?_) zero_lt_one 0
    fin_cases s
    · exact absurd rfl hs
    · change nrtvPeerModel.peerPosterior 1 0 < nrtvPeerModel.peerPosterior 0 0
      linarith [hpost.2.2.1, hpost.2.2.2.1]
  · refine nrtvPeerModel.constStrategy_isStrictBayesNash_logPeerTransfer
      (r := fun i : Fin 2 => i + 1) (fun i => by fin_cases i <;> decide)
      (fun s hs => ?_) zero_lt_one 0
    fin_cases s
    · change nrtvPeerModel.peerPosterior 0 1 < nrtvPeerModel.peerPosterior 1 1
      linarith [hpost.2.2.2.2.1, hpost.2.2.2.2.2]
    · exact absurd rfl hs
  · refine nrtvPeerModel.observedPeer_misreport_strict_gain
      (r := fun i : Fin 2 => i + 1) (i := 0) (by decide) zero_lt_one 0
      (fun _ : Fin 2 => (0 : Fin 2)) (s_true := 1) (s_lie := 0) ?_
    linarith [hpost.2.2.1, hpost.2.2.2.1]

/-! ## 3. Transitive trust graphs, Max-Flow, and Pathrank (NRTV §27.5) -/

/-- Weighted in-degree global reputation `F_in(G, v) = ∑_u G.weight u v`: canonical nontrivial
isomorphism-invariant global reputation function. -/
def inDegreeRep : GlobalRepFn :=
  fun G v => ∑ u, G.weight u v

theorem test_inDegreeRep_symmetric_and_nontrivial :
    inDegreeRep.IsSymmetric ∧ inDegreeRep.IsNontrivial := by
  constructor
  · intro V V' _ _ _ _ G e x
    simp only [inDegreeRep, TrustGraph.relabel_weight, Equiv.symm_apply_apply]
    exact Fintype.sum_equiv e.symm _ (fun u => G.weight u x) fun _ => rfl
  · refine ⟨Fin 3, inferInstance, inferInstance, maxFlowCounterexampleGraph, 0, 1, ?_⟩
    simp [inDegreeRep, Fin.sum_univ_three, maxFlowCounterexampleGraph]

/-- Instantiates Theorems 27.7, 27.5, and §27.5.1 on `inDegreeRep`, and additionally exhibits a
concrete 2-Sybil internal-edge attack breaking value-sybilproofness of `inDegreeRep`. -/
theorem test_inDegreeRep_impossibilities :
    (∀ K, 1 ≤ K → ¬ inDegreeRep.IsKRankSybilproof K) ∧
    ¬ inDegreeRep.IsRankSybilproof ∧
    ¬ inDegreeRep.IsRankStrategyproof ∧
    ¬ inDegreeRep.IsValueSybilproof := by
  have ⟨hSym, hNon⟩ := test_inDegreeRep_symmetric_and_nontrivial
  refine ⟨fun K hK => GlobalRepFn.not_isKRankSybilproof_of_isSymmetric hK hSym hNon,
    GlobalRepFn.not_isRankSybilproof_of_isSymmetric hSym hNon,
    GlobalRepFn.not_isRankStrategyproof_of_isSymmetric hSym hNon, ?_⟩
  intro hVSP
  let G₀ : TrustGraph (Fin 2) := TrustGraph.empty (Fin 2)
  let G' : TrustGraph (Fin 3) :=
    { weight := fun i j => if i = 1 ∧ j = 2 then 5 else 0
      weight_nonneg := fun i j => by split_ifs <;> norm_num
      weight_diag := fun i => by fin_cases i <;> simp }
  let S : SybilStrategy G₀ 1 :=
    { Vertex := Fin 3
      instFintype := inferInstance
      instDecidableEq := inferInstance
      graph := G'
      collapse := fun
        | 0 => 0
        | 1 => 1
        | 2 => 1
      exists_collapse_eq := ⟨2, rfl⟩
      honestEmbed := fun _ => 0
      collapse_honestEmbed := fun ⟨w, hw⟩ => by
        fin_cases w
        · rfl
        · exact absurd rfl hw
      honestEmbed_collapse := fun x hx => by
        fin_cases x
        · rfl
        · exact absurd rfl hx
        · exact absurd rfl hx
      contract_eq := by
        ext i j
        by_cases hij : i = j
        · subst hij; rw [TrustGraph.weight_diag, G₀.weight_diag]
        · rw [TrustGraph.contract_weight_of_ne _ _ hij]
          fin_cases i <;> fin_cases j <;>
            simp [sum_filter, Fin.sum_univ_three, G', G₀, TrustGraph.empty] at hij ⊢ }
  have hmem : (2 : S.Vertex) ∈ S.sybils := S.mem_sybils.mpr rfl
  have hle := hVSP G₀ 1 S (2 : Fin 3) hmem
  change inDegreeRep G' 2 ≤ inDegreeRep G₀ 1 at hle
  simp [inDegreeRep, G', G₀, TrustGraph.empty] at hle
  linarith

/-- Exercises Max-Flow and Pathrank theorems and evaluates concrete Pathrank scores on
`maxFlowCounterexampleGraph` (`pathrankRep 0 0 = 1`, `pathrankRep 0 1 = 1 / 2`, and unreachable
`pathrankRep 1 0 = 0`). -/
theorem test_maxFlow_and_pathrank_witnesses :
    Cslib.Algorithms.Lean.MaxFlow.IsMaxRealFlow maxFlowCounterexampleGraph.weight 0 2
      (maxFlowRep maxFlowCounterexampleGraph 0 2) ∧
    SeededRepFn.IsValueSybilproof maxFlowRep ∧
    ¬ SeededRepFn.IsRankSybilproof maxFlowRep ∧
    (SeededRepFn.IsValueSybilproof fun G => pathrankRep G) ∧
    (SeededRepFn.IsRankSybilproof fun G => pathrankRep G) ∧
    (SeededRepFn.IsRankStrategyproof fun G => pathrankRep G) ∧
    (SeededRepFn.IsMonotonic fun G => pathrankRep G) ∧
    pathrankRep maxFlowCounterexampleGraph 0 0 = 1 ∧
    pathrankRep maxFlowCounterexampleGraph 0 1 = 1 / 2 ∧
    pathrankRep maxFlowCounterexampleGraph 1 0 = 0 := by
  refine ⟨isMaxRealFlow_maxFlowRep maxFlowCounterexampleGraph (by decide),
    isValueSybilproof_maxFlowRep, not_isRankSybilproof_maxFlowRep,
    isValueSybilproof_pathrankRep, isRankSybilproof_pathrankRep,
    isRankStrategyproof_pathrankRep, isMonotonic_pathrankRep,
    pathrankRep_self maxFlowCounterexampleGraph 0, ?_, ?_⟩
  · -- `pathrankDist maxFlowCounterexampleGraph 0 1 = 1`, hence `pathrankRep = 1 / 2`.
    have hd : pathrankDist maxFlowCounterexampleGraph 0 1 = 1 := by
      apply le_antisymm
      · refine (iInf₂_le [0, 1] ⟨rfl, rfl⟩).trans_eq ?_
        simp [invTrustLen, maxFlowCounterexampleGraph]
      · refine le_iInf₂ fun p hp => ?_
        rcases p with _ | ⟨x, _ | ⟨y, rest⟩⟩
        · simp at hp
        · simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hp
          exact absurd (hp.1.symm.trans hp.2) (by decide)
        · simp only [List.head?_cons, Option.some.injEq] at hp
          rcases hp with ⟨rfl, _⟩
          rw [walkInvTrustLen_cons_cons]
          have hstep : (1 : ℝ≥0∞) ≤ invTrustLen maxFlowCounterexampleGraph 0 y := by
            fin_cases y <;> simp [invTrustLen, maxFlowCounterexampleGraph]
          exact hstep.trans le_self_add
    simp [pathrankRep, hd]
    norm_num
  · -- Vertex `0` has zero incoming edges in `maxFlowCounterexampleGraph`, so `pathrankDist = ⊤`.
    have hno_in : ∀ p : List (Fin 3),
        ∀ x : Fin 3, x ≠ 0 → p.head? = some x → p.getLast? = some 0 →
          walkInvTrustLen maxFlowCounterexampleGraph p = ⊤ := by
      intro p
      induction p with
      | nil => intro _ _ hh; simp at hh
      | cons z rest ih =>
        intro x hx hh hl
        simp only [List.head?_cons, Option.some.injEq] at hh
        subst hh
        rcases rest with _ | ⟨y, rest'⟩
        · simp only [List.getLast?_singleton, Option.some.injEq] at hl
          exact absurd hl hx
        · rw [walkInvTrustLen_cons_cons]
          by_cases hy0 : y = 0
          · subst hy0
            have hw0 : maxFlowCounterexampleGraph.weight z 0 = 0 := by fin_cases z <;> rfl
            simp [invTrustLen, hw0]
          · have hrec := ih y hy0 rfl (by simpa using hl)
            simp [hrec]
    have hd_top : pathrankDist maxFlowCounterexampleGraph 1 0 = ⊤ :=
      top_unique (le_iInf₂ fun p hp => top_le_iff.mpr (hno_in p 1 (by decide) hp.1 hp.2))
    simp [pathrankRep, hd_top]

end CslibFrontierTests.ReputationNRTV
