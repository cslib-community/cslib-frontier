/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Analysis.Convex.FirstOrder
public import CslibFrontier.GameTheory.MixedStrategy
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Proper scoring rules and the Savage characterization

A *scoring rule* on a finite outcome space `Ω` assigns a real reward `S.score p ω` to a reported
probability distribution `p : Ω → ℝ` when outcome `ω : Ω` realizes
[FriedmanResnickSami2007, §27.4.2, pp. 686–687; GneitingRaftery2007]. Probability distributions are
represented by `Cslib.GameTheory.IsMixedStrategy`, forming the closed simplex `probSimplex Ω` and
its strictly positive interior `openProbSimplex Ω`.

A scoring rule is *proper* on a set `P` of distributions if reporting one's true belief `q ∈ P`
maximizes expected score `∑ ω, q ω * S.score p ω` over `p ∈ P`, and *strictly proper* on `P` if
`p = q` is the unique maximizer [FriedmanResnickSami2007, Definition 27.1, p. 686]. Real-valued
scoring rules such as the quadratic (Brier) score and spherical score are strictly proper on the
entire closed simplex `probSimplex Ω`, while the logarithmic score `ω ↦ Real.log (p ω)` is strictly
proper on `openProbSimplex Ω` (and, more generally, whenever the support of `q` is contained in
that of `p`, avoiding the real-valued `Real.log 0 = 0` convention at zero-probability reports).

Following [Savage1971] and [GneitingRaftery2007], every (strictly) proper scoring rule
on a convex set `P ⊆ probSimplex Ω` is characterized by a (strictly) convex potential
`G : (Ω → ℝ) → ℝ` together with a (strict) subgradient map `g : (Ω → ℝ) → Ω → ℝ` via
`S(p, ω) = G(p) + g(p)(ω) - p ⬝ᵥ g(p)`. The expected score loss of misreporting `p` under true
belief `q` equals the Bregman divergence `G(q) - G(p) - (q - p) ⬝ᵥ g(p)`. When `G` is Fréchet
differentiable within `P` with gradient `g(p)`, convexity (respectively strict convexity) of `G`
directly implies propriety (respectively strict propriety) of `savageScoringRule G g`.

## Main definitions

* `Cslib.GameTheory.PredictionMarket.probSimplex`: the closed probability simplex
  `{p : Ω → ℝ | IsMixedStrategy p}`.
* `Cslib.GameTheory.PredictionMarket.openProbSimplex`: the strictly positive probability simplex.
* `Cslib.GameTheory.PredictionMarket.ScoringRule`: a real-valued scoring rule on `Ω`.
* `Cslib.GameTheory.PredictionMarket.ScoringRule.expectedScore`: expected score under a true
  belief `q` for report `p`.
* `Cslib.GameTheory.PredictionMarket.ScoringRule.IsProperOn`,
  `Cslib.GameTheory.PredictionMarket.ScoringRule.IsStrictlyProperOn`: propriety and strict
  propriety on a domain `P` (with `IsProper` and `IsStrictlyProper` on `probSimplex Ω`).
* `Cslib.GameTheory.PredictionMarket.savageScoringRule`: the scoring rule induced by `(G, g)`.
* `Cslib.GameTheory.PredictionMarket.bregmanDivergence`: the Bregman divergence
  `G q - G p - (q - p) ⬝ᵥ g p`.
* `Cslib.GameTheory.PredictionMarket.quadraticScore`,
  `Cslib.GameTheory.PredictionMarket.brierScore`,
  `Cslib.GameTheory.PredictionMarket.logScore`,
  `Cslib.GameTheory.PredictionMarket.sphericalScore`: the canonical strictly proper scoring rules.

## Main results

* `Cslib.GameTheory.PredictionMarket.savageScoringRule_score_gap_eq_bregmanDivergence`: expected
  score gap equals Bregman divergence.
* `Cslib.GameTheory.PredictionMarket.isProperOn_iff_exists_savage`,
  `Cslib.GameTheory.PredictionMarket.isStrictlyProperOn_iff_exists_savage`: the Savage /
  Gneiting–Raftery characterization of proper and strictly proper scoring rules on a convex subset
  of the simplex [Savage1971; GneitingRaftery2007].
* `Cslib.GameTheory.PredictionMarket.isProperOn_savageScoringRule_of_convexOn`,
  `Cslib.GameTheory.PredictionMarket.isStrictlyProperOn_savageScoringRule_of_strictConvexOn`:
  differentiable convex / strictly convex potentials generate proper / strictly proper scoring
  rules.
* `Cslib.GameTheory.PredictionMarket.isStrictlyProper_quadraticScore`,
  `Cslib.GameTheory.PredictionMarket.isStrictlyProper_brierScore`,
  `Cslib.GameTheory.PredictionMarket.quadraticScore_bounds`: strict propriety and `[-1, 1]` bounds
  for the quadratic (Brier) scoring rule
  [Brier1950; FriedmanResnickSami2007, §27.4.2, pp. 686–687, Exercise 27.7, p. 697;
  GneitingRaftery2007].
* `Cslib.GameTheory.PredictionMarket.isStrictlyProperOn_logScore`,
  `Cslib.GameTheory.PredictionMarket.logScore_expectedScore_lt`: strict propriety of the
  logarithmic scoring rule [FriedmanResnickSami2007, §27.4.2, pp. 686–687; GneitingRaftery2007].
* `Cslib.GameTheory.PredictionMarket.isStrictlyProper_sphericalScore`: strict propriety of the
  spherical scoring rule [GneitingRaftery2007].

## References

* [G. W. Brier, *Verification of Forecasts Expressed in Terms of Probability*][Brier1950]
* [E. Friedman, P. Resnick, R. Sami, *Manipulation-Resistant Reputation Systems*,
  Chapter 27 of *Algorithmic Game Theory*][FriedmanResnickSami2007]
* [T. Gneiting, A. E. Raftery, *Strictly Proper Scoring Rules, Prediction, and
  Estimation*][GneitingRaftery2007]
* [L. J. Savage, *Elicitation of Personal Probabilities and Expectations*][Savage1971]
-/

public section

open Finset Matrix Set

namespace Cslib.GameTheory.PredictionMarket

section Simplex

variable {Ω : Type*} [Fintype Ω]

/-- The closed probability simplex over a finite outcome type `Ω`. -/
abbrev probSimplex (Ω : Type*) [Fintype Ω] : Set (Ω → ℝ) :=
  {p | IsMixedStrategy p}

/-- The open (strictly positive) probability simplex over a finite outcome type `Ω`. -/
abbrev openProbSimplex (Ω : Type*) [Fintype Ω] : Set (Ω → ℝ) :=
  {p | IsMixedStrategy p ∧ ∀ ω, 0 < p ω}

/-- The closed probability simplex is convex. -/
theorem convex_probSimplex : Convex ℝ (probSimplex Ω) := by
  intro p hp q hq a b ha hb hab
  refine isMixedStrategy_iff.2 ⟨fun ω => add_nonneg (mul_nonneg ha (hp.nonneg ω))
    (mul_nonneg hb (hq.nonneg ω)), ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum, hp.sum_eq_one,
    hq.sum_eq_one, mul_one, hab]

/-- The open probability simplex is convex. -/
theorem convex_openProbSimplex : Convex ℝ (openProbSimplex Ω) := by
  intro p hp q hq a b ha hb hab
  refine ⟨convex_probSimplex hp.1 hq.1 ha hb hab, fun ω => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases ha.eq_or_lt with rfl | ha'
  · have hb' : b = 1 := by linarith
    subst hb'
    simpa only [zero_mul, zero_add, one_mul] using hq.2 ω
  · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hp.2 ω)) (mul_nonneg hb (hq.2 ω).le)

end Simplex

section ScoringRuleCore

variable {Ω : Type*}

/-- A real-valued scoring rule on a finite outcome space `Ω`, mapping a reported probability
vector `p : Ω → ℝ` and realized outcome `ω : Ω` to a real score
[FriedmanResnickSami2007, §27.4.2, pp. 686–687]. -/
@[ext]
structure ScoringRule (Ω : Type*) where
  /-- The score awarded when reporting distribution `p` and outcome `ω` occurs. -/
  score : (Ω → ℝ) → Ω → ℝ

namespace ScoringRule

/-- Positive affine transformation of a scoring rule: `b * S(p, ω) + h(ω)`. -/
def affine (S : ScoringRule Ω) (b : ℝ) (h : Ω → ℝ) : ScoringRule Ω where
  score p ω := b * S.score p ω + h ω

@[simp]
theorem affine_score (S : ScoringRule Ω) (b : ℝ) (h : Ω → ℝ) (p : Ω → ℝ) (ω : Ω) :
    (S.affine b h).score p ω = b * S.score p ω + h ω := by
  rfl

variable [Fintype Ω] (S : ScoringRule Ω)

/-- The expected score under true belief distribution `q` when reporting distribution `p`. -/
def expectedScore (q p : Ω → ℝ) : ℝ :=
  ∑ ω, q ω * S.score p ω

@[simp]
theorem expectedScore_apply (q p : Ω → ℝ) : S.expectedScore q p = ∑ ω, q ω * S.score p ω := by
  rfl

theorem expectedScore_eq_dotProduct (q p : Ω → ℝ) : S.expectedScore q p = q ⬝ᵥ S.score p := by
  rfl

/-- Two scoring rules that agree at report `p` across all outcomes have equal expected scores at
report `p` under every belief `q`. -/
theorem expectedScore_congr {S₁ S₂ : ScoringRule Ω} {p : Ω → ℝ}
    (h : ∀ ω, S₁.score p ω = S₂.score p ω) (q : Ω → ℝ) :
    S₁.expectedScore q p = S₂.expectedScore q p :=
  sum_congr rfl fun ω _ => by rw [h ω]

/-- A scoring rule is *proper* on a set `P` of distributions if reporting one's true belief `q ∈ P`
maximizes expected score among all reports `p ∈ P`. -/
def IsProperOn (P : Set (Ω → ℝ)) : Prop :=
  ∀ q ∈ P, ∀ p ∈ P, S.expectedScore q p ≤ S.expectedScore q q

/-- A scoring rule is *strictly proper* on a set `P` of distributions if reporting one's true
belief `q ∈ P` is the unique maximizer of expected score among all reports `p ∈ P`
[FriedmanResnickSami2007, Definition 27.1, p. 686]. -/
def IsStrictlyProperOn (P : Set (Ω → ℝ)) : Prop :=
  ∀ q ∈ P, ∀ p ∈ P, p ≠ q → S.expectedScore q p < S.expectedScore q q

/-- A scoring rule is *proper* if it is proper on the full probability simplex `probSimplex Ω`. -/
abbrev IsProper : Prop :=
  S.IsProperOn (probSimplex Ω)

/-- A scoring rule is *strictly proper* if it is strictly proper on the full probability simplex
`probSimplex Ω`. -/
abbrev IsStrictlyProper : Prop :=
  S.IsStrictlyProperOn (probSimplex Ω)

theorem isProperOn_iff {S : ScoringRule Ω} {P : Set (Ω → ℝ)} :
    S.IsProperOn P ↔ ∀ q ∈ P, ∀ p ∈ P, S.expectedScore q p ≤ S.expectedScore q q := by
  rfl

theorem isStrictlyProperOn_iff {S : ScoringRule Ω} {P : Set (Ω → ℝ)} :
    S.IsStrictlyProperOn P ↔
      ∀ q ∈ P, ∀ p ∈ P, p ≠ q → S.expectedScore q p < S.expectedScore q q := by
  rfl

theorem IsProperOn.expectedScore_le {S : ScoringRule Ω} {P : Set (Ω → ℝ)}
    (h : S.IsProperOn P) {q p : Ω → ℝ} (hq : q ∈ P) (hp : p ∈ P) :
    S.expectedScore q p ≤ S.expectedScore q q :=
  h q hq p hp

theorem IsStrictlyProperOn.expectedScore_lt {S : ScoringRule Ω} {P : Set (Ω → ℝ)}
    (h : S.IsStrictlyProperOn P) {q p : Ω → ℝ} (hq : q ∈ P) (hp : p ∈ P) (hpq : p ≠ q) :
    S.expectedScore q p < S.expectedScore q q :=
  h q hq p hp hpq

/-- Strict propriety implies propriety on the same domain. -/
theorem IsStrictlyProperOn.isProperOn {S : ScoringRule Ω} {P : Set (Ω → ℝ)}
    (h : S.IsStrictlyProperOn P) : S.IsProperOn P := by
  intro q hq p hp
  by_cases hpq : p = q
  · subst hpq; exact le_rfl
  · exact (h q hq p hp hpq).le

/-- Propriety is preserved under restricting the domain of distributions. -/
theorem IsProperOn.mono {S : ScoringRule Ω} {P Q : Set (Ω → ℝ)} (h : S.IsProperOn P)
    (hQP : Q ⊆ P) : S.IsProperOn Q :=
  fun q hq p hp => h q (hQP hq) p (hQP hp)

/-- Strict propriety is preserved under restricting the domain of distributions. -/
theorem IsStrictlyProperOn.mono {S : ScoringRule Ω} {P Q : Set (Ω → ℝ)}
    (h : S.IsStrictlyProperOn P) (hQP : Q ⊆ P) : S.IsStrictlyProperOn Q :=
  fun q hq p hp hpq => h q (hQP hq) p (hQP hp) hpq

theorem expectedScore_affine (b : ℝ) (h : Ω → ℝ) (q p : Ω → ℝ) :
    (S.affine b h).expectedScore q p = b * S.expectedScore q p + q ⬝ᵥ h := by
  simp only [expectedScore_apply, affine_score, mul_add, sum_add_distrib, dotProduct, mul_sum]
  congr 1
  exact sum_congr rfl fun ω _ => by ring

/-- Nonnegative affine rescaling preserves propriety. -/
theorem IsProperOn.affine {S : ScoringRule Ω} {P : Set (Ω → ℝ)} (hS : S.IsProperOn P) {b : ℝ}
    (hb : 0 ≤ b) (h : Ω → ℝ) : (S.affine b h).IsProperOn P := by
  intro q hq p hp
  rw [expectedScore_affine, expectedScore_affine]
  linarith [mul_le_mul_of_nonneg_left (hS q hq p hp) hb]

/-- Positive affine rescaling preserves strict propriety. -/
theorem IsStrictlyProperOn.affine {S : ScoringRule Ω} {P : Set (Ω → ℝ)}
    (hS : S.IsStrictlyProperOn P) {b : ℝ} (hb : 0 < b) (h : Ω → ℝ) :
    (S.affine b h).IsStrictlyProperOn P := by
  intro q hq p hp hpq
  rw [expectedScore_affine, expectedScore_affine]
  linarith [mul_lt_mul_of_pos_left (hS q hq p hp hpq) hb]

end ScoringRule

end ScoringRuleCore

section Savage

variable {Ω : Type*} [Fintype Ω]

/-- The continuous linear functional `v ↦ v ⬝ᵥ g` on `Ω → ℝ`. -/
def dotCLM (g : Ω → ℝ) : (Ω → ℝ) →L[ℝ] ℝ :=
  ∑ ω, g ω • ContinuousLinearMap.proj (R := ℝ) ω

@[simp]
theorem dotCLM_apply (g v : Ω → ℝ) : dotCLM g v = v ⬝ᵥ g := by
  simp only [dotCLM, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, dotProduct]
  exact sum_congr rfl fun ω _ => mul_comm _ _

/-- The **Savage scoring rule** generated by a potential `G : (Ω → ℝ) → ℝ` and vector field
`g : (Ω → ℝ) → Ω → ℝ`: `S(p, ω) = G(p) + g(p)(ω) - p ⬝ᵥ g(p) = G(p) + (e_ω - p) ⬝ᵥ g(p)`
[Savage1971; GneitingRaftery2007]. -/
def savageScoringRule (G : (Ω → ℝ) → ℝ) (g : (Ω → ℝ) → Ω → ℝ) : ScoringRule Ω where
  score p ω := G p + g p ω - p ⬝ᵥ g p

@[simp]
theorem savageScoringRule_score (G : (Ω → ℝ) → ℝ) (g : (Ω → ℝ) → Ω → ℝ) (p : Ω → ℝ) (ω : Ω) :
    (savageScoringRule G g).score p ω = G p + g p ω - p ⬝ᵥ g p := by
  rfl

theorem savageScoringRule_score_eq_single [DecidableEq Ω] (G : (Ω → ℝ) → ℝ)
    (g : (Ω → ℝ) → Ω → ℝ) (p : Ω → ℝ) (ω : Ω) :
    (savageScoringRule G g).score p ω = G p + (Pi.single ω (1 : ℝ) - p) ⬝ᵥ g p := by
  rw [savageScoringRule_score, sub_dotProduct, single_dotProduct, one_mul]
  ring

/-- The **Bregman divergence** associated with a potential `G : (Ω → ℝ) → ℝ` and subgradient map
`g : (Ω → ℝ) → Ω → ℝ`: `D_{G, g}(q ‖ p) = G(q) - G(p) - (q - p) ⬝ᵥ g(p)`. -/
def bregmanDivergence (G : (Ω → ℝ) → ℝ) (g : (Ω → ℝ) → Ω → ℝ) (q p : Ω → ℝ) : ℝ :=
  G q - G p - (q - p) ⬝ᵥ g p

@[simp]
theorem bregmanDivergence_apply (G : (Ω → ℝ) → ℝ) (g : (Ω → ℝ) → Ω → ℝ) (q p : Ω → ℝ) :
    bregmanDivergence G g q p = G q - G p - (q - p) ⬝ᵥ g p := by
  rfl

/-- Expected score of `savageScoringRule G g` under any vector `q` summing to `1`. -/
theorem savageScoringRule_expectedScore {G : (Ω → ℝ) → ℝ} {g : (Ω → ℝ) → Ω → ℝ} {q p : Ω → ℝ}
    (hq : ∑ ω, q ω = 1) :
    (savageScoringRule G g).expectedScore q p = G p + (q - p) ⬝ᵥ g p := by
  have h1 : ∑ ω, q ω * (G p + g p ω - p ⬝ᵥ g p) =
      (∑ ω, q ω) * (G p - p ⬝ᵥ g p) + ∑ ω, q ω * g p ω := by
    rw [sum_mul, ← sum_add_distrib]
    exact sum_congr rfl fun ω _ => by ring
  simp only [ScoringRule.expectedScore_apply, savageScoringRule_score]
  rw [h1, hq, one_mul, sub_dotProduct]
  simp only [dotProduct]
  ring

theorem savageScoringRule_expectedScore_self {G : (Ω → ℝ) → ℝ} {g : (Ω → ℝ) → Ω → ℝ} {q : Ω → ℝ}
    (hq : ∑ ω, q ω = 1) :
    (savageScoringRule G g).expectedScore q q = G q := by
  rw [savageScoringRule_expectedScore hq, sub_self, zero_dotProduct, add_zero]

/-- The expected score gap of `savageScoringRule G g` between truthfully reporting `q` and
reporting `p` equals the Bregman divergence `bregmanDivergence G g q p`
[GneitingRaftery2007]. -/
theorem savageScoringRule_score_gap_eq_bregmanDivergence {G : (Ω → ℝ) → ℝ} {g : (Ω → ℝ) → Ω → ℝ}
    {q p : Ω → ℝ} (hq : ∑ ω, q ω = 1) :
    (savageScoringRule G g).expectedScore q q - (savageScoringRule G g).expectedScore q p =
      bregmanDivergence G g q p := by
  rw [savageScoringRule_expectedScore_self hq, savageScoringRule_expectedScore hq,
    bregmanDivergence_apply]
  ring

/-- `savageScoringRule G g` is proper on `P ⊆ probSimplex Ω` iff `g` is a subgradient of `G` on
`P` (equivalently, `bregmanDivergence G g` is nonnegative on `P`). -/
theorem savageScoringRule_isProperOn_iff {P : Set (Ω → ℝ)} (hP : P ⊆ probSimplex Ω)
    {G : (Ω → ℝ) → ℝ} {g : (Ω → ℝ) → Ω → ℝ} :
    (savageScoringRule G g).IsProperOn P ↔
      ∀ p ∈ P, ∀ q ∈ P, G p + (q - p) ⬝ᵥ g p ≤ G q :=
  ⟨fun h p hp q hq => by
      have h' := h q hq p hp
      rw [savageScoringRule_expectedScore (hP hq).sum_eq_one,
        savageScoringRule_expectedScore_self (hP hq).sum_eq_one] at h'
      exact h',
    fun h q hq p hp => by
      rw [savageScoringRule_expectedScore (hP hq).sum_eq_one,
        savageScoringRule_expectedScore_self (hP hq).sum_eq_one]
      exact h p hp q hq⟩

/-- `savageScoringRule G g` is strictly proper on `P ⊆ probSimplex Ω` iff `g` is a strict
subgradient of `G` on `P`. -/
theorem savageScoringRule_isStrictlyProperOn_iff {P : Set (Ω → ℝ)} (hP : P ⊆ probSimplex Ω)
    {G : (Ω → ℝ) → ℝ} {g : (Ω → ℝ) → Ω → ℝ} :
    (savageScoringRule G g).IsStrictlyProperOn P ↔
      ∀ p ∈ P, ∀ q ∈ P, q ≠ p → G p + (q - p) ⬝ᵥ g p < G q :=
  ⟨fun h p hp q hq hqp => by
      have h' := h q hq p hp hqp.symm
      rw [savageScoringRule_expectedScore (hP hq).sum_eq_one,
        savageScoringRule_expectedScore_self (hP hq).sum_eq_one] at h'
      exact h',
    fun h q hq p hp hpq => by
      rw [savageScoringRule_expectedScore (hP hq).sum_eq_one,
        savageScoringRule_expectedScore_self (hP hq).sum_eq_one]
      exact h p hp q hq hpq.symm⟩

/-- Differentiable sufficient condition for propriety: if `G` is convex on `P ⊆ probSimplex Ω`
and has Fréchet derivative `dotCLM (g p)` within `P` at every `p ∈ P`, then
`savageScoringRule G g` is proper on `P` [Savage1971; GneitingRaftery2007]. -/
theorem isProperOn_savageScoringRule_of_convexOn {P : Set (Ω → ℝ)} (hP : P ⊆ probSimplex Ω)
    {G : (Ω → ℝ) → ℝ} {g : (Ω → ℝ) → Ω → ℝ} (hG : ConvexOn ℝ P G)
    (hd : ∀ p ∈ P, HasFDerivWithinAt G (dotCLM (g p)) P p) :
    (savageScoringRule G g).IsProperOn P :=
  (savageScoringRule_isProperOn_iff hP).2 fun p hp _ hq => by
    simpa only [dotCLM_apply] using hG.add_le_of_hasFDerivWithinAt hp hq (hd p hp)

/-- Differentiable sufficient condition for strict propriety: if `G` is strictly convex on
`P ⊆ probSimplex Ω` and has Fréchet derivative `dotCLM (g p)` within `P` at every `p ∈ P`, then
`savageScoringRule G g` is strictly proper on `P` [Savage1971; GneitingRaftery2007]. -/
theorem isStrictlyProperOn_savageScoringRule_of_strictConvexOn {P : Set (Ω → ℝ)}
    (hP : P ⊆ probSimplex Ω) {G : (Ω → ℝ) → ℝ} {g : (Ω → ℝ) → Ω → ℝ}
    (hG : StrictConvexOn ℝ P G) (hd : ∀ p ∈ P, HasFDerivWithinAt G (dotCLM (g p)) P p) :
    (savageScoringRule G g).IsStrictlyProperOn P :=
  (savageScoringRule_isStrictlyProperOn_iff hP).2 fun p hp _ hq hqp => by
    simpa only [dotCLM_apply] using hG.add_lt_of_hasFDerivWithinAt hp hq hqp (hd p hp)

/-- **Savage / Gneiting–Raftery characterization of proper scoring rules**
[Savage1971; GneitingRaftery2007]: on a convex subset `P ⊆ probSimplex Ω`, a scoring
rule `S` is proper on `P` if and only if there exist a convex potential `G` on `P` and a
subgradient map `g` on `P` such that `S.score p ω = (savageScoringRule G g).score p ω` for all
`p ∈ P` and `ω : Ω`. -/
theorem isProperOn_iff_exists_savage {P : Set (Ω → ℝ)} (hP : P ⊆ probSimplex Ω)
    (hPconv : Convex ℝ P) (S : ScoringRule Ω) :
    S.IsProperOn P ↔
      ∃ G g, ConvexOn ℝ P G ∧
        (∀ p ∈ P, ∀ q ∈ P, G p + (q - p) ⬝ᵥ g p ≤ G q) ∧
        (∀ p ∈ P, ∀ ω, S.score p ω = (savageScoringRule G g).score p ω) := by
  refine ⟨fun hS => ?_, fun ⟨G, g, _, hsub, heq⟩ q hq p hp => ?_⟩
  · have hsub : ∀ p ∈ P, ∀ q ∈ P, S.expectedScore p p + (q - p) ⬝ᵥ S.score p ≤
        S.expectedScore q q := fun p hp q hq => by
      have := hS q hq p hp
      simp only [sub_dotProduct, ScoringRule.expectedScore_eq_dotProduct] at this ⊢
      linarith
    exact ⟨fun p => S.expectedScore p p, S.score,
      convexOn_of_forall_add_le (g := fun p => dotCLM (S.score p)) hPconv
        (fun p hp q hq => by simpa only [dotCLM_apply] using hsub p hp q hq),
      hsub, fun p _ ω => by
        simp only [savageScoringRule_score, ScoringRule.expectedScore_eq_dotProduct]
        ring⟩
  · rw [ScoringRule.expectedScore_congr (heq p hp) q,
      ScoringRule.expectedScore_congr (heq q hq) q]
    exact (savageScoringRule_isProperOn_iff hP).2 hsub q hq p hp

/-- **Savage / Gneiting–Raftery characterization of strictly proper scoring rules**
[Savage1971; GneitingRaftery2007]: on a convex subset `P ⊆ probSimplex Ω`, a scoring
rule `S` is strictly proper on `P` if and only if there exist a strictly convex potential `G` on
`P` and a strict subgradient map `g` on `P` such that
`S.score p ω = (savageScoringRule G g).score p ω` for all `p ∈ P` and `ω : Ω`. -/
theorem isStrictlyProperOn_iff_exists_savage {P : Set (Ω → ℝ)} (hP : P ⊆ probSimplex Ω)
    (hPconv : Convex ℝ P) (S : ScoringRule Ω) :
    S.IsStrictlyProperOn P ↔
      ∃ G g, StrictConvexOn ℝ P G ∧
        (∀ p ∈ P, ∀ q ∈ P, q ≠ p → G p + (q - p) ⬝ᵥ g p < G q) ∧
        (∀ p ∈ P, ∀ ω, S.score p ω = (savageScoringRule G g).score p ω) := by
  refine ⟨fun hS => ?_, fun ⟨G, g, _, hsub, heq⟩ q hq p hp hpq => ?_⟩
  · have hsub : ∀ p ∈ P, ∀ q ∈ P, q ≠ p →
        S.expectedScore p p + (q - p) ⬝ᵥ S.score p < S.expectedScore q q := fun p hp q hq hqp => by
      have := hS q hq p hp hqp.symm
      simp only [sub_dotProduct, ScoringRule.expectedScore_eq_dotProduct] at this ⊢
      linarith
    exact ⟨fun p => S.expectedScore p p, S.score,
      strictConvexOn_of_forall_add_lt (g := fun p => dotCLM (S.score p)) hPconv
        (fun p hp q hq hqp => by simpa only [dotCLM_apply] using hsub p hp q hq hqp),
      hsub, fun p _ ω => by
        simp only [savageScoringRule_score, ScoringRule.expectedScore_eq_dotProduct]
        ring⟩
  · rw [ScoringRule.expectedScore_congr (heq p hp) q,
      ScoringRule.expectedScore_congr (heq q hq) q]
    exact (savageScoringRule_isStrictlyProperOn_iff hP).2 hsub q hq p hp hpq

end Savage

section CanonicalRules

/-! ### Quadratic (Brier) scoring rule -/

/-- The **quadratic scoring rule**: `S(p, ω) = 2 * p ω - ∑ ω', p ω' ^ 2`
[FriedmanResnickSami2007, §27.4.2, pp. 686–687, Exercise 27.7, p. 697; GneitingRaftery2007]. -/
def quadraticScore (Ω : Type*) [Fintype Ω] : ScoringRule Ω where
  score p ω := 2 * p ω - ∑ ω', p ω' ^ 2

@[simp]
theorem quadraticScore_score {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (ω : Ω) :
    (quadraticScore Ω).score p ω = 2 * p ω - ∑ ω', p ω' ^ 2 := by
  rfl

/-- The quadratic scoring rule is the Savage scoring rule generated by `G(p) = ∑ ω, p ω ^ 2` and
`g(p)(ω) = 2 * p ω`. -/
theorem quadraticScore_eq_savage {Ω : Type*} [Fintype Ω] :
    quadraticScore Ω = savageScoringRule (fun p => ∑ ω, p ω ^ 2) (fun p ω => 2 * p ω) := by
  ext p ω
  simp only [quadraticScore_score, savageScoringRule_score, dotProduct]
  have hsum : ∑ i : Ω, p i * (2 * p i) = 2 * ∑ i : Ω, p i ^ 2 := by
    rw [mul_sum]
    exact sum_congr rfl fun i _ => by ring
  rw [hsum]
  ring

/-- The expected score gap of `quadraticScore` equals the squared Euclidean distance
`∑ ω, (q ω - p ω) ^ 2`. -/
theorem quadraticScore_expectedScore_sub {Ω : Type*} [Fintype Ω] {q p : Ω → ℝ}
    (hq : ∑ ω, q ω = 1) :
    (quadraticScore Ω).expectedScore q q - (quadraticScore Ω).expectedScore q p =
      ∑ ω, (q ω - p ω) ^ 2 := by
  have heval (r : Ω → ℝ) : (quadraticScore Ω).expectedScore q r =
      2 * (∑ ω, q ω * r ω) - ∑ ω, r ω ^ 2 := by
    simp only [ScoringRule.expectedScore_apply, quadraticScore_score, mul_sub, sum_sub_distrib,
      ← sum_mul, hq, one_mul]
    rw [mul_sum]
    congr 1
    exact sum_congr rfl fun _ _ => by ring
  have hqq : ∑ ω, q ω * q ω = ∑ ω, q ω ^ 2 := sum_congr rfl fun _ _ => (sq _).symm
  have hsq : ∑ ω, (q ω - p ω) ^ 2 = ∑ ω, (q ω ^ 2 - 2 * (q ω * p ω) + p ω ^ 2) :=
    sum_congr rfl fun _ _ => by ring
  rw [heval q, heval p, hqq, hsq]
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]
  ring

/-- **Strict propriety of the quadratic scoring rule** on the full probability simplex
[FriedmanResnickSami2007, §27.4.2, pp. 686–687, Exercise 27.7, p. 697; GneitingRaftery2007]. -/
theorem isStrictlyProper_quadraticScore {Ω : Type*} [Fintype Ω] :
    (quadraticScore Ω).IsStrictlyProper := fun q hq p _ hpq => by
  obtain ⟨ω₀, hω₀⟩ := Function.ne_iff.mp hpq
  linarith [quadraticScore_expectedScore_sub (p := p) hq.sum_eq_one,
    sum_pos' (fun ω _ => sq_nonneg (q ω - p ω))
      ⟨ω₀, mem_univ _, sq_pos_of_ne_zero (sub_ne_zero.mpr hω₀.symm)⟩]

/-- Sharp range bounds for the quadratic scoring rule on `probSimplex Ω`: every score lies in
`[-1, 1]` (giving `[a - b, a + b]` for the affine version `a + b * quadraticScore`, `b > 0`, as in
[FriedmanResnickSami2007, Exercise 27.7, p. 697]). -/
theorem quadraticScore_bounds {Ω : Type*} [Fintype Ω] {p : Ω → ℝ} (hp : IsMixedStrategy p)
    (ω : Ω) : -1 ≤ (quadraticScore Ω).score p ω ∧ (quadraticScore Ω).score p ω ≤ 1 := by
  have hp_le_one (i : Ω) : p i ≤ 1 :=
    (single_le_sum (fun j _ => hp.nonneg j) (mem_univ i)).trans_eq hp.sum_eq_one
  simp only [quadraticScore_score]
  refine ⟨?_, by
    nlinarith [single_le_sum (fun i _ => sq_nonneg (p i)) (mem_univ ω), sq_nonneg (p ω - 1)]⟩
  have hsum_le : ∑ i, p i ^ 2 ≤ 1 :=
    calc ∑ i, p i ^ 2
        ≤ ∑ i, p i := sum_le_sum fun i _ => by nlinarith [hp.nonneg i, hp_le_one i]
      _ = 1 := hp.sum_eq_one
  linarith [hp.nonneg ω]

/-- The **Brier scoring rule** [Brier1950]: `S(p, ω) = -∑ ω', (1_{ω' = ω} - p ω') ^ 2`. -/
def brierScore (Ω : Type*) [Fintype Ω] [DecidableEq Ω] : ScoringRule Ω where
  score p ω := -∑ ω', ((if ω' = ω then (1 : ℝ) else 0) - p ω') ^ 2

@[simp]
theorem brierScore_score {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (p : Ω → ℝ) (ω : Ω) :
    (brierScore Ω).score p ω = -∑ ω', ((if ω' = ω then (1 : ℝ) else 0) - p ω') ^ 2 := by
  rfl

/-- The Brier score equals `quadraticScore - 1` identically on all vectors `p`. -/
theorem brierScore_eq_quadraticScore_sub_one {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : Ω → ℝ) (ω : Ω) :
    (brierScore Ω).score p ω = (quadraticScore Ω).score p ω - 1 := by
  simp only [brierScore_score, quadraticScore_score]
  have h1 : ∑ ω', ((if ω' = ω then (1 : ℝ) else 0) - p ω') ^ 2 =
      ∑ ω', ((if ω' = ω then (1 : ℝ) else 0) -
        2 * ((if ω' = ω then (1 : ℝ) else 0) * p ω') + p ω' ^ 2) :=
    sum_congr rfl fun _ _ => by split_ifs <;> ring
  rw [h1, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  simp only [ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq']
  ring

/-- **Strict propriety of the Brier scoring rule** on the full probability simplex [Brier1950]. -/
theorem isStrictlyProper_brierScore {Ω : Type*} [Fintype Ω] [DecidableEq Ω] :
    (brierScore Ω).IsStrictlyProper := by
  have heq : brierScore Ω = (quadraticScore Ω).affine 1 (fun _ => -1) := by
    ext p ω
    rw [brierScore_eq_quadraticScore_sub_one, ScoringRule.affine_score, one_mul]
    ring
  rw [heq]
  exact ScoringRule.IsStrictlyProperOn.affine isStrictlyProper_quadraticScore one_pos _

/-! ### Logarithmic scoring rule -/

/-- The **logarithmic scoring rule**: `S(p, ω) = Real.log (p ω)`
[FriedmanResnickSami2007, §27.4.2, pp. 686–687; GneitingRaftery2007]. -/
noncomputable def logScore (Ω : Type*) : ScoringRule Ω where
  score p ω := Real.log (p ω)

@[simp]
theorem logScore_score {Ω : Type*} (p : Ω → ℝ) (ω : Ω) :
    (logScore Ω).score p ω = Real.log (p ω) := by
  rfl

/-- On vectors summing to `1`, the logarithmic scoring rule agrees with the Savage scoring rule
generated by negative Shannon entropy `G(p) = ∑ ω, p ω * log (p ω)` and
`g(p)(ω) = log (p ω) + 1`. -/
theorem logScore_eq_savage {Ω : Type*} [Fintype Ω] {p : Ω → ℝ} (hp : ∑ ω, p ω = 1) (ω : Ω) :
    (logScore Ω).score p ω =
      (savageScoringRule (fun r => ∑ i, r i * Real.log (r i))
        (fun r i => Real.log (r i) + 1)).score p ω := by
  simp only [logScore_score, savageScoringRule_score, dotProduct]
  have hsum : ∑ i : Ω, p i * (Real.log (p i) + 1) = (∑ i : Ω, p i * Real.log (p i)) + 1 := by
    simp only [mul_add, mul_one, sum_add_distrib, hp]
  rw [hsum]
  ring

/-- Strict Gibbs / KL-divergence inequality for the logarithmic scoring rule: for any
`q, p ∈ probSimplex Ω` with `p ≠ q` and `∀ ω, 0 < q ω → 0 < p ω`, truthfully reporting `q`
achieves strictly higher expected log-score than reporting `p`. -/
theorem logScore_expectedScore_lt {Ω : Type*} [Fintype Ω] {q p : Ω → ℝ} (hq : IsMixedStrategy q)
    (hp : IsMixedStrategy p) (hsupp : ∀ ω, 0 < q ω → 0 < p ω) (hpq : p ≠ q) :
    (logScore Ω).expectedScore q p < (logScore Ω).expectedScore q q := by
  have hterm (ω : Ω) : q ω * Real.log (p ω) - q ω * Real.log (q ω) ≤ p ω - q ω := by
    rcases (hq.nonneg ω).eq_or_lt with hq0 | hqpos
    · simpa only [← hq0, zero_mul, sub_zero] using hp.nonneg ω
    · have hppos : 0 < p ω := hsupp ω hqpos
      have hlog := Real.log_le_sub_one_of_pos (div_pos hppos hqpos)
      rw [Real.log_div hppos.ne' hqpos.ne'] at hlog
      linarith [mul_le_mul_of_nonneg_left hlog hqpos.le,
        show q ω * (p ω / q ω - 1) = p ω - q ω by field_simp [hqpos.ne']]
  obtain ⟨ω₀, hω₀⟩ := Function.ne_iff.mp hpq
  have hstrict : q ω₀ * Real.log (p ω₀) - q ω₀ * Real.log (q ω₀) < p ω₀ - q ω₀ := by
    rcases (hq.nonneg ω₀).eq_or_lt with hq0 | hqpos
    · simpa only [← hq0, zero_mul, sub_zero] using (hp.nonneg ω₀).lt_of_ne' (hq0 ▸ hω₀)
    · have hppos : 0 < p ω₀ := hsupp ω₀ hqpos
      have hne1 : p ω₀ / q ω₀ ≠ 1 := fun h => hω₀ ((div_eq_one_iff_eq hqpos.ne').mp h)
      have hlt := Real.add_one_lt_exp
        (Real.log_ne_zero_of_pos_of_ne_one (div_pos hppos hqpos) hne1)
      rw [Real.exp_log (div_pos hppos hqpos), Real.log_div hppos.ne' hqpos.ne'] at hlt
      linarith [mul_lt_mul_of_pos_left (by linarith :
        Real.log (p ω₀) - Real.log (q ω₀) < p ω₀ / q ω₀ - 1) hqpos,
        show q ω₀ * (p ω₀ / q ω₀ - 1) = p ω₀ - q ω₀ by field_simp [hqpos.ne']]
  have hsum_lt := sum_lt_sum (fun ω _ => hterm ω) ⟨ω₀, mem_univ _, hstrict⟩
  simp only [sum_sub_distrib, hp.sum_eq_one, hq.sum_eq_one, sub_self] at hsum_lt
  simp only [ScoringRule.expectedScore_apply, logScore_score]
  linarith

/-- **Strict propriety of the logarithmic scoring rule** on the open probability simplex
`openProbSimplex Ω` [FriedmanResnickSami2007, §27.4.2, pp. 686–687; GneitingRaftery2007]. -/
theorem isStrictlyProperOn_logScore {Ω : Type*} [Fintype Ω] :
    (logScore Ω).IsStrictlyProperOn (openProbSimplex Ω) :=
  fun _ hq _ hp hpq => logScore_expectedScore_lt hq.1 hp.1 (fun ω _ => hp.2 ω) hpq

/-! ### Spherical scoring rule -/

/-- The **spherical scoring rule**: `S(p, ω) = p ω / √(∑ ω', p ω' ^ 2)`
[GneitingRaftery2007]. -/
noncomputable def sphericalScore (Ω : Type*) [Fintype Ω] : ScoringRule Ω where
  score p ω := p ω / Real.sqrt (∑ ω', p ω' ^ 2)

@[simp]
theorem sphericalScore_score {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (ω : Ω) :
    (sphericalScore Ω).score p ω = p ω / Real.sqrt (∑ ω', p ω' ^ 2) := by
  rfl

private theorem sum_sq_pos_of_isMixedStrategy {Ω : Type*} [Fintype Ω] {p : Ω → ℝ}
    (hp : IsMixedStrategy p) : 0 < ∑ ω, p ω ^ 2 := by
  obtain ⟨ω₀, hω₀⟩ := hp.exists_pos
  exact sum_pos' (fun ω _ => sq_nonneg _) ⟨ω₀, mem_univ _, sq_pos_of_pos hω₀⟩

/-- On `probSimplex Ω`, the spherical scoring rule agrees with the Savage scoring rule generated
by the Euclidean norm `G(p) = √(∑ ω, p ω ^ 2)` and `g(p)(ω) = p ω / √(∑ ω', p ω' ^ 2)`. -/
theorem sphericalScore_eq_savage {Ω : Type*} [Fintype Ω] {p : Ω → ℝ} (hp : IsMixedStrategy p)
    (ω : Ω) :
    (sphericalScore Ω).score p ω =
      (savageScoringRule (fun r => Real.sqrt (∑ i, r i ^ 2))
        (fun r i => r i / Real.sqrt (∑ j, r j ^ 2))).score p ω := by
  have hpos := sum_sq_pos_of_isMixedStrategy hp
  have h1 : ∑ i, p i * (p i / Real.sqrt (∑ j, p j ^ 2)) =
      (∑ i, p i ^ 2) / Real.sqrt (∑ j, p j ^ 2) := by
    rw [sum_div]
    exact sum_congr rfl fun _ _ => by ring
  simp only [sphericalScore_score, savageScoringRule_score, dotProduct, h1]
  have hdiv : (∑ i, p i ^ 2) / Real.sqrt (∑ j, p j ^ 2) = Real.sqrt (∑ i, p i ^ 2) := by
    rw [div_eq_iff (Real.sqrt_pos.mpr hpos).ne', Real.mul_self_sqrt hpos.le]
  rw [hdiv]
  ring

/-- Truthful expected spherical score on `probSimplex Ω` equals the Euclidean norm
`√(∑ ω, q ω ^ 2)`. -/
theorem sphericalScore_expectedScore_self {Ω : Type*} [Fintype Ω] {q : Ω → ℝ}
    (hq : IsMixedStrategy q) :
    (sphericalScore Ω).expectedScore q q = Real.sqrt (∑ ω, q ω ^ 2) := by
  rw [ScoringRule.expectedScore_congr (sphericalScore_eq_savage hq) q,
    savageScoringRule_expectedScore_self hq.sum_eq_one]

/-- Lagrange's identity for finite sums. -/
private theorem lagrange_identity {Ω : Type*} [Fintype Ω] (q p : Ω → ℝ) :
    ∑ i, ∑ j, (q i * p j - q j * p i) ^ 2 =
      2 * ((∑ i, q i ^ 2) * (∑ j, p j ^ 2) - (∑ i, q i * p i) ^ 2) := by
  have hexpand (i : Ω) : ∑ j, (q i * p j - q j * p i) ^ 2 =
      q i ^ 2 * (∑ j, p j ^ 2) - 2 * (q i * p i) * (∑ j, q j * p j) +
        p i ^ 2 * (∑ j, q j ^ 2) := by
    rw [mul_sum, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun _ _ => by ring
  simp only [hexpand, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum]
  ring

/-- **Strict propriety of the spherical scoring rule** on the full probability simplex
[GneitingRaftery2007]. -/
theorem isStrictlyProper_sphericalScore {Ω : Type*} [Fintype Ω] :
    (sphericalScore Ω).IsStrictlyProper := by
  intro q hq p hp hpq
  have hqpos := sum_sq_pos_of_isMixedStrategy hq
  have hppos := sum_sq_pos_of_isMixedStrategy hp
  have hqsqrt : 0 < Real.sqrt (∑ ω, q ω ^ 2) := Real.sqrt_pos.mpr hqpos
  have hpsqrt : 0 < Real.sqrt (∑ ω, p ω ^ 2) := Real.sqrt_pos.mpr hppos
  obtain ⟨i₀, j₀, hij⟩ : ∃ i j, q i * p j - q j * p i ≠ 0 := by
    by_contra! hall
    refine hpq (funext fun i => ?_)
    have hsum : ∑ j, q i * p j = ∑ j, q j * p i :=
      sum_congr rfl fun j _ => sub_eq_zero.mp (hall i j)
    simpa only [← mul_sum, ← sum_mul, hp.sum_eq_one, hq.sum_eq_one, mul_one, one_mul] using
      hsum.symm
  have hlag_pos : 0 < ∑ i, ∑ j, (q i * p j - q j * p i) ^ 2 :=
    sum_pos' (fun _ _ => sum_nonneg fun _ _ => sq_nonneg _)
      ⟨i₀, mem_univ _, sum_pos' (fun _ _ => sq_nonneg _) ⟨j₀, mem_univ _, sq_pos_of_ne_zero hij⟩⟩
  have hsq_eq : (Real.sqrt (∑ ω, q ω ^ 2) * Real.sqrt (∑ ω, p ω ^ 2)) ^ 2 =
      (∑ ω, q ω ^ 2) * (∑ ω, p ω ^ 2) := by
    rw [mul_pow, Real.sq_sqrt hqpos.le, Real.sq_sqrt hppos.le]
  have heval_p : (sphericalScore Ω).expectedScore q p =
      (∑ ω, q ω * p ω) / Real.sqrt (∑ ω, p ω ^ 2) := by
    simp only [ScoringRule.expectedScore_apply, sphericalScore_score, sum_div]
    exact sum_congr rfl fun _ _ => by ring
  rw [heval_p, sphericalScore_expectedScore_self hq, div_lt_iff₀ hpsqrt]
  nlinarith [lagrange_identity q p, mul_pos hqsqrt hpsqrt]

end CanonicalRules

end Cslib.GameTheory.PredictionMarket
