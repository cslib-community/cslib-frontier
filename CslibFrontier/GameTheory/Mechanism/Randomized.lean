/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.VCG
public import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Randomized mechanisms: universal truthfulness vs truthfulness in expectation

Following [Nisan2007] (§9.5.6, Definition 9.38, pp. 231–232), a *randomized mechanism*
(`RandomizedMechanism ι Ω`) is a discrete probability distribution (`PMF (Mechanism ι Ω)`) over
deterministic direct-revelation mechanisms sharing the same agents `ι` and outcome space `Ω`. This
representation separates two notions of dominant-strategy truthfulness on valuation domains
`V : ι → Set (Ω → ℝ)`:

* **Universal incentive compatibility** (`RandomizedMechanism.IsUniversallyDSICOn`): every
  deterministic mechanism in the support `R.dist.support` is incentive compatible on `V`.
* **Incentive compatibility in expectation** (`RandomizedMechanism.IsTruthfulInExpectationOn`):
  truthful reporting maximizes expected quasilinear utility
  `R.expectedUtility i v b = ∑' M, (R.dist M).toReal * M.utility i v b` over the mechanism's
  internal randomization.

Whenever expected utilities are summable on `V` (`RandomizedMechanism.HasSummableUtilityOn`, which
holds automatically whenever `R.dist.support` is finite or utilities are bounded across the
support), universal truthfulness implies truthfulness in expectation
(`RandomizedMechanism.IsUniversallyDSICOn.isTruthfulInExpectationOn`, [Nisan2007], §9.5.6, p. 232).

The converse fails (`exists_isTruthfulInExpectation_not_isUniversallyDSIC`, original separation not
in [Nisan2007]): the concrete 1-agent, 2-outcome coin-flip mechanism `coinFlipMechanism`
(`Ω = Bool`) outputs `true` and `false` with probability `1/2` each and pairs opposite
report-dependent payments (`2` vs `0`) on the two branches so that expected payment is identically
`1` and expected utility is `(v true + v false)/2 - 1` regardless of the report, making it truthful
in expectation on every valuation domain while neither deterministic branch in its support is DSIC
even on nonnegative valuations.

## Main definitions

* `RandomizedMechanism`: a `PMF` over deterministic `Mechanism ι Ω`s ([Nisan2007],
  Definition 9.38).
* `RandomizedMechanism.deterministic`: embeds a deterministic mechanism via `PMF.pure`.
* `RandomizedMechanism.expectedUtility`, `RandomizedMechanism.SummableUtility`,
  `RandomizedMechanism.HasSummableUtilityOn`: expected quasilinear utility and summability.
* `RandomizedMechanism.IsUniversallyDSICOn`, `RandomizedMechanism.IsUniversallyDSIC`: universal
  incentive compatibility ([Nisan2007], Definition 9.38).
* `RandomizedMechanism.IsTruthfulInExpectationOn`, `RandomizedMechanism.IsTruthfulInExpectation`:
  incentive compatibility in expectation ([Nisan2007], Definition 9.38).
* `RandomizedMechanism.coinFlipBranch`, `RandomizedMechanism.coinFlipMechanism`: concrete 2-outcome
  randomized mechanism separating the two notions (original).

## Main results

* `RandomizedMechanism.hasSummableUtilityOn_of_support_finite`,
  `RandomizedMechanism.hasSummableUtilityOn_of_bdd`: automatic summability for finite-support or
  bounded-utility randomized mechanisms.
* `RandomizedMechanism.IsUniversallyDSICOn.isTruthfulInExpectationOn`,
  `RandomizedMechanism.IsUniversallyDSICOn.isTruthfulInExpectationOn_of_support_finite`: universal
  truthfulness implies truthfulness in expectation ([Nisan2007], §9.5.6).
* `RandomizedMechanism.coinFlipMechanism_isTruthfulInExpectation`,
  `RandomizedMechanism.not_isUniversallyDSICOn_coinFlipMechanism`,
  `RandomizedMechanism.exists_isTruthfulInExpectation_not_isUniversallyDSIC`: truthfulness in
  expectation does not imply universal truthfulness, even with two outcomes and nonnegative
  valuations (original).

## References

* [N. Nisan, *Introduction to mechanism design (for computer scientists)*][Nisan2007]
-/

public section

namespace Cslib.GameTheory

open scoped ENNReal

/-- A **randomized mechanism** ([Nisan2007], Definition 9.38): a discrete probability distribution
over deterministic mechanisms with agents `ι` and outcome set `Ω`. -/
@[ext] structure RandomizedMechanism (ι Ω : Type*) where
  /-- The probability mass function over deterministic mechanisms. -/
  dist : PMF (Mechanism ι Ω)

namespace RandomizedMechanism

variable {ι Ω : Type*}

/-- Embed a deterministic mechanism `M` as a point-mass randomized mechanism `PMF.pure M`. -/
noncomputable def deterministic (M : Mechanism ι Ω) : RandomizedMechanism ι Ω :=
  ⟨PMF.pure M⟩

@[simp] theorem deterministic_dist (M : Mechanism ι Ω) : (deterministic M).dist = PMF.pure M := by
  rfl

/-- The expected quasilinear utility `E_{M ∼ R}[v(M.outcome b) − M.payment b i]` of agent `i` with
true valuation `v` on reported valuations `b` ([Nisan2007], Definition 9.38). -/
noncomputable def expectedUtility (R : RandomizedMechanism ι Ω) (i : ι) (v : Ω → ℝ)
    (b : ι → Ω → ℝ) : ℝ :=
  ∑' M : Mechanism ι Ω, (R.dist M).toReal * M.utility i v b

theorem expectedUtility_def (R : RandomizedMechanism ι Ω) (i : ι) (v : Ω → ℝ) (b : ι → Ω → ℝ) :
    R.expectedUtility i v b = ∑' M : Mechanism ι Ω, (R.dist M).toReal * M.utility i v b := by
  rfl

/-- Summability of the utility series defining `expectedUtility R i v b`. -/
@[expose] def SummableUtility (R : RandomizedMechanism ι Ω) (i : ι) (v : Ω → ℝ)
    (b : ι → Ω → ℝ) : Prop :=
  Summable fun M : Mechanism ι Ω => (R.dist M).toReal * M.utility i v b

/-- Every utility series on profiles and valuations from `V` is summable. -/
@[expose] def HasSummableUtilityOn (R : RandomizedMechanism ι Ω) (V : ι → Set (Ω → ℝ)) : Prop :=
  ∀ (i : ι) (b : ι → Ω → ℝ) (v : Ω → ℝ), (∀ j, b j ∈ V j) → v ∈ V i →
    R.SummableUtility i v b

/-- **Universal incentive compatibility** on `V` ([Nisan2007], Definition 9.38): every
deterministic mechanism in the support of `R` is DSIC on `V`. -/
@[expose] def IsUniversallyDSICOn [DecidableEq ι] (R : RandomizedMechanism ι Ω)
    (V : ι → Set (Ω → ℝ)) : Prop :=
  ∀ M ∈ R.dist.support, M.IsDSICOn V

/-- Unrestricted universal incentive compatibility (`V i = Set.univ`). -/
abbrev IsUniversallyDSIC [DecidableEq ι] (R : RandomizedMechanism ι Ω) : Prop :=
  R.IsUniversallyDSICOn fun _ => Set.univ

/-- **Incentive compatibility in expectation** on `V` ([Nisan2007], Definition 9.38): truthful
reporting maximizes expected quasilinear utility on `V`. -/
@[expose] def IsTruthfulInExpectationOn [DecidableEq ι] (R : RandomizedMechanism ι Ω)
    (V : ι → Set (Ω → ℝ)) : Prop :=
  ∀ (i : ι) (b : ι → Ω → ℝ) (v : Ω → ℝ), (∀ j, b j ∈ V j) → v ∈ V i →
    R.expectedUtility i v b ≤ R.expectedUtility i v (Function.update b i v)

/-- Unrestricted incentive compatibility in expectation (`V i = Set.univ`). -/
abbrev IsTruthfulInExpectation [DecidableEq ι] (R : RandomizedMechanism ι Ω) : Prop :=
  R.IsTruthfulInExpectationOn fun _ => Set.univ

@[simp] theorem expectedUtility_deterministic (M : Mechanism ι Ω) (i : ι) (v : Ω → ℝ)
    (b : ι → Ω → ℝ) :
    (deterministic M).expectedUtility i v b = M.utility i v b :=
  Probability.PMF.tsum_pure_toReal_mul M fun N => N.utility i v b

@[simp] theorem isUniversallyDSICOn_deterministic_iff [DecidableEq ι] (M : Mechanism ι Ω)
    (V : ι → Set (Ω → ℝ)) :
    (deterministic M).IsUniversallyDSICOn V ↔ M.IsDSICOn V := by
  simp only [IsUniversallyDSICOn, deterministic, PMF.support_pure, Set.mem_singleton_iff,
    forall_eq]

@[simp] theorem isTruthfulInExpectationOn_deterministic_iff [DecidableEq ι] (M : Mechanism ι Ω)
    (V : ι → Set (Ω → ℝ)) :
    (deterministic M).IsTruthfulInExpectationOn V ↔ M.IsDSICOn V := by
  simp only [IsTruthfulInExpectationOn, expectedUtility_deterministic, Mechanism.IsDSICOn]

/-- Every finitely supported randomized mechanism has summable expected utilities on every
domain. -/
theorem summableUtility_of_support_finite {R : RandomizedMechanism ι Ω}
    (hfin : R.dist.support.Finite) (i : ι) (v : Ω → ℝ) (b : ι → Ω → ℝ) :
    R.SummableUtility i v b := by
  refine summable_of_ne_finset_zero (s := hfin.toFinset) fun M hM => ?_
  have hnot : M ∉ R.dist.support := fun h => hM (hfin.mem_toFinset.2 h)
  rw [PMF.mem_support_iff, not_not] at hnot
  simp only [hnot, ENNReal.toReal_zero, zero_mul]

theorem hasSummableUtilityOn_of_support_finite {R : RandomizedMechanism ι Ω}
    (hfin : R.dist.support.Finite) (V : ι → Set (Ω → ℝ)) : R.HasSummableUtilityOn V :=
  fun i b v _ _ => summableUtility_of_support_finite hfin i v b

/-- Uniformly bounded utilities on `R.dist.support` ensure summability of expected utilities, since
`(R.dist M).toReal` sums to `1`. -/
theorem summableUtility_of_bdd {R : RandomizedMechanism ι Ω} {i : ι} {v : Ω → ℝ} {b : ι → Ω → ℝ}
    {C : ℝ} (hC : ∀ M ∈ R.dist.support, |M.utility i v b| ≤ C) :
    R.SummableUtility i v b := by
  have hC0 : 0 ≤ max C 0 := le_max_right C 0
  have hdom : Summable fun M => (R.dist M).toReal * max C 0 :=
    (Cslib.Probability.PMF.summable_toReal R.dist).mul_right (max C 0)
  refine Summable.of_norm_bounded hdom fun M => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  by_cases hM : M ∈ R.dist.support
  · exact mul_le_mul_of_nonneg_left ((hC M hM).trans (le_max_left C 0)) ENNReal.toReal_nonneg
  · rw [PMF.mem_support_iff, not_not] at hM
    simp only [hM, ENNReal.toReal_zero, zero_mul, le_rfl]

theorem hasSummableUtilityOn_of_bdd {R : RandomizedMechanism ι Ω} {V : ι → Set (Ω → ℝ)}
    (hbdd : ∀ i b v, (∀ j, b j ∈ V j) → v ∈ V i →
      ∃ C, ∀ M ∈ R.dist.support, |M.utility i v b| ≤ C) :
    R.HasSummableUtilityOn V := by
  intro i b v hb hv
  obtain ⟨C, hC⟩ := hbdd i b v hb hv
  exact summableUtility_of_bdd hC

/-- **Universal truthfulness implies truthfulness in expectation** ([Nisan2007], §9.5.6): if every
deterministic mechanism in `R.dist.support` is DSIC on `V` and utilities are summable on `V`, then
`R` is truthful in expectation on `V`. -/
theorem IsUniversallyDSICOn.isTruthfulInExpectationOn [DecidableEq ι]
    {R : RandomizedMechanism ι Ω} {V : ι → Set (Ω → ℝ)} (hR : R.IsUniversallyDSICOn V)
    (hsum : R.HasSummableUtilityOn V) : R.IsTruthfulInExpectationOn V := by
  intro i b v hb hv
  have hs1 : R.SummableUtility i v b := hsum i b v hb hv
  have hs2 : R.SummableUtility i v (Function.update b i v) :=
    hsum i (Function.update b i v) v
      ((Function.forall_update_iff b fun j u => u ∈ V j).2 ⟨hv, fun j _ => hb j⟩) hv
  refine hs1.tsum_le_tsum (fun M => ?_) hs2
  by_cases hM : M ∈ R.dist.support
  · exact mul_le_mul_of_nonneg_left (hR M hM i b v hb hv) ENNReal.toReal_nonneg
  · rw [PMF.mem_support_iff, not_not] at hM
    simp only [hM, ENNReal.toReal_zero, zero_mul, le_rfl]

/-- For finitely supported randomized mechanisms, universal truthfulness implies truthfulness in
expectation with no extra summability hypothesis. -/
theorem IsUniversallyDSICOn.isTruthfulInExpectationOn_of_support_finite [DecidableEq ι]
    {R : RandomizedMechanism ι Ω} {V : ι → Set (Ω → ℝ)} (hR : R.IsUniversallyDSICOn V)
    (hfin : R.dist.support.Finite) : R.IsTruthfulInExpectationOn V :=
  hR.isTruthfulInExpectationOn (hasSummableUtilityOn_of_support_finite hfin V)

theorem IsTruthfulInExpectationOn.mono [DecidableEq ι] {R : RandomizedMechanism ι Ω}
    {V W : ι → Set (Ω → ℝ)} (hR : R.IsTruthfulInExpectationOn W) (hVW : ∀ i, V i ⊆ W i) :
    R.IsTruthfulInExpectationOn V :=
  fun i b v hb hv => hR i b v (fun j => hVW j (hb j)) (hVW i hv)

/-! ### Separation: truthfulness in expectation does not imply universal truthfulness -/

open Classical in
/-- One branch of `coinFlipMechanism` on two outcomes (`Ω = Bool`) and one agent (`ι = Unit`):
branch `true` always selects `true` and charges `2` when `b () false ≤ b () true` (else `0`),
while branch `false` always selects `false` and charges `0` when `b () false ≤ b () true` (else
`2`). -/
noncomputable def coinFlipBranch (c : Bool) : Mechanism Unit Bool where
  outcome _ := c
  payment b _ :=
    if c then (if b () false ≤ b () true then 2 else 0)
    else (if b () false ≤ b () true then 0 else 2)

@[simp] theorem coinFlipBranch_outcome (c : Bool) (b : Unit → Bool → ℝ) :
    (coinFlipBranch c).outcome b = c := by
  rfl

open Classical in
theorem coinFlipBranch_payment (c : Bool) (b : Unit → Bool → ℝ) (i : Unit) :
    (coinFlipBranch c).payment b i =
      if c then (if b () false ≤ b () true then 2 else 0)
      else (if b () false ≤ b () true then 0 else 2) := by
  rfl

private theorem coinFlipBranch_injective : Function.Injective coinFlipBranch := by
  intro c₁ c₂ h
  exact congrArg (fun M => M.outcome 0) h

/-- A 2-outcome randomized mechanism (`Ω = Bool`, original; not in [Nisan2007]) tossing a fair coin
between `coinFlipBranch true` and `coinFlipBranch false`. Its expected payment is identically `1`
and its expected outcome is uniform on `Bool` regardless of the report, so it is truthful in
expectation everywhere while neither deterministic branch in its support is DSIC. -/
noncomputable def coinFlipMechanism : RandomizedMechanism Unit Bool :=
  ⟨(Cslib.Probability.PMF.uniformOfFintype Bool).map coinFlipBranch⟩

theorem coinFlipMechanism_support :
    coinFlipMechanism.dist.support = {coinFlipBranch true, coinFlipBranch false} := by
  ext M
  simp only [coinFlipMechanism, PMF.support_map, Set.mem_image,
    Cslib.Probability.PMF.mem_support_uniformOfFintype, true_and, Bool.exists_bool,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem coinFlipMechanism_expectedUtility (v : Bool → ℝ) (b : Unit → Bool → ℝ) :
    coinFlipMechanism.expectedUtility () v b = (v true + v false) / 2 - 1 := by
  classical
  have hprob (c : Bool) : (coinFlipMechanism.dist (coinFlipBranch c)).toReal = 1 / 2 := by
    rw [coinFlipMechanism,
      Cslib.Probability.PMF.map_apply_of_injective _ coinFlipBranch_injective c,
      Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.card_bool]
    norm_num
  rw [expectedUtility, ← coinFlipBranch_injective.tsum_eq fun M hM => ?_,
    tsum_fintype, Fintype.sum_bool, hprob, hprob]
  · simp only [Mechanism.utility, coinFlipBranch, ↓reduceIte, Bool.false_eq_true]
    split_ifs <;> ring
  · have hmem : M ∈ coinFlipMechanism.dist.support := fun h0 => hM (by simp [h0])
    obtain ⟨c, _, rfl⟩ := (PMF.mem_support_map_iff _ _ M).1 hmem
    exact ⟨c, rfl⟩

/-- `coinFlipMechanism` is truthful in expectation on all real valuations (`Set.univ`), hence on
every valuation domain `V`. -/
theorem coinFlipMechanism_isTruthfulInExpectation :
    coinFlipMechanism.IsTruthfulInExpectation := by
  intro i b v _ _
  cases i
  rw [coinFlipMechanism_expectedUtility, coinFlipMechanism_expectedUtility]

/-- Neither branch of `coinFlipMechanism` is DSIC, even on the domain `{v | 0 ≤ v}` of nonnegative
valuations: when `v true = 2` and `v false = 0`, misreporting `b () false = 2 > 0 = b () true`
lowers the payment on `coinFlipBranch true` from `2` to `0` without changing the outcome `true`. -/
theorem not_isUniversallyDSICOn_coinFlipMechanism :
    ¬ coinFlipMechanism.IsUniversallyDSICOn (fun _ => {v : Bool → ℝ | 0 ≤ v}) := by
  intro hU
  have hmem : coinFlipBranch true ∈ coinFlipMechanism.dist.support := by
    rw [coinFlipMechanism_support]
    exact Set.mem_insert _ _
  let v : Bool → ℝ := fun c => if c then 2 else 0
  let w : Bool → ℝ := fun c => if c then 0 else 2
  have hv : v ∈ {u : Bool → ℝ | 0 ≤ u} := fun c => by cases c <;> norm_num [v]
  have hw : ∀ j : Unit, (fun _ => w) j ∈ {u : Bool → ℝ | 0 ≤ u} :=
    fun _ c => by cases c <;> norm_num [w]
  have hineq := hU (coinFlipBranch true) hmem () (fun _ => w) v hw hv
  simp only [Mechanism.utility, coinFlipBranch, Function.update_self, v, w] at hineq
  norm_num at hineq

/-- **Truthfulness in expectation does not imply universal truthfulness** (original; not in
[Nisan2007]), even with one agent, two outcomes (`Bool`), finite support, and nonnegative
valuations. -/
theorem exists_isTruthfulInExpectation_not_isUniversallyDSIC :
    ∃ R : RandomizedMechanism Unit Bool,
      R.dist.support.Finite ∧
      R.IsTruthfulInExpectation ∧
      ¬ R.IsUniversallyDSICOn (fun _ => {v : Bool → ℝ | 0 ≤ v}) :=
  ⟨coinFlipMechanism,
    by rw [coinFlipMechanism_support]; exact (Set.finite_singleton _).insert _,
    coinFlipMechanism_isTruthfulInExpectation,
    not_isUniversallyDSICOn_coinFlipMechanism⟩

end RandomizedMechanism

end Cslib.GameTheory
