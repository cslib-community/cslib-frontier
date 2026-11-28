/-
Copyright (c) 2026 Samuel Schlesinger, Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
import CslibFrontier.Probability.Minimax.Value
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.SupportTsum
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Data.Fintype.Powerset

/-!
# Averaging and the minimax principle for finite distributions

Think of a two-player game in which one player picks a strategy `a` and the other an input `b`,
with loss `loss a b`; for an algorithm, `loss a b` may be whether `a` errs on `b`. Drawing the
strategy from a distribution `μ` and the input from a distribution `ν` relates the two classical
guarantees of randomized algorithms [Yao1977]. Distributions appear in two forms: finitely
supported ones as points of the standard simplex (`Convexity.StdSimplex`), and probability mass
functions (`PMF`), whose supports may be infinite. On a finite type the two correspond
(`Probability.PMF.ofStdSimplex`, `Probability.PMF.toStdSimplex`).

* *The averaging argument*: some outcome of a distribution is at most the mean
  (`Convexity.StdSimplex.exists_mem_support_le_sum_mul`,
  `Probability.PMF.exists_mem_support_le_tsum_mul`). So if a strategy drawn from `μ` has expected
  loss at most `ε` on every input, then for every `ν` some single strategy has expected loss at
  most `ε` on inputs drawn from `ν` (`Probability.PMF.exists_mem_support_tsum_mul_le`; for the
  probability of failing, `Probability.PMF.exists_mem_support_toOuterMeasure_le`). This is the easy
  direction of Yao's principle.
* *The minimax theorem* [vonNeumann1928]: for finitely many strategies and inputs, the converse
  holds. If against every distribution `ν` on the inputs some strategy has expected loss at most
  `ε`, then some distribution `μ` on the strategies has expected loss at most `ε` on every input
  (`Convexity.StdSimplex.exists_forall_sum_le_of_forall_exists_sum_le`, over every linearly
  ordered field, from the existence of the value of a finite game,
  `Cslib.Probability.exists_isMinimaxValue`, which is proved by linear-programming duality;
  `Probability.PMF.exists_forall_sum_mul_le` for distributions as probability mass functions).
  For the probability of failing, only the inputs need to be finite: strategies failing on the same
  inputs are interchangeable, so `μ` can be taken with finite support
  (`Probability.PMF.exists_forall_toOuterMeasure_le`). This is the hard direction of Yao's
  principle.

## Main definitions

* `Cslib.Probability.PMF.ofStdSimplex`, `Cslib.Probability.PMF.toStdSimplex`: distributions on a
  finite type as points of the standard simplex.
* `Convexity.StdSimplex.maxCost`, `Convexity.StdSimplex.errorProb`,
  `Cslib.Probability.PMF.maxCost`, `Cslib.Probability.PMF.errorProb`: maximum cost over the support
  and failure probability of a randomized strategy or input distribution.

## Main results

* `Convexity.StdSimplex.exists_mem_support_le_sum_mul`,
  `Cslib.Probability.PMF.exists_mem_support_le_tsum_mul`: some outcome is at most the mean.
* `Cslib.Probability.PMF.exists_mem_support_sum_mul_le`: some possible outcome is at least the
  mean of a real-valued function on a finite type.
* `Cslib.Probability.PMF.exists_mem_support_tsum_mul_le_tsum_mul`,
  `Cslib.Probability.PMF.exists_mem_support_tsum_mul_le`,
  `Cslib.Probability.PMF.exists_mem_support_toOuterMeasure_le`,
  `Convexity.StdSimplex.exists_errorProb_le`, `Cslib.Probability.PMF.exists_errorProb_le`: the
  averaging argument.
* `Convexity.StdSimplex.exists_forall_sum_le_of_forall_exists_sum_le`,
  `Cslib.Probability.PMF.exists_forall_sum_mul_le`: the minimax theorem for finite games.
* `Convexity.StdSimplex.exists_forall_errorProb_le`,
  `Cslib.Probability.PMF.exists_forall_toOuterMeasure_le`,
  `Convexity.StdSimplex.exists_maxCost_le_and_forall_errorProb_le`,
  `Cslib.Probability.PMF.exists_maxCost_le_and_forall_errorProb_le`: Yao's minimax principle for
  failure probabilities on finitely many inputs.

## References

* [A. C.-C. Yao, *Probabilistic computations: toward a unified measure of complexity*][Yao1977]
* [J. von Neumann, *Zur Theorie der Gesellschaftsspiele*][vonNeumann1928]
-/

@[expose] public section

namespace Convexity.StdSimplex

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### Finitely supported distributions -/

section Averaging

variable {α : Type*} {μ : StdSimplex K α} {g : α → K} {c : K}

/-- An average under a finitely supported distribution is at most any bound on the support. -/
theorem sum_mul_le_of_forall_le (h : ∀ a ∈ μ.weights.support, g a ≤ c) :
    (μ.weights.sum fun a w => w * g a) ≤ c :=
  calc (μ.weights.sum fun a w => w * g a) ≤ μ.weights.sum fun _ w => w * c :=
        Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (h a ha) (μ.weights_nonneg a)
    _ = c := by rw [← Finsupp.sum_mul, μ.total, one_mul]

/-- **The averaging argument**: some point of the support of a finitely supported distribution is
at most the average. -/
theorem exists_mem_support_le_sum_mul (μ : StdSimplex K α) (g : α → K) :
    ∃ a ∈ μ.weights.support, g a ≤ μ.weights.sum fun a w => w * g a := by
  by_contra! h
  have hlt : (μ.weights.sum fun a w => w * (μ.weights.sum fun a w => w * g a)) <
      μ.weights.sum fun a w => w * g a :=
    Finset.sum_lt_sum_of_nonempty μ.support_weights_nonempty fun a ha =>
      mul_lt_mul_of_pos_left (h a ha)
        ((μ.weights_nonneg a).lt_of_ne' (Finsupp.mem_support_iff.mp ha))
  rw [← Finsupp.sum_mul, μ.total, one_mul] at hlt
  exact lt_irrefl _ hlt

end Averaging

/-! ### The minimax theorem for finite games -/

/-- **The minimax theorem for finite two-player zero-sum games** [vonNeumann1928], over every
linearly ordered field `K`, in the form used by Yao's principle. A row player picks `i : I`, a
column player picks `j : J`, and the row player pays `M i j`. If against every mixed strategy `q`
of the column player some row `i` has expected payment at most `c`, then some mixed strategy `p` of
the row player has expected payment at most `c` against every column `j`. It follows from the
existence of the value (`Cslib.Probability.exists_isMinimaxValue`), so the proof is
linear-programming duality, with no topology. -/
theorem exists_forall_sum_le_of_forall_exists_sum_le {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] (M : I → J → K) {c : K}
    (h : ∀ q : StdSimplex K J, ∃ i, ∑ j, q.weights j * M i j ≤ c) :
    ∃ p : StdSimplex K I, ∀ j, ∑ i, p.weights i * M i j ≤ c := by
  rcases isEmpty_or_nonempty J with hJ | hJ
  · exact ⟨.single (Classical.arbitrary I), fun j => isEmptyElim j⟩
  -- the value `v`: the optimal row strategy `p` pays at most `v`, and the optimal column strategy
  -- `q` collects at least `v` from every row, in particular from the row that `h` gives
  obtain ⟨v, ⟨p, hp⟩, q, hq⟩ := Cslib.Probability.exists_isMinimaxValue M
  obtain ⟨i, hi⟩ := h q
  exact ⟨p, fun j => (hp j).trans ((hq i).trans hi)⟩

/-! ### Randomized strategies and distributional error on `StdSimplex` -/

section Strategies

variable {α β γ : Type*}

/-- The maximum of `cost` over the support of a finitely supported distribution `μ`. -/
def maxCost (cost : α → ℕ) (μ : StdSimplex ℝ α) : ℕ :=
  μ.weights.support.sup cost

theorem maxCost_le_iff {cost : α → ℕ} {μ : StdSimplex ℝ α} {d : ℕ} :
    μ.maxCost cost ≤ d ↔ ∀ a ∈ μ.weights.support, cost a ≤ d :=
  Finset.sup_le_iff

theorem le_maxCost {cost : α → ℕ} {μ : StdSimplex ℝ α} {a : α} (ha : a ∈ μ.weights.support) :
    cost a ≤ μ.maxCost cost :=
  Finset.le_sup ha

@[simp] theorem maxCost_single (cost : α → ℕ) (a : α) :
    (StdSimplex.single a : StdSimplex ℝ α).maxCost cost = cost a := by
  simp [maxCost]

/-- Every element in the support of `StdSimplex.map φ μ` is the image of some element in the
support of `μ`. -/
theorem exists_of_mem_support_map {φ : α → β} {μ : StdSimplex ℝ α} {b : β}
    (hb : b ∈ (StdSimplex.map φ μ).weights.support) :
    ∃ a ∈ μ.weights.support, φ a = b := by
  classical
  exact Finset.mem_image.mp
    (Finsupp.mapDomain_support (by simpa [StdSimplex.weights_map] using hb))

/-- If `φ` adds at most `d` to the cost of every strategy in the support, so does `map φ`. -/
theorem maxCost_map_le (cost : α → ℕ) (cost' : β → ℕ) (φ : α → β) (μ : StdSimplex ℝ α) {d : ℕ}
    (hφ : ∀ a, cost' (φ a) ≤ cost a + d) :
    (StdSimplex.map φ μ).maxCost cost' ≤ μ.maxCost cost + d := by
  refine maxCost_le_iff.mpr fun b hb => ?_
  obtain ⟨a, ha, rfl⟩ := exists_of_mem_support_map hb
  exact (hφ a).trans (Nat.add_le_add_right (le_maxCost ha) d)

open Classical in
/-- The probability under `μ` that `Acc` fails. -/
noncomputable def errorProb (Acc : α → Prop) (μ : StdSimplex ℝ α) : ℝ :=
  μ.weights.sum fun a w => w * if Acc a then 0 else 1

/-- `errorProb` with any decidable predicate `Acc`. -/
theorem errorProb_eq_sum (Acc : α → Prop) [DecidablePred Acc] (μ : StdSimplex ℝ α) :
    μ.errorProb Acc = μ.weights.sum fun a w => w * if Acc a then 0 else 1 := by
  unfold errorProb
  congr!

open Classical in
theorem errorProb_nonneg {Acc : α → Prop} {μ : StdSimplex ℝ α} : 0 ≤ μ.errorProb Acc :=
  Finset.sum_nonneg fun a _ => mul_nonneg (μ.weights_nonneg a) (ite_nonneg le_rfl zero_le_one)

open Classical in
theorem errorProb_le_one {Acc : α → Prop} {μ : StdSimplex ℝ α} : μ.errorProb Acc ≤ 1 :=
  sum_mul_le_of_forall_le fun _ _ => ite_le_one zero_le_one le_rfl

theorem errorProb_eq_zero_iff {Acc : α → Prop} {μ : StdSimplex ℝ α} :
    μ.errorProb Acc = 0 ↔ ∀ a ∈ μ.weights.support, Acc a := by
  classical
  rw [errorProb, Finsupp.sum, Finset.sum_eq_zero_iff_of_nonneg fun a _ =>
    mul_nonneg (μ.weights_nonneg a) (ite_nonneg le_rfl zero_le_one)]
  refine forall₂_congr fun a ha => ?_
  rw [mul_eq_zero, or_iff_right (Finsupp.mem_support_iff.mp ha)]
  split_ifs with h <;> simp [h]

open Classical in
@[simp] theorem errorProb_single (Acc : α → Prop) (a : α) :
    (StdSimplex.single a : StdSimplex ℝ α).errorProb Acc = if Acc a then 0 else 1 := by
  simp [errorProb]

theorem errorProb_single_of_pos {Acc : α → Prop} {a : α} (ha : Acc a) :
    (StdSimplex.single a : StdSimplex ℝ α).errorProb Acc = 0 := by
  simp [ha]

theorem errorProb_single_of_neg {Acc : α → Prop} {a : α} (ha : ¬Acc a) :
    (StdSimplex.single a : StdSimplex ℝ α).errorProb Acc = 1 := by
  simp [ha]

/-- Mapping strategies by `φ` that preserves acceptance cannot increase the failure probability. -/
theorem errorProb_map_le (Acc : α → Prop) (Acc' : β → Prop) (φ : α → β) (μ : StdSimplex ℝ α)
    (hφ : ∀ a, Acc a → Acc' (φ a)) :
    (StdSimplex.map φ μ).errorProb Acc' ≤ μ.errorProb Acc := by
  classical
  rw [errorProb_eq_sum, errorProb_eq_sum, StdSimplex.weights_map,
    Finsupp.sum_mapDomain_index (fun _ => zero_mul _) fun _ _ _ => add_mul _ _ _]
  refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ (μ.weights_nonneg a)
  by_cases h : Acc a
  · simp [h, hφ a h]
  · split_ifs <;> linarith

/-- **The averaging argument** for failure probabilities under `StdSimplex`: if `μ` fails on every
input `b` with probability at most `ε`, then for every input distribution `ν` some strategy in the
support of `μ` fails on `ν` with probability at most `ε`. -/
theorem exists_errorProb_le (Acc : α → β → Prop) (μ : StdSimplex ℝ α) (ν : StdSimplex ℝ β)
    {ε : ℝ} (h : ∀ b, μ.errorProb (fun a => Acc a b) ≤ ε) :
    ∃ a ∈ μ.weights.support, ν.errorProb (fun b => Acc a b) ≤ ε := by
  classical
  obtain ⟨a, ha, hle⟩ := exists_mem_support_le_sum_mul μ fun a => ν.errorProb (fun b => Acc a b)
  refine ⟨a, ha, hle.trans ((le_of_eq ?_).trans (sum_mul_le_of_forall_le (μ := ν) fun b _ => h b))⟩
  simp only [errorProb, Finsupp.sum, Finset.mul_sum]
  exact Finset.sum_comm.trans <|
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _

/-- **Yao's minimax principle** for failure probabilities on a finite input space: if against every
input distribution `ν` some strategy in `α` fails with probability at most `ε`, then some finitely
supported distribution `μ` on `α` fails with probability at most `ε` on every input. Strategies
with the same failure set on `β` are interchangeable, so only finitely many representative
strategies are needed even when `α` is infinite. -/
theorem exists_forall_errorProb_le [Finite β] [Nonempty α] (Acc : α → β → Prop) {ε : ℝ}
    (h : ∀ ν : StdSimplex ℝ β, ∃ a : α, ν.errorProb (fun b => Acc a b) ≤ ε) :
    ∃ μ : StdSimplex ℝ α, ∀ b, μ.errorProb (fun a => Acc a b) ≤ ε := by
  classical
  have := Fintype.ofFinite β
  let r : α → Set β := fun a => {b | ¬Acc a b}
  have := Fintype.ofFinite (Set.range r)
  have : Nonempty (Set.range r) := ⟨⟨r (Classical.arbitrary α), _, rfl⟩⟩
  let rep : Set.range r → α := fun s => s.property.choose
  have hrep (s : Set.range r) (b : β) :
      (if Acc (rep s) b then 0 else 1 : ℝ) = if b ∈ s.val then 1 else 0 := by
    have hmem : b ∈ s.val ↔ ¬Acc (rep s) b := by rw [← s.property.choose_spec]; rfl
    by_cases hb : Acc (rep s) b <;> simp [hb, hmem]
  obtain ⟨p, hp⟩ := exists_forall_sum_le_of_forall_exists_sum_le
    (fun (s : Set.range r) b => if b ∈ s.val then 1 else 0) (c := ε) fun q => by
      obtain ⟨a, hq⟩ := h q
      rw [errorProb_eq_sum, Finsupp.sum_fintype _ _ fun _ => zero_mul _] at hq
      exact ⟨⟨r a, a, rfl⟩, le_of_eq_of_le
        (Finset.sum_congr rfl fun b _ => by by_cases hb : Acc a b <;> simp [hb, r]) hq⟩
  refine ⟨p.map rep, fun b => ?_⟩
  rw [errorProb_eq_sum, StdSimplex.weights_map,
    Finsupp.sum_mapDomain_index (fun _ => zero_mul _) fun _ _ _ => add_mul _ _ _,
    Finsupp.sum_fintype _ _ fun _ => zero_mul _]
  exact le_of_eq_of_le (Finset.sum_congr rfl fun s _ => by rw [hrep]) (hp b)

/-- **Yao's minimax principle** for bounded-cost finitely supported randomized strategies on a
finite nonempty input space: if against every input distribution `ν` some strategy of cost at most
`d` fails with probability at most `ε`, then some finitely supported distribution `μ` over
strategies of cost at most `d` fails with probability at most `ε` on every input. -/
theorem exists_maxCost_le_and_forall_errorProb_le [Finite β] [Nonempty β]
    (cost : α → ℕ) (Acc : α → β → Prop) {d : ℕ} {ε : ℝ}
    (h : ∀ ν : StdSimplex ℝ β, ∃ a : α, cost a ≤ d ∧ ν.errorProb (fun b => Acc a b) ≤ ε) :
    ∃ μ : StdSimplex ℝ α, (∀ b, μ.errorProb (fun a => Acc a b) ≤ ε) ∧ μ.maxCost cost ≤ d := by
  classical
  obtain ⟨a₀, ha₀, -⟩ := h (.single (Classical.arbitrary β))
  have : Nonempty {a : α // cost a ≤ d} := ⟨⟨a₀, ha₀⟩⟩
  obtain ⟨μ, hμ⟩ := exists_forall_errorProb_le (α := {a : α // cost a ≤ d})
    (fun a b => Acc a.val b) (ε := ε) fun ν =>
      let ⟨a, ha, hν⟩ := h ν
      ⟨⟨a, ha⟩, hν⟩
  refine ⟨μ.map Subtype.val, fun b => (errorProb_map_le
      (fun a : {a : α // cost a ≤ d} => Acc a.val b)
      (fun a => Acc a b) Subtype.val μ fun _ => id).trans (hμ b),
    maxCost_le_iff.mpr fun a ha => ?_⟩
  obtain ⟨a', -, rfl⟩ := exists_of_mem_support_map ha
  exact a'.property

end Strategies

end Convexity.StdSimplex

namespace Cslib.Probability.PMF

open scoped ENNReal
open Convexity Finset

/-! ### Probability mass functions -/

variable {α β : Type*}

/-- **Some possible outcome is at most the mean**: for every distribution `μ` and every function
`g` with values in `[0, ∞]`, some outcome `a` that `μ` can produce has `g a` at most the mean of `g`
under `μ`. The sample space may be infinite. -/
theorem exists_mem_support_le_tsum_mul (μ : PMF α) (g : α → ℝ≥0∞) :
    ∃ a ∈ μ.support, g a ≤ ∑' a, μ a * g a := by
  by_contra! hlt
  obtain ⟨a₀, ha₀⟩ := μ.support_nonempty
  have htop : ∑' a, μ a * g a ≠ ⊤ := ne_top_of_lt (hlt a₀ ha₀)
  have := ENNReal.tsum_lt_tsum (f := fun a => μ a * ∑' a, μ a * g a)
    (g := fun a => μ a * g a) (i := a₀)
    (by rwa [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul])
    (fun a => by
      by_cases ha : a ∈ μ.support
      · gcongr
        exact (hlt a ha).le
      · simp [(PMF.apply_eq_zero_iff μ a).mpr ha])
    (ENNReal.mul_lt_mul_right ((PMF.mem_support_iff μ a₀).mp ha₀) (PMF.apply_ne_top μ a₀)
      (hlt a₀ ha₀))
  rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul] at this
  exact lt_irrefl _ this

/-- **The averaging argument**, the easy direction of Yao's principle: for any strategy
distribution `μ`, input distribution `ν`, and `[0, ∞]`-valued loss `loss`, some strategy in the
support of `μ` has `ν`-expected loss at most the `ν`-expectation of the `μ`-expected loss. The
sample spaces may be infinite. -/
theorem exists_mem_support_tsum_mul_le_tsum_mul (μ : PMF α) (ν : PMF β) (loss : α → β → ℝ≥0∞) :
    ∃ a ∈ μ.support, ∑' b, ν b * loss a b ≤ ∑' b, ν b * ∑' a, μ a * loss a b := by
  obtain ⟨a, ha, hle⟩ := exists_mem_support_le_tsum_mul μ fun a => ∑' b, ν b * loss a b
  refine ⟨a, ha, hle.trans (le_of_eq ?_)⟩
  simp only [← ENNReal.tsum_mul_left]
  rw [tsum_comm]
  exact tsum_congr fun b => tsum_congr fun a => by ring

/-- **The averaging argument**, the easy direction of Yao's principle. Let `loss a b` be the loss
of a strategy `a` on an input `b`. If drawing the strategy from `μ` has expected loss at most `ε` on
every input that `ν` can produce, then some strategy that `μ` can produce has expected loss at most
`ε` on inputs drawn from `ν`. The sample spaces may be infinite. -/
theorem exists_mem_support_tsum_mul_le (μ : PMF α) (ν : PMF β) (loss : α → β → ℝ≥0∞)
    {ε : ℝ≥0∞} (h : ∀ b ∈ ν.support, ∑' a, μ a * loss a b ≤ ε) :
    ∃ a ∈ μ.support, ∑' b, ν b * loss a b ≤ ε := by
  obtain ⟨a, ha, hle⟩ := exists_mem_support_tsum_mul_le_tsum_mul μ ν loss
  exact ⟨a, ha, hle.trans (tsum_mul_le_of_support ν h)⟩

/-- The probability of an event as the mean of its indicator. -/
private theorem toOuterMeasure_eq_tsum_mul_ite {γ : Type*} (π : PMF γ) (s : Set γ)
    [DecidablePred (· ∈ s)] : π.toOuterMeasure s = ∑' c, π c * if c ∈ s then 1 else 0 := by
  simp only [toOuterMeasure_eq_tsum_mul_indicator, Set.indicator_apply, Pi.one_apply]

/-- **The averaging argument** for events, the easy direction of Yao's principle: if a strategy
drawn from `μ` fails on every input that `ν` can produce with probability at most `ε`, then some
strategy that `μ` can produce fails on an input drawn from `ν` with probability at most `ε`. The
sample spaces may be infinite. -/
theorem exists_mem_support_toOuterMeasure_le (μ : PMF α) (ν : PMF β) (E : α → β → Prop)
    {ε : ℝ} (h : ∀ b ∈ ν.support, (μ.toOuterMeasure {a | E a b}).toReal ≤ ε) :
    ∃ a ∈ μ.support, (ν.toOuterMeasure {b | E a b}).toReal ≤ ε := by
  classical
  obtain ⟨b₀, hb₀⟩ := ν.support_nonempty
  have hε : 0 ≤ ε := ENNReal.toReal_nonneg.trans (h b₀ hb₀)
  obtain ⟨a, ha, hle⟩ := exists_mem_support_tsum_mul_le μ ν
    (fun a b => if E a b then 1 else 0) (ε := ENNReal.ofReal ε) fun b hb => by
      have := h b hb
      rwa [← ENNReal.ofReal_le_ofReal_iff hε,
        ENNReal.ofReal_toReal (PMF.toOuterMeasure_ne_top μ _),
        toOuterMeasure_eq_tsum_mul_ite] at this
  exact ⟨a, ha, ENNReal.toReal_le_of_le_ofReal hε
    (by simpa only [toOuterMeasure_eq_tsum_mul_ite, Set.mem_ofPred_eq] using hle)⟩

/-! ### The minimax theorem for probability mass functions -/

section Minimax

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The finitely supported distribution whose probabilities are the weights of a point of the
standard simplex on an arbitrary type `I`. -/
noncomputable def ofStdSimplex {I : Type*} (p : StdSimplex ℝ I) : PMF I :=
  PMF.ofFinset (fun i => ENNReal.ofReal (p.weights i)) p.weights.support
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => p.weights_nonneg i]
      exact (congrArg ENNReal.ofReal p.total).trans ENNReal.ofReal_one)
    (fun i hi => by rw [Finsupp.notMem_support_iff.mp hi, ENNReal.ofReal_zero])

@[simp] theorem ofStdSimplex_apply {I : Type*} (p : StdSimplex ℝ I) (i : I) :
    ofStdSimplex p i = ENNReal.ofReal (p.weights i) :=
  rfl

/-- The probability of `i` under `ofStdSimplex p` is the weight of `i` in `p`. -/
theorem toReal_ofStdSimplex {I : Type*} (p : StdSimplex ℝ I) (i : I) :
    (ofStdSimplex p i).toReal = p.weights i :=
  ENNReal.toReal_ofReal (p.weights_nonneg i)

/-- Every distribution obtained from `StdSimplex` has finite support. -/
theorem finite_support_ofStdSimplex {I : Type*} (p : StdSimplex ℝ I) :
    (ofStdSimplex p).support.Finite :=
  p.weights.support.finite_toSet.subset fun i hi => by
    contrapose hi
    rw [PMF.mem_support_iff, not_not, ofStdSimplex_apply,
      Finsupp.notMem_support_iff.mp hi, ENNReal.ofReal_zero]

/-- The real-valued outer measure of `{i | P i}` under `ofStdSimplex p` equals
`p.errorProb (fun i => ¬P i)`. -/
theorem toOuterMeasure_toReal_ofStdSimplex_setOf {I : Type*} (p : StdSimplex ℝ I) (P : I → Prop) :
    ((ofStdSimplex p).toOuterMeasure {i | P i}).toReal = p.errorProb (fun i => ¬P i) := by
  classical
  rw [toOuterMeasure_eq_tsum_mul_ite,
    tsum_eq_sum (s := p.weights.support) fun i hi => by
      rw [ofStdSimplex_apply, Finsupp.notMem_support_iff.mp hi, ENNReal.ofReal_zero, zero_mul],
    ENNReal.toReal_sum fun i _ =>
      ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (by split_ifs <;> simp),
    StdSimplex.errorProb_eq_sum, Finsupp.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : P i <;> simp [hi, p.weights_nonneg i]

/-- The point of the standard simplex whose weights are the probabilities of a distribution on a
finite type. -/
noncomputable def toStdSimplex (μ : PMF I) : StdSimplex ℝ I where
  weights := Finsupp.equivFunOnFinite.symm fun i => (μ i).toReal
  nonneg _ := ENNReal.toReal_nonneg
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simpa using sum_toReal μ

/-- The weight of `i` in `toStdSimplex μ` is the probability of `i`, as a real number. -/
@[simp] theorem weights_toStdSimplex (μ : PMF I) (i : I) :
    (toStdSimplex μ).weights i = (μ i).toReal :=
  rfl

/-- Passing from a distribution to the simplex and back returns the distribution. -/
@[simp] theorem ofStdSimplex_toStdSimplex (μ : PMF I) : ofStdSimplex (toStdSimplex μ) = μ :=
  PMF.ext fun i => by
    rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top μ i), ← weights_toStdSimplex]
    rfl

/-- **Some possible outcome is at least the mean** of a real-valued function on a finite type:
the averaging argument that fixes a choice at least as good as a random one. This is
`Convexity.StdSimplex.exists_mem_support_le_sum_mul` applied to `-g`. -/
theorem exists_mem_support_sum_mul_le (μ : PMF I) (g : I → ℝ) :
    ∃ i ∈ μ.support, ∑ j, (μ j).toReal * g j ≤ g i := by
  obtain ⟨i, hi, hle⟩ := StdSimplex.exists_mem_support_le_sum_mul (toStdSimplex μ) fun i => -g i
  refine ⟨i, ?_, ?_⟩
  · simpa [toStdSimplex, PMF.mem_support_iff, ENNReal.toReal_eq_zero_iff, PMF.apply_ne_top]
      using hi
  · rw [Finsupp.sum_fintype _ _ (by simp)] at hle
    simp only [weights_toStdSimplex, mul_neg, Finset.sum_neg_distrib] at hle
    linarith

/-- **The minimax theorem for finite games** [vonNeumann1928], for distributions. Let `M i j` be
the loss of a strategy `i` on an input `j`. If against every distribution `ν` on the inputs some
strategy has expected loss at most `ε`, then some distribution `μ` on the strategies has expected
loss at most `ε` on every input. This is the hard direction of Yao's principle; it is
`Convexity.StdSimplex.exists_forall_sum_le_of_forall_exists_sum_le` read through `ofStdSimplex`.
-/
theorem exists_forall_sum_mul_le [Nonempty I] (M : I → J → ℝ) {ε : ℝ}
    (h : ∀ ν : PMF J, ∃ i, ∑ j, (ν j).toReal * M i j ≤ ε) :
    ∃ μ : PMF I, ∀ j, ∑ i, (μ i).toReal * M i j ≤ ε := by
  obtain ⟨p, hp⟩ := StdSimplex.exists_forall_sum_le_of_forall_exists_sum_le M fun q => by
    simpa using h (ofStdSimplex q)
  exact ⟨ofStdSimplex p, by simpa using hp⟩

/-- **Yao's minimax principle** for finite sets of inputs. Let `E i j` say that a strategy `i`
fails on an input `j`, where there may be infinitely many strategies but only finitely many inputs.
If against every distribution `ν` on the inputs some strategy fails with probability at most `ε`,
then some distribution `μ` on finitely many strategies fails with probability at most `ε` on every
input. This is `Convexity.StdSimplex.exists_forall_errorProb_le` read through `ofStdSimplex`. -/
theorem exists_forall_toOuterMeasure_le {I J : Type*} [Finite J] [Nonempty I] (E : I → J → Prop)
    {ε : ℝ} (h : ∀ ν : PMF J, ∃ i, (ν.toOuterMeasure {j | E i j}).toReal ≤ ε) :
    ∃ μ : PMF I, μ.support.Finite ∧ ∀ j, (μ.toOuterMeasure {i | E i j}).toReal ≤ ε := by
  obtain ⟨p, hp⟩ := StdSimplex.exists_forall_errorProb_le (fun i j => ¬E i j) (ε := ε) fun q => by
    simpa only [toOuterMeasure_toReal_ofStdSimplex_setOf] using h (ofStdSimplex q)
  exact ⟨ofStdSimplex p, finite_support_ofStdSimplex p, fun j => by
    simpa only [toOuterMeasure_toReal_ofStdSimplex_setOf] using hp j⟩

end Minimax

/-! ### Public-coin cost, error probability, and Yao's minimax bridge on `PMF` -/

section PublicCoin

/-- The supremum of `cost` over the support of `μ`, in `ℕ∞`. -/
noncomputable def maxCost (cost : α → ℕ) (μ : PMF α) : ℕ∞ :=
  ⨆ a ∈ μ.support, (cost a : ℕ∞)

theorem maxCost_le_iff {cost : α → ℕ} {μ : PMF α} {c : ℕ∞} :
    maxCost cost μ ≤ c ↔ ∀ a ∈ μ.support, (cost a : ℕ∞) ≤ c :=
  iSup₂_le_iff

theorem le_maxCost {cost : α → ℕ} {μ : PMF α} {a : α} (ha : a ∈ μ.support) :
    (cost a : ℕ∞) ≤ maxCost cost μ :=
  le_iSup₂ (f := fun a (_ : a ∈ μ.support) => (cost a : ℕ∞)) a ha

@[simp] theorem maxCost_pure (cost : α → ℕ) (a : α) :
    maxCost cost (PMF.pure a) = cost a :=
  le_antisymm (maxCost_le_iff.mpr fun b hb => by rw [(PMF.mem_support_pure_iff _ _).mp hb])
    (le_maxCost ((PMF.mem_support_pure_iff _ _).mpr rfl))

theorem maxCost_map_le {γ : Type*} (cost : α → ℕ) (cost' : γ → ℕ) (f : γ → α) (μ : PMF γ)
    (hf : ∀ c ∈ μ.support, cost (f c) ≤ cost' c) :
    maxCost cost (μ.map f) ≤ maxCost cost' μ := by
  refine maxCost_le_iff.mpr fun a ha => ?_
  obtain ⟨c, hc, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
  exact (Nat.cast_le.mpr (hf c hc)).trans (le_maxCost hc)

theorem maxCost_map_le_of_le {γ : Type*} (cost : α → ℕ) (f : γ → α) (μ : PMF γ) {c : ℕ}
    (hf : ∀ x ∈ μ.support, cost (f x) ≤ c) :
    maxCost cost (μ.map f) ≤ c := by
  refine maxCost_le_iff.mpr fun a ha => ?_
  obtain ⟨x, hx, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
  exact_mod_cast hf x hx

/-- The real-valued probability that a strategy `a` drawn from `μ` fails `Acc a b` on input `b`. -/
noncomputable def errorProb (Acc : α → β → Prop) (μ : PMF α) (b : β) : ℝ :=
  (μ.toOuterMeasure {a | ¬Acc a b}).toReal

theorem errorProb_eq_sum [Fintype α] (Acc : α → β → Prop) (μ : PMF α) (b : β)
    [DecidablePred fun a => Acc a b] :
    errorProb Acc μ b = ∑ a, if Acc a b then 0 else (μ a).toReal := by
  rw [errorProb, PMF.toOuterMeasure_apply_toReal]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : Acc a b <;> simp [h]

theorem errorProb_nonneg {Acc : α → β → Prop} {μ : PMF α} {b : β} : 0 ≤ errorProb Acc μ b :=
  ENNReal.toReal_nonneg

theorem errorProb_le_one {Acc : α → β → Prop} {μ : PMF α} {b : β} : errorProb Acc μ b ≤ 1 :=
  toOuterMeasure_toReal_le_one μ _

open Classical in
theorem errorProb_pure (Acc : α → β → Prop) (a : α) (b : β) :
    errorProb Acc (PMF.pure a) b = if Acc a b then 0 else 1 := by
  rw [errorProb, PMF.toOuterMeasure_pure_apply]
  split_ifs <;> simp_all

theorem errorProb_pure_le (Acc : α → β → Prop) {a : α} {b : β} {ε : ℝ} (ha : Acc a b)
    (hε : 0 ≤ ε) : errorProb Acc (PMF.pure a) b ≤ ε := by
  classical
  simpa [errorProb_pure, ha] using hε

theorem errorProb_map {γ : Type*} (Acc : α → β → Prop) (f : γ → α) (μ : PMF γ) (b : β) :
    errorProb Acc (μ.map f) b = errorProb (fun c b => Acc (f c) b) μ b := by
  rw [errorProb, errorProb, PMF.toOuterMeasure_map_apply]
  rfl

/-- **The averaging argument** in terms of `errorProb`: if `μ` errs with probability at most `ε`
on every input in the support of `ν`, then some strategy in the support of `μ` errs with
probability at most `ε` on inputs drawn from `ν`. -/
theorem exists_errorProb_le {Acc : α → β → Prop} {μ : PMF α} (ν : PMF β) {ε : ℝ}
    (h : ∀ b ∈ ν.support, errorProb Acc μ b ≤ ε) :
    ∃ a ∈ μ.support, errorProb (fun b a => Acc a b) ν a ≤ ε :=
  exists_mem_support_toOuterMeasure_le μ ν (fun a b => ¬Acc a b) h

/-- **Yao's minimax principle** for bounded-cost `PMF` strategies on a finite input domain `D`:
if under every distribution `ν` supported on `D` some strategy of cost at most `c` errs with
probability at most `ε`, then some distribution `μ` over strategies of cost at most `c` errs with
probability at most `ε` on every input of `D`. -/
theorem exists_maxCost_le_and_forall_errorProb_le {cost : α → ℕ} {Acc : α → β → Prop}
    {D : Set β} [Finite D] {c : ℕ} [Nonempty {a : α // cost a ≤ c}] {ε : ℝ}
    (h : ∀ ν : PMF β, (∀ b ∈ ν.support, b ∈ D) →
      ∃ a : α, cost a ≤ c ∧ errorProb (fun b a => Acc a b) ν a ≤ ε) :
    ∃ μ : PMF α, (∀ b ∈ D, errorProb Acc μ b ≤ ε) ∧ maxCost cost μ ≤ c := by
  obtain ⟨μ, -, hμ⟩ := exists_forall_toOuterMeasure_le
    (I := {a : α // cost a ≤ c}) (J := D) (fun a b => ¬Acc a.val b.val) (ε := ε) fun ν => by
      obtain ⟨a, hc, hp⟩ := h (ν.map Subtype.val) fun b hb =>
        let ⟨b', _, hb'⟩ := (PMF.mem_support_map_iff _ _ _).mp hb
        hb' ▸ b'.property
      exact ⟨⟨a, hc⟩, by rwa [errorProb, PMF.toOuterMeasure_map_apply] at hp⟩
  refine ⟨μ.map Subtype.val, fun b hb => ?_,
    maxCost_map_le_of_le cost Subtype.val μ fun a _ => a.property⟩
  rw [errorProb, PMF.toOuterMeasure_map_apply]
  exact hμ ⟨b, hb⟩

end PublicCoin

end Cslib.Probability.PMF
