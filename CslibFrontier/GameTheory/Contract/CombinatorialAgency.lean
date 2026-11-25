/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Strategic.StrongNash
public import CslibFrontier.Init
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Bounds.Defs
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Combinatorial agency, contracts, and the Price of Unaccountability

This module formalizes the combinatorial principal-agent (moral-hazard in teams) framework from
[BabaioffChuangFeldman2007] (NRTV Chapter 23, §23.5):

* **Production technologies, marginal contributions, and Nash-inducing contracts**:
  `marginalContrib` (discrete marginal contribution `Δ_i(a_{-i})`), `IsStrictlyMonotone`
  (characterized pointwise via `isStrictlyMonotone_iff_marginalContrib_pos`), `contractCostGame`
  (embedding the agents' effort game into `Cslib.GameTheory.CostGame`), best-response thresholds
  (`bestResponse_true_iff`, `bestResponse_false_iff`, `isPureNash_iff_marginalContrib`), minimal
  expected-payment Nash-inducing contracts (`optContract`, `optPayment`, `isPureNash_optContract`,
  `optContract_le_of_isPureNash`), and coalition stability (`isStrongNash_optContract` and
  `isStrongEquilibrium_optContract` reusing `Cslib.GameTheory.CostGame.IsStrongNash` and
  `CostGame.IsStrongEquilibrium`).
* **First-best welfare, hidden-action utility, Monotonicity Lemma, and POU**:
  `firstBestWelfare`, `agencyPrincipalUtility`, `monotonicity_firstBest`, `monotonicity_agency`,
  and `priceOfUnaccountability` (`POU(t, c) = ⨆ v > 0, SW_ns(v) / U_ag(v)`).
* **Anonymous technologies and transition characterization**:
  `countTrue` and general slope monotonicity criteria characterizing when optimal team size skips
  intermediate cardinalities versus stepping through every `0, 1, …, n`.
* **AND and OR technologies**:
  For `andTech n γ` (`γ ∈ (0, 1 / 2)`), proves the single `0 → n` jump at `andThreshold n γ c`,
  the exact formula `POU = (1 / γ - 1) ^ (n - 1) + (1 - γ / (1 - γ))` (`andTech_pou_eq`), and
  unboundedness in both `n` and `1 / γ`. For `orTech n γ` (`γ ∈ (0, 1 / 2)`), proves `n`
  strictly increasing transition thresholds through all `0, 1, …, n` (`orTech_transitions`) and
  the uniform constant upper bound `POU ≤ 2` (`orTech_pou_le_two`, sharpening Theorem 23.9's
  `≤ 5 / 2` bound).

## References

* [M. Babaioff, J. Chuang, and M. Feldman, *Incentives in Peer-to-Peer
  Systems*][BabaioffChuangFeldman2007] (NRTV Chapter 23; exact source theorem/page locators
  unverified against the printed book beyond #7789's chapter index).
-/

public section

namespace Cslib.GameTheory.Contract

open Finset

section CoreAgency

variable {ι : Type*} [DecidableEq ι]

/-- **Marginal contribution** (`Δ_i(a_{-i})`) of agent `i` under production technology `t` given
the opponents' actions in `a`: `t(1, a_{-i}) - t(0, a_{-i})`. -/
def marginalContrib (t : (ι → Bool) → ℝ) (i : ι) (a : ι → Bool) : ℝ :=
  t (Function.update a i true) - t (Function.update a i false)

theorem marginalContrib_eq (t : (ι → Bool) → ℝ) (i : ι) (a : ι → Bool) :
    marginalContrib t i a = t (Function.update a i true) - t (Function.update a i false) := by
  rfl

theorem marginalContrib_update (t : (ι → Bool) → ℝ) (i : ι) (a : ι → Bool) (b : Bool) :
    marginalContrib t i (Function.update a i b) = marginalContrib t i a := by
  simp only [marginalContrib, Function.update_idem]

/-- A production technology `t : (ι → Bool) → ℝ` is **strictly monotone** if strictly raising
at least one agent's effort strictly increases the success probability. -/
@[expose] def IsStrictlyMonotone (t : (ι → Bool) → ℝ) : Prop :=
  ∀ ⦃a b : ι → Bool⦄, (∀ i, a i = true → b i = true) → a ≠ b → t a < t b

omit [DecidableEq ι] in
theorem IsStrictlyMonotone.le_of_le {t : (ι → Bool) → ℝ} (ht : IsStrictlyMonotone t)
    {a b : ι → Bool} (h : ∀ i, a i = true → b i = true) : t a ≤ t b := by
  by_cases hab : a = b
  · rw [hab]
  · exact (ht h hab).le

private theorem le_of_update_false_lt_true [Fintype ι] {t : (ι → Bool) → ℝ}
    (ht : ∀ i a, 0 < marginalContrib t i a) :
    ∀ {n : ℕ} {a b : ι → Bool}, (∀ i, a i = true → b i = true) →
      (Finset.univ.filter fun i => b i = true ∧ a i = false).card = n →
      a ≠ b → t a < t b := by
  intro n
  induction n with
  | zero =>
    intro a b hab hcard hne
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hcard
    apply False.elim (hne _)
    funext i
    cases ha : a i with
    | true => exact (hab i ha).symm
    | false =>
      have hmem := hcard (mem_univ i)
      cases hb : b i with
      | false => rfl
      | true => exact False.elim (hmem ⟨hb, ha⟩)
  | succ k ih =>
    intro a b hab hcard _
    have hpos : 0 < (Finset.univ.filter fun i => b i = true ∧ a i = false).card :=
      hcard ▸ Nat.succ_pos k
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
    simp only [mem_filter, mem_univ, true_and] at hj
    let a' := Function.update a j true
    have ha'_lt : t a < t a' := by
      have hupd : Function.update a j false = a := Function.update_eq_self_iff.mpr hj.2.symm
      have hm := ht j a
      rw [marginalContrib, hupd] at hm
      linarith
    have ha'b : ∀ i, a' i = true → b i = true := by
      intro i hi
      by_cases hij : i = j
      · subst hij; exact hj.1
      · dsimp [a'] at hi
        rw [Function.update_of_ne hij] at hi
        exact hab i hi
    have hcard' : (Finset.univ.filter fun i => b i = true ∧ a' i = false).card = k := by
      have hsub : (Finset.univ.filter fun i => b i = true ∧ a i = false) =
          insert j (Finset.univ.filter fun i => b i = true ∧ a' i = false) := by
        ext i
        simp only [mem_filter, mem_univ, true_and, mem_insert]
        by_cases hij : i = j
        · subst hij; simp [hj.1, hj.2]
        · dsimp [a']
          simp [hij]
      have hjnot : j ∉ Finset.univ.filter fun i => b i = true ∧ a' i = false := by
        simp [a']
      rw [hsub, Finset.card_insert_of_notMem hjnot] at hcard
      omega
    by_cases ha'eq : a' = b
    · rw [← ha'eq]; exact ha'_lt
    · exact ha'_lt.trans (ih ha'b hcard' ha'eq)

/-- A Boolean-action technology is strictly monotone iff every agent has strictly positive
marginal contribution everywhere. -/
theorem isStrictlyMonotone_iff_marginalContrib_pos [Finite ι] (t : (ι → Bool) → ℝ) :
    IsStrictlyMonotone t ↔ ∀ i a, 0 < marginalContrib t i a := by
  let : Fintype ι := Fintype.ofFinite ι
  constructor
  · intro ht i a
    have hle : ∀ j, Function.update a i false j = true → Function.update a i true j = true := by
      intro j hj
      by_cases hij : j = i
      · subst hij; simp at hj
      · simpa [Function.update_of_ne hij] using hj
    have hne : Function.update a i false ≠ Function.update a i true := by
      intro heq
      have h := congrFun heq i
      simp at h
    exact sub_pos.mpr (ht hle hne)
  · intro ht a b hab hne
    exact le_of_update_false_lt_true ht hab rfl hne

/-- The normal-form strategic game (in cost-minimization form) induced by production technology
`t`, effort costs `c`, and limited-liability success payments `p`: agent `i` minimizes
`c_i a_i - p_i t(a)`. -/
def contractCostGame (t : (ι → Bool) → ℝ) (c p : ι → ℝ) :
    CostGame ι (fun _ => Bool) where
  cost i a := (if a i then c i else 0) - p i * t a

omit [DecidableEq ι] in
@[simp]
theorem contractCostGame_cost (t : (ι → Bool) → ℝ) (c p : ι → ℝ) (i : ι) (a : ι → Bool) :
    (contractCostGame t c p).cost i a = (if a i then c i else 0) - p i * t a := by
  rfl

/-- **Best-response effort threshold**: exerting effort (`true`) is weakly optimal for agent `i`
given `a_{-i}` iff `p_i ≥ c_i / Δ_i(a_{-i})`. -/
theorem bestResponse_true_iff (t : (ι → Bool) → ℝ) (c p : ι → ℝ) {i : ι} {a : ι → Bool}
    (hΔ : 0 < marginalContrib t i a) :
    (contractCostGame t c p).cost i (Function.update a i true) ≤
        (contractCostGame t c p).cost i (Function.update a i false) ↔
      c i / marginalContrib t i a ≤ p i := by
  simp only [contractCostGame, Function.update_self, ↓reduceIte, Bool.false_eq_true]
  rw [div_le_iff₀ hΔ, marginalContrib]
  constructor <;> intro h <;> linarith

/-- **Best-response shirking threshold**: shirking (`false`) is weakly optimal for agent `i`
given `a_{-i}` iff `p_i ≤ c_i / Δ_i(a_{-i})`. -/
theorem bestResponse_false_iff (t : (ι → Bool) → ℝ) (c p : ι → ℝ) {i : ι} {a : ι → Bool}
    (hΔ : 0 < marginalContrib t i a) :
    (contractCostGame t c p).cost i (Function.update a i false) ≤
        (contractCostGame t c p).cost i (Function.update a i true) ↔
      p i ≤ c i / marginalContrib t i a := by
  simp only [contractCostGame, Function.update_self, Bool.false_eq_true, ↓reduceIte]
  rw [le_div_iff₀ hΔ, marginalContrib]
  constructor <;> intro h <;> linarith

/-- Characterization of pure Nash equilibria in `contractCostGame t c p`. -/
theorem isPureNash_iff_marginalContrib (t : (ι → Bool) → ℝ) (c p : ι → ℝ) (a : ι → Bool)
    (hΔ : ∀ i, 0 < marginalContrib t i a) :
    (contractCostGame t c p).IsPureNash a ↔
      ∀ i, (a i = true → c i / marginalContrib t i a ≤ p i) ∧
        (a i = false → p i ≤ c i / marginalContrib t i a) := by
  constructor
  · intro hnash i
    constructor
    · intro hai
      have h := hnash i false
      have hupd : Function.update a i true = a := Function.update_eq_self_iff.mpr hai.symm
      rw [← hupd] at h
      simp only [Function.update_idem] at h
      exact (bestResponse_true_iff t c p (hΔ i)).mp h
    · intro hai
      have h := hnash i true
      have hupd : Function.update a i false = a := Function.update_eq_self_iff.mpr hai.symm
      rw [← hupd] at h
      simp only [Function.update_idem] at h
      exact (bestResponse_false_iff t c p (hΔ i)).mp h
  · intro h i b
    cases hb : b with
    | true =>
      cases hai : a i with
      | true =>
        rw [Function.update_eq_self_iff.mpr hai.symm]
      | false =>
        have hbr := (bestResponse_false_iff t c p (hΔ i)).mpr ((h i).2 hai)
        have hupd : Function.update a i false = a := Function.update_eq_self_iff.mpr hai.symm
        rwa [hupd] at hbr
    | false =>
      cases hai : a i with
      | true =>
        have hbr := (bestResponse_true_iff t c p (hΔ i)).mpr ((h i).1 hai)
        have hupd : Function.update a i true = a := Function.update_eq_self_iff.mpr hai.symm
        rwa [hupd] at hbr
      | false =>
        rw [Function.update_eq_self_iff.mpr hai.symm]

/-- Minimal limited-liability success-payment contract inducing profile `a`: pays
`c_i / Δ_i(a_{-i})` to agents with `a_i = true` and `0` otherwise. -/
noncomputable def optContract (t : (ι → Bool) → ℝ) (c : ι → ℝ) (a : ι → Bool)
    (i : ι) : ℝ :=
  if a i then c i / marginalContrib t i a else 0

theorem optContract_eq (t : (ι → Bool) → ℝ) (c : ι → ℝ) (a : ι → Bool) (i : ι) :
    optContract t c a i = if a i then c i / marginalContrib t i a else 0 := by
  rfl

@[simp]
theorem optContract_of_true (t : (ι → Bool) → ℝ) (c : ι → ℝ) {a : ι → Bool} {i : ι}
    (h : a i = true) : optContract t c a i = c i / marginalContrib t i a := by
  simp [optContract, h]

@[simp]
theorem optContract_of_false (t : (ι → Bool) → ℝ) (c : ι → ℝ) {a : ι → Bool} {i : ι}
    (h : a i = false) : optContract t c a i = 0 := by
  simp [optContract, h]

/-- Expected total payment made by the principal under the optimal inducing contract
`optContract t c a`: `t(a) * ∑ i, optContract t c a i`. -/
noncomputable def optPayment [Fintype ι] (t : (ι → Bool) → ℝ) (c : ι → ℝ)
    (a : ι → Bool) : ℝ :=
  t a * ∑ i, optContract t c a i

theorem optPayment_eq [Fintype ι] (t : (ι → Bool) → ℝ) (c : ι → ℝ) (a : ι → Bool) :
    optPayment t c a = t a * ∑ i, optContract t c a i := by
  rfl

theorem optPayment_false [Fintype ι] (t : (ι → Bool) → ℝ) (c : ι → ℝ) :
    optPayment t c (fun _ => false) = 0 := by
  simp [optPayment, optContract]

/-- The minimal contract `optContract t c a` implements `a` as a pure Nash equilibrium. -/
theorem isPureNash_optContract (t : (ι → Bool) → ℝ) (c : ι → ℝ) (a : ι → Bool)
    (hΔ : ∀ i, 0 < marginalContrib t i a) (hc : ∀ i, 0 ≤ c i) :
    (contractCostGame t c (optContract t c a)).IsPureNash a := by
  rw [isPureNash_iff_marginalContrib t c (optContract t c a) a hΔ]
  intro i
  constructor
  · intro hai
    simp [optContract, hai]
  · intro hai
    simp only [optContract, hai, Bool.false_eq_true, ↓reduceIte]
    exact div_nonneg (hc i) (hΔ i).le

/-- Optimality of `optContract t c a`: any nonnegative success-payment contract `p` under which
`a` is a pure Nash equilibrium of `contractCostGame t c p` pays at least `optContract t c a i`
to every agent. -/
theorem optContract_le_of_isPureNash (t : (ι → Bool) → ℝ) (c : ι → ℝ) (a : ι → Bool)
    (hΔ : ∀ i, 0 < marginalContrib t i a) {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hnash : (contractCostGame t c p).IsPureNash a) (i : ι) :
    optContract t c a i ≤ p i := by
  cases hai : a i with
  | false =>
    simp only [optContract, hai, Bool.false_eq_true, ↓reduceIte]
    exact hp i
  | true =>
    have hbr := (isPureNash_iff_marginalContrib t c p a hΔ).mp hnash i
    simp only [optContract, hai, ↓reduceIte]
    exact hbr.1 hai

/-- Any nonnegative success-payment contract `p` implementing `a` as a pure Nash equilibrium
has expected payment at least `optPayment t c a`. -/
theorem optPayment_le_of_isPureNash [Fintype ι] (t : (ι → Bool) → ℝ) (c : ι → ℝ) (a : ι → Bool)
    (hΔ : ∀ i, 0 < marginalContrib t i a) (ht0 : 0 ≤ t a) {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hnash : (contractCostGame t c p).IsPureNash a) :
    optPayment t c a ≤ t a * ∑ i, p i := by
  unfold optPayment
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun i _ => optContract_le_of_isPureNash t c a hΔ hp hnash i) ht0

/-- **Optimality under two-outcome limited liability** (NRTV Claim 23.5): any limited-liability
contract `(p, q)` (`0 ≤ p`, `0 ≤ q` on success and failure) under which `a` is a pure Nash
equilibrium incurs expected total payment at least `optPayment t c a`. -/
theorem optPayment_le_of_limitedLiability [Fintype ι] (t : (ι → Bool) → ℝ) (c : ι → ℝ)
    (a : ι → Bool) (hΔ : ∀ i, 0 < marginalContrib t i a) (ht0 : 0 ≤ t a) (ht1 : t a ≤ 1)
    {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hnash : ∀ i b, (if a i then c i else 0) - (p i * t a + q i * (1 - t a)) ≤
      (if b then c i else 0) -
        (p i * t (Function.update a i b) + q i * (1 - t (Function.update a i b)))) :
    optPayment t c a ≤ t a * ∑ i, p i + (1 - t a) * ∑ i, q i := by
  have hterm : ∀ i, optContract t c a i * t a ≤ p i * t a + q i * (1 - t a) := by
    intro i
    cases hai : a i with
    | false =>
      simp only [optContract, hai, Bool.false_eq_true, ↓reduceIte, zero_mul]
      exact add_nonneg (mul_nonneg (hp i) ht0) (mul_nonneg (hq i) (sub_nonneg.mpr ht1))
    | true =>
      have hdev := hnash i false
      have hself : Function.update a i true = a := Function.update_eq_self_iff.mpr hai.symm
      have hm : marginalContrib t i a = t a - t (Function.update a i false) := by
        rw [marginalContrib, hself]
      simp only [hai, ↓reduceIte, Bool.false_eq_true] at hdev
      have hci : c i ≤ (p i - q i) * marginalContrib t i a := by
        rw [hm]
        linarith
      have hdiv : c i / marginalContrib t i a ≤ p i - q i := (div_le_iff₀ (hΔ i)).mpr hci
      simp only [optContract, hai, ↓reduceIte]
      have hmul : (c i / marginalContrib t i a) * t a ≤ (p i - q i) * t a :=
        mul_le_mul_of_nonneg_right hdiv ht0
      have hqnonneg := hq i
      linarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
  simp only [optPayment]
  linarith

private theorem cost_le_piecewise_of_subset [Finite ι] (t : (ι → Bool) → ℝ) (c : ι → ℝ)
    (a : ι → Bool) (ht : IsStrictlyMonotone t) (hc : ∀ i, 0 ≤ c i) (A : Finset ι)
    (b : ι → Bool) (hsub : ∀ j, A.piecewise b a j = true → a j = true) (i : ι) :
    (contractCostGame t c (optContract t c a)).cost i a ≤
      (contractCostGame t c (optContract t c a)).cost i (A.piecewise b a) := by
  let : Fintype ι := Fintype.ofFinite ι
  have hΔ : ∀ k s, 0 < marginalContrib t k s := (isStrictlyMonotone_iff_marginalContrib_pos t).mp ht
  set a' := A.piecewise b a
  cases hai : a i with
  | false =>
    have ha'i : a' i = false := by
      cases h : a' i with
      | false => rfl
      | true => exact absurd (hsub i h) (by simp [hai])
    simp [contractCostGame, optContract, hai, ha'i]
  | true =>
    have hc_opt : 0 ≤ optContract t c a i := by
      simp only [optContract, hai, ↓reduceIte]
      exact div_nonneg (hc i) (hΔ i a).le
    cases ha'i : a' i with
    | true =>
      have htle : t a' ≤ t a := ht.le_of_le hsub
      simp only [contractCostGame, hai, ha'i, ↓reduceIte]
      nlinarith
    | false =>
      have hle_upd : ∀ j, a' j = true → Function.update a i false j = true := by
        intro j hj
        by_cases hij : j = i
        · subst hij
          rw [ha'i] at hj
          contradiction
        · rw [Function.update_of_ne hij]
          exact hsub j hj
      have htle : t a' ≤ t (Function.update a i false) := ht.le_of_le hle_upd
      have hmul : optContract t c a i * marginalContrib t i a = c i := by
        simp only [optContract, hai, ↓reduceIte]
        exact div_mul_cancel₀ _ (hΔ i a).ne'
      have hself : Function.update a i true = a := Function.update_eq_self_iff.mpr hai.symm
      have hm : marginalContrib t i a = t a - t (Function.update a i false) := by
        rw [marginalContrib, hself]
      simp only [contractCostGame, hai, ha'i, Bool.false_eq_true, ↓reduceIte]
      nlinarith

/-- Under any strictly monotone technology `t` and nonnegative costs `c`, the optimal contract
`optContract t c a` implements `a` as a **strong equilibrium** (no nonempty coalition can
strictly improve every member, NRTV Exercise 23.6). -/
theorem isStrongEquilibrium_optContract [Finite ι] (t : (ι → Bool) → ℝ) (c : ι → ℝ)
    (a : ι → Bool) (ht : IsStrictlyMonotone t) (hc : ∀ i, 0 ≤ c i) :
    (contractCostGame t c (optContract t c a)).IsStrongEquilibrium a := by
  intro A b hdev
  have hsub : ∀ j, A.piecewise b a j = true → a j = true := by
    intro j hj
    by_cases hjA : j ∈ A
    · cases haj : a j with
      | true => rfl
      | false =>
        have hlt := hdev.2 j hjA
        have hcost : (contractCostGame t c (optContract t c a)).cost j a = 0 := by
          simp [contractCostGame, optContract, haj]
        have hcost' :
            0 ≤ (contractCostGame t c (optContract t c a)).cost j (A.piecewise b a) := by
          simp only [contractCostGame, optContract, haj, Bool.false_eq_true, ↓reduceIte, zero_mul,
            sub_zero, hj]
          exact hc j
        linarith
    · simpa [Finset.piecewise, hjA] using hj
  obtain ⟨i, hiA⟩ := hdev.1
  have hle := cost_le_piecewise_of_subset t c a ht hc A b hsub i
  have hlt := hdev.2 i hiA
  linarith

/-- Under strictly positive effort costs `0 < c i`, `optContract t c a` implements `a` as a
**strong Nash equilibrium** (no coalition can weakly improve all members and strictly improve one,
NRTV Exercise 23.6). Notice strict positivity is necessary: with `c j = 0`, an agent with
`a j = false` can weakly profitably raise `a_j` to help a coalitional partner. -/
theorem isStrongNash_optContract [Finite ι] (t : (ι → Bool) → ℝ) (c : ι → ℝ) (a : ι → Bool)
    (ht : IsStrictlyMonotone t) (hc : ∀ i, 0 < c i) :
    (contractCostGame t c (optContract t c a)).IsStrongNash a := by
  have hcn : ∀ i, 0 ≤ c i := fun i => (hc i).le
  intro A b hdev
  have hsub : ∀ j, A.piecewise b a j = true → a j = true := by
    intro j hj
    by_cases hjA : j ∈ A
    · cases haj : a j with
      | true => rfl
      | false =>
        have hle := hdev.1 j hjA
        have hcost : (contractCostGame t c (optContract t c a)).cost j a = 0 := by
          simp [contractCostGame, optContract, haj]
        have hcost' :
            (contractCostGame t c (optContract t c a)).cost j (A.piecewise b a) = c j := by
          simp only [contractCostGame, optContract, haj, Bool.false_eq_true, ↓reduceIte, zero_mul,
            sub_zero, hj]
        have := hc j
        linarith
    · simpa [Finset.piecewise, hjA] using hj
  obtain ⟨i, _, hlt⟩ := hdev.2
  have hle := cost_le_piecewise_of_subset t c a ht hcn A b hsub i
  linarith

end CoreAgency

section WelfareAndPOU

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- Social welfare of effort profile `a` under full information when project success yields `v`
and agent costs are `c`: `t(a) * v - ∑_{a_i} c_i`. -/
def profileWelfare (t : (ι → Bool) → ℝ) (c : ι → ℝ) (a : ι → Bool) (v : ℝ) : ℝ :=
  t a * v - ∑ i, if a i then c i else 0

omit [DecidableEq ι] in
theorem profileWelfare_eq (t : (ι → Bool) → ℝ) (c : ι → ℝ) (a : ι → Bool) (v : ℝ) :
    profileWelfare t c a v = t a * v - ∑ i, if a i then c i else 0 := by
  rfl

/-- **First-best social welfare** (`SW_ns(v)`): maximum achievable total welfare without moral
hazard, `max_{a} (t(a) * v - ∑_{a_i} c_i)`. -/
noncomputable def firstBestWelfare (t : (ι → Bool) → ℝ) (c : ι → ℝ) (v : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun a => profileWelfare t c a v

theorem firstBestWelfare_eq (t : (ι → Bool) → ℝ) (c : ι → ℝ) (v : ℝ) :
    firstBestWelfare t c v =
      Finset.univ.sup' Finset.univ_nonempty fun a => profileWelfare t c a v := by
  rfl

/-- Expected utility of the principal when inducing profile `a` via `optContract t c a`:
`t(a) * v - optPayment t c a`. -/
noncomputable def principalUtility (t : (ι → Bool) → ℝ) (c : ι → ℝ)
    (a : ι → Bool) (v : ℝ) : ℝ :=
  t a * v - optPayment t c a

theorem principalUtility_eq (t : (ι → Bool) → ℝ) (c : ι → ℝ) (a : ι → Bool) (v : ℝ) :
    principalUtility t c a v = t a * v - optPayment t c a := by
  rfl

/-- **Hidden-action optimal principal utility** (`U_ag(v)`): maximum of
`principalUtility t c a v = t(a) * v - optPayment t c a` over action profiles `a`.
Under the §23.6.1 assumptions `IsStrictlyMonotone t` (`∀ i a, 0 < marginalContrib t i a`),
`0 ≤ t a ≤ 1`, and `∀ i, 0 ≤ c i`, every profile `a` is pure-Nash implementable via
`optContract t c a` (`isPureNash_optContract`) and no limited-liability contract implementing `a`
achieves smaller expected payment (`optPayment_le_of_limitedLiability`), so this equals the
maximum expected principal utility over all Nash-implementable limited-liability contracts. -/
noncomputable def agencyPrincipalUtility (t : (ι → Bool) → ℝ)
    (c : ι → ℝ) (v : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun a => principalUtility t c a v

theorem agencyPrincipalUtility_eq (t : (ι → Bool) → ℝ) (c : ι → ℝ) (v : ℝ) :
    agencyPrincipalUtility t c v =
      Finset.univ.sup' Finset.univ_nonempty fun a => principalUtility t c a v := by
  rfl

theorem profileWelfare_le_firstBestWelfare (t : (ι → Bool) → ℝ) (c : ι → ℝ) (a : ι → Bool)
    (v : ℝ) : profileWelfare t c a v ≤ firstBestWelfare t c v :=
  Finset.le_sup' (fun a => profileWelfare t c a v) (mem_univ a)

theorem principalUtility_le_agencyPrincipalUtility (t : (ι → Bool) → ℝ) (c : ι → ℝ)
    (a : ι → Bool) (v : ℝ) : principalUtility t c a v ≤ agencyPrincipalUtility t c v :=
  Finset.le_sup' (fun a => principalUtility t c a v) (mem_univ a)

theorem sum_costs_le_optPayment (t : (ι → Bool) → ℝ) (c : ι → ℝ) (a : ι → Bool)
    (ht0 : ∀ s, 0 ≤ t s) (hΔ : ∀ i, 0 < marginalContrib t i a) (hc : ∀ i, 0 ≤ c i) :
    (∑ i, if a i then c i else 0) ≤ optPayment t c a := by
  have hterm : ∀ i, (if a i then c i else 0) ≤ optContract t c a i * t a := by
    intro i
    cases hai : a i with
    | false => simp [optContract, hai]
    | true =>
      have hself : Function.update a i true = a := Function.update_eq_self_iff.mpr hai.symm
      have hm_le : marginalContrib t i a ≤ t a := by
        rw [marginalContrib, hself]
        linarith [ht0 (Function.update a i false)]
      simp only [optContract, hai, ↓reduceIte]
      have hopt_nn : 0 ≤ c i / marginalContrib t i a := div_nonneg (hc i) (hΔ i).le
      calc
        c i = (c i / marginalContrib t i a) * marginalContrib t i a :=
          (div_mul_cancel₀ (c i) (hΔ i).ne').symm
        _ ≤ (c i / marginalContrib t i a) * t a := mul_le_mul_of_nonneg_left hm_le hopt_nn
  calc
    (∑ i, if a i then c i else 0) ≤ ∑ i, optContract t c a i * t a :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = optPayment t c a := by
      simp [optPayment, Finset.mul_sum, mul_comm]

theorem agencyPrincipalUtility_le_firstBestWelfare (t : (ι → Bool) → ℝ)
    (c : ι → ℝ) (ht0 : ∀ s, 0 ≤ t s) (hΔ : ∀ i s, 0 < marginalContrib t i s)
    (hc : ∀ i, 0 ≤ c i) (v : ℝ) :
    agencyPrincipalUtility t c v ≤ firstBestWelfare t c v := by
  refine Finset.sup'_le Finset.univ_nonempty _ fun a _ => ?_
  calc
    principalUtility t c a v ≤ profileWelfare t c a v := by
      simp only [principalUtility, profileWelfare]
      linarith [sum_costs_le_optPayment t c a ht0 (fun i => hΔ i a) hc]
    _ ≤ firstBestWelfare t c v := profileWelfare_le_firstBestWelfare t c a v

theorem agencyPrincipalUtility_pos (t : (ι → Bool) → ℝ) (c : ι → ℝ)
    (htpos : ∀ s, 0 < t s) {v : ℝ} (hv : 0 < v) :
    0 < agencyPrincipalUtility t c v := by
  have h0 : principalUtility t c (fun _ => false) v = t (fun _ => false) * v := by
    simp [principalUtility, optPayment_false]
  calc
    0 < t (fun _ => false) * v := mul_pos (htpos _) hv
    _ = principalUtility t c (fun _ => false) v := h0.symm
    _ ≤ agencyPrincipalUtility t c v := principalUtility_le_agencyPrincipalUtility t c _ v

private theorem affineSup_mono {α : Type*} [Fintype α] [Nonempty α] (prob cost : α → ℝ)
    (hprob : ∀ a, 0 ≤ prob a) {v₁ v₂ : ℝ} (hv : v₁ ≤ v₂) :
    Finset.univ.sup' Finset.univ_nonempty (fun a => prob a * v₁ - cost a) ≤
      Finset.univ.sup' Finset.univ_nonempty (fun a => prob a * v₂ - cost a) := by
  refine Finset.sup'_le Finset.univ_nonempty _ fun a ha => ?_
  calc
    prob a * v₁ - cost a ≤ prob a * v₂ - cost a := by
      nlinarith [hprob a]
    _ ≤ Finset.univ.sup' Finset.univ_nonempty (fun b => prob b * v₂ - cost b) :=
      Finset.le_sup' (fun b => prob b * v₂ - cost b) ha

private theorem affineSup_maximizer_mono {α : Type*} {prob cost : α → ℝ} {a₁ a₂ : α}
    {v₁ v₂ : ℝ} (hmax₁ : prob a₂ * v₁ - cost a₂ ≤ prob a₁ * v₁ - cost a₁)
    (hmax₂ : prob a₁ * v₂ - cost a₁ ≤ prob a₂ * v₂ - cost a₂)
    (hv : v₁ < v₂) :
    prob a₁ ≤ prob a₂ := by
  have h1 : (prob a₁ - prob a₂) * (v₂ - v₁) ≤ 0 := by linarith
  have hpos : 0 < v₂ - v₁ := sub_pos.mpr hv
  have : prob a₁ - prob a₂ ≤ 0 := nonpos_of_mul_nonpos_left h1 hpos
  linarith

private theorem affineSup_maximizer_cost_mono {α : Type*} {prob cost : α → ℝ} {a₁ a₂ : α}
    {v₁ v₂ : ℝ} (hmax₁ : prob a₂ * v₁ - cost a₂ ≤ prob a₁ * v₁ - cost a₁)
    (hmax₂ : prob a₁ * v₂ - cost a₁ ≤ prob a₂ * v₂ - cost a₂)
    (hv₀ : 0 ≤ v₁) (hv : v₁ < v₂) :
    cost a₁ ≤ cost a₂ := by
  have hp : prob a₁ ≤ prob a₂ := affineSup_maximizer_mono hmax₁ hmax₂ hv
  have hprod : (prob a₁ - prob a₂) * v₁ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hv₀
  linarith

theorem firstBestWelfare_mono (t : (ι → Bool) → ℝ) (c : ι → ℝ) (ht0 : ∀ s, 0 ≤ t s)
    {v₁ v₂ : ℝ} (hv : v₁ ≤ v₂) :
    firstBestWelfare t c v₁ ≤ firstBestWelfare t c v₂ :=
  affineSup_mono t (fun a => ∑ i, if a i then c i else 0) ht0 hv

theorem agencyPrincipalUtility_mono (t : (ι → Bool) → ℝ) (c : ι → ℝ)
    (ht0 : ∀ s, 0 ≤ t s) {v₁ v₂ : ℝ} (hv : v₁ ≤ v₂) :
    agencyPrincipalUtility t c v₁ ≤ agencyPrincipalUtility t c v₂ :=
  affineSup_mono t (optPayment t c) ht0 hv

/-- **Monotonicity Lemma** for first-best welfare (NRTV Lemma 23.7): as the principal's value `v`
strictly increases (`0 ≤ v₁ < v₂`), any sequence of optimal profiles has nondecreasing success
probability `t(a₁) ≤ t(a₂)` and nondecreasing effort cost. -/
theorem monotonicity_firstBest (t : (ι → Bool) → ℝ) (c : ι → ℝ) {v₁ v₂ : ℝ}
    {a₁ a₂ : ι → Bool}
    (h₁ : profileWelfare t c a₁ v₁ = firstBestWelfare t c v₁)
    (h₂ : profileWelfare t c a₂ v₂ = firstBestWelfare t c v₂)
    (hv₀ : 0 ≤ v₁) (hv : v₁ < v₂) :
    t a₁ ≤ t a₂ ∧ (∑ i, if a₁ i then c i else 0) ≤ ∑ i, if a₂ i then c i else 0 := by
  have hm₁ : profileWelfare t c a₂ v₁ ≤ profileWelfare t c a₁ v₁ := by
    rw [h₁]; exact profileWelfare_le_firstBestWelfare t c a₂ v₁
  have hm₂ : profileWelfare t c a₁ v₂ ≤ profileWelfare t c a₂ v₂ := by
    rw [h₂]; exact profileWelfare_le_firstBestWelfare t c a₁ v₂
  simp only [profileWelfare] at hm₁ hm₂
  let costFn : (ι → Bool) → ℝ := fun a => ∑ i, if a i then c i else 0
  exact ⟨affineSup_maximizer_mono (prob := t) (cost := costFn) hm₁ hm₂ hv,
    affineSup_maximizer_cost_mono (prob := t) (cost := costFn) hm₁ hm₂ hv₀ hv⟩

/-- **Monotonicity Lemma** for hidden-action principal utility (NRTV Lemma 23.7): as the
principal's value `v` strictly increases (`0 ≤ v₁ < v₂`), optimal contracts achieve nondecreasing
success probability `t(a₁) ≤ t(a₂)` and incur nondecreasing expected payment `optPayment`. -/
theorem monotonicity_agency (t : (ι → Bool) → ℝ) (c : ι → ℝ) {v₁ v₂ : ℝ}
    {a₁ a₂ : ι → Bool}
    (h₁ : principalUtility t c a₁ v₁ = agencyPrincipalUtility t c v₁)
    (h₂ : principalUtility t c a₂ v₂ = agencyPrincipalUtility t c v₂)
    (hv₀ : 0 ≤ v₁) (hv : v₁ < v₂) :
    t a₁ ≤ t a₂ ∧ optPayment t c a₁ ≤ optPayment t c a₂ := by
  have hm₁ : principalUtility t c a₂ v₁ ≤ principalUtility t c a₁ v₁ := by
    rw [h₁]; exact principalUtility_le_agencyPrincipalUtility t c a₂ v₁
  have hm₂ : principalUtility t c a₁ v₂ ≤ principalUtility t c a₂ v₂ := by
    rw [h₂]; exact principalUtility_le_agencyPrincipalUtility t c a₁ v₂
  simp only [principalUtility] at hm₁ hm₂
  exact ⟨affineSup_maximizer_mono (cost := optPayment t c) hm₁ hm₂ hv,
    affineSup_maximizer_cost_mono (cost := optPayment t c) hm₁ hm₂ hv₀ hv⟩

/-- **Price of Unaccountability** (`POU(t, c)`, NRTV Definition 23.6): worst-case ratio
`sup_{v > 0} SW_ns(v) / U_ag(v)` measuring welfare loss from hidden action under limited
liability. -/
noncomputable def priceOfUnaccountability (t : (ι → Bool) → ℝ)
    (c : ι → ℝ) : ℝ :=
  ⨆ v : {v : ℝ // 0 < v}, firstBestWelfare t c v.1 / agencyPrincipalUtility t c v.1

theorem priceOfUnaccountability_eq (t : (ι → Bool) → ℝ) (c : ι → ℝ) :
    priceOfUnaccountability t c =
      ⨆ v : {v : ℝ // 0 < v}, firstBestWelfare t c v.1 / agencyPrincipalUtility t c v.1 := by
  rfl

theorem bddAbove_pou_range (t : (ι → Bool) → ℝ) (c : ι → ℝ)
    (htpos : ∀ s, 0 < t s) (hc : ∀ i, 0 ≤ c i) :
    BddAbove (Set.range fun v : {v : ℝ // 0 < v} =>
      firstBestWelfare t c v.1 / agencyPrincipalUtility t c v.1) := by
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty t / t (fun _ => false)
  refine ⟨M, ?_⟩
  rintro _ ⟨⟨v, hv⟩, rfl⟩
  have hU_pos : 0 < agencyPrincipalUtility t c v := agencyPrincipalUtility_pos t c htpos hv
  have hU_ge : t (fun _ => false) * v ≤ agencyPrincipalUtility t c v := by
    have h0 : principalUtility t c (fun _ => false) v = t (fun _ => false) * v := by
      simp [principalUtility, optPayment_false]
    rw [← h0]
    exact principalUtility_le_agencyPrincipalUtility t c _ v
  have hSW_le : firstBestWelfare t c v ≤ Finset.univ.sup' Finset.univ_nonempty t * v := by
    refine Finset.sup'_le Finset.univ_nonempty _ fun a _ => ?_
    have hcost : 0 ≤ ∑ i, if a i then c i else 0 :=
      Finset.sum_nonneg fun i _ => by split_ifs <;> [exact hc i; exact le_rfl]
    have hta : t a ≤ Finset.univ.sup' Finset.univ_nonempty t := Finset.le_sup' t (mem_univ a)
    simp only [profileWelfare]
    nlinarith
  have htf_pos : 0 < t (fun _ => false) * v := mul_pos (htpos _) hv
  rw [div_le_iff₀ hU_pos]
  calc
    firstBestWelfare t c v ≤ Finset.univ.sup' Finset.univ_nonempty t * v := hSW_le
    _ = M * (t (fun _ => false) * v) := by
      dsimp [M]
      field_simp [(htpos _).ne']
    _ ≤ M * agencyPrincipalUtility t c v := by
      refine mul_le_mul_of_nonneg_left hU_ge ?_
      dsimp [M]
      exact div_nonneg
        ((htpos (fun _ => false)).le.trans (Finset.le_sup' t (mem_univ _)))
        (htpos _).le

theorem le_priceOfUnaccountability (t : (ι → Bool) → ℝ) (c : ι → ℝ)
    (htpos : ∀ s, 0 < t s) (hc : ∀ i, 0 ≤ c i) {v : ℝ} (hv : 0 < v) :
    firstBestWelfare t c v / agencyPrincipalUtility t c v ≤ priceOfUnaccountability t c :=
  le_ciSup (bddAbove_pou_range t c htpos hc) ⟨v, hv⟩

theorem priceOfUnaccountability_le_iff (t : (ι → Bool) → ℝ) (c : ι → ℝ)
    (htpos : ∀ s, 0 < t s) (hc : ∀ i, 0 ≤ c i) {B : ℝ} :
    priceOfUnaccountability t c ≤ B ↔
      ∀ v : ℝ, 0 < v → firstBestWelfare t c v ≤ B * agencyPrincipalUtility t c v := by
  have : Nonempty {v : ℝ // 0 < v} := ⟨⟨1, zero_lt_one⟩⟩
  rw [priceOfUnaccountability, ciSup_le_iff (bddAbove_pou_range t c htpos hc)]
  constructor
  · intro h v hv
    have hU := agencyPrincipalUtility_pos t c htpos hv
    exact (div_le_iff₀ hU).mp (h ⟨v, hv⟩)
  · rintro h ⟨v, hv⟩
    exact (div_le_iff₀ (agencyPrincipalUtility_pos t c htpos hv)).mpr (h v hv)

theorem one_le_priceOfUnaccountability (t : (ι → Bool) → ℝ) (c : ι → ℝ)
    (htpos : ∀ s, 0 < t s) (hΔ : ∀ i s, 0 < marginalContrib t i s) (hc : ∀ i, 0 ≤ c i) :
    1 ≤ priceOfUnaccountability t c := by
  have ht0 : ∀ s, 0 ≤ t s := fun s => (htpos s).le
  have h1 : 1 ≤ firstBestWelfare t c 1 / agencyPrincipalUtility t c 1 :=
    (one_le_div (agencyPrincipalUtility_pos t c htpos zero_lt_one)).mpr
      (agencyPrincipalUtility_le_firstBestWelfare t c ht0 hΔ hc 1)
  exact h1.trans (le_priceOfUnaccountability t c htpos hc zero_lt_one)

end WelfareAndPOU

section AnonymousAndExamples

open Finset

/-- Number of agents exerting effort (`true`) in profile `a`. -/
def countTrue {n : ℕ} (a : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => a i = true).card

theorem countTrue_eq {n : ℕ} (a : Fin n → Bool) :
    countTrue a = (Finset.univ.filter fun i => a i = true).card := by
  rfl

theorem countTrue_le {n : ℕ} (a : Fin n → Bool) : countTrue a ≤ n := by
  calc
    countTrue a ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := Fintype.card_fin n

theorem countTrue_false {n : ℕ} : countTrue (fun _ : Fin n => false) = 0 := by
  simp [countTrue]

theorem countTrue_true {n : ℕ} : countTrue (fun _ : Fin n => true) = n := by
  simp [countTrue]

theorem exists_profile_countTrue {n k : ℕ} (hk : k ≤ n) :
    ∃ a : Fin n → Bool, countTrue a = k := by
  refine ⟨fun i => decide (i.val < k), ?_⟩
  rw [countTrue]
  have himg : (Finset.univ : Finset (Fin k)).map
      ⟨Fin.castLE hk, Fin.castLE_injective hk⟩ =
      Finset.univ.filter (fun i : Fin n => decide (i.val < k) = true) := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter, decide_eq_true_eq]
    exact ⟨fun ⟨j, hji⟩ => by subst hji; exact j.isLt, fun hi => ⟨⟨i.val, hi⟩, Fin.ext rfl⟩⟩
  rw [← himg, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem countTrue_update_false {n : ℕ} {a : Fin n → Bool} {i : Fin n} (hai : a i = true) :
    countTrue (Function.update a i false) = countTrue a - 1 := by
  have hmem : i ∈ Finset.univ.filter (fun j => a j = true) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hai⟩
  have heq : Finset.univ.filter (fun j => Function.update a i false j = true) =
      (Finset.univ.filter (fun j => a j = true)).erase i := by
    ext j
    by_cases hji : j = i
    · subst hji; simp
    · simp only [mem_filter, mem_univ, true_and, mem_erase, ne_eq, Function.update_of_ne hji]
      exact ⟨fun h => ⟨hji, h⟩, fun h => h.2⟩
  rw [countTrue, countTrue, heq, Finset.card_erase_of_mem hmem]

theorem countTrue_pos_of_true {n : ℕ} {a : Fin n → Bool} {i : Fin n} (hai : a i = true) :
    0 < countTrue a :=
  Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hai⟩⟩

/-- Minimal expected payment under an anonymous technology `t(a) = f (countTrue a)` and
uniform effort cost `c` as a function of team size `k`. -/
noncomputable def anonOptPayment (f : ℕ → ℝ) (c : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else (k : ℝ) * c * f k / (f k - f (k - 1))

theorem anonOptPayment_eq (f : ℕ → ℝ) (c : ℝ) (k : ℕ) :
    anonOptPayment f c k = if k = 0 then 0 else (k : ℝ) * c * f k / (f k - f (k - 1)) := by
  rfl

@[simp]
theorem anonOptPayment_zero (f : ℕ → ℝ) (c : ℝ) : anonOptPayment f c 0 = 0 := by
  simp [anonOptPayment]

@[simp]
theorem anonOptPayment_succ (f : ℕ → ℝ) (c : ℝ) (k : ℕ) :
    anonOptPayment f c (k + 1) =
      ((k + 1 : ℕ) : ℝ) * c * f (k + 1) / (f (k + 1) - f k) := by
  simp [anonOptPayment]

theorem anon_marginalContrib {n : ℕ} {t : (Fin n → Bool) → ℝ} {f : ℕ → ℝ}
    (ht : ∀ a, t a = f (countTrue a)) {a : Fin n → Bool} {i : Fin n} (hai : a i = true) :
    marginalContrib t i a = f (countTrue a) - f (countTrue a - 1) := by
  have hupd : Function.update a i true = a := Function.update_eq_self_iff.mpr hai.symm
  rw [marginalContrib, hupd, ht, ht, countTrue_update_false hai]

theorem anon_optPayment {n : ℕ} {t : (Fin n → Bool) → ℝ} {f : ℕ → ℝ}
    (ht : ∀ a, t a = f (countTrue a)) (c : ℝ) (a : Fin n → Bool) :
    optPayment t (fun _ => c) a = anonOptPayment f c (countTrue a) := by
  by_cases hk : countTrue a = 0
  · have hnone : ∀ i, a i = false := by
      intro i
      cases hai : a i with
      | false => rfl
      | true => exact False.elim ((countTrue_pos_of_true hai).ne' hk)
    have ha0 : a = fun _ => false := funext hnone
    rw [ha0, optPayment_false, anonOptPayment, countTrue_false]
    simp
  · simp only [optPayment, anonOptPayment, hk, ↓reduceIte, ht a]
    have hsum : (∑ i : Fin n, optContract t (fun _ => c) a i) =
        (countTrue a : ℝ) * (c / (f (countTrue a) - f (countTrue a - 1))) := by
      have hterm : ∀ i : Fin n, optContract t (fun _ => c) a i =
          if a i = true then c / (f (countTrue a) - f (countTrue a - 1)) else 0 := by
        intro i
        cases hai : a i with
        | false => simp [optContract, hai]
        | true => simp [optContract, hai, anon_marginalContrib ht hai]
      simp_rw [hterm, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
        nsmul_eq_mul]
      simp only [countTrue]
    rw [hsum]
    ring

theorem anon_sum_costs {n : ℕ} (c : ℝ) (a : Fin n → Bool) :
    (∑ i : Fin n, if a i then c else 0) = (countTrue a : ℝ) * c := by
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    countTrue]

private theorem affineSup_anon {n : ℕ} {t : (Fin n → Bool) → ℝ} {f : ℕ → ℝ}
    (ht : ∀ a, t a = f (countTrue a)) (cost : ℕ → ℝ) (v : ℝ) :
    Finset.univ.sup' Finset.univ_nonempty (fun a : Fin n → Bool => t a * v - cost (countTrue a)) =
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => f k * v - cost k := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le Finset.univ_nonempty _ fun a _ => ?_
    rw [ht a]
    exact Finset.le_sup' (fun k => f k * v - cost k)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (countTrue_le a)))
  · refine Finset.sup'_le Finset.nonempty_range_add_one _ fun k hk => ?_
    obtain ⟨a, ha⟩ := exists_profile_countTrue (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    calc
      f k * v - cost k = t a * v - cost (countTrue a) := by rw [ht a, ha]
      _ ≤ Finset.univ.sup' Finset.univ_nonempty (fun b => t b * v - cost (countTrue b)) :=
        Finset.le_sup' (fun b : Fin n → Bool => t b * v - cost (countTrue b)) (mem_univ a)

theorem firstBestWelfare_anon {n : ℕ} {t : (Fin n → Bool) → ℝ} {f : ℕ → ℝ}
    (ht : ∀ a, t a = f (countTrue a)) (c v : ℝ) :
    firstBestWelfare t (fun _ => c) v =
      (Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩
        fun k => f k * v - (k : ℝ) * c := by
  simp only [firstBestWelfare, profileWelfare]
  have h : (fun a : Fin n → Bool => t a * v - ∑ i, if a i then c else 0) =
      fun a => t a * v - (countTrue a : ℝ) * c := by
    ext a; rw [anon_sum_costs]
  rw [h]
  exact affineSup_anon ht (fun k => (k : ℝ) * c) v

theorem agencyPrincipalUtility_anon {n : ℕ} {t : (Fin n → Bool) → ℝ} {f : ℕ → ℝ}
    (ht : ∀ a, t a = f (countTrue a)) (c v : ℝ) :
    agencyPrincipalUtility t (fun _ => c) v =
      (Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩
        fun k => f k * v - anonOptPayment f c k := by
  simp only [agencyPrincipalUtility, principalUtility]
  have h : (fun a : Fin n → Bool => t a * v - optPayment t (fun _ => c) a) =
      fun a => t a * v - anonOptPayment f c (countTrue a) := by
    ext a; rw [anon_optPayment ht]
  rw [h]
  exact affineSup_anon ht (anonOptPayment f c) v

private theorem isStrictlyMonotone_of_anon {n : ℕ} {t : (Fin n → Bool) → ℝ} {f : ℕ → ℝ}
    (ht : ∀ a, t a = f (countTrue a)) (hf : ∀ k, k < n → f k < f (k + 1)) :
    IsStrictlyMonotone t := by
  rw [isStrictlyMonotone_iff_marginalContrib_pos]
  intro i a
  by_cases hai : a i = true
  · rw [anon_marginalContrib ht hai]
    have hpos := countTrue_pos_of_true hai
    have hlt := hf (countTrue a - 1) (by have := countTrue_le a; omega)
    rw [Nat.sub_add_cancel hpos] at hlt
    exact sub_pos.mpr hlt
  · have hupd : Function.update a i true i = true := Function.update_self i true a
    rw [← marginalContrib_update t i a true, anon_marginalContrib ht hupd]
    have hpos := countTrue_pos_of_true hupd
    have hlt := hf (countTrue (Function.update a i true) - 1)
      (by have := countTrue_le (Function.update a i true); omega)
    rw [Nat.sub_add_cancel hpos] at hlt
    exact sub_pos.mpr hlt

/-- Slope-monotonicity criterion (NRTV Exercise 23.5, skipping case): if `f` is strictly
increasing on `0..n` and marginal cost per marginal success probability strictly decreases around
every interior team size `0 < k < n`, then no interior size `k` ever strictly maximizes
`f k * v - cost k`, and the supremum reduces to `max (f 0 * v - cost 0) (f n * v - cost n)`. -/
theorem strictly_decreasing_slope_skips {n : ℕ} (hn : 1 ≤ n) (f cost : ℕ → ℝ)
    (hf : ∀ k, k < n → f k < f (k + 1))
    (hslope : ∀ k, 0 < k → k < n →
      (cost (k + 1) - cost k) / (f (k + 1) - f k) <
        (cost k - cost (k - 1)) / (f k - f (k - 1)))
    (v : ℝ) :
    ((Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩
        fun k => f k * v - cost k) =
        max (f 0 * v - cost 0) (f n * v - cost n) ∧
      ∀ k, 0 < k → k < n →
        f k * v - cost k <
          max (f (k - 1) * v - cost (k - 1)) (f (k + 1) * v - cost (k + 1)) := by
  have hinterior : ∀ k, 0 < k → k < n →
      f k * v - cost k <
        max (f (k - 1) * v - cost (k - 1)) (f (k + 1) * v - cost (k + 1)) := by
    intro k hk0 hkn
    have hdf₁ : 0 < f k - f (k - 1) :=
      sub_pos.mpr (by simpa [Nat.sub_add_cancel hk0] using hf (k - 1) (by omega))
    have hdf₂ : 0 < f (k + 1) - f k := sub_pos.mpr (hf k hkn)
    by_cases hv : v < (cost k - cost (k - 1)) / (f k - f (k - 1))
    · rw [lt_div_iff₀ hdf₁] at hv
      exact lt_max_of_lt_left (by linarith)
    · have hv₂ := (hslope k hk0 hkn).trans_le (not_lt.mp hv)
      rw [div_lt_iff₀ hdf₂] at hv₂
      exact lt_max_of_lt_right (by linarith)
  have hle : ∀ j ≤ n, f j * v - cost j ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun j => f j * v - cost j :=
    fun j hj => Finset.le_sup' (fun j => f j * v - cost j) (Finset.mem_range.mpr (by omega))
  refine ⟨le_antisymm ?_ (max_le (hle 0 (Nat.zero_le n)) (hle n le_rfl)), hinterior⟩
  obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup' (Finset.nonempty_range_add_one (n := n))
    (fun j => f j * v - cost j)
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [hjeq]
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact le_max_left _ _
  rcases hjn.eq_or_lt with rfl | hjn
  · exact le_max_right _ _
  exact absurd (hinterior j hj0 hjn)
    (not_lt.mpr ((max_le (hle (j - 1) (by omega)) (hle (j + 1) hjn)).trans hjeq.le))

/-- A sequence that strictly increases at each step from `a` to `b` satisfies `g a < g b`. -/
private theorem lt_of_forall_lt_succ {g : ℕ → ℝ} {a : ℕ} :
    ∀ {b}, a < b → (∀ m, a ≤ m → m < b → g m < g (m + 1)) → g a < g b
  | 0, hab, _ => absurd hab (Nat.not_lt_zero a)
  | b + 1, hab, h => by
    rcases (Nat.lt_succ_iff.mp hab).eq_or_lt with rfl | hab
    · exact h a le_rfl a.lt_succ_self
    · exact (lt_of_forall_lt_succ hab fun m h1 h2 => h m h1 (by omega)).trans
        (h b hab.le b.lt_succ_self)

/-- Slope-monotonicity criterion (NRTV Exercise 23.5, stepping case): if `f` is strictly
increasing on `0..n` and marginal cost per marginal success probability strictly increases with
each step (with positive initial slope), then every team size `k ≤ n` is uniquely optimal for
some `v > 0`. -/
theorem strictly_increasing_slope_attains_all {n : ℕ} (hn : 1 ≤ n) (f cost : ℕ → ℝ)
    (hf : ∀ k, k < n → f k < f (k + 1))
    (hs₀ : 0 < (cost 1 - cost 0) / (f 1 - f 0))
    (hslope : ∀ k, k + 1 < n →
      (cost (k + 1) - cost k) / (f (k + 1) - f k) <
        (cost (k + 2) - cost (k + 1)) / (f (k + 2) - f (k + 1))) :
    ∀ k, k ≤ n → ∃ v : ℝ, 0 < v ∧
      ∀ j, j ≤ n → j ≠ k → f j * v - cost j < f k * v - cost k := by
  let s : ℕ → ℝ := fun m => (cost (m + 1) - cost m) / (f (m + 1) - f m)
  have hs_lt : ∀ a b, a < b → b < n → s a < s b := fun a b hab hb =>
    lt_of_forall_lt_succ hab fun m _ hm => hslope m (by omega)
  have hs_le : ∀ a b, a ≤ b → b < n → s a ≤ s b := fun a b hab hb =>
    hab.eq_or_lt.elim (fun h => h ▸ le_rfl) fun h => (hs_lt a b h hb).le
  have hs_pos : ∀ m, m < n → 0 < s m := fun m hm => hs₀.trans_le (hs_le 0 m m.zero_le hm)
  have step_up : ∀ (v : ℝ) (m : ℕ), m < n → s m < v →
      f m * v - cost m < f (m + 1) * v - cost (m + 1) := by
    intro v m hm hsv
    simp only [s] at hsv
    rw [div_lt_iff₀ (sub_pos.mpr (hf m hm))] at hsv
    linarith
  have step_down : ∀ (v : ℝ) (m : ℕ), m < n → v < s m →
      f (m + 1) * v - cost (m + 1) < f m * v - cost m := by
    intro v m hm hvs
    simp only [s] at hvs
    rw [lt_div_iff₀ (sub_pos.mpr (hf m hm))] at hvs
    linarith
  intro k hk
  obtain ⟨v, hvpos, hleft, hright⟩ : ∃ v : ℝ, 0 < v ∧ (∀ m, m < k → s m < v) ∧
      (∀ m, k ≤ m → m < n → v < s m) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact ⟨s 0 / 2, half_pos hs₀, fun m hm => absurd hm m.not_lt_zero,
        fun m _ hmn => (half_lt_self hs₀).trans_le (hs_le 0 m m.zero_le hmn)⟩
    rcases hk.eq_or_lt with rfl | hkn
    · exact ⟨s (k - 1) + 1, by linarith [hs_pos (k - 1) (by omega)],
        fun m hm => by linarith [hs_le m (k - 1) (by omega) (by omega)], fun m _ _ => by omega⟩
    have hlt : s (k - 1) < s k := hs_lt (k - 1) k (by omega) hkn
    exact ⟨(s (k - 1) + s k) / 2, by linarith [hs_pos (k - 1) (by omega)],
      fun m hm => by linarith [hs_le m (k - 1) (by omega) (by omega)],
      fun m hkm hmn => by linarith [hs_le k m hkm hmn]⟩
  refine ⟨v, hvpos, fun j hj hne => ?_⟩
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · exact lt_of_forall_lt_succ (g := fun m => f m * v - cost m) hjk
      fun m _ hm => step_up v m (by omega) (hleft m hm)
  · exact neg_lt_neg_iff.mp (lt_of_forall_lt_succ (g := fun m => -(f m * v - cost m)) hkj
      fun m hm _ => neg_lt_neg (step_down v m (by omega) (hright m hm (by omega))))

/-! ### AND technology (NRTV Theorem 23.8 and Exercise 23.3) -/

/-- Success probability as a function of `k` active agents in the noisy `n`-agent AND
technology: `(1 - γ) ^ k * γ ^ (n - k)`. -/
def andProb (n : ℕ) (γ : ℝ) (k : ℕ) : ℝ :=
  (1 - γ) ^ k * γ ^ (n - k)

theorem andProb_eq (n : ℕ) (γ : ℝ) (k : ℕ) :
    andProb n γ k = (1 - γ) ^ k * γ ^ (n - k) := by
  rfl

/-- Noisy `n`-agent **AND technology** with parameter `γ`: each agent exerts effort with failure
probability `γ` on effort and success probability `γ` on shirking, so all `n` signals must
succeed with probability `(1 - γ) ^ k * γ ^ (n - k)`. -/
def andTech (n : ℕ) (γ : ℝ) (a : Fin n → Bool) : ℝ :=
  andProb n γ (countTrue a)

theorem andTech_eq (n : ℕ) (γ : ℝ) (a : Fin n → Bool) :
    andTech n γ a = andProb n γ (countTrue a) := by
  rfl

theorem andProb_pos {n : ℕ} {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1) (k : ℕ) :
    0 < andProb n γ k :=
  mul_pos (pow_pos (sub_pos.mpr hγ₁) k) (pow_pos hγ₀ (n - k))

theorem andTech_pos {n : ℕ} {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1) (a : Fin n → Bool) :
    0 < andTech n γ a :=
  andProb_pos hγ₀ hγ₁ _

theorem andProb_diff {n : ℕ} (γ : ℝ) {k : ℕ} (hk : k < n) :
    andProb n γ (k + 1) - andProb n γ k =
      (1 - 2 * γ) * (1 - γ) ^ k * γ ^ (n - k - 1) := by
  have hnk1 : n - k = (n - k - 1) + 1 := by omega
  have hnk2 : n - (k + 1) = n - k - 1 := by omega
  dsimp [andProb]
  rw [hnk2]
  nth_rw 2 [hnk1]
  rw [pow_succ (1 - γ) k, pow_succ γ (n - k - 1)]
  ring

theorem andProb_strictMono {n : ℕ} {γ : ℝ} (hγ₀ : 0 < γ) (hγh : γ < 1 / 2) {k : ℕ} (hk : k < n) :
    andProb n γ k < andProb n γ (k + 1) := by
  rw [← sub_pos, andProb_diff γ hk]
  exact mul_pos (mul_pos (by linarith) (pow_pos (by linarith) k)) (pow_pos hγ₀ _)

theorem isStrictlyMonotone_andTech (n : ℕ) {γ : ℝ} (hγ₀ : 0 < γ) (hγh : γ < 1 / 2) :
    IsStrictlyMonotone (andTech n γ) :=
  isStrictlyMonotone_of_anon (fun _ => rfl) fun _ hk => andProb_strictMono hγ₀ hγh hk

theorem and_anonOptPayment {n : ℕ} {γ : ℝ} (hγ₀ : 0 < γ) (hγh : γ < 1 / 2) (c : ℝ)
    {k : ℕ} (hk : k ≤ n) :
    anonOptPayment (andProb n γ) c k = (k : ℝ) * (c * (1 - γ) / (1 - 2 * γ)) := by
  by_cases hk0 : k = 0
  · subst hk0; simp [anonOptPayment]
  · have hpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hkn : k - 1 < n := by omega
    have hdiff := andProb_diff γ hkn
    rw [Nat.sub_add_cancel hpos] at hdiff
    have hnk : n - k = n - (k - 1) - 1 := by omega
    have hk_pow : (1 - γ) ^ k = (1 - γ) * (1 - γ) ^ (k - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hpos, pow_succ']
    have hdiff_ne : andProb n γ k - andProb n γ (k - 1) ≠ 0 := by
      rw [hdiff]
      exact (mul_pos (mul_pos (by linarith) (pow_pos (by linarith) _)) (pow_pos hγ₀ _)).ne'
    have h12γ : 1 - 2 * γ ≠ 0 := by linarith
    simp only [anonOptPayment, hk0, ↓reduceIte]
    rw [hdiff, andProb, hnk, hk_pow]
    have hq_ne : (1 - γ) ^ (k - 1) ≠ 0 := (pow_pos (by linarith) _).ne'
    have hg_ne : γ ^ (n - (k - 1) - 1) ≠ 0 := (pow_pos hγ₀ _).ne'
    field_simp [h12γ, hq_ne, hg_ne]

/-- Exact hidden-action value threshold at which the principal transitions directly from inducing
`0` agents to inducing all `n` agents under `andTech n γ` (NRTV Theorem 23.8). -/
noncomputable def andThreshold (n : ℕ) (γ c : ℝ) : ℝ :=
  (n : ℝ) * c * (1 - γ) / ((1 - 2 * γ) * ((1 - γ) ^ n - γ ^ n))

theorem andThreshold_eq (n : ℕ) (γ c : ℝ) :
    andThreshold n γ c = (n : ℝ) * c * (1 - γ) / ((1 - 2 * γ) * ((1 - γ) ^ n - γ ^ n)) := by
  rfl

theorem andThreshold_pos {n : ℕ} (hn : 1 ≤ n) {γ c : ℝ} (hγ₀ : 0 < γ) (hγh : γ < 1 / 2)
    (hc : 0 < c) : 0 < andThreshold n γ c := by
  have hpow : γ ^ n < (1 - γ) ^ n := pow_lt_pow_left₀ (by linarith) hγ₀.le (by omega)
  exact div_pos (mul_pos (mul_pos (Nat.cast_pos.mpr hn) hc) (by linarith))
    (mul_pos (by linarith) (sub_pos.mpr hpow))

private theorem andProb_diff_strictMono {n : ℕ} {γ : ℝ} (hγ₀ : 0 < γ) (hγh : γ < 1 / 2)
    {k : ℕ} (hkn : 0 < k) (hkn' : k < n) :
    andProb n γ k - andProb n γ (k - 1) < andProb n γ (k + 1) - andProb n γ k := by
  have hk1 : k - 1 < n := by omega
  have hd1 := andProb_diff γ hk1
  rw [Nat.sub_add_cancel hkn] at hd1
  have hd2 := andProb_diff γ hkn'
  rw [hd1, hd2]
  have hpowk : (1 - γ) ^ k = (1 - γ) * (1 - γ) ^ (k - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hkn, pow_succ']
  have hnk : n - (k - 1) - 1 = (n - k - 1) + 1 := by omega
  rw [hpowk, hnk, pow_succ]
  have hbase : 0 < (1 - 2 * γ) * (1 - γ) ^ (k - 1) * γ ^ (n - k - 1) :=
    mul_pos (mul_pos (by linarith) (pow_pos (by linarith) _)) (pow_pos hγ₀ _)
  have hγ_lt : γ < 1 - γ := by linarith
  calc
    (1 - 2 * γ) * (1 - γ) ^ (k - 1) * (γ ^ (n - k - 1) * γ) =
        ((1 - 2 * γ) * (1 - γ) ^ (k - 1) * γ ^ (n - k - 1)) * γ := by ring
    _ < ((1 - 2 * γ) * (1 - γ) ^ (k - 1) * γ ^ (n - k - 1)) * (1 - γ) :=
      mul_lt_mul_of_pos_left hγ_lt hbase
    _ = (1 - 2 * γ) * ((1 - γ) * (1 - γ) ^ (k - 1)) * γ ^ (n - k - 1) := by ring

private theorem and_linear_cost_skips {n : ℕ} (hn : 1 ≤ n) {γ a : ℝ} (hγ₀ : 0 < γ)
    (hγh : γ < 1 / 2) (ha : 0 < a) (v : ℝ) :
    ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        fun k => andProb n γ k * v - (k : ℝ) * a) =
      max (γ ^ n * v) ((1 - γ) ^ n * v - (n : ℝ) * a) := by
  have h := (strictly_decreasing_slope_skips hn (andProb n γ) (fun k => (k : ℝ) * a)
    (fun k hk => andProb_strictMono hγ₀ hγh hk)
    (fun k hk0 hkn => by
      have hdf₁ : 0 < andProb n γ k - andProb n γ (k - 1) := by
        have hlt := andProb_strictMono hγ₀ hγh (by omega : k - 1 < n)
        rw [Nat.sub_add_cancel hk0] at hlt
        exact sub_pos.mpr hlt
      have hnum₁ : ((k : ℝ) * a - ((k - 1 : ℕ) : ℝ) * a) = a := by
        rw [Nat.cast_sub hk0]; ring
      have hnum₂ : (((k + 1 : ℕ) : ℝ) * a - (k : ℝ) * a) = a := by
        push_cast; ring
      rw [hnum₁, hnum₂]
      exact div_lt_div_of_pos_left ha hdf₁ (andProb_diff_strictMono hγ₀ hγh hk0 hkn)) v).1
  simpa [andProb] using h

theorem firstBestWelfare_andTech {n : ℕ} (hn : 1 ≤ n) {γ c : ℝ} (hγ₀ : 0 < γ)
    (hγh : γ < 1 / 2) (hc : 0 < c) (v : ℝ) :
    firstBestWelfare (andTech n γ) (fun _ => c) v =
      max (γ ^ n * v) ((1 - γ) ^ n * v - (n : ℝ) * c) := by
  rw [firstBestWelfare_anon (t := andTech n γ) (f := andProb n γ) (fun _ => rfl)]
  exact and_linear_cost_skips hn hγ₀ hγh hc v

theorem agencyPrincipalUtility_andTech {n : ℕ} (hn : 1 ≤ n) {γ c : ℝ} (hγ₀ : 0 < γ)
    (hγh : γ < 1 / 2) (hc : 0 < c) (v : ℝ) :
    agencyPrincipalUtility (andTech n γ) (fun _ => c) v =
      max (γ ^ n * v) ((1 - γ) ^ n * v - (n : ℝ) * (c * (1 - γ) / (1 - 2 * γ))) := by
  rw [agencyPrincipalUtility_anon (t := andTech n γ) (f := andProb n γ) (fun _ => rfl)]
  have heq : (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => andProb n γ k * v - anonOptPayment (andProb n γ) c k) =
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => andProb n γ k * v - (k : ℝ) * (c * (1 - γ) / (1 - 2 * γ))) := by
    refine Finset.sup'_congr Finset.nonempty_range_add_one rfl fun k hk => ?_
    rw [and_anonOptPayment hγ₀ hγh c (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  rw [heq]
  have ha : 0 < c * (1 - γ) / (1 - 2 * γ) := div_pos (mul_pos hc (by linarith)) (by linarith)
  exact and_linear_cost_skips hn hγ₀ hγh ha v

/-- In the noisy AND technology, optimal team size jumps directly from `0` to `n`, skipping all
intermediate cardinalities `0 < k < n` in both first-best and hidden-action optima
(NRTV Exercise 23.3 / Theorem 23.8). -/
theorem andTech_skips_interior {n : ℕ} (hn : 1 ≤ n) {γ c : ℝ} (hγ₀ : 0 < γ) (hγh : γ < 1 / 2)
    (hc : 0 < c) (v : ℝ) (k : ℕ) (hk0 : 0 < k) (hkn : k < n) :
    andProb n γ k * v - (k : ℝ) * c <
        max (andProb n γ (k - 1) * v - ((k - 1 : ℕ) : ℝ) * c)
          (andProb n γ (k + 1) * v - ((k + 1 : ℕ) : ℝ) * c) ∧
      andProb n γ k * v - anonOptPayment (andProb n γ) c k <
        max (andProb n γ (k - 1) * v - anonOptPayment (andProb n γ) c (k - 1))
          (andProb n γ (k + 1) * v - anonOptPayment (andProb n γ) c (k + 1)) := by
  have ha : 0 < c * (1 - γ) / (1 - 2 * γ) := div_pos (mul_pos hc (by linarith)) (by linarith)
  have hskip : ∀ d : ℝ, 0 < d →
      andProb n γ k * v - (k : ℝ) * d <
        max (andProb n γ (k - 1) * v - ((k - 1 : ℕ) : ℝ) * d)
          (andProb n γ (k + 1) * v - ((k + 1 : ℕ) : ℝ) * d) := fun d hd =>
    (strictly_decreasing_slope_skips hn (andProb n γ) (fun j => (j : ℝ) * d)
      (fun j hj => andProb_strictMono hγ₀ hγh hj)
      (fun j hj0 hjn => by
        have hdf₁ : 0 < andProb n γ j - andProb n γ (j - 1) := by
          have hlt := andProb_strictMono hγ₀ hγh (by omega : j - 1 < n)
          rw [Nat.sub_add_cancel hj0] at hlt
          exact sub_pos.mpr hlt
        have hnum₁ : ((j : ℝ) * d - ((j - 1 : ℕ) : ℝ) * d) = d := by
          rw [Nat.cast_sub hj0]; ring
        have hnum₂ : (((j + 1 : ℕ) : ℝ) * d - (j : ℝ) * d) = d := by push_cast; ring
        rw [hnum₁, hnum₂]
        exact div_lt_div_of_pos_left hd hdf₁ (andProb_diff_strictMono hγ₀ hγh hj0 hjn)) v).2
      k hk0 hkn
  refine ⟨hskip c hc, ?_⟩
  simpa only [and_anonOptPayment hγ₀ hγh c hkn.le,
    and_anonOptPayment hγ₀ hγh c (by omega : k - 1 ≤ n),
    and_anonOptPayment hγ₀ hγh c (by omega : k + 1 ≤ n)] using hskip _ ha

/-- **Price of Unaccountability for the noisy AND technology** (NRTV Theorem 23.8):
`POU(andTech n γ, c) = (1 / γ - 1) ^ (n - 1) + (1 - γ / (1 - γ))`, attained at
`v = andThreshold n γ c`. -/
theorem andTech_pou_eq {n : ℕ} (hn : 1 ≤ n) {γ c : ℝ} (hγ₀ : 0 < γ) (hγh : γ < 1 / 2)
    (hc : 0 < c) :
    priceOfUnaccountability (andTech n γ) (fun _ => c) =
      (1 / γ - 1) ^ (n - 1) + (1 - γ / (1 - γ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  set R : ℝ := (1 / γ - 1) ^ m + (1 - γ / (1 - γ)) with hR
  let vStar : ℝ := andThreshold (m + 1) γ c
  have hvStar_pos : 0 < vStar := andThreshold_pos hn hγ₀ hγh hc
  have h1γ : 0 < 1 - γ := by linarith
  have h12γ : 0 < 1 - 2 * γ := by linarith
  have hpow : 0 < (1 - γ) ^ (m + 1) - γ ^ (m + 1) :=
    sub_pos.mpr (pow_lt_pow_left₀ (by linarith) hγ₀.le (by omega))
  have hden : 0 < γ ^ (m + 1) * vStar := mul_pos (pow_pos hγ₀ _) hvStar_pos
  have hP_ge : ((m + 1 : ℕ) : ℝ) * c ≤ ((m + 1 : ℕ) : ℝ) * (c * (1 - γ) / (1 - 2 * γ)) := by
    gcongr
    rw [le_div_iff₀ h12γ]
    nlinarith
  -- At `vStar`, inducing nobody and inducing everybody give the principal the same utility.
  have hvStar_bal : γ ^ (m + 1) * vStar =
      (1 - γ) ^ (m + 1) * vStar - ((m + 1 : ℕ) : ℝ) * (c * (1 - γ) / (1 - 2 * γ)) := by
    dsimp [vStar, andThreshold]
    field_simp [h12γ.ne', hpow.ne']
    ring
  -- ... and the first-best welfare there is `R` times that utility.
  have hRA : R * (γ ^ (m + 1) * vStar) = (1 - γ) ^ (m + 1) * vStar - ((m + 1 : ℕ) : ℝ) * c := by
    have hv_eq : (1 - 2 * γ) * ((1 - γ) ^ (m + 1) - γ ^ (m + 1)) * vStar =
        ((m + 1 : ℕ) : ℝ) * c * (1 - γ) := by
      dsimp [vStar, andThreshold]
      rw [mul_div_cancel₀ _ (mul_pos h12γ hpow).ne']
    rw [eq_div_of_mul_eq h1γ.ne' hv_eq.symm, hR, show 1 / γ - 1 = (1 - γ) / γ by field_simp,
      div_pow]
    field_simp [h1γ.ne', hγ₀.ne']
    ring
  have hR_ge_one : 1 ≤ R := le_of_mul_le_mul_right (by rw [one_mul, hRA]; linarith) hden
  have htpos : ∀ s, 0 < andTech (m + 1) γ s := fun s => andTech_pos hγ₀ (by linarith) s
  have hc_nn : ∀ _ : Fin (m + 1), 0 ≤ c := fun _ => hc.le
  apply le_antisymm
  · rw [priceOfUnaccountability_le_iff (andTech (m + 1) γ) (fun _ => c) htpos hc_nn]
    intro v hv
    rw [firstBestWelfare_andTech hn hγ₀ hγh hc v, agencyPrincipalUtility_andTech hn hγ₀ hγh hc v]
    rcases le_total v vStar with hvle | hvge
    · have hslope : 0 ≤ (1 - γ) ^ (m + 1) - R * γ ^ (m + 1) :=
        nonneg_of_mul_nonneg_left (by nlinarith [hRA]) hvStar_pos
      have hUA : (1 - γ) ^ (m + 1) * v - ((m + 1 : ℕ) : ℝ) * (c * (1 - γ) / (1 - 2 * γ)) ≤
          γ ^ (m + 1) * v := by
        linarith [mul_le_mul_of_nonneg_left hvle hpow.le]
      rw [max_eq_left hUA]
      exact max_le (le_mul_of_one_le_left (mul_nonneg (pow_nonneg hγ₀.le _) hv.le) hR_ge_one)
        (by linarith [mul_le_mul_of_nonneg_left hvle hslope])
    · have hAU : γ ^ (m + 1) * v ≤
          (1 - γ) ^ (m + 1) * v - ((m + 1 : ℕ) : ℝ) * (c * (1 - γ) / (1 - 2 * γ)) := by
        linarith [mul_le_mul_of_nonneg_left hvge hpow.le]
      rw [max_eq_right hAU]
      refine max_le (hAU.trans (le_mul_of_one_le_left
        ((mul_nonneg (pow_nonneg hγ₀.le _) hv.le).trans hAU) hR_ge_one)) ?_
      rw [hvStar_bal] at hRA
      linarith [mul_le_mul_of_nonneg_left hvge
        (mul_nonneg (sub_nonneg.mpr hR_ge_one) (pow_nonneg h1γ.le (m + 1)))]
  · calc
      R = ((1 - γ) ^ (m + 1) * vStar - ((m + 1 : ℕ) : ℝ) * c) / (γ ^ (m + 1) * vStar) := by
        rw [← hRA, mul_div_cancel_right₀ _ hden.ne']
      _ ≤ firstBestWelfare (andTech (m + 1) γ) (fun _ => c) vStar /
          agencyPrincipalUtility (andTech (m + 1) γ) (fun _ => c) vStar := by
        rw [firstBestWelfare_andTech hn hγ₀ hγh hc, agencyPrincipalUtility_andTech hn hγ₀ hγh hc,
          ← hvStar_bal, max_self]
        exact div_le_div_of_nonneg_right (le_max_right _ _) hden.le
      _ ≤ priceOfUnaccountability (andTech (m + 1) γ) (fun _ => c) :=
        le_priceOfUnaccountability (andTech (m + 1) γ) (fun _ => c) htpos hc_nn hvStar_pos

/-- `POU(andTech n γ, c)` is unbounded in `n` for any fixed `γ ∈ (0, 1 / 2)` and `c > 0`
(NRTV Theorem 23.8). -/
theorem andTech_pou_unbounded_in_n {γ c : ℝ} (hγ₀ : 0 < γ) (hγh : γ < 1 / 2) (hc : 0 < c)
    (B : ℝ) :
    ∃ n ≥ 1, B < priceOfUnaccountability (andTech n γ) (fun _ => c) := by
  have hδ : 0 < 1 / γ - 2 := by
    have : 2 < 1 / γ := by
      rw [lt_div_iff₀ hγ₀]; linarith
    linarith
  have hbern_all : ∀ k : ℕ, 1 + (k : ℝ) * (1 / γ - 2) ≤ (1 / γ - 1) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hk1 : 1 ≤ (1 / γ - 1) ^ k := one_le_pow₀ (by linarith)
      push_cast
      rw [pow_succ']
      nlinarith
  obtain ⟨m, hm⟩ := exists_nat_gt (B / (1 / γ - 2) + 1)
  refine ⟨m + 1, by omega, ?_⟩
  rw [andTech_pou_eq (by omega) hγ₀ hγh hc]
  have hbern := hbern_all m
  have hm_lt : B < 1 + (m : ℝ) * (1 / γ - 2) := by
    have h1 : B < ((m : ℝ) - 1) * (1 / γ - 2) := by
      have : B / (1 / γ - 2) < (m : ℝ) - 1 := by linarith
      exact (div_lt_iff₀ hδ).mp this
    nlinarith
  have htail : 0 < 1 - γ / (1 - γ) := by
    have : γ / (1 - γ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    linarith
  have hsub : (m + 1 - 1 : ℕ) = m := Nat.add_sub_cancel m 1
  rw [hsub]
  linarith

/-- `POU(andTech n γ, c)` is unbounded as `γ → 0⁺` for any fixed `n ≥ 2` and `c > 0`
(NRTV Theorem 23.8). -/
theorem andTech_pou_unbounded_in_gamma {n : ℕ} (hn : 2 ≤ n) {c : ℝ} (hc : 0 < c) (B : ℝ) :
    ∃ γ, 0 < γ ∧ γ < 1 / 2 ∧ B < priceOfUnaccountability (andTech n γ) (fun _ => c) := by
  let M : ℝ := max B 0 + 3
  let γ : ℝ := 1 / M
  have hM : 3 ≤ M := by simp [M]
  have hγ₀ : 0 < γ := by dsimp [γ]; positivity
  have hγh : γ < 1 / 2 := by
    dsimp [γ]
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
    linarith
  refine ⟨γ, hγ₀, hγh, ?_⟩
  rw [andTech_pou_eq (by omega) hγ₀ hγh hc]
  have hbase : 1 < 1 / γ - 1 := by
    have : 2 < 1 / γ := (lt_div_iff₀ hγ₀).mpr (by linarith)
    linarith
  have hpow_ge : 1 / γ - 1 ≤ (1 / γ - 1) ^ (n - 1) :=
    le_self_pow₀ hbase.le (by omega)
  have hgt : B < 1 / γ - 1 := by
    have hinv : 1 / γ = M := by dsimp [γ]; simp
    rw [hinv]
    have : B ≤ max B 0 := le_max_left B 0
    linarith
  have htail : 0 < 1 - γ / (1 - γ) := by
    have : γ / (1 - γ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    linarith
  linarith

/-! ### OR technology (NRTV Theorem 23.9 and Exercise 23.4) -/

/-- Success probability as a function of `k` active agents in the noisy `n`-agent OR
technology: `1 - γ ^ k * (1 - γ) ^ (n - k)`. -/
def orProb (n : ℕ) (γ : ℝ) (k : ℕ) : ℝ :=
  1 - γ ^ k * (1 - γ) ^ (n - k)

theorem orProb_eq (n : ℕ) (γ : ℝ) (k : ℕ) :
    orProb n γ k = 1 - γ ^ k * (1 - γ) ^ (n - k) := by
  rfl

/-- Noisy `n`-agent **OR technology** with parameter `γ`: success occurs unless all `n` signals
fail, yielding probability `1 - γ ^ k * (1 - γ) ^ (n - k)`. -/
def orTech (n : ℕ) (γ : ℝ) (a : Fin n → Bool) : ℝ :=
  orProb n γ (countTrue a)

theorem orTech_eq (n : ℕ) (γ : ℝ) (a : Fin n → Bool) :
    orTech n γ a = orProb n γ (countTrue a) := by
  rfl

theorem orProb_pos {n : ℕ} (hn : 1 ≤ n) {γ : ℝ} (hγ₀ : 0 < γ) (hγh : γ < 1 / 2) {k : ℕ}
    (hk : k ≤ n) : 0 < orProb n γ k := by
  have h1γ : 0 < 1 - γ := by linarith
  have hlt1 : 1 - γ < 1 := by linarith
  have hprod : γ ^ k * (1 - γ) ^ (n - k) < 1 := by
    by_cases hk0 : k = 0
    · subst hk0
      simp only [pow_zero, one_mul, Nat.sub_zero]
      exact pow_lt_one₀ h1γ.le hlt1 (by omega)
    · have hgk : γ ^ k < 1 := pow_lt_one₀ hγ₀.le (by linarith) hk0
      have hqk : (1 - γ) ^ (n - k) ≤ 1 := pow_le_one₀ h1γ.le hlt1.le
      calc
        γ ^ k * (1 - γ) ^ (n - k) ≤ γ ^ k * 1 := mul_le_mul_of_nonneg_left hqk (pow_nonneg hγ₀.le k)
        _ < 1 := by simpa using hgk
  dsimp [orProb]
  linarith

theorem orTech_pos {n : ℕ} (hn : 1 ≤ n) {γ : ℝ} (hγ₀ : 0 < γ) (hγh : γ < 1 / 2)
    (a : Fin n → Bool) : 0 < orTech n γ a :=
  orProb_pos hn hγ₀ hγh (countTrue_le a)

theorem orProb_lt_one {n : ℕ} {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1) (k : ℕ) :
    orProb n γ k < 1 := by
  have : 0 < γ ^ k * (1 - γ) ^ (n - k) := mul_pos (pow_pos hγ₀ k) (pow_pos (sub_pos.mpr hγ₁) _)
  dsimp [orProb]
  linarith

theorem orProb_diff {n : ℕ} (γ : ℝ) {k : ℕ} (hk : k < n) :
    orProb n γ (k + 1) - orProb n γ k =
      (1 - 2 * γ) * γ ^ k * (1 - γ) ^ (n - k - 1) := by
  have hnk1 : n - k = (n - k - 1) + 1 := by omega
  have hnk2 : n - (k + 1) = n - k - 1 := by omega
  dsimp [orProb]
  rw [hnk2]
  nth_rw 2 [hnk1]
  rw [pow_succ γ k, pow_succ (1 - γ) (n - k - 1)]
  ring

theorem orProb_strictMono {n : ℕ} {γ : ℝ} (hγ₀ : 0 < γ) (hγh : γ < 1 / 2) {k : ℕ} (hk : k < n) :
    orProb n γ k < orProb n γ (k + 1) := by
  rw [← sub_pos, orProb_diff γ hk]
  exact mul_pos (mul_pos (by linarith) (pow_pos hγ₀ k)) (pow_pos (by linarith) _)

theorem orProb_mono {n : ℕ} {γ : ℝ} (hγ₀ : 0 < γ) (hγh : γ < 1 / 2) {k₁ k₂ : ℕ}
    (hk₁₂ : k₁ ≤ k₂) (hk₂ : k₂ ≤ n) : orProb n γ k₁ ≤ orProb n γ k₂ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk₁₂
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
    exact (ih (by omega) (by omega)).trans (orProb_strictMono hγ₀ hγh (by omega)).le

theorem isStrictlyMonotone_orTech (n : ℕ) {γ : ℝ} (hγ₀ : 0 < γ) (hγh : γ < 1 / 2) :
    IsStrictlyMonotone (orTech n γ) :=
  isStrictlyMonotone_of_anon (fun _ => rfl) fun _ hk => orProb_strictMono hγ₀ hγh hk

private theorem orProb_diff_strictAnti {n : ℕ} {γ : ℝ} (hγ₀ : 0 < γ) (hγh : γ < 1 / 2)
    {k : ℕ} (hk : k + 1 < n) :
    orProb n γ (k + 2) - orProb n γ (k + 1) < orProb n γ (k + 1) - orProb n γ k := by
  rw [orProb_diff γ (k := k + 1) hk, orProb_diff γ (k := k) (by omega)]
  have hnk : n - k - 1 = (n - (k + 1) - 1) + 1 := by omega
  rw [hnk, pow_succ (1 - γ), pow_succ γ]
  have hbase : 0 < (1 - 2 * γ) * γ ^ k * (1 - γ) ^ (n - (k + 1) - 1) :=
    mul_pos (mul_pos (by linarith) (pow_pos hγ₀ _)) (pow_pos (by linarith) _)
  have hγ_lt : γ < 1 - γ := by linarith
  calc
    (1 - 2 * γ) * (γ ^ k * γ) * (1 - γ) ^ (n - (k + 1) - 1) =
        ((1 - 2 * γ) * γ ^ k * (1 - γ) ^ (n - (k + 1) - 1)) * γ := by ring
    _ < ((1 - 2 * γ) * γ ^ k * (1 - γ) ^ (n - (k + 1) - 1)) * (1 - γ) :=
      mul_lt_mul_of_pos_left hγ_lt hbase
    _ = (1 - 2 * γ) * γ ^ k * ((1 - γ) ^ (n - (k + 1) - 1) * (1 - γ)) := by ring

private theorem orProb_diff_ratio {n : ℕ} {γ : ℝ} (hγ₀ : 0 < γ) (hγh : γ < 1 / 2)
    {k : ℕ} (hk : k + 1 < n) :
    (orProb n γ (k + 1) - orProb n γ k) / (orProb n γ (k + 2) - orProb n γ (k + 1)) =
      (1 - γ) / γ := by
  rw [orProb_diff γ (k := k + 1) hk, orProb_diff γ (k := k) (by omega)]
  have hnk : n - k - 1 = (n - (k + 1) - 1) + 1 := by omega
  rw [hnk, pow_succ (1 - γ), pow_succ γ]
  have h12γ : 1 - 2 * γ ≠ 0 := by linarith
  have hgk : γ ^ k ≠ 0 := (pow_pos hγ₀ _).ne'
  have hq : (1 - γ) ^ (n - (k + 1) - 1) ≠ 0 := (pow_pos (by linarith) _).ne'
  field_simp [h12γ, hgk, hq, hγ₀.ne']

/-- Under the noisy OR technology, optimal hidden-action team size increases strictly through
every cardinality `0, 1, …, n` at `n` strictly increasing value thresholds (NRTV Exercise 23.4). -/
theorem orTech_transitions {n : ℕ} (hn : 1 ≤ n) {γ c : ℝ} (hγ₀ : 0 < γ) (hγh : γ < 1 / 2)
    (hc : 0 < c) :
    ∀ k, k ≤ n → ∃ v : ℝ, 0 < v ∧
      ∀ j, j ≤ n → j ≠ k →
        orProb n γ j * v - anonOptPayment (orProb n γ) c j <
          orProb n γ k * v - anonOptPayment (orProb n γ) c k := by
  let P := anonOptPayment (orProb n γ) c
  let h : ℕ → ℝ := fun m => c * orProb n γ m / (orProb n γ m - orProb n γ (m - 1))
  let r : ℝ := (1 - γ) / γ
  have hr_gt : 1 < r := (one_lt_div hγ₀).mpr (by linarith)
  have hdf : ∀ m, m < n → 0 < orProb n γ (m + 1) - orProb n γ m := fun m hm =>
    sub_pos.mpr (orProb_strictMono hγ₀ hγh hm)
  have hP0 : P 0 = 0 := by simp [P]
  have hP_eq : ∀ m, 1 ≤ m → P m = (m : ℝ) * h m := by
    intro m hm
    simp only [P, anonOptPayment, Nat.one_le_iff_ne_zero.mp hm, ↓reduceIte, h]
    ring
  have hh_pos : ∀ m, 1 ≤ m → m ≤ n → 0 < h m := by
    intro m hm hmn
    have hd := hdf (m - 1) (by omega)
    rw [Nat.sub_add_cancel hm] at hd
    exact div_pos (mul_pos hc (orProb_pos hn hγ₀ hγh hmn)) hd
  -- The per-agent payments satisfy the affine recursion `h (m + 1) = r * h m + c`.
  have hh_rec : ∀ m, 1 ≤ m → m < n → h (m + 1) = r * h m + c := by
    intro m hm hmn
    have hD : orProb n γ m - orProb n γ (m - 1) = r * (orProb n γ (m + 1) - orProb n γ m) := by
      have hratio := orProb_diff_ratio (n := n) hγ₀ hγh (k := m - 1) (by omega)
      rwa [Nat.sub_add_cancel hm, show m - 1 + 2 = m + 1 by omega,
        div_eq_iff (hdf m hmn).ne'] at hratio
    have hd := (hdf m hmn).ne'
    have hr := (zero_lt_one.trans hr_gt).ne'
    simp only [h, hD, Nat.add_sub_cancel]
    field_simp
    ring
  have hP_diff_lt : ∀ k, k + 1 < n → P (k + 1) - P k < P (k + 2) - P (k + 1) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · rw [hP0, hP_eq 1 le_rfl, hP_eq 2 (by omega), hh_rec 1 le_rfl hk]
      push_cast
      linarith [mul_pos (sub_pos.mpr hr_gt) (hh_pos 1 le_rfl hn)]
    · have hA : 0 < ((k : ℝ) + 2) * r - k := by
        nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ k + 2) (sub_pos.mpr hr_gt).le]
      rw [hP_eq (k + 1) (by omega), hP_eq k hk1, hP_eq (k + 2) (by omega),
        hh_rec (k + 1) (by omega) hk, hh_rec k hk1 (by omega)]
      push_cast
      linarith [mul_pos (mul_pos (sub_pos.mpr hr_gt) hA) (hh_pos k hk1 (by omega)),
        mul_pos hA hc]
  have hP_inc : ∀ k, k < n → 0 < P (k + 1) - P k := by
    intro k hk
    induction k with
    | zero => rw [hP0, hP_eq 1 le_rfl]; simpa using hh_pos 1 le_rfl hn
    | succ k ih => exact (ih (by omega)).trans (hP_diff_lt k hk)
  refine strictly_increasing_slope_attains_all hn (orProb n γ) P
    (fun k hk => orProb_strictMono hγ₀ hγh hk) (div_pos (hP_inc 0 (by omega)) (hdf 0 (by omega)))
    fun k hk => ?_
  exact (div_lt_div_of_pos_right (hP_diff_lt k hk) (hdf k (by omega))).trans
    (div_lt_div_of_pos_left (hP_inc (k + 1) hk) (hdf (k + 1) hk)
      (orProb_diff_strictAnti hγ₀ hγh hk))

/-- Under the noisy OR technology, first-best optimal team size also steps strictly through
every cardinality `0, 1, …, n` (NRTV Exercise 23.4). -/
theorem orTech_firstBest_transitions {n : ℕ} (hn : 1 ≤ n) {γ c : ℝ} (hγ₀ : 0 < γ)
    (hγh : γ < 1 / 2) (hc : 0 < c) :
    ∀ k, k ≤ n → ∃ v : ℝ, 0 < v ∧
      ∀ j, j ≤ n → j ≠ k →
        orProb n γ j * v - (j : ℝ) * c < orProb n γ k * v - (k : ℝ) * c := by
  refine strictly_increasing_slope_attains_all hn (orProb n γ) (fun k => (k : ℝ) * c)
    (fun k hk => orProb_strictMono hγ₀ hγh hk) ?_ ?_
  · simp only [Nat.cast_zero, zero_mul, sub_zero, Nat.cast_one, one_mul]
    exact div_pos hc (sub_pos.mpr (orProb_strictMono hγ₀ hγh hn))
  · intro k hk
    have hdf₂ : 0 < orProb n γ (k + 2) - orProb n γ (k + 1) :=
      sub_pos.mpr (orProb_strictMono hγ₀ hγh hk)
    have hnum₁ : ((k + 1 : ℕ) : ℝ) * c - (k : ℝ) * c = c := by push_cast; ring
    have hnum₂ : ((k + 2 : ℕ) : ℝ) * c - ((k + 1 : ℕ) : ℝ) * c = c := by push_cast; ring
    rw [hnum₁, hnum₂]
    exact div_lt_div_of_pos_left hc hdf₂ (orProb_diff_strictAnti hγ₀ hγh hk)

private theorem orTech_pou_n_two_ineq (q : ℝ) :
    2 * q ^ 2 - 1 ≤ 2 * (2 * q - 1) ^ 2 * q ^ 2 := by
  have hpol : 2 * (2 * q - 1) ^ 2 * q ^ 2 - (2 * q ^ 2 - 1) =
      (q - 3 / 4) ^ 2 * (8 * (q + 1 / 4) ^ 2 + 1) + 5 / 32 := by ring
  have hsq : 0 ≤ (q - 3 / 4) ^ 2 * (8 * (q + 1 / 4) ^ 2 + 1) + 5 / 32 := by positivity
  linarith

private theorem orTech_pou_large_n_ineq {q : ℝ} {n : ℕ} (hn : 3 ≤ n) (hq₀ : 0 ≤ q)
    (hqn : 1 / 2 < q ^ n) (hq₁ : q ≤ 1) :
    2 * q ^ n - 1 ≤ 2 * (2 * q - 1) ^ 2 * q ^ (2 * n - 2) := by
  have hq79 : 7 / 9 < q := by
    by_contra hle
    have hqle : q ≤ 7 / 9 := not_lt.mp hle
    have h3 : q ^ 3 ≤ (7 / 9 : ℝ) ^ 3 := pow_le_pow_left₀ hq₀ hqle 3
    have hn3 : q ^ n ≤ q ^ 3 := pow_le_pow_of_le_one hq₀ hq₁ hn
    have hnum : (7 / 9 : ℝ) ^ 3 < 1 / 2 := by norm_num
    linarith
  have hquad : q ^ 2 ≤ 2 * (2 * q - 1) ^ 2 := by
    have hid : 2 * (2 * q - 1) ^ 2 - q ^ 2 =
        7 * (q - 7 / 9) ^ 2 + (26 / 9) * (q - 7 / 9) + 1 / 81 := by ring
    have hpos : 0 ≤ 7 * (q - 7 / 9) ^ 2 + (26 / 9) * (q - 7 / 9) + 1 / 81 := by
      have hsub : 0 ≤ q - 7 / 9 := sub_nonneg.mpr hq79.le
      positivity
    linarith
  have hpow2 : q ^ (2 * n) = q ^ 2 * q ^ (2 * n - 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hsq : 2 * q ^ n - 1 ≤ q ^ (2 * n) := by
    have h2n : q ^ (2 * n) = (q ^ n) ^ 2 := by rw [← pow_mul]; congr 1; omega
    have hnonneg : 0 ≤ (q ^ n - 1) ^ 2 := sq_nonneg _
    nlinarith
  calc
    2 * q ^ n - 1 ≤ q ^ (2 * n) := hsq
    _ = q ^ 2 * q ^ (2 * n - 2) := hpow2
    _ ≤ (2 * (2 * q - 1) ^ 2) * q ^ (2 * n - 2) :=
      mul_le_mul_of_nonneg_right hquad (pow_nonneg hq₀ _)

/-- **Price of Unaccountability bound for the noisy OR technology** (NRTV Theorem 23.9):
`POU(orTech n γ, c) ≤ 2` uniformly across all `n ≥ 1`, `γ ∈ (0, 1 / 2)`, and `c > 0`
(sharpening `[BabaioffChuangFeldman2007]` Theorem 23.9's `≤ 5 / 2` bound), using only the
`0`-agent and `1`-agent contracts. -/
theorem orTech_pou_le_two {n : ℕ} (hn : 1 ≤ n) {γ c : ℝ} (hγ₀ : 0 < γ) (hγh : γ < 1 / 2)
    (hc : 0 < c) :
    priceOfUnaccountability (orTech n γ) (fun _ => c) ≤ 2 := by
  have htpos : ∀ s, 0 < orTech n γ s := fun s => orTech_pos hn hγ₀ hγh s
  have hc_nn : ∀ _ : Fin n, 0 ≤ c := fun _ => hc.le
  rw [priceOfUnaccountability_le_iff (orTech n γ) (fun _ => c) htpos hc_nn]
  intro v hv
  rw [firstBestWelfare_anon (t := orTech n γ) (f := orProb n γ) (fun _ => rfl),
    agencyPrincipalUtility_anon (t := orTech n γ) (f := orProb n γ) (fun _ => rfl)]
  refine Finset.sup'_le Finset.nonempty_range_add_one _ fun k hk => ?_
  change orProb n γ k * v - (k : ℝ) * c ≤ _
  have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  -- The hidden-action optimum is at least the utility of inducing `0` or `1` agents.
  have hU : ∀ j ≤ n, orProb n γ j * v - anonOptPayment (orProb n γ) c j ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun j => orProb n γ j * v - anonOptPayment (orProb n γ) c j) := fun j hj =>
    Finset.le_sup' (fun j => orProb n γ j * v - anonOptPayment (orProb n γ) c j)
      (Finset.mem_range.mpr (by omega))
  have hU0 := hU 0 (Nat.zero_le n)
  have hU1 := hU 1 hn
  rw [anonOptPayment_zero, sub_zero] at hU0
  have h1γ : 0 < 1 - γ := by linarith
  have hp0 : 0 < orProb n γ 0 := orProb_pos hn hγ₀ hγh (Nat.zero_le n)
  have hp1 : 1 / 2 < orProb n γ 1 := by
    have := mul_le_of_le_one_right hγ₀.le (pow_le_one₀ (n := n - 1) h1γ.le (by linarith))
    simp only [orProb, pow_one]
    linarith
  have hpk : orProb n γ k < 1 := orProb_lt_one hγ₀ (by linarith) k
  -- At `v01`, inducing `0` or `1` agents gives the principal the same utility.
  obtain ⟨Δ₁, hΔ₁⟩ : ∃ d, orProb n γ 1 - orProb n γ 0 = d := ⟨_, rfl⟩
  have hΔ₁_pos : 0 < Δ₁ := hΔ₁ ▸ sub_pos.mpr (orProb_strictMono hγ₀ hγh hn)
  have hP₁ : anonOptPayment (orProb n γ) c 1 = c * orProb n γ 1 / Δ₁ := by
    simp [anonOptPayment, hΔ₁]
  obtain ⟨v01, hv01⟩ : ∃ w, c * orProb n γ 1 / Δ₁ ^ 2 = w := ⟨_, rfl⟩
  have hv01_pos : 0 < v01 := hv01 ▸ div_pos (mul_pos hc (by linarith)) (pow_pos hΔ₁_pos 2)
  have hbal : orProb n γ 1 * v01 - anonOptPayment (orProb n γ) c 1 = orProb n γ 0 * v01 := by
    rw [hP₁, ← hv01]
    field_simp
    rw [← hΔ₁]
    ring
  -- The claimed bound holds at `v01`.
  have hat : orProb n γ k * v01 - k * c ≤ 2 * (orProb n γ 0 * v01) := by
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · rcases k with _ | _ | k
      · push_cast
        linarith [mul_pos hp0 hv01_pos]
      · have : (orProb n γ 1 - 2 * orProb n γ 0) * v01 ≤ c := by
          rw [← hv01, mul_div_assoc', div_le_iff₀ (pow_pos hΔ₁_pos 2), ← hΔ₁]
          linarith [mul_nonneg hc.le (sq_nonneg (orProb n γ 0))]
        push_cast
        linarith
      · omega
    have hn2 : 2 ≤ n := by omega
    have hkc : 2 * c ≤ k * c := mul_le_mul_of_nonneg_right (by exact_mod_cast hk2) hc.le
    have hp0_eq : orProb n γ 0 = 1 - (1 - γ) ^ n := by simp [orProb]
    suffices (orProb n γ k - 2 * orProb n γ 0) * v01 ≤ 2 * c by linarith
    rcases le_or_gt ((1 - γ) ^ n) (1 / 2) with hqn | hqn
    · linarith [mul_nonpos_of_nonpos_of_nonneg
        (by linarith : orProb n γ k - 2 * orProb n γ 0 ≤ 0) hv01_pos.le]
    have hΔ₁_sq : Δ₁ ^ 2 = (2 * (1 - γ) - 1) ^ 2 * (1 - γ) ^ (2 * n - 2) := by
      rw [← hΔ₁, orProb_diff γ hn, show 2 * n - 2 = (n - 0 - 1) * 2 by omega, pow_mul]
      ring
    have hineq : 2 * (1 - γ) ^ n - 1 ≤ 2 * (2 * (1 - γ) - 1) ^ 2 * (1 - γ) ^ (2 * n - 2) := by
      rcases hn2.eq_or_lt with rfl | hn3
      · exact orTech_pou_n_two_ineq (1 - γ)
      · exact orTech_pou_large_n_ineq hn3 h1γ.le hqn (by linarith)
    have hv01_ub : v01 ≤ c / Δ₁ ^ 2 := hv01 ▸ div_le_div_of_nonneg_right
      (mul_le_of_le_one_right hc.le (orProb_lt_one hγ₀ (by linarith) 1).le) (sq_nonneg Δ₁)
    calc
      (orProb n γ k - 2 * orProb n γ 0) * v01 ≤ (2 * (1 - γ) ^ n - 1) * v01 :=
        mul_le_mul_of_nonneg_right (by linarith) hv01_pos.le
      _ ≤ (2 * (1 - γ) ^ n - 1) * (c / Δ₁ ^ 2) := mul_le_mul_of_nonneg_left hv01_ub (by linarith)
      _ ≤ 2 * c := by
        rw [hΔ₁_sq, mul_div_assoc',
          div_le_iff₀ (mul_pos (pow_pos (by linarith) 2) (pow_pos h1γ _))]
        linarith [mul_le_mul_of_nonneg_right hineq hc.le]
  -- Below `v01` compare with inducing nobody; above it, with inducing one agent.
  rcases le_total v v01 with hv_le | hv_ge
  · refine le_trans ?_ (mul_le_mul_of_nonneg_left hU0 zero_le_two)
    rcases le_total (orProb n γ k - 2 * orProb n γ 0) 0 with hneg | hpos
    · linarith [mul_nonpos_of_nonpos_of_nonneg hneg hv.le, mul_nonneg (Nat.cast_nonneg k) hc.le]
    · linarith [mul_le_mul_of_nonneg_left hv_le hpos]
  · refine le_trans ?_ (mul_le_mul_of_nonneg_left hU1 zero_le_two)
    linarith [mul_nonneg (by linarith : 0 ≤ 2 * orProb n γ 1 - orProb n γ k)
      (sub_nonneg.mpr hv_ge)]

end AnonymousAndExamples

end Cslib.GameTheory.Contract
