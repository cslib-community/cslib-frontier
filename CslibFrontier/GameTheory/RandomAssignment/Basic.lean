/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Convex.DoublyStochasticMatrix
public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Relation

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Random assignment: stochastic dominance, efficiency, fairness and incentives

Foundations for the house allocation / random assignment problem with `n` agents and `n`
indivisible objects (`Fin n`), without monetary transfers and without initial endowments,
following the framework of Bogomolnaia and Moulin ([BogomolnaiaMoulin2001]; note: the primary
article PDF has not been consulted locally, so theorem/lemma/page numbers are not cited).

A **strict preference profile** `p : Profile n` assigns to each agent `i : Fin n` a bijection
`p i : Equiv.Perm (Fin n)` listing agent `i`'s strict ranking from best (`k = 0`) to worst
(`k = n - 1`). Thus `p i k` is agent `i`'s `k`-th preferred object, and `(p i).symm o` is the
rank of object `o` in agent `i`'s preference order (smaller rank means strictly preferred).

A **random assignment** (probabilistic assignment / bistochastic matrix) is a matrix
`P : Matrix (Fin n) (Fin n) ℝ` lying in `doublyStochastic ℝ (Fin n)`. Entry `P i o` is the
probability that agent `i` receives object `o`. By Birkhoff's theorem (already formalized in
Mathlib as `exists_eq_sum_perm_of_mem_doublyStochastic`), every doubly stochastic matrix can be
realized as a probability distribution over deterministic assignments `Equiv.Perm (Fin n)`.

## Main definitions

* `Cslib.GameTheory.RandomAssignment.Profile`: strict preference profiles `Fin n → Equiv.Perm`.
* `Cslib.GameTheory.RandomAssignment.AssignmentRule`: maps profiles to `Matrix (Fin n) (Fin n) ℝ`.
* `Cslib.GameTheory.RandomAssignment.upperContourSum`: prefix probability mass `∑ r ≤ k, x (π r)`.
* `Cslib.GameTheory.RandomAssignment.SDDominates` / `SDDominatesStrict`: first-order stochastic
  dominance relative to a strict ranking `π`.
* `Cslib.GameTheory.RandomAssignment.IsEqualTreatmentOfEquals`: equal agents get equal lotteries.
* `Cslib.GameTheory.RandomAssignment.IsSDEnvyFree`: `sd`-envy-freeness.
* `Cslib.GameTheory.RandomAssignment.IsSDEfficient`: ordinal (`sd`-) efficiency.
* `Cslib.GameTheory.RandomAssignment.IsExPostEfficient`: convex combination of Pareto-efficient
  deterministic matchings.
* `Cslib.GameTheory.RandomAssignment.IsSDStrategyProof` / `IsWeaklySDStrategyProof`: strong and
  weak `sd`-strategy-proofness.
* `Cslib.GameTheory.RandomAssignment.tradeRel` / `IsAcyclicTrade`: the pairwise trade graph
  `a ≻_P b` and its acyclicity predicate.

## Main results

* `Cslib.GameTheory.RandomAssignment.sdDominates_iff_forall_antitone`: first-order stochastic
  dominance is equivalent to weakly higher expected utility under every rank-consistent utility.
* `Cslib.GameTheory.RandomAssignment.isSDEfficient_iff_isAcyclicTrade`: a doubly stochastic matrix
  is `sd`-efficient if and only if its trade relation `tradeRel p P` is acyclic.
* `Cslib.GameTheory.RandomAssignment.IsSDEfficient.isExPostEfficient`: `sd`-efficiency implies
  ex-post efficiency (via Mathlib's Birkhoff–von Neumann theorem).
* `Cslib.GameTheory.RandomAssignment.IsSDStrategyProof.upperContour_eq`: upper-contour-set
  invariance under `sd`-strategy-proof rules (and adjacent-swap specialization `adjSwap_eq`).

## References

* [BogomolnaiaMoulin2001] (primary article PDF not consulted; section/theorem locators
  unverified).
-/

public section

namespace Cslib.GameTheory.RandomAssignment

open Finset Matrix

/-- A strict preference profile for `n` agents over `n` objects. Agent `i`'s `k`-th preferred
object is `p i k`, with `0` most preferred and `n - 1` least preferred. Thus `(p i).symm o` is the
rank of object `o` for agent `i`. -/
abbrev Profile (n : ℕ) : Type := Fin n → Equiv.Perm (Fin n)

/-- A random assignment rule maps a preference profile to an `n × n` real matrix whose `(i, o)`
entry represents the probability that agent `i` receives object `o`. -/
abbrev AssignmentRule (n : ℕ) : Type := Profile n → Matrix (Fin n) (Fin n) ℝ

/-- An assignment rule is *feasible* if it always returns a doubly stochastic matrix. -/
@[expose] def IsFeasible {n : ℕ} (φ : AssignmentRule n) : Prop :=
  ∀ p : Profile n, φ p ∈ doublyStochastic ℝ (Fin n)

/-- Cumulative probability mass assigned to the `k + 1` best objects `{π r | r ≤ k}` under strict
ranking `π` and lottery vector `x : Fin n → ℝ`. -/
@[expose] def upperContourSum {n : ℕ} (π : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (k : Fin n) : ℝ :=
  ∑ r ∈ Finset.Iic k, x (π r)

lemma upperContourSum_add {n : ℕ} (π : Equiv.Perm (Fin n)) (x y : Fin n → ℝ) (k : Fin n) :
    upperContourSum π (x + y) k = upperContourSum π x k + upperContourSum π y k := by
  simp [upperContourSum, Finset.sum_add_distrib]

lemma upperContourSum_smul {n : ℕ} (π : Equiv.Perm (Fin n)) (c : ℝ) (x : Fin n → ℝ) (k : Fin n) :
    upperContourSum π (c • x) k = c * upperContourSum π x k := by
  simp [upperContourSum, Finset.mul_sum]

lemma upperContourSum_eq_sum_filter {n : ℕ} (π : Equiv.Perm (Fin n)) (x : Fin n → ℝ)
    (k : Fin n) :
    upperContourSum π x k = ∑ o : Fin n with π.symm o ≤ k, x o := by
  unfold upperContourSum
  refine Finset.sum_nbij π ?_ ?_ ?_ (fun _ _ => rfl)
  · intro r hr
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa using Finset.mem_Iic.mp hr⟩
  · intro a _ b _ hab
    exact π.injective hab
  · intro o ho
    rw [Finset.mem_coe, Finset.mem_filter] at ho
    exact ⟨π.symm o, Finset.mem_Iic.mpr ho.2, π.apply_symm_apply o⟩

lemma upperContourSum_last {n : ℕ} [NeZero n] (π : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    upperContourSum π x (Fin.last (n - 1) |>.cast (by
      have := NeZero.pos n; omega)) = ∑ o : Fin n, x o := by
  unfold upperContourSum
  have htop : Finset.Iic ((Fin.last (n - 1)).cast (by have := NeZero.pos n; omega)) =
      (Finset.univ : Finset (Fin n)) := by
    ext r
    simp only [Finset.mem_Iic, Finset.mem_univ, iff_true, Fin.le_def, Fin.val_cast, Fin.val_last]
    omega
  rw [htop]
  exact Equiv.sum_comp π x

lemma upperContourSum_succ {n : ℕ} (π : Equiv.Perm (Fin n)) (x : Fin n → ℝ)
    {k : Fin n} (hk : 0 < k.val) :
    upperContourSum π x k =
      upperContourSum π x ⟨k.val - 1, by omega⟩ + x (π k) := by
  unfold upperContourSum
  have hsub : Finset.Iic k =
      insert k (Finset.Iic (⟨k.val - 1, by omega⟩ : Fin n)) := by
    ext r
    simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_def, Fin.ext_iff]
    omega
  rw [hsub, Finset.sum_insert, add_comm]
  simp only [Finset.mem_Iic, Fin.le_def]
  omega

lemma upperContourSum_zero {n : ℕ} (π : Equiv.Perm (Fin n)) (x : Fin n → ℝ)
    {k : Fin n} (hk : k.val = 0) :
    upperContourSum π x k = x (π k) := by
  unfold upperContourSum
  have hsub : Finset.Iic k = {k} := by
    ext r
    simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_def, Fin.ext_iff]
    omega
  rw [hsub, Finset.sum_singleton]

lemma eq_of_upperContourSum_eq {n : ℕ} (π : Equiv.Perm (Fin n)) {x y : Fin n → ℝ}
    (h : ∀ k : Fin n, upperContourSum π x k = upperContourSum π y k) : x = y := by
  funext o
  have hko : x (π (π.symm o)) = y (π (π.symm o)) := by
    set k := π.symm o
    by_cases hk : k.val = 0
    · simpa [upperContourSum_zero π x hk, upperContourSum_zero π y hk] using h k
    · have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk
      have h1 := h k
      have h0 := h ⟨k.val - 1, by omega⟩
      rw [upperContourSum_succ π x hkpos, upperContourSum_succ π y hkpos] at h1
      linarith
  simpa using hko

/-- First-order stochastic dominance: lottery `x` weakly `sd`-dominates lottery `y` with respect to
the strict ranking `π` when every upper contour set `{π r | r ≤ k}` receives at least as much
probability mass under `x` as under `y`. -/
@[expose] def SDDominates {n : ℕ} (π : Equiv.Perm (Fin n)) (x y : Fin n → ℝ) : Prop :=
  ∀ k : Fin n, upperContourSum π y k ≤ upperContourSum π x k

/-- Strict first-order stochastic dominance: `x` weakly `sd`-dominates `y` and strictly dominates it
at some rank `k`. -/
@[expose] def SDDominatesStrict {n : ℕ} (π : Equiv.Perm (Fin n)) (x y : Fin n → ℝ) : Prop :=
  SDDominates π x y ∧ ∃ k : Fin n, upperContourSum π y k < upperContourSum π x k

lemma SDDominates.refl {n : ℕ} (π : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    SDDominates π x x :=
  fun _ => le_rfl

lemma SDDominates.trans {n : ℕ} {π : Equiv.Perm (Fin n)} {x y z : Fin n → ℝ}
    (hxy : SDDominates π x y) (hyz : SDDominates π y z) :
    SDDominates π x z :=
  fun k => (hyz k).trans (hxy k)

lemma SDDominates.antisymm {n : ℕ} {π : Equiv.Perm (Fin n)} {x y : Fin n → ℝ}
    (hxy : SDDominates π x y) (hyx : SDDominates π y x) : x = y :=
  eq_of_upperContourSum_eq π fun k => le_antisymm (hyx k) (hxy k)

lemma SDDominates.add {n : ℕ} {π : Equiv.Perm (Fin n)} {x₁ y₁ x₂ y₂ : Fin n → ℝ}
    (h₁ : SDDominates π x₁ y₁) (h₂ : SDDominates π x₂ y₂) :
    SDDominates π (x₁ + x₂) (y₁ + y₂) := by
  intro k
  rw [upperContourSum_add, upperContourSum_add]
  exact add_le_add (h₁ k) (h₂ k)

lemma SDDominates.smul {n : ℕ} {π : Equiv.Perm (Fin n)} {c : ℝ} (hc : 0 ≤ c)
    {x y : Fin n → ℝ} (h : SDDominates π x y) :
    SDDominates π (c • x) (c • y) := by
  intro k
  rw [upperContourSum_smul, upperContourSum_smul]
  exact mul_le_mul_of_nonneg_left (h k) hc

lemma sdDominatesStrict_iff_ne {n : ℕ} (π : Equiv.Perm (Fin n)) (x y : Fin n → ℝ) :
    SDDominatesStrict π x y ↔ SDDominates π x y ∧ x ≠ y := by
  constructor
  · rintro ⟨hdom, k, hk⟩
    refine ⟨hdom, fun h => ?_⟩
    subst h
    exact lt_irrefl _ hk
  · rintro ⟨hdom, hne⟩
    refine ⟨hdom, ?_⟩
    by_contra! hle
    exact hne (eq_of_upperContourSum_eq π fun k => le_antisymm (hle k) (hdom k))

lemma SDDominatesStrict.not_reverse {n : ℕ} {π : Equiv.Perm (Fin n)} {x y : Fin n → ℝ}
    (h : SDDominatesStrict π x y) : ¬ SDDominates π y x := by
  intro hrev
  obtain ⟨_, k, hk⟩ := h
  exact hk.not_ge (hrev k)

lemma sdDominates_single_iff {n : ℕ} (π : Equiv.Perm (Fin n)) (a b : Fin n)
    {c : ℝ} (hc : 0 < c) :
    SDDominates π (fun o => if o = a then c else 0) (fun o => if o = b then c else 0) ↔
      π.symm a ≤ π.symm b := by
  have heval : ∀ (z k : Fin n),
      upperContourSum π (fun o => if o = z then c else 0) k =
        if π.symm z ≤ k then c else 0 := by
    intro z k
    rw [upperContourSum_eq_sum_filter]
    by_cases h : π.symm z ≤ k
    · rw [Finset.sum_eq_single z]
      · simp [h]
      · intro o _ ho; simp [ho]
      · intro hz
        exfalso
        exact hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    · rw [ite_eq_right_iff.mpr fun hc' => absurd hc' h]
      refine Finset.sum_eq_zero fun o ho => ?_
      have ho' := (Finset.mem_filter.mp ho).2
      have hne : o ≠ z := fun heq => h (heq ▸ ho')
      simp [hne]
  constructor
  · intro h
    have hk := h (π.symm b)
    rw [heval a (π.symm b), heval b (π.symm b)] at hk
    simp only [le_refl, ↓reduceIte] at hk
    by_contra hlt
    simp only [hlt, ↓reduceIte] at hk
    linarith
  · intro hab k
    rw [heval a k, heval b k]
    by_cases hb : π.symm b ≤ k
    · simp [hb, hab.trans hb]
    · simp only [hb, ↓reduceIte]
      split_ifs <;> linarith

/-- Expected-utility formula by discrete Abel summation (summation by parts) along ranking `π`. -/
private lemma sum_mul_eq_abel {n : ℕ} [NeZero n] (π : Equiv.Perm (Fin n)) (d u : Fin n → ℝ) :
    ∑ o : Fin n, d o * u o =
      (∑ k : Fin (n - 1),
        upperContourSum π d ⟨k.val, by have := NeZero.pos n; omega⟩ *
          (u (π ⟨k.val, by have := NeZero.pos n; omega⟩) -
           u (π ⟨k.val + 1, by have := NeZero.pos n; omega⟩))) +
      (∑ o : Fin n, d o) * u (π ⟨n - 1, by have := NeZero.pos n; omega⟩) := by
  have hn : 0 < n := NeZero.pos n
  have hcomp : ∑ o : Fin n, d o * u o = ∑ r : Fin n, d (π r) * u (π r) :=
    (Equiv.sum_comp π (fun o => d o * u o)).symm
  rw [hcomp]
  have htot : ∑ o : Fin n, d o = ∑ r : Fin n, d (π r) :=
    (Equiv.sum_comp π d).symm
  rw [htot]
  have hgen : ∀ m : ℕ, (hm : m < n) →
      ∑ r : Fin n with r.val ≤ m, d (π r) * u (π r) =
        (∑ k : Fin m,
          upperContourSum π d ⟨k.val, by omega⟩ *
            (u (π ⟨k.val, by omega⟩) - u (π ⟨k.val + 1, by omega⟩))) +
        upperContourSum π d ⟨m, hm⟩ * u (π ⟨m, hm⟩) := by
    intro m
    induction m with
    | zero =>
      intro hm
      have hf : (Finset.univ.filter fun r : Fin n => r.val ≤ 0) = {⟨0, hm⟩} := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          Fin.ext_iff]
        omega
      rw [hf, Finset.sum_singleton, upperContourSum_zero π d (k := ⟨0, hm⟩) rfl]
      simp
    | succ m ih =>
      intro hm
      have hm' : m < n := by omega
      have hsplit : (Finset.univ.filter fun r : Fin n => r.val ≤ m + 1) =
          insert ⟨m + 1, hm⟩ (Finset.univ.filter fun r : Fin n => r.val ≤ m) := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.ext_iff]
        omega
      have hnotin : (⟨m + 1, hm⟩ : Fin n) ∉
          (Finset.univ.filter fun r : Fin n => r.val ≤ m) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      rw [hsplit, Finset.sum_insert hnotin, ih hm', Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [upperContourSum_succ π d (k := ⟨m + 1, hm⟩) (Nat.succ_pos m)]
      simp only [Nat.add_sub_cancel]
      ring
  have hlast := hgen (n - 1) (by omega)
  have hfilt : (Finset.univ.filter fun r : Fin n => r.val ≤ n - 1) = Finset.univ := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    omega
  rw [hfilt] at hlast
  rw [hlast]
  congr 1
  congr 1
  unfold upperContourSum
  have hiic : Finset.Iic (⟨n - 1, by omega⟩ : Fin n) = Finset.univ := by
    ext r
    simp only [Finset.mem_Iic, Finset.mem_univ, iff_true, Fin.le_def]
    omega
  rw [hiic]

/-- First-order stochastic dominance characterizes weakly higher expected utility across all
von Neumann–Morgenstern utility vectors consistent with the strict preference ranking `π`. -/
theorem sdDominates_iff_forall_antitone {n : ℕ} (π : Equiv.Perm (Fin n)) {x y : Fin n → ℝ}
    (hsum : ∑ o : Fin n, x o = ∑ o : Fin n, y o) :
    SDDominates π x y ↔
      ∀ u : Fin n → ℝ, Antitone (fun k : Fin n => u (π k)) →
        ∑ o : Fin n, y o * u o ≤ ∑ o : Fin n, x o * u o := by
  constructor
  · intro hdom u hu
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have : NeZero n := ⟨hn.ne'⟩
    have hdiff : ∑ o : Fin n, (x - y) o * u o =
        ∑ o : Fin n, x o * u o - ∑ o : Fin n, y o * u o := by
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    suffices h : 0 ≤ ∑ o : Fin n, (x - y) o * u o by linarith
    rw [sum_mul_eq_abel π (x - y) u]
    have hzero : ∑ o : Fin n, (x - y) o = 0 := by
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, hsum, sub_self]
    rw [hzero, zero_mul, add_zero]
    refine Finset.sum_nonneg fun k _ => mul_nonneg ?_ ?_
    · have hk : upperContourSum π (x - y) ⟨k.val, by omega⟩ =
          upperContourSum π x ⟨k.val, by omega⟩ -
            upperContourSum π y ⟨k.val, by omega⟩ := by
        simp [upperContourSum, Finset.sum_sub_distrib]
      rw [hk]
      exact sub_nonneg.mpr (hdom ⟨k.val, by omega⟩)
    · refine sub_nonneg.mpr (hu ?_)
      simp [Fin.le_def]
  · intro hexp k
    let u : Fin n → ℝ := fun o => if π.symm o ≤ k then 1 else 0
    have hu : Antitone (fun r : Fin n => u (π r)) := by
      intro r₁ r₂ hr
      simp only [u, Equiv.symm_apply_apply]
      by_cases h₂ : r₂ ≤ k
      · simp [h₂, hr.trans h₂]
      · simp only [h₂, ↓reduceIte]; split_ifs <;> norm_num
    have hspec := hexp u hu
    have heq : ∀ z : Fin n → ℝ, ∑ o : Fin n, z o * u o = upperContourSum π z k := by
      intro z
      rw [upperContourSum_eq_sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun o _ => ?_
      simp [u, mul_ite]
    simpa only [heq] using hspec

/-- Equal treatment of equals (ETE): agents with identical strict preferences receive the exact
same lottery row. -/
@[expose] def IsEqualTreatmentOfEquals {n : ℕ} (p : Profile n)
    (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, p i = p j → P i = P j

/-- Stochastic-dominance (`sd`-) envy-freeness: every agent's own lottery weakly `sd`-dominates
every other agent's lottery under that agent's strict preference order. -/
@[expose] def IsSDEnvyFree {n : ℕ} (p : Profile n) (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, SDDominates (p i) (P i) (P j)

lemma IsSDEnvyFree.equalTreatmentOfEquals {n : ℕ} {p : Profile n} {P : Matrix (Fin n) (Fin n) ℝ}
    (hef : IsSDEnvyFree p P) : IsEqualTreatmentOfEquals p P := by
  intro i j hij
  refine SDDominates.antisymm (hef i j) ?_
  have h := hef j i
  rwa [← hij] at h

/-- Ordinal (`sd`-) efficiency of a random assignment `P`: `P` is doubly stochastic and no other
doubly stochastic matrix `Q` weakly `sd`-dominates `P` for every agent and strictly for at least
one agent. -/
@[expose] def IsSDEfficient {n : ℕ} (p : Profile n) (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  P ∈ doublyStochastic ℝ (Fin n) ∧
    ¬ ∃ Q ∈ doublyStochastic ℝ (Fin n),
      (∀ i : Fin n, SDDominates (p i) (Q i) (P i)) ∧
      ∃ i : Fin n, SDDominatesStrict (p i) (Q i) (P i)

/-- Deterministic Pareto efficiency of a bijection `μ : Equiv.Perm (Fin n)`: no bijection `ν` gives
every agent a weakly better rank and at least one agent a strictly better rank. -/
@[expose] def IsParetoEfficientPerm {n : ℕ} (p : Profile n) (μ : Equiv.Perm (Fin n)) : Prop :=
  ¬ ∃ ν : Equiv.Perm (Fin n),
    (∀ i : Fin n, (p i).symm (ν i) ≤ (p i).symm (μ i)) ∧
    ∃ i : Fin n, (p i).symm (ν i) < (p i).symm (μ i)

/-- Ex-post efficiency: `P` is a convex combination of deterministic Pareto-efficient matchings. -/
@[expose] def IsExPostEfficient {n : ℕ} (p : Profile n) (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ w : Equiv.Perm (Fin n) → ℝ,
    (∀ μ, 0 ≤ w μ) ∧
    ∑ μ : Equiv.Perm (Fin n), w μ = 1 ∧
    (∀ μ, 0 < w μ → IsParetoEfficientPerm p μ) ∧
    ∑ μ : Equiv.Perm (Fin n), w μ • μ.permMatrix ℝ = P

/-- Strong `sd`-strategy-proofness: for every profile `p`, agent `i`, and alternative report `π'`,
truth-telling weakly `sd`-dominates misreporting `π'` under `i`'s true preference `p i`. -/
@[expose] def IsSDStrategyProof {n : ℕ} (φ : AssignmentRule n) : Prop :=
  ∀ (p : Profile n) (i : Fin n) (π' : Equiv.Perm (Fin n)),
    SDDominates (p i) (φ p i) (φ (Function.update p i π') i)

/-- Weak `sd`-strategy-proofness: no unilateral misreport strictly `sd`-dominates truth-telling
under the agent's true preference. -/
@[expose] def IsWeaklySDStrategyProof {n : ℕ} (φ : AssignmentRule n) : Prop :=
  ∀ (p : Profile n) (i : Fin n) (π' : Equiv.Perm (Fin n)),
    ¬ SDDominatesStrict (p i) (φ (Function.update p i π') i) (φ p i)

lemma IsSDStrategyProof.weaklySDStrategyProof {n : ℕ} {φ : AssignmentRule n}
    (hsp : IsSDStrategyProof φ) : IsWeaklySDStrategyProof φ :=
  fun p i π' hstrict => hstrict.not_reverse (hsp p i π')

/-- Upper-contour invariance: under a strong `sd`-strategy-proof rule, if two reports `p i` and `π'`
share the same `k`-th upper contour set, the total probability mass assigned to that set is equal
under both reports. -/
theorem IsSDStrategyProof.upperContour_eq {n : ℕ} {φ : AssignmentRule n}
    (hsp : IsSDStrategyProof φ) (p : Profile n) (i : Fin n) (π' : Equiv.Perm (Fin n))
    (k : Fin n) (hset : ∀ o : Fin n, (p i).symm o ≤ k ↔ π'.symm o ≤ k) :
    upperContourSum (p i) (φ p i) k =
      upperContourSum (p i) (φ (Function.update p i π') i) k := by
  have h1 : upperContourSum (p i) (φ (Function.update p i π') i) k ≤
      upperContourSum (p i) (φ p i) k := hsp p i π' k
  have hback : Function.update (Function.update p i π') i (p i) = p := by
    ext j k'
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  have h2 := hsp (Function.update p i π') i (p i) k
  rw [hback, Function.update_self] at h2
  have hcongr : ∀ x : Fin n → ℝ,
      upperContourSum π' x k = upperContourSum (p i) x k := by
    intro x
    rw [upperContourSum_eq_sum_filter, upperContourSum_eq_sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext o
    simp [hset o]
  rw [hcongr, hcongr] at h2
  exact le_antisymm h2 h1

/-- Swapping two adjacent ranks `k` and `k + 1` in agent `i`'s preference leaves the probability of
every other object unchanged and preserves the sum of the two swapped objects' probabilities. -/
theorem IsSDStrategyProof.adjSwap_invariance {n : ℕ} {φ : AssignmentRule n}
    (hsp : IsSDStrategyProof φ) (p : Profile n) (i : Fin n) (k : Fin n) (hk : k.val + 1 < n)
    (π' : Equiv.Perm (Fin n))
    (hswap : π' = Equiv.swap (p i k) (p i ⟨k.val + 1, hk⟩) * p i) :
    (∀ r : Fin n, r ≠ k → r ≠ ⟨k.val + 1, hk⟩ →
      φ (Function.update p i π') i (p i r) = φ p i (p i r)) ∧
    φ (Function.update p i π') i (p i k) +
      φ (Function.update p i π') i (p i ⟨k.val + 1, hk⟩) =
    φ p i (p i k) + φ p i (p i ⟨k.val + 1, hk⟩) := by
  have hperm : ∀ r : Fin n, π' r =
      if r = k then p i ⟨k.val + 1, hk⟩
      else if r = ⟨k.val + 1, hk⟩ then p i k
      else p i r := by
    intro r
    rw [hswap, Equiv.Perm.mul_apply]
    by_cases h1 : r = k
    · subst h1; simp [Equiv.swap_apply_left]
    · by_cases h2 : r = ⟨k.val + 1, hk⟩
      · subst h2
        have hne : (⟨k.val + 1, hk⟩ : Fin n) ≠ k := by
          simp [Fin.ext_iff]
        simp [hne]
      · simp only [h1, h2, ↓reduceIte]
        exact Equiv.swap_apply_of_ne_of_ne (fun h => h1 ((p i).injective h))
          (fun h => h2 ((p i).injective h))
  have hsymm : ∀ r : Fin n, π'.symm (p i r) =
      if r = k then ⟨k.val + 1, hk⟩
      else if r = ⟨k.val + 1, hk⟩ then k
      else r := by
    intro r
    rw [Equiv.symm_apply_eq]
    by_cases h1 : r = k
    · subst h1
      have hne : (⟨r.val + 1, hk⟩ : Fin n) ≠ r := by simp [Fin.ext_iff]
      simp [hperm, hne]
    · by_cases h2 : r = ⟨k.val + 1, hk⟩
      · subst h2
        simp [hperm]
      · simp [hperm, h1, h2]
  have huc : ∀ s : Fin n, s ≠ k →
      upperContourSum (p i) (φ p i) s =
        upperContourSum (p i) (φ (Function.update p i π') i) s := by
    intro s hs
    refine hsp.upperContour_eq p i π' s fun o => ?_
    obtain ⟨r, rfl⟩ := (p i).surjective o
    rw [Equiv.symm_apply_apply, hsymm r]
    by_cases h1 : r = k
    · subst h1
      simp only [↓reduceIte, Fin.le_def]
      have : r.val ≠ s.val := fun heq => hs (Fin.ext heq.symm)
      omega
    · by_cases h2 : r = ⟨k.val + 1, hk⟩
      · subst h2
        simp only [h1, ↓reduceIte, Fin.le_def]
        have : s.val ≠ k.val := fun heq => hs (Fin.ext heq)
        omega
      · simp [h1, h2]
  refine ⟨fun r hr1 hr2 => ?_, ?_⟩
  · by_cases hr0 : r.val = 0
    · have hu := huc r hr1
      rw [upperContourSum_zero (p i) _ hr0, upperContourSum_zero (p i) _ hr0] at hu
      exact hu.symm
    · have hrpos : 0 < r.val := Nat.pos_of_ne_zero hr0
      have hprev : (⟨r.val - 1, by omega⟩ : Fin n) ≠ k := by
        intro heq
        apply hr2
        have hv : r.val - 1 = k.val := congrArg Fin.val heq
        ext; change r.val = k.val + 1; omega
      have hu1 := huc r hr1
      have hu0 := huc ⟨r.val - 1, by omega⟩ hprev
      rw [upperContourSum_succ (p i) _ hrpos, upperContourSum_succ (p i) _ hrpos] at hu1
      linarith
  · have hk1ne : (⟨k.val + 1, hk⟩ : Fin n) ≠ k := by simp [Fin.ext_iff]
    have htop := huc ⟨k.val + 1, hk⟩ hk1ne
    have hk1pos : 0 < (⟨k.val + 1, hk⟩ : Fin n).val := Nat.succ_pos k.val
    rw [upperContourSum_succ (p i) _ hk1pos, upperContourSum_succ (p i) _ hk1pos] at htop
    have hsub_eq : (⟨(⟨k.val + 1, hk⟩ : Fin n).val - 1, by omega⟩ : Fin n) = k := by
      ext; exact Nat.add_sub_cancel k.val 1
    rw [hsub_eq] at htop
    by_cases hk0 : k.val = 0
    · rw [upperContourSum_zero (p i) _ hk0, upperContourSum_zero (p i) _ hk0] at htop
      linarith
    · have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk0
      have hprev : (⟨k.val - 1, by omega⟩ : Fin n) ≠ k := by
        intro heq
        have hv : k.val - 1 = k.val := congrArg Fin.val heq
        omega
      have hbot := huc ⟨k.val - 1, by omega⟩ hprev
      rw [upperContourSum_succ (p i) _ hkpos, upperContourSum_succ (p i) _ hkpos] at htop
      linarith

/-- The pairwise trade (envy/improvement) relation induced by a random assignment `P`: there is a
directed edge `a ≻_P b` if some agent `i` receives positive probability of `b` and strictly
prefers `a` over `b`. -/
@[expose] def tradeRel {n : ℕ} (p : Profile n) (P : Matrix (Fin n) (Fin n) ℝ)
    (a b : Fin n) : Prop :=
  ∃ i : Fin n, 0 < P i b ∧ (p i).symm a < (p i).symm b

/-- Acyclicity of the trade relation: no object reaches itself along a non-empty directed path in
`tradeRel p P`. -/
@[expose] def IsAcyclicTrade {n : ℕ} (p : Profile n) (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ a : Fin n, ¬ Relation.TransGen (tradeRel p P) a a

lemma IsAcyclicTrade.not_twoCycle {n : ℕ} {p : Profile n} {P : Matrix (Fin n) (Fin n) ℝ}
    (ha : IsAcyclicTrade p P) {i j a b : Fin n}
    (hib : 0 < P i b) (hij : (p i).symm a < (p i).symm b)
    (hja : 0 < P j a) (hji : (p j).symm b < (p j).symm a) : False :=
  ha a (Relation.TransGen.trans (Relation.TransGen.single ⟨i, hib, hij⟩)
    (Relation.TransGen.single ⟨j, hja, hji⟩))

/-- Every nonempty finite set in an acyclic directed graph has a source (a vertex with no incoming
edge from inside the set). -/
lemma exists_source_of_acyclic {α : Type*} [Finite α] {r : α → α → Prop}
    (hacyc : ∀ x, ¬ Relation.TransGen r x x) (S : Finset α) (hne : S.Nonempty) :
    ∃ a ∈ S, ∀ b ∈ S, ¬ r b a := by
  have hirr : Std.Irrefl (Relation.TransGen r) := ⟨hacyc⟩
  have hwf : WellFounded (Relation.TransGen r) := Finite.wellFounded_of_trans_of_irrefl _
  obtain ⟨a, haS, hmin⟩ :=
    hwf.has_min (s := (S : Set α)) hne
  exact ⟨a, haS, fun b hb hba => hmin b hb (Relation.TransGen.single hba)⟩

/-- Extract a simple cycle (pairwise distinct vertices `c : Fin m → α`, `m ≥ 2`, with each
consecutive cyclic pair related by `r`) from any self-loop `TransGen r a a` of an irreflexive
relation `r`. -/
lemma exists_simple_cycle_of_transGen {α : Type*} {r : α → α → Prop}
    (hirr : ∀ x, ¬ r x x) {a : α} (h : Relation.TransGen r a a) :
    ∃ (m : ℕ) (_ : 2 ≤ m) (c : Fin m → α),
      Function.Injective c ∧
      ∀ j : Fin m, r (c ⟨(j.val + 1) % m, Nat.mod_lt _ (by omega)⟩) (c j) := by
  have hrev_exists : ∃ m : ℕ, 2 ≤ m ∧ ∃ c : Fin m → α,
      ∀ j : Fin m, r (c ⟨(j.val + 1) % m, Nat.mod_lt _ (Nat.zero_lt_of_lt j.isLt)⟩) (c j) := by
    have hwalk : ∀ {x y : α}, Relation.TransGen r x y →
        ∃ (k : ℕ) (hk : 1 ≤ k) (f : Fin k → α), f ⟨0, hk⟩ = y ∧
          (∀ (j : ℕ) (hj : j + 1 < k),
            r (f ⟨j + 1, hj⟩) (f ⟨j, by omega⟩)) ∧
          r x (f ⟨k - 1, by omega⟩) := by
      intro x y hxy
      induction hxy with
      | @single b hr =>
        exact ⟨1, le_rfl, fun _ => b, rfl, fun j hj => absurd hj (by omega), hr⟩
      | @tail b c _ hbc ih =>
        obtain ⟨k, hk, f, h0, hchain, hlast⟩ := ih
        refine ⟨k + 1, by omega,
          fun j => if h0j : j.val = 0 then c else f ⟨j.val - 1, by omega⟩,
          by simp, ?_, ?_⟩
        · intro j hj
          rcases Nat.eq_zero_or_pos j with rfl | hjpos
          · simp only [Nat.zero_add, Nat.one_ne_zero, ↓reduceDIte, Nat.sub_self]
            exact h0 ▸ hbc
          · have hjne : j ≠ 0 := hjpos.ne'
            have hj1ne : j + 1 ≠ 0 := by omega
            simp only [hjne, hj1ne, ↓reduceDIte]
            have := hchain (j - 1) (by omega)
            have heq1 : (⟨j + 1 - 1, by omega⟩ : Fin k) = ⟨j - 1 + 1, by omega⟩ := by
              ext; change j + 1 - 1 = j - 1 + 1; omega
            rw [heq1]
            exact this
        · have hne : k + 1 - 1 ≠ 0 := by omega
          simp only [hne, ↓reduceDIte]
          exact hlast
    obtain ⟨k, hk, f, h0, hchain, hlast⟩ := hwalk h
    have hge2 : 2 ≤ k := by
      by_contra hlt
      have hk1 : k = 1 := by omega
      have hsame : (⟨k - 1, by omega⟩ : Fin k) = ⟨0, hk⟩ := by ext; change k - 1 = 0; omega
      rw [hsame, h0] at hlast
      exact hirr a hlast
    refine ⟨k, hge2, f, fun i => ?_⟩
    by_cases hlasti : i.val + 1 = k
    · have hmod : (i.val + 1) % k = 0 := by rw [hlasti, Nat.mod_self]
      have h1 : (⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = ⟨0, hk⟩ := by
        ext; exact hmod
      have h2 : i = ⟨k - 1, by omega⟩ := by ext; change i.val = k - 1; omega
      rw [h1, h0, h2]
      exact hlast
    · have hlt : i.val + 1 < k := by omega
      have hmod : (i.val + 1) % k = i.val + 1 := Nat.mod_eq_of_lt hlt
      have h1 : (⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = ⟨i.val + 1, hlt⟩ := by
        ext; exact hmod
      rw [h1]
      exact hchain i.val hlt
  classical
  let P (m : ℕ) : Prop := 2 ≤ m ∧ ∃ c : Fin m → α,
    ∀ j : Fin m, r (c ⟨(j.val + 1) % m, Nat.mod_lt _ (Nat.zero_lt_of_lt j.isLt)⟩) (c j)
  set m := Nat.find hrev_exists
  have hm_spec : P m := Nat.find_spec hrev_exists
  have hm_min : ∀ k < m, ¬ P k := fun k hk => Nat.find_min hrev_exists hk
  obtain ⟨hm2, c, hstep⟩ := hm_spec
  refine ⟨m, hm2, c, ?_, hstep⟩
  intro x y hxy
  by_contra hne
  have hord : ∀ (p q : Fin m), c p = c q → p.val < q.val → False := by
    intro p q hpq hlt
    set d := q.val - p.val
    have hd_pos : 0 < d := by omega
    have hd_lt : d < m := by omega
    have hstep_sub : ∀ j : Fin d, r (c ⟨p.val + (j.val + 1) % d,
        by have := Nat.mod_lt (j.val + 1) hd_pos; omega⟩)
        (c ⟨p.val + j.val, by omega⟩) := by
      intro j
      by_cases hlast : j.val + 1 = d
      · have hmod : (j.val + 1) % d = 0 := by rw [hlast, Nat.mod_self]
        have hsub1 : (⟨p.val + (j.val + 1) % d, by omega⟩ : Fin m) = p := by
          ext; change p.val + (j.val + 1) % d = p.val; rw [hmod, add_zero]
        rw [hsub1]
        have hstep' := hstep ⟨p.val + j.val, by omega⟩
        have hmodm : (p.val + j.val + 1) % m = q.val := by
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        have hc1 : (⟨(p.val + j.val + 1) % m, Nat.mod_lt _ (by omega)⟩ : Fin m) = q := by
          ext; exact hmodm
        have heq : c ⟨(p.val + j.val + 1) % m, Nat.mod_lt _ (by omega)⟩ = c p := by
          rw [hc1, hpq]
        rwa [heq] at hstep'
      · have hmod : (j.val + 1) % d = j.val + 1 := Nat.mod_eq_of_lt (by omega)
        have hstep' := hstep ⟨p.val + j.val, by omega⟩
        have hmodm : (p.val + j.val + 1) % m = p.val + j.val + 1 :=
          Nat.mod_eq_of_lt (by omega)
        have hc1 : (⟨(p.val + j.val + 1) % m, Nat.mod_lt _ (by omega)⟩ : Fin m) =
            ⟨p.val + (j.val + 1) % d, by omega⟩ := by
          ext; change (p.val + j.val + 1) % m = p.val + (j.val + 1) % d
          rw [hmodm, hmod]; omega
        rwa [hc1] at hstep'
    by_cases hd1 : d = 1
    · have hself := hstep_sub ⟨0, hd_pos⟩
      have hmod : (0 + 1) % d = 0 := by rw [hd1]
      have hx0 : (⟨p.val + (0 + 1) % d, by omega⟩ : Fin m) = ⟨p.val + 0, by omega⟩ := by
        ext; change p.val + (0 + 1) % d = p.val + 0; rw [hmod]
      rw [hx0] at hself
      exact hirr _ hself
    · exact hm_min d hd_lt ⟨by omega, fun j => c ⟨p.val + j.val, by omega⟩, hstep_sub⟩
  rcases Nat.lt_or_gt_of_ne (fun hv => hne (Fin.ext hv)) with hlt | hgt
  · exact hord x y hxy hlt
  · exact hord y x hxy.symm hgt

/-- **Bogomolnaia–Moulin ordinal efficiency characterization** ([BogomolnaiaMoulin2001], locator
unverified): a doubly stochastic matrix `P` is `sd`-efficient if and only if its trade relation
`tradeRel p P` is acyclic. -/
theorem isSDEfficient_iff_isAcyclicTrade {n : ℕ} (p : Profile n) (P : Matrix (Fin n) (Fin n) ℝ) :
    IsSDEfficient p P ↔ P ∈ doublyStochastic ℝ (Fin n) ∧ IsAcyclicTrade p P := by
  constructor
  · rintro ⟨hP, hno⟩
    refine ⟨hP, fun a ha => hno ?_⟩
    have hirr : ∀ x, ¬ tradeRel p P x x := fun x ⟨i, _, hlt⟩ => lt_irrefl _ hlt
    obtain ⟨m, hm2, c, hc_inj, hstep⟩ := exists_simple_cycle_of_transGen hirr ha
    choose agent hpos hpref using hstep
    let next : Fin m → Fin n := fun j => c ⟨(j.val + 1) % m, Nat.mod_lt _ (by omega)⟩
    have hmpos : 0 < m := by omega
    have : Nonempty (Fin m) := ⟨⟨0, hmpos⟩⟩
    obtain ⟨j₀, _, hj₀⟩ :=
      Finset.exists_min_image (Finset.univ : Finset (Fin m)) (fun j => P (agent j) (c j))
        Finset.univ_nonempty
    let ε : ℝ := P (agent j₀) (c j₀)
    have hε_pos : 0 < ε := hpos j₀
    have hε_le : ∀ j : Fin m, ε ≤ P (agent j) (c j) := fun j => hj₀ j (Finset.mem_univ j)
    let Q : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i o =>
      P i o + ∑ j : Fin m,
        ((if agent j = i ∧ next j = o then ε else 0) -
         (if agent j = i ∧ c j = o then ε else 0))
    have hPds := mem_doublyStochastic_iff_sum.mp hP
    have hQds : Q ∈ doublyStochastic ℝ (Fin n) := by
      rw [mem_doublyStochastic_iff_sum]
      refine ⟨fun i o => ?_, fun i => ?_, fun o => ?_⟩
      · simp only [Q, Matrix.of_apply]
        have hpos_sum : 0 ≤ ∑ j : Fin m, (if agent j = i ∧ next j = o then ε else 0) :=
          Finset.sum_nonneg fun j _ => by split_ifs <;> linarith
        have hneg_le : ∑ j : Fin m, (if agent j = i ∧ c j = o then ε else 0) ≤ P i o := by
          by_cases hex : ∃ j : Fin m, agent j = i ∧ c j = o
          · obtain ⟨j, rfl, rfl⟩ := hex
            rw [Finset.sum_eq_single j]
            · simp [hε_le j]
            · intro j' _ hj'
              have hne : ¬ (agent j' = agent j ∧ c j' = c j) := fun h => hj' (hc_inj h.2)
              simp [hne]
            · intro hj; exact absurd (Finset.mem_univ j) hj
          · have hzero : ∑ j : Fin m, (if agent j = i ∧ c j = o then ε else 0) = 0 :=
              Finset.sum_eq_zero fun j _ =>
                ite_eq_right_iff.mpr fun h => absurd ⟨j, h⟩ hex
            rw [hzero]
            exact hPds.1 i o
        rw [Finset.sum_sub_distrib]
        linarith
      · -- Row sums equal 1.
        simp only [Q, Matrix.of_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
          (f := fun o j => if agent j = i ∧ next j = o then ε else 0)]
        rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
          (f := fun o j => if agent j = i ∧ c j = o then ε else 0)]
        have hrow : ∀ j : Fin m,
            ∑ o : Fin n, (if agent j = i ∧ next j = o then ε else 0) =
              ∑ o : Fin n, (if agent j = i ∧ c j = o then ε else 0) := by
          intro j
          by_cases hji : agent j = i
          · simp [hji]
          · simp [hji]
        simp only [hrow, sub_self, add_zero, hPds.2.1 i]
      · -- Column sums equal 1 (cyclic shift permutes `c j` to `next j`).
        simp only [Q, Matrix.of_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
          (f := fun i j => if agent j = i ∧ next j = o then ε else 0)]
        rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
          (f := fun i j => if agent j = i ∧ c j = o then ε else 0)]
        have hcol1 : ∀ j : Fin m,
            ∑ i : Fin n, (if agent j = i ∧ next j = o then ε else 0) =
              if next j = o then ε else 0 := by
          intro j
          rw [Finset.sum_eq_single (agent j)]
          · simp
          · intro i _ hi; simp [hi.symm]
          · intro h; exact absurd (Finset.mem_univ _) h
        have hcol2 : ∀ j : Fin m,
            ∑ i : Fin n, (if agent j = i ∧ c j = o then ε else 0) =
              if c j = o then ε else 0 := by
          intro j
          rw [Finset.sum_eq_single (agent j)]
          · simp
          · intro i _ hi; simp [hi.symm]
          · intro h; exact absurd (Finset.mem_univ _) h
        simp only [hcol1, hcol2]
        let rot : Equiv.Perm (Fin m) :=
          { toFun := fun j => ⟨(j.val + 1) % m, Nat.mod_lt _ hmpos⟩
            invFun := fun j => ⟨(j.val + (m - 1)) % m, Nat.mod_lt _ hmpos⟩
            left_inv := fun j => by
              ext; dsimp
              have h1 : (j.val + 1) % m + (m - 1) ≡ j.val + 1 + (m - 1) [MOD m] :=
                Nat.ModEq.add_right _ (Nat.mod_modEq _ _)
              change ((j.val + 1) % m + (m - 1)) % m = j.val
              rw [h1, show j.val + 1 + (m - 1) = j.val + m by omega, Nat.add_mod_right,
                Nat.mod_eq_of_lt j.isLt]
            right_inv := fun j => by
              ext; dsimp
              have h1 : (j.val + (m - 1)) % m + 1 ≡ j.val + (m - 1) + 1 [MOD m] :=
                Nat.ModEq.add_right _ (Nat.mod_modEq _ _)
              change ((j.val + (m - 1)) % m + 1) % m = j.val
              rw [h1, show j.val + (m - 1) + 1 = j.val + m by omega, Nat.add_mod_right,
                Nat.mod_eq_of_lt j.isLt] }
        have hsum_rot : ∑ j : Fin m, (if next j = o then ε else 0) =
            ∑ j : Fin m, (if c j = o then ε else 0) :=
          Equiv.sum_comp rot (fun j => if c j = o then ε else 0)
        rw [hsum_rot, sub_self, add_zero, hPds.2.2 o]
    have hdiff : ∀ (i k : Fin n),
        upperContourSum (p i) (Q i) k - upperContourSum (p i) (P i) k =
          ∑ j : Fin m,
            ((if agent j = i ∧ (p i).symm (next j) ≤ k then ε else 0) -
             (if agent j = i ∧ (p i).symm (c j) ≤ k then ε else 0)) := by
      intro i k
      rw [upperContourSum_eq_sum_filter, upperContourSum_eq_sum_filter,
        ← Finset.sum_sub_distrib]
      have : ∀ o : Fin n, Q i o - P i o =
          ∑ j : Fin m, ((if agent j = i ∧ next j = o then ε else 0) -
            (if agent j = i ∧ c j = o then ε else 0)) := fun o => by
        simp [Q]
      simp_rw [this]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_sub_distrib]
      congr 1
      · by_cases hji : agent j = i
        · subst hji
          by_cases hnk : (p (agent j)).symm (next j) ≤ k
          · simp only [hnk, and_self, ↓reduceIte]
            rw [Finset.sum_eq_single (next j)]
            · simp
            · intro o _ ho; simp [ho.symm]
            · intro hmem
              exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ (next j), hnk⟩) hmem
          · simp only [hnk, and_false, ↓reduceIte]
            refine Finset.sum_eq_zero fun o ho => ?_
            have ho' := (Finset.mem_filter.mp ho).2
            have hne : next j ≠ o := fun heq => hnk (heq ▸ ho')
            simp [hne]
        · simp only [hji, false_and, ↓reduceIte, Finset.sum_const_zero]
      · by_cases hji : agent j = i
        · subst hji
          by_cases hck : (p (agent j)).symm (c j) ≤ k
          · simp only [hck, and_self, ↓reduceIte]
            rw [Finset.sum_eq_single (c j)]
            · simp
            · intro o _ ho; simp [ho.symm]
            · intro hmem
              exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ (c j), hck⟩) hmem
          · simp only [hck, and_false, ↓reduceIte]
            refine Finset.sum_eq_zero fun o ho => ?_
            have ho' := (Finset.mem_filter.mp ho).2
            have hne : c j ≠ o := fun heq => hck (heq ▸ ho')
            simp [hne]
        · simp only [hji, false_and, ↓reduceIte, Finset.sum_const_zero]
    have hterm_nonneg : ∀ (i k : Fin n) (j : Fin m),
        0 ≤ (if agent j = i ∧ (p i).symm (next j) ≤ k then ε else 0) -
            (if agent j = i ∧ (p i).symm (c j) ≤ k then ε else 0) := by
      intro i k j
      by_cases hji : agent j = i
      · subst hji
        by_cases hck : (p (agent j)).symm (c j) ≤ k
        · have hnk : (p (agent j)).symm (next j) ≤ k := (hpref j).le.trans hck
          simp [hnk, hck]
        · simp only [hck, and_false, ↓reduceIte, sub_zero]
          split_ifs
          · exact hε_pos.le
          · exact le_rfl
      · simp [hji]
    have hweak : ∀ i : Fin n, SDDominates (p i) (Q i) (P i) := fun i k => by
      have hge : 0 ≤ upperContourSum (p i) (Q i) k - upperContourSum (p i) (P i) k := by
        rw [hdiff i k]
        exact Finset.sum_nonneg fun j _ => hterm_nonneg i k j
      linarith
    refine ⟨Q, hQds, hweak, agent j₀, hweak (agent j₀), (p (agent j₀)).symm (next j₀), ?_⟩
    have hterm_pos :
        (if agent j₀ = agent j₀ ∧ (p (agent j₀)).symm (next j₀) ≤
            (p (agent j₀)).symm (next j₀) then ε else 0) -
          (if agent j₀ = agent j₀ ∧ (p (agent j₀)).symm (c j₀) ≤
            (p (agent j₀)).symm (next j₀) then ε else 0) = ε := by
      have hnot : ¬ (p (agent j₀)).symm (c j₀) ≤ (p (agent j₀)).symm (next j₀) :=
        (hpref j₀).not_ge
      simp [hnot]
    have hsum_ge : ε ≤ upperContourSum (p (agent j₀)) (Q (agent j₀))
        ((p (agent j₀)).symm (next j₀)) -
        upperContourSum (p (agent j₀)) (P (agent j₀)) ((p (agent j₀)).symm (next j₀)) := by
      rw [hdiff]
      calc ε = (if agent j₀ = agent j₀ ∧ (p (agent j₀)).symm (next j₀) ≤
                  (p (agent j₀)).symm (next j₀) then ε else 0) -
                (if agent j₀ = agent j₀ ∧ (p (agent j₀)).symm (c j₀) ≤
                  (p (agent j₀)).symm (next j₀) then ε else 0) := hterm_pos.symm
        _ ≤ _ := Finset.single_le_sum
            (f := fun j =>
              (if agent j = agent j₀ ∧
                  (p (agent j₀)).symm (next j) ≤ (p (agent j₀)).symm (next j₀) then ε else 0) -
              (if agent j = agent j₀ ∧
                  (p (agent j₀)).symm (c j) ≤ (p (agent j₀)).symm (next j₀) then ε else 0))
            (fun j _ => hterm_nonneg _ _ j) (Finset.mem_univ j₀)
    linarith
  · rintro ⟨hP, hacyc⟩
    refine ⟨hP, ?_⟩
    rintro ⟨Q, hQ, hweak, i₀, hstrict⟩
    let R : Finset (Fin n) := Finset.univ.filter fun a => ∃ i : Fin n, Q i a ≠ P i a
    have hRne : R.Nonempty := by
      have hne : Q i₀ ≠ P i₀ := ((sdDominatesStrict_iff_ne _ _ _).mp hstrict).2
      have hex : ∃ a, Q i₀ a ≠ P i₀ a := by
        by_contra! hall
        exact hne (funext hall)
      obtain ⟨a, ha⟩ := hex
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i₀, ha⟩⟩
    obtain ⟨a, haR, hsrc⟩ := exists_source_of_acyclic hacyc R hRne
    have hPds := mem_doublyStochastic_iff_sum.mp hP
    have hQds := mem_doublyStochastic_iff_sum.mp hQ
    have hle : ∀ i : Fin n, P i a ≤ Q i a := by
      intro i
      rcases (hPds.1 i a).eq_or_lt with hzero | hpos
      · rw [← hzero]; exact hQds.1 i a
      · have hdom := hweak i ((p i).symm a)
        rw [upperContourSum_eq_sum_filter, upperContourSum_eq_sum_filter] at hdom
        have hlt_eq : ∀ b : Fin n, (p i).symm b < (p i).symm a → Q i b = P i b := by
          intro b hba
          by_contra hne
          exact hsrc b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hne⟩) ⟨i, hpos, hba⟩
        have hsplit : (Finset.univ.filter fun o : Fin n => (p i).symm o ≤ (p i).symm a) =
            insert a (Finset.univ.filter fun o : Fin n => (p i).symm o < (p i).symm a) := by
          ext o
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          exact ⟨fun h => h.eq_or_lt.imp (fun he => (p i).symm.injective he) id,
            fun h => h.elim (fun he => he ▸ le_rfl) le_of_lt⟩
        have hnotmem : a ∉
            (Finset.univ.filter fun o : Fin n => (p i).symm o < (p i).symm a) := by
          intro hm
          exact lt_irrefl _ (Finset.mem_filter.mp hm).2
        rw [hsplit, Finset.sum_insert hnotmem, Finset.sum_insert hnotmem] at hdom
        have hpref_eq :
            ∑ o ∈ Finset.univ.filter (fun o => (p i).symm o < (p i).symm a), Q i o =
              ∑ o ∈ Finset.univ.filter (fun o => (p i).symm o < (p i).symm a), P i o :=
          Finset.sum_congr rfl fun b hb => hlt_eq b (Finset.mem_filter.mp hb).2
        linarith
    have hcol : ∑ i : Fin n, (Q i a - P i a) = 0 := by
      rw [Finset.sum_sub_distrib, hQds.2.2 a, hPds.2.2 a, sub_self]
    have hall_eq : ∀ i ∈ (Finset.univ : Finset (Fin n)), Q i a - P i a = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sub_nonneg.mpr (hle i)).mp hcol
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp haR).2
    exact hi (sub_eq_zero.mp (hall_eq i (Finset.mem_univ i)))

lemma IsSDEfficient.not_twoCycle {n : ℕ} {p : Profile n} {P : Matrix (Fin n) (Fin n) ℝ}
    (heff : IsSDEfficient p P) {i j a b : Fin n}
    (hib : 0 < P i b) (hij : (p i).symm a < (p i).symm b)
    (hja : 0 < P j a) (hji : (p j).symm b < (p j).symm a) : False :=
  ((isSDEfficient_iff_isAcyclicTrade p P).mp heff).2.not_twoCycle hib hij hja hji

/-- Every `sd`-efficient random assignment is ex-post efficient: in any Birkhoff–von Neumann
decomposition into permutation matrices, every positively weighted matching is Pareto efficient. -/
theorem IsSDEfficient.isExPostEfficient {n : ℕ} {p : Profile n} {P : Matrix (Fin n) (Fin n) ℝ}
    (heff : IsSDEfficient p P) : IsExPostEfficient p P := by
  obtain ⟨w, hw_nn, hw_sum, hw_eq⟩ := exists_eq_sum_perm_of_mem_doublyStochastic heff.1
  refine ⟨w, hw_nn, hw_sum, ?_, hw_eq⟩
  intro μ hwμ ⟨ν, hweak, i₀, hstrict⟩
  let Q : Matrix (Fin n) (Fin n) ℝ :=
    P + w μ • (ν.permMatrix ℝ - μ.permMatrix ℝ)
  have hQ_eq : Q =
      ∑ σ : Equiv.Perm (Fin n),
        (if σ = μ then 0 else w σ) • σ.permMatrix ℝ + w μ • ν.permMatrix ℝ := by
    have hsplit : ∑ σ : Equiv.Perm (Fin n), w σ • σ.permMatrix ℝ =
        ∑ σ : Equiv.Perm (Fin n), (if σ = μ then 0 else w σ) • σ.permMatrix ℝ +
          w μ • μ.permMatrix ℝ := by
      have h1 : ∀ σ : Equiv.Perm (Fin n),
          w σ • σ.permMatrix ℝ =
            (if σ = μ then 0 else w σ) • σ.permMatrix ℝ +
              (if σ = μ then w μ • μ.permMatrix ℝ else 0) := by
        intro σ
        by_cases h : σ = μ <;> simp [h]
      calc ∑ σ : Equiv.Perm (Fin n), w σ • σ.permMatrix ℝ
          = ∑ σ : Equiv.Perm (Fin n),
              ((if σ = μ then 0 else w σ) • σ.permMatrix ℝ +
                (if σ = μ then w μ • μ.permMatrix ℝ else 0)) :=
            Finset.sum_congr rfl fun σ _ => h1 σ
        _ = ∑ σ : Equiv.Perm (Fin n), (if σ = μ then 0 else w σ) • σ.permMatrix ℝ +
              ∑ σ : Equiv.Perm (Fin n), (if σ = μ then w μ • μ.permMatrix ℝ else 0) :=
            Finset.sum_add_distrib
        _ = ∑ σ : Equiv.Perm (Fin n), (if σ = μ then 0 else w σ) • σ.permMatrix ℝ +
              w μ • μ.permMatrix ℝ := by
            congr 1
            rw [Finset.sum_ite_eq']
            simp [Finset.mem_univ]
    simp only [Q, ← hw_eq, hsplit, smul_sub]
    abel
  have hQds : Q ∈ doublyStochastic ℝ (Fin n) := by
    rw [mem_doublyStochastic_iff_sum]
    have hperm_row : ∀ σ : Equiv.Perm (Fin n), ∀ i, ∑ j, σ.permMatrix ℝ i j = 1 :=
      fun σ i => sum_row_of_mem_doublyStochastic (permMatrix_mem_doublyStochastic (σ := σ)) i
    have hperm_col : ∀ σ : Equiv.Perm (Fin n), ∀ j, ∑ i, σ.permMatrix ℝ i j = 1 :=
      fun σ j => sum_col_of_mem_doublyStochastic (permMatrix_mem_doublyStochastic (σ := σ)) j
    have hperm_nn : ∀ σ : Equiv.Perm (Fin n), ∀ i j, 0 ≤ σ.permMatrix ℝ i j :=
      fun σ i j => nonneg_of_mem_doublyStochastic (permMatrix_mem_doublyStochastic (σ := σ))
    have hsum_rest : ∑ σ : Equiv.Perm (Fin n), (if σ = μ then 0 else w σ) = 1 - w μ := by
      have h2 : ∑ σ : Equiv.Perm (Fin n), w σ =
          ∑ σ : Equiv.Perm (Fin n), (if σ = μ then 0 else w σ) + w μ := by
        have h1 : ∀ σ : Equiv.Perm (Fin n),
            w σ = (if σ = μ then 0 else w σ) + (if σ = μ then w μ else 0) := fun σ => by
          by_cases h : σ = μ <;> simp [h]
        calc ∑ σ : Equiv.Perm (Fin n), w σ
            = ∑ σ : Equiv.Perm (Fin n),
                ((if σ = μ then 0 else w σ) + (if σ = μ then w μ else 0)) :=
              Finset.sum_congr rfl fun σ _ => h1 σ
          _ = ∑ σ : Equiv.Perm (Fin n), (if σ = μ then 0 else w σ) +
                ∑ σ : Equiv.Perm (Fin n), (if σ = μ then w μ else 0) :=
              Finset.sum_add_distrib
          _ = ∑ σ : Equiv.Perm (Fin n), (if σ = μ then 0 else w σ) + w μ := by
              congr 1
              rw [Finset.sum_ite_eq']
              simp [Finset.mem_univ]
      linarith
    refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
    · rw [hQ_eq]
      simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      refine add_nonneg (Finset.sum_nonneg fun σ _ => mul_nonneg ?_ (hperm_nn σ i j))
        (mul_nonneg hwμ.le (hperm_nn ν i j))
      split_ifs
      · exact le_rfl
      · exact hw_nn σ
    · rw [hQ_eq]
      simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
        Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun j σ => (if σ = μ then 0 else w σ) * σ.permMatrix ℝ i j)]
      simp only [← Finset.mul_sum, hperm_row, mul_one, hsum_rest]
      linarith
    · rw [hQ_eq]
      simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
        Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i σ => (if σ = μ then 0 else w σ) * σ.permMatrix ℝ i j)]
      simp only [← Finset.mul_sum, hperm_col, mul_one, hsum_rest]
      linarith
  have hperm_uc : ∀ (π σ : Equiv.Perm (Fin n)) (i k : Fin n),
      upperContourSum π (σ.permMatrix ℝ i) k =
        if π.symm (σ i) ≤ k then 1 else 0 := by
    intro π σ i k
    rw [upperContourSum_eq_sum_filter]
    have hentry : ∀ o : Fin n, σ.permMatrix ℝ i o = if σ i = o then 1 else 0 := by
      intro o
      by_cases h : σ i = o
      · subst h; simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
      · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, h]
    simp_rw [hentry]
    by_cases h : π.symm (σ i) ≤ k
    · simp only [h, ↓reduceIte]
      rw [Finset.sum_eq_single (σ i)]
      · simp
      · intro o _ ho; simp [ho.symm]
      · intro hmem
        exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ (σ i), h⟩) hmem
    · simp only [h, ↓reduceIte]
      refine Finset.sum_eq_zero fun o ho => ?_
      have ho' := (Finset.mem_filter.mp ho).2
      have hne : σ i ≠ o := fun heq => h (heq ▸ ho')
      simp [hne]
  have hQ_uc : ∀ i k : Fin n,
      upperContourSum (p i) (Q i) k = upperContourSum (p i) (P i) k +
        w μ * ((if (p i).symm (ν i) ≤ k then 1 else 0) -
               (if (p i).symm (μ i) ≤ k then 1 else 0)) := by
    intro i k
    have hdiff_row : ∀ o : Fin n, Q i o =
        P i o + w μ * (ν.permMatrix ℝ i o - μ.permMatrix ℝ i o) := fun o => rfl
    unfold upperContourSum
    simp_rw [hdiff_row, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
    congr 2
    rw [← upperContourSum, ← upperContourSum, hperm_uc, hperm_uc]
  have hQ_dom : ∀ i : Fin n, SDDominates (p i) (Q i) (P i) := fun i k => by
    rw [hQ_uc]
    have hdiff : (0 : ℝ) ≤ (if (p i).symm (ν i) ≤ k then 1 else 0) -
        (if (p i).symm (μ i) ≤ k then 1 else 0) := by
      by_cases hμ : (p i).symm (μ i) ≤ k
      · have hν : (p i).symm (ν i) ≤ k := (hweak i).trans hμ
        simp [hμ, hν]
      · simp only [hμ, ↓reduceIte, sub_zero]
        split_ifs <;> norm_num
    nlinarith [hwμ.le]
  refine heff.2 ⟨Q, hQds, hQ_dom, i₀, hQ_dom i₀, (p i₀).symm (ν i₀), ?_⟩
  rw [hQ_uc]
  have hnot : ¬ (p i₀).symm (μ i₀) ≤ (p i₀).symm (ν i₀) := hstrict.not_ge
  simp only [le_refl, ↓reduceIte, hnot, sub_zero, mul_one]
  linarith

end Cslib.GameTheory.RandomAssignment
