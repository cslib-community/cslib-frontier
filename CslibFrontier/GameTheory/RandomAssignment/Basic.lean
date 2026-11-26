/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Relation.Acyclic
public import Mathlib.Analysis.Convex.DoublyStochasticMatrix
public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Relation

import CslibFrontier.Foundations.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Equiv.Fin.Rotate
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
* `Cslib.GameTheory.RandomAssignment.tradeRel`: the pairwise trade relation `a ≻_P b`.

## Main results

* `Cslib.GameTheory.RandomAssignment.sdDominates_iff_forall_antitone`: first-order stochastic
  dominance is equivalent to weakly higher expected utility under every rank-consistent utility.
* `Cslib.GameTheory.RandomAssignment.isSDEfficient_iff_isAcyclicTrade`: a doubly stochastic matrix
  is `sd`-efficient if and only if its trade relation `tradeRel p P` is `Relation.Acyclic`.
* `Cslib.GameTheory.RandomAssignment.IsSDEfficient.isExPostEfficient`: `sd`-efficiency implies
  ex-post efficiency (via Mathlib's Birkhoff–von Neumann theorem).
* `Cslib.GameTheory.RandomAssignment.IsSDStrategyProof.upperContour_eq`: upper-contour-set
  invariance under `sd`-strategy-proof rules (and adjacent-swap specialization
  `IsSDStrategyProof.adjSwap_invariance`).

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

lemma upperContourSum_eq_sum_filter {n : ℕ} (π : Equiv.Perm (Fin n)) (x : Fin n → ℝ)
    (k : Fin n) :
    upperContourSum π x k = ∑ o : Fin n with π.symm o ≤ k, x o := by
  exact Finset.sum_nbij' π π.symm (by simp) (by simp) (by simp) (by simp) (by simp)

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

private lemma apply_eq_of_upperContourSum_eq {n : ℕ} (π : Equiv.Perm (Fin n)) {x y : Fin n → ℝ}
    {r : Fin n} (hr : upperContourSum π x r = upperContourSum π y r)
    (hprev : ∀ _ : 0 < r.val,
      upperContourSum π x ⟨r.val - 1, by omega⟩ = upperContourSum π y ⟨r.val - 1, by omega⟩) :
    x (π r) = y (π r) := by
  by_cases hr0 : r.val = 0
  · rwa [upperContourSum_zero π x hr0, upperContourSum_zero π y hr0] at hr
  · have hrpos : 0 < r.val := Nat.pos_of_ne_zero hr0
    rw [upperContourSum_succ π x hrpos, upperContourSum_succ π y hrpos, hprev hrpos] at hr
    linarith

lemma eq_of_upperContourSum_eq {n : ℕ} (π : Equiv.Perm (Fin n)) {x y : Fin n → ℝ}
    (h : ∀ k : Fin n, upperContourSum π x k = upperContourSum π y k) : x = y := by
  funext o
  simpa using apply_eq_of_upperContourSum_eq π (h (π.symm o)) fun _ => h _

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

lemma sdDominatesStrict_iff_ne {n : ℕ} (π : Equiv.Perm (Fin n)) (x y : Fin n → ℝ) :
    SDDominatesStrict π x y ↔ SDDominates π x y ∧ x ≠ y := by
  refine ⟨fun ⟨hdom, k, hk⟩ => ⟨hdom, ?_⟩, fun ⟨hdom, hne⟩ => ⟨hdom, ?_⟩⟩
  · rintro rfl
    exact lt_irrefl _ hk
  · by_contra! hle
    exact hne (hdom.antisymm hle)

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
    simp [upperContourSum_eq_sum_filter]
  constructor
  · intro h
    by_contra hlt
    have hk := h (π.symm b)
    simp only [heval, le_refl, hlt, ↓reduceIte] at hk
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
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    have h := Fin.sum_univ_smul_by_parts_prefix (d ∘ π) (u ∘ π)
    simp only [Function.comp_apply, smul_eq_mul] at h
    rw [Equiv.sum_comp π d] at h
    rw [← Equiv.sum_comp π (fun o => d o * u o)]
    rw [h.trans (add_comm _ _)]
    simp only [Nat.succ_sub_one]
    congr 1

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
    suffices h : 0 ≤ ∑ o : Fin n, (x - y) o * u o by
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib] at h
      linarith
    rw [sum_mul_eq_abel π (x - y) u]
    have hzero : ∑ o : Fin n, (x - y) o = 0 := by
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, hsum, sub_self]
    rw [hzero, zero_mul, add_zero]
    refine Finset.sum_nonneg fun k _ => mul_nonneg ?_ ?_
    · simp only [upperContourSum, Pi.sub_apply, Finset.sum_sub_distrib]
      exact sub_nonneg.mpr (hdom ⟨k.val, by omega⟩)
    · exact sub_nonneg.mpr (hu (by simp [Fin.le_def]))
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
  have h2 := hsp (Function.update p i π') i (p i) k
  simp only [Function.update_idem, Function.update_eq_self, Function.update_self] at h2
  have hcongr (x : Fin n → ℝ) : upperContourSum π' x k = upperContourSum (p i) x k := by
    rw [upperContourSum_eq_sum_filter, upperContourSum_eq_sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext o
    simp [hset o]
  rw [hcongr, hcongr] at h2
  exact le_antisymm h2 (hsp p i π' k)

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
  have hsymm : ∀ r : Fin n, π'.symm (p i r) = Equiv.swap k ⟨k.val + 1, hk⟩ r := fun r => by
    rw [Equiv.symm_apply_eq, hswap, Equiv.Perm.mul_apply, ← (p i).injective.swap_apply,
      Equiv.swap_apply_self]
  have huc : ∀ s : Fin n, s ≠ k →
      upperContourSum (p i) (φ p i) s =
        upperContourSum (p i) (φ (Function.update p i π') i) s := by
    intro s hs
    refine hsp.upperContour_eq p i π' s fun o => ?_
    obtain ⟨r, rfl⟩ := (p i).surjective o
    have hs' : s.val ≠ k.val := fun h => hs (Fin.ext h)
    rw [Equiv.symm_apply_apply, hsymm r, Equiv.swap_apply_def]
    split_ifs with h1 h2
    · subst h1; simp only [Fin.le_def]; omega
    · subst h2; simp only [Fin.le_def]; omega
    · exact Iff.rfl
  refine ⟨fun r hr1 hr2 => ?_, ?_⟩
  · refine (apply_eq_of_upperContourSum_eq (p i) (huc r hr1) fun _ => huc _ ?_).symm
    intro heq
    have hv : r.val - 1 = k.val := congrArg Fin.val heq
    exact hr2 (Fin.ext (by dsimp; omega))
  · have htop := huc ⟨k.val + 1, hk⟩ (by simp [Fin.ext_iff])
    have hk1pos : 0 < (⟨k.val + 1, hk⟩ : Fin n).val := Nat.succ_pos k.val
    have hsub_eq : (⟨(⟨k.val + 1, hk⟩ : Fin n).val - 1, by omega⟩ : Fin n) = k :=
      Fin.ext (Nat.add_sub_cancel k.val 1)
    rw [upperContourSum_succ (p i) _ hk1pos, upperContourSum_succ (p i) _ hk1pos, hsub_eq] at htop
    by_cases hk0 : k.val = 0
    · rw [upperContourSum_zero (p i) _ hk0, upperContourSum_zero (p i) _ hk0] at htop
      linarith
    · have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk0
      have hbot := huc ⟨k.val - 1, by omega⟩ (Fin.ne_of_val_ne (Nat.sub_one_lt hk0).ne)
      rw [upperContourSum_succ (p i) _ hkpos, upperContourSum_succ (p i) _ hkpos, hbot] at htop
      linarith

/-- The pairwise trade (envy/improvement) relation induced by a random assignment `P`: there is a
directed edge `a ≻_P b` if some agent `i` receives positive probability of `b` and strictly
prefers `a` over `b`. -/
@[expose] def tradeRel {n : ℕ} (p : Profile n) (P : Matrix (Fin n) (Fin n) ℝ)
    (a b : Fin n) : Prop :=
  ∃ i : Fin n, 0 < P i b ∧ (p i).symm a < (p i).symm b

/-- Every simple cycle extracted from a self-loop in `tradeRel p P`, reusing
`Relation.exists_cycle_chain_of_transGen` and `Relation.exists_nodup_of_cycle_chain`. -/
lemma exists_simple_tradeCycle {n : ℕ} {p : Profile n} {P : Matrix (Fin n) (Fin n) ℝ}
    {a : Fin n} (h : Relation.TransGen (tradeRel p P) a a) :
    ∃ (m : ℕ) (_ : 2 ≤ m) (c : Fin m → Fin n),
      Function.Injective c ∧
      ∀ j : Fin m, tradeRel p P (c ⟨(j.val + 1) % m, Nat.mod_lt _ (by omega)⟩) (c j) := by
  obtain ⟨l₀, hal, hch₀⟩ := Relation.exists_cycle_chain_of_transGen (Relation.transGen_swap.mpr h)
  obtain ⟨l, hlne, hlnd, -, hlch⟩ :=
    Relation.exists_nodup_of_cycle_chain (List.ne_nil_of_mem hal) hch₀
  rcases l with _ | ⟨x, t⟩
  · exact absurd rfl hlne
  rw [Cycle.chain_coe_cons] at hlch
  set m := (x :: t).length
  have hm_pos : 0 < m := Nat.zero_lt_succ _
  have hget_chain : ∀ k (hk : k < m),
      tradeRel p P ((x :: t)[(k + 1) % m]'(Nat.mod_lt _ hm_pos)) ((x :: t)[k]) := by
    intro k hk
    have hlt_ext : k + 1 < (x :: t ++ [x]).length := by simp [m] at hk ⊢; omega
    have hrel := List.isChain_iff_getElem.mp hlch k hlt_ext
    change tradeRel p P (x :: t ++ [x])[k + 1] (x :: t ++ [x])[k] at hrel
    rw [List.getElem_append_left hk] at hrel
    by_cases hlast : k + 1 = m
    · rw [List.getElem_append_right (by omega)] at hrel
      simpa [m, hlast] using hrel
    · have hlt' : k + 1 < m := by omega
      rw [List.getElem_append_left hlt'] at hrel
      simpa only [Nat.mod_eq_of_lt hlt'] using hrel
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have h0 : (0 + 1) % m = 0 := by rw [show m = 1 by lia]
    obtain ⟨_, _, hlt'⟩ := hget_chain 0 hm_pos
    exact lt_irrefl _ (by simpa only [h0] using hlt')
  exact ⟨m, hm2, fun j => (x :: t)[j.val],
    fun _ _ h => Fin.ext ((List.Nodup.getElem_inj_iff hlnd).mp h),
    fun j => hget_chain j.val j.isLt⟩

/-- **Bogomolnaia–Moulin ordinal efficiency characterization** ([BogomolnaiaMoulin2001], locator
unverified): a doubly stochastic matrix `P` is `sd`-efficient if and only if its trade relation
`tradeRel p P` is acyclic (`Relation.Acyclic`). -/
theorem isSDEfficient_iff_isAcyclicTrade {n : ℕ} (p : Profile n) (P : Matrix (Fin n) (Fin n) ℝ) :
    IsSDEfficient p P ↔ P ∈ doublyStochastic ℝ (Fin n) ∧ Relation.Acyclic (tradeRel p P) := by
  constructor
  · rintro ⟨hP, hno⟩
    refine ⟨hP, ⟨fun a ha => hno ?_⟩⟩
    obtain ⟨m, hm2, c, hc_inj, hstep⟩ := exists_simple_tradeCycle ha
    have hmpos : 0 < m := by lia
    let : NeZero m := ⟨hmpos.ne'⟩
    have hrotate (j : Fin m) :
        finRotate m j = ⟨(j.val + 1) % m, Nat.mod_lt _ hmpos⟩ := by
      apply Fin.ext
      rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < m by lia)]
    simp only [← hrotate] at hstep
    choose agent hpos hpref using hstep
    let next : Fin m → Fin n := fun j => c (finRotate m j)
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
        have hrow_sum : ∀ f : Fin m → Fin n,
            ∑ o : Fin n, ∑ j : Fin m, (if agent j = i ∧ f j = o then ε else 0) =
              ∑ j : Fin m, (if agent j = i then ε else 0) := fun f => by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => by by_cases hji : agent j = i <;> simp [hji]
        simp only [Q, Matrix.of_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          hrow_sum next, hrow_sum c, sub_self, add_zero, hPds.2.1 i]
      · -- Column sums equal 1 (cyclic shift permutes `c j` to `next j`).
        have hcol_sum : ∀ f : Fin m → Fin n,
            ∑ i : Fin n, ∑ j : Fin m, (if agent j = i ∧ f j = o then ε else 0) =
              ∑ j : Fin m, (if f j = o then ε else 0) := fun f => by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => by by_cases h : f j = o <;> simp [h]
        simp only [Q, Matrix.of_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          hcol_sum next, hcol_sum c]
        have hsum_rot : ∑ j : Fin m, (if next j = o then ε else 0) =
            ∑ j : Fin m, (if c j = o then ε else 0) :=
          Equiv.sum_comp (finRotate m) (fun j => if c j = o then ε else 0)
        rw [hsum_rot, sub_self, add_zero, hPds.2.2 o]
    have hdiff : ∀ (i k : Fin n),
        upperContourSum (p i) (Q i) k - upperContourSum (p i) (P i) k =
          ∑ j : Fin m,
            ((if agent j = i ∧ (p i).symm (next j) ≤ k then ε else 0) -
             (if agent j = i ∧ (p i).symm (c j) ≤ k then ε else 0)) := by
      intro i k
      rw [upperContourSum_eq_sum_filter, upperContourSum_eq_sum_filter,
        ← Finset.sum_sub_distrib]
      simp only [Q, Matrix.of_apply, add_sub_cancel_left]
      rw [Finset.sum_comm]
      have hterm_uc : ∀ (f : Fin m → Fin n) (j : Fin m),
          ∑ o ∈ Finset.univ.filter (fun o => (p i).symm o ≤ k),
              (if agent j = i ∧ f j = o then ε else 0) =
            if agent j = i ∧ (p i).symm (f j) ≤ k then ε else 0 := fun f j => by
        by_cases hji : agent j = i <;> simp [hji]
      exact Finset.sum_congr rfl fun j _ => by
        rw [Finset.sum_sub_distrib, hterm_uc next j, hterm_uc c j]
    have hterm_nonneg : ∀ (i k : Fin n) (j : Fin m),
        0 ≤ (if agent j = i ∧ (p i).symm (next j) ≤ k then ε else 0) -
            (if agent j = i ∧ (p i).symm (c j) ≤ k then ε else 0) := by
      intro i k j
      by_cases hck : agent j = i ∧ (p i).symm (c j) ≤ k
      · obtain ⟨rfl, h⟩ := hck
        simp [show (p (agent j)).symm (next j) ≤ k from (hpref j).le.trans h, h]
      · simp only [hck, ↓reduceIte, sub_zero]
        split_ifs <;> linarith
    have hweak : ∀ i : Fin n, SDDominates (p i) (Q i) (P i) := fun i k =>
      sub_nonneg.mp ((Finset.sum_nonneg fun j _ => hterm_nonneg i k j).trans_eq (hdiff i k).symm)
    refine ⟨Q, hQds, hweak, agent j₀, hweak (agent j₀), (p (agent j₀)).symm (next j₀), ?_⟩
    have h := Finset.single_le_sum
      (fun j _ => hterm_nonneg (agent j₀) ((p (agent j₀)).symm (next j₀)) j) (Finset.mem_univ j₀)
    rw [← hdiff] at h
    have hnot : ¬ (p (agent j₀)).symm (c j₀) ≤ (p (agent j₀)).symm (next j₀) := (hpref j₀).not_ge
    simp only [true_and, le_refl, ↓reduceIte, hnot, sub_zero] at h
    linarith
  · rintro ⟨hP, hacyc⟩
    refine ⟨hP, ?_⟩
    rintro ⟨Q, hQ, hweak, i₀, hstrict⟩
    let R : Finset (Fin n) := Finset.univ.filter fun a => ∃ i : Fin n, Q i a ≠ P i a
    obtain ⟨a₀, ha₀⟩ := Function.ne_iff.mp ((sdDominatesStrict_iff_ne _ _ _).mp hstrict).2
    have hRne : R.Nonempty := ⟨a₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i₀, ha₀⟩⟩
    obtain ⟨rank, -, hrank⟩ :=
      hacyc.exists_rank Finset.univ fun _ _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩
    obtain ⟨a, haR, hmin⟩ := Finset.exists_min_image R rank hRne
    have hsrc : ∀ b ∈ R, ¬ tradeRel p P b a := fun b hb hba =>
      (hrank b a hba).not_ge (hmin b hb)
    have hPds := mem_doublyStochastic_iff_sum.mp hP
    have hQds := mem_doublyStochastic_iff_sum.mp hQ
    have hle : ∀ i : Fin n, P i a ≤ Q i a := by
      intro i
      rcases (hPds.1 i a).eq_or_lt with hzero | hpos
      · rw [← hzero]; exact hQds.1 i a
      · have hdom := hweak i ((p i).symm a)
        rw [upperContourSum_eq_sum_filter, upperContourSum_eq_sum_filter] at hdom
        have ha_mem : a ∈ Finset.univ.filter (fun o : Fin n => (p i).symm o ≤ (p i).symm a) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ a, le_rfl⟩
        rw [← Finset.add_sum_erase _ _ ha_mem, ← Finset.add_sum_erase _ _ ha_mem] at hdom
        have hpref_eq :
            ∑ o ∈ (Finset.univ.filter fun o => (p i).symm o ≤ (p i).symm a).erase a, Q i o =
              ∑ o ∈ (Finset.univ.filter fun o => (p i).symm o ≤ (p i).symm a).erase a, P i o :=
          Finset.sum_congr rfl fun b hb => by
            obtain ⟨hb_ne, hb_le⟩ := Finset.mem_erase.mp hb
            have hba : (p i).symm b < (p i).symm a :=
              lt_of_le_of_ne (Finset.mem_filter.mp hb_le).2 ((p i).symm.injective.ne hb_ne)
            by_contra hne
            exact hsrc b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hne⟩) ⟨i, hpos, hba⟩
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
  ((isSDEfficient_iff_isAcyclicTrade p P).mp heff).2.irrefl a
    (Relation.TransGen.trans (Relation.TransGen.single ⟨i, hib, hij⟩)
      (Relation.TransGen.single ⟨j, hja, hji⟩))

/-- Every `sd`-efficient random assignment is ex-post efficient: in any Birkhoff–von Neumann
decomposition into permutation matrices, every positively weighted matching is Pareto efficient. -/
theorem IsSDEfficient.isExPostEfficient {n : ℕ} {p : Profile n} {P : Matrix (Fin n) (Fin n) ℝ}
    (heff : IsSDEfficient p P) : IsExPostEfficient p P := by
  obtain ⟨w, hw_nn, hw_sum, hw_eq⟩ := exists_eq_sum_perm_of_mem_doublyStochastic heff.1
  refine ⟨w, hw_nn, hw_sum, ?_, hw_eq⟩
  intro μ hwμ ⟨ν, hweak, i₀, hstrict⟩
  let Q : Matrix (Fin n) (Fin n) ℝ :=
    P + w μ • (ν.permMatrix ℝ - μ.permMatrix ℝ)
  have hPds := mem_doublyStochastic_iff_sum.mp heff.1
  have hperm (σ : Equiv.Perm (Fin n)) :=
    mem_doublyStochastic_iff_sum.mp (permMatrix_mem_doublyStochastic (R := ℝ) (σ := σ))
  have hQds : Q ∈ doublyStochastic ℝ (Fin n) := by
    rw [mem_doublyStochastic_iff_sum]
    simp only [Q, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hPds.2.1, hPds.2.2,
      (hperm ν).2.1, (hperm μ).2.1, (hperm ν).2.2, (hperm μ).2.2, sub_self, mul_zero, add_zero,
      implies_true, and_true]
    intro i j
    -- `P` dominates the `μ`-summand of its Birkhoff–von Neumann decomposition.
    have hμ : w μ * μ.permMatrix ℝ i j ≤ P i j := by
      rw [← hw_eq, Matrix.sum_apply]
      exact Finset.single_le_sum (f := fun σ => (w σ • σ.permMatrix ℝ) i j)
        (fun σ _ => mul_nonneg (hw_nn σ) ((hperm σ).1 i j)) (Finset.mem_univ μ)
    linarith [mul_nonneg hwμ.le ((hperm ν).1 i j)]
  have hQ_uc : ∀ i k : Fin n,
      upperContourSum (p i) (Q i) k = upperContourSum (p i) (P i) k +
        w μ * ((if (p i).symm (ν i) ≤ k then 1 else 0) -
               (if (p i).symm (μ i) ≤ k then 1 else 0)) := fun i k => by
    have hperm_uc (σ : Equiv.Perm (Fin n)) :
        ∑ r ∈ Finset.Iic k, σ.permMatrix ℝ i (p i r) =
          if (p i).symm (σ i) ≤ k then 1 else 0 := by
      simpa only [upperContourSum] using
        (by simp [upperContourSum_eq_sum_filter] :
          upperContourSum (p i) (σ.permMatrix ℝ i) k = _)
    simp only [upperContourSum, Q, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hperm_uc]
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
