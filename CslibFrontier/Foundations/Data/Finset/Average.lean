/-
Copyright (c) 2026 Anthropic, PBC, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Samuel Schlesinger
-/
module
-- upstream: candidate

public import CslibFrontier.Init

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# Few indices are far above the average

Let `f` be a function with natural numbers as values on a nonempty finite set `Q`.  Division is
avoided: "`f p` is at most `k` times the average of `f`" is written
`f p * |Q| ≤ k * ∑ p' ∈ Q, f p'`.

* Fewer than `|Q|/k` indices are more than `k` times as bad as the average
  (`Finset.mul_card_above_average_lt`, Markov's inequality).
* So for `k` functions there is one index at which each of them is at most `k` times its average
  (`Finset.exists_forall_mul_card_le_mul_sum`, the union bound).
* Given a vertex map `v : I → V`, nonnegative payoffs `W : I → α → R`, and vertex-wise
  sub-probability weights `p : V → α → R` (`0 ≤ p u a` and `∑ a, p u a ≤ 1`), choosing the best
  label at each vertex produces a deterministic assignment `f : V → α` whose total payoff is at
  least the weighted payoff (`Finset.exists_choice_sum_le`).

For the non-strict, unnormalised finite Markov bound, see
`Finset.mul_card_filter_le_sum` in `CslibFrontier/Foundations/Data/Finset/Markov.lean`.

Adapted from [Average.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Util/Average.lean) in
`anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.

## Main results

* `Finset.exists_forall_mul_card_le_mul_sum`: simultaneous finite average bound.
* `Finset.exists_choice_sum_le`: deterministic vertex-wise maximum choice beats any vertex-wise
  sub-probability weighting.

-/

public section

namespace Finset

/-- Markov's inequality: fewer than `|Q|/k` indices are more than `k` times as bad as the
average. -/
theorem mul_card_above_average_lt {ι : Type*} {Q : Finset ι} (hQ : Q.Nonempty) (k : ℕ)
    (f : ι → ℕ) : k * #{p ∈ Q | k * ∑ p' ∈ Q, f p' < f p * #Q} < #Q := by
  set B := {p ∈ Q | k * ∑ p' ∈ Q, f p' < f p * #Q}
  rcases B.eq_empty_or_nonempty with he | hne
  · rw [he, card_empty, mul_zero]
    exact hQ.card_pos
  refine lt_of_mul_lt_mul_right (a := ∑ p ∈ Q, f p) ?_ (Nat.zero_le _)
  calc k * #B * ∑ p ∈ Q, f p = ∑ _p ∈ B, k * ∑ p' ∈ Q, f p' := by
        rw [sum_const, smul_eq_mul]; ring
    _ < ∑ p ∈ B, f p * #Q := sum_lt_sum_of_nonempty hne fun p hp => (mem_filter.mp hp).2
    _ ≤ ∑ p ∈ Q, f p * #Q := sum_le_sum_of_subset (filter_subset _ _)
    _ = #Q * ∑ p ∈ Q, f p := by rw [← sum_mul, mul_comm]

/-- The union bound: one index is good for `k` functions at once, in that each function is at most
`k` times its average there. -/
theorem exists_forall_mul_card_le_mul_sum {ι : Type*} {Q : Finset ι} (hQ : Q.Nonempty) (k : ℕ)
    (f : Fin k → ι → ℕ) : ∃ p ∈ Q, ∀ i, f i p * #Q ≤ k * ∑ p' ∈ Q, f i p' := by
  classical
  by_contra hcon
  push Not at hcon
  set B : Fin k → Finset ι := fun i => {p ∈ Q | k * ∑ p' ∈ Q, f i p' < f i p * #Q}
  have hcover : Q ⊆ univ.biUnion B := fun p hp =>
    let ⟨i, hi⟩ := hcon p hp
    mem_biUnion.mpr ⟨i, mem_univ i, mem_filter.mpr ⟨hp, hi⟩⟩
  -- there is at least one function, which the strict inequality below needs
  obtain ⟨i₀, -⟩ := hcon _ hQ.choose_spec
  refine lt_irrefl (k * #Q) ?_
  calc k * #Q ≤ k * ∑ i, #(B i) :=
        Nat.mul_le_mul_left _ ((card_le_card hcover).trans card_biUnion_le)
    _ = ∑ i, k * #(B i) := mul_sum ..
    _ < ∑ _i : Fin k, #Q :=
        sum_lt_sum_of_nonempty ⟨i₀, mem_univ i₀⟩ fun i _ => mul_card_above_average_lt hQ k (f i)
    _ = k * #Q := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

/-- **Deterministic vertex-choice lemma**: given a vertex map `v : I → V`, nonnegative payoffs
`W : I → α → R`, and vertex-wise sub-probability weights `p : V → α → R` (`0 ≤ p u a` and
`∑ a, p u a ≤ 1`), choosing the best label at each vertex produces a deterministic assignment
`f : V → α` whose payoff is at least the weighted payoff under `p`. -/
theorem exists_choice_sum_le {I V α R : Type*} [Fintype I] [Fintype α] [Nonempty α]
    [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
    (v : I → V) (W : I → α → R) (hW : ∀ i a, 0 ≤ W i a)
    (p : V → α → R) (hp0 : ∀ u a, 0 ≤ p u a) (hp1 : ∀ u, ∑ a : α, p u a ≤ 1) :
    ∃ f : V → α, (∑ i : I, ∑ a : α, p (v i) a * W i a) ≤ ∑ i : I, W i (f (v i)) := by
  classical
  let U (u : V) (a : α) : R := ∑ i ∈ univ.filter (v · = u), W i a
  have hmax (u : V) : ∃ b : α, ∀ a : α, U u a ≤ U u b := by
    obtain ⟨b, _, hb⟩ := univ.exists_max_image (U u) univ_nonempty
    exact ⟨b, fun a => hb a (mem_univ a)⟩
  choose f hf using hmax
  refine ⟨f, ?_⟩
  rw [← sum_fiberwise_of_maps_to (g := v) (t := univ.image v)
      (fun i _ => mem_image_of_mem v (mem_univ i)),
    ← sum_fiberwise_of_maps_to (g := v) (t := univ.image v)
      (fun i _ => mem_image_of_mem v (mem_univ i))]
  refine sum_le_sum fun u _ => ?_
  calc ∑ i ∈ univ.filter (v · = u), ∑ a : α, p (v i) a * W i a
      = ∑ i ∈ univ.filter (v · = u), ∑ a : α, p u a * W i a :=
        sum_congr rfl fun i hi => by rw [(mem_filter.mp hi).2]
    _ = ∑ a : α, p u a * U u a := by
        rw [sum_comm]; exact sum_congr rfl fun a _ => (mul_sum ..).symm
    _ ≤ ∑ a : α, p u a * U u (f u) :=
        sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hf u a) (hp0 u a)
    _ = (∑ a : α, p u a) * U u (f u) := (sum_mul ..).symm
    _ ≤ 1 * U u (f u) :=
        mul_le_mul_of_nonneg_right (hp1 u) (sum_nonneg fun i _ => hW i (f u))
    _ = ∑ i ∈ univ.filter (v · = u), W i (f (v i)) := by
        rw [one_mul]; exact sum_congr rfl fun i hi => by rw [(mem_filter.mp hi).2]

end Finset
