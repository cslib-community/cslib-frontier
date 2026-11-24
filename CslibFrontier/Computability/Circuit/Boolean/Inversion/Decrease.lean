/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Inversion.Basic
public import CslibFrontier.Foundations.Data.BitString.Weight
public import Mathlib.Data.List.Chain
import Mathlib.Data.List.Destutter
import Mathlib.Order.Lattice.Nat

/-!
# Decreases of a Boolean system along chains

The decrease of a finite system of Boolean functions is the maximum number of adjacent
transitions along an increasing input chain at which at least one output changes from true
to false. The outputs may also have increasing coordinates at the same transition: the test
is failure of the pointwise order, rather than strict decrease of the whole output vector.

`chainDecrease` counts these transitions on a list. `decreaseTo` takes the maximum over
chains lying below a given input; these maxima give the canonical descent rank needed in
Markov's construction. `decrease` is the maximum over all increasing input chains.

The lists may be empty or may repeat inputs. Empty lists contribute zero, and repetitions
contribute no decreases, so these conventions give the usual maximum over strictly
increasing chains. All maxima are attained and are at most the number of input coordinates.

## Main results

* `Cslib.Circuits.Boolean.isDescentRank_decreaseTo`: the canonical descent rank.
* `Cslib.Circuits.Boolean.exists_chain_decrease`: attainment of the maximum chain decrease.
* `Cslib.Circuits.Boolean.exists_strict_chain_decrease`: the same maximum on a nonempty,
  strictly increasing chain, matching Markov's chain convention.
* `Cslib.Circuits.Boolean.decrease_le_numInputs`: the input-dimension bound.
* `Cslib.Circuits.Boolean.decrease_eq_zero_iff`: zero decrease characterizes monotonicity.

## References

* [A. A. Markov, *On the Inversion Complexity of a System of Boolean Functions*][Markov1963],
  §3, printed pp. 477–478, for the decrease of a system. The canonical rank uses maximal
  decreases below an input; Markov's Lemma 5.1 uses the dual rank above an input.
-/

public section

namespace Cslib.Circuits.Boolean

variable {X α β : Type*} [Preorder α] [Preorder β]

open scoped Classical in
/-- The number of adjacent transitions on a list at which the target fails to increase. -/
@[expose] noncomputable def chainDecrease (target : X → β) : List X → ℕ
  | x :: y :: xs => (if target x ≤ target y then 0 else 1) + chainDecrease target (y :: xs)
  | _ => 0

/-- Concatenating two chains preserves all decreases internal to either chain. -/
theorem chainDecrease_append_le (target : X → β) (xs ys : List X) :
    chainDecrease target xs + chainDecrease target ys ≤ chainDecrease target (xs ++ ys) := by
  classical
  induction xs with
  | nil => simp only [List.nil_append, chainDecrease, Nat.zero_add, le_rfl]
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => simp only [List.append_nil, chainDecrease, Nat.zero_add, le_rfl]
      | cons y ys =>
        simp only [List.singleton_append, chainDecrease]
        omega
    | cons y xs =>
      simp only [List.cons_append, chainDecrease] at ih ⊢
      omega

private theorem chainDecrease_destutter'_aux {Y : Type*} [PartialOrder Y] [DecidableLT Y]
    (target : Y → β) (xs : List Y) (x : Y) (hchain : (x :: xs).IsChain (· ≤ ·)) :
    chainDecrease target (xs.destutter' (· < ·) x) = chainDecrease target (x :: xs) ∧
      ∀ p, chainDecrease target (p :: xs.destutter' (· < ·) x) =
        chainDecrease target (p :: x :: xs) := by
  classical
  induction xs generalizing x with
  | nil => exact ⟨rfl, fun _ => rfl⟩
  | cons y ys ih =>
    have hxy := (List.isChain_cons_cons.mp hchain).1
    have htail := (List.isChain_cons_cons.mp hchain).2
    by_cases hlt : x < y
    · have hi := ih y htail
      rw [List.destutter'_cons, ite_eq_left hlt]
      refine ⟨hi.2 x, ?_⟩
      intro p
      change (if target p ≤ target x then 0 else 1) +
        chainDecrease target (x :: ys.destutter' (· < ·) y) =
        (if target p ≤ target x then 0 else 1) + chainDecrease target (x :: y :: ys)
      exact congrArg ((if target p ≤ target x then 0 else 1) + ·) (hi.2 x)
    · have heq : x = y := (lt_or_eq_of_le hxy).resolve_left hlt
      subst y
      have hi := ih x htail
      rw [List.destutter'_cons, ite_eq_right (lt_irrefl x)]
      refine ⟨?_, ?_⟩
      · simpa only [chainDecrease, ite_eq_left (le_refl (target x)), Nat.zero_add] using hi.1
      · intro p
        simpa only [chainDecrease, ite_eq_left (le_refl (target x)), Nat.zero_add] using hi.2 p

/-- Removing repeated inputs from an increasing chain preserves its decrease count. -/
theorem chainDecrease_destutter {Y : Type*} [PartialOrder Y] [DecidableLT Y] (target : Y → β)
    (xs : List Y) (hchain : xs.IsChain (· ≤ ·)) :
    chainDecrease target (xs.destutter (· < ·)) = chainDecrease target xs := by
  classical
  cases xs with
  | nil => rfl
  | cons x xs => exact (chainDecrease_destutter'_aux target xs x hchain).1

private theorem chainDecrease_add_le_of_descentRank
    {sources : X → α} {target : X → β} {rank : X → ℕ}
    (hrank : IsDescentRank sources target rank) {x : X} {xs : List X} {b : ℕ}
    (hchain : (x :: xs).IsChain (fun x y => sources x ≤ sources y))
    (hbound : ∀ z ∈ x :: xs, rank z ≤ b) :
    chainDecrease target (x :: xs) + rank x ≤ b := by
  classical
  induction xs generalizing x with
  | nil =>
    simpa only [chainDecrease, Nat.zero_add] using hbound x (List.mem_cons_self ..)
  | cons y ys ih =>
    have hxy := (List.isChain_cons_cons.mp hchain).1
    have htail := (List.isChain_cons_cons.mp hchain).2
    have hi := ih htail (fun z hz => hbound z (List.mem_cons_of_mem x hz))
    have hm := hrank.monotone hxy
    by_cases htarget : target x ≤ target y
    · simp only [chainDecrease, ite_eq_left htarget, Nat.zero_add]
      omega
    · have hne : rank x ≠ rank y := fun heq => htarget (hrank.preserves_eq hxy heq)
      simp only [chainDecrease, ite_eq_right htarget]
      omega

/-- A bounded descent rank bounds the number of decreases on every increasing source chain. -/
theorem IsDescentRank.chainDecrease_le {sources : X → α} {target : X → β}
    {rank : X → ℕ} (hrank : IsDescentRank sources target rank) {xs : List X} {b : ℕ}
    (hchain : xs.IsChain (fun x y => sources x ≤ sources y))
    (hbound : ∀ z ∈ xs, rank z ≤ b) : chainDecrease target xs ≤ b := by
  cases xs with
  | nil => exact Nat.zero_le _
  | cons x xs =>
    have := chainDecrease_add_le_of_descentRank hrank hchain hbound
    omega

variable {n : ℕ}

private theorem isDescentRank_weight (target : BitString n → β) :
    IsDescentRank id target BitString.weight where
  monotone := BitString.monotone_weight
  preserves_eq := by
    intro x y hxy heq
    have h : x = y := BitString.eq_of_le_of_weight_eq hxy heq
    rw [h]

/-- Maximum chain decrease among increasing chains whose inputs are all at most `x`. -/
noncomputable def decreaseTo (target : BitString n → β) (x : BitString n) : ℕ :=
  sSup {d | ∃ xs : List (BitString n), xs.IsChain (· ≤ ·) ∧
    (∀ y ∈ xs, y ≤ x) ∧ chainDecrease target xs = d}

private theorem decreaseTo_set_nonempty (target : BitString n → β) (x : BitString n) :
    {d | ∃ xs : List (BitString n), xs.IsChain (· ≤ ·) ∧
      (∀ y ∈ xs, y ≤ x) ∧ chainDecrease target xs = d}.Nonempty :=
  ⟨0, [], List.IsChain.nil, by simp only [List.not_mem_nil, false_implies, forall_const], rfl⟩

private theorem decreaseTo_set_bddAbove (target : BitString n → β) (x : BitString n) :
    BddAbove {d | ∃ xs : List (BitString n), xs.IsChain (· ≤ ·) ∧
      (∀ y ∈ xs, y ≤ x) ∧ chainDecrease target xs = d} := by
  refine ⟨BitString.weight x, ?_⟩
  rintro d ⟨xs, hchain, hbelow, rfl⟩
  exact (isDescentRank_weight target).chainDecrease_le hchain
    (fun y hy => BitString.monotone_weight (hbelow y hy))

/-- The maximum decrease below an input is bounded by its Hamming weight. -/
theorem decreaseTo_le_weight (target : BitString n → β) (x : BitString n) :
    decreaseTo target x ≤ BitString.weight x := by
  apply csSup_le (decreaseTo_set_nonempty target x)
  rintro d ⟨xs, hchain, hbelow, rfl⟩
  exact (isDescentRank_weight target).chainDecrease_le hchain
    (fun y hy => BitString.monotone_weight (hbelow y hy))

/-- Enlarging the upper endpoint can only add admissible chains. -/
theorem monotone_decreaseTo (target : BitString n → β) : Monotone (decreaseTo target) := by
  intro x y hxy
  apply csSup_le (decreaseTo_set_nonempty target x)
  rintro d ⟨xs, hchain, hbelow, heq⟩
  exact le_csSup (decreaseTo_set_bddAbove target y)
    ⟨xs, hchain, (fun z hz => (hbelow z hz).trans hxy), heq⟩

/-- Maximal chain decreases form a descent rank. A target drop after `x` would extend a
maximizing chain below `x` by one additional decrease. -/
theorem isDescentRank_decreaseTo (target : BitString n → β) :
    IsDescentRank id target (decreaseTo target) := by
  classical
  refine ⟨monotone_decreaseTo target, ?_⟩
  intro x y hxy heq
  by_contra htarget
  obtain ⟨xs, hchain, hbelow, hcount⟩ := Nat.sSup_mem
    (decreaseTo_set_nonempty target x) (decreaseTo_set_bddAbove target x)
  change chainDecrease target xs = decreaseTo target x at hcount
  have hpair : ([x, y] : List (BitString n)).IsChain (· ≤ ·) := by
    simpa only [List.isChain_cons_cons, List.IsChain.singleton, and_true, id_eq] using hxy
  have hnewchain : (xs ++ [x, y]).IsChain (· ≤ ·) := by
    apply hchain.append hpair
    intro z hz w hw
    have hw' : x = w := by simpa only [List.head?_cons, Option.mem_some_iff] using hw
    exact hw' ▸ hbelow z (List.mem_of_mem_getLast? hz)
  have hnewbelow : ∀ z ∈ xs ++ [x, y], z ≤ y := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact (hbelow z hz).trans hxy
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact hxy
      · exact le_rfl
  have hupper : chainDecrease target (xs ++ [x, y]) ≤ decreaseTo target y :=
    le_csSup (decreaseTo_set_bddAbove target y) ⟨xs ++ [x, y], hnewchain, hnewbelow, rfl⟩
  have hlower := chainDecrease_append_le target xs [x, y]
  simp only [chainDecrease, ite_eq_right htarget, Nat.add_zero, hcount] at hlower
  omega

/-- The decrease of a system is its maximum number of drops along an increasing input chain.
For Boolean vector outputs, a drop means that some coordinate changes from true to false. -/
noncomputable def decrease (target : BitString n → β) : ℕ := decreaseTo target ⊤

/-- Every chain below a fixed input is admissible in the global maximum. -/
theorem decreaseTo_le_decrease (target : BitString n → β) (x : BitString n) :
    decreaseTo target x ≤ decrease target := monotone_decreaseTo target le_top

/-- The maximum in the definition of decrease is attained by an increasing input chain. -/
theorem exists_chain_decrease (target : BitString n → β) :
    ∃ xs : List (BitString n), xs.IsChain (· ≤ ·) ∧ chainDecrease target xs = decrease target := by
  obtain ⟨xs, hchain, _, hcount⟩ := Nat.sSup_mem
    (decreaseTo_set_nonempty target ⊤) (decreaseTo_set_bddAbove target ⊤)
  exact ⟨xs, hchain, hcount⟩

/-- The maximum decrease is already attained on a nonempty strictly increasing chain.
This identifies the list-based definition with Markov's original chain convention. -/
theorem exists_strict_chain_decrease (target : BitString n → β) :
    ∃ xs : List (BitString n), xs ≠ [] ∧ xs.IsChain (· < ·) ∧
      chainDecrease target xs = decrease target := by
  classical
  obtain ⟨xs, hchain, hcount⟩ := exists_chain_decrease target
  by_cases hnil : xs = []
  · refine ⟨[⊥], List.cons_ne_nil _ _, List.IsChain.singleton _, ?_⟩
    simpa only [hnil, chainDecrease] using hcount
  · refine ⟨xs.destutter (· < ·), ?_, List.isChain_destutter _ _, ?_⟩
    · exact mt (List.destutter_eq_nil (· < ·)).mp hnil
    · exact (chainDecrease_destutter target xs hchain).trans hcount

/-- The count on any increasing input chain is bounded by the system's decrease. -/
theorem chainDecrease_le_decrease (target : BitString n → β) {xs : List (BitString n)}
    (hchain : xs.IsChain (· ≤ ·)) : chainDecrease target xs ≤ decrease target :=
  le_csSup (decreaseTo_set_bddAbove target ⊤) ⟨xs, hchain, fun _ _ => le_top, rfl⟩

/-- Any descent rank bounded by `b` bounds the maximum chain decrease by `b`. -/
theorem decrease_le_of_descentRank {target : BitString n → β} {rank : BitString n → ℕ}
    (hrank : IsDescentRank id target rank) {b : ℕ} (hbound : ∀ x, rank x ≤ b) :
    decrease target ≤ b := by
  obtain ⟨xs, hchain, hcount⟩ := exists_chain_decrease target
  rw [← hcount]
  exact hrank.chainDecrease_le hchain (fun x _ => hbound x)

/-- There are at most `n` decreases on an increasing chain of `n`-bit inputs. -/
theorem decrease_le_numInputs (target : BitString n → β) : decrease target ≤ n :=
  (decreaseTo_le_weight target ⊤).trans (BitString.weight_le_length _)

/-- A system has zero decrease exactly when it is monotone. -/
theorem decrease_eq_zero_iff (target : BitString n → β) :
    decrease target = 0 ↔ Monotone target := by
  constructor
  · intro hzero x y hxy
    apply (isDescentRank_decreaseTo target).preserves_eq hxy
    have hx := decreaseTo_le_decrease target x
    have hy := decreaseTo_le_decrease target y
    omega
  · intro hmono
    apply Nat.eq_zero_of_le_zero
    have hconst : IsDescentRank id target (fun _ => 0) :=
      ⟨by intro x y _; exact le_rfl, by intro x y h _; exact hmono h⟩
    exact decrease_le_of_descentRank hconst (fun _ => le_rfl)

end Cslib.Circuits.Boolean
