/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Interval and generalized prefix distribution trees for segment extraction

Internal combinatorial tree structures representing binary interval aggregation trees
(`IntervalTree`) and bounded-fanout segment distribution trees (`GenPrefixTree`) extracted along the
principal chain of a zero-deficiency prefix circuit [Sergeev2025PrefixDepth].

## Main definitions

* `Cslib.Circuits.Prefix.IntervalTree`: binary aggregation tree partitioning `[a, b)` into
  contiguous subintervals.
* `Cslib.Circuits.Prefix.GenPrefixTree`: bounded-fanout distribution tree over interval states with
  output and `mul`-transition counters.

## Main results

* `Cslib.Circuits.Prefix.IntervalTree.width_le_two_pow`,
  `Cslib.Circuits.Prefix.IntervalTree.suffixOfLeftPrefix`: width bound `b - a ≤ 2 ^ depth` and
  right-suffix extraction after erasing a left-anchored interval `(a, s)`.
* `Cslib.Circuits.Prefix.GenPrefixTree.outCount_le_two_pow`: output count bound
  `outCount ≤ 2 ^ depth` at fanout bound `2` when each state occurs as an output at most once.

## References

* [I. S. Sergeev, *A Note on the Depth of Optimal Fanout-Bounded Prefix
  Circuits*][Sergeev2025PrefixDepth]
-/

public section

namespace Cslib.Circuits.Prefix

/-- Binary aggregation tree partitioning `[a, b)` into contiguous subintervals. -/
inductive IntervalTree : ℕ → ℕ → Type
  | leaf (a : ℕ) : IntervalTree a (a + 1)
  | node {a m b : ℕ} (left : IntervalTree a m) (right : IntervalTree m b) : IntervalTree a b

/-- Every `IntervalTree a b` spans a nonempty interval `a < b`. -/
theorem IntervalTree.lt {a b : ℕ} (t : IntervalTree a b) : a < b := by
  induction t with
  | leaf a => exact Nat.lt_succ_self a
  | node _ _ ihL ihR => exact ihL.trans ihR


/-- Depth of a binary interval aggregation tree. -/
@[expose] def IntervalTree.depth : {a b : ℕ} → IntervalTree a b → ℕ
  | _, _, .leaf _ => 0
  | _, _, .node L R => max L.depth R.depth + 1

/-- Set of subintervals `(p, q)` represented by nodes of an `IntervalTree`. -/
@[expose] def IntervalTree.intervals : {a b : ℕ} → IntervalTree a b → Finset (ℕ × ℕ)
  | _, _, .leaf a => {(a, a + 1)}
  | a, b, .node L R => insert (a, b) (L.intervals ∪ R.intervals)

/-- An interval tree over `[a, b)` has span `b - a ≤ 2 ^ t.depth`. -/
theorem IntervalTree.width_le_two_pow {a b : ℕ} (t : IntervalTree a b) :
    b - a ≤ 2 ^ t.depth := by
  induction t with
  | leaf a => simp only [IntervalTree.depth, pow_zero, Nat.add_sub_cancel_left, le_rfl]
  | node L R ihL ihR =>
    have hL := L.lt
    have hR := R.lt
    have hpowL : 2 ^ L.depth ≤ 2 ^ max L.depth R.depth :=
      Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)
    have hpowR : 2 ^ R.depth ≤ 2 ^ max L.depth R.depth :=
      Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)
    simp only [IntervalTree.depth, Nat.pow_succ]
    omega


/-- Every interval `(p, q) ∈ t.intervals` satisfies `a ≤ p < q ≤ b`. -/
theorem IntervalTree.mem_intervals_bounds {a b : ℕ} (t : IntervalTree a b) :
    ∀ {p q : ℕ}, (p, q) ∈ t.intervals → a ≤ p ∧ p < q ∧ q ≤ b := by
  induction t with
  | leaf a =>
    intro p q hpq
    simp only [IntervalTree.intervals, Finset.mem_singleton, Prod.mk.injEq] at hpq
    omega
  | node L R ihL ihR =>
    intro p q hpq
    have hL := L.lt
    have hR := R.lt
    simp only [IntervalTree.intervals, Finset.mem_insert, Finset.mem_union, Prod.mk.injEq] at hpq
    rcases hpq with ⟨rfl, rfl⟩ | hpL | hpR
    · exact ⟨le_rfl, hL.trans hR, le_rfl⟩
    · obtain ⟨h1, h2, h3⟩ := ihL hpL
      exact ⟨h1, h2, by omega⟩
    · obtain ⟨h1, h2, h3⟩ := ihR hpR
      exact ⟨by omega, h2, h3⟩

/-- Every unit interval `(p, p + 1)` inside `[a, b)` belongs to `t.intervals`. -/
theorem IntervalTree.unit_mem_intervals {a b : ℕ} (t : IntervalTree a b) :
    ∀ p, a ≤ p → p < b → (p, p + 1) ∈ t.intervals := by
  induction t with
  | leaf a =>
    intro p hp1 hp2
    have hpeq : p = a := by omega
    rw [hpeq]
    simp only [IntervalTree.intervals, Finset.mem_singleton]
  | @node _ m _ L R ihL ihR =>
    intro p hp1 hp2
    simp only [IntervalTree.intervals, Finset.mem_insert, Finset.mem_union]
    by_cases hpm : p < m
    · exact Or.inr (Or.inl (ihL p hp1 hpm))
    · exact Or.inr (Or.inr (ihR p (by omega) hp2))

/-- Erasing the root interval `(a, b)` of `.node L R` leaves `L.intervals ∪ R.intervals`. -/
theorem IntervalTree.erase_root_eq_union {a m b : ℕ} (L : IntervalTree a m)
    (R : IntervalTree m b) :
    (IntervalTree.node L R).intervals.erase (a, b) = L.intervals ∪ R.intervals := by
  have hL := L.lt
  have hR := R.lt
  have hnot : (a, b) ∉ L.intervals ∪ R.intervals := by
    rw [Finset.mem_union]
    rintro (h1 | h2)
    · have := L.mem_intervals_bounds h1; omega
    · have := R.mem_intervals_bounds h2; omega
  simp only [IntervalTree.intervals, Finset.erase_insert hnot]

/-- Given a proper left prefix `(a, s) ∈ t.intervals.erase (a, b)`, extracts a suffix interval tree
on `[s, b)` of depth at most `t.depth` covering all intervals starting at `≥ s`. -/
theorem IntervalTree.suffixOfLeftPrefix {a b : ℕ} (t : IntervalTree a b) :
    ∀ s, (a, s) ∈ t.intervals.erase (a, b) →
      a < s ∧ s < b ∧
        ∃ J : IntervalTree s b,
          J.depth ≤ t.depth ∧
          ∀ p q, (p, q) ∈ t.intervals.erase (a, b) → s ≤ p → (p, q) ∈ J.intervals := by
  induction t with
  | leaf a =>
    intro s hs
    simp only [IntervalTree.intervals, Finset.erase_singleton, Finset.notMem_empty] at hs
  | @node a m b L R ihL _ =>
    intro s hs
    have hL := L.lt
    have hR := R.lt
    rw [IntervalTree.erase_root_eq_union, Finset.mem_union] at hs
    have hsL : (a, s) ∈ L.intervals :=
      hs.resolve_right fun hsR => by have := R.mem_intervals_bounds hsR; omega
    have hbds := L.mem_intervals_bounds hsL
    by_cases hsm : s = m
    · rw [hsm]
      refine ⟨hL, hR, R, by simp only [IntervalTree.depth]; omega, ?_⟩
      intro p q hpq hmp
      rw [IntervalTree.erase_root_eq_union, Finset.mem_union] at hpq
      rcases hpq with hpL | hpR
      · have := L.mem_intervals_bounds hpL; omega
      · exact hpR
    · have hsL_er : (a, s) ∈ L.intervals.erase (a, m) :=
        Finset.mem_erase.mpr ⟨fun heq => hsm (Prod.mk.inj heq).2, hsL⟩
      obtain ⟨has, _, JL, hJL_d, hJL_sub⟩ := ihL s hsL_er
      refine ⟨has, by omega, .node JL R, ?_, ?_⟩
      · simp only [IntervalTree.depth]
        omega
      · intro p q hpq hsp
        rw [IntervalTree.erase_root_eq_union, Finset.mem_union] at hpq
        simp only [IntervalTree.intervals, Finset.mem_insert, Finset.mem_union]
        rcases hpq with hpL | hpR
        · exact Or.inr (Or.inl (hJL_sub p q (Finset.mem_erase.mpr
            ⟨fun heq => by have := (Prod.mk.inj heq).1; omega, hpL⟩) hsp))
        · exact Or.inr (Or.inr hpR)


/-- Generalized bounded-fanout prefix distribution tree extracted from a DAG segment. -/
inductive GenPrefixTree : Type
  | node (state : ℕ) (hasOut : Bool) (r : ℕ) (isMul : Fin r → Bool)
      (child : Fin r → GenPrefixTree) : GenPrefixTree

/-- Prefix state label at the root of a `GenPrefixTree`. -/
@[expose] def GenPrefixTree.state : GenPrefixTree → ℕ
  | .node s _ _ _ _ => s

/-- Root fanout budget `r + (1 if hasOut else 0)` of a `GenPrefixTree`. -/
@[expose] def GenPrefixTree.rootBudget : GenPrefixTree → ℕ
  | .node _ hasOut r _ _ => r + if hasOut then 1 else 0

/-- Tree height of a `GenPrefixTree`. -/
@[expose] def GenPrefixTree.depth : GenPrefixTree → ℕ
  | .node _ _ r _ child => Finset.univ.sup fun i : Fin r => (child i).depth + 1

/-- Every node in the `GenPrefixTree` uses total fanout budget at most `k`. -/
@[expose] def GenPrefixTree.FanoutAtMost (k : ℕ) : GenPrefixTree → Prop
  | .node _ hasOut r _ child =>
      r + (if hasOut then 1 else 0) ≤ k ∧ ∀ i : Fin r, (child i).FanoutAtMost k

/-- Every node in the `GenPrefixTree` carries state strictly below `b`. -/
@[expose] def GenPrefixTree.MaxStateLt (b : ℕ) : GenPrefixTree → Prop
  | .node s _ r _ child => s < b ∧ ∀ i : Fin r, (child i).MaxStateLt b

/-- Validity of `GenPrefixTree` transitions against an allowed interval set `iv`. -/
@[expose] def GenPrefixTree.Valid (iv : Finset (ℕ × ℕ)) : GenPrefixTree → Prop
  | .node s _ r isMul child =>
      (∀ i : Fin r,
        if isMul i then s < (child i).state ∧ (s, (child i).state) ∈ iv
        else (child i).state = s) ∧
        ∀ i : Fin r, (child i).Valid iv

/-- Total number of output-bearing nodes in a `GenPrefixTree`. -/
@[expose] def GenPrefixTree.outCount : GenPrefixTree → ℕ
  | .node _ hasOut r _ child => (if hasOut then 1 else 0) + ∑ i : Fin r, (child i).outCount

/-- Number of output-bearing nodes at state `s` in a `GenPrefixTree`. -/
@[expose] def GenPrefixTree.outAt (s : ℕ) : GenPrefixTree → ℕ
  | .node st hasOut r _ child =>
      (if hasOut ∧ st = s then 1 else 0) + ∑ i : Fin r, (child i).outAt s

/-- Number of `mul` child transitions landing at state `m` in a `GenPrefixTree`. -/
@[expose] def GenPrefixTree.mulCount (m : ℕ) : GenPrefixTree → ℕ
  | .node _ _ r isMul child =>
      ∑ i : Fin r,
        ((if isMul i ∧ (child i).state = m then 1 else 0) + (child i).mulCount m)

/-- Every child subtree has depth strictly smaller than its parent node. -/
theorem GenPrefixTree.child_depth_lt {st : ℕ} {hasOut : Bool} {r : ℕ}
    {isMul : Fin r → Bool} {child : Fin r → GenPrefixTree} (i : Fin r) :
    (child i).depth + 1 ≤ (GenPrefixTree.node st hasOut r isMul child).depth :=
  Finset.le_sup (f := fun j : Fin r => (child j).depth + 1) (Finset.mem_univ i)

/-- A fanout-`2` `GenPrefixTree` with at most one output per state has `outCount ≤ 2 ^ depth`. -/
theorem GenPrefixTree.outCount_le_two_pow :
    ∀ (t : GenPrefixTree), t.FanoutAtMost 2 → (∀ s, t.outAt s ≤ 1) →
      t.outCount ≤ 2 ^ t.depth
  | .node st hasOut r isMul child, hfan, hout => by
    obtain ⟨hr, hch_fan⟩ := hfan
    have hch_out : ∀ i : Fin r, ∀ s, (child i).outAt s ≤ 1 := by
      intro i s
      have hs := hout s
      simp only [GenPrefixTree.outAt] at hs
      have hle : (child i).outAt s ≤ ∑ j : Fin r, (child j).outAt s :=
        Finset.single_le_sum (f := fun j : Fin r => (child j).outAt s)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    by_cases hr0 : r = 0
    · subst hr0
      simp only [GenPrefixTree.outCount, Finset.univ_eq_empty, Finset.sum_empty]
      have h1 : 1 ≤ 2 ^ (GenPrefixTree.node st hasOut 0 isMul child).depth :=
        Nat.one_le_pow _ _ (by omega)
      cases hasOut <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    · have hr_le2 : r ≤ 2 := by omega
      have hd_pos : 1 ≤ (GenPrefixTree.node st hasOut r isMul child).depth := by
        have := GenPrefixTree.child_depth_lt (child := child) (isMul := isMul)
          (st := st) (hasOut := hasOut) ⟨0, by omega⟩
        omega
      set H := (GenPrefixTree.node st hasOut r isMul child).depth - 1
      have hch_le : ∀ i : Fin r, (child i).outCount ≤ 2 ^ H := by
        intro i
        have h1 := GenPrefixTree.outCount_le_two_pow (child i) (hch_fan i) (hch_out i)
        have h2 := GenPrefixTree.child_depth_lt (st := st) (hasOut := hasOut) (isMul := isMul)
          (child := child) i
        exact h1.trans (Nat.pow_le_pow_right (by omega) (by omega))
      have hsum_le : ∑ i : Fin r, (child i).outCount ≤ r * 2 ^ H :=
        (Finset.sum_le_sum fun i _ => hch_le i).trans_eq (by simp)
      have hpow : 2 ^ (GenPrefixTree.node st hasOut r isMul child).depth = 2 * 2 ^ H := by
        rw [show (GenPrefixTree.node st hasOut r isMul child).depth = H + 1 by omega,
          Nat.pow_succ, Nat.mul_comm]
      have hH_pos : 1 ≤ 2 ^ H := Nat.one_le_pow _ _ (by omega)
      simp only [GenPrefixTree.outCount]
      rcases (show r = 1 ∨ r = 2 by omega) with rfl | rfl <;>
        (cases hasOut <;>
          simp only [Bool.false_eq_true, ↓reduceIte, Nat.one_mul] at hr hsum_le ⊢ <;>
          omega)


end Cslib.Circuits.Prefix
