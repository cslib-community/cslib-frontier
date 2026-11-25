/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Prefix.OptimalDepth.Recurrence
public import CslibFrontier.Computability.Circuit.Prefix.OptimalDepth.Trees
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Subtree splitting and `W_k(r, d, h)` output bound for `GenPrefixTree`

Inductive `mul`-subtree extraction (`extract_mul_subtree`) and output-count upper bound
`(t.outCount : ℝ) ≤ W k r d h` (`GenPrefixTree.outCount_le_W`) for valid bounded-fanout segment
trees when `k ≥ 3` [Sergeev2025PrefixDepth].

## Main results

* `Cslib.Circuits.Prefix.GenPrefixTree.outCount_le_W`: bounds `t.outCount` by `W k r d h` for any
  `GenPrefixTree` valid against an `IntervalTree` of depth at most `d`.

## References

* [I. S. Sergeev, *A Note on the Depth of Optimal Fanout-Bounded Prefix
  Circuits*][Sergeev2025PrefixDepth]
-/

public section

namespace Cslib.Circuits.Prefix

private theorem exists_eq_one_of_sum_eq_one {r : ℕ} {f : Fin r → ℕ}
    (h : ∑ i : Fin r, f i = 1) :
    ∃ i₀ : Fin r, f i₀ = 1 ∧ ∀ j : Fin r, j ≠ i₀ → f j = 0 := by
  have hex : ∃ i₀ : Fin r, f i₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    simp only [hall, Finset.sum_const_zero] at h
    omega
  obtain ⟨i₀, hi₀_ne⟩ := hex
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by have := i₀.isLt; omega⟩
  rw [Fin.sum_univ_succAbove f i₀] at h
  have hi₀_eq : f i₀ = 1 := by omega
  have hrest : ∑ j : Fin r', f (i₀.succAbove j) = 0 := by omega
  rw [Finset.sum_eq_zero_iff] at hrest
  refine ⟨i₀, hi₀_eq, fun j hj => ?_⟩
  obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
  exact hrest j' (Finset.mem_univ j')

private theorem GenPrefixTree.all_state_eq_of_valid_empty :
    ∀ (t : GenPrefixTree), t.Valid ∅ →
      ∀ s, s ≠ t.state → t.outAt s = 0
  | .node st hasOut r isMul child, hval, s, hne => by
    obtain ⟨hedges, hch_val⟩ := hval
    have hch_zero : ∀ i : Fin r, (child i).outAt s = 0 := by
      intro i
      have hi := hedges i
      by_cases hm : isMul i = true
      · simp only [hm, ↓reduceIte, Finset.notMem_empty, and_false] at hi
      · simp only [hm, Bool.false_eq_true, ↓reduceIte] at hi
        exact (child i).all_state_eq_of_valid_empty (hch_val i) s (hi.symm ▸ hne)
    simp only [GenPrefixTree.outAt, GenPrefixTree.state] at hne ⊢
    have h0 : ¬ (hasOut = true ∧ st = s) := fun h => hne h.2.symm
    simp only [h0, ↓reduceIte, hch_zero, Finset.sum_const_zero, Nat.add_zero]

private theorem GenPrefixTree.outCount_eq_outAt_of_valid_empty :
    ∀ (t : GenPrefixTree), t.Valid ∅ → t.outCount = t.outAt t.state
  | .node st hasOut r isMul child, hval => by
    obtain ⟨hedges, hch_val⟩ := hval
    have hch_eq : ∀ i : Fin r, (child i).outCount = (child i).outAt st := by
      intro i
      have hi := hedges i
      by_cases hm : isMul i = true
      · simp only [hm, ↓reduceIte, Finset.notMem_empty, and_false] at hi
      · simp only [hm, Bool.false_eq_true, ↓reduceIte] at hi
        rw [← hi]
        exact (child i).outCount_eq_outAt_of_valid_empty (hch_val i)
    simp only [GenPrefixTree.outCount, GenPrefixTree.outAt, GenPrefixTree.state, and_true]
    rw [Finset.sum_congr rfl fun i _ => hch_eq i]

private theorem child_edge_left {a m b st s' : ℕ} {hmul : Bool}
    (IL : IntervalTree a m) (IR : IntervalTree m b)
    (hst_ge : a ≤ st) (hst_lt : st < m)
    (hed : if hmul = true then st < s' ∧ (st, s') ∈ IL.intervals ∪ IR.intervals else s' = st)
    (hnhit : ¬ (hmul = true ∧ s' = m)) :
    a ≤ s' ∧ s' < m ∧
      (if hmul = true then st < s' ∧ (st, s') ∈ IL.intervals.erase (a, m) else s' = st) := by
  by_cases hm : hmul = true
  · simp only [hm, ↓reduceIte] at hed ⊢
    have hne_m : s' ≠ m := fun heq => hnhit ⟨hm, heq⟩
    rw [Finset.mem_union] at hed
    have hmem_L : (st, s') ∈ IL.intervals := by
      rcases hed.2 with hL | hR
      · exact hL
      · have := IR.mem_intervals_bounds hR; omega
    have hbds := IL.mem_intervals_bounds hmem_L
    refine ⟨by omega, by omega, hed.1, Finset.mem_erase.mpr ⟨?_, hmem_L⟩⟩
    intro heq; rw [Prod.mk.injEq] at heq; exact hne_m heq.2
  · simp only [hm, Bool.false_eq_true, ↓reduceIte] at hed ⊢
    exact ⟨by omega, by omega, hed⟩

private theorem GenPrefixTree.valid_left_of_mulCount_zero {a m b : ℕ}
    (IL : IntervalTree a m) (IR : IntervalTree m b) :
    ∀ (t : GenPrefixTree),
      a ≤ t.state →
      t.state < m →
      t.Valid (IL.intervals ∪ IR.intervals) →
      t.mulCount m = 0 →
      t.MaxStateLt m ∧ t.Valid (IL.intervals.erase (a, m))
  | .node st hasOut r isMul child, hst_ge, hst_lt, hval, hmc0 => by
    simp only [GenPrefixTree.state] at hst_ge hst_lt
    simp only [GenPrefixTree.mulCount, Finset.sum_eq_zero_iff, Finset.mem_univ,
      forall_true_left] at hmc0
    obtain ⟨hedges, hch_val⟩ := hval
    have hch_step : ∀ i : Fin r,
        (if isMul i = true then
          st < (child i).state ∧ (st, (child i).state) ∈ IL.intervals.erase (a, m)
        else (child i).state = st) ∧
        (child i).MaxStateLt m ∧
        (child i).Valid (IL.intervals.erase (a, m)) := by
      intro i
      have hi_mc := hmc0 i
      have hnhit : ¬ (isMul i = true ∧ (child i).state = m) := by
        rintro ⟨h1, h2⟩; simp only [h1, h2, and_self, ↓reduceIte] at hi_mc; omega
      obtain ⟨hs_ge, hs_lt, hed'⟩ := child_edge_left IL IR hst_ge hst_lt (hedges i) hnhit
      have ih := (child i).valid_left_of_mulCount_zero IL IR hs_ge hs_lt (hch_val i)
        (Nat.add_eq_zero_iff.mp hi_mc).2
      exact ⟨hed', ih.1, ih.2⟩
    exact ⟨⟨hst_lt, fun i => (hch_step i).2.1⟩,
      ⟨fun i => (hch_step i).1, fun i => (hch_step i).2.2⟩⟩

private theorem GenPrefixTree.child_valid_left_of_step_zero {a m b st : ℕ} {hmul : Bool}
    (IL : IntervalTree a m) (IR : IntervalTree m b) (c : GenPrefixTree)
    (hst_ge : a ≤ st) (hst_lt : st < m)
    (hed : if hmul = true then st < c.state ∧ (st, c.state) ∈ IL.intervals ∪ IR.intervals
      else c.state = st)
    (hval : c.Valid (IL.intervals ∪ IR.intervals))
    (hstep0 : (if hmul = true ∧ c.state = m then 1 else 0) + c.mulCount m = 0) :
    (if hmul = true then st < c.state ∧ (st, c.state) ∈ IL.intervals.erase (a, m)
      else c.state = st) ∧
    c.MaxStateLt m ∧ c.Valid (IL.intervals.erase (a, m)) := by
  have hnhit : ¬ (hmul = true ∧ c.state = m) := by
    rintro ⟨h1, h2⟩; simp only [h1, h2, and_self, ↓reduceIte] at hstep0; omega
  obtain ⟨hs_ge, hs_lt, hed'⟩ := child_edge_left IL IR hst_ge hst_lt hed hnhit
  have hsub := c.valid_left_of_mulCount_zero IL IR hs_ge hs_lt hval
    (Nat.add_eq_zero_iff.mp hstep0).2
  exact ⟨hed', hsub.1, hsub.2⟩

private theorem GenPrefixTree.valid_right_of_state_ge {a m b : ℕ}
    (IL : IntervalTree a m) (IR : IntervalTree m b) :
    ∀ (t : GenPrefixTree),
      m ≤ t.state →
      t.MaxStateLt b →
      t.Valid (IL.intervals ∪ IR.intervals) →
      t.Valid (IR.intervals.erase (m, b))
  | .node st hasOut r isMul child, hst_ge, hmax, hval => by
    simp only [GenPrefixTree.state] at hst_ge
    obtain ⟨_, hch_max⟩ := hmax
    obtain ⟨hedges, hch_val⟩ := hval
    have hch_st_lt : ∀ i : Fin r, (child i).state < b := by
      intro i
      rcases h : child i with ⟨s', _, _, _, _⟩
      have := hch_max i
      rw [h] at this
      exact this.1
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have hi_ed := hedges i
      by_cases hm : isMul i = true
      · simp only [hm, ↓reduceIte] at hi_ed ⊢
        rw [Finset.mem_union] at hi_ed
        have hmem_R : (st, (child i).state) ∈ IR.intervals := by
          rcases hi_ed.2 with hL | hR
          · have := IL.mem_intervals_bounds hL; omega
          · exact hR
        have hlt_b := hch_st_lt i
        refine ⟨hi_ed.1, Finset.mem_erase.mpr ⟨?_, hmem_R⟩⟩
        intro heq; rw [Prod.mk.injEq] at heq; omega
      · simp only [hm, Bool.false_eq_true, ↓reduceIte] at hi_ed ⊢
        exact hi_ed
    · have hi_ed := hedges i
      have hge_i : m ≤ (child i).state := by
        by_cases hm : isMul i = true
        · simp only [hm, ↓reduceIte] at hi_ed; omega
        · simp only [hm, Bool.false_eq_true, ↓reduceIte] at hi_ed; omega
      exact (child i).valid_right_of_state_ge IL IR hge_i (hch_max i) (hch_val i)

private theorem GenPrefixTree.extract_mul_subtree {k a m b : ℕ}
    (IL : IntervalTree a m) (IR : IntervalTree m b) :
    ∀ (t : GenPrefixTree),
      a ≤ t.state →
      t.state < m →
      t.MaxStateLt b →
      t.FanoutAtMost k →
      t.Valid (IL.intervals ∪ IR.intervals) →
      t.mulCount m = 1 →
      (∃ Q₁ Q₂ : GenPrefixTree,
        Q₁.state = t.state ∧
        Q₁.rootBudget + 1 = t.rootBudget ∧
        Q₁.depth ≤ t.depth ∧
        Q₁.FanoutAtMost k ∧
        Q₁.MaxStateLt m ∧
        Q₁.Valid (IL.intervals.erase (a, m)) ∧
        (∀ x, Q₁.outAt x ≤ t.outAt x) ∧
        (∀ x, Q₁.mulCount x ≤ t.mulCount x) ∧
        Q₂.state = m ∧
        Q₂.depth + 1 ≤ t.depth ∧
        Q₂.FanoutAtMost k ∧
        Q₂.MaxStateLt b ∧
        Q₂.Valid (IR.intervals.erase (m, b)) ∧
        (∀ x, Q₂.outAt x ≤ t.outAt x) ∧
        (∀ x, Q₂.mulCount x ≤ t.mulCount x) ∧
        t.outCount = Q₁.outCount + Q₂.outCount) ∨
      (∃ Q₁ Q₂ : GenPrefixTree,
        Q₁.state = t.state ∧
        Q₁.rootBudget ≤ t.rootBudget ∧
        Q₁.depth ≤ t.depth ∧
        Q₁.FanoutAtMost k ∧
        Q₁.MaxStateLt m ∧
        Q₁.Valid (IL.intervals.erase (a, m)) ∧
        (∀ x, Q₁.outAt x ≤ t.outAt x) ∧
        (∀ x, Q₁.mulCount x ≤ t.mulCount x) ∧
        Q₂.state = m ∧
        Q₂.depth + 2 ≤ t.depth ∧
        Q₂.FanoutAtMost k ∧
        Q₂.MaxStateLt b ∧
        Q₂.Valid (IR.intervals.erase (m, b)) ∧
        (∀ x, Q₂.outAt x ≤ t.outAt x) ∧
        (∀ x, Q₂.mulCount x ≤ t.mulCount x) ∧
        t.outCount = Q₁.outCount + Q₂.outCount)
  | .node _ _ 0 _ _, _, _, _, _, _, hmc1 => by
    simp only [GenPrefixTree.mulCount, Finset.univ_eq_empty, Finset.sum_empty] at hmc1
    omega
  | .node st hasOut (r' + 1) isMul child, hst_ge, hst_lt, hmax, hfan, hval, hmc1 => by
    simp only [GenPrefixTree.state] at hst_ge hst_lt
    obtain ⟨hst_b, hch_max⟩ := hmax
    obtain ⟨hr_bud, hch_fan⟩ := hfan
    obtain ⟨hedges, hch_val⟩ := hval
    simp only [GenPrefixTree.mulCount] at hmc1
    obtain ⟨i₀, hi₀_one, hother_zero⟩ := exists_eq_one_of_sum_eq_one hmc1
    have hother_left (j : Fin (r' + 1)) (hj : j ≠ i₀) :=
      (child j).child_valid_left_of_step_zero IL IR hst_ge hst_lt (hedges j) (hch_val j)
        (hother_zero j hj)
    by_cases hhit : isMul i₀ = true ∧ (child i₀).state = m
    · left
      let Q₁ := GenPrefixTree.node st hasOut r' (isMul ∘ i₀.succAbove) (child ∘ i₀.succAbove)
      let Q₂ := child i₀
      refine ⟨Q₁, Q₂, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hhit.2,
        GenPrefixTree.child_depth_lt i₀, hch_fan i₀, hch_max i₀,
        (child i₀).valid_right_of_state_ge IL IR hhit.2.ge (hch_max i₀) (hch_val i₀),
        ?_, ?_, ?_⟩
      · simp only [Q₁, GenPrefixTree.rootBudget]; omega
      · simp only [Q₁, GenPrefixTree.depth]
        refine Finset.sup_le fun j _ => ?_
        exact GenPrefixTree.child_depth_lt (st := st) (hasOut := hasOut)
          (isMul := isMul) (child := child) (i₀.succAbove j)
      · exact ⟨by omega, fun j => hch_fan (i₀.succAbove j)⟩
      · exact ⟨hst_lt, fun j => (hother_left _ (Fin.succAbove_ne i₀ j)).2.1⟩
      · exact ⟨fun j => (hother_left _ (Fin.succAbove_ne i₀ j)).1,
          fun j => (hother_left _ (Fin.succAbove_ne i₀ j)).2.2⟩
      · intro x
        simp only [Q₁, GenPrefixTree.outAt, Function.comp_apply]
        rw [Fin.sum_univ_succAbove (fun i => (child i).outAt x) i₀]
        omega
      · intro x
        simp only [Q₁, GenPrefixTree.mulCount, Function.comp_apply]
        rw [Fin.sum_univ_succAbove
          (fun i => (if isMul i = true ∧ (child i).state = x then 1 else 0) +
            (child i).mulCount x) i₀]
        omega
      · intro x
        simp only [Q₂, GenPrefixTree.outAt]
        rw [Fin.sum_univ_succAbove (fun i => (child i).outAt x) i₀]
        omega
      · intro x
        simp only [Q₂, GenPrefixTree.mulCount]
        rw [Fin.sum_univ_succAbove
          (fun i => (if isMul i = true ∧ (child i).state = x then 1 else 0) +
            (child i).mulCount x) i₀]
        omega
      · simp only [Q₁, Q₂, GenPrefixTree.outCount, Function.comp_apply]
        rw [Fin.sum_univ_succAbove (fun i => (child i).outCount) i₀]
        omega
    · right
      have hi₀_mc1 : (child i₀).mulCount m = 1 := by
        simp only [hhit, ↓reduceIte, Nat.zero_add] at hi₀_one
        exact hi₀_one
      have hi₀_bounds := child_edge_left IL IR hst_ge hst_lt (hedges i₀) hhit
      have hcommon : ∀ (Q₁_s Q₂ : GenPrefixTree),
          Q₁_s.state = (child i₀).state →
          Q₁_s.depth ≤ (child i₀).depth →
          Q₁_s.FanoutAtMost k →
          Q₁_s.MaxStateLt m →
          Q₁_s.Valid (IL.intervals.erase (a, m)) →
          (∀ x, Q₁_s.outAt x ≤ (child i₀).outAt x) →
          (∀ x, Q₁_s.mulCount x ≤ (child i₀).mulCount x) →
          Q₂.state = m →
          Q₂.depth + 1 ≤ (child i₀).depth →
          Q₂.FanoutAtMost k →
          Q₂.MaxStateLt b →
          Q₂.Valid (IR.intervals.erase (m, b)) →
          (∀ x, Q₂.outAt x ≤ (child i₀).outAt x) →
          (∀ x, Q₂.mulCount x ≤ (child i₀).mulCount x) →
          (child i₀).outCount = Q₁_s.outCount + Q₂.outCount →
          ∃ Q₁ Q₂' : GenPrefixTree,
            Q₁.state = st ∧
            Q₁.rootBudget ≤ (GenPrefixTree.node st hasOut (r' + 1) isMul child).rootBudget ∧
            Q₁.depth ≤ (GenPrefixTree.node st hasOut (r' + 1) isMul child).depth ∧
            Q₁.FanoutAtMost k ∧
            Q₁.MaxStateLt m ∧
            Q₁.Valid (IL.intervals.erase (a, m)) ∧
            (∀ x, Q₁.outAt x ≤ (GenPrefixTree.node st hasOut (r' + 1) isMul child).outAt x) ∧
            (∀ x, Q₁.mulCount x ≤
              (GenPrefixTree.node st hasOut (r' + 1) isMul child).mulCount x) ∧
            Q₂'.state = m ∧
            Q₂'.depth + 2 ≤ (GenPrefixTree.node st hasOut (r' + 1) isMul child).depth ∧
            Q₂'.FanoutAtMost k ∧
            Q₂'.MaxStateLt b ∧
            Q₂'.Valid (IR.intervals.erase (m, b)) ∧
            (∀ x, Q₂'.outAt x ≤ (GenPrefixTree.node st hasOut (r' + 1) isMul child).outAt x) ∧
            (∀ x, Q₂'.mulCount x ≤
              (GenPrefixTree.node st hasOut (r' + 1) isMul child).mulCount x) ∧
            (GenPrefixTree.node st hasOut (r' + 1) isMul child).outCount =
              Q₁.outCount + Q₂'.outCount := by
        intro Q₁_s Q₂ hQ1_st hQ1_d hQ1_fan hQ1_max hQ1_val hQ1_oa hQ1_mc
          hQ2_st hQ2_d hQ2_fan hQ2_max hQ2_val hQ2_oa hQ2_mc hcnt_eq
        let ch' := Function.update child i₀ Q₁_s
        let Q₁ := GenPrefixTree.node st hasOut (r' + 1) isMul ch'
        have hc0_d : (child i₀).depth + 1 ≤
            (GenPrefixTree.node st hasOut (r' + 1) isMul child).depth :=
          GenPrefixTree.child_depth_lt i₀
        refine ⟨Q₁, Q₂, rfl, le_rfl, ?_, ⟨hr_bud, ?_⟩, ⟨hst_lt, ?_⟩, ⟨?_, ?_⟩, ?_, ?_,
          hQ2_st, by omega, hQ2_fan, hQ2_max, hQ2_val, ?_, ?_, ?_⟩
        · simp only [Q₁, GenPrefixTree.depth]
          refine Finset.sup_le fun j _ => ?_
          dsimp only [ch']
          by_cases hj : j = i₀
          · rw [hj, Function.update_self]
            exact (Nat.add_le_add_right hQ1_d 1).trans
              (Finset.le_sup (f := fun i => (child i).depth + 1) (Finset.mem_univ i₀))
          · rw [Function.update_of_ne hj]
            exact Finset.le_sup (f := fun i => (child i).depth + 1) (Finset.mem_univ j)
        · intro j; dsimp only [ch']
          by_cases hj : j = i₀
          · rw [hj, Function.update_self]; exact hQ1_fan
          · rw [Function.update_of_ne hj]; exact hch_fan j
        · intro j; dsimp only [ch']
          by_cases hj : j = i₀
          · rw [hj, Function.update_self]; exact hQ1_max
          · rw [Function.update_of_ne hj]; exact (hother_left j hj).2.1
        · intro j; dsimp only [ch']
          by_cases hj : j = i₀
          · rw [hj, Function.update_self, hQ1_st]; exact hi₀_bounds.2.2
          · rw [Function.update_of_ne hj]; exact (hother_left j hj).1
        · intro j; dsimp only [ch']
          by_cases hj : j = i₀
          · rw [hj, Function.update_self]; exact hQ1_val
          · rw [Function.update_of_ne hj]; exact (hother_left j hj).2.2
        · intro x
          simp only [Q₁, GenPrefixTree.outAt]
          refine Nat.add_le_add_left (Finset.sum_le_sum fun j _ => ?_) _
          dsimp only [ch']
          by_cases hj : j = i₀
          · rw [hj, Function.update_self]; exact hQ1_oa x
          · rw [Function.update_of_ne hj]
        · intro x
          simp only [Q₁, GenPrefixTree.mulCount]
          refine Finset.sum_le_sum fun j _ => ?_
          by_cases hj : j = i₀
          · simp only [ch', hj, Function.update_self, hQ1_st]
            exact Nat.add_le_add_left (hQ1_mc x) _
          · simp only [ch', Function.update_of_ne hj, le_rfl]
        · intro x
          simp only [GenPrefixTree.outAt]
          rw [Fin.sum_univ_succAbove (fun i => (child i).outAt x) i₀]
          have := hQ2_oa x
          omega
        · intro x
          simp only [GenPrefixTree.mulCount]
          rw [Fin.sum_univ_succAbove
            (fun i => (if isMul i = true ∧ (child i).state = x then 1 else 0) +
              (child i).mulCount x) i₀]
          have := hQ2_mc x
          omega
        · simp only [Q₁, GenPrefixTree.outCount, ch']
          rw [Fin.sum_univ_succAbove (fun i => (child i).outCount) i₀,
            Fin.sum_univ_succAbove (fun i => (Function.update child i₀ Q₁_s i).outCount) i₀,
            Function.update_self]
          have hrest_eq : (∑ j : Fin r',
              (Function.update child i₀ Q₁_s (i₀.succAbove j)).outCount) =
              ∑ j : Fin r', (child (i₀.succAbove j)).outCount :=
            Finset.sum_congr rfl fun j _ => by
              rw [Function.update_of_ne (Fin.succAbove_ne i₀ j)]
          rw [hrest_eq, hcnt_eq]
          omega
      rcases (child i₀).extract_mul_subtree IL IR hi₀_bounds.1 hi₀_bounds.2.1
          (hch_max i₀) (hch_fan i₀) (hch_val i₀) hi₀_mc1 with
        ⟨Q₁_s, Q₂, h1, _, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ |
        ⟨Q₁_s, Q₂, h1, _, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩
      · exact hcommon Q₁_s Q₂ h1 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
      · exact hcommon Q₁_s Q₂ h1 h3 h4 h5 h6 h7 h8 h9 (by omega) h11 h12 h13 h14 h15 h16

private theorem GenPrefixTree.valid_suffix {a c b : ℕ} {S T : Finset (ℕ × ℕ)}
    (hsub : ∀ x y, (x, y) ∈ S → c ≤ x → (x, y) ∈ T) :
    ∀ (u : GenPrefixTree),
      c ≤ u.state →
      u.MaxStateLt b →
      u.Valid S →
      u.Valid (T.erase (c, b))
  | .node su ho ru imu chu, hge_u, hmax_u, hval_u => by
    change c ≤ su at hge_u
    obtain ⟨_, hch_mu⟩ := hmax_u
    obtain ⟨hed_u, hcv_u⟩ := hval_u
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have hi := hed_u i
      by_cases hmi : imu i = true
      · simp only [hmi, ↓reduceIte] at hi ⊢
        have hlt_b : (chu i).state < b := by
          rcases hcu : chu i with ⟨_, _, _, _, _⟩
          have := hch_mu i
          rw [hcu] at this
          exact this.1
        refine ⟨hi.1, Finset.mem_erase.mpr ⟨?_, hsub _ _ hi.2 hge_u⟩⟩
        intro heq; rw [Prod.mk.injEq] at heq; omega
      · simp only [hmi, Bool.false_eq_true, ↓reduceIte] at hi ⊢
        exact hi
    · have hi := hed_u i
      have hge_i : c ≤ (chu i).state := by
        by_cases hmi : imu i = true
        · simp only [hmi, ↓reduceIte] at hi; omega
        · simp only [hmi, Bool.false_eq_true, ↓reduceIte] at hi; omega
      exact (chu i).valid_suffix (a := a) hsub hge_i (hch_mu i) (hcv_u i)

/-- Any `GenPrefixTree` valid against `I.intervals.erase (a, b)` with root budget `≤ r ≤ k`,
fanout `≤ k`, at most one output per state, and at most one `mul` transition per target state
satisfies `(t.outCount : ℝ) ≤ W k r d h` when `I.depth ≤ d` and `t.depth ≤ h`. -/
theorem GenPrefixTree.outCount_le_W {k : ℕ} (hk : 3 ≤ k) :
    ∀ (d h r a b : ℕ) (I : IntervalTree a b) (t : GenPrefixTree),
      r ≤ k →
      I.depth ≤ d →
      t.depth ≤ h →
      t.state = a →
      t.MaxStateLt b →
      t.rootBudget ≤ r →
      t.FanoutAtMost k →
      t.Valid (I.intervals.erase (a, b)) →
      (∀ s, t.outAt s ≤ 1) →
      (∀ m, t.mulCount m ≤ 1) →
      (t.outCount : ℝ) ≤ W k r d h := by
  have haux : ∀ n, ∀ (d h r a b : ℕ) (I : IntervalTree a b) (t : GenPrefixTree),
      d + h = n →
      r ≤ k →
      I.depth ≤ d →
      t.depth ≤ h →
      t.state = a →
      t.MaxStateLt b →
      t.rootBudget ≤ r →
      t.FanoutAtMost k →
      t.Valid (I.intervals.erase (a, b)) →
      (∀ s, t.outAt s ≤ 1) →
      (∀ m, t.mulCount m ≤ 1) →
      (t.outCount : ℝ) ≤ W k r d h := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro d h r a b I t hdh hrk hd_le hh_le hst hmax hbud hfan hval hout_at hmul_cnt
      cases h with
      | zero =>
        rcases t with ⟨st, hasOut, r_ch, isMul, child⟩
        by_cases hr0 : r_ch = 0
        · subst hr0
          simp only [GenPrefixTree.outCount, Finset.univ_eq_empty, Finset.sum_empty, Nat.add_zero]
          have h1 : (1 : ℝ) ≤ W k r d 0 := by unfold W; exact one_le_pow₀ (by norm_num)
          cases hasOut <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_one, Nat.cast_zero]
          · positivity
          · exact h1
        · have hc0 := GenPrefixTree.child_depth_lt (st := st) (hasOut := hasOut)
            (isMul := isMul) (child := child) ⟨0, by omega⟩
          omega
      | succ h' =>
        by_cases hr0 : r = 0
        · subst hr0
          rcases t with ⟨st, hasOut, r_ch, isMul, child⟩
          simp only [GenPrefixTree.rootBudget] at hbud
          have hr_ch0 : r_ch = 0 := by omega
          have hno : hasOut = false := by
            cases hasOut
            · rfl
            · simp only [↓reduceIte] at hbud; omega
          subst hr_ch0 hno
          simp only [GenPrefixTree.outCount, Bool.false_eq_true, ↓reduceIte, Finset.univ_eq_empty,
            Finset.sum_empty, Nat.add_zero, Nat.cast_zero, W, le_rfl]
        · by_cases hr1 : r = 1
          · subst hr1
            have hw_eq : W k 1 d (h' + 1) = W k k d h' := by
              rw [W_eq_V (by omega)]
              rfl
            rw [hw_eq]
            rcases t with ⟨st, hasOut, r_ch, isMul, child⟩
            simp only [GenPrefixTree.rootBudget] at hbud
            simp only [GenPrefixTree.state] at hst
            by_cases hr_ch0 : r_ch = 0
            · subst hr_ch0
              simp only [GenPrefixTree.outCount, Finset.univ_eq_empty, Finset.sum_empty,
                Nat.add_zero]
              have h1 := W_one_le (k := k) (by omega : 1 ≤ k) d h'
              cases hasOut <;>
                simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_zero, Nat.cast_one]
              · linarith
              · exact h1
            · have hr_ch1 : r_ch = 1 := by omega
              have hno : hasOut = false := by
                cases hasOut
                · rfl
                · simp only [↓reduceIte] at hbud; omega
              subst hr_ch1 hno
              simp only [GenPrefixTree.outCount, Bool.false_eq_true, ↓reduceIte, Nat.zero_add,
                Fin.sum_univ_one]
              have hc0_d : (child 0).depth ≤ h' := by
                have := GenPrefixTree.child_depth_lt (st := st) (hasOut := false)
                  (isMul := isMul) (child := child) 0
                omega
              obtain ⟨_, hch_max⟩ := hmax
              obtain ⟨_, hch_fan⟩ := hfan
              obtain ⟨hedges, hch_val⟩ := hval
              have hc0_bud : (child 0).rootBudget ≤ k := by
                rcases h : child 0 with ⟨_, _, _, _, _⟩
                have hf0 := hch_fan 0
                rw [h] at hf0
                exact hf0.1
              have hc0_oa : ∀ s, (child 0).outAt s ≤ 1 := by
                intro s
                have hs := hout_at s
                simp only [GenPrefixTree.outAt, Bool.false_eq_true, false_and, ↓reduceIte,
                  Nat.zero_add, Fin.sum_univ_one] at hs
                exact hs
              have hc0_mc : ∀ m, (child 0).mulCount m ≤ 1 := by
                intro m
                have hm := hmul_cnt m
                simp only [GenPrefixTree.mulCount, Fin.sum_univ_one] at hm
                omega
              have hed0 := hedges 0
              by_cases hm0 : isMul 0 = true
              · simp only [hm0, ↓reduceIte, hst] at hed0
                obtain ⟨_, _, J, hJd, hJsub⟩ := I.suffixOfLeftPrefix (child 0).state hed0.2
                have hc0_val_J : (child 0).Valid (J.intervals.erase ((child 0).state, b)) :=
                  (child 0).valid_suffix (a := a) hJsub le_rfl (hch_max 0) (hch_val 0)
                exact ih (d + h') (by omega) d h' k (child 0).state b J (child 0) rfl le_rfl
                  (hJd.trans hd_le) hc0_d rfl (hch_max 0) hc0_bud (hch_fan 0) hc0_val_J
                  hc0_oa hc0_mc
              · simp only [hm0, Bool.false_eq_true, ↓reduceIte, hst] at hed0
                exact ih (d + h') (by omega) d h' k a b I (child 0) rfl le_rfl hd_le hc0_d
                  hed0 (hch_max 0) hc0_bud (hch_fan 0) (hch_val 0) hc0_oa hc0_mc
          · have hr2 : 2 ≤ r := by omega
            cases I with
            | leaf a =>
              have hval_emp : t.Valid ∅ := by
                simpa only [IntervalTree.intervals, Finset.erase_singleton] using hval
              have heq_oa := t.outCount_eq_outAt_of_valid_empty hval_emp
              have hle1 : t.outCount ≤ 1 := heq_oa ▸ hout_at t.state
              have h1 := W_one_le (k := k) (by omega : 1 ≤ r) d (h' + 1)
              have hcast : (t.outCount : ℝ) ≤ 1 := by exact_mod_cast hle1
              exact hcast.trans h1
            | @node a m b IL IR =>
              have hIL := IL.lt
              have hIR := IR.lt
              simp only [IntervalTree.depth] at hd_le
              obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
              have hdL : IL.depth ≤ d' := by omega
              have hdR : IR.depth ≤ d' := by omega
              rw [IntervalTree.erase_root_eq_union] at hval
              have hmc_m := hmul_cnt m
              by_cases hmc0 : t.mulCount m = 0
              · obtain ⟨hmax_L, hval_L⟩ := t.valid_left_of_mulCount_zero IL IR
                  (by omega) (by omega) hval hmc0
                have hsub := ih (d' + (h' + 1)) (by omega) d' (h' + 1) r a m IL t rfl hrk
                  hdL hh_le hst hmax_L hbud hfan hval_L hout_at hmul_cnt
                exact hsub.trans (W_mono_left k r d' (h' + 1))
              · have hmc1 : t.mulCount m = 1 := by omega
                rcases t.extract_mul_subtree IL IR (by omega) (by omega) hmax hfan hval hmc1 with
                  ⟨Q₁, Q₂, hQ1_st, hQ1_bud, hQ1_d, hQ1_fan, hQ1_max, hQ1_val, hQ1_oa, hQ1_mc,
                    hQ2_st, hQ2_d, hQ2_fan, hQ2_max, hQ2_val, hQ2_oa, hQ2_mc, hcnt_eq⟩ |
                  ⟨Q₁, Q₂, hQ1_st, hQ1_bud, hQ1_d, hQ1_fan, hQ1_max, hQ1_val, hQ1_oa, hQ1_mc,
                    hQ2_st, hQ2_d, hQ2_fan, hQ2_max, hQ2_val, hQ2_oa, hQ2_mc, hcnt_eq⟩
                · have hQ2_bud : Q₂.rootBudget ≤ k := by
                    rcases hq : Q₂ with ⟨_, _, _, _, _⟩
                    have hf := hQ2_fan
                    rw [hq] at hf
                    exact hf.1
                  have hb1 := ih (d' + (h' + 1)) (by omega) d' (h' + 1) (r - 1) a m IL Q₁ rfl
                    (by omega) hdL (hQ1_d.trans hh_le) (hQ1_st.trans hst) hQ1_max (by omega)
                    hQ1_fan hQ1_val (fun s => (hQ1_oa s).trans (hout_at s))
                    (fun x => (hQ1_mc x).trans (hmul_cnt x))
                  have hb2 := ih (d' + h') (by omega) d' h' k m b IR Q₂ rfl le_rfl hdR
                    (by omega) hQ2_st hQ2_max hQ2_bud hQ2_fan hQ2_val
                    (fun s => (hQ2_oa s).trans (hout_at s))
                    (fun x => (hQ2_mc x).trans (hmul_cnt x))
                  rw [W_eq_V (by omega)] at hb2
                  have hsp := W_split_depth_one (k := k) (d := d') (h := h') hr2
                  rw [hcnt_eq, Nat.cast_add]
                  linarith
                · obtain ⟨h'', rfl⟩ : ∃ h'', h' = h'' + 1 := ⟨h' - 1, by omega⟩
                  have hQ2_bud : Q₂.rootBudget ≤ k := by
                    rcases hq : Q₂ with ⟨_, _, _, _, _⟩
                    have hf := hQ2_fan
                    rw [hq] at hf
                    exact hf.1
                  have hb1 := ih (d' + (h'' + 2)) (by omega) d' (h'' + 2) r a m IL Q₁ rfl hrk
                    hdL (hQ1_d.trans hh_le) (hQ1_st.trans hst) hQ1_max (hQ1_bud.trans hbud)
                    hQ1_fan hQ1_val (fun s => (hQ1_oa s).trans (hout_at s))
                    (fun x => (hQ1_mc x).trans (hmul_cnt x))
                  have hb2 := ih (d' + h'') (by omega) d' h'' k m b IR Q₂ rfl le_rfl hdR
                    (by omega) hQ2_st hQ2_max hQ2_bud hQ2_fan hQ2_val
                    (fun s => (hQ2_oa s).trans (hout_at s))
                    (fun x => (hQ2_mc x).trans (hmul_cnt x))
                  rw [W_eq_V (by omega)] at hb2
                  have hsp := W_split_depth_two (d := d') (h := h'') hk hr2 hrk
                  rw [hcnt_eq, Nat.cast_add]
                  linarith
  intro d h r a b I t
  exact haux (d + h) d h r a b I t rfl


end Cslib.Circuits.Prefix
