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
  obtain ⟨i₀, -, hi₀_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by omega : ∑ i : Fin r, f i ≠ 0)
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by have := i₀.isLt; omega⟩
  rw [Fin.sum_univ_succAbove f i₀] at h
  have hrest := Finset.sum_eq_zero_iff.mp (by omega : ∑ j : Fin r', f (i₀.succAbove j) = 0)
  refine ⟨i₀, by omega, fun j hj => ?_⟩
  obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
  exact hrest j' (Finset.mem_univ j')

/-- An edge of a tree valid against `∅` keeps the state. -/
private theorem state_eq_of_edge_empty {b : Bool} {st s : ℕ}
    (h : if b = true then st < s ∧ (st, s) ∈ (∅ : Finset (ℕ × ℕ)) else s = st) : s = st := by
  split_ifs at h
  exacts [absurd h.2 (Finset.notMem_empty _), h]

private theorem GenPrefixTree.all_state_eq_of_valid_empty :
    ∀ (t : GenPrefixTree), t.Valid ∅ →
      ∀ s, s ≠ t.state → t.outAt s = 0
  | .node st hasOut r isMul child, ⟨hedges, hch_val⟩, s, hne => by
    have hch_zero (i : Fin r) : (child i).outAt s = 0 :=
      (child i).all_state_eq_of_valid_empty (hch_val i) s
        ((state_eq_of_edge_empty (hedges i)).symm ▸ hne)
    simp only [GenPrefixTree.outAt, GenPrefixTree.state] at hne ⊢
    have h0 : ¬ (hasOut = true ∧ st = s) := fun h => hne h.2.symm
    simp only [h0, ↓reduceIte, hch_zero, Finset.sum_const_zero, Nat.add_zero]

private theorem GenPrefixTree.outCount_eq_outAt_of_valid_empty :
    ∀ (t : GenPrefixTree), t.Valid ∅ → t.outCount = t.outAt t.state
  | .node st hasOut r isMul child, ⟨hedges, hch_val⟩ => by
    have hch_eq (i : Fin r) : (child i).outCount = (child i).outAt st := by
      rw [← state_eq_of_edge_empty (hedges i)]
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
    have hmem_L : (st, s') ∈ IL.intervals :=
      (Finset.mem_union.mp hed.2).resolve_right fun hR => by
        have := IR.mem_intervals_bounds hR
        omega
    have hbds := IL.mem_intervals_bounds hmem_L
    exact ⟨by omega, by omega, hed.1,
      Finset.mem_erase.mpr ⟨fun heq => hne_m (Prod.mk.inj heq).2, hmem_L⟩⟩
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

private theorem GenPrefixTree.valid_suffix {c b : ℕ} {S T : Finset (ℕ × ℕ)}
    (hsub : ∀ x y, (x, y) ∈ S → c ≤ x → (x, y) ∈ T) :
    ∀ (u : GenPrefixTree),
      c ≤ u.state →
      u.MaxStateLt b →
      u.Valid S →
      u.Valid (T.erase (c, b))
  | .node su ho ru imu chu, hge_u, ⟨_, hch_mu⟩, ⟨hed_u, hcv_u⟩ => by
    change c ≤ su at hge_u
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have hi := hed_u i
      split_ifs at hi ⊢
      · have hlt_b : (chu i).state < b :=
          match chu i, hch_mu i with | .node _ _ _ _ _, h => h.1
        refine ⟨hi.1, Finset.mem_erase.mpr ⟨fun heq => ?_, hsub _ _ hi.2 hge_u⟩⟩
        rw [Prod.mk.injEq] at heq; omega
      · exact hi
    · have hi := hed_u i
      have hge_i : c ≤ (chu i).state := by split_ifs at hi <;> omega
      exact (chu i).valid_suffix hsub hge_i (hch_mu i) (hcv_u i)

private theorem GenPrefixTree.extract_mul_subtree {k a m b : ℕ}
    (IL : IntervalTree a m) (IR : IntervalTree m b) :
    ∀ (t : GenPrefixTree),
      a ≤ t.state →
      t.state < m →
      t.MaxStateLt b →
      t.FanoutAtMost k →
      t.Valid (IL.intervals ∪ IR.intervals) →
      t.mulCount m = 1 →
      ∃ Q₁ Q₂ : GenPrefixTree,
        ((Q₁.rootBudget + 1 = t.rootBudget ∧ Q₂.depth + 1 ≤ t.depth) ∨
          (Q₁.rootBudget ≤ t.rootBudget ∧ Q₂.depth + 2 ≤ t.depth)) ∧
        Q₁.state = t.state ∧
        Q₁.depth ≤ t.depth ∧
        Q₁.FanoutAtMost k ∧
        Q₁.MaxStateLt m ∧
        Q₁.Valid (IL.intervals.erase (a, m)) ∧
        (∀ x, Q₁.outAt x ≤ t.outAt x) ∧
        (∀ x, Q₁.mulCount x ≤ t.mulCount x) ∧
        Q₂.state = m ∧
        Q₂.FanoutAtMost k ∧
        Q₂.MaxStateLt b ∧
        Q₂.Valid (IR.intervals.erase (m, b)) ∧
        (∀ x, Q₂.outAt x ≤ t.outAt x) ∧
        (∀ x, Q₂.mulCount x ≤ t.mulCount x) ∧
        t.outCount = Q₁.outCount + Q₂.outCount
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
    have hc0_d : (child i₀).depth + 1 ≤
        (GenPrefixTree.node st hasOut (r' + 1) isMul child).depth :=
      GenPrefixTree.child_depth_lt i₀
    by_cases hhit : isMul i₀ = true ∧ (child i₀).state = m
    · -- The `mul` edge into `m` leaves the root: split off the child `i₀`.
      refine ⟨.node st hasOut r' (isMul ∘ i₀.succAbove) (child ∘ i₀.succAbove), child i₀,
        Or.inl ⟨?_, hc0_d⟩, rfl,
        Finset.sup_le fun j _ => GenPrefixTree.child_depth_lt (i₀.succAbove j),
        ⟨by omega, fun j => hch_fan (i₀.succAbove j)⟩,
        ⟨hst_lt, fun j => (hother_left _ (Fin.succAbove_ne i₀ j)).2.1⟩,
        ⟨fun j => (hother_left _ (Fin.succAbove_ne i₀ j)).1,
          fun j => (hother_left _ (Fin.succAbove_ne i₀ j)).2.2⟩, ?_, ?_, hhit.2,
        hch_fan i₀, hch_max i₀,
        (child i₀).valid_suffix (fun x y hxy hx => (Finset.mem_union.mp hxy).resolve_left
          fun hL => by have := IL.mem_intervals_bounds hL; omega) hhit.2.ge (hch_max i₀)
          (hch_val i₀),
        ?_, ?_, ?_⟩
      · simp only [GenPrefixTree.rootBudget]; omega
      all_goals
        intros
        simp only [GenPrefixTree.outAt, GenPrefixTree.mulCount, GenPrefixTree.outCount,
          Function.comp_apply, Fin.sum_univ_succAbove _ i₀]
        omega
    · -- The edge lies deeper: split `child i₀` recursively and replace it by its left part.
      have hi₀_mc1 : (child i₀).mulCount m = 1 := by
        simpa only [hhit, ↓reduceIte, Nat.zero_add] using hi₀_one
      have hi₀_bounds := child_edge_left IL IR hst_ge hst_lt (hedges i₀) hhit
      obtain ⟨Q₁, Q₂, hsplit, hQ1_st, hQ1_d, hQ1_fan, hQ1_max, hQ1_val, hQ1_oa, hQ1_mc,
        hQ2_st, hQ2_fan, hQ2_max, hQ2_val, hQ2_oa, hQ2_mc, hcnt_eq⟩ :=
        (child i₀).extract_mul_subtree IL IR hi₀_bounds.1 hi₀_bounds.2.1
          (hch_max i₀) (hch_fan i₀) (hch_val i₀) hi₀_mc1
      have hQ2_d : Q₂.depth + 1 ≤ (child i₀).depth :=
        hsplit.elim And.right (fun h => (Nat.le_succ _).trans h.2)
      let ch' := Function.update child i₀ Q₁
      have hch' (P : Fin (r' + 1) → GenPrefixTree → Prop) (h₀ : P i₀ Q₁)
          (h₁ : ∀ j ≠ i₀, P j (child j)) (j : Fin (r' + 1)) : P j (ch' j) :=
        (Function.forall_update_iff child P).2 ⟨h₀, h₁⟩ j
      refine ⟨.node st hasOut (r' + 1) isMul ch', Q₂,
        Or.inr ⟨le_rfl, (Nat.add_le_add_right hQ2_d 1).trans hc0_d⟩, rfl,
        Finset.sup_le fun j _ => hch' (fun j t => t.depth + 1 ≤
          (GenPrefixTree.node st hasOut (r' + 1) isMul child).depth)
          ((Nat.add_le_add_right hQ1_d 1).trans hc0_d)
          (fun j _ => GenPrefixTree.child_depth_lt j) j,
        ⟨hr_bud, hch' (fun _ t => t.FanoutAtMost k) hQ1_fan fun j _ => hch_fan j⟩,
        ⟨hst_lt, hch' (fun _ t => t.MaxStateLt m) hQ1_max fun j hj => (hother_left j hj).2.1⟩,
        ⟨hch' (fun j t => if isMul j = true then
            st < t.state ∧ (st, t.state) ∈ IL.intervals.erase (a, m) else t.state = st)
          (by rw [hQ1_st]; exact hi₀_bounds.2.2) fun j hj => (hother_left j hj).1,
        hch' (fun _ t => t.Valid (IL.intervals.erase (a, m))) hQ1_val
          fun j hj => (hother_left j hj).2.2⟩,
        fun x => Nat.add_le_add_left (Finset.sum_le_sum fun j _ =>
          hch' (fun j t => t.outAt x ≤ (child j).outAt x) (hQ1_oa x) (fun _ _ => le_rfl) j) _,
        fun x => Finset.sum_le_sum fun j _ => hch' (fun j t =>
          (if isMul j = true ∧ t.state = x then 1 else 0) + t.mulCount x ≤
            (if isMul j = true ∧ (child j).state = x then 1 else 0) + (child j).mulCount x)
          (by rw [hQ1_st]; exact Nat.add_le_add_left (hQ1_mc x) _)
          (fun _ _ => le_rfl) j,
        hQ2_st, hQ2_fan, hQ2_max, hQ2_val, fun x => ?_, fun x => ?_, ?_⟩
      · have := hQ2_oa x
        simp only [GenPrefixTree.outAt, Fin.sum_univ_succAbove _ i₀]
        omega
      · have := hQ2_mc x
        simp only [GenPrefixTree.mulCount, Fin.sum_univ_succAbove _ i₀]
        omega
      · simp only [GenPrefixTree.outCount, Fin.sum_univ_succAbove _ i₀, ch',
          Function.update_self, Function.update_of_ne (Fin.succAbove_ne i₀ _)]
        omega

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
  intro d h
  induction hn : d + h using Nat.strong_induction_on generalizing d h with
  | _ n ih =>
    intro r a b I t hrk hd_le hh_le hst hmax hbud hfan hval hout_at hmul_cnt
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
        obtain rfl : r_ch = 0 := by simp only [GenPrefixTree.rootBudget] at hbud; omega
        cases hasOut
        · simp only [GenPrefixTree.outCount, Bool.false_eq_true, ↓reduceIte, Finset.univ_eq_empty,
            Finset.sum_empty, Nat.add_zero, Nat.cast_zero, W, le_rfl]
        · simp [GenPrefixTree.rootBudget] at hbud
      by_cases hr1 : r = 1
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
          refine le_trans ?_ (W_one_le (k := k) (by omega : 1 ≤ k) d h')
          simp only [GenPrefixTree.outCount, Finset.univ_eq_empty, Finset.sum_empty, Nat.add_zero]
          split <;> norm_num
        obtain rfl : r_ch = 1 := by omega
        obtain rfl : hasOut = false := by revert hbud; cases hasOut <;> simp
        simp only [GenPrefixTree.outCount, Bool.false_eq_true, ↓reduceIte, Nat.zero_add,
          Fin.sum_univ_one]
        have hc0_d : (child 0).depth ≤ h' := by
          have := GenPrefixTree.child_depth_lt (st := st) (hasOut := false)
            (isMul := isMul) (child := child) 0
          omega
        obtain ⟨_, hch_max⟩ := hmax
        obtain ⟨_, hch_fan⟩ := hfan
        obtain ⟨hedges, hch_val⟩ := hval
        have hc0_bud : (child 0).rootBudget ≤ k :=
          match child 0, hch_fan 0 with | .node _ _ _ _ _, h => h.1
        have hc0_oa (s : ℕ) : (child 0).outAt s ≤ 1 := by
          simpa only [GenPrefixTree.outAt, Bool.false_eq_true, false_and, ↓reduceIte,
            Nat.zero_add, Fin.sum_univ_one] using hout_at s
        have hc0_mc (m : ℕ) : (child 0).mulCount m ≤ 1 := by
          have hm := hmul_cnt m
          simp only [GenPrefixTree.mulCount, Fin.sum_univ_one] at hm
          omega
        have hed0 := hedges 0
        by_cases hm0 : isMul 0 = true
        · simp only [hm0, ↓reduceIte, hst] at hed0
          obtain ⟨_, _, J, hJd, hJsub⟩ := I.suffixOfLeftPrefix (child 0).state hed0.2
          exact ih (d + h') (by omega) d h' rfl k (child 0).state b J (child 0) le_rfl
            (hJd.trans hd_le) hc0_d rfl (hch_max 0) hc0_bud (hch_fan 0)
            ((child 0).valid_suffix hJsub le_rfl (hch_max 0) (hch_val 0)) hc0_oa hc0_mc
        · simp only [hm0, Bool.false_eq_true, ↓reduceIte, hst] at hed0
          exact ih (d + h') (by omega) d h' rfl k a b I (child 0) le_rfl hd_le hc0_d
            hed0 (hch_max 0) hc0_bud (hch_fan 0) (hch_val 0) hc0_oa hc0_mc
      have hr2 : 2 ≤ r := by omega
      cases I with
      | leaf a =>
        have hval_emp : t.Valid ∅ := by
          simpa only [IntervalTree.intervals, Finset.erase_singleton] using hval
        have hle1 : t.outCount ≤ 1 :=
          t.outCount_eq_outAt_of_valid_empty hval_emp ▸ hout_at t.state
        exact (Nat.cast_le_one.mpr hle1).trans (W_one_le (k := k) (by omega : 1 ≤ r) d (h' + 1))
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
          exact (ih (d' + (h' + 1)) (by omega) d' (h' + 1) rfl r a m IL t hrk
            hdL hh_le hst hmax_L hbud hfan hval_L hout_at hmul_cnt).trans
            (W_mono_left k r d' (h' + 1))
        obtain ⟨Q₁, Q₂, hsplit, hQ1_st, hQ1_d, hQ1_fan, hQ1_max, hQ1_val, hQ1_oa, hQ1_mc,
          hQ2_st, hQ2_fan, hQ2_max, hQ2_val, hQ2_oa, hQ2_mc, hcnt_eq⟩ :=
          t.extract_mul_subtree IL IR hst.symm.le (hst ▸ hIL) hmax hfan hval
            (hmc_m.antisymm (Nat.pos_of_ne_zero hmc0))
        have hQ2_bud : Q₂.rootBudget ≤ k :=
          match Q₂, hQ2_fan with | .node _ _ _ _ _, h => h.1
        rw [hcnt_eq, Nat.cast_add]
        rcases hsplit with ⟨hQ1_bud, hQ2_d⟩ | ⟨hQ1_bud, hQ2_d⟩
        · have hb1 := ih (d' + (h' + 1)) (by omega) d' (h' + 1) rfl (r - 1) a m IL Q₁
            (by omega) hdL (hQ1_d.trans hh_le) (hQ1_st.trans hst) hQ1_max (by omega)
            hQ1_fan hQ1_val (fun s => (hQ1_oa s).trans (hout_at s))
            (fun x => (hQ1_mc x).trans (hmul_cnt x))
          have hb2 := ih (d' + h') (by omega) d' h' rfl k m b IR Q₂ le_rfl hdR
            (by omega) hQ2_st hQ2_max hQ2_bud hQ2_fan hQ2_val
            (fun s => (hQ2_oa s).trans (hout_at s))
            (fun x => (hQ2_mc x).trans (hmul_cnt x))
          rw [W_eq_V (by lia)] at hb2
          exact (add_le_add hb1 hb2).trans_eq (W_split_depth_one hr2)
        · obtain ⟨h'', rfl⟩ : ∃ h'', h' = h'' + 1 := ⟨h' - 1, by omega⟩
          have hb1 := ih (d' + (h'' + 2)) (by omega) d' (h'' + 2) rfl r a m IL Q₁ hrk
            hdL (hQ1_d.trans hh_le) (hQ1_st.trans hst) hQ1_max (hQ1_bud.trans hbud)
            hQ1_fan hQ1_val (fun s => (hQ1_oa s).trans (hout_at s))
            (fun x => (hQ1_mc x).trans (hmul_cnt x))
          have hb2 := ih (d' + h'') (by omega) d' h'' rfl k m b IR Q₂ le_rfl hdR
            (by omega) hQ2_st hQ2_max hQ2_bud hQ2_fan hQ2_val
            (fun s => (hQ2_oa s).trans (hout_at s))
            (fun x => (hQ2_mc x).trans (hmul_cnt x))
          rw [W_eq_V (by lia)] at hb2
          exact (add_le_add hb1 hb2).trans (W_split_depth_two hk hr2 hrk)

end Cslib.Circuits.Prefix
