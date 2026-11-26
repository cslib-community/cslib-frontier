/-
Copyright (c) 2026 Paulo Matos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paulo Matos
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Rope.Basic
public import CslibFrontier.Foundations.Data.Nat.Fib

/-!
# Ropes: local balance and the height bound

`Rope.balanceNode l r` joins two well-formed ropes whose heights differ by at most two into one
well-formed rope, using a single or a double rotation when one side is two levels taller. It is
the constructor that join uses on its way back up the spine, following the AVL join of
[Blelloch, Ferizovic and Sun][BlellochFerizovicSun2016], Figure 2. The result represents
`l.toList ++ r.toList`, and its height is between `max l.height r.height` and one more.

A well-formed rope of height `h` has at least `Nat.fib (h + 2)` leaves, since its sibling heights
differ by at most one and its internal nodes have non-empty children. Each leaf holds at least one
element, so the height is at most `2 * Nat.log 2 (length + 1)`.

## Main definitions

* `Rope.balanceNode`: a node over `l` and `r` that rotates when their heights differ by two.
* `Rope.balanceL`, `Rope.balanceR`: the rotations for a left or right child that is two levels
  taller.

## Main results

* `Rope.toList_balanceNode`, `Rope.isWF_balanceNode`, `Rope.height_balanceNode`: the list model,
  well-formedness and the height effect of `balanceNode`.
* `Rope.leaves_le_length`: a chunked rope has at most as many leaves as elements.
* `Rope.fib_height_le_leaves`, `Rope.fib_height_le_leaves_add_one`: the Fibonacci lower bound on
  the number of leaves, for non-empty and for all well-formed ropes.
* `Rope.height_le_two_mul_log`: a well-formed rope has height at most
  `2 * Nat.log 2 (length + 1)`.

## References

* [G. E. Blelloch, D. Ferizovic and Y. Sun, *Just Join for Parallel Ordered
  Sets*][BlellochFerizovicSun2016]
-/

public section

universe u

namespace Cslib.DataStructure.Rope

variable {α : Type u}

/-! ### Rotations -/

/-- A node over `l` and `r` when `l` is two levels taller than `r`. A single right rotation is
used when the outer grandchild `ll` is at least as tall as the inner one `lr`, and otherwise a
double rotation through `lr`. -/
@[expose] def balanceL (l r : Rope α) : Rope α :=
  match l with
  | .node _ _ ll lr@(.node _ _ lrl lrr) =>
    if lr.height ≤ ll.height then mkNode ll (mkNode lr r)
    else mkNode (mkNode ll lrl) (mkNode lrr r)
  | .node _ _ ll lr => mkNode ll (mkNode lr r)
  | l => mkNode l r

/-- A node over `l` and `r` when `r` is two levels taller than `l`: the mirror image of
`balanceL`. -/
@[expose] def balanceR (l r : Rope α) : Rope α :=
  match r with
  | .node _ _ rl@(.node _ _ rll rlr) rr =>
    if rl.height ≤ rr.height then mkNode (mkNode l rl) rr
    else mkNode (mkNode l rll) (mkNode rlr rr)
  | .node _ _ rl rr => mkNode (mkNode l rl) rr
  | r => mkNode l r

/-- A node over `l` and `r` that restores balance when their cached heights differ by two, and
drops an empty side. It reads only cached heights of the children and grandchildren. -/
@[expose] def balanceNode : Rope α → Rope α → Rope α
  | .empty, r => r
  | l, .empty => l
  | l, r =>
    if r.height + 1 < l.height then balanceL l r
    else if l.height + 1 < r.height then balanceR l r
    else mkNode l r

@[simp] theorem balanceNode_empty_left (r : Rope α) : balanceNode .empty r = r := rfl

@[simp] theorem balanceNode_empty_right (l : Rope α) : balanceNode l .empty = l := by
  cases l <;> rfl

private theorem balanceNode_of_isEmpty_eq_false {l r : Rope α} (hl : l.isEmpty = false)
    (hr : r.isEmpty = false) :
    balanceNode l r = if r.height + 1 < l.height then balanceL l r
      else if l.height + 1 < r.height then balanceR l r else mkNode l r := by
  cases l <;> cases r <;> simp_all [balanceNode]

/-! ### The list model -/

private theorem toList_balanceL (l r : Rope α) : (balanceL l r).toList = l.toList ++ r.toList := by
  unfold balanceL
  split <;> (try split) <;> simp

private theorem toList_balanceR (l r : Rope α) : (balanceR l r).toList = l.toList ++ r.toList := by
  unfold balanceR
  split <;> (try split) <;> simp

/-- `balanceNode` represents the concatenation of its arguments, with no hypotheses. -/
@[simp] theorem toList_balanceNode (l r : Rope α) :
    (balanceNode l r).toList = l.toList ++ r.toList := by
  unfold balanceNode
  split
  · simp
  · simp
  · split
    · exact toList_balanceL _ _
    · split
      · exact toList_balanceR _ _
      · simp

/-! ### Well-formedness and the height effect -/

variable {B : ℕ}

/-- `mkNode` over two non-empty well-formed children whose heights differ by at most one. -/
private theorem mkNode_spec {l r : Rope α} (hl : IsWF B l) (hr : IsWF B r)
    (hl0 : l.isEmpty = false) (hr0 : r.isEmpty = false)
    (h₁ : l.height ≤ r.height + 1) (h₂ : r.height ≤ l.height + 1) :
    IsWF B (mkNode l r) ∧ (mkNode l r).isEmpty = false ∧
      (mkNode l r).height = max l.height r.height + 1 :=
  ⟨isWF_mkNode hl hr h₁ h₂, by simp [hl0], height_mkNode hl0 hr0⟩

private theorem balanceL_spec {l r : Rope α} (hl : IsWF B l) (hr : IsWF B r)
    (hr0 : r.isEmpty = false) (hh : l.height = r.height + 2) :
    IsWF B (balanceL l r) ∧ l.height ≤ (balanceL l r).height ∧
      (balanceL l r).height ≤ l.height + 1 := by
  rcases l with _ | _ | ⟨n, h, ll, lr⟩
  · simp at hh
  · simp at hh
  obtain ⟨hll, hlr, hll0, hlr0, -, rfl, h₁, h₂⟩ := isWF_node_iff.1 hl
  simp only [height_node] at hh ⊢
  have single (hs : lr.height ≤ ll.height) : IsWF B (mkNode ll (mkNode lr r)) ∧
      max ll.height lr.height + 1 ≤ (mkNode ll (mkNode lr r)).height ∧
      (mkNode ll (mkNode lr r)).height ≤ max ll.height lr.height + 1 + 1 := by
    obtain ⟨wb, eb, hgb⟩ := mkNode_spec hlr hr hlr0 hr0 (by omega) (by omega)
    obtain ⟨w, -, hg⟩ := mkNode_spec hll wb hll0 eb (by omega) (by omega)
    exact ⟨w, by omega, by omega⟩
  rcases lr with _ | _ | ⟨m, k, lrl, lrr⟩
  · simp at hlr0
  · exact single (Nat.zero_le _)
  obtain ⟨hlrl, hlrr, hlrl0, hlrr0, -, rfl, h₃, h₄⟩ := isWF_node_iff.1 hlr
  simp only [balanceL]
  split
  · exact single ‹_›
  · simp only [height_node] at *
    obtain ⟨wa, ea, hga⟩ := mkNode_spec hll hlrl hll0 hlrl0 (by omega) (by omega)
    obtain ⟨wb, eb, hgb⟩ := mkNode_spec hlrr hr hlrr0 hr0 (by omega) (by omega)
    obtain ⟨w, -, hg⟩ := mkNode_spec wa wb ea eb (by omega) (by omega)
    exact ⟨w, by omega, by omega⟩

private theorem balanceR_spec {l r : Rope α} (hl : IsWF B l) (hr : IsWF B r)
    (hl0 : l.isEmpty = false) (hh : r.height = l.height + 2) :
    IsWF B (balanceR l r) ∧ r.height ≤ (balanceR l r).height ∧
      (balanceR l r).height ≤ r.height + 1 := by
  rcases r with _ | _ | ⟨n, h, rl, rr⟩
  · simp at hh
  · simp at hh
  obtain ⟨hrl, hrr, hrl0, hrr0, -, rfl, h₁, h₂⟩ := isWF_node_iff.1 hr
  simp only [height_node] at hh ⊢
  have single (hs : rl.height ≤ rr.height) : IsWF B (mkNode (mkNode l rl) rr) ∧
      max rl.height rr.height + 1 ≤ (mkNode (mkNode l rl) rr).height ∧
      (mkNode (mkNode l rl) rr).height ≤ max rl.height rr.height + 1 + 1 := by
    obtain ⟨wa, ea, hga⟩ := mkNode_spec hl hrl hl0 hrl0 (by omega) (by omega)
    obtain ⟨w, -, hg⟩ := mkNode_spec wa hrr ea hrr0 (by omega) (by omega)
    exact ⟨w, by omega, by omega⟩
  rcases rl with _ | _ | ⟨m, k, rll, rlr⟩
  · simp at hrl0
  · exact single (Nat.zero_le _)
  obtain ⟨hrll, hrlr, hrll0, hrlr0, -, rfl, h₃, h₄⟩ := isWF_node_iff.1 hrl
  simp only [balanceR]
  split
  · exact single ‹_›
  · simp only [height_node] at *
    obtain ⟨wa, ea, hga⟩ := mkNode_spec hl hrll hl0 hrll0 (by omega) (by omega)
    obtain ⟨wb, eb, hgb⟩ := mkNode_spec hrlr hrr hrlr0 hrr0 (by omega) (by omega)
    obtain ⟨w, -, hg⟩ := mkNode_spec wa wb ea eb (by omega) (by omega)
    exact ⟨w, by omega, by omega⟩

private theorem balanceNode_spec {l r : Rope α} (hl : IsWF B l) (hr : IsWF B r)
    (h₁ : l.height ≤ r.height + 2) (h₂ : r.height ≤ l.height + 2) :
    IsWF B (balanceNode l r) ∧ max l.height r.height ≤ (balanceNode l r).height ∧
      (balanceNode l r).height ≤ max l.height r.height + 1 := by
  cases hl0 : l.isEmpty
  · cases hr0 : r.isEmpty
    · rw [balanceNode_of_isEmpty_eq_false hl0 hr0]
      split
      · have := balanceL_spec hl hr hr0 (by omega)
        exact ⟨this.1, by omega, by omega⟩
      · split
        · have := balanceR_spec hl hr hl0 (by omega)
          exact ⟨this.1, by omega, by omega⟩
        · obtain ⟨w, -, hg⟩ := mkNode_spec hl hr hl0 hr0 (by omega) (by omega)
          exact ⟨w, by omega, by omega⟩
    · obtain rfl := isEmpty_iff.1 hr0
      simpa using hl
  · obtain rfl := isEmpty_iff.1 hl0
    simpa using hr

/-- `balanceNode` over well-formed ropes whose heights differ by at most two is well-formed. -/
theorem isWF_balanceNode {l r : Rope α} (hl : IsWF B l) (hr : IsWF B r)
    (h₁ : l.height ≤ r.height + 2) (h₂ : r.height ≤ l.height + 2) :
    IsWF B (balanceNode l r) :=
  (balanceNode_spec hl hr h₁ h₂).1

/-- The height of `balanceNode` is between `max l.height r.height` and one more. When one side is
`empty`, the result is the other side, so the lower bound is an equality. -/
theorem height_balanceNode {l r : Rope α} (hl : IsWF B l) (hr : IsWF B r)
    (h₁ : l.height ≤ r.height + 2) (h₂ : r.height ≤ l.height + 2) :
    max l.height r.height ≤ (balanceNode l r).height ∧
      (balanceNode l r).height ≤ max l.height r.height + 1 :=
  (balanceNode_spec hl hr h₁ h₂).2

/-! ### The height bound -/

/-- A chunked rope has at most as many leaves as elements. -/
theorem leaves_le_length {t : Rope α} (hc : CacheCorrect t) (hk : Chunked B t) :
    t.leaves ≤ t.length := by
  induction t with
  | empty => simp [leaves]
  | leaf xs => exact hk.1
  | node n h l r ihl ihr =>
    have := ihl hc.1 hk.1
    have := ihr hc.2.1 hk.2.1
    simp only [leaves, length_node, hc.2.2.1]
    omega

/-- A non-empty well-formed rope of height `h` has at least `Nat.fib (h + 2)` leaves. -/
theorem fib_height_le_leaves {t : Rope α} (hw : IsWF B t) (hne : t.isEmpty = false) :
    Nat.fib (t.height + 2) ≤ t.leaves := by
  induction t with
  | empty => simp at hne
  | leaf xs => simp [leaves]
  | node n h l r ihl ihr =>
    obtain ⟨hl, hr, hl0, hr0, -, rfl, h₁, h₂⟩ := isWF_node_iff.1 hw
    have := Nat.fib_max_add_three_le h₁ h₂
    have := ihl hl hl0
    have := ihr hr hr0
    change Nat.fib (max l.height r.height + 3) ≤ l.leaves + r.leaves
    omega

/-- A well-formed rope of height `h` has at least `Nat.fib (h + 2) - 1` leaves; unlike
`fib_height_le_leaves`, this also covers `empty`. -/
theorem fib_height_le_leaves_add_one {t : Rope α} (hw : IsWF B t) :
    Nat.fib (t.height + 2) ≤ t.leaves + 1 := by
  cases h : t.isEmpty
  · exact (fib_height_le_leaves hw h).trans (Nat.le_succ _)
  · obtain rfl := isEmpty_iff.1 h
    simp [leaves]

/-- A well-formed rope has height at most `2 * Nat.log 2 (length + 1)`. -/
theorem height_le_two_mul_log {t : Rope α} (hw : IsWF B t) :
    t.height ≤ 2 * Nat.log 2 (t.length + 1) :=
  Nat.le_two_mul_log_of_fib_le ((fib_height_le_leaves_add_one hw).trans
    (Nat.add_le_add_right (leaves_le_length hw.cacheCorrect hw.chunked) 1))

end Cslib.DataStructure.Rope
