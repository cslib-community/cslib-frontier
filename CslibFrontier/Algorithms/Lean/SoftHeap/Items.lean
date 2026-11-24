/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

-- upstream: candidate
public import CslibFrontier.Algorithms.Lean.SoftHeap.Forest

/-!
# Conservation of soft-heap items

Moving and pooling buckets preserves each item with its multiplicity. A successful extraction
removes exactly the returned label. These identities hold even for arbitrary input trees.
-/

public section

namespace Cslib.SoftHeap

variable {α W : Type} [LinearOrder W] {r : ℕ}

/-- Multiset of live occurrences in an optional bucket. -/
@[expose] def contents : Option (Bucket α) → Multiset α
  | none => 0
  | some b => {b.rep} + b.pending

theorem contents_pool (w : α → W) (a b : Bucket α) :
    contents (some (Bucket.pool w a b)) = contents (some a) + contents (some b) := by
  unfold Bucket.pool
  split <;> simp only [contents, ← Multiset.cons_coe, ← Multiset.singleton_add,
    ← Multiset.coe_add] <;> ac_rfl

namespace Tree

/-- All live occurrences under this root, including the root's pending list. -/
@[expose] def items : {r : ℕ} → Tree α r → Multiset α
  | _, .leaf b => contents b
  | _, .node b cs => contents b + ∑ i, (cs i).items

private theorem pull_items (w : α → W) (next : Tree α r → Tree α r)
    (good : ∀ tr, contents tr.root + (next tr).items = tr.items) (cs : Fin 4 → Tree α r) :
    contents (pull w next cs).1 + ∑ i, ((pull w next cs).2 i).items = ∑ i, (cs i).items := by
  unfold pull
  cases h : leastChild w cs with
  | none => simp [contents]
  | some p =>
    obtain ⟨j, b⟩ := p
    change contents (some b) + ∑ i, (Function.update cs j (next (cs j)) i).items = _
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
      ← Finset.add_sum_erase _ (fun i => (cs i).items) (Finset.mem_univ j)]
    simp only [Function.update_self, ← add_assoc]
    rw [← root_of_leastChild h, good]
    congr 1
    exact Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

theorem refill_items (w : α → W) (t : ℕ) (soft : Bool) (tr : Tree α r) :
    contents tr.root + (refill w t soft tr).items = tr.items := by
  induction r with
  | zero => cases tr; simp [refill, root, items, contents]
  | succ r ih =>
    cases tr with
    | node old cs =>
      let next := refill w t soft (r := r)
      generalize ha : pull w next cs = first
      obtain ⟨a, cs'⟩ := first
      have one := pull_items w next ih cs
      rw [ha] at one
      simp only [refill, show refill w t soft (r := r) = next from rfl, ha, root]
      split
      · cases a with
        | none => exact congrArg (contents old + ·) one
        | some a =>
          generalize hb : pull w next cs' = second
          obtain ⟨b, cs''⟩ := second
          have two := pull_items w next ih cs'
          rw [hb] at two
          change contents old + _ = contents old + _
          congr 1
          cases b with
          | none =>
            have eq : (∑ i, (cs'' i).items) = ∑ i, (cs' i).items := by
              simpa [contents] using two
            change contents (some a) + _ = _
            simpa only [← eq] using one
          | some b =>
            change contents (some (Bucket.pool w a b)) + _ = _
            rw [contents_pool, add_assoc]
            exact ((congrArg (contents (some a) + ·) two).trans one)
      · exact congrArg (contents old + ·) one

theorem link_items (w : α → W) (t : ℕ) (cs : Fin 4 → Tree α r) :
    (link w t cs).items = ∑ i, (cs i).items := by
  simpa [link, root, items, contents] using refill_items w t false (.node none cs)

theorem extract_items {w : α → W} {t : ℕ} {tr tr' : Tree α r} {x a : α}
    (hit : extract w t tr = some ((x, a), tr')) : {x} + tr'.items = tr.items := by
  unfold extract at hit
  split at hit
  · contradiction
  · next b e =>
    cases hit
    simpa only [e, contents, Multiset.coe_nil, add_zero] using refill_items w t true tr
  · next b y ys e =>
    cases hit
    cases tr with
    | leaf old =>
      change old = _ at e
      rw [e]
      simp only [setRoot, items, contents, ← Multiset.cons_coe, ← Multiset.singleton_add]
      ac_rfl
    | node old cs =>
      change old = _ at e
      rw [e]
      simp only [setRoot, items, contents, ← Multiset.cons_coe, ← Multiset.singleton_add]
      ac_rfl

end Tree

namespace Forest

/-- The multiset of live edge labels stored across all roots. -/
@[expose] def items (h : Forest α) : Multiset α := (h.map fun f => f.2.items).sum

theorem carry_items (w : α → W) (t : ℕ) (tr : Tree α r) (h : Forest α) :
    (carry w t tr h).items = tr.items + h.items := by
  induction r, tr, h using carry.induct w t with
  | case1 r C rest B A tr ih =>
    rw [carry]
    simp only [dite_true, ih, Tree.link_items, Fin.sum_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
    simp [items, add_assoc]
  | case2 | case3 | case4 | case5 =>
    rw [carry]
    all_goals first | assumption | simp_all [items]

theorem insert_items (w : α → W) (t : ℕ) (x : α) (h : Forest α) :
    (insert w t x h).items = {x} + h.items := by
  simpa [insert, Tree.singleton, Tree.items, contents, Bucket.singleton] using
    carry_items w t (Tree.singleton x) h

private theorem items_set (h : Forest α) (i : Fin h.length) (tr : Tree α (h.get i).1) (x : α)
    (eq : {x} + tr.items = (h.get i).2.items) :
    {x} + items (h.set i ⟨(h.get i).1, tr⟩) = h.items := by
  induction h with
  | nil => exact Fin.elim0 i
  | cons f fs ih =>
    induction i using Fin.cases with
    | zero =>
      change {x} + tr.items = f.2.items at eq
      simpa [items, ← add_assoc] using congrArg (· + items fs) eq
    | succ j =>
      have step := ih j tr eq
      simpa [items, add_assoc, add_left_comm, add_comm] using congrArg (f.2.items + ·) step

theorem extract_items {w : α → W} {t : ℕ} {h h' : Forest α} {x a : α}
    (hit : extract w t h = some ((x, a), h')) : {x} + h'.items = h.items := by
  unfold extract at hit
  cases found : leastRoot w h with
  | none => simp [found] at hit
  | some p =>
    obtain ⟨i, b⟩ := p
    cases ran : Tree.extract w t (h.get i).2 with
    | none => simp only [found, Option.bind_some, Option.bind_eq_bind, ran, Option.bind_none,
        Option.pure_def, reduceCtorEq] at hit
    | some result =>
      obtain ⟨⟨y, k⟩, tr⟩ := result
      simp only [found, Option.bind_some, Option.bind_eq_bind, ran, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at hit
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hit
      exact items_set h i tr _ (Tree.extract_items ran)

end Forest
end Cslib.SoftHeap
