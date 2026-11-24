/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

-- upstream: candidate
public import CslibFrontier.Algorithms.Lean.SoftHeap.Ordering
public import CslibFrontier.Algorithms.Lean.SoftHeap.Items
import Mathlib.Tactic.FinCases

/-!
# Per-item key accounting

An external key function is covered by a soft heap if it gives each stored item a lower bound
on its current representative key. A successful extraction supplies a new common lower bound
for all remaining items. Thus cut minima can be recorded as floors without maintaining a
pointer to every bucket.
-/

public section

namespace Cslib.SoftHeap

variable {α W : Type} [LinearOrder W] {r : ℕ}

/-- Every occupant's recorded key lies below its representative key. -/
@[expose] def CoversSlot (w k : α → W) (s : Option (Bucket α)) : Prop :=
  ∀ b, s = some b → ∀ x ∈ contents (some b), k x ≤ w b.rep

private theorem empty_covers (w k : α → W) : CoversSlot w k none := by simp [CoversSlot]

private theorem pool_covers (w k : α → W) {a b : Bucket α}
    (ha : CoversSlot w k (some a)) (hb : CoversSlot w k (some b)) :
    CoversSlot w k (some (Bucket.pool w a b)) := by
  rintro _ ⟨⟩ x hx
  rw [contents_pool, Multiset.mem_add] at hx
  rcases hx with h | h
  · have le := ha _ rfl x h
    unfold Bucket.pool
    split
    · next eq => exact le.trans eq
    · exact le
  · have le := hb _ rfl x h
    unfold Bucket.pool
    split
    · exact le
    · next eq => exact le.trans (le_of_not_ge eq)

namespace Tree

/-- All the buckets in this tree cover their items' recorded keys. -/
@[expose] def Covers (w k : α → W) : {r : ℕ} → Tree α r → Prop
  | 0, .leaf b => CoversSlot w k b
  | _, .node b cs => CoversSlot w k b ∧ ∀ i, (cs i).Covers w k

theorem root_covers {w k : α → W} {tr : Tree α r} (h : tr.Covers w k) :
    CoversSlot w k tr.root := by cases tr with | leaf => exact h | node => exact h.1

private theorem pull_covers (w k : α → W) (next : Tree α r → Tree α r)
    (ih : ∀ tr, tr.Covers w k → (next tr).Covers w k) (cs : Fin 4 → Tree α r)
    (hc : ∀ i, (cs i).Covers w k) :
    CoversSlot w k (pull w next cs).1 ∧ ∀ i, ((pull w next cs).2 i).Covers w k := by
  unfold pull
  cases h : leastChild w cs with
  | none => exact ⟨empty_covers w k, hc⟩
  | some p =>
    obtain ⟨j, b⟩ := p
    constructor
    · simpa only [root_of_leastChild h] using root_covers (hc j)
    · intro i
      by_cases eq : i = j
      · subst i; simpa using ih _ (hc j)
      · simpa only [Function.update_of_ne eq] using hc i

theorem refill_covers (w k : α → W) (t : ℕ) (soft : Bool) (tr : Tree α r) (cov : tr.Covers w k) :
    (refill w t soft tr).Covers w k := by
  induction r with
  | zero => cases tr; exact empty_covers w k
  | succ r ih =>
    cases tr with
    | node old cs =>
      let next := refill w t soft (r := r)
      generalize ha : pull w next cs = first
      obtain ⟨a, cs'⟩ := first
      obtain ⟨ca, cc⟩ := pull_covers w k next ih cs cov.2
      rw [ha] at ca cc
      simp only [refill, show refill w t soft (r := r) = next from rfl, ha]
      split
      · cases a with
        | none => exact ⟨ca, cc⟩
        | some a =>
          generalize hb : pull w next cs' = second
          obtain ⟨b, cs''⟩ := second
          obtain ⟨cb, cd⟩ := pull_covers w k next ih cs' cc
          rw [hb] at cb cd
          cases b with
          | none => exact ⟨ca, cd⟩
          | some b => exact ⟨pool_covers w k ca cb, cd⟩
      · exact ⟨ca, cc⟩

theorem link_covers (w k : α → W) (t : ℕ) (cs : Fin 4 → Tree α r)
    (cov : ∀ i, (cs i).Covers w k) : (link w t cs).Covers w k :=
  refill_covers w k t false _ ⟨empty_covers w k, cov⟩

theorem extract_covers {w k : α → W} {t : ℕ} {tr tr' : Tree α r} {x a : α}
    (cov : tr.Covers w k) (hit : extract w t tr = some ((x, a), tr')) :
    k x ≤ w a ∧ tr'.Covers w k := by
  unfold extract at hit
  split at hit
  · contradiction
  · next b eq =>
    cases hit
    exact ⟨root_covers cov _ eq _ (by simp [contents]), refill_covers w k t true tr cov⟩
  · next b y ys eq =>
    cases hit
    obtain hold := root_covers cov _ eq
    have rest : CoversSlot w k (some ⟨a, ys⟩) := by
      rintro z ⟨⟩ f hf
      apply hold
      simp only [contents, Multiset.mem_add, Multiset.mem_singleton, Multiset.mem_coe] at hf ⊢
      exact hf.imp_right (List.mem_cons_of_mem _)
    refine ⟨hold x (by simp [contents]), ?_⟩
    cases tr with | leaf => exact rest | node => exact ⟨rest, cov.2⟩

/-- Increase any covered keys up to the heap minimum. -/
theorem covers_floor {w k k' : α → W} {tr : Tree α r} {level : W} (ord : tr.Ordered w)
    (lo : (level : WithTop W) ≤ key w tr.root) (cov : tr.Covers w k)
    (h : ∀ x, k' x ≤ max (k x) level) : tr.Covers w k' := by
  have slot {s : Option (Bucket α)} (hs : CoversSlot w k s)
      (low : (level : WithTop W) ≤ key w s) : CoversSlot w k' s := by
    rintro b rfl x hx
    exact (h x).trans (max_le (hs _ rfl _ hx) (WithTop.coe_le_coe.mp low))
  induction r with
  | zero => cases tr; exact slot cov lo
  | succ r ih =>
    cases tr with
    | node b cs =>
      exact ⟨slot cov.1 lo, fun i => ih (ord i).2 (lo.trans (ord i).1) (cov.2 i)⟩

/-- Every item whose recorded key strictly exceeds its input key is counted by the
pending-list corruption bound. -/
theorem count_raised_le {w k : α → W} {tr : Tree α r} (cov : tr.Covers w k) :
    (tr.items.filter (fun e => w e < k e)).card ≤ tr.corruptions := by
  have slot (s : Option (Bucket α)) (hs : CoversSlot w k s) :
      ((contents s).filter (fun e => w e < k e)).card ≤ s.elim 0 (fun b => b.pending.length) := by
    cases s with
    | none => simp [contents]
    | some b =>
      have le := hs b rfl b.rep (by simp [contents])
      simpa [contents, not_lt.mpr le] using
        Multiset.card_le_card (Multiset.filter_le (fun e => w e < k e) (b.pending : Multiset α))
  induction r with
  | zero => cases tr; exact slot _ cov
  | succ r ih =>
    cases tr with
    | node b cs =>
      have bnd := Finset.sum_le_sum (s := Finset.univ) fun (i : Fin 4) _ => ih (cov.2 i)
      simp only [items, corruptions, Multiset.filter_add, Multiset.card_add]
      convert Nat.add_le_add (slot b cov.1) bnd using 1
      simp [Fin.sum_univ_four]

end Tree

namespace Forest

/-- All trees are heap-ordered and cover a given set of external keys. -/
@[expose] def Covers (w k : α → W) (h : Forest α) : Prop := ∀ f ∈ h, f.2.Ordered w ∧ f.2.Covers w k

private theorem carry_covers (w k : α → W) (t : ℕ) (tr : Tree α r) (h : Forest α)
    (ord : tr.Ordered w) (co : tr.Covers w k) (all : h.Covers w k) :
    (carry w t tr h).Covers w k := by
  induction r, tr, h using carry.induct w t with
  | case1 r C rest B A tr ih =>
    rw [carry]
    simp only [dite_true]
    apply ih
    · apply Tree.link_ordered
      intro i
      fin_cases i
      · exact ord
      · exact (all ⟨r, A⟩ (by simp)).1
      · exact (all ⟨r, B⟩ (by simp)).1
      · exact (all ⟨r, C⟩ (by simp)).1
    · apply Tree.link_covers
      intro i
      fin_cases i
      · exact co
      · exact (all ⟨r, A⟩ (by simp)).2
      · exact (all ⟨r, B⟩ (by simp)).2
      · exact (all ⟨r, C⟩ (by simp)).2
    · exact fun f hf => all f (by simp [hf])
  | case2 | case3 | case4 | case5 =>
    rw [carry]
    all_goals first | assumption | simp_all [Covers]

theorem insert_covers {w k : α → W} (t : ℕ) (x : α) (h : Forest α) (eq : k x ≤ w x)
    (co : h.Covers w k) : (insert w t x h).Covers w k := by
  apply carry_covers w k t (Tree.singleton x) h trivial _ co
  rintro b ⟨⟩ y hy
  have eqy : y = x := by simpa [Bucket.singleton, contents] using hy
  exact eqy ▸ eq

private theorem leastRoot_min {w : α → W} {h : Forest α} {j : Fin h.length} {b : Bucket α}
    (hit : leastRoot w h = some (j, b)) (i : Fin h.length) :
    key w (some b) ≤ key w (h.get i).2.root := by
  cases e : (h.get i).2.root with
  | none => exact le_top
  | some c =>
    let rows := (List.finRange h.length).filterMap fun l => (h.get l).2.root.map (l, ·)
    have mem : (i, c) ∈ rows := List.mem_filterMap.mpr ⟨i, List.mem_finRange _, by rw [e]; rfl⟩
    change rows.minOn? (fun p => w p.2.rep) = some (j, b) at hit
    have bound := List.apply_minOn_le_of_mem (f := fun p : Fin h.length × Bucket α => w p.2.rep) mem
    rw [List.minOn_eq_of_minOn?_eq_some hit] at bound
    exact WithTop.coe_le_coe.mpr bound

private theorem root_of_leastRoot {w : α → W} {h : Forest α} {i : Fin h.length} {b : Bucket α}
    (hit : leastRoot w h = some (i, b)) : (h.get i).2.root = some b := by
  have mem := List.minOn?_mem hit
  obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp mem
  cases eq : (h.get j).2.root <;>
    simp only [eq, Option.map_none, Option.map_some, Option.some.injEq,
      Prod.mk.injEq, reduceCtorEq] at hj
  obtain ⟨rfl, rfl⟩ := hj
  exact eq

/-- The extracted item's old lower bound does not exceed its reported key. Any surviving
item's lower bound may now be increased to at most the maximum of its old bound and that key. -/
theorem extract_covers {w k : α → W} {t : ℕ} {h h' : Forest α} {x a : α}
    (cov : h.Covers w k) (hit : extract w t h = some ((x, a), h')) :
    k x ≤ w a ∧ ∀ k' : α → W, (∀ e, k' e ≤ max (k e) (w a)) → h'.Covers w k' := by
  unfold extract at hit
  cases found : leastRoot w h with
  | none => simp [found] at hit
  | some p =>
    obtain ⟨i, b⟩ := p
    cases ran : Tree.extract w t (h.get i).2 with
    | none => simp only [found, Option.bind_some, Option.bind_eq_bind, ran, Option.bind_none,
        Option.pure_def, reduceCtorEq] at hit
    | some result =>
      obtain ⟨⟨y, a'⟩, tr⟩ := result
      simp only [found, Option.bind_some, Option.bind_eq_bind, ran, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at hit
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hit
      obtain ⟨ord, co⟩ := cov (h.get i) (List.get_mem ..)
      obtain ⟨le, cov'⟩ := Tree.extract_covers co ran
      have ⟨ord', eq⟩ := Tree.extract_order ord ran
      have hb : key w (some b) = ↑(w a') :=
        (congrArg (key w) (root_of_leastRoot found)).symm.trans eq
      refine ⟨le, fun k' hk f hf => ?_⟩
      rcases List.mem_or_eq_of_mem_set hf with mem | rfl
      · obtain ⟨j, hj⟩ := List.mem_iff_get.mp mem
        have low := leastRoot_min found j
        rw [hb, hj] at low
        exact ⟨(cov f mem).1, Tree.covers_floor (cov f mem).1 low (cov f mem).2 hk⟩
      · have lifted : key w (h.get i).2.root ≤ key w tr.root := by
          unfold Tree.extract at ran
          split at ran
          · contradiction
          · cases ran; exact (Tree.refill_order w t true _ ord).2
          · next z v vs rootEq =>
            cases ran
            cases et : h.get i with
            | mk rr tree =>
              rw [et] at rootEq
              cases tree <;> exact (congrArg (key w) rootEq).le
        exact ⟨ord', Tree.covers_floor ord' (eq.ge.trans lifted) cov' hk⟩

theorem count_raised_le {w k : α → W} (h : Forest α) (cov : h.Covers w k) :
    (h.items.filter (fun e => w e < k e)).card ≤ h.corruptions := by
  induction h with
  | nil => simp [items, corruptions]
  | cons f fs ih =>
    simpa only [items, corruptions, List.map_cons, List.sum_cons, Multiset.filter_add,
      Multiset.card_add] using Nat.add_le_add (Tree.count_raised_le (cov f (by simp)).2)
        (ih fun z hz => cov z (by simp [hz]))

private theorem items_of_empty_root {w : α → W} {tr : Tree α r} (ord : tr.Ordered w)
    (empty : tr.root = none) : tr.items = 0 := by
  induction r with
  | zero =>
    cases tr with
    | leaf b => change b = none at empty; simp [Tree.items, empty, contents]
  | succ r ih =>
    cases tr with
    | node b cs =>
      change b = none at empty
      simp only [Tree.items, empty, contents, zero_add]
      apply Finset.sum_eq_zero
      intro i _
      apply ih (ord i).2
      have top := (ord i).1
      cases e : (cs i).root with
      | none => rfl
      | some c => simp [empty, e, key] at top

/-- An ordered forest can fail extraction only when it has no live occurrences. -/
theorem items_eq_zero_of_extract_none {w k : α → W} {h : Forest α} {t : ℕ} (cov : h.Covers w k)
    (empty : extract w t h = none) : h.items = 0 := by
  cases hmin : leastRoot w h with
  | none =>
    have no (i : Fin h.length) : (h.get i).2.root = none := by
      cases e : (h.get i).2.root with
      | none => rfl
      | some b =>
        have mem : (i, b) ∈ (List.finRange h.length).filterMap
            (fun j => (h.get j).2.root.map (j, ·)) :=
          List.mem_filterMap.mpr ⟨i, List.mem_finRange _, by rw [e]; rfl⟩
        have yes : (leastRoot w h).isSome := List.isSome_minOn?_of_mem mem
        simp [hmin] at yes
    apply List.sum_eq_zero
    intro b mem
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp mem
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hf
    exact items_of_empty_root (cov _ (List.get_mem ..)).1 (no i)
  | some p =>
    obtain ⟨i, b⟩ := p
    have root := root_of_leastRoot hmin
    obtain ⟨a, pending⟩ := b
    cases pending <;> simp only [extract, hmin, Option.bind_eq_bind, Option.bind_some,
      Tree.extract, root, Option.pure_def, reduceCtorEq] at empty

end Forest
end Cslib.SoftHeap
