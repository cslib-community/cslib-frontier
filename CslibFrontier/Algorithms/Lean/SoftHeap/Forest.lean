/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

-- upstream: candidate
public import CslibFrontier.Algorithms.Lean.SoftHeap.RankedTree
import Mathlib.Tactic.FinCases

/-!
# A forest of ranked soft-heap trees

Insertions propagate carries in base four. Extraction finds a minimum representative among
occupied roots and refills just that tree. The forest keeps the insertion-leaf count through
deletions, giving the denominator for the soft heap's corruption guarantee. This functional
implementation finds the minimum by scanning the roots.
-/

public section

namespace Cslib.SoftHeap

/-- Trees of various ranks, packed together with their rank. -/
abbrev Packed (α : Type) := (r : ℕ) × Tree α r

/-- Roots in increasing rank order, with up to three trees in each rank. -/
abbrev Forest (α : Type) := List (Packed α)

variable {α : Type}

namespace Forest

/-- Insert a ranked tree, linking three leading trees of equal rank when a carry occurs. -/
@[expose] def carry {W : Type*} [LinearOrder W] (w : α → W) (t : ℕ) :
    {r : ℕ} → Tree α r → Forest α → Forest α
  | r, tr, ⟨a, A⟩ :: ⟨b, B⟩ :: ⟨c, C⟩ :: rest =>
      if ha : a = r then
        if hb : b = r then
          if hc : c = r then
            carry w t (Tree.link w t ![tr, ha ▸ A, hb ▸ B, hc ▸ C]) rest
          else ⟨r, tr⟩ :: ⟨a, A⟩ :: ⟨b, B⟩ :: ⟨c, C⟩ :: rest
        else ⟨r, tr⟩ :: ⟨a, A⟩ :: ⟨b, B⟩ :: ⟨c, C⟩ :: rest
      else ⟨r, tr⟩ :: ⟨a, A⟩ :: ⟨b, B⟩ :: ⟨c, C⟩ :: rest
  | r, tr, rest => ⟨r, tr⟩ :: rest
termination_by _ _ h => h.length

/-- Insert a new item with its original key. -/
@[expose] def insert {W : Type*} [LinearOrder W] (w : α → W) (t : ℕ) (x : α)
    (h : Forest α) : Forest α := carry w t (Tree.singleton x) h

/-- Find a current minimum root and its representative. -/
@[expose] def leastRoot {W : Type*} [LinearOrder W] (w : α → W) (h : Forest α) :
    Option (Fin h.length × Bucket α) :=
  ((List.finRange h.length).filterMap fun i => (h.get i).2.root.map (i, ·)).minOn?
    (fun p => w p.2.rep)

/-- Extract a live item, return its current representative, and replace the selected root. -/
@[expose] def extract {W : Type*} [LinearOrder W] (w : α → W) (t : ℕ) (h : Forest α) :
    Option ((α × α) × Forest α) := do
  let (i, _) ← leastRoot w h
  let result ← Tree.extract w t (h.get i).2
  return (result.1, h.set i ⟨(h.get i).1, result.2⟩)

/-- Number of previous insertions represented by the leaves of the forest. -/
@[expose] def insertions (h : Forest α) : ℕ := (h.map fun f => 4 ^ f.1).sum

/-- Count of live items currently assigned to another representative. -/
@[expose] def corruptions (h : Forest α) : ℕ := (h.map fun f => f.2.corruptions).sum

/-- All trees satisfy the bucket capacity and key-order invariant of the soft heap. -/
@[expose] def Valid {W : Type*} [LE W] (w : α → W) (t : ℕ) (h : Forest α) : Prop :=
  ∀ f ∈ h, f.2.Valid w t

theorem carry_spec {W : Type*} [LinearOrder W] (w : α → W) (t : ℕ) {r}
    (tr : Tree α r) (h : Forest α) (v : tr.Valid w t) (vh : h.Valid w t) :
    (carry w t tr h).Valid w t ∧ (carry w t tr h).insertions = 4 ^ r + h.insertions := by
  induction r, tr, h using carry.induct w t with
  | case1 r C rest B A tr ih =>
    rw [carry]
    simp only [dite_true]
    have vl : (Tree.link w t ![tr, A, B, C]).Valid w t := by
      apply Tree.link_valid
      intro i
      fin_cases i
      · exact v
      · exact vh ⟨r, A⟩ (by simp)
      · exact vh ⟨r, B⟩ (by simp)
      · exact vh ⟨r, C⟩ (by simp)
    have ⟨valid, mass⟩ := ih vl (fun f hf => vh f (by simp [hf]))
    refine ⟨valid, ?_⟩
    rw [mass]
    simp [insertions, Nat.pow_succ]
    omega
  | case2 | case3 | case4 | case5 =>
    rw [carry]
    all_goals first | assumption | simp_all [Valid, insertions]

theorem insert_spec {W : Type*} [LinearOrder W] (w : α → W) (t : ℕ)
    (x : α) (h : Forest α) (vh : h.Valid w t) :
    (insert w t x h).Valid w t ∧ (insert w t x h).insertions = 1 + h.insertions := by
  simpa [insert] using carry_spec w t (Tree.singleton x) h (Tree.singleton_valid w t x) vh

private theorem set_preserves {h : Forest α} (i : Fin h.length) (tr : Tree α (h.get i).1)
    {W : Type*} [LinearOrder W] {w : α → W} {t : ℕ} (v : tr.Valid w t) (vh : h.Valid w t) :
    Valid w t (h.set i ⟨(h.get i).1, tr⟩) ∧
      insertions (h.set i ⟨(h.get i).1, tr⟩) = h.insertions := by
  constructor
  · intro f hf
    rcases List.mem_or_eq_of_mem_set hf with h | e
    · exact vh f h
    · subst f; exact v
  · simp only [insertions, List.map_set]
    let mass := fun f : Packed α => 4 ^ f.1
    have hi : i.val < (h.map mass).length := by simp
    have eq := List.set_getElem_self (as := h.map mass) hi
    exact congrArg List.sum (by simpa only [List.getElem_map, List.get_eq_getElem] using eq)

theorem extract_spec {W : Type*} [LinearOrder W] {w : α → W} {t : ℕ} {h h' : Forest α}
    {x a : α} (vh : h.Valid w t) (hit : extract w t h = some ((x, a), h')) :
    w x ≤ w a ∧ h'.Valid w t ∧ h'.insertions = h.insertions := by
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
      simp only [found, Option.bind_some, Option.bind_eq_bind, ran,
        Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hit
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hit
      obtain ⟨raised, v⟩ := Tree.extract_valid (vh _ (List.getElem_mem ..)) ran
      exact ⟨raised, set_preserves i tr v vh⟩

/-- At any instant, at most a `1 / 4 ^ t` fraction of all insertions are currently corrupted. -/
theorem corruptions_bound {W : Type*} [LE W] {w : α → W} {t : ℕ} (h : Forest α) (vh : h.Valid w t) :
    h.corruptions * 4 ^ t ≤ h.insertions := by
  induction h with
  | nil => simp [corruptions, insertions]
  | cons f fs ih =>
    simpa only [corruptions, insertions, List.map_cons, List.sum_cons, Nat.add_mul] using
      Nat.add_le_add (Tree.corruptions_bound f.2 (vh f (by simp)))
        (ih (fun z hz => vh z (by simp [hz])))

end Forest
end Cslib.SoftHeap
