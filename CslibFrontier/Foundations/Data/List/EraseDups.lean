/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card
import CslibFrontier.Foundations.Data.List.EraseDupsBy
import Mathlib.Data.List.Find

/-!
# Erasing duplicates, keeping first occurrences

Core `List.eraseDups` keeps the first occurrence of each entry, in order, and core proves that it
keeps every entry (`List.mem_eraseDups`). This file adds that the result is a duplicate-free
sublist, that it fixes exactly the duplicate-free lists, and that its length is the number of
distinct entries.

## Main results

* `List.eraseDups_sublist`, `List.nodup_eraseDups`, `List.eraseDups_eq_self`.
* `List.find?_eraseDups`: the first entry satisfying a predicate is that of the list.
* `List.toFinset_eraseDups`, `List.length_eraseDups`.
-/

public section

namespace List

variable {α : Type*}

/-- `eraseDups` keeps a sublist. -/
theorem eraseDups_sublist [BEq α] (l : List α) : l.eraseDups.Sublist l :=
  eraseDupsBy_sublist l

/-- `eraseDups` leaves no duplicates. -/
theorem nodup_eraseDups [BEq α] [LawfulBEq α] (l : List α) : l.eraseDups.Nodup :=
  (pairwise_eraseDupsBy l).imp fun h hab => by subst hab; simp at h

/-- `eraseDups` fixes exactly the duplicate-free lists. -/
theorem eraseDups_eq_self [BEq α] [LawfulBEq α] {l : List α} : l.eraseDups = l ↔ l.Nodup := by
  refine ⟨fun h => h ▸ nodup_eraseDups l, fun h => ?_⟩
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := nodup_cons.1 h
    have hfilter : (l.filter fun b => !b == a) = l :=
      filter_eq_self.2 fun b hb => by
        have hba : b ≠ a := fun hba => ha (hba ▸ hb)
        simpa using hba
    rw [eraseDups_cons, hfilter, ih hl]

/-- `eraseDups` keeps first occurrences, so its first entry satisfying `p` is that of the list. -/
theorem find?_eraseDups [BEq α] [LawfulBEq α] (p : α → Bool) (l : List α) :
    l.eraseDups.find? p = l.find? p := by
  induction l using (measure List.length).wf.induction
  rename_i l ih
  cases l with
  | nil => rfl
  | cons a l =>
    rw [eraseDups_cons, find?_cons, find?_cons]
    cases hp : p a with
    | true => rfl
    | false =>
      rw [ih _ (Nat.lt_succ_of_le (length_filter_le _ _)), find?_filter]
      refine find?_congr rfl fun x _ => ?_
      by_cases hx : x = a
      · subst hx; simp [hp]
      · simp [hx]

variable [DecidableEq α]

@[simp] theorem toFinset_eraseDups (l : List α) : l.eraseDups.toFinset = l.toFinset := by
  ext
  simp

/-- The length of `eraseDups` is the number of distinct entries. -/
theorem length_eraseDups (l : List α) : l.eraseDups.length = l.toFinset.card := by
  rw [← toFinset_eraseDups, toFinset_card_of_nodup (nodup_eraseDups l)]

end List
