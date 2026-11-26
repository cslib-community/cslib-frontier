/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.List.Sections

/-!
# The odometer order of sections

A section of a list of lists `L = [l₀, l₁, …]` picks one entry from each list (`List.sections`).
`List.sections` lists them in odometer order, with the first entry running fastest.
`Cslib.Algorithms.WordRAM.PPSZ.nextSection` is the odometer step: advance the first entry to its
successor in its list, or, at the end of that list, return it to the start and carry into the
rest. `Cslib.Algorithms.WordRAM.PPSZ.nextSection_sections` proves that it steps through
`List.sections L` in order and stops after the last section, when every list is duplicate-free.
A word-RAM program that keeps a section in an array and steps it with `nextSection` therefore
visits every section exactly once.

## Main definitions

* `Cslib.Algorithms.WordRAM.PPSZ.succIn`: the entry after a given one in a list.
* `Cslib.Algorithms.WordRAM.PPSZ.nextSection`: the odometer step on sections.
* `Cslib.Algorithms.WordRAM.PPSZ.Enumerates`: a list of sections in odometer order, ending with
  a section that has no successor.

## Main results

* `Cslib.Algorithms.WordRAM.PPSZ.succIn_getElem`: the successor in a duplicate-free list.
* `Cslib.Algorithms.WordRAM.PPSZ.nextSection_sections`: the odometer enumerates
  `List.sections L`.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PPSZ

/-- The entry after the first occurrence of `a` in the list `l`, if any. -/
def succIn : List ℕ → ℕ → Option ℕ
  | [], _ => none
  | b :: l, a => if a = b then l.head? else succIn l a

/-- **The odometer step**: the section after `t` among the sections of `L`, if any. The first entry
advances to its successor in its list; at the end of its list, it returns to the start of the list
and the rest of the section advances. -/
def nextSection : List (List ℕ) → List ℕ → Option (List ℕ)
  | l :: L, a :: t =>
    match succIn l a with
    | some a' => some (a' :: t)
    | none => (nextSection L t).map (l.headD 0 :: ·)
  | _, _ => none

/-- In a duplicate-free list, the successor of the `i`-th entry is the `i + 1`-st, if any. -/
theorem succIn_getElem {l : List ℕ} (hl : l.Nodup) {i : ℕ} (hi : i < l.length) :
    succIn l l[i] = l[i + 1]? := by
  induction l generalizing i with
  | nil => simp at hi
  | cons b l ih =>
    rcases i with _ | i
    · simp [succIn, List.head?_eq_getElem?]
    · have hne : l[i]'(by simpa using hi) ≠ b :=
        fun h => (List.nodup_cons.mp hl).1 (h ▸ List.getElem_mem _)
      simp only [List.getElem_cons_succ, succIn, hne, ↓reduceIte]
      exact ih (List.nodup_cons.mp hl).2 (by simpa using hi)

/-- The list `xs` lists sections of `L` in odometer order: the odometer leads from each entry to
the next one, and from the last entry nowhere. -/
def Enumerates (L : List (List ℕ)) (xs : List (List ℕ)) : Prop :=
  ∀ i (h : i < xs.length), nextSection L xs[i] = xs[i + 1]?

/-- The first step of an enumeration. -/
theorem Enumerates.head {L : List (List ℕ)} {t : List ℕ} {xs : List (List ℕ)}
    (h : Enumerates L (t :: xs)) : nextSection L t = xs.head? := by
  rw [List.head?_eq_getElem?]
  exact h 0 (Nat.zero_lt_succ _)

/-- The rest of an enumeration. -/
theorem Enumerates.tail {L : List (List ℕ)} {t : List ℕ} {xs : List (List ℕ)}
    (h : Enumerates L (t :: xs)) : Enumerates L xs :=
  fun i hi => h (i + 1) (Nat.succ_lt_succ hi)

/-- One more list in front: each section of the rest is extended by every entry of `l`. -/
private theorem enumerates_flatMap {l : List ℕ} (hl : l.Nodup) (hne : l ≠ [])
    {L : List (List ℕ)} :
    ∀ S : List (List ℕ), Enumerates L S →
      Enumerates (l :: L) (S.flatMap fun t => l.map (· :: t))
  | [], _ => fun i hi => by simp at hi
  | t :: S, h => fun i hi => by
    have ih := enumerates_flatMap hl hne S h.tail
    simp only [List.flatMap_cons] at hi ⊢
    by_cases hil : i < l.length
    · rw [List.getElem_append_left (by simpa using hil)]
      simp only [List.getElem_map]
      by_cases hi1 : i + 1 < l.length
      · rw [List.getElem?_append_left (by simpa using hi1)]
        simp [nextSection, succIn_getElem hl hil, List.getElem?_eq_getElem hi1]
      · rw [List.getElem?_append_right (by simp; omega)]
        simp only [List.length_map, show i + 1 - l.length = 0 by omega, nextSection,
          succIn_getElem hl hil, List.getElem?_eq_none (by omega : l.length ≤ i + 1), h.head]
        obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil hne
        cases S <;> simp
    · have hi' : i - (l.map (· :: t)).length < (S.flatMap fun t => l.map (· :: t)).length := by
        simp only [List.length_append, List.length_map] at hi ⊢
        omega
      rw [List.getElem_append_right (by simp; omega),
        List.getElem?_append_right (by simp; omega), ih _ hi']
      exact congrArg _ (by simp only [List.length_map]; omega)

/-- **The odometer enumerates the sections.** When every list of `L` is duplicate-free, the
odometer step leads from each section of `L` to the next one in `List.sections L`, and from the
last one nowhere. -/
theorem nextSection_sections : ∀ {L : List (List ℕ)}, (∀ l ∈ L, l.Nodup) →
    Enumerates L L.sections
  | [], _ => fun i hi => by
    obtain rfl : i = 0 := by simpa [List.sections] using hi
    simp [nextSection]
  | l :: L, hL => by
    by_cases hne : l = []
    · rintro i hi
      simp [hne, List.sections, List.flatMap_eq_nil_iff.mpr fun _ _ => rfl] at hi
    · exact enumerates_flatMap (hL l (by simp)) hne _
        (nextSection_sections fun l' h => hL l' (by simp [h]))

end Cslib.Algorithms.WordRAM.PPSZ
