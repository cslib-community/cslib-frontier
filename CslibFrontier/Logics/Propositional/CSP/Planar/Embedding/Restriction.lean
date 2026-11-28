/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Boundary
import Mathlib.Data.List.GetD

/-!
# Short first returns in executable boundary restrictions

These equations inspect the literal list-funded scan used by `restrictPrefix`. Its first
retained successor is read after one, two or three steps. The raw table may be malformed elsewhere;
the stated length and retained-index hypotheses are sufficient for these local equations.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

private theorem getD_restrictPrefix_eq_find? (c : Graph.RotationCertificate) (darts i : ℕ)
    (hi : i < darts) :
    (restrictPrefix darts c).successor.getD i 0 =
      (((List.range c.successor.length).map fun k =>
        Graph.RotationCertificate.walk c.successor (k + 1) i).find?
          (fun j => decide (j < darts))).getD 0 := by
  unfold restrictPrefix
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map, List.length_range] using hi),
    List.getElem_map, List.getElem_range]

private theorem find?_map_range_succ {α : Type*} (f : ℕ → α) (p : α → Bool) (n : ℕ) :
    ((List.range (n + 1)).map f).find? p =
      if p (f 0) then some (f 0) else ((List.range n).map fun k => f (k + 1)).find? p := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  cases hp : p (f 0) <;> simp [hp, Function.comp_def]

/-- A retained immediate successor is the first return, provided the table funds one step. -/
theorem getD_restrictPrefix_one (c : Graph.RotationCertificate) (darts i : ℕ)
    (hi : i < darts) (hc : 0 < c.successor.length) (hs : c.successor.getD i 0 < darts) :
    (restrictPrefix darts c).successor.getD i 0 = c.successor.getD i 0 := by
  rw [getD_restrictPrefix_eq_find? c darts i hi,
    show c.successor.length = (c.successor.length - 1) + 1 by omega, find?_map_range_succ]
  simp only [Graph.RotationCertificate.walk, Nat.zero_add, Function.iterate_one,
    decide_eq_true_eq, hs, ↓reduceIte, Option.getD_some]

private theorem rotationCertificate_eq_of_getD {a b : Graph.RotationCertificate}
    (hlen : a.successor.length = b.successor.length)
    (hget : ∀ i < a.successor.length, a.successor.getD i 0 = b.successor.getD i 0) : a = b := by
  cases a; cases b
  congr 1
  exact List.ext_getElem hlen fun i hi hj => by
    simpa only [List.getD_eq_getElem _ 0 hi, List.getD_eq_getElem _ 0 hj] using hget i hi

/-- Restriction to the full table is literal identity when every successor stays within
its length. This includes the empty table, without inventing a positive scan clock. -/
theorem restrictPrefix_eq_self (c : Graph.RotationCertificate)
    (h : ∀ i < c.successor.length, c.successor.getD i 0 < c.successor.length) :
    restrictPrefix c.successor.length c = c :=
  rotationCertificate_eq_of_getD (length_restrictPrefix _ _) fun i hi => by
    rw [length_restrictPrefix] at hi
    exact getD_restrictPrefix_one c _ i hi (by omega) (h i hi)

/-- If the first successor is deleted and the second retained, two list-funded steps find
the second successor exactly. No search clock depends on the numerical table entries. -/
theorem getD_restrictPrefix_two (c : Graph.RotationCertificate) (darts i : ℕ)
    (hi : i < darts) (hc : 2 ≤ c.successor.length)
    (hs : darts ≤ c.successor.getD i 0)
    (ht : c.successor.getD (c.successor.getD i 0) 0 < darts) :
    (restrictPrefix darts c).successor.getD i 0 = c.successor.getD (c.successor.getD i 0) 0 := by
  rw [getD_restrictPrefix_eq_find? c darts i hi,
    show c.successor.length = (c.successor.length - 2) + 1 + 1 by omega,
    find?_map_range_succ, find?_map_range_succ]
  simp only [Graph.RotationCertificate.walk, Nat.zero_add, Function.iterate_succ_apply',
    Function.iterate_zero_apply, decide_eq_true_eq, Nat.not_lt.mpr hs, ht, ↓reduceIte,
    Option.getD_some]

/-- If exactly the first two successors are deleted, three list-funded steps find the
third successor. In particular the clock is not funded by the deleted numerical indices. -/
theorem getD_restrictPrefix_three (c : Graph.RotationCertificate) (darts i : ℕ)
    (hi : i < darts) (hc : 3 ≤ c.successor.length)
    (hs : darts ≤ c.successor.getD i 0)
    (ht : darts ≤ c.successor.getD (c.successor.getD i 0) 0)
    (hu : c.successor.getD (c.successor.getD (c.successor.getD i 0) 0) 0 < darts) :
    (restrictPrefix darts c).successor.getD i 0 =
      c.successor.getD (c.successor.getD (c.successor.getD i 0) 0) 0 := by
  rw [getD_restrictPrefix_eq_find? c darts i hi,
    show c.successor.length = (c.successor.length - 3) + 1 + 1 + 1 by omega,
    find?_map_range_succ, find?_map_range_succ, find?_map_range_succ]
  simp only [Graph.RotationCertificate.walk, Nat.zero_add, Function.iterate_succ_apply',
    Function.iterate_zero_apply, decide_eq_true_eq, Nat.not_lt.mpr hs, Nat.not_lt.mpr ht, hu,
    ↓reduceIte, Option.getD_some]

/-- An intermediate restriction does not change first returns that reach the smaller
prefix in at most two steps. Both scans use their literal list-funded clocks; the raw table
may be malformed away from the stated prefix. This applies to distinct boundary markers. -/
theorem restrictPrefix_restrictPrefix_of_short_returns (c : Graph.RotationCertificate)
    (m n : ℕ) (hmn : m ≤ n) (hc : 2 ≤ c.successor.length)
    (hshort : ∀ i < m, c.successor.getD i 0 < m ∨
      c.successor.getD (c.successor.getD i 0) 0 < m) :
    restrictPrefix m (restrictPrefix n c) = restrictPrefix m c := by
  refine rotationCertificate_eq_of_getD
    ((length_restrictPrefix m (restrictPrefix n c)).trans (length_restrictPrefix m c).symm)
    fun i hi => ?_
  have him : i < m := by rwa [length_restrictPrefix] at hi
  have hin : i < n := by omega
  have hclock : 0 < (restrictPrefix n c).successor.length := by rw [length_restrictPrefix]; omega
  by_cases hs : c.successor.getD i 0 < m
  · have hn : (restrictPrefix n c).successor.getD i 0 = c.successor.getD i 0 :=
      getD_restrictPrefix_one c n i hin (by omega) (by omega)
    rw [getD_restrictPrefix_one (restrictPrefix n c) m i him hclock (by rw [hn]; exact hs),
      hn, getD_restrictPrefix_one c m i him (by omega) hs]
  · have ht : c.successor.getD (c.successor.getD i 0) 0 < m := (hshort i him).resolve_left hs
    have hold := getD_restrictPrefix_two c m i him hc (by omega) ht
    by_cases hn : c.successor.getD i 0 < n
    · have h₁ := getD_restrictPrefix_one c n i hin (by omega) hn
      have h₂ := getD_restrictPrefix_one c n (c.successor.getD i 0) hn (by omega) (by omega)
      have hfund : 2 ≤ (restrictPrefix n c).successor.length := by
        rw [length_restrictPrefix]; omega
      rw [getD_restrictPrefix_two (restrictPrefix n c) m i him hfund (by rw [h₁]; omega)
        (by rw [h₁, h₂]; exact ht), h₁, h₂, hold]
    · have h₁ := getD_restrictPrefix_two c n i hin hc (by omega) (by omega)
      rw [getD_restrictPrefix_one (restrictPrefix n c) m i him hclock (by rw [h₁]; exact ht),
        h₁, hold]

end Cslib.Complexity.CSP.OrderedBoundary
