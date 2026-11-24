/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Permutation
import Mathlib.Data.List.ProdSigma
import Mathlib.Tactic.Ring

/-!
# Constant row budgets for actual wire crossings

A crossing between neighboring owner rows belongs to their minimum row. A row containing at
most `B` original labels has at most `4 * B²` actual canonical crossings assigned to it.

## Main results

* `Diagram.crossingPairs_reorder_row_le`: a constant crossing budget per source row.
-/

public section

namespace Cslib.Complexity.NCL.Diagram
variable {Label : Type*}

private theorem row_support {owner : Label → ℕ} {a b : Label} {r : ℕ}
    (hab : owner a ≤ owner b + 1) (hba : owner b ≤ owner a + 1)
    (hr : min (owner a) (owner b) = r) :
    (owner a = r ∨ owner a = r + 1) ∧ (owner b = r ∨ owner b = r + 1) := by
  omega

private theorem local_pairs_row_le (pairs : List (Label × Label)) (xs : List Label)
    (owner : Label → ℕ) (B : ℕ) (hn : pairs.Nodup)
    (hm : ∀ a b, (a, b) ∈ pairs → a ∈ xs ∧ b ∈ xs)
    (hl : ∀ a b, (a, b) ∈ pairs → owner a ≤ owner b + 1 ∧ owner b ≤ owner a + 1)
    (hb : ∀ r, (xs.filter (fun a => owner a == r)).length ≤ B) (r : ℕ) :
    (pairs.filter (fun p => min (owner p.1) (owner p.2) == r)).length ≤ 4 * B ^ 2 := by
  let labels := xs.filter (fun a => owner a == r) ++ xs.filter (fun a => owner a == r + 1)
  have hmem (a : Label) (ha : a ∈ xs) (hr : owner a = r ∨ owner a = r + 1) :
      a ∈ labels := by
    rcases hr with hr | hr <;> simp [labels, ha, hr]
  have hsub : pairs.filter (fun p => min (owner p.1) (owner p.2) == r) ⊆ labels ×ˢ labels := by
    rintro ⟨a, b⟩ hp
    obtain ⟨hp, hr⟩ := List.mem_filter.mp hp
    have hs := row_support (hl a b hp).1 (hl a b hp).2 (by simpa only [beq_iff_eq] using hr)
    exact List.mem_product.mpr ⟨hmem a (hm a b hp).1 hs.1, hmem b (hm a b hp).2 hs.2⟩
  have hlen := (hn.filter (fun p => min (owner p.1) (owner p.2) == r)).length_le_of_subset hsub
  have hlabels : labels.length ≤ B + B := by
    simpa only [labels, List.length_append] using Nat.add_le_add (hb r) (hb (r + 1))
  calc
    _ ≤ labels.length * labels.length := by simpa only [List.length_product] using hlen
    _ ≤ (B + B) * (B + B) := Nat.mul_le_mul hlabels hlabels
    _ = 4 * B ^ 2 := by ring

variable {Γ : List Color → List Color → Type} [DecidableEq Label]

/-- A row with at most `B` wire labels owns at most `4 * B²` actual canonical crossings. -/
theorem crossingPairs_reorder_row_le (color : Label → Color) (ys xs : List Label)
    (h : xs.Perm ys) (hn : xs.Nodup) (srcRow ownerRow : Label → ℕ)
    (hxs : xs.Pairwise (fun a b => srcRow a ≤ srcRow b))
    (hys : ys.Pairwise (fun a b => ownerRow a ≤ ownerRow b))
    (hrow : ∀ a ∈ xs, ownerRow a ≤ srcRow a ∧ srcRow a ≤ ownerRow a + 1)
    (B : ℕ) (hb : ∀ r, (xs.filter (fun a => ownerRow a == r)).length ≤ B) (r : ℕ) :
    (((reorder (Γ := Γ) color ys xs h).diagram.crossingPairs
      (reorder color ys xs h).labeling.label).filter
        (fun p => min (ownerRow p.1) (ownerRow p.2) == r)).length ≤ 4 * B ^ 2 := by
  apply local_pairs_row_le _ xs ownerRow B (crossingPairs_reorder_nodup color ys xs h hn)
    (fun _ _ hp => mem_crossingPairs_reorder color ys xs h hp) _ hb r
  intro a b hp
  obtain ⟨hba, hab⟩ :=
    owner_bounds_crossingPairs_reorder color ys xs h srcRow ownerRow hxs hys hrow hp
  exact ⟨hab, hba.trans (Nat.le_succ _)⟩

end Cslib.Complexity.NCL.Diagram
