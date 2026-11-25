/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

/-!
# Unate grid functions cut corners of few border squares

A function `g : ℕ → ℕ → Bool` **cuts a corner** of the unit square with lower-left corner `(i, j)`
if its mixed difference there is nonzero (`CutsCorner`):
`g i j + g (i + 1) (j + 1) ≠ g (i + 1) j + g i (j + 1)`, as `0/1` values. A function of two bits
has zero mixed difference exactly when it is the sum of a function of the first bit and a
function of the second. A threshold function of two bits cuts the corner exactly when it is not
constant and not a literal.

**Ring lemma** (`card_filter_cutsCorner_gridBorder_le`): if `g` is monotone or antitone in each
coordinate, uniformly in the other one, then it cuts a corner of at most `4` of the `4 (m - 1)`
squares on the border of the grid `{0, …, m} ^ 2` (`gridBorder`, `le_card_gridBorder`).

After reflecting coordinates, `g` is monotone in both. Then a cut square `(i, j)` has
`g i j = false`, `g (i + 1) (j + 1) = true` and `g (i + 1) j = g i (j + 1)`; it is an *outer* or
an *inner* corner of the boundary of the up-set `{g = true}` according to this common value. Two
distinct cut squares of the same kind are incomparable in the product order
(`eq_of_cutsCorner_of_le`), so a chain contains at most two cut squares
(`card_filter_cutsCorner_le_two`). The border is the union of the two chains
`{i = 0} ∪ {j = m - 1}` and `{j = 0} ∪ {i = m - 1}`.

This is the combinatorial step of the lower bound for Andreev's function with two address blocks
in [cslib-frontier#4640](https://github.com/cslib-community/cslib-frontier/issues/4640), there
phrased as "the boundary of a monotone region in the grid cuts corners of at most four border
squares".

## Main definitions

* `Cslib.Combinatorics.CutsCorner`: nonzero mixed difference on a unit square.
* `Cslib.Combinatorics.gridBorder`: the border squares of the `m × m` grid of unit squares.

## Main results

* `Cslib.Combinatorics.card_filter_cutsCorner_le_two`: a monotone grid function cuts a corner of
  at most two squares of a chain.
* `Cslib.Combinatorics.card_filter_cutsCorner_gridBorder_le`: the ring lemma.
* `Cslib.Combinatorics.le_card_gridBorder`: the border has at least `4 (m - 1)` squares.
-/

public section

namespace Cslib.Combinatorics

open Finset

/-- `g` **cuts a corner** of the unit square with lower-left corner `(i, j)`: its mixed difference
`g i j + g (i + 1) (j + 1) - g (i + 1) j - g i (j + 1)` there is nonzero. -/
@[expose] def CutsCorner (g : ℕ → ℕ → Bool) (i j : ℕ) : Prop :=
  (g i j).toNat + (g (i + 1) (j + 1)).toNat ≠ (g (i + 1) j).toNat + (g i (j + 1)).toNat

instance (g : ℕ → ℕ → Bool) (i j : ℕ) : Decidable (CutsCorner g i j) :=
  decidable_of_iff (¬(g i j).toNat + (g (i + 1) (j + 1)).toNat =
    (g (i + 1) j).toNat + (g i (j + 1)).toNat) Iff.rfl

/-- The unit squares `(i, j)`, `i, j < m`, on the border of the grid `{0, …, m} ^ 2`. -/
def gridBorder (m : ℕ) : Finset (ℕ × ℕ) :=
  (range m ×ˢ range m).filter fun p => p.1 = 0 ∨ p.2 = 0 ∨ p.1 + 1 = m ∨ p.2 + 1 = m

theorem mem_gridBorder {m : ℕ} {p : ℕ × ℕ} :
    p ∈ gridBorder m ↔ p.1 < m ∧ p.2 < m ∧ (p.1 = 0 ∨ p.2 = 0 ∨ p.1 + 1 = m ∨ p.2 + 1 = m) := by
  simp [gridBorder, and_assoc]

/-- The border of the `m × m` grid of unit squares has at least `4 (m - 1)` squares (exactly
`4 (m - 1)` for `m ≥ 2`). -/
theorem le_card_gridBorder (m : ℕ) : 4 * (m - 1) ≤ #(gridBorder m) := by
  rcases lt_or_ge m 2 with hm | hm
  · simp [show m - 1 = 0 by omega]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hsplit := card_filter_add_card_filter_not (s := range (k + 2) ×ˢ range (k + 2))
    fun p : ℕ × ℕ => p.1 = 0 ∨ p.2 = 0 ∨ p.1 + 1 = k + 2 ∨ p.2 + 1 = k + 2
  have hint : #((range (k + 2) ×ˢ range (k + 2)).filter fun p : ℕ × ℕ =>
      ¬(p.1 = 0 ∨ p.2 = 0 ∨ p.1 + 1 = k + 2 ∨ p.2 + 1 = k + 2)) ≤ k * k :=
    (card_le_card (t := Ioo 0 (k + 1) ×ˢ Ioo 0 (k + 1)) fun p hp => by
      simp only [mem_filter, mem_product, mem_range, mem_Ioo] at hp ⊢
      omega).trans_eq (by simp)
  rw [card_product, card_range, show (k + 2) * (k + 2) = k * k + 4 * k + 4 by ring] at hsplit
  simp only [gridBorder]
  omega

variable {g : ℕ → ℕ → Bool}

/-- On a grid function monotone in both coordinates, a cut square `(i, j)` has `g i j = false`,
`g (i + 1) (j + 1) = true` and `g (i + 1) j = g i (j + 1)`. -/
theorem CutsCorner.of_monotone (hg : ∀ ⦃i i' j j'⦄, i ≤ i' → j ≤ j' → g i j ≤ g i' j')
    {i j : ℕ} (h : CutsCorner g i j) :
    g i j = false ∧ g (i + 1) (j + 1) = true ∧ g (i + 1) j = g i (j + 1) :=
  (show ∀ a b c d : Bool, a.toNat + d.toNat ≠ b.toNat + c.toNat →
      a ≤ b → a ≤ c → b ≤ d → c ≤ d → a = false ∧ d = true ∧ b = c by decide)
    (g i j) (g (i + 1) j) (g i (j + 1)) (g (i + 1) (j + 1)) h
    (hg (Nat.le_succ i) le_rfl) (hg le_rfl (Nat.le_succ j))
    (hg le_rfl (Nat.le_succ j)) (hg (Nat.le_succ i) le_rfl)

/-- **Cut squares of the same kind are incomparable**: for a grid function monotone in both
coordinates, two cut squares `p ≤ q` with the same value `g (· + 1) ·` at their lower-right corners
are equal. -/
theorem eq_of_cutsCorner_of_le (hg : ∀ ⦃i i' j j'⦄, i ≤ i' → j ≤ j' → g i j ≤ g i' j')
    {p q : ℕ × ℕ} (hp : CutsCorner g p.1 p.2) (hq : CutsCorner g q.1 q.2) (hpq : p ≤ q)
    (hv : g (p.1 + 1) p.2 = g (q.1 + 1) q.2) : p = q := by
  rcases p, q with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  obtain ⟨hac, hbd⟩ := Prod.mk_le_mk.mp hpq
  obtain ⟨hp0, hp1, hp2⟩ := hp.of_monotone hg
  obtain ⟨hq0, hq1, hq2⟩ := hq.of_monotone hg
  dsimp only at *
  by_contra hne
  rw [Prod.mk.injEq] at hne
  have hlt : a < c ∨ (a = c ∧ b < d) := by omega
  have hF : ∀ {u v : Bool}, u ≤ v → u = true → v = false → False := by decide
  cases hval : g (a + 1) b <;> rcases hlt with h | ⟨rfl, h⟩
  · exact hF (hg (by omega) (Nat.succ_le_succ hbd)) hp1 (hq2.symm.trans (hv.symm.trans hval))
  · exact hF (hg le_rfl (by omega)) hp1 (hv.symm.trans hval)
  · exact hF (hg (by omega) hbd) hval hq0
  · exact hF (hg le_rfl (by omega)) (hp2.symm.trans hval) hq0

/-- **Chains**: a grid function monotone in both coordinates cuts a corner of at most two squares
of any chain of the product order. -/
theorem card_filter_cutsCorner_le_two (hg : ∀ ⦃i i' j j'⦄, i ≤ i' → j ≤ j' → g i j ≤ g i' j')
    (s : Finset (ℕ × ℕ)) (hs : ∀ p ∈ s, ∀ q ∈ s, p ≤ q ∨ q ≤ p) :
    #(s.filter fun p => CutsCorner g p.1 p.2) ≤ 2 := by
  refine (card_le_card_of_injOn (t := (univ : Finset Bool)) (fun p => g (p.1 + 1) p.2)
    (fun _ _ => mem_coe.mpr (mem_univ _)) fun p hp q hq hv => ?_).trans_eq rfl
  rw [mem_coe, mem_filter] at hp hq
  rcases hs p hp.1 q hq.1 with h | h
  · exact eq_of_cutsCorner_of_le hg hp.2 hq.2 h hv
  · exact (eq_of_cutsCorner_of_le hg hq.2 hp.2 h hv.symm).symm

/-- The ring lemma for a grid function monotone in both coordinates. -/
theorem card_filter_cutsCorner_gridBorder_le_of_monotone
    (hg : ∀ ⦃i i' j j'⦄, i ≤ i' → j ≤ j' → g i j ≤ g i' j') (m : ℕ) :
    #((gridBorder m).filter fun p => CutsCorner g p.1 p.2) ≤ 4 := by
  set A := (gridBorder m).filter fun p => p.1 = 0 ∨ p.2 + 1 = m
  set B := (gridBorder m).filter fun p => p.2 = 0 ∨ p.1 + 1 = m
  have hchain (s : Finset (ℕ × ℕ)) (P : ℕ × ℕ → Prop) [DecidablePred P]
      (hs : s = (gridBorder m).filter P)
      (hP : ∀ p q, p.1 < m → p.2 < m → q.1 < m → q.2 < m → P p → P q → p ≤ q ∨ q ≤ p) :
      #(s.filter fun p => CutsCorner g p.1 p.2) ≤ 2 :=
    card_filter_cutsCorner_le_two hg s fun p hp q hq => by
      rw [hs, mem_filter, mem_gridBorder] at hp hq
      exact hP p q hp.1.1 hp.1.2.1 hq.1.1 hq.1.2.1 hp.2 hq.2
  have hA := hchain A (fun p => p.1 = 0 ∨ p.2 + 1 = m) rfl fun _ _ _ _ _ _ _ _ => by
    simp only [Prod.le_def]; omega
  have hB := hchain B (fun p => p.2 = 0 ∨ p.1 + 1 = m) rfl fun _ _ _ _ _ _ _ _ => by
    simp only [Prod.le_def]; omega
  refine (card_le_card fun p hp => ?_).trans ((card_union_le _ _).trans (add_le_add hA hB))
  rw [mem_filter, mem_gridBorder] at hp
  simp only [A, B, mem_union, mem_filter, mem_gridBorder]
  by_cases hA : p.1 = 0 ∨ p.2 + 1 = m
  · exact Or.inl ⟨⟨hp.1, hA⟩, hp.2⟩
  · exact Or.inr ⟨⟨hp.1, by omega⟩, hp.2⟩

/-- Reflecting the first coordinate, `i ↦ m - i`, maps cut squares to cut squares. -/
theorem cutsCorner_reflect_fst {m i j : ℕ} (hi : i < m) :
    CutsCorner (fun i j => g (m - i) j) i j ↔ CutsCorner g (m - 1 - i) j := by
  simp only [CutsCorner, show m - i = m - 1 - i + 1 by omega, show m - (i + 1) = m - 1 - i by omega]
  omega

/-- Reflecting the second coordinate, `j ↦ m - j`, maps cut squares to cut squares. -/
theorem cutsCorner_reflect_snd {m i j : ℕ} (hj : j < m) :
    CutsCorner (fun i j => g i (m - j)) i j ↔ CutsCorner g i (m - 1 - j) := by
  simp only [CutsCorner, show m - j = m - 1 - j + 1 by omega, show m - (j + 1) = m - 1 - j by omega]
  omega

/-- An involution on `gridBorder m` transferring `CutsCorner` preserves its border count. -/
private theorem card_filter_cutsCorner_gridBorder_eq_of_involution {g g' : ℕ → ℕ → Bool} {m : ℕ}
    (f : ℕ × ℕ → ℕ × ℕ) (hmem : ∀ p ∈ gridBorder m, f p ∈ gridBorder m)
    (hinv : ∀ p ∈ gridBorder m, f (f p) = p)
    (hcut : ∀ p ∈ gridBorder m, CutsCorner g' p.1 p.2 ↔ CutsCorner g (f p).1 (f p).2) :
    #((gridBorder m).filter fun p => CutsCorner g' p.1 p.2) =
      #((gridBorder m).filter fun p => CutsCorner g p.1 p.2) := by
  refine card_nbij' f f ?_ ?_ (fun p hp => hinv p (mem_filter.mp hp).1)
    (fun p hp => hinv p (mem_filter.mp hp).1) <;> intro p hp <;> rw [mem_coe, mem_filter] at hp ⊢
  · exact ⟨hmem p hp.1, (hcut p hp.1).mp hp.2⟩
  · exact ⟨hmem p hp.1, (hcut (f p) (hmem p hp.1)).mpr (by simpa only [hinv p hp.1] using hp.2)⟩

theorem card_filter_cutsCorner_gridBorder_reflect_fst (g : ℕ → ℕ → Bool) (m : ℕ) :
    #((gridBorder m).filter fun p => CutsCorner (fun i j => g (m - i) j) p.1 p.2) =
      #((gridBorder m).filter fun p => CutsCorner g p.1 p.2) :=
  card_filter_cutsCorner_gridBorder_eq_of_involution (fun p => (m - 1 - p.1, p.2))
    (fun p hp => by rw [mem_gridBorder] at hp ⊢; omega)
    (fun p hp => by rw [mem_gridBorder] at hp; exact Prod.ext (by omega) rfl)
    fun p hp => by rw [mem_gridBorder] at hp; exact cutsCorner_reflect_fst hp.1

theorem card_filter_cutsCorner_gridBorder_reflect_snd (g : ℕ → ℕ → Bool) (m : ℕ) :
    #((gridBorder m).filter fun p => CutsCorner (fun i j => g i (m - j)) p.1 p.2) =
      #((gridBorder m).filter fun p => CutsCorner g p.1 p.2) :=
  card_filter_cutsCorner_gridBorder_eq_of_involution (fun p => (p.1, m - 1 - p.2))
    (fun p hp => by rw [mem_gridBorder] at hp ⊢; omega)
    (fun p hp => by rw [mem_gridBorder] at hp; exact Prod.ext rfl (by omega))
    fun p hp => by rw [mem_gridBorder] at hp; exact cutsCorner_reflect_snd hp.2.1

/-- **Ring lemma**: if `g` is monotone or antitone in each coordinate, uniformly in the other
coordinate, then `g` cuts a corner of at most `4` border squares of the `m × m` grid. -/
theorem card_filter_cutsCorner_gridBorder_le
    (h₁ : (∀ j, Monotone fun i => g i j) ∨ ∀ j, Antitone fun i => g i j)
    (h₂ : (∀ i, Monotone (g i)) ∨ ∀ i, Antitone (g i)) (m : ℕ) :
    #((gridBorder m).filter fun p => CutsCorner g p.1 p.2) ≤ 4 := by
  have hsub : ∀ {i i' : ℕ}, i ≤ i' → m - i' ≤ m - i := fun h => Nat.sub_le_sub_left h m
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact card_filter_cutsCorner_gridBorder_le_of_monotone
      (fun _ _ _ _ hi hj => (h₁ _ hi).trans (h₂ _ hj)) m
  · rw [← card_filter_cutsCorner_gridBorder_reflect_snd]
    exact card_filter_cutsCorner_gridBorder_le_of_monotone
      (fun _ _ _ _ hi hj => (h₁ _ hi).trans (h₂ _ (hsub hj))) m
  · rw [← card_filter_cutsCorner_gridBorder_reflect_fst]
    exact card_filter_cutsCorner_gridBorder_le_of_monotone
      (fun _ _ _ _ hi hj => (h₁ _ (hsub hi)).trans (h₂ _ hj)) m
  · rw [← card_filter_cutsCorner_gridBorder_reflect_snd,
      ← card_filter_cutsCorner_gridBorder_reflect_fst]
    exact card_filter_cutsCorner_gridBorder_le_of_monotone
      (fun _ _ _ _ hi hj => (h₁ _ (hsub hi)).trans (h₂ _ (hsub hj))) m

end Cslib.Combinatorics
