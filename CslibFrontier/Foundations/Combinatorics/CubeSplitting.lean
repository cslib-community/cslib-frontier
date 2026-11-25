/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

/-!
# Threshold crossings of separable unate forms on unit cubes of a grid

Let `F : ι → ℕ → ℝ` be a family of functions, each monotone or antitone, and consider the
separable form `s ↦ ∑ i, F i (s i)` on the grid `{0, …, m} ^ ι`. The **unit cubes** of the grid are
indexed by `q : ι → Fin m`, with vertices `q + z` for `z : ι → Bool`. The threshold `θ` **splits**
`q` if the form is `< θ` at one vertex and `≥ θ` at another (`CubeSplits`).

At most `m ^ |ι| - (m - 1) ^ |ι|` of the `m ^ |ι|` unit cubes are split
(`card_cubeSplits_le`). After reflecting the antitone coordinates, every form is monotone; then the
cube `q` is split only if the form is `< θ` at `q` and `≥ θ` at `q + 1`, so at most one cube on each
diagonal line `q, q + 1, q + 2, …` is split. Each line contains exactly one cube with a zero
coordinate, and there are `m ^ |ι| - (m - 1) ^ |ι|` of those. That a unate function changes value
at most once along a chain compatible with its orientation is classical
([Impagliazzo, Paturi and Saks, Lemma 2.1][ImpagliazzoPaturiSaks1997]); the count of split cubes is
Lemma 15 of Reitwiessner, *Depth-Two Threshold Circuits for Andreev's Function* (2026).

## Main definitions

* `Cslib.Combinatorics.CubeSplits`: the threshold `θ` splits the unit cube `q`.

## Main results

* `Cslib.Combinatorics.card_cubeSplits_le_of_monotone`: the bound for monotone forms.
* `Cslib.Combinatorics.card_cubeSplits_le`: the bound when each form is monotone or antitone.
-/

public section

namespace Cslib.Combinatorics

open Finset

variable {ι : Type*} [Fintype ι] {m : ℕ}

/-- The threshold `θ` **splits** the unit cube `q : ι → Fin m` of the separable form
`s ↦ ∑ i, F i (s i)` if the form is below `θ` at some vertex `q + z` and at least `θ` at another
vertex `q + z'`, `z z' : ι → Bool`. -/
def CubeSplits (F : ι → ℕ → ℝ) (θ : ℝ) (q : ι → Fin m) : Prop :=
  ∃ z z' : ι → Bool, ∑ i, F i (q i + (z i).toNat) < θ ∧ θ ≤ ∑ i, F i (q i + (z' i).toNat)

noncomputable instance (F : ι → ℕ → ℝ) (θ : ℝ) (q : ι → Fin m) : Decidable (CubeSplits F θ q) :=
  Classical.propDecidable _

theorem cubeSplits_iff {F : ι → ℕ → ℝ} {θ : ℝ} {q : ι → Fin m} :
    CubeSplits F θ q ↔ ∃ z z' : ι → Bool,
      ∑ i, F i (q i + (z i).toNat) < θ ∧ θ ≤ ∑ i, F i (q i + (z' i).toNat) :=
  Iff.rfl

/-- For monotone forms, a split cube has its lowest vertex below `θ` and its highest vertex at
least `θ`. -/
theorem CubeSplits.lt_and_le_of_monotone {F : ι → ℕ → ℝ} (hF : ∀ i, Monotone (F i)) {θ : ℝ}
    {q : ι → Fin m} (h : CubeSplits F θ q) :
    ∑ i, F i (q i) < θ ∧ θ ≤ ∑ i, F i (q i + 1) := by
  obtain ⟨z, z', hz, hz'⟩ := h
  refine ⟨lt_of_le_of_lt (sum_le_sum fun i _ => hF i (Nat.le_add_right _ _)) hz,
    hz'.trans (sum_le_sum fun i _ => hF i ?_)⟩
  cases z' i <;> simp

/-- For monotone forms, two split cubes on a common diagonal line coincide. -/
theorem CubeSplits.eq_zero_of_monotone {F : ι → ℕ → ℝ} (hF : ∀ i, Monotone (F i)) {θ : ℝ}
    {q q' : ι → Fin m} (h : CubeSplits F θ q) (h' : CubeSplits F θ q') {d : ℕ}
    (hd : ∀ i, (q' i : ℕ) = q i + d) : d = 0 := by
  by_contra hd0
  have := sum_le_sum (s := univ) fun i _ => hF i (show (q i : ℕ) + 1 ≤ q' i by rw [hd i]; omega)
  linarith [(h.lt_and_le_of_monotone hF).2, (h'.lt_and_le_of_monotone hF).1]

/-- The number of `p : ι → Fin m` with a zero coordinate is `m ^ |ι| - (m - 1) ^ |ι|`. -/
theorem card_exists_val_eq_zero [DecidableEq ι] :
    #{p : ι → Fin m | ∃ i, (p i : ℕ) = 0} = m ^ Fintype.card ι - (m - 1) ^ Fintype.card ι := by
  classical
  have hne : #(univ.filter fun t : Fin m => (t : ℕ) ≠ 0) = m - 1 := by
    rcases m with _ | m
    · simp
    · rw [show (univ.filter fun t : Fin (m + 1) => (t : ℕ) ≠ 0) = univ.erase 0 by
        ext t; rw [mem_filter, mem_erase, Fin.ne_iff_vne]
        simp,
        card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  have hsum := card_filter_add_card_filter_not
    (s := (univ : Finset (ι → Fin m))) fun p => ∃ i, (p i : ℕ) = 0
  rw [show (univ.filter fun p : ι → Fin m => ¬∃ i, (p i : ℕ) = 0) =
      Fintype.piFinset fun _ => univ.filter fun t : Fin m => (t : ℕ) ≠ 0 by
    ext p; simp [Fintype.mem_piFinset], Fintype.card_piFinset, prod_const, card_univ, hne,
    card_univ, Fintype.card_fun, Fintype.card_fin] at hsum
  omega

/-- **Split cubes of a monotone separable form**: if every `F i` is monotone, the threshold `θ`
splits at most `m ^ |ι| - (m - 1) ^ |ι|` of the `m ^ |ι|` unit cubes. -/
theorem card_cubeSplits_le_of_monotone [DecidableEq ι] (F : ι → ℕ → ℝ) (hF : ∀ i, Monotone (F i))
    (θ : ℝ) :
    #{q : ι → Fin m | CubeSplits F θ q} ≤ m ^ Fintype.card ι - (m - 1) ^ Fintype.card ι := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [filter_false_of_mem fun q _ ⟨z, z', hz, hz'⟩ => by
      simp only [univ_eq_empty, sum_empty] at hz hz'; linarith]
    simp
  -- Map every cube to the first cube of its diagonal line.
  let a : (ι → Fin m) → ℕ := fun q => univ.inf' univ_nonempty fun i => (q i : ℕ)
  have ha (q : ι → Fin m) (i : ι) : a q ≤ q i := inf'_le _ (mem_univ i)
  let start : (ι → Fin m) → ι → Fin m := fun q i =>
    ⟨q i - a q, lt_of_le_of_lt (Nat.sub_le _ _) (q i).isLt⟩
  have hmaps : ∀ q ∈ univ.filter fun q : ι → Fin m => CubeSplits F θ q,
      start q ∈ univ.filter fun p : ι → Fin m => ∃ i, (p i : ℕ) = 0 := fun q _ => by
    obtain ⟨i, -, hi⟩ := exists_mem_eq_inf' (univ_nonempty (α := ι)) fun i => (q i : ℕ)
    exact mem_filter.mpr ⟨mem_univ _, i, by simp only [start, a]; omega⟩
  have hinj : Set.InjOn start ↑(univ.filter fun q : ι → Fin m => CubeSplits F θ q) := by
    have step {q q' : ι → Fin m} (hs : CubeSplits F θ q) (hs' : CubeSplits F θ q')
        (hst : start q = start q') (hle : a q ≤ a q') : q = q' := by
      have hcoord (i : ι) : (q i : ℕ) - a q = q' i - a q' := congrArg Fin.val (congrFun hst i)
      have hd := hs.eq_zero_of_monotone hF hs' (d := a q' - a q) fun i => by
        have : _ ∧ _ ∧ _ := ⟨hcoord i, ha q i, ha q' i⟩; omega
      exact funext fun i => Fin.ext (by have : _ ∧ _ ∧ _ := ⟨hcoord i, ha q i, ha q' i⟩; omega)
    intro q hq q' hq' hst
    rcases le_total (a q) (a q') with hle | hle
    · exact step (mem_filter.mp hq).2 (mem_filter.mp hq').2 hst hle
    · exact (step (mem_filter.mp hq').2 (mem_filter.mp hq).2 hst.symm hle).symm
  exact (card_le_card_of_injOn start hmaps hinj).trans_eq card_exists_val_eq_zero

/-- **Split cubes of a unate separable form** (Lemma 15 of Reitwiessner's preprint): if every
`F i` is monotone or antitone, the threshold `θ` splits at most `m ^ |ι| - (m - 1) ^ |ι|` of the
`m ^ |ι|` unit cubes. -/
theorem card_cubeSplits_le [DecidableEq ι] (F : ι → ℕ → ℝ)
    (hF : ∀ i, Monotone (F i) ∨ Antitone (F i)) (θ : ℝ) :
    #{q : ι → Fin m | CubeSplits F θ q} ≤ m ^ Fintype.card ι - (m - 1) ^ Fintype.card ι := by
  classical
  -- Reflect the antitone coordinates.
  let F' : ι → ℕ → ℝ := fun i s => if Monotone (F i) then F i s else F i (m - s)
  have hF' (i : ι) : Monotone (F' i) := by
    by_cases hi : Monotone (F i)
    · simp [F', hi]
    · intro s t hst
      simp only [F', hi, ↓reduceIte]
      exact (hF i).resolve_left hi (Nat.sub_le_sub_left hst m)
  let r : (ι → Fin m) → ι → Fin m := fun q i => if Monotone (F i) then q i else (q i).rev
  have hr : Function.Injective r := fun q q' h => funext fun i => by
    by_cases hi : Monotone (F i) <;> simpa [r, hi] using congrFun h i
  refine (card_le_card_of_injOn r (fun q hq => ?_) hr.injOn).trans
    (card_cubeSplits_le_of_monotone F' hF' θ)
  obtain ⟨z, z', hz, hz'⟩ := (mem_filter.mp hq).2
  let flip : (ι → Bool) → ι → Bool := fun z i => if Monotone (F i) then z i else !z i
  have hval (z : ι → Bool) (i : ι) :
      F' i (r q i + (flip z i).toNat) = F i (q i + (z i).toNat) := by
    by_cases hi : Monotone (F i)
    · simp [F', r, flip, hi]
    · simp only [F', r, flip, hi, ↓reduceIte, Fin.val_rev]
      exact congrArg (F i) (by have := (q i).isLt; cases z i <;> simp <;> omega)
  exact mem_filter.mpr ⟨mem_univ _, flip z, flip z', by simpa only [hval] using hz,
    by simpa only [hval] using hz'⟩

end Cslib.Combinatorics
