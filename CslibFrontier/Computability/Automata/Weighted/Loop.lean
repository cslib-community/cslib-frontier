/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Automata.Weighted.Hat

/-!
# Words and loop bodies on disjoint channels

Single-word indicator series `Series.word` and weighted finite sums of words `Series.body`, with
`RatLe` dimension bounds and `hat` evaluations.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Tape.Loop`.

## Main definitions

* `Cslib.Automata.Weighted.Series.word`: indicator series of one word.
* `Cslib.Automata.Weighted.Series.body`: weighted sum of finitely many words (a loop body).

## Main results

* `RatLe.word`: `Series.word w` has dimension at most `2 * w.length + 1`.
* `hat_word`, `RatLe.body`, `hat_body`.
-/

public section

namespace Cslib.Automata.Weighted

open Finset

variable {F : Type*} [CommRing F]

/-- The indicator series of a single word `w`. -/
@[expose] def Series.word {Ω : Type*} [DecidableEq Ω] (w : List Ω) : Series F Ω :=
  fun o => if o = w then 1 else 0

theorem RatLe.word {Ω : Type*} [DecidableEq Ω] (w : List Ω) :
    RatLe (2 * w.length + 1) (Series.word w : Series F Ω) := by
  induction w with
  | nil => exact RatLe.one
  | cons a w ih =>
    have h := (RatLe.letter (F := F) a).mul ih
    have e : Series.mul (Series.letter a) (Series.word w) =
        (Series.word (a :: w) : Series F Ω) := by
      funext o
      cases o with
      | nil => simp [Series.mul, Series.letter, Series.word]
      | cons b o =>
        rw [Series.mul, List.length_cons, Finset.sum_range_succ', Finset.sum_range_succ']
        have hzero : ∀ k ∈ range o.length,
            Series.letter (F := F) a ((b :: o).take (k + 1 + 1)) *
              Series.word w ((b :: o).drop (k + 1 + 1)) = 0 := by
          intro k hk
          have hk' : k < o.length := Finset.mem_range.1 hk
          obtain ⟨c, o', rfl⟩ : ∃ c o', o = c :: o' := by
            cases o with
            | nil => simp at hk'
            | cons c o' => exact ⟨c, o', rfl⟩
          simp [Series.letter]
        rw [Finset.sum_eq_zero hzero, zero_add]
        by_cases hb : b = a
        · subst hb
          by_cases ho : o = w <;> simp [Series.letter, Series.word, ho]
        · simp [Series.letter, Series.word, hb]
    rw [e] at h
    exact h.mono (by simp; omega)

section Channel

variable {Z Γ : Type*} [Fintype Z] [DecidableEq Z] [Finite Γ] [DecidableEq Γ]

theorem hat_word (w : List (Z × Γ)) (v : Z → List Γ) :
    hat (Series.word w : Series F (Z × Γ)) v = if v = proj w then 1 else 0 := by
  simp only [hat, Series.word, Finset.sum_ite_eq', mem_fib]
  by_cases h : v = proj w
  · simp [h]
  · simp [h, Ne.symm h]

/-- The body of a loop: a weighted sum of finitely many words. -/
@[expose] def Series.body {Z Γ κ : Type*} [DecidableEq Z] [DecidableEq Γ] [Fintype κ]
    (wd : κ → List (Z × Γ)) (c : κ → F) : Series F (Z × Γ) :=
  ∑ k, c k • Series.word (wd k)

theorem RatLe.body {Z Γ κ : Type*} [DecidableEq Z] [DecidableEq Γ] [Fintype κ]
    (wd : κ → List (Z × Γ)) (c : κ → F) :
    RatLe (∑ k, (2 * (wd k).length + 1)) (Series.body wd c) :=
  RatLe.sum _ _ _ fun k _ => (RatLe.word (wd k)).smul (c k)

theorem hat_body {κ : Type*} [Fintype κ] (wd : κ → List (Z × Γ)) (c : κ → F) (v : Z → List Γ) :
    hat (Series.body wd c) v = ∑ k, if v = proj (wd k) then c k else 0 := by
  rw [Series.body, hat_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hat_smul, hat_word]
  simp

end Channel

end Cslib.Automata.Weighted
