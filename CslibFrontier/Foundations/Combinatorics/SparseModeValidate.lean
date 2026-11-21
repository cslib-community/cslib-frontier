/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.SparseModeDense

/-!
# Validating a compressed exponent tuple

After checking the padded sparse syntax, the validator checks the last occupied colour and
the strict weighted mass budget. These two checks suffice: the original finite exponent
array reconstructs every row and entry of an accepted word.
-/

public section

namespace Cslib.SparseModeTuple

private theorem entryAt_ext (es fs : List Entry) (h : ∀ i, entryAt es i = entryAt fs i) :
    es = fs := by
  induction es generalizing fs with
  | nil =>
    cases fs with
    | nil => rfl
    | cons f fs => simpa [entryAt] using h f.skip
  | cons e es ih =>
    cases fs with
    | nil => simpa [entryAt] using h e.skip
    | cons f fs =>
      have hs : e.skip = f.skip := by
        rcases lt_trichotomy e.skip f.skip with hl | heq | hr
        · have := h e.skip
          simp [entryAt, hl] at this
        · exact heq
        · have := h f.skip
          simp [entryAt, hr] at this
      have hm : e.extra = f.extra := by simpa [entryAt, hs] using h e.skip
      have he : e = f := by cases e; cases f; simp_all
      subst f
      congr 1
      apply ih
      intro i
      have ht := h (e.skip + 1 + i)
      simpa [entryAt, show ¬e.skip + 1 + i < e.skip by omega,
        show e.skip + 1 + i ≠ e.skip by omega] using ht

/-- Positive gaps and multiplicities make a sparse descriptor unique, even when only
its exponent function is observable. -/
theorem coord_ext (rows other : List Row) (h : ∀ c i, coord rows c i = coord other c i) :
    rows = other := by
  induction rows generalizing other with
  | nil =>
    cases other with
    | nil => rfl
    | cons s ss => simpa [coord, entryAt] using h s.skip s.first.skip
  | cons r rs ih =>
    cases other with
    | nil => simpa [coord, entryAt] using h r.skip r.first.skip
    | cons s ss =>
      have hs : r.skip = s.skip := by
        rcases lt_trichotomy r.skip s.skip with hl | heq | hr
        · have := h r.skip r.first.skip
          simp [coord, entryAt, hl] at this
        · exact heq
        · have := h s.skip s.first.skip
          simp [coord, entryAt, hr] at this
      have he := entryAt_ext (r.first :: r.rest) (s.first :: s.rest)
        (fun i => by simpa [coord, hs] using h r.skip i)
      have hr : r = s := by cases r; cases s; simp_all
      subst s
      congr 1
      apply ih
      intro c i
      simpa [coord, show ¬r.skip + 1 + c < r.skip by omega,
        show r.skip + 1 + c ≠ r.skip by omega] using h (r.skip + 1 + c) i

private theorem entryAt_zero_of_mass (es : List Entry) (offset i : ℕ)
    (h : entryMass offset es ≤ offset + i) : entryAt es i = 0 := by
  induction es generalizing offset i with
  | nil => rfl
  | cons e es ih =>
    have hmass : offset + (e.skip + 1) ≤ entryMass offset (e :: es) := by
      simp only [entryMass]
      exact (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans (Nat.le_add_right _ _)
    have hl : e.skip < i := by omega
    rw [entryAt, ite_eq_right (by omega), ite_eq_right (by omega)]
    apply ih (offset + (e.skip + 1))
    have htail : entryMass (offset + (e.skip + 1)) es ≤ entryMass offset (e :: es) :=
      Nat.le_add_left _ _
    omega

/-- No weight can occur past the total weighted mass. Coordinates start at weight one. -/
theorem coord_zero_of_mass (rows : List Row) (c i : ℕ) (h : mass rows ≤ i) :
    coord rows c i = 0 := by
  induction rows generalizing c with
  | nil => rfl
  | cons r rs ih =>
    change entryMass 0 (r.first :: r.rest) + mass rs ≤ i at h
    rw [coord]
    split_ifs
    · rfl
    · exact entryAt_zero_of_mass _ 0 _ (by omega)
    · exact ih _ (by omega)

/-- Every coordinate beyond the occupied colour span is zero. -/
theorem coord_zero_of_colours (rows : List Row) (c i : ℕ) (h : colours rows ≤ c) :
    coord rows c i = 0 := by
  induction rows generalizing c with
  | nil => rfl
  | cons r rs ih =>
    change (r.skip + 1) + colours rs ≤ c at h
    rw [coord, ite_eq_right (by omega), ite_eq_right (by omega)]
    exact ih _ (by omega)

/-- Once the colour span and mass fit, reading the finite rectangle and repacking recovers
the entire sparse description, including its last occupied weight and colour. -/
theorem ofFn_coord {m n : ℕ} (rows : List Row) (hc : colours rows ≤ m) (hm : mass rows ≤ n) :
    ofFn (fun (c : Fin m) (i : Fin n) => coord rows c.val i.val) = rows := by
  apply coord_ext
  intro c i
  by_cases h₁ : c < m
  · by_cases h₂ : i < n
    · exact coord_ofFn _ ⟨c, h₁⟩ ⟨i, h₂⟩
    · rw [coord_ofFn_eq_zero _ (Or.inr (by omega)), coord_zero_of_mass _ _ _ (by omega)]
  · rw [coord_ofFn_eq_zero _ (Or.inl (by omega)), coord_zero_of_colours _ _ _ (by omega)]

/-- Validate a guessed word against its width, colour count and strict weight budget.
The two domain checks inspect only the sparse rows. -/
def validate (width m p : ℕ) (word : List Bool) : Option (List Row) := do
  let rows ← decode width word
  if colours rows ≤ m ∧ mass rows < p then some rows else none

/-- On canonical syntax only the two numerical domain tests remain. -/
theorem validate_padded {width m p : ℕ} {rows : List Row} (h : (encode rows).length ≤ width) :
    validate width m p (padded width rows) =
      if colours rows ≤ m ∧ mass rows < p then some rows else none := by
  simp [validate, decode_padded h]

/-- Exactly the canonically padded words for in-domain rows of mass strictly below the budget
pass the sparse validator. -/
theorem validate_eq_some_iff {width m p : ℕ} {word : List Bool} {rows : List Row} :
    validate width m p word = some rows ↔
      decode width word = some rows ∧ colours rows ≤ m ∧ mass rows < p := by
  cases h : decode width word with
  | none => simp [validate, h]
  | some r =>
    by_cases he : r = rows
    · subst rows
      by_cases hdom : colours r ≤ m ∧ mass r < p <;> simp [validate, h, hdom]
    · by_cases hdom : colours r ≤ m ∧ mass r < p <;> simp [validate, h, hdom, he]

end Cslib.SparseModeTuple
