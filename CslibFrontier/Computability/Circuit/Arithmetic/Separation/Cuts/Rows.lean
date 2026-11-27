/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.List.StairRefinement
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Fin.Basic

/-!
# Row data of a staircase

In Lemma I.2 of [AnthropicVPVNP2026] (modules `Nc.Cut.Defs` and `Nc.Cut.Rows`), the words
`X a b` that a party `a` (a node of the paper) writes on a tape and a party `b` reads form a
matrix with staircase support (`List.StairRefinement.Stair`), because a tape is a queue. This
condition compares two rows. *Row data* (`Cut.RowData`, the data `ρ` of the paper) replace it by
conditions on single rows: they say for every row whether it is empty, and which are the first
and the last column that it uses; for an empty row both are the last column of the row before.
Every row has to be as its row data say (`Cut.RowData.Ok`), and the row data have to be those of
a staircase (`Cut.ValidRow`).

A matrix of words has valid row data that fit its rows if and only if it has staircase support,
and then the row data are those of the matrix, `Cut.rowsOf` (`Cut.validRow_and_ok_iff`).

## Main definitions

* `Cut.RowData`, `Cut.RowData.Ok`: the row data of a row, and the rows that fit them.
* `Cut.prevLast`, `Cut.ValidRow`, `Cut.ValidRows`: the last column of the row before, and the
  row data of a staircase, on one tape and on all tapes.
* `Cut.rowsOf`: the row data of a matrix of words.

## Main results

* `Cut.validRow_and_ok_iff`: row data are valid and fit the rows of a matrix if and only if the
  matrix has staircase support and they are its row data.
* `Cut.stair_of_rows`, `Cut.exists_rows`, `Cut.rows_unique`: its three parts.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Lemma I.2 (Section I.3), which Proposition J.2 of Appendix J applies; modules `Nc.Cut.Defs`,
  `Nc.Cut.Rows`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Cut

open Finset List.StairRefinement

variable {Γ : Type*} {A : ℕ}

/-- The row data of a party on a tape: whether the party writes nothing on the tape, and the
first and the last party that read what it writes. If it writes nothing, both are the last party
of the row before. -/
@[ext] structure RowData (A : ℕ) where
  /-- The party writes nothing on the tape. -/
  empty : Bool
  /-- The first party that reads what the party writes. -/
  first : Fin A
  /-- The last party that reads what the party writes. -/
  last : Fin A
deriving DecidableEq, Fintype

/-- The number of row data of `A` parties: a flag and two parties. -/
theorem RowData.card_eq (A : ℕ) : Fintype.card (RowData A) = 2 * (A * A) := by
  rw [Fintype.card_congr (β := Bool × Fin A × Fin A) ⟨fun d => (d.empty, d.first, d.last),
    fun ⟨e, f, l⟩ => ⟨e, f, l⟩, fun _ => rfl, fun _ => rfl⟩]
  simp

/-- The segments `X b` that a party writes on a tape for the parties `b` are as the row data
say: all are empty, or those for the first and for the last party are not empty and all others
that are not empty lie between them. -/
@[expose] def RowData.Ok (d : RowData A) (X : Fin A → List Γ) : Prop :=
  if d.empty then ∀ b, X b = []
  else X d.first ≠ [] ∧ X d.last ≠ [] ∧ ∀ b, X b ≠ [] → d.first ≤ b ∧ b ≤ d.last

instance (d : RowData A) (X : Fin A → List Γ) : Decidable (d.Ok X) :=
  inferInstanceAs (Decidable (if d.empty then _ else _))

/-- The last party of the row before row `p`, and `0` for the first row. -/
@[expose] def prevLast (ρ : Fin A → RowData A) (p : Fin A) : ℕ :=
  if h : p.1 = 0 then 0 else (ρ ⟨p.1 - 1, by omega⟩).last

/-- The row data of row `p` are those of a row of a staircase: an empty row repeats the last
party of the row before, and another row begins at that party or later. -/
@[expose] def ValidRow (ρ : Fin A → RowData A) (p : Fin A) : Prop :=
  if (ρ p).empty then (ρ p).first.1 = prevLast ρ p ∧ (ρ p).last.1 = prevLast ρ p
  else prevLast ρ p ≤ (ρ p).first ∧ (ρ p).first ≤ (ρ p).last

instance (ρ : Fin A → RowData A) (p : Fin A) : Decidable (ValidRow ρ p) :=
  inferInstanceAs (Decidable (if (ρ p).empty then _ else _))

/-- The row data on all tapes `s` are those of staircases. -/
@[expose] def ValidRows {σ : Type*} (ρ : σ → Fin A → RowData A) : Prop :=
  ∀ s p, ValidRow (ρ s) p

instance {σ : Type*} [Fintype σ] (ρ : σ → Fin A → RowData A) : Decidable (ValidRows ρ) :=
  inferInstanceAs (Decidable (∀ s p, ValidRow (ρ s) p))

/-- The last column that a row before row `q` uses, and `0` if there is none. -/
private def lastBefore (X : Fin A → Fin A → List Γ) (q : ℕ) : ℕ :=
  (univ.filter fun z : Fin A × Fin A => z.1 < q ∧ X z.1 z.2 ≠ []).sup fun z => z.2

private theorem lastBefore_le_iff {X : Fin A → Fin A → List Γ} {q c : ℕ} :
    lastBefore X q ≤ c ↔ ∀ p b, p.1 < q → X p b ≠ [] → b.1 ≤ c := by
  simp [lastBefore, Finset.sup_le_iff]

private theorem le_lastBefore {X : Fin A → Fin A → List Γ} {q : ℕ} {p b : Fin A} (hp : p.1 < q)
    (hb : X p b ≠ []) : b.1 ≤ lastBefore X q :=
  lastBefore_le_iff.1 le_rfl p b hp hb

private theorem lastBefore_lt (X : Fin A → Fin A → List Γ) (p : Fin A) (q : ℕ) :
    lastBefore X q < A :=
  (Finset.sup_lt_iff p.pos).2 fun z _ => z.2.2

/-- The row data of a matrix of words: a row that is not empty has its first and its last column
that are not empty, and an empty row has twice the last column that a row before it uses (`0` if
there is none). They are the valid row data that fit the rows if the matrix has staircase support
(`validRow_and_ok_iff`). -/
def rowsOf (X : Fin A → Fin A → List Γ) (p : Fin A) : RowData A :=
  if h : (univ.filter fun b => X p b ≠ []).Nonempty then ⟨false, min' _ h, max' _ h⟩
  else ⟨true, ⟨lastBefore X p, lastBefore_lt X p p⟩, ⟨lastBefore X p, lastBefore_lt X p p⟩⟩

private theorem ok_rowsOf (X : Fin A → Fin A → List Γ) (p : Fin A) : (rowsOf X p).Ok (X p) := by
  unfold rowsOf
  split_ifs with h
  · exact ⟨(mem_filter.1 (min'_mem _ h)).2, (mem_filter.1 (max'_mem _ h)).2,
      fun b hb => ⟨min'_le _ _ (by simpa using hb), le_max' _ _ (by simpa using hb)⟩⟩
  · simpa [RowData.Ok, Finset.Nonempty] using h

/-- The last party of the row before row `p` is the last column that a row before row `p` uses,
if the row data fit the rows and are valid before row `p`. -/
private theorem prevLast_eq {ρ : Fin A → RowData A} {X : Fin A → Fin A → List Γ}
    (hX : ∀ p, (ρ p).Ok (X p)) (p : Fin A) (h : ∀ p' < p, ValidRow ρ p') :
    prevLast ρ p = lastBefore X p := by
  obtain ⟨p, hp⟩ := p
  induction p with
  | zero => simp [prevLast, lastBefore]
  | succ q ih =>
    have hq : q < A := by omega
    have hv := h ⟨q, hq⟩ (Fin.mk_lt_mk.2 q.lt_succ_self)
    have hok := hX ⟨q, hq⟩
    simp only [ValidRow, ih hq fun p' hp' => h p' (hp'.trans (Fin.mk_lt_mk.2 q.lt_succ_self))]
      at hv
    simp only [RowData.Ok] at hok
    change prevLast ρ ⟨q + 1, hp⟩ = lastBefore X (q + 1)
    rw [show prevLast ρ ⟨q + 1, hp⟩ = (ρ ⟨q, hq⟩).last by simp [prevLast]]
    refine le_antisymm ?_ (lastBefore_le_iff.2 fun p' b hp' hb => ?_)
    · split_ifs at hv hok
      · exact hv.2.trans_le (lastBefore_le_iff.2 fun p' b hp' hb => le_lastBefore (by omega) hb)
      · exact le_lastBefore q.lt_succ_self hok.2.1
    · obtain hp' | rfl : p'.1 < q ∨ p'.1 = q := by omega
      · have := le_lastBefore hp' hb
        split_ifs at hv <;> omega
      · split_ifs at hok
        · exact absurd (hok b) hb
        · exact (hok.2.2 b hb).2

/-- Valid row data that fit the rows of a matrix imply that it has staircase support. -/
theorem stair_of_rows {ρ : Fin A → RowData A} (h : ∀ p, ValidRow ρ p)
    {X : Fin A → Fin A → List Γ} (hX : ∀ p, (ρ p).Ok (X p)) : Stair X := by
  intro a a' b b' hb hb' hlt
  have h1 := le_lastBefore (q := a') hlt hb
  rw [← prevLast_eq hX a' fun p _ => h p] at h1
  have hv := h a'
  have hok := hX a'
  simp only [ValidRow] at hv
  simp only [RowData.Ok] at hok
  split_ifs at hv hok
  · exact absurd (hok b') hb'
  · exact Fin.le_def.2 (h1.trans (hv.1.trans (hok.2.2 b' hb').1))

/-- Two valid families of row data that fit the rows of a matrix: one half of their equality. -/
private theorem row_le {ρ ρ' : Fin A → RowData A} {X : Fin A → Fin A → List Γ}
    (h : ∀ p, ValidRow ρ p) (h' : ∀ p, ValidRow ρ' p) (hX : ∀ p, (ρ p).Ok (X p))
    (hX' : ∀ p, (ρ' p).Ok (X p)) (p : Fin A) :
    (ρ p).empty = (ρ' p).empty ∧ (ρ p).first ≤ (ρ' p).first ∧ (ρ' p).last ≤ (ρ p).last := by
  have v := h p
  have v' := h' p
  have r := hX p
  have r' := hX' p
  simp only [ValidRow, prevLast_eq hX p fun p' _ => h p',
    prevLast_eq hX' p fun p' _ => h' p'] at v v'
  simp only [RowData.Ok] at r r'
  cases e : (ρ p).empty <;> cases e' : (ρ' p).empty <;>
    simp only [e, e', Bool.false_eq_true, ↓reduceIte] at v v' r r'
  · exact ⟨rfl, (r.2.2 _ r'.1).1, (r.2.2 _ r'.2.1).2⟩
  · exact absurd (r' _) r.1
  · exact absurd (r _) r'.1
  · exact ⟨rfl, Fin.le_def.2 (by omega), Fin.le_def.2 (by omega)⟩

/-- Valid row data that fit the rows of a matrix are determined by the matrix. -/
theorem rows_unique {X : Fin A → Fin A → List Γ} {ρ ρ' : Fin A → RowData A}
    (h : ∀ p, ValidRow ρ p) (h' : ∀ p, ValidRow ρ' p) (hX : ∀ p, (ρ p).Ok (X p))
    (hX' : ∀ p, (ρ' p).Ok (X p)) : ρ = ρ' := funext fun p => by
  obtain ⟨e, f, l⟩ := row_le h h' hX hX' p
  obtain ⟨-, f', l'⟩ := row_le h' h hX' hX p
  exact RowData.ext e (le_antisymm f f') (le_antisymm l' l)

private theorem validRow_rowsOf {X : Fin A → Fin A → List Γ} (hX : Stair X) (p : Fin A) :
    ValidRow (rowsOf X) p := by
  induction p using WellFoundedLT.induction with | _ p ih
  have hok := ok_rowsOf X p
  rw [ValidRow, prevLast_eq (ok_rowsOf X) p ih]
  by_cases hne : (univ.filter fun b => X p b ≠ []).Nonempty
  · simp only [RowData.Ok, show (rowsOf X p).empty = false by rw [rowsOf, dite_eq_left hne],
      Bool.false_eq_true, ite_false] at hok ⊢
    exact ⟨lastBefore_le_iff.2 fun p' b hp' hb => hX p' p b _ hb hok.1 hp',
      (hok.2.2 _ hok.1).2⟩
  · simp [rowsOf, dite_eq_right hne]

/-- **Row data of a staircase.** Row data are valid and fit the rows of a matrix of words if and
only if the matrix has staircase support and they are the row data of the matrix. -/
theorem validRow_and_ok_iff {ρ : Fin A → RowData A} {X : Fin A → Fin A → List Γ} :
    ((∀ p, ValidRow ρ p) ∧ ∀ p, (ρ p).Ok (X p)) ↔ Stair X ∧ ρ = rowsOf X := by
  refine ⟨fun ⟨h, hX⟩ => ⟨stair_of_rows h hX,
    rows_unique h (validRow_rowsOf (stair_of_rows h hX)) hX (ok_rowsOf X)⟩, ?_⟩
  rintro ⟨hX, rfl⟩
  exact ⟨validRow_rowsOf hX, ok_rowsOf X⟩

/-- A matrix of words with staircase support has valid row data that fit its rows. -/
theorem exists_rows {X : Fin A → Fin A → List Γ} (hX : Stair X) :
    ∃ ρ : Fin A → RowData A, (∀ p, ValidRow ρ p) ∧ ∀ p, (ρ p).Ok (X p) :=
  ⟨rowsOf X, validRow_and_ok_iff.2 ⟨hX, rfl⟩⟩

end Cslib.Circuits.Arithmetic.Separation.Cut
