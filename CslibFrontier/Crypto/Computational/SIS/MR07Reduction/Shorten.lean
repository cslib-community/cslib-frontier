/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.LinearAlgebra.BareissElimination
public import CslibFrontier.Computability.Circuit.Rational.Runtime.Determinant
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Computability.PolyTime.LinearAlgebra.RationalElimination
public import CslibFrontier.Crypto.Computational.Lattice.MR07Shorten
public import CslibFrontier.Crypto.Computational.SIS.MR07Core
public import CslibFrontier.Foundations.Data.List.DotProduct
public import CslibFrontier.Foundations.Data.Matrix.RowTable

import Mathlib.Data.List.GetD

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.PolyTime.Int.DotProduct
import CslibFrontier.Computability.PolyTime.Int.Table

/-!
# Strict-PPT Basis Shortening Helpers for the Micciancio–Regev Reduction

Executable polynomial-time implementations on row-major `IntTable`s of the deterministic basis
shortening primitives in `CslibFrontier.Crypto.Computational.Lattice.MR07Shorten` (supporting
the finite-parameter reduction step toward `[MicciancioRegev2007]` Lemma 5.10, p. 24):

* Row-major `IntTable` column helpers (`intTableCol`, `intTableColSqNorm`, `intTableMaxColSqNorm`,
  `intTableMaxSqNormIdx`) matching `MR07Shorten.maxSqNormIndex`.
* Denominator-clearing exact rational squared norm (`sqNormRatList`) reusing
  `BareissElimination.{rowDenomProd, clearRow}`, and strict-PPT rational orthogonal target
  `ratOrthoTargetIntTable` matching `MR07Shorten.ratOrthoTarget`.
* Strict-PPT guarded column update `guardedUpdateIntTable` (using Bird's staged determinant
  `detRows_polytime`) preserving unconditional well-formedness and column-norm bounds and
  matching `MR07Shorten.shortenGuardedStep` column-by-column.
* Cubic `IntTable.enc` encoding-length bound `length_intTableEnc_le_of_colSqNorm_le` for
  `IsPPTOn.iterateWith_spec`.
-/

public section

namespace Cslib.Crypto.SIS.MR07

open Cslib Cslib.LinearAlgebra Cslib.Crypto Cslib.Crypto.MR07Shorten Mathlib.Tactic.Matrix
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open scoped Cslib.LinearAlgebra.IntTable Cslib.LinearAlgebra.RatTable
open scoped BigOperators _root_.Matrix RealInnerProductSpace

attribute [local irreducible] encRat encIntBin encNat encUnary IntTable.enc RatTable.enc

private theorem cpt_eq {α β : Type} {e₁ : α ↪ List Bool} {e₂ : β ↪ List Bool}
    {f g : α → β} (h : ComputableInPolyTime f e₁ e₂) (heq : ∀ x, f x = g x) :
    ComputableInPolyTime g e₁ e₂ := by
  rwa [show g = f from funext fun x => (heq x).symm]

private theorem cpt_comp2 {α β₁ β₂ γ : Type}
    {eA : α ↪ List Bool} {e₁ : β₁ ↪ List Bool} {e₂ : β₂ ↪ List Bool} {eC : γ ↪ List Bool}
    {h : β₁ → β₂ → γ} {f : α → β₁} {g : α → β₂}
    (hh : ComputableInPolyTime (fun p : β₁ × β₂ => h p.1 p.2) (encPair e₁ e₂) eC)
    (hf : ComputableInPolyTime f eA e₁) (hg : ComputableInPolyTime g eA e₂) :
    ComputableInPolyTime (fun a => h (f a) (g a)) eA eC :=
  hh.comp (hf.prod hg)

private theorem cpt_comp3 {α β₁ β₂ β₃ γ : Type}
    {eA : α ↪ List Bool} {e₁ : β₁ ↪ List Bool} {e₂ : β₂ ↪ List Bool}
    {e₃ : β₃ ↪ List Bool} {eC : γ ↪ List Bool}
    {h : β₁ → β₂ → β₃ → γ} {f₁ : α → β₁} {f₂ : α → β₂} {f₃ : α → β₃}
    (hh : ComputableInPolyTime (fun p : (β₁ × β₂) × β₃ => h p.1.1 p.1.2 p.2)
      (encPair (encPair e₁ e₂) e₃) eC)
    (hf₁ : ComputableInPolyTime f₁ eA e₁) (hf₂ : ComputableInPolyTime f₂ eA e₂)
    (hf₃ : ComputableInPolyTime f₃ eA e₃) :
    ComputableInPolyTime (fun a => h (f₁ a) (f₂ a) (f₃ a)) eA eC :=
  hh.comp ((hf₁.prod hf₂).prod hf₃)

private theorem list_sum_map_range_eq_sum_fin {α : Type*} [AddCommMonoid α] (n : ℕ) (f : ℕ → α) :
    ((List.range n).map f).sum = ∑ k : Fin n, f k.val := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      ih, Fin.sum_univ_castSucc]
    rfl

private theorem list_sum_nonneg_of_forall {l : List ℤ} (h : ∀ x ∈ l, 0 ≤ x) : 0 ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.sum_cons]
    exact add_nonneg (h a List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem a hx))

private theorem list_mem_le_sum_nat {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => simp at hx
  | cons a rest ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | hrest
    · omega
    · have := ih hrest; omega

private theorem list_sum_le_length_mul_nat {l : List ℕ} {B : ℕ} (h : ∀ x ∈ l, x ≤ B) :
    l.sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.sum_cons, List.length_cons]
    have ha := h a List.mem_cons_self
    have hrest := ih fun x hx => h x (List.mem_cons_of_mem a hx)
    nlinarith

private theorem foldl_max_le_nat (l : List ℕ) (f : ℕ → ℕ) (a B : ℕ) (ha : a ≤ B)
    (hf : ∀ x ∈ l, f x ≤ B) :
    l.foldl (fun acc j => max acc (f j)) a ≤ B := by
  induction l generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih _ (max_le ha (hf x List.mem_cons_self)) fun y hy => hf y (List.mem_cons_of_mem x hy)

/-! ### 1. Row-major `IntTable` column helpers and `RowTable.ofMatrix` bridge -/

/-- A well-formed `n × n` `IntTable` equals `RowTable.ofMatrix` of its entry matrix. -/
theorem intTable_eq_ofMatrix_of_wellFormed {n : ℕ} (T : IntTable)
    (hr : T.numRows = n) (hc : T.numCols = n) (hwf : T.WellFormed) :
    T = RowTable.ofMatrix (Matrix.of fun i j : Fin n => T.entry i.val j.val) :=
  RowTable.eq_of_wellFormed_of_entry_eq hwf (RowTable.wellFormed_ofMatrix _) hr hc
    fun i hi j hj => by
      rw [RowTable.entry_ofMatrix_of_lt _ (hr ▸ hi) (hc ▸ hj), Matrix.of_apply]

/-- Column `j` of a row-major `IntTable`, matching `MR07.intCol T.toMatrix`. -/
def intTableCol (T : IntTable) (j : ℕ) : List ℤ :=
  (List.range T.numRows).map fun i => T.entry i j

/-- Exact squared Euclidean norm of column `j` of `T` (as `ℕ`). -/
def intTableColSqNorm (T : IntTable) (j : ℕ) : ℕ :=
  let c := intTableCol T j
  (ListMatrix.dotProduct T.numRows c c).natAbs

/-- Maximum squared column norm across all columns `j < T.numCols` (as `ℕ`). -/
def intTableMaxColSqNorm (T : IntTable) : ℕ :=
  (List.range T.numCols).foldl (fun acc j => max acc (intTableColSqNorm T j)) 0

/-- Column index `iStar < T.numCols` maximizing squared Euclidean column norm. -/
def intTableMaxSqNormIdx (T : IntTable) : ℕ :=
  (List.range T.numCols).foldl
    (fun best j => if intTableColSqNorm T best < intTableColSqNorm T j then j else best) 0

/-- `intTableColSqNorm T j` equals the sum of squared `natAbs` entries in column `j`. -/
theorem intTableColSqNorm_eq_sum_sq (T : IntTable) (j : ℕ) :
    intTableColSqNorm T j = ((List.range T.numRows).map fun i => (T.entry i j).natAbs ^ 2).sum := by
  dsimp only [intTableColSqNorm]
  rw [ListMatrix.dotProduct_eq_sum_map_range]
  have hget : ∀ i < T.numRows, (intTableCol T j).getD i 0 = T.entry i j := fun i hi => by
    have hlen : i < (intTableCol T j).length := by simp [intTableCol, hi]
    rw [List.getD_eq_getElem _ _ hlen]
    simp [intTableCol]
  have hmap_eq :
      ((List.range T.numRows).map fun i =>
        (intTableCol T j).getD i 0 * (intTableCol T j).getD i 0) =
      ((List.range T.numRows).map fun i => (((T.entry i j).natAbs ^ 2 : ℕ) : ℤ)) := by
    refine List.map_congr_left fun i hi => ?_
    rw [hget i (List.mem_range.mp hi), Nat.cast_pow, sq, Int.natAbs_mul_self']
  rw [hmap_eq]
  have hsum_cast :
      (((List.range T.numRows).map fun i => (((T.entry i j).natAbs ^ 2 : ℕ) : ℤ)).sum) =
      ((((List.range T.numRows).map fun i => (T.entry i j).natAbs ^ 2).sum : ℕ) : ℤ) := by
    rw [list_sum_map_range_eq_sum_fin, list_sum_map_range_eq_sum_fin, Nat.cast_sum]
  rw [hsum_cast, Int.natAbs_natCast]

/-- Every column squared norm `j < T.numCols` is at most `intTableMaxColSqNorm T`. -/
theorem intTableColSqNorm_le_max (T : IntTable) {j : ℕ} (hj : j < T.numCols) :
    intTableColSqNorm T j ≤ intTableMaxColSqNorm T := by
  have hfold : ∀ (l : List ℕ) (a : ℕ),
      a ≤ l.foldl (fun acc k => max acc (intTableColSqNorm T k)) a ∧
      ∀ x ∈ l,
        intTableColSqNorm T x ≤ l.foldl (fun acc k => max acc (intTableColSqNorm T k)) a := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons y ys ih =>
      intro a
      simp only [List.foldl_cons]
      obtain ⟨h1, h2⟩ := ih (max a (intTableColSqNorm T y))
      refine ⟨(le_max_left _ _).trans h1, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact (le_max_right _ _).trans h1
      · exact h2 x hmem
  exact (hfold (List.range T.numCols) 0).2 j (List.mem_range.mpr hj)

/-- `intTableMaxColSqNorm T` is at most `B` whenever every column squared norm is at most `B`. -/
theorem intTableMaxColSqNorm_le (T : IntTable) {B : ℕ}
    (h : ∀ j < T.numCols, intTableColSqNorm T j ≤ B) :
    intTableMaxColSqNorm T ≤ B :=
  foldl_max_le_nat (List.range T.numCols) (intTableColSqNorm T) 0 B (Nat.zero_le B)
    fun j hj => h j (List.mem_range.mp hj)

/-- For any nonempty-column table `T`, `intTableMaxSqNormIdx T < T.numCols`. -/
theorem intTableMaxSqNormIdx_lt (T : IntTable) (hpos : 0 < T.numCols) :
    intTableMaxSqNormIdx T < T.numCols := by
  have hfold : ∀ (l : List ℕ) (a : ℕ), a < T.numCols → (∀ x ∈ l, x < T.numCols) →
      l.foldl
        (fun best j => if intTableColSqNorm T best < intTableColSqNorm T j then j else best) a <
        T.numCols := by
    intro l
    induction l with
    | nil => intro a ha _; exact ha
    | cons x xs ih =>
      intro a ha hall
      simp only [List.foldl_cons]
      refine ih _ ?_ fun y hy => hall y (List.mem_cons_of_mem x hy)
      split_ifs
      · exact hall x List.mem_cons_self
      · exact ha
  exact hfold (List.range T.numCols) 0 hpos fun x hx => List.mem_range.mp hx

@[local fun_prop]
private theorem computableInPolyTime_intTableEntry :
    ComputableInPolyTime (fun p : (IntTable × ℕ) × ℕ => p.1.1.entry p.1.2 p.2)
      (encPair (encPair IntTable.enc encUnary) encUnary) encIntBin := by
  change ComputableInPolyTime (fun p : (IntTable × ℕ) × ℕ => Cslib.rowEntry p.1.1.rows p.1.2 p.2)
    (encPair (encPair IntTable.enc encUnary) encUnary) encIntBin
  exact computableInPolyTime_rowEntry (by fun_prop) (by fun_prop) (by fun_prop)

/-- Polynomial-time certificate for extracting column `j` of a row-major `IntTable`. -/
theorem computableInPolyTime_intTableCol :
    ComputableInPolyTime (fun p : IntTable × ℕ => intTableCol p.1 p.2)
      (encPair IntTable.enc encUnary) (encList encIntBin) := by
  unfold intTableCol
  have hrange : ComputableInPolyTime (fun p : IntTable × ℕ => List.range p.1.numRows)
      (encPair IntTable.enc encUnary) (encList encUnary) := by fun_prop
  have hbody : ComputableInPolyTime (fun q : (IntTable × ℕ) × ℕ => q.1.1.entry q.2 q.1.2)
      (encPair (encPair IntTable.enc encUnary) encUnary) encIntBin :=
    computableInPolyTime_intTableEntry.comp
      (by fun_prop : ComputableInPolyTime (fun q : (IntTable × ℕ) × ℕ => ((q.1.1, q.2), q.1.2))
        (encPair (encPair IntTable.enc encUnary) encUnary)
        (encPair (encPair IntTable.enc encUnary) encUnary))
  exact ComputableInPolyTime.mapWithInput hrange hbody

/-- Polynomial-time certificate for `intTableColSqNorm`. -/
theorem computableInPolyTime_intTableColSqNorm :
    ComputableInPolyTime (fun p : IntTable × ℕ => intTableColSqNorm p.1 p.2)
      (encPair IntTable.enc encUnary) encNat := by
  unfold intTableColSqNorm
  have hnr : ComputableInPolyTime (fun p : IntTable × ℕ => p.1.numRows)
      (encPair IntTable.enc encUnary) encUnary := by fun_prop
  have hdot : ComputableInPolyTime
      (fun p : IntTable × ℕ =>
        ListMatrix.dotProduct p.1.numRows (intTableCol p.1 p.2) (intTableCol p.1 p.2))
      (encPair IntTable.enc encUnary) encIntBin :=
    listDotProduct.comp
      (hnr.prod (computableInPolyTime_intTableCol.prod computableInPolyTime_intTableCol))
  exact intBin_natAbs.comp hdot

private theorem length_intTableEnc_eq (T : IntTable) :
    (IntTable.enc T).length =
      2 * T.numRows + 1 + (2 * T.numCols + 1 + (encList (encList encIntBin) T.rows).length) := by
  rw [IntTable.enc_apply, length_encPair, length_encPair, encUnary_apply, List.length_replicate,
    encUnary_apply, List.length_replicate]

private theorem natAbs_entry_lt_two_pow_enc (T : IntTable) (i j : ℕ) :
    (T.entry i j).natAbs < 2 ^ (IntTable.enc T).length := by
  set L := (IntTable.enc T).length
  have hL_eq : L =
      2 * T.numRows + 1 + (2 * T.numCols + 1 + (encList (encList encIntBin) T.rows).length) :=
    length_intTableEnc_eq T
  have hrows_le : (encList (encList encIntBin) T.rows).length ≤ L := by omega
  unfold RowTable.entry
  by_cases hi : i < T.rows.length
  · rw [List.getD_eq_getElem _ _ hi]
    by_cases hj : j < T.rows[i].length
    · rw [List.getD_eq_getElem _ _ hj]
      have hmem_row : T.rows[i] ∈ T.rows := List.getElem_mem hi
      have hmem_z : T.rows[i][j] ∈ T.rows[i] := List.getElem_mem hj
      have hlen_z : (encIntBin T.rows[i][j]).length ≤ (encList encIntBin T.rows[i]).length :=
        SizedListEncoding.length_elem_le T.rows[i] _ hmem_z
      have hlen_r :
          (encList encIntBin T.rows[i]).length ≤ (encList (encList encIntBin) T.rows).length :=
        SizedListEncoding.length_elem_le T.rows _ hmem_row
      rw [length_encIntBin] at hlen_z
      have hsize : T.rows[i][j].natAbs.size ≤ L := by omega
      exact (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) hsize)
    · rw [List.getD_eq_default _ _ (by omega)]; simp
  · rw [List.getD_eq_default T.rows [] (by omega), List.getD_nil]; simp

private theorem intTableColSqNorm_le_numRows_mul_two_pow (T : IntTable) (j : ℕ) :
    intTableColSqNorm T j ≤ T.numRows * 2 ^ (2 * (IntTable.enc T).length) := by
  set L := (IntTable.enc T).length
  rw [intTableColSqNorm_eq_sum_sq]
  refine (list_sum_le_length_mul_nat (B := 2 ^ (2 * L)) fun x hx => ?_).trans (by simp)
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  have habs := natAbs_entry_lt_two_pow_enc T i j
  have hsq : (T.entry i j).natAbs ^ 2 ≤ (2 ^ L) ^ 2 := Nat.pow_le_pow_left habs.le 2
  simpa only [← pow_mul, mul_comm L 2] using hsq

private theorem intTableColSqNorm_lt_two_pow (T : IntTable) (j : ℕ) :
    intTableColSqNorm T j < 2 ^ (3 * (IntTable.enc T).length + 1) := by
  set L := (IntTable.enc T).length
  have hL_eq : L =
      2 * T.numRows + 1 + (2 * T.numCols + 1 + (encList (encList encIntBin) T.rows).length) :=
    length_intTableEnc_eq T
  have hnr_le : T.numRows ≤ L := by omega
  have h1 := intTableColSqNorm_le_numRows_mul_two_pow T j
  have hnr_lt : T.numRows < 2 ^ (L + 1) :=
    hnr_le.trans_lt (Nat.lt_two_pow_self.trans
      (Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self L)))
  have hmul : T.numRows * 2 ^ (2 * L) < 2 ^ (L + 1) * 2 ^ (2 * L) :=
    Nat.mul_lt_mul_of_pos_right hnr_lt (Nat.two_pow_pos _)
  have hpow : 2 ^ (L + 1) * 2 ^ (2 * L) = 2 ^ (3 * L + 1) := by
    rw [← pow_add]; congr 1; omega
  exact h1.trans_lt (hpow ▸ hmul)

private theorem computableInPolyTime_intTableColsFoldl {β : Type} {encB : β ↪ List Bool}
    (init : β) (step : IntTable → β → ℕ → β) (B : IntTable → ℕ)
    (hstep : ComputableInPolyTime (fun q : (IntTable × β) × ℕ => step q.1.1 q.1.2 q.2)
      (encPair (encPair IntTable.enc encB) encUnary) encB)
    (hB : PolyBounded (fun T : IntTable => (IntTable.enc T).length) B)
    (hbound : ∀ T i, i ≤ (List.range T.numCols).length →
      (encB (((List.range T.numCols).take i).foldl (step T) init)).length ≤ B T) :
    ComputableInPolyTime (fun T : IntTable => (List.range T.numCols).foldl (step T) init)
      IntTable.enc encB :=
  ComputableInPolyTime.foldlWith (encA := encUnary) (encB := encB) (encL := encList encUnary)
    (encP := IntTable.enc) (par := id) (list := fun T => List.range T.numCols)
    (init := fun _ => init) (step := step) (by fun_prop) (by fun_prop) (.const init)
    hstep hB hbound

private theorem computableInPolyTime_intTableStepColSqNorm {β : Type} (encB : β ↪ List Bool) :
    ComputableInPolyTime (fun q : (IntTable × β) × ℕ => intTableColSqNorm q.1.1 q.2)
      (encPair (encPair IntTable.enc encB) encUnary) encNat :=
  computableInPolyTime_intTableColSqNorm.comp
    (((fst IntTable.enc encB).comp (fst _ _)).prod (snd _ _))

/-- Polynomial-time certificate for `intTableMaxColSqNorm`. -/
theorem computableInPolyTime_intTableMaxColSqNorm :
    ComputableInPolyTime intTableMaxColSqNorm IntTable.enc encNat := by
  have hstep : ComputableInPolyTime
      (fun q : (IntTable × ℕ) × ℕ => max q.1.2 (intTableColSqNorm q.1.1 q.2))
      (encPair (encPair IntTable.enc encNat) encUnary) encNat := by
    have hacc : ComputableInPolyTime (fun q : (IntTable × ℕ) × ℕ => q.1.2)
        (encPair (encPair IntTable.enc encNat) encUnary) encNat := by fun_prop
    have hcol := computableInPolyTime_intTableStepColSqNorm encNat
    exact cpt_eq ((binary_lt' hacc hcol).ite_decide hcol hacc) fun q => by
      by_cases h : q.1.2 < intTableColSqNorm q.1.1 q.2
      · simp [h, max_eq_right h.le]
      · simp [h, max_eq_left (Nat.le_of_not_lt h)]
  refine computableInPolyTime_intTableColsFoldl (encB := encNat) 0
    (fun T acc j => max acc (intTableColSqNorm T j))
    (fun T => 3 * (IntTable.enc T).length + 1) hstep
    (PolyBounded.of_forall_le 3 1 fun T => by simp) fun T i _ => ?_
  have hlt_fold : ∀ (l : List ℕ) (a : ℕ), a < 2 ^ (3 * (IntTable.enc T).length + 1) →
      l.foldl (fun acc j => max acc (intTableColSqNorm T j)) a <
        2 ^ (3 * (IntTable.enc T).length + 1) := by
    intro l
    induction l with
    | nil => intro a ha; exact ha
    | cons x xs ih =>
      intro a ha
      simp only [List.foldl_cons]
      exact ih _ (max_lt ha (intTableColSqNorm_lt_two_pow T x))
  exact length_encNat_le_of_lt_two_pow
    (hlt_fold ((List.range T.numCols).take i) 0 (Nat.pow_pos (by decide : 0 < 2)))

/-- Polynomial-time certificate for `intTableMaxSqNormIdx`. -/
theorem computableInPolyTime_intTableMaxSqNormIdx :
    ComputableInPolyTime intTableMaxSqNormIdx IntTable.enc encUnary := by
  have hstep : ComputableInPolyTime
      (fun q : (IntTable × ℕ) × ℕ =>
        if intTableColSqNorm q.1.1 q.1.2 < intTableColSqNorm q.1.1 q.2 then q.2 else q.1.2)
      (encPair (encPair IntTable.enc encUnary) encUnary) encUnary := by
    have hbest : ComputableInPolyTime (fun q : (IntTable × ℕ) × ℕ => intTableColSqNorm q.1.1 q.1.2)
        (encPair (encPair IntTable.enc encUnary) encUnary) encNat :=
      computableInPolyTime_intTableColSqNorm.comp (fst _ _)
    have hj := computableInPolyTime_intTableStepColSqNorm encUnary
    exact (binary_lt' hbest hj).ite_decide (snd _ _) ((snd IntTable.enc encUnary).comp (fst _ _))
  refine computableInPolyTime_intTableColsFoldl (encB := encUnary) 0
    (fun T best j => if intTableColSqNorm T best < intTableColSqNorm T j then j else best)
    (fun T => (IntTable.enc T).length) hstep
    (PolyBounded.of_forall_le 1 1 fun T => by simp) fun T i _ => ?_
  have hle_fold : ∀ (l : List ℕ) (a : ℕ), a ≤ T.numCols → (∀ x ∈ l, x ≤ T.numCols) →
      l.foldl
        (fun best j => if intTableColSqNorm T best < intTableColSqNorm T j then j else best)
        a ≤ T.numCols := by
    intro l
    induction l with
    | nil => intro a ha _; exact ha
    | cons x xs ih =>
      intro a ha hall
      simp only [List.foldl_cons]
      refine ih _ ?_ fun y hy => hall y (List.mem_cons_of_mem x hy)
      split_ifs
      · exact hall x List.mem_cons_self
      · exact ha
  have hres_le : ((List.range T.numCols).take i).foldl
      (fun best j => if intTableColSqNorm T best < intTableColSqNorm T j then j else best) 0 ≤
      T.numCols :=
    hle_fold _ 0 (Nat.zero_le _) fun x hx => (List.mem_range.mp (List.mem_of_mem_take hx)).le
  have hnc_le : T.numCols ≤ (IntTable.enc T).length := by
    have hL := length_intTableEnc_eq T; omega
  simpa [encUnary_apply] using hres_le.trans hnc_le

/-- Exact cast equality between `intTableColSqNorm T j` and `MR07Shorten.sqNormRat`. -/
theorem intTableColSqNorm_cast_eq_sqNormRat {m : ℕ} (T : IntTable)
    (hr : T.numRows = m + 1) (j : Fin (m + 1)) :
    ((intTableColSqNorm T j.val : ℕ) : ℚ) =
      MR07Shorten.sqNormRat (fun k : Fin (m + 1) => (T.entry k.val j.val : ℚ)) := by
  rw [intTableColSqNorm_eq_sum_sq, hr, list_sum_map_range_eq_sum_fin, Nat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Int.cast_natCast, Nat.cast_pow, Int.natAbs_sq, Int.cast_pow]

/-- Exact real cast equality between `intTableColSqNorm T j` and `‖intCol TMat j‖²`. -/
theorem intTableColSqNorm_cast_eq_norm_sq {n : ℕ} (T : IntTable)
    (hr : T.numRows = n) (j : Fin n) :
    ((intTableColSqNorm T j.val : ℕ) : ℝ) =
      ‖intCol (Matrix.of fun i k : Fin n => T.entry i.val k.val) j‖ ^ 2 := by
  rw [intTableColSqNorm_eq_sum_sq, hr, list_sum_map_range_eq_sum_fin, Nat.cast_sum,
    EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [intCol, Real.norm_eq_abs, sq]

/-- Exact equality between executable `intTableMaxSqNormIdx T` and `MR07Shorten.maxSqNormIndex`. -/
theorem intTableMaxSqNormIdx_eq_maxSqNormIndex {m : ℕ} (T : IntTable)
    (hr : T.numRows = m + 1) (hc : T.numCols = m + 1) :
    intTableMaxSqNormIdx T =
      (MR07Shorten.maxSqNormIndex
        (fun j k : Fin (m + 1) => (T.entry k.val j.val : ℚ))).val := by
  let S : Fin (m + 1) → Fin (m + 1) → ℚ := fun j k => (T.entry k.val j.val : ℚ)
  have hfold_eq : ∀ (l : List (Fin (m + 1))) (init : Fin (m + 1)),
      (l.map Fin.val).foldl
        (fun best j => if intTableColSqNorm T best < intTableColSqNorm T j then j else best)
        init.val =
      (l.foldl
        (fun best j =>
          if MR07Shorten.sqNormRat (S best) < MR07Shorten.sqNormRat (S j) then j else best)
        init).val := by
    intro l
    induction l with
    | nil => intro init; rfl
    | cons j rest ih =>
      intro init
      simp only [List.map_cons, List.foldl_cons]
      have hcmp : (intTableColSqNorm T init.val < intTableColSqNorm T j.val) ↔
          (MR07Shorten.sqNormRat (S init) < MR07Shorten.sqNormRat (S j)) := by
        rw [← Nat.cast_lt (α := ℚ), intTableColSqNorm_cast_eq_sqNormRat T hr init,
          intTableColSqNorm_cast_eq_sqNormRat T hr j]
      by_cases h : intTableColSqNorm T init.val < intTableColSqNorm T j.val
      · have h' : MR07Shorten.sqNormRat (S init) < MR07Shorten.sqNormRat (S j) := hcmp.mp h
        simp only [h, h', ↓reduceIte]
        exact ih j
      · have h' : ¬ MR07Shorten.sqNormRat (S init) < MR07Shorten.sqNormRat (S j) :=
          fun hc' => h (hcmp.mpr hc')
        simp only [h, h', ↓reduceIte]
        exact ih init
  have hmap_finRange : (List.finRange (m + 1)).map Fin.val = List.range (m + 1) := by
    apply List.ext_getElem <;> simp
  dsimp only [intTableMaxSqNormIdx, MR07Shorten.maxSqNormIndex]
  rw [hc, ← hmap_finRange]
  exact hfold_eq (List.finRange (m + 1)) 0

/-! ### 2. Strict-PPT `ratOrthoTargetIntTable` matching `MR07Shorten.ratOrthoTarget` -/

/-- Direct `ComputableInPolyTime` certificate for `MR07Shorten.ratOrthoScale`. -/
theorem computableInPolyTime_ratOrthoScale :
    ComputableInPolyTime (fun p : ℚ × ℚ => MR07Shorten.ratOrthoScale p.1 p.2)
      (encPair encRat encRat) encRat := by
  unfold MR07Shorten.ratOrthoScale
  have hq : ComputableInPolyTime (fun p : ℚ × ℚ => p.1 / p.2) (encPair encRat encRat) encRat :=
    rat_div' (fst encRat encRat) (snd encRat encRat)
  have hp : ComputableInPolyTime (fun p : ℚ × ℚ => (p.1 / p.2).num.toNat)
      (encPair encRat encRat) encNat := by
    have hnum : ComputableInPolyTime (fun p : ℚ × ℚ => (p.1 / p.2).num)
        (encPair encRat encRat) encIntBin := rat_num.comp hq
    have hneg : ComputableInPolyTime (fun p : ℚ × ℚ => decide ((p.1 / p.2).num < 0))
        (encPair encRat encRat) encBool := intBin_isNeg.comp hnum
    have habs : ComputableInPolyTime (fun p : ℚ × ℚ => (p.1 / p.2).num.natAbs)
        (encPair encRat encRat) encNat := intBin_natAbs.comp hnum
    exact cpt_eq (hneg.ite_decide (.const 0) habs) fun p => by
      by_cases h : (p.1 / p.2).num < 0
      · simp [h, Int.toNat_of_nonpos h.le]
      · simp only [h, ↓reduceIte]
        have hnn : 0 ≤ (p.1 / p.2).num := Int.not_lt.mp h
        omega
  have hd : ComputableInPolyTime (fun p : ℚ × ℚ => (p.1 / p.2).den)
      (encPair encRat encRat) encNat := rat_den.comp hq
  have hnum_nat : ComputableInPolyTime
      (fun p : ℚ × ℚ => Nat.sqrt (64 * (p.1 / p.2).num.toNat * (p.1 / p.2).den) + 1)
      (encPair encRat encRat) encNat := by
    have hprod : ComputableInPolyTime
        (fun p : ℚ × ℚ => 64 * (p.1 / p.2).num.toNat * (p.1 / p.2).den)
        (encPair encRat encRat) encNat :=
      binary_mul' (binary_mul' (.const 64) hp) hd
    exact binary_add' (binary_sqrt' hprod) (.const 1)
  have hnum_q : ComputableInPolyTime
      (fun p : ℚ × ℚ => ((Nat.sqrt (64 * (p.1 / p.2).num.toNat * (p.1 / p.2).den) + 1 : ℕ) : ℚ))
      (encPair encRat encRat) encRat :=
    cpt_eq (rat_intCast.comp (intBin_natCast.comp hnum_nat)) fun _ => by simp
  have hden_q : ComputableInPolyTime (fun p : ℚ × ℚ => 16 * ((p.1 / p.2).den : ℚ))
      (encPair encRat encRat) encRat :=
    rat_mul' (.const 16) (cpt_eq (rat_intCast.comp (intBin_natCast.comp hd)) fun _ => by simp)
  exact rat_div' hnum_q hden_q

private theorem rowDenomProd_cons (q : ℚ) (qs : List ℚ) :
    rowDenomProd (q :: qs) = q.den * rowDenomProd qs := by
  have hfold : ∀ (l : List ℚ) (a : ℕ),
      l.foldl (fun acc x => acc * x.den) a = a * rowDenomProd l := by
    intro l
    induction l with
    | nil => intro a; simp [rowDenomProd]
    | cons x xs ih =>
      intro a
      simp only [rowDenomProd, List.foldl_cons, one_mul]
      rw [ih (a * x.den), ih x.den, mul_assoc]
  simpa only [rowDenomProd, List.foldl_cons, one_mul] using hfold qs q.den

private theorem rowDenomProd_lt_two_pow (v : List ℚ) :
    rowDenomProd v < 2 ^ ((encList encRat v).length + 1) := by
  induction v with
  | nil => simp [rowDenomProd]
  | cons q qs ih =>
    rw [rowDenomProd_cons]
    have hmul := Nat.mul_lt_mul_of_lt_of_lt (den_lt_two_pow_length_encRat q) ih
    rw [← pow_add] at hmul
    refine hmul.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) ?_)
    simp only [encList_cons, List.length_append, length_frame]; omega

/-- Polynomial-time certificate for `BareissElimination.rowDenomProd`. -/
theorem computableInPolyTime_rowDenomProd :
    ComputableInPolyTime rowDenomProd (encList encRat) encNat := by
  have hstep : ComputableInPolyTime (fun p : ℕ × ℚ => p.1 * p.2.den)
      (encPair encNat encRat) encNat := by fun_prop
  have hB : PolyBounded (fun t : List ℚ => (encList encRat t).length)
      (fun t => (encList encRat t).length + 1) :=
    PolyBounded.of_forall_le 1 1 fun t => by simp
  refine ComputableInPolyTime.foldl' (encA := encRat) (encB := encNat) (encL := encList encRat)
    (list := id) (init := fun _ => 1) (step := fun acc q => acc * q.den)
    (by fun_prop) (.const 1) hstep hB fun t i _ => ?_
  have hsub := length_encList_sublist encRat (List.take_sublist i t)
  exact length_encNat_le_of_lt_two_pow ((rowDenomProd_lt_two_pow (t.take i)).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.add_le_add_right hsub 1)))

/-- Polynomial-time certificate for `BareissElimination.clearRow`. -/
theorem computableInPolyTime_clearRow :
    ComputableInPolyTime clearRow (encList encRat) (encList encIntBin) := by
  unfold clearRow
  let encR := encPair (encList encRat) encRat
  have hnum : ComputableInPolyTime (fun r : List ℚ × ℚ => r.2.num) encR encIntBin :=
    rat_num.comp (snd (encList encRat) encRat)
  have hden : ComputableInPolyTime (fun r : List ℚ × ℚ => r.2.den) encR encNat :=
    rat_den.comp (snd (encList encRat) encRat)
  have hD' : ComputableInPolyTime (fun r : List ℚ × ℚ => rowDenomProd r.1) encR encNat :=
    computableInPolyTime_rowDenomProd.comp (fst (encList encRat) encRat)
  have hbody : ComputableInPolyTime
      (fun r : List ℚ × ℚ => r.2.num * Int.ofNat (rowDenomProd r.1 / r.2.den))
      encR encIntBin :=
    intBin_mul' hnum (cpt_eq (intBin_natCast.comp (binary_div' hD' hden)) fun _ => rfl)
  exact ComputableInPolyTime.mapWithInput id' hbody

/-- Denominator-clearing exact rational squared norm of `v : List ℚ` (first `n` coordinates),
reusing `BareissElimination.{rowDenomProd, clearRow}` and a single integer dot product. -/
def sqNormRatList (n : ℕ) (v : List ℚ) : ℚ :=
  let D := rowDenomProd v
  let vNum := clearRow v
  Rat.divInt (ListMatrix.dotProduct n vNum vNum) ((D * D : ℕ) : ℤ)

/-- `sqNormRatList n v` equals `MR07Shorten.sqNormRat` on the zero-padded coordinates of `v`. -/
theorem sqNormRatList_eq_sqNormRat (n : ℕ) (v : List ℚ) :
    sqNormRatList n v = MR07Shorten.sqNormRat (fun k : Fin n => v.getD k.val 0) := by
  set D := rowDenomProd v
  have hDpos : 0 < D := rowDenomProd_pos v
  have hDQ : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hDpos.ne'
  dsimp only [sqNormRatList, MR07Shorten.sqNormRat, clearRow]
  rw [Rat.divInt_eq_div, ListMatrix.dotProduct_eq_sum_map_range, list_sum_map_range_eq_sum_fin,
    Int.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k.val < v.length
  · have hlen : k.val < (v.map fun q => q.num * Int.ofNat (D / q.den)).length := by simp [hk]
    rw [List.getD_eq_getElem _ _ hlen, List.getD_eq_getElem _ _ hk]
    simp only [List.getElem_map, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    have hcast : ((v[k.val].num * Int.ofNat (D / v[k.val].den) : ℤ) : ℚ) = (D : ℚ) * v[k.val] :=
      cast_clearRow_mem (List.getElem_mem hk)
    rw [show (v[k.val].num : ℚ) * ((Int.ofNat (D / v[k.val].den) : ℤ) : ℚ) =
        ((v[k.val].num * Int.ofNat (D / v[k.val].den) : ℤ) : ℚ) by push_cast; rfl, hcast]
    change ((D : ℚ) * v[k.val] * ((D : ℚ) * v[k.val])) / ((D : ℚ) * (D : ℚ)) = v[k.val] ^ 2
    field_simp [hDQ]
  · have hlen : (v.map fun q => q.num * Int.ofNat (D / q.den)).length ≤ k.val := by simp; omega
    rw [List.getD_eq_default _ _ hlen, List.getD_eq_default _ _ (by omega)]
    simp

/-- Polynomial-time certificate for `sqNormRatList`. -/
theorem computableInPolyTime_sqNormRatList :
    ComputableInPolyTime (fun p : ℕ × List ℚ => sqNormRatList p.1 p.2)
      (encPair encUnary (encList encRat)) encRat := by
  unfold sqNormRatList
  have hD : ComputableInPolyTime (fun p : ℕ × List ℚ => rowDenomProd p.2)
      (encPair encUnary (encList encRat)) encNat :=
    computableInPolyTime_rowDenomProd.comp (snd encUnary (encList encRat))
  have hvNum : ComputableInPolyTime (fun p : ℕ × List ℚ => clearRow p.2)
      (encPair encUnary (encList encRat)) (encList encIntBin) :=
    computableInPolyTime_clearRow.comp (snd encUnary (encList encRat))
  have hdot : ComputableInPolyTime
      (fun p : ℕ × List ℚ => ListMatrix.dotProduct p.1 (clearRow p.2) (clearRow p.2))
      (encPair encUnary (encList encRat)) encIntBin :=
    listDotProduct.comp ((fst encUnary (encList encRat)).prod (hvNum.prod hvNum))
  have hden2 : ComputableInPolyTime
      (fun p : ℕ × List ℚ => ((rowDenomProd p.2 * rowDenomProd p.2 : ℕ) : ℤ))
      (encPair encUnary (encList encRat)) encIntBin :=
    intBin_natCast.comp (binary_mul' hD hD)
  exact rat_divInt' hdot hden2

/-- Build the `(T.numCols - 1) × T.numRows` `RatTable` whose rows are the columns `j ≠ iStar`
of row-major `IntTable` `T` (matching `MR07Shorten.omitRowTable`). -/
private def omitColAsRatRows (T : IntTable) (iStar : ℕ) : RatTable :=
  let m := T.numCols - 1
  ⟨m, T.numRows,
    (List.range m).map fun a =>
      let j := if a < iStar then a else a + 1
      (List.range T.numRows).map fun k => (T.entry k j : ℚ)⟩

private theorem computableInPolyTime_omitColAsRatRows :
    ComputableInPolyTime (fun p : IntTable × ℕ => omitColAsRatRows p.1 p.2)
      (encPair IntTable.enc encUnary) RatTable.enc := by
  unfold omitColAsRatRows
  have hm : ComputableInPolyTime (fun p : IntTable × ℕ => p.1.numCols - 1)
      (encPair IntTable.enc encUnary) encUnary := by fun_prop
  have hnr : ComputableInPolyTime (fun p : IntTable × ℕ => p.1.numRows)
      (encPair IntTable.enc encUnary) encUnary := by fun_prop
  have hrows : ComputableInPolyTime
      (fun p : IntTable × ℕ =>
        (List.range (p.1.numCols - 1)).map fun a =>
          let j := if a < p.2 then a else a + 1
          (List.range p.1.numRows).map fun k => (p.1.entry k j : ℚ))
      (encPair IntTable.enc encUnary) (encList (encList encRat)) := by
    have houter : ComputableInPolyTime
        (fun p : IntTable × ℕ => List.range (p.1.numCols - 1))
        (encPair IntTable.enc encUnary) (encList encUnary) := by fun_prop
    have hrow : ComputableInPolyTime
        (fun q : (IntTable × ℕ) × ℕ =>
          let j := if q.2 < q.1.2 then q.2 else q.2 + 1
          (List.range q.1.1.numRows).map fun k => (q.1.1.entry k j : ℚ))
        (encPair (encPair IntTable.enc encUnary) encUnary) (encList encRat) := by
      have hinner : ComputableInPolyTime
          (fun q : (IntTable × ℕ) × ℕ => List.range q.1.1.numRows)
          (encPair (encPair IntTable.enc encUnary) encUnary) (encList encUnary) := by fun_prop
      have hentry : ComputableInPolyTime
          (fun r : ((IntTable × ℕ) × ℕ) × ℕ =>
            let j := if r.1.2 < r.1.1.2 then r.1.2 else r.1.2 + 1
            (r.1.1.1.entry r.2 j : ℚ))
          (encPair (encPair (encPair IntTable.enc encUnary) encUnary) encUnary) encRat := by
        let encR := encPair (encPair (encPair IntTable.enc encUnary) encUnary) encUnary
        have hj : ComputableInPolyTime
            (fun r : ((IntTable × ℕ) × ℕ) × ℕ => if r.1.2 < r.1.1.2 then r.1.2 else r.1.2 + 1)
            encR encUnary := by fun_prop
        have hT : ComputableInPolyTime (fun r : ((IntTable × ℕ) × ℕ) × ℕ => r.1.1.1)
            encR IntTable.enc := by fun_prop
        have hk : ComputableInPolyTime (fun r : ((IntTable × ℕ) × ℕ) × ℕ => r.2)
            encR encUnary := by fun_prop
        exact rat_intCast.comp (computableInPolyTime_intTableEntry.comp ((hT.prod hk).prod hj))
      exact ComputableInPolyTime.mapWithInput hinner hentry
    exact ComputableInPolyTime.mapWithInput houter hrow
  exact RatTable.enc_mk_polyTime hm hnr hrows

private theorem omitColAsRatRows_eq_omitRowTable {m : ℕ} (T : IntTable)
    (hr : T.numRows = m + 1) (hc : T.numCols = m + 1) (iStar : Fin (m + 1)) :
    omitColAsRatRows T iStar.val =
      MR07Shorten.omitRowTable (fun j k : Fin (m + 1) => (T.entry k.val j.val : ℚ)) iStar := by
  cases T with
  | mk numRows numCols rows =>
    dsimp only at hr hc
    subst hr; subst hc
    dsimp only [omitColAsRatRows, MR07Shorten.omitRowTable]
    have hm : m + 1 - 1 = m := by omega
    rw [hm]
    congr 1
    apply List.ext_getElem
    · simp
    · intro a ha1 ha2
      simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
      apply List.ext_getElem
      · simp
      · intro k hk1 hk2
        simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
        have hsucc : (iStar.succAbove ⟨a, by simpa using ha2⟩).val =
            if a < iStar.val then a else a + 1 := by
          by_cases hlt : a < iStar.val
          · rw [ite_eq_left hlt,
              Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using hlt)]
            rfl
          · rw [ite_eq_right hlt, Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)]
            rfl
        exact congrArg (fun j => ((RowTable.mk (m + 1) (m + 1) rows).entry k j : ℚ)) hsucc.symm

private def scaleRatList (ρ : ℚ) (v : List ℚ) (n : ℕ) : List ℚ :=
  (List.range n).map fun k => ρ * v.getD k 0

private theorem computableInPolyTime_scaleRatList :
    ComputableInPolyTime (fun p : (ℚ × List ℚ) × ℕ => scaleRatList p.1.1 p.1.2 p.2)
      (encPair (encPair encRat (encList encRat)) encUnary) (encList encRat) := by
  unfold scaleRatList
  let encP := encPair (encPair encRat (encList encRat)) encUnary
  have hrange : ComputableInPolyTime (fun p : (ℚ × List ℚ) × ℕ => List.range p.2)
      encP (encList encUnary) := by fun_prop
  have hbody : ComputableInPolyTime
      (fun q : ((ℚ × List ℚ) × ℕ) × ℕ => q.1.1.1 * q.1.1.2.getD q.2 0)
      (encPair encP encUnary) encRat :=
    rat_mul'
      ((fst encRat (encList encRat)).comp
        ((fst (encPair encRat (encList encRat)) encUnary).comp (fst encP encUnary)))
      ((ComputableInPolyTime.listGetD (encA := encRat) 0).comp
        (((snd encRat (encList encRat)).comp
          ((fst (encPair encRat (encList encRat)) encUnary).comp (fst encP encUnary))).prod
          (snd encP encUnary)))
  exact ComputableInPolyTime.mapWithInput hrange hbody

private def ratOrthoKernelVec (T : IntTable) : List ℚ :=
  (ratKernelBasis (omitColAsRatRows T (intTableMaxSqNormIdx T))).headD []

private theorem computableInPolyTime_ratOrthoKernelVec :
    ComputableInPolyTime ratOrthoKernelVec IntTable.enc (encList encRat) := by
  have hiStar : ComputableInPolyTime intTableMaxSqNormIdx IntTable.enc encUnary :=
    computableInPolyTime_intTableMaxSqNormIdx
  have hM : ComputableInPolyTime (fun T => omitColAsRatRows T (intTableMaxSqNormIdx T))
      IntTable.enc RatTable.enc :=
    computableInPolyTime_omitColAsRatRows.comp (id'.prod hiStar)
  exact (ComputableInPolyTime.headD (encA := encList encRat) []).comp
    (ratKernelBasis_computableInPolyTime.comp hM)

/-- Executable strict-PPT rational orthogonal target `t : List ℚ` for row-major `IntTable` `T`,
matching `MR07Shorten.ratOrthoTarget` entry-by-entry. -/
def ratOrthoTargetIntTable (T : IntTable) : List ℚ :=
  scaleRatList
    (MR07Shorten.ratOrthoScale
      (intTableColSqNorm T (intTableMaxSqNormIdx T) : ℚ)
      (sqNormRatList T.numRows (ratOrthoKernelVec T)))
    (ratOrthoKernelVec T)
    T.numRows

/-- Polynomial-time certificate for `ratOrthoTargetIntTable`. -/
theorem computableInPolyTime_ratOrthoTargetIntTable :
    ComputableInPolyTime ratOrthoTargetIntTable IntTable.enc (encList encRat) := by
  have hiStar : ComputableInPolyTime intTableMaxSqNormIdx IntTable.enc encUnary :=
    computableInPolyTime_intTableMaxSqNormIdx
  have hvList : ComputableInPolyTime ratOrthoKernelVec IntTable.enc (encList encRat) :=
    computableInPolyTime_ratOrthoKernelVec
  have hsqS : ComputableInPolyTime (fun T => (intTableColSqNorm T (intTableMaxSqNormIdx T) : ℚ))
      IntTable.enc encRat :=
    cpt_eq (rat_intCast.comp (intBin_natCast.comp
      (computableInPolyTime_intTableColSqNorm.comp (id'.prod hiStar))))
      fun _ => by simp
  have hnr : ComputableInPolyTime RowTable.numRows IntTable.enc encUnary := by fun_prop
  have hsqV : ComputableInPolyTime
      (fun T => sqNormRatList T.numRows (ratOrthoKernelVec T))
      IntTable.enc encRat :=
    cpt_comp2 computableInPolyTime_sqNormRatList hnr hvList
  have hρ : ComputableInPolyTime
      (fun T => MR07Shorten.ratOrthoScale
        (intTableColSqNorm T (intTableMaxSqNormIdx T) : ℚ)
        (sqNormRatList T.numRows (ratOrthoKernelVec T)))
      IntTable.enc encRat :=
    cpt_comp2 computableInPolyTime_ratOrthoScale hsqS hsqV
  exact cpt_comp3 computableInPolyTime_scaleRatList hρ hvList hnr

/-- Entry-by-entry equality between `ratOrthoTargetIntTable T` and `MR07Shorten.ratOrthoTarget`. -/
theorem ratOrthoTargetIntTable_getD_eq {m : ℕ} (T : IntTable)
    (hr : T.numRows = m + 1) (hc : T.numCols = m + 1) (k : Fin (m + 1)) :
    (ratOrthoTargetIntTable T).getD k.val 0 =
      MR07Shorten.ratOrthoTarget
        (fun j i : Fin (m + 1) => (T.entry i.val j.val : ℚ)) k := by
  cases T with
  | mk nr nc rows =>
    dsimp only at hr hc
    subst hr; subst hc
    let T' : IntTable := ⟨m + 1, m + 1, rows⟩
    let S : Fin (m + 1) → Fin (m + 1) → ℚ := fun j i => (T'.entry i.val j.val : ℚ)
    have hiStar : intTableMaxSqNormIdx T' = (MR07Shorten.maxSqNormIndex S).val :=
      intTableMaxSqNormIdx_eq_maxSqNormIndex T' rfl rfl
    have hM : omitColAsRatRows T' (intTableMaxSqNormIdx T') =
        MR07Shorten.omitRowTable S (MR07Shorten.maxSqNormIndex S) := by
      rw [hiStar]
      exact omitColAsRatRows_eq_omitRowTable T' rfl rfl (MR07Shorten.maxSqNormIndex S)
    have hsqS : (intTableColSqNorm T' (intTableMaxSqNormIdx T') : ℚ) =
        MR07Shorten.sqNormRat (S (MR07Shorten.maxSqNormIndex S)) := by
      rw [hiStar]
      exact intTableColSqNorm_cast_eq_sqNormRat T' rfl (MR07Shorten.maxSqNormIndex S)
    dsimp only [ratOrthoTargetIntTable, ratOrthoKernelVec, scaleRatList, MR07Shorten.ratOrthoTarget]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range k.isLt]
    simp only [Option.map_some, Option.getD_some]
    rw [hM, hsqS, sqNormRatList_eq_sqNormRat]

/-- Geometric specification of `ratOrthoTargetIntTable`: orthogonality to all columns `j ≠ iStar`
and norm window `(1 / 2) * ‖intCol TMat‖ < ‖tE‖ ≤ (9 / 16) * ‖intCol TMat‖`. -/
theorem ratOrthoTargetIntTable_spec {m : ℕ} (T : IntTable)
    (hr : T.numRows = m + 1) (hc : T.numCols = m + 1)
    (hli : LinearIndependent ℝ
      (intCol (Matrix.of fun i j : Fin (m + 1) => T.entry i.val j.val))) :
    let TMat : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ := Matrix.of fun i j => T.entry i.val j.val
    let S : Fin (m + 1) → Fin (m + 1) → ℚ := fun j i => (T.entry i.val j.val : ℚ)
    let iStar := MR07Shorten.maxSqNormIndex S
    let tE := MR07Shorten.toEuclidean
      (fun k : Fin (m + 1) => (ratOrthoTargetIntTable T).getD k.val 0)
    intTableMaxSqNormIdx T = iStar.val ∧
    ‖intCol TMat iStar‖ = ‖intCol TMat‖ ∧
    (∀ j, j ≠ iStar → ⟪tE, intCol TMat j⟫ = 0) ∧
    (1 / 2 : ℝ) * ‖intCol TMat‖ < ‖tE‖ ∧
    ‖tE‖ ≤ (9 / 16 : ℝ) * ‖intCol TMat‖ := by
  let TMat : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ := Matrix.of fun i j => T.entry i.val j.val
  let S : Fin (m + 1) → Fin (m + 1) → ℚ := fun j i => (T.entry i.val j.val : ℚ)
  have hcol_eq : (fun j => MR07Shorten.toEuclidean (S j)) = intCol TMat := by
    funext j; ext i
    simp [MR07Shorten.toEuclidean, intCol, TMat, S]
  have hcol_pt : ∀ j, MR07Shorten.toEuclidean (S j) = intCol TMat j :=
    fun j => congrFun hcol_eq j
  have ht_eq :
      MR07Shorten.toEuclidean (fun k : Fin (m + 1) => (ratOrthoTargetIntTable T).getD k.val 0) =
      MR07Shorten.toEuclidean (MR07Shorten.ratOrthoTarget S) := by
    congr 1; funext k
    exact ratOrthoTargetIntTable_getD_eq T hr hc k
  have hspec := MR07Shorten.ratOrthoTarget_spec S (hcol_eq.symm ▸ hli)
  have hmax := MR07Shorten.norm_maxSqNormIndex_eq_pi_norm S
  refine ⟨intTableMaxSqNormIdx_eq_maxSqNormIndex T hr hc, ?_, ?_, ?_, ?_⟩
  · simpa only [hcol_eq, hcol_pt] using hmax
  · intro j hj
    rw [ht_eq]
    have h1 := hspec.1 j hj
    simpa only [hcol_pt] using h1
  · rw [ht_eq]
    simpa only [hcol_eq] using hspec.2.1
  · rw [ht_eq]
    simpa only [hcol_eq] using hspec.2.2

/-! ### 3. Strict-PPT `guardedUpdateIntTable` matching `MR07Shorten.shortenGuardedStep` -/

/-- Replace column `iStar` of row-major `IntTable` `T` with `u : List ℤ`. -/
private def replaceColIntTable (T : IntTable) (iStar : ℕ) (u : List ℤ) : IntTable :=
  ⟨T.numRows, T.numCols,
    tabulateTable T.numRows T.numCols fun i j =>
      if j = iStar then u.getD i 0 else T.entry i j⟩

/-- Computable Boolean check for `T.numRows = n ∧ T.numCols = n ∧ T.WellFormed`. -/
def intTableIsSquareWF (n : ℕ) (T : IntTable) : Bool :=
  decide (T.numRows = n) && decide (T.numCols = n) && decide (T.rows.length = n) &&
    T.rows.all fun row => decide (row.length = n)

/-- Equivalence between `intTableIsSquareWF n T = true` and well-formed `n × n` shape. -/
theorem intTableIsSquareWF_eq_true_iff (n : ℕ) (T : IntTable) :
    intTableIsSquareWF n T = true ↔ (T.numRows = n ∧ T.numCols = n ∧ T.WellFormed) := by
  unfold intTableIsSquareWF RowTable.WellFormed
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, h1.symm ▸ h3, fun row hrow => h2.symm ▸ h4 row hrow⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, h2⟩, h1 ▸ h3⟩, fun row hrow => h2 ▸ h4 row hrow⟩

/-- Pure-integer squared Euclidean norm of `u : List ℤ` (first `n` entries). -/
private def vecSqNormNat (n : ℕ) (u : List ℤ) : ℕ :=
  (ListMatrix.dotProduct n u u).natAbs

/-- Executable guarded column update for the shortening loop (`IsPPTOn.iterateWith_spec`). -/
def guardedUpdateIntTable (n : ℕ) (T : IntTable) (iStar : ℕ) (u : List ℤ) : IntTable :=
  if intTableIsSquareWF n T && decide (iStar < n) && decide (u.length = n) then
    let cand := replaceColIntTable T iStar u
    if decide (vecSqNormNat n u < intTableColSqNorm T iStar) &&
        !decide (Cslib.Circuits.Rational.detRows cand.rows = 0) then
      cand
    else
      T
  else
    T

private theorem computableInPolyTime_replaceColIntTable :
    ComputableInPolyTime (fun p : (IntTable × ℕ) × List ℤ => replaceColIntTable p.1.1 p.1.2 p.2)
      (encPair (encPair IntTable.enc encUnary) (encList encIntBin)) IntTable.enc := by
  unfold replaceColIntTable
  let encP := encPair (encPair IntTable.enc encUnary) (encList encIntBin)
  have hnr : ComputableInPolyTime (fun p : (IntTable × ℕ) × List ℤ => p.1.1.numRows)
      encP encUnary := by fun_prop
  have hnc : ComputableInPolyTime (fun p : (IntTable × ℕ) × List ℤ => p.1.1.numCols)
      encP encUnary := by fun_prop
  have hrows : ComputableInPolyTime
      (fun p : (IntTable × ℕ) × List ℤ =>
        tabulateTable p.1.1.numRows p.1.1.numCols fun i j =>
          if j = p.1.2 then p.2.getD i 0 else p.1.1.entry i j)
      encP encIntTable := by
    let encR := encPair (encPair encP encUnary) encUnary
    have hg : ComputableInPolyTime
        (fun r : (((IntTable × ℕ) × List ℤ) × ℕ) × ℕ =>
          if r.2 = r.1.1.1.2 then r.1.1.2.getD r.1.2 0 else r.1.1.1.1.entry r.1.2 r.2)
        encR encIntBin := by
      have heq : ComputableInPolyTime
          (fun r : (((IntTable × ℕ) × List ℤ) × ℕ) × ℕ => decide (r.2 = r.1.1.1.2))
          encR encBool := by fun_prop
      have hu : ComputableInPolyTime
          (fun r : (((IntTable × ℕ) × List ℤ) × ℕ) × ℕ => r.1.1.2.getD r.1.2 0) encR encIntBin :=
        (ComputableInPolyTime.listGetD (encA := encIntBin) 0).comp
          (by fun_prop : ComputableInPolyTime
            (fun r : (((IntTable × ℕ) × List ℤ) × ℕ) × ℕ => (r.1.1.2, r.1.2))
            encR (encPair (encList encIntBin) encUnary))
      have hent : ComputableInPolyTime
          (fun r : (((IntTable × ℕ) × List ℤ) × ℕ) × ℕ => r.1.1.1.1.entry r.1.2 r.2)
          encR encIntBin :=
        computableInPolyTime_intTableEntry.comp
          (by fun_prop : ComputableInPolyTime
            (fun r : (((IntTable × ℕ) × List ℤ) × ℕ) × ℕ => ((r.1.1.1.1, r.1.2), r.2))
            encR (encPair (encPair IntTable.enc encUnary) encUnary))
      exact heq.ite_decide hu hent
    exact computableInPolyTime_tabulateTable hnr hnc hg
  exact IntTable.enc_mk_polyTime hnr hnc hrows

private theorem computableInPolyTime_intTableIsSquareWF :
    ComputableInPolyTime (fun p : ℕ × IntTable => intTableIsSquareWF p.1 p.2)
      (encPair encUnary IntTable.enc) encBool := by
  unfold intTableIsSquareWF
  let encP := encPair encUnary IntTable.enc
  have hall : ComputableInPolyTime
      (fun p : ℕ × IntTable => p.2.rows.all fun row => decide (row.length = p.1))
      encP encBool := by
    have hrows : ComputableInPolyTime (fun p : ℕ × IntTable => p.2.rows)
        encP (encList (encList encIntBin)) := by fun_prop
    have hlen_row : ComputableInPolyTime
        (fun q : (ℕ × IntTable) × List ℤ => decide (q.2.length = q.1.1))
        (encPair encP (encList encIntBin)) encBool := by fun_prop
    have hmap : ComputableInPolyTime
        (fun p : ℕ × IntTable => p.2.rows.map fun row => decide (row.length = p.1))
        encP (encList encBool) :=
      ComputableInPolyTime.mapWithInput hrows hlen_row
    have hfold : ComputableInPolyTime (fun l : List Bool => l.foldl (· && ·) true)
        (encList encBool) encBool := by
      refine ComputableInPolyTime.foldl' (encA := encBool) (encB := encBool)
        (encL := encList encBool) (list := id) (init := fun _ => true) (step := fun a b => a && b)
        (by fun_prop) (.const true) (by fun_prop)
        (B := fun _ => 1) (PolyBounded.of_forall_le 1 0 fun _ => by simp)
        fun _ _ _ => by simp [encBool_apply]
    exact cpt_eq (hfold.comp hmap) fun p => by
      have hall_fold : ∀ (l : List (List ℤ)) (b : Bool),
          (l.map fun row => decide (row.length = p.1)).foldl (· && ·) b =
            (b && l.all fun row => decide (row.length = p.1)) := by
        intro l
        induction l with
        | nil => intro b; simp
        | cons r rs ih =>
          intro b
          simp only [List.map_cons, List.foldl_cons, List.all_cons, ih, Bool.and_assoc]
      simpa using hall_fold p.2.rows true
  have h1 : ComputableInPolyTime (fun p : ℕ × IntTable => decide (p.2.numRows = p.1))
      encP encBool := by fun_prop
  have h2 : ComputableInPolyTime (fun p : ℕ × IntTable => decide (p.2.numCols = p.1))
      encP encBool := by fun_prop
  have h3 : ComputableInPolyTime (fun p : ℕ × IntTable => decide (p.2.rows.length = p.1))
      encP encBool := by fun_prop
  exact bool_and.comp ((bool_and.comp ((bool_and.comp (h1.prod h2)).prod h3)).prod hall)

/-- Unconditional polynomial-time certificate for `guardedUpdateIntTable`. -/
theorem computableInPolyTime_guardedUpdateIntTable :
    ComputableInPolyTime
      (fun p : (ℕ × IntTable) × (ℕ × List ℤ) => guardedUpdateIntTable p.1.1 p.1.2 p.2.1 p.2.2)
      (encPair (encPair encUnary IntTable.enc) (encPair encUnary (encList encIntBin)))
      IntTable.enc := by
  unfold guardedUpdateIntTable
  let encIn := encPair (encPair encUnary IntTable.enc) (encPair encUnary (encList encIntBin))
  have hwf : ComputableInPolyTime
      (fun p : (ℕ × IntTable) × (ℕ × List ℤ) => intTableIsSquareWF p.1.1 p.1.2) encIn encBool :=
    computableInPolyTime_intTableIsSquareWF.comp (fst _ _)
  have hi_lt : ComputableInPolyTime
      (fun p : (ℕ × IntTable) × (ℕ × List ℤ) => decide (p.2.1 < p.1.1)) encIn encBool := by fun_prop
  have hu_len : ComputableInPolyTime
      (fun p : (ℕ × IntTable) × (ℕ × List ℤ) => decide (p.2.2.length = p.1.1))
      encIn encBool := by fun_prop
  have houter_cond : ComputableInPolyTime
      (fun p : (ℕ × IntTable) × (ℕ × List ℤ) =>
        intTableIsSquareWF p.1.1 p.1.2 && decide (p.2.1 < p.1.1) && decide (p.2.2.length = p.1.1))
      encIn encBool :=
    bool_and.comp ((bool_and.comp (hwf.prod hi_lt)).prod hu_len)
  have hcand : ComputableInPolyTime
      (fun p : (ℕ × IntTable) × (ℕ × List ℤ) => replaceColIntTable p.1.2 p.2.1 p.2.2)
      encIn IntTable.enc :=
    computableInPolyTime_replaceColIntTable.comp
      ((((snd encUnary IntTable.enc).comp (fst _ _)).prod ((fst encUnary _).comp (snd _ _))).prod
        ((snd encUnary _).comp (snd _ _)))
  have hvec : ComputableInPolyTime
      (fun p : (ℕ × IntTable) × (ℕ × List ℤ) => vecSqNormNat p.1.1 p.2.2) encIn encNat := by
    unfold vecSqNormNat
    have hn : ComputableInPolyTime (fun p : (ℕ × IntTable) × (ℕ × List ℤ) => p.1.1)
        encIn encUnary := by fun_prop
    have hu : ComputableInPolyTime (fun p : (ℕ × IntTable) × (ℕ × List ℤ) => p.2.2)
        encIn (encList encIntBin) := by fun_prop
    exact intBin_natAbs.comp (listDotProduct.comp (hn.prod (hu.prod hu)))
  have hcol : ComputableInPolyTime
      (fun p : (ℕ × IntTable) × (ℕ × List ℤ) => intTableColSqNorm p.1.2 p.2.1) encIn encNat :=
    computableInPolyTime_intTableColSqNorm.comp
      (((snd encUnary IntTable.enc).comp (fst _ _)).prod ((fst encUnary _).comp (snd _ _)))
  have hlt : ComputableInPolyTime
      (fun p : (ℕ × IntTable) × (ℕ × List ℤ) =>
        decide (vecSqNormNat p.1.1 p.2.2 < intTableColSqNorm p.1.2 p.2.1))
      encIn encBool := binary_lt' hvec hcol
  have hcand_rows : ComputableInPolyTime
      (fun p : (ℕ × IntTable) × (ℕ × List ℤ) => (replaceColIntTable p.1.2 p.2.1 p.2.2).rows)
      encIn encIntTable :=
    (by fun_prop : ComputableInPolyTime RowTable.rows IntTable.enc encIntTable).comp hcand
  have hdet0 : ComputableInPolyTime
      (fun p : (ℕ × IntTable) × (ℕ × List ℤ) =>
        !decide (Cslib.Circuits.Rational.detRows (replaceColIntTable p.1.2 p.2.1 p.2.2).rows = 0))
      encIn encBool :=
    bool_not.comp (intBin_isZero.comp (Cslib.Circuits.Rational.detRows_polytime.comp hcand_rows))
  have hinner_cond : ComputableInPolyTime
      (fun p : (ℕ × IntTable) × (ℕ × List ℤ) =>
        decide (vecSqNormNat p.1.1 p.2.2 < intTableColSqNorm p.1.2 p.2.1) &&
          !decide (Cslib.Circuits.Rational.detRows
            (replaceColIntTable p.1.2 p.2.1 p.2.2).rows = 0))
      encIn encBool := bool_and.comp (hlt.prod hdet0)
  have hT : ComputableInPolyTime (fun p : (ℕ × IntTable) × (ℕ × List ℤ) => p.1.2)
      encIn IntTable.enc := by fun_prop
  exact houter_cond.ite (hinner_cond.ite hcand hT) hT

private theorem replaceColIntTable_entry {T : IntTable} {iStar i j : ℕ} {u : List ℤ}
    (hi : i < T.numRows) (hj : j < T.numCols) :
    (replaceColIntTable T iStar u).entry i j = if j = iStar then u.getD i 0 else T.entry i j :=
  rowEntry_tabulateTable_of_lt _ hi hj

/-- Unconditional invariants of `guardedUpdateIntTable`: malformed inputs are returned unchanged,
and well-formed `n × n` inputs stay well-formed `n × n` with every column squared norm bounded by
`intTableMaxColSqNorm T`. -/
theorem guardedUpdateIntTable_invariants (n : ℕ) (T : IntTable) (iStar : ℕ) (u : List ℤ) :
    let T' := guardedUpdateIntTable n T iStar u
    (¬ (T.numRows = n ∧ T.numCols = n ∧ T.WellFormed) → T' = T) ∧
    ((T.numRows = n ∧ T.numCols = n ∧ T.WellFormed) →
      T'.numRows = n ∧ T'.numCols = n ∧ T'.WellFormed ∧
      ∀ j < n, intTableColSqNorm T' j ≤ intTableMaxColSqNorm T) := by
  constructor
  · intro hmal
    have hwf : intTableIsSquareWF n T = false := by
      cases h : intTableIsSquareWF n T
      · rfl
      · exact absurd ((intTableIsSquareWF_eq_true_iff n T).mp h) hmal
    simp [guardedUpdateIntTable, hwf]
  · intro hwf
    dsimp only [guardedUpdateIntTable]
    split_ifs with h1 h2
    · obtain ⟨hr, hc, _⟩ := hwf
      have hcand_wf : (replaceColIntTable T iStar u).WellFormed :=
        isTableShape_tabulateTable T.numRows T.numCols _
      have hlt_sq : vecSqNormNat n u < intTableColSqNorm T iStar := by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
        exact h2.1
      have hi_lt : iStar < n := by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
        exact h1.1.2
      refine ⟨hr, hc, hcand_wf, fun j hj => ?_⟩
      by_cases hji : j = iStar
      · subst hji
        have hcol_eq :
            intTableCol (replaceColIntTable T j u) j = (List.range n).map fun i => u.getD i 0 := by
          unfold intTableCol
          have hnr_eq : (replaceColIntTable T j u).numRows = n := hr
          rw [hnr_eq]
          refine List.map_congr_left fun i hi => ?_
          have hi_lt' : i < T.numRows := hr.symm ▸ List.mem_range.mp hi
          have hj_lt' : j < T.numCols := hc.symm ▸ hj
          simpa using replaceColIntTable_entry (T := T) (iStar := j) (u := u) hi_lt' hj_lt'
        have hsq_eq : intTableColSqNorm (replaceColIntTable T j u) j = vecSqNormNat n u := by
          dsimp only [intTableColSqNorm, vecSqNormNat]
          rw [hcol_eq]
          have hnr_eq : (replaceColIntTable T j u).numRows = n := hr
          rw [hnr_eq, ListMatrix.dotProduct_eq_sum_map_range,
            ListMatrix.dotProduct_eq_sum_map_range]
          congr 2
          refine List.map_congr_left fun i hi => ?_
          have hi_lt' : i < n := List.mem_range.mp hi
          have hlen : i < ((List.range n).map fun k => u.getD k 0).length := by simp [hi_lt']
          rw [List.getD_eq_getElem _ _ hlen]
          simp
        rw [hsq_eq]
        exact hlt_sq.le.trans (intTableColSqNorm_le_max T (hc.symm ▸ hi_lt))
      · have hcol_eq : intTableCol (replaceColIntTable T iStar u) j = intTableCol T j := by
          unfold intTableCol
          change (List.range T.numRows).map (fun i => (replaceColIntTable T iStar u).entry i j) = _
          refine List.map_congr_left fun i hi => ?_
          have hi_lt' : i < T.numRows := List.mem_range.mp hi
          have hj_lt' : j < T.numCols := hc.symm ▸ hj
          simpa [hji] using
            replaceColIntTable_entry (T := T) (iStar := iStar) (u := u) hi_lt' hj_lt'
        have hsq_eq :
            intTableColSqNorm (replaceColIntTable T iStar u) j = intTableColSqNorm T j := by
          dsimp only [intTableColSqNorm]
          rw [hcol_eq]
          rfl
        rw [hsq_eq]
        exact intTableColSqNorm_le_max T (hc.symm ▸ hj)
    · exact ⟨hwf.1, hwf.2.1, hwf.2.2, fun j hj => intTableColSqNorm_le_max T (hwf.2.1.symm ▸ hj)⟩
    · exact ⟨hwf.1, hwf.2.1, hwf.2.2, fun j hj => intTableColSqNorm_le_max T (hwf.2.1.symm ▸ hj)⟩

/-- Real linear independence of the columns `intCol M` is equivalent to `M.det ≠ 0`. -/
theorem linearIndependent_intCol_iff_det_ne_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    LinearIndependent ℝ (intCol M) ↔ M.det ≠ 0 := by
  let MR : Matrix (Fin n) (Fin n) ℝ := M.map Int.cast
  have hdetR : MR.det = (M.det : ℝ) := by
    simpa [MR] using ((Int.castRingHom ℝ).map_det M).symm
  have hcoord_sum : ∀ (c : Fin n → ℝ) (i : Fin n),
      (∑ j : Fin n, c j • intCol M j).ofLp i = (MR *ᵥ c) i := by
    intro c i
    have hlin : (WithLp.linearEquiv 2 ℝ (Fin n → ℝ) (∑ j : Fin n, c j • intCol M j)) i =
        ∑ j : Fin n, c j * (M i j : ℝ) := by
      rw [map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, Pi.smul_apply, smul_eq_mul]
      rfl
    simpa [MR, Matrix.mulVec, dotProduct, mul_comm] using hlin
  have hsum_eq : ∀ c : Fin n → ℝ,
      (∑ j : Fin n, c j • intCol M j = 0) ↔ MR *ᵥ c = 0 := by
    intro c
    constructor
    · intro h; ext i; rw [← hcoord_sum c i, h]; rfl
    · intro h; ext i
      change (∑ j : Fin n, c j • intCol M j).ofLp i = 0
      rw [hcoord_sum c i, h]; rfl
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro hli hdet0
    have hR0 : MR.det = 0 := by rw [hdetR, hdet0, Int.cast_zero]
    obtain ⟨c, hc_ne, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hR0
    exact hc_ne (funext (hli c ((hsum_eq c).mpr hmul)))
  · intro hdet c hc
    have hmul : MR *ᵥ c = 0 := (hsum_eq c).mp hc
    have hunit : IsUnit MR.det :=
      isUnit_iff_ne_zero.mpr (by rw [hdetR]; exact Int.cast_ne_zero.mpr hdet)
    have hc0 : c = 0 := by
      calc c = (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ c := (Matrix.one_mulVec c).symm
        _ = (MR⁻¹ * MR) *ᵥ c := by rw [Matrix.nonsing_inv_mul MR hunit]
        _ = MR⁻¹ *ᵥ (MR *ᵥ c) := (Matrix.mulVec_mulVec _ _ _).symm
        _ = 0 := by rw [hmul, Matrix.mulVec_zero]
    intro j; exact congrFun hc0 j

private theorem vecSqNormNat_cast_eq_norm_sq (n : ℕ) (u : List ℤ) :
    ((vecSqNormNat n u : ℕ) : ℝ) =
      ‖(WithLp.toLp 2 fun i : Fin n => (u.getD i.val 0 : ℝ) : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
  dsimp only [vecSqNormNat]
  rw [ListMatrix.dotProduct_eq_sum_map_range, EuclideanSpace.norm_sq_eq]
  have hsum_nn : 0 ≤ ((List.range n).map fun i => u.getD i 0 * u.getD i 0).sum :=
    list_sum_nonneg_of_forall fun x hx => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      exact mul_self_nonneg _
  have hcast : ((((List.range n).map fun i => u.getD i 0 * u.getD i 0).sum).natAbs : ℝ) =
      ((((List.range n).map fun i => u.getD i 0 * u.getD i 0).sum : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg hsum_nn]
  rw [hcast, list_sum_map_range_eq_sum_fin, Int.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Real.norm_eq_abs, sq]

/-- Exact column-by-column bridge from executable `guardedUpdateIntTable` to
`MR07Shorten.shortenGuardedStep` via `MR07.intColCast`. -/
theorem guardedUpdateIntTable_eq_shortenGuardedStep {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (T : IntTable) (hr : T.numRows = n) (hc : T.numCols = n) (hwf : T.WellFormed)
    (iStar : Fin n) (u : List ℤ) (hu_len : u.length = n)
    (hu_mem : (WithLp.toLp 2 fun i : Fin n => (u.getD i.val 0 : ℝ) : EuclideanSpace ℝ (Fin n)) ∈
      intLattice B) :
    let TMat : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => T.entry i.val j.val
    let T' := guardedUpdateIntTable n T iStar.val u
    let T'Mat : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => T'.entry i.val j.val
    let uE : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i => (u.getD i.val 0 : ℝ)
    intColCast B T'Mat hB =
      MR07Shorten.shortenGuardedStep (intLattice B) (intColCast B TMat hB)
        (Fin.cast (finrank_intLattice hB).symm iStar) uE := by
  let TMat : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => T.entry i.val j.val
  let cand := replaceColIntTable T iStar.val u
  let candMat : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => cand.entry i.val j.val
  let uE : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i => (u.getD i.val 0 : ℝ)
  let iCast : Fin (Module.finrank ℤ (intLattice B)) := Fin.cast (finrank_intLattice hB).symm iStar
  have hcand_col : intCol candMat = Function.update (intCol TMat) iStar uE := by
    funext j; ext i
    have hi : i.val < T.numRows := hr.symm ▸ i.isLt
    have hj : j.val < T.numCols := hc.symm ▸ j.isLt
    have hent : candMat i j = if j = iStar then u.getD i.val 0 else TMat i j := by
      have h1 := replaceColIntTable_entry (T := T) (iStar := iStar.val) (u := u) hi hj
      simpa [candMat, TMat, cand, Fin.ext_iff] using h1
    by_cases hji : j = iStar
    · subst hji; simp [intCol, uE, hent]
    · simp [intCol, hent, hji]
  have hcand_cast : intColCast B candMat hB = Function.update (intColCast B TMat hB) iCast uE := by
    funext k
    simp only [intColCast, Function.comp_apply, hcand_col]
    by_cases hk : k = iCast
    · subst hk; simp [iCast]
    · have hk' : Fin.cast (finrank_intLattice hB) k ≠ iStar := fun h =>
        hk (by ext; simpa [iCast, Fin.ext_iff] using h)
      simp [Function.update_of_ne hk, Function.update_of_ne hk']
  have hdet_eq : Cslib.Circuits.Rational.detRows cand.rows = candMat.det :=
    Cslib.Circuits.Rational.detRows_eq_det_of_rowEntry candMat
      (by simp [cand, replaceColIntTable, hr]) (fun _ _ => rfl)
  have hli_iff : LinearIndependent ℝ (Function.update (intColCast B TMat hB) iCast uE) ↔
      Cslib.Circuits.Rational.detRows cand.rows ≠ 0 := by
    rw [← hcand_cast, hdet_eq, ← linearIndependent_intCol_iff_det_ne_zero candMat]
    let e : Fin (Module.finrank ℤ (intLattice B)) ≃ Fin n := finCongr (finrank_intLattice hB)
    have hcomp : intColCast B candMat hB = intCol candMat ∘ e := rfl
    rw [hcomp]
    exact linearIndependent_equiv e
  have hnorm_iff : vecSqNormNat n u < intTableColSqNorm T iStar.val ↔
      ‖uE‖ < ‖intColCast B TMat hB iCast‖ := by
    have h1 : ‖intColCast B TMat hB iCast‖ = ‖intCol TMat iStar‖ := by
      simp [intColCast, iCast]
    rw [h1, ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _),
      ← vecSqNormNat_cast_eq_norm_sq n u, ← intTableColSqNorm_cast_eq_norm_sq T hr iStar,
      Nat.cast_lt]
  have houter :
      (intTableIsSquareWF n T && decide (iStar.val < n) && decide (u.length = n)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, intTableIsSquareWF_eq_true_iff]
    exact ⟨⟨⟨hr, hc, hwf⟩, iStar.isLt⟩, hu_len⟩
  dsimp only [guardedUpdateIntTable, MR07Shorten.shortenGuardedStep]
  rw [houter]
  simp only [↓reduceIte]
  by_cases hcond : (decide (vecSqNormNat n u < intTableColSqNorm T iStar.val) &&
      !decide (Cslib.Circuits.Rational.detRows cand.rows = 0)) = true
  · have hcond' : uE ∈ intLattice B ∧ ‖uE‖ < ‖intColCast B TMat hB iCast‖ ∧
        LinearIndependent ℝ (Function.update (intColCast B TMat hB) iCast uE) := by
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
        decide_eq_false_iff_not] at hcond
      exact ⟨hu_mem, hnorm_iff.mp hcond.1, hli_iff.mpr hcond.2⟩
    dsimp only [TMat, uE, iCast] at hcond'
    simp only [cand, hcond, ↓reduceIte]
    rw [ite_eq_left hcond']
    exact hcand_cast
  · have hcond' : ¬ (uE ∈ intLattice B ∧ ‖uE‖ < ‖intColCast B TMat hB iCast‖ ∧
        LinearIndependent ℝ (Function.update (intColCast B TMat hB) iCast uE)) := by
      rintro ⟨_, hlt, hli⟩
      apply hcond
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
      exact ⟨hnorm_iff.mpr hlt, hli_iff.mp hli⟩
    dsimp only [TMat, uE, iCast] at hcond'
    simp only [cand, hcond, Bool.false_eq_true, ↓reduceIte]
    rw [ite_eq_right hcond']

/-! ### 4. Cubic `IntTable.enc` encoding-length bound for `IsPPTOn.iterateWith_spec` -/

/-- Direct cubic `IntTable.enc` encoding-length bound: any well-formed `n × n` `IntTable` `T`
whose column squared norms are at most `intTableMaxColSqNorm B₀` satisfies
`(IntTable.enc T).length ≤ 14 * ((IntTable.enc B₀).length + 1) ^ 3`. -/
theorem length_intTableEnc_le_of_colSqNorm_le {n : ℕ} {B₀ T : IntTable}
    (hBr : B₀.numRows = n) (hBc : B₀.numCols = n)
    (hTr : T.numRows = n) (hTc : T.numCols = n) (hTwf : T.WellFormed)
    (hnorm : ∀ j < n, intTableColSqNorm T j ≤ intTableMaxColSqNorm B₀) :
    (IntTable.enc T).length ≤ 14 * ((IntTable.enc B₀).length + 1) ^ 3 := by
  set L := (IntTable.enc B₀).length
  have hBenc : L =
      2 * n + 1 + (2 * n + 1 + (encList (encList encIntBin) B₀.rows).length) := by
    dsimp only [L]
    rw [IntTable.enc_apply, length_encPair, length_encPair, encUnary_apply, List.length_replicate,
      encUnary_apply, List.length_replicate]
    dsimp only; rw [hBr, hBc]
  have hn_le : n ≤ L := by omega
  have hmaxB : intTableMaxColSqNorm B₀ ≤ n * 2 ^ (2 * L) :=
    intTableMaxColSqNorm_le B₀ fun j _ =>
      hBr ▸ intTableColSqNorm_le_numRows_mul_two_pow B₀ j
  have hentry_enc : ∀ row ∈ T.rows, ∀ x ∈ row, (encIntBin x).length ≤ 2 * L + 2 := by
    intro row hrow x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrow
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < T.numRows := by rw [← hTwf.1]; exact hi
    have hj' : j < T.numCols := by rw [← hTwf.2 _ hrow]; exact hj
    have heq : T.entry i j = (T.rows[i])[j] := by
      unfold RowTable.entry
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
    have hsq_le : ((T.rows[i])[j]).natAbs ^ 2 ≤ intTableColSqNorm T j := by
      rw [← heq, intTableColSqNorm_eq_sum_sq]
      exact list_mem_le_sum_nat (List.mem_map.mpr ⟨i, List.mem_range.mpr hi', rfl⟩)
    have hsq_bound : ((T.rows[i])[j]).natAbs ^ 2 < 2 ^ (4 * L) := by
      have h1 : ((T.rows[i])[j]).natAbs ^ 2 ≤ n * 2 ^ (2 * L) :=
        hsq_le.trans ((hnorm j (hTc ▸ hj')).trans hmaxB)
      have hn_lt : n < 2 ^ L := lt_of_le_of_lt hn_le Nat.lt_two_pow_self
      have h2 : n * 2 ^ (2 * L) < 2 ^ L * 2 ^ (2 * L) :=
        Nat.mul_lt_mul_of_pos_right hn_lt (Nat.two_pow_pos _)
      have h3 : 2 ^ L * 2 ^ (2 * L) ≤ 2 ^ (4 * L) := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by decide) (by omega)
      exact lt_of_le_of_lt h1 (lt_of_lt_of_le h2 h3)
    have habs_lt : ((T.rows[i])[j]).natAbs < 2 ^ (2 * L) := by
      by_contra hge
      push Not at hge
      have hsq : (2 ^ (2 * L)) ^ 2 ≤ ((T.rows[i])[j]).natAbs ^ 2 := Nat.pow_le_pow_left hge 2
      have hpow : (2 ^ (2 * L)) ^ 2 = 2 ^ (4 * L) := by rw [← pow_mul]; congr 1; omega
      omega
    rw [length_encIntBin]
    have hsize : ((T.rows[i])[j]).natAbs.size ≤ 2 * L := Nat.size_le.mpr habs_lt
    omega
  have hrow_enc : ∀ row ∈ T.rows, (encList encIntBin row).length ≤ n * (4 * L + 5) := by
    intro row hrow
    have hlen_row : row.length = n := (hTwf.2 row hrow).trans hTc
    have h := length_encList_le encIntBin row (b := 2 * L + 2) (hentry_enc row hrow)
    rw [hlen_row] at h
    exact h.trans (by ring_nf; exact le_rfl)
  have hrows_T : (encList (encList encIntBin) T.rows).length ≤ n * (2 * (n * (4 * L + 5)) + 1) := by
    have h := length_encList_le (encList encIntBin) T.rows (b := n * (4 * L + 5)) hrow_enc
    rw [hTwf.1, hTr] at h
    exact h
  have hTenc : (IntTable.enc T).length =
      2 * n + 1 + (2 * n + 1 + (encList (encList encIntBin) T.rows).length) := by
    rw [IntTable.enc_apply, length_encPair, length_encPair, encUnary_apply, List.length_replicate,
      encUnary_apply, List.length_replicate]
    dsimp only; rw [hTr, hTc]
  have hcubic : n * (2 * (n * (4 * L + 5)) + 1) ≤ L * (2 * (L * (4 * L + 5)) + 1) :=
    Nat.mul_le_mul hn_le
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hn_le)) 1)
  have hexp1 : L * (2 * (L * (4 * L + 5)) + 1) = 8 * L ^ 3 + 10 * L ^ 2 + L := by ring
  have hexp2 : 14 * (L + 1) ^ 3 = 14 * L ^ 3 + 42 * L ^ 2 + 42 * L + 14 := by ring
  rw [hTenc]
  omega

private theorem computableInPolyTime_binary_log_two :
    ComputableInPolyTime (Nat.log 2) encNat encUnary := by
  have h1 : ComputableInPolyTime (fun m : ℕ => if m ≤ 0 then 0 else Nat.clog 2 (m + 1) - 1)
      encNat encUnary := by
    have hz : ComputableInPolyTime (fun m : ℕ => decide (m ≤ 0)) encNat encBool :=
      binary_le' (by fun_prop) (.const 0)
    have hclog : ComputableInPolyTime (fun m : ℕ => Nat.clog 2 (m + 1) - 1) encNat encUnary := by
      have hsucc : ComputableInPolyTime (fun m : ℕ => m + 1) encNat encNat :=
        binary_add' (by fun_prop) (.const 1)
      have hc : ComputableInPolyTime (fun m : ℕ => Nat.clog 2 (m + 1)) encNat encUnary :=
        binary_clog_two.comp hsucc
      exact unary_sub.comp
        (hc.prod (ComputableInPolyTime.const (encIn := encNat) (encOut := encUnary) 1))
    exact hz.ite_decide (.const 0) hclog
  exact cpt_eq h1 fun m => by
    by_cases hm : m = 0
    · subst hm; simp
    · have hnotle : ¬ m ≤ 0 := by omega
      simp only [hnotle, ↓reduceIte]
      set k := Nat.log 2 m
      have hlo : 2 ^ k ≤ m := Nat.pow_log_le_self 2 hm
      have hhi : m < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < 2) m
      have hle : Nat.clog 2 (m + 1) ≤ k + 1 :=
        (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr (by omega)
      have hlt : k < Nat.clog 2 (m + 1) :=
        (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr (by omega)
      omega

/-- Direct `ComputableInPolyTime` certificate for `MR07Shorten.shortenRoundBound`
(via `ComputableInPolyTime.binary_clog_two`). -/
theorem computableInPolyTime_shortenRoundBound :
    ComputableInPolyTime (fun p : ℕ × ℕ => MR07Shorten.shortenRoundBound p.1 p.2)
      (encPair encUnary encNat) encUnary := by
  unfold MR07Shorten.shortenRoundBound
  have hlog : ComputableInPolyTime (fun p : ℕ × ℕ => Nat.log 2 p.2)
      (encPair encUnary encNat) encUnary :=
    computableInPolyTime_binary_log_two.comp (snd encUnary encNat)
  have h1 : ComputableInPolyTime (fun p : ℕ × ℕ => 2 * p.1)
      (encPair encUnary encNat) encUnary := by fun_prop
  have h2 : ComputableInPolyTime (fun p : ℕ × ℕ => Nat.log 2 p.2 + 1)
      (encPair encUnary encNat) encUnary :=
    unary_add.comp
      (hlog.prod (ComputableInPolyTime.const (encIn := encPair encUnary encNat)
        (encOut := encUnary) 1))
  exact unary_mul.comp (h1.prod h2)

end Cslib.Crypto.SIS.MR07
