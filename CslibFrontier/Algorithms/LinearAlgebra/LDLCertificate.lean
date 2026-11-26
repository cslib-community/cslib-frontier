/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Matrix.OfLists
import CslibFrontier.Foundations.Data.Rat.ClearDenom
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Data.List.GetD
import Mathlib.Data.Rat.Cast.Order
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.LinearCombination

/-!
# Exact `LDLᵀ` certificates for rational matrices, checked by the kernel

A symmetric rational matrix `M` is positive definite when it factors as `M = L * diagonal d * Lᵀ`
with `L` unit lower triangular and every `d i > 0`, and positive semidefinite when every
`d i ≥ 0` (`Matrix.posDef_mul_diagonal_mul_conjTranspose_iff`). An external tool, such as SymPy's
`LDLdecomposition`, finds `L` and `d`; this module checks them exactly, by a Boolean function
that the kernel evaluates (`decide +kernel`), and turns acceptance into Mathlib's
`Matrix.PosDef` or `Matrix.PosSemidef` of `M` cast to `ℝ`. A singular positive semidefinite `M`
has a witness with some `d i = 0`, and the checker never divides.

The checkers are also complete: a matrix given by `n` rows of `n` entries has an accepted witness
exactly when it is positive (semi)definite over `ℝ`. Symmetric elimination without pivoting
(`Matrix.exists_LDL_of_posSemidef`, `Matrix.exists_LDL_of_posDef`) stays in `ℚ` and supplies one.
A rejected witness says nothing about the matrix, but the absence of any accepted witness refutes
`⪰ 0` (`≻ 0`).

## Representation

A matrix is given by its list of rows and read as `Mathlib.Tactic.Matrix.ofLists m n rows`, the
`m × n` matrix of the first `m` rows and their first `n` entries, padded with zeros; for a list
literal this is the `!![…]` matrix up to definitional unfolding. The dimensions are explicit, so
the theorems concern `Matrix (Fin m) (Fin n) ℚ` and their casts to `ℝ`. The checkers do not rely
on the padding: `Cslib.LinearAlgebra.LDLCert.factors` rejects a matrix unless it has exactly `n`
rows of exactly `n` entries (`Cslib.LinearAlgebra.isShape`).

Matrices are combined on rows by `Mathlib.Tactic.Matrix.ListMatrix.transpose`,
`Cslib.LinearAlgebra.rowsMul` (a product the kernel evaluates; Mathlib's `ListMatrix.mul` seals
its dot product), `Cslib.LinearAlgebra.rowsMap₂` (entrywise sums, differences, negations and
scalings) and `Cslib.LinearAlgebra.rowsTrace`, each interpreted by an `ofLists` lemma without any
shape hypothesis. A trace of a product, such as the Gramian energy `tr (Bᵀ * W * B)` of #8322, is
`rowsTrace` of `rowsMul` (`Cslib.LinearAlgebra.trace_mul_ofLists`). A positive
semidefinite residual `N - M ⪰ 0` is checked on `rowsMap₂ (· - ·) n n N M`, and the Lyapunov
client `Cslib.LinearAlgebra.LyapunovCert` recomputes `-(Aᵀ * P + P * A)` from `A` and `P`
instead of taking it as input, in integers (`Cslib.LinearAlgebra.scaledLyapunovResidual`, which
agrees with `Cslib.LinearAlgebra.lyapunovResidual` by
`Cslib.LinearAlgebra.map_ofLists_scaledLyapunovResidual`).

A certificate `Cslib.LinearAlgebra.LDLCert` lists the rows of `L` and the entries of `d`. Row `i`
of `lower` holds `L i 0, …, L i i`, so triangularity is the length `i + 1` of the row and the unit
diagonal is its last entry `1`. A certificate for `n × n` matrices is rejected unless `lower` has
exactly `n` rows of these lengths, each ending in `1`, and `diag` has exactly `n` entries. The
empty dimension `n = 0` has the empty certificate, and the empty matrix is positive definite.

## Certificate layout

A certificate is ordinary Lean source: the rows of `M` (or `A` and `P`), `lower` and `diag` as list
literals of rational literals. Write every non-integer entry with its type, as `(5/4 : ℚ)`.
Bare `5/4` entries are elaborated as untyped `binop%` trees whose type is settled only when the
whole literal is, and elaborating a `48 × 48` matrix of them did not finish in 20 minutes; with
the ascription elaboration is linear in the size of the literal (about 5 s for a `48 × 48`
certificate). The ascribed and the bare literal elaborate to the same term, so the kernel cost is
unchanged.

## Kernel cost

The identity `M = L * diagonal d * Lᵀ` is checked in integer arithmetic. Row `i` of `L` is
scaled to integers by the least common multiple `sᵢ` of its denominators, and `d` by `t`
(`Cslib.LinearAlgebra.denLcm`, `Cslib.LinearAlgebra.scaleRow`), and entry `(i, j)` is checked as
`M i j * (sᵢ * sⱼ * t) = ∑ₖ aᵢₖ eₖ aⱼₖ` for the scaled rows `a` and `e`, with the rational
`M i j` compared through its numerator and denominator. Rational `+` and `*` normalize by a `gcd`
at every step; in the kernel the integer form is the faster one on the benchmarks of #8319,
increasingly so as the coefficients grow. Only the entries on and below the diagonal are checked
(`Cslib.LinearAlgebra.LDLCert.scaledLowerCheck`), at `j + 1` integer products for entry
`(i, j)`, and the rest follow from the symmetry of `M`, which `factors` checks by comparing the
rows with their transpose. The Lyapunov residual is computed from `A` and `P` scaled by the lcm
of all their denominators, so its two products are integer products, and its symmetry is not
checked but proved from that of the accepted `P`. All recursion is structural, on lists or on
the dimensions, and the kernel's GMP-accelerated `Nat` operations do the arithmetic.

## Main definitions

* `Cslib.LinearAlgebra.rowDot`, `Cslib.LinearAlgebra.rowsMul`, `Cslib.LinearAlgebra.rowsMap₂`,
  `Cslib.LinearAlgebra.rowsTrace`: operations on lists of rows that the kernel evaluates.
* `Cslib.LinearAlgebra.LDLCert`: an `LDLᵀ` witness, with its factors `LDLCert.L` and `LDLCert.d`.
* `Cslib.LinearAlgebra.LDLCert.factors`, `LDLCert.checkPosDef`, `LDLCert.checkPosSemidef`: the
  checkers, built on the lower-triangle check `LDLCert.factorsLower`.
* `Cslib.LinearAlgebra.scaledLyapunovResidual`, `Cslib.LinearAlgebra.lyapunovScale`: the
  fraction-free Lyapunov residual.
* `Cslib.LinearAlgebra.LyapunovCert`, `LyapunovCert.check`: witnesses for `P ≻ 0` and
  `-(Aᵀ * P + P * A) ≻ 0`.

## Main results

* `Cslib.LinearAlgebra.ofLists_rowsMul`, `Cslib.LinearAlgebra.ofLists_rowsMap₂`,
  `Cslib.LinearAlgebra.trace_ofLists`, `Cslib.LinearAlgebra.trace_mul_ofLists`,
  `Cslib.LinearAlgebra.ofLists_lyapunovResidual`: the row operations compute the matrix ones.
* `Cslib.LinearAlgebra.map_ofLists_scaleRow`,
  `Cslib.LinearAlgebra.map_ofLists_scaledLyapunovResidual`: integer scaling agrees with the
  rational matrices.
* `Cslib.LinearAlgebra.LDLCert.eq_of_factors`: an accepted witness factors `M`.
* `Cslib.LinearAlgebra.LDLCert.posDef_of_checkPosDef`,
  `Cslib.LinearAlgebra.LDLCert.posSemidef_of_checkPosSemidef`: soundness over `ℝ`.
* `Cslib.LinearAlgebra.LDLCert.exists_checkPosDef_iff`,
  `Cslib.LinearAlgebra.LDLCert.exists_checkPosSemidef_iff`: soundness and completeness, for
  matrices of `n` rows of `n` entries.
* `Cslib.LinearAlgebra.LyapunovCert.posDef_of_check`: an accepted Lyapunov witness gives
  `P ≻ 0` and `-(Aᵀ * P + P * A) ≻ 0` over `ℝ`.
-/
public section

open Matrix Mathlib.Tactic.Matrix

namespace Cslib.LinearAlgebra

/-! ### Kernel-reducible operations on lists of rows -/

section ListOps

variable {α β γ : Type*}

/-- The sum of the products of corresponding entries of two lists, over the positions where both
have one. Unlike Mathlib's sealed `Mathlib.Tactic.Matrix.ListMatrix.dotProduct`, the kernel
evaluates it. -/
@[expose] def rowDot [Mul α] [Add α] [Zero α] : List α → List α → α
  | a :: r, b :: s => a * b + rowDot r s
  | _, _ => 0

/-- `rowDot r s` is the dot product of the length-`n` vectors read from `r` and `s`, padded with
zeros, whenever `r` has at most `n` entries. -/
theorem rowDot_eq_sum [NonUnitalNonAssocSemiring α] {n : ℕ} {r : List α} (s : List α)
    (hr : r.length ≤ n) : rowDot r s = ∑ k : Fin n, r.getD k 0 * s.getD k 0 := by
  induction n generalizing r s with
  | zero => simp [List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hr), rowDot]
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    rcases r with _ | ⟨a, r⟩ <;> rcases s with _ | ⟨b, s⟩
    · simp [rowDot]
    · simp [rowDot]
    · simp [rowDot]
    · simp only [rowDot, Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ,
        ih _ (Nat.le_of_succ_le_succ hr)]

/-- The product of `A`, read as `l × m`, and `B`, read as `m × n`, as `l` rows of `n` entries:
Mathlib's `Mathlib.Tactic.Matrix.ListMatrix.mul` with `rowDot` in place of its sealed dot
product, so that the kernel evaluates it. -/
@[expose] def rowsMul [Mul α] [Add α] [Zero α] (l m n : ℕ) (A B : List (List α)) :
    List (List α) :=
  let cols := ListMatrix.transpose n B
  (A.rightpad l []).map fun row => cols.map (rowDot (row.take m))

/-- `rowsMul` computes the matrix product, with no shape hypothesis on `A` or `B`. -/
theorem ofLists_rowsMul [NonUnitalNonAssocSemiring α] (l m n : ℕ) (A B : List (List α)) :
    ofLists l n (rowsMul l m n A B) = ofLists l m A * ofLists m n B := by
  rw [ofLists_mul]
  congr 1
  refine List.map_congr_left fun row _ => List.map_congr_left fun col _ => ?_
  rw [rowDot_eq_sum _ (List.length_take_le _ _), ListMatrix.dotProduct_eq]
  exact Finset.sum_congr rfl fun _ _ => by simp [ofList_apply, List.getD_eq_getElem?_getD]

/-- `f` applied to corresponding entries of the first `n` entries of two lists, padded with
zeros. -/
@[expose] def rowMap₂ [Zero α] [Zero β] (f : α → β → γ) : ℕ → List α → List β → List γ
  | 0, _, _ => []
  | n + 1, r, s => f (r.headD 0) (s.headD 0) :: rowMap₂ f n r.tail s.tail

/-- `f` applied entrywise to `A` and `B`, both read as `m × n` matrices, as `m` rows of `n`
entries. -/
@[expose] def rowsMap₂ [Zero α] [Zero β] (f : α → β → γ) :
    ℕ → ℕ → List (List α) → List (List β) → List (List γ)
  | 0, _, _, _ => []
  | m + 1, n, A, B => rowMap₂ f n (A.headD []) (B.headD []) :: rowsMap₂ f m n A.tail B.tail

private theorem getD_rowMap₂ [Zero α] [Zero β] [Zero γ] (f : α → β → γ) :
    ∀ {n k : ℕ} (r : List α) (s : List β), k < n →
      (rowMap₂ f n r s).getD k 0 = f (r.getD k 0) (s.getD k 0)
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, 0, r, s, _ => by cases r <;> cases s <;> simp [rowMap₂]
  | n + 1, k + 1, r, s, h => by
    rw [rowMap₂, List.getD_cons_succ, getD_rowMap₂ f r.tail s.tail (by omega)]
    cases r <;> cases s <;> simp

private theorem getD_rowsMap₂ [Zero α] [Zero β] (f : α → β → γ) :
    ∀ {m i : ℕ} (n : ℕ) (A : List (List α)) (B : List (List β)), i < m →
      (rowsMap₂ f m n A B).getD i [] = rowMap₂ f n (A.getD i []) (B.getD i [])
  | 0, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | m + 1, 0, n, A, B, _ => by cases A <;> cases B <;> simp [rowsMap₂]
  | m + 1, i + 1, n, A, B, h => by
    rw [rowsMap₂, List.getD_cons_succ, getD_rowsMap₂ f n A.tail B.tail (by omega)]
    cases A <;> cases B <;> simp

/-- `rowsMap₂ f` computes `f` entrywise, with no shape hypothesis on `A` or `B`. -/
theorem ofLists_rowsMap₂ [Zero α] [Zero β] [Zero γ] (f : α → β → γ) (m n : ℕ)
    (A : List (List α)) (B : List (List β)) :
    ofLists m n (rowsMap₂ f m n A B) = of fun i j => f (ofLists m n A i j) (ofLists m n B i j) := by
  ext i j
  simp only [ofLists_apply, ofList_apply, of_apply, getD_rowsMap₂ f n A B i.is_lt,
    getD_rowMap₂ f _ _ j.is_lt]

/-- The sum of the first `n` diagonal entries of `rows`, read as an `n × n` matrix padded with
zeros: entry `(0, 0)`, then the trace of the rows below with their first entries dropped. -/
@[expose] def rowsTrace [Add α] [Zero α] : ℕ → List (List α) → α
  | 0, _ => 0
  | n + 1, rows => (rows.headD []).headD 0 + rowsTrace n (rows.tail.map List.tail)

private theorem getD_map_tail (rows : List (List α)) (i : ℕ) :
    (rows.map List.tail).getD i [] = (rows.getD i []).tail := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases rows[i]? <;> rfl

private theorem getD_tail [Zero α] (r : List α) (i : ℕ) : r.tail.getD i 0 = r.getD (i + 1) 0 := by
  cases r <;> simp

/-- `rowsTrace` computes the trace, with no shape hypothesis on `rows`. -/
theorem trace_ofLists [AddCommMonoid α] (n : ℕ) (rows : List (List α)) :
    (ofLists n n rows).trace = rowsTrace n rows := by
  induction n generalizing rows with
  | zero => simp [rowsTrace]
  | succ n ih =>
    rw [rowsTrace, ← ih, trace, trace, Fin.sum_univ_succ]
    congr 1
    · rcases rows with _ | ⟨r, rows⟩
      · simp [ofLists_apply, ofList_apply]
      · cases r <;> simp [ofLists_apply, ofList_apply]
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [diag_apply, ofLists_apply, ofList_apply, Fin.val_succ, getD_map_tail,
        getD_tail]
      cases rows <;> simp

/-- The trace of a product computed on rows, such as `tr (Bᵀ * W * B)`: `rowsTrace` of
`rowsMul`. -/
theorem trace_mul_ofLists [NonUnitalNonAssocSemiring α] (l m : ℕ) (A B : List (List α)) :
    (ofLists l m A * ofLists m l B).trace = rowsTrace l (rowsMul l m l A B) := by
  rw [← ofLists_rowsMul, trace_ofLists]

/-- Whether `rows` has exactly `m` rows of exactly `n` entries. -/
@[expose] def isShape (m n : ℕ) (rows : List (List α)) : Bool :=
  rows.length == m && rows.all (·.length == n)

end ListOps

/-! ### Integer scaling of rational rows -/

/-- The least common multiple of the denominators of a list of rationals. -/
@[expose] def denLcm (r : List ℚ) : ℕ :=
  r.foldl (fun acc q => acc.lcm q.den) 1

/-- The integer list `s * q` for the entries `q` of `r`, exact when every `q.den` divides `s`. -/
@[expose] def scaleRow (s : ℕ) (r : List ℚ) : List ℤ :=
  r.map fun q => q.num * ((s / q.den : ℕ) : ℤ)

private theorem foldl_lcm_spec (r : List ℚ) (acc : ℕ) :
    acc ∣ r.foldl (fun a q => a.lcm q.den) acc ∧
      ∀ q ∈ r, q.den ∣ r.foldl (fun a q => a.lcm q.den) acc := by
  induction r generalizing acc with
  | nil => simp
  | cons q r ih =>
    obtain ⟨h₁, h₂⟩ := ih (acc.lcm q.den)
    exact ⟨(Nat.dvd_lcm_left _ _).trans h₁,
      List.forall_mem_cons.2 ⟨(Nat.dvd_lcm_right _ _).trans h₁, h₂⟩⟩

private theorem foldl_lcm_pos (r : List ℚ) {acc : ℕ} (h : 0 < acc) :
    0 < r.foldl (fun a q => a.lcm q.den) acc := by
  induction r generalizing acc with
  | nil => exact h
  | cons q r ih => exact ih (Nat.lcm_pos h q.den_pos)

/-- The denominators' lcm is positive. -/
theorem denLcm_pos (r : List ℚ) : 0 < denLcm r := foldl_lcm_pos r Nat.one_pos

/-- Every denominator divides `denLcm`. -/
theorem den_dvd_denLcm {r : List ℚ} {q : ℚ} (hq : q ∈ r) : q.den ∣ denLcm r :=
  (foldl_lcm_spec r 1).2 q hq

/-- `scaleRow s r` is `s` times `r`, entrywise and with zero padding, when every denominator of
`r` divides `s`. -/
private theorem cast_getD_scaleRow {s : ℕ} {r : List ℚ} (hs : ∀ q ∈ r, q.den ∣ s) (k : ℕ) :
    (((scaleRow s r).getD k 0 : ℤ) : ℚ) = s * r.getD k 0 := by
  simp only [scaleRow, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : r[k]? with
  | none => simp
  | some q => simpa using (Rat.clearDenom_entry (hs _ (List.mem_of_getElem? h))).symm

/-- Scaling every row of `A` by a common multiple `s` of its denominators scales its matrix. -/
theorem map_ofLists_scaleRow {m n s : ℕ} {A : List (List ℚ)} (hs : ∀ q ∈ A.flatten, q.den ∣ s) :
    (ofLists m n (A.map (scaleRow s))).map ((↑) : ℤ → ℚ) = (s : ℚ) • ofLists m n A := by
  ext i j
  have hrow : (A.map (scaleRow s)).getD i [] = scaleRow s (A.getD i []) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases A[(i : ℕ)]? <;> rfl
  have hs' : ∀ q ∈ A.getD i [], q.den ∣ s := by
    intro q hq
    rcases Nat.lt_or_ge i A.length with hi | hi
    · rw [List.getD_eq_getElem _ _ hi] at hq
      exact hs q (List.mem_flatten.2 ⟨_, List.getElem_mem hi, hq⟩)
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi] at hq
  simp only [map_apply, Matrix.smul_apply, smul_eq_mul, ofLists_apply, ofList_apply]
  rw [hrow, cast_getD_scaleRow hs']

/-! ### `LDLᵀ` certificates -/

/-- A rational matrix whose cast to `ℝ` is positive semidefinite is positive semidefinite. -/
private theorem posSemidef_of_map_ratCast {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ}
    (h : (M.map ((↑) : ℚ → ℝ)).PosSemidef) : M.PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    have := congrFun (congrFun h.isHermitian.eq i) j
    simp only [conjTranspose_apply, map_apply, star_trivial] at this ⊢
    exact_mod_cast this
  · have := h.dotProduct_mulVec_nonneg fun i => (x i : ℝ)
    simp only [star_trivial, dotProduct, mulVec, map_apply] at this ⊢
    exact_mod_cast this

/-- A rational matrix whose cast to `ℝ` is positive definite is positive definite. -/
private theorem posDef_of_map_ratCast {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ}
    (h : (M.map ((↑) : ℚ → ℝ)).PosDef) : M.PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext i j
    have := congrFun (congrFun h.isHermitian.eq i) j
    simp only [conjTranspose_apply, map_apply, star_trivial] at this ⊢
    exact_mod_cast this
  · have := h.dotProduct_mulVec_pos (x := fun i => (x i : ℝ)) fun h0 =>
      hx (funext fun i => by simpa using congrFun h0 i)
    simp only [star_trivial, dotProduct, mulVec, map_apply] at this ⊢
    exact_mod_cast this

/-- A predicate holds on a zipped list exactly when it holds at every position. -/
private theorem all_zip_iff {β γ : Type*} {p : β × γ → Bool} {l₁ : List β} {l₂ : List γ} :
    (l₁.zip l₂).all p = true ↔
      ∀ i (h₁ : i < l₁.length) (h₂ : i < l₂.length), p (l₁[i], l₂[i]) = true := by
  simp only [List.all_eq_true, List.mem_iff_getElem, List.length_zip]
  constructor
  · intro h i h₁ h₂
    simpa using h _ ⟨i, by omega, rfl⟩
  · rintro h _ ⟨i, hi, rfl⟩
    simpa using h i (by omega) (by omega)

/-- An `LDLᵀ` witness for an `n × n` rational matrix: `L` unit lower triangular and `d` the
diagonal. Row `i` of `lower` lists `L i 0, …, L i i`, ending in the diagonal entry `1`. -/
structure LDLCert where
  /-- Row `i` lists `L i 0, …, L i i`. -/
  lower : List (List ℚ)
  /-- The diagonal `d 0, …, d (n - 1)`. -/
  diag : List ℚ

namespace LDLCert

variable (c : LDLCert) {n : ℕ}

/-- The factor `L` as an `n × n` matrix: the rows of `c.lower`, padded with zeros. -/
@[expose] def L (n : ℕ) : Matrix (Fin n) (Fin n) ℚ := ofLists n n c.lower

/-- The diagonal factor `d` as an `n`-vector, padded with zeros. -/
@[expose] def d (n : ℕ) : Fin n → ℚ := ofList n c.diag

/-- Whether row `k` of `rows` has `i + k + 1` entries ending in `1`, for every `k`: the rows
`i, i + 1, …` of a unit lower-triangular factor. -/
@[expose] def unitLowerFrom : ℕ → List (List ℚ) → Bool
  | _, [] => true
  | i, r :: rows => r.length == i + 1 && r.getLast? == some 1 && unitLowerFrom (i + 1) rows

/-- Whether `v = L * diagonal d * Lᵀ` holds on and below the diagonal, for `v` given by rows of
entries `x` standing for `num x / den x`, checked in integers: row `i` of `L` is scaled by
`sᵢ = denLcm (row i)` and `d` by `t = denLcm d`, and entry `(i, j)` with `j ≤ i` is checked as
`num x * (sᵢ * sⱼ * t) = (∑ₖ aᵢₖ eₖ aⱼₖ) * den x` for the scaled rows `a` and `e`. Row `i` of
`L` has `i + 1` entries, so the zip with the first `i + 1` entries of row `i` of `v` stops at the
diagonal. -/
@[expose] def scaledLowerCheck {β : Type*} (num : β → ℤ) (den : β → ℕ) (rows : List (List β))
    (lower : List (List ℚ)) (diag : List ℚ) : Bool :=
  let t := denLcm diag
  let e := scaleRow t diag
  let A := lower.map fun r => (scaleRow (denLcm r) r, denLcm r)
  (rows.zip A).all fun ⟨mrow, a, s⟩ =>
    let w := List.zipWith (· * ·) a e
    ((mrow.take a.length).zip A).all fun ⟨m, b, s'⟩ =>
      num m * ((s * s' * t : ℕ) : ℤ) == rowDot w b * den m

/-- Whether `c` factors a symmetric `n × n` matrix given by rows of entries `x` standing for
`num x / den x`, on and below the diagonal: `rows` has `n` rows of `n` entries, `c.lower` has `n`
rows, row `i` with `i + 1` entries ending in `1`, `c.diag` has `n` entries, and
`scaledLowerCheck` accepts. Symmetry is not checked here. -/
@[expose] def factorsLower {β : Type*} (num : β → ℤ) (den : β → ℕ) (n : ℕ)
    (rows : List (List β)) : Bool :=
  isShape n n rows && c.lower.length == n && c.diag.length == n && unitLowerFrom 0 c.lower &&
    scaledLowerCheck num den rows c.lower c.diag

/-- Whether `c` is an `LDLᵀ` factorization of the `n × n` matrix with rows `rows`: `rows` is
symmetric, it has `n` rows of `n` entries, `c.lower` has `n` rows, row `i` with `i + 1` entries
ending in `1`, `c.diag` has `n` entries, and `ofLists n n rows = c.L n * diagonal (c.d n) *
(c.L n)ᵀ` on and below the diagonal, hence everywhere. -/
@[expose] def factors (n : ℕ) (rows : List (List ℚ)) : Bool :=
  ListMatrix.transpose n rows == rows && c.factorsLower Rat.num Rat.den n rows

/-- Whether `c` certifies `ofLists n n rows ≻ 0`: it factors the matrix and every `d i` is
positive. -/
@[expose] def checkPosDef (n : ℕ) (rows : List (List ℚ)) : Bool :=
  c.factors n rows && c.diag.all (0 < ·)

/-- Whether `c` certifies `ofLists n n rows ⪰ 0`: it factors the matrix and every `d i` is
nonnegative. -/
@[expose] def checkPosSemidef (n : ℕ) (rows : List (List ℚ)) : Bool :=
  c.factors n rows && c.diag.all (0 ≤ ·)

private theorem unitLowerFrom_iff {i : ℕ} {rows : List (List ℚ)} :
    unitLowerFrom i rows = true ↔
      ∀ k (hk : k < rows.length), rows[k].length = i + k + 1 ∧ rows[k].getLast? = some 1 := by
  induction rows generalizing i with
  | nil => simp [unitLowerFrom]
  | cons r rows ih =>
    simp only [unitLowerFrom, Bool.and_eq_true, beq_iff_eq, ih, List.length_cons]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩ k hk
      rcases k with _ | k
      · simpa using ⟨h₁, h₂⟩
      · obtain ⟨h₄, h₅⟩ := h₃ k (by omega)
        exact ⟨by simp only [List.getElem_cons_succ, h₄]; omega, h₅⟩
    · intro h
      refine ⟨⟨by simpa using (h 0 (by omega)).1, by simpa using (h 0 (by omega)).2⟩,
        fun k hk => ?_⟩
      obtain ⟨h₄, h₅⟩ := h (k + 1) (by omega)
      exact ⟨by simp only [List.getElem_cons_succ] at h₄; omega, h₅⟩

private theorem L_apply {c : LDLCert} (i j : Fin n) :
    c.L n i j = (c.lower.getD i []).getD j 0 := by
  simp [L, ofLists_apply, ofList_apply]

private theorem isLowerTriangular_L {c : LDLCert} (hlen : c.lower.length = n)
    (hl : unitLowerFrom 0 c.lower = true) : (c.L n).IsLowerTriangular := by
  intro i j hij
  have hi : (i : ℕ) < c.lower.length := hlen ▸ i.is_lt
  have hrow := (unitLowerFrom_iff.1 hl i hi).1
  have hij' : (i : ℕ) < j := hij
  rw [L_apply, List.getD_eq_getElem _ _ hi, List.getD_eq_default _ _ (by omega)]

private theorem L_apply_self {c : LDLCert} (hlen : c.lower.length = n)
    (hl : unitLowerFrom 0 c.lower = true) (i : Fin n) : c.L n i i = 1 := by
  have hi : (i : ℕ) < c.lower.length := hlen ▸ i.is_lt
  obtain ⟨hrow, hlast⟩ := unitLowerFrom_iff.1 hl i hi
  rw [List.getLast?_eq_getElem?, hrow, List.getElem?_eq_getElem (by omega)] at hlast
  rw [L_apply, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by omega)]
  simpa using hlast

/-- `List.zipWith (· * ·)`, read entrywise with zero padding. -/
private theorem getD_zipWith_mul (a b : List ℤ) (k : ℕ) :
    (List.zipWith (· * ·) a b).getD k 0 = a.getD k 0 * b.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_zipWith]
  cases a[k]? <;> cases b[k]? <;> simp

/-- The integer check of one entry, read over `ℚ`: when `a` stands for `v * b` with `b > 0` and
`D` for `S * X` with `S > 0`, the check `a * S = D * b` holds exactly when `v = X`. -/
private theorem scaled_eq_iff {v X : ℚ} {a D : ℤ} {b S : ℕ} (hb : 0 < b) (hS : 0 < S)
    (hv : (a : ℚ) = v * b) (hD : (D : ℚ) = S * X) : a * (S : ℤ) = D * b ↔ v = X := by
  rw [← @Int.cast_inj ℚ]
  push_cast
  rw [hv, hD]
  constructor
  · intro h
    apply mul_left_cancel₀ (mul_ne_zero (Nat.cast_ne_zero.2 hb.ne') (Nat.cast_ne_zero.2 hS.ne'))
    linear_combination h
  · rintro rfl
    ring

/-- The product `L * diagonal d * Lᵀ` is symmetric. -/
private theorem transpose_LDLt : (c.L n * diagonal (c.d n) * (c.L n)ᵀ)ᵀ =
    c.L n * diagonal (c.d n) * (c.L n)ᵀ := by
  rw [transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]

/-- The lower-triangle check of a well-formed witness accepts exactly when `v` agrees with
`L * diagonal d * Lᵀ` on and below the diagonal, for `v` given by `n` rows of `n` entries `x`
standing for `num x / den x`. -/
private theorem scaledLowerCheck_iff {β : Type*} [Zero β] {num : β → ℤ} {den : β → ℕ}
    {rows : List (List β)} {v : Matrix (Fin n) (Fin n) ℚ}
    (hval : ∀ i j : Fin n,
      (num ((rows.getD i []).getD j 0) : ℚ) = v i j * den ((rows.getD i []).getD j 0))
    (hden : ∀ i j : Fin n, 0 < den ((rows.getD i []).getD j 0))
    (hrows : rows.length = n) (hrow : ∀ r ∈ rows, r.length = n) (hlen : c.lower.length = n)
    (hdlen : c.diag.length = n) (hl : unitLowerFrom 0 c.lower = true) :
    scaledLowerCheck num den rows c.lower c.diag = true ↔
      ∀ i j : Fin n, j ≤ i → v i j = (c.L n * diagonal (c.d n) * (c.L n)ᵀ) i j := by
  -- the integer dot product of scaled rows `i` and `j` is the scaled entry of the product
  have hdot : ∀ i j : Fin n,
      ((rowDot (List.zipWith (· * ·) (scaleRow (denLcm (c.lower.getD i [])) (c.lower.getD i []))
          (scaleRow (denLcm c.diag) c.diag))
          (scaleRow (denLcm (c.lower.getD j [])) (c.lower.getD j [])) : ℤ) : ℚ) =
        ((denLcm (c.lower.getD i []) * denLcm (c.lower.getD j []) * denLcm c.diag : ℕ) : ℚ) *
          (c.L n * diagonal (c.d n) * (c.L n)ᵀ) i j := by
    intro i j
    rw [rowDot_eq_sum (n := n) _ (by simp [scaleRow, hdlen]), mul_diagonal_mul_transpose_apply,
      Finset.mul_sum]
    simp only [getD_zipWith_mul, Int.cast_sum, Int.cast_mul,
      cast_getD_scaleRow (fun _ hq => den_dvd_denLcm hq), L_apply, d, ofList_apply]
    push_cast
    exact Finset.sum_congr rfl fun _ _ => by ring
  have key := fun i j : Fin n => scaled_eq_iff (hden i j)
    (Nat.mul_pos (Nat.mul_pos (denLcm_pos _) (denLcm_pos _)) (denLcm_pos _)) (hval i j) (hdot i j)
  simp only [scaledLowerCheck, all_zip_iff, List.length_map, List.getElem_map, List.length_take,
    List.getElem_take, beq_iff_eq]
  have hrowlen : ∀ i (hi : i < c.lower.length), (scaleRow (denLcm c.lower[i]) c.lower[i]).length =
      i + 1 := fun i hi => by simpa [scaleRow] using (unitLowerFrom_iff.1 hl i hi).1
  -- entry `(i, j)` of the check, read by position
  have hkey : ∀ (i j : Fin n) (hi : (i : ℕ) < rows.length) (hj : (j : ℕ) < rows[(i : ℕ)].length)
      (hi' : (i : ℕ) < c.lower.length) (hj' : (j : ℕ) < c.lower.length),
      num rows[(i : ℕ)][(j : ℕ)] *
          ((denLcm c.lower[(i : ℕ)] * denLcm c.lower[(j : ℕ)] * denLcm c.diag : ℕ) : ℤ) =
        rowDot (List.zipWith (· * ·) (scaleRow (denLcm c.lower[(i : ℕ)]) c.lower[(i : ℕ)])
            (scaleRow (denLcm c.diag) c.diag))
            (scaleRow (denLcm c.lower[(j : ℕ)]) c.lower[(j : ℕ)]) * den rows[(i : ℕ)][(j : ℕ)] ↔
        v i j = (c.L n * diagonal (c.d n) * (c.L n)ᵀ) i j := by
    intro i j hi hj hi' hj'
    have := key i j
    rwa [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hi',
      List.getD_eq_getElem _ _ hj'] at this
  constructor
  · intro h i j hji
    have hi : (i : ℕ) < rows.length := hrows ▸ i.is_lt
    have hj : (j : ℕ) < rows[(i : ℕ)].length := (hrow _ (List.getElem_mem hi)).symm ▸ j.is_lt
    have hi' : (i : ℕ) < c.lower.length := hlen ▸ i.is_lt
    have hji' : (j : ℕ) ≤ i := hji
    exact (hkey i j hi hj hi' (hlen ▸ j.is_lt)).1
      (h i hi hi' j (by rw [hrowlen i hi']; omega) (hlen ▸ j.is_lt))
  · intro h i hi hi' j hj hj'
    rw [hrowlen i hi'] at hj
    have hn : i < n := hlen ▸ hi'
    have hri := hrow _ (List.getElem_mem hi)
    exact (hkey ⟨i, hn⟩ ⟨j, by omega⟩ hi (by simp only; omega) hi' hj').2
      (h ⟨i, hn⟩ ⟨j, by omega⟩ (by simp only [Fin.mk_le_mk]; omega))

/-- An accepted lower-triangle check factors every symmetric matrix `v` whose entries the rows
give as `num x / den x`. -/
private theorem eq_of_factorsLower {β : Type*} [Zero β] {num : β → ℤ} {den : β → ℕ}
    {rows : List (List β)} {v : Matrix (Fin n) (Fin n) ℚ}
    (hval : ∀ i j : Fin n,
      (num ((rows.getD i []).getD j 0) : ℚ) = v i j * den ((rows.getD i []).getD j 0))
    (hden : ∀ i j : Fin n, 0 < den ((rows.getD i []).getD j 0)) (hsymm : vᵀ = v)
    (h : c.factorsLower num den n rows = true) : v = c.L n * diagonal (c.d n) * (c.L n)ᵀ := by
  simp only [factorsLower, isShape, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hrows, hrow⟩, hlen⟩, hdlen⟩, hl⟩, hcheck⟩ := h
  have hlow := (c.scaledLowerCheck_iff hval hden hrows hrow hlen hdlen hl).1 hcheck
  ext i j
  rcases le_total j i with hji | hij
  · exact hlow i j hji
  · have h₁ := congrFun (congrFun hsymm i) j
    have h₂ := congrFun (congrFun c.transpose_LDLt i) j
    rw [transpose_apply] at h₁ h₂
    rw [← h₁, hlow j i hij, h₂]

/-- An accepted witness factors the matrix: `M = L * diagonal d * Lᵀ` over `ℚ`. -/
theorem eq_of_factors {rows : List (List ℚ)} (h : c.factors n rows = true) :
    ofLists n n rows = c.L n * diagonal (c.d n) * (c.L n)ᵀ := by
  simp only [factors, Bool.and_eq_true, beq_iff_eq] at h
  refine c.eq_of_factorsLower (fun i j => ?_) (fun i j => Rat.den_pos _) ?_ h.2
  · rw [ofLists_apply, ofList_apply, Rat.mul_den_eq_num]
  · rw [← ofLists_transpose, h.1]

/-- Casting a product of rational matrices to `ℝ`. -/
private theorem map_ratCast_mul {l m k : ℕ} (A : Matrix (Fin l) (Fin m) ℚ)
    (B : Matrix (Fin m) (Fin k) ℚ) :
    (A * B).map ((↑) : ℚ → ℝ) = A.map ((↑) : ℚ → ℝ) * B.map ((↑) : ℚ → ℝ) :=
  Matrix.map_mul (f := Rat.castHom ℝ)

/-- The real form of a factorization by a well-formed witness, with `L` unit lower
triangular. -/
private theorem map_eq_of_eq {v : Matrix (Fin n) (Fin n) ℚ} (hlen : c.lower.length = n)
    (hdlen : c.diag.length = n) (hl : unitLowerFrom 0 c.lower = true)
    (hM : v = c.L n * diagonal (c.d n) * (c.L n)ᵀ) :
    (∀ i, c.d n i ∈ c.diag) ∧
      ∃ L : Matrix (Fin n) (Fin n) ℝ, L.IsLowerTriangular ∧ (∀ i, L i i = 1) ∧
        v.map ((↑) : ℚ → ℝ) = L * diagonal (fun i => (c.d n i : ℝ)) * Lᴴ := by
  refine ⟨fun i => ?_, (c.L n).map (↑), fun i j hij => ?_, fun i => ?_, ?_⟩
  · have hi : (i : ℕ) < c.diag.length := hdlen ▸ i.is_lt
    rw [d, ofList_apply, List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  · rw [map_apply, isLowerTriangular_L hlen hl hij, Rat.cast_zero]
  · rw [map_apply, L_apply_self hlen hl i, Rat.cast_one]
  · rw [conjTranspose_eq_transpose_of_trivial, hM, map_ratCast_mul, map_ratCast_mul,
      diagonal_map Rat.cast_zero, transpose_map]

/-- A well-formed witness with positive diagonal proves the matrix it factors positive
definite over `ℝ`. -/
private theorem posDef_of_eq {v : Matrix (Fin n) (Fin n) ℚ} (hlen : c.lower.length = n)
    (hdlen : c.diag.length = n) (hl : unitLowerFrom 0 c.lower = true)
    (hd : c.diag.all (0 < ·) = true) (hM : v = c.L n * diagonal (c.d n) * (c.L n)ᵀ) :
    (v.map ((↑) : ℚ → ℝ)).PosDef := by
  simp only [List.all_eq_true, decide_eq_true_eq] at hd
  obtain ⟨hdmem, L, hL, h1, hM⟩ := c.map_eq_of_eq hlen hdlen hl hM
  rw [hM, posDef_mul_diagonal_mul_conjTranspose_iff hL h1]
  exact fun i => Rat.cast_pos.2 (hd _ (hdmem i))

/-- The shape facts recorded by an accepted factorization. -/
private theorem shape_of_factorsLower {β : Type*} {num : β → ℤ} {den : β → ℕ}
    {rows : List (List β)} (h : c.factorsLower num den n rows = true) :
    c.lower.length = n ∧ c.diag.length = n ∧ unitLowerFrom 0 c.lower = true := by
  simp only [factorsLower, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.2, h.1.1.2, h.1.2⟩

/-- **Soundness for `≻ 0`.** An accepted witness proves the matrix positive definite over
`ℝ`. -/
theorem posDef_of_checkPosDef {rows : List (List ℚ)} (h : c.checkPosDef n rows = true) :
    ((ofLists n n rows).map ((↑) : ℚ → ℝ)).PosDef := by
  simp only [checkPosDef, Bool.and_eq_true] at h
  have hs := c.shape_of_factorsLower (by simp only [factors, Bool.and_eq_true] at h; exact h.1.2)
  exact c.posDef_of_eq hs.1 hs.2.1 hs.2.2 h.2 (c.eq_of_factors h.1)

/-- **Soundness for `⪰ 0`.** An accepted witness proves the matrix positive semidefinite over
`ℝ`, including a singular one, whose witnesses have some `d i = 0`. -/
theorem posSemidef_of_checkPosSemidef {rows : List (List ℚ)}
    (h : c.checkPosSemidef n rows = true) :
    ((ofLists n n rows).map ((↑) : ℚ → ℝ)).PosSemidef := by
  simp only [checkPosSemidef, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  have hs := c.shape_of_factorsLower (by simp only [factors, Bool.and_eq_true] at h; exact h.1.2)
  obtain ⟨hdmem, L, hL, h1, hM⟩ := c.map_eq_of_eq hs.1 hs.2.1 hs.2.2 (c.eq_of_factors h.1)
  rw [hM, posSemidef_mul_diagonal_mul_conjTranspose_iff hL h1]
  exact fun i => Rat.cast_nonneg.2 (h.2 _ (hdmem i))

/-! ### Completeness -/

/-- Each row of `ListMatrix.transpose n rows` has one entry per row of `rows`. -/
private theorem length_of_mem_transpose {α : Type*} [Zero α] (n : ℕ) (rows : List (List α)) :
    ∀ r ∈ ListMatrix.transpose n rows, r.length = rows.length := by
  induction rows with
  | nil => simp [ListMatrix.transpose]
  | cons row rows ih =>
    intro r hr
    simp only [ListMatrix.transpose, ListMatrix.consPad_eq_zipWith, List.mem_iff_getElem,
      List.length_zipWith, List.getElem_zipWith] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    simp [ih _ (List.getElem_mem _)]

/-- Two lists of `m` rows of `n` entries with the same matrix are equal. -/
private theorem eq_of_ofLists_eq {α : Type*} [Zero α] {m k : ℕ} {A B : List (List α)}
    (hA : isShape m k A = true) (hB : isShape m k B = true) (h : ofLists m k A = ofLists m k B) :
    A = B := by
  simp only [isShape, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hA hB
  refine List.ext_getElem (hA.1.trans hB.1.symm) fun i hiA hiB => ?_
  have hAi := hA.2 _ (List.getElem_mem hiA)
  have hBi := hB.2 _ (List.getElem_mem hiB)
  refine List.ext_getElem (hAi.trans hBi.symm) fun j hjA hjB => ?_
  have := congrFun (congrFun h ⟨i, hA.1 ▸ hiA⟩) ⟨j, hAi ▸ hjA⟩
  simp only [ofLists_apply, ofList_apply] at this
  rwa [List.getD_eq_getElem _ _ hiA, List.getD_eq_getElem _ _ hiB, List.getD_eq_getElem _ _ hjA,
    List.getD_eq_getElem _ _ hjB] at this

/-- A well-formed witness whose product is the matrix of `n` rows of `n` entries is accepted:
the converse of `LDLCert.eq_of_factors`. -/
private theorem factors_of_eq {rows : List (List ℚ)} (hshape : isShape n n rows = true)
    (hlen : c.lower.length = n) (hdlen : c.diag.length = n) (hl : unitLowerFrom 0 c.lower = true)
    (hM : ofLists n n rows = c.L n * diagonal (c.d n) * (c.L n)ᵀ) : c.factors n rows = true := by
  have hs := hshape
  simp only [isShape, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hs
  have hT : isShape n n (ListMatrix.transpose n rows) = true := by
    simp only [isShape, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
      ListMatrix.length_transpose, true_and]
    exact fun r hr => (length_of_mem_transpose n rows r hr).trans hs.1
  simp only [factors, factorsLower, hshape, hlen, hdlen, hl, Bool.and_eq_true, beq_iff_eq,
    and_true, true_and]
  refine ⟨eq_of_ofLists_eq hT hshape ?_, (c.scaledLowerCheck_iff (v := ofLists n n rows)
    (fun i j => ?_) (fun _ _ => Rat.den_pos _) hs.1 hs.2 hlen hdlen hl).2 fun i j _ => by rw [hM]⟩
  · rw [ofLists_transpose, hM, c.transpose_LDLt]
  · rw [ofLists_apply, ofList_apply, Rat.mul_den_eq_num]

/-- The witness listing `L` and `d`: row `i` of `lower` holds `L i 0, …, L i i`. -/
private def ofFactors (L : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ) : LDLCert where
  lower := List.ofFn fun i : Fin n => List.ofFn fun j : Fin (i + 1) => L i (Fin.castLE i.is_lt j)
  diag := List.ofFn d

/-- The witness of a unit lower-triangular `L` and a diagonal `d` is well formed and has factors
`L` and `d`. -/
private theorem ofFactors_spec {L : Matrix (Fin n) (Fin n) ℚ} {d : Fin n → ℚ}
    (hL : L.IsLowerTriangular) (h1 : ∀ i, L i i = 1) :
    (ofFactors L d).lower.length = n ∧ (ofFactors L d).diag.length = n ∧
      unitLowerFrom 0 (ofFactors L d).lower = true ∧ (ofFactors L d).L n = L ∧
      (ofFactors L d).d n = d := by
  refine ⟨by simp [ofFactors], by simp [ofFactors], unitLowerFrom_iff.2 fun k hk => ?_, ?_, ?_⟩
  · simp only [ofFactors, List.length_ofFn] at hk
    simp only [ofFactors, List.getElem_ofFn, List.length_ofFn, zero_add,
      List.getLast?_eq_getElem?, Nat.add_sub_cancel, List.getElem?_ofFn, true_and]
    simp [Fin.castLE, h1 ⟨k, hk⟩]
  · ext i j
    have hrow : (ofFactors L d).lower.getD i [] =
        List.ofFn fun j : Fin (i + 1) => L i (Fin.castLE i.is_lt j) := by
      simp [ofFactors]
    rw [L_apply, hrow]
    rcases Nat.lt_or_ge (j : ℕ) (i + 1) with hj | hj
    · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]
      rfl
    · rw [List.getD_eq_default _ _ (by simpa using hj), hL (show i < j by rw [Fin.lt_def]; omega)]
  · ext i
    simp [LDLCert.d, ofFactors]

/-- **Completeness for `⪰ 0`.** Some witness is accepted exactly when `rows` lists `n` rows of
`n` entries and the matrix is positive semidefinite over `ℝ`, singular or not
(`Matrix.exists_LDL_of_posSemidef`). A rejected witness therefore says nothing about the matrix,
but the absence of any accepted witness for a well-shaped `rows` refutes `⪰ 0`. -/
theorem exists_checkPosSemidef_iff {rows : List (List ℚ)} :
    (∃ c : LDLCert, c.checkPosSemidef n rows = true) ↔
      isShape n n rows = true ∧ ((ofLists n n rows).map ((↑) : ℚ → ℝ)).PosSemidef := by
  constructor
  · rintro ⟨c, h⟩
    refine ⟨?_, c.posSemidef_of_checkPosSemidef h⟩
    simp only [checkPosSemidef, factors, factorsLower, Bool.and_eq_true] at h
    exact h.1.2.1.1.1.1
  · rintro ⟨hshape, hM⟩
    obtain ⟨L, d, hL, h1, hd, hLd⟩ := exists_LDL_of_posSemidef (posSemidef_of_map_ratCast hM)
    obtain ⟨hlen, hdlen, hl, hLL, hdd⟩ := ofFactors_spec (d := d) hL h1
    refine ⟨ofFactors L d, ?_⟩
    simp only [checkPosSemidef, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    refine ⟨(ofFactors L d).factors_of_eq hshape hlen hdlen hl (by rw [hLL, hdd, hLd]),
      fun x hx => ?_⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact hd i

/-- **Completeness for `≻ 0`.** Some witness is accepted exactly when `rows` lists `n` rows of
`n` entries and the matrix is positive definite over `ℝ` (`Matrix.exists_LDL_of_posDef`). -/
theorem exists_checkPosDef_iff {rows : List (List ℚ)} :
    (∃ c : LDLCert, c.checkPosDef n rows = true) ↔
      isShape n n rows = true ∧ ((ofLists n n rows).map ((↑) : ℚ → ℝ)).PosDef := by
  constructor
  · rintro ⟨c, h⟩
    refine ⟨?_, c.posDef_of_checkPosDef h⟩
    simp only [checkPosDef, factors, factorsLower, Bool.and_eq_true] at h
    exact h.1.2.1.1.1.1
  · rintro ⟨hshape, hM⟩
    obtain ⟨L, d, hL, h1, hd, hLd⟩ := exists_LDL_of_posDef (posDef_of_map_ratCast hM)
    obtain ⟨hlen, hdlen, hl, hLL, hdd⟩ := ofFactors_spec (d := d) hL h1
    refine ⟨ofFactors L d, ?_⟩
    simp only [checkPosDef, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    refine ⟨(ofFactors L d).factors_of_eq hshape hlen hdlen hl (by rw [hLL, hdd, hLd]),
      fun x hx => ?_⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact hd i

end LDLCert

/-! ### Lyapunov residuals -/

/-- The rows of `-(Aᵀ * P + P * A)` for the `n × n` matrices with rows `A` and `P`. -/
@[expose] def lyapunovResidual {α : Type*} [Ring α] (n : ℕ) (A P : List (List α)) :
    List (List α) :=
  rowsMap₂ (fun x y => -(x + y)) n n (rowsMul n n n (ListMatrix.transpose n A) P)
    (rowsMul n n n P A)

/-- `lyapunovResidual` computes `-(Aᵀ * P + P * A)`. -/
theorem ofLists_lyapunovResidual {α : Type*} [Ring α] (n : ℕ) (A P : List (List α)) :
    ofLists n n (lyapunovResidual n A P) =
      -((ofLists n n A)ᵀ * ofLists n n P + ofLists n n P * ofLists n n A) := by
  rw [lyapunovResidual, ofLists_rowsMap₂, ofLists_rowsMul, ofLists_rowsMul, ofLists_transpose]
  rfl

/-- The common scale `denLcm A * denLcm P` of the fraction-free Lyapunov residual. -/
@[expose] def lyapunovScale (A P : List (List ℚ)) : ℕ :=
  denLcm A.flatten * denLcm P.flatten

/-- The fraction-free Lyapunov residual: `-(Âᵀ * P̂ + P̂ * Â)` in integers, for `Â` and `P̂` the
rows of `A` and `P` scaled by the lcm of all their denominators. It is
`lyapunovScale A P • -(Aᵀ * P + P * A)` (`map_ofLists_scaledLyapunovResidual`). -/
@[expose] def scaledLyapunovResidual (n : ℕ) (A P : List (List ℚ)) : List (List ℤ) :=
  lyapunovResidual n (A.map (scaleRow (denLcm A.flatten))) (P.map (scaleRow (denLcm P.flatten)))

/-- Casting a product of integer matrices to `ℚ`. -/
private theorem map_intCast_mul {l m k : ℕ} (A : Matrix (Fin l) (Fin m) ℤ)
    (B : Matrix (Fin m) (Fin k) ℤ) :
    (A * B).map ((↑) : ℤ → ℚ) = A.map ((↑) : ℤ → ℚ) * B.map ((↑) : ℤ → ℚ) :=
  Matrix.map_mul (f := Int.castRingHom ℚ)

/-- The fraction-free residual agrees with `lyapunovResidual`. -/
theorem map_ofLists_scaledLyapunovResidual (n : ℕ) (A P : List (List ℚ)) :
    (ofLists n n (scaledLyapunovResidual n A P)).map ((↑) : ℤ → ℚ) =
      (lyapunovScale A P : ℚ) • ofLists n n (lyapunovResidual n A P) := by
  have hA := map_ofLists_scaleRow (m := n) (n := n) (s := denLcm A.flatten) (A := A)
    fun _ hq => den_dvd_denLcm hq
  have hP := map_ofLists_scaleRow (m := n) (n := n) (s := denLcm P.flatten) (A := P)
    fun _ hq => den_dvd_denLcm hq
  rw [scaledLyapunovResidual, ofLists_lyapunovResidual, ofLists_lyapunovResidual,
    Matrix.map_neg _ Int.cast_neg, Matrix.map_add _ Int.cast_add, map_intCast_mul,
    map_intCast_mul, transpose_map, hA, hP, lyapunovScale]
  simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, smul_neg,
    Nat.cast_mul]
  rw [mul_comm (denLcm P.flatten : ℚ)]

/-- Witnesses for the two inequalities of a quadratic Lyapunov certificate for `ẋ = A x`:
`P ≻ 0` and `-(Aᵀ * P + P * A) ≻ 0`. -/
structure LyapunovCert where
  /-- An `LDLᵀ` witness for `P`. -/
  P : LDLCert
  /-- An `LDLᵀ` witness for `-(Aᵀ * P + P * A)`. -/
  Q : LDLCert

namespace LyapunovCert

/-- Whether `c` certifies `P ≻ 0` and `-(Aᵀ * P + P * A) ≻ 0` for the `n × n` matrices with rows
`A` and `P`. The residual is recomputed from `A` and `P`, in integers
(`scaledLyapunovResidual`), and checked on and below the diagonal: it is symmetric because the
accepted `P` is. -/
@[expose] def check (c : LyapunovCert) (n : ℕ) (A P : List (List ℚ)) : Bool :=
  isShape n n A && c.P.checkPosDef n P &&
    c.Q.factorsLower id (fun _ => lyapunovScale A P) n (scaledLyapunovResidual n A P) &&
    c.Q.diag.all (0 < ·)

/-- **Soundness.** An accepted Lyapunov witness proves `P ≻ 0` and `-(Aᵀ * P + P * A) ≻ 0` for
the real matrices `A` and `P`. -/
theorem posDef_of_check {c : LyapunovCert} {n : ℕ} {A P : List (List ℚ)}
    (h : c.check n A P = true) :
    ((ofLists n n P).map ((↑) : ℚ → ℝ)).PosDef ∧
      (-(((ofLists n n A).map ((↑) : ℚ → ℝ))ᵀ * (ofLists n n P).map ((↑) : ℚ → ℝ) +
        (ofLists n n P).map ((↑) : ℚ → ℝ) * (ofLists n n A).map ((↑) : ℚ → ℝ))).PosDef := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, hP⟩, hQ⟩, hd⟩ := h
  refine ⟨c.P.posDef_of_checkPosDef hP, ?_⟩
  set R := ofLists n n (lyapunovResidual n A P) with hR
  have hσ : 0 < lyapunovScale A P := Nat.mul_pos (denLcm_pos _) (denLcm_pos _)
  -- the residual is symmetric because `P` is
  have hPs : (ofLists n n P)ᵀ = ofLists n n P := by
    have := c.P.eq_of_factors (by simp only [LDLCert.checkPosDef, Bool.and_eq_true] at hP
                                  exact hP.1)
    rw [this, LDLCert.transpose_LDLt]
  have hsymm : Rᵀ = R := by
    rw [hR, ofLists_lyapunovResidual, transpose_neg, transpose_add, transpose_mul,
      transpose_mul, transpose_transpose, hPs, add_comm]
  -- the integer rows give `σ • R`
  have hval : ∀ i j : Fin n, (((scaledLyapunovResidual n A P).getD i []).getD j 0 : ℚ) =
      R i j * lyapunovScale A P := by
    intro i j
    have := congrFun (congrFun (map_ofLists_scaledLyapunovResidual n A P) i) j
    simp only [map_apply, Matrix.smul_apply, smul_eq_mul, ofLists_apply, ofList_apply] at this
    rw [this, mul_comm, hR, ofLists_apply, ofList_apply]
  have hM := c.Q.eq_of_factorsLower (num := id) (den := fun _ => lyapunovScale A P)
    (rows := scaledLyapunovResidual n A P) (fun i j => by simpa only [id] using hval i j)
    (fun _ _ => hσ) hsymm hQ
  have hs := c.Q.shape_of_factorsLower hQ
  have hQpos := c.Q.posDef_of_eq hs.1 hs.2.1 hs.2.2 hd hM
  rw [hR, ofLists_lyapunovResidual] at hQpos
  rwa [Matrix.map_neg _ Rat.cast_neg, Matrix.map_add _ Rat.cast_add,
    LDLCert.map_ratCast_mul, LDLCert.map_ratCast_mul, transpose_map] at hQpos

end LyapunovCert

end Cslib.LinearAlgebra
