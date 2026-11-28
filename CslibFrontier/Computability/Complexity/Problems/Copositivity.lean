/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Complexity.Problems.Clique
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Copositive
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MotzkinStraus
public import CslibFrontier.Foundations.Data.Rat.Basic
public import Mathlib.Tactic.Matrix.ListMatrix
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import CslibFrontier.Computability.PolyTime.Int.DotProduct
import CslibFrontier.Computability.PolyTime.Int.ExactDiv
import CslibFrontier.Foundations.Data.List.DotProduct
import CslibFrontier.Foundations.Data.List.OfFn
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative

/-!
# CoNP-Completeness of Matrix Copositivity

Testing whether an encoded symmetric rational matrix `M` is *copositive*—meaning `x ⬝ᵥ M *ᵥ x ≥ 0`
for all entrywise nonnegative vectors `x`—is `coNP`-complete, and testing non-copositivity is
`NP`-complete. The completeness statements are credited to [MurtyKabadi1987] (secondary search
summaries indicate that [MurtyKabadi1987] proves hardness by reducing from subset sum rather than
`Clique`; the published text was not inspected). This library's `Clique`/Motzkin–Straus
reduction (`polyTimeReducible_Clique_NonCopositive`), the row-list representation `SymRatMatrix`,
binary encoding `encSymRatMatrix`, denominator-cleared verifier `NonCopositive.check`, and the
KKT/Cramer bounded integer witness derivation are original to this formalization.

By `Matrix.exists_nat_dotProduct_lt_zero_of_rat`, a symmetric rational matrix fails to be
copositive if and only if it admits a polynomially bit-bounded nonnegative integer vector `p` with
`p ⬝ᵥ M *ᵥ p < 0`. A polynomial-time verifier clears denominators by multiplying by the product
`D` of entry denominators and evaluates `p ⬝ᵥ M_int *ᵥ p < 0`, placing `NonCopositive` in `NP`
and `Copositive` in `coNP`. In the reverse direction, the Motzkin–Straus copositivity
characterization (`SimpleGraph.exists_nonneg_dotProduct_copositiveCliqueMatrix_lt_zero_iff`) gives
a polynomial-time many-one reduction from `Clique` to `NonCopositive`.

## Main definitions

- `Cslib.Complexity.SymRatMatrix`, `Cslib.Complexity.encSymRatMatrix`: symmetric rational square
  matrices represented by row lists and their binary encoding via `Turing.MultiTapeTM.encRat`.
- `Cslib.Complexity.Copositive`, `Cslib.Complexity.NonCopositive`: the copositivity and
  non-copositivity decision problems.
- `Cslib.Complexity.NonCopositive.check`: polynomial-time verifier relation for `NonCopositive`.
- `Cslib.Complexity.cliqueToSymRatMatrix`: polynomial-time reduction from `Clique` to
  `NonCopositive`.

## Main results

- `Cslib.Complexity.NonCopositive.mem_NP`, `Cslib.Complexity.Copositive.mem_coNP`: `NP` / `coNP`
  membership using the bounded nonnegative integer witness theorem.
- `Cslib.Complexity.polyTimeReducible_Clique_NonCopositive`: polynomial-time many-one reduction
  `Clique ≤ₚ NonCopositive`.
- `Cslib.Complexity.NonCopositive_npHard`, `Cslib.Complexity.NonCopositive_npComplete`:
  `NP`-completeness of `NonCopositive`.
- `Cslib.Complexity.Copositive_coNPHard`, `Cslib.Complexity.Copositive_coNPComplete`:
  `coNP`-completeness of `Copositive`.

## References

- [MotzkinStraus1965] T. S. Motzkin and E. G. Straus, *Maxima for graphs and a new proof of a
  theorem of Turán*, Canadian Journal of Mathematics 17, 1965, 533–540 (bibliographic metadata
  only; the published text is uninspected, and no internal theorem numbers are claimed).
- [MurtyKabadi1987] K. G. Murty and S. N. Kabadi, *Some NP-complete problems in quadratic and
  nonlinear programming*, Mathematical Programming 39(2), 1987, 117–129 (bibliographic metadata
  only; the published text is uninspected, and no internal theorem numbers are claimed).
-/

public section

namespace Cslib.Complexity

open Matrix Turing.MultiTapeTM

/-! ### Symmetric rational matrix encoding -/

/-- Binary encoding of a rational matrix row list. -/
abbrev encRatMatrixRows : List (List ℚ) ↪ List Bool :=
  encList (encList encRat)

/-- A square symmetric rational matrix represented by its list of rows. -/
structure SymRatMatrix where
  /-- The rows of the matrix. -/
  rows : List (List ℚ)
  /-- Every row has length equal to the number of rows. -/
  square : ∀ r ∈ rows, r.length = rows.length
  /-- Symmetry of entries under index transposition. -/
  symm : ∀ i j, (rows.getD i []).getD j 0 = (rows.getD j []).getD i 0

@[ext]
theorem SymRatMatrix.ext {M₁ M₂ : SymRatMatrix} (h : M₁.rows = M₂.rows) : M₁ = M₂ := by
  cases M₁
  cases M₂
  simp only [SymRatMatrix.mk.injEq]
  exact h

/-- Binary encoding of symmetric rational matrices via their row lists. -/
@[expose] def encSymRatMatrix : SymRatMatrix ↪ List Bool where
  toFun M := encRatMatrixRows M.rows
  inj' _ _ h := SymRatMatrix.ext (encRatMatrixRows.injective h)

/-- Binary encoding of `(M, p)` pairs for `NonCopositive` verification. -/
abbrev encSymRatMatrixWitness : SymRatMatrix × List ℕ ↪ List Bool :=
  encPair encSymRatMatrix (encList encNat)

/-- Interpret a `SymRatMatrix` as an `n × n` `Matrix` over `ℚ`, where `n = M.rows.length`. -/
@[expose] def SymRatMatrix.toMatrix (M : SymRatMatrix) :
    Matrix (Fin M.rows.length) (Fin M.rows.length) ℚ :=
  Matrix.of fun i j => (M.rows.getD i []).getD j 0

theorem SymRatMatrix.isSymm_toMatrix (M : SymRatMatrix) : M.toMatrix.IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, SymRatMatrix.toMatrix, Matrix.of_apply]
  exact M.symm j i

/-- The language of symmetric rational matrices that are copositive. -/
@[expose] def Copositive : Set SymRatMatrix :=
  {M | M.toMatrix.IsCopositive}

/-- The language of symmetric rational matrices that are not copositive. -/
@[expose] def NonCopositive : Set SymRatMatrix :=
  {M | ¬ M.toMatrix.IsCopositive}

theorem mem_Copositive_iff {M : SymRatMatrix} : M ∈ Copositive ↔ M.toMatrix.IsCopositive :=
  Iff.rfl

theorem mem_NonCopositive_iff {M : SymRatMatrix} : M ∈ NonCopositive ↔ ¬ M.toMatrix.IsCopositive :=
  Iff.rfl

theorem NonCopositive_eq_compl : NonCopositive = Copositiveᶜ := rfl

theorem Copositive_eq_compl : Copositive = NonCopositiveᶜ := by
  ext M
  simp only [Set.mem_compl_iff, mem_Copositive_iff, mem_NonCopositive_iff, not_not]

/-- Copositivity of a `SymRatMatrix` over `ℚ` coincides with copositivity over `ℝ`. -/
theorem mem_Copositive_iff_real {M : SymRatMatrix} :
    M ∈ Copositive ↔ (M.toMatrix.map (Rat.cast : ℚ → ℝ)).IsCopositive :=
  Matrix.isCopositive_rat_iff_map_real M.isSymm_toMatrix

/-! ### NP verifier for non-copositivity -/

/-- Common denominator for all entries of a rational matrix `M`: the product of its denominators. -/
@[expose] def SymRatMatrix.commonDenom (M : SymRatMatrix) : ℤ :=
  (M.rows.flatten.map fun q : ℚ => (q.den : ℤ)).prod

/-- Integerized matrix obtained by multiplying each entry of `M` by `M.commonDenom`. -/
@[expose] def SymRatMatrix.intRows (M : SymRatMatrix) : List (List ℤ) :=
  let D := M.commonDenom
  M.rows.map fun r => r.map fun q => q.num * (D / (q.den : ℤ))

/-- Polynomial-time verifier relation for `NonCopositive`: `p` has length `M.rows.length` and
`p ⬝ᵥ M.intRows *ᵥ p < 0`. -/
@[expose] def NonCopositive.check (M : SymRatMatrix) (p : List ℕ) : Bool :=
  let M_int := M.intRows
  let p_int : List ℤ := p.map Nat.cast
  let quad : ℤ :=
    Mathlib.Tactic.Matrix.ListMatrix.dotProduct M.rows.length p_int
      (M_int.map fun row =>
        Mathlib.Tactic.Matrix.ListMatrix.dotProduct M.rows.length row p_int)
  decide (p.length = M.rows.length) && decide (quad < 0)

private def SymRatMatrix.commonDenomNat (M : SymRatMatrix) : ℕ :=
  (M.rows.flatten.map fun q : ℚ => q.den).prod

private theorem SymRatMatrix.commonDenomNat_pos (M : SymRatMatrix) : 0 < M.commonDenomNat :=
  List.prod_pos fun _ hx => by
    obtain ⟨q, _, rfl⟩ := List.mem_map.1 hx
    exact q.pos

private theorem SymRatMatrix.commonDenom_eq_nat (M : SymRatMatrix) :
    M.commonDenom = (M.commonDenomNat : ℤ) := by
  dsimp only [SymRatMatrix.commonDenom, SymRatMatrix.commonDenomNat]
  rw [Nat.cast_list_prod (R := ℤ), List.map_map]
  rfl

private theorem SymRatMatrix.toMatrix_eq_getElem (M : SymRatMatrix) (i j : Fin M.rows.length) :
    M.toMatrix i j =
      M.rows[i.1][j.1]'(by rw [M.square _ (List.getElem_mem i.2)]; exact j.2) := by
  have hj_lt : j.1 < M.rows[i.1].length := by
    rw [M.square _ (List.getElem_mem i.2)]
    exact j.2
  dsimp only [SymRatMatrix.toMatrix, Matrix.of_apply]
  rw [List.getD_eq_getElem _ _ i.2, List.getD_eq_getElem _ _ hj_lt]

private theorem SymRatMatrix.den_dvd_commonDenomNat (M : SymRatMatrix)
    {i j : Fin M.rows.length} :
    (M.toMatrix i j).den ∣ M.commonDenomNat := by
  have hi : M.rows[i.1] ∈ M.rows := List.getElem_mem i.2
  have hj_lt : j.1 < M.rows[i.1].length := by
    rw [M.square _ hi]
    exact j.2
  have hmem_row : M.rows[i.1][j.1] ∈ M.rows[i.1] := List.getElem_mem hj_lt
  have hmem_flat : M.rows[i.1][j.1] ∈ M.rows.flatten :=
    List.mem_flatten.2 ⟨M.rows[i.1], hi, hmem_row⟩
  rw [M.toMatrix_eq_getElem i j]
  exact List.dvd_prod (List.mem_map.2 ⟨M.rows[i.1][j.1], hmem_flat, rfl⟩)

private noncomputable def SymRatMatrix.intMatrix (M : SymRatMatrix) :
    Matrix (Fin M.rows.length) (Fin M.rows.length) ℤ :=
  Matrix.of fun i j => (M.intRows.getD i []).getD j 0

private theorem SymRatMatrix.intMatrix_eq (M : SymRatMatrix) (i j : Fin M.rows.length) :
    M.intMatrix i j =
      (M.toMatrix i j).num * ((M.commonDenomNat / (M.toMatrix i j).den : ℕ) : ℤ) := by
  have hi_int : i.1 < M.intRows.length := by simp [SymRatMatrix.intRows]
  have hj_int : j.1 < M.intRows[i.1].length := by
    simp [SymRatMatrix.intRows, M.square _ (List.getElem_mem i.2)]
  dsimp only [SymRatMatrix.intMatrix, Matrix.of_apply]
  rw [List.getD_eq_getElem _ _ hi_int, List.getD_eq_getElem _ _ hj_int]
  simp only [SymRatMatrix.intRows, List.getElem_map]
  rw [← M.toMatrix_eq_getElem i j, M.commonDenom_eq_nat, Int.natCast_ediv]

private theorem SymRatMatrix.intMatrix_mul_eq (M : SymRatMatrix)
    (i j : Fin M.rows.length) :
    (M.commonDenomNat : ℚ) * M.toMatrix i j = (M.intMatrix i j : ℚ) := by
  rw [M.intMatrix_eq i j]
  exact Rat.clearDenom_entry M.den_dvd_commonDenomNat

private theorem SymRatMatrix.dotProduct_check_eq (M : SymRatMatrix) {p : List ℕ}
    (hlen : p.length = M.rows.length) :
    let pFin : Fin M.rows.length → ℕ := fun i => p.getD i.1 0
    Mathlib.Tactic.Matrix.ListMatrix.dotProduct M.rows.length (p.map Nat.cast)
        (M.intRows.map fun row =>
          Mathlib.Tactic.Matrix.ListMatrix.dotProduct M.rows.length row (p.map Nat.cast)) =
      (fun i => (pFin i : ℤ)) ⬝ᵥ (M.intMatrix *ᵥ fun i => (pFin i : ℤ)) := by
  intro pFin
  have hp_ofFn :
      (p.map Nat.cast : List ℤ) = List.ofFn fun i : Fin M.rows.length => (pFin i : ℤ) := by
    refine List.ext_getElem (by simp [hlen]) fun k hk1 _ => ?_
    have hk_lt : k < p.length := by simpa using hk1
    simp only [List.getElem_map, List.getElem_ofFn, pFin]
    rw [List.getD_eq_getElem _ _ hk_lt]
  have hrows_ofFn :
      (M.intRows.map fun row =>
          Mathlib.Tactic.Matrix.ListMatrix.dotProduct M.rows.length row (p.map Nat.cast)) =
        List.ofFn fun i : Fin M.rows.length => (M.intMatrix *ᵥ fun j => (pFin j : ℤ)) i := by
    refine List.ext_getElem (by simp [SymRatMatrix.intRows]) fun k hk1 _ => ?_
    have hk_lt : k < M.rows.length := by simpa [SymRatMatrix.intRows] using hk1
    have hrow_len : M.rows[k].length = M.rows.length := M.square _ (List.getElem_mem hk_lt)
    have hrow_ofFn :
        M.intRows[k]'(by simpa [SymRatMatrix.intRows] using hk_lt) =
          List.ofFn fun j : Fin M.rows.length => M.intMatrix ⟨k, hk_lt⟩ j := by
      refine List.ext_getElem (by simp [SymRatMatrix.intRows, hrow_len]) fun j _ hj2 => ?_
      have hk_int : k < M.intRows.length := by simpa [SymRatMatrix.intRows] using hk_lt
      have hj_int : j < M.intRows[k].length := by
        simpa [SymRatMatrix.intRows, hrow_len] using hj2
      simp only [List.getElem_ofFn, SymRatMatrix.intMatrix, Matrix.of_apply]
      rw [List.getD_eq_getElem _ _ hk_int, List.getD_eq_getElem _ _ hj_int]
    simp only [List.getElem_map, List.getElem_ofFn, Matrix.mulVec]
    rw [hrow_ofFn, hp_ofFn]
    exact Mathlib.Tactic.Matrix.ListMatrix.dotProduct_ofFn _ _
  rw [hrows_ofFn, hp_ofFn]
  exact Mathlib.Tactic.Matrix.ListMatrix.dotProduct_ofFn _ _

private theorem SymRatMatrix.dotProduct_scale (M : SymRatMatrix) (pFin : Fin M.rows.length → ℕ) :
    (M.commonDenomNat : ℚ) *
        ((fun i => (pFin i : ℚ)) ⬝ᵥ (M.toMatrix *ᵥ fun i => (pFin i : ℚ))) =
      (((fun i => (pFin i : ℤ)) ⬝ᵥ (M.intMatrix *ᵥ fun i => (pFin i : ℤ)) : ℤ) : ℚ) := by
  rw [Matrix.dotProduct_scale_of_eq (M₂ := M.intMatrix.map (Int.cast : ℤ → ℚ))
    (fun i j => by simpa only [Matrix.map_apply] using M.intMatrix_mul_eq i j),
    Matrix.intCast_dotProduct_mulVec_nat]

private theorem NonCopositive.sound_of_check {M : SymRatMatrix} {p : List ℕ}
    (hc : NonCopositive.check M p = true) : M ∈ NonCopositive := by
  simp only [NonCopositive.check, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hlen, hquad⟩ := hc
  rw [SymRatMatrix.dotProduct_check_eq M hlen] at hquad
  set pFin : Fin M.rows.length → ℕ := fun i => p.getD i.1 0
  have hnegQ :
      (M.commonDenomNat : ℚ) *
          ((fun i => (pFin i : ℚ)) ⬝ᵥ (M.toMatrix *ᵥ fun i => (pFin i : ℚ))) < 0 := by
    rw [M.dotProduct_scale pFin]
    exact Int.cast_lt_zero.2 hquad
  have hneg : (fun i => (pFin i : ℚ)) ⬝ᵥ (M.toMatrix *ᵥ fun i => (pFin i : ℚ)) < 0 :=
    lt_of_not_ge fun hge =>
      not_lt_of_ge (mul_nonneg (Nat.cast_nonneg _) hge) hnegQ
  intro hcop
  exact (not_lt_of_ge (hcop (fun i => (pFin i : ℚ)) fun i => Nat.cast_nonneg _)) hneg

private theorem natAbs_le_two_pow_encIntBin (z : ℤ) : z.natAbs ≤ 2 ^ (encIntBin z).length := by
  have h := Nat.lt_size_self z.natAbs
  have hlen : z.natAbs.size ≤ (encIntBin z).length := by
    rw [length_encIntBin]
    exact Nat.le_succ _
  exact (h.le).trans (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hlen)

private theorem nat_le_two_pow_encNat (n : ℕ) : n ≤ 2 ^ (encNat n).length := by
  have h := Nat.lt_size_self n
  have hlen : n.size = (encNat n).length := by simp only [encNat_apply, Nat.size_eq_bits_len]
  rw [← hlen]
  exact h.le

private theorem list_prod_le_two_pow_sum {α : Type*} (l : List α) (f w : α → ℕ)
    (hf : ∀ a ∈ l, f a ≤ 2 ^ w a) : (l.map f).prod ≤ 2 ^ (l.map w).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, List.sum_nil, pow_zero, le_rfl]
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, pow_add]
      exact Nat.mul_le_mul (hf a List.mem_cons_self)
        (ih fun x hx => hf x (List.mem_cons_of_mem a hx))

private theorem sum_encRat_flatten_le_rows (rows : List (List ℚ)) :
    (rows.flatten.map fun q => (encRat q).length).sum ≤ (encList (encList encRat) rows).length := by
  refine le_trans ?_ (sum_length_le_length_encList (encList encRat) rows)
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.flatten_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    exact Nat.add_le_add (sum_length_le_length_encList encRat r) ih

private theorem NonCopositive.complete_of_mem {M : SymRatMatrix} (hM : M ∈ NonCopositive) :
    ∃ p : List ℕ,
      NonCopositive.check M p = true ∧
        (encList encNat p).length ≤
          ((Polynomial.X * (16 * (Polynomial.X + 1) ^ 2 + 3)).eval (encSymRatMatrix M).length) := by
  set L := (encSymRatMatrix M).length
  set n := M.rows.length
  have hn_le_L : n ≤ L := by
    change M.rows.length ≤ (encList (encList encRat) M.rows).length
    exact SizedListEncoding.length_le (encA := encList encRat) M.rows
  have hden_le : M.commonDenomNat ≤ 2 ^ L := by
    refine (list_prod_le_two_pow_sum M.rows.flatten (fun q => q.den) (fun q => (encRat q).length)
      fun q _ => (nat_le_two_pow_encNat q.den).trans
        (Nat.pow_le_pow_right (by omega) (length_encRat_den_le q))).trans ?_
    exact Nat.pow_le_pow_right (by omega) (sum_encRat_flatten_le_rows M.rows)
  have hB : ∀ i j : Fin n, |M.intMatrix i j| ≤ ((2 ^ (2 * L) : ℕ) : ℤ) := fun i j => by
    have hi : M.rows[i.1] ∈ M.rows := List.getElem_mem i.2
    have hj_lt : j.1 < M.rows[i.1].length := by rw [M.square _ hi]; exact j.2
    have hq_enc : (encRat (M.toMatrix i j)).length ≤ L := by
      rw [M.toMatrix_eq_getElem i j]
      exact (SizedListEncoding.length_elem_le (encA := encRat) _ _ (List.getElem_mem hj_lt)).trans
        (show (encList encRat M.rows[i.1]).length ≤ (encList (encList encRat) M.rows).length from
          SizedListEncoding.length_elem_le (encA := encList encRat) M.rows _ hi)
    have hnum_le : (M.toMatrix i j).num.natAbs ≤ 2 ^ L :=
      (natAbs_le_two_pow_encIntBin _).trans
        (Nat.pow_le_pow_right (by omega) ((length_encRat_num_le _).trans hq_enc))
    rw [M.intMatrix_eq i j, abs_mul, abs_of_nonneg (Int.natCast_nonneg _), ← Int.natCast_natAbs,
      ← Int.natCast_mul]
    exact Int.ofNat_le.2 ((Nat.mul_le_mul hnum_le ((Nat.div_le_self _ _).trans hden_le)).trans_eq
      (by rw [← pow_add, two_mul]))
  obtain ⟨pFin, hpFin_le, hpFin_neg⟩ :=
    Matrix.exists_nat_dotProduct_lt_zero_of_rat M.commonDenomNat_pos M.isSymm_toMatrix
      M.intMatrix_mul_eq hB hM
  simp only [Fintype.card_fin] at hpFin_le
  let p : List ℕ := List.ofFn pFin
  have hp_len : p.length = n := List.length_ofFn
  have hcheck : NonCopositive.check M p = true := by
    simp only [NonCopositive.check, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hp_len, ?_⟩
    rw [SymRatMatrix.dotProduct_check_eq M hp_len]
    have hp_getD : (fun i : Fin M.rows.length => p.getD i.1 0) = pFin :=
      funext fun i => by simp [p, List.getD_eq_getElem?_getD, i.2]
    rw [hp_getD, ← Int.cast_lt (R := ℚ), Int.cast_zero, ← M.dotProduct_scale pFin]
    exact mul_neg_of_pos_of_neg (Nat.cast_pos.2 M.commonDenomNat_pos) hpFin_neg
  refine ⟨p, hcheck, ?_⟩
  have hpow_elem : ∀ a ∈ p, (encNat a).length ≤ 8 * (L + 1) ^ 2 + 1 := fun a ha => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
    have hn2 : n ≤ 2 ^ L := hn_le_L.trans Nat.lt_two_pow_self.le
    have hle1 : Nat.factorial n ≤ 2 ^ (L ^ 2) :=
      (Nat.factorial_le_pow n).trans <| (Nat.pow_le_pow_left hn2 n).trans <|
        (pow_mul 2 L n).symm.trans_le <| Nat.pow_le_pow_right (by omega) <|
          (Nat.mul_le_mul_left L hn_le_L).trans_eq (sq L).symm
    have hbase : n * (2 ^ (2 * L)) ^ 2 + 1 ≤ 2 ^ (5 * L + 1) := by
      calc n * (2 ^ (2 * L)) ^ 2 + 1
          ≤ 2 ^ L * 2 ^ (4 * L) + 2 ^ (5 * L) :=
            Nat.add_le_add (by
              rw [← pow_mul, show 2 * L * 2 = 4 * L by ring]
              exact Nat.mul_le_mul_right _ hn2) Nat.one_le_two_pow
        _ = 2 ^ (5 * L + 1) := by rw [← pow_add, show L + 4 * L = 5 * L by ring, pow_succ]; ring
    have hle2 : (n * (max (2 ^ (2 * L)) 1) ^ 2 + 1) ^ n ≤ 2 ^ (6 * L ^ 2 + L) := by
      rw [max_eq_left Nat.one_le_two_pow]
      exact (Nat.pow_le_pow_left hbase n).trans <| (pow_mul 2 _ n).symm.trans_le <|
        Nat.pow_le_pow_right (by omega) <| (Nat.mul_le_mul_left _ hn_le_L).trans (by nlinarith)
    have hlt_pow : pFin i < 2 ^ (8 * (L + 1) ^ 2 + 1) :=
      ((hpFin_le i).trans (Nat.mul_le_mul hle1 hle2)).trans_lt <| by
        rw [← pow_add]; exact Nat.pow_lt_pow_right (by omega) (by nlinarith)
    simp only [encNat_apply, Nat.size_eq_bits_len]
    exact Nat.size_le.2 hlt_pow
  refine (length_encList_le encNat p hpow_elem).trans ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_add,
    Polynomial.eval_ofNat, Polynomial.eval_pow, Polynomial.eval_one, hp_len]
  exact (Nat.mul_le_mul_right _ hn_le_L).trans_eq' (by ring)

theorem NonCopositive.exists_check_eq_true_iff (M : SymRatMatrix) :
    (∃ p : List ℕ, NonCopositive.check M p = true) ↔ M ∈ NonCopositive :=
  ⟨fun ⟨_, hp⟩ => NonCopositive.sound_of_check hp, fun hM =>
    let ⟨p, hp, _⟩ := NonCopositive.complete_of_mem hM; ⟨p, hp⟩⟩

@[local fun_prop]
private theorem computableInPolyTime_rows :
    ComputableInPolyTime SymRatMatrix.rows encSymRatMatrix encRatMatrixRows :=
  ComputableInPolyTime.of_eq (f := SymRatMatrix.rows)
    (encIn := encSymRatMatrix) (encOut := encRatMatrixRows) fun _ => rfl

@[local fun_prop]
private theorem computableInPolyTime_commonDenom :
    ComputableInPolyTime SymRatMatrix.commonDenom encSymRatMatrix encIntBin := by
  unfold SymRatMatrix.commonDenom
  simp only [List.flatten_eq_flatMap]
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_intRows :
    ComputableInPolyTime SymRatMatrix.intRows encSymRatMatrix (encList (encList encIntBin)) := by
  fun_prop [SymRatMatrix.intRows]

theorem NonCopositive.computableInPolyTime_check :
    ComputableInPolyTime (fun x : SymRatMatrix × List ℕ => NonCopositive.check x.1 x.2)
      encSymRatMatrixWitness encBool := by
  fun_prop [NonCopositive.check]

theorem NonCopositive.mem_NP : NonCopositive ∈ NP encSymRatMatrix := by
  have hmem : {M : SymRatMatrix | ∃ p : List ℕ, NonCopositive.check M p = true} ∈
      NP encSymRatMatrix :=
    mem_NP_of_witness (Decoder.list Decoder.nat) NonCopositive.computableInPolyTime_check
      (fun _ _ => Iff.rfl)
      (fun _ _ h => NonCopositive.complete_of_mem (NonCopositive.sound_of_check h))
  have hset : {M : SymRatMatrix | ∃ p : List ℕ, NonCopositive.check M p = true} = NonCopositive :=
    Set.ext NonCopositive.exists_check_eq_true_iff
  rwa [← hset]

theorem Copositive.mem_coNP : Copositive ∈ coNP encSymRatMatrix := by
  change Copositiveᶜ ∈ NP encSymRatMatrix
  rw [← NonCopositive_eq_compl]
  exact NonCopositive.mem_NP

/-! ### Reduction from `Clique` to `NonCopositive` -/

/-- Entry `(u, v)` of the reduction matrix for `(G, k)`. -/
@[expose] def cliqueEntry (G : Graph) (k u v : ℕ) : ℚ :=
  if u = v then (((k : ℤ) - 2 : ℤ) : ℚ)
  else if G.adjBool u v then (-1 : ℚ)
  else (((k : ℤ) - 2 : ℤ) : ℚ)

/-- Row list produced by the reduction from a `Clique` instance `(G, k)` to a symmetric rational
matrix. For `k ≥ 2` on a graph with nonempty vertex list, this is the Motzkin–Straus matrix
`(k - 2) J - (k - 1) A_G`. -/
@[expose] def cliqueToRows (gk : CliqueInstance) : List (List ℚ) :=
  let ⟨G, k⟩ := gk
  if k = 0 then [[(-1 : ℚ)]]
  else if G.distinctVertices.isEmpty then [[(1 : ℚ)]]
  else if k = 1 then [[(-1 : ℚ)]]
  else
    G.distinctVertices.map fun u =>
      G.distinctVertices.map fun v => cliqueEntry G k u v

private theorem graph_adjBool_comm (G : Graph) (u v : ℕ) :
    G.adjBool u v = G.adjBool v u := by
  rw [Bool.eq_iff_iff, G.adjBool_eq_true_iff u v, G.adjBool_eq_true_iff v u,
    G.toSimpleGraph.adj_comm]

private theorem cliqueToRows_square (gk : CliqueInstance) :
    ∀ r ∈ cliqueToRows gk, r.length = (cliqueToRows gk).length := by
  rcases gk with ⟨G, k⟩
  dsimp only [cliqueToRows]
  split_ifs <;> intro r hr
  all_goals
    first
    | (rw [List.mem_singleton] at hr; subst hr; rfl)
    | (obtain ⟨_, _, rfl⟩ := List.mem_map.1 hr; simp only [List.length_map])

private theorem cliqueToRows_symm (gk : CliqueInstance) :
    ∀ i j, ((cliqueToRows gk).getD i []).getD j 0 =
      ((cliqueToRows gk).getD j []).getD i 0 := by
  rcases gk with ⟨G, k⟩
  intro i j
  dsimp only [cliqueToRows]
  split_ifs
  any_goals (rcases i with _ | i <;> rcases j with _ | j <;> simp; done)
  by_cases hi : i < G.distinctVertices.length <;>
      by_cases hj : j < G.distinctVertices.length
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.map_some,
      Option.getD_some, cliqueEntry]
    by_cases huv : G.distinctVertices[i] = G.distinctVertices[j]
    · simp only [huv, ↓reduceIte]
    · have hvu : G.distinctVertices[j] ≠ G.distinctVertices[i] := fun h => huv h.symm
      simp only [huv, hvu, ↓reduceIte, graph_adjBool_comm G]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      List.getElem?_eq_none (Nat.le_of_not_lt hj)]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
      List.getElem?_eq_none (Nat.le_of_not_lt hi)]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi),
      List.getElem?_eq_none (Nat.le_of_not_lt hj)]

/-- Polynomial-time many-one reduction mapping a `Clique` instance `(G, k)` to a symmetric
rational matrix `M` such that `(G, k) ∈ Clique ↔ M ∈ NonCopositive`. -/
def cliqueToSymRatMatrix (gk : CliqueInstance) : SymRatMatrix where
  rows := cliqueToRows gk
  square := cliqueToRows_square gk
  symm := cliqueToRows_symm gk

@[simp]
theorem cliqueToSymRatMatrix_rows (gk : CliqueInstance) :
    (cliqueToSymRatMatrix gk).rows = cliqueToRows gk := by
  dsimp only [cliqueToSymRatMatrix]

private def singletonSymRatMatrix (c : ℚ) : SymRatMatrix where
  rows := [[c]]
  square r hr := by rw [List.mem_singleton] at hr; subst hr; rfl
  symm i j := by rcases i with _ | i <;> rcases j with _ | j <;> simp

private theorem singleton_neg_nonCopositive :
    singletonSymRatMatrix (-1) ∈ NonCopositive := by
  intro hcop
  have h := hcop (fun _ => (1 : ℚ)) fun _ => zero_le_one
  change 0 ≤ ∑ i : Fin 1, (1 : ℚ) * ∑ j : Fin 1, (([[(-1 : ℚ)]].getD i.1 []).getD j.1 0) * 1 at h
  norm_num [Fin.sum_univ_one] at h

private theorem singleton_pos_copositive :
    singletonSymRatMatrix 1 ∈ Copositive := by
  intro x hx
  change 0 ≤ ∑ i : Fin 1,
    x ⟨i.1, i.2⟩ * ∑ j : Fin 1, (([[(1 : ℚ)]].getD i.1 []).getD j.1 0) * x ⟨j.1, j.2⟩
  simpa [Fin.sum_univ_one] using mul_nonneg (hx ⟨0, Nat.zero_lt_one⟩) (hx ⟨0, Nat.zero_lt_one⟩)

private theorem clique_iff_comap_cliqueNum (G : Graph) (k : ℕ)
    (ι : Fin G.distinctVertices.length ↪ ℕ) (hι : ∀ i, ι i = G.distinctVertices[i.1]) :
    (⟨G, k⟩ : CliqueInstance) ∈ Clique ↔ k ≤ (G.toSimpleGraph.comap ι).cliqueNum := by
  set H := G.toSimpleGraph.comap ι
  rw [mem_Clique_iff]
  constructor
  · rintro ⟨S, hSG, hS⟩
    let S' : Finset (Fin G.distinctVertices.length) := Finset.univ.filter fun i => ι i ∈ S
    have hS'_img : S'.image ι = S := by
      ext v
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, S']
      refine ⟨by rintro ⟨i, hi, rfl⟩; exact hi, fun hvS => ?_⟩
      obtain ⟨idx, hidx, hval⟩ := List.mem_iff_getElem.1 (Graph.mem_distinctVertices.2 (hSG v hvS))
      exact ⟨⟨idx, hidx⟩, by rwa [hι, hval], (hι ⟨idx, hidx⟩).trans hval⟩
    have hS'clique : H.IsClique (S' : Set (Fin G.distinctVertices.length)) := by
      intro i hi j hj hij
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, S'] at hi hj
      exact hS.isClique hi hj (ι.injective.ne hij)
    have hcard : S'.card = k := by
      rw [← Finset.card_image_of_injective S' ι.injective, hS'_img, hS.card_eq]
    exact hcard ▸ hS'clique.card_le_cliqueNum
  · intro hle
    obtain ⟨S_max, hS_max⟩ := H.exists_isNClique_cliqueNum
    obtain ⟨S', hS'_sub, hS'_card⟩ :=
      Finset.exists_subset_card_eq (n := k) (hS_max.card_eq ▸ hle)
    refine ⟨S'.map ι, fun v hv => ?_, ?_⟩
    · obtain ⟨i, _, rfl⟩ := Finset.mem_map.1 hv
      exact Graph.mem_distinctVertices.1 (hι i ▸ List.getElem_mem i.2)
    · rw [SimpleGraph.isNClique_iff]
      refine ⟨fun u hu v hv hij => ?_, by rw [Finset.card_map, hS'_card]⟩
      rw [Finset.coe_map, Set.mem_image] at hu hv
      rcases hu with ⟨i, hi, rfl⟩; rcases hv with ⟨j, hj, rfl⟩
      exact hS_max.isClique (hS'_sub hi) (hS'_sub hj) fun h => hij (congrArg ι h)

private theorem cliqueToSymRatMatrix_mem_iff_two_le {G : Graph} {k : ℕ}
    (hk2 : 2 ≤ k) (hemp : G.distinctVertices.isEmpty = false) :
    (⟨G, k⟩ : CliqueInstance) ∈ Clique ↔ cliqueToSymRatMatrix ⟨G, k⟩ ∈ NonCopositive := by
  have hk0 : k ≠ 0 := by omega
  have hk1 : k ≠ 1 := by omega
  have hemp' : G.distinctVertices ≠ [] := by intro hnil; simp [hnil] at hemp
  have hn_pos : 0 < G.distinctVertices.length := List.length_pos_of_ne_nil hemp'
  let _ : Nonempty (Fin G.distinctVertices.length) := ⟨⟨0, hn_pos⟩⟩
  let ι : Fin G.distinctVertices.length ↪ ℕ :=
    ⟨fun i => G.distinctVertices[i.1],
      fun _ _ hij => Fin.ext (G.nodup_distinctVertices.getElem_inj_iff.1 hij)⟩
  let H : SimpleGraph (Fin G.distinctVertices.length) := G.toSimpleGraph.comap ι
  let _ : DecidableRel H.Adj := fun i j =>
    decidable_of_iff (G.adjBool (ι i) (ι j) = true)
      (by simp only [H, SimpleGraph.comap_adj]; exact G.adjBool_eq_true_iff (ι i) (ι j))
  have hrows_eq :
      (cliqueToSymRatMatrix ⟨G, k⟩).rows =
        G.distinctVertices.map fun u => G.distinctVertices.map fun v => cliqueEntry G k u v := by
    simp [cliqueToSymRatMatrix_rows, cliqueToRows, hk0, hemp, hk1]
  have hlen_rows : (cliqueToSymRatMatrix ⟨G, k⟩).rows.length = G.distinctVertices.length := by
    rw [hrows_eq, List.length_map]
  let eFin : Fin (cliqueToSymRatMatrix ⟨G, k⟩).rows.length ≃ Fin G.distinctVertices.length :=
    ⟨Fin.cast hlen_rows, Fin.cast hlen_rows.symm, fun _ => rfl, fun _ => rfl⟩
  have hsub : (cliqueToSymRatMatrix ⟨G, k⟩).toMatrix =
      ((H.copositiveCliqueMatrix k).map (Int.cast : ℤ → ℚ)).submatrix eFin eFin := by
    ext i j
    have hi : i.1 < G.distinctVertices.length := hlen_rows ▸ i.2
    have hj : j.1 < G.distinctVertices.length := hlen_rows ▸ j.2
    have hget1 : (cliqueToSymRatMatrix ⟨G, k⟩).rows.getD i.1 [] =
        G.distinctVertices.map fun v => cliqueEntry G k G.distinctVertices[i.1] v := by
      simpa [List.getD_eq_getElem?_getD, hi] using congrArg (fun l => List.getD l i.1 []) hrows_eq
    dsimp only [SymRatMatrix.toMatrix, Matrix.of_apply, Matrix.submatrix_apply]
    rw [hget1, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
      Option.map_some, Option.getD_some, Matrix.map_apply, SimpleGraph.copositiveCliqueMatrix_apply]
    by_cases hij : i.1 = j.1
    · have heij : eFin i = eFin j := Fin.ext hij
      simp [cliqueEntry, hij, heij]
    · have hij_v : G.distinctVertices[i.1] ≠ G.distinctVertices[j.1] :=
        fun h => hij (G.nodup_distinctVertices.getElem_inj_iff.1 h)
      have hH : H.Adj (eFin i) (eFin j) ↔
          G.adjBool G.distinctVertices[i.1] G.distinctVertices[j.1] = true :=
        (G.adjBool_eq_true_iff _ _).symm
      by_cases hadj : G.adjBool G.distinctVertices[i.1] G.distinctVertices[j.1] = true <;>
        simp [cliqueEntry, hij_v, hadj, hH]
  have hnc_iff :
      cliqueToSymRatMatrix ⟨G, k⟩ ∈ NonCopositive ↔
        ∃ x : Fin G.distinctVertices.length → ℚ, (∀ v, 0 ≤ x v) ∧
          x ⬝ᵥ ((H.copositiveCliqueMatrix k).map (Int.cast : ℤ → ℚ) *ᵥ x) < 0 := by
    rw [mem_NonCopositive_iff, hsub, Matrix.IsCopositive.submatrix_equiv_iff, Matrix.IsCopositive]
    push Not
    rfl
  rw [clique_iff_comap_cliqueNum G k ι (fun _ => rfl), hnc_iff]
  exact (SimpleGraph.exists_nonneg_dotProduct_copositiveCliqueMatrix_lt_zero_iff H hk2).symm

theorem cliqueToSymRatMatrix_mem_iff (gk : CliqueInstance) :
    gk ∈ Clique ↔ cliqueToSymRatMatrix gk ∈ NonCopositive := by
  rcases gk with ⟨G, k⟩
  by_cases hk0 : k = 0
  · subst hk0
    have hin : (⟨G, 0⟩ : CliqueInstance) ∈ Clique := mem_Clique_iff.2
      ⟨∅, fun _ h => absurd h (Finset.notMem_empty _), by simp⟩
    have hrows : (cliqueToSymRatMatrix ⟨G, 0⟩).rows = (singletonSymRatMatrix (-1)).rows := by
      simp [cliqueToSymRatMatrix_rows, cliqueToRows, singletonSymRatMatrix]
    exact iff_of_true hin (SymRatMatrix.ext hrows ▸ singleton_neg_nonCopositive)
  · by_cases hemp : G.distinctVertices.isEmpty = true
    · have hnot : (⟨G, k⟩ : CliqueInstance) ∉ Clique := fun hmem => by
        obtain ⟨S, hSG, hS⟩ := mem_Clique_iff.1 hmem
        obtain ⟨v, hvS⟩ := Finset.card_pos.1 (by rw [hS.card_eq]; dsimp only; omega)
        simpa [List.isEmpty_iff.1 hemp] using Graph.mem_distinctVertices.2 (hSG v hvS)
      have hrows : (cliqueToSymRatMatrix ⟨G, k⟩).rows = (singletonSymRatMatrix 1).rows := by
        simp [cliqueToSymRatMatrix_rows, cliqueToRows, hk0, hemp, singletonSymRatMatrix]
      exact iff_of_false hnot (SymRatMatrix.ext hrows ▸ fun h => h singleton_pos_copositive)
    · have hemp' : G.distinctVertices.isEmpty = false := Bool.eq_false_iff.2 hemp
      by_cases hk1 : k = 1
      · subst hk1
        obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil G.distinctVertices
          (by intro hnil; simp [hnil] at hemp')
        have hin : (⟨G, 1⟩ : CliqueInstance) ∈ Clique := mem_Clique_iff.2
          ⟨{v}, fun _ hw => by simp only [Finset.mem_singleton] at hw; exact hw ▸
            Graph.mem_distinctVertices.1 hv, by simp⟩
        have hrows : (cliqueToSymRatMatrix ⟨G, 1⟩).rows = (singletonSymRatMatrix (-1)).rows := by
          simp [cliqueToSymRatMatrix_rows, cliqueToRows, hk0, hemp', singletonSymRatMatrix]
        exact iff_of_true hin (SymRatMatrix.ext hrows ▸ singleton_neg_nonCopositive)
      · exact cliqueToSymRatMatrix_mem_iff_two_le (by omega) hemp'

private theorem computableInPolyTime_toRows :
    ComputableInPolyTime cliqueToRows encCliqueInstance encRatMatrixRows := by
  fun_prop [cliqueEntry, cliqueToRows]

theorem computableInPolyTime_cliqueToSymRatMatrix :
    ComputableInPolyTime cliqueToSymRatMatrix encCliqueInstance encSymRatMatrix :=
  computableInPolyTime_toRows.of_enc_eq fun _ => rfl

/-- Polynomial-time many-one reduction from `Clique` to `NonCopositive`. -/
theorem polyTimeReducible_Clique_NonCopositive :
    PolyTimeReducible encCliqueInstance encSymRatMatrix Clique NonCopositive :=
  ⟨cliqueToSymRatMatrix, computableInPolyTime_cliqueToSymRatMatrix, cliqueToSymRatMatrix_mem_iff⟩

/-- `NonCopositive` is `NP`-hard (proved here via `Clique` and Motzkin–Straus; [MurtyKabadi1987]
establishes completeness in the literature, reported via subset sum). -/
theorem NonCopositive_npHard : NPHard encSymRatMatrix NonCopositive :=
  HardUnder.trans (fun _ _ h₁ h₂ => h₁.trans h₂) Clique_npHard
    polyTimeReducible_Clique_NonCopositive

/-- `NonCopositive` is `NP`-complete (completeness statement credited to [MurtyKabadi1987];
library proof combines bounded integer witness verification with `Clique`/Motzkin–Straus). -/
theorem NonCopositive_npComplete : NPComplete encSymRatMatrix NonCopositive :=
  ⟨NonCopositive.mem_NP, NonCopositive_npHard⟩

/-- `Copositive` is `coNP`-hard (proved here via `Clique` and Motzkin–Straus). -/
theorem Copositive_coNPHard : coNPHard encSymRatMatrix Copositive := by
  rw [coNPHard, Copositive_eq_compl]
  exact HardUnder.compl (fun _ _ h => h.compl) (fun _ _ h => h) NonCopositive_npHard

/-- `Copositive` is `coNP`-complete (completeness statement credited to [MurtyKabadi1987];
library proof uses `NonCopositive` membership and the `Clique`/Motzkin–Straus reduction). -/
theorem Copositive_coNPComplete : coNPComplete encSymRatMatrix Copositive :=
  ⟨Copositive.mem_coNP, Copositive_coNPHard⟩

end Cslib.Complexity
