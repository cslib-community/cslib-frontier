/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Communication.Rank
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.NonnegRank
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Transfer-matrix atlas for matched Boolean gate pairs

When a matched edge `e = (u, v)` in a cubic circuit network has two crossing external wires
`(b, d)` and two internal external wires `(a, c)`, eliminating the shared wire `e : Bool` produces
a `4 × 4` transfer matrix indexed by `(b, d) : Bool × Bool` and `(a, c) : Bool × Bool`.

This module establishes the complete rank and rectangle-partition atlas for fan-in-two Boolean
gates (`U₂` AND-type gates, `XOR` parity gates, and `COPY` fan-out junctions):

* **Unambiguous rectangle partitions** (`IsUnambiguousCover`, `HasUnambiguousRectangles`). If the
  `true` entries of a Boolean matrix `M` partition into `k` pairwise disjoint combinatorial
  rectangles, then its indicator matrix over any semiring factors through `Fin k`, bounding both
  its field rank and its nonnegative rank (`Matrix.nonnegRank`) by `k`.
* **`2`-rectangle pairs (`1` bit).** `COPY – COPY` and every polarity of `XOR – XOR` have
  unambiguous `2`-rectangle partitions (`hasUnambiguousRectangles_copy_copy`,
  `hasUnambiguousRectangles_xor_xor`), with unique internal wire witnesses (`pairCount ≤ 1`).
* **`3`-rectangle `U₂ + COPY` atlas (`log₂ 3` bits).** Every port and polarity placement of
  `COPY – U₂`, `U₂ – COPY`, and DAG-oriented `U₂(out = e) – U₂(in = e)` /
  `U₂(in = e) – U₂(out = e)` (`305` pairs in total) has `pairCount ≤ 1` and an unambiguous
  `3`-rectangle partition (`hasUnambiguousRectangles_copy_andType`,
  `hasUnambiguousRectangles_andType_copy`, `hasUnambiguousRectangles_andType_out_in`,
  `hasUnambiguousRectangles_andType_in_out`). Even the `32` `AND – AND` pairs with four distinct
  rows partition into three disjoint `1`-rectangles.
* **`AND → XOR` rank separation** (`rank_signMatrix_andXorMatrix_real`,
  `rank_andXorMatrix_real`, `rank_andXorMatrix_zmod2`, `nonnegRank_andXorMatrix_real`). The
  `AND → XOR` transfer matrix is a permutation of the square slack matrix: its `{±1}` sign matrix
  has real rank `2`, its `{0, 1}` matrix has rank `3` over `ℝ` and over `ZMod 2`, whereas its
  `K_{2,2}`-freeness forces every combinatorial `1`-rectangle to cover at most `2` of its `8` ones,
  giving `nonnegRank = 4` [Fiorini, Massar, Pokutta, Tiwary, and de Wolf,
  Section 3.1][FioriniMassarPokuttaTiwaryDeWolf2015].

The unambiguous `2`- and `3`-rectangle transfer-matrix atlas for matched Boolean gate pairs is
original to this library.

## Main definitions

* `Cslib.Circuits.Frontier.Basis.IsUnambiguousCover`,
  `Cslib.Circuits.Frontier.Basis.HasUnambiguousRectangles`: unambiguous `1`-rectangle partitions.
* `Cslib.Circuits.Frontier.Basis.copyRel`, `Cslib.Circuits.Frontier.Basis.xorRel`,
  `Cslib.Circuits.Frontier.Basis.andTypeRel`: `3`-pin relations of `COPY`, `XOR`, and `U₂` gates.
* `Cslib.Circuits.Frontier.Basis.pairCount`, `Cslib.Circuits.Frontier.Basis.pairMatrix`:
  witness multiplicity and Boolean transfer matrix of a coupled gate pair.
* `Cslib.Circuits.Frontier.Basis.andXorMatrix`: the canonical `AND → XOR` transfer matrix.

## Main results

* `Cslib.Circuits.Frontier.Basis.HasUnambiguousRectangles.nonnegRank_le`,
  `Cslib.Circuits.Frontier.Basis.HasUnambiguousRectangles.rank_le`: nonnegative-rank and rank
  bounds on `Cslib.Communication.communicationMatrix` from unambiguous rectangle partitions.
* `Cslib.Circuits.Frontier.Basis.hasUnambiguousRectangles_copy_copy`,
  `Cslib.Circuits.Frontier.Basis.hasUnambiguousRectangles_xor_xor`: `2`-rectangle bounds.
* `Cslib.Circuits.Frontier.Basis.hasUnambiguousRectangles_copy_andType`,
  `Cslib.Circuits.Frontier.Basis.hasUnambiguousRectangles_andType_copy`,
  `Cslib.Circuits.Frontier.Basis.hasUnambiguousRectangles_andType_out_in`,
  `Cslib.Circuits.Frontier.Basis.hasUnambiguousRectangles_andType_in_out`: `3`-rectangle `U₂`
  atlas.
* `Cslib.Circuits.Frontier.Basis.rank_signMatrix_andXorMatrix_real`,
  `Cslib.Circuits.Frontier.Basis.rank_andXorMatrix_real`,
  `Cslib.Circuits.Frontier.Basis.rank_andXorMatrix_zmod2`,
  `Cslib.Circuits.Frontier.Basis.nonnegRank_andXorMatrix_real`: the `2 < 3 < 4` rank separation on
  `AND → XOR`.

## References

* [S. Fiorini, S. Massar, S. Pokutta, H. R. Tiwary, and R. de Wolf, *Exponential Lower Bounds for
  Polytopes in Combinatorial Optimization*, Section 3.1][FioriniMassarPokuttaTiwaryDeWolf2015]
-/

public section

namespace Cslib.Circuits.Frontier.Basis

open Matrix

/-! ### Unambiguous combinatorial rectangle partitions -/

section Rectangles

variable {m n m' n' : Type*}

/-- Predicates `row` and `col` form an **unambiguous `k`-rectangle cover** of `M` when `(i, j)`
belongs to a unique rectangle `r : Fin k` if `M i j = true`, and to no rectangle if
`M i j = false`. -/
@[expose]
def IsUnambiguousCover (M : Matrix m n Bool) {k : ℕ}
    (row : Fin k → m → Bool) (col : Fin k → n → Bool) : Prop :=
  ∀ i j, (Finset.univ.filter fun r : Fin k => row r i && col r j).card = if M i j then 1 else 0

instance [Fintype m] [Fintype n] (M : Matrix m n Bool) {k : ℕ}
    (row : Fin k → m → Bool) (col : Fin k → n → Bool) :
    Decidable (IsUnambiguousCover M row col) := by
  unfold IsUnambiguousCover
  infer_instance

/-- `M` admits an unambiguous partition of its `true` entries into `k` combinatorial
rectangles. -/
@[expose]
def HasUnambiguousRectangles (M : Matrix m n Bool) (k : ℕ) : Prop :=
  ∃ (row : Fin k → m → Bool) (col : Fin k → n → Bool), IsUnambiguousCover M row col

/-- Reindexing rows and columns along equivalences preserves `HasUnambiguousRectangles`. -/
theorem HasUnambiguousRectangles.submatrix_equiv {M : Matrix m n Bool} {k : ℕ}
    (h : HasUnambiguousRectangles M k) (e₁ : m' → m) (e₂ : n' → n) :
    HasUnambiguousRectangles (M.submatrix e₁ e₂) k := by
  obtain ⟨row, col, hcov⟩ := h
  exact ⟨fun r i => row r (e₁ i), fun r j => col r (e₂ j), fun i j => hcov (e₁ i) (e₂ j)⟩

/-- Transposing a matrix swaps the row and column predicates of an unambiguous cover. -/
theorem HasUnambiguousRectangles.transpose {M : Matrix m n Bool} {k : ℕ}
    (h : HasUnambiguousRectangles M k) : HasUnambiguousRectangles Mᵀ k := by
  obtain ⟨row, col, hcov⟩ := h
  refine ⟨col, row, fun j i => ?_⟩
  rw [Matrix.transpose_apply, ← hcov i j]
  congr 1
  ext r
  simp [Bool.and_comm]

/-- Padding with empty rectangles raises the rectangle budget monotonically. -/
theorem HasUnambiguousRectangles.mono {M : Matrix m n Bool} {k k' : ℕ}
    (h : HasUnambiguousRectangles M k) (hle : k ≤ k') : HasUnambiguousRectangles M k' := by
  obtain ⟨row, col, hcov⟩ := h
  refine ⟨fun r i => if hlt : r.val < k then row ⟨r.val, hlt⟩ i else false,
    fun r j => if hlt : r.val < k then col ⟨r.val, hlt⟩ j else false, fun i j => ?_⟩
  rw [← hcov i j]
  refine (Finset.card_bij (fun r _ => Fin.castLE hle r)
    (fun r hr => by simpa [r.isLt] using hr)
    (fun r₁ _ r₂ _ heq => Fin.ext (by simpa using congrArg Fin.val heq)) fun r hr => ?_).symm
  by_cases hlt : r.val < k
  · exact ⟨⟨r.val, hlt⟩, by simpa [hlt] using hr, Fin.ext rfl⟩
  · simp [hlt] at hr

/-- An unambiguous `k`-rectangle cover gives an exact `{0, 1}` matrix factorization over any
semiring `R`. -/
theorem IsUnambiguousCover.mul_eq_communicationMatrix (R : Type*) [Semiring R]
    {M : Matrix m n Bool} {k : ℕ} {row : Fin k → m → Bool} {col : Fin k → n → Bool}
    (h : IsUnambiguousCover M row col) :
    Matrix.of (fun i (r : Fin k) => if row r i then (1 : R) else 0) *
      Matrix.of (fun (r : Fin k) j => if col r j then (1 : R) else 0) =
      Communication.communicationMatrix R M := by
  ext i j
  have hterm (r : Fin k) :
      (if row r i then (1 : R) else 0) * (if col r j then 1 else 0) =
        if (row r i && col r j) = true then 1 else 0 := by cases row r i <;> cases col r j <;> simp
  simp only [Matrix.mul_apply, Communication.communicationMatrix, Matrix.of_apply, hterm,
    Finset.sum_boole, h i j]
  cases M i j <;> simp

/-- An unambiguous `k`-rectangle cover yields a nonnegative factorization of
`Communication.communicationMatrix R M` through `Fin k`. -/
theorem HasUnambiguousRectangles.hasNonnegFactorization (R : Type*) [Semiring R] [PartialOrder R]
    [ZeroLEOneClass R] {M : Matrix m n Bool} {k : ℕ} (h : HasUnambiguousRectangles M k) :
    (Communication.communicationMatrix R M).HasNonnegFactorization (Fin k) := by
  obtain ⟨row, col, hcov⟩ := h
  have h01 (b : Bool) : (0 : R) ≤ if b then 1 else 0 := by cases b <;> simp
  exact ⟨Matrix.of fun i r => if row r i then 1 else 0,
    Matrix.of fun r j => if col r j then 1 else 0, fun i r => h01 _, fun r j => h01 _,
    hcov.mul_eq_communicationMatrix R⟩

/-- An unambiguous `k`-rectangle cover bounds the nonnegative rank by `k`. -/
theorem HasUnambiguousRectangles.nonnegRank_le (R : Type*) [Semiring R] [PartialOrder R]
    [ZeroLEOneClass R] {M : Matrix m n Bool} {k : ℕ} (h : HasUnambiguousRectangles M k) :
    (Communication.communicationMatrix R M).nonnegRank ≤ k := by
  simpa using (h.hasNonnegFactorization R).nonnegRank_le

/-- An unambiguous `k`-rectangle cover bounds the matrix rank over any commutative ring with the
strong rank condition by `k`. -/
theorem HasUnambiguousRectangles.rank_le (R : Type*) [CommRing R] [StrongRankCondition R]
    [Finite n] {M : Matrix m n Bool} {k : ℕ} (h : HasUnambiguousRectangles M k) :
    (Communication.communicationMatrix R M).rank ≤ k := by
  obtain ⟨row, col, hcov⟩ := h
  rw [← hcov.mul_eq_communicationMatrix R]
  exact (Matrix.rank_mul_le_right _ _).trans
    ((Matrix.rank_le_card_height _).trans_eq (Fintype.card_fin k))

end Rectangles

/-! ### Three-pin Boolean gate relations and matched-pair transfer matrices -/

/-- Three-pin relation of a `COPY` fan-out junction: all three incident wires carry equal bits. -/
@[expose]
def copyRel (a b e : Bool) : Bool :=
  (a == b) && (b == e)

/-- Three-pin relation of an `XOR`/`XNOR` gate: `a ^^ b ^^ e == neg`. -/
@[expose]
def xorRel (neg a b e : Bool) : Bool :=
  ((a ^^ b) ^^ e) == neg

/-- Three-pin relation of a `U₂` (`AND`-type) gate with input/output polarities `(nx, ny, nz)` and
distinguished port `port : Fin 3` for the shared wire `e`:
* `port = 0`: `a` is the gate output and `(e, b)` are the two inputs;
* `port = 1`: `b` is the gate output and `(a, e)` are the two inputs;
* `port = 2`: `e` is the gate output and `(a, b)` are the two inputs. -/
@[expose]
def andTypeRel (nx ny nz : Bool) (port : Fin 3) (a b e : Bool) : Bool :=
  match port with
  | ⟨0, _⟩ => (((e ^^ nx) && (b ^^ ny)) ^^ nz) == a
  | ⟨1, _⟩ => (((a ^^ nx) && (e ^^ ny)) ^^ nz) == b
  | ⟨2, _⟩ => (((a ^^ nx) && (b ^^ ny)) ^^ nz) == e

/-- Number of internal wire values `e : Bool` jointly satisfying `relU a b e` and `relV c d e`,
indexed by crossing wires `(b, d)` (row) and internal wires `(a, c)` (column). -/
@[expose]
def pairCount (relU relV : Bool → Bool → Bool → Bool) :
    Matrix (Bool × Bool) (Bool × Bool) ℕ
  | (b, d), (a, c) =>
    (if relU a b false && relV c d false then 1 else 0) +
      (if relU a b true && relV c d true then 1 else 0)

/-- Boolean transfer matrix of a matched pair `(u, v)` joined by an internal wire `e`. -/
@[expose]
def pairMatrix (relU relV : Bool → Bool → Bool → Bool) :
    Matrix (Bool × Bool) (Bool × Bool) Bool
  | (b, d), (a, c) =>
    (relU a b false && relV c d false) || (relU a b true && relV c d true)

/-- When at most one internal wire `e` witnesses every boundary assignment, `pairCount` agrees with
the `{0, 1}` indicator of `pairMatrix`. -/
theorem pairCount_eq_ite_pairMatrix {relU relV : Bool → Bool → Bool → Bool}
    (hmult : ∀ bd ac, pairCount relU relV bd ac ≤ 1) (bd ac : Bool × Bool) :
    pairCount relU relV bd ac = if pairMatrix relU relV bd ac then 1 else 0 := by
  rcases bd, ac with ⟨⟨b, d⟩, ⟨a, c⟩⟩
  exact (by decide : ∀ x y : Bool,
    (if x then 1 else 0) + (if y then 1 else 0) ≤ 1 →
      (if x then 1 else 0) + (if y then 1 else 0) = if x || y then 1 else 0)
    _ _ (hmult (b, d) (a, c))

/-- Bitmask decoder on `Bool × Bool`, encoding `(x, y)` as `2 * x + y ∈ {0, 1, 2, 3}`. -/
private def maskPred (mask : ℕ) : Bool × Bool → Bool
  | (x, y) => mask.testBit ((if x then 2 else 0) + (if y then 1 else 0))

/-- Swapping the two endpoints `(u, v)` transposes `pairMatrix` up to swapping the components of
`Bool × Bool`. -/
private theorem pairMatrix_swap (relU relV : Bool → Bool → Bool → Bool) :
    pairMatrix relV relU =
      (pairMatrix relU relV).submatrix Prod.swap Prod.swap := by
  ext ⟨d, b⟩ ⟨c, a⟩
  simp only [pairMatrix, submatrix_apply, Prod.swap, Bool.and_comm]

/-! ### Base cases and polarity reductions for `COPY`, `XOR`, and `U₂` -/

/-- `COPY – COPY` has unique internal wire witnesses (`pairCount ≤ 1`). -/
theorem pairCount_copy_copy_le_one (bd ac : Bool × Bool) :
    pairCount copyRel copyRel bd ac ≤ 1 := by
  rcases bd, ac with ⟨⟨b, d⟩, ⟨a, c⟩⟩
  decide +revert

/-- `COPY – COPY` partitions unambiguously into `2` combinatorial rectangles (`1` bit). -/
theorem hasUnambiguousRectangles_copy_copy :
    HasUnambiguousRectangles (pairMatrix copyRel copyRel) 2 :=
  ⟨fun r => maskPred (![1, 8] r), fun r => maskPred (![1, 8] r), by decide⟩

private theorem hasUnambiguousRectangles_xor_base :
    HasUnambiguousRectangles (pairMatrix (xorRel false) (xorRel false)) 2 :=
  ⟨fun r => maskPred (![6, 9] r), fun r => maskPred (![6, 9] r), by decide⟩

/-- Every `XOR – XOR` pair has unique internal wire witnesses (`pairCount ≤ 1`). -/
theorem pairCount_xor_xor_le_one (n₁ n₂ : Bool) (bd ac : Bool × Bool) :
    pairCount (xorRel n₁) (xorRel n₂) bd ac ≤ 1 := by
  rcases bd, ac with ⟨⟨b, d⟩, ⟨a, c⟩⟩
  decide +revert

/-- Every `XOR – XOR` pair partitions unambiguously into `2` combinatorial rectangles (`1` bit). -/
theorem hasUnambiguousRectangles_xor_xor (n₁ n₂ : Bool) :
    HasUnambiguousRectangles (pairMatrix (xorRel n₁) (xorRel n₂)) 2 :=
  (by decide +revert : (pairMatrix (xorRel false) (xorRel false)).submatrix
      (fun (b, d) => (b ^^ n₁, d ^^ n₂)) id = pairMatrix (xorRel n₁) (xorRel n₂)) ▸
    hasUnambiguousRectangles_xor_base.submatrix_equiv _ _

private theorem hasUnambiguousRectangles_copy_and_base (port : Fin 3) :
    HasUnambiguousRectangles (pairMatrix copyRel (andTypeRel false false false port)) 3 := by
  fin_cases port
  · exact ⟨fun r => maskPred (![3, 4, 8] r), fun r => maskPred (![1, 4, 8] r), by decide⟩
  · exact ⟨fun r => maskPred (![1, 4, 8] r), fun r => maskPred (![3, 4, 8] r), by decide⟩
  · exact ⟨fun r => maskPred (![1, 3, 8] r), fun r => maskPred (![2, 1, 8] r), by decide⟩

/-- Every `COPY – U₂` pair has unique internal wire witnesses (`pairCount ≤ 1`). -/
theorem pairCount_copy_andType_le_one (nx ny nz : Bool) (port : Fin 3) (bd ac : Bool × Bool) :
    pairCount copyRel (andTypeRel nx ny nz port) bd ac ≤ 1 := by
  rcases bd, ac with ⟨⟨b, d⟩, ⟨a, c⟩⟩
  decide +revert

/-- **The `COPY – U₂` `3`-rectangle theorem.** For every polarity `(nx, ny, nz)` and every port
`port : Fin 3`, `COPY – U₂` partitions unambiguously into `3` combinatorial rectangles. -/
theorem hasUnambiguousRectangles_copy_andType (nx ny nz : Bool) (port : Fin 3) :
    HasUnambiguousRectangles (pairMatrix copyRel (andTypeRel nx ny nz port)) 3 := by
  fin_cases port
  · exact (by decide +revert : (pairMatrix copyRel (andTypeRel false false false 0)).submatrix
        (fun (b, d) => (b ^^ nx, d ^^ ny)) (fun (a, c) => (a ^^ nx, c ^^ nz)) =
        pairMatrix copyRel (andTypeRel nx ny nz 0)) ▸
      (hasUnambiguousRectangles_copy_and_base 0).submatrix_equiv _ _
  · exact (by decide +revert : (pairMatrix copyRel (andTypeRel false false false 1)).submatrix
        (fun (b, d) => (b ^^ ny, d ^^ nz)) (fun (a, c) => (a ^^ ny, c ^^ nx)) =
        pairMatrix copyRel (andTypeRel nx ny nz 1)) ▸
      (hasUnambiguousRectangles_copy_and_base 1).submatrix_equiv _ _
  · exact (by decide +revert : (pairMatrix copyRel (andTypeRel false false false 2)).submatrix
        (fun (b, d) => (b ^^ nz, d ^^ ny)) (fun (a, c) => (a ^^ nz, c ^^ nx)) =
        pairMatrix copyRel (andTypeRel nx ny nz 2)) ▸
      (hasUnambiguousRectangles_copy_and_base 2).submatrix_equiv _ _

/-- Every `U₂ – COPY` pair has unique internal wire witnesses (`pairCount ≤ 1`). -/
theorem pairCount_andType_copy_le_one (nx ny nz : Bool) (port : Fin 3) (bd ac : Bool × Bool) :
    pairCount (andTypeRel nx ny nz port) copyRel bd ac ≤ 1 := by
  rcases bd, ac with ⟨⟨b, d⟩, ⟨a, c⟩⟩
  decide +revert

/-- **The `U₂ – COPY` `3`-rectangle theorem.** -/
theorem hasUnambiguousRectangles_andType_copy (nx ny nz : Bool) (port : Fin 3) :
    HasUnambiguousRectangles (pairMatrix (andTypeRel nx ny nz port) copyRel) 3 := by
  rw [pairMatrix_swap]
  exact (hasUnambiguousRectangles_copy_andType nx ny nz port).submatrix_equiv _ _

private theorem hasUnambiguousRectangles_and_and_base (portV : Fin 2) (flipE : Bool) :
    HasUnambiguousRectangles
      (pairMatrix (andTypeRel false false flipE 2)
        (andTypeRel false false false ⟨portV.val, by omega⟩)) 3 := by
  fin_cases portV <;> cases flipE
  · exact ⟨fun r => maskPred (![1, 6, 8] r), fun r => maskPred (![5, 5, 9] r), by decide⟩
  · exact ⟨fun r => maskPred (![2, 5, 8] r), fun r => maskPred (![10, 5, 6] r), by decide⟩
  · exact ⟨fun r => maskPred (![1, 4, 9] r), fun r => maskPred (![7, 7, 8] r), by decide⟩
  · exact ⟨fun r => maskPred (![5, 6, 10] r), fun r => maskPred (![5, 8, 2] r), by decide⟩

/-- Every DAG-oriented `U₂(out = e) – U₂(in = e)` pair has unique internal wire witnesses
(`pairCount ≤ 1`). -/
theorem pairCount_andType_out_in_le_one (nx₁ ny₁ nz₁ nx₂ ny₂ nz₂ : Bool) (portV : Fin 2)
    (bd ac : Bool × Bool) :
    pairCount (andTypeRel nx₁ ny₁ nz₁ 2)
      (andTypeRel nx₂ ny₂ nz₂ ⟨portV.val, by omega⟩) bd ac ≤ 1 := by
  rcases bd, ac with ⟨⟨b, d⟩, ⟨a, c⟩⟩
  fin_cases portV <;> decide +revert

/-- **The `U₂(out = e) – U₂(in = e)` `3`-rectangle theorem (`128` directed pairs).** -/
theorem hasUnambiguousRectangles_andType_out_in (nx₁ ny₁ nz₁ nx₂ ny₂ nz₂ : Bool)
    (portV : Fin 2) :
    HasUnambiguousRectangles
      (pairMatrix (andTypeRel nx₁ ny₁ nz₁ 2)
        (andTypeRel nx₂ ny₂ nz₂ ⟨portV.val, by omega⟩)) 3 := by
  fin_cases portV
  · exact (by decide +revert :
        (pairMatrix (andTypeRel false false (nz₁ ^^ nx₂) 2)
          (andTypeRel false false false 0)).submatrix
          (fun (b, d) => (b ^^ ny₁, d ^^ ny₂)) (fun (a, c) => (a ^^ nx₁, c ^^ nz₂)) =
        pairMatrix (andTypeRel nx₁ ny₁ nz₁ 2) (andTypeRel nx₂ ny₂ nz₂ 0)) ▸
      (hasUnambiguousRectangles_and_and_base 0 (nz₁ ^^ nx₂)).submatrix_equiv _ _
  · exact (by decide +revert :
        (pairMatrix (andTypeRel false false (nz₁ ^^ ny₂) 2)
          (andTypeRel false false false 1)).submatrix
          (fun (b, d) => (b ^^ ny₁, d ^^ nz₂)) (fun (a, c) => (a ^^ nx₁, c ^^ nx₂)) =
        pairMatrix (andTypeRel nx₁ ny₁ nz₁ 2) (andTypeRel nx₂ ny₂ nz₂ 1)) ▸
      (hasUnambiguousRectangles_and_and_base 1 (nz₁ ^^ ny₂)).submatrix_equiv _ _

/-- Every DAG-oriented `U₂(in = e) – U₂(out = e)` pair has unique internal wire witnesses
(`pairCount ≤ 1`). -/
theorem pairCount_andType_in_out_le_one (nx₁ ny₁ nz₁ nx₂ ny₂ nz₂ : Bool) (portU : Fin 2)
    (bd ac : Bool × Bool) :
    pairCount (andTypeRel nx₁ ny₁ nz₁ ⟨portU.val, by omega⟩)
      (andTypeRel nx₂ ny₂ nz₂ 2) bd ac ≤ 1 := by
  rcases bd, ac with ⟨⟨b, d⟩, ⟨a, c⟩⟩
  fin_cases portU <;> decide +revert

/-- **The `U₂(in = e) – U₂(out = e)` `3`-rectangle theorem (`128` directed pairs).** -/
theorem hasUnambiguousRectangles_andType_in_out (nx₁ ny₁ nz₁ nx₂ ny₂ nz₂ : Bool)
    (portU : Fin 2) :
    HasUnambiguousRectangles
      (pairMatrix (andTypeRel nx₁ ny₁ nz₁ ⟨portU.val, by omega⟩)
        (andTypeRel nx₂ ny₂ nz₂ 2)) 3 := by
  rw [pairMatrix_swap]
  exact (hasUnambiguousRectangles_andType_out_in nx₂ ny₂ nz₂ nx₁ ny₁ nz₁ portU).submatrix_equiv _ _

/-! ### Polarized `U₂ + COPY` endpoint classes closed under pin swaps and wire flips -/

/-- Polarized `COPY` relation `(a ^^ na == e) && (b ^^ nb == e)`. -/
@[expose]
def copyPolarRel (na nb a b e : Bool) : Bool :=
  copyRel (a ^^ na) (b ^^ nb) e

/-- Clean `3`-pin relations where the shared wire `e` is an outgoing pin (`src e` side): either a
polarized `COPY` junction or an `AND`-type gate emitting `e` (`port = 2`). -/
inductive U2OutRel : (Bool → Bool → Bool → Bool) → Prop
  | copy (na nb : Bool) : U2OutRel (copyPolarRel na nb)
  | gate (nx ny nz : Bool) : U2OutRel (andTypeRel nx ny nz 2)

/-- Clean `3`-pin relations where the shared wire `e` is an incoming pin (`tgt e` side): either a
polarized `COPY` junction or an `AND`-type gate reading `e` (`port = 0` or `port = 1`). -/
inductive U2InRel : (Bool → Bool → Bool → Bool) → Prop
  | copy (nc nd : Bool) : U2InRel (copyPolarRel nc nd)
  | gate (nx ny nz : Bool) (port : Fin 2) :
      U2InRel (andTypeRel nx ny nz ⟨port.val, by omega⟩)

/-- `U2OutRel` is closed under swapping its two outer pins `(a, b) ↦ (b, a)`. -/
theorem U2OutRel.swap {rel : Bool → Bool → Bool → Bool} (h : U2OutRel rel) :
    U2OutRel (fun a b e => rel b a e) := by
  rcases h with ⟨na, nb⟩ | ⟨nx, ny, nz⟩
  · exact (by decide +revert : copyPolarRel nb na = fun a b e => copyPolarRel na nb b a e) ▸
      .copy nb na
  · exact (by decide +revert : andTypeRel ny nx nz 2 = fun a b e => andTypeRel nx ny nz 2 b a e) ▸
      .gate ny nx nz

/-- `U2InRel` is closed under swapping its two outer pins `(c, d) ↦ (d, c)`. -/
theorem U2InRel.swap {rel : Bool → Bool → Bool → Bool} (h : U2InRel rel) :
    U2InRel (fun c d e => rel d c e) := by
  rcases h with ⟨nc, nd⟩ | ⟨nx, ny, nz, port⟩
  · exact (by decide +revert : copyPolarRel nd nc = fun c d e => copyPolarRel nc nd d c e) ▸
      .copy nd nc
  · fin_cases port
    · exact (by decide +revert : andTypeRel ny nx nz 1 =
        fun c d e => andTypeRel nx ny nz 0 d c e) ▸ .gate ny nx nz 1
    · exact (by decide +revert : andTypeRel ny nx nz 0 =
        fun c d e => andTypeRel nx ny nz 1 d c e) ▸ .gate ny nx nz 0

/-- `U2OutRel` is closed under flipping polarities on all three pins. -/
theorem U2OutRel.flip {rel : Bool → Bool → Bool → Bool} (h : U2OutRel rel) (fa fb fe : Bool) :
    U2OutRel (fun a b e => rel (a ^^ fa) (b ^^ fb) (e ^^ fe)) := by
  rcases h with ⟨na, nb⟩ | ⟨nx, ny, nz⟩
  · exact (by decide +revert : copyPolarRel (na ^^ fa ^^ fe) (nb ^^ fb ^^ fe) =
      fun a b e => copyPolarRel na nb (a ^^ fa) (b ^^ fb) (e ^^ fe)) ▸ .copy _ _
  · exact (by decide +revert : andTypeRel (nx ^^ fa) (ny ^^ fb) (nz ^^ fe) 2 =
      fun a b e => andTypeRel nx ny nz 2 (a ^^ fa) (b ^^ fb) (e ^^ fe)) ▸ .gate _ _ _

/-- `U2InRel` is closed under flipping polarities on all three pins. -/
theorem U2InRel.flip {rel : Bool → Bool → Bool → Bool} (h : U2InRel rel) (fc fd fe : Bool) :
    U2InRel (fun c d e => rel (c ^^ fc) (d ^^ fd) (e ^^ fe)) := by
  rcases h with ⟨nc, nd⟩ | ⟨nx, ny, nz, port⟩
  · exact (by decide +revert : copyPolarRel (nc ^^ fc ^^ fe) (nd ^^ fd ^^ fe) =
      fun c d e => copyPolarRel nc nd (c ^^ fc) (d ^^ fd) (e ^^ fe)) ▸ .copy _ _
  · fin_cases port
    · exact (by decide +revert : andTypeRel (nx ^^ fe) (ny ^^ fd) (nz ^^ fc) 0 =
        fun c d e => andTypeRel nx ny nz 0 (c ^^ fc) (d ^^ fd) (e ^^ fe)) ▸ .gate _ _ _ 0
    · exact (by decide +revert : andTypeRel (nx ^^ fc) (ny ^^ fe) (nz ^^ fd) 1 =
        fun c d e => andTypeRel nx ny nz 1 (c ^^ fc) (d ^^ fd) (e ^^ fe)) ▸ .gate _ _ _ 1

/-- Every oriented `U₂ + COPY` pair `(relU, relV)` has unique internal wire witnesses
(`pairCount ≤ 1`). -/
theorem pairCount_u2_le_one {relU relV : Bool → Bool → Bool → Bool}
    (hU : U2OutRel relU) (hV : U2InRel relV) (bd ac : Bool × Bool) :
    pairCount relU relV bd ac ≤ 1 := by
  rcases bd, ac with ⟨⟨b, d⟩, ⟨a, c⟩⟩
  rcases hU with ⟨na, nb⟩ | ⟨nx₁, ny₁, nz₁⟩ <;> rcases hV with ⟨nc, nd⟩ | ⟨nx₂, ny₂, nz₂, port⟩
  · decide +revert
  · fin_cases port <;> decide +revert
  · decide +revert
  · exact pairCount_andType_out_in_le_one nx₁ ny₁ nz₁ nx₂ ny₂ nz₂ port (b, d) (a, c)

/-- **Unified `U₂ + COPY` `3`-rectangle theorem.** Every oriented `U₂ + COPY` pair `(relU, relV)`
partitions unambiguously into `3` combinatorial rectangles. -/
theorem hasUnambiguousRectangles_u2 {relU relV : Bool → Bool → Bool → Bool}
    (hU : U2OutRel relU) (hV : U2InRel relV) :
    HasUnambiguousRectangles (pairMatrix relU relV) 3 := by
  rcases hU with ⟨na, nb⟩ | ⟨nx₁, ny₁, nz₁⟩ <;> rcases hV with ⟨nc, nd⟩ | ⟨nx₂, ny₂, nz₂, port⟩
  · exact (by decide +revert : (pairMatrix copyRel copyRel).submatrix
        (fun (b, d) => (b ^^ nb, d ^^ nd)) (fun (a, c) => (a ^^ na, c ^^ nc)) =
        pairMatrix (copyPolarRel na nb) (copyPolarRel nc nd)) ▸
      (hasUnambiguousRectangles_copy_copy.mono (by decide)).submatrix_equiv _ _
  · exact (by fin_cases port <;> decide +revert :
        (pairMatrix copyRel (andTypeRel nx₂ ny₂ nz₂ ⟨port.val, by omega⟩)).submatrix
          (fun (b, d) => (b ^^ nb, d)) (fun (a, c) => (a ^^ na, c)) =
        pairMatrix (copyPolarRel na nb) (andTypeRel nx₂ ny₂ nz₂ ⟨port.val, by omega⟩)) ▸
      (hasUnambiguousRectangles_copy_andType nx₂ ny₂ nz₂ ⟨port.val, by omega⟩).submatrix_equiv _ _
  · exact (by decide +revert : (pairMatrix (andTypeRel nx₁ ny₁ nz₁ 2) copyRel).submatrix
        (fun (b, d) => (b, d ^^ nd)) (fun (a, c) => (a, c ^^ nc)) =
        pairMatrix (andTypeRel nx₁ ny₁ nz₁ 2) (copyPolarRel nc nd)) ▸
      (hasUnambiguousRectangles_andType_copy nx₁ ny₁ nz₁ 2).submatrix_equiv _ _
  · exact hasUnambiguousRectangles_andType_out_in nx₁ ny₁ nz₁ nx₂ ny₂ nz₂ port

/-! ### Exact `3 < 4` rank vs nonnegative-rank separation on `AND → XOR` -/

/-- The canonical `AND → XOR` `4 × 4` transfer matrix (`e = a && b`, `c ^^ d ^^ e = false`). Its
`1`-entries form a permutation of the `4 × 4` square slack matrix. -/
@[expose]
def andXorMatrix : Matrix (Bool × Bool) (Bool × Bool) Bool :=
  pairMatrix (andTypeRel false false false 2) (xorRel false)

private def andXorLeft (R : Type*) [Ring R] : Matrix (Bool × Bool) (Fin 3) R
  | (false, false) => ![1, 0, 0]
  | (false, true) => ![0, 1, 0]
  | (true, false) => ![0, 0, 1]
  | (true, true) => ![1, 1, -1]

private def andXorRight (R : Type*) [Ring R] : Matrix (Fin 3) (Bool × Bool) R
  | ⟨0, _⟩ => Communication.communicationMatrix R andXorMatrix (false, false)
  | ⟨1, _⟩ => Communication.communicationMatrix R andXorMatrix (false, true)
  | ⟨2, _⟩ => Communication.communicationMatrix R andXorMatrix (true, false)

private theorem andXorLeft_mul_andXorRight (R : Type*) [Ring R] :
    andXorLeft R * andXorRight R = Communication.communicationMatrix R andXorMatrix := by
  ext ⟨b, d⟩ ⟨a, c⟩
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  cases b <;> cases d <;> cases a <;> cases c <;>
    simp [andXorLeft, andXorRight, Communication.communicationMatrix, andXorMatrix, pairMatrix,
      andTypeRel, xorRel]

private def andXorRowSel (R : Type*) [Ring R] : Matrix (Fin 3) (Bool × Bool) R
  | ⟨0, _⟩, (b, d) => if !b && !d then 1 else 0
  | ⟨1, _⟩, (b, d) => if !b && d then 1 else 0
  | ⟨2, _⟩, (b, d) => if b && !d then 1 else 0

private def andXorColInv (R : Type*) [Ring R] : Matrix (Bool × Bool) (Fin 3) R
  | (false, false) => ![1, 0, 0]
  | (false, true) => ![1, 1, -1]
  | (true, false) => ![0, 0, 0]
  | (true, true) => ![-1, 0, 1]

private theorem andXorRowSel_mul_andXorColInv (R : Type*) [Ring R] :
    andXorRowSel R * Communication.communicationMatrix R andXorMatrix * andXorColInv R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, andXorRowSel, andXorColInv,
      Communication.communicationMatrix, andXorMatrix, pairMatrix, andTypeRel, xorRel]

/-- Over any commutative ring with the strong rank condition, `andXorMatrix` has matrix rank
exactly `3`. -/
theorem rank_andXorMatrix (R : Type*) [CommRing R] [StrongRankCondition R] :
    (Communication.communicationMatrix R andXorMatrix).rank = 3 := by
  apply le_antisymm
  · rw [← andXorLeft_mul_andXorRight R]
    exact (Matrix.rank_mul_le_right _ _).trans
      ((Matrix.rank_le_card_height _).trans_eq (Fintype.card_fin 3))
  · calc 3 = (1 : Matrix (Fin 3) (Fin 3) R).rank := by simp
      _ = (andXorRowSel R * Communication.communicationMatrix R andXorMatrix *
            andXorColInv R).rank := by
        rw [andXorRowSel_mul_andXorColInv R]
      _ ≤ (andXorRowSel R * Communication.communicationMatrix R andXorMatrix).rank :=
        Matrix.rank_mul_le_left _ _
      _ ≤ (Communication.communicationMatrix R andXorMatrix).rank := Matrix.rank_mul_le_right _ _

/-- Over `ℝ`, the `AND → XOR` transfer matrix has rank `3`. -/
theorem rank_andXorMatrix_real : (Communication.communicationMatrix ℝ andXorMatrix).rank = 3 :=
  rank_andXorMatrix ℝ

/-- Over `ZMod 2`, the `AND → XOR` transfer matrix has rank `3`. -/
theorem rank_andXorMatrix_zmod2 :
    (Communication.communicationMatrix (ZMod 2) andXorMatrix).rank = 3 :=
  rank_andXorMatrix (ZMod 2)

private def andXorSignLeft : Matrix (Bool × Bool) (Fin 2) ℝ
  | (false, false) => ![1, 0]
  | (false, true) => ![-1, 0]
  | (true, false) => ![0, 1]
  | (true, true) => ![0, -1]

private def andXorSignRight : Matrix (Fin 2) (Bool × Bool) ℝ
  | ⟨0, _⟩ => Communication.signMatrix ℝ andXorMatrix (false, false)
  | ⟨1, _⟩ => Communication.signMatrix ℝ andXorMatrix (true, false)

private theorem andXorSignLeft_mul_andXorSignRight :
    andXorSignLeft * andXorSignRight = Communication.signMatrix ℝ andXorMatrix := by
  ext ⟨b, d⟩ ⟨a, c⟩
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  cases b <;> cases d <;> cases a <;> cases c <;>
    simp [andXorSignLeft, andXorSignRight, Communication.signMatrix, andXorMatrix, pairMatrix,
      andTypeRel, xorRel]

private def andXorSignRowSel : Matrix (Fin 2) (Bool × Bool) ℝ
  | ⟨0, _⟩, (b, d) => if !b && !d then 1 else 0
  | ⟨1, _⟩, (b, d) => if b && !d then 1 else 0

private noncomputable def andXorSignColInv : Matrix (Bool × Bool) (Fin 2) ℝ
  | (false, false) => ![-1 / 2, -1 / 2]
  | (false, true) => ![0, 0]
  | (true, false) => ![-1 / 2, 1 / 2]
  | (true, true) => ![0, 0]

private theorem andXorSignRowSel_mul_andXorSignColInv :
    andXorSignRowSel * Communication.signMatrix ℝ andXorMatrix * andXorSignColInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, andXorSignRowSel, andXorSignColInv,
      Communication.signMatrix, andXorMatrix, pairMatrix, andTypeRel, xorRel] <;> norm_num

/-- Over `ℝ`, the `{-1, 1}` sign matrix of `AND → XOR` has rank `2`: flipping the `XOR` external
wire negates its row, halving the `4` rows to two antipodal pairs. -/
theorem rank_signMatrix_andXorMatrix_real :
    (Communication.signMatrix ℝ andXorMatrix).rank = 2 := by
  apply le_antisymm
  · rw [← andXorSignLeft_mul_andXorSignRight]
    exact (Matrix.rank_mul_le_right _ _).trans
      ((Matrix.rank_le_card_height _).trans_eq (Fintype.card_fin 2))
  · calc 2 = (1 : Matrix (Fin 2) (Fin 2) ℝ).rank := by simp
      _ = (andXorSignRowSel * Communication.signMatrix ℝ andXorMatrix *
            andXorSignColInv).rank := by rw [andXorSignRowSel_mul_andXorSignColInv]
      _ ≤ (andXorSignRowSel * Communication.signMatrix ℝ andXorMatrix).rank :=
        Matrix.rank_mul_le_left _ _
      _ ≤ (Communication.signMatrix ℝ andXorMatrix).rank := Matrix.rank_mul_le_right _ _

private theorem not_two_by_two_andXorMatrix (i₁ i₂ j₁ j₂ : Bool × Bool)
    (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂) :
    ¬(andXorMatrix i₁ j₁ = true ∧ andXorMatrix i₁ j₂ = true ∧
      andXorMatrix i₂ j₁ = true ∧ andXorMatrix i₂ j₂ = true) := by
  rcases i₁, i₂ with ⟨⟨b₁, d₁⟩, ⟨b₂, d₂⟩⟩
  rcases j₁, j₂ with ⟨⟨a₁, c₁⟩, ⟨a₂, c₂⟩⟩
  decide +revert

/-- `andXorMatrix` is `K_{2,2}`-free: no `2 × 2` combinatorial rectangle consists entirely of
`true` entries, so every monochromatic `true`-rectangle has size at most `2`. -/
theorem card_product_le_two_of_andXorMatrix (A B : Finset (Bool × Bool))
    (hAB : ∀ i ∈ A, ∀ j ∈ B, andXorMatrix i j = true) : (A ×ˢ B).card ≤ 2 := by
  rw [Finset.card_product]
  rcases lt_or_ge A.card 2 with hA | hA
  · interval_cases hAc : A.card
    · simp
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hAc
      simpa using (Finset.card_le_card fun j hj => Finset.mem_filter.2
        ⟨Finset.mem_univ j, hAB i (Finset.mem_singleton_self i) j hj⟩).trans
        ((by decide : ∀ i, (Finset.univ.filter fun j => andXorMatrix i j = true).card ≤ 2) i)
  · rcases lt_or_ge B.card 2 with hB | hB
    · interval_cases hBc : B.card
      · simp
      · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hBc
        simpa using (Finset.card_le_card fun i hi => Finset.mem_filter.2
          ⟨Finset.mem_univ i, hAB i hi j (Finset.mem_singleton_self j)⟩).trans
          ((by decide : ∀ j, (Finset.univ.filter fun i => andXorMatrix i j = true).card ≤ 2) j)
    · obtain ⟨i₁, hi₁, i₂, hi₂, hij⟩ := Finset.one_lt_card.mp hA
      obtain ⟨j₁, hj₁, j₂, hj₂, hjj⟩ := Finset.one_lt_card.mp hB
      exact (not_two_by_two_andXorMatrix i₁ i₂ j₁ j₂ hij hjj
        ⟨hAB i₁ hi₁ j₁ hj₁, hAB i₁ hi₁ j₂ hj₂, hAB i₂ hi₂ j₁ hj₁, hAB i₂ hi₂ j₂ hj₂⟩).elim

/-- **Exact nonnegative rank of `AND → XOR` (`nonnegRank = 4 > 3 = rank`).** Because `andXorMatrix`
has `8` ones and every `1`-rectangle covers at most `2` ones, no `3` nonnegative rank-one matrices
can sum to `andXorMatrix`. -/
theorem nonnegRank_andXorMatrix_real :
    (Communication.communicationMatrix ℝ andXorMatrix).nonnegRank = 4 := by
  apply le_antisymm
  · exact (Matrix.nonnegRank_le_card_height fun i j => by
      dsimp only [Communication.communicationMatrix, Matrix.of_apply]
      split_ifs <;> norm_num
    ).trans_eq (by simp)
  · rw [Matrix.le_nonnegRank_iff]
    rintro r ⟨T, U, hT, hU, hTU⟩
    let supp := Finset.univ.filter fun p : (Bool × Bool) × (Bool × Bool) =>
      andXorMatrix p.1 p.2 = true
    let rect (k : Fin r) : Finset ((Bool × Bool) × (Bool × Bool)) :=
      (Finset.univ.filter fun i => T i k ≠ 0) ×ˢ (Finset.univ.filter fun j => U k j ≠ 0)
    have hrect_le (k : Fin r) : (rect k).card ≤ 2 :=
      card_product_le_two_of_andXorMatrix _ _ fun i hi j hj => by
        have hne := hTU ▸ (Matrix.mul_apply_ne_zero_iff_of_nonneg hT hU i j).2
          ⟨k, (Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2⟩
        by_contra hf
        simp [Communication.communicationMatrix, hf] at hne
    have hsub : supp ⊆ Finset.univ.biUnion rect := fun ⟨i, j⟩ hp => by
      have hne : (T * U) i j ≠ 0 := by
        simp [hTU, Communication.communicationMatrix, (Finset.mem_filter.mp hp).2]
      obtain ⟨k, hik, hkj⟩ := (Matrix.mul_apply_ne_zero_iff_of_nonneg hT hU i j).1 hne
      exact Finset.mem_biUnion.2 ⟨k, Finset.mem_univ k,
        Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ i, hik⟩,
          Finset.mem_filter.2 ⟨Finset.mem_univ j, hkj⟩⟩⟩
    have h8 : 8 ≤ 2 * r :=
      calc 8 = supp.card := by decide
        _ ≤ (Finset.univ.biUnion rect).card := Finset.card_le_card hsub
        _ ≤ ∑ k : Fin r, (rect k).card := Finset.card_biUnion_le
        _ ≤ ∑ _k : Fin r, 2 := Finset.sum_le_sum fun k _ => hrect_le k
        _ = 2 * r := by simp [mul_comm]
    exact_mod_cast (by omega : 4 ≤ r)

end Cslib.Circuits.Frontier.Basis
