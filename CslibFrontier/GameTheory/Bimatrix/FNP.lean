/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Bimatrix.Basic
public import CslibFrontier.Computability.Complexity.Classes.TFNP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
import CslibFrontier.Computability.PolyTime.Int.DotProduct
import CslibFrontier.Computability.PolyTime.Int.ExactDiv
import CslibFrontier.Computability.PolyTime.Int.Table
import CslibFrontier.Foundations.Data.List.GetD
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.List.OfFn
import CslibFrontier.Foundations.Data.List.OfFnGetD
import Mathlib.Data.List.GetD

/-!
# Encoded two-player rational bimatrix games and `FNP` verification

This module defines the binary encoding of finite two-player rational bimatrix games, the exact
rational Nash equilibrium search problem `BimatrixCode.BimatrixNash`, and a polynomial-time exact
integer verifier showing `BimatrixNash ∈ FNP encBimatrix`.

Payoff matrices are encoded by the structure `BimatrixCode` (fields `matA`, `matB`) under
`encBimatrix` using `Turing.MultiTapeTM.encRat`, and rational mixed strategy pairs by
`StrategyPair` under `encWitness`. For well-formed nonempty `m × n` matrices, `BimatrixNash c w`
holds when `w` is a polynomially bounded canonical rational strategy pair forming an exact Nash
equilibrium of `c.toGame`; non-well-formed inputs admit only the empty witness `[]`.

Verification clears payoff and strategy denominators without rational division, checking
canonical lowest-terms nonnegativity, unit strategy sums, and all pure-deviation inequalities in
signed binary integer arithmetic.

## Main definitions

* `Cslib.GameTheory.StrategyPair`, `Cslib.GameTheory.encWitness`: rational mixed strategy pairs and
  their canonical binary encoding via `encRat`.
* `Cslib.GameTheory.BimatrixCode`, `Cslib.GameTheory.encBimatrix`: explicitly presented two-player
  rational payoff matrices and their binary encoding.
* `Cslib.GameTheory.BimatrixCode.WellFormed`, `Cslib.GameTheory.BimatrixCode.toGame`:
  nonempty rectangularity predicate and induced `BimatrixGame`.
* `Cslib.GameTheory.BimatrixCode.IsSymmetric`, `Cslib.GameTheory.BimatrixCode.toSymGame`:
  symmetric rational bimatrix codes (`B = Aᵀ`) and their induced symmetric games.
* `Cslib.GameTheory.BimatrixCode.IsRationalNash`, `Cslib.GameTheory.BimatrixCode.BimatrixNash`:
  exact rational Nash predicate and polynomially bounded total search relation.

## Main results

* `Cslib.GameTheory.BimatrixCode.IsRationalNash.toGame_isNash`: rational Nash strategy pairs induce
  mixed Nash equilibria of `c.toGame`.
* `Cslib.GameTheory.BimatrixCode.BimatrixNash_mem_FNP`: `BimatrixNash ∈ FNP encBimatrix`.

## References

* [C. H. Papadimitriou, *On the complexity of the parity argument and other inefficient proofs of
  existence*][Papadimitriou1994PPAD]
* [B. von Stengel, *Equilibrium computation for two-player games in strategic and extensive
  form*][vonStengel2007], Chapter 3
-/

public section

namespace Cslib.GameTheory

open Cslib Cslib.BitString Cslib.Complexity Cslib.GameTheory.BimatrixGame
  Mathlib.Tactic.Matrix Matrix
open Turing.MultiTapeTM ComputableInPolyTime

/-! ### Section 1: Encodings, games, and the rational Nash search problem -/

/-- Encoding of a pair of lists of raw `(ℤ, ℕ)` rational numerator-denominator pairs: the first
framed list of `encRatData` pairs followed by the second unframed list of `encRatData` pairs. -/
private abbrev encWitnessPairs : (List (ℤ × ℕ) × List (ℤ × ℕ)) ↪ List Bool :=
  encPair (encList encRatData) (encList encRatData)

/-- A pair of rational mixed strategy lists `(x, y)` for players 1 and 2. -/
@[ext]
structure StrategyPair where
  /-- Player 1's rational mixed strategy list. -/
  x : List ℚ
  /-- Player 2's rational mixed strategy list. -/
  y : List ℚ
deriving DecidableEq, Repr

/-- Canonical encoding of a rational strategy pair `(x, y)` via `Turing.MultiTapeTM.encRat`. -/
enc_structure encWitness : StrategyPair where
  x : (encList encRat),
  y : (encList encRat)

/-- An explicitly presented two-player game given by two lists of rational payoff rows. -/
@[ext]
structure BimatrixCode where
  /-- Player 1's rational payoff matrix as a list of rows. -/
  matA : List (List ℚ)
  /-- Player 2's rational payoff matrix as a list of rows. -/
  matB : List (List ℚ)
deriving DecidableEq, Repr

/-- Binary encoding of rational bimatrix games as `(matA, matB)` via `encRat`. -/
enc_structure encBimatrix : BimatrixCode where
  matA : (encList (encList encRat)),
  matB : (encList (encList encRat))

namespace BimatrixCode

/-- Number of pure strategies of player 1. -/
@[expose] def rows (c : BimatrixCode) : ℕ := c.matA.length

/-- Number of pure strategies of player 2. -/
@[expose] def cols (c : BimatrixCode) : ℕ := (c.matA.headD []).length

/-- Decidable rectangularity and nonemptiness check for `BimatrixCode`. -/
@[expose] def wellFormedB (c : BimatrixCode) : Bool :=
  decide (0 < c.rows) && decide (0 < c.cols) && decide (c.matB.length = c.rows) &&
    c.matA.all (fun r => decide (r.length = c.cols)) &&
    c.matB.all (fun r => decide (r.length = c.cols))

/-- Predicate asserting `c` encodes nonempty rectangular `rows × cols` payoff matrices. -/
@[expose] def WellFormed (c : BimatrixCode) : Prop :=
  0 < c.rows ∧ 0 < c.cols ∧ c.matB.length = c.rows ∧
    (∀ r ∈ c.matA, r.length = c.cols) ∧ (∀ r ∈ c.matB, r.length = c.cols)

theorem wellFormed_iff_wellFormedB (c : BimatrixCode) : c.WellFormed ↔ c.wellFormedB = true := by
  simp only [WellFormed, wellFormedB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  tauto

/-- Player 1's rational payoff matrix extracted from `c`. -/
@[expose] def toMatA (c : BimatrixCode) : Matrix (Fin c.rows) (Fin c.cols) ℚ :=
  fun i j => (c.matA.getD i.val []).getD j.val 0

/-- Player 2's rational payoff matrix extracted from `c`. -/
@[expose] def toMatB (c : BimatrixCode) : Matrix (Fin c.rows) (Fin c.cols) ℚ :=
  fun i j => (c.matB.getD i.val []).getD j.val 0

/-- The `BimatrixGame` induced by a `BimatrixCode`. -/
@[expose] noncomputable def toGame (c : BimatrixCode) : BimatrixGame (Fin c.rows) (Fin c.cols) :=
  BimatrixGame.mk ((toMatA c).map Rat.cast) ((toMatB c).map Rat.cast)

/-- Predicate asserting that `c : BimatrixCode` encodes a finite symmetric two-player game:
nonempty, square (`rows = cols`), and with player 2's payoff matrix equal to the transpose of
player 1's (`B = Aᵀ`). -/
@[expose] def IsSymmetric (c : BimatrixCode) : Prop :=
  c.WellFormed ∧ c.rows = c.cols ∧
    ∀ i j : Fin c.rows, (c.matB.getD i.val []).getD j.val 0 = (c.matA.getD j.val []).getD i.val 0

/-- The symmetric two-player game `⟨A, Aᵀ⟩` on `Fin c.rows` extracted from player 1's payoff
matrix `c.matA`. When `c.IsSymmetric`, this coincides with `c.toGame` up to casting
`Fin c.rows` to `Fin c.cols`. -/
@[expose] noncomputable def toSymGame (c : BimatrixCode) :
    BimatrixGame (Fin c.rows) (Fin c.rows) :=
  let A : Matrix (Fin c.rows) (Fin c.rows) ℝ :=
    fun i j => ((c.matA.getD i.val []).getD j.val 0 : ℝ)
  ⟨A, Aᵀ⟩

/-- The real strategy vector `Fin n → ℝ` of a rational strategy list, padded with zeros. -/
@[expose] def strategyVec {n : ℕ} (x : List ℚ) : Fin n → ℝ := fun i => (x.getD i.val 0 : ℝ)

@[simp]
theorem strategyVec_apply {n : ℕ} (x : List ℚ) (i : Fin n) :
    strategyVec x i = (x.getD i.val 0 : ℝ) :=
  rfl

/-- Pure rational Nash condition on strategy lists `x` (length `c.rows`) and `y`
(length `c.cols`). -/
@[expose] def IsRationalNash (c : BimatrixCode) (x y : List ℚ) : Prop :=
  x.length = c.rows ∧ y.length = c.cols ∧
    (∀ q ∈ x, 0 ≤ q) ∧ x.sum = 1 ∧
    (∀ q ∈ y, 0 ≤ q) ∧ y.sum = 1 ∧
    (∀ i : Fin c.rows,
      (∑ j : Fin c.cols, c.toMatA i j * y.getD j.val 0) ≤
        ∑ a : Fin c.rows, ∑ j : Fin c.cols, x.getD a.val 0 * c.toMatA a j * y.getD j.val 0) ∧
    (∀ j : Fin c.cols,
      (∑ i : Fin c.rows, x.getD i.val 0 * c.toMatB i j) ≤
        ∑ i : Fin c.rows, ∑ b : Fin c.cols, x.getD i.val 0 * c.toMatB i b * y.getD b.val 0)

/-- A nonnegative rational list of length `n` summing to `1` is a mixed strategy on `Fin n`. -/
theorem isMixedStrategy_strategyVec {n : ℕ} {x : List ℚ} (hlen : x.length = n)
    (hnn : ∀ q ∈ x, 0 ≤ q) (hsum : x.sum = 1) : IsMixedStrategy (strategyVec (n := n) x) := by
  refine isMixedStrategy_iff.2 ⟨fun i => Rat.cast_nonneg.2 (hnn _ ?_), ?_⟩
  · exact List.getD_mem 0 (by omega)
  · simp only [strategyVec_apply, ← Rat.cast_sum, ← List.sum_ofFn,
      List.ofFn_getD_eq_of_length 0 hlen, hsum, Rat.cast_one]

theorem IsRationalNash.toGame_isNash {c : BimatrixCode} {x y : List ℚ}
    (hn : c.IsRationalNash x y) : c.toGame.IsNash (strategyVec x) (strategyVec y) := by
  obtain ⟨hxlen, hylen, hxnn, hxsum, hynn, hysum, hbr1, hbr2⟩ := hn
  have hpt₁ : ∀ a : Fin c.rows, (c.toGame.A *ᵥ strategyVec y) a ≤
      strategyVec x ⬝ᵥ (c.toGame.A *ᵥ strategyVec y) := fun a => by
    have ha := (Rat.cast_le (K := ℝ)).2 (hbr1 a)
    simpa only [strategyVec_apply, toGame, Matrix.mulVec, dotProduct, Matrix.map_apply,
      Rat.cast_sum, Rat.cast_mul, Finset.mul_sum, mul_assoc] using ha
  have hpt₂ : ∀ b : Fin c.cols, (strategyVec x ᵥ* c.toGame.B) b ≤
      strategyVec y ⬝ᵥ (strategyVec x ᵥ* c.toGame.B) := fun b => by
    have hb := (Rat.cast_le (K := ℝ)).2 (hbr2 b)
    rw [Finset.sum_comm] at hb
    rw [dotProduct_comm (strategyVec y)]
    simpa only [strategyVec_apply, toGame, Matrix.vecMul, dotProduct, Matrix.map_apply,
      Rat.cast_sum, Rat.cast_mul, Finset.sum_mul, mul_assoc] using hb
  have hmx := isMixedStrategy_strategyVec hxlen hxnn hxsum
  have hmy := isMixedStrategy_strategyVec hylen hynn hysum
  rw [BimatrixGame.isNash_iff, BimatrixGame.isBestResponse₁_iff, BimatrixGame.isBestResponse₂_iff]
  refine ⟨⟨hmx, fun i hi => BimatrixGame.isPureBestResponse₁_iff.2 ?_⟩,
    ⟨hmy, fun j hj => BimatrixGame.isPureBestResponse₂_iff.2 ?_⟩⟩
  · exact hmx.forall_dotProduct_le_iff.1 (fun x' hx' => hx'.dotProduct_le_of_forall_le hpt₁) i hi
  · exact hmy.forall_dotProduct_le_iff.1 (fun y' hy' => hy'.dotProduct_le_of_forall_le hpt₂) j hj

/-- Polynomial witness length bound `120 * L^3 + 400 * L + 100` in `L = (encBimatrix c).length`. -/
@[expose] noncomputable def witnessPoly : Polynomial ℕ :=
  Polynomial.C 120 * Polynomial.X ^ 3 + Polynomial.C 400 * Polynomial.X + Polynomial.C 100

theorem witnessPoly_eval (L : ℕ) :
    witnessPoly.eval L = 120 * L ^ 3 + 400 * L + 100 := by
  simp only [witnessPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]

/-- The rational bimatrix Nash search problem: given `c`, find a polynomially bounded canonical
rational strategy pair `s` forming an exact Nash equilibrium of `c.toGame` (or `[]` on malformed
`c`). -/
@[expose] def BimatrixNash (c : BimatrixCode) (w : List Bool) : Prop :=
  if c.wellFormedB then
    w.length ≤ witnessPoly.eval (encBimatrix c).length ∧
      ∃ s : StrategyPair, w = encWitness s ∧ c.IsRationalNash s.x s.y
  else w = []

/-! ### Section 2: Executable denominator clearing -/

/-- Product of all rational denominators appearing in `c`. -/
@[expose] def clearScale (c : BimatrixCode) : ℤ :=
  (c.matA.map fun row => (row.map fun q => (q.den : ℤ)).prod).prod *
    (c.matB.map fun row => (row.map fun q => (q.den : ℤ)).prod).prod

/-- Scale a single rational `q` by `D` via exact truncated division `q.num * (D.tdiv q.den)`. -/
@[expose] def scaledEntry (D : ℤ) (q : ℚ) : ℤ :=
  q.num * (D.tdiv (q.den : ℤ))

/-- Clear denominators of a matrix of rationals using scale factor `D`. -/
private def clearMat (D : ℤ) (M : List (List ℚ)) : List (List ℤ) :=
  M.map fun row => row.map (scaledEntry D)

@[fun_prop]
theorem clearScale_polytime :
    ComputableInPolyTime clearScale encBimatrix encIntBin := by
  unfold clearScale
  fun_prop

@[fun_prop]
theorem scaledEntry_polytime {α : Type} {encIn : α ↪ List Bool}
    {D : α → ℤ} {q : α → ℚ}
    (hD : ComputableInPolyTime D encIn encIntBin)
    (hq : ComputableInPolyTime q encIn encRat) :
    ComputableInPolyTime (fun x => scaledEntry (D x) (q x)) encIn encIntBin := by
  unfold scaledEntry
  fun_prop

@[local fun_prop]
private theorem clearMat_polytime {α : Type} {encIn : α ↪ List Bool}
    {D : α → ℤ} {M : α → List (List ℚ)}
    (hD : ComputableInPolyTime D encIn encIntBin)
    (hM : ComputableInPolyTime M encIn (encList (encList encRat))) :
    ComputableInPolyTime (fun x => clearMat (D x) (M x)) encIn encIntTable := by
  unfold clearMat
  refine mapWithInput (encA := encList encRat) hM ?_
  refine mapWithInput (encA := encRat) (snd _ _) ?_
  exact scaledEntry_polytime (hD.comp ((fst _ _).comp (fst _ _))) (snd _ _)

@[local fun_prop]
private theorem codeFst_polytime :
    ComputableInPolyTime (fun c : BimatrixCode => c.matA) encBimatrix
      (encList (encList encRat)) :=
  encBimatrix_matA_polyTime .id'

@[local fun_prop]
private theorem codeSnd_polytime :
    ComputableInPolyTime (fun c : BimatrixCode => c.matB) encBimatrix
      (encList (encList encRat)) :=
  encBimatrix_matB_polyTime .id'

@[fun_prop]
theorem codeRows_polytime :
    ComputableInPolyTime rows encBimatrix encUnary := by
  unfold rows
  exact (length_list _).comp codeFst_polytime

@[fun_prop]
theorem codeCols_polytime :
    ComputableInPolyTime cols encBimatrix encUnary := by
  unfold cols
  exact (length_list _).comp ((headD (encA := encList encRat) []).comp codeFst_polytime)

@[fun_prop]
theorem wellFormedB_polytime :
    ComputableInPolyTime wellFormedB encBimatrix encBool := by
  have hallCols : ∀ {M : BimatrixCode → List (List ℚ)},
      ComputableInPolyTime M encBimatrix (encList (encList encRat)) →
      ComputableInPolyTime (fun c : BimatrixCode => (M c).all fun r => decide (r.length = c.cols))
        encBimatrix encBool := fun hM =>
    allWithInput (encA := encList encRat) hM
      (decide_eq' ((length_list encRat).comp (snd _ _)) (codeCols_polytime.comp (fst _ _)))
  have ha1 := hallCols codeFst_polytime
  have ha2 := hallCols codeSnd_polytime
  unfold wellFormedB
  fun_prop

/-! ### Section 3: Exact FNP verifier -/

private def witnessDecoder : Decoder encWitnessPairs :=
  Decoder.pair (Decoder.list (Decoder.pair Decoder.intBin Decoder.nat))
    (Decoder.list (Decoder.pair Decoder.intBin Decoder.nat))

/-- Check that `(num, den)` represents a canonical lowest-terms nonnegative rational (`0 ≤ num`,
`0 < den`, `gcd |num| den = 1`). -/
private def isCanonicalNonnegPair (pq : ℤ × ℕ) : Bool :=
  decide (0 ≤ pq.1) && decide (0 < pq.2) && decide (Nat.gcd pq.1.natAbs pq.2 = 1)

/-- Rational value `(pq.1 : ℚ) / (pq.2 : ℚ)` of a numerator-denominator pair. -/
private def mkRatOfPair (pq : ℤ × ℕ) : ℚ :=
  (pq.1 : ℚ) / (pq.2 : ℚ)

private lemma mkRatOfPair_num_den {pq : ℤ × ℕ} (hc : isCanonicalNonnegPair pq = true) :
    (mkRatOfPair pq).num = pq.1 ∧ (mkRatOfPair pq).den = pq.2 := by
  simp only [isCanonicalNonnegPair, Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc with ⟨⟨_, hq⟩, hgcd⟩
  have hr : mkRatOfPair pq = Rat.divInt pq.1 (pq.2 : ℤ) := by
    simp only [mkRatOfPair, ← Int.cast_natCast (R := ℚ), Rat.divInt_eq_div]
  have hgcdZ : (pq.2 : ℤ).gcd pq.1 = 1 := by
    rw [Int.gcd, Int.natAbs_natCast, Nat.gcd_comm]
    exact hgcd
  have hne0 : pq.2 ≠ 0 := by omega
  rw [hr, Rat.num_divInt, Rat.den_divInt, Int.sign_eq_one_of_pos (by omega), hgcdZ]
  simp [hne0]

private lemma rat_isCanonical {q : ℚ} (hq : 0 ≤ q) :
    isCanonicalNonnegPair (q.num, q.den) = true := by
  simp only [isCanonicalNonnegPair, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨Rat.num_nonneg.2 hq, Nat.pos_of_ne_zero q.den_nz⟩, q.reduced⟩

private def scaleVecNum (D : ℤ) (v : List (ℤ × ℕ)) : List ℤ :=
  v.map fun pq => pq.1 * D.tdiv (pq.2 : ℤ)

private def transposeRows (m n : ℕ) (M : List (List ℤ)) : List (List ℤ) :=
  (List.range n).map fun j => (List.range m).map fun i => rowEntry M i j

private def rowPayoffs (M : List (List ℤ)) (k : ℕ) (v : List ℤ) : List ℤ :=
  M.map fun row => ListMatrix.dotProduct k row v

private def clearMatA (c : BimatrixCode) : List (List ℤ) := clearMat (clearScale c) c.matA
private def clearMatB (c : BimatrixCode) : List (List ℤ) := clearMat (clearScale c) c.matB

private def vecProdDen (v : List (ℤ × ℕ)) : ℤ := (v.map fun pq => (pq.2 : ℤ)).prod

private def pay1Vec (c : BimatrixCode) (yl : List (ℤ × ℕ)) : List ℤ :=
  rowPayoffs (clearMatA c) c.cols (scaleVecNum (vecProdDen yl) yl)

private def pay2Vec (c : BimatrixCode) (xl : List (ℤ × ℕ)) : List ℤ :=
  rowPayoffs (transposeRows c.rows c.cols (clearMatB c)) c.rows (scaleVecNum (vecProdDen xl) xl)

private def brCheck (D mix : ℤ) (pays : List ℤ) : Bool :=
  pays.all fun v => decide (D * v ≤ mix)

private def verifiesDecoded (c : BimatrixCode) (w : List Bool)
    (dec : List (ℤ × ℕ) × List (ℤ × ℕ)) : Bool :=
  decide (encWitnessPairs dec = w) &&
    decide (dec.1.length = c.rows) && decide (dec.2.length = c.cols) &&
    dec.1.all isCanonicalNonnegPair && dec.2.all isCanonicalNonnegPair &&
    decide ((scaleVecNum (vecProdDen dec.1) dec.1).sum = vecProdDen dec.1) &&
    decide ((scaleVecNum (vecProdDen dec.2) dec.2).sum = vecProdDen dec.2) &&
    brCheck (vecProdDen dec.1)
      (ListMatrix.dotProduct c.rows (scaleVecNum (vecProdDen dec.1) dec.1) (pay1Vec c dec.2))
      (pay1Vec c dec.2) &&
    brCheck (vecProdDen dec.2)
      (ListMatrix.dotProduct c.cols (scaleVecNum (vecProdDen dec.2) dec.2) (pay2Vec c dec.1))
      (pay2Vec c dec.1)

private def verifiesBimatrixNash (p : BimatrixCode × List Bool) : Bool :=
  if !p.1.wellFormedB then p.2.isEmpty
  else verifiesDecoded p.1 p.2 (witnessDecoder.decode p.2)

@[local fun_prop]
private theorem witnessDecoder_polytime :
    ComputableInPolyTime witnessDecoder.decode encBits encWitnessPairs :=
  witnessDecoder.computableInPolyTime

@[local fun_prop]
private theorem isCanonicalNonnegPair_polytime :
    ComputableInPolyTime isCanonicalNonnegPair encRatData encBool := by
  unfold isCanonicalNonnegPair
  fun_prop

@[local fun_prop]
private theorem vecProdDen_polytime {α : Type} {encIn : α ↪ List Bool}
    {v : α → List (ℤ × ℕ)} (hv : ComputableInPolyTime v encIn (encList encRatData)) :
    ComputableInPolyTime (fun x => vecProdDen (v x)) encIn encIntBin := by
  unfold vecProdDen
  fun_prop

@[local fun_prop]
private theorem scaleVecNum_polytime {α : Type} {encIn : α ↪ List Bool}
    {D : α → ℤ} {v : α → List (ℤ × ℕ)}
    (hD : ComputableInPolyTime D encIn encIntBin)
    (hv : ComputableInPolyTime v encIn (encList encRatData)) :
    ComputableInPolyTime (fun x => scaleVecNum (D x) (v x)) encIn (encList encIntBin) := by
  unfold scaleVecNum
  refine mapWithInput (encA := encRatData) hv ?_
  exact intBin_mul' ((fst encIntBin encNat).comp (snd _ _))
    (intBin_tdiv' (hD.comp (fst _ _))
      (intBin_natCast.comp ((snd encIntBin encNat).comp (snd _ _))))

@[local fun_prop]
private theorem transposeRows_polytime {α : Type} {encIn : α ↪ List Bool}
    {m n : α → ℕ} {M : α → List (List ℤ)}
    (hm : ComputableInPolyTime m encIn encUnary)
    (hn : ComputableInPolyTime n encIn encUnary)
    (hM : ComputableInPolyTime M encIn encIntTable) :
    ComputableInPolyTime (fun x => transposeRows (m x) (n x) (M x)) encIn encIntTable := by
  unfold transposeRows
  refine mapWithInput (encA := encUnary) (range.comp hn) ?_
  refine mapWithInput (encA := encUnary) (range.comp (hm.comp (fst _ _))) ?_
  exact computableInPolyTime_rowEntry (hM.comp ((fst _ _).comp (fst _ _)))
    (snd _ _) ((snd _ _).comp (fst _ _))

@[local fun_prop]
private theorem rowPayoffs_polytime {α : Type} {encIn : α ↪ List Bool}
    {M : α → List (List ℤ)} {k : α → ℕ} {v : α → List ℤ}
    (hM : ComputableInPolyTime M encIn encIntTable)
    (hk : ComputableInPolyTime k encIn encUnary)
    (hv : ComputableInPolyTime v encIn (encList encIntBin)) :
    ComputableInPolyTime (fun x => rowPayoffs (M x) (k x) (v x)) encIn (encList encIntBin) := by
  unfold rowPayoffs
  refine mapWithInput (encA := encList encIntBin) hM ?_
  exact listDotProduct.comp ((hk.comp (fst _ _)).prod ((snd _ _).prod (hv.comp (fst _ _))))

@[local fun_prop]
private theorem clearMatA_polytime :
    ComputableInPolyTime clearMatA encBimatrix encIntTable := by
  unfold clearMatA
  exact clearMat_polytime clearScale_polytime codeFst_polytime

@[local fun_prop]
private theorem clearMatB_polytime :
    ComputableInPolyTime clearMatB encBimatrix encIntTable := by
  unfold clearMatB
  exact clearMat_polytime clearScale_polytime codeSnd_polytime

@[local fun_prop]
private theorem pay1Vec_polytime {α : Type} {encIn : α ↪ List Bool}
    {c : α → BimatrixCode} {yl : α → List (ℤ × ℕ)}
    (hc : ComputableInPolyTime c encIn encBimatrix)
    (hyl : ComputableInPolyTime yl encIn (encList encRatData)) :
    ComputableInPolyTime (fun x => pay1Vec (c x) (yl x)) encIn (encList encIntBin) := by
  unfold pay1Vec
  exact rowPayoffs_polytime (clearMatA_polytime.comp hc) (codeCols_polytime.comp hc)
    (scaleVecNum_polytime (vecProdDen_polytime hyl) hyl)

@[local fun_prop]
private theorem pay2Vec_polytime {α : Type} {encIn : α ↪ List Bool}
    {c : α → BimatrixCode} {xl : α → List (ℤ × ℕ)}
    (hc : ComputableInPolyTime c encIn encBimatrix)
    (hxl : ComputableInPolyTime xl encIn (encList encRatData)) :
    ComputableInPolyTime (fun x => pay2Vec (c x) (xl x)) encIn (encList encIntBin) := by
  unfold pay2Vec
  exact rowPayoffs_polytime
    (transposeRows_polytime (codeRows_polytime.comp hc) (codeCols_polytime.comp hc)
      (clearMatB_polytime.comp hc))
    (codeRows_polytime.comp hc)
    (scaleVecNum_polytime (vecProdDen_polytime hxl) hxl)

@[local fun_prop]
private theorem brCheck_polytime {α : Type} {encIn : α ↪ List Bool}
    {D mix : α → ℤ} {pays : α → List ℤ}
    (hD : ComputableInPolyTime D encIn encIntBin)
    (hmix : ComputableInPolyTime mix encIn encIntBin)
    (hpays : ComputableInPolyTime pays encIn (encList encIntBin)) :
    ComputableInPolyTime (fun x => brCheck (D x) (mix x) (pays x)) encIn encBool := by
  unfold brCheck
  refine allWithInput (encA := encIntBin) hpays ?_
  exact intBin_le' (intBin_mul' (hD.comp (fst _ _)) (snd _ _)) (hmix.comp (fst _ _))

private theorem verifiesDecoded_polytime {α : Type} {encIn : α ↪ List Bool}
    {c : α → BimatrixCode} {w : α → List Bool} {dec : α → List (ℤ × ℕ) × List (ℤ × ℕ)}
    (hc : ComputableInPolyTime c encIn encBimatrix)
    (hw : ComputableInPolyTime w encIn encBits)
    (hdec : ComputableInPolyTime dec encIn encWitnessPairs) :
    ComputableInPolyTime (fun x => verifiesDecoded (c x) (w x) (dec x)) encIn encBool := by
  have hreenc : ComputableInPolyTime (fun x => encWitnessPairs (dec x)) encIn encBits :=
    (of_eq (f := fun z => encWitnessPairs z) (encIn := encWitnessPairs)
      (encOut := encBits) fun _ => rfl).comp hdec
  have hxl : ComputableInPolyTime (fun x => (dec x).1) encIn (encList encRatData) :=
    (fst _ _).comp hdec
  have hyl : ComputableInPolyTime (fun x => (dec x).2) encIn (encList encRatData) :=
    (snd _ _).comp hdec
  have hDx := vecProdDen_polytime hxl
  have hDy := vecProdDen_polytime hyl
  have hxs := scaleVecNum_polytime hDx hxl
  have hys := scaleVecNum_polytime hDy hyl
  have hp1 := pay1Vec_polytime hc hyl
  have hp2 := pay2Vec_polytime hc hxl
  have hm1 : ComputableInPolyTime
      (fun x => ListMatrix.dotProduct (c x).rows
        (scaleVecNum (vecProdDen (dec x).1) (dec x).1) (pay1Vec (c x) (dec x).2))
      encIn encIntBin := listDotProduct.comp ((codeRows_polytime.comp hc).prod (hxs.prod hp1))
  have hm2 : ComputableInPolyTime
      (fun x => ListMatrix.dotProduct (c x).cols
        (scaleVecNum (vecProdDen (dec x).2) (dec x).2) (pay2Vec (c x) (dec x).1))
      encIn encIntBin := listDotProduct.comp ((codeCols_polytime.comp hc).prod (hys.prod hp2))
  have hallCanon : ∀ {v : α → List (ℤ × ℕ)},
      ComputableInPolyTime v encIn (encList encRatData) →
      ComputableInPolyTime (fun x => (v x).all isCanonicalNonnegPair) encIn encBool := fun hv =>
    allWithInput (encA := encRatData) hv (isCanonicalNonnegPair_polytime.comp (snd _ _))
  unfold verifiesDecoded
  refine bool_and' ?_ (brCheck_polytime hDy hm2 hp2)
  refine bool_and' ?_ (brCheck_polytime hDx hm1 hp1)
  refine bool_and' ?_ (decide_eq' (intBin_sum.comp hys) hDy)
  refine bool_and' ?_ (decide_eq' (intBin_sum.comp hxs) hDx)
  refine bool_and' ?_ (hallCanon hyl)
  refine bool_and' ?_ (hallCanon hxl)
  refine bool_and' ?_ (decide_eq' ((length_list encRatData).comp hyl) (codeCols_polytime.comp hc))
  exact bool_and' (decide_eq' hreenc hw)
    (decide_eq' ((length_list encRatData).comp hxl) (codeRows_polytime.comp hc))

private theorem verifiesBimatrixNash_polytime :
    ComputableInPolyTime verifiesBimatrixNash (encPair encBimatrix encBits) encBool := by
  have hdec := verifiesDecoded_polytime (fst encBimatrix encBits) (snd encBimatrix encBits)
    (witnessDecoder_polytime.comp (snd encBimatrix encBits))
  have hi := ite' (bool_not.comp (wellFormedB_polytime.comp (fst encBimatrix encBits)))
    (bitsIsEmpty.comp (snd encBimatrix encBits)) hdec
  exact hi.of_enc_eq (encD := encBool) fun p => by
    simp only [verifiesBimatrixNash, Function.comp_apply]

private lemma encWitness_eq_pairs (x y : List ℚ) :
    encWitness ⟨x, y⟩ =
      encWitnessPairs (x.map (fun q => (q.num, q.den)), y.map (fun q => (q.num, q.den))) := by
  have hmap (l : List ℚ) :
      encList encRat l = encList encRatData (l.map fun q => (q.num, q.den)) := by
    induction l with
    | nil => rfl
    | cons _ _ ih => simp only [encList_cons, List.map_cons, ih, encRat_apply]
  simp only [encWitness_apply, encPair_apply, hmap]

theorem clearScale_pos (c : BimatrixCode) : 0 < clearScale c := by
  have hprod (M : List (List ℚ)) :
      0 < (M.map fun row => (row.map fun q => (q.den : ℤ)).prod).prod :=
    List.prod_pos <| List.forall_mem_map.2 fun _ _ =>
      List.prod_pos <| List.forall_mem_map.2 fun q _ => Int.natCast_pos.2 q.den_pos
  exact mul_pos (hprod c.matA) (hprod c.matB)

theorem den_dvd_clearScale {c : BimatrixCode} {M : List (List ℚ)}
    (hM : M = c.matA ∨ M = c.matB) {r : List ℚ} (hr : r ∈ M) {q : ℚ} (hq : q ∈ r) :
    (q.den : ℤ) ∣ clearScale c := by
  have hdvd : (q.den : ℤ) ∣ (M.map fun row => (row.map fun q => (q.den : ℤ)).prod).prod :=
    (List.dvd_prod (List.mem_map_of_mem (f := fun q : ℚ => (q.den : ℤ)) hq)).trans
      (List.dvd_prod
        (List.mem_map_of_mem (f := fun row : List ℚ => (row.map fun q => (q.den : ℤ)).prod) hr))
  rcases hM with rfl | rfl
  · exact dvd_mul_of_dvd_left hdvd _
  · exact dvd_mul_of_dvd_right hdvd _

theorem scaledEntry_cast {D : ℤ} {q : ℚ} (hdvd : (q.den : ℤ) ∣ D) :
    ((scaledEntry D q : ℤ) : ℚ) = (D : ℚ) * q := by
  rcases hdvd with ⟨k, rfl⟩
  have hneZ : (q.den : ℤ) ≠ 0 := Nat.cast_ne_zero.2 q.den_nz
  have hneQ : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.2 q.den_nz
  simp only [scaledEntry, Int.mul_tdiv_cancel_left k hneZ, Int.cast_mul, Int.cast_natCast]
  rw [(div_eq_iff hneQ).1 (Rat.num_div_den q)]
  ring

private lemma clearMat_getD_cast {c : BimatrixCode} (hc : c.WellFormed)
    (i : Fin c.rows) (j : Fin c.cols) :
    (((clearMatA c).getD i.val []).getD j.val 0 : ℚ) = (clearScale c : ℚ) * c.toMatA i j ∧
      (((clearMatB c).getD i.val []).getD j.val 0 : ℚ) = (clearScale c : ℚ) * c.toMatB i j := by
  obtain ⟨_, _, hl2, hr1, hr2⟩ := hc
  have aux (M : List (List ℚ)) (hM : M = c.matA ∨ M = c.matB)
      (hlen : M.length = c.rows) (hrows : ∀ r ∈ M, r.length = c.cols) :
      (((clearMat (clearScale c) M).getD i.val []).getD j.val 0 : ℚ) =
        (clearScale c : ℚ) * (M.getD i.val []).getD j.val 0 := by
    have hi : i.val < M.length := by omega
    have hrmem : M.getD i.val [] ∈ M := List.getD_mem [] hi
    have hj : j.val < (M.getD i.val []).length := by have := hrows _ hrmem; omega
    rw [clearMat, List.getD_map_of_lt _ M [] [] hi, List.getD_map_of_lt _ _ 0 0 hj]
    exact scaledEntry_cast (den_dvd_clearScale hM hrmem (List.getD_mem 0 hj))
  exact ⟨aux c.matA (Or.inl rfl) rfl hr1, aux c.matB (Or.inr rfl) hl2 hr2⟩

private lemma vecProdDen_pos {v : List (ℤ × ℕ)} (hv : v.all isCanonicalNonnegPair = true) :
    0 < vecProdDen v :=
  List.prod_pos <| List.forall_mem_map.2 fun pq hpq => by
    have h := (List.all_eq_true.1 hv) pq hpq
    simp only [isCanonicalNonnegPair, Bool.and_eq_true, decide_eq_true_eq] at h
    omega

private lemma den_dvd_vecProdDen {v : List (ℤ × ℕ)} {pq : ℤ × ℕ} (hpq : pq ∈ v) :
    (pq.2 : ℤ) ∣ vecProdDen v :=
  List.dvd_prod (List.mem_map_of_mem hpq)

private lemma scaleVecNum_getD_cast {v : List (ℤ × ℕ)} (hv : v.all isCanonicalNonnegPair = true)
    {k : ℕ} (hk : v.length = k) (i : Fin k) :
    ((scaleVecNum (vecProdDen v) v).getD i.val 0 : ℚ) =
      (vecProdDen v : ℚ) * (v.map mkRatOfPair).getD i.val 0 := by
  have hi : i.val < v.length := by omega
  have hpq : v.getD i.val (0, 0) ∈ v := List.getD_mem (0, 0) hi
  have hmem := (List.all_eq_true.1 hv) _ hpq
  simp only [isCanonicalNonnegPair, Bool.and_eq_true, decide_eq_true_eq] at hmem
  rcases den_dvd_vecProdDen hpq with ⟨t, ht⟩
  have hneZ : ((v.getD i.val (0, 0)).2 : ℤ) ≠ 0 := by omega
  have hneQ : ((v.getD i.val (0, 0)).2 : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [scaleVecNum, List.getD_map_of_lt _ v (0, 0) 0 hi,
    List.getD_map_of_lt mkRatOfPair v (0, 0) 0 hi, ht, Int.mul_tdiv_cancel_left t hneZ]
  simp only [mkRatOfPair, Int.cast_mul, Int.cast_natCast]
  field_simp [hneQ]

private lemma rowPayoffs_scaleVecNum_getD_cast {m n : ℕ} {M_int : List (List ℤ)}
    (hM_len : M_int.length = m) {C : ℚ} {entry : Fin m → Fin n → ℚ}
    (hentry : ∀ (i : Fin m) (j : Fin n), ((M_int.getD i.val []).getD j.val 0 : ℚ) = C * entry i j)
    {vl : List (ℤ × ℕ)} (hvl_c : vl.all isCanonicalNonnegPair = true) (hvl_len : vl.length = n)
    (i : Fin m) :
    ((rowPayoffs M_int n (scaleVecNum (vecProdDen vl) vl)).getD i.val 0 : ℚ) =
      C * (vecProdDen vl : ℚ) * ∑ j : Fin n, entry i j * (vl.map mkRatOfPair).getD j.val 0 := by
  have hi : i.val < M_int.length := hM_len ▸ i.isLt
  rw [rowPayoffs, List.getD_map_of_lt _ M_int [] 0 hi,
    ListMatrix.dotProduct_eq_sum_map_range, List.sum_map_range]
  push_cast
  calc
    ∑ j : Fin n, ((M_int.getD i.val []).getD j.val 0 : ℚ) *
        ((scaleVecNum (vecProdDen vl) vl).getD j.val 0 : ℚ)
      = ∑ j : Fin n, (C * entry i j) *
          ((vecProdDen vl : ℚ) * (vl.map mkRatOfPair).getD j.val 0) :=
        Finset.sum_congr rfl fun j _ => by
          rw [hentry i j, scaleVecNum_getD_cast hvl_c hvl_len j]
    _ = C * (vecProdDen vl : ℚ) * ∑ j : Fin n, entry i j * (vl.map mkRatOfPair).getD j.val 0 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring

private lemma pay1Vec_getD_cast {c : BimatrixCode} (hc : c.WellFormed)
    {yl : List (ℤ × ℕ)} (hyl_c : yl.all isCanonicalNonnegPair = true) (hyl_len : yl.length = c.cols)
    (i : Fin c.rows) :
    ((pay1Vec c yl).getD i.val 0 : ℚ) =
      (clearScale c : ℚ) * (vecProdDen yl : ℚ) *
        ∑ j : Fin c.cols, c.toMatA i j * (yl.map mkRatOfPair).getD j.val 0 :=
  rowPayoffs_scaleVecNum_getD_cast (by simp [clearMatA, clearMat, rows])
    (fun a b => (clearMat_getD_cast hc a b).1) hyl_c hyl_len i

private lemma pay2Vec_getD_cast {c : BimatrixCode} (hc : c.WellFormed)
    {xl : List (ℤ × ℕ)} (hxl_c : xl.all isCanonicalNonnegPair = true) (hxl_len : xl.length = c.rows)
    (j : Fin c.cols) :
    ((pay2Vec c xl).getD j.val 0 : ℚ) =
      (clearScale c : ℚ) * (vecProdDen xl : ℚ) *
        ∑ i : Fin c.rows, (xl.map mkRatOfPair).getD i.val 0 * c.toMatB i j := by
  rw [pay2Vec, rowPayoffs_scaleVecNum_getD_cast (entry := fun b i => c.toMatB i b)
    (by simp [transposeRows])
    (fun b a => by
      simp only [transposeRows]
      rw [List.getD_map_range _ [] b.isLt, List.getD_map_range _ 0 a.isLt]
      exact (clearMat_getD_cast hc a b).2)
    hxl_c hxl_len j]
  exact congrArg _ (Finset.sum_congr rfl fun _ _ => mul_comm _ _)

private lemma brCheck_iff {D mix : ℤ} {pays : List ℤ} {k : ℕ} (hk : pays.length = k) :
    brCheck D mix pays = true ↔ ∀ i : Fin k, D * pays.getD i.val 0 ≤ mix := by
  simp only [brCheck, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h i
    exact h _ (List.getD_mem 0 (by omega))
  · intro h v hv
    rcases List.mem_iff_getElem.1 hv with ⟨i, hi, rfl⟩
    have hi' : i < k := by omega
    simpa only [List.getD_eq_getElem pays 0 hi] using h ⟨i, hi'⟩

private lemma bilinear_dotProduct_eq_cast {m n : ℕ} (xl yl : List (ℤ × ℕ)) (pv : List ℤ)
    (C : ℚ) (M : Fin m → Fin n → ℚ)
    (hxl_c : xl.all isCanonicalNonnegPair = true) (hxl_len : xl.length = m)
    (hpv : ∀ a : Fin m, (pv.getD a.val 0 : ℚ) =
      C * (vecProdDen yl : ℚ) * ∑ j : Fin n, M a j * (yl.map mkRatOfPair).getD j.val 0) :
    ((ListMatrix.dotProduct m (scaleVecNum (vecProdDen xl) xl) pv : ℤ) : ℚ) =
      (vecProdDen xl : ℚ) * C * (vecProdDen yl : ℚ) *
        ∑ a : Fin m, ∑ j : Fin n,
          (xl.map mkRatOfPair).getD a.val 0 * M a j * (yl.map mkRatOfPair).getD j.val 0 := by
  rw [ListMatrix.dotProduct_eq_sum_map_range, List.sum_map_range]
  push_cast
  calc
    ∑ a : Fin m, ((scaleVecNum (vecProdDen xl) xl).getD a.val 0 : ℚ) * (pv.getD a.val 0 : ℚ)
      = ∑ a : Fin m, ((vecProdDen xl : ℚ) * (xl.map mkRatOfPair).getD a.val 0) *
          (C * (vecProdDen yl : ℚ) *
            ∑ j : Fin n, M a j * (yl.map mkRatOfPair).getD j.val 0) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [scaleVecNum_getD_cast hxl_c hxl_len a, hpv a]
    _ = (vecProdDen xl : ℚ) * C * (vecProdDen yl : ℚ) *
          ∑ a : Fin m, ∑ j : Fin n,
            (xl.map mkRatOfPair).getD a.val 0 * M a j * (yl.map mkRatOfPair).getD j.val 0 := by
          simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring

private lemma mix1_eq_cast {c : BimatrixCode} (hc : c.WellFormed)
    {xl yl : List (ℤ × ℕ)} (hxl_c : xl.all isCanonicalNonnegPair = true)
    (hyl_c : yl.all isCanonicalNonnegPair = true)
    (hxl_len : xl.length = c.rows) (hyl_len : yl.length = c.cols) :
    ((ListMatrix.dotProduct c.rows (scaleVecNum (vecProdDen xl) xl)
        (pay1Vec c yl) : ℤ) : ℚ) =
      (vecProdDen xl : ℚ) * (clearScale c : ℚ) * (vecProdDen yl : ℚ) *
        ∑ a : Fin c.rows, ∑ j : Fin c.cols,
          (xl.map mkRatOfPair).getD a.val 0 * c.toMatA a j * (yl.map mkRatOfPair).getD j.val 0 :=
  bilinear_dotProduct_eq_cast xl yl (pay1Vec c yl) (clearScale c) c.toMatA
    hxl_c hxl_len (pay1Vec_getD_cast hc hyl_c hyl_len)

private lemma mix2_eq_cast {c : BimatrixCode} (hc : c.WellFormed)
    {xl yl : List (ℤ × ℕ)} (hxl_c : xl.all isCanonicalNonnegPair = true)
    (hyl_c : yl.all isCanonicalNonnegPair = true)
    (hxl_len : xl.length = c.rows) (hyl_len : yl.length = c.cols) :
    ((ListMatrix.dotProduct c.cols (scaleVecNum (vecProdDen yl) yl)
        (pay2Vec c xl) : ℤ) : ℚ) =
      (vecProdDen yl : ℚ) * (clearScale c : ℚ) * (vecProdDen xl : ℚ) *
        ∑ i : Fin c.rows, ∑ b : Fin c.cols,
          (xl.map mkRatOfPair).getD i.val 0 * c.toMatB i b * (yl.map mkRatOfPair).getD b.val 0 := by
  rw [bilinear_dotProduct_eq_cast yl xl (pay2Vec c xl) (clearScale c) (fun b i => c.toMatB i b)
      hyl_c hyl_len (fun b => by
        rw [pay2Vec_getD_cast hc hxl_c hxl_len b]
        refine congrArg _ (Finset.sum_congr rfl fun i _ => mul_comm _ _)),
      Finset.sum_comm]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => by ring)

private lemma all_mkRatOfPair_nonneg {l : List (ℤ × ℕ)}
    (hl : l.all isCanonicalNonnegPair = true) : ∀ q ∈ l.map mkRatOfPair, 0 ≤ q := by
  intro q hq
  rcases List.mem_map.1 hq with ⟨pq, hpq, rfl⟩
  have hpqc := (List.all_eq_true.1 hl) pq hpq
  simp only [isCanonicalNonnegPair, Bool.and_eq_true, decide_eq_true_eq] at hpqc
  exact div_nonneg (by exact_mod_cast hpqc.1.1) (by exact_mod_cast Nat.zero_le pq.2)

private lemma scaleVecNum_sum_cast {n : ℕ} {l : List (ℤ × ℕ)}
    (hl_c : l.all isCanonicalNonnegPair = true) (hl_len : l.length = n) :
    ((scaleVecNum (vecProdDen l) l).sum : ℚ) =
      (vecProdDen l : ℚ) * (l.map mkRatOfPair).sum := by
  rw [← List.ofFn_getD_eq_of_length (n := n) (l := scaleVecNum (vecProdDen l) l) 0
      (by simp [scaleVecNum, hl_len]),
    ← List.ofFn_getD_eq_of_length (n := n) (l := l.map mkRatOfPair) 0 (by simp [hl_len]),
    List.sum_ofFn, List.sum_ofFn]
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => scaleVecNum_getD_cast hl_c hl_len i

private lemma sum_map_mkRatOfPair_eq_one {n : ℕ} {l : List (ℤ × ℕ)}
    (hl_c : l.all isCanonicalNonnegPair = true) (hl_len : l.length = n)
    (hsum : (scaleVecNum (vecProdDen l) l).sum = vecProdDen l) :
    (l.map mkRatOfPair).sum = 1 := by
  have hD : (vecProdDen l : ℚ) ≠ 0 := by exact_mod_cast (vecProdDen_pos hl_c).ne'
  have hsQ : ((scaleVecNum (vecProdDen l) l).sum : ℚ) = (vecProdDen l : ℚ) * 1 := by
    rw [mul_one]
    exact_mod_cast hsum
  exact mul_left_cancel₀ hD ((scaleVecNum_sum_cast hl_c hl_len).symm.trans hsQ)

private lemma scaleVecNum_sum_eq_vecProdDen_of_sum_eq_one {n : ℕ} {l : List (ℤ × ℕ)}
    (hl_c : l.all isCanonicalNonnegPair = true) (hl_len : l.length = n)
    (hsum : (l.map mkRatOfPair).sum = 1) :
    (scaleVecNum (vecProdDen l) l).sum = vecProdDen l :=
  Int.cast_injective (α := ℚ) ((scaleVecNum_sum_cast hl_c hl_len).trans (by rw [hsum, mul_one]))

private lemma map_pair_mkRatOfPair_eq {l : List (ℤ × ℕ)}
    (hl : l.all isCanonicalNonnegPair = true) :
    (l.map mkRatOfPair).map (fun q => (q.num, q.den)) = l := by
  induction l with
  | nil => rfl
  | cons pq l ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hl
    have hpq : ((mkRatOfPair pq).num, (mkRatOfPair pq).den) = pq :=
      Prod.ext (mkRatOfPair_num_den hl.1).1 (mkRatOfPair_num_den hl.1).2
    simp only [List.map_cons, hpq, ih hl.2]

private lemma all_isCanonicalNonnegPair_of_nonneg {l : List ℚ} (hl : ∀ q ∈ l, 0 ≤ q) :
    (l.map fun q => (q.num, q.den)).all isCanonicalNonnegPair = true :=
  List.all_eq_true.2 <| List.forall_mem_map.2 fun q hq => rat_isCanonical (hl q hq)

private lemma map_mkRatOfPair_pair_eq (l : List ℚ) :
    (l.map fun q => (q.num, q.den)).map mkRatOfPair = l := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    simp only [List.map_cons, mkRatOfPair, Rat.num_div_den, ih]

private lemma brCheck_dotProduct_iff {m : ℕ} {ul : List (ℤ × ℕ)} {pv : List ℤ}
    {S payMix : ℚ} {payPure : Fin m → ℚ}
    (hpv_len : pv.length = m) (hDu : 0 < (vecProdDen ul : ℚ)) (hS : 0 < S)
    (hpv : ∀ i : Fin m, (pv.getD i.val 0 : ℚ) = S * payPure i)
    (hmix : ((ListMatrix.dotProduct m (scaleVecNum (vecProdDen ul) ul) pv : ℤ) : ℚ) =
      ((vecProdDen ul : ℚ) * S) * payMix) :
    brCheck (vecProdDen ul)
      (ListMatrix.dotProduct m (scaleVecNum (vecProdDen ul) ul) pv) pv = true ↔
      ∀ i : Fin m, payPure i ≤ payMix := by
  rw [brCheck_iff hpv_len]
  have hpos : 0 < (vecProdDen ul : ℚ) * S := mul_pos hDu hS
  refine forall_congr' fun i => ?_
  rw [← Int.cast_le (R := ℚ), Int.cast_mul, hpv i, hmix, ← mul_assoc]
  exact mul_le_mul_iff_right₀ hpos

private lemma verifiesDecoded_iff {c : BimatrixCode} (hc : c.WellFormed)
    (w : List Bool) (dec : List (ℤ × ℕ) × List (ℤ × ℕ)) :
    verifiesDecoded c w dec = true ↔
      w = encWitnessPairs dec ∧
        dec.1.all isCanonicalNonnegPair = true ∧
        dec.2.all isCanonicalNonnegPair = true ∧
        c.IsRationalNash (dec.1.map mkRatOfPair) (dec.2.map mkRatOfPair) := by
  let x := dec.1.map mkRatOfPair
  let y := dec.2.map mkRatOfPair
  have hlenA : (pay1Vec c dec.2).length = c.rows := by
    simp [pay1Vec, rowPayoffs, clearMatA, clearMat, rows]
  have hlenB : (pay2Vec c dec.1).length = c.cols := by
    simp [pay2Vec, rowPayoffs, transposeRows]
  have hDc : (0 : ℚ) < (clearScale c : ℚ) := by exact_mod_cast clearScale_pos c
  have hbr_iff (hcx : dec.1.all isCanonicalNonnegPair = true)
      (hcy : dec.2.all isCanonicalNonnegPair = true)
      (hdx : dec.1.length = c.rows) (hdy : dec.2.length = c.cols) :
      (brCheck (vecProdDen dec.1)
          (ListMatrix.dotProduct c.rows (scaleVecNum (vecProdDen dec.1) dec.1) (pay1Vec c dec.2))
          (pay1Vec c dec.2) = true ↔
        ∀ i : Fin c.rows, (∑ j : Fin c.cols, c.toMatA i j * y.getD j.val 0) ≤
          ∑ a : Fin c.rows, ∑ j : Fin c.cols, x.getD a.val 0 * c.toMatA a j * y.getD j.val 0) ∧
      (brCheck (vecProdDen dec.2)
          (ListMatrix.dotProduct c.cols (scaleVecNum (vecProdDen dec.2) dec.2) (pay2Vec c dec.1))
          (pay2Vec c dec.1) = true ↔
        ∀ j : Fin c.cols, (∑ i : Fin c.rows, x.getD i.val 0 * c.toMatB i j) ≤
          ∑ i : Fin c.rows, ∑ b : Fin c.cols, x.getD i.val 0 * c.toMatB i b * y.getD b.val 0) := by
    have hDx : (0 : ℚ) < (vecProdDen dec.1 : ℚ) := by exact_mod_cast vecProdDen_pos hcx
    have hDy : (0 : ℚ) < (vecProdDen dec.2 : ℚ) := by exact_mod_cast vecProdDen_pos hcy
    refine ⟨brCheck_dotProduct_iff hlenA hDx (mul_pos hDc hDy) (pay1Vec_getD_cast hc hcy hdy)
        (by rw [mix1_eq_cast hc hcx hcy hdx hdy]; dsimp only [x, y]; ring),
      brCheck_dotProduct_iff hlenB hDy (mul_pos hDc hDx) (pay2Vec_getD_cast hc hcx hdx)
        (by rw [mix2_eq_cast hc hcx hcy hdx hdy]; dsimp only [x, y]; ring)⟩
  constructor
  · intro h
    simp only [verifiesDecoded, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨hew, hdx⟩, hdy⟩, hcx⟩, hcy⟩, hsx⟩, hsy⟩, hb1⟩, hb2⟩
    obtain ⟨hbr1, hbr2⟩ := hbr_iff hcx hcy hdx hdy
    exact ⟨hew.symm, hcx, hcy, by simp [hdx], by simp [hdy],
      all_mkRatOfPair_nonneg hcx, sum_map_mkRatOfPair_eq_one hcx hdx hsx,
      all_mkRatOfPair_nonneg hcy, sum_map_mkRatOfPair_eq_one hcy hdy hsy,
      hbr1.1 hb1, hbr2.1 hb2⟩
  · rintro ⟨hew, hcx, hcy, hxlen, hylen, -, hxsum, -, hysum, hbr1, hbr2⟩
    have hdx : dec.1.length = c.rows := by simpa [x] using hxlen
    have hdy : dec.2.length = c.cols := by simpa [y] using hylen
    obtain ⟨hb1, hb2⟩ := hbr_iff hcx hcy hdx hdy
    simp only [verifiesDecoded, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨hew.symm, hdx⟩, hdy⟩, hcx⟩, hcy⟩,
      scaleVecNum_sum_eq_vecProdDen_of_sum_eq_one hcx hdx hxsum⟩,
      scaleVecNum_sum_eq_vecProdDen_of_sum_eq_one hcy hdy hysum⟩,
      hb1.2 hbr1⟩, hb2.2 hbr2⟩

private lemma verifiesBimatrixNash_eq_true_iff (c : BimatrixCode) (w : List Bool) :
    verifiesBimatrixNash (c, w) = true ↔
      if c.wellFormedB then ∃ s : StrategyPair, w = encWitness s ∧ c.IsRationalNash s.x s.y
      else w = [] := by
  by_cases hwb : c.wellFormedB = true
  · have hc : c.WellFormed := (wellFormed_iff_wellFormedB c).2 hwb
    simp only [verifiesBimatrixNash, hwb, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    rw [verifiesDecoded_iff hc w (witnessDecoder.decode w)]
    constructor
    · rintro ⟨hew, hcx, hcy, hrat⟩
      let x := (witnessDecoder.decode w).1.map mkRatOfPair
      let y := (witnessDecoder.decode w).2.map mkRatOfPair
      refine ⟨⟨x, y⟩, ?_, hrat⟩
      rw [hew, encWitness_eq_pairs x y, map_pair_mkRatOfPair_eq hcx, map_pair_mkRatOfPair_eq hcy]
    · rintro ⟨⟨x, y⟩, rfl, hrat⟩
      let dec0 : List (ℤ × ℕ) × List (ℤ × ℕ) :=
        (x.map (fun q => (q.num, q.den)), y.map (fun q => (q.num, q.den)))
      have hdec0 : witnessDecoder.decode (encWitness ⟨x, y⟩) = dec0 := by
        rw [encWitness_eq_pairs x y, witnessDecoder.decode_enc]
      rw [hdec0]
      have hcx := all_isCanonicalNonnegPair_of_nonneg hrat.2.2.1
      have hcy := all_isCanonicalNonnegPair_of_nonneg hrat.2.2.2.2.1
      rw [map_mkRatOfPair_pair_eq x, map_mkRatOfPair_pair_eq y]
      exact ⟨encWitness_eq_pairs x y, hcx, hcy, hrat⟩
  · have hwf : c.wellFormedB = false := Bool.eq_false_iff.2 hwb
    simp only [verifiesBimatrixNash, hwf, Bool.not_false, ite_true, List.isEmpty_iff,
      Bool.false_eq_true, ite_false]

/-- **Two-player rational Nash equilibrium is in `FNP`.** -/
theorem BimatrixNash_mem_FNP : BimatrixNash ∈ FNP encBimatrix := by
  rw [mem_FNP_iff_exists_bounded]
  refine ⟨witnessPoly, verifiesBimatrixNash, verifiesBimatrixNash_polytime, fun c w => ?_⟩
  rw [verifiesBimatrixNash_eq_true_iff]
  by_cases hwb : c.wellFormedB = true
  · simp only [BimatrixNash, hwb, ite_true]
  · have hwf : c.wellFormedB = false := Bool.eq_false_iff.2 hwb
    simp only [BimatrixNash, hwf, Bool.false_eq_true, ite_false]
    exact ⟨fun hw => ⟨by subst hw; simp, hw⟩, fun h => h.2⟩

end BimatrixCode

end Cslib.GameTheory
