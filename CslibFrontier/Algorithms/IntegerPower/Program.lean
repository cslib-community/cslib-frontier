/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.IntegerPower.Basic
public import CslibFrontier.Computability.PolyTime.Int.MatrixPower
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Uniform native integer matrix power search

The input is a row table of signed binary integers and a unary growth threshold. The row count
is the runtime dimension, including for ragged tables. The program searches the first `n + 1`
powers of every standard-basis vector in step order and then seed order, using exactly the
integer squared-norm test of `growingColumn?`. If no test succeeds, it returns the zero vector.

`recoveredIntegerVector_ofFn` identifies this stored-list program with `recoveredVector` for
every square integer matrix, with no spectral premise. The compositional native multitape
certificate `computableInPolyTime_recoveredIntegerVector` charges every candidate test and
integer operation; the matrix-power kernel bounds every intermediate binary encoding.
-/

public section

namespace Cslib.Algorithms.IntegerPower

open Turing.MultiTapeTM Matrix

private structure ColumnCode where
  /-- Unary number of multiplications before testing growth. -/
  steps : ℕ
  /-- Unary seed identifier, with no bounded-index proof stored. -/
  seed : ℕ
  deriving DecidableEq

/-- A framed unary step count followed by the unary seed identifier. -/
private enc_structure encColumnCode : ColumnCode where
  steps : encUnary,
  seed : encUnary

private def PowerColumn.code {n : ℕ} (c : PowerColumn n) : ColumnCode :=
  ⟨c.steps, c.seed.val⟩

private def columnCodes (n : ℕ) : List ColumnCode :=
  (List.range (n + 1)).flatMap fun s => (List.range n).map fun i => ⟨s, i⟩

private def squaredNorm (v : List ℤ) : ℤ :=
  (v.map fun z => z * z).sum

private def growthTest (rows : List (List ℤ)) (k : ℕ) (c : ColumnCode) : Bool :=
  let v := IntTable.powerColumn rows c.steps c.seed
  let w := IntTable.powerColumn rows (c.steps + 1) c.seed
  decide (0 < squaredNorm w ∧ (k : ℤ) ^ 2 * squaredNorm v ≤ 4 * squaredNorm w)

/-- Search stored integer power columns through the dimension, returning the first nonzero
next iterate with squared-norm growth `k² * ‖v‖² ≤ 4 * ‖w‖²`, or a zero vector. -/
def recoveredIntegerVector (rows : List (List ℤ)) (k : ℕ) : List ℤ :=
  ((columnCodes rows.length).find? (growthTest rows k)).elim
    (List.replicate rows.length 0)
    (fun c => IntTable.powerColumn rows (c.steps + 1) c.seed)

/-- The search always returns exactly one coordinate for every matrix row. -/
@[simp] theorem length_recoveredIntegerVector (rows : List (List ℤ)) (k : ℕ) :
    (recoveredIntegerVector rows k).length = rows.length := by
  unfold recoveredIntegerVector
  cases (columnCodes rows.length).find? (growthTest rows k) <;> simp

private theorem columnCodes_eq (n : ℕ) :
    columnCodes n = (powerColumns n).map PowerColumn.code := by
  simp only [columnCodes, powerColumns, List.map_flatMap, List.map_map,
    Function.comp_def, PowerColumn.code]
  congr 1
  funext s
  rw [← List.map_coe_finRange_eq_range]
  simp only [List.map_map, Function.comp_def]

private theorem squaredNorm_ofFn {n : ℕ} (v : Fin n → ℤ) :
    squaredNorm (List.ofFn v) = dotProduct v v := by
  simp [squaredNorm, dotProduct, List.sum_ofFn]

private theorem storedColumn_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (s : ℕ) (i : Fin n) :
    IntTable.powerColumn (List.ofFn fun j => List.ofFn (M j)) s i.val =
      List.ofFn (powerVector M s i) := by
  calc
    _ = List.ofFn fun j => (M ^ s) j i := IntTable.powerColumn_ofFn M s i
    _ = _ := congrArg List.ofFn (funext fun j => (powerVector_apply M s i j).symm)

private theorem growthTest_code {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (k : ℕ) (c : PowerColumn n) :
    growthTest (List.ofFn fun j => List.ofFn (M j)) k c.code = grows M k c := by
  simp only [growthTest, PowerColumn.code, storedColumn_eq, squaredNorm_ofFn, grows]

private theorem find_columnCodes_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) :
    (columnCodes n).find? (growthTest (List.ofFn fun j => List.ofFn (M j)) k) =
      (growingColumn? M k).map PowerColumn.code := by
  simp only [columnCodes_eq, List.find?_map, Function.comp_def, growthTest_code,
    growingColumn?]

/-- On a tabulated square matrix, the native list search returns exactly the mathematical
search vector, including the zero fallback and the candidate order. -/
theorem recoveredIntegerVector_ofFn {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) :
    recoveredIntegerVector (List.ofFn fun j => List.ofFn (M j)) k =
      List.ofFn (recoveredVector M k) := by
  rw [recoveredIntegerVector, List.length_ofFn, find_columnCodes_eq]
  cases h : growingColumn? M k with
  | none =>
    simp only [recoveredVector, h, Option.map_none, Option.elim_none]
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp
  | some c => simpa [recoveredVector, h, PowerColumn.code] using
      storedColumn_eq M (c.steps + 1) c.seed

private theorem computableInPolyTime_columnCodes :
    ComputableInPolyTime columnCodes encUnary (encList encColumnCode) := by
  unfold columnCodes
  fun_prop

private theorem computableInPolyTime_squaredNorm :
    ComputableInPolyTime squaredNorm (encList encIntBin) encIntBin := by
  unfold squaredNorm
  fun_prop

private theorem computableInPolyTime_growthTest {α : Type} {encIn : α ↪ List Bool}
    {rows : α → List (List ℤ)} {k : α → ℕ}
    (hrows : ComputableInPolyTime rows encIn encIntTable)
    (hk : ComputableInPolyTime k encIn encUnary) :
    ComputableInPolyTime (fun p : α × ColumnCode => growthTest (rows p.1) (k p.1) p.2)
      (encPair encIn encColumnCode) encBool := by
  have hk' : ComputableInPolyTime (fun p : α × ColumnCode => (k p.1 : ℤ))
      (encPair encIn encColumnCode) encIntBin :=
    ComputableInPolyTime.intBin_natCast.comp
      (ComputableInPolyTime.unary_to_binary.comp (hk.comp (by fun_prop)))
  unfold growthTest
  have hrows' : ComputableInPolyTime (fun p : α × ColumnCode => rows p.1)
      (encPair encIn encColumnCode) encIntTable := hrows.comp (by fun_prop)
  have hv : ComputableInPolyTime
      (fun p : α × ColumnCode => IntTable.powerColumn (rows p.1) p.2.steps p.2.seed)
      (encPair encIn encColumnCode) (encList encIntBin) := by fun_prop
  have hw : ComputableInPolyTime
      (fun p : α × ColumnCode => IntTable.powerColumn (rows p.1) (p.2.steps + 1) p.2.seed)
      (encPair encIn encColumnCode) (encList encIntBin) := by fun_prop
  have hnv := computableInPolyTime_squaredNorm.comp hv
  have hnw := computableInPolyTime_squaredNorm.comp hw
  dsimp only
  simp only [Bool.decide_and]
  fun_prop

/-- One native multitape polynomial-time machine searches the computed integer matrix. The
matrix dimension and unary growth threshold vary at runtime, with signed binary arithmetic. -/
@[fun_prop] theorem computableInPolyTime_recoveredIntegerVector
    {α : Type} {encIn : α ↪ List Bool} {rows : α → List (List ℤ)} {k : α → ℕ}
    (hrows : ComputableInPolyTime rows encIn encIntTable)
    (hk : ComputableInPolyTime k encIn encUnary) :
    ComputableInPolyTime (fun x => recoveredIntegerVector (rows x) (k x))
      encIn (encList encIntBin) := by
  have hdim := (ComputableInPolyTime.length_list (encList encIntBin)).comp hrows
  unfold recoveredIntegerVector
  apply ComputableInPolyTime.optionElimWithInput
  · exact ComputableInPolyTime.findWithInput
      (computableInPolyTime_columnCodes.comp hdim) (computableInPolyTime_growthTest hrows hk)
  · fun_prop
  · have hrows' := hrows.comp (ComputableInPolyTime.fst encIn encColumnCode)
    fun_prop

end Cslib.Algorithms.IntegerPower
