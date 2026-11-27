/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.PlantedClique.Selection
public import CslibFrontier.Computability.PolyTime.Int.MatrixPower
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# A uniform program for spectral planted-clique recovery

This module realizes the complete recovery algorithm on the dense inputs of `RecoveryInput`.
The vertex count, target clique size, and adjacency word all vary at runtime. Search counters
use unary encodings; matrix and vector entries and squared norms use signed binary encodings.

The program enumerates the same candidate columns in the same order as `growingColumn?`, with
the same exact integer growth test. Its zero fallback, selection among tied coordinates, and
degree-cleanup threshold are also identical. `toFinset_recoverInput` identifies the complete
list of output identifiers with `recover` on the decoded graph. This agreement holds for every
dense input, including empty graphs and malformed adjacency words.

`computableInPolyTime_recoverInput` gives one native multitape polynomial-time certificate for
all dense inputs. It charges building the signed matrix, enumerating and testing candidate
columns, sorting their coordinates, and degree cleanup. The power-column kernel bounds all
intermediate signed-binary encodings. The certificate has no planted-clique or spectral premise;
the probabilistic correctness theorem is connected separately in `PolyTime`.
-/

public section

namespace Cslib.Algorithms.PlantedClique

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

private def growthTest (x : RecoveryInput) (c : ColumnCode) : Bool :=
  let v := IntTable.powerColumn x.signedRows c.steps c.seed
  let w := IntTable.powerColumn x.signedRows (c.steps + 1) c.seed
  decide (0 < squaredNorm w ∧ (x.cliqueSize : ℤ) ^ 2 * squaredNorm v ≤ 4 * squaredNorm w)

/-- The complete stored vector returned by the uniform finite growth search. -/
def recoveredIntegerVector (x : RecoveryInput) : List ℤ :=
  ((columnCodes x.vertexCount).find? (growthTest x)).elim
    (List.replicate x.vertexCount 0)
    (fun c => IntTable.powerColumn x.signedRows (c.steps + 1) c.seed)

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

private theorem storedColumn_eq (x : RecoveryInput) (s : ℕ) (i : Fin x.vertexCount) :
    IntTable.powerColumn x.signedRows s i.val =
      List.ofFn (powerVector (signedAdjacency x.graph) s i) := by
  rw [x.signedRows_eq_ofFn]
  calc
    _ = List.ofFn fun j => (signedAdjacency x.graph ^ s) j i :=
      IntTable.powerColumn_ofFn (signedAdjacency x.graph) s i
    _ = _ := congrArg List.ofFn (funext fun j =>
      (powerVector_apply (signedAdjacency x.graph) s i j).symm)

private theorem growthTest_code (x : RecoveryInput) (c : PowerColumn x.vertexCount) :
    growthTest x c.code = grows (signedAdjacency x.graph) x.cliqueSize c := by
  simp only [growthTest, PowerColumn.code, storedColumn_eq, squaredNorm_ofFn, grows]

private theorem find_columnCodes_eq (x : RecoveryInput) :
    (columnCodes x.vertexCount).find? (growthTest x) =
      (growingColumn? (signedAdjacency x.graph) x.cliqueSize).map PowerColumn.code := by
  simp only [columnCodes_eq, List.find?_map, Function.comp_def, growthTest_code,
    growingColumn?]

/-- The uniform list program returns exactly the vector used in the recovery proof. -/
theorem recoveredIntegerVector_eq (x : RecoveryInput) :
    recoveredIntegerVector x =
      List.ofFn (recoveredVector (signedAdjacency x.graph) x.cliqueSize) := by
  rw [recoveredIntegerVector, find_columnCodes_eq]
  cases h : growingColumn? (signedAdjacency x.graph) x.cliqueSize with
  | none => simp [recoveredVector, h, Pi.zero_def]
  | some c => simpa [recoveredVector, h, PowerColumn.code] using
      storedColumn_eq x (c.steps + 1) c.seed

private theorem computableInPolyTime_columnCodes :
    ComputableInPolyTime columnCodes encUnary (encList encColumnCode) := by
  unfold columnCodes
  fun_prop

private theorem computableInPolyTime_squaredNorm :
    ComputableInPolyTime squaredNorm (encList encIntBin) encIntBin := by
  unfold squaredNorm
  fun_prop

private theorem computableInPolyTime_growthTest :
    ComputableInPolyTime (fun p : RecoveryInput × ColumnCode => growthTest p.1 p.2)
      (encPair encRecoveryInput encColumnCode) encBool := by
  have hk : ComputableInPolyTime (fun p : RecoveryInput × ColumnCode => (p.1.cliqueSize : ℤ))
      (encPair encRecoveryInput encColumnCode) encIntBin :=
    ComputableInPolyTime.intBin_natCast.comp
      (ComputableInPolyTime.unary_to_binary.comp (by fun_prop))
  have hrows := RecoveryInput.computableInPolyTime_signedRows.comp
    (ComputableInPolyTime.fst encRecoveryInput encColumnCode)
  have hnv := computableInPolyTime_squaredNorm.comp (show ComputableInPolyTime
    (fun p : RecoveryInput × ColumnCode => IntTable.powerColumn p.1.signedRows p.2.steps p.2.seed)
    (encPair encRecoveryInput encColumnCode) (encList encIntBin) by fun_prop)
  have hnw := computableInPolyTime_squaredNorm.comp (show ComputableInPolyTime
    (fun p : RecoveryInput × ColumnCode =>
      IntTable.powerColumn p.1.signedRows (p.2.steps + 1) p.2.seed)
    (encPair encRecoveryInput encColumnCode) (encList encIntBin) by fun_prop)
  unfold growthTest
  dsimp only
  simp only [Bool.decide_and]
  fun_prop

/-- One native polynomial-time machine computes the complete search vector for every dense
input. In particular, its dimension is not fixed before the machine is chosen. -/
@[fun_prop] theorem computableInPolyTime_recoveredIntegerVector :
    ComputableInPolyTime recoveredIntegerVector encRecoveryInput (encList encIntBin) := by
  unfold recoveredIntegerVector
  apply ComputableInPolyTime.optionElimWithInput
  · exact ComputableInPolyTime.findWithInput
      (computableInPolyTime_columnCodes.comp (by fun_prop)) computableInPolyTime_growthTest
  · fun_prop
  · have hrows := RecoveryInput.computableInPolyTime_signedRows.comp
      (ComputableInPolyTime.fst encRecoveryInput encColumnCode)
    fun_prop

/-- Recover a list of vertex identifiers from a dense input by exact integer powers, stable
coordinate selection, and degree cleanup. -/
@[expose] def recoverInput (x : RecoveryInput) : List ℕ :=
  x.cleanup (largestIndices x.cliqueSize (recoveredIntegerVector x))

/-- The complete list program computes precisely the mathematical recovery set, including on
inputs outside the probabilistic recovery regime. -/
theorem toFinset_recoverInput (x : RecoveryInput) :
    (recoverInput x).toFinset = (recover x.graph x.cliqueSize).image Fin.val := by
  unfold recoverInput recover
  apply x.toFinset_cleanup _ _ _ (nodup_largestIndices _ _)
  rw [recoveredIntegerVector_eq]
  exact toFinset_largestIndices_ofFn x.cliqueSize
    (recoveredVector (signedAdjacency x.graph) x.cliqueSize)

/-- A single native multitape machine computes the complete recovery output in polynomial time
on every dense input. Both dimensions are supplied at runtime, and the output identifiers are
framed unary naturals. -/
@[fun_prop] theorem computableInPolyTime_recoverInput :
    ComputableInPolyTime recoverInput encRecoveryInput (encList encUnary) := by
  unfold recoverInput
  exact RecoveryInput.computableInPolyTime_cleanup ComputableInPolyTime.id'
    (computableInPolyTime_largestIndices (by fun_prop)
      computableInPolyTime_recoveredIntegerVector)

end Cslib.Algorithms.PlantedClique
