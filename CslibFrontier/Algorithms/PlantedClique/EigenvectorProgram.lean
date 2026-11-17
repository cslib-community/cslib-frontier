/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.PlantedClique.Selection
public import CslibFrontier.Computability.PolyTime.Int.MatrixPower
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List.Sort
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort

/-!
# A native integer filter for the second adjacency eigenvector

The filter `16 (n + k + 1)² I - (2 A - k I)²` is an integer polynomial in the ordinary
adjacency matrix. `eigenvectorPowerColumn` computes its power on every standard basis vector,
stores the columns, and returns one of maximum squared norm. It uses only exact arithmetic
on signed binary integers. The unary iteration count is an explicit input.

The table and column agreement theorems identify this implementation with the finite matrix
power. The native polynomial-time certificate holds on every dense input, independently of
any planted-clique or spectral hypothesis. Approximation to the second eigenvector is proved
separately from these computational and representation facts.
-/

public section

namespace Cslib.Algorithms.PlantedClique

open Turing.MultiTapeTM Matrix
open Mathlib.Tactic.Matrix

/-- Integer spectral filter centered at the public target eigenvalue `k / 2` of the raw
adjacency matrix. The scalar shift keeps the intended spectral interval nonnegative. -/
@[expose] def secondEigenvectorFilter {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (k : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  ((16 * (n + k + 1) ^ 2 : ℕ) : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) -
    ((2 : ℤ) • G.adjMatrix ℤ - (k : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) ^ 2

namespace RecoveryInput

private def eigenvectorShiftEntry (x : RecoveryInput) (i j : ℕ) : ℤ :=
  (if x.adjacent i j then 2 else 0) - if i = j then (x.cliqueSize : ℤ) else 0

/-- The spectral filter stored as a square row table of signed binary integers. -/
def eigenvectorFilterRows (x : RecoveryInput) : List (List ℤ) :=
  tabulateTable x.vertexCount x.vertexCount fun i j =>
    (if i = j then ((16 * (x.vertexCount + x.cliqueSize + 1) ^ 2 : ℕ) : ℤ) else 0) -
      ((List.range x.vertexCount).map fun l =>
        x.eigenvectorShiftEntry i l * x.eigenvectorShiftEntry l j).sum

/-- The filter row table always has the declared square dimensions. -/
theorem isTableShape_eigenvectorFilterRows (x : RecoveryInput) :
    IsTableShape x.vertexCount x.vertexCount x.eigenvectorFilterRows :=
  isTableShape_tabulateTable _ _ _

private theorem eigenvectorShiftEntry_eq (x : RecoveryInput) (i j : Fin x.vertexCount) :
    x.eigenvectorShiftEntry i j =
      ((2 : ℤ) • x.graph.adjMatrix ℤ - (x.cliqueSize : ℤ) •
        (1 : Matrix (Fin x.vertexCount) (Fin x.vertexCount) ℤ)) i j := by
  have hadj : x.graph.adjMatrix ℤ i j = if x.adjacent i j then 1 else 0 := rfl
  simp only [eigenvectorShiftEntry, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, hadj, Fin.ext_iff]
  split_ifs <;> ring

/-- The row table agrees with the raw-adjacency filter, including malformed dense inputs. -/
theorem eigenvectorFilterRows_eq_ofFn (x : RecoveryInput) :
    x.eigenvectorFilterRows =
      List.ofFn (fun i => List.ofFn (fun j =>
        secondEigenvectorFilter x.graph x.cliqueSize i j)) := by
  simp only [eigenvectorFilterRows, tabulateTable, List.map_range_eq_ofFn]
  congr 1
  funext i
  congr 1
  funext j
  simp only [List.sum_ofFn, eigenvectorShiftEntry_eq, secondEigenvectorFilter,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, pow_two,
    Matrix.mul_apply]
  by_cases hij : i = j
  · simp [hij]
  · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp [hij, hval]

private theorem computableInPolyTime_eigenvectorShiftEntry {α : Type}
    {encIn : α ↪ List Bool} {input : α → RecoveryInput} {i j : α → ℕ}
    (hx : ComputableInPolyTime input encIn encRecoveryInput)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun a => (input a).eigenvectorShiftEntry (i a) (j a))
      encIn encIntBin := by
  have hk : ComputableInPolyTime (fun a => ((input a).cliqueSize : ℤ)) encIn encIntBin :=
    ComputableInPolyTime.intBin_natCast.comp
      (ComputableInPolyTime.unary_to_binary.comp (by fun_prop))
  unfold eigenvectorShiftEntry
  fun_prop

/-- Construct the integer spectral filter in native polynomial time with binary arithmetic. -/
@[fun_prop] theorem computableInPolyTime_eigenvectorFilterRows :
    ComputableInPolyTime eigenvectorFilterRows encRecoveryInput encIntTable := by
  unfold eigenvectorFilterRows
  apply computableInPolyTime_tabulateTable (by fun_prop) (by fun_prop)
  have hc : ComputableInPolyTime
      (fun p : TableIndex RecoveryInput =>
        ((16 * (p.ctx.vertexCount + p.ctx.cliqueSize + 1) ^ 2 : ℕ) : ℤ))
      (encPair (encPair encRecoveryInput encUnary) encUnary) encIntBin :=
    ComputableInPolyTime.intBin_natCast.comp
      (ComputableInPolyTime.unary_to_binary.comp (by fun_prop))
  have hm : ComputableInPolyTime
      (fun p : TableIndex RecoveryInput =>
        ((List.range p.ctx.vertexCount).map fun l =>
          p.ctx.eigenvectorShiftEntry p.row l * p.ctx.eigenvectorShiftEntry l p.col).sum)
      (encPair (encPair encRecoveryInput encUnary) encUnary) encIntBin := by
    apply ComputableInPolyTime.intBin_sum.comp
    apply ComputableInPolyTime.mapWithInput (by fun_prop)
    have hleft := computableInPolyTime_eigenvectorShiftEntry
      (encIn := encPair (encPair (encPair encRecoveryInput encUnary) encUnary) encUnary)
      (input := fun p => TableIndex.ctx p.1) (i := fun p => TableIndex.row p.1)
      (j := fun p => p.2)
      (by fun_prop) (by fun_prop) (by fun_prop)
    have hright := computableInPolyTime_eigenvectorShiftEntry
      (encIn := encPair (encPair (encPair encRecoveryInput encUnary) encUnary) encUnary)
      (input := fun p => TableIndex.ctx p.1) (i := fun p => p.2)
      (j := fun p => TableIndex.col p.1)
      (by fun_prop) (by fun_prop) (by fun_prop)
    exact ComputableInPolyTime.intBin_mul.comp (hleft.prod hright)
  fun_prop

end RecoveryInput

/-- Compute every power column of the integer raw-adjacency filter and select a column of
maximum squared norm. The empty-dimensional fallback is the empty vector. -/
@[expose] def eigenvectorPowerColumn (x : RecoveryInput) (steps : ℕ) : List ℤ :=
  (((List.range x.vertexCount).map fun i =>
    IntTable.powerColumn x.eigenvectorFilterRows steps i).mergeSort fun v w =>
      decide (ListMatrix.dotProduct w.length w w ≤ ListMatrix.dotProduct v.length v v)).headD
        (List.replicate x.vertexCount 0)

private theorem sorted_headD_max {α : Type} (score : α → ℤ) (l : List α) (d : α)
    (hl : l ≠ []) :
    let best := (l.mergeSort fun a b => decide (score b ≤ score a)).headD d
    best ∈ l ∧ ∀ a ∈ l, score a ≤ score best := by
  let r := fun a b => decide (score b ≤ score a)
  have hp := List.pairwise_mergeSort (le := r)
    (fun a b c hab hbc => decide_eq_true (le_trans (of_decide_eq_true hbc)
      (of_decide_eq_true hab)))
    (fun a b => by simp only [r, Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _) l
  have hperm := List.mergeSort_perm l r
  change (l.mergeSort r).headD d ∈ l ∧ ∀ a ∈ l, score a ≤ score ((l.mergeSort r).headD d)
  cases hs : l.mergeSort r with
  | nil =>
    have hlen : l.length = 0 := by simpa only [hs, List.length_nil] using hperm.length_eq.symm
    exact (hl (List.eq_nil_of_length_eq_zero hlen)).elim
  | cons a as =>
    simp only [List.headD_cons]
    have ha : a ∈ l := hperm.mem_iff.mp (by simp [hs])
    refine ⟨ha, ?_⟩
    intro b hb
    have hb' : b ∈ a :: as := by simpa only [hs] using hperm.mem_iff.mpr hb
    rcases List.mem_cons.mp hb' with rfl | hb'
    · exact le_rfl
    · have hrel := List.rel_of_pairwise_cons (hs ▸ hp) hb'
      exact of_decide_eq_true hrel

/-- The selected stored vector is one filter-power column and its squared norm dominates
every other column. The selection itself uses only exact binary-integer comparisons. -/
theorem eigenvectorPowerColumn_spec (x : RecoveryInput) (steps : ℕ)
    (hn : 0 < x.vertexCount) :
    ∃ i : Fin x.vertexCount,
      eigenvectorPowerColumn x steps =
        List.ofFn (fun j => (secondEigenvectorFilter x.graph x.cliqueSize ^ steps) j i) ∧
      ∀ l : Fin x.vertexCount,
        (∑ j, (secondEigenvectorFilter x.graph x.cliqueSize ^ steps) j l ^ 2) ≤
          ∑ j, (secondEigenvectorFilter x.graph x.cliqueSize ^ steps) j i ^ 2 := by
  let columns := (List.range x.vertexCount).map fun i =>
    IntTable.powerColumn x.eigenvectorFilterRows steps i
  have hcolumns : columns ≠ [] := by
    simp only [columns, ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
    omega
  have hspec := sorted_headD_max (fun v : List ℤ => ListMatrix.dotProduct v.length v v)
    columns (List.replicate x.vertexCount 0) hcolumns
  obtain ⟨i, hi, hcol⟩ := List.mem_map.mp hspec.1
  let v : Fin x.vertexCount := ⟨i, List.mem_range.mp hi⟩
  have hstored (j : Fin x.vertexCount) :
      IntTable.powerColumn x.eigenvectorFilterRows steps j =
        List.ofFn (fun l => (secondEigenvectorFilter x.graph x.cliqueSize ^ steps) l j) := by
    rw [x.eigenvectorFilterRows_eq_ofFn]
    exact IntTable.powerColumn_ofFn _ _ _
  have houtput : eigenvectorPowerColumn x steps =
      List.ofFn (fun j => (secondEigenvectorFilter x.graph x.cliqueSize ^ steps) j v) := by
    exact hcol.symm.trans (hstored v)
  refine ⟨v, houtput, ?_⟩
  intro l
  have hle := hspec.2 (IntTable.powerColumn x.eigenvectorFilterRows steps l)
    (List.mem_map.mpr ⟨l.val, List.mem_range.mpr l.isLt, rfl⟩)
  change ListMatrix.dotProduct _ _ _ ≤ ListMatrix.dotProduct
    (eigenvectorPowerColumn x steps).length (eigenvectorPowerColumn x steps)
      (eigenvectorPowerColumn x steps) at hle
  rw [hstored l, houtput] at hle
  simpa only [List.length_ofFn, ListMatrix.dotProduct_ofFn, pow_two] using hle

/-- The selected column has exactly the declared number of coordinates on every input. -/
@[simp] theorem length_eigenvectorPowerColumn (x : RecoveryInput) (steps : ℕ) :
    (eigenvectorPowerColumn x steps).length = x.vertexCount := by
  by_cases hn : 0 < x.vertexCount
  · obtain ⟨i, hi, -⟩ := eigenvectorPowerColumn_spec x steps hn
    simp only [hi, List.length_ofFn]
  · have hz : x.vertexCount = 0 := by omega
    simp [eigenvectorPowerColumn, hz]

/-- Uniform native polynomial-time computation of the stored maximizing column. The step
count is unary and all filter entries, coordinates and comparison scores are signed binary. -/
@[fun_prop] theorem computableInPolyTime_eigenvectorPowerColumn {α : Type}
    {encIn : α ↪ List Bool} {input : α → RecoveryInput} {steps : α → ℕ}
    (hx : ComputableInPolyTime input encIn encRecoveryInput)
    (hs : ComputableInPolyTime steps encIn encUnary) :
    ComputableInPolyTime (fun a => eigenvectorPowerColumn (input a) (steps a))
      encIn (encList encIntBin) := by
  have hrows := RecoveryInput.computableInPolyTime_eigenvectorFilterRows.comp hx
  have hcolumns : ComputableInPolyTime
      (fun a => (List.range (input a).vertexCount).map fun i =>
        IntTable.powerColumn (input a).eigenvectorFilterRows (steps a) i)
      encIn encIntTable := by
    apply ComputableInPolyTime.mapWithInput (by fun_prop)
    have hr := hrows.comp (ComputableInPolyTime.fst encIn encUnary)
    have ht := hs.comp (ComputableInPolyTime.fst encIn encUnary)
    fun_prop
  have hrel : ComputableInPolyTime
      (fun p : (α × List ℤ) × List ℤ =>
        decide (ListMatrix.dotProduct p.2.length p.2 p.2 ≤
          ListMatrix.dotProduct p.1.2.length p.1.2 p.1.2))
      (encPair (encPair encIn (encList encIntBin)) (encList encIntBin)) encBool := by
    have hleft := ComputableInPolyTime.listDotProduct.comp
      (show ComputableInPolyTime
        (fun p : (α × List ℤ) × List ℤ => (p.2.length, p.2, p.2))
        (encPair (encPair encIn (encList encIntBin)) (encList encIntBin))
        (encPair encUnary (encPair (encList encIntBin) (encList encIntBin))) by fun_prop)
    have hright := ComputableInPolyTime.listDotProduct.comp
      (show ComputableInPolyTime
        (fun p : (α × List ℤ) × List ℤ => (p.1.2.length, p.1.2, p.1.2))
        (encPair (encPair encIn (encList encIntBin)) (encList encIntBin))
        (encPair encUnary (encPair (encList encIntBin) (encList encIntBin))) by fun_prop)
    fun_prop
  unfold eigenvectorPowerColumn
  apply ComputableInPolyTime.listHeadDWithInput
  · exact ComputableInPolyTime.mergeSortWithInput
      (r := fun _ v w => ListMatrix.dotProduct w.length w w ≤ ListMatrix.dotProduct v.length v v)
      hcolumns hrel (fun _ _ _ _ h₁ h₂ => h₂.trans h₁) (fun _ _ _ => le_total _ _)
  · fun_prop

/-- Apply stable largest-coordinate selection and degree cleanup to the computed filter column. -/
@[expose] def recoverEigenvectorPowerInput (x : RecoveryInput) (steps : ℕ) : List ℕ :=
  x.cleanup (largestIndices x.cliqueSize (eigenvectorPowerColumn x steps))

/-- The complete filter-power recovery program has an unconditional uniform native
polynomial-time certificate for arbitrary dense inputs and unary iteration counts. -/
@[fun_prop] theorem computableInPolyTime_recoverEigenvectorPowerInput {α : Type}
    {encIn : α ↪ List Bool} {input : α → RecoveryInput} {steps : α → ℕ}
    (hx : ComputableInPolyTime input encIn encRecoveryInput)
    (hs : ComputableInPolyTime steps encIn encUnary) :
    ComputableInPolyTime (fun a => recoverEigenvectorPowerInput (input a) (steps a))
      encIn (encList encUnary) := by
  unfold recoverEigenvectorPowerInput
  exact RecoveryInput.computableInPolyTime_cleanup hx
    (computableInPolyTime_largestIndices (by fun_prop)
      (computableInPolyTime_eigenvectorPowerColumn hx hs))

end Cslib.Algorithms.PlantedClique
