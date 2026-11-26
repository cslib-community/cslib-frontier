/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.PlantedClique.Encoding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List.Sort
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Tactic.PolyTime
import Mathlib.Data.List.FinRange

/-!
# Uniform integer selection and degree cleanup

`largestIndices` sorts runtime indices by decreasing absolute integer coordinate and keeps the
requested number. It uses the same stable merge sort as `List.selectLargest`, with an exact
agreement theorem for finite vectors. `RecoveryInput.cleanup` counts neighbors in that list
and filters all declared vertices by the original degree threshold.

Both operations have unconditional native polynomial-time certificates on explicit encodings.
Indices, list lengths and the target size are in unary; score magnitudes are binary integers.
The semantic cleanup theorem assumes a duplicate-free selected list, which the selection
procedure always supplies. The running-time theorem needs no such promise.
-/

public section

namespace Cslib.Algorithms.PlantedClique

open Turing.MultiTapeTM

/-- Select the first `k` indices in stable descending order of absolute integer coordinate. -/
@[expose] def largestIndices (k : ℕ) (v : List ℤ) : List ℕ :=
  ((List.range v.length).mergeSort fun i j =>
    decide ((v.getD j 0).natAbs ≤ (v.getD i 0).natAbs)).take k

/-- Every selected index lies within the input vector. -/
theorem mem_largestIndices_lt (k : ℕ) (v : List ℤ) {i : ℕ}
    (hi : i ∈ largestIndices k v) : i < v.length := by
  have h := List.mem_of_mem_take hi
  simpa only [List.mem_mergeSort, List.mem_range] using h

/-- Selection introduces no duplicate indices. -/
theorem nodup_largestIndices (k : ℕ) (v : List ℤ) : (largestIndices k v).Nodup :=
  ((List.mergeSort_perm (List.range v.length) _).nodup_iff.mpr List.nodup_range).take

/-- On a finite vector, native index selection is exactly the original selection after forgetting
the bounded-index proofs, including the same choices among tied scores. -/
theorem toFinset_largestIndices_ofFn {n : ℕ} (k : ℕ) (v : Fin n → ℤ) :
    (largestIndices k (List.ofFn v)).toFinset =
      (List.selectLargest (fun i => (v i).natAbs) k (List.finRange n)).image Fin.val := by
  have hmap : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp
  have hsort := List.map_mergeSort (l := List.finRange n) (f := Fin.val)
    (r := fun i j => decide ((v j).natAbs ≤ (v i).natAbs))
    (s := fun i j => decide (((List.ofFn v).getD j 0).natAbs ≤
      ((List.ofFn v).getD i 0).natAbs)) (by
      intro i _ j _
      simp [List.getD_eq_getElem?_getD])
  rw [hmap] at hsort
  simp only [largestIndices, List.length_ofFn, List.selectLargest]
  rw [← hsort, ← List.map_take]
  ext i
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]

/-- Sorting binary integer scores and taking a unary number of indices is uniformly
polynomial-time. The comparator is charged for both coordinate lookups and both magnitudes. -/
@[fun_prop] theorem computableInPolyTime_largestIndices {α : Type} {encIn : α ↪ List Bool}
    {k : α → ℕ} {v : α → List ℤ}
    (hk : ComputableInPolyTime k encIn encUnary)
    (hv : ComputableInPolyTime v encIn (encList encIntBin)) :
    ComputableInPolyTime (fun x => largestIndices (k x) (v x)) encIn (encList encUnary) := by
  have hlist : ComputableInPolyTime (fun x => List.range (v x).length)
      encIn (encList encUnary) := by fun_prop
  have hrel : ComputableInPolyTime
      (fun p : (α × ℕ) × ℕ => decide (((v p.1.1).getD p.2 0).natAbs ≤
        ((v p.1.1).getD p.1.2 0).natAbs))
      (encPair (encPair encIn encUnary) encUnary) encBool := by fun_prop
  have hsort := ComputableInPolyTime.mergeSortWithInput
    (r := fun x i j => ((v x).getD j 0).natAbs ≤ ((v x).getD i 0).natAbs) hlist hrel
    (fun _ _ _ _ h₁ h₂ => h₂.trans h₁) (fun _ _ _ => le_total _ _)
  exact ComputableInPolyTime.listTakeWithInput hsort hk

namespace RecoveryInput

/-- Keep declared vertices having at least three quarters of the requested number of neighbors
in the selected list. Duplicate entries, if supplied, are counted with multiplicity. -/
@[expose] def cleanup (x : RecoveryInput) (selected : List ℕ) : List ℕ :=
  (List.range x.vertexCount).filter fun i =>
    decide (3 * x.cliqueSize ≤ 4 * selected.countP (x.adjacent i))

/-- Every cleaned vertex is within the declared graph. -/
theorem mem_cleanup_lt (x : RecoveryInput) (selected : List ℕ) {i : ℕ}
    (hi : i ∈ x.cleanup selected) : i < x.vertexCount :=
  List.mem_range.mp (List.mem_filter.mp hi).1

/-- Degree cleanup returns each accepted vertex once. -/
theorem nodup_cleanup (x : RecoveryInput) (selected : List ℕ) : (x.cleanup selected).Nodup :=
  List.nodup_range.filter _

/-- Native list cleanup agrees with the graph operation when the input list represents the
candidate set without duplicates. -/
theorem toFinset_cleanup (x : RecoveryInput) (selected : List ℕ)
    (T : Finset (Fin x.vertexCount)) (hselected : selected.toFinset = T.image Fin.val)
    (hnodup : selected.Nodup) :
    (x.cleanup selected).toFinset =
      (x.graph.recoverCliqueByDegree x.cliqueSize T).image Fin.val := by
  have hcount (i : Fin x.vertexCount) : selected.countP (x.adjacent i) =
      (T.filter (x.graph.Adj i)).card := by
    have hc := hnodup.card_eq_countP (P := fun j => x.adjacent i j = true)
    simp only [Bool.decide_eq_true] at hc
    rw [← hc, hselected, Finset.filter_image]
    exact Finset.card_image_of_injective _ Fin.val_injective
  ext i
  simp only [cleanup, List.mem_toFinset, List.mem_filter, List.mem_range, Finset.mem_image,
    SimpleGraph.recoverCliqueByDegree, Finset.mem_filter, Finset.mem_univ, true_and,
    decide_eq_true_eq]
  refine ⟨fun ⟨hi, hd⟩ => ⟨⟨i, hi⟩, hcount ⟨i, hi⟩ ▸ hd, rfl⟩, ?_⟩
  rintro ⟨v, hv, rfl⟩
  exact ⟨v.isLt, (hcount v).symm ▸ hv⟩

/-- Uniform native polynomial-time degree cleanup on arbitrary dense inputs and candidate lists. -/
@[fun_prop] theorem computableInPolyTime_cleanup {α : Type} {encIn : α ↪ List Bool}
    {input : α → RecoveryInput} {selected : α → List ℕ}
    (hx : ComputableInPolyTime input encIn encRecoveryInput)
    (hselected : ComputableInPolyTime selected encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => (input x).cleanup (selected x)) encIn (encList encUnary) := by
  unfold cleanup
  fun_prop

end RecoveryInput

end Cslib.Algorithms.PlantedClique
