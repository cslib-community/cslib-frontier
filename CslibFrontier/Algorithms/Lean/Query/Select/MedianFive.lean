/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Algorithms.Lean.Query.Sort.LEQuery
import CslibFrontier.Algorithms.Lean.Query.FreeM.LiftM
import CslibFrontier.Algorithms.Lean.Query.Sort.LEQuery.KeyOracle
import CslibFrontier.Foundations.Data.List.MergeSort
import all Mathlib.Data.List.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation

/-!
# The median of five in six comparisons

Pair four inputs and compare the two pair maxima. The larger maximum has three inputs below it
in the order refined by input position; discard it. Pair its former partner with the fifth input.
The second largest among the two remaining pairs is the larger of the losing maximum and the
winning maximum's partner.

This construction attains the six-comparison upper bound discussed in
[Růžička and Wiedermann][RuzickaWiedermann1979], §2, p. 322. Their Figure 3 on p. 324 gives
a six-comparison decision tree for distinct items. On a total preorder we break ties by input
position and obtain the exact entry of a stable sort. The query count holds for every oracle.
-/

public section

namespace Cslib.Query

variable {α : Type}

private abbrev Pos := Fin 5

/-- Compare the earlier position to the later one, reversing the answer if necessary. -/
private def before (i j : Pos) : FreeM (LEQuery Pos) Bool :=
  if i ≤ j then LEQuery.ask i j else Bool.not <$> LEQuery.ask j i

private def sortPair (i j : Pos) : FreeM (LEQuery Pos) (Pos × Pos) := do
  return if ← before i j then (i, j) else (j, i)

private def medianIndex : FreeM (LEQuery Pos) Pos := do
  let ab ← sortPair 0 1
  let cd ← sortPair 2 3
  let (keep, free) := if ← before ab.2 cd.2 then (ab, cd.1) else (cd, ab.1)
  let other ← sortPair free 4
  let (u, v) := if ← before keep.2 other.2 then (keep.2, other.1) else (other.2, keep.1)
  return if ← before u v then v else u

private def queryAt (x : Pos → α) : {ι : Type} → LEQuery Pos ι → FreeM (LEQuery α) ι
  | _, .le i j => LEQuery.ask (x i) (x j)

/-- Select the middle of five indexed inputs. Equivalent elements are ordered by their input
positions, using one directed comparison per decision. -/
def medianFive (x : Fin 5 → α) : FreeM (LEQuery α) α := x <$> medianIndex.liftM (queryAt x)

/-- The output is one of the five supplied values, irrespective of the oracle. -/
theorem eval_medianFive_mem_range (oracle : {ι : Type} → LEQuery α ι → ι) (x : Fin 5 → α) :
    (medianFive x).eval oracle ∈ Set.range x := by
  simp only [medianFive, FreeM.eval_map]
  exact ⟨_, rfl⟩

private theorem count_before (oracle : {ι : Type} → LEQuery Pos ι → ι) (i j : Pos) :
    (before i j).countQueries oracle = 1 := by
  by_cases h : i ≤ j <;> simp [before, h, LEQuery.ask]

/-- Every run uses exactly six comparison queries, including runs with inconsistent answers. -/
theorem medianFive_countQueries (oracle : {ι : Type} → LEQuery α ι → ι) (x : Fin 5 → α) :
    (medianFive x).countQueries oracle = 6 := by
  have cost (o : {ι : Type} → LEQuery Pos ι → ι) : medianIndex.countQueries o = 6 := by
    simp [medianIndex, sortPair, FreeM.countQueries_bind, count_before]
  rw [medianFive, FreeM.countQueries_map]
  change (medianIndex.liftM (queryAt x)).cost oracle (fun _ => 1) = 6
  rw [FreeM.cost_liftM]
  have unit {ι} (q : LEQuery Pos ι) : (queryAt x q).cost oracle (fun _ => 1) = 1 := by
    cases q; rfl
  simp only [unit, ← FreeM.countQueries_eq_cost_one]
  exact cost _

private def positions : List Pos := [0, 1, 2, 3, 4]

private theorem checkRanks :
    ∀ a b c d e : Fin 5,
      let f : Pos → Fin 5 := ![a, b, c, d, e]
      medianIndex.eval (LEQuery.keyOracle f) =
        (positions.insertionSort fun i j => f i ≤ f j).getD 2 0 := by
  decide +kernel

/-- On a total preorder, the algorithm returns the very same input occurrence as a stable sort,
even if distinct inputs are equivalent under the comparator. -/
theorem eval_medianFive (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (oracle : {ι : Type} → LEQuery α ι → ι) (horacle : ∀ a b, oracle (.le a b) = decide (r a b))
    (x : Fin 5 → α) :
    (medianFive x).eval oracle =
      ([x 0, x 1, x 2, x 3, x 4].mergeSort fun a b => oracle (.le a b)).getD 2 (x 0) := by
  -- Strict-predecessor counts represent this finite total preorder without breaking its ties.
  have refl (i) : r (x i) (x i) := (Std.Total.total _ _).elim id id
  let lower (i : Pos) := Finset.univ.filter fun j : Pos => ¬ r (x i) (x j)
  let score (i : Pos) : Fin 5 := ⟨(lower i).card, by
    have h : lower i ⊂ Finset.univ :=
      Finset.filter_ssubset.mpr ⟨i, Finset.mem_univ _, not_not.mpr (refl i)⟩
    simpa [Pos] using Finset.card_lt_card h⟩
  have sub {i j} (h : r (x i) (x j)) : lower i ⊆ lower j := by
    intro k hk
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, fun hjk => (Finset.mem_filter.mp hk).2 (_root_.trans h hjk)⟩
  have rank (i j) : r (x i) (x j) ↔ score i ≤ score j := by
    refine ⟨fun h => Finset.card_le_card (sub h), fun h => ?_⟩
    by_contra hij
    have hsub := sub ((Std.Total.total (x i) (x j)).resolve_left hij)
    have hlt : (lower j).card < (lower i).card := by
      apply Finset.card_lt_card
      apply (Finset.ssubset_iff_of_subset hsub).mpr
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩,
        fun hj => (Finset.mem_filter.mp hj).2 (refl j)⟩
    exact (Nat.not_le_of_gt hlt) h
  have answers (i j : Pos) : oracle (.le (x i) (x j)) = decide (score i ≤ score j) := by
    simp only [horacle, rank]
  have handle : (fun {ι} (q : LEQuery Pos ι) => (queryAt x q).eval oracle) =
      (fun {ι} (q : LEQuery Pos ι) => LEQuery.keyOracle score q) := by
    funext ι q; cases q with | le i j => exact answers i j
  have tuple : ![score 0, score 1, score 2, score 3, score 4] = score := by
    funext i; fin_cases i <;> rfl
  have verified := checkRanks (score 0) (score 1) (score 2) (score 3) (score 4)
  dsimp only at verified
  rw [tuple] at verified
  let cmp (i j : Pos) := decide (score i ≤ score j)
  have sorted := List.map_mergeSort (l := positions) (f := x) (r := cmp)
    (s := fun a b => oracle (.le a b)) (fun i _ j _ => (answers i j).symm)
  rw [medianFive, FreeM.eval_map, FreeM.eval_liftM, handle, verified]
  change x ((positions.insertionSort fun i j => score i ≤ score j).getD 2 0) =
    ((positions.map x).mergeSort fun a b => oracle (.le a b)).getD 2 (x 0)
  rw [← sorted, List.getD_map, List.mergeSort_decide_eq_insertionSort
    (fun i j => score i ≤ score j) (fun _ _ _ => le_trans)
    (fun i j => le_total (score i) (score j))]

end Cslib.Query
