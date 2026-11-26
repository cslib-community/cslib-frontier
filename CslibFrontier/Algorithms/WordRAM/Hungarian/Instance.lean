/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxFlow.Hungarian
public import CslibFrontier.Computability.WordRAM.ListOutput
public import CslibFrontier.Computability.WordRAM.Signed.Encoding
import CslibFrontier.Computability.WordRAM.InputArray
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# Problem instances and encodings for the Word-RAM Hungarian method

Defines `Instance` together with its row-major signed-word encoding (`Instance.encode`),
word-width envelope (`Instance.wordBound`), optimal assignment (`Instance.assignment`), and
minimum matching cost (`Instance.encodedMinCost`).
-/

public section

namespace Cslib.Algorithms.WordRAM.Hungarian

open Cslib.WordRAM
open Cslib.Algorithms.Lean.MaxFlow

/-- An instance of the `n × n` balanced bipartite minimum-cost assignment problem with integer edge
costs. -/
structure Instance where
  /-- Common side size `n` of the balanced bipartite graph `Fin n × Fin n`. -/
  n : ℕ
  /-- Signed integer cost of pairing row `u` with column `v`. -/
  cost : Fin n × Fin n → ℤ

namespace Instance

/-- Maximum absolute cost `max_{u, v} |cost (u, v)|` (`0` when `n = 0`). -/
@[expose] def maxMag (inst : Instance) : ℕ :=
  Finset.univ.sup fun p : Fin inst.n × Fin inst.n => (inst.cost p).natAbs

theorem natAbs_cost_le_maxMag (inst : Instance) (u v : Fin inst.n) :
    (inst.cost (u, v)).natAbs ≤ inst.maxMag :=
  Finset.le_sup (f := fun p : Fin inst.n × Fin inst.n => (inst.cost p).natAbs)
    (Finset.mem_univ (u, v))

/-- Encode an `n × n` assignment instance as `n` followed by the `n²` row-major `Signed.encode`
cost words. -/
@[expose] def encode (inst : Instance) : List ℕ :=
  inst.n :: (List.finRange inst.n).flatMap fun u =>
    (List.finRange inst.n).map fun v => Signed.encode (inst.cost (u, v))

/-- Sufficient word-value envelope covering all input words, array addresses, shifted potentials,
slacks, and accumulated matching costs. -/
@[expose] def wordBound (inst : Instance) : ℕ :=
  2 * inst.n * inst.n + 8 * inst.n + 4 * (inst.n + 1) * inst.maxMag + 4

/-- Column matched to row `u` in `(hungarian inst.cost).matching`. -/
@[expose] def assignedCol (inst : Instance) (u : Fin inst.n) : Fin inst.n :=
  match (List.finRange inst.n).find?
      (fun v => decide ((u, v) ∈ (hungarian inst.cost).matching)) with
  | some v => v
  | none => u

/-- Row-indexed list `[col_0, …, col_{n - 1}]` of column indices assigned to rows `0, …, n - 1`. -/
@[expose] def assignment (inst : Instance) : List ℕ :=
  (List.finRange inst.n).map fun u => (inst.assignedCol u).val

/-- Minimum perfect-matching cost of `inst`, encoded as an unsigned word via `Signed.encode`. -/
@[expose] def encodedMinCost (inst : Instance) : ℕ :=
  Signed.encode (matchingCost inst.cost (hungarian inst.cost).matching)

@[simp] theorem length_assignment (inst : Instance) : inst.assignment.length = inst.n := by
  simp [assignment]

theorem getElem_assignment (inst : Instance) (u : Fin inst.n) :
    inst.assignment[u.val]'(by simp [assignment]) = (inst.assignedCol u).val := by
  simp [assignment]

theorem mem_matching_assignedCol (inst : Instance) (u : Fin inst.n) :
    (u, inst.assignedCol u) ∈ (hungarian inst.cost).matching := by
  obtain ⟨⟨_, hleft, _⟩, _⟩ := (hungarian_correct inst.cost).1
  obtain ⟨v₀, hv₀⟩ := mem_matchedLeft.mp (hleft.symm ▸ Finset.mem_univ u)
  let p : Fin inst.n → Bool := fun v => decide ((u, v) ∈ (hungarian inst.cost).matching)
  change (u, match (List.finRange inst.n).find? p with | some v => v | none => u) ∈ _
  cases hfind : (List.finRange inst.n).find? p with
  | some v => exact of_decide_eq_true (List.find?_some hfind : p v = true)
  | none =>
    exact absurd (decide_eq_true hv₀) (List.find?_eq_none.mp hfind v₀ (List.mem_finRange v₀))

theorem assignedCol_eq_of_mem (inst : Instance) {u v : Fin inst.n}
    (h : (u, v) ∈ (hungarian inst.cost).matching) : inst.assignedCol u = v := by
  obtain ⟨⟨⟨_, hleft_inj, _⟩, _⟩, _⟩ := (hungarian_correct inst.cost).1
  exact hleft_inj u (inst.assignedCol u) v (inst.mem_matching_assignedCol u) h

/-- The Finset of pairs `(u, inst.assignedCol u)` equals `(hungarian inst.cost).matching`. -/
theorem image_assignedCol_eq_matching (inst : Instance) :
    (Finset.univ.image fun u : Fin inst.n => (u, inst.assignedCol u)) =
      (hungarian inst.cost).matching := by
  ext ⟨u, v⟩
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq]
  exact ⟨fun ⟨u', hu, hv⟩ => hu ▸ hv ▸ inst.mem_matching_assignedCol u',
    fun h => ⟨u, rfl, inst.assignedCol_eq_of_mem h⟩⟩

/-- The induced matching of `inst.assignment` is a minimum-cost perfect matching of `inst.cost`. -/
theorem isMinCostPerfectMatching_assignment (inst : Instance) :
    IsMinCostPerfectMatching (fun _ => true) inst.cost
      (Finset.univ.image fun u : Fin inst.n => (u, inst.assignedCol u)) :=
  inst.image_assignedCol_eq_matching ▸ (hungarian_correct inst.cost).1

/-- Summing `inst.cost (u, inst.assignedCol u)` over all rows equals the minimum matching cost. -/
theorem sum_cost_assignedCol (inst : Instance) :
    (∑ u : Fin inst.n, inst.cost (u, inst.assignedCol u)) =
      matchingCost inst.cost (hungarian inst.cost).matching := by
  rw [matchingCost, ← inst.image_assignedCol_eq_matching,
    Finset.sum_image fun _ _ _ _ h => (Prod.mk.inj h).1]

theorem encode_length (inst : Instance) : inst.encode.length = 1 + inst.n * inst.n := by
  simp [encode, List.length_flatMap, Nat.add_comm]

theorem init_mem_n {r : ℕ} (inst : Instance) :
    (Data.init inst.encode : Data r).mem 1 = inst.n := rfl

theorem init_mem_cost {r : ℕ} (inst : Instance) (u v : Fin inst.n) :
    (Data.init inst.encode : Data r).mem (2 + (u.val * inst.n + v.val)) =
      Signed.encode (inst.cost (u, v)) :=
  Data.init_mem_flatMap_finRange [inst.n] (fun u' v' => Signed.encode (inst.cost (u', v'))) u v

/-- Every instance's encoding fits at any word width admitting `inst.wordBound`. -/
theorem inputFits_encode (inst : Instance) {w : ℕ} (hw : Fits w inst.wordBound) :
    InputFits w inst.encode :=
  InputFits.flatMap_finRange [inst.n] (fun u v => Signed.encode (inst.cost (u, v)))
    (hw.of_le (by unfold wordBound; dsimp only [List.length]; nlinarith))
    (by
      simp only [List.mem_singleton]
      rintro _ rfl
      exact hw.of_le (by unfold wordBound; nlinarith))
    (fun u v => hw.of_le ((Signed.encode_le_two_mul_add_one
      (inst.natAbs_cost_le_maxMag u v)).trans (by unfold wordBound; nlinarith)))

end Instance

end Cslib.Algorithms.WordRAM.Hungarian
