/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Assignment.Auction
public import CslibFrontier.Computability.WordRAM.InputArray
public import CslibFrontier.Computability.WordRAM.Signed.Encoding
import CslibFrontier.Foundations.Data.List.Counting
import Mathlib.Tactic.Linarith

/-!
# Word-RAM auction problem instances and encodings

Public input/output definitions and word-width fit lemmas for Bertsekas's Gauss–Seidel auction
algorithms on the word RAM:

* `Cslib.Algorithms.WordRAM.Auction.Instance`: exact `(n + 1)`-scaled integer assignment problem
  instance (`encode`, `wordBound`, `maxMag`, `rowSpread`, `assignment`, `minCost`,
  `encodedMinCost`).
* `Cslib.Algorithms.WordRAM.Auction.EpsInstance`: unscaled `ε`-auction problem instance (`encode`,
  `wordBound`, `assignment`, plus `toInstance`, `maxMag`, `rowSpread`).

This module has no dependency on the `Memory.Prog` realization stack so clients can work with
`Instance` and `EpsInstance` without elaborating the Word-RAM refinement machinery.

## Main definitions

* `Cslib.Algorithms.WordRAM.Auction.Instance`: `(n + 1)`-scaled integer assignment instance.
* `Cslib.Algorithms.WordRAM.Auction.EpsInstance`: unscaled `ε`-auction instance.

## Main results

* `Cslib.Algorithms.WordRAM.Auction.Instance.natAbs_cost_le_maxMag`,
  `Cslib.Algorithms.WordRAM.Auction.Instance.sub_le_rowSpread`: cost-matrix bounds.
* `Cslib.Algorithms.WordRAM.Auction.Instance.encode_length`,
  `Cslib.Algorithms.WordRAM.Auction.Instance.inputFits_encode`: encoding length and word-fit.
* `Cslib.Algorithms.WordRAM.Auction.EpsInstance.encode_length`,
  `Cslib.Algorithms.WordRAM.Auction.EpsInstance.inputFits_encode`: `ε`-auction encoding length
  and word-fit.

## References

* [Bertsekas1979]
* [Bertsekas1988]
* [Bertsekas1998]
-/

public section

namespace Cslib.Algorithms.WordRAM.Auction

open Cslib.WordRAM
open Cslib.Algorithms.Lean.Assignment

/-- Problem instance for exact minimum-cost integer assignment via Bertsekas's `(n + 1)`-scaled
auction (`scaledAuction`, `ε = 1`). -/
structure Instance where
  /-- Common number of persons and objects. -/
  n : ℕ
  /-- Signed integer assignment cost `Fin n × Fin n → ℤ`. -/
  cost : Fin n × Fin n → ℤ

namespace Instance

/-- Maximum entry magnitude `max_{i, j} |cost (i, j)|` (`0` when `n = 0`). -/
@[expose] def maxMag (inst : Instance) : ℕ :=
  Finset.univ.sup fun p : Fin inst.n × Fin inst.n => (inst.cost p).natAbs

/-- Maximum within-row cost difference `max_{i, j, k} (cost (i, k) - cost (i, j))` (`0` when
`n = 0`). -/
@[expose] def rowSpread (inst : Instance) : ℕ :=
  Finset.univ.sup fun i : Fin inst.n =>
    Finset.univ.sup fun j : Fin inst.n =>
      Finset.univ.sup fun k : Fin inst.n =>
        (inst.cost (i, k) - inst.cost (i, j)).toNat

/-- Every entry magnitude is bounded by `inst.maxMag`. -/
theorem natAbs_cost_le_maxMag (inst : Instance) (i j : Fin inst.n) :
    (inst.cost (i, j)).natAbs ≤ inst.maxMag :=
  Finset.le_sup (f := fun p : Fin inst.n × Fin inst.n => (inst.cost p).natAbs)
    (Finset.mem_univ (i, j))

/-- Every within-row cost difference is bounded by `inst.rowSpread`. -/
theorem sub_le_rowSpread (inst : Instance) (i j k : Fin inst.n) :
    inst.cost (i, k) - inst.cost (i, j) ≤ (inst.rowSpread : ℤ) := by
  have hk := Finset.le_sup (s := Finset.univ)
    (f := fun k' : Fin inst.n => (inst.cost (i, k') - inst.cost (i, j)).toNat) (Finset.mem_univ k)
  have hj := Finset.le_sup (s := Finset.univ)
    (f := fun j' : Fin inst.n => Finset.univ.sup fun k' =>
      (inst.cost (i, k') - inst.cost (i, j')).toNat) (Finset.mem_univ j)
  have hi := Finset.le_sup (s := Finset.univ)
    (f := fun i' : Fin inst.n => Finset.univ.sup fun j' => Finset.univ.sup fun k' =>
      (inst.cost (i', k') - inst.cost (i', j')).toNat) (Finset.mem_univ i)
  exact (Int.self_le_toNat _).trans (Nat.cast_le.mpr (hk.trans (hj.trans hi)))

/-- Row-major word encoding `n :: matrixWords` (`1 + n * n` words). -/
@[expose] def encode (inst : Instance) : List ℕ :=
  inst.n :: (List.finRange inst.n).flatMap fun i =>
    (List.finRange inst.n).map fun j => Signed.encode (inst.cost (i, j))

/-- Word-value envelope covering input words, workspace addresses, `(n + 1)`-scaled shifted costs,
prices, reduced costs, and accumulated total assignment cost (`w = O(log n + log M)`). -/
@[expose] def wordBound (inst : Instance) : ℕ :=
  2 * (inst.n * inst.n) + 5 * inst.n + 4 * (inst.n + 1) * inst.maxMag + 10

/-- Optimal assignment list `[obj_0, …, obj_{n - 1}]` computed by `scaledAuction`
(`scaledAuctionPerm inst.cost`; optimal by `sum_scaledAuctionPerm_le`). -/
@[expose] def assignment (inst : Instance) : List ℕ :=
  (List.finRange inst.n).map fun i => (scaledAuctionPerm inst.cost i).val

/-- Minimum assignment cost `∑ i, inst.cost (i, scaledAuctionPerm inst.cost i)`. -/
@[expose] def minCost (inst : Instance) : ℤ :=
  ∑ i : Fin inst.n, inst.cost (i, scaledAuctionPerm inst.cost i)

/-- Minimum assignment cost encoded via `Signed.encode`. -/
@[expose] def encodedMinCost (inst : Instance) : ℕ :=
  Signed.encode inst.minCost

@[simp] theorem length_assignment (inst : Instance) : inst.assignment.length = inst.n := by
  simp [assignment]

/-- Length of the encoded input list `inst.encode`. -/
theorem encode_length (inst : Instance) : inst.encode.length = 1 + inst.n * inst.n := by
  rw [encode, List.length_cons,
    List.length_flatMap_of_forall_length_eq (k := inst.n) (fun _ _ => by simp),
    List.length_finRange, Nat.add_comm]

/-- Every word of `inst.encode` fits in `w` bits when `Fits w inst.wordBound`. -/
theorem inputFits_encode {w : ℕ} (inst : Instance) (hw : Fits w inst.wordBound) :
    InputFits w inst.encode :=
  InputFits.flatMap_finRange [inst.n] (fun i j => Signed.encode (inst.cost (i, j)))
    (hw.of_le (by unfold wordBound; dsimp only [List.length]; nlinarith))
    (by
      simp only [List.mem_singleton]
      rintro _ rfl
      exact hw.of_le (by unfold wordBound; nlinarith))
    (fun i j => hw.of_le ((Signed.encode_le_two_mul_add_one
      (inst.natAbs_cost_le_maxMag i j)).trans (by unfold wordBound; nlinarith)))

end Instance

/-- Problem instance for Bertsekas's Gauss–Seidel `ε`-auction on an `n × n` integer cost matrix. -/
structure EpsInstance where
  /-- Common number of persons and objects. -/
  n : ℕ
  /-- Bidding increment `ε` (admitted when `0 < eps`). -/
  eps : ℕ
  /-- Signed integer assignment cost `Fin n × Fin n → ℤ`. -/
  cost : Fin n × Fin n → ℤ

namespace EpsInstance

/-- Underlying `n × n` cost matrix instance. -/
abbrev toInstance (inst : EpsInstance) : Instance := ⟨inst.n, inst.cost⟩

/-- Maximum entry magnitude `max_{i, j} |cost (i, j)|` (`0` when `n = 0`). -/
abbrev maxMag (inst : EpsInstance) : ℕ := inst.toInstance.maxMag

/-- Maximum within-row cost difference `max_{i, j, k} (cost (i, k) - cost (i, j))` (`0` when
`n = 0`). -/
abbrev rowSpread (inst : EpsInstance) : ℕ := inst.toInstance.rowSpread

/-- Row-major word encoding `n :: eps :: matrixWords` (`2 + n * n` words). -/
@[expose] def encode (inst : EpsInstance) : List ℕ :=
  inst.n :: inst.eps :: inst.toInstance.encode.tail

/-- Word-value envelope covering input words, workspace addresses, shifted costs, reduced costs,
and object prices (`w = O(log n + log M + log ε)`). -/
@[expose] def wordBound (inst : EpsInstance) : ℕ :=
  2 * (inst.n * inst.n) + 5 * inst.n + 4 * inst.maxMag + 2 * inst.eps + 8

/-- Person-indexed assignment list `[obj_0, …, obj_{n - 1}]` computed by
`auction inst.cost inst.eps` (`auctionPerm` when `0 < inst.eps`; `n * eps`-optimal by
`sum_auctionPerm_le`). -/
@[expose] def assignment (inst : EpsInstance) : List ℕ :=
  (List.finRange inst.n).map fun i => ((auction inst.cost (inst.eps : ℤ)).objectOf i).val

@[simp] theorem length_assignment (inst : EpsInstance) : inst.assignment.length = inst.n := by
  simp [assignment]

/-- Length of the encoded input list `inst.encode`. -/
theorem encode_length (inst : EpsInstance) : inst.encode.length = 2 + inst.n * inst.n := by
  have htail : inst.toInstance.encode.tail.length = inst.n * inst.n := by
    have := inst.toInstance.encode_length
    simp only [Instance.encode, List.length_cons] at this
    simp only [Instance.encode, List.tail_cons]
    omega
  simp only [encode, List.length_cons, htail]
  omega

/-- Every word of `inst.encode` fits in `w` bits when `Fits w inst.wordBound`. -/
theorem inputFits_encode {w : ℕ} (inst : EpsInstance) (hw : Fits w inst.wordBound) :
    InputFits w inst.encode :=
  InputFits.flatMap_finRange [inst.n, inst.eps] (fun i j => Signed.encode (inst.cost (i, j)))
    (hw.of_le (by unfold wordBound; dsimp only [List.length]; nlinarith))
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl) <;> exact hw.of_le (by unfold wordBound; nlinarith))
    (fun i j => hw.of_le ((Signed.encode_le_two_mul_add_one
      (inst.toInstance.natAbs_cost_le_maxMag i j)).trans (by unfold wordBound; nlinarith)))

end EpsInstance

end Cslib.Algorithms.WordRAM.Auction
