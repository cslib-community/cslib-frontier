/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Allocation
public import Mathlib.Data.List.FinRange
import CslibFrontier.Foundations.Data.List.RowMajor
import Mathlib.Data.List.GetD

/-!
# Array blocks in ordinary initialized inputs

## Main results

* `WordRAM.Data.init_mem_append`: read a word after an arbitrary prefix in `Data.init`, accounting
  for the machine's length header.
* `WordRAM.Data.init_mem_of_length_lt`: every cell past the input is `0`.
* `WordRAM.Data.init_realizes_append`: a list segment appears at its actual initialized address,
  including the machine's length header.
* `WordRAM.Data.init_mem_flatMap_finRange`, `WordRAM.InputFits.flatMap_finRange`: row-major lookup
  in `Data.init` and `InputFits` after a header prefix.

This is a representation API for the existing `Data.init`, with no alternate input convention.
It lives in a narrow input-array module to keep the list `getD` dependency and initialization
bridge out of `Allocation`. This avoids changing the allocation interface and rebuilding its
unrelated importers when the input representation API changes.
-/

public section

namespace Cslib.WordRAM

/-- Reading word `k` after an arbitrary prefix `pre` in `Data.init (pre ++ rest)`. The extra
address word is the standard unsigned input-length header at address `0`. -/
theorem Data.init_mem_append {r : ℕ} (pre rest : List ℕ) (k : ℕ) :
    (Data.init (pre ++ rest) : Data r).mem (pre.length + 1 + k) = rest.getD k 0 := by
  rw [show pre.length + 1 + k = (pre.length + k) + 1 by omega,
    Data.init_mem_succ, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

/-- Every cell past the input is `0` in `Data.init`. -/
theorem Data.init_mem_of_length_lt {r : ℕ} {input : List ℕ} {a : ℕ} (h : input.length < a) :
    (Data.init input : Data r).mem a = 0 := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  rw [Data.init_mem_succ]
  exact List.getD_eq_default _ _ (by omega)

/-- The payload between an arbitrary prefix and suffix occupies its corresponding actual
input block. The extra address word is the standard unsigned input-length header. -/
theorem Data.init_realizes_append {r : ℕ} (pre payload post : List ℕ) :
    (Block.mk (pre.length + 1) payload.length).Realizes
      (Data.init (pre ++ (payload ++ post)) : Data r).mem payload.get := by
  intro i
  change (Data.init (pre ++ (payload ++ post)) : Data r).mem
    (pre.length + 1 + i.val) = payload.get i
  rw [Data.init_mem_append, List.getD_append _ _ _ _ i.isLt, List.getD_eq_get]

/-- Reading entry `(i, j)` of a flattened `n × d` row-major block after a header prefix `pre`
in `Data.init`. -/
theorem Data.init_mem_flatMap_finRange {r n d : ℕ} (pre : List ℕ) (f : Fin n → Fin d → ℕ)
    (i : Fin n) (j : Fin d) :
    (Data.init (pre ++ (List.finRange n).flatMap fun i' => (List.finRange d).map (f i')) :
      Data r).mem (pre.length + 1 + (i.val * d + j.val)) = f i j := by
  have h : ((List.finRange n).flatMap fun i' => (List.finRange d).map (f i')) =
      (List.finRange n).flatMap fun i' => List.ofFn (f i') := by
    simp only [List.ofFn_eq_map]
  rw [Data.init_mem_append, h, List.getD_flatMap_ofFn]

/-- `InputFits` for a header prefix `pre` followed by a flattened `n × d` row-major block. -/
theorem InputFits.flatMap_finRange {w n d : ℕ} (pre : List ℕ) (f : Fin n → Fin d → ℕ)
    (hlen : Fits w (pre.length + n * d)) (hpre : ∀ x ∈ pre, Fits w x)
    (hf : ∀ i j, Fits w (f i j)) :
    InputFits w (pre ++ (List.finRange n).flatMap fun i => (List.finRange d).map (f i)) := by
  refine ⟨?_, fun x hx => ?_⟩
  · simp only [List.length_append, List.length_flatMap, List.length_map, List.length_finRange,
      List.map_const', List.sum_replicate_nat]
    exact hlen
  · simp only [List.mem_append, List.mem_flatMap, List.mem_finRange, List.mem_map,
      true_and] at hx
    rcases hx with hx | ⟨i, j, rfl⟩
    · exact hpre x hx
    · exact hf i j

end Cslib.WordRAM
