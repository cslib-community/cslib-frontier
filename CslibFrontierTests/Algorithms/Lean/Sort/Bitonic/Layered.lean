/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Lean.Sort.Bitonic.Layered

/-!
# Tests for Batcher's network as global layers

Concrete checks, by `decide` on four positions, for
`CslibFrontier.Algorithms.Lean.Sort.Bitonic.Layered`:

* `schedule` lists the merge levels and exponents, and has `6` layers on `8` positions;
* `partner` and `low` at the boundaries of a bit;
* `cmpRun` along `schedule 2` with the directions `dirFn 2 true` sorts `[3, 1, 2, 0]`, and with
  `dirFn 2 false` sorts it in descending order;
* a descending comparison exchanges ties and an ascending one does not;
* `stage` with all flags clear is the identity, and with all flags set exchanges every pair.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.Lean.Sort.Bitonic.Layered

open Cslib.BitonicSort

/-! ### The schedule -/

/-- The schedule on four positions: merge level `1`, then merge level `2` with exponents `1, 0`. -/
example : schedule 2 = [(1, 0), (2, 1), (2, 0)] := by decide

/-- Eight positions have `1 + 2 + 3` layers. -/
example : (schedule 3).length = 6 := by decide

/-! ### Pairs of positions -/

/-- The partner of a position with bit `e` clear is above it, and of one with bit `e` set below. -/
example : partner 1 5 = 7 ∧ partner 1 7 = 5 ∧ partner 0 5 = 4 ∧ partner 2 3 = 7 := by decide

/-- The lower position of a pair is the one with bit `e` clear. -/
example : low 0 5 = 4 ∧ low 1 7 = 5 ∧ low 2 3 = 3 ∧ low 2 7 = 3 := by decide

/-! ### The comparator network -/

/-- The input records `[3, 1, 2, 0]`. -/
def input : ℕ → ℕ := fun i => [3, 1, 2, 0].getD i 0

/-- The comparator network of four positions sorts them in ascending order. -/
example : (List.range 4).map (cmpRun id (dirFn 2 true) (schedule 2) input) = [0, 1, 2, 3] := by
  decide

/-- With the top direction descending, it sorts in descending order. -/
example : (List.range 4).map (cmpRun id (dirFn 2 false) (schedule 2) input) = [3, 2, 1, 0] := by
  decide

/-- A descending comparison exchanges equal keys, an ascending one does not. -/
example : cmpFlag id (fun _ _ => false) 1 0 (fun _ => 5) 0 = true ∧
    cmpFlag id (fun _ _ => true) 1 0 (fun _ => 5) 0 = false := by decide

/-- Ascending comparisons exchange exactly the strict inversions. -/
example : cmpFlag id (fun _ _ => true) 1 0 input 0 = true ∧
    cmpFlag id (fun _ _ => true) 1 0 input 2 = true ∧
    cmpFlag id (fun _ _ => true) 1 0 id 0 = false := by decide

/-! ### The switching network -/

/-- With all flags clear, every stage of the network is the input. -/
example : (List.range 4).map (stage (schedule 2) (fun _ _ => false) input 3) = [3, 1, 2, 0] := by
  decide

/-- With all flags set, the layer of exponent `0` exchanges every neighbouring pair. -/
example : (List.range 4).map (stage [(1, 0)] (fun _ _ => true) input 1) = [1, 3, 0, 2] := by
  decide

/-- The stages of the comparator flags are the stages of the comparator network
(`stage_cmpFlags`), here after two layers. -/
example : (List.range 4).map (stage (schedule 2) (cmpFlags id (dirFn 2 true) (schedule 2) input)
    input 2) = (List.range 4).map (cmpRun id (dirFn 2 true) ((schedule 2).take 2) input) := by
  rw [stage_cmpFlags id (dirFn 2 true) (schedule 2) input 2 (by decide)]

end CslibFrontierTests.Algorithms.Lean.Sort.Bitonic.Layered
