/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.RawScheduleSum

open Cslib.Complexity.CountingSimulation.RawScheduleSum
open Turing.MultiTapePTM Turing.MultiTapeTM

-- Padding at the invalid pair is necessary even for a constant nonzero contraction.
example : weight (k := 0) (q := 1) (fun _ => 3) [true, true] = 0 := by decide

-- For one input head and one round there are three schedules. Each contributes three.
example : total (k := 0) (q := 1) 4 (fun _ => 3) ⟨3, by decide⟩ = true := by
  rw [total_apply, Finset.sum_const, Finset.card_univ]
  decide

-- At zero rounds there is one schedule and the entire leaf value survives.
example : total (k := 2) (q := 0) 3 (fun _ => 6) ⟨2, by decide⟩ = true := by
  rw [total_apply, Finset.sum_const, Finset.card_univ]
  decide
