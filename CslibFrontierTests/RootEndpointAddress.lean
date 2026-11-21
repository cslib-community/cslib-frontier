/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootEndpointAddress

open Turing.MultiTapeTM.RootEndpointAddress

-- Source, control target, and work target of a two-interval graph.
example : query 1 ⟨4, 1, 0⟩ = some ⟨.inl 0, 10⟩ := by decide
example : query 1 ⟨4, 1, 9⟩ = some ⟨.inl 3, 11⟩ := by decide
example : query 1 ⟨4, 1, 10⟩ = some ⟨.inr ⟨0, 0, 4⟩, 12⟩ := by decide
example : scanIndices (query 1 ⟨4, 1, 15⟩) = (2, 1) := by decide

-- Copy subdivision and the zero-head control graph.
example : query 1 ⟨4, 2, 21⟩ = some ⟨.inr ⟨0, 0, 4⟩, 15⟩ := by decide
example : query 0 ⟨2, 1, 3⟩ = some ⟨.inl 3, 5⟩ := by decide

-- Empty universes and the first padded edge.
example : query 1 ⟨0, 4, 0⟩ = none := by decide
example : query 1 ⟨4, 0, 0⟩ = none := by decide
example : query 1 ⟨4, 1, 16⟩ = none := by decide
