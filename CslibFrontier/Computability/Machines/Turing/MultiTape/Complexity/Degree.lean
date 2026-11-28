/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- vendored: move pure degree bounds to ResourceBounds.Degree and add direct plain certificates.

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreeComposition
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreeClosure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreePrimitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime

/-!
# Computability with independent polynomial degrees

The plain `ComputableInDegree` certificates track time and workspace degree `d` separately from
encoded-output degree `e`, including degree zero. This entry point exports degree weakening,
composition, branching, pairing and encoding primitive providers. Left folds live in
`Complexity.Fold`; no derived tidy degree calculus is retained here.
-/
