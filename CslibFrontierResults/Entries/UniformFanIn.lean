/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Circuit.Boolean.UniformFanIn

/-! # Logspace-uniform fan-in reduction -/

register_result "logspace-uniform-ac-within-next-nc" where
  title := "Logspace-uniform AC^i is contained in logspace-uniform NC^(i+1)"
  topic := "circuit complexity"
  sources := [
    { paper := AroraBarak09,
      theorem := "Fan-in simulation following Definition 6.25, with Definition 6.14 uniformity",
      locator := "Sections 6.2.1 and 6.7.1, printed pp. 112 and 117–118" }
  ]
  theorems := [Cslib.Circuits.Boolean.logspaceUniformAC_subset_NC_succ]
  scope := "Every natural exponent and every total Boolean language. Both generators receive \
    the input length in unary and stream the native gate list in topological order, with binary \
    wire numbers. Lean's native gate lists allow repeated wire references and nullary AND and OR \
    gates. Section 6.7.1 gives the binary simulation of unbounded gates and defines the uniform \
    variants. The Lean construction proves logarithmic workspace for the resulting generator."
