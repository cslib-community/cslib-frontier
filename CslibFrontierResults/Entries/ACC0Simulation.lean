/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Circuit.Boolean.ACC0.Simulation

/-! # Simulation of modular counting gates by logarithmic-depth circuits -/

register_result "acc0-subset-nc1" where
  title := "Nonuniform ACC⁰ is contained in NC¹"
  topic := "circuit complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 13, Exercise 4",
      locator := "Web draft 2007-01-08, printed p. 252 (PDF p. 268), Definitions 13.3–13.4" }
  ]
  theorems := [Cslib.Circuits.Boolean.ACC0_subset_NC_one]
  scope := "Both circuit families are nonuniform. Polynomial-size constant-depth circuits with \
    unbounded fan-in AND, OR and fixed-modulus counting gates can be simulated by polynomial-size \
    fan-in-two circuits of logarithmic depth. A finite list of moduli shares a single product \
    modulus by repeating wires. The exercise is interpreted for nonuniform NC¹."
