/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Complexity.Classes.LogSpace.Circuit

/-! # Nondeterministic logarithmic space in uniform NC -/

register_result "nl-in-logspace-uniform-nc" where
  title := "NL is contained in logspace-uniform NC²"
  topic := "circuit complexity"
  sources := [
    { paper := AroraBarak07,
      theorem := "Chapter 6, Exercise 9(c)",
      locator := "Printed p. 114 (PDF p. 130); Definitions 6.5 and 6.21, pp. 104 and 109" }
  ]
  theorems := [Cslib.Complexity.NL_subset_logspaceUniformNC_two]
  scope := "Every bit language in NL has a polynomial-size, log-squared-depth family of \
    fan-in-two De Morgan circuits. A single logspace transducer generates the native topological \
    gate list and binary wire addresses on input the length in unary. Remark 6.6 permits list \
    representations. The exercise concludes NL is contained in NC; the proof specifies level 2."
