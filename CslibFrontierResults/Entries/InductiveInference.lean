/-
Copyright (c) 2026 Matthew Doty, Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Alexandre Rademaker
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.MachineLearning.InductiveInference.Basic

/-! # Language identification in the limit -/

register_result "gold-superfinite-not-identifiable" where
  title := "Gold's theorem: no class with all finite languages and an infinite one is \
    identifiable from text"
  topic := "inductive inference"
  sources := [
    { paper := Gold1967, theorem := unverified, locator := unverified }
  ]
  theorems := [Cslib.MachineLearning.InductiveInference.not_identifiable_of_finite_subsets]
  scope := "Ineffective learners: any function from finite sequences of presentations to \
    conjectured languages, which strengthens the impossibility. Texts may contain pauses. \
    Strings form an arbitrary countable type rather than words over a finite alphabet; the \
    corollaries for regular and context-free languages are in \
    `CslibFrontier.MachineLearning.InductiveInference.FormalLanguages`. The general statement \
    assumes the class contains one infinite language and all of its finite subsets."
