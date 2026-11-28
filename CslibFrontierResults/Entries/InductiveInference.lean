/-
Copyright (c) 2026 Matthew Doty, Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Alexandre Rademaker
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.MachineLearning.InductiveInference.Informant

/-! # Language identification in the limit -/

register_result "gold-superfinite-not-identifiable" where
  title := "Gold's theorem: no class with all finite languages and an infinite one is \
    identifiable from text"
  topic := "inductive inference"
  sources := [
    { paper := Gold1967,
      theorem := "§8, Language identifiability (arbitrary text): every proper superclass of \
        the finite languages is not ineffectively identifiable",
      locator := "Information and Control 10 (1967), printed p. 460; construction in §9, \
        pp. 460–461" }
  ]
  theorems := [Cslib.MachineLearning.InductiveInference.not_identifiable_of_finite_subsets]
  scope := "Ineffective learners, as in Gold's §8: any function from finite sequences of \
    presentations to conjectured languages rather than names. Texts may contain pauses, which \
    Gold's (§2, p. 450) do not. Strings form an arbitrary countable type rather than words \
    over a finite alphabet; the corollaries for regular and context-free languages are in \
    `CslibFrontier.MachineLearning.InductiveInference.FormalLanguages`. The general statement \
    assumes the class contains one infinite language and all of its finite subsets."

register_result "blum-blum-locking-sequence" where
  title := "Locking-sequence lemma: a learner identifying a language from text has a locking \
    sequence for it"
  topic := "inductive inference"
  sources := [
    { paper := BlumBlum1975, theorem := unverified, locator := unverified }
  ]
  theorems := [Cslib.MachineLearning.InductiveInference.Identifies.exists_isLockingSequence]
  scope := "Ineffective learners conjecturing languages, over an arbitrary countable type of \
    strings; texts may contain pauses. The lemma is stated for a single language and learner."

register_result "gold-informant-identifiable" where
  title := "Every countable class of languages is identifiable in the limit from informant"
  topic := "inductive inference"
  sources := [
    { paper := Gold1967, theorem := unverified, locator := unverified }
  ]
  theorems := [Cslib.MachineLearning.InductiveInference.identifiableFromInformant_of_countable]
  scope := "Ineffective learners conjecturing languages, by identification by enumeration. Any \
    countable class over an arbitrary type of strings; no effective enumeration of the class or \
    effective learner is required."
