/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Crypto.Primitives.UHF.PrefixFreePRF

/-!
# Collected results: universal hashing from prefix-free PRFs
-/

register_result "extendable-prefix-free-prf-computational-universality" where
  title := "An extendable prefix-free PRF is computationally universal"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 7.3",
      locator := "v0.6, Section 7.2.2, printed pp. 258–259; equations (7.6)–(7.8)" }
  ]
  theorems := [
    Cslib.Crypto.UHF.isComputationalUHF_of_extendable_prefixFreePRF,
    Cslib.Crypto.UHF.succProbability_collisionGame_le_prefixFreeCollisionReduction,
    Cslib.Crypto.UHF.isQueryBounded_prefixFreeCollisionReduction
  ]
  scope := "Uniform strict PPT collision adversaries and a strict oracle-PPT wrapper with \
    a private uniform n-bit key and public unary security parameter. Messages are raw bit \
    lists of whole blocks. Block width and hash-domain recognition are polynomial-time \
    computable. The PRF domain admits every one-block extension of a valid hash input, and \
    the reciprocal of the reply-space cardinality is negligible. The wrapper rejects \
    invalid or repeated guesses, always appends a common block to an accepted pair, and \
    caps each of its two replies at the width it computes by public PRF evaluation. \
    The resulting queries are nonempty and in the PRF domain, so the library's \
    domain-relative prefix condition applies to the source game."
