/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Crypto.Primitives.UHF.CBCMAC

/-!
# Collected results: universal hashing from prefix-free PRFs
-/

register_result "cbc-mac-computational-universality" where
  title := "CBC-MAC from a secure PRF is computationally universal"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Corollary 7.5 (CBC-MAC case)",
      locator := "v0.6, Section 7.2.2, printed p. 260; equation (7.10) and Q = 2 specialization" }
  ]
  theorems := [
    Cslib.Crypto.PseudorandomFunction.isMultiQueryUHF_cbcMac,
    Cslib.Crypto.PseudorandomFunction.isComputationalUHF_cbcMac,
    Cslib.Crypto.UHF.succProbability_multiQueryGame_cbcMac_le,
    Cslib.Crypto.UHF.succProbability_collisionGame_cbcMac_le,
    Cslib.Crypto.UHF.isOraclePPT_cbcMacMultiQueryReduction
  ]
  scope := "The CBC-MAC case of Corollary 7.5 in the word model, with a base PRF on n-bit keys, \
    blocks and replies. The hash domain consists of zero to ℓ(n) whole blocks with a unary \
    polynomial-time cap ℓ. Uniform strict PPT adversaries submit lists of messages or pairs. \
    A collision requires two distinct valid messages. The prefix-free batch wrapper appends a \
    common fresh block to each distinct valid message when the alphabet exceeds the block \
    budget. The base-PRF reduction is certified strict oracle PPT. The concrete \
    bound uses (7.10)'s CBC term Q²(ℓ(n)+1)²/(2 · 2^n) with the sharper Q.choose 2/2^n \
    for reply collisions. The single-pair wrapper uses Q = 2 and preserves success exactly. \
    At width zero only the empty word is valid. At positive widths too small for the block \
    budget, the CBC term already bounds success by one. Cascade is tracked in #5801."

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
    lists of whole positive-width blocks. Width and hash-domain recognition are polynomial-time \
    computable. For hash inputs of one to ℓ blocks, the PRF's length clause on queries of \
    one to ℓ + 1 blocks gives fixed-width digests. The word theorem also admits the \
    zero-block hash input by extending it to one block. If the oracle domain excludes \
    the empty word, the family supplies its digest width separately, as CBC-MAC does. \
    The conclusion compares raw bit lists, which at the declared width represent \
    fixed-width bit strings. Every one-block extension of a valid hash input is PRF-valid, and \
    the reciprocal of the reply-space cardinality is negligible. The wrapper rejects \
    invalid or repeated guesses, always appends a common block to an accepted pair, and \
    caps each of its two replies at the width it computes by public PRF evaluation. \
    The resulting queries are nonempty and in the PRF domain, so the library's \
    domain-relative prefix condition applies to the source game."

register_result "extendable-prefix-free-prf-multi-query-universality" where
  title := "An extendable prefix-free PRF is computationally multi-query universal"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 7.4",
      locator := "v0.6, Section 7.2.2, printed pp. 259–260; equation (7.9)" }
  ]
  theorems := [
    Cslib.Crypto.UHF.isMultiQueryUHF_of_extendable_prefixFreePRF,
    Cslib.Crypto.UHF.succProbability_multiQueryGame_le_prefixFreeBatchReduction,
    Cslib.Crypto.UHF.isQueryBounded_prefixFreeBatchReduction
  ]
  scope := "Uniform strict PPT adversaries, a uniform n-bit key, and public unary security \
    parameter. Valid hash inputs are aligned raw bit lists within a polynomial block cap. \
    The block width and hash-domain recognition are polynomial-time computable. \
    Each one-block extension is in the PRF domain, which eventually contains the all-zero \
    block used to compute the reply width by public evaluation. Both alphabet reciprocals \
    are negligible. The wrapper filters and deduplicates the batch, appends a fresh block, \
    and tests equality of fixed-width replies. The adversary's strict PPT certificate gives \
    the query cap. Equation (7.9) keeps the sharper birthday term choose(Q, 2) over the \
    size of the reply alphabet."
