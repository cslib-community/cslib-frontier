/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Circuit.Boolean.Lupanov.FormulaSynthesis

/-!
# Proposed Lupanov formula result entries

These mappings accompany the implementation for source review. A reviewer outside the authoring
fleet must check the source, definitions and scope before merge. No such review is claimed here.
-/

register_result "lupanov-unrestricted-formula-upper-bound" where
  title := "Lupanov's unrestricted-depth upper bound for literal-only De Morgan formulas"
  topic := "circuit complexity"
  sources := [
    { paper := Lupanov1961Formulas,
      theorem := "Unrestricted-depth upper corollary of the unnumbered theorem",
      locator := "§4, unnumbered theorem, printed/PDF p. 8; class inclusion in §1, equation (1), \
        p. 3; main theorem and equation (5) in §1, p. 4. Literal-only grammar and complexity \
        appear in §1, pp. 1–2; the binary-log convention is explicit on p. 3" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.LupanovFormula.eventually_exists_computes_leafSize_le
  ]
  scope := "For every real ε > 0, eventually in the natural input dimension n, every total \
    Boolean function BitString n → Bool has a native Formula Boolean.signature n computing it \
    with at most (1 + ε) 2^n / Real.logb 2 n input-leaf occurrences. The witness satisfies \
    Formula.IsConstantFree and Formula.IsNNF: no nullary constant gates and negations only on \
    inputs. Thus input-leaf count is the source's literal count. Native constants used inside \
    the construction are propagated away; constant functions use two literals, with no change \
    to the eventual budget. Binary AND/OR trees match the source's inductive syntax, with \
    its alternating-depth restriction omitted. All parameter choices, open-sphere \
    partitions and native formula realizations are proved, with no supplied formula or \
    realizability premise. This is only the unrestricted upper corollary; it does not claim \
    the source's alternating-depth-three theorem, asymptotic equality, or almost-all lower \
    bound. Proposed entry: outside-authoring-fleet source review is pending and is a merge hold."

register_result "lupanov-power-of-two-open-sphere-partition" where
  title := "Lupanov's partition of a power-of-two-dimensional cube into open spheres"
  topic := "circuit complexity"
  sources := [
    { paper := Lupanov1961Formulas,
      theorem := "Lemma 3",
      locator := "§4, Lemma 3, printed/PDF p. 8 of the English translation; \
        the open-sphere definition is on p. 7" }
  ]
  theorems := [
    Cslib.BitString.exists_openSpherePartition
  ]
  scope := "For every r : Nat, dimension d = 2^r has a finite set C of binary centers with \
    C.card * d = 2^d and a bijection from pairs (center in C, coordinate in Fin d) to the \
    Boolean cube by flipping that coordinate. This supplies disjoint open radius-one spheres \
    covering the entire cube, including r = 0 as an extension of the source's asymptotic use. \
    The bijection expresses both coverage and disjointness of the source's spheres; their \
    centers are excluded. Proposed entry: outside-authoring-fleet source review is pending \
    and is a merge hold."
