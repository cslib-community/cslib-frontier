/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Circuit.Boolean.Rectifier.Asymptotic

register_result "lupanov-rectifier-row-pattern-bound" where
  title := "Every Boolean p × q matrix has a depth-two rectifier realization with at most \
    p + q · 2^(q - 1) wires"
  topic := "circuit complexity"
  sources := [
    { paper := Lupanov1956,
      theorem := "Section 2°, unnumbered Lemma",
      locator := "English translation, PDF p. 2; printed page of the Russian original not \
        verified" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.Rectifier.exists_depth_two
  ]
  scope := "For every natural p and q and every Boolean matrix with p input rows and q \
    output columns. A witness is a native Circuit over the pure disjunction signature \
    (operation m has arity m); IsTwoLayer requires it to be a composition of two matrix \
    layers, so output poles have distinct terminal gates rather than free aliases. \
    Matrix action is OR over the input rows whose entries in the output column are true. \
    Program.cost id counts all gate-input wires, including those entering terminal gates; \
    the output pointers themselves are free. With wires as edges, a two-layer circuit has \
    edges only from inputs to inner gates and from inner gates to outputs, so it is a \
    rectifier (p, q)-circuit of rank at most two in the source's sense and the statement \
    bounds the source's B₂; this reading is prose, since B₂ is not defined in the library. \
    Native circuit depth at most two follows from IsTwoLayer.depth_le. Nullary \
    disjunctions represent vertices with no incoming path. Zero-dimensional matrices are \
    included as an extension, with natural truncated subtraction in q - 1. No construction \
    or factorization hypothesis is assumed. The corollary \
    Cslib.Circuits.orDepthComplexity_two_le_add_mul_two_pow for the library's \
    rectifier-graph measure orDepthComplexity 2 (transposed matrix) is weaker and is not \
    the registered result: that model admits edges into input poles and out of output poles."

register_result "lupanov-rectifier-asymptotic-upper" where
  title := "Lupanov's rectangular rectifier synthesis upper bound with leading constant one"
  topic := "circuit complexity"
  sources := [
    { paper := Lupanov1956,
      theorem := "Theorem 1, upper-bound direction with corrected growth condition",
      locator := "Section 2°; English translation, PDF p. 3, proof part 1; printed page of \
        the Russian original not verified" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.Rectifier.exists_depth_two_asymptotic_upper,
    Cslib.Circuits.Boolean.Rectifier.exists_depth_two_eventually
  ]
  scope := "For each real ε > 0, uniform natural thresholds N and K ensure that every \
    Boolean p × q matrix has a native two-layer rectifier circuit with at most \
    (1 + ε) p q / Real.logb 2 p wires whenever p ≥ N and q ≥ K Real.logb 2 p. The sequence \
    version assumes p tends to infinity and q / Real.logb 2 p tends to infinity and is \
    uniform in the matrix at each index. Uses the exact real logarithm and the same \
    distinct-pole, pure-OR, gate-input wire model as the finite row-pattern result; as \
    there, a two-layer witness is a rectifier (p, q)-circuit of rank at most two in the \
    source's sense, so the statements bound the source's B₂ (a prose reading: B₂ is not \
    defined in the library). The \
    available English translation displays log₂ p / q tending to infinity; here the \
    reciprocal q / log₂ p tends to infinity, as required to absorb the final incomplete \
    block in its upper-bound proof and as stated in Jukna's companion note on Lupanov's \
    decomposition lemma. This corrects the displayed translation; the Russian original \
    has not been inspected. The source additionally assumes p ≥ q; that condition is \
    unnecessary for the proved upper \
    construction and is omitted. The counting lower bound, minimization over all rectifier \
    graphs, and the full asymptotic equivalence in Theorem 1 are not asserted. The corollary \
    Cslib.Circuits.orDepthComplexity_two_asymptotic_upper for the library's rectifier-graph \
    measure orDepthComplexity 2 (transposed matrix) is weaker and is not the registered \
    result."
