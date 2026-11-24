/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.DecisionTree.Truncate

/-!
# Collected results: truncation and the spectrum of small decision trees
-/

register_result "odonnell-decision-tree-truncation-and-concentration" where
  title := "Truncating a decision tree of size s at log(s/ε) changes it on at most an ε fraction \
    of inputs, and its spectrum is ε-concentrated on degree up to log(s/ε)"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Proposition 3.17 and Exercise 3.22",
      locator := "arXiv:2105.10386v1, §3.2, printed p. 74; Exercise 3.22 in §3.6, printed p. 87" }
  ]
  theorems := [
    Cslib.DecisionTree.dens_eval_truncate_floor_logb_ne_le,
    Cslib.DecisionTree.sum_fourierCoeff_sq_logb_lt_card_le
  ]
  scope := "Decision trees t : DecisionTree ι β over a finite coordinate type ι, on the uniform \
    cube ι → Bool; log is log₂ (Real.logb 2), as in the book (List of Notation, printed p. xvi). \
    Exercise 3.22 (closeness claim): for t with t.QueriesDistinctFrom A for some A (A = ∅ is \
    the book's convention, Definition 3.13, printed p. 73, that no path queries a coordinate \
    twice) and every ε > 0, cutting every path at length ⌊log₂(t.leafCount / ε)⌋ \
    (DecisionTree.truncate) gives a tree that outputs some (t.eval x) on all but an ε fraction \
    of inputs. The new leaves are labelled none rather than −1 or 1; any such labelling errs \
    on at most the same inputs. For such trees every leaf is reachable, so leafCount is the \
    book's size (Definition 3.14, printed p. 74). The book's ε ∈ (0, 1] is relaxed to ε > 0. \
    The proof goes through the general-k bound s / 2 ^ (k + 1) \
    (DecisionTree.dens_eval_truncate_ne_le), which is not registered separately. \
    Proposition 3.17: for every tree t (repeated queries allowed), every g : β → ℝ with \
    |g b| ≤ 1 and every ε > 0 (the book's ε ∈ (0, 1] is relaxed to ε > 0), the Fourier \
    weight of fun x => g (t.eval x) on the sets S with log₂(t.leafCount / ε) < #S is at \
    most ε. The book's case is g = signVal on a tree of size \
    s without repeated queries; leafCount is the structural leaf count, which for a tree that \
    repeats queries also counts unreachable leaves. The proof follows the book's route through \
    Exercise 3.22, with the new leaves valued 0 rather than ±1, and pruning first \
    (DecisionTree.queriesDistinctFrom_prune, DecisionTree.leafCount_prune_le) to drop the \
    distinct-query hypothesis."
