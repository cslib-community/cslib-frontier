/-
Copyright (c) 2026 Sam, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam, Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Algorithms.PlantedClique.CommonNeighborAsymptotics

/-!
# Collected results: planted-clique recovery
-/

register_result "planted-clique-recovery-every-sqrt-constant" where
  title := "Polynomial-time recovery of a planted clique of size at least c √n, for every \
    fixed c > 0, with an integer matrix-power base solver"
  topic := "algorithms"
  sources := [
    { paper := AlonKrivelevichSudakov1998,
      theorem := "main result, as stated in the introduction",
      locator := "author-hosted manuscript (bibliography URL), printed p. 2; Algorithm B and \
        its exposure argument, §2.3, printed pp. 7–8" }
  ]
  theorems := [Cslib.Algorithms.PlantedClique.exists_commonNeighborRecover_ppt_tendsto_failure]
  scope := "For every fixed real c > 0 there is a seed size s such that the deterministic \
    program commonNeighborRecover recoverInput s is realized by one multi-tape machine with a \
    strict polynomial clock (IsPPTOn, on the input record of unary n, unary k and row-major \
    adjacency bits; the polynomial may depend on s) and, for every target schedule k with \
    c √n ≤ k(n) eventually and every family of priors on the k(n)-subsets of Fin n, the \
    probability that it does not return exactly the hidden set tends to 0. The hidden set is \
    drawn from the prior before independent fair edge coins, and the program receives only the \
    graph and k(n); uniform planting, the source's model, is a special case. Success is exact \
    recovery of the hidden set, not finding some clique. The program is the common-neighbor \
    reduction of Algorithm B over an exact integer matrix-power base solver, a variant \
    developed for this formalization in place of the second-eigenvector Algorithm A, with \
    conservative constants. Not covered: the source's constant 10 for Algorithm A, a \
    finite-precision implementation of the second-eigenvector algorithm and its running time, \
    which remain open in #6238. The finite recovery bound for the exact second-eigenvector \
    specification (searchProblem_recoverEigenvector_failure_le) carries no running-time claim \
    and is not registered here. Outside-fleet source check (agent review, \
    codex-coord-20261111-1634) at c4b69bc953ba: \
    https://github.com/cslib-community/cslib-frontier/pull/6193#pullrequestreview-5945776197"
