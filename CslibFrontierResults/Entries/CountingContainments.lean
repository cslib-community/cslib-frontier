/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Complexity.Classes.BPPpath.ApproximateCounting
import CslibFrontier.Computability.Complexity.Classes.BQP.Nondeterministic
import CslibFrontier.Computability.Complexity.Classes.PostBQP
import CslibFrontier.Computability.Complexity.Classes.QMA.Counting

/-!
# Counting characterizations and containments for encoded decision languages
-/

register_result "qma-subset-a0pp" where
  title := "QMA is contained in A₀PP"
  topic := "quantum complexity"
  sources := [
    { paper := Vyalyi2003, theorem := "Theorem 1",
      locator := "ECCC TR03-021, Definition 3 and the trace argument, pp. 5–7" }
  ]
  theorems := [Cslib.Complexity.QMA_subset_A0PP]
  scope := "For every input encoding, a polynomial-time length-uniform real-gate verifier with \
    a pure quantum witness, completeness at least 2/3 and soundness at most 1/3 yields a GapP \
    function with a signed binary FP threshold. The source uses strict error inequalities."

register_result "a0pp-subset-pp" where
  title := "A₀PP is contained in PP"
  topic := "counting complexity"
  sources := [
    { paper := Vyalyi2003, theorem := "Observation following Definition 2",
      locator := "ECCC TR03-021, p. 3" }
  ]
  theorems := [Cslib.Complexity.A0PP_subset_PP]
  scope := "The GapP value exceeds the polynomial-time threshold on members and lies in \
    [0, T(x)/2) on nonmembers. Subtracting the threshold gives the sign test for PP."

register_result "nqp-eq-coceqp" where
  title := "NQP equals coC₌P"
  topic := "quantum complexity"
  sources := [
    { paper := FennerGreenHomerPruim1999, theorem := "Theorem 1.1",
      locator := "arXiv:quant-ph/9812056v1, p. 2, with Theorem 3.2 and §4 on amplitudes" }
  ]
  theorems := [Cslib.Complexity.NQP_eq_coCeqP]
  scope := "For every input encoding, the positive-acceptance languages of polynomial-time \
    uniform Hadamard, NOT, CNOT and Toffoli circuits are precisely the nonzero sets of GapP \
    functions. The paper states the theorem for quantum Turing machines."

register_result "postbqp-eq-pp" where
  title := "PostBQP equals PP"
  topic := "quantum complexity"
  sources := [
    { paper := Aaronson2005Postselection, theorem := "Theorem 4",
      locator := "arXiv:quant-ph/0412187v1, Definition 1 and Proposition 2" }
  ]
  theorems := [Cslib.Complexity.PostBQP_eq_PP]
  scope := "For every input encoding, polynomial-time uniform elementary quantum circuits \
    postselect on a positive-probability output bit. Conditional acceptance on the other bit \
    is at least 2/3 for members and at most 1/3 for nonmembers. PP uses strict majority."

register_result "bpppath-subset-bpp-with-sat-oracle" where
  title := "BPPpath is contained in bounded-error polynomial time with a SAT oracle"
  topic := "randomized complexity"
  sources := [
    { paper := HanHemaspaandraThierauf1997, theorem := "Theorem 3.11(2)",
      locator := "September 1995 revision, approximate-counting argument before Definition 3.8" }
  ]
  theorems := [Cslib.Complexity.BPPpath_subset_BPOp_PWithOracle_SAT]
  scope := "The verifier-count model uses two #P counts with positive sum. The accepting \
    fraction is at least \
    3/4 on members and at most 1/4 on nonmembers. Independent estimates yield a bounded-error \
    decision procedure with the encoded NP-complete SAT language as its oracle. The paper \
    presents BPPpath using nondeterministic machines with variable path lengths."
