/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Circuit.Boolean.MajorityNonlinear

/-!
# Collected results: multiplicative complexity of majority
-/

register_result "chistopolskaya-podolskii-majority-multiplicative-complexity" where
  title := "Majority on n inputs has multiplicative complexity at least n - B(n), where B(n) is \
    the binary digit sum of n"
  topic := "circuit complexity"
  sources := [
    { paper := ChistopolskayaPodolskii2018,
      theorem := "Corollary 11",
      locator := "ECCC TR18-174 revision 2, §4, printed p. 12; multiplicative complexity is \
        defined in §2.3" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.Zhegalkin.sub_sum_digits_le_multiplicativeComplexity_majority
  ]
  scope := "This entry covers Corollary 11 only. For every input count n, \
    n - (Nat.digits 2 n).sum ≤ Zhegalkin.multiplicativeComplexity (single (majority n)), the \
    least number of conjunction gates in a circuit over the native basis {⊕, ∧, 1} whose single \
    output is majority on every Boolean input, with depth, fanout and the number of ⊕ gates \
    unrestricted. The source counts AND gates in fan-in-two circuits over {AND, XOR, NOT}. The \
    native basis has a free constant 1 in place of NOT: NOT is XOR with 1, and for positive n \
    the constant 1 is NOT (x XOR x) at no AND cost, so the two minima agree; n = 0 is a trivial \
    extension. majority n accepts ties (threshold (n + 1) / 2), as the source's MAJ_n does, and \
    the source's output -1 is Lean's true. The parity decision-tree statements (Lemma 5, \
    Theorem 6, Theorem 10) and a matching upper bound are not asserted. The proof does not \
    follow the source's decision-tree route: it uses a denominator invariant for circuits over \
    any Boolean basis of fan-in at most two, charging only nonaffine gates \
    (Circuit.exists_fourierCoeff_signVal_eval_eq_intCast_div_two_pow_nonlinearCost). That \
    invariant and its majority form \
    Circuit.sub_sum_digits_le_nonlinearCost_of_eval_eq_majority are a generalization beyond \
    the source's basis and are not listed here as source statements. Outside-fleet agent source \
    check (reviewer-codex-edemaine): \
    https://github.com/cslib-community/cslib-frontier/pull/7936#pullrequestreview-6022710102"
