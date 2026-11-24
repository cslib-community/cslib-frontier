/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade
public import CslibFrontier.Crypto.Computational.PseudorandomFunction.PrefixHybrid
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Probabilistic.PPT.Composition

/-!
# Prefix hybrids for the word cascade

This is the endpoint step for the cascade proof of [BonehShoup2023], v0.6, Section 6.4.2
(printed pp. 229–230), which carries over the variable-length tree hybrids from
Section 4.6.1 (printed pp. 152–153). At block depth `d`, sample a uniform key for each distinct
prefix of at most `d` blocks and evaluate the remaining suffix using the cascade. Short queries are
their own frontier prefixes, so a cut covering the domain is the random-function oracle
even when valid queries can have different lengths. The adjacent-hybrid reduction requires
prefix-free admissibility and is separate.

For the source's admissible queries (Definition 4.5), choose `valid n` to accept encodings of
one through `ℓ` blocks from the input alphabet. The endpoint laws also hold when the predicate
allows the empty word. Invalid queries receive `[]`.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- Run a cascade prefix hybrid. The level counts whole blocks; the shared word hybrid
cuts after `depth * inLen n` bits. -/
@[expose]
noncomputable def cascadePrefixHybridGame (valid : ℕ → List Bool → Bool)
    (inLen : ℕ → ℕ) (family : List Bool → List Bool → List Bool)
    (adversary : OracleDistinguisher) (n depth : ℕ) : ProbComp Bool :=
  prefixHybridGame valid (cascadeFamily inLen family) adversary n (depth * inLen n)

/-- At depth zero the suffix is the entire query and the shared root is the real key. -/
theorem eval_cascadePrefixHybridGame_zero (valid : ℕ → List Bool → Bool)
    (inLen : ℕ → ℕ) (family : List Bool → List Bool → List Bool)
    (adversary : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (cascadePrefixHybridGame valid inLen family adversary n 0) =
      ProbComp.eval (prfRealGameOn valid (cascadeFamily inLen family) adversary n) := by
  simpa only [cascadePrefixHybridGame, Nat.zero_mul] using
    eval_prefixHybridGame_zero valid (cascadeFamily inLen family) adversary n

/-- If the cut covers every valid query then the labels are independent ideal oracle replies. -/
theorem eval_cascadePrefixHybridGame_eq_ideal {valid : ℕ → List Bool → Bool}
    {inLen : ℕ → ℕ} (family : List Bool → List Bool → List Bool)
    (adversary : OracleDistinguisher) {n depth : ℕ}
    (hcut : ∀ query, valid n query = true → query.length ≤ depth * inLen n) :
    ProbComp.eval (cascadePrefixHybridGame valid inLen family adversary n depth) =
      ProbComp.eval (prfIdealGameOn valid id adversary n) := by
  simp only [cascadePrefixHybridGame, prefixHybridGame, prfIdealGameOn, id_eq,
    prefixHybridOracle_eq_cachedRandomFunctionOracle hcut (cascadeFamily_nil inLen family)]

/-- Certify the complete word-cascade hybrid against a strict oracle-PPT adversary. The evaluator,
block width and validity test are polynomial-time computable, and the base evaluator preserves the
key width on valid blocks. The parameter and depth are unary and the certificate charges the
encoded prefix cache. -/
theorem isPPTOn_cascadePrefixHybridGame {valid : ℕ → List Bool → Bool}
    {inLen : ℕ → ℕ} {family : List Bool → List Bool → List Bool}
    {adversary : OracleDistinguisher}
    (hValid : ComputableInPolyTime (fun p : ℕ × List Bool => valid p.1 p.2)
      (encPair encUnary encBits) encBool)
    (hIn : ComputableInPolyTime inLen encUnary encUnary)
    (hLen : ∀ key block, block.length = inLen key.length → (family key block).length = key.length)
    (hEval : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits)
    (hAdversary : IsOraclePPT encBool adversary) :
    IsPPTOn (encPair encUnary encUnary) encBool
      (fun p => cascadePrefixHybridGame valid inLen family adversary p.1 p.2) := by
  have hGame := isPPTOn_prefixHybridGame hValid (computableInPolyTime_cascadeFamily hIn hLen hEval)
    (fun seed suffix => (length_cascadeFamily hLen seed suffix).le) hAdversary
  exact hGame.preprocess (show ComputableInPolyTime (fun p : ℕ × ℕ => (p.1, p.2 * inLen p.1))
    (encPair encUnary encUnary) (encPair encUnary encUnary) by fun_prop)

end Cslib.Crypto
