/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.AdjacentPRF
public import CslibFrontier.Crypto.Primitives.UHF.PrefixFreePRF
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Crypto.Negligible.Dyadic

/-!
# Cascade as a multi-query universal hash

Appending one fresh block to each candidate hash input gives a prefix-free batch
and preserves every collision. The cascade reduction then compares that batch against
the base PRF. The loss is the query budget times the extended block cap, plus the
ideal birthday term.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

private theorem cascade_collision_extend
    {width : ℕ → ℕ} {family : List Bool → List Bool → List Bool}
    (hLen : ∀ key block, block.length = width key.length → (family key block).length = key.length)
    {key left right block : List Bool} (hWidth : 0 < width key.length)
    (hLeft : width key.length ∣ left.length) (hRight : width key.length ∣ right.length)
    (hBlock : block.length = width key.length)
    (hEq : cascadeFamily width family key left = cascadeFamily width family key right) :
    cascadeFamily width family key (left ++ block) = cascadeFamily width family key
      (right ++ block) := by
  have hab : width key.length ∣ block.length := by simp only [hBlock, dvd_refl]
  rw [cascadeFamily_append hLen key hWidth hLeft hab, cascadeFamily_append hLen key hWidth
    hRight hab, hEq]

/-- The multi-query cascade conclusion of [BonehShoup2023], v0.6, Corollary 7.5
(printed p. 260). The word predicates describe the hash domain of at most `hops n`
blocks and the PRF domain with one extra block. The reciprocal of the block alphabet
size is negligible. Hash inputs use positive-width blocks, the extended domain
eventually admits the all-zero block, and the keys and digests are `n` bits. -/
theorem PseudorandomFunctionOver.isMultiQueryUHF_cascade
    {width hops : ℕ → ℕ} {valid oracleValid : ℕ → List Bool → Bool}
    {family : List Bool → List Bool → List Bool}
    (hF : PseudorandomFunctionOver width id family)
    (hIn : ComputableInPolyTime width encUnary encUnary)
    (hHops : ComputableInPolyTime hops encUnary encUnary)
    (hValid : ComputableInPolyTime (fun p : ℕ × List Bool => valid p.1 p.2)
      (encPair encUnary encBits) encBool)
    (hOracleValid : ComputableInPolyTime (fun p : ℕ × List Bool => oracleValid p.1 p.2)
      (encPair encUnary encBits) encBool)
    (hAligned : ∀ n word, valid n word = true → 0 < width n ∧ width n ∣ word.length)
    (hBlocks : ∀ n word, valid n word = true → word.length ≤ hops n * width n)
    (hOracleAligned : ∀ n word, oracleValid n word = true → width n ∣ word.length)
    (hOracleBlocks : ∀ n word, oracleValid n word = true → word.length ≤ (hops n + 1) * width n)
    (hDomain : ∀ {n word block}, valid n word = true → block.length = width n →
      oracleValid n (word ++ block) = true)
    (hProbe : ∀ᶠ n in Filter.atTop, oracleValid n (List.replicate (width n) false) = true)
    (hAlphabet : Negligible (fun n => ((2 : ℝ≥0) ^ width n)⁻¹)) :
    UHF.IsMultiQueryUHF encUnary encBits pure (fun _ d => valid d)
      (fun _ d (key : BitString d) => cascadeFamily width family (List.ofFn key)) := by
  have hWidth : ∀ᶠ n in Filter.atTop, 0 < width n := by
    filter_upwards [(hAlphabet 0).eventually_lt_const zero_lt_one] with n hn
    by_contra! h
    simp [Nat.eq_zero_of_le_zero h] at hn
  have hPRF := hF.prefixFree_cascade hOracleValid hIn
    (hHops.unary_add' (.const 1)) hWidth hOracleAligned hOracleBlocks
  refine UHF.isMultiQueryUHF_of_extendable_prefixFreePRF hPRF hIn hValid hAligned
    (fun n word hw => Nat.div_le_of_le_mul (by simpa only [Nat.mul_comm] using hBlocks n word hw))
    hHops.polynomiallyBounded hDomain hProbe ?_ hAlphabet negligible_inv_two_pow
  intro n key left right block hk hl hr hb heq
  obtain ⟨hw, hleft⟩ := hAligned n left hl
  exact cascade_collision_extend hF.length_eq (by simpa only [hk] using hw)
    (by simpa only [hk] using hleft) (by simpa only [hk] using (hAligned n right hr).2)
    (by simpa only [hk] using hb) heq

namespace UHF

/-- The concrete cascade bound of [BonehShoup2023], v0.6, Corollary 7.5, equation
(7.11) (printed p. 260), at a specified security parameter. The two predicates describe
the smaller hash domain and the oracle domain with one extra block, using aligned bit
words. The block alphabet must have room for a block absent from the batch as in
Theorem 7.4. The base advantage is for the ordinary one-block PRF game, as in the
application of (6.15). The birthday term retains the number of unordered pairs, `Q.choose 2`. -/
theorem succProbability_multiQueryGame_cascade_le_pointwise
    {width : ℕ → ℕ} {valid oracleValid : ℕ → List Bool → Bool}
    {family : List Bool → List Bool → List Bool}
    (guessBatch : ℕ × ℕ → ProbComp (List (List Bool))) (n ℓ Q : ℕ)
    (hIn : ComputableInPolyTime width encUnary encUnary)
    (hValid : ComputableInPolyTime (fun p : ℕ × List Bool => valid p.1 p.2)
      (encPair encUnary encBits) encBool)
    (hOracleValid : ComputableInPolyTime (fun p : ℕ × List Bool => oracleValid p.1 p.2)
      (encPair encUnary encBits) encBool)
    (hLen : ∀ key block, block.length = width key.length → (family key block).length = key.length)
    (hEval : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits)
    (hGuess : IsPPTOn (encPair encUnary encUnary) (encList encBits) guessBatch)
    (hWidth : 0 < width n)
    (hAligned : ∀ word, valid n word = true → width n ∣ word.length)
    (hBlocks : ∀ word, valid n word = true → word.length ≤ ℓ * width n)
    (hOracleAligned : ∀ word, oracleValid n word = true → width n ∣ word.length)
    (hOracleBlocks : ∀ word, oracleValid n word = true → word.length ≤ (ℓ + 1) * width n)
    (hAlphabet : ℓ * Q < 2 ^ width n)
    (hDomain : ∀ {word block}, valid n word = true → block.length = width n →
      oracleValid n (word ++ block) = true)
    (hBudget : ∀ guesses ∈ (ProbComp.eval (guessBatch (n, n))).support, guesses.length ≤ Q) :
    ∃ reduction : OracleDistinguisher, IsOraclePPT encBool reduction ∧
      (reduction n []).IsQueryBounded Q ∧
      Game.succProbability (multiQueryGame pure (fun _ d => valid d)
        (fun _ d (key : BitString d) => cascadeFamily width family (List.ofFn key)) guessBatch n) ≤
      (Q * (ℓ + 1) : ℕ) * Game.advantage
        (ProbComp.eval (prfRealGame width family reduction n))
        (ProbComp.eval (prfIdealGame width id reduction n)) + Q.choose 2 / (2 : ℝ≥0) ^ n := by
  have hExtend {key left right block : List Bool} (hk : key.length = n)
      (hl : valid n left = true) (hr : valid n right = true) (hb : block.length = width n)
      (heq : cascadeFamily width family key left = cascadeFamily width family key right) :
      cascadeFamily width family key (left ++ block) =
        cascadeFamily width family key (right ++ block) := by
    have hw : 0 < width key.length := by simpa only [hk] using hWidth
    have hal : width key.length ∣ left.length := by simpa only [hk] using hAligned left hl
    have har : width key.length ∣ right.length := by simpa only [hk] using hAligned right hr
    exact cascade_collision_extend hLen hw hal har (by simpa only [hk] using hb) heq
  let batch := prefixFreeBatchReduction width id (fun _ => Q) valid guessBatch
  have hCollision := succProbability_multiQueryGame_le_prefixFreeBatchReduction
    (width := width) (outLen := id) (Q := fun _ => Q) (valid := valid)
    (oracleValid := oracleValid) (cascadeFamily width family) guessBatch n ℓ hBudget
    (fun word hw => Nat.div_le_of_le_mul (by simpa only [Nat.mul_comm] using hBlocks word hw))
    hAlphabet hDomain hExtend
  obtain ⟨reduction, hppt, hqueries, hCascade⟩ := advantage_cascade_le_pointwise
    (valid := oracleValid) (adversary := batch) n (ℓ + 1) Q hOracleValid hIn hWidth
    hOracleAligned hOracleBlocks hLen hEval
    (isOraclePPT_prefixFreeBatchReduction hIn .id' (.const Q) hValid hGuess)
    (isPrefixFreeOn_prefixFreeBatchReduction guessBatch n n
      (fun word hw => ⟨hWidth, hAligned word hw⟩))
    (isQueryBounded_prefixFreeBatchReduction width id (fun _ => Q) valid guessBatch n [])
  refine ⟨reduction, hppt, hqueries, hCollision.trans (add_le_add ?_ le_rfl)⟩
  simpa only [Nat.mul_comm (ℓ + 1) Q] using hCascade

end UHF

end Cslib.Crypto
