/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.CBCMAC
public import CslibFrontier.Crypto.Primitives.UHF.PrefixFreePRF
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Tactic.Negligible

/-!
# Computational universal hashing from CBC-MAC

This proves the CBC-MAC case of [BonehShoup2023], v0.6, Corollary 7.5 (printed p. 260).
The collision game includes the empty word. The prefix-free wrapper appends one block before
querying the CBC oracle, so its queries are in the nonempty CBC domain. Composing the batch
wrapper with the CBC-to-PRF reduction gives an explicit distinguisher and a birthday bound.
The single-pair bound applies it to a two-message batch. The cascade application also depends
on the Chapter 6 construction and security proof in #5801.

## Main definitions

* `Cslib.Crypto.UHF.cbcMacMultiQueryReduction`: the composed base-PRF distinguisher.

## Main results

* `Cslib.Crypto.PseudorandomFunction.isMultiQueryUHF_cbcMac`: asymptotic multi-query UHF security.
* `Cslib.Crypto.PseudorandomFunction.isComputationalUHF_cbcMac`: asymptotic single-pair security.
* `Cslib.Crypto.UHF.isOraclePPT_cbcMacMultiQueryReduction`: strict oracle PPT for the composition.
* `Cslib.Crypto.UHF.succProbability_multiQueryGame_cbcMac_le`: the concrete CBC comparison,
  using the library's Theorem 6.3 error term and the exact pair count from Theorem 7.4.
* `Cslib.Crypto.UHF.succProbability_collisionGame_cbcMac_le`: the two-message specialization.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

private theorem lpBlockValid_spec {ℓ : ℕ → ℕ} {n : ℕ} {word : List Bool}
    (hw : lpBlockValid ℓ n word = true) : n ∣ word.length ∧ word.length ≤ ℓ n * n := by
  simp only [lpBlockValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
  exact ⟨Nat.dvd_of_mod_eq_zero hw.1, hw.2⟩

private theorem lpBlockValid_blockCount_le {ℓ : ℕ → ℕ} {n : ℕ} {word : List Bool}
    (hw : lpBlockValid ℓ n word = true) : word.length / n ≤ ℓ n :=
  Nat.div_le_of_le_mul (by simpa only [Nat.mul_comm] using (lpBlockValid_spec hw).2)

private theorem cbcBlockValid_append_of_lpBlockValid {ℓ : ℕ → ℕ} {n : ℕ}
    {word block : List Bool} (hn : 0 < n) (hw : lpBlockValid ℓ n word = true)
    (hBlock : block.length = n) : cbcBlockValid (fun k => ℓ k + 1) n (word ++ block) = true := by
  obtain ⟨halign, hcap⟩ := lpBlockValid_spec hw
  simp only [cbcBlockValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.length_append, hBlock, Nat.add_mul, one_mul]
  refine ⟨⟨Nat.lt_of_lt_of_le hn (Nat.le_add_left _ _), ?_⟩, Nat.add_le_add_right hcap _⟩
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd halign, Nat.mod_self, Nat.zero_add, Nat.zero_mod]

private theorem cbcMacFamily_extend_of_lpBlockValid (family : List Bool → List Bool → List Bool)
    {ℓ : ℕ → ℕ} {n : ℕ} {key left right block : List Bool} (hn : 0 < n)
    (hKey : key.length = n) (hLeft : lpBlockValid ℓ n left = true)
    (hRight : lpBlockValid ℓ n right = true) (hBlock : block.length = n)
    (hEq : cbcMacFamily family key left = cbcMacFamily family key right) :
    cbcMacFamily family key (left ++ block) = cbcMacFamily family key (right ++ block) := by
  simp only [cbcMacFamily, hKey] at hEq ⊢
  rw [cbcMacWord_append_block family hn key (lpBlockValid_spec hLeft).1 hBlock,
    cbcMacWord_append_block family hn key (lpBlockValid_spec hRight).1 hBlock, hEq]

namespace UHF

/-- Compose the prefix-free batch collision wrapper with the base-PRF reduction for CBC-MAC
on the domain with one extra block. -/
@[expose]
def cbcMacMultiQueryReduction (ℓ Q : ℕ → ℕ)
    (guessBatch : ℕ × ℕ → ProbComp (List (List Bool))) : OracleDistinguisher :=
  cbcMacToPrfDistinguisher (fun n => ℓ n + 1)
    (prefixFreeBatchReduction id id Q (lpBlockValid ℓ) guessBatch)

/-- The composed CBC-MAC distinguisher is strict oracle PPT whenever the guesser is strict
PPT and the block and query caps are polynomial-time computable in unary. -/
theorem isOraclePPT_cbcMacMultiQueryReduction {ℓ Q : ℕ → ℕ}
    {guessBatch : ℕ × ℕ → ProbComp (List (List Bool))}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hGuess : IsPPTOn (encPair encUnary encUnary) (encList encBits) guessBatch) :
    IsOraclePPT encBool (cbcMacMultiQueryReduction ℓ Q guessBatch) :=
  isOraclePPT_cbcMacToPrfDistinguisher (hℓ.unary_add' (ComputableInPolyTime.const 1))
    (isOraclePPT_prefixFreeBatchReduction ComputableInPolyTime.id' ComputableInPolyTime.id'
      hQ (computableInPolyTime_lpBlockValid hℓ) hGuess)

/-- The concrete CBC-MAC bound from [BonehShoup2023], v0.6, Corollary 7.5 (printed p. 260).
The CBC term is `Q² * (ℓ + 1)² / (2 * 2^n)` as in (7.10). For the reply collisions,
the bound uses the exact pair count `Q.choose 2` from (7.9). At parameter zero the only valid
word is empty. If the block alphabet is too small for fresh-block search at positive width,
the CBC term already bounds the probability by one. -/
theorem succProbability_multiQueryGame_cbcMac_le
    {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query : List Bool, query.length = key.length →
      (family key query).length = key.length)
    (ℓ Q : ℕ → ℕ) (guessBatch : ℕ × ℕ → ProbComp (List (List Bool))) {n : ℕ}
    (hBudget : ∀ guesses ∈ (ProbComp.eval (guessBatch (n, n))).support, guesses.length ≤ Q n) :
    Game.succProbability (multiQueryGame pure (fun _ d => lpBlockValid ℓ d)
      (fun _ d (key : BitString d) => cbcMacFamily family (List.ofFn key)) guessBatch n) ≤
    Game.advantage
      (ProbComp.eval (prfRealGame id family (cbcMacMultiQueryReduction ℓ Q guessBatch) n))
      (ProbComp.eval (prfIdealGame id id (cbcMacMultiQueryReduction ℓ Q guessBatch) n)) +
      (Q n : ℝ≥0) ^ 2 * (ℓ n + 1 : ℝ≥0) ^ 2 / (2 * 2 ^ n) + (Q n).choose 2 / (2 : ℝ≥0) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hEmpty {word : List Bool} (hw : lpBlockValid ℓ 0 word = true) : word = [] := by
      simpa using (lpBlockValid_spec hw).2
    have hNoCollision (guesses : List (List Bool)) (key : BitString 0) :
        ¬ ∃ u ∈ guesses, ∃ v ∈ guesses, u ≠ v ∧ lpBlockValid ℓ 0 u = true ∧
          lpBlockValid ℓ 0 v = true ∧
          cbcMacFamily family (List.ofFn key) u = cbcMacFamily family (List.ofFn key) v :=
      fun ⟨_, _, _, _, hne, hu, hv, _⟩ => hne ((hEmpty hu).trans (hEmpty hv).symm)
    simp only [multiQueryGame, Game.withSetup_pure, ProbComp.eval_pure, ProbComp.eval_bind,
      hNoCollision, decide_false, PMF.bind_const]
    simp [Game.succProbability]
  by_cases hSmallAlphabet : 2 ^ n ≤ ℓ n * Q n
  · have hNat : 2 ^ n ≤ Q n * (ℓ n + 1) := hSmallAlphabet.trans
      (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (Q n) (Nat.le_succ (ℓ n)))
    have hSize : (2 : ℝ≥0) ^ n ≤ (Q n : ℝ≥0) * (ℓ n + 1 : ℝ≥0) := by exact_mod_cast hNat
    have hTwo : (2 : ℝ≥0) ≤ 2 ^ n := le_self_pow₀ one_le_two hn.ne'
    have hCBC : (1 : ℝ≥0) ≤ (Q n : ℝ≥0) ^ 2 * (ℓ n + 1 : ℝ≥0) ^ 2 / (2 * 2 ^ n) := by
      rw [le_div_iff₀ (by positivity), one_mul, ← mul_pow, pow_two]
      exact mul_le_mul (hTwo.trans hSize) hSize (by positivity) (by positivity)
    refine (Game.succProbability_le_one _).trans (hCBC.trans ?_)
    exact (le_add_of_nonneg_left zero_le).trans (le_add_of_nonneg_right zero_le)
  let batch := prefixFreeBatchReduction id id Q (lpBlockValid ℓ) guessBatch
  have hBatch := succProbability_multiQueryGame_le_prefixFreeBatchReduction
    (width := id) (outLen := id) (cbcMacFamily family) guessBatch n (ℓ n) hBudget
    (fun _ hw => lpBlockValid_blockCount_le hw) (Nat.lt_of_not_ge hSmallAlphabet)
    (cbcBlockValid_append_of_lpBlockValid hn) (cbcMacFamily_extend_of_lpBlockValid family hn)
  have hCBC := advantage_cbcMac_le hlen (fun k => ℓ k + 1) batch
    (isQueryBounded_prefixFreeBatchReduction id id Q (lpBlockValid ℓ) guessBatch n [])
    (isPrefixFreeOn_prefixFreeBatchReduction guessBatch n n
      (fun _ hw => ⟨hn, (lpBlockValid_spec hw).1⟩))
  refine hBatch.trans (add_le_add ?_ le_rfl)
  simpa only [cbcMacMultiQueryReduction, batch, Nat.cast_add, Nat.cast_one] using hCBC

/-- The single-pair CBC-MAC bound from [BonehShoup2023], v0.6, Corollary 7.5 (printed p. 260).
The collision guess is presented to the multi-query reduction as a batch with `Q = 2`. -/
theorem succProbability_collisionGame_cbcMac_le
    {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query : List Bool, query.length = key.length →
      (family key query).length = key.length)
    (ℓ : ℕ → ℕ) (guess : ℕ × ℕ → ProbComp (CollisionGuess (List Bool))) (n : ℕ) :
    let reduction := cbcMacMultiQueryReduction ℓ (fun _ => 2)
      (fun p => collisionPairToBatch (guess p))
    Game.succProbability (collisionGame pure (fun _ d => lpBlockValid ℓ d)
      (fun _ d (key : BitString d) => cbcMacFamily family (List.ofFn key)) guess n) ≤
    Game.advantage
      (ProbComp.eval (prfRealGame id family reduction n))
      (ProbComp.eval (prfIdealGame id id reduction n)) +
      (2 : ℝ≥0) ^ 2 * (ℓ n + 1 : ℝ≥0) ^ 2 / (2 * 2 ^ n) + 1 / (2 : ℝ≥0) ^ n := by
  simpa only [multiQueryGame_collisionPairToBatch, Nat.choose_self,
    Nat.cast_one, Nat.cast_ofNat] using
    succProbability_multiQueryGame_cbcMac_le hlen ℓ (fun _ => 2)
      (fun p => collisionPairToBatch (guess p)) (n := n)
      (fun _ hm => (length_of_mem_support_collisionPairToBatch hm).le)

end UHF

/-- The CBC-MAC case of [BonehShoup2023], v0.6, Corollary 7.5 (printed p. 260), for batches.
CBC-MAC on zero to `ℓ n` whole blocks is a multi-query UHF under a length-preserving secure
PRF. The word model uses uniform `n`-bit keys and a unary polynomial-time block cap.
The cascade case depends on #5801. -/
theorem PseudorandomFunction.isMultiQueryUHF_cbcMac
    {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family)
    {ℓ : ℕ → ℕ} (hℓ : ComputableInPolyTime ℓ encUnary encUnary) :
    UHF.IsMultiQueryUHF encUnary encBits pure (fun _ d => lpBlockValid ℓ d)
      (fun _ d (key : BitString d) => cbcMacFamily family (List.ofFn key)) := by
  apply Game.Indistinguishable.of_negligible_succProbability
  intro guessBatch hGuess
  obtain ⟨Q, hQ, hBudget⟩ := UHF.exists_computableInPolyTime_batchQueryCap hGuess
  have hBase := hF.secure _ (UHF.isOraclePPT_cbcMacMultiQueryReduction hℓ hQ hGuess)
  negligible using fun n =>
    UHF.succProbability_multiQueryGame_cbcMac_le hF.length_eq ℓ Q guessBatch (hBudget n)

/-- The CBC-MAC case of [BonehShoup2023], v0.6, Corollary 7.5 (printed p. 260), for
single-pair adversaries. A secure length-preserving PRF gives a computational UHF on zero to
`ℓ n` whole blocks, with uniform `n`-bit keys and a unary polynomial-time block cap. -/
theorem PseudorandomFunction.isComputationalUHF_cbcMac
    {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family)
    {ℓ : ℕ → ℕ} (hℓ : ComputableInPolyTime ℓ encUnary encUnary) :
    UHF.IsComputationalUHF encUnary encBits pure (fun _ d => lpBlockValid ℓ d)
      (fun _ d (key : BitString d) => cbcMacFamily family (List.ofFn key)) :=
  (hF.isMultiQueryUHF_cbcMac hℓ).isComputationalUHF

end Cslib.Crypto
