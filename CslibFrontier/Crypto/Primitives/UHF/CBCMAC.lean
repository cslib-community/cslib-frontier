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
import CslibFrontier.Crypto.Negligible.Dyadic

/-!
# Computational multi-query universal hashing from CBC-MAC

This is the CBC-MAC step toward [BonehShoup2023], v0.6, Corollary 7.5 (printed p. 260).
The collision game includes the empty word. The prefix-free wrapper appends one block before
querying the CBC oracle, so its queries are in the nonempty CBC domain. Composing the batch
wrapper with the CBC-to-PRF reduction gives an explicit distinguisher and a birthday bound.

## Main definitions

* `Cslib.Crypto.UHF.cbcMacMultiQueryReduction`: the composed base-PRF distinguisher.

## Main results

* `Cslib.Crypto.PseudorandomFunction.isMultiQueryUHF_cbcMac`: asymptotic multi-query UHF security.
* `Cslib.Crypto.UHF.succProbability_multiQueryGame_cbcMac_le`: the concrete CBC comparison,
  using the library's Theorem 6.3 error term and the exact pair count from Theorem 7.4.
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

/-- CBC-MAC on zero to `ℓ n` whole blocks is a multi-query UHF under a length-preserving
secure PRF, the CBC part of [BonehShoup2023], v0.6, Corollary 7.5 (printed p. 260).
The word model uses uniform `n`-bit keys and a unary polynomial-time block cap. For positive
`n`, appending a block puts each hash word in the nonempty CBC oracle domain of at most
`ℓ n + 1` blocks. The proof uses this reduction for `n ≥ 1`, which suffices for negligibility. -/
theorem PseudorandomFunction.isMultiQueryUHF_cbcMac
    {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family)
    {ℓ : ℕ → ℕ} (hℓ : ComputableInPolyTime ℓ encUnary encUnary) :
    UHF.IsMultiQueryUHF encUnary encBits pure (fun _ d => lpBlockValid ℓ d)
      (fun _ d (key : BitString d) => cbcMacFamily family (List.ofFn key)) := by
  let valid (n : ℕ) (word : List Bool) := decide (0 < n) && lpBlockValid ℓ n word
  have hValid : ComputableInPolyTime (fun p => valid p.1 p.2)
      (encPair encUnary encBits) encBool :=
    ComputableInPolyTime.bool_and'
      ((ComputableInPolyTime.const 0).unary_lt' (ComputableInPolyTime.fst encUnary encBits))
      (computableInPolyTime_lpBlockValid hℓ)
  have hValidSpec {n : ℕ} {word : List Bool} (hw : valid n word = true) :
      0 < n ∧ lpBlockValid ℓ n word = true := by
    simpa only [valid, Bool.and_eq_true, decide_eq_true_eq] using hw
  have hPRF := hF.prefixFreePRF_cbcMac (hℓ.unary_add' (ComputableInPolyTime.const 1))
  have hProbe : ∀ᶠ n in Filter.atTop,
      cbcBlockValid (fun k => ℓ k + 1) n (List.replicate n false) = true := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    have hEmpty : lpBlockValid ℓ n [] = true := by simp [lpBlockValid]
    simpa only [List.nil_append] using
      cbcBlockValid_append_of_lpBlockValid hn hEmpty (List.length_replicate (a := false))
  have hGuarded := UHF.isMultiQueryUHF_of_extendable_prefixFreePRF
    (maxBlocks := ℓ) hPRF ComputableInPolyTime.id' hValid
    (fun _ _ hw => ⟨(hValidSpec hw).1, (lpBlockValid_spec (hValidSpec hw).2).1⟩)
    (fun _ _ hw => lpBlockValid_blockCount_le (hValidSpec hw).2) hℓ.polynomiallyBounded
    (fun hw hb => cbcBlockValid_append_of_lpBlockValid (hValidSpec hw).1 (hValidSpec hw).2 hb)
    hProbe (fun hk hl hr hb => cbcMacFamily_extend_of_lpBlockValid family
      (hValidSpec hl).1 hk (hValidSpec hl).2 (hValidSpec hr).2 hb)
    negligible_inv_two_pow negligible_inv_two_pow
  apply Game.Indistinguishable.of_negligible_succProbability
  intro guessBatch hGuess
  apply negligible_of_eventually_le (hGuarded.negligible_succProbability guessBatch hGuess)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hvalidEq : valid n = lpBlockValid ℓ n := by
    funext word
    simp only [valid, decide_eq_true (show 0 < n from hn), Bool.true_and]
  simp only [UHF.multiQueryGame, ProbComp.eval_pure, Game.withSetup_pure, hvalidEq]
  exact le_rfl

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

/-- Concrete CBC-MAC instance of [BonehShoup2023], v0.6, Corollary 7.5 (printed p. 260),
combining the library's Theorem 6.3 bound with (7.9). The length-preserving base PRF
contributes the error `Q² * (ℓ + 1)² / 2^n`, twice the corresponding term in (7.10).
The batch comparison contributes the sharper birthday term `Q.choose 2 / 2^n`.
As in Theorem 7.4, the block alphabet must exceed the largest batch's block count. -/
theorem succProbability_multiQueryGame_cbcMac_le
    {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query : List Bool, query.length = key.length →
      (family key query).length = key.length)
    (ℓ Q : ℕ → ℕ) (guessBatch : ℕ × ℕ → ProbComp (List (List Bool))) {n : ℕ} (hn : 0 < n)
    (hBudget : ∀ guesses ∈ (ProbComp.eval (guessBatch (n, n))).support, guesses.length ≤ Q n)
    (hAlphabet : ℓ n * Q n < 2 ^ n) :
    Game.succProbability (multiQueryGame pure (fun _ d => lpBlockValid ℓ d)
      (fun _ d (key : BitString d) => cbcMacFamily family (List.ofFn key)) guessBatch n) ≤
    Game.advantage
      (ProbComp.eval (prfRealGame id family (cbcMacMultiQueryReduction ℓ Q guessBatch) n))
      (ProbComp.eval (prfIdealGame id id (cbcMacMultiQueryReduction ℓ Q guessBatch) n)) +
      (Q n : ℝ≥0) ^ 2 * (ℓ n + 1 : ℝ≥0) ^ 2 / 2 ^ n + (Q n).choose 2 / (2 : ℝ≥0) ^ n := by
  let batch := prefixFreeBatchReduction id id Q (lpBlockValid ℓ) guessBatch
  have hBatch := succProbability_multiQueryGame_le_prefixFreeBatchReduction
    (width := id) (outLen := id) (cbcMacFamily family) guessBatch n (ℓ n) hBudget
    (fun _ hw => lpBlockValid_blockCount_le hw) hAlphabet
    (cbcBlockValid_append_of_lpBlockValid hn) (cbcMacFamily_extend_of_lpBlockValid family hn)
  have hCBC := advantage_cbcMac_le hlen (fun k => ℓ k + 1) batch
    (isQueryBounded_prefixFreeBatchReduction id id Q (lpBlockValid ℓ) guessBatch n [])
    (isPrefixFreeOn_prefixFreeBatchReduction guessBatch n n
      (fun _ hw => ⟨hn, (lpBlockValid_spec hw).1⟩))
  refine hBatch.trans (add_le_add ?_ le_rfl)
  simpa only [cbcMacMultiQueryReduction, batch, Nat.cast_add, Nat.cast_one] using hCBC

end UHF

end Cslib.Crypto
