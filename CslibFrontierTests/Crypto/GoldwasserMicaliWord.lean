/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Crypto.Computational.Encryption.Bitwise
import CslibFrontier.Crypto.Computational.Encryption.PublicKeyCPA
import CslibFrontier.Crypto.Computational.GoldwasserMicali
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Languages.Probabilistic.BitString
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Tactic.PolyTime
import Mathlib.NumberTheory.LSeries.WeakPNT
import Mathlib.Tactic.NormNum.Prime

/-!
# Module Client Tests for Multi-Bit Blum Goldwasser–Micali and Bitwise PKE

Ordinary-import `module` client tests for `CslibFrontier.Crypto.Computational.Encryption.Bitwise`
and the multi-bit Blum-modulus API of `CslibFrontier.Crypto.Computational.GoldwasserMicali`:

* concrete evaluation and support-level round-trip correctness of `(blumKeyGen, encryptWord,
  decryptWord)` at `N = 21 = 3 * 7`, plus `computableInPolyTime_decryptWord` and
  `length_blumPublicKey_le`;
* coordinate hybrid endpoints (`eval_bitwiseHybridGameOn_zero`, `eval_bitwiseHybridGameOn_of_le`),
  the non-vanishing exact advantage identity `advantage_bitwiseEncrypt_eq` (`1 = 4 * (1 / 4)` at
  `maxLen = 2`), strict-PPT certification (`isPPT_bitwiseToSingleAt`, `isPPT_bitwiseToSingle`),
  boundary witnesses (`bitwise_boundary_witnesses`), refutation of `WordINDCPA` on a
  plaintext-leaking 1-bit scheme, and necessity of polynomially bounded public-key length for
  `INDCPA → WordINDCPA` (`indcpa_and_not_wordINDCPA_expKeyGen`);
* client instantiations of `wordINDCPA_blumGoldwasserMicali` (and its lift to `WordINDCPAOracle`),
  plus `INDCPA.wordINDCPA_bitwiseEncrypt` when `gen` is uniform strict PPT;
* joint satisfiability of `hblum`, `hsize`, `PolynomiallyBounded sizeBound`, and `hupper` at every
  `n : ℕ` via the prime number theorem for `p ≡ 3 (mod 4)`
  (`Chebyshev.tendsto_sum_log_prime_modEq_div_atTop`), leaving `QuadraticResiduosityHard` as the
  sole hypothesis of `wordINDCPA_blumGoldwasserMicali`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.GoldwasserMicaliWord

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Encryption Cslib.Crypto.GoldwasserMicali
open Turing.MultiTapeTM Filter Topology
open scoped NNReal ENNReal

/-! ### Word-level round-trip correctness and evaluation at `N = 21 = 3 * 7` -/

private def d21 : ModulusDesc := ⟨3, 7, by norm_num, by norm_num, by decide, by decide, by decide⟩

private theorem isBlumModulus_3_7 : IsBlumModulus 3 7 :=
  ⟨⟨by norm_num, by decide⟩, ⟨by norm_num, by decide⟩, by decide⟩

private noncomputable def constBlumGen : ℕ → ProbComp ModulusDesc := fun _ => pure d21

private theorem isBlum_constBlumGen (n : ℕ) :
    ∀ d ∈ (ProbComp.eval (constBlumGen n)).support, IsBlumModulus d.p d.q := by
  intro d hd
  simp only [constBlumGen, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hd
  exact hd ▸ isBlumModulus_3_7

/-- Concrete word decryption of a framed 3-bit Goldwasser–Micali ciphertext under `sk = ⟨3, 7⟩`. -/
theorem decryptWord_concrete_21 :
    decryptWord (encPair encNat encNat (3, 7))
      (encList encBits
        [encNat (ciphertext 21 20 true 5),
         encNat (ciphertext 21 20 false 5),
         encNat (ciphertext 21 20 true 11)]) = [true, false, true] := by
  simp only [decryptWord_encList, decryptBits, List.map_cons, List.map_nil, decrypt_encPair]
  decide

/-- Concrete check of `length_blumPublicKey_le` on `(3, 7)` (`3.size ≤ 3`, `7.size ≤ 3`). -/
theorem length_blumPublicKey_21_le : (blumPublicKey (3 * 7)).length ≤ 19 :=
  length_blumPublicKey_le (B := 3) (by decide) (by decide)

/-- Support-level round-trip correctness of `(blumKeyGen constBlumGen, encryptWord, decryptWord)` on
arbitrary bit words, together with polynomial-time word decryption. -/
theorem roundTrip_blumKeyGen_encryptWord (n : ℕ) (bits : List Bool)
    {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (blumKeyGen constBlumGen n)).support)
    {ct : List Bool} (hct : ct ∈ (ProbComp.eval (encryptWord n keys.1 bits)).support) :
    decryptWord keys.2 ct = bits ∧
      ComputableInPolyTime (fun ⟨sk, c⟩ => decryptWord sk c) (encPair encBits encBits) encBits :=
  ⟨decryptWord_encryptWord_blumKeyGen (isBlum_constBlumGen n) hkeys bits hct,
   computableInPolyTime_decryptWord⟩

/-! ### Coordinate hybrid identities and nonvacuity on a plaintext-leaking 1-bit scheme -/

private def emptyKeyGen (_ : ℕ) : ProbComp (List Bool × List Bool) := pure ([], [])
private def leakBitEncrypt (_ : ℕ) (_ : List Bool) (b : Bool) : ProbComp (List Bool) := pure [b]

private noncomputable def bothWordAdv : WordAdversary where
  choose _ _ := pure (([false, false], [true, true]), [])
  guess _ _ ct := pure (ct == encList encBits [[true], [true]])

private theorem isPPT_bothWordAdv : bothWordAdv.IsPPT where
  choose :=
    (ComputableInPolyTime.const
      ((([false, false], [true, true]), []) : ChoiceOut (List Bool))).isPPTOn
  guess := by
    have hconst : ComputableInPolyTime
        (fun _ : ℕ × List Bool × List Bool => encList encBits [[true], [true]])
        encGuessInput encBits :=
      ComputableInPolyTime.const (encList encBits [[true], [true]])
    have hct : ComputableInPolyTime (fun x : ℕ × List Bool × List Bool => x.2.2)
        encGuessInput encBits := by dsimp only [encGuessInput]; fun_prop
    exact (hct.beq hconst).isPPTOn

private theorem advantage_bothWordAdv (n : ℕ) :
    Encryption.advantage
      (gameOn (validBoundedWords fun _ => 2) emptyKeyGen (bitwiseEncrypt leakBitEncrypt)
        bothWordAdv) n = 1 := by
  simp [Encryption.advantage, gameOn, validBoundedWords, bitwiseEncrypt, emptyKeyGen,
    leakBitEncrypt, bothWordAdv, Game.advantage, Game.succProbability]

/-- Hybrid endpoints match `false` at `0` and `true` at `maxLen = 2`. -/
theorem leak_hybridEndpoints (n : ℕ) :
    ProbComp.eval (bitwiseHybridGameOn (validBoundedWords fun _ => 2) emptyKeyGen leakBitEncrypt
        bothWordAdv 0 n) =
      ProbComp.eval (gameOn (validBoundedWords fun _ => 2) emptyKeyGen
        (bitwiseEncrypt leakBitEncrypt) bothWordAdv false n) ∧
    ProbComp.eval (bitwiseHybridGameOn (validBoundedWords fun _ => 2) emptyKeyGen leakBitEncrypt
        bothWordAdv 2 n) =
      ProbComp.eval (gameOn (validBoundedWords fun _ => 2) emptyKeyGen
        (bitwiseEncrypt leakBitEncrypt) bothWordAdv true n) :=
  ⟨eval_bitwiseHybridGameOn_zero _ _ _ _ n,
   eval_bitwiseHybridGameOn_of_le _ _ _ _ fun _ _ _ _ hv => by
     simp only [validBoundedWords, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
     exact hv⟩

/-- Non-vanishing check of `advantage_bitwiseEncrypt_eq`: against `leakBitEncrypt` at `maxLen = 2`,
the word advantage is `1` and the certified reduction `bitwiseToSingle` achieves exact single-bit
advantage `1 / dyadicSize 2 = 1 / 4`. -/
theorem leak_bitwiseToSingle_advantage_eq (n : ℕ) :
    Encryption.advantage
      (Encryption.game emptyKeyGen leakBitEncrypt
        (bitwiseToSingle (validBoundedWords fun _ => 2) leakBitEncrypt (fun _ => 2)
          bothWordAdv)) n = 1 / 4 ∧
    (bitwiseToSingle (validBoundedWords fun _ => 2) leakBitEncrypt (fun _ => 2)
      bothWordAdv).IsPPT := by
  refine ⟨?_, ?_⟩
  · have h := advantage_bitwiseEncrypt_eq (validBoundedWords fun _ => 2) emptyKeyGen
      leakBitEncrypt (fun _ => 2) bothWordAdv n fun _ _ _ _ hv => by
        simp only [validBoundedWords, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
        exact hv
    have h4 : dyadicSize 2 = 4 := by decide
    rw [advantage_bothWordAdv, h4] at h
    rw [eq_div_iff (by norm_num), mul_comm]
    exact_mod_cast h.symm
  · have henc : IsPPTOn (encKeyedInput encBool) encBits
        (fun x : ℕ × List Bool × Bool => pure [x.2.2]) := by
      have hb : ComputableInPolyTime (fun x : ℕ × List Bool × Bool => [x.2.2])
          (encKeyedInput encBool) encBits := by
        dsimp only [encKeyedInput]; polytime
      exact hb.isPPTOn
    exact isPPT_bitwiseToSingle
      (computableInPolyTime_validBoundedWords (ComputableInPolyTime.const 2))
      henc (ComputableInPolyTime.const 2) isPPT_bothWordAdv

/-- Nonvacuity: plaintext-leaking bitwise encryption fails `WordINDCPA`. -/
theorem not_wordINDCPA_leakBitEncrypt :
    ¬ WordINDCPA emptyKeyGen (bitwiseEncrypt leakBitEncrypt) := by
  intro hsec
  have hneg := hsec bothWordAdv isPPT_bothWordAdv
  have hadv1 (n : ℕ) :
      Encryption.advantage
        (gameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length) emptyKeyGen
          (bitwiseEncrypt leakBitEncrypt) bothWordAdv) n = 1 := by
    simp [Encryption.advantage, gameOn, bitwiseEncrypt, emptyKeyGen, leakBitEncrypt, bothWordAdv,
      Game.advantage, Game.succProbability]
  exact not_negligible_const (one_ne_zero : (1 : ℝ≥0) ≠ 0) (by simpa only [hadv1] using hneg)

private noncomputable def mismatchLenAdv : WordAdversary where
  choose _ _ := pure (([false], [true, true]), [])
  guess _ _ _ := pure true

private noncomputable def shortWordAdv : WordAdversary where
  choose _ _ := pure (([false], [true]), [])
  guess _ _ ct := pure (ct == encList encBits [[true]])

/-- Boundary witnesses: empty-word decryption, unequal-length challenge rejection (`1 ≠ 2`),
over-length challenge rejection (`2 > maxLen = 1`), and an admissible 1-bit challenge under
`maxLen = 2` where `split = 1 < maxLen` falls past `m₀.length` (`bitwiseToSingle` still achieves
exact advantage `1 / 4`). -/
theorem bitwise_boundary_witnesses (n : ℕ) :
    decryptWord (encPair encNat encNat (3, 7)) (encList encBits []) = [] ∧
    Encryption.advantage
      (gameOn (validBoundedWords fun _ => 2) emptyKeyGen (bitwiseEncrypt leakBitEncrypt)
        mismatchLenAdv) n = 0 ∧
    Encryption.advantage
      (gameOn (validBoundedWords fun _ => 1) emptyKeyGen (bitwiseEncrypt leakBitEncrypt)
        bothWordAdv) n = 0 ∧
    Encryption.advantage
      (Encryption.game emptyKeyGen leakBitEncrypt
        (bitwiseToSingle (validBoundedWords fun _ => 2) leakBitEncrypt (fun _ => 2)
          shortWordAdv)) n = 1 / 4 := by
  refine ⟨by rw [decryptWord_encList]; rfl, ?_, ?_, ?_⟩
  · simp [Encryption.advantage, gameOn, validBoundedWords, emptyKeyGen, mismatchLenAdv]
  · simp [Encryption.advantage, gameOn, validBoundedWords, emptyKeyGen, bothWordAdv]
  · have h := advantage_bitwiseEncrypt_eq (validBoundedWords fun _ => 2) emptyKeyGen
      leakBitEncrypt (fun _ => 2) shortWordAdv n fun _ _ _ _ hv => by
        simp only [validBoundedWords, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
        exact hv
    have hshort : Encryption.advantage
        (gameOn (validBoundedWords fun _ => 2) emptyKeyGen (bitwiseEncrypt leakBitEncrypt)
          shortWordAdv) n = 1 := by
      simp [Encryption.advantage, gameOn, validBoundedWords, bitwiseEncrypt, emptyKeyGen,
        leakBitEncrypt, shortWordAdv, Game.advantage, Game.succProbability]
    have h4 : dyadicSize 2 = 4 := by decide
    rw [hshort, h4] at h
    rw [eq_div_iff (by norm_num), mul_comm]
    exact_mod_cast h.symm

/-! ### Necessity of polynomially bounded public-key length for `INDCPA → WordINDCPA` -/

private def expKeyGen (n : ℕ) : ProbComp (List Bool × List Bool) :=
  pure (List.replicate (2 ^ n) false, [])

private noncomputable def expLeakEncrypt (n : ℕ) (_pk : List Bool) (b : Bool) :
    ProbComp (List Bool) :=
  (fun coins => [b && (coins == encUnary n)]) <$> BitString.sampleList n

private theorem isPPTOn_expLeakEncrypt :
    IsPPTOn (encKeyedInput encBool) encBits (fun ⟨n, pk, b⟩ => expLeakEncrypt n pk b) := by
  let E := encKeyedInput encBool
  have hn : ComputableInPolyTime (fun x : ℕ × List Bool × Bool => x.1) E encUnary := by
    dsimp only [E, encKeyedInput]; fun_prop
  have hb : ComputableInPolyTime
      (fun p : (ℕ × List Bool × Bool) × List Bool => p.1.2.2) (encPair E encBits) encBool := by
    dsimp only [E, encKeyedInput]; fun_prop
  have hcoins : ComputableInPolyTime
      (fun p : (ℕ × List Bool × Bool) × List Bool => p.2) (encPair E encBits) encBits :=
    ComputableInPolyTime.snd E encBits
  have htarget : ComputableInPolyTime
      (fun p : (ℕ × List Bool × Bool) × List Bool => encUnary p.1.1) (encPair E encBits) encBits :=
    (hn.comp (ComputableInPolyTime.fst E encBits)).encoding_comp
  have hbody : ComputableInPolyTime
      (fun p : (ℕ × List Bool × Bool) × List Bool => [p.1.2.2 && (p.2 == encUnary p.1.1)])
      (encPair E encBits) encBits :=
    (ComputableInPolyTime.bool_and.comp (hb.prod (hcoins.beq htarget))).encoding_comp
  exact (IsPPTOn.of_seeded hn hbody).congr fun ⟨_, _, _⟩ => rfl

private theorem eval_expLeakEncrypt_false (n : ℕ) (pk : List Bool) :
    ProbComp.eval (expLeakEncrypt n pk false) = PMF.pure [false] := by
  simp [expLeakEncrypt, PMF.map, Function.comp_def, PMF.bind_const]

private theorem eval_expLeakEncrypt_true_apply_true (n : ℕ) (pk : List Bool) :
    (ProbComp.eval (expLeakEncrypt n pk true)) [true] = (1 : ℝ≥0∞) / 2 ^ n := by
  simp only [expLeakEncrypt, ProbComp.eval_map, BitString.eval_sampleList, Bool.true_and]
  rw [BitString.uniformList_map_apply]
  have hcard : (Finset.univ.filter fun r : Fin n → Bool =>
      [List.ofFn r == encUnary n] = [true]).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨fun _ => true, Finset.ext fun r => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.cons.injEq, and_true,
      beq_iff_eq, Finset.mem_singleton, encUnary_apply]
    refine ⟨fun h => funext fun i => ?_, fun h => by subst h; simp⟩
    have hi := congrArg (·[i.val]?) h
    simpa using hi
  rw [hcard, Nat.cast_one]

private theorem eval_expLeakEncrypt_true_ne (n : ℕ) (pk : List Bool) {c : List Bool}
    (hf : c ≠ [false]) (ht : c ≠ [true]) :
    (ProbComp.eval (expLeakEncrypt n pk true)) c = 0 := by
  rw [PMF.apply_eq_zero_iff]
  simp only [expLeakEncrypt, ProbComp.eval_map, PMF.mem_support_map_iff, not_exists, not_and]
  rintro coins _ rfl
  cases hcoin : coins == encUnary n
  · exact hf (by rw [hcoin]; rfl)
  · exact ht (by rw [hcoin]; rfl)

private theorem closeTo_expLeakEncrypt (n : ℕ) (pk : List Bool) (b₀ b₁ : Bool) :
    CloseTo (ProbComp.eval (expLeakEncrypt n pk b₀))
      (ProbComp.eval (expLeakEncrypt n pk b₁)) ((1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) := by
  have htf : CloseTo (ProbComp.eval (expLeakEncrypt n pk true))
      (PMF.pure [false]) ((1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) := by
    rw [closeTo_iff_tsum_tsub_le, tsum_eq_single [true]]
    · rw [ENNReal.coe_div (pow_ne_zero _ (by norm_num))]
      simp [eval_expLeakEncrypt_true_apply_true]
    · intro c hc
      by_cases hf : c = [false]
      · subst hf
        simp only [PMF.pure_apply, ↓reduceIte, tsub_eq_zero_iff_le]
        exact PMF.coe_le_one _ _
      · simp [eval_expLeakEncrypt_true_ne n pk hf hc]
  cases b₀ <;> cases b₁
  · exact (CloseTo.refl _).mono zero_le
  · rw [eval_expLeakEncrypt_false]; exact htf.symm
  · rw [eval_expLeakEncrypt_false]; exact htf
  · exact (CloseTo.refl _).mono zero_le

private theorem indcpa_expLeakEncrypt : INDCPA expKeyGen expLeakEncrypt := by
  intro adversary _
  refine negligible_of_le (negligible_const_div_two_pow 1) fun n => ?_
  rw [Nat.cast_one]
  dsimp only [Encryption.advantage, Encryption.game, gameOn]
  simp only [Bool.false_eq_true, ↓reduceIte, expKeyGen, pmf_norm]
  exact Game.advantage_bind_le_nnreal _ _ _ fun choice =>
    Game.advantage_bind_le_of_closeTo (closeTo_expLeakEncrypt n _ _ _) _

private noncomputable def expWordAdv : WordAdversary where
  choose _ pk := pure ((pk, encUnary pk.length), pk)
  guess _ state ct := pure (!(bitwiseDecrypt (fun _ c => c == [true]) [] ct == state))

private theorem isPPT_expWordAdv : expWordAdv.IsPPT where
  choose := by
    have hpk := ComputableInPolyTime.snd encUnary encBits
    have hones : ComputableInPolyTime (fun p : ℕ × List Bool => encUnary p.2.length)
        (encPair encUnary encBits) encBits :=
      ((ComputableInPolyTime.encoding_length encBits).comp hpk).encoding_comp
    exact ((hpk.prod hones).prod hpk).isPPTOn
  guess := by
    have hbit : ComputableInPolyTime (fun q : List Bool × List Bool => q.2 == [true])
        (encPair encBits encBits) encBool :=
      (ComputableInPolyTime.snd encBits encBits).beq (ComputableInPolyTime.const [true])
    have hct : ComputableInPolyTime (fun x : ℕ × List Bool × List Bool => x.2.2)
        encGuessInput encBits := by dsimp only [encGuessInput]; fun_prop
    have hst : ComputableInPolyTime (fun x : ℕ × List Bool × List Bool => x.2.1)
        encGuessInput encBits := by dsimp only [encGuessInput]; fun_prop
    have hdec := (computableInPolyTime_bitwiseDecrypt (decrypt := fun _ c => c == [true]) hbit).comp
      ((ComputableInPolyTime.const ([] : List Bool)).prod hct)
    exact (ComputableInPolyTime.bool_not.comp (hdec.beq hst)).isPPTOn

private theorem eval_mapM_expLeakEncrypt_false (n : ℕ) (pk : List Bool) (k : ℕ) :
    ProbComp.eval ((List.replicate k false).mapM (expLeakEncrypt n pk)) =
      PMF.pure (List.replicate k [false]) := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, List.mapM_cons, eval_expLeakEncrypt_false, ih]

private noncomputable def allFalseRun (n : ℕ) (pk : List Bool) (k : ℕ) : PMF Bool :=
  (ProbComp.eval ((List.replicate k true).mapM (expLeakEncrypt n pk))).map
    fun cts => cts.map (· == [true]) == List.replicate k false

private theorem allFalseRun_apply_true (n : ℕ) (pk : List Bool) (k : ℕ) :
    (allFalseRun n pk k) true = ((ProbComp.eval (expLeakEncrypt n pk true)) [false]) ^ k := by
  induction k with
  | zero => simp [allFalseRun]
  | succ k ih =>
    have hstep : allFalseRun n pk (k + 1) =
        (ProbComp.eval (expLeakEncrypt n pk true)).bind fun c =>
          (allFalseRun n pk k).map fun ok => ((c == [true]) == false) && ok := by
      simp [allFalseRun, List.replicate_succ, List.mapM_cons, pmf_norm, PMF.map_bind, PMF.map_comp,
        Function.comp_def]
    rw [hstep, PMF.bind_apply, tsum_eq_single [false]]
    · have hf : (fun ok : Bool => (([false] == [true]) == false) && ok) = id := by
        funext ok; simp
      rw [hf, PMF.map_id, ih, pow_succ']
    · intro c hc
      by_cases ht : c = [true]
      · subst ht
        simp [PMF.map, Function.comp_def, PMF.bind_const]
      · simp [eval_expLeakEncrypt_true_ne n pk hc ht]

private theorem toReal_expLeakEncrypt_true_false (n : ℕ) (pk : List Bool) :
    ((ProbComp.eval (expLeakEncrypt n pk true)) [false]).toReal = 1 - 1 / (2 : ℝ) ^ n := by
  have hsum := Probability.PMF.toOuterMeasure_add_compl_ennreal
    (ProbComp.eval (expLeakEncrypt n pk true)) ({[false]} : Set (List Bool))
  rw [PMF.toOuterMeasure_apply_singleton] at hsum
  have hcompl : (ProbComp.eval (expLeakEncrypt n pk true)).toOuterMeasure
      ({[false]} : Set (List Bool))ᶜ =
      (ProbComp.eval (expLeakEncrypt n pk true)) [true] := by
    rw [PMF.toOuterMeasure_apply, tsum_eq_single [true]]
    · simp
    · intro c hc
      by_cases hf : c = [false]
      · subst hf; simp
      · simp [eval_expLeakEncrypt_true_ne n pk hf hc]
  rw [hcompl, eval_expLeakEncrypt_true_apply_true] at hsum
  have hreal := congrArg ENNReal.toReal hsum
  have hne1 : (1 : ℝ≥0∞) / 2 ^ n ≠ ⊤ := by
    rw [div_eq_mul_inv]
    exact ENNReal.mul_ne_top ENNReal.one_ne_top
      (ENNReal.inv_ne_top.mpr (pow_ne_zero _ (by norm_num)))
  rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) hne1, ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat] at hreal
  linarith

/-- Separation witness (`Bitwise.lean`): `(expKeyGen, expLeakEncrypt)` has `2 ^ n`-bit public keys,
strict-PPT encryption, and 1-bit `INDCPA` (`≤ 1 / 2 ^ n` advantage against all adversaries), yet
`bitwiseEncrypt expLeakEncrypt` fails `WordINDCPA` (`expWordAdv` achieves advantage `≥ 1 / 2` at
every `n`). Thus polynomially bounded public-key length is necessary for `INDCPA → WordINDCPA`. -/
theorem indcpa_and_not_wordINDCPA_expKeyGen :
    INDCPA expKeyGen expLeakEncrypt ∧
    IsPPTOn (encKeyedInput encBool) encBits (fun ⟨n, pk, b⟩ => expLeakEncrypt n pk b) ∧
    ¬ WordINDCPA expKeyGen (bitwiseEncrypt expLeakEncrypt) := by
  refine ⟨indcpa_expLeakEncrypt, isPPTOn_expLeakEncrypt, fun hword => ?_⟩
  have hneg := hword expWordAdv isPPT_expWordAdv
  have hhalf : ∀ n : ℕ, (1 / 2 : ℝ≥0) ≤
      Encryption.advantage
        (gameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length) expKeyGen
          (bitwiseEncrypt expLeakEncrypt) expWordAdv) n := by
    intro n
    let pk := List.replicate (2 ^ n) false
    have hfalse : ProbComp.eval
        (gameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length) expKeyGen
          (bitwiseEncrypt expLeakEncrypt) expWordAdv false n) = PMF.pure false := by
      simp [gameOn, expKeyGen, expWordAdv, bitwiseEncrypt, eval_mapM_expLeakEncrypt_false,
        List.map_replicate]
    have htrue : ProbComp.eval
        (gameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length) expKeyGen
          (bitwiseEncrypt expLeakEncrypt) expWordAdv true n) =
        (allFalseRun n pk (2 ^ n)).map (!·) := by
      simp [gameOn, expKeyGen, expWordAdv, bitwiseEncrypt, allFalseRun, pk, encUnary_apply,
        pmf_norm, PMF.map_comp, Function.comp_def]
    have htrue_false : ((allFalseRun n pk (2 ^ n)).map (!·)) false =
        (allFalseRun n pk (2 ^ n)) true := by
      rw [PMF.map_apply, tsum_bool]; simp
    have hsum := Probability.PMF.apply_true_add_apply_false
      ((allFalseRun n pk (2 ^ n)).map (!·))
    have hreal_sum := congrArg ENNReal.toReal hsum
    rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _), ENNReal.toReal_one,
      htrue_false, allFalseRun_apply_true, ENNReal.toReal_pow,
      toReal_expLeakEncrypt_true_false] at hreal_sum
    have hpow_le : (1 - 1 / (2 : ℝ) ^ n) ^ (2 ^ n) ≤ 1 / 2 := by
      set t : ℝ := 1 / (2 : ℝ) ^ n with ht_def
      have ht0 : 0 ≤ t := by positivity
      have ht1 : t ≤ 1 := div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)
      have hsq : 1 - t ^ 2 ≤ 1 := by nlinarith
      have hprod : ((1 - t) * (1 + t)) ^ (2 ^ n) ≤ 1 := by
        have hring : (1 - t) * (1 + t) = 1 - t ^ 2 := by ring
        rw [hring]
        exact pow_le_one₀ (by nlinarith) hsq
      have hbern : (2 : ℝ) ≤ (1 + t) ^ (2 ^ n) := by
        have hb := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ t) (2 ^ n)
        have hkt : (2 ^ n : ℕ) * t = 1 := by
          rw [ht_def]; push_cast; exact mul_one_div_cancel (by positivity)
        linarith
      rw [mul_pow] at hprod
      have hnonneg : 0 ≤ (1 - t) ^ (2 ^ n) := pow_nonneg (by linarith) _
      have h2 := mul_le_mul_of_nonneg_left hbern hnonneg
      linarith
    have hs0 : Game.succProbability (PMF.pure false) = 0 := by simp [Game.succProbability]
    rw [← NNReal.coe_le_coe]
    dsimp only [Encryption.advantage]
    rw [hfalse, htrue, Game.coe_advantage, hs0, NNReal.coe_zero, zero_sub, abs_neg,
      abs_of_nonneg (NNReal.coe_nonneg _), Game.coe_succProbability]
    push_cast
    linarith
  exact not_negligible_const (by norm_num : (1 / 2 : ℝ≥0) ≠ 0) (negligible_of_le hneg hhalf)

/-! ### Multi-bit Blum Goldwasser–Micali security clients -/

/-- `wordINDCPA_blumGoldwasserMicali` yields both `WordINDCPA` and oracle-CPA security
`WordINDCPAOracle` (`PublicKeyCPA.lean`) for `(blumKeyGen gen, encryptWord)`. -/
theorem blumWordINDCPA_and_oracle {gen : ℕ → ProbComp ModulusDesc}
    {sizeBound : ℕ → ℕ} (hbound : PolynomiallyBounded sizeBound)
    (hblum : ∀ n, ∀ d ∈ (ProbComp.eval (gen n)).support, IsBlumModulus d.p d.q)
    (hsize : ∀ n, ∀ d ∈ (ProbComp.eval (gen n)).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (hupper : ∀ n, ∀ d ∈ (ProbComp.eval (gen n)).support,
      d.p.size ≤ sizeBound n ∧ d.q.size ≤ sizeBound n)
    (hQR : QuadraticResiduosityHard fun n => ProbComp.eval (gen n)) :
    WordINDCPA (blumKeyGen gen) encryptWord ∧
      WordINDCPAOracle (blumKeyGen gen) encryptWord := by
  have hcpa := wordINDCPA_blumGoldwasserMicali hbound hblum hsize hupper hQR
  exact ⟨hcpa, hcpa.wordINDCPAOracle isPPTOn_encryptWord⟩

/-- Direct client of `INDCPA.wordINDCPA_bitwiseEncrypt` when `gen` is uniform strict PPT:
`encryptWord` and `Encryption.bitwiseEncrypt encrypt` agree definitionally under `module`. -/
theorem blumWordINDCPA_of_isPPTOn {gen : ℕ → ProbComp ModulusDesc}
    (hgen : IsPPTOn encUnary encModulusDesc gen)
    (hblum : ∀ n, ∀ d ∈ (ProbComp.eval (gen n)).support, IsBlumModulus d.p d.q)
    (hsize : ∀ n, ∀ d ∈ (ProbComp.eval (gen n)).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (hQR : QuadraticResiduosityHard fun n => ProbComp.eval (gen n)) :
    WordINDCPA (blumKeyGen gen) encryptWord :=
  (indcpa_blumGoldwasserMicali hblum hsize hQR).wordINDCPA_bitwiseEncrypt
    (isPPTOn_blumKeyGen hgen) isPPTOn_encrypt

/-! ### Joint satisfiability of `hblum`, `hsize`, `hbound`, and `hupper` via `WeakPNT` -/

private noncomputable def blumPrimesUpTo (m : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 m).filter fun p => p.Prime ∧ p ≡ 3 [MOD 4]

private noncomputable def blumLogSum (m : ℕ) : ℝ :=
  ∑ p ∈ blumPrimesUpTo m, Real.log p

private theorem eventually_exists_blumPrime_Ioc :
    ∀ᶠ m : ℕ in atTop, ∃ p : ℕ, IsBlumPrime p ∧ m < p ∧ p ≤ 2 * m := by
  have hreal := Chebyshev.tendsto_sum_log_prime_modEq_div_atTop (q := 4) (a := 3) (by decide)
  have hφ4 : ((Nat.totient 4 : ℝ))⁻¹ = (1 / 2 : ℝ) := by
    have ht : Nat.totient 4 = 2 := by decide
    rw [ht]; norm_num
  rw [hφ4] at hreal
  have hnat : Tendsto (fun m : ℕ => blumLogSum m / (m : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) := by
    refine (hreal.comp tendsto_natCast_atTop_atTop).congr fun m => ?_
    simp only [Function.comp_apply, Nat.floor_natCast, blumLogSum, blumPrimesUpTo]
  have hmul2 : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  have h2 : Tendsto (fun m : ℕ => blumLogSum (2 * m) / (m : ℝ)) atTop (𝓝 1) := by
    have hcomp := (hnat.comp hmul2).const_mul 2
    rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num] at hcomp
    refine hcomp.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with m hm
    simp only [Function.comp_apply, Nat.cast_mul, Nat.cast_ofNat]
    have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    field_simp [hmR]
  have hdiff : Tendsto (fun m : ℕ => (blumLogSum (2 * m) - blumLogSum m) / (m : ℝ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    have hsub := h2.sub hnat
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hsub
    exact hsub.congr fun m => (sub_div _ _ _).symm
  filter_upwards [hdiff.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_gt_atTop 0] with m hpos hm
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hlt : blumLogSum m < blumLogSum (2 * m) := by
    have := (div_pos_iff_of_pos_right hmR).mp hpos
    linarith
  have hsub : blumPrimesUpTo m ⊆ blumPrimesUpTo (2 * m) := fun p hp => by
    simp only [blumPrimesUpTo, Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans (by omega)⟩, hp.2⟩
  have hne : (blumPrimesUpTo (2 * m) \ blumPrimesUpTo m).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hemp
    have heq := Finset.Subset.antisymm hsub hemp
    simp only [blumLogSum, heq, lt_irrefl] at hlt
  obtain ⟨p, hp⟩ := hne
  simp only [Finset.mem_sdiff, blumPrimesUpTo, Finset.mem_filter, Finset.mem_Ioc] at hp
  have hmp : m < p := by
    by_contra hle
    exact hp.2 ⟨⟨hp.1.1.1, Nat.le_of_not_lt hle⟩, hp.1.2⟩
  exact ⟨p, ⟨hp.1.2.1, hp.1.2.2⟩, hmp, hp.1.1.2⟩

private theorem exists_blumThreshold :
    ∃ M₀ : ℕ, ∀ m ≥ M₀, ∃ p : ℕ, IsBlumPrime p ∧ m < p ∧ p ≤ 2 * m :=
  eventually_atTop.mp eventually_exists_blumPrime_Ioc

private noncomputable def M₀ : ℕ := exists_blumThreshold.choose

private theorem exists_bounded_blumModulusDesc (n : ℕ) :
    ∃ d : ModulusDesc,
      IsBlumModulus d.p d.q ∧
      (n ≤ d.p.size ∧ n ≤ d.q.size) ∧
      (d.p.size ≤ n + (M₀ + 3) ∧ d.q.size ≤ n + (M₀ + 3)) := by
  let B := max n M₀
  have hBM₀ : M₀ ≤ 2 ^ B := (le_max_right n M₀).trans (Nat.lt_two_pow_self (n := B)).le
  have hBM₁ : M₀ ≤ 2 ^ (B + 1) := hBM₀.trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ B))
  obtain ⟨p, hp, hp_gt, hp_le⟩ := exists_blumThreshold.choose_spec (2 ^ B) hBM₀
  obtain ⟨q, hq, hq_gt, hq_le⟩ := exists_blumThreshold.choose_spec (2 ^ (B + 1)) hBM₁
  have hp_lt_pow : p < 2 ^ (B + 2) := by
    calc p ≤ 2 * 2 ^ B := hp_le
      _ = 2 ^ (B + 1) := by ring
      _ < 2 ^ (B + 2) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)
  have hq_lt_pow : q < 2 ^ (B + 3) := by
    calc q ≤ 2 * 2 ^ (B + 1) := hq_le
      _ = 2 ^ (B + 2) := by ring
      _ < 2 ^ (B + 3) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)
  have hp_lt_q : p < q := by
    calc p ≤ 2 * 2 ^ B := hp_le
      _ = 2 ^ (B + 1) := by ring
      _ < q := hq_gt
  have hn_le_B : 2 ^ n ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) (le_max_left n M₀)
  have hB_le : B ≤ n + M₀ := max_le (Nat.le_add_right n M₀) (Nat.le_add_left M₀ n)
  have hp3 := hp.2
  have hq3 := hq.2
  refine ⟨⟨p, q, hp.1, hq.1, by omega, by omega, by omega⟩,
    ⟨hp, hq, hp_lt_q.ne⟩,
    ⟨(Nat.lt_size.mpr (hn_le_B.trans hp_gt.le)).le,
     (Nat.lt_size.mpr (hn_le_B.trans (hp_gt.le.trans hp_lt_q.le))).le⟩,
    ⟨(Nat.size_le.mpr hp_lt_pow).trans (by omega),
     (Nat.size_le.mpr hq_lt_pow).trans (by omega)⟩⟩

private noncomputable def blumBoundedWitnessGen (n : ℕ) : ProbComp ModulusDesc :=
  pure (exists_bounded_blumModulusDesc n).choose

/-- All modulus hypotheses (`hbound`, `hblum`, `hsize`, `hupper`) of
`wordINDCPA_blumGoldwasserMicali` hold simultaneously on `blumBoundedWitnessGen`, leaving
`QuadraticResiduosityHard` as the sole hypothesis. -/
theorem wordINDCPA_blumBoundedWitnessGen
    (hQR : QuadraticResiduosityHard fun n => ProbComp.eval (blumBoundedWitnessGen n)) :
    WordINDCPA (blumKeyGen blumBoundedWitnessGen) encryptWord := by
  have hbound : PolynomiallyBounded (fun n => n + (M₀ + 3)) := by fun_prop
  refine wordINDCPA_blumGoldwasserMicali hbound ?_ ?_ ?_ hQR
  · intro n d hd
    simp only [blumBoundedWitnessGen, ProbComp.eval_pure, PMF.support_pure,
      Set.mem_singleton_iff] at hd
    exact hd ▸ (exists_bounded_blumModulusDesc n).choose_spec.1
  · intro n d hd
    simp only [blumBoundedWitnessGen, ProbComp.eval_pure, PMF.support_pure,
      Set.mem_singleton_iff] at hd
    exact hd ▸ (exists_bounded_blumModulusDesc n).choose_spec.2.1
  · intro n d hd
    simp only [blumBoundedWitnessGen, ProbComp.eval_pure, PMF.support_pure,
      Set.mem_singleton_iff] at hd
    exact hd ▸ (exists_bounded_blumModulusDesc n).choose_spec.2.2

end CslibFrontierTests.Crypto.GoldwasserMicaliWord
