/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module

public import CslibFrontier.Crypto.Computational.FuzzyExtractor.Basic
public import CslibFrontier.Crypto.Computational.FuzzyExtractor.DecodeThenExtract
public import CslibFrontier.Crypto.Computational.FuzzyExtractor.DecodeThenExtract.Security
public import CslibFrontier.Crypto.Computational.FuzzyExtractor.Reusable
public import CslibFrontier.Crypto.Computational.FuzzyExtractor.Reusable.Encrypt
import CslibFrontier.Probability.PMF.Uniform

/-!
# Computational fuzzy extractor tests

Exercise the fuzzy-extractor definitions, the sketch-and-extract construction (Lemma 2.5), and the
LWE decode-then-extract construction (Construction 4.1) on concrete finite-field parameters.
Distinguishers are `Experiment` programs. Includes positive instances (zero-error
sketch-and-extract, the additive extractor on a uniform source, the LWE security bound for
Construction 4.1 at concrete dimensions against `LWE.advantage`, a concrete Hamming distance) and a
separating negative fixture
(`revealingFuzzyExtractor`) that is perfectly reproducible for every distance threshold `t` yet
has distinguishing advantage `1 / 2` on a uniform 1-bit source. The asymptotic theorem
`computationallySecure_lweFuzzyExtractor` is applied to the uniform source, for which its LWE
premise holds unconditionally, and to independent-coordinate sources under `DecisionLWE`.
The reusable-extractor tests check the common-matrix scheme and its strong-reuse attack, that both
correctness hypotheses of the Section 5 scheme are satisfiable, and that its strong-reuse bound is
attained (advantage `0`) for a uniform source and uniform encryption errors.
-/

public section

namespace CslibFrontierTests.Crypto.Computational.FuzzyExtractorTest

open Cslib Cslib.Crypto Cslib.Crypto.FuzzyExtractor Cslib.Probability
open scoped ENNReal NNReal

/-! ### Concrete Hamming distance -/

/-- Concrete verification of `hammingDist w w' = 1` on two 3-symbol vectors over `ZMod 5`. -/
example : hammingDist ![(1 : ZMod 5), 2, 3] ![(1 : ZMod 5), 4, 3] = 1 := by
  decide

/-! ### Concrete sketch-and-extract instance (Lemma 2.5) -/

/-- Trivial exact secure sketch on `Fin 3 → ZMod 2` for zero-noise readings (`t = 0`). -/
def trivialSecureSketch : SecureSketch (Fin 3 → ZMod 2) Unit where
  sketch _ := return ()
  recover w' _ := return w'

theorem correct_trivialSecureSketch : trivialSecureSketch.Correct hammingDist 0 := by
  intro w w' hdis s _ wHat hwHat
  simp only [trivialSecureSketch, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hwHat
  have hw : w = w' := hammingDist_eq_zero.mp (Nat.eq_zero_of_le_zero hdis)
  rw [hwHat, hw]

/-- Applying `sketchAndExtract` with the one-time-pad extractor `fun w x => w + x` yields a
zero-error Hamming fuzzy extractor at threshold `t = 0`. -/
theorem correctHamming_trivialSketchAndExtract :
    (trivialSecureSketch.sketchAndExtract (fun (w x : Fin 3 → ZMod 2) => w + x)).CorrectHamming
      0 :=
  correct_trivialSecureSketch.sketchAndExtract _

/-- On identical readings `w' = w`, the reproduction game of the sketch-and-extract instance
always outputs `true` with failure probability `0`. -/
example (w : Fin 3 → ZMod 2) :
    Game.failProbability
      ((trivialSecureSketch.sketchAndExtract
        (fun (v x : Fin 3 → ZMod 2) => v + x)).reproduceGame w w) = 0 := by
  have h := correctHamming_trivialSketchAndExtract.correctWithError_zero w w
    (by simp [hammingDist_self])
  exact le_antisymm h zero_le

/-! ### Concrete decode-then-extract security (Construction 4.1) -/

/-- Concrete instantiation of `decodeThenExtract` on `m = 3, n = 2, q = 5` with the additive
extractor `fun s x => s + x`: on a uniform source `W`, every distinguisher has advantage `0`. -/
theorem securityAdvantage_decodeThenExtract_concrete_zero
    (decode : Matrix (Fin 3) (Fin 2) (ZMod 5) → (Fin 3 → ZMod 5) →
      ProbComp (Option (Fin 2 → ZMod 5)))
    (D : (Fin 2 → ZMod 5) → DecodeHelper 3 2 5 (Fin 2 → ZMod 5) → Experiment) :
    (decodeThenExtract 3 2 5 decode (fun (s x : Fin 2 → ZMod 5) => s + x)).securityAdvantage
        (PMF.uniformOfFintype (Fin 3 → ZMod 5)) D = 0 :=
  securityAdvantage_decodeThenExtract_add_uniform_eq_zero 3 2 5 decode D

/-- Construction 4.1 at `m = 4, k = 1, l = 1, q = 7`: for every source and distinguisher, the
advantage is at most the sum of two dimension-`1` decisional LWE advantages. -/
example
    (decode : Matrix (Fin 4) (Fin (1 + 1)) (ZMod 7) → (Fin 4 → ZMod 7) →
      ProbComp (Option (Fin (1 + 1) → ZMod 7)))
    (W : PMF (Fin 4 → ZMod 7))
    (D : (Fin 1 → ZMod 7) → DecodeHelper 4 (1 + 1) 7 Unit → Experiment) :
    (lweFuzzyExtractor 4 1 1 7 decode).securityAdvantage W D ≤
      LWE.advantage (PMF.uniformOfFintype (Fin 1 → ZMod 7)) W (hardcoreKeyReduction D) +
        LWE.advantage (PMF.uniformOfFintype (Fin 1 → ZMod 7)) W (hardcoreUniformReduction D) :=
  securityAdvantage_lweFuzzyExtractor_le decode W D

/-- With a uniform error distribution, the decisional LWE advantage of every distinguisher is `0`:
`A s + e` is uniform and independent of `(A, s)`. -/
theorem lweAdvantage_uniform_error_eq_zero
    (B : Matrix (Fin 4) (Fin 1) (ZMod 7) → (Fin 4 → ZMod 7) → Experiment) :
    LWE.advantage (PMF.uniformOfFintype (Fin 1 → ZMod 7))
      (PMF.uniformOfFintype (Fin 4 → ZMod 7)) B = 0 :=
  LWE.advantage_uniform_error_eq_zero _ B

/-- For the uniform source, both LWE advantages in `securityAdvantage_lweFuzzyExtractor_le` vanish,
so Construction 4.1 is `0`-secure for it against every distinguisher. -/
example
    (decode : Matrix (Fin 4) (Fin (1 + 1)) (ZMod 7) → (Fin 4 → ZMod 7) →
      ProbComp (Option (Fin (1 + 1) → ZMod 7))) :
    (lweFuzzyExtractor 4 1 1 7 decode).ComputationallySecureFor
      {PMF.uniformOfFintype (Fin 4 → ZMod 7)} (fun _ => True) 0 := by
  intro W hW D _
  rw [Set.mem_singleton_iff] at hW
  subst hW
  simpa only [lweAdvantage_uniform_error_eq_zero, add_zero] using
    securityAdvantage_lweFuzzyExtractor_le decode (PMF.uniformOfFintype (Fin 4 → ZMod 7)) D

/-! ### Asymptotic security: the premise is satisfiable -/

/-- With uniform errors, `DecisionLWEWithErrors` holds for all dimensions: `A s + e` is uniform and
independent of `(A, s)`, so the real and random games coincide. -/
theorem decisionLWEWithErrors_uniform (n m w : ℕ → ℕ) :
    DecisionLWEWithErrors n m w fun κ => PMF.uniformOfFintype (Fin (m κ) → ZMod (2 ^ w κ)) := by
  intro D _
  simp only [LWE.realGame_uniform_error_eq_randomGame, Game.advantage_self]
  exact negligible_zero

open Turing.MultiTapeTM in
/-- The asymptotic theorem applies to the family with `κ` samples, key length `κ`, `κ` further
secret coordinates and modulus `2`, on the uniform source. -/
example (decode : (κ : ℕ) → Matrix (Fin κ) (Fin (κ + κ)) (ZMod (2 ^ 1)) →
      (Fin κ → ZMod (2 ^ 1)) → ProbComp (Option (Fin (κ + κ) → ZMod (2 ^ 1)))) :
    ComputationallySecure (fun κ => lweFuzzyExtractor κ κ κ (2 ^ 1) (decode κ))
      {fun κ => PMF.uniformOfFintype (Fin κ → ZMod (2 ^ 1))}
      (LWEFamily.Distinguisher.IsPPT (m := id) (k := id) (l := id) (w := fun _ => 1)) :=
  computationallySecure_lweFuzzyExtractor (m := id) (k := id) (l := id) (w := fun _ => 1)
    ComputableInPolyTime.id' ComputableInPolyTime.id' ComputableInPolyTime.id'
    (ComputableInPolyTime.const 1) decode (by
      rintro _ rfl
      exact decisionLWEWithErrors_uniform id id fun _ => 1)

open Turing.MultiTapeTM in
/-- On the source whose coordinates are independent draws from `noise κ`, the premise is
`DecisionLWE l m w noise`, the form of the assumption used by the Regev and GSW schemes. -/
example {m k l w : ℕ → ℕ} (hm : ComputableInPolyTime m encUnary encUnary)
    (hk : ComputableInPolyTime k encUnary encUnary) (hl : ComputableInPolyTime l encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary)
    (decode : (κ : ℕ) → Matrix (Fin (m κ)) (Fin (k κ + l κ)) (ZMod (2 ^ w κ)) →
      (Fin (m κ) → ZMod (2 ^ w κ)) → ProbComp (Option (Fin (k κ + l κ) → ZMod (2 ^ w κ))))
    (noise : (κ : ℕ) → PMF (ZMod (2 ^ w κ))) (hLWE : DecisionLWE l m w noise) :
    ComputationallySecure (fun κ => lweFuzzyExtractor (m κ) (k κ) (l κ) (2 ^ w κ) (decode κ))
      {fun κ => PMF.pi fun _ : Fin (m κ) => noise κ} LWEFamily.Distinguisher.IsPPT :=
  computationallySecure_lweFuzzyExtractor hm hk hl hw decode (by
    rintro _ rfl
    exact (decisionLWE_iff_decisionLWEWithErrors l m w noise).mp hLWE)

/-! ### Separating fixture: reproducible for all `t`, but insecure -/

/-- A fuzzy extractor on `Bool` that outputs `(w, w)`: `Rep` ignores `w'` and returns the helper
bit `p = w`, so reproduction succeeds for every distance threshold `t`, but the helper leaks the
key completely. -/
def revealingFuzzyExtractor : FuzzyExtractor Bool Bool Bool where
  gen w := return (w, w)
  rep _ p := return p

/-- `revealingFuzzyExtractor` is zero-error correct for every distance function `dis` and every
threshold `t`. -/
theorem correct_revealingFuzzyExtractor (dis : Bool → Bool → ℕ) (t : ℕ) :
    revealingFuzzyExtractor.Correct dis t := by
  intro w w' _ r p hrp r' hr'
  simp only [revealingFuzzyExtractor, ProbComp.eval_pure, PMF.mem_support_pure_iff,
    Prod.mk.injEq] at hrp hr'
  rw [hr', hrp.2, hrp.1]

/-- The equality distinguisher on `Bool` keys and helpers, testing whether the key equals the
helper bit. -/
def eqBitDistinguisher (r p : Bool) : Experiment :=
  pure (decide (r = p))

/-- On a uniform 1-bit source, `revealingFuzzyExtractor` has distinguishing advantage `1 / 2`
against `eqBitDistinguisher`. -/
theorem securityAdvantage_revealingFuzzyExtractor :
    revealingFuzzyExtractor.securityAdvantage (PMF.uniformOfFintype Bool) eqBitDistinguisher =
      (1 : ℝ≥0) / 2 := by
  simp only [FuzzyExtractor.securityAdvantage, FuzzyExtractor.realGame_eq_bind,
    FuzzyExtractor.idealGame_eq_bind, FuzzyExtractor.realDistribution,
    FuzzyExtractor.idealDistribution, revealingFuzzyExtractor, eqBitDistinguisher,
    ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind, decide_true, PMF.bind_const,
    Game.advantage, Game.succProbability, PMF.pure_apply_self,
    PMF.bind_apply, PMF.uniformOfFintype_apply, Fintype.card_bool, tsum_bool,
    Bool.true_eq_false, decide_false, PMF.pure_apply, Bool.false_eq_true, ↓reduceIte,
    mul_zero, mul_one, add_zero, zero_add]
  norm_num [NNReal.nndist_eq]
  rw [ENNReal.toNNReal_add] <;>
    norm_num [ENNReal.toNNReal_add, ENNReal.toNNReal_mul, ENNReal.toNNReal_inv,
      ENNReal.toNNReal_ofNat, ENNReal.mul_eq_top, ENNReal.inv_eq_top]
  norm_num [NNReal.sub_def, Real.toNNReal_div]
  rw [Real.toNNReal_of_nonpos (by norm_num)]
  positivity

/-! ### Reusable fuzzy extractors: shift clamping, common-matrix FMR, and strong attack -/

/-- Concrete verification of `clampShift`: a shift of Hamming weight `2` is zeroed out when the
allowed budget is `t = 1`, whereas a shift of Hamming weight `1` is preserved. -/
example : clampShift 1 ![(1 : ZMod 5), 2, 0] = 0 := by
  decide

example : clampShift 1 ![(0 : ZMod 5), 2, 0] = ![(0 : ZMod 5), 2, 0] := by
  decide

/-- By Theorem 1 (`weakReuseAdvantage_commonMatrixFuzzyExtractor_le`), on a uniform source at
`m = 4, k = 1, l = 1, q = 7`, the common-matrix FMR construction is `0`-weakly reusable for every
error bound `t` and query count `Q`. -/
example
    (decode : Matrix (Fin 4) (Fin (1 + 1)) (ZMod 7) → (Fin 4 → ZMod 7) →
      ProbComp (Option (Fin (1 + 1) → ZMod 7)))
    (t Q : ℕ) :
    WeakReuseSecureFor (PMF.uniformOfFintype (Matrix (Fin 4) (Fin (1 + 1)) (ZMod 7)))
      (commonMatrixFuzzyExtractor 4 1 1 7 decode)
      {PMF.uniformOfFintype (Fin 4 → ZMod 7)} t Q 0 := by
  intro W hW St adv
  rw [Set.mem_singleton_iff] at hW
  subst hW
  simpa only [lweAdvantage_uniform_error_eq_zero, add_zero] using
    weakReuseAdvantage_commonMatrixFuzzyExtractor_le decode
      (PMF.uniformOfFintype (Fin 4 → ZMod 7)) t Q adv

/-- Concrete instantiation of the Section 3.3 strong-reusability attack at
`m = 3, k = 1, l = 1, q = 5`: a 1-query strong-reusability adversary recovers the key with
probability `1` in the real game (`PMF.pure true`). -/
example
    (decode : Matrix (Fin 3) (Fin (1 + 1)) (ZMod 5) → (Fin 3 → ZMod 5) →
      ProbComp (Option (Fin (1 + 1) → ZMod 5)))
    (hdec : DecoderCorrect decode 0) (W : PMF (Fin 3 → ZMod 5)) :
    strongReuseRealGame (PMF.uniformOfFintype (Matrix (Fin 3) (Fin (1 + 1)) (ZMod 5)))
      (commonMatrixFuzzyExtractor 3 1 1 5 decode) W 0 1
      (commonMatrixStrongAttack decode) = PMF.pure true :=
  strongReuseRealGame_commonMatrixStrongAttack_eq_pure_true hdec _ W

/-! ### Section 5 encryption-based strongly reusable fuzzy extractor -/

/-- Concrete verification of half-modulus encoding and `[3q / 8, 5q / 8]` threshold decoding
modulo `q = 16`: `encodeHalfBit 16 true = 8`, noisy residues `6, 7, 8, 9, 10` decode to `true`,
and noisy residues `15, 0, 1, 2` decode to `false`. -/
example : encodeHalfBit 16 true = (8 : ZMod 16) := by
  decide

example : decodeThresholdBit 16 (7 : ZMod 16) = true := by
  decide

example : decodeThresholdBit 16 (15 : ZMod 16) = false := by
  decide

/-- Concrete round-trip of `symDecrypt` on a 2-bit key modulo `q = 16` with error
`![1, -1]` (each coordinate satisfies `8 * |e_i| + 4 = 12 ≤ 16`). -/
example (s : Fin 2 → ZMod 16) (B : Matrix (Fin 2) (Fin 2) (ZMod 16)) (r : Fin 2 → Bool) :
    symDecrypt s B (B.mulVec s + ![(1 : ZMod 16), (-1 : ZMod 16)] + encodeHalfBits 16 r) = r := by
  apply symDecrypt_symEncrypt_eq
  intro i
  fin_cases i <;> decide

/-- Concrete strong-reusability bound for `lweEncryptFuzzyExtractor` at
`m = 4, n = 2, l = 2, q = 16`: the `Q`-query strong-reusability advantage is bounded by two
decisional LWE advantages with `4 + (Q + 1) * 2` rows. -/
example
    (E : ProbComp (Fin 2 → ZMod 16))
    (decode : Matrix (Fin 4) (Fin 2) (ZMod 16) → (Fin 4 → ZMod 16) →
      ProbComp (Option (Fin 2 → ZMod 16)))
    (W : PMF (Fin 4 → ZMod 16)) (t Q : ℕ) (St : Type)
    (adv : StrongReuseAdversary (Matrix (Fin 4) (Fin 2) (ZMod 16)) 4 16
      (Fin 2 → Bool) (EncryptHelper 4 2 2 16) St) :
    strongReuseAdvantage (PMF.uniformOfFintype (Matrix (Fin 4) (Fin 2) (ZMod 16)))
      (lweEncryptFuzzyExtractor 4 2 2 16 E decode) W t Q adv ≤
      LWE.advantage (PMF.uniformOfFintype (Fin 2 → ZMod 16))
        (encryptLWEErrorLaw W (ProbComp.eval E) Q) (encryptRealReduction t Q adv) +
      LWE.advantage (PMF.uniformOfFintype (Fin 2 → ZMod 16))
        (encryptLWEErrorLaw W (ProbComp.eval E) Q) (encryptIdealReduction t Q adv) :=
  strongReuseAdvantage_lweEncryptFuzzyExtractor_le E decode W t Q adv

/-! ### Section 5: the hypotheses are satisfiable and the bound can be attained -/

/-- A decoder in secret dimension `0`: it always returns the unique secret. -/
def trivialDecode {m q : ℕ} (_ : Matrix (Fin m) (Fin 0) (ZMod q)) (_ : Fin m → ZMod q) :
    ProbComp (Option (Fin 0 → ZMod q)) :=
  return some 0

/-- `trivialDecode` satisfies `DecoderCorrect` at every distance threshold `t`. -/
theorem decoderCorrect_trivialDecode (m q t : ℕ) :
    DecoderCorrect (trivialDecode (m := m) (q := q)) t := by
  intro A s e _ sOpt hsOpt
  simp only [trivialDecode, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hsOpt
  rw [hsOpt, Subsingleton.elim (0 : Fin 0 → ZMod q) s]

/-- Both hypotheses of `lweEncryptFuzzyExtractor_correctHamming` hold for `trivialDecode` and the
zero encryption error at `q = 16`, so the Section 5 scheme is `t`-correct for every `t`: the
threshold decryption recovers the full 2-bit key. -/
example (A : Matrix (Fin 4) (Fin 0) (ZMod 16)) (t : ℕ) :
    (lweEncryptFuzzyExtractor 4 0 2 16 (return 0) trivialDecode A).CorrectHamming t := by
  refine lweEncryptFuzzyExtractor_correctHamming (decoderCorrect_trivialDecode 4 16 t) ?_ A
  intro e he i
  simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at he
  subst he
  simp

/-- With a uniform source and uniform encryption errors, both LWE advantages in
`strongReuseAdvantage_lweEncryptFuzzyExtractor_le` vanish, so every strong-reusability adversary
has advantage exactly `0`: the bound is attained, not vacuous. -/
example
    (decode : Matrix (Fin 4) (Fin 2) (ZMod 16) → (Fin 4 → ZMod 16) →
      ProbComp (Option (Fin 2 → ZMod 16)))
    (t Q : ℕ) (St : Type)
    (adv : StrongReuseAdversary (Matrix (Fin 4) (Fin 2) (ZMod 16)) 4 16
      (Fin 2 → Bool) (EncryptHelper 4 2 2 16) St) :
    strongReuseAdvantage (PMF.uniformOfFintype (Matrix (Fin 4) (Fin 2) (ZMod 16)))
      (lweEncryptFuzzyExtractor 4 2 2 16 (ProbComp.uniform (Fin 2 → ZMod 16)) decode)
      (PMF.uniformOfFintype (Fin 4 → ZMod 16)) t Q adv = 0 := by
  have h := strongReuseAdvantage_lweEncryptFuzzyExtractor_le
    (ProbComp.uniform (Fin 2 → ZMod 16)) decode (PMF.uniformOfFintype (Fin 4 → ZMod 16)) t Q adv
  rw [ProbComp.eval_uniform, encryptLWEErrorLaw_uniform, LWE.advantage_uniform_error_eq_zero,
    LWE.advantage_uniform_error_eq_zero, add_zero] at h
  exact le_antisymm h zero_le

end CslibFrontierTests.Crypto.Computational.FuzzyExtractorTest
