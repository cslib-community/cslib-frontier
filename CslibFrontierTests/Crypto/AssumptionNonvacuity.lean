/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.CompositeResiduosity
import CslibFrontier.Crypto.Computational.DiffieHellman
import CslibFrontier.Crypto.Computational.DiffieHellman.Decodable
import CslibFrontier.Crypto.Computational.DiffieHellman.GapCDH.Assumption
import CslibFrontier.Crypto.Computational.Encryption.CCA
import CslibFrontier.Crypto.Computational.PseudorandomFunction
import CslibFrontier.Crypto.Computational.RabinFactoring
import CslibFrontier.Crypto.Computational.RSAAttacks
import CslibFrontier.Crypto.Computational.RSAUnitInversion
import CslibFrontier.Crypto.Computational.StrongRSA
import CslibFrontier.Probability.Product
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Tactic.PPT
import CslibFrontierTests.Crypto.PrimeOrderGroupFixture

/-!
# The group, encryption and pseudorandom-function assumptions are not vacuous

Each security definition below fails for an obviously insecure instance, so none of them holds
for every candidate. The negative instances for one-way functions, symmetric IND-CPA,
pseudorandom generators and hard-core predicates are elsewhere.

* **Discrete logarithm, CDH, Gap-CDH and DDH.** For every prime-order group family `F` and every
  fixed description `d`, the constant setup `fun _ => PMF.pure d` satisfies none of
  `F.DiscreteLog`, `F.CDH`, `F.WordCDH` and `F.DDH` (nor `F.GapCDH` when `F` is a
  `DecodablePrimeOrderGroupFamily`). Guessing the exponent `0` solves the discrete logarithm with
  probability `1 / q`. Testing whether the first and third elements are both the identity has
  advantage `1 / q - 1 / q²` against DDH. These are constant because the group does not grow with
  the security parameter.
* **IND-CPA and IND-CCA2.** Sending the plaintext bit as the ciphertext is neither `INDCPA` nor
  `INDCCA2`: copying the ciphertext guesses the challenge bit with advantage `1`.
* **Pseudorandom functions.** The family answering every query with zeros of the declared width
  is not a `PseudorandomFunctionOver` on `n`-bit inputs, for any output length that is positive at
  positive parameters: asking for the first answer bit at the zero word has advantage `1 / 2` at
  every positive parameter. At equal input and output lengths it is not a `PseudorandomFunction`
  either.
* **Factoring, Rabin, quadratic residuosity, composite residuosity, and RSA.** For every fixed
  composite modulus `N = p * q` (`1 < p`, `1 < q`), outputting `(p, q)` solves
  `modulusFactoringGame` with probability `1`, so `ModulusFactoringHard` fails for
  `fun _ => PMF.pure (p * q)`. By the factoring-hierarchy reductions, `FactoringHard`,
  `RabinOneWay`, `QuadraticResiduosityHard`, `DCR`, `TotientHard`, `RSAKeyRecoveryHard`, and
  `RSAOneWay` all fail for a fixed modulus or key descriptor `fun _ => PMF.pure d`.
  `RSAUnitOneWay` fails for a fixed key descriptor too: decrypting with its private exponent
  always wins.
* **Strong RSA.** For a fixed modulus `N` and a fixed unit base `g`, `StrongRSA` fails for
  `fun _ => PMF.pure ⟨N, g⟩`: Euler's theorem gives the order multiple `φ(N)`, and the adversary
  of `not_strongRSA_of_orderMultiple` wins with probability `1`.
-/

namespace CslibFrontierTests.Crypto.AssumptionNonvacuity

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.PrimeOrderGroupFamily
  CslibFrontierTests.Crypto.PrimeOrderGroupFixture Turing.MultiTapeTM
open scoped NNReal ENNReal

variable (F : PrimeOrderGroupFamily) (d : F.Desc)

/-! ### Discrete logarithm and CDH -/

/-- **The discrete-logarithm assumption fails for a fixed group.** -/
theorem not_discreteLog_const : ¬ F.DiscreteLog fun _ => PMF.pure d := by
  intro h
  have hneg := h (guessZero F) (guessZero_isPPT F)
  simp only [succProbability_discreteLogGame_guessZero] at hneg
  exact not_negligible_const (inv_ne_zero (Nat.cast_ne_zero.mpr (F.prime_order d).ne_zero)) hneg

/-- **CDH fails for a fixed group**, since it implies the discrete-logarithm assumption. -/
theorem not_cdh_const : ¬ F.CDH fun _ => PMF.pure d :=
  fun h => not_discreteLog_const F d h.discreteLog

/-- **Word-level CDH fails for a fixed group**, since it implies CDH. -/
theorem not_wordCDH_const : ¬ F.WordCDH fun _ => PMF.pure d :=
  fun h => not_cdh_const F d h.cdh

/-- **Gap-CDH fails for a fixed decodable group**, since it implies word-level CDH. -/
theorem not_gapCDH_const (F : DecodablePrimeOrderGroupFamily) (d : F.Desc) :
    ¬ F.GapCDH fun _ => PMF.pure d :=
  fun h => not_wordCDH_const F.toPrimeOrderGroupFamily d h.wordCDH

/-! ### DDH -/

-- `identityTest`, its experiment/game acceptance probabilities (`1 / q` and `1 / q²`), and
-- `not_ddh_const` are exported by `CslibFrontierTests.Crypto.PrimeOrderGroupFixture`.
example (n : ℕ) :
    Game.succProbability (ProbComp.eval
      (ddhRealExperiment (F.order d) (F.generator d) (identityTest F n d))) =
      (F.order d : ℝ≥0)⁻¹ ∧
    Game.succProbability (ProbComp.eval
      (ddhRandomExperiment (F.order d) (F.generator d) (identityTest F n d))) =
      (F.order d : ℝ≥0)⁻¹ ^ 2 ∧
    ¬ F.DDH (fun _ => PMF.pure d) :=
  ⟨succProbability_ddhRealExperiment_identityTest F d n,
   succProbability_ddhRandomExperiment_identityTest F d n,
   not_ddh_const F d⟩

/-! ### IND-CPA and IND-CCA2 -/

/-- The empty key pair. -/
noncomputable def emptyKeys : ℕ → ProbComp (List Bool × List Bool) := fun _ => pure ([], [])

/-- Send the plaintext bit as the ciphertext. -/
noncomputable def plaintext : ℕ → List Bool → Bool → ProbComp (List Bool) := fun _ _ b => pure [b]

/-- Challenge with `false` and `true`, and output the ciphertext's bit. -/
noncomputable def copyCiphertext : Encryption.Adversary where
  choose _ _ := pure ((false, true), [])
  guess _ _ c := pure (c.headD false)

theorem copyCiphertext_isPPT : copyCiphertext.IsPPT where
  choose := (ComputableInPolyTime.const _).isPPTOn
  guess := by
    unfold copyCiphertext
    ppt

/-- Copying the ciphertext recovers the challenge bit. -/
theorem eval_game_copyCiphertext (bit : Bool) (n : ℕ) :
    ProbComp.eval (Encryption.game emptyKeys plaintext copyCiphertext bit n) = PMF.pure bit := by
  cases bit <;>
    simp [Encryption.game, Encryption.gameOn, emptyKeys, plaintext, copyCiphertext]

/-- **Sending the plaintext is not IND-CPA.** -/
theorem not_indcpa_plaintext : ¬ Encryption.INDCPA emptyKeys plaintext := by
  intro h
  have hneg := h copyCiphertext copyCiphertext_isPPT
  simp only [eval_game_copyCiphertext] at hneg
  refine not_negligible_const ?_ hneg
  simp [Game.advantage, Game.succProbability]

/-- **Sending the plaintext is not IND-CCA2**, for any decryption, since IND-CCA2 implies
IND-CPA. -/
theorem not_indcca2_plaintext (decrypt : ℕ → List Bool → List Bool → Option Bool) :
    ¬ Encryption.INDCCA2 emptyKeys plaintext decrypt :=
  fun h => not_indcpa_plaintext h.indcpa

/-! ### Pseudorandom functions -/

/-- The all-zero family with `outLen m`-bit answers: every `m`-bit query gets the zero word of
`outLen m` bits. -/
def zeroFamily (outLen : ℕ → ℕ) : List Bool → List Bool → List Bool :=
  fun _ query => List.replicate (outLen query.length) false

/-- Query the zero word and accept when the first answer bit is `false`. -/
noncomputable def firstBitZero : OracleDistinguisher := fun n _ => do
  let reply ← List.take n <$> ProbOracleComp.query ((), List.replicate n false)
  return !(reply.headD true)

theorem firstBitZero_isOraclePPT : IsOraclePPT encBool firstBitZero := by
  have hq : ComputableInPolyTime (fun p : ℕ × List Bool => List.replicate p.1 false)
      (encPair encUnary encBits) encBits := by
    polytime
  have hlim : ComputableInPolyTime (fun p : ℕ × List Bool => p.1)
      (encPair encUnary encBits) encUnary := by
    fun_prop
  have hout : ComputableInPolyTime (fun p : (ℕ × List Bool) × List Bool => !(p.2.headD true))
      (encPair (encPair encUnary encBits) encBits) encBool := by
    polytime
  unfold firstBitZero
  exact ((IsOraclePPTOn.query_take' () hq hlim).bind_with hout.isOraclePPTOn).isOraclePPT

theorem eval_prfRealGame_firstBitZero {outLen : ℕ → ℕ} (hout : ∀ n, 0 < outLen (n + 1))
    (n : ℕ) :
    ProbComp.eval (prfRealGame id (zeroFamily outLen) firstBitZero (n + 1)) =
      PMF.pure true := by
  obtain ⟨m, hm⟩ : ∃ m, outLen (n + 1) = m + 1 := ⟨outLen (n + 1) - 1, by have := hout n; omega⟩
  simp only [prfRealGame, id_eq, ProbOracleComp.run, firstBitZero, zeroFamily, prfOracle,
    List.length_cons, List.length_replicate, ↓reduceIte, hm, List.replicate_succ,
    List.headD_eq_head?_getD,
    bind_pure_comp, Functor.map_map, OracleComp.interpret_map, ProbOracleComp.interpret_query,
    map_pure, List.take_succ_cons, List.head?_cons, Option.getD_some, ProbComp.eval_map,
    BitString.eval_sampleList]
  exact PMF.map_const _ _

theorem eval_prfIdealGame_firstBitZero {outLen : ℕ → ℕ} (hout : ∀ n, 0 < outLen (n + 1))
    (n : ℕ) :
    ProbComp.eval (prfIdealGame id outLen firstBitZero (n + 1)) =
      PMF.uniformOfFintype Bool := by
  have hhead (word : BitString (outLen (n + 1))) :
      (List.take (n + 1) (List.ofFn word)).headD true = word ⟨0, hout n⟩ := by
    rw [List.headD_eq_head?_getD, List.head?_take, List.head?_eq_getElem?, List.getElem?_ofFn]
    simp [hout n]
  simp only [prfIdealGame, id_eq, ProbOracleComp.run, firstBitZero, randomFunctionOracle,
    bind_pure_comp, Functor.map_map, OracleComp.interpret_map, ProbOracleComp.interpret_query,
    List.length_replicate, ↓reduceIte, map_pure, hhead, ProbComp.eval_map,
    ProbComp.eval_uniform]
  have h1 : (PMF.uniformOfFintype (BitString (n + 1) → BitString (outLen (n + 1)))).map
      (fun table => table (BitString.ofList (n + 1) (List.replicate (n + 1) false))) =
        PMF.uniformOfFintype (BitString (outLen (n + 1))) := by
    rw [← Cslib.Probability.PMF.pi_uniformOfFintype, Cslib.Probability.PMF.pi_map_eval]
  have h2 : (PMF.uniformOfFintype (BitString (outLen (n + 1)))).map
      (fun word => word ⟨0, hout n⟩) = PMF.uniformOfFintype Bool := by
    rw [← Cslib.Probability.PMF.pi_uniformOfFintype, Cslib.Probability.PMF.pi_map_eval]
  have h3 : (PMF.uniformOfFintype Bool).map Bool.not = PMF.uniformOfFintype Bool := by
    ext b
    cases b <;> simp [PMF.map_apply, tsum_fintype, PMF.uniformOfFintype_apply]
  rw [← h3, ← h2, ← h1, PMF.map_comp, PMF.map_comp]
  rfl

/-- **The all-zero family is not a pseudorandom function over `n`-bit inputs**, for any output
length that is positive at positive parameters: at every positive parameter the real experiment
always accepts and the ideal one accepts with probability `1 / 2`. -/
theorem not_pseudorandomFunctionOver_zeroFamily {outLen : ℕ → ℕ}
    (hout : ∀ n, 0 < outLen (n + 1)) :
    ¬ PseudorandomFunctionOver id outLen (zeroFamily outLen) := by
  intro h
  have hneg := h.secure firstBitZero firstBitZero_isOraclePPT
  have hshift : Negligible fun n => Game.advantage
      (ProbComp.eval (prfRealGame id (zeroFamily outLen) firstBitZero (n + 1)))
      (ProbComp.eval (prfIdealGame id outLen firstBitZero (n + 1))) :=
    hneg.shift 1
  simp only [eval_prfRealGame_firstBitZero hout, eval_prfIdealGame_firstBitZero hout]
    at hshift
  refine not_negligible_const ?_ hshift
  norm_num [Game.advantage, Game.succProbability, PMF.uniformOfFintype_apply,
    ENNReal.toNNReal_ofNat]

/-- **The all-zero family is not a pseudorandom function.** `PseudorandomFunction` is the case
`inLen = outLen = id` of `PseudorandomFunctionOver`, where the attack above applies. -/
theorem not_pseudorandomFunction_zeroFamily : ¬ PseudorandomFunction (zeroFamily id) :=
  not_pseudorandomFunctionOver_zeroFamily Nat.succ_pos

/-! ### Factoring, Rabin, quadratic residuosity, composite residuosity, and RSA -/

/-- Always return the fixed factor pair `(p, q)`. -/
def constFactors (p q : ℕ) : ℕ → ℕ → ProbComp (ℕ × ℕ) :=
  fun _ _ => pure (p, q)

theorem constFactors_isPPT (p q : ℕ) :
    IsPPTOn (encPair encUnary encNat) (encPair encNat encNat)
      (fun input => constFactors p q input.1 input.2) :=
  (ComputableInPolyTime.const (p, q)).isPPTOn

theorem eval_modulusFactoringGame_constFactors {p q : ℕ} (hp : 1 < p) (hq : 1 < q) (n : ℕ) :
    modulusFactoringGame (fun _ => PMF.pure (p * q)) (constFactors p q) n = PMF.pure true := by
  simp [modulusFactoringGame, constFactors, hp, hq]

/-- **Integer factoring fails for a fixed composite modulus `p * q`.** -/
theorem not_modulusFactoringHard_const {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    ¬ ModulusFactoringHard (fun _ => PMF.pure (p * q)) := by
  intro h
  have hneg := h (constFactors p q) (constFactors_isPPT p q)
  simp only [eval_modulusFactoringGame_constFactors hp hq] at hneg
  exact not_negligible_const (by simp [Game.succProbability]) hneg

/-- **`FactoringHard` fails for a fixed Blum modulus**, since the factors do not grow with `n`. -/
theorem not_factoringHard_const (desc : BlumDesc) : ¬ FactoringHard (fun _ => PMF.pure desc) := by
  intro h
  have hmod := (factoringHard_iff_modulusFactoringHard (fun _ => PMF.pure desc)).mp h
  simp only [PMF.pure_map] at hmod
  exact not_modulusFactoringHard_const desc.hp.one_lt desc.hq.one_lt hmod

/-- **`RabinOneWay` fails for a fixed Blum modulus**, since it implies `FactoringHard`. -/
theorem not_rabinOneWay_const (desc : BlumDesc) : ¬ RabinOneWay (fun _ => PMF.pure desc) :=
  fun h => not_factoringHard_const desc (factoringHard_of_rabinOneWay h)

/-- **`QuadraticResiduosityHard` fails for a fixed modulus**, since it implies factoring hardness.
-/
theorem not_quadraticResiduosityHard_const (d : ModulusDesc) :
    ¬ QuadraticResiduosityHard (fun _ => PMF.pure d) := by
  intro h
  have hmod := h.modulusFactoringHard
  simp only [PMF.pure_map] at hmod
  exact not_modulusFactoringHard_const d.prime_p.one_lt d.prime_q.one_lt hmod

/-- **`DCR` fails for a fixed balanced modulus**, since it implies factoring hardness. -/
theorem not_dcr_const (d : BalancedModulus.Desc) : ¬ DCR (fun _ => PMF.pure d) := by
  intro h
  have hmod := h.modulusFactoringHard
  simp only [PMF.pure_map] at hmod
  exact not_modulusFactoringHard_const d.2.prime_fst.one_lt d.2.prime_snd.one_lt hmod

/-- **`TotientHard` fails for a fixed RSA descriptor**, since it implies factoring hardness. -/
theorem not_totientHard_const (desc : RSADesc) : ¬ TotientHard (fun _ => PMF.pure desc) := by
  intro h
  have hmod := h.modulusFactoringHard
  simp only [PMF.pure_map] at hmod
  exact not_modulusFactoringHard_const desc.hp.one_lt desc.hq.one_lt hmod

/-- **`RSAKeyRecoveryHard` fails for a fixed RSA descriptor**, since it implies `TotientHard`. -/
theorem not_rsaKeyRecoveryHard_const (desc : RSADesc) :
    ¬ RSAKeyRecoveryHard (fun _ => PMF.pure desc) :=
  fun h => not_totientHard_const desc h.totientHard

/-- **`RSAOneWay` fails for a fixed RSA descriptor**, since it implies `RSAKeyRecoveryHard`. -/
theorem not_rsaOneWay_const (desc : RSADesc) : ¬ RSAOneWay (fun _ => PMF.pure desc) :=
  fun h => not_rsaKeyRecoveryHard_const desc h.rsaKeyRecoveryHard

/-- **`RSAUnitOneWay` fails for a fixed RSA descriptor**: decrypting every challenge with the fixed
private exponent `desc.d` recovers the unit with probability `1`. -/
theorem not_rsaUnitOneWay_const (desc : RSADesc) : ¬ RSAUnitOneWay (fun _ => PMF.pure desc) := by
  intro h
  have hneg := h (keyRecoveryToRSA fun _ _ => pure desc.d)
    (isPPT_keyRecoveryToRSA (ComputableInPolyTime.const desc.d).isPPTOn)
  have hwin (x : (ZMod desc.modulus)ˣ) :
      (⟨rsaInvert desc.modulus desc.d (rsaEval desc.modulus desc.e (desc.unitResidue x)),
        Nat.mod_lt _ desc.modulus_pos⟩ : Fin desc.modulus) = desc.unitResidue x :=
    Fin.ext (rsaInvert_rsaEval desc (desc.unitResidue x).isLt)
  have hone (n : ℕ) : Game.succProbability (rsaUnitInversionGame (fun _ => PMF.pure desc)
      (keyRecoveryToRSA fun _ _ => pure desc.d) n) = 1 := by
    rw [rsaUnitInversionGame_eq]
    simp [keyRecoveryToRSA, hwin, Game.succProbability]
  simp only [hone] at hneg
  exact not_negligible_const one_ne_zero hneg

/-- **`StrongRSA` fails for a fixed modulus and a fixed unit base**: by Euler's theorem
`g ^ φ(N) ≡ 1 [MOD N]`, so the order-multiple adversary with `u = max 1 φ(N)` wins with
probability `1`. For `N = 0` the only unit is `g = 1`. The unit condition is needed
(`strongRSA_const_four_two` in `CslibFrontierTests/Crypto/StrongRSA.lean`). -/
theorem not_strongRSA_const {N g : ℕ} (hg : Nat.Coprime g N) :
    ¬ StrongRSA fun _ => PMF.pure ⟨N, g⟩ := by
  refine not_strongRSA_of_orderMultiple (u := fun _ _ => max 1 N.totient)
    (ComputableInPolyTime.const _) fun n p hp => ?_
  obtain rfl : p = ⟨N, g⟩ := by simpa using hp
  refine ⟨by simp, ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain rfl : g = 1 := Nat.coprime_zero_right _ |>.mp hg
    simp [Nat.ModEq.refl]
  · rw [max_eq_right (Nat.totient_pos.mpr hN)]
    exact Nat.ModEq.pow_totient hg

end CslibFrontierTests.Crypto.AssumptionNonvacuity
