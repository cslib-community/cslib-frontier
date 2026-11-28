/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.Commitment.Basic
import CslibFrontier.Crypto.Computational.CompositeResiduosity
import CslibFrontier.Crypto.Computational.DiffieHellman
import CslibFrontier.Crypto.Computational.DiffieHellman.Decodable
import CslibFrontier.Crypto.Computational.DiffieHellman.GapCDH.Assumption
import CslibFrontier.Crypto.Computational.DiffieHellman.MultiDDH
import CslibFrontier.Crypto.Computational.Encryption.CCA
import CslibFrontier.Crypto.Computational.OneWay.Weak
import CslibFrontier.Crypto.Computational.PseudorandomFunction
import CslibFrontier.Crypto.Computational.PseudorandomFunction.CircuitLowerBound
import CslibFrontier.Crypto.Computational.PseudorandomFunction.PrefixFree
import CslibFrontier.Crypto.Computational.PseudorandomPermutation
import CslibFrontier.Crypto.Computational.RabinFactoring
import CslibFrontier.Crypto.Computational.RSAAttacks
import CslibFrontier.Crypto.Computational.RSAUnitInversion
import CslibFrontier.Crypto.Computational.StrongRSA
import CslibFrontier.Crypto.Computational.WeakPRF
import CslibFrontier.Probability.Product
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Tactic.PPT
import CslibFrontierTests.Crypto.PrimeOrderGroupFixture

/-!
# The group, encryption and pseudorandom-function assumptions are not vacuous

Each security definition below fails for an obviously insecure instance, so none of them holds
for every candidate. The negative instances for one-way functions, symmetric IND-CPA,
pseudorandom generators, hard-core predicates and zero-knowledge assumptions are elsewhere.

* **Discrete logarithm, CDH, Gap-CDH, DDH and Multi-DDH.** For every prime-order group family `F`
  and every fixed description `d`, the constant setup `fun _ => PMF.pure d` satisfies none of
  `F.DiscreteLog`, `F.CDH`, `F.WordCDH`, `F.DDH`, `F.SingleSecretMultiDDH _ (fun _ => 1)` and
  `F.MultiDDH _ (fun _ => 1) (fun _ => 1)` (nor `F.GapCDH` when `F` is a
  `DecodablePrimeOrderGroupFamily`). Guessing the exponent `0` solves the discrete logarithm with
  probability `1 / q`. Testing whether the first and third elements are both the identity has
  advantage `1 / q - 1 / q²` against DDH; testing whether the single-pair Multi-DDH tuple is all
  identity has advantage `1 / q² - 1 / q³`. These are constant because the group does not grow with
  the security parameter.
* **IND-CPA and IND-CCA2.** Sending the plaintext bit as the ciphertext is neither `INDCPA` nor
  `INDCCA2`: copying the ciphertext guesses the challenge bit with advantage `1`.
* **Pseudorandom functions, weak PRFs, Boolean PRFs and block ciphers (PRP / strong PRP).** The
  family answering every query with zeros of the declared width is not a
  `PseudorandomFunctionOver` on `n`-bit inputs, for any output length that is positive at positive
  parameters: asking for the first answer bit at the zero word has advantage `1 / 2` at every
  positive parameter. At equal input and output lengths it is neither a `PseudorandomFunction` nor
  a `WeakPseudorandomFunction`, and the constant-false ensemble is not a `BooleanPRF`. The identity
  block cipher `idBlockCipher` is neither a `BlockCipher.PRP` nor a `BlockCipher.StrongPRP`.
* **Weak one-way functions and commitment hiding.** The identity function fails `WeakOneWayAt`
  for every eventually positive failure threshold `α`, and committing to a message in the clear
  fails both `CommitmentScheme.ComputationalHiding` and `CommitmentScheme.StatisticalHiding`.
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
  exact ((IsOraclePPTOn.query_take () hq hlim).bind_with hout.isOraclePPTOn).isOraclePPT

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
  rw [← Cslib.Probability.PMF.uniformOfFintype_map_equiv Bool.involutive_not.toPerm, ← h2, ← h1,
    PMF.map_comp, PMF.map_comp]
  rfl

private theorem not_negligible_advantage_firstBitZero {outLen : ℕ → ℕ}
    (hout : ∀ n, 0 < outLen (n + 1)) :
    ¬ Negligible (fun n => Game.advantage
      (ProbComp.eval (prfRealGame id (zeroFamily outLen) firstBitZero n))
      (ProbComp.eval (prfIdealGame id outLen firstBitZero n))) := by
  intro hneg
  have hshift : Negligible fun n => Game.advantage
      (ProbComp.eval (prfRealGame id (zeroFamily outLen) firstBitZero (n + 1)))
      (ProbComp.eval (prfIdealGame id outLen firstBitZero (n + 1))) :=
    hneg.shift 1
  simp only [eval_prfRealGame_firstBitZero hout, eval_prfIdealGame_firstBitZero hout]
    at hshift
  refine not_negligible_const ?_ hshift
  norm_num [Game.advantage, Game.succProbability, PMF.uniformOfFintype_apply,
    ENNReal.toNNReal_ofNat]

/-- **The all-zero family is not a pseudorandom function over `n`-bit inputs**, for any output
length that is positive at positive parameters: at every positive parameter the real experiment
always accepts and the ideal one accepts with probability `1 / 2`. -/
theorem not_pseudorandomFunctionOver_zeroFamily {outLen : ℕ → ℕ}
    (hout : ∀ n, 0 < outLen (n + 1)) :
    ¬ PseudorandomFunctionOver id outLen (zeroFamily outLen) :=
  fun h => not_negligible_advantage_firstBitZero hout
    (h.secure firstBitZero firstBitZero_isOraclePPT)

/-- **The all-zero family is not a pseudorandom function.** `PseudorandomFunction` is the case
`inLen = outLen = id` of `PseudorandomFunctionOver`, where the attack above applies. -/
theorem not_pseudorandomFunction_zeroFamily : ¬ PseudorandomFunction (zeroFamily id) :=
  not_pseudorandomFunctionOver_zeroFamily Nat.succ_pos

/-- The same one-query test refutes prefix-free PRF security on the domain of `n`-bit words.
Its query is nonempty at every positive parameter, where its advantage is `1 / 2`. -/
theorem not_prefixFreePseudorandomFunctionOn_zeroFamily :
    ¬ PrefixFreePseudorandomFunctionOn (fun n word => word.length == id n) id (zeroFamily id) := by
  intro h
  have hpf : IsPrefixFreeOraclePPT (fun n word => word.length == id n) id firstBitZero := by
    refine ⟨firstBitZero_isOraclePPT, fun n => isPrefixFreeOn_of_fixedLength ?_ _⟩
    intro u v hu hv
    exact (beq_iff_eq.mp hu).trans (beq_iff_eq.mp hv).symm
  apply not_negligible_advantage_firstBitZero (outLen := id) Nat.succ_pos
  simpa only [eval_prfRealGameOn_length_eq, eval_prfIdealGameOn_length_eq] using
    h.secure firstBitZero hpf

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
  exact not_modulusFactoringHard_const d.property.prime_fst.one_lt d.property.prime_snd.one_lt hmod

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

/-! ### Multi-DDH -/

/-- Accept when `u = 0` and the single-secret pair list equals `[(0, 0)]`. -/
noncomputable def singleSecretAllZeroTest : F.SingleSecretMultiDDHDistinguisher :=
  fun _ _ u pairs => pure (decide (u = 0) && decide (pairs = [(0, 0)]))

theorem singleSecretAllZeroTest_isPPT : (singleSecretAllZeroTest F).IsPPT := by
  have henc : ComputableInPolyTime
      (fun x : F.SingleSecretMultiDDHInput =>
        decide (F.encode x.groupParameters x.leftPublic = F.encode x.groupParameters 0) &&
        decide (encList (F.encCarrierPair x.groupParameters) x.pairs =
          encList (encPair encBits encBits)
            [(F.encode x.groupParameters 0, F.encode x.groupParameters 0)]))
      F.encSingleSecretMultiDDHInput encBool := by
    fun_prop
  refine henc.isPPTOn.congr fun x => ?_
  have hzero :
      encList (encPair encBits encBits)
          [(F.encode x.groupParameters 0, F.encode x.groupParameters 0)] =
        encList (F.encCarrierPair x.groupParameters) [(0, 0)] := by
    rw [F.encList_encCarrierPair]
    rfl
  simp only [singleSecretAllZeroTest, hzero, (F.encode_injective _).eq_iff,
    (encList (F.encCarrierPair x.groupParameters)).injective.eq_iff]

/-- Accept when the Multi-DDH block list equals `[(0, [(0, 0)])]`. -/
noncomputable def multiDDHAllZeroTest : F.MultiDDHDistinguisher :=
  fun _ _ blocks => pure (decide (blocks = [(0, [(0, 0)])]))

theorem multiDDHAllZeroTest_isPPT : (multiDDHAllZeroTest F).IsPPT := by
  have hz : ComputableInPolyTime (fun x : F.MultiDDHInput => F.encode x.groupParameters 0)
      F.encMultiDDHInput encBits := by
    fun_prop
  have hjoin : ComputableInPolyTime (fun p : List Bool × List Bool => frame p.1 ++ p.2)
      (encPair encBits encBits) encBits :=
    ComputableInPolyTime.of_eq fun _ => rfl
  have hfmt : ComputableInPolyTime
      (fun z : List Bool => frame (frame z ++ frame (frame z ++ z))) encBits encBits :=
    ComputableInPolyTime.frame.comp
      (hjoin.comp (ComputableInPolyTime.id'.prod
        (ComputableInPolyTime.frame.comp
          (hjoin.comp (ComputableInPolyTime.id'.prod ComputableInPolyTime.id')))))
  have hzeroEnc : ComputableInPolyTime
      (fun x : F.MultiDDHInput =>
        let z := F.encode x.groupParameters 0
        frame (frame z ++ frame (frame z ++ z)))
      F.encMultiDDHInput encBits :=
    hfmt.comp hz
  have hblocks : ComputableInPolyTime
      (fun x : F.MultiDDHInput => encList (F.encMultiDDHBlock x.groupParameters) x.blocks)
      F.encMultiDDHInput encBits :=
    F.encMultiDDHInput_blocks_polyTime .id'
  have heq : ComputableInPolyTime (fun p : List Bool × List Bool => decide (p.1 = p.2))
      (encPair encBits encBits) encBool := by
    fun_prop
  have henc : ComputableInPolyTime
      (fun x : F.MultiDDHInput =>
        let z := F.encode x.groupParameters 0
        decide (encList (F.encMultiDDHBlock x.groupParameters) x.blocks =
          frame (frame z ++ frame (frame z ++ z))))
      F.encMultiDDHInput encBool :=
    heq.comp (hblocks.prod hzeroEnc)
  refine henc.isPPTOn.congr fun x => ?_
  have hzero :
      let z := F.encode x.groupParameters 0
      frame (frame z ++ frame (frame z ++ z)) =
        encList (F.encMultiDDHBlock x.groupParameters) [(0, [(0, 0)])] := by
    rw [F.encList_encMultiDDHBlock]
    simp
  simp only [multiDDHAllZeroTest, hzero,
    (encList (F.encMultiDDHBlock x.groupParameters)).injective.eq_iff]

private theorem succProbability_singleSecretReal_allZero (n : ℕ) :
    Game.succProbability
      (F.singleSecretMultiDDHRealGame (fun _ => PMF.pure d) (fun _ => 1)
        (singleSecretAllZeroTest F) n) =
      (F.order d : ℝ≥0)⁻¹ ^ 2 := by
  have hcond (α : ZMod (F.order d)) (B : Fin 1 → ZMod (F.order d)) :
      (decide (α • F.generator d = 0) &&
        decide (List.ofFn (fun i : Fin 1 =>
          (B i • F.generator d, (α * B i) • F.generator d)) = [(0, 0)])) =
        decide (α = 0 ∧ B = 0) := by
    simp only [List.ofFn_succ, List.ofFn_zero, List.cons.injEq, and_true, Prod.mk.injEq,
      smul_eq_zero, F.generator_ne_zero, or_false, funext_iff, Fin.forall_fin_one, Pi.zero_apply]
    by_cases hα : α = 0 <;> by_cases hB : B 0 = 0 <;> simp [hα, hB]
  simp only [singleSecretMultiDDHRealGame, multiDDHRealTupleLaw, singleSecretAllZeroTest,
    PMF.monad_bind_eq_bind, PMF.pure_bind, PMF.bind_map, ProbComp.eval_pure, Function.comp_def,
    hcond]
  rw [Game.succProbability, ← ENNReal.toNNReal_natCast, ← ENNReal.toNNReal_inv,
    ← ENNReal.toNNReal_pow]
  congr 1
  have hcard : Fintype.card (Fin 1 → ZMod (F.order d)) = F.order d := by
    simp [ZMod.card]
  simp [PMF.bind_apply, tsum_fintype, PMF.uniformOfFintype_apply, PMF.pure_apply, ite_and,
    ZMod.card, hcard, Finset.sum_ite_eq', sq]

private theorem succProbability_singleSecretRandom_allZero (n : ℕ) :
    Game.succProbability
      (F.singleSecretMultiDDHRandomGame (fun _ => PMF.pure d) (fun _ => 1)
        (singleSecretAllZeroTest F) n) =
      (F.order d : ℝ≥0)⁻¹ ^ 3 := by
  have hcond (α : ZMod (F.order d)) (B : Fin 1 → ZMod (F.order d) × ZMod (F.order d)) :
      (decide (α • F.generator d = 0) &&
        decide (List.ofFn (fun i : Fin 1 =>
          ((B i).1 • F.generator d, (B i).2 • F.generator d)) = [(0, 0)])) =
        decide (α = 0 ∧ B = fun _ => (0, 0)) := by
    simp only [List.ofFn_succ, List.ofFn_zero, List.cons.injEq, and_true,
      smul_eq_zero, F.generator_ne_zero, or_false, funext_iff, Fin.forall_fin_one, Prod.ext_iff]
    by_cases hα : α = 0 <;> by_cases h1 : (B 0).1 = 0 <;> by_cases h2 : (B 0).2 = 0 <;>
      simp [hα, h1, h2]
  simp only [singleSecretMultiDDHRandomGame, multiDDHRandomTupleLaw, singleSecretAllZeroTest,
    PMF.monad_bind_eq_bind, PMF.pure_bind, PMF.bind_map, ProbComp.eval_pure, Function.comp_def,
    hcond]
  rw [Game.succProbability, ← ENNReal.toNNReal_natCast, ← ENNReal.toNNReal_inv,
    ← ENNReal.toNNReal_pow]
  congr 1
  have hcard : Fintype.card (Fin 1 → ZMod (F.order d) × ZMod (F.order d)) = F.order d ^ 2 := by
    simp [ZMod.card, sq]
  simp [PMF.bind_apply, tsum_fintype, PMF.uniformOfFintype_apply, PMF.pure_apply, ite_and,
    ZMod.card, hcard, Finset.sum_ite_eq', ENNReal.inv_pow]
  ring

private theorem inv_sq_ne_inv_cube :
    (F.order d : ℝ≥0)⁻¹ ^ 2 ≠ (F.order d : ℝ≥0)⁻¹ ^ 3 := by
  have hgt : (1 : ℝ≥0) < (F.order d : ℝ≥0) := by
    exact_mod_cast (F.prime_order d).one_lt
  have hpos : (0 : ℝ≥0) < (F.order d : ℝ≥0) := zero_lt_one.trans hgt
  have hlt : (F.order d : ℝ≥0)⁻¹ ^ 3 < (F.order d : ℝ≥0)⁻¹ ^ 2 := by
    have hinv_lt : (F.order d : ℝ≥0)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hgt
    have hinv_sq_pos : (0 : ℝ≥0) < (F.order d : ℝ≥0)⁻¹ ^ 2 := pow_pos (inv_pos.mpr hpos) 2
    calc (F.order d : ℝ≥0)⁻¹ ^ 3
        = (F.order d : ℝ≥0)⁻¹ ^ 2 * (F.order d : ℝ≥0)⁻¹ := by ring
      _ < (F.order d : ℝ≥0)⁻¹ ^ 2 * 1 := mul_lt_mul_of_pos_left hinv_lt hinv_sq_pos
      _ = (F.order d : ℝ≥0)⁻¹ ^ 2 := mul_one _
  exact ne_of_gt hlt

/-- **`SingleSecretMultiDDH` fails for a fixed group**: testing whether the single pair is all
identity has constant advantage `1 / q² - 1 / q³ > 0`. -/
theorem not_singleSecretMultiDDH_const :
    ¬ F.SingleSecretMultiDDH (fun _ => PMF.pure d) (fun _ => 1) := by
  intro h
  have hneg := h (singleSecretAllZeroTest F) (singleSecretAllZeroTest_isPPT F)
  simp only [Game.advantage, succProbability_singleSecretReal_allZero,
    succProbability_singleSecretRandom_allZero] at hneg
  exact not_negligible_const (mt nndist_eq_zero.mp (inv_sq_ne_inv_cube F d)) hneg

/-- **`MultiDDH` fails for a fixed group**: with one secret and one pair, testing whether the
sole block is `(0, [(0, 0)])` has the same constant advantage `1 / q² - 1 / q³ > 0`. -/
theorem not_multiDDH_const :
    ¬ F.MultiDDH (fun _ => PMF.pure d) (fun _ => 1) (fun _ => 1) := by
  intro h
  have hneg := h (multiDDHAllZeroTest F) (multiDDHAllZeroTest_isPPT F)
  have hreal (n : ℕ) :
      F.multiDDHRealGame (fun _ => PMF.pure d) (fun _ => 1) (fun _ => 1)
        (multiDDHAllZeroTest F) n =
      F.singleSecretMultiDDHRealGame (fun _ => PMF.pure d) (fun _ => 1)
        (singleSecretAllZeroTest F) n := by
    simp only [multiDDHRealGame, singleSecretMultiDDHRealGame, multiDDHRealBlockLaw,
      multiDDHAllZeroTest, singleSecretAllZeroTest, PMF.iid, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.pure_bind, PMF.bind_bind, PMF.pure_map,
      ProbComp.eval_pure, List.ofFn_succ, List.ofFn_zero, Fin.cons_zero, List.cons.injEq,
      and_true, Prod.mk.injEq, Bool.decide_and]
  have hrand (n : ℕ) :
      F.multiDDHRandomGame (fun _ => PMF.pure d) (fun _ => 1) (fun _ => 1)
        (multiDDHAllZeroTest F) n =
      F.singleSecretMultiDDHRandomGame (fun _ => PMF.pure d) (fun _ => 1)
        (singleSecretAllZeroTest F) n := by
    simp only [multiDDHRandomGame, singleSecretMultiDDHRandomGame, multiDDHRandomBlockLaw,
      multiDDHAllZeroTest, singleSecretAllZeroTest, PMF.iid, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.pure_bind, PMF.bind_bind, PMF.pure_map,
      ProbComp.eval_pure, List.ofFn_succ, List.ofFn_zero, Fin.cons_zero, List.cons.injEq,
      and_true, Prod.mk.injEq, Bool.decide_and]
  simp only [hreal, hrand, Game.advantage, succProbability_singleSecretReal_allZero,
    succProbability_singleSecretRandom_allZero] at hneg
  exact not_negligible_const (mt nndist_eq_zero.mp (inv_sq_ne_inv_cube F d)) hneg

/-! ### Boolean PRFs, weak PRFs, and block ciphers (`PRP` / `StrongPRP`) -/

/-- The constant-false Boolean function ensemble on `n` bits. -/
noncomputable def constFalseBooleanEnsemble : ∀ n, PMF (BooleanFunction n) :=
  fun _ => PMF.pure (fun _ => false)

/-- **`BooleanPRF` fails for the constant-false ensemble**: querying the zero word and checking
that the reply bit is `false` succeeds with probability `1` in the real game and `1 / 2` in the
ideal game at every positive parameter. -/
theorem not_booleanPRF_constFalse : ¬ BooleanPRF constFalseBooleanEnsemble := by
  intro h
  have hshift := (h firstBitZero firstBitZero_isOraclePPT).shift 1
  have heval (n : ℕ) (f : BooleanFunction (n + 1)) :
      evalBooleanOracle firstBitZero (n + 1) f =
        PMF.pure !(f (BitString.ofList (n + 1) (List.replicate (n + 1) false))) := by
    simp only [evalBooleanOracle, booleanOracle, ProbOracleComp.run, firstBitZero,
      List.length_replicate, ↓reduceIte, bind_pure_comp, Functor.map_map,
      OracleComp.interpret_map, ProbOracleComp.interpret_query, map_pure, List.take_succ_cons,
      List.headD_eq_head?_getD, List.head?_cons, Option.getD_some, ProbComp.eval_pure]
  have hreal (n : ℕ) :
      booleanPRFRealGame constFalseBooleanEnsemble firstBitZero (n + 1) = PMF.pure true := by
    simp only [booleanPRFRealGame, constFalseBooleanEnsemble, PMF.pure_bind, heval]
    rfl
  have hideal (n : ℕ) :
      booleanPRFIdealGame firstBitZero (n + 1) = PMF.uniformOfFintype Bool := by
    rw [booleanPRFIdealGame,
      show evalBooleanOracle firstBitZero (n + 1) =
          fun f => PMF.pure !(f (BitString.ofList (n + 1) (List.replicate (n + 1) false)))
        from funext (heval n)]
    have h1 : (PMF.uniformOfFintype (BooleanFunction (n + 1))).map
        (fun f => f (BitString.ofList (n + 1) (List.replicate (n + 1) false))) =
          PMF.uniformOfFintype Bool := by
      rw [← Cslib.Probability.PMF.pi_uniformOfFintype, Cslib.Probability.PMF.pi_map_eval]
    change (PMF.uniformOfFintype (BooleanFunction (n + 1))).map
        (fun f => !(f (BitString.ofList (n + 1) (List.replicate (n + 1) false)))) = _
    rw [← Cslib.Probability.PMF.uniformOfFintype_map_equiv Bool.involutive_not.toPerm, ← h1,
      PMF.map_comp]
    rfl
  simp only [hreal, hideal] at hshift
  refine not_negligible_const ?_ hshift
  norm_num [Game.advantage, Game.succProbability, PMF.uniformOfFintype_apply,
    ENNReal.toNNReal_ofNat]

/-- Request one weak-PRF sample `(point, answer)` and accept when the first bit of `answer`
(index `n` of the `2n`-bit sample) is `false`. -/
noncomputable def weakAnswerFirstBitZero : OracleDistinguisher := fun n _ => do
  let reply ← List.take (2 * n) <$> ProbOracleComp.query ((), [])
  return !(reply.getD n true)

theorem weakAnswerFirstBitZero_isOraclePPT : IsOraclePPT encBool weakAnswerFirstBitZero := by
  have hq : ComputableInPolyTime (fun _ : ℕ × List Bool => ([] : List Bool))
      (encPair encUnary encBits) encBits := ComputableInPolyTime.const []
  have hlim : ComputableInPolyTime (fun p : ℕ × List Bool => 2 * p.1)
      (encPair encUnary encBits) encUnary := by
    fun_prop
  have hout : ComputableInPolyTime (fun p : (ℕ × List Bool) × List Bool => !(p.2.getD p.1.1 true))
      (encPair (encPair encUnary encBits) encBits) encBool := by
    polytime
  unfold weakAnswerFirstBitZero
  exact ((IsOraclePPTOn.query_take () hq hlim).bind_with hout.isOraclePPTOn).isOraclePPT

/-- **`WeakPseudorandomFunction` fails for the all-zero family**: reading the first answer bit of
one weak sample accepts with probability `1` in the real game and `1 / 2` in the ideal game at
every positive parameter. -/
theorem not_weakPseudorandomFunction_zeroFamily :
    ¬ WeakPseudorandomFunction (zeroFamily id) := by
  intro h
  have hshift := (h.secure weakAnswerFirstBitZero weakAnswerFirstBitZero_isOraclePPT).shift 1
  have hreal (n : ℕ) :
      ProbComp.eval (weakPrfRealGame (zeroFamily id) weakAnswerFirstBitZero (n + 1)) =
        PMF.pure true := by
    have hbit (point : List Bool) (hp : point.length = n + 1) :
        ((point ++ List.replicate (n + 1) false).take (2 * (n + 1))).getD (n + 1) true = false := by
      have hlen : (point ++ List.replicate (n + 1) false).length = 2 * (n + 1) := by
        simp [hp]; omega
      rw [List.take_of_length_le hlen.le, List.getD_eq_getElem?_getD, List.getElem?_append_right
        (by omega)]
      simp [hp]
    simp only [weakPrfRealGame, weakSample, ProbOracleComp.run, weakAnswerFirstBitZero,
      bind_pure_comp, Functor.map_map, OracleComp.interpret_map, ProbOracleComp.interpret_query,
      ProbComp.eval_bind, BitString.eval_sampleList, ProbComp.eval_map]
    refine (PMF.bind_congr_on_support _ _ (fun _ => PMF.pure true) fun key _ => ?_).trans
      (PMF.bind_const _ _)
    refine (PMF.bind_congr_on_support _ _ (fun _ => PMF.pure true) fun point hp => ?_).trans
      (PMF.bind_const _ _)
    have hplen : point.length = n + 1 := BitString.length_of_mem_support_uniformList hp
    simp only [Function.comp_apply, prfOracle, zeroFamily, id_eq, hplen, ↓reduceIte,
      hbit point hplen, Bool.not_false]
  have hideal (n : ℕ) :
      ProbComp.eval (weakPrfIdealGame weakAnswerFirstBitZero (n + 1)) =
        PMF.uniformOfFintype Bool := by
    have hbit (point : List Bool) (hp : point.length = n + 1) (word : BitString (n + 1)) :
        ((point ++ List.ofFn word).take (2 * (n + 1))).getD (n + 1) true =
          word ⟨0, Nat.succ_pos n⟩ := by
      have hlen : (point ++ List.ofFn word).length = 2 * (n + 1) := by
        simp [hp]; omega
      rw [List.take_of_length_le hlen.le, List.getD_eq_getElem?_getD, List.getElem?_append_right
        (by omega)]
      simp [hp]
    simp only [weakPrfIdealGame, weakSample, ProbOracleComp.run, weakAnswerFirstBitZero,
      bind_pure_comp, Functor.map_map, OracleComp.interpret_map, ProbOracleComp.interpret_query,
      ProbComp.eval_bind, ProbComp.eval_uniform, BitString.eval_sampleList, ProbComp.eval_map,
      PMF.map]
    rw [PMF.bind_comm]
    refine (PMF.bind_congr_on_support _ _ (fun _ => PMF.uniformOfFintype Bool)
      fun point hp => ?_).trans (PMF.bind_const _ _)
    have hplen : point.length = n + 1 := BitString.length_of_mem_support_uniformList hp
    have h1 : (PMF.uniformOfFintype (BitString (n + 1) → BitString (n + 1))).map
        (fun table => table (BitString.ofList (n + 1) point)) =
          PMF.uniformOfFintype (BitString (n + 1)) := by
      rw [← Cslib.Probability.PMF.pi_uniformOfFintype, Cslib.Probability.PMF.pi_map_eval]
    have h2 : (PMF.uniformOfFintype (BitString (n + 1))).map
        (fun word => word ⟨0, Nat.succ_pos n⟩) = PMF.uniformOfFintype Bool := by
      rw [← Cslib.Probability.PMF.pi_uniformOfFintype, Cslib.Probability.PMF.pi_map_eval]
    simp only [Function.comp_apply, randomFunctionOracle, hplen, ↓reduceIte, hbit point hplen]
    change (PMF.uniformOfFintype (BitString (n + 1) → BitString (n + 1))).map
      (fun table => !(table (BitString.ofList (n + 1) point) ⟨0, Nat.succ_pos n⟩)) = _
    rw [← Cslib.Probability.PMF.uniformOfFintype_map_equiv Bool.involutive_not.toPerm, ← h2, ← h1,
      PMF.map_comp, PMF.map_comp]
    rfl
  simp only [hreal, hideal] at hshift
  refine not_negligible_const ?_ hshift
  norm_num [Game.advantage, Game.succProbability, PMF.uniformOfFintype_apply,
    ENNReal.toNNReal_ofNat]

/-- The identity block cipher with `keyLen = blockLen = id`: `encrypt _ _ x = x`. -/
def idBlockCipher : BlockCipher where
  keyLen := id
  blockLen := id
  keyLen_polyTime := ComputableInPolyTime.id'
  blockLen_polyTime := ComputableInPolyTime.id'
  encrypt _ _ x := x
  decrypt _ _ y := y
  encrypt_polyTime := by polytime
  decrypt_polyTime := by polytime
  length_encrypt _ _ _ _ hx := hx
  length_decrypt _ _ _ _ hy := hy
  decrypt_encrypt _ _ _ _ _ := rfl
  encrypt_decrypt _ _ _ _ _ := rfl

/-- **`BlockCipher.PRP` fails for the identity block cipher**: by the PRP/PRF switching lemma,
`idBlockCipher.PRP` would make `fun _ x => x` a PRF, refuted by `firstBitZero` on `0^{n+1}`. -/
theorem not_prp_idBlockCipher : ¬ idBlockCipher.PRP := by
  intro hprp
  have hprf : PseudorandomFunctionOver id id (fun _ query => query) :=
    (BlockCipher.prp_iff_pseudorandomFunctionOver_of_keyLen_eq_id (E := idBlockCipher)
      rfl negligible_inv_two_pow).mp hprp
  have hshift := (hprf.secure firstBitZero firstBitZero_isOraclePPT).shift 1
  have hreal (n : ℕ) :
      ProbComp.eval (prfRealGame id (fun _ query => query) firstBitZero (n + 1)) =
        PMF.pure true := by
    simp only [prfRealGame, id_eq, ProbOracleComp.run, firstBitZero, prfOracle,
      List.length_cons, List.length_replicate, ↓reduceIte, List.replicate_succ,
      List.headD_eq_head?_getD, bind_pure_comp, Functor.map_map, OracleComp.interpret_map,
      ProbOracleComp.interpret_query, map_pure, List.take_succ_cons, List.head?_cons,
      Option.getD_some, ProbComp.eval_map, BitString.eval_sampleList]
    exact PMF.map_const _ _
  simp only [hreal, eval_prfIdealGame_firstBitZero (outLen := id) Nat.succ_pos] at hshift
  refine not_negligible_const ?_ hshift
  norm_num [Game.advantage, Game.succProbability, PMF.uniformOfFintype_apply,
    ENNReal.toNNReal_ofNat]

/-- **`BlockCipher.StrongPRP` fails for the identity block cipher**, since strong PRP security
implies PRP security. -/
theorem not_strongPRP_idBlockCipher : ¬ idBlockCipher.StrongPRP :=
  fun h => not_prp_idBlockCipher h.prp

/-! ### Weak one-way functions and commitment hiding -/

/-- **`WeakOneWayAt` fails for the identity function** at every eventually positive failure
threshold `α`. -/
theorem not_weakOneWayAt_id {α : ℕ → ℝ} (hα : ∀ᶠ n in Filter.atTop, 0 < α n) :
    ¬ WeakOneWayAt id α :=
  not_weakOneWayAt_of_inverse hα (fun _ y => y)
    (ComputableInPolyTime.id' (encIn := encBits)).isPPT (fun _ => rfl)

/-- Trivial commitment scheme that reveals the message verbatim as the commitment string. -/
noncomputable def plaintextCommitment : CommitmentScheme Unit where
  encodeKey := ⟨fun _ => [], fun _ _ _ => rfl⟩
  ValidMessage _ _ := True
  commitDist _ m := PMF.pure (m, [])
  verify _ m c _ := decide (c = m)
  validMessage_of_verify _ _ _ _ _ := trivial
  verify_of_mem_support _ m co _ hco := by
    simp only [PMF.support_pure, Set.mem_singleton_iff] at hco
    simp [hco]

/-- Challenge `plaintextCommitment` with `([false], [true])` and output the first commitment bit.
-/
noncomputable def copyCommitmentBit : Encryption.WordAdversary where
  choose _ _ := pure (([false], [true]), [])
  guess _ _ c := pure (c.headD false)

theorem copyCommitmentBit_isPPT : copyCommitmentBit.IsPPT :=
  ⟨(ComputableInPolyTime.const _).isPPTOn, by unfold copyCommitmentBit; ppt⟩

/-- **`CommitmentScheme.ComputationalHiding` fails for `plaintextCommitment`.** -/
theorem not_computationalHiding_plaintextCommitment :
    ¬ plaintextCommitment.ComputationalHiding (fun _ => PMF.pure ()) := by
  intro h
  have hneg := h copyCommitmentBit copyCommitmentBit_isPPT
  have heval (bit : Bool) (n : ℕ) :
      plaintextCommitment.hidingGame (fun _ => PMF.pure ()) copyCommitmentBit bit n =
        PMF.pure bit := by
    cases bit <;> simp [CommitmentScheme.hidingGame, CommitmentScheme.hidingForKey,
      plaintextCommitment, copyCommitmentBit]
  simp only [heval] at hneg
  refine not_negligible_const ?_ hneg
  simp [Game.advantage, Game.succProbability]

/-- **`CommitmentScheme.StatisticalHiding` fails for `plaintextCommitment`**, since statistical
hiding implies computational hiding. -/
theorem not_statisticalHiding_plaintextCommitment :
    ¬ plaintextCommitment.StatisticalHiding (fun _ => PMF.pure ()) :=
  fun h => not_computationalHiding_plaintextCommitment h.computationalHiding

end CslibFrontierTests.Crypto.AssumptionNonvacuity
