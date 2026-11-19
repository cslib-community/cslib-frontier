/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SchnorrProtocol
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.ProofOfKnowledge
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.Rewinding

/-!
# Schnorr's protocol is a proof of knowledge of discrete logarithms

Schnorr's Sigma protocol `schnorrFamily` ([BonehShoup2023]), indexed by a unary security
parameter `n` and a group description `d`, is a proof of knowledge of the discrete logarithm of
the statement `u`. The knowledge extractor `schnorrKnowledgeExtractor A` is the generic rewinding
extractor of `CslibFrontier.Crypto.Protocols.SigmaProtocol.ProofOfKnowledge` for a prover `A` on
words. It draws its two challenges with the fair-coin sampler `schnorrSampleChallenge` and computes
`(c - c')⁻¹ (z - z')` modulo the group order `q` with `schnorrExtractWord`.

* **Efficiency** (`isPPTOn_schnorrKnowledgeExtractor`): the extractor is uniform strict PPT
  whenever `A` is. There is no other hypothesis.
* **Extraction** (`le_add_sqrt_schnorrExtractionGame`): for every group description and every
  statement `u`, not only on average over generated keys, the honest verifier's acceptance
  probability `ε` of `A` and the probability `ε'` that the extractor outputs the binary encoding of
  the discrete logarithm of `u` satisfy

    `ε ≤ 1 / q + 2 / 2 ^ n + √ε'`.

  The term `2 / 2 ^ n` comes from the challenge sampler, which is within statistical distance
  `1 / 2 ^ n` of uniform on `ZMod q`.

Combined with a discrete-logarithm assumption, this yields the average-key proof-of-knowledge
reduction `succProbability_schnorrPoKGame_le` / `DiscreteLog.negligible_schnorrPoKGame` (any
uniform strict PPT prover succeeds in `schnorrPoKGame` with negligible probability under
`DiscreteLog`) and is the extraction step behind the security of Schnorr identification;
`negligible_schnorrDirectProbGame` in
`CslibFrontier.Crypto.Computational.SchnorrEavesdrop` proves that security with `k`-bit challenges.
This module also instantiates the `andProof`, `orProofWith`, and `parallelRepetition` compositions
of `CslibFrontier.Crypto.Protocols.SigmaProtocol.Composition` and
`CslibFrontier.Crypto.Protocols.SigmaProtocol.Efficient` on the fair-coin Schnorr Sigma protocol
`schnorrProbFamily` (original instantiations combining [BonehShoup2023], Examples 19.1–19.3 with
Theorems 19.18–19.19 and Exercise 19.6). In the OR composition (`schnorrOrProbFamily`), the honest
prover draws the simulated side's challenge with `schnorrSampleChallenge`, simulates the other side
with `schnorrSimulator`, and commits on its witness side with `schnorrProbFamily`. Because a
strict-PPT fair-coin machine cannot sample `ZMod q` with zero error when `q` is not a power of two,
Definition 19.5(ii)'s identical transcript distribution is relaxed to `4 / 2 ^ n` (`andProof`),
`6 / 2 ^ n` (`schnorrOrProbFamily`), and `2 * k / 2 ^ n` (`parallelRepetition`) statistical
closeness and to Definition 20.6 (`ComputationalSpecialHVZK`) with exact zero acceptance error.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrKnowledgeExtractor`: the rewinding knowledge
  extractor.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrPoKGame`: the average-key proof-of-knowledge
  acceptance experiment over `setup`.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrPoKToDLogSolver`: the discrete-logarithm solver
  built from `schnorrKnowledgeExtractor`.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrSubChallengeWord`: word-level challenge subtraction
  modulo the group order for `orProofWith` composition.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrOrProbFamily`: fair-coin OR-proof of two Schnorr
  protocols using `schnorrSampleChallenge`, `schnorrProbFamily`, and `schnorrSimulator`.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_schnorrKnowledgeExtractor`: it is uniform strict PPT.
* `Cslib.Crypto.PrimeOrderGroupFamily.le_add_sqrt_schnorrExtractionGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.le_add_sqrt_bind_schnorrExtractionGame`:
  `ε ≤ 1 / q + 2 / 2 ^ n + √ε'` on every statement and on average over any statement distribution.
* `Cslib.Crypto.PrimeOrderGroupFamily.succProbability_schnorrPoKGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DiscreteLog.negligible_schnorrPoKGame`: average-key
  proof-of-knowledge security under `DiscreteLog`.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrOrProbFamily_complete`: completeness of the fair-coin
  OR-proof of two Schnorr protocols.
* `Cslib.Crypto.PrimeOrderGroupFamily.efficientSpecialSoundness_andProof_schnorr`,
  `Cslib.Crypto.PrimeOrderGroupFamily.efficientSpecialSoundness_orProof_schnorr`,
  `Cslib.Crypto.PrimeOrderGroupFamily.efficientSpecialSoundness_parallelRepetition_schnorr`:
  efficient special soundness of the fair-coin composed Schnorr protocols.
* `Cslib.Crypto.PrimeOrderGroupFamily.closeTo_transcript_andProof_schnorrProbFamily_simulator`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_chvzkGame_andProof_schnorrProbFamily_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computationalSpecialHVZK_andProof_schnorr`: `4 / 2 ^ n`
  statistical closeness, Attack Game 20.4 bound, and `ComputationalSpecialHVZK` for fair-coin AND.
* `Cslib.Crypto.PrimeOrderGroupFamily.closeTo_transcript_schnorrOrProbFamily_simulator`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_chvzkGame_schnorrOrProbFamily_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computationalSpecialHVZK_orProof_schnorr`: `6 / 2 ^ n`
  statistical closeness, Attack Game 20.4 bound, and `ComputationalSpecialHVZK` for fair-coin OR.
* `PrimeOrderGroupFamily.closeTo_transcript_parallelRepetition_schnorrProbFamily_simulator`,
  `PrimeOrderGroupFamily.advantage_chvzkGame_parallelRepetition_schnorrProbFamily_le`,
  `PrimeOrderGroupFamily.computationalSpecialHVZK_parallelRepetition_schnorr`:
  `2 * k / 2 ^ n` statistical closeness, Attack Game 20.4 bound, and `ComputationalSpecialHVZK` for
  fair-coin `k`-fold parallel repetition under polynomially bounded `k`.

## References

* [M. Bellare, O. Goldreich, *On Defining Proofs of Knowledge*][BellareGoldreich1992]
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023]
* [C.-P. Schnorr, *Efficient Signature Generation by Smart Cards*][Schnorr1991]
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Protocols Protocols.SigmaProtocol
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)

/-- The rewinding knowledge extractor for Schnorr's protocol: run the prover `A` to its
commitment, answer two challenges sampled by `schnorrSampleChallenge` from the same state, and
apply `schnorrExtractWord` to the two conversations. -/
noncomputable def schnorrKnowledgeExtractor (A : MaliciousProver (ℕ × F.Desc)) :
    (ℕ × F.Desc) × List Bool → ProbComp (List Bool) :=
  knowledgeExtractor F.schnorrEncoding F.schnorrSampleChallenge F.schnorrExtractWord A

/-- **Schnorr's knowledge extractor is uniform strict PPT** whenever the prover is. -/
theorem isPPTOn_schnorrKnowledgeExtractor {A : MaliciousProver (ℕ × F.Desc)}
    (hA : A.IsPPT (encPair encUnary F.encDesc)) :
    IsPPTOn (encPair (encPair encUnary F.encDesc) encBits) encBits
      (F.schnorrKnowledgeExtractor A) :=
  isPPTOn_knowledgeExtractor F.isPPTOn_schnorrSampleChallenge
    F.computableInPolyTime_schnorrExtractWord hA

/-- **Schnorr's protocol is a proof of knowledge of discrete logarithms.** At the security
parameter `n`, in the group described by `d` of order `q`, and on every statement `u`, if the
prover `A` convinces the honest verifier with probability `ε`, the knowledge extractor outputs the
binary encoding of the discrete logarithm of `u` with probability `ε'` such that
`ε ≤ 1 / q + 2 / 2 ^ n + √ε'`. -/
theorem le_add_sqrt_schnorrExtractionGame (A : MaliciousProver (ℕ × F.Desc)) (n : ℕ)
    (d : F.Desc) (u : F.Carrier d) :
    (Game.succProbability (acceptanceGame F.schnorrFamily F.schnorrEncoding A (n, d) u
        (PMF.uniformOfFintype (ZMod (F.order d)))) : ℝ) ≤
      1 / F.order d + 2 / 2 ^ n +
        √(Game.succProbability (extractionGame F.schnorrEncoding (fun i => F.encScalar i.2)
          (fun i α u => α • F.generator i.2 = u) (F.schnorrKnowledgeExtractor A) (n, d) u)) := by
  have h := le_add_sqrt_extractionGame F.efficientSpecialSoundness_schnorr.specialSoundness
    F.extractorRealizedBy_schnorrExtractWord A (n, d) u (F.closeTo_schnorrSampleChallenge (n, d))
  simp only [ZMod.card, NNReal.coe_div, NNReal.coe_one, NNReal.coe_pow, NNReal.coe_ofNat] at h
  refine h.trans_eq ?_
  rw [schnorrKnowledgeExtractor]
  ring

/-- **Average-statement extraction for Schnorr's protocol.** At security parameter `n`, in the
group described by `d` of order `q`, and for any statement distribution `μ : PMF (F.Carrier d)`,
the honest verifier's average acceptance probability `ε` of `A` over `u ← μ` and the average
probability `ε'` over `u ← μ` that `schnorrKnowledgeExtractor A` outputs the binary encoding of
the discrete logarithm of `u` satisfy `ε ≤ 1 / q + 2 / 2 ^ n + √ε'`. -/
theorem le_add_sqrt_bind_schnorrExtractionGame (A : MaliciousProver (ℕ × F.Desc)) (n : ℕ)
    (d : F.Desc) (μ : PMF (F.Carrier d)) :
    (Game.succProbability
        (μ.bind fun u => acceptanceGame F.schnorrFamily F.schnorrEncoding A (n, d) u
          (PMF.uniformOfFintype (ZMod (F.order d)))) : ℝ) ≤
      1 / F.order d + 2 / 2 ^ n +
        √(Game.succProbability (μ.bind fun u =>
          extractionGame F.schnorrEncoding (fun i => F.encScalar i.2)
            (fun i α u => α • F.generator i.2 = u) (F.schnorrKnowledgeExtractor A) (n, d) u)) := by
  have h := le_add_sqrt_bind_extractionGame F.efficientSpecialSoundness_schnorr.specialSoundness
    F.extractorRealizedBy_schnorrExtractWord A (n, d) μ (F.closeTo_schnorrSampleChallenge (n, d))
  simp only [ZMod.card, NNReal.coe_div, NNReal.coe_one, NNReal.coe_pow, NNReal.coe_ofNat] at h
  refine h.trans_eq ?_
  rw [schnorrKnowledgeExtractor]
  ring

/-! ### Average-key proof of knowledge under `DiscreteLog` -/

/-- Average-key proof-of-knowledge experiment for `schnorrFamily` at security parameter `n`:
draw group parameters `d ← setup n` and a uniform secret key `α ← PMF.uniformOfFintype (ZMod
(F.order d))`, and run `acceptanceGame` of `A` on the public key `α • F.generator d` against the
honest verifier. -/
noncomputable def schnorrPoKGame (setup : ℕ → PMF F.Desc)
    (A : MaliciousProver (ℕ × F.Desc)) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  acceptanceGame F.schnorrFamily F.schnorrEncoding A (n, d) (α • F.generator d)
    (PMF.uniformOfFintype (ZMod (F.order d)))

/-- Discrete-logarithm adversary built from `schnorrKnowledgeExtractor`: on security parameter `n`
and `(d, u_word)`, run `F.schnorrKnowledgeExtractor A ((n, d), u_word)`. -/
noncomputable def schnorrPoKToDLogSolver (A : MaliciousProver (ℕ × F.Desc))
    (n : ℕ) (input : F.Desc × List Bool) : ProbComp (List Bool) :=
  F.schnorrKnowledgeExtractor A ((n, input.1), input.2)

/-- `schnorrPoKToDLogSolver A` is uniform strict PPT whenever `A` is. -/
theorem isPPTOn_schnorrPoKToDLogSolver {A : MaliciousProver (ℕ × F.Desc)}
    (hA : A.IsPPT (encPair encUnary F.encDesc)) :
    IsPPTOn (encPair encUnary (encPair F.encDesc encBits)) encBits
      (fun input => F.schnorrPoKToDLogSolver A input.1 input.2) :=
  (F.isPPTOn_schnorrKnowledgeExtractor hA).preprocess
    (prepare := fun p : ℕ × F.Desc × List Bool => ((p.1, p.2.1), p.2.2)) (by fun_prop)

private theorem schnorrExtractionGame_le_dlog (A : MaliciousProver (ℕ × F.Desc)) (n : ℕ)
    (d : F.Desc) (α : ZMod (F.order d)) :
    extractionGame F.schnorrEncoding (fun i => F.encScalar i.2)
        (fun i α' u => α' • F.generator i.2 = u) (F.schnorrKnowledgeExtractor A) (n, d)
        (α • F.generator d) true ≤
      ((ProbComp.eval (F.schnorrPoKToDLogSolver A n (d, F.encode d (α • F.generator d)))).bind
        fun guess => PMF.pure (decide ((ofBits guess : ZMod (F.order d)) = α))) true := by
  classical
  simp only [extractionGame, schnorrEncoding, encodeEmbedding, schnorrPoKToDLogSolver,
    Function.Embedding.coeFn_mk, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun w _ => ?_
  by_cases h : ∃ x : ZMod (F.order d), F.encScalar d x = w ∧
      x • F.generator d = α • F.generator d
  · have ⟨x, hx, hsmul⟩ := h
    have hxα : x = α := F.smul_generator_injective d hsmul
    have hguess : (ofBits w : ZMod (F.order d)) = α := by
      rw [← hx, encScalar, Function.Embedding.coeFn_mk, encNat_apply, ofBits_bits,
        ZMod.natCast_zmod_val, hxα]
    simp [h, hguess]
  · simp [h]

/-- **Quantitative average-key reduction from `schnorrPoKGame` to `discreteLogGame`.** When every
group in the support of `setup n` has order at least `m > 0`, a prover's average acceptance
probability in `schnorrPoKGame` is at most `1 / m + 2 / 2 ^ n + √ε'`, where `ε'` is the
discrete-logarithm success probability of `schnorrPoKToDLogSolver A`. -/
theorem succProbability_schnorrPoKGame_le (setup : ℕ → PMF F.Desc)
    (A : MaliciousProver (ℕ × F.Desc)) (n m : ℕ) (hm0 : 0 < m)
    (hm : ∀ d ∈ (setup n).support, m ≤ F.order d) :
    (Game.succProbability (F.schnorrPoKGame setup A n) : ℝ) ≤
      1 / m + 2 / 2 ^ n +
        √(Game.succProbability (F.discreteLogGame setup (F.schnorrPoKToDLogSolver A) n)) := by
  classical
  set δ : ℝ≥0 := 1 / 2 ^ n
  set κ : ℝ := 1 / m + δ with hκ_def
  have hκ0 : 0 ≤ κ := by positivity
  let G (d : F.Desc) : Game :=
    (PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
      acceptanceGame F.schnorrFamily F.schnorrEncoding A (n, d) (α • F.generator d)
        (ProbComp.eval (F.schnorrSampleChallenge (n, d)))
  let H (d : F.Desc) : Game :=
    (PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
      (ProbComp.eval (F.schnorrPoKToDLogSolver A n (d, F.encode d (α • F.generator d)))).bind
        fun guess => PMF.pure (decide ((ofBits guess : ZMod (F.order d)) = α))
  have hGH : ∀ d ∈ (setup n).support,
      (Game.succProbability (G d) : ℝ) ^ 2 - κ * Game.succProbability (G d) ≤
        Game.succProbability (H d) := by
    intro d hd
    have hκ_d (c : ZMod (F.order d)) :
        (ProbComp.eval (F.schnorrSampleChallenge (n, d)) c).toReal ≤ κ := by
      have h := (F.closeTo_schnorrSampleChallenge (n, d)).toReal_apply_le_of_uniformOfFintype c
      rw [ZMod.card] at h
      refine h.trans ?_
      rw [hκ_def]
      gcongr
      exact hm d hd
    have hsq := sq_sub_mul_le_bind_extractionGame
      F.efficientSpecialSoundness_schnorr.specialSoundness
      F.extractorRealizedBy_schnorrExtractWord F.schnorrSampleChallenge A (n, d)
      ((PMF.uniformOfFintype (ZMod (F.order d))).map (· • F.generator d)) hκ_d
    simp only [PMF.bind_map, Function.comp_def] at hsq
    refine hsq.trans ?_
    rw [NNReal.coe_le_coe]
    refine Game.succProbability_mono
      (Probability.PMF.bind_apply_mono_on_support _ _ fun α _ => ?_)
    exact F.schnorrExtractionGame_le_dlog A n d α
  have hsampled :
      (Game.succProbability ((setup n).bind G) : ℝ) ≤
        κ + √(Game.succProbability (F.discreteLogGame setup (F.schnorrPoKToDLogSolver A) n)) :=
    Rewinding.le_add_sqrt_of_sq_sub_mul_le hκ0 (Game.sq_sub_mul_le_bind (setup n) G H hGH)
  have hclose_game : CloseTo (F.schnorrPoKGame setup A n) ((setup n).bind G) δ := by
    simp only [schnorrPoKGame, G, PMF.monad_bind_eq_bind]
    refine CloseTo.bind_right _ fun d _ => ?_
    refine CloseTo.bind_right _ fun α _ => ?_
    simp only [acceptanceGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
    exact CloseTo.bind_right _ fun ts _ =>
      (F.closeTo_schnorrSampleChallenge (n, d)).bind_left _
  have hswap := Game.coe_succProbability_le_add_of_advantage_le
    (NNReal.coe_le_coe.mpr (Game.closeTo_iff_advantage_le.mp hclose_game))
  have hδ : (δ : ℝ) = 1 / 2 ^ n := by
    simp [δ]
  calc (Game.succProbability (F.schnorrPoKGame setup A n) : ℝ)
      ≤ Game.succProbability ((setup n).bind G) + δ := hswap
    _ ≤ (κ + √(Game.succProbability (F.discreteLogGame setup (F.schnorrPoKToDLogSolver A) n))) +
        δ := by gcongr
    _ = 1 / m + 2 / 2 ^ n +
        √(Game.succProbability (F.discreteLogGame setup (F.schnorrPoKToDLogSolver A) n)) := by
      rw [hκ_def, hδ]
      ring

/-- **Average-key proof-of-knowledge security of `schnorrFamily` under `DiscreteLog`.** When every
group in the support of `setup n` has order at least `m n > 0` with `1 / m n` negligible, every
uniform strict PPT prover succeeds in `schnorrPoKGame` with negligible probability under
`F.DiscreteLog setup`. -/
theorem DiscreteLog.negligible_schnorrPoKGame {F : PrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc} (hDL : F.DiscreteLog setup)
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n) (hm : ∀ n, ∀ d ∈ (setup n).support, m n ≤ F.order d)
    (hinv : Negligible fun n => (1 / m n : ℝ≥0))
    {A : MaliciousProver (ℕ × F.Desc)} (hA : A.IsPPT (encPair encUnary F.encDesc)) :
    Negligible fun n => Game.succProbability (F.schnorrPoKGame setup A n) := by
  have hbound := (hinv.add (negligible_const_div_two_pow 2)).add
    (Negligible.sqrt (hDL _ (F.isPPTOn_schnorrPoKToDLogSolver hA)))
  refine negligible_of_le hbound fun n => ?_
  rw [← NNReal.coe_le_coe, Pi.add_apply, Pi.add_apply, NNReal.coe_add, NNReal.coe_add,
    Real.coe_sqrt, NNReal.coe_div, NNReal.coe_div, NNReal.coe_one, NNReal.coe_natCast,
    NNReal.coe_pow, NNReal.coe_ofNat]
  exact F.succProbability_schnorrPoKGame_le setup A n (m n) (hm0 n) (hm n)

/-! ### Composed fair-coin Schnorr protocols (`andProof`, `schnorrOrProbFamily`,
  `parallelRepetition`) -/

/-- Word-level challenge subtraction `(c - c₀) mod q` for `schnorrFamily` and `schnorrProbFamily`.
-/
def schnorrSubChallengeWord : (ℕ × F.Desc) × List Bool × List Bool → List Bool
  | ((_, d), c, c₀) =>
    ((ofBits c + (F.order d - ofBits c₀ % F.order d)) % F.order d).bits

/-- `schnorrSubChallengeWord` is computable in polynomial time. -/
theorem computableInPolyTime_schnorrSubChallengeWord :
    ComputableInPolyTime F.schnorrSubChallengeWord
      (encSubChallengeWordInput F.schnorrEncoding.index) encBits := by
  let encIn := encPair (encPair encUnary F.encDesc) (encPair encBits encBits)
  have hd : ComputableInPolyTime
      (fun p : (ℕ × F.Desc) × List Bool × List Bool => p.1.2) encIn F.encDesc := by fun_prop
  have hc : ComputableInPolyTime
      (fun p : (ℕ × F.Desc) × List Bool × List Bool => ofBits p.2.1) encIn encNat :=
    .of_tidy (ComputableTidilyInPolyTime.bitsToNat.comp (by fun_prop))
  have hc₀ : ComputableInPolyTime
      (fun p : (ℕ × F.Desc) × List Bool × List Bool => ofBits p.2.2) encIn encNat :=
    .of_tidy (ComputableTidilyInPolyTime.bitsToNat.comp (by fun_prop))
  have hq := F.computableInPolyTime_order.comp hd
  exact .of_tidy (ComputableTidilyInPolyTime.natBits.comp
    (.binary_mod' (.binary_add' hc.tidy (.binary_sub' hq.tidy (.binary_mod' hc₀.tidy hq.tidy)))
      hq.tidy))

/-- `schnorrSubChallengeWord` computes `c - c₀` on encoded Schnorr challenges. -/
theorem schnorrSubChallengeWord_eq (i : ℕ × F.Desc) (c c₀ : ZMod (F.order i.2)) :
    F.schnorrSubChallengeWord (i, F.schnorrEncoding.challenge i c,
      F.schnorrEncoding.challenge i c₀) = F.schnorrEncoding.challenge i (c - c₀) := by
  obtain ⟨n, d⟩ := i
  have hsub :
      (((c.val + (F.order d - c₀.val) : ℕ) : ZMod (F.order d))) = c - c₀ := by
    rw [Nat.cast_add, Nat.cast_sub (ZMod.val_lt c₀).le,
      ZMod.natCast_self, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, zero_sub,
      sub_eq_add_neg]
  simp only [schnorrSubChallengeWord, schnorrEncoding, encScalar, Function.Embedding.coeFn_mk,
    encNat_apply, ofBits_bits, Nat.mod_eq_of_lt (ZMod.val_lt c₀)]
  rw [← ZMod.val_natCast, hsub]

private theorem mem_support_schnorrSimulator_accepts (i : ℕ × F.Desc) (u : F.Carrier i.2)
    (c : ZMod (F.order i.2)) {tz : F.Carrier i.2 × ZMod (F.order i.2)}
    (htz : tz ∈ (ProbComp.eval (F.schnorrSimulator i u c)).support) :
    (F.schnorrProbFamily i).Accepts u tz.1 c tz.2 :=
  (PMF.toOuterMeasure_apply_eq_one_iff _ _).mp (F.accepts_schnorrSimulator i u c) htz

private theorem closeTo_schnorrSampleChallenge_ennreal (i : ℕ × F.Desc) :
    CloseTo (PMF.uniformOfFintype (ZMod (F.order i.2)))
      (ProbComp.eval (F.schnorrSampleChallenge i)) (1 / 2 ^ i.1 : ℝ≥0∞) := by
  have h1 : (((1 / 2 ^ i.1 : ℝ≥0)) : ℝ≥0∞) = 1 / 2 ^ i.1 := by simp
  rw [← h1]
  exact F.closeTo_schnorrSampleChallenge i

private theorem closeTo_transcript_schnorrProb (i : ℕ × F.Desc) (α : ZMod (F.order i.2))
    (u : F.Carrier i.2) (c : ZMod (F.order i.2)) :
    CloseTo ((F.schnorrFamily i).transcript α u c)
      ((F.schnorrProbFamily i).transcript α u c) (1 / 2 ^ i.1 : ℝ≥0) :=
  F.closeTo_transcript_linearProbFamily
    (fun j _ => LinearMap.toSpanSingleton (ZMod (F.order j.2)) (F.Carrier j.2) (F.generator j.2))
    (fun _ => id) (fun _ => Function.Embedding.refl _) i α u c

/-! #### Conjunction (`andProof`) -/

/-- **Efficient special soundness of the conjunction of two fair-coin Schnorr protocols** (original
instantiation combining [BonehShoup2023], Example 19.2, p. 773, with Theorem 19.18, pp. 787–788).
-/
theorem efficientSpecialSoundness_andProof_schnorr :
    EfficientSpecialSoundness
      (fun i => (F.schnorrProbFamily i).andProof (F.schnorrProbFamily i))
      (fun i x y => x.1 • F.generator i.2 = y.1 ∧ x.2 • F.generator i.2 = y.2)
      (F.schnorrEncoding.andProof F.schnorrEncoding)
      (fun i => encPair (F.encScalar i.2) (F.encScalar i.2))
      (fun i => andExtract (F.schnorrExtract i) (F.schnorrExtract i)) :=
  EfficientSpecialSoundness.andProof rfl (fun _ => rfl)
    F.efficientSpecialSoundness_schnorrProb F.efficientSpecialSoundness_schnorrProb

private theorem closeTo_transcript_andProof_schnorrProbFamily (i : ℕ × F.Desc)
    (x : ZMod (F.order i.2) × ZMod (F.order i.2)) (y : F.Carrier i.2 × F.Carrier i.2)
    (c : ZMod (F.order i.2)) :
    CloseTo (((F.schnorrFamily i).andProof (F.schnorrFamily i)).transcript x y c)
      (((F.schnorrProbFamily i).andProof (F.schnorrProbFamily i)).transcript x y c)
      (2 / 2 ^ i.1 : ℝ≥0) := by
  have h := closeTo_andProof_transcript
    (F.closeTo_transcript_schnorrProb i x.1 y.1 c)
    (F.closeTo_transcript_schnorrProb i x.2 y.2 c)
  have hadd : (((1 / 2 ^ i.1 : ℝ≥0)) : ℝ≥0∞) + ((1 / 2 ^ i.1 : ℝ≥0) : ℝ≥0∞) =
      ((2 / 2 ^ i.1 : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.coe_add]
    congr 1
    ext
    push_cast
    ring
  rwa [hadd] at h

/-- On every valid pair `(x, y)` and challenge `c`, the honest transcript of the fair-coin AND
protocol `(F.schnorrProbFamily i).andProof (F.schnorrProbFamily i)` and the strict PPT simulator
`andSimulator F.schnorrSimulator F.schnorrSimulator` are within statistical distance `4 / 2 ^ n`
(`2 / 2 ^ n` from the two honest commitment nonces and `2 / 2 ^ n` from the two simulated
responses; original instantiation combining [BonehShoup2023], Example 19.3, p. 774, with
Theorem 19.18, pp. 787–788, relaxing Definition 19.5(ii)'s identical transcript distribution to
`4 / 2 ^ n` statistical closeness in the strict-PPT fair-coin model). -/
theorem closeTo_transcript_andProof_schnorrProbFamily_simulator (i : ℕ × F.Desc)
    {x : ZMod (F.order i.2) × ZMod (F.order i.2)} {y : F.Carrier i.2 × F.Carrier i.2}
    (hxy : x.1 • F.generator i.2 = y.1 ∧ x.2 • F.generator i.2 = y.2)
    (c : ZMod (F.order i.2)) :
    CloseTo (((F.schnorrProbFamily i).andProof (F.schnorrProbFamily i)).transcript x y c)
      (ProbComp.eval (andSimulator F.schnorrSimulator F.schnorrSimulator i y c))
      (4 / 2 ^ i.1) := by
  have htrans : CloseTo (((F.schnorrFamily i).andProof (F.schnorrFamily i)).transcript x y c)
      (((F.schnorrProbFamily i).andProof (F.schnorrProbFamily i)).transcript x y c)
      (2 / 2 ^ i.1 : ℝ≥0∞) := by
    have h2 : (((2 / 2 ^ i.1 : ℝ≥0)) : ℝ≥0∞) = 2 / 2 ^ i.1 := by simp
    rw [← h2]
    exact F.closeTo_transcript_andProof_schnorrProbFamily i x y c
  have h := (simulatorRealizedBy_andSimulator F.simulatorRealizedBy_schnorrSimulator
    F.simulatorRealizedBy_schnorrSimulator).closeTo_transcript_of_closeTo
    (P := fun j => (F.schnorrFamily j).andProof (F.schnorrFamily j))
    (P' := fun j => (F.schnorrProbFamily j).andProof (F.schnorrProbFamily j))
    (δP := fun j => 2 / 2 ^ j.1)
    (fun j => andProof_specialHVZK (F.efficientSpecialHVZK_schnorr_ideal.specialHVZK j)
      (F.efficientSpecialHVZK_schnorr_ideal.specialHVZK j)) hxy htrans
  have h4 : (2 / 2 ^ i.1 : ℝ≥0∞) + (1 / 2 ^ i.1 + 1 / 2 ^ i.1) = 4 / 2 ^ i.1 := by
    rw [← ENNReal.add_div, ← ENNReal.add_div]
    norm_num
  rwa [h4] at h

/-- In Attack Game 20.4 (`chvzkRealGame` vs `chvzkSimGame`), the fair-coin AND-proof of two Schnorr
protocols and `andSimulator F.schnorrSimulator F.schnorrSimulator` differ in distinguishing
advantage by at most `4 / 2 ^ n` against *every* adversary (including computationally unbounded
ones). -/
theorem advantage_chvzkGame_andProof_schnorrProbFamily_le {σ : Type} (setup : ℕ → PMF F.Desc)
    (A : CHVZKAdversary (ℕ × F.Desc)
      (fun i => ZMod (F.order i.2) × ZMod (F.order i.2))
      (fun i => F.Carrier i.2 × F.Carrier i.2)
      (fun i => F.Carrier i.2 × F.Carrier i.2)
      (fun i => ZMod (F.order i.2))
      (fun i => ZMod (F.order i.2) × ZMod (F.order i.2)) σ) (n : ℕ) :
    Game.advantage
      (chvzkRealGame (fun i => (F.schnorrProbFamily i).andProof (F.schnorrProbFamily i))
        (fun i x y => x.1 • F.generator i.2 = y.1 ∧ x.2 • F.generator i.2 = y.2)
        (fun m => (setup m).map (m, ·)) A n)
      (chvzkSimGame (fun i x y => x.1 • F.generator i.2 = y.1 ∧ x.2 • F.generator i.2 = y.2)
        (fun m => (setup m).map (m, ·))
        (andSimulator F.schnorrSimulator F.schnorrSimulator) A n) ≤
      4 / 2 ^ n := by
  refine ((simulatorRealizedBy_andSimulator F.simulatorRealizedBy_schnorrSimulator
    F.simulatorRealizedBy_schnorrSimulator).advantage_chvzkGame_le_of_closeTo_transcript
    (P := fun j => (F.schnorrFamily j).andProof (F.schnorrFamily j))
    (P' := fun i => (F.schnorrProbFamily i).andProof (F.schnorrProbFamily i))
    (εP := 2 / 2 ^ n) (εS := 2 / 2 ^ n)
    (fun j => andProof_specialHVZK (F.efficientSpecialHVZK_schnorr_ideal.specialHVZK j)
      (F.efficientSpecialHVZK_schnorr_ideal.specialHVZK j))
    (fun i hi x y _ c => ?_) (fun i hi => ?_) A).trans_eq ?_
  · obtain ⟨d, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hi
    exact F.closeTo_transcript_andProof_schnorrProbFamily (n, d) x y c
  · obtain ⟨d, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hi
    dsimp only
    rw [← ENNReal.add_div, one_add_one_eq_two]
    exact le_of_eq (by simp)
  · ext
    push_cast
    ring

/-- **Computational special HVZK of the conjunction of two fair-coin Schnorr protocols** (original
instantiation combining [BonehShoup2023], Example 19.3, p. 774, and Theorem 19.18, pp. 787–788,
with Definition 20.6, p. 840): against the fair-coin honest prover of
`(F.schnorrProbFamily i).andProof (F.schnorrProbFamily i)`, the strict PPT simulator
`andSimulator F.schnorrSimulator F.schnorrSimulator` satisfies Definition 20.6 with exact zero
acceptance error (`δ = fun _ => 0`), relaxing Theorem 19.18's exact transcript identity to
`4 / 2 ^ n` statistical closeness (`closeTo_transcript_andProof_schnorrProbFamily_simulator`) and
Definition 20.6 in the strict-PPT fair-coin model. -/
theorem computationalSpecialHVZK_andProof_schnorr (setup : ℕ → PMF F.Desc) :
    ComputationalSpecialHVZK
      (fun i => (F.schnorrProbFamily i).andProof (F.schnorrProbFamily i))
      (fun i x y => x.1 • F.generator i.2 = y.1 ∧ x.2 • F.generator i.2 = y.2)
      (F.schnorrEncoding.andProof F.schnorrEncoding)
      (fun i => encPair (F.encScalar i.2) (F.encScalar i.2))
      (fun n => (setup n).map (n, ·))
      (andSimulator F.schnorrSimulator F.schnorrSimulator)
      (fun _ => 0) where
  ppt := isPPT_andSimulator rfl (fun _ => rfl) F.isPPT_schnorrSimulator F.isPPT_schnorrSimulator
  accepts i y c := by
    rw [tsub_zero]
    refine le_of_eq (Eq.symm ?_)
    rw [PMF.toOuterMeasure_apply_eq_one_iff]
    intro tz htz
    simp only [andSimulator, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at htz
    obtain ⟨a, ha, b, hb, rfl⟩ := htz
    exact andProof_accepts_iff.mpr
      ⟨F.mem_support_schnorrSimulator_accepts i y.1 c ha,
       F.mem_support_schnorrSimulator_accepts i y.2 c hb⟩
  indistinguishable _ A _ :=
    negligible_of_le (negligible_const_div_two_pow 4) fun n =>
      F.advantage_chvzkGame_andProof_schnorrProbFamily_le setup A n

/-! #### Disjunction (`schnorrOrProbFamily`) -/

private noncomputable abbrev schnorrIdealSimulate (i : ℕ × F.Desc) :
    F.Carrier i.2 → ZMod (F.order i.2) → PMF (F.Carrier i.2 × ZMod (F.order i.2)) :=
  linearSimulate
    (fun _ => LinearMap.toSpanSingleton (ZMod (F.order i.2)) (F.Carrier i.2) (F.generator i.2))
    id (Function.Embedding.refl _)

private noncomputable abbrev schnorrOrIdealFamily (i : ℕ × F.Desc) :
    SigmaProtocol (ZMod (F.order i.2) ⊕ ZMod (F.order i.2))
      (F.Carrier i.2 × F.Carrier i.2) (F.Carrier i.2 × F.Carrier i.2)
      (ZMod (F.order i.2)) (ZMod (F.order i.2) × ZMod (F.order i.2) × ZMod (F.order i.2)) :=
  SigmaProtocol.orProof (F.schnorrFamily i) (F.schnorrFamily i)
    (F.schnorrIdealSimulate i) (F.schnorrIdealSimulate i)

/-- Fair-coin OR-proof of two Schnorr protocols ([BonehShoup2023], Section 19.7.2, pp. 788–789):
the honest prover draws the simulated side's challenge with `schnorrSampleChallenge`, simulates the
other side with `schnorrSimulator`, and commits on its witness side with `schnorrProbFamily`. -/
noncomputable abbrev schnorrOrProbFamily (i : ℕ × F.Desc) :
    SigmaProtocol (ZMod (F.order i.2) ⊕ ZMod (F.order i.2))
      (F.Carrier i.2 × F.Carrier i.2) (F.Carrier i.2 × F.Carrier i.2)
      (ZMod (F.order i.2)) (ZMod (F.order i.2) × ZMod (F.order i.2) × ZMod (F.order i.2)) :=
  SigmaProtocol.orProofWith (ProbComp.eval (F.schnorrSampleChallenge i))
    (F.schnorrProbFamily i) (F.schnorrProbFamily i)
    (fun u c => ProbComp.eval (F.schnorrSimulator i u c))
    (fun u c => ProbComp.eval (F.schnorrSimulator i u c))

/-- **Completeness of the fair-coin OR-proof of two Schnorr protocols** (original instantiation
combining [BonehShoup2023], Examples 19.1 and 19.3, pp. 773–774, with Theorem 19.19, p. 789):
every simulated conversation of `schnorrSimulator` is accepting, so every honest conversation of
`schnorrOrProbFamily` is accepting. -/
theorem schnorrOrProbFamily_complete (i : ℕ × F.Desc) :
    (F.schnorrOrProbFamily i).Complete
      (orRelation (fun α u => α • F.generator i.2 = u) (fun α u => α • F.generator i.2 = u)) :=
  orProofWith_complete (F.schnorrProbFamily_complete i) (F.schnorrProbFamily_complete i)
    (fun u c _ => F.mem_support_schnorrSimulator_accepts i u c)
    (fun u c _ => F.mem_support_schnorrSimulator_accepts i u c)

/-- **Efficient special soundness of the fair-coin OR-proof of two Schnorr protocols** (original
instantiation combining [BonehShoup2023], Example 19.2, p. 773, with Theorem 19.19, p. 789). -/
theorem efficientSpecialSoundness_orProof_schnorr :
    EfficientSpecialSoundness F.schnorrOrProbFamily
      (fun i => orRelation (fun α u => α • F.generator i.2 = u)
        (fun α u => α • F.generator i.2 = u))
      (F.schnorrEncoding.orProof F.schnorrEncoding)
      (fun i => encSum (F.encScalar i.2) (F.encScalar i.2))
      (fun i => orExtract (F.schnorrExtract i) (F.schnorrExtract i)) :=
  (EfficientSpecialSoundness.orProof
    (simulate₀ := F.schnorrIdealSimulate) (simulate₁ := F.schnorrIdealSimulate)
    rfl (fun _ => rfl) F.computableInPolyTime_schnorrSubChallengeWord F.schnorrSubChallengeWord_eq
    F.efficientSpecialSoundness_schnorrProb F.efficientSpecialSoundness_schnorrProb).of_verify_eq
    fun _ => by funext _ _ _ ⟨_, _, _⟩; rfl

private theorem closeTo_transcript_schnorrOrProbFamily (i : ℕ × F.Desc)
    {x : ZMod (F.order i.2) ⊕ ZMod (F.order i.2)} {y : F.Carrier i.2 × F.Carrier i.2}
    (hxy : orRelation (fun α u => α • F.generator i.2 = u)
      (fun α u => α • F.generator i.2 = u) x y)
    (c : ZMod (F.order i.2)) :
    CloseTo ((F.schnorrOrIdealFamily i).transcript x y c)
      ((F.schnorrOrProbFamily i).transcript x y c)
      (3 / 2 ^ i.1 : ℝ≥0) := by
  have hp : ∀ (α : ZMod (F.order i.2)) (u : F.Carrier i.2) (c₀ : ZMod (F.order i.2)),
      CloseTo ((F.schnorrFamily i).transcript α u c₀)
        ((F.schnorrProbFamily i).transcript α u c₀) (1 / 2 ^ i.1 : ℝ≥0∞) := fun α u c₀ => by
    have h1 : (((1 / 2 ^ i.1 : ℝ≥0)) : ℝ≥0∞) = 1 / 2 ^ i.1 := by simp
    rw [← h1]
    exact F.closeTo_transcript_schnorrProb i α u c₀
  have h := closeTo_orProofWith_transcript
    (sampleChallenge := PMF.uniformOfFintype (ZMod (F.order i.2)))
    (sampleChallenge' := ProbComp.eval (F.schnorrSampleChallenge i))
    (P₀ := F.schnorrFamily i) (P₀' := F.schnorrProbFamily i)
    (P₁ := F.schnorrFamily i) (P₁' := F.schnorrProbFamily i)
    (simulate₀ := F.schnorrIdealSimulate i)
    (simulate₀' := fun u c => ProbComp.eval (F.schnorrSimulator i u c))
    (simulate₁ := F.schnorrIdealSimulate i)
    (simulate₁' := fun u c => ProbComp.eval (F.schnorrSimulator i u c))
    hxy c (F.closeTo_schnorrSampleChallenge_ennreal i)
    (fun c₀ => F.simulatorRealizedBy_schnorrSimulator i y.1 c₀)
    (fun c₁ => F.simulatorRealizedBy_schnorrSimulator i y.2 c₁)
    (fun α _ c₀ => hp α y.1 c₀) (fun α _ c₁ => hp α y.2 c₁)
  have h3 : (1 / 2 ^ i.1 : ℝ≥0∞) + (1 / 2 ^ i.1 + 1 / 2 ^ i.1) =
      ((3 / 2 ^ i.1 : ℝ≥0) : ℝ≥0∞) := by
    have hc3 : (((3 / 2 ^ i.1 : ℝ≥0)) : ℝ≥0∞) = 3 / 2 ^ i.1 := by simp
    rw [hc3, ← ENNReal.add_div, ← ENNReal.add_div]
    norm_num
  rwa [h3] at h

/-- On every valid pair `(x, y)` and challenge `c`, the honest transcript of `schnorrOrProbFamily`
and the strict PPT simulator
`orSimulator F.schnorrSampleChallenge F.schnorrSimulator F.schnorrSimulator` are within statistical
distance `6 / 2 ^ n` (`3 / 2 ^ n` from the honest OR prover's three `sampleExp` draws and
`3 / 2 ^ n` from the OR simulator's three `sampleExp` draws; original instantiation combining
[BonehShoup2023], Example 19.3, p. 774, with Theorem 19.19, p. 789, relaxing Definition 19.5(ii)'s
identical transcript distribution to `6 / 2 ^ n` statistical closeness in the strict-PPT fair-coin
model). -/
theorem closeTo_transcript_schnorrOrProbFamily_simulator (i : ℕ × F.Desc)
    {x : ZMod (F.order i.2) ⊕ ZMod (F.order i.2)} {y : F.Carrier i.2 × F.Carrier i.2}
    (hxy : orRelation (fun α u => α • F.generator i.2 = u)
      (fun α u => α • F.generator i.2 = u) x y)
    (c : ZMod (F.order i.2)) :
    CloseTo ((F.schnorrOrProbFamily i).transcript x y c)
      (ProbComp.eval
        (orSimulator F.schnorrSampleChallenge F.schnorrSimulator F.schnorrSimulator i y c))
      (6 / 2 ^ i.1) := by
  have htrans : CloseTo ((F.schnorrOrIdealFamily i).transcript x y c)
      ((F.schnorrOrProbFamily i).transcript x y c) (3 / 2 ^ i.1 : ℝ≥0∞) := by
    have hc3 : (((3 / 2 ^ i.1 : ℝ≥0)) : ℝ≥0∞) = 3 / 2 ^ i.1 := by simp
    rw [← hc3]
    exact F.closeTo_transcript_schnorrOrProbFamily i hxy c
  have h := (simulatorRealizedBy_orSimulator F.closeTo_schnorrSampleChallenge_ennreal
    F.simulatorRealizedBy_schnorrSimulator
    F.simulatorRealizedBy_schnorrSimulator).closeTo_transcript_of_closeTo
    (P := F.schnorrOrIdealFamily) (P' := F.schnorrOrProbFamily) (δP := fun j => 3 / 2 ^ j.1)
    (fun j => orProof_specialHVZK (F.efficientSpecialHVZK_schnorr_ideal.specialHVZK j)
      (F.efficientSpecialHVZK_schnorr_ideal.specialHVZK j)) hxy htrans
  have h6 : (3 / 2 ^ i.1 : ℝ≥0∞) + (1 / 2 ^ i.1 + (1 / 2 ^ i.1 + 1 / 2 ^ i.1)) = 6 / 2 ^ i.1 := by
    rw [← ENNReal.add_div, ← ENNReal.add_div, ← ENNReal.add_div]
    norm_num
  rwa [h6] at h

/-- In Attack Game 20.4 (`chvzkRealGame` vs `chvzkSimGame`), the fair-coin OR-proof
`schnorrOrProbFamily` and
`orSimulator F.schnorrSampleChallenge F.schnorrSimulator F.schnorrSimulator` differ in
distinguishing advantage by at most `6 / 2 ^ n` against *every* adversary (including computationally
unbounded ones). -/
theorem advantage_chvzkGame_schnorrOrProbFamily_le {σ : Type} (setup : ℕ → PMF F.Desc)
    (A : CHVZKAdversary (ℕ × F.Desc)
      (fun i => ZMod (F.order i.2) ⊕ ZMod (F.order i.2))
      (fun i => F.Carrier i.2 × F.Carrier i.2)
      (fun i => F.Carrier i.2 × F.Carrier i.2)
      (fun i => ZMod (F.order i.2))
      (fun i => ZMod (F.order i.2) × ZMod (F.order i.2) × ZMod (F.order i.2)) σ) (n : ℕ) :
    Game.advantage
      (chvzkRealGame F.schnorrOrProbFamily
        (fun i => orRelation (fun α u => α • F.generator i.2 = u)
          (fun α u => α • F.generator i.2 = u))
        (fun m => (setup m).map (m, ·)) A n)
      (chvzkSimGame
        (fun i => orRelation (fun α u => α • F.generator i.2 = u)
          (fun α u => α • F.generator i.2 = u))
        (fun m => (setup m).map (m, ·))
        (orSimulator F.schnorrSampleChallenge F.schnorrSimulator F.schnorrSimulator) A n) ≤
      6 / 2 ^ n := by
  refine ((simulatorRealizedBy_orSimulator F.closeTo_schnorrSampleChallenge_ennreal
    F.simulatorRealizedBy_schnorrSimulator
    F.simulatorRealizedBy_schnorrSimulator).advantage_chvzkGame_le_of_closeTo_transcript
    (P := F.schnorrOrIdealFamily) (P' := F.schnorrOrProbFamily)
    (εP := 3 / 2 ^ n) (εS := 3 / 2 ^ n)
    (fun j => orProof_specialHVZK (F.efficientSpecialHVZK_schnorr_ideal.specialHVZK j)
      (F.efficientSpecialHVZK_schnorr_ideal.specialHVZK j))
    (fun i hi _ _ hxy c => ?_) (fun i hi => ?_) A).trans_eq ?_
  · obtain ⟨d, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hi
    exact F.closeTo_transcript_schnorrOrProbFamily (n, d) hxy c
  · obtain ⟨d, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hi
    dsimp only
    have hc3 : (((3 / 2 ^ n : ℝ≥0)) : ℝ≥0∞) = 3 / 2 ^ n := by simp
    rw [← ENNReal.add_div, ← ENNReal.add_div, hc3]
    norm_num
  · ext
    push_cast
    ring

/-- **Computational special HVZK of the fair-coin OR-proof of two Schnorr protocols** (original
instantiation combining [BonehShoup2023], Example 19.3, p. 774, and Theorem 19.19, p. 789, with
Definition 20.6, p. 840): against the fair-coin honest prover of `schnorrOrProbFamily`, the strict
PPT simulator `orSimulator F.schnorrSampleChallenge F.schnorrSimulator F.schnorrSimulator`
satisfies Definition 20.6 with exact zero acceptance error (`δ = fun _ => 0`), relaxing
Theorem 19.19's exact transcript identity to `6 / 2 ^ n` statistical closeness
(`closeTo_transcript_schnorrOrProbFamily_simulator`) and Definition 20.6 in the strict-PPT
fair-coin model. -/
theorem computationalSpecialHVZK_orProof_schnorr (setup : ℕ → PMF F.Desc) :
    ComputationalSpecialHVZK F.schnorrOrProbFamily
      (fun i => orRelation (fun α u => α • F.generator i.2 = u)
        (fun α u => α • F.generator i.2 = u))
      (F.schnorrEncoding.orProof F.schnorrEncoding)
      (fun i => encSum (F.encScalar i.2) (F.encScalar i.2))
      (fun n => (setup n).map (n, ·))
      (orSimulator F.schnorrSampleChallenge F.schnorrSimulator F.schnorrSimulator)
      (fun _ => 0) where
  ppt := isPPT_orSimulator rfl (fun _ => rfl) F.isPPTOn_schnorrSampleChallenge
    F.computableInPolyTime_schnorrSubChallengeWord F.schnorrSubChallengeWord_eq
    F.isPPT_schnorrSimulator F.isPPT_schnorrSimulator
  accepts i y c := by
    rw [tsub_zero]
    refine le_of_eq (Eq.symm ?_)
    rw [PMF.toOuterMeasure_apply_eq_one_iff]
    intro tz htz
    simp only [orSimulator, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at htz
    obtain ⟨c₀, -, a, ha, b, hb, rfl⟩ := htz
    exact orProofWith_accepts_iff.mpr
      ⟨F.mem_support_schnorrSimulator_accepts i y.1 c₀ ha,
       F.mem_support_schnorrSimulator_accepts i y.2 (c - c₀) hb⟩
  indistinguishable _ A _ :=
    negligible_of_le (negligible_const_div_two_pow 6) fun n =>
      F.advantage_chvzkGame_schnorrOrProbFamily_le setup A n

/-! #### `k`-fold parallel repetition (`parallelRepetition`) -/

/-- **Efficient special soundness of the `k`-fold parallel repetition of the fair-coin Schnorr
protocol** (original instantiation combining [BonehShoup2023], Example 19.2, p. 773, with
Exercise 19.6(b), pp. 810–811, allowing `k = 0`). -/
theorem efficientSpecialSoundness_parallelRepetition_schnorr (k : ℕ × F.Desc → ℕ) :
    EfficientSpecialSoundness
      (fun i => (F.schnorrProbFamily i).parallelRepetition (k i))
      (fun i α u => α • F.generator i.2 = u)
      (F.schnorrEncoding.parallelRepetition k)
      (fun i => F.encScalar i.2)
      (fun i => parallelExtract (F.schnorrExtract i) (k i)) := by
  refine EfficientSpecialSoundness.parallelRepetition_of_default ?_
    F.efficientSpecialSoundness_schnorrProb
  have hdef : (fun i : ℕ × F.Desc => F.encScalar i.2 default) = fun _ => encNat 0 := by
    funext i
    change F.encScalar i.2 0 = encNat 0
    simp [encScalar]
  rw [hdef]
  exact ComputableInPolyTime.const _

private theorem closeTo_transcript_parallelRepetition_schnorrProbFamily (k : ℕ × F.Desc → ℕ)
    (i : ℕ × F.Desc) (α : ZMod (F.order i.2)) (u : F.Carrier i.2)
    (c : Fin (k i) → ZMod (F.order i.2)) :
    CloseTo (((F.schnorrFamily i).parallelRepetition (k i)).transcript α u c)
      (((F.schnorrProbFamily i).parallelRepetition (k i)).transcript α u c)
      (((k i : ℝ≥0) / 2 ^ i.1 : ℝ≥0)) := by
  have h := closeTo_parallelRepetition_transcript
    (P := F.schnorrFamily i) (P' := F.schnorrProbFamily i) (δ := (1 / 2 ^ i.1 : ℝ≥0))
    fun j => F.closeTo_transcript_schnorrProb i α u (c j)
  have hmul : (k i : ℝ≥0∞) * ((1 / 2 ^ i.1 : ℝ≥0) : ℝ≥0∞) =
      (((k i : ℝ≥0) / 2 ^ i.1 : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.coe_natCast, ← ENNReal.coe_mul, mul_one_div]
  rwa [hmul] at h

/-- On every valid pair `(α, u)` and challenge tuple `c`, the honest transcript of the `k`-fold
parallel repetition `(F.schnorrProbFamily i).parallelRepetition (k i)` and the strict PPT simulator
`parallelSimulator F.schnorrSimulator k` are within statistical distance `2 * k i / 2 ^ n`
(`k i / 2 ^ n` from the `k i` honest commitment nonces and `k i / 2 ^ n` from the `k i` simulated
responses; original instantiation combining [BonehShoup2023], Example 19.3, p. 774, with
Exercise 19.6(c), pp. 810–811, allowing `k = 0` and relaxing Definition 19.5(ii)'s identical
transcript distribution to `2 * k i / 2 ^ n` statistical closeness in the strict-PPT fair-coin
model). -/
theorem closeTo_transcript_parallelRepetition_schnorrProbFamily_simulator (k : ℕ × F.Desc → ℕ)
    (i : ℕ × F.Desc) {α : ZMod (F.order i.2)} {u : F.Carrier i.2}
    (hxy : α • F.generator i.2 = u) (c : Fin (k i) → ZMod (F.order i.2)) :
    CloseTo (((F.schnorrProbFamily i).parallelRepetition (k i)).transcript α u c)
      (ProbComp.eval (parallelSimulator F.schnorrSimulator k i u c))
      ((2 * k i : ℕ) / 2 ^ i.1) := by
  have htrans : CloseTo (((F.schnorrFamily i).parallelRepetition (k i)).transcript α u c)
      (((F.schnorrProbFamily i).parallelRepetition (k i)).transcript α u c)
      ((k i : ℝ≥0∞) / 2 ^ i.1) := by
    have hck : ((((k i : ℝ≥0) / 2 ^ i.1 : ℝ≥0)) : ℝ≥0∞) = (k i : ℝ≥0∞) / 2 ^ i.1 := by simp
    rw [← hck]
    exact F.closeTo_transcript_parallelRepetition_schnorrProbFamily k i α u c
  have h := (simulatorRealizedBy_parallelSimulator k
    F.simulatorRealizedBy_schnorrSimulator).closeTo_transcript_of_closeTo
    (P := fun j => (F.schnorrFamily j).parallelRepetition (k j))
    (P' := fun j => (F.schnorrProbFamily j).parallelRepetition (k j))
    (δP := fun j => (k j : ℝ≥0∞) / 2 ^ j.1)
    (fun j => parallelRepetition_specialHVZK (k := k j)
      (F.efficientSpecialHVZK_schnorr_ideal.specialHVZK j)) hxy htrans
  have h2k : (k i : ℝ≥0∞) / 2 ^ i.1 + (k i : ℝ≥0∞) * (1 / 2 ^ i.1) =
      (2 * k i : ℕ) / 2 ^ i.1 := by
    rw [mul_one_div, ← ENNReal.add_div, ← two_mul, Nat.cast_mul, Nat.cast_ofNat]
  rwa [h2k] at h

/-- When `k (n, d) ≤ K` across `(setup n).support`, Attack Game 20.4 distinguishing advantage for
the `k`-fold parallel repetition of `schnorrProbFamily` and `parallelSimulator F.schnorrSimulator k`
is at most `2 * K / 2 ^ n` against *every* adversary (including computationally unbounded ones). -/
theorem advantage_chvzkGame_parallelRepetition_schnorrProbFamily_le {σ : Type}
    (k : ℕ × F.Desc → ℕ) (setup : ℕ → PMF F.Desc) (n K : ℕ)
    (hk : ∀ d ∈ (setup n).support, k (n, d) ≤ K)
    (A : CHVZKAdversary (ℕ × F.Desc)
      (fun i => ZMod (F.order i.2))
      (fun i => F.Carrier i.2)
      (fun i => Fin (k i) → F.Carrier i.2)
      (fun i => Fin (k i) → ZMod (F.order i.2))
      (fun i => Fin (k i) → ZMod (F.order i.2)) σ) :
    Game.advantage
      (chvzkRealGame (fun i => (F.schnorrProbFamily i).parallelRepetition (k i))
        (fun i α u => α • F.generator i.2 = u)
        (fun m => (setup m).map (m, ·)) A n)
      (chvzkSimGame (fun i α u => α • F.generator i.2 = u)
        (fun m => (setup m).map (m, ·))
        (parallelSimulator F.schnorrSimulator k) A n) ≤
      (2 * K : ℝ≥0) / 2 ^ n := by
  refine ((simulatorRealizedBy_parallelSimulator k
    F.simulatorRealizedBy_schnorrSimulator).advantage_chvzkGame_le_of_closeTo_transcript
    (P := fun j => (F.schnorrFamily j).parallelRepetition (k j))
    (P' := fun i => (F.schnorrProbFamily i).parallelRepetition (k i))
    (εP := (K : ℝ≥0) / 2 ^ n) (εS := (K : ℝ≥0) / 2 ^ n)
    (fun j => parallelRepetition_specialHVZK (k := k j)
      (F.efficientSpecialHVZK_schnorr_ideal.specialHVZK j))
    (fun i hi α u _ c => ?_) (fun i hi => ?_) A).trans_eq ?_
  · obtain ⟨d, hd, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hi
    refine (F.closeTo_transcript_parallelRepetition_schnorrProbFamily k (n, d) α u c).mono ?_
    rw [ENNReal.coe_le_coe]
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (hk d hd)) zero_le
  · obtain ⟨d, hd, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hi
    dsimp only
    have hcK : ((((K : ℝ≥0) / 2 ^ n : ℝ≥0)) : ℝ≥0∞) = (K : ℝ≥0∞) / 2 ^ n := by simp
    rw [mul_one_div, hcK]
    exact ENNReal.div_le_div_right (Nat.cast_le.mpr (hk d hd)) _
  · ext
    push_cast
    ring

/-- **Computational special HVZK of the `k`-fold parallel repetition of the fair-coin Schnorr
protocol** (original instantiation combining [BonehShoup2023], Example 19.3, p. 774, and
Exercise 19.6(c), pp. 810–811, with Definition 20.6, p. 840): when `k (n, d) ≤ K n` across
`(setup n).support` for a polynomially bounded `K : ℕ → ℕ`, the strict PPT simulator
`parallelSimulator F.schnorrSimulator k` satisfies Definition 20.6 against
`(F.schnorrProbFamily i).parallelRepetition (k i)` with exact zero acceptance error
(`δ = fun _ => 0`), allowing `k = 0` and relaxing Exercise 19.6(c)'s exact transcript identity to
`2 * k / 2 ^ n` statistical closeness
(`closeTo_transcript_parallelRepetition_schnorrProbFamily_simulator`) and Definition 20.6 in the
strict-PPT fair-coin model. -/
theorem computationalSpecialHVZK_parallelRepetition_schnorr
    (k : ℕ × F.Desc → ℕ) (setup : ℕ → PMF F.Desc)
    {K : ℕ → ℕ} (hK : PolynomiallyBounded K)
    (hk : ∀ n, ∀ d ∈ (setup n).support, k (n, d) ≤ K n) :
    ComputationalSpecialHVZK
      (fun i => (F.schnorrProbFamily i).parallelRepetition (k i))
      (fun i α u => α • F.generator i.2 = u)
      (F.schnorrEncoding.parallelRepetition k)
      (fun i => F.encScalar i.2)
      (fun n => (setup n).map (n, ·))
      (parallelSimulator F.schnorrSimulator k)
      (fun _ => 0) where
  ppt := isPPT_parallelSimulator k F.isPPT_schnorrSimulator
  accepts i y c := by
    rw [tsub_zero]
    refine le_of_eq (Eq.symm ?_)
    rw [PMF.toOuterMeasure_apply_eq_one_iff]
    intro tz htz
    simp only [parallelSimulator, ProbComp.eval_map, ProbComp.eval_pi_eq_piFin,
      PMF.mem_support_map_iff, PMF.mem_support_piFin_iff] at htz
    obtain ⟨v, hv, rfl⟩ := htz
    exact parallelRepetition_accepts_iff.mpr fun j =>
      F.mem_support_schnorrSimulator_accepts i y (c j) (hv j)
  indistinguishable _ A _ :=
    negligible_of_le (by fun_prop) fun n =>
      F.advantage_chvzkGame_parallelRepetition_schnorrProbFamily_le k setup n (K n) (hk n) A

end Cslib.Crypto.PrimeOrderGroupFamily
