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
import CslibFrontier.Crypto.Negligible.Basic
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
`CslibFrontier.Crypto.Computational.SchnorrIdentification` proves that security with `k`-bit
challenges. This module also instantiates the `andProof`, `orProof`, and `parallelRepetition`
efficiency transfer theorems of `CslibFrontier.Crypto.Protocols.SigmaProtocol.Efficient` for
`schnorrFamily`.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrKnowledgeExtractor`: the rewinding knowledge
  extractor.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrPoKGame`: the average-key proof-of-knowledge
  acceptance experiment over `setup`.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrPoKToDLogSolver`: the discrete-logarithm solver
  built from `schnorrKnowledgeExtractor`.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrSubChallengeWord`: word-level challenge subtraction
  modulo the group order for `orProof` composition.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_schnorrKnowledgeExtractor`: it is uniform strict PPT.
* `Cslib.Crypto.PrimeOrderGroupFamily.le_add_sqrt_schnorrExtractionGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.le_add_sqrt_bind_schnorrExtractionGame`:
  `ε ≤ 1 / q + 2 / 2 ^ n + √ε'` on every statement and on average over any statement distribution.
* `Cslib.Crypto.PrimeOrderGroupFamily.succProbability_schnorrPoKGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DiscreteLog.negligible_schnorrPoKGame`: average-key
  proof-of-knowledge security under `DiscreteLog`.
* `Cslib.Crypto.PrimeOrderGroupFamily.efficientSpecialSoundness_andProof_schnorr`,
  `Cslib.Crypto.PrimeOrderGroupFamily.efficientSpecialHVZK_andProof_schnorr`,
  `Cslib.Crypto.PrimeOrderGroupFamily.efficientSpecialSoundness_orProof_schnorr`,
  `Cslib.Crypto.PrimeOrderGroupFamily.efficientSpecialHVZK_orProof_schnorr`,
  `Cslib.Crypto.PrimeOrderGroupFamily.efficientSpecialSoundness_parallelRepetition_schnorr`,
  `Cslib.Crypto.PrimeOrderGroupFamily.efficientSpecialHVZK_parallelRepetition_schnorr`:
  efficiency transfer of Schnorr's protocol through `andProof`, `orProof`, and
  `parallelRepetition`.

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
  have htwo : Negligible fun n => (2 / 2 ^ n : ℝ≥0) := by
    refine negligible_of_le
      ((negligible_geometric (ratio := 2⁻¹) (by norm_num)).const_mul 2) fun n => ?_
    simp [div_eq_mul_inv, inv_pow]
  have hbound := (hinv.add htwo).add
    (Negligible.sqrt (hDL _ (F.isPPTOn_schnorrPoKToDLogSolver hA)))
  refine negligible_of_le hbound fun n => ?_
  rw [← NNReal.coe_le_coe, Pi.add_apply, Pi.add_apply, NNReal.coe_add, NNReal.coe_add,
    Real.coe_sqrt, NNReal.coe_div, NNReal.coe_div, NNReal.coe_one, NNReal.coe_natCast,
    NNReal.coe_pow, NNReal.coe_ofNat]
  exact F.succProbability_schnorrPoKGame_le setup A n (m n) (hm0 n) (hm n)

/-! ### Efficiency of composed Schnorr protocols (`andProof`, `orProof`, `parallelRepetition`) -/

/-- Word-level challenge subtraction `(c - c₀) mod q` for `schnorrFamily`. -/
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

/-- **Efficient special soundness of the conjunction of two Schnorr protocols.** -/
theorem efficientSpecialSoundness_andProof_schnorr :
    EfficientSpecialSoundness
      (fun i => (F.schnorrFamily i).andProof (F.schnorrFamily i))
      (fun i x y => x.1 • F.generator i.2 = y.1 ∧ x.2 • F.generator i.2 = y.2)
      (F.schnorrEncoding.andProof F.schnorrEncoding)
      (fun i => encPair (F.encScalar i.2) (F.encScalar i.2))
      (fun i => andExtract (F.schnorrExtract i) (F.schnorrExtract i)) :=
  EfficientSpecialSoundness.andProof rfl (fun _ => rfl)
    F.efficientSpecialSoundness_schnorr F.efficientSpecialSoundness_schnorr

/-- **Efficient special HVZK of the conjunction of two Schnorr protocols.** -/
theorem efficientSpecialHVZK_andProof_schnorr :
    EfficientSpecialHVZK
      (fun i => (F.schnorrFamily i).andProof (F.schnorrFamily i))
      (fun i x y => x.1 • F.generator i.2 = y.1 ∧ x.2 • F.generator i.2 = y.2)
      (F.schnorrEncoding.andProof F.schnorrEncoding)
      (fun i => andSimulate
        (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod (F.order i.2))
          (F.Carrier i.2) (F.generator i.2)) id (Function.Embedding.refl _))
        (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod (F.order i.2))
          (F.Carrier i.2) (F.generator i.2)) id (Function.Embedding.refl _)))
      (fun i => 1 / 2 ^ i.1 + 1 / 2 ^ i.1) :=
  EfficientSpecialHVZK.andProof rfl (fun _ => rfl)
    F.efficientSpecialHVZK_schnorr F.efficientSpecialHVZK_schnorr

/-- **Efficient special soundness of the disjunction of two Schnorr protocols.** -/
theorem efficientSpecialSoundness_orProof_schnorr :
    EfficientSpecialSoundness
      (fun i => SigmaProtocol.orProof (F.schnorrFamily i) (F.schnorrFamily i)
        (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod (F.order i.2))
          (F.Carrier i.2) (F.generator i.2)) id (Function.Embedding.refl _))
        (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod (F.order i.2))
          (F.Carrier i.2) (F.generator i.2)) id (Function.Embedding.refl _)))
      (fun i => orRelation (fun α u => α • F.generator i.2 = u)
        (fun α u => α • F.generator i.2 = u))
      (F.schnorrEncoding.orProof F.schnorrEncoding)
      (fun i => encSum (F.encScalar i.2) (F.encScalar i.2))
      (fun i => orExtract (F.schnorrExtract i) (F.schnorrExtract i)) :=
  EfficientSpecialSoundness.orProof rfl (fun _ => rfl)
    F.computableInPolyTime_schnorrSubChallengeWord F.schnorrSubChallengeWord_eq
    F.efficientSpecialSoundness_schnorr F.efficientSpecialSoundness_schnorr

/-- **Efficient special HVZK of the disjunction of two Schnorr protocols.** -/
theorem efficientSpecialHVZK_orProof_schnorr :
    EfficientSpecialHVZK
      (fun i => SigmaProtocol.orProof (F.schnorrFamily i) (F.schnorrFamily i)
        (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod (F.order i.2))
          (F.Carrier i.2) (F.generator i.2)) id (Function.Embedding.refl _))
        (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod (F.order i.2))
          (F.Carrier i.2) (F.generator i.2)) id (Function.Embedding.refl _)))
      (fun i => orRelation (fun α u => α • F.generator i.2 = u)
        (fun α u => α • F.generator i.2 = u))
      (F.schnorrEncoding.orProof F.schnorrEncoding)
      (fun i => orSimulate
        (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod (F.order i.2))
          (F.Carrier i.2) (F.generator i.2)) id (Function.Embedding.refl _))
        (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod (F.order i.2))
          (F.Carrier i.2) (F.generator i.2)) id (Function.Embedding.refl _)))
      (fun i => (1 / 2 ^ i.1 : ℝ≥0) + (1 / 2 ^ i.1 + 1 / 2 ^ i.1)) :=
  EfficientSpecialHVZK.orProof rfl (fun _ => rfl)
    F.isPPTOn_schnorrSampleChallenge F.closeTo_schnorrSampleChallenge
    F.computableInPolyTime_schnorrSubChallengeWord F.schnorrSubChallengeWord_eq
    F.efficientSpecialHVZK_schnorr F.efficientSpecialHVZK_schnorr

/-- **Efficient special soundness of the `k`-fold parallel repetition of Schnorr's protocol.** -/
theorem efficientSpecialSoundness_parallelRepetition_schnorr (k : ℕ × F.Desc → ℕ) :
    EfficientSpecialSoundness
      (fun i => (F.schnorrFamily i).parallelRepetition (k i))
      (fun i α u => α • F.generator i.2 = u)
      (F.schnorrEncoding.parallelRepetition k)
      (fun i => F.encScalar i.2)
      (fun i => parallelExtract (F.schnorrExtract i) (k i)) := by
  refine EfficientSpecialSoundness.parallelRepetition ?_ F.efficientSpecialSoundness_schnorr
  have hdef : (fun i : ℕ × F.Desc => F.encScalar i.2 default) = fun _ => encNat 0 := by
    funext i
    change F.encScalar i.2 0 = encNat 0
    simp [encScalar]
  rw [hdef]
  exact ComputableInPolyTime.const _

/-- **Efficient special HVZK of the `k`-fold parallel repetition of Schnorr's protocol.** -/
theorem efficientSpecialHVZK_parallelRepetition_schnorr (k : ℕ × F.Desc → ℕ) :
    EfficientSpecialHVZK
      (fun i => (F.schnorrFamily i).parallelRepetition (k i))
      (fun i α u => α • F.generator i.2 = u)
      (F.schnorrEncoding.parallelRepetition k)
      (fun i => parallelSimulate
        (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod (F.order i.2))
          (F.Carrier i.2) (F.generator i.2)) id (Function.Embedding.refl _)) (k i))
      (fun i => (k i : ℝ≥0∞) * (1 / 2 ^ i.1)) :=
  EfficientSpecialHVZK.parallelRepetition k F.efficientSpecialHVZK_schnorr

end Cslib.Crypto.PrimeOrderGroupFamily
