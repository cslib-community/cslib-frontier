/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SchnorrProofOfKnowledge
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Lyubashevsky.ProofOfKnowledge
import CslibFrontier.Tactic.PPT

/-!
# Tests for Sigma-protocol knowledge extraction

`MaliciousProver.IsPPT` is satisfiable: the echoing prover, which commits to the statement word and
answers with the challenge word, is uniform strict PPT for any index encoding. So the strict PPT
certificates of the Schnorr and Lyubashevsky knowledge extractors apply to it.

The extraction bounds are not vacuous. In a toy special-sound protocol for the relation `x = y` on
bits, a prover that answers the challenge `c` with `c xor y` is accepted with probability one, so
the generic bounds give the knowledge extractor success probability at least `1 / 2` (exactly
uniform challenges) and `1 / 4` (challenges within distance `0` of uniform).
-/

public section

namespace CslibFrontierTests.SigmaProofOfKnowledge

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Protocols
open Cslib.Crypto.Protocols.SigmaProtocol
open Turing.MultiTapeTM

/-- A prover that commits to the statement word, keeps it as its state, and answers each challenge
word with itself. -/
def echoProver (I : Type) : MaliciousProver I where
  commit _ y := pure (y, y)
  respond _ _ c := pure c

/-- The echoing prover is uniform strict PPT for any index encoding. -/
theorem isPPT_echoProver {I : Type} (encI : I ↪ List Bool) : (echoProver I).IsPPT encI where
  commit := (ComputableInPolyTime.tidy (by fun_prop :
    ComputableInPolyTime (fun p : I × List Bool => (p.2, p.2)) (encPair encI encBits)
      (encPair encBits encBits))).isPPTOn
  respond := (ComputableInPolyTime.tidy (by fun_prop :
    ComputableInPolyTime (fun p : I × List Bool × List Bool => p.2.2)
      (encPair encI (encPair encBits encBits)) encBits)).isPPTOn

/-- Schnorr's knowledge extractor for the echoing prover is uniform strict PPT. -/
example (F : PrimeOrderGroupFamily) :
    IsPPTOn (encPair (encPair encUnary F.encDesc) encBits) encBits
      (F.schnorrKnowledgeExtractor (echoProver _)) :=
  F.isPPTOn_schnorrKnowledgeExtractor (isPPT_echoProver _)

/-- Lyubashevsky's knowledge extractor for the echoing prover is uniform strict PPT. -/
example :
    IsPPTOn (encPair encLyubashevskyParams encBits) encBits
      (lyubashevskyKnowledgeExtractor (echoProver _)) :=
  isPPTOn_lyubashevskyKnowledgeExtractor (isPPT_echoProver _)

/-! ### A toy protocol where extraction succeeds -/

/-- A toy Sigma protocol for the relation `x = y` on bits: the commitment is trivial, and the
response to the challenge `c` is `c xor x`. -/
noncomputable def xorProtocol : SigmaProtocol Bool Bool Unit Bool Bool where
  State := Unit
  commit _ _ := PMF.pure ((), ())
  respond x _ _ c := xor c x
  verify y _ c z := z == xor c y

/-- Two accepting conversations of `xorProtocol` give the witness `c xor z`. -/
theorem xorProtocol_specialSoundness :
    xorProtocol.SpecialSoundness (fun x y => x = y) fun _ _ c z _ _ => xor c z := by
  intro y _ c z _ _ _ h _
  simp only [SigmaProtocol.Accepts, xorProtocol, beq_iff_eq] at h
  subst h
  cases c <;> cases y <;> rfl

/-- Bits are encoded as one-letter words, and the trivial commitment as the empty word. -/
def xorEncoding :
    Encoding Unit (fun _ => Bool) (fun _ => Unit) (fun _ => Bool) (fun _ => Bool) where
  index := encUnit
  statement _ := encBool
  commitment _ := encUnit
  challenge _ := encBool
  response _ := encBool

/-- The word function of the extractor of `xorProtocol`: the bitwise `xor` of the first challenge
word and the first response word. -/
def xorExtractWord :
    Unit × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool → List Bool :=
  fun (_, _, _, c, z, _, _) => List.zipWith xor c z

/-- `xorExtractWord` computes the extractor of `xorProtocol` on encodings. -/
theorem xorExtractorRealizedBy :
    ExtractorRealizedBy xorEncoding (fun _ => encBool) (fun _ _ _ c z _ _ => xor c z)
      xorExtractWord :=
  fun _ _ _ _ _ _ _ => rfl

/-- The honest prover of `xorProtocol` on words. The witness is the statement bit `y`, so it
commits to the empty word, keeps the statement word as its state, and answers the challenge word
`c` with `c xor y`. -/
def xorProver : MaliciousProver Unit where
  commit _ y := pure ([], y)
  respond _ s c := pure (List.zipWith xor c s)

/-- The honest verifier accepts `xorProver` with probability one. -/
theorem succProbability_xorAcceptanceGame (y : Bool) :
    Game.succProbability (acceptanceGame (fun _ => xorProtocol) xorEncoding xorProver () y
      (PMF.uniformOfFintype Bool)) = 1 := by
  have h : acceptanceGame (fun _ => xorProtocol) xorEncoding xorProver () y
      (PMF.uniformOfFintype Bool) = PMF.pure true := by
    have hacc (c : Bool) : AcceptsWord (fun _ => xorProtocol) xorEncoding () y [] c
        (List.zipWith xor (xorEncoding.challenge () c) (xorEncoding.statement () y)) :=
      ⟨(), xor c y, rfl, rfl, by simp [SigmaProtocol.Accepts, xorProtocol]⟩
    simp only [acceptanceGame, xorProver, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.pure_bind, hacc, decide_true, PMF.bind_const]
  simp [h, Game.succProbability]

/-- The knowledge extractor with uniform challenges outputs the witness with probability at least
`1 / 2`, by `sq_sub_le_extractionGame`. -/
example (y : Bool) :
    (1 / 2 : ℝ) ≤ Game.succProbability (extractionGame xorEncoding (fun _ => encBool)
      (fun _ x y => x = y) (knowledgeExtractor xorEncoding (fun _ => ProbComp.uniform Bool)
        xorExtractWord xorProver) () y) := by
  have h := sq_sub_le_extractionGame (P := fun _ => xorProtocol)
    (fun _ => xorProtocol_specialSoundness) xorExtractorRealizedBy xorProver () y
    (sampleChallenge := fun _ => ProbComp.uniform Bool) (ProbComp.eval_uniform _)
  rw [succProbability_xorAcceptanceGame] at h
  simp only [NNReal.coe_one, one_pow, Fintype.card_bool, Nat.cast_ofNat] at h
  linarith

/-- With the same sampler, viewed as within distance `0` of uniform, `le_add_sqrt_extractionGame`
gives success probability at least `1 / 4`. -/
example (y : Bool) :
    (1 / 4 : ℝ) ≤ Game.succProbability (extractionGame xorEncoding (fun _ => encBool)
      (fun _ x y => x = y) (knowledgeExtractor xorEncoding (fun _ => ProbComp.uniform Bool)
        xorExtractWord xorProver) () y) := by
  have h := le_add_sqrt_extractionGame (P := fun _ => xorProtocol)
    (fun _ => xorProtocol_specialSoundness) xorExtractorRealizedBy xorProver () y
    (sampleChallenge := fun _ => ProbComp.uniform Bool) (δ := 0)
    (by rw [ProbComp.eval_uniform]; exact CloseTo.refl _)
  rw [succProbability_xorAcceptanceGame] at h
  simp only [NNReal.coe_one, Fintype.card_bool, Nat.cast_ofNat, NNReal.coe_zero, mul_zero,
    add_zero] at h
  have hsqrt : (1 / 2 : ℝ) ≤ √(Game.succProbability (extractionGame xorEncoding
      (fun _ => encBool) (fun _ x y => x = y) (knowledgeExtractor xorEncoding
        (fun _ => ProbComp.uniform Bool) xorExtractWord xorProver) () y)) := by
    linarith
  have := (Real.le_sqrt' (by norm_num)).mp hsqrt
  linarith

/-- Averaged over a uniform statement `y ← PMF.uniformOfFintype Bool`,
`sq_sub_le_bind_extractionGame` gives the same `1 / 2` lower bound on extraction success. -/
example :
    (1 / 2 : ℝ) ≤ Game.succProbability ((PMF.uniformOfFintype Bool).bind fun y =>
      extractionGame xorEncoding (fun _ => encBool) (fun _ x y => x = y)
        (knowledgeExtractor xorEncoding (fun _ => ProbComp.uniform Bool) xorExtractWord xorProver)
        () y) := by
  have hacc : Game.succProbability ((PMF.uniformOfFintype Bool).bind fun y =>
      acceptanceGame (fun _ => xorProtocol) xorEncoding xorProver () y
        (PMF.uniformOfFintype Bool)) = 1 := by
    have hbind : ((PMF.uniformOfFintype Bool).bind fun y =>
        acceptanceGame (fun _ => xorProtocol) xorEncoding xorProver () y
          (PMF.uniformOfFintype Bool)) = PMF.pure true := by
      have hpure (y : Bool) : acceptanceGame (fun _ => xorProtocol) xorEncoding xorProver () y
          (PMF.uniformOfFintype Bool) = PMF.pure true := by
        have hacc' (c : Bool) : AcceptsWord (fun _ => xorProtocol) xorEncoding () y [] c
            (List.zipWith xor (xorEncoding.challenge () c) (xorEncoding.statement () y)) :=
          ⟨(), xor c y, rfl, rfl, by simp [SigmaProtocol.Accepts, xorProtocol]⟩
        simp only [acceptanceGame, xorProver, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
          PMF.monad_pure_eq_pure, PMF.pure_bind, hacc', decide_true, PMF.bind_const]
      simp only [hpure, PMF.bind_const]
    simp [hbind, Game.succProbability]
  have h := sq_sub_le_bind_extractionGame (P := fun _ => xorProtocol)
    (fun _ => xorProtocol_specialSoundness) xorExtractorRealizedBy xorProver ()
    (PMF.uniformOfFintype Bool) (sampleChallenge := fun _ => ProbComp.uniform Bool)
    (ProbComp.eval_uniform _)
  rw [hacc] at h
  simp only [NNReal.coe_one, one_pow, Fintype.card_bool, Nat.cast_ofNat] at h
  linarith

/-! ### Average-key Schnorr proof of knowledge and composed Schnorr efficiency -/

open scoped NNReal ENNReal in
/-- Under `F.DiscreteLog setup`, the echoing prover succeeds in `schnorrPoKGame` with negligible
probability. -/
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc) (hDL : F.DiscreteLog setup)
    (m : ℕ → ℕ) (hm0 : ∀ n, 0 < m n) (hm : ∀ n, ∀ d ∈ (setup n).support, m n ≤ F.order d)
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) :
    Negligible fun n => Game.succProbability (F.schnorrPoKGame setup (echoProver _) n) :=
  hDL.negligible_schnorrPoKGame hm0 hm hinv (isPPT_echoProver _)

open scoped ENNReal in
/-- Efficiency transfer for `andProof`, `orProof`, and `parallelRepetition` applied to
`schnorrFamily`. -/
example (F : PrimeOrderGroupFamily) (k : ℕ × F.Desc → ℕ) :
    EfficientSpecialSoundness
      (fun i => (F.schnorrFamily i).andProof (F.schnorrFamily i))
      (fun i x y => x.1 • F.generator i.2 = y.1 ∧ x.2 • F.generator i.2 = y.2)
      (F.schnorrEncoding.andProof F.schnorrEncoding)
      (fun i => encPair (F.encScalar i.2) (F.encScalar i.2))
      (fun i => andExtract (F.schnorrExtract i) (F.schnorrExtract i)) ∧
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
      (fun i => orExtract (F.schnorrExtract i) (F.schnorrExtract i)) ∧
    EfficientSpecialSoundness
      (fun i => (F.schnorrFamily i).parallelRepetition (k i))
      (fun i α u => α • F.generator i.2 = u)
      (F.schnorrEncoding.parallelRepetition k)
      (fun i => F.encScalar i.2)
      (fun i => parallelExtract (F.schnorrExtract i) (k i)) ∧
    EfficientSpecialHVZK
      (fun i => (F.schnorrFamily i).parallelRepetition (k i))
      (fun i α u => α • F.generator i.2 = u)
      (F.schnorrEncoding.parallelRepetition k)
      (fun i => parallelSimulate
        (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod (F.order i.2))
          (F.Carrier i.2) (F.generator i.2)) id (Function.Embedding.refl _)) (k i))
      (fun i => (k i : ℝ≥0∞) * (1 / 2 ^ i.1)) :=
  ⟨F.efficientSpecialSoundness_andProof_schnorr,
   F.efficientSpecialSoundness_orProof_schnorr,
   F.efficientSpecialSoundness_parallelRepetition_schnorr k,
   F.efficientSpecialHVZK_parallelRepetition_schnorr k⟩

end CslibFrontierTests.SigmaProofOfKnowledge
