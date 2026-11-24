/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.ChaumPedersenProtocol
public import CslibFrontier.Crypto.Computational.ChaumPedersenProtocol.Verifier
public import CslibFrontier.Crypto.Computational.DiscreteLog.SchnorrGroup
import CslibFrontier.Crypto.Protocols.SigmaProtocol.Interactive
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for the Chaum–Pedersen family

Checks of `PrimeOrderGroupFamily.chaumPedersenProbFamily`, `chaumPedersenFamily` and their
efficiency certificates: completeness, efficient verifier, efficient special soundness, prover word
realizations, `2 / 2 ^ n` statistical closeness and `ComputationalSpecialHVZK` in Schnorr groups and
over an arbitrary `PrimeOrderGroupFamily`, the word verifier agreeing with `Accepts`, concrete
verifier evaluations in the Schnorr group of order `11` modulo `23`, the extractor on two accepting
conversations, the simulator's exact acceptance on a non-Diffie–Hellman triple, and the word
encodings on a statement.
-/

public section

namespace CslibFrontierTests.Crypto.ChaumPedersenProtocol

open Cslib Cslib.Crypto Cslib.Crypto.Protocols Cslib.Crypto.Protocols.SigmaProtocol
  Cslib.Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

/-! ### The certificates in Schnorr groups -/

/-- Efficient verifier holds in Schnorr groups for both the fair-coin and ideal-nonce families. -/
example :
    EfficientVerifier schnorrGroups.chaumPedersenProbFamily schnorrGroups.chaumPedersenEncoding ∧
      EfficientVerifier schnorrGroups.chaumPedersenFamily schnorrGroups.chaumPedersenEncoding :=
  ⟨schnorrGroups.efficientVerifier_chaumPedersenProb,
    schnorrGroups.efficientVerifier_chaumPedersen⟩

/-- Completeness (Definition 19.3) and `CommitRealizedBy` hold for `chaumPedersenProbFamily` in
Schnorr groups. -/
example (i : ℕ × schnorrGroups.Desc) :
    (schnorrGroups.chaumPedersenProbFamily i).Complete
        (fun β (u, v, w) => β • schnorrGroups.generator i.2 = v ∧ β • u = w) ∧
      (schnorrGroups.chaumPedersenProbFamily i).CommitRealizedBy
        (schnorrGroups.chaumPedersenCommit i) :=
  ⟨schnorrGroups.chaumPedersenProbFamily_complete i, fun _ _ => rfl⟩

/-- Efficient special soundness (Definition 19.4) holds in Schnorr groups for
`chaumPedersenProbFamily`. -/
example :
    EfficientSpecialSoundness schnorrGroups.chaumPedersenProbFamily
      (fun i β (u, v, w) => β • schnorrGroups.generator i.2 = v ∧ β • u = w)
      schnorrGroups.chaumPedersenEncoding (fun i => schnorrGroups.encScalar i.2)
      schnorrGroups.chaumPedersenExtract :=
  schnorrGroups.efficientSpecialSoundness_chaumPedersenProb

/-- Computational special HVZK (Definition 20.6) holds for the fair-coin `chaumPedersenProbFamily`
in Schnorr groups with exact zero acceptance error, for any setup. -/
example (setup : ℕ → PMF schnorrGroups.Desc) :
    ComputationalSpecialHVZK schnorrGroups.chaumPedersenProbFamily
      (fun i β (u, v, w) => β • schnorrGroups.generator i.2 = v ∧ β • u = w)
      schnorrGroups.chaumPedersenEncoding (fun i => schnorrGroups.encScalar i.2)
      (fun n => (setup n).map (n, ·)) schnorrGroups.chaumPedersenSimulator (fun _ => 0) :=
  schnorrGroups.computationalSpecialHVZK_chaumPedersen setup

/-! ### Clients over any family -/

variable (F : PrimeOrderGroupFamily)

/-- A client of the extractor: from two accepting conversations with one commitment and distinct
challenges, `chaumPedersenExtract` returns `β` with `β • g = v` and `β • u = w`. -/
example (i : ℕ × F.Desc) (u v w : F.Carrier i.2) (t : F.Carrier i.2 × F.Carrier i.2)
    (c z c' z' : ZMod (F.order i.2)) (hc : c ≠ c')
    (hz : (F.chaumPedersenFamily i).Accepts (u, v, w) t c z)
    (hz' : (F.chaumPedersenFamily i).Accepts (u, v, w) t c' z') :
    F.chaumPedersenExtract i (u, v, w) t c z c' z' • F.generator i.2 = v ∧
      F.chaumPedersenExtract i (u, v, w) t c z c' z' • u = w :=
  F.efficientSpecialSoundness_chaumPedersen.specialSoundness i (u, v, w) t c z c' z' hc hz hz'

/-- The extractor does not read the statement or the commitment. -/
example (i : ℕ × F.Desc) (y y' : F.Carrier i.2 × F.Carrier i.2 × F.Carrier i.2)
    (t t' : F.Carrier i.2 × F.Carrier i.2) (c z c' z' : ZMod (F.order i.2)) :
    F.chaumPedersenExtract i y t c z c' z' = F.chaumPedersenExtract i y' t' c z c' z' := rfl

/-- The simulator is within `2 / 2 ^ n` of the fair-coin honest prover (and within `1 / 2 ^ n` of
the ideal-sampling honest prover) on every Diffie–Hellman triple. -/
example (n : ℕ) (d : F.Desc) (β : ZMod (F.order d)) (u : F.Carrier d) (c : ZMod (F.order d)) :
    CloseTo ((F.chaumPedersenProbFamily (n, d)).transcript β (u, β • F.generator d, β • u) c)
        (ProbComp.eval (F.chaumPedersenSimulator (n, d) (u, β • F.generator d, β • u) c))
        (2 / 2 ^ n) ∧
      CloseTo ((F.chaumPedersenFamily (n, d)).transcript β (u, β • F.generator d, β • u) c)
        (ProbComp.eval (F.chaumPedersenSimulator (n, d) (u, β • F.generator d, β • u) c))
        (1 / 2 ^ n) :=
  ⟨F.closeTo_transcript_chaumPedersenProbFamily_simulator (n, d) ⟨rfl, rfl⟩ c,
    F.simulatorRealizedBy_chaumPedersenSimulator.closeTo_transcript
      F.efficientSpecialHVZK_chaumPedersen_ideal.specialHVZK (i := (n, d)) ⟨rfl, rfl⟩ c⟩

/-- The fair-coin prover's commitment and response word realizations are uniform strict PPT and
agree with `chaumPedersenCommit` and `respond` on encodings. -/
example (i : ℕ × F.Desc) (β r c : ZMod (F.order i.2))
    (y : F.Carrier i.2 × F.Carrier i.2 × F.Carrier i.2) :
    IsPPTOn (encPair F.chaumPedersenEncoding.index encBits) (encPair encBits encBits)
        F.chaumPedersenCommitWord ∧
      ProbComp.eval (F.chaumPedersenCommitWord (i, F.chaumPedersenEncoding.statement i y)) =
        (ProbComp.eval (F.chaumPedersenCommit i β y)).map
          (Prod.map (F.chaumPedersenEncoding.commitment i) (F.encScalar i.2)) ∧
      F.schnorrRespondBits
          (i.2, F.encScalar i.2 β, F.encScalar i.2 r, F.chaumPedersenEncoding.challenge i c) =
        F.chaumPedersenEncoding.response i ((F.chaumPedersenProbFamily i).respond β y r c) :=
  ⟨F.isPPTOn_chaumPedersenCommitWord, F.eval_chaumPedersenCommitWord i β y,
    F.schnorrRespondBits_chaumPedersen i β y r c⟩

/-! ### The encodings -/

/-- A statement word is the framed encoding of `u`, then of `v`, then the encoding of `w`. -/
example (i : ℕ × F.Desc) (u v w : F.Carrier i.2) :
    F.chaumPedersenEncoding.statement i (u, v, w) =
      frame (F.encode i.2 u) ++ (frame (F.encode i.2 v) ++ F.encode i.2 w) := rfl

/-- A commitment word is the framed encoding of `t₁`, then the encoding of `t₂`. -/
example (i : ℕ × F.Desc) (t₁ t₂ : F.Carrier i.2) :
    F.chaumPedersenEncoding.commitment i (t₁, t₂) =
      frame (F.encode i.2 t₁) ++ F.encode i.2 t₂ := rfl

/-- A client of the word program through its specification: on an encoded statement and
challenge, every output of `chaumPedersenSimulateWord` is the encoding of an accepting
conversation. -/
example (i : ℕ × F.Desc) (y : F.Carrier i.2 × F.Carrier i.2 × F.Carrier i.2)
    (c : ZMod (F.order i.2)) (out : List Bool × List Bool)
    (h : out ∈ (ProbComp.eval (F.chaumPedersenSimulateWord
      (i, F.chaumPedersenEncoding.statement i y, F.chaumPedersenEncoding.challenge i c))).support) :
    ∃ t z, out = (F.chaumPedersenEncoding.commitment i t, F.chaumPedersenEncoding.response i z) ∧
      (F.chaumPedersenFamily i).Accepts y t c z := by
  rw [F.eval_chaumPedersenSimulateWord, PMF.mem_support_map_iff] at h
  obtain ⟨⟨t, z⟩, htz, rfl⟩ := h
  exact ⟨t, z, rfl, ((PMF.toOuterMeasure_apply_eq_one_iff _ _).mp
    (F.accepts_chaumPedersenSimulator i y c)) htz⟩

/-- A client of the word verifier: on an encoded conversation, `chaumPedersenVerifyWord` agrees with
`Accepts`. -/
example (i : ℕ × F.Desc) (y : F.Carrier i.2 × F.Carrier i.2 × F.Carrier i.2)
    (t : F.Carrier i.2 × F.Carrier i.2) (c z : ZMod (F.order i.2)) :
    (F.chaumPedersenVerifyWord (i, F.chaumPedersenEncoding.statement i y,
      F.chaumPedersenEncoding.commitment i t, F.chaumPedersenEncoding.challenge i c,
      F.chaumPedersenEncoding.response i z) = true) ↔
      (F.chaumPedersenFamily i).Accepts y t c z := by
  rw [F.verifierRealizedBy_chaumPedersenVerifyWord i y t c z]
  rfl

/-! ### Concrete evaluations -/

/-- The Schnorr group of prime order `11` inside `(ZMod 23)ˣ`, generated by `2`. -/
def d23 : schnorrGroups.Desc :=
  ⟨(23, 11, 2), ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

private theorem smul_bits_d23 (a : ℕ) :
    schnorrGroups.encode d23 ((a : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23) =
      (2 ^ a % 23).bits := by
  have hg : schnorrGroups.encode d23 (schnorrGroups.generator d23) =
      (d23 : SchnorrGroup.Desc).generatorResidue.bits :=
    SchnorrGroup.encode_generator (d23 : SchnorrGroup.Desc)
  rw [← schnorrGroups.smul_encode, hg]
  rfl

private theorem d23_chaumPedersenVerifyWord_eq (au av aw at1 at2 : ℕ)
    (c z : ZMod (schnorrGroups.order d23)) :
    schnorrGroups.chaumPedersenVerifyWord
      ((0, d23), frame (2 ^ au % 23).bits ++ (frame (2 ^ av % 23).bits ++ (2 ^ aw % 23).bits),
        frame (2 ^ at1 % 23).bits ++ (2 ^ at2 % 23).bits, c.val.bits, z.val.bits) =
      decide ((schnorrGroups.chaumPedersenFamily (0, d23)).Accepts
        ((au : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23,
         (av : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23,
         (aw : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23)
        ((at1 : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23,
         (at2 : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23)
        c z) := by
  have hs : schnorrGroups.chaumPedersenEncoding.statement (0, d23)
      ((au : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23,
       (av : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23,
       (aw : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23) =
      frame (2 ^ au % 23).bits ++ (frame (2 ^ av % 23).bits ++ (2 ^ aw % 23).bits) := by
    change frame (schnorrGroups.encode d23 _) ++
        (frame (schnorrGroups.encode d23 _) ++ schnorrGroups.encode d23 _) = _
    rw [smul_bits_d23 au, smul_bits_d23 av, smul_bits_d23 aw]
  have ht : schnorrGroups.chaumPedersenEncoding.commitment (0, d23)
      ((at1 : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23,
       (at2 : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23) =
      frame (2 ^ at1 % 23).bits ++ (2 ^ at2 % 23).bits := by
    change frame (schnorrGroups.encode d23 _) ++ schnorrGroups.encode d23 _ = _
    rw [smul_bits_d23 at1, smul_bits_d23 at2]
  have hc : schnorrGroups.chaumPedersenEncoding.challenge (0, d23) c = c.val.bits := rfl
  have hz : schnorrGroups.chaumPedersenEncoding.response (0, d23) z = z.val.bits := rfl
  rw [← hs, ← ht, ← hc, ← hz, schnorrGroups.verifierRealizedBy_chaumPedersenVerifyWord]
  rfl

/-- Concrete accepting Chaum–Pedersen transcript in `d23`: encoded statement
`(4, 8, 18) = (2^2, 2^3, 2^6)`, commitment `(4, 16) = (2^2, 2^4)`, challenge `1`, response
`5 = 2 + 1 * 3` (`2^5 = 9 = 4 * 8`, `4^5 = 12 = 16 * 18` mod `23`). -/
example : schnorrGroups.chaumPedersenVerifyWord
    ((0, d23), frame (Nat.bits 4) ++ (frame (Nat.bits 8) ++ Nat.bits 18),
      frame (Nat.bits 4) ++ Nat.bits 16, Nat.bits 1, Nat.bits 5) = true := by
  change schnorrGroups.chaumPedersenVerifyWord
    ((0, d23), frame (2 ^ 2 % 23).bits ++ (frame (2 ^ 3 % 23).bits ++ (2 ^ 6 % 23).bits),
      frame (2 ^ 2 % 23).bits ++ (2 ^ 4 % 23).bits,
      ((1 : ZMod (schnorrGroups.order d23)).val).bits,
      ((5 : ZMod (schnorrGroups.order d23)).val).bits) = true
  rw [d23_chaumPedersenVerifyWord_eq 2 3 6 2 4 1 5, decide_eq_true_iff,
    PrimeOrderGroupFamily.chaumPedersenFamily, chaumPedersen_accepts_iff]
  simp only [Function.Embedding.refl_apply, one_smul]
  refine ⟨?_, ?_⟩ <;> module

/-- Changing the statement to the non-Diffie–Hellman triple `(4, 8, 2)` rejects the same
conversation words. -/
example : schnorrGroups.chaumPedersenVerifyWord
    ((0, d23), frame (Nat.bits 4) ++ (frame (Nat.bits 8) ++ Nat.bits 2),
      frame (Nat.bits 4) ++ Nat.bits 16, Nat.bits 1, Nat.bits 5) = false := by
  change schnorrGroups.chaumPedersenVerifyWord
    ((0, d23), frame (2 ^ 2 % 23).bits ++ (frame (2 ^ 3 % 23).bits ++ (2 ^ 1 % 23).bits),
      frame (2 ^ 2 % 23).bits ++ (2 ^ 4 % 23).bits,
      ((1 : ZMod (schnorrGroups.order d23)).val).bits,
      ((5 : ZMod (schnorrGroups.order d23)).val).bits) = false
  rw [d23_chaumPedersenVerifyWord_eq 2 3 1 2 4 1 5, decide_eq_false_iff_not,
    PrimeOrderGroupFamily.chaumPedersenFamily, chaumPedersen_accepts_iff]
  rintro ⟨-, h2⟩
  simp only [Function.Embedding.refl_apply, one_smul] at h2
  have hzero : (5 : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23 = 0 := by
    calc
      (5 : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23 =
          (5 : ZMod (schnorrGroups.order d23)) •
            (((2 : ℕ) : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23) -
          (((4 : ℕ) : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23 +
            ((1 : ℕ) : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23) := by
        module
      _ = 0 := sub_eq_zero.mpr h2
  refine schnorrGroups.generator_ne_zero d23 ((smul_eq_zero.mp hzero).resolve_left ?_)
  change (5 : ZMod 11) ≠ 0
  decide

/-- Changing the response to `6` rejects the valid Diffie–Hellman statement `(4, 8, 18)`. -/
example : schnorrGroups.chaumPedersenVerifyWord
    ((0, d23), frame (Nat.bits 4) ++ (frame (Nat.bits 8) ++ Nat.bits 18),
      frame (Nat.bits 4) ++ Nat.bits 16, Nat.bits 1, Nat.bits 6) = false := by
  change schnorrGroups.chaumPedersenVerifyWord
    ((0, d23), frame (2 ^ 2 % 23).bits ++ (frame (2 ^ 3 % 23).bits ++ (2 ^ 6 % 23).bits),
      frame (2 ^ 2 % 23).bits ++ (2 ^ 4 % 23).bits,
      ((1 : ZMod (schnorrGroups.order d23)).val).bits,
      ((6 : ZMod (schnorrGroups.order d23)).val).bits) = false
  rw [d23_chaumPedersenVerifyWord_eq 2 3 6 2 4 1 6, decide_eq_false_iff_not,
    PrimeOrderGroupFamily.chaumPedersenFamily, chaumPedersen_accepts_iff]
  rintro ⟨h1, -⟩
  simp only [Function.Embedding.refl_apply, one_smul] at h1
  have hzero : (1 : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23 = 0 := by
    calc
      (1 : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23 =
          (6 : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23 -
          (((2 : ℕ) : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23 +
            ((3 : ℕ) : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23) := by
        module
      _ = 0 := sub_eq_zero.mpr h1
  exact schnorrGroups.generator_ne_zero d23 ((smul_eq_zero.mp hzero).resolve_left one_ne_zero)

/-- Concrete `chaumPedersenExtract` in `d23`: `(1 - 2)⁻¹ * (5 - 8) = (-1)⁻¹ * (-3) = 3` in
`ZMod 11`. -/
example :
    let g := schnorrGroups.generator d23
    schnorrGroups.chaumPedersenExtract (0, d23) (g, g, g) (g, g) 1 5 2 8 = 3 := by
  decide

/-- A concrete non-Diffie–Hellman triple in `d23` has no witness, yet `chaumPedersenSimulator`
accepts on it with probability `1`. -/
example (c : ZMod (schnorrGroups.order d23)) :
    let g := schnorrGroups.generator d23
    let y := ((2 : ZMod (schnorrGroups.order d23)) • g,
      (3 : ZMod (schnorrGroups.order d23)) • g, (1 : ZMod (schnorrGroups.order d23)) • g)
    (¬ ∃ β : ZMod (schnorrGroups.order d23), β • g = y.2.1 ∧ β • y.1 = y.2.2) ∧
      (ProbComp.eval (schnorrGroups.chaumPedersenSimulator (0, d23) y c)).toOuterMeasure
        {tz | (schnorrGroups.chaumPedersenFamily (0, d23)).Accepts y tz.1 c tz.2} = 1 := by
  refine ⟨?_, schnorrGroups.accepts_chaumPedersenSimulator (0, d23) _ c⟩
  rintro ⟨β, h1, h2⟩
  have hβ3 : β - 3 = 0 := (smul_eq_zero.mp (by
    rw [sub_smul, sub_eq_zero]
    exact h1)).resolve_right (schnorrGroups.generator_ne_zero d23)
  have h5g : (5 : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23 = 0 := by
    calc
      (5 : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23 =
          β • ((2 : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23) -
          (1 : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23 -
          (2 : ZMod (schnorrGroups.order d23)) •
            ((β - 3) • schnorrGroups.generator d23) := by
        module
      _ = 0 := by rw [h2, sub_self, zero_sub, hβ3, zero_smul, smul_zero, neg_zero]
  refine schnorrGroups.generator_ne_zero d23 ((smul_eq_zero.mp h5g).resolve_left ?_)
  change (5 : ZMod 11) ≠ 0
  decide

end CslibFrontierTests.Crypto.ChaumPedersenProtocol
