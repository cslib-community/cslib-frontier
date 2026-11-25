/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Crypto.Protocols.AnonymousToken.RandomTargetPolyTime
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for polynomial-time random-target reduction witnesses

Exercises `Cslib.Crypto.AnonymousToken.RandomTargetPolyTime` via a `module` client with ordinary
imports:
* checked `wordClaimListDecoder` round-trips and full-list rejection on any out-of-range claim
  index `i ≥ N` (including `i = N` modulo wraparound traps and `budget + 2`-length mixed lists);
* concrete inhabited message families `Fin 2` (`N n = 2`) and fixed-length bitstrings
  `{ b : List Bool // b.length = n + 1 }` with exponential challenge space `N n = 2 ^ (n + 1)` and
  binary polynomial-time `slotWord`;
* concrete `WordSignatureScheme` (`idWordSigScheme`), certified `IsOraclePPT` and `1`-query
  `wordCollisionAttack`, exact `1` colliding-target witness, exact `1 / 2` uniform `Bool`-target
  witness matching `Signature.succProbability_collisionAttack_uniform`, exact `0` honest run,
  `> budget + 1` prefix truncation behavior;
* concrete non-vacuous instantiations of `negligible_extractedRedemptionWordGame`,
  `indistinguishable_extractedRedemptionWordGame`, and
  `succWithin_extractedRedemptionWordGame_withinQueries`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.AnonymousTokenRandomTargetPolyTime

open Cslib Cslib.Crypto Cslib.Crypto.AnonymousToken Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-! ### 1. Checked claim-list decoding and out-of-range index rejection -/

example :
    wordClaimListDecoder 2 (encWordClaimList [(0, [true]), (1, [false])]) =
      some [⟨0, [true]⟩, ⟨1, [false]⟩] := by
  let xs : List (Fin 2 × List Bool) := [(0, [true]), (1, [false])]
  have h := wordClaimListDecoder_encWordClaimList_map 2 xs Prod.fst Prod.snd
  simpa [xs] using h

-- Out-of-range index `i = 2 ≥ N = 2` is rejected cleanly (`none`) rather than wrapping `2 % 2 = 0`.
example :
    wordClaimListDecoder 2 (encWordClaimList [(0, [false]), (2, [false])]) = none :=
  wordClaimListDecoder_eq_none_of_mem_ge (p := (2, [false])) (by simp) (by omega)

-- A `budget + 2`-length list with one bad index rejects the whole list (never `.filterMap` to `2`).
example :
    wordClaimListDecoder 2
      (encWordClaimList [(0, [false]), (2, [false]), (1, [false])]) = none :=
  wordClaimListDecoder_eq_none_of_mem_ge (p := (2, [false])) (by simp) (by omega)

/-! ### 2. Concrete `WordSignatureScheme` and adversaries -/

/-- Deterministic word signature scheme signing a message with itself. -/
private def idWordSigScheme : WordSignatureScheme where
  keyGen _ := pure ([], [])
  sign _ msg := pure msg
  verify _ msg sig := decide (msg = sig)
  keyGen_ppt := by ppt
  sign_ppt := by ppt
  verify_polyTime := by polytime
  verify_sign := by
    intro _ _ _ _ msg sig hsig
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hsig
    subst hsig
    simp

/-- Word-level out-of-range one-more adversary outputting `[(0, [false]), (2, [false]), (1, [])]`,
testing full-list rejection inside `oneMoreWordGame` when `N n = 2` and `budget n = 1`. -/
private def badOutOfRangeOneMoreAdversary : WordOneMoreAdversary :=
  fun _ _ => pure (encWordClaimList [(0, [false]), (2, [false]), (1, [])])

example (n : ℕ) :
    Game.succProbability (ProbComp.eval
      (oneMoreWordGame idWordSigScheme (fun _ => 2)
        (fun _ _ => pure fun i => match i with | 0 => [false] | 1 => [true])
        (fun _ => 1) badOutOfRangeOneMoreAdversary n)) = 0 := by
  have hdec : wordClaimListDecoder 2
      (encWordClaimList [(0, [false]), (2, [false]), (1, [])]) = none :=
    wordClaimListDecoder_eq_none_of_mem_ge (p := (2, [false])) (by simp) (by omega)
  simp only [oneMoreWordGame, Signature.oneMoreExperiment, idWordSigScheme,
    WordSignatureScheme.toScheme_keyGen, WordOneMoreAdversary.toTyped,
    badOutOfRangeOneMoreAdversary, ProbOracleComp.simulate_pure, map_pure, hdec,
    Option.getD_none, ProbOracleComp.runLog, ProbOracleComp.runState, OracleComp.interpret_pure,
    StateT.run_pure, pure_bind, Signature.oneMoreAccept, List.length_nil, ProbComp.eval_pure,
    Game.succProbability]
  simp

/-! ### 3. Inhabited message families: `Fin 2` and exponential `FixedBits (n + 1)` -/

private def encFinTwo : Fin 2 ↪ List Bool where
  toFun i := [decide (i = 1)]
  inj' i j h := by
    fin_cases i <;> fin_cases j <;> simp_all

private def decFinTwo : Decoder encFinTwo where
  decode w := if w.headD false then 1 else 0
  decode_enc i := by fin_cases i <;> rfl
  computable := by
    have hhead : ComputableInPolyTime (fun w : List Bool => w.headD false) encBits encBool :=
      ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false
    have hfin : ComputableInPolyTime (fun b : Bool => if b then (1 : Fin 2) else 0)
        encBool encFinTwo := ComputableInPolyTime.of_finite _
    exact (hfin.comp hhead).exists_degree

private def slotWordFinTwo (_ : ℕ) (w : List Bool) : ℕ :=
  (w.headD false).toNat

private theorem slotWordFinTwo_eq (n : ℕ) (w : List Bool) :
    slotWordFinTwo n w = ((Equiv.refl (Fin 2)).toEmbedding (decFinTwo.decode w)).val := by
  simp only [slotWordFinTwo, decFinTwo, List.headD_eq_head?_getD]
  cases w.head?.getD false <;> rfl

private theorem computableInPolyTime_slotWordFinTwo :
    ComputableInPolyTime (fun p : ℕ × List Bool => slotWordFinTwo p.1 p.2)
      (encPair encUnary encBits) encNat := by
  have hsnd : ComputableInPolyTime (fun p : ℕ × List Bool => p.2)
      (encPair encUnary encBits) encBits := ComputableInPolyTime.snd _ _
  have hhead : ComputableInPolyTime (fun p : ℕ × List Bool => p.2.headD false)
      (encPair encUnary encBits) encBool :=
    (ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false).comp hsnd
  exact (ComputableInPolyTime.of_finite (encIn := encBool) (encOut := encNat) Bool.toNat).comp
    hhead

/-- Fixed-length bitstrings `{ b : List Bool // b.length = len }`, always inhabited by all-zero. -/
private abbrev FixedBits (len : ℕ) : Type :=
  { b : List Bool // b.length = len }

private instance (len : ℕ) : Inhabited (FixedBits len) :=
  ⟨⟨List.replicate len false, List.length_replicate⟩⟩

private def encFixedBits (len : ℕ) : FixedBits len ↪ List Bool :=
  ⟨Subtype.val, Subtype.val_injective⟩

private def decodeFixedBits (len : ℕ) (w : List Bool) : FixedBits len :=
  ⟨(w ++ List.replicate len false).take len, by
    rw [List.length_take_of_le]
    simp⟩

private theorem decodeFixedBits_enc (len : ℕ) (x : FixedBits len) :
    decodeFixedBits len (encFixedBits len x) = x := by
  ext1
  dsimp only [decodeFixedBits, encFixedBits, Function.Embedding.coeFn_mk]
  rw [List.take_append_of_le_length (le_of_eq x.2.symm)]
  simp [x.2]

private def decFixedBits (len : ℕ) : Decoder (encFixedBits len) where
  decode := decodeFixedBits len
  decode_enc := decodeFixedBits_enc len
  computable := by
    have happ : ComputableInPolyTime (fun w : List Bool => w ++ List.replicate len false)
        encBits encBits :=
      ComputableInPolyTime.bitsAppend ComputableInPolyTime.id'
        (ComputableInPolyTime.const (List.replicate len false))
    have htake : ComputableInPolyTime
        (fun w : List Bool => (w ++ List.replicate len false).take len) encBits encBits :=
      ComputableInPolyTime.bitsTakeWithInput happ (ComputableInPolyTime.const len)
    exact (htake.of_enc_eq fun _ => rfl).exists_degree

private theorem ofBits_inj_of_length_eq :
    ∀ {l₁ l₂ : List Bool}, l₁.length = l₂.length → ofBits l₁ = ofBits l₂ → l₁ = l₂
  | [], [], _, _ => rfl
  | b₁ :: l₁, b₂ :: l₂, hlen, heq => by
    simp only [ofBits, List.foldr_cons, Nat.bit_val] at heq
    have hb : b₁ = b₂ := by
      cases b₁ <;> cases b₂ <;> simp at heq ⊢ <;> omega
    subst hb
    have hrest : l₁.foldr Nat.bit 0 = l₂.foldr Nat.bit 0 := by omega
    rw [ofBits_inj_of_length_eq (by simpa using hlen) hrest]

private def slotFixedBits (n : ℕ) : FixedBits (n + 1) ↪ Fin (2 ^ (n + 1)) where
  toFun x := ⟨ofBits x.1, Nat.lt_of_lt_of_eq (Nat.foldr_bit_lt x.1) (congrArg (2 ^ ·) x.2)⟩
  inj' x y h := by
    apply Subtype.ext
    exact ofBits_inj_of_length_eq (x.2.trans y.2.symm) (congrArg Fin.val h)

private def slotWordFixedBits (n : ℕ) (w : List Bool) : ℕ :=
  ofBits ((w ++ List.replicate (n + 1) false).take (n + 1))

private theorem slotWordFixedBits_eq (n : ℕ) (w : List Bool) :
    slotWordFixedBits n w = (slotFixedBits n ((decFixedBits (n + 1)).decode w)).val := rfl

private theorem computableInPolyTime_slotWordFixedBits :
    ComputableInPolyTime (fun p : ℕ × List Bool => slotWordFixedBits p.1 p.2)
      (encPair encUnary encBits) encNat := by
  have hlen : ComputableInPolyTime (fun p : ℕ × List Bool => p.1 + 1)
      (encPair encUnary encBits) encUnary := by
    have hfst : ComputableInPolyTime (fun p : ℕ × List Bool => p.1)
        (encPair encUnary encBits) encUnary := ComputableInPolyTime.fst _ _
    exact hfst.unary_add' (ComputableInPolyTime.const 1)
  have hpad : ComputableInPolyTime (fun p : ℕ × List Bool => List.replicate (p.1 + 1) false)
      (encPair encUnary encBits) encBits :=
    (ComputableInPolyTime.bitsReplicate false).comp hlen
  have happ : ComputableInPolyTime (fun p : ℕ × List Bool => p.2 ++ List.replicate (p.1 + 1) false)
      (encPair encUnary encBits) encBits :=
    ComputableInPolyTime.bitsAppend (ComputableInPolyTime.snd _ _) hpad
  have htake : ComputableInPolyTime
      (fun p : ℕ × List Bool => (p.2 ++ List.replicate (p.1 + 1) false).take (p.1 + 1))
      (encPair encUnary encBits) encBits :=
    ComputableInPolyTime.bitsTakeWithInput happ hlen
  exact ComputableInPolyTime.bitsToNat.comp htake

/-! ### 4. Concrete `wordCollisionAttack`, `= 1`, `= 1/2`, `= 0`, and truncation checks -/

/-- Uniform oracle-PPT collision attack against `N = 2`, `budget = 1`: queries the signing oracle
once on target `0` (truncating the reply to `y0.length + 1` bits) and outputs two distinct-slot
tokens `[false]` and `[true]` sharing that signature. -/
private def wordCollisionAttack : WordRedemptionAdversary :=
  fun _ input => do
    let y0 := (wordTargetsInputDecoder.decode input).2.getD 0 []
    let sig ← List.take (y0.length + 1) <$> ProbOracleComp.query ((), y0)
    return [⟨⟨[false], ()⟩, sig⟩, ⟨⟨[true], ()⟩, sig⟩]

private theorem isOraclePPT_wordCollisionAttack :
    IsOraclePPT (encRedemptionTokenList encBits) wordCollisionAttack := by
  let encIn := encPair encUnary encBits
  have hin : ComputableInPolyTime (fun p : ℕ × List Bool => p.2) encIn encBits :=
    ComputableInPolyTime.snd _ _
  have hdec : ComputableInPolyTime
      (fun p : ℕ × List Bool => wordTargetsInputDecoder.decode p.2) encIn encWordTargetsInput :=
    wordTargetsInputDecoder.computableInPolyTime.comp hin
  have hys : ComputableInPolyTime
      (fun p : ℕ × List Bool => (wordTargetsInputDecoder.decode p.2).2)
      encIn (encList encBits) := hdec.snd'
  have hy0 : ComputableInPolyTime
      (fun p : ℕ × List Bool => ((wordTargetsInputDecoder.decode p.2).2).getD 0 [])
      encIn encBits :=
    ComputableInPolyTime.listGetDWithInput hys (ComputableInPolyTime.const 0) []
  have hlim : ComputableInPolyTime
      (fun p : ℕ × List Bool => (((wordTargetsInputDecoder.decode p.2).2).getD 0 []).length + 1)
      encIn encUnary :=
    (ComputableInPolyTime.length_bits.comp hy0).unary_add' (ComputableInPolyTime.const 1)
  have hq : IsOraclePPTOn encIn encBits (fun p : ℕ × List Bool =>
      let y0 := (wordTargetsInputDecoder.decode p.2).2.getD 0 []
      List.take (y0.length + 1) <$> ProbOracleComp.query ((), y0)) :=
    IsOraclePPTOn.query_take () hy0 hlim
  have hret : ComputableInPolyTime
      (fun q : (ℕ × List Bool) × List Bool =>
        ([⟨⟨[false], ()⟩, q.2⟩, ⟨⟨[true], ()⟩, q.2⟩] :
          List (Token (List Bool) Unit (List Bool))))
      (encPair encIn encBits) (encRedemptionTokenList encBits) := by
    fun_prop
  have heq : (fun p : ℕ × List Bool =>
      (fun sig => ([⟨⟨[false], ()⟩, sig⟩, ⟨⟨[true], ()⟩, sig⟩] :
          List (Token (List Bool) Unit (List Bool)))) <$>
        (let y0 := (wordTargetsInputDecoder.decode p.2).2.getD 0 []
         List.take (y0.length + 1) <$> ProbOracleComp.query ((), y0))) =
      fun p => wordCollisionAttack p.1 p.2 := by
    funext ⟨n, input⟩
    simp [wordCollisionAttack, bind_pure_comp]
  exact ((hq.map_with hret).congr fun a State oracle s => by
    have hfun : ((fun q => (fun sig => [⟨⟨[false], ()⟩, sig⟩, ⟨⟨[true], ()⟩, sig⟩]) <$> _) a) =
        wordCollisionAttack a.1 a.2 := congrFun heq a
    rw [← hfun]).isOraclePPT

private theorem withinWordQueries_wordCollisionAttack (n : ℕ) :
    WithinWordQueries n 1 wordCollisionAttack := by
  intro input
  simp only [wordCollisionAttack, ProbOracleComp.IsQueryBounded]
  have hq : OracleComp.IsCostBounded (Sum.elim (fun _ => 0) (fun _ => 1))
      (List.take (((wordTargetsInputDecoder.decode input).2.getD 0 []).length + 1) <$>
        ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
          ((), (wordTargetsInputDecoder.decode input).2.getD 0 [])) 1 :=
    (OracleComp.isCostBounded_map_iff _ _ _).mpr (ProbOracleComp.IsQueryBounded.query _)
  exact hq.bind fun _ => OracleComp.IsCostBounded.pure _ 0

-- Colliding targets `[false, false]` yield probability `1` in both `extractedRedemptionWordGame`
-- and `oneMoreWordGame`.
example (n : ℕ) :
    Game.succProbability (ProbComp.eval
      (extractedRedemptionWordGame idWordSigScheme (fun _ => 2)
        (fun _ _ => pure fun _ => [false]) (fun _ => Fin 2) (fun _ => encFinTwo)
        (fun _ => decFinTwo) (fun _ => (Equiv.refl (Fin 2)).toEmbedding) (fun _ => 1)
        wordCollisionAttack n)) = 1 ∧
    Game.succProbability (ProbComp.eval
      (oneMoreWordGame idWordSigScheme (fun _ => 2) (fun _ _ => pure fun _ => [false])
        (fun _ => 1) (reduceRedemptionsWord (fun _ => 1) slotWordFinTwo wordCollisionAttack) n)) =
      1 := by
  have hdec : (wordTargetsInputDecoder.decode
      (encWordTargetsInput ([], List.ofFn fun _ : Fin 2 => ([false] : List Bool)))).2 =
      [[false], [false]] := by
    rw [wordTargetsInputDecoder.decode_enc]
    rfl
  have h1 : ProbComp.eval
      (extractedRedemptionWordGame idWordSigScheme (fun _ => 2)
        (fun _ _ => pure fun _ => [false]) (fun _ => Fin 2) (fun _ => encFinTwo)
        (fun _ => decFinTwo) (fun _ => (Equiv.refl (Fin 2)).toEmbedding) (fun _ => 1)
        wordCollisionAttack n) = PMF.pure true := by
    simp only [extractedRedemptionWordGame, extractedRedemptionExperiment,
      WordSignatureScheme.toScheme_keyGen, WordSignatureScheme.toScheme_sign,
      idWordSigScheme, WordRedemptionAdversary.toTyped,
      ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind,
      ProbOracleComp.runLog, ProbOracleComp.runState]
    rw [ProbOracleComp.eval_run_interpret_eq_runWith]
    dsimp only [wordCollisionAttack]
    rw [hdec]
    simp [ProbOracleComp.simulate, OracleComp.substitute_eq_interpret,
      ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
      extractedRedemptionAccept, Token.valid, decFinTwo]
  have h2 : ProbComp.eval
      (oneMoreWordGame idWordSigScheme (fun _ => 2) (fun _ _ => pure fun _ => [false])
        (fun _ => 1) (reduceRedemptionsWord (fun _ => 1) slotWordFinTwo wordCollisionAttack) n) =
      PMF.pure true := by
    rw [eval_oneMoreGame_reduceRedemptionsWord_eq idWordSigScheme (fun _ => 2)
      (fun _ _ => pure fun _ => [false]) (fun _ => 1) slotWordFinTwo n decFinTwo
      (Equiv.refl (Fin 2)).toEmbedding (slotWordFinTwo_eq n) wordCollisionAttack]
    simp only [Signature.oneMoreExperiment, reduceRedemptions, idWordSigScheme,
      WordSignatureScheme.toScheme_keyGen, WordSignatureScheme.toScheme_sign,
      WordRedemptionAdversary.toTyped,
      ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind,
      ProbOracleComp.runLog, ProbOracleComp.runState]
    rw [ProbOracleComp.eval_run_interpret_eq_runWith]
    dsimp only [wordCollisionAttack]
    rw [hdec]
    simp [ProbOracleComp.simulate, OracleComp.substitute_eq_interpret,
      ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
      Signature.oneMoreAccept, decFinTwo]
  rw [h1, h2]
  simp [Game.succProbability]

private def boolIdScheme : Signature.Scheme Unit Unit Bool Bool where
  keyGen := pure ((), ())
  sign _ b := pure b
  verify _ y s := decide (y = s)

private theorem boolIdScheme_verify_inj (pk : Unit) (y z s : Bool)
    (hy : boolIdScheme.verify pk y s = true) (hz : boolIdScheme.verify pk z s = true) :
    y = z := by
  simp only [boolIdScheme, decide_eq_true_eq] at hy hz
  exact hy.trans hz.symm

private noncomputable def uniformBoolWordTargets : ℕ → List Bool → ProbComp (Fin 2 → List Bool) :=
  fun _ _ => (fun f i => [f i]) <$> $ᵗ (Fin 2 → Bool)

-- Uniform `Bool`-valued 1-bit targets yield exact `1 / 2` collision success probability,
-- matching `Signature.succProbability_collisionAttack_uniform` on `boolIdScheme`.
example (n : ℕ) :
    Game.succProbability (ProbComp.eval
      (extractedRedemptionWordGame idWordSigScheme (fun _ => 2) uniformBoolWordTargets
        (fun _ => Fin 2) (fun _ => encFinTwo) (fun _ => decFinTwo)
        (fun _ => (Equiv.refl (Fin 2)).toEmbedding) (fun _ => 1) wordCollisionAttack n)) =
      (2 : ℝ≥0)⁻¹ ∧
    Game.succProbability (ProbComp.eval
      (extractedRedemptionWordGame idWordSigScheme (fun _ => 2) uniformBoolWordTargets
        (fun _ => Fin 2) (fun _ => encFinTwo) (fun _ => decFinTwo)
        (fun _ => (Equiv.refl (Fin 2)).toEmbedding) (fun _ => 1) wordCollisionAttack n)) =
      (Signature.oneMoreExperiment boolIdScheme (fun _ => $ᵗ (Fin 2 → Bool)) 1
        Signature.collisionAttack).succProbability := by
  have hunif :
      (Signature.oneMoreExperiment boolIdScheme (fun _ => $ᵗ (Fin 2 → Bool)) 1
        Signature.collisionAttack).succProbability = (2 : ℝ≥0)⁻¹ := by
    rw [Signature.succProbability_collisionAttack_uniform boolIdScheme boolIdScheme_verify_inj]
    have hcorr :
        (Signature.signingCorrectnessExperiment boolIdScheme fun _ => $ᵗ Bool).succProbability =
          1 := by
      simp [Signature.signingCorrectnessExperiment, Experiment.succProbability,
        Game.succProbability, boolIdScheme, ENNReal.toNNReal_ofNat]
    rw [hcorr, mul_one, Fintype.card_bool]
    rfl
  have hred : ProbComp.eval
      (extractedRedemptionWordGame idWordSigScheme (fun _ => 2) uniformBoolWordTargets
        (fun _ => Fin 2) (fun _ => encFinTwo) (fun _ => decFinTwo)
        (fun _ => (Equiv.refl (Fin 2)).toEmbedding) (fun _ => 1) wordCollisionAttack n) =
      ProbComp.eval (Signature.oneMoreExperiment boolIdScheme (fun _ => $ᵗ (Fin 2 → Bool)) 1
        Signature.collisionAttack) := by
    rw [Signature.eval_oneMore_collisionAttack boolIdScheme boolIdScheme_verify_inj]
    simp only [extractedRedemptionWordGame, extractedRedemptionExperiment, uniformBoolWordTargets,
      WordSignatureScheme.toScheme_keyGen, WordSignatureScheme.toScheme_sign,
      idWordSigScheme, boolIdScheme, WordRedemptionAdversary.toTyped,
      ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
      PMF.pure_bind, PMF.bind_map, Function.comp_def]
    congr 1
    funext f
    have hdec : (wordTargetsInputDecoder.decode
        (encWordTargetsInput ([], List.ofFn fun i => [f i]))).2 = [[f 0], [f 1]] := by
      rw [wordTargetsInputDecoder.decode_enc]
      rfl
    dsimp only [wordCollisionAttack]
    rw [ProbOracleComp.runLog, ProbOracleComp.runState,
      ProbOracleComp.eval_run_interpret_eq_runWith, hdec]
    simp [ProbOracleComp.simulate, OracleComp.substitute_eq_interpret,
      ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
      ProbComp.eval_pure, WordSignatureScheme.toScheme_verify,
      extractedRedemptionAccept, Token.valid, decFinTwo]
    cases f 0 <;> cases f 1 <;> simp
  have heq_succ : Game.succProbability (ProbComp.eval
      (extractedRedemptionWordGame idWordSigScheme (fun _ => 2) uniformBoolWordTargets
        (fun _ => Fin 2) (fun _ => encFinTwo) (fun _ => decFinTwo)
        (fun _ => (Equiv.refl (Fin 2)).toEmbedding) (fun _ => 1) wordCollisionAttack n)) =
      (2 : ℝ≥0)⁻¹ := by
    rw [hred]
    exact hunif
  exact ⟨heq_succ, heq_succ.trans hunif.symm⟩

/-- Honest single-query adversary returning only `1` valid token (`< budget + 1 = 2`). -/
private def honestSingleAttack : WordRedemptionAdversary :=
  fun _ input => do
    let ys := (wordTargetsInputDecoder.decode input).2
    let y0 := ys.getD 0 []
    let sig ← List.take (y0.length + 1) <$> ProbOracleComp.query ((), y0)
    return [⟨⟨[false], ()⟩, sig⟩]

-- Honest `1`-token run gives `extractedRedemptionWordGame = pure false` (`succProbability = 0`).
example (n : ℕ) :
    Game.succProbability (ProbComp.eval
      (extractedRedemptionWordGame idWordSigScheme (fun _ => 2)
        (fun _ _ => pure fun _ => [false]) (fun _ => Fin 2) (fun _ => encFinTwo)
        (fun _ => decFinTwo) (fun _ => (Equiv.refl (Fin 2)).toEmbedding) (fun _ => 1)
        honestSingleAttack n)) = 0 := by
  have hdec : (wordTargetsInputDecoder.decode
      (encWordTargetsInput ([], List.ofFn fun _ : Fin 2 => ([false] : List Bool)))).2 =
      [[false], [false]] := by
    rw [wordTargetsInputDecoder.decode_enc]
    rfl
  simp only [extractedRedemptionWordGame, extractedRedemptionExperiment, idWordSigScheme,
    WordSignatureScheme.toScheme_keyGen, WordSignatureScheme.toScheme_sign,
    WordRedemptionAdversary.toTyped, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind,
    ProbOracleComp.runLog, ProbOracleComp.runState]
  rw [ProbOracleComp.eval_run_interpret_eq_runWith]
  dsimp only [honestSingleAttack]
  rw [hdec]
  simp [ProbOracleComp.simulate, OracleComp.substitute_eq_interpret,
    ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
    extractedRedemptionAccept, Game.succProbability]

-- Overlong adversary (`> budget + 1` tokens): `wordOverlongAttack` returns `3` distinct-slot
-- tokens (the 3rd `[false, true]` has a forged empty signature), failing
-- `extractedRedemptionWordGame` (`0`), while `reduceRedemptionsWord` truncates to `budget + 1 = 2`
-- tokens and succeeds in `oneMoreWordGame` (`1`).
private def wordOverlongAttack : WordRedemptionAdversary :=
  fun _ input => do
    let ys := (wordTargetsInputDecoder.decode input).2
    let y0 := ys.getD 0 []
    let sig ← List.take (y0.length + 1) <$> ProbOracleComp.query ((), y0)
    return [⟨⟨[false, false], ()⟩, sig⟩, ⟨⟨[true, false], ()⟩, sig⟩, ⟨⟨[false, true], ()⟩, []⟩]

private theorem replicate_take_eq_replicate_false (n : ℕ) :
    ([false, false] ++ List.replicate (n + 1) false).take (n + 1) =
      List.replicate (n + 1) false := by
  have h : [false, false] ++ List.replicate (n + 1) false = List.replicate (n + 3) false := by
    rfl
  rw [h, List.take_replicate]
  simp

private theorem take_true_false_pad (n : ℕ) :
    ([true, false] ++ List.replicate (n + 1) false).take (n + 1) =
      true :: List.replicate n false := by
  have h : [true, false] ++ List.replicate (n + 1) false =
      true :: List.replicate (n + 2) false := by
    rfl
  rw [h, List.take_succ_cons, List.take_replicate]
  simp

example (n : ℕ) :
    Game.succProbability (ProbComp.eval
      (extractedRedemptionWordGame idWordSigScheme (fun n => 2 ^ (n + 1))
        (fun _ _ => pure fun _ => [false]) (fun n => FixedBits (n + 1))
        (fun n => encFixedBits (n + 1)) (fun n => decFixedBits (n + 1)) slotFixedBits
        (fun _ => 1) wordOverlongAttack n)) = 0 ∧
    Game.succProbability (ProbComp.eval
      (oneMoreWordGame idWordSigScheme (fun n => 2 ^ (n + 1))
        (fun _ _ => pure fun _ => [false]) (fun _ => 1)
        (reduceRedemptionsWord (fun _ => 1) slotWordFixedBits wordOverlongAttack) n)) = 1 := by
  have hy0 : ((wordTargetsInputDecoder.decode (encWordTargetsInput
      ([], List.ofFn fun _ : Fin (2 ^ (n + 1)) => ([false] : List Bool)))).2).getD 0 [] =
      [false] := by
    rw [wordTargetsInputDecoder.decode_enc]
    simp [List.ofFn_const]
  have hslot0 : slotWordFixedBits n [false, false] = 0 := by
    rw [slotWordFixedBits, replicate_take_eq_replicate_false]
    exact Nat.foldr_bit_replicate_false _
  have hslot1 : slotWordFixedBits n [true, false] = 1 := by
    rw [slotWordFixedBits, take_true_false_pad, ofBits, List.foldr_cons,
      Nat.foldr_bit_replicate_false]
    rfl
  have hbound0 : (0 : ℕ) < 2 ^ (n + 1) := by positivity
  have hbound1 : (1 : ℕ) < 2 ^ (n + 1) := by
    have : 2 ≤ 2 ^ (n + 1) := Nat.le_self_pow (Nat.succ_ne_zero n) 2
    omega
  constructor
  · simp only [extractedRedemptionWordGame, extractedRedemptionExperiment,
      WordSignatureScheme.toScheme_keyGen, WordSignatureScheme.toScheme_sign,
      idWordSigScheme, WordRedemptionAdversary.toTyped,
      ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind,
      ProbOracleComp.runLog, ProbOracleComp.runState]
    rw [ProbOracleComp.eval_run_interpret_eq_runWith]
    dsimp only [wordOverlongAttack]
    rw [hy0]
    simp [ProbOracleComp.simulate, OracleComp.substitute_eq_interpret,
      ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
      extractedRedemptionAccept, Token.valid, Game.succProbability]
  · simp only [oneMoreWordGame, Signature.oneMoreExperiment,
      WordSignatureScheme.toScheme_keyGen, WordSignatureScheme.toScheme_sign,
      idWordSigScheme, WordOneMoreAdversary.toTyped,
      reduceRedemptionsWord, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind,
      ProbOracleComp.runLog, ProbOracleComp.runState]
    rw [ProbOracleComp.eval_run_interpret_eq_runWith]
    dsimp only [wordOverlongAttack]
    rw [hy0]
    simp only [map_pure, ProbComp.eval_pure, Nat.reduceAdd, List.map_take, List.length_cons,
      List.length_nil, zero_add, bind_pure_comp, Functor.map_map, List.map_cons, List.map_nil,
      List.take_succ_cons, List.take_zero, ProbOracleComp.simulate_map,
      ProbOracleComp.simulate_query, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
      List.nil_append, PMF.pure_map, Prod.map_apply, List.take_nil, id_eq, PMF.pure_bind,
      hslot0, hslot1]
    have hdecClaim : wordClaimListDecoder (2 ^ (n + 1))
        (encWordClaimList [(0, [false]), (1, [false])]) =
        some [⟨⟨0, hbound0⟩, [false]⟩, ⟨⟨1, hbound1⟩, [false]⟩] := by
      let xs : List (Fin (2 ^ (n + 1)) × List Bool) :=
        [(⟨0, hbound0⟩, [false]), (⟨1, hbound1⟩, [false])]
      exact wordClaimListDecoder_encWordClaimList_map (2 ^ (n + 1)) xs Prod.fst Prod.snd
    change Game.succProbability (PMF.pure (Signature.oneMoreAccept _ [] _ 1
      ((wordClaimListDecoder (2 ^ (n + 1))
        (encWordClaimList [(0, [false]), (1, [false])])).getD []) [([false], [false])])) = 1
    rw [hdecClaim]
    simp [Signature.oneMoreAccept, Game.succProbability]

/-! ### 5. Concrete non-vacuous instantiations of asymptotic and query-bounded security -/

private theorem budget_plus_one_polyTime :
    ComputableInPolyTime (fun n : ℕ => (n + 1) + 1) encUnary encUnary := by
  have h1 : ComputableInPolyTime (fun n : ℕ => n + 1) encUnary encUnary :=
    ComputableInPolyTime.id'.unary_add' (ComputableInPolyTime.const 1)
  exact h1.unary_add' (ComputableInPolyTime.const 1)

-- Concrete instantiation of `negligible_extractedRedemptionWordGame` and
-- `indistinguishable_extractedRedemptionWordGame` on exponential `FixedBits (n + 1)` messages,
-- `N n = 2 ^ (n + 1)` targets, `budget n = n + 1`, and certified `wordCollisionAttack`.
example (S : WordSignatureScheme)
    (targets : ∀ n, List Bool → ProbComp (Fin (2 ^ (n + 1)) → List Bool))
    (hOneMore : Game.Indistinguishable
      (fun B n =>
        ProbComp.eval (oneMoreWordGame S (fun n => 2 ^ (n + 1)) targets (fun n => n + 1) B n))
      (fun _ _ => PMF.pure false) (IsOraclePPT encBits)) :
    Negligible (fun n => Game.succProbability (ProbComp.eval
      (extractedRedemptionWordGame S (fun n => 2 ^ (n + 1)) targets (fun n => FixedBits (n + 1))
        (fun n => encFixedBits (n + 1)) (fun n => decFixedBits (n + 1)) slotFixedBits
        (fun n => n + 1) wordCollisionAttack n))) ∧
    Game.Indistinguishable
      (fun A n => ProbComp.eval
        (extractedRedemptionWordGame S (fun n => 2 ^ (n + 1)) targets (fun n => FixedBits (n + 1))
          (fun n => encFixedBits (n + 1)) (fun n => decFixedBits (n + 1)) slotFixedBits
          (fun n => n + 1) A n))
      (fun _ _ => PMF.pure false)
      (IsOraclePPT (encRedemptionTokenList encBits)) :=
  ⟨negligible_extractedRedemptionWordGame S (fun n => 2 ^ (n + 1)) targets
      (fun n => FixedBits (n + 1)) (fun n => encFixedBits (n + 1)) (fun n => decFixedBits (n + 1))
      slotFixedBits (fun n => n + 1) slotWordFixedBits hOneMore budget_plus_one_polyTime
      computableInPolyTime_slotWordFixedBits slotWordFixedBits_eq wordCollisionAttack
      isOraclePPT_wordCollisionAttack,
   indistinguishable_extractedRedemptionWordGame S (fun n => 2 ^ (n + 1)) targets
      (fun n => FixedBits (n + 1)) (fun n => encFixedBits (n + 1)) (fun n => decFixedBits (n + 1))
      slotFixedBits (fun n => n + 1) slotWordFixedBits hOneMore budget_plus_one_polyTime
      computableInPolyTime_slotWordFixedBits slotWordFixedBits_eq⟩

-- Concrete instantiation of `succWithin_extractedRedemptionWordGame_withinQueries` applied to
-- the `1`-query `wordCollisionAttack`.
example (S : WordSignatureScheme)
    (targets : ∀ n, List Bool → ProbComp (Fin (2 ^ (n + 1)) → List Bool))
    {ε : ℕ → ℕ → ℝ≥0}
    (hOneMore : Game.SuccWithin
      (fun B n => ProbComp.eval (oneMoreWordGame S (fun n => 2 ^ (n + 1)) targets (fun _ => 1) B n))
      WithinWordQueries ε) (n : ℕ) :
    Game.succProbability (ProbComp.eval
      (extractedRedemptionWordGame S (fun n => 2 ^ (n + 1)) targets (fun n => FixedBits (n + 1))
        (fun n => encFixedBits (n + 1)) (fun n => decFixedBits (n + 1)) slotFixedBits
        (fun _ => 1) wordCollisionAttack n)) ≤ ε n 1 :=
  succWithin_extractedRedemptionWordGame_withinQueries S (fun n => 2 ^ (n + 1)) targets
    (fun n => FixedBits (n + 1)) (fun n => encFixedBits (n + 1)) (fun n => decFixedBits (n + 1))
    slotFixedBits (fun _ => 1) slotWordFixedBits slotWordFixedBits_eq hOneMore n 1
    wordCollisionAttack (withinWordQueries_wordCollisionAttack n)

end CslibFrontierTests.Crypto.AnonymousTokenRandomTargetPolyTime
