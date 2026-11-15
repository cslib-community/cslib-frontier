/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.Encryption.LoRCPA.FromSingle
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for Left-or-Right CPA from Single-Challenge Semantic Security

Smoke tests for `Cslib.Crypto.Encryption.LoRCPA.FromSingle`: saved-state framing, hybrid endpoint
identities, concrete `dyadicSize (Q n)` and uniform `Q n` advantage equalities, strict-PPT
certificates, positive asymptotic `INDCPAOf`/`WordLoRINDCPA`/`LoRINDCPA` clients, and nonvacuity
via a plaintext-leaking scheme.
-/

namespace LoRCPAFromSingleTests

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Encryption Turing.MultiTapeTM

private def constKeyGen (_ : ℕ) : ProbComp (List Bool × List Bool) := pure ([], [])
private def constBitEncrypt (_ : ℕ) (_ : List Bool) (_ : Bool) : ProbComp (List Bool) :=
  pure [false]
private def constWordEncrypt (_ : ℕ) (_ _ : List Bool) : ProbComp (List Bool) := pure [false]

private noncomputable def constWordAdv : WordLoRAdversary where
  start _ _ := pure []
  query _ st tr := pure ((tr.headD [], [false]), st)
  guess _ _ tr := pure (tr.length == 3)

private lemma isPPT_constWordAdv : LoRAdversaryOf.IsPPT encBits constWordAdv where
  start := (ComputableInPolyTime.const ([] : List Bool)).tidy.isPPTOn
  query := (ComputableInPolyTime.of_tidy (by polytime)).isPPTOn
  guess := (ComputableInPolyTime.of_tidy (by polytime)).isPPTOn
  state_growth := ⟨fun n => n, by fun_prop, fun _ _ _ r hr => by
    simp only [constWordAdv, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hr
    subst hr; simp [ChoiceOut.state]⟩

/-- `encLoRToSingleState` matches the five-field nested `encPair` framing tuple. -/
example (s : LoRToSingleState) :
    encLoRToSingleState s =
      encPair encBool (encPair encBits (encPair encUnary (encPair encBits (encList encBits))))
        (s.active, s.pk, s.split, s.stateA, s.transcript) := rfl

/-- Hybrid endpoint identities match left (`bit = false`) at `0` and right (`bit = true`) at
`split ≥ Q n`. -/
theorem constHybridEndpoints (n : ℕ) :
    ProbComp.eval (lorHybridGameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
        constKeyGen constWordEncrypt (fun _ => 3) constWordAdv 0 n) =
      ProbComp.eval (lorGameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
        constKeyGen constWordEncrypt (fun _ => 3) constWordAdv false n) ∧
    ProbComp.eval (lorHybridGameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
        constKeyGen constWordEncrypt (fun _ => 3) constWordAdv 3 n) =
      ProbComp.eval (lorGameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
        constKeyGen constWordEncrypt (fun _ => 3) constWordAdv true n) :=
  ⟨eval_lorHybridGameOn_zero _ _ _ _ _ n,
   eval_lorHybridGameOn_of_le _ _ _ _ _ (Nat.le_refl 3)⟩

/-- Concrete exact identity with strict-PPT `dyadicSize (Q n)` factor (`Q n = 3`). -/
theorem const_exact_eq (n : ℕ) :
    Game.advantage
      (ProbComp.eval (lorGameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
        constKeyGen constWordEncrypt (fun _ => 3) constWordAdv false n))
      (ProbComp.eval (lorGameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
        constKeyGen constWordEncrypt (fun _ => 3) constWordAdv true n)) =
      dyadicSize 3 *
        Game.advantage
          (ProbComp.eval (gameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length) constKeyGen
            constWordEncrypt (lorToSingle (fun _ _ m₀ m₁ => m₀.length == m₁.length)
              constWordEncrypt (fun _ => 3) constWordAdv) false n))
          (ProbComp.eval (gameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length) constKeyGen
            constWordEncrypt (lorToSingle (fun _ _ m₀ m₁ => m₀.length == m₁.length)
              constWordEncrypt (fun _ => 3) constWordAdv) true n)) :=
  advantage_lorGameOn_eq _ _ _ _ _ n

/-- Concrete literal-`Q` identity (`CPAadv[A, E] = Q · SSadv[B, E]`) when `Q n = 3` is nonzero. -/
theorem const_exact_eq_uniform (n : ℕ) :
    Game.advantage
      (ProbComp.eval (lorGameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
        constKeyGen constWordEncrypt (fun _ => 3) constWordAdv false n))
      (ProbComp.eval (lorGameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
        constKeyGen constWordEncrypt (fun _ => 3) constWordAdv true n)) =
      3 *
        Game.advantage
          ((PMF.uniformOfFintype (Fin 3)).bind fun i =>
            ProbComp.eval (gameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length) constKeyGen
              constWordEncrypt (lorToSingleAt (fun _ _ m₀ m₁ => m₀.length == m₁.length)
                constWordEncrypt (fun _ => 3) constWordAdv i.val) false n))
          ((PMF.uniformOfFintype (Fin 3)).bind fun i =>
            ProbComp.eval (gameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length) constKeyGen
              constWordEncrypt (lorToSingleAt (fun _ _ m₀ m₁ => m₀.length == m₁.length)
                constWordEncrypt (fun _ => 3) constWordAdv i.val) true n)) :=
  advantage_lorGameOn_eq_uniform _ _ _ (fun _ => 3) _ n

/-- `isPPT_lorToSingleAt` and `isPPT_lorToSingle` certify PPT on `constWordAdv` with `Q n = 3`. -/
theorem isPPT_const_lorToSingle :
    (lorToSingleAt (fun _ _ m₀ m₁ => m₀.length == m₁.length)
        constWordEncrypt (fun _ => 3) constWordAdv 1).IsPPT encBits ∧
      (lorToSingle (fun _ _ m₀ m₁ => m₀.length == m₁.length)
        constWordEncrypt (fun _ => 3) constWordAdv).IsPPT encBits := by
  have hvalid : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool × List Bool =>
      p.2.2.1.length == p.2.2.2.length) (encChallengePairInput encBits) encBool :=
    ComputableInPolyTime.of_tidy (by polytime)
  have henc : IsPPTOn (encKeyedInput encBits) encBits (fun _ => pure [false]) :=
    (ComputableInPolyTime.const ([false] : List Bool)).tidy.isPPTOn
  have hctB : Cslib.PolynomiallyBounded (fun _ => 1) := by fun_prop
  have hctL :
      ∀ n k msg c, c ∈ (ProbComp.eval (constWordEncrypt n k msg)).support → c.length ≤ 1 :=
    fun _ _ _ c hc => by
      simp only [constWordEncrypt, ProbComp.eval_pure, PMF.support_pure,
        Set.mem_singleton_iff] at hc
      subst hc; simp
  have hQ : ComputableInPolyTime (fun _ : ℕ => 3) encUnary encUnary :=
    ComputableInPolyTime.const 3
  exact ⟨isPPT_lorToSingleAt hvalid henc hctB hctL hQ isPPT_constWordAdv 1,
    isPPT_lorToSingle hvalid henc hctB hctL hQ isPPT_constWordAdv⟩

/-- Positive asymptotic client: constant bit-word encryption satisfies `WordLoRINDCPA` and
unrestricted `LoRINDCPAOf`. -/
theorem const_wordLoRINDCPA :
    WordLoRINDCPA constKeyGen constWordEncrypt (fun _ => 3) ∧
      LoRINDCPAOf encBits constKeyGen constWordEncrypt (fun _ => 3) := by
  have hssW : WordINDCPA constKeyGen constWordEncrypt := fun adv _ =>
    negligible_of_le negligible_zero fun n => by
      have hconst (b : Bool) : ProbComp.eval (gameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
          constKeyGen constWordEncrypt adv b n) = ProbComp.eval (do
          let keys ← constKeyGen n
          let c ← adv.choose n keys.1
          if c.1.1.length == c.1.2.length then adv.guess n c.2 [false]
          else pure false) := by
        simp [gameOn, constWordEncrypt]
      simp [Game.advantage, hconst false, hconst true]
  have hssU : INDCPAOf encBits constKeyGen constWordEncrypt := fun adv _ =>
    negligible_of_le negligible_zero fun n => by
      have hconst (b : Bool) : ProbComp.eval (gameOn (fun _ _ _ _ => true)
          constKeyGen constWordEncrypt adv b n) = ProbComp.eval (do
          let keys ← constKeyGen n
          let c ← adv.choose n keys.1
          adv.guess n c.2 [false]) := by
        simp [gameOn, constWordEncrypt]
      simp [Game.advantage, hconst false, hconst true]
  have henc : IsPPTOn (encKeyedInput encBits) encBits (fun _ => pure [false]) :=
    (ComputableInPolyTime.const ([false] : List Bool)).tidy.isPPTOn
  have hctB : Cslib.PolynomiallyBounded (fun _ => 1) := by fun_prop
  have hctL :
      ∀ n k msg c, c ∈ (ProbComp.eval (constWordEncrypt n k msg)).support → c.length ≤ 1 :=
    fun _ _ _ c hc => by
      simp only [constWordEncrypt, ProbComp.eval_pure, PMF.support_pure,
        Set.mem_singleton_iff] at hc
      subst hc; simp
  exact ⟨hssW.wordLoRINDCPA (ctBound := fun _ => 1) henc hctB hctL (ComputableInPolyTime.const 3),
    hssU.lorINDCPAOf (ctBound := fun _ => 1) henc hctB hctL (ComputableInPolyTime.const 3)⟩

/-- Positive asymptotic client: constant single-bit encryption satisfies `LoRINDCPA`. -/
theorem const_lorINDCPA : LoRINDCPA constKeyGen constBitEncrypt (fun _ => 3) := by
  have hss : INDCPA constKeyGen constBitEncrypt := fun adv _ =>
    negligible_of_le negligible_zero fun n => by
      have hconst (b : Bool) : ProbComp.eval (gameOn (fun _ _ _ _ => true)
          constKeyGen constBitEncrypt adv b n) = ProbComp.eval (do
          let keys ← constKeyGen n
          let c ← adv.choose n keys.1
          adv.guess n c.2 [false]) := by
        simp [gameOn, constBitEncrypt]
      simp [Game.advantage, hconst false, hconst true]
  exact hss.lorINDCPA (ctBound := fun _ => 1)
    ((ComputableInPolyTime.const ([false] : List Bool)).tidy.isPPTOn)
    (by fun_prop)
    (fun _ _ _ c hc => by
      simp only [constBitEncrypt, ProbComp.eval_pure, PMF.support_pure,
        Set.mem_singleton_iff] at hc
      subst hc; simp)
    (ComputableInPolyTime.const 3)

/-- Nonvacuity: plaintext-leaking bit-word encryption fails `WordLoRINDCPA` via a 1-query adversary
distinguishing `[false]` from `[true]`. -/
theorem leak_not_wordLoRINDCPA :
    ¬ WordLoRINDCPA constKeyGen (fun _ _ m => pure m) (fun _ => 1) := by
  let adv : WordLoRAdversary :=
    { start := fun _ _ => pure []
      query := fun _ _ _ => pure (([false], [true]), [])
      guess := fun _ _ tr => pure (tr == [[true]]) }
  have hadv : LoRAdversaryOf.IsPPT encBits adv :=
    { start := (ComputableInPolyTime.const ([] : List Bool)).tidy.isPPTOn
      query := (ComputableInPolyTime.const
        ((([false], [true]), []) : ChoiceOut (List Bool))).tidy.isPPTOn
      guess := (ComputableInPolyTime.of_tidy (by polytime)).isPPTOn
      state_growth := ⟨fun n => n, by fun_prop, fun _ _ _ r hr => by
        simp only [adv, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hr
        subst hr; simp [ChoiceOut.state]⟩ }
  intro hsec
  have hneg := hsec adv hadv
  have hadv1 : ∀ n, Game.advantage
      (ProbComp.eval (lorGameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
        constKeyGen (fun _ _ m => pure m) (fun _ => 1) adv false n))
      (ProbComp.eval (lorGameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
        constKeyGen (fun _ _ m => pure m) (fun _ => 1) adv true n)) = 1 := fun n => by
    simp [lorGameOn, lorDistinguisherOn, lorRunOn, lorStepOn, OracleComp.iterate_succ,
      OracleComp.iterate_zero, constKeyGen, adv, Game.advantage, Game.succProbability]
  have hzero : Filter.Tendsto (fun _ : ℕ => (1 : NNReal)) Filter.atTop (nhds 0) := by
    have h := hneg 0
    simp only [hadv1, pow_zero, one_mul] at h
    exact h
  exact one_ne_zero (tendsto_const_nhds_iff.mp hzero)

end LoRCPAFromSingleTests
