/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.Encryption.LoRCPA.FromSingle
import CslibFrontier.Crypto.Computational.LWE.Regev.Security
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT
import Mathlib.Data.Set.Finite.List

/-!
# Tests for Left-or-Right CPA from Single-Challenge Semantic Security

Smoke tests for `Cslib.Crypto.Encryption.LoRCPA.FromSingle`: hybrid endpoint identities, concrete
`dyadicSize (Q n)` and uniform `Q n` advantage equalities, strict-PPT certificates, positive
asymptotic `INDCPAOf`/`WordLoRINDCPA`/`LoRINDCPA` clients (including Regev under `DecisionLWE`),
`hctLen` witness on infinite word messages, and nonvacuity via a plaintext-leaking scheme.
-/

set_option linter.privateModule false

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
  start := (ComputableInPolyTime.const ([] : List Bool)).isPPTOn
  query := (ComputableInPolyTime.of_tidy (by polytime)).isPPTOn
  guess := (ComputableInPolyTime.of_tidy (by polytime)).isPPTOn
  state_growth := ⟨fun n => n, by fun_prop, fun _ _ _ r hr => by
    simp only [constWordAdv, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hr
    subst hr; simp [ChoiceOut.state]⟩

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

private def leakBitEncrypt (_ : ℕ) (_ : List Bool) (m : Bool) : ProbComp (List Bool) := pure [m]

/-- Asks `(false, true)` twice and outputs `true` iff both replies are `[true]`. -/
private noncomputable def bothAdv : LoRAdversary where
  start _ _ := pure []
  query _ _ _ := pure ((false, true), [])
  guess _ _ tr := pure (tr == [[true], [true]])

private theorem advantage_bothAdv (n : ℕ) :
    Game.advantage
      (ProbComp.eval (lorGame constKeyGen leakBitEncrypt (fun _ => 2) bothAdv false n))
      (ProbComp.eval (lorGame constKeyGen leakBitEncrypt (fun _ => 2) bothAdv true n)) = 1 := by
  simp [lorGameOn, lorDistinguisherOn, lorRunOn, lorStepOn, OracleComp.iterate_succ,
    OracleComp.iterate_zero, constKeyGen, leakBitEncrypt, bothAdv, Game.advantage,
    Game.succProbability]

/-- `advantage_lorGameOn_eq` where neither side vanishes: against the bit-leaking scheme with
`Q n = 2`, the certified `lorToSingle` has advantage exactly `1 / dyadicSize 2 = 1 / 4`. -/
theorem leak_exact_eq (n : ℕ) :
    Game.advantage
      (ProbComp.eval (game constKeyGen leakBitEncrypt
        (lorToSingle (fun _ _ _ _ => true) leakBitEncrypt (fun _ => 2) bothAdv) false n))
      (ProbComp.eval (game constKeyGen leakBitEncrypt
        (lorToSingle (fun _ _ _ _ => true) leakBitEncrypt (fun _ => 2) bothAdv) true n)) =
      1 / 4 := by
  have h := advantage_lorGameOn_eq (fun _ _ _ _ => true) constKeyGen leakBitEncrypt (fun _ => 2)
    bothAdv n
  have h4 : dyadicSize 2 = 4 := by decide
  rw [advantage_bothAdv, h4] at h
  rw [eq_div_iff (by norm_num), mul_comm]
  exact_mod_cast h.symm

/-- `advantage_lorGameOn_eq_uniform` on the same instance: the uniform mixture of `lorToSingleAt`
over `Fin 2`, the book's `B`, has advantage `1 / 2`, the printed `1 = Q · (1 / 2)`. -/
theorem leak_exact_eq_uniform (n : ℕ) :
    Game.advantage
      ((PMF.uniformOfFintype (Fin 2)).bind fun i =>
        ProbComp.eval (game constKeyGen leakBitEncrypt
          (lorToSingleAt (fun _ _ _ _ => true) leakBitEncrypt (fun _ => 2) bothAdv i.val) false n))
      ((PMF.uniformOfFintype (Fin 2)).bind fun i =>
        ProbComp.eval (game constKeyGen leakBitEncrypt
          (lorToSingleAt (fun _ _ _ _ => true) leakBitEncrypt (fun _ => 2) bothAdv i.val) true n)) =
      1 / 2 := by
  have h := advantage_lorGameOn_eq_uniform (fun _ _ _ _ => true) constKeyGen leakBitEncrypt
    (fun _ => 2) bothAdv n
  rw [advantage_bothAdv] at h
  rw [eq_div_iff (by norm_num), mul_comm]
  exact_mod_cast h.symm

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
    (ComputableInPolyTime.const ([false] : List Bool)).isPPTOn
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
    (ComputableInPolyTime.const ([false] : List Bool)).isPPTOn
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
    ((ComputableInPolyTime.const ([false] : List Bool)).isPPTOn)
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
    { start := (ComputableInPolyTime.const ([] : List Bool)).isPPTOn
      query := (ComputableInPolyTime.const
        ((([false], [true]), []) : ChoiceOut (List Bool))).isPPTOn
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

open Turing.MultiTapeTM.ComputableInPolyTime in
/-- Real-scheme client: `INDCPA.lorINDCPA` turns Regev `INDCPA` under `DecisionLWE` into
`Regev.LoRINDCPA`. -/
theorem regev_lorINDCPA_of_decisionLWE {n m w η Q : ℕ → ℕ}
    (hn : ComputableInPolyTime n encUnary encUnary)
    (hm : ComputableInPolyTime m encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hmargin : ∀ᶠ security in Filter.atTop,
      (n security + 1) * w security + 2 * security ≤ m security)
    (hLWE : DecisionLWE n m w (fun k => LWE.noiseLaw (w k) (η k))) :
    Regev.LoRINDCPA n m w η Q := by
  have hlen : Cslib.PolynomiallyBounded (fun k => (n k + 1) * w k) := by
    have h : ComputableInPolyTime (fun k => (n k + 1) * w k) encUnary encUnary := by fun_prop
    exact h.polynomiallyBounded
  have henc : IsPPTOn (encKeyedInput encBool) encBits
      (fun ⟨security, pk, msg⟩ =>
        Regev.encryptSerialized (n security) (m security) (w security) pk msg) :=
    Regev.isPPTOn_encryptSerialized (hn.comp (by fun_prop)) (hm.comp (by fun_prop))
      (hw.comp (by fun_prop)) (by fun_prop) (by fun_prop)
  exact (Regev.indCPA_of_decisionLWE hn hm hw hmargin hLWE).lorINDCPA henc hlen
    (fun _ _ _ _ hc => le_of_eq (Regev.length_of_mem_support_encryptSerialized hc)) hQ

/-- On `Msg = List Bool`, no scheme that decrypts every message satisfies `hctLen`. -/
theorem no_correct_word_scheme_with_hctLen
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (decrypt : List Bool → List Bool → List Bool) (ctBound : ℕ → ℕ) (n : ℕ) (pk sk : List Bool)
    (hctLen : ∀ n k msg c, c ∈ (ProbComp.eval (encrypt n k msg)).support → c.length ≤ ctBound n)
    (hcorrect : ∀ msg c, c ∈ (ProbComp.eval (encrypt n pk msg)).support → decrypt sk c = msg) :
    False := by
  classical
  let f : List Bool → List Bool :=
    fun msg => (PMF.support_nonempty (ProbComp.eval (encrypt n pk msg))).some
  have hf (msg : List Bool) : f msg ∈ (ProbComp.eval (encrypt n pk msg)).support :=
    (PMF.support_nonempty _).some_mem
  have hinj : Function.Injective f := fun a b h => by
    rw [← hcorrect a (f a) (hf a), h, hcorrect b (f b) (hf b)]
  have hfin : (Set.range f).Finite :=
    (List.finite_length_le Bool (ctBound n)).subset (by
      rintro _ ⟨msg, rfl⟩
      exact hctLen n pk msg _ (hf msg))
  exact Set.infinite_range_of_injective hinj hfin

end LoRCPAFromSingleTests
