/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.Encryption.Bitwise
import CslibFrontier.Crypto.Computational.Encryption.LoRCPA.FromSingle
import CslibFrontier.Crypto.Computational.GoldwasserMicali
import CslibFrontier.Crypto.Computational.LWE.Regev.Security
import CslibFrontier.Crypto.Computational.Paillier.Security
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Tests for Left-or-Right CPA from Single-Challenge Semantic Security

Smoke tests and boundary witnesses for `Cslib.Crypto.Encryption.LoRCPA` and
`Cslib.Crypto.Encryption.LoRCPA.FromSingle`: hybrid endpoint identities, concrete
`dyadicSize (Q n)` and uniform `Q n` advantage equalities, strict-PPT certificates, boundary
witness refuting `LoRAdversaryOf.IsPPT` for an adaptive transcript-doubling adversary, positive
asymptotic `INDCPAOn`/`INDCPAOf`/`LoRINDCPA`/`WordLoRINDCPA` clients on genuinely correct schemes
(Regev, bitwise Regev under `DecisionLWE`, Goldwasser–Micali `encrypt` and `encryptWord` under
`QuadraticResiduosityHard`, and Paillier under `DCR`), and nonvacuity via a plaintext-leaking
scheme.
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
  query _ st tr := pure (([(tr.headD []).headD false], [false]), st)
  guess _ _ tr := pure (tr.length == 3)

private lemma isPPT_constWordAdv : LoRAdversaryOf.IsPPT encBits constWordAdv where
  start := (ComputableInPolyTime.const ([] : List Bool)).isPPTOn
  query := by
    apply ComputableInPolyTime.isPPTOn
    have htr : ComputableInPolyTime
        (fun x : ℕ × List Bool × List (List Bool) => x.2.2.headD [])
        encLoRStageInput encBits :=
      (ComputableInPolyTime.headD (encA := encBits) (encL := encList encBits) []).comp
        (by fun_prop)
    have hbit : ComputableInPolyTime
        (fun x : ℕ × List Bool × List (List Bool) => (x.2.2.headD []).headD false)
        encLoRStageInput encBool :=
      (ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false).comp htr
    have hmsg0 : ComputableInPolyTime
        (fun x : ℕ × List Bool × List (List Bool) => [(x.2.2.headD []).headD false])
        encLoRStageInput encBits :=
      (ComputableInPolyTime.of_finite (encIn := encBool) (encOut := encBits) fun b => [b]).comp hbit
    exact (hmsg0.prod (ComputableInPolyTime.const [false])).prod (by fun_prop)
  guess := by
    apply ComputableInPolyTime.isPPTOn
    polytime
  state_growth := ⟨fun n => n, by fun_prop, fun _ _ _ r hr => by
    simp only [constWordAdv, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hr
    subst hr; simp [ChoiceOut.state]⟩
  msg_length_le := ⟨4, 0, fun _ _ _ r hr => by
    simp only [constWordAdv, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hr
    subst hr
    simp [ChoiceOut.msgs, encPair_apply, encBits_apply]⟩

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
    by polytime
  have henc : IsPPTOn (encKeyedInput encBits) encBits (fun _ => pure [false]) :=
    (ComputableInPolyTime.const ([false] : List Bool)).isPPTOn
  have hQ : ComputableInPolyTime (fun _ : ℕ => 3) encUnary encUnary :=
    ComputableInPolyTime.const 3
  exact ⟨isPPT_lorToSingleAt hvalid henc hQ isPPT_constWordAdv 1,
    isPPT_lorToSingle hvalid henc hQ isPPT_constWordAdv⟩

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
  exact ⟨hssW.wordLoRINDCPA henc (ComputableInPolyTime.const 3),
    hssU.lorINDCPAOf henc (ComputableInPolyTime.const 3)⟩

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
  exact hss.lorINDCPA
    ((ComputableInPolyTime.const ([false] : List Bool)).isPPTOn)
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
      guess := by
        apply ComputableInPolyTime.isPPTOn
        polytime
      state_growth := ⟨fun n => n, by fun_prop, fun _ _ _ r hr => by
        simp only [adv, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hr
        subst hr; simp [ChoiceOut.state]⟩
      msg_length_le := ⟨4, 0, fun _ _ _ r hr => by
        simp only [adv, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hr
        subst hr
        simp [ChoiceOut.msgs, encPair_apply, encBits_apply]⟩ }
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

/-- Boundary witness: an adaptive adversary that doubles the latest transcript ciphertext
`c ++ c` as its next challenge pair satisfies uniform strict-PPT `start`, `query`, `guess` and
zero `state_growth`, yet is rejected by `LoRAdversaryOf.IsPPT.msg_length_le`, blocking adaptive
exponential transcript blowup. -/
private def doublingWordAdv : WordLoRAdversary where
  start _ _ := pure []
  query _ st tr :=
    let m := tr.headD [false] ++ tr.headD [false]
    pure ((m, m), st)
  guess _ _ _ := pure false

theorem doublingWordAdv_stages_and_not_isPPT :
    Probability.IsPPT encBits doublingWordAdv.start ∧
    IsPPTOn encLoRStageInput (encChoiceOut encBits)
      (fun ⟨n, state, transcript⟩ => doublingWordAdv.query n state transcript) ∧
    IsPPTOn encLoRStageInput encBool
      (fun ⟨n, state, transcript⟩ => doublingWordAdv.guess n state transcript) ∧
    (∃ bound : ℕ → ℕ, Cslib.PolynomiallyBounded bound ∧
      ∀ n state transcript choice,
        choice ∈ (ProbComp.eval (doublingWordAdv.query n state transcript)).support →
        (ChoiceOut.state choice).length ≤ state.length + bound n) ∧
    ¬ LoRAdversaryOf.IsPPT encBits doublingWordAdv := by
  refine ⟨(ComputableInPolyTime.const ([] : List Bool)).isPPTOn, ?_,
    (ComputableInPolyTime.const false).isPPTOn, ⟨fun _ => 0, by fun_prop, ?_⟩, ?_⟩
  · apply ComputableInPolyTime.isPPTOn
    have htr : ComputableInPolyTime
        (fun x : ℕ × List Bool × List (List Bool) => x.2.2.headD [false])
        encLoRStageInput encBits :=
      (ComputableInPolyTime.headD (encA := encBits) (encL := encList encBits) [false]).comp
        (by fun_prop)
    have hdbl : ComputableInPolyTime
        (fun x : ℕ × List Bool × List (List Bool) =>
          x.2.2.headD [false] ++ x.2.2.headD [false])
        encLoRStageInput encBits :=
      ComputableInPolyTime.bitsAppend htr htr
    exact (hdbl.prod hdbl).prod (by fun_prop)
  · intro _ st tr choice hchoice
    simp only [doublingWordAdv, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hchoice
    subst hchoice
    simp [ChoiceOut.state]
  · intro hadv
    obtain ⟨cm, dm, hmsg⟩ := hadv.msg_length_le
    let c : List Bool := List.replicate (cm * 2 ^ dm + 1) false
    have hmem : ((c ++ c, c ++ c), ([] : List Bool)) ∈
        (ProbComp.eval (doublingWordAdv.query 0 [] [c])).support := by
      simp [doublingWordAdv]
    have hle := hmsg 0 [] [c] ((c ++ c, c ++ c), []) hmem
    simp only [ChoiceOut.msgs, encPair_apply, encBits_apply, List.length_append, length_frame,
      List.length_nil, List.length_replicate, zero_add, c] at hle
    omega

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
  have henc : IsPPTOn (encKeyedInput encBool) encBits
      (fun ⟨security, pk, msg⟩ =>
        Regev.encryptSerialized (n security) (m security) (w security) pk msg) :=
    Regev.isPPTOn_encryptSerialized (hn.comp (by fun_prop)) (hm.comp (by fun_prop))
      (hw.comp (by fun_prop)) (by fun_prop) (by fun_prop)
  exact (Regev.indCPA_of_decisionLWE hn hm hw hmargin hLWE).lorINDCPA henc hQ

open Turing.MultiTapeTM.ComputableInPolyTime in
/-- Real-scheme bit-word client: `WordINDCPA.wordLoRINDCPA` instantiates directly on
`Encryption.bitwiseEncrypt` of Regev under `DecisionLWE` (a genuinely zero-error correct bit-word
scheme over all of `List Bool`, which was previously excluded by `hctLen`). -/
theorem regev_bitwise_wordLoRINDCPA_of_decisionLWE {n m w η Q : ℕ → ℕ}
    (hn : ComputableInPolyTime n encUnary encUnary)
    (hm : ComputableInPolyTime m encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary)
    (hη : ComputableInPolyTime η encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hmargin : ∀ᶠ security in Filter.atTop,
      (n security + 1) * w security + 2 * security ≤ m security)
    (hLWE : DecisionLWE n m w (fun k => LWE.noiseLaw (w k) (η k))) :
    WordLoRINDCPA
      (fun k => LWE.keyGenSerialized (n k) (m k) (w k) (η k))
      (bitwiseEncrypt (fun k => Regev.encryptSerialized (n k) (m k) (w k))) Q := by
  have hkeyGen : IsPPTOn encUnary (encPair encBits encBits)
      (fun k => LWE.keyGenSerialized (n k) (m k) (w k) (η k)) :=
    LWE.isPPTOn_keyGenSerialized hn hm hw hη
  have hencBit : IsPPTOn (encKeyedInput encBool) encBits
      (fun ⟨security, pk, msg⟩ =>
        Regev.encryptSerialized (n security) (m security) (w security) pk msg) :=
    Regev.isPPTOn_encryptSerialized (hn.comp (by fun_prop)) (hm.comp (by fun_prop))
      (hw.comp (by fun_prop)) (by fun_prop) (by fun_prop)
  have hwordSS : WordINDCPA
      (fun k => LWE.keyGenSerialized (n k) (m k) (w k) (η k))
      (bitwiseEncrypt (fun k => Regev.encryptSerialized (n k) (m k) (w k))) :=
    (Regev.indCPA_of_decisionLWE hn hm hw hmargin hLWE).wordINDCPA_bitwiseEncrypt hkeyGen hencBit
  exact hwordSS.wordLoRINDCPA (isPPTOn_bitwiseEncrypt hencBit) hQ

/-- Real-scheme clients on Goldwasser–Micali (whose ciphertext length depends on `pk.length`, so
both `encrypt` and `encryptWord` previously violated `hctLen`): `INDCPA.lorINDCPA` and
`WordINDCPA.wordLoRINDCPA` apply directly under `QuadraticResiduosityHard`. -/
theorem goldwasserMicali_lorINDCPA_of_qr {gen : ℕ → ProbComp ModulusDesc}
    {sizeBound Q : ℕ → ℕ}
    (hbound : PolynomiallyBounded sizeBound)
    (hblum : ∀ n, ∀ d ∈ (ProbComp.eval (gen n)).support, IsBlumModulus d.p d.q)
    (hsize : ∀ n, ∀ d ∈ (ProbComp.eval (gen n)).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (hupper : ∀ n, ∀ d ∈ (ProbComp.eval (gen n)).support,
      d.p.size ≤ sizeBound n ∧ d.q.size ≤ sizeBound n)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hQR : QuadraticResiduosityHard fun n => ProbComp.eval (gen n)) :
    LoRINDCPA (GoldwasserMicali.blumKeyGen gen) GoldwasserMicali.encrypt Q ∧
      WordLoRINDCPA (GoldwasserMicali.blumKeyGen gen) GoldwasserMicali.encryptWord Q :=
  ⟨(GoldwasserMicali.indcpa_blumGoldwasserMicali hblum hsize hQR).lorINDCPA
      GoldwasserMicali.isPPTOn_encrypt hQ,
   (GoldwasserMicali.wordINDCPA_blumGoldwasserMicali hbound hblum hsize hupper hQR).wordLoRINDCPA
      GoldwasserMicali.isPPTOn_encryptWord hQ⟩

/-- Real-scheme client on Paillier (whose ciphertext length also depends on `pk.length`, previously
violating `hctLen`): `INDCPAOn.lorINDCPAOn` applies directly under `DCR`. -/
theorem paillier_lorINDCPAOn_of_dcr {gen : ℕ → ProbComp BalancedModulus.Desc} {Q : ℕ → ℕ}
    (hsize : ∀ n, ∀ d ∈ (ProbComp.eval (gen n)).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hDCR : DCR fun n => ProbComp.eval (gen n)) :
    LoRINDCPAOn Paillier.validMessages encNat (Paillier.keyGen gen) Paillier.encrypt Q := by
  have hvalid : ComputableInPolyTime
      (fun ⟨n, k, m₀, m₁⟩ => Paillier.validMessages n k m₀ m₁)
      (encChallengePairInput encNat) encBool := by
    let E := encChallengePairInput encNat
    have hk : ComputableInPolyTime (fun p : ℕ × List Bool × ℕ × ℕ => ofBits p.2.1) E encNat :=
      ComputableInPolyTime.bitsToNat.comp (by dsimp only [E, encChallengePairInput]; fun_prop)
    have hm0 : ComputableInPolyTime (fun p : ℕ × List Bool × ℕ × ℕ => p.2.2.1) E encNat := by
      dsimp only [E, encChallengePairInput]; fun_prop
    have hm1 : ComputableInPolyTime (fun p : ℕ × List Bool × ℕ × ℕ => p.2.2.2) E encNat := by
      dsimp only [E, encChallengePairInput]; fun_prop
    simpa only [Paillier.validMessages] using
      ComputableInPolyTime.decide_and
        (ComputableInPolyTime.binary_lt' hm0 hk)
        (ComputableInPolyTime.binary_lt' hm1 hk)
  exact (Paillier.DCR.indcpaOn_paillier hsize hDCR).lorINDCPAOn hvalid Paillier.isPPTOn_encrypt hQ

end LoRCPAFromSingleTests
