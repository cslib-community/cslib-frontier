/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.Encryption.Nested
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Probability.PMF.Bind

/-!
# Tests and counterexamples for `n`-way nested encryption

Positive tests verify correctness (`Cipher.nested_correct`), exact zero advantage
(`advantage_otp_nested_eq_zero`), asymptotic `Game.Indistinguishable` semantic security
(`otp_nested_indistinguishable`), module usability of `Cipher.nestedDecrypt` and `revealKeys`,
a nontrivial `Cipher.PreservesValid` instance (`firstBitCipher_preservesValid`), and the vacuous
`n = 0` case (`isEmpty_nestedRequest_zero`). Two counterexamples show why the added hypotheses
cannot be dropped:

1. `tagCipher_no_wrapper`: without `Cipher.PreservesValid`, a correct cipher whose single-key
   one-time advantage is `0` against every adversary can still have `2`-way nested advantage `1`
   against an adversary that withholds the outer key and reads the revealed inner key, so no wrapper
   `B` satisfies the equality of Theorem 2.12 (`1 ≠ 0`).
2. `padLeak_unguarded_oneTime_adv_eq_one`: even when `Cipher.PreservesValid` holds, omitting the
   `st.admissible` guard in `nestedToSingleAdversary.guess` turns an inadmissible pair into an
   admissible outer challenge (`0 ≠ 1`).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.NestedEncryption

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

/-! ### Positive client tests (one-bit one-time pad and module interface) -/

/-- One-bit one-time pad cipher for testing nested correctness and security. -/
def otpCipher : Cipher Bool Bool Bool where
  encrypt k m := pure (xor k m)
  decrypt k c := xor k c

/-- `otpCipher` decrypts every encrypted message to itself. -/
theorem otpCipher_correct : otpCipher.Correct := by
  intro k m c hc
  simp only [otpCipher, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hc
  subst hc
  simp [otpCipher]

/-- `n`-way nested `otpCipher` is correct for every `n`. -/
theorem otpCipher_nested_correct (n : ℕ) : (otpCipher.nested n).Correct :=
  Cipher.nested_correct otpCipher_correct n

/-- Module clients can evaluate `(E.nested 0).decrypt` and `revealKeys` via their simp lemmas. -/
example (k : Fin 0 → Bool) (c : Bool) : (otpCipher.nested 0).decrypt k c = some c := by
  simp [Cipher.nested]

example (k : Fin 2 → Bool) :
    revealKeys (1 : Fin 2) k 0 = some (k 0) ∧ revealKeys (1 : Fin 2) k 1 = none := by
  simp

/-- Single-key `otpCipher` has identical `false` and `true` experiment distributions. -/
theorem otp_oneTime_eval_eq {σ : Type}
    (B : TwoStage Unit (MessagePair Bool) Bool Bool σ) :
    ProbComp.eval (otpCipher.oneTimeExperiment (ProbComp.uniform Bool) (fun _ _ => true) B false) =
      ProbComp.eval
        (otpCipher.oneTimeExperiment (ProbComp.uniform Bool) (fun _ _ => true) B true) := by
  simp only [Cipher.oneTimeExperiment, lrExperiment, otpCipher, ↓reduceIte,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind]
  rw [PMF.bind_comm (ProbComp.eval (ProbComp.uniform Bool))]
  conv_rhs => rw [PMF.bind_comm (ProbComp.eval (ProbComp.uniform Bool))]
  congr 1; funext ⟨⟨m₀, m₁⟩, st⟩
  cases m₀ <;> cases m₁ <;>
    simp only [MessagePair.select, Bool.cond_false, Bool.cond_true, Bool.xor_false, Bool.xor_true]
  · refine PMF.ext fun b => ?_
    simp only [PMF.bind_apply, ProbComp.eval_uniform, PMF.uniformOfFintype_apply,
      Fintype.card_bool, Nat.cast_ofNat, tsum_fintype, Fintype.sum_bool, Bool.not_true,
      Bool.not_false]
    ring
  · refine PMF.ext fun b => ?_
    simp only [PMF.bind_apply, ProbComp.eval_uniform, PMF.uniformOfFintype_apply,
      Fintype.card_bool, Nat.cast_ofNat, tsum_fintype, Fintype.sum_bool, Bool.not_true,
      Bool.not_false]
    ring

/-- Every `n`-way nested `otpCipher` adversary has exact advantage `0`. -/
theorem advantage_otp_nested_eq_zero {σ : Type} (n : ℕ)
    (A : TwoStage Unit (NestedRequest Bool n) (NestedChallenge Bool Bool n) Bool σ) :
    Experiment.advantage
        (otpCipher.nestedExperiment (ProbComp.uniform Bool) (fun _ _ => true) n A false)
        (otpCipher.nestedExperiment (ProbComp.uniform Bool) (fun _ _ => true) n A true) = 0 := by
  have hpres : otpCipher.PreservesValid (ProbComp.uniform Bool) (fun _ _ => true) :=
    fun _ _ _ _ _ _ _ _ _ => rfl
  rw [advantage_nestedExperiment_eq otpCipher (ProbComp.uniform Bool) (fun _ _ => true) hpres n A]
  simp [Experiment.advantage, Game.advantage, otp_oneTime_eval_eq]

/-- Asymptotic instantiation of `indistinguishable_nestedExperiment_of_oneTimeExperiment` for
`otpCipher` and every constant nesting depth `n`. -/
theorem otp_nested_indistinguishable (n : ℕ) {σ : Type} (encσ : σ ↪ List Bool) :
    Game.Indistinguishable
      (fun (A : ℕ → TwoStage Unit (NestedRequest Bool n) (NestedChallenge Bool Bool n) Bool σ)
        sec => ProbComp.eval
          (otpCipher.nestedExperiment (ProbComp.uniform Bool) (fun _ _ => true) n (A sec) false))
      (fun A sec => ProbComp.eval
        (otpCipher.nestedExperiment (ProbComp.uniform Bool) (fun _ _ => true) n (A sec) true))
      (TwoStage.IsPPT encUnit (encNestedRequest encBool n) (encNestedChallenge encBool encBool n)
        encBool encσ) := by
  have hencrypt : IsPPTOn (encPair encUnary (encPair encBool encBool)) encBool
      fun ⟨_, k, m⟩ => otpCipher.encrypt k m :=
    (ComputableInPolyTime.bool_xor.comp
      (ComputableInPolyTime.snd encUnary (encPair encBool encBool))).isPPTOn
  refine indistinguishable_nestedExperiment_of_oneTimeExperiment
    (fun _ => otpCipher) (fun _ => ProbComp.uniform Bool) (fun _ _ _ => true)
    (isPPTOn_uniform_bool encUnary) hencrypt (ComputableInPolyTime.const true)
    (fun _ _ _ _ _ _ _ _ _ _ => rfl) n (fun encσ' _ _ => ?_) encσ
  simp [Game.advantage, otp_oneTime_eval_eq, negligible_zero]

/-! ### Boundary case (`n = 0`) and nontrivial `PreservesValid` witness -/

/-- `n = 0` makes `NestedRequest M 0` uninhabited (`withheld : Fin 0`). -/
theorem isEmpty_nestedRequest_zero (M : Type) : IsEmpty (NestedRequest M 0) :=
  ⟨fun r => Fin.elim0 r.withheld⟩

/-- Admissibility: equal first components (the first component plays the role of length). -/
def tagValid (m₀ m₁ : Bool × Bool) : Bool := m₀.1 == m₁.1

/-- Nontrivial `PreservesValid` witness: encrypts the payload while preserving the tag bit. -/
def firstBitCipher : Cipher Bool (Bool × Bool) (Bool × Bool) where
  encrypt k m := pure (m.1, xor k m.2)
  decrypt k c := some (c.1, xor k c.2)

theorem firstBitCipher_preservesValid :
    firstBitCipher.PreservesValid (ProbComp.uniform Bool) tagValid := by
  intro k _ m₀ m₁ hm c₀ hc₀ c₁ hc₁
  simp only [firstBitCipher, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hc₀ hc₁
  subst hc₀ hc₁
  exact hm

/-- Applying `advantage_nestedExperiment_eq` at the nontrivial predicate `tagValid` via
`firstBitCipher_preservesValid`. -/
example {σ : Type} (n : ℕ)
    (A : TwoStage Unit (NestedRequest (Bool × Bool) n)
      (NestedChallenge Bool (Bool × Bool) n) Bool σ) :
    Experiment.advantage
        (firstBitCipher.nestedExperiment (ProbComp.uniform Bool) tagValid n A false)
        (firstBitCipher.nestedExperiment (ProbComp.uniform Bool) tagValid n A true) =
      Experiment.advantage
        (firstBitCipher.oneTimeExperiment (ProbComp.uniform Bool) tagValid
          (nestedToSingleAdversary firstBitCipher (ProbComp.uniform Bool) tagValid n A) false)
        (firstBitCipher.oneTimeExperiment (ProbComp.uniform Bool) tagValid
          (nestedToSingleAdversary firstBitCipher (ProbComp.uniform Bool) tagValid n A) true) :=
  advantage_nestedExperiment_eq firstBitCipher (ProbComp.uniform Bool) tagValid
    firstBitCipher_preservesValid n A

/-! ### Counterexample 1: necessity of `Cipher.PreservesValid` -/

/-- One-time pad on the payload; the ciphertext's tag is the plaintext's tag XOR the padded
payload, so it depends on the payload and breaks `PreservesValid`. -/
def tagCipher : Cipher Bool (Bool × Bool) (Bool × Bool) where
  encrypt k m := pure (m.1 ^^ (m.2 ^^ k), m.2 ^^ k)
  decrypt k c := some (c.1 ^^ c.2, c.2 ^^ k)

theorem tagCipher_correct : tagCipher.Correct := by
  intro k m c hc
  simp only [tagCipher, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hc
  subst hc
  obtain ⟨t, p⟩ := m
  cases t <;> cases p <;> cases k <;> rfl

theorem not_preservesValid_tagCipher :
    ¬ tagCipher.PreservesValid (ProbComp.uniform Bool) tagValid := by
  intro h
  have := h true (by simp [ProbComp.eval_uniform]) (false, false) (false, true) rfl
    (true, true) (by simp [tagCipher]) (false, false) (by simp [tagCipher])
  exact absurd this (by decide)

/-- Every single-key adversary has advantage zero against `tagCipher`. -/
theorem advantage_oneTimeExperiment_tagCipher {σ : Type}
    (B : TwoStage Unit (MessagePair (Bool × Bool)) (Bool × Bool) Bool σ) :
    Experiment.advantage (tagCipher.oneTimeExperiment (ProbComp.uniform Bool) tagValid B false)
      (tagCipher.oneTimeExperiment (ProbComp.uniform Bool) tagValid B true) = 0 := by
  have heval :
      ProbComp.eval (tagCipher.oneTimeExperiment (ProbComp.uniform Bool) tagValid B true) =
        ProbComp.eval (tagCipher.oneTimeExperiment (ProbComp.uniform Bool) tagValid B false) := by
    simp only [Cipher.oneTimeExperiment, tagCipher, ProbComp.eval_bind, ProbComp.eval_uniform,
      eval_lrExperiment, ProbComp.eval_pure, PMF.pure_bind, MessagePair.select_true,
      MessagePair.select_false]
    rw [PMF.bind_comm]
    conv_rhs => rw [PMF.bind_comm]
    congr 1 with choice : 1
    obtain ⟨⟨⟨t₀, p₀⟩, ⟨t₁, p₁⟩⟩, st⟩ := choice
    by_cases hv : tagValid (t₀, p₀) (t₁, p₁) = true
    · have ht : t₀ = t₁ := by simpa [tagValid] using hv
      subst ht
      simp only [hv, ite_true]
      ext out
      simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, Fintype.card_bool, tsum_bool]
      cases t₀ <;> cases p₀ <;> cases p₁ <;> simp [add_comm]
    · simp only [hv, Bool.false_eq_true, ite_false, PMF.bind_const]
  rw [Experiment.advantage, heval, Game.advantage_self]

/-- Withholds the outer key and uses the revealed inner key `chal.revealedKeys 0`. -/
def tagAdv : TwoStage Unit (NestedRequest (Bool × Bool) 2)
    (NestedChallenge Bool (Bool × Bool) 2) Bool Unit where
  choose _ := pure (⟨⟨(false, false), (false, true)⟩, 1⟩, ())
  guess _ chal :=
    pure (chal.ciphertext.1 ^^ chal.ciphertext.2 ^^ (chal.revealedKeys 0).getD false)

theorem advantage_nestedExperiment_tagAdv :
    Experiment.advantage
        (tagCipher.nestedExperiment (ProbComp.uniform Bool) tagValid 2 tagAdv false)
        (tagCipher.nestedExperiment (ProbComp.uniform Bool) tagValid 2 tagAdv true) = 1 := by
  have heval (b : Bool) :
      ProbComp.eval (tagCipher.nestedExperiment (ProbComp.uniform Bool) tagValid 2 tagAdv b) =
        PMF.pure b := by
    simp only [Cipher.nestedExperiment, tagAdv, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.pure_bind]
    trans (ProbComp.eval (OracleComp.replicateFin 2 (ProbComp.uniform Bool))).bind fun _ =>
      PMF.pure b
    · congr 1; funext keys
      have hv : tagValid (false, false) (false, true) = true := rfl
      simp only [hv, ite_true, Cipher.nested, Cipher.nestedEncrypt, tagCipher, ProbComp.eval_bind,
        ProbComp.eval_pure, PMF.pure_bind]
      have h01 : (0 : Fin 2) ≠ 1 := by decide
      simp only [revealKeys_of_ne h01, Option.getD_some, Fin.tail]
      generalize keys 0 = k₀
      generalize keys (Fin.succ 0) = k₁
      cases b <;> cases k₀ <;> cases k₁ <;> rfl
    · exact PMF.bind_const _ _
  simp only [Experiment.advantage, Game.advantage, heval, Game.succProbability]
  simp [PMF.pure_apply]

/-- Counterexample 1: without `Cipher.PreservesValid`, the equality of Theorem 2.12 fails for
every single-key wrapper `B` (`1 ≠ 0`). -/
theorem tagCipher_no_wrapper {σ : Type}
    (B : TwoStage Unit (MessagePair (Bool × Bool)) (Bool × Bool) Bool σ) :
    Experiment.advantage
        (tagCipher.nestedExperiment (ProbComp.uniform Bool) tagValid 2 tagAdv false)
        (tagCipher.nestedExperiment (ProbComp.uniform Bool) tagValid 2 tagAdv true) ≠
      Experiment.advantage (tagCipher.oneTimeExperiment (ProbComp.uniform Bool) tagValid B false)
        (tagCipher.oneTimeExperiment (ProbComp.uniform Bool) tagValid B true) := by
  rw [advantage_nestedExperiment_tagAdv, advantage_oneTimeExperiment_tagCipher]
  exact one_ne_zero

/-! ### Counterexample 2: necessity of `st.admissible` in `nestedToSingleAdversary.guess` -/

/-- Equal-length admissibility predicate on `List Bool` messages. -/
def eqLenValid (m₀ m₁ : List Bool) : Bool := m₀.length == m₁.length

/-- Padding cipher that outputs length-2 lists (`PreservesValid` holds vacuously for `eqLenValid`)
while leaking the message's first bit. -/
def padLeakCipher : Cipher Bool (List Bool) (List Bool) where
  encrypt _ m := pure [m.headD false, true]
  decrypt _ _ := none

/-- `padLeakCipher` trivially preserves `eqLenValid` because all ciphertexts have length 2. -/
theorem padLeakCipher_preservesValid :
    padLeakCipher.PreservesValid (ProbComp.uniform Bool) eqLenValid := by
  intro _ _ _ _ _ c₀ hc₀ c₁ hc₁
  simp only [padLeakCipher, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hc₀ hc₁
  subst hc₀ hc₁
  rfl

/-- Nested adversary submitting an inadmissible pair `([false], [true, false])` to expose why
`nestedToSingleAdversary.guess` must check `st.admissible`. -/
def padLeakAdv :
    TwoStage Unit (NestedRequest (List Bool) 2) (NestedChallenge Bool (List Bool) 2) Bool Unit where
  choose _ := pure ({ pair := { msg₀ := [false], msg₁ := [true, false] }, withheld := 1 }, ())
  guess _ chal := pure (chal.ciphertext.headD false)

/-- Variant of `nestedToSingleAdversary` omitting the `st.admissible` check in `guess`. -/
def unguardedReduction {K M σ : Type} (E : Cipher K M M) (sampleKey : ProbComp K)
    (n : ℕ) (A : TwoStage Unit (NestedRequest M n) (NestedChallenge K M n) Bool σ) :
    TwoStage Unit (MessagePair M) M Bool (NestedReductionState K σ n) where
  choose _ := do
    let (req, st) ← A.choose ()
    let keys ← OracleComp.replicateFin n sampleKey
    let m₀' ← E.nestedPrefix req.withheld keys req.pair.msg₀
    let m₁' ← E.nestedPrefix req.withheld keys req.pair.msg₁
    pure ({ msg₀ := m₀', msg₁ := m₁' },
      { innerState := st, withheld := req.withheld, keys := keys, admissible := true })
  guess st c := do
    let c' ← E.nestedSuffix st.withheld st.keys c
    A.guess st.innerState ⟨c', revealKeys st.withheld st.keys⟩

/-- `padLeakAdv` has nested advantage `0` because its message pair fails `eqLenValid`. -/
theorem padLeak_nested_adv_eq_zero :
    Experiment.advantage
        (padLeakCipher.nestedExperiment (ProbComp.uniform Bool) eqLenValid 2 padLeakAdv false)
        (padLeakCipher.nestedExperiment
          (ProbComp.uniform Bool) eqLenValid 2 padLeakAdv true) = 0 := by
  have heval : ∀ b : Bool,
      ProbComp.eval
          (padLeakCipher.nestedExperiment (ProbComp.uniform Bool) eqLenValid 2 padLeakAdv b) =
        PMF.pure false := by
    intro b
    simp only [Cipher.nestedExperiment, eqLenValid, padLeakAdv, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.pure_bind]
    have hfalse :
        (([false] : List Bool).length == ([true, false] : List Bool).length) = false := rfl
    change (ProbComp.eval (OracleComp.replicateFin 2 (ProbComp.uniform Bool))).bind (fun _ =>
      ProbComp.eval (if (([false] : List Bool).length == ([true, false] : List Bool).length) then _
        else pure false)) = PMF.pure false
    simp only [hfalse, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure, PMF.bind_const]
  simp only [Experiment.advantage, Game.advantage, Game.succProbability, heval false, heval true]
  simp

/-- Counterexample 2: omitting `st.admissible` lets `unguardedReduction` turn an inadmissible
pair into an admissible outer pair with advantage `1 ≠ 0` even under `PreservesValid`. -/
theorem padLeak_unguarded_oneTime_adv_eq_one :
    Experiment.advantage
        (padLeakCipher.oneTimeExperiment (ProbComp.uniform Bool) eqLenValid
          (unguardedReduction padLeakCipher (ProbComp.uniform Bool) 2 padLeakAdv) false)
        (padLeakCipher.oneTimeExperiment (ProbComp.uniform Bool) eqLenValid
          (unguardedReduction padLeakCipher (ProbComp.uniform Bool) 2 padLeakAdv) true) =
      1 := by
  have heval : ∀ b : Bool,
      ProbComp.eval
          (padLeakCipher.oneTimeExperiment (ProbComp.uniform Bool) eqLenValid
            (unguardedReduction padLeakCipher (ProbComp.uniform Bool) 2 padLeakAdv) b) =
        PMF.pure b := by
    intro b
    simp only [Cipher.oneTimeExperiment, lrExperiment, unguardedReduction, padLeakAdv,
      ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
    trans ((ProbComp.eval (ProbComp.uniform Bool)).bind fun _ =>
        (ProbComp.eval (OracleComp.replicateFin 2 (ProbComp.uniform Bool))).bind fun _ =>
          PMF.pure b)
    · congr 1; funext k₁
      congr 1; funext keys
      have h1 : (1 : Fin 2) = Fin.succ 0 := rfl
      rw [h1]
      simp only [Cipher.nestedPrefix, Cipher.nestedSuffix, Fin.cases_succ, Fin.cases_zero,
        padLeakCipher, eqLenValid, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind]
      have htrue :
          (([false, true] : List Bool).length == ([true, true] : List Bool).length) = true := rfl
      change ProbComp.eval
          (if (([false, true] : List Bool).length == ([true, true] : List Bool).length) then _
           else pure false) = PMF.pure b
      simp only [htrue, ↓reduceIte]
      cases b <;> simp [MessagePair.select, Cipher.nestedEncrypt]
    · simp only [PMF.bind_const]
  simp only [Experiment.advantage, Game.advantage, Game.succProbability, heval false, heval true]
  simp [PMF.pure_apply]

/-- info: 'Cslib.Crypto.Cipher.nested_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Crypto.Cipher.nested_correct

/-- info: 'Cslib.Crypto.advantage_nestedExperiment_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Crypto.advantage_nestedExperiment_eq

/-- info: 'Cslib.Crypto.isPPT_nestedToSingleAdversary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Crypto.isPPT_nestedToSingleAdversary

/--
info: 'Cslib.Crypto.indistinguishable_nestedExperiment_of_oneTimeExperiment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.indistinguishable_nestedExperiment_of_oneTimeExperiment

end CslibFrontierTests.Crypto.NestedEncryption
