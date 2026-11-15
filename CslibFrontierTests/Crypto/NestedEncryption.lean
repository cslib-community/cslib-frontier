/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.Encryption.Nested
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PMFSwap

/-!
# Tests and counterexamples for `n`-way nested encryption

Positive tests verify correctness (`Cipher.nested_correct`) and zero advantage
(`advantage_nestedExperiment_eq`) for `n`-way nested one-time pad encryption, together with the
vacuous `n = 0` case (`IsEmpty (NestedRequest M 0)`). Two counterexamples show why the added
hypotheses in `advantage_nestedExperiment_eq` cannot be dropped:

1. `varLen_nested_ne_oneTime`: without `Cipher.PreservesValid`, a correct cipher whose encryption
   can emit distinct ciphertext lengths loses admissibility after prefix encryption, breaking
   `advantage_nestedExperiment_eq` (`1 ≠ 1 / 2`).
2. `padLeak_unguarded_oneTime_adv_eq_one`: even when `Cipher.PreservesValid` holds, omitting the
   `st.admissible` guard in `nestedToSingleAdversary.guess` turns an inadmissible pair into an
   admissible outer challenge (`0 ≠ 1`).
-/

namespace CslibFrontierTests.Crypto.NestedEncryption

open Cslib Cslib.Crypto Cslib.Probability

/-! ### Positive client tests (one-bit one-time pad) -/

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

/-! ### Boundary case (`n = 0`) and counterexamples for added hypotheses -/

/-- `n = 0` makes `NestedRequest M 0` uninhabited (`withheld : Fin 0`). -/
theorem isEmpty_nestedRequest_zero (M : Type) : IsEmpty (NestedRequest M 0) :=
  ⟨fun r => Fin.elim0 r.withheld⟩

/-- Equal-length admissibility predicate on `List Bool` messages. -/
def varLenValid (m₀ m₁ : List Bool) : Bool := m₀.length == m₁.length

/-- Variable-length-tag cipher: correct (`varLenCipher_correct`), ignores the key, and tags the
message with `[true]` or `[false, false]` uniformly at random, violating `PreservesValid`. -/
noncomputable def varLenCipher : Cipher Bool (List Bool) (List Bool) where
  encrypt _ m := do
    let r ← ProbComp.uniform Bool
    return (if r then [true] ++ m else [false, false] ++ m)
  decrypt _ c :=
    match c with
    | true :: rest => some rest
    | false :: false :: rest => some rest
    | _ => none

/-- `varLenCipher` is perfectly correct despite violating `PreservesValid`. -/
theorem varLenCipher_correct : varLenCipher.Correct := by
  intro k m c hc
  simp only [varLenCipher, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.support_pure, Set.mem_singleton_iff] at hc
  rcases hc with ⟨r, _, rfl⟩
  cases r <;> rfl

/-- Nested adversary against 2-way `varLenCipher` reading the last bit of the challenge. -/
def varLenAdv :
    TwoStage Unit (NestedRequest (List Bool) 2) (NestedChallenge Bool (List Bool) 2) Bool Unit where
  choose _ := pure ({ pair := { msg₀ := [false], msg₁ := [true] }, withheld := 1 }, ())
  guess _ chal := pure (chal.ciphertext.getLast? == some true)

/-- Against 2-way `varLenCipher`, `varLenAdv` achieves nested advantage `1`. -/
theorem varLen_nested_adv_eq_one :
    Experiment.advantage
        (varLenCipher.nestedExperiment (ProbComp.uniform Bool) varLenValid 2 varLenAdv false)
        (varLenCipher.nestedExperiment
          (ProbComp.uniform Bool) varLenValid 2 varLenAdv true) = 1 := by
  have heval : ∀ b : Bool,
      ProbComp.eval
          (varLenCipher.nestedExperiment (ProbComp.uniform Bool) varLenValid 2 varLenAdv b) =
        PMF.pure b := by
    intro b
    simp only [Cipher.nestedExperiment, varLenValid, varLenAdv, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.pure_bind]
    trans ((ProbComp.eval (OracleComp.replicateFin 2 (ProbComp.uniform Bool))).bind fun _ =>
        PMF.pure b)
    · congr 1; funext keys
      have hadm : (([false] : List Bool).length == ([true] : List Bool).length) = true := rfl
      change ProbComp.eval
          (if (([false] : List Bool).length == ([true] : List Bool).length) then _ else _) = _
      simp only [hadm, ↓reduceIte]
      simp only [Cipher.nested, nestedEncrypt, varLenCipher, ProbComp.eval_bind,
        ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
      have huniv : ∀ f : Bool → PMF Bool, (∀ r, f r = PMF.pure b) →
          ((ProbComp.eval (ProbComp.uniform Bool)).bind f) = PMF.pure b := by
        intro f hf
        rw [show f = fun _ => PMF.pure b from funext hf]
        exact PMF.bind_const _ _
      apply huniv; intro r₀
      apply huniv; intro r₁
      cases b <;> cases r₀ <;> cases r₁ <;> rfl
    · exact PMF.bind_const _ _
  simp only [Experiment.advantage, Game.advantage, heval false, heval true, Game.succProbability]
  simp [PMF.pure_apply]

/-- Without `PreservesValid`, `nestedToSingleAdversary` loses half its advantage (`1 / 2`) because
the prefix encryptions have equal length with probability `1 / 2`. -/
theorem varLen_oneTime_adv_eq_half :
    Experiment.advantage
        (varLenCipher.oneTimeExperiment (ProbComp.uniform Bool) varLenValid
          (nestedToSingleAdversary varLenCipher (ProbComp.uniform Bool) varLenValid 2 varLenAdv)
          false)
        (varLenCipher.oneTimeExperiment (ProbComp.uniform Bool) varLenValid
          (nestedToSingleAdversary varLenCipher (ProbComp.uniform Bool) varLenValid 2 varLenAdv)
          true) = (1 / 2 : NNReal) := by
  have hprob : ∀ b : Bool,
      ProbComp.eval
          (varLenCipher.oneTimeExperiment (ProbComp.uniform Bool) varLenValid
            (nestedToSingleAdversary varLenCipher (ProbComp.uniform Bool) varLenValid 2 varLenAdv)
            b) =
        PMF.bind (ProbComp.eval (ProbComp.uniform Bool)) fun r₀ =>
          PMF.bind (ProbComp.eval (ProbComp.uniform Bool)) fun r₁ =>
            PMF.pure (b && (r₀ == r₁)) := by
    intro b
    simp only [Cipher.oneTimeExperiment, lrExperiment, nestedToSingleAdversary, varLenAdv,
      ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
    have hadm : varLenValid [false] [true] = true := rfl
    have hbody : ∀ (k₁ : Bool) (revealed : Fin 2 → Option Bool),
        revealed ∈
            (ProbComp.eval (sampleRevealedKeys (ProbComp.uniform Bool) (1 : Fin 2))).support →
        ((ProbComp.eval (nestedPrefixOpt varLenCipher (1 : Fin 2) revealed [false])).bind fun m₀' =>
          (ProbComp.eval (nestedPrefixOpt varLenCipher (1 : Fin 2) revealed [true])).bind fun m₁' =>
            ProbComp.eval (if varLenValid m₀' m₁' then do
              let c ← varLenCipher.encrypt k₁
                (({ msg₀ := m₀', msg₁ := m₁' } : MessagePair (List Bool)).select b)
              let c' ← nestedSuffixOpt varLenCipher (1 : Fin 2) revealed c
              pure (c'.getLast? == some true)
            else pure false)) =
          PMF.bind (ProbComp.eval (ProbComp.uniform Bool)) fun r₀ =>
            PMF.bind (ProbComp.eval (ProbComp.uniform Bool)) fun r₁ =>
              PMF.pure (b && (r₀ == r₁)) := by
      intro k₁ revealed hrev
      have h1 : (1 : Fin 2) = Fin.succ 0 := rfl
      rw [h1] at hrev ⊢
      simp only [sampleRevealedKeys, Fin.cases_succ, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_singleton_iff] at hrev
      obtain ⟨k₀, _, _, _, rfl⟩ := hrev
      simp only [nestedPrefixOpt, nestedSuffixOpt, Fin.cases_succ, Fin.cases_zero, Fin.cons_zero,
        varLenCipher, varLenValid, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind,
        PMF.pure_bind]
      congr 1; funext r₀
      congr 1; funext r₁
      cases b <;> cases r₀ <;> cases r₁ <;>
        first
        | (simp; done)
        | (simp only [Bool.false_eq_true, ↓reduceIte, MessagePair.select, Bool.cond_false,
            Bool.cond_true, nestedEncryptOpt, ProbComp.eval_bind, ProbComp.eval_pure,
            PMF.bind_bind, PMF.pure_bind, List.cons_append, List.nil_append, List.length_cons,
            List.length_nil, BEq.rfl, Bool.and_true]
           rw [show (fun _ : Bool => PMF.pure _) = fun _ => PMF.pure _ from
             funext fun x => by cases x <;> rfl]
           exact PMF.bind_const _ _)
    have hstep1 : ∀ k₁ : Bool,
        ((ProbComp.eval
            (sampleRevealedKeys (ProbComp.uniform Bool) (1 : Fin 2))).bind fun revealed =>
          ((ProbComp.eval
              (nestedPrefixOpt varLenCipher (1 : Fin 2) revealed [false])).bind fun m₀' =>
            (ProbComp.eval
                (nestedPrefixOpt varLenCipher (1 : Fin 2) revealed [true])).bind fun m₁' =>
              ProbComp.eval (if varLenValid m₀' m₁' then do
                let c ← varLenCipher.encrypt k₁
                  (({ msg₀ := m₀', msg₁ := m₁' } : MessagePair (List Bool)).select b)
                if varLenValid ([false] : List Bool) ([true] : List Bool) then
                  let c' ← nestedSuffixOpt varLenCipher (1 : Fin 2) revealed c
                  pure (c'.getLast? == some true)
                else pure false
              else pure false))) =
          PMF.bind (ProbComp.eval (ProbComp.uniform Bool)) fun r₀ =>
            PMF.bind (ProbComp.eval (ProbComp.uniform Bool)) fun r₁ =>
              PMF.pure (b && (r₀ == r₁)) := by
      intro k₁
      trans ((ProbComp.eval (sampleRevealedKeys (ProbComp.uniform Bool) (1 : Fin 2))).bind fun _ =>
          PMF.bind (ProbComp.eval (ProbComp.uniform Bool)) fun r₀ =>
            PMF.bind (ProbComp.eval (ProbComp.uniform Bool)) fun r₁ =>
              PMF.pure (b && (r₀ == r₁)))
      · refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun revealed hrev => ?_
        simpa only [hadm, ↓reduceIte] using hbody k₁ revealed hrev
      · exact PMF.bind_const _ _
    trans ((ProbComp.eval (ProbComp.uniform Bool)).bind fun _ =>
        PMF.bind (ProbComp.eval (ProbComp.uniform Bool)) fun r₀ =>
          PMF.bind (ProbComp.eval (ProbComp.uniform Bool)) fun r₁ =>
            PMF.pure (b && (r₀ == r₁)))
    · congr 1; funext k₁; exact hstep1 k₁
    · exact PMF.bind_const _ _
  have hnn : ∀ b : Bool,
      ((ProbComp.eval
          (varLenCipher.oneTimeExperiment (ProbComp.uniform Bool) varLenValid
            (nestedToSingleAdversary varLenCipher (ProbComp.uniform Bool) varLenValid 2 varLenAdv)
            b)) true).toNNReal =
        if b then (1 / 2 : NNReal) else 0 := by
    intro b
    rw [hprob b]
    ext
    simp only [PMF.bind_apply, ProbComp.eval_uniform, PMF.uniformOfFintype_apply,
      Fintype.card_bool, Nat.cast_ofNat, tsum_fintype, Fintype.sum_bool, PMF.pure_apply]
    cases b
    · simp
    · have htf : (true == false) = false := rfl
      have hft : (false == true) = false := rfl
      simp only [Bool.true_and, beq_self_eq_true, htf, hft, Bool.true_eq_false, ↓reduceIte,
        mul_one, NNReal.coe_one, NNReal.coe_div, NNReal.coe_ofNat]
      have hsum : (2 : ENNReal)⁻¹ * (2⁻¹ + 2⁻¹ * 0) + 2⁻¹ * (2⁻¹ * 0 + 2⁻¹) =
          (2 : ENNReal)⁻¹ * 2⁻¹ + 2⁻¹ * 2⁻¹ := by ring
      rw [hsum]
      have hinv : (2 : ENNReal)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by norm_num)
      have hmul : (2 : ENNReal)⁻¹ * 2⁻¹ ≠ ⊤ := ENNReal.mul_ne_top hinv hinv
      change ((2 : ENNReal)⁻¹ * 2⁻¹ + 2⁻¹ * 2⁻¹).toReal = 1 / 2
      rw [ENNReal.toReal_add hmul hmul, ENNReal.toReal_mul, ENNReal.toReal_inv,
        ENNReal.toReal_ofNat]
      norm_num
  simp only [Experiment.advantage, Game.advantage, hnn false, hnn true]
  ext
  simp only [nndist, NNReal.coe_one, NNReal.coe_div, NNReal.coe_ofNat]
  change dist (0 : ℝ) (1 / 2) = 1 / 2
  rw [Real.dist_eq]
  norm_num

/-- Counterexample 1: without `Cipher.PreservesValid`, `advantage_nestedExperiment_eq` fails
(`1 ≠ 1 / 2`). -/
theorem varLen_nested_ne_oneTime :
    Experiment.advantage
        (varLenCipher.nestedExperiment (ProbComp.uniform Bool) varLenValid 2 varLenAdv false)
        (varLenCipher.nestedExperiment (ProbComp.uniform Bool) varLenValid 2 varLenAdv true) ≠
      Experiment.advantage
        (varLenCipher.oneTimeExperiment (ProbComp.uniform Bool) varLenValid
          (nestedToSingleAdversary varLenCipher (ProbComp.uniform Bool) varLenValid 2 varLenAdv)
          false)
        (varLenCipher.oneTimeExperiment (ProbComp.uniform Bool) varLenValid
          (nestedToSingleAdversary varLenCipher (ProbComp.uniform Bool) varLenValid 2 varLenAdv)
          true) := by
  rw [varLen_nested_adv_eq_one, varLen_oneTime_adv_eq_half]
  norm_num

/-- Padding cipher that outputs length-2 lists (`PreservesValid` holds vacuously for `varLenValid`)
while leaking the message's first bit. -/
def padLeakCipher : Cipher Bool (List Bool) (List Bool) where
  encrypt _ m := pure [m.headD false, true]
  decrypt _ _ := none

/-- `padLeakCipher` trivially preserves `varLenValid` because all ciphertexts have length 2. -/
theorem padLeakCipher_preservesValid :
    padLeakCipher.PreservesValid (ProbComp.uniform Bool) varLenValid := by
  intro k hk m₀ m₁ _ c₀ hc₀ c₁ hc₁
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
    let revealed ← sampleRevealedKeys sampleKey req.withheld
    let m₀' ← nestedPrefixOpt E req.withheld revealed req.pair.msg₀
    let m₁' ← nestedPrefixOpt E req.withheld revealed req.pair.msg₁
    pure ({ msg₀ := m₀', msg₁ := m₁' },
      { admissible := true, withheld := req.withheld, revealedKeys := revealed, innerState := st })
  guess st c := do
    let c' ← nestedSuffixOpt E st.withheld st.revealedKeys c
    A.guess st.innerState ⟨c', st.revealedKeys⟩

/-- `padLeakAdv` has nested advantage `0` because its message pair fails `varLenValid`. -/
theorem padLeak_nested_adv_eq_zero :
    Experiment.advantage
        (padLeakCipher.nestedExperiment (ProbComp.uniform Bool) varLenValid 2 padLeakAdv false)
        (padLeakCipher.nestedExperiment
          (ProbComp.uniform Bool) varLenValid 2 padLeakAdv true) = 0 := by
  have heval : ∀ b : Bool,
      ProbComp.eval
          (padLeakCipher.nestedExperiment (ProbComp.uniform Bool) varLenValid 2 padLeakAdv b) =
        PMF.pure false := by
    intro b
    simp only [Cipher.nestedExperiment, varLenValid, padLeakAdv, ProbComp.eval_bind,
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
        (padLeakCipher.oneTimeExperiment (ProbComp.uniform Bool) varLenValid
          (unguardedReduction padLeakCipher (ProbComp.uniform Bool) 2 padLeakAdv) false)
        (padLeakCipher.oneTimeExperiment (ProbComp.uniform Bool) varLenValid
          (unguardedReduction padLeakCipher (ProbComp.uniform Bool) 2 padLeakAdv) true) =
      1 := by
  have heval : ∀ b : Bool,
      ProbComp.eval
          (padLeakCipher.oneTimeExperiment (ProbComp.uniform Bool) varLenValid
            (unguardedReduction padLeakCipher (ProbComp.uniform Bool) 2 padLeakAdv) b) =
        PMF.pure b := by
    intro b
    simp only [Cipher.oneTimeExperiment, lrExperiment, unguardedReduction, padLeakAdv,
      ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
    have h1 : (1 : Fin 2) = Fin.succ 0 := rfl
    trans ((ProbComp.eval (ProbComp.uniform Bool)).bind fun _ =>
        (ProbComp.eval (sampleRevealedKeys (ProbComp.uniform Bool) (1 : Fin 2))).bind fun _ =>
          PMF.pure b)
    · congr 1; funext k₁
      refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun revealed hrev => ?_
      rw [h1] at hrev ⊢
      simp only [sampleRevealedKeys, Fin.cases_succ, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_singleton_iff] at hrev
      obtain ⟨k₀, _, _, _, rfl⟩ := hrev
      simp only [nestedPrefixOpt, nestedSuffixOpt, Fin.cases_succ, Fin.cases_zero, Fin.cons_zero,
        padLeakCipher, varLenValid, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind]
      have htrue :
          (([false, true] : List Bool).length == ([true, true] : List Bool).length) = true := rfl
      change ProbComp.eval
          (if (([false, true] : List Bool).length == ([true, true] : List Bool).length) then _
           else pure false) = PMF.pure b
      simp only [htrue, ↓reduceIte]
      cases b <;> simp [MessagePair.select, nestedEncryptOpt]
    · simp only [PMF.bind_const]
  simp only [Experiment.advantage, Game.advantage, Game.succProbability, heval false, heval true]
  simp [PMF.pure_apply]

end CslibFrontierTests.Crypto.NestedEncryption
