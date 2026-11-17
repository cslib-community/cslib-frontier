/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.AuthenticatedKeyExchange.Static
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Tactic.PPT

/-!
# Authenticated key exchange: tests and counterexamples

Concrete checks for `CslibFrontier.Crypto.Computational.AuthenticatedKeyExchange`:

* **T2 (`abortProtocol`)**: a protocol that immediately aborts every session satisfies
  `Protocol.StaticallySecure` (`abortProtocol_staticallySecure`), showing the lack of a
  correctness clause in Definition 21.1 of [BonehShoup2023], §21.9.
* **T1a (`echoProtocol`)**: a protocol that accepts any incoming identity as its partner with a
  fresh key fails static security with advantage `1` (`staticAdvantage_echoAttack`,
  `not_staticallySecure_echoProtocol`).
* **T1b (`constKeyProtocol`)**: a protocol that outputs a predictable constant key `0^n` with its
  own user as partner fails static security for `1 ≤ n` (`staticAdvantage_constKeyAttack_ge`,
  `not_staticallySecure_constKeyProtocol`), while at `n = 0` (`P2`) the singleton key space yields
  advantage `0` (`staticAdvantage_constKeyAttack_zero`).
* **P1 (`eval_challenger_deliver_fresh_reply`)**: a finishing fresh query to a registered user
  returns a reply with the same distribution in Experiments 0 and 1.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.AuthenticatedKeyExchange

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.AKE Turing.MultiTapeTM
open scoped NNReal

/-! ### Test helpers -/

/-- Build a protocol with a trivial trusted third party from `keyLength`, a `step` that keeps no
instance state, and their certificates. -/
private def Protocol.ofStep (keyLength : ℕ → ℕ)
    (step : StepInput → ProbComp StepOutput)
    (keyLength_polyTime : ComputableInPolyTime keyLength encUnary encUnary)
    (step_ppt : IsPPTOn encStepInput encStepOutput step)
    (key_length : ∀ input, ∀ out ∈ (ProbComp.eval (step input)).support,
      out.phase = .finished → out.key.length = keyLength input.parameter)
    (step_state : ∀ input, ∀ out ∈ (ProbComp.eval (step input)).support, out.state = []) :
    Protocol where
  keyLength := keyLength
  ttpInit := fun _ => pure []
  registerHonest := fun input => pure ⟨input.ttp, []⟩
  registerCorrupt := fun input => pure ⟨input.ttp, []⟩
  ttpStep := fun input => pure ⟨input.ttp, []⟩
  step := step
  keyLength_polyTime := keyLength_polyTime
  ttpInit_ppt := by ppt
  registerHonest_ppt := by ppt
  registerCorrupt_ppt := by ppt
  ttpStep_ppt := by ppt
  step_ppt := step_ppt
  key_length := key_length
  sizeBound := fun _ => 1
  sizeBound_polyTime := by ppt
  registerHonest_ttp_length := fun _ _ hout => by simp_all
  registerHonest_output_length := fun _ _ hout => by simp_all
  registerCorrupt_ttp_length := fun _ _ hout => by simp_all
  ttpStep_ttp_length := fun _ _ hout => by simp_all
  step_state_length := fun input out hout => by simp [step_state input out hout]

/-- Taking `w.length + 1` bits of `w ++ b :: k` strictly extends `w` and therefore differs from
`w`. -/
theorem take_append_cons_bne (w k : List Bool) (b : Bool) :
    ((w ++ b :: k).take (w.length + 1) != w) = true := by
  simp only [bne_iff_ne, ne_eq]
  intro h
  have hlen := congrArg List.length h
  rw [List.length_take, List.length_append, List.length_cons] at hlen
  omega

/-- A Boolean test satisfied by at most one `n`-bit word passes on a uniform `n`-bit word with
probability at most `1 / 2 ^ n`. -/
theorem uniformList_map_true_le (n : ℕ) (f : List Bool → Bool)
    (huniq : ∀ k₁ k₂, k₁.length = n → k₂.length = n → f k₁ = true → f k₂ = true → k₁ = k₂) :
    (BitString.uniformList n).map f true ≤ (1 : ENNReal) / 2 ^ n := by
  rw [BitString.uniformList_map_apply]
  gcongr
  norm_cast
  exact Finset.card_le_one.mpr fun a ha b hb => List.ofFn_injective (huniq _ _
    (by simp) (by simp) (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2)

/-- When `I.partner` is unregistered, `exposed = false`, and no instance in `s` is classified as
`fresh`, `effectiveKey` evaluates to `PMF.pure none` for every classification. -/
theorem effectiveKey_of_not_registered (P : Protocol) (n : ℕ) (c : Classification)
    (I : Instance) (s : Challenger) (hreg : s.isRegistered I.partner = false)
    (hfresh : ∀ J ∈ s.instances, J.classification ≠ some .fresh) :
    ProbComp.eval (effectiveKey P n c false I s) = PMF.pure none := by
  have hcor : s.isCorrupt I.partner = false := by
    simp only [Challenger.isRegistered, Bool.or_eq_false_iff] at hreg
    exact hreg.2
  cases c with
  | vulnerable => simp [effectiveKey, hcor, ProbComp.eval_pure]
  | fresh => simp [effectiveKey, hreg, ProbComp.eval_pure]
  | connected peer =>
    simp only [effectiveKey]
    cases hget : s.instances[peer]? with
    | none => simp [ProbComp.eval_pure]
    | some J =>
      have hne : J.classification ≠ some .fresh := hfresh J (List.mem_of_getElem? hget)
      simp [hne, ProbComp.eval_pure]

/-- Common three-step execution for `Protocol.ofStep` attacks: register user `[]`, initialize
instance `0` with `.left`, and deliver `msg` to instance `0`, continuing via `k` on the truncated
reply. -/
private theorem eval_ofStep_threeStep (kl : ℕ → ℕ)
    (step : StepInput → ProbComp StepOutput) (hkl) (hstep_ppt) (hlen) (hstate)
    (ideal : Option Idealization) (n : ℕ) (m : ℕ → ℕ) (msg : List Bool)
    (k : ℕ → List Bool → Bool) :
    ProbComp.eval ((Protocol.ofStep kl step hkl hstep_ppt hlen hstate).run ideal (fun i _ => do
      let _ ← List.take 0 <$> ProbOracleComp.query (.registerHonest, [])
      let _ ← List.take 0 <$> ProbOracleComp.query (.init .left, [])
      let reply ← List.take (m i) <$>
        ProbOracleComp.query (.deliver, encPair encBits encBits ([], msg))
      pure (k i reply)) n) =
      (ProbComp.eval (challenger (Protocol.ofStep kl step hkl hstep_ppt hlen hstate) n ideal
        (.deliver, encPair encBits encBits ([], msg))
        ⟨[], [⟨[], []⟩], [], [⟨[], [], .left, [], .running, [], [], none, none⟩],
          [LogEntry.init 0 .left]⟩)).map (fun res => k n (res.1.take (m n))) := by
  simp only [Protocol.run, Protocol.ofStep, OracleComp.interpret_bind, OracleComp.interpret_map,
    OracleComp.interpret_pure, ProbOracleComp.interpret_query, StateT.run_bind, StateT.run_map,
    StateT.run_pure, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure]
  dsimp only [StateT.run, OracleComp.sumHandler]
  rw [PMF.pure_bind, challenger_registerHonest]
  have hreg : (⟨[], [], [], [], []⟩ : Challenger).isRegistered [] = false := rfl
  simp only [hreg, Bool.false_eq_true, Protocol.not_tooLong_nil, or_self, ↓reduceIte,
    ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.pure_bind, PMF.pure_map, List.nil_append]
  rw [challenger_init]
  have hfind : (⟨[], [⟨[], []⟩], [], [], []⟩ : Challenger).findHonest [] = some ⟨[], []⟩ := rfl
  simp only [hfind, List.nil_append, List.length_nil, ProbComp.eval_pure, PMF.pure_bind,
    PMF.pure_map, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  exact (PMF.bind_pure_comp _ _).symm

/-! ### T2: Protocol that always aborts satisfies static security -/

/-- Degenerate protocol whose session key establishment immediately aborts every instance. -/
def abortProtocol : Protocol :=
  Protocol.ofStep id
    (fun _ => pure ⟨[], [], .aborted, [], []⟩)
    (by ppt) (by ppt)
    (fun _ _ hout hfin => by
      simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hout
      subst hout
      cases hfin)
    fun _ _ hout => by
      simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hout
      subst hout
      rfl

/-- Because `abortProtocol` never finishes an instance, Experiment 1 and Experiment 0 have identical
query handlers for every idealization. -/
theorem challenger_abortProtocol (n : ℕ) (idl : Idealization) :
    challenger abortProtocol n (some idl) = challenger abortProtocol n none := by
  funext ⟨op, req⟩ s
  cases op with
  | registerHonest => simp only [challenger_registerHonest]
  | registerCorrupt => simp only [challenger_registerCorrupt]
  | init role => simp only [challenger_init]
  | deliverTTP => simp only [challenger_deliverTTP]
  | deliver =>
    cases hget : s.instances[(unframe req).length]? with
    | none =>
      rw [challenger_deliver_of_getElem?_eq_none _ _ _ _ _ hget,
        challenger_deliver_of_getElem?_eq_none _ _ _ _ _ hget]
    | some inst =>
      by_cases hlong : abortProtocol.TooLong n (dropFrame req)
      · rw [challenger_deliver_of_tooLong _ _ _ _ _ hlong,
          challenger_deliver_of_tooLong _ _ _ _ _ hlong]
      by_cases hrun : inst.phase = .running
      · rw [challenger_deliver_of_running _ _ _ _ _ inst hget hrun hlong,
          challenger_deliver_of_running _ _ _ _ _ inst hget hrun hlong]
        simp [abortProtocol, Protocol.ofStep]
      · rw [challenger_deliver_of_not_running _ _ _ _ _ inst hget hrun,
          challenger_deliver_of_not_running _ _ _ _ _ inst hget hrun]

/-- `abortProtocol` is statically secure against every partner function. -/
theorem abortProtocol_staticallySecureWith (pf : PartnerFunction) :
    abortProtocol.StaticallySecureWith pf := by
  intro adversary _
  have hrun (n : ℕ) :
      abortProtocol.run (some { partner := pf n }) adversary n =
        abortProtocol.run none adversary n := by
    simp only [Protocol.run, challenger_abortProtocol]
  simp only [hrun, Game.advantage_self]
  exact negligible_zero

/-- `abortProtocol` satisfies `Protocol.StaticallySecure`. -/
theorem abortProtocol_staticallySecure : abortProtocol.StaticallySecure :=
  ⟨fun _ _ => .fresh, ComputableInPolyTime.const _, abortProtocol_staticallySecureWith _⟩

/-! ### T1a: Accepting an unregistered partner breaks static security -/

/-- Protocol whose session step immediately finishes with a fresh uniform `n`-bit key and accepts
the incoming message verbatim as the partner identity. -/
noncomputable def echoProtocol : Protocol :=
  Protocol.ofStep id
    (fun input => do
      let key ← BitString.sampleList input.parameter
      pure ⟨[], [], .finished, input.message, key⟩)
    (by ppt) (by ppt)
    (fun input out hout _ => by
      simp only [ProbComp.eval_bind, BitString.eval_sampleList, ProbComp.eval_pure,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hout
      obtain ⟨k, hk, rfl⟩ := hout
      exact BitString.length_of_mem_support_uniformList hk)
    fun _ _ hout => by
      simp only [ProbComp.eval_bind, BitString.eval_sampleList, ProbComp.eval_pure,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hout
      obtain ⟨_, _, rfl⟩ := hout
      rfl

private def echoErrorReply : List Bool :=
  encDeliverReply ⟨[], .finished, [true], none⟩

/-- Active attack against `echoProtocol`: registers user `[]`, creates instance `0`, delivers
partner identity `[true]`, and tests whether the reply extends the `error` prefix. -/
def echoAttack : Adversary := fun _ _ => do
  let _ ← List.take 0 <$> ProbOracleComp.query (.registerHonest, [])
  let _ ← List.take 0 <$> ProbOracleComp.query (.init .left, [])
  let reply ← List.take (echoErrorReply.length + 1) <$>
    ProbOracleComp.query (.deliver, encPair encBits encBits ([], [true]))
  pure (reply != echoErrorReply)

/-- `echoAttack` is uniformly strict oracle-PPT. -/
theorem isOraclePPT_echoAttack : IsOraclePPT encBool echoAttack := by
  ppt [echoAttack]

/-- In Experiment 0, `echoAttack` always outputs `true` against `echoProtocol`. -/
theorem eval_run_none_echoAttack (n : ℕ) :
    ProbComp.eval (echoProtocol.run none echoAttack n) = PMF.pure true := by
  unfold echoProtocol echoAttack
  rw [eval_ofStep_threeStep]
  rw [challenger_deliver_of_running _ _ _ _ _
    ⟨[], [], .left, [], .running, [], [], none, none⟩
    (by rw [unframe_encPair_encBits]; rfl) rfl
    (by rw [dropFrame_encPair_encBits]; simp [Protocol.TooLong, Protocol.ofStep])]
  dsimp only [Protocol.ofStep]
  simp only [unframe_encPair_encBits, dropFrame_encPair_encBits, List.length_nil,
    ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList, PMF.bind_bind,
    PMF.pure_bind, ↓reduceIte, PMF.map_bind, PMF.pure_map]
  trans (BitString.uniformList n).bind (fun _ => PMF.pure true)
  · refine congrArg (PMF.bind _) (funext fun k => ?_)
    simp only [echoErrorReply, encDeliverReply_some, take_append_cons_bne]
  · exact PMF.bind_const _ _

/-- In Experiment 1, `echoAttack` always outputs `false` against `echoProtocol` for every
partner function `pf`, because partner `[true]` is unregistered. -/
theorem eval_run_some_echoAttack (pf : PartnerFunction) (n : ℕ) :
    ProbComp.eval (echoProtocol.run (some { partner := pf n }) echoAttack n) = PMF.pure false := by
  unfold echoProtocol echoAttack
  rw [eval_ofStep_threeStep]
  rw [challenger_deliver_of_running _ _ _ _ _
    ⟨[], [], .left, [], .running, [], [], none, none⟩
    (by rw [unframe_encPair_encBits]; rfl) rfl
    (by rw [dropFrame_encPair_encBits]; simp [Protocol.TooLong, Protocol.ofStep])]
  dsimp only [Protocol.ofStep]
  simp only [unframe_encPair_encBits, dropFrame_encPair_encBits, List.length_nil,
    ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList, PMF.bind_bind,
    PMF.pure_bind, ↓reduceIte, PMF.map_bind, PMF.pure_map]
  trans (BitString.uniformList n).bind (fun _ => PMF.pure false)
  · refine congrArg (PMF.bind _) (funext fun k => ?_)
    rw [effectiveKey_of_not_registered _ n _ _ _]
    · simp [echoErrorReply, List.take_of_length_le]
    · rfl
    · simp
  · exact PMF.bind_const _ _

/-- `echoAttack` achieves distinguishing advantage `1` against `echoProtocol` for every `pf` and
`n`. -/
theorem staticAdvantage_echoAttack (pf : PartnerFunction) (n : ℕ) :
    echoProtocol.staticAdvantage pf echoAttack n = 1 := by
  rw [Protocol.staticAdvantage, eval_run_none_echoAttack, eval_run_some_echoAttack,
    Game.advantage_pure_false, Game.succProbability]
  simp

/-- `echoProtocol` is not statically secure. -/
theorem not_staticallySecure_echoProtocol : ¬ echoProtocol.StaticallySecure := by
  rintro ⟨pf, _, hsec⟩
  have hnot := hsec echoAttack isOraclePPT_echoAttack
  change Negligible (fun n => echoProtocol.staticAdvantage pf echoAttack n) at hnot
  have heq : (fun n => echoProtocol.staticAdvantage pf echoAttack n) = fun _ => 1 :=
    funext (staticAdvantage_echoAttack pf)
  rw [heq] at hnot
  exact not_negligible_const one_ne_zero hnot

/-! ### T1b & P2: A constant key breaks static security for `1 ≤ n` (`0` at `n = 0`) -/

/-- Protocol whose session step immediately finishes with its own user as partner and the
constant all-zero key `List.replicate n false`. -/
def constKeyProtocol : Protocol :=
  Protocol.ofStep id
    (fun input => pure ⟨[], [], .finished, input.user, List.replicate input.parameter false⟩)
    (by ppt) (by ppt)
    (fun input out hout _ => by
      simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hout
      subst hout
      simp)
    fun _ _ hout => by
      simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hout
      subst hout
      rfl

private def zeroReplyPrefix : List Bool :=
  encDeliverReply ⟨[], .finished, [], none⟩ ++ [true]

private def zeroReplyExpected (n : ℕ) : List Bool :=
  zeroReplyPrefix ++ List.replicate n false

@[fun_prop]
private theorem computableInPolyTime_zeroReplyExpected :
    ComputableInPolyTime zeroReplyExpected encUnary encBits := by
  unfold zeroReplyExpected
  fun_prop

/-- Active attack against `constKeyProtocol`: registers user `[]`, creates instance `0`, delivers
`[]`, and tests whether the reply matches the all-zero session key `0^n`. -/
def constKeyAttack : Adversary := fun n _ => do
  let _ ← List.take 0 <$> ProbOracleComp.query (.registerHonest, [])
  let _ ← List.take 0 <$> ProbOracleComp.query (.init .left, [])
  let reply ← List.take (zeroReplyPrefix.length + n + 1) <$>
    ProbOracleComp.query (.deliver, encPair encBits encBits ([], []))
  pure (reply == zeroReplyExpected n)

/-- `constKeyAttack` is uniformly strict oracle-PPT. -/
theorem isOraclePPT_constKeyAttack : IsOraclePPT encBool constKeyAttack := by
  ppt [constKeyAttack]

private theorem zeroReplyPrefix_append_eq (n : ℕ) :
    zeroReplyPrefix ++ List.replicate n false =
      encDeliverReply ⟨[], .finished, [], some (List.replicate n false)⟩ := by
  simp [zeroReplyPrefix]

private theorem zeroReplyPrefix_length_add (n : ℕ) :
    zeroReplyPrefix.length + n + 1 =
      (encDeliverReply ⟨[], .finished, [], some (List.replicate n false)⟩).length + 1 := by
  rw [← zeroReplyPrefix_append_eq, List.length_append, List.length_replicate]

/-- In Experiment 0, `constKeyAttack` outputs `true` with probability `1`. -/
theorem eval_run_none_constKeyAttack (n : ℕ) :
    ProbComp.eval (constKeyProtocol.run none constKeyAttack n) = PMF.pure true := by
  unfold constKeyProtocol constKeyAttack
  rw [eval_ofStep_threeStep]
  rw [challenger_deliver_of_running _ _ _ _ _
    ⟨[], [], .left, [], .running, [], [], none, none⟩
    (by rw [unframe_encPair_encBits]; rfl) rfl
    (by rw [dropFrame_encPair_encBits]; simp [Protocol.TooLong, Protocol.ofStep])]
  dsimp only [Protocol.ofStep]
  simp only [unframe_encPair_encBits, dropFrame_encPair_encBits, List.length_nil,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, PMF.pure_map, ↓reduceIte,
    zeroReplyExpected, zeroReplyPrefix_append_eq, zeroReplyPrefix_length_add]
  simp [List.take_of_length_le]

/-- In Experiment 1, `constKeyAttack` outputs `true` with probability at most `1 / 2 ^ n` for
every partner function `pf`. -/
theorem eval_run_some_constKeyAttack_le (pf : PartnerFunction) (n : ℕ) :
    ProbComp.eval (constKeyProtocol.run (some { partner := pf n }) constKeyAttack n) true ≤
      (1 : ENNReal) / 2 ^ n := by
  unfold constKeyProtocol constKeyAttack
  rw [eval_ofStep_threeStep]
  rw [challenger_deliver_of_running _ _ _ _ _
    ⟨[], [], .left, [], .running, [], [], none, none⟩
    (by rw [unframe_encPair_encBits]; rfl) rfl
    (by rw [dropFrame_encPair_encBits]; simp [Protocol.TooLong, Protocol.ofStep])]
  dsimp only [Protocol.ofStep]
  simp only [unframe_encPair_encBits, dropFrame_encPair_encBits, List.length_nil,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, PMF.map_bind, PMF.pure_map,
    ↓reduceIte, List.singleton_append, zeroReplyExpected, zeroReplyPrefix_append_eq,
    zeroReplyPrefix_length_add]
  have htake : (encDeliverReply ⟨[], .finished, [], none⟩).take
      ((encDeliverReply ⟨[], .finished, [], some (List.replicate n false)⟩).length + 1) =
      encDeliverReply ⟨[], .finished, [], none⟩ := by
    apply List.take_of_length_le
    rw [encDeliverReply_some]
    simp
  have hne : encDeliverReply ⟨[], .finished, [], none⟩ ≠
      encDeliverReply ⟨[], .finished, [], some (List.replicate n false)⟩ :=
    fun h => by injection encDeliverReply.injective h with _ _ _ hopt; cases hopt
  cases hc : pf n [LogEntry.init 0 .left, LogEntry.deliver 0 [] [] .finished] with
  | vulnerable =>
    simp only [effectiveKey, Challenger.isCorrupt, List.contains_nil, Bool.false_or,
      Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure, PMF.pure_bind]
    rw [htake, beq_false_of_ne hne]
    simp
  | connected peer =>
    cases peer with
    | zero =>
      simp only [effectiveKey, List.set_cons_zero, List.getElem?_cons_zero, reduceCtorEq,
        and_false, false_and, ↓reduceIte, ProbComp.eval_pure, PMF.pure_bind]
      rw [htake, beq_false_of_ne hne]
      simp
    | succ k =>
      simp only [effectiveKey, List.set_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
        ProbComp.eval_pure, PMF.pure_bind]
      rw [htake, beq_false_of_ne hne]
      simp
  | fresh =>
    simp only [effectiveKey, Challenger.isRegistered, Challenger.isHonest, Challenger.findHonest,
      List.find?_cons_of_pos, beq_self_eq_true, Option.isSome_some, Bool.true_or, ↓reduceIte,
      ProbComp.eval_map, BitString.eval_sampleList]
    rw [PMF.bind_map]
    have hmap : ((BitString.uniformList n).bind fun k => PMF.pure
        ((encDeliverReply ⟨[], .finished, [], some k⟩).take
          ((encDeliverReply ⟨[], .finished, [], some (List.replicate n false)⟩).length + 1) ==
          encDeliverReply ⟨[], .finished, [], some (List.replicate n false)⟩)) =
        (BitString.uniformList n).map fun k =>
          (encDeliverReply ⟨[], .finished, [], some k⟩).take
            ((encDeliverReply ⟨[], .finished, [], some (List.replicate n false)⟩).length + 1) ==
            encDeliverReply ⟨[], .finished, [], some (List.replicate n false)⟩ :=
      PMF.bind_pure_comp _ _
    dsimp only [Function.comp_def, id]
    rw [hmap]
    apply uniformList_map_true_le
    intro k₁ k₂ hk₁ hk₂ h₁ h₂
    have hle1 : (encDeliverReply ⟨[], .finished, [], some k₁⟩).length ≤
        (encDeliverReply ⟨[], .finished, [], some (List.replicate n false)⟩).length + 1 := by
      simp only [encDeliverReply_some, List.length_append, List.length_cons, hk₁,
        List.length_replicate]
      omega
    have hle2 : (encDeliverReply ⟨[], .finished, [], some k₂⟩).length ≤
        (encDeliverReply ⟨[], .finished, [], some (List.replicate n false)⟩).length + 1 := by
      simp only [encDeliverReply_some, List.length_append, List.length_cons, hk₂,
        List.length_replicate]
      omega
    rw [List.take_of_length_le hle1, beq_iff_eq] at h₁
    rw [List.take_of_length_le hle2, beq_iff_eq] at h₂
    have hi₁ := encDeliverReply.injective h₁
    have hi₂ := encDeliverReply.injective h₂
    injection hi₁ with _ _ _ ho₁
    injection hi₂ with _ _ _ ho₂
    exact (Option.some.inj ho₁).trans (Option.some.inj ho₂).symm

/-- For `1 ≤ n`, `constKeyAttack` has advantage at least `1 / 2` against `constKeyProtocol`. -/
theorem staticAdvantage_constKeyAttack_ge (pf : PartnerFunction) {n : ℕ} (hn : 1 ≤ n) :
    (1 / 2 : ℝ≥0) ≤ constKeyProtocol.staticAdvantage pf constKeyAttack n := by
  have hreal : ProbComp.eval (constKeyProtocol.run none constKeyAttack n) = PMF.pure true :=
    eval_run_none_constKeyAttack n
  have hideal := eval_run_some_constKeyAttack_le pf n
  have hle2 : (2 : ENNReal) ≤ 2 ^ n := by
    calc (2 : ENNReal) = 2 ^ 1 := by simp
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hhalf : (1 : ENNReal) / 2 ^ n ≤ 1 / 2 := by
    simpa only [one_div] using ENNReal.inv_le_inv.mpr hle2
  have hhalfToNNReal : ((1 : ENNReal) / 2).toNNReal = 1 / 2 := by
    rw [ENNReal.toNNReal_div, ENNReal.toNNReal_one, ENNReal.toNNReal_ofNat]
  have hidealHalf :
      Game.succProbability (ProbComp.eval
        (constKeyProtocol.run (some { partner := pf n }) constKeyAttack n)) ≤
        1 / 2 := by
    rw [Game.succProbability]
    exact (ENNReal.toNNReal_mono (by simp [one_div]) (hideal.trans hhalf)).trans_eq hhalfToNNReal
  rw [Protocol.staticAdvantage, hreal, Game.advantage, NNReal.nndist_eq]
  refine le_trans ?_ (le_max_left _ _)
  have h1 : Game.succProbability (PMF.pure true) = 1 := by simp [Game.succProbability]
  rw [h1]
  exact le_tsub_of_add_le_right (calc
    (1 / 2 : ℝ≥0) +
        Game.succProbability (ProbComp.eval
          (constKeyProtocol.run (some { partner := pf n }) constKeyAttack n))
      ≤ 1 / 2 + 1 / 2 := add_le_add le_rfl hidealHalf
    _ = 1 := by norm_num)

/-- `constKeyProtocol` is not statically secure. -/
theorem not_staticallySecure_constKeyProtocol : ¬ constKeyProtocol.StaticallySecure := by
  rintro ⟨pf, _, hsec⟩
  have hneg := hsec constKeyAttack isOraclePPT_constKeyAttack
  have hev := (hneg 0).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ≥0) < 1 / 2))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  have hlt := hN (max N 1) (le_max_left N 1)
  simp only [pow_zero, one_mul] at hlt
  have hge := staticAdvantage_constKeyAttack_ge pf (le_max_right N 1)
  exact not_lt_of_ge hge hlt

/-- **P2**: At security parameter `n = 0`, the session key space `{0, 1}⁰` is a singleton `{[]}`,
so `constKeyAttack` has distinguishing advantage `0` under the constant `fresh` partner
function. -/
theorem staticAdvantage_constKeyAttack_zero :
    constKeyProtocol.staticAdvantage (fun _ _ => .fresh) constKeyAttack 0 = 0 := by
  rw [Protocol.staticAdvantage, eval_run_none_constKeyAttack 0]
  suffices h :
      ProbComp.eval (constKeyProtocol.run (some { partner := fun _ => .fresh }) constKeyAttack 0) =
        PMF.pure true by
    rw [h, Game.advantage_self]
  unfold constKeyProtocol constKeyAttack
  rw [eval_ofStep_threeStep]
  rw [challenger_deliver_of_running _ _ _ _ _
    ⟨[], [], .left, [], .running, [], [], none, none⟩
    (by rw [unframe_encPair_encBits]; rfl) rfl
    (by rw [dropFrame_encPair_encBits]; simp [Protocol.TooLong, Protocol.ofStep])]
  dsimp only [Protocol.ofStep]
  simp only [unframe_encPair_encBits, dropFrame_encPair_encBits, List.length_nil,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, PMF.pure_map,
    ↓reduceIte, effectiveKey, id, Challenger.isRegistered, Challenger.isHonest,
    Challenger.findHonest, List.find?_cons_of_pos, beq_self_eq_true, Option.isSome_some,
    Bool.true_or, ProbComp.eval_map, BitString.eval_sampleList, BitString.uniformList_zero,
    zeroReplyExpected, List.replicate_zero, List.append_nil]
  have h0 : zeroReplyPrefix = encDeliverReply ⟨[], .finished, [], some []⟩ := by
    simpa using zeroReplyPrefix_append_eq 0
  rw [← h0, List.take_of_length_le (by omega), beq_self_eq_true]

/-! ### P1: Fresh finishing reply matches Experiment 0 -/

/-- **P1**: If `P.step` always finishes on input with deterministic state/message `stateOut`/
`msgOut`, partner `input.user`, and a uniform `P.keyLength input.parameter`-bit key, then on a
running instance of a registered user a `.deliver` query produces the same reply law in Experiment 0
and Experiment 1 with classification `fresh`. -/
theorem eval_challenger_deliver_fresh_reply (P : Protocol) (n : ℕ) (req : List Bool)
    (s : Challenger) (inst : Instance)
    (stateOut msgOut : StepInput → List Bool)
    (hinst : s.instances[(unframe req).length]? = some inst)
    (hphase : inst.phase = .running) (hlen : ¬ P.TooLong n (dropFrame req))
    (hreg : s.isRegistered inst.user = true)
    (hstep : ∀ input, ProbComp.eval (P.step input) =
      (BitString.uniformList (P.keyLength input.parameter)).map
        (fun k => ⟨stateOut input, msgOut input, .finished, input.user, k⟩)) :
    (ProbComp.eval (challenger P n (some { partner := fun _ => .fresh }) (.deliver, req) s)).map
        Prod.fst =
      (ProbComp.eval (challenger P n none (.deliver, req) s)).map Prod.fst := by
  rw [challenger_deliver_of_running P n _ req s inst hinst hphase hlen,
    challenger_deliver_of_running P n none req s inst hinst hphase hlen]
  simp only [ProbComp.eval_bind, hstep, PMF.map_bind, PMF.bind_map, Function.comp_def,
    ↓reduceIte, ProbComp.eval_pure, PMF.pure_map]
  trans (BitString.uniformList (P.keyLength n)).bind (fun _ =>
      (BitString.uniformList (P.keyLength n)).bind (fun k =>
        PMF.pure (encDeliverReply ⟨msgOut ⟨n, inst.user, inst.longTermKey, inst.role,
          inst.state, dropFrame req⟩, .finished, inst.user, some k⟩)))
  · refine congrArg (PMF.bind _) (funext fun k => ?_)
    simp only [effectiveKey]
    have hreg' : (⟨s.ttp, s.honest, s.corrupt, s.instances.set (unframe req).length
          ⟨inst.user, inst.longTermKey, inst.role,
            stateOut ⟨n, inst.user, inst.longTermKey, inst.role, inst.state, dropFrame req⟩,
            .finished, inst.user, k, inst.classification, inst.effectiveKey⟩,
          s.log ++ [.deliver (unframe req).length (dropFrame req)
            (msgOut ⟨n, inst.user, inst.longTermKey, inst.role, inst.state, dropFrame req⟩)
            .finished]⟩ : Challenger).isRegistered inst.user = true := hreg
    simp only [hreg', ↓reduceIte, ProbComp.eval_map, BitString.eval_sampleList, PMF.bind_map,
      Function.comp_def]
  · exact PMF.bind_const _ _

end CslibFrontierTests.Crypto.AuthenticatedKeyExchange
