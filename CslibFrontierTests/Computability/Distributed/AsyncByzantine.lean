/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Distributed.AsyncByzantine.Impossibility
import CslibFrontier.Computability.Distributed.AsyncByzantine.Bracha

/-! Asynchronous Byzantine reliable broadcast (checked as a `module` client with ordinary imports):
direct broadcast counterexample against an equivocating dealer on three processes, positive checks
for `directProtocol` (`t = 0` and `n ≤ 2`), dot-notation checks for `Reachable.*` and
`SolvesReliableBroadcast.*`, message-conservation identity `Protocol.card_msgs_add_traceSent`,
threshold arithmetic (`echoThreshold`), concrete `brachaStep` deduplication and phase execution on
`Fin 4` against an honest dealer, an honest silent dealer (`input = none`, `noSpurious`), and an
equivocating dealer with Byzantine replay flooding (`t = 1`), tight `O(n²)` message-count
accounting, `solvesReliableBroadcast_bracha` instantiations including infinite `V = ℕ`,
impossibility for `3 ≤ n ≤ 3t` including the singleton domain `V = Unit`, and the sharp
`exists_solvesReliableBroadcast_iff` threshold. -/
set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.AsyncByzantine

open Cslib Cslib.Distributed.AsyncByzantine

/-! ### Direct broadcast: valid for `t = 0` and `n ≤ 2`, broken on `Fin 3` for `t = 1` -/

example : (directProtocol (Fin 4) Bool 0).SolvesReliableBroadcast 0 :=
  solvesReliableBroadcast_direct_of_zero 0

example (t : ℕ) : (directProtocol (Fin 2) Bool 0).SolvesReliableBroadcast t :=
  solvesReliableBroadcast_direct_of_card_le_two 0 (by simp) t

/-- On `Fin 3`, a single faulty dealer `0` can equivocate directly (`true` to `1`, `false` to `2`),
violating consistency in two `byzRecv` steps. -/
theorem direct_fin3_equivocation_reachable :
    let π := directProtocol (Fin 3) Bool 0
    let s₀ := π.start {0} none
    let s₁ := π.recvByz 0 1 true s₀
    let s₂ := π.recvByz 0 2 false s₁
    π.Reachable {0} none s₂ ∧ s₂.ProcDecided 1 true ∧ s₂.ProcDecided 2 false := by
  intro π s₀ s₁ s₂
  have h01 : (π.lts {0}).Tr s₀ (.byzRecv 0 1 true) s₁ := ⟨by decide, by decide, rfl⟩
  have h12 : (π.lts {0}).Tr s₁ (.byzRecv 0 2 false) s₂ := ⟨by decide, by decide, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨[.byzRecv 0 1 true, .byzRecv 0 2 false],
      LTS.MTr.stepL h01 (LTS.MTr.stepL h12 LTS.MTr.refl)⟩
  · simp [s₂, s₁, s₀, π, State.ProcDecided, Protocol.recvByz, Protocol.recvCore,
      Protocol.updateProc, Protocol.start, directProtocol]
  · simp [s₂, s₁, s₀, π, State.ProcDecided, Protocol.recvByz, Protocol.recvCore,
      Protocol.updateProc, Protocol.start, directProtocol]

example : ¬ (directProtocol (Fin 3) Bool 0).SolvesReliableBroadcast 1 := by
  intro h
  obtain ⟨hr, h1, h2⟩ := direct_fin3_equivocation_reachable
  have heq := h.consistency {0} (by decide) none _ hr 1 (by decide) 2 (by decide) true false h1 h2
  cases heq

-- `card_msgs_add_traceSent` conservation on a concrete fault-free `directProtocol` trace on
-- `Fin 3`: 3 initial messages are emitted, 2 are delivered, leaving 1 in flight (`3 + 0 = 1 + 2`).
example :
    let π := directProtocol (Fin 3) Bool 0
    let xl : List (Action (Fin 3) Bool) :=
      [.deliver ⟨0, 0, true⟩, .deliver ⟨0, 1, true⟩]
    let s₀ := π.start ∅ (some true)
    let s₁ := π.recvHonest ⟨0, 0, true⟩ s₀
    let s₂ := π.recvHonest ⟨0, 1, true⟩ s₁
    s₀.msgs.card + π.traceSent s₀ xl = s₂.msgs.card + xl.countP Action.isDeliver ∧
    π.sentInTrace ∅ (some true) xl = 3 ∧
    s₂.msgs.card = 1 ∧
    s₂.ProcDecided 0 true ∧ s₂.ProcDecided 1 true ∧ (s₂.proc 2).out = none := by
  intro π xl s₀ s₁ s₂
  have h01 : (π.lts ∅).Tr s₀ (.deliver ⟨0, 0, true⟩) s₁ := by
    refine ⟨?_, by decide, rfl⟩; decide
  have h12 : (π.lts ∅).Tr s₁ (.deliver ⟨0, 1, true⟩) s₂ := by
    refine ⟨?_, by decide, rfl⟩; decide
  have hcons := π.card_msgs_add_traceSent (LTS.MTr.stepL h01 (LTS.MTr.stepL h12 LTS.MTr.refl))
  exact ⟨hcons, by decide, by decide, by decide, by decide, by decide⟩

-- Dot-notation usability outside `namespace Protocol` (`Reachable.*`, `SolvesReliableBroadcast.*`).
example {P S M V : Type*} {dealer : P} [Fintype P] [DecidableEq P] [DecidableEq M]
    {π : Protocol P S M V dealer} {F : Finset P} {input : Option V} {s : State P S M V}
    (hr : π.Reachable F input s) {e : Envelope P M} (he : e ∈ s.msgs) :
    e.src ∉ F ∧ π.Reachable F input s :=
  ⟨hr.msgs_src_notMem he, hr.trans (LTS.CanReach.refl (π.lts F) s)⟩

example {P S M V : Type*} {dealer : P} [Fintype P] [DecidableEq P] [DecidableEq M]
    {π : Protocol P S M V dealer} {t : ℕ} (hsol : π.SolvesReliableBroadcast t)
    {F : Finset P} (hF : F.card ≤ t) {input : Option V} {s : State P S M V}
    (hr : π.Reachable F input s) {i j : P} (hi : i ∉ F) (hj : j ∉ F) {v₁ v₂ : V}
    (h₁ : s.ProcDecided i v₁) (h₂ : s.ProcDecided j v₂) : v₁ = v₂ := by
  obtain ⟨ss, xs, k, ha, hsk, _⟩ := hr.exists_admissibleRun
  exact hsol.consistency_admissible hF ha hi hj (hsk.symm ▸ h₁) (hsk.symm ▸ h₂)

/-! ### Echo quorum threshold arithmetic -/

example : echoThreshold 1 0 = 1 := rfl
example : echoThreshold 4 1 = 3 := rfl
example : echoThreshold 5 1 = 4 := rfl
example : echoThreshold 7 2 = 5 := rfl
example : echoThreshold 10 3 = 7 := rfl

/-! ### Helper: driving local `brachaStep` and LTS traces -/

private def runLocal {n : ℕ} (dealer : Fin n) (t : ℕ) (st : BrachaState (Fin n) Bool)
    (events : List (Fin n × BrachaMsg Bool)) : BrachaState (Fin n) Bool × Option Bool :=
  events.foldl
    (fun (acc : BrachaState (Fin n) Bool × Option Bool) ev =>
      let r := brachaStep dealer t acc.1 ev.1 ev.2
      (r.nextState, acc.2.or r.delivered))
    (st, none)

-- First `initial true` from dealer `0` triggers `echo true` to all 4 processes; a duplicate
-- `initial false` from `0` (equivocation) or from non-dealer `1` is ignored with zero output.
example :
    let st0 := brachaInit (Fin 4) Bool
    let r1 := brachaStep (0 : Fin 4) 1 st0 0 (.initial true)
    let rDup := brachaStep (0 : Fin 4) 1 r1.nextState 0 (.initial false)
    let rNonDealer := brachaStep (0 : Fin 4) 1 st0 1 (.initial false)
    r1.nextState.sentEcho = some true ∧
    r1.outgoing = broadcastAll (Fin 4) (.echo true) ∧
    rDup.nextState.sentEcho = some true ∧
    rDup.outgoing = 0 ∧
    rNonDealer.nextState.sentEcho = none ∧
    rNonDealer.outgoing = 0 := by
  decide

-- Equivocation and replay deduplication: receiving `echo false` then `echo true` from the same
-- faulty sender `0` records only the first value (`false`), and sending two `echo true` messages
-- from the same sender `1` never raises the distinct-sender count to 3.
example :
    let st0 := brachaInit (Fin 4) Bool
    let s1 := runLocal (0 : Fin 4) 1 st0
      [(0, .echo false), (0, .echo true), (1, .echo true), (1, .echo true)]
    s1.1.echoFrom 0 = some false ∧
    s1.1.echoFrom 1 = some true ∧
    (echoSenders s1.1 true).card = 1 ∧
    s1.1.sentReady = none := by
  decide

-- Exact thresholds on `Fin 4`, `t = 1` (`echoThreshold 4 1 = 3`, amplification `t + 1 = 2`,
-- delivery `2 * t + 1 = 3`): 2 echoes do not trigger `ready`, the 3rd echo does; 2 readies do not
-- deliver, the 3rd ready delivers.
example :
    let st0 := brachaInit (Fin 4) Bool
    let after2Echo := runLocal (0 : Fin 4) 1 st0 [(0, .echo true), (1, .echo true)]
    let after3Echo := runLocal (0 : Fin 4) 1 st0
      [(0, .echo true), (1, .echo true), (2, .echo true)]
    let after2Ready := runLocal (0 : Fin 4) 1 after3Echo.1
      [(0, .ready true), (1, .ready true)]
    let after3Ready := runLocal (0 : Fin 4) 1 after3Echo.1
      [(0, .ready true), (1, .ready true), (2, .ready true)]
    after2Echo.1.sentReady = none ∧
    after3Echo.1.sentReady = some true ∧
    after2Ready.2 = none ∧
    after3Ready.2 = some true := by
  decide

-- Ready amplification against an equivocating dealer (`Fin 4`, `t = 1`): process `3` first
-- received `initial false` (so `sentEcho = some false`), yet upon receiving `t + 1 = 2` distinct
-- `ready true` messages (from `0` and `1`), it amplifies by setting `sentReady = some true`, and
-- upon receiving the 3rd `ready true` (from `2`), it delivers `true`.
example :
    let st0 := brachaInit (Fin 4) Bool
    let afterInit := runLocal (0 : Fin 4) 1 st0 [(0, .initial false)]
    let after1Ready := runLocal (0 : Fin 4) 1 afterInit.1 [(0, .ready true)]
    let after2Ready := runLocal (0 : Fin 4) 1 afterInit.1 [(0, .ready true), (1, .ready true)]
    let after3Ready := runLocal (0 : Fin 4) 1 afterInit.1
      [(0, .ready true), (1, .ready true), (2, .ready true)]
    afterInit.1.sentEcho = some false ∧
    after1Ready.1.sentReady = none ∧
    after2Ready.1.sentReady = some true ∧
    after2Ready.2 = none ∧
    after3Ready.2 = some true := by
  decide

/-! ### Full LTS traces on `Fin 4`, `t = 1` (`module`-checked `decide`) -/

private def execState {P S M V : Type*} {dealer : P} [DecidableEq P] [DecidableEq M]
    (π : Protocol P S M V dealer) (s : State P S M V) :
    List (Action P M) → State P S M V
  | [] => s
  | .deliver e :: xl => execState π (π.recvHonest e s) xl
  | .byzRecv src dest body :: xl => execState π (π.recvByz src dest body s) xl
  | .stutter :: xl => execState π s xl

private def validStepBool {P S M V : Type*} {dealer : P} [DecidableEq P] [DecidableEq M]
    (_π : Protocol P S M V dealer) (F : Finset P) (s : State P S M V) :
    Action P M → Bool
  | .deliver e => decide (e ∈ s.msgs ∧ e.dest ∉ F)
  | .byzRecv src dest _ => decide (src ∈ F ∧ dest ∉ F)
  | .stutter => true

private lemma mTr_of_validTraceBool {P S M V : Type*} {dealer : P}
    [DecidableEq P] [DecidableEq M]
    (π : Protocol P S M V dealer) (F : Finset P)
    (s : State P S M V) (xl : List (Action P M)) :
    (xl.foldl (fun (acc : Bool × State P S M V) a =>
      (acc.1 && validStepBool π F acc.2 a,
        match a with
        | .deliver e => π.recvHonest e acc.2
        | .byzRecv src dest body => π.recvByz src dest body acc.2
        | .stutter => acc.2)) (true, s)).1 = true →
    (π.lts F).MTr s xl (execState π s xl) := by
  induction xl generalizing s with
  | nil => intro _; exact LTS.MTr.refl
  | cons a xl ih =>
    intro h
    simp only [List.foldl_cons, Bool.true_and] at h
    have hfold : ∀ (b : Bool) (st : State P S M V) (xs : List (Action P M)),
        (xs.foldl (fun (acc : Bool × State P S M V) x =>
          (acc.1 && validStepBool π F acc.2 x,
            match x with
            | .deliver e => π.recvHonest e acc.2
            | .byzRecv src dest body => π.recvByz src dest body acc.2
            | .stutter => acc.2)) (b, st)).1 = true →
        b = true := by
      intro b st xs
      induction xs generalizing b st with
      | nil => exact id
      | cons x xs ihx =>
        intro hx
        exact (Bool.and_eq_true _ _ |>.mp (ihx _ _ hx)).1
    have ha : validStepBool π F s a = true := hfold _ _ xl h
    rw [ha] at h
    cases a with
    | deliver e =>
      simp only [validStepBool, decide_eq_true_eq] at ha
      exact LTS.MTr.stepL ⟨ha.1, ha.2, rfl⟩ (ih (π.recvHonest e s) h)
    | byzRecv src dest body =>
      simp only [validStepBool, decide_eq_true_eq] at ha
      exact LTS.MTr.stepL ⟨ha.1, ha.2, rfl⟩ (ih (π.recvByz src dest body s) h)
    | stutter =>
      exact LTS.MTr.stepL rfl (ih s h)

-- 1. Fault-free `Fin 4` trace: all 4 processes deliver `true`, `sentInTrace = 36` meets the
-- upper bound `4 + 2 * (4 - 0) * 4` tightly, and `card_msgs_add_traceSent` conserves `36 = 8 + 28`.
private def brachaFin4NormalTrace : List (Action (Fin 4) (BrachaMsg Bool)) :=
  (List.finRange 4).map (fun p => .deliver ⟨0, p, .initial true⟩) ++
  (List.finRange 4).flatMap (fun p =>
    [0, 1, 2].map (fun s => .deliver ⟨s, p, .echo true⟩)) ++
  (List.finRange 4).flatMap (fun p =>
    [0, 1, 2].map (fun s => .deliver ⟨s, p, .ready true⟩))

theorem bracha_fin4_normal_trace_valid :
    let π := brachaProtocol (Fin 4) Bool 0 1
    (π.lts ∅).MTr (π.start ∅ (some true)) brachaFin4NormalTrace
      (execState π (π.start ∅ (some true)) brachaFin4NormalTrace) := by
  apply mTr_of_validTraceBool
  decide

example :
    let π := brachaProtocol (Fin 4) Bool 0 1
    let sFinal := execState π (π.start ∅ (some true)) brachaFin4NormalTrace
    (∀ p : Fin 4, sFinal.ProcDecided p true) ∧
    π.sentInTrace ∅ (some true) brachaFin4NormalTrace =
      4 + 2 * (4 - (∅ : Finset (Fin 4)).card) * 4 ∧
    sFinal.msgs.card = 8 ∧
    brachaFin4NormalTrace.countP Action.isDeliver = 28 := by
  decide

example :
    let π := brachaProtocol (Fin 4) Bool 0 1
    let sFinal := execState π (π.start ∅ (some true)) brachaFin4NormalTrace
    π.sentInTrace ∅ (some true) brachaFin4NormalTrace =
      sFinal.msgs.card + brachaFin4NormalTrace.countP Action.isDeliver :=
  (brachaProtocol (Fin 4) Bool 0 1).card_msgs_add_traceSent bracha_fin4_normal_trace_valid

-- 2. Honest silent dealer (`input = none`, `F = {1}`): faulty process `1` floods `initial`, `echo`,
-- and `ready` messages to every correct process `{0, 2, 3}`; no authentic envelope is emitted
-- (`sentInTrace = 0`) and no correct process ever sets `sentEcho`, `sentReady`, or `out`.
private def brachaFin4SilentAttackTrace : List (Action (Fin 4) (BrachaMsg Bool)) :=
  [0, 2, 3].flatMap fun q =>
    [ .byzRecv 1 q (.initial true)
    , .byzRecv 1 q (.initial false)
    , .byzRecv 1 q (.echo true)
    , .byzRecv 1 q (.echo false)
    , .byzRecv 1 q (.ready true)
    , .byzRecv 1 q (.ready false) ]

theorem bracha_fin4_silent_attack_valid :
    let π := brachaProtocol (Fin 4) Bool 0 1
    (π.lts {1}).MTr (π.start {1} none) brachaFin4SilentAttackTrace
      (execState π (π.start {1} none) brachaFin4SilentAttackTrace) := by
  apply mTr_of_validTraceBool
  decide

example :
    let π := brachaProtocol (Fin 4) Bool 0 1
    let sFinal := execState π (π.start {1} none) brachaFin4SilentAttackTrace
    (∀ p ∈ ({0, 2, 3} : Finset (Fin 4)),
      (sFinal.proc p).state.sentEcho = none ∧
      (sFinal.proc p).state.sentReady = none ∧
      (sFinal.proc p).out = none) ∧
    π.sentInTrace {1} none brachaFin4SilentAttackTrace = 0 := by
  decide

-- 3. Equivocating faulty dealer (`F = {0}`, `input = none`): `0` sends `initial true` to `{1, 2}`
-- and `initial false` to `3`, then injects `echo true` and `ready true`. Process `3` (which echoed
-- `false`!) amplifies to `ready true`, and all three correct processes deliver `true` with `24`
-- envelopes. Appending duplicate Byzantine flooding injections leaves `sentInTrace = 24`.
private def brachaFin4EquivTrace : List (Action (Fin 4) (BrachaMsg Bool)) :=
  [ .byzRecv 0 1 (.initial true)
  , .byzRecv 0 2 (.initial true)
  , .byzRecv 0 3 (.initial false)
  , .byzRecv 0 1 (.echo true)
  , .deliver ⟨1, 1, .echo true⟩
  , .deliver ⟨2, 1, .echo true⟩
  , .byzRecv 0 2 (.ready true)
  , .deliver ⟨1, 2, .ready true⟩
  , .byzRecv 0 3 (.ready true)
  , .deliver ⟨1, 3, .ready true⟩
  , .deliver ⟨1, 1, .ready true⟩
  , .deliver ⟨2, 1, .ready true⟩
  , .deliver ⟨3, 1, .ready true⟩
  , .deliver ⟨2, 2, .ready true⟩
  , .deliver ⟨3, 2, .ready true⟩
  , .deliver ⟨2, 3, .ready true⟩
  , .deliver ⟨3, 3, .ready true⟩ ]

private def brachaFin4FloodSuffix : List (Action (Fin 4) (BrachaMsg Bool)) :=
  [ .byzRecv 0 1 (.initial false)
  , .byzRecv 0 1 (.echo false)
  , .byzRecv 0 2 (.echo false)
  , .byzRecv 0 3 (.initial true)
  , .byzRecv 0 3 (.ready false)
  , .byzRecv 0 2 (.ready false) ]

theorem bracha_fin4_equiv_trace_valid :
    let π := brachaProtocol (Fin 4) Bool 0 1
    (π.lts {0}).MTr (π.start {0} none) brachaFin4EquivTrace
      (execState π (π.start {0} none) brachaFin4EquivTrace) := by
  apply mTr_of_validTraceBool
  decide

theorem bracha_fin4_equiv_flood_valid :
    let π := brachaProtocol (Fin 4) Bool 0 1
    let xl := brachaFin4EquivTrace ++ brachaFin4FloodSuffix
    (π.lts {0}).MTr (π.start {0} none) xl (execState π (π.start {0} none) xl) := by
  apply mTr_of_validTraceBool
  decide

example :
    let π := brachaProtocol (Fin 4) Bool 0 1
    let sFinal := execState π (π.start {0} none) brachaFin4EquivTrace
    (sFinal.proc 3).state.sentEcho = some false ∧
    (sFinal.proc 3).state.sentReady = some true ∧
    (sFinal.proc 1).out = some true ∧
    (sFinal.proc 2).out = some true ∧
    (sFinal.proc 3).out = some true ∧
    π.sentInTrace {0} none brachaFin4EquivTrace = 24 ∧
    π.sentInTrace {0} none (brachaFin4EquivTrace ++ brachaFin4FloodSuffix) = 24 := by
  decide

example :
    (brachaProtocol (Fin 4) Bool 0 1).sentInTrace {0} none
        (brachaFin4EquivTrace ++ brachaFin4FloodSuffix) ≤
      4 + 2 * (4 - ({0} : Finset (Fin 4)).card) * 4 := by
  simpa using brachaSentInTrace_le 0 1 {0} none bracha_fin4_equiv_flood_valid

/-! ### Correctness instantiations (including infinite value domain `ℕ`) -/

example : (brachaProtocol (Fin 1) Bool 0 0).SolvesReliableBroadcast 0 :=
  solvesReliableBroadcast_bracha (by simp)

example : (brachaProtocol (Fin 4) Bool 0 1).SolvesReliableBroadcast 1 :=
  solvesReliableBroadcast_bracha (by simp)

example : (brachaProtocol (Fin 4) ℕ 0 1).SolvesReliableBroadcast 1 :=
  solvesReliableBroadcast_bracha (by simp)

example : (brachaProtocol (Fin 7) ℕ 0 2).SolvesReliableBroadcast 2 :=
  solvesReliableBroadcast_bracha (by simp)

/-! ### Impossibility at `3 ≤ n ≤ 3t` (including singleton `Unit`) and sharp threshold -/

example {S M : Type*} [DecidableEq M] (π : Protocol (Fin 3) S M Unit 0) :
    ¬ π.SolvesReliableBroadcast 1 :=
  π.not_solvesReliableBroadcast_three

example {S M : Type*} [DecidableEq M] (π : Protocol (Fin 3) S M Bool 0) :
    ¬ π.SolvesReliableBroadcast 1 :=
  π.not_solvesReliableBroadcast_three

example {S M : Type*} [DecidableEq M] (π : Protocol (Fin 6) S M ℕ 0) :
    ¬ π.SolvesReliableBroadcast 2 :=
  π.not_solvesReliableBroadcast (by simp) (by simp)

example : ¬ (brachaProtocol (Fin 3) Unit 0 1).SolvesReliableBroadcast 1 :=
  (brachaProtocol (Fin 3) Unit 0 1).not_solvesReliableBroadcast_three

example : ∃ (S M : Type) (_ : DecidableEq M) (π : Protocol (Fin 2) S M Unit 0),
    π.SolvesReliableBroadcast 5 :=
  (exists_solvesReliableBroadcast_iff (Fin 2) Unit 0 5).2 (Or.inl (by simp))

example : ¬ ∃ (S M : Type) (_ : DecidableEq M) (π : Protocol (Fin 3) S M Unit 0),
    π.SolvesReliableBroadcast 1 := by
  rw [exists_solvesReliableBroadcast_iff]
  simp

example : ∃ (S M : Type) (_ : DecidableEq M) (π : Protocol (Fin 4) S M Bool 0),
    π.SolvesReliableBroadcast 1 :=
  (exists_solvesReliableBroadcast_iff (Fin 4) Bool 0 1).2 (Or.inr (by simp))

example : ¬ ∃ (S M : Type) (_ : DecidableEq M) (π : Protocol (Fin 6) S M ℕ 0),
    π.SolvesReliableBroadcast 2 := by
  rw [exists_solvesReliableBroadcast_iff]
  simp

example : ∃ (S M : Type) (_ : DecidableEq M) (π : Protocol (Fin 7) S M ℕ 0),
    π.SolvesReliableBroadcast 2 :=
  (exists_solvesReliableBroadcast_iff (Fin 7) ℕ 0 2).2 (Or.inr (by simp))

end CslibFrontierTests.Distributed.AsyncByzantine
