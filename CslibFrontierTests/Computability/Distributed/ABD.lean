/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Distributed.ABD.Protocol
import CslibFrontier.Computability.Distributed.ABD.Impossibility

/-! Two-phase quorum multi-writer atomic register emulation and `n > 2t` resilience threshold
(checked as a `module` client with ordinary imports): executable LTS trace stepper (`execTrace`),
concrete `decide`-checked traces on `Fin 3, t = 1` showing (a) why omitting the Phase-2 read
write-back allows a "new-old inversion" violating `Linearizable` under a slow/pending write and two
sequential reads, (b) how `abdProtocol`'s Phase-2 read write-back prevents the inversion on the
same quorum schedule (linearizing the pending write before both reads via `IsLinearization`), and
(c) concurrent multi-writer tie-breaking via lexicographic `(seq, writer)` tags; plus instantiations
of `prec_irrefl`, `prec_trans`, `quorum_inter_notMem`, `mTr_repTag_mono`,
`implementsAtomicRegister_local_of_card_le_one`, `implementsAtomicRegister_abd` (on `Bool` and
infinite `ℕ`), `not_implementsAtomicRegister`, and the universe-polymorphic
`exists_linearizableRegister_iff` characterization across `Fin 1`, `Fin 2`, `Fin 3`, and `Fin 4`. -/
set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.ABD

open Cslib Cslib.Distributed.ABD

/-! ### Executable LTS trace runner for concrete `decide` witnesses -/

/-- Execute one concrete `Action` on `s`, returning `none` if its precondition fails. -/
def execStep {P S M V : Type*} [DecidableEq P] [DecidableEq M]
    (π : Protocol P S M V) (s : State P S M V) :
    Action P M V → Option (State P S M V)
  | .invoke caller kind =>
    if (s.proc caller).pending = none then some (π.doInvoke caller kind s) else none
  | .deliver e =>
    if e ∈ s.msgs then some (π.doDeliver e s) else none
  | .stutter => some s

/-- Execute a finite list of `Action`s starting from `s`. -/
def execTrace {P S M V : Type*} [DecidableEq P] [DecidableEq M]
    (π : Protocol P S M V) :
    State P S M V → List (Action P M V) → Option (State P S M V)
  | s, [] => some s
  | s, a :: xl => (execStep π s a).bind fun s' => execTrace π s' xl

theorem tr_of_execStep {P S M V : Type*} [DecidableEq P] [DecidableEq M]
    {π : Protocol P S M V} {s s' : State P S M V} {a : Action P M V}
    (h : execStep π s a = some s') : π.lts.Tr s a s' := by
  cases a with
  | invoke caller kind =>
    simp only [execStep] at h
    split_ifs at h with hp
    cases h
    exact ⟨hp, rfl⟩
  | deliver e =>
    simp only [execStep] at h
    split_ifs at h with hm
    cases h
    exact ⟨hm, rfl⟩
  | stutter =>
    simp only [execStep, Option.some.injEq] at h
    exact h.symm

theorem mTr_of_execTrace {P S M V : Type*} [DecidableEq P] [DecidableEq M]
    {π : Protocol P S M V} {s₀ s : State P S M V} {xl : List (Action P M V)}
    (h : execTrace π s₀ xl = some s) : π.lts.MTr s₀ xl s := by
  induction xl generalizing s₀ with
  | nil =>
    simp only [execTrace, Option.some.injEq] at h
    exact h ▸ LTS.MTr.refl
  | cons a xl ih =>
    simp only [execTrace, Option.bind_eq_some_iff] at h
    obtain ⟨s₁, hs₁, hrest⟩ := h
    exact LTS.MTr.stepL (tr_of_execStep hs₁) (ih hrest)

theorem mTr_of_execTrace_isSome {P S M V : Type*} [DecidableEq P] [DecidableEq M]
    {π : Protocol P S M V} {s₀ : State P S M V} {xl : List (Action P M V)}
    (h : (execTrace π s₀ xl).isSome = true) :
    π.lts.MTr s₀ xl ((execTrace π s₀ xl).getD s₀) := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp h
  rw [hs, Option.getD_some]
  exact mTr_of_execTrace hs

theorem reachable_of_execTrace_isSome {P S M V : Type*} [Fintype P] [DecidableEq P] [DecidableEq M]
    {π : Protocol P S M V} {xl : List (Action P M V)}
    (h : (execTrace π π.start xl).isSome = true) :
    π.Reachable ((execTrace π π.start xl).getD π.start) :=
  ⟨xl, mTr_of_execTrace_isSome h⟩

/-! ### (a) Why read write-back is required: new-old inversion without Phase-2 write-back -/

/-- Flawed variant of `abdOnRecv` on `(Fin 3, Bool)` (`t = 1`, quorum size `2`) that omits the
Phase-2 read write-back: a `read` returns `bestVal'` immediately upon collecting `2` Phase-1
`queryResp` messages. -/
def noWriteBackOnRecv (dest : Fin 3) (st : ABDState (Fin 3) Bool)
    (src : Fin 3) (msg : ABDMsg (Fin 3) Bool) :
    StepOut (Fin 3) (ABDMsg (Fin 3) Bool) (ABDState (Fin 3) Bool) Bool :=
  match msg with
  | .query reqId =>
    ⟨st, {(src, .queryResp reqId st.repTag st.repVal)}, none⟩
  | .store reqId inTag inVal =>
    let st' := if st.repTag < inTag then { st with repTag := inTag, repVal := inVal } else st
    ⟨st', {(src, .ack reqId)}, none⟩
  | .queryResp rId rTag rVal =>
    match st.phase with
    | .phase1 reqId kind responses bestTag bestVal =>
      if rId = reqId then
        let responses' := insert src responses
        let bestTag' := if bestTag < rTag then rTag else bestTag
        let bestVal' := if bestTag < rTag then rVal else bestVal
        if 2 ≤ responses'.card then
          match kind with
          | .write v =>
            let chosenTag := nextWriteTag bestTag'.seq dest
            ⟨{ st with phase := .phase2 reqId kind chosenTag v ∅ },
             broadcastAll (Fin 3) (.store reqId chosenTag v),
             none⟩
          | .read =>
            -- Omitting Phase-2 write-back: return `bestVal'` immediately!
            ⟨{ st with phase := .idle }, 0, some (.readRet bestVal')⟩
        else
          ⟨{ st with phase := .phase1 reqId kind responses' bestTag' bestVal' }, 0, none⟩
      else
        ⟨st, 0, none⟩
    | _ => ⟨st, 0, none⟩
  | .ack rId =>
    match st.phase with
    | .phase2 reqId kind chosenTag chosenVal acks =>
      if rId = reqId then
        let acks' := insert src acks
        if 2 ≤ acks'.card then
          ⟨{ st with phase := .idle }, 0,
           some (match kind with | .read => .readRet chosenVal | .write _ => .writeAck)⟩
        else
          ⟨{ st with phase := .phase2 reqId kind chosenTag chosenVal acks' }, 0, none⟩
      else
        ⟨st, 0, none⟩
    | _ => ⟨st, 0, none⟩

/-- Register protocol on `Fin 3` (`v₀ = false`, `t = 1`) without read write-back. -/
def noWriteBackProtocol :
    Protocol (Fin 3) (ABDState (Fin 3) Bool) (ABDMsg (Fin 3) Bool) Bool where
  init _ := abdInit (Fin 3) false
  onInvoke := abdOnInvoke false
  onRecv := noWriteBackOnRecv

/-- Tag `(1, ↑0)` chosen by writer `0` on its first write. -/
def wTag0 : Tag (Fin 3) := nextWriteTag 0 0

/-- Shared 6-step prefix: writer `0` invokes `write true`, queries quorum `{0, 1}`, enters Phase 2
with `wTag0`, and delivers `.store` ONLY to replica `0` (leaving `write true` pending while replicas
`1` and `2` still hold `(initTag, false)`). -/
def slowWritePrefix : List (Action (Fin 3) (ABDMsg (Fin 3) Bool) Bool) :=
  [ .invoke 0 (.write true)
  , .deliver ⟨0, 0, .query 0⟩
  , .deliver ⟨0, 1, .query 0⟩
  , .deliver ⟨0, 0, .queryResp 0 (initTag (Fin 3)) false⟩
  , .deliver ⟨1, 0, .queryResp 0 (initTag (Fin 3)) false⟩
  , .deliver ⟨0, 0, .store 0 wTag0 true⟩ ]

/-- Schedule exposing new-old inversion in `noWriteBackProtocol`: after `slowWritePrefix`, reader
`1` queries `{0, 1}` and returns `true`, and strictly afterward reader `2` queries `{1, 2}` and
returns `false`. -/
def noWriteBackInversionTrace : List (Action (Fin 3) (ABDMsg (Fin 3) Bool) Bool) :=
  slowWritePrefix ++
  [ -- Reader `1` (`op 1`) queries `{0, 1}` and returns `true` without write-back:
    .invoke 1 .read
  , .deliver ⟨1, 0, .query 0⟩
  , .deliver ⟨1, 1, .query 0⟩
  , .deliver ⟨0, 1, .queryResp 0 wTag0 true⟩
  , .deliver ⟨1, 1, .queryResp 0 (initTag (Fin 3)) false⟩
  , -- Strictly after `op 1` completes, reader `2` (`op 2`) queries `{1, 2}` and returns `false`:
    .invoke 2 .read
  , .deliver ⟨2, 1, .query 0⟩
  , .deliver ⟨2, 2, .query 0⟩
  , .deliver ⟨1, 2, .queryResp 0 (initTag (Fin 3)) false⟩
  , .deliver ⟨2, 2, .queryResp 0 (initTag (Fin 3)) false⟩ ]

/-- Without Phase-2 read write-back, `noWriteBackInversionTrace` reaches a state where `op 1`
(`read → true`) strictly precedes `op 2` (`read → false`) in real time, violating
`Linearizable false`. -/
theorem noWriteBack_new_old_inversion :
    ∃ s, noWriteBackProtocol.Reachable s ∧
      s.history =
        [ ⟨0, .write true, 0, .pending⟩
        , ⟨1, .read, 6, .doneRead 10 true⟩
        , ⟨2, .read, 11, .doneRead 15 false⟩ ] ∧
      prec s.history 1 2 ∧
      ¬ Linearizable false s.history := by
  have hsome :
      (execTrace noWriteBackProtocol noWriteBackProtocol.start noWriteBackInversionTrace).isSome =
        true := by decide
  refine ⟨_, reachable_of_execTrace_isSome hsome, by decide, by decide, by decide⟩

example : ¬ noWriteBackProtocol.ImplementsAtomicRegister false 1 := by
  intro hImpl
  obtain ⟨s, hr, _, _, hnot⟩ := noWriteBack_new_old_inversion
  exact hnot (hImpl.linearizable s hr)

/-! ### (b) ABD's Phase-2 read write-back prevents new-old inversion on the same schedule -/

/-- Exact same quorum schedule on `abdProtocol (Fin 3) Bool false 1`: reader `1` queries `{0, 1}`,
writes `(wTag0, true)` back to `{0, 1}` before returning `true`, and subsequent reader `2` querying
`{1, 2}` observes `(wTag0, true)` at replica `1` and also returns `true`. -/
def abdWriteBackTrace : List (Action (Fin 3) (ABDMsg (Fin 3) Bool) Bool) :=
  slowWritePrefix ++
  [ -- Reader `1` (`op 1`) Phase 1 on `{0, 1}`:
    .invoke 1 .read
  , .deliver ⟨1, 0, .query 0⟩
  , .deliver ⟨1, 1, .query 0⟩
  , .deliver ⟨0, 1, .queryResp 0 wTag0 true⟩
  , .deliver ⟨1, 1, .queryResp 0 (initTag (Fin 3)) false⟩
  , -- Reader `1` Phase 2 (write-back!) on `{0, 1}`:
    .deliver ⟨1, 0, .store 0 wTag0 true⟩
  , .deliver ⟨1, 1, .store 0 wTag0 true⟩
  , .deliver ⟨0, 1, .ack 0⟩
  , .deliver ⟨1, 1, .ack 0⟩
  , -- Strictly after `op 1` completes, reader `2` (`op 2`) queries `{1, 2}` (with `0` silent):
    .invoke 2 .read
  , .deliver ⟨2, 1, .query 0⟩
  , .deliver ⟨2, 2, .query 0⟩
  , .deliver ⟨1, 2, .queryResp 0 wTag0 true⟩
  , .deliver ⟨2, 2, .queryResp 0 (initTag (Fin 3)) false⟩
  , -- Reader `2` Phase 2 write-back on `{1, 2}`:
    .deliver ⟨2, 1, .store 0 wTag0 true⟩
    , .deliver ⟨2, 2, .store 0 wTag0 true⟩
  , .deliver ⟨1, 2, .ack 0⟩
  , .deliver ⟨2, 2, .ack 0⟩ ]

/-- With ABD's write-back, both sequential reads return `true` while `op 0` (`write true`) is still
pending, and `[0, 1, 2]` is a `decide`-verified linearization. -/
theorem abd_writeBack_prevents_inversion :
    let π := abdProtocol (Fin 3) Bool false 1
    ∃ s, π.Reachable s ∧
      s.history =
        [ ⟨0, .write true, 0, .pending⟩
        , ⟨1, .read, 6, .doneRead 14 true⟩
        , ⟨2, .read, 15, .doneRead 23 true⟩ ] ∧
      prec s.history 1 2 ∧
      IsLinearization false s.history [0, 1, 2] ∧
      Linearizable false s.history := by
  intro π
  have hsome : (execTrace π π.start abdWriteBackTrace).isSome = true := by decide
  refine ⟨_, reachable_of_execTrace_isSome hsome, by decide, by decide, by decide, by decide⟩

/-! ### Concurrent multi-writer tie-breaking via lexicographic `(seq, writer)` tags -/

/-- Tag `(1, ↑1)` chosen by concurrent writer `1`. -/
def wTag1 : Tag (Fin 3) := nextWriteTag 0 1

example : initTag (Fin 3) ≤ wTag0 ∧ wTag0 < wTag1 :=
  ⟨initTag_le wTag0, by decide⟩

/-- Concurrent MWMR trace on `Fin 3, t = 1`: writer `0` (`write true`) and writer `1`
(`write false`) overlap in Phase 1, choosing sequence-`1` tags `wTag0 < wTag1`; both complete Phase
2 on `{0, 1}`, and subsequent reader `2` returns `false` (linearizing as `[0, 1, 2]`). -/
def abdConcurrentMWMRTrace : List (Action (Fin 3) (ABDMsg (Fin 3) Bool) Bool) :=
  [ -- Concurrent invocations by writers `0` and `1`:
    .invoke 0 (.write true)
  , .invoke 1 (.write false)
  , -- Both Phase-1 queries answered by `{0, 1}` with `(initTag, false)`:
    .deliver ⟨0, 0, .query 0⟩
  , .deliver ⟨0, 1, .query 0⟩
  , .deliver ⟨1, 0, .query 0⟩
  , .deliver ⟨1, 1, .query 0⟩
  , .deliver ⟨0, 0, .queryResp 0 (initTag (Fin 3)) false⟩
  , .deliver ⟨1, 0, .queryResp 0 (initTag (Fin 3)) false⟩
  , .deliver ⟨0, 1, .queryResp 0 (initTag (Fin 3)) false⟩
  , .deliver ⟨1, 1, .queryResp 0 (initTag (Fin 3)) false⟩
  , -- Writer `1` (`wTag1`) stores first on `{0, 1}`, then delayed writer `0` (`wTag0 < wTag1`)
    -- arrives at `{0, 1}` without overwriting `wTag1`:
    .deliver ⟨1, 0, .store 0 wTag1 false⟩
  , .deliver ⟨1, 1, .store 0 wTag1 false⟩
  , .deliver ⟨0, 0, .store 0 wTag0 true⟩
  , .deliver ⟨0, 1, .store 0 wTag0 true⟩
  , .deliver ⟨0, 0, .ack 0⟩
  , .deliver ⟨1, 0, .ack 0⟩
  , .deliver ⟨0, 1, .ack 0⟩
  , .deliver ⟨1, 1, .ack 0⟩
  , -- Reader `2` queries `{1, 2}`, sees `(wTag1, false)` from `1`, writes back to `{1, 2}`,
    -- and returns `false`:
    .invoke 2 .read
  , .deliver ⟨2, 1, .query 0⟩
  , .deliver ⟨2, 2, .query 0⟩
  , .deliver ⟨1, 2, .queryResp 0 wTag1 false⟩
  , .deliver ⟨2, 2, .queryResp 0 (initTag (Fin 3)) false⟩
  , .deliver ⟨2, 1, .store 0 wTag1 false⟩
  , .deliver ⟨2, 2, .store 0 wTag1 false⟩
  , .deliver ⟨1, 2, .ack 0⟩
  , .deliver ⟨2, 2, .ack 0⟩ ]

example :
    let π := abdProtocol (Fin 3) Bool false 1
    ∃ s, π.Reachable s ∧
      π.lts.MTr π.start abdConcurrentMWMRTrace s ∧
      (π.start.proc 1).state.repTag ≤ (s.proc 1).state.repTag ∧
      (s.proc 0).state.repVal = false ∧
      IsLinearization false s.history [0, 1, 2] ∧
      Linearizable false s.history := by
  intro π
  have hsome : (execTrace π π.start abdConcurrentMWMRTrace).isSome = true := by decide
  have hm := mTr_of_execTrace_isSome hsome
  refine ⟨_, ⟨abdConcurrentMWMRTrace, hm⟩, hm,
    mTr_repTag_mono hm 1, by decide, by decide, by decide⟩

/-! ### Precedence, quorum intersection, positive instantiations, and `2t + 1` threshold -/

-- `prec_irrefl` and `prec_trans` on a concrete 3-operation well-timed history.
example :
    let hist : List (OpRecord (Fin 3) Bool) :=
      [ ⟨0, .write true, 0, .doneWrite 2⟩
      , ⟨1, .read, 3, .doneRead 5 true⟩
      , ⟨2, .read, 6, .doneRead 8 true⟩ ]
    ¬ prec hist 0 0 ∧ prec hist 0 2 := by
  intro hist
  have hwf : ∀ i (hi : i < hist.length) r,
      hist[i].status.respStep? = some r → hist[i].invStep ≤ r := by decide
  exact ⟨prec_irrefl hwf 0, prec_trans hwf (j := 1) (by decide) (by decide)⟩

-- Live quorum intersection (`quorum_inter_notMem`) on `Fin 3, t = 1` with faulty `{0}`.
example : ∃ q ∈ ({1, 2} : Finset (Fin 3)) ∩ ({0, 2} : Finset (Fin 3)),
    q ∉ ({0} : Finset (Fin 3)) :=
  quorum_inter_notMem (t := 1) (by decide) (by decide) (by decide) (by decide)

-- Single-process zero-message register (`Fintype.card P ≤ 1`) tolerates arbitrary `t`.
example (t : ℕ) : (localRegisterProtocol (Fin 1) ℕ 0).ImplementsAtomicRegister 0 t :=
  implementsAtomicRegister_local_of_card_le_one (by decide) 0 t

-- Positive ABD instantiations on `Fin 3, t = 1` (`Bool` and infinite value domain `ℕ`),
-- plus monotonicity (`ImplementsAtomicRegister.mono`) and `linearizable_iff_admissible`.
example : (abdProtocol (Fin 3) Bool false 1).ImplementsAtomicRegister false 1 :=
  implementsAtomicRegister_abd (by decide) false

example : (abdProtocol (Fin 3) ℕ 42 1).ImplementsAtomicRegister 42 1 :=
  implementsAtomicRegister_abd (by decide) 42

example : (abdProtocol (Fin 3) ℕ 42 1).ImplementsAtomicRegister 42 0 :=
  (implementsAtomicRegister_abd (t := 1) (by decide) 42).mono (by decide)

example :
    ∀ (F : Finset (Fin 3)), F.card ≤ 1 →
      ∀ ss xs, (abdProtocol (Fin 3) Bool false 1).AdmissibleRun F ss xs →
        ∀ k, Linearizable false (ss k).history :=
  ((abdProtocol (Fin 3) Bool false 1).linearizable_iff_admissible false 1).mp
    (implementsAtomicRegister_abd (t := 1) (by decide) false).linearizable

-- Impossibility on `Fin 2, t = 1` and `Fin 4, t = 2`.
example {S M : Type} [DecidableEq M] (π : Protocol (Fin 2) S M Bool) :
    ¬ π.ImplementsAtomicRegister false 1 :=
  π.not_implementsAtomicRegister (by decide) (by decide) false

example {S M : Type} [DecidableEq M] (π : Protocol (Fin 4) S M ℕ) :
    ¬ π.ImplementsAtomicRegister 0 2 :=
  π.not_implementsAtomicRegister (by decide) (by decide) 0

-- Sharp resilience characterization (`exists_linearizableRegister_iff`) across `Fin 1..4`
-- and across distinct universes (`P = Fin 3 : Type`, `V = ULift.{1} Bool : Type 1`).
example : (∃ (S M : Type) (_ : DecidableEq M) (π : Protocol (Fin 1) S M Bool),
    π.ImplementsAtomicRegister false 5) :=
  (exists_linearizableRegister_iff (Fin 1) Bool false 5).mpr (Or.inl (by decide))

example : ¬ (∃ (S M : Type) (_ : DecidableEq M) (π : Protocol (Fin 2) S M Bool),
    π.ImplementsAtomicRegister false 1) := by
  rw [exists_linearizableRegister_iff]
  decide

example : (∃ (S M : Type) (_ : DecidableEq M) (π : Protocol (Fin 3) S M Bool),
    π.ImplementsAtomicRegister false 1) :=
  (exists_linearizableRegister_iff (Fin 3) Bool false 1).mpr (Or.inr (by decide))

example : ¬ (∃ (S M : Type) (_ : DecidableEq M) (π : Protocol (Fin 4) S M Bool),
    π.ImplementsAtomicRegister false 2) := by
  rw [exists_linearizableRegister_iff]
  decide

example : (∃ (S M : Type 1) (_ : DecidableEq M) (π : Protocol (Fin 3) S M (ULift.{1} Bool)),
    π.ImplementsAtomicRegister (.up false) 1) := by
  have : Nontrivial (ULift.{1} Bool) := ⟨.up false, .up true, by decide⟩
  exact (exists_linearizableRegister_iff.{0, 1} (Fin 3) (ULift.{1} Bool) (.up false) 1).mpr
    (Or.inr (by decide))

end CslibFrontierTests.Distributed.ABD
