/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Compiler
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.CountingView
public import Mathlib.Data.Set.Card
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.CallReplay

/-! # Occurrence replay for compiled query machines

Initialization writes the initial boundary and takes no choice. Every first-halting replay
from the machine's start has this deterministic prefix. At a choice boundary, a halted
replay splits after one selected pass and its continuation check, with no change to the
remaining choices or terminal configuration. The finalizer consumes no abstract choices
and emits the abstract state's verdict.

`replay_correct` and `existsUnique_replay_iff` compose these boundaries: first-halting abstract
choice traces (`FirstHalting`) correspond exactly to unique halted native occurrence traces,
with the same verdict. An initially halted source reaches the finalizer without any choice.
`branchCount_eq_encard_firstHalting` counts the first-halting traces by verdict at a sufficient
native clock. `acceptCount_eq_one_iff` specializes this count to uniqueness of accepting traces.
The full native class-equality theorem remains in #6747.
`existsUnique_accepting_replay_iff` specializes the replay correspondence to acceptance.
-/

public section

namespace Turing.NondeterministicQueryMachine.Routines

open MultiTapeTM

variable {α σ : Type} {M : NondeterministicQueryMachine σ} {start : α → σ}
  {enc : α ↪ List Bool} {S : α → ℕ} (R : Routines M start enc S)

private theorem exists_native_path_of_replay {a : α}
    {cfg final : Cfg R.k Bool (Native.State R.SI R.SP R.SF) (enc a)}
    {indices : List ℕ} {bits : List Bool}
    (hr : Native.replayChoices R.I R.P R.F R.C cfg indices = some (bits, final)) :
    ∃ p : R.machine.RunPath (enc a),
      p.head = cfg ∧ p.last = final ∧ p.length = indices.length := by
  have hrun : (Native.countingMachine R.I R.P R.F R.C).runBranch cfg indices = some final :=
    (Native.map_snd_replayChoices ..).symm.trans (congrArg (Option.map Prod.snd) hr)
  let statement (N : MultiTapeNTM R.k Bool (Native.State R.SI R.SP R.SF)) : Prop :=
    ∃ p : RelSeries (N.runningStepRel (enc a)),
      p.head = cfg ∧ p.last = final ∧ p.length = indices.length
  obtain ⟨p, hhead, hlast, hlen⟩ := (congrArg statement
    (Native.toNTM_countingMachine R.I R.P R.F R.C)).mp
      ((Native.countingMachine R.I R.P R.F R.C).exists_runningPath_of_runBranch hrun)
  exact ⟨p.map ⟨id, fun h => h.2⟩, hhead, hlast, hlen⟩

/-- Initialization computes and checks the continuation flag with one fixed sequence of zero
occurrence indices, recording no choices. It reaches the finalizer for an initially halted
source and the choice boundary otherwise. Every first-halting replay has this exact prefix. -/
theorem init_replay (a : α) :
    ∃ n,
      let initial := R.machine.initCfg (enc a)
      let boundary := wordsCfg (enc a) (some (if M.halted (start a) then
          (.finish R.F.q₀ : Native.State R.SI R.SP R.SF) else .choose))
        (R.boundary (start a) (!M.halted (start a))) []
      Native.replayChoices R.I R.P R.F R.C initial (List.replicate n 0) = some ([], boundary) ∧
        ∀ (indices : List ℕ) (bits : List Bool)
          (final : Cfg R.k Bool (Native.State R.SI R.SP R.SF) (enc a)), final.Halted →
          (Native.replayChoices R.I R.P R.F R.C initial indices = some (bits, final) ↔
            ∃ rest, indices = List.replicate n 0 ++ rest ∧
              Native.replayChoices R.I R.P R.F R.C boundary rest = some (bits, final)) := by
  obtain ⟨t, ht⟩ := R.initial_spec a
  obtain ⟨ws, e, ⟨hws, he⟩, q₀, hqhead, hqlast, _, _⟩ := ht _ _ [] ⟨rfl, rfl⟩
  obtain ⟨q, hhead', hlast', _, _⟩ := q₀.exists_running (by rw [hqlast]; rfl)
  let f : (R.I.runningStepRel (enc a)).Hom (R.machine.runningStepRel (enc a)) :=
    ⟨Cfg.mapState Native.initState, fun h =>
      ⟨by change Native.initState _ ≠ none; simp [Native.initState],
        (Native.initHom R.I R.P R.F R.C).map_rel' h⟩⟩
  let p := q.map f
  have hhead : p.head = R.machine.initCfg (enc a) := by
    change _ = Cfg.init (.init R.I.q₀ : Native.State R.SI R.SP R.SF) (enc a)
    simp [p, f, hhead', hqhead, Native.initState, wordsCfg, Cfg.mapState]
  have hlast : p.last = wordsCfg (enc a) (some .check)
      (R.boundary (start a) (!M.halted (start a))) [] := by
    simp [p, f, hlast', hqlast, Native.initState, hws, he]
  have hprefix := Native.replayChoices_replicate_zero R.I R.P R.F R.C p fun i => by
    change Native.initState (q i.castSucc).state ≠ some Native.State.choose
    rcases hstate : (q i.castSucc).state with _ | s
    · exact ((q.step i).1 hstate).elim
    · simp [Native.initState]
  rw [hhead, hlast] at hprefix
  have hstep : R.machine.Step
      (wordsCfg (enc a) (some .check) (R.boundary (start a) (!M.halted (start a))) [])
      (wordsCfg (enc a) (some (if M.halted (start a) then .finish R.F.q₀ else .choose))
        (R.boundary (start a) (!M.halted (start a))) []) := by
    refine (Native.step_iff R.I R.P R.F R.C).mpr ⟨false, ?_⟩
    rw [Native.step_check_words R.I R.P R.F R.C false, R.boundary_flag]
    cases M.halted (start a) <;> simp [flagWord]
  have hroute := Native.replayChoices_step_zero R.I R.P R.F R.C (by simp)
    (by simp [Cfg.Halted, wordsCfg]) hstep []
  have hprefix' : Native.replayChoices R.I R.P R.F R.C (R.machine.initCfg (enc a))
      (List.replicate (p.length + 1) 0) =
      some ([], wordsCfg (enc a)
        (some (if M.halted (start a) then .finish R.F.q₀ else .choose))
        (R.boundary (start a) (!M.halted (start a))) []) := by
    rw [List.replicate_add, Native.replayChoices_append, hprefix]
    simp only [Option.bind, List.replicate_one, hroute, Native.replayChoices_nil,
      Option.map_some, List.nil_append]
  refine ⟨p.length + 1, hprefix', fun indices bits final hhalt => ⟨?_, ?_⟩⟩
  · intro hr
    obtain ⟨full, hfullhead, hfulllast, hfulllen⟩ := R.exists_native_path_of_replay hr
    have hlen : (List.replicate (p.length + 1) 0).length ≤ indices.length := by
      simp only [List.length_replicate, ← hfulllen]
      by_contra! hshort
      have hmap : full.head = q.head.mapState Native.initState := by
        simpa [p, f] using hfullhead.trans hhead.symm
      have heq := Native.follows_init R.I R.P R.F R.C full q hmap full.length
        (Nat.lt_succ_self _) (by simp [p] at hshort; omega)
      exact Option.some_ne_none _ ((congrArg Cfg.state (heq.symm.trans hfulllast)).trans hhalt)
    exact Native.exists_suffix_of_replayChoices R.I R.P R.F R.C hprefix'
      (by simpa only [List.nil_append] using hr) hlen
  · rintro ⟨rest, rfl, hrest⟩
    rw [Native.replayChoices_append, hprefix']
    simp [hrest, Option.bind]

/-- The finalizer has a halted occurrence replay with no choices. Every halted replay
from this boundary consumes no genuine choices and emits the abstract verdict. -/
theorem finish_replay (a : α) (s : σ)
    (hs : (M.withInit (start a)).Reachable (enc a) s) (flag : Bool) (out : List Bool) :
    let initial := wordsCfg (enc a)
      (some (.finish R.F.q₀ : Native.State R.SI R.SP R.SF)) (R.boundary s flag) out
    (∃ indices final, Native.replayChoices R.I R.P R.F R.C initial indices =
      some ([], final) ∧ final.Halted) ∧
      ∀ indices bits final, Native.replayChoices R.I R.P R.F R.C initial indices =
        some (bits, final) → final.Halted →
          bits = [] ∧ final.output = out ++ [M.accept s] := by
  let initial : Cfg R.k Bool (Native.State R.SI R.SP R.SF) (enc a) :=
    wordsCfg (enc a) (some (.finish R.F.q₀)) (R.boundary s flag) out
  obtain ⟨t, ht⟩ := R.final_spec a s hs flag
  obtain ⟨ws', e, he, q₀, hqhead, hqlast, _, _⟩ := ht _ _ out ⟨rfl, rfl⟩
  obtain ⟨q, hhead', hlast', _, _⟩ := q₀.exists_running (by rw [hqlast]; rfl)
  let f : (R.F.runningStepRel (enc a)).Hom (R.machine.runningStepRel (enc a)) :=
    ⟨Cfg.mapState Native.finishState, fun h =>
      ⟨fun hh => h.1 (Option.map_eq_none_iff.mp hh),
        (Native.finishHom R.I R.P R.F R.C).map_rel' h⟩⟩
  let q' := q.map f
  have hhead : q'.head = initial := by
    simp [q', f, initial, hhead', hqhead, Native.finishState]
  have hlast : q'.last = wordsCfg (enc a) none ws' (out ++ [M.accept s]) := by
    simp [q', f, hlast', hqlast, Native.finishState, he]
  have hdet := Native.replayChoices_replicate_zero R.I R.P R.F R.C q' fun i => by
    change Option.map Native.State.finish (q i.castSucc).state ≠ some Native.State.choose
    cases (q i.castSucc).state <;> simp
  rw [hhead] at hdet
  refine ⟨⟨List.replicate q'.length 0, q'.last, hdet, hlast ▸ rfl⟩, ?_⟩
  intro indices bits final hr hhalt
  obtain ⟨p, hphead, hplast, hplen⟩ := R.exists_native_path_of_replay hr
  have hlong : q.length ≤ indices.length := by
    by_contra! hshort
    have hmap : p.head = q.head.mapState Native.finishState := by
      simpa [q', f] using hphead.trans hhead.symm
    have h := Native.follows_finish R.I R.P R.F R.C p q hmap p.length
      (Nat.lt_succ_self _) (by omega)
    exact (q.step ⟨p.length, by omega⟩).1 (Option.map_eq_none_iff.mp
      ((congrArg Cfg.state (h.symm.trans hplast)).trans hhalt))
  obtain ⟨rest, _, hrest⟩ :=
    Native.exists_suffix_of_replayChoices R.I R.P R.F R.C hdet hr (by simpa [q'] using hlong)
  have htail := congrArg (Option.map Prod.snd) hrest
  rw [Native.map_snd_replayChoices] at htail
  have hqhalt : q'.last.Halted := hlast ▸ rfl
  rcases rest with _ | ⟨j, rest⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (Native.replayChoices_nil .. ▸ hrest))
    exact ⟨rfl, by simp [hlast]⟩
  · simp [MultiTapeCTM.runBranch_of_halted _ hqhalt] at htail

/-- One selected native pass records its selector and updates the boundary according to the
abstract step. A halted replay beginning with that selector is exactly this pass, including the
deterministic continuation check, followed by a replay with the remaining choices. -/
theorem pass_replay (a : α) (s : σ)
    (hs : (M.withInit (start a)).Reachable (enc a) s) (b flag : Bool) (out : List Bool) :
    let initial := wordsCfg (enc a) (some (.choose : Native.State R.SI R.SP R.SF))
      (R.boundary s flag) out
    let next := M.step (enc a) s b
    let boundary := wordsCfg (enc a) (some (if M.halted next then
      (.finish R.F.q₀ : Native.State R.SI R.SP R.SF) else .choose))
      (R.boundary next (!M.halted next)) out
    ∃ first, Native.replayChoices R.I R.P R.F R.C initial first = some ([b], boundary) ∧
      ∀ (indices : List ℕ) (bits : List Bool)
        (final : Cfg R.k Bool (Native.State R.SI R.SP R.SF) (enc a)), final.Halted →
        (Native.replayChoices R.I R.P R.F R.C initial indices = some (b :: bits, final) ↔
          ∃ rest, indices = first ++ rest ∧
            Native.replayChoices R.I R.P R.F R.C boundary rest = some (bits, final)) := by
  dsimp only
  set initial := wordsCfg (enc a) (some (.choose : Native.State R.SI R.SP R.SF))
    (R.boundary s flag) out
  set boundary := wordsCfg (enc a)
    (some (if M.halted (M.step (enc a) s b) then
      (.finish R.F.q₀ : Native.State R.SI R.SP R.SF) else .choose))
    (R.boundary (M.step (enc a) s b) (!M.halted (M.step (enc a) s b))) out
  obtain ⟨t, ht⟩ := R.pass_spec a s hs b flag
  obtain ⟨ws', e, ⟨hws, he⟩, q₀, hqhead, hqlast, _, _⟩ := ht _ _ out ⟨rfl, rfl⟩
  obtain ⟨q, hhead', hlast', _, _⟩ := q₀.exists_running (by rw [hqlast]; rfl)
  let f : ((R.P b).runningStepRel (enc a)).Hom (R.machine.runningStepRel (enc a)) :=
    ⟨Cfg.mapState (Native.passState b), fun h =>
      ⟨by change some _ ≠ none; simp, (Native.passHom R.I R.P R.F R.C b).map_rel' h⟩⟩
  let p := q.map f
  have hphead : p.head = wordsCfg (enc a) (some (.pass b (R.P b).q₀))
      (R.boundary s flag) out := by simp [p, f, hhead', hqhead, Native.passState]
  have hplast : p.last = wordsCfg (enc a) (some .check) ws' out := by
    simp [p, f, hlast', hqlast, Native.passState, he]
  have hp := Native.replayChoices_replicate_zero R.I R.P R.F R.C p fun i => by
    change some ((q i.castSucc).state.elim Native.State.check (Native.State.pass b)) ≠
      some Native.State.choose
    cases (q i.castSucc).state <;> simp
  have hstep : R.machine.Step p.last
      (wordsCfg (enc a) (some (if ws' R.C = [] then .finish R.F.q₀ else .choose)) ws' out) :=
    hplast ▸ (Native.step_iff R.I R.P R.F R.C).mpr
      ⟨false, Native.step_check_words R.I R.P R.F R.C false ws' out⟩
  have hcheck := Native.replayChoices_step_zero R.I R.P R.F R.C (by simp [hplast])
    (by simp [hplast, Cfg.Halted, wordsCfg]) hstep []
  let first := b.toNat :: (List.replicate p.length 0 ++ [0])
  have hfirst : Native.replayChoices R.I R.P R.F R.C initial first = some ([b], boundary) := by
    dsimp only [initial, boundary, first]
    rw [Native.replayChoices_choose _ _ _ _ _ rfl, withState_wordsCfg, ← hphead,
      Native.replayChoices_append, hp]
    simp only [Option.bind, hcheck, Native.replayChoices_nil, Option.map_some, List.nil_append]
    rw [hws, R.boundary_flag]
    cases M.halted (M.step (enc a) s b) <;> simp [flagWord]
  refine ⟨first, hfirst, fun indices bits final hhalt => ⟨?_, ?_⟩⟩
  · intro hr
    have hchoose : Native.replayChoices R.I R.P R.F R.C initial [b.toNat] =
        some ([b], p.head) := by
      rw [Native.replayChoices_choose _ _ _ _ _ rfl, withState_wordsCfg, ← hphead,
        Native.replayChoices_nil, Option.map_some]
    have hnonempty : indices ≠ [] := fun h => by simp [h, Native.replayChoices_nil] at hr
    obtain ⟨tail, hindices, htail⟩ := Native.exists_suffix_of_replayChoices R.I R.P R.F R.C
      hchoose (show _ = some ([b] ++ bits, final) from hr)
      (List.length_pos_iff.mpr hnonempty)
    obtain ⟨full, hfullhead, hfulllast, hfulllen⟩ := R.exists_native_path_of_replay htail
    have hpass : q.length < full.length := by
      by_contra! hshort
      have heq := Native.follows_pass R.I R.P R.F R.C b full q hfullhead full.length
        (Nat.lt_succ_self _) (by omega)
      exact Option.some_ne_none _ ((congrArg Cfg.state (heq.symm.trans hfulllast)).trans hhalt)
    have hlen : first.length ≤ indices.length := by
      simp only [hindices, first, p, List.length_cons, List.length_append, List.length_replicate,
        List.length_nil, RelSeries.map_length]
      omega
    exact Native.exists_suffix_of_replayChoices R.I R.P R.F R.C hfirst
      (show _ = some ([b] ++ bits, final) from hr) hlen
  · rintro ⟨rest, rfl, hrest⟩
    simp [Native.replayChoices_append, hfirst, hrest, Option.bind]


private theorem choose_replay_correct (a : α) (bits : List Bool) (s : σ)
    (hs : (M.withInit (start a)).Reachable (enc a) s) (hlive : M.halted s = false)
    (flag : Bool) (out : List Bool) {indices : List ℕ}
    {final : Cfg R.k Bool (Native.State R.SI R.SP R.SF) (enc a)}
    (hr : Native.replayChoices R.I R.P R.F R.C
      (wordsCfg (enc a) (some .choose) (R.boundary s flag) out) indices = some (bits, final))
    (hhalt : final.Halted) :
    M.FirstHalting (enc a) bits s ∧
      final.output = out ++ [M.accept (M.replay (enc a) bits s)] := by
  induction bits generalizing s flag out indices final with
  | nil => exact (Native.replayChoices_choose_ne_nil R.I R.P R.F R.C rfl hr hhalt rfl).elim
  | cons b bits ih =>
    obtain ⟨_, _, hfactor⟩ := R.pass_replay a s hs b flag out
    obtain ⟨rest, _, hrest⟩ := (hfactor indices bits final hhalt).mp hr
    have hs' := Reachable.step (M.withInit (start a)) (enc a) hs b
    cases hn : M.halted (M.step (enc a) s b) with
    | false =>
      have hi := ih (M.step (enc a) s b) hs' hn true out (by simpa [hn] using hrest) hhalt
      exact ⟨(M.firstHalting_cons_iff (enc a) b bits s).mpr ⟨hlive, hi.1⟩, hi.2⟩
    | true =>
      obtain ⟨rfl, hout⟩ := (R.finish_replay a (M.step (enc a) s b) hs' false out).2 rest bits final
        (by simpa [hn] using hrest) hhalt
      exact ⟨(M.firstHalting_cons_iff (enc a) b [] s).mpr
        ⟨hlive, (M.firstHalting_iff_nil_of_halted (enc a) [] _ hn).mpr rfl⟩, hout⟩

private theorem exists_choose_replay (a : α) (bits : List Bool) (s : σ)
    (hs : (M.withInit (start a)).Reachable (enc a) s) (hlive : M.halted s = false)
    (hfirst : M.FirstHalting (enc a) bits s)
    (flag : Bool) (out : List Bool) :
    ∃ indices final, Native.replayChoices R.I R.P R.F R.C
      (wordsCfg (enc a) (some .choose) (R.boundary s flag) out) indices =
        some (bits, final) ∧ final.Halted := by
  induction bits generalizing s flag out with
  | nil => exact Bool.noConfusion (hlive.symm.trans hfirst.1)
  | cons b bits ih =>
    have hnext := ((M.firstHalting_cons_iff (enc a) b bits s).mp hfirst).2
    obtain ⟨first, hfirst, _⟩ := R.pass_replay a s hs b flag out
    have hs' := Reachable.step (M.withInit (start a)) (enc a) hs b
    suffices htail : ∃ rest final, Native.replayChoices R.I R.P R.F R.C
        (wordsCfg (enc a) (some (if M.halted (M.step (enc a) s b) then
          (.finish R.F.q₀ : Native.State R.SI R.SP R.SF) else .choose))
          (R.boundary (M.step (enc a) s b) (!M.halted (M.step (enc a) s b))) out) rest =
            some (bits, final) ∧ final.Halted by
      obtain ⟨rest, final, hrest, hhalt⟩ := htail
      exact ⟨first ++ rest, final,
        by simp [Native.replayChoices_append, hfirst, hrest, Option.bind], hhalt⟩
    cases hn : M.halted (M.step (enc a) s b) with
    | false =>
      simpa [hn] using ih (M.step (enc a) s b) hs' hn hnext true out
    | true =>
      obtain rfl := (M.firstHalting_iff_nil_of_halted (enc a) bits _ hn).mp hnext
      simpa [hn] using (R.finish_replay a (M.step (enc a) s b) hs' false out).1

/-- Every halted native replay records exactly a first-halting abstract trace and outputs
its verdict. An initially halted source records the empty trace. -/
theorem replay_correct (a : α)
    {indices : List ℕ} {bits : List Bool}
    {final : Cfg R.k Bool (Native.State R.SI R.SP R.SF) (enc a)}
    (hr : Native.replayChoices R.I R.P R.F R.C (R.machine.initCfg (enc a)) indices =
      some (bits, final)) (hhalt : final.Halted) :
    M.FirstHalting (enc a) bits (start a) ∧
      final.output = [M.accept (M.replay (enc a) bits (start a))] := by
  obtain ⟨_, _, hfactor⟩ := R.init_replay a
  obtain ⟨rest, _, hrest⟩ := (hfactor indices bits final hhalt).mp hr
  have hs := (M.withInit (start a)).reachable_init (enc a)
  cases hn : M.halted (start a) with
  | false =>
    exact R.choose_replay_correct a bits (start a) hs hn true [] (by simpa [hn] using hrest) hhalt
  | true =>
    obtain ⟨rfl, hout⟩ := (R.finish_replay a (start a) hs false []).2 rest bits final
      (by simpa [hn] using hrest) hhalt
    exact ⟨(M.firstHalting_iff_nil_of_halted (enc a) [] (start a) hn).mpr rfl, hout⟩

/-- An abstract trace halts for the first time at its end iff
there is exactly one halted native occurrence trace recording those bits. The quantification
is over occurrence lists, so two equal native transitions at a choice boundary remain distinct.
This is the replay correspondence, not the full native unambiguity or class-equality theorem. -/
theorem existsUnique_replay_iff (a : α) (bits : List Bool) :
    (∃! indices, ∃ final, Native.replayChoices R.I R.P R.F R.C
      (R.machine.initCfg (enc a)) indices = some (bits, final) ∧ final.Halted) ↔
    M.FirstHalting (enc a) bits (start a) := by
  refine ⟨fun ⟨_, ⟨final, hr, hhalt⟩, _⟩ => (R.replay_correct a hr hhalt).1, fun hfirst => ?_⟩
  obtain ⟨n, _, hfactor⟩ := R.init_replay a
  have hs := (M.withInit (start a)).reachable_init (enc a)
  obtain ⟨rest, final, hrest, hhalt⟩ : ∃ rest final,
      Native.replayChoices R.I R.P R.F R.C
        (wordsCfg (enc a) (some (if M.halted (start a) then .finish R.F.q₀ else .choose))
          (R.boundary (start a) (!M.halted (start a))) []) rest =
            some (bits, final) ∧ final.Halted := by
    cases hn : M.halted (start a) with
    | false =>
      simpa [hn] using R.exists_choose_replay a bits (start a) hs hn hfirst true []
    | true =>
      obtain rfl := (M.firstHalting_iff_nil_of_halted (enc a) bits (start a) hn).mp hfirst
      simpa [hn] using (R.finish_replay a (start a) hs false []).1
  have hr := (hfactor _ bits final hhalt).mpr ⟨rest, rfl, hrest⟩
  exact ⟨List.replicate n 0 ++ rest, ⟨final, hr, hhalt⟩, fun indices ⟨final', hr', hhalt'⟩ =>
    Native.eq_occurrences_of_replayChoices R.I R.P R.F R.C hr' hr hhalt' hhalt⟩

/-- A fixed selector list has exactly one accepting native occurrence list iff its
abstract replay first halts at the end of that list and accepts. -/
theorem existsUnique_accepting_replay_iff (a : α) (bits : List Bool) :
    (∃! indices, ∃ final, Native.replayChoices R.I R.P R.F R.C
      (R.machine.initCfg (enc a)) indices = some (bits, final) ∧
      final.Halted ∧ final.output = [true]) ↔
    M.FirstHalting (enc a) bits (start a) ∧ M.accept (M.replay (enc a) bits (start a)) = true := by
  refine ⟨fun ⟨_, ⟨final, hreplay, hhalt, hout⟩, _⟩ =>
      let ⟨hfirst, houtput⟩ := R.replay_correct a hreplay hhalt
      ⟨hfirst, (List.cons.inj (houtput.symm.trans hout)).1⟩,
    fun ⟨hfirst, haccept⟩ => ?_⟩
  obtain ⟨indices, ⟨final, hreplay, hhalt⟩, hunique⟩ :=
    (R.existsUnique_replay_iff a bits).mpr hfirst
  exact ⟨indices, ⟨final, hreplay, hhalt, (R.replay_correct a hreplay hhalt).2.trans
    (congrArg (· :: []) haccept)⟩, fun other ⟨f, hr, hh, _⟩ => hunique other ⟨f, hr, hh⟩⟩

/-- At a sufficient native clock, the counted occurrences for a
verdict are in bijection with the first-halting abstract choice traces for that verdict. The
extended cardinality on the right is finite, as witnessed by the native branch count. -/
theorem branchCount_eq_encard_firstHalting (a : α) {fuel : ℕ}
    (hclock : R.machine.RunsInTime (enc a) fuel) (verdict : List Bool → Bool) :
    ((Native.countingMachine R.I R.P R.F R.C).branchCount verdict fuel
      (R.machine.initCfg (enc a)) : ℕ∞) =
      {bits : List Bool |
        M.FirstHalting (enc a) bits (start a) ∧
        verdict [M.accept (M.replay (enc a) bits (start a))]}.encard := by
  classical
  let N := Native.countingMachine R.I R.P R.F R.C
  let cfg := R.machine.initCfg (enc a)
  let terminal := (N.branches fuel cfg).filter fun indices =>
    (N.runBranch cfg indices).any (fun final => verdict final.output)
  let good : Set (List Bool) := {bits |
    M.FirstHalting (enc a) bits (start a) ∧
    verdict [M.accept (M.replay (enc a) bits (start a))]}
  change (terminal.card : ℕ∞) = good.encard
  rw [← Set.encard_coe_eq_coe_finsetCard]
  have htrace (i : (terminal : Set (List ℕ))) : ∃ bits final,
      Native.replayChoices R.I R.P R.F R.C cfg i.val = some (bits, final) ∧
        final.Halted ∧ verdict final.output := by
    obtain ⟨hmem, hv⟩ := Finset.mem_filter.mp i.property
    obtain ⟨_, final, hrun, hhalt⟩ := (N.mem_branches_iff _ _ _).mp hmem
    have hval : verdict final.output := by simpa [hrun] using hv
    rw [← Native.map_snd_replayChoices R.I R.P R.F R.C] at hrun
    obtain ⟨⟨bits, last⟩, hr, rfl⟩ := Option.map_eq_some_iff.mp hrun
    exact ⟨bits, last, hr, hhalt, hval⟩
  choose trace final hreplay hhalt hverdict using htrace
  let f (i : (terminal : Set (List ℕ))) : good := by
    obtain ⟨hfirst, hout⟩ := R.replay_correct a (hreplay i) (hhalt i)
    exact ⟨trace i, hfirst, hout ▸ hverdict i⟩
  apply Set.encard_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · intro i j heq
    have htr : trace i = trace j := congrArg Subtype.val heq
    exact Subtype.ext (Native.eq_occurrences_of_replayChoices R.I R.P R.F R.C
      (htr ▸ hreplay i) (hreplay j) (hhalt i) (hhalt j))
  · intro bits
    obtain ⟨hfirst, hv⟩ := bits.property
    obtain ⟨indices, ⟨last, hr, hlast⟩, _⟩ :=
      (R.existsUnique_replay_iff a bits.val).mpr hfirst
    have hrun := congrArg (Option.map Prod.snd) hr
    rw [Native.map_snd_replayChoices] at hrun
    change N.runBranch cfg indices = some last at hrun
    have hc : N.HaltsWithin fuel cfg := Native.countingMachine_haltsWithin R.I R.P R.F R.C hclock
    have hout := (R.replay_correct a hr hlast).2
    have hmem : indices ∈ terminal := Finset.mem_filter.mpr
      ⟨(N.mem_branches_iff _ _ _).mpr ⟨hc.length_le hrun, last, hrun, hlast⟩,
        by simpa [hrun, hout] using hv⟩
    exact ⟨⟨indices, hmem⟩, Subtype.ext
      (congrArg Prod.fst (Option.some.inj ((hreplay ⟨indices, hmem⟩).symm.trans hr)))⟩

/-- At a sufficient native clock, the accepting occurrence count is the cardinality of
the accepting first-halting selector traces. -/
theorem acceptCount_eq_encard_firstHalting (a : α) {fuel : ℕ}
    (hclock : R.machine.RunsInTime (enc a) fuel) :
    ((Native.countingMachine R.I R.P R.F R.C).acceptCount fuel
      (R.machine.initCfg (enc a)) : ℕ∞) =
      {bits : List Bool | M.FirstHalting (enc a) bits (start a) ∧
        M.accept (M.replay (enc a) bits (start a)) = true}.encard := by
  simpa only [MultiTapeCTM.acceptCount, beq_iff_eq, List.cons.injEq, and_true] using
    R.branchCount_eq_encard_firstHalting a hclock (· == [true])

/-- At a sufficient native clock, exactly one abstract accepting first halt gives exactly
one accepting native branch, and conversely. -/
theorem acceptCount_eq_one_iff (a : α) {fuel : ℕ}
    (hclock : R.machine.RunsInTime (enc a) fuel) :
    (Native.countingMachine R.I R.P R.F R.C).acceptCount fuel (R.machine.initCfg (enc a)) = 1 ↔
      ∃! bits, M.FirstHalting (enc a) bits (start a) ∧
        M.accept (M.replay (enc a) bits (start a)) = true := by
  rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_one, R.acceptCount_eq_encard_firstHalting a hclock,
    Set.encard_eq_one]
  simp only [Set.eq_singleton_iff_unique_mem, Set.mem_ofPred_eq, ExistsUnique]

end Turing.NondeterministicQueryMachine.Routines
