/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Compiler
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.CountingView

/-! # Occurrence replay for compiled query machines

Initialization writes the initial boundary and takes no choice. Every first-halting replay
from the machine's start has this deterministic prefix. At a choice boundary, a halted
replay splits after one selected pass and its continuation check, with no change to the
remaining choices or terminal configuration. The finalizer consumes no abstract choices
and emits the abstract state's verdict. The full compiler correspondence is tracked in #6747.
The initializer still routes to the first choice when the abstract start is halted.
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
  have hrun := congrArg (Option.map Prod.snd) hr
  rw [Native.map_snd_replayChoices] at hrun
  change (Native.countingMachine R.I R.P R.F R.C).runBranch cfg indices = some final at hrun
  let statement (N : MultiTapeNTM R.k Bool (Native.State R.SI R.SP R.SF)) : Prop :=
    ∃ p : RelSeries (N.runningStepRel (enc a)),
      p.head = cfg ∧ p.last = final ∧ p.length = indices.length
  obtain ⟨p, hhead, hlast, hlen⟩ := (congrArg statement
    (Native.toNTM_countingMachine R.I R.P R.F R.C)).mp
      ((Native.countingMachine R.I R.P R.F R.C).exists_runningPath_of_runBranch hrun)
  exact ⟨p.map ⟨id, fun h => h.2⟩, hhead, hlast, hlen⟩

/-- Initialization reaches the first choice boundary by one fixed sequence of zero occurrence
indices, recording no choices. A first-halting replay from the start is exactly that prefix
followed by a replay from the boundary with the same choice trace and terminal configuration. -/
theorem init_replay (a : α) :
    ∃ n,
      let initial := R.machine.initCfg (enc a)
      let boundary := wordsCfg (enc a) (some (.choose : Native.State R.SI R.SP R.SF))
        (R.boundary (start a) false) []
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
  have hlast : p.last = wordsCfg (enc a) (some .choose) (R.boundary (start a) false) [] := by
    simp [p, f, hlast', hqlast, Native.initState, hws, he]
  have hprefix := Native.replayChoices_replicate_zero R.I R.P R.F R.C p (by
    intro i
    change Native.initState (q i.castSucc).state ≠ some Native.State.choose
    cases hstate : (q i.castSucc).state with
    | none => exact ((q.step i).1 hstate).elim
    | some s => simp [Native.initState])
  rw [hhead, hlast] at hprefix
  refine ⟨p.length, hprefix, fun indices bits final hhalt => ⟨?_, ?_⟩⟩
  · intro hr
    obtain ⟨full, hfullhead, hfulllast, hfulllen⟩ := R.exists_native_path_of_replay hr
    have hlen : (List.replicate p.length 0).length ≤ indices.length := by
      simp only [List.length_replicate, ← hfulllen]
      by_contra! hshort
      have hmap : full.head = q.head.mapState Native.initState := by
        simpa [p, f] using hfullhead.trans hhead.symm
      have hl : full.length < q.length := hshort
      have heq := Native.follows_init R.I R.P R.F R.C full q hmap full.length
        (Nat.lt_succ_self _) (by omega)
      change full.last = (q ⟨full.length, by omega⟩).mapState Native.initState at heq
      have hh : full.last.Halted := hfulllast ▸ hhalt
      rw [heq] at hh
      change some _ = none at hh
      cases hh
    exact Native.exists_suffix_of_replayChoices R.I R.P R.F R.C hprefix
      (by simpa only [List.nil_append] using hr) hlen
  · rintro ⟨rest, rfl, hrest⟩
    rw [Native.replayChoices_append, hprefix]
    change (Native.replayChoices R.I R.P R.F R.C _ rest).map _ = _
    rw [hrest]
    rfl

/-- A halted occurrence replay from the finalizer has no genuine choices and emits the
abstract verdict. -/
theorem finish_replay (a : α) (s : σ)
    (hs : (M.withInit (start a)).Reachable (enc a) s) (flag : Bool) (out : List Bool)
    {indices : List ℕ} {bits : List Bool}
    {final : Cfg R.k Bool (Native.State R.SI R.SP R.SF) (enc a)}
    (hr : Native.replayChoices R.I R.P R.F R.C
      (wordsCfg (enc a) (some (.finish R.F.q₀)) (R.boundary s flag) out)
        indices = some (bits, final))
    (hhalt : final.Halted) : bits = [] ∧ final.output = out ++ [M.accept s] := by
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
  have hdet := Native.replayChoices_replicate_zero R.I R.P R.F R.C q' (by
    intro i
    change Option.map Native.State.finish _ ≠ some Native.State.choose
    cases (q i.castSucc).state <;> simp)
  rw [hhead] at hdet
  obtain ⟨p, hphead, hplast, hplen⟩ := R.exists_native_path_of_replay hr
  have hlong : q.length ≤ indices.length := by
    by_contra! hshort
    have hmap : p.head = q.head.mapState Native.finishState := by
      simpa [q', f] using hphead.trans hhead.symm
    have h := Native.follows_finish R.I R.P R.F R.C p q hmap p.length
      (Nat.lt_succ_self _) (by omega)
    change p.last = (q ⟨p.length, by omega⟩).mapState Native.finishState at h
    have hh : p.last.Halted := hplast ▸ hhalt
    rw [h] at hh
    exact (q.step ⟨p.length, by omega⟩).1 (Option.map_eq_none_iff.mp hh)
  obtain ⟨rest, _, hrest⟩ :=
    Native.exists_suffix_of_replayChoices R.I R.P R.F R.C hdet hr (by simpa [q'] using hlong)
  have htail := congrArg (Option.map Prod.snd) hrest
  rw [Native.map_snd_replayChoices] at htail
  have hqhalt : q'.last.Halted := by rw [hlast]; rfl
  cases rest with
  | nil =>
    rw [Native.replayChoices_nil] at hrest
    have ⟨hb, hf⟩ := Prod.mk.inj (Option.some.inj hrest)
    exact ⟨hb.symm, by rw [← hf]; simp [hlast]⟩
  | cons j rest =>
    simp [MultiTapeCTM.runBranch_of_halted _ hqhalt] at htail

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
  have hp := Native.replayChoices_replicate_zero R.I R.P R.F R.C p (by
    intro i
    change (some ((q i.castSucc).state.elim Native.State.check (Native.State.pass b))) ≠
      some Native.State.choose
    cases (q i.castSucc).state <;> simp)
  have hstep : R.machine.Step p.last
      (wordsCfg (enc a) (some (if ws' R.C = [] then .finish R.F.q₀ else .choose)) ws' out) := by
    rw [hplast]
    exact (Native.step_iff R.I R.P R.F R.C).mpr
      ⟨false, Native.step_check_words R.I R.P R.F R.C false ws' out⟩
  have hcheck := Native.replayChoices_step_zero R.I R.P R.F R.C
    (show p.last.state ≠ some .choose by rw [hplast]; exact fun h => by cases h)
    (show ¬p.last.Halted by rw [hplast]; exact fun h => by cases h) hstep []
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
      dsimp only [initial]
      rw [Native.replayChoices_choose _ _ _ _ _ rfl, withState_wordsCfg, ← hphead,
        Native.replayChoices_nil, Option.map_some]
    have hnonempty : indices ≠ [] := by
      intro hempty
      simp [hempty, Native.replayChoices_nil] at hr
    obtain ⟨tail, hindices, htail⟩ := Native.exists_suffix_of_replayChoices R.I R.P R.F R.C
      hchoose (show _ = some ([b] ++ bits, final) from hr)
      (List.length_pos_iff.mpr hnonempty)
    obtain ⟨full, hfullhead, hfulllast, hfulllen⟩ := R.exists_native_path_of_replay htail
    have hpass : q.length < full.length := by
      by_contra! hshort
      have hmap : full.head = q.head.mapState (Native.passState b) := hfullhead
      have heq := Native.follows_pass R.I R.P R.F R.C b full q hmap full.length
        (Nat.lt_succ_self _) (by omega)
      change full.last = (q ⟨full.length, by omega⟩).mapState (Native.passState b) at heq
      have hh : full.last.Halted := hfulllast ▸ hhalt
      rw [heq] at hh
      change some _ = none at hh
      cases hh
    have hlen : first.length ≤ indices.length := by
      have hplen : p.length = q.length := rfl
      rw [hindices]
      simp only [first, List.length_cons, List.length_append, List.length_replicate,
        List.length_nil, hplen]
      omega
    exact Native.exists_suffix_of_replayChoices R.I R.P R.F R.C hfirst
      (show _ = some ([b] ++ bits, final) from hr) hlen
  · rintro ⟨rest, rfl, hrest⟩
    rw [Native.replayChoices_append, hfirst]
    simp [hrest, Option.bind]

end Turing.NondeterministicQueryMachine.Routines
