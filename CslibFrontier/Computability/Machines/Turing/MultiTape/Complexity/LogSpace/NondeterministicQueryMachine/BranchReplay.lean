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

The finalizer consumes no abstract choices and emits the abstract state's verdict.
-/

public section

namespace Turing.NondeterministicQueryMachine.Routines

open MultiTapeTM

variable {α σ : Type} {M : NondeterministicQueryMachine σ} {start : α → σ}
  {enc : α ↪ List Bool} {S : α → ℕ} (R : Routines M start enc S)

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
  have hrun := congrArg (Option.map Prod.snd) hr
  rw [Native.map_snd_replayChoices] at hrun
  change (Native.countingMachine R.I R.P R.F R.C).runBranch initial indices = some final at hrun
  obtain ⟨p₀, hphead, hplast, hplen⟩ : ∃ p : RelSeries (R.machine.runningStepRel (enc a)),
      p.head = initial ∧ p.last = final ∧ p.length = indices.length := by
    let statement (N : MultiTapeNTM R.k Bool (Native.State R.SI R.SP R.SF)) : Prop :=
      ∃ p : RelSeries (N.runningStepRel (enc a)),
        p.head = initial ∧ p.last = final ∧ p.length = indices.length
    exact (congrArg statement (Native.toNTM_countingMachine R.I R.P R.F R.C)).mp
      ((Native.countingMachine R.I R.P R.F R.C).exists_runningPath_of_runBranch hrun)
  let p : R.machine.RunPath (enc a) := p₀.map ⟨id, fun h => h.2⟩
  have hlong : q.length ≤ indices.length := by
    by_contra! hshort
    have hmap : p.head = q.head.mapState Native.finishState := by
      simpa [p, q', f] using hphead.trans hhead.symm
    have hpLen : p.length = indices.length := hplen
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
abstract step. The continuation check records no choice. -/
theorem exists_pass_replay (a : α) (s : σ)
    (hs : (M.withInit (start a)).Reachable (enc a) s) (b flag : Bool) (out : List Bool) :
    ∃ indices, Native.replayChoices R.I R.P R.F R.C
      (wordsCfg (enc a) (some .choose) (R.boundary s flag) out) indices =
      some ([b], wordsCfg (enc a)
        (some (if M.halted (M.step (enc a) s b) then .finish R.F.q₀ else .choose))
        (R.boundary (M.step (enc a) s b) (!M.halted (M.step (enc a) s b))) out) := by
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
  refine ⟨b.toNat :: (List.replicate p.length 0 ++ [0]), ?_⟩
  rw [Native.replayChoices_choose _ _ _ _ _ rfl, withState_wordsCfg, ← hphead,
    Native.replayChoices_append, hp]
  simp only [Option.bind, hcheck, Native.replayChoices_nil, Option.map_some, List.nil_append]
  rw [hws, R.boundary_flag]
  cases M.halted (M.step (enc a) s b) <;> simp [flagWord]

end Turing.NondeterministicQueryMachine.Routines
