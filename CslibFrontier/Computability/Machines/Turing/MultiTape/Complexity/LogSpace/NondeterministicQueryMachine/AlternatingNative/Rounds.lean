/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.AlternatingNative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-!
# Rounds of the alternating native machine

Acceptance by the alternating native machine `Turing.NondeterministicQueryMachine.Routines.atm`
is read round by round. Inside a deterministic routine the two moves agree and the guess register
is unchanged, so each routine run is a phase of moves that do not matter. Between routines, the
choice state makes the move `b` (recording or clearing a guess) and the continuation check routes
to the next round boundary `Turing.NondeterministicQueryMachine.Routines.boundaryCfg`.

## Main results

* `Turing.NondeterministicQueryMachine.Routines.accepts_atm_iff`: acceptance is acceptance from
  the first round boundary.
* `Turing.NondeterministicQueryMachine.Routines.exists_acceptsWithin_boundaryCfg_of_halted`: at a
  halted abstract state, the boundary accepts after the finalizer exactly when the state accepts.
* `Turing.NondeterministicQueryMachine.Routines.exists_acceptsWithin_boundaryCfg_of_live`: at a
  live abstract state, the boundary accepts when both (recorded guess `true`) or one (otherwise)
  of the moves lead, after the selected pass, to an accepting boundary.
-/

public section

namespace Turing.NondeterministicQueryMachine

open MultiTapeTM

namespace Native

variable {k : ℕ} {SI SF : Type} {SP : Bool → Type}
  (I : MultiTapeTM k Bool SI) (P : (b : Bool) → MultiTapeTM k Bool (SP b))
  (F : MultiTapeTM k Bool SF) (C : Fin k)

/-- A move of the alternating native machine is the native instruction under the same choice,
with the guess register updated by `trackGuess`. -/
private theorem next_altMachine_mapState (b : Bool) {input : List Bool}
    (c : Cfg k Bool (State SI SP SF) input) {st : State SI SP SF} (h : c.state = some st)
    (g : Option Bool) :
    (altMachine I P F C).next b (c.mapState (Option.map (·, g))) =
      (((table I P F C).withCoin b).toTM.step c).mapState
        (Option.map (·, trackGuess st g b)) := by
  have hs : (c.mapState (Option.map (·, g))).state = some (st, g) := by
    simp [Cfg.mapState, h]
  rw [altMachine, MultiTapeATM.next_ofTMs, MultiTapeTM.step_of_state hs,
    MultiTapeTM.step_of_state h, tr_withCoin]
  simp only [guessTM, MultiTapeTM.tr_ofTr]
  rfl

private theorem next_init (b : Bool) {input : List Bool} (g : Option Bool)
    (c : Cfg k Bool SI input) (h : c.state ≠ none) :
    (altMachine I P F C).next b ((c.mapState initState).mapState (Option.map (·, g))) =
      ((I.step c).mapState initState).mapState (Option.map (·, g)) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp h
  rw [next_altMachine_mapState I P F C b (c.mapState initState) (st := .init q)
    (by simp [Cfg.mapState, initState, hq]), step_init I P F C b c h]
  rfl

private theorem next_pass (b' b : Bool) {input : List Bool} (g : Option Bool)
    (c : Cfg k Bool (SP b) input) (h : c.state ≠ none) :
    (altMachine I P F C).next b' ((c.mapState (passState b)).mapState (Option.map (·, g))) =
      (((P b).step c).mapState (passState b)).mapState (Option.map (·, g)) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp h
  rw [next_altMachine_mapState I P F C b' (c.mapState (passState b)) (st := .pass b q)
    (by simp [Cfg.mapState, passState, hq]), step_pass I P F C b' b c h]
  rfl

private theorem next_finish (b : Bool) {input : List Bool} (g : Option Bool)
    (c : Cfg k Bool SF input) (h : c.state ≠ none) :
    (altMachine I P F C).next b ((c.mapState finishState).mapState (Option.map (·, g))) =
      ((F.step c).mapState finishState).mapState (Option.map (·, g)) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp h
  rw [next_altMachine_mapState I P F C b (c.mapState finishState) (st := .finish q)
    (by simp [Cfg.mapState, finishState, hq]), step_finish I P F C b c h]
  rfl

end Native

namespace Routines

variable {α σ : Type} {M : NondeterministicQueryMachine σ} {start : α → σ}
  {enc : α ↪ List Bool} {S : α → ℕ} (R : Routines M start enc S)

/-- The continuation check after a routine leading to the boundary of `s` takes one move. -/
private theorem acceptsWithin_check (a : α) (s : σ) (g : Option Bool) (n : ℕ) :
    R.atm.AcceptsWithin n
      (wordsCfg (enc a) (some (.check, g)) (R.boundary s (!M.halted s)) []) ↔
      1 ≤ n ∧ R.atm.AcceptsWithin (n - 1) (R.boundaryCfg a s g) := by
  have hnext (b : Bool) : R.atm.next b
      (wordsCfg (enc a) (some (.check, g)) (R.boundary s (!M.halted s)) []) =
      R.boundaryCfg a s g := by
    refine (Native.next_altMachine_mapState R.I R.P R.F R.C b
      (wordsCfg (enc a) (some .check) (R.boundary s (!M.halted s)) []) rfl g).trans ?_
    rw [Native.step_check_words, R.boundary_flag, boundaryCfg]
    cases M.halted s <;> rfl
  cases n with
  | zero => exact iff_of_false (MultiTapeATM.not_acceptsWithin_zero _ rfl) (by simp)
  | succ n =>
    rw [MultiTapeATM.acceptsWithin_succ_of_next_eq hnext]
    simp

/-- A pass from the boundary of `s`, followed by its continuation check, leads to the boundary of
the successor of `s` under the choice of the pass. -/
private theorem exists_pass (a : α) (s : σ) (hs : (M.withInit (start a)).Reachable (enc a) s)
    (b flag : Bool) (g : Option Bool) :
    ∃ τ, ∀ n, R.atm.AcceptsWithin n
      (wordsCfg (enc a) (some (.pass b (R.P b).q₀, g)) (R.boundary s flag) []) ↔
      τ ≤ n ∧ R.atm.AcceptsWithin (n - τ) (R.boundaryCfg a (M.step (enc a) s b) g) := by
  obtain ⟨t, ht⟩ := R.pass_spec a s hs b flag
  obtain ⟨ws', e, hrun, ⟨rfl, rfl⟩, -⟩ :=
    transformsTapes_iff_runFrom.mp ht (enc a) _ [] ⟨rfl, rfl⟩
  obtain ⟨τ, hτ⟩ := MultiTapeATM.exists_acceptsWithin_iff_of_lift (atm := R.atm)
    (fun c : Cfg R.k Bool (R.SP b) (enc a) =>
      (c.mapState (Native.passState b)).mapState (Option.map (·, g)))
    (fun b' c hc => Native.next_pass R.I R.P R.F R.C b' b g c hc)
    (fun c _ => by simp [Cfg.mapState, Native.passState]) hrun rfl
  exact ⟨τ + 1, MultiTapeATM.acceptsWithin_iff_of_phase_trans hτ (R.acceptsWithin_check a _ g)⟩

/-- The initializer, followed by its continuation check, leads to the boundary of the start. -/
private theorem exists_init (a : α) :
    ∃ τ, ∀ n, R.atm.AcceptsWithin n (R.atm.toPTM.toNTM.initCfg (enc a)) ↔
      τ ≤ n ∧ R.atm.AcceptsWithin (n - τ) (R.boundaryCfg a (start a) none) := by
  obtain ⟨t, ht⟩ := R.initial_spec a
  obtain ⟨ws', e, hrun, ⟨rfl, rfl⟩, -⟩ :=
    transformsTapes_iff_runFrom.mp ht (enc a) _ [] ⟨rfl, rfl⟩
  obtain ⟨τ, hτ⟩ := MultiTapeATM.exists_acceptsWithin_iff_of_lift (atm := R.atm)
    (fun c : Cfg R.k Bool R.SI (enc a) =>
      (c.mapState Native.initState).mapState (Option.map (·, (none : Option Bool))))
    (fun b c hc => Native.next_init R.I R.P R.F R.C b none c hc)
    (fun c _ => by simp [Cfg.mapState, Native.initState]) hrun rfl
  have hinit : R.atm.toPTM.toNTM.initCfg (enc a) =
      wordsCfg (enc a) (some (.init R.I.q₀, none)) (fun _ => []) [] :=
    Cfg.init_eq_wordsCfg _ _
  rw [hinit]
  exact ⟨τ + 1, MultiTapeATM.acceptsWithin_iff_of_phase_trans hτ (R.acceptsWithin_check a _ none)⟩

/-- **Acceptance from the first round boundary.** The alternating native machine accepts exactly
when the boundary of the start state, with an empty guess register, accepts within some number of
moves. -/
theorem accepts_atm_iff (a : α) :
    R.atm.Accepts (enc a) ↔ ∃ n, R.atm.AcceptsWithin n (R.boundaryCfg a (start a) none) := by
  obtain ⟨τ, hτ⟩ := R.exists_init a
  exact ⟨fun ⟨n, hn⟩ => ⟨n - τ, ((hτ n).mp hn).2⟩,
    fun ⟨n, hn⟩ => ⟨n + τ, (hτ (n + τ)).mpr ⟨Nat.le_add_left _ _, by rwa [Nat.add_sub_cancel]⟩⟩⟩

/-- **The boundary of a halted state.** After the finalizer's moves, the boundary of a reachable
halted state accepts exactly when the state accepts. -/
theorem exists_acceptsWithin_boundaryCfg_of_halted (a : α) (s : σ)
    (hs : (M.withInit (start a)).Reachable (enc a) s) (hh : M.halted s = true) (g : Option Bool) :
    ∃ τ, ∀ n, R.atm.AcceptsWithin n (R.boundaryCfg a s g) ↔ τ ≤ n ∧ M.accept s = true := by
  obtain ⟨t, ht⟩ := R.final_spec a s hs false
  obtain ⟨ws', e, hrun, rfl, -⟩ := transformsTapes_iff_runFrom.mp ht (enc a) _ [] ⟨rfl, rfl⟩
  obtain ⟨τ, hτ⟩ := MultiTapeATM.exists_acceptsWithin_iff_of_lift (atm := R.atm)
    (fun c : Cfg R.k Bool R.SF (enc a) =>
      (c.mapState Native.finishState).mapState (Option.map (·, g)))
    (fun b c hc => Native.next_finish R.I R.P R.F R.C b g c hc)
    (fun c hc => by
      obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hc
      simp [Cfg.mapState, Native.finishState, hq]) hrun rfl
  have hb : R.boundaryCfg a s g =
      wordsCfg (enc a) (some (.finish R.F.q₀, g)) (R.boundary s false) [] := by
    simp [boundaryCfg, hh]
  refine ⟨τ, fun n => ?_⟩
  rw [hb]
  refine (hτ n).trans (and_congr_right fun _ => ?_)
  rw [MultiTapeATM.acceptsWithin_of_halted _ (by rfl)]
  simp

/-- **The boundary of a live state.** The boundary of a reachable live state accepts within
`n + 1` moves exactly when, for both moves `b` (recorded guess `true`: a universal state) or for
one of them (otherwise), the selected pass and its continuation check, taking `τ b` moves, lead to
the boundary of the successor under `b`, with the updated guess register, accepting within the
remaining moves. -/
theorem exists_acceptsWithin_boundaryCfg_of_live (a : α) (s : σ)
    (hs : (M.withInit (start a)).Reachable (enc a) s) (hh : M.halted s = false) (g : Option Bool) :
    ∃ τ : Bool → ℕ, ∀ n, R.atm.AcceptsWithin (n + 1) (R.boundaryCfg a s g) ↔
      if g = some true then
        ∀ b, τ b ≤ n ∧ R.atm.AcceptsWithin (n - τ b)
          (R.boundaryCfg a (M.step (enc a) s b) (Native.nextGuess g b))
      else
        ∃ b, τ b ≤ n ∧ R.atm.AcceptsWithin (n - τ b)
          (R.boundaryCfg a (M.step (enc a) s b) (Native.nextGuess g b)) := by
  have hb : R.boundaryCfg a s g =
      wordsCfg (enc a) (some (.choose, g)) (R.boundary s true) [] := by
    simp [boundaryCfg, hh]
  have hnext (b : Bool) : R.atm.next b (R.boundaryCfg a s g) =
      wordsCfg (enc a) (some (.pass b (R.P b).q₀, Native.nextGuess g b)) (R.boundary s true)
        [] := by
    rw [hb]
    exact (Native.next_altMachine_mapState R.I R.P R.F R.C b
      (wordsCfg (enc a) (some .choose) (R.boundary s true) []) rfl g).trans
      (by rw [Native.step_choose R.I R.P R.F R.C b _ rfl]; rfl)
  choose τ hτ using fun b => R.exists_pass a s hs b true (Native.nextGuess g b)
  have hstate : (R.boundaryCfg a s g).state = some (.choose, g) := by rw [hb]; rfl
  refine ⟨τ, fun n => ?_⟩
  by_cases hg : g = some true
  · subst hg
    rw [ite_eq_left rfl, MultiTapeATM.acceptsWithin_succ_of_universal _ hstate rfl]
    exact forall_congr' fun b => by rw [hnext]; exact hτ b n
  · have hu : R.atm.universal (.choose, g) = false := by
      rcases g with _ | _ | _ <;> first | rfl | exact absurd rfl hg
    rw [ite_eq_right hg, MultiTapeATM.acceptsWithin_succ_of_existential _ hstate hu]
    exact exists_congr fun b => by rw [hnext]; exact hτ b n

end Routines

end Turing.NondeterministicQueryMachine
