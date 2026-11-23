/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import Cslib.Computability.Machines.Turing.MultiTape.Configuration
import CslibFrontier.Computability.Complexity.Classes.Alternation
import CslibFrontier.Computability.Complexity.Classes.Alternation.DeterministicSpace
import CslibFrontier.Computability.Complexity.Classes.Space.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.DeterministicSpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Bool
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Nondeterministic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.StateFlags
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds

/-!
# Module client tests for alternating time within deterministic space

Exercises the public surface of `StateFlags`, `Alternating.DeterministicSpace`, and
`Classes.Alternation.DeterministicSpace` under ordinary `module` encapsulation on a concrete
three-step alternating machine `twoPrefixEqATM` that existentially guesses a bit `b`, universally
branches across the first two input cells, and accepts iff the input begins with `b, b`.
-/

-- Ordinary module client test: private declarations only.
set_option linter.privateModule false

namespace CslibFrontierTests.AlternatingDeterministicSpace

open Cslib Cslib.Complexity Turing
open Turing.MultiTapeTM (ComputableInSpace encBits encBool encPair)

/-- Control states for testing whether the first two input bits are equal:
`guess` existentially chooses `b`, `all b` universally picks index `0` or `1`, and `second b`
inspects index `1` after advancing the input head. -/
private inductive TwoEqState
  | guess
  | all (b : Bool)
  | second (b : Bool)
  deriving DecidableEq

private instance : Finite TwoEqState :=
  Finite.of_equiv (Unit ⊕ Bool ⊕ Bool)
    { toFun := fun
        | .inl () => .guess
        | .inr (.inl b) => .all b
        | .inr (.inr b) => .second b
      invFun := fun
        | .guess => .inl ()
        | .all b => .inr (.inl b)
        | .second b => .inr (.inr b)
      left_inv := by rintro (_ | _ | _) <;> rfl
      right_inv := by rintro (_ | _ | _) <;> rfl }

/-- A nontrivial 3-step alternating machine deciding
`{w | ∃ b, w[0]? = some b ∧ w[1]? = some b}`:
step 0 existentially chooses `b ∈ Bool`; step 1 universally chooses between checking
`w[0]? = some b` immediately (`move = false`) and advancing the input head right (`move = true`)
to check `w[1]? = some b` at step 2. -/
private def twoPrefixEqATM : MultiTapeATM 0 Bool TwoEqState where
  toPTM :=
    { initial := .guess
      tr := fun q sym _ _ move =>
        match q with
        | .guess =>
          .step ⟨0, Fin.elim0, none, some (.all move)⟩ Empty.elim Empty.elim
        | .all b =>
          if move then
            .step ⟨.pos, Fin.elim0, none, some (.second b)⟩ Empty.elim Empty.elim
          else
            .step ⟨0, Fin.elim0, some (sym == some b), none⟩ Empty.elim Empty.elim
        | .second b =>
          .step ⟨0, Fin.elim0, some (sym == some b), none⟩ Empty.elim Empty.elim }
  universal
    | .all _ => true
    | _ => false

/-- Words beginning with two equal bits: nonempty and strict (`[true, true]` in, `[true, false]`
and `[]` out). -/
private def twoPrefixEq : Set (List Bool) :=
  {w | ∃ b : Bool, w[0]? = some b ∧ w[1]? = some b}

private theorem mem_twoPrefixEq_tt : [true, true] ∈ twoPrefixEq :=
  ⟨true, rfl, rfl⟩

private theorem notMem_twoPrefixEq_tf : [true, false] ∉ twoPrefixEq := by
  rintro ⟨b, h0, h1⟩
  cases b <;> simp at h0 h1

private theorem notMem_twoPrefixEq_nil : ([] : List Bool) ∉ twoPrefixEq := by
  rintro ⟨b, h0, _⟩
  simp at h0

/-- The input symbol at head position `1` is `w[0]?`. -/
private theorem inputSymbol_pos_one (q : TwoEqState) (w : List Bool) :
    ({ state := some q
       inputPos := 1
       workTapes := fun _ _ => none
       workTapePos := fun _ => 0
       output := [] } : Cfg 0 Bool TwoEqState w).inputSymbol = w[0]? := by
  rcases w with _ | ⟨x₀, xs⟩
  · exact inputSymbol_eq_none_of_boundary (Or.inr rfl)
  · exact inputSymbolInner 0 rfl (by simp)

/-- After one right move of the input head from position `1`, the input symbol is `w[1]?`. -/
private theorem inputSymbol_moveRight_one (q : TwoEqState) (w : List Bool) :
    ({ state := some q
       inputPos := moveInputPos (1 : Fin (w.length + 2)) .pos
       workTapes := fun _ _ => none
       workTapePos := fun _ => 0
       output := [] } : Cfg 0 Bool TwoEqState w).inputSymbol = w[1]? := by
  rcases w with _ | ⟨x₀, _ | ⟨x₁, xs⟩⟩
  · exact inputSymbol_eq_none_of_boundary (Or.inr rfl)
  · exact inputSymbol_eq_none_of_boundary (Or.inr rfl)
  · have hpos : (moveInputPos (1 : Fin ((x₀ :: x₁ :: xs).length + 2)) .pos).val = 2 := by
      rw [moveInputPos_pos_of_ne_right _ (by simp)]
      rfl
    exact inputSymbolInner 1 hpos (by simp)

private theorem step_guess (b : Bool) (w : List Bool) :
    twoPrefixEqATM.next b (twoPrefixEqATM.toPTM.toNTM.initCfg w) =
      ⟨some (.all b), 1, fun _ _ => none, fun _ => 0, []⟩ := by
  rw [twoPrefixEqATM.next_of_state (q := .guess) rfl]
  exact Cfg.ext_zero_tapes rfl (moveInputPos_zero 1) rfl

private theorem step_all_false (b : Bool) (w : List Bool) :
    twoPrefixEqATM.next false
        (⟨some (.all b), 1, fun _ _ => none, fun _ => 0, []⟩ : Cfg 0 Bool TwoEqState w) =
      ⟨none, 1, fun _ _ => none, fun _ => 0, [w[0]? == some b]⟩ := by
  rw [twoPrefixEqATM.next_of_state (q := .all b) rfl]
  refine Cfg.ext_zero_tapes rfl (moveInputPos_zero 1) ?_
  simp only [Action.apply_output, List.nil_append, Option.toList_some, twoPrefixEqATM,
    MultiTapeATM.action, Bool.false_eq_true, ↓reduceIte,
    MultiTapeMachine.Action.emptyOracleEquiv, Equiv.coe_fn_mk, inputSymbol_pos_one]

private theorem step_all_true (b : Bool) (w : List Bool) :
    twoPrefixEqATM.next true
        (⟨some (.all b), 1, fun _ _ => none, fun _ => 0, []⟩ : Cfg 0 Bool TwoEqState w) =
      ⟨some (.second b), moveInputPos 1 .pos, fun _ _ => none, fun _ => 0, []⟩ := by
  rw [twoPrefixEqATM.next_of_state (q := .all b) rfl]
  exact Cfg.ext_zero_tapes rfl rfl rfl

private theorem step_second (b m : Bool) (w : List Bool) :
    twoPrefixEqATM.next m
        (⟨some (.second b), moveInputPos 1 .pos, fun _ _ => none, fun _ => 0, []⟩ :
          Cfg 0 Bool TwoEqState w) =
      ⟨none, moveInputPos 1 .pos, fun _ _ => none, fun _ => 0, [w[1]? == some b]⟩ := by
  rw [twoPrefixEqATM.next_of_state (q := .second b) rfl]
  refine Cfg.ext_zero_tapes rfl (moveInputPos_zero _) ?_
  simp only [Action.apply_output, List.nil_append, Option.toList_some, twoPrefixEqATM,
    MultiTapeATM.action, MultiTapeMachine.Action.emptyOracleEquiv, Equiv.coe_fn_mk,
    inputSymbol_moveRight_one]

/-- Every 3-move path of `twoPrefixEqATM` halts. -/
private theorem runsInTime_twoPrefixEqATM (w : List Bool) :
    twoPrefixEqATM.toPTM.toNTM.RunsInTime w 3 := by
  refine MultiTapeATM.runsInTime_iff_stepCoins.mpr fun coins hlen => ?_
  rcases coins with _ | ⟨b₀, _ | ⟨b₁, _ | ⟨b₂, _ | _⟩⟩⟩ <;> simp at hlen
  change (twoPrefixEqATM.next b₂ (twoPrefixEqATM.next b₁
    (twoPrefixEqATM.next b₀ (twoPrefixEqATM.toPTM.toNTM.initCfg w)))).state = none
  rw [step_guess]
  cases b₁
  · rw [step_all_false, twoPrefixEqATM.next_of_halted rfl]
  · rw [step_all_true, step_second]

/-- From `.all b`, acceptance within 2 moves checks `w[0]? = some b ∧ w[1]? = some b`. -/
private theorem acceptsWithin_two_all_iff (b : Bool) (w : List Bool) :
    twoPrefixEqATM.AcceptsWithin 2
        (⟨some (.all b), 1, fun _ _ => none, fun _ => 0, []⟩ : Cfg 0 Bool TwoEqState w) ↔
      (w[0]? = some b ∧ w[1]? = some b) := by
  rw [twoPrefixEqATM.acceptsWithin_succ_of_universal (q := .all b) rfl rfl, Bool.forall_bool,
    step_all_false, twoPrefixEqATM.acceptsWithin_of_halted rfl,
    step_all_true, twoPrefixEqATM.acceptsWithin_succ_of_existential (q := .second b) rfl rfl,
    Bool.exists_bool, step_second, step_second]
  simp [MultiTapeATM.AcceptsWithin]

/-- `twoPrefixEqATM` accepts `w` within 3 moves iff `w ∈ twoPrefixEq`. -/
private theorem acceptsWithin_three_iff (w : List Bool) :
    twoPrefixEqATM.AcceptsWithin 3 (twoPrefixEqATM.toPTM.toNTM.initCfg w) ↔ w ∈ twoPrefixEq := by
  rw [twoPrefixEqATM.acceptsWithin_succ_of_existential (q := .guess) rfl rfl]
  simp only [step_guess, acceptsWithin_two_all_iff]
  rfl

/-- `twoPrefixEqATM` decides `twoPrefixEq` within 3 steps. -/
private theorem decidesInTime_twoPrefixEq :
    twoPrefixEqATM.DecidesInTime encBits twoPrefixEq fun _ => 3 := fun w =>
  ⟨runsInTime_twoPrefixEqATM (encBits w), by
    rw [MultiTapeATM.accepts_iff_acceptsWithin (runsInTime_twoPrefixEqATM (encBits w)),
      acceptsWithin_three_iff (encBits w)]
    rfl⟩

/-! ### Public-surface client checks (`StateFlags` and machine-level simulation) -/

/-- On `twoPrefixEqATM`, the flag table distinguishes a halted 2-move branch (`[true, false]`) from
a still-running 2-move branch (`[true, true]`), without unfolding `MultiTapePTM.flag`. -/
example (w : List Bool) :
    (((twoPrefixEqATM.toPTM.flag Option.isNone).runClosedCoins [true, false] w).getLastD false =
        true) ∧
      (((twoPrefixEqATM.toPTM.flag Option.isNone).runClosedCoins [true, true] w).getLastD false =
        false) := by
  have h1 := MultiTapePTM.getLastD_runClosedCoins_flag twoPrefixEqATM.toPTM Option.isNone
    [true, false] w
  have h2 := MultiTapePTM.getLastD_runClosedCoins_flag twoPrefixEqATM.toPTM Option.isNone
    [true, true] w
  dsimp only [Option.isNone] at h1 h2
  rw [h1, h2]
  constructor
  · change (twoPrefixEqATM.next false
      (twoPrefixEqATM.next true (twoPrefixEqATM.toPTM.toNTM.initCfg w))).state.isNone = true
    rw [step_guess, step_all_false]
    rfl
  · change (twoPrefixEqATM.next true
      (twoPrefixEqATM.next true (twoPrefixEqATM.toPTM.toNTM.initCfg w))).state.isNone = false
    rw [step_guess, step_all_true]
    rfl

/-- `ComputableInSpace.lastFlag` certifies state-flag replay in linear space. -/
example :
    ComputableInSpace
      (fun p : List Bool × List Bool =>
        (twoPrefixEqATM.toPTM.stepCoins p.1
          (Cfg.init twoPrefixEqATM.toPTM.initial p.2)).state.isNone)
      (encPair encBits encBits) encBool fun p => (encPair encBits encBits p).length :=
  ComputableInSpace.lastFlag twoPrefixEqATM.toPTM Option.isNone

/-- Machine-level `gameValue` evaluates `[true, true]` to `true` and `[true, false]` and `[]` to
`false`, and `computableInSpace_gameValue` certifies linear-space evaluation. -/
example :
    twoPrefixEqATM.gameValue [true, true] 3 [] = true ∧
      twoPrefixEqATM.gameValue [true, false] 3 [] = false ∧
      twoPrefixEqATM.gameValue [] 3 [] = false ∧
      ComputableInSpace (fun w => twoPrefixEqATM.gameValue w 3 []) encBits encBool
        (fun w => w.length + 3) :=
  ⟨(decidesInTime_twoPrefixEq.mem_iff_gameValue [true, true]).mp mem_twoPrefixEq_tt,
    Bool.eq_false_iff.mpr
      ((decidesInTime_twoPrefixEq.mem_iff_gameValue [true, false]).not.mp notMem_twoPrefixEq_tf),
    Bool.eq_false_iff.mpr
      ((decidesInTime_twoPrefixEq.mem_iff_gameValue []).not.mp notMem_twoPrefixEq_nil),
    twoPrefixEqATM.computableInSpace_gameValue runsInTime_twoPrefixEqATM⟩

/-- Stepwise `cfgAfter` and `gameValue_eq_true_iff` let an ordinary `module` client inspect
mid-game positions (`u = [true]`, after existential guess `true`). -/
example :
    twoPrefixEqATM.gameValue [true, true] 2 [true] = true ∧
      twoPrefixEqATM.gameValue [true, false] 2 [true] = false := by
  have hcfg (w : List Bool) :
      twoPrefixEqATM.cfgAfter w [true] =
        ⟨some (.all true), 1, fun _ _ => none, fun _ => 0, []⟩ := by
    rw [← twoPrefixEqATM.next_cfgAfter w [] true, twoPrefixEqATM.cfgAfter_nil, step_guess]
  rw [twoPrefixEqATM.gameValue_eq_true_iff, hcfg, acceptsWithin_two_all_iff,
    Bool.eq_false_iff, ne_eq, twoPrefixEqATM.gameValue_eq_true_iff, hcfg,
    acceptsWithin_two_all_iff]
  decide

/-! ### Complexity-class containment checks (`ATIME_subset_DSPACE` and `t(n) ≥ n`) -/

/-- `twoPrefixEq ∈ ATIME 1` transfers via `ATIME_subset_DSPACE` to `DSPACE (n + 1)`, and via
`ATIME_subset_DSPACE_of_le` (at `t n = n`, where `n ≤ t n`) to linear space `DSPACE id`. -/
example :
    twoPrefixEq ∈ ATIME encBits (fun _ => 1) ∧
      twoPrefixEq ∈ DSPACE encBits (fun n => n + 1) ∧
      twoPrefixEq ∈ DSPACE encBits id := by
  have hatime1 : twoPrefixEq ∈ ATIME encBits (fun _ => 1) :=
    ⟨0, 3, 0, TwoEqState, inferInstance, twoPrefixEqATM,
      decidesInTime_twoPrefixEq.mono fun _ => le_rfl⟩
  have hatimeN : twoPrefixEq ∈ ATIME encBits id :=
    ATIME_mono_of_le_mul_add (C := 1) (fun _ => by simp) hatime1
  exact ⟨hatime1, ATIME_subset_DSPACE hatime1, ATIME_subset_DSPACE_of_le (fun _ => le_rfl) hatimeN⟩

end CslibFrontierTests.AlternatingDeterministicSpace
