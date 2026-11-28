/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- vendored: `spaceUsed` is the space of a run path since cslib #1133 and #1122
-- vendored: `whileInput` combines `tm` with a test machine through `combine`, as cslib #1151 builds
-- `repeatUntilBlank`

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Cursor
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.RepeatUntilBlank
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run.FirstStep
import CslibFrontier.Computability.Machines.Turing.MultiTape.Tactic.Step

/-!
# Repeating a machine while the input head reads a symbol

`whileInput tm` reads the symbol under the input head and halts if it is blank; otherwise it runs
`tm` and repeats. A body that consumes the input from left to right, leaving the input head after
what it read (`Turing.MultiTapeTM.TransformsTapesAt`), is thus run until the input is used up.

## Main definitions

* `Turing.MultiTapeTM.inputSymbolAt`: the symbol at a position of the input.
* `Turing.MultiTapeTM.WhileInput.inputTest`: the test of the input head.
* `Turing.MultiTapeTM.whileInput`: the loop, `tm` combined with the test.
* `Turing.MultiTapeMachine.whileInput`: the corresponding choice-free explicit transition table.

## Main results

* `Turing.MultiTapeTM.transformsTapesAt_combine_test`: loop specification for `tm` combined with a
  unit-state halting test.
* `Turing.MultiTapeTM.transformsTapesAt_whileInput`: a loop invariant preserved by every round
  gives a specification of `whileInput tm`, with the times of the rounds adding up.
* `Turing.MultiTapeMachine.toTM_whileInput`: forgetting the explicit table recovers the legacy
  loop.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The symbol at position `p` of the input tape holding `input`: blank at both ends. -/
@[expose] public def inputSymbolAt (input : List Symbol) (p : Fin (input.length + 2)) :
    Option Symbol :=
  if p.val = 0 then none else input[p.val - 1]?

public lemma inputSymbol_eq_inputSymbolAt (c : Cfg k Symbol State input) :
    c.inputSymbol = inputSymbolAt input c.inputPos := by
  unfold Cfg.inputSymbol inputSymbolAt
  have := c.inputPos.isLt
  split_ifs <;> grind

/-- The test of the input head: it halts if the input head reads a blank and otherwise stays in
its only state, moving no head. -/
public def WhileInput.inputTest : MultiTapeTM k Symbol Unit :=
  ofTr () fun _ inp _ =>
    { inputTape := 0, workTapes := fun _ => (none, 0), output := none,
      state := inp.map fun _ => () }

/-- `tm` combined with the test of the input head, which it starts with: the test halts the loop on
a blank and otherwise starts `tm`, and halting of `tm` returns to the test. -/
public noncomputable abbrev whileInput (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM k Symbol (State ⊕ Unit) :=
  combine tm WhileInput.inputTest (handOver ()) (Option.map fun _ => .inl tm.q₀) (.inr ())

-- upstream: vendored crei:crei/tidy-universal @9cce4cc7 (unsubmitted)
-- vendored: the two input-head lemmas below, from that revision's `Plumbing/WhileInput`

/-- A move to the left stops at the blank before the input. -/
@[simp] public lemma val_moveInputPos_neg {n : ℕ} (p : Fin (n + 2)) :
    (moveInputPos p (-1)).val = p.val - 1 := by
  have := val_moveInputPos_eq p (-1)
  simp only [SignType.coe_neg, SignType.coe_one] at this
  omega

/-- A move to the right stops at the blank after the input. -/
@[simp] public lemma val_moveInputPos_pos {n : ℕ} (p : Fin (n + 2)) :
    (moveInputPos p 1).val = min (p.val + 1) (n + 1) := by
  have := val_moveInputPos_eq p 1
  simp only [SignType.coe_one] at this
  omega

/-- One round of `combine tm test (handOver ()) f q₀`: once the test step hands over to `tm.q₀`,
running `tm` to a halted `wordsCfgAt` configuration within space `σ` returns to `.inr ()` in
`u + 1` steps (`u ≤ τ`) while keeping every head within `[-σ, σ]`. -/
public theorem ConfinedRun.exists_combine_round {test : MultiTapeTM k Symbol Unit}
    {tm : MultiTapeTM k Symbol State} {f : Option Unit → Option (State ⊕ Unit)}
    {q₀ : State ⊕ Unit} {start : Cfg k Symbol (State ⊕ Unit) input} {t : ℕ}
    {p p' : Fin (input.length + 2)} {w w' : Fin k → List Symbol} {out out' : List Symbol}
    {τ σ : ℕ}
    (hd : ConfinedRun (combine tm test (handOver ()) f q₀) start
      (wordsCfgAt input p (some (.inr ())) w out) t σ)
    (hstart : (combine tm test (handOver ()) f q₀).step
      (wordsCfgAt input p (some (.inr ())) w out) =
      (wordsCfgAt input p (some tm.q₀) w out).mapState (handOver ()))
    (hrun : tm.runFrom (wordsCfgAt input p (some tm.q₀) w out) τ =
      wordsCfgAt input p' none w' out')
    (hsp : (MultiTapeNTM.RunPath.ofDeterministic tm (wordsCfgAt input p (some tm.q₀) w out)
      τ).space ≤ σ) :
    ∃ u ≤ τ, ConfinedRun (combine tm test (handOver ()) f q₀) start
      (wordsCfgAt input p' (some (.inr ())) w' out') (t + (u + 1)) σ := by
  obtain ⟨u, hu, hhalt⟩ := exists_haltsAt (show (tm.runFrom _ τ).Halted by rw [hrun]; rfl)
  have hround :
      (combine tm test (handOver ()) f q₀).runFrom
        (wordsCfgAt input p (some (.inr ())) w out) (u + 1) =
      wordsCfgAt input p' (some (.inr ())) w' out' := by
    rw [runFrom_succ_eq_step, hstart, hhalt.runFrom_combine_left (handOver_some ()) le_rfl,
      ← hhalt.runFrom_eq hu, hrun]
    rfl
  refine ⟨u, hu, by rw [runFrom_add, hd.reaches, hround], fun l => ?_⟩
  rw [visitedByTapeHead_add, hd.reaches]
  refine Finset.union_subset (hd.confined l) (visitedByTapeHead_subset _ fun m hm => ?_)
  rcases m with _ | m
  · simp [runFrom]
  · rw [runFrom_succ_eq_step, hstart]
    obtain hlt | rfl := (Nat.lt_succ_iff.mp hm).lt_or_eq
    · rw [hhalt.runFrom_combine_left (handOver_some ()) hlt.le]
      exact visitedByTapeHead_subset_Icc _ rfl ((space_mono tm _ hu).trans hsp)
        (MultiTapeNTM.RunPath.mem_visitedByTapeHead_ofDeterministic.mpr ⟨m, by lia, rfl⟩)
    · rw [hhalt.runFrom_combine_left (handOver_some ()) le_rfl, ← hhalt.runFrom_eq hu, hrun]
      simp

/-- Let `P n` be a loop invariant after `n` rounds of `tm` combined with a unit-state test `test`
that steps according to `cont`: halting on `false` and handing over to `tm.q₀` on `true`. If each
round `n < rounds` starts with `cont` true and takes `P n` to `P (n + 1)` within `t n` steps and
`s` cells, and `P rounds` implies `cont` is false and `R` holds, then the combined loop takes
`P 0` to `R`. -/
public theorem transformsTapesAt_combine_test {test : MultiTapeTM k Symbol Unit}
    {tm : MultiTapeTM k Symbol State}
    {cont : (input : List Symbol) → Fin (input.length + 2) → (Fin k → List Symbol) → Bool}
    {P : ℕ → (input : List Symbol) → Fin (input.length + 2) → (Fin k → List Symbol) →
      List Symbol → Prop}
    {R : (input : List Symbol) → Fin (input.length + 2) → (Fin k → List Symbol) → List Symbol →
      Prop} {rounds : ℕ} {t : ℕ → ℕ} {s : ℕ}
    (hcheck : ∀ {input : List Symbol} (p : Fin (input.length + 2)) (ws : Fin k → List Symbol)
        (out : List Symbol),
      (combine tm test (handOver ()) (Option.map fun _ => .inl tm.q₀) (.inr ())).step
        (wordsCfgAt input p (some (.inr ())) ws out) =
        wordsCfgAt input p (if cont input p ws then some (.inl tm.q₀) else none) ws out)
    (hround : ∀ n < rounds, ∀ emitted, TransformsTapesAt tm
      (fun input p ws => P n input p ws emitted)
      (fun input _ _ p' ws' e => P (n + 1) input p' ws' (emitted ++ e)) (t n) s)
    (hmore : ∀ n < rounds, ∀ input p ws emitted, P n input p ws emitted → cont input p ws)
    (hend : ∀ input p ws emitted, P rounds input p ws emitted →
      cont input p ws = false ∧ R input p ws emitted) :
    TransformsTapesAt (combine tm test (handOver ()) (Option.map fun _ => .inl tm.q₀) (.inr ()))
      (fun input p ws => P 0 input p ws [])
      (fun input _ _ p' ws' emitted => R input p' ws' emitted)
      (∑ n ∈ Finset.range rounds, (t n + 1) + 1) (2 * k * s + k) := by
  let loop := combine tm test (handOver ()) (Option.map fun _ => .inl tm.q₀) (.inr ())
  intro input p ws out hP0
  rw [show loop.q₀ = .inr () from rfl]
  set start := wordsCfgAt (State := State ⊕ Unit) input p (some (.inr ())) ws out with hstart
  have hrec : ∀ n ≤ rounds, ∃ m ≤ ∑ j ∈ Finset.range n, (t j + 1),
      ∃ (pn : Fin (input.length + 2)) (wsn : Fin k → List Symbol) (acc : List Symbol),
      ConfinedRun loop start (wordsCfgAt input pn (some (.inr ())) wsn (out ++ acc)) m s ∧
        P n input pn wsn acc := by
    intro n hn
    induction n with
    | zero =>
      exact ⟨0, by simp, p, ws, [], ⟨by simp [runFrom, hstart], fun l => by
        simp [MultiTapeNTM.RunPath.visitedByTapeHead, MultiTapeNTM.RunPath.ofDeterministic,
          hstart, Finset.subset_iff]⟩, hP0⟩
    | succ n ih =>
      obtain ⟨m, hm, pn, wsn, acc, hc, hPn⟩ := ih (by lia)
      obtain ⟨pn', wsn', e, hrunTm, hQ, hsp⟩ := hround n (by lia) acc input pn wsn (out ++ acc) hPn
      have hgo : cont input pn wsn = true := hmore n (by lia) input pn wsn acc hPn
      obtain ⟨u, hu, hc'⟩ :=
        hc.exists_combine_round (by rw [hcheck, hgo]; rfl) hrunTm hsp
      rw [List.append_assoc] at hc'
      exact ⟨m + (u + 1), by rw [Finset.sum_range_succ]; lia, pn', wsn', acc ++ e, hc', hQ⟩
  obtain ⟨m, hm, pLast, wsLast, acc, hc, hPlast⟩ := hrec rounds le_rfl
  obtain ⟨hstop, hR⟩ := hend input pLast wsLast acc hPlast
  have hfinal : loop.runFrom start (m + 1) =
      wordsCfgAt input pLast none wsLast (out ++ acc) := by
    rw [runFrom_succ, hc.reaches, hcheck, hstop]
    rfl
  have hhalt : (loop.runFrom start (m + 1)).Halted := by rw [hfinal]; rfl
  refine ⟨pLast, wsLast, acc, ?_, hR, ?_⟩
  · rw [runFrom_eq_of_halt _ _ (by lia) hhalt, hfinal]
  · rw [space_eq_of_halt _ (by lia) hhalt]
    refine space_le_of_visited_subset_Icc _ _ fun l => ?_
    rw [visitedByTapeHead_add, hc.reaches]
    refine Finset.union_subset (hc.confined l) (visitedByTapeHead_subset _ fun j hj => ?_)
    rcases j with _ | j
    · simp [runFrom]
    · rw [runFrom_eq_of_halt (τ := 1) _ _ (by lia) (by rw [runFrom_one, hcheck, hstop]; rfl),
        runFrom_one, hcheck, hstop]
      simp

namespace WhileInput

variable {tm : MultiTapeTM k Symbol State}

/-- From the test, the machine halts on a blank and otherwise starts `tm`. -/
lemma step_check (p : Fin (input.length + 2)) (ws : Fin k → List Symbol) (out : List Symbol) :
    (whileInput tm).step (wordsCfgAt input p (some (.inr ())) ws out) =
      wordsCfgAt input p ((inputSymbolAt input p).map fun _ => .inl tm.q₀) ws out := by
  rw [step_of_state rfl, inputSymbol_eq_inputSymbolAt]
  cases h : inputSymbolAt input p <;>
    tm_step [combine, adaptedTr, inputTest, wordsCfgAt, h]

end WhileInput

open WhileInput in
/-- Let `P n` be a loop invariant after `n` rounds, on the input position, the words on the tapes
and the word emitted so far. If each round `n < rounds` starts on a symbol of the input and takes
`P n` to `P (n + 1)` within `t n` steps and `s` cells, and `P rounds` implies that the input head
is on a blank and that `R` holds, then `whileInput tm` takes `P 0` to `R`. -/
public theorem transformsTapesAt_whileInput {tm : MultiTapeTM k Symbol State}
    {P : ℕ → (input : List Symbol) → Fin (input.length + 2) → (Fin k → List Symbol) →
      List Symbol → Prop}
    {R : (input : List Symbol) → Fin (input.length + 2) → (Fin k → List Symbol) → List Symbol →
      Prop} {rounds : ℕ} {t : ℕ → ℕ} {s : ℕ}
    (hround : ∀ n < rounds, ∀ emitted, TransformsTapesAt tm
      (fun input p ws => P n input p ws emitted)
      (fun input _ _ p' ws' e => P (n + 1) input p' ws' (emitted ++ e)) (t n) s)
    (hmore : ∀ n < rounds, ∀ input p ws emitted, P n input p ws emitted →
      inputSymbolAt input p ≠ none)
    (hend : ∀ input p ws emitted, P rounds input p ws emitted →
      inputSymbolAt input p = none ∧ R input p ws emitted) :
    TransformsTapesAt (whileInput tm) (fun input p ws => P 0 input p ws [])
      (fun input _ _ p' ws' emitted => R input p' ws' emitted)
      (∑ n ∈ Finset.range rounds, (t n + 1) + 1) (2 * k * s + k) :=
  transformsTapesAt_combine_test (cont := fun input p _ => (inputSymbolAt input p).isSome)
    (fun p ws out => by rw [step_check]; cases inputSymbolAt _ p <;> rfl)
    hround
    (fun n hn input p ws emitted hP =>
      Option.isSome_iff_ne_none.mpr (hmore n hn input p ws emitted hP))
    (fun input p ws emitted hP =>
      let ⟨hb, hR⟩ := hend input p ws emitted hP
      ⟨by simp [hb], hR⟩)

end Turing.MultiTapeTM

namespace Turing.MultiTapeMachine

variable {k : ℕ} {Symbol State : Type}

/-- Repeat an explicit table while the physical input head reads a symbol. -/
public def whileInput (machine : MultiTapeMachine k Symbol State Empty Id) :
    MultiTapeMachine k Symbol (State ⊕ Unit) Empty Id :=
  ofTr (.inr ()) fun state input work =>
    match state with
    | .inl state =>
      let action := Action.emptyOracleEquiv (machine.tr state input work Empty.elim)
      { action with state := MultiTapeTM.handOver () action.state }
    | .inr () =>
      ⟨0, fun _ => (none, 0), none, input.map fun _ => .inl machine.initial⟩

/-- Forgetting the explicit input loop gives the established deterministic loop. -/
public theorem toTM_whileInput (machine : MultiTapeMachine k Symbol State Empty Id) :
    machine.whileInput.toTM = MultiTapeTM.whileInput machine.toTM := by
  rw [whileInput, toTM_ofTr]
  simp only [MultiTapeTM.whileInput, MultiTapeTM.combine]
  congr 1 with state input work : 3
  cases state with
  | inl state =>
      simp only [Sum.elim_inl, MultiTapeTM.adaptedTr, MultiTapeNTM.Adapter.mapState,
        id_eq, MultiTapeTM.tr_ofTr, toTM]
  | inr state =>
      obtain rfl := Subsingleton.elim state ()
      cases input <;>
        simp [MultiTapeTM.adaptedTr, MultiTapeNTM.Adapter.mapState,
          MultiTapeTM.WhileInput.inputTest, MultiTapeTM.tr_ofTr, toTM]

end Turing.MultiTapeMachine
