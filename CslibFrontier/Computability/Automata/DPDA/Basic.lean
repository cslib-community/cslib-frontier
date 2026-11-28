/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Automata.Acceptors.Acceptor
public import Mathlib.Logic.Relation

/-!
# Deterministic pushdown automata

A deterministic pushdown automaton has a finite control and a stack. A move replaces the top
stack symbol by a list of symbols and either reads one input symbol or takes an epsilon
transition. An enabled epsilon transition excludes every input transition for the same control
state and stack top. Acceptance requires a finite run that consumes the input and reaches a
final state. In the model of [Hopcroft et al., Sections 6.2 and 6.4][Hopcroft2006], the transition
table associates at most one result to each state, stack top and input label. The two cases of
`Option` represent no result or one result, and the `epsilon_exclusive` field enforces the
condition across different labels. The machine type leaves the alphabets and control type
generic. The DCFL predicate imposes finiteness.

## Main definitions

* `Cslib.Automata.DPDA` and `DPDA.Config` describe machines and configurations.
* `DPDA.Move` names the destination state and stack replacement in the transition table.
* `DPDA.step?` computes the next configuration, if any, and `DPDA.Step` is its graph.
* The `Acceptor` instance recognizes words by final state with the whole input consumed.

## Main results

* `DPDA.step_deterministic` gives uniqueness of the successor configuration.
* `DPDA.accepts_iff` gives the run characterization of acceptance.
-/

public section

namespace Cslib.Automata

/-- The result of a pushdown transition. -/
structure DPDA.Move (State Γ : Type*) where
  /-- The destination control state. -/
  state : State
  /-- The word replacing the stack top, with its new top first. -/
  replacement : List Γ

/-- A deterministic pushdown automaton with control states `State`, input symbols `Symbol`
and stack symbols `Γ`. The first symbol in a replacement list becomes the new stack top. -/
structure DPDA (State Symbol Γ : Type*) where
  /-- Initial control state. -/
  start : State
  /-- Initial stack symbol. -/
  bottom : Γ
  /-- Accepting control states. -/
  accept : Set State
  /-- A partial transition on a state, stack top and optional input symbol. -/
  transition : State → Γ → Option Symbol → Option (DPDA.Move State Γ)
  /-- When an epsilon transition is available, no input transition is available. -/
  epsilon_exclusive : ∀ q γ a, (transition q γ none).isSome → transition q γ (some a) = none

namespace DPDA

variable {State Symbol Γ : Type*}

/-- The control state, unread input and stack contents. The stack top is the head of the list. -/
structure Config (State Symbol Γ : Type*) where
  /-- The current control state. -/
  state : State
  /-- Input symbols still to be read. -/
  input : List Symbol
  /-- Stack contents, top first. -/
  stack : List Γ

/-- The configuration before reading any input. -/
@[expose] def initial (M : DPDA State Symbol Γ) (word : List Symbol) : Config State Symbol Γ :=
  ⟨M.start, word, [M.bottom]⟩

/-- Compute the unique enabled move. An empty stack admits no move. -/
@[expose] def step? (M : DPDA State Symbol Γ) (c : Config State Symbol Γ) :
    Option (Config State Symbol Γ) :=
  match c.stack with
  | [] => none
  | γ :: tail =>
    match M.transition c.state γ none with
    | some move => some ⟨move.state, c.input, move.replacement ++ tail⟩
    | none =>
      match c.input with
      | [] => none
      | a :: rest =>
        (M.transition c.state γ (some a)).map fun move =>
          ⟨move.state, rest, move.replacement ++ tail⟩

/-- The one-step transition relation on configurations. -/
@[expose] def Step (M : DPDA State Symbol Γ) (c d : Config State Symbol Γ) : Prop :=
  M.step? c = some d

/-- An epsilon transition updates the control and stack while preserving all unread input. -/
theorem step_of_epsilon {M : DPDA State Symbol Γ} {q : State} {γ : Γ} {move : Move State Γ}
    {input : List Symbol} {tail : List Γ}
    (h : M.transition q γ none = some move) :
    M.Step ⟨q, input, γ :: tail⟩ ⟨move.state, input, move.replacement ++ tail⟩ := by
  simp [Step, step?, h]

/-- An input transition reads the next symbol and updates the control and stack. -/
theorem step_of_symbol {M : DPDA State Symbol Γ} {q : State} {γ : Γ} {move : Move State Γ}
    {a : Symbol} {input : List Symbol} {tail : List Γ}
    (h : M.transition q γ (some a) = some move) :
    M.Step ⟨q, a :: input, γ :: tail⟩ ⟨move.state, input, move.replacement ++ tail⟩ := by
  cases he : M.transition q γ none with
  | none => simp [Step, step?, he, h]
  | some _ => exact absurd h (by simp [M.epsilon_exclusive q γ a (by simp [he])])

/-- Any two steps starting at the same configuration have the same target. -/
theorem step_deterministic {M : DPDA State Symbol Γ} {c d e : Config State Symbol Γ}
    (hd : M.Step c d) (he : M.Step c e) : d = e :=
  Option.some.inj (hd.symm.trans he)

instance : Acceptor (DPDA State Symbol Γ) Symbol where
  Accepts M word := ∃ q ∈ M.accept, ∃ stack,
    Relation.ReflTransGen M.Step (M.initial word) ⟨q, [], stack⟩

/-- A word is accepted when a finite run reads it completely and reaches an accepting state. -/
theorem accepts_iff (M : DPDA State Symbol Γ) (word : List Symbol) :
    Acceptor.Accepts M word ↔ ∃ q ∈ M.accept, ∃ stack,
      Relation.ReflTransGen M.Step (M.initial word) ⟨q, [], stack⟩ :=
  Iff.rfl

end DPDA

end Cslib.Automata
