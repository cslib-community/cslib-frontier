/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.Task

/-!
# Runs of automata on tapes and inputs

A letter of a run is `none` (idle) or `some (ch, γ)` (a letter `γ` on channel `ch`). The value of
an automaton at an input `u` is the sum, over all runs of length `t` that emit the same word on
both sides of every tape and the input on each input channel (`Tape.Matched`), of their weights
(`Tape.runVal`).

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Tape.Run`.

## Main definitions

* `Tape.Letter`: `Option (Ch S J × Γ)`.
* `Tape.emit`: channel words emitted by a run.
* `Tape.Matched`: predicate that both sides of each tape agree and input channels equal `u`.
* `Tape.runVal`: sum of matrix-product weights over matched runs of length `t`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Tape

open Cslib.Automata.Weighted

/-- A letter emitted at one step of an automaton run (`none` is idle). -/
abbrev Letter (S J Γ : Type*) := Option (Ch S J × Γ)

/-- The words emitted on each channel by a run. -/
@[expose] def emit {Γ S J : Type*} [DecidableEq S] [DecidableEq J]
    (o : List (Letter S J Γ)) : Ch S J → List Γ :=
  proj o.reduceOption

/-- The run is matched at input `u`: both sides of every tape agree, and the input channels emit
`u`. -/
@[expose] def Matched {Γ S J : Type*} [DecidableEq S] [DecidableEq J]
    (o : List (Letter S J Γ)) (u : J → List Γ) : Prop :=
  (∀ s, emit o (.tp s false) = emit o (.tp s true)) ∧ ∀ j, emit o (.inp j) = u j

instance instDecidableMatched {Γ S J : Type*} [DecidableEq Γ] [Fintype S] [DecidableEq S]
    [Fintype J] [DecidableEq J] (o : List (Letter S J Γ)) (u : J → List Γ) :
    Decidable (Matched o u) := by
  unfold Matched; infer_instance

/-- The value of an automaton with transition matrices `mu`, initial state `i`, and final state `e`
at input `u`: the sum of run weights over matched runs of length `t`. -/
@[expose] def runVal {F Γ S J Q : Type*} [CommRing F] [Fintype Γ] [DecidableEq Γ]
    [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J] [Fintype Q] [DecidableEq Q]
    (mu : Letter S J Γ → Matrix Q Q F) (i e : Q) (t : ℕ) (u : J → List Γ) : F :=
  ∑ o : Fin t → Letter S J Γ,
    if Matched (List.ofFn o) u then ((List.ofFn o).map mu).prod i e else 0

end Cslib.Circuits.Arithmetic.Separation.Tape
