/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @9cce4cc7 (unsubmitted)
-- vendored: `spaceUsed` is the space of a run path since cslib #1133 and #1122
-- vendored: `whileCond` combines `tm` with a test machine through `combine`, as cslib #1151 builds
-- `repeatUntilBlank`; the body of the test is exposed for the run law on arbitrary configurations
-- in `Plumbing/RunsBetween`

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WhileInput
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run.FirstStep
import CslibFrontier.Computability.Machines.Turing.MultiTape.Tactic.Step

/-!
# Repeating a machine while a condition holds

`whileCond c tm` reads the symbols under its heads and halts unless the condition `c` holds of them;
otherwise it runs `tm` and repeats. Unlike `Turing.MultiTapeTM.repeatUntilBlank`, the rounds may
leave the input head anywhere (`Turing.MultiTapeTM.TransformsTapesAt`), so the loop can drive a
two-way input head.

## Main definitions

* `Turing.MultiTapeTM.WhileCond.condTest`: the test of the condition.
* `Turing.MultiTapeTM.whileCond`: the loop, `tm` combined with the test.

## Main results

* `Turing.MultiTapeTM.transformsTapesAt_whileCond`: a loop invariant preserved by every round
  gives a specification of `whileCond c tm`, with the times of the rounds adding up.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The test of the condition `c`: it halts unless `c` holds of the symbols under the input head
and the work-tape heads, and otherwise stays in its only state, moving no head. -/
@[expose] public def WhileCond.condTest (c : Option Symbol → (Fin k → Option Symbol) → Bool) :
    MultiTapeTM k Symbol Unit :=
  ofTr () fun _ inp work =>
    { inputTape := 0, workTapes := fun _ => (none, 0), output := none,
      state := if c inp work then some () else none }

/-- `tm` combined with the test of `c`, which it starts with: the test halts the loop unless `c`
holds and otherwise starts `tm`, and halting of `tm` returns to the test. -/
public noncomputable abbrev whileCond (c : Option Symbol → (Fin k → Option Symbol) → Bool)
    (tm : MultiTapeTM k Symbol State) : MultiTapeTM k Symbol (State ⊕ Unit) :=
  combine tm (WhileCond.condTest c) (handOver ()) (Option.map fun _ => .inl tm.q₀) (.inr ())

/-- The condition `c` on the configuration with the input head at `p` and the words `ws` on the
work tapes, read at the start of each word. -/
@[expose] public def condAt (c : Option Symbol → (Fin k → Option Symbol) → Bool)
    (input : List Symbol) (p : Fin (input.length + 2)) (ws : Fin k → List Symbol) : Bool :=
  c (inputSymbolAt input p) fun j => (ws j).head?

namespace WhileCond

variable {c : Option Symbol → (Fin k → Option Symbol) → Bool} {tm : MultiTapeTM k Symbol State}

/-- From the test, the machine halts unless the condition holds, and otherwise starts `tm`. -/
lemma step_check (p : Fin (input.length + 2)) (ws : Fin k → List Symbol) (out : List Symbol) :
    (whileCond c tm).step (wordsCfgAt input p (some (.inr ())) ws out) =
      wordsCfgAt input p (if condAt c input p ws then some (.inl tm.q₀) else none) ws out := by
  have hsym : (wordsCfgAt (State := State ⊕ Unit) input p (some (.inr ())) ws
      out).workTapeSymbols = fun j => (ws j).head? := by
    funext j
    simp [Cfg.workTapeSymbols, wordsCfgAt, tapeOfList_zero]
  rw [step_of_state rfl, inputSymbol_eq_inputSymbolAt, hsym]
  rcases hc : condAt c input p ws <;> simp only [condAt] at hc <;>
    tm_step [combine, adaptedTr, condTest, hc, wordsCfgAt]

end WhileCond

open WhileCond in
/-- Let `P n` be a loop invariant after `n` rounds, on the input position, the words on the tapes
and the word emitted so far. If each round `n < rounds` starts with the condition holding and takes
`P n` to `P (n + 1)` within `t n` steps and `s` cells, and `P rounds` implies that the condition
fails and that `R` holds, then `whileCond c tm` takes `P 0` to `R`. -/
public theorem transformsTapesAt_whileCond {c : Option Symbol → (Fin k → Option Symbol) → Bool}
    {tm : MultiTapeTM k Symbol State}
    {P : ℕ → (input : List Symbol) → Fin (input.length + 2) → (Fin k → List Symbol) →
      List Symbol → Prop}
    {R : (input : List Symbol) → Fin (input.length + 2) → (Fin k → List Symbol) → List Symbol →
      Prop} {rounds : ℕ} {t : ℕ → ℕ} {s : ℕ}
    (hround : ∀ n < rounds, ∀ emitted, TransformsTapesAt tm
      (fun input p ws => P n input p ws emitted)
      (fun input _ _ p' ws' e => P (n + 1) input p' ws' (emitted ++ e)) (t n) s)
    (hmore : ∀ n < rounds, ∀ input p ws emitted, P n input p ws emitted → condAt c input p ws)
    (hend : ∀ input p ws emitted, P rounds input p ws emitted →
      condAt c input p ws = false ∧ R input p ws emitted) :
    TransformsTapesAt (whileCond c tm) (fun input p ws => P 0 input p ws [])
      (fun input _ _ p' ws' emitted => R input p' ws' emitted)
      (∑ n ∈ Finset.range rounds, (t n + 1) + 1) (2 * k * s + k) :=
  transformsTapesAt_combine_test (fun p ws out => step_check p ws out) hround hmore hend

end Turing.MultiTapeTM
