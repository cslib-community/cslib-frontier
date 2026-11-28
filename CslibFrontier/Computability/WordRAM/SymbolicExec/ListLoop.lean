/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.SymbolicExec.Havoc

/-!
# Loops that consume a list

Many loops of word-RAM programs take one element of a list per iteration: the words of an array
between a pointer and its end, the clauses of a formula, the indices below a bound. Their proofs
by induction on the list repeat the same steps: leave the loop on the empty list, enter it on a
nonempty one, run the body, and carry every fact the rest of the loop needs to the induction
hypothesis.

`Cslib.WordRAM.WP.loop_list` is that induction, once. Its invariant `I rest y` holds at the head of
an iteration with the elements `rest` left. The data there is the data `x` at the entry of the
loop with the registers the body writes, and memory, replaced (`Cslib.WordRAM.Data.havoc`), so the
invariant states those and nothing about the registers the body leaves alone: reads of them
reduce to reads in `x`. The elements may take different numbers of instructions; the loop takes
their sum, and two more for each test.

An invariant that says what is left to do needs no ghost state for what was done: for a loop
computing `f s l` from registers holding `s`, take
`I rest y := ∃ s', (the registers of y hold s') ∧ f s' rest = f s l`.

`wram_fold I over l cost T` applies the rule at a goal `WP w (.loop cond body) x Q` or
`∃ y, ExecWithin w (.loop cond body) x y n ∧ P y`, and simplifies the reads of the data at the
head of an iteration in the goals `exit`, `step` and `post` with `wram_simp`.

## Main definitions

* `wram_fold I over l cost T`: the list rule at a loop.

## Main results

* `Cslib.WordRAM.WP.loop_list`: a loop consuming a list, by an invariant on the elements left.
-/

public section

namespace Cslib.WordRAM

variable {B : Basis} {r : ℕ}

/-- **A loop consuming a list `l`**, one element per iteration. `I rest y` holds at the head of
an iteration with `rest` left: the loop is left when `rest` is empty (`exit`), and otherwise its
body leads, within `T a` instructions for the first element `a`, to data satisfying `I` for the
other elements (`step`). The data at the head of an iteration is the entry data `x` with the
registers the body writes, and memory, replaced. The loop takes the instructions of its bodies and
two for each test. -/
theorem WP.loop_list {w : ℕ} {cond : Cond r} {body : Code B r} {x : Data r}
    {Q : Data r → ℕ → Prop} {α : Type*} (I : List α → Data r → Prop) (T : α → ℕ) (l : List α)
    (init : I l x)
    (exit : ∀ v m, I [] (x.havoc body v m) → ¬cond.Holds (x.havoc body v m))
    (step : ∀ a as v m, I (a :: as) (x.havoc body v m) →
      cond.Holds (x.havoc body v m) ∧
        WP w body (x.havoc body v m) fun z t => t ≤ T a ∧ I as z)
    (post : ∀ v m, I [] (x.havoc body v m) →
      Q (x.havoc body v m) ((l.map fun a => T a + 2).sum + 2)) :
    WP w (.loop cond body) x Q := by
  suffices H : ∀ (l : List α) (v : Fin r → ℕ) (m : ℕ → ℕ), I l (x.havoc body v m) →
      ∃ v' m', ExecWithin w (.loop cond body) (x.havoc body v m) (x.havoc body v' m')
        ((l.map fun a => T a + 2).sum + 2) ∧ I [] (x.havoc body v' m') by
    obtain ⟨v', m', he, hI⟩ := H l x.regs x.mem (by rwa [Data.havoc_self])
    rw [Data.havoc_self] at he
    exact WP.of_execWithin he (post v' m' hI)
  intro l
  induction l with
  | nil =>
    intro v m hI
    exact ⟨v, m, (ExecWithin.loop_exit (exit v m hI)).mono (by simp), hI⟩
  | cons a as ih =>
    intro v m hI
    obtain ⟨hc, z, t, hz, ht, hIz⟩ := step a as v m hI
    have hzh : z = x.havoc body z.regs z.mem := by
      have := hz.eq_havoc
      rwa [Data.havoc_havoc] at this
    rw [hzh] at hz hIz
    obtain ⟨v', m', he, hI'⟩ := ih z.regs z.mem hIz
    refine ⟨v', m', (ExecWithin.loop_iter hc hz he).mono ?_, hI'⟩
    simp only [List.map_cons, List.sum_cons]
    omega

/-- `wram_fold I over l cost T` proves a loop that consumes the list `l`, one element per
iteration, from the invariant `I rest y` on the elements `rest` left and the data `y` at the head
of an iteration (`Cslib.WordRAM.WP.loop_list`), on a goal `WP w (.loop cond body) x Q` or
`∃ y, ExecWithin w (.loop cond body) x y n ∧ P y`. The body takes at most `T a` instructions on
the element `a`. It leaves four goals:

* `init`: the invariant holds at the entry, `I l x`;
* `exit`: `∀ v m, I [] y → ¬cond.Holds y`;
* `step`: `∀ a as v m, I (a :: as) y → cond.Holds y ∧ WP w body y fun z t => t ≤ T a ∧ I as z`;
* `post`: `∀ v m, I [] y → Q y n`, where `n` is the sum of `T a + 2` over `l`, plus two.

Here `y` is the entry data `x` with the registers the body writes replaced by `v` and memory by
`m`. In the last three goals the reads of `y` are simplified with `wram_simp`: a register the
body does not write is read in `x`, and the others are `v i`. Those of the three that this
closes are not left. The goals after the loop's goal are not touched and stay after these. -/
syntax (name := wramFold) "wram_fold " term:max &" over " term:max &" cost " term:max : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| wram_fold $I over $l cost $T) => withMainContext do
    let tail := (← getGoals).tail
    let (g, _, _) ← WP.Exec.toWP (← getMainGoal)
    setGoals [g]
    evalTactic (← `(tactic|
      refine Cslib.WordRAM.WP.loop_list (I := $I) (T := $T) $l ?init ?exit ?step ?post))
    let reads ← `(tactic|
      try wram_simp [Cslib.WordRAM.Cond.holds_lt, Cslib.WordRAM.Cond.holds_eq,
        List.length_nil, List.length_cons])
    let goals ← (← getGoals).mapM fun g => do
      if [`exit, `step, `post].contains (← g.getTag).eraseMacroScopes then
        evalTacticAt reads g
      else
        return [g]
    setGoals (goals.flatten ++ tail)

end Cslib.WordRAM

end
