/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Calls that keep the registers a routine does not write

`wram_call spec with y post` continues from a routine's contract with data `y` about which only
the contract's conclusion is known. A register the routine never writes keeps its contents
(`Cslib.WordRAM.ExecWithin.regs_eq`), but the continuation does not see that: every contract
restates the registers its caller still needs, and every caller passes them on by hand.

`x.havoc c v m` is the data reached from `x` by a run of `c` about which nothing else is known:
the registers `c` does not write hold what they hold in `x`, the others hold `v`, and memory is
`m`. Every run of `c` from `x` ends in such data (`Cslib.WordRAM.ExecWithin.eq_havoc`). Reading a
register of it is decided by evaluating `c.Preserves i`, so `wram_exec` and `wram_simp` reduce a
read of an unwritten register to the read in `x`, and through the earlier writes to its value,
with the simp set they already use.

`wram_call spec framed with v m post` is `wram_call` with the data reached in this form
(`Cslib.WordRAM.WP.of_spec_havoc`). The contract may leave its hypotheses out, as in
`wram_call (routine_spec a b ..) framed with v m post`: each is simplified with `wram_simp` and
the given lemmas and proved by a hypothesis, by `fits` or by `omega`, and those that remain
follow the continuation as goals. The contract's conclusion is simplified in the same way
before `post` names its parts, so that it speaks of `v`, `m` and the caller's data.

## Main definitions

* `Cslib.WordRAM.Data.havoc`: the data after a run of a program, with the registers it does not
  write kept.
* `wram_call … framed with v m post`: continue from a contract, keeping those registers.

## Main results

* `Cslib.WordRAM.ExecWithin.eq_havoc`: a run of `c` from `x` ends in `x.havoc c v m`.
* `Cslib.WordRAM.WP.of_spec_havoc`: the rule of the framed call.
-/

public section

namespace Cslib.WordRAM

variable {B : Basis} {r : ℕ}

/-- The data `x` after a run of `c` about which nothing else is known: the registers `c` does not
write keep their contents, the others hold `v`, and memory is `m`. -/
def Data.havoc (c : Code B r) (x : Data r) (v : Fin r → ℕ) (m : ℕ → ℕ) : Data r :=
  ⟨fun i => if c.Preserves i then x.regs i else v i, m⟩

namespace Data

variable {c : Code B r} {i : Fin r}

/-- A register the program does not write keeps its contents. -/
@[wram_simps]
theorem havoc_regs_of_preserves (h : c.Preserves i) (x : Data r) (v : Fin r → ℕ) (m : ℕ → ℕ) :
    (x.havoc c v m).regs i = x.regs i := by
  simp [havoc, h]

/-- A register the program writes holds its new contents. -/
@[wram_simps]
theorem havoc_regs_of_not_preserves (h : ¬c.Preserves i) (x : Data r) (v : Fin r → ℕ)
    (m : ℕ → ℕ) : (x.havoc c v m).regs i = v i := by
  simp [havoc, h]

/-- The memory after the run. -/
@[wram_simps]
theorem havoc_mem (c : Code B r) (x : Data r) (v : Fin r → ℕ) (m : ℕ → ℕ) :
    (x.havoc c v m).mem = m := by
  rfl

/-- Data is the data after a run that changes nothing. -/
theorem havoc_self (c : Code B r) (x : Data r) : x.havoc c x.regs x.mem = x := by
  ext j
  · simp [havoc]
  · rfl

/-- A second run of the same program writes the same registers. -/
theorem havoc_havoc (c : Code B r) (x : Data r) (v v' : Fin r → ℕ) (m m' : ℕ → ℕ) :
    (x.havoc c v m).havoc c v' m' = x.havoc c v' m' := by
  ext j
  · simp only [havoc]
    split <;> simp_all
  · rfl

end Data

/-- **A run of `c` from `x` ends in `x.havoc c v m`**, for the registers and memory reached. -/
theorem ExecWithin.eq_havoc {w T : ℕ} {c : Code B r} {x y : Data r}
    (h : ExecWithin w c x y T) : y = x.havoc c y.regs y.mem := by
  ext j
  · simp only [Data.havoc]
    split
    · exact h.regs_eq ‹_›
    · rfl
  · rfl

/-- Continue from a routine's contract at its instruction allowance. The data reached is the
caller's with the registers the routine writes, and memory, replaced. -/
theorem WP.of_spec_havoc {w T : ℕ} {c : Code B r} {x : Data r} {P : Data r → Prop}
    {Q : Data r → ℕ → Prop} (h : ∃ y, ExecWithin w c x y T ∧ P y)
    (hQ : ∀ v m, P (x.havoc c v m) → Q (x.havoc c v m) T) : WP w c x Q := by
  obtain ⟨y, hy, hP⟩ := h
  have he := hy.eq_havoc
  exact WP.of_execWithin hy (he ▸ hQ y.regs y.mem (he ▸ hP))

/-- Apply a routine contract and keep the registers the routine does not write: the data reached
is the caller's data `x` with the registers the routine writes replaced by `v` and memory by `m`
(`x.havoc c v m`), so `wram_exec` and `wram_simp` reduce later reads of the other registers to
their values in `x`. Hypotheses the contract leaves out, as in `(routine_spec a b ..)`, are
simplified with `wram_simp` and the given lemmas and proved by a hypothesis, up to reducible
unfolding, or by `fits` or `omega`; those that remain follow the continuation. The contract's
conclusion is simplified in the same way before the patterns after `v` and `m` name its parts. -/
tactic_extension wramCall

@[tactic_alt wramCall]
syntax (name := wramCallFramed) "wram_call " term:max &" framed"
  (" [" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
    Lean.Parser.Tactic.simpLemma),* "]")? " with" (ppSpace colGt rintroPat)+ : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| wram_call $h framed $[[$args,*]]? with $pats*) => do
    let tail := (← getGoals).tail
    try
      withoutRecover <| refineCore (← `(Cslib.WordRAM.WP.of_spec_havoc $h ?cont)) `wram_call
        (allowNaturalHoles := true)
    catch ex =>
      throwError "wram_call: the contract does not apply to the goal{indentExpr (← getMainTarget)}\
        \nFor the goal `WP w c x Q`, the framed form takes a contract of type \
        `∃ y, ExecWithin w c x y T ∧ P y`, possibly with hypotheses left out by `..`.\n\
        {ex.toMessageData}"
    let goals := (← getGoals).take ((← getGoals).length - tail.length)
    let some cont ← goals.findM? fun g => return (← g.getTag).eraseMacroScopes == `cont
      | throwError "wram_call: no continuation"
    let simpArgs := args.map (·.getElems.map (·.raw)) |>.getD #[]
    let disch ← `(Lean.Parser.Tactic.tacticSeq|
      first | with_reducible assumption | fits | omega)
    let sideGoals ← IO.mkRef #[]
    WP.Exec.withSimpContext disch simpArgs fun ctx simprocs simpDischarge => do
      let cfg : WP.Exec.Config :=
        { ctx, simprocs, simpDischarge, disch := ← `(tactic| ($disch)), sideGoals,
          steps := ← IO.mkRef 0, split := false }
      for g in goals do
        if g == cont || (← g.isAssigned) then continue
        g.withContext do
          if ← isProp (← g.getType) then
            WP.Exec.sidePremise cfg (← g.getTag) (mkMVar g)
          else
            sideGoals.modify (·.push g)
    setGoals [cont]
    match args with
    | some args => evalTactic (← `(tactic| try wram_simp [$args,*]))
    | none => evalTactic (← `(tactic| try wram_simp))
    evalTactic (← `(tactic| rintro $pats*))
    setGoals ((← getGoals) ++ (← sideGoals.get).toList ++ tail)

end Cslib.WordRAM

end
