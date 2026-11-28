/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.Realization.WhileAbsorb
public import CslibFrontier.Computability.WordRAM.Realization.Reindex
public import CslibFrontier.Tactic.Realize

/-!
# Absorbed loop rules and `realize` tactic extension for `RealizesBounded`

Absorbed `iterate₀` and `while₀` rules for `Cslib.WordRAM.Realization.RealizesBounded`, together
with an `elab_rules` extension instantiating `Cslib.Tactic.Realize.elabRealize` directly on
`RealizesBounded` combinators without post-hoc proof translation.

## Main results

* `Cslib.WordRAM.Realization.RealizesBounded.iterate₀`,
  `Cslib.WordRAM.Realization.RealizesBounded.while₀`: absorbed frontier-bounded iteration and
  `boundedWhile` certificates when each step issues at least one memory query.
-/

public section

namespace Cslib.WordRAM.Realization.RealizesBounded

open Cslib.DataStructure

/-- Absorbed frontier-bounded `iterate₀` rule when every body issues at least one memory query. -/
theorem iterate₀ {δ : Type} {k l : ℕ} {σ : Type}
    (input : δ ↪ (Fin k → ℕ)) (output : σ ↪ (Fin l → ℕ))
    {body : δ × σ → Memory.Prog σ} {safe : ℕ → (δ × σ) → Memory.State → Prop}
    (h : RealizesBounded .exact body
      ((input.prodMap output).trans (Fin.appendEquiv k l).toEmbedding)
      output safe (fun _ _ => 0))
    (hquery : ∀ x s, 1 ≤ memoryCost (body x) s) :
    RealizesBounded .exact (fun ((d, a), fuel) => iterate body d fuel a)
      ((((input.prodMap output).trans (Fin.appendEquiv k l).toEmbedding).prodMap
        (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding).trans
          (Fin.appendEquiv (k + l) 1).toEmbedding) output
      (fun w ((d, a), fuel) s => iterationSafe body safe w d fuel a s) (fun _ _ => 0) :=
  (iterateRuntime input output h).mono_mul 1 fun ((d, a), fuel) s => by
    have := iterationWork_zero_le body hquery d fuel a s
    dsimp only
    omega

/-- Absorbed frontier-bounded `while₀` rule when every body issues at least one memory query. -/
theorem while₀ {δ σ : Type} {B : Basis} {k l : ℕ}
    (input : δ ↪ (Fin k → ℕ)) (output : σ ↪ (Fin l → ℕ)) (cond : Cond (k + l))
    (cutoff : δ × σ → ℕ) {body : δ × σ → Memory.Prog σ}
    {safe : ℕ → (δ × σ) → Memory.State → Prop}
    (h : RealizesBounded B body (appendWords input output) output safe (fun _ _ => 0))
    (hquery : ∀ x s, 1 ≤ memoryCost (body x) s) :
    RealizesBounded B (fun (d, a) => boundedWhile
      (fun d a => test cond ((appendWords input output) (d, a))) body d (cutoff (d, a)) a)
      (appendWords input output) output
      (fun w (d, a) s => whileSafe
        (fun d a => test cond ((appendWords input output) (d, a))) body safe w d
        (cutoff (d, a)) a s)
      (fun _ _ => 0) :=
  (whileBounded input output cond cutoff h).mono_mul 1 fun (d, a) s => by
    have := whileWork_zero_le (fun d a => test cond ((appendWords input output) (d, a))) body
      hquery d (cutoff (d, a)) a s
    dsimp only
    omega

end Cslib.WordRAM.Realization.RealizesBounded

public meta section

namespace Cslib.WordRAM

open Lean Meta Elab Tactic Cslib.WordRAM.Realization in
/-- Combinator bundle for frontier-bounded `RealizesBounded` goals. -/
private def boundedCombinators : Cslib.Tactic.Realize.Combinators where
  label := "RealizesBounded"
  cert := ``RealizesBounded
  consequenceWork := ``RealizesBounded.consequence_work
  consequenceValid := ``RealizesBounded.consequence_valid
  congr := ``RealizesBounded.congr
  reindex := ``RealizesBounded.reindex
  monoMul := ``RealizesBounded.mono_mul
  pure0 := ``RealizesBounded.pure₀
  bind0OfRun := ``RealizesBounded.bind₀_of_run
  bind := ``RealizesBounded.bind
  read := ``RealizesBounded.read
  write := ``RealizesBounded.write
  alloc := ``RealizesBounded.alloc
  allocDirty := ``RealizesBounded.allocDirty
  branch0 := ``RealizesBounded.branch₀
  branch := ``RealizesBounded.branch
  iterate0 := ``RealizesBounded.iterate₀
  iterateRuntime := ``RealizesBounded.iterateRuntime
  while0 := ``RealizesBounded.while₀
  whileBounded := ``RealizesBounded.whileBounded

open Lean Meta Elab Tactic Cslib.WordRAM.Realization in
/-- Extend `realize` to `RealizesBounded` goals directly via `Cslib.Tactic.Realize.elabRealize`. -/
elab_rules : tactic | `(tactic| realize) => withMainContext do
  let target ← instantiateMVars (← whnfR (← (← getMainGoal).getType))
  unless target.isAppOfArity ``RealizesBounded 10 do
    throwUnsupportedSyntax
  Cslib.Tactic.Realize.elabRealize boundedCombinators

end Cslib.WordRAM
