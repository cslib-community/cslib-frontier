/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import all CslibFrontier.Crypto.Computational.SIS.SelfTargetFork

/-! # Tests for the classical self-target Module-SIS experiment -/

open Cslib Cslib.Crypto Cslib.Probability

/-- With no oracle queries, a solver that always outputs zero guesses the one-bit challenge
on its output point with probability one half. -/
example : (ModuleSIS.SelfTarget.game (Function.Embedding.refl (Fin 1 → ZMod 2)) 0
    (PMF.pure ()) (fun _ _ => pure ([], 0))
    (0 : Matrix (Fin 1) (Fin 1) (Fin 1 → ZMod 2))) true = 1 / 2 := by
  classical
  have fresh (p : ModuleSIS.SelfTarget.Point 1 1 2) :
      Protocols.ROMSignature.oracle (Fin 1 → ZMod 2) p [] =
        (PMF.uniformOfFintype (Fin 1 → ZMod 2)).bind fun c => PMF.pure (c, [(p, c)]) :=
    Protocols.ROMSignature.run_oracle_of_lookup_eq_none rfl
  simp [ModuleSIS.SelfTarget.game, ModuleSIS.SelfTarget.accepts, fresh,
    Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
    OracleComp.interpret_pure, PMF.uniformOfFintype_apply]
