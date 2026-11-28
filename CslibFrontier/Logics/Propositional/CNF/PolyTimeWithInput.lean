/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Polynomial-time relabelling by a renaming computed from the input

`Cslib.Logic.PL.CNF.computableInPolyTime_relabel` renames the variables of a formula by a fixed
polynomial-time function. Here the formula and the renaming both depend on an input, as when a
reduction shifts the variables of a block of clauses into the block of its index
(`Cslib.Logic.PL.CNF.computableInPolyTime_relabelWithInput`). It is a separate module so that the
many clients of `CslibFrontier.Logics.Propositional.CNF.PolyTime` do not depend on it.

## Main results

* `Cslib.Logic.PL.CNF.computableInPolyTime_relabelWithInput`: relabelling a polynomial-time formula
  by a polynomial-time renaming that also reads the input.
-/

public section

namespace Cslib.Logic.PL

open Turing.MultiTapeTM ComputableInPolyTime

/-- Relabelling a formula that is computed from the input by a renaming computed from the input
is polynomial-time. -/
theorem CNF.computableInPolyTime_relabelWithInput {α V W : Type} {encIn : α ↪ List Bool}
    {encV : V ↪ List Bool} {encW : W ↪ List Bool} {φ : α → CNF V} {f : α → V → W}
    (hφ : ComputableInPolyTime φ encIn (encCNFOver encV))
    (hf : ComputableInPolyTime (fun p : α × V => f p.1 p.2) (encPair encIn encV) encW) :
    ComputableInPolyTime (fun a => (φ a).relabel (f a)) encIn (encCNFOver encW) := by
  unfold CNF.relabel Clause.relabel
  refine mapWithInput (f := fun a c => c.map (Prod.map (f a) id)) hφ ?_
  refine mapWithInput (f := fun (p : α × Clause V) (l : V × Bool) => Prod.map (f p.1) id l)
    (ComputableInPolyTime.snd _ _) ?_
  exact (hf.comp (((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)).prod
    ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _)))).prod
    ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _))

end Cslib.Logic.PL
