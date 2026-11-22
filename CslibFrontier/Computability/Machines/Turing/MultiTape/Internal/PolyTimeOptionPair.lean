/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives

/-!
# Pairing computed optional values

`ComputableInPolyTime.optionPair` assembles two computed optional fields into one optional pair.
It returns `none` when either field is absent, retains the original input for both computations,
and requires no inhabitant of either field type. The result uses the existing `encPair` layout
inside `encOption`.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Pair two computed optional values, preserving the original input for both field machines. -/
@[fun_prop] theorem optionPair {α β γ : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {encC : γ ↪ List Bool} {f : α → Option β} {g : α → Option γ}
    (hf : ComputableInPolyTime f encA (encOption encB))
    (hg : ComputableInPolyTime g encA (encOption encC)) :
    ComputableInPolyTime
      (fun a => (f a).elim none fun b => (g a).map fun c => (b, c))
      encA (encOption (encPair encB encC)) := by
  have hbody : ComputableInPolyTime
      (fun p : α × β => (g p.1).map fun c => (p.2, c))
      (encPair encA encB) (encOption (encPair encB encC)) :=
    optionMapWithInput (hg.comp (fst encA encB))
      (((snd encA encB).comp (fst (encPair encA encB) encC)).prod
        (snd (encPair encA encB) encC))
  exact hf.optionElimWithInput (const none) hbody

end Turing.MultiTapeTM.ComputableInPolyTime
