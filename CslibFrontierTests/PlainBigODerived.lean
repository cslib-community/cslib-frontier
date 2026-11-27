/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Cases
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Lists

/-! # Plain derived resource rules

Ordinary imports exercise branch-specific time and charged workspace independently.
The deleted private provider names are checked in the environment, rather than by name lookup
outside their original module (which would also reject a surviving private declaration).
-/

open Turing.MultiTapeTM

example {π α β ε : Type} {encP : π ↪ List Bool} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {encE : ε ↪ List Bool}
    {f : π × α → ε} {g : π × β → ε} {Tf Sf : π × α → ℕ} {Tg Sg : π × β → ℕ}
    (hf : ComputableInO f (encPair encP encA) encE Tf Sf)
    (hg : ComputableInO g (encPair encP encB) encE Tg Sg) :
    ComputableInO
      (fun p : π × (α ⊕ β) => p.2.elim (fun a => f (p.1, a)) (fun b => g (p.1, b)))
      (encPair encP (encSum encA encB)) encE
      (fun p => (encPair encP (encSum encA encB) p).length +
        p.2.elim (fun a => Tf (p.1, a)) (fun b => Tg (p.1, b)))
      (fun p => (encPair encP (encSum encA encB) p).length +
        p.2.elim (fun a => Sf (p.1, a)) (fun b => Sg (p.1, b))) :=
  ComputableInO.sumElimSnd hf hg

example : ComputableInO (fun l : List Bool => l.length) encBits encNat
    (fun l => l.length) (fun l => l.length) := ComputableInO.lengthNat

run_cmd do
  let env ← Lean.getEnv
  for (name, _) in env.constants.toList do
    if name.toString.endsWith ".sumElimSnd_tidy" ||
        name.toString.endsWith ".optionElimSnd_tidy" then
      throwError "superseded private case provider survives: {name}"
