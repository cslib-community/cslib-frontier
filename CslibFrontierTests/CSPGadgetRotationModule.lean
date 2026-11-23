/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Computability.PolyTime.CSP.Gadget.CertifiedRotation
import Lean.Elab.Command

/-!
# Ordinary runtime compiler clients without fine-grained counting imports

The native all-raw compiler certificate composes through an ordinary import for a finite fixed
source and arbitrary encoded target. Its runtime import closure has no FineGrained dependency.
The malformed binary successor case still executes the explicit invalid-certificate branch.
-/

public section

open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.CSP
open Cslib.Complexity.CSP.GadgetRotation Turing.MultiTapeTM

example {Src Rel : Type} [Finite Src] (encSrc : Src ↪ List Bool) (encRel : Rel ↪ List Bool)
    (srcArity : Src → ℕ) (B : ℕ) (templates : Src → CSP Rel (Bool × ℕ))
    (freeBlocks auxiliaryBlocks : Src → List (List ℕ)) :
    ComputableInPolyTime
      (fun p => (compile srcArity B templates freeBlocks auxiliaryBlocks p).2)
      (encCSPRotationCertificate encSrc encNat) Graph.encRotationCertificate :=
  (ComputableInPolyTime.snd (encCSP encRel encNat) Graph.encRotationCertificate).comp
    (computableInPolyTime_compile encSrc encRel srcArity B templates freeBlocks auxiliaryBlocks)

example : compile (fun (_ : Unit) => 2) 0
    (fun _ => ([⟨(), [(false, 0), (false, 1)]⟩] : CSP Unit (Bool × ℕ)))
    (fun _ => [[0], [1]]) (fun _ => [])
    ([⟨(), [7, 7]⟩], ⟨[2 ^ 100, 3, 0, 1]⟩) = ([], ⟨[0]⟩) := by
  rfl

open Lean Elab Command in
run_cmd do
  for name in (← getEnv).header.moduleNames do
    if (`CslibFrontier.Computability.Complexity.FineGrained).isPrefixOf name then
      throwError "runtime compiler imports fine-grained counting module {name}"
