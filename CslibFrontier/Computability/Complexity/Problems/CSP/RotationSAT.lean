/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.Basic
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Certificate
import CslibFrontier.Computability.Complexity.Classes.NP.Closure
import CslibFrontier.Computability.Complexity.Classes.NP.Witness

/-!
# CSP satisfiability with a supplied ordered numerical rotation

An input contains the original constraint list and a finite rotation-successor table. Acceptance
requires exact arities, the full numerical genus-zero and cyclic argument-order check, and a
satisfying assignment. The rotation is supplied, not existentially chosen or recognized. This
is a decision problem on raw inputs, including malformed certificates; it makes no geometric
realization or full planar recognition/dichotomy claim.

The relation alphabet and semantics are fixed. Variable names and successor indices are binary;
constraint positions, repeated variables, duplicate constraints and nullary scopes retain their
existing meanings. Every fixed finite relation alphabet gives native NP membership by combining
the existing CSP verifier with the native supplied-certificate checker. This assembly and its
record encoding are original library infrastructure.

## Main definitions

* `Cslib.Complexity.CSP.RotationInstance`: constraints and their supplied rotation certificate.
* `Cslib.Complexity.CSP.encRotationInstance`: framed constraints followed by the certificate.
* `Cslib.Complexity.RotationCSPSAT`: the guarded supplied-rotation satisfiability problem.

## Main results

* `Cslib.Complexity.RotationCSPSAT.mem_NP`: native NP membership for fixed finite languages.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

namespace CSP

/-- A raw CSP with a supplied numerical rotation certificate in its original argument order. -/
structure RotationInstance (Rel : Type) where
  /-- Original constraints, with arbitrary binary natural-number variable names. -/
  constraints : CSP Rel ℕ
  /-- Successor table checked for numerical genus zero and cyclic argument order. -/
  rotation : Graph.RotationCertificate

variable {Rel : Type}

/-- Binary variable names and successor indices: framed `encCSP` constraints first, followed
by the rotation certificate's encoded successor list, with no additional tag or grouping. -/
enc_structure encRotationInstance (encRel : Rel ↪ List Bool) : RotationInstance Rel where
  constraints : (encCSP encRel encNat),
  rotation : Graph.encRotationCertificate

end CSP

/-- Exact-arity satisfiable CSPs whose supplied numerical rotation passes the complete
genus-zero and cyclic argument-order checker. This does not recognize an unsupplied embedding. -/
@[expose] def RotationCSPSAT {Rel : Type} (arity : Rel → ℕ)
    (sem : Rel → List Bool → Bool) : Set (CSP.RotationInstance Rel) :=
  {I | I.constraints.WellFormed arity ∧
    CSP.verifyRotationCertificate I.constraints I.rotation = true ∧ I.constraints.Satisfiable sem}

namespace RotationCSPSAT

open Cslib.Complexity.CSP

/-- Supplied ordered numerical rotation CSP satisfiability belongs to native NP for every
fixed finite Boolean language, with binary names and the complete framed record encoding. -/
theorem mem_NP {Rel : Type} [Finite Rel] (encRel : Rel ↪ List Bool) (arity : Rel → ℕ)
    (sem : Rel → List Bool → Bool) :
    RotationCSPSAT arity sem ∈ NP (CSP.encRotationInstance encRel) := by
  open scoped RotationInstance in
  have hforget : PolyTimeReducible (CSP.encRotationInstance encRel) (encCSP encRel encNat)
      {I : CSP.RotationInstance Rel | I.constraints ∈ CSPSAT arity sem} (CSPSAT arity sem) :=
    ⟨CSP.RotationInstance.constraints, by fun_prop, fun _ => Iff.rfl⟩
  have hcheck : ComputableInPolyTime
      (fun I : CSP.RotationInstance Rel => CSP.verifyRotationCertificate I.constraints I.rotation)
      (CSP.encRotationInstance encRel) Turing.MultiTapeTM.encBool :=
    (CSP.computableInPolyTime_verifyRotationCertificate encRel Turing.MultiTapeTM.encNat).comp
      (g := fun I : CSP.RotationInstance Rel => (I.constraints, I.rotation))
      (by unfold CSP.encCSPRotationCertificate; fun_prop)
  apply mem_NP_of_guard hcheck (hforget.mem_NP (CSPSAT.mem_NP encRel arity sem))
  intro I
  exact ⟨fun ⟨hw, hc, hs⟩ => ⟨hc, hw, hs⟩, fun ⟨hc, hw, hs⟩ => ⟨hw, hc, hs⟩⟩

end RotationCSPSAT

end Cslib.Complexity
