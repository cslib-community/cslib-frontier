/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSAT
public import CslibFrontier.Foundations.Data.BitString.CyclicDifference
public import CslibFrontier.Foundations.Data.BitString.DeltaMatroid.Basic
import CslibFrontier.Computability.Complexity.Problems.CSP.Schaefer
import CslibFrontier.Computability.PolyTime.CSP.CyclicDifference.Spec
import CslibFrontier.Computability.PolyTime.CSP.Edge.Solver.Endpoint

/-!
# Native tractability with supplied ordered numerical rotations

The supplied-certificate problem has native polynomial-time deciders in the ordinary six
Schaefer cases and when every nonempty relation is self-complementary with an even-delta-matroid
cyclic difference. The latter composes the complete cyclic-difference compiler with the actual
explicit-table edge solver. No solver, target language, order or genus oracle is supplied by the
caller. The finite source language is fixed; the internal target uses the existing infinite
encoded table alphabet, including its actual stored rows.

These are results about supplied numerical genus-zero rotations that preserve original cyclic
argument order. They do not recognize or construct an unsupplied embedding. The assembly of the
existing compiler and solver is original library infrastructure; their modules record the
source mappings for the individual algorithms.

## Main results

* `Cslib.Complexity.RotationCSPSAT.mem_P_of_hasSchaeferPolymorphism`: the six ordinary cases.
* `Cslib.Complexity.RotationCSPSAT.mem_P_of_cyclicDifference`: the additional difference branch.
-/

public section

namespace Cslib.Complexity.RotationCSPSAT

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.BitString Turing.MultiTapeTM
open Cslib.Complexity.CSP

variable {Rel : Type} [Finite Rel]

/-- Each ordinary Schaefer case remains native polynomial-time with the supplied numerical
rotation and original cyclic order checked on every raw input. -/
theorem mem_P_of_hasSchaeferPolymorphism (encRel : Rel ↪ List Bool) (arity : Rel → ℕ)
    (sem : Rel → List Bool → Bool) (h : HasSchaeferPolymorphism arity sem) :
    RotationCSPSAT arity sem ∈ P (CSP.encRotationInstance encRel) := by
  obtain ⟨solve, hsolve, hcorrect⟩ := CSPSAT.mem_P_of_hasSchaeferPolymorphism encRel arity sem h
  have hcheck := (CSP.computableInPolyTime_verifyRotationCertificate encRel encNat).comp
    (show ComputableInPolyTime
      (fun I : CSP.RotationInstance Rel => (I.constraints, I.rotation))
      (CSP.encRotationInstance encRel) (CSP.encCSPRotationCertificate encRel encNat) by fun_prop)
  have hsolveInput := hsolve.comp (encRotationInstance_constraints_polyTime encRel .id')
  refine ⟨fun I => CSP.verifyRotationCertificate I.constraints I.rotation && solve I.constraints,
    ComputableInPolyTime.bool_and' hcheck hsolveInput, fun I => ?_⟩
  rw [Bool.and_eq_true, ← hcorrect]
  exact ⟨fun ⟨hw, hc, hs⟩ => ⟨hc, hw, hs⟩, fun ⟨hc, hw, hs⟩ => ⟨hw, hc, hs⟩⟩

/-- If every nonempty relation is self-complementary and its ordered cyclic difference is
an even delta-matroid, the supplied numerical-rotation problem is in native P. Empty relations
are allowed and rejected when they occur. The total compiler and edge solver are constructed
internally; the theorem assumes only the fixed language's mathematical criterion. -/
theorem mem_P_of_cyclicDifference (encRel : Rel ↪ List Bool) (arity : Rel → ℕ)
    (sem : Rel → List Bool → Bool)
    (hself : ∀ r, (booleanRelation arity sem r).Nonempty →
      IsSelfComplementary (booleanRelation arity sem r))
    (hdelta : ∀ r, (booleanRelation arity sem r).Nonempty →
      IsEvenDeltaMatroid (cyclicDifferenceRelation (booleanRelation arity sem r))) :
    RotationCSPSAT arity sem ∈ P (CSP.encRotationInstance encRel) := by
  classical
  have hselfAll (r : Rel) : IsSelfComplementary (booleanRelation arity sem r) := by
    by_cases hne : (booleanRelation arity sem r).Nonempty
    · exact hself r hne
    · have he := Set.not_nonempty_iff_eq_empty.mp hne
      rw [he]
      exact fun _ => Iff.rfl
  obtain ⟨hcompile, hcorrect⟩ := CSP.CyclicCompiler.compile_spec encRel arity sem hselfAll hdelta
  have hinput : ComputableInPolyTime
      (fun I : CSP.RotationInstance Rel => (I.constraints, I.rotation))
      (CSP.encRotationInstance encRel) (CSP.encCSPRotationCertificate encRel encNat) := by fun_prop
  have hmap := hcompile.comp hinput
  have hred : PolyTimeReducible (CSP.encRotationInstance encRel) (encCSP encTable encNat)
      (RotationCSPSAT arity sem) CSP.EdgeSolver.evenEdgeSAT := by
    refine ⟨fun I => CSP.CyclicCompiler.compile arity sem (I.constraints, I.rotation),
      hmap, fun I => ?_⟩
    obtain ⟨hedge, _, heven, hsat⟩ := hcorrect (I.constraints, I.rotation)
    change (_ ∧ _ ∧ _) ↔ _ ∧ _ ∧ _
    exact hsat.trans ⟨fun hs => ⟨hedge, heven, hs⟩, fun hs => hs.2.2⟩
  exact hred.mem_P CSP.EdgeSolver.evenEdgeSAT_mem_P

end Cslib.Complexity.RotationCSPSAT
