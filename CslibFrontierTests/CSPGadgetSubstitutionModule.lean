/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.Genus
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.AtomBoundary
public import CslibFrontier.Computability.PolyTime.CSP.Gadget.ConstructionCompiler

/-! Ordinary module clients of mathematical substitution and the native compiler.
Concrete repeated ports exercise exposed computations; the tree wrapper is used through
its public guard, semantic and framed polynomial certificates. -/

namespace CslibFrontierTests.CSPGadgetSubstitutionModule

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Complexity
open Cslib.Complexity.CSP Cslib.Complexity.CSP.GadgetRotation
open Cslib.Complexity.CSP.OrderedBoundary Turing.MultiTapeTM

private def arity (_ : Unit) : ℕ := 2
private def sem (_ : Unit) (_ : List Bool) : Bool := true
private def atom := PPGadget.atom (arity := arity) (sem := sem) ()
private def witness : GadgetWitness atom := Witness.atom arity sem ()
private def input : CSP Unit ℕ × Graph.RotationCertificate :=
  ([⟨(), [7, 7]⟩], ⟨[2, 3, 0, 1]⟩)

-- The mathematical endpoint accepts the actual replacement, without target invariants.
example : verifyRotationCertificate
    (replaceGadgets 0 (fun (_ : Unit) => atom.template) input.1)
    (replacementCertificate 0 (fun (_ : Unit) => atom.template)
      (fun _ => freeBoundaryBlocks atom witness)
      (fun _ => auxiliaryBoundaryBlocks atom witness) input.1 input.2) = true :=
  verifyRotationCertificate_replacementCertificate (fun _ => atom) (fun _ => witness)
    0 (fun _ => by rfl) input.1 (by decide) input.2 (by decide +kernel)

private def run := compile arity 0 (fun (_ : Unit) => atom.template)
  (fun _ => freeBoundaryBlocks atom witness) (fun _ => auxiliaryBoundaryBlocks atom witness)

-- Repeated variables retain their two positional incidences and literal successor table.
example : sourceGuard arity input = true := by decide +kernel
example : run input = ([⟨(), [14, 14]⟩], ⟨[2, 3, 0, 1]⟩) := by rfl
example : run (input.1, ⟨[2 ^ 250, 3, 0, 1]⟩) = ([], ⟨[0]⟩) := by rfl
example : sourceGuard arity ([⟨(), [7]⟩], ⟨[0, 1]⟩) = false := by decide +kernel

-- Fixed tree preprocessing need not be executable to use the public all-raw contracts.
private def trees (_ : Unit) : RelationMinor.Construction arity sem
    (booleanRelation arity sem ()) := .atom ()

example : verifyRotationCertificate (compileConstructions trees input).1
    (compileConstructions trees input).2 = true :=
  (verifyRotationCertificate_compileConstructions_iff trees input).mpr (by decide +kernel)

example : (compileConstructions trees input).1.Satisfiable sem :=
  ((wellFormed_certifiedSatisfiable_compileConstructions_iff trees input).mpr
    ⟨by decide, by decide +kernel, ⟨fun _ => false, by decide⟩⟩).2.2

example : compileConstructions trees (input.1, ⟨[0]⟩) = ([], ⟨[0]⟩) :=
  compileConstructions_of_sourceGuard_false trees _ (by decide +kernel)

example (encUnit : Unit ↪ List Bool) : ∃ c d : ℕ,
    (encCSPRotationCertificate encUnit encNat (compileConstructions trees input)).length ≤
      c * ((encCSPRotationCertificate encUnit encNat input).length + 1) ^ d := by
  obtain ⟨c, d, h⟩ := exists_framed_bound_compileConstructions encUnit encUnit trees
  exact ⟨c, d, h input⟩

/-- An ordinary module client can compose the all-raw certificate with body projection,
without imposing a finite target alphabet. -/
public theorem computableInPolyTime_projectedCompiler {Src Rel : Type} [Finite Src]
    {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
    {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool}
    (trees : ∀ r, RelationMinor.Construction arity sem (booleanRelation srcArity srcSem r))
    (encSrc : Src ↪ List Bool) (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun p => (compileConstructions trees p).1)
      (encCSPRotationCertificate encSrc encNat) (encCSP encRel encNat) :=
  (ComputableInPolyTime.fst (encCSP encRel encNat) Graph.encRotationCertificate).comp
    (computableInPolyTime_compileConstructions encSrc encRel trees)

end CslibFrontierTests.CSPGadgetSubstitutionModule
