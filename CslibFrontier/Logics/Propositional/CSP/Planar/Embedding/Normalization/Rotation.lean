/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Normalization
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.BoundaryTransport

/-!
# Arbitrary cyclic starts for normalization

The literal `finCycle` used by normalization is an iteration of the positive one-step
boundary rotation. Only the starting position changes; argument chirality is preserved.
These are original numerical witness constructions, with no geometric recognition claim.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Cslib.Logic.PL.CSP

variable {Rel V : Type} [DecidableEq V]

private noncomputable def rotateIterate {F : CSP Rel V} {n : ℕ} {v : Fin n → V}
    (w : Witness F (List.ofFn v)) (hv : Function.Injective v) (k : ℕ) :
    Witness F (List.ofFn (v ∘ (finRotate n)^[k])) := by
  induction k with
  | zero => exact w
  | succ k ih =>
    let h := ih.rotateOfFn (List.nodup_ofFn.mpr
      (hv.comp ((finRotate n).injective.iterate k)))
    exact ⟨h.certificate, by
      simpa only [Function.iterate_succ, Function.comp_assoc] using h.accepted⟩

/-- Choose any cyclic start on a distinct actual boundary. This is positive cyclic
transport of the same body, including unused ports and arbitrary repeated body labels. -/
noncomputable def Witness.cycleOfFn {F : CSP Rel V} {n : ℕ} {v : Fin n → V}
    (w : Witness F (List.ofFn v)) (hv : Function.Injective v) (e : Fin n) :
    Witness F (List.ofFn (v ∘ finCycle e)) := by
  let h := rotateIterate w hv e.val
  exact ⟨h.certificate, by
    simpa only [finCycle_eq_finRotate_iterate] using h.accepted⟩

/-- Realize precisely normalization's arbitrary cyclic free-label map, rather than
only a single shift. The certificate comes entirely from the source witness. -/
noncomputable def GadgetWitness.normalizationRotate
    {arity : Rel → ℕ} {sem : Rel → List Bool → Bool} {n : ℕ}
    {R : Set (Fin n → Bool)} {g : PPGadget arity sem R}
    (w : GadgetWitness g) (e : Fin n) :
    GadgetWitness (g.relabelFree (finCycle e).symm) := by
  let h := (w.cycleOfFn Sum.inl_injective e).relabel
    (Sum.map (finCycle e).symm (id : Fin g.numAux → _))
    (fun _ _ _ _ he => (Sum.map_injective.mpr
      ⟨(finCycle e).symm.injective, Function.injective_id⟩) he)
  have hp : (List.ofFn ((Sum.inl : Fin n → Fin n ⊕ Fin g.numAux) ∘ finCycle e)).map
      (Sum.map (finCycle e).symm id) = List.ofFn Sum.inl := by
    rw [List.map_ofFn]
    congr 1
    funext i
    change Sum.inl ((finCycle e).symm (finCycle e i)) = Sum.inl i
    rw [Equiv.symm_apply_apply]
  refine ⟨h.certificate, ?_⟩
  change verify (g.body.relabel (Sum.map (finCycle e).symm id))
    (List.ofFn (Sum.inl : Fin n → Fin n ⊕ Fin g.numAux)) h.certificate = true
  rw [← hp]
  exact h.accepted

end Cslib.Complexity.CSP.OrderedBoundary
