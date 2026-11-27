/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.BoundaryIdentify
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Relabel
public import CslibFrontier.Logics.Propositional.CSP.Planar.Construction.Gadget
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.AdjacentIdentification
import CslibFrontier.Foundations.Logic.Function.UpdateKernel
import CslibFrontier.Foundations.GroupTheory.Perm.Fin

/-!
# Adjacent equality restriction on the actual original-language body

The first two free labels are identified at the corners supplied by their consecutive probe
arguments. The duplicate probe marker is then deleted before actual-body extraction uses
distinct surviving ports. The body is exactly the existing `PPGadget.equalDrop`, with no
equality relation added to the language. This original static realization retains arbitrary
body degree, repeated occurrences, nullaries and closed components.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Cslib.Logic.PL.CSP Graph

variable {Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}

private theorem foldFirstTwo_kernel (n a : ℕ) (x y : Fin (n + 2) ⊕ Fin a) :
    Sum.map (Fin.cases (0 : Fin (n + 1)) id) id x =
      Sum.map (Fin.cases (0 : Fin (n + 1)) id) id y ↔
    Function.update id (Sum.inl (1 : Fin (n + 2))) (Sum.inl (0 : Fin (n + 2))) x =
      Function.update id (Sum.inl (1 : Fin (n + 2))) (Sum.inl (0 : Fin (n + 2))) y := by
  have hk (i j : Fin (n + 2)) :
      (Fin.cases 0 id : Fin (n + 2) → Fin (n + 1)) i =
        (Fin.cases 0 id : Fin (n + 2) → Fin (n + 1)) j ↔
      i = j ∨ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
    change _ ↔ i = j ∨ (i = 0 ∧ j = Fin.succ 0) ∨ (i = Fin.succ 0 ∧ j = 0)
    cases i using Fin.cases <;> cases j using Fin.cases <;>
      simp only [Fin.cases_zero, Fin.cases_succ, id_eq, Fin.succ_inj] <;> simp [eq_comm]
  rw [Function.update_id_apply_eq_iff]
  cases x with
  | inl x =>
    cases y with
    | inl y => simpa only [Sum.map_inl, Sum.inl.injEq] using hk x y
    | inr y => simp
  | inr x => cases y <;> simp

/-- Identify the first two free ports on exactly `PPGadget.equalDrop`. Their structural
probe arguments internally supply cofacial corners; the first duplicate marker is removed
before deriving the actual-body certificate with canonical distinct surviving free ports. -/
noncomputable def GadgetWitness.equalDrop {n : ℕ} {R : Set (Fin (n + 2) → Bool)}
    {g : PPGadget arity sem R} (w : GadgetWitness g) : GadgetWitness g.equalDrop := by
  let f : Fin (n + 2) ⊕ Fin g.numAux → Fin (n + 1) ⊕ Fin g.numAux :=
    Sum.map (Fin.cases 0 id) id
  have hv : (Sum.inl (0 : Fin (n + 2)) : Fin (n + 2) ⊕ Fin g.numAux) ≠ Sum.inl 1 := by
    simp
  have hk : ∀ a ∈ g.body.vars ++ List.ofFn Sum.inl,
      ∀ b ∈ g.body.vars ++ List.ofFn Sum.inl,
        f a = f b ↔ Function.update id (Sum.inl (1 : Fin (n + 2))) (Sum.inl 0) a =
          Function.update id (Sum.inl (1 : Fin (n + 2))) (Sum.inl 0) b := by
    intro a _ b _
    exact foldFirstTwo_kernel n g.numAux a b
  let h := w.identifyFirstTwoOfFn f hv hk
    (List.nodup_ofFn.mpr Sum.inl_injective)
  exact h

/-- The supplied adjacent-equality witness uses exactly the explicit outgoing swap and
bounded prefix restriction on the original raw table. No rotation search or embedding provider
appears in this generated-table equation. -/
theorem GadgetWitness.equalDrop_certificate {n : ℕ} {R : Set (Fin (n + 2) → Bool)}
    {g : PPGadget arity sem R} (w : GadgetWitness g) :
    w.equalDrop.certificate = equalDropCertificate g.body n w.certificate := by
  unfold GadgetWitness.equalDrop
  exact Witness.identifyFirstTwoOfFn_certificate _ _ _ _ _

end Cslib.Complexity.CSP.OrderedBoundary
