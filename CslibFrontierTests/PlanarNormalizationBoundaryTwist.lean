/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Normalization

/-! Literal twist and completed Construction clients. Noncomputable witnesses are used as
proofs of acceptance; only the displayed explicit tables and coordinate maps execute by kernel
decision. Flipped ports retain their allocated but unused middle labels.
-/

namespace CslibFrontierTests.PlanarNormalizationBoundaryTwist

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.BitString
open Cslib.Logic.PL.CSP.Normalization Cslib.Complexity.CSP.OrderedBoundary

noncomputable section

example : GadgetWitness (twistGadget (Set.univ : Set (Fin 0 → Bool)) Fin.elim0) :=
  twistBodyWitness _

example : GadgetWitness (twistGadget (Set.univ : Set (Fin 1 → Bool)) (fun _ => false)) :=
  twistBodyWitness _

example : GadgetWitness (twistGadget (Set.univ : Set (Fin 1 → Bool)) (fun _ => true)) :=
  twistBodyWitness _

example : GadgetWitness (twistGadget (Set.univ : Set (Fin 3 → Bool)) ![false, true, false]) :=
  twistBodyWitness _

example : twistBody (n := 0) Fin.elim0 = [⟨.relation, []⟩] := rfl

example : twistBody (fun _ : Fin 1 => true) =
    [⟨.relation, [.inr 0]⟩, ⟨.disequality, [.inr 0, .inl 0]⟩] := rfl

example : twistBody (fun _ : Fin 1 => false) =
    [⟨.relation, [.inr 0]⟩, ⟨.disequality, [.inr 0, .inr 1]⟩,
      ⟨.disequality, [.inr 1, .inl 0]⟩] := rfl

-- Complete actual-body/probe checking of literal tables, including the empty twist.
example : verify (twistBody (n := 0) Fin.elim0) (List.ofFn Sum.inl) ⟨[]⟩ = true := by
  decide +kernel

example : verify (twistBody (fun _ : Fin 1 => true)) (List.ofFn Sum.inl)
    ⟨[2, 1, 0, 5, 6, 3, 4, 7]⟩ = true := by decide +kernel

example : verify (twistBody (fun _ : Fin 1 => false)) (List.ofFn Sum.inl)
    ⟨[2, 1, 0, 5, 6, 3, 4, 9, 10, 7, 8, 11]⟩ = true := by decide +kernel

example : verify (twistBody (fun _ : Fin 2 => true)) (List.ofFn Sum.inl)
    ⟨[4, 3, 8, 1, 0, 7, 14, 5, 2, 11, 12, 9, 10, 15, 6, 13]⟩ = true := by decide +kernel

example : verify (twistBody (fun _ : Fin 2 => false)) (List.ofFn Sum.inl)
    ⟨[4, 3, 12, 1, 0, 7, 8, 5, 6, 11, 22, 9, 2, 15, 16, 13, 14, 19, 20, 17,
      18, 23, 10, 21]⟩ = true := by decide +kernel

example : verify (twistBody ![true, false]) (List.ofFn Sum.inl)
    ⟨[4, 3, 8, 1, 0, 7, 18, 5, 2, 11, 12, 9, 10, 15, 16, 13, 14, 19, 6, 17]⟩ = true := by
  decide +kernel

-- A reflected original ternary row must not pass the positive argument-order check.
example : verify (twistBody ![false, true, false]) (List.ofFn Sum.inl)
    ⟨[6, 3, 14, 5, 18, 1, 0, 9, 10, 7, 8, 13, 30, 11, 2, 17, 28, 15,
      4, 21, 22, 19, 20, 25, 26, 23, 24, 29, 16, 31, 12, 27]⟩ = true := by
  decide +kernel

example : Cslib.Complexity.CSP.verifyArgumentOrder
    (probeBody (twistBody ![false, true, false]) (List.ofFn Sum.inl))
      ⟨[6, 5, 14, 1, 18, 3, 0, 9, 10, 7, 8, 13, 30, 11, 2, 17, 28, 15,
        4, 21, 22, 19, 20, 25, 26, 23, 24, 29, 16, 31, 12, 27]⟩ = false := by
  decide +kernel

-- Flipped middle labels remain allocated and do not occur in the literal body.
example : (Sum.inr (3 : Fin 4) : Fin 2 ⊕ Fin 4) ∉ (twistBody ![false, true]).vars := by
  decide +kernel

example (R : Set (Fin 2 → Bool)) : (twistGadget R (fun _ => true)).numAux = 4 := rfl

example {n : ℕ} {R : Set (Fin n → Bool)} (c : Construction R) :
    verify c.gadget.body (List.ofFn Sum.inl) c.orderedWitness.certificate = true ∧
      c.gadget.numAux ≤ 3 * n - 4 :=
  ⟨c.orderedWitness.accepted, c.numAux_bound⟩

-- The original existence theorem now supplies an actual accepted ordered gadget too.
example {n : ℕ} (R : Set (Fin n → Bool)) (hne : R.Nonempty)
    (hself : IsSelfComplementary R)
    (hfail : ¬IsEvenDeltaMatroid (cyclicDifferenceRelation R)) :
    ∃ c : Construction R, Nonempty (GadgetWitness c.gadget) := by
  obtain ⟨_, ⟨c⟩⟩ := exists_construction R hne hself hfail
  exact ⟨c, ⟨c.orderedWitness⟩⟩

end

end CslibFrontierTests.PlanarNormalizationBoundaryTwist
