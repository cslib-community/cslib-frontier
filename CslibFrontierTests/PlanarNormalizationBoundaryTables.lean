/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Normalization
import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.DegreeTwo

/-! Literal expected tables of noncomputable witness constructors. Uniqueness derives the
identities from accepted tables and variable fibers of size at most two; the displayed
tables execute with kernel decision. No noncomputable preprocessing is claimed to execute.
-/

namespace CslibFrontierTests.PlanarNormalizationBoundaryTables

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Complexity.CSP
open Cslib.Logic.PL.CSP.Normalization Cslib.Complexity.CSP.OrderedBoundary
open Cslib.Complexity.Graph

private theorem table_eq {Rel V : Type} [DecidableEq V] {F : CSP Rel V} {ports : List V}
    (w : Witness F ports) (c : RotationCertificate)
    (hdegree : ∀ d : Dart (incidenceGraph (probeBody F ports)), d.2 = false →
      (Finset.univ.filter fun e : Dart (incidenceGraph (probeBody F ports)) =>
        e.vertex = d.vertex).card ≤ 2)
    (hc : verify F ports c = true) : w.certificate = c := by
  obtain ⟨hw, _, hwo⟩ := (verifyRotationCertificate_eq_true_iff _ _).mp w.probe_accepted
  have hprobe := ((verify_eq_true_iff F ports c).mp hc).2
  obtain ⟨hc, _, hco⟩ := (verifyRotationCertificate_eq_true_iff _ _).mp hprobe
  exact rotationCertificate_eq_of_variable_degree_le_two hdegree hw hc
    ((verifyArgumentOrder_eq_true_iff hw).mpr hwo) ((verifyArgumentOrder_eq_true_iff hc).mpr hco)

example : (twistBodyWitness (n := 0) Fin.elim0).certificate = ⟨[]⟩ :=
  table_eq _ _ (by decide +kernel) (by decide +kernel)

example : (twistBodyWitness (fun _ : Fin 1 => true)).certificate =
    ⟨[2, 1, 0, 5, 6, 3, 4, 7]⟩ :=
  table_eq _ _ (by decide +kernel) (by decide +kernel)

example : (twistBodyWitness (fun _ : Fin 1 => false)).certificate =
    ⟨[2, 1, 0, 5, 6, 3, 4, 9, 10, 7, 8, 11]⟩ :=
  table_eq _ _ (by decide +kernel) (by decide +kernel)

example : (twistBodyWitness (fun _ : Fin 2 => true)).certificate =
    ⟨[4, 3, 8, 1, 0, 7, 14, 5, 2, 11, 12, 9, 10, 15, 6, 13]⟩ :=
  table_eq _ _ (by decide +kernel) (by decide +kernel)

example : (twistBodyWitness (fun _ : Fin 2 => false)).certificate =
    ⟨[4, 3, 12, 1, 0, 7, 8, 5, 6, 11, 22, 9, 2, 15, 16, 13, 14, 19, 20, 17,
      18, 23, 10, 21]⟩ := table_eq _ _ (by decide +kernel) (by decide +kernel)

example : (twistBodyWitness ![true, false]).certificate =
    ⟨[4, 3, 8, 1, 0, 7, 18, 5, 2, 11, 12, 9, 10, 15, 16, 13, 14, 19, 6, 17]⟩ :=
  table_eq _ _ (by decide +kernel) (by decide +kernel)

-- An independent cyclic-transport client uses the same unrestricted-arity uniqueness API.
example :
    ((Witness.atom (fun (_ : Unit) => 3) (fun _ _ => true) ()).normalizationRotate 2).certificate =
      ⟨[8, 3, 6, 5, 10, 1, 2, 9, 0, 11, 4, 7]⟩ :=
  table_eq _ _ (by decide +kernel) (by decide +kernel)

-- Empty-body source witnesses exercise every arbitrary/wrap zero and the guarded cap.
-- The allocated auxiliary block is retained even though none of its labels occurs.
private def emptyWithAux : PPGadget (fun _ : Unit => 0) (fun _ _ => true)
    (Set.univ : Set (Fin 6 → Bool)) where
  numAux := 2
  body := []
  wellFormed := by simp [WellFormed]
  correct _ := by simp [CSP.eval]

private def emptyWithAuxWitness : GadgetWitness emptyWithAux :=
  Witness.empty (List.ofFn Sum.inl) (List.nodup_ofFn.mpr Sum.inl_injective)

example (i : Fin 6) : (emptyWithAuxWitness.normalizationZero i).certificate =
    ⟨[0, 3, 2, 5, 4, 7, 6, 9, 8, 1]⟩ := by
  apply table_eq _ _
  · change ∀ d : Dart (incidenceGraph (probeBody ([] : CSP Unit (Fin 5 ⊕ Fin 2))
        (List.ofFn Sum.inl))), d.2 = false →
          (Finset.univ.filter fun e : Dart (incidenceGraph (probeBody
            ([] : CSP Unit (Fin 5 ⊕ Fin 2)) (List.ofFn Sum.inl))) =>
              e.vertex = d.vertex).card ≤ 2
    decide +kernel
  · change verify ([] : CSP Unit (Fin 5 ⊕ Fin 2)) (List.ofFn Sum.inl)
      ⟨[0, 3, 2, 5, 4, 7, 6, 9, 8, 1]⟩ = true
    decide +kernel

example : (emptyWithAuxWitness.normalizationCap (by decide)).certificate =
    ⟨[0, 3, 2, 5, 4, 7, 6, 1]⟩ := by
  apply table_eq _ _
  · change ∀ d : Dart (incidenceGraph (probeBody ([] : CSP Unit (Fin 4 ⊕ Fin 3))
        (List.ofFn Sum.inl))), d.2 = false →
          (Finset.univ.filter fun e : Dart (incidenceGraph (probeBody
            ([] : CSP Unit (Fin 4 ⊕ Fin 3)) (List.ofFn Sum.inl))) =>
              e.vertex = d.vertex).card ≤ 2
    decide +kernel
  · change verify ([] : CSP Unit (Fin 4 ⊕ Fin 3)) (List.ofFn Sum.inl)
      ⟨[0, 3, 2, 5, 4, 7, 6, 1]⟩ = true
    decide +kernel

-- The guard detects a genuinely higher-degree variable fiber; it is not vacuous.
example : ¬(∀ d : Dart (incidenceGraph ([⟨(), [0, 0, 0]⟩] : CSP Unit (Fin 1))),
    d.2 = false → (Finset.univ.filter fun e :
      Dart (incidenceGraph ([⟨(), [0, 0, 0]⟩] : CSP Unit (Fin 1))) =>
        e.vertex = d.vertex).card ≤ 2) := by decide +kernel

end CslibFrontierTests.PlanarNormalizationBoundaryTables
