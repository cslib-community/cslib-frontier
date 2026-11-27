/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.OneHot3.Order
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Certificate
import CslibFrontier.Computability.Complexity.Problems.CSP.IncidenceUniform
import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.ArityOccurrence
import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.OccurrenceTransport
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateLookup
import Mathlib.Tactic.FinCases

/-!
# Acceptance of the executed ternary scope alignment

The actual ternary occurrence bijection retains original variables and constraint positions.
It conjugates the original rotation by the same index map executed on the binary table.
Every three-element constraint fiber is one of the two directed three-cycles; the first
constraint-end table entry selects the scope permutation that makes its cycle positive.
Numerical genus is transported internally along the indexed occurrence bijection.

The width-three restriction belongs only to the symmetric base problem. This construction
does not restrict arities or body degrees in an original target constraint language.
-/

public section

namespace Cslib.Complexity.CSP.OneHot3

open Cslib.Logic.PL Graph

private def ternaryCoordinates (F : CSP Unit ℕ) (hw : F.WellFormed arity) :
    F.Occurrence ≃ Fin F.length × Fin 3 where
  toFun o := (o.1, ⟨o.2.val, by
    have h := hw F[o.1.val] (List.getElem_mem o.1.isLt)
    simpa only [arity, h] using o.2.isLt⟩)
  invFun p := arityOccurrence F hw p.1 p.2
  left_inv o := by cases o; rfl
  right_inv p := by cases p; rfl

private def portPermutation (c : RotationCertificate) (i : ℕ) : Equiv.Perm (Fin 3) :=
  if forward c i then Equiv.refl _ else Equiv.swap 1 2

private def rowPortEquiv (c : RotationCertificate) (n : ℕ) :
    (Fin n × Fin 3) ≃ (Fin n × Fin 3) where
  toFun p := (p.1, portPermutation c p.1 p.2)
  invFun p := (p.1, (portPermutation c p.1).symm p.2)
  left_inv p := by simp only [Equiv.symm_apply_apply]
  right_inv p := by simp only [Equiv.apply_symm_apply]

private def orderedOccurrenceEquiv (F : CSP Unit ℕ) (c : RotationCertificate)
    (hw : F.WellFormed arity) : F.Occurrence ≃ (orderedConstraints F c).Occurrence :=
  (ternaryCoordinates F hw).trans ((rowPortEquiv c F.length).trans
    ((Equiv.prodCongr (finCongr (length_orderedConstraints F c).symm) (Equiv.refl _)).trans
      (ternaryCoordinates (orderedConstraints F c) (wellFormed_orderedConstraints F c hw)).symm))

private theorem orderedOccurrence_constraint (F : CSP Unit ℕ) (c : RotationCertificate)
    (hw : F.WellFormed arity) (o : F.Occurrence) :
    (orderedOccurrenceEquiv F c hw o).1.val = o.1.val := rfl

private theorem orderedOccurrence_var (F : CSP Unit ℕ) (c : RotationCertificate)
    (hw : F.WellFormed arity) (o : F.Occurrence) :
    (orderedOccurrenceEquiv F c hw o).var = o.var := by
  obtain ⟨⟨i, j⟩, rfl⟩ := (ternaryCoordinates F hw).symm.surjective o
  have hlen : F[i.val].scope.length = 3 := hw _ (List.getElem_mem i.isLt)
  obtain ⟨a, b, v, hscope⟩ := List.length_eq_three.mp hlen
  let i' : Fin (orderedConstraints F c).length :=
    ⟨i.val, by rw [length_orderedConstraints]; exact i.isLt⟩
  have htarget : (orderedConstraints F c)[i'.val].scope.length = 3 :=
    wellFormed_orderedConstraints F c hw _ (List.getElem_mem i'.isLt)
  change (orderedConstraints F c)[i'.val].scope[(portPermutation c i j).val]'(by
      rw [htarget]; exact (portPermutation c i j).isLt) =
    F[i.val].scope[j.val]'(by rw [hlen]; exact j.isLt)
  cases hf : forward c i.val <;> fin_cases j <;>
    simp [i', portPermutation, orderedConstraints, List.getElem_mapIdx,
      hf, hscope, swapTail3, Equiv.swap_apply_def]

private theorem variable_fibers (F : CSP Unit ℕ) (c : RotationCertificate)
    (hw : F.WellFormed arity) (o p : F.Occurrence) :
    (orderedOccurrenceEquiv F c hw o).var = (orderedOccurrenceEquiv F c hw p).var ↔
      o.var = p.var := by
  rw [orderedOccurrence_var, orderedOccurrence_var]

private theorem constraint_fibers (F : CSP Unit ℕ) (c : RotationCertificate)
    (hw : F.WellFormed arity) (o p : F.Occurrence) :
    (orderedOccurrenceEquiv F c hw o).1 = (orderedOccurrenceEquiv F c hw p).1 ↔ o.1 = p.1 := by
  simp only [Fin.ext_iff, orderedOccurrence_constraint]

private theorem index_coordinates (F : CSP Unit ℕ) (hw : F.WellFormed arity)
    (p : Fin F.length × Fin 3) (side : Bool) :
    (incidenceDart ((ternaryCoordinates F hw).symm p) side).index =
      6 * p.1.val + 2 * p.2.val + side.toNat := by
  change 2 * incidenceEdgeIndex ((ternaryCoordinates F hw).symm p) + side.toNat = _
  rw [incidenceEdgeIndex_eq_mul_add 3 hw]
  change 2 * (3 * p.1.val + p.2.val) + side.toNat = _
  omega

private theorem index_orderedOccurrence (F : CSP Unit ℕ) (c : RotationCertificate)
    (hw : F.WellFormed arity) (o : F.Occurrence) (side : Bool) :
    (incidenceDart (orderedOccurrenceEquiv F c hw o) side).index =
      dartReindex c (incidenceDart o side).index := by
  obtain ⟨⟨i, j⟩, rfl⟩ := (ternaryCoordinates F hw).symm.surjective o
  let i' : Fin (orderedConstraints F c).length :=
    ⟨i.val, by rw [length_orderedConstraints]; exact i.isLt⟩
  change (incidenceDart ((ternaryCoordinates (orderedConstraints F c)
      (wellFormed_orderedConstraints F c hw)).symm (i', portPermutation c i j)) side).index = _
  rw [index_coordinates, index_coordinates]
  have hside : side.toNat < 2 := by cases side <;> decide
  simp only [dartReindex, show (6 * i.val + 2 * j.val + side.toNat) / 6 = i.val by omega,
    show (6 * i.val + 2 * j.val + side.toNat) / 2 % 3 = j.val by omega,
    show (6 * i.val + 2 * j.val + side.toNat) % 2 = side.toNat by omega]
  cases hf : forward c i.val <;> fin_cases j <;>
    simp [portPermutation, hf, Equiv.swap_apply_def, i']

private theorem index_orderedDart (F : CSP Unit ℕ) (c : RotationCertificate)
    (hw : F.WellFormed arity) (a : Dart (incidenceGraph F)) :
    (occurrenceDartEquiv (orderedOccurrenceEquiv F c hw) a).index = dartReindex c a.index := by
  obtain ⟨⟨o, side⟩, rfl⟩ := (incidenceDartEquiv F).surjective a
  rw [incidenceDartEquiv_apply, occurrenceDartEquiv_apply]
  exact index_orderedOccurrence F c hw o _

private noncomputable def orderedRotation (F : CSP Unit ℕ) (c : RotationCertificate)
    (hw : F.WellFormed arity) (r : RotationSystem (incidenceGraph F)) :
    RotationSystem (incidenceGraph (orderedConstraints F c)) :=
  occurrenceTransport r (orderedOccurrenceEquiv F c hw)
    (variable_fibers F c hw) (constraint_fibers F c hw)

private theorem orderedCertificate_eq_ofRotation (F : CSP Unit ℕ) (c : RotationCertificate)
    (hw : F.WellFormed arity) (r : RotationSystem (incidenceGraph F))
    (ht : ∀ a, c.successor.getD a.index 0 = (r.rotate a).index) :
    orderedCertificate F c = RotationCertificate.ofRotation (orderedRotation F c hw r) := by
  have hcount : (incidenceGraph (orderedConstraints F c)).edges.length =
      (incidenceGraph F).edges.length := by
    rw [length_edges_incidenceGraph_eq_mul 3 (wellFormed_orderedConstraints F c hw),
      length_edges_incidenceGraph_eq_mul 3 hw, length_orderedConstraints]
  simpa only [orderedCertificate, orderedRotation, occurrenceTransport, hcount] using
    RotationCertificate.reindex_eq_ofRotation_transport r c ht
      (occurrenceDartEquiv (orderedOccurrenceEquiv F c hw))
      (occurrenceDartEquiv_vertex_eq_iff _ (variable_fibers F c hw) (constraint_fibers F c hw))
      (dartReindex c) (dartReindex c) (index_orderedDart F c hw)
      fun a => by rw [index_orderedDart, dartReindex_involutive c]

private theorem constraint_cycle_step (F : CSP Unit ℕ) (c : RotationCertificate)
    (hw : F.WellFormed arity) (r : RotationSystem (incidenceGraph F))
    (ht : ∀ a, c.successor.getD a.index 0 = (r.rotate a).index)
    (i : Fin F.length) (j : Fin 3) :
    r.rotate (incidenceDart ((ternaryCoordinates F hw).symm (i, j)) true) =
      incidenceDart ((ternaryCoordinates F hw).symm
        (i, (portPermutation c i).symm (finRotate 3 (portPermutation c i j)))) true := by
  let dart (k : Fin 3) := incidenceDart ((ternaryCoordinates F hw).symm (i, k)) true
  have hdinj : Function.Injective dart := fun _ _ hab =>
    congrArg Prod.snd ((ternaryCoordinates F hw).symm.injective (incidenceDart_injective true hab))
  have himage (a : Fin 3) : ∃ b : Fin 3, r.rotate (dart a) = dart b := by
    obtain ⟨o, ho⟩ := exists_incidenceDart (r.rotate (dart a))
    have hvertex := r.vertex_rotate (dart a)
    rw [← ho] at hvertex
    have hf := (vertex_incidenceDart_eq_iff o
      ((ternaryCoordinates F hw).symm (i, a)) (r.rotate (dart a)).2 true).mp hvertex
    refine ⟨(ternaryCoordinates F hw o).2, ho.symm.trans ?_⟩
    rw [hf.1]
    refine congrArg (fun occ => incidenceDart occ true) ((ternaryCoordinates F hw).injective ?_)
    rw [Equiv.apply_symm_apply]
    have hrow : o.1 = ((ternaryCoordinates F hw).symm (i, a)).1 := by
      simpa only [hf.1, ite_true] using hf.2
    exact Prod.ext hrow rfl
  let next (a : Fin 3) := (himage a).choose
  have hnext (a : Fin 3) : r.rotate (dart a) = dart (next a) := (himage a).choose_spec
  have hni : Function.Injective next := fun a b hab =>
    hdinj <| r.rotate.injective <| (hnext a).trans ((congrArg dart hab).trans (hnext b).symm)
  have hnf (a : Fin 3) : next a ≠ a := fun he =>
    let ⟨b, hba⟩ := exists_ne a
    hba (hdinj <| ((r.sameCycle_iff (dart a) (dart b)).mpr
      ((vertex_incidenceDart_eq_iff _ _ true true).mpr ⟨rfl, rfl⟩)).eq_of_left
        ((hnext a).trans (congrArg dart he))).symm
  have hread : c.successor.getD (6 * i.val + 1) 0 = 6 * i.val + 2 * (next 0).val + 1 := by
    simpa only [dart, index_coordinates, Fin.val_zero, Nat.mul_zero, Nat.add_zero,
      Bool.toNat_true] using (ht (dart 0)).trans (congrArg Dart.index (hnext 0))
  have hforward : forward c i.val = decide (next 0 = 1) := Bool.eq_iff_iff.mpr <| by
    simp only [forward, decide_eq_true_eq, hread, Fin.ext_iff, Fin.val_one]; omega
  -- Only the three finite ports are enumerated here, never a source graph or drawing.
  have classification : ∀ f : Fin 3 → Fin 3, Function.Injective f →
      (∀ a, f a ≠ a) → ∀ a,
      let q : Equiv.Perm (Fin 3) :=
        if decide (f 0 = 1) then Equiv.refl _ else Equiv.swap 1 2
      q (f a) = finRotate 3 (q a) := by
    decide +kernel
  have hconj : portPermutation c i (next j) = finRotate 3 (portPermutation c i j) := by
    simpa only [portPermutation, hforward] using classification next hni hnf j
  exact (hnext j).trans (congrArg dart <| by simpa using congrArg (portPermutation c i).symm hconj)

private theorem respectsArgumentOrder_orderedRotation (F : CSP Unit ℕ)
    (c : RotationCertificate) (hw : F.WellFormed arity)
    (r : RotationSystem (incidenceGraph F))
    (ht : ∀ a, c.successor.getD a.index 0 = (r.rotate a).index) :
    RespectsArgumentOrder (orderedRotation F c hw r) := by
  intro p
  let e := orderedOccurrenceEquiv F c hw
  obtain ⟨o, rfl⟩ := e.surjective p
  obtain ⟨⟨i, j⟩, rfl⟩ := (ternaryCoordinates F hw).symm.surjective o
  let i' : Fin (orderedConstraints F c).length :=
    ⟨i.val, by rw [length_orderedConstraints]; exact i.isLt⟩
  change (occurrenceTransport r e (variable_fibers F c hw) (constraint_fibers F c hw)).rotate
    (incidenceDart (e ((ternaryCoordinates F hw).symm (i, j))) true) = _
  rw [← occurrenceDartEquiv_apply, occurrenceTransport_rotate,
    constraint_cycle_step F c hw r ht i j, occurrenceDartEquiv_apply]
  refine congrArg (fun occ => incidenceDart occ true) ?_
  change arityOccurrence (orderedConstraints F c) (wellFormed_orderedConstraints F c hw) i'
      (portPermutation c i ((portPermutation c i).symm (finRotate 3 (portPermutation c i j)))) = _
  rw [Equiv.apply_symm_apply]
  exact (argumentSuccessor_arityOccurrence (orderedConstraints F c)
    (wellFormed_orderedConstraints F c hw) i' (portPermutation c i j)).symm

/-- A well-formed ternary source with an accepted numerical rotation makes the actual
scope permutation and conjugated binary table pass the full ordered target checker.
The target argument order and numerical genus are derived internally. -/
theorem verifyRotationCertificate_orderedCertificate (F : CSP Unit ℕ)
    (c : RotationCertificate) (hw : F.WellFormed arity)
    (hc : RotationCertificate.verifyGenusZero (incidenceGraph F) c = true) :
    verifyRotationCertificate (orderedConstraints F c) (orderedCertificate F c) = true := by
  obtain ⟨hrot, hgenus⟩ := (RotationCertificate.verifyGenusZero_eq_true_iff _ _).mp hc
  let r := RotationCertificate.decode (incidenceGraph F) c hrot
  have ht a : c.successor.getD a.index 0 = (r.rotate a).index :=
    (RotationCertificate.index_decode_rotate hrot a).symm
  rw [orderedCertificate_eq_ofRotation F c hw r ht]
  exact verifyRotationCertificate_ofRotation (orderedRotation F c hw r)
    (numericalGenusZero_occurrenceTransport r (orderedOccurrenceEquiv F c hw)
      (variable_fibers F c hw) (constraint_fibers F c hw) hgenus)
    (respectsArgumentOrder_orderedRotation F c hw r ht)

end Cslib.Complexity.CSP.OneHot3
