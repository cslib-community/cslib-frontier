/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Append
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.DisjointGenus
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.OccurrenceTransport
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Certificate

/-!
# Appending actual CSP bodies with disjoint variable supports

The positional occurrence correspondence transports the disjoint graph rotation to the
actual dense incidence names. Variable supports are disjoint; constraint positions occupy
separate blocks. Original row order, directed argument order and source numerical genus
are retained, including closed components and nullary constraints.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Cslib.Logic.PL.CSP Graph Graph.RotationSystem

variable {Rel V : Type} [DecidableEq V]

/-- Actual disjoint graph darts map to the original argument positions in the appended body. -/
@[expose] noncomputable def appendDartEquiv (F H : CSP Rel V) :
    Dart ((incidenceGraph F).disjointUnion (incidenceGraph H)) ≃ Dart (incidenceGraph (F ++ H)) :=
  (disjointDartEquiv (incidenceGraph F) (incidenceGraph H)).symm.trans
    (((Equiv.sumCongr (incidenceDartEquiv F).symm (incidenceDartEquiv H).symm).trans
      (Equiv.sumProdDistrib F.Occurrence H.Occurrence Bool).symm).trans
      (((appendOccurrenceEquiv F H).prodCongr (Equiv.refl Bool)).trans
        (incidenceDartEquiv (F ++ H))))

/-- Left occurrence/end coordinates are literal through both indexed graph maps. -/
theorem appendDartEquiv_inl (F H : CSP Rel V) (o : F.Occurrence) (side : Bool) :
    appendDartEquiv F H (disjointDartEquiv _ _ (Sum.inl (incidenceDart o side))) =
      incidenceDart (appendOccurrenceEquiv F H (Sum.inl o)) side := by
  simp only [appendDartEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.sumCongr_apply, Sum.map_inl]
  rw [show (incidenceDartEquiv F).symm (incidenceDart o side) = (o, side) from
    (incidenceDartEquiv F).symm_apply_apply (o, side)]
  rfl

/-- Right occurrence/end coordinates retain the exact right constraint block shift. -/
theorem appendDartEquiv_inr (F H : CSP Rel V) (o : H.Occurrence) (side : Bool) :
    appendDartEquiv F H (disjointDartEquiv _ _ (Sum.inr (incidenceDart o side))) =
      incidenceDart (appendOccurrenceEquiv F H (Sum.inr o)) side := by
  simp only [appendDartEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.sumCongr_apply, Sum.map_inr]
  rw [show (incidenceDartEquiv H).symm (incidenceDart o side) = (o, side) from
    (incidenceDartEquiv H).symm_apply_apply (o, side)]
  rfl

omit [DecidableEq V] in
private theorem append_var_inl (F H : CSP Rel V) (o : F.Occurrence) :
    (appendOccurrenceEquiv F H (Sum.inl o)).var = o.var :=
  congrArg (fun record => record.2.2) (record_appendOccurrenceEquiv_inl F H o)

omit [DecidableEq V] in
private theorem append_var_inr (F H : CSP Rel V) (o : H.Occurrence) :
    (appendOccurrenceEquiv F H (Sum.inr o)).var = o.var :=
  congrArg (fun record => record.2.2) (record_appendOccurrenceEquiv_inr F H o)

private theorem appendDartEquiv_vertex_eq_iff_inl_inr (F H : CSP Rel V)
    (hd : List.Disjoint F.vars H.vars)
    (a : Dart (incidenceGraph F)) (b : Dart (incidenceGraph H)) :
    let e := disjointDartEquiv (incidenceGraph F) (incidenceGraph H)
    (appendDartEquiv F H (e (Sum.inl a))).vertex = (appendDartEquiv F H (e (Sum.inr b))).vertex ↔
      (e (Sum.inl a)).vertex = (e (Sum.inr b)).vertex := by
  dsimp only
  obtain ⟨⟨o, side⟩, rfl⟩ := (incidenceDartEquiv F).surjective a
  obtain ⟨⟨p, other⟩, rfl⟩ := (incidenceDartEquiv H).surjective b
  rw [incidenceDartEquiv_apply, incidenceDartEquiv_apply,
    appendDartEquiv_inl, appendDartEquiv_inr,
    vertex_disjointDartEquiv_inl, vertex_disjointDartEquiv_inr,
    vertex_incidenceDart_eq_iff, append_var_inl, append_var_inr]
  have hc : (appendOccurrenceEquiv F H (Sum.inl o)).1 ≠
      (appendOccurrenceEquiv F H (Sum.inr p)).1 := by
    intro he
    have he' : o.1.val = F.length + p.1.val := congrArg Fin.val he
    omega
  have hv : o.var ≠ p.var := fun he => List.disjoint_left.mp hd o.var_mem (he ▸ p.var_mem)
  change (side = other ∧ if side then
    (appendOccurrenceEquiv F H (Sum.inl o)).1 = (appendOccurrenceEquiv F H (Sum.inr p)).1
    else o.var = p.var) ↔
      2 * (incidenceDart o side).vertex = 2 * (incidenceDart p other).vertex + 1
  simp only [hc, hv, ite_self, and_false, false_iff]
  omega

/-- Endpoint fibers match precisely when the actual occurring variable supports are disjoint.
No condition is placed on repetitions inside either body or on its graph degrees. -/
theorem appendDartEquiv_vertex_eq_iff (F H : CSP Rel V) (hd : List.Disjoint F.vars H.vars)
    (a b : Dart ((incidenceGraph F).disjointUnion (incidenceGraph H))) :
    (appendDartEquiv F H a).vertex = (appendDartEquiv F H b).vertex ↔ a.vertex = b.vertex := by
  obtain ⟨a, rfl⟩ := (disjointDartEquiv _ _).surjective a
  obtain ⟨b, rfl⟩ := (disjointDartEquiv _ _).surjective b
  match a, b with
  | .inl a, .inl b =>
    obtain ⟨⟨o, side⟩, rfl⟩ := (incidenceDartEquiv F).surjective a
    obtain ⟨⟨p, other⟩, rfl⟩ := (incidenceDartEquiv F).surjective b
    rw [incidenceDartEquiv_apply, incidenceDartEquiv_apply,
      appendDartEquiv_inl, appendDartEquiv_inl,
      vertex_disjointDartEquiv_inl, vertex_disjointDartEquiv_inl,
      vertex_incidenceDart_eq_iff, append_var_inl, append_var_inl]
    have hc : (appendOccurrenceEquiv F H (Sum.inl o)).1 =
        (appendOccurrenceEquiv F H (Sum.inl p)).1 ↔ o.1 = p.1 := by
      simp only [Fin.ext_iff]; rfl
    rw [hc, ← vertex_incidenceDart_eq_iff]
    change _ ↔ 2 * _ = 2 * _
    dsimp only
    omega
  | .inl a, .inr b => exact appendDartEquiv_vertex_eq_iff_inl_inr F H hd a b
  | .inr a, .inl b =>
    exact eq_comm.trans ((appendDartEquiv_vertex_eq_iff_inl_inr F H hd b a).trans eq_comm)
  | .inr a, .inr b =>
    obtain ⟨⟨o, side⟩, rfl⟩ := (incidenceDartEquiv H).surjective a
    obtain ⟨⟨p, other⟩, rfl⟩ := (incidenceDartEquiv H).surjective b
    rw [incidenceDartEquiv_apply, incidenceDartEquiv_apply,
      appendDartEquiv_inr, appendDartEquiv_inr,
      vertex_disjointDartEquiv_inr, vertex_disjointDartEquiv_inr,
      vertex_incidenceDart_eq_iff, append_var_inr, append_var_inr]
    have hc : (appendOccurrenceEquiv F H (Sum.inr o)).1 =
        (appendOccurrenceEquiv F H (Sum.inr p)).1 ↔ o.1 = p.1 := by
      simp only [Fin.ext_iff]
      change F.length + o.1.val = F.length + p.1.val ↔ o.1.val = p.1.val
      omega
    rw [hc, ← vertex_incidenceDart_eq_iff]
    change _ ↔ 2 * _ + 1 = 2 * _ + 1
    dsimp only
    omega

/-- Positional concatenation commutes with actual edge reversal. -/
theorem reverse_appendDartEquiv (F H : CSP Rel V)
    (d : Dart ((incidenceGraph F).disjointUnion (incidenceGraph H))) :
    appendDartEquiv F H d.reverse = (appendDartEquiv F H d).reverse := by
  obtain ⟨d, rfl⟩ := (disjointDartEquiv _ _).surjective d
  rw [← reverse_disjointDartEquiv]
  cases d with
  | inl d =>
    obtain ⟨⟨o, side⟩, rfl⟩ := (incidenceDartEquiv F).surjective d
    simp only [incidenceDartEquiv_apply, Sum.map_inl]
    change appendDartEquiv F H (disjointDartEquiv _ _ (Sum.inl (incidenceDart o (!side)))) = _
    rw [appendDartEquiv_inl, appendDartEquiv_inl]
    rfl
  | inr d =>
    obtain ⟨⟨o, side⟩, rfl⟩ := (incidenceDartEquiv H).surjective d
    simp only [incidenceDartEquiv_apply, Sum.map_inr]
    change appendDartEquiv F H (disjointDartEquiv _ _ (Sum.inr (incidenceDart o (!side)))) = _
    rw [appendDartEquiv_inr, appendDartEquiv_inr]
    rfl

/-- Append two actual incidence rotations with disjoint occurring variable names. -/
@[expose] noncomputable def appendRotation (F H : CSP Rel V) (hd : List.Disjoint F.vars H.vars)
    (r : RotationSystem (incidenceGraph F)) (s : RotationSystem (incidenceGraph H)) :
    RotationSystem (incidenceGraph (F ++ H)) :=
  (r.disjointUnion s).transport (appendDartEquiv F H) (appendDartEquiv_vertex_eq_iff F H hd)

/-- Target numerical genus follows from the two endpoint-declared source incidences. -/
theorem numericalGenusZero_appendRotation (F H : CSP Rel V) (hd : List.Disjoint F.vars H.vars)
    (r : RotationSystem (incidenceGraph F)) (s : RotationSystem (incidenceGraph H))
    (hr : r.NumericalGenusZero) (hs : s.NumericalGenusZero) :
    (appendRotation F H hd r s).NumericalGenusZero :=
  (r.disjointUnion s).numericalGenusZero_transport (appendDartEquiv F H)
    (appendDartEquiv_vertex_eq_iff F H hd) (reverse_appendDartEquiv F H)
    (endpoints_declared_disjointUnion _ _ (incidenceVertices_declared F)
      (incidenceVertices_declared H))
    (incidenceVertices_declared (F ++ H)) (r.numericalGenusZero_disjointUnion s
      (incidenceVertices_declared F) (incidenceVertices_declared H) hr hs)

/-- Appended successors are exactly the two old source rotations in positional coordinates. -/
theorem rotate_appendRotation (F H : CSP Rel V) (hd : List.Disjoint F.vars H.vars)
    (r : RotationSystem (incidenceGraph F)) (s : RotationSystem (incidenceGraph H))
    (d : Dart (incidenceGraph F) ⊕ Dart (incidenceGraph H)) :
    (appendRotation F H hd r s).rotate (appendDartEquiv F H (disjointDartEquiv _ _ d)) =
      appendDartEquiv F H (disjointDartEquiv _ _ (Sum.map r.rotate s.rotate d)) := by
  simp only [appendRotation, transport, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    rotate_disjointUnion]

/-- Original clockwise argument order is inherited on both exact constraint blocks. -/
theorem respectsArgumentOrder_appendRotation (F H : CSP Rel V)
    (hd : List.Disjoint F.vars H.vars) (r : RotationSystem (incidenceGraph F))
    (s : RotationSystem (incidenceGraph H)) (hr : RespectsArgumentOrder r)
    (hs : RespectsArgumentOrder s) : RespectsArgumentOrder (appendRotation F H hd r s) := by
  intro o
  obtain ⟨o, rfl⟩ := (appendOccurrenceEquiv F H).surjective o
  cases o with
  | inl o =>
    rw [← appendDartEquiv_inl, rotate_appendRotation]
    simp only [Sum.map_inl]
    rw [hr o, appendDartEquiv_inl, argumentSuccessor_appendOccurrenceEquiv]
    rfl
  | inr o =>
    rw [← appendDartEquiv_inr, rotate_appendRotation]
    simp only [Sum.map_inr]
    rw [hs o, appendDartEquiv_inr, argumentSuccessor_appendOccurrenceEquiv]
    rfl

/-- Full checker acceptance for the actual appended body, derived from its source rotations. -/
theorem verifyRotationCertificate_appendRotation (F H : CSP Rel V)
    (hd : List.Disjoint F.vars H.vars) (r : RotationSystem (incidenceGraph F))
    (s : RotationSystem (incidenceGraph H)) (hr : r.NumericalGenusZero)
    (hs : s.NumericalGenusZero) (hor : RespectsArgumentOrder r) (hos : RespectsArgumentOrder s) :
    verifyRotationCertificate (F ++ H) (RotationCertificate.ofRotation
      (appendRotation F H hd r s)) = true :=
  verifyRotationCertificate_ofRotation _ (numericalGenusZero_appendRotation F H hd r s hr hs)
    (respectsArgumentOrder_appendRotation F H hd r s hor hos)

end Cslib.Complexity.CSP
