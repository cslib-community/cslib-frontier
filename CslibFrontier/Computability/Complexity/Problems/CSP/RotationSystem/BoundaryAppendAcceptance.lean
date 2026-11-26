/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.BoundaryAppendProgram
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.ScopeJoin
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Probe
import CslibFrontier.Computability.Complexity.Problems.CSP.IncidencePrefix
import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.AppendScopeIndex
import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Nullary
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateTransport
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Relabel
import CslibFrontier.Foundations.Data.List.Blocks
import CslibFrontier.Foundations.Data.List.OfFnPositions
import CslibFrontier.Foundations.GroupTheory.Perm.Fin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn

/-!
# Acceptance of the executed ordered-boundary append table

The raw append program concatenates two supplied tables, exchanges their last outgoing
probe corners when both probes are nonempty, and moves the left probe behind the right
body and probe. Its proof uses the exact positional occurrence maps of `scopeJoinRotation`.
The output direction is the original positive cyclic direction. No target rotation or
genus certificate is supplied to the program. Closed components and nullary rows remain.

The table identities and their numerical-genus consequences are original.
The actual CROSS compiler and the full source-model/native dichotomy remain objectives of
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

## Main definitions

* `OrderedBoundary.Witness.appendComputed`: append source witnesses with the literal raw program.

## Main results

* `ofRotation_appendRotation`: exact concatenation of disjoint source tables.
* `OrderedBoundary.appendRawCertificate_eq_scopeJoin`: exact outgoing splice and index transport
  for two nonempty scopes, retaining the original directed order.
* `OrderedBoundary.verify_appendRawCertificate_scopes`: full checker acceptance of the executed
  table for all empty/nonempty scope cases, retaining every original closed component.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Cslib.Logic.PL.CSP Graph Graph.RotationSystem

variable {Rel V : Type} [DecidableEq V]

omit [DecidableEq V] in
private theorem occurrences_length_append (F H : CSP Rel V) :
    (F ++ H).occurrences.length = F.occurrences.length + H.occurrences.length := by
  simp only [CSP.length_occurrences, List.map_append, List.sum_append]

private theorem append_index_inr (F H : CSP Rel V) (o : H.Occurrence) :
    incidenceEdgeIndex (appendOccurrenceEquiv F H (Sum.inr o)) =
      F.occurrences.length + incidenceEdgeIndex o := by
  rw [incidenceEdgeIndex_eq_prefix, incidenceEdgeIndex_eq_prefix]
  change (CSP.vars ((F ++ H).take (F.length + o.1.val))).length + o.2.val = _
  rw [List.take_append]
  simp only [List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    CSP.vars, List.flatMap_append, List.length_append]
  change F.vars.length + (CSP.vars (H.take o.1.val)).length + o.2.val = _
  rw [vars_length_eq_occurrences]
  simp only [CSP.vars]
  omega

private theorem append_dart_index_inl (F H : CSP Rel V) (d : Dart (incidenceGraph F)) :
    (appendDartEquiv F H (disjointDartEquiv _ _ (Sum.inl d))).index = d.index := by
  obtain ⟨⟨o, side⟩, rfl⟩ := (incidenceDartEquiv F).surjective d
  rw [incidenceDartEquiv_apply, appendDartEquiv_inl]
  simp only [Dart.index, incidenceDart, incidenceEdgeIndex_appendOccurrenceEquiv_inl]

private theorem append_dart_index_inr (F H : CSP Rel V) (d : Dart (incidenceGraph H)) :
    (appendDartEquiv F H (disjointDartEquiv _ _ (Sum.inr d))).index =
      2 * F.occurrences.length + d.index := by
  obtain ⟨⟨o, side⟩, rfl⟩ := (incidenceDartEquiv H).surjective d
  rw [incidenceDartEquiv_apply, appendDartEquiv_inr]
  simp only [Dart.index, incidenceDart, append_index_inr]
  omega

/-- The complete table of the actual disjoint body append is literal concatenation, with
the right successor entries shifted by the actual left dart count. This includes empty
tables and every closed component; no name-based enumeration is performed. -/
theorem ofRotation_appendRotation (F H : CSP Rel V) (hd : List.Disjoint F.vars H.vars)
    (r : RotationSystem (incidenceGraph F)) (s : RotationSystem (incidenceGraph H)) :
    RotationCertificate.ofRotation (appendRotation F H hd r s) =
      ⟨(RotationCertificate.ofRotation r).successor ++
        (RotationCertificate.ofRotation s).successor.map (2 * F.occurrences.length + ·)⟩ := by
  apply (RotationCertificate.ofRotation_eq_iff _ _).mpr
  constructor
  · simp only [List.length_append, List.length_map, RotationCertificate.length_ofRotation,
      incidenceGraph_edges, occurrences_length_append]
    omega
  · intro d
    obtain ⟨d, rfl⟩ := (appendDartEquiv F H).surjective d
    obtain ⟨d, rfl⟩ := (disjointDartEquiv _ _).surjective d
    rw [rotate_appendRotation]
    cases d with
    | inl d =>
      simp only [Sum.map_inl, append_dart_index_inl]
      rw [List.getD_append _ _ _ _
        ((RotationCertificate.length_ofRotation r) ▸ (Dart.indexEquiv _ d).isLt),
        RotationCertificate.getD_ofRotation]
    | inr d =>
      simp only [Sum.map_inr, append_dart_index_inr]
      have hl : (RotationCertificate.ofRotation r).successor.length =
          2 * F.occurrences.length := by
        simp only [RotationCertificate.length_ofRotation, incidenceGraph_edges, List.length_map]
      have hi : d.index < (RotationCertificate.ofRotation s).successor.length :=
        (RotationCertificate.length_ofRotation s) ▸ (Dart.indexEquiv _ d).isLt
      rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl, Nat.add_sub_cancel_left,
        List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi),
        List.getElem_map, ← List.getD_eq_getElem _ _ hi, RotationCertificate.getD_ofRotation]

/-- Concatenating the two actual supplied tables with the actual right offset preserves
the full numerical-genus and directed-order checker on disjoint variable supports.
Source tables are decoded only inside this proof; the output is the stated list program. -/
private theorem verifyRotationCertificate_append_tables (F H : CSP Rel V)
    (hd : List.Disjoint F.vars H.vars) (c d : RotationCertificate)
    (hc : verifyRotationCertificate F c = true) (hd' : verifyRotationCertificate H d = true) :
    verifyRotationCertificate (F ++ H)
      ⟨c.successor ++ d.successor.map (2 * F.occurrences.length + ·)⟩ = true := by
  obtain ⟨hr, hg, ho⟩ := (verifyRotationCertificate_eq_true_iff F c).mp hc
  obtain ⟨hs, hq, hp⟩ := (verifyRotationCertificate_eq_true_iff H d).mp hd'
  rw [← RotationCertificate.ofRotation_decode hr, ← RotationCertificate.ofRotation_decode hs,
    ← ofRotation_appendRotation F H hd]
  exact verifyRotationCertificate_appendRotation F H hd _ _ hg hq ho hp

omit [DecidableEq V] in
private theorem appended_scope_length (F : CSP Rel V) (r : Rel) {n : ℕ}
    (x : Fin n → V) :
    (F ++ [Constraint.mk r (List.ofFn x)]).occurrences.length = F.occurrences.length + n := by
  simp only [occurrences_append_scope, List.length_append, List.length_map,
    List.length_zipIdx, List.length_ofFn]

private theorem scopeJoin_source_index (F H : CSP Rel V) (r : Rel) {m n : ℕ}
    (x : Fin m → V) (y : Fin n → V)
    (a : (F.Occurrence ⊕ Fin m) ⊕ (H.Occurrence ⊕ Fin n)) :
    incidenceEdgeIndex (scopeJoinSourceEquiv F H r x y a) = match a with
      | Sum.inl (Sum.inl o) => incidenceEdgeIndex o
      | Sum.inl (Sum.inr i) => F.occurrences.length + i.val
      | Sum.inr (Sum.inl o) => F.occurrences.length + m + incidenceEdgeIndex o
      | Sum.inr (Sum.inr i) => F.occurrences.length + m + H.occurrences.length + i.val := by
  rcases a with (o | i) | (o | i) <;>
    simp only [scopeJoinSourceEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
      Sum.map_inr]
  · rw [incidenceEdgeIndex_appendOccurrenceEquiv_inl,
      incidenceEdgeIndex_appendOfFnOccurrenceEquiv_inl]
  · rw [incidenceEdgeIndex_appendOccurrenceEquiv_inl,
      incidenceEdgeIndex_appendOfFnOccurrenceEquiv_inr]
  · rw [append_index_inr, appended_scope_length, incidenceEdgeIndex_appendOfFnOccurrenceEquiv_inl]
  · rw [append_index_inr, appended_scope_length, incidenceEdgeIndex_appendOfFnOccurrenceEquiv_inr]
    omega

private theorem scopeJoin_target_index (F H : CSP Rel V) (r : Rel) {m n : ℕ}
    (x : Fin m → V) (y : Fin n → V)
    (a : (F.Occurrence ⊕ Fin m) ⊕ (H.Occurrence ⊕ Fin n)) :
    incidenceEdgeIndex (scopeJoinTargetEquiv F H r x y a) = match a with
      | Sum.inl (Sum.inl o) => incidenceEdgeIndex o
      | Sum.inl (Sum.inr i) => F.occurrences.length + H.occurrences.length + n + i.val
      | Sum.inr (Sum.inl o) => F.occurrences.length + incidenceEdgeIndex o
      | Sum.inr (Sum.inr i) => F.occurrences.length + H.occurrences.length + i.val := by
  rcases a with (o | i) | (o | i)
  · change incidenceEdgeIndex (appendOfFnOccurrenceEquiv _ r (Fin.addCases y x)
      (Sum.inl (appendOccurrenceEquiv F H (Sum.inl o)))) = _
    rw [incidenceEdgeIndex_appendOfFnOccurrenceEquiv_inl,
      incidenceEdgeIndex_appendOccurrenceEquiv_inl]
  · change incidenceEdgeIndex (appendOfFnOccurrenceEquiv _ r (Fin.addCases y x)
      (Sum.inr (Fin.natAdd n i))) = _
    rw [incidenceEdgeIndex_appendOfFnOccurrenceEquiv_inr, occurrences_length_append]
    simp only [Fin.val_natAdd]
    omega
  · change incidenceEdgeIndex (appendOfFnOccurrenceEquiv _ r (Fin.addCases y x)
      (Sum.inl (appendOccurrenceEquiv F H (Sum.inr o)))) = _
    rw [incidenceEdgeIndex_appendOfFnOccurrenceEquiv_inl, append_index_inr]
  · change incidenceEdgeIndex (appendOfFnOccurrenceEquiv _ r (Fin.addCases y x)
      (Sum.inr (Fin.castAdd m i))) = _
    rw [incidenceEdgeIndex_appendOfFnOccurrenceEquiv_inr, occurrences_length_append]
    rfl

private theorem scopeJoin_dart_index (F H : CSP Rel V) (r : Rel) {m n : ℕ}
    (x : Fin m → V) (y : Fin n → V)
    (d : Dart (incidenceGraph ((F ++ [Constraint.mk r (List.ofFn x)]) ++
      (H ++ [Constraint.mk r (List.ofFn y)])))) :
    (occurrenceDartEquiv (scopeJoinOccurrenceEquiv F H r x y) d).index =
      Nat.blockMove (2 * F.occurrences.length) (2 * m)
        (2 * (H.occurrences.length + n)) d.index := by
  obtain ⟨⟨o, side⟩, rfl⟩ := (incidenceDartEquiv _).surjective d
  rw [incidenceDartEquiv_apply, occurrenceDartEquiv_apply]
  obtain ⟨a, rfl⟩ := (scopeJoinSourceEquiv F H r x y).surjective o
  simp only [scopeJoinOccurrenceEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    Dart.index, incidenceDart, scopeJoin_source_index, scopeJoin_target_index]
  have hside := Bool.toNat_le side
  simp only [Nat.blockMove]
  rcases a with (o | i) | (o | i) <;> dsimp only
  · have ho : incidenceEdgeIndex o < F.occurrences.length := by
      simpa only [incidenceGraph_edges, List.length_map] using incidenceEdgeIndex_lt o
    split_ifs <;> omega
  · have hi := i.isLt; split_ifs <;> omega
  · have ho : incidenceEdgeIndex o < H.occurrences.length := by
      simpa only [incidenceGraph_edges, List.length_map] using incidenceEdgeIndex_lt o
    split_ifs <;> omega
  · have hi := i.isLt; split_ifs <;> omega

private theorem reindex_constraintJoin {Other W : Type} [DecidableEq W]
    {F : CSP Rel V} {T : CSP Other W} (e : F.Occurrence ≃ T.Occurrence)
    (a b : ℕ) (hab : a ≠ b) (h k : Dart (incidenceGraph F))
    (hh : h.vertex = F.numVars + a) (hk : k.vertex = F.numVars + b)
    (hv : ∀ o p, (e o).var = (e p).var ↔ o.var = p.var)
    (hc : ∀ o p, (e o).1 = (e p).1 ↔
      Function.update id b a o.1.val = Function.update id b a p.1.val)
    (r : RotationSystem (incidenceGraph F)) (c : RotationCertificate)
    (ht : RotationCertificate.ofRotation r = c) (forward back : ℕ → ℕ)
    (hf : ∀ d, (occurrenceDartEquiv e d).index = forward d.index)
    (hb : ∀ d, back (occurrenceDartEquiv e d).index = d.index) :
    RotationCertificate.reindex (c.swapSuccessors h.index k.index)
      (2 * (incidenceGraph T).edges.length) forward back =
        RotationCertificate.ofRotation (constraintJoinRotation e a b hab h k hh hk hv hc r) := by
  unfold constraintJoinRotation
  rw [← ht, ← ofRotation_mergeVertices r h k (by rw [hh, hk]; omega)]
  have hi (d : Dart (incidenceGraph F)) : (mergeDartEquiv h k d).index = d.index := rfl
  apply RotationCertificate.reindex_eq_ofRotation_transport
  · exact RotationCertificate.getD_ofRotation _
  · exact (mergeDartEquiv h k).surjective.forall.mpr fun d => by
      simpa only [constraintJoinDartEquiv, Equiv.trans_apply, Equiv.symm_apply_apply, hi] using hf d
  · exact (mergeDartEquiv h k).surjective.forall.mpr fun d => by
      simpa only [constraintJoinDartEquiv, Equiv.trans_apply, Equiv.symm_apply_apply, hi] using hb d

namespace OrderedBoundary

private theorem scopeJoin_target_edges (F H : CSP Rel V) (r : Rel) {m n : ℕ}
    (x : Fin m → V) (y : Fin n → V) :
    2 * (F.occurrences.length + m + H.occurrences.length + n) =
      2 * (incidenceGraph ((F ++ H) ++
        [Constraint.mk r (List.ofFn (Fin.addCases y x))])).edges.length := by
  rw [incidenceGraph_edges, List.length_map, appended_scope_length, occurrences_length_append]
  omega

/-- For two nonempty scopes the entire executed word is the table of the existing actual
scope-join rotation. The selected entries are the two last outgoing probe darts, and the
forward/back maps are the concrete opposite block moves, with no reflected port order. -/
theorem appendRawCertificate_eq_scopeJoin (F H : CSP Rel V) (r : Rel) {m n : ℕ}
    (x : Fin (m + 1) → V) (y : Fin (n + 1) → V)
    (hd : List.Disjoint (F ++ [Constraint.mk r (List.ofFn x)]).vars
      (H ++ [Constraint.mk r (List.ofFn y)]).vars)
    (rho : RotationSystem (incidenceGraph (F ++ [Constraint.mk r (List.ofFn x)])))
    (tau : RotationSystem (incidenceGraph (H ++ [Constraint.mk r (List.ofFn y)]))) :
    appendRawCertificate F.occurrences.length (m + 1) H.occurrences.length (n + 1)
      (RotationCertificate.ofRotation rho) (RotationCertificate.ofRotation tau) =
        RotationCertificate.ofRotation (scopeJoinRotation F H r x y hd rho tau) := by
  have hleft : (incidenceDart (scopeJoinSourceEquiv F H r x y
      (Sum.inl (Sum.inr (Fin.last m)))) true).index =
        2 * (F.occurrences.length + (m + 1)) - 1 := by
    simp only [Dart.index, incidenceDart, scopeJoin_source_index, Bool.toNat_true, Fin.val_last]
    omega
  have hright : (incidenceDart (scopeJoinSourceEquiv F H r x y
      (Sum.inr (Sum.inr (Fin.last n)))) true).index =
        2 * (F.occurrences.length + (m + 1)) +
          2 * (H.occurrences.length + (n + 1)) - 1 := by
    simp only [Dart.index, incidenceDart, scopeJoin_source_index, Bool.toNat_true, Fin.val_last]
    omega
  simp only [appendRawCertificate, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    false_or, ite_false]
  rw [scopeJoin_target_edges F H r x y, ← hleft, ← hright]
  unfold scopeJoinRotation
  apply reindex_constraintJoin
  · simpa only [appended_scope_length] using ofRotation_appendRotation _ _ hd rho tau
  · exact scopeJoin_dart_index F H r x y
  · intro d
    rw [scopeJoin_dart_index]
    exact Nat.blockMove_inverse _ _ _ _

/-- The actual nonempty append program passes the full target checker. Only the two
source checker results and disjoint source supports are premises; target acceptance and
genus follow from the literal table identity and the existing scope-join construction. -/
private theorem verify_appendRawCertificate_ofFn (F H : CSP Rel V) (r : Rel) {m n : ℕ}
    (x : Fin (m + 1) → V) (y : Fin (n + 1) → V)
    (hd : List.Disjoint (F ++ [Constraint.mk r (List.ofFn x)]).vars
      (H ++ [Constraint.mk r (List.ofFn y)]).vars) (c d : RotationCertificate)
    (hc : verifyRotationCertificate (F ++ [Constraint.mk r (List.ofFn x)]) c = true)
    (hq : verifyRotationCertificate (H ++ [Constraint.mk r (List.ofFn y)]) d = true) :
    verifyRotationCertificate ((F ++ H) ++ [Constraint.mk r (List.ofFn (Fin.addCases y x))])
      (appendRawCertificate F.occurrences.length (m + 1) H.occurrences.length (n + 1) c d) =
        true := by
  obtain ⟨hr, hg, ho⟩ := (verifyRotationCertificate_eq_true_iff _ _).mp hc
  obtain ⟨hs, hqg, hqo⟩ := (verifyRotationCertificate_eq_true_iff _ _).mp hq
  rw [← RotationCertificate.ofRotation_decode hr, ← RotationCertificate.ofRotation_decode hs,
    appendRawCertificate_eq_scopeJoin F H r x y hd]
  exact verifyRotationCertificate_scopeJoinRotation F H r x y hd _ _ hg hqg ho hqo

private theorem appendRawCertificate_zero_left (M N Q : ℕ)
    (c d : RotationCertificate)
    (hc : c.successor.length = 2 * M) (hd : d.successor.length = 2 * (N + Q)) :
    appendRawCertificate M 0 N Q c d =
      ⟨c.successor ++ d.successor.map (2 * M + ·)⟩ := by
  simp only [appendRawCertificate, Nat.add_zero, Nat.mul_zero, true_or, ite_true,
    RotationCertificate.reindex, Nat.blockMove_zero_moved, Nat.blockMove_zero_after]
  apply congrArg RotationCertificate.mk
  have hlen : (c.successor ++ d.successor.map (2 * M + ·)).length =
      2 * (M + N + Q) := by
    simp only [List.length_append, List.length_map, hc, hd]
    omega
  rw [← hlen]
  exact List.map_getD_range _ 0

private theorem verify_appendRawCertificate_nil_left (F H : CSP Rel V) (r : Rel)
    (ys : List V) (hd : List.Disjoint F.vars (H ++ [Constraint.mk r ys]).vars)
    (c d : RotationCertificate)
    (hc : verifyRotationCertificate (F ++ [Constraint.mk r []]) c = true)
    (hq : verifyRotationCertificate (H ++ [Constraint.mk r ys]) d = true) :
    verifyRotationCertificate ((F ++ H) ++ [Constraint.mk r ys])
      (appendRawCertificate F.occurrences.length 0 H.occurrences.length ys.length c d) = true := by
  have hb : verifyRotationCertificate F c = true := by
    rwa [verifyRotationCertificate_append_nullary] at hc
  obtain ⟨hc', -, -⟩ := (verifyRotationCertificate_eq_true_iff _ _).mp hb
  obtain ⟨hq', -, -⟩ := (verifyRotationCertificate_eq_true_iff _ _).mp hq
  have hl : c.successor.length = 2 * F.occurrences.length := by
    simpa only [incidenceGraph_edges, List.length_map] using
      RotationCertificate.length_of_verifyRotation hc'
  have hr : d.successor.length = 2 * (H.occurrences.length + ys.length) := by
    simpa only [incidenceGraph_edges, List.length_map, occurrences_append_scope,
      List.length_append, List.length_zipIdx] using
      RotationCertificate.length_of_verifyRotation hq'
  rw [appendRawCertificate_zero_left _ _ _ _ _ hl hr]
  simpa only [List.append_assoc] using
    verifyRotationCertificate_append_tables F (H ++ [Constraint.mk r ys]) hd c d hb hq

omit [DecidableEq V] in
private theorem scopeJoin_no_right_probe (F H : CSP Rel V) (r : Rel) {m : ℕ}
    (x : Fin m → V) (y : Fin 0 → V)
    (o : ((F ++ [Constraint.mk r (List.ofFn x)]) ++
      (H ++ [Constraint.mk r (List.ofFn y)])).Occurrence) :
    o.1.val ≠ F.length + 1 + H.length := by
  obtain ⟨a, rfl⟩ := (scopeJoinSourceEquiv F H r x y).surjective o
  have hc := congrArg Prod.fst (record_scopeJoinSourceEquiv F H r x y a)
  dsimp only [Occurrence.record] at hc
  rcases a with (o | i) | (o | i)
  · have := o.1.isLt; dsimp only at hc; omega
  · dsimp only at hc; omega
  · have := o.1.isLt; dsimp only at hc; omega
  · exact i.elim0

omit [DecidableEq V] in
private theorem scopeJoin_constraint_nil_right (F H : CSP Rel V) (r : Rel) {m : ℕ}
    (x : Fin m → V) (y : Fin 0 → V)
    (o p : ((F ++ [Constraint.mk r (List.ofFn x)]) ++
      (H ++ [Constraint.mk r (List.ofFn y)])).Occurrence) :
    (scopeJoinOccurrenceEquiv F H r x y o).1 =
      (scopeJoinOccurrenceEquiv F H r x y p).1 ↔ o.1 = p.1 := by
  rw [constraint_scopeJoinOccurrenceEquiv]
  simp only [Function.update_of_ne (scopeJoin_no_right_probe F H r x y o),
    Function.update_of_ne (scopeJoin_no_right_probe F H r x y p), id_eq, Fin.ext_iff]

omit [DecidableEq V] in
private theorem scopeJoin_target_successor_nil_right (F H : CSP Rel V) (r : Rel) {m : ℕ}
    (x : Fin m → V) (y : Fin 0 → V)
    (a : (F.Occurrence ⊕ Fin m) ⊕ (H.Occurrence ⊕ Fin 0)) :
    argumentSuccessor (scopeJoinTargetEquiv F H r x y a) =
      scopeJoinTargetEquiv F H r x y (Sum.map
        (Sum.map argumentSuccessor (finRotate m))
        (Sum.map argumentSuccessor (finRotate 0)) a) := by
  rcases a with (o | i) | (o | i)
  · change argumentSuccessor (appendOfFnOccurrenceEquiv _ r (Fin.addCases y x)
      (Sum.inl (appendOccurrenceEquiv F H (Sum.inl o)))) = _
    rw [argumentSuccessor_appendOfFnOccurrenceEquiv_inl, argumentSuccessor_appendOccurrenceEquiv]
    rfl
  · change argumentSuccessor (appendOfFnOccurrenceEquiv _ r (Fin.addCases y x)
      (Sum.inr (Fin.natAdd 0 i))) =
        appendOfFnOccurrenceEquiv _ r (Fin.addCases y x)
          (Sum.inr (Fin.natAdd 0 (finRotate m i)))
    rw [argumentSuccessor_appendOfFnOccurrenceEquiv_inr]
    exact congrArg (fun j => appendOfFnOccurrenceEquiv _ r (Fin.addCases y x) (Sum.inr j))
      (Fin.ext (by simp only [val_finRotate, Fin.val_natAdd, Nat.zero_add]))
  · change argumentSuccessor (appendOfFnOccurrenceEquiv _ r (Fin.addCases y x)
      (Sum.inl (appendOccurrenceEquiv F H (Sum.inr o)))) = _
    rw [argumentSuccessor_appendOfFnOccurrenceEquiv_inl, argumentSuccessor_appendOccurrenceEquiv]
    rfl
  · exact i.elim0

omit [DecidableEq V] in
private theorem scopeJoin_successor_nil_right (F H : CSP Rel V) (r : Rel) {m : ℕ}
    (x : Fin m → V) (y : Fin 0 → V)
    (o : ((F ++ [Constraint.mk r (List.ofFn x)]) ++
      (H ++ [Constraint.mk r (List.ofFn y)])).Occurrence) :
    scopeJoinOccurrenceEquiv F H r x y (argumentSuccessor o) =
      argumentSuccessor (scopeJoinOccurrenceEquiv F H r x y o) := by
  obtain ⟨a, rfl⟩ := (scopeJoinSourceEquiv F H r x y).surjective o
  rw [argumentSuccessor_scopeJoinSourceEquiv]
  simp only [scopeJoinOccurrenceEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  exact (scopeJoin_target_successor_nil_right F H r x y a).symm

private theorem verify_appendRawCertificate_nil_right_ofFn (F H : CSP Rel V) (r : Rel)
    {m : ℕ} (x : Fin m → V) (y : Fin 0 → V)
    (hd : List.Disjoint (F ++ [Constraint.mk r (List.ofFn x)]).vars
      (H ++ [Constraint.mk r (List.ofFn y)]).vars) (c d : RotationCertificate)
    (hc : verifyRotationCertificate (F ++ [Constraint.mk r (List.ofFn x)]) c = true)
    (hq : verifyRotationCertificate (H ++ [Constraint.mk r (List.ofFn y)]) d = true) :
    verifyRotationCertificate ((F ++ H) ++ [Constraint.mk r (List.ofFn (Fin.addCases y x))])
      (appendRawCertificate F.occurrences.length m H.occurrences.length 0 c d) = true := by
  obtain ⟨hr, hg, ho⟩ := (verifyRotationCertificate_eq_true_iff _ _).mp hc
  obtain ⟨hs, hqg, hqo⟩ := (verifyRotationCertificate_eq_true_iff _ _).mp hq
  let rho := RotationCertificate.decode _ c hr
  let tau := RotationCertificate.decode _ d hs
  let source := appendRotation _ _ hd rho tau
  let e := scopeJoinOccurrenceEquiv F H r x y
  have hv (o p) : (e o).var = (e p).var ↔ o.var = p.var := by
    rw [var_scopeJoinOccurrenceEquiv, var_scopeJoinOccurrenceEquiv]
  have hfib := scopeJoin_constraint_nil_right F H r x y
  let target := occurrenceTransport source e hv hfib
  have ht : RotationCertificate.ofRotation source =
      ⟨c.successor ++ d.successor.map (2 * (F.occurrences.length + m) + ·)⟩ := by
    simp only [source, ofRotation_appendRotation, rho, tau, RotationCertificate.ofRotation_decode,
      appended_scope_length]
  have hidx (a) : (occurrenceDartEquiv e a).index =
      Nat.blockMove (2 * F.occurrences.length) (2 * m) (2 * H.occurrences.length) a.index := by
    simpa only [Nat.add_zero] using scopeJoin_dart_index F H r x y a
  have heq : appendRawCertificate F.occurrences.length m H.occurrences.length 0 c d =
      RotationCertificate.ofRotation target := by
    have hedges := scopeJoin_target_edges F H r x y
    rw [Nat.add_zero] at hedges
    simp only [appendRawCertificate, or_true, ite_true, Nat.add_zero, hedges]
    unfold target occurrenceTransport
    apply RotationCertificate.reindex_eq_ofRotation_transport
    · intro a; rw [← ht]; exact RotationCertificate.getD_ofRotation source a
    · exact hidx
    · intro a; rw [hidx]; exact Nat.blockMove_inverse _ _ _ _
  rw [heq]
  apply verifyRotationCertificate_ofRotation
  · exact numericalGenusZero_occurrenceTransport source e hv hfib
      (numericalGenusZero_appendRotation _ _ hd rho tau hg hqg)
  · exact respectsArgumentOrder_occurrenceTransport source e hv hfib
      (scopeJoin_successor_nil_right F H r x y)
      (respectsArgumentOrder_appendRotation _ _ hd rho tau ho hqo)

/-- The full executed append table accepts for arbitrary scopes, including both-empty
and either one-empty case. The target scope is literally right then left; all body rows
and closed components survive. Only the supplied source tables are assumed accepted. -/
theorem verify_appendRawCertificate_scopes (F H : CSP Rel V) (r : Rel) (xs ys : List V)
    (hd : List.Disjoint (F ++ [Constraint.mk r xs]).vars (H ++ [Constraint.mk r ys]).vars)
    (c d : RotationCertificate)
    (hc : verifyRotationCertificate (F ++ [Constraint.mk r xs]) c = true)
    (hq : verifyRotationCertificate (H ++ [Constraint.mk r ys]) d = true) :
    verifyRotationCertificate ((F ++ H) ++ [Constraint.mk r (ys ++ xs)])
      (appendRawCertificate F.occurrences.length xs.length H.occurrences.length ys.length c d) =
        true := by
  cases xs with
  | nil =>
    have hd' : List.Disjoint F.vars (H ++ [Constraint.mk r ys]).vars := by
      simpa only [CSP.vars_append_nullary] using hd
    simpa only [List.append_nil, List.length_nil] using
      verify_appendRawCertificate_nil_left F H r ys hd' c d hc hq
  | cons x xs =>
    let p : Fin (xs.length + 1) → V := Fin.cons x xs.get
    have hp : List.ofFn p = x :: xs := by rw [List.ofFn_cons, List.ofFn_get]
    have hscope {k} (q : Fin k → V) : List.ofFn (Fin.addCases q p) = List.ofFn q ++ List.ofFn p :=
      List.ofFn_fin_append q p
    cases ys with
    | nil =>
      have h := verify_appendRawCertificate_nil_right_ofFn F H r p Fin.elim0
        (by simpa only [hp, List.ofFn_zero] using hd) c d
        (by simpa only [hp] using hc) (by simpa only [List.ofFn_zero] using hq)
      simpa only [hscope, List.ofFn_zero, List.nil_append, hp, List.length_cons,
        List.length_nil] using h
    | cons y ys =>
      let q : Fin (ys.length + 1) → V := Fin.cons y ys.get
      have hq' : List.ofFn q = y :: ys := by rw [List.ofFn_cons, List.ofFn_get]
      have h := verify_appendRawCertificate_ofFn F H r p q
        (by simpa only [hp, hq'] using hd) c d
        (by simpa only [hp] using hc) (by simpa only [hq'] using hq)
      simpa only [hscope, hq', hp, List.length_cons] using h

/-- Append two supplied ordered boundaries by executing the literal raw table program.
The source certificates are read as data. Target probe acceptance, target body acceptance
and numerical genus are derived internally, with no target certificate supplied. -/
@[expose] def Witness.appendComputed {F H : CSP Rel V} {ps qs : List V}
    (w : Witness F ps) (v : Witness H qs)
    (hd : List.Disjoint (F.vars ++ ps) (H.vars ++ qs)) (hn : (ps ++ qs).Nodup) :
    Witness (F ++ H) (ps ++ qs) :=
  Witness.ofProbe hn
    (appendRawCertificate F.occurrences.length ps.length H.occurrences.length qs.length
      w.certificate v.certificate) (by
    let B : CSP (Option Rel) V := F.map fun row => ⟨some row.rel, row.scope⟩
    let C : CSP (Option Rel) V := H.map fun row => ⟨some row.rel, row.scope⟩
    have hB : B.vars = F.vars := by simp only [B, CSP.vars, List.flatMap_map]
    have hC : C.vars = H.vars := by simp only [C, CSP.vars, List.flatMap_map]
    have hd' : List.Disjoint (B ++ [Constraint.mk none ps.reverse]).vars
        (C ++ [Constraint.mk none qs.reverse]).vars := by
      change List.Disjoint (probeBody F ps).vars (probeBody H qs).vars
      rw [vars_probeBody, vars_probeBody]
      apply List.disjoint_left.mpr
      intro z hz hw
      have hz' : z ∈ F.vars ++ ps := by
        simpa only [List.mem_append, List.mem_reverse] using hz
      have hw' : z ∈ H.vars ++ qs := by
        simpa only [List.mem_append, List.mem_reverse] using hw
      exact List.disjoint_left.mp hd hz' hw'
    have h := verify_appendRawCertificate_scopes B C none ps.reverse qs.reverse hd'
      w.certificate v.certificate w.probe_accepted v.probe_accepted
    have hBl : B.occurrences.length = F.occurrences.length := by
      rw [← vars_length_eq_occurrences B, hB, vars_length_eq_occurrences F]
    have hCl : C.occurrences.length = H.occurrences.length := by
      rw [← vars_length_eq_occurrences C, hC, vars_length_eq_occurrences H]
    simpa only [probeBody, List.map_append, List.reverse_append, List.length_reverse,
      B, C, hBl, hCl] using h)

end OrderedBoundary

end Cslib.Complexity.CSP
