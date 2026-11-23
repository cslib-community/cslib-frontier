/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EdgeCSP.Blossom.Ports
import CslibFrontier.Foundations.Data.List.Blocks
import CslibFrontier.Logics.Propositional.CSP.Table.ContractionRows
import Mathlib.Data.List.GetD

/-!
# Positional transport and the contracted reference labeling

This module defines the general positional `transport` labeling (projecting outside ports of `g`,
appending per-constraint `bits`, and setting the central row to `central`) together with its port
and defect rules, and derives the corresponding facts for the zero-connector, one-hot `reference`
specialization from Section 5.3 of [KazdaKolmogorovRolinek2018], arXiv:1602.03124v6, printed p. 12.
All port constructors search finite actual position lists and use binary names only as data.
-/

public section

namespace Cslib.Logic.PL.CSP.Blossom

open Table Finset
open Cslib.BitString

variable {F : CSP Table ℕ}

/-- Project changed original labels, supplying each connector bit and the actual central row. -/
@[expose] def transport (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (g : OccurrenceLabeling F Bool) (bits : Fin F.length → Bool) (central : List Bool) :
    OccurrenceLabeling (contract f vs) Bool := labels _ (transportRows g vs bits central)

/-- An original argument position survives exactly when its variable is outside the blossom. -/
theorem mem_outsidePositions (vs scope : List ℕ) (j : ℕ) :
    j ∈ outsidePositions scope.length (positions vs scope) ↔
      j < scope.length ∧ scope.getD j 0 ∉ vs := by
  simp [outsidePositions, positions]
  omega

/-- Every surviving port has a valid index in the actual old-constraint output scope. -/
theorem outside_length_le_scope (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (i : Fin F.length) :
    (outsidePositions F[i.val].scope.length (positions vs F[i.val].scope)).length ≤
      (constraint f vs i).scope.length := by
  rw [scope_constraint, ← outsideScope_eq_filter]
  simp

/-- Map a surviving original occurrence to its new scope position. Its original constraint
index is preserved, and its new argument index is found in the actual finite outside list. -/
@[expose] def oldPort (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (o : Occurrence F) (ho : o.var ∉ vs) : Occurrence (contract f vs) :=
  ⟨⟨o.1.val, by simpa only [length_contract] using Nat.lt_succ_of_lt o.1.isLt⟩,
    ⟨(outsidePositions F[o.1.val].scope.length (positions vs F[o.1.val].scope)).idxOf o.2.val, by
      have hm : o.2.val ∈ outsidePositions F[o.1.val].scope.length
          (positions vs F[o.1.val].scope) := by
        apply (mem_outsidePositions _ _ _).mpr
        exact ⟨o.2.isLt, by simpa only [List.getD_eq_getElem _ _ o.2.isLt, Occurrence.var] using ho⟩
      have hl := (List.idxOf_lt_length_iff.mpr hm).trans_le (outside_length_le_scope f vs o.1)
      simpa only [get_contract_old] using hl⟩⟩

/-- Surviving occurrence transport preserves the original binary variable name. -/
theorem oldPort_var (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (o : Occurrence F) (ho : o.var ∉ vs) : (oldPort f vs o ho).var = o.var := by
  let os := outsidePositions F[o.1.val].scope.length (positions vs F[o.1.val].scope)
  have hm : o.2.val ∈ os := (mem_outsidePositions _ _ _).mpr
    ⟨o.2.isLt, by simpa only [List.getD_eq_getElem _ _ o.2.isLt, Occurrence.var] using ho⟩
  have hl := List.idxOf_lt_length_iff.mpr hm
  have he := List.getElem_idxOf hl
  have hn : os.idxOf o.2.val < (contract f vs)[o.1.val].scope.length := by
    simpa only [get_contract_old] using hl.trans_le (outside_length_le_scope f vs o.1)
  change (contract f vs)[o.1.val].scope[os.idxOf o.2.val] = o.var
  simp only [get_contract_old, scope_constraint, ← outsideScope_eq_filter]
  change (os.map (fun j => F[o.1.val].scope.getD j 0) ++
    if (positions vs F[o.1.val].scope).isEmpty then [] else [connector F o.1])[os.idxOf o.2.val]'
      (by simp only [List.length_append, List.length_map]; omega) = _
  rw [List.getElem_append_left (by simpa only [List.length_map] using hl), List.getElem_map]
  change F[o.1.val].scope.getD (os[os.idxOf o.2.val]) 0 = o.var
  rw [he, List.getD_eq_getElem _ _ o.2.isLt]
  rfl

/-- The old rows project outside coordinates in their original order, with a bit appended
precisely at touched constraints. -/
theorem transportRows_project (g : OccurrenceLabeling F Bool) (vs : List ℕ)
    (bits : Fin F.length → Bool) (central : List Bool) (i : Fin F.length) :
    (transportRows g vs bits central).getD i.val [] =
      project (localTuple g i)
          (outsidePositions F[i.val].scope.length (positions vs F[i.val].scope)) ++
        if (positions vs F[i.val].scope).isEmpty then [] else [bits i] := by
  rw [get_transportRows_old]
  split
  next hp =>
    have he := List.isEmpty_iff.mp hp
    have hl : (localTuple g i).length = F[i.val].scope.length := by simp [localTuple]
    simp only [he, outsidePositions, List.contains_nil, Bool.not_false, List.filter_true,
      project, List.append_nil]
    rw [← hl, List.map_getD_range]
  · rfl

/-- Arbitrarily changed outside values survive the actual positional transport. -/
theorem transport_oldPort (f g : OccurrenceLabeling F Bool) (vs : List ℕ)
    (bits : Fin F.length → Bool) (central : List Bool) (o : Occurrence F) (ho : o.var ∉ vs) :
    transport f vs g bits central (oldPort f vs o ho) = g o := by
  let os := outsidePositions F[o.1.val].scope.length (positions vs F[o.1.val].scope)
  have hm : o.2.val ∈ os := (mem_outsidePositions _ _ _).mpr
    ⟨o.2.isLt, by simpa only [List.getD_eq_getElem _ _ o.2.isLt, Occurrence.var] using ho⟩
  have hl := List.idxOf_lt_length_iff.mpr hm
  change ((transportRows g vs bits central).getD o.1.val []).getD
    (os.idxOf o.2.val) false = g o
  rw [transportRows_project, List.getD_append _ _ _ _
    (by simpa only [project, List.length_map] using hl), project_getD_idxOf _ _ hm]
  simp [localTuple, o.2.isLt]

/-- The explicit finite contracted reference retains every old outside occurrence value. -/
theorem reference_oldPort (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (o : Occurrence F) (ho : o.var ∉ vs) : reference f vs (oldPort f vs o ho) = f o :=
  transport_oldPort f f vs (fun _ => false) (listSingle (connectors F vs).length 0) o ho

/-- The gathered outside list followed by the fresh port is the actual touched scope. -/
theorem scope_constraint_touched (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    {i : Fin F.length} (hi : i ∈ touched F vs) :
    (constraint f vs i).scope =
      (outsidePositions F[i.val].scope.length (positions vs F[i.val].scope)).map
        (fun j => F[i.val].scope.getD j 0) ++ [connector F i] := by
  have hp : (positions vs F[i.val].scope).isEmpty = false := by
    simpa only [List.isEmpty_eq_false_iff] using (mem_touched vs i).mp hi
  rw [scope_constraint, ← outsideScope_eq_filter]
  simp only [hp, Bool.false_eq_true, ↓reduceIte]

/-- The new terminal port of a touched original constraint. -/
@[expose] def connectorPort (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (i : Fin F.length) (hi : i ∈ touched F vs) : Occurrence (contract f vs) :=
  ⟨⟨i.val, by simpa only [length_contract] using Nat.lt_succ_of_lt i.isLt⟩,
    ⟨(outsidePositions F[i.val].scope.length (positions vs F[i.val].scope)).length, by
      simp only [get_contract_old, scope_constraint_touched f vs hi,
        List.length_append, List.length_map, List.length_singleton]
      omega⟩⟩

/-- The central port at an actual connector-scope position. -/
@[expose] def centralPort (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (k : Fin (connectors F vs).length) : Occurrence (contract f vs) :=
  ⟨⟨F.length, by simp⟩, ⟨k.val, by simpa only [get_contract_central] using k.isLt⟩⟩

@[simp] theorem connectorPort_var (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (i : Fin F.length) (hi : i ∈ touched F vs) : (connectorPort f vs i hi).var = connector F i := by
  simp [connectorPort, Occurrence.var, get_contract_old, scope_constraint_touched f vs hi]

@[simp] theorem centralPort_var (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (k : Fin (connectors F vs).length) : (centralPort f vs k).var = (connectors F vs)[k.val] := by
  simp [centralPort, Occurrence.var, get_contract_central]

/-- The connector's old-constraint endpoint reads its supplied finite bit. -/
theorem transport_connectorPort (f g : OccurrenceLabeling F Bool) (vs : List ℕ)
    (bits : Fin F.length → Bool) (central : List Bool) (i : Fin F.length)
    (hi : i ∈ touched F vs) :
    transport f vs g bits central (connectorPort f vs i hi) = bits i := by
  have hp : (positions vs F[i.val].scope).isEmpty = false := by
    simpa only [List.isEmpty_eq_false_iff] using (mem_touched vs i).mp hi
  change ((transportRows g vs bits central).getD i.val []).getD
    (outsidePositions F[i.val].scope.length (positions vs F[i.val].scope)).length false = bits i
  rw [transportRows_project]
  simp only [hp, Bool.false_eq_true, ↓reduceIte]
  rw [List.getD_append_right _ _ _ _ (by simp [project])]
  simp [project]

/-- The central endpoint reads the supplied central row at the actual scope position. -/
theorem transport_centralPort (f g : OccurrenceLabeling F Bool) (vs : List ℕ)
    (bits : Fin F.length → Bool) (central : List Bool) (k : Fin (connectors F vs).length) :
    transport f vs g bits central (centralPort f vs k) = central.getD k.val false := by
  change ((transportRows g vs bits central).getD F.length []).getD k.val false = _
  rw [get_transportRows_central]

/-- The touched-constraint end of every connector is honestly zero in the reference. -/
@[simp] theorem reference_connectorPort (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (i : Fin F.length) (hi : i ∈ touched F vs) :
    reference f vs (connectorPort f vs i hi) = false :=
  transport_connectorPort f f vs (fun _ => false) (listSingle (connectors F vs).length 0) i hi

/-- The central end of exactly the first connector is one. -/
@[simp] theorem reference_centralPort (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (k : Fin (connectors F vs).length) :
    reference f vs (centralPort f vs k) = decide (0 = k.val) := by
  change transport f vs f (fun _ => false) (listSingle (connectors F vs).length 0)
    (centralPort f vs k) = _
  rw [transport_centralPort, List.getD_eq_getElem _ _ (by
    simpa only [listSingle, List.length_map, List.length_range] using k.isLt)]
  simp only [listSingle, List.getElem_map, List.getElem_range]

/-- Surviving occurrence transport commutes with edge partnership. -/
theorem oldPort_partner (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (o : Occurrence F) (ho : o.var ∉ vs) :
    oldPort f vs (hF.partner o) (by rwa [← hF.partner_variable o]) =
      (edge_contract hF f vs).partner (oldPort f vs o ho) := by
  have hp : (hF.partner o).var ∉ vs := by rwa [← hF.partner_variable o]
  let p := oldPort f vs o ho
  let q := oldPort f vs (hF.partner o) hp
  have hv : q.var = p.var := by
    rw [oldPort_var, oldPort_var]
    exact (hF.partner_variable o).symm
  have hn : q ≠ p := by
    intro he
    exact hF.partner_constraint_ne o
      (Fin.ext (congrArg (fun a : Occurrence (contract f vs) => a.1.val) he).symm)
  exact ((edge_contract hF f vs).eq_or_eq_partner hv).resolve_left hn

/-- Arbitrary outside defects are preserved exactly by projection. -/
theorem inconsistent_transport_old (hF : EdgeInstance F) (f g : OccurrenceLabeling F Bool)
    (vs : List ℕ) (bits : Fin F.length → Bool) (central : List Bool)
    (o : Occurrence F) (ho : o.var ∉ vs) :
    Inconsistent (transport f vs g bits central) o.var ↔ Inconsistent g o.var := by
  calc
    _ ↔ Inconsistent (transport f vs g bits central) (oldPort f vs o ho).var := by
      rw [oldPort_var]
    _ ↔ transport f vs g bits central (oldPort f vs o ho) ≠
        transport f vs g bits central
          (oldPort f vs (hF.partner o) (by rwa [← hF.partner_variable o])) := by
      rw [(edge_contract hF f vs).inconsistent_iff, ← oldPort_partner hF f vs o ho]
    _ ↔ g o ≠ g (hF.partner o) := by rw [transport_oldPort, transport_oldPort]
    _ ↔ _ := (hF.inconsistent_iff g o).symm

/-- Every old outside variable retains its exact defect status under reference transport. -/
theorem inconsistent_reference_old (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool)
    (vs : List ℕ) (o : Occurrence F) (ho : o.var ∉ vs) :
    Inconsistent (reference f vs) o.var ↔ Inconsistent f o.var :=
  inconsistent_transport_old hF f f vs (fun _ => false) (listSingle (connectors F vs).length 0) o ho

/-- The central port at position `k` is the contracted edge partner of the `k`-th touched
constraint's fresh connector port. -/
theorem centralPort_eq_partner_connectorPort (hF : EdgeInstance F)
    (f : OccurrenceLabeling F Bool) (vs : List ℕ) (k : Fin (touched F vs).length) :
    centralPort f vs ⟨k.val, by simpa only [length_connectors] using k.isLt⟩ =
      (edge_contract hF f vs).partner
        (connectorPort f vs (touched F vs)[k.val] (List.getElem_mem k.isLt)) := by
  let i := (touched F vs)[k.val]
  let p := connectorPort f vs i (List.getElem_mem k.isLt)
  let q := centralPort f vs ⟨k.val, by simpa only [length_connectors] using k.isLt⟩
  have hv : q.var = p.var := by
    rw [centralPort_var, connectorPort_var]
    simp only [i, connectors, List.getElem_map]
  have hn : q ≠ p := by
    intro he
    have hh := congrArg (fun a : Occurrence (contract f vs) => a.1.val) he
    change F.length = i.val at hh
    have := i.isLt
    omega
  exact ((edge_contract hF f vs).eq_or_eq_partner hv).resolve_left hn

/-- The connector's defect is exactly disagreement of its two supplied endpoint bits. -/
theorem inconsistent_transport_connector (hF : EdgeInstance F)
    (f g : OccurrenceLabeling F Bool) (vs : List ℕ) (bits : Fin F.length → Bool)
    (central : List Bool) (k : Fin (touched F vs).length) :
    Inconsistent (transport f vs g bits central) (connector F (touched F vs)[k.val]) ↔
      bits (touched F vs)[k.val] ≠ central.getD k.val false := by
  let p := connectorPort f vs (touched F vs)[k.val] (List.getElem_mem k.isLt)
  calc
    _ ↔ Inconsistent (transport f vs g bits central) p.var := by rw [connectorPort_var]
    _ ↔ transport f vs g bits central p ≠
        transport f vs g bits central
          (centralPort f vs ⟨k.val, by simpa only [length_connectors] using k.isLt⟩) := by
      rw [(edge_contract hF f vs).inconsistent_iff,
        ← centralPort_eq_partner_connectorPort hF f vs k]
    _ ↔ _ := by rw [transport_connectorPort, transport_centralPort]

/-- The first connector is the unique new defect of the honest contracted reference. -/
@[expose] def baseConnector (F : CSP Table ℕ) (vs : List ℕ) (hne : touched F vs ≠ []) : ℕ :=
  connector F ((touched F vs).head hne)

/-- The actual finite connector defects, scanned by distinct touched-constraint position. -/
@[expose] def connectorDefects (F : CSP Table ℕ) (vs : List ℕ)
    (bits : Fin F.length → Bool) (central : List Bool) : List ℕ :=
  ((List.finRange (touched F vs).length).filter fun k =>
    bits (touched F vs)[k.val] != central.getD k.val false).map
      fun k => connector F (touched F vs)[k.val]

/-- Exact defect transport for arbitrary outside values and arbitrary finite connector rows. -/
theorem defects_transport (hF : EdgeInstance F) (f g : OccurrenceLabeling F Bool)
    (vs : List ℕ) (bits : Fin F.length → Bool) (central : List Bool) :
    defects (transport f vs g bits central) =
      (defects g \ vs.toFinset) ∪ (connectorDefects F vs bits central).toFinset := by
  ext v
  simp only [mem_defects, mem_union, mem_sdiff, List.mem_toFinset]
  constructor
  · intro hv
    have hm : v ∈ (contract f vs).vars := by
      obtain ⟨o, _, ho, _, _⟩ := hv
      exact ho ▸ o.var_mem
    have hset : v ∈ (F.vars.toFinset \ vs.toFinset) ∪ (connectors F vs).toFinset := by
      rw [← vars_contract f vs]
      exact List.mem_toFinset.mpr hm
    rcases mem_union.mp hset with hset | hset
    · obtain ⟨hm, hn⟩ := mem_sdiff.mp hset
      obtain ⟨o, rfl⟩ := (exists_occurrence_iff v).mpr (List.mem_toFinset.mp hm)
      have hout : o.var ∉ vs := by simpa using hn
      exact Or.inl ⟨(inconsistent_transport_old hF f g vs bits central o hout).mp hv, hout⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hset)
      obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hi
      have hd := (inconsistent_transport_connector hF f g vs bits central ⟨k, hk⟩).mp (he ▸ hv)
      exact Or.inr (List.mem_map.mpr ⟨⟨k, hk⟩,
        List.mem_filter.mpr ⟨by simp, by simpa using hd⟩, congrArg (connector F) he⟩)
  · rintro (⟨hv, hn⟩ | hv)
    · obtain ⟨o, p, ho, hp, hne⟩ := hv
      have hout : o.var ∉ vs := ho.symm ▸ hn
      rw [← ho]
      apply (inconsistent_transport_old hF f g vs bits central o hout).mpr
      exact ⟨o, p, rfl, hp.trans ho.symm, hne⟩
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
      exact (inconsistent_transport_connector hF f g vs bits central k).mpr
        (by simpa using (List.mem_filter.mp hk).2)

/-- Zero old connector ends and the honest central reference create one fresh defect. -/
theorem connectorDefects_zero (vs : List ℕ) (hne : touched F vs ≠ []) :
    (connectorDefects F vs (fun _ => false)
      (listSingle (connectors F vs).length 0)).toFinset = {baseConnector F vs hne} := by
  have hpos : 0 < (touched F vs).length := List.length_pos_iff.mpr hne
  have hpred (k : Fin (touched F vs).length) :
      (false != (listSingle (connectors F vs).length 0).getD k.val false) = true ↔ k.val = 0 := by
    rw [List.getD_eq_getElem _ _ (by simp [listSingle])]
    simp [listSingle, eq_comm]
  ext v
  simp only [connectorDefects, List.mem_toFinset, List.mem_map, List.mem_filter,
    List.mem_finRange, true_and, hpred, mem_singleton]
  constructor
  · rintro ⟨k, hk, he⟩
    have heq : k = ⟨0, hpos⟩ := Fin.ext hk
    subst k
    simpa only [baseConnector, List.getElem_zero] using he.symm
  · rintro rfl
    exact ⟨⟨0, hpos⟩, rfl, by simp only [baseConnector, List.getElem_zero]⟩

/-- General zero-connector transport deletes the old internal defects and inserts exactly one
fresh connector defect, even when every outside value has changed. -/
theorem card_defects_transport_zero (hF : EdgeInstance F) (f g : OccurrenceLabeling F Bool)
    (vs : List ℕ) (hne : touched F vs ≠ []) :
    (defects (transport f vs g (fun _ => false) (listSingle (connectors F vs).length 0))).card +
      (defects g ∩ vs.toFinset).card = (defects g).card + 1 := by
  have hfresh : baseConnector F vs hne ∉ defects g := by
    intro hv
    obtain ⟨o, _, ho, _, _⟩ := mem_defects.mp hv
    have hm : baseConnector F vs hne ∈ F.vars := ho ▸ o.var_mem
    exact connector_not_mem ((touched F vs).head hne) hm
  rw [defects_transport hF, connectorDefects_zero vs hne, union_singleton,
    card_insert_of_notMem (fun hm => hfresh (mem_sdiff.mp hm).1)]
  have hp := card_sdiff_add_card_inter (defects g) vs.toFinset
  omega

/-- Exact reference-defect transport: old outside defects survive and the single central
one-hot entry contributes exactly one fresh connector defect. -/
theorem defects_reference (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (hne : touched F vs ≠ []) :
    defects (reference f vs) = (defects f \ vs.toFinset) ∪ {baseConnector F vs hne} :=
  (defects_transport hF f f vs (fun _ => false) (listSingle (connectors F vs).length 0)).trans
    (by rw [connectorDefects_zero vs hne])

/-- The finite reference defect count deletes all old internal defects and inserts one.
A blossom supplies exactly one old internal defect, yielding count preservation. -/
theorem card_defects_reference (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool)
    (vs : List ℕ) (hne : touched F vs ≠ []) :
    (defects (reference f vs)).card + (defects f ∩ vs.toFinset).card = (defects f).card + 1 :=
  card_defects_transport_zero hF f f vs hne

/-- Observation 26's exact defect-count relation for the actual prepared blossom reference. -/
theorem card_defects_reference_blossom (hF : EdgeInstance F) {f : OccurrenceLabeling F Bool}
    {w : Walk F} (hb : w.IsBlossom Table.sem f) :
    (defects (reference f (internal w))).card = (defects f).card := by
  have hc := card_defects_reference hF f (internal w) (touched_ne_nil w hb.2.2.1)
  rw [defects_inter_internal hb, card_singleton] at hc
  omega

end Cslib.Logic.PL.CSP.Blossom
