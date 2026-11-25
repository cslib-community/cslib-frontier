/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EdgeCSP.Blossom.Reference
public import CslibFrontier.Logics.Propositional.CSP.Table.ContractionRows
public import CslibFrontier.Logics.Propositional.CSP.Edge.Ports
import Mathlib.Data.List.GetD
import CslibFrontier.Foundations.Data.List.Blocks

/-!
# Transporting changed outside labels through whole contraction

Building on `transport` and its port and defect rules in `Reference.lean` (alongside the
zero-connector `reference` specialization), this module proves constraint validity and
zero-connector expansion agreement for transported labelings in Section 5.3 of
[KazdaKolmogorovRolinek2018], arXiv:1602.03124v6, printed pp. 12–13. Connector zero fixes the
internal reference bits without restricting outside changes, connector one records one changed
internal port, and contracted occurrences are classified into outside and connector ports.
-/

public section

namespace Cslib.Logic.PL.CSP.Blossom

open Table Finset
open Cslib.BitString

variable {F : CSP Table ℕ}

/-- Feasible original rows with at most one selected deviation transport to feasible actual
contracted labels, with their computed connector bits and any accepted central one-hot row. -/
theorem valid_transport {f g : OccurrenceLabeling F Bool} (hf : ValidLabeling sem f)
    (hg : ValidLabeling sem g) (vs : List ℕ) (bits : Fin F.length → Bool)
    {central : List Bool} (hc : (exactlyOne (connectors F vs)).sem central = true)
    (hd : ∀ i ∈ touched F vs, deviations (localTuple f i) (localTuple g i)
      (positions vs F[i.val].scope) ≤ 1)
    (hb : ∀ i ∈ touched F vs, bits i = decide (deviations (localTuple f i)
      (localTuple g i) (positions vs F[i.val].scope) = 1)) :
    ValidLabeling sem (transport f vs g bits central) := by
  refine valid_labels _ _ (transportRows_length f g vs bits (sem_exactlyOne_eq_true _ _ |>.mp hc).1)
    fun i => ?_
  if hi : i.val < F.length then
    let j : Fin F.length := ⟨i.val, hi⟩
    rw [get_contract_old f vs j, get_transportRows_old g vs bits central j, constraint]
    split
    · exact hg j
    next hp =>
      have hj : j ∈ touched F vs := (mem_touched vs j).mpr (by simpa using hp)
      exact (sem_contract_eq_true (canContract_constraint hf vs j)).mpr
        ⟨localTuple g j, (sem_eq_true.mp (hg j)).2, hd j hj, by
          simp only [localTuple, List.length_ofFn, hb j hj]⟩
  else
    have he : i.val = F.length := by
      have := i.isLt
      simp only [length_contract] at this
      omega
    simpa only [he, get_contract_central, get_transportRows_central] using hc

/-- Zero connectors reflect validity for arbitrary outside changes when the internal reference
bits are retained. This is the local inverse used before the first new connector of a walk. -/
theorem valid_of_transport_zero {f g : OccurrenceLabeling F Bool} (hf : ValidLabeling sem f)
    (vs : List ℕ) {central : List Bool}
    (hc : central.length = (connectors F vs).length)
    (hi : ∀ o : Occurrence F, o.var ∈ vs → g o = f o)
    (hg : ValidLabeling sem (transport f vs g (fun _ => false) central)) :
    ValidLabeling sem g := by
  intro i
  let j : Fin (contract f vs).length := ⟨i.val, by
    have := i.isLt
    simp only [length_contract]
    omega⟩
  have hv := hg j
  change (contract f vs)[i.val].rel.sem
    (localTuple (labels _ (transportRows g vs (fun _ => false) central)) j) = true at hv
  rw [localTuple_labels _ _ j (transportRows_length f g vs _ hc j),
    get_contract_old f vs i, get_transportRows_old g vs (fun _ => false) central i] at hv
  unfold constraint at hv
  split at hv
  · exact hv
  · apply (sem_contract_zero_iff (canContract_constraint hf vs i) (by simp [localTuple]) ?_).mp
      (by simpa only [localTuple, List.length_ofFn] using hv)
    intro k hk
    have hkb := List.mem_range.mp (List.mem_filter.mp hk).1
    have hkv := (mem_positions vs i ⟨k, hkb⟩).mp hk
    simpa [localTuple, hkb] using hi ⟨i, ⟨k, hkb⟩⟩ hkv

/-- Every nonconnector port of the actual contracted edge instance is a surviving old port. -/
theorem exists_oldPort (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (o : Occurrence (contract f vs)) (ho : o.var ∉ connectors F vs) :
    ∃ p : Occurrence F, ∃ hp : p.var ∉ vs, oldPort f vs p hp = o := by
  have hv : o.var ∈ F.vars.toFinset \ vs.toFinset :=
    (mem_union.mp (vars_contract f vs ▸ List.mem_toFinset.mpr o.var_mem)).resolve_right
      (by simpa using ho)
  obtain ⟨p, hpv⟩ := (exists_occurrence_iff o.var).mpr (List.mem_toFinset.mp (mem_sdiff.mp hv).1)
  have hp : p.var ∉ vs := by simpa only [hpv, List.mem_toFinset] using (mem_sdiff.mp hv).2
  rcases (edge_contract hF f vs).eq_or_eq_partner
      (show o.var = (oldPort f vs p hp).var by rw [oldPort_var, hpv]) with he | he
  · exact ⟨p, hp, he.symm⟩
  · exact ⟨hF.partner p, by rwa [← hF.partner_variable p],
      (oldPort_partner hF f vs p hp).trans he.symm⟩

/-- Every connector port of the contracted edge instance is either a touched old constraint's
terminal fresh port or a central exactly-one port. -/
theorem exists_connectorPort_or_centralPort (hF : EdgeInstance F)
    (f : OccurrenceLabeling F Bool) (vs : List ℕ) (o : Occurrence (contract f vs))
    (ho : o.var ∈ connectors F vs) :
    (∃ i : Fin F.length, ∃ hi : i ∈ touched F vs, connectorPort f vs i hi = o) ∨
      ∃ k : Fin (connectors F vs).length, centralPort f vs k = o := by
  obtain ⟨i, hi, he⟩ := List.mem_map.mp ho
  obtain ⟨k, hk, hki⟩ := List.mem_iff_getElem.mp hi
  subst i
  have hoa : o.var = (connectorPort f vs (touched F vs)[k] (List.getElem_mem hk)).var := by
    rw [connectorPort_var]
    exact he.symm
  rcases (edge_contract hF f vs).eq_or_eq_partner hoa with heq | heq
  · exact Or.inl ⟨(touched F vs)[k], List.getElem_mem hk, heq.symm⟩
  · exact Or.inr ⟨⟨k, by simpa only [length_connectors] using hk⟩,
      (centralPort_eq_partner_connectorPort hF f vs ⟨k, hk⟩).trans heq.symm⟩

/-- Restore every original internal reference bit and read all changed outside bits from their
actual surviving contracted ports. This is a total executable finite-label construction. -/
@[expose] def expandZero (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (g : OccurrenceLabeling (contract f vs) Bool) : OccurrenceLabeling F Bool :=
  fun o => if ho : o.var ∈ vs then f o else g (oldPort f vs o ho)

/-- If the connector endpoints keep their reference values, projecting the restored labels
recovers every actual contracted label, including arbitrary changed outside values. -/
theorem transport_expandZero (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool)
    (vs : List ℕ) (g : OccurrenceLabeling (contract f vs) Bool)
    (hbits : ∀ i (hi : i ∈ touched F vs), g (connectorPort f vs i hi) = false)
    (hcentral : ∀ k : Fin (connectors F vs).length,
      g (centralPort f vs k) = (listSingle (connectors F vs).length 0).getD k.val false) :
    transport f vs (expandZero f vs g) (fun _ => false)
      (listSingle (connectors F vs).length 0) = g := by
  funext o
  by_cases ho : o.var ∈ connectors F vs
  · rcases exists_connectorPort_or_centralPort hF f vs o ho with ⟨i, hi, rfl⟩ | ⟨k, rfl⟩
    · rw [transport_connectorPort, hbits i hi]
    · rw [transport_centralPort, hcentral k]
  · obtain ⟨p, hp, rfl⟩ := exists_oldPort hF f vs o ho
    rw [transport_oldPort]
    simp only [expandZero, dite_eq_right hp]

/-- Restoring a valid zero-connector comparison gives a valid original labeling; outside
coordinates need not agree with the prepared reference. -/
theorem valid_expandZero (hF : EdgeInstance F) {f : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) (vs : List ℕ) (g : OccurrenceLabeling (contract f vs) Bool)
    (hg : ValidLabeling sem g)
    (hbits : ∀ i (hi : i ∈ touched F vs), g (connectorPort f vs i hi) = false)
    (hcentral : ∀ k : Fin (connectors F vs).length,
      g (centralPort f vs k) = (listSingle (connectors F vs).length 0).getD k.val false) :
    ValidLabeling sem (expandZero f vs g) := by
  apply valid_of_transport_zero hf vs (central := listSingle (connectors F vs).length 0)
    (by simp [listSingle]) (fun o ho => by simp only [expandZero, dite_eq_left ho])
  rwa [transport_expandZero hF f vs g hbits hcentral]

/-- A prepared blossom's internal defect is retained by zero expansion, and therefore the
expanded original labeling has exactly the returned comparison's defect count. -/
theorem card_defects_expandZero (hF : EdgeInstance F) {f : OccurrenceLabeling F Bool}
    {w : Walk F} (hb : w.IsBlossom sem f) (g : OccurrenceLabeling (contract f (internal w)) Bool)
    (hbits : ∀ i (hi : i ∈ touched F (internal w)),
      g (connectorPort f (internal w) i hi) = false)
    (hcentral : ∀ k : Fin (connectors F (internal w)).length,
      g (centralPort f (internal w) k) =
        (listSingle (connectors F (internal w)).length 0).getD k.val false) :
    (defects (expandZero f (internal w) g)).card = (defects g).card := by
  let e := expandZero f (internal w) g
  have hi : defects e ∩ (internal w).toFinset = defects f ∩ (internal w).toFinset :=
    defects_inter_eq_of_eqOn _ (fun o ho => by
      simp only [e, expandZero, dite_eq_left (List.mem_toFinset.mp ho)])
  have hc := card_defects_transport_zero hF f e (internal w) (touched_ne_nil w hb.2.2.1)
  rw [transport_expandZero hF f (internal w) g hbits hcentral, hi,
    defects_inter_internal hb, card_singleton] at hc
  change (defects e).card = (defects g).card
  omega

end Cslib.Logic.PL.CSP.Blossom
