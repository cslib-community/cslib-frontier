/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EdgeCSP.Blossom.Transport
public import CslibFrontier.Logics.Propositional.CSP.Edge.Walk.Map
public import CslibFrontier.Logics.Propositional.CSP.Occurrence.Enumeration
import Mathlib.Data.List.GetD

/-!
# Restoring surviving original incidences

Finite lookup in the actual original port list inverts whole-instance contraction away from
fresh connectors. The walk map retains original constraint positions and binary variable names.
The fallback is used only to make lookup total; the proved domain never reaches it.
-/

public section

namespace Cslib.Logic.PL.CSP.Blossom

open Table Finset
open Cslib.BitString

variable {F : CSP Table ℕ}

/-- A connector port at an old constraint is exactly that constraint's terminal fresh port.
The central alternative is excluded by its appended constraint index. -/
theorem exists_connectorPort (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool)
    (vs : List ℕ) (o : Occurrence (contract f vs)) (ho : o.var ∈ connectors F vs)
    (hindex : o.1.val < F.length) :
    ∃ i : Fin F.length, ∃ hi : i ∈ touched F vs, connectorPort f vs i hi = o := by
  rcases exists_connectorPort_or_centralPort hF f vs o ho with h | ⟨k, rfl⟩
  · exact h
  · exact absurd hindex (Nat.lt_irrefl F.length)

/-- Find an original outside port by scanning actual original incidences. -/
@[expose] def restorePort (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (o : Occurrence (contract f vs)) : Option (Occurrence F) :=
  (incidenceList F).find? fun p =>
    if hp : p.var ∈ vs then false else oldPort f vs p hp == o

/-- Nonconnector lookup returns an actual surviving port with exactly the requested image. -/
theorem restorePort_spec (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (o : Occurrence (contract f vs)) (ho : o.var ∉ connectors F vs) :
    ∃ p, restorePort f vs o = some p ∧ ∃ hp : p.var ∉ vs, oldPort f vs p hp = o := by
  obtain ⟨q, hq, heq⟩ := exists_oldPort hF f vs o ho
  cases he : restorePort f vs o with
  | none =>
    exact (List.find?_eq_none.mp he q (mem_incidenceList q)
      (by simp only [dite_eq_right hq, heq, beq_self_eq_true])).elim
  | some p =>
    have hh := List.find?_some he
    by_cases hp : p.var ∈ vs
    · simp only [dite_eq_left hp, Bool.false_eq_true] at hh
    · exact ⟨p, rfl, hp, by simpa only [dite_eq_right hp, beq_iff_eq] using hh⟩

/-- Total original-port lookup, with an explicit actual fallback for malformed requests. -/
@[expose] def restorePortOr (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (fallback : Occurrence F) (o : Occurrence (contract f vs)) : Occurrence F :=
  (restorePort f vs o).getD fallback

/-- On the certified domain the fallback is irrelevant and lookup is the actual inverse. -/
theorem restorePortOr_spec (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (fallback : Occurrence F) (o : Occurrence (contract f vs))
    (ho : o.var ∉ connectors F vs) :
    ∃ hp : (restorePortOr f vs fallback o).var ∉ vs,
      oldPort f vs (restorePortOr f vs fallback o) hp = o := by
  obtain ⟨p, he, hp, ho⟩ := restorePort_spec hF f vs o ho
  simpa only [restorePortOr, he, Option.getD_some] using ⟨hp, ho⟩

/-- Successful restoration retains the original binary variable name. -/
theorem restorePortOr_var (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (fallback : Occurrence F) (o : Occurrence (contract f vs)) (ho : o.var ∉ connectors F vs) :
    (restorePortOr f vs fallback o).var = o.var := by
  obtain ⟨hp, he⟩ := restorePortOr_spec hF f vs fallback o ho
  exact (oldPort_var f vs _ hp).symm.trans (congrArg Occurrence.var he)

/-- Successful restoration retains the actual original constraint position. -/
theorem restorePortOr_constraint (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool)
    (vs : List ℕ) (fallback : Occurrence F) (o : Occurrence (contract f vs))
    (ho : o.var ∉ connectors F vs) : (restorePortOr f vs fallback o).1.val = o.1.val := by
  obtain ⟨_, he⟩ := restorePortOr_spec hF f vs fallback o ho
  exact congrArg (fun p : Occurrence (contract f vs) => p.1.val) he

/-- Surviving original ports are embedded injectively in the actual output occurrence type. -/
theorem oldPort_injective (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    {o p : Occurrence F} (ho : o.var ∉ vs) (hp : p.var ∉ vs)
    (he : oldPort f vs o ho = oldPort f vs p hp) : o = p := by
  refine hF.eq_of_constraint_eq ?_ (Fin.ext (congrArg (fun a => a.1.val) he))
  rw [← oldPort_var f vs o ho, ← oldPort_var f vs p hp]
  exact congrArg Occurrence.var he

/-- Restoring an actual outside original port cancels the positional embedding. -/
theorem restorePortOr_oldPort (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool)
    (vs : List ℕ) (fallback o : Occurrence F) (ho : o.var ∉ vs) :
    restorePortOr f vs fallback (oldPort f vs o ho) = o := by
  obtain ⟨hp, he⟩ := restorePortOr_spec hF f vs fallback (oldPort f vs o ho) fun hc => by
    rw [oldPort_var] at hc
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hc
    exact connector_not_mem i (hi ▸ o.var_mem)
  exact oldPort_injective hF f vs hp ho he

/-- Restore each actual port of a contracted walk by the finite original-port lookup. -/
@[expose] def restoreWalk (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (fallback : Occurrence F) (p : Walk (contract f vs)) : Walk F :=
  Walk.mapPorts (restorePortOr f vs fallback) p

/-- A contracted trail avoiding connectors restores to an actual outside original trail with
the same variable endpoints. Repeated original constraints remain positional. -/
theorem restoreWalk_spec (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (fallback : Occurrence F) {p : Walk (contract f vs)} (hp : p.IsWalk)
    (hno : ∀ o ∈ p.edges, o.var ∉ connectors F vs) :
    (restoreWalk f vs fallback p).IsWalk ∧
      (restoreWalk f vs fallback p).finish = p.finish ∧
      ∀ o ∈ (restoreWalk f vs fallback p).edges, o.var ∉ vs := by
  have hv := fun o ho => restorePortOr_var hF f vs fallback o (hno o ho)
  refine ⟨hp.mapPorts _ hv (fun s hs => Fin.ext ?_) (fun o ho q hq heq => ?_),
    Walk.finish_mapPorts _ _ hv, fun o ho => ?_⟩
  · rw [restorePortOr_constraint hF f vs fallback s.1
        (hno _ (List.mem_flatMap.mpr ⟨s, hs, by simp⟩)),
      restorePortOr_constraint hF f vs fallback s.2
        (hno _ (List.mem_flatMap.mpr ⟨s, hs, by simp⟩))]
    exact congrArg Fin.val (DAG.linked_constraint hp.1 hs)
  · obtain ⟨hro, hero⟩ := restorePortOr_spec hF f vs fallback o (hno o ho)
    obtain ⟨hrq, herq⟩ := restorePortOr_spec hF f vs fallback q (hno q hq)
    have he : (⟨restorePortOr f vs fallback o, hro⟩ : {a : Occurrence F // a.var ∉ vs}) =
        ⟨restorePortOr f vs fallback q, hrq⟩ := Subtype.ext heq
    exact hero.symm.trans ((congrArg (fun a => oldPort f vs a.val a.property) he).trans herq)
  · rw [restoreWalk, Walk.edges_mapPorts] at ho
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ho
    exact (restorePortOr_spec hF f vs fallback q (hno q hq)).1

/-- Membership in a restored outside trail is the exact inverse of surviving-port transport. -/
theorem mem_restoreWalk_edges (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool)
    (vs : List ℕ) (fallback : Occurrence F) (p : Walk (contract f vs))
    (hno : ∀ o ∈ p.edges, o.var ∉ connectors F vs) (o : Occurrence F) (ho : o.var ∉ vs) :
    o ∈ (restoreWalk f vs fallback p).edges ↔ oldPort f vs o ho ∈ p.edges := by
  rw [restoreWalk, Walk.edges_mapPorts, List.mem_map]
  refine ⟨?_, fun hm => ⟨oldPort f vs o ho, hm, restorePortOr_oldPort hF f vs fallback o ho⟩⟩
  rintro ⟨q, hq, rfl⟩
  rwa [(restorePortOr_spec hF f vs fallback q (hno q hq)).2]

/-- Flipping a restored outside walk is exactly zero-expansion of the actual contracted flip. -/
theorem restoreWalk_flip (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool)
    (vs : List ℕ) (fallback : Occurrence F) (p : Walk (contract f vs))
    (hno : ∀ o ∈ p.edges, o.var ∉ connectors F vs) :
    (restoreWalk f vs fallback p).flip f = expandZero f vs (p.flip (reference f vs)) := by
  funext o
  by_cases ho : o.var ∈ vs
  · have hn : o ∉ (restoreWalk f vs fallback p).edges := fun hm => by
      rw [restoreWalk, Walk.edges_mapPorts] at hm
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
      exact (restorePortOr_spec hF f vs fallback q (hno q hq)).1 ho
    simp only [expandZero, dite_eq_left ho, Walk.flip, BitString.flipOn_apply,
      List.mem_toFinset, hn, ↓reduceIte]
  · simp only [expandZero, dite_eq_right ho, Walk.flip, BitString.flipOn_apply, List.mem_toFinset,
      mem_restoreWalk_edges hF f vs fallback p hno o ho, reference_oldPort]

/-- Avoiding connector variables leaves both endpoint values of every fresh connector at the
actual reference values, including the honest central one-hot row. -/
theorem flip_reference_connectors (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (p : Walk (contract f vs)) (hno : ∀ o ∈ p.edges, o.var ∉ connectors F vs) :
    (∀ i (hi : i ∈ touched F vs),
      p.flip (reference f vs) (connectorPort f vs i hi) = false) ∧
    (∀ k : Fin (connectors F vs).length,
      p.flip (reference f vs) (centralPort f vs k) =
        (listSingle (connectors F vs).length 0).getD k.val false) := by
  have hunchanged (o : Occurrence (contract f vs)) (ho : o.var ∈ connectors F vs) :
      p.flip (reference f vs) o = reference f vs o := by
    simp [Walk.flip, BitString.flipOn_apply, show o ∉ p.edges from fun he => hno o he ho]
  refine ⟨fun i hi => ?_, fun k => ?_⟩
  · rw [hunchanged _ (by simp [connectors, List.mem_map.mpr ⟨i, hi, rfl⟩]),
      reference_connectorPort]
  · rw [hunchanged _ (by simp [List.getElem_mem k.isLt]), reference_centralPort,
      List.getD_eq_getElem _ _
        (by simpa only [listSingle, List.length_map, List.length_range] using k.isLt)]
    simp [listSingle]

/-- Every connector-free contracted f-prefix restores to an original f-prefix. Each actual
intermediate row is reflected through connector zero, so arbitrary outside changes are allowed. -/
theorem restoreWalk_isFPrefix (hF : EdgeInstance F) {f : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) (vs : List ℕ) (fallback : Occurrence F)
    {p : Walk (contract f vs)} (hp : p.IsFPrefix sem (reference f vs))
    (hno : ∀ o ∈ p.edges, o.var ∉ connectors F vs) :
    (restoreWalk f vs fallback p).IsFPrefix sem f := by
  have hw := (restoreWalk_spec hF f vs fallback hp.1 hno).1
  refine ⟨hw, hp.2.1.mapPorts (restorePortOr f vs fallback) fun o ho => ?_,
    Walk.prefixValid_iff_forall_take.mpr fun n hn => ?_⟩
  · obtain ⟨hr, _⟩ := restorePortOr_spec hF f vs fallback o (hno o ho)
    simpa only [restorePortOr_var hF f vs fallback o (hno o ho)] using
      (inconsistent_reference_old hF f vs (restorePortOr f vs fallback o) hr).symm
  · have hnp : n ≤ p.steps.length := by simpa [restoreWalk, Walk.mapPorts] using hn
    have hno' : ∀ o ∈ (p.take n).edges, o.var ∉ connectors F vs := fun o ho =>
      hno o ((List.take_sublist n p.steps).flatMap (fun s => [s.1, s.2]) |>.subset ho)
    obtain ⟨hbits, hcentral⟩ := flip_reference_connectors f vs (p.take n) hno'
    have hv := valid_expandZero hF hf vs ((p.take n).flip (reference f vs))
      (hp.valid_take n hnp) hbits hcentral
    have htake : restoreWalk f vs fallback (p.take n) = (restoreWalk f vs fallback p).take n :=
      Walk.mapPorts_take ..
    rwa [← restoreWalk_flip hF f vs fallback (p.take n) hno', htake,
      Walk.flip, Walk.edges, ← Walk.flipSteps_eq_flipOn f _ (hw.take n).2] at hv

/-- Distinct endpoints are retained when restoring a contracted f-walk avoiding connectors. -/
theorem restoreWalk_isFWalk (hF : EdgeInstance F) {f : OccurrenceLabeling F Bool}
    (hf : ValidLabeling sem f) (vs : List ℕ) (fallback : Occurrence F)
    {p : Walk (contract f vs)} (hp : p.IsFWalk sem (reference f vs))
    (hno : ∀ o ∈ p.edges, o.var ∉ connectors F vs) :
    (restoreWalk f vs fallback p).IsFWalk sem f :=
  ⟨restoreWalk_isFPrefix hF hf vs fallback hp.1 hno, by
    rw [(restoreWalk_spec hF f vs fallback hp.1.1 hno).2.1]
    exact hp.2⟩

/-- The connector-free case of Lemma 44 returns the actual restored finite walk flip and
removes exactly two original defects, with no condition on changed outside comparison values. -/
theorem restore_augmentation (hF : EdgeInstance F) {f : OccurrenceLabeling F Bool}
    {w : Walk F} (hb : w.IsBlossom sem f) (hf : ValidLabeling sem f) (fallback : Occurrence F)
    {p : Walk (contract f (internal w))} (hp : p.IsAugmenting sem (reference f (internal w)))
    (hno : ∀ o ∈ p.edges, o.var ∉ connectors F (internal w)) :
    ValidLabeling sem ((restoreWalk f (internal w) fallback p).flip f) ∧
      (defects ((restoreWalk f (internal w) fallback p).flip f)).card + 2 = (defects f).card := by
  have hq := restoreWalk_isFPrefix hF hf (internal w) fallback hp.1.1 hno
  refine ⟨by simpa only [Walk.take, List.take_length] using hq.valid_take _ le_rfl, ?_⟩
  obtain ⟨hbits, hcentral⟩ := flip_reference_connectors f (internal w) p hno
  rw [restoreWalk_flip hF f (internal w) fallback p hno,
    card_defects_expandZero hF hb _ hbits hcentral]
  exact (hp.card_defects_flip_add_two (edge_contract hF f (internal w))).trans
    (card_defects_reference_blossom hF hb)

end Cslib.Logic.PL.CSP.Blossom
