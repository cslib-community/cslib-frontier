/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Edge.Walk.Operations

/-!
# Transporting actual incidence walks

Port transport between positional CSP lists retains the original variable names. Linkage,
endpoint and nonreuse proofs require preservation only at the actual used ports. This permits
total executable lookup maps with an irrelevant fallback outside their certified domain.
-/

public section

namespace Cslib.Logic.PL.CSP.Walk

variable {Rel Rel' V : Type*} {F : CSP Rel V} {G : CSP Rel' V}

/-- Map actual incidence pairs, retaining the original starting variable. -/
@[expose] def mapPorts (port : Occurrence F → Occurrence G) (w : Walk F) : Walk G :=
  ⟨w.start, w.steps.map fun (input, output) => (port input, port output)⟩

/-- The transported incidence list is the original finite incidence list mapped portwise. -/
theorem edges_mapPorts (port : Occurrence F → Occurrence G) (w : Walk F) :
    (mapPorts port w).edges = w.edges.map port := by
  obtain ⟨_, ss⟩ := w
  induction ss with
  | nil => rfl
  | cons s _ ih =>
    rcases s with ⟨input, output⟩
    simpa only [mapPorts, edges, edgesOf_cons, List.map_cons] using
      congrArg (port input :: port output :: ·) ih

/-- Actual-port transport commutes with every variable-ended prefix. -/
theorem mapPorts_take (port : Occurrence F → Occurrence G) (w : Walk F) (n : ℕ) :
    mapPorts port (w.take n) = (mapPorts port w).take n := by
  simp [mapPorts, take, List.map_take]

private theorem linked_mapPorts (port : Occurrence F → Occurrence G)
    {v : V} {ss : List (Occurrence F × Occurrence F)} (hl : Linked v ss)
    (hv : ∀ o ∈ edgesOf ss, (port o).var = o.var)
    (hc : ∀ s ∈ ss, let (input, output) := s; (port input).1 = (port output).1) :
    Linked v (ss.map fun (input, output) => (port input, port output)) := by
  induction ss generalizing v with
  | nil => trivial
  | cons s ss ih =>
    rcases s with ⟨input, output⟩
    refine ⟨(hv input (by simp [edgesOf_cons])).trans hl.1, hc _ List.mem_cons_self, ?_⟩
    rw [hv output (by simp [edgesOf_cons])]
    exact ih hl.2.2 (fun o ho => hv o (by simp [edgesOf_cons, ho]))
      fun s hs => hc s (List.mem_cons_of_mem _ hs)

/-- Preserving used variable names and step constraints, with injectivity on used ports,
transports a genuine incidence trail between the original positional CSP list models. -/
theorem IsWalk.mapPorts (port : Occurrence F → Occurrence G) {w : Walk F} (hw : w.IsWalk)
    (hv : ∀ o ∈ w.edges, (port o).var = o.var)
    (hc : ∀ s ∈ w.steps, let (input, output) := s; (port input).1 = (port output).1)
    (hi : ∀ o ∈ w.edges, ∀ p ∈ w.edges, port o = port p → o = p) :
    (mapPorts port w).IsWalk := by
  exact ⟨linked_mapPorts port hw.1 hv hc, edges_mapPorts port w ▸ hw.2.map_on hi⟩

/-- Used-variable preservation retains the actual final variable, also for the empty walk. -/
theorem finish_mapPorts (port : Occurrence F → Occurrence G) (w : Walk F)
    (hv : ∀ o ∈ w.edges, (port o).var = o.var) : (mapPorts port w).finish = w.finish := by
  obtain ⟨v, ss⟩ := w
  induction ss generalizing v with
  | nil => rfl
  | cons s ss ih =>
    rcases s with ⟨input, output⟩
    change finishFrom (port output).var _ = finishFrom output.var ss
    rw [hv output (by simp [edges, edgesOf_cons])]
    exact ih output.var fun o ho =>
      hv o (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ho))

/-- Internal consistency transports when defect status agrees at each actual used port. -/
theorem InternallyConsistent.mapPorts (port : Occurrence F → Occurrence G)
    {f : OccurrenceLabeling F Bool} {g : OccurrenceLabeling G Bool}
    {ss : List (Occurrence F × Occurrence F)} (hi : InternallyConsistent f ss)
    (hd : ∀ o ∈ edgesOf ss, Inconsistent g (port o).var ↔ Inconsistent f o.var) :
    InternallyConsistent g (ss.map fun (input, output) => (port input, port output)) := by
  induction ss with
  | nil => trivial
  | cons s ss ih =>
    rcases s with ⟨input, output⟩
    refine ⟨?_, ih hi.2 (fun o ho => hd o (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ ho)))⟩
    rcases hi.1 with he | hn
    · exact Or.inl (by rw [he]; rfl)
    · exact Or.inr (fun h => hn ((hd output (by simp [edgesOf_cons])).mp h))

end Cslib.Logic.PL.CSP.Walk
