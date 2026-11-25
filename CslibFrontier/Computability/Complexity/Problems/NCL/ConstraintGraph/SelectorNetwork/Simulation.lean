/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.Legality

/-!
# Exact simulation by weighted selector networks

The source uses a shared character bit in its row clause and all binary exclusions. The physical
network replaces every occurrence by its own edge. Its canonical state points a unit edge towards
its character exactly when the character is selected. Extra incoming unit edges can be cleared
individually, which connects every legal fiber to this canonical state.

## Main definitions

* `SelectorNetwork.sourceGraph`: the nonempty-row and negative binary clauses.
* `SelectorNetwork.encode`: the canonical physical orientation.

## Main results

* `SelectorNetwork.simulation`: the weighted physical graph simulates the shared constraints.
-/

public section

namespace Cslib.Complexity.NCL.SelectorNetwork

variable {U C R : Type*} [DecidableEq U] (N : SelectorNetwork U C R)

/-- Shared selector constraints before introducing separate relation edges. -/
@[expose] def sourceGraph : ConstraintGraph (U ⊕ R) C
  | .inl u => Vertex.clause ((N.characters.filter fun c => decide (N.row c = u)).map
      fun c => ⟨c, true⟩)
  | .inr r =>
    { ports := [⟨⟨N.endpoint r false, false⟩, 1⟩, ⟨⟨N.endpoint r true, false⟩, 1⟩]
      minInflow := if N.required r then 1 else 0 }

/-- Nonempty rows and the specified pair exclusions on character selections. -/
structure SourceLegal (s : C → Bool) : Prop where
  /-- A row contains a selected character. -/
  nonempty : ∀ u, ∃ c, N.row c = u ∧ s c = true
  /-- A required relation has an absent endpoint. -/
  relation : ∀ r, N.required r = true → s (N.endpoint r false) = false ∨
    s (N.endpoint r true) = false

/-- The shared constraints express exactly nonempty compatible selections. -/
theorem legal_source_iff (s : C → Bool) : N.sourceGraph.Legal s ↔ N.SourceLegal s := by
  have hrow (u : U) : (N.sourceGraph (.inl u)).Sat s ↔ ∃ c, N.row c = u ∧ s c = true := by
    simp [sourceGraph, Vertex.sat_clause_iff, Port.In, N.characters_complete]
  have hrel (r : R) : (N.sourceGraph (.inr r)).Sat s ↔
      N.required r = true → s (N.endpoint r false) = false ∨ s (N.endpoint r true) = false := by
    cases hr : N.required r <;> cases hl : s (N.endpoint r false) <;>
      cases hh : s (N.endpoint r true) <;>
      simp [sourceGraph, Vertex.Sat, Vertex.inflow, Port.In, hr, hl, hh]
  exact ⟨fun hs => ⟨fun u => (hrow u).mp (hs (.inl u)), fun r => (hrel r).mp (hs (.inr r))⟩,
    fun hs => Sum.rec (fun u => (hrow u).mpr (hs.nonempty u))
      fun r => (hrel r).mpr (hs.relation r)⟩

variable [DecidableEq C] [DecidableEq R]

/-- Canonical physical state: each unit edge follows the selection at its character endpoint. -/
@[expose] def encode (s : C → Bool) : Edge C R → Bool
  | .inl c => s c
  | .inr e => s (N.endpoint e.1 e.2)

/-- Reading the selector edges of a legal physical orientation satisfies the shared clauses. -/
theorem legal_project {s : Edge C R → Bool} (hs : N.graph.Legal s) :
    N.sourceGraph.Legal (s ∘ Sum.inl) := by
  have ht := (legal_iff N s).mp hs
  refine (legal_source_iff N _).mpr ⟨ht.nonempty, fun r hr => ?_⟩
  exact (ht.relation r hr).imp
    (fun h => Bool.eq_false_iff.mpr fun hc =>
      Bool.noConfusion ((ht.forced r false hc).symm.trans h))
    (fun h => Bool.eq_false_iff.mpr fun hc =>
      Bool.noConfusion ((ht.forced r true hc).symm.trans h))

/-- Canonical physical orientations have exactly the source legality conditions. -/
theorem legal_encode_iff (s : C → Bool) : N.graph.Legal (N.encode s) ↔ N.sourceGraph.Legal s :=
  ⟨legal_project N, fun hs =>
    have hsrc := (legal_source_iff N s).mp hs
    (legal_iff N _).mpr ⟨hsrc.nonempty, fun _ _ h => h, hsrc.relation⟩⟩

private def clear (a : C → Bool) (s : Edge C R → Bool) : List (R × Bool) → Edge C R → Bool
  | [] => s
  | e :: es => clear a (Function.update s (.inr e) (a (N.endpoint e.1 e.2))) es

omit [DecidableEq U] in
private theorem clear_selector (a : C → Bool) (s : Edge C R → Bool) (es : List (R × Bool))
    (c : C) : clear N a s es (.inl c) = s (.inl c) := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih => simp [clear, ih]

omit [DecidableEq U] in
private theorem clear_branch (a : C → Bool) (s : Edge C R → Bool) (es : List (R × Bool))
    (e : R × Bool) : clear N a s es (.inr e) =
      if e ∈ es then a (N.endpoint e.1 e.2) else s (.inr e) := by
  induction es generalizing s with
  | nil => rfl
  | cons f es ih =>
    simp only [clear, ih, List.mem_cons]
    by_cases hef : e = f <;> simp [hef]

private theorem legal_clear_one (a : C → Bool) {s : Edge C R → Bool} (hs : N.graph.Legal s)
    (hsel : ∀ c, s (.inl c) = a c) (e : R × Bool) :
    N.graph.Legal (Function.update s (.inr e) (a (N.endpoint e.1 e.2))) := by
  have hsrc := (legal_iff N s).mp hs
  refine (legal_iff N _).mpr
    ⟨by simpa only [Function.update_of_ne Sum.inl_ne_inr] using hsrc.nonempty,
      fun r b hc => ?_, fun r hr => ?_⟩
  · rcases eq_or_ne (r, b) e with rfl | he
    · simpa only [Function.update_self] using (hsel (N.endpoint r b)).symm.trans
        (by simpa only [Function.update_of_ne Sum.inl_ne_inr] using hc)
    · rw [Function.update_of_ne (Sum.inr_injective.ne he)]
      exact hsrc.forced r b (by simpa only [Function.update_of_ne Sum.inl_ne_inr] using hc)
  · have lower (b : Bool) (hb : s (.inr (r, b)) = false) :
        Function.update s (.inr e) (a (N.endpoint e.1 e.2)) (.inr (r, b)) = false := by
      rcases eq_or_ne (r, b) e with rfl | he
      · rw [Function.update_self, Bool.eq_false_iff]
        exact fun ha => Bool.noConfusion ((hsrc.forced r b ((hsel _).trans ha)).symm.trans hb)
      · simpa only [Function.update_of_ne (Sum.inr_injective.ne he)] using hb
    exact (hsrc.relation r hr).imp (lower false) (lower true)

private theorem clear_path (a : C → Bool) (es : List (R × Bool))
    {s : Edge C R → Bool} (hs : N.graph.Legal s) (hsel : ∀ c, s (.inl c) = a c) :
    N.graph.Reachable s (clear N a s es) := by
  induction es generalizing s with
  | nil => exact .refl
  | cons e es ih =>
    let t := Function.update s (.inr e) (a (N.endpoint e.1 e.2))
    have ht : N.graph.Legal t := legal_clear_one N a hs hsel e
    refine (?_ : N.graph.Reachable s t).trans (ih ht fun c => by simp [t, hsel])
    by_cases he : s (.inr e) = a (N.endpoint e.1 e.2)
    · exact (show t = s by simpa only [t, ← he] using Function.update_eq_self (.inr e) s).symm ▸
        .refl
    · exact .single ⟨hs, ht, .inr e, by
        cases hsbit : s (.inr e) <;> cases hab : a (N.endpoint e.1 e.2) <;>
          simp_all [t, reverse]⟩

/-- Clearing surplus unit-edge supply connects every legal orientation to its canonical fiber. -/
theorem reachable_encode_project {s : Edge C R → Bool} (hs : N.graph.Legal s) :
    N.graph.Reachable s (N.encode (s ∘ Sum.inl)) := by
  refine (show clear N (s ∘ Sum.inl) s N.branches = N.encode (s ∘ Sum.inl) from funext ?_) ▸
    clear_path N (s ∘ Sum.inl) N.branches hs fun _ => rfl
  rintro (c | ⟨r, b⟩)
  · exact clear_selector N _ _ _ c
  · have hm : (r, b) ∈ N.branches := by cases b <;> simp [branches, N.relations_complete r]
    simp [clear_branch, hm, encode]

private def prepare (s t : C → Bool) : Edge C R → Bool
  | .inl c => s c
  | .inr e => t (N.endpoint e.1 e.2)

private theorem legal_prepare {s t : C → Bool} (hs : N.sourceGraph.Legal s)
    (ht : N.sourceGraph.Legal t) (hle : ∀ c, s c ≤ t c) : N.graph.Legal (prepare N s t) := by
  have hsrc := (legal_source_iff N s).mp hs
  exact (legal_iff N _).mpr ⟨hsrc.nonempty,
    fun r b hc => Bool.eq_true_of_true_le (hc ▸ hle (N.endpoint r b)),
    ((legal_source_iff N t).mp ht).relation⟩

private theorem lift_add (s : C → Bool) (c : C) (hs : N.sourceGraph.Legal s)
    (ht : N.sourceGraph.Legal (reverse s c)) (hc : s c = false) :
    N.graph.Reachable (N.encode s) (N.encode (reverse s c)) := by
  have hp := legal_prepare N hs ht fun d => by
    rcases eq_or_ne d c with rfl | hd
    · simp [hc]
    · rw [reverse_of_ne s hd]
  have hpath : N.graph.Reachable (prepare N s (reverse s c)) (N.encode s) :=
    reachable_encode_project N hp
  refine hpath.symm.tail ⟨hp, (legal_encode_iff N _).mpr ht, .inl c, (funext ?_).symm⟩
  rintro (d | e)
  · by_cases hd : d = c <;> simp [reverse, prepare, encode, hd]
  · exact reverse_of_ne _ Sum.inr_ne_inl

private theorem lift_step {s t : C → Bool} (hm : N.sourceGraph.Step s t) :
    N.graph.Reachable (N.encode s) (N.encode t) := by
  obtain ⟨hs, ht, c, rfl⟩ := hm
  cases hc : s c with
  | false => exact lift_add N s c hs ht hc
  | true =>
    simpa only [reverse_reverse] using (lift_add N (reverse s c) c ht
      (by simpa only [reverse_reverse] using hs) (by simp [hc])).symm

/-- Independent relation ports implement the shared selector clauses with exact reachability. -/
def simulation : ConstraintGraph.Simulation N.sourceGraph N.graph where
  abs s := s ∘ Sum.inl
  enc := N.encode
  abs_enc _ := rfl
  step_abs {s t} hm := by
    obtain ⟨hs, ht, e, rfl⟩ := hm
    rcases e with c | e
    · exact .single ⟨legal_project N hs, legal_project N ht, c,
        reverse_comp_of_injective Sum.inl_injective s c⟩
    · rw [reverse_comp_of_not_mem_range s (fun _ => Sum.inl_ne_inr)]
  step_enc hm := lift_step N hm
  legal_abs hs := legal_project N hs
  legal_enc hs := (legal_encode_iff N _).mpr hs

/-- The simulation encodes each relation port by its character's selected bit. -/
@[simp] theorem simulation_enc (s : C → Bool) : N.simulation.enc s = N.encode s := by
  simp only [simulation]

/-- The simulation reads exactly the character selector edges. -/
@[simp] theorem simulation_abs (s : Edge C R → Bool) :
    N.simulation.abs s = s ∘ Sum.inl := by
  simp only [simulation]

end Cslib.Complexity.NCL.SelectorNetwork
