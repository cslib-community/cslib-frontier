/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.Cells
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.Legality
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Replacement.Incidence

/-!
# Compiling selector networks to AND/OR graphs

One character in each row is drawn as the reversed output of its OR tree. All other row
characters are inputs. Character trees force their incident relation branches, and every
relation is replaced by a blue bend or two independent free endpoints. Shared edges retain
their selector and relation names; all implementation wires are private to one source vertex.

## Main definitions

* `SelectorNetwork.RowSection`: a chosen character in every row.
* `SelectorNetwork.AndOr.graph`: the closed standard implementation.

## Main results

* `SelectorNetwork.AndOr.simulation`: exact simulation of the complete weighted network.
-/

public section

attribute [local implicit_reducible] Cslib.Complexity.NCL.Diagram.Inner
  Cslib.Complexity.NCL.Diagram.instDecidableEqInner

namespace Cslib.Complexity.NCL.SelectorNetwork

/-- A chosen character in each row, used as the final OR-tree port. -/
structure RowSection {U C R : Type*} (N : SelectorNetwork U C R) where
  /-- The chosen character. -/
  character : U → C
  /-- The character belongs to the indicated row. -/
  row_character : ∀ u, N.row (character u) = u

namespace AndOr

open Diagram

variable {U C R : Type*} [DecidableEq U] [DecidableEq C] [DecidableEq R]
variable (N : SelectorNetwork U C R) (A : RowSection N)

/-- All characters in a row except its chosen final port. -/
@[expose] def rowInputs (u : U) : List C :=
  N.characters.filter fun c => decide (N.row c = u ∧ c ≠ A.character u)

/-- The implementation shape at each source vertex. -/
abbrev cell : Vert U C R → Cell
  | .inl u => .row (rowInputs N A u).length
  | .inr (.inl c) => .character (N.incident c).length
  | .inr (.inr r) => .relation (N.required r)

private def input {α : Type*} (xs : List α)
    (i : Fin (Gadgets.OrTree.bundle xs.length).length) : α :=
  xs.get (i.cast (Gadgets.OrTree.length_bundle xs.length))

private theorem input_mem {α : Type*} (xs : List α)
    (i : Fin (Gadgets.OrTree.bundle xs.length).length) : input xs i ∈ xs :=
  List.get_mem _ _

private theorem input_injective {α : Type*} (xs : List α) (hxs : xs.Nodup) :
    Function.Injective (input xs) := fun _ _ hij =>
  Fin.ext (congrArg (fun k : Fin xs.length => k.val) (hxs.injective_get hij))

private theorem exists_input {α : Type*} (xs : List α) {x : α} (hx : x ∈ xs) :
    ∃ i, input xs i = x := by
  obtain ⟨i, hi⟩ := List.get_of_mem hx
  exact ⟨i.cast (Gadgets.OrTree.length_bundle xs.length).symm, hi⟩

/-- The original edge at each local boundary port. -/
@[expose] def port : (v : Vert U C R) →
    Fin (cell N A v).top.length ⊕ Fin (cell N A v).bottom.length → Edge C R
  | .inl u, .inl i => .inl ((rowInputs N A u).get (i.cast (Gadgets.OrTree.length_bundle _)))
  | .inl u, .inr _ => .inl (A.character u)
  | .inr (.inl c), .inl i => .inr ((N.incident c).get (i.cast (Gadgets.OrTree.length_bundle _)))
  | .inr (.inl c), .inr _ => .inl c
  | .inr (.inr _), .inl i => i.elim0
  | .inr (.inr r), .inr i => .inr (r, decide (i.val = 1))

/-- Only the final row character uses a reversed local reference direction. -/
@[expose] def polarity : Vert U C R → Edge C R → Bool
  | .inl u, e => decide (e = .inl (A.character u))
  | .inr _, _ => false

attribute [local implicit_reducible] Cell.generator port

omit [DecidableEq R] in
private theorem port_injective (v : Vert U C R) : Function.Injective (port N A v) := by
  rcases v with u | (c | r)
  · rintro (i | i) (j | j) h
    · exact congrArg Sum.inl (input_injective _ (N.characters_nodup.filter _) (Sum.inl.inj h))
    · exact absurd (Sum.inl.inj h) (of_decide_eq_true (List.mem_filter.mp (input_mem _ i)).2).2
    · exact absurd (Sum.inl.inj h).symm (of_decide_eq_true (List.mem_filter.mp (input_mem _ j)).2).2
    · exact congrArg Sum.inr (Subsingleton.elim (α := Fin 1) i j)
  · rintro (i | i) (j | j) h
    · exact congrArg Sum.inl (input_injective _ ((N.branches_nodup).filter _) (Sum.inr.inj h))
    · cases h
    · cases h
    · exact congrArg Sum.inr (Subsingleton.elim (α := Fin 1) i j)
  · rintro (i | i) (j | j) h
    · exact i.elim0
    · exact i.elim0
    · exact j.elim0
    · have hij := decide_eq_decide.mp (congrArg Prod.snd (Sum.inr.inj h))
      have : i.val < 2 ∧ j.val < 2 := ⟨i.isLt, j.isLt⟩
      exact congrArg Sum.inr (Fin.ext (by omega))

private theorem source_row (u : U) (s : Edge C R → Bool) :
    (((gen (cell N A (.inl u)).generator).graph Prim.interp).Legal
      ((polarity N A (.inl u) + s) ∘ port N A (.inl u))) ↔
      (N.graph (.inl u)).Sat s := by
  rw [N.sat_row_iff]
  change ((Gadgets.OrTree.node _).graph Prim.interp).Legal _ ↔ _
  rw [Gadgets.OrTree.legal_generator_iff]
  have hi (i : Fin (Gadgets.OrTree.bundle (rowInputs N A u).length).length) :
      (polarity N A (.inl u) + s) (port N A (.inl u) (.inl i)) =
        s (.inl (input (rowInputs N A u) i)) := by
    have hc := (of_decide_eq_true (List.mem_filter.mp (input_mem (rowInputs N A u) i)).2).2
    dsimp only [input] at hc ⊢
    simp only [List.get_eq_getElem, Fin.val_cast] at hc
    simp [port, polarity, hc, Pi.add_apply, Bool.add_eq_xor]
  have ho : (polarity N A (.inl u) + s) (port N A (.inl u) (.inr 0)) =
      !(s (.inl (A.character u))) := by simp [port, polarity, Pi.add_apply, Bool.add_eq_xor]
  simp only [Function.comp_apply, hi, ho, Bool.not_eq_false']
  constructor
  · rintro (⟨i, hi⟩ | ho)
    · exact ⟨_, (of_decide_eq_true
        (List.mem_filter.mp (input_mem (rowInputs N A u) i)).2).1, hi⟩
    · exact ⟨_, A.row_character u, ho⟩
  · rintro ⟨c, hc, hs⟩
    by_cases ha : c = A.character u
    · exact Or.inr (ha ▸ hs)
    · obtain ⟨i, rfl⟩ := exists_input (rowInputs N A u)
        (List.mem_filter.mpr ⟨N.characters_complete c, decide_eq_true ⟨hc, ha⟩⟩)
      exact Or.inl ⟨i, hs⟩

private theorem source_character (c : C) (s : Edge C R → Bool) :
    (((gen (cell N A (.inr (.inl c))).generator).graph Prim.interp).Legal
      ((polarity N A (.inr (.inl c)) + s) ∘ port N A (.inr (.inl c)))) ↔
      (N.graph (.inr (.inl c))).Sat s := by
  rw [N.sat_character_iff]
  change (((gen (Gadgets.AndTree.generator _)).graph Prim.interp).Legal _) ↔ _
  rw [Gadgets.AndTree.legal_generator_iff]
  simp only [polarity, Pi.add_apply, Bool.add_eq_xor, Bool.false_xor,
    Function.comp_apply, port]
  constructor
  · rintro (h | h) hc e he
    · obtain ⟨i, rfl⟩ := exists_input (N.incident c) he
      exact h i
    · exact Bool.noConfusion (hc.symm.trans h)
  · intro h
    cases hc : s (.inl c) with
    | false => exact Or.inr rfl
    | true => exact Or.inl (fun i => h hc _ (input_mem _ i))

private theorem source_relation (r : R) (s : Edge C R → Bool) :
    (((gen (cell N A (.inr (.inr r))).generator).graph Prim.interp).Legal
      ((polarity N A (.inr (.inr r)) + s) ∘ port N A (.inr (.inr r)))) ↔
      (N.graph (.inr (.inr r))).Sat s := by
  rw [N.sat_relation_iff, ← genLegal_iff]
  dsimp only [cell, Cell.generator]
  cases hreq : N.required r with
  | false => simp [GenLegal, Prim.interp, Vertex.Sat, genVertex]
  | true =>
    simp only [Gadgets.Wire.generator, GenLegal, Prim.interp, List.mem_singleton, forall_eq,
      true_implies, polarity, Pi.add_apply, Bool.add_eq_xor, Bool.false_xor, Function.comp_def]
    change (2 ≤ (if s (.inr (r, false)) = false then 2 else 0) +
      ((if s (.inr (r, true)) = false then 2 else 0) + 0)) ↔ _
    cases s (.inr (r, false)) <;> cases s (.inr (r, true)) <;> decide

private theorem source_iff (v : Vert U C R) (s : Edge C R → Bool) :
    (((gen (cell N A v).generator).graph Prim.interp).Legal
      ((polarity N A v + s) ∘ port N A v)) ↔ (N.graph v).Sat s := by
  rcases v with u | (c | r)
  · exact source_row N A u s
  · exact source_character N A c s
  · exact source_relation N A r s

/-- Private implementation wires, tagged by their source vertex. This dependent sum is the
private-edge type of `ConstraintGraph.Replacement.graph`. -/
abbrev Private := (v : Vert U C R) × Diagram.Replacement.Inner (cell N A v).openSim

instance instDecidableEqPrivate : DecidableEq (Private N A) :=
  inferInstanceAs (DecidableEq ((v : Vert U C R) × Diagram.Replacement.Inner (cell N A v).openSim))

/-- Standard vertices, tagged by their source vertex. The dependent sum matches the vertex type
of `ConstraintGraph.Replacement.graph`. -/
abbrev TargetVertex := (v : Vert U C R) × (cell N A v).diagram.Vtx Prim.interp

/-- A local implementation with the row's chosen reference direction. -/
@[expose] def localGraph (v : Vert U C R) :
    ConstraintGraph ((cell N A v).diagram.Vtx Prim.interp)
      (Edge C R ⊕ Diagram.Replacement.Inner (cell N A v).openSim) :=
  (Diagram.Replacement.graph (cell N A v).openSim (port N A v)).reorient
    (Sum.elim (polarity N A v) (fun _ => false))

/-- The actual AND/OR graph obtained by joining all local implementations on shared edges. -/
@[expose] def graph : ConstraintGraph (TargetVertex N A) (Edge C R ⊕ Private N A) :=
  ConstraintGraph.Replacement.graph (localGraph N A)

private def localRealizes (v : Vert U C R) :
    Realizes (ConstraintGraph.Replacement.component (localGraph N A v)) (N.graph v) := by
  let mask := polarity N A v
  have hm (s : Edge C R → Bool) : mask + (mask + s) = s := by
    funext e
    simp [Pi.add_apply, Bool.add_eq_xor]
  let S := (cell N A v).openSim
  let H := Diagram.Replacement.graph S (port N A v)
  let base := Diagram.Replacement.realizesOfLegalIff S (port N A v) (port_injective N A v)
    ((N.graph v).reorient mask) (fun s => by
      rw [Vertex.sat_reorient]
      simpa only [show polarity N A v = mask from rfl, hm] using source_iff N A v (mask + s))
  let impl := ConstraintGraph.Replacement.realizesReorient H base mask
  have hsat (s : Edge C R → Bool) :
      (((N.graph v).reorient mask).reorient mask).Sat s ↔ (N.graph v).Sat s := by
    rw [Vertex.sat_reorient, Vertex.sat_reorient, hm]
  exact
    { canon := impl.canon
      sound := fun hs => (hsat _).mp (impl.sound hs)
      legal_canon := fun hs => impl.legal_canon ((hsat _).mpr hs)
      move := fun e hs ht => impl.move e ((hsat _).mpr hs) ((hsat _).mpr ht) }

/-- The complete standard graph preserves and reflects the weighted network's dynamics. -/
def simulation [Fintype U] [Fintype C] [Fintype R] :
    ConstraintGraph.Simulation N.graph (graph N A) :=
  ConstraintGraph.Replacement.simulation (localGraph N A) N.graph (localRealizes N A)

/-- Original selector and relation bits are read on the corresponding shared edges. -/
theorem simulation_abs [Fintype U] [Fintype C] [Fintype R]
    (s : Edge C R ⊕ Private N A → Bool) (e : Edge C R) :
    (simulation N A).abs s e = s (.inl e) :=
  ConstraintGraph.Replacement.simulation_abs _ _ _ s e

/-- Shared wire directions of a canonical implementation are the original directions. -/
theorem simulation_enc_shared [Fintype U] [Fintype C] [Fintype R]
    (s : Edge C R → Bool) (e : Edge C R) :
    (simulation N A).enc s (.inl e) = s e := by
  simpa only [simulation_abs] using congrFun ((simulation N A).abs_enc s) e

/-- Private canonical directions are exactly the local open simulation's canonical directions. -/
theorem simulation_enc_private [Fintype U] [Fintype C] [Fintype R]
    (s : Edge C R → Bool) (v : Vert U C R)
    (e : Diagram.Replacement.Inner (cell N A v).openSim) :
    (simulation N A).enc s (.inr ⟨v, e⟩) =
      (cell N A v).openSim.enc ((polarity N A v + s) ∘ port N A v) e.val := by
  rw [simulation, ConstraintGraph.Replacement.simulation_enc_private]
  simp only [localRealizes, ConstraintGraph.Replacement.realizesReorient, Realizes.reorient,
    Diagram.Replacement.realizesOfLegalIff_canon]

/-- Every vertex of the joined graph is a standard AND or OR vertex. -/
theorem isAndOr : (graph N A).IsAndOr :=
  ConstraintGraph.Replacement.isAndOr _ fun v =>
    ConstraintGraph.IsAndOr.reorient _ _ fun w =>
      (isAndOr_of_checkGens Prim.interp _
        ((checkGens_checkStandard_iff _).mp (cell N A v).checkStandard).1 w).map _

/-- Local port injectivity and fresh private wires give a graph without self-loops. -/
theorem loopFree : (graph N A).LoopFree := by
  classical
  exact ConstraintGraph.Replacement.loopFree _ fun v =>
    ConstraintGraph.LoopFree.reorient _ _ <|
      (loopFree_of_checkGens Prim.interp _
        ((checkGens_checkStandard_iff _).mp (cell N A v).checkStandard).2.1).map
        (Diagram.Replacement.label_injective _ (port_injective N A v))

private abbrev Boundary (v : Vert U C R) :=
  Fin (cell N A v).top.length ⊕ Fin (cell N A v).bottom.length

private def direction (v : Vert U C R) (x : Boundary N A v) : Bool :=
  polarity N A v (port N A v x) ^^ Sum.elim (fun _ => true) (fun _ => false) x

private def boundaryEnd (x : (v : Vert U C R) × Boundary N A v) : Edge C R × Bool :=
  (port N A x.1 x.2, direction N A x.1 x.2)

private theorem endpoint_boundary (v : Vert U C R) (x : Boundary N A v) :
    N.endpoints.endpoint (port N A v x) (direction N A v x) = v := by
  rcases v with u | (c | r)
  · rcases x with i | i
    · have hc := of_decide_eq_true (List.mem_filter.mp (input_mem (rowInputs N A u) i)).2
      dsimp only [input] at hc
      simp only [List.get_eq_getElem, Fin.val_cast] at hc
      simp [port, direction, polarity, hc.2, endpoints, hc.1]
    · simp [port, direction, polarity, endpoints, A.row_character]
  · rcases x with i | i
    · have hc := of_decide_eq_true (List.mem_filter.mp (input_mem (N.incident c) i)).2
      dsimp only [input] at hc
      simp only [List.get_eq_getElem, Fin.val_cast] at hc
      simpa [port, direction, polarity, endpoints] using hc
    · rfl
  · rcases x with i | i
    · exact i.elim0
    · rfl

private theorem boundaryEnd_injective : Function.Injective (boundaryEnd N A) := by
  rintro ⟨v, x⟩ ⟨w, y⟩ h
  obtain rfl : v = w := (endpoint_boundary N A v x).symm.trans
    ((congrArg (fun z => N.endpoints.endpoint z.1 z.2) h).trans (endpoint_boundary N A w y))
  exact congrArg (Sigma.mk v) (port_injective N A v (congrArg Prod.fst h))

private theorem boundaryEnd_surjective : Function.Surjective (boundaryEnd N A) := by
  rintro ⟨e, b⟩
  rcases e with c | ⟨r, d⟩
  · cases b
    · exact ⟨⟨.inr (.inl c), .inr 0⟩, rfl⟩
    · by_cases hc : c = A.character (N.row c)
      · exact ⟨⟨.inl (N.row c), .inr 0⟩, by simp [boundaryEnd, port, direction, polarity, ← hc]⟩
      · obtain ⟨i, hi⟩ := exists_input (rowInputs N A (N.row c))
          (List.mem_filter.mpr ⟨N.characters_complete c, decide_eq_true ⟨rfl, hc⟩⟩)
        refine ⟨⟨.inl (N.row c), .inl i⟩, ?_⟩
        change (Sum.inl (input (rowInputs N A (N.row c)) i),
          decide ((Sum.inl (input (rowInputs N A (N.row c)) i) : Edge C R) =
            .inl (A.character (N.row c))) ^^ true) = (.inl c, true)
        simp [hi, hc]
  · cases b
    · cases d
      exacts [⟨⟨.inr (.inr r), .inr 0⟩, rfl⟩, ⟨⟨.inr (.inr r), .inr 1⟩, rfl⟩]
    · obtain ⟨i, hi⟩ := exists_input (N.incident (N.endpoint r d))
        (by simp [incident, branches, N.relations_complete r] : (r, d) ∈ _)
      exact ⟨⟨.inr (.inl (N.endpoint r d)), .inl i⟩, Prod.ext (congrArg Sum.inr hi) rfl⟩

open scoped BigOperators

private theorem local_portMultiset (v : Vert U C R) :
    (localGraph N A v).portMultiset =
      (∑ x : Boundary N A v, {⟨⟨Sum.inl (port N A v x), direction N A v x⟩, 2⟩}) +
      ∑ e : Diagram.Replacement.Inner (cell N A v).openSim,
        ({⟨⟨Sum.inr e, false⟩, (cell N A v).diagram.edgeWeight e⟩} +
          {⟨⟨Sum.inr e, true⟩, (cell N A v).diagram.edgeWeight e⟩}) := by
  have ht (i : Fin (cell N A v).top.length) : ((cell N A v).top.get i).weight = 2 := by
    match v with
    | .inl _ | .inr (.inl _) => simp [Cell.top, List.get_eq_getElem, Color.weight]
    | .inr (.inr _) => exact i.elim0
  have hb (i : Fin (cell N A v).bottom.length) : ((cell N A v).bottom.get i).weight = 2 := by
    match v with
    | .inl _ | .inr (.inl _) =>
      exact congrArg Color.weight (List.mem_singleton.mp (List.get_mem _ i))
    | .inr (.inr r) =>
      have hi := List.get_mem (cell N A (.inr (.inr r))).bottom i
      simp only [Cell.bottom, List.mem_cons, List.not_mem_nil, or_false, or_self] at hi
      exact congrArg Color.weight hi
  rw [localGraph, ConstraintGraph.portMultiset_reorient,
    Diagram.Replacement.portMultiset_boundary _ _ (cell N A v).checkPorts]
  simp only [ports_genVertex, ← Multiset.coe_mapAddMonoidHom, map_add, map_sum,
    Fintype.sum_sum_type]
  simp only [Multiset.coe_mapAddMonoidHom, Multiset.map_singleton, ht, hb, WeightedPort.map,
    WeightedPort.reorient, Port.map, Port.reorient, Sum.elim_inl, Sum.elim_inr, Bool.false_xor,
    direction]

/-- A shared local port retains the original edge's endpoint and reference direction. -/
private theorem local_shared_endpoint (v : Vert U C R) (w : (cell N A v).diagram.Vtx Prim.interp)
    (p : WeightedPort (Edge C R ⊕ Diagram.Replacement.Inner (cell N A v).openSim))
    (hp : p ∈ (localGraph N A v w).ports) (e : Edge C R) (he : p.port.edge = .inl e) :
    N.endpoints.endpoint e p.port.dir = v := by
  have hm : p ∈ (localGraph N A v).portMultiset :=
    Multiset.mem_sum.mpr ⟨w, Finset.mem_univ _, Multiset.mem_coe.mpr hp⟩
  rw [local_portMultiset] at hm
  rcases Multiset.mem_add.mp hm with hm | hm
  · obtain ⟨x, _, hx⟩ := Multiset.mem_sum.mp hm
    rw [Multiset.mem_singleton.mp hx] at he ⊢
    exact Sum.inl.inj he ▸ endpoint_boundary N A v x
  · obtain ⟨x, _, hx⟩ := Multiset.mem_sum.mp hm
    rcases Multiset.mem_add.mp hx with hx | hx <;> simp [Multiset.mem_singleton.mp hx] at he

/-- The original source cell containing an implementation port of the indicated direction. -/
@[expose] def cellEndpoint : Edge C R ⊕ Private N A → Bool → Vert U C R
  | .inl e, d => N.endpoints.endpoint e d
  | .inr e, _ => e.1

/-- Every port's component origin agrees with the original endpoint or private-wire owner. -/
theorem cellEndpoint_of_mem (v : TargetVertex N A) (p : WeightedPort (Edge C R ⊕ Private N A))
    (hp : p ∈ (graph N A v).ports) : cellEndpoint N A p.port.edge p.port.dir = v.1 := by
  rcases v with ⟨v, w⟩
  change p ∈ ((localGraph N A v w).ports.map
    (WeightedPort.map (Sum.map id (Sigma.mk v)))) at hp
  obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hp
  rcases he : p.port.edge with e | e
  · simpa only [WeightedPort.map, Port.map, he, Sum.map_inl, id_eq, cellEndpoint] using
      local_shared_endpoint N A v w p hp' e he
  · simp only [WeightedPort.map, Port.map, he, Sum.map_inr, cellEndpoint]

/-- The joined standard graph has exactly two opposite, equally weighted ports per edge. -/
theorem wellFormed [Fintype U] [Fintype C] [Fintype R] : (graph N A).WellFormed := by
  let eqv : ((v : Vert U C R) × Boundary N A v) ≃ Edge C R × Bool :=
    Equiv.ofBijective (boundaryEnd N A) ⟨boundaryEnd_injective N A, boundaryEnd_surjective N A⟩
  have hboundary : (∑ v, ∑ x : Boundary N A v,
      ({⟨⟨Sum.inl (port N A v x), direction N A v x⟩, 2⟩} :
        Multiset (WeightedPort (Edge C R ⊕ Private N A)))) =
      ∑ e : Edge C R, ({⟨⟨Sum.inl e, false⟩, 2⟩} + {⟨⟨Sum.inl e, true⟩, 2⟩}) := by
    have h := Fintype.sum_equiv eqv
      (fun x => ({⟨⟨Sum.inl (port N A x.1 x.2), direction N A x.1 x.2⟩, 2⟩} :
        Multiset (WeightedPort (Edge C R ⊕ Private N A))))
      (fun x => {⟨⟨Sum.inl x.1, x.2⟩, 2⟩}) (fun _ => rfl)
    simpa only [Fintype.sum_sigma, Fintype.sum_prod_type, Fintype.sum_bool, add_comm] using h
  have hlocal (v : Vert U C R) :
      Multiset.map (WeightedPort.map (Sum.map id (Sigma.mk v))) (localGraph N A v).portMultiset =
      (∑ x : Boundary N A v, {⟨⟨Sum.inl (port N A v x), direction N A v x⟩, 2⟩}) +
      ∑ e : Diagram.Replacement.Inner (cell N A v).openSim,
        ({⟨⟨Sum.inr (⟨v, e⟩ : Private N A), false⟩, (cell N A v).diagram.edgeWeight e⟩} +
          {⟨⟨Sum.inr (⟨v, e⟩ : Private N A), true⟩, (cell N A v).diagram.edgeWeight e⟩}) := by
    rw [local_portMultiset, ← Multiset.coe_mapAddMonoidHom, map_add, map_sum, map_sum]
    simp [WeightedPort.map, Port.map, Sum.map]
  refine ⟨Sum.elim (fun _ => 2) (fun e => (cell N A e.1).diagram.edgeWeight e.2), ?_⟩
  rw [graph, ConstraintGraph.Replacement.portMultiset_graph]
  simp_rw [hlocal]
  rw [Finset.sum_add_distrib, hboundary]
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma, Sum.elim_inl, Sum.elim_inr]

end AndOr
end Cslib.Complexity.NCL.SelectorNetwork
