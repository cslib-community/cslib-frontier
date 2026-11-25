/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SAT.Planar.PairedCompile
public import CslibFrontier.Computability.Complexity.Problems.SAT.Planar.PathGeometry
public import CslibFrontier.Computability.Complexity.Problems.Graph.OrthogonalDrawing
public import CslibFrontier.Computability.Complexity.Problems.SAT.Planar.Paths.Occupancy
public import CslibFrontier.Foundations.Geometry.Orthogonal.PairedBoundary
import CslibFrontier.Computability.Complexity.Problems.SAT.Incidence.Compact
import CslibFrontier.Foundations.Data.List.GetD
import CslibFrontier.Foundations.Data.List.Range
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.Forall2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Geometry of the paired-port compiler

The compiler reuses the canonical unit paths. Paired accesses have disjoint supports,
and their only boundary contacts identify the same lane of the same unit grid edge.
All geometric assertions concern entire real supports.

## Main results

* `access_eq_translate`: every actual access uses the common fixed paired-port interface.
* `route_contacts`, `routes_contacts`: continuous endpoint-only contacts of the actual routes.
* `isPlanarOrthogonalDrawing`: the actual compact formula's continuous drawing certificate.

## References

The paired macrocell assembly is original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ParsimoniousPlanar

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

/-! ### Local cell-geometry and tile helpers -/

private theorem cell_eq_of_open {c d : Point} {p : ℝ × ℝ}
    (hc : p ∈ openCell 120 c) (hd : p ∈ openCell 120 d) : c = d :=
  cell_eq_of_mem_open_closed (by decide) hc ⟨hd.1.le, hd.2.1.le, hd.2.2.1.le, hd.2.2.2.le⟩

private theorem not_mem_openCell_of_ne {c d : Point} (hcd : c ≠ d) {p : ℝ × ℝ}
    (hd : p ∈ closedCell 120 d) : p ∉ openCell 120 c :=
  fun ho => hcd (cell_eq_of_mem_open_closed (by decide) ho hd)

private theorem mem_support_translate_sub {v : Point} {r : Route} {p : ℝ × ℝ}
    (hp : p ∈ support (translate v r)) : p - realPoint v ∈ support r :=
  (mem_support_translate_iff v r _).1 (by simpa only [sub_add_cancel] using hp)

private theorem realPoint_mem_support_of_head? {r : Route} {p : Point} (h : r.head? = some p) :
    realPoint p ∈ support r :=
  Or.inl ⟨p, List.mem_of_mem_head? h, rfl⟩

private theorem add_origin_mem_openCell (c p : Point)
    (h : 0 < p.1 ∧ p.1 < 240 ∧ 0 < p.2 ∧ p.2 < 240) :
    realPoint (cellOrigin 120 c + p) ∈ openCell 120 c := by
  rw [realPoint_add, add_comm, mem_openCell_add_origin_iff]
  norm_num [realPoint]
  exact_mod_cast h

/-- A translated local route whose boundary contacts isolate a single port `b` stays inside
its closed macrocell and meets the outer boundary only at `cellOrigin 120 c + b`. -/
private theorem translate_support_cell_isolation {r : Route} {b c : Point} {p : ℝ × ℝ}
    (hiso : ∀ {x : ℝ × ℝ}, x ∈ support r →
      0 ≤ x.1 ∧ x.1 ≤ 240 ∧ 0 ≤ x.2 ∧ x.2 ≤ 240 ∧
        (x.1 = 0 ∨ x.1 = 240 ∨ x.2 = 0 ∨ x.2 = 240 → x = realPoint b))
    (hp : p ∈ support (translate (cellOrigin 120 c) r)) :
    p ∈ closedCell 120 c ∧
      (p ∉ openCell 120 c → p = realPoint (cellOrigin 120 c + b)) := by
  let x := p - realPoint (cellOrigin 120 c)
  have hx : x + realPoint (cellOrigin 120 c) = p := sub_add_cancel _ _
  obtain ⟨h₀, h₁, h₂, h₃, hb⟩ := hiso (mem_support_translate_sub hp)
  refine ⟨by rw [← hx, mem_closedCell_add_origin_iff]; exact ⟨h₀, h₁, h₂, h₃⟩, fun hnot => ?_⟩
  have hedge : x.1 = 0 ∨ x.1 = 240 ∨ x.2 = 0 ∨ x.2 = 240 := by
    by_contra h; apply hnot; rw [← hx, mem_openCell_add_origin_iff]; push Not at h
    exact ⟨lt_of_le_of_ne h₀ h.1.symm, lt_of_le_of_ne h₁ h.2.1,
      lt_of_le_of_ne h₂ h.2.2.1.symm, lt_of_le_of_ne h₃ h.2.2.2⟩
  rw [← hx, show x = realPoint b from hb hedge, realPoint_add, add_comm]

/-- Common data interface for the two fixed macrocell gadgets (`OrdinaryRing` and
`PairedCrossover`), whose placed clauses are definitionally `t.clauses p`. -/
private structure TileSpec (V : Type) where
  formula : CNF V
  clausePos : List Point
  inc : List (ℕ × V × Route)
  tag : V → (Fin 4 × Fin 2) ⊕ PairedCrossover.Variable
  varPos : V → Point

private abbrev TileSpec.clauses {V : Type} (t : TileSpec V) (p : Point) : List PlacedClause :=
  t.formula.zipIdx.map fun (c, i) =>
    (c.relabel (fun v => (p, t.tag v)),
      cellOrigin 120 p + t.clausePos.getD i (0, 0),
      (t.inc.filter fun e => e.1 == i).map fun e => translate (cellOrigin 120 p) e.2.2)

private abbrev ordTile : TileSpec OrdinaryRing.Variable where
  formula := OrdinaryRing.formula
  clausePos := OrdinaryRing.clausePositions
  inc := OrdinaryRing.incidenceRoutes
  tag := Sum.inl
  varPos := OrdinaryRing.variablePosition

private abbrev crossTile : TileSpec PairedCrossover.Variable where
  formula := PairedCrossover.formula
  clausePos := PairedCrossover.clausePositions
  inc := PairedCrossover.incidenceRoutes
  tag := Sum.inr
  varPos := PairedCrossover.variablePosition

private theorem TileSpec.route_regular {V : Type} {t : TileSpec V} {p : Point} {pc : PlacedClause}
    {r : Route} (horth : ∀ e ∈ t.inc, IsOrthogonal e.2.2)
    (hsimp : ∀ {e}, e ∈ t.inc → IsSimple e.2.2)
    (hpc : pc ∈ t.clauses p) (hr : r ∈ pc.2.2) : IsOrthogonal r ∧ IsSimple r := by
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hpc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
  have he' := (List.mem_filter.mp he).1
  exact ⟨(isOrthogonal_translate_iff _ _).2 (horth e he'),
    (isSimple_translate_iff _ _).2 (hsimp he')⟩

private theorem TileSpec.route_count {V : Type} {t : TileSpec V} {n : ℕ}
    (hlen : t.formula.length = n)
    (hvars : ∀ i : Fin n,
      (t.inc.filter fun e => e.1 == i.val).map (·.2.1) = (t.formula.getD i.val []).map Prod.fst)
    {p : Point} {pc : PlacedClause} (hpc : pc ∈ t.clauses p) :
    pc.2.2.length = pc.1.length := by
  obtain ⟨⟨c, i⟩, hci, rfl⟩ := List.mem_map.mp hpc
  have hi : i < t.formula.length := by simpa only [Nat.zero_add] using (List.mem_zipIdx hci).2.1
  have hc : c = t.formula[i] := by simpa only [Nat.sub_zero] using (List.mem_zipIdx hci).2.2
  have hcount := congrArg List.length (hvars ⟨i, hlen ▸ hi⟩)
  rw [List.getD_eq_getElem t.formula [] hi, ← hc, List.length_map, List.length_map] at hcount
  simpa only [List.length_map, Clause.length_relabel] using hcount

private theorem TileSpec.clause_endpoints {V : Type} {t : TileSpec V} {n : ℕ}
    (hlen : t.formula.length = n)
    (htag : ∀ c v, variablePosition (c, t.tag v) = cellOrigin 120 c + t.varPos v)
    (hvars : ∀ i : Fin n,
      (t.inc.filter fun e => e.1 == i.val).map (·.2.1) = (t.formula.getD i.val []).map Prod.fst)
    (hend : ∀ e ∈ t.inc,
      e.2.2.head? = some (t.clausePos.getD e.1 (0, 0)) ∧ e.2.2.getLast? = some (t.varPos e.2.1))
    {c : Point} {pc : PlacedClause} (hpc : pc ∈ t.clauses c)
    {l : Literal Variable} {r : Route} (hlr : (l, r) ∈ pc.1.zip pc.2.2) :
    r.head? = some pc.2.1 ∧ r.getLast? = some (variablePosition l.1) := by
  obtain ⟨⟨src, i⟩, hci, rfl⟩ := List.mem_map.mp hpc
  dsimp only at hlr ⊢
  have hi : i < t.formula.length := by simpa only [Nat.zero_add] using (List.mem_zipIdx hci).2.1
  have hsrc : src = t.formula.getD i [] :=
    (show src = t.formula[i] by simpa only [Nat.sub_zero] using (List.mem_zipIdx hci).2.2).trans
      (List.getD_eq_getElem _ _ hi).symm
  change (l, r) ∈ (src.map (Prod.map (fun v => (c, t.tag v)) id)).zip
    ((t.inc.filter fun e => e.1 == i).map fun e => translate (cellOrigin 120 c) e.2.2) at hlr
  rw [show ((t.inc.filter fun e => e.1 == i).map fun e => translate (cellOrigin 120 c) e.2.2) =
      ((t.inc.filter fun e => e.1 == i).map (·.2.2)).map (translate (cellOrigin 120 c)) by
    rw [List.map_map]; rfl, List.zip_map] at hlr
  obtain ⟨⟨ol, _⟩, hold, rfl, rfl⟩ := List.mem_map.mp hlr
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hold
  rw [List.length_zip, List.length_map] at hk
  have hk1 : k < src.length := lt_of_lt_of_le hk (Nat.min_le_left _ _)
  have hk2 : k < (t.inc.filter fun e => e.1 == i).length := lt_of_lt_of_le hk (Nat.min_le_right _ _)
  obtain ⟨rfl, rfl⟩ : src[k] = ol ∧ (t.inc.filter fun e => e.1 == i)[k].2.2 = _ := by
    simpa only [List.getElem_zip, List.getElem_map, Prod.mk.injEq] using hget
  have he_mem := List.mem_filter.mp (List.getElem_mem hk2)
  have he_var : (t.inc.filter fun e => e.1 == i)[k].2.1 = src[k].1 := by
    have hv := congrArg (·[k]?) (hvars ⟨i, hlen ▸ hi⟩)
    rwa [← hsrc, List.getElem?_eq_getElem (by simpa using hk2),
      List.getElem?_eq_getElem (by simpa using hk1), List.getElem_map, List.getElem_map,
      Option.some.injEq] at hv
  obtain ⟨hhead, hlast⟩ := hend _ he_mem.1
  rw [beq_iff_eq.mp he_mem.2] at hhead; rw [he_var] at hlast
  exact ⟨by simp only [translate, List.head?_map, hhead, Option.map_some, add_comm],
    by simp only [translate, List.getLast?_map, hlast, Option.map_some, Prod.map_fst, htag,
      add_comm]⟩

private theorem TileSpec.clause_mem_openCell {V : Type} {t : TileSpec V}
    (hlen : t.formula.length = t.clausePos.length)
    (hbd : ∀ p ∈ t.clausePos, 20 ≤ p.1 ∧ p.1 ≤ 220 ∧ 20 ≤ p.2 ∧ p.2 ≤ 220)
    {c : Point} {pc : PlacedClause} (hpc : pc ∈ t.clauses c) :
    realPoint pc.2.1 ∈ openCell 120 c := by
  obtain ⟨⟨_, i⟩, hci, rfl⟩ := List.mem_map.mp hpc
  have hi : i < t.clausePos.length := hlen ▸ by simpa using (List.mem_zipIdx hci).2.1
  have hb := hbd _ (List.getD_mem (0, 0) hi)
  exact add_origin_mem_openCell c _ (by omega)

private theorem TileSpec.clause_positions {V : Type} (t : TileSpec V)
    (hlen : t.formula.length = t.clausePos.length) (c : Point) :
    (t.clauses c).map (·.2.1) = t.clausePos.map (cellOrigin 120 c + ·) := by
  refine List.ext_getElem (by simp [TileSpec.clauses, hlen]) fun i _ hj => ?_
  simp only [TileSpec.clauses, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hj)]

private theorem TileSpec.routes_nodup {V : Type} {t : TileSpec V} {n : ℕ}
    (hlen : t.formula.length = n)
    (hnd : ∀ i : Fin n, ((t.inc.filter fun e => e.1 == i.val).map (·.2.2)).Nodup)
    {c : Point} {pc : PlacedClause} (hpc : pc ∈ t.clauses c) : pc.2.2.Nodup := by
  obtain ⟨⟨_, i⟩, hci, rfl⟩ := List.mem_map.mp hpc
  have hi : i < n := hlen ▸ by simpa only [Nat.zero_add] using (List.mem_zipIdx hci).2.1
  simpa only [List.map_map, Function.comp_def] using (hnd ⟨i, hi⟩).map
    (f := translate (cellOrigin 120 c))
    (fun _ _ h => (List.map_inj_right (fun _ _ => add_right_cancel)).mp h)

private theorem TileSpec.route_length_ge_two {V : Type} {t : TileSpec V} {c : Point}
    {pc : PlacedClause} {r : Route} (hlen : ∀ e ∈ t.inc, 2 ≤ e.2.2.length)
    (hpc : pc ∈ t.clauses c) (hr : r ∈ pc.2.2) : 2 ≤ r.length := by
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hpc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
  simpa only [translate, List.length_map] using hlen e (List.mem_filter.mp he).1

private theorem TileSpec.mem_var {V : Type} {t : TileSpec V} {p : Point} {pc : PlacedClause}
    {v : Variable} {b : Bool} (hpc : pc ∈ t.clauses p) (hv : (v, b) ∈ pc.1) :
    ∃ x, v = (p, t.tag x) := by
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hpc
  obtain ⟨l, _, h⟩ := List.mem_map.mp hv
  exact ⟨l.1, (congrArg Prod.fst h).symm⟩

private theorem consecutivePairs_dropLast : ∀ r : Route,
    r.dropLast.consecutivePairs = r.consecutivePairs.dropLast
  | [] | [_] | [_, _] => rfl
  | a :: b :: c :: t => congrArg ((a, b) :: ·) (consecutivePairs_dropLast (b :: c :: t))

private theorem prefixStep_mem {φ : CNF ℕ} {o : Occurrence ℕ} {e : Point × Point}
    (he : e ∈ (occurrencePath φ o).dropLast.consecutivePairs) :
    e ∈ (occurrencePath φ o).consecutivePairs :=
  (List.dropLast_sublist _).subset (consecutivePairs_dropLast _ ▸ he)

/-! ### Boundary ports and paired accesses -/

/-- Within one cell, boundary positions identify both the side and the lane. -/
theorem boundary_injective (c : Point) :
    Function.Injective (fun p : PairedPorts.Port => boundary c p.1 p.2) :=
  fun _ _ h => PairedPorts.boundaryPort_injective (add_left_cancel h)

/-- Opposite facing sides of unit neighbors match in the same lane. -/
theorem shared_boundary {p q : Point} (h : Orthogonal.length p q = 1) (l : Fin 2) :
    boundary p (side p q) l = boundary q (side q p) l := by
  rcases p with ⟨x, y⟩
  rcases PlanarCompile.unit_neighbor_cases h with rfl | rfl | rfl | rfl <;>
    fin_cases l <;>
    ext <;> norm_num [boundary, side, PlanarCompile.side, cellOrigin, PairedPorts.boundaryPort,
      PairedPorts.offset] <;> omega

/-- Every actual access is proper and orthogonal. -/
theorem access_orthogonal (sites : List Point) (p q : Point) (l : Fin 2) :
    IsOrthogonal (access sites p q l) := by
  rw [access_eq_translate, isOrthogonal_translate_iff]
  exact (PairedPorts.access_endpoints _ _).1

/-- Every actual access is continuously simple. -/
theorem access_simple (sites : List Point) (p q : Point) (l : Fin 2) :
    IsSimple (access sites p q l) := by
  rw [access_eq_translate, isSimple_translate_iff]
  exact PairedPorts.access_isSimple _ _

/-- All actual access routes have the same fixed cost. -/
theorem access_cost (sites : List Point) (p q : Point) (l : Fin 2) :
    wireLength (access sites p q l) = 20 ∧ (access sites p q l).consecutivePairs.length = 1 := by
  rw [access_eq_translate, wireLength_translate]
  exact ⟨(PairedPorts.access_route_sizes _ _).2, rfl⟩

/-- Every actual access stays in its closed cell and touches its boundary only at its port. -/
theorem access_support_cell (sites : List Point) (c q : Point) (l : Fin 2) {p : ℝ × ℝ}
    (hp : p ∈ support (access sites c q l)) :
    p ∈ closedCell 120 c ∧
      (p ∉ openCell 120 c → p = realPoint (boundary c (side c q) l)) :=
  translate_support_cell_isolation PairedPorts.access_boundary_isolation
    (access_eq_translate sites c q l ▸ hp)

/-- Contacts between accesses in different cells occur at both designated boundary ports. -/
theorem access_contact_of_distinct_cells (sites otherSites : List Point)
    {c d : Point} (hcd : c ≠ d) (q t : Point) (l k : Fin 2) {p : ℝ × ℝ}
    (hp : p ∈ support (access sites c q l)) (hq : p ∈ support (access otherSites d t k)) :
    p = realPoint (boundary c (side c q) l) ∧ p = realPoint (boundary d (side d t) k) :=
  let hc := access_support_cell sites c q l hp
  let hd := access_support_cell otherSites d t k hq
  ⟨hc.2 (not_mem_openCell_of_ne hcd hd.1), hd.2 (not_mem_openCell_of_ne hcd.symm hc.1)⟩

/-- Distinct paired ports of one cell have disjoint continuous accesses. -/
theorem access_disjoint_same_cell (sites : List Point) (c q t : Point) (l k : Fin 2)
    (hne : (side c q, l) ≠ (side c t, k)) :
    Disjoint (support (access sites c q l)) (support (access sites c t k)) :=
  Set.disjoint_left.mpr fun _ hp hq =>
    Set.disjoint_left.mp (PairedPorts.access_disjoint hne)
      (mem_support_translate_sub (access_eq_translate sites c q l ▸ hp))
      (mem_support_translate_sub (access_eq_translate sites c t k ▸ hq))

/-- Equality of paired seam points identifies the lane and the old single seam midpoint. -/
theorem boundary_step_midpoint_eq {p q a b : Point} {l k : Fin 2}
    (hpq : Orthogonal.length p q = 1) (hab : Orthogonal.length a b = 1)
    (h : boundary p (side p q) l = boundary a (side a b) k) :
    l = k ∧ cellPort 120 p (side p q) = cellPort 120 a (side a b) := by
  by_cases hpa : p = a
  · subst hpa
    obtain ⟨hs, hl⟩ := Prod.mk.inj
      (boundary_injective p (a₁ := (side p q, l)) (a₂ := (side p b, k)) h)
    exact ⟨hl, congrArg (cellPort 120 p) hs⟩
  · obtain ⟨rfl, rfl, ht⟩ := PairedPorts.boundary_eq_cases hpa h
    rcases p with ⟨px, py⟩
    rw [ht]; generalize side (px, py) q = s; refine ⟨rfl, ?_⟩
    fin_cases s <;> (ext <;>
      dsimp [cellPort, cellOrigin, PairedPorts.neighbor, PairedPorts.oppositeSide, Prod.mk_add_mk]
      <;> omega)

/-- All actual unit steps are proper; this includes final steps into clause cells. -/
theorem path_step_unit {φ : CNF ℕ} {e : Point × Point}
    (he : e ∈ (paths φ).flatMap List.consecutivePairs) : Orthogonal.length e.1 e.2 = 1 := by
  obtain ⟨r, hr, he⟩ := List.mem_flatMap.mp he
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  have hi' : i < (SAT.incidenceGraph φ).2.length := by
    simpa only [PlanarCompile.paths_eq_unitPaths, Graph.unitPaths_length] using hi
  apply Graph.unitPath_unit _ (fun _ => SAT.incidenceGraph_endpoints)
    (fun _ => SAT.incidenceGraph_loopless) hi'
  change e ∈ ((paths φ).getD i []).consecutivePairs
  rwa [List.getD_eq_getElem _ _ hi]

/-- Paired seam points of every actual path step are all distinct, including final steps. -/
theorem pathBoundaries_nodup {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    ((paths φ).flatMap fun r => r.consecutivePairs.flatMap fun e =>
      [boundary e.1 (side e.1 e.2) 0, boundary e.1 (side e.1 e.2) 1]).Nodup := by
  let steps := (paths φ).flatMap List.consecutivePairs
  have hn : (steps.map fun e => cellPort 120 e.1 (side e.1 e.2)).Nodup := by
    simpa only [steps, List.map_flatMap] using PlanarCompile.pathMidpoints_nodup hw hv
  have hsub : (steps.flatMap fun e =>
      [boundary e.1 (side e.1 e.2) 0, boundary e.1 (side e.1 e.2) 1]).Nodup := by
    refine List.nodup_flatMap.mpr ⟨fun e _ => ?_, ?_⟩
    · simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, List.nodup_nil,
        not_false_eq_true, and_true]
      exact fun h => Fin.zero_ne_one
        (congrArg Prod.snd (boundary_injective e.1 (a₁ := (_, 0)) (a₂ := (_, 1)) h))
    · apply (List.pairwise_map.mp hn).imp_of_mem; intro e f he hf hmid x hx hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with hy | hy <;>
        exact hmid (boundary_step_midpoint_eq (path_step_unit he) (path_step_unit hf) hy).2
  simpa only [steps, List.flatMap_assoc] using hsub

/-- Every original clause cell is disjoint from all ordinary tiles. -/
theorem clause_cell_not_ordinary {φ : CNF ℕ} {i : ℕ} (hi : i < φ.length) :
    Layout.center (φ.distinctVars.length + i) ∉ ordinaryCells φ := by
  intro hp
  obtain ⟨⟨r, hr, hp⟩, -⟩ := (mem_ordinaryCells φ _).1 hp
  rw [show paths φ = _ from (PlanarCompile.occurrencePaths_eq_paths φ).symm] at hr
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hr
  exact PlanarCompile.clause_cell_not_mem_path_dropLast ho hi hp

private theorem finalLocalRoute_orthogonal : ∀ s, IsOrthogonal (finalLocalRoute s) := by
  decide +kernel

private theorem finalLocalRoute_nodup : ∀ s, (finalLocalRoute s).Nodup := by decide +kernel

private theorem finalLocalRoute_simple_check : ∀ s, ∀ a ∈ (finalLocalRoute s).consecutivePairs,
    ∀ b ∈ (finalLocalRoute s).consecutivePairs, a ≠ b →
      segmentContactCheck (consecutiveContact a b) a.1 a.2 b.1 b.2 = true := by decide +kernel

/-- Every actual final literal route is proper, orthogonal and continuously simple. -/
theorem lastLiteral_route_regular (sites : List Point) (r : Route) (b : Bool)
    (h : Orthogonal.length (r.getD (r.length - 2) (0, 0)) (r.getLastD (0, 0)) = 1) :
    IsOrthogonal (lastLiteral sites r b).2 ∧ IsSimple (lastLiteral sites r b).2 := by
  dsimp only [lastLiteral]
  rw [finalRoute_eq_translate sites h, isOrthogonal_translate_iff, isSimple_translate_iff]
  exact ⟨finalLocalRoute_orthogonal _,
    isSimple_of_segmentContactCheck (finalLocalRoute_nodup _) (finalLocalRoute_simple_check _)⟩

/-- The final incidence starts at its clause center and ends at its actual signal variable. -/
theorem lastLiteral_endpoints (sites : List Point) (r : Route) (b : Bool) :
    (lastLiteral sites r b).2.head? = some (center (r.getLastD (0, 0))) ∧
      (lastLiteral sites r b).2.getLast? = some (variablePosition (lastLiteral sites r b).1.1) :=
  ⟨rfl, rfl⟩

/-- Every route in a placed seam clause is an actual paired access. -/
theorem link_routes_cases (sites : List Point) (p q : Point) (l : Fin 2) {r : Route}
    (hr : r ∈ (link sites p q l).2.2) : r = access sites p q l ∨ r = access sites q p l := by
  by_cases hl : l = 0
  · simpa only [link, hl, ite_true, List.mem_cons, List.not_mem_nil, or_false] using hr
  · simpa only [link, hl, ite_false, List.mem_cons, List.not_mem_nil, or_false, false_or,
      or_comm] using hr

/-- Every route in a seam clause is proper, orthogonal and continuously simple. -/
theorem link_routes_regular (sites : List Point) (p q : Point) (l : Fin 2) {r : Route}
    (hr : r ∈ (link sites p q l).2.2) : IsOrthogonal r ∧ IsSimple r := by
  rcases link_routes_cases sites p q l hr with rfl | rfl <;>
    exact ⟨access_orthogonal _ _ _ _, access_simple _ _ _ _⟩

/-- Seam incidence routes match their literal variables in both lane orientations. -/
theorem link_endpoints (sites : List Point) {p q : Point} (h : Orthogonal.length p q = 1)
    (lane : Fin 2) {l : Literal Variable} {r : Route}
    (hlr : (l, r) ∈ (link sites p q lane).1.zip (link sites p q lane).2.2) :
    r.head? = some (link sites p q lane).2.1 ∧
      r.getLast? = some (variablePosition l.1) := by
  fin_cases lane <;>
    simp only [link, Fin.zero_eta, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte,
      List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hlr <;>
    (rcases hlr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      first | exact ⟨rfl, rfl⟩ | exact ⟨congrArg some (shared_boundary h _).symm, rfl⟩)

/-- Every seam literal uses one of its two actual presented signals. -/
theorem link_literal_cases (sites : List Point) (p q : Point) (lane : Fin 2)
    {lit : Literal Variable} (h : lit ∈ (link sites p q lane).1) :
    lit.1 = signal sites p q lane ∨ lit.1 = signal sites q p lane := by
  fin_cases lane <;>
    simp only [link, Fin.zero_eta, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte,
      List.mem_cons, List.not_mem_nil, or_false] at h <;>
    rcases h with rfl | rfl <;> simp

/-! ### Variable positions and formula indexing -/

/-- Every structured variable lies strictly inside its indexed macrocell. -/
theorem variablePosition_mem_openCell (v : Variable) :
    realPoint (variablePosition v) ∈ openCell 120 v.1 := by
  rcases v with ⟨p, v | v⟩
  · have hb := PairedPorts.variable_bounds v.1 v.2
    exact add_origin_mem_openCell p (PairedPorts.variablePosition v.1 v.2) (by omega)
  · have hb := PairedCrossover.variable_bounds v
    exact add_origin_mem_openCell p (PairedCrossover.variablePosition v) (by omega)

private theorem penultimate_mem_dropLast {r : Route} (h : 2 ≤ r.length) :
    r.getD (r.length - 2) (0, 0) ∈ r.dropLast := by
  have hk : r.length - 2 < r.dropLast.length := by simp only [List.length_dropLast]; omega
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_dropLast] at hk; omega),
    ← List.getElem_dropLast hk]
  exact List.getElem_mem hk

/-- Every raw variable is an ordinary cell's own variable, a selected crossing's own variable, or
a signal presented by a non-final cell of an occurrence path. -/
private theorem raw_variable_cases (φ : CNF ℕ) {v : Variable} (hv : v ∈ (rawFormula φ).vars) :
    (∃ p ∈ ordinaryCells φ, ∃ x, v = (p, .inl x)) ∨ (∃ p ∈ crossingSites φ, ∃ x, v = (p, .inr x)) ∨
      ∃ o ∈ Cslib.Logic.PL.occurrences φ, ∃ p ∈ (occurrencePath φ o).dropLast, ∃ q lane,
        v = signal (crossingSites φ) p q lane := by
  obtain ⟨c, hc, _, hv⟩ := CNF.mem_vars.mp hv
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hc
  rcases mem_placedClauses.mp hpc with hpc | ⟨p, hp, hpc⟩ | ⟨p, hp, hpc⟩ | ⟨o, ho, _, he, hpc⟩
  · obtain ⟨_, _, _, ho, heq⟩ := (exists_occurrence_of_mem_originalClauses hpc).1 _ hv
    exact Or.inr (Or.inr ⟨_, ho, _,
      penultimate_mem_dropLast (PlanarCompile.occurrencePath_length_ge_two ho), _, _,
      (congrArg Prod.fst heq).symm⟩)
  · exact let ⟨x, hx⟩ := ordTile.mem_var hpc hv; Or.inl ⟨p, hp, x, hx⟩
  · exact let ⟨x, hx⟩ := crossTile.mem_var hpc hv; Or.inr (Or.inl ⟨p, hp, x, hx⟩)
  · have ⟨h1, h2⟩ := List.of_mem_zip he
    rcases hpc with rfl | rfl <;> rcases link_literal_cases _ _ _ _ hv with heq | heq
    all_goals exact Or.inr (Or.inr ⟨o, ho, _, by first | exact h1 | exact List.mem_of_mem_tail h2,
      _, _, heq⟩)

/-- Every raw variable has the tag prescribed by its cell's kind. -/
theorem raw_variable_cell_kind (φ : CNF ℕ) {v : Variable}
    (hv : v ∈ (rawFormula φ).vars) : v.2.isLeft = true ↔ v.1 ∉ crossingSites φ := by
  rcases raw_variable_cases φ hv with ⟨p, hp, _, rfl⟩ | ⟨p, hp, _, rfl⟩ | ⟨-, -, p, -, q, l, rfl⟩
  · simpa using ((mem_ordinaryCells φ p).1 hp).2
  · simp [hp]
  · by_cases hp : p ∈ crossingSites φ <;> simp [signal, port, hp, Sum.isLeft]

/-- Actual variable positions identify their structured names. -/
theorem variablePosition_injOn_rawVars (φ : CNF ℕ) :
    Set.InjOn variablePosition {v | v ∈ (rawFormula φ).vars} := by
  rintro ⟨p, v⟩ hv ⟨q, w⟩ hw heq
  obtain rfl : p = q := cell_eq_of_open (variablePosition_mem_openCell (p, v))
    (congrArg realPoint heq ▸ variablePosition_mem_openCell (q, w))
  have hvk := raw_variable_cell_kind φ hv; have hwk := raw_variable_cell_kind φ hw
  cases v <;> cases w
  · exact congrArg (p, Sum.inl ·) (PairedPorts.variablePosition_injective (add_left_cancel heq))
  · exact absurd (hwk.mpr (hvk.mp rfl)) Bool.false_ne_true
  · exact absurd (hvk.mpr (hwk.mp rfl)) Bool.false_ne_true
  · exact congrArg (p, Sum.inr ·) (PairedCrossover.variablePosition_injective (add_left_cancel heq))

/-- The variable-position prefix of the actual drawing has no repetitions. -/
theorem variablePositions_nodup (φ : CNF ℕ) :
    ((rawFormula φ).distinctVars.map variablePosition).Nodup :=
  (CNF.nodup_distinctVars _).map_on (fun _ hv _ hw =>
    variablePosition_injOn_rawVars φ (CNF.mem_distinctVars.mp hv) (CNF.mem_distinctVars.mp hw))

/-- The actual drawing has exactly the compact incidence graph's number of vertices. -/
theorem positions_length (φ : CNF ℕ) :
    (positions φ).length = (SAT.incidenceGraph (formula φ)).1.length := by
  rw [positions, SAT.incidenceGraph, List.length_range, formula, CNF.distinctVars_compact]
  simp only [CNF.compact, CNF.relabel, rawFormula, List.length_append, List.length_map]

/-- Compaction preserves the ordered incidence graph. -/
theorem incidenceGraph_formula (φ : CNF ℕ) :
    SAT.incidenceGraph (formula φ) = SAT.incidenceGraph (rawFormula φ) :=
  SAT.incidenceGraph_compact _

/-! ### Route regularity, counts, and endpoint certificates -/

/-- Every actual output route is proper, orthogonal and continuously simple. -/
theorem routes_regular (φ : CNF ℕ) :
    ∀ r ∈ routes φ, IsOrthogonal r ∧ IsSimple r := fun r hr => by
  obtain ⟨pc, hpc, hr⟩ := List.mem_flatMap.mp hr
  rcases mem_placedClauses.mp hpc with hpc | ⟨_, _, hpc⟩ | ⟨_, _, hpc⟩ | ⟨_, _, _, _, hpc⟩
  · obtain ⟨_, _, _, ho, rfl⟩ := (exists_occurrence_of_mem_originalClauses hpc).2 _ hr
    exact lastLiteral_route_regular _ _ _ (PlanarCompile.occurrencePath_last_unit ho)
  · exact ordTile.route_regular OrdinaryRing.incidence_orthogonal
      OrdinaryRing.incidence_isSimple hpc hr
  · exact crossTile.route_regular PairedCrossover.incidence_orthogonal
      PairedCrossover.incidence_isSimple hpc hr
  · rcases hpc with rfl | rfl <;> exact link_routes_regular _ _ _ _ hr

private theorem ordinary_clause_vars : ∀ i : Fin 8,
    (OrdinaryRing.incidenceRoutes.filter fun e => e.1 == i.val).map (·.2.1) =
      (OrdinaryRing.formula.getD i.val []).map Prod.fst := by decide +kernel

private theorem crossing_clause_vars (i : Fin 78) :
    (PairedCrossover.incidenceRoutes.filter fun e => e.1 == i.val).map (·.2.1) =
      (PairedCrossover.formula.getD i.val []).map Prod.fst := by
  have h : ((List.range 78).map fun j =>
      (PairedCrossover.incidenceRoutes.filter fun e => e.1 == j).map (·.2.1)) =
    PairedCrossover.formula.map (List.map Prod.fst) := by decide +kernel
  have hi := congrArg (·.getD i.val []) h
  have hlt : i.val < PairedCrossover.formula.length := PairedCrossover.length_formula.symm ▸ i.isLt
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range,
    List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map] at hi
  rwa [List.getD_eq_getElem _ _ hlt]

/-- Each actual placed clause supplies exactly one route per literal, in literal order. -/
theorem placedClause_route_count (φ : CNF ℕ) :
    ∀ pc ∈ placedClauses φ, pc.2.2.length = pc.1.length := fun pc hpc => by
  rcases mem_placedClauses.mp hpc with hpc | ⟨_, _, hpc⟩ | ⟨_, _, hpc⟩ | ⟨_, _, _, _, hpc⟩
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hpc; simp
  · exact ordTile.route_count OrdinaryRing.formula_sizes.1 ordinary_clause_vars hpc
  · exact crossTile.route_count PairedCrossover.length_formula crossing_clause_vars hpc
  · rcases hpc with rfl | rfl <;> rfl

/-- The actual route count is the edge count of the final compact incidence graph. -/
theorem routes_length (φ : CNF ℕ) :
    (routes φ).length = (SAT.incidenceGraph (formula φ)).2.length := by
  rw [SAT.length_edges_incidenceGraph, formula, CNF.compact, CNF.vars_relabel, List.length_map]
  simp only [routes, List.length_flatMap, CNF.vars, List.length_map,
    List.length_flatten, rawFormula, List.map_map, Function.comp_def]
  exact congrArg List.sum (List.map_congr_left (placedClause_route_count φ))

/-- Every actual literal/route pair has the clause and variable endpoints in its record. -/
theorem placedClause_endpoints (φ : CNF ℕ) {pc : PlacedClause} (hpc : pc ∈ placedClauses φ)
    {l : Literal Variable} {r : Route} (hlr : (l, r) ∈ pc.1.zip pc.2.2) :
    r.head? = some pc.2.1 ∧ r.getLast? = some (variablePosition l.1) := by
  rcases mem_placedClauses.mp hpc with hpc | ⟨_, _, hpc⟩ | ⟨_, _, hpc⟩ | ⟨o, ho, e, he, hpc⟩
  · obtain ⟨⟨c, i⟩, hci, rfl⟩ := List.mem_map.mp hpc
    dsimp only at hlr ⊢
    obtain ⟨⟨srcLit, j⟩, hlj, rfl, rfl⟩ := List.mem_map.mp (List.zip_of_prod rfl rfl ▸ hlr)
    have ho := mk_mem_occurrences_of_mem_zipIdx hci hlj
    have hlast : (occurrencePath φ ⟨i, j, srcLit⟩).getLastD (0, 0) =
        Layout.center (φ.distinctVars.length + i) := by
      rw [List.getLastD_eq_getLast?, (PlanarCompile.occurrencePath_endpoints ho).2]; rfl
    simpa only [lastLiteral, hlast] using
      lastLiteral_endpoints (crossingSites φ) (occurrencePath φ ⟨i, j, srcLit⟩) srcLit.2
  · exact ordTile.clause_endpoints OrdinaryRing.formula_sizes.1 (fun _ _ => rfl)
      ordinary_clause_vars (fun e he => (OrdinaryRing.incidence_endpoints e he).2) hpc hlr
  · exact crossTile.clause_endpoints PairedCrossover.length_formula (fun _ _ => rfl)
      crossing_clause_vars (fun e he => (PairedCrossover.incidence_endpoints e he).2) hpc hlr
  · rcases hpc with rfl | rfl <;>
      exact link_endpoints _ (PlanarCompile.occurrencePath_unit ho (prefixStep_mem he)) _ hlr

/-- The final incidence is exactly one translated clause spoke and one neighboring access. -/
theorem support_lastLiteral (sites : List Point) (r : Route) (b : Bool)
    (h : Orthogonal.length (r.getD (r.length - 2) (0, 0)) (r.getLastD (0, 0)) = 1) :
    let p := r.getD (r.length - 2) (0, 0)
    let q := r.getLastD (0, 0)
    let s := side q p
    support (lastLiteral sites r b).2 =
      support (translate (cellOrigin 120 q) (PairedPorts.spokeRoute s)) ∪
        support (access sites p q (PairedPorts.spokeLane s)) := by
  dsimp only
  have hspoke (p q : Point) : translate (cellOrigin 120 q) (PairedPorts.spokeRoute (side q p)) =
      [center q, cellOrigin 120 q + PairedPorts.spokeElbow (side q p),
        boundary q (side q p) (PairedPorts.spokeLane (side q p))] := by
    simp only [translate, PairedPorts.spokeRoute, List.map_cons, List.map_nil, center,
      PlanarCompile.center, boundary, add_comm]
  rw [hspoke, access, shared_boundary h]
  change support [_, _, _, _] = _
  rw [support_cons_cons, support_cons_cons, support_pair, support_cons_cons, support_pair,
    Set.union_assoc]

/-- Matching paired boundaries of actual occurrence steps identify the whole occurrence and
oriented step, as well as the lane. -/
theorem boundary_occurrence_step_unique {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {o t : Occurrence ℕ} (ho : o ∈ Cslib.Logic.PL.occurrences φ)
    (ht : t ∈ Cslib.Logic.PL.occurrences φ) {e f : Point × Point} {l k : Fin 2}
    (he : e ∈ (occurrencePath φ o).consecutivePairs)
    (hf : f ∈ (occurrencePath φ t).consecutivePairs)
    (h : boundary e.1 (side e.1 e.2) l = boundary f.1 (side f.1 f.2) k) :
    l = k ∧ o = t ∧ e = f := by
  obtain ⟨hl, hmid⟩ := boundary_step_midpoint_eq (PlanarCompile.occurrencePath_unit ho he)
    (PlanarCompile.occurrencePath_unit ht hf) h
  let mids (o : Occurrence ℕ) :=
    (occurrencePath φ o).consecutivePairs.map fun e => cellPort 120 e.1 (side e.1 e.2)
  have hnf := List.nodup_flatMap.mp (show ((Cslib.Logic.PL.occurrences φ).flatMap mids).Nodup by
    simpa only [← PlanarCompile.occurrencePaths_eq_paths φ, List.flatMap_map, mids] using
      PlanarCompile.pathMidpoints_nodup hw hv)
  have hme : cellPort 120 e.1 (side e.1 e.2) ∈ mids o := List.mem_map_of_mem he
  have hmf : cellPort 120 e.1 (side e.1 e.2) ∈ mids t := hmid ▸ List.mem_map_of_mem hf
  obtain rfl : o = t := by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ho
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ht
    rcases Nat.lt_trichotomy i j with hij | rfl | hji
    · exact ((List.pairwise_iff_getElem.mp hnf.2 i j hi hj hij) hme hmf).elim
    · rfl
    · exact ((List.pairwise_iff_getElem.mp hnf.2 j i hj hi hji) hmf hme).elim
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hf
  obtain rfl := (hnf.1 o ho).eq_of_getElem_eq (by simpa [mids] using hi)
    (by simpa [mids] using hj) (by simpa [mids] using hmid)
  exact ⟨hl, rfl, rfl⟩

/-- A raw variable's incidence-graph index resolves to its actual geometric position. -/
theorem drawingPosition_raw_variable (φ : CNF ℕ) {v : Variable}
    (hv : v ∈ (rawFormula φ).vars) :
    Graph.drawingPosition (SAT.incidenceGraph (rawFormula φ)) (positions φ, routes φ)
      ((rawFormula φ).distinctVars.idxOf v) = variablePosition v := by
  have hi := List.idxOf_lt_length_of_mem (CNF.mem_distinctVars.mpr hv)
  have hlen : (rawFormula φ).distinctVars.idxOf v <
      ((rawFormula φ).distinctVars.map variablePosition).length := by simpa using hi
  change (positions φ).getD ((List.range _).idxOf ((rawFormula φ).distinctVars.idxOf v)) (0, 0) = _
  rw [List.idxOf_range_of_lt (by omega), positions, List.getD_append _ _ _ _ hlen,
    List.getD_eq_getElem _ _ hlen, List.getElem_map, List.getElem_idxOf hi]

/-- A raw clause's incidence-graph index resolves to its actual placed clause position. -/
theorem drawingPosition_raw_clause (φ : CNF ℕ) {i : ℕ} (hi : i < (placedClauses φ).length) :
    Graph.drawingPosition (SAT.incidenceGraph (rawFormula φ)) (positions φ, routes φ)
      ((rawFormula φ).distinctVars.length + i) = ((placedClauses φ)[i]).2.1 := by
  change (positions φ).getD ((List.range _).idxOf ((rawFormula φ).distinctVars.length + i))
    (0, 0) = _
  have hlen : (rawFormula φ).length = (placedClauses φ).length := List.length_map ..
  rw [List.idxOf_range_of_lt (by omega), positions,
    List.getD_append_right _ _ _ _ (by simp only [List.length_map]; omega)]
  simp only [List.length_map, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi), List.getElem_map]

private theorem raw_edges_eq (φ : CNF ℕ) :
    (SAT.incidenceGraph (rawFormula φ)).2 =
      (placedClauses φ).zipIdx.flatMap fun pci => pci.1.1.map fun l =>
        ((rawFormula φ).distinctVars.idxOf l.1, (rawFormula φ).distinctVars.length + pci.2) := by
  simp only [SAT.incidenceGraph, Cslib.Logic.PL.occurrences, rawFormula, List.zipIdx_map,
    List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def,
    Prod.map_fst, Prod.map_snd, id_eq, List.idxOf, beq_eq_decide]
  congr 1; funext pci
  simpa only [List.map_map, Function.comp_def] using
    congrArg (List.map fun (l : Literal Variable) =>
      (List.findIdx (fun x => decide (x = l.1))
        (distinctVars (List.map Prod.fst (placedClauses φ))),
        (distinctVars (List.map Prod.fst (placedClauses φ))).length + pci.2))
      (List.zipIdx_map_fst (i := 0) (l := pci.1.1))

private theorem raw_routes_endpoints (φ : CNF ℕ) :
    List.Forall₂ (fun e r =>
      r.head? = some (Graph.drawingPosition (SAT.incidenceGraph (rawFormula φ))
        (positions φ, routes φ) e.2) ∧
      r.getLast? = some (Graph.drawingPosition (SAT.incidenceGraph (rawFormula φ))
        (positions φ, routes φ) e.1))
      (SAT.incidenceGraph (rawFormula φ)).2 (routes φ) := by
  have hroutes : routes φ = (placedClauses φ).zipIdx.flatMap (·.1.2.2) := by
    simpa only [routes, List.flatMap_map] using (congrArg (List.flatMap (·.2.2))
      (List.zipIdx_map_fst (i := 0) (l := placedClauses φ))).symm
  rw [raw_edges_eq]; conv => arg 3; rw [hroutes]
  refine List.rel_flatMap (R := fun a b => a ∈ (placedClauses φ).zipIdx ∧ a = b)
    (List.forall₂_same.mpr fun _ h => ⟨h, rfl⟩) fun ⟨pc, i⟩ _ ⟨hpci, rfl⟩ => ?_
  have hpc := List.fst_mem_of_mem_zipIdx hpci
  have hi : i < (placedClauses φ).length := by simpa using (List.mem_zipIdx hpci).2.1
  rw [List.forall₂_map_left_iff, List.forall₂_iff_zip]
  refine ⟨(placedClause_route_count φ pc hpc).symm, fun {l r} hlr => ?_⟩
  have hvar : l.1 ∈ (rawFormula φ).vars :=
    CNF.mem_vars.mpr ⟨pc.1, List.mem_map_of_mem hpc, l.2, (List.of_mem_zip hlr).1⟩
  dsimp only [Function.comp_def]
  rw [drawingPosition_raw_clause φ hi, drawingPosition_raw_variable φ hvar,
    ← show pc = (placedClauses φ)[i] by simpa using (List.mem_zipIdx hpci).2.2]
  exact placedClause_endpoints φ hpc hlr

/-- Actual indexed routes have the final compact incidence graph's endpoints, in clause-to-
variable order, including repeated literal incidences. -/
theorem routes_endpoints (φ : CNF ℕ) {i : ℕ}
    (hi : i < (SAT.incidenceGraph (formula φ)).2.length) :
    let r := (routes φ).getD i []
    r.head? = some (Graph.drawingPosition (SAT.incidenceGraph (formula φ))
      (positions φ, routes φ) (SAT.incidenceGraph (formula φ)).2[i].2) ∧
    r.getLast? = some (Graph.drawingPosition (SAT.incidenceGraph (formula φ))
      (positions φ, routes φ) (SAT.incidenceGraph (formula φ)).2[i].1) := by
  simp only [incidenceGraph_formula] at hi ⊢
  have hir : i < (routes φ).length := by rwa [routes_length, incidenceGraph_formula]
  simpa only [List.get_eq_getElem, List.getD_eq_getElem _ _ hir] using
    (raw_routes_endpoints φ).get hi hir

/-! ### Variable-route contact and macrocell interiors -/

/-- Every emitted variable lies in a selected crossing or a retained occupied path cell. -/
theorem raw_variable_cell_membership (φ : CNF ℕ) {v : Variable}
    (hv : v ∈ (rawFormula φ).vars) :
    v.1 ∈ crossingSites φ ∨ ∃ r ∈ paths φ, v.1 ∈ r.dropLast := by
  rcases raw_variable_cases φ hv with ⟨p, hp, _, rfl⟩ | ⟨p, hp, _, rfl⟩ | ⟨_, ho, _, hp, _, _, rfl⟩
  · exact Or.inr ((mem_ordinaryCells φ p).1 hp).1
  · exact Or.inl hp
  · exact Or.inr ⟨_, PlanarCompile.occurrencePath_mem_paths ho, hp⟩

/-- No actual variable is placed in an original clause cell. -/
theorem raw_variable_not_clause_cell {φ : CNF ℕ} {v : Variable}
    (hv : v ∈ (rawFormula φ).vars) {i : ℕ} (hi : i < φ.length) :
    v.1 ≠ Layout.center (φ.distinctVars.length + i) := by
  intro heq
  rcases raw_variable_cell_membership φ hv with hc | ⟨r, hr, hmem⟩
  · exact PlanarCompile.clause_cell_not_mem_crossingSites φ hi (heq ▸ hc)
  · rw [show paths φ = _ from (PlanarCompile.occurrencePaths_eq_paths φ).symm] at hr
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hr
    exact PlanarCompile.clause_cell_not_mem_path_dropLast ho hi (heq ▸ hmem)

private theorem spoke_boundary_isolation {s : Fin 4} {p : ℝ × ℝ}
    (hp : p ∈ support (PairedPorts.spokeRoute s)) :
    0 ≤ p.1 ∧ p.1 ≤ 240 ∧ 0 ≤ p.2 ∧ p.2 ≤ 240 ∧
      (p.1 = 0 ∨ p.1 = 240 ∨ p.2 = 0 ∨ p.2 = 240 →
        p = realPoint (PairedPorts.boundaryPort s (PairedPorts.spokeLane s))) := by
  unfold PairedPorts.spokeRoute at hp
  rw [support_cons_cons, support_pair] at hp
  fin_cases s <;> rcases hp with hp | hp <;>
    norm_num [PairedPorts.spokeElbow, PairedPorts.spokeLane, PairedPorts.boundaryPort,
      PairedPorts.offset, Orthogonal.segment, realPoint, mem_horizontal, mem_vertical,
      Set.mem_uIcc, Prod.ext_iff] at hp ⊢ <;>
    (rcases hp with ⟨heq, hlo, hhi⟩;
      refine ⟨by linarith, by linarith, by linarith, by linarith, ?_⟩;
      rintro (h | h | h | h) <;> constructor <;> linarith)

/-- Every translated original-clause spoke stays in its clause cell. -/
theorem spoke_support_cell (c : Point) (s : Fin 4) {p : ℝ × ℝ}
    (hp : p ∈ support (translate (cellOrigin 120 c) (PairedPorts.spokeRoute s))) :
    p ∈ closedCell 120 c :=
  (translate_support_cell_isolation spoke_boundary_isolation hp).1

private theorem translated_core_mem_openCell {r : Route}
    (hi : ∀ p ∈ support r, 0 < p.1 ∧ p.1 < 240 ∧ 0 < p.2 ∧ p.2 < 240)
    (c : Point) {p : ℝ × ℝ} (hp : p ∈ support (translate (cellOrigin 120 c) r)) :
    p ∈ openCell 120 c := by
  have hx := hi _ (mem_support_translate_sub hp)
  simpa only [sub_add_cancel] using
    (mem_openCell_add_origin_iff 120 c (p - realPoint (cellOrigin 120 c))).2 hx

/-- Every translated ordinary core incidence is strictly inside its cell. -/
theorem ordinaryRoute_mem_openCell {e : ℕ × OrdinaryRing.Variable × Route}
    (he : e ∈ OrdinaryRing.incidenceRoutes) (c : Point) {p : ℝ × ℝ}
    (hp : p ∈ support (translate (cellOrigin 120 c) e.2.2)) : p ∈ openCell 120 c :=
  translated_core_mem_openCell (fun _ hp => OrdinaryRing.core_support_interior he hp) c hp

/-- Every translated crossover core incidence is strictly inside its cell. -/
theorem crossingRoute_mem_openCell {e : ℕ × PairedCrossover.Variable × Route}
    (he : e ∈ PairedCrossover.incidenceRoutes) (c : Point) {p : ℝ × ℝ}
    (hp : p ∈ support (translate (cellOrigin 120 c) e.2.2)) : p ∈ openCell 120 c :=
  translated_core_mem_openCell (fun _ hp => PairedCrossover.core_support_interior he hp) c hp

/-- An actual access visits a correctly tagged variable only at its own endpoint. -/
theorem access_variable_contact {sites : List Point} {c q : Point} {lane : Fin 2} {v : Variable}
    (hkind : v.2.isLeft = true ↔ v.1 ∉ sites)
    (hp : realPoint (variablePosition v) ∈ support (access sites c q lane)) :
    v = signal sites c q lane := by
  have hcell : v.1 = c := cell_eq_of_mem_open_closed (by decide)
    (variablePosition_mem_openCell v) (access_support_cell sites c q lane hp).1
  have resolve {V : Type} (varPos : V → Point) (tgt w : V)
      (hpos : realPoint (cellOrigin 120 c + varPos w) ∈
        support (translate (cellOrigin 120 c) (PairedPorts.accessRoute (side c q) lane)))
      (havoid : w ≠ tgt →
        realPoint (varPos w) ∉ support (PairedPorts.accessRoute (side c q) lane)) : w = tgt :=
    by_contra fun h => havoid h ((mem_support_translate_iff _ _ _).1
      (by simpa only [realPoint_add, add_comm] using hpos))
  rw [access_eq_translate] at hp
  rcases v with ⟨d, v | v⟩ <;> (change d = c at hcell; subst d)
  · simp only [resolve OrdinaryRing.variablePosition (side c q, lane) v hp
      OrdinaryRing.access_variable_not_mem, signal, port, hkind.mp rfl, ↓reduceIte]
  · have hc : c ∈ sites := by_contra fun hn => Bool.false_ne_true (hkind.mpr hn)
    simp only [resolve PairedCrossover.variablePosition (PairedCrossover.terminal (side c q) lane) v
      hp PairedCrossover.access_variable_not_mem, signal, port, hc, ↓reduceIte]

private theorem TileSpec.variable_contact {V : Type} {t : TileSpec V} {c : Point}
    {pc : PlacedClause} {r : Route} {v : Variable}
    (htag : ∀ x, variablePosition (c, t.tag x) = cellOrigin 120 c + t.varPos x)
    (hmatch : v.1 = c → ∃ x, v.2 = t.tag x)
    (hcore : ∀ e ∈ t.inc, ∀ {q}, q ∈ support (translate (cellOrigin 120 c) e.2.2) →
      q ∈ openCell 120 c)
    (havoid : ∀ {e}, e ∈ t.inc → ∀ w, w ≠ e.2.1 → realPoint (t.varPos w) ∉ support e.2.2)
    (hlast : ∀ e ∈ t.inc, e.2.2.getLast? = some (t.varPos e.2.1))
    (hpc : pc ∈ t.clauses c) (hr : r ∈ pc.2.2)
    (hp : realPoint (variablePosition v) ∈ support r) :
    r.getLast? = some (variablePosition v) := by
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hpc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
  have he' := (List.mem_filter.mp he).1
  have hcell : v.1 = c := cell_eq_of_open (variablePosition_mem_openCell v) (hcore e he' hp)
  obtain ⟨w, hvw⟩ := hmatch hcell
  have hv_eq : v = (c, t.tag w) := Prod.ext hcell hvw
  have hwe : w = e.2.1 := by_contra fun hne => havoid he' w hne
    ((mem_support_translate_iff (cellOrigin 120 c) _ _).1
      (by simpa only [hv_eq, htag, realPoint_add, add_comm] using hp))
  simp only [translate, List.getLast?_map, hlast e he', Option.map_some, hv_eq, htag, hwe, add_comm]

/-- Every actual route can meet an emitted variable only at its variable endpoint. -/
theorem route_variable_contact (φ : CNF ℕ) {r : Route} (hr : r ∈ routes φ)
    {v : Variable} (hv : v ∈ (rawFormula φ).vars)
    (hp : realPoint (variablePosition v) ∈ support r) :
    r.getLast? = some (variablePosition v) := by
  obtain ⟨pc, hpc, hr⟩ := List.mem_flatMap.mp hr
  have hkind := raw_variable_cell_kind φ hv
  rcases mem_placedClauses.mp hpc with hpc | ⟨c, hc, hpc⟩ | ⟨c, hc, hpc⟩ | ⟨_, _, _, _, hpc⟩
  · obtain ⟨_, _, _, ho, rfl⟩ := (exists_occurrence_of_mem_originalClauses hpc).2 _ hr
    rw [support_lastLiteral _ _ _ (PlanarCompile.occurrencePath_last_unit ho)] at hp
    rcases hp with hp | hp
    · have hcell := cell_eq_of_mem_open_closed (by decide) (variablePosition_mem_openCell v)
        (spoke_support_cell _ _ hp)
      rw [List.getLastD_eq_getLast?, (PlanarCompile.occurrencePath_endpoints ho).2] at hcell
      exact (raw_variable_not_clause_cell hv (Cslib.Logic.PL.mem_occurrences.mp ho).1 hcell).elim
    · exact access_variable_contact hkind hp ▸ (lastLiteral_endpoints _ _ _).2
  · refine ordTile.variable_contact (fun _ => rfl)
      (fun hc' => match hv2 : v.2 with
        | .inl w => ⟨w, rfl⟩
        | .inr _ => absurd (hkind.mpr (hc' ▸ ((mem_ordinaryCells φ c).1 hc).2))
            (by rw [hv2]; exact Bool.false_ne_true))
      (fun _ he _ => ordinaryRoute_mem_openCell he c)
      (fun he _ => OrdinaryRing.variable_not_mem_support he)
      (fun e he => (OrdinaryRing.incidence_endpoints e he).2.2) hpc hr hp
  · refine crossTile.variable_contact (fun _ => rfl)
      (fun hc' => match hv2 : v.2 with
        | .inl _ => absurd (hc' ▸ hc) (hkind.mp (by rw [hv2]; rfl))
        | .inr w => ⟨w, rfl⟩)
      (fun _ he _ => crossingRoute_mem_openCell he c)
      (fun he _ => PairedCrossover.variable_not_mem_support he)
      (fun e he => (PairedCrossover.incidence_endpoints e he).2.2) hpc hr hp
  · rcases hpc with rfl | rfl <;> rcases link_routes_cases _ _ _ _ hr with rfl | rfl <;>
      exact access_variable_contact hkind hp ▸ rfl

/-! ### Clause positions and vertex distinctness -/

/-- Ordinary clause positions are strictly inside their cell. -/
theorem ordinaryClause_mem_openCell {c : Point} {pc : PlacedClause}
    (hpc : pc ∈ ordinaryClauses c) : realPoint pc.2.1 ∈ openCell 120 c :=
  ordTile.clause_mem_openCell
    (OrdinaryRing.formula_sizes.1.trans OrdinaryRing.drawing_sizes.1.symm)
    OrdinaryRing.clause_bounds hpc

/-- Crossover clause positions are strictly inside their cell. -/
theorem crossingClause_mem_openCell {c : Point} {pc : PlacedClause}
    (hpc : pc ∈ crossingClauses c) : realPoint pc.2.1 ∈ openCell 120 c :=
  crossTile.clause_mem_openCell
    (PairedCrossover.length_formula.trans PairedCrossover.drawing_sizes.1.symm)
    PairedCrossover.clause_bounds hpc

/-- An ordinary tile retains the fixed ring's clause-position order. -/
theorem ordinaryClause_positions (c : Point) :
    (ordinaryClauses c).map (fun pc => pc.2.1) =
      OrdinaryRing.clausePositions.map (cellOrigin 120 c + ·) :=
  ordTile.clause_positions
    (OrdinaryRing.formula_sizes.1.trans OrdinaryRing.drawing_sizes.1.symm) c

/-- A crossover tile retains the fixed paired crossover's clause-position order. -/
theorem crossingClause_positions (c : Point) :
    (crossingClauses c).map (fun pc => pc.2.1) =
      PairedCrossover.clausePositions.map (cellOrigin 120 c + ·) :=
  crossTile.clause_positions
    (PairedCrossover.length_formula.trans PairedCrossover.drawing_sizes.1.symm) c

private theorem interior_positions_nodup {cells : List Point} (hn : cells.Nodup)
    (pcs : Point → List PlacedClause) (base : List Point) (hbase : base.Nodup)
    (hpos : ∀ c, (pcs c).map (·.2.1) = base.map (cellOrigin 120 c + ·))
    (hinterior : ∀ c, ∀ pc ∈ pcs c, realPoint pc.2.1 ∈ openCell 120 c) :
    ((cells.flatMap pcs).map fun pc => pc.2.1).Nodup := by
  rw [List.map_flatMap, List.nodup_flatMap]
  refine ⟨fun c _ => by rw [hpos]; exact hbase.map fun _ _ => add_left_cancel, hn.imp ?_⟩
  intro c d hcd p hp hq
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hp
  obtain ⟨pd, hpd, heq⟩ := List.mem_map.mp hq
  exact hcd (cell_eq_of_open (hinterior c pc hpc) (heq ▸ hinterior d pd hpd))

/-- Emitted seam clause positions are a sublist of all paired path boundaries. -/
theorem linkPositions_sublist_boundaries (φ : CNF ℕ) :
    (((Cslib.Logic.PL.occurrences φ).flatMap fun o =>
      links (crossingSites φ) (occurrencePath φ o)).map fun pc => pc.2.1).Sublist
    ((paths φ).flatMap fun r => r.consecutivePairs.flatMap fun e =>
      [boundary e.1 (side e.1 e.2) 0, boundary e.1 (side e.1 e.2) 1]) := by
  change List.Sublist _ ((PlanarCompile.paths φ).flatMap fun r =>
    r.consecutivePairs.flatMap fun e =>
      [boundary e.1 (side e.1 e.2) 0, boundary e.1 (side e.1 e.2) 1])
  rw [← PlanarCompile.occurrencePaths_eq_paths φ, List.flatMap_map]
  simp only [List.map_flatMap, links, List.map_cons, List.map_nil, link]
  apply List.Sublist.flatMap_right
  intro _ _; apply List.Sublist.flatMap
  rw [consecutivePairs_dropLast]; exact List.dropLast_sublist _

/-- All actual paired-link clauses have distinct positions. -/
theorem linkPositions_nodup {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    (((Cslib.Logic.PL.occurrences φ).flatMap fun o =>
      links (crossingSites φ) (occurrencePath φ o)).map fun pc => pc.2.1).Nodup :=
  (pathBoundaries_nodup hw hv).sublist (linkPositions_sublist_boundaries φ)

private theorem clause_map_disjoint_of_openCell {A B : List PlacedClause}
    (h : ∀ pc ∈ A, ∀ pd ∈ B, pc.2.1 = pd.2.1 → False) :
    List.Disjoint (A.map fun pc => pc.2.1) (B.map fun pc => pc.2.1) := by
  intro p hp hq
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hp
  obtain ⟨pd, hpd, heq⟩ := List.mem_map.mp hq
  exact h pc hpc pd hpd heq.symm

private theorem original_interior_positions_disjoint (φ : CNF ℕ) {cells : List Point}
    {pcs : Point → List PlacedClause}
    (hint : ∀ c, ∀ pc ∈ pcs c, realPoint pc.2.1 ∈ openCell 120 c)
    (hex : ∀ i < φ.length, Layout.center (φ.distinctVars.length + i) ∉ cells) :
    List.Disjoint ((originalClauses φ (crossingSites φ)).map fun pc => pc.2.1)
      ((cells.flatMap pcs).map fun pc => pc.2.1) :=
  clause_map_disjoint_of_openCell fun pc hpc pd hpd heq => by
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨c, hc, hpd⟩ := List.mem_flatMap.mp hpd
    have hi : ci.2 < φ.length := by simpa only [Nat.zero_add] using (List.mem_zipIdx hci).2.1
    exact hex ci.2 hi (cell_eq_of_open (center_mem_openCell (r := 120) (by decide) _)
      (heq ▸ hint c pd hpd) ▸ hc)

private theorem originalPositions_nodup (φ : CNF ℕ) :
    ((originalClauses φ (crossingSites φ)).map fun pc => pc.2.1).Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j _ _ hij heq
  simp only [originalClauses, List.getElem_map, List.getElem_zipIdx] at heq
  have hx := congrArg Prod.fst (PlanarCompile.center_injective heq)
  simp only [Layout.center] at hx; omega

private theorem open_prefix_disjoint_links (φ : CNF ℕ) :
    List.Disjoint ((originalClauses φ (crossingSites φ) ++
        (ordinaryCells φ).flatMap ordinaryClauses ++
        (crossingSites φ).flatMap crossingClauses).map fun pc => pc.2.1)
      (((Cslib.Logic.PL.occurrences φ).flatMap fun o =>
        links (crossingSites φ) (occurrencePath φ o)).map fun pc => pc.2.1) :=
  clause_map_disjoint_of_openCell fun pc hpc pd hpd heq => by
    obtain ⟨_, _, hpd⟩ := List.mem_flatMap.mp hpd
    have ⟨c, hc⟩ : ∃ c, realPoint pc.2.1 ∈ openCell 120 c := by
      simp only [List.mem_append, List.mem_flatMap] at hpc
      rcases hpc with (hpc | ⟨c, _, hpc⟩) | ⟨c, _, hpc⟩
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hpc
        exact ⟨_, center_mem_openCell (by decide) _⟩
      · exact ⟨c, ordinaryClause_mem_openCell hpc⟩
      · exact ⟨c, crossingClause_mem_openCell hpc⟩
    obtain ⟨_, _, rfl | rfl⟩ := mem_links.mp hpd <;>
      exact PairedPorts.boundary_not_mem_openCell _ c _ _ (heq ▸ hc)

/-- All actual original, ordinary, crossover and paired-seam clause positions are distinct. -/
theorem clausePositions_nodup {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    ((placedClauses φ).map fun pc => pc.2.1).Nodup := by
  have hord := interior_positions_nodup (ordinaryCells_nodup φ) ordinaryClauses
    OrdinaryRing.clausePositions OrdinaryRing.clausePositions_nodup ordinaryClause_positions
    (fun _ _ => ordinaryClause_mem_openCell)
  have hcross := interior_positions_nodup (PlanarCompile.crossingSites_nodup φ)
    crossingClauses PairedCrossover.clausePositions PairedCrossover.clausePositions_nodup
    crossingClause_positions (fun _ _ => crossingClause_mem_openCell)
  have hdisj_oc := clause_map_disjoint_of_openCell
    (A := (ordinaryCells φ).flatMap ordinaryClauses)
    (B := (crossingSites φ).flatMap crossingClauses) fun _ hpc _ hpd heq => by
      obtain ⟨c, hc, hpc⟩ := List.mem_flatMap.mp hpc
      obtain ⟨d, hd, hpd⟩ := List.mem_flatMap.mp hpd
      exact ((mem_ordinaryCells φ c).1 hc).2
        (cell_eq_of_open (ordinaryClause_mem_openCell hpc)
          (heq ▸ crossingClause_mem_openCell hpd) ▸ hd)
  rw [placedClauses, List.map_append]
  refine List.Nodup.append ?_ (linkPositions_nodup hw hv) (open_prefix_disjoint_links φ)
  simp only [List.map_append]
  refine ((originalPositions_nodup φ).append hord (original_interior_positions_disjoint φ
    (fun _ _ => ordinaryClause_mem_openCell) (fun _ hi => clause_cell_not_ordinary hi))).append
    hcross fun _ hp hq => (List.mem_append.mp hp).elim
      (fun h => original_interior_positions_disjoint φ (fun _ _ => crossingClause_mem_openCell)
        (fun _ hi => PlanarCompile.clause_cell_not_mem_crossingSites φ hi) h hq)
      (fun h => hdisj_oc h hq)

private theorem crossingRoute_length : ∀ e ∈ PairedCrossover.incidenceRoutes,
    2 ≤ e.2.2.length := by decide +kernel

private theorem crossing_formula_nonempty : ∀ c ∈ PairedCrossover.formula, c ≠ [] := by
  decide +kernel

/-- Every actual incidence route contains at least two distinct endpoint positions. -/
theorem routes_length_ge_two (φ : CNF ℕ) : ∀ r ∈ routes φ, 2 ≤ r.length := by
  intro r hr
  obtain ⟨pc, hpc, hr⟩ := List.mem_flatMap.mp hr
  rcases mem_placedClauses.mp hpc with hpc | ⟨_, _, hpc⟩ | ⟨_, _, hpc⟩ | ⟨_, _, _, _, hpc⟩
  · obtain ⟨_, _, _, -, rfl⟩ := (exists_occurrence_of_mem_originalClauses hpc).2 _ hr
    simp [lastLiteral]
  · exact ordTile.route_length_ge_two
      (fun e he => by rw [OrdinaryRing.incidence_pair e he]; simp) hpc hr
  · exact crossTile.route_length_ge_two crossingRoute_length hpc hr
  · rcases hpc with rfl | rfl <;>
      rcases link_routes_cases _ _ _ _ hr with rfl | rfl <;> simp [access]

private theorem placedClause_nonempty_or_original {φ : CNF ℕ} {pc : PlacedClause}
    (hpc : pc ∈ placedClauses φ) : pc.1 ≠ [] ∨ pc ∈ originalClauses φ (crossingSites φ) := by
  rcases mem_placedClauses.mp hpc with hpc | ⟨_, _, hpc⟩ | ⟨_, _, hpc⟩ | ⟨_, _, _, _, hpc⟩
  · exact Or.inr hpc
  · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
    exact Or.inl fun h => by
      have hw := OrdinaryRing.formula_sizes.2 ci.1 (List.fst_mem_of_mem_zipIdx hci)
      have hl := congrArg List.length h
      simp only [Clause.length_relabel, List.length_nil] at hl
      omega
  · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
    exact Or.inl fun h =>
      crossing_formula_nonempty ci.1 (List.fst_mem_of_mem_zipIdx hci) (List.map_eq_nil_iff.mp h)
  · rcases hpc with rfl | rfl <;> exact Or.inl (by simp [link])

private theorem placedClause_route_endpoints (φ : CNF ℕ) {pc : PlacedClause}
    (hpc : pc ∈ placedClauses φ) {r : Route} (hr : r ∈ pc.2.2) :
    ∃ v ∈ (rawFormula φ).vars,
      r.head? = some pc.2.1 ∧ r.getLast? = some (variablePosition v) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  have hi' : i < pc.1.length := placedClause_route_count φ pc hpc ▸ hi
  have hzip : (pc.1[i], pc.2.2[i]) ∈ pc.1.zip pc.2.2 := by
    have hz : i < (pc.1.zip pc.2.2).length := by simp only [List.length_zip]; omega
    simpa only [List.getElem_zip] using List.getElem_mem hz
  exact ⟨pc.1[i].1, CNF.mem_vars.mpr ⟨pc.1, List.mem_map_of_mem hpc, pc.1[i].2,
    List.getElem_mem hi'⟩, placedClause_endpoints φ hpc hzip⟩

private theorem placedClause_exists_route {φ : CNF ℕ} {pc : PlacedClause}
    (hpc : pc ∈ placedClauses φ) (hne : pc.1 ≠ []) :
    ∃ r ∈ routes φ, r.head? = some pc.2.1 :=
  let hpos : 0 < pc.2.2.length :=
    (placedClause_route_count φ pc hpc).symm ▸ List.length_pos_iff.mpr hne
  let hm := List.getElem_mem hpos
  ⟨pc.2.2[0], List.mem_flatMap.mpr ⟨pc, hpc, hm⟩,
    (placedClause_route_endpoints φ hpc hm).choose_spec.2.1⟩

/-- Actual variable and clause position lists are disjoint. -/
theorem variable_clause_positions_disjoint (φ : CNF ℕ) :
    List.Disjoint ((rawFormula φ).distinctVars.map variablePosition)
      ((placedClauses φ).map fun pc => pc.2.1) := by
  intro p hp hq
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
  obtain ⟨pc, hpc, heq⟩ := List.mem_map.mp hq
  have hv' := CNF.mem_distinctVars.mp hv
  rcases placedClause_nonempty_or_original hpc with hne | horiginal
  · obtain ⟨r, hr, hhead⟩ := placedClause_exists_route hpc hne
    have hhead' : r.head? = some (variablePosition v) := hhead.trans (congrArg some heq)
    have hlast := route_variable_contact φ hr hv' (realPoint_mem_support_of_head? hhead')
    have hlen : 2 ≤ r.length := routes_length_ge_two φ r hr
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hhead'
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlast
    have hidx := (routes_regular φ r hr).2.1.eq_of_getElem_eq (by omega) (by omega)
      (Option.some.inj (hhead'.trans hlast.symm))
    omega
  · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp horiginal
    have hi : ci.2 < φ.length := by simpa only [Nat.zero_add] using (List.mem_zipIdx hci).2.1
    exact raw_variable_not_clause_cell hv' hi (cell_eq_of_open (variablePosition_mem_openCell v)
      (congrArg realPoint heq ▸ center_mem_openCell (r := 120) (by decide) _))

/-- Every actual displayed graph vertex has its own position. -/
theorem positions_nodup {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) : (positions φ).Nodup :=
  (variablePositions_nodup φ).append (clausePositions_nodup hw hv)
    (variable_clause_positions_disjoint φ)

/-! ### Continuous piece-by-piece contact decomposition -/

private def lastStep (r : Route) : Point × Point :=
  (r.getD (r.length - 2) (0, 0), r.getLastD (0, 0))

private theorem lastStep_mem {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
    lastStep (occurrencePath φ o) ∈ (occurrencePath φ o).consecutivePairs := by
  let r := occurrencePath φ o
  have hlen : 2 ≤ r.length := PlanarCompile.occurrencePath_length_ge_two ho
  have hk : r.length - 2 < r.consecutivePairs.length := by grind
  suffices r.consecutivePairs[r.length - 2] = lastStep r from this ▸ List.getElem_mem hk
  rw [List.getElem_zip, List.getElem_tail]
  refine Prod.ext ((List.getD_eq_getElem r (0, 0) (by omega)).symm) ?_
  dsimp only [lastStep]
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega),
    Option.getD_some]
  change r[r.length - 2 + 1] = r[r.length - 1]; congr 1; omega

private theorem lastStep_not_prefix {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
    lastStep (occurrencePath φ o) ∉ (occurrencePath φ o).dropLast.consecutivePairs := by
  intro he
  have hp : (occurrencePath φ o).getLastD (0, 0) ∈ (occurrencePath φ o).dropLast :=
    List.mem_of_mem_tail (List.of_mem_zip he).2
  rw [List.getLastD_eq_getLast?, (PlanarCompile.occurrencePath_endpoints ho).2] at hp
  exact PlanarCompile.clause_cell_not_mem_path_dropLast ho
    (Cslib.Logic.PL.mem_occurrences.mp ho).1 hp

private def RouteEnd (r : Route) (a : Point) : Prop :=
  r.head? = some a ∨ r.getLast? = some a

private inductive AccessPiece (φ : CNF ℕ) : Route → Point → Point → Fin 2 → Prop where
  | link {o : Occurrence ℕ} (ho : o ∈ Cslib.Logic.PL.occurrences φ) {e : Point × Point}
      (he : e ∈ (occurrencePath φ o).dropLast.consecutivePairs) (l : Fin 2) :
      AccessPiece φ (access (crossingSites φ) e.1 e.2 l) e.1 e.2 l
  | reverseLink {o : Occurrence ℕ} (ho : o ∈ Cslib.Logic.PL.occurrences φ) {e : Point × Point}
      (he : e ∈ (occurrencePath φ o).dropLast.consecutivePairs) (l : Fin 2) :
      AccessPiece φ (access (crossingSites φ) e.2 e.1 l) e.2 e.1 l
  | final {o : Occurrence ℕ} (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
      AccessPiece φ (lastLiteral (crossingSites φ) (occurrencePath φ o) o.lit.2).2
        (lastStep (occurrencePath φ o)).1 (lastStep (occurrencePath φ o)).2
        (PairedPorts.spokeLane
          (side (lastStep (occurrencePath φ o)).2 (lastStep (occurrencePath φ o)).1))

private theorem AccessPiece.inner_endpoint {φ : CNF ℕ} {r : Route} {c q : Point} {l : Fin 2}
    (h : AccessPiece φ r c q l) :
    r.getLast? = some (variablePosition (signal (crossingSites φ) c q l)) := by
  cases h <;> rfl

private theorem AccessPiece.not_clause_cell {φ : CNF ℕ} {r : Route} {c q : Point} {l : Fin 2}
    (h : AccessPiece φ r c q l) {i : ℕ} (hi : i < φ.length) :
    c ≠ Layout.center (φ.distinctVars.length + i) := by
  intro heq
  cases h with
  | link ho he _ =>
    exact PlanarCompile.clause_cell_not_mem_path_dropLast ho hi (heq ▸ (List.of_mem_zip he).1)
  | reverseLink ho he _ =>
    exact PlanarCompile.clause_cell_not_mem_path_dropLast ho hi
      (heq ▸ List.mem_of_mem_tail (List.of_mem_zip he).2)
  | final ho =>
    exact PlanarCompile.clause_cell_not_mem_path_dropLast ho hi
      (heq ▸ penultimate_mem_dropLast (PlanarCompile.occurrencePath_length_ge_two ho))

private theorem AccessPiece.source {φ : CNF ℕ} {r : Route} {c q : Point} {l : Fin 2}
    (h : AccessPiece φ r c q l) :
    ∃ o ∈ Cslib.Logic.PL.occurrences φ, ∃ e ∈ (occurrencePath φ o).consecutivePairs,
      boundary c (side c q) l = boundary e.1 (side e.1 e.2) l ∧
      ((e ∈ (occurrencePath φ o).dropLast.consecutivePairs ∧
          r = access (crossingSites φ) c q l) ∨
        (e = lastStep (occurrencePath φ o) ∧
          r = (lastLiteral (crossingSites φ) (occurrencePath φ o) o.lit.2).2)) := by
  cases h with
  | link ho he l => exact ⟨_, ho, _, prefixStep_mem he, rfl, Or.inl ⟨he, rfl⟩⟩
  | reverseLink ho he l =>
    exact ⟨_, ho, _, prefixStep_mem he,
      (shared_boundary (PlanarCompile.occurrencePath_unit ho (prefixStep_mem he)) l).symm,
      Or.inl ⟨he, rfl⟩⟩
  | final ho => exact ⟨_, ho, _, lastStep_mem ho, rfl, Or.inr ⟨rfl, rfl⟩⟩

private theorem accessPieces_same_boundary {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {r s : Route} {c q d t : Point} {l k : Fin 2}
    (hr : AccessPiece φ r c q l) (hs : AccessPiece φ s d t k)
    (h : boundary c (side c q) l = boundary d (side d t) k) :
    (r = access (crossingSites φ) c q l ∧ s = access (crossingSites φ) d t k) ∨ r = s := by
  obtain ⟨o, ho, e, he, hport, hr⟩ := hr.source
  obtain ⟨u, hu, f, hf, hport', hs⟩ := hs.source
  obtain ⟨_, rfl, rfl⟩ := boundary_occurrence_step_unique hw hv ho hu he hf
    (hport.symm.trans (h.trans hport'))
  rcases hr with ⟨hp, hr⟩ | ⟨hf, hr⟩ <;> rcases hs with ⟨hp', hs⟩ | ⟨hf', hs⟩
  · exact Or.inl ⟨hr, hs⟩
  · exact (lastStep_not_prefix ho (hf' ▸ hp)).elim
  · exact (lastStep_not_prefix ho (hf ▸ hp')).elim
  · exact Or.inr (hr.trans hs.symm)

private theorem accessPieces_contact {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {r s : Route} {c q d t : Point} {l k : Fin 2}
    (hr : AccessPiece φ r c q l) (hs : AccessPiece φ s d t k) (hne : r ≠ s)
    {p : ℝ × ℝ} (hp : p ∈ support (access (crossingSites φ) c q l))
    (hq : p ∈ support (access (crossingSites φ) d t k)) :
    ∃ a : Point, p = realPoint a ∧ RouteEnd r a ∧ RouteEnd s a := by
  by_cases hcd : c = d
  · subst d
    by_cases hport : (side c q, l) = (side c t, k)
    · have hb : boundary c (side c q) l = boundary c (side c t) k :=
        congrArg (fun x : PairedPorts.Port => boundary c x.1 x.2) hport
      rcases accessPieces_same_boundary hw hv hr hs hb with ⟨hr', hs'⟩ | heq
      · exact (hne (by
          rw [hr', hs', access_eq_translate, access_eq_translate]
          exact congrArg (fun x : PairedPorts.Port =>
            translate (cellOrigin 120 c) (PairedPorts.accessRoute x.1 x.2)) hport)).elim
      · exact (hne heq).elim
    · exact (Set.disjoint_left.mp (access_disjoint_same_cell _ _ _ _ _ _ hport) hp hq).elim
  · have hcontact := access_contact_of_distinct_cells (crossingSites φ) (crossingSites φ)
      hcd q t l k hp hq
    have hport := realPoint_injective (hcontact.1.symm.trans hcontact.2)
    rcases accessPieces_same_boundary hw hv hr hs hport with ⟨hr', hs'⟩ | heq
    · exact ⟨boundary c (side c q) l, hcontact.1,
        Or.inl (by rw [hr', access]; rfl), Or.inl (by rw [hs', access, ← hport]; rfl)⟩
    · exact (hne heq).elim

/-- A translated clause spoke touches its cell boundary only at the chosen paired port. -/
theorem spoke_support_boundary (c : Point) (s : Fin 4) {p : ℝ × ℝ}
    (hp : p ∈ support (translate (cellOrigin 120 c) (PairedPorts.spokeRoute s)))
    (hnot : p ∉ openCell 120 c) :
    p = realPoint (boundary c s (PairedPorts.spokeLane s)) :=
  (translate_support_cell_isolation spoke_boundary_isolation hp).2 hnot

private inductive SpokePiece (φ : CNF ℕ) : Route → Point → Fin 4 → Prop where
  | final {o : Occurrence ℕ} (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
      SpokePiece φ (lastLiteral (crossingSites φ) (occurrencePath φ o) o.lit.2).2
        (lastStep (occurrencePath φ o)).2
        (side (lastStep (occurrencePath φ o)).2 (lastStep (occurrencePath φ o)).1)

private theorem SpokePiece.clause_cell {φ : CNF ℕ} {r : Route} {c : Point} {s : Fin 4}
    (h : SpokePiece φ r c s) : ∃ i < φ.length, c = Layout.center (φ.distinctVars.length + i) := by
  cases h with
  | final ho =>
    refine ⟨_, (Cslib.Logic.PL.mem_occurrences.mp ho).1, ?_⟩
    change (occurrencePath φ _).getLastD (0, 0) = _
    rw [List.getLastD_eq_getLast?, (PlanarCompile.occurrencePath_endpoints ho).2]; rfl

private theorem SpokePiece.access {φ : CNF ℕ} {r : Route} {c : Point} {s : Fin 4}
    (h : SpokePiece φ r c s) :
    ∃ q, AccessPiece φ r q c (PairedPorts.spokeLane s) ∧
      boundary c s (PairedPorts.spokeLane s) = boundary q (side q c) (PairedPorts.spokeLane s) := by
  cases h with
  | final ho =>
    exact ⟨_, AccessPiece.final ho,
      (shared_boundary (PlanarCompile.occurrencePath_last_unit ho) _).symm⟩

private theorem spoke_access_same_boundary {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {r s : Route} {c d t : Point} {i : Fin 4} {k : Fin 2}
    (hr : SpokePiece φ r c i) (hs : AccessPiece φ s d t k)
    (hb : boundary c i (PairedPorts.spokeLane i) = boundary d (side d t) k) : r = s := by
  obtain ⟨_, haccess, hport⟩ := hr.access
  rcases accessPieces_same_boundary hw hv haccess hs (hport.symm.trans hb) with ⟨hr', _⟩ | heq
  · have hlen := congrArg List.length hr'
    cases hr; simp [lastLiteral, access] at hlen
  · exact heq

private theorem spoke_access_disjoint {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {r s : Route} {c d t : Point} {i : Fin 4} {k : Fin 2}
    (hr : SpokePiece φ r c i) (hs : AccessPiece φ s d t k) (hne : r ≠ s) :
    Disjoint (support (translate (cellOrigin 120 c) (PairedPorts.spokeRoute i)))
      (support (access (crossingSites φ) d t k)) := by
  rw [Set.disjoint_left]
  intro p hp hq
  by_cases hcd : c = d
  · obtain ⟨_, hj, hcell⟩ := hr.clause_cell
    exact hs.not_clause_cell hj (hcd.symm.trans hcell)
  · have hc := spoke_support_cell c i hp
    have hd := access_support_cell (crossingSites φ) d t k hq
    have hp' := spoke_support_boundary c i hp (not_mem_openCell_of_ne hcd hd.1)
    have hq' := hd.2 (not_mem_openCell_of_ne (Ne.symm hcd) hc)
    exact hne (spoke_access_same_boundary hw hv hr hs (realPoint_injective (hp'.symm.trans hq')))

private theorem spokePieces_contact {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {r s : Route} {c d : Point} {i j : Fin 4}
    (hr : SpokePiece φ r c i) (hs : SpokePiece φ s d j) (hne : r ≠ s)
    {p : ℝ × ℝ} (hp : p ∈ support (translate (cellOrigin 120 c) (PairedPorts.spokeRoute i)))
    (hq : p ∈ support (translate (cellOrigin 120 d) (PairedPorts.spokeRoute j))) :
    ∃ a : Point, p = realPoint a ∧ RouteEnd r a ∧ RouteEnd s a := by
  have same_bdy (hb : boundary c i (PairedPorts.spokeLane i) =
      boundary d j (PairedPorts.spokeLane j)) : r = s := by
    obtain ⟨_, hacc, hport⟩ := hs.access
    exact spoke_access_same_boundary hw hv hr hacc (hb.trans hport)
  by_cases hcd : c = d
  · subst d
    by_cases hij : i = j
    · exact (hne (same_bdy (hij ▸ rfl))).elim
    · have hcenter := PairedPorts.spokes_contact hij
        (mem_support_translate_sub hp) (mem_support_translate_sub hq)
      have hpr : p = realPoint (center c) := by
        rw [← sub_add_cancel p (realPoint (cellOrigin 120 c)), hcenter, center,
          PlanarCompile.center, realPoint_add, add_comm]
      exact ⟨center c, hpr, Or.inl (by cases hr; rfl), Or.inl (by cases hs; rfl)⟩
  · have hp' := spoke_support_boundary c i hp
      (not_mem_openCell_of_ne hcd (spoke_support_cell d j hq))
    have hq' := spoke_support_boundary d j hq
      (not_mem_openCell_of_ne (Ne.symm hcd) (spoke_support_cell c i hp))
    exact (hne (same_bdy (realPoint_injective (hp'.symm.trans hq')))).elim

private inductive CorePiece (φ : CNF ℕ) : Route → Point → Prop where
  | ordinary {c : Point} (hc : c ∈ ordinaryCells φ) {e : ℕ × OrdinaryRing.Variable × Route}
      (he : e ∈ OrdinaryRing.incidenceRoutes) :
      CorePiece φ (translate (cellOrigin 120 c) e.2.2) c
  | crossing {c : Point} (hc : c ∈ crossingSites φ) {e : ℕ × PairedCrossover.Variable × Route}
      (he : e ∈ PairedCrossover.incidenceRoutes) :
      CorePiece φ (translate (cellOrigin 120 c) e.2.2) c

private theorem CorePiece.interior {φ : CNF ℕ} {r : Route} {c : Point}
    (h : CorePiece φ r c) {p : ℝ × ℝ} (hp : p ∈ support r) : p ∈ openCell 120 c := by
  cases h with
  | ordinary _ he => exact ordinaryRoute_mem_openCell he _ hp
  | crossing _ he => exact crossingRoute_mem_openCell he _ hp

private theorem CorePiece.not_clause_cell {φ : CNF ℕ} {r : Route} {c : Point}
    (h : CorePiece φ r c) {i : ℕ} (hi : i < φ.length) :
    c ≠ Layout.center (φ.distinctVars.length + i) := fun heq =>
  match h with
  | .ordinary hc _ => clause_cell_not_ordinary hi (heq ▸ hc)
  | .crossing hc _ => PlanarCompile.clause_cell_not_mem_crossingSites φ hi (heq ▸ hc)

private theorem translate_local_core_contact {A : Type*} [DecidableEq A]
    (v : Point) (cp : ℕ → Point) (vp : A → Point) {e f : ℕ × A × Route}
    (he : e.2.2.head? = some (cp e.1) ∧ e.2.2.getLast? = some (vp e.2.1))
    (hf : f.2.2.head? = some (cp f.1) ∧ f.2.2.getLast? = some (vp f.2.1))
    {p : ℝ × ℝ}
    (hcontact : ∀ x ∈ support e.2.2, x ∈ support f.2.2 →
      ∃ a ∈ (if e.1 = f.1 then [cp e.1] else []) ++
        (if e.2.1 = f.2.1 then [vp e.2.1] else []), x = realPoint a)
    (hp : p ∈ support (translate v e.2.2)) (hq : p ∈ support (translate v f.2.2)) :
    ∃ a : Point, p = realPoint a ∧ RouteEnd (translate v e.2.2) a ∧
      RouteEnd (translate v f.2.2) a := by
  obtain ⟨a, ha, hxa⟩ := hcontact _ (mem_support_translate_sub hp) (mem_support_translate_sub hq)
  refine ⟨a + v, ?_, ?_⟩
  · rw [realPoint_add, ← hxa, sub_add_cancel]
  · simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton] at ha
    rcases ha with ⟨hc, rfl⟩ | ⟨hv, rfl⟩
    · exact ⟨Or.inl (by simp only [translate, List.head?_map, he.1, Option.map_some]),
        Or.inl (by simp only [translate, List.head?_map, hc ▸ hf.1, Option.map_some])⟩
    · exact ⟨Or.inr (by simp only [translate, List.getLast?_map, he.2, Option.map_some]),
        Or.inr (by simp only [translate, List.getLast?_map, hv ▸ hf.2, Option.map_some])⟩

private theorem corePieces_contact {φ : CNF ℕ} {r s : Route} {c d : Point}
    (hr : CorePiece φ r c) (hs : CorePiece φ s d) (hne : r ≠ s)
    {p : ℝ × ℝ} (hp : p ∈ support r) (hq : p ∈ support s) :
    ∃ a : Point, p = realPoint a ∧ RouteEnd r a ∧ RouteEnd s a := by
  have hcd := cell_eq_of_open (hr.interior hp) (hs.interior hq)
  subst d
  cases hr with
  | ordinary hc he =>
    cases hs with
    | ordinary _ hf =>
      exact translate_local_core_contact _ OrdinaryRing.clausePosition
        OrdinaryRing.variablePosition (OrdinaryRing.incidence_endpoints _ he).2
        (OrdinaryRing.incidence_endpoints _ hf).2
        (fun _ hx hy => OrdinaryRing.routes_contact he hf (fun h => hne (h ▸ rfl)) hx hy) hp hq
    | crossing hd _ => exact (((mem_ordinaryCells φ _).1 hc).2 hd).elim
  | crossing hc he =>
    cases hs with
    | ordinary hd _ => exact (((mem_ordinaryCells φ _).1 hd).2 hc).elim
    | crossing _ hf =>
      exact translate_local_core_contact _ PairedCrossover.clausePosition
        PairedCrossover.variablePosition (PairedCrossover.incidence_endpoints _ he).2
        (PairedCrossover.incidence_endpoints _ hf).2
        (fun _ hx hy => PairedCrossover.routes_contact he hf (fun h => hne (h ▸ rfl)) hx hy) hp hq

private theorem core_spoke_disjoint {φ : CNF ℕ} {r s : Route} {c d : Point} {i : Fin 4}
    (hr : CorePiece φ r c) (hs : SpokePiece φ s d i) :
    Disjoint (support r) (support (translate (cellOrigin 120 d) (PairedPorts.spokeRoute i))) :=
  Set.disjoint_left.mpr fun _ hp hq =>
    let ⟨_, hj, hd⟩ := hs.clause_cell
    hr.not_clause_cell hj ((cell_eq_of_mem_open_closed (by decide) (hr.interior hp)
      (spoke_support_cell d i hq)).trans hd)

private theorem core_access_contact {φ : CNF ℕ} {r s : Route} {c d q : Point} {l : Fin 2}
    (hr : CorePiece φ r c) (hs : AccessPiece φ s d q l) {p : ℝ × ℝ}
    (hp : p ∈ support r) (hq : p ∈ support (access (crossingSites φ) d q l)) :
    ∃ a : Point, p = realPoint a ∧ RouteEnd r a ∧ RouteEnd s a := by
  have hcd := cell_eq_of_mem_open_closed (by decide) (hr.interior hp)
    (access_support_cell (crossingSites φ) d q l hq).1
  subst d
  have hq' : p - realPoint (cellOrigin 120 c) ∈ support (PairedPorts.accessRoute (side c q) l) :=
    mem_support_translate_sub (access_eq_translate (crossingSites φ) c q l ▸ hq)
  have mk {loc : Route} (hlast : loc.getLast? = some (PairedPorts.variablePosition (side c q) l))
      (hxp : p - realPoint (cellOrigin 120 c) =
        realPoint (PairedPorts.variablePosition (side c q) l)) :
      ∃ a : Point, p = realPoint a ∧
        RouteEnd (translate (cellOrigin 120 c) loc) a ∧ RouteEnd s a :=
    ⟨cellOrigin 120 c + PairedPorts.variablePosition (side c q) l,
      by rw [← sub_add_cancel p (realPoint (cellOrigin 120 c)), hxp, realPoint_add, add_comm],
      Or.inr (by simp only [translate, List.getLast?_map, hlast, Option.map_some, add_comm]),
      Or.inr (by rw [hs.inner_endpoint, signal_position])⟩
  cases hr with
  | ordinary _ he =>
    obtain ⟨hevar, hxp⟩ := OrdinaryRing.access_contact he hq' (mem_support_translate_sub hp)
    exact mk (by simpa only [hevar, OrdinaryRing.variablePosition] using
      (OrdinaryRing.incidence_endpoints _ he).2.2) hxp
  | crossing _ he =>
    obtain ⟨hevar, hxp⟩ := PairedCrossover.access_contact he hq' (mem_support_translate_sub hp)
    exact mk (by simpa only [hevar, PairedCrossover.terminal,
      PairedCrossover.variablePosition] using (PairedCrossover.incidence_endpoints _ he).2.2) hxp

private theorem route_support_cases {φ : CNF ℕ} {r : Route} (hr : r ∈ routes φ)
    {p : ℝ × ℝ} (hp : p ∈ support r) :
    (∃ c, CorePiece φ r c) ∨
      (∃ c q l, AccessPiece φ r c q l ∧ p ∈ support (access (crossingSites φ) c q l)) ∨
        ∃ c s, SpokePiece φ r c s ∧
          p ∈ support (translate (cellOrigin 120 c) (PairedPorts.spokeRoute s)) := by
  obtain ⟨pc, hpc, hr⟩ := List.mem_flatMap.mp hr
  rcases mem_placedClauses.mp hpc with hpc | ⟨c, hc, hpc⟩ | ⟨c, hc, hpc⟩ | ⟨o, ho, _, he, hpc⟩
  · obtain ⟨_, _, _, ho, rfl⟩ := (exists_occurrence_of_mem_originalClauses hpc).2 _ hr
    rw [support_lastLiteral _ _ _ (PlanarCompile.occurrencePath_last_unit ho)] at hp
    rcases hp with hp | hp
    · exact Or.inr (Or.inr ⟨_, _, SpokePiece.final ho, hp⟩)
    · exact Or.inr (Or.inl ⟨_, _, _, AccessPiece.final ho, hp⟩)
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨_, he, rfl⟩ := List.mem_map.mp hr
    exact Or.inl ⟨c, CorePiece.ordinary hc (List.mem_filter.mp he).1⟩
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨_, he, rfl⟩ := List.mem_map.mp hr
    exact Or.inl ⟨c, CorePiece.crossing hc (List.mem_filter.mp he).1⟩
  · rcases hpc with rfl | rfl <;> rcases link_routes_cases _ _ _ _ hr with rfl | rfl <;>
      first
      | exact Or.inr (Or.inl ⟨_, _, _, AccessPiece.link ho he _, hp⟩)
      | exact Or.inr (Or.inl ⟨_, _, _, AccessPiece.reverseLink ho he _, hp⟩)

/-- Distinct actual route values meet only at endpoints of both routes, over the complete
real plane. Unit-step ownership includes the omitted final binary link. -/
theorem route_contacts {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {r s : Route} (hr : r ∈ routes φ) (hs : s ∈ routes φ) (hne : r ≠ s)
    {p : ℝ × ℝ} (hp : p ∈ support r) (hq : p ∈ support s) :
    ∃ a : Point, p = realPoint a ∧
      (r.head? = some a ∨ r.getLast? = some a) ∧
      (s.head? = some a ∨ s.getLast? = some a) := by
  rcases route_support_cases hr hp with ⟨c, hr'⟩ | ⟨c, q, l, hr', hp'⟩ | ⟨c, i, hr', hp'⟩ <;>
    rcases route_support_cases hs hq with ⟨d, hs'⟩ | ⟨d, t, k, hs', hq'⟩ | ⟨d, j, hs', hq'⟩
  · exact corePieces_contact hr' hs' hne hp hq
  · exact core_access_contact hr' hs' hp hq'
  · exact (Set.disjoint_left.mp (core_spoke_disjoint hr' hs') hp hq').elim
  · obtain ⟨a, ha, hsEnd, hrEnd⟩ := core_access_contact hs' hr' hq hp'
    exact ⟨a, ha, hrEnd, hsEnd⟩
  · exact accessPieces_contact hw hv hr' hs' hne hp' hq'
  · exact (Set.disjoint_left.mp (spoke_access_disjoint hw hv hs' hr' hne.symm) hq' hp').elim
  · exact (Set.disjoint_left.mp (core_spoke_disjoint hs' hr') hq hp').elim
  · exact (Set.disjoint_left.mp (spoke_access_disjoint hw hv hr' hs' hne) hp' hq').elim
  · exact spokePieces_contact hw hv hr' hs' hne hp' hq'

/-! ### Route uniqueness, vertex avoidance, and drawing certificate -/

private theorem ordinary_routes_nodup_check : ∀ i : Fin 8,
    ((OrdinaryRing.incidenceRoutes.filter fun e => e.1 == i.val).map fun e => e.2.2).Nodup := by
  decide +kernel

private theorem crossing_routes_nodup_check (i : Fin 78) :
    ((PairedCrossover.incidenceRoutes.filter fun e => e.1 == i.val).map fun e => e.2.2).Nodup :=
  have h : ((List.range 78).all fun j =>
    decide (((PairedCrossover.incidenceRoutes.filter fun e => e.1 == j).map
      fun e => e.2.2).Nodup)) = true := by decide +kernel
  of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

private theorem placedClause_routes_nodup {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {pc : PlacedClause} (hpc : pc ∈ placedClauses φ) : pc.2.2.Nodup := by
  rcases mem_placedClauses.mp hpc with hpc | ⟨_, _, hpc⟩ | ⟨_, _, hpc⟩ | ⟨o, ho, e, he, hpc⟩
  · obtain ⟨⟨_, i⟩, hci, rfl⟩ := List.mem_map.mp hpc
    dsimp only; rw [List.map_map]
    refine (List.Nodup.of_map Prod.snd (by
      rw [List.zipIdx_map_snd]; exact List.nodup_range' _)).map_on fun lj hlj mk hmk heq => ?_
    have ho := mk_mem_occurrences_of_mem_zipIdx hci hlj
    have ht := mk_mem_occurrences_of_mem_zipIdx hci hmk
    have hb := congrArg (fun r : Route => r.getD 2 (0, 0)) heq
    simp only [Function.comp_def, lastLiteral, List.getD_cons_succ, List.getD_cons_zero] at hb
    have stepBdy {o : Occurrence ℕ} (h : o ∈ Cslib.Logic.PL.occurrences φ) :=
      shared_boundary (PlanarCompile.occurrencePath_last_unit h) (PairedPorts.spokeLane
        (side (lastStep (occurrencePath φ o)).2 (lastStep (occurrencePath φ o)).1))
    have hot := (boundary_occurrence_step_unique hw hv ho ht (lastStep_mem ho) (lastStep_mem ht)
      ((stepBdy ho).trans (hb.trans (stepBdy ht).symm))).2.1
    have hjl := Occurrence.mk.inj hot
    exact Prod.ext hjl.2.2 hjl.2.1
  · exact ordTile.routes_nodup OrdinaryRing.formula_sizes.1 ordinary_routes_nodup_check hpc
  · exact crossTile.routes_nodup PairedCrossover.length_formula crossing_routes_nodup_check hpc
  · have hne (l : Fin 2) :
        access (crossingSites φ) e.1 e.2 l ≠ access (crossingSites φ) e.2 e.1 l := fun heq => by
      have hvar := Option.some.inj (congrArg List.getLast? heq)
      have he12 : e.1 = e.2 := cell_eq_of_open
        (variablePosition_mem_openCell (signal (crossingSites φ) e.1 e.2 l))
        (congrArg realPoint hvar ▸
          variablePosition_mem_openCell (signal (crossingSites φ) e.2 e.1 l))
      have hunit := PlanarCompile.occurrencePath_unit ho (prefixStep_mem he)
      simp [he12, Orthogonal.length] at hunit
    rcases hpc with rfl | rfl <;> simp [link, hne, Ne.symm (hne _)]

/-- Distinct actual incidence occurrences have distinct polygonal route lists. -/
theorem routes_nodup {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) : (routes φ).Nodup := by
  refine List.nodup_flatMap.mpr ⟨fun _ hpc => placedClause_routes_nodup hw hv hpc, ?_⟩
  apply (List.pairwise_map.mp (clausePositions_nodup hw hv)).imp_of_mem
  intro pc pd hpc hpd hpos r hr hs
  exact hpos (Option.some.inj
    ((placedClause_route_endpoints φ hpc hr).choose_spec.2.1.symm.trans
      (placedClause_route_endpoints φ hpd hs).choose_spec.2.1))

/-- Every actual route meets an actual clause vertex only at its own clause endpoint.
The original-clause case includes isolated empty clauses. -/
theorem route_clause_contact {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {r : Route} (hr : r ∈ routes φ) {pc : PlacedClause} (hpc : pc ∈ placedClauses φ)
    (hp : realPoint pc.2.1 ∈ support r) : r.head? = some pc.2.1 := by
  rcases placedClause_nonempty_or_original hpc with hne | horiginal
  · obtain ⟨s, hs, hshead⟩ := placedClause_exists_route hpc hne
    by_cases hrs : r = s
    · exact hrs ▸ hshead
    · obtain ⟨a, hpa, hrEnd, _⟩ :=
        route_contacts hw hv hr hs hrs hp (realPoint_mem_support_of_head? hshead)
      rw [← realPoint_injective hpa] at hrEnd
      rcases hrEnd with hhead | hlast
      · exact hhead
      · obtain ⟨pd, hpd, hrm⟩ := List.mem_flatMap.mp hr
        obtain ⟨v, hv', -, hrLast⟩ := placedClause_route_endpoints φ hpd hrm
        exact (variable_clause_positions_disjoint φ
          (List.mem_map_of_mem (CNF.mem_distinctVars.mpr hv'))
          ((Option.some.inj (hrLast.symm.trans hlast)) ▸ List.mem_map_of_mem hpc)).elim
  · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp horiginal
    have hi : ci.2 < φ.length := by simpa only [Nat.zero_add] using (List.mem_zipIdx hci).2.1
    have hcenter := center_mem_openCell (r := 120) (by decide)
      (Layout.center (φ.distinctVars.length + ci.2))
    rcases route_support_cases hr hp with ⟨_, hcore⟩ | ⟨c, q, l, haccess, hp⟩ | ⟨c, s, hspoke, hp⟩
    · exact (hcore.not_clause_cell hi (cell_eq_of_open hcenter (hcore.interior hp)).symm).elim
    · exact (haccess.not_clause_cell hi (cell_eq_of_mem_open_closed (by decide) hcenter
        (access_support_cell (crossingSites φ) c q l hp).1).symm).elim
    · have hcell := cell_eq_of_mem_open_closed (by decide) hcenter (spoke_support_cell c s hp)
      cases hspoke
      exact congrArg (fun x => some (center x)) hcell.symm

private theorem drawingPosition_eq_getD {φ : CNF ℕ} {v : ℕ}
    (hv : v ∈ (SAT.incidenceGraph (formula φ)).1) :
    Graph.drawingPosition (SAT.incidenceGraph (formula φ)) (positions φ, routes φ) v =
      (positions φ).getD v (0, 0) := by
  simp only [Graph.drawingPosition, SAT.incidenceGraph]
  rw [List.idxOf_range_of_lt (by simpa only [SAT.incidenceGraph, List.mem_range] using hv)]

private theorem drawingPosition_injective {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {a b : ℕ} (ha : a ∈ (SAT.incidenceGraph (formula φ)).1)
    (hb : b ∈ (SAT.incidenceGraph (formula φ)).1)
    (heq : Graph.drawingPosition (SAT.incidenceGraph (formula φ)) (positions φ, routes φ) a =
      Graph.drawingPosition (SAT.incidenceGraph (formula φ)) (positions φ, routes φ) b) :
    a = b := by
  have hlt {x} (hx : x ∈ (SAT.incidenceGraph (formula φ)).1) : x < (positions φ).length := by
    rw [positions_length]
    simpa only [SAT.incidenceGraph, List.mem_range, List.length_range] using hx
  rw [drawingPosition_eq_getD ha, drawingPosition_eq_getD hb,
    List.getD_eq_getElem _ _ (hlt ha), List.getD_eq_getElem _ _ (hlt hb)] at heq
  exact (positions_nodup hw hv).eq_of_getElem_eq (hlt ha) (hlt hb) heq

private theorem indexed_route_mem {φ : CNF ℕ} {i : ℕ}
    (hi : i < (SAT.incidenceGraph (formula φ)).2.length) :
    (routes φ).getD i [] ∈ routes φ :=
  List.getD_mem [] (by rwa [routes_length])

/-- Actual indexed routes avoid all nonincident declared graph vertices. -/
theorem routes_avoid_vertices {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {i : ℕ} (hi : i < (SAT.incidenceGraph (formula φ)).2.length)
    {v : ℕ} (hvertex : v ∈ (SAT.incidenceGraph (formula φ)).1)
    (hp : realPoint (Graph.drawingPosition (SAT.incidenceGraph (formula φ))
      (positions φ, routes φ) v) ∈ support ((routes φ).getD i [])) :
    v = (SAT.incidenceGraph (formula φ)).2[i].1 ∨
      v = (SAT.incidenceGraph (formula φ)).2[i].2 := by
  have hend := routes_endpoints φ hi
  have hdecl := SAT.incidenceGraph_endpoints (List.getElem_mem hi)
  have hlt : v < (positions φ).length := by
    rw [positions_length]
    simpa only [SAT.incidenceGraph, List.mem_range, List.length_range] using hvertex
  have hmem : Graph.drawingPosition (SAT.incidenceGraph (formula φ)) (positions φ, routes φ) v ∈
      positions φ := drawingPosition_eq_getD hvertex ▸ List.getD_mem (0, 0) hlt
  simp only [positions, List.mem_append, List.mem_map] at hmem
  rcases hmem with ⟨_, hwmem, heq⟩ | ⟨_, hpc, heq⟩
  · exact Or.inl (drawingPosition_injective hw hv hvertex hdecl.1 (heq.symm.trans (Option.some.inj
      ((route_variable_contact φ (indexed_route_mem hi) (CNF.mem_distinctVars.mp hwmem)
        (heq ▸ hp)).symm.trans hend.2))))
  · exact Or.inr (drawingPosition_injective hw hv hvertex hdecl.2 (heq.symm.trans (Option.some.inj
      ((route_clause_contact hw hv (indexed_route_mem hi) hpc
        (heq ▸ hp)).symm.trans hend.1))))

/-- Actual indexed incidence routes meet only at their shared declared graph endpoints. -/
theorem routes_contacts {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {i : ℕ} (hi : i < (SAT.incidenceGraph (formula φ)).2.length)
    {j : ℕ} (hj : j < (SAT.incidenceGraph (formula φ)).2.length) (hij : i ≠ j)
    {p : ℝ × ℝ} (hp : p ∈ support ((routes φ).getD i []))
    (hq : p ∈ support ((routes φ).getD j [])) :
    ∃ v ∈ (SAT.incidenceGraph (formula φ)).1,
      (v = (SAT.incidenceGraph (formula φ)).2[i].1 ∨
        v = (SAT.incidenceGraph (formula φ)).2[i].2) ∧
      (v = (SAT.incidenceGraph (formula φ)).2[j].1 ∨
        v = (SAT.incidenceGraph (formula φ)).2[j].2) ∧
      p = realPoint (Graph.drawingPosition (SAT.incidenceGraph (formula φ))
        (positions φ, routes φ) v) := by
  have hir : i < (routes φ).length := by rwa [routes_length]
  have hjr : j < (routes φ).length := by rwa [routes_length]
  have hne : (routes φ).getD i [] ≠ (routes φ).getD j [] := by
    rw [List.getD_eq_getElem _ _ hir, List.getD_eq_getElem _ _ hjr]
    exact fun h => hij ((routes_nodup hw hv).eq_of_getElem_eq hir hjr h)
  have end_decl {k : ℕ} (hk : k < (SAT.incidenceGraph (formula φ)).2.length) {a : Point}
      (ha : RouteEnd ((routes φ).getD k []) a) :
      ∃ v ∈ (SAT.incidenceGraph (formula φ)).1,
        (v = (SAT.incidenceGraph (formula φ)).2[k].1 ∨
          v = (SAT.incidenceGraph (formula φ)).2[k].2) ∧
        a = Graph.drawingPosition (SAT.incidenceGraph (formula φ)) (positions φ, routes φ) v := by
    rcases ha with ha | ha
    · exact ⟨_, (SAT.incidenceGraph_endpoints (List.getElem_mem hk)).2, Or.inr rfl,
        Option.some.inj (ha.symm.trans (routes_endpoints φ hk).1)⟩
    · exact ⟨_, (SAT.incidenceGraph_endpoints (List.getElem_mem hk)).1, Or.inl rfl,
        Option.some.inj (ha.symm.trans (routes_endpoints φ hk).2)⟩
  obtain ⟨a, hpa, ha, hb⟩ := route_contacts hw hv
    (indexed_route_mem hi) (indexed_route_mem hj) hne hp hq
  obtain ⟨v, hv', hvi, hav⟩ := end_decl hi ha
  obtain ⟨w, hw', hwj, haw⟩ := end_decl hj hb
  have heq := drawingPosition_injective hw hv hv' hw' (hav.symm.trans haw)
  exact ⟨v, hv', hvi, heq ▸ hwj, hpa.trans (congrArg realPoint hav)⟩

/-- The actual paired-port compiler supplies a continuous planar orthogonal drawing.
The only assumptions are source width and literal-occurrence bounds of three. -/
theorem isPlanarOrthogonalDrawing {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph (formula φ)) (positions φ, routes φ) where
  vertexCount := positions_length φ
  edgeCount := routes_length φ
  labelsNodup := List.nodup_range
  positionsNodup := positions_nodup hw hv
  endpointsDeclared := fun _ => SAT.incidenceGraph_endpoints
  loopless := fun _ => SAT.incidenceGraph_loopless
  endpoints := fun _ hi => Or.inr (routes_endpoints φ hi)
  orthogonal := fun _ hi => (routes_regular φ _ (indexed_route_mem hi)).1
  simple := fun _ hi => (routes_regular φ _ (indexed_route_mem hi)).2
  avoidsVertices := fun _ hi _ hvertex => routes_avoid_vertices hw hv hi hvertex
  contacts := fun _ hi _ hj hij _ hp hq => routes_contacts hw hv hi hj hij hp hq

end Cslib.Complexity.SAT.ParsimoniousPlanar
