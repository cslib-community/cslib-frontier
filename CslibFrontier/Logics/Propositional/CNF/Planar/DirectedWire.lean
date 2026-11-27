/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.ModelCount
public import Mathlib.Data.List.Defs
import CslibFrontier.Logics.Propositional.CNF.Vars
import Mathlib.Data.List.Basic
import Mathlib.Data.Bool.Basic

/-!
# Directed wires for CNF substitution

A wire lists pairs of cell entry and exit variables, from its source to its clause. Local
constraints must equate the two values in each cell. One binary implication joins each exit
to the next entry. Positive literals direct that implication backwards; negative literals
direct it forwards. In either case, a true literal at the final exit implies the source literal.
Constant values satisfy every link.

These are conditional composition rules. They construct no layout and do not establish that
any particular generator satisfies the local equalities or endpoint conditions.

## Main definitions

* `Cslib.Logic.PL.CNF.DirectedWire.links`: one directed binary clause per cell gap.
* `Cslib.Logic.PL.CNF.DirectedWire.assemble`: endpoint clauses and links for indexed occurrences.

## Main results

* `Cslib.Logic.PL.CNF.DirectedWire.propagate`: literal truth propagates from final exit to entry.
* `Cslib.Logic.PL.CNF.DirectedWire.eval_links_of_constant`: constant signals satisfy the links.
* `Cslib.Logic.PL.CNF.DirectedWire.length_links`: exact clause count, including empty wires.
* `Cslib.Logic.PL.CNF.DirectedWire.eval_assemble_sound`: projection under local constraints.
* `Cslib.Logic.PL.CNF.DirectedWire.eval_assemble_complete`: compatibility-based completeness.
* `Cslib.Logic.PL.CNF.DirectedWire.length_assemble`,
  `Cslib.Logic.PL.CNF.DirectedWire.length_vars_assemble`: exact total resource counts.

## References

The polarity-directed composition and cell-pair construction are original.
-/

public section

namespace Cslib.Logic.PL.CNF.DirectedWire

variable {V W : Type*}

/-- A positive literal propagates truth backwards; a negative literal propagates falsity
backwards by a forward implication. This reuses the ordinary implication-clause constructor. -/
@[expose] def link (b : Bool) (previous next : V) : Clause V :=
  if b then Clause.imp [next] previous else Clause.imp [previous] next

/-- One binary implication between each consecutive pair of cells, using its exit and entry. -/
@[expose] def links (b : Bool) (cells : List (V × V)) : CNF V :=
  cells.consecutivePairs.map fun (prev, next) => link b prev.2 next.1

/-- A link enforces exactly the direction needed for its literal's truth. -/
theorem eval_link_iff (σ : V → Bool) (b : Bool) (previous next : V) :
    (link b previous next).eval σ = true ↔ (σ next = b → σ previous = b) := by
  grind [link, Clause.eval_imp]

/-- All links hold exactly when literal truth propagates across every gap. -/
theorem eval_links_iff (σ : V → Bool) (b : Bool) (cells : List (V × V)) :
    (links b cells).eval σ = true ↔
      ∀ prev next, (prev, next) ∈ cells.consecutivePairs → σ next.1 = b → σ prev.2 = b := by
  simp only [links, eval_map_eq_true_iff, Prod.forall, eval_link_iff]

/-- Empty and singleton cell lists have no intercell clauses. -/
@[simp] theorem links_nil (b : Bool) : links b ([] : List (V × V)) = [] := rfl

/-- A single cell needs only its own local equality, with no additional wire clauses. -/
@[simp] theorem links_singleton (b : Bool) (cell : V × V) : links b [cell] = [] := rfl

/-- Splitting off the first gap leaves the links of the nonempty tail. -/
theorem links_cons_cons (b : Bool) (first next : V × V) (rest : List (V × V)) :
    links b (first :: next :: rest) = link b first.2 next.1 :: links b (next :: rest) := rfl

/-- Given local entry/exit equality in each cell, final literal truth implies initial truth. -/
theorem propagate (σ : V → Bool) (b : Bool) (first : V × V) (rest : List (V × V))
    (hcells : ∀ c ∈ first :: rest, σ c.1 = σ c.2)
    (hlinks : (links b (first :: rest)).eval σ = true)
    (hlast : σ ((first :: rest).getLastD first).2 = b) : σ first.1 = b := by
  induction rest generalizing first with
  | nil => exact (hcells first List.mem_cons_self).trans hlast
  | cons next rest ih =>
    rw [links_cons_cons, eval_cons, Bool.and_eq_true] at hlinks
    exact (hcells first List.mem_cons_self).trans ((eval_link_iff σ b _ _).1 hlinks.1
      (ih next (fun c hc => hcells c (List.mem_cons_of_mem _ hc)) hlinks.2
        (by simpa only [List.getLastD_cons] using hlast)))

/-- The propagation rule for a possibly empty list, with nonemptiness stated explicitly.
The fallback only makes the endpoint expressions total; it is unused under this hypothesis. -/
theorem propagate_of_ne_nil (σ : V → Bool) (b : Bool) (fallback : V)
    (cells : List (V × V)) (hne : cells ≠ [])
    (hcells : ∀ c ∈ cells, σ c.1 = σ c.2)
    (hlinks : (links b cells).eval σ = true)
    (hlast : σ (cells.getLastD (fallback, fallback)).2 = b) :
    σ (cells.headD (fallback, fallback)).1 = b := by
  cases cells with
  | nil => exact False.elim (hne rfl)
  | cons first rest =>
    apply propagate σ b first rest hcells hlinks
    simpa only [List.getLastD_cons] using hlast

/-- Assigning a common value to all entries and exits satisfies every directed link. -/
theorem eval_links_of_constant (σ : V → Bool) (b value : Bool) (cells : List (V × V))
    (h : ∀ c ∈ cells, σ c.1 = value ∧ σ c.2 = value) :
    (links b cells).eval σ = true := by
  apply (eval_links_iff σ b cells).2
  intro prev next hp hn
  have hm := List.of_mem_zip hp
  rw [(h prev hm.1).2, ← (h next (List.mem_of_mem_tail hm.2)).1]
  exact hn

/-- There is exactly one clause per consecutive gap. -/
theorem length_links_eq_gaps (b : Bool) (cells : List (V × V)) :
    (links b cells).length = cells.consecutivePairs.length := List.length_map _

/-- A nonempty wire has one fewer link than cells; an empty wire has zero links. -/
theorem length_links (b : Bool) (cells : List (V × V)) :
    (links b cells).length = cells.length - 1 := by
  simp [links, List.consecutivePairs]

/-- Every directed link has exactly two literals, even if its endpoints coincide. -/
theorem length_link (b : Bool) (previous next : V) : (link b previous next).length = 2 := by
  cases b <;> rfl

/-- Every clause of the wire is binary. -/
theorem length_of_mem_links (b : Bool) (cells : List (V × V)) {c : Clause V}
    (hc : c ∈ links b cells) : c.length = 2 := by
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hc
  exact length_link b _ _

/-- There are exactly two literal occurrences per gap, with multiplicities retained. -/
theorem length_vars_links (b : Bool) (cells : List (V × V)) :
    (links b cells).vars.length = 2 * (cells.length - 1) := by
  rw [CNF.length_vars, links, List.map_map]
  simp only [Function.comp_def, length_link]
  simp [List.consecutivePairs, Nat.mul_comm]

/-- Replace each original literal by the final exit variable on its occurrence's wire,
retaining its polarity and its clause/literal position. -/
@[expose] def replacementClauses (φ : CNF V) (wire : Occurrence V → List (W × W))
    (fallback : W) : CNF W :=
  φ.zipIdx.map fun (clause, ci) => clause.zipIdx.map fun (lit, li) =>
    (((wire ⟨ci, li, lit⟩).getLastD (fallback, fallback)).2, lit.2)

/-- The directed-link clauses for every original literal occurrence, including duplicates. -/
@[expose] def allLinks (φ : CNF V) (wire : Occurrence V → List (W × W)) : CNF W :=
  (Cslib.Logic.PL.occurrences φ).flatMap fun o => links o.lit.2 (wire o)

/-- Original clauses at their wire endpoints, followed by all directed links.
Local cell constraints, such as crossover formulas, are supplied separately by the caller. -/
@[expose] def assemble (φ : CNF V) (wire : Occurrence V → List (W × W)) (fallback : W) : CNF W :=
  replacementClauses φ wire fallback ++ allLinks φ wire

/-- Evaluation of the replacement clauses, indexed by the original clause and literal positions. -/
theorem eval_replacementClauses_iff (φ : CNF V) (wire : Occurrence V → List (W × W))
    (fallback : W) (σ : W → Bool) :
    (replacementClauses φ wire fallback).eval σ = true ↔
      ∀ clause ci, (clause, ci) ∈ φ.zipIdx → ∃ lit li, (lit, li) ∈ clause.zipIdx ∧
        σ ((wire ⟨ci, li, lit⟩).getLastD (fallback, fallback)).2 = lit.2 := by
  rw [replacementClauses, eval_map_eq_true_iff, Prod.forall]
  refine forall₂_congr fun clause _ => forall_congr' fun _ => ?_
  rw [Clause.eval_eq_true_iff]
  constructor
  · rintro ⟨_, hm, ht⟩
    obtain ⟨⟨lit, li⟩, hl, rfl⟩ := List.mem_map.mp hm
    exact ⟨lit, li, hl, ht⟩
  · rintro ⟨lit, li, hl, ht⟩
    exact ⟨_, List.mem_map.mpr ⟨(lit, li), hl, rfl⟩, ht⟩

/-- The global link block holds exactly when every occurrence's wire links hold. -/
theorem eval_allLinks_iff (φ : CNF V) (wire : Occurrence V → List (W × W)) (σ : W → Bool) :
    (allLinks φ wire).eval σ = true ↔
      ∀ o ∈ Cslib.Logic.PL.occurrences φ, (links o.lit.2 (wire o)).eval σ = true :=
  eval_flatMap_eq_true_iff σ _ _

/-- Satisfaction projects back to the ordinary source formula when the caller proves local
cell equality and agreement between the first entries and source variable values. -/
theorem eval_assemble_sound (φ : CNF V) (wire : Occurrence V → List (W × W))
    (fallback : W) (τ : V → Bool) (σ : W → Bool)
    (hne : ∀ o ∈ Cslib.Logic.PL.occurrences φ, wire o ≠ [])
    (hcells : ∀ o ∈ Cslib.Logic.PL.occurrences φ, ∀ c ∈ wire o, σ c.1 = σ c.2)
    (hfirst : ∀ o ∈ Cslib.Logic.PL.occurrences φ,
      σ ((wire o).headD (fallback, fallback)).1 = τ o.lit.1)
    (h : (assemble φ wire fallback).eval σ = true) : φ.eval τ = true := by
  rw [assemble, eval_append, Bool.and_eq_true, eval_replacementClauses_iff, eval_allLinks_iff] at h
  rw [← List.zipIdx_map_fst 0 φ, eval_map_eq_true_iff, Prod.forall]
  intro clause ci hc
  obtain ⟨lit, li, hl, hv⟩ := h.1 clause ci hc
  have ho := mk_mem_occurrences_of_mem_zipIdx hc hl
  exact (Clause.eval_eq_true_iff τ clause).2 ⟨lit, List.fst_mem_of_mem_zipIdx hl,
    (hfirst _ ho).symm.trans (propagate_of_ne_nil σ lit.2 fallback _ (hne _ ho) (hcells _ ho)
      (h.2 _ ho) hv)⟩

/-- A source satisfying assignment extends through the link assembly whenever the caller
supplies one compatible target assignment constant along each occurrence's nonempty wire.
This is an assignment-level conditional result, not an existence theorem for such a target. -/
theorem eval_assemble_complete (φ : CNF V) (wire : Occurrence V → List (W × W))
    (fallback : W) (τ : V → Bool) (σ : W → Bool)
    (hne : ∀ o ∈ Cslib.Logic.PL.occurrences φ, wire o ≠ [])
    (hcompat : ∀ o ∈ Cslib.Logic.PL.occurrences φ, ∀ c ∈ wire o,
      σ c.1 = τ o.lit.1 ∧ σ c.2 = τ o.lit.1)
    (h : φ.eval τ = true) : (assemble φ wire fallback).eval σ = true := by
  rw [assemble, eval_append, Bool.and_eq_true]
  constructor
  · apply (eval_replacementClauses_iff φ wire fallback σ).2
    intro clause ci hc
    have hclause := (eval_eq_true_iff τ φ).1 h clause (List.fst_mem_of_mem_zipIdx hc)
    obtain ⟨lit, hl, hv⟩ := (Clause.eval_eq_true_iff τ clause).1 hclause
    rw [← List.zipIdx_map_fst 0 clause] at hl
    obtain ⟨⟨lit, li⟩, hli, rfl⟩ := List.mem_map.mp hl
    refine ⟨lit, li, hli, ?_⟩
    have ho := mk_mem_occurrences_of_mem_zipIdx hc hli
    have hm : (wire ⟨ci, li, lit⟩).getLastD (fallback, fallback) ∈
        wire ⟨ci, li, lit⟩ := by
      cases hw : wire ⟨ci, li, lit⟩ with
      | nil => exact False.elim (hne _ ho hw)
      | cons a rest =>
        rw [List.getLastD_cons]
        exact List.getLastD_mem_cons
    exact (hcompat _ ho _ hm).2.trans hv
  · apply (eval_allLinks_iff φ wire σ).2
    intro o ho
    exact eval_links_of_constant σ o.lit.2 (τ o.lit.1) (wire o) (hcompat o ho)

/-- Clause replacement preserves all original clause widths. -/
theorem map_length_replacementClauses (φ : CNF V) (wire : Occurrence V → List (W × W))
    (fallback : W) : (replacementClauses φ wire fallback).map List.length = φ.map List.length := by
  conv_rhs => rw [← List.zipIdx_map_fst 0 φ, List.map_map]
  simp only [replacementClauses, List.map_map, Function.comp_def, List.length_map,
    List.length_zipIdx]

/-- The link block has one clause per gap of each occurrence's wire. -/
theorem length_allLinks (φ : CNF V) (wire : Occurrence V → List (W × W)) :
    (allLinks φ wire).length =
      ((Cslib.Logic.PL.occurrences φ).map fun o => (wire o).length - 1).sum := by
  simp [allLinks, List.length_flatMap, length_links]

/-- Exact total clause count: original clauses plus all intercell gaps. -/
theorem length_assemble (φ : CNF V) (wire : Occurrence V → List (W × W)) (fallback : W) :
    (assemble φ wire fallback).length = φ.length +
      ((Cslib.Logic.PL.occurrences φ).map fun o => (wire o).length - 1).sum := by
  simp [assemble, replacementClauses, length_allLinks]

/-- Endpoint replacement preserves the number of source literal occurrences. -/
theorem length_vars_replacementClauses (φ : CNF V) (wire : Occurrence V → List (W × W))
    (fallback : W) : (replacementClauses φ wire fallback).vars.length = φ.vars.length := by
  rw [CNF.length_vars, map_length_replacementClauses, ← CNF.length_vars]

/-- The global link block contributes exactly two literals per gap. -/
theorem length_vars_allLinks (φ : CNF V) (wire : Occurrence V → List (W × W)) :
    (allLinks φ wire).vars.length =
      2 * ((Cslib.Logic.PL.occurrences φ).map fun o => (wire o).length - 1).sum := by
  have total (os : List (Occurrence V)) :
      (CNF.vars (os.flatMap fun o => links o.lit.2 (wire o))).length =
        2 * (os.map fun o => (wire o).length - 1).sum := by
    induction os with
    | nil => rfl
    | cons _ _ ih =>
      simp only [List.flatMap_cons, CNF.vars_append, List.length_append, length_vars_links, ih,
        List.map_cons, List.sum_cons, Nat.mul_add]
  exact total _

/-- Exact total literal count, with no distinctness assumptions on signal variables. -/
theorem length_vars_assemble (φ : CNF V) (wire : Occurrence V → List (W × W)) (fallback : W) :
    (assemble φ wire fallback).vars.length = φ.vars.length +
      2 * ((Cslib.Logic.PL.occurrences φ).map fun o => (wire o).length - 1).sum := by
  rw [assemble, CNF.vars_append, List.length_append, length_vars_replacementClauses,
    length_vars_allLinks]

/-- Source clause widths are preserved and every added clause is binary. -/
theorem width_assemble (φ : CNF V) (wire : Occurrence V → List (W × W)) (fallback : W)
    {k : ℕ} (hwidth : ∀ c ∈ φ, c.length ≤ k) :
    ∀ c ∈ assemble φ wire fallback, c.length ≤ max k 2 := by
  intro c hc
  change c ∈ replacementClauses φ wire fallback ++ allLinks φ wire at hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨⟨clause, ci⟩, hd, rfl⟩ := List.mem_map.mp hc
    have h := hwidth clause (List.fst_mem_of_mem_zipIdx hd)
    calc
      _ = clause.length := by simp only [List.length_map, List.length_zipIdx]
      _ ≤ k := h
      _ ≤ max k 2 := Nat.le_max_left _ _
  · obtain ⟨o, _, hc⟩ := List.mem_flatMap.mp hc
    rw [length_of_mem_links _ _ hc]
    exact Nat.le_max_right _ _

end Cslib.Logic.PL.CNF.DirectedWire
