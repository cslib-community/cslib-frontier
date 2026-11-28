/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.OneInThreeSAT
public import CslibFrontier.Computability.Complexity.Problems.CSP.Incidence
public import CslibFrontier.Logics.Propositional.CSP.Boolean
public import CslibFrontier.Foundations.Data.BitString.DeltaMatroid.Composition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Mathlib.Tactic.FinCases

/-!
# Positive exact-one formulas as OneHot3 constraint instances

The single-symbol language uses the existing constraint records and list semantics. Dropping
the positive polarity tag preserves the actual incidence graph, including indexed parallel
occurrences, repeated clauses and nullaries. Under ternary source scopes the relation is
exactly `BitString.oneHotRelation (Fin 3)`; all permutations of its scope preserve semantics.

This is original representation transport for the supplied-drawing positive exact-three
base problem. It makes no NP-hardness assertion and does not supply a rotation certificate.
-/

public section

namespace Cslib.Complexity.CSP.OneHot3

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.BitString Turing.MultiTapeTM

/-- The single source relation has exactly three ordered argument positions. -/
@[expose] def arity (_ : Unit) : ℕ := 3

/-- Exactly one supplied Boolean argument is true. Exact width is checked by `WellFormed`;
this total semantics also gives a defined answer to every raw scope length. -/
@[expose] def sem (_ : Unit) (bits : List Bool) : Bool := bits.count true == 1

/-- Drop the positive literal tags, retaining every constraint and argument position. -/
@[expose] def ofCNF (φ : CNF ℕ) : CSP Unit ℕ :=
  φ.map fun clause => ⟨(), clause.map Prod.fst⟩

/-- At its declared arity the source relation is the actual existing one-hot relation. -/
theorem booleanRelation_eq : booleanRelation arity sem () = oneHotRelation (Fin 3) := by
  apply Set.ext
  change ∀ a : Fin 3 → Bool, ((List.ofFn a).count true == 1) = true ↔
    ∃ i : Fin 3, (fun j => decide (j = i)) = a
  decide +kernel

/-- The symmetric source relation permits clockwise reordering of its actual scope. -/
theorem sem_eq_of_perm (a b : List Bool) (h : a.Perm b) : sem () a = sem () b := by
  unfold sem
  rw [h.count_eq]

/-- Positive formulas recover exactly their original CNF syntax through the existing
CSP incidence adapter; no renumbering or deduplication of occurrences occurs. -/
theorem varCNF_ofCNF (φ : CNF ℕ) (hp : OneSAT.positiveCheck φ = true) :
    (ofCNF φ).varCNF = φ := by
  have hpos := (OneSAT.positiveCheck_iff φ).mp hp
  simp only [ofCNF, Cslib.Logic.PL.CSP.varCNF, List.map_map, Function.comp_def]
  refine (List.map_congr_left (g := id) fun c hc => ?_).trans (List.map_id φ)
  exact (List.map_congr_left (g := id) fun l hl =>
    (Prod.ext rfl (hpos c hc l hl).symm : (l.1, true) = l)).trans (List.map_id c)

/-- Positive CNF and CSP use literally the same listed incidence multigraph. -/
theorem incidenceGraph_ofCNF (φ : CNF ℕ) (hp : OneSAT.positiveCheck φ = true) :
    incidenceGraph (ofCNF φ) = SAT.incidenceGraph φ := by
  rw [incidenceGraph, varCNF_ofCNF φ hp]

/-- Exact ternary source clauses give the single relation's exact declared arity. -/
theorem wellFormed_ofCNF (φ : CNF ℕ) (hw : ∀ c ∈ φ, c.length = 3) :
    (ofCNF φ).WellFormed arity := by
  intro c hc
  obtain ⟨clause, hclause, rfl⟩ := List.mem_map.mp hc
  simpa only [List.length_map, arity] using hw clause hclause

private theorem eval_eq_evalOne_varCNF (F : CSP Unit ℕ) (σ : ℕ → Bool) :
    F.eval sem σ = F.varCNF.evalOne σ := by
  simp only [Cslib.Logic.PL.CSP.eval, Cslib.Logic.PL.CSP.varCNF, CNF.evalOne, List.all_map]
  apply congrArg (fun f : Constraint Unit ℕ → Bool => F.all f)
  funext c
  simp [Constraint.eval, sem, Clause.evalOne, List.count, List.countP_map, Literal.eval,
    Function.comp_def]

/-- Dropping positive polarity tags preserves exact-one evaluation under each original
assignment, rather than merely preserving the existence of a model. -/
theorem eval_ofCNF (φ : CNF ℕ) (hp : OneSAT.positiveCheck φ = true) (σ : ℕ → Bool) :
    (ofCNF φ).eval sem σ = φ.evalOne σ := by
  rw [eval_eq_evalOne_varCNF, varCNF_ofCNF φ hp]

/-- The positive CNF adapter preserves satisfiability with the same variable assignment. -/
theorem satisfiable_ofCNF_iff (φ : CNF ℕ) (hp : OneSAT.positiveCheck φ = true) :
    (ofCNF φ).Satisfiable sem ↔ φ.OneSatisfiable := by
  simp only [Cslib.Logic.PL.CSP.Satisfiable, CNF.OneSatisfiable, eval_ofCNF φ hp]

/-- The adapter scans the existing clause and literal lists. Original variable names stay
binary, and the one relation symbol uses the existing empty-word unit encoding. -/
theorem computableInPolyTime_ofCNF :
    ComputableInPolyTime ofCNF encCNF (encCSP encUnit encNat) := by
  unfold ofCNF encCNF encCSP
  apply ComputableInPolyTime.map
  exact encConstraint_mk_polyTime (ComputableInPolyTime.const ())
    (ComputableInPolyTime.map (ComputableInPolyTime.fst encNat encBool))

end Cslib.Complexity.CSP.OneHot3
