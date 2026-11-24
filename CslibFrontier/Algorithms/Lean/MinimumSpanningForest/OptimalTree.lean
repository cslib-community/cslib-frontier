/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.OptimalTree.Search
public import CslibFrontier.Algorithms.Lean.Query.Sort.LEQuery.KeyOracle
public import CslibFrontier.Foundations.Combinatorics.Multigraph.MinimumSpanningForest
public import Mathlib.Data.Fintype.Powerset

/-!
# An optimal comparison program for each small multigraph

In the preprocessing of [PettieRamachandran2002], §4.1, the topology of the graph is known
before its edge weights are supplied. Enumerating the possible strict weight orders turns
the MSF problem into a finite table. Searching this table at successive comparison budgets
computes a program whose worst-case number of weight comparisons is optimal for the topology.
-/

public section

namespace Cslib.Multigraph

open Cslib.Query
open scoped Sym2

variable {m n : ℕ} {α : Type*}

namespace OptimalTree

/-- All functions from a finite ordinal into a list of values. -/
@[expose] def assignments (vals : List α) : (n : ℕ) → List (Fin n → α)
  | 0 => [Fin.elim0]
  | n + 1 => vals.flatMap fun a => (assignments vals n).map fun f => Fin.cases a f

theorem mem_assignments (vals : List α) (all : ∀ a, a ∈ vals) (n : ℕ) (f : Fin n → α) :
    f ∈ assignments vals n := by
  induction n with
  | zero => simp only [assignments, List.mem_singleton]; funext i; exact Fin.elim0 i
  | succ n ih =>
    apply List.mem_flatMap.mpr
    refine ⟨f 0, all _, List.mem_map.mpr ⟨fun i => f i.succ, ih _, ?_⟩⟩
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

/-- All distinct rank assignments to the labeled edges. -/
@[expose] def ranks (m : ℕ) : List (Fin m → Fin m) :=
  (assignments (List.finRange m) m).filter fun r => decide (∀ a b, r a = r b → a = b)

theorem mem_ranks (r : Fin m → Fin m) : r ∈ ranks m ↔ Function.Injective r := by
  simp only [ranks, List.mem_filter, mem_assignments _ (fun a => List.mem_finRange a),
    true_and, decide_eq_true_eq]
  rfl

/-- Every ordered pair of edge labels names an admissible comparison. -/
@[expose] def pairs (m : ℕ) := (List.finRange m).product (List.finRange m)

theorem mem_pairs (q : Fin m × Fin m) : q ∈ pairs m := by
  obtain ⟨a, b⟩ := q
  exact List.mem_product.mpr ⟨List.mem_finRange a, List.mem_finRange b⟩

@[simp] theorem length_pairs (m : ℕ) : (pairs m).length = m * m := by
  exact (List.length_product (List.finRange m) (List.finRange m)).trans (by simp)

/-- Test membership in a finite cut by enumerating the two ends. -/
@[expose] def crosses (ends : Fin m → Sym2 (Fin n)) (cut : Finset (Fin n)) (e : Fin m) : Bool :=
  decide (∃ a b, ends e = s(a, b) ∧ a ∈ cut ∧ b ∉ cut)

/-- Compute the reference output from a table of edge comparisons. An edge is retained when
it is minimum on at least one cut. -/
@[expose] def output (ends : Fin m → Sym2 (Fin n)) (ask : Fin m → Fin m → Bool) :
    Finset (Fin m) :=
  Finset.univ.filter fun e => ∃ cut : Finset (Fin n), crosses ends cut e ∧
    ∀ f, crosses ends cut f → ask e f = true

theorem output_eq_msf {W : Type*} [LinearOrder W] (ends : Fin m → Sym2 (Fin n)) (w : Fin m → W) :
    output ends (fun e f => decide (w e ≤ w f)) = msf ends w Finset.univ := by
  classical
  ext e
  simp only [output, Finset.mem_filter, Finset.mem_univ, true_and, crosses, decide_eq_true_eq]
  constructor
  · rintro ⟨cut, he, light⟩
    apply mem_msf_of_mem_edgeCut w (Finset.mem_univ e) (P := ↑cut) (Graph.mem_edgeCut_iff.mpr he)
    exact fun f _ hf => light f (Graph.mem_edgeCut_iff.mp hf)
  · intro he
    have ex : ∃ a b, ends e = s(a, b) := by
      induction ends e using Sym2.ind with | _ a b => exact ⟨a, b, rfl⟩
    obtain ⟨a, b, hab⟩ := ex
    let lower : Set (Fin m) := {f | f ∈ (Finset.univ : Finset (Fin m)) ∧ w f < w e}
    let cut := Finset.univ.filter fun v => Joins ends lower a v
    have inCut (v : Fin n) : v ∈ cut ↔ Joins ends lower a v := by simp [cut]
    refine ⟨cut, ⟨a, b, hab, (inCut _).mpr (Joins.refl _), ?_⟩, ?_⟩
    · exact fun hb => ((mem_msf_iff w hab).mp he).2 ((inCut _).mp hb)
    · rintro f ⟨c, d, hcd, hc, hd⟩
      by_contra! lighter
      exact hd ((inCut _).mpr (((inCut _).mp hc).trans
        (Joins.of_mem (S := lower) ⟨Finset.mem_univ _, lighter⟩ hcd)))

/-- The order rank of an edge, obtained by counting its strictly lighter predecessors. -/
@[expose] def rank {W : Type*} [LinearOrder W] (w : Fin m → W) (e : Fin m) : Fin m :=
  ⟨(Finset.univ.filter (fun f => w f < w e)).card, by
    have proper : Finset.univ.filter (fun f => w f < w e) ⊂ (Finset.univ : Finset (Fin m)) :=
      (Finset.ssubset_iff_of_subset (Finset.subset_univ _)).mpr ⟨e, Finset.mem_univ _, by simp⟩
    simpa using Finset.card_lt_card proper⟩

theorem rank_strict {W : Type*} [LinearOrder W] {w : Fin m → W} {a b : Fin m}
    (hab : w a < w b) : rank w a < rank w b := by
  change (Finset.univ.filter (fun f => w f < w a)).card <
    (Finset.univ.filter (fun f => w f < w b)).card
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset ?_).mpr
  · exact ⟨a, by simp [hab], by simp⟩
  · intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans (Finset.mem_filter.mp he).2 hab⟩

theorem rank_lt {W : Type*} [LinearOrder W] (w : Fin m → W) (a b : Fin m) :
    rank w a < rank w b ↔ w a < w b := by
  constructor
  · intro h
    rcases lt_trichotomy (w a) (w b) with yes | same | rev
    · exact yes
    · have eq : rank w a = rank w b := by simp [rank, same]
      exact False.elim ((ne_of_lt h) eq)
    · exact False.elim ((not_lt_of_gt h) (rank_strict rev))
  · exact rank_strict

theorem rank_injective {W : Type*} [LinearOrder W] {w : Fin m → W} (hw : Function.Injective w) :
    Function.Injective (rank w) := by
  intro a b eq
  apply hw
  exact le_antisymm (le_of_not_gt (fun h => (ne_of_lt (rank_strict h)) eq.symm))
    (le_of_not_gt (fun h => (ne_of_lt (rank_strict h)) eq))

/-- Synthesize a program at a fixed comparison budget on the complete rank table. -/
@[expose] def atDepth (ends : Fin m → Sym2 (Fin n)) (d : ℕ) :=
  LEQuery.boundedSearch (pairs m) (fun (r : Fin m → Fin m) e f => decide (r e ≤ r f))
    (fun r => output ends (fun e f => decide (r e ≤ r f))) d (ranks m)

theorem atDepth_complete (ends : Fin m → Sym2 (Fin n)) (d : ℕ)
    (p : FreeM (LEQuery (Fin m)) (Finset (Fin m)))
    (ok : ∀ r : Fin m → Fin m, Function.Injective r →
      p.eval (LEQuery.keyOracle r) = msf ends r Finset.univ ∧
        p.countQueries (LEQuery.keyOracle r) ≤ d) :
    (atDepth ends d).isSome := by
  apply LEQuery.boundedSearch_complete mem_pairs p
  intro r hr
  obtain ⟨v, c⟩ := ok r ((mem_ranks r).mp hr)
  exact ⟨v.trans (output_eq_msf ends r).symm, c⟩

theorem atDepth_limit (ends : Fin m → Sym2 (Fin n)) : (atDepth ends (m * m)).isSome := by
  apply LEQuery.boundedSearch_complete mem_pairs
    (LEQuery.queryPairs (output ends) (pairs m) (fun _ _ => false))
  intro r _
  have h := LEQuery.queryPairs_spec (output ends) (pairs m) (fun _ _ => false)
    (fun a b => decide (r a ≤ r b)) (fun x y missing => False.elim (missing (mem_pairs (x, y))))
  exact ⟨h.1, by simpa using h.2.le⟩

/-- The first successful comparison budget and the program certified at that budget. -/
@[expose] def solution (ends : Fin m → Sym2 (Fin n)) :
    ℕ × FreeM (LEQuery (Fin m)) (Finset (Fin m)) :=
  (LEQuery.firstFeasible (atDepth ends) (m * m)).get
    (LEQuery.firstFeasible_isSome _ _ (atDepth_limit ends))

theorem solution_spec (ends : Fin m → Sym2 (Fin n)) :
    atDepth ends (solution ends).1 = some (solution ends).2 ∧ (solution ends).1 ≤ m * m ∧
    ∀ d ≤ m * m, (atDepth ends d).isSome → (solution ends).1 ≤ d :=
  LEQuery.firstFeasible_spec (Option.some_get _).symm

end OptimalTree

/-- The optimal fixed-topology comparison program constructed without inspecting the weights. -/
@[expose] def optimalMSFProgram (ends : Fin m → Sym2 (Fin n)) :
    FreeM (LEQuery (Fin m)) (Finset (Fin m)) := (OptimalTree.solution ends).2

/-- The exact comparison budget found by iterative deepening for this topology. -/
@[expose] def optimalMSFComparisons (ends : Fin m → Sym2 (Fin n)) : ℕ :=
  (OptimalTree.solution ends).1

/-- Every injective labeling into any linear order produces the native minimum spanning forest,
within the synthesized comparison budget. -/
theorem optimalMSFProgram_spec {W : Type*} [LinearOrder W] (ends : Fin m → Sym2 (Fin n))
    (w : Fin m → W) (hw : Function.Injective w) :
    (optimalMSFProgram ends).eval (LEQuery.keyOracle w) = msf ends w Finset.univ ∧
      (optimalMSFProgram ends).countQueries (LEQuery.keyOracle w) ≤ optimalMSFComparisons ends := by
  have h := LEQuery.boundedSearch_spec (OptimalTree.solution_spec ends).1
    ((OptimalTree.mem_ranks _).mpr (OptimalTree.rank_injective hw))
  have eq : (fun e f => decide (OptimalTree.rank w e ≤ OptimalTree.rank w f)) =
      (fun e f => decide (w e ≤ w f)) := by
    funext e f
    simp only [← not_lt, OptimalTree.rank_lt]
  change (optimalMSFProgram ends).eval (LEQuery.oracleOf _) = OptimalTree.output ends _ ∧
    (optimalMSFProgram ends).countQueries (LEQuery.oracleOf _) ≤ optimalMSFComparisons ends at h
  rw [eq, OptimalTree.output_eq_msf] at h
  exact h

/-- No correct program can use fewer worst-case comparisons on the rank permutations. It follows
that this budget is also optimal against programs correct on every ordered weight type. -/
theorem optimalMSFComparisons_le (ends : Fin m → Sym2 (Fin n))
    (p : FreeM (LEQuery (Fin m)) (Finset (Fin m))) (d : ℕ)
    (ok : ∀ r : Fin m → Fin m, Function.Injective r →
      p.eval (LEQuery.keyOracle r) = msf ends r Finset.univ ∧
        p.countQueries (LEQuery.keyOracle r) ≤ d) :
    optimalMSFComparisons ends ≤ d := by
  obtain ⟨_, bound, first⟩ := OptimalTree.solution_spec ends
  by_cases hd : d ≤ m * m
  · exact first d hd (OptimalTree.atDepth_complete ends d p ok)
  · exact bound.trans (by omega)

end Cslib.Multigraph
