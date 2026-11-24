/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Multigraph.MinimumSpanningForest
public import CslibFrontier.DataStructure.DisjointSet.UnionFind
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Evaluating the reference answers of the finite rank table

For each candidate edge, scan the strictly lighter edges and merge their components using
CSLib's concrete union-find client. The candidate is in the forest exactly when its endpoints
remain disconnected. For all candidate edges in a table row together, the union-find executions
inspect at most `m (m+1) (2 ⌊log₂ n⌋ + 3)` parent records and links. This bounds the operations
in the concrete union-find trace used by the reference computation in the small-tree search.
-/

public section

namespace Cslib.Multigraph.OptimalTree

open Cslib.DataStructure Cslib.DataStructure.DisjointSet
open scoped Sym2

variable {m n : ℕ} {V : Type*}

/-- The two ends of an undirected edge, in increasing order. -/
@[expose] def endpointPair [LinearOrder V] : Sym2 V → V × V :=
  Sym2.lift ⟨fun a b => (min a b, max a b), by simp [min_comm, max_comm]⟩

@[simp] theorem mk_endpointPair [LinearOrder V] (z : Sym2 V) :
    s((endpointPair z).1, (endpointPair z).2) = z := by
  induction z using Sym2.ind with
  | _ a b =>
    rcases le_total a b with h | h
    · simp [endpointPair, min_eq_left h, max_eq_right h]
    · simp [endpointPair, min_eq_right h, max_eq_left h]

/-- Merge the specified edge endpoints, then query connectivity of one pair. -/
@[expose] def connectivityClient (ends : Fin m → Sym2 (Fin n)) (es : List (Fin m))
    (a b : Fin n) : (spec n).Client Bool := do
  let _ ← spanningForestEdges (endpointPair ∘ ends) es
  same a b

private theorem client_correct (ends : Fin m → Sym2 (Fin n)) (es : List (Fin m)) (a b : Fin n) :
    (UnionFind.run (UnionFind.init n) (connectivityClient ends es a b)).value = true ↔
      Joins ends {e | e ∈ es} a b := by
  let z := Partition.discrete n
  let p := spanningForestEdges (endpointPair ∘ ends) es
  have native := (UnionFind.run_correct (connectivityClient ends es a b) (UnionFind.rep_init n)).1
  have result : (UnionFind.run (UnionFind.init n) (connectivityClient ends es a b)).value =
      (eval (spec n) p z).2.rel a b := by
    rw [native]
    change (spec n).clientResult z (p >>= fun _ => same a b) = _
    rw [StateTransitionSpec.clientResult_bind]
    change ((spec n).clientState z p).rel a b = _
    have finalState {β : Type} (q : (spec n).Client β) (t : Partition n) :
        (spec n).clientState t q = (eval (spec n) q t).2 := by
      induction q generalizing t with
      | pure _ => rfl
      | liftBind o next ih =>
        rw [eval_liftBind]
        exact ih _ _
    rw [finalState]
  rw [result, spanningForestEdges_rel_iff_eqvGen]
  clear native result
  constructor
  · intro path
    induction path with
    | rel x y h =>
      rcases h with eq | ⟨f, hf, rfl, rfl⟩
      · exact (Partition.rel_discrete_eq_true.mp eq) ▸ Joins.refl _
      · exact Joins.of_mem hf (mk_endpointPair (ends f)).symm
    | refl => exact Joins.refl _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ p q => exact p.trans q
  · intro path
    induction path with
    | refl => exact .refl _
    | tail _ step ih =>
      obtain ⟨f, hf, hxy⟩ := step
      rcases Sym2.eq_iff.mp ((mk_endpointPair (ends f)).trans hxy) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .trans _ _ _ ih (.rel _ _ (.inr ⟨f, hf, rfl, rfl⟩))
      · exact .trans _ _ _ ih (.symm _ _ (.rel _ _ (.inr ⟨f, hf, rfl, rfl⟩)))

/-- The edge labels strictly lighter than the candidate according to the row comparisons. -/
@[expose] def lighterLabels (ask : Fin m → Fin m → Bool) (e : Fin m) : List (Fin m) :=
  (List.finRange m).filter fun f => !(ask e f)

/-- Concrete union-find run used to decide whether one candidate belongs to the row's MSF. -/
@[expose] def testEdge (ends : Fin m → Sym2 (Fin n)) (ask : Fin m → Fin m → Bool) (e : Fin m) :=
  let ep := endpointPair (ends e)
  UnionFind.run (UnionFind.init n) (connectivityClient ends (lighterLabels ask e) ep.1 ep.2)

/-- Compute a reference output from the supplied pairwise comparison table. -/
@[expose] def output (ends : Fin m → Sym2 (Fin n)) (ask : Fin m → Fin m → Bool) :
    Finset (Fin m) :=
  Finset.univ.filter fun e => !(testEdge ends ask e).value

theorem output_eq_msf {W : Type*} [LinearOrder W] (ends : Fin m → Sym2 (Fin n)) (w : Fin m → W) :
    output ends (fun e f => decide (w e ≤ w f)) = msf ends w Finset.univ := by
  ext e
  let s := endpointPair (ends e)
  have eq : ends e = s(s.1, s.2) := (mk_endpointPair (ends e)).symm
  rw [mem_msf_iff w eq]
  simp only [output, Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true']
  change _ = false ↔ ¬ Joins ends _ s.1 s.2
  rw [Bool.eq_false_iff, testEdge]
  apply not_congr
  rw [client_correct]
  have lower : {f | f ∈ lighterLabels (fun x y => decide (w x ≤ w y)) e} = {f | w f < w e} :=
    Set.ext fun _ => by simp [lighterLabels, not_le]
  rw [lower]

/-- Total parent-record inspections and link operations in the concrete union-find traces of
one evaluation of the reference output, summed over all candidate edges. -/
theorem output_parent_steps_le (ends : Fin m → Sym2 (Fin n)) (ask : Fin m → Fin m → Bool) :
    ∑ e : Fin m, total id (testEdge ends ask e).traces ≤ m * (m + 1) * (2 * Nat.log 2 n + 3) := by
  have bound (e : Fin m) : total id (testEdge ends ask e).traces ≤
      (m + 1) * (2 * Nat.log 2 n + 3) := by
    let es := lighterLabels ask e
    let P := Partition.discrete n
    let ep := endpointPair (ends e)
    let cl := connectivityClient ends es ep.1 ep.2
    have native := (UnionFind.run_correct cl (UnionFind.rep_init n)).2.2.2
    have calls : ((spec n).clientHistory P cl).length = es.length + 1 := by
      dsimp only [cl, connectivityClient]
      rw [StateTransitionSpec.clientHistory_bind]
      change (_ ++ [Op.same ep.1 ep.2]).length = _
      rw [List.length_append, runClient_spanningForestEdges_length]
      rfl
    have len : es.length ≤ m := by
      simpa only [es, lighterLabels, List.length_finRange] using
        List.length_filter_le (fun f => !(ask e f)) (List.finRange m)
    exact native.trans (Nat.mul_le_mul_right _ (calls.le.trans (Nat.add_le_add_right len _)))
  calc
    _ ≤ ∑ _ : Fin m, (m + 1) * (2 * Nat.log 2 n + 3) := Finset.sum_le_sum fun e _ => bound e
    _ = _ := by simp [Nat.mul_assoc]

end Cslib.Multigraph.OptimalTree
