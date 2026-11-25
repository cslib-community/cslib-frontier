/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.DPLL.Trail
public import CslibFrontier.Logics.Propositional.Resolution.TreeLikePigeonhole
import CslibFrontier.Logics.Propositional.CNF.Eval

/-! # The search tree of the DPLL trail run

The run of the DPLL search with an explicit trail (`Cslib.Algorithms.Lean.DPLL.Trail.run`)
explores a binary tree: at a partial assignment that falsifies a clause it backtracks, and at one
that neither falsifies nor satisfies every clause it tries both literals of the branch variable.
This file names that tree as a decision tree (`Cslib.Algorithms.Lean.DPLL.searchTree`): it queries
the branch variable at each branching, and its leaves carry the first clause falsified there. On
an unsatisfiable formula, the tree from the empty partial assignment finds a falsified clause on
every assignment (`Cslib.Algorithms.Lean.DPLL.findsFalsifiedClause_searchTree`), so it is a DPLL
tree in the sense of `Cslib.DecisionTree.FindsFalsifiedClause`, which converts to a tree-like
resolution refutation with at most as many leaves
(`Cslib.DecisionTree.FindsFalsifiedClause.exists_derivation_leafCount_le`). The lower bound of
Beyersdorff, Galesi and Lauria [BeyersdorffGalesiLauria2010, Theorem 2] then gives the tree at
least `(n / 2 + 1) ^ (n / 2)` leaves on `PHP^m_n`, `m > n`
(`Cslib.Algorithms.Lean.DPLL.pow_half_le_leafCount_searchTree_pigeonhole`).

The trail run need not explore the tree of the recursive search
(`Cslib.Algorithms.Lean.DPLL.search`), whose refutation `Cslib.Algorithms.Lean.DPLL.refutation?`
is: the recursive search skips the second branch of a variable when the derivation of the first
branch does not mention it, and the trail run never skips. The bound above is for the tree the
trail run explores.

A run can also emit words as it goes, some words for each partial assignment it visits
(`Cslib.Algorithms.Lean.DPLL.Trail.runLog`). Without a model below the trail, the words emitted
while the run explores the subtree at the top of the trail are those of the subtree in preorder
(`Cslib.Algorithms.Lean.DPLL.preorder`, `Cslib.Algorithms.Lean.DPLL.Trail.runLog_add_nodes`).

## Main definitions

* `Cslib.Algorithms.Lean.DPLL.searchTree`: the tree explored by the trail run.
* `Cslib.Algorithms.Lean.DPLL.preorder`, `Cslib.Algorithms.Lean.DPLL.Trail.runLog`: words
  emitted at the nodes of the tree, in preorder and along the run.

## Main results

* `Cslib.Algorithms.Lean.DPLL.findsFalsifiedClause_searchTree`: on an unsatisfiable formula, the
  tree finds a falsified clause.
* `Cslib.Algorithms.Lean.DPLL.pow_half_le_leafCount_searchTree_pigeonhole`: at least
  `(n / 2 + 1) ^ (n / 2)` leaves on `PHP^m_n`, `m > n`.
* `Cslib.Algorithms.Lean.DPLL.Trail.runLog_add_nodes`: the run emits the words of the subtree in
  preorder.

## References

* [O. Beyersdorff, N. Galesi, M. Lauria, *A lower bound for the pigeonhole principle in tree-like
  Resolution by asymmetric Prover–Delayer games*][BeyersdorffGalesiLauria2010]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.DPLL

open Cslib.Logic.PL Cslib.Logic.PL.CNF

/-! ### The search tree -/

/-- The first clause of `φ` falsified by `π`, or the empty clause if there is none. -/
def falsifiedClause (φ : CNF ℕ) (π : List (Literal ℕ)) : Clause ℕ :=
  (φ.find? (Falsifies π)).getD []

/-- **The tree explored by the trail run** from `π` with `fuel` levels: a query of the branch
variable at each branching, and the first falsified clause at each leaf. -/
def searchTree (φ : CNF ℕ) : ℕ → List (Literal ℕ) → DecisionTree ℕ (Clause ℕ)
  | 0, π => .leaf (falsifiedClause φ π)
  | fuel + 1, π =>
    match status φ π with
    | .branch l =>
      .node l.1 (searchTree φ fuel ((l.1, false) :: π)) (searchTree φ fuel ((l.1, true) :: π))
    | _ => .leaf (falsifiedClause φ π)

theorem falsifiedClause_spec {φ : CNF ℕ} {π : List (Literal ℕ)} (h : status φ π = .conflict)
    {σ : ℕ → Bool} (hσ : ∀ l ∈ π, σ l.1 = l.2) :
    falsifiedClause φ π ∈ φ ∧ (falsifiedClause φ π).eval σ = false := by
  unfold status at h
  split at h
  · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 ‹_›
    rw [falsifiedClause, hc, Option.getD_some]
    refine ⟨List.mem_of_find?_eq_some hc, (Clause.eval_eq_false_iff σ c).2 fun l hl => ?_⟩
    simpa [Std.Sat.Literal.negate] using hσ _ (falsifies_iff.1 (List.find?_some hc) l hl)
  · split at h <;> cases h

/-- The tree from `π`, without a model below `π`, finds a falsified clause on the assignments that
agree with `π`. -/
theorem eval_searchTree (φ : CNF ℕ) : (fuel : ℕ) → (π : List (Literal ℕ)) →
    (openVars φ π).length ≤ fuel → dfs φ fuel π = none → (σ : ℕ → Bool) →
    (∀ l ∈ π, σ l.1 = l.2) →
      (searchTree φ fuel π).eval σ ∈ φ ∧ ((searchTree φ fuel π).eval σ).eval σ = false
  | fuel, π, hf, hd, σ, hσ => by
    cases hs : status φ π with
    | conflict =>
      have hleaf : searchTree φ fuel π = .leaf (falsifiedClause φ π) := by
        cases fuel <;> simp [searchTree, hs]
      rw [hleaf]
      exact falsifiedClause_spec hs hσ
    | sat => cases fuel <;> simp [dfs, hs] at hd
    | branch l =>
      obtain ⟨fuel, rfl, hlen'⟩ := length_openVars_cons_le hs hf
      rw [dfs, hs, Option.or_eq_none_iff] at hd
      have hd' (b : Bool) : dfs φ fuel ((l.1, b) :: π) = none := by
        rcases l with ⟨_, _ | _⟩ <;> cases b <;> simp_all [Std.Sat.Literal.negate]
      have heval : (searchTree φ (fuel + 1) π).eval σ =
          (searchTree φ fuel ((l.1, σ l.1) :: π)).eval σ := by
        cases hv : σ l.1 <;> simp [searchTree, hs, hv]
      rw [heval]
      exact eval_searchTree φ fuel ((l.1, σ l.1) :: π) (hlen' _ rfl) (hd' _) σ
        (List.forall_mem_cons.2 ⟨rfl, hσ⟩)
  termination_by fuel => fuel

/-- The search without skipping finds no model of an unsatisfiable formula. -/
theorem dfs_eq_none_of_not_satisfiable {φ : CNF ℕ} (h : ¬ φ.Satisfiable) :
    dfs φ (depth φ) [] = none := by
  simpa [Bool.eq_false_iff.2 (mt (isSat_solve_iff φ).1 h)] using (isSat_solve_eq_isSome_dfs φ).symm

/-- **The trail run explores a DPLL tree**: on an unsatisfiable formula, the tree explored from the
empty partial assignment finds a falsified clause on every assignment. -/
theorem findsFalsifiedClause_searchTree {φ : CNF ℕ} (h : ¬ φ.Satisfiable) :
    (searchTree φ (depth φ) []).FindsFalsifiedClause φ :=
  fun σ => eval_searchTree φ _ _ (by simp [openVars_nil, depth])
    (dfs_eq_none_of_not_satisfiable h) σ (by simp)

/-- **The trail run explores `2 ^ Ω(n log n)` leaves on the pigeonhole formulas.** For `m > n`
and an injective map `f` numbering the variables of `PHP^m_n`, the tree explored by the trail run
on the renamed formula has at least `(n / 2 + 1) ^ (n / 2)` leaves. This is the bound of
[BeyersdorffGalesiLauria2010, Theorem 2] for every tree-like refutation, applied to the refutation
that the tree gives. -/
theorem pow_half_le_leafCount_searchTree_pigeonhole {m n : ℕ} {f : Fin m × Fin n → ℕ}
    (hf : Function.Injective f) (hnm : n < m) :
    (n / 2 + 1) ^ (n / 2) ≤ (searchTree ((pigeonhole m n).relabel f)
      (depth ((pigeonhole m n).relabel f)) []).leafCount :=
  pow_half_le_leafCount_relabel_pigeonhole hf hnm (findsFalsifiedClause_searchTree
    (by rw [satisfiable_relabel hf]; exact not_satisfiable_pigeonhole hnm))

/-! ### Words emitted along the tree -/

/-- The words `out π` of the nodes of the tree from `π` in preorder. -/
def preorder (φ : CNF ℕ) (out : List (Literal ℕ) → List ℕ) :
    ℕ → List (Literal ℕ) → List ℕ
  | 0, π => out π
  | fuel + 1, π =>
    match status φ π with
    | .branch l => out π ++ (preorder φ out fuel (l :: π) ++ preorder φ out fuel (l.negate :: π))
    | _ => out π

/-- If every leaf emits a word, there are at least as many words as leaves. -/
theorem leafCount_searchTree_le_length_preorder (φ : CNF ℕ) (out : List (Literal ℕ) → List ℕ)
    (hout : ∀ π, status φ π ≠ .sat → out π ≠ []) :
    (fuel : ℕ) → (π : List (Literal ℕ)) → (openVars φ π).length ≤ fuel → dfs φ fuel π = none →
      (searchTree φ fuel π).leafCount ≤ (preorder φ out fuel π).length
  | fuel, π, hf, hd => by
    cases hs : status φ π with
    | sat => cases fuel <;> simp [dfs, hs] at hd
    | conflict =>
      have hne := List.length_pos_of_ne_nil (hout π (by simp [hs]))
      cases fuel <;> simp [searchTree, preorder, hs, DecisionTree.leafCount] <;> omega
    | branch l =>
      obtain ⟨fuel, rfl, hlen'⟩ := length_openVars_cons_le hs hf
      have hlen : ∀ b : Bool, (openVars φ ((l.1, b) :: π)).length ≤ fuel := fun b => hlen' _ rfl
      rw [dfs, hs, Option.or_eq_none_iff] at hd
      have ih := fun b => leafCount_searchTree_le_length_preorder φ out hout fuel
        ((l.1, b) :: π) (hlen b)
      simp only [searchTree, preorder, hs, DecisionTree.leafCount, List.length_append]
      obtain ⟨v, c⟩ := l
      cases c
      · have h₁ := ih false hd.1
        have h₂ := ih true hd.2
        simp only [Std.Sat.Literal.negate, Bool.not_false] at h₁ h₂ ⊢
        omega
      · have h₁ := ih false hd.2
        have h₂ := ih true hd.1
        simp only [Std.Sat.Literal.negate, Bool.not_true] at h₁ h₂ ⊢
        omega
  termination_by fuel => fuel

/-- With at most one word per node, the preorder has at most one word per node of the tree. -/
theorem length_preorder_le (φ : CNF ℕ) (out : List (Literal ℕ) → List ℕ)
    (hout : ∀ π, (out π).length ≤ 1) :
    (fuel : ℕ) → (π : List (Literal ℕ)) → (preorder φ out fuel π).length ≤ Trail.nodes φ fuel π
  | 0, π => by simpa [preorder, Trail.nodes] using hout π
  | fuel + 1, π => by
    have := hout π
    cases hs : status φ π with
    | branch l =>
      have h₁ := length_preorder_le φ out hout fuel (l :: π)
      have h₂ := length_preorder_le φ out hout fuel (l.negate :: π)
      simp only [preorder, Trail.nodes, hs, List.length_append]
      omega
    | conflict => simpa [preorder, Trail.nodes, hs] using this
    | sat => simpa [preorder, Trail.nodes, hs] using this

/-- Every word of the preorder is a word of some node. -/
theorem exists_mem_of_mem_preorder (φ : CNF ℕ) (out : List (Literal ℕ) → List ℕ) {x : ℕ} :
    (fuel : ℕ) → (π : List (Literal ℕ)) → x ∈ preorder φ out fuel π → ∃ π', x ∈ out π'
  | 0, π, h => ⟨π, by simpa [preorder] using h⟩
  | fuel + 1, π, h => by
    unfold preorder at h
    split at h
    · rcases List.mem_append.1 h with h | h
      · exact ⟨π, h⟩
      rcases List.mem_append.1 h with h | h <;>
        exact exists_mem_of_mem_preorder φ out fuel _ h
    · exact ⟨π, h⟩

namespace Trail

/-- **The words emitted by a run** of at most `k` steps from the trail `t`: the words `out π` of
the partial assignment of each trail it steps from. -/
def runLog (φ : CNF ℕ) (out : List (Literal ℕ) → List ℕ) : ℕ → Trail → List ℕ
  | 0, _ => []
  | k + 1, t =>
    out (lits t) ++
      match step φ t with
      | .inl _ => []
      | .inr t' => runLog φ out k t'

/-- **The run emits the words of the subtree at the top of the trail** in preorder, when the
subtree has no model, and then continues by backtracking. -/
theorem runLog_add_nodes (φ : CNF ℕ) (out : List (Literal ℕ) → List ℕ) :
    (fuel : ℕ) → (t : Trail) → (k : ℕ) → (openVars φ (lits t)).length ≤ fuel →
      dfs φ fuel (lits t) = none →
      runLog φ out (k + nodes φ fuel (lits t)) t =
        preorder φ out fuel (lits t) ++
          match backtrack t with
          | none => []
          | some t' => runLog φ out k t'
  | fuel, t, k, hf, hd => by
    cases hs : status φ (lits t) with
    | sat => cases fuel <;> simp [dfs, hs] at hd
    | conflict =>
      rw [show nodes φ fuel (lits t) = 1 by cases fuel <;> simp [nodes, hs],
        show preorder φ out fuel (lits t) = out (lits t) by cases fuel <;> simp [preorder, hs],
        runLog, step, hs]
      cases backtrack t <;> rfl
    | branch l =>
      obtain ⟨fuel, rfl, hlen⟩ := length_openVars_cons_le hs hf
      rw [dfs, hs, Option.or_eq_none_iff] at hd
      have ih₁ := runLog_add_nodes φ out fuel (⟨l, false⟩ :: t)
        (k + nodes φ fuel (l.negate :: lits t)) (hlen l rfl) hd.1
      have ih₂ := runLog_add_nodes φ out fuel (⟨l.negate, true⟩ :: t) k (hlen l.negate rfl) hd.2
      simp only [lits_cons, backtrack_cons_false, backtrack_cons_true] at ih₁ ih₂
      have hn : k + nodes φ (fuel + 1) (lits t) =
          (k + nodes φ fuel (l.negate :: lits t) + nodes φ fuel (l :: lits t)) + 1 := by
        simp only [nodes, hs]
        omega
      rw [hn, runLog, step, hs]
      simp only [ih₁, ih₂, preorder, hs, List.append_assoc]
  termination_by fuel => fuel

end Trail

end Cslib.Algorithms.Lean.DPLL
