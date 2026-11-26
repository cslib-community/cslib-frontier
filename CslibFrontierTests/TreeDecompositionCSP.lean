/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.Lean.TreeDecomposition.CSP
public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.CSP
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Fin.VecNotation

/-! # Tree-decomposition CSP counting and decision tests

Kernel-checked tests (with no `native_decide`) exercising pure `cspCountNice`, `cspDecideNice`,
`cspCountRooted`, `cspDecideRooted`, `cspCountActiveRooted`, `cspDecideActiveRooted`, the
finite-alphabet equivalence bridges `cspCountNice_equiv` / `cspDecideNice_equiv`, and the
Word-RAM realization theorems `exists_program_cspDecide_nice`, `exists_program_cspCount_nice`,
`exists_program_cspDecide_rooted`, `exists_program_cspCount_rooted`:

1. Proper `3`-coloring (`Fin 3`) of the 4-vertex path `P₄`: `cspCountNice` evaluates by `decide`
   to `24` (`3 * 2 ^ 3`), `cspDecideNice` evaluates to `true`, and `cspCountRooted` /
   `cspDecideRooted` match.
2. Proper `3`-coloring (`Fin 3`) of `K₄` on a single-bag width-3 decomposition: `cspCountNice`
   evaluates by `decide` to `0` and `cspDecideNice` certifies `¬Satisfiable`.
3. Active primal graph DP (`cspCountActiveRooted`, `cspDecideActiveRooted`) and the
   `Bool ≃ Fin 2` bridge (`cspCountNice_equiv` / `cspDecideNice_equiv`) on a Boolean `≠`
   constraint over `{0, 1}` inside `Fin 3` with an isolated variable `2`.
4. Word-RAM FPT execution witnesses for nice and rooted tree decompositions on `path4CSP`, `k4CSP`,
   plus boundary witnesses with repeated-variable scopes `[0, 0]` and empty-scope `[]`
   constraints.
-/

public section

namespace Cslib.Tests.TreeDecompositionCSP

open SimpleGraph Cslib.Logic.PL Cslib.Algorithms.Lean Cslib.Algorithms.Lean.TreeDecomposition
open Cslib.Algorithms.WordRAM.TreeDecomposition Cslib.WordRAM

/-! ### 1. Non-Boolean `3`-coloring (`Fin 3`) on `P₄` -/

/-- Binary inequality relation (`a ≠ b`). -/
@[expose] def neqSem (q : ℕ) : Unit → List (Fin q) → Bool
  | (), [a, b] => decide (a ≠ b)
  | (), _ => false

/-- `3`-coloring CSP on `P₄`: edges `0-1`, `1-2`, `2-3`. -/
@[expose] def path4CSP : CSP Unit (Fin 4) :=
  [⟨(), [0, 1]⟩, ⟨(), [1, 2]⟩, ⟨(), [2, 3]⟩]

/-- Concrete `NiceTree` covering edges `{0, 1}`, `{1, 2}`, `{2, 3}` with width `1`. -/
@[expose] def path4NiceTree : NiceTree (Fin 4) :=
  .forget 3 (.forget 2 (.introduce 3 (.forget 1 (.introduce 2 (.forget 0
    (.introduce 1 (.introduce 0 .leaf)))))))

/-- Nice tree decomposition of `path4CSP.primalGraph`. -/
def path4Nice : path4CSP.primalGraph.NiceTreeDecomposition where
  tree := path4NiceTree
  localValid := by decide
  bag_root := by decide
  exists_mem_bag := by decide
  exists_adj_mem_bag := by
    intro u v huv
    fin_cases u <;> fin_cases v <;>
      first
      | exact absurd huv (by decide)
      | (simp only [path4NiceTree, NiceTree.CoversFinset.eq_1, NiceTree.CoversFinset.eq_2,
          NiceTree.CoversFinset.eq_3, NiceTree.bag]; decide)

/-- Width-1 rooted tree decomposition covering `path4CSP.primalGraph`. -/
def path4Rooted : path4CSP.primalGraph.RootedTreeDecomposition 2 where
  parent := ![0, 0, 1]
  parent_zero := by decide
  parent_lt := by decide
  bag := ![{0, 1}, {1, 2}, {2, 3}]
  exists_mem_bag := by decide
  exists_adj_mem_bag := by decide
  top_unique := by decide

private lemma pos3 : 0 < 3 := by decide

example : path4Nice.width = 1 := by decide
example : cspCountNice 3 pos3 (neqSem 3) path4CSP path4Nice = 24 := by decide
example : CSP.modelCount (neqSem 3) path4CSP = 24 := by
  rw [← cspCountNice_eq_modelCount pos3 (neqSem 3) path4Nice]
  decide

example : cspDecideNice 3 pos3 (neqSem 3) path4CSP path4Nice = true := by decide
example : CSP.Satisfiable (neqSem 3) path4CSP :=
  (cspDecideNice_eq_true_iff pos3 (neqSem 3) path4Nice).mp (by decide)

example : cspCountRooted 3 pos3 (neqSem 3) path4CSP path4Rooted = 24 := by
  rw [cspCountRooted_eq_modelCount, ← cspCountNice_eq_modelCount pos3 (neqSem 3) path4Nice]
  decide

example : cspDecideRooted 3 pos3 (neqSem 3) path4CSP path4Rooted = true := by
  rw [cspDecideRooted_eq_true_iff]
  exact (cspDecideNice_eq_true_iff pos3 (neqSem 3) path4Nice).mp (by decide)

/-! ### 2. Unsatisfiable `3`-coloring on `K₄` -/

/-- `K₄` all-pairs inequality CSP over `Fin 4`. -/
@[expose] def k4CSP : CSP Unit (Fin 4) :=
  [⟨(), [0, 1]⟩, ⟨(), [0, 2]⟩, ⟨(), [0, 3]⟩, ⟨(), [1, 2]⟩, ⟨(), [1, 3]⟩, ⟨(), [2, 3]⟩]

/-- Single-bag `NiceTree` over `Fin 4` introducing `{0, 1, 2, 3}` then forgetting all. -/
@[expose] def k4NiceTree : NiceTree (Fin 4) :=
  .forget 3 (.forget 2 (.forget 1 (.forget 0
    (.introduce 3 (.introduce 2 (.introduce 1 (.introduce 0 .leaf)))))))

/-- Nice decomposition of `k4CSP.primalGraph`. -/
def k4Nice : k4CSP.primalGraph.NiceTreeDecomposition where
  tree := k4NiceTree
  localValid := by decide
  bag_root := by decide
  exists_mem_bag := by decide
  exists_adj_mem_bag := by
    intro u v huv
    fin_cases u <;> fin_cases v <;>
      first
      | exact absurd huv (by decide)
      | (simp only [k4NiceTree, NiceTree.CoversFinset.eq_1, NiceTree.CoversFinset.eq_2,
          NiceTree.CoversFinset.eq_3, NiceTree.bag]; decide)

example : cspCountNice 3 pos3 (neqSem 3) k4CSP k4Nice = 0 := by decide
example : CSP.modelCount (neqSem 3) k4CSP = 0 := by
  rw [← cspCountNice_eq_modelCount pos3 (neqSem 3) k4Nice]
  decide
example : ¬CSP.Satisfiable (neqSem 3) k4CSP := by
  rw [← cspDecideNice_eq_true_iff pos3 (neqSem 3) k4Nice]
  decide

/-! ### 3. Active primal graph and `Equiv Bool (Fin 2)` bridge -/

/-- Boolean inequality constraint only on variables `0` and `1` (leaving `2` unconstrained). -/
@[expose] def boolXorSem : Unit → List Bool → Bool
  | (), [a, b] => a != b
  | (), _ => false

/-- CSP on `Fin 3` constraining only `{0, 1}`. -/
@[expose] def activePairCSP : CSP Unit (Fin 3) :=
  [⟨(), [0, 1]⟩]

/-- Decomposition over `activePairCSP.activePrimalGraph`: variable `2` is omitted from all bags. -/
def activePairRooted : activePairCSP.activePrimalGraph.RootedTreeDecomposition 0 where
  parent := ![0]
  parent_zero := by decide
  parent_lt := by decide
  bag := ![{(⟨0, by decide⟩ : ↥activePairCSP.vars.toFinset),
    (⟨1, by decide⟩ : ↥activePairCSP.vars.toFinset)}]
  exists_mem_bag := by
    rintro ⟨v, hv⟩
    fin_cases v
    · exact ⟨0, Finset.mem_insert_self _ _⟩
    · exact ⟨0, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
    · exact absurd hv (by decide)
  exists_adj_mem_bag := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩ _
    refine ⟨0, ?_, ?_⟩
    · fin_cases u
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · exact absurd hu (by decide)
    · fin_cases v
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · exact absurd hv (by decide)
  top_unique := by
    rintro ⟨v, hv⟩ i j _ _ _ _
    fin_cases i; fin_cases j; rfl

/-- Explicit `NiceTree` over `Fin 3` covering `{0, 1}` and `2` for `Equiv Bool (Fin 2)`. -/
@[expose] def pairFullNiceTree : NiceTree (Fin 3) :=
  .forget 2 (.introduce 2 (.forget 1 (.forget 0 (.introduce 1 (.introduce 0 .leaf)))))

/-- Nice decomposition over `activePairCSP.primalGraph`. -/
def pairFullNice : activePairCSP.primalGraph.NiceTreeDecomposition where
  tree := pairFullNiceTree
  localValid := by decide
  bag_root := by decide
  exists_mem_bag := by decide
  exists_adj_mem_bag := by
    intro u v huv
    fin_cases u <;> fin_cases v <;>
      first
      | exact absurd huv (by decide)
      | (simp only [pairFullNiceTree, NiceTree.CoversFinset.eq_1, NiceTree.CoversFinset.eq_2,
          NiceTree.CoversFinset.eq_3, NiceTree.bag]; decide)

private lemma pos2 : 0 < 2 := by decide

/-- `cspCountNice_equiv` and `cspDecideNice_equiv` recover `Bool` CSP model count `2`
and satisfiability directly from kernel evaluation on `pairFullNice` (ignoring isolated `2`). -/
example : CSP.modelCount boolXorSem activePairCSP = 2 := by
  rw [← cspCountNice_equiv boolXorSem pairFullNice finTwoEquiv.symm]
  decide

example : CSP.Satisfiable boolXorSem activePairCSP :=
  (cspDecideNice_equiv boolXorSem pairFullNice finTwoEquiv.symm).mp (by decide)

/-- Counting and decision on `activePairCSP.activePrimalGraph` match `CSP.modelCount` (`2`) and
`CSP.Satisfiable` (`true`). -/
example :
    cspCountActiveRooted 2 pos2 (semFin boolXorSem finTwoEquiv.symm)
        activePairCSP activePairRooted = 2 ∧
      cspDecideActiveRooted 2 pos2 (semFin boolXorSem finTwoEquiv.symm)
        activePairCSP activePairRooted = true := by
  have hc : CSP.modelCount boolXorSem activePairCSP = 2 := by
    rw [← cspCountNice_equiv boolXorSem pairFullNice finTwoEquiv.symm]
    decide
  have hs : CSP.Satisfiable boolXorSem activePairCSP :=
    (cspDecideNice_equiv boolXorSem pairFullNice finTwoEquiv.symm).mp (by decide)
  refine ⟨?_, ?_⟩
  · rw [cspCountActiveRooted_eq_modelCount, modelCount_semFin pos2 boolXorSem finTwoEquiv.symm, hc]
  · rw [cspDecideActiveRooted_eq_true_iff, satisfiable_semFin_iff boolXorSem finTwoEquiv.symm]
    exact hs

/-! ### 4. Word-RAM execution witnesses and subtle boundary scopes -/

/-- Binary equality relation (`a = b`). -/
@[expose] def eqSem (q : ℕ) : Unit → List (Fin q) → Bool
  | (), [a, b] => decide (a = b)
  | (), _ => false

/-- Constant relation taking value `b` on any tuple (including `[]`). -/
@[expose] def constSem (b : Bool) : Unit → List (Fin 2) → Bool
  | (), _ => b

/-- CSP with a repeated variable in scope `[0, 0]` plus an unconstrained variable `1`. -/
@[expose] def dupVarCSP : CSP Unit (Fin 2) := [⟨(), [0, 0]⟩]

/-- CSP with an empty-scope `[]` constraint over `Fin 2`. -/
@[expose] def emptyScopeCSP : CSP Unit (Fin 2) := [⟨(), []⟩]

/-- Single-bag `NiceTree` covering `Fin 2`. -/
@[expose] def twoVarNiceTree : NiceTree (Fin 2) :=
  .forget 1 (.forget 0 (.introduce 1 (.introduce 0 .leaf)))

/-- Nice decomposition for `dupVarCSP.primalGraph` (no edges). -/
def dupVarNice : dupVarCSP.primalGraph.NiceTreeDecomposition where
  tree := twoVarNiceTree
  localValid := by decide
  bag_root := by decide
  exists_mem_bag := by decide
  exists_adj_mem_bag := by intro u v huv; exact absurd huv (by decide +revert)

/-- Nice decomposition for `emptyScopeCSP.primalGraph` (no edges). -/
def emptyScopeNice : emptyScopeCSP.primalGraph.NiceTreeDecomposition where
  tree := twoVarNiceTree
  localValid := by decide
  bag_root := by decide
  exists_mem_bag := by decide
  exists_adj_mem_bag := by intro u v huv; exact absurd huv (by decide +revert)

example : cspCountNice 2 pos2 (eqSem 2) dupVarCSP dupVarNice = 2 := by decide
example : cspCountNice 2 pos2 (neqSem 2) dupVarCSP dupVarNice = 0 := by decide
example : cspCountNice 2 pos2 (constSem true) emptyScopeCSP emptyScopeNice = 1 := by decide
example : cspCountNice 2 pos2 (constSem false) emptyScopeCSP emptyScopeNice = 0 := by decide

/-- Branching diamond CSP on `Fin 4` with edges `(0,1), (0,2), (1,2), (0,3), (1,3)`. -/
@[expose] def diamondCSP : CSP Unit (Fin 4) :=
  [⟨(), [0, 1]⟩, ⟨(), [0, 2]⟩, ⟨(), [1, 2]⟩, ⟨(), [0, 3]⟩, ⟨(), [1, 3]⟩]

/-- Branching nice tree for `diamondCSP` whose `.join` children have distinct bag list orders
`[0, 1]` and `[1, 0]`, exercising non-identity `radixProjProg` projection. -/
@[expose] def diamondJoinTree : NiceTree (Fin 4) :=
  .forget 1 (.forget 0
    (.join
      (.forget 2 (.introduce 2 (.introduce 0 (.introduce 1 .leaf))))
      (.forget 3 (.introduce 3 (.introduce 1 (.introduce 0 .leaf))))))

/-- Nice decomposition for `diamondCSP.primalGraph`. -/
def diamondJoinNice : diamondCSP.primalGraph.NiceTreeDecomposition where
  tree := diamondJoinTree
  localValid := by decide
  bag_root := by decide
  exists_mem_bag := by decide
  exists_adj_mem_bag := by
    intro u v huv
    fin_cases u <;> fin_cases v <;>
      first
      | exact absurd huv (by decide)
      | (simp only [diamondJoinTree, NiceTree.CoversFinset.eq_1, NiceTree.CoversFinset.eq_2,
          NiceTree.CoversFinset.eq_3, NiceTree.CoversFinset.eq_4, NiceTree.bag]; decide)

example : cspCountNice 3 pos3 (neqSem 3) diamondCSP diamondJoinNice = 6 := by decide
example : cspCountNice 2 pos2 (neqSem 2) diamondCSP diamondJoinNice = 0 := by decide

private lemma diamondJoin_wordBound_le (counting : Bool) {q : ℕ} (hq : 0 < q) (hq3 : q ≤ 3) :
    (TreeCSPInstance.ofNice counting q hq (Equiv.refl (Fin 4)) (neqSem q)
      diamondCSP diamondJoinNice).wordBound ≤
      (if counting then q ^ 13 else 1) + 1000 := by
  let inst := TreeCSPInstance.ofNice counting q hq (Equiv.refl (Fin 4)) (neqSem q)
    diamondCSP diamondJoinNice
  have hcons_len :
      (inst.constraints.flatMap ConstraintTable.encode).length = 5 * (4 + q ^ 2) := by
    simp only [inst, TreeCSPInstance.ofNice, TreeCSPInstance.ofNiceTree,
      List.length_flatMap, diamondCSP, ConstraintTable.encode, ConstraintTable.ofConstraint,
      List.length_append, List.length_cons, List.length_nil, List.length_ofFn,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  have hvars_len : inst.vars.length = 10 := by
    simp only [inst, TreeCSPInstance.ofNice, TreeCSPInstance.ofNiceTree, List.length_map]
    decide
  have htree_sz : inst.tree.size = 13 := by
    simp only [inst, TreeCSPInstance.ofNice, TreeCSPInstance.ofNiceTree, NiceTree.size_map]
    decide
  have henc : inst.encode.length = 5 + 10 + 4 * 13 + 5 * (4 + q ^ 2) := by
    simp only [TreeCSPInstance.encode, List.length_append, List.length_cons, List.length_nil,
      length_encodeNiceTree, hvars_len, htree_sz, hcons_len]
  have hexp : maxTableExp inst.tree = 3 := by
    change maxTableExp (diamondJoinTree.map Fin.val) = 3
    decide
  have hv : (diamondCSP.vars.map fun v => ((Equiv.refl (Fin 4)) v).val).foldl max 0 = 3 := by
    decide
  have ht : maxTreeVert (diamondJoinNice.tree.map fun v => ((Equiv.refl (Fin 4)) v).val) = 3 := by
    decide
  have hc : ((diamondCSP.map (ConstraintTable.ofConstraint hq (Equiv.refl (Fin 4))
      (neqSem q))).flatMap fun ct => ct.scope).foldl max 0 = 3 := by
    simp [diamondCSP, ConstraintTable.ofConstraint]
  have hmv : inst.maxVarLabel = 3 := by
    dsimp only [inst, TreeCSPInstance.ofNice, TreeCSPInstance.ofNiceTree,
      TreeCSPInstance.maxVarLabel]
    rw [hv, ht, hc]
    rfl
  have hq_pow2 : q ^ 2 ≤ 9 := Nat.pow_le_pow_left hq3 2
  have hq_pow3 : q ^ 3 ≤ 27 := Nat.pow_le_pow_left hq3 3
  have hq_pow4 : q * q ^ 3 ≤ 3 * 27 := Nat.mul_le_mul hq3 hq_pow3
  have hdom : inst.domainSize = q := rfl
  have hcnt : inst.maxEntryBound = if counting then q ^ 13 else 1 := by
    have hds : diamondJoinNice.tree.size = 13 := by decide
    cases counting <;> simp [inst, TreeCSPInstance.maxEntryBound, TreeCSPInstance.ofNice,
      TreeCSPInstance.ofNiceTree, hds]
  dsimp only [inst] at henc hmv hdom hcnt ⊢
  dsimp only [TreeCSPInstance.wordBound]
  rw [henc, htree_sz, hexp, hmv, hdom, hcnt]
  omega

open Classical in
/-- Checked Word-RAM nice-tree decision witnesses (`path4Nice`, `k4Nice`, `diamondJoinNice`,
`[0, 0]`, `[]`) at realistic word width `w = 16`. -/
example : ∃ r C : ℕ, ∃ prog : Program .exact r,
    (∃ steps,
      Executes 16 prog (.init (TreeCSPInstance.ofNice false 3 pos3 (Equiv.refl (Fin 4))
        (neqSem 3) path4CSP path4Nice).encode) 1 steps ∧
      steps ≤ C * (cspNiceStepBound 3 path4Nice.size 1 6 3 + 1) + 1) ∧
    (∃ steps,
      Executes 16 prog (.init (TreeCSPInstance.ofNice false 3 pos3 (Equiv.refl (Fin 4))
        (neqSem 3) k4CSP k4Nice).encode) 0 steps ∧
      steps ≤ C * (cspNiceStepBound 3 k4Nice.size 3 12 6 + 1) + 1) ∧
    (∃ steps,
      Executes 16 prog (.init (TreeCSPInstance.ofNice false 3 pos3 (Equiv.refl (Fin 4))
        (neqSem 3) diamondCSP diamondJoinNice).encode) 1 steps ∧
      steps ≤ C * (cspNiceStepBound 3 diamondJoinNice.size 2 10 5 + 1) + 1) ∧
    (∃ steps,
      Executes 16 prog (.init (TreeCSPInstance.ofNice false 2 pos2 (Equiv.refl (Fin 4))
        (neqSem 2) diamondCSP diamondJoinNice).encode) 0 steps ∧
      steps ≤ C * (cspNiceStepBound 2 diamondJoinNice.size 2 10 5 + 1) + 1) ∧
    (∃ steps,
      Executes 16 prog (.init (TreeCSPInstance.ofNice false 2 pos2 (Equiv.refl (Fin 2))
        (neqSem 2) dupVarCSP dupVarNice).encode) 0 steps ∧
      steps ≤ C * (cspNiceStepBound 2 dupVarNice.size 1 2 1 + 1) + 1) ∧
    (∃ steps,
      Executes 16 prog (.init (TreeCSPInstance.ofNice false 2 pos2 (Equiv.refl (Fin 2))
        (constSem true) emptyScopeCSP emptyScopeNice).encode) 1 steps ∧
      steps ≤ C * (cspNiceStepBound 2 emptyScopeNice.size 1 0 1 + 1) + 1) := by
  obtain ⟨r, C, prog, hprog⟩ := exists_program_cspDecide_nice
  refine ⟨r, C, prog, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨steps, hex, hle⟩ := hprog (k := 1) pos3 (Equiv.refl (Fin 4)) (neqSem 3) path4CSP
      path4Nice (by decide) 16 (by decide)
    rw [show (if CSP.Satisfiable (neqSem 3) path4CSP then 1 else 0) = 1 from by
      have hsat : CSP.Satisfiable (neqSem 3) path4CSP :=
        (cspDecideNice_eq_true_iff pos3 (neqSem 3) path4Nice).mp (by decide)
      simp [hsat]] at hex
    rw [show path4CSP.vars.length = 6 by decide, show path4CSP.length = 3 by rfl] at hle
    exact ⟨steps, hex, hle⟩
  · let instK4 := TreeCSPInstance.ofNice false 3 pos3 (Equiv.refl (Fin 4)) (neqSem 3) k4CSP k4Nice
    have hk4_cons_len :
        (instK4.constraints.flatMap ConstraintTable.encode).length = 78 := by
      simp only [instK4, TreeCSPInstance.ofNice, TreeCSPInstance.ofNiceTree,
        List.length_flatMap, List.map_map, Function.comp_def]
      have hmap : k4CSP.map (fun c =>
          (ConstraintTable.ofConstraint pos3 (Equiv.refl (Fin 4)) (neqSem 3) c).encode.length) =
          [13, 13, 13, 13, 13, 13] := by
        simp [k4CSP, ConstraintTable.encode, ConstraintTable.ofConstraint]
      rw [hmap]
      decide
    have hvars_len : instK4.vars.length = 12 := by decide
    have htree_sz : instK4.tree.size = 9 := by decide
    have henc : instK4.encode.length = 5 + 12 + 4 * 9 + 78 := by
      simp only [TreeCSPInstance.encode, List.length_append, List.length_cons, List.length_nil,
        length_encodeNiceTree, hvars_len, htree_sz, hk4_cons_len]
    have hk4_wb : instK4.wordBound ≤ 1500 := by
      have hexp : maxTableExp instK4.tree = 4 := by decide
      have hv : (k4CSP.vars.map fun v => ((Equiv.refl (Fin 4)) v).val).foldl max 0 = 3 := by
        decide
      have ht : maxTreeVert (k4Nice.tree.map fun v => ((Equiv.refl (Fin 4)) v).val) = 3 := by
        decide
      have hc : ((k4CSP.map (ConstraintTable.ofConstraint pos3 (Equiv.refl (Fin 4))
          (neqSem 3))).flatMap fun ct => ct.scope).foldl max 0 = 3 := by decide
      have hmv : instK4.maxVarLabel = 3 := by
        dsimp only [instK4, TreeCSPInstance.ofNice, TreeCSPInstance.ofNiceTree,
          TreeCSPInstance.maxVarLabel]
        rw [hv, ht, hc]
        rfl
      have hq : instK4.domainSize = 3 := rfl
      have hcnt : instK4.maxEntryBound = 1 := rfl
      dsimp only [TreeCSPInstance.wordBound]
      rw [henc, htree_sz, hexp, hmv, hq, hcnt]
      omega
    have hk4_fit : Fits 16 instK4.wordBound :=
      (by decide : Fits 16 1500).of_le hk4_wb
    obtain ⟨steps, hex, hle⟩ := hprog (k := 3) pos3 (Equiv.refl (Fin 4)) (neqSem 3) k4CSP k4Nice
      (by decide) 16 hk4_fit
    rw [show (if CSP.Satisfiable (neqSem 3) k4CSP then 1 else 0) = 0 from by
      have hunsat : ¬CSP.Satisfiable (neqSem 3) k4CSP := by
        rw [← cspDecideNice_eq_true_iff pos3 (neqSem 3) k4Nice]; decide
      simp [hunsat]] at hex
    rw [show k4CSP.vars.length = 12 by decide, show k4CSP.length = 6 by rfl] at hle
    exact ⟨steps, hex, hle⟩
  · obtain ⟨steps, hex, hle⟩ := hprog (k := 2) pos3 (Equiv.refl (Fin 4)) (neqSem 3) diamondCSP
      diamondJoinNice (by decide) 16
      ((by decide : Fits 16 1001).of_le (diamondJoin_wordBound_le false pos3 (by decide)))
    rw [show (if CSP.Satisfiable (neqSem 3) diamondCSP then 1 else 0) = 1 from by
      have hsat : CSP.Satisfiable (neqSem 3) diamondCSP :=
        (cspDecideNice_eq_true_iff pos3 (neqSem 3) diamondJoinNice).mp (by decide)
      simp [hsat]] at hex
    rw [show diamondCSP.vars.length = 10 by decide, show diamondCSP.length = 5 by rfl] at hle
    exact ⟨steps, hex, hle⟩
  · obtain ⟨steps, hex, hle⟩ := hprog (k := 2) pos2 (Equiv.refl (Fin 4)) (neqSem 2) diamondCSP
      diamondJoinNice (by decide) 16
      ((by decide : Fits 16 1001).of_le (diamondJoin_wordBound_le false pos2 (by decide)))
    rw [show (if CSP.Satisfiable (neqSem 2) diamondCSP then 1 else 0) = 0 from by
      have hunsat : ¬CSP.Satisfiable (neqSem 2) diamondCSP := by
        rw [← cspDecideNice_eq_true_iff pos2 (neqSem 2) diamondJoinNice]; decide
      simp [hunsat]] at hex
    rw [show diamondCSP.vars.length = 10 by decide, show diamondCSP.length = 5 by rfl] at hle
    exact ⟨steps, hex, hle⟩
  · obtain ⟨steps, hex, hle⟩ := hprog (k := 1) pos2 (Equiv.refl (Fin 2)) (neqSem 2) dupVarCSP
      dupVarNice (by decide) 16 (by decide)
    rw [show (if CSP.Satisfiable (neqSem 2) dupVarCSP then 1 else 0) = 0 from by
      have hunsat : ¬CSP.Satisfiable (neqSem 2) dupVarCSP := by
        rw [← cspDecideNice_eq_true_iff pos2 (neqSem 2) dupVarNice]; decide
      simp [hunsat]] at hex
    rw [show dupVarCSP.vars.length = 2 by decide, show dupVarCSP.length = 1 by rfl] at hle
    exact ⟨steps, hex, hle⟩
  · obtain ⟨steps, hex, hle⟩ := hprog (k := 1) pos2 (Equiv.refl (Fin 2)) (constSem true)
      emptyScopeCSP emptyScopeNice (by decide) 16 (by decide)
    rw [show (if CSP.Satisfiable (constSem true) emptyScopeCSP then 1 else 0) = 1 from by
      have hsat : CSP.Satisfiable (constSem true) emptyScopeCSP :=
        (cspDecideNice_eq_true_iff pos2 (constSem true) emptyScopeNice).mp (by decide)
      simp [hsat]] at hex
    rw [show emptyScopeCSP.vars.length = 0 by decide, show emptyScopeCSP.length = 1 by rfl] at hle
    exact ⟨steps, hex, hle⟩

/-- Checked Word-RAM nice-tree counting witnesses (`path4Nice`, `diamondJoinNice` at `q = 3` and
`q = 2`, `[0, 0]`, `[]`). -/
example : ∃ r C : ℕ, ∃ prog : Program .exact r,
    (∃ steps,
      Executes 16 prog (.init (TreeCSPInstance.ofNice true 3 pos3 (Equiv.refl (Fin 4))
        (neqSem 3) path4CSP path4Nice).encode) 24 steps ∧
      steps ≤ C * (cspNiceStepBound 3 path4Nice.size 1 6 3 + 1) + 1) ∧
    (∃ steps,
      Executes 24 prog (.init (TreeCSPInstance.ofNice true 3 pos3 (Equiv.refl (Fin 4))
        (neqSem 3) diamondCSP diamondJoinNice).encode) 6 steps ∧
      steps ≤ C * (cspNiceStepBound 3 diamondJoinNice.size 2 10 5 + 1) + 1) ∧
    (∃ steps,
      Executes 16 prog (.init (TreeCSPInstance.ofNice true 2 pos2 (Equiv.refl (Fin 4))
        (neqSem 2) diamondCSP diamondJoinNice).encode) 0 steps ∧
      steps ≤ C * (cspNiceStepBound 2 diamondJoinNice.size 2 10 5 + 1) + 1) ∧
    (∃ steps,
      Executes 16 prog (.init (TreeCSPInstance.ofNice true 2 pos2 (Equiv.refl (Fin 2))
        (eqSem 2) dupVarCSP dupVarNice).encode) 2 steps ∧
      steps ≤ C * (cspNiceStepBound 2 dupVarNice.size 1 2 1 + 1) + 1) ∧
    (∃ steps,
      Executes 16 prog (.init (TreeCSPInstance.ofNice true 2 pos2 (Equiv.refl (Fin 2))
        (constSem false) emptyScopeCSP emptyScopeNice).encode) 0 steps ∧
      steps ≤ C * (cspNiceStepBound 2 emptyScopeNice.size 1 0 1 + 1) + 1) := by
  obtain ⟨r, C, prog, hprog⟩ := exists_program_cspCount_nice
  refine ⟨r, C, prog, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨steps, hex, hle⟩ := hprog (k := 1) pos3 (Equiv.refl (Fin 4)) (neqSem 3) path4CSP
      path4Nice (by decide) 16 (by decide)
    rw [show (@CSP.modelCount _ _ (Fin 3) _ inferInstance ⟨⟨0, pos3⟩⟩ (neqSem 3) path4CSP) =
        24 by
      rw [← cspCountNice_eq_modelCount pos3 (neqSem 3) path4Nice]; decide] at hex
    rw [show path4CSP.vars.length = 6 by decide, show path4CSP.length = 3 by rfl] at hle
    exact ⟨steps, hex, hle⟩
  · obtain ⟨steps, hex, hle⟩ := hprog (k := 2) pos3 (Equiv.refl (Fin 4)) (neqSem 3) diamondCSP
      diamondJoinNice (by decide) 24
      ((by decide : Fits 24 2000000).of_le
        ((diamondJoin_wordBound_le true pos3 (by decide)).trans (by decide)))
    rw [show (@CSP.modelCount _ _ (Fin 3) _ inferInstance ⟨⟨0, pos3⟩⟩ (neqSem 3) diamondCSP) =
        6 by
      rw [← cspCountNice_eq_modelCount pos3 (neqSem 3) diamondJoinNice]; decide] at hex
    rw [show diamondCSP.vars.length = 10 by decide, show diamondCSP.length = 5 by rfl] at hle
    exact ⟨steps, hex, hle⟩
  · obtain ⟨steps, hex, hle⟩ := hprog (k := 2) pos2 (Equiv.refl (Fin 4)) (neqSem 2) diamondCSP
      diamondJoinNice (by decide) 16
      ((by decide : Fits 16 10000).of_le
        ((diamondJoin_wordBound_le true pos2 (by decide)).trans (by decide)))
    rw [show (@CSP.modelCount _ _ (Fin 2) _ inferInstance ⟨⟨0, pos2⟩⟩ (neqSem 2) diamondCSP) =
        0 by
      rw [← cspCountNice_eq_modelCount pos2 (neqSem 2) diamondJoinNice]; decide] at hex
    rw [show diamondCSP.vars.length = 10 by decide, show diamondCSP.length = 5 by rfl] at hle
    exact ⟨steps, hex, hle⟩
  · obtain ⟨steps, hex, hle⟩ := hprog (k := 1) pos2 (Equiv.refl (Fin 2)) (eqSem 2) dupVarCSP
      dupVarNice (by decide) 16 (by decide)
    rw [show (@CSP.modelCount _ _ (Fin 2) _ inferInstance ⟨⟨0, pos2⟩⟩ (eqSem 2) dupVarCSP) =
        2 by
      rw [← cspCountNice_eq_modelCount pos2 (eqSem 2) dupVarNice]; decide] at hex
    rw [show dupVarCSP.vars.length = 2 by decide, show dupVarCSP.length = 1 by rfl] at hle
    exact ⟨steps, hex, hle⟩
  · obtain ⟨steps, hex, hle⟩ := hprog (k := 1) pos2 (Equiv.refl (Fin 2)) (constSem false)
      emptyScopeCSP emptyScopeNice (by decide) 16 (by decide)
    rw [show (@CSP.modelCount _ _ (Fin 2) _ inferInstance ⟨⟨0, pos2⟩⟩
        (constSem false) emptyScopeCSP) = 0 by
      rw [← cspCountNice_eq_modelCount pos2 (constSem false) emptyScopeNice]; decide] at hex
    rw [show emptyScopeCSP.vars.length = 0 by decide, show emptyScopeCSP.length = 1 by rfl] at hle
    exact ⟨steps, hex, hle⟩

open Classical in
/-- Checked Word-RAM rooted tree decomposition decision and counting witnesses on `path4Rooted`
(`Satisfiable = true`, `modelCount = 24`) at an admissible word width `w`. -/
example :
    (∃ w r C : ℕ, ∃ prog : Program .exact r,
      Fits w (TreeCSPInstance.ofRooted false 3 pos3 (Equiv.refl (Fin 4))
        (neqSem 3) path4CSP path4Rooted).wordBound ∧
      ∃ steps,
        Executes w prog (.init (TreeCSPInstance.ofRooted false 3 pos3 (Equiv.refl (Fin 4))
          (neqSem 3) path4CSP path4Rooted).encode) 1 steps ∧
        steps ≤ C * (cspRootedStepBound 3 4 1 6 3 + 1) + 1) ∧
    (∃ w r C : ℕ, ∃ prog : Program .exact r,
      Fits w (TreeCSPInstance.ofRooted true 3 pos3 (Equiv.refl (Fin 4))
        (neqSem 3) path4CSP path4Rooted).wordBound ∧
      ∃ steps,
        Executes w prog (.init (TreeCSPInstance.ofRooted true 3 pos3 (Equiv.refl (Fin 4))
          (neqSem 3) path4CSP path4Rooted).encode) 24 steps ∧
        steps ≤ C * (cspRootedStepBound 3 4 1 6 3 + 1) + 1) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨r, C, prog, hprog⟩ := exists_program_cspDecide_rooted
    let inst := TreeCSPInstance.ofRooted false 3 pos3 (Equiv.refl (Fin 4))
      (neqSem 3) path4CSP path4Rooted
    have hfit : Fits inst.wordBound inst.wordBound := fits_self inst.wordBound
    obtain ⟨steps, hex, hle⟩ := hprog (k := 1) pos3 (Equiv.refl (Fin 4)) (neqSem 3) path4CSP
      path4Rooted (path4Rooted.width_le_iff.2 (by decide)) inst.wordBound hfit
    rw [show (if CSP.Satisfiable (neqSem 3) path4CSP then 1 else 0) = 1 from by
      have hsat : CSP.Satisfiable (neqSem 3) path4CSP :=
        (cspDecideNice_eq_true_iff pos3 (neqSem 3) path4Nice).mp (by decide)
      simp [hsat]] at hex
    rw [show path4CSP.vars.length = 6 by decide, show path4CSP.length = 3 by rfl] at hle
    exact ⟨inst.wordBound, r, C, prog, hfit, steps, hex, hle⟩
  · obtain ⟨r, C, prog, hprog⟩ := exists_program_cspCount_rooted
    let inst := TreeCSPInstance.ofRooted true 3 pos3 (Equiv.refl (Fin 4))
      (neqSem 3) path4CSP path4Rooted
    have hfit : Fits inst.wordBound inst.wordBound := fits_self inst.wordBound
    obtain ⟨steps, hex, hle⟩ := hprog (k := 1) pos3 (Equiv.refl (Fin 4)) (neqSem 3) path4CSP
      path4Rooted (path4Rooted.width_le_iff.2 (by decide)) inst.wordBound hfit
    rw [show (@CSP.modelCount _ _ (Fin 3) _ inferInstance ⟨⟨0, pos3⟩⟩ (neqSem 3) path4CSP) =
        24 by
      rw [← cspCountNice_eq_modelCount pos3 (neqSem 3) path4Nice]; decide] at hex
    rw [show path4CSP.vars.length = 6 by decide, show path4CSP.length = 3 by rfl] at hle
    exact ⟨inst.wordBound, r, C, prog, hfit, steps, hex, hle⟩

end Cslib.Tests.TreeDecompositionCSP
