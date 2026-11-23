/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.TreeDecomposition.CSP
public import CslibFrontier.Computability.WordRAM.Function
import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.Scan
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontier.Foundations.Data.List.FoldMax
import CslibFrontier.Tactic.Realize
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Ring

/-!
# Word-RAM FPT dynamic programming for finite-domain CSPs over bounded treewidth

This module proves genuine exact-basis Word-RAM (`Program .exact r`) running-time bounds for both
finite-domain CSP satisfiability (`cspDecideNice`, `cspDecideRooted`) and bounded-word exact model
counting (`cspCountNice`, `cspCountRooted`) over serialized nice tree decompositions and
materialized constraint truth tables.

Unlike abstract recurrence counters, the Word-RAM program here executes every phase in linear
memory and charges every instruction:

* **Bag materialization and erasure**: `introduce` nodes allocate `1 + |childBag|` words and copy
  the child bag via `copyBagProg`; `forget` nodes scan the child bag, allocate `|childBag.erase v|`
  words, and copy the erased bag via `eraseBagProg`.
* **Radix decoding and Horner projection**: `lookupRadixProg` decodes `ofRadix q L m x` in `|L|`
  division/remainder steps, and `radixProjProg` evaluates `toRadix` across constraint scopes,
  `forget`-updated child bags, and `join` sibling bags.
* **Constraint truth-table evaluation**: each constraint `c` is stored in memory as
  `[|c.scope|, q ^ |c.scope|] ++ c.scope ++ table`, and `introduce` / `leaf` nodes scan every
  constraint, test scope inclusion (`subsetBagProg`, `bagMemProg`), project the current radix
  assignment to `c.scope`, and index the truth table in memory.
* **Bounded-word DP arithmetic**: in decision mode (`counting = false`) all DP entries lie in
  `{0, 1}` (no `q ^ |T|` word-width term); in model-counting mode (`counting = true`) DP entries at
  subtree `S` are bounded by `q ^ S.size ≤ q ^ T.size`, accounted for explicitly in
  `Fits w inst.wordBound`.

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.tupleOfRadix`: positional decoding of a radix index
  into an arity-`r` tuple in `List (Fin q)`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.ConstraintTable`: materialized truth table of a
  constraint over `ℕ` variable indices.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.encodeNiceTree`: post-order 4-word-per-node
  serialization of `NiceTree ℕ`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.TreeCSPInstance`: serialized CSP + nice tree
  decomposition instance supporting both satisfiability (`counting = false`) and exact model
  counting (`counting = true`), with constructors `ofNiceTree`, `ofNice`, and `ofRooted`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.cspNiceStepBound`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.cspRootedStepBound`: explicit FPT step-count
  polynomials.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.exists_program_csp_treeDecomposition`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.uniformComputableInTime_csp_treeDecomposition`:
  one fixed Word-RAM program computes `TreeCSPInstance.result` within
  `C * (inst.stepBound + 1) + 1`
  instructions whenever `Fits w inst.wordBound`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.exists_program_cspDecide_nice`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.exists_program_cspCount_nice`: FPT Word-RAM
  satisfiability and bounded-word model counting on `NiceTreeDecomposition`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.exists_program_cspDecide_rooted`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.exists_program_cspCount_rooted`: FPT Word-RAM
  satisfiability and bounded-word model counting on `RootedTreeDecomposition` via
  `toNiceTreePruned` (`O((|V| + 1) · q ^ (k + 1) · poly(k, |F|, |F.vars|))` instructions).
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open SimpleGraph
open Cslib.Logic.PL
open Cslib.Algorithms.Lean.TreeDecomposition
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### Positional radix tuples and materialized constraint tables -/

/-- Decode `m` in base `q` into a `List (Fin q)` of length `r` (least-significant digit first). -/
@[expose] def tupleOfRadix (q : ℕ) (hq : 0 < q) : ℕ → ℕ → List (Fin q)
  | 0, _ => []
  | r + 1, m => ⟨m % q, Nat.mod_lt m hq⟩ :: tupleOfRadix q hq r (m / q)

@[simp] theorem length_tupleOfRadix (q : ℕ) (hq : 0 < q) (r m : ℕ) :
    (tupleOfRadix q hq r m).length = r := by
  induction r generalizing m with
  | zero => rfl
  | succ r ih => simp [tupleOfRadix, ih]

/-- `tupleOfRadix` inverts `toRadix` along any variable list `scope`, even when `scope` repeats
variables. -/
theorem tupleOfRadix_toRadix {V : Type*} (q : ℕ) (hq : 0 < q) (scope : List V) (α : V → Fin q) :
    tupleOfRadix q hq scope.length (toRadix q scope (fun v => (α v).val)) = scope.map α := by
  induction scope with
  | nil => rfl
  | cons v rest ih =>
    simp only [List.length_cons, toRadix_cons, tupleOfRadix, List.map_cons]
    have hv_mod : (α v).val % q = (α v).val := Nat.mod_eq_of_lt (α v).isLt
    rw [hv_mod]
    have hhead :
        (⟨((α v).val + q * toRadix q rest (fun w => (α w).val)) % q,
          Nat.mod_lt _ hq⟩ : Fin q) = α v := by
      ext
      dsimp only
      rw [Nat.add_mul_mod_self_left, hv_mod]
    have hdiv :
        ((α v).val + q * toRadix q rest (fun w => (α w).val)) / q =
          toRadix q rest (fun w => (α w).val) := by
      rw [Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt (α v).isLt, Nat.zero_add]
    rw [hhead, hdiv, ih]

/-- Materialized truth table of a single constraint over `ℕ` variable indices and domain `Fin q`.
-/
structure ConstraintTable (q : ℕ) where
  /-- Constrained variable indices in argument order. -/
  scope : List ℕ
  /-- Flattened `{0, 1}` truth table indexed by `toRadix q scope α`. -/
  table : List ℕ
  /-- `table` has length `q ^ scope.length`. -/
  table_len : table.length = q ^ scope.length
  /-- Every entry of `table` is `0` or `1`. -/
  table_bool : ∀ x ∈ table, x ≤ 1

/-- Flat word encoding of a `ConstraintTable`: `[|scope|, |table|] ++ scope ++ table`. -/
@[expose] def ConstraintTable.encode {q : ℕ} (ct : ConstraintTable q) : List ℕ :=
  [ct.scope.length, ct.table.length] ++ ct.scope ++ ct.table

/-- Evaluate a `ConstraintTable` on a natural-valued assignment `α : ℕ → ℕ`. -/
@[expose] def ConstraintTable.eval {q : ℕ} (ct : ConstraintTable q) (α : ℕ → ℕ) : Bool :=
  ct.table.getD (toRadix q ct.scope α) 0 == 1

/-- Compile a `Constraint Rel V` into a materialized `ConstraintTable q` via `e : V ≃ Fin m`. -/
@[expose] def ConstraintTable.ofConstraint {Rel V : Type*} {q m : ℕ} (hq : 0 < q)
    (e : V ≃ Fin m) (sem : Rel → List (Fin q) → Bool) (c : Constraint Rel V) :
    ConstraintTable q where
  scope := c.scope.map fun v => (e v).val
  table := List.ofFn fun idx : Fin (q ^ c.scope.length) =>
    if sem c.rel (tupleOfRadix q hq c.scope.length idx.val) then 1 else 0
  table_len := by simp
  table_bool := by
    intro x hx
    obtain ⟨_, rfl⟩ := List.mem_ofFn.1 hx
    split_ifs <;> decide

private theorem toRadix_map {U W : Type*} (q : ℕ) (f : U → W) (xs : List U) (α : W → ℕ) :
    toRadix q (xs.map f) α = toRadix q xs (fun u => α (f u)) := by
  induction xs with
  | nil => rfl
  | cons u rest ih => simp [toRadix_cons, ih]

theorem ConstraintTable.eval_ofConstraint {Rel V : Type*} {q m : ℕ} (hq : 0 < q)
    (e : V ≃ Fin m) (sem : Rel → List (Fin q) → Bool) (c : Constraint Rel V)
    (σ : V → Fin q) (α : ℕ → ℕ) (hα : ∀ v ∈ c.scope, α (e v).val = (σ v).val) :
    (ConstraintTable.ofConstraint hq e sem c).eval α = c.eval sem σ := by
  unfold ConstraintTable.eval ConstraintTable.ofConstraint Constraint.eval
  dsimp only
  have hrad : toRadix q (c.scope.map fun v => (e v).val) α =
      toRadix q c.scope (fun v => (σ v).val) := by
    rw [toRadix_map]
    exact toRadix_congr hα
  rw [hrad]
  have hlt : toRadix q c.scope (fun v => (σ v).val) < q ^ c.scope.length :=
    toRadix_lt hq _ _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hlt), Option.getD_some,
    List.getElem_ofFn, tupleOfRadix_toRadix]
  cases sem c.rel (c.scope.map σ) <;> rfl

/-! ### Post-order serialization of `NiceTree ℕ` and pure `ℕ`-table DP -/

/-- Post-order 4-word-per-node serialization of `S` starting at node index `offset`:
* `leaf` → `[0, 0, 0, 0]`
* `introduce v child` → `encode child ++ [1, v, root(child), 0]`
* `forget v child` → `encode child ++ [2, v, root(child), 0]`
* `join left right` → `encode left ++ encode right ++ [3, 0, root(left), root(right)]`. -/
@[expose] def encodeNiceTreeAux : ℕ → NiceTree ℕ → List ℕ
  | _, .leaf => [0, 0, 0, 0]
  | offset, .introduce v child =>
    encodeNiceTreeAux offset child ++ [1, v, offset + child.size - 1, 0]
  | offset, .forget v child =>
    encodeNiceTreeAux offset child ++ [2, v, offset + child.size - 1, 0]
  | offset, .join left right =>
    encodeNiceTreeAux offset left ++
      encodeNiceTreeAux (offset + left.size) right ++
      [3, 0, offset + left.size - 1, offset + left.size + right.size - 1]

/-- Post-order 4-word-per-node serialization of `T : NiceTree ℕ` rooted at `T.size - 1`. -/
@[expose] def encodeNiceTree (T : NiceTree ℕ) : List ℕ :=
  encodeNiceTreeAux 0 T

@[simp] theorem length_encodeNiceTreeAux (offset : ℕ) (T : NiceTree ℕ) :
    (encodeNiceTreeAux offset T).length = 4 * T.size := by
  induction T generalizing offset with
  | leaf => rfl
  | introduce v child ih =>
    simp only [encodeNiceTreeAux, List.length_append, ih, List.length_cons, List.length_nil,
      NiceTree.size_introduce]
    omega
  | forget v child ih =>
    simp only [encodeNiceTreeAux, List.length_append, ih, List.length_cons, List.length_nil,
      NiceTree.size_forget]
    omega
  | join left right ihl ihr =>
    simp only [encodeNiceTreeAux, List.length_append, ihl, ihr, List.length_cons, List.length_nil,
      NiceTree.size_join]
    omega

@[simp] theorem length_encodeNiceTree (T : NiceTree ℕ) :
    (encodeNiceTree T).length = 4 * T.size :=
  length_encodeNiceTreeAux 0 T

private theorem width_child_le_introduce (v : ℕ) (c : NiceTree ℕ) :
    c.width ≤ (NiceTree.introduce v c).width :=
  Nat.sub_le_sub_right (le_max_right _ _) 1

private theorem width_child_le_forget (v : ℕ) (c : NiceTree ℕ) :
    c.width ≤ (NiceTree.forget v c).width :=
  Nat.sub_le_sub_right (le_max_right _ _) 1

private theorem width_left_le_join (l r : NiceTree ℕ) :
    l.width ≤ (NiceTree.join l r).width :=
  Nat.sub_le_sub_right ((le_max_left _ _).trans (le_max_right _ _)) 1

private theorem width_right_le_join (l r : NiceTree ℕ) :
    r.width ≤ (NiceTree.join l r).width :=
  Nat.sub_le_sub_right ((le_max_right _ _).trans (le_max_right _ _)) 1

/-- Largest vertex label occurring anywhere in `T`. -/
@[expose] def maxTreeVert : NiceTree ℕ → ℕ
  | .leaf => 0
  | .introduce v child => max v (maxTreeVert child)
  | .forget v child => max v (maxTreeVert child)
  | .join left right => max (maxTreeVert left) (maxTreeVert right)

private theorem mem_bagList_le_maxTreeVert :
    ∀ (T : NiceTree ℕ) {u : ℕ}, u ∈ bagList T → u ≤ maxTreeVert T
  | .leaf, _, h => absurd h List.not_mem_nil
  | .introduce v child, u, h => by
    simp only [bagList, List.mem_cons] at h
    rcases h with rfl | hc
    · exact le_max_left _ _
    · exact (mem_bagList_le_maxTreeVert child hc).trans (le_max_right _ _)
  | .forget v child, u, h =>
    (mem_bagList_le_maxTreeVert child (List.mem_of_mem_erase h)).trans (le_max_right _ _)
  | .join left _, u, h =>
    (mem_bagList_le_maxTreeVert left h).trans (le_max_left _ _)

private theorem encodeNiceTreeAux_max_le (offset : ℕ) (T : NiceTree ℕ) :
    ∀ x ∈ encodeNiceTreeAux offset T, x ≤ max 3 (max (maxTreeVert T) (offset + T.size)) := by
  induction T generalizing offset with
  | leaf =>
    intro x hx
    simp only [encodeNiceTreeAux, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega
  | introduce v child ih =>
    intro x hx
    simp only [encodeNiceTreeAux, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    have hv_le : v ≤ maxTreeVert (.introduce v child) := le_max_left _ _
    have hc_le : maxTreeVert child ≤ maxTreeVert (.introduce v child) := le_max_right _ _
    rcases hx with hsub | rfl | rfl | rfl | rfl
    · have h1 := ih offset x hsub
      simp only [NiceTree.size_introduce]
      omega
    · omega
    · omega
    · simp only [NiceTree.size_introduce]; omega
    · omega
  | forget v child ih =>
    intro x hx
    simp only [encodeNiceTreeAux, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    have hv_le : v ≤ maxTreeVert (.forget v child) := le_max_left _ _
    have hc_le : maxTreeVert child ≤ maxTreeVert (.forget v child) := le_max_right _ _
    rcases hx with hsub | rfl | rfl | rfl | rfl
    · have h1 := ih offset x hsub
      simp only [NiceTree.size_forget]
      omega
    · omega
    · omega
    · simp only [NiceTree.size_forget]; omega
    · omega
  | join left right ihl ihr =>
    intro x hx
    simp only [encodeNiceTreeAux, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    have hl_le : maxTreeVert left ≤ maxTreeVert (.join left right) := le_max_left _ _
    have hr_le : maxTreeVert right ≤ maxTreeVert (.join left right) := le_max_right _ _
    rcases hx with (hL | hR) | rfl | rfl | rfl | rfl
    · have h1 := ihl offset x hL
      simp only [NiceTree.size_join]
      omega
    · have h1 := ihr (offset + left.size) x hR
      simp only [NiceTree.size_join]
      omega
    · omega
    · omega
    · simp only [NiceTree.size_join]; omega
    · simp only [NiceTree.size_join]; omega

/-- Unified natural-valued DP table over `ConstraintTable q` matching both `cspDecideTree`
(`counting = false`, `{0, 1}` entries) and `cspCountTree` (`counting = true`, `ℕ` entries). -/
@[expose] def dpInstTree (counting : Bool) (q : ℕ) (cs : List (ConstraintTable q))
    (vars : List ℕ) : NiceTree ℕ → List ℕ
  | .leaf =>
    let ok := cs.all fun ct => !decide (ct.scope = []) || ct.eval (fun _ => 0)
    [if ok then 1 else 0]
  | .introduce v child =>
    let childTbl := dpInstTree counting q cs vars child
    let LB := v :: bagList child
    List.ofFn fun m : Fin (q ^ LB.length) =>
      let ok := cs.all fun ct =>
        !(decide (ct.scope.toFinset ⊆ LB.toFinset) && decide (v ∈ ct.scope)) ||
          ct.eval (ofRadix q LB m.val)
      if ok then childTbl.getD (m.val / q) 0 else 0
  | .forget v child =>
    let childTbl := dpInstTree counting q cs vars child
    let LB := (bagList child).erase v
    let addFn : ℕ → ℕ → ℕ :=
      if counting then (· + ·) else fun acc val => if val = 0 then acc else 1
    List.ofFn fun m : Fin (q ^ LB.length) =>
      if v ∈ vars then
        dpAlgFold 0 addFn q fun d =>
          let idx := toRadix q (bagList child) (Function.update (ofRadix q LB m.val) v d)
          childTbl.getD idx 0
      else
        let idx := toRadix q (bagList child) (Function.update (ofRadix q LB m.val) v 0)
        childTbl.getD idx 0
  | .join left right =>
    let leftTbl := dpInstTree counting q cs vars left
    let rightTbl := dpInstTree counting q cs vars right
    let LL := bagList left
    let LR := bagList right
    List.ofFn fun m : Fin (q ^ LL.length) =>
      let mr := toRadix q LR (ofRadix q LL m.val)
      leftTbl.getD m.val 0 * rightTbl.getD mr 0

@[simp] private theorem length_dpInstTree (counting : Bool) (q : ℕ)
    (cs : List (ConstraintTable q)) (vars : List ℕ) (T : NiceTree ℕ) :
    (dpInstTree counting q cs vars T).length = q ^ (bagList T).length := by
  cases T <;> simp [dpInstTree, bagList]

/-- Entry magnitude bound for `dpInstTree`: `≤ 1` in decision mode and `≤ q ^ T.size` in counting
mode. -/
private theorem mem_dpInstTree_le (counting : Bool) {q : ℕ} (hq : 0 < q)
    (cs : List (ConstraintTable q)) (vars : List ℕ) (T : NiceTree ℕ) :
    ∀ x ∈ dpInstTree counting q cs vars T, x ≤ if counting then q ^ T.size else 1 := by
  cases counting
  · simp only [Bool.false_eq_true, ↓reduceIte]
    induction T with
    | leaf =>
      intro x hx
      simp only [dpInstTree, List.mem_singleton] at hx
      subst hx
      split_ifs <;> omega
    | introduce v child ih =>
      intro x hx
      simp only [dpInstTree] at hx
      obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx
      split_ifs with hok
      · rw [List.getD_eq_getElem?_getD]
        cases hg : (dpInstTree false q cs vars child)[m.val / q]? with
        | none => exact Nat.zero_le _
        | some y => exact ih y (List.mem_of_getElem? hg)
      · exact Nat.zero_le _
    | forget v child ih =>
      intro x hx
      simp only [dpInstTree, Bool.false_eq_true, ↓reduceIte] at hx
      obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx
      have hchild_get (idx : ℕ) : (dpInstTree false q cs vars child).getD idx 0 ≤ 1 := by
        rw [List.getD_eq_getElem?_getD]
        cases hg : (dpInstTree false q cs vars child)[idx]? with
        | none => exact Nat.zero_le _
        | some y => exact ih y (List.mem_of_getElem? hg)
      split_ifs with hmem
      · suffices ∀ k,
            (dpAlgFold 0 (fun acc val => if val = 0 then acc else 1) k fun d =>
              (dpInstTree false q cs vars child).getD
                (toRadix q (bagList child) (Function.update (ofRadix q _ m.val) v d)) 0) ≤ 1 from
          this q
        intro k
        induction k with
        | zero => exact Nat.zero_le _
        | succ k ihk =>
          dsimp only [dpAlgFold]
          split_ifs <;> omega
      · exact hchild_get _
    | join left right ihl ihr =>
      intro x hx
      simp only [dpInstTree] at hx
      obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx
      have hL : (dpInstTree false q cs vars left).getD m.val 0 ≤ 1 := by
        rw [List.getD_eq_getElem?_getD]
        cases hg : (dpInstTree false q cs vars left)[m.val]? with
        | none => exact Nat.zero_le _
        | some y => exact ihl y (List.mem_of_getElem? hg)
      have hR : (dpInstTree false q cs vars right).getD
          (toRadix q (bagList right) (ofRadix q (bagList left) m.val)) 0 ≤ 1 := by
        rw [List.getD_eq_getElem?_getD]
        cases hg : (dpInstTree false q cs vars right)[toRadix q (bagList right)
            (ofRadix q (bagList left) m.val)]? with
        | none => exact Nat.zero_le _
        | some y => exact ihr y (List.mem_of_getElem? hg)
      exact (Nat.mul_le_mul hL hR).trans (by decide)
  · simp only [↓reduceIte]
    induction T with
    | leaf =>
      intro x hx
      simp only [dpInstTree, List.mem_singleton] at hx
      subst hx
      have hq1 : 1 ≤ q ^ (NiceTree.leaf : NiceTree ℕ).size := Nat.one_le_pow _ _ hq
      split_ifs <;> omega
    | introduce v child ih =>
      intro x hx
      simp only [dpInstTree] at hx
      obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx
      split_ifs with hok
      · have hget : (dpInstTree true q cs vars child).getD (m.val / q) 0 ≤ q ^ child.size := by
          rw [List.getD_eq_getElem?_getD]
          cases hg : (dpInstTree true q cs vars child)[m.val / q]? with
          | none => exact Nat.zero_le _
          | some y => exact ih y (List.mem_of_getElem? hg)
        exact hget.trans (Nat.pow_le_pow_right hq (by simp))
      · exact Nat.zero_le _
    | forget v child ih =>
      intro x hx
      simp only [dpInstTree, ↓reduceIte] at hx
      obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx
      have hchild_get (idx : ℕ) :
          (dpInstTree true q cs vars child).getD idx 0 ≤ q ^ child.size := by
        rw [List.getD_eq_getElem?_getD]
        cases hg : (dpInstTree true q cs vars child)[idx]? with
        | none => exact Nat.zero_le _
        | some y => exact ih y (List.mem_of_getElem? hg)
      split_ifs with hmem
      · rw [dpAlgFold_nat]
        have hsum : (∑ d ∈ Finset.range q,
            (dpInstTree true q cs vars child).getD
              (toRadix q (bagList child)
                (Function.update (ofRadix q ((bagList child).erase v) m.val) v d)) 0) ≤
            ∑ _d ∈ Finset.range q, q ^ child.size :=
          Finset.sum_le_sum fun d _ => hchild_get _
        simpa only [Finset.sum_const, Finset.card_range, smul_eq_mul, NiceTree.size_forget,
          Nat.pow_succ, Nat.mul_comm] using hsum
      · exact (hchild_get _).trans (Nat.pow_le_pow_right hq (by simp))
    | join left right ihl ihr =>
      intro x hx
      simp only [dpInstTree] at hx
      obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx
      have hL : (dpInstTree true q cs vars left).getD m.val 0 ≤ q ^ left.size := by
        rw [List.getD_eq_getElem?_getD]
        cases hg : (dpInstTree true q cs vars left)[m.val]? with
        | none => exact Nat.zero_le _
        | some y => exact ihl y (List.mem_of_getElem? hg)
      have hR : (dpInstTree true q cs vars right).getD
          (toRadix q (bagList right) (ofRadix q (bagList left) m.val)) 0 ≤ q ^ right.size := by
        rw [List.getD_eq_getElem?_getD]
        cases hg : (dpInstTree true q cs vars right)[toRadix q (bagList right)
            (ofRadix q (bagList left) m.val)]? with
        | none => exact Nat.zero_le _
        | some y => exact ihr y (List.mem_of_getElem? hg)
      calc _ ≤ q ^ left.size * q ^ right.size := Nat.mul_le_mul hL hR
        _ = q ^ (left.size + right.size) := (Nat.pow_add q left.size right.size).symm
        _ ≤ q ^ (NiceTree.join left right).size :=
            Nat.pow_le_pow_right hq (by simp [NiceTree.size_join])

/-! ### Agreement of `dpInstTree` with `cspCountTree` and `cspDecideTree` -/

private theorem bagList_map {U W : Type*} [DecidableEq U] [DecidableEq W]
    {f : U → W} (hf : Function.Injective f) (T : NiceTree U) :
    bagList (T.map f) = (bagList T).map f := by
  induction T with
  | leaf => rfl
  | introduce v child ih => simp [NiceTree.map, bagList, ih]
  | forget v child ih =>
    simp only [NiceTree.map, bagList, ih]
    clear ih
    induction bagList child with
    | nil => rfl
    | cons u rest ihr =>
      simp only [List.map_cons, List.erase_cons]
      by_cases huv : u = v
      · subst huv; simp
      · have hne : f u ≠ f v := fun h => huv (hf h)
        simp [beq_eq_false_iff_ne.2 huv, beq_eq_false_iff_ne.2 hne, ihr]
  | join left _ ihl _ => simp [NiceTree.map, bagList, ihl]

private theorem ofRadix_map_inj {U W : Type*} [DecidableEq U] [DecidableEq W]
    {f : U → W} (hf : Function.Injective f) (q : ℕ) (L : List U) (m : ℕ) (u : U) :
    ofRadix q (L.map f) m (f u) = ofRadix q L m u := by
  induction L generalizing m with
  | nil => rfl
  | cons v rest ih =>
    simp only [List.map_cons, ofRadix]
    by_cases huv : u = v
    · subst huv; simp
    · have hne : f u ≠ f v := fun h => huv (hf h)
      simp [huv, hne, ih]

private theorem dpAlgFold_bool_toNat (k : ℕ) (g : ℕ → Bool) :
    (if dpAlgFold false (· || ·) k g then 1 else 0) =
      dpAlgFold 0 (fun acc val => if val = 0 then acc else 1) k
        (fun d => if g d then 1 else 0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [dpAlgFold, dpAlgFold, ← ih]
    cases dpAlgFold false (· || ·) k g <;> cases g k <;> rfl

private theorem getD_map_boolToNat (xs : List Bool) (k : ℕ) :
    (xs.map fun b => if b then 1 else 0).getD k 0 = if xs.getD k false then 1 else 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases xs[k]? with
  | none => rfl
  | some b => cases b <;> rfl

private theorem all_ofConstraint_leaf {Rel V : Type*} {q m : ℕ} (hq : 0 < q)
    (e : V ≃ Fin m) (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) :
    ((F.map (ConstraintTable.ofConstraint hq e sem)).all fun ct =>
      !decide (ct.scope = []) || ct.eval (fun _ => 0)) =
    (F.all fun c => !decide (c.scope = []) || c.eval sem (fun _ => ⟨0, hq⟩)) := by
  rw [List.all_map]
  refine congrArg F.all (funext fun c => ?_)
  dsimp only [Function.comp_def]
  have hsc : decide ((ConstraintTable.ofConstraint hq e sem c).scope = []) =
      decide (c.scope = []) := by
    simp [ConstraintTable.ofConstraint]
  have hev := ConstraintTable.eval_ofConstraint hq e sem c (fun _ => ⟨0, hq⟩) (fun _ => 0)
    (fun _ _ => rfl)
  rw [hsc, hev]

private theorem all_ofConstraint_introduce {Rel V : Type*} [DecidableEq V] {q m : ℕ} (hq : 0 < q)
    (e : V ≃ Fin m) (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V)
    (v : V) (child : NiceTree V) (idx : ℕ) :
    ((F.map (ConstraintTable.ofConstraint hq e sem)).all fun ct =>
      !(decide (ct.scope.toFinset ⊆
          ((e v).val :: bagList (child.map fun u => (e u).val)).toFinset) &&
        decide ((e v).val ∈ ct.scope)) ||
        ct.eval (ofRadix q ((e v).val :: bagList (child.map fun u => (e u).val)) idx)) =
    (F.all fun c =>
      !(decide (c.scope.toFinset ⊆ (v :: bagList child).toFinset) && decide (v ∈ c.scope)) ||
        c.eval sem (ofRadixFin q hq (v :: bagList child) idx)) := by
  have hinj : Function.Injective (fun u : V => (e u).val) :=
    fun _ _ h => e.injective (Fin.ext h)
  have hcons_map : (e v).val :: bagList (child.map fun u => (e u).val) =
      (v :: bagList child).map fun u => (e u).val := by
    simp [bagList_map hinj child]
  rw [List.all_map]
  refine congrArg F.all (funext fun c => ?_)
  dsimp only [Function.comp_def]
  have hsub :
      decide ((ConstraintTable.ofConstraint hq e sem c).scope.toFinset ⊆
        ((e v).val :: bagList (child.map fun u => (e u).val)).toFinset) =
      decide (c.scope.toFinset ⊆ (v :: bagList child).toFinset) := by
    rw [hcons_map]
    refine decide_eq_decide.2 ?_
    simp only [ConstraintTable.ofConstraint, Finset.subset_iff, List.mem_toFinset, List.mem_map]
    refine ⟨fun hs x hx => ?_, fun hs => ?_⟩
    · obtain ⟨y, hy, heq⟩ := hs ⟨x, hx, rfl⟩
      exact hinj heq ▸ hy
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, hs hx, rfl⟩
  have hmem :
      decide ((e v).val ∈ (ConstraintTable.ofConstraint hq e sem c).scope) =
      decide (v ∈ c.scope) := by
    refine decide_eq_decide.2 ?_
    simp only [ConstraintTable.ofConstraint, List.mem_map]
    exact ⟨fun ⟨u, hu, heq⟩ => hinj heq ▸ hu, fun hv => ⟨v, hv, rfl⟩⟩
  have hev := ConstraintTable.eval_ofConstraint hq e sem c
    (ofRadixFin q hq (v :: bagList child) idx)
    (ofRadix q ((e v).val :: bagList (child.map fun u => (e u).val)) idx)
    (fun u _ => by
      rw [hcons_map]
      exact ofRadix_map_inj hinj q (v :: bagList child) idx u)
  rw [hsub, hmem, hev]

private theorem mem_map_val_iff {V : Type*} {m : ℕ} (e : V ≃ Fin m) (v : V) (vars : List V) :
    ((e v).val ∈ vars.map fun u => (e u).val) ↔ v ∈ vars := by
  have hinj : Function.Injective (fun u : V => (e u).val) :=
    fun _ _ h => e.injective (Fin.ext h)
  simp only [List.mem_map]
  exact ⟨fun ⟨u, hu, heq⟩ => hinj heq ▸ hu, fun hv => ⟨v, hv, rfl⟩⟩

private theorem toRadix_forget_map {V : Type*} [DecidableEq V] {q m : ℕ} (e : V ≃ Fin m)
    (v : V) (child : NiceTree V) (idx d : ℕ) :
    toRadix q (bagList (child.map fun u => (e u).val))
      (Function.update
        (ofRadix q ((bagList (child.map fun u => (e u).val)).erase (e v).val) idx)
        (e v).val d) =
    toRadix q (bagList child)
      (Function.update (ofRadix q ((bagList child).erase v) idx) v d) := by
  have hinj : Function.Injective (fun u : V => (e u).val) :=
    fun _ _ h => e.injective (Fin.ext h)
  have hbl := bagList_map hinj child
  have herase := bagList_map hinj (.forget v child)
  simp only [NiceTree.map, bagList] at herase
  rw [herase, hbl, toRadix_map]
  refine toRadix_congr fun u _ => ?_
  by_cases huv : u = v
  · subst huv; simp
  · have hne : (e u).val ≠ (e v).val := fun h => huv (hinj h)
    simp [huv, hne, ofRadix_map_inj hinj]

private theorem toRadix_join_map {V : Type*} [DecidableEq V] {q m : ℕ} (e : V ≃ Fin m)
    (left right : NiceTree V) (idx : ℕ) :
    toRadix q (bagList (right.map fun u => (e u).val))
      (ofRadix q (bagList (left.map fun u => (e u).val)) idx) =
    toRadix q (bagList right) (ofRadix q (bagList left) idx) := by
  have hinj : Function.Injective (fun u : V => (e u).val) :=
    fun _ _ h => e.injective (Fin.ext h)
  rw [bagList_map hinj left, bagList_map hinj right, toRadix_map]
  exact toRadix_congr fun u _ => ofRadix_map_inj hinj q (bagList left) idx u

private theorem dpInstTree_ofConstraint_count {Rel V : Type*} [DecidableEq V] {q m : ℕ}
    (hq : 0 < q) (e : V ≃ Fin m) (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V)
    (vars : List V) (T : NiceTree V) :
    dpInstTree true q (F.map (ConstraintTable.ofConstraint hq e sem))
      (vars.map fun v => (e v).val) (T.map fun v => (e v).val) =
      (cspCountTree q hq sem F vars T).toList := by
  have hinj : Function.Injective (fun v : V => (e v).val) :=
    fun _ _ h => e.injective (Fin.ext h)
  induction T with
  | leaf =>
    simp only [NiceTree.map, dpInstTree, cspCountTree, dpTree, dpCountAlg, List.toList_toArray]
    rw [all_ofConstraint_leaf]
  | introduce v child ih =>
    have hbl := bagList_map hinj child
    simp only [NiceTree.map, dpInstTree, cspCountTree, dpTree, dpCountAlg]
    rw [Array.toList_ofFn]
    refine List.ext_getElem (by simp [hbl]) fun idx h1 h2 => ?_
    simp only [List.getElem_ofFn]
    rw [all_ofConstraint_introduce, ih, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
      Array.getElem?_toList]
    rfl
  | forget v child ih =>
    have herase := bagList_map hinj (.forget v child)
    simp only [NiceTree.map, bagList] at herase
    simp only [NiceTree.map, dpInstTree, cspCountTree, dpTree, dpCountAlg, ↓reduceIte]
    rw [Array.toList_ofFn]
    refine List.ext_getElem (by simp [herase]) fun idx h1 h2 => ?_
    simp only [List.getElem_ofFn]
    have hmem := mem_map_val_iff e v vars
    rw [ih]
    by_cases hv : v ∈ vars
    · simp only [hmem.2 hv, hv, ↓reduceIte]
      refine dpAlgFold_congr fun d _ => ?_
      rw [toRadix_forget_map, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
        Array.getElem?_toList]
      rfl
    · simp only [mt hmem.1 hv, hv, ↓reduceIte, toRadix_forget_map,
        Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]
      rfl
  | join left right ihl ihr =>
    have hblL := bagList_map hinj left
    simp only [NiceTree.map, dpInstTree, cspCountTree, dpTree, dpCountAlg]
    rw [Array.toList_ofFn, ihl, ihr]
    refine List.ext_getElem (by simp [hblL]) fun idx h1 h2 => ?_
    simp only [List.getElem_ofFn]
    rw [toRadix_join_map]
    simp only [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]
    rfl

private theorem dpInstTree_ofConstraint_decide {Rel V : Type*} [DecidableEq V] {q m : ℕ}
    (hq : 0 < q) (e : V ≃ Fin m) (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V)
    (vars : List V) (T : NiceTree V) :
    dpInstTree false q (F.map (ConstraintTable.ofConstraint hq e sem))
      (vars.map fun v => (e v).val) (T.map fun v => (e v).val) =
      (cspDecideTree q hq sem F vars T).toList.map (fun b => if b then 1 else 0) := by
  have hinj : Function.Injective (fun v : V => (e v).val) :=
    fun _ _ h => e.injective (Fin.ext h)
  have hget_arr (C : NiceTree V) (k : ℕ) :
      ((cspDecideTree q hq sem F vars C).toList.map (fun b => if b then 1 else 0)).getD k 0 =
        if (cspDecideTree q hq sem F vars C).getD k false then 1 else 0 := by
    rw [getD_map_boolToNat, List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_toList]
  induction T with
  | leaf =>
    simp only [NiceTree.map, dpInstTree, cspDecideTree, dpTree, dpDecideAlg,
      List.toList_toArray, List.map_cons, List.map_nil]
    rw [all_ofConstraint_leaf]
    cases F.all fun c => !decide (c.scope = []) || c.eval sem (fun _ => ⟨0, hq⟩) <;> rfl
  | introduce v child ih =>
    have hbl := bagList_map hinj child
    simp only [NiceTree.map, dpInstTree, cspDecideTree, dpTree, dpDecideAlg]
    rw [Array.toList_ofFn]
    refine List.ext_getElem (by simp [hbl]) fun idx h1 h2 => ?_
    simp only [List.getElem_ofFn, List.getElem_map]
    rw [all_ofConstraint_introduce, ih]
    change (if _ then ((cspDecideTree q hq sem F vars child).toList.map _).getD (idx / q) 0
        else 0) =
      if (if _ then (cspDecideTree q hq sem F vars child).getD (idx / q) false else false) = true
      then 1 else 0
    rw [hget_arr child (idx / q)]
    cases F.all fun c =>
      !(decide (c.scope.toFinset ⊆ (v :: bagList child).toFinset) && decide (v ∈ c.scope)) ||
        c.eval sem (ofRadixFin q hq (v :: bagList child) idx) <;> rfl
  | forget v child ih =>
    have herase := bagList_map hinj (.forget v child)
    simp only [NiceTree.map, bagList] at herase
    simp only [NiceTree.map, dpInstTree, cspDecideTree, dpTree, dpDecideAlg,
      Bool.false_eq_true, ↓reduceIte]
    rw [Array.toList_ofFn]
    refine List.ext_getElem (by simp [herase]) fun idx h1 h2 => ?_
    simp only [List.getElem_ofFn, List.getElem_map]
    have hmem := mem_map_val_iff e v vars
    rw [ih]
    by_cases hv : v ∈ vars
    · simp only [hmem.2 hv, hv, ↓reduceIte]
      change dpAlgFold 0 _ q (fun d =>
          ((cspDecideTree q hq sem F vars child).toList.map _).getD _ 0) =
        if dpAlgFold false (· || ·) q (fun d =>
          (cspDecideTree q hq sem F vars child).getD _ false) = true then 1 else 0
      rw [dpAlgFold_bool_toNat]
      refine dpAlgFold_congr fun d _ => ?_
      rw [toRadix_forget_map, hget_arr child]
    · simp only [mt hmem.1 hv, hv, ↓reduceIte, toRadix_forget_map]
      exact hget_arr child _
  | join left right ihl ihr =>
    have hblL := bagList_map hinj left
    simp only [NiceTree.map, dpInstTree, cspDecideTree, dpTree, dpDecideAlg]
    rw [Array.toList_ofFn, ihl, ihr]
    refine List.ext_getElem (by simp [hblL]) fun idx h1 h2 => ?_
    simp only [List.getElem_ofFn, List.getElem_map]
    rw [toRadix_join_map]
    change ((cspDecideTree q hq sem F vars left).toList.map _).getD idx 0 *
        ((cspDecideTree q hq sem F vars right).toList.map _).getD _ 0 =
      if ((cspDecideTree q hq sem F vars left).getD idx false &&
          (cspDecideTree q hq sem F vars right).getD _ false) = true then 1 else 0
    rw [hget_arr left, hget_arr right]
    cases (cspDecideTree q hq sem F vars left).getD idx false <;>
      cases (cspDecideTree q hq sem F vars right).getD
        (toRadix q (bagList right) (ofRadix q (bagList left) idx)) false <;> rfl

/-! ### `TreeCSPInstance` and FPT step bounds -/

/-- Worst-case table exponent across `T`: bounds `(bagList S).length` at all nodes and
`((bagList child).erase v).length + 1` at `forget` nodes, while staying `≤ T.width + 1` whenever
`T.LocalValid` holds. -/
@[expose] def maxTableExp : NiceTree ℕ → ℕ
  | .leaf => 0
  | .introduce v child => max (v :: bagList child).length (maxTableExp child)
  | .forget v child => max (((bagList child).erase v).length + 1) (maxTableExp child)
  | .join left right => max (bagList left).length (max (maxTableExp left) (maxTableExp right))

private theorem bagList_length_le_maxTableExp (T : NiceTree ℕ) :
    (bagList T).length ≤ maxTableExp T := by
  cases T <;> simp [bagList, maxTableExp]

private theorem maxTableExp_le_width_succ {T : NiceTree ℕ} (hval : T.LocalValid) :
    maxTableExp T ≤ T.width + 1 := by
  induction T with
  | leaf => simp [maxTableExp]
  | introduce v child ih =>
    have hb : (v :: bagList child).length ≤ (NiceTree.introduce v child).width + 1 :=
      length_bagList_le hval
    have hc : maxTableExp child ≤ (NiceTree.introduce v child).width + 1 :=
      (ih hval.2).trans (Nat.add_le_add_right (width_child_le_introduce v child) 1)
    exact max_le hb hc
  | forget v child ih =>
    have hv_mem : v ∈ bagList child := by
      have hfin := toFinset_bagList hval.2
      exact List.mem_toFinset.1 (hfin.symm ▸ hval.1)
    have hlen_er : ((bagList child).erase v).length + 1 = (bagList child).length := by
      have hpos : 0 < (bagList child).length := List.length_pos_of_mem hv_mem
      have her := List.length_erase_of_mem hv_mem
      omega
    have hb : ((bagList child).erase v).length + 1 ≤ (NiceTree.forget v child).width + 1 := by
      rw [hlen_er]
      exact (length_bagList_le hval.2).trans
        (Nat.add_le_add_right (width_child_le_forget v child) 1)
    have hc : maxTableExp child ≤ (NiceTree.forget v child).width + 1 :=
      (ih hval.2).trans (Nat.add_le_add_right (width_child_le_forget v child) 1)
    exact max_le hb hc
  | join left right ihl ihr =>
    have hb : (bagList left).length ≤ (NiceTree.join left right).width + 1 :=
      length_bagList_le hval
    have hl : maxTableExp left ≤ (NiceTree.join left right).width + 1 :=
      (ihl hval.2.2.1).trans (Nat.add_le_add_right (width_left_le_join left right) 1)
    have hr : maxTableExp right ≤ (NiceTree.join left right).width + 1 :=
      (ihr hval.2.2.2).trans (Nat.add_le_add_right (width_right_le_join left right) 1)
    exact max_le hb (max_le hl hr)

/-- FPT `memoryCost` bound for CSP satisfiability or bounded-word model counting on a nice tree
decomposition of size `numNodes` and width `≤ k`, domain size `q`, `numCons = |F|`,
and `varsLen = |F.vars|` (total arity across all constraints):
`O(numNodes · q ^ (k + 1) · ((k + 1) ^ 2 + |F| + |F.vars| · (k + 1)) + numNodes · |F.vars|)`. -/
@[expose] def cspNiceStepBound (q numNodes k varsLen numCons : ℕ) : ℕ :=
  let W1 := k + 1
  12 + numNodes *
    (16 + 4 * W1 + varsLen +
      q ^ W1 * (W1 ^ 2 + W1 + 4 + 3 * numCons + varsLen * (2 * W1 + 3)))

/-- FPT `memoryCost` bound on a rooted tree decomposition via `toNiceTreePruned`
(`numNodes ≤ (3 * k + 5) * (card V + 1)`). -/
@[expose] def cspRootedStepBound (q cardV k varsLen numCons : ℕ) : ℕ :=
  cspNiceStepBound q ((3 * k + 5) * (cardV + 1)) k varsLen numCons

theorem cspNiceStepBound_mono {q n₁ n₂ k₁ k₂ v₁ v₂ c₁ c₂ : ℕ} (hq : 0 < q)
    (hn : n₁ ≤ n₂) (hk : k₁ ≤ k₂) (hv : v₁ ≤ v₂) (hc : c₁ ≤ c₂) :
    cspNiceStepBound q n₁ k₁ v₁ c₁ ≤ cspNiceStepBound q n₂ k₂ v₂ c₂ := by
  unfold cspNiceStepBound
  dsimp only
  refine Nat.add_le_add_left (Nat.mul_le_mul hn ?_) 12
  have hW : k₁ + 1 ≤ k₂ + 1 := Nat.add_le_add_right hk 1
  have hpow : q ^ (k₁ + 1) ≤ q ^ (k₂ + 1) := Nat.pow_le_pow_right hq hW
  have hsq : (k₁ + 1) ^ 2 ≤ (k₂ + 1) ^ 2 := Nat.pow_le_pow_left hW 2
  have hmulA : v₁ * (2 * (k₁ + 1) + 3) ≤ v₂ * (2 * (k₂ + 1) + 3) :=
    Nat.mul_le_mul hv (by omega)
  refine Nat.add_le_add (Nat.add_le_add (by omega) hv) (Nat.mul_le_mul hpow ?_)
  omega

/-- Serialized finite-domain CSP instance with a nice tree decomposition for Word-RAM execution. -/
structure TreeCSPInstance where
  /-- `false` for satisfiability (`{0, 1}` output), `true` for exact model counting. -/
  counting : Bool
  /-- Domain size `q > 0`. -/
  domainSize : ℕ
  /-- Positivity of `domainSize`. -/
  domainSize_pos : 0 < domainSize
  /-- Active variable indices (`F.vars`). -/
  vars : List ℕ
  /-- Materialized constraint truth tables. -/
  constraints : List (ConstraintTable domainSize)
  /-- Nice tree decomposition over `ℕ` vertex indices. -/
  tree : NiceTree ℕ

namespace TreeCSPInstance

/-- Flat word encoding loaded into `State.init`:
`[mode, q, |vars|, |constraints|, tree.size] ++ vars ++ encodeNiceTree tree ++ constraints`. -/
@[expose] def encode (inst : TreeCSPInstance) : List ℕ :=
  [if inst.counting then 1 else 0,
   inst.domainSize,
   inst.vars.length,
   inst.constraints.length,
   inst.tree.size] ++
  inst.vars ++
  encodeNiceTree inst.tree ++
  inst.constraints.flatMap ConstraintTable.encode

/-- Root DP answer (`1`/`0` for satisfiability when `counting = false`, exact model count when
`counting = true`). -/
@[expose] def result (inst : TreeCSPInstance) : ℕ :=
  (dpInstTree inst.counting inst.domainSize inst.constraints inst.vars inst.tree).getD 0 0

/-- Total arity across all materialized constraints. -/
@[expose] def totalArity (inst : TreeCSPInstance) : ℕ :=
  (inst.constraints.map fun ct => ct.scope.length).sum

/-- Maximum variable index occurring in `vars`, `tree`, or any constraint scope. -/
@[expose] def maxVarLabel (inst : TreeCSPInstance) : ℕ :=
  max (inst.vars.foldl max 0)
    (max (maxTreeVert inst.tree)
      ((inst.constraints.flatMap fun ct => ct.scope).foldl max 0))

/-- Maximum DP entry value: `1` in decision mode, `q ^ tree.size` in counting mode. -/
@[expose] def maxEntryBound (inst : TreeCSPInstance) : ℕ :=
  if inst.counting then inst.domainSize ^ inst.tree.size else 1

/-- Sufficient word bound covering all memory frontiers, node/bag/table indices, variable names,
and DP entry values. -/
@[expose] def wordBound (inst : TreeCSPInstance) : ℕ :=
  let E := maxTableExp inst.tree
  inst.encode.length + 8 +
    4 * inst.tree.size +
    inst.tree.size * (E + 2 + inst.domainSize ^ E) +
    inst.domainSize * inst.domainSize ^ E +
    inst.maxVarLabel +
    inst.maxEntryBound

/-- Step-count bound (`memoryCost`) for `inst`. -/
@[expose] def stepBound (inst : TreeCSPInstance) : ℕ :=
  let E := maxTableExp inst.tree
  12 + inst.tree.size *
    (16 + 4 * E + inst.vars.length +
      inst.domainSize ^ E *
        (E ^ 2 + E + 4 + 3 * inst.constraints.length + inst.totalArity * (2 * E + 3)))

/-- Compile a `CSP Rel V` and `NiceTree V` into a `TreeCSPInstance` via `e : V ≃ Fin m`. -/
@[expose] def ofNiceTree {Rel V : Type*} {m : ℕ} (counting : Bool) (q : ℕ) (hq : 0 < q)
    (e : V ≃ Fin m) (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) (T : NiceTree V) :
    TreeCSPInstance where
  counting := counting
  domainSize := q
  domainSize_pos := hq
  vars := F.vars.map fun v => (e v).val
  constraints := F.map (ConstraintTable.ofConstraint hq e sem)
  tree := T.map fun v => (e v).val

/-- Compile a `CSP Rel V` and `NiceTreeDecomposition` of `F.primalGraph`. -/
@[expose] def ofNice {Rel V : Type*} [DecidableEq V] {m : ℕ} (counting : Bool) (q : ℕ) (hq : 0 < q)
    (e : V ≃ Fin m) (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V)
    (N : F.primalGraph.NiceTreeDecomposition) : TreeCSPInstance :=
  ofNiceTree counting q hq e sem F N.tree

/-- Compile a `CSP Rel V` and `RootedTreeDecomposition` of `F.primalGraph` via
`toNiceTreePruned`. -/
@[expose] def ofRooted {Rel V : Type*} [LinearOrder V] {m n : ℕ}
    (counting : Bool) (q : ℕ) (hq : 0 < q) (e : V ≃ Fin m)
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V)
    (R : F.primalGraph.RootedTreeDecomposition n) : TreeCSPInstance :=
  ofNice counting q hq e sem F R.toNiceTreePruned

theorem result_ofNiceTree_count {Rel V : Type*} [DecidableEq V] {q m : ℕ} (hq : 0 < q)
    (e : V ≃ Fin m) (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) (T : NiceTree V) :
    (ofNiceTree true q hq e sem F T).result = cspCountNiceTree q hq sem F T := by
  unfold result ofNiceTree cspCountNiceTree
  dsimp only
  rw [dpInstTree_ofConstraint_count hq e sem F F.vars T,
    List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, Array.getElem?_toList]

theorem result_ofNiceTree_decide {Rel V : Type*} [DecidableEq V] {q m : ℕ} (hq : 0 < q)
    (e : V ≃ Fin m) (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) (T : NiceTree V) :
    (ofNiceTree false q hq e sem F T).result =
      if cspDecideNiceTree q hq sem F T then 1 else 0 := by
  unfold result ofNiceTree cspDecideNiceTree
  dsimp only
  rw [dpInstTree_ofConstraint_decide hq e sem F F.vars T,
    List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, List.getElem?_map,
    Array.getElem?_toList]
  cases (cspDecideTree q hq sem F F.vars T)[0]? with
  | none => rfl
  | some b => cases b <;> rfl

theorem result_ofNice_count {Rel V : Type*} [DecidableEq V] {q m : ℕ} (hq : 0 < q)
    (e : V ≃ Fin m) (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V)
    (N : F.primalGraph.NiceTreeDecomposition) :
    (ofNice true q hq e sem F N).result =
      @CSP.modelCount _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩ sem F := by
  rw [ofNice, result_ofNiceTree_count, ← cspCountNice_eq_modelCount hq sem N]
  rfl

theorem result_ofNice_decide {Rel V : Type*} [DecidableEq V] {q m : ℕ} (hq : 0 < q)
    (e : V ≃ Fin m) (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V)
    (N : F.primalGraph.NiceTreeDecomposition) :
    (ofNice false q hq e sem F N).result = 1 ↔ CSP.Satisfiable sem F := by
  rw [ofNice, result_ofNiceTree_decide, ← cspDecideNice_eq_true_iff hq sem N]
  unfold cspDecideNice
  cases cspDecideNiceTree q hq sem F N.tree <;> simp

theorem result_ofRooted_count {Rel V : Type*} [LinearOrder V] {q m n : ℕ} (hq : 0 < q)
    (e : V ≃ Fin m) (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V)
    (R : F.primalGraph.RootedTreeDecomposition n) :
    (ofRooted true q hq e sem F R).result =
      @CSP.modelCount _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩ sem F :=
  result_ofNice_count hq e sem F R.toNiceTreePruned

theorem result_ofRooted_decide {Rel V : Type*} [LinearOrder V] {q m n : ℕ} (hq : 0 < q)
    (e : V ≃ Fin m) (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V)
    (R : F.primalGraph.RootedTreeDecomposition n) :
    (ofRooted false q hq e sem F R).result = 1 ↔ CSP.Satisfiable sem F :=
  result_ofNice_decide hq e sem F R.toNiceTreePruned

theorem stepBound_ofNice_le {Rel V : Type*} [DecidableEq V] {q m k : ℕ} (hq : 0 < q)
    (counting : Bool) (e : V ≃ Fin m) (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V)
    (N : F.primalGraph.NiceTreeDecomposition) (hk : N.width ≤ k) :
    (ofNice counting q hq e sem F N).stepBound ≤
      cspNiceStepBound q N.size k F.vars.length F.length := by
  have hinj : Function.Injective (fun v : V => (e v).val) :=
    fun _ _ h => e.injective (Fin.ext h)
  have hval : (N.tree.map fun v => (e v).val).LocalValid :=
    NiceTree.localValid_map hinj N.localValid
  have hw_eq : (N.tree.map fun v => (e v).val).width = N.width :=
    NiceTree.width_map hinj N.tree
  have hexp : maxTableExp (N.tree.map fun v => (e v).val) ≤ k + 1 := by
    refine (maxTableExp_le_width_succ hval).trans ?_
    rw [hw_eq]
    exact Nat.add_le_add_right hk 1
  have hsize : (N.tree.map fun v => (e v).val).size = N.size :=
    NiceTree.size_map _ N.tree
  have hvars : ((ofNice counting q hq e sem F N).vars).length = F.vars.length := by
    simp [ofNice, ofNiceTree]
  have hcons : ((ofNice counting q hq e sem F N).constraints).length = F.length := by
    simp [ofNice, ofNiceTree]
  have harity : (ofNice counting q hq e sem F N).totalArity = F.vars.length := by
    unfold ofNice ofNiceTree totalArity CSP.vars
    dsimp only
    rw [List.length_flatMap, List.map_map]
    congr 2
    funext c
    simp [ConstraintTable.ofConstraint]
  unfold stepBound
  dsimp only
  have htree : (ofNice counting q hq e sem F N).tree = N.tree.map fun v => (e v).val := rfl
  rw [htree, hsize, hvars, hcons, harity]
  have hdom : (ofNice counting q hq e sem F N).domainSize = q := rfl
  rw [hdom]
  have hpow : q ^ maxTableExp (N.tree.map fun v => (e v).val) ≤ q ^ (k + 1) :=
    Nat.pow_le_pow_right hq hexp
  have hsq : maxTableExp (N.tree.map fun v => (e v).val) ^ 2 ≤ (k + 1) ^ 2 :=
    Nat.pow_le_pow_left hexp 2
  have hmulA :
      F.vars.length * (2 * maxTableExp (N.tree.map fun v => (e v).val) + 3) ≤
        F.vars.length * (2 * (k + 1) + 3) :=
    Nat.mul_le_mul_left _ (by omega)
  unfold cspNiceStepBound
  dsimp only
  refine Nat.add_le_add_left (Nat.mul_le_mul_left N.size ?_) 12
  refine Nat.add_le_add (Nat.add_le_add (by omega) le_rfl) (Nat.mul_le_mul hpow ?_)
  omega

theorem stepBound_ofRooted_le {Rel V : Type*} [LinearOrder V] {q m n k : ℕ} (hq : 0 < q)
    (counting : Bool) (e : V ≃ Fin m) (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V)
    (R : F.primalGraph.RootedTreeDecomposition n) (hk : R.width ≤ k) :
    (ofRooted counting q hq e sem F R).stepBound ≤
      cspRootedStepBound q m k F.vars.length F.length := by
  let _ : Fintype V := Fintype.ofEquiv (Fin m) e.symm
  have hcard : Fintype.card V = m := by
    rw [Fintype.card_congr e, Fintype.card_fin]
  have hw : R.toNiceTreePruned.width ≤ k := R.toNiceTreePruned_width_le.trans hk
  have hs : R.toNiceTreePruned.size ≤ (3 * k + 5) * (m + 1) := by
    have h1 := R.toNiceTreePruned_size_le
    rw [hcard] at h1
    exact h1.trans (Nat.mul_le_mul_right _ (by omega))
  exact (stepBound_ofNice_le hq counting e sem F R.toNiceTreePruned hw).trans
    (cspNiceStepBound_mono hq hs le_rfl le_rfl le_rfl)

end TreeCSPInstance

/-! ### Low-level Word-RAM bag, radix, and constraint-table routines -/

private structure LookupRadixArgs where
  q : ℕ
  bagPtr : ℕ
  bagLen : ℕ
  m : ℕ
  target : ℕ

private def LookupRadixArgs.equiv : LookupRadixArgs ≃ (((ℕ × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a := ((((a.q, a.bagPtr), a.bagLen), a.m), a.target)
  invFun := fun ((((q, bp), bl), m), t) => ⟨q, bp, bl, m, t⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding LookupRadixArgs := .ofEquiv LookupRadixArgs.equiv

private structure LookupRadixState where
  curPtr : ℕ
  curM : ℕ
  found : ℕ
  ans : ℕ

private def LookupRadixState.equiv : LookupRadixState ≃ ((ℕ × ℕ) × ℕ) × ℕ where
  toFun s := (((s.curPtr, s.curM), s.found), s.ans)
  invFun := fun (((cp, cm), f), a) => ⟨cp, cm, f, a⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding LookupRadixState := .ofEquiv LookupRadixState.equiv

private def lookupRadixStep (env : (ℕ × ℕ) × LookupRadixState) :
    Memory.Prog LookupRadixState := do
  let q := env.1.1
  let target := env.1.2
  let st := env.2
  let v ← Memory.read st.curPtr
  let digit := st.curM % q
  let nextM := st.curM / q
  let hit := if st.found = 0 ∧ target = v then 1 else 0
  let ans' := if hit = 1 then digit else st.ans
  let found' := if hit = 1 then 1 else st.found
  pure ⟨st.curPtr + 1, nextM, found', ans'⟩

private def lookupRadixProg (args : LookupRadixArgs) : Memory.Prog ℕ := do
  let res ← iterate lookupRadixStep (args.q, args.target) args.bagLen
    ⟨args.bagPtr, args.m, 0, 0⟩
  pure res.ans

private theorem lookupRadixProg_state (args : LookupRadixArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (lookupRadixProg args) = s := by
  unfold lookupRadixProg
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of lookupRadixStep (args.q, args.target)
    (fun _ _ => rfl) args.bagLen ⟨args.bagPtr, args.m, 0, 0⟩ s

private theorem lookupRadixProg_result (args : LookupRadixArgs) {LB : List ℕ} {s : Memory.State}
    (hLB : HoldsIn args.bagPtr LB s) (hlen : LB.length = args.bagLen) :
    (Memory.spec 0).clientResult s (lookupRadixProg args) =
      ofRadix args.q LB args.m args.target := by
  unfold lookupRadixProg
  rw [StateTransitionSpec.clientResult_bind]
  suffices ∀ ys curPtr curM found ans,
      HoldsIn curPtr ys s →
      ((found = 0 ∧ ans = 0) ∨ found = 1) →
      ((Memory.spec 0).clientResult s
        (iterate lookupRadixStep (args.q, args.target) ys.length
          ⟨curPtr, curM, found, ans⟩)).ans =
        if found = 1 then ans else ofRadix args.q ys curM args.target by
    have hrun := this LB args.bagPtr args.m 0 0 hLB (.inl ⟨rfl, rfl⟩)
    rw [hlen] at hrun
    exact hrun
  intro ys
  induction ys with
  | nil =>
    intro curPtr curM found ans _ hfd
    have h0 : iterate lookupRadixStep (args.q, args.target) 0 ⟨curPtr, curM, found, ans⟩ =
        pure ⟨curPtr, curM, found, ans⟩ := rfl
    have hr : (Memory.spec 0).clientResult s
        (pure (⟨curPtr, curM, found, ans⟩ : LookupRadixState)) =
        ⟨curPtr, curM, found, ans⟩ := rfl
    rw [List.length_nil, h0, hr]
    dsimp only
    rcases hfd with ⟨rfl, rfl⟩ | rfl <;> simp [ofRadix]
  | cons v rest ih =>
    intro curPtr curM found ans hcur hfd
    rw [HoldsIn.cons_iff] at hcur
    obtain ⟨_, hmem_v, hrest⟩ := hcur
    simp only [List.length_cons]
    change ((Memory.spec 0).clientResult s
      (lookupRadixStep ((args.q, args.target), ⟨curPtr, curM, found, ans⟩) >>=
        iterate lookupRadixStep (args.q, args.target) rest.length)).ans = _
    rw [StateTransitionSpec.clientResult_bind]
    have hstep_res : (Memory.spec 0).clientResult s
        (lookupRadixStep ((args.q, args.target), ⟨curPtr, curM, found, ans⟩)) =
        ⟨curPtr + 1, curM / args.q,
         if (if found = 0 ∧ args.target = v then 1 else 0) = 1 then 1 else found,
         if (if found = 0 ∧ args.target = v then 1 else 0) = 1 then curM % args.q else ans⟩ := by
      dsimp only [lookupRadixStep]
      change (⟨curPtr + 1, curM / args.q, _, _⟩ : LookupRadixState) = _
      rw [hmem_v]
    rw [hstep_res]
    change ((Memory.spec 0).clientResult s
      (iterate lookupRadixStep (args.q, args.target) rest.length _)).ans = _
    rcases hfd with ⟨rfl, rfl⟩ | rfl
    · by_cases htv : v = args.target
      · subst htv
        simp only [and_self, ↓reduceIte, ofRadix]
        simpa using ih (curPtr + 1) (curM / args.q) 1 (curM % args.q) hrest (.inr rfl)
      · have htv' : args.target ≠ v := Ne.symm htv
        simp only [htv', and_false, ↓reduceIte, Nat.zero_ne_one, ofRadix]
        simpa using ih (curPtr + 1) (curM / args.q) 0 0 hrest (.inl ⟨rfl, rfl⟩)
    · simp only [Nat.one_ne_zero, false_and, ↓reduceIte]
      simpa using ih (curPtr + 1) (curM / args.q) 1 ans hrest (.inr rfl)

private theorem lookupRadixProg_spec {w : ℕ} (args : LookupRadixArgs)
    {LB : List ℕ} {s : Memory.State}
    (hLB : HoldsIn args.bagPtr LB s) (hlen : LB.length = args.bagLen) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (lookupRadixProg args)) ∧
    (Memory.spec 0).clientState s (lookupRadixProg args) = s ∧
    (Memory.spec 0).clientResult s (lookupRadixProg args) =
      ofRadix args.q LB args.m args.target ∧
    memoryCost (lookupRadixProg args) s ≤ args.bagLen := by
  have hcost : memoryCost (lookupRadixProg args) s ≤ args.bagLen := by
    unfold lookupRadixProg
    rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
    simpa only [Nat.one_mul] using
      memoryCost_iterate_le_of lookupRadixStep 1 (args.q, args.target)
        (fun _ _ => le_rfl) args.bagLen ⟨args.bagPtr, args.m, 0, 0⟩ s
  suffices ∀ ys st, HoldsIn st.curPtr ys s →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (iterate lookupRadixStep (args.q, args.target) ys.length st)) by
    have hv := this LB ⟨args.bagPtr, args.m, 0, 0⟩ hLB
    rw [hlen] at hv
    refine ⟨?_, lookupRadixProg_state args s, lookupRadixProg_result args hLB hlen, hcost⟩
    unfold lookupRadixProg
    exact validHistory_bind_step hv (validHistory_pure w _ _)
  intro ys
  induction ys with
  | nil =>
    intro st _
    have h0 : iterate lookupRadixStep (args.q, args.target) 0 st = pure st := rfl
    rw [List.length_nil, h0]
    exact validHistory_pure w s st
  | cons _ rest ih =>
    intro st hcur
    rw [HoldsIn.cons_iff] at hcur
    obtain ⟨hb, _, hrest⟩ := hcur
    have hlt : st.curPtr < s.frontier := by omega
    simp only [List.length_cons]
    exact validHistory_bind_step
      (validHistory_read_bind hlt (validHistory_pure w s _))
      (ih _ hrest)

private theorem lookupRadixProg_realizes :
    Realizes .exact lookupRadixProg WordEncoding.encode WordEncoding.encode
      (fun w args _ =>
        0 < args.q ∧ Fits w 1 ∧ Fits w args.q ∧ Fits w args.m ∧
        Fits w (args.bagPtr + args.bagLen))
      (fun _ _ => 0) := by
  unfold lookupRadixProg
  realize
  obtain ⟨hq_pos, h1, hfit_q, hfit_m, hfit_bag⟩ := h
  refine iterationSafe_of_stepInv _ _ w _
    (fun (j : ℕ) (st : LookupRadixState) (_ : Memory.State) =>
      st.curPtr + j = d.bagPtr + d.bagLen ∧
      st.curM ≤ d.m ∧ st.found ≤ 1 ∧ st.ans ≤ d.q)
    (fun j st m ⟨hptr, hm_le, hfd_le, hans_le⟩ => ?_)
    ⟨rfl, le_rfl, Nat.zero_le _, Nat.zero_le _⟩
  dsimp only [lookupRadixStep]
  have hq_ne : d.q ≠ 0 := by omega
  have hfit_ptr : Fits w (st.curPtr + 1) := hfit_bag.of_le (by omega)
  have hm_div : st.curM / d.q ≤ d.m := (Nat.div_le_self _ _).trans hm_le
  have hmod_le : st.curM % d.q ≤ d.q := le_of_lt (Nat.mod_lt _ hq_pos)
  have hfit_div : Fits w (st.curM / d.q) := hfit_m.of_le hm_div
  have hfit_mod : Fits w (st.curM % d.q) := hfit_q.of_le hmod_le
  have hfit_fd : Fits w st.found := h1.of_le hfd_le
  have hfit_ans : Fits w st.ans := hfit_q.of_le hans_le
  refine ⟨?_, ?_, hm_div, ?_, ?_⟩
  · repeat (
      first
      | split
      | exact trivial
      | assumption
      | refine And.intro ?_ ?_)
  · change (st.curPtr + 1) + j = d.bagPtr + d.bagLen; omega
  · change (if _ then 1 else st.found) ≤ 1; split_ifs <;> omega
  · change (if _ then _ else st.ans) ≤ d.q; split_ifs <;> omega

/-! ### General Horner radix projection (`radixProjProg`) -/

private structure RadixProjArgs where
  q : ℕ
  srcPtr : ℕ
  srcLen : ℕ
  srcM : ℕ
  updVar : ℕ
  updVal : ℕ
  hasUpd : ℕ
  dstPtr : ℕ
  dstLen : ℕ

private def RadixProjArgs.equiv :
    RadixProjArgs ≃ (((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a :=
    ((((((((a.q, a.srcPtr), a.srcLen), a.srcM), a.updVar), a.updVal), a.hasUpd), a.dstPtr),
      a.dstLen)
  invFun := fun ((((((((q, sp), sl), sm), uv), uval), hu), dp), dl) =>
    ⟨q, sp, sl, sm, uv, uval, hu, dp, dl⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding RadixProjArgs := .ofEquiv RadixProjArgs.equiv

private structure RadixProjState where
  remIdx : ℕ
  acc : ℕ

private def RadixProjState.equiv : RadixProjState ≃ ℕ × ℕ where
  toFun s := (s.remIdx, s.acc)
  invFun := fun (r, a) => ⟨r, a⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding RadixProjState := .ofEquiv RadixProjState.equiv

private def radixProjAssign (args : RadixProjArgs) (srcL : List ℕ) : ℕ → ℕ :=
  if args.hasUpd = 1 then
    Function.update (ofRadix args.q srcL args.srcM) args.updVar args.updVal
  else
    ofRadix args.q srcL args.srcM

private def radixProjStep (p : RadixProjArgs × RadixProjState) :
    Memory.Prog RadixProjState := do
  let a := p.1
  let st := p.2
  let idx := st.remIdx - 1
  let v ← Memory.read (a.dstPtr + idx)
  let looked ← lookupRadixProg ⟨a.q, a.srcPtr, a.srcLen, a.srcM, v⟩
  let val := if a.hasUpd = 1 ∧ v = a.updVar then a.updVal else looked
  pure ⟨idx, val % a.q + a.q * st.acc⟩

private def radixProjProg (args : RadixProjArgs) : Memory.Prog ℕ := do
  let res ← iterate radixProjStep args args.dstLen ⟨args.dstLen, 0⟩
  pure res.acc

private theorem radixProjStep_eval (a : RadixProjArgs) (st : RadixProjState) (t : Memory.State) :
    let idx := st.remIdx - 1
    let v := t.mem (a.dstPtr + idx)
    let looked := (Memory.spec 0).clientResult t
      (lookupRadixProg ⟨a.q, a.srcPtr, a.srcLen, a.srcM, v⟩)
    let val := if a.hasUpd = 1 ∧ v = a.updVar then a.updVal else looked
    (Memory.spec 0).clientState t (radixProjStep (a, st)) = t ∧
    (Memory.spec 0).clientResult t (radixProjStep (a, st)) =
      ⟨idx, val % a.q + a.q * st.acc⟩ := by
  have hr_st (x : ℕ) : (Memory.spec 0).clientState t (Memory.read x) = t := rfl
  have hr_res (x : ℕ) : (Memory.spec 0).clientResult t (Memory.read x) = t.mem x := rfl
  unfold radixProjStep
  dsimp only
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_st, hr_res,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    lookupRadixProg_state]
  exact ⟨rfl, rfl⟩

private theorem radixProjProg_state (args : RadixProjArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (radixProjProg args) = s := by
  unfold radixProjProg
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of radixProjStep args
    (fun st m => (radixProjStep_eval args st m).1) args.dstLen ⟨args.dstLen, 0⟩ s

private theorem radixProjProg_result_lt {args : RadixProjArgs} (hq : 0 < args.q)
    (s : Memory.State) :
    (Memory.spec 0).clientResult s (radixProjProg args) < args.q ^ args.dstLen := by
  unfold radixProjProg
  rw [StateTransitionSpec.clientResult_bind]
  suffices ∀ k st, st.acc < args.q ^ (args.dstLen - k) → k ≤ args.dstLen →
      ((Memory.spec 0).clientResult s (iterate radixProjStep args k st)).acc <
        args.q ^ args.dstLen from
    this args.dstLen ⟨args.dstLen, 0⟩
      (by simp only [Nat.sub_self, Nat.pow_zero]; exact Nat.zero_lt_one) le_rfl
  intro k
  induction k with
  | zero =>
    intro st hacc _
    have h0 : iterate radixProjStep args 0 st = pure st := rfl
    have hr : (Memory.spec 0).clientResult s (pure st) = st := rfl
    simpa only [h0, hr, Nat.sub_zero] using hacc
  | succ j ih =>
    intro st hacc hj_le
    obtain ⟨hst_ev, hres_ev⟩ := radixProjStep_eval args st s
    have hiter : iterate radixProjStep args (j + 1) st =
        (radixProjStep (args, st) >>= iterate radixProjStep args j) := rfl
    rw [hiter, StateTransitionSpec.clientResult_bind, hst_ev, hres_ev]
    refine ih _ ?_ (Nat.le_of_succ_le hj_le)
    dsimp only
    have hsub : args.dstLen - j = (args.dstLen - (j + 1)) + 1 := by omega
    have hmod : (if args.hasUpd = 1 ∧ s.mem (args.dstPtr + (st.remIdx - 1)) = args.updVar
        then args.updVal
        else (Memory.spec 0).clientResult s
          (lookupRadixProg ⟨args.q, args.srcPtr, args.srcLen, args.srcM,
            s.mem (args.dstPtr + (st.remIdx - 1))⟩)) % args.q < args.q :=
      Nat.mod_lt _ hq
    have hmul : args.q * (st.acc + 1) ≤ args.q * args.q ^ (args.dstLen - (j + 1)) :=
      Nat.mul_le_mul_left args.q hacc
    rw [hsub, Nat.pow_succ, Nat.mul_comm (args.q ^ _) args.q]
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega

private theorem radixProjProg_spec {w : ℕ} (args : RadixProjArgs)
    {srcL dstL : List ℕ} {s : Memory.State}
    (hsrc : HoldsIn args.srcPtr srcL s) (hsrc_len : srcL.length = args.srcLen)
    (hdst : HoldsIn args.dstPtr dstL s) (hdst_len : dstL.length = args.dstLen) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (radixProjProg args)) ∧
    (Memory.spec 0).clientState s (radixProjProg args) = s ∧
    (Memory.spec 0).clientResult s (radixProjProg args) =
      toRadix args.q dstL (radixProjAssign args srcL) ∧
    memoryCost (radixProjProg args) s ≤ args.dstLen * (args.srcLen + 1) := by
  let stepCost := args.srcLen + 1
  suffices ∀ rem (hrem : rem ≤ dstL.length),
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (iterate radixProjStep args rem
            ⟨rem, toRadix args.q (dstL.drop rem) (radixProjAssign args srcL)⟩)) ∧
      ((Memory.spec 0).clientResult s
        (iterate radixProjStep args rem
          ⟨rem, toRadix args.q (dstL.drop rem) (radixProjAssign args srcL)⟩)).acc =
        toRadix args.q dstL (radixProjAssign args srcL) ∧
      memoryCost
        (iterate radixProjStep args rem
          ⟨rem, toRadix args.q (dstL.drop rem) (radixProjAssign args srcL)⟩) s ≤
        rem * stepCost by
    have hrun := this dstL.length le_rfl
    rw [List.drop_length, toRadix_nil, hdst_len] at hrun
    refine ⟨?_, radixProjProg_state args s, ?_, ?_⟩
    · unfold radixProjProg
      exact validHistory_bind_step hrun.1 (validHistory_pure w _ _)
    · unfold radixProjProg
      rw [StateTransitionSpec.clientResult_bind]
      exact hrun.2.1
    · unfold radixProjProg
      rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
      exact hrun.2.2
  intro rem
  induction rem with
  | zero =>
    intro _
    have h0 : iterate radixProjStep args 0
        ⟨0, toRadix args.q (dstL.drop 0) (radixProjAssign args srcL)⟩ =
        pure ⟨0, toRadix args.q (dstL.drop 0) (radixProjAssign args srcL)⟩ := rfl
    rw [h0, List.drop_zero]
    exact ⟨validHistory_pure w s _, rfl, by simp [memoryCost_pure]⟩
  | succ k ih =>
    intro hk_le
    have hk_lt : k < dstL.length := hk_le
    have haddr_lt : args.dstPtr + k < s.frontier := by have := hdst.1; omega
    have hmem_v : s.mem (args.dstPtr + k) = dstL[k] := hdst.get k hk_lt
    obtain ⟨hv_lk, hst_lk, hr_lk, hc_lk⟩ :=
      lookupRadixProg_spec (w := w) ⟨args.q, args.srcPtr, args.srcLen, args.srcM, dstL[k]⟩
        hsrc hsrc_len
    dsimp only at hr_lk hc_lk
    let curAcc := toRadix args.q (dstL.drop (k + 1)) (radixProjAssign args srcL)
    obtain ⟨hst_step, hres_step⟩ := radixProjStep_eval args ⟨k + 1, curAcc⟩ s
    have hval_eq :
        (if args.hasUpd = 1 ∧ dstL[k] = args.updVar then args.updVal
         else ofRadix args.q srcL args.srcM dstL[k]) =
          radixProjAssign args srcL dstL[k] := by
      unfold radixProjAssign
      by_cases h1 : args.hasUpd = 1
      · by_cases h2 : dstL[k] = args.updVar
        · simp [h1, h2]
        · simp [h1, h2]
      · simp [h1]
    have hacc_next :
        radixProjAssign args srcL dstL[k] % args.q + args.q * curAcc =
          toRadix args.q (dstL.drop k) (radixProjAssign args srcL) := by
      have hdrop : dstL.drop k = dstL[k] :: dstL.drop (k + 1) :=
        List.drop_eq_getElem_cons hk_lt
      rw [hdrop, toRadix_cons]
    have hres_step' : (Memory.spec 0).clientResult s (radixProjStep (args, ⟨k + 1, curAcc⟩)) =
        ⟨k, toRadix args.q (dstL.drop k) (radixProjAssign args srcL)⟩ := by
      rw [hres_step]
      simp only [Nat.add_sub_cancel, hmem_v, hr_lk, hval_eq, hacc_next]
    have hv_step : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (radixProjStep (args, ⟨k + 1, curAcc⟩))) := by
      unfold radixProjStep
      dsimp only
      rw [Nat.add_sub_cancel]
      refine validHistory_read_bind haddr_lt ?_
      rw [hmem_v]
      exact validHistory_bind_step hv_lk (validHistory_pure w _ _)
    have hc_step : memoryCost (radixProjStep (args, ⟨k + 1, curAcc⟩)) s ≤ stepCost := by
      have hr_s (x : ℕ) : (Memory.spec 0).clientState s (Memory.read x) = s := rfl
      have hr_r (x : ℕ) : (Memory.spec 0).clientResult s (Memory.read x) = s.mem x := rfl
      unfold radixProjStep
      dsimp only
      rw [Nat.add_sub_cancel, memoryCost_bind', memoryCost_read, hr_s, hr_r, hmem_v,
        memoryCost_bind', hst_lk, memoryCost_pure]
      dsimp only [stepCost]
      omega
    obtain ⟨hv_rem, hr_rem, hc_rem⟩ := ih (Nat.le_of_succ_le hk_le)
    have hiter_eq : iterate radixProjStep args (k + 1) ⟨k + 1, curAcc⟩ =
        (radixProjStep (args, ⟨k + 1, curAcc⟩) >>= iterate radixProjStep args k) := rfl
    rw [hiter_eq]
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_step, hres_step']), ?_, ?_⟩
    · rw [StateTransitionSpec.clientResult_bind, hst_step, hres_step']
      exact hr_rem
    · rw [memoryCost_bind', hst_step, hres_step']
      calc memoryCost (radixProjStep (args, ⟨k + 1, curAcc⟩)) s +
            memoryCost
              (iterate radixProjStep args k
                ⟨k, toRadix args.q (dstL.drop k) (radixProjAssign args srcL)⟩) s
          ≤ stepCost + k * stepCost := Nat.add_le_add hc_step hc_rem
        _ = (k + 1) * stepCost := by ring

private theorem radixProjProg_realizes :
    Realizes .exact radixProjProg WordEncoding.encode WordEncoding.encode
      (fun w args _ =>
        0 < args.q ∧ Fits w 1 ∧ Fits w args.q ∧ Fits w args.srcM ∧
        Fits w (args.srcPtr + args.srcLen) ∧
        Fits w (args.dstPtr + args.dstLen) ∧
        Fits w (args.q ^ args.dstLen))
      (fun _ _ => 0) := by
  unfold radixProjProg
  realize [lookupRadixProg_realizes]
  obtain ⟨hq_pos, h1, hfit_q, hfit_srcM, hfit_src, hfit_dst, hfit_pow⟩ := h
  refine iterationSafe_of_stepInv _ _ w _
    (fun (j : ℕ) (st : RadixProjState) (_ : Memory.State) =>
      j ≤ d.dstLen ∧ st.remIdx = j ∧ st.acc < d.q ^ (d.dstLen - j))
    (fun j st m ⟨hj_le, hrem_eq, hacc_lt⟩ => ?_)
    ⟨le_rfl, rfl, by simp only [Nat.sub_self, Nat.pow_zero]; exact Nat.zero_lt_one⟩
  have hst_eta : st = ⟨j + 1, st.acc⟩ := by
    cases st
    dsimp only at hrem_eq
    subst hrem_eq
    rfl
  rw [hst_eta]
  have hsub_pow : d.dstLen - j = (d.dstLen - (j + 1)) + 1 := by omega
  have hnext_lt : ∀ v, v % d.q + d.q * st.acc < d.q ^ (d.dstLen - j) := fun v => by
    have hmod : v % d.q < d.q := Nat.mod_lt v hq_pos
    have hmul : d.q * (st.acc + 1) ≤ d.q * d.q ^ (d.dstLen - (j + 1)) :=
      Nat.mul_le_mul_left d.q hacc_lt
    rw [hsub_pow, Nat.pow_succ, Nat.mul_comm (d.q ^ _) d.q]
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega
  have hpow_le : d.q ^ (d.dstLen - j) ≤ d.q ^ d.dstLen :=
    Nat.pow_le_pow_right hq_pos (Nat.sub_le _ _)
  have hlk_safe :
      0 < d.q ∧ Fits w 1 ∧ Fits w d.q ∧ Fits w d.srcM ∧ Fits w (d.srcPtr + d.srcLen) :=
    ⟨hq_pos, h1, hfit_q, hfit_srcM, hfit_src⟩
  have h1_le : 1 ≤ j + 1 := by omega
  have hfit_sub : Fits w (j + 1 - 1) := hfit_dst.of_le (by omega)
  have hfit_addr : Fits w (d.dstPtr + (j + 1 - 1)) := hfit_dst.of_le (by omega)
  have hq_ne : d.q ≠ 0 := by omega
  have hfit_mul : Fits w (d.q * st.acc) := by
    have h0 : d.q * st.acc < d.q ^ (d.dstLen - j) := by simpa using hnext_lt 0
    exact hfit_pow.of_le (le_of_lt (h0.trans_le hpow_le))
  have hfit_next (v : ℕ) : Fits w (v % d.q + d.q * st.acc) :=
    hfit_pow.of_le (le_of_lt ((hnext_lt v).trans_le hpow_le))
  have hfit_upd : Fits w (d.updVal % d.q + d.q * st.acc) := hfit_next d.updVal
  let lkVal := (Memory.spec 0).clientResult m
    (lookupRadixProg ⟨d.q, d.srcPtr, d.srcLen, d.srcM, m.mem (d.dstPtr + (j + 1 - 1))⟩)
  have hfit_lk : Fits w (lkVal % d.q + d.q * st.acc) := hfit_next lkVal
  obtain ⟨_, hres_ev⟩ := radixProjStep_eval d ⟨j + 1, st.acc⟩ m
  refine ⟨?_, Nat.le_of_succ_le hj_le, ?_, ?_⟩
  · dsimp only [radixProjStep]
    repeat (
      first
      | split
      | exact hlk_safe
      | assumption
      | refine And.intro ?_ ?_)
  · rw [hres_ev]; exact Nat.add_sub_cancel j 1
  · rw [hres_ev]; exact hnext_lt _

/-! ### Scope subset test (`subsetBagProg`) and bag erasure (`eraseBagProg`) -/

private structure SubsetBagArgs where
  scopePtr : ℕ
  scopeLen : ℕ
  bagPtr : ℕ
  bagLen : ℕ

private def SubsetBagArgs.equiv : SubsetBagArgs ≃ ((ℕ × ℕ) × ℕ) × ℕ where
  toFun a := (((a.scopePtr, a.scopeLen), a.bagPtr), a.bagLen)
  invFun := fun (((sp, sl), bp), bl) => ⟨sp, sl, bp, bl⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding SubsetBagArgs := .ofEquiv SubsetBagArgs.equiv

private structure SubScanState where
  cur : ℕ
  found : ℕ

private def SubScanState.equiv : SubScanState ≃ ℕ × ℕ where
  toFun s := (s.cur, s.found)
  invFun := fun (cur, found) => ⟨cur, found⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding SubScanState := .ofEquiv SubScanState.equiv

private def subsetBagStep (p : (ℕ × ℕ) × SubScanState) : Memory.Prog SubScanState := do
  let bagPtr := p.1.1
  let bagLen := p.1.2
  let st := p.2
  let u ← Memory.read st.cur
  let mem ← bagMemProg ⟨u, bagPtr, bagLen⟩
  pure ⟨st.cur + 1, if mem = 1 then st.found else 0⟩

private def subsetBagProg (args : SubsetBagArgs) : Memory.Prog ℕ := do
  let res ← iterate subsetBagStep (args.bagPtr, args.bagLen) args.scopeLen ⟨args.scopePtr, 1⟩
  pure res.found

private theorem subsetBagStep_eval (bp bl : ℕ) (st : SubScanState) (t : Memory.State) :
    let u := t.mem st.cur
    let mem := (Memory.spec 0).clientResult t (bagMemProg ⟨u, bp, bl⟩)
    (Memory.spec 0).clientState t (subsetBagStep ((bp, bl), st)) = t ∧
    (Memory.spec 0).clientResult t (subsetBagStep ((bp, bl), st)) =
      ⟨st.cur + 1, if mem = 1 then st.found else 0⟩ := by
  have hr_st (x : ℕ) : (Memory.spec 0).clientState t (Memory.read x) = t := rfl
  have hr_res (x : ℕ) : (Memory.spec 0).clientResult t (Memory.read x) = t.mem x := rfl
  unfold subsetBagStep
  dsimp only
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_st, hr_res,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    bagMemProg_state]
  exact ⟨rfl, rfl⟩

private theorem subsetBagProg_state (args : SubsetBagArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (subsetBagProg args) = s := by
  unfold subsetBagProg
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of subsetBagStep (args.bagPtr, args.bagLen)
    (fun st m => (subsetBagStep_eval args.bagPtr args.bagLen st m).1)
    args.scopeLen ⟨args.scopePtr, 1⟩ s

private theorem ite_one_zero_congr {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    (if P then 1 else 0) = (if Q then 1 else 0) := by
  by_cases hp : P
  · rw [ite_eq_left hp, ite_eq_left (h.1 hp)]
  · rw [ite_eq_right hp, ite_eq_right (mt h.2 hp)]

private theorem subsetBagProg_spec {w : ℕ} (args : SubsetBagArgs)
    {scopeL bagL : List ℕ} {s : Memory.State}
    (hscope : HoldsIn args.scopePtr scopeL s) (hscope_len : scopeL.length = args.scopeLen)
    (hbag : HoldsIn args.bagPtr bagL s) (hbag_len : bagL.length = args.bagLen) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (subsetBagProg args)) ∧
    (Memory.spec 0).clientState s (subsetBagProg args) = s ∧
    (Memory.spec 0).clientResult s (subsetBagProg args) =
      (if decide (scopeL.toFinset ⊆ bagL.toFinset) then 1 else 0) ∧
    memoryCost (subsetBagProg args) s ≤ args.scopeLen * (args.bagLen + 1) := by
  let stepCost := args.bagLen + 1
  suffices ∀ ys cur ok,
      HoldsIn cur ys s →
      (ok = 0 ∨ ok = 1) →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (iterate subsetBagStep (args.bagPtr, args.bagLen) ys.length ⟨cur, ok⟩)) ∧
      ((Memory.spec 0).clientResult s
        (iterate subsetBagStep (args.bagPtr, args.bagLen) ys.length ⟨cur, ok⟩)).found =
        (if ok = 1 ∧ ∀ u ∈ ys, u ∈ bagL then 1 else 0) ∧
      memoryCost (iterate subsetBagStep (args.bagPtr, args.bagLen) ys.length ⟨cur, ok⟩) s ≤
        ys.length * stepCost by
    have hrun := this scopeL args.scopePtr 1 hscope (.inr rfl)
    rw [hscope_len] at hrun
    have hsub_iff : (∀ u ∈ scopeL, u ∈ bagL) ↔ scopeL.toFinset ⊆ bagL.toFinset := by
      simp [Finset.subset_iff]
    refine ⟨?_, subsetBagProg_state args s, ?_, ?_⟩
    · unfold subsetBagProg
      exact validHistory_bind_step hrun.1 (validHistory_pure w _ _)
    · unfold subsetBagProg
      rw [StateTransitionSpec.clientResult_bind, hrun.2.1]
      exact ite_one_zero_congr (by simp [hsub_iff])
    · unfold subsetBagProg
      rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
      exact hrun.2.2
  intro ys
  induction ys with
  | nil =>
    intro cur ok _ hok
    have h0 : iterate subsetBagStep (args.bagPtr, args.bagLen) 0 ⟨cur, ok⟩ = pure ⟨cur, ok⟩ := rfl
    have hr : (Memory.spec 0).clientResult s (pure (⟨cur, ok⟩ : SubScanState)) = ⟨cur, ok⟩ := rfl
    rw [List.length_nil, h0]
    refine ⟨validHistory_pure w s _, ?_, by simp [memoryCost_pure]⟩
    rw [hr]
    rcases hok with rfl | rfl <;> simp
  | cons u rest ih =>
    intro cur ok hcur hok
    rw [HoldsIn.cons_iff] at hcur
    obtain ⟨hb, hmem_u, hrest⟩ := hcur
    have hlt : cur < s.frontier := by omega
    obtain ⟨hv_bm, hst_bm, hr_bm, hc_bm⟩ :=
      bagMemProg_spec (w := w) ⟨u, args.bagPtr, args.bagLen⟩ hbag hbag_len
    dsimp only at hr_bm hc_bm
    let ok' := if (if memBag u bagL then 1 else 0) = 1 then ok else 0
    have hok' : ok' = 0 ∨ ok' = 1 := by
      dsimp only [ok']
      by_cases hm : (if memBag u bagL then 1 else 0) = 1
      · rw [ite_eq_left hm]; exact hok
      · rw [ite_eq_right hm]; exact .inl rfl
    obtain ⟨hst_step, hres_step⟩ := subsetBagStep_eval args.bagPtr args.bagLen ⟨cur, ok⟩ s
    have hres_step' :
        (Memory.spec 0).clientResult s
          (subsetBagStep ((args.bagPtr, args.bagLen), ⟨cur, ok⟩)) = ⟨cur + 1, ok'⟩ := by
      rw [hres_step]
      simp only [hmem_u, hr_bm, ok']
    have hv_step : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (subsetBagStep ((args.bagPtr, args.bagLen), ⟨cur, ok⟩))) := by
      unfold subsetBagStep
      dsimp only
      refine validHistory_read_bind hlt ?_
      rw [hmem_u]
      exact validHistory_bind_step hv_bm (validHistory_pure w _ _)
    have hc_step :
        memoryCost (subsetBagStep ((args.bagPtr, args.bagLen), ⟨cur, ok⟩)) s ≤ stepCost := by
      have hr_s (x : ℕ) : (Memory.spec 0).clientState s (Memory.read x) = s := rfl
      have hr_r (x : ℕ) : (Memory.spec 0).clientResult s (Memory.read x) = s.mem x := rfl
      unfold subsetBagStep
      dsimp only
      rw [memoryCost_bind', memoryCost_read, hr_s, hr_r, hmem_u,
        memoryCost_bind', hst_bm, memoryCost_pure]
      dsimp only [stepCost]
      omega
    obtain ⟨hv_rem, hr_rem, hc_rem⟩ := ih (cur + 1) ok' hrest hok'
    simp only [List.length_cons]
    have hiter_eq :
        iterate subsetBagStep (args.bagPtr, args.bagLen) (rest.length + 1) ⟨cur, ok⟩ =
          (subsetBagStep ((args.bagPtr, args.bagLen), ⟨cur, ok⟩) >>=
            iterate subsetBagStep (args.bagPtr, args.bagLen) rest.length) := rfl
    rw [hiter_eq]
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_step, hres_step']), ?_, ?_⟩
    · rw [StateTransitionSpec.clientResult_bind, hst_step, hres_step', hr_rem]
      refine ite_one_zero_congr ?_
      dsimp only [ok']
      rw [memBag_eq_decide]
      rcases hok with rfl | rfl
      · simp
      · by_cases hu : u ∈ bagL <;> simp [hu]
    · rw [memoryCost_bind', hst_step, hres_step']
      calc _ ≤ stepCost + rest.length * stepCost := Nat.add_le_add hc_step hc_rem
        _ = (rest.length + 1) * stepCost := by ring

private theorem subsetBagProg_realizes :
    Realizes .exact subsetBagProg WordEncoding.encode WordEncoding.encode
      (fun w args _ =>
        Fits w 1 ∧ Fits w (args.scopePtr + args.scopeLen) ∧ Fits w (args.bagPtr + args.bagLen))
      (fun _ _ => 0) := by
  unfold subsetBagProg
  realize [bagMemProg_realizes]
  · exact h.1
  · obtain ⟨h1, hfit_sc, hfit_bg⟩ := h
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : SubScanState) (_ : Memory.State) =>
        st.cur + j = d.scopePtr + d.scopeLen ∧ st.found ≤ 1)
      (fun j st m ⟨hcur, hfd⟩ => ?_)
      ⟨rfl, le_rfl⟩
    have hbm_safe : Fits w 1 ∧ Fits w (d.bagPtr + d.bagLen) := ⟨h1, hfit_bg⟩
    have hfit_cur1 : Fits w (st.cur + 1) := hfit_sc.of_le (by omega)
    have hfit_fd : Fits w st.found := h1.of_le hfd
    obtain ⟨_, hres_ev⟩ := subsetBagStep_eval d.bagPtr d.bagLen st m
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [subsetBagStep]
      repeat (
        first
        | split
        | exact hbm_safe
        | assumption
        | refine And.intro ?_ ?_)
    · rw [hres_ev]; dsimp only; omega
    · rw [hres_ev]; dsimp only; split_ifs <;> omega

/-! ### Materialized bag erasure (`eraseBagProg`) -/

private structure EraseState where
  srcCur : ℕ
  dstCur : ℕ
  skipped : ℕ

private def EraseState.equiv : EraseState ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.srcCur, s.dstCur), s.skipped)
  invFun := fun ((sc, dc), sk) => ⟨sc, dc, sk⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding EraseState := .ofEquiv EraseState.equiv

private def eraseCopyStep (env : ℕ × EraseState) : Memory.Prog EraseState := do
  let target := env.1
  let st := env.2
  let x ← Memory.read st.srcCur
  if st.skipped = 0 ∧ x = target then
    pure ⟨st.srcCur + 1, st.dstCur, 1⟩
  else do
    Memory.write st.dstCur x
    pure ⟨st.srcCur + 1, st.dstCur + 1, st.skipped⟩

private theorem eraseCopyStep_eval (target : ℕ) (st : EraseState) (t : Memory.State) :
    let x := t.mem st.srcCur
    (Memory.spec 0).clientState t (eraseCopyStep (target, st)) =
      (if st.skipped = 0 ∧ x = target then t
       else ⟨Function.update t.mem st.dstCur x, t.frontier⟩) ∧
    (Memory.spec 0).clientResult t (eraseCopyStep (target, st)) =
      (if st.skipped = 0 ∧ x = target then ⟨st.srcCur + 1, st.dstCur, 1⟩
       else ⟨st.srcCur + 1, st.dstCur + 1, st.skipped⟩) ∧
    memoryCost (eraseCopyStep (target, st)) t ≤ 2 := by
  have hr_st : (Memory.spec 0).clientState t (Memory.read st.srcCur) = t := rfl
  have hr_res : (Memory.spec 0).clientResult t (Memory.read st.srcCur) = t.mem st.srcCur := rfl
  unfold eraseCopyStep
  dsimp only
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    memoryCost_bind', memoryCost_read, hr_st, hr_res]
  by_cases hc : st.skipped = 0 ∧ t.mem st.srcCur = target
  · rw [ite_eq_left hc, ite_eq_left hc, ite_eq_left hc, memoryCost_pure]
    exact ⟨rfl, rfl, by omega⟩
  · rw [ite_eq_right hc, ite_eq_right hc, ite_eq_right hc,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
      memoryCost_bind', memoryCost_write, memoryCost_pure]
    exact ⟨rfl, rfl, by omega⟩

private def eraseBagProg (args : BagScanArgs) : Memory.Prog (ℕ × ℕ) := do
  let hasV ← bagMemProg args
  let bagLen := args.len - hasV
  let bagPtr ← Memory.allocDirty bagLen
  let _ ← iterate eraseCopyStep args.target args.len ⟨args.base, bagPtr, 0⟩
  pure (bagPtr, bagLen)

private theorem eraseBagProg_spec {w : ℕ} (args : BagScanArgs)
    {xs : List ℕ} {s : Memory.State}
    (hxs : HoldsIn args.base xs s) (hlen : xs.length = args.len)
    (hfit_elems : ∀ u ∈ xs, Fits w u)
    (hfit_fr : Fits w (s.frontier + (xs.erase args.target).length)) :
    let bagLen := (xs.erase args.target).length
    let s₁ := (Memory.spec 0).clientState s (eraseBagProg args)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (eraseBagProg args)) ∧
    (Memory.spec 0).clientResult s (eraseBagProg args) = (s.frontier, bagLen) ∧
    s₁.frontier = s.frontier + bagLen ∧
    PreservesBelow s.frontier s s₁ ∧
    HoldsIn s.frontier (xs.erase args.target) s₁ ∧
    memoryCost (eraseBagProg args) s ≤ 3 * args.len + 1 := by
  obtain ⟨hv_bm, hst_bm, hr_bm, hc_bm⟩ := bagMemProg_spec (w := w) args hxs hlen
  have hlen_er :
      args.len - (if memBag args.target xs then 1 else 0) =
        (xs.erase args.target).length := by
    rw [memBag_eq_decide]
    by_cases hm : args.target ∈ xs
    · simp only [hm, decide_true, ↓reduceIte, ← hlen]
      exact (List.length_erase_of_mem hm).symm
    · simp [hm, List.erase_of_not_mem hm, hlen]
  let bagLen := (xs.erase args.target).length
  let bagPtr := s.frontier
  let s_a := (Memory.spec 0).clientState s (Memory.allocDirty bagLen)
  have hp_a : PreservesBelow bagPtr s s_a := preservesBelow_allocDirty s bagLen
  have hv_a : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (Memory.allocDirty bagLen)) :=
    validHistory_allocDirty hfit_fr
  suffices ∀ ys srcCur written skipped t,
      (∀ u ∈ ys, Fits w u) →
      srcCur + ys.length ≤ bagPtr →
      t.frontier = bagPtr + bagLen →
      PreservesBelow bagPtr s t →
      HoldsIn srcCur ys t →
      HoldsIn bagPtr written t →
      (skipped = 0 ∨ skipped = 1) →
      written ++ (if skipped = 1 then ys else ys.erase args.target) = xs.erase args.target →
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t
          (iterate eraseCopyStep args.target ys.length
            ⟨srcCur, bagPtr + written.length, skipped⟩)) ∧
      (let tEnd := (Memory.spec 0).clientState t
         (iterate eraseCopyStep args.target ys.length
           ⟨srcCur, bagPtr + written.length, skipped⟩)
       tEnd.frontier = bagPtr + bagLen ∧
       PreservesBelow bagPtr s tEnd ∧
       HoldsIn bagPtr (xs.erase args.target) tEnd) ∧
      memoryCost
        (iterate eraseCopyStep args.target ys.length
          ⟨srcCur, bagPtr + written.length, skipped⟩) t ≤ 2 * ys.length by
    have hrun := this xs args.base [] 0 s_a hfit_elems hxs.1 rfl hp_a
      (hxs.mono_frontier hp_a) (HoldsIn.nil (Nat.le_add_right _ _)) (.inl rfl)
      (by simp)
    simp only [List.length_nil, Nat.add_zero, hlen] at hrun
    obtain ⟨hv_loop, ⟨hfr_end, hp_end, hbag_end⟩, hc_loop⟩ := hrun
    unfold eraseBagProg
    dsimp only
    have ha_st : (Memory.spec 0).clientState s (Memory.allocDirty bagLen) = s_a := rfl
    have ha_res : (Memory.spec 0).clientResult s (Memory.allocDirty bagLen) = bagPtr := rfl
    refine ⟨validHistory_bind_step hv_bm ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hst_bm, hr_bm, hlen_er]
      refine validHistory_bind_step hv_a ?_
      rw [ha_st, ha_res]
      exact validHistory_bind_step hv_loop (validHistory_pure w _ _)
    · rw [StateTransitionSpec.clientResult_bind, hst_bm, hr_bm, hlen_er,
        StateTransitionSpec.clientResult_bind, ha_st, ha_res,
        StateTransitionSpec.clientResult_bind]
      rfl
    · rw [StateTransitionSpec.clientState_bind, hst_bm, hr_bm, hlen_er,
        StateTransitionSpec.clientState_bind, ha_st, ha_res,
        StateTransitionSpec.clientState_bind]
      exact hfr_end
    · rw [StateTransitionSpec.clientState_bind, hst_bm, hr_bm, hlen_er,
        StateTransitionSpec.clientState_bind, ha_st, ha_res,
        StateTransitionSpec.clientState_bind]
      exact hp_end
    · rw [StateTransitionSpec.clientState_bind, hst_bm, hr_bm, hlen_er,
        StateTransitionSpec.clientState_bind, ha_st, ha_res,
        StateTransitionSpec.clientState_bind]
      exact hbag_end
    · rw [memoryCost_bind', hst_bm, hr_bm, hlen_er,
        memoryCost_bind', memoryCost_allocDirty, ha_st, ha_res,
        memoryCost_bind', memoryCost_pure, Nat.add_zero]
      omega
  intro ys
  induction ys with
  | nil =>
    intro srcCur written skipped t _ _ hfr hpres _ hwr hsk hconcat
    have h0 : iterate eraseCopyStep args.target 0
        ⟨srcCur, bagPtr + written.length, skipped⟩ =
        pure ⟨srcCur, bagPtr + written.length, skipped⟩ := rfl
    rw [List.length_nil, h0]
    have hwr_eq : written = xs.erase args.target := by
      rcases hsk with rfl | rfl <;> simpa using hconcat
    rw [hwr_eq] at hwr
    exact ⟨validHistory_pure w t _, ⟨hfr, hpres, hwr⟩, by simp [memoryCost_pure]⟩
  | cons x rest ih =>
    intro srcCur written skipped t hfit_ys hsrc_end hfr hpres hys hwr hsk hconcat
    rw [HoldsIn.cons_iff] at hys
    obtain ⟨_, hmem_x, hrest⟩ := hys
    have hsrc_lt : srcCur < t.frontier := by simp only [List.length_cons] at hsrc_end; omega
    have hx_fit : Fits w x := hfit_ys x List.mem_cons_self
    have hfit_rest : ∀ u ∈ rest, Fits w u := fun u hu => hfit_ys u (List.mem_cons_of_mem _ hu)
    simp only [List.length_cons] at hsrc_end ⊢
    have hiter_eq : iterate eraseCopyStep args.target (rest.length + 1)
        ⟨srcCur, bagPtr + written.length, skipped⟩ =
      (eraseCopyStep (args.target, ⟨srcCur, bagPtr + written.length, skipped⟩) >>=
        iterate eraseCopyStep args.target rest.length) := rfl
    obtain ⟨hst_ev, hres_ev, hc_step⟩ :=
      eraseCopyStep_eval args.target ⟨srcCur, bagPtr + written.length, skipped⟩ t
    dsimp only at hst_ev hres_ev
    rw [hmem_x] at hst_ev hres_ev
    by_cases hskip_cond : skipped = 0 ∧ x = args.target
    · rw [ite_eq_left hskip_cond] at hst_ev hres_ev
      obtain ⟨rfl, rfl⟩ := hskip_cond
      have hv_step : (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t
            (eraseCopyStep (args.target, ⟨srcCur, bagPtr + written.length, 0⟩))) := by
        unfold eraseCopyStep
        dsimp only
        refine validHistory_read_bind hsrc_lt ?_
        rw [hmem_x, ite_eq_left ⟨rfl, rfl⟩]
        exact validHistory_pure w t _
      have hconcat' : written ++ (if (1 : ℕ) = 1 then rest else rest.erase args.target) =
          xs.erase args.target := by
        simpa [List.erase_cons] using hconcat
      obtain ⟨hv_rem, hprops_rem, hc_rem⟩ :=
        ih (srcCur + 1) written 1 t hfit_rest (by omega) hfr hpres hrest hwr (.inr rfl) hconcat'
      rw [hiter_eq]
      refine ⟨validHistory_bind_step hv_step (by rwa [hst_ev, hres_ev]), ?_, ?_⟩
      · rw [StateTransitionSpec.clientState_bind, hst_ev, hres_ev]
        exact hprops_rem
      · rw [memoryCost_bind', hst_ev, hres_ev]
        omega
    · rw [ite_eq_right hskip_cond] at hst_ev hres_ev
      have htail_eq :
          (if skipped = 1 then x :: rest else (x :: rest).erase args.target) =
            x :: (if skipped = 1 then rest else rest.erase args.target) := by
        rcases hsk with rfl | rfl
        · have hne : x ≠ args.target := fun hx => hskip_cond ⟨rfl, hx⟩
          simp [beq_eq_false_iff_ne.2 hne]
        · simp
      have hlen_sum : written.length + 1 +
          (if skipped = 1 then rest else rest.erase args.target).length = bagLen := by
        have hc_len := congrArg List.length hconcat
        rw [htail_eq, List.length_append, List.length_cons] at hc_len
        dsimp only [bagLen]
        omega
      have hdst_lt : bagPtr + written.length < t.frontier := by omega
      let t₁ : Memory.State := ⟨Function.update t.mem (bagPtr + written.length) x, t.frontier⟩
      have hres_ev' :
          (Memory.spec 0).clientResult t
            (eraseCopyStep (args.target, ⟨srcCur, bagPtr + written.length, skipped⟩)) =
            ⟨srcCur + 1, bagPtr + (written ++ [x]).length, skipped⟩ := by
        rw [hres_ev]
        simp [Nat.add_assoc]
      have hv_step : (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t
            (eraseCopyStep (args.target, ⟨srcCur, bagPtr + written.length, skipped⟩))) := by
        unfold eraseCopyStep
        dsimp only
        refine validHistory_read_bind hsrc_lt ?_
        rw [hmem_x, ite_eq_right hskip_cond]
        exact validHistory_write_bind hdst_lt hx_fit (validHistory_pure w t₁ _)
      have hp₁ : PreservesBelow bagPtr t t₁ :=
        preservesBelow_write (Nat.le_add_right _ _) hdst_lt
      have hrest₁ : HoldsIn (srcCur + 1) rest t₁ :=
        hrest.mono (F := bagPtr) (by omega) hp₁
      have hwr₁ : HoldsIn bagPtr (written ++ [x]) t₁ :=
        holdsIn_append_one hwr (by omega)
      have hconcat₁ :
          (written ++ [x]) ++ (if skipped = 1 then rest else rest.erase args.target) =
            xs.erase args.target := by
        rw [List.append_assoc, List.singleton_append, ← htail_eq]
        exact hconcat
      obtain ⟨hv_rem, hprops_rem, hc_rem⟩ :=
        ih (srcCur + 1) (written ++ [x]) skipped t₁ hfit_rest (by omega) hfr
          (hpres.trans hp₁) hrest₁ hwr₁ hsk hconcat₁
      rw [hiter_eq]
      refine ⟨validHistory_bind_step hv_step (by rwa [hst_ev, hres_ev']), ?_, ?_⟩
      · rw [StateTransitionSpec.clientState_bind, hst_ev, hres_ev']
        exact hprops_rem
      · rw [memoryCost_bind', hst_ev, hres_ev']
        dsimp only [t₁] at hc_rem
        omega

private theorem eraseBagProg_realizes :
    Realizes .exact eraseBagProg WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 1 ∧
        ∃ xs,
          HoldsIn args.base xs s ∧
          xs.length = args.len ∧
          args.base + args.len ≤ s.frontier ∧
          (∀ u ∈ xs, Fits w u) ∧
          Fits w (s.frontier + args.len))
      (fun _ _ => 0) := by
  unfold eraseBagProg
  realize [bagMemProg_realizes]
  · exact h.1
  · obtain ⟨_, _, _, _, hbase_le, _, hfit_fr⟩ := h
    exact hfit_fr.of_le (by omega)
  · obtain ⟨_, xs, hxs, hlen, _, _, _⟩ := h
    obtain ⟨_, _, hr_bm, _⟩ := bagMemProg_spec (w := w) d hxs hlen
    rw [hr_bm, memBag_eq_decide]
    by_cases hm : d.target ∈ xs
    · simp only [hm, decide_true, ↓reduceIte, ← hlen]
      exact List.length_pos_of_mem hm
    · simp [hm]
  · obtain ⟨h1, xs, hxs, hlen, hbase_le, hfit_elems, hfit_fr⟩ := h
    obtain ⟨_, hst_bm, hr_bm, _⟩ := bagMemProg_spec (w := w) d hxs hlen
    rw [hst_bm, hr_bm]
    have hlen_er :
        d.len - (if memBag d.target xs then 1 else 0) =
          (xs.erase d.target).length := by
      rw [memBag_eq_decide]
      by_cases hm : d.target ∈ xs
      · simp only [hm, decide_true, ↓reduceIte, ← hlen]
        exact (List.length_erase_of_mem hm).symm
      · simp [hm, List.erase_of_not_mem hm, hlen]
    let bagLen := (xs.erase d.target).length
    have hbagLen_le : bagLen ≤ d.len := by
      dsimp only [bagLen]; rw [← hlen]; exact List.length_erase_le
    let s_a : Memory.State := { mem := s.mem, frontier := s.frontier + bagLen }
    have hp_a : PreservesBelow s.frontier s s_a := ⟨le_rfl, Nat.le_add_right _ _, fun _ _ => rfl⟩
    rw [hlen_er]
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : EraseState) (t : Memory.State) =>
        j ≤ d.len ∧
        st.srcCur + j = d.base + d.len ∧
        s.frontier ≤ st.dstCur ∧
        st.dstCur ≤ s.frontier + (d.len - j) ∧
        st.skipped ≤ 1 ∧
        HoldsIn st.srcCur (xs.drop (d.len - j)) t)
      (fun j st t ⟨hj_le, hsrc_eq, hdst_lo, hdst_hi, hsk_le, hdrop_t⟩ => ?_)
      ⟨le_rfl, by simp, le_rfl, by simp, Nat.zero_le _,
        by dsimp only; rw [Nat.sub_self, List.drop_zero]; exact hxs.mono_frontier hp_a⟩
    have hidx_lt : d.len - (j + 1) < xs.length := by omega
    have hdrop_cons : xs.drop (d.len - (j + 1)) =
        xs[d.len - (j + 1)] :: xs.drop (d.len - j) := by
      have heq : d.len - (j + 1) + 1 = d.len - j := by omega
      rw [← heq]
      exact List.drop_eq_getElem_cons hidx_lt
    rw [hdrop_cons, HoldsIn.cons_iff] at hdrop_t
    obtain ⟨_, hmem_cur, hrest_t⟩ := hdrop_t
    have hx_fit : Fits w (t.mem st.srcCur) := by
      rw [hmem_cur]
      exact hfit_elems _ (List.getElem_mem hidx_lt)
    have hfit_src1 : Fits w (st.srcCur + 1) := hfit_fr.of_le (by omega)
    have hfit_dst : Fits w st.dstCur := hfit_fr.of_le (by omega)
    have hfit_dst1 : Fits w (st.dstCur + 1) := hfit_fr.of_le (by omega)
    have hfit_sk : Fits w st.skipped := h1.of_le hsk_le
    obtain ⟨hst_ev, hres_ev, _⟩ := eraseCopyStep_eval d.target st t
    dsimp only at hst_ev hres_ev
    refine ⟨?_, Nat.le_of_succ_le hj_le, ?_⟩
    · dsimp only [eraseCopyStep]
      repeat (
        first
        | split
        | assumption
        | refine And.intro ?_ ?_)
    · rw [hst_ev, hres_ev]
      by_cases hc : st.skipped = 0 ∧ t.mem st.srcCur = d.target
      · rw [ite_eq_left hc, ite_eq_left hc]
        exact ⟨by dsimp only; omega, hdst_lo,
          hdst_hi.trans (Nat.add_le_add_left (by omega) _), le_rfl, hrest_t⟩
      · rw [ite_eq_right hc, ite_eq_right hc]
        dsimp only
        refine ⟨by omega, by omega, by omega, hsk_le, hrest_t.1,
          hrest_t.2.frame fun a _ ha => ?_⟩
        have hdl : (xs.drop (d.len - j)).length = j := by simp [hlen]; omega
        exact Function.update_of_ne (by omega) _ t.mem

/-! ### Constraint-list scans for `leaf` and `introduce` nodes -/

private def checkLeafStep (env : Unit × SubScanState) : Memory.Prog SubScanState := do
  let st := env.2
  let scopeLen ← Memory.read st.cur
  let tblLen ← Memory.read (st.cur + 1)
  let t0 ← Memory.read (st.cur + 2 + scopeLen)
  let ok' := if scopeLen = 0 then (if t0 = 1 then st.found else 0) else st.found
  pure ⟨st.cur + 2 + scopeLen + tblLen, ok'⟩

private def checkLeafConstraintsProg (args : ℕ × ℕ) : Memory.Prog ℕ := do
  let res ← iterate checkLeafStep () args.2 ⟨args.1, 1⟩
  pure res.found

private theorem checkLeafConstraintsProg_state (args : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (checkLeafConstraintsProg args) = s := by
  unfold checkLeafConstraintsProg
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of checkLeafStep () (fun _ _ => rfl) args.2 ⟨args.1, 1⟩ s

private theorem checkLeafConstraintsProg_spec {w q : ℕ} (hq : 0 < q) (args : ℕ × ℕ)
    {cs : List (ConstraintTable q)} {s : Memory.State}
    (hcs : HoldsIn args.1 (cs.flatMap ConstraintTable.encode) s)
    (hlen : cs.length = args.2) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (checkLeafConstraintsProg args)) ∧
    (Memory.spec 0).clientState s (checkLeafConstraintsProg args) = s ∧
    (Memory.spec 0).clientResult s (checkLeafConstraintsProg args) =
      (if cs.all fun ct => !decide (ct.scope = []) || ct.eval (fun _ => 0) then 1 else 0) ∧
    memoryCost (checkLeafConstraintsProg args) s ≤ 3 * args.2 := by
  suffices ∀ (rem : List (ConstraintTable q)) cur ok,
      HoldsIn cur (rem.flatMap ConstraintTable.encode) s →
      (ok = 0 ∨ ok = 1) →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (iterate checkLeafStep () rem.length ⟨cur, ok⟩)) ∧
      ((Memory.spec 0).clientResult s
        (iterate checkLeafStep () rem.length ⟨cur, ok⟩)).found =
        (if ok = 1 ∧
            (rem.all fun ct => !decide (ct.scope = []) || ct.eval (fun _ => 0)) = true
          then 1 else 0) ∧
      memoryCost (iterate checkLeafStep () rem.length ⟨cur, ok⟩) s ≤ 3 * rem.length by
    have hrun := this cs args.1 1 hcs (.inr rfl)
    rw [hlen] at hrun
    refine ⟨?_, checkLeafConstraintsProg_state args s, ?_, ?_⟩
    · unfold checkLeafConstraintsProg
      exact validHistory_bind_step hrun.1 (validHistory_pure w _ _)
    · unfold checkLeafConstraintsProg
      rw [StateTransitionSpec.clientResult_bind, hrun.2.1]
      cases cs.all fun ct => !decide (ct.scope = []) || ct.eval (fun _ => 0) <;> rfl
    · unfold checkLeafConstraintsProg
      rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
      exact hrun.2.2
  intro rem
  induction rem with
  | nil =>
    intro cur ok _ hok
    have h0 : iterate checkLeafStep () 0 ⟨cur, ok⟩ = pure ⟨cur, ok⟩ := rfl
    rw [List.length_nil, h0]
    refine ⟨validHistory_pure w s _, ?_, by simp [memoryCost_pure]⟩
    rcases hok with rfl | rfl <;> rfl
  | cons ct rest ih =>
    intro cur ok hcur hok
    rw [List.flatMap_cons, ConstraintTable.encode] at hcur
    have hcons_split :
        ([ct.scope.length, ct.table.length] ++ ct.scope ++ ct.table) ++
          rest.flatMap ConstraintTable.encode =
        ct.scope.length :: ct.table.length ::
          (ct.scope ++ (ct.table ++ rest.flatMap ConstraintTable.encode)) := by
      simp [List.append_assoc]
    rw [hcons_split, HoldsIn.cons_iff] at hcur
    obtain ⟨_, hm_sl, hcur1⟩ := hcur
    rw [HoldsIn.cons_iff] at hcur1
    obtain ⟨_, hm_tl, hcur2⟩ := hcur1
    rw [HoldsIn.append_iff] at hcur2
    obtain ⟨_, hcur3⟩ := hcur2
    rw [HoldsIn.append_iff] at hcur3
    obtain ⟨htbl_h, hrest_h⟩ := hcur3
    have htl_pos : 0 < ct.table.length := by
      rw [ct.table_len]
      exact Nat.one_le_pow _ _ hq
    have h0_lt : cur < s.frontier := by have := htbl_h.1; omega
    have h1_lt : cur + 1 < s.frontier := by have := htbl_h.1; omega
    have ht0_lt : cur + 2 + ct.scope.length < s.frontier := by have := htbl_h.1; omega
    have hm_t0 : s.mem (cur + 2 + ct.scope.length) = ct.table[0] := by
      have haddr : cur + 2 + ct.scope.length = cur + 1 + 1 + ct.scope.length + 0 := by omega
      rw [haddr]
      exact htbl_h.get 0 htl_pos
    let ok' := if ct.scope.length = 0 then (if ct.table[0] = 1 then ok else 0) else ok
    have hok' : ok' = 0 ∨ ok' = 1 := by
      dsimp only [ok']
      split_ifs <;> first | exact hok | exact .inl rfl
    have hstep_res : (Memory.spec 0).clientResult s (checkLeafStep ((), ⟨cur, ok⟩)) =
        ⟨cur + 2 + ct.scope.length + ct.table.length, ok'⟩ := by
      unfold checkLeafStep
      dsimp only
      have hr_s (x : ℕ) : (Memory.spec 0).clientState s (Memory.read x) = s := rfl
      have hr_r (x : ℕ) : (Memory.spec 0).clientResult s (Memory.read x) = s.mem x := rfl
      rw [StateTransitionSpec.clientResult_bind, hr_s, hr_r, hm_sl,
        StateTransitionSpec.clientResult_bind, hr_s, hr_r, hm_tl,
        StateTransitionSpec.clientResult_bind, hr_s, hr_r, hm_t0]
      rfl
    have hv_step : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (checkLeafStep ((), ⟨cur, ok⟩))) := by
      unfold checkLeafStep
      dsimp only
      refine validHistory_read_bind h0_lt ?_
      rw [hm_sl]
      refine validHistory_read_bind h1_lt ?_
      rw [hm_tl]
      exact validHistory_read_bind ht0_lt (validHistory_pure w s _)
    have hc_step : memoryCost (checkLeafStep ((), ⟨cur, ok⟩)) s ≤ 3 := by
      have hr_s (x : ℕ) : (Memory.spec 0).clientState s (Memory.read x) = s := rfl
      have hr_r (x : ℕ) : (Memory.spec 0).clientResult s (Memory.read x) = s.mem x := rfl
      unfold checkLeafStep
      dsimp only
      rw [memoryCost_bind', memoryCost_read, hr_s, hr_r, hm_sl,
        memoryCost_bind', memoryCost_read, hr_s, hr_r, hm_tl,
        memoryCost_bind', memoryCost_read, hr_s, hr_r, memoryCost_pure]
    have hrest_ptr : cur + 1 + 1 + ct.scope.length + ct.table.length =
        cur + 2 + ct.scope.length + ct.table.length := by omega
    rw [hrest_ptr] at hrest_h
    obtain ⟨hv_rem, hr_rem, hc_rem⟩ := ih _ ok' hrest_h hok'
    simp only [List.length_cons, List.all_cons]
    have hiter_eq : iterate checkLeafStep () (rest.length + 1) ⟨cur, ok⟩ =
        (checkLeafStep ((), ⟨cur, ok⟩) >>= iterate checkLeafStep () rest.length) := rfl
    rw [hiter_eq]
    refine ⟨validHistory_bind_step hv_step (by rwa [hstep_res]), ?_, ?_⟩
    · rw [StateTransitionSpec.clientResult_bind, hstep_res]
      change ((Memory.spec 0).clientResult s
        (iterate checkLeafStep () rest.length _)).found = _
      rw [hr_rem]
      refine ite_one_zero_congr ?_
      rw [Bool.and_eq_true]
      have hct_pred :
          (!decide (ct.scope = []) || ct.eval (fun _ => 0)) =
            if ct.scope.length = 0 then decide (ct.table[0] = 1) else true := by
        by_cases hsl : ct.scope.length = 0
        · have hnil : ct.scope = [] := List.eq_nil_of_length_eq_zero hsl
          rw [ite_eq_left hsl]
          refine Bool.eq_iff_iff.2 ?_
          simp [hnil, ConstraintTable.eval, toRadix_nil, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem htl_pos]
        · have hnnil : ct.scope ≠ [] := fun h => hsl (by simp [h])
          simp [hsl, hnnil]
      rw [hct_pred]
      dsimp only [ok']
      rcases hok with rfl | rfl
      · split_ifs <;> simp
      · by_cases hsl : ct.scope.length = 0
        · by_cases ht1 : ct.table[0] = 1 <;> simp [hsl, ht1]
        · simp [hsl]
    · rw [memoryCost_bind']
      change memoryCost (checkLeafStep ((), ⟨cur, ok⟩)) s +
          memoryCost (iterate checkLeafStep () rest.length _) s ≤ _
      rw [hstep_res]
      omega

private theorem checkLeafConstraintsProg_realizes :
    Realizes .exact checkLeafConstraintsProg WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 2 ∧
        ∃ (q : ℕ) (cs : List (ConstraintTable q)),
          0 < q ∧
          cs.length = args.2 ∧
          HoldsIn args.1 (cs.flatMap ConstraintTable.encode) s ∧
          Fits w (args.1 + (cs.flatMap ConstraintTable.encode).length))
      (fun _ _ => 0) := by
  unfold checkLeafConstraintsProg
  realize
  · exact h.1.of_le (by decide)
  · obtain ⟨h2, q, cs, hq, hcs_len, hcs_h, hfit_end⟩ := h
    have h1 : Fits w 1 := h2.of_le (by decide)
    let endPtr := d.1 + (cs.flatMap ConstraintTable.encode).length
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : SubScanState) (t : Memory.State) =>
        j ≤ d.2 ∧ st.found ≤ 1 ∧
        st.cur + ((cs.drop (d.2 - j)).flatMap ConstraintTable.encode).length = endPtr ∧
        HoldsIn st.cur ((cs.drop (d.2 - j)).flatMap ConstraintTable.encode) t)
      (fun j st t ⟨hj_le, hfd_le, hcur_end, hcur_h⟩ => ?_)
      ⟨le_rfl, le_rfl, by simp [endPtr], by simpa only [Nat.sub_self, List.drop_zero] using hcs_h⟩
    have hidx_lt : d.2 - (j + 1) < cs.length := by omega
    have hdrop_cons : cs.drop (d.2 - (j + 1)) =
        cs[d.2 - (j + 1)] :: cs.drop (d.2 - j) := by
      have heq : d.2 - (j + 1) + 1 = d.2 - j := by omega
      rw [← heq]
      exact List.drop_eq_getElem_cons hidx_lt
    let ct := cs[d.2 - (j + 1)]
    rw [hdrop_cons, List.flatMap_cons, ConstraintTable.encode] at hcur_h hcur_end
    have hcons_split :
        ([ct.scope.length, ct.table.length] ++ ct.scope ++ ct.table) ++
          (cs.drop (d.2 - j)).flatMap ConstraintTable.encode =
        ct.scope.length :: ct.table.length ::
          (ct.scope ++ (ct.table ++ (cs.drop (d.2 - j)).flatMap ConstraintTable.encode)) := by
      simp [ct, List.append_assoc]
    rw [hcons_split, HoldsIn.cons_iff] at hcur_h
    obtain ⟨_, hm_sl, hcur1⟩ := hcur_h
    rw [HoldsIn.cons_iff] at hcur1
    obtain ⟨_, hm_tl, hcur2⟩ := hcur1
    rw [HoldsIn.append_iff] at hcur2
    obtain ⟨_, hcur3⟩ := hcur2
    rw [HoldsIn.append_iff] at hcur3
    obtain ⟨_, hrest_h⟩ := hcur3
    have htl_pos : 0 < ct.table.length := by
      rw [ct.table_len]; exact Nat.one_le_pow _ _ hq
    simp only [List.length_append, List.length_cons, List.length_nil] at hcur_end
    have hfit_cur1 : Fits w (st.cur + 1) := hfit_end.of_le (by dsimp only [endPtr] at *; omega)
    have hfit_cur2 : Fits w (st.cur + 2) := hfit_end.of_le (by dsimp only [endPtr] at *; omega)
    have hfit_t0 : Fits w (st.cur + 2 + t.mem st.cur) := hfit_end.of_le (by
      rw [hm_sl]; dsimp only [ct, endPtr] at *; omega)
    have hfit_next : Fits w (st.cur + 2 + t.mem st.cur + t.mem (st.cur + 1)) :=
      hfit_end.of_le (by rw [hm_sl, hm_tl]; dsimp only [ct, endPtr] at *; omega)
    have hfit_fd : Fits w st.found := h1.of_le hfd_le
    refine ⟨?_, Nat.le_of_succ_le hj_le, ?_, ?_, ?_⟩
    · dsimp only [checkLeafStep]
      repeat (
        first
        | split
        | assumption
        | refine And.intro ?_ ?_)
    · dsimp only [checkLeafStep]
      rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
        StateTransitionSpec.clientResult_bind]
      change (if _ then (if _ then st.found else 0) else st.found) ≤ 1
      split_ifs <;> omega
    · dsimp only [checkLeafStep]
      rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
        StateTransitionSpec.clientResult_bind]
      change (st.cur + 2 + t.mem st.cur + t.mem (st.cur + 1)) + _ = endPtr
      rw [hm_sl, hm_tl]
      dsimp only [ct] at *
      omega
    · dsimp only [checkLeafStep]
      rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
        StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
        StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind]
      change HoldsIn (st.cur + 2 + t.mem st.cur + t.mem (st.cur + 1)) _ t
      rw [hm_sl, hm_tl]
      have hptr : st.cur + 1 + 1 + ct.scope.length + ct.table.length =
          st.cur + 2 + ct.scope.length + ct.table.length := by omega
      rwa [hptr] at hrest_h

private structure IntroConsEnv where
  q : ℕ
  v : ℕ
  bagPtr : ℕ
  bagLen : ℕ
  m : ℕ

private def IntroConsEnv.equiv : IntroConsEnv ≃ (((ℕ × ℕ) × ℕ) × ℕ) × ℕ where
  toFun e := ((((e.q, e.v), e.bagPtr), e.bagLen), e.m)
  invFun := fun ((((q, v), bp), bl), m) => ⟨q, v, bp, bl, m⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding IntroConsEnv := .ofEquiv IntroConsEnv.equiv

private structure IntroConsArgs where
  q : ℕ
  v : ℕ
  bagPtr : ℕ
  bagLen : ℕ
  m : ℕ
  consRawPtr : ℕ
  numCons : ℕ

private def IntroConsArgs.equiv :
    IntroConsArgs ≃ (((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a := ((((((a.q, a.v), a.bagPtr), a.bagLen), a.m), a.consRawPtr), a.numCons)
  invFun := fun ((((((q, v), bp), bl), m), cp), nc) => ⟨q, v, bp, bl, m, cp, nc⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding IntroConsArgs := .ofEquiv IntroConsArgs.equiv

private def checkIntroStep (p : IntroConsEnv × SubScanState) : Memory.Prog SubScanState := do
  let e := p.1
  let st := p.2
  let scopeLen ← Memory.read st.cur
  let tblLen ← Memory.read (st.cur + 1)
  let scopePtr := st.cur + 2
  let tblPtr := scopePtr + scopeLen
  let isSub ← subsetBagProg ⟨scopePtr, scopeLen, e.bagPtr, e.bagLen⟩
  let hasV ← bagMemProg ⟨e.v, scopePtr, scopeLen⟩
  let idx ← radixProjProg ⟨e.q, e.bagPtr, e.bagLen, e.m, 0, 0, 0, scopePtr, scopeLen⟩
  let sat ← Memory.read (tblPtr + idx)
  let ok' := if isSub = 1 ∧ hasV = 1 then (if sat = 1 then st.found else 0) else st.found
  pure ⟨tblPtr + tblLen, ok'⟩

private def checkIntroConstraintsProg (args : IntroConsArgs) : Memory.Prog ℕ := do
  let env : IntroConsEnv := ⟨args.q, args.v, args.bagPtr, args.bagLen, args.m⟩
  let res ← iterate checkIntroStep env args.numCons ⟨args.consRawPtr, 1⟩
  pure res.found

private theorem checkIntroStep_eval (e : IntroConsEnv) (st : SubScanState) (t : Memory.State) :
    let scopeLen := t.mem st.cur
    let tblLen := t.mem (st.cur + 1)
    let scopePtr := st.cur + 2
    let tblPtr := scopePtr + scopeLen
    let isSub := (Memory.spec 0).clientResult t
      (subsetBagProg ⟨scopePtr, scopeLen, e.bagPtr, e.bagLen⟩)
    let hasV := (Memory.spec 0).clientResult t (bagMemProg ⟨e.v, scopePtr, scopeLen⟩)
    let idx := (Memory.spec 0).clientResult t
      (radixProjProg ⟨e.q, e.bagPtr, e.bagLen, e.m, 0, 0, 0, scopePtr, scopeLen⟩)
    let sat := t.mem (tblPtr + idx)
    let ok' := if isSub = 1 ∧ hasV = 1 then (if sat = 1 then st.found else 0) else st.found
    (Memory.spec 0).clientState t (checkIntroStep (e, st)) = t ∧
    (Memory.spec 0).clientResult t (checkIntroStep (e, st)) = ⟨tblPtr + tblLen, ok'⟩ := by
  have hr_st (x : ℕ) : (Memory.spec 0).clientState t (Memory.read x) = t := rfl
  have hr_res (x : ℕ) : (Memory.spec 0).clientResult t (Memory.read x) = t.mem x := rfl
  unfold checkIntroStep
  dsimp only
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_st, hr_res,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_st, hr_res,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    subsetBagProg_state,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    bagMemProg_state,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    radixProjProg_state,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_st, hr_res]
  exact ⟨rfl, rfl⟩

private theorem checkIntroConstraintsProg_state (args : IntroConsArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (checkIntroConstraintsProg args) = s := by
  unfold checkIntroConstraintsProg
  dsimp only
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of checkIntroStep
    ⟨args.q, args.v, args.bagPtr, args.bagLen, args.m⟩
    (fun st m => (checkIntroStep_eval _ st m).1) args.numCons ⟨args.consRawPtr, 1⟩ s

private theorem checkIntroConstraintsProg_spec {w : ℕ} (args : IntroConsArgs) (hq : 0 < args.q)
    {LB : List ℕ} {cs : List (ConstraintTable args.q)} {s : Memory.State}
    (hLB : HoldsIn args.bagPtr LB s) (hLB_len : LB.length = args.bagLen)
    (hcs : HoldsIn args.consRawPtr (cs.flatMap ConstraintTable.encode) s)
    (hcs_len : cs.length = args.numCons) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (checkIntroConstraintsProg args)) ∧
    (Memory.spec 0).clientState s (checkIntroConstraintsProg args) = s ∧
    (Memory.spec 0).clientResult s (checkIntroConstraintsProg args) =
      (if cs.all fun ct =>
          !(decide (ct.scope.toFinset ⊆ LB.toFinset) && decide (args.v ∈ ct.scope)) ||
            ct.eval (ofRadix args.q LB args.m)
        then 1 else 0) ∧
    memoryCost (checkIntroConstraintsProg args) s ≤
      3 * args.numCons +
        (cs.map fun ct => ct.scope.length).sum * (2 * args.bagLen + 3) := by
  let env : IntroConsEnv := ⟨args.q, args.v, args.bagPtr, args.bagLen, args.m⟩
  suffices ∀ (rem : List (ConstraintTable args.q)) cur ok,
      HoldsIn cur (rem.flatMap ConstraintTable.encode) s →
      (ok = 0 ∨ ok = 1) →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (iterate checkIntroStep env rem.length ⟨cur, ok⟩)) ∧
      ((Memory.spec 0).clientResult s
        (iterate checkIntroStep env rem.length ⟨cur, ok⟩)).found =
        (if ok = 1 ∧
            (rem.all fun ct =>
              !(decide (ct.scope.toFinset ⊆ LB.toFinset) && decide (args.v ∈ ct.scope)) ||
                ct.eval (ofRadix args.q LB args.m)) = true
          then 1 else 0) ∧
      memoryCost (iterate checkIntroStep env rem.length ⟨cur, ok⟩) s ≤
        3 * rem.length +
          (rem.map fun ct => ct.scope.length).sum * (2 * args.bagLen + 3) by
    have hrun := this cs args.consRawPtr 1 hcs (.inr rfl)
    rw [hcs_len] at hrun
    refine ⟨?_, checkIntroConstraintsProg_state args s, ?_, ?_⟩
    · unfold checkIntroConstraintsProg
      exact validHistory_bind_step hrun.1 (validHistory_pure w _ _)
    · unfold checkIntroConstraintsProg
      rw [StateTransitionSpec.clientResult_bind, hrun.2.1]
      cases cs.all fun ct =>
        !(decide (ct.scope.toFinset ⊆ LB.toFinset) && decide (args.v ∈ ct.scope)) ||
          ct.eval (ofRadix args.q LB args.m) <;> rfl
    · unfold checkIntroConstraintsProg
      rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
      exact hrun.2.2
  intro rem
  induction rem with
  | nil =>
    intro cur ok _ hok
    have h0 : iterate checkIntroStep env 0 ⟨cur, ok⟩ = pure ⟨cur, ok⟩ := rfl
    rw [List.length_nil, h0]
    refine ⟨validHistory_pure w s _, ?_, by simp [memoryCost_pure]⟩
    rcases hok with rfl | rfl <;> rfl
  | cons ct rest ih =>
    intro cur ok hcur hok
    rw [List.flatMap_cons, ConstraintTable.encode] at hcur
    have hcons_split :
        ([ct.scope.length, ct.table.length] ++ ct.scope ++ ct.table) ++
          rest.flatMap ConstraintTable.encode =
        ct.scope.length :: ct.table.length ::
          (ct.scope ++ (ct.table ++ rest.flatMap ConstraintTable.encode)) := by
      simp [List.append_assoc]
    rw [hcons_split, HoldsIn.cons_iff] at hcur
    obtain ⟨_, hm_sl, hcur1⟩ := hcur
    rw [HoldsIn.cons_iff] at hcur1
    obtain ⟨_, hm_tl, hcur2⟩ := hcur1
    have hcur11 : cur + 1 + 1 = cur + 2 := by omega
    rw [hcur11, HoldsIn.append_iff] at hcur2
    obtain ⟨hscope_h, hcur3⟩ := hcur2
    rw [HoldsIn.append_iff] at hcur3
    obtain ⟨htbl_h, hrest_h⟩ := hcur3
    have h0_lt : cur < s.frontier := by have := htbl_h.1; omega
    have h1_lt : cur + 1 < s.frontier := by have := htbl_h.1; omega
    obtain ⟨hv_sub, hst_sub, hr_sub, hc_sub⟩ :=
      subsetBagProg_spec (w := w) ⟨cur + 2, ct.scope.length, args.bagPtr, args.bagLen⟩
        hscope_h rfl hLB hLB_len
    obtain ⟨hv_bm, hst_bm, hr_bm, hc_bm⟩ :=
      bagMemProg_spec (w := w) ⟨args.v, cur + 2, ct.scope.length⟩ hscope_h rfl
    obtain ⟨hv_rp, hst_rp, hr_rp, hc_rp⟩ :=
      radixProjProg_spec (w := w)
        ⟨args.q, args.bagPtr, args.bagLen, args.m, 0, 0, 0, cur + 2, ct.scope.length⟩
        hLB hLB_len hscope_h rfl
    simp only [radixProjAssign, Nat.zero_ne_one, ↓reduceIte] at hr_rp hc_rp
    let idx := toRadix args.q ct.scope (ofRadix args.q LB args.m)
    have hidx_lt : idx < ct.table.length := by
      rw [ct.table_len]
      exact toRadix_lt hq _ _
    have hsat_addr : cur + 2 + ct.scope.length + idx < s.frontier := by
      have := htbl_h.1; omega
    have hm_sat : s.mem (cur + 2 + ct.scope.length + idx) = ct.table[idx] :=
      htbl_h.get idx hidx_lt
    let isSubB := decide (ct.scope.toFinset ⊆ LB.toFinset)
    let hasVB := memBag args.v ct.scope
    let ok' :=
      if (if isSubB then 1 else 0) = 1 ∧ (if hasVB then 1 else 0) = 1 then
        if ct.table[idx] = 1 then ok else 0
      else ok
    have hok' : ok' = 0 ∨ ok' = 1 := by
      dsimp only [ok']
      split_ifs <;> first | exact hok | exact .inl rfl
    obtain ⟨hst_step, hres_step⟩ := checkIntroStep_eval env ⟨cur, ok⟩ s
    have hres_step' :
        (Memory.spec 0).clientResult s (checkIntroStep (env, ⟨cur, ok⟩)) =
          ⟨cur + 2 + ct.scope.length + ct.table.length, ok'⟩ := by
      rw [hres_step]
      dsimp only [env]
      dsimp only [idx] at hm_sat
      rw [hm_sl, hm_tl, hr_sub, hr_bm, hr_rp, hm_sat]
    have hv_step : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (checkIntroStep (env, ⟨cur, ok⟩))) := by
      unfold checkIntroStep
      dsimp only [env]
      refine validHistory_read_bind h0_lt ?_
      rw [hm_sl]
      refine validHistory_read_bind h1_lt ?_
      rw [hm_tl]
      refine validHistory_bind_step hv_sub ?_
      rw [hst_sub, hr_sub]
      refine validHistory_bind_step hv_bm ?_
      rw [hst_bm, hr_bm]
      refine validHistory_bind_step hv_rp ?_
      rw [hst_rp, hr_rp]
      exact validHistory_read_bind hsat_addr (validHistory_pure w s _)
    have hc_step : memoryCost (checkIntroStep (env, ⟨cur, ok⟩)) s ≤
        3 + ct.scope.length * (2 * args.bagLen + 3) := by
      have hr_s (x : ℕ) : (Memory.spec 0).clientState s (Memory.read x) = s := rfl
      have hr_r (x : ℕ) : (Memory.spec 0).clientResult s (Memory.read x) = s.mem x := rfl
      dsimp only at hc_sub hc_bm hc_rp
      unfold checkIntroStep
      dsimp only [env]
      rw [memoryCost_bind', memoryCost_read, hr_s, hr_r, hm_sl,
        memoryCost_bind', memoryCost_read, hr_s, hr_r, hm_tl,
        memoryCost_bind', hst_sub, hr_sub,
        memoryCost_bind', hst_bm, hr_bm,
        memoryCost_bind', hst_rp, hr_rp,
        memoryCost_bind', memoryCost_read, hr_s, hr_r, memoryCost_pure]
      have hring :
          ct.scope.length * (args.bagLen + 1) + ct.scope.length +
            ct.scope.length * (args.bagLen + 1) =
          ct.scope.length * (2 * args.bagLen + 3) := by ring
      omega
    obtain ⟨hv_rem, hr_rem, hc_rem⟩ := ih _ ok' hrest_h hok'
    simp only [List.length_cons, List.all_cons, List.map_cons, List.sum_cons]
    have hiter_eq : iterate checkIntroStep env (rest.length + 1) ⟨cur, ok⟩ =
        (checkIntroStep (env, ⟨cur, ok⟩) >>= iterate checkIntroStep env rest.length) := rfl
    rw [hiter_eq]
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_step, hres_step']), ?_, ?_⟩
    · rw [StateTransitionSpec.clientResult_bind, hst_step, hres_step', hr_rem]
      refine ite_one_zero_congr ?_
      rw [Bool.and_eq_true]
      have heval_eq : ct.eval (ofRadix args.q LB args.m) = decide (ct.table[idx] = 1) := by
        refine Bool.eq_iff_iff.2 ?_
        simp [ConstraintTable.eval, idx, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hidx_lt]
      have hhasV_eq : decide (args.v ∈ ct.scope) = hasVB := (memBag_eq_decide _ _).symm
      rw [heval_eq, hhasV_eq]
      change (ok' = 1 ∧ _) ↔
        ok = 1 ∧ ((!(isSubB && hasVB) || decide (ct.table[idx] = 1)) = true ∧ _)
      dsimp only [ok']
      rcases hok with rfl | rfl
      · cases isSubB <;> cases hasVB <;> split_ifs <;> simp
      · cases isSubB <;> cases hasVB
        · simp
        · simp
        · simp
        · by_cases ht1 : ct.table[idx] = 1 <;> simp [ht1]
    · rw [memoryCost_bind', hst_step, hres_step']
      have hadd_mul :
          (ct.scope.length + (rest.map fun c => c.scope.length).sum) * (2 * args.bagLen + 3) =
            ct.scope.length * (2 * args.bagLen + 3) +
              (rest.map fun c => c.scope.length).sum * (2 * args.bagLen + 3) :=
        Nat.add_mul _ _ _
      rw [hadd_mul]
      omega

private theorem checkIntroConstraintsProg_realizes :
    Realizes .exact checkIntroConstraintsProg WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        0 < args.q ∧ Fits w 2 ∧ Fits w args.q ∧ Fits w args.m ∧
        Fits w (args.bagPtr + args.bagLen) ∧
        ∃ cs : List (ConstraintTable args.q),
          cs.length = args.numCons ∧
          HoldsIn args.consRawPtr (cs.flatMap ConstraintTable.encode) s ∧
          Fits w (args.consRawPtr + (cs.flatMap ConstraintTable.encode).length))
      (fun _ _ => 0) := by
  unfold checkIntroConstraintsProg
  realize [subsetBagProg_realizes, bagMemProg_realizes, radixProjProg_realizes]
  · exact h.2.1.of_le (by decide)
  · obtain ⟨hq_pos, h2, hfit_q, hfit_m, hfit_bag, cs, hcs_len, hcs_h, hfit_end⟩ := h
    have h1 : Fits w 1 := h2.of_le (by decide)
    let endPtr := d.consRawPtr + (cs.flatMap ConstraintTable.encode).length
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : SubScanState) (t : Memory.State) =>
        j ≤ d.numCons ∧ st.found ≤ 1 ∧
        st.cur + ((cs.drop (d.numCons - j)).flatMap ConstraintTable.encode).length = endPtr ∧
        HoldsIn st.cur ((cs.drop (d.numCons - j)).flatMap ConstraintTable.encode) t)
      (fun j st t ⟨hj_le, hfd_le, hcur_end, hcur_h⟩ => ?_)
      ⟨le_rfl, le_rfl, by simp [endPtr], by simpa only [Nat.sub_self, List.drop_zero] using hcs_h⟩
    have hidx_lt : d.numCons - (j + 1) < cs.length := by omega
    have hdrop_cons : cs.drop (d.numCons - (j + 1)) =
        cs[d.numCons - (j + 1)] :: cs.drop (d.numCons - j) := by
      have heq : d.numCons - (j + 1) + 1 = d.numCons - j := by omega
      rw [← heq]
      exact List.drop_eq_getElem_cons hidx_lt
    let ct := cs[d.numCons - (j + 1)]
    rw [hdrop_cons, List.flatMap_cons, ConstraintTable.encode] at hcur_h hcur_end
    have hcons_split :
        ([ct.scope.length, ct.table.length] ++ ct.scope ++ ct.table) ++
          (cs.drop (d.numCons - j)).flatMap ConstraintTable.encode =
        ct.scope.length :: ct.table.length ::
          (ct.scope ++ (ct.table ++ (cs.drop (d.numCons - j)).flatMap ConstraintTable.encode)) :=
      by
      simp [ct, List.append_assoc]
    rw [hcons_split, HoldsIn.cons_iff] at hcur_h
    obtain ⟨_, hm_sl, hcur1⟩ := hcur_h
    rw [HoldsIn.cons_iff] at hcur1
    obtain ⟨_, hm_tl, hcur2⟩ := hcur1
    have hcur11 : st.cur + 1 + 1 = st.cur + 2 := by omega
    rw [hcur11, HoldsIn.append_iff] at hcur2
    obtain ⟨hscope_h, hcur3⟩ := hcur2
    rw [HoldsIn.append_iff] at hcur3
    obtain ⟨_, hrest_h⟩ := hcur3
    simp only [List.length_append, List.length_cons, List.length_nil] at hcur_end
    have hfit_cur1 : Fits w (st.cur + 1) := hfit_end.of_le (by dsimp only [endPtr] at *; omega)
    have hfit_cur2 : Fits w (st.cur + 2) := hfit_end.of_le (by dsimp only [endPtr] at *; omega)
    have hfit_sc_end : Fits w (st.cur + 2 + t.mem st.cur) := hfit_end.of_le (by
      rw [hm_sl]; dsimp only [ct, endPtr] at *; omega)
    have hpow_eq : d.q ^ t.mem st.cur = ct.table.length := by
      rw [hm_sl, ct.table_len]
    have hfit_pow : Fits w (d.q ^ t.mem st.cur) := hfit_end.of_le (by
      rw [hpow_eq]; dsimp only [ct, endPtr] at *; omega)
    let rpArgs : RadixProjArgs :=
      ⟨d.q, d.bagPtr, d.bagLen, d.m, 0, 0, 0, st.cur + 2, t.mem st.cur⟩
    have hfit_sat (m' : Memory.State) :
        Fits w (st.cur + 2 + t.mem st.cur +
          (Memory.spec 0).clientResult m' (radixProjProg rpArgs)) := by
      have hlt : (Memory.spec 0).clientResult m' (radixProjProg rpArgs) < ct.table.length := by
        have h := radixProjProg_result_lt (args := rpArgs) hq_pos m'
        dsimp only [rpArgs] at h
        rwa [hpow_eq] at h
      exact hfit_end.of_le (by rw [hm_sl]; dsimp only [ct, endPtr] at *; omega)
    have hfit_next : Fits w (st.cur + 2 + t.mem st.cur + t.mem (st.cur + 1)) :=
      hfit_end.of_le (by rw [hm_sl, hm_tl]; dsimp only [ct, endPtr] at *; omega)
    have hfit_fd : Fits w st.found := h1.of_le hfd_le
    have hsub_safe : Fits w 1 ∧ Fits w (st.cur + 2 + t.mem st.cur) ∧
        Fits w (d.bagPtr + d.bagLen) := ⟨h1, hfit_sc_end, hfit_bag⟩
    have hbm_safe : Fits w 1 ∧ Fits w (st.cur + 2 + t.mem st.cur) := ⟨h1, hfit_sc_end⟩
    have hrp_safe :
        0 < d.q ∧ Fits w 1 ∧ Fits w d.q ∧ Fits w d.m ∧
          Fits w (d.bagPtr + d.bagLen) ∧ Fits w (st.cur + 2 + t.mem st.cur) ∧
          Fits w (d.q ^ t.mem st.cur) :=
      ⟨hq_pos, h1, hfit_q, hfit_m, hfit_bag, hfit_sc_end, hfit_pow⟩
    obtain ⟨hst_ev, hres_ev⟩ :=
      checkIntroStep_eval ⟨d.q, d.v, d.bagPtr, d.bagLen, d.m⟩ st t
    refine ⟨?_, Nat.le_of_succ_le hj_le, ?_, ?_, ?_⟩
    · dsimp only [checkIntroStep]
      refine ⟨hfit_cur1, ⟨hfit_cur2, hsub_safe⟩, ⟨hfit_cur2, hbm_safe⟩, ⟨hfit_cur2, hrp_safe⟩,
        hfit_sat _, h1, ?_⟩
      repeat (
        first
        | split
        | exact h1
        | exact hfit_next
        | refine And.intro ?_ ?_)
    · rw [hres_ev]
      dsimp only
      split_ifs <;> omega
    · rw [hres_ev]
      dsimp only
      rw [hm_sl, hm_tl]
      dsimp only [ct] at *
      omega
    · rw [hst_ev, hres_ev]
      dsimp only
      rw [hm_sl, hm_tl]
      exact hrest_h


/-! ### Descriptor writes, framing invariants, and the four nice-tree node handlers -/

private structure DescWriteArgs where
  dCur : ℕ
  bagPtr : ℕ
  bagLen : ℕ
  tblPtr : ℕ
  tblLen : ℕ

private def DescWriteArgs.equiv :
    DescWriteArgs ≃ (((ℕ × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a := ((((a.dCur, a.bagPtr), a.bagLen), a.tblPtr), a.tblLen)
  invFun := fun ((((dc, bp), bl), tp), tl) => ⟨dc, bp, bl, tp, tl⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding DescWriteArgs := .ofEquiv DescWriteArgs.equiv

private def writeDescProg (a : DescWriteArgs) : Memory.Prog Unit := do
  Memory.write a.dCur a.bagPtr
  Memory.write (a.dCur + 1) a.bagLen
  Memory.write (a.dCur + 2) a.tblPtr
  Memory.write (a.dCur + 3) a.tblLen

private def FrameOutsideRange (lo hi : ℕ) (s₀ s₁ : Memory.State) : Prop :=
  s₀.frontier ≤ s₁.frontier ∧
  ∀ x < s₀.frontier, (x < lo ∨ hi ≤ x) → s₁.mem x = s₀.mem x

private theorem FrameOutsideRange.refl (lo hi : ℕ) (s : Memory.State) :
    FrameOutsideRange lo hi s s :=
  ⟨le_rfl, fun _ _ _ => rfl⟩

private theorem FrameOutsideRange.of_preservesBelow (lo hi : ℕ) {s₀ s₁ : Memory.State}
    (hp : PreservesBelow s₀.frontier s₀ s₁) :
    FrameOutsideRange lo hi s₀ s₁ :=
  ⟨hp.2.1, fun x hx _ => hp.2.2 x hx⟩

private theorem FrameOutsideRange.mono_range {lo₁ hi₁ lo₂ hi₂ : ℕ} {s₀ s₁ : Memory.State}
    (h : FrameOutsideRange lo₁ hi₁ s₀ s₁) (hlo : lo₂ ≤ lo₁) (hhi : hi₁ ≤ hi₂) :
    FrameOutsideRange lo₂ hi₂ s₀ s₁ :=
  ⟨h.1, fun x hx hout => h.2 x hx (hout.imp (fun hlt => lt_of_lt_of_le hlt hlo)
    (fun hge => le_trans hhi hge))⟩

private theorem FrameOutsideRange.trans {lo hi : ℕ} {s₀ s₁ s₂ : Memory.State}
    (h₁ : FrameOutsideRange lo hi s₀ s₁) (h₂ : FrameOutsideRange lo hi s₁ s₂) :
    FrameOutsideRange lo hi s₀ s₂ :=
  ⟨h₁.1.trans h₂.1, fun x hx hout =>
    (h₂.2 x (lt_of_lt_of_le hx h₁.1) hout).trans (h₁.2 x hx hout)⟩

private theorem HoldsIn.frame_outsideRange {base lo hi : ℕ} {xs : List ℕ} {s₀ s₁ : Memory.State}
    (h : HoldsIn base xs s₀)
    (hdisj : base + xs.length ≤ lo ∨ hi ≤ base)
    (hf : FrameOutsideRange lo hi s₀ s₁) :
    HoldsIn base xs s₁ := by
  refine ⟨h.1.trans hf.1, h.2.frame fun x hlo hhi => ?_⟩
  exact hf.2 x (by have := h.1; omega) (by omega)

private theorem writeDescProg_spec {w : ℕ} (a : DescWriteArgs) {s : Memory.State}
    (hd : a.dCur + 4 ≤ s.frontier)
    (hbp : Fits w a.bagPtr) (hbl : Fits w a.bagLen)
    (htp : Fits w a.tblPtr) (htl : Fits w a.tblLen) :
    let s₁ := (Memory.spec 0).clientState s (writeDescProg a)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (writeDescProg a)) ∧
    s₁.frontier = s.frontier ∧
    FrameOutsideRange a.dCur (a.dCur + 4) s s₁ ∧
    s₁.mem a.dCur = a.bagPtr ∧
    s₁.mem (a.dCur + 1) = a.bagLen ∧
    s₁.mem (a.dCur + 2) = a.tblPtr ∧
    s₁.mem (a.dCur + 3) = a.tblLen ∧
    memoryCost (writeDescProg a) s ≤ 4 := by
  unfold writeDescProg
  let t₁ : Memory.State := ⟨Function.update s.mem a.dCur a.bagPtr, s.frontier⟩
  let t₂ : Memory.State := ⟨Function.update t₁.mem (a.dCur + 1) a.bagLen, s.frontier⟩
  let t₃ : Memory.State := ⟨Function.update t₂.mem (a.dCur + 2) a.tblPtr, s.frontier⟩
  let t₄ : Memory.State := ⟨Function.update t₃.mem (a.dCur + 3) a.tblLen, s.frontier⟩
  have hst : (Memory.spec 0).clientState s
      (Memory.write a.dCur a.bagPtr >>= fun _ =>
        Memory.write (a.dCur + 1) a.bagLen >>= fun _ =>
        Memory.write (a.dCur + 2) a.tblPtr >>= fun _ =>
        Memory.write (a.dCur + 3) a.tblLen) = t₄ := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact validHistory_write_bind (by omega) hbp
      (validHistory_write_bind (by dsimp only; omega) hbl
        (validHistory_write_bind (by dsimp only; omega) htp
          (validHistory_write (by dsimp only; omega) htl)))
  · rw [hst]
  · rw [hst]
    refine ⟨le_rfl, fun x _ hout => ?_⟩
    dsimp only [t₄, t₃, t₂, t₁]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · rw [hst]
    dsimp only [t₄, t₃, t₂, t₁]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_self]
  · rw [hst]
    dsimp only [t₄, t₃, t₂, t₁]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_self]
  · rw [hst]
    dsimp only [t₄, t₃, t₂, t₁]
    rw [Function.update_of_ne (by omega), Function.update_self]
  · rw [hst]
    dsimp only [t₄]
    exact Function.update_self _ _ _
  · simp only [memoryCost_bind', memoryCost_write]
    omega

private theorem writeDescProg_realizes :
    Realizes .exact writeDescProg WordEncoding.encode WordEncoding.encode
      (fun w a _ => Fits w (a.dCur + 3))
      (fun _ _ => 0) := by
  unfold writeDescProg
  realize
  · exact h.of_le (by omega)
  · exact h.of_le (by omega)
  · exact h

private structure NodeDescAt (F_lo : ℕ) (counting : Bool) (q : ℕ)
    (cs : List (ConstraintTable q)) (vars : List ℕ) (S : NiceTree ℕ) (d : ℕ)
    (s : Memory.State) : Prop where
  desc_hi : d + 4 ≤ F_lo
  bag_lo : F_lo ≤ s.mem d
  bag_len : s.mem (d + 1) = (bagList S).length
  bag_holds : HoldsIn (s.mem d) (bagList S) s
  tbl_lo : F_lo ≤ s.mem (d + 2)
  tbl_len : s.mem (d + 3) = q ^ (bagList S).length
  tbl_holds : HoldsIn (s.mem (d + 2)) (dpInstTree counting q cs vars S) s

private theorem NodeDescAt.frame {F_lo : ℕ} {counting : Bool} {q : ℕ}
    {cs : List (ConstraintTable q)} {vars : List ℕ} {S : NiceTree ℕ} {d lo hi : ℕ}
    {s₀ s₁ : Memory.State}
    (h : NodeDescAt F_lo counting q cs vars S d s₀)
    (hd : d + 4 ≤ lo ∨ hi ≤ d) (hhi : hi ≤ F_lo)
    (hf : FrameOutsideRange lo hi s₀ s₁) :
    NodeDescAt F_lo counting q cs vars S d s₁ where
  desc_hi := h.desc_hi
  bag_lo := by
    have hlt : d < s₀.frontier := by
      have := h.bag_holds.1; have := h.bag_lo; have := h.desc_hi; omega
    rw [hf.2 d hlt (by omega)]
    exact h.bag_lo
  bag_len := by
    have hlt : d + 1 < s₀.frontier := by
      have := h.bag_holds.1; have := h.bag_lo; have := h.desc_hi; omega
    rw [hf.2 (d + 1) hlt (by omega)]
    exact h.bag_len
  bag_holds := by
    have hlt : d < s₀.frontier := by
      have := h.bag_holds.1; have := h.bag_lo; have := h.desc_hi; omega
    rw [hf.2 d hlt (by omega)]
    exact h.bag_holds.frame_outsideRange (.inr (le_trans hhi h.bag_lo)) hf
  tbl_lo := by
    have hlt : d + 2 < s₀.frontier := by
      have := h.bag_holds.1; have := h.bag_lo; have := h.desc_hi; omega
    rw [hf.2 (d + 2) hlt (by omega)]
    exact h.tbl_lo
  tbl_len := by
    have hlt : d + 3 < s₀.frontier := by
      have := h.bag_holds.1; have := h.bag_lo; have := h.desc_hi; omega
    rw [hf.2 (d + 3) hlt (by omega)]
    exact h.tbl_len
  tbl_holds := by
    have hlt : d + 2 < s₀.frontier := by
      have := h.bag_holds.1; have := h.bag_lo; have := h.desc_hi; omega
    rw [hf.2 (d + 2) hlt (by omega)]
    exact h.tbl_holds.frame_outsideRange (.inr (le_trans hhi h.tbl_lo)) hf

private theorem NodeDescAt.mono_frontier {F_lo : ℕ} {counting : Bool} {q : ℕ}
    {cs : List (ConstraintTable q)} {vars : List ℕ} {S : NiceTree ℕ} {d : ℕ}
    {s₀ s₁ : Memory.State}
    (h : NodeDescAt F_lo counting q cs vars S d s₀)
    (hp : PreservesBelow s₀.frontier s₀ s₁) :
    NodeDescAt F_lo counting q cs vars S d s₁ :=
  h.frame (.inr le_rfl) (by have := h.desc_hi; omega)
    (FrameOutsideRange.of_preservesBelow d d hp)

/-! #### 1. Leaf node handler (`leafNodeProg`) -/

private structure LeafNodeArgs where
  consRawPtr : ℕ
  numCons : ℕ
  dCur : ℕ

private def LeafNodeArgs.equiv : LeafNodeArgs ≃ (ℕ × ℕ) × ℕ where
  toFun a := ((a.consRawPtr, a.numCons), a.dCur)
  invFun := fun ((cp, nc), dc) => ⟨cp, nc, dc⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding LeafNodeArgs := .ofEquiv LeafNodeArgs.equiv

private def leafNodeProg (a : LeafNodeArgs) : Memory.Prog Unit := do
  let ok ← checkLeafConstraintsProg (a.consRawPtr, a.numCons)
  let tblPtr ← Memory.allocDirty 1
  Memory.write tblPtr ok
  writeDescProg ⟨a.dCur, tblPtr, 0, tblPtr, 1⟩

private theorem leafNodeProg_spec {w q F_lo : ℕ} (counting : Bool) (hq : 0 < q)
    (a : LeafNodeArgs) {cs : List (ConstraintTable q)} {vars : List ℕ} {s : Memory.State}
    (hcs : HoldsIn a.consRawPtr (cs.flatMap ConstraintTable.encode) s)
    (hcs_len : cs.length = a.numCons)
    (hdCur : a.dCur + 4 ≤ F_lo)
    (hFlo : F_lo ≤ s.frontier)
    (hfit_fr1 : Fits w (s.frontier + 1)) :
    let sEnd := (Memory.spec 0).clientState s (leafNodeProg a)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (leafNodeProg a)) ∧
    sEnd.frontier ≤ s.frontier + 1 ∧
    FrameOutsideRange a.dCur (a.dCur + 4) s sEnd ∧
    NodeDescAt F_lo counting q cs vars .leaf a.dCur sEnd ∧
    memoryCost (leafNodeProg a) s ≤ 6 + 3 * a.numCons := by
  obtain ⟨hv_cl, hst_cl, hr_cl, hc_cl⟩ :=
    checkLeafConstraintsProg_spec (w := w) hq (a.consRawPtr, a.numCons) hcs hcs_len
  dsimp only at hr_cl hc_cl
  let okVal := if cs.all fun ct => !decide (ct.scope = []) || ct.eval (fun _ => 0) then 1 else 0
  have hok_fit : Fits w okVal := by
    dsimp only [okVal]
    split_ifs
    · exact hfit_fr1.of_le (by omega)
    · exact fits_zero w
  let s_a := (Memory.spec 0).clientState s (Memory.allocDirty 1)
  have ha_fr : s_a.frontier = s.frontier + 1 := rfl
  have hp_a : PreservesBelow s.frontier s s_a := preservesBelow_allocDirty s 1
  have hv_a : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (Memory.allocDirty 1)) :=
    validHistory_allocDirty hfit_fr1
  let s_w : Memory.State := ⟨Function.update s_a.mem s.frontier okVal, s_a.frontier⟩
  have hlt_w : s.frontier < s_a.frontier := by rw [ha_fr]; omega
  have hp_w : PreservesBelow s.frontier s_a s_w := preservesBelow_write le_rfl hlt_w
  have htbl_w : HoldsIn s.frontier [okVal] s_w := by
    have h0 : HoldsIn s.frontier [] s_a := HoldsIn.nil (by rw [ha_fr]; omega)
    simpa only [List.nil_append, List.length_nil, Nat.add_zero] using
      holdsIn_append_one h0 (by rw [ha_fr]; simp)
  have hd_w : a.dCur + 4 ≤ s_w.frontier := by dsimp only [s_w]; rw [ha_fr]; omega
  have hfit_ptr : Fits w s.frontier := hfit_fr1.of_le (by omega)
  have hfit_1 : Fits w 1 := hfit_fr1.of_le (by omega)
  obtain ⟨hv_wd, hfr_wd, hframe_wd, hm0, hm1, hm2, hm3, hc_wd⟩ :=
    writeDescProg_spec (w := w) ⟨a.dCur, s.frontier, 0, s.frontier, 1⟩
      hd_w hfit_ptr (fits_zero w) hfit_ptr hfit_1
  dsimp only at hm0 hm1 hm2 hm3
  let sEnd :=
    (Memory.spec 0).clientState s_w (writeDescProg ⟨a.dCur, s.frontier, 0, s.frontier, 1⟩)
  have hsEnd_eq : (Memory.spec 0).clientState s (leafNodeProg a) = sEnd := by
    unfold leafNodeProg
    rw [StateTransitionSpec.clientState_bind, hst_cl, hr_cl,
      StateTransitionSpec.clientState_bind]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold leafNodeProg
    refine validHistory_bind_step hv_cl ?_
    rw [hst_cl, hr_cl]
    refine validHistory_bind_step hv_a ?_
    exact validHistory_write_bind hlt_w hok_fit hv_wd
  · rw [hsEnd_eq, hfr_wd]
    exact le_rfl
  · rw [hsEnd_eq]
    exact (FrameOutsideRange.of_preservesBelow a.dCur (a.dCur + 4) (hp_a.trans hp_w)).trans
      hframe_wd
  · rw [hsEnd_eq]
    refine ⟨hdCur, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hm0]; exact hFlo
    · rw [hm1]; rfl
    · rw [hm0]; exact HoldsIn.nil (by rw [hfr_wd]; dsimp only [s_w]; rw [ha_fr]; omega)
    · rw [hm2]; exact hFlo
    · rw [hm3]; simp [bagList]
    · rw [hm2]
      have htbl_eq : [okVal] = dpInstTree counting q cs vars .leaf := rfl
      rw [← htbl_eq]
      exact htbl_w.frame_outsideRange (.inr (le_trans hdCur hFlo)) hframe_wd
  · unfold leafNodeProg
    rw [memoryCost_bind', hst_cl, hr_cl, memoryCost_bind', memoryCost_allocDirty]
    change _ + (1 + memoryCost (Memory.write s.frontier okVal >>= _) s_a) ≤ _
    rw [memoryCost_bind', memoryCost_write]
    change _ + (1 + (1 +
      memoryCost (writeDescProg ⟨a.dCur, s.frontier, 0, s.frontier, 1⟩) s_w)) ≤ _
    omega

private theorem leafNodeProg_realizes :
    Realizes .exact leafNodeProg WordEncoding.encode WordEncoding.encode
      (fun w a s =>
        Fits w 2 ∧
        Fits w (a.dCur + 3) ∧
        ∃ (q : ℕ) (cs : List (ConstraintTable q)),
          0 < q ∧
          cs.length = a.numCons ∧
          HoldsIn a.consRawPtr (cs.flatMap ConstraintTable.encode) s ∧
          Fits w (a.consRawPtr + (cs.flatMap ConstraintTable.encode).length))
      (fun _ _ => 0) := by
  unfold leafNodeProg
  realize [checkLeafConstraintsProg_realizes, writeDescProg_realizes]
  · exact h.1
  · obtain ⟨_, _, q, cs, hq, hlen, hcs, hend⟩ := h
    exact ⟨q, cs, hq, hlen, hcs, hend⟩
  · exact h.1.of_le (by decide)
  · exact h.2.1

/-! #### 2. Introduce node handler (`introFillProg` & `introNodeProg`) -/

private structure IntroFillArgs where
  q : ℕ
  v : ℕ
  bagPtr : ℕ
  bagLen : ℕ
  consRawPtr : ℕ
  numCons : ℕ
  cTblPtr : ℕ
  tblPtr : ℕ
  tblLen : ℕ

private def IntroFillArgs.equiv :
    IntroFillArgs ≃ (((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a :=
    ((((((((a.q, a.v), a.bagPtr), a.bagLen), a.consRawPtr), a.numCons), a.cTblPtr), a.tblPtr),
      a.tblLen)
  invFun := fun ((((((((q, v), bp), bl), cp), nc), ctp), tp), tl) =>
    ⟨q, v, bp, bl, cp, nc, ctp, tp, tl⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding IntroFillArgs := .ofEquiv IntroFillArgs.equiv

private def introFillStep (p : IntroFillArgs × ℕ) : Memory.Prog ℕ := do
  let a := p.1
  let m := p.2
  let cVal ← Memory.read (a.cTblPtr + m / a.q)
  let ok ← checkIntroConstraintsProg ⟨a.q, a.v, a.bagPtr, a.bagLen, m, a.consRawPtr, a.numCons⟩
  let val := if ok = 1 then cVal else 0
  Memory.write (a.tblPtr + m) val
  pure (m + 1)

private def introFillProg (a : IntroFillArgs) : Memory.Prog Unit := do
  let _ ← iterate introFillStep a a.tblLen 0
  pure ()

private theorem introFillStep_eval (a : IntroFillArgs) (m : ℕ) (t : Memory.State) :
    let ok := (Memory.spec 0).clientResult t
      (checkIntroConstraintsProg ⟨a.q, a.v, a.bagPtr, a.bagLen, m, a.consRawPtr, a.numCons⟩)
    let cVal := t.mem (a.cTblPtr + m / a.q)
    let val := if ok = 1 then cVal else 0
    (Memory.spec 0).clientState t (introFillStep (a, m)) =
      ⟨Function.update t.mem (a.tblPtr + m) val, t.frontier⟩ ∧
    (Memory.spec 0).clientResult t (introFillStep (a, m)) = m + 1 := by
  have hr_st (x : ℕ) : (Memory.spec 0).clientState t (Memory.read x) = t := rfl
  have hr_res (x : ℕ) : (Memory.spec 0).clientResult t (Memory.read x) = t.mem x := rfl
  unfold introFillStep
  dsimp only
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_st, hr_res,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    checkIntroConstraintsProg_state,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind]
  exact ⟨rfl, rfl⟩

private theorem tableFillProg_spec {α : Type} {w : ℕ} (step : α × ℕ → Memory.Prog ℕ)
    (a : α) (tblPtr tblLen stepCost : ℕ) (targetTbl : List ℕ) (s : Memory.State)
    (Inv : Memory.State → Prop) (hinv : Inv s)
    (htarget_len : targetTbl.length = tblLen) (htbl_hi : tblPtr + tblLen ≤ s.frontier)
    (hstep : ∀ (k : ℕ) (t : Memory.State), (hk : k < tblLen) →
      let m := tblLen - (k + 1)
      Inv t → t.frontier = s.frontier → PreservesBelow tblPtr s t →
      HoldsIn tblPtr (targetTbl.take m) t →
      let entryVal := targetTbl[m]'(by
        have hm : tblLen - (k + 1) < tblLen := Nat.sub_lt (Nat.zero_lt_of_lt hk) (Nat.succ_pos k)
        simpa only [htarget_len] using hm)
      let t₁ : Memory.State := ⟨Function.update t.mem (tblPtr + m) entryVal, t.frontier⟩
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (step (a, m))) ∧
      (Memory.spec 0).clientState t (step (a, m)) = t₁ ∧
      (Memory.spec 0).clientResult t (step (a, m)) = m + 1 ∧
      Inv t₁ ∧
      memoryCost (step (a, m)) t ≤ stepCost) :
    let prog : Memory.Prog Unit := do let _ ← iterate step a tblLen 0; pure ()
    let s₁ := (Memory.spec 0).clientState s prog
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s₁.frontier = s.frontier ∧
    PreservesBelow tblPtr s s₁ ∧
    HoldsIn tblPtr targetTbl s₁ ∧
    memoryCost prog s ≤ tblLen * stepCost := by
  suffices ∀ rem (t : Memory.State), rem ≤ tblLen → Inv t → t.frontier = s.frontier →
      PreservesBelow tblPtr s t → HoldsIn tblPtr (targetTbl.take (tblLen - rem)) t →
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (iterate step a rem (tblLen - rem))) ∧
      (let tEnd := (Memory.spec 0).clientState t (iterate step a rem (tblLen - rem))
       tEnd.frontier = s.frontier ∧ PreservesBelow tblPtr s tEnd ∧
       HoldsIn tblPtr targetTbl tEnd) ∧
      memoryCost (iterate step a rem (tblLen - rem)) t ≤ rem * stepCost by
    have hrun := this tblLen s le_rfl hinv rfl (PreservesBelow.refl (by omega))
      (by simp only [Nat.sub_self, List.take_zero]; exact HoldsIn.nil (by omega))
    simp only [Nat.sub_self] at hrun
    obtain ⟨hv_l, ⟨hfr_l, hp_l, htbl_l⟩, hc_l⟩ := hrun
    refine ⟨validHistory_bind_step hv_l (validHistory_pure w _ ()), ?_, ?_, ?_, ?_⟩
    · rw [StateTransitionSpec.clientState_bind]; exact hfr_l
    · rw [StateTransitionSpec.clientState_bind]; exact hp_l
    · rw [StateTransitionSpec.clientState_bind]; exact htbl_l
    · rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]; exact hc_l
  intro rem
  induction rem with
  | zero =>
    intro t _ _ hfr hp hhold
    have h0 : iterate step a 0 (tblLen - 0) = pure (tblLen - 0) := rfl
    simp only [Nat.sub_zero] at h0 hhold ⊢
    rw [h0]
    rw [← htarget_len, List.take_length] at hhold
    exact ⟨validHistory_pure w t _, ⟨hfr, hp, hhold⟩, by simp [memoryCost_pure]⟩
  | succ k ih =>
    intro t hk_le hinv_t hfr_t hp_t hhold_t
    let m := tblLen - (k + 1)
    have hm_lt : m < tblLen := by omega
    obtain ⟨hv_step, hst_t₁, hres_ev, hinv₁, hc_step⟩ :=
      hstep k t hk_le hinv_t hfr_t hp_t hhold_t
    let entryVal := targetTbl[m]'(by rw [htarget_len]; exact hm_lt)
    let t₁ : Memory.State := ⟨Function.update t.mem (tblPtr + m) entryVal, t.frontier⟩
    have hdst_lt : tblPtr + m < t.frontier := by rw [hfr_t]; omega
    have hp₁ : PreservesBelow tblPtr t t₁ :=
      preservesBelow_write (Nat.le_add_right _ _) hdst_lt
    have htake_len : (targetTbl.take m).length = m :=
      List.length_take_of_le (by rw [htarget_len]; omega)
    have hhold₁ : HoldsIn tblPtr (targetTbl.take (m + 1)) t₁ := by
      have happ := holdsIn_append_one (v := entryVal) hhold_t (by rw [htake_len, hfr_t]; omega)
      rw [htake_len] at happ
      have htake_succ : targetTbl.take (m + 1) = targetTbl.take m ++ [entryVal] :=
        List.take_succ_eq_append_getElem (by rw [htarget_len]; exact hm_lt)
      rwa [← htake_succ] at happ
    have hm_succ : m + 1 = tblLen - k := by dsimp only [m]; omega
    rw [hm_succ] at hhold₁ hres_ev
    obtain ⟨hv_rem, hprops_rem, hc_rem⟩ :=
      ih t₁ (Nat.le_of_succ_le hk_le) hinv₁ hfr_t (hp_t.trans hp₁) hhold₁
    have hiter_eq : iterate step a (k + 1) m = (step (a, m) >>= iterate step a k) := rfl
    change (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (iterate step a (k + 1) m)) ∧ _ ∧ _
    rw [hiter_eq]
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_t₁, hres_ev]), ?_, ?_⟩
    · rw [StateTransitionSpec.clientState_bind, hst_t₁, hres_ev]
      exact hprops_rem
    · rw [memoryCost_bind', hst_t₁, hres_ev]
      calc _ ≤ stepCost + k * stepCost := Nat.add_le_add hc_step hc_rem
        _ = (k + 1) * stepCost := by ring

private theorem introFillProg_spec {w : ℕ} (counting : Bool) (a : IntroFillArgs)
    (hq : 0 < a.q) {child : NiceTree ℕ} {cs : List (ConstraintTable a.q)} {vars : List ℕ}
    {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hv_eq : a.v = a.v)
    (hLB : HoldsIn a.bagPtr (a.v :: bagList child) s)
    (hLB_len : (a.v :: bagList child).length = a.bagLen)
    (hLB_hi : a.bagPtr + a.bagLen ≤ a.tblPtr)
    (hcs : HoldsIn a.consRawPtr (cs.flatMap ConstraintTable.encode) s)
    (hcs_len : cs.length = a.numCons)
    (hcs_hi : a.consRawPtr + (cs.flatMap ConstraintTable.encode).length ≤ a.tblPtr)
    (hcTbl : HoldsIn a.cTblPtr (dpInstTree counting a.q cs vars child) s)
    (hcTbl_hi : a.cTblPtr + a.q ^ (bagList child).length ≤ a.tblPtr)
    (htblLen : a.tblLen = a.q ^ a.bagLen)
    (htbl_hi : a.tblPtr + a.tblLen ≤ s.frontier) :
    let targetTbl := dpInstTree counting a.q cs vars (.introduce a.v child)
    let s₁ := (Memory.spec 0).clientState s (introFillProg a)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (introFillProg a)) ∧
    s₁.frontier = s.frontier ∧
    PreservesBelow a.tblPtr s s₁ ∧
    HoldsIn a.tblPtr targetTbl s₁ ∧
    memoryCost (introFillProg a) s ≤
      a.tblLen *
        (2 + 3 * a.numCons +
          (cs.map fun ct => ct.scope.length).sum * (2 * a.bagLen + 3)) := by
  let _ := hv_eq
  let targetTbl := dpInstTree counting a.q cs vars (.introduce a.v child)
  have htarget_len : targetTbl.length = a.tblLen := by
    simp [targetTbl, bagList, hLB_len, htblLen]
  let stepCost :=
    2 + 3 * a.numCons + (cs.map fun ct => ct.scope.length).sum * (2 * a.bagLen + 3)
  refine tableFillProg_spec introFillStep a a.tblPtr a.tblLen stepCost targetTbl s
    (Memory.WellFormed w) hwf htarget_len htbl_hi fun k t hk_le hwf_t hfr_t hp_t _ => ?_
  let m := a.tblLen - (k + 1)
  have hm_lt : m < a.tblLen := by omega
  have hm_pow : a.tblLen = a.q * a.q ^ (bagList child).length := by
    rw [htblLen, ← hLB_len, List.length_cons, Nat.pow_succ, Nat.mul_comm]
  have hdiv_lt : m / a.q < a.q ^ (bagList child).length := by
    rw [Nat.div_lt_iff_lt_mul hq, Nat.mul_comm]
    omega
  have hcTbl_t : HoldsIn a.cTblPtr (dpInstTree counting a.q cs vars child) t :=
    hcTbl.mono (F := a.tblPtr) (by simpa using hcTbl_hi) hp_t
  have hLB_t : HoldsIn a.bagPtr (a.v :: bagList child) t :=
    hLB.mono (F := a.tblPtr) (by rw [hLB_len]; exact hLB_hi) hp_t
  have hcs_t : HoldsIn a.consRawPtr (cs.flatMap ConstraintTable.encode) t :=
    hcs.mono (F := a.tblPtr) hcs_hi hp_t
  obtain ⟨hv_ci, hst_ci, hr_ci, hc_ci⟩ :=
    checkIntroConstraintsProg_spec (w := w)
      ⟨a.q, a.v, a.bagPtr, a.bagLen, m, a.consRawPtr, a.numCons⟩ hq
      hLB_t hLB_len hcs_t hcs_len
  dsimp only at hr_ci hc_ci
  have hc_len : (dpInstTree counting a.q cs vars child).length = a.q ^ (bagList child).length :=
    length_dpInstTree _ _ _ _ _
  have hm_cval : t.mem (a.cTblPtr + m / a.q) =
      (dpInstTree counting a.q cs vars child).getD (m / a.q) 0 := by
    rw [hcTbl_t.get (m / a.q) (by rw [hc_len]; exact hdiv_lt), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [hc_len]; exact hdiv_lt), Option.getD_some]
  have hc_addr_lt : a.cTblPtr + m / a.q < t.frontier := by rw [hfr_t]; omega
  have hdst_addr_lt : a.tblPtr + m < t.frontier := by rw [hfr_t]; omega
  have hcval_fit : Fits w (t.mem (a.cTblPtr + m / a.q)) := hwf_t.2 _
  obtain ⟨hst_ev, hres_ev⟩ := introFillStep_eval a m t
  let entryVal := targetTbl[m]'(by rw [htarget_len]; exact hm_lt)
  have hval_eq :
      (if (Memory.spec 0).clientResult t
          (checkIntroConstraintsProg
            ⟨a.q, a.v, a.bagPtr, a.bagLen, m, a.consRawPtr, a.numCons⟩) =
            1 then t.mem (a.cTblPtr + m / a.q) else 0) = entryVal := by
    rw [hr_ci, hm_cval]
    simp only [entryVal, targetTbl, dpInstTree, List.getElem_ofFn]
    cases cs.all fun ct =>
      !(decide (ct.scope.toFinset ⊆ (a.v :: bagList child).toFinset) &&
        decide (a.v ∈ ct.scope)) ||
        ct.eval (ofRadix a.q (a.v :: bagList child) m) <;> rfl
  have hst_t₁ : (Memory.spec 0).clientState t (introFillStep (a, m)) =
      ⟨Function.update t.mem (a.tblPtr + m) entryVal, t.frontier⟩ := by
    rw [hst_ev, hval_eq]
  have hv_step : (Memory.spec w).ValidHistory t
      ((Memory.spec w).clientHistory t (introFillStep (a, m))) := by
    unfold introFillStep
    dsimp only
    refine validHistory_read_bind hc_addr_lt ?_
    refine validHistory_bind_step hv_ci ?_
    rw [hst_ci]
    refine validHistory_write_bind hdst_addr_lt ?_ (validHistory_pure w _ _)
    split_ifs
    · exact hcval_fit
    · exact fits_zero w
  have hc_step : memoryCost (introFillStep (a, m)) t ≤ stepCost := by
    have hr_s (x : ℕ) : (Memory.spec 0).clientState t (Memory.read x) = t := rfl
    unfold introFillStep
    dsimp only
    rw [memoryCost_bind', memoryCost_read, hr_s, memoryCost_bind', hst_ci,
      memoryCost_bind', memoryCost_write, memoryCost_pure]
    dsimp only [stepCost]
    omega
  exact ⟨hv_step, hst_t₁, hres_ev, hst_t₁ ▸ wellFormed_clientState hwf_t hv_step, hc_step⟩

private theorem introFillProg_realizes :
    Realizes .exact introFillProg WordEncoding.encode WordEncoding.encode
      (fun w a s =>
        0 < a.q ∧ Fits w 2 ∧ Fits w a.q ∧
        Fits w (a.bagPtr + a.bagLen) ∧
        Fits w (a.cTblPtr + a.tblLen) ∧
        Fits w (a.tblPtr + a.tblLen) ∧
        ∃ cs : List (ConstraintTable a.q),
          cs.length = a.numCons ∧
          a.consRawPtr + (cs.flatMap ConstraintTable.encode).length ≤ a.tblPtr ∧
          HoldsIn a.consRawPtr (cs.flatMap ConstraintTable.encode) s ∧
          Fits w (a.consRawPtr + (cs.flatMap ConstraintTable.encode).length))
      (fun _ _ => 0) := by
  unfold introFillProg
  realize [checkIntroConstraintsProg_realizes]
  obtain ⟨hq_pos, h2, hfit_q, hfit_bag, hfit_cTbl, hfit_tbl,
    cs, hcs_len, hcs_hi, hcs_h, hfit_cs⟩ := h
  have h1 : Fits w 1 := h2.of_le (by decide)
  refine iterationSafe_of_stepInv _ _ w _
    (fun (j : ℕ) (m : ℕ) (t : Memory.State) =>
      j ≤ d.tblLen ∧ m + j = d.tblLen ∧
      HoldsIn d.consRawPtr (cs.flatMap ConstraintTable.encode) t)
    (fun j m t ⟨hj_le, hm_eq, hcs_t⟩ => ?_)
    ⟨le_rfl, Nat.zero_add _, hcs_h⟩
  have hm_lt : m < d.tblLen := by omega
  have hfit_m : Fits w m := hfit_tbl.of_le (by omega)
  have hfit_m1 : Fits w (m + 1) := hfit_tbl.of_le (by omega)
  have hq_ne : d.q ≠ 0 := by omega
  have hdiv_le : m / d.q ≤ m := Nat.div_le_self m d.q
  have hfit_caddr : Fits w (d.cTblPtr + m / d.q) := hfit_cTbl.of_le (by omega)
  have hfit_taddr : Fits w (d.tblPtr + m) := hfit_tbl.of_le (by omega)
  have hci_safe :
      0 < d.q ∧ Fits w 2 ∧ Fits w d.q ∧ Fits w m ∧ Fits w (d.bagPtr + d.bagLen) ∧
        ∃ cs : List (ConstraintTable d.q),
          cs.length = d.numCons ∧
          HoldsIn d.consRawPtr (cs.flatMap ConstraintTable.encode) t ∧
          Fits w (d.consRawPtr + (cs.flatMap ConstraintTable.encode).length) :=
    ⟨hq_pos, h2, hfit_q, hfit_m, hfit_bag, cs, hcs_len, hcs_t, hfit_cs⟩
  obtain ⟨hst_ev, hres_ev⟩ := introFillStep_eval d m t
  refine ⟨?_, Nat.le_of_succ_le hj_le, ?_, ?_⟩
  · dsimp only [introFillStep]
    refine ⟨⟨hq_ne, hfit_caddr⟩, hci_safe, ⟨hfit_taddr, h1, ?_⟩, hfit_m1⟩
    split_ifs
  · rw [hres_ev]; omega
  · rw [hst_ev]
    exact holdsIn_write_outside hcs_t (.inr (by omega))

private structure CopyBagState where
  srcCur : ℕ
  dstCur : ℕ

private def CopyBagState.equiv : CopyBagState ≃ ℕ × ℕ where
  toFun s := (s.srcCur, s.dstCur)
  invFun := fun (srcCur, dstCur) => ⟨srcCur, dstCur⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding CopyBagState := .ofEquiv CopyBagState.equiv

private structure BagCopyArgs where
  src : ℕ
  dst : ℕ
  len : ℕ

private def BagCopyArgs.equiv : BagCopyArgs ≃ (ℕ × ℕ) × ℕ where
  toFun a := ((a.src, a.dst), a.len)
  invFun := fun ((src, dst), len) => ⟨src, dst, len⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding BagCopyArgs := .ofEquiv BagCopyArgs.equiv

private def copyBagStep (env : Unit × CopyBagState) : Memory.Prog CopyBagState := do
  let v ← Memory.read env.2.srcCur
  Memory.write env.2.dstCur v
  pure ⟨env.2.srcCur + 1, env.2.dstCur + 1⟩

private def copyBagProg (args : BagCopyArgs) : Memory.Prog Unit := do
  let _ ← iterate copyBagStep () args.len ⟨args.src, args.dst⟩
  pure ()

private theorem copyBagProg_spec {w : ℕ} (args : BagCopyArgs) {xs : List ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hxs : HoldsIn args.src xs s) (hlen : xs.length = args.len)
    (hdisj : args.src + args.len ≤ args.dst) (hdst : args.dst + args.len ≤ s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (copyBagProg args)) ∧
    ((Memory.spec 0).clientState s (copyBagProg args)).frontier = s.frontier ∧
    PreservesBelow args.dst s ((Memory.spec 0).clientState s (copyBagProg args)) ∧
    HoldsIn args.dst xs ((Memory.spec 0).clientState s (copyBagProg args)) ∧
    memoryCost (copyBagProg args) s ≤ 2 * args.len := by
  have hcost : memoryCost (copyBagProg args) s ≤ 2 * args.len := by
    unfold copyBagProg
    rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
    have hle := memoryCost_iterate_le_of copyBagStep 2 () (fun _ _ => le_rfl)
      args.len ⟨args.src, args.dst⟩ s
    omega
  suffices ∀ ys src dst st,
      Memory.WellFormed w st →
      HoldsIn src ys st →
      src + ys.length ≤ dst →
      dst + ys.length ≤ st.frontier →
      (Memory.spec w).ValidHistory st
        ((Memory.spec w).clientHistory st (iterate copyBagStep () ys.length ⟨src, dst⟩)) ∧
      ((Memory.spec 0).clientState st
        (iterate copyBagStep () ys.length ⟨src, dst⟩)).frontier = st.frontier ∧
      PreservesBelow dst st
        ((Memory.spec 0).clientState st (iterate copyBagStep () ys.length ⟨src, dst⟩)) ∧
      HoldsIn dst ys
        ((Memory.spec 0).clientState st (iterate copyBagStep () ys.length ⟨src, dst⟩)) by
    have hrun := this xs args.src args.dst s hwf hxs (by omega) (by omega)
    rw [hlen] at hrun
    unfold copyBagProg
    refine ⟨validHistory_bind_step hrun.1 (validHistory_pure w _ ()), ?_, ?_, ?_, hcost⟩
    · rw [StateTransitionSpec.clientState_bind]
      exact hrun.2.1
    · rw [StateTransitionSpec.clientState_bind]
      exact hrun.2.2.1
    · rw [StateTransitionSpec.clientState_bind]
      exact hrun.2.2.2
  intro ys
  induction ys with
  | nil =>
    intro src dst st _ _ _ hdst_st
    have h0 : iterate copyBagStep () 0 ⟨src, dst⟩ = pure ⟨src, dst⟩ := rfl
    simp only [List.length_nil, Nat.add_zero] at hdst_st ⊢
    rw [h0]
    exact ⟨validHistory_pure w st _, rfl, PreservesBelow.refl hdst_st, HoldsIn.nil hdst_st⟩
  | cons u rest ih =>
    intro src dst st hwf_st hsrc_st hdisj_st hdst_st
    rw [HoldsIn.cons_iff] at hsrc_st
    obtain ⟨hsrc_b, hmem_u, hrest_src⟩ := hsrc_st
    simp only [List.length_cons] at hdisj_st hdst_st ⊢
    have hsrc_lt : src < st.frontier := by omega
    have hdst_lt : dst < st.frontier := by omega
    have hv_fit : Fits w (st.mem src) := hwf_st.mem_fits src
    let st₁ : Memory.State := ⟨Function.update st.mem dst (st.mem src), st.frontier⟩
    have hv_step : (Memory.spec w).ValidHistory st
        ((Memory.spec w).clientHistory st (copyBagStep ((), ⟨src, dst⟩))) :=
      validHistory_read_bind hsrc_lt (validHistory_write_bind hdst_lt hv_fit
        (validHistory_pure w st₁ _))
    have hst₁ : (Memory.spec 0).clientState st (copyBagStep ((), ⟨src, dst⟩)) = st₁ := rfl
    have hres₁ : (Memory.spec 0).clientResult st (copyBagStep ((), ⟨src, dst⟩)) =
        ⟨src + 1, dst + 1⟩ := rfl
    have hwf₁ : Memory.WellFormed w st₁ := hst₁ ▸ wellFormed_clientState hwf_st hv_step
    have hp₁ : PreservesBelow dst st st₁ := preservesBelow_write le_rfl hdst_lt
    have hrest_st₁ : HoldsIn (src + 1) rest st₁ := hrest_src.mono (by omega) hp₁
    have hst₁_fr : st₁.frontier = st.frontier := rfl
    obtain ⟨hv_rest, hfr_rest, hp_rest, hhold_rest⟩ :=
      ih (src + 1) (dst + 1) st₁ hwf₁ hrest_st₁ (by omega) (by rw [hst₁_fr]; omega)
    change (Memory.spec w).ValidHistory st
        ((Memory.spec w).clientHistory st
          (copyBagStep ((), ⟨src, dst⟩) >>= iterate copyBagStep () rest.length)) ∧
      ((Memory.spec 0).clientState st
        (copyBagStep ((), ⟨src, dst⟩) >>= iterate copyBagStep () rest.length)).frontier =
        st.frontier ∧
      PreservesBelow dst st
        ((Memory.spec 0).clientState st
          (copyBagStep ((), ⟨src, dst⟩) >>= iterate copyBagStep () rest.length)) ∧
      HoldsIn dst (u :: rest)
        ((Memory.spec 0).clientState st
          (copyBagStep ((), ⟨src, dst⟩) >>= iterate copyBagStep () rest.length))
    refine ⟨validHistory_bind_step hv_step (by rwa [hst₁, hres₁]), ?_, ?_, ?_⟩
    · rw [StateTransitionSpec.clientState_bind, hst₁, hres₁]
      exact hfr_rest
    · rw [StateTransitionSpec.clientState_bind, hst₁, hres₁]
      exact hp₁.trans (hp_rest.mono_bound (by omega))
    · rw [StateTransitionSpec.clientState_bind, hst₁, hres₁, HoldsIn.cons_iff]
      refine ⟨by rw [hfr_rest, hst₁_fr]; omega, ?_, hhold_rest⟩
      rw [hp_rest.2.2 dst (by omega)]
      simp only [st₁, Function.update_self, hmem_u]

private theorem copyBagProg_realizes :
    Realizes .exact copyBagProg WordEncoding.encode WordEncoding.encode
      (fun w args _ => Fits w 1 ∧ Fits w (args.src + args.len) ∧ Fits w (args.dst + args.len))
      (fun _ _ => 0) := by
  unfold copyBagProg
  realize
  obtain ⟨_, hsrc_fit, hdst_fit⟩ := h
  refine iterationSafe_of_stepInv _ _ w _
    (fun (j : ℕ) (st : CopyBagState) (_ : Memory.State) =>
      st.srcCur + j = d.src + d.len ∧ st.dstCur + j = d.dst + d.len)
    (fun j st _ ⟨hsrc, hdst⟩ => ?_)
    ⟨rfl, rfl⟩
  dsimp only [copyBagStep]
  refine ⟨⟨hsrc_fit.of_le (by omega), hdst_fit.of_le (by omega)⟩, ?_, ?_⟩
  · change (st.srcCur + 1) + j = d.src + d.len
    omega
  · change (st.dstCur + 1) + j = d.dst + d.len
    omega

private structure IntroNodeArgs where
  q : ℕ
  v : ℕ
  consRawPtr : ℕ
  numCons : ℕ
  dChild : ℕ
  dCur : ℕ

private def IntroNodeArgs.equiv :
    IntroNodeArgs ≃ ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a := (((((a.q, a.v), a.consRawPtr), a.numCons), a.dChild), a.dCur)
  invFun := fun (((((q, v), cp), nc), dch), dc) => ⟨q, v, cp, nc, dch, dc⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding IntroNodeArgs := .ofEquiv IntroNodeArgs.equiv

private def introNodeProg (a : IntroNodeArgs) : Memory.Prog Unit := do
  let cBagPtr ← Memory.read a.dChild
  let cBagLen ← Memory.read (a.dChild + 1)
  let cTblPtr ← Memory.read (a.dChild + 2)
  let cTblLen ← Memory.read (a.dChild + 3)
  let bagLen := cBagLen + 1
  let bagPtr ← Memory.allocDirty bagLen
  Memory.write bagPtr a.v
  let _ ← copyBagProg ⟨cBagPtr, bagPtr + 1, cBagLen⟩
  let tblLen := a.q * cTblLen
  let tblPtr ← Memory.allocDirty tblLen
  let _ ← introFillProg
    ⟨a.q, a.v, bagPtr, bagLen, a.consRawPtr, a.numCons, cTblPtr, tblPtr, tblLen⟩
  writeDescProg ⟨a.dCur, bagPtr, bagLen, tblPtr, tblLen⟩

private theorem introNodeProg_spec {w F_lo : ℕ} (counting : Bool) (a : IntroNodeArgs)
    (hq : 0 < a.q) {child : NiceTree ℕ} {cs : List (ConstraintTable a.q)} {vars : List ℕ}
    {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hfit_v : Fits w a.v)
    (hcs : HoldsIn a.consRawPtr (cs.flatMap ConstraintTable.encode) s)
    (hcs_len : cs.length = a.numCons)
    (hcs_hi : a.consRawPtr + (cs.flatMap ConstraintTable.encode).length ≤ F_lo)
    (hchild : NodeDescAt F_lo counting a.q cs vars child a.dChild s)
    (hdCur : a.dCur + 4 ≤ F_lo)
    (hFlo : F_lo ≤ s.frontier)
    (hfit_peak : Fits w (s.frontier + ((a.v :: bagList child).length +
      a.q ^ (a.v :: bagList child).length))) :
    let sEnd := (Memory.spec 0).clientState s (introNodeProg a)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (introNodeProg a)) ∧
    sEnd.frontier ≤
      s.frontier + ((a.v :: bagList child).length + a.q ^ (a.v :: bagList child).length) ∧
    FrameOutsideRange a.dCur (a.dCur + 4) s sEnd ∧
    NodeDescAt F_lo counting a.q cs vars (.introduce a.v child) a.dCur sEnd ∧
    memoryCost (introNodeProg a) s ≤
      11 + 2 * (bagList child).length +
        a.q ^ (a.v :: bagList child).length *
          (2 + 3 * a.numCons +
            (cs.map fun ct => ct.scope.length).sum *
              (2 * (a.v :: bagList child).length + 3)) := by
  have hd_ch := hchild.desc_hi
  have hm_cbLen : s.mem (a.dChild + 1) = (bagList child).length := hchild.bag_len
  have hm_ctLen : s.mem (a.dChild + 3) = a.q ^ (bagList child).length := hchild.tbl_len
  let cBagPtr := s.mem a.dChild
  let cBagLen := (bagList child).length
  let cTblPtr := s.mem (a.dChild + 2)
  let cTblLen := a.q ^ cBagLen
  let bagLen := cBagLen + 1
  have hbagLen_eq : (a.v :: bagList child).length = bagLen := rfl
  let tblLen := a.q * cTblLen
  have htblLen_eq : tblLen = a.q ^ bagLen := by
    dsimp only [tblLen, cTblLen, bagLen]
    rw [Nat.pow_succ, Nat.mul_comm]
  let bagPtr := s.frontier
  let s₁ := (Memory.spec 0).clientState s (Memory.allocDirty bagLen)
  have hs₁_fr : s₁.frontier = bagPtr + bagLen := rfl
  have hp₁ : PreservesBelow bagPtr s s₁ := preservesBelow_allocDirty s bagLen
  have hfit_fr₁ : Fits w (s.frontier + bagLen) :=
    hfit_peak.of_le (by rw [hbagLen_eq, ← htblLen_eq]; omega)
  have hv₁ : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (Memory.allocDirty bagLen)) :=
    validHistory_allocDirty hfit_fr₁
  have hwf₁ : Memory.WellFormed w s₁ := wellFormed_clientState hwf hv₁
  let s₂ : Memory.State := ⟨Function.update s₁.mem bagPtr a.v, s₁.frontier⟩
  have hlt_bp : bagPtr < s₁.frontier := by rw [hs₁_fr]; dsimp only [bagLen]; omega
  have hp₂ : PreservesBelow bagPtr s₁ s₂ := preservesBelow_write le_rfl hlt_bp
  have hv₂ : (Memory.spec w).ValidHistory s₁
      ((Memory.spec w).clientHistory s₁ (Memory.write bagPtr a.v)) :=
    validHistory_write hlt_bp hfit_v
  have hwf₂ : Memory.WellFormed w s₂ := wellFormed_clientState hwf₁ hv₂
  have hcBag_s₂ : HoldsIn cBagPtr (bagList child) s₂ :=
    hchild.bag_holds.mono_frontier (hp₁.trans hp₂)
  obtain ⟨hv_cp, hfr_cp, hp_cp, hcp_holds, hc_cp⟩ :=
    copyBagProg_spec (w := w) ⟨cBagPtr, bagPtr + 1, cBagLen⟩ hwf₂ hcBag_s₂ rfl
      (by have := hchild.bag_holds.1; dsimp only [cBagPtr, cBagLen, bagPtr]; omega)
      (by dsimp only [s₂]; rw [hs₁_fr]; dsimp only [bagLen]; omega)
  let s₃ := (Memory.spec 0).clientState s₂ (copyBagProg ⟨cBagPtr, bagPtr + 1, cBagLen⟩)
  have hwf₃ : Memory.WellFormed w s₃ := wellFormed_clientState hwf₂ hv_cp
  have hs₃_fr : s₃.frontier = bagPtr + bagLen := by rw [hfr_cp]; exact hs₁_fr
  have hp_s_s₃ : PreservesBelow bagPtr s s₃ :=
    (hp₁.trans hp₂).trans (hp_cp.mono_bound (Nat.le_succ bagPtr))
  have hLB_s₃ : HoldsIn bagPtr (a.v :: bagList child) s₃ := by
    rw [HoldsIn.cons_iff]
    refine ⟨by rw [hs₃_fr]; dsimp only [bagLen, cBagLen]; omega, ?_, hcp_holds⟩
    rw [hp_cp.2.2 bagPtr (Nat.lt_succ_self bagPtr)]
    exact Function.update_self _ _ _
  let tblPtr := s₃.frontier
  let s₄ := (Memory.spec 0).clientState s₃ (Memory.allocDirty tblLen)
  have hs₄_fr : s₄.frontier = tblPtr + tblLen := rfl
  have hp₄ : PreservesBelow tblPtr s₃ s₄ := preservesBelow_allocDirty s₃ tblLen
  have hfit_fr₄ : Fits w (s₃.frontier + tblLen) := by
    rw [hs₃_fr]
    exact hfit_peak.of_le (by rw [hbagLen_eq, ← htblLen_eq]; dsimp only [bagPtr]; omega)
  have hv₄ : (Memory.spec w).ValidHistory s₃
      ((Memory.spec w).clientHistory s₃ (Memory.allocDirty tblLen)) :=
    validHistory_allocDirty hfit_fr₄
  have hwf₄ : Memory.WellFormed w s₄ := wellFormed_clientState hwf₃ hv₄
  have hp_s_s₄ : PreservesBelow bagPtr s s₄ :=
    hp_s_s₃.trans (hp₄.mono_bound (by dsimp only [tblPtr]; rw [hs₃_fr]; omega))
  let fillArgs : IntroFillArgs :=
    ⟨a.q, a.v, bagPtr, bagLen, a.consRawPtr, a.numCons, cTblPtr, tblPtr, tblLen⟩
  obtain ⟨hv_fill, hfr_fill, hp_fill, htbl_fill, hc_fill⟩ :=
    introFillProg_spec (w := w) counting fillArgs hq hwf₄ rfl
      (hLB_s₃.mono_frontier hp₄) hbagLen_eq
      (by dsimp only [fillArgs, tblPtr]; rw [hs₃_fr])
      (hcs.mono_frontier hp_s_s₄) hcs_len
      (by dsimp only [fillArgs, tblPtr]; rw [hs₃_fr]; dsimp only [bagPtr]; omega)
      (hchild.tbl_holds.mono_frontier hp_s_s₄)
      (by have := hchild.tbl_holds.1; rw [length_dpInstTree] at this
          dsimp only [fillArgs, cTblPtr, tblPtr]; rw [hs₃_fr]; dsimp only [bagPtr]; omega)
      htblLen_eq
      (by rw [hs₄_fr])
  let s₅ := (Memory.spec 0).clientState s₄ (introFillProg fillArgs)
  have hs₅_fr : s₅.frontier = tblPtr + tblLen := by rw [hfr_fill, hs₄_fr]
  have hp_s_s₅ : PreservesBelow bagPtr s s₅ :=
    hp_s_s₄.trans (hp_fill.mono_bound (by dsimp only [fillArgs, tblPtr]; rw [hs₃_fr]; omega))
  have hLB_s₅ : HoldsIn bagPtr (a.v :: bagList child) s₅ :=
    (hLB_s₃.mono_frontier hp₄).mono (F := tblPtr)
      (by rw [hbagLen_eq, ← hs₃_fr]) hp_fill
  have hd_s₅ : a.dCur + 4 ≤ s₅.frontier := by
    rw [hs₅_fr]; dsimp only [tblPtr]; rw [hs₃_fr]; dsimp only [bagPtr]; omega
  have hfit_bt : Fits w (bagPtr + bagLen + tblLen) := by rwa [hs₃_fr] at hfit_fr₄
  obtain ⟨hv_wd, hfr_wd, hframe_wd, hm0, hm1, hm2, hm3, hc_wd⟩ :=
    writeDescProg_spec (w := w) ⟨a.dCur, bagPtr, bagLen, tblPtr, tblLen⟩ hd_s₅
      (hfit_bt.of_le (by dsimp only [bagPtr, bagLen, tblLen]; omega))
      (hfit_bt.of_le (by dsimp only [bagPtr, bagLen, tblLen]; omega))
      (hfit_bt.of_le (by dsimp only [tblPtr]; rw [hs₃_fr]; omega))
      (hfit_bt.of_le (by dsimp only [bagPtr, bagLen, tblLen]; omega))
  dsimp only at hm0 hm1 hm2 hm3
  let sEnd := (Memory.spec 0).clientState s₅
    (writeDescProg ⟨a.dCur, bagPtr, bagLen, tblPtr, tblLen⟩)
  have hr_s (x : ℕ) : (Memory.spec 0).clientState s (Memory.read x) = s := rfl
  have hr_r (x : ℕ) : (Memory.spec 0).clientResult s (Memory.read x) = s.mem x := rfl
  have ha1_s : (Memory.spec 0).clientState s (Memory.allocDirty bagLen) = s₁ := rfl
  have ha1_r : (Memory.spec 0).clientResult s (Memory.allocDirty bagLen) = bagPtr := rfl
  have hw_s : (Memory.spec 0).clientState s₁ (Memory.write bagPtr a.v) = s₂ := rfl
  have ha4_s : (Memory.spec 0).clientState s₃ (Memory.allocDirty tblLen) = s₄ := rfl
  have ha4_r : (Memory.spec 0).clientResult s₃ (Memory.allocDirty tblLen) = tblPtr := rfl
  have hsEnd_eq : (Memory.spec 0).clientState s (introNodeProg a) = sEnd := by
    unfold introNodeProg
    dsimp only
    iterate 4 rw [StateTransitionSpec.clientState_bind, hr_s, hr_r]
    rw [hm_cbLen, hm_ctLen]
    rw [StateTransitionSpec.clientState_bind, ha1_s, ha1_r,
      StateTransitionSpec.clientState_bind, hw_s,
      StateTransitionSpec.clientState_bind]
    change (Memory.spec 0).clientState s₃
      (Memory.allocDirty tblLen >>= fun tp =>
        introFillProg ⟨a.q, a.v, bagPtr, bagLen, a.consRawPtr, a.numCons, cTblPtr, tp, tblLen⟩ >>=
          fun _ => writeDescProg ⟨a.dCur, bagPtr, bagLen, tp, tblLen⟩) = sEnd
    rw [StateTransitionSpec.clientState_bind, ha4_s, ha4_r,
      StateTransitionSpec.clientState_bind]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold introNodeProg
    dsimp only
    refine validHistory_read_bind (by omega) ?_
    refine validHistory_read_bind (by omega) ?_
    refine validHistory_read_bind (by omega) ?_
    refine validHistory_read_bind (by omega) ?_
    rw [hm_cbLen, hm_ctLen]
    refine validHistory_bind_step hv₁ ?_
    rw [ha1_s, ha1_r]
    refine validHistory_bind_step hv₂ ?_
    rw [hw_s]
    refine validHistory_bind_step hv_cp ?_
    change (Memory.spec w).ValidHistory s₃ _
    refine validHistory_bind_step hv₄ ?_
    rw [ha4_s, ha4_r]
    exact validHistory_bind_step hv_fill hv_wd
  · rw [hsEnd_eq, hfr_wd, hs₅_fr]
    dsimp only [tblPtr]
    rw [hs₃_fr, hbagLen_eq, ← htblLen_eq]
    dsimp only [bagPtr]
    omega
  · rw [hsEnd_eq]
    exact (FrameOutsideRange.of_preservesBelow a.dCur (a.dCur + 4) hp_s_s₅).trans hframe_wd
  · rw [hsEnd_eq]
    refine ⟨hdCur, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hm0]; exact hFlo
    · rw [hm1]; rfl
    · rw [hm0]
      exact hLB_s₅.frame_outsideRange (.inr (le_trans hdCur hFlo)) hframe_wd
    · rw [hm2]; dsimp only [tblPtr]; rw [hs₃_fr]; dsimp only [bagPtr]; omega
    · rw [hm3]; exact htblLen_eq
    · rw [hm2]
      exact htbl_fill.frame_outsideRange
        (.inr (by dsimp only [fillArgs, tblPtr]; rw [hs₃_fr]; dsimp only [bagPtr]; omega))
        hframe_wd
  · unfold introNodeProg
    dsimp only
    iterate 4 rw [memoryCost_bind', memoryCost_read, hr_s, hr_r]
    rw [hm_cbLen, hm_ctLen, memoryCost_bind', memoryCost_allocDirty, ha1_s, ha1_r,
      memoryCost_bind', memoryCost_write, hw_s, memoryCost_bind']
    change 1 + (1 + (1 + (1 + (1 + (1 + (memoryCost (copyBagProg _) s₂ +
      memoryCost (Memory.allocDirty tblLen >>= _) s₃)))))) ≤ _
    rw [memoryCost_bind', memoryCost_allocDirty, ha4_s, ha4_r, memoryCost_bind']
    change 1 + (1 + (1 + (1 + (1 + (1 + (memoryCost (copyBagProg _) s₂ +
      (1 + (memoryCost (introFillProg fillArgs) s₄ +
        memoryCost (writeDescProg ⟨a.dCur, bagPtr, bagLen, tblPtr, tblLen⟩) s₅)))))))) ≤ _
    have hcost_eq :
        a.q ^ (a.v :: bagList child).length *
          (2 + 3 * a.numCons +
            (cs.map fun ct => ct.scope.length).sum * (2 * (a.v :: bagList child).length + 3)) =
          tblLen *
            (2 + 3 * a.numCons + (cs.map fun ct => ct.scope.length).sum * (2 * bagLen + 3)) := by
      rw [htblLen_eq, hbagLen_eq]
    dsimp only [s₅, fillArgs, cBagPtr, cBagLen, cTblPtr, cTblLen, bagPtr, bagLen, tblPtr, tblLen]
      at hc_cp hc_fill hc_wd hcost_eq ⊢
    omega

private theorem introNodeProg_realizes :
    Realizes .exact introNodeProg WordEncoding.encode WordEncoding.encode
      (fun w a s =>
        0 < a.q ∧ Fits w 3 ∧ Fits w a.q ∧ Fits w a.v ∧
        Fits w (a.dChild + 3) ∧ Fits w (a.dCur + 3) ∧
        ∃ (F_lo : ℕ) (counting : Bool) (child : NiceTree ℕ)
          (cs : List (ConstraintTable a.q)) (vars : List ℕ),
          Memory.WellFormed w s ∧
          cs.length = a.numCons ∧
          HoldsIn a.consRawPtr (cs.flatMap ConstraintTable.encode) s ∧
          a.consRawPtr + (cs.flatMap ConstraintTable.encode).length ≤ F_lo ∧
          NodeDescAt F_lo counting a.q cs vars child a.dChild s ∧
          F_lo ≤ s.frontier ∧
          Fits w (s.frontier + ((a.v :: bagList child).length +
            a.q ^ (a.v :: bagList child).length)))
      (fun _ _ => 0) := by
  unfold introNodeProg
  realize [copyBagProg_realizes, introFillProg_realizes, writeDescProg_realizes]
  all_goals
    obtain ⟨hq, h3, hfit_q, hfit_v, hdCh, hdCur, F_lo, counting, child, cs, vars, hwf, hcs_len,
      hcs_h, hcs_hi, hch, hFlo, hfit_peak⟩ := h
    have h1 : Fits w 1 := h3.of_le (by decide)
    have h2 : Fits w 2 := h3.of_le (by decide)
    try rw [hch.bag_len]
    try rw [hch.tbl_len]
    let bagLen := (bagList child).length + 1
    let tblLen := d.q * d.q ^ (bagList child).length
    have htblLen_eq : tblLen = d.q ^ (d.v :: bagList child).length := by
      dsimp only [tblLen]; simp [Nat.pow_succ, Nat.mul_comm]
    let s₁ := (Memory.spec 0).clientState s (Memory.allocDirty bagLen)
    have hp₁ : PreservesBelow s.frontier s s₁ := preservesBelow_allocDirty s bagLen
    have hv₁ : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (Memory.allocDirty bagLen)) :=
      validHistory_allocDirty
        (hfit_peak.of_le (by dsimp only [bagLen]; rw [List.length_cons]; omega))
    have hwf₁ : Memory.WellFormed w s₁ := wellFormed_clientState hwf hv₁
    let s₂ : Memory.State := ⟨Function.update s₁.mem s.frontier d.v, s₁.frontier⟩
    have hlt_bp : s.frontier < s₁.frontier := by
      change s.frontier < s.frontier + bagLen; dsimp only [bagLen]; omega
    have hp₂ : PreservesBelow s.frontier s₁ s₂ := preservesBelow_write le_rfl hlt_bp
    have hwf₂ : Memory.WellFormed w s₂ :=
      wellFormed_clientState hwf₁ (validHistory_write hlt_bp hfit_v)
    obtain ⟨_, hfr_cp, hp_cp, _, _⟩ :=
      copyBagProg_spec (w := w) ⟨s.mem d.dChild, s.frontier + 1, (bagList child).length⟩
        hwf₂ (hch.bag_holds.mono_frontier (hp₁.trans hp₂)) rfl
        (by have := hch.bag_holds.1; dsimp only; omega)
        (by dsimp only [s₂, s₁, bagLen]; change s.frontier + 1 + _ ≤ s.frontier + _; omega)
    let s₃ := (Memory.spec 0).clientState s₂
      (copyBagProg ⟨s.mem d.dChild, s.frontier + 1, (bagList child).length⟩)
    have hs₃_fr : s₃.frontier = s.frontier + bagLen := hfr_cp
    let s₄ := (Memory.spec 0).clientState s₃ (Memory.allocDirty tblLen)
    have hp₄ : PreservesBelow s₃.frontier s₃ s₄ := preservesBelow_allocDirty s₃ tblLen
    have hp_all : PreservesBelow s.frontier s s₄ :=
      ((hp₁.trans hp₂).trans (hp_cp.mono_bound (Nat.le_succ s.frontier))).trans
        (hp₄.mono_bound (by rw [hs₃_fr]; omega))
    have hc_bag := hch.bag_holds.1
    have hc_tbl := hch.tbl_holds.1
    rw [length_dpInstTree] at hc_tbl
    have hpow_ge : d.q ^ (bagList child).length ≤ tblLen := by
      rw [htblLen_eq]; exact Nat.pow_le_pow_right hq (Nat.le_succ _)
    have hf_ch1 : Fits w (d.dChild + 1) := hdCh.of_le (by omega)
    have hf_ch2 : Fits w (d.dChild + 2) := hdCh.of_le (by omega)
    have hf_bagLen : Fits w bagLen :=
      hfit_peak.of_le (by dsimp only [bagLen]; rw [List.length_cons]; omega)
    have hf_fr1 : Fits w (s.frontier + 1) :=
      hfit_peak.of_le (by rw [List.length_cons]; omega)
    have hf_csrc : Fits w (s.mem d.dChild + (bagList child).length) := hfit_peak.of_le (by omega)
    have hf_cdst : Fits w (s.frontier + 1 + (bagList child).length) :=
      hfit_peak.of_le (by rw [List.length_cons]; omega)
    have hf_tblLen : Fits w tblLen := hfit_peak.of_le (by rw [htblLen_eq]; omega)
    have hf_bagEnd : Fits w (s.frontier + bagLen) :=
      hfit_peak.of_le (by dsimp only [bagLen]; rw [List.length_cons]; omega)
    have hf_ctEnd : Fits w (s.mem (d.dChild + 2) + tblLen) :=
      hfit_peak.of_le (by rw [htblLen_eq] at *; omega)
    have hf_tEnd : Fits w (s₃.frontier + tblLen) :=
      hfit_peak.of_le
        (by rw [hs₃_fr, htblLen_eq]; dsimp only [bagLen]; rw [List.length_cons]; omega)
    have hexists_cs : ∃ cs : List (ConstraintTable d.q),
        cs.length = d.numCons ∧
        d.consRawPtr + (cs.flatMap ConstraintTable.encode).length ≤ s₃.frontier ∧
        HoldsIn d.consRawPtr (cs.flatMap ConstraintTable.encode) s₄ ∧
        Fits w (d.consRawPtr + (cs.flatMap ConstraintTable.encode).length) :=
      ⟨cs, hcs_len, by rw [hs₃_fr]; omega, hcs_h.mono_frontier hp_all, hfit_peak.of_le (by omega)⟩
    repeat (
      first
      | exact hexists_cs
      | exact hq
      | exact h1
      | exact h2
      | exact hfit_q
      | exact hdCh
      | exact hdCur
      | exact hf_ch1
      | exact hf_ch2
      | exact hf_bagLen
      | exact hf_fr1
      | exact hf_csrc
      | exact hf_cdst
      | exact hf_tblLen
      | exact hf_bagEnd
      | exact hf_ctEnd
      | exact hf_tEnd)

/-! #### 3. Forget node handler (`forgetInnerProg`, `forgetFillProg`, `forgetNodeProg`) -/

private structure ForgetInnerArgs where
  mode : ℕ
  q : ℕ
  v : ℕ
  bagPtr : ℕ
  bagLen : ℕ
  m : ℕ
  cBagPtr : ℕ
  cBagLen : ℕ
  cTblPtr : ℕ
  dLim : ℕ

private def ForgetInnerArgs.equiv :
    ForgetInnerArgs ≃ ((((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a :=
    (((((((((a.mode, a.q), a.v), a.bagPtr), a.bagLen), a.m), a.cBagPtr), a.cBagLen),
      a.cTblPtr), a.dLim)
  invFun := fun (((((((((md, q), v), bp), bl), m), cbp), cbl), ctp), dl) =>
    ⟨md, q, v, bp, bl, m, cbp, cbl, ctp, dl⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding ForgetInnerArgs := .ofEquiv ForgetInnerArgs.equiv

private def forgetInnerStep (p : ForgetInnerArgs × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let a := p.1
  let d := p.2.1
  let acc := p.2.2
  let idx ← radixProjProg ⟨a.q, a.bagPtr, a.bagLen, a.m, a.v, d, 1, a.cBagPtr, a.cBagLen⟩
  let cVal ← Memory.read (a.cTblPtr + idx)
  let nextAcc := if a.mode = 1 then acc + cVal else (if cVal = 0 then acc else 1)
  pure (d + 1, nextAcc)

private def forgetInnerProg (a : ForgetInnerArgs) : Memory.Prog ℕ := do
  let res ← iterate forgetInnerStep a a.dLim (0, 0)
  pure res.2

private theorem forgetInnerStep_eval (a : ForgetInnerArgs) (d acc : ℕ) (t : Memory.State) :
    let idx := (Memory.spec 0).clientResult t
      (radixProjProg ⟨a.q, a.bagPtr, a.bagLen, a.m, a.v, d, 1, a.cBagPtr, a.cBagLen⟩)
    let cVal := t.mem (a.cTblPtr + idx)
    let nextAcc := if a.mode = 1 then acc + cVal else (if cVal = 0 then acc else 1)
    (Memory.spec 0).clientState t (forgetInnerStep (a, (d, acc))) = t ∧
    (Memory.spec 0).clientResult t (forgetInnerStep (a, (d, acc))) = (d + 1, nextAcc) := by
  have hr_st (x : ℕ) : (Memory.spec 0).clientState t (Memory.read x) = t := rfl
  have hr_res (x : ℕ) : (Memory.spec 0).clientResult t (Memory.read x) = t.mem x := rfl
  unfold forgetInnerStep
  dsimp only
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    radixProjProg_state,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_st, hr_res]
  exact ⟨rfl, rfl⟩

private theorem forgetInnerProg_state (a : ForgetInnerArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (forgetInnerProg a) = s := by
  unfold forgetInnerProg
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of forgetInnerStep a
    (fun st m => (forgetInnerStep_eval a st.1 st.2 m).1) a.dLim (0, 0) s

private theorem forgetInnerProg_spec {w : ℕ} (counting : Bool) (a : ForgetInnerArgs)
    (hq : 0 < a.q) (hmode : a.mode = if counting then 1 else 0)
    {LB cBagL cTbl : List ℕ} {s : Memory.State}
    (hLB : HoldsIn a.bagPtr LB s) (hLB_len : LB.length = a.bagLen)
    (hcBag : HoldsIn a.cBagPtr cBagL s) (hcBag_len : cBagL.length = a.cBagLen)
    (hcTbl : HoldsIn a.cTblPtr cTbl s) (hcTbl_len : cTbl.length = a.q ^ a.cBagLen) :
    let addFn : ℕ → ℕ → ℕ :=
      if counting then (· + ·) else fun acc val => if val = 0 then acc else 1
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (forgetInnerProg a)) ∧
    (Memory.spec 0).clientState s (forgetInnerProg a) = s ∧
    (Memory.spec 0).clientResult s (forgetInnerProg a) =
      dpAlgFold 0 addFn a.dLim
        (fun d => cTbl.getD (toRadix a.q cBagL (Function.update (ofRadix a.q LB a.m) a.v d)) 0) ∧
    memoryCost (forgetInnerProg a) s ≤ a.dLim * (a.cBagLen * (a.bagLen + 1) + 1) := by
  let addFn : ℕ → ℕ → ℕ :=
    if counting then (· + ·) else fun acc val => if val = 0 then acc else 1
  let stepCost := a.cBagLen * (a.bagLen + 1) + 1
  let g (d : ℕ) := cTbl.getD (toRadix a.q cBagL (Function.update (ofRadix a.q LB a.m) a.v d)) 0
  suffices ∀ rem, rem ≤ a.dLim →
      let d := a.dLim - rem
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (iterate forgetInnerStep a rem (d, dpAlgFold 0 addFn d g))) ∧
      ((Memory.spec 0).clientResult s
        (iterate forgetInnerStep a rem (d, dpAlgFold 0 addFn d g))).2 =
        dpAlgFold 0 addFn a.dLim g ∧
      memoryCost (iterate forgetInnerStep a rem (d, dpAlgFold 0 addFn d g)) s ≤
        rem * stepCost by
    have hrun := this a.dLim le_rfl
    simp only [Nat.sub_self, dpAlgFold] at hrun
    refine ⟨?_, forgetInnerProg_state a s, ?_, ?_⟩
    · unfold forgetInnerProg
      exact validHistory_bind_step hrun.1 (validHistory_pure w _ _)
    · unfold forgetInnerProg
      rw [StateTransitionSpec.clientResult_bind]
      exact hrun.2.1
    · unfold forgetInnerProg
      rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
      exact hrun.2.2
  intro rem
  induction rem with
  | zero =>
    intro _
    have h0 : iterate forgetInnerStep a 0
        (a.dLim - 0, dpAlgFold 0 addFn (a.dLim - 0) g) =
        pure (a.dLim - 0, dpAlgFold 0 addFn (a.dLim - 0) g) := rfl
    have hr : (Memory.spec 0).clientResult s
        (pure (a.dLim, dpAlgFold 0 addFn a.dLim g)) =
        (a.dLim, dpAlgFold 0 addFn a.dLim g) := rfl
    simp only [Nat.sub_zero] at h0 ⊢
    rw [h0]
    exact ⟨validHistory_pure w s _, by rw [hr], by simp [memoryCost_pure]⟩
  | succ k ih =>
    intro hk_le
    let d := a.dLim - (k + 1)
    let curAcc := dpAlgFold 0 addFn d g
    obtain ⟨hv_rp, hst_rp, hr_rp, hc_rp⟩ :=
      radixProjProg_spec (w := w)
        ⟨a.q, a.bagPtr, a.bagLen, a.m, a.v, d, 1, a.cBagPtr, a.cBagLen⟩
        hLB hLB_len hcBag hcBag_len
    simp only [radixProjAssign, ↓reduceIte] at hr_rp hc_rp
    let idx := toRadix a.q cBagL (Function.update (ofRadix a.q LB a.m) a.v d)
    have hidx_lt : idx < cTbl.length := by
      rw [hcTbl_len, ← hcBag_len]
      exact toRadix_lt hq _ _
    have haddr_lt : a.cTblPtr + idx < s.frontier := by have := hcTbl.1; omega
    have hm_cval : s.mem (a.cTblPtr + idx) = g d := by
      dsimp only [g, idx]
      rw [hcTbl.get _ hidx_lt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hidx_lt, Option.getD_some]
    obtain ⟨hst_ev, hres_ev⟩ := forgetInnerStep_eval a d curAcc s
    have hnext_eq :
        (if a.mode = 1 then curAcc + g d else if g d = 0 then curAcc else 1) =
          dpAlgFold 0 addFn (d + 1) g := by
      rw [hmode]
      cases counting <;> rfl
    have hres_ev' :
        (Memory.spec 0).clientResult s (forgetInnerStep (a, (d, curAcc))) =
          (a.dLim - k, dpAlgFold 0 addFn (a.dLim - k) g) := by
      have hd_succ : d + 1 = a.dLim - k := by dsimp only [d]; omega
      rw [hres_ev]
      dsimp only [idx] at hm_cval
      rw [hr_rp, hm_cval, hnext_eq, hd_succ]
    have hv_step : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (forgetInnerStep (a, (d, curAcc)))) := by
      unfold forgetInnerStep
      dsimp only
      refine validHistory_bind_step hv_rp ?_
      rw [hst_rp, hr_rp]
      exact validHistory_read_bind haddr_lt (validHistory_pure w s _)
    have hc_step : memoryCost (forgetInnerStep (a, (d, curAcc))) s ≤ stepCost := by
      have hr_s (x : ℕ) : (Memory.spec 0).clientState s (Memory.read x) = s := rfl
      unfold forgetInnerStep
      dsimp only
      rw [memoryCost_bind', hst_rp, memoryCost_bind', memoryCost_read, hr_s, memoryCost_pure]
      dsimp only [stepCost]
      omega
    obtain ⟨hv_rem, hr_rem, hc_rem⟩ := ih (Nat.le_of_succ_le hk_le)
    have hiter_eq : iterate forgetInnerStep a (k + 1) (d, curAcc) =
        (forgetInnerStep (a, (d, curAcc)) >>= iterate forgetInnerStep a k) := rfl
    change (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (iterate forgetInnerStep a (k + 1) (d, curAcc))) ∧ _ ∧ _
    rw [hiter_eq]
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_ev, hres_ev']), ?_, ?_⟩
    · rw [StateTransitionSpec.clientResult_bind, hst_ev, hres_ev']
      exact hr_rem
    · rw [memoryCost_bind', hst_ev, hres_ev']
      calc _ ≤ stepCost + k * stepCost := Nat.add_le_add hc_step hc_rem
        _ = (k + 1) * stepCost := by ring

private theorem forgetInnerProg_realizes :
    Realizes .exact forgetInnerProg WordEncoding.encode WordEncoding.encode
      (fun w a s =>
        0 < a.q ∧ Fits w 1 ∧ Fits w a.q ∧ Fits w a.m ∧ Fits w a.dLim ∧
        Fits w (a.bagPtr + a.bagLen) ∧
        Fits w (a.cBagPtr + a.cBagLen) ∧
        Fits w (a.q ^ a.cBagLen) ∧
        Fits w (a.cTblPtr + a.q ^ a.cBagLen) ∧
        ∃ (cTbl : List ℕ) (cCap : ℕ),
          HoldsIn a.cTblPtr cTbl s ∧
          cTbl.length = a.q ^ a.cBagLen ∧
          (∀ x ∈ cTbl, x ≤ cCap) ∧
          (a.mode = 1 → Fits w (a.dLim * cCap)))
      (fun _ _ => 0) := by
  have hraw :
      Realizes .exact forgetInnerProg WordEncoding.encode WordEncoding.encode
        (fun w a s =>
          0 < a.q ∧ Fits w 1 ∧ Fits w a.q ∧ Fits w a.m ∧ Fits w a.dLim ∧
          Fits w (a.bagPtr + a.bagLen) ∧
          Fits w (a.cBagPtr + a.cBagLen) ∧
          Fits w (a.q ^ a.cBagLen) ∧
          Fits w (a.cTblPtr + a.q ^ a.cBagLen) ∧
          ∃ (cTbl : List ℕ) (cCap : ℕ),
            HoldsIn a.cTblPtr cTbl s ∧
            cTbl.length = a.q ^ a.cBagLen ∧
            (∀ x ∈ cTbl, x ≤ cCap) ∧
            (a.mode = 1 → Fits w (a.dLim * cCap)))
        (fun a _ => a.dLim) := by
    unfold forgetInnerProg
    realize [radixProjProg_realizes]
    · obtain ⟨hq_pos, h1, hfit_q, hfit_m, hfit_dLim, hfit_bag, hfit_cBag, hfit_cPow, hfit_cTbl,
        cTbl, cCap, hcTbl_h, hcTbl_len, hcTbl_le, hfit_sumCap⟩ := h
      refine iterationSafe_of_stepInv _ _ w _
        (fun (j : ℕ) (st : ℕ × ℕ) (t : Memory.State) =>
          j ≤ d.dLim ∧ st.1 + j = d.dLim ∧
          HoldsIn d.cTblPtr cTbl t ∧
          (if d.mode = 1 then st.2 ≤ st.1 * cCap else st.2 ≤ 1))
        (fun j st t ⟨hj_le, hd_eq, hcTbl_t, hacc_bound⟩ => ?_)
        ⟨le_rfl, Nat.zero_add _, hcTbl_h, by split_ifs <;> simp⟩
      let rpArgs : RadixProjArgs :=
        ⟨d.q, d.bagPtr, d.bagLen, d.m, d.v, st.1, 1, d.cBagPtr, d.cBagLen⟩
      have hidx_lt : (Memory.spec 0).clientResult t (radixProjProg rpArgs) < d.q ^ d.cBagLen :=
        radixProjProg_result_lt (args := rpArgs) hq_pos t
      have hfit_caddr :
          Fits w (d.cTblPtr + (Memory.spec 0).clientResult t (radixProjProg rpArgs)) :=
        hfit_cTbl.of_le (by omega)
      have hcVal_le :
          t.mem (d.cTblPtr + (Memory.spec 0).clientResult t (radixProjProg rpArgs)) ≤ cCap := by
        have hlt_len : (Memory.spec 0).clientResult t (radixProjProg rpArgs) < cTbl.length := by
          rwa [hcTbl_len]
        rw [hcTbl_t.get _ hlt_len]
        exact hcTbl_le _ (List.getElem_mem hlt_len)
      have hfit_d1 : Fits w (st.1 + 1) := hfit_dLim.of_le (by omega)
      have hrp_safe :
          0 < d.q ∧ Fits w 1 ∧ Fits w d.q ∧ Fits w d.m ∧
            Fits w (d.bagPtr + d.bagLen) ∧ Fits w (d.cBagPtr + d.cBagLen) ∧
            Fits w (d.q ^ d.cBagLen) :=
        ⟨hq_pos, h1, hfit_q, hfit_m, hfit_bag, hfit_cBag, hfit_cPow⟩
      obtain ⟨hst_ev, hres_ev⟩ := forgetInnerStep_eval d st.1 st.2 t
      refine ⟨?_, Nat.le_of_succ_le hj_le, ?_, ?_, ?_⟩
      · dsimp only [forgetInnerStep]
        rw [radixProjProg_state]
        refine ⟨⟨h1, hrp_safe⟩, hfit_caddr, h1, ?_⟩
        by_cases hm1 : d.mode = 1
        · simp only [hm1, ↓reduceIte] at hacc_bound ⊢
          have hsum_le :
              st.2 + t.mem (d.cTblPtr + (Memory.spec 0).clientResult t (radixProjProg rpArgs)) ≤
                d.dLim * cCap := by
            have hstep : (st.1 + 1) * cCap ≤ d.dLim * cCap :=
              Nat.mul_le_mul_right cCap (by omega)
            calc st.2 + t.mem (d.cTblPtr + (Memory.spec 0).clientResult t (radixProjProg rpArgs))
                ≤ st.1 * cCap + cCap := Nat.add_le_add hacc_bound hcVal_le
              _ = (st.1 + 1) * cCap := by ring
              _ ≤ d.dLim * cCap := hstep
          exact ⟨hfit_d1, (hfit_sumCap hm1).of_le hsum_le⟩
        · simp only [hm1, ↓reduceIte] at hacc_bound ⊢
          split_ifs
          · exact hfit_d1
          · exact ⟨hfit_d1, h1⟩
      · rw [hres_ev]; dsimp only; omega
      · rw [hst_ev]; exact hcTbl_t
      · rw [hres_ev]; dsimp only
        by_cases hm1 : d.mode = 1
        · simp only [hm1, ↓reduceIte] at hacc_bound ⊢
          change st.2 + t.mem (d.cTblPtr + (Memory.spec 0).clientResult t (radixProjProg rpArgs)) ≤
            (st.1 + 1) * cCap
          calc st.2 + t.mem (d.cTblPtr + (Memory.spec 0).clientResult t (radixProjProg rpArgs))
              ≤ st.1 * cCap + cCap := Nat.add_le_add hacc_bound hcVal_le
            _ = (st.1 + 1) * cCap := by ring
        · simp only [hm1, ↓reduceIte] at hacc_bound ⊢
          split_ifs <;> omega
    · simp only [iterationWork_zero]; exact le_rfl
  refine hraw.mono_mul 1 fun a s => ?_
  unfold forgetInnerProg
  rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
  have hquery : ∀ x m, 1 ≤ memoryCost (forgetInnerStep x) m := fun ⟨a', d', acc'⟩ m => by
    unfold forgetInnerStep; dsimp only
    rw [memoryCost_bind', radixProjProg_state, memoryCost_bind', memoryCost_read]
    omega
  have hw := iterationWork_zero_le forgetInnerStep hquery a a.dLim (0, 0) s
  rw [iterationWork_zero] at hw
  omega

private structure ForgetFillArgs where
  mode : ℕ
  q : ℕ
  v : ℕ
  bagPtr : ℕ
  bagLen : ℕ
  cBagPtr : ℕ
  cBagLen : ℕ
  cTblPtr : ℕ
  dLim : ℕ
  tblPtr : ℕ
  tblLen : ℕ

private def ForgetFillArgs.equiv :
    ForgetFillArgs ≃ (((((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a :=
    ((((((((((a.mode, a.q), a.v), a.bagPtr), a.bagLen), a.cBagPtr), a.cBagLen), a.cTblPtr),
      a.dLim), a.tblPtr), a.tblLen)
  invFun := fun ((((((((((md, q), v), bp), bl), cbp), cbl), ctp), dl), tp), tl) =>
    ⟨md, q, v, bp, bl, cbp, cbl, ctp, dl, tp, tl⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding ForgetFillArgs := .ofEquiv ForgetFillArgs.equiv

private def forgetOuterStep (p : ForgetFillArgs × ℕ) : Memory.Prog ℕ := do
  let a := p.1
  let m := p.2
  let val ← forgetInnerProg
    ⟨a.mode, a.q, a.v, a.bagPtr, a.bagLen, m, a.cBagPtr, a.cBagLen, a.cTblPtr, a.dLim⟩
  Memory.write (a.tblPtr + m) val
  pure (m + 1)

private def forgetFillProg (a : ForgetFillArgs) : Memory.Prog Unit := do
  let _ ← iterate forgetOuterStep a a.tblLen 0
  pure ()

private theorem forgetOuterStep_eval (a : ForgetFillArgs) (m : ℕ) (t : Memory.State) :
    let val := (Memory.spec 0).clientResult t
      (forgetInnerProg
        ⟨a.mode, a.q, a.v, a.bagPtr, a.bagLen, m, a.cBagPtr, a.cBagLen, a.cTblPtr, a.dLim⟩)
    (Memory.spec 0).clientState t (forgetOuterStep (a, m)) =
      ⟨Function.update t.mem (a.tblPtr + m) val, t.frontier⟩ ∧
    (Memory.spec 0).clientResult t (forgetOuterStep (a, m)) = m + 1 := by
  unfold forgetOuterStep
  dsimp only
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    forgetInnerProg_state,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind]
  exact ⟨rfl, rfl⟩

private theorem forgetFillProg_spec {w : ℕ} (counting : Bool) (a : ForgetFillArgs)
    (hq : 0 < a.q) (hmode : a.mode = if counting then 1 else 0)
    {child : NiceTree ℕ} {cs : List (ConstraintTable a.q)} {vars : List ℕ}
    {s : Memory.State}
    (hdLim : a.dLim = if a.v ∈ vars then a.q else 1)
    (hLB : HoldsIn a.bagPtr ((bagList child).erase a.v) s)
    (hLB_len : ((bagList child).erase a.v).length = a.bagLen)
    (hLB_hi : a.bagPtr + a.bagLen ≤ a.tblPtr)
    (hcBag : HoldsIn a.cBagPtr (bagList child) s)
    (hcBag_len : (bagList child).length = a.cBagLen)
    (hcBag_hi : a.cBagPtr + a.cBagLen ≤ a.tblPtr)
    (hcTbl : HoldsIn a.cTblPtr (dpInstTree counting a.q cs vars child) s)
    (hcTbl_hi : a.cTblPtr + a.q ^ a.cBagLen ≤ a.tblPtr)
    (htblLen : a.tblLen = a.q ^ a.bagLen)
    (htbl_hi : a.tblPtr + a.tblLen ≤ s.frontier)
    (hfit_cap : Fits w (if counting then a.q ^ (NiceTree.forget a.v child).size else 1)) :
    let targetTbl := dpInstTree counting a.q cs vars (.forget a.v child)
    let s₁ := (Memory.spec 0).clientState s (forgetFillProg a)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (forgetFillProg a)) ∧
    s₁.frontier = s.frontier ∧
    PreservesBelow a.tblPtr s s₁ ∧
    HoldsIn a.tblPtr targetTbl s₁ ∧
    memoryCost (forgetFillProg a) s ≤
      a.tblLen * (a.dLim * (a.cBagLen * (a.bagLen + 1) + 1) + 1) := by
  let targetTbl := dpInstTree counting a.q cs vars (.forget a.v child)
  have htarget_len : targetTbl.length = a.tblLen := by
    simp [targetTbl, bagList, hLB_len, htblLen]
  let stepCost := a.dLim * (a.cBagLen * (a.bagLen + 1) + 1) + 1
  refine tableFillProg_spec forgetOuterStep a a.tblPtr a.tblLen stepCost targetTbl s
    (fun _ => True) trivial htarget_len htbl_hi fun k t hk_le _ hfr_t hp_t _ => ?_
  let m := a.tblLen - (k + 1)
  have hm_lt : m < a.tblLen := by omega
  have hLB_t : HoldsIn a.bagPtr ((bagList child).erase a.v) t :=
    hLB.mono (F := a.tblPtr) (by rw [hLB_len]; exact hLB_hi) hp_t
  have hcBag_t : HoldsIn a.cBagPtr (bagList child) t :=
    hcBag.mono (F := a.tblPtr) (by rw [hcBag_len]; exact hcBag_hi) hp_t
  have hcTbl_t : HoldsIn a.cTblPtr (dpInstTree counting a.q cs vars child) t :=
    hcTbl.mono (F := a.tblPtr) (by rw [length_dpInstTree, hcBag_len]; exact hcTbl_hi) hp_t
  obtain ⟨hv_in, hst_in, hr_in, hc_in⟩ :=
    forgetInnerProg_spec (w := w) counting
      ⟨a.mode, a.q, a.v, a.bagPtr, a.bagLen, m, a.cBagPtr, a.cBagLen, a.cTblPtr, a.dLim⟩
      hq hmode hLB_t hLB_len hcBag_t hcBag_len hcTbl_t
      (by rw [length_dpInstTree, hcBag_len])
  dsimp only at hr_in hc_in
  let entryVal := targetTbl[m]'(by rw [htarget_len]; exact hm_lt)
  have hval_eq :
      (Memory.spec 0).clientResult t
        (forgetInnerProg
          ⟨a.mode, a.q, a.v, a.bagPtr, a.bagLen, m, a.cBagPtr, a.cBagLen, a.cTblPtr, a.dLim⟩) =
        entryVal := by
    rw [hr_in]
    simp only [entryVal, targetTbl, dpInstTree, List.getElem_ofFn, hdLim]
    by_cases hv : a.v ∈ vars
    · simp [hv]
    · simp only [hv, ↓reduceIte, dpAlgFold]
      cases counting
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hle1 :
            (dpInstTree false a.q cs vars child).getD
              (toRadix a.q (bagList child)
                (Function.update (ofRadix a.q ((bagList child).erase a.v) m) a.v 0)) 0 ≤ 1 := by
          rw [List.getD_eq_getElem?_getD]
          cases hg : (dpInstTree false a.q cs vars child)[toRadix a.q (bagList child)
              (Function.update (ofRadix a.q ((bagList child).erase a.v) m) a.v 0)]? with
          | none => exact Nat.zero_le _
          | some y =>
            simpa using mem_dpInstTree_le false hq cs vars child y (List.mem_of_getElem? hg)
        split_ifs <;> omega
      · simp
  have hentry_fit : Fits w entryVal := by
    have hmem_e : entryVal ∈ targetTbl := List.getElem_mem _
    exact hfit_cap.of_le (mem_dpInstTree_le counting hq cs vars (.forget a.v child) _ hmem_e)
  have hdst_lt : a.tblPtr + m < t.frontier := by rw [hfr_t]; omega
  obtain ⟨hst_ev, hres_ev⟩ := forgetOuterStep_eval a m t
  have hst_t₁ : (Memory.spec 0).clientState t (forgetOuterStep (a, m)) =
      ⟨Function.update t.mem (a.tblPtr + m) entryVal, t.frontier⟩ := by
    rw [hst_ev, hval_eq]
  have hv_step : (Memory.spec w).ValidHistory t
      ((Memory.spec w).clientHistory t (forgetOuterStep (a, m))) := by
    unfold forgetOuterStep
    dsimp only
    refine validHistory_bind_step hv_in ?_
    rw [hst_in, hval_eq]
    exact validHistory_write_bind hdst_lt hentry_fit (validHistory_pure w _ _)
  have hc_step : memoryCost (forgetOuterStep (a, m)) t ≤ stepCost := by
    unfold forgetOuterStep
    dsimp only
    rw [memoryCost_bind', hst_in, memoryCost_bind', memoryCost_write, memoryCost_pure]
    dsimp only [stepCost]
    omega
  exact ⟨hv_step, hst_t₁, hres_ev, trivial, hc_step⟩

private theorem forgetFillProg_realizes :
    Realizes .exact forgetFillProg WordEncoding.encode WordEncoding.encode
      (fun w a s =>
        0 < a.q ∧ Fits w 1 ∧ Fits w a.q ∧ Fits w a.dLim ∧
        Fits w (a.bagPtr + a.bagLen) ∧
        Fits w (a.cBagPtr + a.cBagLen) ∧
        Fits w (a.q ^ a.cBagLen) ∧
        Fits w (a.cTblPtr + a.q ^ a.cBagLen) ∧
        Fits w (a.tblPtr + a.tblLen) ∧
        ∃ (cTbl : List ℕ) (cCap : ℕ),
          a.cTblPtr + a.q ^ a.cBagLen ≤ a.tblPtr ∧
          HoldsIn a.cTblPtr cTbl s ∧
          cTbl.length = a.q ^ a.cBagLen ∧
          (∀ x ∈ cTbl, x ≤ cCap) ∧
          (a.mode = 1 → Fits w (a.dLim * cCap)))
      (fun _ _ => 0) := by
  have hraw :
      Realizes .exact forgetFillProg WordEncoding.encode WordEncoding.encode
        (fun w a s =>
          0 < a.q ∧ Fits w 1 ∧ Fits w a.q ∧ Fits w a.dLim ∧
          Fits w (a.bagPtr + a.bagLen) ∧
          Fits w (a.cBagPtr + a.cBagLen) ∧
          Fits w (a.q ^ a.cBagLen) ∧
          Fits w (a.cTblPtr + a.q ^ a.cBagLen) ∧
          Fits w (a.tblPtr + a.tblLen) ∧
          ∃ (cTbl : List ℕ) (cCap : ℕ),
            a.cTblPtr + a.q ^ a.cBagLen ≤ a.tblPtr ∧
            HoldsIn a.cTblPtr cTbl s ∧
            cTbl.length = a.q ^ a.cBagLen ∧
            (∀ x ∈ cTbl, x ≤ cCap) ∧
            (a.mode = 1 → Fits w (a.dLim * cCap)))
        (fun a _ => a.tblLen) := by
    unfold forgetFillProg
    realize [forgetInnerProg_realizes]
    · obtain ⟨hq_pos, h1, hfit_q, hfit_dLim, hfit_bag, hfit_cBag, hfit_cPow, hfit_cTbl, hfit_tbl,
        cTbl, cCap, hcTbl_hi, hcTbl_h, hcTbl_len, hcTbl_le, hfit_sumCap⟩ := h
      refine iterationSafe_of_stepInv _ _ w _
        (fun (j : ℕ) (m : ℕ) (t : Memory.State) =>
          j ≤ d.tblLen ∧ m + j = d.tblLen ∧
          HoldsIn d.cTblPtr cTbl t)
        (fun j m t ⟨hj_le, hm_eq, hcTbl_t⟩ => ?_)
        ⟨le_rfl, Nat.zero_add _, hcTbl_h⟩
      have hfit_m : Fits w m := hfit_tbl.of_le (by omega)
      have hfit_m1 : Fits w (m + 1) := hfit_tbl.of_le (by omega)
      have hfit_taddr : Fits w (d.tblPtr + m) := hfit_tbl.of_le (by omega)
      have hin_safe :
          0 < d.q ∧ Fits w 1 ∧ Fits w d.q ∧ Fits w m ∧ Fits w d.dLim ∧
            Fits w (d.bagPtr + d.bagLen) ∧ Fits w (d.cBagPtr + d.cBagLen) ∧
            Fits w (d.q ^ d.cBagLen) ∧ Fits w (d.cTblPtr + d.q ^ d.cBagLen) ∧
            ∃ (cTbl : List ℕ) (cCap : ℕ),
              HoldsIn d.cTblPtr cTbl t ∧
              cTbl.length = d.q ^ d.cBagLen ∧
              (∀ x ∈ cTbl, x ≤ cCap) ∧
              (d.mode = 1 → Fits w (d.dLim * cCap)) :=
        ⟨hq_pos, h1, hfit_q, hfit_m, hfit_dLim, hfit_bag, hfit_cBag, hfit_cPow, hfit_cTbl,
          cTbl, cCap, hcTbl_t, hcTbl_len, hcTbl_le, hfit_sumCap⟩
      obtain ⟨hst_ev, hres_ev⟩ := forgetOuterStep_eval d m t
      refine ⟨?_, Nat.le_of_succ_le hj_le, ?_, ?_⟩
      · dsimp only [forgetOuterStep]
        exact ⟨hin_safe, hfit_taddr, hfit_m1⟩
      · rw [hres_ev]; omega
      · rw [hst_ev]
        exact holdsIn_write_outside hcTbl_t (.inr (by rw [hcTbl_len]; omega))
    · simp only [iterationWork_zero]; exact le_rfl
  refine hraw.mono_mul 1 fun a s => ?_
  unfold forgetFillProg
  rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
  have hquery : ∀ x m, 1 ≤ memoryCost (forgetOuterStep x) m := fun ⟨a', m'⟩ st => by
    unfold forgetOuterStep; dsimp only
    rw [memoryCost_bind', forgetInnerProg_state, memoryCost_bind', memoryCost_write]
    omega
  have hw := iterationWork_zero_le forgetOuterStep hquery a a.tblLen 0 s
  rw [iterationWork_zero] at hw
  omega

private structure ForgetNodeArgs where
  mode : ℕ
  q : ℕ
  v : ℕ
  varsPtr : ℕ
  varsLen : ℕ
  dChild : ℕ
  dCur : ℕ

private def ForgetNodeArgs.equiv :
    ForgetNodeArgs ≃ (((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a := ((((((a.mode, a.q), a.v), a.varsPtr), a.varsLen), a.dChild), a.dCur)
  invFun := fun ((((((md, q), v), vp), vl), dch), dc) => ⟨md, q, v, vp, vl, dch, dc⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding ForgetNodeArgs := .ofEquiv ForgetNodeArgs.equiv

private theorem ite_pure_do {α β : Type} (c : Prop) [Decidable c] (x y : α)
    (k : α → Memory.Prog β) :
    (if c then (pure x >>= k) else (pure y >>= k)) = k (if c then x else y) := by
  split_ifs <;> simp

private def forgetNodeProg (a : ForgetNodeArgs) : Memory.Prog Unit := do
  let cBagPtr ← Memory.read a.dChild
  let cBagLen ← Memory.read (a.dChild + 1)
  let cTblPtr ← Memory.read (a.dChild + 2)
  let p ← eraseBagProg ⟨a.v, cBagPtr, cBagLen⟩
  let bagPtr := p.1
  let bagLen := p.2
  let tblLen ← powProg ⟨a.q, bagLen⟩
  let tblPtr ← Memory.allocDirty tblLen
  let inVars ← bagMemProg ⟨a.v, a.varsPtr, a.varsLen⟩
  let dLim ← if inVars = 1 then pure a.q else pure 1
  let _ ← forgetFillProg
    ⟨a.mode, a.q, a.v, bagPtr, bagLen, cBagPtr, cBagLen, cTblPtr, dLim, tblPtr, tblLen⟩
  writeDescProg ⟨a.dCur, bagPtr, bagLen, tblPtr, tblLen⟩

private theorem forgetNodeProg_spec {w F_lo : ℕ} (counting : Bool) (a : ForgetNodeArgs)
    (hq : 0 < a.q) (hmode : a.mode = if counting then 1 else 0)
    {child : NiceTree ℕ} {cs : List (ConstraintTable a.q)} {vars : List ℕ}
    {s : Memory.State}
    (hvars : HoldsIn a.varsPtr vars s)
    (hvars_len : vars.length = a.varsLen)
    (hfit_bag_elems : ∀ u ∈ bagList child, Fits w u)
    (hchild : NodeDescAt F_lo counting a.q cs vars child a.dChild s)
    (hdCur : a.dCur + 4 ≤ F_lo)
    (hFlo : F_lo ≤ s.frontier)
    (hfit_peak : Fits w (s.frontier +
      max (bagList child).length
        (((bagList child).erase a.v).length + a.q ^ ((bagList child).erase a.v).length)))
    (hfit_cap : Fits w (if counting then a.q ^ (NiceTree.forget a.v child).size else 1)) :
    let LB := (bagList child).erase a.v
    let sEnd := (Memory.spec 0).clientState s (forgetNodeProg a)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (forgetNodeProg a)) ∧
    sEnd.frontier ≤ s.frontier + (LB.length + a.q ^ LB.length) ∧
    FrameOutsideRange a.dCur (a.dCur + 4) s sEnd ∧
    NodeDescAt F_lo counting a.q cs vars (.forget a.v child) a.dCur sEnd ∧
    memoryCost (forgetNodeProg a) s ≤
      14 + 3 * (bagList child).length + LB.length + a.varsLen +
        a.q ^ LB.length *
          (a.q * ((bagList child).length * (LB.length + 1) + 1) + 1) := by
  have hd_ch := hchild.desc_hi
  have hm_cbLen : s.mem (a.dChild + 1) = (bagList child).length := hchild.bag_len
  let cBagPtr := s.mem a.dChild
  let cBagLen := (bagList child).length
  let cTblPtr := s.mem (a.dChild + 2)
  let LB := (bagList child).erase a.v
  let bagPtr := s.frontier
  let bagLen := LB.length
  obtain ⟨hv_er, hr_er, hfr_er, hp_er, hLB_s₁, hc_er⟩ :=
    eraseBagProg_spec (w := w) ⟨a.v, cBagPtr, cBagLen⟩ hchild.bag_holds rfl hfit_bag_elems
      (hfit_peak.of_le (by dsimp only [LB]; omega))
  dsimp only at hr_er hfr_er hc_er
  let s₁ := (Memory.spec 0).clientState s (eraseBagProg ⟨a.v, cBagPtr, cBagLen⟩)
  have hs₁_fr_pos : 0 < s₁.frontier := by rw [hfr_er]; have := hchild.desc_hi; omega
  obtain ⟨hv_pw, hst_pw, hr_pw, hc_pw⟩ := powProg_spec (w := w) ⟨a.q, bagLen⟩ hs₁_fr_pos
  dsimp only at hr_pw hc_pw
  let tblLen := a.q ^ bagLen
  let tblPtr := s₁.frontier
  let s₂ := (Memory.spec 0).clientState s₁ (Memory.allocDirty tblLen)
  have hs₂_fr : s₂.frontier = tblPtr + tblLen := rfl
  have hp₂ : PreservesBelow tblPtr s₁ s₂ := preservesBelow_allocDirty s₁ tblLen
  have hfit_fr₂ : Fits w (s₁.frontier + tblLen) := by
    rw [hfr_er]; exact hfit_peak.of_le (by dsimp only [LB, tblLen, bagLen]; omega)
  have hv₂ : (Memory.spec w).ValidHistory s₁
      ((Memory.spec w).clientHistory s₁ (Memory.allocDirty tblLen)) :=
    validHistory_allocDirty hfit_fr₂
  have hp_s_s₂ : PreservesBelow bagPtr s s₂ :=
    hp_er.trans (hp₂.mono_bound (by dsimp only [tblPtr, bagPtr]; rw [hfr_er]; omega))
  obtain ⟨hv_bm, hst_bm, hr_bm, hc_bm⟩ :=
    bagMemProg_spec (w := w) ⟨a.v, a.varsPtr, a.varsLen⟩ (hvars.mono_frontier hp_s_s₂) hvars_len
  dsimp only at hr_bm hc_bm
  let dLim := if (if memBag a.v vars then 1 else 0) = 1 then a.q else 1
  have hdLim_eq : dLim = if a.v ∈ vars then a.q else 1 := by
    dsimp only [dLim]; rw [memBag_eq_decide]
    by_cases hv : a.v ∈ vars <;> simp [hv]
  have hdLim_le : dLim ≤ a.q := by
    rw [hdLim_eq]; split_ifs <;> omega
  let fillArgs : ForgetFillArgs :=
    ⟨a.mode, a.q, a.v, bagPtr, bagLen, cBagPtr, cBagLen, cTblPtr, dLim, tblPtr, tblLen⟩
  obtain ⟨hv_fill, hfr_fill, hp_fill, htbl_fill, hc_fill⟩ :=
    forgetFillProg_spec (w := w) counting fillArgs hq hmode hdLim_eq
      (hLB_s₁.mono_frontier hp₂) rfl
      (by dsimp only [fillArgs, tblPtr, bagPtr, bagLen, LB]; rw [hfr_er])
      (hchild.bag_holds.mono_frontier hp_s_s₂) rfl
      (by have := hchild.bag_holds.1
          dsimp only [fillArgs, cBagPtr, cBagLen, tblPtr]; rw [hfr_er]; omega)
      (hchild.tbl_holds.mono_frontier hp_s_s₂)
      (by have := hchild.tbl_holds.1; rw [length_dpInstTree] at this
          dsimp only [fillArgs, cTblPtr, cBagLen, tblPtr]; rw [hfr_er]; omega)
      rfl (by rw [hs₂_fr]) hfit_cap
  let s₃ := (Memory.spec 0).clientState s₂ (forgetFillProg fillArgs)
  have hs₃_fr : s₃.frontier = tblPtr + tblLen := by rw [hfr_fill, hs₂_fr]
  have hp_s_s₃ : PreservesBelow bagPtr s s₃ :=
    hp_s_s₂.trans
      (hp_fill.mono_bound (by dsimp only [fillArgs, tblPtr, bagPtr]; rw [hfr_er]; omega))
  have hLB_s₃ : HoldsIn bagPtr LB s₃ :=
    (hLB_s₁.mono_frontier hp₂).mono (F := tblPtr)
      (by dsimp only [tblPtr, bagPtr, LB]; rw [hfr_er]) hp_fill
  have hd_s₃ : a.dCur + 4 ≤ s₃.frontier := by
    rw [hs₃_fr]; dsimp only [tblPtr]; rw [hfr_er]; omega
  have hfit_bt : Fits w (s.frontier + bagLen + tblLen) := by rwa [hfr_er] at hfit_fr₂
  obtain ⟨hv_wd, hfr_wd, hframe_wd, hm0, hm1, hm2, hm3, hc_wd⟩ :=
    writeDescProg_spec (w := w) ⟨a.dCur, bagPtr, bagLen, tblPtr, tblLen⟩ hd_s₃
      (hfit_bt.of_le (by dsimp only [bagPtr, bagLen, tblLen]; omega))
      (hfit_bt.of_le (by dsimp only [bagPtr, bagLen, tblLen]; omega))
      (hfit_bt.of_le (by
        dsimp only [tblPtr, bagLen, tblLen] at hfit_bt ⊢
        rw [hfr_er]; dsimp only [bagLen, LB]; omega))
      (hfit_bt.of_le (by dsimp only [bagPtr, bagLen, tblLen]; omega))
  dsimp only at hm0 hm1 hm2 hm3
  let sEnd := (Memory.spec 0).clientState s₃
    (writeDescProg ⟨a.dCur, bagPtr, bagLen, tblPtr, tblLen⟩)
  have hr_s (x : ℕ) : (Memory.spec 0).clientState s (Memory.read x) = s := rfl
  have hr_r (x : ℕ) : (Memory.spec 0).clientResult s (Memory.read x) = s.mem x := rfl
  have ha2_s : (Memory.spec 0).clientState s₁ (Memory.allocDirty tblLen) = s₂ := rfl
  have ha2_r : (Memory.spec 0).clientResult s₁ (Memory.allocDirty tblLen) = tblPtr := rfl
  have hsEnd_eq : (Memory.spec 0).clientState s (forgetNodeProg a) = sEnd := by
    unfold forgetNodeProg
    dsimp only
    iterate 3 rw [StateTransitionSpec.clientState_bind, hr_s, hr_r]
    rw [hm_cbLen, StateTransitionSpec.clientState_bind]
    change (Memory.spec 0).clientState s₁
      (powProg ⟨a.q, ((Memory.spec 0).clientResult s (eraseBagProg ⟨a.v, cBagPtr, cBagLen⟩)).2⟩ >>=
        _) = sEnd
    rw [hr_er]
    dsimp only
    rw [StateTransitionSpec.clientState_bind, hst_pw, hr_pw,
      StateTransitionSpec.clientState_bind, ha2_s, ha2_r,
      StateTransitionSpec.clientState_bind, hst_bm, hr_bm,
      ite_pure_do, StateTransitionSpec.clientState_bind]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold forgetNodeProg
    dsimp only
    refine validHistory_read_bind (by omega) ?_
    refine validHistory_read_bind (by omega) ?_
    refine validHistory_read_bind (by omega) ?_
    rw [hm_cbLen]
    refine validHistory_bind_step hv_er ?_
    change (Memory.spec w).ValidHistory s₁ _
    rw [hr_er]
    dsimp only
    refine validHistory_bind_step hv_pw ?_
    rw [hst_pw, hr_pw]
    refine validHistory_bind_step hv₂ ?_
    rw [ha2_s, ha2_r]
    refine validHistory_bind_step hv_bm ?_
    rw [hst_bm, hr_bm, ite_pure_do]
    exact validHistory_bind_step hv_fill hv_wd
  · rw [hsEnd_eq, hfr_wd, hs₃_fr]
    dsimp only [tblPtr, tblLen, bagLen, LB]
    rw [hfr_er]
    omega
  · rw [hsEnd_eq]
    exact (FrameOutsideRange.of_preservesBelow a.dCur (a.dCur + 4) hp_s_s₃).trans hframe_wd
  · rw [hsEnd_eq]
    refine ⟨hdCur, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hm0]; exact hFlo
    · rw [hm1]; rfl
    · rw [hm0]
      exact hLB_s₃.frame_outsideRange (.inr (le_trans hdCur hFlo)) hframe_wd
    · rw [hm2]; dsimp only [tblPtr]; rw [hfr_er]; omega
    · rw [hm3]; rfl
    · rw [hm2]
      exact htbl_fill.frame_outsideRange
        (.inr (by dsimp only [fillArgs, tblPtr]; rw [hfr_er]; omega)) hframe_wd
  · unfold forgetNodeProg
    dsimp only
    iterate 3 rw [memoryCost_bind', memoryCost_read, hr_s, hr_r]
    rw [hm_cbLen, memoryCost_bind']
    change 1 + (1 + (1 + (memoryCost (eraseBagProg ⟨a.v, cBagPtr, cBagLen⟩) s +
      memoryCost (powProg ⟨a.q, ((Memory.spec 0).clientResult s
        (eraseBagProg ⟨a.v, cBagPtr, cBagLen⟩)).2⟩ >>= _) s₁))) ≤ _
    rw [hr_er]
    dsimp only
    rw [memoryCost_bind', hst_pw, hr_pw, memoryCost_bind', memoryCost_allocDirty, ha2_s, ha2_r,
      memoryCost_bind', hst_bm, hr_bm, ite_pure_do, memoryCost_bind']
    have hmul_dLim :
        tblLen * (dLim * (cBagLen * (bagLen + 1) + 1) + 1) ≤
          tblLen * (a.q * (cBagLen * (bagLen + 1) + 1) + 1) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_right _ hdLim_le) 1)
    dsimp only [fillArgs] at hc_fill
    have hc_fill' := hc_fill.trans hmul_dLim
    dsimp only [s₃, fillArgs, cBagPtr, cBagLen, cTblPtr, bagPtr, bagLen, tblPtr, tblLen, dLim, LB]
      at hc_er hc_pw hc_bm hc_fill hc_fill' hc_wd ⊢
    omega

private theorem forgetNodeProg_realizes :
    Realizes .exact forgetNodeProg WordEncoding.encode WordEncoding.encode
      (fun w a s =>
        0 < a.q ∧ Fits w 3 ∧ Fits w a.q ∧
        Fits w (a.varsPtr + a.varsLen) ∧
        Fits w (a.dChild + 3) ∧ Fits w (a.dCur + 3) ∧
        ∃ (F_lo : ℕ) (counting : Bool) (child : NiceTree ℕ)
          (cs : List (ConstraintTable a.q)) (vars : List ℕ),
          a.mode = (if counting then 1 else 0) ∧
          (∀ u ∈ bagList child, Fits w u) ∧
          NodeDescAt F_lo counting a.q cs vars child a.dChild s ∧
          F_lo ≤ s.frontier ∧
          Fits w (a.q ^ (bagList child).length) ∧
          Fits w (s.frontier +
            max (bagList child).length
              (((bagList child).erase a.v).length + a.q ^ ((bagList child).erase a.v).length)) ∧
          Fits w (if counting then a.q ^ (NiceTree.forget a.v child).size else 1))
      (fun _ _ => 0) := by
  unfold forgetNodeProg
  realize [eraseBagProg_realizes, powProg_realizes, bagMemProg_realizes,
    forgetFillProg_realizes, writeDescProg_realizes]
  all_goals
    obtain ⟨hq, h3, hfit_q, hfit_vars, hdCh, hdCur, F_lo, counting, child, cs, vars, hmode,
      hfit_elems, hch, hFlo, hfit_cPow, hfit_peak, hfit_cap⟩ := h
    have h1 : Fits w 1 := h3.of_le (by decide)
    try rw [hch.bag_len]
    obtain ⟨_, hr_er, hfr_er, hp_er, _, _⟩ :=
      eraseBagProg_spec (w := w) ⟨d.v, s.mem d.dChild, (bagList child).length⟩
        hch.bag_holds rfl hfit_elems (hfit_peak.of_le (by dsimp only; omega))
    dsimp only at hr_er hfr_er
    let s₁ :=
      (Memory.spec 0).clientState s (eraseBagProg ⟨d.v, s.mem d.dChild, (bagList child).length⟩)
    try rw [hr_er]; dsimp only
    try rw [powProg_state]
    try rw [powProg_result]; dsimp only
    let bagLen := ((bagList child).erase d.v).length
    let tblLen := d.q ^ bagLen
    let s₂ := (Memory.spec 0).clientState s₁ (Memory.allocDirty tblLen)
    have hp₂ : PreservesBelow s₁.frontier s₁ s₂ := preservesBelow_allocDirty s₁ tblLen
    try rw [bagMemProg_state]
    have hp_all : PreservesBelow s.frontier s s₂ :=
      hp_er.trans (hp₂.mono_bound (by rw [hfr_er]; omega))
    have hc_bag := hch.bag_holds.1
    have hc_tbl := hch.tbl_holds.1
    rw [length_dpInstTree] at hc_tbl
    let cCap := if counting then d.q ^ child.size else 1
    have hf_ch1 : Fits w (d.dChild + 1) := hdCh.of_le (by omega)
    have hf_ch2 : Fits w (d.dChild + 2) := hdCh.of_le (by omega)
    have hex_er : ∃ xs : List ℕ,
        HoldsIn (s.mem d.dChild) xs s ∧
        xs.length = (bagList child).length ∧
        s.mem d.dChild + (bagList child).length ≤ s.frontier ∧
        (∀ u ∈ xs, Fits w u) ∧
        Fits w (s.frontier + (bagList child).length) :=
      ⟨bagList child, hch.bag_holds, rfl, hc_bag, hfit_elems, hfit_peak.of_le (by omega)⟩
    have hf_bagEnd : Fits w (s.frontier + bagLen) :=
      hfit_peak.of_le (by dsimp only [bagLen]; omega)
    have hf_cbagEnd : Fits w (s.mem d.dChild + (bagList child).length) :=
      hfit_peak.of_le (by omega)
    have hf_ctblEnd : Fits w (s.mem (d.dChild + 2) + d.q ^ (bagList child).length) :=
      hfit_peak.of_le (by omega)
    have hf_tblLen : Fits w tblLen :=
      hfit_peak.of_le (by dsimp only [tblLen, bagLen]; omega)
    have hf_tblEnd : Fits w (s₁.frontier + tblLen) :=
      hfit_peak.of_le (by rw [hfr_er]; dsimp only [bagLen, tblLen]; omega)
    have hex_fill (dLim : ℕ) (hdLim_le : dLim ≤ d.q) :
        ∃ (cTbl : List ℕ) (cCap' : ℕ),
          s.mem (d.dChild + 2) + d.q ^ (bagList child).length ≤ s₁.frontier ∧
          HoldsIn (s.mem (d.dChild + 2)) cTbl s₂ ∧
          cTbl.length = d.q ^ (bagList child).length ∧
          (∀ x ∈ cTbl, x ≤ cCap') ∧
          (d.mode = 1 → Fits w (dLim * cCap')) := by
      refine ⟨dpInstTree counting d.q cs vars child, cCap,
        by rw [hfr_er]; omega,
        hch.tbl_holds.mono_frontier hp_all,
        length_dpInstTree _ _ _ _ _,
        mem_dpInstTree_le counting hq cs vars child,
        fun hm1 => ?_⟩
      rw [hmode] at hm1
      cases counting
      · simp at hm1
      · simp only [↓reduceIte, NiceTree.size_forget, Nat.pow_succ, Nat.mul_comm] at hfit_cap
        dsimp only [cCap]
        exact hfit_cap.of_le (Nat.mul_le_mul_right _ hdLim_le)
    have hex_fill_q := hex_fill d.q le_rfl
    have hex_fill_1 := hex_fill 1 (by omega)
    repeat (
      first
      | exact hex_er
      | exact hex_fill_q
      | exact hex_fill_1
      | exact hq
      | exact h1
      | exact hfit_q
      | exact hfit_vars
      | exact hdCur
      | exact hf_ch1
      | exact hf_ch2
      | exact hfit_cPow
      | exact hf_bagEnd
      | exact hf_cbagEnd
      | exact hf_ctblEnd
      | exact hf_tblLen
      | exact hf_tblEnd)

/-! #### 4. Join node handler (`joinFillProg`, `joinNodeProg`) -/

private structure JoinFillArgs where
  q : ℕ
  lBagPtr : ℕ
  lBagLen : ℕ
  lTblPtr : ℕ
  rBagPtr : ℕ
  rBagLen : ℕ
  rTblPtr : ℕ
  tblPtr : ℕ
  tblLen : ℕ

private def JoinFillArgs.equiv :
    JoinFillArgs ≃ (((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a :=
    ((((((((a.q, a.lBagPtr), a.lBagLen), a.lTblPtr), a.rBagPtr), a.rBagLen), a.rTblPtr),
      a.tblPtr), a.tblLen)
  invFun := fun ((((((((q, lbp), lbl), ltp), rbp), rbl), rtp), tp), tl) =>
    ⟨q, lbp, lbl, ltp, rbp, rbl, rtp, tp, tl⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding JoinFillArgs := .ofEquiv JoinFillArgs.equiv

private def joinFillStep (p : JoinFillArgs × ℕ) : Memory.Prog ℕ := do
  let a := p.1
  let m := p.2
  let lv ← Memory.read (a.lTblPtr + m)
  let mr ← radixProjProg ⟨a.q, a.lBagPtr, a.lBagLen, m, 0, 0, 0, a.rBagPtr, a.rBagLen⟩
  let rv ← Memory.read (a.rTblPtr + mr)
  Memory.write (a.tblPtr + m) (lv * rv)
  pure (m + 1)

private def joinFillProg (a : JoinFillArgs) : Memory.Prog Unit := do
  let _ ← iterate joinFillStep a a.tblLen 0
  pure ()

private theorem joinFillStep_eval (a : JoinFillArgs) (m : ℕ) (t : Memory.State) :
    let mr := (Memory.spec 0).clientResult t
      (radixProjProg ⟨a.q, a.lBagPtr, a.lBagLen, m, 0, 0, 0, a.rBagPtr, a.rBagLen⟩)
    let lv := t.mem (a.lTblPtr + m)
    let rv := t.mem (a.rTblPtr + mr)
    (Memory.spec 0).clientState t (joinFillStep (a, m)) =
      ⟨Function.update t.mem (a.tblPtr + m) (lv * rv), t.frontier⟩ ∧
    (Memory.spec 0).clientResult t (joinFillStep (a, m)) = m + 1 := by
  have hr_st (x : ℕ) : (Memory.spec 0).clientState t (Memory.read x) = t := rfl
  have hr_res (x : ℕ) : (Memory.spec 0).clientResult t (Memory.read x) = t.mem x := rfl
  unfold joinFillStep
  dsimp only
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_st, hr_res,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    radixProjProg_state,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_st, hr_res,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind]
  exact ⟨rfl, rfl⟩

private theorem joinFillProg_spec {w : ℕ} (counting : Bool) (a : JoinFillArgs)
    (hq : 0 < a.q) {left right : NiceTree ℕ} {cs : List (ConstraintTable a.q)} {vars : List ℕ}
    {s : Memory.State}
    (hlBag : HoldsIn a.lBagPtr (bagList left) s)
    (hlBag_len : (bagList left).length = a.lBagLen)
    (hlBag_hi : a.lBagPtr + a.lBagLen ≤ a.tblPtr)
    (hlTbl : HoldsIn a.lTblPtr (dpInstTree counting a.q cs vars left) s)
    (hlTbl_hi : a.lTblPtr + a.tblLen ≤ a.tblPtr)
    (hrBag : HoldsIn a.rBagPtr (bagList right) s)
    (hrBag_len : (bagList right).length = a.rBagLen)
    (hrBag_hi : a.rBagPtr + a.rBagLen ≤ a.tblPtr)
    (hrTbl : HoldsIn a.rTblPtr (dpInstTree counting a.q cs vars right) s)
    (hrTbl_hi : a.rTblPtr + a.q ^ a.rBagLen ≤ a.tblPtr)
    (htblLen : a.tblLen = a.q ^ a.lBagLen)
    (htbl_hi : a.tblPtr + a.tblLen ≤ s.frontier)
    (hfit_cap : Fits w (if counting then a.q ^ (NiceTree.join left right).size else 1)) :
    let targetTbl := dpInstTree counting a.q cs vars (.join left right)
    let s₁ := (Memory.spec 0).clientState s (joinFillProg a)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (joinFillProg a)) ∧
    s₁.frontier = s.frontier ∧
    PreservesBelow a.tblPtr s s₁ ∧
    HoldsIn a.tblPtr targetTbl s₁ ∧
    memoryCost (joinFillProg a) s ≤
      a.tblLen * (a.rBagLen * (a.lBagLen + 1) + 3) := by
  let targetTbl := dpInstTree counting a.q cs vars (.join left right)
  have htarget_len : targetTbl.length = a.tblLen := by
    simp [targetTbl, bagList, hlBag_len, htblLen]
  let stepCost := a.rBagLen * (a.lBagLen + 1) + 3
  refine tableFillProg_spec joinFillStep a a.tblPtr a.tblLen stepCost targetTbl s
    (fun _ => True) trivial htarget_len htbl_hi fun k t hk_le _ hfr_t hp_t _ => ?_
  let m := a.tblLen - (k + 1)
  have hm_lt : m < a.tblLen := by omega
  have hlBag_t : HoldsIn a.lBagPtr (bagList left) t :=
    hlBag.mono (F := a.tblPtr) (by rw [hlBag_len]; exact hlBag_hi) hp_t
  have hrBag_t : HoldsIn a.rBagPtr (bagList right) t :=
    hrBag.mono (F := a.tblPtr) (by rw [hrBag_len]; exact hrBag_hi) hp_t
  have hlTbl_t : HoldsIn a.lTblPtr (dpInstTree counting a.q cs vars left) t :=
    hlTbl.mono (F := a.tblPtr) (by rw [length_dpInstTree, hlBag_len, ← htblLen]; exact hlTbl_hi)
      hp_t
  have hrTbl_t : HoldsIn a.rTblPtr (dpInstTree counting a.q cs vars right) t :=
    hrTbl.mono (F := a.tblPtr) (by rw [length_dpInstTree, hrBag_len]; exact hrTbl_hi) hp_t
  obtain ⟨hv_rp, hst_rp, hr_rp, hc_rp⟩ :=
    radixProjProg_spec (w := w)
      ⟨a.q, a.lBagPtr, a.lBagLen, m, 0, 0, 0, a.rBagPtr, a.rBagLen⟩
      hlBag_t hlBag_len hrBag_t hrBag_len
  simp only [radixProjAssign, Nat.zero_ne_one, ↓reduceIte] at hr_rp hc_rp
  let mr := toRadix a.q (bagList right) (ofRadix a.q (bagList left) m)
  have hl_len : (dpInstTree counting a.q cs vars left).length = a.tblLen := by
    rw [length_dpInstTree, hlBag_len, htblLen]
  have hr_len : (dpInstTree counting a.q cs vars right).length = a.q ^ a.rBagLen := by
    rw [length_dpInstTree, hrBag_len]
  have hmr_lt : mr < a.q ^ a.rBagLen := by
    rw [← hrBag_len]; exact toRadix_lt hq _ _
  have hm_lv : t.mem (a.lTblPtr + m) = (dpInstTree counting a.q cs vars left).getD m 0 := by
    rw [hlTbl_t.get m (by rw [hl_len]; exact hm_lt), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [hl_len]; exact hm_lt), Option.getD_some]
  have hm_rv : t.mem (a.rTblPtr + mr) = (dpInstTree counting a.q cs vars right).getD mr 0 := by
    rw [hrTbl_t.get mr (by rw [hr_len]; exact hmr_lt), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [hr_len]; exact hmr_lt), Option.getD_some]
  let entryVal := targetTbl[m]'(by rw [htarget_len]; exact hm_lt)
  have hprod_eq : t.mem (a.lTblPtr + m) * t.mem (a.rTblPtr + mr) = entryVal := by
    rw [hm_lv, hm_rv]
    simp only [entryVal, targetTbl, dpInstTree, mr, List.getElem_ofFn]
  have hentry_fit : Fits w entryVal := by
    have hmem_e : entryVal ∈ targetTbl := List.getElem_mem _
    exact hfit_cap.of_le (mem_dpInstTree_le counting hq cs vars (.join left right) _ hmem_e)
  have hl_addr_lt : a.lTblPtr + m < t.frontier := by rw [hfr_t]; omega
  have hr_addr_lt : a.rTblPtr + mr < t.frontier := by rw [hfr_t]; omega
  have hdst_lt : a.tblPtr + m < t.frontier := by rw [hfr_t]; omega
  obtain ⟨hst_ev, hres_ev⟩ := joinFillStep_eval a m t
  have hst_t₁ : (Memory.spec 0).clientState t (joinFillStep (a, m)) =
      ⟨Function.update t.mem (a.tblPtr + m) entryVal, t.frontier⟩ := by
    rw [hst_ev]
    dsimp only [mr] at hprod_eq
    rw [hr_rp, hprod_eq]
  have hv_step : (Memory.spec w).ValidHistory t
      ((Memory.spec w).clientHistory t (joinFillStep (a, m))) := by
    unfold joinFillStep
    dsimp only
    refine validHistory_read_bind hl_addr_lt ?_
    refine validHistory_bind_step hv_rp ?_
    rw [hst_rp, hr_rp]
    refine validHistory_read_bind hr_addr_lt ?_
    dsimp only [mr] at hprod_eq
    rw [hprod_eq]
    exact validHistory_write_bind hdst_lt hentry_fit (validHistory_pure w _ _)
  have hc_step : memoryCost (joinFillStep (a, m)) t ≤ stepCost := by
    have hr_s (x : ℕ) : (Memory.spec 0).clientState t (Memory.read x) = t := rfl
    unfold joinFillStep
    dsimp only
    rw [memoryCost_bind', memoryCost_read, hr_s, memoryCost_bind', hst_rp,
      memoryCost_bind', memoryCost_read, hr_s,
      memoryCost_bind', memoryCost_write, memoryCost_pure]
    dsimp only [stepCost]
    omega
  exact ⟨hv_step, hst_t₁, hres_ev, trivial, hc_step⟩

private theorem joinFillProg_realizes :
    Realizes .exact joinFillProg WordEncoding.encode WordEncoding.encode
      (fun w a s =>
        0 < a.q ∧ Fits w 1 ∧ Fits w a.q ∧
        Fits w (a.lBagPtr + a.lBagLen) ∧
        Fits w (a.lTblPtr + a.tblLen) ∧
        Fits w (a.rBagPtr + a.rBagLen) ∧
        Fits w (a.q ^ a.rBagLen) ∧
        Fits w (a.rTblPtr + a.q ^ a.rBagLen) ∧
        Fits w (a.tblPtr + a.tblLen) ∧
        ∃ (lTbl rTbl : List ℕ) (lCap rCap : ℕ),
          a.lTblPtr + a.tblLen ≤ a.tblPtr ∧
          a.rTblPtr + a.q ^ a.rBagLen ≤ a.tblPtr ∧
          HoldsIn a.lTblPtr lTbl s ∧ lTbl.length = a.tblLen ∧ (∀ x ∈ lTbl, x ≤ lCap) ∧
          HoldsIn a.rTblPtr rTbl s ∧ rTbl.length = a.q ^ a.rBagLen ∧ (∀ x ∈ rTbl, x ≤ rCap) ∧
          Fits w (lCap * rCap))
      (fun _ _ => 0) := by
  unfold joinFillProg
  realize [radixProjProg_realizes]
  obtain ⟨hq_pos, h1, hfit_q, hfit_lBag, hfit_lTbl, hfit_rBag, hfit_rPow, hfit_rTbl, hfit_tbl,
    lTbl, rTbl, lCap, rCap, hl_hi, hr_hi, hl_h, hl_len, hl_le, hr_h, hr_len, hr_le, hfit_prod⟩ := h
  refine iterationSafe_of_stepInv _ _ w _
    (fun (j : ℕ) (m : ℕ) (t : Memory.State) =>
      j ≤ d.tblLen ∧ m + j = d.tblLen ∧
      HoldsIn d.lTblPtr lTbl t ∧ HoldsIn d.rTblPtr rTbl t)
    (fun j m t ⟨hj_le, hm_eq, hl_t, hr_t⟩ => ?_)
    ⟨le_rfl, Nat.zero_add _, hl_h, hr_h⟩
  have hm_lt : m < d.tblLen := by omega
  have hfit_m : Fits w m := hfit_tbl.of_le (by omega)
  have hfit_m1 : Fits w (m + 1) := hfit_tbl.of_le (by omega)
  let rpArgs : RadixProjArgs :=
    ⟨d.q, d.lBagPtr, d.lBagLen, m, 0, 0, 0, d.rBagPtr, d.rBagLen⟩
  have hmr_lt : (Memory.spec 0).clientResult t (radixProjProg rpArgs) < d.q ^ d.rBagLen :=
    radixProjProg_result_lt (args := rpArgs) hq_pos t
  have hfit_laddr : Fits w (d.lTblPtr + m) := hfit_lTbl.of_le (by omega)
  have hfit_raddr :
      Fits w (d.rTblPtr + (Memory.spec 0).clientResult t (radixProjProg rpArgs)) :=
    hfit_rTbl.of_le (by omega)
  have hfit_taddr : Fits w (d.tblPtr + m) := hfit_tbl.of_le (by omega)
  have hlv_le : t.mem (d.lTblPtr + m) ≤ lCap := by
    have hm_l : m < lTbl.length := by rwa [hl_len]
    rw [hl_t.get m hm_l]
    exact hl_le _ (List.getElem_mem hm_l)
  have hrv_le :
      t.mem (d.rTblPtr + (Memory.spec 0).clientResult t (radixProjProg rpArgs)) ≤ rCap := by
    have hm_r : (Memory.spec 0).clientResult t (radixProjProg rpArgs) < rTbl.length := by
      rwa [hr_len]
    rw [hr_t.get _ hm_r]
    exact hr_le _ (List.getElem_mem hm_r)
  have hfit_mul :
      Fits w (t.mem (d.lTblPtr + m) *
        t.mem (d.rTblPtr + (Memory.spec 0).clientResult t (radixProjProg rpArgs))) :=
    hfit_prod.of_le (Nat.mul_le_mul hlv_le hrv_le)
  have hrp_safe :
      0 < d.q ∧ Fits w 1 ∧ Fits w d.q ∧ Fits w m ∧
        Fits w (d.lBagPtr + d.lBagLen) ∧ Fits w (d.rBagPtr + d.rBagLen) ∧
        Fits w (d.q ^ d.rBagLen) :=
    ⟨hq_pos, h1, hfit_q, hfit_m, hfit_lBag, hfit_rBag, hfit_rPow⟩
  obtain ⟨hst_ev, hres_ev⟩ := joinFillStep_eval d m t
  refine ⟨?_, Nat.le_of_succ_le hj_le, ?_, ?_, ?_⟩
  · dsimp only [joinFillStep]
    rw [radixProjProg_state]
    refine ⟨hfit_laddr, hrp_safe, ?_⟩
    repeat (
      first
      | refine And.intro ?_ ?_
      | exact hfit_raddr
      | exact hfit_taddr
      | exact hfit_mul
      | exact hfit_m1)
  · rw [hres_ev]; omega
  · rw [hst_ev]
    exact holdsIn_write_outside hl_t (.inr (by rw [hl_len]; omega))
  · rw [hst_ev]
    exact holdsIn_write_outside hr_t (.inr (by rw [hr_len]; omega))

private structure JoinNodeArgs where
  q : ℕ
  dLeft : ℕ
  dRight : ℕ
  dCur : ℕ

private def JoinNodeArgs.equiv : JoinNodeArgs ≃ ((ℕ × ℕ) × ℕ) × ℕ where
  toFun a := (((a.q, a.dLeft), a.dRight), a.dCur)
  invFun := fun (((q, dl), dr), dc) => ⟨q, dl, dr, dc⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding JoinNodeArgs := .ofEquiv JoinNodeArgs.equiv

private def joinNodeProg (a : JoinNodeArgs) : Memory.Prog Unit := do
  let lBagPtr ← Memory.read a.dLeft
  let lBagLen ← Memory.read (a.dLeft + 1)
  let lTblPtr ← Memory.read (a.dLeft + 2)
  let lTblLen ← Memory.read (a.dLeft + 3)
  let rBagPtr ← Memory.read a.dRight
  let rBagLen ← Memory.read (a.dRight + 1)
  let rTblPtr ← Memory.read (a.dRight + 2)
  let tblPtr ← Memory.allocDirty lTblLen
  let _ ← joinFillProg
    ⟨a.q, lBagPtr, lBagLen, lTblPtr, rBagPtr, rBagLen, rTblPtr, tblPtr, lTblLen⟩
  writeDescProg ⟨a.dCur, lBagPtr, lBagLen, tblPtr, lTblLen⟩

private theorem joinNodeProg_spec {w F_lo : ℕ} (counting : Bool) (a : JoinNodeArgs)
    (hq : 0 < a.q) {left right : NiceTree ℕ} {cs : List (ConstraintTable a.q)} {vars : List ℕ}
    {s : Memory.State}
    (hleft : NodeDescAt F_lo counting a.q cs vars left a.dLeft s)
    (hright : NodeDescAt F_lo counting a.q cs vars right a.dRight s)
    (hdCur : a.dCur + 4 ≤ F_lo)
    (hFlo : F_lo ≤ s.frontier)
    (hfit_peak : Fits w (s.frontier + a.q ^ (bagList left).length))
    (hfit_cap : Fits w (if counting then a.q ^ (NiceTree.join left right).size else 1)) :
    let sEnd := (Memory.spec 0).clientState s (joinNodeProg a)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (joinNodeProg a)) ∧
    sEnd.frontier ≤ s.frontier + a.q ^ (bagList left).length ∧
    FrameOutsideRange a.dCur (a.dCur + 4) s sEnd ∧
    NodeDescAt F_lo counting a.q cs vars (.join left right) a.dCur sEnd ∧
    memoryCost (joinNodeProg a) s ≤
      12 + a.q ^ (bagList left).length *
        ((bagList right).length * ((bagList left).length + 1) + 3) := by
  have hd_l := hleft.desc_hi
  have hd_r := hright.desc_hi
  have hm_lbLen : s.mem (a.dLeft + 1) = (bagList left).length := hleft.bag_len
  have hm_ltLen : s.mem (a.dLeft + 3) = a.q ^ (bagList left).length := hleft.tbl_len
  have hm_rbLen : s.mem (a.dRight + 1) = (bagList right).length := hright.bag_len
  let lBagPtr := s.mem a.dLeft
  let lBagLen := (bagList left).length
  let lTblPtr := s.mem (a.dLeft + 2)
  let lTblLen := a.q ^ lBagLen
  let rBagPtr := s.mem a.dRight
  let rBagLen := (bagList right).length
  let rTblPtr := s.mem (a.dRight + 2)
  let tblPtr := s.frontier
  let s₁ := (Memory.spec 0).clientState s (Memory.allocDirty lTblLen)
  have hs₁_fr : s₁.frontier = tblPtr + lTblLen := rfl
  have hp₁ : PreservesBelow tblPtr s s₁ := preservesBelow_allocDirty s lTblLen
  have hv₁ : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (Memory.allocDirty lTblLen)) :=
    validHistory_allocDirty hfit_peak
  let fillArgs : JoinFillArgs :=
    ⟨a.q, lBagPtr, lBagLen, lTblPtr, rBagPtr, rBagLen, rTblPtr, tblPtr, lTblLen⟩
  obtain ⟨hv_fill, hfr_fill, hp_fill, htbl_fill, hc_fill⟩ :=
    joinFillProg_spec (w := w) counting fillArgs hq
      (hleft.bag_holds.mono_frontier hp₁) rfl hleft.bag_holds.1
      (hleft.tbl_holds.mono_frontier hp₁)
      (by have := hleft.tbl_holds.1; rw [length_dpInstTree] at this; exact this)
      (hright.bag_holds.mono_frontier hp₁) rfl hright.bag_holds.1
      (hright.tbl_holds.mono_frontier hp₁)
      (by have := hright.tbl_holds.1; rw [length_dpInstTree] at this; exact this)
      rfl (by rw [hs₁_fr]) hfit_cap
  let s₂ := (Memory.spec 0).clientState s₁ (joinFillProg fillArgs)
  have hs₂_fr : s₂.frontier = tblPtr + lTblLen := by rw [hfr_fill, hs₁_fr]
  have hp_s_s₂ : PreservesBelow tblPtr s s₂ := hp₁.trans hp_fill
  have hlBag_s₂ : HoldsIn lBagPtr (bagList left) s₂ :=
    hleft.bag_holds.mono_frontier hp_s_s₂
  have hd_s₂ : a.dCur + 4 ≤ s₂.frontier := by rw [hs₂_fr]; dsimp only [tblPtr]; omega
  obtain ⟨hv_wd, hfr_wd, hframe_wd, hm0, hm1, hm2, hm3, hc_wd⟩ :=
    writeDescProg_spec (w := w) ⟨a.dCur, lBagPtr, lBagLen, tblPtr, lTblLen⟩ hd_s₂
      (hfit_peak.of_le (by have := hleft.bag_holds.1; dsimp only [lBagPtr]; omega))
      (hfit_peak.of_le (by have := hleft.bag_holds.1; dsimp only [lBagLen]; omega))
      (hfit_peak.of_le (by dsimp only [tblPtr]; omega))
      (hfit_peak.of_le (by dsimp only [lTblLen, lBagLen]; omega))
  dsimp only at hm0 hm1 hm2 hm3
  let sEnd := (Memory.spec 0).clientState s₂
    (writeDescProg ⟨a.dCur, lBagPtr, lBagLen, tblPtr, lTblLen⟩)
  have hr_s (x : ℕ) : (Memory.spec 0).clientState s (Memory.read x) = s := rfl
  have hr_r (x : ℕ) : (Memory.spec 0).clientResult s (Memory.read x) = s.mem x := rfl
  have ha1_s : (Memory.spec 0).clientState s (Memory.allocDirty lTblLen) = s₁ := rfl
  have ha1_r : (Memory.spec 0).clientResult s (Memory.allocDirty lTblLen) = tblPtr := rfl
  have hsEnd_eq : (Memory.spec 0).clientState s (joinNodeProg a) = sEnd := by
    unfold joinNodeProg
    iterate 7 rw [StateTransitionSpec.clientState_bind, hr_s, hr_r]
    rw [hm_lbLen, hm_ltLen, hm_rbLen,
      StateTransitionSpec.clientState_bind, ha1_s, ha1_r,
      StateTransitionSpec.clientState_bind]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold joinNodeProg
    iterate 7 (refine validHistory_read_bind (by omega) ?_)
    rw [hm_lbLen, hm_ltLen, hm_rbLen]
    refine validHistory_bind_step hv₁ ?_
    rw [ha1_s, ha1_r]
    exact validHistory_bind_step hv_fill hv_wd
  · rw [hsEnd_eq, hfr_wd, hs₂_fr]
  · rw [hsEnd_eq]
    exact (FrameOutsideRange.of_preservesBelow a.dCur (a.dCur + 4) hp_s_s₂).trans hframe_wd
  · rw [hsEnd_eq]
    refine ⟨hdCur, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hm0]; exact hleft.bag_lo
    · rw [hm1]; rfl
    · rw [hm0]
      exact hlBag_s₂.frame_outsideRange (.inr (le_trans hdCur hleft.bag_lo)) hframe_wd
    · rw [hm2]; exact hFlo
    · rw [hm3]; rfl
    · rw [hm2]
      exact htbl_fill.frame_outsideRange (.inr (le_trans hdCur hFlo)) hframe_wd
  · unfold joinNodeProg
    iterate 7 rw [memoryCost_bind', memoryCost_read, hr_s, hr_r]
    rw [hm_lbLen, hm_ltLen, hm_rbLen, memoryCost_bind', memoryCost_allocDirty, ha1_s, ha1_r,
      memoryCost_bind']
    dsimp only [s₂, fillArgs, lBagPtr, lBagLen, lTblPtr, lTblLen, rBagPtr, rBagLen, rTblPtr,
      tblPtr] at hc_fill hc_wd ⊢
    omega

private theorem joinNodeProg_realizes :
    Realizes .exact joinNodeProg WordEncoding.encode WordEncoding.encode
      (fun w a s =>
        0 < a.q ∧ Fits w 3 ∧ Fits w a.q ∧
        Fits w (a.dLeft + 3) ∧ Fits w (a.dRight + 2) ∧ Fits w (a.dCur + 3) ∧
        ∃ (F_lo : ℕ) (counting : Bool) (left right : NiceTree ℕ)
          (cs : List (ConstraintTable a.q)) (vars : List ℕ),
          NodeDescAt F_lo counting a.q cs vars left a.dLeft s ∧
          NodeDescAt F_lo counting a.q cs vars right a.dRight s ∧
          Fits w (a.q ^ (bagList right).length) ∧
          Fits w (s.frontier + a.q ^ (bagList left).length) ∧
          Fits w (if counting then a.q ^ (NiceTree.join left right).size else 1))
      (fun _ _ => 0) := by
  unfold joinNodeProg
  realize [joinFillProg_realizes, writeDescProg_realizes]
  all_goals
    obtain ⟨hq, _, hfit_q, hdL, hdR, hdCur, F_lo, counting, left, right, cs, vars,
      hl, hr, hfit_rPow, hfit_peak, hfit_cap⟩ := h
    try rw [hl.bag_len]
    try rw [hl.tbl_len]
    try rw [hr.bag_len]
    let lTblLen := d.q ^ (bagList left).length
    let s₁ := (Memory.spec 0).clientState s (Memory.allocDirty lTblLen)
    have hp₁ : PreservesBelow s.frontier s s₁ := preservesBelow_allocDirty s lTblLen
    have hl_bag := hl.bag_holds.1
    have hl_tbl := hl.tbl_holds.1
    rw [length_dpInstTree] at hl_tbl
    have hr_bag := hr.bag_holds.1
    have hr_tbl := hr.tbl_holds.1
    rw [length_dpInstTree] at hr_tbl
    let lCap := if counting then d.q ^ left.size else 1
    let rCap := if counting then d.q ^ right.size else 1
    have hprod_cap : Fits w (lCap * rCap) := by
      cases counting
      · simpa [lCap, rCap] using hfit_cap
      · simp only [↓reduceIte] at hfit_cap
        dsimp only [lCap, rCap]
        simp only [↓reduceIte]
        rw [← Nat.pow_add]
        exact hfit_cap.of_le (Nat.pow_le_pow_right hq (by simp [NiceTree.size_join]))
    first
    | exact hdL.of_le (by omega)
    | exact hdR.of_le (by omega)
    | exact hdCur
    | exact hq
    | exact hfit_q
    | exact hfit_rPow
    | exact hfit_peak.of_le (by omega)
    | exact ⟨dpInstTree counting d.q cs vars left, dpInstTree counting d.q cs vars right,
        lCap, rCap, hl_tbl, hr_tbl,
        hl.tbl_holds.mono_frontier hp₁, length_dpInstTree _ _ _ _ _,
        mem_dpInstTree_le counting hq cs vars left,
        hr.tbl_holds.mono_frontier hp₁, length_dpInstTree _ _ _ _ _,
        mem_dpInstTree_le counting hq cs vars right,
        hprod_cap⟩

/-! ### Bottom-up nice-tree DP pass and top-level Word-RAM entry point -/

private theorem NodeDescAt.frame_outsideRange {F_lo : ℕ} {counting : Bool} {q : ℕ}
    {cs : List (ConstraintTable q)} {vars : List ℕ} {S : NiceTree ℕ} {d lo hi : ℕ}
    {s₀ s₁ : Memory.State} (h : NodeDescAt F_lo counting q cs vars S d s₀)
    (hd_out : d + 4 ≤ lo ∨ hi ≤ d) (hhi_lo : hi ≤ F_lo)
    (hf : FrameOutsideRange lo hi s₀ s₁) :
    NodeDescAt F_lo counting q cs vars S d s₁ := by
  have hFlo_fr : F_lo ≤ s₀.frontier := by
    have := h.bag_lo; have := h.bag_holds.1; omega
  have hm0 : s₁.mem d = s₀.mem d := hf.2 d (by have := h.desc_hi; omega) (by omega)
  have hm1 : s₁.mem (d + 1) = s₀.mem (d + 1) :=
    hf.2 (d + 1) (by have := h.desc_hi; omega) (by omega)
  have hm2 : s₁.mem (d + 2) = s₀.mem (d + 2) :=
    hf.2 (d + 2) (by have := h.desc_hi; omega) (by omega)
  have hm3 : s₁.mem (d + 3) = s₀.mem (d + 3) :=
    hf.2 (d + 3) (by have := h.desc_hi; omega) (by omega)
  exact
    ⟨h.desc_hi,
     by rw [hm0]; exact h.bag_lo,
     by rw [hm1]; exact h.bag_len,
     by rw [hm0]; exact h.bag_holds.frame_outsideRange (.inr (le_trans hhi_lo h.bag_lo)) hf,
     by rw [hm2]; exact h.tbl_lo,
     by rw [hm3]; exact h.tbl_len,
     by rw [hm2]; exact h.tbl_holds.frame_outsideRange (.inr (le_trans hhi_lo h.tbl_lo)) hf⟩

private structure NodeEnv where
  mode : ℕ
  q : ℕ
  varsPtr : ℕ
  varsLen : ℕ
  treePtr : ℕ
  consRawPtr : ℕ
  numCons : ℕ
  descBase : ℕ

private def NodeEnv.equiv :
    NodeEnv ≃ (((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) where
  toFun e := (((((((e.mode, e.q), e.varsPtr), e.varsLen), e.treePtr), e.consRawPtr),
    e.numCons), e.descBase)
  invFun := fun (((((((md, q), vp), vl), tp), cp), nc), db) =>
    ⟨md, q, vp, vl, tp, cp, nc, db⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding NodeEnv := .ofEquiv NodeEnv.equiv

private def nodeStep (p : NodeEnv × ℕ) : Memory.Prog ℕ := do
  let env := p.1
  let cur := p.2
  let tag ← Memory.read (env.treePtr + 4 * cur)
  let arg ← Memory.read (env.treePtr + 4 * cur + 1)
  let ch1 ← Memory.read (env.treePtr + 4 * cur + 2)
  let ch2 ← Memory.read (env.treePtr + 4 * cur + 3)
  let dCur := env.descBase + 4 * cur
  if tag = 0 then
    let _ ← leafNodeProg ⟨env.consRawPtr, env.numCons, dCur⟩
    pure (cur + 1)
  else if tag = 1 then
    let _ ← introNodeProg ⟨env.q, arg, env.consRawPtr, env.numCons, env.descBase + 4 * ch1, dCur⟩
    pure (cur + 1)
  else if tag = 2 then
    let _ ← forgetNodeProg ⟨env.mode, env.q, arg, env.varsPtr, env.varsLen,
      env.descBase + 4 * ch1, dCur⟩
    pure (cur + 1)
  else
    let _ ← joinNodeProg ⟨env.q, env.descBase + 4 * ch1, env.descBase + 4 * ch2, dCur⟩
    pure (cur + 1)

private def nodeStepSafe (w : ℕ) (p : NodeEnv × ℕ) (s : Memory.State) : Prop :=
  let env := p.1
  let cur := p.2
  let dCur := env.descBase + 4 * cur
  Fits w 4 ∧ Fits w (cur + 1) ∧
  Fits w (env.treePtr + 4 * cur + 3) ∧
  Fits w (dCur + 3) ∧
  ((s.mem (env.treePtr + 4 * cur) = 0 ∧
      ∃ (q : ℕ) (cs : List (ConstraintTable q)),
        0 < q ∧ cs.length = env.numCons ∧
        HoldsIn env.consRawPtr (cs.flatMap ConstraintTable.encode) s ∧
        Fits w (env.consRawPtr + (cs.flatMap ConstraintTable.encode).length)) ∨
   (s.mem (env.treePtr + 4 * cur) = 1 ∧
      0 < env.q ∧ Fits w env.q ∧ Fits w (s.mem (env.treePtr + 4 * cur + 1)) ∧
      Fits w (env.descBase + 4 * s.mem (env.treePtr + 4 * cur + 2) + 3) ∧
      ∃ (F_lo : ℕ) (counting : Bool) (child : NiceTree ℕ)
        (cs : List (ConstraintTable env.q)) (vars : List ℕ),
        Memory.WellFormed w s ∧ cs.length = env.numCons ∧
        HoldsIn env.consRawPtr (cs.flatMap ConstraintTable.encode) s ∧
        env.consRawPtr + (cs.flatMap ConstraintTable.encode).length ≤ F_lo ∧
        NodeDescAt F_lo counting env.q cs vars child
          (env.descBase + 4 * s.mem (env.treePtr + 4 * cur + 2)) s ∧
        F_lo ≤ s.frontier ∧
        Fits w (s.frontier +
          ((s.mem (env.treePtr + 4 * cur + 1) :: bagList child).length +
            env.q ^ (s.mem (env.treePtr + 4 * cur + 1) :: bagList child).length))) ∨
   (s.mem (env.treePtr + 4 * cur) = 2 ∧
      0 < env.q ∧ Fits w env.q ∧ Fits w (env.varsPtr + env.varsLen) ∧
      Fits w (env.descBase + 4 * s.mem (env.treePtr + 4 * cur + 2) + 3) ∧
      ∃ (F_lo : ℕ) (counting : Bool) (child : NiceTree ℕ)
        (cs : List (ConstraintTable env.q)) (vars : List ℕ),
        env.mode = (if counting then 1 else 0) ∧
        (∀ u ∈ bagList child, Fits w u) ∧
        NodeDescAt F_lo counting env.q cs vars child
          (env.descBase + 4 * s.mem (env.treePtr + 4 * cur + 2)) s ∧
        F_lo ≤ s.frontier ∧
        Fits w (env.q ^ (bagList child).length) ∧
        Fits w (s.frontier +
          max (bagList child).length
            (((bagList child).erase (s.mem (env.treePtr + 4 * cur + 1))).length +
              env.q ^ ((bagList child).erase (s.mem (env.treePtr + 4 * cur + 1))).length)) ∧
        Fits w (if counting then env.q ^ (NiceTree.forget
          (s.mem (env.treePtr + 4 * cur + 1)) child).size else 1)) ∨
   (s.mem (env.treePtr + 4 * cur) ≠ 0 ∧ s.mem (env.treePtr + 4 * cur) ≠ 1 ∧
      s.mem (env.treePtr + 4 * cur) ≠ 2 ∧
      0 < env.q ∧ Fits w env.q ∧
      Fits w (env.descBase + 4 * s.mem (env.treePtr + 4 * cur + 2) + 3) ∧
      Fits w (env.descBase + 4 * s.mem (env.treePtr + 4 * cur + 3) + 2) ∧
      ∃ (F_lo : ℕ) (counting : Bool) (left right : NiceTree ℕ)
        (cs : List (ConstraintTable env.q)) (vars : List ℕ),
        NodeDescAt F_lo counting env.q cs vars left
          (env.descBase + 4 * s.mem (env.treePtr + 4 * cur + 2)) s ∧
        NodeDescAt F_lo counting env.q cs vars right
          (env.descBase + 4 * s.mem (env.treePtr + 4 * cur + 3)) s ∧
        Fits w (env.q ^ (bagList right).length) ∧
        Fits w (s.frontier + env.q ^ (bagList left).length) ∧
        Fits w (if counting then env.q ^ (NiceTree.join left right).size else 1)))

private theorem nodeStep_realizes :
    Realizes .exact nodeStep WordEncoding.encode WordEncoding.encode
      nodeStepSafe (fun _ _ => 0) := by
  unfold nodeStep
  realize [leafNodeProg_realizes, introNodeProg_realizes, forgetNodeProg_realizes,
    joinNodeProg_realizes]
  all_goals
    obtain ⟨h4, hcur1, htree3, hdCur3, hbranch⟩ := h
    have ht0 : Fits w (d.1.treePtr + 4 * d.2) := htree3.of_le (by omega)
    have ht1 : Fits w (d.1.treePtr + 4 * d.2 + 1) := htree3.of_le (by omega)
    have ht2 : Fits w (d.1.treePtr + 4 * d.2 + 2) := htree3.of_le (by omega)
    first
    | exact h4.of_le (by decide)
    | exact ht0
    | exact ht1
    | exact ht2
    | exact htree3
    | exact hdCur3
    | exact hdCur3.of_le (by omega)
    | (rcases hbranch with
        ⟨ht0', q, cs, hq, hlen, hcs, hend⟩ |
        ⟨ht0', _⟩ | ⟨ht0', _⟩ | ⟨ht0', _⟩ <;>
      omega)
    | (rcases hbranch with
        ⟨ht0', _⟩ |
        ⟨ht0', hq, hfit_q, hfit_arg, hfit_dCh, hex⟩ |
        ⟨ht0', _⟩ | ⟨_, ht1', _⟩ <;>
      first
      | omega
      | exact hfit_dCh.of_le (by omega))
    | (rcases hbranch with
        ⟨ht0', _⟩ | ⟨ht0', _⟩ |
        ⟨ht0', hq, hfit_q, hfit_vars, hfit_dCh, hex⟩ |
        ⟨_, _, ht2', _⟩ <;>
      first
      | omega
      | exact hfit_dCh.of_le (by omega))
    | (rcases hbranch with
        ⟨ht0', _⟩ | ⟨ht0', _⟩ | ⟨ht0', _⟩ |
        ⟨ht0', ht1', ht2', hq, hfit_q, hfit_dL, hfit_dR, hex⟩ <;>
      first
      | contradiction
      | exact hfit_q
      | exact hfit_dL
      | exact hfit_dL.of_le (by omega)
      | exact hfit_dR
      | exact hfit_dR.of_le (by omega)
      | exact hex)

private def iterNodesProg (d : (NodeEnv × ℕ) × ℕ) : Memory.Prog ℕ :=
  iterate nodeStep d.1.1 d.2 d.1.2

private theorem iterNodesProg_realizes :
    Realizes .exact iterNodesProg WordEncoding.encode WordEncoding.encode
      (fun w d s => iterationSafe nodeStep nodeStepSafe w d.1.1 d.2 d.1.2 s)
      (fun _ _ => 0) :=
  Realizes.iterate₀ WordEncoding.encode WordEncoding.encode nodeStep_realizes (fun _ _ => by
    unfold nodeStep; dsimp only; rw [memoryCost_bind', memoryCost_read]; omega)

private theorem clientState_iterate_add {δ σ : Type} (body : δ × σ → Memory.Prog σ) (d : δ)
    (n₁ n₂ : ℕ) (a : σ) (s : Memory.State) :
    (Memory.spec 0).clientState s (iterate body d (n₁ + n₂) a) =
      (Memory.spec 0).clientState ((Memory.spec 0).clientState s (iterate body d n₁ a))
        (iterate body d n₂ ((Memory.spec 0).clientResult s (iterate body d n₁ a))) := by
  induction n₁ generalizing a s with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ n₁ ih =>
    rw [Nat.succ_add]
    change (Memory.spec 0).clientState s (body (d, a) >>= iterate body d (n₁ + n₂)) =
      (Memory.spec 0).clientState
        ((Memory.spec 0).clientState s (body (d, a) >>= iterate body d n₁))
        (iterate body d n₂ ((Memory.spec 0).clientResult s (body (d, a) >>= iterate body d n₁)))
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientResult_bind, ih]

private theorem clientResult_iterate_add {δ σ : Type} (body : δ × σ → Memory.Prog σ) (d : δ)
    (n₁ n₂ : ℕ) (a : σ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (iterate body d (n₁ + n₂) a) =
      (Memory.spec 0).clientResult ((Memory.spec 0).clientState s (iterate body d n₁ a))
        (iterate body d n₂ ((Memory.spec 0).clientResult s (iterate body d n₁ a))) := by
  induction n₁ generalizing a s with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ n₁ ih =>
    rw [Nat.succ_add]
    change (Memory.spec 0).clientResult s (body (d, a) >>= iterate body d (n₁ + n₂)) =
      (Memory.spec 0).clientResult
        ((Memory.spec 0).clientState s (body (d, a) >>= iterate body d n₁))
        (iterate body d n₂ ((Memory.spec 0).clientResult s (body (d, a) >>= iterate body d n₁)))
    rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientResult_bind, ih]

private theorem memoryCost_iterate_add {δ σ : Type} (body : δ × σ → Memory.Prog σ) (d : δ)
    (n₁ n₂ : ℕ) (a : σ) (s : Memory.State) :
    memoryCost (iterate body d (n₁ + n₂) a) s =
      memoryCost (iterate body d n₁ a) s +
        memoryCost (iterate body d n₂ ((Memory.spec 0).clientResult s (iterate body d n₁ a)))
          ((Memory.spec 0).clientState s (iterate body d n₁ a)) := by
  induction n₁ generalizing a s with
  | zero =>
    rw [Nat.zero_add]
    change memoryCost (iterate body d n₂ a) s = 0 + memoryCost (iterate body d n₂ a) s
    omega
  | succ n₁ ih =>
    rw [Nat.succ_add]
    change memoryCost (body (d, a) >>= iterate body d (n₁ + n₂)) s =
      memoryCost (body (d, a) >>= iterate body d n₁) s +
        memoryCost (iterate body d n₂ ((Memory.spec 0).clientResult s (body (d, a) >>=
          iterate body d n₁)))
          ((Memory.spec 0).clientState s (body (d, a) >>= iterate body d n₁))
    rw [memoryCost_bind', memoryCost_bind', StateTransitionSpec.clientResult_bind,
      StateTransitionSpec.clientState_bind, ih]
    omega

private theorem validHistory_iterate_add {w : ℕ} {δ σ : Type} (body : δ × σ → Memory.Prog σ)
    (d : δ) (n₁ n₂ : ℕ) (a : σ) (s : Memory.State)
    (hv₁ : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (iterate body d n₁ a)))
    (hv₂ : let s₁ := (Memory.spec 0).clientState s (iterate body d n₁ a)
      let r₁ := (Memory.spec 0).clientResult s (iterate body d n₁ a)
      (Memory.spec w).ValidHistory s₁ ((Memory.spec w).clientHistory s₁ (iterate body d n₂ r₁))) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (iterate body d (n₁ + n₂) a)) := by
  induction n₁ generalizing a s with
  | zero =>
    rw [Nat.zero_add]
    exact hv₂
  | succ n₁ ih =>
    rw [Nat.succ_add]
    change (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (body (d, a) >>= iterate body d (n₁ + n₂)))
    change (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (body (d, a) >>= iterate body d n₁)) at hv₁
    obtain ⟨hb, hrest⟩ := (validHistory_bind' w (body (d, a)) (iterate body d n₁) s).1 hv₁
    refine validHistory_bind_step hb (ih _ _ hrest ?_)
    dsimp only
    rwa [← StateTransitionSpec.clientState_bind, ← StateTransitionSpec.clientResult_bind]

private theorem iterationSafe_add {δ σ : Type} (body : δ × σ → Memory.Prog σ)
    (safe : ℕ → (δ × σ) → Memory.State → Prop) (w : ℕ) (d : δ)
    (n₁ n₂ : ℕ) (a : σ) (s : Memory.State)
    (hs₁ : iterationSafe body safe w d n₁ a s)
    (hs₂ : iterationSafe body safe w d n₂
      ((Memory.spec 0).clientResult s (iterate body d n₁ a))
      ((Memory.spec 0).clientState s (iterate body d n₁ a))) :
    iterationSafe body safe w d (n₁ + n₂) a s := by
  induction n₁ generalizing a s with
  | zero =>
    rw [Nat.zero_add]
    exact hs₂
  | succ n₁ ih =>
    rw [Nat.succ_add]
    refine ⟨hs₁.1, ih _ _ hs₁.2 ?_⟩
    change iterationSafe body safe w d n₂
      ((Memory.spec 0).clientResult s (body (d, a) >>= iterate body d n₁))
      ((Memory.spec 0).clientState s (body (d, a) >>= iterate body d n₁)) at hs₂
    rwa [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind] at hs₂

private theorem niceTree_size_pos (T : NiceTree ℕ) : 0 < T.size := by
  cases T <;> simp [NiceTree.size]

private theorem maxTreeVert_le_introduce (v : ℕ) (child : NiceTree ℕ) :
    maxTreeVert child ≤ maxTreeVert (.introduce v child) := le_max_right _ _

private theorem maxTreeVert_le_forget (v : ℕ) (child : NiceTree ℕ) :
    maxTreeVert child ≤ maxTreeVert (.forget v child) := le_max_right _ _

private theorem maxTreeVert_le_join_left (left right : NiceTree ℕ) :
    maxTreeVert left ≤ maxTreeVert (.join left right) := le_max_left _ _

private theorem maxTreeVert_le_join_right (left right : NiceTree ℕ) :
    maxTreeVert right ≤ maxTreeVert (.join left right) := le_max_right _ _

private theorem maxTableExp_le_introduce (v : ℕ) (child : NiceTree ℕ) :
    maxTableExp child ≤ maxTableExp (.introduce v child) := le_max_right _ _

private theorem maxTableExp_le_forget (v : ℕ) (child : NiceTree ℕ) :
    maxTableExp child ≤ maxTableExp (.forget v child) := le_max_right _ _

private theorem maxTableExp_le_join_left (left right : NiceTree ℕ) :
    maxTableExp left ≤ maxTableExp (.join left right) :=
  (le_max_left _ _).trans (le_max_right _ _)

private theorem maxTableExp_le_join_right (left right : NiceTree ℕ) :
    maxTableExp right ≤ maxTableExp (.join left right) :=
  (le_max_right _ _).trans (le_max_right _ _)

private theorem holdsIn_encode_decode (inst : TreeCSPInstance) :
    let s₀ := Memory.State.init inst.encode
    let treePtr := 6 + inst.vars.length
    let consRawPtr := treePtr + 4 * inst.tree.size
    s₀.frontier = inst.encode.length + 1 ∧
    inst.encode.length = 5 + inst.vars.length + 4 * inst.tree.size +
      (inst.constraints.flatMap ConstraintTable.encode).length ∧
    s₀.mem 1 = (if inst.counting then 1 else 0) ∧
    s₀.mem 2 = inst.domainSize ∧
    s₀.mem 3 = inst.vars.length ∧
    s₀.mem 4 = inst.constraints.length ∧
    s₀.mem 5 = inst.tree.size ∧
    HoldsIn 6 inst.vars s₀ ∧
    HoldsIn treePtr (encodeNiceTree inst.tree) s₀ ∧
    HoldsIn consRawPtr (inst.constraints.flatMap ConstraintTable.encode) s₀ := by
  let s₀ := Memory.State.init inst.encode
  have hfr : s₀.frontier = inst.encode.length + 1 := rfl
  have hlen : inst.encode.length = 5 + inst.vars.length + 4 * inst.tree.size +
      (inst.constraints.flatMap ConstraintTable.encode).length := by
    unfold TreeCSPInstance.encode
    simp only [List.length_append, List.length_cons, List.length_nil, length_encodeNiceTree]
  have hall : HoldsIn 1 inst.encode s₀ := holdsIn_init inst.encode
  unfold TreeCSPInstance.encode at hall
  rw [HoldsIn.append_iff] at hall; obtain ⟨hall, hcons⟩ := hall
  rw [HoldsIn.append_iff] at hall; obtain ⟨hall, htree⟩ := hall
  rw [HoldsIn.append_iff] at hall; obtain ⟨hall, hvars⟩ := hall
  rw [HoldsIn.cons_iff] at hall; obtain ⟨_, hm1, hall⟩ := hall
  rw [HoldsIn.cons_iff] at hall; obtain ⟨_, hm2, hall⟩ := hall
  rw [HoldsIn.cons_iff] at hall; obtain ⟨_, hm3, hall⟩ := hall
  rw [HoldsIn.cons_iff] at hall; obtain ⟨_, hm4, hall⟩ := hall
  rw [HoldsIn.cons_iff] at hall; obtain ⟨_, hm5, _⟩ := hall
  rw [show 1 + ([if inst.counting then 1 else 0, inst.domainSize, inst.vars.length,
      inst.constraints.length, inst.tree.size] ++ inst.vars).length = 6 + inst.vars.length from by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega] at htree
  rw [show 1 + ([if inst.counting then 1 else 0, inst.domainSize, inst.vars.length,
      inst.constraints.length, inst.tree.size] ++ inst.vars ++
      encodeNiceTree inst.tree).length = 6 + inst.vars.length + 4 * inst.tree.size from by
    simp only [List.length_append, List.length_cons, List.length_nil, length_encodeNiceTree]
    omega] at hcons
  exact ⟨hfr, hlen, hm1, hm2, hm3, hm4, hm5, hvars, htree, hcons⟩

private abbrev subtreeEnv (inst : TreeCSPInstance) : NodeEnv :=
  ⟨if inst.counting then 1 else 0, inst.domainSize, 6, inst.vars.length,
    6 + inst.vars.length, 6 + inst.vars.length + 4 * inst.tree.size,
    inst.constraints.length, inst.encode.length + 1⟩

private abbrev SubtreeFullSpec (w : ℕ) (inst : TreeCSPInstance) (S : NiceTree ℕ) (offset : ℕ)
    (s : Memory.State) : Prop :=
  let env := subtreeEnv inst
  let F_lo := env.descBase + 4 * inst.tree.size
  offset + S.size ≤ inst.tree.size →
  maxTableExp S ≤ maxTableExp inst.tree →
  maxTreeVert S ≤ maxTreeVert inst.tree →
  Memory.WellFormed w s →
  F_lo ≤ s.frontier →
  s.frontier + S.size * (maxTableExp inst.tree + 2 + inst.domainSize ^ maxTableExp inst.tree) ≤
    F_lo + inst.tree.size *
      (maxTableExp inst.tree + 2 + inst.domainSize ^ maxTableExp inst.tree) →
  HoldsIn env.varsPtr inst.vars s →
  HoldsIn (env.treePtr + 4 * offset) (encodeNiceTreeAux offset S) s →
  HoldsIn env.consRawPtr (inst.constraints.flatMap ConstraintTable.encode) s →
  let prog := iterate nodeStep env S.size offset
  let sEnd := (Memory.spec 0).clientState s prog
  iterationSafe nodeStep nodeStepSafe w env S.size offset s ∧
  (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
  (Memory.spec 0).clientResult s prog = offset + S.size ∧
  sEnd.frontier ≤
    s.frontier + S.size * (maxTableExp inst.tree + 2 + inst.domainSize ^ maxTableExp inst.tree) ∧
  FrameOutsideRange (env.descBase + 4 * offset)
    (env.descBase + 4 * (offset + S.size)) s sEnd ∧
  NodeDescAt F_lo inst.counting inst.domainSize inst.constraints inst.vars S
    (env.descBase + 4 * (offset + S.size - 1)) sEnd ∧
  memoryCost prog s ≤
    S.size *
      (16 + 4 * maxTableExp inst.tree + inst.vars.length +
        inst.domainSize ^ maxTableExp inst.tree *
          (maxTableExp inst.tree ^ 2 + maxTableExp inst.tree + 4 +
            3 * inst.constraints.length +
            inst.totalArity * (2 * maxTableExp inst.tree + 3)))

private theorem subtree_setup {w : ℕ} (inst : TreeCSPInstance) (hw : Fits w inst.wordBound) :
    let env := subtreeEnv inst
    let F_lo := env.descBase + 4 * inst.tree.size
    let E := maxTableExp inst.tree
    let perSpace := E + 2 + inst.domainSize ^ E
    1 ≤ inst.domainSize ^ E ∧
    Fits w 4 ∧
    Fits w inst.domainSize ∧
    Fits w inst.tree.size ∧
    Fits w (F_lo + inst.tree.size * perSpace) ∧
    env.consRawPtr + (inst.constraints.flatMap ConstraintTable.encode).length = env.descBase ∧
    env.varsPtr + env.varsLen ≤ env.descBase ∧
    env.consRawPtr + (inst.constraints.flatMap ConstraintTable.encode).length ≤ env.descBase ∧
    0 < inst.tree.size ∧
    perSpace ≤ inst.tree.size * perSpace ∧
    (∀ A : ℕ, A ≤ E ^ 2 + E + 4 + 3 * inst.constraints.length + inst.totalArity * (2 * E + 3) →
      inst.domainSize ^ E * A ≤
        inst.domainSize ^ E *
          (E ^ 2 + E + 4 + 3 * inst.constraints.length + inst.totalArity * (2 * E + 3))) ∧
    (∀ S, maxTreeVert S ≤ maxTreeVert inst.tree → ∀ u ∈ bagList S, Fits w u) := by
  intro env F_lo E perSpace
  have hq : 0 < inst.domainSize := inst.domainSize_pos
  have hpow_ge1 : 1 ≤ inst.domainSize ^ E := Nat.one_le_pow E inst.domainSize hq
  have hfit_4 : Fits w 4 := hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
  have hfit_q : Fits w inst.domainSize := hw.of_le (by
    have h1q : inst.domainSize ≤ inst.domainSize * inst.domainSize ^ E :=
      Nat.le_mul_of_pos_right _ hpow_ge1
    dsimp only [E] at h1q
    unfold TreeCSPInstance.wordBound; dsimp only; omega)
  have hfit_tree : Fits w inst.tree.size :=
    hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
  have hfit_total : Fits w (F_lo + inst.tree.size * perSpace) := hw.of_le (by
    have hlen_enc : inst.encode.length = 5 + inst.vars.length + 4 * inst.tree.size +
        (inst.constraints.flatMap ConstraintTable.encode).length :=
      (holdsIn_encode_decode inst).2.1
    dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *
    unfold TreeCSPInstance.wordBound; dsimp only; omega)
  have hcons_len_bound : env.consRawPtr +
      (inst.constraints.flatMap ConstraintTable.encode).length = env.descBase := by
    have hlen_enc := (holdsIn_encode_decode inst).2.1
    dsimp only [env, subtreeEnv]
    omega
  have hvars_lt_desc : env.varsPtr + env.varsLen ≤ env.descBase := by
    have hlen_enc := (holdsIn_encode_decode inst).2.1
    dsimp only [env, subtreeEnv]
    omega
  have hcons_lt_desc : env.consRawPtr +
      (inst.constraints.flatMap ConstraintTable.encode).length ≤ env.descBase :=
    le_of_eq hcons_len_bound
  have hts_pos : 0 < inst.tree.size := niceTree_size_pos inst.tree
  have hperSpace_le_total : perSpace ≤ inst.tree.size * perSpace :=
    Nat.le_mul_of_pos_left perSpace hts_pos
  have hc_ge : ∀ A : ℕ,
      A ≤ E ^ 2 + E + 4 + 3 * inst.constraints.length + inst.totalArity * (2 * E + 3) →
      inst.domainSize ^ E * A ≤
        inst.domainSize ^ E *
          (E ^ 2 + E + 4 + 3 * inst.constraints.length + inst.totalArity * (2 * E + 3)) :=
    fun _ hA => Nat.mul_le_mul_left _ hA
  have hfit_tree_vert : ∀ S, maxTreeVert S ≤ maxTreeVert inst.tree → ∀ u ∈ bagList S, Fits w u :=
    fun S hmv u hu => hw.of_le (by
      have hum := (mem_bagList_le_maxTreeVert S hu).trans hmv
      have hmvt : maxTreeVert inst.tree ≤ inst.maxVarLabel :=
        le_trans (le_max_left _ _) (le_max_right _ _)
      unfold TreeCSPInstance.wordBound; dsimp only; omega)
  exact ⟨hpow_ge1, hfit_4, hfit_q, hfit_tree, hfit_total, hcons_len_bound, hvars_lt_desc,
    hcons_lt_desc, hts_pos, hperSpace_le_total, hc_ge, hfit_tree_vert⟩

private theorem subtree_forget {w : ℕ} (inst : TreeCSPInstance) (hw : Fits w inst.wordBound)
    (v : ℕ) (child : NiceTree ℕ) (ih : ∀ offset s, SubtreeFullSpec w inst child offset s) :
    ∀ offset s, SubtreeFullSpec w inst (.forget v child) offset s := by
  let env := subtreeEnv inst
  let F_lo := env.descBase + 4 * inst.tree.size
  have hq : 0 < inst.domainSize := inst.domainSize_pos
  let E := maxTableExp inst.tree
  let perSpace := E + 2 + inst.domainSize ^ E
  let perCost := 16 + 4 * E + inst.vars.length + inst.domainSize ^ E *
    (E ^ 2 + E + 4 + 3 * inst.constraints.length + inst.totalArity * (2 * E + 3))
  obtain ⟨hpow_ge1, hfit_4, hfit_q, hfit_tree, hfit_total, _, hvars_lt_desc, _,
    _, hperSpace_le_total, hc_ge, hfit_tree_vert⟩ := subtree_setup inst hw
  have hfit_total' : Fits w (F_lo + inst.tree.size * perSpace) := hfit_total
  intro offset s hsz hexp hmv hwf hs_fr hfit_bud hvars htree hcons
  have hsz_ch_pos := niceTree_size_pos child
  have hsz_ch : offset + child.size ≤ inst.tree.size := by
    simp only [NiceTree.size_forget] at hsz; omega
  have hexp_ch : maxTableExp child ≤ E := (maxTableExp_le_forget v child).trans hexp
  have hmv_ch : maxTreeVert child ≤ maxTreeVert inst.tree :=
    (maxTreeVert_le_forget v child).trans hmv
  have hfit_bud_ch : s.frontier + child.size * perSpace ≤ F_lo + inst.tree.size * perSpace := by
    have hmul_le : child.size * perSpace ≤ (NiceTree.forget v child).size * perSpace :=
      Nat.mul_le_mul_right _ (by simp [NiceTree.size_forget])
    exact le_trans (Nat.add_le_add_left hmul_le _) hfit_bud
  have htree_app := htree
  rw [encodeNiceTreeAux, HoldsIn.append_iff, length_encodeNiceTreeAux] at htree_app
  obtain ⟨htree_ch, hroot_hold⟩ := htree_app
  obtain ⟨hsafe_ch, hv_ch, hres_ch, hfr_ch, hframe_ch, hdesc_ch, hc_ch⟩ :=
    ih offset s hsz_ch hexp_ch hmv_ch hwf hs_fr hfit_bud_ch hvars htree_ch hcons
  let cur := offset + child.size
  obtain ⟨s₁, hs₁_def⟩ :
      ∃ s₁, (Memory.spec 0).clientState s (iterate nodeStep env child.size offset) = s₁ := ⟨_, rfl⟩
  rw [hs₁_def] at hfr_ch hframe_ch hdesc_ch
  have hFlo₁ : F_lo ≤ s₁.frontier := hs_fr.trans hframe_ch.1
  have hout_vars : env.varsPtr + env.varsLen ≤ env.descBase + 4 * offset :=
    hvars_lt_desc.trans (Nat.le_add_right _ _)
  have hout_root : env.treePtr + 4 * cur + [2, v, cur - 1, 0].length ≤
      env.descBase + 4 * offset := by
    simp only [List.length_cons, List.length_nil]
    change env.treePtr + 4 * (offset + child.size) + 4 ≤ env.descBase + 4 * offset
    simp only [NiceTree.size_forget] at hsz
    dsimp only [env, subtreeEnv] at *
    omega
  have hvars₁ : HoldsIn env.varsPtr inst.vars s₁ :=
    hvars.frame_outsideRange (.inl hout_vars) hframe_ch
  have hroot₁ : HoldsIn (env.treePtr + 4 * cur) [2, v, cur - 1, 0] s₁ := by
    rw [show env.treePtr + 4 * offset + 4 * child.size = env.treePtr + 4 * cur from by
      dsimp only [cur]; omega] at hroot_hold
    simpa only [cur, Nat.add_sub_cancel] using
      hroot_hold.frame_outsideRange (.inl hout_root) hframe_ch
  have hr_root := hroot₁
  rw [HoldsIn.cons_iff, HoldsIn.cons_iff, HoldsIn.cons_iff, HoldsIn.cons_iff] at hr_root
  obtain ⟨_, htag2, _, harg_v, _, hch1_eq, _, _, _⟩ := hr_root
  have hdCur_hi : env.descBase + 4 * cur + 4 ≤ F_lo := by
    simp only [NiceTree.size_forget] at hsz; dsimp only [cur, F_lo, env, subtreeEnv] at *; omega
  let LB := (bagList child).erase v
  have hLB_succ_le : LB.length + 1 ≤ E := by
    have h1 : LB.length + 1 ≤ maxTableExp (.forget v child) := le_max_left _ _
    exact h1.trans hexp
  have hcbag_len_le : (bagList child).length ≤ E :=
    (bagList_length_le_maxTableExp child).trans hexp_ch
  have hpow_ch_le : inst.domainSize ^ (bagList child).length ≤ inst.domainSize ^ E :=
    Nat.pow_le_pow_right hq hcbag_len_le
  have hpow_LB1_le : inst.domainSize ^ (LB.length + 1) ≤ inst.domainSize ^ E :=
    Nat.pow_le_pow_right hq hLB_succ_le
  have hpow_LB_le : inst.domainSize ^ LB.length ≤ inst.domainSize ^ E :=
    Nat.pow_le_pow_right hq (by omega)
  have hfit_cPow : Fits w (inst.domainSize ^ (bagList child).length) := by
    have hc_le_sp : inst.domainSize ^ (bagList child).length ≤ perSpace := by
      dsimp only [perSpace]; omega
    exact hfit_total.of_le (le_trans hc_le_sp (le_trans hperSpace_le_total (Nat.le_add_left _ _)))
  have hs₁_peak : Fits w (s₁.frontier +
      max (bagList child).length (LB.length + inst.domainSize ^ LB.length)) :=
    hfit_total'.of_le (by
      change s.frontier + (NiceTree.forget v child).size * perSpace ≤
        F_lo + inst.tree.size * perSpace at hfit_bud
      simp only [NiceTree.size_forget] at hfit_bud
      have hmx : max (bagList child).length (LB.length + inst.domainSize ^ LB.length) ≤
          perSpace :=
        max_le (by dsimp only [perSpace]; omega) (by dsimp only [perSpace]; omega)
      have hmul_bud : (child.size + 1) * perSpace = child.size * perSpace + perSpace := by ring
      change s₁.frontier ≤ s.frontier + child.size * perSpace at hfr_ch
      omega)
  have hfit_cap : Fits w
      (if inst.counting then inst.domainSize ^ (NiceTree.forget v child).size else 1) :=
    hw.of_le (by
      have hsz_le : (NiceTree.forget v child).size ≤ inst.tree.size :=
        Nat.le_trans (Nat.le_add_left _ offset) hsz
      have hpow_s := Nat.pow_le_pow_right hq hsz_le
      unfold TreeCSPInstance.wordBound TreeCSPInstance.maxEntryBound
      dsimp only
      by_cases hcnt : inst.counting = true
      · rw [ite_eq_left hcnt, ite_eq_left hcnt]; omega
      · rw [ite_eq_right hcnt, ite_eq_right hcnt]; omega)
  have hfit_bag_el := hfit_tree_vert child hmv_ch
  let fgArgs : ForgetNodeArgs :=
    ⟨env.mode, env.q, v, env.varsPtr, env.varsLen, env.descBase + 4 * (cur - 1),
      env.descBase + 4 * cur⟩
  obtain ⟨hv_fg, hfr_fg, hframe_fg, hdesc_fg, hc_fg⟩ :=
    forgetNodeProg_spec (w := w) inst.counting fgArgs hq rfl hvars₁ rfl
      hfit_bag_el hdesc_ch hdCur_hi hFlo₁ hs₁_peak hfit_cap
  have htree_lt : env.treePtr + 4 * cur + 3 < s₁.frontier := by
    have := hroot₁.1; simp only [List.length_cons, List.length_nil] at this; omega
  have hfit_vars : Fits w (env.varsPtr + env.varsLen) :=
    hfit_total.of_le (by dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *; omega)
  have ht2_ne0 : s₁.mem (env.treePtr + 4 * cur) ≠ 0 := by omega
  have ht2_ne1 : s₁.mem (env.treePtr + 4 * cur) ≠ 1 := by omega
  have hsafe_root : nodeStepSafe w (env, cur) s₁ :=
    ⟨hfit_4, hfit_tree.of_le (by simp only [NiceTree.size_forget] at hsz; omega),
      hfit_total.of_le (by dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *; omega),
      hfit_total.of_le (by dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *; omega),
      Or.inr (Or.inr (Or.inl ⟨htag2, hq, hfit_q, hfit_vars,
        hfit_total.of_le (by
          rw [hch1_eq]; dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *; omega),
        F_lo, inst.counting, child, inst.constraints, inst.vars,
        rfl, hfit_bag_el, by rw [hch1_eq]; exact hdesc_ch, hFlo₁,
        hfit_cPow, by rw [harg_v]; exact hs₁_peak, by rw [harg_v]; exact hfit_cap⟩))⟩
  have hr_s (x : ℕ) : (Memory.spec 0).clientState s₁ (Memory.read x) = s₁ := rfl
  have hr_r (x : ℕ) : (Memory.spec 0).clientResult s₁ (Memory.read x) = s₁.mem x := rfl
  have hst_root : (Memory.spec 0).clientState s₁ (nodeStep (env, cur)) =
      (Memory.spec 0).clientState s₁ (forgetNodeProg fgArgs) := by
    unfold nodeStep; dsimp only
    iterate 4 rw [StateTransitionSpec.clientState_bind, hr_s, hr_r]
    rw [ite_eq_right ht2_ne0, ite_eq_right ht2_ne1, ite_eq_left htag2,
      harg_v, hch1_eq, StateTransitionSpec.clientState_bind]
    rfl
  have hres_root : (Memory.spec 0).clientResult s₁ (nodeStep (env, cur)) = cur + 1 := by
    unfold nodeStep; dsimp only
    iterate 4 rw [StateTransitionSpec.clientResult_bind, hr_s, hr_r]
    rw [ite_eq_right ht2_ne0, ite_eq_right ht2_ne1, ite_eq_left htag2,
      StateTransitionSpec.clientResult_bind]
    rfl
  have hv_root : (Memory.spec w).ValidHistory s₁
      ((Memory.spec w).clientHistory s₁ (nodeStep (env, cur))) := by
    have hlt0 : env.treePtr + 4 * cur < s₁.frontier := lt_of_le_of_lt (by omega) htree_lt
    have hlt1 : env.treePtr + 4 * cur + 1 < s₁.frontier := lt_of_le_of_lt (by omega) htree_lt
    have hlt2 : env.treePtr + 4 * cur + 2 < s₁.frontier := lt_of_le_of_lt (by omega) htree_lt
    unfold nodeStep; dsimp only
    refine validHistory_read_bind hlt0 ?_
    refine validHistory_read_bind hlt1 ?_
    refine validHistory_read_bind hlt2 ?_
    refine validHistory_read_bind htree_lt ?_
    rw [ite_eq_right ht2_ne0, ite_eq_right ht2_ne1, ite_eq_left htag2,
      harg_v, hch1_eq]
    exact validHistory_bind_step hv_fg (validHistory_pure w _ _)
  have hcost_root : memoryCost (nodeStep (env, cur)) s₁ ≤ perCost := by
    unfold nodeStep; dsimp only
    iterate 4 rw [memoryCost_bind', memoryCost_read, hr_s, hr_r]
    rw [ite_eq_right ht2_ne0, ite_eq_right ht2_ne1, ite_eq_left htag2,
      harg_v, hch1_eq, memoryCost_bind', memoryCost_pure, Nat.add_zero]
    have hfg_mul :
        inst.domainSize ^ LB.length *
            (inst.domainSize * ((bagList child).length * (LB.length + 1) + 1) + 1) ≤
          inst.domainSize ^ E * (E ^ 2 + 2) := by
      calc inst.domainSize ^ LB.length *
            (inst.domainSize * ((bagList child).length * (LB.length + 1) + 1) + 1)
          = inst.domainSize ^ (LB.length + 1) *
              ((bagList child).length * (LB.length + 1) + 1) +
              inst.domainSize ^ LB.length := by
            rw [Nat.pow_succ]; ring
        _ ≤ inst.domainSize ^ E * (E * E + 1) + inst.domainSize ^ E := by
            refine Nat.add_le_add (Nat.mul_le_mul hpow_LB1_le ?_) hpow_LB_le
            exact Nat.add_le_add_right (Nat.mul_le_mul hcbag_len_le hLB_succ_le) 1
        _ = inst.domainSize ^ E * (E ^ 2 + 2) := by ring
    have h2_pow : 2 ≤ 2 * inst.domainSize ^ E := by
      dsimp only [E] at hpow_ge1 ⊢; omega
    have hfg_sum :
        18 + 3 * (bagList child).length + LB.length +
            inst.domainSize ^ LB.length *
              (inst.domainSize * ((bagList child).length * (LB.length + 1) + 1) + 1) ≤
          16 + 4 * E + inst.domainSize ^ E * (E ^ 2 + E + 4) := by
      have hqE_mul : inst.domainSize ^ E * (E ^ 2 + 2) + 2 * inst.domainSize ^ E ≤
          inst.domainSize ^ E * (E ^ 2 + E + 4) := by
        have : inst.domainSize ^ E * (E ^ 2 + 2) + 2 * inst.domainSize ^ E =
            inst.domainSize ^ E * (E ^ 2 + 4) := by ring
        rw [this]
        exact Nat.mul_le_mul_left _ (by omega)
      omega
    have hmul_c := hc_ge (E ^ 2 + E + 4) (by dsimp only [E]; omega)
    dsimp only [fgArgs, env, subtreeEnv, LB, perCost, E] at hc_fg hfg_sum hmul_c ⊢
    omega
  have hit_root_st : (Memory.spec 0).clientState s₁ (iterate nodeStep env 1 cur) =
      (Memory.spec 0).clientState s₁ (nodeStep (env, cur)) := by
    have hpure_st : ∀ t (x : ℕ), (Memory.spec 0).clientState t (pure x) = t := fun _ _ => rfl
    change (Memory.spec 0).clientState s₁ (nodeStep (env, cur) >>= iterate nodeStep env 0) = _
    rw [StateTransitionSpec.clientState_bind]
    exact hpure_st _ _
  have hit_root_res : (Memory.spec 0).clientResult s₁ (iterate nodeStep env 1 cur) = cur + 1 := by
    have hpure_res : ∀ t (x : ℕ), (Memory.spec 0).clientResult t (pure x) = x := fun _ _ => rfl
    change (Memory.spec 0).clientResult s₁ (nodeStep (env, cur) >>= iterate nodeStep env 0) = _
    rw [StateTransitionSpec.clientResult_bind, hres_root]
    exact hpure_res _ _
  have hv_it_root : (Memory.spec w).ValidHistory s₁
      ((Memory.spec w).clientHistory s₁ (iterate nodeStep env 1 cur)) := by
    change (Memory.spec w).ValidHistory s₁
      ((Memory.spec w).clientHistory s₁ (nodeStep (env, cur) >>= iterate nodeStep env 0))
    exact validHistory_bind_step hv_root (validHistory_pure w _ _)
  have hc_it_root : memoryCost (iterate nodeStep env 1 cur) s₁ ≤ perCost := by
    change memoryCost (nodeStep (env, cur) >>= iterate nodeStep env 0) s₁ ≤ _
    rw [memoryCost_bind', show memoryCost (iterate nodeStep env 0 _) _ = 0 from rfl, Nat.add_zero]
    exact hcost_root
  simp only [NiceTree.size_forget]
  refine ⟨iterationSafe_add nodeStep nodeStepSafe w env child.size 1 offset s hsafe_ch
      (by rw [hres_ch, hs₁_def]; exact ⟨hsafe_root, trivial⟩),
    validHistory_iterate_add nodeStep env child.size 1 offset s hv_ch
      (by dsimp only [cur]; rw [hres_ch, hs₁_def]; exact hv_it_root),
    by rw [clientResult_iterate_add, hres_ch, hs₁_def]; exact hit_root_res,
    ?_, ?_, ?_, ?_⟩
  · rw [clientState_iterate_add, hres_ch, hs₁_def, hit_root_st, hst_root]
    have hfr_le : LB.length + inst.domainSize ^ LB.length ≤ perSpace := by
      dsimp only [perSpace]; omega
    have hmul_bud : (child.size + 1) * perSpace = child.size * perSpace + perSpace := by ring
    change s₁.frontier ≤ s.frontier + child.size * perSpace at hfr_ch
    change _ ≤ s.frontier + (child.size + 1) * perSpace
    dsimp only [fgArgs, env, subtreeEnv, LB] at hfr_fg hfr_le hfr_ch ⊢
    omega
  · rw [clientState_iterate_add, hres_ch, hs₁_def]
    change FrameOutsideRange (env.descBase + 4 * offset)
      (env.descBase + 4 * (offset + (child.size + 1))) s
      ((Memory.spec 0).clientState s₁ (iterate nodeStep env 1 cur))
    rw [hit_root_st, hst_root]
    have hfr_fg' : FrameOutsideRange (env.descBase + 4 * cur)
        (env.descBase + 4 * (cur + 1)) s₁
        ((Memory.spec 0).clientState s₁ (forgetNodeProg fgArgs)) := by
      dsimp only [fgArgs] at hframe_fg
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using hframe_fg
    simpa only [cur, env, subtreeEnv, Nat.add_assoc] using
      FrameOutsideRange.trans
        (hframe_ch.mono_range le_rfl (by dsimp only [cur, env, subtreeEnv]; omega))
        (hfr_fg'.mono_range (by dsimp only [cur, env, subtreeEnv]; omega) le_rfl)
  · rw [clientState_iterate_add, hres_ch, hs₁_def]
    change NodeDescAt F_lo inst.counting inst.domainSize inst.constraints inst.vars
      (.forget v child) (env.descBase + 4 * (offset + (child.size + 1) - 1))
      ((Memory.spec 0).clientState s₁ (iterate nodeStep env 1 cur))
    rw [hit_root_st, hst_root, show offset + (child.size + 1) - 1 = cur from by omega]
    exact hdesc_fg
  · rw [memoryCost_iterate_add, hres_ch, hs₁_def]
    change memoryCost (iterate nodeStep env child.size offset) s +
        memoryCost (iterate nodeStep env 1 cur) s₁ ≤ (child.size + 1) * perCost
    have : (child.size + 1) * perCost = child.size * perCost + perCost := by ring
    change memoryCost (iterate nodeStep env child.size offset) s ≤ child.size * perCost at hc_ch
    omega

private theorem nodeStep_join_branch {w : ℕ} (env : NodeEnv) (cur ch1 ch2 : ℕ)
    (s : Memory.State)
    (htree_lt : env.treePtr + 4 * cur + 3 < s.frontier)
    (hne0 : s.mem (env.treePtr + 4 * cur) ≠ 0)
    (hne1 : s.mem (env.treePtr + 4 * cur) ≠ 1)
    (hne2 : s.mem (env.treePtr + 4 * cur) ≠ 2)
    (hch1_eq : s.mem (env.treePtr + 4 * cur + 2) = ch1)
    (hch2_eq : s.mem (env.treePtr + 4 * cur + 3) = ch2)
    (jnArgs : JoinNodeArgs)
    (hjn : jnArgs = ⟨env.q, env.descBase + 4 * ch1, env.descBase + 4 * ch2,
      env.descBase + 4 * cur⟩)
    (hv_jn : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (joinNodeProg jnArgs))) :
    (Memory.spec 0).clientState s (iterate nodeStep env 1 cur) =
      (Memory.spec 0).clientState s (joinNodeProg jnArgs) ∧
    (Memory.spec 0).clientResult s (iterate nodeStep env 1 cur) = cur + 1 ∧
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (iterate nodeStep env 1 cur)) ∧
    memoryCost (iterate nodeStep env 1 cur) s ≤ 4 + memoryCost (joinNodeProg jnArgs) s := by
  subst hjn
  have hr_s (x : ℕ) : (Memory.spec 0).clientState s (Memory.read x) = s := rfl
  have hr_r (x : ℕ) : (Memory.spec 0).clientResult s (Memory.read x) = s.mem x := rfl
  have hlt0 : env.treePtr + 4 * cur < s.frontier := lt_of_le_of_lt (by omega) htree_lt
  have hlt1 : env.treePtr + 4 * cur + 1 < s.frontier := lt_of_le_of_lt (by omega) htree_lt
  have hlt2 : env.treePtr + 4 * cur + 2 < s.frontier := lt_of_le_of_lt (by omega) htree_lt
  have hst : (Memory.spec 0).clientState s (nodeStep (env, cur)) =
      (Memory.spec 0).clientState s (joinNodeProg ⟨env.q, env.descBase + 4 * ch1,
        env.descBase + 4 * ch2, env.descBase + 4 * cur⟩) := by
    unfold nodeStep; dsimp only
    iterate 4 rw [StateTransitionSpec.clientState_bind, hr_s, hr_r]
    rw [ite_eq_right hne0, ite_eq_right hne1, ite_eq_right hne2,
      hch1_eq, hch2_eq, StateTransitionSpec.clientState_bind]
    rfl
  have hres : (Memory.spec 0).clientResult s (nodeStep (env, cur)) = cur + 1 := by
    unfold nodeStep; dsimp only
    iterate 4 rw [StateTransitionSpec.clientResult_bind, hr_s, hr_r]
    rw [ite_eq_right hne0, ite_eq_right hne1, ite_eq_right hne2,
      StateTransitionSpec.clientResult_bind]
    rfl
  have hv : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (nodeStep (env, cur))) := by
    unfold nodeStep; dsimp only
    refine validHistory_read_bind hlt0 ?_
    refine validHistory_read_bind hlt1 ?_
    refine validHistory_read_bind hlt2 ?_
    refine validHistory_read_bind htree_lt ?_
    rw [ite_eq_right hne0, ite_eq_right hne1, ite_eq_right hne2, hch1_eq, hch2_eq]
    exact validHistory_bind_step hv_jn (validHistory_pure w _ _)
  have hcost : memoryCost (nodeStep (env, cur)) s ≤
      4 + memoryCost (joinNodeProg ⟨env.q, env.descBase + 4 * ch1,
        env.descBase + 4 * ch2, env.descBase + 4 * cur⟩) s := by
    unfold nodeStep; dsimp only
    iterate 4 rw [memoryCost_bind', memoryCost_read, hr_s, hr_r]
    rw [ite_eq_right hne0, ite_eq_right hne1, ite_eq_right hne2,
      hch1_eq, hch2_eq, memoryCost_bind', memoryCost_pure, Nat.add_zero]
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (Memory.spec 0).clientState s (nodeStep (env, cur) >>= iterate nodeStep env 0) = _
    rw [StateTransitionSpec.clientState_bind]; exact hst
  · change (Memory.spec 0).clientResult s (nodeStep (env, cur) >>= iterate nodeStep env 0) = _
    rw [StateTransitionSpec.clientResult_bind, hres]; rfl
  · change (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (nodeStep (env, cur) >>= iterate nodeStep env 0))
    exact validHistory_bind_step hv (validHistory_pure w _ _)
  · change memoryCost (nodeStep (env, cur) >>= iterate nodeStep env 0) s ≤ _
    rw [memoryCost_bind', show memoryCost (iterate nodeStep env 0 _) _ = 0 from rfl, Nat.add_zero]
    exact hcost

private theorem subtree_join_step {w : ℕ} (inst : TreeCSPInstance) (hw : Fits w inst.wordBound)
    (left right : NiceTree ℕ) (offset mid cur : ℕ) (s₂ : Memory.State)
    (hsz : offset + (NiceTree.join left right).size ≤ inst.tree.size)
    (hexp_l : maxTableExp left ≤ maxTableExp inst.tree)
    (hexp_r : maxTableExp right ≤ maxTableExp inst.tree)
    (hmid : mid = offset + left.size)
    (hcur : cur = mid + right.size)
    (hFlo₂ : (subtreeEnv inst).descBase + 4 * inst.tree.size ≤ s₂.frontier)
    (hfr_bound : s₂.frontier + inst.domainSize ^ (bagList left).length ≤
      (subtreeEnv inst).descBase + 4 * inst.tree.size +
        inst.tree.size * (maxTableExp inst.tree + 2 + inst.domainSize ^ maxTableExp inst.tree))
    (hroot₂ : HoldsIn ((subtreeEnv inst).treePtr + 4 * cur) [3, 0, mid - 1, cur - 1] s₂)
    (hdesc_l₂ : NodeDescAt ((subtreeEnv inst).descBase + 4 * inst.tree.size)
      inst.counting inst.domainSize inst.constraints inst.vars left
      ((subtreeEnv inst).descBase + 4 * (mid - 1)) s₂)
    (hdesc_r : NodeDescAt ((subtreeEnv inst).descBase + 4 * inst.tree.size)
      inst.counting inst.domainSize inst.constraints inst.vars right
      ((subtreeEnv inst).descBase + 4 * (cur - 1)) s₂) :
    nodeStepSafe w (subtreeEnv inst, cur) s₂ ∧
    (Memory.spec w).ValidHistory s₂
      ((Memory.spec w).clientHistory s₂ (iterate nodeStep (subtreeEnv inst) 1 cur)) ∧
    (Memory.spec 0).clientResult s₂ (iterate nodeStep (subtreeEnv inst) 1 cur) = cur + 1 ∧
    ((Memory.spec 0).clientState s₂ (iterate nodeStep (subtreeEnv inst) 1 cur)).frontier ≤
      s₂.frontier + inst.domainSize ^ (bagList left).length ∧
    FrameOutsideRange ((subtreeEnv inst).descBase + 4 * cur)
      ((subtreeEnv inst).descBase + 4 * (cur + 1)) s₂
      ((Memory.spec 0).clientState s₂ (iterate nodeStep (subtreeEnv inst) 1 cur)) ∧
    NodeDescAt ((subtreeEnv inst).descBase + 4 * inst.tree.size)
      inst.counting inst.domainSize inst.constraints inst.vars (.join left right)
      ((subtreeEnv inst).descBase + 4 * cur)
      ((Memory.spec 0).clientState s₂ (iterate nodeStep (subtreeEnv inst) 1 cur)) ∧
    memoryCost (iterate nodeStep (subtreeEnv inst) 1 cur) s₂ ≤
      16 + 4 * maxTableExp inst.tree + inst.vars.length +
        inst.domainSize ^ maxTableExp inst.tree *
          (maxTableExp inst.tree ^ 2 + maxTableExp inst.tree + 4 +
            3 * inst.constraints.length + inst.totalArity * (2 * maxTableExp inst.tree + 3)) := by
  let env := subtreeEnv inst
  let F_lo := env.descBase + 4 * inst.tree.size
  have hq : 0 < inst.domainSize := inst.domainSize_pos
  let E := maxTableExp inst.tree
  let perSpace := E + 2 + inst.domainSize ^ E
  let perCost := 16 + 4 * E + inst.vars.length + inst.domainSize ^ E *
    (E ^ 2 + E + 4 + 3 * inst.constraints.length + inst.totalArity * (2 * E + 3))
  obtain ⟨_, hfit_4, hfit_q, hfit_tree, hfit_total, _, _, _,
    _, hperSpace_le_total, hc_ge, _⟩ := subtree_setup inst hw
  have hsz_l_pos := niceTree_size_pos left
  have hsz_r_pos := niceTree_size_pos right
  have hr_root := hroot₂
  change HoldsIn (env.treePtr + 4 * cur) [3, 0, mid - 1, cur - 1] s₂ at hr_root
  rw [HoldsIn.cons_iff, HoldsIn.cons_iff, HoldsIn.cons_iff, HoldsIn.cons_iff] at hr_root
  obtain ⟨_, htag3, _, _, _, hch1_eq, _, hch2_eq, _⟩ := hr_root
  have hdCur_hi : env.descBase + 4 * cur + 4 ≤ F_lo := by
    simp only [NiceTree.size_join] at hsz; dsimp only [F_lo, env, subtreeEnv] at *; omega
  have hllen_le : (bagList left).length ≤ E :=
    (bagList_length_le_maxTableExp left).trans hexp_l
  have hrlen_le : (bagList right).length ≤ E :=
    (bagList_length_le_maxTableExp right).trans hexp_r
  have hpow_l_le : inst.domainSize ^ (bagList left).length ≤ inst.domainSize ^ E :=
    Nat.pow_le_pow_right hq hllen_le
  have hfit_rPow : Fits w (inst.domainSize ^ (bagList right).length) := by
    have hpow_r_le : inst.domainSize ^ (bagList right).length ≤ inst.domainSize ^ E :=
      Nat.pow_le_pow_right hq hrlen_le
    have hr_le_sp : inst.domainSize ^ (bagList right).length ≤ perSpace := by
      dsimp only [perSpace]; omega
    exact hfit_total.of_le (le_trans hr_le_sp (le_trans hperSpace_le_total (Nat.le_add_left _ _)))
  have hs₂_peak : Fits w (s₂.frontier + inst.domainSize ^ (bagList left).length) :=
    hfit_total.of_le hfr_bound
  have hfit_cap : Fits w
      (if inst.counting then inst.domainSize ^ (NiceTree.join left right).size else 1) :=
    hw.of_le (by
      have hsz_le : (NiceTree.join left right).size ≤ inst.tree.size :=
        Nat.le_trans (Nat.le_add_left _ offset) hsz
      have hpow_s := Nat.pow_le_pow_right hq hsz_le
      unfold TreeCSPInstance.wordBound TreeCSPInstance.maxEntryBound
      dsimp only
      by_cases hcnt : inst.counting = true
      · rw [ite_eq_left hcnt, ite_eq_left hcnt]; omega
      · rw [ite_eq_right hcnt, ite_eq_right hcnt]; omega)
  let jnArgs : JoinNodeArgs :=
    ⟨env.q, env.descBase + 4 * (mid - 1), env.descBase + 4 * (cur - 1), env.descBase + 4 * cur⟩
  obtain ⟨hv_jn, hfr_jn, hframe_jn, hdesc_jn, hc_jn⟩ :=
    joinNodeProg_spec (w := w) inst.counting jnArgs hq hdesc_l₂ hdesc_r hdCur_hi hFlo₂
      hs₂_peak hfit_cap
  have htree_lt : env.treePtr + 4 * cur + 3 < s₂.frontier := by
    have := hroot₂.1; simp only [List.length_cons, List.length_nil] at this; omega
  have hne0 : s₂.mem (env.treePtr + 4 * cur) ≠ 0 := by omega
  have hne1 : s₂.mem (env.treePtr + 4 * cur) ≠ 1 := by omega
  have hne2 : s₂.mem (env.treePtr + 4 * cur) ≠ 2 := by omega
  have hsafe_root : nodeStepSafe w (env, cur) s₂ :=
    ⟨hfit_4, hfit_tree.of_le (by simp only [NiceTree.size_join] at hsz; omega),
      hfit_total.of_le (by dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *; omega),
      hfit_total.of_le (by dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *; omega),
      Or.inr (Or.inr (Or.inr ⟨hne0, hne1, hne2, hq, hfit_q,
        hfit_total.of_le (by
          rw [hch1_eq]; dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *; omega),
        hfit_total.of_le (by
          rw [hch2_eq]; dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *; omega),
        F_lo, inst.counting, left, right, inst.constraints, inst.vars,
        by rw [hch1_eq]; exact hdesc_l₂, by rw [hch2_eq]; exact hdesc_r,
        hfit_rPow, hs₂_peak, hfit_cap⟩))⟩
  obtain ⟨hit_root_st, hit_root_res, hv_it_root, hcost_br⟩ :=
    nodeStep_join_branch env cur (mid - 1) (cur - 1) s₂ htree_lt hne0 hne1 hne2
      hch1_eq hch2_eq jnArgs rfl hv_jn
  have hc_it_root : memoryCost (iterate nodeStep env 1 cur) s₂ ≤ perCost := by
    have hjn_mul :
        inst.domainSize ^ (bagList left).length *
            ((bagList right).length * ((bagList left).length + 1) + 3) ≤
          inst.domainSize ^ E * (E ^ 2 + E + 4) := by
      refine Nat.mul_le_mul hpow_l_le ?_
      have hmul_lr : (bagList right).length * ((bagList left).length + 1) ≤ E * (E + 1) :=
        Nat.mul_le_mul hrlen_le (Nat.add_le_add_right hllen_le 1)
      have hsq : E * (E + 1) = E ^ 2 + E := by ring
      omega
    have hmul_c := hc_ge (E ^ 2 + E + 4) (by dsimp only [E]; omega)
    dsimp only [jnArgs, env, subtreeEnv, perCost, E] at hc_jn hcost_br hjn_mul hmul_c ⊢
    omega
  have hfr_jn' : FrameOutsideRange (env.descBase + 4 * cur) (env.descBase + 4 * (cur + 1)) s₂
      ((Memory.spec 0).clientState s₂ (joinNodeProg jnArgs)) := by
    dsimp only [jnArgs] at hframe_jn
    simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using hframe_jn
  refine ⟨hsafe_root, hv_it_root, hit_root_res, ?_, ?_, ?_, hc_it_root⟩
  · rw [hit_root_st]; exact hfr_jn
  · rw [hit_root_st]; exact hfr_jn'
  · rw [hit_root_st]; exact hdesc_jn

private theorem subtree_join {w : ℕ} (inst : TreeCSPInstance) (hw : Fits w inst.wordBound)
    (left right : NiceTree ℕ)
    (ihl : ∀ offset s, SubtreeFullSpec w inst left offset s)
    (ihr : ∀ offset s, SubtreeFullSpec w inst right offset s) :
    ∀ offset s, SubtreeFullSpec w inst (.join left right) offset s := by
  let env := subtreeEnv inst
  let F_lo := env.descBase + 4 * inst.tree.size
  have hq : 0 < inst.domainSize := inst.domainSize_pos
  let E := maxTableExp inst.tree
  let perSpace := E + 2 + inst.domainSize ^ E
  let perCost := 16 + 4 * E + inst.vars.length + inst.domainSize ^ E *
    (E ^ 2 + E + 4 + 3 * inst.constraints.length + inst.totalArity * (2 * E + 3))
  obtain ⟨_, _, _, _, _, _, hvars_lt_desc, hcons_lt_desc, _, _, _, _⟩ := subtree_setup inst hw
  intro offset s hsz hexp hmv hwf hs_fr hfit_bud hvars htree hcons
  have hsz_l_pos := niceTree_size_pos left
  have hsz_r_pos := niceTree_size_pos right
  have hsz_l : offset + left.size ≤ inst.tree.size := by
    simp only [NiceTree.size_join] at hsz; omega
  have hsz_r : (offset + left.size) + right.size ≤ inst.tree.size := by
    simp only [NiceTree.size_join] at hsz; omega
  have hexp_l : maxTableExp left ≤ E := (maxTableExp_le_join_left left right).trans hexp
  have hexp_r : maxTableExp right ≤ E := (maxTableExp_le_join_right left right).trans hexp
  have hmv_l : maxTreeVert left ≤ maxTreeVert inst.tree :=
    (maxTreeVert_le_join_left left right).trans hmv
  have hmv_r : maxTreeVert right ≤ maxTreeVert inst.tree :=
    (maxTreeVert_le_join_right left right).trans hmv
  have hfit_bud_l : s.frontier + left.size * perSpace ≤ F_lo + inst.tree.size * perSpace := by
    have hmul_le : left.size * perSpace ≤ (NiceTree.join left right).size * perSpace :=
      Nat.mul_le_mul_right _ (by simp [NiceTree.size_join]; omega)
    exact le_trans (Nat.add_le_add_left hmul_le _) hfit_bud
  have htree_app := htree
  rw [encodeNiceTreeAux, List.append_assoc, HoldsIn.append_iff, length_encodeNiceTreeAux,
    HoldsIn.append_iff, length_encodeNiceTreeAux] at htree_app
  obtain ⟨htree_l, htree_r0, hroot_hold⟩ := htree_app
  obtain ⟨hsafe_l, hv_l, hres_l, hfr_l, hframe_l, hdesc_l, hc_l⟩ :=
    ihl offset s hsz_l hexp_l hmv_l hwf hs_fr hfit_bud_l hvars htree_l hcons
  let mid := offset + left.size
  obtain ⟨s₁, hs₁_def⟩ : ∃ s₁,
      (Memory.spec 0).clientState s (iterate nodeStep env left.size offset) = s₁ := ⟨_, rfl⟩
  rw [hs₁_def] at hfr_l hframe_l hdesc_l
  have hwf₁ : Memory.WellFormed w s₁ := by
    rw [← hs₁_def]
    exact wellFormed_clientState hwf hv_l
  have hFlo₁ : F_lo ≤ s₁.frontier := hs_fr.trans hframe_l.1
  have hout_vars₁ : env.varsPtr + env.varsLen ≤ env.descBase + 4 * offset :=
    hvars_lt_desc.trans (Nat.le_add_right _ _)
  have hout_cons₁ : env.consRawPtr + (inst.constraints.flatMap ConstraintTable.encode).length ≤
      env.descBase + 4 * offset :=
    hcons_lt_desc.trans (Nat.le_add_right _ _)
  have hout_tr₁ : env.treePtr + 4 * mid + (encodeNiceTreeAux mid right).length ≤
      env.descBase + 4 * offset := by
    rw [length_encodeNiceTreeAux]
    simp only [NiceTree.size_join] at hsz
    dsimp only [mid, env, subtreeEnv] at *
    omega
  have hout_root₁ : env.treePtr + 4 * (mid + right.size) +
      [3, 0, mid - 1, mid + right.size - 1].length ≤ env.descBase + 4 * offset := by
    simp only [List.length_cons, List.length_nil]
    simp only [NiceTree.size_join] at hsz
    dsimp only [mid, env, subtreeEnv] at *
    omega
  have hvars₁ : HoldsIn env.varsPtr inst.vars s₁ :=
    hvars.frame_outsideRange (.inl hout_vars₁) hframe_l
  have hcons₁ : HoldsIn env.consRawPtr (inst.constraints.flatMap ConstraintTable.encode) s₁ :=
    hcons.frame_outsideRange (.inl hout_cons₁) hframe_l
  have htree_r₁ : HoldsIn (env.treePtr + 4 * mid) (encodeNiceTreeAux mid right) s₁ := by
    rw [show env.treePtr + 4 * offset + 4 * left.size = env.treePtr + 4 * mid from by
      dsimp only [mid]; omega] at htree_r0
    exact htree_r0.frame_outsideRange (.inl hout_tr₁) hframe_l
  have hroot₁ : HoldsIn (env.treePtr + 4 * (mid + right.size))
      [3, 0, mid - 1, mid + right.size - 1] s₁ := by
    rw [show env.treePtr + 4 * offset + 4 * left.size + 4 * right.size =
      env.treePtr + 4 * (mid + right.size) from by dsimp only [mid]; omega] at hroot_hold
    exact hroot_hold.frame_outsideRange (.inl hout_root₁) hframe_l
  have hfit_bud_r : s₁.frontier + right.size * perSpace ≤ F_lo + inst.tree.size * perSpace := by
    change s.frontier + (NiceTree.join left right).size * perSpace ≤
      F_lo + inst.tree.size * perSpace at hfit_bud
    simp only [NiceTree.size_join] at hfit_bud
    have hmul_sum : (left.size + right.size + 1) * perSpace =
        left.size * perSpace + right.size * perSpace + perSpace := by ring
    change s₁.frontier ≤ s.frontier + left.size * perSpace at hfr_l
    omega
  obtain ⟨hsafe_r, hv_r, hres_r, hfr_r, hframe_r, hdesc_r, hc_r⟩ :=
    ihr mid s₁ hsz_r hexp_r hmv_r hwf₁ hFlo₁ hfit_bud_r hvars₁ htree_r₁ hcons₁
  let cur := mid + right.size
  obtain ⟨s₂, hs₂_def⟩ : ∃ s₂,
      (Memory.spec 0).clientState s₁ (iterate nodeStep env right.size mid) = s₂ := ⟨_, rfl⟩
  rw [hs₂_def] at hfr_r hframe_r hdesc_r
  have hFlo₂ : F_lo ≤ s₂.frontier := hFlo₁.trans hframe_r.1
  have hout_root₂ : env.treePtr + 4 * cur + [3, 0, mid - 1, cur - 1].length ≤
      env.descBase + 4 * mid := by
    simp only [List.length_cons, List.length_nil]
    simp only [NiceTree.size_join] at hsz
    dsimp only [cur, mid, env, subtreeEnv] at *
    omega
  have hroot₂ : HoldsIn (env.treePtr + 4 * cur) [3, 0, mid - 1, cur - 1] s₂ :=
    hroot₁.frame_outsideRange (.inl hout_root₂) hframe_r
  have hdesc_l₂ : NodeDescAt F_lo inst.counting inst.domainSize inst.constraints inst.vars left
      (env.descBase + 4 * (mid - 1)) s₂ :=
    hdesc_l.frame_outsideRange (.inl (by dsimp only [mid]; omega))
      (by
        dsimp only [F_lo, mid, env, subtreeEnv] at *
        simp only [NiceTree.size_join] at hsz; omega)
      hframe_r
  have hllen_le : (bagList left).length ≤ E :=
    (bagList_length_le_maxTableExp left).trans hexp_l
  have hpow_l_le : inst.domainSize ^ (bagList left).length ≤ inst.domainSize ^ E :=
    Nat.pow_le_pow_right hq hllen_le
  have hfr_bound : s₂.frontier + inst.domainSize ^ (bagList left).length ≤
      F_lo + inst.tree.size * perSpace := by
    change s.frontier + (NiceTree.join left right).size * perSpace ≤
      F_lo + inst.tree.size * perSpace at hfit_bud
    simp only [NiceTree.size_join] at hfit_bud
    have hmul_sum : (left.size + right.size + 1) * perSpace =
        left.size * perSpace + right.size * perSpace + perSpace := by ring
    have : inst.domainSize ^ (bagList left).length ≤ perSpace := by
      dsimp only [perSpace]; omega
    change s₁.frontier ≤ s.frontier + left.size * perSpace at hfr_l
    change s₂.frontier ≤ s₁.frontier + right.size * perSpace at hfr_r
    omega
  obtain ⟨hsafe_root, hv_it_root, hit_root_res, hfr_root, hframe_root, hdesc_root, hc_it_root⟩ :=
    subtree_join_step inst hw left right offset mid cur s₂ hsz hexp_l hexp_r rfl rfl
      hFlo₂ hfr_bound hroot₂ hdesc_l₂ hdesc_r
  have hsafe_lr : iterationSafe nodeStep nodeStepSafe w env (left.size + right.size) offset s :=
    iterationSafe_add nodeStep nodeStepSafe w env left.size right.size offset s hsafe_l
      (by rw [hres_l, hs₁_def]; exact hsafe_r)
  have hv_lr : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (iterate nodeStep env (left.size + right.size) offset)) :=
    validHistory_iterate_add nodeStep env left.size right.size offset s hv_l
      (by dsimp only; rw [hs₁_def, hres_l]; exact hv_r)
  have hres_lr : (Memory.spec 0).clientResult s
      (iterate nodeStep env (left.size + right.size) offset) = cur := by
    rw [clientResult_iterate_add, hres_l, hs₁_def]; exact hres_r
  have hst_lr : (Memory.spec 0).clientState s
      (iterate nodeStep env (left.size + right.size) offset) = s₂ := by
    rw [clientState_iterate_add, hres_l, hs₁_def, hs₂_def]
  simp only [NiceTree.size_join]
  refine ⟨iterationSafe_add nodeStep nodeStepSafe w env (left.size + right.size) 1 offset s
      hsafe_lr (by
        rw [hst_lr, hres_lr, show env = subtreeEnv inst from rfl]
        exact ⟨hsafe_root, trivial⟩),
    validHistory_iterate_add nodeStep env (left.size + right.size) 1 offset s hv_lr
      (by
        dsimp only
        rw [hst_lr, hres_lr, show env = subtreeEnv inst from rfl]
        exact hv_it_root),
    by
      rw [clientResult_iterate_add, hres_lr, hst_lr, hit_root_res]
      dsimp only [cur, mid]
      omega,
    ?_, ?_, ?_, ?_⟩
  · rw [clientState_iterate_add, hres_lr, hst_lr]
    have hfr_le : inst.domainSize ^ (bagList left).length ≤ perSpace := by
      dsimp only [perSpace]; omega
    have hsum_sp : (left.size + right.size + 1) * perSpace =
        left.size * perSpace + right.size * perSpace + perSpace := by ring
    dsimp only [perSpace, E] at hfr_le hsum_sp
    omega
  · rw [clientState_iterate_add, hres_lr, hst_lr]
    change FrameOutsideRange (env.descBase + 4 * offset)
      (env.descBase + 4 * (offset + (left.size + right.size + 1))) s
      ((Memory.spec 0).clientState s₂ (iterate nodeStep env 1 cur))
    rw [show env = subtreeEnv inst from rfl]
    have hfr_lr : FrameOutsideRange ((subtreeEnv inst).descBase + 4 * offset)
        ((subtreeEnv inst).descBase + 4 * cur) s s₂ :=
      FrameOutsideRange.trans
        (hframe_l.mono_range le_rfl (by dsimp only [mid, cur, env, subtreeEnv]; omega))
        (hframe_r.mono_range (by dsimp only [mid, env, subtreeEnv]; omega) le_rfl)
    rw [show (subtreeEnv inst).descBase + 4 * (offset + (left.size + right.size + 1)) =
        (subtreeEnv inst).descBase + 4 * (cur + 1) from by dsimp only [cur, mid]; omega]
    exact FrameOutsideRange.trans
      (hfr_lr.mono_range le_rfl (by dsimp only [cur, mid]; omega))
      (hframe_root.mono_range (by dsimp only [cur, mid]; omega) le_rfl)
  · rw [clientState_iterate_add, hres_lr, hst_lr]
    rw [show offset + (left.size + right.size + 1) - 1 = cur from by dsimp only [cur, mid]; omega]
    exact hdesc_root
  · rw [memoryCost_iterate_add, hres_lr, hst_lr]
    have hs₁_def' : (Memory.spec 0).clientState s
        (iterate nodeStep (subtreeEnv inst) left.size offset) = s₁ := hs₁_def
    have hc_lr :
        memoryCost (iterate nodeStep (subtreeEnv inst) (left.size + right.size) offset) s =
          memoryCost (iterate nodeStep (subtreeEnv inst) left.size offset) s +
            memoryCost (iterate nodeStep (subtreeEnv inst) right.size mid) s₁ := by
      rw [memoryCost_iterate_add, hres_l, hs₁_def']
    rw [hc_lr]
    have hsum_c : (left.size + right.size + 1) * perCost =
        left.size * perCost + right.size * perCost + perCost := by ring
    dsimp only [perCost, E] at hc_it_root hsum_c ⊢
    omega

private theorem subtree_leaf {w : ℕ} (inst : TreeCSPInstance) (hw : Fits w inst.wordBound) :
    ∀ offset s, SubtreeFullSpec w inst .leaf offset s := by
  let env := subtreeEnv inst
  let F_lo := env.descBase + 4 * inst.tree.size
  have hq : 0 < inst.domainSize := inst.domainSize_pos
  let E := maxTableExp inst.tree
  let perSpace := E + 2 + inst.domainSize ^ E
  let perCost := 16 + 4 * E + inst.vars.length + inst.domainSize ^ E *
    (E ^ 2 + E + 4 + 3 * inst.constraints.length + inst.totalArity * (2 * E + 3))
  obtain ⟨hpow_ge1, hfit_4, hfit_q, hfit_tree, hfit_total, hcons_len_bound, _, _,
    _, _, hc_ge, _⟩ := subtree_setup inst hw
  have hfit_total' : Fits w (F_lo + inst.tree.size * perSpace) := hfit_total
  intro offset s hsz _ _ _ hs_fr hfit_bud _ htree hcons
  have ht_eq := htree
  rw [encodeNiceTreeAux, HoldsIn.cons_iff, HoldsIn.cons_iff, HoldsIn.cons_iff,
    HoldsIn.cons_iff] at ht_eq
  obtain ⟨_, htag0, _, _, _, _, _, _, _⟩ := ht_eq
  have hdCur_hi : env.descBase + 4 * offset + 4 ≤ F_lo := by
    simp only [NiceTree.size_leaf] at hsz; dsimp only [F_lo, env, subtreeEnv] at *; omega
  have hs_fr1 : Fits w (s.frontier + 1) := hfit_total'.of_le (by
    have : 1 ≤ perSpace := by dsimp only [perSpace]; omega
    change s.frontier + NiceTree.size .leaf * perSpace ≤
      F_lo + inst.tree.size * perSpace at hfit_bud
    simp only [NiceTree.size_leaf, Nat.one_mul] at hfit_bud
    omega)
  have htree_lt : env.treePtr + 4 * offset + 3 < s.frontier := by
    have := htree.1; simp only [length_encodeNiceTreeAux, NiceTree.size_leaf] at this
    dsimp only [env, subtreeEnv] at this ⊢; omega
  let leafArgs : LeafNodeArgs := ⟨env.consRawPtr, env.numCons, env.descBase + 4 * offset⟩
  obtain ⟨hv_lf, hfr_lf, hframe_lf, hdesc_lf, hc_lf⟩ :=
    leafNodeProg_spec (w := w) inst.counting hq leafArgs (vars := inst.vars) hcons rfl hdCur_hi
      hs_fr hs_fr1
  have hcons_fit : Fits w (env.consRawPtr +
      (inst.constraints.flatMap ConstraintTable.encode).length) :=
    hw.of_le (by
      rw [hcons_len_bound]; dsimp only [env, subtreeEnv]
      unfold TreeCSPInstance.wordBound; dsimp only; omega)
  have hsafe0 : nodeStepSafe w (env, offset) s := by
    refine ⟨hfit_4, hfit_tree.of_le (by simp only [NiceTree.size_leaf] at hsz; exact hsz),
      hfit_total.of_le (by dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *; omega),
      hfit_total.of_le (by dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *; omega),
      Or.inl ⟨htag0, inst.domainSize, inst.constraints, hq, rfl, hcons, hcons_fit⟩⟩
  have hr_s (x : ℕ) : (Memory.spec 0).clientState s (Memory.read x) = s := rfl
  have hr_r (x : ℕ) : (Memory.spec 0).clientResult s (Memory.read x) = s.mem x := rfl
  have hst1 : (Memory.spec 0).clientState s (nodeStep (env, offset)) =
      (Memory.spec 0).clientState s (leafNodeProg leafArgs) := by
    unfold nodeStep; dsimp only
    iterate 4 rw [StateTransitionSpec.clientState_bind, hr_s, hr_r]
    rw [ite_eq_left htag0, StateTransitionSpec.clientState_bind]
    rfl
  have hres1 : (Memory.spec 0).clientResult s (nodeStep (env, offset)) = offset + 1 := by
    unfold nodeStep; dsimp only
    iterate 4 rw [StateTransitionSpec.clientResult_bind, hr_s, hr_r]
    rw [ite_eq_left htag0, StateTransitionSpec.clientResult_bind]
    rfl
  have hv1 : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (nodeStep (env, offset))) := by
    unfold nodeStep; dsimp only
    refine validHistory_read_bind (by omega) ?_
    refine validHistory_read_bind (by omega) ?_
    refine validHistory_read_bind (by omega) ?_
    refine validHistory_read_bind (by omega) ?_
    rw [ite_eq_left htag0]
    exact validHistory_bind_step hv_lf (validHistory_pure w _ _)
  have hcost1 : memoryCost (nodeStep (env, offset)) s ≤ 1 * perCost := by
    unfold nodeStep; dsimp only
    iterate 4 rw [memoryCost_bind', memoryCost_read, hr_s, hr_r]
    rw [ite_eq_left htag0, memoryCost_bind', memoryCost_pure, Nat.add_zero]
    have hmul_nc : 3 * inst.constraints.length ≤
        inst.domainSize ^ E *
          (E ^ 2 + E + 4 + 3 * inst.constraints.length + inst.totalArity * (2 * E + 3)) :=
      (Nat.le_mul_of_pos_left _ hpow_ge1).trans
        (hc_ge (3 * inst.constraints.length) (by omega))
    dsimp only [leafArgs, env, subtreeEnv, perCost] at hc_lf ⊢
    omega
  have hfr1' : ((Memory.spec 0).clientState s (nodeStep (env, offset))).frontier ≤
      s.frontier + 1 * perSpace := by
    rw [hst1]
    exact hfr_lf.trans (by dsimp only [perSpace]; omega)
  have hit1 : (Memory.spec 0).clientState s (iterate nodeStep env 1 offset) =
      (Memory.spec 0).clientState s (nodeStep (env, offset)) := by
    change (Memory.spec 0).clientState s (nodeStep (env, offset) >>= iterate nodeStep env 0) = _
    rw [StateTransitionSpec.clientState_bind]; rfl
  have hres_it1 : (Memory.spec 0).clientResult s (iterate nodeStep env 1 offset) = offset + 1 := by
    change (Memory.spec 0).clientResult s (nodeStep (env, offset) >>= iterate nodeStep env 0) = _
    rw [StateTransitionSpec.clientResult_bind, hres1]; rfl
  have hv_it1 : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (iterate nodeStep env 1 offset)) := by
    change (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (nodeStep (env, offset) >>= iterate nodeStep env 0))
    exact validHistory_bind_step hv1 (validHistory_pure w _ _)
  have hc_it1 : memoryCost (iterate nodeStep env 1 offset) s ≤ 1 * perCost := by
    change memoryCost (nodeStep (env, offset) >>= iterate nodeStep env 0) s ≤ _
    rw [memoryCost_bind', show memoryCost (iterate nodeStep env 0 _) _ = 0 from rfl, Nat.add_zero]
    exact hcost1
  simp only [NiceTree.size_leaf]
  refine ⟨⟨hsafe0, trivial⟩, hv_it1, hres_it1, by rw [hit1]; exact hfr1', ?_, ?_, hc_it1⟩
  · rw [hit1, hst1]
    dsimp only [leafArgs, env, subtreeEnv] at hframe_lf ⊢
    simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using hframe_lf
  · rw [hit1, hst1, Nat.add_sub_cancel]
    exact hdesc_lf

private theorem subtree_introduce {w : ℕ} (inst : TreeCSPInstance) (hw : Fits w inst.wordBound)
    (v : ℕ) (child : NiceTree ℕ) (ih : ∀ offset s, SubtreeFullSpec w inst child offset s) :
    ∀ offset s, SubtreeFullSpec w inst (.introduce v child) offset s := by
  let env := subtreeEnv inst
  let F_lo := env.descBase + 4 * inst.tree.size
  have hq : 0 < inst.domainSize := inst.domainSize_pos
  let E := maxTableExp inst.tree
  let perSpace := E + 2 + inst.domainSize ^ E
  let perCost := 16 + 4 * E + inst.vars.length + inst.domainSize ^ E *
    (E ^ 2 + E + 4 + 3 * inst.constraints.length + inst.totalArity * (2 * E + 3))
  obtain ⟨_, hfit_4, hfit_q, hfit_tree, hfit_total, _, hvars_lt_desc, hcons_lt_desc,
    _, _, _, _⟩ := subtree_setup inst hw
  have hfit_total' : Fits w (F_lo + inst.tree.size * perSpace) := hfit_total
  intro offset s hsz hexp hmv hwf hs_fr hfit_bud hvars htree hcons
  have hsz_ch_pos := niceTree_size_pos child
  have hsz_ch : offset + child.size ≤ inst.tree.size := by
    simp only [NiceTree.size_introduce] at hsz; omega
  have hexp_ch : maxTableExp child ≤ E := (maxTableExp_le_introduce v child).trans hexp
  have hmv_ch : maxTreeVert child ≤ maxTreeVert inst.tree :=
    (maxTreeVert_le_introduce v child).trans hmv
  have hfit_bud_ch : s.frontier + child.size * perSpace ≤ F_lo + inst.tree.size * perSpace := by
    have hmul_le : child.size * perSpace ≤ (NiceTree.introduce v child).size * perSpace :=
      Nat.mul_le_mul_right _ (by simp [NiceTree.size_introduce])
    exact le_trans (Nat.add_le_add_left hmul_le _) hfit_bud
  have htree_app := htree
  rw [encodeNiceTreeAux, HoldsIn.append_iff, length_encodeNiceTreeAux] at htree_app
  obtain ⟨htree_ch, hroot_hold⟩ := htree_app
  obtain ⟨hsafe_ch, hv_ch, hres_ch, hfr_ch, hframe_ch, hdesc_ch, hc_ch⟩ :=
    ih offset s hsz_ch hexp_ch hmv_ch hwf hs_fr hfit_bud_ch hvars htree_ch hcons
  let cur := offset + child.size
  obtain ⟨s₁, hs₁_def⟩ :
      ∃ s₁, (Memory.spec 0).clientState s (iterate nodeStep env child.size offset) = s₁ := ⟨_, rfl⟩
  rw [hs₁_def] at hfr_ch hframe_ch hdesc_ch
  have hwf₁ : Memory.WellFormed w s₁ := hs₁_def ▸ wellFormed_clientState hwf hv_ch
  have hFlo₁ : F_lo ≤ s₁.frontier := hs_fr.trans hframe_ch.1
  have hout_vars : env.varsPtr + env.varsLen ≤ env.descBase + 4 * offset :=
    hvars_lt_desc.trans (Nat.le_add_right _ _)
  have hout_cons : env.consRawPtr + (inst.constraints.flatMap ConstraintTable.encode).length ≤
      env.descBase + 4 * offset :=
    hcons_lt_desc.trans (Nat.le_add_right _ _)
  have hout_root : env.treePtr + 4 * cur + [1, v, cur - 1, 0].length ≤
      env.descBase + 4 * offset := by
    simp only [List.length_cons, List.length_nil]
    change env.treePtr + 4 * (offset + child.size) + 4 ≤ env.descBase + 4 * offset
    simp only [NiceTree.size_introduce] at hsz
    dsimp only [env, subtreeEnv] at *
    omega
  have hvars₁ : HoldsIn env.varsPtr inst.vars s₁ :=
    hvars.frame_outsideRange (.inl hout_vars) hframe_ch
  have hcons₁ : HoldsIn env.consRawPtr (inst.constraints.flatMap ConstraintTable.encode) s₁ :=
    hcons.frame_outsideRange (.inl hout_cons) hframe_ch
  have hroot₁ : HoldsIn (env.treePtr + 4 * cur) [1, v, cur - 1, 0] s₁ := by
    rw [show env.treePtr + 4 * offset + 4 * child.size = env.treePtr + 4 * cur from by
      dsimp only [cur]; omega] at hroot_hold
    simpa only [cur, Nat.add_sub_cancel] using
      hroot_hold.frame_outsideRange (.inl hout_root) hframe_ch
  have hr_root := hroot₁
  rw [HoldsIn.cons_iff, HoldsIn.cons_iff, HoldsIn.cons_iff, HoldsIn.cons_iff] at hr_root
  obtain ⟨_, htag1, _, harg_v, _, hch1_eq, _, _, _⟩ := hr_root
  have hdCur_hi : env.descBase + 4 * cur + 4 ≤ F_lo := by
    simp only [NiceTree.size_introduce] at hsz; dsimp only [cur, F_lo, env, subtreeEnv] at *; omega
  have hbag_len_le : (v :: bagList child).length ≤ E := by
    have h1 : (v :: bagList child).length ≤ maxTableExp (.introduce v child) := le_max_left _ _
    exact h1.trans hexp
  have hcbag_len_le : (bagList child).length ≤ E :=
    (bagList_length_le_maxTableExp child).trans hexp_ch
  have hpow_le : inst.domainSize ^ (v :: bagList child).length ≤ inst.domainSize ^ E :=
    Nat.pow_le_pow_right hq hbag_len_le
  have hs₁_peak : Fits w (s₁.frontier +
      ((v :: bagList child).length + inst.domainSize ^ (v :: bagList child).length)) :=
    hfit_total'.of_le (by
      change s.frontier + (NiceTree.introduce v child).size * perSpace ≤
        F_lo + inst.tree.size * perSpace at hfit_bud
      simp only [NiceTree.size_introduce] at hfit_bud
      have hsp : (v :: bagList child).length + inst.domainSize ^ (v :: bagList child).length ≤
          perSpace := by dsimp only [perSpace]; omega
      have hmul_bud : (child.size + 1) * perSpace = child.size * perSpace + perSpace := by ring
      change s₁.frontier ≤ s.frontier + child.size * perSpace at hfr_ch
      omega)
  have hfit_v : Fits w v := hw.of_le (by
    have hv_m : v ≤ maxTreeVert (.introduce v child) := le_max_left _ _
    have hmvt : maxTreeVert inst.tree ≤ inst.maxVarLabel :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    unfold TreeCSPInstance.wordBound; dsimp only; omega)
  let introArgs : IntroNodeArgs :=
    ⟨env.q, v, env.consRawPtr, env.numCons, env.descBase + 4 * (cur - 1), env.descBase + 4 * cur⟩
  have hcons_le : env.consRawPtr +
      (inst.constraints.flatMap ConstraintTable.encode).length ≤ F_lo := by
    dsimp only [F_lo, env, subtreeEnv] at *; omega
  obtain ⟨hv_in, hfr_in, hframe_in, hdesc_in, hc_in⟩ :=
    introNodeProg_spec (w := w) inst.counting introArgs hq hwf₁ hfit_v
      hcons₁ rfl hcons_le hdesc_ch hdCur_hi hFlo₁ hs₁_peak
  have htree_lt : env.treePtr + 4 * cur + 3 < s₁.frontier := by
    have := hroot₁.1; simp only [List.length_cons, List.length_nil] at this; omega
  have hne0 : s₁.mem (env.treePtr + 4 * cur) ≠ 0 := by omega
  have hsafe_root : nodeStepSafe w (env, cur) s₁ :=
    ⟨hfit_4, hfit_tree.of_le (by simp only [NiceTree.size_introduce] at hsz; omega),
      hfit_total.of_le (by dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *; omega),
      hfit_total.of_le (by dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *; omega),
      Or.inr (Or.inl ⟨htag1, hq, hfit_q,
        by rw [harg_v]; exact hfit_v,
        hfit_total.of_le (by
          rw [hch1_eq]; dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *; omega),
        F_lo, inst.counting, child, inst.constraints, inst.vars,
        hwf₁, rfl, hcons₁, hcons_le, by rw [hch1_eq]; exact hdesc_ch, hFlo₁,
        by rw [harg_v]; exact hs₁_peak⟩)⟩
  have hr_s (x : ℕ) : (Memory.spec 0).clientState s₁ (Memory.read x) = s₁ := rfl
  have hr_r (x : ℕ) : (Memory.spec 0).clientResult s₁ (Memory.read x) = s₁.mem x := rfl
  have hst_root : (Memory.spec 0).clientState s₁ (nodeStep (env, cur)) =
      (Memory.spec 0).clientState s₁ (introNodeProg introArgs) := by
    unfold nodeStep; dsimp only
    iterate 4 rw [StateTransitionSpec.clientState_bind, hr_s, hr_r]
    rw [ite_eq_right hne0, ite_eq_left htag1, harg_v, hch1_eq,
      StateTransitionSpec.clientState_bind]
    rfl
  have hres_root : (Memory.spec 0).clientResult s₁ (nodeStep (env, cur)) = cur + 1 := by
    unfold nodeStep; dsimp only
    iterate 4 rw [StateTransitionSpec.clientResult_bind, hr_s, hr_r]
    rw [ite_eq_right hne0, ite_eq_left htag1, StateTransitionSpec.clientResult_bind]
    rfl
  have hv_root : (Memory.spec w).ValidHistory s₁
      ((Memory.spec w).clientHistory s₁ (nodeStep (env, cur))) := by
    unfold nodeStep; dsimp only
    refine validHistory_read_bind (by omega) ?_
    refine validHistory_read_bind (by omega) ?_
    refine validHistory_read_bind (by omega) ?_
    refine validHistory_read_bind (by omega) ?_
    rw [ite_eq_right hne0, ite_eq_left htag1, harg_v, hch1_eq]
    exact validHistory_bind_step hv_in (validHistory_pure w _ _)
  have hcost_root : memoryCost (nodeStep (env, cur)) s₁ ≤ perCost := by
    unfold nodeStep; dsimp only
    iterate 4 rw [memoryCost_bind', memoryCost_read, hr_s, hr_r]
    rw [ite_eq_right hne0, ite_eq_left htag1, harg_v, hch1_eq, memoryCost_bind',
      memoryCost_pure, Nat.add_zero]
    have hmul_c :
        inst.domainSize ^ (v :: bagList child).length *
          (2 + 3 * inst.constraints.length +
            inst.totalArity * (2 * (v :: bagList child).length + 3)) ≤
          inst.domainSize ^ E *
            (E ^ 2 + E + 4 + 3 * inst.constraints.length + inst.totalArity * (2 * E + 3)) := by
      refine Nat.mul_le_mul hpow_le ?_
      have har : inst.totalArity * (2 * (v :: bagList child).length + 3) ≤
          inst.totalArity * (2 * E + 3) := Nat.mul_le_mul_left _ (by omega)
      omega
    dsimp only [introArgs, TreeCSPInstance.totalArity, env, subtreeEnv, perCost] at hc_in hmul_c ⊢
    omega
  have hit_root_st : (Memory.spec 0).clientState s₁ (iterate nodeStep env 1 cur) =
      (Memory.spec 0).clientState s₁ (nodeStep (env, cur)) := by
    change (Memory.spec 0).clientState s₁ (nodeStep (env, cur) >>= iterate nodeStep env 0) = _
    rw [StateTransitionSpec.clientState_bind]; rfl
  have hit_root_res : (Memory.spec 0).clientResult s₁ (iterate nodeStep env 1 cur) = cur + 1 := by
    change (Memory.spec 0).clientResult s₁ (nodeStep (env, cur) >>= iterate nodeStep env 0) = _
    rw [StateTransitionSpec.clientResult_bind, hres_root]; rfl
  have hv_it_root : (Memory.spec w).ValidHistory s₁
      ((Memory.spec w).clientHistory s₁ (iterate nodeStep env 1 cur)) := by
    change (Memory.spec w).ValidHistory s₁
      ((Memory.spec w).clientHistory s₁ (nodeStep (env, cur) >>= iterate nodeStep env 0))
    exact validHistory_bind_step hv_root (validHistory_pure w _ _)
  have hc_it_root : memoryCost (iterate nodeStep env 1 cur) s₁ ≤ perCost := by
    change memoryCost (nodeStep (env, cur) >>= iterate nodeStep env 0) s₁ ≤ _
    rw [memoryCost_bind', show memoryCost (iterate nodeStep env 0 _) _ = 0 from rfl, Nat.add_zero]
    exact hcost_root
  simp only [NiceTree.size_introduce]
  refine ⟨iterationSafe_add nodeStep nodeStepSafe w env child.size 1 offset s hsafe_ch
      (by rw [hres_ch, hs₁_def]; exact ⟨hsafe_root, trivial⟩),
    validHistory_iterate_add nodeStep env child.size 1 offset s hv_ch
      (by dsimp only [cur]; rw [hres_ch, hs₁_def]; exact hv_it_root),
    by rw [clientResult_iterate_add, hres_ch, hs₁_def]; exact hit_root_res,
    ?_, ?_, ?_, ?_⟩
  · rw [clientState_iterate_add, hres_ch, hs₁_def, hit_root_st, hst_root]
    have hfr_le : (v :: bagList child).length +
        inst.domainSize ^ (v :: bagList child).length ≤ perSpace := by
      dsimp only [perSpace]; omega
    have hmul_bud : (child.size + 1) * perSpace = child.size * perSpace + perSpace := by ring
    change s₁.frontier ≤ s.frontier + child.size * perSpace at hfr_ch
    change _ ≤ s.frontier + (child.size + 1) * perSpace
    dsimp only [introArgs, env, subtreeEnv] at hfr_in hfr_ch ⊢
    omega
  · rw [clientState_iterate_add, hres_ch, hs₁_def]
    change FrameOutsideRange (env.descBase + 4 * offset)
      (env.descBase + 4 * (offset + (child.size + 1))) s
      ((Memory.spec 0).clientState s₁ (iterate nodeStep env 1 cur))
    rw [hit_root_st, hst_root]
    have hfr_in' : FrameOutsideRange (env.descBase + 4 * cur)
        (env.descBase + 4 * (cur + 1)) s₁
        ((Memory.spec 0).clientState s₁ (introNodeProg introArgs)) := by
      dsimp only [introArgs] at hframe_in
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using hframe_in
    simpa only [cur, env, subtreeEnv, Nat.add_assoc] using
      FrameOutsideRange.trans
        (hframe_ch.mono_range le_rfl (by dsimp only [cur, env, subtreeEnv]; omega))
        (hfr_in'.mono_range (by dsimp only [cur, env, subtreeEnv]; omega) le_rfl)
  · rw [clientState_iterate_add, hres_ch, hs₁_def]
    change NodeDescAt F_lo inst.counting inst.domainSize inst.constraints inst.vars
      (.introduce v child) (env.descBase + 4 * (offset + (child.size + 1) - 1))
      ((Memory.spec 0).clientState s₁ (iterate nodeStep env 1 cur))
    rw [hit_root_st, hst_root, show offset + (child.size + 1) - 1 = cur from by omega]
    exact hdesc_in
  · rw [memoryCost_iterate_add, hres_ch, hs₁_def]
    change memoryCost (iterate nodeStep env child.size offset) s +
        memoryCost (iterate nodeStep env 1 cur) s₁ ≤ (child.size + 1) * perCost
    have : (child.size + 1) * perCost = child.size * perCost + perCost := by ring
    change memoryCost (iterate nodeStep env child.size offset) s ≤ child.size * perCost at hc_ch
    omega

private theorem subtree_full {w : ℕ} (inst : TreeCSPInstance) (hw : Fits w inst.wordBound) :
    ∀ (S : NiceTree ℕ) (offset : ℕ) (s : Memory.State),
      SubtreeFullSpec w inst S offset s := by
  intro S
  induction S with
  | leaf => exact subtree_leaf inst hw
  | introduce v child ih => exact subtree_introduce inst hw v child ih
  | forget v child ih => exact subtree_forget inst hw v child ih
  | join left right ihl ihr => exact subtree_join inst hw left right ihl ihr

private def runTreeCSPProg (_ : Unit) : Memory.Prog ℕ := do
  let mode ← Memory.read 1
  let q ← Memory.read 2
  let varsLen ← Memory.read 3
  let numCons ← Memory.read 4
  let treeSize ← Memory.read 5
  let varsPtr := 6
  let treePtr := 6 + varsLen
  let consRawPtr := treePtr + 4 * treeSize
  let descBase ← Memory.allocDirty (4 * treeSize)
  let env : NodeEnv := ⟨mode, q, varsPtr, varsLen, treePtr, consRawPtr, numCons, descBase⟩
  let _ ← iterNodesProg ((env, 0), treeSize)
  let rootDesc := descBase + 4 * (treeSize - 1)
  let rootTblPtr ← Memory.read (rootDesc + 2)
  Memory.read rootTblPtr

private theorem inputFits_encode {w : ℕ} (inst : TreeCSPInstance) (hw : Fits w inst.wordBound) :
    InputFits w inst.encode := by
  have hlen_enc := (holdsIn_encode_decode inst).2.1
  refine ⟨hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega), fun x hx => ?_⟩
  unfold TreeCSPInstance.encode at hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap] at hx
  rcases hx with ((((rfl | rfl | rfl | rfl | rfl) | hx_v) | hx_t) | ⟨ct, hct, hx_c⟩)
  · exact hw.of_le (by split_ifs <;> (unfold TreeCSPInstance.wordBound; dsimp only; omega))
  · have hpow1 : 1 ≤ inst.domainSize ^ maxTableExp inst.tree :=
      Nat.one_le_pow _ _ inst.domainSize_pos
    have h1q : inst.domainSize ≤ inst.domainSize * inst.domainSize ^ maxTableExp inst.tree :=
      Nat.le_mul_of_pos_right _ hpow1
    exact hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
  · exact hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
  · have hcl : inst.constraints.length ≤
        (inst.constraints.flatMap ConstraintTable.encode).length := by
      have hlen : ∀ cs : List (ConstraintTable inst.domainSize),
          cs.length ≤ (cs.flatMap ConstraintTable.encode).length := by
        intro cs
        induction cs with
        | nil => exact le_rfl
        | cons c cs ih =>
          simp only [List.length_cons, List.flatMap_cons, List.length_append]
          have hce : 1 ≤ (ConstraintTable.encode c).length := by
            simp [ConstraintTable.encode]
          omega
      exact hlen inst.constraints
    exact hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
  · exact hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
  · have hv_m : x ≤ inst.vars.foldl max 0 := List.mem_le_foldl_max hx_v
    have hmvl : inst.vars.foldl max 0 ≤ inst.maxVarLabel := le_max_left _ _
    exact hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
  · have ht_m := encodeNiceTreeAux_max_le 0 inst.tree x hx_t
    have hmvt : maxTreeVert inst.tree ≤ inst.maxVarLabel :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    exact hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
  · have hct_len : (ConstraintTable.encode ct).length ≤
        (inst.constraints.flatMap ConstraintTable.encode).length := by
      have hsub : ∀ cs : List (ConstraintTable inst.domainSize), ct ∈ cs →
          (ConstraintTable.encode ct).length ≤ (cs.flatMap ConstraintTable.encode).length := by
        intro cs hmem
        induction cs with
        | nil => simp at hmem
        | cons c cs ih =>
          simp only [List.mem_cons] at hmem
          simp only [List.flatMap_cons, List.length_append]
          rcases hmem with rfl | hmem
          · exact Nat.le_add_right _ _
          · exact (ih hmem).trans (Nat.le_add_left _ _)
      exact hsub inst.constraints hct
    have hce_len : (ConstraintTable.encode ct).length =
        2 + ct.scope.length + ct.table.length := by
      simp [ConstraintTable.encode]; omega
    unfold ConstraintTable.encode at hx_c
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx_c
    rcases hx_c with ((rfl | rfl) | hx_s) | hx_t
    · exact hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
    · exact hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
    · have hsm : x ≤ (inst.constraints.flatMap fun c => c.scope).foldl max 0 :=
        List.mem_le_foldl_max (List.mem_flatMap.2 ⟨ct, hct, hx_s⟩)
      have hmvs : (inst.constraints.flatMap fun c => c.scope).foldl max 0 ≤ inst.maxVarLabel :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      exact hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
    · have htb := ct.table_bool x hx_t
      exact hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)

private theorem runTreeCSPProg_spec {w : ℕ} (inst : TreeCSPInstance)
    (hw : Fits w inst.wordBound) :
    let s₀ := Memory.State.init inst.encode
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (runTreeCSPProg ())) ∧
    (Memory.spec 0).clientResult s₀ (runTreeCSPProg ()) = inst.result ∧
    memoryCost (runTreeCSPProg ()) s₀ ≤ inst.stepBound := by
  let s₀ := Memory.State.init inst.encode
  obtain ⟨hfr₀, hlen_enc, hm1, hm2, hm3, hm4, hm5, hvars₀, htree₀, hcons₀⟩ :=
    holdsIn_encode_decode inst
  have hts_pos : 0 < inst.tree.size := niceTree_size_pos inst.tree
  have hf_len : Fits w (inst.encode.length + 1) :=
    hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
  have hwf₀ : Memory.WellFormed w s₀ :=
    Memory.wellFormed_init (inputFits_encode inst hw) hf_len
  let treePtr := 6 + inst.vars.length
  let consRawPtr := treePtr + 4 * inst.tree.size
  let descBase := inst.encode.length + 1
  let F_lo := descBase + 4 * inst.tree.size
  let s₁ := (Memory.spec 0).clientState s₀ (Memory.allocDirty (4 * inst.tree.size))
  have hs₁_fr : s₁.frontier = F_lo := by
    change s₀.frontier + 4 * inst.tree.size = F_lo; rw [hfr₀]
  have hp₁ : PreservesBelow descBase s₀ s₁ := by
    dsimp only [descBase]; rw [← hfr₀]; exact preservesBelow_allocDirty s₀ (4 * inst.tree.size)
  have hfit_a1 : Fits w (s₀.frontier + 4 * inst.tree.size) := hw.of_le (by
    rw [hfr₀]; unfold TreeCSPInstance.wordBound; dsimp only; omega)
  have hv₁ : (Memory.spec w).ValidHistory s₀
      ((Memory.spec w).clientHistory s₀ (Memory.allocDirty (4 * inst.tree.size))) :=
    validHistory_allocDirty hfit_a1
  have hwf₁ : Memory.WellFormed w s₁ := wellFormed_clientState hwf₀ hv₁
  have hvars₁ : HoldsIn 6 inst.vars s₁ :=
    hvars₀.mono (by dsimp only [descBase]; omega) hp₁
  have htree₁ : HoldsIn (treePtr + 4 * 0) (encodeNiceTreeAux 0 inst.tree) s₁ := by
    rw [Nat.mul_zero, Nat.add_zero]
    exact htree₀.mono (by rw [length_encodeNiceTree]; dsimp only [treePtr, descBase]; omega) hp₁
  have hcons₁ : HoldsIn consRawPtr (inst.constraints.flatMap ConstraintTable.encode) s₁ :=
    hcons₀.mono (by dsimp only [consRawPtr, treePtr, descBase]; omega) hp₁
  let env : NodeEnv :=
    ⟨if inst.counting then 1 else 0, inst.domainSize, 6, inst.vars.length,
      treePtr, consRawPtr, inst.constraints.length, descBase⟩
  have hfull := subtree_full inst hw inst.tree 0 s₁ (by omega) le_rfl le_rfl hwf₁
    (le_of_eq hs₁_fr.symm) (by rw [hs₁_fr]) hvars₁ htree₁ hcons₁
  obtain ⟨hsafe_tr, hv_tr, _, hfr_tr, _, hdesc_tr, hc_tr⟩ := hfull
  let s₂ := (Memory.spec 0).clientState s₁ (iterNodesProg ((env, 0), inst.tree.size))
  have hroot_tbl := hdesc_tr.tbl_holds
  have hroot_len : (dpInstTree inst.counting inst.domainSize inst.constraints inst.vars
      inst.tree).length = inst.domainSize ^ (bagList inst.tree).length :=
    length_dpInstTree _ _ _ _ _
  have h0_lt : 0 < inst.domainSize ^ (bagList inst.tree).length :=
    Nat.one_le_pow _ _ inst.domainSize_pos
  have hroot_get : s₂.mem (s₂.mem (descBase + 4 * (inst.tree.size - 1) + 2)) = inst.result := by
    have hg := hroot_tbl.get 0 (by rw [hroot_len]; exact h0_lt)
    dsimp only [s₂, iterNodesProg, env, subtreeEnv, descBase, treePtr, consRawPtr] at hg ⊢
    simp only [Nat.add_zero, Nat.zero_add] at hg
    rw [hg]
    unfold TreeCSPInstance.result
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hroot_len]; exact h0_lt)]
    rfl
  have hroot_desc_lt : descBase + 4 * (inst.tree.size - 1) + 2 < s₂.frontier := by
    have := hdesc_tr.desc_hi
    have := hdesc_tr.tbl_holds.1
    have : s₁.frontier ≤ s₂.frontier := by
      have htl := hdesc_tr.tbl_lo
      have htbl1 := hdesc_tr.tbl_holds.1
      rw [Nat.zero_add] at htl htbl1
      dsimp only [F_lo, s₂, iterNodesProg, env, subtreeEnv, descBase, treePtr, consRawPtr]
        at htl htbl1 ⊢
      omega
    rw [Nat.zero_add] at *
    dsimp only [F_lo, s₂, iterNodesProg, env, subtreeEnv, descBase, treePtr, consRawPtr] at *; omega
  have hroot_tbl_lt : s₂.mem (descBase + 4 * (inst.tree.size - 1) + 2) < s₂.frontier := by
    have htbl1 := hroot_tbl.1
    rw [hroot_len] at htbl1
    dsimp only [s₂, iterNodesProg, env, subtreeEnv, descBase, treePtr, consRawPtr] at htbl1 ⊢
    rw [Nat.zero_add] at htbl1
    omega
  have h1_lt : 1 < s₀.frontier := by rw [hfr₀]; omega
  have h2_lt : 2 < s₀.frontier := by rw [hfr₀]; omega
  have h3_lt : 3 < s₀.frontier := by rw [hfr₀]; omega
  have h4_lt : 4 < s₀.frontier := by rw [hfr₀]; omega
  have h5_lt : 5 < s₀.frontier := by rw [hfr₀]; omega
  have hr₀_s (a : ℕ) : (Memory.spec 0).clientState s₀ (Memory.read a) = s₀ := rfl
  have hr₀_r (a : ℕ) : (Memory.spec 0).clientResult s₀ (Memory.read a) = s₀.mem a := rfl
  have ha1_s : (Memory.spec 0).clientState s₀ (Memory.allocDirty (4 * inst.tree.size)) = s₁ := rfl
  have ha1_r : (Memory.spec 0).clientResult s₀ (Memory.allocDirty (4 * inst.tree.size)) =
      descBase := by
    change s₀.frontier = descBase; exact hfr₀
  have hr₂_s (a : ℕ) : (Memory.spec 0).clientState s₂ (Memory.read a) = s₂ := rfl
  have hr₂_r (a : ℕ) : (Memory.spec 0).clientResult s₂ (Memory.read a) = s₂.mem a := rfl
  refine ⟨?_, ?_, ?_⟩
  · unfold runTreeCSPProg
    dsimp only
    refine validHistory_read_bind h1_lt ?_; rw [hm1]
    refine validHistory_read_bind h2_lt ?_; rw [hm2]
    refine validHistory_read_bind h3_lt ?_; rw [hm3]
    refine validHistory_read_bind h4_lt ?_; rw [hm4]
    refine validHistory_read_bind h5_lt ?_; rw [hm5]
    refine validHistory_bind_step hv₁ ?_
    rw [ha1_s, ha1_r]
    change (Memory.spec w).ValidHistory s₁
      ((Memory.spec w).clientHistory s₁ (iterNodesProg ((env, 0), inst.tree.size) >>= _))
    refine validHistory_bind_step hv_tr ?_
    change (Memory.spec w).ValidHistory s₂
      ((Memory.spec w).clientHistory s₂
        (Memory.read (descBase + 4 * (inst.tree.size - 1) + 2) >>= fun tp => Memory.read tp))
    exact validHistory_read_bind hroot_desc_lt (validHistory_read hroot_tbl_lt)
  · unfold runTreeCSPProg
    dsimp only
    iterate 5 rw [StateTransitionSpec.clientResult_bind, hr₀_s, hr₀_r]
    rw [hm1, hm2, hm3, hm4, hm5, StateTransitionSpec.clientResult_bind, ha1_s, ha1_r]
    change (Memory.spec 0).clientResult s₁ (iterNodesProg ((env, 0), inst.tree.size) >>= _) =
      inst.result
    rw [StateTransitionSpec.clientResult_bind]
    change (Memory.spec 0).clientResult s₂
      (Memory.read (descBase + 4 * (inst.tree.size - 1) + 2) >>= fun tp => Memory.read tp) =
      inst.result
    rw [StateTransitionSpec.clientResult_bind, hr₂_s, hr₂_r, hr₂_r]
    exact hroot_get
  · unfold runTreeCSPProg
    dsimp only
    iterate 5 rw [memoryCost_bind', memoryCost_read, hr₀_s, hr₀_r]
    rw [hm1, hm2, hm3, hm4, hm5, memoryCost_bind', memoryCost_allocDirty, ha1_s, ha1_r,
      memoryCost_bind']
    change 1 + (1 + (1 + (1 + (1 + (1 + (memoryCost (iterNodesProg ((env, 0), inst.tree.size)) s₁ +
      memoryCost (Memory.read (descBase + 4 * (inst.tree.size - 1) + 2) >>= fun tp =>
        Memory.read tp) s₂)))))) ≤ inst.stepBound
    rw [memoryCost_bind', memoryCost_read, memoryCost_read]
    unfold TreeCSPInstance.stepBound
    dsimp only [env, subtreeEnv, treePtr, consRawPtr, descBase] at hc_tr ⊢
    change 1 + (1 + (1 + (1 + (1 + (1 + (memoryCost (iterate nodeStep env inst.tree.size 0) s₁ +
      (1 + 1))))))) ≤ _
    dsimp only [env, subtreeEnv, treePtr, consRawPtr, descBase]
    omega

private theorem runTreeCSPProg_realizes :
    Realizes .exact runTreeCSPProg WordEncoding.encode WordEncoding.encode
      (fun w _ s =>
        ∃ inst : TreeCSPInstance,
          s = Memory.State.init inst.encode ∧
          Fits w inst.wordBound)
      (fun _ _ => 0) := by
  unfold runTreeCSPProg
  realize [iterNodesProg_realizes]
  all_goals
    obtain ⟨inst, rfl, hw⟩ := h
    obtain ⟨hfr₀, hlen_enc, hm1, hm2, hm3, hm4, hm5, hvars₀, htree₀, hcons₀⟩ :=
      holdsIn_encode_decode inst
    have hts_pos : 0 < inst.tree.size := niceTree_size_pos inst.tree
    have hf_len : Fits w (inst.encode.length + 1) :=
      hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
    first
    | exact hts_pos
    | exact hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
    | (rw [hm1, hm2, hm3, hm4, hm5]
       have hwf₀ : Memory.WellFormed w (Memory.State.init inst.encode) :=
         Memory.wellFormed_init (inputFits_encode inst hw) hf_len
       let treePtr := 6 + inst.vars.length
       let consRawPtr := treePtr + 4 * inst.tree.size
       let descBase := inst.encode.length + 1
       let F_lo := descBase + 4 * inst.tree.size
       let s₀ := Memory.State.init inst.encode
       let s₁ := (Memory.spec 0).clientState s₀ (Memory.allocDirty (4 * inst.tree.size))
       have hs₁_fr : s₁.frontier = F_lo := by
         change s₀.frontier + 4 * inst.tree.size = F_lo; rw [hfr₀]
       have hp₁ : PreservesBelow descBase s₀ s₁ := by
         dsimp only [descBase]; rw [← hfr₀]; exact preservesBelow_allocDirty s₀ (4 * inst.tree.size)
       have hfit_a1 : Fits w (s₀.frontier + 4 * inst.tree.size) := hw.of_le (by
         rw [hfr₀]; unfold TreeCSPInstance.wordBound; dsimp only; omega)
       have hv₁ : (Memory.spec w).ValidHistory s₀
           ((Memory.spec w).clientHistory s₀ (Memory.allocDirty (4 * inst.tree.size))) :=
         validHistory_allocDirty hfit_a1
       have hwf₁ : Memory.WellFormed w s₁ := wellFormed_clientState hwf₀ hv₁
       have hvars₁ : HoldsIn 6 inst.vars s₁ :=
         hvars₀.mono (by dsimp only [descBase]; omega) hp₁
       have htree₁ : HoldsIn (treePtr + 4 * 0) (encodeNiceTreeAux 0 inst.tree) s₁ := by
         rw [Nat.mul_zero, Nat.add_zero]
         exact htree₀.mono
           (by rw [length_encodeNiceTree]; dsimp only [treePtr, descBase]; omega) hp₁
       have hcons₁ : HoldsIn consRawPtr (inst.constraints.flatMap ConstraintTable.encode) s₁ :=
         hcons₀.mono (by dsimp only [consRawPtr, treePtr, descBase]; omega) hp₁
       have hfull := subtree_full inst hw inst.tree 0 s₁ (by omega) le_rfl le_rfl hwf₁
         (le_of_eq hs₁_fr.symm) (by rw [hs₁_fr]) hvars₁ htree₁ hcons₁
       exact hfull.1)

/-- One fixed exact-basis Word-RAM program computes `TreeCSPInstance.result` within
`≤ C * (inst.stepBound + 1) + 1` instructions for every word width `w` satisfying
`Fits w inst.wordBound` and `InputFits w inst.encode`. -/
theorem exists_program_csp_treeDecomposition :
    ∃ r C : ℕ, ∃ prog : Program .exact r,
      prog.ComputesInTime
        (fun _ inst => inst.encode)
        (fun inst _ => C * (inst.stepBound + 1) + 1)
        (fun inst w => Fits w inst.wordBound)
        TreeCSPInstance.result := by
  obtain ⟨r, C, pc, prog, _, _, hexec⟩ :=
    runTreeCSPProg_realizes.exists_standard_init_program_state_from_words (0 : Fin 1)
  refine ⟨r, C, prog, fun inst w hw hin => ?_⟩
  have hf_len : Fits w (inst.encode.length + 1) :=
    hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
  obtain ⟨hval, hres, hcost⟩ := runTreeCSPProg_spec inst hw
  obtain ⟨y, n, hruns, hhalt, _, _, hn_le⟩ :=
    hexec w () inst.encode (fun i => Fin.elim0 i) (Nat.zero_le _) hf_len hin
      ⟨inst, rfl, hw⟩ hval
  rw [clientResult_width, hres] at hhalt
  refine ⟨n + 1, ⟨⟨pc, y⟩, n, hruns, hhalt, rfl⟩, ?_⟩
  have hmul : C * (memoryCost (runTreeCSPProg ()) (Memory.State.init inst.encode) + 0 + 1) + 1 ≤
      C * (inst.stepBound + 1) + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left C (by omega)) 1
  exact hn_le.trans hmul

/-- Uniform exact-basis Word-RAM computability certificate for `TreeCSPInstance.result`. -/
theorem uniformComputableInTime_csp_treeDecomposition :
    ∃ C : ℕ,
      UniformComputableInTime .exact
        TreeCSPInstance.result
        (fun _ inst => inst.encode)
        (fun inst _ => C * (inst.stepBound + 1) + 1)
        (fun inst w => Fits w inst.wordBound) := by
  obtain ⟨r, C, prog, hcomp⟩ := exists_program_csp_treeDecomposition
  refine ⟨C, r, prog, hcomp, fun inst => ?_⟩
  obtain ⟨w, hw_le, hin⟩ := InputFits.exists_width inst.encode inst.wordBound
  exact ⟨w, (fits_self inst.wordBound).mono hw_le, hin⟩

open Classical in
/-- **FPT Word-RAM CSP Decision (Nice Tree Decomposition).** One fixed exact-basis Word-RAM
program decides `CSP.Satisfiable sem F` (returning `1` if satisfiable, `0` otherwise) on any
finite-domain CSP `F : CSP Rel V` (`q > 0`, `e : V ≃ Fin m`) and nice tree decomposition `N` of
`F.primalGraph` with `N.width ≤ k` in `≤ C * (cspNiceStepBound q N.size k |F.vars| |F| + 1) + 1`
instructions at any word width `w` satisfying `Fits w inst.wordBound`. -/
theorem exists_program_cspDecide_nice :
    ∃ r C : ℕ, ∃ prog : Program .exact r,
      ∀ {Rel V : Type*} [DecidableEq V] {q m k : ℕ} (hq : 0 < q) (e : V ≃ Fin m)
        (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V)
        (N : F.primalGraph.NiceTreeDecomposition),
        N.width ≤ k →
        ∀ w : ℕ,
          let inst := TreeCSPInstance.ofNice false q hq e sem F N
          Fits w inst.wordBound →
          ∃ steps,
            Executes w prog (.init inst.encode) (if CSP.Satisfiable sem F then 1 else 0) steps ∧
            steps ≤ C * (cspNiceStepBound q N.size k F.vars.length F.length + 1) + 1 := by
  obtain ⟨r, C, prog, hcomp⟩ := exists_program_csp_treeDecomposition
  refine ⟨r, C, prog, fun {Rel V _ q m k} hq e sem F N hk w hw => ?_⟩
  let inst := TreeCSPInstance.ofNice false q hq e sem F N
  obtain ⟨steps, hexec, hsteps⟩ := hcomp inst w hw (inputFits_encode inst hw)
  have hres : inst.result = if CSP.Satisfiable sem F then 1 else 0 := by
    dsimp only [inst]
    rw [TreeCSPInstance.ofNice, TreeCSPInstance.result_ofNiceTree_decide]
    have hiff : cspDecideNiceTree q hq sem F N.tree = true ↔ CSP.Satisfiable sem F :=
      cspDecideNice_eq_true_iff hq sem N
    simp only [hiff]
  rw [hres] at hexec
  have hbound := TreeCSPInstance.stepBound_ofNice_le hq false e sem F N hk
  exact ⟨steps, hexec, hsteps.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_left C (Nat.add_le_add_right hbound 1)) 1)⟩

/-- **FPT Word-RAM CSP Model Counting (Nice Tree Decomposition).** One fixed exact-basis Word-RAM
program computes `CSP.modelCount sem F` in `≤ C * (cspNiceStepBound ... + 1) + 1` instructions at
any word width `w` satisfying `Fits w inst.wordBound` (accounting for DP count growth up to
`q ^ N.size`). -/
theorem exists_program_cspCount_nice :
    ∃ r C : ℕ, ∃ prog : Program .exact r,
      ∀ {Rel V : Type*} [DecidableEq V] {q m k : ℕ} (hq : 0 < q) (e : V ≃ Fin m)
        (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V)
        (N : F.primalGraph.NiceTreeDecomposition),
        N.width ≤ k →
        ∀ w : ℕ,
          let inst := TreeCSPInstance.ofNice true q hq e sem F N
          Fits w inst.wordBound →
          ∃ steps,
            Executes w prog (.init inst.encode)
              (@CSP.modelCount _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩ sem F) steps ∧
            steps ≤ C * (cspNiceStepBound q N.size k F.vars.length F.length + 1) + 1 := by
  obtain ⟨r, C, prog, hcomp⟩ := exists_program_csp_treeDecomposition
  refine ⟨r, C, prog, fun {Rel V _ q m k} hq e sem F N hk w hw => ?_⟩
  let inst := TreeCSPInstance.ofNice true q hq e sem F N
  obtain ⟨steps, hexec, hsteps⟩ := hcomp inst w hw (inputFits_encode inst hw)
  rw [TreeCSPInstance.result_ofNice_count hq e sem F N] at hexec
  have hbound := TreeCSPInstance.stepBound_ofNice_le hq true e sem F N hk
  exact ⟨steps, hexec, hsteps.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_left C (Nat.add_le_add_right hbound 1)) 1)⟩

open Classical in
/-- **FPT Word-RAM CSP Decision (Rooted Tree Decomposition).** One fixed exact-basis Word-RAM
program decides `CSP.Satisfiable sem F` over any `RootedTreeDecomposition` via `toNiceTreePruned`
in `≤ C * (cspRootedStepBound q m k |F.vars| |F| + 1) + 1` instructions. -/
theorem exists_program_cspDecide_rooted :
    ∃ r C : ℕ, ∃ prog : Program .exact r,
      ∀ {Rel V : Type*} [LinearOrder V] {q m n k : ℕ} (hq : 0 < q) (e : V ≃ Fin m)
        (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V)
        (R : F.primalGraph.RootedTreeDecomposition n),
        R.width ≤ k →
        ∀ w : ℕ,
          let inst := TreeCSPInstance.ofRooted false q hq e sem F R
          Fits w inst.wordBound →
          ∃ steps,
            Executes w prog (.init inst.encode) (if CSP.Satisfiable sem F then 1 else 0) steps ∧
            steps ≤ C * (cspRootedStepBound q m k F.vars.length F.length + 1) + 1 := by
  obtain ⟨r, C, prog, hcomp⟩ := exists_program_csp_treeDecomposition
  refine ⟨r, C, prog, fun {Rel V _ q m n k} hq e sem F R hk w hw => ?_⟩
  let inst := TreeCSPInstance.ofRooted false q hq e sem F R
  obtain ⟨steps, hexec, hsteps⟩ := hcomp inst w hw (inputFits_encode inst hw)
  have hres : inst.result = if CSP.Satisfiable sem F then 1 else 0 := by
    dsimp only [inst]
    rw [TreeCSPInstance.ofRooted, TreeCSPInstance.ofNice, TreeCSPInstance.result_ofNiceTree_decide]
    have hiff : cspDecideNiceTree q hq sem F R.toNiceTreePruned.tree = true ↔
        CSP.Satisfiable sem F :=
      cspDecideNice_eq_true_iff hq sem R.toNiceTreePruned
    simp only [hiff]
  rw [hres] at hexec
  have hbound := TreeCSPInstance.stepBound_ofRooted_le hq false e sem F R hk
  exact ⟨steps, hexec, hsteps.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_left C (Nat.add_le_add_right hbound 1)) 1)⟩

/-- **FPT Word-RAM CSP Model Counting (Rooted Tree Decomposition).** One fixed exact-basis
Word-RAM program computes `CSP.modelCount sem F` over any `RootedTreeDecomposition` via
`toNiceTreePruned` in `≤ C * (cspRootedStepBound q m k |F.vars| |F| + 1) + 1` instructions whenever
`Fits w inst.wordBound`. -/
theorem exists_program_cspCount_rooted :
    ∃ r C : ℕ, ∃ prog : Program .exact r,
      ∀ {Rel V : Type*} [LinearOrder V] {q m n k : ℕ} (hq : 0 < q) (e : V ≃ Fin m)
        (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V)
        (R : F.primalGraph.RootedTreeDecomposition n),
        R.width ≤ k →
        ∀ w : ℕ,
          let inst := TreeCSPInstance.ofRooted true q hq e sem F R
          Fits w inst.wordBound →
          ∃ steps,
            Executes w prog (.init inst.encode)
              (@CSP.modelCount _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩ sem F) steps ∧
            steps ≤ C * (cspRootedStepBound q m k F.vars.length F.length + 1) + 1 := by
  obtain ⟨r, C, prog, hcomp⟩ := exists_program_csp_treeDecomposition
  refine ⟨r, C, prog, fun {Rel V _ q m n k} hq e sem F R hk w hw => ?_⟩
  let inst := TreeCSPInstance.ofRooted true q hq e sem F R
  obtain ⟨steps, hexec, hsteps⟩ := hcomp inst w hw (inputFits_encode inst hw)
  rw [TreeCSPInstance.result_ofRooted_count hq e sem F R] at hexec
  have hbound := TreeCSPInstance.stepBound_ofRooted_le hq true e sem F R hk
  exact ⟨steps, hexec, hsteps.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_left C (Nat.add_le_add_right hbound 1)) 1)⟩

end Cslib.Algorithms.WordRAM.TreeDecomposition
