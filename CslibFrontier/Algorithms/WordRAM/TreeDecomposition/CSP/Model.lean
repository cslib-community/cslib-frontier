/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.TreeDecomposition.CSP
import CslibFrontier.Foundations.Data.List.FoldMax

/-!
# Serialized finite-domain CSP model and DP specification over nice tree decompositions

This module defines the pure data structures, post-order serialization, explicit `ℕ`-table DP
(`dpInstTree`), and FPT step-count bounds shared by the Word-RAM tree-decomposition CSP modules:

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.tupleOfRadix`: positional base-`q` decoding into
  `List (Fin q)`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.ConstraintTable`: materialized truth table for a
  constraint over `ℕ` variable indices.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.encodeNiceTree`: post-order 4-word-per-node
  serialization of `NiceTree ℕ`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.dpInstTree`: explicit `ℕ`-table DP over
  `ConstraintTable` lists mirroring `cspCountTree` / `cspDecideTree`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.TreeCSPInstance`: serialized CSP + nice tree
  decomposition instance supporting both satisfiability (`counting = false`) and exact model
  counting (`counting = true`), with constructors `ofNiceTree`, `ofNice`, and `ofRooted`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.cspNiceStepBound`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.cspRootedStepBound`: explicit FPT step-count
  polynomials.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.tupleOfRadix_toRadix`: `tupleOfRadix` inverts
  `toRadix` along any variable list, including repeated variables.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.TreeCSPInstance.result_ofNice_count`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.TreeCSPInstance.result_ofNice_decide`: agreement of
  `TreeCSPInstance.result` with exact model counting and satisfiability on nice decompositions.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.TreeCSPInstance.stepBound_ofNice_le`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.TreeCSPInstance.stepBound_ofRooted_le`: explicit
  FPT upper bounds on `TreeCSPInstance.stepBound`.
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open SimpleGraph
open Cslib.Logic.PL
open Cslib.Algorithms.Lean.TreeDecomposition

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

/-- Every vertex in `bagList T` is bounded by `maxTreeVert T`. -/
theorem mem_bagList_le_maxTreeVert :
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

/-- Every word emitted by `encodeNiceTreeAux offset T` is bounded by
`max 3 (max (maxTreeVert T) (offset + T.size))`. -/
theorem encodeNiceTreeAux_max_le (offset : ℕ) (T : NiceTree ℕ) :
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

/-- `dpInstTree` emits `q ^ (bagList T).length` entries. -/
@[simp] theorem length_dpInstTree (counting : Bool) (q : ℕ)
    (cs : List (ConstraintTable q)) (vars : List ℕ) (T : NiceTree ℕ) :
    (dpInstTree counting q cs vars T).length = q ^ (bagList T).length := by
  cases T <;> simp [dpInstTree, bagList]

/-- Entry magnitude bound for `dpInstTree`: `≤ 1` in decision mode and `≤ q ^ T.size` in counting
mode. -/
theorem mem_dpInstTree_le (counting : Bool) {q : ℕ} (hq : 0 < q)
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

/-- The bag length at `T` is bounded by `maxTableExp T`. -/
theorem bagList_length_le_maxTableExp (T : NiceTree ℕ) :
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

/-- Monotonicity of `maxTreeVert` across `introduce`. -/
theorem maxTreeVert_le_introduce (v : ℕ) (child : NiceTree ℕ) :
    maxTreeVert child ≤ maxTreeVert (.introduce v child) := le_max_right _ _

/-- Monotonicity of `maxTreeVert` across `forget`. -/
theorem maxTreeVert_le_forget (v : ℕ) (child : NiceTree ℕ) :
    maxTreeVert child ≤ maxTreeVert (.forget v child) := le_max_right _ _

/-- Monotonicity of `maxTreeVert` into the left child of `join`. -/
theorem maxTreeVert_le_join_left (left right : NiceTree ℕ) :
    maxTreeVert left ≤ maxTreeVert (.join left right) := le_max_left _ _

/-- Monotonicity of `maxTreeVert` into the right child of `join`. -/
theorem maxTreeVert_le_join_right (left right : NiceTree ℕ) :
    maxTreeVert right ≤ maxTreeVert (.join left right) := le_max_right _ _

/-- Monotonicity of `maxTableExp` across `introduce`. -/
theorem maxTableExp_le_introduce (v : ℕ) (child : NiceTree ℕ) :
    maxTableExp child ≤ maxTableExp (.introduce v child) := le_max_right _ _

/-- Monotonicity of `maxTableExp` across `forget`. -/
theorem maxTableExp_le_forget (v : ℕ) (child : NiceTree ℕ) :
    maxTableExp child ≤ maxTableExp (.forget v child) := le_max_right _ _

/-- Monotonicity of `maxTableExp` into the left child of `join`. -/
theorem maxTableExp_le_join_left (left right : NiceTree ℕ) :
    maxTableExp left ≤ maxTableExp (.join left right) :=
  (le_max_left _ _).trans (le_max_right _ _)

/-- Monotonicity of `maxTableExp` into the right child of `join`. -/
theorem maxTableExp_le_join_right (left right : NiceTree ℕ) :
    maxTableExp right ≤ maxTableExp (.join left right) :=
  (le_max_right _ _).trans (le_max_right _ _)

end Cslib.Algorithms.WordRAM.TreeDecomposition
