/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Algorithms.Lean.TimeM
public import CslibFrontier.Algorithms.Lean.TreeDecomposition.BagMask
public import CslibFrontier.Algorithms.Lean.TreeDecomposition.BagAssignment
public import CslibFrontier.Logics.Propositional.CSP.PrimalGraph
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import CslibFrontier.Algorithms.Lean.TimeM.Simps

/-!
# Dynamic programming for CSPs on bounded treewidth

For a constraint satisfaction problem `F : CSP Rel V` over a finite inhabited domain `Fin q`
(`0 < q`), and a valid nice tree decomposition covering every constraint scope of `F` (e.g., from
`F.primalGraph` or `F.activePrimalGraph`), we implement explicit `TimeM ℕ` dynamic programming
procedures for both exact model counting (`cspCountNiceM`, `cspCountRootedM`) and satisfiability
(`cspDecideNiceM`, `cspDecideRootedM`).

Using `SimpleGraph.RootedTreeDecomposition.toNiceTreePruned`, any supplied rooted tree
decomposition `R` of width `w` is first converted to a nice tree decomposition of width at most `w`
and size at most `(3 * w + 5) * (card V + 1)`, yielding total `TimeM ℕ` cost at most
`N.size * (q ^ (w + 1) * poly(w, |F|, totalArity F))` inner-loop ticks. The `TimeM` bound
is a selected-operation milestone for the table loops; it explicitly excludes the uncharged
recursive overhead of `bagList` list construction and element erasure, the structure normalization
work of `toNiceTreePruned` computed outside `TimeM`, `sem` evaluations, and unbounded integer
arithmetic. A bound on all traversal and arithmetic work remains an open objective.

## Main definitions

* `Cslib.Algorithms.Lean.TreeDecomposition.bagList`: canonical vertex list order at each nice-tree
  node.
* `Cslib.Algorithms.Lean.TreeDecomposition.cspCountTreeM`,
  `Cslib.Algorithms.Lean.TreeDecomposition.cspDecideTreeM`: bottom-up DP tables in `TimeM ℕ`.
* `Cslib.Algorithms.Lean.TreeDecomposition.cspCountNiceM`,
  `Cslib.Algorithms.Lean.TreeDecomposition.cspDecideNiceM`: root answers on nice decompositions of
  `F.primalGraph` (and `cspCountActiveNiceM`, `cspDecideActiveNiceM` on `F.activePrimalGraph`).
* `Cslib.Algorithms.Lean.TreeDecomposition.cspCountRootedM`,
  `Cslib.Algorithms.Lean.TreeDecomposition.cspDecideRootedM`: wrappers over arbitrary rooted tree
  decompositions via `toNiceTreePruned`.
* `Cslib.Algorithms.Lean.TreeDecomposition.dpNodeCost`: polynomial factor per node in the tree
  width `w`, constraint count `F.length`, and total arity `F.vars.length`.

## Main results

* `Cslib.Algorithms.Lean.TreeDecomposition.ret_cspCountNiceM`,
  `Cslib.Algorithms.Lean.TreeDecomposition.ret_cspDecideNiceM`: exact agreement with
  `CSP.modelCount` and `CSP.Satisfiable`.
* `Cslib.Algorithms.Lean.TreeDecomposition.time_cspCountTreeM_le`,
  `Cslib.Algorithms.Lean.TreeDecomposition.time_cspDecideTreeM_le`: `N.size * q ^ (w + 1) * poly`
  tick bounds.
* `Cslib.Algorithms.Lean.TreeDecomposition.ret_cspCountRootedM`,
  `Cslib.Algorithms.Lean.TreeDecomposition.time_cspCountRootedM_le` (and decision / active
  counterparts): exact correctness and explicit `(3 * w + 5) * (card V + 1) * q ^ (w + 1) * poly`
  tick bounds via `toNiceTreePruned`.
* `Cslib.Algorithms.Lean.TreeDecomposition.modelCount_semFin`,
  `Cslib.Algorithms.Lean.TreeDecomposition.satisfiable_semFin_iff`: reduction from an arbitrary
  `[Fintype D] [Inhabited D]` domain to `Fin (Fintype.card D)`.
-/

public section

namespace Cslib.Algorithms.Lean.TreeDecomposition

open Cslib.Logic.PL SimpleGraph

section BagOrder

variable {V : Type*} [DecidableEq V]

/-- Canonical variable listing of each bag in a `NiceTree`. -/
@[expose] def bagList : NiceTree V → List V
  | .leaf => []
  | .introduce v child => v :: bagList child
  | .forget v child => (bagList child).erase v
  | .join left _ => bagList left

private theorem toFinset_erase_of_nodup {L : List V} (hL : L.Nodup) (v : V) :
    (L.erase v).toFinset = L.toFinset.erase v := by
  ext x
  simp only [List.mem_toFinset, Finset.mem_erase]
  exact hL.mem_erase_iff

theorem bagList_nodup_and_toFinset :
    ∀ {T : NiceTree V}, T.LocalValid → (bagList T).Nodup ∧ (bagList T).toFinset = T.bag
  | .leaf, _ => ⟨List.nodup_nil, rfl⟩
  | .introduce v child, hval => by
    obtain ⟨hnodup, hfin⟩ := bagList_nodup_and_toFinset hval.2
    have hvnot : v ∉ bagList child := fun hv =>
      hval.1 (child.bag_subset_subtreeVerts (hfin ▸ List.mem_toFinset.2 hv))
    refine ⟨List.nodup_cons.2 ⟨hvnot, hnodup⟩, ?_⟩
    simp only [bagList, List.toFinset_cons, NiceTree.bag, hfin]
  | .forget v child, hval => by
    obtain ⟨hnodup, hfin⟩ := bagList_nodup_and_toFinset hval.2
    refine ⟨hnodup.erase v, ?_⟩
    simp only [bagList, NiceTree.bag, toFinset_erase_of_nodup hnodup v, hfin]
  | .join left _, hval => by
    obtain ⟨hnodup, hfin⟩ := bagList_nodup_and_toFinset hval.2.2.1
    exact ⟨hnodup, hfin⟩

theorem bagList_nodup {T : NiceTree V} (hval : T.LocalValid) : (bagList T).Nodup :=
  (bagList_nodup_and_toFinset hval).1

theorem toFinset_bagList {T : NiceTree V} (hval : T.LocalValid) : (bagList T).toFinset = T.bag :=
  (bagList_nodup_and_toFinset hval).2

theorem length_bagList {T : NiceTree V} (hval : T.LocalValid) :
    (bagList T).length = T.bag.card := by
  rw [← List.toFinset_card_of_nodup (bagList_nodup hval), toFinset_bagList hval]

theorem length_bagList_le {T : NiceTree V} (hval : T.LocalValid) :
    (bagList T).length ≤ T.width + 1 := by
  rw [length_bagList hval]
  have h1 := T.card_bag_le_maxBagCard
  have h2 : T.width = T.maxBagCard - 1 := rfl
  omega

end BagOrder

/-! ### Timed helper loops -/

section Helpers

variable {Rel V : Type*} [DecidableEq V]

/-- Check in `TimeM ℕ` whether every variable in `scope` appears in `LB`. -/
@[expose] def subsetListM : List V → List V → TimeM ℕ Bool
  | [], _ => pure true
  | x :: xs, LB => do
    let b1 ← memM x LB
    let b2 ← subsetListM xs LB
    TimeM.tick 1
    pure (b1 && b2)

@[time_simps]
theorem ret_subsetListM (xs LB : List V) :
    (subsetListM xs LB).ret = decide (xs.toFinset ⊆ LB.toFinset) := by
  time_spec subsetListM [List.toFinset_cons, Finset.insert_subset_iff, List.mem_toFinset]

theorem time_subsetListM (xs LB : List V) :
    (subsetListM xs LB).time = xs.length * (LB.length + 1) := by
  time_spec subsetListM [Nat.succ_mul]

/-- Evaluate all zero-arity constraints of `F` on a constant `Fin q` assignment. -/
@[expose] def checkNilScopeM {q : ℕ} (hq : 0 < q) (sem : Rel → List (Fin q) → Bool) :
    CSP Rel V → TimeM ℕ Bool
  | [] => pure true
  | c :: F => do
    let r ← checkNilScopeM hq sem F
    TimeM.tick 1
    let ok := match c.scope with
      | [] => sem c.rel []
      | _ :: _ => true
    pure (ok && r)

omit [DecidableEq V] in
@[time_simps]
theorem ret_checkNilScopeM {q : ℕ} (hq : 0 < q) (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) :
    (checkNilScopeM hq sem F).ret =
      F.all fun c => !decide (c.scope = []) || c.eval sem (fun _ => ⟨0, hq⟩) := by
  induction F with
  | nil => rfl
  | cons c F ih =>
    simp only [checkNilScopeM, TimeM.ret_bind, TimeM.ret_pure, ih, List.all_cons]
    cases hc : c.scope with
    | nil => simp [Constraint.eval, hc]
    | cons _ _ => simp

omit [DecidableEq V] in
theorem time_checkNilScopeM {q : ℕ} (hq : 0 < q) (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) :
    (checkNilScopeM hq sem F).time = F.length := by
  time_spec checkNilScopeM

/-- Check all constraints in `F` whose scopes lie in `LB` and include `v`, under `ofRadixFin`. -/
@[expose] def checkIntroScopeM (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (v : V) (LB : List V) (m : ℕ) : CSP Rel V → TimeM ℕ Bool
  | [] => pure true
  | c :: F => do
    let hsub ← subsetListM c.scope LB
    let hv ← memM v c.scope
    let vals ← evalScopeM q hq LB m c.scope
    let r ← checkIntroScopeM q hq sem v LB m F
    TimeM.tick 1
    pure ((!(hsub && hv) || sem c.rel vals) && r)

@[time_simps]
theorem ret_checkIntroScopeM {q : ℕ} (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (v : V) (LB : List V) (m : ℕ) (F : CSP Rel V) :
    (checkIntroScopeM q hq sem v LB m F).ret =
      F.all fun c =>
        !(decide (c.scope.toFinset ⊆ LB.toFinset) && decide (v ∈ c.scope)) ||
          c.eval sem (ofRadixFin q hq LB m) := by
  time_spec checkIntroScopeM

theorem time_checkIntroScopeM (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (v : V) (LB : List V) (m : ℕ) (F : CSP Rel V) :
    (checkIntroScopeM q hq sem v LB m F).time =
      F.length + F.vars.length * (2 * LB.length + 3) := by
  induction F with
  | nil => simp [checkIntroScopeM, CSP.vars]
  | cons c F ih =>
    simp only [checkIntroScopeM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure,
      time_subsetListM, time_memM, time_evalScopeM, ih, List.length_cons, CSP.vars,
      List.flatMap_cons, List.length_append]
    ring

/-- Encode `Function.update (ofRadix q LB m) v d` along `LP`. -/
@[expose] def projectUpdateM (q : ℕ) (v : V) (d : ℕ) (LB : List V) (m : ℕ) :
    List V → TimeM ℕ ℕ
  | [] => pure 0
  | u :: LP => do
    let r ← projectUpdateM q v d LB m LP
    let val ← if u = v then pure d else lookupM q u LB m
    TimeM.tick 1
    pure (val % q + q * r)

theorem ret_projectUpdateM {q : ℕ} (hq : 0 < q) (v : V) (d : ℕ) (LB LP : List V) (m : ℕ) :
    (projectUpdateM q v d LB m LP).ret = toRadix q LP (Function.update (ofRadix q LB m) v d) := by
  induction LP with
  | nil => rfl
  | cons u LP ih =>
    by_cases huv : u = v
    · simp only [projectUpdateM, huv, ite_true, time_simps, ih, toRadix_cons, Function.update_self]
    · simp only [projectUpdateM, huv, ite_false, time_simps, ih, toRadix_cons,
        Function.update_of_ne huv, Nat.mod_eq_of_lt (ofRadix_lt hq LB m u)]

theorem time_projectUpdateM_le (q : ℕ) (v : V) (d : ℕ) (LB LP : List V) (m : ℕ) :
    (projectUpdateM q v d LB m LP).time ≤ LP.length * (LB.length + 1) := by
  induction LP with
  | nil => simp [projectUpdateM]
  | cons u LP ih =>
    by_cases huv : u = v
    · simp only [projectUpdateM, huv, ite_true, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure,
        List.length_cons, Nat.succ_mul]
      omega
    · simp only [projectUpdateM, huv, ite_false, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure,
        time_lookupM, List.length_cons, Nat.succ_mul]
      omega

/-- Build a length-`n` array table entry by entry in `TimeM ℕ`. -/
@[expose] def tableLoopM {β : Type} : ℕ → (ℕ → TimeM ℕ β) → TimeM ℕ (Array β)
  | 0, _ => pure #[]
  | n + 1, f => do
    let acc ← tableLoopM n f
    let val ← f n
    TimeM.tick 1
    pure (acc.push val)

theorem size_tableLoopM {β : Type} (n : ℕ) (f : ℕ → TimeM ℕ β) :
    (tableLoopM n f).ret.size = n := by
  time_spec tableLoopM [Array.size_push]

theorem getD_tableLoopM {β : Type} (f : ℕ → TimeM ℕ β) {s n : ℕ} (hs : s < n) (z : β) :
    (tableLoopM n f).ret.getD s z = (f s).ret := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [tableLoopM, time_simps]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_push, size_tableLoopM]
    by_cases hsn : s = n
    · subst hsn
      simp
    · rw [ite_eq_right hsn, ← Array.getD_eq_getD_getElem?, ih (by omega)]

theorem time_tableLoopM_le {β : Type} {n B : ℕ} {f : ℕ → TimeM ℕ β}
    (hB : ∀ s < n, (f s).time ≤ B) : (tableLoopM n f).time ≤ n * (B + 1) := by
  time_spec tableLoopM

/-- Aggregate `f 0, ..., f (k - 1)` using `add` and identity `z` in `TimeM ℕ`. -/
@[expose] def sumLoopM {β : Type} (z : β) (add : β → β → β) :
    ℕ → (ℕ → TimeM ℕ β) → TimeM ℕ β
  | 0, _ => pure z
  | k + 1, f => do
    let acc ← sumLoopM z add k f
    let val ← f k
    TimeM.tick 1
    pure (add acc val)

private theorem time_sumLoopM_le {β : Type} (z : β) (add : β → β → β) {k B : ℕ}
    {f : ℕ → TimeM ℕ β} (hB : ∀ d < k, (f d).time ≤ B) :
    (sumLoopM z add k f).time ≤ k * (B + 1) := by
  time_spec sumLoopM

end Helpers

/-! ### Shared DP engine, specifications, and runtime bounds -/

section Engine

variable {Rel V : Type*} [DecidableEq V]

/-- Semiring-like operations used by `dpTreeM` for both counting and decision. -/
structure DPAlg (β : Type) where
  /-- Additive identity (0 for counting, `false` for decision). -/
  zero : β
  /-- Multiplicative identity (1 for counting, `true` for decision). -/
  one : β
  /-- Aggregation across values of a forgotten variable. -/
  add : β → β → β
  /-- Combination of two join-branch table entries. -/
  mul : β → β → β

/-- Generic bottom-up DP engine over a `NiceTree`, parameterized by `DPAlg`. -/
@[expose] def dpTreeM {β : Type} (A : DPAlg β) (q : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) (vars : List V) :
    NiceTree V → TimeM ℕ (Array β)
  | .leaf => do
    let ok ← checkNilScopeM hq sem F
    TimeM.tick 1
    pure #[if ok then A.one else A.zero]
  | .introduce v child => do
    let childTbl ← dpTreeM A q hq sem F vars child
    let LB := v :: bagList child
    tableLoopM (q ^ LB.length) fun m => do
      let ok ← checkIntroScopeM q hq sem v LB m F
      TimeM.tick 1
      pure (if ok then childTbl.getD (m / q) A.zero else A.zero)
  | .forget v child => do
    let childTbl ← dpTreeM A q hq sem F vars child
    let LB := (bagList child).erase v
    let hU ← memM v vars
    tableLoopM (q ^ LB.length) fun m => do
      if hU then
        sumLoopM A.zero A.add q fun d => do
          let idx ← projectUpdateM q v d LB m (bagList child)
          pure (childTbl.getD idx A.zero)
      else
        let idx ← projectUpdateM q v 0 LB m (bagList child)
        pure (childTbl.getD idx A.zero)
  | .join left right => do
    let leftTbl ← dpTreeM A q hq sem F vars left
    let rightTbl ← dpTreeM A q hq sem F vars right
    let LL := bagList left
    let LR := bagList right
    tableLoopM (q ^ LL.length) fun m => do
      let mr ← projectM q LL m LR
      TimeM.tick 1
      pure (A.mul (leftTbl.getD m A.zero) (rightTbl.getD mr A.zero))

private def dpAlgFold {β : Type} (z : β) (add : β → β → β) : ℕ → (ℕ → β) → β
  | 0, _ => z
  | k + 1, g => add (dpAlgFold z add k g) (g k)

private theorem dpAlgFold_congr {β : Type} {z : β} {add : β → β → β} {k : ℕ}
    {g₁ g₂ : ℕ → β} (h : ∀ d < k, g₁ d = g₂ d) :
    dpAlgFold z add k g₁ = dpAlgFold z add k g₂ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [dpAlgFold, ih fun d hd => h d (Nat.lt_succ_of_lt hd), h k (Nat.lt_succ_self k)]

private theorem ret_sumLoopM_eq_dpAlgFold {β : Type} (z : β) (add : β → β → β) (k : ℕ)
    (f : ℕ → TimeM ℕ β) :
    (sumLoopM z add k f).ret = dpAlgFold z add k (fun d => (f d).ret) := by
  time_spec sumLoopM

private theorem dpAlgFold_nat (k : ℕ) (g : ℕ → ℕ) :
    dpAlgFold 0 (· + ·) k g = ∑ d ∈ Finset.range k, g d := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [dpAlgFold, Finset.sum_range_succ, ih]

private theorem dpAlgFold_bool (k : ℕ) (g : ℕ → Bool) :
    dpAlgFold false (· || ·) k g = decide (∃ d < k, g d = true) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [dpAlgFold, ih]
    rw [← Bool.decide_eq_true (b := g k), ← Bool.decide_or]
    refine decide_eq_decide.2 ⟨?_, ?_⟩
    · rintro (⟨d, hdk, hfd⟩ | hk)
      · exact ⟨d, Nat.lt_succ_of_lt hdk, hfd⟩
      · exact ⟨k, Nat.lt_succ_self k, hk⟩
    · rintro ⟨d, hdk, hfd⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hdk with hlt | rfl
      · exact Or.inl ⟨d, hlt, hfd⟩
      · exact Or.inr hfd

private noncomputable def dpSpec {β : Type} (A : DPAlg β) (q : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) (U : Finset V) :
    NiceTree V → (V → Fin q) → β
  | .leaf, _ =>
    if F.all (fun c => !decide (c.scope = []) || c.eval sem (fun _ => ⟨0, hq⟩)) then
      A.one
    else A.zero
  | .introduce v child, α =>
    if F.all (fun c => !(decide (c.scope.toFinset ⊆ insert v child.bag) && decide (v ∈ c.scope)) ||
        c.eval sem α) then
      dpSpec A q hq sem F U child α
    else A.zero
  | .forget v child, α =>
    letI := Classical.propDecidable (v ∈ U)
    if v ∈ U then
      dpAlgFold A.zero A.add q fun d =>
        if hd : d < q then dpSpec A q hq sem F U child (Function.update α v ⟨d, hd⟩) else A.zero
    else
      dpSpec A q hq sem F U child (Function.update α v ⟨0, hq⟩)
  | .join left right, α =>
    A.mul (dpSpec A q hq sem F U left α) (dpSpec A q hq sem F U right α)

/-- `DPAlg` instance over `ℕ` for exact model counting. -/
@[expose] def dpCountAlg : DPAlg ℕ where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)

/-- `DPAlg` instance over `Bool` for satisfiability decision. -/
@[expose] def dpDecideAlg : DPAlg Bool where
  zero := false
  one := true
  add := (· || ·)
  mul := (· && ·)

/-- Compute the bottom-up exact-count DP table on a nice tree decomposition over `Fin q`. -/
@[expose] def cspCountTreeM (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) (vars : List V) (T : NiceTree V) : TimeM ℕ (Array ℕ) :=
  dpTreeM dpCountAlg q hq sem F vars T

/-- Compute the bottom-up satisfiability DP table on a nice tree decomposition over `Fin q`. -/
@[expose] def cspDecideTreeM (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) (vars : List V) (T : NiceTree V) : TimeM ℕ (Array Bool) :=
  dpTreeM dpDecideAlg q hq sem F vars T

/-- Polynomial per-node tick factor in treewidth `w`, constraint count `F.length`, and total
arity `F.vars.length`. -/
@[expose] def dpNodeCost (w : ℕ) (F : CSP Rel V) : ℕ :=
  F.length + F.vars.length * (2 * w + 6) + (w + 1) * (w + 2) + 4

private theorem width_le_of_maxBagCard_le {S T : NiceTree V}
    (h : S.maxBagCard ≤ T.maxBagCard) : S.width ≤ T.width := by
  change S.maxBagCard - 1 ≤ T.maxBagCard - 1
  omega

omit [DecidableEq V] in
private theorem dpNodeCost_mono {w w' : ℕ} (h : w ≤ w') (F : CSP Rel V) :
    dpNodeCost w F ≤ dpNodeCost w' F := by
  unfold dpNodeCost
  gcongr

omit [DecidableEq V] in
private theorem treeCost_mono {q w₁ w₂ : ℕ} (hq : 0 < q) (hw : w₁ ≤ w₂) (F : CSP Rel V) :
    q ^ (w₁ + 1) * dpNodeCost w₁ F ≤ q ^ (w₂ + 1) * dpNodeCost w₂ F :=
  Nat.mul_le_mul (Nat.pow_le_pow_right hq (Nat.add_le_add_right hw 1)) (dpNodeCost_mono hw F)

private theorem time_dpTreeM_forget_step {β : Type} (A : DPAlg β) (q : ℕ) (hq : 0 < q)
    (v : V) (child : NiceTree V) (F : CSP Rel V)
    (childTbl : Array β) (hval : (NiceTree.forget v child).LocalValid) :
    (memM v F.vars).time + (tableLoopM (q ^ ((bagList child).erase v).length) fun m =>
      if (memM v F.vars).ret then
        sumLoopM A.zero A.add q fun d => do
          let idx ← projectUpdateM q v d ((bagList child).erase v) m (bagList child)
          pure (childTbl.getD idx A.zero)
      else do
        let idx ← projectUpdateM q v 0 ((bagList child).erase v) m (bagList child)
        pure (childTbl.getD idx A.zero)).time ≤
      q ^ ((NiceTree.forget v child).width + 1) *
        dpNodeCost (NiceTree.forget v child).width F := by
  let W := (NiceTree.forget v child).width
  have hcw : child.width ≤ W := width_le_of_maxBagCard_le (le_max_right _ _)
  have hlenChild : (bagList child).length ≤ W + 1 :=
    (length_bagList_le hval.2).trans (Nat.add_le_add_right hcw 1)
  have hlen : ((bagList child).erase v).length ≤ W := by
    have h1 : ((bagList child).erase v).length = (NiceTree.forget v child).bag.card := by
      simpa only [bagList] using length_bagList (T := .forget v child) hval
    have hcard : (NiceTree.forget v child).bag.card + 1 = child.bag.card :=
      Finset.card_erase_add_one hval.1
    have h2 := length_bagList hval.2
    omega
  have hinner : ∀ m d : ℕ, (do
      let idx ← projectUpdateM q v d ((bagList child).erase v) m (bagList child)
      pure (childTbl.getD idx A.zero)).time ≤ (W + 1) * (W + 2) := fun m d => by
    simp only [TimeM.time_bind, TimeM.time_pure, Nat.add_zero]
    exact (time_projectUpdateM_le q v d _ _ _).trans (Nat.mul_le_mul hlenChild (by omega))
  have hloop := time_tableLoopM_le (n := q ^ ((bagList child).erase v).length)
    (B := q * ((W + 1) * (W + 2) + 1))
    (f := fun m =>
      if (memM v F.vars).ret then
        sumLoopM A.zero A.add q fun d => do
          let idx ← projectUpdateM q v d ((bagList child).erase v) m (bagList child)
          pure (childTbl.getD idx A.zero)
      else do
        let idx ← projectUpdateM q v 0 ((bagList child).erase v) m (bagList child)
        pure (childTbl.getD idx A.zero))
    fun m _ => by
      split_ifs
      · exact time_sumLoopM_le A.zero A.add fun d _ => hinner m d
      · exact (hinner m 0).trans ((Nat.le_mul_of_pos_left _ hq).trans
          (Nat.mul_le_mul_left q (Nat.le_succ _)))
  have hstep1 : q ^ ((bagList child).erase v).length * (q * ((W + 1) * (W + 2) + 1) + 1) ≤
      q ^ (W + 1) * ((W + 1) * (W + 2) + 2) := by
    calc q ^ ((bagList child).erase v).length * (q * ((W + 1) * (W + 2) + 1) + 1)
        ≤ q ^ ((bagList child).erase v).length * (q * ((W + 1) * (W + 2) + 1) + q) := by
          gcongr
          exact hq
      _ = q ^ (((bagList child).erase v).length + 1) * ((W + 1) * (W + 2) + 2) := by
          rw [Nat.pow_succ]; ring
      _ ≤ q ^ (W + 1) * ((W + 1) * (W + 2) + 2) := by gcongr
  have hvars : F.vars.length ≤ q ^ (W + 1) * F.vars.length :=
    Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ hq)
  rw [time_memM]
  refine (Nat.add_le_add hvars (hloop.trans hstep1)).trans ?_
  rw [← Nat.mul_add]
  refine Nat.mul_le_mul_left _ ?_
  unfold dpNodeCost
  have h2 := Nat.le_mul_of_pos_right F.vars.length
    (by omega : 0 < 2 * (NiceTree.forget v child).width + 6)
  dsimp only [W]
  omega

private theorem time_dpTreeM_le_aux {β : Type} (A : DPAlg β) (q : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) :
    ∀ {T : NiceTree V}, T.LocalValid →
      (dpTreeM A q hq sem F F.vars T).time ≤
        T.size * (q ^ (T.width + 1) * dpNodeCost T.width F)
  | .leaf, _ => by
    simp only [dpTreeM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, time_checkNilScopeM]
    have hqpow : 1 ≤ q ^ ((NiceTree.leaf : NiceTree V).width + 1) := Nat.one_le_pow _ _ hq
    have hcost : F.length + 1 ≤ dpNodeCost (NiceTree.leaf : NiceTree V).width F := by
      unfold dpNodeCost; omega
    have hsize : (NiceTree.leaf : NiceTree V).size = 1 := rfl
    rw [hsize, Nat.one_mul]
    calc F.length + 1 + 0 = 1 * (F.length + 1) := by omega
      _ ≤ _ := Nat.mul_le_mul hqpow hcost
  | .introduce v child, hval => by
    have hcw : child.width ≤ (NiceTree.introduce v child).width :=
      width_le_of_maxBagCard_le (le_max_right _ _)
    have hih := (time_dpTreeM_le_aux A q hq sem F hval.2).trans
      (Nat.mul_le_mul_left _ (treeCost_mono hq hcw F))
    have hlen : (v :: bagList child).length ≤ (NiceTree.introduce v child).width + 1 := by
      simpa only [bagList] using length_bagList_le (T := .introduce v child) hval
    have hloop := time_tableLoopM_le (n := q ^ (v :: bagList child).length)
      (B := F.length + F.vars.length * (2 * ((NiceTree.introduce v child).width + 1) + 3) + 1)
      (f := fun m => do
        let ok ← checkIntroScopeM q hq sem v (v :: bagList child) m F
        TimeM.tick 1
        pure (if ok then (dpTreeM A q hq sem F F.vars child).ret.getD (m / q) A.zero else A.zero))
      fun m _ => by
        simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, time_checkIntroScopeM]
        gcongr
        omega
    have hstep : q ^ (v :: bagList child).length *
          (F.length + F.vars.length * (2 * ((NiceTree.introduce v child).width + 1) + 3) + 1 + 1) ≤
        q ^ ((NiceTree.introduce v child).width + 1) *
          dpNodeCost (NiceTree.introduce v child).width F := by
      refine Nat.mul_le_mul (Nat.pow_le_pow_right hq hlen) ?_
      unfold dpNodeCost
      have hmul := Nat.mul_le_mul_left F.vars.length
        (by omega : 2 * ((NiceTree.introduce v child).width + 1) + 3 ≤
          2 * (NiceTree.introduce v child).width + 6)
      omega
    have hsize : (NiceTree.introduce v child).size = child.size + 1 := rfl
    simp only [dpTreeM, TimeM.time_bind]
    rw [hsize, Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add hih (hloop.trans hstep)
  | .forget v child, hval => by
    have hcw : child.width ≤ (NiceTree.forget v child).width :=
      width_le_of_maxBagCard_le (le_max_right _ _)
    have hih := (time_dpTreeM_le_aux A q hq sem F hval.2).trans
      (Nat.mul_le_mul_left _ (treeCost_mono hq hcw F))
    have hstep := time_dpTreeM_forget_step A q hq v child F
      (dpTreeM A q hq sem F F.vars child).ret hval
    have hsize : (NiceTree.forget v child).size = child.size + 1 := rfl
    simp only [dpTreeM, TimeM.time_bind]
    rw [hsize, Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add hih hstep
  | .join left right, hval => by
    have hlw : left.width ≤ (NiceTree.join left right).width :=
      width_le_of_maxBagCard_le (le_trans (le_max_left _ _) (le_max_right _ _))
    have hrw : right.width ≤ (NiceTree.join left right).width :=
      width_le_of_maxBagCard_le (le_trans (le_max_right _ _) (le_max_right _ _))
    have ihL' := (time_dpTreeM_le_aux A q hq sem F hval.2.2.1).trans
      (Nat.mul_le_mul_left _ (treeCost_mono hq hlw F))
    have ihR' := (time_dpTreeM_le_aux A q hq sem F hval.2.2.2).trans
      (Nat.mul_le_mul_left _ (treeCost_mono hq hrw F))
    have hlenL : (bagList left).length ≤ (NiceTree.join left right).width + 1 :=
      (length_bagList_le hval.2.2.1).trans (Nat.add_le_add_right hlw 1)
    have hlenR : (bagList right).length ≤ (NiceTree.join left right).width + 1 :=
      (length_bagList_le hval.2.2.2).trans (Nat.add_le_add_right hrw 1)
    have hstep : q ^ (bagList left).length *
          (((NiceTree.join left right).width + 1) * ((NiceTree.join left right).width + 2) + 2) ≤
        q ^ ((NiceTree.join left right).width + 1) *
          dpNodeCost (NiceTree.join left right).width F := by
      refine Nat.mul_le_mul (Nat.pow_le_pow_right hq hlenL) ?_
      unfold dpNodeCost; omega
    have hloop := time_tableLoopM_le (n := q ^ (bagList left).length)
      (B := ((NiceTree.join left right).width + 1) * ((NiceTree.join left right).width + 2) + 1)
      (f := fun m => do
        let mr ← projectM q (bagList left) m (bagList right)
        TimeM.tick 1
        pure (A.mul ((dpTreeM A q hq sem F F.vars left).ret.getD m A.zero)
          ((dpTreeM A q hq sem F F.vars right).ret.getD mr A.zero)))
      fun m _ => by
        simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, time_projectM]
        have hmul := Nat.mul_le_mul hlenR
          (by omega : (bagList left).length + 1 ≤ (NiceTree.join left right).width + 2)
        omega
    have hsize : (NiceTree.join left right).size = left.size + right.size + 1 := by
      simp only [NiceTree.size, NiceTree.sizePred]; omega
    simp only [dpTreeM, TimeM.time_bind]
    rw [hsize, Nat.add_mul, Nat.add_mul, Nat.one_mul]
    calc _ ≤ left.size * _ + (right.size * _ + q ^ ((left.join right).width + 1) *
          dpNodeCost (left.join right).width F) :=
        Nat.add_le_add ihL' (Nat.add_le_add ihR' (hloop.trans hstep))
      _ = _ := by ring

theorem time_cspCountTreeM_le (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) {T : NiceTree V} (hval : T.LocalValid) :
    (cspCountTreeM q hq sem F F.vars T).time ≤
      T.size * (q ^ (T.width + 1) * dpNodeCost T.width F) :=
  time_dpTreeM_le_aux dpCountAlg q hq sem F hval

theorem time_cspDecideTreeM_le (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) {T : NiceTree V} (hval : T.LocalValid) :
    (cspDecideTreeM q hq sem F F.vars T).time ≤
      T.size * (q ^ (T.width + 1) * dpNodeCost T.width F) :=
  time_dpTreeM_le_aux dpDecideAlg q hq sem F hval

end Engine

/-! ### Correctness of the DP tables against `specDPCount` and `specDPDecide` -/

section Correctness

variable {Rel V : Type*} [DecidableEq V]

private theorem dpSpec_congr {β : Type} (A : DPAlg β) (q : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) (U : Finset V) :
    ∀ {T : NiceTree V}, T.LocalValid →
      ∀ {α₁ α₂ : V → Fin q}, (∀ v ∈ T.bag, α₁ v = α₂ v) →
        dpSpec A q hq sem F U T α₁ = dpSpec A q hq sem F U T α₂
  | .leaf, _, _, _, _ => rfl
  | .introduce v child, hval, α₁, α₂, h => by
    simp only [dpSpec]
    have hbag : ∀ u ∈ child.bag, α₁ u = α₂ u := fun u hu => h u (Finset.mem_insert_of_mem hu)
    have hAll : (F.all fun c => !(decide (c.scope.toFinset ⊆ insert v child.bag) &&
        decide (v ∈ c.scope)) || c.eval sem α₁) =
      (F.all fun c => !(decide (c.scope.toFinset ⊆ insert v child.bag) &&
        decide (v ∈ c.scope)) || c.eval sem α₂) := by
      refine List.all_congr rfl fun c => ?_
      by_cases hc : c.scope.toFinset ⊆ insert v child.bag
      · have hev : c.eval sem α₁ = c.eval sem α₂ :=
          Constraint.eval_congr fun u hu => h u (hc (List.mem_toFinset.2 hu))
        rw [hev]
      · simp [hc]
    rw [hAll, dpSpec_congr A q hq sem F U hval.2 hbag]
  | .forget v child, hval, α₁, α₂, h => by
    have hupd (d : Fin q) :
        dpSpec A q hq sem F U child (Function.update α₁ v d) =
          dpSpec A q hq sem F U child (Function.update α₂ v d) :=
      dpSpec_congr A q hq sem F U hval.2 fun u hu => by
        by_cases huv : u = v
        · simp [huv]
        · simp [huv, h u (Finset.mem_erase.2 ⟨huv, hu⟩)]
    simp only [dpSpec]
    split_ifs with hvU
    · refine dpAlgFold_congr fun d _ => ?_
      by_cases hd : d < q
      · simp only [hd, ↓reduceDIte, hupd]
      · simp [hd]
    · exact hupd ⟨0, hq⟩
  | .join left right, hval, α₁, α₂, h => by
    simp only [dpSpec]
    have hL : ∀ u ∈ left.bag, α₁ u = α₂ u := h
    have hR : ∀ u ∈ right.bag, α₁ u = α₂ u := fun u hu => h u (hval.1 ▸ hu)
    rw [dpSpec_congr A q hq sem F U hval.2.2.1 hL,
      dpSpec_congr A q hq sem F U hval.2.2.2 hR]

private theorem getD_dpTreeM {β : Type} (A : DPAlg β) (q : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) :
    ∀ {T : NiceTree V}, T.LocalValid →
      ∀ {m : ℕ}, m < q ^ (bagList T).length →
        (dpTreeM A q hq sem F F.vars T).ret.getD m A.zero =
          dpSpec A q hq sem F F.vars.toFinset T (ofRadixFin q hq (bagList T) m)
  | .leaf, _, m, hm => by
    simp only [bagList, List.length_nil, Nat.pow_zero, Nat.lt_one_iff] at hm
    subst hm
    simp only [dpTreeM, time_simps, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getElem?_cons_zero, Option.getD_some, dpSpec]
  | .introduce v child, hval, m, hm => by
    have hm' : m < q * q ^ (bagList child).length := by
      rw [Nat.mul_comm]
      simpa only [bagList, List.length_cons, Nat.pow_succ] using hm
    have hmdiv : m / q < q ^ (bagList child).length := Nat.div_lt_of_lt_mul hm'
    have ih := getD_dpTreeM A q hq sem F hval.2 hmdiv
    have hbagC : (bagList child).toFinset = child.bag := toFinset_bagList hval.2
    have hbagT : (v :: bagList child).toFinset = insert v child.bag := by
      simp [hbagC]
    have hcongr : ∀ u ∈ child.bag,
        ofRadixFin q hq (v :: bagList child) m u =
          ofRadixFin q hq (bagList child) (m / q) u := fun u hu => by
      have huv : u ≠ v := fun h => hval.1 (child.bag_subset_subtreeVerts (h ▸ hu))
      ext
      exact ofRadix_cons_ne huv (bagList child) m
    simp only [dpTreeM, bagList, TimeM.ret_bind]
    rw [getD_tableLoopM _ (by simpa [bagList] using hm) A.zero]
    simp only [time_simps, hbagT, dpSpec]
    rw [ih, dpSpec_congr A q hq sem F F.vars.toFinset hval.2 fun u hu => (hcongr u hu).symm]
  | .forget v child, hval, m, hm => by
    have hbagC : (bagList child).toFinset = child.bag := toFinset_bagList hval.2
    have hret : ∀ d (hd : d < q),
        let idx := (projectUpdateM q v d ((bagList child).erase v) m (bagList child)).ret
        (dpTreeM A q hq sem F F.vars child).ret.getD idx A.zero =
          dpSpec A q hq sem F F.vars.toFinset child
            (Function.update (ofRadixFin q hq ((bagList child).erase v) m) v
              ⟨d, hd⟩) := fun d hd => by
      intro idx
      have hidx : idx < q ^ (bagList child).length := by
        dsimp only [idx]
        rw [ret_projectUpdateM hq]
        exact toRadix_lt hq _ _
      have ih := getD_dpTreeM A q hq sem F hval.2 hidx
      have hagree : ∀ u ∈ child.bag,
          ofRadixFin q hq (bagList child) idx u =
            Function.update (ofRadixFin q hq ((bagList child).erase v) m) v
              ⟨d, hd⟩ u := fun u hu => by
        have huC : u ∈ bagList child := List.mem_toFinset.1 (hbagC ▸ hu)
        have hlt : ∀ w ∈ bagList child,
            Function.update (ofRadix q ((bagList child).erase v) m) v d w < q := by
          intro w _
          by_cases hwv : w = v
          · simpa [hwv] using hd
          · simpa [hwv] using ofRadix_lt hq ((bagList child).erase v) m w
        ext
        dsimp only [idx, ofRadixFin]
        rw [ret_projectUpdateM hq, ofRadix_toRadix hq hlt huC]
        by_cases huv : u = v
        · simp only [huv, Function.update_self]
        · simp only [Function.update_of_ne huv]
          rfl
      rw [ih, dpSpec_congr A q hq sem F F.vars.toFinset hval.2 hagree]
    simp only [dpTreeM, bagList, TimeM.ret_bind]
    rw [getD_tableLoopM _ (by simpa [bagList] using hm) A.zero]
    simp only [ret_memM, dpSpec]
    by_cases hv : v ∈ F.vars
    · have hvF : v ∈ F.vars.toFinset := List.mem_toFinset.2 hv
      simp only [hv, decide_true, ite_true, hvF]
      rw [ret_sumLoopM_eq_dpAlgFold]
      refine dpAlgFold_congr fun d hd => ?_
      simp only [hd, ↓reduceDIte, time_simps]
      exact hret d hd
    · have hvF : v ∉ F.vars.toFinset := by simpa [List.mem_toFinset] using hv
      simp only [hv, decide_false, Bool.false_eq_true, ite_false, hvF, time_simps]
      exact hret 0 hq
  | .join left right, hval, m, hm => by
    have hmL : m < q ^ (bagList left).length := by simpa [bagList] using hm
    have hmR : (projectM q (bagList left) m (bagList right)).ret < q ^ (bagList right).length := by
      rw [ret_projectM hq]
      exact toRadix_lt hq _ _
    have ihL := getD_dpTreeM A q hq sem F hval.2.2.1 hmL
    have ihR := getD_dpTreeM A q hq sem F hval.2.2.2 hmR
    have hbagL : (bagList left).toFinset = left.bag := toFinset_bagList hval.2.2.1
    have hbagR : (bagList right).toFinset = right.bag := toFinset_bagList hval.2.2.2
    have hagree : ∀ u ∈ right.bag,
        ofRadixFin q hq (bagList right) (projectM q (bagList left) m (bagList right)).ret u =
          ofRadixFin q hq (bagList left) m u := fun u hu => by
      have huR : u ∈ bagList right := List.mem_toFinset.1 (hbagR ▸ hu)
      ext
      dsimp only [ofRadixFin]
      rw [ret_projectM hq, ofRadix_toRadix hq
        (fun w _ => ofRadix_lt hq (bagList left) m w) huR]
    simp only [dpTreeM, bagList, TimeM.ret_bind]
    rw [getD_tableLoopM _ (by simpa [bagList] using hm) A.zero]
    simp only [time_simps, dpSpec]
    rw [ihL, ihR, dpSpec_congr A q hq sem F F.vars.toFinset hval.2.2.2 hagree]

private theorem dpSpec_dpCountAlg_eq {q : ℕ} (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) (U : Finset V) :
    ∀ T α, dpSpec dpCountAlg q hq sem F U T α =
      @CSP.specDPCount _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩ sem F U T α
  | .leaf, α => by
    dsimp only [dpSpec, CSP.specDPCount, dpCountAlg]
    exact if_congr (by simp [List.all_eq_true, imp_iff_not_or]) rfl rfl
  | .introduce v child, α => by
    dsimp only [dpSpec, CSP.specDPCount]
    rw [dpSpec_dpCountAlg_eq hq sem F U child α]
    exact if_congr (by simp [List.all_eq_true, imp_iff_not_or, or_assoc]) rfl rfl
  | .forget v child, α => by
    dsimp only [dpSpec, CSP.specDPCount]
    split_ifs with hvU
    · dsimp only [dpCountAlg]
      rw [dpAlgFold_nat, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [dite_eq_left d.isLt, Fin.eta]
      exact dpSpec_dpCountAlg_eq hq sem F U child _
    · exact dpSpec_dpCountAlg_eq hq sem F U child _
  | .join left right, α => by
    dsimp only [dpSpec, CSP.specDPCount]
    rw [dpSpec_dpCountAlg_eq hq sem F U left α, dpSpec_dpCountAlg_eq hq sem F U right α]
    rfl

private theorem dpSpec_dpDecideAlg_eq {q : ℕ} (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) (U : Finset V) :
    ∀ T α, dpSpec dpDecideAlg q hq sem F U T α =
      @CSP.specDPDecide _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩ sem F U T α
  | .leaf, α => by
    dsimp only [dpSpec, CSP.specDPDecide, dpDecideAlg]
    cases h : F.all fun c => !decide (c.scope = []) || c.eval sem (fun _ => ⟨0, hq⟩) <;> simp
  | .introduce v child, α => by
    dsimp only [dpSpec, CSP.specDPDecide]
    rw [dpSpec_dpDecideAlg_eq hq sem F U child α]
    have hall : (F.all fun c => !(decide (c.scope.toFinset ⊆ insert v child.bag) &&
        decide (v ∈ c.scope)) || c.eval sem α) =
      (F.all fun c => !decide (c.scope.toFinset ⊆ insert v child.bag) ||
        !decide (v ∈ c.scope) || c.eval sem α) := by
      simp only [Bool.not_and, Bool.or_assoc]
    rw [hall]
    dsimp only [dpDecideAlg]
    cases h : F.all fun c => !decide (c.scope.toFinset ⊆ insert v child.bag) ||
        !decide (v ∈ c.scope) || c.eval sem α <;> simp
  | .forget v child, α => by
    dsimp only [dpSpec, CSP.specDPDecide]
    split_ifs with hvU
    · rw [show dpAlgFold dpDecideAlg.zero dpDecideAlg.add = dpAlgFold false (· || ·) from rfl,
        dpAlgFold_bool]
      congr 1
      simp only [eq_iff_iff]
      refine ⟨fun ⟨d, hd, h⟩ => ⟨⟨d, hd⟩, ?_⟩, fun ⟨d, h⟩ => ⟨d.1, d.isLt, ?_⟩⟩
      · simpa only [dite_eq_left hd, dpSpec_dpDecideAlg_eq] using h
      · simpa only [dite_eq_left d.isLt, Fin.eta, dpSpec_dpDecideAlg_eq] using h
    · exact dpSpec_dpDecideAlg_eq hq sem F U child _
  | .join left right, α => by
    dsimp only [dpSpec, CSP.specDPDecide]
    rw [dpSpec_dpDecideAlg_eq hq sem F U left α, dpSpec_dpDecideAlg_eq hq sem F U right α]
    rfl

theorem getD_cspCountTreeM {q : ℕ} (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) {T : NiceTree V} (hval : T.LocalValid) {m : ℕ}
    (hm : m < q ^ (bagList T).length) :
    (cspCountTreeM q hq sem F F.vars T).ret.getD m 0 =
      @CSP.specDPCount _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩
        sem F F.vars.toFinset T (ofRadixFin q hq (bagList T) m) :=
  (getD_dpTreeM dpCountAlg q hq sem F hval hm).trans (dpSpec_dpCountAlg_eq hq sem F _ _ _)

theorem getD_cspDecideTreeM {q : ℕ} (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) {T : NiceTree V} (hval : T.LocalValid) {m : ℕ}
    (hm : m < q ^ (bagList T).length) :
    (cspDecideTreeM q hq sem F F.vars T).ret.getD m false =
      @CSP.specDPDecide _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩
        sem F F.vars.toFinset T (ofRadixFin q hq (bagList T) m) :=
  (getD_dpTreeM dpDecideAlg q hq sem F hval hm).trans (dpSpec_dpDecideAlg_eq hq sem F _ _ _)

end Correctness

/-! ### Top-level CSP solvers on nice and rooted tree decompositions -/

section Wrappers

variable {Rel V : Type*} [DecidableEq V]

/-- Exact model count computed from a supplied nice tree `T`. -/
@[expose] def cspCountNiceTreeM (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) (T : NiceTree V) : TimeM ℕ ℕ := do
  let tbl ← cspCountTreeM q hq sem F F.vars T
  pure (tbl.getD 0 0)

/-- Satisfiability decision computed from a supplied nice tree `T`. -/
@[expose] def cspDecideNiceTreeM (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) (T : NiceTree V) : TimeM ℕ Bool := do
  let tbl ← cspDecideTreeM q hq sem F F.vars T
  pure (tbl.getD 0 false)

theorem ret_cspCountNiceTreeM {q : ℕ} (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    {F : CSP Rel V} {T : NiceTree V} (hval : T.LocalValid) (hbag : T.bag = ∅)
    (hsub : F.vars.toFinset ⊆ T.subtreeVerts) (hcov : ∀ c ∈ F, T.CoversFinset c.scope.toFinset) :
    (cspCountNiceTreeM q hq sem F T).ret =
      @CSP.modelCount _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩ sem F := by
  have hm : 0 < q ^ (bagList T).length := Nat.one_le_pow _ _ hq
  simp only [cspCountNiceTreeM, time_simps, getD_cspCountTreeM hq sem F hval hm]
  exact @CSP.specDPCount_eq_modelCount _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩
    sem F T hval hbag hsub hcov _

theorem ret_cspDecideNiceTreeM {q : ℕ} (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    {F : CSP Rel V} {T : NiceTree V} (hval : T.LocalValid) (hbag : T.bag = ∅)
    (hsub : F.vars.toFinset ⊆ T.subtreeVerts) (hcov : ∀ c ∈ F, T.CoversFinset c.scope.toFinset) :
    (cspDecideNiceTreeM q hq sem F T).ret = true ↔
      CSP.Satisfiable sem F := by
  have hm : 0 < q ^ (bagList T).length := Nat.one_le_pow _ _ hq
  simp only [cspDecideNiceTreeM, time_simps, getD_cspDecideTreeM hq sem F hval hm]
  exact @CSP.specDPDecide_eq_true_iff_satisfiable _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩
    sem F T hval hbag hsub hcov _

theorem time_cspCountNiceTreeM_le (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) {T : NiceTree V} (hval : T.LocalValid) :
    (cspCountNiceTreeM q hq sem F T).time ≤
      T.size * (q ^ (T.width + 1) * dpNodeCost T.width F) := by
  simpa [cspCountNiceTreeM] using time_cspCountTreeM_le q hq sem F hval

theorem time_cspDecideNiceTreeM_le (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) {T : NiceTree V} (hval : T.LocalValid) :
    (cspDecideNiceTreeM q hq sem F T).time ≤
      T.size * (q ^ (T.width + 1) * dpNodeCost T.width F) := by
  simpa [cspDecideNiceTreeM] using time_cspDecideTreeM_le q hq sem F hval

/-- Exact model count on a nice tree decomposition of `F.primalGraph`. -/
@[expose] def cspCountNiceM (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) (N : F.primalGraph.NiceTreeDecomposition) : TimeM ℕ ℕ :=
  cspCountNiceTreeM q hq sem F N.tree

/-- Satisfiability decision on a nice tree decomposition of `F.primalGraph`. -/
@[expose] def cspDecideNiceM (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) (N : F.primalGraph.NiceTreeDecomposition) : TimeM ℕ Bool :=
  cspDecideNiceTreeM q hq sem F N.tree

theorem ret_cspCountNiceM {q : ℕ} (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    {F : CSP Rel V} (N : F.primalGraph.NiceTreeDecomposition) :
    (cspCountNiceM q hq sem F N).ret =
      @CSP.modelCount _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩ sem F :=
  ret_cspCountNiceTreeM hq sem N.localValid N.bag_root (fun v _ => N.exists_mem_bag v)
    (fun _ hc => F.exists_coversFinset_scope_of_mem N hc)

theorem ret_cspDecideNiceM {q : ℕ} (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    {F : CSP Rel V} (N : F.primalGraph.NiceTreeDecomposition) :
    (cspDecideNiceM q hq sem F N).ret = true ↔ CSP.Satisfiable sem F :=
  ret_cspDecideNiceTreeM hq sem N.localValid N.bag_root (fun v _ => N.exists_mem_bag v)
    (fun _ hc => F.exists_coversFinset_scope_of_mem N hc)

theorem time_cspCountNiceM_le (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) (N : F.primalGraph.NiceTreeDecomposition) :
    (cspCountNiceM q hq sem F N).time ≤
      N.size * (q ^ (N.width + 1) * dpNodeCost N.width F) :=
  time_cspCountNiceTreeM_le q hq sem F N.localValid

theorem time_cspDecideNiceM_le (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) (N : F.primalGraph.NiceTreeDecomposition) :
    (cspDecideNiceM q hq sem F N).time ≤
      N.size * (q ^ (N.width + 1) * dpNodeCost N.width F) :=
  time_cspDecideNiceTreeM_le q hq sem F N.localValid

/-- Exact model count on a nice tree decomposition of `F.activePrimalGraph`. -/
@[expose] def cspCountActiveNiceM (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) (N : F.activePrimalGraph.NiceTreeDecomposition) : TimeM ℕ ℕ :=
  cspCountNiceTreeM q hq sem F (CSP.liftActiveNiceTree N)

/-- Satisfiability decision on a nice tree decomposition of `F.activePrimalGraph`. -/
@[expose] def cspDecideActiveNiceM (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) (N : F.activePrimalGraph.NiceTreeDecomposition) : TimeM ℕ Bool :=
  cspDecideNiceTreeM q hq sem F (CSP.liftActiveNiceTree N)

theorem ret_cspCountActiveNiceM {q : ℕ} (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    {F : CSP Rel V} (N : F.activePrimalGraph.NiceTreeDecomposition) :
    (cspCountActiveNiceM q hq sem F N).ret =
      @CSP.modelCount _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩ sem F :=
  ret_cspCountNiceTreeM hq sem (CSP.liftActiveNiceTree_localValid N)
    (CSP.liftActiveNiceTree_bag N) (by rw [CSP.liftActiveNiceTree_subtreeVerts])
    (fun _ hc => CSP.liftActiveNiceTree_coversFinset N hc)

theorem ret_cspDecideActiveNiceM {q : ℕ} (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    {F : CSP Rel V} (N : F.activePrimalGraph.NiceTreeDecomposition) :
    (cspDecideActiveNiceM q hq sem F N).ret = true ↔ CSP.Satisfiable sem F :=
  ret_cspDecideNiceTreeM hq sem (CSP.liftActiveNiceTree_localValid N)
    (CSP.liftActiveNiceTree_bag N) (by rw [CSP.liftActiveNiceTree_subtreeVerts])
    (fun _ hc => CSP.liftActiveNiceTree_coversFinset N hc)

theorem time_cspCountActiveNiceM_le (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) (N : F.activePrimalGraph.NiceTreeDecomposition) :
    (cspCountActiveNiceM q hq sem F N).time ≤
      N.size * (q ^ (N.width + 1) * dpNodeCost N.width F) := by
  have h := time_cspCountNiceTreeM_le q hq sem F (CSP.liftActiveNiceTree_localValid N)
  rwa [CSP.liftActiveNiceTree_size, CSP.liftActiveNiceTree_width] at h

theorem time_cspDecideActiveNiceM_le (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) (N : F.activePrimalGraph.NiceTreeDecomposition) :
    (cspDecideActiveNiceM q hq sem F N).time ≤
      N.size * (q ^ (N.width + 1) * dpNodeCost N.width F) := by
  have h := time_cspDecideNiceTreeM_le q hq sem F (CSP.liftActiveNiceTree_localValid N)
  rwa [CSP.liftActiveNiceTree_size, CSP.liftActiveNiceTree_width] at h

/-- Exact model count on a rooted tree decomposition of `F.primalGraph` via `toNiceTreePruned`. -/
@[expose] def cspCountRootedM [LinearOrder V] (q : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) {n : ℕ}
    (R : F.primalGraph.RootedTreeDecomposition n) : TimeM ℕ ℕ :=
  cspCountNiceM q hq sem F R.toNiceTreePruned

/-- Satisfiability decision on a rooted tree decomposition of `F.primalGraph` via
`toNiceTreePruned`. -/
@[expose] def cspDecideRootedM [LinearOrder V] (q : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) {n : ℕ}
    (R : F.primalGraph.RootedTreeDecomposition n) : TimeM ℕ Bool :=
  cspDecideNiceM q hq sem F R.toNiceTreePruned

theorem ret_cspCountRootedM [LinearOrder V] {q : ℕ} (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) {F : CSP Rel V} {n : ℕ}
    (R : F.primalGraph.RootedTreeDecomposition n) :
    (cspCountRootedM q hq sem F R).ret =
      @CSP.modelCount _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩ sem F :=
  ret_cspCountNiceM hq sem R.toNiceTreePruned

theorem ret_cspDecideRootedM [LinearOrder V] {q : ℕ} (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) {F : CSP Rel V} {n : ℕ}
    (R : F.primalGraph.RootedTreeDecomposition n) :
    (cspDecideRootedM q hq sem F R).ret = true ↔ CSP.Satisfiable sem F :=
  ret_cspDecideNiceM hq sem R.toNiceTreePruned

theorem time_cspCountRootedM_le [LinearOrder V] [Fintype V] (q : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) {n : ℕ}
    (R : F.primalGraph.RootedTreeDecomposition n) :
    (cspCountRootedM q hq sem F R).time ≤
      (3 * R.width + 5) * (Fintype.card V + 1) * (q ^ (R.width + 1) * dpNodeCost R.width F) :=
  (time_cspCountNiceM_le q hq sem F R.toNiceTreePruned).trans
    (Nat.mul_le_mul R.toNiceTreePruned_size_le (treeCost_mono hq R.toNiceTreePruned_width_le F))

theorem time_cspDecideRootedM_le [LinearOrder V] [Fintype V] (q : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) {n : ℕ}
    (R : F.primalGraph.RootedTreeDecomposition n) :
    (cspDecideRootedM q hq sem F R).time ≤
      (3 * R.width + 5) * (Fintype.card V + 1) * (q ^ (R.width + 1) * dpNodeCost R.width F) :=
  (time_cspDecideNiceM_le q hq sem F R.toNiceTreePruned).trans
    (Nat.mul_le_mul R.toNiceTreePruned_size_le (treeCost_mono hq R.toNiceTreePruned_width_le F))

/-- Exact model count on a rooted tree decomposition of `F.activePrimalGraph` via
`toNiceTreePruned`. -/
@[expose] def cspCountActiveRootedM [LinearOrder V] (q : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) {n : ℕ}
    (R : F.activePrimalGraph.RootedTreeDecomposition n) : TimeM ℕ ℕ :=
  cspCountActiveNiceM q hq sem F R.toNiceTreePruned

/-- Satisfiability decision on a rooted tree decomposition of `F.activePrimalGraph` via
`toNiceTreePruned`. -/
@[expose] def cspDecideActiveRootedM [LinearOrder V] (q : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) {n : ℕ}
    (R : F.activePrimalGraph.RootedTreeDecomposition n) : TimeM ℕ Bool :=
  cspDecideActiveNiceM q hq sem F R.toNiceTreePruned

theorem ret_cspCountActiveRootedM [LinearOrder V] {q : ℕ} (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) {F : CSP Rel V} {n : ℕ}
    (R : F.activePrimalGraph.RootedTreeDecomposition n) :
    (cspCountActiveRootedM q hq sem F R).ret =
      @CSP.modelCount _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩ sem F :=
  ret_cspCountActiveNiceM hq sem R.toNiceTreePruned

theorem ret_cspDecideActiveRootedM [LinearOrder V] {q : ℕ} (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) {F : CSP Rel V} {n : ℕ}
    (R : F.activePrimalGraph.RootedTreeDecomposition n) :
    (cspDecideActiveRootedM q hq sem F R).ret = true ↔ CSP.Satisfiable sem F :=
  ret_cspDecideActiveNiceM hq sem R.toNiceTreePruned

theorem time_cspCountActiveRootedM_le [LinearOrder V] (q : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) {n : ℕ}
    (R : F.activePrimalGraph.RootedTreeDecomposition n) :
    (cspCountActiveRootedM q hq sem F R).time ≤
      (3 * R.width + 5) * (F.vars.toFinset.card + 1) *
        (q ^ (R.width + 1) * dpNodeCost R.width F) := by
  have hs := R.toNiceTreePruned_size_le
  rw [Fintype.card_coe] at hs
  exact (time_cspCountActiveNiceM_le q hq sem F R.toNiceTreePruned).trans
    (Nat.mul_le_mul hs (treeCost_mono hq R.toNiceTreePruned_width_le F))

theorem time_cspDecideActiveRootedM_le [LinearOrder V] (q : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) {n : ℕ}
    (R : F.activePrimalGraph.RootedTreeDecomposition n) :
    (cspDecideActiveRootedM q hq sem F R).time ≤
      (3 * R.width + 5) * (F.vars.toFinset.card + 1) *
        (q ^ (R.width + 1) * dpNodeCost R.width F) := by
  have hs := R.toNiceTreePruned_size_le
  rw [Fintype.card_coe] at hs
  exact (time_cspDecideActiveNiceM_le q hq sem F R.toNiceTreePruned).trans
    (Nat.mul_le_mul hs (treeCost_mono hq R.toNiceTreePruned_width_le F))

end Wrappers

/-! ### Finite inhabited domain equivalence bridge -/

section DomainBridge

variable {Rel V D : Type*} [DecidableEq V] [Fintype D] [Inhabited D]

/-- Pull back constraint semantics across `e : D ≃ Fin q`. -/
@[expose] def semFin {q : ℕ} (sem : Rel → List D → Bool) (e : D ≃ Fin q) :
    Rel → List (Fin q) → Bool :=
  fun r xs => sem r (xs.map e.symm)

omit [DecidableEq V] [Fintype D] [Inhabited D] in
theorem eval_semFin {q : ℕ} (sem : Rel → List D → Bool) (e : D ≃ Fin q)
    (σ : V → Fin q) (F : CSP Rel V) :
    CSP.eval (semFin sem e) σ F = CSP.eval sem (fun v => e.symm (σ v)) F := by
  unfold CSP.eval Constraint.eval semFin
  simp only [List.map_map]
  rfl

omit [DecidableEq V] [Fintype D] [Inhabited D] in
theorem satisfiable_semFin_iff {q : ℕ} (sem : Rel → List D → Bool) (e : D ≃ Fin q)
    (F : CSP Rel V) :
    CSP.Satisfiable (semFin sem e) F ↔ CSP.Satisfiable sem F := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨fun v => e.symm (σ v), (eval_semFin sem e σ F).symm ▸ hσ⟩
  · rintro ⟨τ, hτ⟩
    refine ⟨fun v => e (τ v), ?_⟩
    rw [eval_semFin]
    simpa [Function.comp_def] using hτ

theorem modelCount_semFin {q : ℕ} (hq : 0 < q) (sem : Rel → List D → Bool) (e : D ≃ Fin q)
    (F : CSP Rel V) :
    @CSP.modelCount _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩ (semFin sem e) F =
      CSP.modelCount sem F := by
  classical
  let _ : Inhabited (Fin q) := ⟨⟨0, hq⟩⟩
  unfold CSP.modelCount CSP.modelCountOn
  refine Finset.card_bij (fun σ _ v => e.symm (σ v)) ?_ (fun _ _ _ _ h => funext fun v =>
      e.symm.injective (congrFun h v)) ?_
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    rw [eval_semFin] at hσ
    exact (CSP.eval_congr fun v hv => by simp [List.mem_toFinset.2 hv]).trans hσ
  · intro τ hτ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
    refine ⟨fun v => e (τ v), Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, funext fun v => by simp⟩
    rw [eval_semFin]
    exact (CSP.eval_congr fun v hv => by simp [List.mem_toFinset.2 hv]).trans hτ

theorem ret_cspCountNiceM_equiv (sem : Rel → List D → Bool) {F : CSP Rel V}
    (N : F.primalGraph.NiceTreeDecomposition) (e : D ≃ Fin (Fintype.card D)) :
    (cspCountNiceM (Fintype.card D) Fintype.card_pos (semFin sem e) F N).ret =
      CSP.modelCount sem F := by
  rw [ret_cspCountNiceM Fintype.card_pos (semFin sem e) N,
    modelCount_semFin Fintype.card_pos sem e F]

theorem ret_cspDecideNiceM_equiv (sem : Rel → List D → Bool) {F : CSP Rel V}
    (N : F.primalGraph.NiceTreeDecomposition) (e : D ≃ Fin (Fintype.card D)) :
    (cspDecideNiceM (Fintype.card D) Fintype.card_pos (semFin sem e) F N).ret = true ↔
      CSP.Satisfiable sem F :=
  (ret_cspDecideNiceM Fintype.card_pos (semFin sem e) N).trans (satisfiable_semFin_iff sem e F)

end DomainBridge

end Cslib.Algorithms.Lean.TreeDecomposition
