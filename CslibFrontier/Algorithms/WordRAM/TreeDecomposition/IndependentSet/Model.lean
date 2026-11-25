/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.Instance
import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.InstDP
import Mathlib.Data.List.OfFn

/-!
# Serialized MWIS instance result and rooted-decomposition bridge

This module defines `MWISInstance.result` (unexposed) over the private `ℕ`-indexed dynamic
program in `InstDP`, proves its equivalence with `mwisFPT` and `mwisValue`
(`MWISInstance.result_ofRooted_eq_mwisFPT`, `MWISInstance.result_ofRooted`), and publicly
re-exports `IndependentSet.Instance`.

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.encodeBag`: length-prefixed bag word list.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.MWISInstance`: flat word-serializable instance bundle
  with `MWISInstance.encode`, `MWISInstance.result`, `MWISInstance.maxBagLen`,
  `MWISInstance.maxWeight`, `MWISInstance.wordBound`, `MWISInstance.stepBound`, and
  `MWISInstance.ofRooted`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.mwisFPTBound`: closed-form width-`k` step bound
  `6 + (n + 1) * (2 ^ (k + 1) * (5 * (k + 1) ^ 2 + 6 * (k + 1) + 32))`.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.MWISInstance.result_ofRooted_eq_mwisFPT`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.MWISInstance.result_ofRooted`:
  `MWISInstance.ofRooted` agrees with `mwisFPT R w L`, and equals `mwisValue R w` under
  `IsBagOrder R L`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.MWISInstance.maxBagLen_ofRooted_le`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.MWISInstance.stepBound_ofRooted_le`: width-`k`
  bounds on `maxBagLen` and `stepBound`.
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open SimpleGraph
open Cslib.Algorithms.Lean.TreeDecomposition

/-- Pure dynamic-programming value computed on `inst`. -/
def MWISInstance.result (inst : MWISInstance) : ℕ :=
  let st := tablesInst inst.adj inst.wt inst.numNodes inst.parFin inst.bagAt inst.numNodes
  rootPassInst inst.adj inst.wt (inst.bagAt 0) st[(0 : Fin (inst.numNodes + 1))]
    (2 ^ (inst.bagAt 0).length)

/-! ### Bridge between `MWISInstance.ofRooted` and `mwisFPT` / `mwisValue` -/

section RootedBridge

private theorem memBag_map_inj {V : Type*} [DecidableEq V] {f : V → ℕ}
    (hf : Function.Injective f) (x : V) (L : List V) :
    memBag (f x) (L.map f) = memBag x L := by
  induction L with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, memBag, ih, hf.eq_iff]

private theorem selMemMask_map_inj {V : Type*} [DecidableEq V] {f : V → ℕ}
    (hf : Function.Injective f) (x : V) (L : List V) (m : ℕ) :
    selMemMask (f x) (L.map f) m = selMemMask x L m := by
  induction L generalizing m with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, selMemMask, ih, hf.eq_iff]

private theorem keyMask_map_inj {V : Type*} [DecidableEq V] {f : V → ℕ}
    (hf : Function.Injective f) (LB LP : List V) (t : ℕ) :
    keyMask (LB.map f) (LP.map f) t = keyMask LB LP t := by
  induction LP with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, keyMask, ih, selMemMask_map_inj hf]

private theorem restrictMask_map_inj {V : Type*} [DecidableEq V] {f : V → ℕ}
    (hf : Function.Injective f) (LB LP : List V) (s : ℕ) :
    restrictMask (LB.map f) (LP.map f) s = restrictMask LB LP s := by
  induction LP generalizing s with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, restrictMask, ih, memBag_map_inj hf]

private theorem forgetWeight_map_inj {V : Type*} [DecidableEq V] {f : V → ℕ}
    (hf : Function.Injective f) {wtNat : ℕ → ℕ} {w : V → ℕ}
    (LP LB : List V) (hw : ∀ u ∈ LB, wtNat (f u) = w u) (t : ℕ) :
    forgetWeight wtNat (LP.map f) (LB.map f) t = forgetWeight w LP LB t := by
  induction LB generalizing t with
  | nil => rfl
  | cons u LB ih =>
    simp only [List.map_cons, forgetWeight, memBag_map_inj hf, hw u List.mem_cons_self,
      ih fun v hv => hw v (List.mem_cons_of_mem u hv)]

private theorem noAdjInst_map {V : Type*} {G : SimpleGraph V}
    [DecidableRel G.Adj] {f : V → ℕ} {adj : ℕ → ℕ → Bool}
    (hadj : ∀ x u, adj (f x) (f u) = decide (G.Adj x u)) (x : V) (L : List V) (m : ℕ) :
    noAdjInst adj (f x) (L.map f) m = noAdjMask G x L m := by
  induction L generalizing m with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, noAdjInst, noAdjMask, ih, hadj]

private theorem indepInst_map {V : Type*} {G : SimpleGraph V}
    [DecidableRel G.Adj] {f : V → ℕ} {adj : ℕ → ℕ → Bool}
    (hadj : ∀ x u, adj (f x) (f u) = decide (G.Adj x u)) (L : List V) (m : ℕ) :
    indepInst adj (L.map f) m = indepMask G L m := by
  induction L generalizing m with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, indepInst, indepMask, ih, noAdjInst_map hadj]

private theorem childPassInst_map {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {f : V → ℕ} (hf : Function.Injective f)
    {adj : ℕ → ℕ → Bool} (hadj : ∀ x u, adj (f x) (f u) = decide (G.Adj x u))
    {wtNat : ℕ → ℕ} {w : V → ℕ} (hw : ∀ x, wtNat (f x) = w x)
    (LB LP : List V) (tbl init : Array ℕ) (c : ℕ) :
    childPassInst adj wtNat (LB.map f) (LP.map f) tbl init c =
      childPass G w LB LP tbl init c := by
  induction c with
  | zero => rfl
  | succ _ ih =>
    simp only [childPassInst, childPass, ih, indepInst_map hadj, keyMask_map_inj hf,
      forgetWeight_map_inj hf LP LB fun u _ => hw u]

private theorem parentPass_map_inj {V : Type*} [DecidableEq V] {f : V → ℕ}
    (hf : Function.Injective f) (LB LP : List V) (old best : Array ℕ) (c : ℕ) :
    parentPass (LB.map f) (LP.map f) old best c = parentPass LB LP old best c := by
  induction c with
  | zero => rfl
  | succ _ ih => simp only [parentPass, ih, restrictMask_map_inj hf]

private theorem rootPassInst_map {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {f : V → ℕ} (hf : Function.Injective f)
    {adj : ℕ → ℕ → Bool} (hadj : ∀ x u, adj (f x) (f u) = decide (G.Adj x u))
    {wtNat : ℕ → ℕ} {w : V → ℕ} (hw : ∀ x, wtNat (f x) = w x)
    (L : List V) (tbl : Array ℕ) (c : ℕ) :
    rootPassInst adj wtNat (L.map f) tbl c = rootPass G w L tbl c := by
  induction c with
  | zero => rfl
  | succ c ih =>
    have hfw := forgetWeight_map_inj hf (w := w) (wtNat := wtNat) [] L (fun u _ => hw u) c
    simp only [List.map_nil] at hfw
    simp only [rootPassInst, rootPass, ih, indepInst_map hadj, hfw]

/-- `MWISInstance.ofRooted` agrees with `mwisFPT R w L`, and equals `mwisValue R w` whenever
`IsBagOrder R L`. -/
theorem MWISInstance.result_ofRooted_eq_mwisFPT {V : Type*} {G : SimpleGraph V}
    [DecidableEq V] [DecidableRel G.Adj] {m n : ℕ} (e : V ≃ Fin m)
    (R : G.RootedTreeDecomposition n) (w : V → ℕ) (L : Fin (n + 1) → List V) :
    (MWISInstance.ofRooted e R w L).result = mwisFPT R w L := by
  let inst := MWISInstance.ofRooted e R w L
  let f : V → ℕ := fun v => (e v).val
  have hf : Function.Injective f := fun _ _ h => e.injective (Fin.ext h)
  have hw (x : V) : inst.wt (f x) = w x := by
    dsimp only [inst, MWISInstance.wt, MWISInstance.ofRooted, f]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left (e x).isLt,
      Option.getD_some, Fin.eta, Equiv.symm_apply_apply]
  have hadj (x u : V) : inst.adj (f x) (f u) = decide (G.Adj x u) := by
    dsimp only [inst, MWISInstance.adj, MWISInstance.ofRooted, f]
    have hm : 0 < m := Nat.zero_lt_of_lt (e x).isLt
    have hlt : (e x).val * m + (e u).val < m * m :=
      calc (e x).val * m + (e u).val < (e x).val * m + m := Nat.add_lt_add_left (e u).isLt _
        _ = ((e x).val + 1) * m := by rw [Nat.succ_mul]
        _ ≤ m * m := Nat.mul_le_mul_right m (e x).isLt
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hlt, Option.getD_some]
    have hdiv : ((e x).val * m + (e u).val) / m = (e x).val := by
      rw [Nat.mul_comm, Nat.mul_add_div hm, Nat.div_eq_of_lt (e u).isLt, Nat.add_zero]
    have hmod : ((e x).val * m + (e u).val) % m = (e u).val := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (e u).isLt]
    simp only [hdiv, hmod, Fin.eta, Equiv.symm_apply_apply]
    by_cases h : G.Adj x u <;> simp [h]
  have hpar_eq (i : Fin (n + 1)) : inst.parFin i = R.parent i := Fin.ext <| by
    by_cases hi : 1 ≤ i.val
    · simp only [MWISInstance.parFin, hi, ↓reduceDIte, inst, MWISInstance.ofRooted,
        Fin.getElem_fin, List.getElem_ofFn, Fin.eta]
    · obtain rfl : i = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
      simp [MWISInstance.parFin, R.parent_zero]
  have hbag (i : Fin (n + 1)) : inst.bagAt i = (L i).map f := by
    simp only [MWISInstance.bagAt, inst, MWISInstance.ofRooted, List.getElem_ofFn, Fin.eta, f]
  have htbl (t : ℕ) :
      tablesInst inst.adj inst.wt n inst.parFin inst.bagAt t = tablesFPT R w L t := by
    induction t with
    | zero => exact tablesInst_zero inst.adj inst.wt n inst.parFin inst.bagAt
    | succ t ih =>
      refine (tablesInst_succ inst.adj inst.wt n inst.parFin inst.bagAt t).trans ?_
      simp only [ih, tablesFPT, processNode, hpar_eq, hbag, List.length_map,
        childPassInst_map hf hadj hw, parentPass_map_inj hf]
  change rootPassInst inst.adj inst.wt (inst.bagAt (0 : Fin (n + 1)))
      (tablesInst inst.adj inst.wt n inst.parFin inst.bagAt n)[(0 : Fin (n + 1))]
      (2 ^ (inst.bagAt (0 : Fin (n + 1))).length) = mwisFPT R w L
  rw [htbl n, hbag (0 : Fin (n + 1)), List.length_map, rootPassInst_map hf hadj hw]; rfl

/-- When `IsBagOrder R L`, `(MWISInstance.ofRooted e R w L).result = mwisValue R w`. -/
theorem MWISInstance.result_ofRooted {V : Type*} {G : SimpleGraph V}
    [DecidableEq V] [DecidableRel G.Adj] {m n : ℕ} (e : V ≃ Fin m)
    (R : G.RootedTreeDecomposition n) (w : V → ℕ) {L : Fin (n + 1) → List V}
    (hL : IsBagOrder R L) :
    (MWISInstance.ofRooted e R w L).result = mwisValue R w :=
  (MWISInstance.result_ofRooted_eq_mwisFPT e R w L).trans (mwisFPT_eq_mwisValue R w hL)

end RootedBridge

end Cslib.Algorithms.WordRAM.TreeDecomposition
