/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.InstDP
public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.Scan
import CslibFrontier.Tactic.Realize

/-!
# Pairwise bag-independence Word-RAM scan (`indepBagProg`)

This module certifies the pairwise adjacency-matrix scan testing whether a bit-mask-selected subset
of a materialized bag slice is independent under a flattened `m × m` row-major adjacency matrix:

* `noAdjScanProg` (private): tests non-adjacency of a single vertex `x` against a masked bag tail.
* `indepBagProg`: tests pairwise independence (`indepInst`) across a masked bag slice in
  `bagLen * (2 * bagLen + 1)` memory operations.

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.IndepBagArgs`: register arguments for `indepBagProg`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.indepBagProg`: pairwise bag-independence check.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.indepBagProg_state`: `indepBagProg` leaves memory
  unchanged.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.indepBagProg_spec`: validity, functional correctness
  against `indepInst`, and `bagLen * (2 * bagLen + 1)` cost bound.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.indepBagProg_realizes`: exact-basis Word-RAM
  realization certificate.
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### Single-vertex non-adjacency scan (`noAdjScanProg`) -/

private structure NoAdjArgs where
  numVerts : ℕ
  adjPtr : ℕ
  x : ℕ
  ptr : ℕ
  len : ℕ
  mask : ℕ

private def NoAdjArgs.equiv : NoAdjArgs ≃ ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a := (((((a.numVerts, a.adjPtr), a.x), a.ptr), a.len), a.mask)
  invFun := fun (((((nv, ap), x), ptr), len), mask) => ⟨nv, ap, x, ptr, len, mask⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding NoAdjArgs := .ofEquiv NoAdjArgs.equiv

private structure NoAdjEnv where
  numVerts : ℕ
  adjPtr : ℕ
  x : ℕ

private def NoAdjEnv.equiv : NoAdjEnv ≃ (ℕ × ℕ) × ℕ where
  toFun e := ((e.numVerts, e.adjPtr), e.x)
  invFun := fun ((nv, ap), x) => ⟨nv, ap, x⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding NoAdjEnv := .ofEquiv NoAdjEnv.equiv

private structure NoAdjState where
  cur : ℕ
  curM : ℕ
  ok : ℕ

private def NoAdjState.equiv : NoAdjState ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.cur, s.curM), s.ok)
  invFun := fun ((cur, curM), ok) => ⟨cur, curM, ok⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding NoAdjState := .ofEquiv NoAdjState.equiv

private def noAdjStep (p : NoAdjEnv × NoAdjState) : Memory.Prog NoAdjState := do
  let env := p.1
  let st := p.2
  let u ← Memory.read st.cur
  let entry ← Memory.read (env.adjPtr + env.x * env.numVerts + u)
  let bit := st.curM % 2
  let ok' := if st.ok = 1 then
      if bit = 1 then
        if entry = 0 then 1 else 0
      else 1
    else 0
  pure ⟨st.cur + 1, st.curM / 2, ok'⟩

private def noAdjScanProg (args : NoAdjArgs) : Memory.Prog ℕ := do
  let res ← iterate noAdjStep ⟨args.numVerts, args.adjPtr, args.x⟩ args.len
    ⟨args.ptr, args.mask, 1⟩
  pure res.ok

private theorem noAdjScanProg_state (args : NoAdjArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (noAdjScanProg args) = s := by
  unfold noAdjScanProg
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of noAdjStep ⟨args.numVerts, args.adjPtr, args.x⟩
    (fun _ _ => rfl) args.len ⟨args.ptr, args.mask, 1⟩ s

private theorem noAdjScanProg_spec {w m : ℕ} (args : NoAdjArgs) {adjL xs : List ℕ}
    {s : Memory.State}
    (hadj : HoldsIn args.adjPtr adjL s) (hadj_len : adjL.length = m * m)
    (hnv : args.numVerts = m) (hx : args.x < m)
    (hxs : HoldsIn args.ptr xs s) (hlen : xs.length = args.len)
    (hxs_lt : ∀ u ∈ xs, u < m) :
    let adj := fun u v => decide (adjL.getD (u * m + v) 0 ≠ 0)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (noAdjScanProg args)) ∧
    (Memory.spec 0).clientState s (noAdjScanProg args) = s ∧
    (Memory.spec 0).clientResult s (noAdjScanProg args) =
      (if noAdjInst adj args.x xs args.mask then 1 else 0) ∧
    memoryCost (noAdjScanProg args) s ≤ 2 * args.len := by
  let adj := fun u v => decide (adjL.getD (u * m + v) 0 ≠ 0)
  let env : NoAdjEnv := ⟨args.numVerts, args.adjPtr, args.x⟩
  have hcost : memoryCost (noAdjScanProg args) s ≤ 2 * args.len := by
    unfold noAdjScanProg
    rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
    have hle := memoryCost_iterate_le_of noAdjStep 2 env (fun _ _ => le_rfl)
      args.len ⟨args.ptr, args.mask, 1⟩ s
    omega
  suffices ∀ ys cur curM ok, HoldsIn cur ys s → (∀ u ∈ ys, u < m) →
      (ok = 0 ∨ ok = 1) →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (iterate noAdjStep env ys.length ⟨cur, curM, ok⟩)) ∧
      ((Memory.spec 0).clientResult s
        (iterate noAdjStep env ys.length ⟨cur, curM, ok⟩)).ok =
        if ok = 1 ∧ noAdjInst adj args.x ys curM = true then 1 else 0 by
    have hrun := this xs args.ptr args.mask 1 hxs hxs_lt (.inr rfl)
    rw [hlen] at hrun
    refine ⟨?_, noAdjScanProg_state args s, ?_, hcost⟩
    · unfold noAdjScanProg
      exact validHistory_bind_step hrun.1 (validHistory_pure w _ _)
    · unfold noAdjScanProg
      rw [StateTransitionSpec.clientResult_bind]
      change ((Memory.spec 0).clientResult s
        (iterate noAdjStep env args.len ⟨args.ptr, args.mask, 1⟩)).ok = _
      rw [hrun.2]
      cases noAdjInst adj args.x xs args.mask <;> rfl
  intro ys
  induction ys with
  | nil =>
    intro cur curM ok _ _ hok
    have h0 : iterate noAdjStep env 0 ⟨cur, curM, ok⟩ = pure ⟨cur, curM, ok⟩ := rfl
    simp only [List.length_nil, h0, noAdjInst]
    refine ⟨validHistory_pure w s _, ?_⟩
    rcases hok with rfl | rfl <;> rfl
  | cons u rest ih =>
    intro cur curM ok hcur hus hok
    rw [HoldsIn.cons_iff] at hcur
    obtain ⟨hb, hmem_u, hrest⟩ := hcur
    have hu_lt : u < m := hus u List.mem_cons_self
    have hidx_lt : args.x * m + u < adjL.length := by
      rw [hadj_len]
      calc args.x * m + u
          < args.x * m + m := Nat.add_lt_add_left hu_lt _
        _ = (args.x + 1) * m := by rw [Nat.succ_mul]
        _ ≤ m * m := Nat.mul_le_mul_right _ hx
    have hadj_addr_lt : args.adjPtr + args.x * args.numVerts + u < s.frontier := by
      have := hadj.1
      rw [hnv, Nat.add_assoc]
      omega
    have hadj_read : s.mem (args.adjPtr + args.x * args.numVerts + u) =
        adjL.getD (args.x * m + u) 0 := by
      rw [hnv, Nat.add_assoc, hadj.get _ hidx_lt,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx_lt, Option.getD_some]
    let entry := s.mem (args.adjPtr + args.x * args.numVerts + u)
    let ok' := if ok = 1 then (if curM % 2 = 1 then (if entry = 0 then 1 else 0) else 1) else 0
    have hok' : ok' = 0 ∨ ok' = 1 := by
      dsimp only [ok']
      split_ifs <;> simp
    obtain ⟨hv_rest, hr_rest⟩ :=
      ih (cur + 1) (curM / 2) ok' hrest (fun v hv => hus v (List.mem_cons_of_mem u hv)) hok'
    have hcur_lt : cur < s.frontier := by omega
    have hv_step : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (noAdjStep (env, ⟨cur, curM, ok⟩))) := by
      dsimp only [noAdjStep, env]
      refine validHistory_read_bind hcur_lt ?_
      rw [hmem_u]
      exact validHistory_read_bind hadj_addr_lt (validHistory_pure w s _)
    have hst_step : (Memory.spec 0).clientState s (noAdjStep (env, ⟨cur, curM, ok⟩)) = s := rfl
    have hres_step : (Memory.spec 0).clientResult s (noAdjStep (env, ⟨cur, curM, ok⟩)) =
        ⟨cur + 1, curM / 2, ok'⟩ := by
      dsimp only [noAdjStep, env, ok', entry]
      change (⟨cur + 1, curM / 2, _⟩ : NoAdjState) = _
      rw [hmem_u]
    simp only [List.length_cons]
    change (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (noAdjStep (env, ⟨cur, curM, ok⟩) >>= iterate noAdjStep env rest.length)) ∧
      ((Memory.spec 0).clientResult s
        (noAdjStep (env, ⟨cur, curM, ok⟩) >>= iterate noAdjStep env rest.length)).ok = _
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_step, hres_step]), ?_⟩
    rw [StateTransitionSpec.clientResult_bind, hst_step, hres_step, hr_rest]
    simp only [ok', entry, hadj_read, noAdjInst]
    rcases hok with rfl | rfl
    · simp
    · by_cases hbit : curM % 2 = 1 <;> simp [hbit, adj, and_comm]

private theorem holdsIn_drop_step {m len j cur : ℕ} {xs : List ℕ} {t : Memory.State}
    (hlen : xs.length = len) (hj : j + 1 ≤ len) (hxs_lt : ∀ u ∈ xs, u < m)
    (hrem : HoldsIn cur (xs.drop (len - (j + 1))) t) :
    t.mem cur < m ∧ HoldsIn (cur + 1) (xs.drop (len - j)) t := by
  have hj_lt : len - (j + 1) < xs.length := by omega
  have hdrop_eq : xs.drop (len - (j + 1)) = xs[len - (j + 1)] :: xs.drop (len - j) := by
    rw [show len - j = (len - (j + 1)) + 1 by omega]
    exact List.drop_eq_getElem_cons hj_lt
  rw [hdrop_eq, HoldsIn.cons_iff] at hrem
  exact ⟨hrem.2.1 ▸ hxs_lt _ (List.getElem_mem hj_lt), hrem.2.2⟩

private theorem noAdjScanProg_realizes :
    Realizes .exact noAdjScanProg WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 2 ∧
        ∃ m adjL xs,
          adjL.length = m * m ∧ args.numVerts = m ∧ args.x < m ∧
          HoldsIn args.adjPtr adjL s ∧ HoldsIn args.ptr xs s ∧ xs.length = args.len ∧
          (∀ u ∈ xs, u < m) ∧
          Fits w (args.adjPtr + m * m) ∧ Fits w (args.ptr + args.len))
      (fun _ _ => 0) := by
  unfold noAdjScanProg
  realize
  · exact h.1.of_le (by decide)
  · obtain ⟨h2, m, adjL, xs, hadjL_len, hnv, hx_lt, hadj_h, hxs_h, hxs_len, hxs_lt,
      hadj_fit, hptr_fit⟩ := h
    have h1 : Fits w 1 := h2.of_le (by decide)
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : NoAdjState) (t : Memory.State) =>
        j ≤ d.len ∧ st.cur + j = d.ptr + d.len ∧ st.ok ≤ 1 ∧
        HoldsIn d.adjPtr adjL t ∧ HoldsIn st.cur (xs.drop (d.len - j)) t)
      (fun j st t ⟨hj_le, hcur, hok, hadj_t, hrem⟩ => ?_)
      ⟨le_rfl, rfl, le_rfl, hadj_h, by simpa only [Nat.sub_self, List.drop_zero] using hxs_h⟩
    dsimp only [noAdjStep]
    obtain ⟨hu_lt, hrem_next⟩ := holdsIn_drop_step hxs_len hj_le hxs_lt hrem
    have hprod_lt : d.x * m + t.mem st.cur < m * m := by
      calc d.x * m + t.mem st.cur < d.x * m + m := Nat.add_lt_add_left hu_lt _
        _ = (d.x + 1) * m := by rw [Nat.succ_mul]
        _ ≤ m * m := Nat.mul_le_mul_right m hx_lt
    have hcur_fit : Fits w (st.cur + 1) := hptr_fit.of_le (by omega)
    have hmul_fit : Fits w (d.x * d.numVerts) := by
      rw [hnv]; exact hadj_fit.of_le (by omega)
    have hsum1_fit : Fits w (d.adjPtr + d.x * d.numVerts) := by
      rw [hnv]; exact hadj_fit.of_le (by omega)
    have hsum2_fit : Fits w (d.adjPtr + d.x * d.numVerts + t.mem st.cur) := by
      rw [hnv]; exact hadj_fit.of_le (by omega)
    have h2_ne : 2 ≠ 0 := by decide
    refine ⟨?_, Nat.le_of_succ_le hj_le, ?_, ?_, hadj_t, hrem_next⟩
    · repeat (first | split | assumption | refine And.intro ?_ ?_)
    · change (st.cur + 1) + j = d.ptr + d.len
      omega
    · change (if st.ok = 1 then
          if st.curM % 2 = 1 then
            if t.mem (d.adjPtr + d.x * d.numVerts + t.mem st.cur) = 0 then 1 else 0
          else 1
        else 0) ≤ 1
      split_ifs <;> omega

/-! ### Pairwise bag-independence scan (`indepBagProg`) -/

/-- Register arguments `(numVerts, adjPtr, bagPtr, bagLen, mask)` for `indepBagProg`. -/
structure IndepBagArgs where
  /-- Number of graph vertices `m` (row stride of the adjacency matrix). -/
  numVerts : ℕ
  /-- Base memory address of the `m × m` adjacency matrix. -/
  adjPtr : ℕ
  /-- Base memory address of the bag vertex list. -/
  bagPtr : ℕ
  /-- Length of the bag vertex list. -/
  bagLen : ℕ
  /-- Subset bit mask over the bag vertex list. -/
  mask : ℕ

/-- Tuple equivalence encoding `IndepBagArgs` into Word-RAM registers. -/
@[expose] def IndepBagArgs.equiv : IndepBagArgs ≃ (((ℕ × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a := ((((a.numVerts, a.adjPtr), a.bagPtr), a.bagLen), a.mask)
  invFun := fun ((((nv, ap), bp), bl), m) => ⟨nv, ap, bp, bl, m⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding IndepBagArgs := .ofEquiv IndepBagArgs.equiv

private structure IndepBagEnv where
  numVerts : ℕ
  adjPtr : ℕ

private def IndepBagEnv.equiv : IndepBagEnv ≃ ℕ × ℕ where
  toFun e := (e.numVerts, e.adjPtr)
  invFun := fun (nv, ap) => ⟨nv, ap⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding IndepBagEnv := .ofEquiv IndepBagEnv.equiv

private structure IndepBagState where
  cur : ℕ
  remLen : ℕ
  curM : ℕ
  ok : ℕ

private def IndepBagState.equiv : IndepBagState ≃ ((ℕ × ℕ) × ℕ) × ℕ where
  toFun s := (((s.cur, s.remLen), s.curM), s.ok)
  invFun := fun (((cur, rem), curM), ok) => ⟨cur, rem, curM, ok⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding IndepBagState := .ofEquiv IndepBagState.equiv

private def indepBagStep (p : IndepBagEnv × IndepBagState) : Memory.Prog IndepBagState := do
  let env := p.1
  let st := p.2
  let u ← Memory.read st.cur
  let remLen' := st.remLen - 1
  let bit := st.curM % 2
  let nextM := st.curM / 2
  let na ← if bit = 1 then
      noAdjScanProg ⟨env.numVerts, env.adjPtr, u, st.cur + 1, remLen', nextM⟩
    else
      pure 1
  let ok' := if st.ok = 1 then na else 0
  pure ⟨st.cur + 1, remLen', nextM, ok'⟩

/-- Return `1` if the subset of the bag slice selected by `args.mask` is pairwise independent
under the row-major adjacency matrix at `args.adjPtr`, else `0`. -/
def indepBagProg (args : IndepBagArgs) : Memory.Prog ℕ := do
  let res ← iterate indepBagStep ⟨args.numVerts, args.adjPtr⟩ args.bagLen
    ⟨args.bagPtr, args.bagLen, args.mask, 1⟩
  pure res.ok

private theorem indepBagStep_eval (env : IndepBagEnv) (st : IndepBagState) (t : Memory.State) :
    let na := if st.curM % 2 = 1 then
      (Memory.spec 0).clientResult t
        (noAdjScanProg ⟨env.numVerts, env.adjPtr, t.mem st.cur, st.cur + 1, st.remLen - 1,
          st.curM / 2⟩)
    else 1
    (Memory.spec 0).clientState t (indepBagStep (env, st)) = t ∧
    (Memory.spec 0).clientResult t (indepBagStep (env, st)) =
      ⟨st.cur + 1, st.remLen - 1, st.curM / 2, if st.ok = 1 then na else 0⟩ := by
  have hr_st (a : ℕ) : (Memory.spec 0).clientState t (Memory.read a) = t := rfl
  have hr_res (a : ℕ) : (Memory.spec 0).clientResult t (Memory.read a) = t.mem a := rfl
  unfold indepBagStep
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_st, hr_res]
  dsimp only
  split
  · rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
      noAdjScanProg_state]
    exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- `indepBagProg` is read-only and leaves memory unchanged. -/
theorem indepBagProg_state (args : IndepBagArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (indepBagProg args) = s := by
  unfold indepBagProg
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of indepBagStep ⟨args.numVerts, args.adjPtr⟩
    (fun st m => (indepBagStep_eval _ st m).1) args.bagLen
    ⟨args.bagPtr, args.bagLen, args.mask, 1⟩ s

/-- Correctness and `bagLen * (2 * bagLen + 1)` memory-cost bound for `indepBagProg`. -/
theorem indepBagProg_spec {w m : ℕ} (args : IndepBagArgs) {adjL xs : List ℕ}
    {s : Memory.State}
    (hadj : HoldsIn args.adjPtr adjL s) (hadj_len : adjL.length = m * m)
    (hnv : args.numVerts = m)
    (hxs : HoldsIn args.bagPtr xs s) (hlen : xs.length = args.bagLen)
    (hxs_lt : ∀ u ∈ xs, u < m) :
    let adj := fun u v => decide (adjL.getD (u * m + v) 0 ≠ 0)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (indepBagProg args)) ∧
    (Memory.spec 0).clientState s (indepBagProg args) = s ∧
    (Memory.spec 0).clientResult s (indepBagProg args) =
      (if indepInst adj xs args.mask then 1 else 0) ∧
    memoryCost (indepBagProg args) s ≤ args.bagLen * (2 * args.bagLen + 1) := by
  let adj := fun u v => decide (adjL.getD (u * m + v) 0 ≠ 0)
  let env : IndepBagEnv := ⟨args.numVerts, args.adjPtr⟩
  suffices ∀ ys cur curM ok, HoldsIn cur ys s → (∀ u ∈ ys, u < m) →
      (ok = 0 ∨ ok = 1) →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (iterate indepBagStep env ys.length ⟨cur, ys.length, curM, ok⟩)) ∧
      ((Memory.spec 0).clientResult s
        (iterate indepBagStep env ys.length ⟨cur, ys.length, curM, ok⟩)).ok =
        (if ok = 1 ∧ indepInst adj ys curM = true then 1 else 0) ∧
      memoryCost (iterate indepBagStep env ys.length ⟨cur, ys.length, curM, ok⟩) s ≤
        ys.length * (2 * ys.length + 1) by
    have hrun := this xs args.bagPtr args.mask 1 hxs hxs_lt (.inr rfl)
    rw [hlen] at hrun
    refine ⟨?_, indepBagProg_state args s, ?_, ?_⟩
    · unfold indepBagProg
      exact validHistory_bind_step hrun.1 (validHistory_pure w _ _)
    · unfold indepBagProg
      rw [StateTransitionSpec.clientResult_bind]
      change ((Memory.spec 0).clientResult s
        (iterate indepBagStep env args.bagLen ⟨args.bagPtr, args.bagLen, args.mask, 1⟩)).ok = _
      rw [hrun.2.1]
      cases indepInst adj xs args.mask <;> rfl
    · unfold indepBagProg
      rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
      exact hrun.2.2
  intro ys
  induction ys with
  | nil =>
    intro cur curM ok _ _ hok
    have h0 : iterate indepBagStep env 0 ⟨cur, 0, curM, ok⟩ = pure ⟨cur, 0, curM, ok⟩ := rfl
    simp only [List.length_nil, h0, indepInst]
    refine ⟨validHistory_pure w s _, ?_, by simp [memoryCost_pure]⟩
    rcases hok with rfl | rfl <;> rfl
  | cons u rest ih =>
    intro cur curM ok hcur hus hok
    rw [HoldsIn.cons_iff] at hcur
    obtain ⟨hb, hmem_u, hrest⟩ := hcur
    have hu_lt : u < m := hus u List.mem_cons_self
    have hrest_lt : ∀ v ∈ rest, v < m :=
      fun v hv => hus v (List.mem_cons_of_mem u hv)
    have hcur_lt : cur < s.frontier := by omega
    let naPure : ℕ :=
      if curM % 2 = 1 then
        if noAdjInst adj u rest (curM / 2) then 1 else 0
      else 1
    let ok' : ℕ := if ok = 1 then naPure else 0
    have hok' : ok' = 0 ∨ ok' = 1 := by
      dsimp only [ok', naPure]
      split_ifs <;> simp
    obtain ⟨hv_rest, hr_rest, hc_rest⟩ := ih (cur + 1) (curM / 2) ok' hrest hrest_lt hok'
    have hr_st (a : ℕ) : (Memory.spec 0).clientState s (Memory.read a) = s := rfl
    have hr_res (a : ℕ) : (Memory.spec 0).clientResult s (Memory.read a) = s.mem a := rfl
    obtain ⟨hv_na, hst_na, hr_na, hc_na⟩ :=
      noAdjScanProg_spec (w := w)
        ⟨args.numVerts, args.adjPtr, u, cur + 1, rest.length, curM / 2⟩
        hadj hadj_len hnv hu_lt hrest rfl hrest_lt
    dsimp only at hr_na hc_na
    have hst_step := (indepBagStep_eval env ⟨cur, (u :: rest).length, curM, ok⟩ s).1
    have hres_step : (Memory.spec 0).clientResult s
        (indepBagStep (env, ⟨cur, (u :: rest).length, curM, ok⟩)) =
        ⟨cur + 1, rest.length, curM / 2, ok'⟩ := by
      refine ((indepBagStep_eval env ⟨cur, (u :: rest).length, curM, ok⟩ s).2).trans ?_
      simp only [env, hmem_u, List.length_cons, Nat.add_sub_cancel, hr_na]
      rfl
    have hv_step : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (indepBagStep (env, ⟨cur, (u :: rest).length, curM, ok⟩))) := by
      unfold indepBagStep
      simp only [env, List.length_cons, Nat.add_sub_cancel]
      refine validHistory_read_bind hcur_lt ?_
      rw [hmem_u]
      split
      · exact validHistory_bind_step hv_na (validHistory_pure w _ _)
      · rw [pure_bind]
        exact validHistory_pure w s _
    have hc_step : memoryCost (indepBagStep (env, ⟨cur, (u :: rest).length, curM, ok⟩)) s ≤
        2 * rest.length + 1 := by
      unfold indepBagStep
      rw [memoryCost_bind', memoryCost_read, hr_st, hr_res, hmem_u]
      simp only [env, List.length_cons, Nat.add_sub_cancel]
      split
      · rw [memoryCost_bind', hst_na, memoryCost_pure, Nat.add_zero]
        omega
      · rw [pure_bind, memoryCost_pure]
        omega
    have hiter_eq :
        iterate indepBagStep env (u :: rest).length ⟨cur, (u :: rest).length, curM, ok⟩ =
        (indepBagStep (env, ⟨cur, (u :: rest).length, curM, ok⟩) >>=
          iterate indepBagStep env rest.length) := rfl
    rw [hiter_eq]
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_step, hres_step]), ?_, ?_⟩
    · rw [StateTransitionSpec.clientResult_bind, hst_step, hres_step, hr_rest]
      dsimp only [ok', naPure, indepInst]
      rcases hok with rfl | rfl
      · simp
      · by_cases hbit : curM % 2 = 1 <;>
          by_cases hna : noAdjInst adj u rest (curM / 2) = true <;>
          by_cases hind : indepInst adj rest (curM / 2) = true <;>
          simp [hbit, hna, hind]
    · rw [memoryCost_bind', hst_step, hres_step]
      simp only [List.length_cons]
      calc memoryCost (indepBagStep (env, ⟨cur, (u :: rest).length, curM, ok⟩)) s +
            memoryCost
              (iterate indepBagStep env rest.length ⟨cur + 1, rest.length, curM / 2, ok'⟩) s
          ≤ (2 * rest.length + 1) + rest.length * (2 * rest.length + 1) :=
            Nat.add_le_add hc_step hc_rest
        _ ≤ (rest.length + 1) * (2 * (rest.length + 1) + 1) := by nlinarith

/-- Exact-basis Word-RAM realization certificate for `indepBagProg`. -/
theorem indepBagProg_realizes :
    Realizes .exact indepBagProg WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 2 ∧
        ∃ m adjL xs,
          adjL.length = m * m ∧ args.numVerts = m ∧
          HoldsIn args.adjPtr adjL s ∧ HoldsIn args.bagPtr xs s ∧ xs.length = args.bagLen ∧
          (∀ u ∈ xs, u < m) ∧
          Fits w (args.adjPtr + m * m) ∧ Fits w (args.bagPtr + args.bagLen))
      (fun _ _ => 0) := by
  unfold indepBagProg
  realize [noAdjScanProg_realizes]
  · exact h.1.of_le (by decide)
  · obtain ⟨h2, m, adjL, xs, hadjL_len, hnv, hadj_h, hxs_h, hxs_len, hxs_lt,
      hadj_fit, hptr_fit⟩ := h
    have h1 : Fits w 1 := h2.of_le (by decide)
    have h2_ne : 2 ≠ 0 := by decide
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : IndepBagState) (t : Memory.State) =>
        j ≤ d.bagLen ∧ st.remLen = j ∧ st.cur + j = d.bagPtr + d.bagLen ∧ st.ok ≤ 1 ∧
        HoldsIn d.adjPtr adjL t ∧ HoldsIn st.cur (xs.drop (d.bagLen - j)) t)
      (fun j st t ⟨hj_le, hrem_eq, hcur, hok, hadj_t, hrem⟩ => ?_)
      ⟨le_rfl, rfl, rfl, le_rfl, hadj_h,
        by simpa only [Nat.sub_self, List.drop_zero] using hxs_h⟩
    obtain ⟨hu_lt, hrem_next⟩ := holdsIn_drop_step hxs_len hj_le hxs_lt hrem
    have hcur_fit : Fits w (st.cur + 1) := hptr_fit.of_le (by omega)
    have hrem_ge1 : 1 ≤ st.remLen := by omega
    have htail_len : (xs.drop (d.bagLen - j)).length = st.remLen - 1 := by
      rw [List.length_drop]; omega
    have htail_lt : ∀ v ∈ xs.drop (d.bagLen - j), v < m :=
      fun v hv => hxs_lt v (List.mem_of_mem_drop hv)
    have hnoAdj_safe : Fits w 2 ∧ ∃ m' adjL' xs',
        adjL'.length = m' * m' ∧ d.numVerts = m' ∧ t.mem st.cur < m' ∧
        HoldsIn d.adjPtr adjL' t ∧ HoldsIn (st.cur + 1) xs' t ∧ xs'.length = st.remLen - 1 ∧
        (∀ u ∈ xs', u < m') ∧ Fits w (d.adjPtr + m' * m') ∧
        Fits w ((st.cur + 1) + (st.remLen - 1)) :=
      ⟨h2, m, adjL, xs.drop (d.bagLen - j), hadjL_len, hnv, hu_lt, hadj_t, hrem_next,
        htail_len, htail_lt, hadj_fit, hptr_fit.of_le (by omega)⟩
    obtain ⟨hst_ev, hres_ev⟩ := indepBagStep_eval ⟨d.numVerts, d.adjPtr⟩ st t
    have hr_na := (noAdjScanProg_spec (w := 0)
      ⟨d.numVerts, d.adjPtr, t.mem st.cur, st.cur + 1, st.remLen - 1, st.curM / 2⟩
      hadj_t hadjL_len hnv hu_lt hrem_next htail_len htail_lt).2.2.1
    dsimp only at hr_na
    refine ⟨?_, Nat.le_of_succ_le hj_le, ?_, ?_, ?_, ?_, ?_⟩
    · repeat (first | split | exact hnoAdj_safe | assumption | refine And.intro ?_ ?_)
    · rw [hres_ev]
      change st.remLen - 1 = j
      omega
    · rw [hres_ev]
      change (st.cur + 1) + j = d.bagPtr + d.bagLen
      omega
    · rw [hres_ev]
      dsimp only
      rw [hr_na]
      change (if st.ok = 1 then (if st.curM % 2 = 1 then (if _ then 1 else 0) else 1) else 0) ≤ 1
      split_ifs <;> omega
    · rwa [hst_ev]
    · rwa [hst_ev, hres_ev]

end Cslib.Algorithms.WordRAM.TreeDecomposition
