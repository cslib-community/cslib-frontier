/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.InstDP
public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.Scan
import CslibFrontier.Computability.WordRAM.Realization.FramedLoop
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
    Memory.FramedTriple w s (noAdjScanProg args) (2 * args.len) ∅ fun r t =>
      r = (if noAdjInst adj args.x xs args.mask then 1 else 0) ∧ t = s := by
  intro adj
  have hxf := hxs.1
  obtain ⟨-, hloop⟩ := Memory.FramedTriple.iterate (w := w) (s := s) (body := noAdjStep)
    (c := 2) (S := ∅) (safe := fun _ _ _ => True) (d := ⟨args.numVerts, args.adjPtr, args.x⟩)
    (n := args.len) (a₀ := ⟨args.ptr, args.mask, 1⟩)
    (Q := fun st t => st.ok = (if noAdjInst adj args.x xs args.mask then 1 else 0) ∧ t = s)
    (fun k st t => t = s ∧ st.cur = args.ptr + k ∧ (st.ok = 0 ∨ st.ok = 1) ∧
      (st.ok = 1 ∧ noAdjInst adj args.x (xs.drop k) st.curM = true ↔
        noAdjInst adj args.x xs args.mask = true)) ⟨rfl, rfl, .inr rfl, by simp⟩
    (fun k hk st t ⟨ht, hcur, hok, hiff⟩ _ => ⟨trivial, by
      subst t
      have hu_lt : s.mem st.cur < m := by
        rw [hcur, hxs.get k (by omega)]; exact hxs_lt _ (List.getElem_mem _)
      have hidx_lt : args.x * m + s.mem st.cur < adjL.length := by
        rw [hadj_len]
        calc args.x * m + s.mem st.cur
            < args.x * m + m := Nat.add_lt_add_left hu_lt _
          _ = (args.x + 1) * m := by rw [Nat.succ_mul]
          _ ≤ m * m := Nat.mul_le_mul_right _ hx
      have haddr : args.adjPtr + args.x * args.numVerts + s.mem st.cur < s.frontier := by
        have := hadj.1; rw [hnv, Nat.add_assoc]; omega
      have hentry : s.mem (args.adjPtr + args.x * args.numVerts + s.mem st.cur) =
          adjL.getD (args.x * m + s.mem st.cur) 0 := by
        rw [hnv, Nat.add_assoc, hadj.get _ hidx_lt, List.getElem_eq_getD 0]
      unfold noAdjStep
      framed_triple
      refine ⟨rfl, by dsimp only; omega, by dsimp only; split_ifs <;> omega, ?_⟩
      rw [← hiff, hentry, hcur, hxs.get k (by omega), List.drop_eq_getElem_cons (i := k) (by omega)]
      dsimp only [noAdjInst]
      rcases hok with h | h
      · simp [h]
      · by_cases hbit : st.curM % 2 = 1 <;> simp [h, hbit, adj, and_comm]⟩)
    fun st t ⟨ht, _, hok, hiff⟩ _ => ⟨by
      rw [← hlen, List.drop_length] at hiff
      rcases hok with h | h <;> simp [h, noAdjInst] at hiff ⊢ <;> simp [hiff], ht⟩
  unfold noAdjScanProg
  exact Memory.FramedTriple.mono (Memory.FramedTriple.call (c₂ := 0) hloop subset_rfl
    fun st t h _ => Memory.FramedTriple.pure h) (by omega) fun _ _ => id

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
    have hmul_fit : Fits w (d.x * d.numVerts) := hnv ▸ hadj_fit.of_le (by omega)
    have hsum1_fit : Fits w (d.adjPtr + d.x * d.numVerts) := hnv ▸ hadj_fit.of_le (by omega)
    have hsum2_fit : Fits w (d.adjPtr + d.x * d.numVerts + t.mem st.cur) :=
      hnv ▸ hadj_fit.of_le (by omega)
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
  intro adj
  have hxf := hxs.1
  obtain ⟨-, hloop⟩ := Memory.FramedTriple.iterate (w := w) (s := s) (body := indepBagStep)
    (c := 2 * args.bagLen + 1) (S := ∅) (safe := fun _ _ _ => True)
    (d := ⟨args.numVerts, args.adjPtr⟩) (n := args.bagLen)
    (a₀ := ⟨args.bagPtr, args.bagLen, args.mask, 1⟩)
    (Q := fun st _ => st.ok = if indepInst adj xs args.mask then 1 else 0)
    (fun k st t => t = s ∧ st.cur = args.bagPtr + k ∧ st.remLen = args.bagLen - k ∧
      (st.ok = 0 ∨ st.ok = 1) ∧
      (st.ok = 1 ∧ indepInst adj (xs.drop k) st.curM = true ↔ indepInst adj xs args.mask = true))
    ⟨rfl, rfl, rfl, .inr rfl, by simp⟩
    (fun k hk st t ⟨ht, hcur, hrem, hok, hiff⟩ _ => ⟨trivial, by
      subst t
      have hu_lt : s.mem st.cur < m := by
        rw [hcur, hxs.get k (by omega)]; exact hxs_lt _ (List.getElem_mem _)
      have hrest : HoldsIn (st.cur + 1) (xs.drop (k + 1)) s := by
        rw [hcur, Nat.add_assoc]; exact hxs.drop (k + 1) (by omega)
      have hna := noAdjScanProg_spec (w := w)
        ⟨args.numVerts, args.adjPtr, s.mem st.cur, st.cur + 1, st.remLen - 1, st.curM / 2⟩
        hadj hadj_len hnv hu_lt hrest (by simp only [List.length_drop]; omega)
        fun v hv => hxs_lt v (List.mem_of_mem_drop hv)
      dsimp only at hna
      unfold indepBagStep
      framed_walk
      all_goals
        refine ⟨rfl, by dsimp only; omega, by dsimp only; omega,
          by dsimp only; split_ifs <;> omega, ?_⟩
        rw [← hiff, List.drop_eq_getElem_cons (i := k) (by omega)]
        simp only [hcur, hxs.get k (by omega)]
        dsimp only [indepInst]
        rename_i hbit
        rcases hok with h | h
        · simp [h]
        · simp [h, hbit, and_comm, adj]⟩)
    fun st t ⟨_, _, _, hok, hiff⟩ _ => by
      rw [← hlen, List.drop_length] at hiff
      rcases hok with h | h <;> simp [h, indepInst] at hiff ⊢ <;> simp [hiff]
  have hft : Memory.FramedTriple w s (indepBagProg args) (args.bagLen * (2 * args.bagLen + 1)) ∅
      fun r _ => r = if indepInst adj xs args.mask then 1 else 0 :=
    Memory.FramedTriple.mono (Memory.FramedTriple.call (c₂ := 0) hloop subset_rfl
      fun st _ h _ => Memory.FramedTriple.pure h) (by rw [Nat.mul_comm]; omega) fun _ _ => id
  obtain ⟨hv, hc, -, hres⟩ := framedTriple_iff_realization.mp hft
  exact ⟨hv, indepBagProg_state args s, hres, hc⟩

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
    obtain ⟨hst_ev, hres_ev⟩ := indepBagStep_eval ⟨d.numVerts, d.adjPtr⟩ st t
    have hr_na := (framedTriple_iff_realization.mp (noAdjScanProg_spec (w := 0)
      ⟨d.numVerts, d.adjPtr, t.mem st.cur, st.cur + 1, st.remLen - 1, st.curM / 2⟩
      hadj_t hadjL_len hnv hu_lt hrem_next htail_len htail_lt)).2.2.2.1
    dsimp only at hr_na
    refine ⟨?_, Nat.le_of_succ_le hj_le,
      (congrArg IndepBagState.remLen hres_ev).trans (by rw [hrem_eq, Nat.add_sub_cancel]),
      by simp only [hres_ev]; omega, ?_, hst_ev.symm ▸ hadj_t,
      hst_ev.symm ▸ (congrArg IndepBagState.cur hres_ev).symm ▸ hrem_next⟩
    · dsimp only
      repeat (first
        | split
        | exact ⟨h2, m, adjL, xs.drop (d.bagLen - j), hadjL_len, hnv, hu_lt, hadj_t, hrem_next,
            htail_len, htail_lt, hadj_fit, hptr_fit.of_le (by omega)⟩
        | assumption
        | refine And.intro ?_ ?_)
    · simp only [hres_ev, hr_na]
      split_ifs <;> omega

end Cslib.Algorithms.WordRAM.TreeDecomposition
