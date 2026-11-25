/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime.Step
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.FixedPrime.Potential
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Callable.Bounds

/-!
# Complete traversal of the actual prepared catalogue

Every guarded iteration constructs the next logical chunk/piece in one fixed slot and calls
the complete backend at physical ordinal zero. The invariant counts only the visited prefix:
distinct failures share one global budget and the successful-return flags sum to at most one.
A charged heap reset reclaims the slot after verification. Queries, catalogue and original
weights stay below the slot; no current state is asserted to contain all logical records.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open FixedPrime
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

attribute [local instance] Classical.propDecidable

private structure Invariant {m n g p : ℕ} (V : ℕ → ℤ) (a : Data 64)
    (start : Data 416) (order : ℕ → InstanceIndex p) (hn : 0 < n) (x : Data 416) : Prop where
  cursor : Cursor n (D m) g p V (x.comap producerBank)
  progress : x.regs (producerBank Instances.produced) = x.regs Reg.index
  heap : x.regs (producerBank Instances.heap) = x.regs (producerBank Instances.output)
  protected_mem : Set.EqOn x.mem a.mem (Set.Iio (a.regs Instances.output))
  frame : ∀ u, u < a.regs Instances.output ∨
    a.regs Instances.output + (6 + 2 * (n * D m)) +
      CallableProduct.windowSize n (n * n) ≤ u → x.mem u = start.mem u
  index_le : x.regs Reg.index ≤ a.regs Instances.produced
  one : x.regs Reg.one = 1
  flag : x.regs Reg.found = 0 ∨ x.regs Reg.found = 1
  limit : x.regs Reg.limit =
    (if x.regs Reg.found = 1 then x.regs Reg.index else a.regs Instances.produced)
  scans_failed : x.regs Reg.scans ≤
    (∑ j ∈ Finset.range (x.regs Reg.index),
      recordFailures (m := m) (g := g) hn V a.mem (order j)) + x.regs Reg.found
  scans_coarse : x.regs Reg.scans ≤ x.regs Reg.index * (n * n + 1)
  searched : Nat.count (fun j => recordHit (m := m) (n := n) (g := g) V (order j))
    (x.regs Reg.index) = x.regs Reg.found
  witness : x.regs Reg.found = 1 →
    x.regs (recordBank RecordWitness.Reg.witnessA) < n ∧
    x.regs (recordBank RecordWitness.Reg.witnessB) < n ∧
    x.regs (recordBank RecordWitness.Reg.witnessC) < n ∧
    V (x.regs (recordBank RecordWitness.Reg.witnessA) * n +
        x.regs (recordBank RecordWitness.Reg.witnessB)) +
      V (n * n + (x.regs (recordBank RecordWitness.Reg.witnessB) * n +
        x.regs (recordBank RecordWitness.Reg.witnessC))) +
      V (2 * (n * n) + (x.regs (recordBank RecordWitness.Reg.witnessA) * n +
        x.regs (recordBank RecordWitness.Reg.witnessC))) = 0

private theorem exec_body {w m n g p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hW : admissionWidth n (D m) g p A ≤ w + 2)
    (a : Data 64) (x : Data 416)
    (hout : Instances.Output n (D m) g p (fun q => values.getD q 0)
      (.init (PreparationInput.input n (D m) g p values)) a)
    (hheap : a.regs Instances.heap ≤ PreparationInput.wordBound n (D m) g p A)
    (hn : 0 < n) (order : ℕ → InstanceIndex p)
    (order_mem : ∀ i < a.regs Instances.produced, order i ∈ instanceIndices
      (fun u v : Fin n => values.getD (pairIndex (u, v)) 0) (D m) g p)
    (order_ord : ∀ i < a.regs Instances.produced,
      RecordProduct.recordOrdinal n (D m) g p (fun q => values.getD q 0) (order i) = i) :
    let V := fun q => values.getD q 0
    let charge := fun idx : InstanceIndex p => recordBase (m := m) hn V a.mem idx +
      (40 * (n * D m) + 67)
    let B := fun i => charge (order i)
    let F := fun i => recordFailures (m := m) (g := g) hn V a.mem (order i)
    let C := 42 * pieceSize (D m) g + 28
    let Inv := Invariant (m := m) (g := g) V a x order hn
    let Φ := fun z : Data 416 => remainingCharge B F C (a.regs Instances.produced)
      (z.regs Reg.index) (z.regs Reg.found)
    ∀ z, Inv z → (Cond.lt Reg.index Reg.limit).Holds z →
      ∃ y T, ExecWithin (w + 2) step z y T ∧ Inv y ∧ T + 2 + Φ y ≤ Φ z := by
  intro V charge B F C Inv Φ z hz hc
  let M := a.regs Instances.produced
  have hguard : z.regs Reg.index < z.regs Reg.limit := hc
  have before : z.regs Reg.found = 0 := hz.flag.resolve_right fun h => by
    have hlim := hz.limit
    rw [h, ite_eq_left rfl] at hlim
    omega
  have lim : z.regs Reg.limit = M := by
    simpa only [before, zero_ne_one, ite_false] using hz.limit
  have hi : z.regs Reg.index < M := by omega
  obtain ⟨y, S, T, he, hT, yi, yl, yo, ys, yf, hS, hcoarse, yhit, yw, ym,
      ycursor, yproduced, yheap⟩ :=
    exec_step values hlen hD hg hp hN hv hW a z hout hz.cursor hz.progress hz.heap
      hz.protected_mem hheap rfl hi lim
      hz.one hz.scans_coarse (order (z.regs Reg.index)) (order_mem _ hi) (order_ord _ hi)
  have newflag : y.regs Reg.found ≤ 1 := by rcases yf with h | h <;> omega
  have yInv : Inv y := by
    refine ⟨ycursor, yproduced.trans yi.symm, yheap,
      fun u hu => (ym u (Or.inl hu)).trans (hz.protected_mem hu), ?_,
      yi ▸ Nat.succ_le_of_lt hi, yo, yf, by simpa only [yi] using yl, ?_,
      by rw [ys, yi, Nat.add_mul, Nat.one_mul]; exact Nat.add_le_add hz.scans_coarse hcoarse,
      ?_, yw⟩
    · intro u hu
      refine (ym u (hu.imp id fun h => le_trans (Nat.add_le_add_left
        (CallableProduct.windowSize_mono_right n (recordQueryCount_le n (D m) p V _)) _) h)).trans
        (hz.frame u hu)
    · have hs := hz.scans_failed
      rw [before, Nat.add_zero] at hs
      rw [ys, yi, Finset.sum_range_succ]
      dsimp only [V] at *
      omega
    · rw [yi, Nat.count_succ, hz.searched, before, Nat.zero_add]
      rcases yf with h | h
      · rw [ite_eq_right (mt yhit.mpr (by omega)), h]
      · rw [ite_eq_left (yhit.mp h), h]
  refine ⟨y, T, he, yInv, ?_⟩
  change T + 2 ≤ B (z.regs Reg.index) + C * S at hT
  simpa only [Φ, yi, before] using
    remainingCharge_step (base := B) (failures := F) (C := C) hi hT hS newflag

/-- Construct and immediately consume each logical record, stopping at the first original
witness. The reference readback indexes immutable catalogue data and mathematical charges;
the actual cursor starts with no records and resets its physical heap after each visit. -/
theorem exec_traverse {w m n g p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hW : admissionWidth n (D m) g p A ≤ w + 2)
    (a : Data 64) (x : Data 416)
    (hout : Instances.Output n (D m) g p (fun q => values.getD q 0)
      (.init (PreparationInput.input n (D m) g p values)) a)
    (cursor : Cursor n (D m) g p (fun q => values.getD q 0) (x.comap producerBank))
    (hproduced : x.regs (producerBank Instances.produced) = 0)
    (hslotHeap : x.regs (producerBank Instances.heap) = x.regs (producerBank Instances.output))
    (hmem : Set.EqOn x.mem a.mem (Set.Iio (a.regs Instances.output)))
    (hheap : a.regs Instances.heap ≤ PreparationInput.wordBound n (D m) g p A) :
    let V := fun q => values.getD q 0
    let wAB := fun u v : Fin n => V (pairIndex (u, v))
    let wBC := fun b c : Fin n => V (n * n + pairIndex (b, c))
    let wAC := fun u c : Fin n => V (2 * (n * n) + pairIndex (u, c))
    let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
    ∃ y, ExecWithin (w + 2) traverse x y
        ((∑ idx ∈ instanceIndices wAB (D m) g p,
          (recordBase (m := m) hn V a.mem idx + (40 * (n * D m) + 67))) +
          (42 * pieceSize (D m) g + 28) * (falsePositiveCount wAB wBC wAC p + 1) + 7) ∧
      (y.regs Reg.found = 0 ∨ y.regs Reg.found = 1) ∧
      y.regs Reg.scans ≤ falsePositiveCount wAB wBC wAC p + y.regs Reg.found ∧
      (y.regs Reg.found = 1 ↔ HasZeroTriangle wAB wBC wAC) ∧
      (y.regs Reg.found = 1 →
        y.regs (recordBank RecordWitness.Reg.witnessA) < n ∧
        y.regs (recordBank RecordWitness.Reg.witnessB) < n ∧
        y.regs (recordBank RecordWitness.Reg.witnessC) < n ∧
        V (y.regs (recordBank RecordWitness.Reg.witnessA) * n +
            y.regs (recordBank RecordWitness.Reg.witnessB)) +
          V (n * n + (y.regs (recordBank RecordWitness.Reg.witnessB) * n +
            y.regs (recordBank RecordWitness.Reg.witnessC))) +
          V (2 * (n * n) + (y.regs (recordBank RecordWitness.Reg.witnessA) * n +
            y.regs (recordBank RecordWitness.Reg.witnessC))) = 0) ∧
      (∀ u, u < a.regs Instances.output ∨
        a.regs Instances.output + (6 + 2 * (n * D m)) +
          CallableProduct.windowSize n (n * n) ≤ u → y.mem u = x.mem u) ∧
      Cursor n (D m) g p V (y.comap producerBank) ∧
      y.regs (producerBank Instances.produced) = y.regs Reg.index ∧
      y.regs (producerBank Instances.heap) = y.regs (producerBank Instances.output) := by
  classical
  intro V wAB wBC wAC hn
  have hDn : D m ≤ n := (Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN
  have hp0 := (Nat.mem_sqrtPrimeWindow_iff_sq.mp hp).1.ne_zero
  let M := a.regs Instances.produced
  let I := instanceIndices wAB (D m) g p
  obtain ⟨f, finj, hf, fsurj⟩ := exists_occupied_order V hout hD hDn hg hp0
  let order : ℕ → InstanceIndex p := fun i =>
    if hi : i < M then f ⟨i, hi⟩ else ⟨⟨0, Nat.pos_of_ne_zero hp0⟩, 0, 0⟩
  have order_at (i : ℕ) (hi : i < M) : order i = f ⟨i, hi⟩ := dite_eq_left hi
  have order_mem (i : ℕ) (hi : i < M) : order i ∈ I := order_at i hi ▸ (hf _).1
  have order_ord (i : ℕ) (hi : i < M) :
      RecordProduct.recordOrdinal n (D m) g p V (order i) = i := order_at i hi ▸ (hf _).2
  have sum_eq (charge : InstanceIndex p → ℕ) :
      (∑ j ∈ Finset.range M, charge (order j)) = ∑ idx ∈ I, charge idx :=
    Finset.sum_bij (fun i hi => f ⟨i, Finset.mem_range.mp hi⟩) (fun _ _ => (hf _).1)
      (fun _ _ _ _ heq => congrArg Fin.val (finj heq))
      (fun idx hidx => let ⟨i, hi⟩ := fsurj idx hidx; ⟨i.val, Finset.mem_range.mpr i.isLt, hi⟩)
      (fun i hi => by rw [order_at i (Finset.mem_range.mp hi)])
  let charge := fun (idx : InstanceIndex p) =>
    recordBase (m := m) hn V a.mem idx + (40 * (n * D m) + 67)
  let B := fun i => charge (order i)
  let F := fun i => recordFailures (m := m) (g := g) hn V a.mem (order i)
  let C := 42 * pieceSize (D m) g + 28
  have hF : (∑ j ∈ Finset.range M, F j) ≤ falsePositiveCount wAB wBC wAC p :=
    (sum_eq (recordFailures (m := m) (g := g) hn V a.mem)).trans_le
      (sum_recordFailures_le hn V hout hD hDn hg hp I (fun _ hi => hi))
  let Inv := Invariant (m := m) (g := g) V a x order hn
  let Φ := fun z : Data 416 => remainingCharge B F C M (z.regs Reg.index) (z.regs Reg.found)
  have body : ∀ z, Inv z → (Cond.lt Reg.index Reg.limit).Holds z →
      ∃ y T, ExecWithin (w + 2) step z y T ∧ Inv y ∧ T + 2 + Φ y ≤ Φ z :=
    exec_body values hlen hD hg hp hN hv hW a x hout hheap hn order order_mem order_ord
  have h1 : Fits (w + 2) 1 := (counter_fits hW).of_le (by unfold counterEnvelope; omega)
  obtain ⟨s, hs, sm, si, sl, sf, ss, so, sbank⟩ := exec_setup x h1
  have sInv : Inv s := by
    refine ⟨cursor.transfer (fun j _ _ _ _ => sbank _ (by change j.val < 400; omega)),
      ((sbank _ (by decide)).trans hproduced).trans si.symm,
      ((sbank _ (by decide)).trans hslotHeap).trans (sbank _ (by decide)).symm,
      fun u hu => (congrFun sm u).trans (hmem hu), fun u _ => congrFun sm u,
      si ▸ Nat.zero_le _, so, Or.inl sf, ?_,
      by simp only [si, ss, sf, Finset.range_zero, Finset.sum_empty, Nat.zero_add, le_refl],
      by simp only [ss, si, Nat.zero_mul, le_refl],
      by simp only [si, sf, Nat.count_zero], fun h => by omega⟩
    rw [sf, ite_eq_right (by decide : ¬(0 : ℕ) = 1), sl]
    have hc := cursor.total
    rw [cursor.chunks, cursor.pieces] at hc
    exact hc.trans hout.2.2.2.2.1.symm
  obtain ⟨y, hy, hIy, hcy⟩ := ExecWithin.loop_potential Inv Φ body sInv
  have hbudget : 5 + (Φ s + 2) ≤
      (∑ idx ∈ I, charge idx) + C * (falsePositiveCount wAB wBC wAC p + 1) + 7 := by
    dsimp only [Φ, remainingCharge]
    simp only [si, sf, Finset.range_zero, Finset.sum_empty, Nat.sub_zero]
    have := Nat.mul_le_mul_left C (Nat.add_le_add_right hF 1)
    rw [sum_eq charge]
    omega
  refine ⟨y, (hs.seq hy).mono hbudget, hIy.flag,
    hIy.scans_failed.trans (Nat.add_le_add_right ((sum_prefix_le F hIy.index_le).trans hF) _),
    ⟨fun hf => let ⟨ha, hb, hc, hw⟩ := hIy.witness hf; ⟨⟨_, ha⟩, ⟨_, hb⟩, ⟨_, hc⟩, hw⟩, ?_⟩,
    hIy.witness, hIy.frame, hIy.cursor, hIy.progress, hIy.heap⟩
  intro ⟨u, v, c, hw⟩
  by_contra hnot
  have hf : y.regs Reg.found = 0 := by rcases hIy.flag with h | h <;> omega
  have hlim : y.regs Reg.limit = M := by simpa only [hf, zero_ne_one, ite_false] using hIy.limit
  have hi : y.regs Reg.index = M := by
    change ¬ y.regs Reg.index < y.regs Reg.limit at hcy
    have := hIy.index_le; omega
  obtain ⟨idx, hacc, hc⟩ := exists_mem_acceptedPairs hD hDn hg hp0
    (RecordProduct.product_answers_correct V wAB wBC wAC hD hg hp (fun _ _ => rfl) (fun _ _ => rfl))
    hw
  obtain ⟨j, hj⟩ := fsurj idx (mem_acceptedPairs.mp hacc).1
  have hh : recordHit (m := m) (n := n) (g := g) V (order j.val) := by
    rw [order_at j.val j.isLt, hj]
    exact ⟨(u, v), (mem_acceptedPairs.mp hacc).2.1, c, hc, hw⟩
  have hpositive := Nat.count_strict_mono
    (p := fun j => recordHit (m := m) (n := n) (g := g) V (order j)) hh j.isLt
  have searched := hIy.searched
  rw [hf, hi] at searched
  exact Nat.not_lt_zero _ (searched ▸ hpositive)

end Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime
