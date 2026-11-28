/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.Program
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Basic

/-!
# Fibonacci Heap: Shared Primitives, Initialization, Queries, and Insertion

This file proves the exact-Word-RAM specifications for:
* shared primitives (`prioLTFlag`, `insertIntoNonEmptyList`, `addRootAndUpdateMin`) reused across
  `insert`, `decreaseKey`, and `extractMin`;
* `allocSpan`, `initSetup`, and `incCur` (`O(1)` fresh initialization on zeroed memory);
* `isEmptyCode`, `getKeyCode`, and `insertCode`.

## Main definitions

* Shared code fragments are defined in
  `CslibFrontier/DataStructure/PriorityQueue/WordRAM/FibonacciHeap/Program.lean` and verified here
  against `FibInv`.

## Main results

* `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.prioLTFlag_exec`,
  `insertIntoNonEmptyList_exec`, `addRootAndUpdateMin_exec`: shared list and priority primitives.
* `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.allocSpan_exec`, `initSetup_exec`,
  `incCur_eval`: initialization specifications for `StateTransitionImpl`.
* `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.isEmptyCode_exec`, `getKeyCode_exec`,
  `insertCode_exec`: `O(1)` query and amortized insertion specifications.

## References

* [M. L. Fredman and R. E. Tarjan, *Fibonacci Heaps and Their Uses in Improved Network Optimization
  Algorithms*][FredmanTarjan1987]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 19][CLRS2009]
-/

public section

namespace Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open Cslib.DataStructure.PriorityQueue.FibonacciHeap (AddsRoot newNode)

theorem owns_arr_addr {n base k idx : ℕ} (hk : k < 8) (hidx : idx < n) :
    base ≤ base + k * n + idx ∧ base + k * n + idx < base + space n := by
  have hkn : (k + 1) * n ≤ 8 * n := Nat.mul_le_mul_right n hk
  rw [Nat.add_mul, Nat.one_mul] at hkn
  unfold space
  omega

theorem owns_cons_addr {n base d : ℕ} (hd : d ≤ n) :
    base ≤ base + 8 * n + d ∧ base + 8 * n + d < base + space n := by
  unfold space
  omega

/-- An address outside the heap block `[base, base + space n)` lies below `base` or at least
`base + 9 * n + 1`. -/
theorem out_of_footprint (n base : ℕ) {a : ℕ} (ha : a < base ∨ base + space n ≤ a) :
    a < base ∨ base + 9 * n + 1 ≤ a := by
  unfold space at ha
  omega

/-! ## Shared primitives: `prioLTFlag`, `insertIntoNonEmptyList`, `addRootAndUpdateMin` -/

/-- `prioLTFlag uReg kuReg vReg kvReg flagReg` sets `flagReg ← 1` iff `(u, ku)` strictly precedes
`(v, kv)` under `IndexedMinPQ.PrioLT`, and `0` otherwise, within `6` instructions. -/
theorem prioLTFlag_exec {n base w : ℕ} {x : Data rFib} (hbr : BaseRegs n base x)
    (uReg kuReg vReg kvReg flagReg : Fin rFib) :
    let ltProp := x.regs kuReg < x.regs kvReg ∨
      (x.regs kuReg = x.regs kvReg ∧ x.regs uReg < x.regs vReg)
    let bval := if ltProp then 1 else 0
    ExecWithin w (prioLTFlag uReg kuReg vReg kvReg flagReg) x (x.set flagReg bval) 6 := by
  intro ltProp bval
  wram_exec [prioLTFlag, hbr.regs_zeroP, hbr.regs_oneP]
  all_goals
    congr 1
    dsimp only [bval, ltProp]
    split_ifs <;> omega

theorem prioLTFlag_preserves {r uReg kuReg vReg kvReg flagReg : Fin rFib} (hf : r ≠ flagReg) :
    (prioLTFlag uReg kuReg vReg kvReg flagReg).Preserves r := by
  simp only [prioLTFlag, Code.Preserves, Op.dest, ne_eq, Option.some.injEq, hf.symm,
    not_false_eq_true, and_self]

theorem insertIntoNonEmptyList_preserves {r hReg uReg : Fin rFib}
    (h0 : r ≠ s0) (h2 : r ≠ s2) :
    (insertIntoNonEmptyList hReg uReg).Preserves r := by
  simp only [insertIntoNonEmptyList, Code.Preserves, Op.dest, Op.exactBin, ne_eq,
    Option.some.injEq, reduceCtorEq, not_false_eq_true, h0.symm, h2.symm, and_self]

/-- `insertIntoNonEmptyList hReg uReg` splices `u` immediately after `h`, whose right neighbour is
`r`, in `10` instructions, modifying only `left[u], left[r], right[u], right[h]` and scratch
registers `s0, s2`. -/
theorem insertIntoNonEmptyList_exec {n base w : ℕ} {x : Data rFib}
    (hb : x.Bounded w) (hbr : BaseRegs n base x)
    {hReg uReg : Fin rFib} (hh0 : hReg ≠ s0) (hh2 : hReg ≠ s2) (hu0 : uReg ≠ s0) (hu2 : uReg ≠ s2)
    {h u r : Fin n} (hh_val : x.regs hReg = h.val) (hu_val : x.regs uReg = u.val)
    (hr : (RawState.ofData n base x).right h = r.val) :
    ∃ y, ExecWithin w (insertIntoNonEmptyList hReg uReg) x y 10 ∧
      BaseRegs n base y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      RawState.ofData n base y =
        { RawState.ofData n base x with
          left := Function.update (Function.update (RawState.ofData n base x).left u h.val) r u.val
          right := Function.update
            (Function.update (RawState.ofData n base x).right u r.val) h u.val } := by
  have hfit := hbr.fits_of_le hb
  have hh_lt := h.isLt
  have hu_lt := u.isLt
  have hr_lt := r.isLt
  have hr_mem : x.mem (base + 4 * n + h.val) = r.val := hr
  wram_exec [insertIntoNonEmptyList,
    hfit, hbr.regs_leftBase, hbr.regs_rightBase, hh_val, hu_val, hr_mem]
  refine ⟨by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr],
    Modifies.block_iff.2 fun a ha => by have := out_of_footprint n base ha; wram_simp, ?_⟩
  wram_simp [ofData_write_right, ofData_write_left, ofData_set_scratch]

theorem addRootAndUpdateMin_preserves {r uReg : Fin rFib}
    (h0 : r ≠ s0) (h1 : r ≠ s1) (h2 : r ≠ s2) (h3 : r ≠ s3) (h4 : r ≠ s4) (h5 : r ≠ s5)
    (hm : r ≠ minRootReg) (hnr : r ≠ numRootsReg) :
    (addRootAndUpdateMin uReg).Preserves r := by
  unfold addRootAndUpdateMin
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [Code.Preserves, Op.dest, Op.exactBin, ne_eq, Option.some.injEq, reduceCtorEq,
      not_false_eq_true, h0.symm, hm.symm, and_self]
  · refine ⟨by simp only [Code.Preserves, Op.dest, Op.exactBin, ne_eq, Option.some.injEq,
        h1.symm, not_false_eq_true],
      insertIntoNonEmptyList_preserves h0 h2, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, prioLTFlag_preserves h5, ?_⟩ <;>
      simp only [Code.Preserves, Op.dest, Op.exactBin, ne_eq, Option.some.injEq,
        h0.symm, h3.symm, h4.symm, hm.symm, not_false_eq_true, and_self]
  · simp only [Code.Preserves, Op.dest, Op.exactBin, ne_eq, Option.some.injEq,
      hnr.symm, not_false_eq_true]

/-- `addRootAndUpdateMin uReg` adds root `u` to the root list in at most `28` instructions: its
effect on the heap is `AddsRoot`, the same as the record program `addRoot`. -/
theorem addRootAndUpdateMin_exec {n base w : ℕ} {x : Data rFib}
    (hb : x.Bounded w) (hbr : BaseRegs n base x)
    {uReg : Fin rFib} (hu_sc : uReg ≠ s0 ∧ uReg ≠ s1 ∧ uReg ≠ s2 ∧ uReg ≠ s3 ∧ uReg ≠ s4 ∧
      uReg ≠ s5 ∧ uReg ≠ minRootReg ∧ uReg ≠ numRootsReg)
    {u : Fin n} (hu_val : x.regs uReg = u.val)
    (hroot : (RawState.ofData n base x).minRoot = 0 ∨ ∃ (m : Fin n) (rtail : List (Fin n)),
      (RawState.ofData n base x).minRoot = m.val + 1 ∧
      IsCircList (RawState.ofData n base x).left (RawState.ofData n base x).right (m :: rtail))
    (hnr : (RawState.ofData n base x).numRoots + 1 ≤ n) :
    ∃ y, ExecWithin w (addRootAndUpdateMin uReg) x y 28 ∧
      BaseRegs n base y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      AddsRoot (RawState.ofData n base x) u (RawState.ofData n base y) := by
  set st := RawState.ofData n base x with hst_def
  have hfit := hbr.fits_of_le hb
  have hu_lt := u.isLt
  obtain ⟨hu0, hu1, hu2, hu3, hu4, hu5, hum, hunr⟩ := hu_sc
  rcases hroot with hmin0 | ⟨m, rtail, hmin_m, hcirc⟩
  · -- Empty root list (`minRoot = 0`)
    have hmin_x : x.regs minRootReg = 0 := hmin0
    have hnr_x : x.regs numRootsReg = st.numRoots := rfl
    wram_exec [addRootAndUpdateMin,
      hfit, hbr.regs_leftBase, hbr.regs_rightBase, hbr.regs_zeroP, hbr.regs_oneP,
      hu_val, hmin_x, hnr_x]
    refine ⟨by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr],
      Modifies.block_iff.2 fun a ha => by have := out_of_footprint n base ha; wram_simp,
      Or.inl ⟨hmin0, ?_⟩⟩
    wram_simp [ofData_set_numRoots, ofData_set_minRoot, ofData_write_right, ofData_write_left,
      ofData_set_scratch, ← hst_def]
  · -- Non-empty root list (`minRoot = m.val + 1`)
    have hm_lt := m.isLt
    have hmin_x : x.regs minRootReg = m.val + 1 := hmin_m
    obtain ⟨r, hr_eq, -⟩ := hcirc.right_head
    wram_exec [addRootAndUpdateMin, hfit, hbr.regs_zeroP, hbr.regs_oneP, hmin_x]
    obtain ⟨x2, he_ins, hbr2, hmod2, hst2⟩ :=
      insertIntoNonEmptyList_exec (x := x.set s1 m.val) (hReg := s1) (uReg := uReg) (h := m)
        (u := u) (r := r) (hb.set (hfit _ (by omega))) (hbr.set_non_base (by decide) _)
        (by decide) (by decide) hu0 hu2 (by wram_simp) (by wram_simp [hu_val])
        (by rw [ofData_set_scratch _ (by decide : 17 ≤ s1.val)]; exact hr_eq)
    rw [ofData_set_scratch _ (by decide : 17 ≤ s1.val)] at hst2
    refine WP.of_execWithin he_ins ?_
    have hx2_u : x2.regs uReg = u.val := by
      rw [he_ins.regs_eq (insertIntoNonEmptyList_preserves hu0 hu2)]
      wram_simp [hu_val]
    have hx2_s1 : x2.regs s1 = m.val := by
      rw [he_ins.regs_eq (insertIntoNonEmptyList_preserves (by decide) (by decide))]
      wram_simp
    have hku_mem : x2.mem (base + u.val) = st.key u := congrFun (congrArg RawState.key hst2) u
    have hkm_mem : x2.mem (base + m.val) = st.key m := congrFun (congrArg RawState.key hst2) m
    wram_exec [hfit, hbr2.regs_baseReg, hx2_u, hx2_s1, hku_mem, hkm_mem]
    refine WP.name fun x4 hx4 => ?_
    have hbr4 : BaseRegs n base x4 := by
      subst hx4
      wram_simp [BaseRegs.set_iff, hbr2]
    have hflag : (x4.regs s3 < x4.regs s4 ∨ x4.regs s3 = x4.regs s4 ∧ x4.regs uReg < x4.regs s1) ↔
        IndexedMinPQ.PrioLT (u, st.key u) (m, st.key m) := by
      subst hx4
      wram_simp [hx2_u, hx2_s1]
      rfl
    refine WP.of_execWithin (prioLTFlag_exec (w := w) hbr4 uReg s3 s1 s4 s5) ?_
    simp only [hflag]
    subst hx4
    have hx2_nr : x2.regs numRootsReg = st.numRoots := congrArg RawState.numRoots hst2
    by_cases hlt : IndexedMinPQ.PrioLT (u, st.key u) (m, st.key m) <;>
      · wram_exec [hfit, hbr2.regs_zeroP, hbr2.regs_oneP, hx2_u, hx2_nr, hlt]
        refine ⟨by wram_simp [BaseRegs.set_iff, hbr2], hmod2, Or.inr ⟨m, r, hmin_m, hr_eq, ?_⟩⟩
        wram_simp [ofData_set_numRoots, ofData_set_minRoot, ofData_set_scratch, hst2, ← hst_def,
          hlt, ← hmin_m]

/-! ## `allocSpan`, `initSetup`, and `incCur` -/

theorem incCur_eval {w : ℕ} {x : Data rFib} (hone : x.regs oneReg = 1)
    (hfit : Fits w (x.regs curReg + 1)) :
    (Op.exactBin .add curReg curReg oneReg).eval w x = some (x.set curReg (x.regs curReg + 1)) := by
  rw [Op.eval_exactBin]
  simp only [BinOp.evalExact, Option.bind_some, hone]
  exact Data.put_of_fits hfit

theorem allocSpan_exec {n w base : ℕ} (hS : Fits w (base + space n)) {x : Data rFib}
    (_hx : x.Bounded w) (hfr : x.regs frontierReg = base)
    (hpar : ∀ j : Fin 1, x.regs (![nReg] j) = ![n] j) :
    ∃ x₁, ExecWithin w allocSpan x x₁ 12 ∧ x₁.mem = x.mem ∧
      x₁.regs baseReg = base ∧ x₁.regs frontierReg = base + space n ∧
      (∀ j : Fin 1, x₁.regs (![nReg] j) = ![n] j) := by
  have hn : x.regs nReg = n := hpar 0
  have hfit (v : ℕ) (hv : v ≤ base + (9 * n + 1)) : Fits w v := by
    unfold space at hS
    exact hS.of_le hv
  wram_exec [allocSpan, hfit, hfr, hn]
  refine ⟨rfl, by wram_simp, by wram_simp [space]; omega, fun j => ?_⟩
  fin_cases j
  wram_simp
  exact hpar _

theorem initSetup_exec {n K_max w base : ℕ} {x₁ : Data rFib}
    (hx₁ : x₁.Bounded w) (hb₁ : x₁.regs baseReg = base)
    (hfr₁ : x₁.regs frontierReg = base + space n)
    (hpar₁ : ∀ j : Fin 1, x₁.regs (![nReg] j) = ![n] j)
    (hz : ∀ a ∈ (Block.mk base (space n)).footprint, x₁.mem a = 0) :
    ∃ y, ExecWithin w initSetup x₁ y 14 ∧ y.regs frontierReg = base + space n ∧
      FibInv n K_max w base (IndexedMinPQ.empty n) y ∧ potential y ≤ 0 ∧
      Modifies (Block.mk base (space n)).footprint x₁.mem y.mem := by
  have hn : x₁.regs nReg = n := hpar₁ 0
  have hS : Fits w (base + space n) := hfr₁ ▸ hx₁.1 frontierReg
  have hfit (v : ℕ) (hv : v ≤ base + (9 * n + 1)) : Fits w v := by
    unfold space at hS
    exact hS.of_le hv
  unfold initSetup
  refine WP.exists_execWithin (WP.bounded hx₁ ?_)
  wram_exec [hfit, hb₁, hn]
  intro hby
  refine ⟨by omega, by wram_simp [hfr₁], ⟨hby, ?_, ?_⟩, by wram_simp [potential]; omega,
    Modifies.refl _ _⟩
  · (refine ⟨by wram_simp [hn], by wram_simp [hfr₁], by wram_simp [hb₁],
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      wram_simp) <;> omega
  · refine FibRawInv.empty
      (fun v => hz _ (Block.mem_footprint.mpr (owns_arr_addr (by decide) v.isLt)))
      (fun d hd => by
        change (if d ≤ n then x₁.mem (base + 8 * n + d) else 0) = 0
        simp only [hd, ↓reduceIte]
        exact hz _ (Block.mem_footprint.mpr (owns_cons_addr hd)))
      ?_ ?_ ?_ ?_ <;> wram_simp [RawState.ofData]

/-! ## `isEmptyCode`, `getKeyCode`, and `insertCode` -/

theorem isEmptyCode_exec {n K_max w base : ℕ} {s : IndexedMinPQ.State n} {x : Data rFib}
    (hinv : FibInv n K_max w base s x) :
    ∃ y t, ExecWithin w isEmptyCode x y t ∧
      code.decode (n := n) (K_max := K_max) .isEmpty y.regs =
        some (decide (IndexedMinPQ.dom s = ∅)) ∧
      FibInv n K_max w base s y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      t + potential y ≤ 3 + potential x := by
  obtain ⟨hb, hbr, hraw⟩ := hinv
  change WP w isEmptyCode x fun y t => _
  unfold isEmptyCode
  refine WP.bounded hb ?_
  wram_exec [hbr.regs_zeroP, hbr.regs_oneP]
  · intro hby
    obtain ⟨hdom, _⟩ := hraw.findMin_eq_none hc
    refine ⟨by wram_simp [PQCode.decode, code, hdom]; rfl,
      ⟨hby, hbr.set_non_base (by decide) 1,
        (ofData_set_scratch x (by decide : 17 ≤ outFlag.val) 1).symm ▸ hraw⟩,
      Modifies.refl _ _, ?_⟩
    rw [potential_set_scratch x (by decide : 17 ≤ outFlag.val) 1]
    omega
  · intro hby
    have hdom_ne : IndexedMinPQ.dom s ≠ ∅ := by
      have hm_le : x.regs minRootReg ≤ n := hraw.bounds.2.2.2
      let z : Fin n := ⟨x.regs minRootReg - 1, by omega⟩
      have hz_eq : (RawState.ofData n base x).minRoot = z.val + 1 := by
        change x.regs minRootReg = x.regs minRootReg - 1 + 1; omega
      obtain ⟨_, hsz, _⟩ := hraw.findMin_eq_some hz_eq
      intro hemp
      have hmem : z ∈ IndexedMinPQ.dom s := IndexedMinPQ.mem_dom_iff.mpr ⟨_, hsz⟩
      rw [hemp] at hmem
      exact Finset.notMem_empty z hmem
    refine ⟨by wram_simp [PQCode.decode, code, hdom_ne]; rfl,
      ⟨hby, hbr.set_non_base (by decide) 0,
        (ofData_set_scratch x (by decide : 17 ≤ outFlag.val) 0).symm ▸ hraw⟩,
      Modifies.refl _ _, ?_⟩
    rw [potential_set_scratch x (by decide : 17 ≤ outFlag.val) 0]

theorem getKeyCode_exec {n K_max w base : ℕ} {s : IndexedMinPQ.State n} {x : Data rFib}
    (v : Fin n) (hinv : FibInv n K_max w base s x) (hv_reg : x.regs argV = v.val) :
    ∃ y t, ExecWithin w getKeyCode x y t ∧
      code.decode (K_max := K_max) (.getKey v) y.regs = some (s v) ∧
      FibInv n K_max w base s y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      t + potential y ≤ 7 + potential x := by
  obtain ⟨hb, hbr, hraw⟩ := hinv
  have hfit := hbr.fits_of_le hb
  have hv_lt := v.isLt
  let st := RawState.ofData n base x
  have hraw' : FibRawInv n K_max s st := hraw
  rcases hraw with ⟨_, _, _, _, hin_spec, hkey_spec, _, _, _, _, _⟩
  change WP w getKeyCode x fun y t => _
  unfold getKeyCode
  refine WP.bounded hb ?_
  cases hsv : s v with
  | none =>
    have hin0 : st.inHeap v = 0 := by
      by_contra hne
      have := (hin_spec v).1.mp hne
      simp only [hsv, Option.isSome_none, Bool.false_eq_true] at this
    have hin_mem : x.mem (base + 7 * n + v.val) = 0 := hin0
    wram_exec [hfit, hbr.regs_inBase, hbr.regs_zeroP, hv_reg, hin_mem]
    intro hby
    refine ⟨by wram_simp [PQCode.decode, code],
      ⟨hby, by wram_simp [BaseRegs.set_iff, hbr], by wram_simp [ofData_set_scratch]; exact hraw'⟩,
      Modifies.refl _ _, by wram_simp [potential_set_scratch]; omega⟩
  | some kv =>
    have hin_ne : st.inHeap v ≠ 0 :=
      (hin_spec v).1.mpr (by simp only [hsv, Option.isSome_some])
    have hin_mem : x.mem (base + 7 * n + v.val) = st.inHeap v := rfl
    have hkv_mem : x.mem (base + v.val) = kv := (hkey_spec v kv hsv).1
    wram_exec [hfit, hbr.regs_inBase, hbr.regs_baseReg, hbr.regs_zeroP, hv_reg,
      hin_mem, hin_ne, hkv_mem]
    intro hby
    refine ⟨by wram_simp [PQCode.decode, code, hin_ne],
      ⟨hby, by wram_simp [BaseRegs.set_iff, hbr], by wram_simp [ofData_set_scratch]; exact hraw'⟩,
      Modifies.refl _ _, by wram_simp [potential_set_scratch]; omega⟩

theorem insertCode_exec {n K_max w base : ℕ} {s : IndexedMinPQ.State n} {x : Data rFib}
    (v : Fin n) (k : ℕ) (hinv : FibInv n K_max w base s x)
    (hval : s v = none ∧ k ≤ K_max) (hv_reg : x.regs argV = v.val) (hk_reg : x.regs argK = k) :
    ∃ y t, ExecWithin w insertCode x y t ∧
      FibInv n K_max w base (Function.update s v (some k)) y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      t + potential y ≤ 121 + potential x := by
  obtain ⟨hb, hbr, hraw⟩ := hinv
  have hfit := hbr.fits_of_le hb
  have hv_lt := v.isLt
  set st := RawState.ofData n base x with hst_def
  have hcnt : st.numRoots + 1 ≤ n ∧ st.sz + 1 ≤ n :=
    FibonacciHeap.counts_lt_of_absent hraw hval.1
  have hroot : st.minRoot = 0 ∨ ∃ (m : Fin n) (rtail : List (Fin n)),
      st.minRoot = m.val + 1 ∧ IsCircList st.left st.right (m :: rtail) :=
    FibonacciHeap.minRoot_cases hraw
  change WP w insertCode x fun y t => _
  unfold insertCode
  refine WP.bounded hb ?_
  wram_exec [hfit, hbr.regs_baseReg, hbr.regs_parBase, hbr.regs_childBase, hbr.regs_degBase,
    hbr.regs_markBase, hbr.regs_inBase, hbr.regs_zeroP, hbr.regs_oneP, hv_reg, hk_reg]
  refine WP.name fun x6 hx6 => ?_
  have hb6 : x6.Bounded w := by
    subst hx6; subst hk_reg
    wram_bounded <;> exact hfit _ (by omega)
  have hbr6 : BaseRegs n base x6 := by
    subst hx6
    wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr]
  have hmod16 : Modifies (Block.mk base (space n)).footprint x.mem x6.mem := by
    subst hx6
    exact Modifies.block_iff.2 fun a ha => by have := out_of_footprint n base ha; wram_simp
  have hst6 : RawState.ofData n base x6 = newNode st v k := by
    subst hx6
    wram_simp [newNode, ofData_write_inHeap, ofData_write_mark, ofData_write_deg,
      ofData_write_child, ofData_write_par, ofData_write_key, ofData_set_scratch, ← hst_def]
  have hx6_v : x6.regs argV = v.val := by subst hx6; wram_simp [hv_reg]
  obtain ⟨x7, he_add, hbr7, hmod7, hadd⟩ :=
    addRootAndUpdateMin_exec hb6 hbr6
      ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
      hx6_v (by rw [hst6]; exact hroot) (by rw [hst6]; exact hcnt.1)
  rw [hst6] at hadd
  obtain ⟨left, right, minRoot, hst7⟩ := hadd.exists_eq
  refine WP.of_execWithin he_add ?_
  have hx7_sz : x7.regs szReg = st.sz := congrArg RawState.sz hst7
  have := hcnt.2
  wram_exec [hfit, hbr7.regs_oneP, hx7_sz]
  intro hby
  refine ⟨⟨hby, hbr7.set_non_base (by decide) _, ?_⟩, modifies_block_trans hmod16 hmod7, ?_⟩
  · have hsty : RawState.ofData n base (x7.set szReg (st.sz + 1)) =
        { RawState.ofData n base x7 with sz := (RawState.ofData n base x7).sz + 1 } := by
      rw [ofData_set_sz, hst7]
      rfl
    rw [hsty]
    exact FibonacciHeap.FibRawInv.insert hraw hval.1 hval.2 hadd
  · have hx7_nr : x7.regs numRootsReg = st.numRoots + 1 := congrArg RawState.numRoots hst7
    have hx7_nm : x7.regs numMarkedReg = st.numMarked := congrArg RawState.numMarked hst7
    have hx_nr : x.regs numRootsReg = st.numRoots := rfl
    have hx_nm : x.regs numMarkedReg = st.numMarked := rfl
    wram_simp [potential, hx7_nr, hx7_nm, hx_nr, hx_nm, unitCredit]
    omega

end Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap
