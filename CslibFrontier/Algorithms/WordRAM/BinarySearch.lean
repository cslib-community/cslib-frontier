/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.Query.BinarySearch
public import CslibFrontier.Computability.WordRAM.ListOutput
import CslibFrontier.Computability.WordRAM.Allocation
import CslibFrontier.Computability.WordRAM.InputArray
import CslibFrontier.Computability.WordRAM.ListArray
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import Mathlib.Data.List.Sort

/-!
# Binary Search on the Word RAM

This module implements overflow-safe bisection (`mid = lo + ((hi - lo) >>> 1)`) on the standard
Word RAM in two forms:

1. **Reusable bisection combinator (`bisectCode`):** parameterized by any structured probe block
   `probe : Code .standard r` that tests `mid ∈ [L, R)` within `T_probe` instructions and sets
   `res` to a positive word when `t mid = true` and `0` otherwise. From any state with
   `L ≤ lo`, `hi ≤ R`, and `Fits w hi`, `bisectCode` executes within
   `(T_probe + 8) * (Nat.log 2 (hi - lo) + 1) + 2` instructions (`2` instructions when `hi ≤ lo`)
   and leaves `Cslib.Algorithms.Lean.lowerBound t lo hi` in register `lo`.

2. **Standalone sorted-array lower-bound program (`lowerBoundCode`, `lowerBoundProgram`):**
   searches an array `arr` of words for the first index whose entry is at least `key`, computing
   `[lowerBound (fun i => decide (arr.toArray[i]! < key)) 0 arr.length]` in
   `13 * (Nat.log 2 |arr| + 1) + 14` instructions at every word width `w` with
   `Fits w (|arr| + 3)`. On sorted arrays (`arr.Pairwise (· ≤ ·)`), this index splits `arr` into
   entries `< key` and entries `≥ key` (`lowerBound_sorted_spec`).

## Main definitions

* `Cslib.Algorithms.WordRAM.BinarySearch.bisectCode`: structured Word-RAM bisection combinator
  parameterized by a probe `Code`.
* `Cslib.Algorithms.WordRAM.BinarySearch.LowerBoundInput`: input record (`key`, `arr`) for array
  lower-bound search, with `LowerBoundInput.encode`.
* `Cslib.Algorithms.WordRAM.BinarySearch.Reg.out`: output base register (`9`).
* `Cslib.Algorithms.WordRAM.BinarySearch.lowerBoundCode`, `lowerBoundProgram`: standalone Word-RAM
  array lower-bound code and uniform `Program .standard 10`.

## Main results

* `Cslib.Algorithms.WordRAM.BinarySearch.bisectCode_exec_tight` and `bisectCode_exec`: logarithmic
  instruction-count bounds and exact functional agreement with `Cslib.Algorithms.Lean.lowerBound`.
* `Cslib.Algorithms.WordRAM.BinarySearch.lowerBoundCode_exec` and
  `lowerBoundProgram_computesListInTime`: `O(log |arr|)` Word-RAM array lower-bound execution.
* `Cslib.Algorithms.WordRAM.BinarySearch.lowerBound_sorted_spec`: sorted-array partition property
  of the computed lower-bound index.
-/

public section

namespace Cslib.Algorithms.WordRAM.BinarySearch

open Cslib.WordRAM
open Cslib.Algorithms.Lean

/-! ## Parameterized Word-RAM bisection combinator -/

/-- Structured Word-RAM bisection on `[lo, hi)`: while `lo < hi`, computes the overflow-safe
midpoint `mid ← lo + ((hi - lo) >>> 1)`, runs `probe` (which tests `mid` and writes a positive
word to `res` for `true` or `0` for `false`), and updates `lo ← mid + 1` or `hi ← mid`. Leaves
`Cslib.Algorithms.Lean.lowerBound` in `lo` (and `hi = lo` when `lo ≤ hi`). Requires registers
`zero` and `one` holding `0` and `1`. -/
def bisectCode {r : ℕ} (lo hi mid res zero one : Fin r) (probe : Code .standard r) :
    Code .standard r :=
  ram[
    while lo < hi do [
      mid ← hi - lo;
      mid ← mid >>> one;
      mid ← lo + mid;
      ⟪probe⟫;
      if zero < res then [
        lo ← mid + one
      ] else [
        hi ← mid
      ]
    ]
  ]

private theorem log_step {d k' : ℕ} (hd : 0 < d) (hk : 2 * k' ≤ d) :
    1 + Nat.log 2 (2 * k') ≤ Nat.log 2 (2 * d) := by
  rcases Nat.eq_zero_or_pos k' with rfl | hpos
  · simpa using Nat.le_log_of_pow_le (b := 2) (by decide) (by omega : 2 ^ 1 ≤ 2 * d)
  · rw [Nat.add_comm, ← Nat.log_mul_base (by decide) (by omega)]
    exact Nat.log_mono_right (by omega)

private theorem bisectBody_exec {r w T_probe L R : ℕ} {lo hi mid res zero one : Fin r}
    (hd : [lo, hi, mid, res, zero, one].Nodup)
    {probe : Code .standard r} {Inv : Data r → Prop} (t : ℕ → Bool)
    (hz : ∀ s, Inv s → s.regs zero = 0)
    (ho : ∀ s, Inv s → s.regs one = 1)
    (hset_lo : ∀ s v, Inv s → Inv (s.set lo v))
    (hset_hi : ∀ s v, Inv s → Inv (s.set hi v))
    (hset_mid : ∀ s v, Inv s → Inv (s.set mid v))
    (hprobe : ∀ s, Inv s → L ≤ s.regs mid → s.regs mid < R →
      ∃ s', ExecWithin w probe s s' T_probe ∧ Inv s' ∧
        s'.regs lo = s.regs lo ∧ s'.regs hi = s.regs hi ∧ s'.regs mid = s.regs mid ∧
        (0 < s'.regs res ↔ t (s.regs mid) = true))
    (x : Data r) (hx : Inv x) (hlt : x.regs lo < x.regs hi)
    (hL : L ≤ x.regs lo) (hR : x.regs hi ≤ R) (hfit_hi : Fits w (x.regs hi)) :
    ∃ y, ExecWithin w
        (ram[ mid ← hi - lo; mid ← mid >>> one; mid ← lo + mid; ⟪probe⟫;
              if zero < res then [ lo ← mid + one ] else [ hi ← mid ] ])
        x y (T_probe + 6) ∧
      Inv y ∧
      (if t ((x.regs lo + x.regs hi) / 2) then
        y.regs lo = (x.regs lo + x.regs hi) / 2 + 1 ∧ y.regs hi = x.regs hi
      else
        y.regs lo = x.regs lo ∧ y.regs hi = (x.regs lo + x.regs hi) / 2) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hd
  obtain ⟨⟨hlh, hlm, hlr, hlz, hlo⟩, ⟨hhm, hhr, hhz, hho⟩, ⟨hmr, hmz, hmo⟩,
    ⟨hrz, hro⟩, hzo⟩ := hd
  set lo₀ := x.regs lo
  set hi₀ := x.regs hi
  set m := (lo₀ + hi₀) / 2
  have hm_eq : lo₀ + ((hi₀ - lo₀) >>> 1) = m := by
    rw [Nat.shiftRight_eq_div_pow]
    omega
  set s₁ := x.set mid (hi₀ - lo₀)
  have hs₁_inv : Inv s₁ := hset_mid x (hi₀ - lo₀) hx
  have hs₁_mid : s₁.regs mid = hi₀ - lo₀ := Data.set_regs_self x mid _
  have hs₁_one : s₁.regs one = 1 :=
    (Data.set_regs_of_ne (Ne.symm hmo) _).trans (ho x hx)
  have e₁ : ExecWithin w (.op (.bin .sub mid hi lo)) x s₁ 1 :=
    ExecWithin.bin (hfit_hi.of_le (by simp only [BinOp.eval]; omega))
  set s₂ := s₁.set mid ((hi₀ - lo₀) >>> 1)
  have hs₂_inv : Inv s₂ := hset_mid s₁ _ hs₁_inv
  have hs₂_lo : s₂.regs lo = lo₀ :=
    (Data.set_regs_of_ne hlm _).trans (Data.set_regs_of_ne hlm _)
  have hs₂_hi : s₂.regs hi = hi₀ :=
    (Data.set_regs_of_ne hhm _).trans (Data.set_regs_of_ne hhm _)
  have hs₂_mid : s₂.regs mid = (hi₀ - lo₀) >>> 1 := Data.set_regs_self s₁ mid _
  have e₂ : ExecWithin w (.op (.bin .shiftRight mid mid one)) s₁ s₂ 1 := by
    have hf : Fits w (BinOp.shiftRight.eval (s₁.regs mid) (s₁.regs one)) := by
      simp only [BinOp.eval, hs₁_mid, hs₁_one, Nat.shiftRight_eq_div_pow]
      exact hfit_hi.of_le (by omega)
    simpa only [BinOp.eval, hs₁_mid, hs₁_one] using ExecWithin.bin hf
  set s₃ := s₂.set mid m
  have hs₃_inv : Inv s₃ := hset_mid s₂ m hs₂_inv
  have hs₃_lo : s₃.regs lo = lo₀ := (Data.set_regs_of_ne hlm _).trans hs₂_lo
  have hs₃_hi : s₃.regs hi = hi₀ := (Data.set_regs_of_ne hhm _).trans hs₂_hi
  have hs₃_mid : s₃.regs mid = m := Data.set_regs_self s₂ mid m
  have e₃ : ExecWithin w (.op (.bin .add mid lo mid)) s₂ s₃ 1 := by
    have hf : Fits w (BinOp.add.eval (s₂.regs lo) (s₂.regs mid)) := by
      simp only [BinOp.eval, hs₂_lo, hs₂_mid, hm_eq]
      exact hfit_hi.of_le (by omega)
    simpa only [BinOp.eval, hs₂_lo, hs₂_mid, hm_eq] using ExecWithin.bin hf
  obtain ⟨s₄, e₄, hs₄_inv, hs₄_lo, hs₄_hi, hs₄_mid, hs₄_res⟩ :=
    hprobe s₃ hs₃_inv (by rw [hs₃_mid]; omega) (by rw [hs₃_mid]; omega)
  rw [hs₃_lo] at hs₄_lo
  rw [hs₃_hi] at hs₄_hi
  rw [hs₃_mid] at hs₄_mid hs₄_res
  have hs₄_zero : s₄.regs zero = 0 := hz s₄ hs₄_inv
  have hs₄_one : s₄.regs one = 1 := ho s₄ hs₄_inv
  by_cases htm : t m = true
  · have hc : (Cond.lt zero res).Holds s₄ := by
      simp only [Cond.holds_lt, hs₄_zero]
      exact hs₄_res.mpr htm
    have e₅ : ExecWithin w
        (ram[ if zero < res then [ lo ← mid + one ] else [ hi ← mid ] ])
        s₄ (s₄.set lo (m + 1)) 2 := by
      have hf : Fits w (BinOp.add.eval (s₄.regs mid) (s₄.regs one)) := by
        simp only [BinOp.eval, hs₄_mid, hs₄_one]
        exact hfit_hi.of_le (by omega)
      have eb : ExecWithin w (.op (.bin .add lo mid one)) s₄ (s₄.set lo (m + 1)) 1 := by
        simpa only [BinOp.eval, hs₄_mid, hs₄_one] using ExecWithin.bin hf
      exact ExecWithin.branch_pos hc eb
    refine ⟨s₄.set lo (m + 1),
      (e₁.seq (e₂.seq (e₃.seq (e₄.seq e₅)))).mono (by omega),
      hset_lo s₄ (m + 1) hs₄_inv, ?_⟩
    simp only [htm, ↓reduceIte, Data.set_regs_self,
      Data.set_regs_of_ne (Ne.symm hlh), hs₄_hi, and_self]
  · have hc : ¬(Cond.lt zero res).Holds s₄ := by
      simp only [Cond.holds_lt, hs₄_zero]
      exact fun hpos => htm (hs₄_res.mp hpos)
    have e₅ : ExecWithin (B := .standard) w
        (ram[ if zero < res then [ lo ← mid + one ] else [ hi ← mid ] ])
        s₄ (s₄.set hi m) 3 := by
      have ec : ExecWithin (B := .standard) w (.op (.copy hi mid)) s₄ (s₄.set hi m) 1 := by
        simpa only [hs₄_mid] using
          (ExecWithin.copy (B := .standard) (d := hi) (s := mid) (x := s₄))
      exact ExecWithin.branch_neg hc ec
    refine ⟨s₄.set hi m,
      (e₁.seq (e₂.seq (e₃.seq (e₄.seq e₅)))).mono (by omega),
      hset_hi s₄ m hs₄_inv, ?_⟩
    have htm' : t m = false := Bool.eq_false_iff.mpr htm
    simp only [htm', Bool.false_eq_true, ↓reduceIte, Data.set_regs_self,
      Data.set_regs_of_ne hlh, hs₄_lo, and_self]

/-- **Tight logarithmic execution bound for `bisectCode`.** Runs within
`(T_probe + 8) * Nat.log 2 (2 * (hi - lo)) + 2` instructions (`2` instructions when `hi ≤ lo`),
preserving `Inv` and setting `lo` to `lowerBound t lo hi`. -/
theorem bisectCode_exec_tight {r w T_probe L R : ℕ} {lo hi mid res zero one : Fin r}
    (hd : [lo, hi, mid, res, zero, one].Nodup)
    {probe : Code .standard r} {Inv : Data r → Prop} (t : ℕ → Bool)
    (hz : ∀ s, Inv s → s.regs zero = 0)
    (ho : ∀ s, Inv s → s.regs one = 1)
    (hset_lo : ∀ s v, Inv s → Inv (s.set lo v))
    (hset_hi : ∀ s v, Inv s → Inv (s.set hi v))
    (hset_mid : ∀ s v, Inv s → Inv (s.set mid v))
    (hprobe : ∀ s, Inv s → L ≤ s.regs mid → s.regs mid < R →
      ∃ s', ExecWithin w probe s s' T_probe ∧ Inv s' ∧
        s'.regs lo = s.regs lo ∧ s'.regs hi = s.regs hi ∧ s'.regs mid = s.regs mid ∧
        (0 < s'.regs res ↔ t (s.regs mid) = true))
    (x : Data r) (hx : Inv x) (hL : L ≤ x.regs lo) (hR : x.regs hi ≤ R)
    (hfit_hi : Fits w (x.regs hi)) :
    ∃ y, ExecWithin w (bisectCode lo hi mid res zero one probe) x y
        ((T_probe + 8) * Nat.log 2 (2 * (x.regs hi - x.regs lo)) + 2) ∧
      Inv y ∧
      y.regs lo = lowerBound t (x.regs lo) (x.regs hi) ∧
      (x.regs lo ≤ x.regs hi → y.regs hi = y.regs lo) := by
  set lo₀ := x.regs lo
  set hi₀ := x.regs hi
  suffices ∀ (a b : ℕ) (s : Data r), s.regs lo = a → s.regs hi = b →
      Inv s → L ≤ a → b ≤ R → Fits w b →
      ∃ y, ExecWithin w (bisectCode lo hi mid res zero one probe) s y
          ((T_probe + 8) * Nat.log 2 (2 * (b - a)) + 2) ∧
        Inv y ∧ y.regs lo = lowerBound t a b ∧ (a ≤ b → y.regs hi = y.regs lo) from
    this lo₀ hi₀ x rfl rfl hx hL hR hfit_hi
  intro a b
  fun_induction lowerBound t a b with
  | case1 a b hlt htm ihR =>
    intro s hsa hsb hs hLa hbR hfit
    obtain ⟨s₁, hstep, hs₁, hbr⟩ := bisectBody_exec hd t hz ho hset_lo hset_hi hset_mid hprobe
      s hs (by omega) (by omega) (by omega) (by rwa [hsb])
    rw [hsa, hsb, ite_eq_left htm] at hbr
    obtain ⟨y, hrec, hy_inv, hy_lo, hy_hi⟩ :=
      ihR s₁ hbr.1 hbr.2 hs₁ (by omega) hbR hfit
    have hc : (Cond.lt lo hi).Holds s := by simp only [Cond.holds_lt, hsa, hsb]; exact hlt
    have hlog := Nat.mul_le_mul_left (T_probe + 8)
      (log_step (d := b - a) (k' := b - ((a + b) / 2 + 1)) (by omega) (by omega))
    rw [Nat.mul_add, Nat.mul_one] at hlog
    refine ⟨y, (ExecWithin.loop_iter hc hstep hrec).mono (by omega),
      hy_inv, hy_lo, fun _ => hy_hi (by omega)⟩
  | case2 a b hlt htm ihL =>
    intro s hsa hsb hs hLa hbR hfit
    obtain ⟨s₁, hstep, hs₁, hbr⟩ := bisectBody_exec hd t hz ho hset_lo hset_hi hset_mid hprobe
      s hs (by omega) (by omega) (by omega) (by rwa [hsb])
    rw [hsa, hsb, ite_eq_right htm] at hbr
    obtain ⟨y, hrec, hy_inv, hy_lo, hy_hi⟩ :=
      ihL s₁ hbr.1 hbr.2 hs₁ hLa (by omega) (hfit.of_le (by omega))
    have hc : (Cond.lt lo hi).Holds s := by simp only [Cond.holds_lt, hsa, hsb]; exact hlt
    have hlog := Nat.mul_le_mul_left (T_probe + 8)
      (log_step (d := b - a) (k' := (a + b) / 2 - a) (by omega) (by omega))
    rw [Nat.mul_add, Nat.mul_one] at hlog
    refine ⟨y, (ExecWithin.loop_iter hc hstep hrec).mono (by omega),
      hy_inv, hy_lo, fun _ => hy_hi (by omega)⟩
  | case3 a b hle =>
    intro s hsa hsb hs _ _ _
    have hc : ¬(Cond.lt lo hi).Holds s := by simp only [Cond.holds_lt, hsa, hsb]; exact hle
    refine ⟨s, (ExecWithin.loop_exit hc).mono (by omega), hs, hsa, fun h => ?_⟩
    rw [hsa, hsb]; omega

/-- **Logarithmic execution bound for `bisectCode`.** Runs within
`(T_probe + 8) * (Nat.log 2 (hi - lo) + 1) + 2` instructions, preserving `Inv` and setting `lo` to
`lowerBound t lo hi`. -/
theorem bisectCode_exec {r w T_probe L R : ℕ} {lo hi mid res zero one : Fin r}
    (hd : [lo, hi, mid, res, zero, one].Nodup)
    {probe : Code .standard r} {Inv : Data r → Prop} (t : ℕ → Bool)
    (hz : ∀ s, Inv s → s.regs zero = 0)
    (ho : ∀ s, Inv s → s.regs one = 1)
    (hset_lo : ∀ s v, Inv s → Inv (s.set lo v))
    (hset_hi : ∀ s v, Inv s → Inv (s.set hi v))
    (hset_mid : ∀ s v, Inv s → Inv (s.set mid v))
    (hprobe : ∀ s, Inv s → L ≤ s.regs mid → s.regs mid < R →
      ∃ s', ExecWithin w probe s s' T_probe ∧ Inv s' ∧
        s'.regs lo = s.regs lo ∧ s'.regs hi = s.regs hi ∧ s'.regs mid = s.regs mid ∧
        (0 < s'.regs res ↔ t (s.regs mid) = true))
    (x : Data r) (hx : Inv x) (hL : L ≤ x.regs lo) (hR : x.regs hi ≤ R)
    (hfit_hi : Fits w (x.regs hi)) :
    ∃ y, ExecWithin w (bisectCode lo hi mid res zero one probe) x y
        ((T_probe + 8) * (Nat.log 2 (x.regs hi - x.regs lo) + 1) + 2) ∧
      Inv y ∧
      y.regs lo = lowerBound t (x.regs lo) (x.regs hi) ∧
      (x.regs lo ≤ x.regs hi → y.regs hi = y.regs lo) := by
  obtain ⟨y, hexec, hy_inv, hy_lo, hy_hi⟩ :=
    bisectCode_exec_tight hd t hz ho hset_lo hset_hi hset_mid hprobe x hx hL hR hfit_hi
  have hlog : Nat.log 2 (2 * (x.regs hi - x.regs lo)) ≤ Nat.log 2 (x.regs hi - x.regs lo) + 1 := by
    rcases Nat.eq_zero_or_pos (x.regs hi - x.regs lo) with h0 | hpos
    · simp only [h0, Nat.mul_zero, Nat.log_zero_right, Nat.zero_le]
    · rw [show 2 * (x.regs hi - x.regs lo) = (x.regs hi - x.regs lo) * 2 by omega,
        Nat.log_mul_base (by decide) (by omega)]
  have hmul := Nat.mul_le_mul_left (T_probe + 8) hlog
  exact ⟨y, hexec.mono (by omega), hy_inv, hy_lo, hy_hi⟩

/-! ## Standalone sorted-array lower-bound program -/

/-- Input to standalone Word-RAM array lower-bound search: a target key and a word array. -/
structure LowerBoundInput where
  /-- Target key to locate. -/
  key : ℕ
  /-- Word array searched by bisection. -/
  arr : List ℕ
  deriving DecidableEq, Repr

/-- Flat word-list encoding of `LowerBoundInput`: `key :: arr`, so `State.init I.encode` places
`|arr| + 1` at `mem[0]`, `key` at `mem[1]`, and `arr` at `[2, 2 + |arr|)`. -/
@[expose] def LowerBoundInput.encode (I : LowerBoundInput) : List ℕ :=
  I.key :: I.arr

/-- Pure array lower-bound predicate for `I`: `arr[i]! < key`. -/
@[expose] def LowerBoundInput.ltKey (I : LowerBoundInput) (i : ℕ) : Bool :=
  decide (I.arr.toArray[i]! < I.key)

/-- Pure lower-bound index of `I.key` in `I.arr`. -/
@[expose] def LowerBoundInput.result (I : LowerBoundInput) : ℕ :=
  lowerBound I.ltKey 0 I.arr.length

/-- On a sorted (`Pairwise (· ≤ ·)`) array, `I.result` lies in `[0, |I.arr|]`, every element before
`I.result` is strictly below `I.key`, and every element from `I.result` onward is at least
`I.key`. -/
theorem lowerBound_sorted_spec (I : LowerBoundInput) (hsort : I.arr.Pairwise (· ≤ ·)) :
    I.result ≤ I.arr.length ∧
      (∀ (i : ℕ) (hi : i < I.result),
        I.arr[i]'(by
          have := (lowerBound_bounds I.ltKey 0 I.arr.length).2
          simp only [LowerBoundInput.result] at hi
          omega) < I.key) ∧
      (∀ (i : ℕ) (hi : i < I.arr.length), I.result ≤ i → I.key ≤ I.arr[i]'hi) := by
  have hmono : ∀ m m', 0 ≤ m → m ≤ m' → m' < I.arr.length →
      I.ltKey m' = true → I.ltKey m = true := by
    intro m m' _ hmm' hm' ht
    simp only [LowerBoundInput.ltKey, decide_eq_true_eq] at ht ⊢
    rw [getElem!_pos I.arr.toArray m' (by simpa using hm'), List.getElem_toArray] at ht
    rw [getElem!_pos I.arr.toArray m (by simp only [List.size_toArray]; omega),
      List.getElem_toArray]
    rcases Nat.eq_or_lt_of_le hmm' with rfl | hlt
    · exact ht
    · exact lt_of_le_of_lt (List.pairwise_iff_getElem.mp hsort m m' (by omega) hm' hlt) ht
  obtain ⟨_, hb2, hlt_seg, hge_seg⟩ := lowerBound_spec I.ltKey hmono
  refine ⟨by simpa [LowerBoundInput.result] using hb2, fun i hi => ?_, fun i hi hge => ?_⟩
  · have hi_lt : i < I.arr.length := by
      simp only [LowerBoundInput.result] at hi
      omega
    simpa only [LowerBoundInput.ltKey, decide_eq_true_eq,
      getElem!_pos I.arr.toArray i (by simpa using hi_lt), List.getElem_toArray] using
      hlt_seg i (Nat.zero_le _) hi
  · simpa only [LowerBoundInput.ltKey, decide_eq_false_iff_not, not_lt,
      getElem!_pos I.arr.toArray i (by simpa using hi), List.getElem_toArray] using
      hge_seg i hge hi

private abbrev loReg : Fin 10 := 0
private abbrev hiReg : Fin 10 := 1
private abbrev midReg : Fin 10 := 2
private abbrev resReg : Fin 10 := 3
private abbrev zeroReg : Fin 10 := 4
private abbrev oneReg : Fin 10 := 5
private abbrev arrBaseReg : Fin 10 := 6
private abbrev keyReg : Fin 10 := 7
private abbrev tmpReg : Fin 10 := 8

/-- Output base register (`9`) for `lowerBoundCode` and `lowerBoundProgram`. -/
abbrev Reg.out : Fin 10 := 9

open Reg

private def lowerBoundSetup : Code .standard 10 := ram[
  zeroReg ← #0;
  oneReg ← #1;
  arrBaseReg ← #2;
  keyReg ← *oneReg;
  hiReg ← *zeroReg;
  hiReg ← hiReg - oneReg;
  loReg ← zeroReg;
  out ← arrBaseReg + hiReg ]

private def arrayProbeCode : Code .standard 10 := ram[
  tmpReg ← arrBaseReg + midReg;
  tmpReg ← *tmpReg;
  if tmpReg < keyReg then [
    resReg ← oneReg
  ] else [
    resReg ← zeroReg
  ] ]

private def lowerBoundFinish : Code .standard 10 := ram[
  *out ← oneReg;
  tmpReg ← out + oneReg;
  *tmpReg ← loReg ]

/-- Structured 10-register Word-RAM program computing `[I.result]` at `Reg.out`. -/
def lowerBoundCode : Code .standard 10 :=
  .seq lowerBoundSetup
    (.seq (bisectCode loReg hiReg midReg resReg zeroReg oneReg arrayProbeCode)
      lowerBoundFinish)

/-- Uniform `Basis.standard` Word-RAM program for array lower-bound search. -/
def lowerBoundProgram : Program .standard 10 := lowerBoundCode.program out

private structure ArraySearchInv (I : LowerBoundInput) (x : Data 10) : Prop where
  zero_eq : x.regs zeroReg = 0
  one_eq : x.regs oneReg = 1
  base_eq : x.regs arrBaseReg = 2
  key_eq : x.regs keyReg = I.key
  out_eq : x.regs out = 2 + I.arr.length
  arr_holds : Block.HoldsList 2 I.arr x.mem

private theorem ArraySearchInv.set_other {I : LowerBoundInput} {x : Data 10}
    (h : ArraySearchInv I x) (d : Fin 10) (v : ℕ)
    (h0 : zeroReg ≠ d := by decide) (h1 : oneReg ≠ d := by decide)
    (hb : arrBaseReg ≠ d := by decide) (hk : keyReg ≠ d := by decide)
    (ho : out ≠ d := by decide) :
    ArraySearchInv I (x.set d v) :=
  ⟨(Data.set_regs_of_ne h0 v).trans h.zero_eq,
   (Data.set_regs_of_ne h1 v).trans h.one_eq,
   (Data.set_regs_of_ne hb v).trans h.base_eq,
   (Data.set_regs_of_ne hk v).trans h.key_eq,
   (Data.set_regs_of_ne ho v).trans h.out_eq,
   h.arr_holds⟩

private theorem init_lowerBoundEncode (I : LowerBoundInput) :
    let x : Data 10 := Data.init I.encode
    x.mem 0 = I.arr.length + 1 ∧ x.mem 1 = I.key ∧ Block.HoldsList 2 I.arr x.mem := by
  intro x
  have h0 : x.mem 0 = I.arr.length + 1 := Data.init_mem_zero I.encode
  have hall : Block.HoldsList 1 (I.key :: I.arr) x.mem := fun i => by
    have h := Data.init_realizes_append (r := 10) [] (I.key :: I.arr) [] i
    dsimp only [x, LowerBoundInput.encode]
    change (Data.init (I.key :: I.arr) : Data 10).mem (1 + i.val) = (I.key :: I.arr)[i.val]
    simpa only [Block.read, List.length_nil, Nat.zero_add, List.nil_append, List.append_nil,
      List.get_eq_getElem] using h
  obtain ⟨h1, harr_blk⟩ := Block.holdsList_cons_iff.mp hall
  exact ⟨h0, h1, harr_blk⟩

private theorem arrayProbeCode_spec (I : LowerBoundInput) {w : ℕ}
    (hw : Fits w (I.arr.length + 3)) (s : Data 10) (hs : ArraySearchInv I s)
    (hm : s.regs midReg < I.arr.length) :
    ∃ s', ExecWithin w arrayProbeCode s s' 5 ∧
      ArraySearchInv I s' ∧
      s'.regs loReg = s.regs loReg ∧
      s'.regs hiReg = s.regs hiReg ∧
      s'.regs midReg = s.regs midReg ∧
      (0 < s'.regs resReg ↔ I.ltKey (s.regs midReg) = true) := by
  have hmem_m : s.mem (2 + s.regs midReg) = I.arr[s.regs midReg] := hs.arr_holds.get _ hm
  have hf_addr : Fits w (2 + s.regs midReg) := hw.of_le (by omega)
  refine WP.exists_execWithin ?_
  unfold arrayProbeCode
  wram_exec [hs.base_eq, hmem_m, hf_addr, hs.key_eq, hs.one_eq, hs.zero_eq]
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, hs.arr_holds⟩, ?_, ?_, ?_, ?_⟩
    · wram_simp [hs.zero_eq]
    · wram_simp [hs.one_eq]
    · wram_simp [hs.base_eq]
    · wram_simp [hs.key_eq]
    · wram_simp [hs.out_eq]
    · wram_simp
    · wram_simp
    · wram_simp
    · wram_simp [LowerBoundInput.ltKey,
        getElem!_pos I.arr.toArray (s.regs midReg) (by simpa using hm),
        List.getElem_toArray, hc, decide_true]
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, hs.arr_holds⟩, ?_, ?_, ?_, ?_⟩
    · wram_simp [hs.zero_eq]
    · wram_simp [hs.one_eq]
    · wram_simp [hs.base_eq]
    · wram_simp [hs.key_eq]
    · wram_simp [hs.out_eq]
    · wram_simp
    · wram_simp
    · wram_simp
    · wram_simp [LowerBoundInput.ltKey,
        getElem!_pos I.arr.toArray (s.regs midReg) (by simpa using hm),
        List.getElem_toArray, hc, decide_false, Bool.false_eq_true]

/-- `lowerBoundCode` executes within `13 * (Nat.log 2 |I.arr| + 1) + 13` instructions from
`Data.init I.encode` whenever `Fits w (|I.arr| + 3)`, writing `[I.result]` as a length-prefixed
output array at `y.regs Reg.out = 2 + |I.arr|` and preserving `I.arr` at `[2, 2 + |I.arr|)`. -/
theorem lowerBoundCode_exec (I : LowerBoundInput) {w : ℕ} (hw : Fits w (I.arr.length + 3)) :
    ∃ y, ExecWithin w lowerBoundCode (Data.init I.encode) y
        (13 * (Nat.log 2 I.arr.length + 1) + 13) ∧
      outputList y.mem (y.regs out) = [I.result] ∧
      y.regs out = 2 + I.arr.length ∧
      Fits w (y.regs out + 1) ∧
      Block.HoldsList 2 I.arr y.mem := by
  let x : Data 10 := Data.init I.encode
  obtain ⟨hm0, hm1, harr⟩ := init_lowerBoundEncode I
  have hf_1 : Fits w 1 := hw.of_le (by omega)
  have hf_2 : Fits w 2 := hw.of_le (by omega)
  have hf_n : Fits w I.arr.length := hw.of_le (by omega)
  have hf_out : Fits w (2 + I.arr.length) := hw.of_le (by omega)
  have hsetup : ∃ x₁, ExecWithin w lowerBoundSetup x x₁ 8 ∧
      ArraySearchInv I x₁ ∧ x₁.regs loReg = 0 ∧ x₁.regs hiReg = I.arr.length := by
    refine WP.exists_execWithin ?_
    unfold lowerBoundSetup
    wram_exec [x, Data.init_regs, hm0, hm1, hf_1, hf_2, hf_n, hf_out]
    exact ⟨⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp,
      by wram_simp, harr⟩, by wram_simp, by wram_simp⟩
  obtain ⟨x₁, es, hx₁_inv, hx₁_lo, hx₁_hi⟩ := hsetup
  obtain ⟨x₂, ebis, hx₂_inv, hx₂_lo, _⟩ :=
    bisectCode_exec (L := 0) (R := I.arr.length)
      (by decide : [loReg, hiReg, midReg, resReg, zeroReg, oneReg].Nodup)
      I.ltKey
      (fun _ h => h.zero_eq) (fun _ h => h.one_eq)
      (fun _ v h => h.set_other loReg v)
      (fun _ v h => h.set_other hiReg v)
      (fun _ v h => h.set_other midReg v)
      (fun s hs _ hm => arrayProbeCode_spec I hw s hs hm)
      x₁ hx₁_inv (by rw [hx₁_lo]) (by rw [hx₁_hi]) (by rw [hx₁_hi]; exact hf_n)
  rw [hx₁_lo, hx₁_hi] at ebis hx₂_lo
  rw [Nat.sub_zero] at ebis
  change x₂.regs loReg = I.result at hx₂_lo
  have hf_out1 : Fits w (2 + I.arr.length + 1) := hw.of_le (by omega)
  have hfin : ∃ y, ExecWithin w lowerBoundFinish x₂ y 3 ∧
      y.regs out = 2 + I.arr.length ∧
      y.mem (2 + I.arr.length) = 1 ∧
      y.mem (2 + I.arr.length + 1) = I.result ∧
      Block.HoldsList 2 I.arr y.mem := by
    refine WP.exists_execWithin ?_
    unfold lowerBoundFinish
    wram_exec [hx₂_inv.out_eq, hx₂_inv.one_eq, hx₂_lo, hf_out1]
    refine ⟨?_, ?_, ?_, hx₂_inv.arr_holds.frame fun a _ ha2 => ?_⟩
    · wram_simp [hx₂_inv.out_eq]
    · wram_simp
    · wram_simp
    · wram_simp
  obtain ⟨y, efin, hy_out, hy_m0, hy_m1, hy_arr⟩ := hfin
  have hout_list : outputList y.mem (y.regs out) = [I.result] :=
    outputList_eq_iff.mpr ⟨by rw [hy_out, List.length_singleton]; exact hy_m0,
      Block.holdsList_cons_iff.mpr ⟨by rw [hy_out]; exact hy_m1, Block.holdsList_nil _ _⟩⟩
  unfold lowerBoundCode
  refine ⟨y, (es.seq (ebis.seq efin)).mono (by omega),
    hout_list, hy_out, by rw [hy_out]; exact hf_out1, hy_arr⟩

/-- `lowerBoundProgram` computes `[I.result]` in `13 * (Nat.log 2 |I.arr| + 1) + 14` instructions
at every word width `w` with `Fits w (|I.arr| + 3)`. -/
theorem lowerBoundProgram_computesListInTime :
    lowerBoundProgram.ComputesListInTime (fun _ (I : LowerBoundInput) => I.encode)
      (fun I _ => 13 * (Nat.log 2 I.arr.length + 1) + 14)
      (fun I w => Fits w (I.arr.length + 3))
      (fun I => [I.result]) :=
  lowerBoundCode.computesListInTime_program out fun I _ hw _ => by
    obtain ⟨y, hexec, hout, _, hfit, _⟩ := lowerBoundCode_exec I hw
    exact ⟨y, hexec, hout, hfit⟩

end Cslib.Algorithms.WordRAM.BinarySearch
