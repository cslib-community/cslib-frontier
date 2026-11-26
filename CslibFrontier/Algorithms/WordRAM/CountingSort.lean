/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.RecordOps
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import Mathlib.Data.List.Pairwise

/-!
# Stable Linear-Time Counting Sort over Fixed-Stride Records

This module implements and verifies a general stable linear-time counting sort over fixed-stride
record arrays in `Memory.Prog` (`countingSortProg`), together with the pure list model
`countingSortPure`.

Given `count` contiguous records of width `stride` starting at `inBase` whose keys at word offset
`keyOff < stride` lie in `[0, numKeys)`, `countingSortProg`:

1. Allocates a zero-initialized count array `cnt` of length `numKeys` via `Memory.allocBlock`.
2. Allocates a dirty output record array `out` of length `stride * count` via
   `Memory.allocBlockDirty`.
3. Counts bucket sizes in `cnt`, computes exclusive prefix offsets via `ArrayOps.prefixSumProg`,
   and scatters each input record to its bucket offset using `Memory.copy`.

## Main definitions

* `countingSortPure`: pure stable bucket-filter model over keys `0 .. numKeys - 1`.
* `CountingSortArgs`, `countingSortArgsWords`: explicit 5-word arguments and encoding.
* `countingSortProg`: 3-pass `Memory.Prog Block` returning the freshly allocated sorted block.

## Main results

* `countingSortPure_perm`, `countingSortPure_pairwise_key`, `countingSortPure_stable`:
  permutation, key monotonicity, and equal-key stability of `countingSortPure`.
* `countingSortProg_spec`: `Memory.FramedTriple` with `S = ∅` (all pre-existing memory preserved),
  exact linear memory cost `2 * (stride * rows.length) + 6 * rows.length + 3 * numKeys + 2`,
  `Memory.WellFormed`, and `HoldsRecords stride out.base (countingSortPure ...)`.
* `realizes_countingSortProg`: `Realizes .exact` certificate with `work = 0`.
-/

public section

namespace Cslib.Algorithms.WordRAM

open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization

/-! ## Pure model and stability properties -/

/-- Pure reference model of stable counting sort by `keyOf : α → ℕ` over keys `0 .. numKeys - 1`. -/
@[expose] def countingSortPure {α : Type*} (numKeys : ℕ) (keyOf : α → ℕ) (xs : List α) :
    List α :=
  (List.range numKeys).flatMap fun k => xs.filter (fun x => decide (keyOf x = k))

/-- When all keys lie below `numKeys`, `countingSortPure` permutes `xs`. -/
theorem countingSortPure_perm {α : Type*} (numKeys : ℕ) (keyOf : α → ℕ) (xs : List α)
    (hbound : ∀ x ∈ xs, keyOf x < numKeys) :
    (countingSortPure numKeys keyOf xs).Perm xs := by
  have hpref : ∀ b ≤ numKeys,
      ((List.range b).flatMap fun k => xs.filter (fun x => decide (keyOf x = k))).Perm
        (xs.filter fun x => decide (keyOf x < b)) := by
    intro b hb
    induction b with
    | zero => simp
    | succ b ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      refine (List.Perm.append_right _ (ih (Nat.le_of_succ_le hb))).trans ?_
      have hlt : xs.filter (fun x => decide (keyOf x < b)) =
          (xs.filter (fun x => decide (keyOf x < b + 1))).filter
            (fun x => decide (keyOf x < b)) := by
        rw [List.filter_filter]
        refine List.filter_congr fun x _ => ?_
        by_cases h1 : keyOf x < b
        · simp [h1, Nat.lt_succ_of_lt h1]
        · simp [h1]
      have heq : xs.filter (fun x => decide (keyOf x = b)) =
          (xs.filter (fun x => decide (keyOf x < b + 1))).filter
            (fun x => !decide (keyOf x < b)) := by
        rw [List.filter_filter]
        refine List.filter_congr fun x _ => ?_
        by_cases h1 : keyOf x = b
        · simp [h1]
        · by_cases h2 : keyOf x < b + 1
          · have h3 : keyOf x < b := by omega
            simp [h1, h2, h3]
          · simp [h1, h2]
      rw [hlt, heq]
      exact List.filter_append_perm _ _
  simpa [countingSortPure, List.filter_eq_self.mpr fun x hx => decide_eq_true (hbound x hx)] using
    hpref numKeys le_rfl

/-- Stability: `countingSortPure` preserves any pairwise relation `R` within equal-key buckets. -/
theorem countingSortPure_stable {α : Type*} (numKeys : ℕ) (keyOf : α → ℕ)
    {R : α → α → Prop} {xs : List α} (hR : xs.Pairwise R) :
    (countingSortPure numKeys keyOf xs).Pairwise
      (fun x y => keyOf x < keyOf y ∨ (keyOf x = keyOf y ∧ R x y)) := by
  rw [countingSortPure, List.pairwise_flatMap]
  refine ⟨fun k _ => ?_, ?_⟩
  · refine List.Pairwise.imp_of_mem (fun {x y} hx hy hr => ?_) (hR.filter _)
    rw [List.mem_filter, decide_eq_true_eq] at hx hy
    exact Or.inr ⟨hx.2.trans hy.2.symm, hr⟩
  · refine List.Pairwise.imp (fun {k₁ k₂} hk x hx y hy => ?_) List.pairwise_lt_range
    rw [List.mem_filter, decide_eq_true_eq] at hx hy
    exact Or.inl (by omega)

/-- `countingSortPure` produces elements ordered monotonically by `keyOf`. -/
theorem countingSortPure_pairwise_key {α : Type*} (numKeys : ℕ) (keyOf : α → ℕ)
    (xs : List α) :
    (countingSortPure numKeys keyOf xs).Pairwise (fun x y => keyOf x ≤ keyOf y) := by
  refine List.Pairwise.imp ?_ (countingSortPure_stable numKeys keyOf (R := fun _ _ => True)
    (List.pairwise_iff_getElem.mpr fun _ _ _ _ _ => trivial))
  rintro x y (h | ⟨h, _⟩) <;> omega

/-! ## Arguments and `Memory.Prog` implementation -/

/-- Input parameters for stable linear-time counting sort over fixed-stride records. -/
structure CountingSortArgs where
  /-- Exclusive upper bound on record keys (`0 ≤ key < numKeys`). -/
  numKeys : ℕ
  /-- Number of records in the input array. -/
  count : ℕ
  /-- Number of machine words per record (`keyOff < stride`). -/
  stride : ℕ
  /-- Zero-based word offset of the sort key inside each record. -/
  keyOff : ℕ
  /-- Base address of the contiguous input record array. -/
  inBase : ℕ

/-- Explicit 5-word encoding of `CountingSortArgs`. -/
word_enc_structure countingSortArgsWords : CountingSortArgs where
  numKeys : wordWords,
  count : wordWords,
  stride : wordWords,
  keyOff : wordWords,
  inBase : wordWords

private def csortCountStep (p : (ℕ × ℕ × ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let inBase := p.1.1
  let stride := p.1.2.1
  let keyOff := p.1.2.2.1
  let cntBase := p.1.2.2.2
  let i := p.2
  let k ← Memory.read (inBase + stride * i + keyOff)
  let c ← Memory.read (cntBase + k)
  Memory.write (cntBase + k) (c + 1)
  pure (i + 1)

private def csortCountStepSafe (w : ℕ) (p : (ℕ × ℕ × ℕ × ℕ) × ℕ) (s : Memory.State) : Prop :=
  let inBase := p.1.1
  let stride := p.1.2.1
  let keyOff := p.1.2.2.1
  let cntBase := p.1.2.2.2
  let i := p.2
  let k := s.mem (inBase + stride * i + keyOff)
  inBase + stride * i + keyOff < s.frontier ∧
  cntBase + k < s.frontier ∧
  Fits w (s.mem (cntBase + k) + 1) ∧
  Fits w (i + 1)

private theorem realizes_csortCountStep :
    Realizes .exact csortCountStep WordEncoding.encode WordEncoding.encode
      csortCountStepSafe (fun _ _ => 0) := by
  have hraw : Realizes .exact
      (fun d : (ℕ × ℕ × ℕ × ℕ) × ℕ => do
        let k ← Memory.read (d.1.1 + d.1.2.1 * d.2 + d.1.2.2.1)
        let c ← Memory.read (d.1.2.2.2 + k)
        Memory.write (d.1.2.2.2 + k) (c + 1)
        pure (d.2 + 1))
      WordEncoding.encode WordEncoding.encode csortCountStepSafe (fun _ _ => 0) := by
    realize
    all_goals
      obtain ⟨h1, h2, h3, h4⟩ := h
      have hfront := hmem.frontier_fits
      first
      | exact h3
      | exact h4
      | exact hfront.of_le (by omega)
  exact hraw.congr fun _ => rfl

private def csortScatterStep (p : (ℕ × ℕ × ℕ × ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let inBase := p.1.1
  let stride := p.1.2.1
  let keyOff := p.1.2.2.1
  let cntBase := p.1.2.2.2.1
  let outBase := p.1.2.2.2.2
  let i := p.2
  let k ← Memory.read (inBase + stride * i + keyOff)
  let pos ← Memory.read (cntBase + k)
  Memory.write (cntBase + k) (pos + 1)
  Memory.copy (inBase + stride * i) (outBase + stride * pos) stride
  pure (i + 1)

private def csortScatterStepSafe (w : ℕ) (p : (ℕ × ℕ × ℕ × ℕ × ℕ) × ℕ)
    (s : Memory.State) : Prop :=
  let inBase := p.1.1
  let stride := p.1.2.1
  let keyOff := p.1.2.2.1
  let cntBase := p.1.2.2.2.1
  let outBase := p.1.2.2.2.2
  let i := p.2
  let k := s.mem (inBase + stride * i + keyOff)
  let pos := s.mem (cntBase + k)
  inBase + stride * i + stride ≤ s.frontier ∧
  keyOff < stride ∧
  cntBase + k < s.frontier ∧
  Fits w (pos + 1) ∧
  outBase + stride * pos + stride ≤ s.frontier ∧
  Fits w (i + 1)

private theorem realizes_csortScatterStep :
    Realizes .exact csortScatterStep WordEncoding.encode WordEncoding.encode
      csortScatterStepSafe (fun _ _ => 0) := by
  have hraw : Realizes .exact
      (fun d : (ℕ × ℕ × ℕ × ℕ × ℕ) × ℕ => do
        let k ← Memory.read (d.1.1 + d.1.2.1 * d.2 + d.1.2.2.1)
        let pos ← Memory.read (d.1.2.2.2.1 + k)
        Memory.write (d.1.2.2.2.1 + k) (pos + 1)
        Memory.copy (d.1.1 + d.1.2.1 * d.2) (d.1.2.2.2.2 + d.1.2.1 * pos) d.1.2.1
        pure (d.2 + 1))
      WordEncoding.encode WordEncoding.encode csortScatterStepSafe (fun _ _ => 0) := by
    realize [realizes_copy]
    all_goals
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      have hfront := hmem.frontier_fits
      first
      | exact h4
      | exact h6
      | exact hfront.of_le (by omega)
      | omega
  exact hraw.congr fun _ => rfl

/-- Sort `a.count` contiguous fixed-stride records at `a.inBase` (each of width `a.stride`, with
sort key `< a.numKeys` at word offset `a.keyOff`) stably into a freshly allocated block using
three linear passes: histogram count, `ArrayOps.prefixSumProg`, and `Memory.copy` scatter. -/
def countingSortProg (a : CountingSortArgs) : Memory.Prog Block := do
  let cnt ← Memory.allocBlock a.numKeys
  let out ← Memory.allocBlockDirty (a.stride * a.count)
  let _ ← iterate csortCountStep (a.inBase, a.stride, a.keyOff, cnt.base) a.count 0
  let _ ← prefixSumProg cnt.base a.numKeys
  let _ ← iterate csortScatterStep (a.inBase, a.stride, a.keyOff, cnt.base, out.base) a.count 0
  pure out

/-! ## Multi-pass verification -/

private theorem sum_filter_eq_length {α : Type*} (keyOf : α → ℕ) :
    ∀ (numKeys : ℕ) (xs : List α), (∀ x ∈ xs, keyOf x < numKeys) →
      ∑ v ∈ Finset.range numKeys, (xs.filter fun x => decide (keyOf x = v)).length =
        xs.length := by
  intro numKeys xs hbound
  induction xs with
  | nil => simp
  | cons a rest ih =>
    have ha : keyOf a < numKeys := hbound a List.mem_cons_self
    have hrest := ih fun x hx => hbound x (List.mem_cons_of_mem a hx)
    have hsplit : ∑ v ∈ Finset.range numKeys,
        ((a :: rest).filter fun x => decide (keyOf x = v)).length =
        (∑ v ∈ Finset.range numKeys, (rest.filter fun x => decide (keyOf x = v)).length) +
        ∑ v ∈ Finset.range numKeys, if v = keyOf a then 1 else 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases h : v = keyOf a <;> simp [eq_comm, h, Nat.add_comm]
    rw [hsplit, hrest, Finset.sum_ite_eq']
    simp only [Finset.mem_range, ha, ↓reduceIte, List.length_cons]

private theorem countingSort_pass1 {w numKeys stride keyOff inBase cntBase : ℕ}
    {rows : List (Fin stride → ℕ)} {s₀ : Memory.State}
    (hwf₀ : Memory.WellFormed w s₀)
    (hin₀ : inBase + stride * rows.length ≤ s₀.frontier)
    (hcnt₀ : cntBase + numKeys ≤ s₀.frontier)
    (hdisj : inBase + stride * rows.length ≤ cntBase)
    (hxs₀ : HoldsRecords stride inBase rows s₀.mem)
    (hzero₀ : ∀ v < numKeys, s₀.mem (cntBase + v) = 0)
    (hkey : keyOff < stride)
    (hbound : ∀ r ∈ rows, r ⟨keyOff, hkey⟩ < numKeys)
    (hfit_cnt : Fits w rows.length) :
    let keyOf : (Fin stride → ℕ) → ℕ := fun r => r ⟨keyOff, hkey⟩
    let prog := iterate csortCountStep (inBase, stride, keyOff, cntBase) rows.length 0
    iterationSafe csortCountStep csortCountStepSafe w (inBase, stride, keyOff, cntBase)
      rows.length 0 s₀ ∧
    Memory.FramedTriple w s₀ prog (3 * rows.length) (Set.Ico cntBase (cntBase + numKeys))
      fun _ s₁ =>
        s₁.frontier = s₀.frontier ∧
        Memory.WellFormed w s₁ ∧
        ∀ v < numKeys, s₁.mem (cntBase + v) =
          (rows.filter fun r => decide (keyOf r = v)).length := by
  intro keyOf
  let S₁ : Set ℕ := Set.Ico cntBase (cntBase + numKeys)
  let bucketLen (k v : ℕ) : ℕ :=
    ((rows.take k).filter fun r => decide (keyOf r = v)).length
  have hle_filter : ∀ k v, bucketLen k v ≤ (rows.filter fun r => decide (keyOf r = v)).length :=
    fun k v => List.Sublist.length_le ((List.take_sublist k rows).filter _)
  let inv₁ (k a : ℕ) (t : Memory.State) : Prop :=
    k ≤ rows.length ∧
    a = k ∧
    t.frontier = s₀.frontier ∧
    Memory.WellFormed w t ∧
    (∀ x, x ∉ S₁ → t.mem x = s₀.mem x) ∧
    ∀ v < numKeys, t.mem (cntBase + v) = bucketLen k v
  have hstep₁ : ∀ k < rows.length, ∀ a t, inv₁ k a t →
      csortCountStepSafe w ((inBase, stride, keyOff, cntBase), a) t ∧
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t
        (csortCountStep ((inBase, stride, keyOff, cntBase), a))) ∧
      let a' := (Memory.spec 0).clientResult t
        (csortCountStep ((inBase, stride, keyOff, cntBase), a))
      let t' := (Memory.spec 0).clientState t
        (csortCountStep ((inBase, stride, keyOff, cntBase), a))
      memoryCost (csortCountStep ((inBase, stride, keyOff, cntBase), a)) t + 0 ≤ 0 + 3 ∧
      Memory.Modifies S₁ t t' ∧
      inv₁ (k + 1) a' t' := by
    intro k hk a t ⟨hk_le, ha, htfr, hwt, hframe, hcnt⟩
    subst a
    have hidx_lt : stride * k + keyOff < stride * rows.length := by
      have hmul : stride * (k + 1) ≤ stride * rows.length := Nat.mul_le_mul_left stride hk
      rw [Nat.mul_add, Nat.mul_one] at hmul
      omega
    have hin_mem : t.mem (inBase + stride * k + keyOff) = keyOf rows[k] := by
      rw [hframe (inBase + stride * k + keyOff)
        (by intro h; simp only [S₁, Set.mem_Ico] at h; omega)]
      exact hxs₀ k hk ⟨keyOff, hkey⟩
    let kv := keyOf rows[k]
    have hkv_lt : kv < numKeys := hbound rows[k] (List.getElem_mem hk)
    have htake : rows.take (k + 1) = rows.take k ++ [rows[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
    have hbl_succ : ∀ v, bucketLen (k + 1) v = bucketLen k v + if kv = v then 1 else 0 := by
      intro v
      dsimp only [bucketLen]
      rw [htake, List.filter_append, List.length_append]
      by_cases h : kv = v <;> simp [kv, h]
    have hcnt_kv : t.mem (cntBase + kv) = bucketLen k kv := hcnt kv hkv_lt
    have hfit_next : Fits w (t.mem (cntBase + kv) + 1) := by
      have hle : bucketLen k kv + 1 ≤ bucketLen (k + 1) kv := by
        have hs := hbl_succ kv
        simp only [↓reduceIte] at hs
        omega
      have hlen : bucketLen (k + 1) kv ≤ rows.length :=
        (hle_filter (k + 1) kv).trans (List.length_filter_le _ _)
      exact hfit_cnt.of_le (by rw [hcnt_kv]; omega)
    have hsafe : csortCountStepSafe w ((inBase, stride, keyOff, cntBase), k) t := by
      dsimp only [csortCountStepSafe]
      rw [hin_mem]
      exact ⟨by rw [htfr]; omega, by rw [htfr]; omega, hfit_next, hfit_cnt.of_le hk⟩
    have hft : Memory.FramedTriple w t
        (csortCountStep ((inBase, stride, keyOff, cntBase), k)) 3 S₁
        fun res t' => res = k + 1 ∧ t'.frontier = t.frontier ∧
          t'.mem = Function.update t.mem (cntBase + kv) (t.mem (cntBase + kv) + 1) := by
      dsimp only [csortCountStep]
      refine Memory.FramedTriple.read_bind (by rw [htfr]; omega) ?_
      rw [hin_mem]
      refine Memory.FramedTriple.read_bind (by rw [htfr]; omega) ?_
      refine Memory.FramedTriple.write_bind_of_mem (by rw [htfr]; omega) hfit_next
        ⟨Nat.le_add_right _ _, by omega⟩ ?_
      exact Memory.FramedTriple.pure ⟨rfl, rfl, rfl⟩
    have hft_wf := hft.wellFormed hwt
    rw [framedTriple_iff_realization] at hft_wf
    obtain ⟨hvh, hcost, hmod, ⟨hres, htfr', hmem'⟩, hwt'⟩ := hft_wf
    refine ⟨hsafe, hvh, by omega, hmod, hk, hres, htfr'.trans htfr, hwt', ?_, ?_⟩
    · intro x hx
      rw [hmem', Function.update_of_ne]
      · exact hframe x hx
      · intro he
        apply hx
        subst he
        exact ⟨Nat.le_add_right _ _, by omega⟩
    · intro v hv
      rw [hmem', hbl_succ v]
      by_cases hkv : kv = v
      · rw [hkv, Function.update_self, ← hkv, hcnt_kv]; simp
      · rw [Function.update_of_ne (by omega), hcnt v hv]; simp [hkv]
  obtain ⟨hsafe₁, hv₁, hcost₁, hmod₁, _, _, htfr₁, hwt₁, _, hcnt₁⟩ :=
    iterate_potential_spec csortCountStep csortCountStepSafe w
      (inBase, stride, keyOff, cntBase) 3 rows.length inv₁ (fun _ _ _ => 0) S₁
      hstep₁ 0 s₀
      ⟨Nat.zero_le _, rfl, rfl, hwf₀, fun _ _ => rfl, fun v hv => by
        simp only [bucketLen, List.take_zero, List.filter_nil, List.length_nil]
        exact hzero₀ v hv⟩
  refine ⟨hsafe₁, framedTriple_iff_realization.mpr ⟨hv₁, by simpa using hcost₁, hmod₁,
    htfr₁, hwt₁, fun v hv => ?_⟩⟩
  simpa only [bucketLen, List.take_of_length_le le_rfl] using hcnt₁ v hv

private theorem countingSort_pass3 {w numKeys stride keyOff inBase cntBase outBase : ℕ}
    {rows : List (Fin stride → ℕ)} {s₂ : Memory.State}
    (hwf₂ : Memory.WellFormed w s₂)
    (hxs₂ : HoldsRecords stride inBase rows s₂.mem)
    (hin_lt : inBase + stride * rows.length ≤ cntBase)
    (hcnt_lt : cntBase + numKeys ≤ outBase)
    (hout_lt : outBase + stride * rows.length ≤ s₂.frontier)
    (hkey : keyOff < stride)
    (hbound : ∀ r ∈ rows, r ⟨keyOff, hkey⟩ < numKeys)
    (hcnt₂ : ∀ v < numKeys, s₂.mem (cntBase + v) =
      ∑ u ∈ Finset.range v, (rows.filter fun r => decide (r ⟨keyOff, hkey⟩ = u)).length)
    (hfit_cnt : Fits w rows.length) :
    let keyOf : (Fin stride → ℕ) → ℕ := fun r => r ⟨keyOff, hkey⟩
    let prog := iterate csortScatterStep (inBase, stride, keyOff, cntBase, outBase) rows.length 0
    iterationSafe csortScatterStep csortScatterStepSafe w
      (inBase, stride, keyOff, cntBase, outBase) rows.length 0 s₂ ∧
    Memory.FramedTriple w s₂ prog ((2 * stride + 3) * rows.length)
      (Set.Ico cntBase (outBase + stride * rows.length))
      fun _ s₃ =>
        s₃.frontier = s₂.frontier ∧
        Memory.WellFormed w s₃ ∧
        HoldsRecords stride outBase (countingSortPure numKeys keyOf rows) s₃.mem := by
  intro keyOf
  let k := rows.length
  let S₃ : Set ℕ := Set.Ico cntBase (outBase + stride * k)
  let bucketSize (v : ℕ) : ℕ := (rows.filter fun r => decide (keyOf r = v)).length
  let bucketOff (v : ℕ) : ℕ := ∑ u ∈ Finset.range v, bucketSize u
  let bucketLen (i v : ℕ) : ℕ :=
    ((rows.take i).filter fun r => decide (keyOf r = v)).length
  have hbo_zero : bucketOff 0 = 0 := rfl
  have hbo_succ : ∀ v, bucketOff (v + 1) = bucketOff v + bucketSize v :=
    fun v => Finset.sum_range_succ bucketSize v
  have hbo_mono : ∀ {a b : ℕ}, a ≤ b → bucketOff a ≤ bucketOff b := fun hab => by
    induction hab with
    | refl => exact le_rfl
    | @step b' _ ih => rw [hbo_succ]; omega
  have hbo_full : bucketOff numKeys = k := sum_filter_eq_length keyOf numKeys rows hbound
  have bucketLen_le : ∀ i v, bucketLen i v ≤ bucketSize v :=
    fun i v => List.Sublist.length_le ((List.take_sublist i rows).filter _)
  let inv₃ (i a : ℕ) (t : Memory.State) : Prop :=
    i ≤ k ∧ a = i ∧ t.frontier = s₂.frontier ∧ Memory.WellFormed w t ∧
    (∀ x < cntBase, t.mem x = s₂.mem x) ∧
    (∀ v < numKeys, t.mem (cntBase + v) = bucketOff v + bucketLen i v) ∧
    ∀ v < numKeys, ∀ j (hj : j < bucketLen i v),
      let r := ((rows.take i).filter fun r => decide (keyOf r = v))[j]'hj
      ∀ m : Fin stride, t.mem (outBase + stride * (bucketOff v + j) + m.val) = r m
  have hstep₃ : ∀ i < k, ∀ a t, inv₃ i a t →
      csortScatterStepSafe w ((inBase, stride, keyOff, cntBase, outBase), a) t ∧
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t
        (csortScatterStep ((inBase, stride, keyOff, cntBase, outBase), a))) ∧
      let a' := (Memory.spec 0).clientResult t
        (csortScatterStep ((inBase, stride, keyOff, cntBase, outBase), a))
      let t' := (Memory.spec 0).clientState t
        (csortScatterStep ((inBase, stride, keyOff, cntBase, outBase), a))
      memoryCost (csortScatterStep ((inBase, stride, keyOff, cntBase, outBase), a)) t + 0 ≤
        0 + (2 * stride + 3) ∧
      Memory.Modifies S₃ t t' ∧
      inv₃ (i + 1) a' t' := by
    intro i hi a t ⟨hi_le, ha, htfr, hwt, hbelow, hcnt, hslice⟩
    subst a
    have htri : HoldsRecords stride inBase rows t.mem :=
      hxs₂.congr fun x _ hhi => hbelow x (lt_of_lt_of_le hhi hin_lt)
    have hidx_lt : stride * i + keyOff < stride * k := by
      have hmul : stride * (i + 1) ≤ stride * k := Nat.mul_le_mul_left stride hi
      rw [Nat.mul_add, Nat.mul_one] at hmul
      omega
    have hslot_in_le : inBase + stride * i + stride ≤ inBase + stride * k := by
      have hmul : stride * (i + 1) ≤ stride * k := Nat.mul_le_mul_left stride hi
      rw [Nat.mul_add, Nat.mul_one] at hmul
      omega
    have hkey_read : t.mem (inBase + stride * i + keyOff) = keyOf rows[i] :=
      htri i hi ⟨keyOff, hkey⟩
    let kv := keyOf rows[i]
    have hkv_lt : kv < numKeys := hbound rows[i] (List.getElem_mem hi)
    have htake : rows.take (i + 1) = rows.take i ++ [rows[i]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some]
    have hfilt_succ : ∀ v, (rows.take (i + 1)).filter (fun r => decide (keyOf r = v)) =
        (rows.take i).filter (fun r => decide (keyOf r = v)) ++
          if kv = v then [rows[i]] else [] := fun v => by
      rw [htake, List.filter_append]
      by_cases h : kv = v <;> simp [kv, h]
    have hbl_succ : ∀ v, bucketLen (i + 1) v = bucketLen i v + if kv = v then 1 else 0 := by
      intro v
      dsimp only [bucketLen]
      rw [hfilt_succ v, List.length_append]
      by_cases h : kv = v <;> simp [h]
    have hpos_eq : t.mem (cntBase + kv) = bucketOff kv + bucketLen i kv := hcnt kv hkv_lt
    have hbl_lt : bucketLen i kv < bucketSize kv := by
      have hle := bucketLen_le (i + 1) kv
      have hs := hbl_succ kv
      simp only [↓reduceIte] at hs
      omega
    have hpos_lt : t.mem (cntBase + kv) < k := by
      have hm := hbo_mono hkv_lt
      rw [hbo_succ] at hm
      omega
    have hout_slot : outBase + stride * t.mem (cntBase + kv) + stride ≤ outBase + stride * k := by
      have hmul : stride * (t.mem (cntBase + kv) + 1) ≤ stride * k :=
        Nat.mul_le_mul_left stride hpos_lt
      rw [Nat.mul_add, Nat.mul_one] at hmul
      omega
    let pos := t.mem (cntBase + kv)
    have hpos_def : pos = t.mem (cntBase + kv) := rfl
    have hpos_k : pos < rows.length := hpos_lt
    have hout_pos : outBase + stride * pos + stride ≤ outBase + stride * rows.length := hout_slot
    have hsafe : csortScatterStepSafe w ((inBase, stride, keyOff, cntBase, outBase), i) t := by
      dsimp only [csortScatterStepSafe]
      rw [hkey_read, ← hpos_def]
      refine ⟨?_, hkey, ?_, hfit_cnt.of_le hpos_k, ?_,
        hfit_cnt.of_le (by dsimp only [k] at hi; omega)⟩
      · rw [htfr]; dsimp only [k] at hslot_in_le; omega
      · rw [htfr]; omega
      · rw [htfr]; omega
    let tMid : Memory.State := ⟨Function.update t.mem (cntBase + kv) (pos + 1), t.frontier⟩
    have hdisj_copy : (inBase + stride * i) + stride ≤ outBase + stride * pos ∨
        (outBase + stride * pos) + stride ≤ inBase + stride * i :=
      Or.inl (by dsimp only [k] at hslot_in_le; omega)
    have hcopy_sub : Set.Ico (outBase + stride * pos) (outBase + stride * pos + stride) ⊆ S₃ := by
      intro x ⟨hx1, hx2⟩
      exact ⟨by omega, by dsimp only [S₃, k]; omega⟩
    have hft_raw : Memory.FramedTriple w t
        (csortScatterStep ((inBase, stride, keyOff, cntBase, outBase), i))
        (2 * stride + 0 + 1 + 1 + 1) S₃
        fun res t' =>
          res = i + 1 ∧
          t' = ⟨ArrayCopy.copyPrefix tMid.mem (inBase + stride * i)
            (outBase + stride * pos) stride, tMid.frontier⟩ := by
      dsimp only [csortScatterStep]
      refine Memory.FramedTriple.read_bind (by rw [htfr]; dsimp only [k] at hidx_lt; omega) ?_
      rw [hkey_read]
      refine Memory.FramedTriple.read_bind (by rw [htfr]; omega) ?_
      rw [← hpos_def]
      refine Memory.FramedTriple.write_bind_of_mem (by rw [htfr]; omega) (hfit_cnt.of_le hpos_k)
        ⟨Nat.le_add_right _ _, by omega⟩ ?_
      have hmid_wf : Memory.WellFormed w tMid :=
        hwt.step (o := .write (cntBase + kv) (pos + 1))
          ⟨by rw [htfr]; omega, hfit_cnt.of_le hpos_k⟩
      have hcopy := (Memory.FramedTriple.copy (w := w) (s := tMid)
        (Q := fun _ t' => t' = ⟨ArrayCopy.copyPrefix tMid.mem (inBase + stride * i)
          (outBase + stride * pos) stride, tMid.frontier⟩)
        hdisj_copy
        (by dsimp only [tMid]; rw [htfr]; dsimp only [k] at hslot_in_le; omega)
        (by dsimp only [tMid]; rw [htfr]; omega)
        (fun _ _ => hmid_wf.mem_fits _) rfl).frame_mono hcopy_sub
      refine Memory.FramedTriple.bind_same (c₂ := 0)
        (hcopy.mono le_rfl fun _ t' ht' => ?_)
      exact Memory.FramedTriple.pure ⟨rfl, ht'⟩
    have hft : Memory.FramedTriple w t
        (csortScatterStep ((inBase, stride, keyOff, cntBase, outBase), i))
        (2 * stride + 3) S₃
        fun res t' =>
          res = i + 1 ∧
          t' = ⟨ArrayCopy.copyPrefix tMid.mem (inBase + stride * i)
            (outBase + stride * pos) stride, tMid.frontier⟩ :=
      Memory.FramedTriple.mono hft_raw (by omega) fun _ _ h => h
    have hft_wf := hft.wellFormed hwt
    rw [framedTriple_iff_realization] at hft_wf
    obtain ⟨hvh, hcost, hmod, ⟨hres, ht'⟩, hwt'⟩ := hft_wf
    refine ⟨hsafe, hvh, by omega, hmod, hi, hres, by rw [ht']; exact htfr, hwt', ?_, ?_, ?_⟩
    · intro x hx
      rw [hmod.mem_eq_of_not_mem (by rw [htfr]; omega)
        (by intro h; simp only [S₃, Set.mem_Ico] at h; omega)]
      exact hbelow x hx
    · intro v hv
      rw [ht']
      have hnot_copy : cntBase + v ∉
          Set.Ico (outBase + stride * pos) (outBase + stride * pos + stride) := by
        simp only [Set.mem_Ico, not_and, not_lt]
        intro hle; omega
      change ArrayCopy.copyPrefix tMid.mem (inBase + stride * i) (outBase + stride * pos) stride
          (cntBase + v) = bucketOff v + bucketLen (i + 1) v
      rw [ArrayCopy.copyPrefix_outside hnot_copy]
      dsimp only [tMid]
      rw [hbl_succ v]
      by_cases hkv : kv = v
      · rw [hkv, Function.update_self, ← hkv]
        dsimp only [pos]
        rw [hpos_eq]
        simp [Nat.add_assoc]
      · rw [Function.update_of_ne (by omega), hcnt v hv]; simp [hkv]
    · intro v hv j hj r m
      have hj_le : j ≤ bucketLen i v := by
        have hs := hbl_succ v
        by_cases hkv : kv = v <;> simp only [hkv, ↓reduceIte] at hs <;> omega
      by_cases hlast : kv = v ∧ j = bucketLen i v
      · obtain ⟨rfl, hj_eq⟩ := hlast
        have hfilt_kv : (rows.take (i + 1)).filter (fun r => decide (keyOf r = kv)) =
            (rows.take i).filter (fun r => decide (keyOf r = kv)) ++ [rows[i]] := by
          simpa only [↓reduceIte] using hfilt_succ kv
        have hr_eq : r = rows[i] := by
          have h1 : r = ((rows.take i).filter (fun r => decide (keyOf r = kv)) ++
              [rows[i]])[j]'(by rw [← hfilt_kv]; exact hj) := getElem_congr_coll hfilt_kv
          refine h1.trans ?_
          rw [List.getElem_append_right (by dsimp only [bucketLen] at hj_eq; omega)]
          simp [hj_eq, bucketLen]
        rw [hr_eq, ht']
        have hpos_j : pos = bucketOff kv + j := by rw [hj_eq]; exact hpos_eq
        change ArrayCopy.copyPrefix tMid.mem (inBase + stride * i) (outBase + stride * pos) stride
            (outBase + stride * (bucketOff kv + j) + m.val) = rows[i] m
        rw [← hpos_j, ArrayCopy.copyPrefix_read m.isLt]
        dsimp only [tMid]
        rw [Function.update_of_ne (by dsimp only [k] at hslot_in_le; omega)]
        exact htri i hi m
      · have hj_lt : j < bucketLen i v := by
          by_cases hkv : kv = v
          · have : j ≠ bucketLen i v := fun he => hlast ⟨hkv, he⟩
            omega
          · have hs := hbl_succ v
            simp only [hkv, ↓reduceIte, Nat.add_zero] at hs
            omega
        have hr_pref : r = ((rows.take i).filter (fun r => decide (keyOf r = v)))[j]'hj_lt := by
          have h1 : r = ((rows.take i).filter (fun r => decide (keyOf r = v)) ++
              if kv = v then [rows[i]] else [])[j]'(by rw [← hfilt_succ v]; exact hj) :=
            getElem_congr_coll (hfilt_succ v)
          exact h1.trans (List.getElem_append_left hj_lt)
        rw [hr_pref, ht']
        have hne_slot : bucketOff v + j ≠ pos := by
          dsimp only [pos]; rw [hpos_eq]
          rcases Nat.lt_trichotomy v kv with hlt | rfl | hlt
          · have hm := hbo_mono hlt
            rw [hbo_succ] at hm
            have := bucketLen_le i v
            omega
          · omega
          · have hm := hbo_mono hlt
            rw [hbo_succ] at hm
            omega
        have hslot_alloc : (Block.slot outBase stride (bucketOff v + j)).Allocated tMid := by
          have hidx_k : bucketOff v + j < k := by
            have hm := hbo_mono hv
            rw [hbo_succ] at hm
            have := bucketLen_le i v
            omega
          exact Block.slot_allocated_of_lt (by dsimp only [tMid]; rw [htfr]; exact hout_lt) hidx_k
        have hmod_copy : Memory.Modifies
            (Set.Ico (Block.slot outBase stride pos).base
              ((Block.slot outBase stride pos).base + stride))
            tMid
            ⟨ArrayCopy.copyPrefix tMid.mem (inBase + stride * i) (outBase + stride * pos) stride,
              tMid.frontier⟩ := by
          refine ⟨le_rfl, fun x _ hx => ?_⟩
          exact ArrayCopy.copyPrefix_outside hx
        have hkeep := Block.slot_mem_eq_of_modifies_other hslot_alloc hne_slot hmod_copy
          (outBase + stride * (bucketOff v + j) + m.val)
          (Block.owns_add m.isLt)
        dsimp only at hkeep ⊢
        rw [hkeep]
        dsimp only [tMid]
        rw [Function.update_of_ne (by omega)]
        exact hslice v hv j hj_lt m
  obtain ⟨hsafe₃, hv₃, hcost₃, hmod₃, _, _, htfr₃, hwt₃, _, _, hslice₃⟩ :=
    iterate_potential_spec csortScatterStep csortScatterStepSafe w
      (inBase, stride, keyOff, cntBase, outBase) (2 * stride + 3) k inv₃ (fun _ _ _ => 0) S₃
      hstep₃ 0 s₂
      ⟨Nat.zero_le k, rfl, rfl, hwf₂, fun _ _ => rfl,
        fun v hv => by
          simp only [bucketLen, List.take_zero, List.filter_nil, List.length_nil, Nat.add_zero]
          exact hcnt₂ v hv,
        fun v hv j hj => by simp [bucketLen] at hj⟩
  refine ⟨hsafe₃, framedTriple_iff_realization.mpr ⟨hv₃, by simpa using hcost₃, hmod₃,
    htfr₃, hwt₃, ?_⟩⟩
  have hpref_flat : ∀ b ≤ numKeys,
      let pref := (List.range b).flatMap fun v => rows.filter (fun r => decide (keyOf r = v))
      pref.length = bucketOff b ∧
      ∀ idx (hidx : idx < pref.length) (m : Fin stride),
        ((Memory.spec 0).clientState s₂
          (iterate csortScatterStep (inBase, stride, keyOff, cntBase, outBase) k 0)).mem
            (outBase + stride * idx + m.val) = pref[idx] m := by
    intro b hb
    induction b with
    | zero => exact ⟨hbo_zero.symm, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ b ih =>
      obtain ⟨hlen_ih, hmem_ih⟩ := ih (Nat.le_of_succ_le hb)
      let prefB := (List.range b).flatMap fun v => rows.filter (fun r => decide (keyOf r = v))
      let buckB := rows.filter fun r => decide (keyOf r = b)
      have hflat : (List.range (b + 1)).flatMap
          (fun v => rows.filter fun r => decide (keyOf r = v)) = prefB ++ buckB := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      have hlen_succ : (prefB ++ buckB).length = bucketOff (b + 1) := by
        rw [List.length_append, hlen_ih, hbo_succ]
      refine ⟨by rw [hflat]; exact hlen_succ, fun idx hidx m => ?_⟩
      have hidx' : idx < (prefB ++ buckB).length := by rw [← hflat]; exact hidx
      have hrow_congr : ((List.range (b + 1)).flatMap
          (fun v => rows.filter fun r => decide (keyOf r = v)))[idx]'hidx =
          (prefB ++ buckB)[idx]'hidx' := getElem_congr_coll hflat
      rw [hrow_congr]
      by_cases hlt : idx < prefB.length
      · rw [List.getElem_append_left hlt]
        exact hmem_ih idx hlt m
      · have hj_lt : idx - prefB.length < buckB.length := by
          rw [List.length_append] at hidx'; omega
        have hj_lt' : idx - prefB.length < bucketLen k b := by
          simpa only [bucketLen, k, List.take_of_length_le le_rfl] using hj_lt
        have hslice_b := hslice₃ b hb (idx - prefB.length) hj_lt' m
        have hidx_eq : bucketOff b + (idx - prefB.length) = idx := by
          dsimp only [prefB] at hlen_ih hlt ⊢
          rw [← hlen_ih]
          omega
        have hbuck_eq : buckB[idx - prefB.length]'hj_lt =
            ((rows.take k).filter fun r => decide (keyOf r = b))[idx - prefB.length]'hj_lt' :=
          getElem_congr_coll (by simp [buckB, k, List.take_of_length_le le_rfl])
        rw [List.getElem_append_right (Nat.le_of_not_lt hlt), hbuck_eq]
        rw [hidx_eq] at hslice_b
        exact hslice_b
  exact (hpref_flat numKeys le_rfl).2

private theorem countingSort_pipeline {w numKeys stride keyOff inBase : ℕ}
    {rows : List (Fin stride → ℕ)} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hxs : HoldsRecords stride inBase rows s.mem)
    (hin : inBase + stride * rows.length ≤ s.frontier)
    (hkey : keyOff < stride)
    (hbound : ∀ r ∈ rows, r ⟨keyOff, hkey⟩ < numKeys)
    (hfit : Fits w (s.frontier + numKeys + stride * rows.length)) :
    let keyOf : (Fin stride → ℕ) → ℕ := fun r => r ⟨keyOff, hkey⟩
    let cntBase := s.frontier
    let outBase := cntBase + numKeys
    let fEnd := outBase + stride * rows.length
    let s₀ : Memory.State := ⟨clear s.mem cntBase numKeys, fEnd⟩
    let s₁ := (Memory.spec 0).clientState s₀
      (iterate csortCountStep (inBase, stride, keyOff, cntBase) rows.length 0)
    let s₂ := (Memory.spec 0).clientState s₁ (prefixSumProg cntBase numKeys)
    iterationSafe csortCountStep csortCountStepSafe w (inBase, stride, keyOff, cntBase)
      rows.length 0 s₀ ∧
    cntBase + numKeys ≤ s₁.frontier ∧
    Fits w (∑ i ∈ Finset.range numKeys, s₁.mem (cntBase + i)) ∧
    iterationSafe csortScatterStep csortScatterStepSafe w
      (inBase, stride, keyOff, cntBase, outBase) rows.length 0 s₂ ∧
    Memory.FramedTriple w s (countingSortProg ⟨numKeys, rows.length, stride, keyOff, inBase⟩)
      (2 * (stride * rows.length) + 6 * rows.length + 3 * numKeys + 2)
      ∅
      fun out s' =>
        out = ⟨s.frontier + numKeys, stride * rows.length⟩ ∧
        out.Allocated s' ∧
        s'.frontier = s.frontier + numKeys + stride * rows.length ∧
        Memory.WellFormed w s' ∧
        HoldsRecords stride out.base (countingSortPure numKeys keyOf rows) s'.mem := by
  intro keyOf cntBase outBase fEnd s₀ s₁ s₂
  have hstride_ge : 1 ≤ stride := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hkey)
  have hfit_cnt : Fits w rows.length :=
    hfit.of_le (le_trans (Nat.le_mul_of_pos_left rows.length hstride_ge) (by omega))
  have hfit_num : Fits w numKeys := hfit.of_le (by omega)
  have hfit₁ : Fits w (s.frontier + numKeys) := hfit.of_le (by omega)
  have hwf_a : Memory.WellFormed w ⟨clear s.mem cntBase numKeys, cntBase + numKeys⟩ :=
    hwf.step (o := .alloc numKeys) hfit₁
  have hwf₀ : Memory.WellFormed w s₀ :=
    hwf_a.step (o := .allocDirty (stride * rows.length))
      (by simpa [fEnd, outBase, cntBase] using hfit)
  have hxs₀ : HoldsRecords stride inBase rows s₀.mem :=
    hxs.congr fun x _ hhi =>
      clear_of_not_owns (fun howns => by simp only [Block.Owns, cntBase] at howns; omega)
  have hzero₀ : ∀ v < numKeys, s₀.mem (cntBase + v) = 0 :=
    fun v hv => clear_of_owns (Block.owns_add (b := ⟨cntBase, numKeys⟩) hv)
  obtain ⟨hsafe₁, hft₁⟩ := countingSort_pass1 hwf₀ (by dsimp only [s₀, fEnd, outBase]; omega)
    (by dsimp only [s₀, fEnd, outBase]; omega) hin hxs₀ hzero₀ hkey hbound hfit_cnt
  have hft₁' := hft₁
  rw [framedTriple_iff_realization] at hft₁'
  obtain ⟨hv₁, hcost₁, hmod₁, hs₁_fr, hwf₁, hcnt₁⟩ := hft₁'
  have hsum_eq : ∑ v ∈ Finset.range numKeys, s₁.mem (cntBase + v) = rows.length := by
    rw [Finset.sum_congr rfl fun v hv => hcnt₁ v (Finset.mem_range.mp hv)]
    exact sum_filter_eq_length keyOf numKeys rows hbound
  have hfit_sum : Fits w (∑ v ∈ Finset.range numKeys, s₁.mem (cntBase + v)) := by
    rw [hsum_eq]; exact hfit_cnt
  have hft₂ := prefixSumProg_spec hwf₁ hfit_num
    (by rw [hs₁_fr]; dsimp only [s₀, fEnd, outBase]; omega) hfit_sum
  have hft₂' := hft₂
  rw [framedTriple_iff_realization] at hft₂'
  obtain ⟨hv₂, hcost₂, hmod₂, _, hs₂_fr, hwf₂, hcnt₂⟩ := hft₂'
  have hxs₂ : HoldsRecords stride inBase rows s₂.mem :=
    hxs₀.congr fun x _ hhi =>
      (hmod₂.mem_eq_of_not_mem (by rw [hs₁_fr]; dsimp only [s₀, fEnd, outBase]; omega)
        (by intro h; simp only [Set.mem_Ico] at h; omega)).trans
        (hmod₁.mem_eq_of_not_mem (by dsimp only [s₀, fEnd, outBase]; omega)
          (by intro h; simp only [Set.mem_Ico] at h; omega))
  obtain ⟨hsafe₃, hft₃⟩ := countingSort_pass3 hwf₂ hxs₂ hin le_rfl
    (by rw [hs₂_fr, hs₁_fr]) hkey hbound
    (fun v hv => (hcnt₂ v hv).trans
      (Finset.sum_congr rfl fun u hu => hcnt₁ u (lt_trans (Finset.mem_range.mp hu) hv)))
    hfit_cnt
  refine ⟨hsafe₁, by rw [hs₁_fr]; dsimp only [s₀, fEnd, outBase]; omega, hfit_sum, hsafe₃, ?_⟩
  let S : Set ℕ := Set.Ico cntBase fEnd
  have hsub₁ : Set.Ico cntBase (cntBase + numKeys) ⊆ S := fun x ⟨h1, h2⟩ =>
    ⟨h1, by dsimp only [fEnd, outBase]; omega⟩
  have hft_body : Memory.FramedTriple w s
      (countingSortProg ⟨numKeys, rows.length, stride, keyOff, inBase⟩)
      (2 * (stride * rows.length) + 6 * rows.length + 3 * numKeys + 2) S
      fun out s' =>
        out = ⟨s.frontier + numKeys, stride * rows.length⟩ ∧
        out.Allocated s' ∧
        s'.frontier = s.frontier + numKeys + stride * rows.length ∧
        Memory.WellFormed w s' ∧
        HoldsRecords stride out.base (countingSortPure numKeys keyOf rows) s'.mem := by
    have hft_inner : Memory.FramedTriple w s
        (countingSortProg ⟨numKeys, rows.length, stride, keyOff, inBase⟩)
        ((3 * rows.length + (2 * numKeys + ((2 * stride + 3) * rows.length + 0))) + 1 +
          (numKeys + 1))
        S
        fun out s' =>
          out = ⟨s.frontier + numKeys, stride * rows.length⟩ ∧
          out.Allocated s' ∧
          s'.frontier = s.frontier + numKeys + stride * rows.length ∧
          Memory.WellFormed w s' ∧
          HoldsRecords stride out.base (countingSortPure numKeys keyOf rows) s'.mem := by
      dsimp only [countingSortProg]
      refine Memory.FramedTriple.allocBlock_bind hfit₁ ?_
      refine Memory.FramedTriple.allocBlockDirty_bind
        (by change Fits w (cntBase + numKeys + stride * rows.length)
            simpa [Nat.add_assoc] using hfit) ?_
      have hbody₁ : Memory.FramedTriple w s₀
          (iterate csortCountStep (inBase, stride, keyOff, cntBase) rows.length 0)
          (3 * rows.length) S fun _ t => t = s₁ :=
        framedTriple_iff_realization.mpr ⟨hv₁, hcost₁, hmod₁.mono hsub₁, rfl⟩
      have hbody₂ : Memory.FramedTriple w s₁
          (prefixSumProg cntBase numKeys) (2 * numKeys) S fun _ t => t = s₂ :=
        framedTriple_iff_realization.mpr ⟨hv₂, hcost₂, hmod₂.mono hsub₁, rfl⟩
      have hbody₃ := hft₃.frame_mono (fun x
          (hx : x ∈ Set.Ico cntBase (outBase + stride * rows.length)) => (hx : x ∈ S))
      refine Memory.FramedTriple.bind_same (hbody₁.mono le_rfl fun _ t₁ ht₁ => ?_)
      subst ht₁
      refine Memory.FramedTriple.bind_same (hbody₂.mono le_rfl fun _ t₂ ht₂ => ?_)
      subst ht₂
      refine Memory.FramedTriple.bind_same
        (hbody₃.mono le_rfl fun _ t₃ ⟨ht₃_fr, hwt₃, hrows₃⟩ => ?_)
      have ht₃_end : t₃.frontier = fEnd := by rw [ht₃_fr, hs₂_fr, hs₁_fr]
      refine Memory.FramedTriple.pure ⟨rfl, ?_, ?_, hwt₃, hrows₃⟩
      · change outBase + stride * rows.length ≤ t₃.frontier
        rw [ht₃_end]
      · rw [ht₃_end]
    exact Memory.FramedTriple.mono hft_inner (by rw [Nat.add_mul, Nat.mul_assoc]; omega)
      fun _ _ h => h
  exact hft_body.frame_empty_of_ge_frontier fun _ ha => ha.1

/-- Framed specification for `countingSortProg`: stably sorts `rows` by key field `keyOff`
into a freshly allocated block `out = ⟨s.frontier + numKeys, stride * rows.length⟩`, preserves all
cells below `s.frontier` (`S = ∅`), preserves `WellFormed`, and costs at most
`2 * (stride * rows.length) + 6 * rows.length + 3 * numKeys + 2`. -/
theorem countingSortProg_spec {w numKeys stride keyOff inBase : ℕ}
    {rows : List (Fin stride → ℕ)} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hxs : HoldsRecords stride inBase rows s.mem)
    (hin : inBase + stride * rows.length ≤ s.frontier)
    (hkey : keyOff < stride)
    (hbound : ∀ r ∈ rows, r ⟨keyOff, hkey⟩ < numKeys)
    (hfit : Fits w (s.frontier + numKeys + stride * rows.length)) :
    Memory.FramedTriple w s
      (countingSortProg ⟨numKeys, rows.length, stride, keyOff, inBase⟩)
      (2 * (stride * rows.length) + 6 * rows.length + 3 * numKeys + 2)
      ∅
      fun out s' =>
        out = ⟨s.frontier + numKeys, stride * rows.length⟩ ∧
        out.Allocated s' ∧
        s'.frontier = s.frontier + numKeys + stride * rows.length ∧
        Memory.WellFormed w s' ∧
        HoldsRecords stride out.base
          (countingSortPure numKeys (fun r => r ⟨keyOff, hkey⟩) rows) s'.mem :=
  (countingSort_pipeline hwf hxs hin hkey hbound hfit).2.2.2.2

/-- Uniform `Realizes .exact` certificate for `countingSortProg` with `work = 0`. -/
theorem realizes_countingSortProg :
    Realizes .exact countingSortProg countingSortArgsWords WordEncoding.encode
      (fun w a s =>
        a.keyOff < a.stride ∧
        a.inBase + a.stride * a.count ≤ s.frontier ∧
        Fits w (s.frontier + a.numKeys + a.stride * a.count) ∧
        ∀ i < a.count, s.mem (a.inBase + a.stride * i + a.keyOff) < a.numKeys)
      (fun _ _ => 0) := by
  unfold countingSortProg
  realize [realizes_allocBlock, realizes_allocBlockDirty, realizes_csortCountStep,
    realizes_prefixSumProg, realizes_csortScatterStep]
  all_goals
    obtain ⟨hkey, hin, hfit, hbound_idx⟩ := h
    let rows : List (Fin d.stride → ℕ) :=
      List.ofFn fun i : Fin d.count => fun j : Fin d.stride =>
        s.mem (d.inBase + d.stride * i.val + j.val)
    have hlen : rows.length = d.count := List.length_ofFn
    have hxs : HoldsRecords d.stride d.inBase rows s.mem := by
      intro i hi j
      simp [rows]
    have hbound : ∀ r ∈ rows, r ⟨d.keyOff, hkey⟩ < d.numKeys := by
      intro r hr
      rw [List.mem_ofFn] at hr
      obtain ⟨i, rfl⟩ := hr
      exact hbound_idx i.val i.isLt
    obtain ⟨hsafe₁, hcnt_fr, hfit_sum, hsafe₃, _⟩ :=
      countingSort_pipeline hmem hxs (by simpa [hlen] using hin) hkey hbound
        (by simpa [hlen] using hfit)
    have hres_cnt : ((Memory.spec 0).clientResult s (Memory.allocBlock d.numKeys)).base =
        s.frontier := rfl
    have hst_cnt : (Memory.spec 0).clientState s (Memory.allocBlock d.numKeys) =
        ⟨clear s.mem s.frontier d.numKeys, s.frontier + d.numKeys⟩ := rfl
    simp only [hres_cnt, hst_cnt, ← hlen] at *
    first
    | exact hfit.of_le (by omega)
    | exact hcnt_fr
    | exact hfit_sum
    | exact iterationSafe_imp hsafe₁ (fun _ => rfl) (fun _ _ hp => hp)
    | exact iterationSafe_imp hsafe₃ (fun _ => rfl) (fun _ _ hp => hp)

end Cslib.Algorithms.WordRAM
