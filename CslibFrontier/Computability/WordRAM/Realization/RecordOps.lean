/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.ArrayOps
import CslibFrontier.Tactic.Realize

/-!
# Fixed-stride record arrays and three-way concatenation

This module provides:

1. `HoldsRecords`: a fixed-stride record-array representation predicate over raw RAM memory,
   together with framing (`HoldsRecords.congr`, `HoldsRecords.of_modifies_disjoint`), slicing
   (`HoldsRecords.append_iff`), and `Memory.copy`-based record copying (`HoldsRecords.copy`).
2. `FramedTriple.frame_empty_of_ge_frontier`: shrinks a `Memory.FramedTriple`'s modification set
   to `∅` whenever all modified addresses lie at or above `s.frontier`.
3. `concatRecordsProg`: three-way dirty concatenation of fixed-stride record slices.

## Main definitions

* `HoldsRecords`: `rows.length` records of width `stride` stored consecutively at `base`.
* `ConcatRecordsArgs`, `concatRecordsArgsWords`, `concatRecordsProg`: concatenate three
  stride-`stride` record arrays into a freshly allocated dirty block.

## Main results

* `HoldsRecords.of_modifies_disjoint`, `HoldsRecords.append_iff`, `HoldsRecords.copy`:
  framing, concatenation, and copy transport for fixed-stride record arrays.
* `Cslib.DataStructure.Memory.FramedTriple.frame_empty_of_ge_frontier`: frontier-disjoint frame
  reduction to `S = ∅`.
* `concatRecordsProg_spec`, `realizes_concatRecordsProg`: framed specification and
  `Realizes .exact` (`work = 0`) certificate for `concatRecordsProg`.
-/

public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

/-! ## Fixed-stride record arrays (`HoldsRecords`) -/

/-- Memory `mem` stores `rows.length` consecutive fixed-stride records of width `stride`
starting at `base`. -/
@[expose] def HoldsRecords (stride base : ℕ) (rows : List (Fin stride → ℕ)) (mem : ℕ → ℕ) : Prop :=
  ∀ i (hi : i < rows.length) (j : Fin stride), mem (base + stride * i + j.val) = rows[i] j

namespace HoldsRecords

/-- An empty list of records holds trivially at any base and stride. -/
theorem nil (stride base : ℕ) (mem : ℕ → ℕ) : HoldsRecords stride base [] mem :=
  fun _ hi => absurd hi (Nat.not_lt_zero _)

/-- Congruence for `HoldsRecords` over `[base, base + stride * rows.length)`. -/
theorem congr {stride base : ℕ} {rows : List (Fin stride → ℕ)} {m₁ m₂ : ℕ → ℕ}
    (heq : ∀ a, base ≤ a → a < base + stride * rows.length → m₂ a = m₁ a)
    (h : HoldsRecords stride base rows m₁) : HoldsRecords stride base rows m₂ := by
  intro i hi j
  have hlt : stride * i + j.val < stride * rows.length := by
    have hmul : stride * (i + 1) ≤ stride * rows.length := Nat.mul_le_mul_left stride hi
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega
  exact (heq (base + stride * i + j.val) (by omega) (by omega)).trans (h i hi j)

/-- A `HoldsRecords` predicate on an allocated block disjoint from `S` survives
`Memory.Modifies S s s'`. -/
theorem of_modifies_disjoint {stride base : ℕ} {rows : List (Fin stride → ℕ)}
    {S : Set ℕ} {s s' : Memory.State}
    (hb : (Block.mk base (stride * rows.length)).Allocated s)
    (hh : HoldsRecords stride base rows s.mem) (hmod : Memory.Modifies S s s')
    (hdisj : Disjoint S (Set.Ico base (base + stride * rows.length))) :
    HoldsRecords stride base rows s'.mem :=
  hh.congr fun _ hlo hhi =>
    hmod.mem_eq_of_disjoint hdisj (lt_of_lt_of_le hhi hb) ⟨hlo, hhi⟩

/-- Concatenating two consecutive `HoldsRecords` slices into one `rows₁ ++ rows₂` slice. -/
theorem append_iff {stride base : ℕ} {rows₁ rows₂ : List (Fin stride → ℕ)} {mem : ℕ → ℕ} :
    HoldsRecords stride base (rows₁ ++ rows₂) mem ↔
      HoldsRecords stride base rows₁ mem ∧
      HoldsRecords stride (base + stride * rows₁.length) rows₂ mem := by
  constructor
  · intro h
    refine ⟨fun i hi j => ?_, fun k hk j => ?_⟩
    · have hi' : i < (rows₁ ++ rows₂).length := by simp only [List.length_append]; omega
      simpa only [List.getElem_append_left hi] using h i hi' j
    · have hk' : rows₁.length + k < (rows₁ ++ rows₂).length := by
        simp only [List.length_append]; omega
      have hcell := h (rows₁.length + k) hk' j
      have hidx : base + stride * (rows₁.length + k) + j.val =
          base + stride * rows₁.length + stride * k + j.val := by
        simp only [Nat.mul_add, Nat.add_assoc]
      have hget : (rows₁ ++ rows₂)[rows₁.length + k]'hk' = rows₂[k]'hk := by
        rw [List.getElem_append_right (Nat.le_add_right _ _)]
        simp
      rw [hidx, hget] at hcell
      exact hcell
  · rintro ⟨h₁, h₂⟩ i hi j
    by_cases hlt : i < rows₁.length
    · simpa only [List.getElem_append_left hlt] using h₁ i hlt j
    · have hge : rows₁.length ≤ i := Nat.le_of_not_lt hlt
      have hk : i - rows₁.length < rows₂.length := by
        simp only [List.length_append] at hi; omega
      have hcell := h₂ (i - rows₁.length) hk j
      have hidx : base + stride * rows₁.length + stride * (i - rows₁.length) + j.val =
          base + stride * i + j.val := by
        have hmul : stride * rows₁.length + stride * (i - rows₁.length) = stride * i := by
          rw [← Nat.mul_add, Nat.add_sub_cancel' hge]
        omega
      have hget : (rows₁ ++ rows₂)[i]'hi = rows₂[i - rows₁.length]'hk :=
        List.getElem_append_right hge
      rw [hidx] at hcell
      rw [hget]
      exact hcell

/-- Non-overlapping `Memory.copy` transfers `HoldsRecords stride src rows` directly to
`HoldsRecords stride dst rows` under `Memory.FramedTriple`. -/
theorem copy {w stride src dst : ℕ} {rows : List (Fin stride → ℕ)} {s : Memory.State}
    (hdisj : src + stride * rows.length ≤ dst ∨ dst + stride * rows.length ≤ src)
    (hsrc : src + stride * rows.length ≤ s.frontier)
    (hdst : dst + stride * rows.length ≤ s.frontier)
    (hwf : Memory.WellFormed w s) (hrows : HoldsRecords stride src rows s.mem) :
    Memory.FramedTriple w s (Memory.copy src dst (stride * rows.length))
      (2 * (stride * rows.length)) (Set.Ico dst (dst + stride * rows.length))
      fun _ s' =>
        s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        HoldsRecords stride dst rows s'.mem := by
  have hcopy : Memory.FramedTriple w s (Memory.copy src dst (stride * rows.length))
      (2 * (stride * rows.length)) (Set.Ico dst (dst + stride * rows.length))
      fun _ s' => s' = ⟨ArrayCopy.copyPrefix s.mem src dst (stride * rows.length), s.frontier⟩ :=
    Memory.FramedTriple.copy hdisj hsrc hdst (fun _ _ => hwf.mem_fits _) rfl
  refine (hcopy.wellFormed hwf).mono le_rfl fun _ s' ⟨hs', hwf'⟩ => ?_
  subst hs'
  refine ⟨rfl, hwf', fun i hi j => ?_⟩
  have hlt : stride * i + j.val < stride * rows.length := by
    have hmul : stride * (i + 1) ≤ stride * rows.length := Nat.mul_le_mul_left stride hi
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega
  dsimp only
  rw [Nat.add_assoc, ArrayCopy.copyPrefix_read hlt, ← Nat.add_assoc]
  exact hrows i hi j

end HoldsRecords

/-! ## Three-way dirty record concatenation (`concatRecordsProg`) -/

/-- Input arguments for concatenating three stride-`stride` record arrays into a freshly
allocated dirty block. -/
structure ConcatRecordsArgs where
  /-- Fixed record width in words. -/
  stride : ℕ
  /-- Base address of the first slice. -/
  srcA : ℕ
  /-- Number of records in the first slice. -/
  lenA : ℕ
  /-- Base address of the second slice. -/
  srcB : ℕ
  /-- Number of records in the second slice. -/
  lenB : ℕ
  /-- Base address of the third slice. -/
  srcC : ℕ
  /-- Number of records in the third slice. -/
  lenC : ℕ

/-- Explicit 7-word encoding of `ConcatRecordsArgs`. -/
word_enc_structure concatRecordsArgsWords : ConcatRecordsArgs where
  stride : wordWords,
  srcA : wordWords,
  lenA : wordWords,
  srcB : wordWords,
  lenB : wordWords,
  srcC : wordWords,
  lenC : wordWords

/-- Shrink the modification set of a `Memory.FramedTriple` to `∅` when every address in `S` lies
at or above `s.frontier`. -/
theorem _root_.Cslib.DataStructure.Memory.FramedTriple.frame_empty_of_ge_frontier
    {α : Type} {w c : ℕ} {s : Memory.State} {p : Memory.Prog α} {S : Set ℕ}
    {Q : α → Memory.State → Prop}
    (h : Memory.FramedTriple w s p c S Q) (hge : ∀ a ∈ S, s.frontier ≤ a) :
    Memory.FramedTriple w s p c ∅ Q :=
  Memory.Triple.mono h le_rfl fun _ _ ⟨hm, hq⟩ =>
    ⟨⟨hm.1, fun a ha _ => hm.2 a ha fun haS => absurd ha (Nat.not_lt.mpr (hge a haS))⟩, hq⟩

/-- Concatenate three fixed-stride record slices into a freshly dirty-allocated `Block` of
length `a.stride * (a.lenA + a.lenB + a.lenC)`. -/
def concatRecordsProg (a : ConcatRecordsArgs) : Memory.Prog Block := do
  let out ← Memory.allocBlockDirty (a.stride * (a.lenA + a.lenB + a.lenC))
  Memory.copy a.srcA out.base (a.stride * a.lenA)
  Memory.copy a.srcB (out.base + a.stride * a.lenA) (a.stride * a.lenB)
  Memory.copy a.srcC (out.base + a.stride * a.lenA + a.stride * a.lenB) (a.stride * a.lenC)
  pure out

private theorem framedTriple_preserve_below {α : Type} {w c bound : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {dst len : ℕ} {Q : α → Memory.State → Prop}
    (hb : bound ≤ dst) (hlim : bound ≤ s.frontier)
    (h : Memory.FramedTriple w s p c (Set.Ico dst (dst + len)) Q) :
    Memory.FramedTriple w s p c (Set.Ico dst (dst + len))
      fun a s' => Q a s' ∧ ∀ x < bound, s'.mem x = s.mem x :=
  h.frame_mem (D := Set.Iio bound) (R := fun m => ∀ x < bound, m x = s.mem x)
    (fun _ _ => rfl) (fun m₁ m₂ heq hr x hx => (heq x hx).symm.trans (hr x hx))
    (Set.disjoint_left.mpr fun a ha1 ha2 => by
      simp only [Set.mem_Ico, Set.mem_Iio] at ha1 ha2
      omega)
    (fun a ha => by
      simp only [Set.mem_Iio] at ha
      omega)

/-- Framed specification for `concatRecordsProg`: allocates a dirty `Block` of size
`stride * (rowsA.length + rowsB.length + rowsC.length)` at `s.frontier`, preserves all cells
below `s.frontier` (`Memory.Modifies ∅`), realizes `HoldsRecords stride out.base (rowsA ++ rowsB ++
rowsC)` in cost at most `2 * (stride * (rowsA.length + rowsB.length + rowsC.length)) + 1`, and
preserves `Memory.WellFormed`. -/
theorem concatRecordsProg_spec {w stride srcA srcB srcC : ℕ}
    {rowsA rowsB rowsC : List (Fin stride → ℕ)} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hA : HoldsRecords stride srcA rowsA s.mem) (hA_lt : srcA + stride * rowsA.length ≤ s.frontier)
    (hB : HoldsRecords stride srcB rowsB s.mem) (hB_lt : srcB + stride * rowsB.length ≤ s.frontier)
    (hC : HoldsRecords stride srcC rowsC s.mem) (hC_lt : srcC + stride * rowsC.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + stride * (rowsA.length + rowsB.length + rowsC.length))) :
    let a : ConcatRecordsArgs :=
      ⟨stride, srcA, rowsA.length, srcB, rowsB.length, srcC, rowsC.length⟩
    let tot := rowsA.length + rowsB.length + rowsC.length
    Memory.FramedTriple w s (concatRecordsProg a) (2 * (stride * tot) + 1) ∅ fun out s' =>
      out = ⟨s.frontier, stride * tot⟩ ∧
      out.Allocated s' ∧
      s'.frontier = s.frontier + stride * tot ∧
      Memory.WellFormed w s' ∧
      HoldsRecords stride out.base (rowsA ++ rowsB ++ rowsC) s'.mem := by
  let tot := rowsA.length + rowsB.length + rowsC.length
  let outBase := s.frontier
  let dstB := outBase + stride * rowsA.length
  let dstC := dstB + stride * rowsB.length
  let fEnd := outBase + stride * tot
  have hmul_tot : stride * tot =
      stride * rowsA.length + stride * rowsB.length + stride * rowsC.length := by
    dsimp only [tot]
    rw [Nat.mul_add, Nat.mul_add]
  have hfEnd_eq : dstC + stride * rowsC.length = fEnd := by
    dsimp only [dstC, dstB, fEnd, outBase]; rw [hmul_tot]; omega
  let S := Set.Ico outBase fEnd
  have hsubA : Set.Ico outBase (outBase + stride * rowsA.length) ⊆ S := by
    intro x ⟨h1, h2⟩; refine ⟨h1, ?_⟩; dsimp only [fEnd]; rw [hmul_tot]; omega
  have hsubB : Set.Ico dstB (dstB + stride * rowsB.length) ⊆ S := by
    intro x ⟨h1, h2⟩; refine ⟨?_, ?_⟩
    · dsimp only [dstB] at h1; omega
    · dsimp only [fEnd, dstB] at h2 ⊢; rw [hmul_tot]; omega
  have hsubC : Set.Ico dstC (dstC + stride * rowsC.length) ⊆ S := by
    intro x ⟨h1, h2⟩; refine ⟨?_, ?_⟩
    · dsimp only [dstC, dstB] at h1; omega
    · dsimp only [fEnd, dstC, dstB] at h2 ⊢; rw [hmul_tot]; omega
  have hft : Memory.FramedTriple w s (concatRecordsProg
      ⟨stride, srcA, rowsA.length, srcB, rowsB.length, srcC, rowsC.length⟩)
      ((2 * (stride * rowsA.length) +
        (2 * (stride * rowsB.length) + (2 * (stride * rowsC.length) + 0))) + 1) S
      fun out s' =>
        out = ⟨outBase, stride * tot⟩ ∧
        out.Allocated s' ∧
        s'.frontier = fEnd ∧
        Memory.WellFormed w s' ∧
        HoldsRecords stride out.base (rowsA ++ rowsB ++ rowsC) s'.mem := by
    dsimp only [concatRecordsProg]
    refine Memory.FramedTriple.allocBlockDirty_bind hfit ?_
    have hwf0 : Memory.WellFormed w ⟨s.mem, fEnd⟩ := hwf.step (o := .allocDirty _) hfit
    have hcA := (framedTriple_preserve_below (bound := s.frontier) (dst := outBase)
      (len := stride * rowsA.length) le_rfl (by dsimp only [fEnd, outBase]; omega)
      (HoldsRecords.copy (w := w) (s := ⟨s.mem, fEnd⟩) (src := srcA) (dst := outBase)
        (rows := rowsA) (Or.inl hA_lt) (by dsimp only [fEnd, outBase]; omega)
        (by dsimp only [fEnd, outBase]; omega) hwf0 hA)).frame_mono hsubA
    refine Memory.FramedTriple.bind_same
      (hcA.mono le_rfl fun _ s₁ ⟨⟨hs₁_fr, hwf₁, hrowsA₁⟩, hkeep₁⟩ => ?_)
    have hB₁ : HoldsRecords stride srcB rowsB s₁.mem :=
      hB.congr fun x _ hhi => hkeep₁ x (lt_of_lt_of_le hhi hB_lt)
    have hcB := (framedTriple_preserve_below (bound := dstB) (dst := dstB)
      (len := stride * rowsB.length) le_rfl
      (by rw [hs₁_fr]; dsimp only [fEnd, dstB, outBase]; omega)
      (HoldsRecords.copy (w := w) (s := s₁) (src := srcB) (dst := dstB)
        (rows := rowsB) (Or.inl (by dsimp only [dstB, outBase]; omega))
        (by rw [hs₁_fr]; dsimp only [fEnd, outBase]; omega)
        (by rw [hs₁_fr]; dsimp only [fEnd, dstB, outBase]; omega) hwf₁ hB₁)).frame_mono hsubB
    refine Memory.FramedTriple.bind_same
      (hcB.mono le_rfl fun _ s₂ ⟨⟨hs₂_fr, hwf₂, hrowsB₂⟩, hkeep₂⟩ => ?_)
    have hs₂_end : s₂.frontier = fEnd := hs₂_fr.trans hs₁_fr
    have hC₂ : HoldsRecords stride srcC rowsC s₂.mem :=
      hC.congr fun x _ hhi =>
        (hkeep₂ x (by dsimp only [dstB, outBase]; omega)).trans
          (hkeep₁ x (lt_of_lt_of_le hhi hC_lt))
    have hcC := (framedTriple_preserve_below (bound := dstC) (dst := dstC)
      (len := stride * rowsC.length) le_rfl
      (by rw [hs₂_end]; dsimp only [fEnd, dstC, dstB, outBase]; omega)
      (HoldsRecords.copy (w := w) (s := s₂) (src := srcC) (dst := dstC)
        (rows := rowsC) (Or.inl (by dsimp only [dstC, dstB, outBase]; omega))
        (by rw [hs₂_end]; dsimp only [fEnd, outBase]; omega)
        (by rw [hs₂_end]; dsimp only [fEnd, dstC, dstB, outBase]; omega) hwf₂ hC₂)).frame_mono hsubC
    refine Memory.FramedTriple.bind_same
      (hcC.mono le_rfl fun _ s₃ ⟨⟨hs₃_fr, hwf₃, hrowsC₃⟩, hkeep₃⟩ => ?_)
    have hs₃_end : s₃.frontier = fEnd := hs₃_fr.trans hs₂_end
    refine Memory.FramedTriple.pure ⟨rfl, ?_, hs₃_end, hwf₃, ?_⟩
    · change outBase + stride * tot ≤ s₃.frontier
      rw [hs₃_end]
    have hrowsA₃ : HoldsRecords stride outBase rowsA s₃.mem :=
      hrowsA₁.congr fun x hlo hhi =>
        (hkeep₃ x (by dsimp only [dstC, dstB]; omega)).trans
          (hkeep₂ x (by dsimp only [dstB]; exact hhi))
    have hrowsB₃ : HoldsRecords stride dstB rowsB s₃.mem :=
      hrowsB₂.congr fun x _ hhi => hkeep₃ x (by dsimp only [dstC]; exact hhi)
    have hAB := HoldsRecords.append_iff.mpr ⟨hrowsA₃, hrowsB₃⟩
    exact HoldsRecords.append_iff.mpr ⟨hAB, by
      simpa only [List.length_append, Nat.mul_add, ← Nat.add_assoc] using hrowsC₃⟩
  have hmul_cost : stride * (rowsA.length + rowsB.length + rowsC.length) =
      stride * rowsA.length + stride * rowsB.length + stride * rowsC.length := by
    simp only [Nat.mul_add]
  exact (Memory.FramedTriple.mono hft (by rw [hmul_cost]; omega)
    fun _ _ h => h).frame_empty_of_ge_frontier fun _ ha => ha.1

/-- Uniform `Realizes .exact` certificate for `concatRecordsProg` with `work = 0`. -/
theorem realizes_concatRecordsProg :
    Realizes .exact concatRecordsProg concatRecordsArgsWords WordEncoding.encode
      (fun w a s =>
        Fits w (a.lenA + a.lenB + a.lenC) ∧
        a.srcA + a.stride * a.lenA ≤ s.frontier ∧
        a.srcB + a.stride * a.lenB ≤ s.frontier ∧
        a.srcC + a.stride * a.lenC ≤ s.frontier)
      (fun _ _ => 0) := by
  unfold concatRecordsProg
  have hbase : Realizes .exact concatRecordsProg concatRecordsArgsWords WordEncoding.encode
      (fun w a s =>
        Fits w (a.lenA + a.lenB + a.lenC) ∧
        Fits w (s.frontier + a.stride * (a.lenA + a.lenB + a.lenC)) ∧
        a.srcA + a.stride * a.lenA ≤ s.frontier ∧
        a.srcB + a.stride * a.lenB ≤ s.frontier ∧
        a.srcC + a.stride * a.lenC ≤ s.frontier)
      (fun _ _ => 0) := by
    realize [realizes_allocBlockDirty, realizes_copy]
    all_goals
      have hfit := h.1
      have htot := h.2.1
      have h1 := h.2.2.1
      have h2 := h.2.2.2.1
      have h3 := h.2.2.2.2
      have hmul : d.stride * (d.lenA + d.lenB + d.lenC) =
          d.stride * d.lenA + d.stride * d.lenB + d.stride * d.lenC := by
        rw [Nat.mul_add, Nat.mul_add]
      have hres0 : ((Memory.spec 0).clientResult s
          (Memory.allocBlockDirty (d.stride * (d.lenA + d.lenB + d.lenC)))).base = s.frontier :=
        rfl
      have hst0 : (Memory.spec 0).clientState s
          (Memory.allocBlockDirty (d.stride * (d.lenA + d.lenB + d.lenC))) =
          ⟨s.mem, s.frontier + d.stride * (d.lenA + d.lenB + d.lenC)⟩ := rfl
      have hc1 : ((Memory.spec 0).clientState
          ⟨s.mem, s.frontier + d.stride * (d.lenA + d.lenB + d.lenC)⟩
          (Memory.copy d.srcA s.frontier (d.stride * d.lenA))).frontier =
          s.frontier + d.stride * (d.lenA + d.lenB + d.lenC) :=
        congrArg Memory.State.frontier (Memory.clientState_copy _ _ _ _ (Or.inl h1))
      have hc2 : ((Memory.spec 0).clientState
          ((Memory.spec 0).clientState
            ⟨s.mem, s.frontier + d.stride * (d.lenA + d.lenB + d.lenC)⟩
            (Memory.copy d.srcA s.frontier (d.stride * d.lenA)))
          (Memory.copy d.srcB (s.frontier + d.stride * d.lenA) (d.stride * d.lenB))).frontier =
          s.frontier + d.stride * (d.lenA + d.lenB + d.lenC) := by
        rw [Memory.clientState_copy _ _ _ _ (Or.inl (by omega))]
        exact hc1
      simp only [hres0, hst0, hc2, hc1] at *
      first
      | exact hfit
      | exact htot.of_le (by omega)
      | omega
  refine hbase.consequence_valid (fun w a s _ _ hv ⟨hlen, hA, hB, hC⟩ => ?_)
  dsimp only [concatRecordsProg, StateTransitionSpec.clientHistory] at hv
  rw [Memory.runClient_allocBlockDirty_bind] at hv
  exact ⟨hlen, hv.1, hA, hB, hC⟩

end Cslib.WordRAM.Realization
