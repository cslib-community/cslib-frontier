/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.StoerWagner.Basic
public import CslibFrontier.Algorithms.WordRAM.Karger.Contract
public import CslibFrontier.Computability.WordRAM.ListOutput
import CslibFrontier.Computability.WordRAM.MapOp
import CslibFrontier.Computability.WordRAM.Realization.FramedLoop
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.Computability.WordRAM.Realization.Program
import CslibFrontier.Computability.WordRAM.Realization.Structure
import CslibFrontier.DataStructure.StateTransition
import CslibFrontier.Tactic.FinIndex
import CslibFrontier.Tactic.Realize

/-!
# Deterministic Stoer–Wagner global minimum cut on the Word-RAM (`O(n³)`)

This module implements the dense `O(n³)` array version of the Stoer–Wagner deterministic global
minimum cut algorithm [StoerWagner1997] on the deterministic width-blind standard-basis Word-RAM
(`Cslib.WordRAM.Basis.standard`, `¬prog.ReadsWidth`), proving a uniform `C * (I.n + 1) ^ 3`
instruction-count bound (`Program.ComputesListInTime`) at any word width `w` satisfying
`Fits w I.wordBound` (i.e., `I.wordBound < 2 ^ w`, where `I.wordBound` is a polynomial bound on
word values and addresses, so a bit width `w` of order
`log (I.n + 2) + log (totalDoubledWeight I.W + 2)` suffices).

On input `I.encode = I.n :: Karger.flattenMatrix I.W` for any weighted multigraph
`I : StoerWagnerInput` (`I.isMultigraph : Cslib.WeightedCut.IsMultigraph I.W`), the algorithm
maintains the active `m × m` contracted weight matrix in-place with stride `n`, the supervertex
assignment array `part : Fin n → Fin m`, maximum-adjacency-search key/visited arrays, and the best
cut buffer directly in the output list layout
`[n + 1, bestWeight, bestSide[0], …, bestSide[n - 1]]`.
Across all `n - 1` contraction phases, `totalDoubledWeight` is nonincreasing
(`Cslib.WeightedCut.totalDoubledWeight_contractMatrix`), so every intermediate matrix entry,
merged edge sum `W s j + W t j`, attachment key, and cut weight stays at most
`totalDoubledWeight I.W`. Any word width `w` with `Fits w I.wordBound`, where
`I.wordBound = max (workspaceBound I.n) (totalDoubledWeight I.W)` bounds all word values and
addresses (`I.wordBound < 2 ^ w`), therefore executes without overflow.

The dense `O(n³)` array Word-RAM program and word-value/address bound are original over
[StoerWagner1997] (which states the algorithm at the high level using a priority queue in
`O(n m + n² log n)` time).

## Main definitions

* `Cslib.Algorithms.WordRAM.StoerWagner.workspaceBound`: word-address bound covering all `O(n²)`
  input, workspace, and output addresses.
* `Cslib.Algorithms.WordRAM.StoerWagner.StoerWagnerInput`: documented weighted-multigraph input
  record carrying `n`, `W`, and `isMultigraph`.
* `Cslib.Algorithms.WordRAM.StoerWagner.StoerWagnerInput.encode`: flat Word-RAM input word list
  `I.n :: Karger.flattenMatrix I.W`.
* `Cslib.Algorithms.WordRAM.StoerWagner.StoerWagnerInput.wordBound`: polynomial word-value and
  address bound `max (workspaceBound I.n) (totalDoubledWeight I.W)` (required to satisfy
  `Fits w I.wordBound`, i.e., `I.wordBound < 2 ^ w`).
* `Cslib.Algorithms.WordRAM.StoerWagner.StoerWagnerInput.expectedOutput`: expected output word list
  consisting of `(stoerWagner I.W).weight` followed by the `0`/`1` indicator of
  `(stoerWagner I.W).side`.

## Main results

* `Cslib.Algorithms.WordRAM.StoerWagner.StoerWagnerInput.inputFits_encode`: every word width
  fitting `I.wordBound` satisfies `InputFits w I.encode`.
* `Cslib.Algorithms.WordRAM.StoerWagner.StoerWagnerInput.expectedOutput_spec`: for `2 ≤ I.n`,
  decoding `I.expectedOutput` yields length `I.n + 1`, head word `minCut I.W`, and a non-trivial
  global minimum cut of `I.W` achieving `minCut I.W`.
* `Cslib.Algorithms.WordRAM.StoerWagner.exists_stoerWagner_program`: uniform `O(n³)` width-blind
  standard-basis Word-RAM program (`Program.ComputesListInTime`) computing `I.expectedOutput` in
  `C * (I.n + 1) ^ 3` instructions at every word width `w` with `Fits w I.wordBound`.

## References

* [M. Stoer and F. Wagner, *A Simple Min-Cut Algorithm*][StoerWagner1997]
-/

namespace Cslib.Algorithms.WordRAM.StoerWagner

open Cslib.Algorithms.Lean.StoerWagner
open Cslib.DataStructure
open Cslib.WeightedCut
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### Public input, output, and word-value bound interface -/

public section

/-- Word-address bound covering the input list, mutable `n × n` matrix workspace, `part`/`key`/
`used` arrays, and the `(n + 2)`-word output buffer. -/
@[expose] def workspaceBound (n : ℕ) : ℕ :=
  2 * n * n + 8 * n + 16

/-- Weighted multigraph input on `Fin n` for Word-RAM Stoer–Wagner global minimum cut. -/
structure StoerWagnerInput where
  /-- Number of vertices. -/
  n : ℕ
  /-- Nonnegative symmetric zero-diagonal edge-weight matrix. -/
  W : Fin n → Fin n → ℕ
  /-- Symmetry and zero-diagonal witness (`IsMultigraph W`). -/
  isMultigraph : IsMultigraph W

/-- Flat Word-RAM input encoding `I.n :: Karger.flattenMatrix I.W`. -/
@[expose] def StoerWagnerInput.encode (I : StoerWagnerInput) : List ℕ :=
  I.n :: Karger.flattenMatrix I.W

/-- Polynomial word-value and address bound `max (workspaceBound I.n) (totalDoubledWeight I.W)`
(requiring `Fits w I.wordBound`, i.e., `I.wordBound < 2 ^ w`). -/
@[expose] def StoerWagnerInput.wordBound (I : StoerWagnerInput) : ℕ :=
  max (workspaceBound I.n) (totalDoubledWeight I.W)

/-- Every word width fitting `I.wordBound` satisfies `InputFits w I.encode`. -/
theorem StoerWagnerInput.inputFits_encode {w : ℕ} (I : StoerWagnerInput)
    (hwb : Fits w I.wordBound) : InputFits w I.encode :=
  Karger.inputFits_cons_flattenMatrix (hwb.of_le (le_max_left _ _))
    (by dsimp only [workspaceBound]; nlinarith)
    (by dsimp only [workspaceBound]; omega)
    (hwb.of_le (le_max_right _ _))

/-- Expected list output `[weight, bit₀, …, bitₙ₋₁]` of `stoerWagner I.W`, where `bitᵥ = 1` iff
`v ∈ (stoerWagner I.W).side`. -/
@[expose] def StoerWagnerInput.expectedOutput (I : StoerWagnerInput) : List ℕ :=
  (stoerWagner I.W).weight ::
    (List.finRange I.n).map fun v => if v ∈ (stoerWagner I.W).side then 1 else 0

/-- For every multigraph with `2 ≤ I.n`, the output word list `I.expectedOutput` has length
`I.n + 1`, its head word is `minCut I.W`, and decoding the `1`-bits at positions `1, …, I.n`
recovers a non-trivial global minimum cut of `I.W` achieving weight `minCut I.W`. -/
theorem StoerWagnerInput.expectedOutput_spec (I : StoerWagnerInput) (hn : 2 ≤ I.n) :
    let out := I.expectedOutput
    let side : Finset (Fin I.n) := Finset.univ.filter fun v : Fin I.n => out[v.1 + 1]? = some 1
    out.length = I.n + 1 ∧
      out.head? = some (minCut I.W) ∧
      IsNonTrivialCut side ∧
      cutWeight I.W side = minCut I.W := by
  obtain ⟨hnt, hcw, hw⟩ := stoerWagner_spec hn I.isMultigraph
  have hside :
      (Finset.univ.filter fun v : Fin I.n => I.expectedOutput[v.1 + 1]? = some 1) =
        (stoerWagner I.W).side := by
    ext v
    simp [StoerWagnerInput.expectedOutput]
  refine ⟨by simp [StoerWagnerInput.expectedOutput], by simp [StoerWagnerInput.expectedOutput, hw],
    hside ▸ hnt, hside ▸ hcw⟩

end

/-! ### Local `Memory.Prog` simplification -/

-- Local `simp`-indexed forms matching `StateTransitionSpec.fst_snd_runClient_bind`.
attribute [local client_simps] StateTransitionSpec.clientState
  runClient_read runClient_write runClient_allocDirty runClient_ite

/-! ### Pure combinatorics and `maSearch` / `run` bridges -/

private theorem cell_lt_mul {m str x y : ℕ} (hstr : m ≤ str) (hx : x < m) (hy : y < m) :
    x * str + y < m * str := by
  have h := Karger.matAddr_lt_end (wb := 0) hstr ⟨x, hx⟩ ⟨y, hy⟩
  dsimp only at h
  rw [Nat.mul_comm str m] at h
  omega

/-- Distinct matrix cells have distinct addresses. -/
private theorem matAddr_ne {mb m str x₁ y₁ x₂ y₂ : ℕ} (hstr : m ≤ str)
    (hx₁ : x₁ < m) (hy₁ : y₁ < m) (hx₂ : x₂ < m) (hy₂ : y₂ < m) (h : ¬(x₁ = x₂ ∧ y₁ = y₂)) :
    mb + x₁ * str + y₁ ≠ mb + x₂ * str + y₂ := fun heq => h <| by
  have ⟨hi, hj⟩ := Karger.matAddr_inj (wb := mb) hstr (i₁ := ⟨x₁, hx₁⟩) (j₁ := ⟨y₁, hy₁⟩)
    (i₂ := ⟨x₂, hx₂⟩) (j₂ := ⟨y₂, hy₂⟩) heq
  exact ⟨congrArg Fin.val hi, congrArg Fin.val hj⟩

/-- Away from the swept index `k`, the sweep condition `· < k + 1` agrees with `· < k`. -/
private theorem and_lt_succ_iff {p : Prop} {j k : ℕ} (h : p → j ≠ k) :
    (p ∧ j < k + 1) ↔ (p ∧ j < k) :=
  and_congr_right fun hp =>
    ⟨fun hlt => lt_of_le_of_ne (Nat.le_of_lt_succ hlt) (h hp), Nat.lt_succ_of_lt⟩

private theorem add_entry_le_totalDoubledWeight {m : ℕ} {W : Fin m → Fin m → ℕ}
    {s t : Fin m} (hst : s ≠ t) (j : Fin m) :
    W s j + W t j ≤ totalDoubledWeight W := by
  have hs : W s j ≤ rowDeg W s := entry_le_rowDeg W s j
  have ht : W t j ≤ rowDeg W t := entry_le_rowDeg W t j
  have hsum : rowDeg W s + rowDeg W t ≤ totalDoubledWeight W := by
    unfold totalDoubledWeight
    rw [← Finset.add_sum_erase _ (rowDeg W) (Finset.mem_univ s),
      ← Finset.add_sum_erase _ (rowDeg W) (Finset.mem_erase.mpr ⟨hst.symm, Finset.mem_univ t⟩)]
    omega
  omega

private theorem attachWeight_le_totalDoubledWeight {m : ℕ} {W : Fin m → Fin m → ℕ}
    (hW : IsMultigraph W) (A : Finset (Fin m)) (y : Fin m) :
    attachWeight W A y ≤ totalDoubledWeight W := by
  have h1 : attachWeight W A y ≤ attachWeight W Finset.univ y :=
    attachWeight_mono W (Finset.subset_univ A) y
  have h2 : attachWeight W Finset.univ y = rowDeg W y := by
    rw [attachWeight_def]
    unfold rowDeg
    exact Finset.sum_congr rfl fun a _ => hW.1 a y
  exact (h1.trans (le_of_eq h2)).trans (rowDeg_le_totalDoubledWeight W y)

private theorem attachWeight_erase_self {m : ℕ} {W : Fin m → Fin m → ℕ}
    (hW : IsMultigraph W) (t : Fin m) :
    attachWeight W (Finset.univ.erase t) t = rowDeg W t := by
  rw [attachWeight_def]
  unfold rowDeg
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin m)) (fun a => W a t)
    (Finset.mem_univ t)
  have hsym : ∑ a : Fin m, W a t = ∑ a : Fin m, W t a :=
    Finset.sum_congr rfl fun a _ => hW.1 a t
  have hdiag : W t t = 0 := hW.2 t
  omega

private theorem erase_filter_finRange {m : ℕ} (p : Fin m → Bool) (v : Fin m) :
    ((List.finRange m).filter p).erase v =
      (List.finRange m).filter (fun x => p x && decide (x ≠ v)) := by
  rw [((List.nodup_finRange m).filter p).erase_eq_filter, List.filter_filter]
  exact List.filter_congr fun x _ => by by_cases h : x = v <;> simp [h]

private theorem idxOf_le_of_pairwise_lt {m : ℕ} {l : List (Fin m)} (hl : l.Pairwise (· < ·))
    {a b : Fin m} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≤ b) :
    l.idxOf a ≤ l.idxOf b := by
  induction l with
  | nil => simp at ha
  | cons x t ih =>
    rw [List.pairwise_cons] at hl
    by_cases hax : x = a
    · subst hax; simp
    · have ha' : a ∈ t := (List.mem_cons.mp ha).resolve_left (Ne.symm hax)
      have hxb : x ≠ b := fun h => by
        subst h
        exact absurd (hl.1 a ha') (not_lt_of_ge hab)
      have hb' : b ∈ t := (List.mem_cons.mp hb).resolve_left (Ne.symm hxb)
      simp only [List.idxOf_cons_ne _ hax, List.idxOf_cons_ne _ hxb]
      exact Nat.succ_le_succ (ih hl.2 ha' hb')

private theorem argmax_filter_finRange_eq {m : ℕ} (used : Fin m → Bool) (key : Fin m → ℕ)
    (v : Fin m) (hv : used v = false)
    (hmax : ∀ x : Fin m, used x = false → key x ≤ key v)
    (hfirst : ∀ x : Fin m, used x = false → x.1 < v.1 → key x < key v) :
    ((List.finRange m).filter fun x => !used x).argmax key = some v := by
  rw [List.argmax_eq_some_iff]
  have hmem : ∀ x : Fin m, x ∈ (List.finRange m).filter (fun x => !used x) ↔ used x = false := by
    intro x
    simp [List.mem_filter, List.mem_finRange]
  refine ⟨(hmem v).mpr hv, fun a ha => hmax a ((hmem a).mp ha), fun a ha hle => ?_⟩
  have hlt : ¬(a.1 < v.1) := fun h => not_lt_of_ge hle (hfirst a ((hmem a).mp ha) h)
  have hvle : v ≤ a := Fin.le_iff_val_le_val.mpr (Nat.le_of_not_lt hlt)
  exact idxOf_le_of_pairwise_lt ((List.pairwise_lt_finRange m).filter _)
    ((hmem v).mpr hv) ha hvle

private def chooseCut {n : ℕ} (a b : CutResult n) : CutResult n :=
  if b.weight ≤ a.weight then b else a

private theorem chooseCut_assoc {n : ℕ} (a b c : CutResult n) :
    chooseCut (chooseCut a b) c = chooseCut a (chooseCut b c) := by
  unfold chooseCut
  split_ifs <;> first | rfl | omega

private theorem maOrder_fin_two (W : Fin 2 → Fin 2 → ℕ) : maOrder W = [0, 1] := by
  unfold maOrder maSearch
  have h0 : (List.finRange 2).argmax (fun _ : Fin 2 => (0 : ℕ)) = some 0 := by decide
  have h1 : ((List.finRange 2).erase 0).argmax (fun y : Fin 2 => W 0 y) = some 1 := by
    have he : (List.finRange 2).erase 0 = [1] := by decide
    rw [he]
    rfl
  simp [h0, h1, maSearch]

/-! ### Workspace address layout -/

private abbrev matBase (ws : ℕ) : ℕ := ws
private abbrev partBase (ws n : ℕ) : ℕ := ws + n * n
private abbrev keyBase (ws n : ℕ) : ℕ := ws + n * n + n
private abbrev usedBase (ws n : ℕ) : ℕ := ws + n * n + 2 * n
private abbrev outBase (ws n : ℕ) : ℕ := ws + n * n + 3 * n
private abbrev wsSize (n : ℕ) : ℕ := n * n + 4 * n + 2

attribute [local wram_arith] matBase partBase keyBase usedBase outBase wsSize

private abbrev pairWords : ℕ × ℕ ↪ (Fin 2 → ℕ) :=
  appendWords wordWords wordWords

/-! ### Primitive array loops (`copyWordsProg`, `initPartProg`, `initMAProg`, `writeSideProg`) -/

private structure CopyArgs where
  src : ℕ
  dst : ℕ
  len : ℕ

private word_enc_structure encCopyArgs : CopyArgs where
  src : wordWords, dst : wordWords, len : wordWords

private instance : WordEncoding CopyArgs := ⟨3, encCopyArgs⟩

private def copyStep (q : CopyArgs × ℕ) : Memory.Prog ℕ := do
  let a := Prod.fst q
  let i := Prod.snd q
  let v ← Memory.read (a.src + i)
  Memory.write (a.dst + i) v
  pure (i + 1)

private abbrev CopyStepSafe (w : ℕ) (q : CopyArgs × ℕ) (_ : Memory.State) : Prop :=
  Fits w (q.1.src + q.2) ∧ Fits w (q.1.dst + q.2) ∧ Fits w (q.2 + 1)

private theorem copyStep_realizes :
    Realizes .exact copyStep (appendWords encCopyArgs wordWords) wordWords
      CopyStepSafe (fun _ _ => 0) := by
  unfold copyStep
  realize
  all_goals first | exact h.1 | exact h.2.1 | exact h.2.2

private def copyWordsProg (a : CopyArgs) : Memory.Prog ℕ :=
  iterate copyStep a a.len 0

private theorem copyWordsProg_realizes :
    Realizes .exact copyWordsProg encCopyArgs wordWords
      (fun w a s => iterationSafe copyStep CopyStepSafe w a a.len 0 s)
      (fun _ _ => 0) := by
  unfold copyWordsProg
  realize [copyStep_realizes]
  exact h

private theorem copyWordsProg_spec {w : ℕ} (a : CopyArgs) (s₀ : Memory.State)
    (hsrc_f : a.src + a.len ≤ s₀.frontier) (hdst_f : a.dst + a.len ≤ s₀.frontier)
    (hdisj : a.src + a.len ≤ a.dst)
    (hfit_src : Fits w (a.src + a.len)) (hfit_dst : Fits w (a.dst + a.len))
    (hfit_len : Fits w a.len)
    (hfit_vals : ∀ i < a.len, Fits w (s₀.mem (a.src + i))) :
    iterationSafe copyStep CopyStepSafe w a a.len 0 s₀ ∧
      Memory.FramedTriple w s₀ (copyWordsProg a) (2 * a.len) (Set.Ico a.dst (a.dst + a.len))
        fun _ t => ∀ i < a.len, t.mem (a.dst + i) = s₀.mem (a.src + i) := by
  refine Memory.FramedTriple.iterate
    (fun k i t => i = k ∧ ∀ j < k, t.mem (a.dst + j) = s₀.mem (a.src + j))
    ⟨rfl, by simp⟩ (fun k hk i t ⟨hi, hdone⟩ ⟨hfr, hframe⟩ => ?_) fun _ _ h _ => h.2
  subst i
  have hsrc := hframe (a.src + k) (by omega) (by region_omega)
  have hval := hsrc ▸ hfit_vals k hk
  refine ⟨⟨by region_omega, by region_omega, by region_omega⟩, ?_⟩
  unfold copyStep
  framed_triple
  refine ⟨rfl, Nat.forall_lt_succ_right.2 ⟨fun j hj => ?_, by simp [hsrc]⟩⟩
  simp [hj.ne, hdone j hj]

private def initPartStep (q : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let base := Prod.fst (Prod.fst q)
  let i := Prod.snd q
  Memory.write (base + i) i
  pure (i + 1)

private abbrev InitPartStepSafe (w : ℕ) (q : (ℕ × ℕ) × ℕ) (_ : Memory.State) : Prop :=
  Fits w (q.1.1 + q.2) ∧ Fits w (q.2 + 1)

private theorem initPartStep_realizes :
    Realizes .exact initPartStep (appendWords pairWords wordWords) wordWords
      InitPartStepSafe (fun _ _ => 0) := by
  unfold initPartStep
  realize
  all_goals first | exact h.1 | exact h.2

private def initPartProg (d : ℕ × ℕ) : Memory.Prog ℕ :=
  iterate initPartStep d (Prod.snd d) 0

private theorem initPartProg_realizes :
    Realizes .exact initPartProg pairWords wordWords
      (fun w d s => iterationSafe initPartStep InitPartStepSafe w d (Prod.snd d) 0 s)
      (fun _ _ => 0) := by
  unfold initPartProg
  realize [initPartStep_realizes]
  exact h

private theorem initPartProg_spec {w : ℕ} (base n : ℕ) (s₀ : Memory.State)
    (hf : base + n ≤ s₀.frontier) (hfit : Fits w (base + n)) :
    iterationSafe initPartStep InitPartStepSafe w (base, n) n 0 s₀ ∧
      Memory.FramedTriple w s₀ (initPartProg (base, n)) (1 * n) (Set.Ico base (base + n))
        fun _ t => ∀ v : Fin n, t.mem (base + v.1) = v.1 := by
  refine Memory.FramedTriple.iterate (fun k i t => i = k ∧ ∀ v < k, t.mem (base + v) = v)
    ⟨rfl, by simp⟩ (fun k hk i t ⟨hi, hdone⟩ ⟨hfr, _⟩ => ?_) fun _ _ h _ v => h.2 v.1 v.isLt
  subst i
  refine ⟨⟨by region_omega, by region_omega⟩, ?_⟩
  unfold initPartStep
  framed_triple
  refine ⟨rfl, Nat.forall_lt_succ_right.2 ⟨fun j hj => ?_, by simp⟩⟩
  simp [hj.ne, hdone j hj]

private structure InitMAArgs where
  kb : ℕ
  ub : ℕ
  m : ℕ

private word_enc_structure encInitMAArgs : InitMAArgs where
  kb : wordWords, ub : wordWords, m : wordWords

private instance : WordEncoding InitMAArgs := ⟨3, encInitMAArgs⟩

private def initMAStep (q : InitMAArgs × ℕ) : Memory.Prog ℕ := do
  let a := Prod.fst q
  let i := Prod.snd q
  Memory.write (a.kb + i) 0
  Memory.write (a.ub + i) 0
  pure (i + 1)

private abbrev InitMAStepSafe (w : ℕ) (q : InitMAArgs × ℕ) (_ : Memory.State) : Prop :=
  Fits w (q.1.kb + q.2) ∧ Fits w (q.1.ub + q.2) ∧ Fits w (q.2 + 1)

private theorem initMAStep_realizes :
    Realizes .exact initMAStep (appendWords encInitMAArgs wordWords) wordWords
      InitMAStepSafe (fun _ _ => 0) := by
  unfold initMAStep
  realize
  all_goals first | exact h.1 | exact h.2.1 | exact h.2.2

private def initMAProg (a : InitMAArgs) : Memory.Prog ℕ :=
  iterate initMAStep a a.m 0

private theorem initMAProg_realizes :
    Realizes .exact initMAProg encInitMAArgs wordWords
      (fun w a s => iterationSafe initMAStep InitMAStepSafe w a a.m 0 s)
      (fun _ _ => 0) := by
  unfold initMAProg
  realize [initMAStep_realizes]
  exact h

private theorem initMAProg_spec {w : ℕ} (a : InitMAArgs) (s₀ : Memory.State)
    (hk_f : a.kb + a.m ≤ s₀.frontier) (hu_f : a.ub + a.m ≤ s₀.frontier)
    (hdisj : a.kb + a.m ≤ a.ub)
    (hfit_k : Fits w (a.kb + a.m)) (hfit_u : Fits w (a.ub + a.m)) :
    iterationSafe initMAStep InitMAStepSafe w a a.m 0 s₀ ∧
      Memory.FramedTriple w s₀ (initMAProg a) (2 * a.m)
        (Set.Ico a.kb (a.kb + a.m) ∪ Set.Ico a.ub (a.ub + a.m))
        fun _ t => ∀ i < a.m, t.mem (a.kb + i) = 0 ∧ t.mem (a.ub + i) = 0 := by
  refine Memory.FramedTriple.iterate
    (fun k i t => i = k ∧ ∀ j < k, t.mem (a.kb + j) = 0 ∧ t.mem (a.ub + j) = 0)
    ⟨rfl, by simp⟩ (fun k hk i t ⟨hi, hdone⟩ ⟨hfr, _⟩ => ?_) fun _ _ h _ => h.2
  subst i
  refine ⟨⟨by region_omega, by region_omega, by region_omega⟩, ?_⟩
  unfold initMAStep
  framed_triple
  refine ⟨rfl, Nat.forall_lt_succ_right.2 ⟨fun j hj => ?_, ?_⟩⟩
  · simp [Function.update_apply, show a.kb + j ≠ a.ub + k by omega, hdone j hj]
  · simp [Function.update_apply]

private structure WriteSideArgs where
  pb : ℕ
  dst : ℕ
  n : ℕ
  target : ℕ

private word_enc_structure encWriteSideArgs : WriteSideArgs where
  pb : wordWords, dst : wordWords, n : wordWords, target : wordWords

private instance : WordEncoding WriteSideArgs := ⟨4, encWriteSideArgs⟩

private def writeSideStep (q : WriteSideArgs × ℕ) : Memory.Prog ℕ := do
  let a := Prod.fst q
  let v := Prod.snd q
  let pv ← Memory.read (a.pb + v)
  let bit := if pv = a.target then 1 else 0
  Memory.write (a.dst + v) bit
  pure (v + 1)

private abbrev WriteSideStepSafe (w : ℕ) (q : WriteSideArgs × ℕ) (_ : Memory.State) : Prop :=
  Fits w (q.1.pb + q.2) ∧ Fits w (q.1.dst + q.2) ∧ Fits w (q.2 + 1) ∧ Fits w 1

private theorem writeSideStep_realizes :
    Realizes .exact writeSideStep (appendWords encWriteSideArgs wordWords) wordWords
      WriteSideStepSafe (fun _ _ => 0) := by
  unfold writeSideStep
  realize
  all_goals first | exact h.1 | exact h.2.1 | exact h.2.2.1 | exact h.2.2.2

private def writeSideProg (a : WriteSideArgs) : Memory.Prog ℕ :=
  iterate writeSideStep a a.n 0

private theorem writeSideProg_realizes :
    Realizes .exact writeSideProg encWriteSideArgs wordWords
      (fun w a s => iterationSafe writeSideStep WriteSideStepSafe w a a.n 0 s)
      (fun _ _ => 0) := by
  unfold writeSideProg
  realize [writeSideStep_realizes]
  exact h

private theorem writeSideProg_spec {w : ℕ} (a : WriteSideArgs) (s₀ : Memory.State)
    (hp_f : a.pb + a.n ≤ s₀.frontier) (hd_f : a.dst + a.n ≤ s₀.frontier)
    (hdisj : a.pb + a.n ≤ a.dst)
    (hfit_p : Fits w (a.pb + a.n)) (hfit_d : Fits w (a.dst + a.n)) (hfit1 : Fits w 1) :
    iterationSafe writeSideStep WriteSideStepSafe w a a.n 0 s₀ ∧
      Memory.FramedTriple w s₀ (writeSideProg a) (2 * a.n) (Set.Ico a.dst (a.dst + a.n))
        fun _ t => ∀ v < a.n,
          t.mem (a.dst + v) = if s₀.mem (a.pb + v) = a.target then 1 else 0 := by
  refine Memory.FramedTriple.iterate (fun k i t => i = k ∧
      ∀ v < k, t.mem (a.dst + v) = if s₀.mem (a.pb + v) = a.target then 1 else 0)
    ⟨rfl, by simp⟩ (fun k hk i t ⟨hi, hdone⟩ ⟨hfr, hframe⟩ => ?_) fun _ _ h _ => h.2
  subst i
  have hp := hframe (a.pb + k) (by omega) (by region_omega)
  refine ⟨⟨by region_omega, by region_omega, by region_omega, hfit1⟩, ?_⟩
  unfold writeSideStep
  framed_triple
  · split_ifs <;> [exact hfit1; exact fits_zero w]
  · refine ⟨rfl, Nat.forall_lt_succ_right.2 ⟨fun j hj => ?_, by simp [hp]⟩⟩
    simp [hj.ne, hdone j hj]

/-! ### Maximum adjacency search (`maPickMaxProg`, `maUpdateKeysProg`, `maOrderProg`) -/


private structure MAPickState where
  i : ℕ
  has : ℕ
  bestIdx : ℕ
  bestKey : ℕ

private word_enc_structure encMAPickState : MAPickState where
  i : wordWords, has : wordWords, bestIdx : wordWords, bestKey : wordWords

private instance : WordEncoding MAPickState := ⟨4, encMAPickState⟩

private def maPickStep (q : InitMAArgs × MAPickState) : Memory.Prog MAPickState := do
  let a := Prod.fst q
  let st := Prod.snd q
  let u ← Memory.read (a.ub + st.i)
  if u = 0 then do
    let k ← Memory.read (a.kb + st.i)
    if st.has = 0 then
      pure ⟨st.i + 1, 1, st.i, k⟩
    else if st.bestKey < k then
      pure ⟨st.i + 1, 1, st.i, k⟩
    else
      pure ⟨st.i + 1, st.has, st.bestIdx, st.bestKey⟩
  else
    pure ⟨st.i + 1, st.has, st.bestIdx, st.bestKey⟩

private abbrev MAPickStepSafe (w : ℕ) (q : InitMAArgs × MAPickState) (_ : Memory.State) : Prop :=
  Fits w (q.1.ub + q.2.i) ∧ Fits w (q.1.kb + q.2.i) ∧ Fits w (q.2.i + 1) ∧ Fits w 1

private theorem maPickStep_realizes :
    Realizes .exact maPickStep (appendWords encInitMAArgs encMAPickState) encMAPickState
      MAPickStepSafe (fun _ _ => 0) := by
  unfold maPickStep
  realize
  all_goals first | exact h.1 | exact h.2.1 | exact h.2.2.1 | exact h.2.2.2

private def maPickMaxProg (a : InitMAArgs) : Memory.Prog MAPickState :=
  iterate maPickStep a a.m ⟨0, 0, 0, 0⟩

private theorem maPickMaxProg_realizes :
    Realizes .exact maPickMaxProg encInitMAArgs encMAPickState
      (fun w a s => iterationSafe maPickStep MAPickStepSafe w a a.m ⟨0, 0, 0, 0⟩ s)
      (fun _ _ => 0) := by
  unfold maPickMaxProg
  realize [maPickStep_realizes]
  exact h

private theorem maPickMaxProg_spec {w : ℕ} (a : InitMAArgs)
    (used : Fin a.m → Bool) (key : Fin a.m → ℕ) (s₀ : Memory.State)
    (hk_f : a.kb + a.m ≤ s₀.frontier) (hu_f : a.ub + a.m ≤ s₀.frontier)
    (hfit_k : Fits w (a.kb + a.m)) (hfit_u : Fits w (a.ub + a.m)) (hfit1 : Fits w 1)
    (hkey : ∀ x : Fin a.m, s₀.mem (a.kb + x.1) = key x)
    (hused : ∀ x : Fin a.m, s₀.mem (a.ub + x.1) = if used x then 1 else 0)
    (hex : ∃ x : Fin a.m, used x = false) :
    iterationSafe maPickStep MAPickStepSafe w a a.m ⟨0, 0, 0, 0⟩ s₀ ∧
      Memory.FramedTriple w s₀ (maPickMaxProg a) (2 * a.m) ∅ fun res t => t = s₀ ∧
        ∃ v : Fin a.m, res.bestIdx = v.1 ∧ res.bestKey = key v ∧
          ((List.finRange a.m).filter fun x => !used x).argmax key = some v := by
  refine Memory.FramedTriple.iterate (fun k st t => t = s₀ ∧ st.i = k ∧
      ((st.has = 0 ∧ ∀ x : Fin a.m, x.1 < k → used x = true) ∨
       (st.has = 1 ∧ ∃ b : Fin a.m, b.1 < k ∧ st.bestIdx = b.1 ∧ st.bestKey = key b ∧
         used b = false ∧
         (∀ x : Fin a.m, x.1 < k → used x = false → key x ≤ key b) ∧
         (∀ x : Fin a.m, x.1 < b.1 → used x = false → key x < key b))))
    ⟨rfl, rfl, Or.inl ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
    (fun k hk st s ⟨hs, hst_i, hinv⟩ _ => ?_) fun res _ ⟨ht, _, hinv⟩ _ => ⟨ht, ?_⟩
  · subst s
    let kFin : Fin a.m := ⟨k, hk⟩
    have hu_k : s₀.mem (a.ub + st.i) = if used kFin then 1 else 0 := hst_i ▸ hused kFin
    have hk_k : s₀.mem (a.kb + st.i) = key kFin := hst_i ▸ hkey kFin
    have hlt_k : ∀ x : Fin a.m, x.1 < k + 1 → x.1 < k ∨ x = kFin := fun x hx =>
      (Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hx)).imp_right Fin.ext
    refine ⟨⟨by region_omega, by region_omega, by region_omega, hfit1⟩, ?_⟩
    unfold maPickStep
    framed_triple
    · rename_i hu0 hh
      have huk : used kFin = false := by cases h : used kFin <;> simp_all
      rcases hinv with ⟨_, hall⟩ | ⟨hhas, _⟩
      · refine ⟨rfl, by dsimp only; omega, Or.inr ⟨rfl, kFin, Nat.lt_succ_self k, hst_i, hk_k,
          huk, fun x hx hux => ?_, fun x hx hux => absurd (hall x hx) (by simp [hux])⟩⟩
        rcases hlt_k x hx with hx | rfl
        · exact absurd (hall x hx) (by simp [hux])
        · exact le_rfl
      · omega
    · rename_i hu0 hh hlt
      have huk : used kFin = false := by cases h : used kFin <;> simp_all
      rcases hinv with ⟨hhas, _⟩ | ⟨_, b, _, _, hbk_eq, _, hmax, _⟩
      · omega
      · rw [hbk_eq, hk_k] at hlt
        refine ⟨rfl, by dsimp only; omega, Or.inr ⟨rfl, kFin, Nat.lt_succ_self k, hst_i, hk_k,
          huk, fun x hx hux => ?_, fun x hx hux => (hmax x hx hux).trans_lt hlt⟩⟩
        rcases hlt_k x hx with hx | rfl
        · exact (hmax x hx hux).trans hlt.le
        · exact le_rfl
    · rename_i hu0 hh hlt
      rcases hinv with ⟨hhas, _⟩ | ⟨hhas, b, hbk, hbi, hbk_eq, hub, hmax, hfirst⟩
      · omega
      · rw [hbk_eq, hk_k] at hlt
        refine ⟨rfl, by dsimp only; omega, Or.inr ⟨hhas, b, Nat.lt_succ_of_lt hbk, hbi, hbk_eq,
          hub, fun x hx hux => ?_, hfirst⟩⟩
        rcases hlt_k x hx with hx | rfl
        · exact hmax x hx hux
        · omega
    · rename_i hu
      have huk : used kFin = true := by cases h : used kFin <;> simp_all
      refine ⟨rfl, by dsimp only; omega, hinv.imp (fun ⟨hhas, hall⟩ => ⟨hhas, fun x hx => ?_⟩)
        fun ⟨hhas, b, hbk, hbi, hbk_eq, hub, hmax, hfirst⟩ =>
          ⟨hhas, b, Nat.lt_succ_of_lt hbk, hbi, hbk_eq, hub, fun x hx hux => ?_, hfirst⟩⟩
      · rcases hlt_k x hx with hx | rfl
        · exact hall x hx
        · exact huk
      · rcases hlt_k x hx with hx | rfl
        · exact hmax x hx hux
        · simp [huk] at hux
  · rcases hinv with ⟨_, hall⟩ | ⟨_, b, _, hbi, hbk, hub, hmax, hfirst⟩
    · obtain ⟨x, hx⟩ := hex
      exact absurd (hall x x.isLt) (by simp [hx])
    · exact ⟨b, hbi, hbk, argmax_filter_finRange_eq used key b hub
        (fun x hux => hmax x x.isLt hux) (fun x hux hlt => hfirst x hlt hux)⟩

private structure MAUpdArgs where
  mb : ℕ
  kb : ℕ
  ub : ℕ
  stride : ℕ
  m : ℕ
  v : ℕ

private word_enc_structure encMAUpdArgs : MAUpdArgs where
  mb : wordWords, kb : wordWords, ub : wordWords, stride : wordWords, m : wordWords, v : wordWords

private instance : WordEncoding MAUpdArgs := ⟨6, encMAUpdArgs⟩

private def maUpdateStep (q : MAUpdArgs × ℕ) : Memory.Prog ℕ := do
  let a := Prod.fst q
  let y := Prod.snd q
  let u ← Memory.read (a.ub + y)
  if u = 0 then do
    let ky ← Memory.read (a.kb + y)
    let w ← Memory.read (a.mb + a.v * a.stride + y)
    Memory.write (a.kb + y) (ky + w)
    pure (y + 1)
  else
    pure (y + 1)

private abbrev MAUpdStepSafe (w : ℕ) (q : MAUpdArgs × ℕ) (s : Memory.State) : Prop :=
  Fits w (q.1.ub + q.2) ∧ Fits w (q.1.kb + q.2) ∧ Fits w (q.1.mb + q.1.v * q.1.stride + q.2) ∧
    Fits w (q.2 + 1) ∧
    (s.mem (q.1.ub + q.2) = 0 →
      Fits w (s.mem (q.1.kb + q.2) + s.mem (q.1.mb + q.1.v * q.1.stride + q.2)))

private theorem maUpdateStep_realizes :
    Realizes .exact maUpdateStep (appendWords encMAUpdArgs wordWords) wordWords
      MAUpdStepSafe (fun _ _ => 0) := by
  unfold maUpdateStep
  realize
  all_goals first
    | exact h.1 | exact h.2.1 | exact h.2.2.1 | exact h.2.2.2.1
    | exact h.2.2.2.2 ‹_›

private def maUpdateKeysProg (a : MAUpdArgs) : Memory.Prog ℕ :=
  iterate maUpdateStep a a.m 0

private theorem maUpdateKeysProg_realizes :
    Realizes .exact maUpdateKeysProg encMAUpdArgs wordWords
      (fun w a s => iterationSafe maUpdateStep MAUpdStepSafe w a a.m 0 s)
      (fun _ _ => 0) := by
  unfold maUpdateKeysProg
  realize [maUpdateStep_realizes]
  exact h

private theorem maUpdateKeysProg_spec {w : ℕ} (a : MAUpdArgs)
    {W : Fin a.m → Fin a.m → ℕ} (hW : IsMultigraph W)
    (v : Fin a.m) (hv : a.v = v.1) (hm_str : a.m ≤ a.stride)
    (A : Finset (Fin a.m)) (hvA : v ∉ A) (used : Fin a.m → Bool)
    (s₀ : Memory.State)
    (hm_f : a.mb + a.m * a.stride ≤ s₀.frontier)
    (hk_f : a.kb + a.m ≤ s₀.frontier) (hu_f : a.ub + a.m ≤ s₀.frontier)
    (hdisj_mk : a.mb + a.m * a.stride ≤ a.kb) (hdisj_ku : a.kb + a.m ≤ a.ub)
    (hfit_m : Fits w (a.mb + a.m * a.stride))
    (hfit_k : Fits w (a.kb + a.m)) (hfit_u : Fits w (a.ub + a.m))
    (hfit_tot : Fits w (totalDoubledWeight W))
    (hmat : ∀ i j : Fin a.m, s₀.mem (a.mb + i.1 * a.stride + j.1) = W i j)
    (hkey : ∀ y : Fin a.m, used y = false → s₀.mem (a.kb + y.1) = attachWeight W A y)
    (hused : ∀ y : Fin a.m, s₀.mem (a.ub + y.1) = if used y then 1 else 0) :
    iterationSafe maUpdateStep MAUpdStepSafe w a a.m 0 s₀ ∧
      Memory.FramedTriple w s₀ (maUpdateKeysProg a) (4 * a.m) (Set.Ico a.kb (a.kb + a.m))
        fun _ t => ∀ y : Fin a.m, used y = false →
          t.mem (a.kb + y.1) = attachWeight W (insert v A) y := by
  refine Memory.FramedTriple.iterate (fun k i s => i = k ∧ ∀ y : Fin a.m, used y = false →
      s.mem (a.kb + y.1) = if y.1 < k then attachWeight W (insert v A) y else attachWeight W A y)
    ⟨rfl, fun y hy => by simp [hkey y hy]⟩ (fun k hk i s ⟨hi, hkeys⟩ ⟨hfr, hframe⟩ => ?_)
    fun _ _ h _ y hy => by simpa [y.isLt] using h.2 y hy
  subst i
  let yFin : Fin a.m := ⟨k, hk⟩
  have hcell : v.1 * a.stride + k < a.m * a.stride := cell_lt_mul hm_str v.isLt hk
  have hu_k : s.mem (a.ub + k) = if used yFin then 1 else 0 := by
    rw [hframe (a.ub + k) (by omega) (by region_omega), hused yFin]
  have hm_k : s.mem (a.mb + a.v * a.stride + k) = W v yFin := by
    rw [hv, hframe (a.mb + v.1 * a.stride + k) (by omega) (by region_omega), hmat v yFin]
  have hsum_fit : s.mem (a.ub + k) = 0 →
      Fits w (s.mem (a.kb + k) + s.mem (a.mb + a.v * a.stride + k)) := by
    intro hu0
    have huy : used yFin = false := by
      rw [hu_k] at hu0
      cases hy : used yFin <;> simp [hy] at hu0 ⊢
    have hky : s.mem (a.kb + k) = attachWeight W A yFin := by
      simpa [yFin] using hkeys yFin huy
    rw [hky, hm_k, add_comm, ← attachWeight_insert W hvA]
    exact hfit_tot.of_le (attachWeight_le_totalDoubledWeight hW (insert v A) yFin)
  have hkeep : ∀ y : Fin a.m, used y = false → y.1 ≠ k →
      (if y.1 < k then attachWeight W (insert v A) y else attachWeight W A y) =
        if y.1 < k + 1 then attachWeight W (insert v A) y else attachWeight W A y := by
    intro y _ hne
    by_cases hlt : y.1 < k
    · simp [hlt, Nat.lt_succ_of_lt hlt]
    · simp [hlt, show ¬(y.1 < k + 1) by omega]
  refine ⟨⟨by region_omega, by region_omega, by rw [hv]; region_omega, by region_omega,
    hsum_fit⟩, ?_⟩
  have hmb : a.mb + a.v * a.stride + k < s.frontier := by rw [hv]; omega
  unfold maUpdateStep
  framed_triple
  · rename_i hu0
    have huy : used yFin = false := by cases hy : used yFin <;> simp_all
    refine ⟨rfl, fun y hy => ?_⟩
    dsimp only
    by_cases heq : y.1 = k
    · obtain rfl : y = yFin := Fin.ext heq
      have hky : s.mem (a.kb + k) = attachWeight W A yFin := by simpa [yFin] using hkeys yFin huy
      rw [Function.update_self, hky, hm_k, add_comm, ← attachWeight_insert W hvA]
      simp [yFin]
    · rw [Function.update_of_ne (by omega)]
      exact (hkeys y hy).trans (hkeep y hy heq)
  · rename_i hu
    refine ⟨rfl, fun y hy => (hkeys y hy).trans (hkeep y hy fun h => ?_)⟩
    obtain rfl : y = yFin := Fin.ext h
    simp [hu_k, hy] at hu

private structure MAOrderArgs where
  mb : ℕ
  kb : ℕ
  ub : ℕ
  stride : ℕ
  m : ℕ

private word_enc_structure encMAOrderArgs : MAOrderArgs where
  mb : wordWords, kb : wordWords, ub : wordWords, stride : wordWords, m : wordWords

private instance : WordEncoding MAOrderArgs := ⟨5, encMAOrderArgs⟩

private structure MAOrderState where
  prev : ℕ
  last : ℕ
  lastKey : ℕ

private word_enc_structure encMAOrderState : MAOrderState where
  prev : wordWords, last : wordWords, lastKey : wordWords

private instance : WordEncoding MAOrderState := ⟨3, encMAOrderState⟩

private def maOrderStep (q : MAOrderArgs × MAOrderState) : Memory.Prog MAOrderState := do
  let a := Prod.fst q
  let st := Prod.snd q
  let _ ← Memory.read 0
  let picked ← maPickMaxProg ⟨a.kb, a.ub, a.m⟩
  Memory.write (a.ub + picked.bestIdx) 1
  let _ ← maUpdateKeysProg ⟨a.mb, a.kb, a.ub, a.stride, a.m, picked.bestIdx⟩
  pure ⟨st.last, picked.bestIdx, picked.bestKey⟩

private abbrev MAOrderStepSafe (w : ℕ) (q : MAOrderArgs × MAOrderState) (s : Memory.State) :
    Prop :=
  let a := Prod.fst q
  let pickA : InitMAArgs := ⟨a.kb, a.ub, a.m⟩
  let picked := (Memory.spec 0).clientResult s (maPickMaxProg pickA)
  let s1 := (Memory.spec 0).clientState s (maPickMaxProg pickA)
  let s2 : Memory.State := ⟨Function.update s1.mem (a.ub + picked.bestIdx) 1, s1.frontier⟩
  iterationSafe maPickStep MAPickStepSafe w pickA a.m ⟨0, 0, 0, 0⟩ s ∧
    Fits w (a.ub + picked.bestIdx) ∧ Fits w 1 ∧
    iterationSafe maUpdateStep MAUpdStepSafe w
      ⟨a.mb, a.kb, a.ub, a.stride, a.m, picked.bestIdx⟩ a.m 0 s2

private theorem maOrderStep_realizes :
    Realizes .exact maOrderStep (appendWords encMAOrderArgs encMAOrderState) encMAOrderState
      MAOrderStepSafe (fun _ _ => 0) := by
  unfold maOrderStep
  realize [maPickMaxProg_realizes, maUpdateKeysProg_realizes]
  all_goals first | exact h.1 | exact h.2.1 | exact h.2.2.1 | exact h.2.2.2

private def maOrderProg (a : MAOrderArgs) : Memory.Prog MAOrderState :=
  iterate maOrderStep a a.m ⟨0, 0, 0⟩

private theorem maOrderProg_realizes :
    Realizes .exact maOrderProg encMAOrderArgs encMAOrderState
      (fun w a s => iterationSafe maOrderStep MAOrderStepSafe w a a.m ⟨0, 0, 0⟩ s)
      (fun _ _ => 0) := by
  unfold maOrderProg
  realize [maOrderStep_realizes]
  exact h

private theorem maOrderProg_spec {w : ℕ} (a : MAOrderArgs)
    {W : Fin a.m → Fin a.m → ℕ} (hm2 : 2 ≤ a.m) (hW : IsMultigraph W)
    (hm_str : a.m ≤ a.stride) (s₀ : Memory.State)
    (hm_f : a.mb + a.m * a.stride ≤ s₀.frontier)
    (hk_f : a.kb + a.m ≤ s₀.frontier) (hu_f : a.ub + a.m ≤ s₀.frontier)
    (hdisj_mk : a.mb + a.m * a.stride ≤ a.kb) (hdisj_ku : a.kb + a.m ≤ a.ub)
    (hfit_m : Fits w (a.mb + a.m * a.stride))
    (hfit_k : Fits w (a.kb + a.m)) (hfit_u : Fits w (a.ub + a.m))
    (hfit1 : Fits w 1) (hfit_tot : Fits w (totalDoubledWeight W))
    (hmat : ∀ i j : Fin a.m, s₀.mem (a.mb + i.1 * a.stride + j.1) = W i j)
    (hinit : ∀ i < a.m, s₀.mem (a.kb + i) = 0 ∧ s₀.mem (a.ub + i) = 0) :
    iterationSafe maOrderStep MAOrderStepSafe w a a.m ⟨0, 0, 0⟩ s₀ ∧
      Memory.FramedTriple w s₀ (maOrderProg a) ((6 * a.m + 2) * a.m)
        (Set.Ico a.kb (a.kb + a.m) ∪ Set.Ico a.ub (a.ub + a.m)) fun res _ =>
          ∃ (p : List (Fin a.m)) (s t : Fin a.m),
            maOrder W = p ++ [s, t] ∧ s ≠ t ∧
            res.prev = s.1 ∧ res.last = t.1 ∧ res.lastKey = rowDeg W t := by
  refine Memory.FramedTriple.iterate
    (fun k st s =>
        ∃ (pref : List (Fin a.m)) (A : Finset (Fin a.m)) (used : Fin a.m → Bool),
          pref.length = k ∧ pref.Nodup ∧ (∀ x, x ∈ pref ↔ x ∈ A) ∧ A.card = k ∧
          (∀ x : Fin a.m, used x = true ↔ x ∈ A) ∧
          (∀ y : Fin a.m, used y = false → s.mem (a.kb + y.1) = attachWeight W A y) ∧
          (∀ y : Fin a.m, s.mem (a.ub + y.1) = if used y then 1 else 0) ∧
          maOrder W =
            pref ++ maSearch W (a.m - k) (attachWeight W A)
              ((List.finRange a.m).filter fun x => !used x) ∧
          (∀ (q : List (Fin a.m)) (u : Fin a.m), pref = q ++ [u] → st.last = u.1) ∧
          (∀ (q : List (Fin a.m)) (u v : Fin a.m), pref = q ++ [u, v] →
            st.prev = u.1 ∧ st.last = v.1) ∧
          (k = a.m → ∀ (q : List (Fin a.m)) (u : Fin a.m), pref = q ++ [u] →
            st.lastKey = rowDeg W u))
    ⟨[], ∅, fun _ => false, rfl, List.nodup_nil, by simp, rfl, by simp,
      fun y _ => by simpa [attachWeight_empty] using (hinit y.1 y.isLt).1,
      fun y => by simpa using (hinit y.1 y.isLt).2,
      by
        have hfn : attachWeight W ∅ = fun _ => 0 := funext (attachWeight_empty W)
        simp [maOrder, hfn],
      fun q u h => by simpa using congrArg List.length h,
      fun q u v h => by simpa using congrArg List.length h,
      fun h0 => by omega⟩
    (fun k hk st s ⟨pref, A, used, hlen, hnd, hmemA, hcard, husedA,
        hkeys, hused_mem, hord_eq, hlast_eq, hprev_eq, _⟩ ⟨hfr, hframe⟩ => ?_)
    fun res _ ⟨pref, A, used, hlen, hnd, _, _, _, _, _, hord_eq, _, hprev_eq, hlastKey_eq⟩ _ => ?_
  · have hex : ∃ x : Fin a.m, used x = false := by
      by_contra hnone
      simp only [not_exists, Bool.not_eq_false] at hnone
      have huniv : A = Finset.univ :=
        Finset.eq_univ_iff_forall.mpr fun x => (husedA x).mp (hnone x)
      have hc : A.card = a.m := by rw [huniv, Finset.card_univ, Fintype.card_fin]
      omega
    let keyFn : Fin a.m → ℕ := fun x => s.mem (a.kb + x.1)
    have hkey_agree : ∀ x : Fin a.m, used x = false → keyFn x = attachWeight W A x := hkeys
    obtain ⟨hsafe_p, hpick⟩ := maPickMaxProg_spec ⟨a.kb, a.ub, a.m⟩ used keyFn s
      (by region_omega) (by region_omega) hfit_k hfit_u hfit1 (fun _ => rfl) hused_mem hex
    obtain ⟨-, -, -, hs_p, v, hv_idx, hv_key, harg_key⟩ := framedTriple_iff_realization.mp hpick
    have hv_unused : used v = false := by
      have hv_mem := List.argmax_mem harg_key
      simp only [List.mem_filter, List.mem_finRange, true_and, Bool.not_eq_true'] at hv_mem
      exact hv_mem
    have hvA : v ∉ A := fun h => by
      have := (husedA v).mpr h
      simp [hv_unused] at this
    have harg_att :
        ((List.finRange a.m).filter fun x => !used x).argmax (attachWeight W A) = some v := by
      rw [List.argmax_eq_some_iff] at harg_key ⊢
      obtain ⟨hm1, hm2, hm3⟩ := harg_key
      refine ⟨hm1, fun y hy => ?_, fun y hy hle => ?_⟩
      · have huy : used y = false := by
          simp only [List.mem_filter, List.mem_finRange, true_and, Bool.not_eq_true'] at hy
          exact hy
        rw [← hkey_agree y huy, ← hkey_agree v hv_unused]
        exact hm2 y hy
      · have huy : used y = false := by
          simp only [List.mem_filter, List.mem_finRange, true_and, Bool.not_eq_true'] at hy
          exact hy
        rw [← hkey_agree y huy, ← hkey_agree v hv_unused] at hle
        exact hm3 y hy hle
    let used' : Fin a.m → Bool := fun x => if x = v then true else used x
    have hused'A : ∀ x : Fin a.m, used' x = true ↔ x ∈ insert v A := by
      intro x
      dsimp only [used']
      by_cases hxv : x = v
      · subst hxv; simp
      · simp [hxv, husedA x]
    let s2 : Memory.State := ⟨Function.update s.mem (a.ub + v.1) 1, s.frontier⟩
    have hs2_used : ∀ y : Fin a.m, s2.mem (a.ub + y.1) = if used' y then 1 else 0 := by
      intro y
      dsimp only [s2, used']
      by_cases hyv : y = v
      · subst hyv; simp
      · rw [Function.update_of_ne (by omega)]
        simp [hyv, hused_mem y]
    have hs2_mat : ∀ i j : Fin a.m, s2.mem (a.mb + i.1 * a.stride + j.1) = W i j := by
      intro i j
      have hcell : i.1 * a.stride + j.1 < a.m * a.stride := cell_lt_mul hm_str i.isLt j.isLt
      dsimp only [s2]
      rw [Function.update_of_ne (by omega), hframe _ (by omega) (by region_omega)]
      exact hmat i j
    have hs2_key : ∀ y : Fin a.m, used' y = false → s2.mem (a.kb + y.1) = attachWeight W A y := by
      intro y hy
      dsimp only [s2, used'] at hy ⊢
      have hyv : y ≠ v := fun h => by subst h; simp at hy
      simp only [hyv, ↓reduceIte] at hy
      rw [Function.update_of_ne (by omega)]
      exact hkeys y hy
    obtain ⟨hsafe_u, hupd⟩ := maUpdateKeysProg_spec ⟨a.mb, a.kb, a.ub, a.stride, a.m, v.1⟩ hW v
      rfl hm_str A hvA used' s2 (by dsimp only [s2]; omega) (by dsimp only [s2]; omega)
      (by dsimp only [s2]; omega) hdisj_mk hdisj_ku hfit_m hfit_k hfit_u hfit_tot hs2_mat
      hs2_key hs2_used
    have hv_lt : v.1 < a.m := v.isLt
    refine ⟨by dsimp only [MAOrderStepSafe]; rw [hs_p, hv_idx]
               exact ⟨hsafe_p, by region_omega, hfit1, hsafe_u⟩, ?_⟩
    unfold maOrderStep
    dsimp only
    refine (Memory.FramedTriple.read_bind (by omega) (Memory.FramedTriple.seq
      (c₂ := 4 * a.m + 1) hpick (Set.empty_subset _) ?_)).mono (by dsimp only; omega) fun _ _ => id
    rw [hs_p, hv_idx, hv_key]
    refine Memory.FramedTriple.write_bind_of_mem (by omega) hfit1 (by region_omega)
      (Memory.FramedTriple.call hupd Set.subset_union_left fun _ t hpost ⟨_, hmod⟩ =>
        Memory.FramedTriple.pure (c := 0) ?_)
    refine ⟨pref ++ [v], insert v A, used', by simp [hlen], ?_, ?_, ?_, hused'A,
      hpost, fun y => ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hnd, List.nodup_singleton v, fun x hx y hy => ?_⟩
      simp only [List.mem_singleton] at hy
      subst hy
      intro heq
      subst heq
      exact hvA ((hmemA x).mp hx)
    · intro x
      simp only [List.mem_append, List.mem_singleton, Finset.mem_insert, hmemA, or_comm]
    · rw [Finset.card_insert_of_notMem hvA, hcard]
    · rw [hmod (a.ub + y.1) (by dsimp only [s2]; omega) (by region_omega)]
      exact hs2_used y
    · have hsub : a.m - k = (a.m - (k + 1)) + 1 := by omega
      rw [hord_eq, hsub, maSearch, harg_att]
      simp only [List.append_assoc, List.singleton_append]
      congr 2
      have hfn : (fun y => attachWeight W A y + W v y) = attachWeight W (insert v A) := by
        funext y
        rw [attachWeight_insert W hvA, add_comm]
      rw [hfn, erase_filter_finRange]
      congr 1
      refine List.filter_congr fun x _ => ?_
      dsimp only [used']
      by_cases hxv : x = v <;> simp [hxv]
    · intro q u hq
      have hu : u = v := by
        have := List.append_inj_right' hq rfl
        simpa using this.symm
      subst u; rfl
    · intro q u x hq
      have hq' : pref ++ [v] = (q ++ [u]) ++ [x] := by simpa [List.append_assoc] using hq
      have hp1 : pref = q ++ [u] := List.append_inj_left' hq' rfl
      have hx : x = v := by
        have := List.append_inj_right' hq' rfl
        simpa using this.symm
      subst x
      exact ⟨hlast_eq q u hp1, rfl⟩
    · intro hkm q u hq
      have hu : u = v := by
        have := List.append_inj_right' hq rfl
        simpa using this.symm
      subst u
      have hA_eq : A = Finset.univ.erase v := by
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          exact Finset.mem_erase.mpr ⟨fun h => hvA (h ▸ hx), Finset.mem_univ x⟩
        · rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
          dsimp only; rw [hcard]; omega
      rw [hkey_agree v hv_unused, hA_eq, attachWeight_erase_self hW v]
  · have hord_pref : maOrder W = pref := by
      simpa [Nat.sub_self, maSearch] using hord_eq
    rcases hrev : pref.reverse with _ | ⟨t, _ | ⟨s, q⟩⟩
    · have := congrArg List.length hrev
      simp [hlen] at this; omega
    · have := congrArg List.length hrev
      simp [hlen] at this; omega
    · have hpref_eq : pref = q.reverse ++ [s, t] := by
        rw [← List.reverse_reverse pref, hrev]; simp
      have hst : s ≠ t := by
        rw [hpref_eq, List.nodup_append] at hnd
        simpa using hnd.2.1
      obtain ⟨hpr, hla⟩ := hprev_eq q.reverse s t hpref_eq
      have hlk := hlastKey_eq rfl (q.reverse ++ [s]) t (by simpa [List.append_assoc] using hpref_eq)
      exact ⟨q.reverse, s, t, hord_pref.trans hpref_eq, hst, hpr, hla, hlk⟩

/-! ### In-place matrix contraction (`mergeRowColProg`, `compactRowColProg`, `contractPartProg`) -/

private structure MergeArgs where
  mb : ℕ
  stride : ℕ
  m : ℕ
  s : ℕ
  t : ℕ

private word_enc_structure encMergeArgs : MergeArgs where
  mb : wordWords, stride : wordWords, m : wordWords, s : wordWords, t : wordWords

private instance : WordEncoding MergeArgs := ⟨5, encMergeArgs⟩

private def mergeStep (q : MergeArgs × ℕ) : Memory.Prog ℕ := do
  let a := Prod.fst q
  let i := Prod.snd q
  let x ← Memory.read (a.mb + a.s * a.stride + i)
  let y ← Memory.read (a.mb + a.t * a.stride + i)
  let sum := if i = a.s then 0 else if i = a.t then 0 else x + y
  Memory.write (a.mb + a.s * a.stride + i) sum
  Memory.write (a.mb + i * a.stride + a.s) sum
  Memory.write (a.mb + a.t * a.stride + i) 0
  Memory.write (a.mb + i * a.stride + a.t) 0
  pure (i + 1)

private abbrev MergeStepSafe (w : ℕ) (q : MergeArgs × ℕ) (s : Memory.State) : Prop :=
  let a := Prod.fst q
  let i := Prod.snd q
  Fits w (a.mb + a.s * a.stride + i) ∧ Fits w (a.mb + a.t * a.stride + i) ∧
    Fits w (a.mb + i * a.stride + a.s) ∧ Fits w (a.mb + i * a.stride + a.t) ∧
    Fits w (i + 1) ∧
    (i ≠ a.s → i ≠ a.t →
      Fits w (s.mem (a.mb + a.s * a.stride + i) + s.mem (a.mb + a.t * a.stride + i)))

private theorem mergeStep_realizes :
    Realizes .exact mergeStep (appendWords encMergeArgs wordWords) wordWords
      MergeStepSafe (fun _ _ => 0) := by
  unfold mergeStep
  realize
  all_goals first
    | exact h.1 | exact h.2.1 | exact h.2.2.1 | exact h.2.2.2.1 | exact h.2.2.2.2.1
    | exact h.2.2.2.2.2 ‹_› ‹_›

private def mergeRowColProg (a : MergeArgs) : Memory.Prog ℕ :=
  iterate mergeStep a a.m 0

private theorem mergeRowColProg_realizes :
    Realizes .exact mergeRowColProg encMergeArgs wordWords
      (fun w a s => iterationSafe mergeStep MergeStepSafe w a a.m 0 s)
      (fun _ _ => 0) := by
  unfold mergeRowColProg
  realize [mergeStep_realizes]
  exact h

private theorem mergeRowColProg_spec {w : ℕ} (a : MergeArgs)
    {W : Fin a.m → Fin a.m → ℕ} (hW : IsMultigraph W)
    {sv tv : Fin a.m} (hst : sv ≠ tv) (hs : a.s = sv.1) (ht : a.t = tv.1)
    (hm_str : a.m ≤ a.stride) (s₀ : Memory.State)
    (hm_f : a.mb + a.m * a.stride ≤ s₀.frontier)
    (hfit_m : Fits w (a.mb + a.m * a.stride))
    (hfit_tot : Fits w (totalDoubledWeight W))
    (hmat : ∀ i j : Fin a.m, s₀.mem (a.mb + i.1 * a.stride + j.1) = W i j) :
    iterationSafe mergeStep MergeStepSafe w a a.m 0 s₀ ∧
      Memory.FramedTriple w s₀ (mergeRowColProg a) (6 * a.m)
        (Set.Ico a.mb (a.mb + a.m * a.stride)) fun _ t => ∀ i j : Fin a.m,
          t.mem (a.mb + i.1 * a.stride + j.1) = mergePair W sv tv i j := by
  have hcell := fun x y (hx : x < a.m) (hy : y < a.m) => cell_lt_mul hm_str hx hy
  refine Memory.FramedTriple.iterate (fun k idx s => idx = k ∧ ∀ i j : Fin a.m,
      s.mem (a.mb + i.1 * a.stride + j.1) =
        if (i = sv ∨ i = tv) ∧ j.1 < k then mergePair W sv tv i j
        else if (j = sv ∨ j = tv) ∧ i.1 < k then mergePair W sv tv i j
        else W i j)
    ⟨rfl, fun i j => by simp [hmat]⟩ (fun k hk idx s ⟨hidx, hcur⟩ ⟨hfr, _⟩ => ?_)
    fun _ _ h _ i j => (h.2 i j).trans ?_
  · subst idx
    let kFin : Fin a.m := ⟨k, hk⟩
    have hcs := hcell sv.1 k sv.isLt hk
    have hct := hcell tv.1 k tv.isLt hk
    have hks := hcell k sv.1 hk sv.isLt
    have hkt := hcell k tv.1 hk tv.isLt
    have hread : ∀ x : Fin a.m, k ≠ sv.1 → k ≠ tv.1 →
        s.mem (a.mb + x.1 * a.stride + k) = W x kFin := fun x h1 h2 => by
      have hne_s : kFin ≠ sv := fun h => h1 (congrArg Fin.val h)
      have hne_t : kFin ≠ tv := fun h => h2 (congrArg Fin.val h)
      rw [hcur x kFin]
      simp [hne_s, hne_t, kFin]
    have hsum_fit : k ≠ sv.1 → k ≠ tv.1 →
        Fits w (s.mem (a.mb + sv.1 * a.stride + k) + s.mem (a.mb + tv.1 * a.stride + k)) :=
        fun h1 h2 => by
      rw [hread sv h1 h2, hread tv h1 h2]
      exact hfit_tot.of_le (add_entry_le_totalDoubledWeight hst kFin)
    have hval_fit : Fits w (if k = sv.1 then 0 else if k = tv.1 then 0 else
        s.mem (a.mb + sv.1 * a.stride + k) + s.mem (a.mb + tv.1 * a.stride + k)) := by
      split_ifs with h1 h2
      · exact fits_zero w
      · exact fits_zero w
      · exact hsum_fit h1 h2
    refine ⟨by dsimp only [MergeStepSafe]; rw [hs, ht]; exact ⟨by region_omega, by region_omega,
      by region_omega, by region_omega, by region_omega, hsum_fit⟩, ?_⟩
    unfold mergeStep
    dsimp only
    rw [hs, ht]
    framed_triple
    refine ⟨rfl, fun i j => ?_⟩
    dsimp only
    by_cases hit : i = tv ∧ j = kFin
    · rcases hit with ⟨hi_eq, hj_eq⟩
      subst i; subst j
      by_cases htk : tv.1 = k
      · obtain rfl : tv = kFin := Fin.ext htk
        simp [kFin, mergePair]
      · rw [Function.update_of_ne
          (matAddr_ne hm_str tv.isLt hk hk tv.isLt fun h => htk h.1), Function.update_self]
        simp [kFin, mergePair]
    · by_cases hjt : i = kFin ∧ j = tv
      · rcases hjt with ⟨hi_eq, hj_eq⟩
        subst i; subst j
        rw [Function.update_self]
        simp [kFin, mergePair]
      · rw [Function.update_of_ne (matAddr_ne hm_str i.isLt j.isLt hk tv.isLt
            fun h => hjt ⟨Fin.ext h.1, Fin.ext h.2⟩),
          Function.update_of_ne (matAddr_ne hm_str i.isLt j.isLt tv.isLt hk
            fun h => hit ⟨Fin.ext h.1, Fin.ext h.2⟩)]
        by_cases his : i = sv ∧ j = kFin
        · rcases his with ⟨hi_eq, hj_eq⟩
          subst i; subst j
          by_cases hsk : sv.1 = k
          · obtain rfl : sv = kFin := Fin.ext hsk
            simp [kFin, mergePair]
          · rw [Function.update_of_ne
              (matAddr_ne hm_str sv.isLt hk hk sv.isLt fun h => hsk h.1), Function.update_self]
            have hne_sv : kFin ≠ sv := fun h => hsk (congrArg Fin.val h).symm
            by_cases htk : k = tv.1
            · obtain rfl : kFin = tv := Fin.ext htk
              simp [kFin, mergePair]
            · have hne_tv : kFin ≠ tv := fun h => htk (congrArg Fin.val h)
              rw [hread sv (Ne.symm hsk) htk, hread tv (Ne.symm hsk) htk]
              simp [kFin, Ne.symm hsk, htk, mergePair, hne_sv.symm, hne_tv, hst]
        · by_cases hjs : i = kFin ∧ j = sv
          · rcases hjs with ⟨hi_eq, hj_eq⟩
            subst i; subst j
            rw [Function.update_self]
            by_cases hsk : k = sv.1
            · obtain rfl : kFin = sv := Fin.ext hsk
              simp [kFin, mergePair]
            · by_cases htk : k = tv.1
              · obtain rfl : kFin = tv := Fin.ext htk
                simp [kFin, mergePair]
              · have hne_sv : kFin ≠ sv := fun h => hsk (congrArg Fin.val h)
                have hne_tv : kFin ≠ tv := fun h => htk (congrArg Fin.val h)
                rw [hread sv hsk htk, hread tv hsk htk]
                simp [kFin, hsk, htk, mergePair, hne_sv, hne_tv, hst, hW.1 sv kFin, hW.1 tv kFin]
          · rw [Function.update_of_ne (matAddr_ne hm_str i.isLt j.isLt hk sv.isLt
                fun h => hjs ⟨Fin.ext h.1, Fin.ext h.2⟩),
              Function.update_of_ne (matAddr_ne hm_str i.isLt j.isLt sv.isLt hk
                fun h => his ⟨Fin.ext h.1, Fin.ext h.2⟩), hcur i j]
            have h1 : (i = sv ∨ i = tv) → j.1 ≠ k := by
              rintro (rfl | rfl) hj
              · exact his ⟨rfl, Fin.ext hj⟩
              · exact hit ⟨rfl, Fin.ext hj⟩
            have h2 : (j = sv ∨ j = tv) → i.1 ≠ k := by
              rintro (rfl | rfl) hi
              · exact hjs ⟨Fin.ext hi, rfl⟩
              · exact hjt ⟨Fin.ext hi, rfl⟩
            simp only [and_lt_succ_iff h1, and_lt_succ_iff h2]
  · simp only [i.isLt, j.isLt, and_true]
    split_ifs with h1 h2
    · rfl
    · rfl
    · unfold mergePair
      by_cases hij : i = j
      · subst hij; simp [hW.2 i]
      · simp only [not_or] at h1 h2
        simp [hij, h1.1, h1.2, h2.1, h2.2]

private structure CompactArgs where
  mb : ℕ
  stride : ℕ
  lastIdx : ℕ
  t : ℕ

private word_enc_structure encCompactArgs : CompactArgs where
  mb : wordWords, stride : wordWords, lastIdx : wordWords, t : wordWords

private instance : WordEncoding CompactArgs := ⟨4, encCompactArgs⟩

private def compactStep (q : CompactArgs × ℕ) : Memory.Prog ℕ := do
  let a := Prod.fst q
  let i := Prod.snd q
  let v ← Memory.read (a.mb + a.lastIdx * a.stride + i)
  let val := if i = a.t then 0 else v
  Memory.write (a.mb + a.t * a.stride + i) val
  Memory.write (a.mb + i * a.stride + a.t) val
  pure (i + 1)

private abbrev CompactStepSafe (w : ℕ) (q : CompactArgs × ℕ) (_ : Memory.State) : Prop :=
  let a := Prod.fst q
  let i := Prod.snd q
  Fits w (a.mb + a.lastIdx * a.stride + i) ∧
    Fits w (a.mb + a.t * a.stride + i) ∧
    Fits w (a.mb + i * a.stride + a.t) ∧
    Fits w (i + 1)

private theorem compactStep_realizes :
    Realizes .exact compactStep (appendWords encCompactArgs wordWords) wordWords
      CompactStepSafe (fun _ _ => 0) := by
  unfold compactStep
  realize
  all_goals first | exact h.1 | exact h.2.1 | exact h.2.2.1 | exact h.2.2.2

private def compactRowColProg (a : CompactArgs) : Memory.Prog ℕ :=
  iterate compactStep a a.lastIdx 0

private theorem compactRowColProg_realizes :
    Realizes .exact compactRowColProg encCompactArgs wordWords
      (fun w a s => iterationSafe compactStep CompactStepSafe w a a.lastIdx 0 s)
      (fun _ _ => 0) := by
  unfold compactRowColProg
  realize [compactStep_realizes]
  exact h

private theorem compactRowColProg_spec {w : ℕ} (a : CompactArgs)
    {M : Fin (a.lastIdx + 1) → Fin (a.lastIdx + 1) → ℕ} (hM : IsMultigraph M)
    (tv : Fin (a.lastIdx + 1)) (ht : a.t = tv.1) (ht_lt : tv.1 < a.lastIdx)
    (hm_str : a.lastIdx + 1 ≤ a.stride) (s₀ : Memory.State)
    (hm_f : a.mb + (a.lastIdx + 1) * a.stride ≤ s₀.frontier)
    (hfit_m : Fits w (a.mb + (a.lastIdx + 1) * a.stride))
    (hfit_vals : ∀ i j : Fin (a.lastIdx + 1), Fits w (M i j))
    (hmat : ∀ i j : Fin (a.lastIdx + 1), s₀.mem (a.mb + i.1 * a.stride + j.1) = M i j) :
    iterationSafe compactStep CompactStepSafe w a a.lastIdx 0 s₀ ∧
      Memory.FramedTriple w s₀ (compactRowColProg a) (3 * a.lastIdx)
        (Set.Ico a.mb (a.mb + a.lastIdx * a.stride)) fun _ t => ∀ i j : Fin a.lastIdx,
          t.mem (a.mb + i.1 * a.stride + j.1) = M (embedCompact tv i) (embedCompact tv j) := by
  have hcell := fun x y (hx : x < a.lastIdx + 1) (hy : y < a.lastIdx + 1) =>
    cell_lt_mul hm_str hx hy
  have hcell_lt := fun x y (hx : x < a.lastIdx) (hy : y < a.lastIdx) =>
    cell_lt_mul (by omega : a.lastIdx ≤ a.stride) hx hy
  refine Memory.FramedTriple.iterate (fun k idx s => idx = k ∧ ∀ i j : Fin a.lastIdx,
      s.mem (a.mb + i.1 * a.stride + j.1) =
        if (i.1 = tv.1 ∧ j.1 < k) ∨ (j.1 = tv.1 ∧ i.1 < k) then
          M (embedCompact tv i) (embedCompact tv j)
        else M i.castSucc j.castSucc)
    ⟨rfl, fun i j => by simpa using hmat i.castSucc j.castSucc⟩
    (fun k hk idx s ⟨hidx, hcur⟩ ⟨hfr, hframe⟩ => ?_) fun _ _ h _ i j => (h.2 i j).trans ?_
  · subst idx
    let kFin : Fin a.lastIdx := ⟨k, hk⟩
    have hcl := hcell a.lastIdx k (Nat.lt_succ_self _) (Nat.lt_succ_of_lt hk)
    have hct := hcell_lt tv.1 k ht_lt hk
    have hkt := hcell_lt k tv.1 hk ht_lt
    have hlast_k : s.mem (a.mb + a.lastIdx * a.stride + k) =
        M (Fin.last a.lastIdx) kFin.castSucc := by
      rw [hframe _ (by omega) (by region_omega)]
      exact hmat (Fin.last a.lastIdx) kFin.castSucc
    have hval_fit : Fits w (if k = tv.1 then 0 else s.mem (a.mb + a.lastIdx * a.stride + k)) := by
      split_ifs
      · exact fits_zero w
      · rw [hlast_k]; exact hfit_vals _ _
    refine ⟨by dsimp only [CompactStepSafe]; rw [ht]; exact ⟨by region_omega, by region_omega,
      by region_omega, by region_omega⟩, ?_⟩
    unfold compactStep
    dsimp only
    rw [ht]
    framed_triple
    refine ⟨rfl, fun i j => ?_⟩
    dsimp only
    rw [hlast_k]
    have hlt := Nat.lt_succ_of_lt hk
    have htlt := Nat.lt_succ_of_lt ht_lt
    by_cases hit : i.1 = tv.1 ∧ j.1 = k
    · rcases hit with ⟨hi_t, hj_k⟩
      by_cases htk : k = tv.1
      · rw [hi_t, hj_k, htk, Function.update_self]
        simp [embedCompact, hi_t, hj_k, htk, hM.2]
      · rw [hi_t, hj_k, Function.update_of_ne
          (matAddr_ne hm_str htlt hlt hlt htlt fun h => htk h.1.symm), Function.update_self]
        obtain rfl : j = kFin := Fin.ext hj_k
        simp [embedCompact, kFin, hi_t, htk]
    by_cases hjt : i.1 = k ∧ j.1 = tv.1
    · rcases hjt with ⟨hi_k, hj_t⟩
      rw [hi_k, hj_t, Function.update_self]
      obtain rfl : i = kFin := Fin.ext hi_k
      by_cases htk : k = tv.1
      · simp [embedCompact, kFin, hj_t, htk, hM.2]
      · dsimp only [embedCompact, kFin]
        simp [hj_t, htk, hM.1]
    rw [Function.update_of_ne (matAddr_ne hm_str (Nat.lt_succ_of_lt i.isLt)
        (Nat.lt_succ_of_lt j.isLt) hlt htlt hjt),
      Function.update_of_ne (matAddr_ne hm_str (Nat.lt_succ_of_lt i.isLt)
        (Nat.lt_succ_of_lt j.isLt) htlt hlt hit), hcur i j]
    simp only [and_lt_succ_iff fun h1 he => hit ⟨h1, he⟩,
      and_lt_succ_iff fun h1 he => hjt ⟨he, h1⟩]
  · simp only [i.isLt, j.isLt, and_true]
    split_ifs with h1
    · rfl
    · simp only [not_or] at h1
      simp [embedCompact, h1.1, h1.2]

private structure ContractPartArgs where
  pb : ℕ
  n : ℕ
  lastIdx : ℕ
  s : ℕ
  t : ℕ

private word_enc_structure encContractPartArgs : ContractPartArgs where
  pb : wordWords, n : wordWords, lastIdx : wordWords, s : wordWords, t : wordWords

private instance : WordEncoding ContractPartArgs := ⟨5, encContractPartArgs⟩

private def contractPartStep (q : ContractPartArgs × ℕ) : Memory.Prog ℕ := do
  let a := Prod.fst q
  let v := Prod.snd q
  let p ← Memory.read (a.pb + v)
  let p1 := if p = a.t then a.s else p
  let p2 := if p1 = a.lastIdx then a.t else p1
  Memory.write (a.pb + v) p2
  pure (v + 1)

private abbrev ContractPartStepSafe (w : ℕ) (q : ContractPartArgs × ℕ) (_ : Memory.State) : Prop :=
  let a := Prod.fst q
  let v := Prod.snd q
  Fits w (a.pb + v) ∧ Fits w (v + 1)

private theorem contractPartStep_realizes :
    Realizes .exact contractPartStep (appendWords encContractPartArgs wordWords) wordWords
      ContractPartStepSafe (fun _ _ => 0) := by
  unfold contractPartStep
  realize
  all_goals first | exact h.1 | exact h.2

private def contractPartProg (a : ContractPartArgs) : Memory.Prog ℕ :=
  iterate contractPartStep a a.n 0

private theorem contractPartProg_realizes :
    Realizes .exact contractPartProg encContractPartArgs wordWords
      (fun w a s => iterationSafe contractPartStep ContractPartStepSafe w a a.n 0 s)
      (fun _ _ => 0) := by
  unfold contractPartProg
  realize [contractPartStep_realizes]
  exact h

private theorem contractPartProg_spec {w : ℕ} (a : ContractPartArgs)
    (part : Fin a.n → Fin (a.lastIdx + 1))
    {sv tv : Fin (a.lastIdx + 1)} (hst : sv ≠ tv) (hs : a.s = sv.1) (ht : a.t = tv.1)
    (s₀ : Memory.State) (hp_f : a.pb + a.n ≤ s₀.frontier)
    (hfit_p : Fits w (a.pb + a.n)) (hfit_m : Fits w a.lastIdx)
    (hpart : ∀ v : Fin a.n, s₀.mem (a.pb + v.1) = (part v).1) :
    iterationSafe contractPartStep ContractPartStepSafe w a a.n 0 s₀ ∧
      Memory.FramedTriple w s₀ (contractPartProg a) (2 * a.n) (Set.Ico a.pb (a.pb + a.n))
        fun _ t => ∀ v : Fin a.n, t.mem (a.pb + v.1) = (contractPart part sv tv hst v).1 := by
  refine Memory.FramedTriple.iterate (fun k i s => i = k ∧ ∀ v : Fin a.n, s.mem (a.pb + v.1) =
      if v.1 < k then (contractPart part sv tv hst v).1 else (part v).1)
    ⟨rfl, fun v => by simp [hpart v]⟩ (fun k hk i s ⟨hi, hcur⟩ ⟨hfr, _⟩ => ?_)
    fun _ _ h _ v => by simpa [v.isLt] using h.2 v
  subst i
  let vFin : Fin a.n := ⟨k, hk⟩
  have hv_cur : s.mem (a.pb + k) = (part vFin).1 := by simpa [vFin] using hcur vFin
  have hval_eq :
      (if (if (part vFin).1 = a.t then a.s else (part vFin).1) = a.lastIdx then a.t
        else if (part vFin).1 = a.t then a.s else (part vFin).1) =
        (contractPart part sv tv hst vFin).1 := by
    unfold contractPart compactIdx
    by_cases hpt : part vFin = tv
    · have hptv : (part vFin).1 = a.t := by rw [hpt, ht]
      simp only [hpt, ↓reduceIte, hs, ht]
      split_ifs <;> simp
    · have hptv : (part vFin).1 ≠ a.t := fun h => hpt (Fin.ext (h.trans ht))
      simp only [hpt, ↓reduceIte, ht]
      have hne : (part vFin).1 ≠ tv.1 := fun h => hpt (Fin.ext h)
      simp only [hne, ↓reduceIte]
      split_ifs <;> simp
  refine ⟨⟨by region_omega, by region_omega⟩, ?_⟩
  unfold contractPartStep
  framed_triple
  · rw [hv_cur, hval_eq]
    exact hfit_m.of_le (Nat.le_of_lt (contractPart part sv tv hst vFin).isLt)
  · refine ⟨rfl, fun v => ?_⟩
    dsimp only
    rw [hv_cur, hval_eq]
    by_cases heq : v.1 = k
    · obtain rfl : v = vFin := Fin.ext heq
      simp [vFin]
    · rw [Function.update_of_ne (by omega), hcur v]
      by_cases hlt : v.1 < k
      · simp [hlt, Nat.lt_succ_of_lt hlt]
      · simp [hlt, show ¬(v.1 < k + 1) by omega]

/-! ### Phase loop (`phaseStep`) and main program (`stoerWagnerProg`) -/

private structure PhaseArgs where
  n : ℕ
  ws : ℕ

private word_enc_structure encPhaseArgs : PhaseArgs where
  n : wordWords, ws : wordWords

private instance : WordEncoding PhaseArgs := ⟨2, encPhaseArgs⟩

private structure PhaseState where
  m : ℕ
  hasBest : ℕ
  bestWeight : ℕ

private word_enc_structure encPhaseState : PhaseState where
  m : wordWords, hasBest : wordWords, bestWeight : wordWords

private instance : WordEncoding PhaseState := ⟨3, encPhaseState⟩

private structure UpdateBestArgs where
  pb : ℕ
  ob : ℕ
  n : ℕ
  last : ℕ
  lastKey : ℕ
  better : ℕ
  bestWeight : ℕ

private word_enc_structure encUpdateBestArgs : UpdateBestArgs where
  pb : wordWords, ob : wordWords, n : wordWords, last : wordWords,
  lastKey : wordWords, better : wordWords, bestWeight : wordWords

private instance : WordEncoding UpdateBestArgs := ⟨7, encUpdateBestArgs⟩

private def updateBestProg (a : UpdateBestArgs) : Memory.Prog ℕ :=
  if a.better = 1 then do
    Memory.write (a.ob + 1) a.lastKey
    let _ ← writeSideProg ⟨a.pb, a.ob + 2, a.n, a.last⟩
    pure a.lastKey
  else
    pure a.bestWeight

private abbrev UpdateBestSafe (w : ℕ) (a : UpdateBestArgs) (s : Memory.State) : Prop :=
  Fits w (a.ob + 2) ∧ Fits w 1 ∧
    (a.better = 1 →
      iterationSafe writeSideStep WriteSideStepSafe w ⟨a.pb, a.ob + 2, a.n, a.last⟩ a.n 0
        ⟨Function.update s.mem (a.ob + 1) a.lastKey, s.frontier⟩)

private theorem updateBestProg_realizes :
    Realizes .exact updateBestProg encUpdateBestArgs wordWords
      UpdateBestSafe (fun _ _ => 0) := by
  unfold updateBestProg
  realize [writeSideProg_realizes]
  all_goals first
    | exact h.1
    | exact h.2.1
    | exact h.1.of_le (by omega)
    | exact h.2.2 ‹_›

private def compactIfProg (a : CompactArgs) : Memory.Prog ℕ :=
  if a.t < a.lastIdx then compactRowColProg a else pure 0

private abbrev CompactIfSafe (w : ℕ) (a : CompactArgs) (s : Memory.State) : Prop :=
  Fits w 1 ∧ (a.t < a.lastIdx → iterationSafe compactStep CompactStepSafe w a a.lastIdx 0 s)

private theorem compactIfProg_realizes :
    Realizes .exact compactIfProg encCompactArgs wordWords
      CompactIfSafe (fun _ _ => 0) := by
  unfold compactIfProg
  realize [compactRowColProg_realizes]
  exact h.2 ‹_›

private def phaseStep (q : PhaseArgs × PhaseState) : Memory.Prog PhaseState := do
  let a := Prod.fst q
  let st := Prod.snd q
  let _ ← Memory.read 0
  let mb := matBase a.ws
  let pb := partBase a.ws a.n
  let kb := keyBase a.ws a.n
  let ub := usedBase a.ws a.n
  let ob := outBase a.ws a.n
  let _ ← initMAProg ⟨kb, ub, st.m⟩
  let ord ← maOrderProg ⟨mb, kb, ub, a.n, st.m⟩
  let better := if st.hasBest = 0 then 1 else if ord.lastKey ≤ st.bestWeight then 1 else 0
  let newBestW ← updateBestProg ⟨pb, ob, a.n, ord.last, ord.lastKey, better, st.bestWeight⟩
  if 2 < st.m then do
    let _ ← mergeRowColProg ⟨mb, a.n, st.m, ord.prev, ord.last⟩
    let lastIdx := st.m - 1
    let _ ← compactIfProg ⟨mb, a.n, lastIdx, ord.last⟩
    let _ ← contractPartProg ⟨pb, a.n, lastIdx, ord.prev, ord.last⟩
    pure ⟨st.m - 1, 1, newBestW⟩
  else
    pure ⟨st.m - 1, 1, newBestW⟩

private abbrev PhaseStepSafe (w : ℕ) (q : PhaseArgs × PhaseState) (s₀ : Memory.State) : Prop :=
  let a := Prod.fst q
  let st := Prod.snd q
  let mb := matBase a.ws
  let pb := partBase a.ws a.n
  let kb := keyBase a.ws a.n
  let ub := usedBase a.ws a.n
  let ob := outBase a.ws a.n
  let s1 := (Memory.spec 0).clientState s₀ (initMAProg ⟨kb, ub, st.m⟩)
  let ord := (Memory.spec 0).clientResult s1 (maOrderProg ⟨mb, kb, ub, a.n, st.m⟩)
  let s2 := (Memory.spec 0).clientState s1 (maOrderProg ⟨mb, kb, ub, a.n, st.m⟩)
  let better := if st.hasBest = 0 then 1 else if ord.lastKey ≤ st.bestWeight then 1 else 0
  let uargs : UpdateBestArgs := ⟨pb, ob, a.n, ord.last, ord.lastKey, better, st.bestWeight⟩
  let s2w : Memory.State := ⟨Function.update s2.mem (ob + 1) ord.lastKey, s2.frontier⟩
  let s3 := (Memory.spec 0).clientState s2 (updateBestProg uargs)
  let s4 := (Memory.spec 0).clientState s3 (mergeRowColProg ⟨mb, a.n, st.m, ord.prev, ord.last⟩)
  let lastIdx := st.m - 1
  let s5 := (Memory.spec 0).clientState s4 (compactIfProg ⟨mb, a.n, lastIdx, ord.last⟩)
  Fits w (ob + a.n + 2) ∧ Fits w 4 ∧ 1 ≤ st.m ∧
    iterationSafe initMAStep InitMAStepSafe w ⟨kb, ub, st.m⟩ st.m 0 s₀ ∧
    iterationSafe maOrderStep MAOrderStepSafe w ⟨mb, kb, ub, a.n, st.m⟩ st.m ⟨0, 0, 0⟩ s1 ∧
    (better = 1 →
      iterationSafe writeSideStep WriteSideStepSafe w ⟨pb, ob + 2, a.n, ord.last⟩ a.n 0 s2w) ∧
    (2 < st.m →
      iterationSafe mergeStep MergeStepSafe w ⟨mb, a.n, st.m, ord.prev, ord.last⟩ st.m 0 s3 ∧
      (ord.last < lastIdx →
        iterationSafe compactStep CompactStepSafe w ⟨mb, a.n, lastIdx, ord.last⟩ lastIdx 0 s4) ∧
      iterationSafe contractPartStep ContractPartStepSafe w
        ⟨pb, a.n, lastIdx, ord.prev, ord.last⟩ a.n 0 s5)

private theorem phaseStep_realizes :
    Realizes .exact phaseStep (appendWords encPhaseArgs encPhaseState) encPhaseState
      PhaseStepSafe (fun _ _ => 0) := by
  unfold phaseStep
  realize [initMAProg_realizes, maOrderProg_realizes, updateBestProg_realizes,
    mergeRowColProg_realizes, compactIfProg_realizes, contractPartProg_realizes]
  all_goals
    obtain ⟨hfit, hfit4, hm1, hinit, hord, hws, hgt2⟩ := h
    first
    | exact hinit
    | exact hord
    | exact ⟨hfit.of_le (by dsimp only [outBase] at hfit ⊢; omega),
        hfit4.of_le (by omega), hws⟩
    | exact (hgt2 ‹_›).1
    | exact ⟨hfit4.of_le (by omega), (hgt2 ‹_›).2.1⟩
    | exact (hgt2 ‹_›).2.2
    | exact hfit4.of_le (by omega)
    | exact hfit.of_le (by
        dsimp only [matBase, partBase, keyBase, usedBase, outBase] at hfit ⊢
        nlinarith)
    | omega

private def phasesLoop (a : PhaseArgs) : Memory.Prog PhaseState :=
  iterate phaseStep a (a.n - 1) ⟨a.n, 0, 0⟩

private theorem phasesLoop_realizes :
    Realizes .exact phasesLoop encPhaseArgs encPhaseState
      (fun w a s => 1 ≤ a.n ∧ Fits w 1 ∧
        iterationSafe phaseStep PhaseStepSafe w a (a.n - 1) ⟨a.n, 0, 0⟩ s)
      (fun _ _ => 0) := by
  unfold phasesLoop
  realize [phaseStep_realizes]
  all_goals first
    | exact h.1
    | exact h.2.2

private def stoerWagnerProg (n : ℕ) : Memory.Prog ℕ := do
  let ws ← Memory.allocDirty (wsSize n)
  let ob := outBase ws n
  Memory.write ob (n + 1)
  if n < 2 then do
    Memory.write (ob + 1) 0
    if n = 1 then do
      Memory.write (ob + 2) 0
      pure ob
    else
      pure ob
  else do
    let _ ← copyWordsProg ⟨2, matBase ws, n * n⟩
    let _ ← initPartProg (partBase ws n, n)
    let _ ← phasesLoop ⟨n, ws⟩
    pure ob

private abbrev StoerWagnerProgSafe (w n : ℕ) (s₀ : Memory.State) : Prop :=
  let ws := s₀.frontier
  let ob := outBase ws n
  let s1 : Memory.State := ⟨Function.update s₀.mem ob (n + 1), ws + wsSize n⟩
  let s2 := (Memory.spec 0).clientState s1 (copyWordsProg ⟨2, matBase ws, n * n⟩)
  let s3 := (Memory.spec 0).clientState s2 (initPartProg (partBase ws n, n))
  Fits w (ws + wsSize n) ∧ Fits w 4 ∧
    (¬(n < 2) →
      iterationSafe copyStep CopyStepSafe w ⟨2, matBase ws, n * n⟩ (n * n) 0 s1 ∧
      iterationSafe initPartStep InitPartStepSafe w (partBase ws n, n) n 0 s2 ∧
      iterationSafe phaseStep PhaseStepSafe w ⟨n, ws⟩ (n - 1) ⟨n, 0, 0⟩ s3)

private theorem stoerWagnerProg_realizes :
    Realizes .exact stoerWagnerProg wordWords wordWords
      StoerWagnerProgSafe (fun _ _ => 0) := by
  unfold stoerWagnerProg
  realize [copyWordsProg_realizes, initPartProg_realizes, phasesLoop_realizes]
  all_goals
    obtain ⟨hfit, hfit4, hge2⟩ := h
    first
    | exact (hge2 ‹_›).1
    | exact (hge2 ‹_›).2.1
    | exact (hge2 ‹_›).2.2
    | exact hfit4.of_le (by omega)
    | exact hfit.of_le (by dsimp only [wsSize, matBase, partBase, outBase] at hfit ⊢; nlinarith)
    | omega

/-! ### Phase invariant and end-to-end correctness -/

private theorem totalDoubledWeight_cast {m₁ m₂ : ℕ} (h : m₁ = m₂) (W : Fin m₁ → Fin m₁ → ℕ) :
    totalDoubledWeight (fun i j : Fin m₂ => W (i.cast h.symm) (j.cast h.symm)) =
      totalDoubledWeight W := by
  subst h; rfl

private theorem isContractionOf_cast {n m₁ m₂ : ℕ} (h : m₁ = m₂)
    {W₀ : Fin n → Fin n → ℕ} {part : Fin n → Fin m₁} {W : Fin m₁ → Fin m₁ → ℕ}
    (hC : IsContractionOf W₀ part W) :
    IsContractionOf W₀ (fun v => (part v).cast h)
      (fun i j : Fin m₂ => W (i.cast h.symm) (j.cast h.symm)) := by
  subst h; exact hC

private theorem phase_run_step {n m q l : ℕ}
    (W : Fin m → Fin m → ℕ) (part : Fin n → Fin m)
    {pref : List (Fin m)} {sv tv : Fin m}
    (hma : maOrder W = pref ++ [sv, tv]) (hst : sv ≠ tv)
    (hm_succ : l + 1 = m) (hk : m = (q + 1) + 2) (hl_q : l = q + 2) :
    let tv' : Fin (l + 1) := tv.cast hm_succ.symm
    let sv' : Fin (l + 1) := sv.cast hm_succ.symm
    let hst' : sv' ≠ tv' := fun h => hst (by simpa [sv', tv', Fin.ext_iff] using h)
    let W' : Fin l → Fin l → ℕ :=
      contractMatrix (fun i j => W (i.cast hm_succ) (j.cast hm_succ)) sv' tv'
    let part' : Fin n → Fin l :=
      contractPart (fun v => (part v).cast hm_succ.symm) sv' tv' hst'
    run (q + 1) (fun i j => W (i.cast hk.symm) (j.cast hk.symm)) (fun v => (part v).cast hk) =
      chooseCut ⟨pullbackCut part {tv}, rowDeg W tv⟩
        (run q (fun i j => W' (i.cast hl_q.symm) (j.cast hl_q.symm))
          (fun v => (part' v).cast hl_q)) := by
  subst hl_q
  subst hm_succ
  dsimp only [Fin.cast_refl]
  exact run_succ W part hma hst

private theorem run_congr_step {n k₁ k₂ m : ℕ} (hk : k₁ = k₂) (hm1 : m = k₁ + 2)
    (hm2 : m = k₂ + 2) (W : Fin m → Fin m → ℕ) (part : Fin n → Fin m) :
    run k₁ (fun i j => W (i.cast hm1.symm) (j.cast hm1.symm)) (fun v => (part v).cast hm1) =
      run k₂ (fun i j => W (i.cast hm2.symm) (j.cast hm2.symm)) (fun v => (part v).cast hm2) := by
  subst hk; rfl

private theorem phase_run_zero {n m : ℕ}
    (W : Fin m → Fin m → ℕ) (part : Fin n → Fin m)
    {pref : List (Fin m)} {sv tv : Fin m}
    (hma : maOrder W = pref ++ [sv, tv]) (hm2 : m = 2) :
    run 0 (fun i j : Fin 2 => W (i.cast hm2.symm) (j.cast hm2.symm))
      (fun v => (part v).cast hm2) = ⟨pullbackCut part {tv}, rowDeg W tv⟩ := by
  subst hm2
  rw [maOrder_fin_two W] at hma
  have hnil : pref = [] := by
    cases pref with
    | nil => rfl
    | cons _ _ =>
      have hlen := congrArg List.length hma
      simp only [List.length_cons, List.length_nil, List.length_append] at hlen
      omega
  subst hnil
  have htv : tv = 1 := by
    have := congrArg (fun l => l[1]?) hma.symm
    simpa using this
  subst htv
  rw [run_zero]
  rfl

private def PhaseInv {n : ℕ} (ws fr₀ : ℕ) (W₀ : Fin n → Fin n → ℕ)
    (p : ℕ) (st : PhaseState) (s : Memory.State) : Prop :=
  s.frontier = fr₀ ∧
    s.mem (outBase ws n) = n + 1 ∧
    st.m = n - p ∧
    ((p = 0 ∧ st.hasBest = 0 ∧
        (∀ i j : Fin n, s.mem (matBase ws + i.1 * n + j.1) = W₀ i j) ∧
        (∀ v : Fin n, s.mem (partBase ws n + v.1) = v.1)) ∨
     (0 < p ∧ p < n - 1 ∧ st.hasBest = 1 ∧
        ∃ (best : CutResult n) (W : Fin (n - p) → Fin (n - p) → ℕ)
          (part : Fin n → Fin (n - p)) (hk : n - p = (n - 2 - p) + 2),
          IsContractionOf W₀ part W ∧
          totalDoubledWeight W ≤ totalDoubledWeight W₀ ∧
          st.bestWeight = best.weight ∧
          s.mem (outBase ws n + 1) = best.weight ∧
          (∀ v : Fin n, s.mem (outBase ws n + 2 + v.1) = if v ∈ best.side then 1 else 0) ∧
          (∀ i j : Fin (n - p), s.mem (matBase ws + i.1 * n + j.1) = W i j) ∧
          (∀ v : Fin n, s.mem (partBase ws n + v.1) = (part v).1) ∧
          chooseCut best (run (n - 2 - p) (fun i j => W (i.cast hk.symm) (j.cast hk.symm))
            (fun v => (part v).cast hk)) = stoerWagner W₀) ∨
     (p = n - 1 ∧ st.hasBest = 1 ∧
        s.mem (outBase ws n + 1) = (stoerWagner W₀).weight ∧
        (∀ v : Fin n, s.mem (outBase ws n + 2 + v.1) =
          if v ∈ (stoerWagner W₀).side then 1 else 0)))

private theorem phaseContract_spec {w n ws p m prev last newBestW : ℕ}
    {W₀ : Fin n → Fin n → ℕ} {W : Fin m → Fin m → ℕ} {part : Fin n → Fin m}
    {pref : List (Fin m)} {sv tv : Fin m} {newBest : CutResult n}
    (hgt2 : 2 < m) (hm_eq : m = n - p) (hk : m = (n - 2 - p) + 2) (hmn : m ≤ n)
    (hC : IsContractionOf W₀ part W) (htotW : totalDoubledWeight W ≤ totalDoubledWeight W₀)
    (hma_eq : maOrder W = pref ++ [sv, tv]) (hst_ne : sv ≠ tv)
    (hprev : prev = sv.1) (hlast : last = tv.1) (hfit_top : Fits w (ws + wsSize n))
    (hfit_tot : Fits w (totalDoubledWeight W₀))
    (s3 : Memory.State) (hf : ws + wsSize n ≤ s3.frontier)
    (hs3_outl : s3.mem (outBase ws n) = n + 1)
    (hnbW : newBestW = newBest.weight)
    (hs3_ob1 : s3.mem (outBase ws n + 1) = newBest.weight)
    (hs3_ob2 : ∀ v : Fin n, s3.mem (outBase ws n + 2 + v.1) = if v ∈ newBest.side then 1 else 0)
    (hs3_mat : ∀ i j : Fin m, s3.mem (matBase ws + i.1 * n + j.1) = W i j)
    (hs3_part : ∀ v : Fin n, s3.mem (partBase ws n + v.1) = (part v).1)
    (hnewBest_rel :
      let phase : CutResult n := ⟨pullbackCut part {tv}, rowDeg W tv⟩
      (newBest = phase ∧
          run (n - 2 - p) (fun i j => W (i.cast hk.symm) (j.cast hk.symm))
            (fun v => (part v).cast hk) = stoerWagner W₀) ∨
       (∃ best : CutResult n, newBest = chooseCut best phase ∧
          chooseCut best (run (n - 2 - p) (fun i j => W (i.cast hk.symm) (j.cast hk.symm))
            (fun v => (part v).cast hk)) = stoerWagner W₀)) :
    let mb := matBase ws
    let pb := partBase ws n
    let lastIdx := m - 1
    let s4 := (Memory.spec 0).clientState s3 (mergeRowColProg ⟨mb, n, m, prev, last⟩)
    let s5 := (Memory.spec 0).clientState s4 (compactIfProg ⟨mb, n, lastIdx, last⟩)
    let prog : Memory.Prog PhaseState := do
      let _ ← mergeRowColProg ⟨mb, n, m, prev, last⟩
      let _ ← compactIfProg ⟨mb, n, lastIdx, last⟩
      let _ ← contractPartProg ⟨pb, n, lastIdx, prev, last⟩
      pure ⟨lastIdx, 1, newBestW⟩
    (iterationSafe mergeStep MergeStepSafe w ⟨mb, n, m, prev, last⟩ m 0 s3 ∧
      (last < lastIdx →
        iterationSafe compactStep CompactStepSafe w ⟨mb, n, lastIdx, last⟩ lastIdx 0 s4) ∧
      iterationSafe contractPartStep ContractPartStepSafe w
        ⟨pb, n, lastIdx, prev, last⟩ n 0 s5) ∧
      Memory.FramedTriple w s3 prog (6 * m + 3 * lastIdx + 2 * n)
        (Set.Ico mb (outBase ws n + n + 2)) fun st t => PhaseInv ws t.frontier W₀ (p + 1) st t := by
  have hmn_sq : m * n ≤ n * n := Nat.mul_le_mul_right n hmn
  have hW : IsMultigraph W := hC.multigraph
  have hfit_W : Fits w (totalDoubledWeight W) := hfit_tot.of_le htotW
  let mb := matBase ws
  let pb := partBase ws n
  let ob := outBase ws n
  let lastIdx := m - 1
  have hm_succ : lastIdx + 1 = m := by omega
  obtain ⟨hsafe_m, hmerge⟩ := mergeRowColProg_spec ⟨mb, n, m, prev, last⟩ hW hst_ne
    hprev hlast hmn s3 (by region_omega) (by region_omega) hfit_W hs3_mat
  let s4 := (Memory.spec 0).clientState s3 (mergeRowColProg ⟨mb, n, m, prev, last⟩)
  obtain ⟨-, -, ⟨hs4_fr, hs4_mod⟩, hs4_mat⟩ := framedTriple_iff_realization.mp hmerge
  let M : Fin (lastIdx + 1) → Fin (lastIdx + 1) → ℕ :=
    fun i j => mergePair W sv tv (i.cast hm_succ) (j.cast hm_succ)
  have hM_multi : IsMultigraph M := by
    have hm := isMultigraph_mergePair hW sv tv
    exact ⟨fun i j => hm.1 _ _, fun i => hm.2 _⟩
  have hM_fit : ∀ i j : Fin (lastIdx + 1), Fits w (M i j) := by
    intro i j
    dsimp only [M, mergePair]
    split_ifs with h1 h2 h3
    · exact fits_zero w
    · exact hfit_W.of_le (add_entry_le_totalDoubledWeight hst_ne _)
    · exact hfit_W.of_le (by
        rw [hW.1 _ sv, hW.1 _ tv]; exact add_entry_le_totalDoubledWeight hst_ne _)
    · exact hfit_W.of_le (entry_le_totalDoubledWeight W _ _)
  let tv' : Fin (lastIdx + 1) := tv.cast hm_succ.symm
  let sv' : Fin (lastIdx + 1) := sv.cast hm_succ.symm
  have hst' : sv' ≠ tv' := fun h => hst_ne (by simpa [sv', tv', Fin.ext_iff] using h)
  let W' : Fin lastIdx → Fin lastIdx → ℕ :=
    contractMatrix (fun i j => W (i.cast hm_succ) (j.cast hm_succ)) sv' tv'
  let part' : Fin n → Fin lastIdx :=
    contractPart (fun v => (part v).cast hm_succ.symm) sv' tv' hst'
  let s5 := (Memory.spec 0).clientState s4 (compactIfProg ⟨mb, n, lastIdx, last⟩)
  have hcomp_spec :
      (last < lastIdx →
        iterationSafe compactStep CompactStepSafe w ⟨mb, n, lastIdx, last⟩ lastIdx 0 s4) ∧
      Memory.FramedTriple w s4 (compactIfProg ⟨mb, n, lastIdx, last⟩) (3 * lastIdx)
        (Set.Ico mb (mb + m * n)) fun _ t =>
          ∀ i j : Fin lastIdx, t.mem (mb + i.1 * n + j.1) = W' i j := by
    by_cases hlt_last : last < lastIdx
    · have hcomp := compactRowColProg_spec ⟨mb, n, lastIdx, last⟩ hM_multi tv'
        hlast (by simpa [tv', hlast] using hlt_last) (by dsimp only; omega) s4
        (by dsimp only; rw [hm_succ]; region_omega) (by dsimp only; rw [hm_succ]; region_omega)
        hM_fit (fun i j => by simpa [M] using hs4_mat (i.cast hm_succ) (j.cast hm_succ))
      have hcif : compactIfProg ⟨mb, n, lastIdx, last⟩ =
          compactRowColProg ⟨mb, n, lastIdx, last⟩ := by
        unfold compactIfProg; exact ite_eq_left hlt_last
      have hln : lastIdx * n ≤ m * n := Nat.mul_le_mul_right n (by omega)
      refine ⟨fun _ => hcomp.1, hcif ▸ (hcomp.2.mono le_rfl fun _ _ h i j => ?_).frame_mono
        (Set.Ico_subset_Ico_right (by dsimp only; omega))⟩
      rw [h i j]
      unfold W' contractMatrix M mergePair
      simp [sv', tv', Fin.ext_iff]
    · have hcif : compactIfProg ⟨mb, n, lastIdx, last⟩ = pure 0 := by
        unfold compactIfProg; exact ite_eq_right hlt_last
      refine ⟨fun h => absurd h hlt_last, hcif ▸ Memory.FramedTriple.pure fun i j => ?_⟩
      have htv_eq : tv.1 = lastIdx := by omega
      have hti : i.1 ≠ tv'.1 := by simp only [tv', Fin.val_cast]; omega
      have htj : j.1 ≠ tv'.1 := by simp only [tv', Fin.val_cast]; omega
      have he1 : embedCompact tv' i = i.castSucc := by simp [embedCompact, hti]
      have he2 : embedCompact tv' j = j.castSucc := by simp [embedCompact, htj]
      unfold W' contractMatrix
      rw [he1, he2]
      have hmij := hs4_mat (i.castSucc.cast hm_succ) (j.castSucc.cast hm_succ)
      simpa [client_simps, mergePair, sv', tv', Fin.ext_iff] using hmij
  obtain ⟨hsafe_c, hcompM⟩ := hcomp_spec
  obtain ⟨-, -, ⟨hs5_fr, hs5_mod'⟩, hs5_mat⟩ := framedTriple_iff_realization.mp hcompM
  have hs5_mod : ∀ addr < s3.frontier, ¬(mb ≤ addr ∧ addr < mb + m * n) →
      s5.mem addr = s3.mem addr := fun addr ha h =>
    (hs5_mod' addr (lt_of_lt_of_le ha hs4_fr) h).trans (hs4_mod addr ha h)
  obtain ⟨hsafe_p, hcp⟩ := contractPartProg_spec (w := w) ⟨pb, n, lastIdx, prev, last⟩
    (fun v => (part v).cast hm_succ.symm) hst'
    (by simpa [sv'] using hprev) (by simpa [tv'] using hlast) s5
    (by region_omega) (by region_omega) (by region_omega)
    (fun v => by
      rw [hs5_mod (pb + v.1) (by region_omega) (by region_omega)]
      exact hs3_part v)
  obtain ⟨-, -, ⟨hs6_fr, hs6_mod⟩, hs6_part⟩ := framedTriple_iff_realization.mp hcp
  have hC_cast : IsContractionOf W₀ (fun v => (part v).cast hm_succ.symm)
      (fun i j => W (i.cast hm_succ) (j.cast hm_succ)) :=
    isContractionOf_cast hm_succ.symm hC
  have hC' : IsContractionOf W₀ part' W' := isContractionOf_contract hC_cast hst'
  have htotW' : totalDoubledWeight W' ≤ totalDoubledWeight W₀ := by
    have hdec := totalDoubledWeight_contractMatrix hC_cast.multigraph hst'
    rw [totalDoubledWeight_cast hm_succ.symm W] at hdec
    dsimp only [W']
    omega
  refine ⟨⟨hsafe_m, hsafe_c, hsafe_p⟩, ?_⟩
  refine (Memory.FramedTriple.seq (c₂ := 3 * lastIdx + (2 * n + 0)) hmerge
    (Set.Ico_subset_Ico_right (by region_omega)) ?_).mono (by dsimp only; omega) fun _ _ => id
  refine Memory.FramedTriple.seq hcompM (Set.Ico_subset_Ico_right (by region_omega)) ?_
  refine Memory.FramedTriple.seq hcp (Set.Ico_subset_Ico (by region_omega) (by region_omega)) ?_
  refine Memory.FramedTriple.pure ?_
  have hlast_eq : lastIdx = n - (p + 1) := by omega
  have hk' : n - (p + 1) = (n - 2 - (p + 1)) + 2 := by omega
  let s6 := (Memory.spec 0).clientState s5 (contractPartProg ⟨pb, n, lastIdx, prev, last⟩)
  have hs6_out : ∀ addr, ob ≤ addr → addr < s3.frontier → s6.mem addr = s3.mem addr :=
    fun addr ha ha' => by
    rw [hs6_mod addr (lt_of_lt_of_le ha' (hs4_fr.trans hs5_fr)) (by region_omega),
      hs5_mod addr ha' (by region_omega)]
  have hrun_step :
      run (n - 2 - p) (fun i j => W (i.cast hk.symm) (j.cast hk.symm))
        (fun v => (part v).cast hk) =
      chooseCut ⟨pullbackCut part {tv}, rowDeg W tv⟩
        (run (n - 2 - (p + 1))
          (fun i j => W' (i.cast (by omega)) (j.cast (by omega)))
          (fun v => (part' v).cast (by omega))) := by
    have hq_succ : n - 2 - p = (n - 2 - (p + 1)) + 1 := by omega
    have hk_q : m = ((n - 2 - (p + 1)) + 1) + 2 := by omega
    have hl_q : lastIdx = (n - 2 - (p + 1)) + 2 := by omega
    rw [run_congr_step hq_succ hk hk_q W part]
    exact phase_run_step W part hma_eq hst_ne hm_succ hk_q hl_q
  refine ⟨rfl, (hs6_out ob le_rfl (by region_omega)).trans hs3_outl, by omega,
    Or.inr (Or.inl ⟨Nat.succ_pos p, by omega, rfl, newBest,
      fun i j => W' (i.cast hlast_eq.symm) (j.cast hlast_eq.symm),
      fun v => (part' v).cast hlast_eq, hk', isContractionOf_cast hlast_eq hC',
      by rw [totalDoubledWeight_cast hlast_eq W']; exact htotW', hnbW,
      (hs6_out (ob + 1) (by omega) (by region_omega)).trans hs3_ob1,
      fun v => (hs6_out (ob + 2 + v.1) (by omega) (by region_omega)).trans (hs3_ob2 v),
      fun i j => by
        have hlt := cell_lt_mul (m := n) le_rfl
          (lt_of_lt_of_le i.isLt (Nat.sub_le n (p + 1)))
          (lt_of_lt_of_le j.isLt (Nat.sub_le n (p + 1)))
        rw [hs6_mod (mb + i.1 * n + j.1) (by region_omega) (by region_omega)]
        exact hs5_mat (i.cast hlast_eq.symm) (j.cast hlast_eq.symm),
      fun v => by simpa using hs6_part v, ?_⟩)⟩
  have hrest_cast :
      run (n - 2 - (p + 1))
        (fun i j => W' ((i.cast hk'.symm).cast hlast_eq.symm)
          ((j.cast hk'.symm).cast hlast_eq.symm))
        (fun v => ((part' v).cast hlast_eq).cast hk') =
      run (n - 2 - (p + 1))
        (fun i j => W' (i.cast (by omega)) (j.cast (by omega)))
        (fun v => (part' v).cast (by omega)) := rfl
  rw [hrest_cast]
  rcases hnewBest_rel with ⟨rfl, hrun0⟩ | ⟨best, rfl, hch0⟩
  · rw [← hrun_step]; exact hrun0
  · rw [chooseCut_assoc, ← hrun_step]; exact hch0

private theorem phaseStep_spec {w n ws : ℕ} (hn : 2 ≤ n) {W₀ : Fin n → Fin n → ℕ}
    (hW₀ : IsMultigraph W₀) (hfit_top : Fits w (ws + wsSize n)) (hfit4 : Fits w 4)
    (hfit_tot : Fits w (totalDoubledWeight W₀))
    (p : ℕ) (hp : p < n - 1) (st : PhaseState) (s : Memory.State)
    (hf : ws + wsSize n ≤ s.frontier) (hinv : PhaseInv ws s.frontier W₀ p st s) :
    PhaseStepSafe w (⟨n, ws⟩, st) s ∧
      Memory.FramedTriple w s (phaseStep (⟨n, ws⟩, st)) (23 * n ^ 2)
        (Set.Ico (matBase ws) (outBase ws n + n + 2))
        fun st' t => PhaseInv ws t.frontier W₀ (p + 1) st' t := by
  have hfit1 : Fits w 1 := hfit4.of_le (by omega)
  obtain ⟨-, hout_l, hst_m, hbranch⟩ := hinv
  have hm_eq : st.m = n - p := hst_m
  have hm2 : 2 ≤ st.m := by omega
  have hmn : st.m ≤ n := by omega
  have hactive : ∃ (W : Fin st.m → Fin st.m → ℕ) (part : Fin n → Fin st.m)
      (hk : st.m = (n - 2 - p) + 2),
      IsContractionOf W₀ part W ∧
      totalDoubledWeight W ≤ totalDoubledWeight W₀ ∧
      (∀ i j : Fin st.m, s.mem (matBase ws + i.1 * n + j.1) = W i j) ∧
      (∀ v : Fin n, s.mem (partBase ws n + v.1) = (part v).1) ∧
      ((st.hasBest = 0 ∧
          run (n - 2 - p) (fun i j => W (i.cast hk.symm) (j.cast hk.symm))
            (fun v => (part v).cast hk) = stoerWagner W₀) ∨
       (st.hasBest = 1 ∧ ∃ best : CutResult n,
          st.bestWeight = best.weight ∧
          s.mem (outBase ws n + 1) = best.weight ∧
          (∀ v : Fin n, s.mem (outBase ws n + 2 + v.1) = if v ∈ best.side then 1 else 0) ∧
          chooseCut best (run (n - 2 - p) (fun i j => W (i.cast hk.symm) (j.cast hk.symm))
            (fun v => (part v).cast hk)) = stoerWagner W₀)) := by
    rcases hbranch with ⟨hp0, hhb, hmat, hpart⟩ |
        ⟨_, _, hhb, best, W, part, hk, hC, htotW, hbw, hob1, hob2, hmat, hpart, hch⟩ |
        ⟨hp_end, _⟩
    · subst hp0
      have hm_n : st.m = n := by omega
      generalize hm_gen : st.m = m at hm_eq hm_n ⊢
      subst hm_n
      have hk0 : m = (m - 2 - 0) + 2 := by omega
      refine ⟨W₀, id, hk0, isContractionOf_id hW₀, le_rfl, hmat, hpart, Or.inl ⟨hhb, ?_⟩⟩
      obtain ⟨q, rfl⟩ : ∃ q, m = q + 2 := ⟨m - 2, by omega⟩
      have hq : q + 2 - 2 - 0 = q := by omega
      simp only [stoerWagner]
      cases hq
      rfl
    · generalize hm_gen : st.m = m at hm_eq ⊢
      subst hm_eq
      exact ⟨W, part, hk, hC, htotW, hmat, hpart, Or.inr ⟨hhb, best, hbw, hob1, hob2, hch⟩⟩
    · omega
  obtain ⟨W, part, hk, hC, htotW, hmat, hpart, hbest_inv⟩ := hactive
  have hW : IsMultigraph W := hC.multigraph
  have hfit_W : Fits w (totalDoubledWeight W) := hfit_tot.of_le htotW
  have hmn_sq : st.m * n ≤ n * n := Nat.mul_le_mul_right n hmn
  let mb := matBase ws
  let pb := partBase ws n
  let kb := keyBase ws n
  let ub := usedBase ws n
  let ob := outBase ws n
  obtain ⟨hsafe_i, hinit⟩ := initMAProg_spec (w := w) ⟨kb, ub, st.m⟩ s
    (by region_omega) (by region_omega) (by region_omega) (by region_omega) (by region_omega)
  let s1 := (Memory.spec 0).clientState s (initMAProg ⟨kb, ub, st.m⟩)
  obtain ⟨-, -, ⟨hs1_fr, hs1_mod⟩, hs1_init⟩ := framedTriple_iff_realization.mp hinit
  have hf1 : ws + wsSize n ≤ s1.frontier := hf.trans hs1_fr
  have hs1_mat : ∀ i j : Fin st.m, s1.mem (mb + i.1 * n + j.1) = W i j := fun i j => by
    have hlt := cell_lt_mul le_rfl (lt_of_lt_of_le i.isLt hmn) (lt_of_lt_of_le j.isLt hmn)
    exact (hs1_mod _ (by region_omega) (by region_omega)).trans (hmat i j)
  obtain ⟨hsafe_o, hord⟩ := maOrderProg_spec ⟨mb, kb, ub, n, st.m⟩ hm2 hW hmn s1
    (by region_omega) (by region_omega) (by region_omega) (by region_omega) (by region_omega)
    (by region_omega) (by region_omega) (by region_omega) hfit1 hfit_W hs1_mat hs1_init
  let ord := (Memory.spec 0).clientResult s1 (maOrderProg ⟨mb, kb, ub, n, st.m⟩)
  let s2 := (Memory.spec 0).clientState s1 (maOrderProg ⟨mb, kb, ub, n, st.m⟩)
  obtain ⟨-, -, ⟨hs2_fr, hs2_mod⟩, pref, sv, tv, hma_eq, hst_ne, hord_prev, hord_last,
    hord_key⟩ := framedTriple_iff_realization.mp hord
  change ord.prev = sv.1 at hord_prev
  change ord.last = tv.1 at hord_last
  change ord.lastKey = rowDeg W tv at hord_key
  have hf2 : ws + wsSize n ≤ s2.frontier := hf1.trans hs2_fr
  have hs2_mem : ∀ addr, addr < s.frontier → (addr < mb + st.m * n ∨ pb ≤ addr ∧ addr < kb ∨
      ob ≤ addr) → s2.mem addr = s.mem addr := fun addr ha hx => by
    rw [hs2_mod addr (lt_of_lt_of_le ha hs1_fr) (by region_omega),
      hs1_mod addr ha (by region_omega)]
  have hs2_part : ∀ v : Fin n, s2.mem (pb + v.1) = (part v).1 := fun v =>
    (hs2_mem _ (by region_omega) (by region_omega)).trans (hpart v)
  have hs2_mat : ∀ i j : Fin st.m, s2.mem (mb + i.1 * n + j.1) = W i j := fun i j => by
    have hlt := cell_lt_mul hmn i.isLt j.isLt
    exact (hs2_mem _ (by region_omega) (by region_omega)).trans (hmat i j)
  let better := if st.hasBest = 0 then 1 else if ord.lastKey ≤ st.bestWeight then 1 else 0
  let s2w : Memory.State := ⟨Function.update s2.mem (ob + 1) ord.lastKey, s2.frontier⟩
  have hf2w : ws + wsSize n ≤ s2w.frontier := hf2
  obtain ⟨hsafe_w, hws⟩ := writeSideProg_spec (w := w) ⟨pb, ob + 2, n, ord.last⟩ s2w
    (by region_omega) (by region_omega) (by region_omega) (by region_omega) (by region_omega) hfit1
  obtain ⟨-, -, ⟨hsw_fr, hsw_mod⟩, hsw_side⟩ := framedTriple_iff_realization.mp hws
  let phase : CutResult n := ⟨pullbackCut part {tv}, rowDeg W tv⟩
  let uargs : UpdateBestArgs := ⟨pb, ob, n, ord.last, ord.lastKey, better, st.bestWeight⟩
  let s3 := (Memory.spec 0).clientState s2 (updateBestProg uargs)
  let newBestW := if better = 1 then ord.lastKey else st.bestWeight
  have hs3_eq : s3 =
      if better = 1 then
        (Memory.spec 0).clientState s2w (writeSideProg ⟨pb, ob + 2, n, ord.last⟩)
      else s2 := by
    dsimp only [s3, updateBestProg, uargs]
    split_ifs <;> simp only [client_simps, s2w]
  have hval_res : (Memory.spec 0).clientResult s2 (updateBestProg uargs) = newBestW := by
    dsimp only [updateBestProg, uargs, newBestW]
    split_ifs <;> simp only [client_simps]
  have hbetter_spec :
      ∃ newBest : CutResult n,
        ws + wsSize n ≤ s3.frontier ∧
        s3.mem ob = n + 1 ∧
        newBestW = newBest.weight ∧
        s3.mem (ob + 1) = newBest.weight ∧
        (∀ v : Fin n, s3.mem (ob + 2 + v.1) = if v ∈ newBest.side then 1 else 0) ∧
        (∀ i j : Fin st.m, s3.mem (mb + i.1 * n + j.1) = W i j) ∧
        (∀ v : Fin n, s3.mem (pb + v.1) = (part v).1) ∧
        ((newBest = phase ∧
            run (n - 2 - p) (fun i j => W (i.cast hk.symm) (j.cast hk.symm))
              (fun v => (part v).cast hk) = stoerWagner W₀) ∨
         (∃ best : CutResult n, newBest = chooseCut best phase ∧
            chooseCut best (run (n - 2 - p) (fun i j => W (i.cast hk.symm) (j.cast hk.symm))
              (fun v => (part v).cast hk)) = stoerWagner W₀)) := by
    have hwrite_ok :
        let sw := (Memory.spec 0).clientState s2w (writeSideProg ⟨pb, ob + 2, n, ord.last⟩)
        ws + wsSize n ≤ sw.frontier ∧
        sw.mem ob = n + 1 ∧
        sw.mem (ob + 1) = phase.weight ∧
        (∀ v : Fin n, sw.mem (ob + 2 + v.1) = if v ∈ phase.side then 1 else 0) ∧
        (∀ i j : Fin st.m, sw.mem (mb + i.1 * n + j.1) = W i j) ∧
        (∀ v : Fin n, sw.mem (pb + v.1) = (part v).1) := by
      have hsw : ∀ addr, addr < s2w.frontier → (addr < ob + 2 ∨ ob + 2 + n ≤ addr) →
          ((Memory.spec 0).clientState s2w (writeSideProg ⟨pb, ob + 2, n, ord.last⟩)).mem addr =
            s2w.mem addr := fun addr ha hx => hsw_mod addr ha (by region_omega)
      refine ⟨hf2w.trans hsw_fr, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hsw ob (by region_omega) (by omega)]
        dsimp only [s2w]
        rw [Function.update_of_ne (by omega), hs2_mem ob (by region_omega) (by omega)]
        exact hout_l
      · rw [hsw (ob + 1) (by region_omega) (by omega)]
        exact (Function.update_self (ob + 1) ord.lastKey s2.mem).trans hord_key
      · intro v
        rw [hsw_side v.1 v.isLt]
        dsimp only [s2w]
        have hne_p : pb + v.1 ≠ ob + 1 := by region_omega
        simp only [Function.update_of_ne hne_p, hs2_part v, hord_last]
        have hiff : (part v).1 = tv.1 ↔ v ∈ pullbackCut part {tv} := by
          simp [pullbackCut, Fin.ext_iff]
        by_cases h1 : (part v).1 = tv.1
        · simp [h1, hiff.mp h1, phase]
        · simp [h1, mt hiff.mpr h1, phase]
      · intro i j
        have hlt := cell_lt_mul le_rfl (lt_of_lt_of_le i.isLt hmn) (lt_of_lt_of_le j.isLt hmn)
        rw [hsw _ (by region_omega) (by region_omega)]
        dsimp only [s2w]
        rw [Function.update_of_ne (by region_omega)]
        exact hs2_mat i j
      · intro v
        rw [hsw _ (by region_omega) (by region_omega)]
        dsimp only [s2w]
        rw [Function.update_of_ne (by region_omega)]
        exact hs2_part v
    obtain ⟨hw_fr, hw_ob, hw_ob1, hw_side, hw_mat, hw_part⟩ := hwrite_ok
    rcases hbest_inv with ⟨hhb0, hrun0⟩ | ⟨hhb1, best, hbw, hob1, hob2, hch0⟩
    · have hbet1 : better = 1 := by simp [better, hhb0]
      have hs3_w : s3 = (Memory.spec 0).clientState s2w
          (writeSideProg ⟨pb, ob + 2, n, ord.last⟩) := by rw [hs3_eq]; simp only [hbet1, ↓reduceIte]
      have hnb_w : newBestW = ord.lastKey := by simp only [newBestW, hbet1, ↓reduceIte]
      exact ⟨phase, hs3_w ▸ hw_fr, hs3_w ▸ hw_ob, hnb_w.trans hord_key, hs3_w ▸ hw_ob1,
        fun v => hs3_w ▸ hw_side v, fun i j => hs3_w ▸ hw_mat i j, fun v => hs3_w ▸ hw_part v,
        Or.inl ⟨rfl, hrun0⟩⟩
    · by_cases hle : rowDeg W tv ≤ best.weight
      · have hbet1 : better = 1 := by
          dsimp only [better]; rw [hhb1, hord_key, hbw]; simp [hle]
        have hch_eq : chooseCut best phase = phase := by simp [chooseCut, phase, hle]
        have hs3_w : s3 = (Memory.spec 0).clientState s2w
            (writeSideProg ⟨pb, ob + 2, n, ord.last⟩) := by
          rw [hs3_eq]; simp only [hbet1, ↓reduceIte]
        have hnb_w : newBestW = ord.lastKey := by simp only [newBestW, hbet1, ↓reduceIte]
        exact ⟨phase, hs3_w ▸ hw_fr, hs3_w ▸ hw_ob, hnb_w.trans hord_key, hs3_w ▸ hw_ob1,
          fun v => hs3_w ▸ hw_side v, fun i j => hs3_w ▸ hw_mat i j, fun v => hs3_w ▸ hw_part v,
          Or.inr ⟨best, hch_eq.symm, hch0⟩⟩
      · have hbet0 : better = 0 := by
          dsimp only [better]; rw [hhb1, hord_key, hbw]; simp [hle]
        have hch_eq : chooseCut best phase = best := by simp [chooseCut, phase, hle]
        have hs3_w : s3 = s2 := by rw [hs3_eq]; simp only [hbet0, Nat.zero_ne_one, ↓reduceIte]
        have hnb_w : newBestW = st.bestWeight := by
          simp only [newBestW, hbet0, Nat.zero_ne_one, ↓reduceIte]
        exact ⟨best, hs3_w ▸ hf2, hs3_w ▸ (hs2_mem ob (by region_omega) (by omega)).trans hout_l,
          hnb_w.trans hbw, hs3_w ▸ (hs2_mem (ob + 1) (by region_omega) (by omega)).trans hob1,
          fun v => hs3_w ▸ (hs2_mem (ob + 2 + v.1) (by region_omega) (by omega)).trans (hob2 v),
          fun i j => hs3_w ▸ hs2_mat i j, fun v => hs3_w ▸ hs2_part v,
          Or.inr ⟨best, hch_eq.symm, hch0⟩⟩
  obtain ⟨newBest, hs3_f, hs3_outl, hnbW, hs3_ob1, hs3_ob2, hs3_mat, hs3_part,
    hnewBest_rel⟩ := hbetter_spec
  have hupd : Memory.FramedTriple w s2 (updateBestProg uargs) (2 * n + 1)
      (Set.Ico (matBase ws) (outBase ws n + n + 2)) fun _ _ => True := by
    have hkey_fit : Fits w ord.lastKey := by
      rw [hord_key]; exact hfit_W.of_le (rowDeg_le_totalDoubledWeight W tv)
    unfold updateBestProg
    framed_triple
  have hsub1 : Set.Ico kb (kb + st.m) ∪ Set.Ico ub (ub + st.m) ⊆
      Set.Ico (matBase ws) (outBase ws n + n + 2) := by
    refine Set.union_subset ?_ ?_ <;> region_omega
  have hsafe : (2 < st.m → _) → PhaseStepSafe w (⟨n, ws⟩, st) s := fun hcon =>
    ⟨by region_omega, hfit4, by dsimp only; omega, hsafe_i, hsafe_o, fun _ => hsafe_w, hcon⟩
  unfold phaseStep
  by_cases hgt2 : 2 < st.m
  · obtain ⟨hcon_safe, hconM⟩ := phaseContract_spec hgt2 hm_eq hk hmn hC htotW hma_eq hst_ne
      hord_prev hord_last hfit_top hfit_tot s3 hs3_f hs3_outl hnbW hs3_ob1 hs3_ob2
      hs3_mat hs3_part hnewBest_rel
    refine ⟨hsafe fun _ => hcon_safe, ?_⟩
    have hst_le : st.m - 1 ≤ n := by omega
    exact Memory.FramedTriple.mono (Memory.FramedTriple.read_bind (by region_omega)
      (Memory.FramedTriple.seq hinit hsub1 (Memory.FramedTriple.seq hord hsub1
        (Memory.FramedTriple.seq hupd le_rfl (by rw [hval_res, ite_eq_left hgt2]; exact hconM)))))
      (by nlinarith only [hn, hmn, hst_le]) fun _ _ => id
  · -- Final phase (`st.m = 2`, `p + 1 = n - 1`).
    have hm_two : st.m = 2 :=
      (by omega : ∀ {m : ℕ}, 2 ≤ m → ¬2 < m → m = 2) hm2 hgt2
    have hp_last : p + 1 = n - 1 :=
      (by omega : ∀ {n p m : ℕ}, 2 ≤ n → p < n - 1 → m = n - p → m = 2 → p + 1 = n - 1)
        hn hp hm_eq hm_two
    have hm_end : st.m - 1 = n - (p + 1) :=
      (by omega : ∀ {n p m : ℕ}, 2 ≤ n → p < n - 1 → m = n - p → m = 2 → m - 1 = n - (p + 1))
        hn hp hm_eq hm_two
    have hrun0_eq :
        run (n - 2 - p) (fun i j => W (i.cast hk.symm) (j.cast hk.symm))
          (fun v => (part v).cast hk) = phase := by
      have hzero : n - 2 - p = 0 :=
        (by omega : ∀ {n p : ℕ}, 2 ≤ n → p + 1 = n - 1 → n - 2 - p = 0) hn hp_last
      rw [run_congr_step hzero hk hm_two W part]
      exact phase_run_zero W part hma_eq hm_two
    have hnewBest_eq : newBest = stoerWagner W₀ := by
      rcases hnewBest_rel with ⟨rfl, hrun0⟩ | ⟨best, rfl, hch0⟩
      · exact hrun0_eq.symm.trans hrun0
      · rw [← hrun0_eq]; exact hch0
    refine ⟨hsafe fun h => absurd h hgt2, ?_⟩
    exact Memory.FramedTriple.mono (Memory.FramedTriple.read_bind (by region_omega)
      (Memory.FramedTriple.seq hinit hsub1 (Memory.FramedTriple.seq hord hsub1
        (Memory.FramedTriple.seq hupd le_rfl (by
          rw [hval_res, ite_eq_right hgt2]
          exact Memory.FramedTriple.pure (c := 0) ⟨rfl, hs3_outl, hm_end, Or.inr (Or.inr
            ⟨hp_last, rfl, hs3_ob1.trans (congrArg CutResult.weight hnewBest_eq),
              fun v => by simpa [hnewBest_eq] using hs3_ob2 v⟩)⟩)))))
      (by nlinarith only [hn, hmn]) fun _ _ => id

private theorem phasesLoop_spec {w n ws : ℕ} (hn : 2 ≤ n) {W₀ : Fin n → Fin n → ℕ}
    (hW₀ : IsMultigraph W₀) (s₀ : Memory.State)
    (hf : ws + wsSize n ≤ s₀.frontier)
    (hfit_top : Fits w (ws + wsSize n)) (hfit4 : Fits w 4)
    (hfit_tot : Fits w (totalDoubledWeight W₀))
    (hout_len : s₀.mem (outBase ws n) = n + 1)
    (hmat₀ : ∀ i j : Fin n, s₀.mem (matBase ws + i.1 * n + j.1) = W₀ i j)
    (hpart₀ : ∀ v : Fin n, s₀.mem (partBase ws n + v.1) = v.1) :
    iterationSafe phaseStep PhaseStepSafe w ⟨n, ws⟩ (n - 1) ⟨n, 0, 0⟩ s₀ ∧
      Memory.FramedTriple w s₀ (phasesLoop ⟨n, ws⟩) ((23 * n ^ 2) * (n - 1))
        (Set.Ico (matBase ws) (outBase ws n + n + 2)) fun _ t =>
          t.mem (outBase ws n) = n + 1 ∧
          t.mem (outBase ws n + 1) = (stoerWagner W₀).weight ∧
          ∀ v : Fin n, t.mem (outBase ws n + 2 + v.1) =
            if v ∈ (stoerWagner W₀).side then 1 else 0 :=
  Memory.FramedTriple.iterate (fun p st t => PhaseInv ws t.frontier W₀ p st t)
    ⟨rfl, hout_len, rfl, Or.inl ⟨rfl, rfl, hmat₀, hpart₀⟩⟩
    (fun p hp st t hinv hm =>
      phaseStep_spec hn hW₀ hfit_top hfit4 hfit_tot p hp st t (hf.trans hm.1) hinv)
    fun _ _ ⟨_, hout_e, _, hbranch_e⟩ _ => by
      rcases hbranch_e with ⟨h0, _⟩ | ⟨_, hlt, _⟩ | ⟨_, _, hob1, hob2⟩
      · omega
      · omega
      · exact ⟨hout_e, hob1, hob2⟩

private theorem stoerWagnerProg_spec {w : ℕ} (I : StoerWagnerInput)
    (hwb : Fits w I.wordBound) :
    StoerWagnerProgSafe w I.n (Memory.State.init I.encode) ∧
      Memory.FramedTriple w (Memory.State.init I.encode) (stoerWagnerProg I.n)
        (26 * (I.n + 1) ^ 3) Set.univ fun r t =>
          outputList t.mem r = I.expectedOutput ∧ Fits w (r + I.expectedOutput.length) := by
  rcases I with ⟨n, W, hW⟩
  let I : StoerWagnerInput := ⟨n, W, hW⟩
  have hwsb : Fits w (workspaceBound n) := hwb.of_le (le_max_left _ _)
  have htot : Fits w (totalDoubledWeight W) := hwb.of_le (le_max_right _ _)
  set s₀ := Memory.State.init I.encode
  let ws := s₀.frontier
  let ob := outBase ws n
  have hws_eq : ws = 2 + n * n := by
    change I.encode.length + 1 = _
    simp [I, StoerWagnerInput.encode, Karger.length_flattenMatrix]
    omega
  have hfit_top : Fits w (ws + wsSize n) :=
    hwsb.of_le (by dsimp only [wsSize, workspaceBound] at hws_eq ⊢; rw [hws_eq]; nlinarith)
  have hfit4 : Fits w 4 := hwsb.of_le (by dsimp only [workspaceBound]; omega)
  have hfit_ob_len : Fits w (ob + I.expectedOutput.length) := by
    simp only [I, StoerWagnerInput.expectedOutput, List.length_cons, List.length_map,
      List.length_finRange]
    region_omega
  have hpos : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow 3 (n + 1) (Nat.succ_pos _)
  let s1 : Memory.State := ⟨Function.update s₀.mem ob (n + 1), ws + wsSize n⟩
  by_cases hn2 : n < 2
  · refine ⟨⟨hfit_top, hfit4, fun h => absurd hn2 h⟩, ?_⟩
    unfold stoerWagnerProg
    simp only [hn2, ↓reduceIte]
    framed_triple
    · rename_i hn1
      subst hn1
      refine ⟨?_, hfit_ob_len⟩
      simp only [StoerWagnerInput.expectedOutput, stoerWagner]
      rw [outputList_eq_iff]
      refine ⟨by
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_self]; rfl, fun i => ?_⟩
      rcases i with ⟨i, hi⟩
      dsimp only at hi
      have hi2 : i < 2 := by simpa using hi
      change (Function.update (Function.update (Function.update s₀.mem ob 2) (ob + 1) 0)
          (ob + 2) 0) (ob + 1 + i) = _
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · rw [show ob + 1 + 0 = ob + 1 by omega, Function.update_of_ne (by omega),
          Function.update_self]
        rfl
      · rw [show ob + 1 + 1 = ob + 2 by omega, Function.update_self]
        rfl
    · rename_i hn1
      obtain rfl : n = 0 := by omega
      refine ⟨?_, hfit_ob_len⟩
      simp only [StoerWagnerInput.expectedOutput, stoerWagner, List.finRange_zero, List.map_nil]
      rw [outputList_eq_iff]
      refine ⟨by rw [Function.update_of_ne (by omega), Function.update_self]; rfl,
        fun i => ?_⟩
      rcases i with ⟨i, hi⟩
      dsimp only at hi
      have hi0 : i = 0 := by simp only [List.length_cons, List.length_nil] at hi; omega
      subst hi0
      change (Function.update (Function.update s₀.mem ob 1) (ob + 1) 0) (ob + 1 + 0) = _
      simp
  · have hge2 : 2 ≤ n := Nat.le_of_not_lt hn2
    have hsq : 2 + n * n ≤ ws := hws_eq.ge
    obtain ⟨hsafe_c, hcp⟩ := copyWordsProg_spec (w := w) ⟨2, matBase ws, n * n⟩ s1
      (by region_omega) (by region_omega) (by region_omega) (by region_omega) (by region_omega)
      (by region_omega)
      (fun i hi => by
        dsimp only at hi
        dsimp only [s1]
        rw [Function.update_of_ne (by region_omega)]
        have hmem := Karger.holdsMatrix_init_single (r := 0) W ⟨i / n, Nat.div_lt_of_lt_mul hi⟩
          ⟨i % n, Nat.mod_lt _ (by omega)⟩
        have hidx : 2 + (i / n) * n + i % n = 2 + i := by
          have := Nat.div_add_mod i n; rw [Nat.mul_comm] at this; omega
        rw [hidx] at hmem
        change Fits w ((Data.init (r := 0) (n :: Karger.flattenMatrix W)).mem (2 + i))
        rw [hmem]
        exact htot.of_le (entry_le_totalDoubledWeight W _ _))
    let s2 := (Memory.spec 0).clientState s1 (copyWordsProg ⟨2, matBase ws, n * n⟩)
    obtain ⟨-, -, ⟨hs2_fr, hs2_mod⟩, hs2_mat⟩ := framedTriple_iff_realization.mp hcp
    have hf2 : ws + wsSize n ≤ s2.frontier := hs2_fr
    obtain ⟨hsafe_p, hip⟩ := initPartProg_spec (w := w) (partBase ws n) n s2
      (by region_omega) (by region_omega)
    let s3 := (Memory.spec 0).clientState s2 (initPartProg (partBase ws n, n))
    obtain ⟨-, -, ⟨hs3_fr, hs3_mod⟩, hs3_part⟩ := framedTriple_iff_realization.mp hip
    have hs3_outl : s3.mem ob = n + 1 := by
      rw [hs3_mod ob (by region_omega) (by region_omega),
        hs2_mod ob (by region_omega) (by region_omega)]
      exact Function.update_self _ _ _
    have hs3_mat : ∀ i j : Fin n, s3.mem (matBase ws + i.1 * n + j.1) = W i j := by
      intro i j
      have hlt : i.1 * n + j.1 < n * n := cell_lt_mul le_rfl i.isLt j.isLt
      rw [hs3_mod _ (by region_omega) (by region_omega),
        show matBase ws + i.1 * n + j.1 = matBase ws + (i.1 * n + j.1) by omega,
        hs2_mat _ hlt]
      dsimp only [s1]
      rw [Function.update_of_ne (by region_omega)]
      have hmem := Karger.holdsMatrix_init_single (r := 0) W i j
      change (Data.init (r := 0) (n :: Karger.flattenMatrix W)).mem (2 + (i.1 * n + j.1)) = W i j
      simpa [add_assoc] using hmem
    obtain ⟨hsafe_l, hph⟩ := phasesLoop_spec hge2 hW s3 (hf2.trans hs3_fr) hfit_top hfit4 htot
      hs3_outl hs3_mat hs3_part
    obtain ⟨-, -, -, hob_len, hob_w, hob_side⟩ := framedTriple_iff_realization.mp hph
    have hcube : 23 * n ^ 2 * (n - 1) ≤ 23 * n ^ 3 := by
      have := Nat.mul_le_mul_left (23 * n ^ 2) (Nat.sub_le n 1)
      nlinarith
    refine ⟨⟨hfit_top, hfit4, fun _ => ⟨hsafe_c, hsafe_p, hsafe_l⟩⟩, ?_⟩
    unfold stoerWagnerProg
    simp only [hn2, ↓reduceIte]
    framed_triple
    · refine ⟨?_, hfit_ob_len⟩
      rw [outputList_eq_iff]
      refine ⟨?_, fun i => ?_⟩
      · simpa [I, StoerWagnerInput.expectedOutput] using hob_len
      · have hlen_exp : I.expectedOutput.length = n + 1 := by
          simp [I, StoerWagnerInput.expectedOutput]
        change ((Memory.spec 0).clientState s3 (phasesLoop ⟨n, ws⟩)).mem (ob + 1 + i.1) = _
        rcases i with ⟨_ | v, hlt⟩
        · simpa [I, StoerWagnerInput.expectedOutput] using hob_w
        · have hv : v < n := by
            have : v + 1 < I.expectedOutput.length := hlt
            omega
          have haddr : ob + 1 + (v + 1) = outBase ws n + 2 + v := by dsimp only [ob]; omega
          rw [haddr]
          simpa [StoerWagnerInput.expectedOutput] using hob_side ⟨v, hv⟩
    · nlinarith

/-! ### Main `O(n³)` Word-RAM running-time theorem -/

public section

/-- **Stoer–Wagner global minimum cut on the Word-RAM (`O(n³)`):**
There is a single uniform deterministic width-blind standard-basis Word-RAM program
(`Program .standard r`, `¬prog.ReadsWidth`) that, on input
`I.encode = I.n :: Karger.flattenMatrix I.W`
for any weighted multigraph `I : StoerWagnerInput` at any word width `w` satisfying
`Fits w I.wordBound` (i.e., `I.wordBound < 2 ^ w`, where
`I.wordBound = max (workspaceBound I.n) (totalDoubledWeight I.W)` bounds all word values and
addresses, so a bit width `w` of order `log (I.n + 2) + log (totalDoubledWeight I.W + 2)` suffices),
outputs `I.expectedOutput` within `C * (I.n + 1) ^ 3` instructions (`Program.ComputesListInTime`).
For all `2 ≤ I.n`, `StoerWagnerInput.expectedOutput_spec` identifies this output with a non-trivial
global minimum cut and its weight `minCut I.W`. -/
theorem exists_stoerWagner_program :
    ∃ r C : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧
      prog.ComputesListInTime (fun _ I => I.encode) (fun I _ => C * (I.n + 1) ^ 3)
        (fun I w => Fits w I.wordBound) StoerWagnerInput.expectedOutput := by
  obtain ⟨m, C, emit, he⟩ := stoerWagnerProg_realizes
  let r := 1 + (1 + (1 + m + 1))
  let frontier : Fin r := ⟨0, by dsimp only [r]; omega⟩
  let src : Fin 1 → Fin r := fun i => Fin.natAdd 1 (Fin.castAdd (1 + m + 1) i)
  let tmp : Fin (1 + m + 1) → Fin r := fun i => Fin.natAdd 1 (Fin.natAdd 1 i)
  have hsrc : Function.Injective src := by fin_index [src]
  have htmp : Function.Injective tmp := by fin_index [tmp]
  have hd : ∀ i j, src i ≠ tmp j := by fin_index [src, tmp]
  have hf : ∀ j, tmp j ≠ frontier := by fin_index [tmp, frontier]
  have hs : ∀ i, src i ≠ frontier := by fin_index [src, frontier]
  let codeExact := Code.seq (inputPrefix frontier (tmp (Fin.last (1 + m))) src)
    (emit frontier src tmp)
  let code := codeExact.mapSimulates .exactStandard
  let prog := code.program (tmp (Fin.castAdd (m + 1) 0))
  have hnw_pre : ¬(inputPrefix frontier (tmp (Fin.last (1 + m))) src).ReadsWidth := by
    simp [inputPrefix, inputLoads, Code.ReadsWidth, Op.ReadsWidth, Op.exactBin, Basis.exact]
  have hnw_code : ¬code.ReadsWidth := by
    intro h
    have hex : codeExact.ReadsWidth := Code.readsWidth_of_mapSimulates .exactStandard h
    rcases hex with hpre | hbody
    · exact hnw_pre hpre
    · exact (he frontier src tmp htmp hd hf hs).1 hbody
  have hnw : ¬prog.ReadsWidth := Code.not_readsWidth_program hnw_code _
  refine ⟨r, 27 * (C + 7) + 1, prog, hnw, fun I w hwb hin_fits => ?_⟩
  have hwsb : Fits w (workspaceBound I.n) := hwb.of_le (le_max_left _ _)
  have hfit_len : Fits w (I.encode.length + 1) := by
    simp only [StoerWagnerInput.encode, List.length_cons, Karger.length_flattenMatrix]
    exact hwsb.of_le (by dsimp only [workspaceBound]; nlinarith)
  have hspec := stoerWagnerProg_spec I hwb
  have hlayout : ∀ j : Fin 1, I.encode.getD j.val 0 = wordWords I.n j := by
    rintro ⟨_ | _, h⟩
    · rfl
    · omega
  have hk : 1 ≤ I.encode.length := by simp [StoerWagnerInput.encode]
  obtain ⟨x, ex, hx, hm, hwords, _⟩ := inputPrefix_exec frontier (tmp (Fin.last (1 + m)))
    src I.encode hsrc (hf _) (fun j => hd j _) hs hk hfit_len hin_fits
  have harg : x.regs ∘ src = wordWords I.n := by
    funext j
    exact (hwords j).trans (hlayout j)
  obtain ⟨y, ey, hmem, hout, _⟩ := (he frontier src tmp htmp hd hf hs).2 w I.n x hx harg
    (hm.symm ▸ hspec.1) (hm.symm ▸ hspec.2.validHistory)
  rw [hm] at ey hmem hout
  obtain ⟨steps, hsteps, erun⟩ := ex.seq ey
  have erunStd := erun.mapSimulates .exactStandard
  have hr := erunStd.runs (pc := 0) (p := prog) (Program.Contains.self _).append_left
  have hhalt : step w prog ⟨code.size, y⟩ =
      .halt (wordWords ((Memory.spec w).clientResult (Memory.State.init I.encode)
        (stoerWagnerProg I.n)) 0) := by
    rw [← hout 0]
    exact step_halt (by simp [prog, Code.program])
  dsimp only [wordWords] at hhalt
  have hymem :
      y.mem = ((Memory.spec w).clientState (Memory.State.init I.encode)
        (stoerWagnerProg I.n)).mem :=
    congrArg Memory.State.mem hmem
  refine ⟨steps + 1, ⟨⟨code.size, y⟩, steps, _,
    by simpa only [Nat.zero_add, State.init, code] using hr,
    hhalt, hymem ▸ hspec.2.post.1, hspec.2.post.2, rfl⟩, ?_⟩
  have hmc := (framedTriple_iff_realization.mp hspec.2).2.1
  have hpos : 1 ≤ (I.n + 1) ^ 3 := Nat.one_le_pow 3 (I.n + 1) (Nat.succ_pos _)
  have hpos_mc : 1 ≤ memoryCost (stoerWagnerProg I.n) (Memory.State.init I.encode) + 0 + 1 := by
    omega
  have hstep_le : steps + 1 ≤ (C + 7) * (memoryCost (stoerWagnerProg I.n)
      (Memory.State.init I.encode) + 0 + 1) + 1 := by
    dsimp only at hsteps
    have hover := Nat.mul_le_mul_left 7 hpos_mc
    simp only [Nat.mul_one] at hover
    rw [Nat.add_mul]
    omega
  have hpoly : memoryCost (stoerWagnerProg I.n) (Memory.State.init I.encode) + 0 + 1 ≤
      27 * (I.n + 1) ^ 3 := by linarith only [hmc, hpos]
  have hmul : (C + 7) * (memoryCost (stoerWagnerProg I.n) (Memory.State.init I.encode) + 0 + 1) ≤
      (C + 7) * (27 * (I.n + 1) ^ 3) :=
    Nat.mul_le_mul_left (C + 7) hpoly
  have hring : (C + 7) * (27 * (I.n + 1) ^ 3) + (I.n + 1) ^ 3 =
      (27 * (C + 7) + 1) * (I.n + 1) ^ 3 := by ring
  linarith only [hstep_le, hmul, hpos, hring]

end

end Cslib.Algorithms.WordRAM.StoerWagner
