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
    let side : Finset (Fin I.n) := Finset.univ.filter fun v : Fin I.n => out[v.val + 1]? = some 1
    out.length = I.n + 1 ∧
      out.head? = some (minCut I.W) ∧
      IsNonTrivialCut side ∧
      cutWeight I.W side = minCut I.W := by
  obtain ⟨hnt, hcw, hw⟩ := stoerWagner_spec hn I.isMultigraph
  have hside :
      (Finset.univ.filter fun v : Fin I.n => I.expectedOutput[v.val + 1]? = some 1) =
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

private theorem matAddr_eq_iff {mb m str x₁ y₁ x₂ y₂ : ℕ} (hstr : m ≤ str)
    (hx₁ : x₁ < m) (hy₁ : y₁ < m) (hx₂ : x₂ < m) (hy₂ : y₂ < m)
    (heq : mb + x₁ * str + y₁ = mb + x₂ * str + y₂) :
    x₁ = x₂ ∧ y₁ = y₂ := by
  have ⟨hi, hj⟩ := Karger.matAddr_inj (wb := mb) hstr (i₁ := ⟨x₁, hx₁⟩) (j₁ := ⟨y₁, hy₁⟩)
    (i₂ := ⟨x₂, hx₂⟩) (j₂ := ⟨y₂, hy₂⟩) heq
  exact ⟨congrArg Fin.val hi, congrArg Fin.val hj⟩

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
    (hfirst : ∀ x : Fin m, used x = false → x.val < v.val → key x < key v) :
    ((List.finRange m).filter fun x => !used x).argmax key = some v := by
  rw [List.argmax_eq_some_iff]
  have hmem : ∀ x : Fin m, x ∈ (List.finRange m).filter (fun x => !used x) ↔ used x = false := by
    intro x
    simp [List.mem_filter, List.mem_finRange]
  refine ⟨(hmem v).mpr hv, fun a ha => hmax a ((hmem a).mp ha), fun a ha hle => ?_⟩
  have hlt : ¬(a.val < v.val) := fun h => not_lt_of_ge hle (hfirst a ((hmem a).mp ha) h)
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
    let s' := (Memory.spec 0).clientState s₀ (copyWordsProg a)
    iterationSafe copyStep CopyStepSafe w a a.len 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (copyWordsProg a)) ∧
      memoryCost (copyWordsProg a) s₀ ≤ 2 * a.len ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬(a.dst ≤ addr ∧ addr < a.dst + a.len) → s'.mem addr = s₀.mem addr) ∧
      (∀ i < a.len, s'.mem (a.dst + i) = s₀.mem (a.src + i)) := by
  have h := iterate_spec copyStep CopyStepSafe w a 2 a.len
    (fun k idx s =>
      idx = k ∧ s.frontier = s₀.frontier ∧
        (∀ j < a.len, s.mem (a.src + j) = s₀.mem (a.src + j)) ∧
        (∀ j < k, s.mem (a.dst + j) = s₀.mem (a.src + j)))
    (fun addr => a.dst ≤ addr ∧ addr < a.dst + a.len)
    (fun k hk idx s ⟨hidx, hfr, hsrc_eq, hdone⟩ => by
      subst idx
      refine ⟨by dsimp only [CopyStepSafe]; exact ⟨hfit_src.of_le (by omega),
          hfit_dst.of_le (by omega), hfit_len.of_le (by omega)⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold copyStep
        dsimp only
        exact validHistory_read_bind (by rw [hfr]; omega)
          (validHistory_write_bind (by rw [hfr]; omega) (by rw [hsrc_eq k hk]; exact hfit_vals k hk)
            (validHistory_pure w _ _))
      · unfold copyStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read, clientState_read, memoryCost_bind', memoryCost_write]
        simp [client_simps]
      · simp only [copyStep, client_simps, hfr]
      · intro addr haddr
        simp only [copyStep, client_simps]
        exact Function.update_of_ne (by omega) _ _
      · unfold copyStep
        dsimp only
        simp only [client_simps, hsrc_eq k hk]
        refine ⟨trivial, hfr, fun j hj => ?_, fun j hj => ?_⟩
        · rw [Function.update_of_ne (by omega)]
          exact hsrc_eq j hj
        · by_cases heq : j = k
          · subst heq; exact Function.update_self _ _ _
          · rw [Function.update_of_ne (by omega)]
            exact hdone j (by omega))
    0 s₀ ⟨rfl, rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hvh, hmc, hfr_e, hmod_e, _, _, _, hdone_e⟩ := h
  unfold copyWordsProg
  exact ⟨hsafe, hvh, hmc, hfr_e, hmod_e, hdone_e⟩

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
    let s' := (Memory.spec 0).clientState s₀ (initPartProg (base, n))
    iterationSafe initPartStep InitPartStepSafe w (base, n) n 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀
        ((Memory.spec w).clientHistory s₀ (initPartProg (base, n))) ∧
      memoryCost (initPartProg (base, n)) s₀ ≤ 1 * n ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬(base ≤ addr ∧ addr < base + n) → s'.mem addr = s₀.mem addr) ∧
      (∀ v : Fin n, s'.mem (base + v.val) = v.val) := by
  have h := iterate_spec initPartStep InitPartStepSafe w (base, n) 1 n
    (fun k idx s =>
      idx = k ∧ s.frontier = s₀.frontier ∧ ∀ v < k, s.mem (base + v) = v)
    (fun addr => base ≤ addr ∧ addr < base + n)
    (fun k hk idx s ⟨hidx, hfr, hdone⟩ => by
      subst idx
      refine ⟨by dsimp only [InitPartStepSafe]; exact ⟨hfit.of_le (by omega),
          hfit.of_le (by omega)⟩, ?_, ?_, ?_, ?_, ?_⟩
      · unfold initPartStep
        dsimp only
        exact validHistory_write_bind (by rw [hfr]; omega) (hfit.of_le (by omega))
          (validHistory_pure w _ _)
      · unfold initPartStep
        dsimp only
        rw [memoryCost_bind', memoryCost_write]
        simp [client_simps]
      · simp only [initPartStep, client_simps, hfr]
      · intro addr haddr
        simp only [initPartStep, client_simps]
        exact Function.update_of_ne (by omega) _ _
      · unfold initPartStep
        dsimp only
        simp only [client_simps]
        refine ⟨trivial, hfr, fun v hv => ?_⟩
        by_cases heq : v = k
        · subst heq; exact Function.update_self _ _ _
        · rw [Function.update_of_ne (by omega)]
          exact hdone v (by omega))
    0 s₀ ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hvh, hmc, hfr_e, hmod_e, _, _, hdone_e⟩ := h
  unfold initPartProg
  exact ⟨hsafe, hvh, hmc, hfr_e, hmod_e, fun v => hdone_e v.val v.isLt⟩

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
    let s' := (Memory.spec 0).clientState s₀ (initMAProg a)
    iterationSafe initMAStep InitMAStepSafe w a a.m 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (initMAProg a)) ∧
      memoryCost (initMAProg a) s₀ ≤ 2 * a.m ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬((a.kb ≤ addr ∧ addr < a.kb + a.m) ∨
        (a.ub ≤ addr ∧ addr < a.ub + a.m)) → s'.mem addr = s₀.mem addr) ∧
      (∀ i < a.m, s'.mem (a.kb + i) = 0 ∧ s'.mem (a.ub + i) = 0) := by
  have h := iterate_spec initMAStep InitMAStepSafe w a 2 a.m
    (fun k idx s =>
      idx = k ∧ s.frontier = s₀.frontier ∧
        ∀ i < k, s.mem (a.kb + i) = 0 ∧ s.mem (a.ub + i) = 0)
    (fun addr => (a.kb ≤ addr ∧ addr < a.kb + a.m) ∨ (a.ub ≤ addr ∧ addr < a.ub + a.m))
    (fun k hk idx s ⟨hidx, hfr, hdone⟩ => by
      subst idx
      refine ⟨by dsimp only [InitMAStepSafe]; exact ⟨hfit_k.of_le (by omega),
          hfit_u.of_le (by omega), hfit_k.of_le (by omega)⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold initMAStep
        dsimp only
        exact validHistory_write_bind (by rw [hfr]; omega) (fits_zero w)
          (validHistory_write_bind (by rw [hfr]; omega) (fits_zero w) (validHistory_pure w _ _))
      · unfold initMAStep
        dsimp only
        rw [memoryCost_bind', memoryCost_write, memoryCost_bind', memoryCost_write]
        simp [client_simps]
      · simp only [initMAStep, client_simps, hfr]
      · intro addr haddr
        simp only [initMAStep, client_simps]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      · unfold initMAStep
        dsimp only
        simp only [client_simps]
        refine ⟨trivial, hfr, fun i hi => ?_⟩
        by_cases heq : i = k
        · subst heq
          exact ⟨by rw [Function.update_of_ne (by omega), Function.update_self],
            Function.update_self _ _ _⟩
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hdone i (by omega))
    0 s₀ ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hvh, hmc, hfr_e, hmod_e, _, _, hdone_e⟩ := h
  unfold initMAProg
  exact ⟨hsafe, hvh, hmc, hfr_e, hmod_e, hdone_e⟩

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
    let s' := (Memory.spec 0).clientState s₀ (writeSideProg a)
    iterationSafe writeSideStep WriteSideStepSafe w a a.n 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (writeSideProg a)) ∧
      memoryCost (writeSideProg a) s₀ ≤ 2 * a.n ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬(a.dst ≤ addr ∧ addr < a.dst + a.n) → s'.mem addr = s₀.mem addr) ∧
      (∀ v < a.n, s'.mem (a.dst + v) = if s₀.mem (a.pb + v) = a.target then 1 else 0) := by
  have h := iterate_spec writeSideStep WriteSideStepSafe w a 2 a.n
    (fun k idx s =>
      idx = k ∧ s.frontier = s₀.frontier ∧
        (∀ v < a.n, s.mem (a.pb + v) = s₀.mem (a.pb + v)) ∧
        (∀ v < k, s.mem (a.dst + v) = if s₀.mem (a.pb + v) = a.target then 1 else 0))
    (fun addr => a.dst ≤ addr ∧ addr < a.dst + a.n)
    (fun k hk idx s ⟨hidx, hfr, hp_eq, hdone⟩ => by
      subst idx
      refine ⟨by dsimp only [WriteSideStepSafe]; exact ⟨hfit_p.of_le (by omega),
          hfit_d.of_le (by omega), hfit_p.of_le (by omega), hfit1⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold writeSideStep
        dsimp only
        exact validHistory_read_bind (by rw [hfr]; omega)
          (validHistory_write_bind (by rw [hfr]; omega)
            (by split_ifs <;> [exact hfit1; exact fits_zero w])
            (validHistory_pure w _ _))
      · unfold writeSideStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read, clientState_read, memoryCost_bind', memoryCost_write]
        simp [client_simps]
      · simp only [writeSideStep, client_simps, hfr]
      · intro addr haddr
        simp only [writeSideStep, client_simps]
        exact Function.update_of_ne (by omega) _ _
      · unfold writeSideStep
        dsimp only
        simp only [client_simps, hp_eq k hk]
        refine ⟨trivial, hfr, fun v hv => ?_, fun v hv => ?_⟩
        · rw [Function.update_of_ne (by omega)]
          exact hp_eq v hv
        · by_cases heq : v = k
          · subst heq; exact Function.update_self _ _ _
          · rw [Function.update_of_ne (by omega)]
            exact hdone v (by omega))
    0 s₀ ⟨rfl, rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hvh, hmc, hfr_e, hmod_e, _, _, _, hdone_e⟩ := h
  unfold writeSideProg
  exact ⟨hsafe, hvh, hmc, hfr_e, hmod_e, hdone_e⟩

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
    (hkey : ∀ x : Fin a.m, s₀.mem (a.kb + x.val) = key x)
    (hused : ∀ x : Fin a.m, s₀.mem (a.ub + x.val) = if used x then 1 else 0)
    (hex : ∃ x : Fin a.m, used x = false) :
    let res := (Memory.spec 0).clientResult s₀ (maPickMaxProg a)
    let s' := (Memory.spec 0).clientState s₀ (maPickMaxProg a)
    iterationSafe maPickStep MAPickStepSafe w a a.m ⟨0, 0, 0, 0⟩ s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (maPickMaxProg a)) ∧
      memoryCost (maPickMaxProg a) s₀ ≤ 2 * a.m ∧
      s' = s₀ ∧
      ∃ v : Fin a.m, res.bestIdx = v.val ∧ res.bestKey = key v ∧
        ((List.finRange a.m).filter fun x => !used x).argmax key = some v := by
  have h := iterate_spec maPickStep MAPickStepSafe w a 2 a.m
    (fun k st s =>
      s = s₀ ∧ st.i = k ∧
        ((st.has = 0 ∧ ∀ x : Fin a.m, x.val < k → used x = true) ∨
         (st.has = 1 ∧ ∃ b : Fin a.m, b.val < k ∧ st.bestIdx = b.val ∧ st.bestKey = key b ∧
           used b = false ∧
           (∀ x : Fin a.m, x.val < k → used x = false → key x ≤ key b) ∧
           (∀ x : Fin a.m, x.val < b.val → used x = false → key x < key b))))
    (fun _ => False)
    (fun k hk st s ⟨hs, hi, hinv⟩ => by
      subst s
      have hst_i : st.i = k := hi
      let kFin : Fin a.m := ⟨k, hk⟩
      have hu_k : s₀.mem (a.ub + k) = if used kFin then 1 else 0 := hused kFin
      have hk_k : s₀.mem (a.kb + k) = key kFin := hkey kFin
      refine ⟨by dsimp only [MAPickStepSafe]; rw [hst_i]; exact ⟨hfit_u.of_le (by omega),
          hfit_k.of_le (by omega), hfit_k.of_le (by omega), hfit1⟩, ?_, ?_, ?_, ?_, ?_⟩
      · unfold maPickStep
        dsimp only
        rw [hst_i]
        refine validHistory_read_bind (by omega) ?_
        exact validHistory_ite
          (fun _ => validHistory_read_bind (by omega)
            (validHistory_ite (fun _ => validHistory_pure w _ _)
              (fun _ => validHistory_ite (fun _ => validHistory_pure w _ _)
                (fun _ => validHistory_pure w _ _))))
          (fun _ => validHistory_pure w _ _)
      · unfold maPickStep
        dsimp only
        rw [hst_i]
        by_cases h1 : s₀.mem (a.ub + k) = 0
        · rw [memoryCost_bind', memoryCost_read, clientState_read, clientResult_read,
            memoryCost_ite, ite_eq_left h1, memoryCost_bind', memoryCost_read, clientState_read,
            clientResult_read, memoryCost_ite]
          by_cases h2 : st.has = 0
          · rw [ite_eq_left h2]; simp [client_simps]
          · rw [ite_eq_right h2, memoryCost_ite]; split_ifs <;> simp [client_simps]
        · rw [memoryCost_bind', memoryCost_read, clientState_read, clientResult_read,
            memoryCost_ite, ite_eq_right h1]
          simp [client_simps]
      · unfold maPickStep
        dsimp only
        rw [hst_i]
        simp only [client_simps]
        by_cases h1 : s₀.mem (a.ub + k) = 0
        · simp only [h1, ↓reduceIte, client_simps]
          by_cases h2 : st.has = 0
          · simp [h2, client_simps]
          · by_cases h3 : st.bestKey < s₀.mem (a.kb + k) <;> simp [h2, h3, client_simps]
        · simp [h1, client_simps]
      · intro addr _
        unfold maPickStep
        dsimp only
        rw [hst_i]
        simp only [client_simps]
        by_cases h1 : s₀.mem (a.ub + k) = 0
        · simp only [h1, ↓reduceIte, client_simps]
          by_cases h2 : st.has = 0
          · simp [h2, client_simps]
          · by_cases h3 : st.bestKey < s₀.mem (a.kb + k) <;> simp [h2, h3, client_simps]
        · simp [h1, client_simps]
      · unfold maPickStep
        dsimp only
        rw [hst_i]
        simp only [client_simps, hu_k]
        cases huk : used kFin
        · simp only [Bool.false_eq_true, ↓reduceIte, client_simps, hk_k]
          rcases hinv with ⟨hhas, hall⟩ | ⟨hhas, b, hbk, hbi, hbk_eq, hub, hmax, hfirst⟩
          · simp only [hhas, ↓reduceIte, client_simps]
            refine ⟨trivial, trivial,
              Or.inr ⟨trivial, kFin, Nat.lt_succ_self k, rfl, rfl, huk, ?_, ?_⟩⟩
            · intro x hx hux
              rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hx) with hlt | heq
              · exact absurd (hall x hlt) (by simp [hux])
              · have : x = kFin := Fin.ext heq; subst this; exact le_rfl
            · intro x hx hux
              exact absurd (hall x hx) (by simp [hux])
          · simp only [hhas, Nat.one_ne_zero, ↓reduceIte, hbk_eq, client_simps]
            by_cases hlt : key b < key kFin
            · simp only [hlt, ↓reduceIte, client_simps]
              refine ⟨trivial, trivial,
                Or.inr ⟨trivial, kFin, Nat.lt_succ_self k, rfl, rfl, huk, ?_, ?_⟩⟩
              · intro x hx hux
                rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hx) with hx' | heq
                · exact (hmax x hx' hux).trans (le_of_lt hlt)
                · have : x = kFin := Fin.ext heq; subst this; exact le_rfl
              · intro x hx hux
                exact lt_of_le_of_lt (hmax x hx hux) hlt
            · simp only [hlt, ↓reduceIte, client_simps]
              refine ⟨trivial, trivial,
                Or.inr ⟨trivial, b, Nat.lt_succ_of_lt hbk, hbi, rfl, hub, ?_, hfirst⟩⟩
              intro x hx hux
              rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hx) with hx' | heq
              · exact hmax x hx' hux
              · have : x = kFin := Fin.ext heq; subst this; omega
        · simp only [↓reduceIte, Nat.one_ne_zero, client_simps]
          rcases hinv with ⟨hhas, hall⟩ | ⟨hhas, b, hbk, hbi, hbk_eq, hub, hmax, hfirst⟩
          · refine ⟨trivial, trivial, Or.inl ⟨hhas, fun x hx => ?_⟩⟩
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hx) with hx' | heq
            · exact hall x hx'
            · have : x = kFin := Fin.ext heq; subst this; exact huk
          · refine ⟨trivial, trivial,
              Or.inr ⟨hhas, b, Nat.lt_succ_of_lt hbk, hbi, hbk_eq, hub, ?_, hfirst⟩⟩
            intro x hx hux
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hx) with hx' | heq
            · exact hmax x hx' hux
            · have : x = kFin := Fin.ext heq; subst this; simp [huk] at hux)
    ⟨0, 0, 0, 0⟩ s₀ ⟨rfl, rfl, Or.inl ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
  obtain ⟨hsafe, hvh, hmc, _, _, hs_e, _, hinv_e⟩ := h
  unfold maPickMaxProg
  refine ⟨hsafe, hvh, hmc, hs_e, ?_⟩
  rcases hinv_e with ⟨_, hall⟩ | ⟨_, b, _, hbi, hbk, hub, hmax, hfirst⟩
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
    (v : Fin a.m) (hv : a.v = v.val) (hm_str : a.m ≤ a.stride)
    (A : Finset (Fin a.m)) (hvA : v ∉ A) (used : Fin a.m → Bool)
    (s₀ : Memory.State)
    (hm_f : a.mb + a.m * a.stride ≤ s₀.frontier)
    (hk_f : a.kb + a.m ≤ s₀.frontier) (hu_f : a.ub + a.m ≤ s₀.frontier)
    (hdisj_mk : a.mb + a.m * a.stride ≤ a.kb) (hdisj_ku : a.kb + a.m ≤ a.ub)
    (hfit_m : Fits w (a.mb + a.m * a.stride))
    (hfit_k : Fits w (a.kb + a.m)) (hfit_u : Fits w (a.ub + a.m))
    (hfit_tot : Fits w (totalDoubledWeight W))
    (hmat : ∀ i j : Fin a.m, s₀.mem (a.mb + i.val * a.stride + j.val) = W i j)
    (hkey : ∀ y : Fin a.m, used y = false → s₀.mem (a.kb + y.val) = attachWeight W A y)
    (hused : ∀ y : Fin a.m, s₀.mem (a.ub + y.val) = if used y then 1 else 0) :
    let s' := (Memory.spec 0).clientState s₀ (maUpdateKeysProg a)
    iterationSafe maUpdateStep MAUpdStepSafe w a a.m 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (maUpdateKeysProg a)) ∧
      memoryCost (maUpdateKeysProg a) s₀ ≤ 4 * a.m ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬(a.kb ≤ addr ∧ addr < a.kb + a.m) → s'.mem addr = s₀.mem addr) ∧
      (∀ y : Fin a.m, used y = false →
        s'.mem (a.kb + y.val) = attachWeight W (insert v A) y) := by
  have h := iterate_spec maUpdateStep MAUpdStepSafe w a 4 a.m
    (fun k idx s =>
      idx = k ∧ s.frontier = s₀.frontier ∧
        (∀ addr, ¬(a.kb ≤ addr ∧ addr < a.kb + a.m) → s.mem addr = s₀.mem addr) ∧
        (∀ y : Fin a.m, used y = false →
          s.mem (a.kb + y.val) =
            if y.val < k then attachWeight W (insert v A) y else attachWeight W A y))
    (fun addr => a.kb ≤ addr ∧ addr < a.kb + a.m)
    (fun k hk idx s ⟨hidx, hfr, hframe, hkeys⟩ => by
      subst idx
      let yFin : Fin a.m := ⟨k, hk⟩
      have hcell : v.val * a.stride + k < a.m * a.stride := cell_lt_mul hm_str v.isLt hk
      have hu_k : s.mem (a.ub + k) = if used yFin then 1 else 0 := by
        rw [hframe (a.ub + k) (by omega), hused yFin]
      have hm_k : s.mem (a.mb + a.v * a.stride + k) = W v yFin := by
        rw [hv, hframe (a.mb + v.val * a.stride + k) (by omega), hmat v yFin]
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
      refine ⟨by dsimp only [MAUpdStepSafe]; exact ⟨hfit_u.of_le (by omega),
          hfit_k.of_le (by omega), hfit_m.of_le (by rw [hv]; omega), hfit_k.of_le (by omega),
          hsum_fit⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold maUpdateStep
        dsimp only
        refine validHistory_read_bind (by rw [hfr]; omega) (validHistory_ite (fun hu0 => ?_)
          (fun _ => validHistory_pure w _ _))
        exact validHistory_read_bind (by rw [hfr]; omega)
          (validHistory_read_bind (by rw [hfr, hv]; omega)
            (validHistory_write_bind (by rw [hfr]; omega) (hsum_fit hu0)
              (validHistory_pure w _ _)))
      · unfold maUpdateStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read, clientState_read, clientResult_read, memoryCost_ite]
        split_ifs
        · rw [memoryCost_bind', memoryCost_read, clientState_read, memoryCost_bind',
            memoryCost_read, clientState_read, memoryCost_bind', memoryCost_write]
          simp [client_simps]
        · simp [client_simps]
      · unfold maUpdateStep
        dsimp only
        simp only [client_simps]
        by_cases h1 : s.mem (a.ub + k) = 0
        · simp only [h1, ↓reduceIte, client_simps, hfr]
        · simp only [h1, ↓reduceIte, client_simps, hfr]
      · intro addr haddr
        unfold maUpdateStep
        dsimp only
        simp only [client_simps]
        by_cases h1 : s.mem (a.ub + k) = 0
        · simp only [h1, ↓reduceIte, client_simps]
          exact Function.update_of_ne (by omega) _ _
        · simp [h1, client_simps]
      · unfold maUpdateStep
        dsimp only
        simp only [client_simps, hu_k]
        cases huy : used yFin
        · simp only [Bool.false_eq_true, ↓reduceIte, client_simps, hm_k]
          have hky : s.mem (a.kb + k) = attachWeight W A yFin := by
            simpa [yFin] using hkeys yFin huy
          refine ⟨trivial, hfr, fun addr haddr => ?_, fun y hy => ?_⟩
          · rw [Function.update_of_ne (by omega)]
            exact hframe addr haddr
          · by_cases heq : y.val = k
            · have hy_eq : y = yFin := Fin.ext heq
              subst hy_eq
              rw [Function.update_self, hky, add_comm, ← attachWeight_insert W hvA]
              simp [yFin]
            · rw [Function.update_of_ne (by omega)]
              have := hkeys y hy
              by_cases hlt : y.val < k
              · simp only [hlt, Nat.lt_succ_of_lt hlt, ↓reduceIte] at this ⊢; exact this
              · have hnot : ¬(y.val < k + 1) := by omega
                simp only [hlt, hnot, ↓reduceIte] at this ⊢; exact this
        · simp only [↓reduceIte, Nat.one_ne_zero, client_simps]
          refine ⟨trivial, hfr, hframe, fun y hy => ?_⟩
          have hne : y.val ≠ k := fun h => by
            have hy_eq : y = yFin := Fin.ext h
            subst hy_eq
            simp [huy] at hy
          have := hkeys y hy
          by_cases hlt : y.val < k
          · simp only [hlt, Nat.lt_succ_of_lt hlt, ↓reduceIte] at this ⊢; exact this
          · have hnot : ¬(y.val < k + 1) := by omega
            simp only [hlt, hnot, ↓reduceIte] at this ⊢; exact this)
    0 s₀ ⟨rfl, rfl, fun _ _ => rfl, fun y hy => by simp [hkey y hy]⟩
  obtain ⟨hsafe, hvh, hmc, hfr_e, hmod_e, _, _, _, hkeys_e⟩ := h
  unfold maUpdateKeysProg
  exact ⟨hsafe, hvh, hmc, hfr_e, hmod_e, fun y hy => by simpa [y.isLt] using hkeys_e y hy⟩

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
    (hmat : ∀ i j : Fin a.m, s₀.mem (a.mb + i.val * a.stride + j.val) = W i j)
    (hinit : ∀ i < a.m, s₀.mem (a.kb + i) = 0 ∧ s₀.mem (a.ub + i) = 0) :
    let res := (Memory.spec 0).clientResult s₀ (maOrderProg a)
    let s' := (Memory.spec 0).clientState s₀ (maOrderProg a)
    iterationSafe maOrderStep MAOrderStepSafe w a a.m ⟨0, 0, 0⟩ s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (maOrderProg a)) ∧
      memoryCost (maOrderProg a) s₀ ≤ (6 * a.m + 2) * a.m ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬((a.kb ≤ addr ∧ addr < a.kb + a.m) ∨
        (a.ub ≤ addr ∧ addr < a.ub + a.m)) → s'.mem addr = s₀.mem addr) ∧
      ∃ (p : List (Fin a.m)) (s t : Fin a.m),
        maOrder W = p ++ [s, t] ∧ s ≠ t ∧
        res.prev = s.val ∧ res.last = t.val ∧ res.lastKey = rowDeg W t := by
  have h := iterate_spec maOrderStep MAOrderStepSafe w a (6 * a.m + 2) a.m
    (fun k st s =>
      s.frontier = s₀.frontier ∧
        (∀ addr, ¬((a.kb ≤ addr ∧ addr < a.kb + a.m) ∨
          (a.ub ≤ addr ∧ addr < a.ub + a.m)) → s.mem addr = s₀.mem addr) ∧
        ∃ (pref : List (Fin a.m)) (A : Finset (Fin a.m)) (used : Fin a.m → Bool),
          pref.length = k ∧ pref.Nodup ∧ (∀ x, x ∈ pref ↔ x ∈ A) ∧ A.card = k ∧
          (∀ x : Fin a.m, used x = true ↔ x ∈ A) ∧
          (∀ y : Fin a.m, used y = false → s.mem (a.kb + y.val) = attachWeight W A y) ∧
          (∀ y : Fin a.m, s.mem (a.ub + y.val) = if used y then 1 else 0) ∧
          maOrder W =
            pref ++ maSearch W (a.m - k) (attachWeight W A)
              ((List.finRange a.m).filter fun x => !used x) ∧
          (∀ (q : List (Fin a.m)) (u : Fin a.m), pref = q ++ [u] → st.last = u.val) ∧
          (∀ (q : List (Fin a.m)) (u v : Fin a.m), pref = q ++ [u, v] →
            st.prev = u.val ∧ st.last = v.val) ∧
          (k = a.m → ∀ (q : List (Fin a.m)) (u : Fin a.m), pref = q ++ [u] →
            st.lastKey = rowDeg W u))
    (fun addr => (a.kb ≤ addr ∧ addr < a.kb + a.m) ∨ (a.ub ≤ addr ∧ addr < a.ub + a.m))
    (fun k hk st s ⟨hfr, hframe, pref, A, used, hlen, hnd, hmemA, hcard, husedA,
        hkeys, hused_mem, hord_eq, hlast_eq, hprev_eq, _⟩ => by
      have hex : ∃ x : Fin a.m, used x = false := by
        by_contra hnone
        simp only [not_exists, Bool.not_eq_false] at hnone
        have huniv : A = Finset.univ :=
          Finset.eq_univ_iff_forall.mpr fun x => (husedA x).mp (hnone x)
        have hc : A.card = a.m := by rw [huniv, Finset.card_univ, Fintype.card_fin]
        omega
      let keyFn : Fin a.m → ℕ := fun x => s.mem (a.kb + x.val)
      have hkey_agree : ∀ x : Fin a.m, used x = false → keyFn x = attachWeight W A x := hkeys
      have hpick := maPickMaxProg_spec ⟨a.kb, a.ub, a.m⟩ used keyFn s
        (by rw [hfr]; exact hk_f) (by rw [hfr]; exact hu_f)
        hfit_k hfit_u hfit1 (fun _ => rfl) hused_mem hex
      obtain ⟨hsafe_p, hvh_p, hmc_p, hs_p, v, hv_idx, hv_key, harg_key⟩ := hpick
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
      let s2 : Memory.State := ⟨Function.update s.mem (a.ub + v.val) 1, s.frontier⟩
      have hs2_used : ∀ y : Fin a.m, s2.mem (a.ub + y.val) = if used' y then 1 else 0 := by
        intro y
        dsimp only [s2, used']
        by_cases hyv : y = v
        · subst hyv; simp
        · rw [Function.update_of_ne (by omega)]
          simp [hyv, hused_mem y]
      have hs2_mat : ∀ i j : Fin a.m, s2.mem (a.mb + i.val * a.stride + j.val) = W i j := by
        intro i j
        have hcell : i.val * a.stride + j.val < a.m * a.stride := cell_lt_mul hm_str i.isLt j.isLt
        dsimp only [s2]
        rw [Function.update_of_ne (by omega), hframe _ (by omega)]
        exact hmat i j
      have hs2_key : ∀ y : Fin a.m, used' y = false →
          s2.mem (a.kb + y.val) = attachWeight W A y := by
        intro y hy
        dsimp only [s2, used'] at hy ⊢
        have hyv : y ≠ v := fun h => by subst h; simp at hy
        simp only [hyv, ↓reduceIte] at hy
        rw [Function.update_of_ne (by omega)]
        exact hkeys y hy
      have hupd := maUpdateKeysProg_spec ⟨a.mb, a.kb, a.ub, a.stride, a.m, v.val⟩ hW v rfl hm_str
        A hvA used' s2
        (by dsimp only [s2]; rw [hfr]; exact hm_f)
        (by dsimp only [s2]; rw [hfr]; exact hk_f)
        (by dsimp only [s2]; rw [hfr]; exact hu_f)
        hdisj_mk hdisj_ku hfit_m hfit_k hfit_u hfit_tot hs2_mat hs2_key hs2_used
      obtain ⟨hsafe_u, hvh_u, hmc_u, hfr_u, hmod_u, hkeys_u⟩ := hupd
      have hv_lt : v.val < a.m := v.isLt
      have hf_pos : 0 < s.frontier := by rw [hfr]; omega
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only [MAOrderStepSafe]
        rw [hs_p, hv_idx]
        exact ⟨hsafe_p, hfit_u.of_le (by omega), hfit1, hsafe_u⟩
      · unfold maOrderStep
        dsimp only
        refine validHistory_read_bind hf_pos (validHistory_bind_step hvh_p ?_)
        rw [hs_p, hv_idx]
        exact validHistory_write_bind (by rw [hfr]; omega) hfit1
          (validHistory_bind_step hvh_u (validHistory_pure w _ _))
      · unfold maOrderStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read, clientState_read, memoryCost_bind', hs_p, hv_idx,
          memoryCost_bind', memoryCost_write]
        simp only [client_simps]
        have h1 : memoryCost (maPickMaxProg ⟨a.kb, a.ub, a.m⟩) s ≤ 2 * a.m := hmc_p
        have h2 : memoryCost (maUpdateKeysProg ⟨a.mb, a.kb, a.ub, a.stride, a.m, v.val⟩) s2 ≤
            4 * a.m := hmc_u
        dsimp only [s2] at h2 ⊢
        omega
      · unfold maOrderStep
        dsimp only
        simp only [client_simps, hs_p, hv_idx]
        exact hfr_u
      · intro addr haddr
        unfold maOrderStep
        dsimp only
        simp only [client_simps, hs_p, hv_idx]
        rw [hmod_u addr (fun h => haddr (Or.inl h))]
        dsimp only [s2]
        exact Function.update_of_ne (fun h => haddr (Or.inr ⟨by omega, by omega⟩)) _ _
      · unfold maOrderStep
        dsimp only
        simp only [client_simps, hs_p, hv_idx, hv_key]
        refine ⟨hfr_u.trans hfr, fun addr haddr => ?_,
          pref ++ [v], insert v A, used', by simp [hlen], ?_, ?_, ?_, hused'A,
          hkeys_u, fun y => ?_, ?_, ?_, ?_, ?_⟩
        · rw [hmod_u addr (fun h => haddr (Or.inl h))]
          dsimp only [s2]
          rw [Function.update_of_ne (fun h => haddr (Or.inr ⟨by omega, by omega⟩))]
          exact hframe addr haddr
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
        · rw [hmod_u (a.ub + y.val) (by dsimp only; omega)]
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
          rw [hkey_agree v hv_unused, hA_eq, attachWeight_erase_self hW v])
    ⟨0, 0, 0⟩ s₀
    ⟨rfl, fun _ _ => rfl, [], ∅, fun _ => false, rfl, List.nodup_nil, by simp, rfl, by simp,
      fun y _ => by simpa [attachWeight_empty] using (hinit y.val y.isLt).1,
      fun y => by simpa using (hinit y.val y.isLt).2,
      by
        have hfn : attachWeight W ∅ = fun _ => 0 := funext (attachWeight_empty W)
        simp [maOrder, hfn],
      fun q u h => by simpa using congrArg List.length h,
      fun q u v h => by simpa using congrArg List.length h,
      fun h0 => by omega⟩
  obtain ⟨hsafe, hvh, hmc, hfr_e, hmod_e, _, _, pref, A, used, hlen, hnd, _, _, _, _, _,
    hord_eq, _, hprev_eq, hlastKey_eq⟩ := h
  unfold maOrderProg
  have hord_pref : maOrder W = pref := by
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
    exact ⟨hsafe, hvh, hmc, hfr_e, hmod_e, q.reverse, s, t, hord_pref.trans hpref_eq, hst,
      hpr, hla, hlk⟩

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
    {sv tv : Fin a.m} (hst : sv ≠ tv) (hs : a.s = sv.val) (ht : a.t = tv.val)
    (hm_str : a.m ≤ a.stride) (s₀ : Memory.State)
    (hm_f : a.mb + a.m * a.stride ≤ s₀.frontier)
    (hfit_m : Fits w (a.mb + a.m * a.stride))
    (hfit_tot : Fits w (totalDoubledWeight W))
    (hmat : ∀ i j : Fin a.m, s₀.mem (a.mb + i.val * a.stride + j.val) = W i j) :
    let s' := (Memory.spec 0).clientState s₀ (mergeRowColProg a)
    iterationSafe mergeStep MergeStepSafe w a a.m 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (mergeRowColProg a)) ∧
      memoryCost (mergeRowColProg a) s₀ ≤ 6 * a.m ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬(a.mb ≤ addr ∧ addr < a.mb + a.m * a.stride) → s'.mem addr = s₀.mem addr) ∧
      (∀ i j : Fin a.m, s'.mem (a.mb + i.val * a.stride + j.val) = mergePair W sv tv i j) := by
  have hcell := fun x y (hx : x < a.m) (hy : y < a.m) => cell_lt_mul hm_str hx hy
  have hinj := fun x₁ y₁ x₂ y₂ (hx₁ : x₁ < a.m) (hy₁ : y₁ < a.m) (hx₂ : x₂ < a.m)
      (hy₂ : y₂ < a.m) (heq : a.mb + x₁ * a.stride + y₁ = a.mb + x₂ * a.stride + y₂) =>
    matAddr_eq_iff hm_str hx₁ hy₁ hx₂ hy₂ heq
  have h := iterate_spec mergeStep MergeStepSafe w a 6 a.m
    (fun k idx s =>
      idx = k ∧ s.frontier = s₀.frontier ∧
        ∀ i j : Fin a.m,
          s.mem (a.mb + i.val * a.stride + j.val) =
            if (i = sv ∨ i = tv) ∧ j.val < k then mergePair W sv tv i j
            else if (j = sv ∨ j = tv) ∧ i.val < k then mergePair W sv tv i j
            else W i j)
    (fun addr => a.mb ≤ addr ∧ addr < a.mb + a.m * a.stride)
    (fun k hk idx s ⟨hidx, hfr, hcur⟩ => by
      subst idx
      let kFin : Fin a.m := ⟨k, hk⟩
      have hcs := hcell sv.val k sv.isLt hk
      have hct := hcell tv.val k tv.isLt hk
      have hks := hcell k sv.val hk sv.isLt
      have hkt := hcell k tv.val hk tv.isLt
      have hread_s : s.mem (a.mb + a.s * a.stride + k) =
          if k = sv.val ∨ k = tv.val then s.mem (a.mb + a.s * a.stride + k) else W sv kFin := by
        split_ifs with hkv
        · rfl
        · rw [hs, hcur sv kFin]
          have hne_s : kFin ≠ sv := fun h => hkv (Or.inl (congrArg Fin.val h))
          have hne_t : kFin ≠ tv := fun h => hkv (Or.inr (congrArg Fin.val h))
          simp [hne_s, hne_t, kFin]
      have hread_t : s.mem (a.mb + a.t * a.stride + k) =
          if k = sv.val ∨ k = tv.val then s.mem (a.mb + a.t * a.stride + k) else W tv kFin := by
        split_ifs with hkv
        · rfl
        · rw [ht, hcur tv kFin]
          have hne_s : kFin ≠ sv := fun h => hkv (Or.inl (congrArg Fin.val h))
          have hne_t : kFin ≠ tv := fun h => hkv (Or.inr (congrArg Fin.val h))
          simp [hne_s, hne_t, kFin]
      have hsum_fit : k ≠ a.s → k ≠ a.t →
          Fits w (s.mem (a.mb + a.s * a.stride + k) + s.mem (a.mb + a.t * a.stride + k)) := by
        intro hks' hkt'
        have hkv : ¬(k = sv.val ∨ k = tv.val) := by omega
        rw [hread_s, hread_t]
        simp only [hkv, ↓reduceIte]
        exact hfit_tot.of_le (add_entry_le_totalDoubledWeight hst kFin)
      refine ⟨by dsimp only [MergeStepSafe]; exact ⟨hfit_m.of_le (by rw [hs]; omega),
          hfit_m.of_le (by rw [ht]; omega), hfit_m.of_le (by rw [hs]; omega),
          hfit_m.of_le (by rw [ht]; omega), hfit_m.of_le (by omega), hsum_fit⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold mergeStep
        dsimp only
        refine validHistory_read_bind (by rw [hfr, hs]; omega)
          (validHistory_read_bind (by rw [hfr, ht]; omega) ?_)
        have hval_fit : Fits w (if k = a.s then 0 else if k = a.t then 0 else
            s.mem (a.mb + a.s * a.stride + k) + s.mem (a.mb + a.t * a.stride + k)) := by
          split_ifs with h1 h2
          · exact fits_zero w
          · exact fits_zero w
          · exact hsum_fit h1 h2
        exact validHistory_write_bind (by rw [hfr, hs]; omega) hval_fit
          (validHistory_write_bind (by rw [hfr, hs]; omega) hval_fit
            (validHistory_write_bind (by rw [hfr, ht]; omega) (fits_zero w)
              (validHistory_write_bind (by rw [hfr, ht]; omega) (fits_zero w)
                (validHistory_pure w _ _))))
      · unfold mergeStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read, clientState_read, memoryCost_bind', memoryCost_read,
          clientState_read, memoryCost_bind', memoryCost_write, memoryCost_bind', memoryCost_write,
          memoryCost_bind', memoryCost_write, memoryCost_bind', memoryCost_write]
        simp [client_simps]
      · simp only [mergeStep, client_simps, hfr]
      · intro addr haddr
        simp only [mergeStep, client_simps]
        rw [Function.update_of_ne (by rw [ht]; omega),
          Function.update_of_ne (by rw [ht]; omega),
          Function.update_of_ne (by rw [hs]; omega),
          Function.update_of_ne (by rw [hs]; omega)]
      · unfold mergeStep
        dsimp only
        simp only [client_simps]
        refine ⟨trivial, hfr, fun i j => ?_⟩
        by_cases hit : i = tv ∧ j = kFin
        · rcases hit with ⟨hi_eq, hj_eq⟩
          subst i; subst j
          by_cases htk : tv.val = k
          · have : tv = kFin := Fin.ext htk
            subst this
            simp [kFin, ht, mergePair]
          · rw [ht, Function.update_of_ne (fun h => by
              have := (hinj tv.val k k tv.val tv.isLt hk hk tv.isLt h).1; omega),
              Function.update_self]
            simp [kFin, mergePair]
        · by_cases hjt : i = kFin ∧ j = tv
          · rcases hjt with ⟨hi_eq, hj_eq⟩
            subst i; subst j
            rw [ht, Function.update_self]
            simp [kFin, mergePair]
          · rw [Function.update_of_ne (fun h => hjt (by
                have ⟨h1, h2⟩ :=
                  hinj i.val j.val k tv.val i.isLt j.isLt hk tv.isLt (by rw [← ht]; exact h)
                exact ⟨Fin.ext h1, Fin.ext h2⟩)),
              Function.update_of_ne (fun h => hit (by
                have ⟨h1, h2⟩ :=
                  hinj i.val j.val tv.val k i.isLt j.isLt tv.isLt hk (by rw [← ht]; exact h)
                exact ⟨Fin.ext h1, Fin.ext h2⟩))]
            by_cases his : i = sv ∧ j = kFin
            · rcases his with ⟨hi_eq, hj_eq⟩
              subst i; subst j
              by_cases hsk : sv.val = k
              · have : sv = kFin := Fin.ext hsk
                subst this
                simp [kFin, hs, mergePair]
              · rw [hs, Function.update_of_ne (fun h => by
                  have := (hinj sv.val k k sv.val sv.isLt hk hk sv.isLt h).1; omega),
                  Function.update_self]
                have hne_sv : kFin ≠ sv := fun h => hsk (congrArg Fin.val h).symm
                by_cases htk : k = tv.val
                · have : kFin = tv := Fin.ext htk
                  subst this
                  simp [kFin, ht, mergePair]
                · have hne_tv : kFin ≠ tv := fun h => htk (congrArg Fin.val h)
                  have hkv : ¬(k = sv.val ∨ k = tv.val) := by omega
                  have hrs := hread_s; have hrt := hread_t
                  simp only [hkv, ↓reduceIte] at hrs hrt
                  rw [← hs, hrs, hrt]
                  simp [kFin, hs, ht, Ne.symm hsk, htk, mergePair, hne_sv.symm, hne_tv, hst]
            · by_cases hjs : i = kFin ∧ j = sv
              · rcases hjs with ⟨hi_eq, hj_eq⟩
                subst i; subst j
                rw [hs, Function.update_self]
                by_cases hsk : k = sv.val
                · have : kFin = sv := Fin.ext hsk
                  subst this
                  simp [kFin, mergePair]
                · by_cases htk : k = tv.val
                  · have : kFin = tv := Fin.ext htk
                    subst this
                    simp [kFin, ht, mergePair]
                  · have hne_sv : kFin ≠ sv := fun h => hsk (congrArg Fin.val h)
                    have hne_tv : kFin ≠ tv := fun h => htk (congrArg Fin.val h)
                    have hkv : ¬(k = sv.val ∨ k = tv.val) := by omega
                    have hrs := hread_s; have hrt := hread_t
                    simp only [hkv, ↓reduceIte] at hrs hrt
                    rw [← hs, hrs, hrt]
                    simp [kFin, hs, ht, hsk, htk, mergePair, hne_sv, hne_tv, hst,
                      hW.1 sv kFin, hW.1 tv kFin]
              · rw [Function.update_of_ne (fun h => hjs (by
                    have ⟨h1, h2⟩ := hinj i.val j.val k sv.val i.isLt j.isLt hk sv.isLt
                      (by rw [← hs]; exact h)
                    exact ⟨Fin.ext h1, Fin.ext h2⟩)),
                  Function.update_of_ne (fun h => his (by
                    have ⟨h1, h2⟩ := hinj i.val j.val sv.val k i.isLt j.isLt sv.isLt hk
                      (by rw [← hs]; exact h)
                    exact ⟨Fin.ext h1, Fin.ext h2⟩)),
                  hcur i j]
                have h1 : ¬((i = sv ∨ i = tv) ∧ j.val = k) := by
                  rintro ⟨rfl | rfl, hj⟩
                  · exact his ⟨rfl, Fin.ext hj⟩
                  · exact hit ⟨rfl, Fin.ext hj⟩
                have h2 : ¬((j = sv ∨ j = tv) ∧ i.val = k) := by
                  rintro ⟨rfl | rfl, hi⟩
                  · exact hjs ⟨Fin.ext hi, rfl⟩
                  · exact hjt ⟨Fin.ext hi, rfl⟩
                have hiff1 : ((i = sv ∨ i = tv) ∧ j.val < k + 1) ↔
                    ((i = sv ∨ i = tv) ∧ j.val < k) := by
                  constructor
                  · rintro ⟨ho, hlt⟩
                    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt) with hlt' | heq
                    · exact ⟨ho, hlt'⟩
                    · exact absurd ⟨ho, heq⟩ h1
                  · rintro ⟨ho, hlt⟩; exact ⟨ho, Nat.lt_succ_of_lt hlt⟩
                have hiff2 : ((j = sv ∨ j = tv) ∧ i.val < k + 1) ↔
                    ((j = sv ∨ j = tv) ∧ i.val < k) := by
                  constructor
                  · rintro ⟨ho, hlt⟩
                    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt) with hlt' | heq
                    · exact ⟨ho, hlt'⟩
                    · exact absurd ⟨ho, heq⟩ h2
                  · rintro ⟨ho, hlt⟩; exact ⟨ho, Nat.lt_succ_of_lt hlt⟩
                simp only [hiff1, hiff2])
    0 s₀ ⟨rfl, rfl, fun i j => by simp [hmat]⟩
  obtain ⟨hsafe, hvh, hmc, hfr_e, hmod_e, _, _, hcur_e⟩ := h
  unfold mergeRowColProg
  refine ⟨hsafe, hvh, hmc, hfr_e, hmod_e, fun i j => ?_⟩
  have hcur_ij := hcur_e i j
  simp only [i.isLt, j.isLt, and_true] at hcur_ij
  rw [hcur_ij]
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
    (tv : Fin (a.lastIdx + 1)) (ht : a.t = tv.val) (ht_lt : tv.val < a.lastIdx)
    (hm_str : a.lastIdx + 1 ≤ a.stride) (s₀ : Memory.State)
    (hm_f : a.mb + (a.lastIdx + 1) * a.stride ≤ s₀.frontier)
    (hfit_m : Fits w (a.mb + (a.lastIdx + 1) * a.stride))
    (hfit_vals : ∀ i j : Fin (a.lastIdx + 1), Fits w (M i j))
    (hmat : ∀ i j : Fin (a.lastIdx + 1), s₀.mem (a.mb + i.val * a.stride + j.val) = M i j) :
    let s' := (Memory.spec 0).clientState s₀ (compactRowColProg a)
    iterationSafe compactStep CompactStepSafe w a a.lastIdx 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (compactRowColProg a)) ∧
      memoryCost (compactRowColProg a) s₀ ≤ 3 * a.lastIdx ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬(a.mb ≤ addr ∧ addr < a.mb + a.lastIdx * a.stride) → s'.mem addr = s₀.mem addr) ∧
      (∀ i j : Fin a.lastIdx,
        s'.mem (a.mb + i.val * a.stride + j.val) = M (embedCompact tv i) (embedCompact tv j)) := by
  have hcell := fun x y (hx : x < a.lastIdx + 1) (hy : y < a.lastIdx + 1) =>
    cell_lt_mul hm_str hx hy
  have hcell_lt := fun x y (hx : x < a.lastIdx) (hy : y < a.lastIdx) =>
    cell_lt_mul (by omega : a.lastIdx ≤ a.stride) hx hy
  have hinj := fun x₁ y₁ x₂ y₂ (hx₁ : x₁ < a.lastIdx + 1) (hy₁ : y₁ < a.lastIdx + 1)
      (hx₂ : x₂ < a.lastIdx + 1) (hy₂ : y₂ < a.lastIdx + 1)
      (heq : a.mb + x₁ * a.stride + y₁ = a.mb + x₂ * a.stride + y₂) =>
    matAddr_eq_iff hm_str hx₁ hy₁ hx₂ hy₂ heq
  have h := iterate_spec compactStep CompactStepSafe w a 3 a.lastIdx
    (fun k idx s =>
      idx = k ∧ s.frontier = s₀.frontier ∧
        (∀ y : Fin a.lastIdx,
          s.mem (a.mb + a.lastIdx * a.stride + y.val) = M (Fin.last a.lastIdx) y.castSucc) ∧
        (∀ i j : Fin a.lastIdx,
          s.mem (a.mb + i.val * a.stride + j.val) =
            if (i.val = tv.val ∧ j.val < k) ∨ (j.val = tv.val ∧ i.val < k) then
              M (embedCompact tv i) (embedCompact tv j)
            else M i.castSucc j.castSucc))
    (fun addr => a.mb ≤ addr ∧ addr < a.mb + a.lastIdx * a.stride)
    (fun k hk idx s ⟨hidx, hfr, hlast_row, hcur⟩ => by
      subst idx
      let kFin : Fin a.lastIdx := ⟨k, hk⟩
      have hcl := hcell a.lastIdx k (Nat.lt_succ_self _) (Nat.lt_succ_of_lt hk)
      have hct := hcell_lt tv.val k ht_lt hk
      have hkt := hcell_lt k tv.val hk ht_lt
      have hlast_k : s.mem (a.mb + a.lastIdx * a.stride + k) =
          M (Fin.last a.lastIdx) kFin.castSucc := hlast_row kFin
      refine ⟨by dsimp only [CompactStepSafe]; exact ⟨hfit_m.of_le (by omega),
          hfit_m.of_le (by rw [ht]; nlinarith), hfit_m.of_le (by rw [ht]; nlinarith),
          hfit_m.of_le (by omega)⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold compactStep
        dsimp only
        have hval_fit :
            Fits w (if k = a.t then 0 else s.mem (a.mb + a.lastIdx * a.stride + k)) := by
          split_ifs
          · exact fits_zero w
          · rw [hlast_k]; exact hfit_vals _ _
        exact validHistory_read_bind (by rw [hfr]; omega)
          (validHistory_write_bind (by rw [hfr, ht]; nlinarith) hval_fit
            (validHistory_write_bind (by rw [hfr, ht]; nlinarith) hval_fit
              (validHistory_pure w _ _)))
      · unfold compactStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read, clientState_read, memoryCost_bind',
          memoryCost_write, memoryCost_bind', memoryCost_write]
        simp [client_simps]
      · simp only [compactStep, client_simps, hfr]
      · intro addr haddr
        simp only [compactStep, client_simps]
        rw [Function.update_of_ne (by rw [ht]; omega), Function.update_of_ne (by rw [ht]; omega)]
      · unfold compactStep
        dsimp only
        simp only [client_simps, hlast_k]
        refine ⟨trivial, hfr, fun y => ?_, fun i j => ?_⟩
        · have hne1 : a.mb + a.lastIdx * a.stride + y.val ≠ a.mb + k * a.stride + a.t := by
            have := hcell_lt k tv.val hk ht_lt
            rw [ht]; omega
          have hne2 : a.mb + a.lastIdx * a.stride + y.val ≠ a.mb + a.t * a.stride + k := by
            have := hcell_lt tv.val k ht_lt hk
            rw [ht]; omega
          rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
          exact hlast_row y
        · by_cases hit : i.val = tv.val ∧ j.val = k
          · rcases hit with ⟨hi_t, hj_k⟩
            by_cases htk : k = tv.val
            · rw [hi_t, hj_k, ht, htk, Function.update_self]
              simp [embedCompact, hi_t, hj_k, htk, hM.2]
            · rw [hi_t, hj_k, ht,
                Function.update_of_ne (fun h => htk (by
                  have := (hinj tv.val k k tv.val (Nat.lt_succ_of_lt ht_lt) (Nat.lt_succ_of_lt hk)
                    (Nat.lt_succ_of_lt hk) (Nat.lt_succ_of_lt ht_lt) h).1; omega)),
                Function.update_self]
              have hj_eq : j = kFin := Fin.ext hj_k
              subst hj_eq
              simp [embedCompact, kFin, hi_t, htk]
          · by_cases hjt : i.val = k ∧ j.val = tv.val
            · rcases hjt with ⟨hi_k, hj_t⟩
              rw [hi_k, hj_t, ht, Function.update_self]
              have hi_eq : i = kFin := Fin.ext hi_k
              subst hi_eq
              by_cases htk : k = tv.val
              · simp [embedCompact, kFin, hj_t, htk, hM.2]
              · dsimp only [embedCompact, kFin]
                simp [hj_t, htk, hM.1]
            · rw [Function.update_of_ne (fun h => hjt (by
                  have := hinj i.val j.val k tv.val (Nat.lt_succ_of_lt i.isLt)
                    (Nat.lt_succ_of_lt j.isLt) (Nat.lt_succ_of_lt hk) (Nat.lt_succ_of_lt ht_lt)
                    (by rw [← ht]; exact h)
                  exact this)),
                Function.update_of_ne (fun h => hit (by
                  have := hinj i.val j.val tv.val k (Nat.lt_succ_of_lt i.isLt)
                    (Nat.lt_succ_of_lt j.isLt) (Nat.lt_succ_of_lt ht_lt) (Nat.lt_succ_of_lt hk)
                    (by rw [← ht]; exact h)
                  exact this)),
                hcur i j]
              have hiff :
                  ((i.val = tv.val ∧ j.val < k + 1) ∨ (j.val = tv.val ∧ i.val < k + 1)) ↔
                  ((i.val = tv.val ∧ j.val < k) ∨ (j.val = tv.val ∧ i.val < k)) := by
                constructor
                · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
                  · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h2) with h2' | h2'
                    · exact Or.inl ⟨h1, h2'⟩
                    · exact absurd ⟨h1, h2'⟩ hit
                  · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h2) with h2' | h2'
                    · exact Or.inr ⟨h1, h2'⟩
                    · exact absurd ⟨h2', h1⟩ hjt
                · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
                  · exact Or.inl ⟨h1, Nat.lt_succ_of_lt h2⟩
                  · exact Or.inr ⟨h1, Nat.lt_succ_of_lt h2⟩
              simp only [hiff])
    0 s₀ ⟨rfl, rfl, fun y => hmat (Fin.last a.lastIdx) y.castSucc,
      fun i j => by simpa using hmat i.castSucc j.castSucc⟩
  obtain ⟨hsafe, hvh, hmc, hfr_e, hmod_e, _, _, _, hcur_e⟩ := h
  unfold compactRowColProg
  refine ⟨hsafe, hvh, hmc, hfr_e, hmod_e, fun i j => ?_⟩
  have hcur_ij := hcur_e i j
  simp only [i.isLt, j.isLt, and_true] at hcur_ij
  rw [hcur_ij]
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
    {sv tv : Fin (a.lastIdx + 1)} (hst : sv ≠ tv) (hs : a.s = sv.val) (ht : a.t = tv.val)
    (s₀ : Memory.State) (hp_f : a.pb + a.n ≤ s₀.frontier)
    (hfit_p : Fits w (a.pb + a.n)) (hfit_m : Fits w a.lastIdx)
    (hpart : ∀ v : Fin a.n, s₀.mem (a.pb + v.val) = (part v).val) :
    let s' := (Memory.spec 0).clientState s₀ (contractPartProg a)
    iterationSafe contractPartStep ContractPartStepSafe w a a.n 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (contractPartProg a)) ∧
      memoryCost (contractPartProg a) s₀ ≤ 2 * a.n ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬(a.pb ≤ addr ∧ addr < a.pb + a.n) → s'.mem addr = s₀.mem addr) ∧
      (∀ v : Fin a.n, s'.mem (a.pb + v.val) = (contractPart part sv tv hst v).val) := by
  have h := iterate_spec contractPartStep ContractPartStepSafe w a 2 a.n
    (fun k idx s =>
      idx = k ∧ s.frontier = s₀.frontier ∧
        ∀ v : Fin a.n, s.mem (a.pb + v.val) =
          if v.val < k then (contractPart part sv tv hst v).val else (part v).val)
    (fun addr => a.pb ≤ addr ∧ addr < a.pb + a.n)
    (fun k hk idx s ⟨hidx, hfr, hcur⟩ => by
      subst idx
      let vFin : Fin a.n := ⟨k, hk⟩
      have hv_cur : s.mem (a.pb + k) = (part vFin).val := by
        simpa [vFin] using hcur vFin
      have hval_eq :
          (if (if (part vFin).val = a.t then a.s else (part vFin).val) = a.lastIdx then a.t
            else if (part vFin).val = a.t then a.s else (part vFin).val) =
            (contractPart part sv tv hst vFin).val := by
        unfold contractPart compactIdx
        by_cases hpt : part vFin = tv
        · have hptv : (part vFin).val = a.t := by rw [hpt, ht]
          simp only [hpt, ↓reduceIte, hs, ht]
          split_ifs <;> simp
        · have hptv : (part vFin).val ≠ a.t := fun h => hpt (Fin.ext (h.trans ht))
          simp only [hpt, ↓reduceIte, ht]
          have hne : (part vFin).val ≠ tv.val := fun h => hpt (Fin.ext h)
          simp only [hne, ↓reduceIte]
          split_ifs <;> simp
      refine ⟨by dsimp only [ContractPartStepSafe]; exact ⟨hfit_p.of_le (by omega),
          hfit_p.of_le (by omega)⟩, ?_, ?_, ?_, ?_, ?_⟩
      · unfold contractPartStep
        dsimp only
        refine validHistory_read_bind (by rw [hfr]; omega)
          (validHistory_write_bind (by rw [hfr]; omega) ?_ (validHistory_pure w _ _))
        rw [hv_cur, hval_eq]
        exact hfit_m.of_le (Nat.le_of_lt (contractPart part sv tv hst vFin).isLt)
      · unfold contractPartStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read, clientState_read, memoryCost_bind', memoryCost_write]
        simp [client_simps]
      · simp only [contractPartStep, client_simps, hfr]
      · intro addr haddr
        simp only [contractPartStep, client_simps]
        exact Function.update_of_ne (by omega) _ _
      · unfold contractPartStep
        dsimp only
        simp only [client_simps, hv_cur, hval_eq]
        refine ⟨trivial, hfr, fun v => ?_⟩
        by_cases heq : v.val = k
        · have hv_eq : v = vFin := Fin.ext heq
          subst hv_eq
          simp [vFin]
        · rw [Function.update_of_ne (by omega), hcur v]
          by_cases hlt : v.val < k
          · simp [hlt, Nat.lt_succ_of_lt hlt]
          · have hnot : ¬(v.val < k + 1) := by omega
            simp [hlt, hnot])
    0 s₀ ⟨rfl, rfl, fun v => by simp [hpart v]⟩
  obtain ⟨hsafe, hvh, hmc, hfr_e, hmod_e, _, _, hcur_e⟩ := h
  unfold contractPartProg
  exact ⟨hsafe, hvh, hmc, hfr_e, hmod_e, fun v => by simpa [v.isLt] using hcur_e v⟩

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
        (∀ i j : Fin n, s.mem (matBase ws + i.val * n + j.val) = W₀ i j) ∧
        (∀ v : Fin n, s.mem (partBase ws n + v.val) = v.val)) ∨
     (0 < p ∧ p < n - 1 ∧ st.hasBest = 1 ∧
        ∃ (best : CutResult n) (W : Fin (n - p) → Fin (n - p) → ℕ)
          (part : Fin n → Fin (n - p)) (hk : n - p = (n - 2 - p) + 2),
          IsContractionOf W₀ part W ∧
          totalDoubledWeight W ≤ totalDoubledWeight W₀ ∧
          st.bestWeight = best.weight ∧
          s.mem (outBase ws n + 1) = best.weight ∧
          (∀ v : Fin n, s.mem (outBase ws n + 2 + v.val) = if v ∈ best.side then 1 else 0) ∧
          (∀ i j : Fin (n - p), s.mem (matBase ws + i.val * n + j.val) = W i j) ∧
          (∀ v : Fin n, s.mem (partBase ws n + v.val) = (part v).val) ∧
          chooseCut best (run (n - 2 - p) (fun i j => W (i.cast hk.symm) (j.cast hk.symm))
            (fun v => (part v).cast hk)) = stoerWagner W₀) ∨
     (p = n - 1 ∧ st.hasBest = 1 ∧
        s.mem (outBase ws n + 1) = (stoerWagner W₀).weight ∧
        (∀ v : Fin n, s.mem (outBase ws n + 2 + v.val) =
          if v ∈ (stoerWagner W₀).side then 1 else 0)))

private theorem phaseContract_spec {w n ws fr₀ p m prev last newBestW : ℕ}
    {W₀ : Fin n → Fin n → ℕ} {W : Fin m → Fin m → ℕ} {part : Fin n → Fin m}
    {pref : List (Fin m)} {sv tv : Fin m} {newBest : CutResult n}
    (hgt2 : 2 < m) (hm_eq : m = n - p) (hk : m = (n - 2 - p) + 2) (hmn : m ≤ n)
    (hC : IsContractionOf W₀ part W) (htotW : totalDoubledWeight W ≤ totalDoubledWeight W₀)
    (hma_eq : maOrder W = pref ++ [sv, tv]) (hst_ne : sv ≠ tv)
    (hprev : prev = sv.val) (hlast : last = tv.val)
    (hf : ws + wsSize n ≤ fr₀) (hfit_top : Fits w (ws + wsSize n))
    (hfit_tot : Fits w (totalDoubledWeight W₀))
    (s3 : Memory.State) (hs3_fr : s3.frontier = fr₀)
    (hs3_outl : s3.mem (outBase ws n) = n + 1)
    (hnbW : newBestW = newBest.weight)
    (hs3_ob1 : s3.mem (outBase ws n + 1) = newBest.weight)
    (hs3_ob2 : ∀ v : Fin n, s3.mem (outBase ws n + 2 + v.val) = if v ∈ newBest.side then 1 else 0)
    (hs3_mat : ∀ i j : Fin m, s3.mem (matBase ws + i.val * n + j.val) = W i j)
    (hs3_part : ∀ v : Fin n, s3.mem (partBase ws n + v.val) = (part v).val)
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
    let s6 := (Memory.spec 0).clientState s3 prog
    (iterationSafe mergeStep MergeStepSafe w ⟨mb, n, m, prev, last⟩ m 0 s3 ∧
      (last < lastIdx →
        iterationSafe compactStep CompactStepSafe w ⟨mb, n, lastIdx, last⟩ lastIdx 0 s4) ∧
      iterationSafe contractPartStep ContractPartStepSafe w
        ⟨pb, n, lastIdx, prev, last⟩ n 0 s5) ∧
      (Memory.spec w).ValidHistory s3 ((Memory.spec w).clientHistory s3 prog) ∧
      memoryCost prog s3 ≤ 6 * m + 3 * lastIdx + 2 * n ∧
      s6.frontier = fr₀ ∧
      (∀ addr, ¬(mb ≤ addr ∧ addr < outBase ws n + n + 2) → s6.mem addr = s3.mem addr) ∧
      PhaseInv ws fr₀ W₀ (p + 1) ((Memory.spec 0).clientResult s3 prog) s6 := by
  have hmn_sq : m * n ≤ n * n := Nat.mul_le_mul_right n hmn
  have hW : IsMultigraph W := hC.multigraph
  have hfit_W : Fits w (totalDoubledWeight W) := hfit_tot.of_le htotW
  let mb := matBase ws
  let pb := partBase ws n
  let ob := outBase ws n
  let lastIdx := m - 1
  have hm_succ : lastIdx + 1 = m := by omega
  have hmerge := mergeRowColProg_spec ⟨mb, n, m, prev, last⟩ hW hst_ne
    hprev hlast hmn s3
    (by rw [hs3_fr]; dsimp only [mb, matBase, wsSize] at hf ⊢; nlinarith)
    (hfit_top.of_le (by dsimp only [mb, matBase, wsSize]; nlinarith))
    hfit_W hs3_mat
  let s4 := (Memory.spec 0).clientState s3 (mergeRowColProg ⟨mb, n, m, prev, last⟩)
  have hs4_fr : s4.frontier = fr₀ := hmerge.2.2.2.1.trans hs3_fr
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
      (Memory.spec w).ValidHistory s4
        ((Memory.spec w).clientHistory s4 (compactIfProg ⟨mb, n, lastIdx, last⟩)) ∧
      memoryCost (compactIfProg ⟨mb, n, lastIdx, last⟩) s4 ≤ 3 * lastIdx ∧
      s5.frontier = fr₀ ∧
      (∀ addr, ¬(mb ≤ addr ∧ addr < mb + m * n) → s5.mem addr = s3.mem addr) ∧
      (∀ i j : Fin lastIdx, s5.mem (mb + i.val * n + j.val) = W' i j) := by
    by_cases hlt_last : last < lastIdx
    · have hcomp := compactRowColProg_spec ⟨mb, n, lastIdx, last⟩ hM_multi tv'
        hlast (by simpa [tv', hlast] using hlt_last) (by dsimp only; omega) s4
        (by rw [hs4_fr]; dsimp only [mb, matBase, wsSize] at hf ⊢; nlinarith)
        (hfit_top.of_le (by dsimp only [mb, matBase, wsSize]; nlinarith))
        hM_fit (fun i j => by
          simpa [M] using hmerge.2.2.2.2.2 (i.cast hm_succ) (j.cast hm_succ))
      have hcif : compactIfProg ⟨mb, n, lastIdx, last⟩ =
          compactRowColProg ⟨mb, n, lastIdx, last⟩ := by
        unfold compactIfProg; exact ite_eq_left hlt_last
      refine ⟨fun _ => hcomp.1, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hcif]; exact hcomp.2.1
      · rw [hcif]; exact hcomp.2.2.1
      · dsimp only [s5]; rw [hcif]; exact hcomp.2.2.2.1.trans hs4_fr
      · intro addr haddr
        dsimp only [s5]; rw [hcif]
        have hln : lastIdx * n ≤ m * n := Nat.mul_le_mul_right n (by omega)
        rw [hcomp.2.2.2.2.1 addr (fun hc => haddr ⟨hc.1, by dsimp only at hc; omega⟩),
          hmerge.2.2.2.2.1 addr (by dsimp only; exact haddr)]
      · intro i j
        dsimp only [s5]; rw [hcif]
        rw [hcomp.2.2.2.2.2 i j]
        unfold W' contractMatrix M mergePair
        simp [sv', tv', Fin.ext_iff]
    · have hcif : compactIfProg ⟨mb, n, lastIdx, last⟩ = pure 0 := by
        unfold compactIfProg; exact ite_eq_right hlt_last
      refine ⟨fun h => absurd h hlt_last, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hcif]; exact validHistory_pure w _ _
      · rw [hcif]; simp [client_simps]
      · dsimp only [s5]; rw [hcif]; exact hs4_fr
      · intro addr haddr
        dsimp only [s5]; rw [hcif]
        exact hmerge.2.2.2.2.1 addr (by dsimp only; exact haddr)
      · intro i j
        dsimp only [s5]; rw [hcif]
        have htv_eq : tv.val = lastIdx := by omega
        have hti : i.val ≠ tv'.val := by simp only [tv', Fin.val_cast]; omega
        have htj : j.val ≠ tv'.val := by simp only [tv', Fin.val_cast]; omega
        have he1 : embedCompact tv' i = i.castSucc := by simp [embedCompact, hti]
        have he2 : embedCompact tv' j = j.castSucc := by simp [embedCompact, htj]
        unfold W' contractMatrix
        rw [he1, he2]
        have hmij := hmerge.2.2.2.2.2 (i.castSucc.cast hm_succ) (j.castSucc.cast hm_succ)
        simpa [client_simps, mergePair, sv', tv', Fin.ext_iff] using hmij
  obtain ⟨hsafe_c, hvh_c, hmc_c, hs5_fr, hs5_mod, hs5_mat⟩ := hcomp_spec
  have hcp := contractPartProg_spec ⟨pb, n, lastIdx, prev, last⟩
    (fun v => (part v).cast hm_succ.symm) hst'
    (by simpa [sv'] using hprev) (by simpa [tv'] using hlast) s5
    (by rw [hs5_fr]; dsimp only [pb, partBase, wsSize] at hf ⊢; omega)
    (hfit_top.of_le (by dsimp only [pb, partBase, wsSize]; omega))
    (hfit_top.of_le (by dsimp only [wsSize]; omega))
    (fun v => by
      rw [hs5_mod _ (fun hc => by dsimp only [mb, pb, matBase, partBase] at hc; omega)]
      exact hs3_part v)
  let s6 := (Memory.spec 0).clientState s5 (contractPartProg ⟨pb, n, lastIdx, prev, last⟩)
  have hC_cast : IsContractionOf W₀ (fun v => (part v).cast hm_succ.symm)
      (fun i j => W (i.cast hm_succ) (j.cast hm_succ)) :=
    isContractionOf_cast hm_succ.symm hC
  have hC' : IsContractionOf W₀ part' W' := isContractionOf_contract hC_cast hst'
  have htotW' : totalDoubledWeight W' ≤ totalDoubledWeight W₀ := by
    have hdec := totalDoubledWeight_contractMatrix hC_cast.multigraph hst'
    rw [totalDoubledWeight_cast hm_succ.symm W] at hdec
    dsimp only [W']
    omega
  refine ⟨⟨hmerge.1, hsafe_c, hcp.1⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact validHistory_bind_step hmerge.2.1 (validHistory_bind_step hvh_c
      (validHistory_bind_step hcp.2.1 (validHistory_pure w _ _)))
  · rw [memoryCost_bind', memoryCost_bind', memoryCost_bind', memoryCost_pure]
    have c4 : memoryCost (mergeRowColProg ⟨mb, n, m, prev, last⟩) s3 ≤ 6 * m := hmerge.2.2.1
    have c5 : memoryCost (compactIfProg ⟨mb, n, lastIdx, last⟩) s4 ≤ 3 * lastIdx := hmc_c
    have c6 : memoryCost (contractPartProg ⟨pb, n, lastIdx, prev, last⟩) s5 ≤ 2 * n := hcp.2.2.1
    exact le_trans (Nat.add_le_add c4 (Nat.add_le_add c5 (Nat.add_le_add_right c6 0))) (by omega)
  · simp only [client_simps]
    exact hcp.2.2.2.1.trans hs5_fr
  · intro addr haddr
    simp only [client_simps]
    rw [hcp.2.2.2.2.1 addr (fun hc => haddr (by
        dsimp only [mb, pb, ob, matBase, partBase, outBase] at hc ⊢; omega)),
      hs5_mod addr (fun hc => haddr (by
        dsimp only [mb, ob, matBase, outBase] at hc ⊢; omega))]
  · simp only [client_simps]
    have hlast_eq : lastIdx = n - (p + 1) := by omega
    have hk' : n - (p + 1) = (n - 2 - (p + 1)) + 2 := by omega
    have hs6_out : ∀ addr, ob ≤ addr → s6.mem addr = s3.mem addr := fun addr ha => by
      rw [hcp.2.2.2.2.1 addr (fun hc => by
          dsimp only [pb, ob, partBase, outBase] at ha hc; omega),
        hs5_mod addr (fun hc => by dsimp only [mb, ob, matBase, outBase] at ha hc; omega)]
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
    refine ⟨hcp.2.2.2.1.trans hs5_fr, (hs6_out ob le_rfl).trans hs3_outl, by omega,
      Or.inr (Or.inl ⟨Nat.succ_pos p, by omega, rfl, newBest,
        fun i j => W' (i.cast hlast_eq.symm) (j.cast hlast_eq.symm),
        fun v => (part' v).cast hlast_eq, hk', isContractionOf_cast hlast_eq hC',
        by rw [totalDoubledWeight_cast hlast_eq W']; exact htotW', hnbW,
        (hs6_out (ob + 1) (by omega)).trans hs3_ob1,
        fun v => (hs6_out (ob + 2 + v.val) (by omega)).trans (hs3_ob2 v),
        fun i j => by
          rw [hcp.2.2.2.2.1 _ (by
            have hlt := cell_lt_mul (m := n) le_rfl
              (lt_of_lt_of_le i.isLt (Nat.sub_le n (p + 1)))
              (lt_of_lt_of_le j.isLt (Nat.sub_le n (p + 1)))
            dsimp only [mb, pb, matBase, partBase]; omega)]
          exact hs5_mat (i.cast hlast_eq.symm) (j.cast hlast_eq.symm),
        fun v => by simpa using hcp.2.2.2.2.2 v, ?_⟩)⟩
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

private theorem seq_phase_spec {α β γ δ : Type} {w : ℕ} {s s1 s2 s3 : Memory.State}
    {p1 : Memory.Prog α} {p2 : Memory.Prog β} {p3 : β → Memory.Prog γ}
    {p4 : β → γ → Memory.Prog δ} {ord : β} {v : γ} {c1 c2 c3 c4 C : ℕ}
    {P : δ → Memory.State → Prop} {Mod : ℕ → Prop}
    (hs0 : 0 < s.frontier)
    (hvh1 : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p1))
    (hs1 : (Memory.spec 0).clientState s p1 = s1)
    (hmc1 : memoryCost p1 s ≤ c1)
    (hvh2 : (Memory.spec w).ValidHistory s1 ((Memory.spec w).clientHistory s1 p2))
    (hord : (Memory.spec 0).clientResult s1 p2 = ord)
    (hs2 : (Memory.spec 0).clientState s1 p2 = s2)
    (hmc2 : memoryCost p2 s1 ≤ c2)
    (hvh3 : (Memory.spec w).ValidHistory s2 ((Memory.spec w).clientHistory s2 (p3 ord)))
    (hv : (Memory.spec 0).clientResult s2 (p3 ord) = v)
    (hs3 : (Memory.spec 0).clientState s2 (p3 ord) = s3)
    (hmc3 : memoryCost (p3 ord) s2 ≤ c3)
    (hvh4 : (Memory.spec w).ValidHistory s3 ((Memory.spec w).clientHistory s3 (p4 ord v)))
    (hmc4 : memoryCost (p4 ord v) s3 ≤ c4)
    (hfr : ((Memory.spec 0).clientState s3 (p4 ord v)).frontier = s.frontier)
    (hmod : ∀ addr, ¬Mod addr → ((Memory.spec 0).clientState s3 (p4 ord v)).mem addr = s.mem addr)
    (hP : P ((Memory.spec 0).clientResult s3 (p4 ord v))
      ((Memory.spec 0).clientState s3 (p4 ord v)))
    (hsum : 1 + c1 + c2 + c3 + c4 ≤ C) :
    let prog : Memory.Prog δ := do
      let _ ← Memory.read 0
      let _ ← p1
      let b ← p2
      let c ← p3 b
      p4 b c
    let s' := (Memory.spec 0).clientState s prog
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
      memoryCost prog s ≤ C ∧
      s'.frontier = s.frontier ∧
      (∀ addr, ¬Mod addr → s'.mem addr = s.mem addr) ∧
      P ((Memory.spec 0).clientResult s prog) s' := by
  subst hs1; subst hord; subst hs2; subst hv; subst hs3
  refine ⟨validHistory_read_bind hs0 (validHistory_bind_step hvh1
      (validHistory_bind_step hvh2 (validHistory_bind_step hvh3 hvh4))), ?_, ?_, ?_, ?_⟩
  · rw [memoryCost_bind', memoryCost_read, clientState_read, memoryCost_bind',
      memoryCost_bind', memoryCost_bind']
    omega
  · simpa only [client_simps] using hfr
  · intro addr haddr
    simpa only [client_simps] using hmod addr haddr
  · simpa only [client_simps] using hP

private theorem phaseStep_spec {w n ws fr₀ : ℕ} (hn : 2 ≤ n) {W₀ : Fin n → Fin n → ℕ}
    (hW₀ : IsMultigraph W₀) (hf : ws + wsSize n ≤ fr₀)
    (hfit_top : Fits w (ws + wsSize n)) (hfit4 : Fits w 4)
    (hfit_tot : Fits w (totalDoubledWeight W₀))
    (p : ℕ) (hp : p < n - 1) (st : PhaseState) (s : Memory.State)
    (hinv : PhaseInv ws fr₀ W₀ p st s) :
    PhaseStepSafe w (⟨n, ws⟩, st) s ∧
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (phaseStep (⟨n, ws⟩, st))) ∧
      memoryCost (phaseStep (⟨n, ws⟩, st)) s ≤ 23 * n ^ 2 ∧
      ((Memory.spec 0).clientState s (phaseStep (⟨n, ws⟩, st))).frontier = s.frontier ∧
      (∀ addr, ¬(matBase ws ≤ addr ∧ addr < outBase ws n + n + 2) →
        ((Memory.spec 0).clientState s (phaseStep (⟨n, ws⟩, st))).mem addr = s.mem addr) ∧
      PhaseInv ws fr₀ W₀ (p + 1)
        ((Memory.spec 0).clientResult s (phaseStep (⟨n, ws⟩, st)))
        ((Memory.spec 0).clientState s (phaseStep (⟨n, ws⟩, st))) := by
  have hf_pos : 0 < fr₀ := by dsimp only [wsSize] at hf; omega
  have hfit_ob2 : Fits w (outBase ws n + n + 2) :=
    hfit_top.of_le (by dsimp only [outBase, wsSize]; omega)
  have hfit1 : Fits w 1 := hfit4.of_le (by omega)
  obtain ⟨hfr, hout_l, hst_m, hbranch⟩ := hinv
  have hm_eq : st.m = n - p := hst_m
  have hm2 : 2 ≤ st.m := by omega
  have hmn : st.m ≤ n := by omega
  have hactive : ∃ (W : Fin st.m → Fin st.m → ℕ) (part : Fin n → Fin st.m)
      (hk : st.m = (n - 2 - p) + 2),
      IsContractionOf W₀ part W ∧
      totalDoubledWeight W ≤ totalDoubledWeight W₀ ∧
      (∀ i j : Fin st.m, s.mem (matBase ws + i.val * n + j.val) = W i j) ∧
      (∀ v : Fin n, s.mem (partBase ws n + v.val) = (part v).val) ∧
      ((st.hasBest = 0 ∧
          run (n - 2 - p) (fun i j => W (i.cast hk.symm) (j.cast hk.symm))
            (fun v => (part v).cast hk) = stoerWagner W₀) ∨
       (st.hasBest = 1 ∧ ∃ best : CutResult n,
          st.bestWeight = best.weight ∧
          s.mem (outBase ws n + 1) = best.weight ∧
          (∀ v : Fin n, s.mem (outBase ws n + 2 + v.val) = if v ∈ best.side then 1 else 0) ∧
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
  let mb := matBase ws
  let pb := partBase ws n
  let kb := keyBase ws n
  let ub := usedBase ws n
  let ob := outBase ws n
  have hinit := initMAProg_spec ⟨kb, ub, st.m⟩ s
    (by dsimp only [kb, keyBase]; rw [hfr]; dsimp only [wsSize] at hf; omega)
    (by dsimp only [ub, usedBase]; rw [hfr]; dsimp only [wsSize] at hf; omega)
    (by dsimp only [kb, ub, keyBase, usedBase]; omega)
    (hfit_top.of_le (by dsimp only [kb, keyBase, wsSize]; omega))
    (hfit_top.of_le (by dsimp only [ub, usedBase, wsSize]; omega))
  let s1 := (Memory.spec 0).clientState s (initMAProg ⟨kb, ub, st.m⟩)
  have hs1_fr : s1.frontier = s.frontier := hinit.2.2.2.1
  have hmat_disj : ∀ i j : Fin st.m,
      ¬((kb ≤ mb + i.val * n + j.val ∧ mb + i.val * n + j.val < kb + st.m) ∨
        (ub ≤ mb + i.val * n + j.val ∧ mb + i.val * n + j.val < ub + st.m)) := fun i j => by
    have hlt := cell_lt_mul le_rfl (lt_of_lt_of_le i.isLt hmn) (lt_of_lt_of_le j.isLt hmn)
    dsimp only [mb, kb, ub, matBase, keyBase, usedBase]; omega
  have hs1_mat : ∀ i j : Fin st.m, s1.mem (mb + i.val * n + j.val) = W i j := fun i j =>
    (hinit.2.2.2.2.1 _ (hmat_disj i j)).trans (hmat i j)
  have hord := maOrderProg_spec ⟨mb, kb, ub, n, st.m⟩ hm2 hW hmn s1
    (by rw [hs1_fr, hfr]; dsimp only [mb, matBase, wsSize] at hf ⊢; nlinarith)
    (by rw [hs1_fr, hfr]; dsimp only [kb, keyBase, wsSize] at hf ⊢; omega)
    (by rw [hs1_fr, hfr]; dsimp only [ub, usedBase, wsSize] at hf ⊢; omega)
    (by dsimp only [mb, kb, matBase, keyBase]; nlinarith)
    (by dsimp only [kb, ub, keyBase, usedBase]; omega)
    (hfit_top.of_le (by dsimp only [mb, matBase, wsSize]; nlinarith))
    (hfit_top.of_le (by dsimp only [kb, keyBase, wsSize]; omega))
    (hfit_top.of_le (by dsimp only [ub, usedBase, wsSize]; omega))
    hfit1 hfit_W hs1_mat hinit.2.2.2.2.2
  let ord := (Memory.spec 0).clientResult s1 (maOrderProg ⟨mb, kb, ub, n, st.m⟩)
  let s2 := (Memory.spec 0).clientState s1 (maOrderProg ⟨mb, kb, ub, n, st.m⟩)
  obtain ⟨hsafe_o, hvh_o, hmc_o, hs2_fr, hs2_mod, pref, sv, tv, hma_eq, hst_ne,
    hord_prev, hord_last, hord_key⟩ := hord
  change ord.prev = sv.val at hord_prev
  change ord.last = tv.val at hord_last
  change ord.lastKey = rowDeg W tv at hord_key
  have hs2_fr0 : s2.frontier = fr₀ := hs2_fr.trans (hs1_fr.trans hfr)
  have hs2_out : ∀ addr, ob ≤ addr → s2.mem addr = s.mem addr := fun addr ha => by
    rw [hs2_mod addr (by dsimp only [ob, kb, ub, outBase, keyBase, usedBase] at ha ⊢; omega),
      hinit.2.2.2.2.1 addr
        (by dsimp only [ob, kb, ub, outBase, keyBase, usedBase] at ha ⊢; omega)]
  have hs2_part : ∀ v : Fin n, s2.mem (pb + v.val) = (part v).val := fun v => by
    rw [hs2_mod _ (by dsimp only [pb, kb, ub, partBase, keyBase, usedBase]; omega),
      hinit.2.2.2.2.1 _ (by dsimp only [pb, kb, ub, partBase, keyBase, usedBase]; omega)]
    exact hpart v
  have hs2_mat : ∀ i j : Fin st.m, s2.mem (mb + i.val * n + j.val) = W i j := fun i j =>
    (hs2_mod _ (hmat_disj i j)).trans (hs1_mat i j)
  let better := if st.hasBest = 0 then 1 else if ord.lastKey ≤ st.bestWeight then 1 else 0
  let s2w : Memory.State := ⟨Function.update s2.mem (ob + 1) ord.lastKey, s2.frontier⟩
  have hws := writeSideProg_spec ⟨pb, ob + 2, n, ord.last⟩ s2w
    (by dsimp only [s2w]; rw [hs2_fr0]; dsimp only [pb, partBase, wsSize] at hf ⊢; omega)
    (by dsimp only [s2w]; rw [hs2_fr0]; dsimp only [ob, outBase, wsSize] at hf ⊢; omega)
    (by dsimp only [pb, ob, partBase, outBase]; omega)
    (hfit_top.of_le (by dsimp only [pb, partBase, wsSize]; omega))
    (hfit_top.of_le (by dsimp only [ob, outBase, wsSize]; omega))
    hfit1
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
  have hs3_outside : ∀ addr, ¬(matBase ws ≤ addr ∧ addr < outBase ws n + n + 2) →
      s3.mem addr = s.mem addr := by
    intro addr haddr
    rw [hs3_eq]
    split_ifs
    · rw [hws.2.2.2.2.1 addr (by dsimp only [mb, ob, matBase, outBase] at haddr ⊢; omega)]
      dsimp only [s2w]
      rw [Function.update_of_ne (by dsimp only [mb, ob, matBase, outBase] at haddr ⊢; omega),
        hs2_mod addr (by
          dsimp only [mb, kb, ub, ob, matBase, keyBase, usedBase, outBase] at haddr ⊢; omega),
        hinit.2.2.2.2.1 addr (by
          dsimp only [mb, kb, ub, ob, matBase, keyBase, usedBase, outBase] at haddr ⊢; omega)]
    · rw [hs2_mod addr (by
          dsimp only [mb, kb, ub, ob, matBase, keyBase, usedBase, outBase] at haddr ⊢; omega),
        hinit.2.2.2.2.1 addr (by
          dsimp only [mb, kb, ub, ob, matBase, keyBase, usedBase, outBase] at haddr ⊢; omega)]
  have hbetter_spec :
      ∃ newBest : CutResult n,
        s3.frontier = fr₀ ∧
        s3.mem ob = n + 1 ∧
        newBestW = newBest.weight ∧
        s3.mem (ob + 1) = newBest.weight ∧
        (∀ v : Fin n, s3.mem (ob + 2 + v.val) = if v ∈ newBest.side then 1 else 0) ∧
        (∀ i j : Fin st.m, s3.mem (mb + i.val * n + j.val) = W i j) ∧
        (∀ v : Fin n, s3.mem (pb + v.val) = (part v).val) ∧
        ((newBest = phase ∧
            run (n - 2 - p) (fun i j => W (i.cast hk.symm) (j.cast hk.symm))
              (fun v => (part v).cast hk) = stoerWagner W₀) ∨
         (∃ best : CutResult n, newBest = chooseCut best phase ∧
            chooseCut best (run (n - 2 - p) (fun i j => W (i.cast hk.symm) (j.cast hk.symm))
              (fun v => (part v).cast hk)) = stoerWagner W₀)) := by
    have hwrite_ok :
        let sw := (Memory.spec 0).clientState s2w (writeSideProg ⟨pb, ob + 2, n, ord.last⟩)
        sw.frontier = fr₀ ∧
        sw.mem ob = n + 1 ∧
        sw.mem (ob + 1) = phase.weight ∧
        (∀ v : Fin n, sw.mem (ob + 2 + v.val) = if v ∈ phase.side then 1 else 0) ∧
        (∀ i j : Fin st.m, sw.mem (mb + i.val * n + j.val) = W i j) ∧
        (∀ v : Fin n, sw.mem (pb + v.val) = (part v).val) := by
      refine ⟨hws.2.2.2.1.trans hs2_fr0, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hws.2.2.2.2.1 ob (by dsimp only; omega)]
        dsimp only [s2w]
        rw [Function.update_of_ne (by omega), hs2_out ob le_rfl]
        exact hout_l
      · rw [hws.2.2.2.2.1 (ob + 1) (by dsimp only; omega)]
        exact (Function.update_self (ob + 1) ord.lastKey s2.mem).trans hord_key
      · intro v
        rw [hws.2.2.2.2.2 v.val v.isLt]
        dsimp only
        dsimp only [s2w]
        have hne_p : pb + v.val ≠ ob + 1 := by dsimp only [pb, ob, partBase, outBase]; omega
        simp only [Function.update_of_ne hne_p, hs2_part v, hord_last]
        have hiff : (part v).val = tv.val ↔ v ∈ pullbackCut part {tv} := by
          simp [pullbackCut, Fin.ext_iff]
        by_cases h1 : (part v).val = tv.val
        · simp [h1, hiff.mp h1, phase]
        · simp [h1, mt hiff.mpr h1, phase]
      · intro i j
        have hlt := cell_lt_mul le_rfl (lt_of_lt_of_le i.isLt hmn) (lt_of_lt_of_le j.isLt hmn)
        rw [hws.2.2.2.2.1 _ (by dsimp only [mb, ob, matBase, outBase]; omega)]
        dsimp only [s2w]
        rw [Function.update_of_ne (by dsimp only [mb, ob, matBase, outBase]; omega)]
        exact hs2_mat i j
      · intro v
        rw [hws.2.2.2.2.1 _ (by dsimp only [pb, ob, partBase, outBase]; omega)]
        dsimp only [s2w]
        rw [Function.update_of_ne (by dsimp only [pb, ob, partBase, outBase]; omega)]
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
        exact ⟨best, hs3_w ▸ hs2_fr0, hs3_w ▸ (hs2_out ob le_rfl).trans hout_l, hnb_w.trans hbw,
          hs3_w ▸ (hs2_out (ob + 1) (by omega)).trans hob1,
          fun v => hs3_w ▸ (hs2_out (ob + 2 + v.val) (by omega)).trans (hob2 v),
          fun i j => hs3_w ▸ hs2_mat i j, fun v => hs3_w ▸ hs2_part v,
          Or.inr ⟨best, hch_eq.symm, hch0⟩⟩
  obtain ⟨newBest, hs3_fr, hs3_outl, hnbW, hs3_ob1, hs3_ob2, hs3_mat, hs3_part,
    hnewBest_rel⟩ := hbetter_spec
  have hvh_better :
      (Memory.spec w).ValidHistory s2
        ((Memory.spec w).clientHistory s2 (updateBestProg uargs)) := by
    unfold updateBestProg
    refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure w _ _)
    refine validHistory_write_bind
      (by rw [hs2_fr0]; dsimp only [uargs, ob, outBase, wsSize] at hf ⊢; omega)
      (by dsimp only [uargs]; rw [hord_key]; exact hfit_W.of_le (rowDeg_le_totalDoubledWeight W tv))
      (validHistory_bind_step hws.2.1 (validHistory_pure w _ _))
  have hmc_better : memoryCost (updateBestProg uargs) s2 ≤ 2 * n + 1 := by
    unfold updateBestProg
    rw [memoryCost_ite]
    split_ifs
    · rw [memoryCost_bind', memoryCost_write, memoryCost_bind']
      have hcost_ws : memoryCost (writeSideProg ⟨pb, ob + 2, n, ord.last⟩) s2w ≤ 2 * n :=
        hws.2.2.1
      change 1 + (memoryCost (writeSideProg ⟨pb, ob + 2, n, ord.last⟩) s2w +
        memoryCost (pure ord.lastKey) _) ≤ 2 * n + 1
      rw [memoryCost_pure]
      omega
    · simp [client_simps]
  have hmc_init : memoryCost (initMAProg ⟨kb, ub, st.m⟩) s ≤ 2 * st.m := hinit.2.2.1
  have hmc_ord : memoryCost (maOrderProg ⟨mb, kb, ub, n, st.m⟩) s1 ≤
      (6 * st.m + 2) * st.m := hmc_o
  let p3f : MAOrderState → Memory.Prog ℕ := fun o =>
    let bet := if st.hasBest = 0 then 1 else if o.lastKey ≤ st.bestWeight then 1 else 0
    updateBestProg ⟨pb, ob, n, o.last, o.lastKey, bet, st.bestWeight⟩
  let p4f : MAOrderState → ℕ → Memory.Prog PhaseState := fun o nbw =>
    if 2 < st.m then do
      let _ ← mergeRowColProg ⟨mb, n, st.m, o.prev, o.last⟩
      let lastIdx := st.m - 1
      let _ ← compactIfProg ⟨mb, n, lastIdx, o.last⟩
      let _ ← contractPartProg ⟨pb, n, lastIdx, o.prev, o.last⟩
      pure ⟨st.m - 1, 1, nbw⟩
    else
      pure ⟨st.m - 1, 1, nbw⟩
  have hfinish := fun (c4 : ℕ)
      (hvh4 : (Memory.spec w).ValidHistory s3
        ((Memory.spec w).clientHistory s3 (p4f ord newBestW)))
      (hmc4 : memoryCost (p4f ord newBestW) s3 ≤ c4)
      (hfr4 : ((Memory.spec 0).clientState s3 (p4f ord newBestW)).frontier = s.frontier)
      (hmod4 : ∀ addr, ¬(matBase ws ≤ addr ∧ addr < outBase ws n + n + 2) →
        ((Memory.spec 0).clientState s3 (p4f ord newBestW)).mem addr = s.mem addr)
      (hP4 : PhaseInv ws fr₀ W₀ (p + 1)
        ((Memory.spec 0).clientResult s3 (p4f ord newBestW))
        ((Memory.spec 0).clientState s3 (p4f ord newBestW)))
      (hbud : 1 + 2 * st.m + (6 * st.m + 2) * st.m + (2 * n + 1) + c4 ≤ 23 * n ^ 2) =>
    seq_phase_spec (p1 := initMAProg ⟨kb, ub, st.m⟩)
      (p2 := maOrderProg ⟨mb, kb, ub, n, st.m⟩) (p3 := p3f) (p4 := p4f)
      (s1 := s1) (s2 := s2) (s3 := s3) (ord := ord) (v := newBestW)
      (c1 := 2 * st.m) (c2 := (6 * st.m + 2) * st.m) (c3 := 2 * n + 1)
      (c4 := c4) (C := 23 * n ^ 2)
      (P := PhaseInv ws fr₀ W₀ (p + 1))
      (Mod := fun addr => matBase ws ≤ addr ∧ addr < outBase ws n + n + 2)
      (by rw [hfr]; exact hf_pos) hinit.2.1 rfl hmc_init
      hvh_o rfl rfl hmc_ord hvh_better hval_res rfl hmc_better
      hvh4 hmc4 hfr4 hmod4 hP4 hbud
  by_cases hgt2 : 2 < st.m
  · have hcon := phaseContract_spec hgt2 hm_eq hk hmn hC htotW hma_eq hst_ne
      hord_prev hord_last hf hfit_top hfit_tot s3 hs3_fr hs3_outl hnbW hs3_ob1 hs3_ob2
      hs3_mat hs3_part hnewBest_rel
    obtain ⟨hcon_safe, hcon_vh, hcon_mc, hcon_fr, hcon_mod, hcon_inv⟩ := hcon
    have hp4_eq : p4f ord newBestW = (do
        let _ ← mergeRowColProg ⟨mb, n, st.m, ord.prev, ord.last⟩
        let lastIdx := st.m - 1
        let _ ← compactIfProg ⟨mb, n, lastIdx, ord.last⟩
        let _ ← contractPartProg ⟨pb, n, lastIdx, ord.prev, ord.last⟩
        pure ⟨st.m - 1, 1, newBestW⟩) := by
      dsimp only [p4f]; exact ite_eq_left hgt2
    have hbudget : 1 + 2 * st.m + (6 * st.m + 2) * st.m + (2 * n + 1) +
        (6 * st.m + 3 * (st.m - 1) + 2 * n) ≤ 23 * n ^ 2 := by
      have hst_le : st.m - 1 ≤ n := by omega
      nlinarith only [hn, hmn, hst_le]
    exact ⟨⟨hfit_ob2, hfit4, by dsimp only; omega, hinit.1, hsafe_o, fun _ => hws.1,
        fun _ => hcon_safe⟩,
      hfinish (6 * st.m + 3 * (st.m - 1) + 2 * n)
        (hp4_eq ▸ hcon_vh) (hp4_eq ▸ hcon_mc) (hp4_eq ▸ hcon_fr.trans hfr.symm)
        (fun addr haddr => hp4_eq ▸ (hcon_mod addr haddr).trans (hs3_outside addr haddr))
        (hp4_eq ▸ hcon_inv) hbudget⟩
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
    have hp4_eq : p4f ord newBestW = pure ⟨st.m - 1, 1, newBestW⟩ := by
      dsimp only [p4f]; exact ite_eq_right hgt2
    have hinv_end : PhaseInv ws fr₀ W₀ (p + 1) ⟨st.m - 1, 1, newBestW⟩ s3 :=
      ⟨hs3_fr, hs3_outl, hm_end, Or.inr (Or.inr ⟨hp_last, rfl,
        hs3_ob1.trans (congrArg CutResult.weight hnewBest_eq),
        fun v => by simpa [hnewBest_eq] using hs3_ob2 v⟩)⟩
    have hbudget : 1 + 2 * st.m + (6 * st.m + 2) * st.m + (2 * n + 1) + 0 ≤ 23 * n ^ 2 := by
      nlinarith only [hn, hmn]
    exact ⟨⟨hfit_ob2, hfit4, by dsimp only; omega, hinit.1, hsafe_o, fun _ => hws.1,
        fun h => absurd h hgt2⟩,
      hfinish 0
        (by rw [hp4_eq]; exact validHistory_pure w _ _)
        (by rw [hp4_eq, memoryCost_pure])
        (by rw [hp4_eq]; simp only [client_simps]; exact hs3_fr.trans hfr.symm)
        (fun addr haddr => by rw [hp4_eq]; simp only [client_simps]; exact hs3_outside addr haddr)
        (by rw [hp4_eq]; simp only [client_simps]; exact hinv_end)
        hbudget⟩

private theorem phasesLoop_spec {w n ws : ℕ} (hn : 2 ≤ n) {W₀ : Fin n → Fin n → ℕ}
    (hW₀ : IsMultigraph W₀) (s₀ : Memory.State)
    (hf : ws + wsSize n ≤ s₀.frontier)
    (hfit_top : Fits w (ws + wsSize n)) (hfit4 : Fits w 4)
    (hfit_tot : Fits w (totalDoubledWeight W₀))
    (hout_len : s₀.mem (outBase ws n) = n + 1)
    (hmat₀ : ∀ i j : Fin n, s₀.mem (matBase ws + i.val * n + j.val) = W₀ i j)
    (hpart₀ : ∀ v : Fin n, s₀.mem (partBase ws n + v.val) = v.val) :
    let prog := phasesLoop ⟨n, ws⟩
    let s' := (Memory.spec 0).clientState s₀ prog
    iterationSafe phaseStep PhaseStepSafe w ⟨n, ws⟩ (n - 1) ⟨n, 0, 0⟩ s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
      memoryCost prog s₀ ≤ (23 * n ^ 2) * (n - 1) ∧
      s'.frontier = s₀.frontier ∧
      s'.mem (outBase ws n) = n + 1 ∧
      s'.mem (outBase ws n + 1) = (stoerWagner W₀).weight ∧
      (∀ v : Fin n, s'.mem (outBase ws n + 2 + v.val) =
        if v ∈ (stoerWagner W₀).side then 1 else 0) := by
  have h := iterate_spec phaseStep PhaseStepSafe w ⟨n, ws⟩ (23 * n ^ 2) (n - 1)
    (PhaseInv ws s₀.frontier W₀)
    (fun addr => matBase ws ≤ addr ∧ addr < outBase ws n + n + 2)
    (fun p hp st s hinv => phaseStep_spec hn hW₀ hf hfit_top hfit4 hfit_tot p hp st s hinv)
    ⟨n, 0, 0⟩ s₀ ⟨rfl, hout_len, rfl, Or.inl ⟨rfl, rfl, hmat₀, hpart₀⟩⟩
  obtain ⟨hsafe, hvh, hmc, hfr_e, _, _, hout_e, _, hbranch_e⟩ := h
  unfold phasesLoop
  rcases hbranch_e with ⟨h0, _⟩ | ⟨_, hlt, _⟩ | ⟨_, _, hob1, hob2⟩
  · omega
  · omega
  · exact ⟨hsafe, hvh, hmc, hfr_e, hout_e, hob1, hob2⟩

private theorem stoerWagnerProg_spec {w : ℕ} (I : StoerWagnerInput)
    (hwb : Fits w I.wordBound) :
    let s₀ := Memory.State.init I.encode
    let outAddr := (Memory.spec 0).clientResult s₀ (stoerWagnerProg I.n)
    let s' := (Memory.spec 0).clientState s₀ (stoerWagnerProg I.n)
    StoerWagnerProgSafe w I.n s₀ ∧
      (Memory.spec w).ValidHistory s₀
        ((Memory.spec w).clientHistory s₀ (stoerWagnerProg I.n)) ∧
      memoryCost (stoerWagnerProg I.n) s₀ ≤ 26 * (I.n + 1) ^ 3 ∧
      outputList s'.mem outAddr = I.expectedOutput ∧
      Fits w (outAddr + I.expectedOutput.length) := by
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
    exact hfit_top.of_le (by dsimp only [ob, outBase, wsSize]; omega)
  let s1 : Memory.State := ⟨Function.update s₀.mem ob (n + 1), ws + wsSize n⟩
  by_cases hn2 : n < 2
  · have hsafe : StoerWagnerProgSafe w n s₀ := ⟨hfit_top, hfit4, fun h => absurd hn2 h⟩
    unfold stoerWagnerProg
    refine ⟨hsafe, ?_, ?_, ?_, ?_⟩
    · refine validHistory_allocDirty_bind hfit_top
        (validHistory_write_bind (by dsimp only [ob, outBase, wsSize]; omega)
          (hfit_top.of_le (by dsimp only [wsSize]; omega)) ?_)
      rw [ite_eq_left hn2]
      refine validHistory_write_bind (by dsimp only [ob, outBase, wsSize]; omega) (fits_zero w) ?_
      exact validHistory_ite
        (fun hn1 => validHistory_write_bind
          (by dsimp only [ob, outBase, wsSize] at hn1 ⊢; rw [hn1]; omega)
          (fits_zero w) (validHistory_pure w _ _))
        (fun _ => validHistory_pure w _ _)
    · rw [memoryCost_bind', memoryCost_allocDirty, memoryCost_bind', memoryCost_write]
      simp only [client_simps]
      rw [memoryCost_ite, ite_eq_left hn2, memoryCost_bind', memoryCost_write, memoryCost_ite]
      split_ifs <;> simp only [memoryCost_bind', memoryCost_write, client_simps]
      · have hpos : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow 3 (n + 1) (Nat.succ_pos _)
        linarith
      · have hpos : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow 3 (n + 1) (Nat.succ_pos _)
        linarith
    · simp only [client_simps, ite_eq_left hn2]
      rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
      · simp only [Nat.zero_ne_one, ↓reduceIte, client_simps, StoerWagnerInput.expectedOutput,
          stoerWagner, List.finRange_zero, List.map_nil]
        rw [outputList_eq_iff]
        refine ⟨by rw [Function.update_of_ne (by omega), Function.update_self]; rfl, fun i => ?_⟩
        rcases i with ⟨i, hi⟩
        dsimp only at hi
        have hi0 : i = 0 := by simp only [List.length_cons, List.length_nil] at hi; omega
        subst hi0
        change (Function.update (Function.update s₀.mem ob 1) (ob + 1) 0) (ob + 1 + 0) = _
        simp
      · simp only [↓reduceIte, client_simps, StoerWagnerInput.expectedOutput, stoerWagner]
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
    · simp only [client_simps, ite_eq_left hn2]
      split_ifs <;> simpa [client_simps] using hfit_ob_len
  · have hge2 : 2 ≤ n := Nat.le_of_not_lt hn2
    have hcp := copyWordsProg_spec ⟨2, matBase ws, n * n⟩ s1
      (by dsimp only [s1, wsSize] at hws_eq ⊢; rw [hws_eq]; omega)
      (by dsimp only [s1, matBase, wsSize]; omega)
      (by dsimp only [matBase]; omega)
      (hfit_top.of_le (by dsimp only [wsSize] at hws_eq ⊢; rw [hws_eq]; omega))
      (hfit_top.of_le (by dsimp only [matBase, wsSize]; omega))
      (hfit_top.of_le (by dsimp only [wsSize]; omega))
      (fun i hi => by
        dsimp only at hi
        dsimp only [s1]
        rw [Function.update_of_ne (by dsimp only [ob, outBase] at hws_eq ⊢; rw [hws_eq]; omega)]
        have hmem := Karger.holdsMatrix_init_single (r := 0) W ⟨i / n, Nat.div_lt_of_lt_mul hi⟩
          ⟨i % n, Nat.mod_lt _ (by omega)⟩
        have hidx : 2 + (i / n) * n + i % n = 2 + i := by
          have := Nat.div_add_mod i n; rw [Nat.mul_comm] at this; omega
        rw [hidx] at hmem
        change Fits w ((Data.init (r := 0) (n :: Karger.flattenMatrix W)).mem (2 + i))
        rw [hmem]
        exact htot.of_le (entry_le_totalDoubledWeight W _ _))
    let s2 := (Memory.spec 0).clientState s1 (copyWordsProg ⟨2, matBase ws, n * n⟩)
    have hs2_fr : s2.frontier = ws + wsSize n := hcp.2.2.2.1
    have hip := initPartProg_spec (partBase ws n) n s2
      (by rw [hs2_fr]; dsimp only [partBase, wsSize]; omega)
      (hfit_top.of_le (by dsimp only [partBase, wsSize]; omega))
    let s3 := (Memory.spec 0).clientState s2 (initPartProg (partBase ws n, n))
    have hs3_fr : s3.frontier = ws + wsSize n := hip.2.2.2.1.trans hs2_fr
    have hs3_outl : s3.mem ob = n + 1 := by
      rw [hip.2.2.2.2.1 ob (by dsimp only [ob, outBase, partBase]; omega),
        hcp.2.2.2.2.1 ob (by dsimp only [ob, outBase, matBase]; omega)]
      exact Function.update_self _ _ _
    have hs3_mat : ∀ i j : Fin n, s3.mem (matBase ws + i.val * n + j.val) = W i j := by
      intro i j
      have hlt : i.val * n + j.val < n * n := cell_lt_mul le_rfl i.isLt j.isLt
      rw [hip.2.2.2.2.1 _ (by dsimp only [matBase, partBase]; omega),
        show matBase ws + i.val * n + j.val = matBase ws + (i.val * n + j.val) by omega,
        hcp.2.2.2.2.2 _ hlt]
      dsimp only [s1]
      rw [Function.update_of_ne (by dsimp only [ob, outBase] at hws_eq ⊢; rw [hws_eq]; omega)]
      have hmem := Karger.holdsMatrix_init_single (r := 0) W i j
      change (Data.init (r := 0) (n :: Karger.flattenMatrix W)).mem (2 + (i.val * n + j.val)) =
          W i j
      simpa [add_assoc] using hmem
    have hph := phasesLoop_spec hge2 hW s3 (by rw [hs3_fr]) hfit_top hfit4 htot
      hs3_outl hs3_mat hip.2.2.2.2.2
    have hsafe : StoerWagnerProgSafe w n s₀ := ⟨hfit_top, hfit4, fun _ => ⟨hcp.1, hip.1, hph.1⟩⟩
    unfold stoerWagnerProg
    refine ⟨hsafe, ?_, ?_, ?_, ?_⟩
    · refine validHistory_allocDirty_bind hfit_top
        (validHistory_write_bind (by dsimp only [ob, outBase, wsSize]; omega)
          (hfit_top.of_le (by dsimp only [wsSize]; omega)) ?_)
      rw [ite_eq_right hn2]
      exact validHistory_bind_step hcp.2.1 (validHistory_bind_step hip.2.1
        (validHistory_bind_step hph.2.1 (validHistory_pure w _ _)))
    · rw [memoryCost_bind', memoryCost_allocDirty, memoryCost_bind', memoryCost_write]
      simp only [client_simps]
      rw [memoryCost_ite, ite_eq_right hn2, memoryCost_bind', memoryCost_bind', memoryCost_bind']
      have c1 := hcp.2.2.1
      have c2 := hip.2.2.1
      have c3 := hph.2.2.1
      dsimp only at c1 c2 c3
      simp only [client_simps]
      have hsub : n - 1 ≤ n := Nat.sub_le n 1
      have hcube : 23 * n ^ 2 * (n - 1) ≤ 23 * n ^ 3 := by
        have := Nat.mul_le_mul_left (23 * n ^ 2) hsub
        nlinarith
      nlinarith
    · simp only [client_simps, ite_eq_right hn2]
      rw [outputList_eq_iff]
      refine ⟨?_, fun i => ?_⟩
      · simpa [I, StoerWagnerInput.expectedOutput] using hph.2.2.2.2.1
      · have hlen_exp : I.expectedOutput.length = n + 1 := by
          simp [I, StoerWagnerInput.expectedOutput]
        change ((Memory.spec 0).clientState s3 (phasesLoop ⟨n, ws⟩)).mem (ob + 1 + i.val) = _
        rcases i with ⟨_ | v, hlt⟩
        · simpa [I, StoerWagnerInput.expectedOutput] using hph.2.2.2.2.2.1
        · have hv : v < n := by
            have : v + 1 < I.expectedOutput.length := hlt
            omega
          have hmem_v := hph.2.2.2.2.2.2 ⟨v, hv⟩
          have haddr : ob + 1 + (v + 1) = outBase ws n + 2 + v := by dsimp only [ob]; omega
          rw [haddr]
          simpa [StoerWagnerInput.expectedOutput] using hmem_v
    · simp only [client_simps, ite_eq_right hn2]
      exact hfit_ob_len

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
    (hm.symm ▸ hspec.1) (hm.symm ▸ hspec.2.1)
  rw [hm] at ey hmem hout
  obtain ⟨steps, hsteps, erun⟩ := ex.seq ey
  have erunStd := erun.mapSimulates .exactStandard
  have hr := erunStd.runs (pc := 0) (p := prog) (Program.Contains.self _).append_left
  have hhalt : step w prog ⟨code.size, y⟩ =
      .halt (wordWords ((Memory.spec w).clientResult (Memory.State.init I.encode)
        (stoerWagnerProg I.n)) 0) := by
    rw [← hout 0]
    exact step_halt (by simp [prog, Code.program])
  rw [clientState_width w] at hmem
  rw [clientResult_width w] at hhalt
  dsimp only [wordWords] at hhalt
  have hymem :
      y.mem = ((Memory.spec 0).clientState (Memory.State.init I.encode)
        (stoerWagnerProg I.n)).mem :=
    congrArg Memory.State.mem hmem
  refine ⟨steps + 1, ⟨⟨code.size, y⟩, steps, _,
    by simpa only [Nat.zero_add, State.init, code] using hr,
    hhalt, hymem ▸ hspec.2.2.2.1, hspec.2.2.2.2, rfl⟩, ?_⟩
  have hmc := hspec.2.2.1
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
