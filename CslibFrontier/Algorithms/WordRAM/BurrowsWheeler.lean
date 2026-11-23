/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.BurrowsWheeler.Basic
public import CslibFrontier.Algorithms.Lean.BurrowsWheeler.Decode
public import CslibFrontier.Computability.WordRAM.ListOutput
public import CslibFrontier.Computability.WordRAM.Structured
import CslibFrontier.Algorithms.WordRAM.Histogram
import CslibFrontier.Computability.WordRAM.Copy
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Burrows–Wheeler Inversion on the Word-RAM

Linear-time implementation of Algorithm D of [BurrowsWheeler1994] (Sections 2 and 4.2) on the
standard-basis Word-RAM (`Basis.standard`) for words over a bounded integer alphabet `[0, σ)`:

1. **`buildTablesCode`** clears `σ` buckets at `cBase` via `zeroFill`, scans the last column `L`
   once to populate both the rank array `P[0..|L|)` (`rankTable L`) at `pBase` and per-symbol
   frequencies in `cBase`, and runs an exclusive prefix-sum scan over `[0, σ)` so that
   `C[b] = L.countP (· < b)`, in `11 * σ + 11 * |L| + 13` machine instructions.
2. **`lfDecodeCode`** executes up to `|L|` table-driven LF steps `r ↦ P[r] + C[L[r]]` from row
   `I`, writing decoded symbols backwards into an output buffer so that halting returns
   `inverseBwt (L, I)` as a length-prefixed array without a post-copy pass, in `14 * |L| + 9`
   machine instructions.
3. **`decodeCode` / `decodeProgram`** unpacks an encoded input `inp = ⟨L, I, σ⟩` (`[I, σ] ++ L`),
   places `C`, `P`, and the output buffer in disjoint regions after the input, and returns
   `inverseBwt (L, I)` in at most `25 * |L| + 11 * σ + 34` instructions at any word width `w` with
   `Fits w (3 * |L| + σ + 4)` (and `InputFits w inp.encode` in `decodeProgram_computesListInTime`
   to bound an arbitrary encoded starting row `I`). On `bwt u` (with `∀ c ∈ u, c < σ`),
   `decodeProgram_bwt` discharges `InputFits` automatically from `bwtIndex u ≤ |u|` and recovers
   `u` in `O(|u| + σ)` instructions.

## Main definitions

* `Cslib.Algorithms.WordRAM.BurrowsWheeler.Input`: integer-alphabet decoder input `⟨L, I, σ⟩`.
* `Cslib.Algorithms.WordRAM.BurrowsWheeler.buildTablesCode`: `O(|L| + σ)` `C` and `P` table builder.
* `Cslib.Algorithms.WordRAM.BurrowsWheeler.lfDecodeCode`: `O(|L|)` table-driven LF-step decoder.
* `Cslib.Algorithms.WordRAM.BurrowsWheeler.decodeCode`, `decodeProgram`: end-to-end BWT inversion.

## Main results

* `Cslib.Algorithms.WordRAM.BurrowsWheeler.buildTablesCode_exec`: builds `C` and `rankTable L`
  within `11 * σ + 11 * |L| + 13` instructions.
* `Cslib.Algorithms.WordRAM.BurrowsWheeler.lfDecodeCode_exec`: decodes `inverseBwt (L, I)` within
  `14 * |L| + 9` instructions.
* `Cslib.Algorithms.WordRAM.BurrowsWheeler.decodeCode_exec`,
  `Cslib.Algorithms.WordRAM.BurrowsWheeler.decodeProgram_computesListInTime`: end-to-end
  `O(|L| + σ)` Word-RAM BWT inversion.
* `Cslib.Algorithms.WordRAM.BurrowsWheeler.decodeProgram_bwt`: recovers `u` from `bwt u` within
  `25 * |u| + 11 * σ + 34` instructions whenever `∀ c ∈ u, c < σ` and `Fits w (3 * |u| + σ + 4)`.

## References

* [BurrowsWheeler1994]
-/

public section

namespace Cslib.Algorithms.WordRAM.BurrowsWheeler

open Cslib.WordRAM
open Cslib.Algorithms.Lean.BurrowsWheeler

/-! ## Input encoding and pure count identities -/

/-- Input to the integer-alphabet Burrows–Wheeler decoder: the last column `last`, the starting
row index `index`, and the strict alphabet upper bound `alphabetSize`. -/
structure Input where
  /-- The last column `L`. -/
  last : List ℕ
  /-- The starting row index `I`. -/
  index : ℕ
  /-- Strict upper bound `σ` on symbols appearing in `last`. -/
  alphabetSize : ℕ
  deriving DecidableEq, Repr

/-- Every symbol of `inp.last` lies in `[0, inp.alphabetSize)`. -/
@[expose] def Input.Valid (inp : Input) : Prop :=
  ∀ c ∈ inp.last, c < inp.alphabetSize

/-- Word-array encoding `[I, σ] ++ L`: `Data.init` places `|L| + 2` at address `0`, `I` at `1`,
`σ` at `2`, and `L[0..|L|)` at `3..|L|+2`. -/
@[expose] def Input.encode (inp : Input) : List ℕ :=
  inp.index :: inp.alphabetSize :: inp.last

@[simp] theorem length_encode (inp : Input) : inp.encode.length = inp.last.length + 2 := by
  simp [Input.encode]

private theorem countP_lt_succ : ∀ (L : List ℕ) (b : ℕ),
    L.countP (· < b + 1) = L.countP (· < b) + L.count b
  | [], _ => rfl
  | a :: L, b => by
    simp only [List.countP_cons, List.count_cons, countP_lt_succ L b, decide_eq_true_eq, beq_iff_eq]
    split_ifs <;> omega

private theorem lfMap_le_length (L : List ℕ) {r : ℕ} (hr : r < L.length) :
    lfMap L r ≤ L.length := by
  have hc : L[r]? = some L[r] := List.getElem?_eq_getElem hr
  rw [lfMap, hc]
  simp only
  have htake : (L.take r).count L[r] ≤ L.count L[r] :=
    (List.take_sublist r L).count_le L[r]
  have hsum := countP_lt_succ L L[r]
  have hle : L.countP (· < L[r] + 1) ≤ L.length := List.countP_le_length
  omega

/-! ## Register layout (`Fin 16`, `Basis.standard`) -/

namespace Reg

/-- Base address of input last column `L`. -/
abbrev src : Fin 16 := 0
/-- Length `n = |L|`. -/
abbrev len : Fin 16 := 1
/-- Alphabet upper bound `σ`. -/
abbrev sigma : Fin 16 := 2
/-- Starting / current row index `r`. -/
abbrev row : Fin 16 := 3
/-- Base address of cumulative count table `C[0..σ)`. -/
abbrev cBase : Fin 16 := 4
/-- Base address of rank table `P[0..n)`. -/
abbrev pBase : Fin 16 := 5
/-- Base address of output buffer `[buf..buf+n]`. -/
abbrev buf : Fin 16 := 6
/-- Output list header address returned at halt. -/
abbrev out : Fin 16 := 7
/-- Loop index / backward write cursor. -/
private abbrev idx : Fin 16 := 8
/-- Running prefix sum / decoded symbol count. -/
private abbrev acc : Fin 16 := 9
/-- Remaining LF steps. -/
private abbrev rem : Fin 16 := 10
/-- Temporary address register. -/
private abbrev addr : Fin 16 := 11
/-- Current symbol `c = L[r]`. -/
private abbrev sym : Fin 16 := 12
/-- Temporary word register. -/
private abbrev tmp : Fin 16 := 13
/-- Constant `0`. -/
private abbrev zero : Fin 16 := 14
/-- Constant `1`. -/
private abbrev one : Fin 16 := 15

end Reg

open Reg

/-! ## Word-RAM structured code -/

/-- Zero `cBase[0..sigma)` via `Histogram.clearBlock` and load constants `zero = 0`, `one = 1`. -/
private def clearC : Code .standard 16 :=
  Histogram.clearBlock cBase sigma idx addr zero one

/-- One step of the combined rank-table and histogram pass over `L`. -/
private def rankCountBody : Code .standard 16 := ram[
  addr ← src + idx;
  sym ← *addr;
  addr ← cBase + sym;
  tmp ← *addr;
  acc ← pBase + idx;
  *acc ← tmp;
  tmp ← tmp + one;
  *addr ← tmp;
  idx ← idx + one ]

/-- Single pass over `L[0..len)` populating `P[0..len)` at `pBase` and counts at `cBase`. -/
private def scanRankAndCount : Code .standard 16 :=
  .seq (ram[ idx ← #0 ]) (.loop (.lt idx len) rankCountBody)

/-- One step of the exclusive prefix-sum scan over `cBase[0..sigma)`. -/
private def prefixSumBody : Code .standard 16 := ram[
  addr ← cBase + idx;
  tmp ← *addr;
  *addr ← acc;
  acc ← acc + tmp;
  idx ← idx + one ]

/-- Convert symbol counts at `cBase[0..sigma)` in place into `C[b] = L.countP (· < b)`. -/
private def prefixSumC : Code .standard 16 :=
  .seq (ram[ idx ← #0; acc ← #0 ]) (.loop (.lt idx sigma) prefixSumBody)

/-- Build both `C[0..sigma)` at `cBase` and `P[0..len)` at `pBase` in `O(len + sigma)` time. -/
def buildTablesCode : Code .standard 16 :=
  .seq clearC (.seq scanRankAndCount prefixSumC)

/-- One guarded table-driven LF step writing decoded symbols backwards from `buf + len`. -/
private def lfStepBody : Code .standard 16 :=
  .branch (.lt row len)
    (ram[
      addr ← src + row;
      sym ← *addr;
      *idx ← sym;
      idx ← idx - one;
      acc ← acc + one;
      rem ← rem - one;
      addr ← pBase + row;
      tmp ← *addr;
      addr ← cBase + sym;
      row ← *addr;
      row ← tmp + row ])
    (ram[ rem ← #0 ])

/-- Run up to `len` LF steps from `row` using `C` at `cBase` and `P` at `pBase`, storing the
length-prefixed decoded word in `[buf..buf+len]` and leaving its header address in `out`. -/
def lfDecodeCode : Code .standard 16 :=
  .seq
    (ram[
      zero ← #0;
      one ← #1;
      idx ← buf + len;
      acc ← #0;
      rem ← len ])
    (.seq (.loop (.lt zero rem) lfStepBody) (ram[ *idx ← acc; out ← idx ]))

/-- Unpack `Input.encode` (`[I, σ] ++ L` at `Data.init`), allocate `C`, `P`, and `buf` after the
input, build the tables, and run LF decoding. -/
def decodeCode : Code .standard 16 :=
  .seq
    (ram[
      zero ← #0;
      one ← #1;
      tmp ← #2;
      len ← *zero;
      len ← len - tmp;
      row ← *one;
      sigma ← *tmp;
      src ← #3;
      cBase ← src + len;
      pBase ← cBase + sigma;
      buf ← pBase + len ])
    (.seq buildTablesCode lfDecodeCode)

/-- Flat Word-RAM program computing `inverseBwt (inp.last, inp.index)` from `inp.encode`. -/
def decodeProgram : Program .standard 16 :=
  decodeCode.program out

/-! ## Correctness and running time of `buildTablesCode` -/

private def rankCountMem (mem : ℕ → ℕ) (L : List ℕ) (cb σ pb j : ℕ) (a : ℕ) : ℕ :=
  if cb ≤ a ∧ a < cb + σ then (L.take j).count (a - cb)
  else if pb ≤ a ∧ a < pb + j then (L.take (a - pb)).count (L.getD (a - pb) 0)
  else mem a

private theorem rankCountMem_succ (mem : ℕ → ℕ) (L : List ℕ) (cb σ pb j : ℕ)
    (hdisj : cb + σ ≤ pb) (hj : j < L.length) (hc : L[j] < σ) :
    Function.update
      (Function.update (rankCountMem mem L cb σ pb j) (pb + j) ((L.take j).count L[j]))
      (cb + L[j]) ((L.take j).count L[j] + 1) =
    rankCountMem mem L cb σ pb (j + 1) := by
  have htake : L.take (j + 1) = L.take j ++ [L[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
  funext a
  by_cases ha_cb : a = cb + L[j]
  · subst a
    rw [Function.update_self]
    have hcond : cb ≤ cb + L[j] ∧ cb + L[j] < cb + σ := by omega
    simp only [rankCountMem, hcond, and_self, ↓reduceIte, Nat.add_sub_cancel_left, htake,
      List.count_append, List.count_singleton_self]
  · rw [Function.update_of_ne ha_cb]
    by_cases ha_pb : a = pb + j
    · subst a
      rw [Function.update_self]
      have hnot_cb : ¬(cb ≤ pb + j ∧ pb + j < cb + σ) := by omega
      have hcond_pb : pb ≤ pb + j ∧ pb + j < pb + (j + 1) := by omega
      have hget : L.getD j 0 = L[j] := List.getD_eq_getElem L 0 hj
      simp only [rankCountMem, hnot_cb, ↓reduceIte, hcond_pb, and_self,
        Nat.add_sub_cancel_left, hget]
    · rw [Function.update_of_ne ha_pb]
      simp only [rankCountMem]
      split_ifs with h1 h2 h3
      · have hne : L[j] ≠ a - cb := by omega
        rw [htake, List.count_append, List.count_cons_of_ne hne, List.count_nil, Nat.add_zero]
      · rfl
      · omega
      · omega
      · rfl

private theorem exec_scanRankAndCount {w : ℕ} (x : Data 16) (L : List ℕ)
    (hlen_eq : x.regs len = L.length)
    (hs : Fits w (x.regs src + L.length))
    (hc : Fits w (x.regs cBase + x.regs sigma))
    (hp : Fits w (x.regs pBase + L.length))
    (hdisj_sc : x.regs src + L.length ≤ x.regs cBase)
    (hdisj_cp : x.regs cBase + x.regs sigma ≤ x.regs pBase)
    (hvalid : ∀ c ∈ L, c < x.regs sigma)
    (hinput : ∀ i (hi : i < L.length), x.mem (x.regs src + i) = L[i])
    (hzero : ∀ b < x.regs sigma, x.mem (x.regs cBase + b) = 0)
    (hz : x.regs zero = 0) (ho : x.regs one = 1) :
    ∃ y, ExecWithin w scanRankAndCount x y (11 * L.length + 3) ∧
      y.mem = rankCountMem x.mem L (x.regs cBase) (x.regs sigma) (x.regs pBase) L.length ∧
      (∀ i : Fin 16, i.val ≤ 6 → y.regs i = x.regs i) ∧
      y.regs zero = 0 ∧ y.regs one = 1 := by
  let P (j : ℕ) (y : Data 16) : Prop :=
    (∀ i : Fin 16, i.val ≤ 6 → y.regs i = x.regs i) ∧
      y.regs zero = 0 ∧ y.regs one = 1 ∧
      y.mem = rankCountMem x.mem L (x.regs cBase) (x.regs sigma) (x.regs pBase) j
  have hbody (y : Data 16) (hy : P (y.regs idx) y) (hlt : y.regs idx < x.regs len) :
      ∃ z, ExecWithin w rankCountBody y z 9 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hzy, hoy, hm⟩ := hy
    have hj : y.regs idx < L.length := by omega
    have hsrc := hr src (by decide)
    have hcb := hr cBase (by decide)
    have hpb := hr pBase (by decide)
    have hsym_lt : L[y.regs idx] < x.regs sigma := hvalid _ (List.getElem_mem hj)
    have hread_L : y.mem (y.regs src + y.regs idx) = L[y.regs idx] := by
      rw [hm, hsrc]
      have hnc : ¬(x.regs cBase ≤ x.regs src + y.regs idx ∧
          x.regs src + y.regs idx < x.regs cBase + x.regs sigma) := by omega
      have hnp : ¬(x.regs pBase ≤ x.regs src + y.regs idx ∧
          x.regs src + y.regs idx < x.regs pBase + y.regs idx) := by omega
      simp only [rankCountMem, hnc, hnp, ↓reduceIte]
      exact hinput _ hj
    have hread_C : y.mem (y.regs cBase + L[y.regs idx]) =
        (L.take (y.regs idx)).count L[y.regs idx] := by
      rw [hm, hcb]
      have hc_in : x.regs cBase ≤ x.regs cBase + L[y.regs idx] ∧
          x.regs cBase + L[y.regs idx] < x.regs cBase + x.regs sigma := by omega
      simp only [rankCountMem, hc_in, and_self, ↓reduceIte, Nat.add_sub_cancel_left]
    have hcnt_le : (L.take (y.regs idx)).count L[y.regs idx] ≤ y.regs idx := by
      have h1 := List.count_le_length (a := L[y.regs idx]) (l := L.take (y.regs idx))
      have h2 := List.length_take_le (y.regs idx) L
      omega
    have hf_src : Fits w (y.regs src + y.regs idx) := hs.of_le (by rw [hsrc]; omega)
    have hf_cb : Fits w (y.regs cBase + L[y.regs idx]) := hc.of_le (by rw [hcb]; omega)
    have hf_pb : Fits w (y.regs pBase + y.regs idx) := hp.of_le (by rw [hpb]; omega)
    have hf_cnt1 : Fits w ((L.take (y.regs idx)).count L[y.regs idx] + 1) := hs.of_le (by omega)
    have hf_idx1 : Fits w (y.regs idx + 1) := hs.of_le (by omega)
    refine WP.exists_execWithin ?_
    unfold rankCountBody
    wram_exec [hoy, hread_L, hread_C, hf_src, hf_cb, hf_pb, hf_cnt1, hf_idx1]
    refine ⟨⟨fun i hi => by
      have hri := hr i hi
      fin_cases i <;> norm_num at hi <;> wram_simp [hri],
      by wram_simp [hzy], by wram_simp [hoy], ?_⟩, by wram_simp⟩
    wram_simp
    rw [hm, hcb, hpb, rankCountMem_succ _ _ _ _ _ _ hdisj_cp hj hsym_lt]
  refine WP.exists_execWithin ?_
  unfold scanRankAndCount
  wram_exec
  wram_call (ExecWithin.loop_count P (fun y hy => hy.1 len (by decide)) hbody
    (by wram_simp; omega) ⟨fun i hi => by fin_cases i <;> norm_num at hi <;> wram_simp,
      by wram_simp [hz], by wram_simp [ho], by
        wram_simp
        funext a
        by_cases h1 : x.regs cBase ≤ a ∧ a < x.regs cBase + x.regs sigma
        · have ha : x.regs cBase + (a - x.regs cBase) = a := by omega
          have h0 := hzero (a - x.regs cBase) (by omega)
          rw [ha] at h0
          simp only [rankCountMem, h1, and_self, ↓reduceIte, List.take_zero, List.count_nil, h0]
        · have h2 : ¬(x.regs pBase ≤ a ∧ a < x.regs pBase + 0) := by omega
          simp only [rankCountMem, h1, h2, ↓reduceIte]⟩)
    with y ⟨⟨hr, hzy, hoy, hm⟩, _⟩
  rw [hlen_eq] at hm ⊢
  exact ⟨by wram_simp [hlen_eq]; omega, hm, hr, hzy, hoy⟩

private def cTableMem (mem : ℕ → ℕ) (L : List ℕ) (cb j : ℕ) (a : ℕ) : ℕ :=
  if cb ≤ a ∧ a < cb + j then L.countP (· < a - cb) else mem a

private theorem cTableMem_succ (mem : ℕ → ℕ) (L : List ℕ) (cb j : ℕ) :
    Function.update (cTableMem mem L cb j) (cb + j) (L.countP (· < j)) =
      cTableMem mem L cb (j + 1) := by
  funext a
  by_cases ha : a = cb + j
  · subst a
    rw [Function.update_self]
    have hcond : cb ≤ cb + j ∧ cb + j < cb + (j + 1) := by omega
    simp only [cTableMem, hcond, and_self, ↓reduceIte, Nat.add_sub_cancel_left]
  · rw [Function.update_of_ne ha]
    simp only [cTableMem]
    split_ifs <;> omega

private theorem exec_prefixSumC {w : ℕ} (x : Data 16) (L : List ℕ)
    (hc : Fits w (x.regs cBase + x.regs sigma))
    (hn : Fits w L.length)
    (hcnt : ∀ b < x.regs sigma, x.mem (x.regs cBase + b) = L.count b)
    (hz : x.regs zero = 0) (ho : x.regs one = 1) :
    ∃ y, ExecWithin w prefixSumC x y (7 * x.regs sigma + 4) ∧
      y.mem = cTableMem x.mem L (x.regs cBase) (x.regs sigma) ∧
      (∀ i : Fin 16, i.val ≤ 6 → y.regs i = x.regs i) := by
  let P (j : ℕ) (y : Data 16) : Prop :=
    (∀ i : Fin 16, i.val ≤ 6 → y.regs i = x.regs i) ∧
      y.regs zero = 0 ∧ y.regs one = 1 ∧
      y.regs acc = L.countP (· < j) ∧
      y.mem = cTableMem x.mem L (x.regs cBase) j
  have hbody (y : Data 16) (hy : P (y.regs idx) y) (hlt : y.regs idx < x.regs sigma) :
      ∃ z, ExecWithin w prefixSumBody y z 5 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hzy, hoy, hacc, hm⟩ := hy
    have hcb := hr cBase (by decide)
    have hread : y.mem (y.regs cBase + y.regs idx) = L.count (y.regs idx) := by
      rw [hm, hcb]
      have hnot : ¬(x.regs cBase ≤ x.regs cBase + y.regs idx ∧
          x.regs cBase + y.regs idx < x.regs cBase + y.regs idx) := by omega
      simp only [cTableMem, hnot, ↓reduceIte]
      exact hcnt _ hlt
    have hsum : L.countP (· < y.regs idx) + L.count (y.regs idx) =
        L.countP (· < y.regs idx + 1) := (countP_lt_succ L (y.regs idx)).symm
    have hsum_le : L.countP (· < y.regs idx + 1) ≤ L.length := List.countP_le_length
    have hf_cb : Fits w (y.regs cBase + y.regs idx) := hc.of_le (by rw [hcb]; omega)
    have hf_sum : Fits w (L.countP (· < y.regs idx) + L.count (y.regs idx)) :=
      hn.of_le (by omega)
    have hf_idx1 : Fits w (y.regs idx + 1) := hc.of_le (by omega)
    refine WP.exists_execWithin ?_
    unfold prefixSumBody
    wram_exec [hoy, hacc, hread, hf_cb, hf_sum, hf_idx1]
    refine ⟨⟨fun i hi => by
      have hri := hr i hi
      fin_cases i <;> norm_num at hi <;> wram_simp [hri],
      by wram_simp [hzy], by wram_simp [hoy],
      by wram_simp [hsum], ?_⟩, by wram_simp⟩
    wram_simp
    rw [hm, hcb, cTableMem_succ]
  refine WP.exists_execWithin ?_
  unfold prefixSumC
  wram_exec
  wram_call (ExecWithin.loop_count P (fun y hy => hy.1 sigma (by decide)) hbody
    (by wram_simp; omega) ⟨fun i hi => by fin_cases i <;> norm_num at hi <;> wram_simp,
      by wram_simp [hz], by wram_simp [ho],
      by wram_simp; simp,
      by
        wram_simp
        funext a
        have hnot : ¬(x.regs cBase ≤ a ∧ a < x.regs cBase + 0) := by omega
        simp only [cTableMem, hnot, ↓reduceIte]⟩)
    with y ⟨⟨hr, _, _, _, hm⟩, _⟩
  exact ⟨by wram_simp; omega, hm, hr⟩

/-- `buildTablesCode` builds `C[0..sigma)` at `cBase` and `rankTable L` at `pBase` within
`11 * sigma + 11 * |L| + 13` instructions, preserving all other memory cells and the parameter
registers `0..6`. -/
theorem buildTablesCode_exec {w : ℕ} (x : Data 16) (L : List ℕ)
    (h1 : Fits w 1)
    (hlen_eq : x.regs len = L.length)
    (hs : Fits w (x.regs src + L.length))
    (hc : Fits w (x.regs cBase + x.regs sigma))
    (hp : Fits w (x.regs pBase + L.length))
    (hdisj_sc : x.regs src + L.length ≤ x.regs cBase)
    (hdisj_cp : x.regs cBase + x.regs sigma ≤ x.regs pBase)
    (hvalid : ∀ c ∈ L, c < x.regs sigma)
    (hinput : ∀ i (hi : i < L.length), x.mem (x.regs src + i) = L[i]) :
    ∃ y, ExecWithin w buildTablesCode x y (11 * x.regs sigma + 11 * L.length + 13) ∧
      (∀ b < x.regs sigma, y.mem (x.regs cBase + b) = L.countP (· < b)) ∧
      Block.HoldsList (x.regs pBase) (rankTable L) y.mem ∧
      (∀ a, ¬(x.regs cBase ≤ a ∧ a < x.regs cBase + x.regs sigma) →
        ¬(x.regs pBase ≤ a ∧ a < x.regs pBase + L.length) → y.mem a = x.mem a) ∧
      (∀ i : Fin 16, i.val ≤ 6 → y.regs i = x.regs i) := by
  obtain ⟨y₁, he₁, hm₁, hr₁_raw, hz₁, ho₁⟩ :=
    Histogram.exec_clearBlock cBase sigma idx addr zero one (by decide) x h1 hc
  have hr₁ : ∀ i : Fin 16, i.val ≤ 6 → y₁.regs i = x.regs i := fun i hi =>
    hr₁_raw i (by fin_cases i <;> norm_num at hi <;> decide)
      (by fin_cases i <;> norm_num at hi <;> decide)
      (by fin_cases i <;> norm_num at hi <;> decide)
      (by fin_cases i <;> norm_num at hi <;> decide)
  have hsrc₁ := hr₁ src (by decide)
  have hlen₁ := hr₁ len (by decide)
  have hsig₁ := hr₁ sigma (by decide)
  have hcb₁ := hr₁ cBase (by decide)
  have hpb₁ := hr₁ pBase (by decide)
  obtain ⟨y₂, he₂, hm₂, hr₂, hz₂, ho₂⟩ := exec_scanRankAndCount y₁ L
    (by rw [hlen₁, hlen_eq])
    (by rwa [hsrc₁])
    (by rwa [hcb₁, hsig₁])
    (by rwa [hpb₁])
    (by rw [hsrc₁, hcb₁]; exact hdisj_sc)
    (by rw [hcb₁, hsig₁, hpb₁]; exact hdisj_cp)
    (by rwa [hsig₁])
    (by
      intro i hi
      rw [hsrc₁, hm₁]
      have hnot : ¬(x.regs cBase ≤ x.regs src + i ∧
          x.regs src + i < x.regs cBase + x.regs sigma) := by omega
      simp only [Cslib.WordRAM.clear, hnot, ↓reduceIte]
      exact hinput i hi)
    (by
      intro b hb
      rw [hcb₁, hm₁]
      have hlt : b < x.regs sigma := by omega
      simp [Cslib.WordRAM.clear, hlt])
    hz₁ ho₁
  have hcb₂ := (hr₂ cBase (by decide)).trans hcb₁
  have hsig₂ := (hr₂ sigma (by decide)).trans hsig₁
  obtain ⟨y₃, he₃, hm₃, hr₃⟩ := exec_prefixSumC y₂ L
    (by rwa [hcb₂, hsig₂])
    (hs.of_le (by omega))
    (by
      intro b hb
      rw [hcb₂, hm₂, hcb₁, hsig₁]
      have hlt : b < x.regs sigma := by omega
      have hcond : x.regs cBase ≤ x.regs cBase + b ∧
          x.regs cBase + b < x.regs cBase + x.regs sigma := by omega
      simp only [rankCountMem, hcond, and_self, ↓reduceIte, Nat.add_sub_cancel_left,
        List.take_length])
    hz₂ ho₂
  refine ⟨y₃, (he₁.seq (he₂.seq he₃)).mono (by rw [hsig₂]; omega), ?_, ?_, ?_,
    fun i hi => (hr₃ i hi).trans ((hr₂ i hi).trans (hr₁ i hi))⟩
  · intro b hb
    rw [hm₃, hcb₂, hsig₂]
    have hcond : x.regs cBase ≤ x.regs cBase + b ∧
        x.regs cBase + b < x.regs cBase + x.regs sigma := by omega
    simp only [cTableMem, hcond, and_self, ↓reduceIte, Nat.add_sub_cancel_left]
  · intro ⟨i, hi_rt⟩
    have hi : i < L.length := by simpa only [length_rankTable] using hi_rt
    change y₃.mem (x.regs pBase + i) = (rankTable L)[i]
    rw [getElem_rankTable L hi, hm₃, hcb₂, hsig₂]
    have hnot_c : ¬(x.regs cBase ≤ x.regs pBase + i ∧
        x.regs pBase + i < x.regs cBase + x.regs sigma) := by omega
    simp only [cTableMem, hnot_c, ↓reduceIte, hm₂, hcb₁, hsig₁, hpb₁]
    have hcond_p : x.regs pBase ≤ x.regs pBase + i ∧
        x.regs pBase + i < x.regs pBase + L.length := by omega
    have hget : L.getD i 0 = L[i] := List.getD_eq_getElem L 0 hi
    simp only [rankCountMem, hnot_c, ↓reduceIte, hcond_p, and_self, Nat.add_sub_cancel_left, hget]
  · intro a hnc hnp
    rw [hm₃, hcb₂, hsig₂]
    simp only [cTableMem, hnc, ↓reduceIte, hm₂, hcb₁, hsig₁, hpb₁, rankCountMem, hnp,
      hm₁, Cslib.WordRAM.clear]

/-! ## Correctness and running time of `lfDecodeCode` -/

private theorem while_lfStepBody_spec {w : ℕ} (L : List ℕ) (σ : ℕ)
    (hvalid : ∀ c ∈ L, c < σ)
    (k : ℕ) :
    ∀ (x : Data 16) (accList : List ℕ),
      Fits w (x.regs buf + L.length) →
      Fits w (x.regs src + L.length) →
      Fits w (x.regs cBase + σ) →
      Fits w (x.regs pBase + L.length) →
      x.regs src + L.length ≤ x.regs buf →
      x.regs cBase + σ ≤ x.regs buf →
      x.regs pBase + L.length ≤ x.regs buf →
      x.regs zero = 0 →
      x.regs one = 1 →
      x.regs len = L.length →
      x.regs rem = k →
      x.regs acc = accList.length →
      accList.length + k = L.length →
      x.regs idx = x.regs buf + k →
      (∀ i (hi : i < L.length), x.mem (x.regs src + i) = L[i]) →
      (∀ b < σ, x.mem (x.regs cBase + b) = L.countP (· < b)) →
      (∀ i (hi : i < L.length), x.mem (x.regs pBase + i) = (L.take i).count L[i]) →
      Block.HoldsList (x.regs buf + k + 1) accList x.mem →
      ∃ y, ExecWithin w (.loop (.lt zero rem) lfStepBody) x y (14 * k + 2) ∧
        y.regs acc = (lfDecode L k (x.regs row) accList).length ∧
        x.regs buf ≤ y.regs idx ∧
        y.regs idx + (lfDecode L k (x.regs row) accList).length = x.regs buf + L.length ∧
        Block.HoldsList (y.regs idx + 1) (lfDecode L k (x.regs row) accList) y.mem := by
  induction k with
  | zero =>
    intro x accList _ _ _ _ _ _ _ hz _ _ hrem hacc hsum hidx _ _ _ hhold
    have hstop : ¬(Cond.lt zero rem).Holds x := by simp only [Cond.holds_lt, hz, hrem]; omega
    refine ⟨x, ExecWithin.loop_exit hstop, ?_, by omega, ?_, ?_⟩
    · simp only [lfDecode, hacc]
    · simp only [lfDecode]
      omega
    · simp only [lfDecode, hidx]
      exact hhold
  | succ k' ih =>
    intro x accList hf_buf hf_src hf_cb hf_pb hd_sb hd_cb hd_pb hz ho hlen hrem hacc hsum hidx
      hL hC hP hhold
    have hc : (Cond.lt zero rem).Holds x := by simp only [Cond.holds_lt, hz, hrem]; omega
    by_cases hlt : x.regs row < L.length
    · have hcond : (Cond.lt row len).Holds x := by simp only [Cond.holds_lt, hlen]; exact hlt
      have hsym_lt : L[x.regs row] < σ := hvalid _ (List.getElem_mem hlt)
      have hread_L : x.mem (x.regs src + x.regs row) = L[x.regs row] := hL (x.regs row) hlt
      have hread_P : x.mem (x.regs pBase + x.regs row) =
          (L.take (x.regs row)).count L[x.regs row] := hP (x.regs row) hlt
      have hread_C : x.mem (x.regs cBase + L[x.regs row]) = L.countP (· < L[x.regs row]) :=
        hC _ hsym_lt
      have hlf_eq : (L.take (x.regs row)).count L[x.regs row] + L.countP (· < L[x.regs row]) =
          lfMap L (x.regs row) := by
        rw [lfMap, List.getElem?_eq_getElem hlt, Nat.add_comm]
      have hlf_le : lfMap L (x.regs row) ≤ L.length := lfMap_le_length L hlt
      have hf_sr : Fits w (x.regs src + x.regs row) := hf_src.of_le (by omega)
      have hf_idx_sub : Fits w (x.regs idx - 1) := hf_buf.of_le (by omega)
      have hf_acc1 : Fits w (x.regs acc + 1) := hf_buf.of_le (by omega)
      have hf_rem1 : Fits w (x.regs rem - 1) := hf_buf.of_le (by omega)
      have hf_pr : Fits w (x.regs pBase + x.regs row) := hf_pb.of_le (by omega)
      have hf_cs : Fits w (x.regs cBase + L[x.regs row]) := hf_cb.of_le (by omega)
      have hf_lf : Fits w ((L.take (x.regs row)).count L[x.regs row] +
          L.countP (· < L[x.regs row])) :=
        hf_buf.of_le (by omega)
      have hstep_true : ∃ x₁, ExecWithin w (ram[
          addr ← src + row;
          sym ← *addr;
          *idx ← sym;
          idx ← idx - one;
          acc ← acc + one;
          rem ← rem - one;
          addr ← pBase + row;
          tmp ← *addr;
          addr ← cBase + sym;
          row ← *addr;
          row ← tmp + row ]) x x₁ 11 ∧
        (∀ i : Fin 16, (i = src ∨ i = len ∨ i = cBase ∨ i = pBase ∨ i = buf ∨
          i = zero ∨ i = one) → x₁.regs i = x.regs i) ∧
        x₁.regs idx = x.regs buf + k' ∧
        x₁.regs acc = accList.length + 1 ∧
        x₁.regs rem = k' ∧
        x₁.regs row = lfMap L (x.regs row) ∧
        x₁.mem = Function.update x.mem (x.regs buf + (k' + 1)) L[x.regs row] := by
        refine WP.exists_execWithin ?_
        wram_exec [ho, hread_L, hread_P, hread_C, hf_sr, hf_idx_sub, hf_acc1, hf_rem1,
          hf_pr, hf_cs, hf_lf]
        exact ⟨fun i hi => by
            rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> wram_simp,
          by wram_simp [hidx, ho]; omega,
          by wram_simp [hacc, ho],
          by wram_simp [hrem, ho],
          by wram_simp [hread_L, hread_P, hread_C, hlf_eq],
          by wram_simp [hidx, hread_L]⟩
      obtain ⟨x₁, hb_t, hfr, hx₁_idx, hx₁_acc, hx₁_rem, hx₁_row, hx₁_mem⟩ := hstep_true
      have hb : ExecWithin w lfStepBody x x₁ 12 := ExecWithin.branch_pos hcond hb_t
      have hs₁ := hfr src (Or.inl rfl)
      have hl₁ := hfr len (Or.inr (Or.inl rfl))
      have hc₁ := hfr cBase (Or.inr (Or.inr (Or.inl rfl)))
      have hp₁ := hfr pBase (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      have hb₁ := hfr buf (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      have hz₁ := hfr zero (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      have ho₁ := hfr one (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
      have hhold₁ : Block.HoldsList (x₁.regs buf + k' + 1) (L[x.regs row] :: accList) x₁.mem := by
        rw [hb₁, hx₁_mem, show x.regs buf + k' + 1 = x.regs buf + (k' + 1) by omega]
        exact Block.holdsList_cons_iff.mpr ⟨Function.update_self _ _ _,
          hhold.frame fun a ha _ => Function.update_of_ne (by omega) _ _⟩
      obtain ⟨y, hy, hy_acc, hy_le, hy_sum, hy_hold⟩ := ih x₁ (L[x.regs row] :: accList)
        (by rwa [hb₁]) (by rwa [hs₁]) (by rwa [hc₁]) (by rwa [hp₁])
        (by rw [hs₁, hb₁]; exact hd_sb)
        (by rw [hc₁, hb₁]; exact hd_cb)
        (by rw [hp₁, hb₁]; exact hd_pb)
        (hz₁.trans hz) (ho₁.trans ho) (hl₁.trans hlen)
        hx₁_rem
        (by rw [hx₁_acc, List.length_cons])
        (by rw [List.length_cons]; omega)
        (by rw [hb₁]; exact hx₁_idx)
        (by
          intro i hi
          rw [hs₁, hx₁_mem, Function.update_of_ne (by omega)]
          exact hL i hi)
        (by
          intro b hb_lt
          rw [hc₁, hx₁_mem, Function.update_of_ne (by omega)]
          exact hC b hb_lt)
        (by
          intro i hi
          rw [hp₁, hx₁_mem, Function.update_of_ne (by omega)]
          exact hP i hi)
        hhold₁
      rw [hb₁] at hy_le hy_sum
      have hdec : lfDecode L (k' + 1) (x.regs row) accList =
          lfDecode L k' (x₁.regs row) (L[x.regs row] :: accList) := by
        rw [lfDecode, List.getElem?_eq_getElem hlt, hx₁_row]
      rw [← hdec] at hy_acc hy_sum hy_hold
      exact ⟨y, (ExecWithin.loop_iter hc hb hy).mono (by omega),
        hy_acc, hy_le, hy_sum, hy_hold⟩
    · have hcond : ¬(Cond.lt row len).Holds x := by simp only [Cond.holds_lt, hlen]; exact hlt
      let x₁ := x.set rem 0
      have hb_f : ExecWithin (B := .standard) w (ram[ rem ← #0 ]) x x₁ 1 :=
        ExecWithin.const (fits_zero w)
      have hb : ExecWithin w lfStepBody x x₁ 3 := ExecWithin.branch_neg hcond hb_f
      have hstop : ¬(Cond.lt zero rem).Holds x₁ := by simp +decide [Cond.holds_lt, x₁, hz]
      have hnone : L[x.regs row]? = none := List.getElem?_eq_none (by omega)
      have hdec : lfDecode L (k' + 1) (x.regs row) accList = accList := by
        rw [lfDecode, hnone]
      have hx₁_idx : x₁.regs idx = x.regs buf + (k' + 1) := by simp +decide [x₁, hidx]
      have hx₁_acc : x₁.regs acc = accList.length := by simp +decide [x₁, hacc]
      refine ⟨x₁, (ExecWithin.loop_once hc hb hstop).mono (by omega),
        by rw [hdec, hx₁_acc],
        by omega,
        by rw [hdec, hx₁_idx]; omega,
        ?_⟩
      rw [hdec, hx₁_idx]
      exact hhold

/-- `lfDecodeCode` computes `inverseBwt (L, row)` as a length-prefixed array inside `[buf..buf+|L|]`
within `14 * |L| + 9` instructions. -/
theorem lfDecodeCode_exec {w : ℕ} (x : Data 16) (L : List ℕ) (σ : ℕ)
    (h1 : Fits w 1)
    (hvalid : ∀ c ∈ L, c < σ)
    (hlen_eq : x.regs len = L.length)
    (hf_buf : Fits w (x.regs buf + L.length))
    (hf_src : Fits w (x.regs src + L.length))
    (hf_cb : Fits w (x.regs cBase + σ))
    (hf_pb : Fits w (x.regs pBase + L.length))
    (hd_sb : x.regs src + L.length ≤ x.regs buf)
    (hd_cb : x.regs cBase + σ ≤ x.regs buf)
    (hd_pb : x.regs pBase + L.length ≤ x.regs buf)
    (hL : ∀ i (hi : i < L.length), x.mem (x.regs src + i) = L[i])
    (hC : ∀ b < σ, x.mem (x.regs cBase + b) = L.countP (· < b))
    (hP : ∀ i (hi : i < L.length), x.mem (x.regs pBase + i) = (L.take i).count L[i]) :
    ∃ y, ExecWithin w lfDecodeCode x y (14 * L.length + 9) ∧
      outputList y.mem (y.regs out) = inverseBwt (L, x.regs row) ∧
      x.regs buf ≤ y.regs out ∧
      y.regs out + (inverseBwt (L, x.regs row)).length = x.regs buf + L.length := by
  have hinit_spec : ∃ x₀, ExecWithin w (ram[
      zero ← #0;
      one ← #1;
      idx ← buf + len;
      acc ← #0;
      rem ← len ]) x x₀ 5 ∧
    (∀ i : Fin 16, i.val ≤ 6 → x₀.regs i = x.regs i) ∧
    x₀.regs zero = 0 ∧ x₀.regs one = 1 ∧
    x₀.regs idx = x.regs buf + L.length ∧
    x₀.regs acc = 0 ∧ x₀.regs rem = L.length ∧
    x₀.mem = x.mem := by
    refine WP.exists_execWithin ?_
    wram_exec [h1, hlen_eq, hf_buf]
    exact ⟨fun i hi => by fin_cases i <;> norm_num at hi <;> wram_simp,
      by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩
  obtain ⟨x₀, hinit, hfr₀, hz₀, ho₀, hidx₀, hacc₀, hrem₀, hmem₀⟩ := hinit_spec
  have hs₀ := hfr₀ src (by decide)
  have hl₀ := hfr₀ len (by decide)
  have hr₀ := hfr₀ row (by decide)
  have hc₀ := hfr₀ cBase (by decide)
  have hp₀ := hfr₀ pBase (by decide)
  have hb₀ := hfr₀ buf (by decide)
  obtain ⟨y₁, hloop, hy₁_acc, hy₁_le, hy₁_sum, hy₁_hold⟩ :=
    while_lfStepBody_spec L σ hvalid L.length x₀ []
      (by rwa [hb₀]) (by rwa [hs₀]) (by rwa [hc₀]) (by rwa [hp₀])
      (by rw [hs₀, hb₀]; exact hd_sb)
      (by rw [hc₀, hb₀]; exact hd_cb)
      (by rw [hp₀, hb₀]; exact hd_pb)
      hz₀ ho₀ (hl₀.trans hlen_eq) hrem₀ hacc₀ (Nat.zero_add L.length)
      (by rw [hb₀]; exact hidx₀)
      (by rwa [hs₀, hmem₀])
      (by rwa [hc₀, hmem₀])
      (by rwa [hp₀, hmem₀])
      (Block.holdsList_nil _ _)
  rw [hb₀] at hy₁_le hy₁_sum
  rw [hr₀] at hy₁_acc hy₁_sum hy₁_hold
  have hfin_spec : ∃ y, ExecWithin (B := .standard) w (ram[ *idx ← acc; out ← idx ]) y₁ y 2 ∧
      y.regs out = y₁.regs idx ∧
      y.mem = Function.update y₁.mem (y₁.regs idx) (y₁.regs acc) := by
    refine WP.exists_execWithin ?_
    wram_exec
    exact ⟨by wram_simp, by wram_simp⟩
  obtain ⟨y, hfin, hy_out, hy_mem⟩ := hfin_spec
  refine ⟨y, (hinit.seq (hloop.seq hfin)).mono (by omega), ?_, ?_, ?_⟩
  · rw [hy_out, hy_mem, inverseBwt, outputList_eq_iff]
    exact ⟨by rw [Function.update_self, hy₁_acc],
      hy₁_hold.frame fun a ha _ => Function.update_of_ne (by omega) _ _⟩
  · rw [hy_out]
    exact hy₁_le
  · rw [hy_out, inverseBwt]
    exact hy₁_sum

/-! ## End-to-end Word-RAM BWT decoder -/

/-- `decodeCode` inverts `inp = ⟨L, I, σ⟩` from `Data.init inp.encode` within
`25 * |L| + 11 * σ + 33` instructions at any fitting width `Fits w (3 * |L| + σ + 4)`. -/
theorem decodeCode_exec (inp : Input) (w : ℕ)
    (hvalid : inp.Valid)
    (hw : Fits w (3 * inp.last.length + inp.alphabetSize + 4)) :
    ∃ y, ExecWithin w decodeCode (.init inp.encode) y
        (25 * inp.last.length + 11 * inp.alphabetSize + 33) ∧
      outputList y.mem (y.regs out) = inverseBwt (inp.last, inp.index) ∧
      Fits w (y.regs out + (inverseBwt (inp.last, inp.index)).length) := by
  have h1 : Fits w 1 := hw.of_le (by omega)
  have h2 : Fits w 2 := hw.of_le (by omega)
  have h3 : Fits w 3 := hw.of_le (by omega)
  have hm0 : (Data.init inp.encode : Data 16).mem 0 = inp.last.length + 2 := rfl
  have hm1 : (Data.init inp.encode : Data 16).mem 1 = inp.index := by
    change (Data.init inp.encode : Data 16).mem (0 + 1) = inp.index
    rw [Data.init_mem_succ]
    rfl
  have hm2 : (Data.init inp.encode : Data 16).mem 2 = inp.alphabetSize := by
    change (Data.init inp.encode : Data 16).mem (1 + 1) = inp.alphabetSize
    rw [Data.init_mem_succ]
    rfl
  have hL_init : ∀ i (hi : i < inp.last.length),
      (Data.init inp.encode : Data 16).mem (3 + i) = inp.last[i] := by
    intro i hi
    have haddr : 3 + i = (i + 2) + 1 := by omega
    rw [haddr, Data.init_mem_succ]
    change (inp.index :: inp.alphabetSize :: inp.last).getD (i + 2) 0 = inp.last[i]
    simpa only [List.getD_cons_succ] using List.getD_eq_getElem inp.last 0 hi
  have hf_n : Fits w inp.last.length := hw.of_le (by omega)
  have hf_cb : Fits w (3 + inp.last.length) := hw.of_le (by omega)
  have hf_pb : Fits w (3 + inp.last.length + inp.alphabetSize) := hw.of_le (by omega)
  have hf_buf : Fits w (3 + inp.last.length + inp.alphabetSize + inp.last.length) :=
    hw.of_le (by omega)
  have hsetup_spec : ∃ x₁, ExecWithin w (ram[
      zero ← #0;
      one ← #1;
      tmp ← #2;
      len ← *zero;
      len ← len - tmp;
      row ← *one;
      sigma ← *tmp;
      src ← #3;
      cBase ← src + len;
      pBase ← cBase + sigma;
      buf ← pBase + len ]) (.init inp.encode) x₁ 11 ∧
    x₁.regs src = 3 ∧
    x₁.regs len = inp.last.length ∧
    x₁.regs sigma = inp.alphabetSize ∧
    x₁.regs row = inp.index ∧
    x₁.regs cBase = 3 + inp.last.length ∧
    x₁.regs pBase = 3 + inp.last.length + inp.alphabetSize ∧
    x₁.regs buf = 3 + 2 * inp.last.length + inp.alphabetSize ∧
    x₁.mem = (Data.init inp.encode : Data 16).mem := by
    refine WP.exists_execWithin ?_
    wram_exec [h1, h2, h3, hm0, hm1, hm2, hf_n, hf_cb, hf_pb, hf_buf]
    exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp,
      by wram_simp, by wram_simp, by wram_simp; omega, by wram_simp⟩
  obtain ⟨x₁, hsetup, hs₁, hl₁, hsig₁, hr₁, hcb₁, hpb₁, hbuf₁, hmem₁⟩ := hsetup_spec
  obtain ⟨x₂, hbuild, hC₂, hP₂, hpres₂, hfr₂⟩ := buildTablesCode_exec x₁ inp.last h1 hl₁
    (by rw [hs₁]; exact hw.of_le (by omega))
    (by rw [hcb₁, hsig₁]; exact hw.of_le (by omega))
    (by rw [hpb₁]; exact hw.of_le (by omega))
    (by rw [hs₁, hcb₁])
    (by rw [hcb₁, hsig₁, hpb₁])
    (by rwa [hsig₁])
    (by rw [hs₁, hmem₁]; exact hL_init)
  rw [hsig₁] at hbuild
  have hs₂ := (hfr₂ src (by decide)).trans hs₁
  have hl₂ := (hfr₂ len (by decide)).trans hl₁
  have hr₂ := (hfr₂ row (by decide)).trans hr₁
  have hcb₂ := (hfr₂ cBase (by decide)).trans hcb₁
  have hpb₂ := (hfr₂ pBase (by decide)).trans hpb₁
  have hbuf₂ := (hfr₂ buf (by decide)).trans hbuf₁
  obtain ⟨y, hdec, hout, _, hy_end⟩ := lfDecodeCode_exec x₂ inp.last inp.alphabetSize h1
    hvalid hl₂
    (by rw [hbuf₂]; exact hw.of_le (by omega))
    (by rw [hs₂]; exact hw.of_le (by omega))
    (by rw [hcb₂]; exact hw.of_le (by omega))
    (by rw [hpb₂]; exact hw.of_le (by omega))
    (by rw [hs₂, hbuf₂]; omega)
    (by rw [hcb₂, hbuf₂]; omega)
    (by rw [hpb₂, hbuf₂]; omega)
    (by
      intro i hi
      rw [hs₂, hpres₂ (3 + i) (by rw [hcb₁, hsig₁]; omega) (by rw [hpb₁]; omega), hmem₁]
      exact hL_init i hi)
    (by
      intro b hb
      rw [hcb₂, ← hcb₁]
      exact hC₂ b (by rwa [hsig₁]))
    (by
      intro i hi
      rw [hpb₂, ← hpb₁, ← getElem_rankTable inp.last hi]
      exact hP₂.get i (by rwa [length_rankTable]))
  rw [hr₂] at hout hy_end
  rw [hbuf₂] at hy_end
  refine ⟨y, (hsetup.seq (hbuild.seq hdec)).mono (by omega), hout, ?_⟩
  rw [hy_end]
  exact hw.of_le (by omega)

/-- `decodeProgram` computes `inverseBwt (inp.last, inp.index)` in `25 * |L| + 11 * σ + 34`
instructions at every fitting width with `inp.Valid`, `Fits w (3 * |L| + σ + 4)`, and
`InputFits w inp.encode` (the `ComputesListInTime` input-fit hypothesis, which bounds an arbitrary
encoded starting row `I`). -/
theorem decodeProgram_computesListInTime :
    decodeProgram.ComputesListInTime
      (fun _ (inp : Input) => inp.encode)
      (fun inp _ => 25 * inp.last.length + 11 * inp.alphabetSize + 34)
      (fun inp w => inp.Valid ∧ Fits w (3 * inp.last.length + inp.alphabetSize + 4))
      (fun inp => inverseBwt (inp.last, inp.index)) :=
  decodeCode.computesListInTime_program out fun inp w ⟨hvalid, hw⟩ _ =>
    decodeCode_exec inp w hvalid hw

/-- On `bwt u` over an integer alphabet `< σ`, `decodeProgram` recovers `u` within
`25 * |u| + 11 * σ + 34` instructions at any word width `w` with `Fits w (3 * |u| + σ + 4)`. -/
theorem decodeProgram_bwt (u : List ℕ) (σ w : ℕ)
    (hu : ∀ c ∈ u, c < σ)
    (hw : Fits w (3 * u.length + σ + 4)) :
    ∃ t, ExecutesList w decodeProgram (.init (Input.mk (bwtLast u) (bwtIndex u) σ).encode) u t ∧
      t ≤ 25 * u.length + 11 * σ + 34 := by
  let inp : Input := ⟨bwtLast u, bwtIndex u, σ⟩
  have hvalid : inp.Valid := fun c hc => hu c ((bwtLast_perm u).subset hc)
  have hlen_last : (bwtLast u).length = u.length := length_bwtLast u
  have hw_inp : Fits w (3 * inp.last.length + inp.alphabetSize + 4) := by
    dsimp only [inp]
    rwa [hlen_last]
  have hidx_le : bwtIndex u ≤ u.length := by
    rcases eq_or_ne u [] with rfl | hne
    · have hlt := bwtIndex_lt_length ([] : List ℕ)
      rw [bwtMatrix_nil, List.length_singleton] at hlt
      omega
    · have hlt := bwtIndex_lt_length u
      rw [length_bwtMatrix hne] at hlt
      omega
  have hfits : InputFits w inp.encode := by
    refine ⟨hw.of_le (by dsimp only [inp]; rw [length_encode, hlen_last]; omega), ?_⟩
    intro x hx
    simp only [Input.encode, inp, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hw.of_le (by omega)
    · exact hw.of_le (by omega)
    · have hlt : x < σ := hvalid x hx
      exact hw.of_le (by omega)
  obtain ⟨t, hexec, ht⟩ := decodeProgram_computesListInTime inp w ⟨hvalid, hw_inp⟩ hfits
  dsimp only at hexec ht
  have hinv : inverseBwt (inp.last, inp.index) = u := by
    simpa only [inp, ← fst_bwt, ← snd_bwt, Prod.eta] using inverseBwt_bwt u
  rw [hinv] at hexec
  dsimp only [inp] at hexec ht
  rw [hlen_last] at ht
  exact ⟨t, hexec, ht⟩

end Cslib.Algorithms.WordRAM.BurrowsWheeler
