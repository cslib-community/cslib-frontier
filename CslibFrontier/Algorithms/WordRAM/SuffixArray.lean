/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.SuffixArray.Kasai
public import CslibFrontier.Algorithms.Lean.SuffixArray.Search
public import CslibFrontier.Algorithms.WordRAM.BinarySearch
public import CslibFrontier.Computability.WordRAM.ListOutput
import CslibFrontier.Computability.WordRAM.Allocation
import CslibFrontier.Computability.WordRAM.InputArray
import CslibFrontier.Computability.WordRAM.ListArray
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Suffix-Array LCP Construction and Pattern Search on the Word RAM

This module implements Kasai et al.'s linear-time LCP array construction
(`[KasaiLeeArimuraArikawaPark2001]`) and Manber and Myers's `O(|p| log |sa|)` suffix-array pattern
search (`[ManberMyers1993]`) as uniform 20-register `Basis.standard` Word-RAM programs over word
arrays, charging every memory read and write, rank-array scatter step, character comparison,
arithmetic operation, and loop branch.

## Memory layouts and cost bounds

1. **Kasai LCP array construction (`kasaiCode`, `kasaiProgram`):**
   * **Input (`State.init I.encode`):** `KasaiInput.encode I = |text| :: |sa| :: (text ++ sa)`
     places `|text|` at `mem[1]`, `|sa|` at `mem[2]`, `text` at `[3, 3 + |text|)`, and `sa` at
     `[3 + |text|, 3 + |text| + |sa|)`.
   * **Workspace and output:** zero-initializes the rank array `rk` at
     `[3 + |text| + |sa|, 3 + 2 * |text| + |sa|)` via `Cslib.WordRAM.zeroFill`, scatters ranks from
     `sa`, and writes `kasai I.text I.sa` (`= lcpArray I.text I.sa` when
     `IsSuffixArray I.text I.sa`) as a length-prefixed array at
     `y.regs Reg.out = 3 + 2 * |text| + |sa|`, preserving `text` and `sa`.
   * **Amortized analysis and time:** using the potential
     $$\Phi(i, h) = 47 \cdot (|text| - i) - 14 \cdot \min(h, |text| - i),$$
     each matched character in `kasaiExtBody` (`14` instructions) increases `h` up to at most
     `|text| - i`, while `h` drops by at most `1` between text positions. On every input
     `(text, sa)` and word width `w` with `Fits w (3 * |text| + |sa| + 4)`, `kasaiCode` executes
     within `55 * |text| + 8 * |sa| + 25` instructions (`55 * |text| + 8 * |sa| + 26` for
     `kasaiProgram`, and `63 * |text| + 26` when `IsSuffixArray I.text I.sa`).

2. **Suffix-array rank-interval and occurrence search (`rangeSearchCode`, `rangeSearchProgram`,
   `occurrencesCode`, `occurrencesProgram`):**
   * **Input (`State.init I.encode`):**
     `SearchInput.encode I = |text| :: |sa| :: |pat| :: (text ++ sa ++ pat)` places `|text|`,
     `|sa|`, `|pat|` at `mem[1..3]` and `text`, `sa`, `pat` contiguously from `mem[4]`.
   * **Execution and time:** runs `Cslib.Algorithms.WordRAM.BinarySearch.bisectCode` twice over
     `[0, |sa|)` using an overflow-safe `O(|pat|)` suffix-comparison probe (`16 * |pat| + 24`
     instructions per probe).
     - `rangeSearchProgram` outputs `[(search I.text I.sa I.pat).1, (search I.text I.sa I.pat).2]`
       at `y.regs Reg.out = 4 + |text| + |sa| + |pat|` within
       `(32 * |pat| + 63) * (Nat.log 2 |sa| + 1) + 26` instructions (`O(|pat| log |sa|)` independent
       of occurrence count) whenever `Fits w (|text| + |sa| + |pat| + 6)`.
     - `occurrencesProgram` outputs `occurrences I.text I.sa I.pat` within
       `(32 * |pat| + 63) * (Nat.log 2 |sa| + 1) + 9 * |occurrences I.text I.sa I.pat| + 27`
       instructions whenever `Fits w (|text| + 2 * |sa| + |pat| + 6)`.

## Main definitions

* `Cslib.Algorithms.WordRAM.SuffixArray.KasaiInput`, `KasaiInput.encode`: input record and word
  encoding for Kasai LCP construction.
* `Cslib.Algorithms.WordRAM.SuffixArray.SearchInput`, `SearchInput.encode`: input record and word
  encoding for suffix-array pattern search.
* `Cslib.Algorithms.WordRAM.SuffixArray.Reg.out`: output base register (`19`).
* `Cslib.Algorithms.WordRAM.SuffixArray.kasaiCode`, `kasaiProgram`: Word-RAM Kasai LCP construction.
* `Cslib.Algorithms.WordRAM.SuffixArray.rangeSearchCode`, `rangeSearchProgram`: Word-RAM
  `O(|pat| log |sa|)` suffix-array rank-interval search.
* `Cslib.Algorithms.WordRAM.SuffixArray.occurrencesCode`, `occurrencesProgram`: Word-RAM
  `O(|pat| log |sa| + occ)` suffix-array occurrence-list search.

## Main results

* `Cslib.Algorithms.WordRAM.SuffixArray.kasaiCode_exec`, `kasaiProgram_computesListInTime`, and
  `kasaiProgram_computesLcpArrayInTime`: linear-time Word-RAM Kasai LCP bounds.
* `Cslib.Algorithms.WordRAM.SuffixArray.rangeSearchCode_exec` and
  `rangeSearchProgram_computesListInTime`: `O(|pat| log |sa|)` Word-RAM rank-interval search bounds.
* `Cslib.Algorithms.WordRAM.SuffixArray.occurrencesCode_exec`,
  `occurrencesProgram_computesListInTime`, and `occurrencesProgram_computesListInTime_worstCase`:
  `O(|pat| log |sa| + occ)` and `O(|pat| log |sa| + |sa|)` Word-RAM occurrence-reporting bounds.

## References

* [T. Kasai, G. Lee, H. Arimura, S. Arikawa, and K. Park, *Linear-Time Longest-Common-Prefix
  Computation in Suffix Arrays and Its Applications*][KasaiLeeArimuraArikawaPark2001]
* [U. Manber and G. Myers, *Suffix Arrays: A New Method for On-Line String
  Searches*][ManberMyers1993]
-/

public section

namespace Cslib.Algorithms.WordRAM.SuffixArray

open Cslib.WordRAM
open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.SuffixArray
open Cslib.Algorithms.WordRAM.BinarySearch (bisectCode bisectCode_exec)

/-! ## Input encodings and registers -/

/-- Input to Word-RAM Kasai LCP array construction: a word `text` and a candidate suffix array
`sa`. -/
structure KasaiInput where
  /-- Input text over word alphabet `ℕ`. -/
  text : List ℕ
  /-- Candidate suffix array (list of starting positions). -/
  sa : List ℕ
  deriving DecidableEq, Repr

/-- Flat word-list encoding `[|text|, |sa|] ++ text ++ sa`: `State.init I.encode` places `|text|`
at `mem[1]`, `|sa|` at `mem[2]`, `text` at `[3, 3 + |text|)`, and `sa` at
`[3 + |text|, 3 + |text| + |sa|)`. -/
@[expose] def KasaiInput.encode (I : KasaiInput) : List ℕ :=
  I.text.length :: I.sa.length :: (I.text ++ I.sa)

/-- Input to Word-RAM suffix-array pattern search: text `text`, suffix array `sa`, and pattern
`pat`. -/
structure SearchInput where
  /-- Input text over word alphabet `ℕ`. -/
  text : List ℕ
  /-- Suffix array of `text` (list of starting positions). -/
  sa : List ℕ
  /-- Pattern to search for in `text`. -/
  pat : List ℕ
  deriving DecidableEq, Repr

/-- Flat word-list encoding `[|text|, |sa|, |pat|] ++ text ++ sa ++ pat`: `State.init I.encode`
places `|text|`, `|sa|`, `|pat|` at `mem[1..3]`, `text` at `[4, 4 + |text|)`, `sa` at
`[4 + |text|, 4 + |text| + |sa|)`, and `pat` at
`[4 + |text| + |sa|, 4 + |text| + |sa| + |pat|)`. -/
@[expose] def SearchInput.encode (I : SearchInput) : List ℕ :=
  I.text.length :: I.sa.length :: I.pat.length :: (I.text ++ I.sa ++ I.pat)

private abbrev zero : Fin 20 := 0
private abbrev one : Fin 20 := 1
private abbrev textBase : Fin 20 := 2
private abbrev textLen : Fin 20 := 3
private abbrev saBase : Fin 20 := 4
private abbrev saLen : Fin 20 := 5
private abbrev rkBase : Fin 20 := 6
private abbrev patBase : Fin 20 := 6
private abbrev lcpBase : Fin 20 := 7
private abbrev patLen : Fin 20 := 7
private abbrev regi : Fin 20 := 8
private abbrev loReg : Fin 20 := 8
private abbrev regh : Fin 20 := 9
private abbrev hiReg : Fin 20 := 9
private abbrev regr : Fin 20 := 10
private abbrev midReg : Fin 20 := 10
private abbrev regj : Fin 20 := 11
private abbrev resReg : Fin 20 := 11
private abbrev savedLo : Fin 20 := 12
private abbrev posReg : Fin 20 := 13
private abbrev regk : Fin 20 := 14
private abbrev go : Fin 20 := 15
private abbrev t0 : Fin 20 := 16
private abbrev t1 : Fin 20 := 17
private abbrev twoReg : Fin 20 := 18

/-- Output base register (`19`) for all programs in `Cslib.Algorithms.WordRAM.SuffixArray`. -/
abbrev Reg.out : Fin 20 := 19

open Reg

/-! ## Shared memory helpers -/

private theorem init_holdsList_append {r : ℕ} (pre payload post : List ℕ) :
    Block.HoldsList (pre.length + 1) payload
      (Data.init (pre ++ (payload ++ post)) : Data r).mem := fun i => by
  have h := Data.init_realizes_append (r := r) pre payload post i
  change (Data.init (pre ++ (payload ++ post)) : Data r).mem (pre.length + 1 + i.val) =
    payload[i.val]
  simpa only [Block.read, List.get_eq_getElem] using h

private theorem holdsList_replicate_clear (m : ℕ → ℕ) (base k : ℕ) :
    Block.HoldsList base (List.replicate k 0) (clear m base k) := by
  intro i
  change clear m base k (base + i.val) = (List.replicate k 0)[i.val]
  rw [List.getElem_replicate]
  exact Block.realizes_clear m base k ⟨i.val, by simpa using i.isLt⟩

private theorem holdsList_set!_lt {base : ℕ} {arr : Array ℕ} {mem : ℕ → ℕ}
    (h : Block.HoldsList base arr.toList mem) {idx : ℕ} (hidx : idx < arr.size) (v : ℕ) :
    Block.HoldsList base (arr.set! idx v).toList (Function.update mem (base + idx) v) := by
  rintro ⟨jv, hjv⟩
  have hj : jv < arr.size := by
    dsimp only at hjv
    rwa [Array.length_toList, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds] at hjv
  change Function.update mem (base + idx) v (base + jv) = (arr.set! idx v).toList[jv]
  rw [Array.getElem_toList]
  simp only [Array.set!_eq_setIfInBounds]
  by_cases heq : jv = idx
  · subst heq
    rw [Function.update_self, Array.getElem_setIfInBounds_self]
  · rw [Function.update_of_ne (by omega), Array.getElem_setIfInBounds_ne hj (Ne.symm heq)]
    exact (h.get jv (by simpa using hj)).trans (Array.getElem_toList _)

private theorem holdsList_set!_ge {base : ℕ} {arr : Array ℕ} {mem : ℕ → ℕ}
    (h : Block.HoldsList base arr.toList mem) {idx : ℕ} (hidx : ¬idx < arr.size) (v : ℕ) :
    Block.HoldsList base (arr.set! idx v).toList mem := by
  have heq : arr.set! idx v = arr := by
    rw [Array.set!_eq_setIfInBounds]
    apply Array.ext
    · exact Array.size_setIfInBounds
    · intro k hk1 hk2
      exact Array.getElem_setIfInBounds_ne hk2 (by omega)
  rwa [heq]

/-! ## Part 1: Kasai et al.'s `O(n)` LCP array construction -/

private def kasaiSetup : Code .standard 20 := ram[
  zero ← #0;
  one ← #1;
  t0 ← #2;
  textBase ← #3;
  textLen ← *one;
  saLen ← *t0;
  saBase ← textBase + textLen;
  rkBase ← saBase + saLen;
  out ← rkBase + textLen;
  *out ← textLen;
  lcpBase ← out + one ]

private def kasaiZeroInit : Code .standard 20 := ram[
  t0 ← rkBase;
  ⟪zeroFill t0 out zero one⟫;
  t0 ← lcpBase;
  t1 ← lcpBase + textLen;
  ⟪zeroFill t0 t1 zero one⟫ ]

private def scatterBody : Code .standard 20 := ram[
  t0 ← saBase + regi;
  t0 ← *t0;
  if t0 < textLen then [
    t1 ← rkBase + t0;
    *t1 ← regi;
    regi ← regi + one
  ] else [
    regi ← regi + one
  ] ]

private def scatterCode : Code .standard 20 :=
  .seq (ram[ regi ← zero ]) (.loop (.lt regi saLen) scatterBody)

private def kasaiExtLoads : Code .standard 20 := ram[
  t0 ← regj + regh;
  t0 ← textBase + t0;
  t0 ← *t0;
  t1 ← regi + regh;
  t1 ← textBase + t1;
  t1 ← *t1 ]

private def kasaiExtBody : Code .standard 20 := ram[
  t0 ← textLen - regi;
  if regh < t0 then [
    t0 ← textLen - regh;
    if regj < t0 then [
      ⟪kasaiExtLoads⟫;
      if t0 = t1 then [
        regh ← regh + one
      ] else [
        go ← zero
      ]
    ] else [
      go ← zero
    ]
  ] else [
    go ← zero
  ] ]

private def kasaiBody : Code .standard 20 := ram[
  t0 ← rkBase + regi;
  regr ← *t0;
  if regr = zero then [
    regi ← regi + one
  ] else [
    t0 ← regr - one;
    if t0 < saLen then [
      t1 ← saBase + t0;
      regj ← *t1
    ] else [
      regj ← zero
    ];
    go ← one;
    ⟪.loop (.lt zero go) kasaiExtBody⟫;
    if regr < textLen then [
      t0 ← lcpBase + regr;
      *t0 ← regh
    ] else [
      t0 ← zero
    ];
    regh ← regh - one;
    regi ← regi + one
  ] ]

private def kasaiMainCode : Code .standard 20 :=
  .seq (ram[ regi ← zero; regh ← zero ]) (.loop (.lt regi textLen) kasaiBody)

/-- Structured 20-register Word-RAM program computing `kasai I.text I.sa` at `Reg.out`. -/
def kasaiCode : Code .standard 20 :=
  .seq (.seq kasaiSetup kasaiZeroInit) (.seq scatterCode kasaiMainCode)

/-- Uniform `Basis.standard` Word-RAM program for Kasai et al.'s LCP array construction. -/
def kasaiProgram : Program .standard 20 := kasaiCode.program out

private structure KasaiRegs (I : KasaiInput) (x : Data 20) : Prop where
  zero_eq : x.regs zero = 0
  one_eq : x.regs one = 1
  tb_eq : x.regs textBase = 3
  tl_eq : x.regs textLen = I.text.length
  sb_eq : x.regs saBase = 3 + I.text.length
  sl_eq : x.regs saLen = I.sa.length
  rkb_eq : x.regs rkBase = 3 + I.text.length + I.sa.length
  out_eq : x.regs out = 3 + 2 * I.text.length + I.sa.length
  lcpb_eq : x.regs lcpBase = 4 + 2 * I.text.length + I.sa.length

private theorem KasaiRegs.set_scratch {I : KasaiInput} {x : Data 20} (hr : KasaiRegs I x)
    (d : Fin 20) (v : ℕ)
    (h0 : zero ≠ d := by decide) (h1 : one ≠ d := by decide)
    (htb : textBase ≠ d := by decide) (htl : textLen ≠ d := by decide)
    (hsb : saBase ≠ d := by decide) (hsl : saLen ≠ d := by decide)
    (hrk : rkBase ≠ d := by decide) (ho : out ≠ d := by decide)
    (hlb : lcpBase ≠ d := by decide) : KasaiRegs I (x.set d v) :=
  ⟨(Data.set_regs_of_ne h0 v).trans hr.zero_eq,
   (Data.set_regs_of_ne h1 v).trans hr.one_eq,
   (Data.set_regs_of_ne htb v).trans hr.tb_eq,
   (Data.set_regs_of_ne htl v).trans hr.tl_eq,
   (Data.set_regs_of_ne hsb v).trans hr.sb_eq,
   (Data.set_regs_of_ne hsl v).trans hr.sl_eq,
   (Data.set_regs_of_ne hrk v).trans hr.rkb_eq,
   (Data.set_regs_of_ne ho v).trans hr.out_eq,
   (Data.set_regs_of_ne hlb v).trans hr.lcpb_eq⟩

private theorem KasaiRegs.write_mem {I : KasaiInput} {x : Data 20} (hr : KasaiRegs I x)
    (a v : ℕ) : KasaiRegs I (x.write a v) :=
  ⟨hr.zero_eq, hr.one_eq, hr.tb_eq, hr.tl_eq, hr.sb_eq, hr.sl_eq, hr.rkb_eq, hr.out_eq,
   hr.lcpb_eq⟩

private theorem KasaiRegs.kasai_exec {I : KasaiInput} {c : Code .standard 20} {x y : Data 20}
    {w T : ℕ} (hr : KasaiRegs I x) (he : ExecWithin w c x y T)
    (h0 : c.Preserves zero := by decide) (h1 : c.Preserves one := by decide)
    (htb : c.Preserves textBase := by decide) (htl : c.Preserves textLen := by decide)
    (hsb : c.Preserves saBase := by decide) (hsl : c.Preserves saLen := by decide)
    (hrk : c.Preserves rkBase := by decide) (ho : c.Preserves out := by decide)
    (hlb : c.Preserves lcpBase := by decide) : KasaiRegs I y :=
  ⟨(he.regs_eq h0).trans hr.zero_eq, (he.regs_eq h1).trans hr.one_eq,
   (he.regs_eq htb).trans hr.tb_eq, (he.regs_eq htl).trans hr.tl_eq,
   (he.regs_eq hsb).trans hr.sb_eq, (he.regs_eq hsl).trans hr.sl_eq,
   (he.regs_eq hrk).trans hr.rkb_eq, (he.regs_eq ho).trans hr.out_eq,
   (he.regs_eq hlb).trans hr.lcpb_eq⟩

private theorem init_kasaiEncode (I : KasaiInput) :
    let x : Data 20 := Data.init I.encode
    x.mem 1 = I.text.length ∧ x.mem 2 = I.sa.length ∧
      Block.HoldsList 3 I.text x.mem ∧
      Block.HoldsList (3 + I.text.length) I.sa x.mem := by
  intro x
  obtain ⟨hm1, hhdr2⟩ := Block.holdsList_cons_iff.mp
    (init_holdsList_append (r := 20) [] [I.text.length, I.sa.length] (I.text ++ I.sa))
  obtain ⟨hm2, _⟩ := Block.holdsList_cons_iff.mp hhdr2
  have hsa := init_holdsList_append (r := 20) (I.text.length :: I.sa.length :: I.text) I.sa []
  have hlen : (I.text.length :: I.sa.length :: I.text).length + 1 = 3 + I.text.length := by
    simp only [List.length_cons]
    omega
  rw [hlen] at hsa
  exact ⟨hm1, hm2,
    init_holdsList_append (r := 20) [I.text.length, I.sa.length] I.text I.sa,
    by
      dsimp only [x, KasaiInput.encode]
      simpa only [List.append_nil, List.cons_append] using hsa⟩

private theorem kasaiSetupAndZero_spec (I : KasaiInput) {w : ℕ}
    (hw : Fits w (3 * I.text.length + I.sa.length + 4)) :
    ∃ x₁, ExecWithin w (.seq kasaiSetup kasaiZeroInit) (Data.init I.encode) x₁
        (8 * I.text.length + 18) ∧
      KasaiRegs I x₁ ∧
      x₁.mem (3 + 2 * I.text.length + I.sa.length) = I.text.length ∧
      Block.HoldsList 3 I.text x₁.mem ∧
      Block.HoldsList (3 + I.text.length) I.sa x₁.mem ∧
      Block.HoldsList (3 + I.text.length + I.sa.length)
        (rankArray I.text.length []).toList x₁.mem ∧
      Block.HoldsList (4 + 2 * I.text.length + I.sa.length)
        (List.replicate I.text.length 0) x₁.mem := by
  let x : Data 20 := Data.init I.encode
  obtain ⟨hm1, hm2, htxt, hsa⟩ := init_kasaiEncode I
  let n := I.text.length
  let m := I.sa.length
  have hf_1 : Fits w 1 := hw.of_le (by omega)
  have hf_2 : Fits w 2 := hw.of_le (by omega)
  have hf_3 : Fits w 3 := hw.of_le (by omega)
  have hf_sb : Fits w (3 + I.text.length) := hw.of_le (by omega)
  have hf_rkb : Fits w (3 + I.text.length + I.sa.length) := hw.of_le (by omega)
  have hf_out : Fits w (3 + I.text.length + I.sa.length + I.text.length) := hw.of_le (by omega)
  have hf_lcpb : Fits w (3 + I.text.length + I.sa.length + I.text.length + 1) :=
    hw.of_le (by omega)
  have hf_lcpe : Fits w (4 + 2 * n + m + n) := hw.of_le (by omega)
  have hsetup : ∃ s₀, ExecWithin w kasaiSetup x s₀ 11 ∧
      KasaiRegs I s₀ ∧
      s₀.mem (3 + 2 * n + m) = n ∧
      Block.HoldsList 3 I.text s₀.mem ∧
      Block.HoldsList (3 + n) I.sa s₀.mem := by
    refine WP.exists_execWithin ?_
    unfold kasaiSetup
    wram_exec [x, Data.init_regs, hm1, hm2, hf_1, hf_2, hf_3, hf_sb, hf_rkb, hf_out, hf_lcpb]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · wram_simp
    · wram_simp
    · wram_simp
    · wram_simp
    · wram_simp
    · wram_simp
    · wram_simp
    · wram_simp
      omega
    · wram_simp
      omega
    · have hout_idx : 3 + I.text.length + I.sa.length + I.text.length = 3 + 2 * n + m := by omega
      simp only [Data.set_mem, Data.write_mem, hout_idx, Function.update_self, n]
    · exact htxt.frame fun a _ ha2 => by
        simp only [Data.set_mem, Data.write_mem]
        rw [Function.update_of_ne (by omega)]
    · exact hsa.frame fun a _ ha2 => by
        simp only [Data.set_mem, Data.write_mem]
        rw [Function.update_of_ne (by omega)]
  obtain ⟨s₀, es₀, hrs₀, hmem_out, htxt₀, hsa₀⟩ := hsetup
  set s₁ := s₀.set t0 (3 + n + m)
  have hrs₁ : KasaiRegs I s₁ := hrs₀.set_scratch t0 _
  have hs₁_t0 : s₁.regs t0 = 3 + n + m := Data.set_regs_self s₀ t0 _
  have ez₁ := (zeroFill_exec (w := w) (cur := t0) (stop := out) (zero := zero) (one := one)
    (x := s₁) (by decide) (by decide) (by decide) hrs₁.zero_eq hrs₁.one_eq
    (by rw [hs₁_t0, hrs₁.out_eq]; omega)
    (by rw [hrs₁.out_eq]; exact hw.of_le (by omega))).within
  set s₂ : Data 20 := ⟨Function.update s₁.regs t0 (s₁.regs out),
    clear s₁.mem (s₁.regs t0) (s₁.regs out - s₁.regs t0)⟩
  have hdiff₁ : s₁.regs out - s₁.regs t0 = n := by
    rw [hrs₁.out_eq, hs₁_t0]
    omega
  rw [hdiff₁] at ez₁
  have hrs₂ : KasaiRegs I s₂ := hrs₁.kasai_exec ez₁
  set s₄ := (s₂.set t0 (4 + 2 * n + m)).set t1 (4 + 2 * n + m + n)
  have hrs₄ : KasaiRegs I s₄ := (hrs₂.set_scratch t0 _).set_scratch t1 _
  have hs₄_t0 : s₄.regs t0 = 4 + 2 * n + m := by wram_simp [s₄]
  have hs₄_t1 : s₄.regs t1 = 4 + 2 * n + m + n := Data.set_regs_self _ t1 _
  have ez₂ := (zeroFill_exec (w := w) (cur := t0) (stop := t1) (zero := zero) (one := one)
    (x := s₄) (by decide) (by decide) (by decide) hrs₄.zero_eq hrs₄.one_eq
    (by rw [hs₄_t0, hs₄_t1]; omega)
    (hs₄_t1 ▸ hf_lcpe)).within
  set x₁ : Data 20 := ⟨Function.update s₄.regs t0 (s₄.regs t1),
    clear s₄.mem (s₄.regs t0) (s₄.regs t1 - s₄.regs t0)⟩
  have hdiff₂ : s₄.regs t1 - s₄.regs t0 = n := by
    rw [hs₄_t1, hs₄_t0]
    omega
  rw [hdiff₂] at ez₂
  have hx₁_mem : x₁.mem = clear (clear s₀.mem (3 + n + m) n) (4 + 2 * n + m) n := by
    change clear s₄.mem (s₄.regs t0) (s₄.regs t1 - s₄.regs t0) = _
    rw [hdiff₂, hs₄_t0]
    change clear (clear s₁.mem (s₁.regs t0) (s₁.regs out - s₁.regs t0)) _ _ = _
    rw [hdiff₁, hs₁_t0]
    rfl
  have hinit_exec : ExecWithin w kasaiZeroInit s₀ x₁ (8 * n + 7) :=
    WP.execWithin <| by
      unfold kasaiZeroInit
      wram_exec [hrs₀.rkb_eq]
      refine WP.of_execWithin ez₁ ?_
      wram_exec [hrs₂.lcpb_eq, hrs₂.tl_eq, hf_lcpe]
      exact WP.of_execWithin ez₂ ⟨by omega, rfl⟩
  have hclr (a : ℕ) (ha : a < 3 + n + m ∨ a = 3 + 2 * n + m) : x₁.mem a = s₀.mem a := by
    rw [hx₁_mem, clear_of_not_owns (by simp only [Block.Owns]; omega),
      clear_of_not_owns (by simp only [Block.Owns]; omega)]
  refine ⟨x₁, (es₀.seq hinit_exec).mono (by omega), hrs₀.kasai_exec hinit_exec,
    (hclr _ (Or.inr rfl)).trans hmem_out,
    htxt₀.frame (fun a _ ha2 => hclr a (Or.inl (by omega))),
    hsa₀.frame (fun a _ ha2 => hclr a (Or.inl (by omega))), ?_, ?_⟩
  · rw [rankArray_nil, Array.toList_replicate, hx₁_mem]
    exact (holdsList_replicate_clear s₀.mem (3 + n + m) n).frame fun a _ ha2 => by
      simp only [List.length_replicate] at ha2
      exact clear_of_not_owns (by simp only [Block.Owns]; omega)
  · rw [hx₁_mem]
    exact holdsList_replicate_clear _ (4 + 2 * n + m) n

private structure ScatterInv (I : KasaiInput) (x₀ : Data 20) (x : Data 20) : Prop where
  regs : KasaiRegs I x
  r_le : x.regs regi ≤ I.sa.length
  out_hdr : x.mem (3 + 2 * I.text.length + I.sa.length) = I.text.length
  txt_holds : Block.HoldsList 3 I.text x.mem
  sa_holds : Block.HoldsList (3 + I.text.length) I.sa x.mem
  rk_holds : Block.HoldsList (3 + I.text.length + I.sa.length)
    (rankArray I.text.length (I.sa.take (x.regs regi))).toList x.mem
  lcp_holds : Block.HoldsList (4 + 2 * I.text.length + I.sa.length)
    (List.replicate I.text.length 0) x.mem

private theorem scatterCode_spec (I : KasaiInput) {w : ℕ}
    (hw : Fits w (3 * I.text.length + I.sa.length + 4))
    (x₁ : Data 20) (hrx₁ : KasaiRegs I x₁)
    (hout : x₁.mem (3 + 2 * I.text.length + I.sa.length) = I.text.length)
    (htxt : Block.HoldsList 3 I.text x₁.mem)
    (hsa : Block.HoldsList (3 + I.text.length) I.sa x₁.mem)
    (hrk : Block.HoldsList (3 + I.text.length + I.sa.length)
      (rankArray I.text.length []).toList x₁.mem)
    (hlcp : Block.HoldsList (4 + 2 * I.text.length + I.sa.length)
      (List.replicate I.text.length 0) x₁.mem) :
    ∃ x₂, ExecWithin w scatterCode x₁ x₂ (8 * I.sa.length + 3) ∧
      KasaiRegs I x₂ ∧
      x₂.mem (3 + 2 * I.text.length + I.sa.length) = I.text.length ∧
      Block.HoldsList 3 I.text x₂.mem ∧
      Block.HoldsList (3 + I.text.length) I.sa x₂.mem ∧
      Block.HoldsList (3 + I.text.length + I.sa.length)
        (rankArray I.text.length I.sa).toList x₂.mem ∧
      Block.HoldsList (4 + 2 * I.text.length + I.sa.length)
        (List.replicate I.text.length 0) x₂.mem := by
  let n := I.text.length
  let m := I.sa.length
  set s₀ := x₁.set regi 0
  have e₀ : ExecWithin (B := .standard) w (ram[ regi ← zero ]) x₁ s₀ 1 :=
    WP.execWithin <| by
      wram_exec [hrx₁.zero_eq]
      rfl
  have hs₀_inv : ScatterInv I x₁ s₀ :=
    ⟨hrx₁.set_scratch regi 0,
     by simp only [s₀, Data.set_regs_self, Nat.zero_le],
     hout, htxt, hsa,
     by
       change Block.HoldsList (3 + I.text.length + I.sa.length)
         (rankArray I.text.length (I.sa.take (s₀.regs regi))).toList x₁.mem
       simpa only [s₀, Data.set_regs_self, List.take_zero] using hrk,
     hlcp⟩
  have hloop := ExecWithin.loop_invariant (w := w) (cond := .lt regi saLen) (body := scatterBody)
    (ScatterInv I x₁) (fun s => m - s.regs regi) (T := 6)
    (fun s hs hc => by
      simp only [Cond.holds_lt, hs.regs.sl_eq] at hc
      set r := s.regs regi
      have hs_sar : s.mem (3 + I.text.length + s.regs regi) = I.sa[r] := hs.sa_holds.get r hc
      have hf_sa_addr : Fits w (3 + n + r) := hw.of_le (by omega)
      have hf_r1 : Fits w (r + 1) := hw.of_le (by omega)
      have htake_step : I.sa.take (r + 1) = I.sa.take r ++ [I.sa[r]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hc, Option.toList_some]
      have htake_len : (I.sa.take r).length = r := List.length_take_of_le (by omega)
      by_cases hlt : I.sa[r] < n
      · have hf_rk_addr : Fits w (3 + n + m + I.sa[r]) := hw.of_le (by omega)
        have hstep : ∃ u, ExecWithin w scatterBody s u 6 ∧
            u.regs regi = r + 1 ∧
            u.mem = Function.update s.mem (3 + n + m + I.sa[r]) r := by
          refine WP.exists_execWithin ?_
          unfold scatterBody
          wram_exec [hs.regs.sb_eq, hs.regs.tl_eq, hs.regs.rkb_eq, hs.regs.one_eq,
            hs_sar, hf_sa_addr, hf_rk_addr, hf_r1]
          refine ⟨?_, ?_⟩
          · wram_simp [r]
          · dsimp only [n, m, r]
            simp only [Data.set_mem, Data.write_mem]
        obtain ⟨u, hexec, hur, humem⟩ := hstep
        refine ⟨u, hexec, ⟨hs.regs.kasai_exec hexec, by rw [hur]; omega, ?_, ?_, ?_, ?_, ?_⟩,
          by rw [hur]; omega⟩
        · rw [humem, Function.update_of_ne (by omega)]
          exact hs.out_hdr
        · exact hs.txt_holds.frame fun a _ ha2 => by
            rw [humem, Function.update_of_ne (by omega)]
        · exact hs.sa_holds.frame fun a _ ha2 => by
            rw [humem, Function.update_of_ne (by omega)]
        · rw [hur, htake_step, rankArray_append_singleton, htake_len, humem]
          exact holdsList_set!_lt hs.rk_holds (by rw [size_rankArray]; exact hlt) r
        · exact hs.lcp_holds.frame fun a ha1 _ => by
            rw [humem, Function.update_of_ne (by omega)]
      · have hstep : ∃ u, ExecWithin w scatterBody s u 6 ∧
            u.regs regi = r + 1 ∧ u.mem = s.mem := by
          refine WP.exists_execWithin ?_
          unfold scatterBody
          wram_exec [hs.regs.sb_eq, hs.regs.tl_eq, hs.regs.one_eq, hs_sar, hf_sa_addr, hf_r1]
          refine ⟨?_, rfl⟩
          wram_simp [r]
        obtain ⟨u, hexec, hur, humem⟩ := hstep
        refine ⟨u, hexec, ⟨hs.regs.kasai_exec hexec, by rw [hur]; omega,
          humem ▸ hs.out_hdr, humem ▸ hs.txt_holds, humem ▸ hs.sa_holds, ?_, humem ▸ hs.lcp_holds⟩,
          by rw [hur]; omega⟩
        rw [hur, htake_step, rankArray_append_singleton, htake_len, humem]
        exact holdsList_set!_ge hs.rk_holds (by simpa only [size_rankArray] using hlt) r)
    hs₀_inv
  obtain ⟨x₂, eloop, hx₂_inv, hnc⟩ := hloop
  simp only [Cond.holds_lt, hx₂_inv.regs.sl_eq, not_lt] at hnc
  have hr_eq : x₂.regs regi = m := le_antisymm hx₂_inv.r_le hnc
  have hs₀_r : s₀.regs regi = 0 := Data.set_regs_self x₁ regi 0
  rw [hs₀_r, Nat.sub_zero] at eloop
  have hrk_fin := hx₂_inv.rk_holds
  rw [hr_eq, List.take_length] at hrk_fin
  unfold scatterCode
  exact ⟨x₂, (e₀.seq eloop).mono (by omega), hx₂_inv.regs, hx₂_inv.out_hdr,
    hx₂_inv.txt_holds, hx₂_inv.sa_holds, hrk_fin, hx₂_inv.lcp_holds⟩

private theorem kasaiExt_stop {I : KasaiInput} {w T : ℕ} {x s₁ : Data 20}
    (hc_go : (Cond.lt zero go).Holds x)
    (hbody : ExecWithin w kasaiExtBody x s₁ T)
    (hT : T + 4 ≤ 17)
    (hrs₁ : KasaiRegs I s₁)
    (hs₁_go : s₁.regs go = 0)
    (hs₁_i : s₁.regs regi = x.regs regi)
    (hs₁_h : s₁.regs regh = x.regs regh)
    (hs₁_r : s₁.regs regr = x.regs regr)
    (hs₁_mem : s₁.mem = x.mem)
    (hlcp0 : List.lcpLen (I.text.drop (x.regs regj + x.regs regh))
      (I.text.drop (x.regs regi + x.regs regh)) = 0) :
    ∃ y T', ExecWithin w (.loop (.lt zero go) kasaiExtBody) x y T' ∧
      KasaiRegs I y ∧
      y.regs regi = x.regs regi ∧
      y.regs regr = x.regs regr ∧
      y.regs regh = x.regs regh +
        List.lcpLen (I.text.drop (x.regs regj + x.regs regh))
          (I.text.drop (x.regs regi + x.regs regh)) ∧
      T' ≤ 14 * List.lcpLen (I.text.drop (x.regs regj + x.regs regh))
        (I.text.drop (x.regs regi + x.regs regh)) + 17 ∧
      y.mem = x.mem := by
  have hc_stop : ¬(Cond.lt zero go).Holds s₁ := by
    simp only [Cond.holds_lt, hrs₁.zero_eq, hs₁_go]; exact Nat.lt_irrefl 0
  exact ⟨s₁, T + 4, ExecWithin.loop_once hc_go hbody hc_stop, hrs₁,
    hs₁_i, hs₁_r, by rw [hs₁_h, hlcp0, Nat.add_zero],
    by rw [hlcp0]; exact hT, hs₁_mem⟩

private theorem kasaiExt_spec (I : KasaiInput) {w : ℕ}
    (hw : Fits w (3 * I.text.length + I.sa.length + 4)) :
    ∀ (rem : ℕ) (x : Data 20),
      I.text.length - (x.regs regi + x.regs regh) = rem →
      KasaiRegs I x →
      x.regs go = 1 →
      Block.HoldsList 3 I.text x.mem →
      ∃ y T, ExecWithin w (.loop (.lt zero go) kasaiExtBody) x y T ∧
        KasaiRegs I y ∧
        y.regs regi = x.regs regi ∧
        y.regs regr = x.regs regr ∧
        y.regs regh = x.regs regh +
          List.lcpLen (I.text.drop (x.regs regj + x.regs regh))
            (I.text.drop (x.regs regi + x.regs regh)) ∧
        T ≤ 14 * List.lcpLen (I.text.drop (x.regs regj + x.regs regh))
          (I.text.drop (x.regs regi + x.regs regh)) + 17 ∧
        y.mem = x.mem := by
  set n := I.text.length
  intro rem
  induction rem with
  | zero =>
    intro x hrem hrx hgo _
    have hc_go : (Cond.lt zero go).Holds x := by
      rw [Cond.holds_lt, hrx.zero_eq, hgo]
      exact Nat.zero_lt_one
    have hlcp0 : List.lcpLen (I.text.drop (x.regs regj + x.regs regh))
        (I.text.drop (x.regs regi + x.regs regh)) = 0 := by
      have := List.lcpLen_le_length_right (I.text.drop (x.regs regj + x.regs regh))
        (I.text.drop (x.regs regi + x.regs regh))
      simp only [List.length_drop] at this
      omega
    have hf_ni : Fits w (n - x.regs regi) := hw.of_le (by omega)
    have hstep : ∃ u, ExecWithin w kasaiExtBody x u 4 ∧
        u.regs go = 0 ∧ u.regs regh = x.regs regh ∧ u.mem = x.mem := by
      refine WP.exists_execWithin ?_
      unfold kasaiExtBody
      wram_exec [hrx.tl_eq, hrx.zero_eq, hf_ni]
      refine ⟨?_, ?_, rfl⟩
      · wram_simp
      · wram_simp
    obtain ⟨u, hbody, hugo, huh, humem⟩ := hstep
    exact kasaiExt_stop hc_go hbody (by omega) (hrx.kasai_exec hbody) hugo
      (hbody.regs_eq (by decide)) huh (hbody.regs_eq (by decide)) humem hlcp0
  | succ rem ih =>
    intro x hrem hrx hgo htxt
    have hc_go : (Cond.lt zero go).Holds x := by
      rw [Cond.holds_lt, hrx.zero_eq, hgo]
      exact Nat.zero_lt_one
    set i := x.regs regi
    set h := x.regs regh
    set j := x.regs regj
    have hih : i + h < n := by omega
    have hf_ni : Fits w (n - i) := hw.of_le (by omega)
    have hf_nh : Fits w (n - h) := hw.of_le (by omega)
    by_cases hjlt : j < n - h
    · have hjh : j + h < n := by omega
      have hread_j : x.mem (3 + (j + h)) = I.text[j + h] := htxt.get (j + h) hjh
      have hread_i : x.mem (3 + (i + h)) = I.text[i + h] := htxt.get (i + h) hih
      have hf_jh : Fits w (j + h) := hw.of_le (by omega)
      have hf_3jh : Fits w (3 + (j + h)) := hw.of_le (by omega)
      have hf_ih : Fits w (i + h) := hw.of_le (by omega)
      have hf_3ih : Fits w (3 + (i + h)) := hw.of_le (by omega)
      by_cases heq : I.text[j + h] = I.text[i + h]
      · have hf_h1 : Fits w (h + 1) := hw.of_le (by omega)
        have hstep : ∃ u, ExecWithin w kasaiExtBody x u 12 ∧
            u.regs regh = h + 1 ∧ u.regs go = 1 ∧ u.mem = x.mem := by
          refine WP.exists_execWithin ?_
          unfold kasaiExtBody kasaiExtLoads
          wram_exec [hrx.tl_eq, hrx.tb_eq, hrx.one_eq, hrx.zero_eq, hgo,
            hread_j, hread_i, hf_ni, hf_nh, hf_jh, hf_3jh, hf_ih, hf_3ih, hf_h1]
          refine ⟨?_, ?_, rfl⟩
          · wram_simp [h]
          · wram_simp [hgo]
        obtain ⟨u, hbody, huh, hugo, humem⟩ := hstep
        have hui : u.regs regi = i := hbody.regs_eq (by decide)
        have huj : u.regs regj = j := hbody.regs_eq (by decide)
        have hur : u.regs regr = x.regs regr := hbody.regs_eq (by decide)
        obtain ⟨y, T_rec, hrec, hry, hy_i, hy_r, hy_h, hT_rec, hy_mem⟩ :=
          ih u (by rw [hui, huh]; omega) (hrx.kasai_exec hbody) hugo (humem ▸ htxt)
        rw [hui] at hy_i hy_h hT_rec
        rw [hur] at hy_r
        rw [huh, huj] at hy_h hT_rec
        have hlcp_step : List.lcpLen (I.text.drop (j + h)) (I.text.drop (i + h)) =
            1 + List.lcpLen (I.text.drop (j + (h + 1))) (I.text.drop (i + (h + 1))) := by
          rw [List.drop_eq_getElem_cons hjh, List.drop_eq_getElem_cons hih, heq,
            List.lcpLen_cons_cons_self, ← Nat.add_assoc j h 1, ← Nat.add_assoc i h 1]
          omega
        refine ⟨y, 12 + T_rec + 2, ExecWithin.loop_iter hc_go hbody hrec, hry, hy_i, hy_r,
          by rw [hlcp_step]; omega,
          by rw [hlcp_step]; omega, hy_mem.trans humem⟩
      · have hstep : ∃ u, ExecWithin w kasaiExtBody x u 13 ∧
            u.regs go = 0 ∧ u.regs regh = h ∧ u.mem = x.mem := by
          refine WP.exists_execWithin ?_
          unfold kasaiExtBody kasaiExtLoads
          wram_exec [hrx.tl_eq, hrx.tb_eq, hrx.zero_eq,
            hread_j, hread_i, hf_ni, hf_nh, hf_jh, hf_3jh, hf_ih, hf_3ih]
          refine ⟨?_, ?_, rfl⟩
          · wram_simp
          · wram_simp [h]
        obtain ⟨u, hbody, hugo, huh, humem⟩ := hstep
        have hlcp0 : List.lcpLen (I.text.drop (j + h)) (I.text.drop (i + h)) = 0 := by
          rw [List.drop_eq_getElem_cons hjh, List.drop_eq_getElem_cons hih,
            List.lcpLen_cons_cons]
          simp only [heq, ↓reduceIte]
        exact kasaiExt_stop hc_go hbody (by omega) (hrx.kasai_exec hbody) hugo
          (hbody.regs_eq (by decide)) huh (hbody.regs_eq (by decide)) humem hlcp0
    · have hstep : ∃ u, ExecWithin w kasaiExtBody x u 6 ∧
          u.regs go = 0 ∧ u.regs regh = h ∧ u.mem = x.mem := by
        refine WP.exists_execWithin ?_
        unfold kasaiExtBody
        wram_exec [hrx.tl_eq, hrx.zero_eq, hf_ni, hf_nh]
        refine ⟨?_, ?_, rfl⟩
        · wram_simp
        · wram_simp [h]
      obtain ⟨u, hbody, hugo, huh, humem⟩ := hstep
      have hlcp0 : List.lcpLen (I.text.drop (j + h)) (I.text.drop (i + h)) = 0 := by
        have := List.lcpLen_le_length_left (I.text.drop (j + h)) (I.text.drop (i + h))
        simp only [List.length_drop] at this
        omega
      exact kasaiExt_stop hc_go hbody (by omega) (hrx.kasai_exec hbody) hugo
        (hbody.regs_eq (by decide)) huh (hbody.regs_eq (by decide)) humem hlcp0

private theorem getElem!_rankArray_le (n : ℕ) (sa : List ℕ) {i : ℕ} (hi : i < n) :
    (rankArray n sa)[i]! ≤ sa.length := by
  induction sa using List.reverseRecOn with
  | nil =>
    rw [rankArray_nil, getElem!_pos _ i (by rw [Array.size_replicate]; exact hi),
      Array.getElem_replicate]
    exact Nat.zero_le _
  | append_singleton l pos ih =>
    rw [rankArray_append_singleton, List.length_append, List.length_singleton,
      Array.set!_eq_setIfInBounds,
      getElem!_pos _ i (by rw [Array.size_setIfInBounds, size_rankArray]; exact hi)]
    by_cases hp : pos = i
    · subst hp; rw [Array.getElem_setIfInBounds_self]; omega
    · rw [Array.getElem_setIfInBounds_ne (by rw [size_rankArray]; exact hi) hp,
        ← getElem!_pos (rankArray n l) i (by rw [size_rankArray]; exact hi)]
      omega

private structure KasaiLoopInv (I : KasaiInput) (x : Data 20) : Prop where
  regs : KasaiRegs I x
  i_le : x.regs regi ≤ I.text.length
  h_le : x.regs regh ≤ I.text.length
  out_hdr : x.mem (3 + 2 * I.text.length + I.sa.length) = I.text.length
  txt_holds : Block.HoldsList 3 I.text x.mem
  sa_holds : Block.HoldsList (3 + I.text.length) I.sa x.mem
  rk_holds : Block.HoldsList (3 + I.text.length + I.sa.length)
    (rankArray I.text.length I.sa).toList x.mem
  lcp_witness : ∃ lcp : Array ℕ, lcp.size = I.text.length ∧
    Block.HoldsList (4 + 2 * I.text.length + I.sa.length) lcp.toList x.mem ∧
    (kasaiLoop I.text.toArray I.sa.toArray (rankArray I.text.length I.sa)
      (x.regs regi) (x.regs regh) lcp).toList = kasai I.text I.sa

private def kasaiPotential (I : KasaiInput) (x : Data 20) : ℕ :=
  47 * (I.text.length - x.regs regi) -
    14 * min (x.regs regh) (I.text.length - x.regs regi)

private theorem kasaiBody_spec (I : KasaiInput) {w : ℕ}
    (hw : Fits w (3 * I.text.length + I.sa.length + 4))
    (x : Data 20) (hx : KasaiLoopInv I x) (hc : (Cond.lt regi textLen).Holds x) :
    ∃ y T, ExecWithin w kasaiBody x y T ∧ KasaiLoopInv I y ∧
      T + 2 + kasaiPotential I y ≤ kasaiPotential I x := by
  simp only [Cond.holds_lt, hx.regs.tl_eq] at hc
  let n := I.text.length
  let m := I.sa.length
  set i := x.regs regi
  set h := x.regs regh
  have hh_le_n : h ≤ n := hx.h_le
  set rk := rankArray n I.sa
  obtain ⟨lcp, hlcp_sz, hlcp_holds, hlcp_eq⟩ := hx.lcp_witness
  have hrk_i_mem : x.mem (3 + n + m + i) = rk[i]! := by
    have hsz : i < rk.size := by rw [size_rankArray]; exact hc
    have h1 := hx.rk_holds.get i (by simpa [size_rankArray] using hc)
    rw [Array.getElem_toList, ← getElem!_pos rk i hsz] at h1
    exact h1
  have hf_rk_i : Fits w (3 + n + m + i) := hw.of_le (by omega)
  have hf_i1 : Fits w (i + 1) := hw.of_le (by omega)
  by_cases hr0 : rk[i]! = 0
  · have hstep : ∃ y, ExecWithin w kasaiBody x y 4 ∧
        y.regs regi = i + 1 ∧ y.regs regh = h ∧ y.mem = x.mem := by
      refine WP.exists_execWithin ?_
      unfold kasaiBody
      wram_exec [hx.regs.rkb_eq, hx.regs.zero_eq, hx.regs.one_eq, hrk_i_mem, hf_rk_i, hf_i1]
      refine ⟨?_, ?_, rfl⟩
      · wram_simp [i]
      · wram_simp [h]
    obtain ⟨y, e_pos, hy_i, hy_h, hy_mem⟩ := hstep
    refine ⟨y, 4, e_pos,
      ⟨hx.regs.kasai_exec e_pos, by rw [hy_i]; omega, hy_h.symm ▸ hh_le_n,
       hy_mem ▸ hx.out_hdr, hy_mem ▸ hx.txt_holds, hy_mem ▸ hx.sa_holds, hy_mem ▸ hx.rk_holds,
       ⟨lcp, hlcp_sz, hy_mem ▸ hlcp_holds, ?_⟩⟩, ?_⟩
    · rw [hy_i, hy_h, ← kasaiLoop_of_rk_zero I.text.toArray I.sa.toArray rk
        (by simpa only [List.size_toArray] using hc) hr0 h lcp]
      exact hlcp_eq
    · unfold kasaiPotential
      rw [hy_i, hy_h]
      clear hlcp_eq hlcp_holds hrk_i_mem
      omega
  · have hrk_le_m : rk[i]! ≤ m := getElem!_rankArray_le n I.sa hc
    have hf_rm1 : Fits w (rk[i]! - 1) := hw.of_le (by omega)
    set u₁ := x.set t0 (3 + n + m + i)
    set u₂ := u₁.set regr rk[i]!
    have b₁ : ExecWithin w (.op (.bin .add t0 rkBase regi)) x u₁ 1 :=
      WP.execWithin <| by
        wram_exec [hx.regs.rkb_eq, hf_rk_i]
        rfl
    have b₂ : ExecWithin (B := .standard) w (.op (.load regr t0)) u₁ u₂ 1 :=
      WP.execWithin <| by
        wram_exec [u₁, hrk_i_mem]
        rfl
    have hc_r0 : ¬(Cond.eq regr zero).Holds u₂ := by
      simp only [Cond.holds_eq, u₂, u₁, Data.set_regs_self,
        Data.set_regs_of_ne (by decide : zero ≠ regr),
        Data.set_regs_of_ne (by decide : zero ≠ t0), hx.regs.zero_eq]
      exact hr0
    set u₃ := u₂.set t0 (rk[i]! - 1)
    have b₃ : ExecWithin w (.op (.bin .sub t0 regr one)) u₂ u₃ 1 :=
      WP.execWithin <| by
        wram_exec [u₂, u₁, hx.regs.one_eq, hf_rm1]
        rfl
    have hru₃ : KasaiRegs I u₃ := ((hx.regs.kasai_exec b₁).kasai_exec b₂).kasai_exec b₃
    have hu₃_t0 : u₃.regs t0 = rk[i]! - 1 := Data.set_regs_self u₂ t0 _
    have hu₃_i : u₃.regs regi = i :=
      (b₃.regs_eq (by decide)).trans ((b₂.regs_eq (by decide)).trans (b₁.regs_eq (by decide)))
    have hu₃_h : u₃.regs regh = h :=
      (b₃.regs_eq (by decide)).trans ((b₂.regs_eq (by decide)).trans (b₁.regs_eq (by decide)))
    have hu₃_r : u₃.regs regr = rk[i]! :=
      (b₃.regs_eq (by decide)).trans (Data.set_regs_self _ regr _)
    set j_val := I.sa.toArray[rk[i]! - 1]!
    have hj_load : ∃ u₄, ExecWithin w
        (ram[ if t0 < saLen then [ t1 ← saBase + t0; regj ← *t1 ] else [ regj ← zero ] ])
        u₃ u₄ 3 ∧
        u₄.regs regj = j_val ∧ u₄.mem = x.mem := by
      by_cases hrm : rk[i]! - 1 < m
      · have hf_sa_rm : Fits w (3 + I.text.length + (rk[i]! - 1)) := hw.of_le (by omega)
        have hmem_sa : u₃.mem (3 + I.text.length + (rk[i]! - 1)) = j_val := by
          change x.mem (3 + I.text.length + (rk[i]! - 1)) = I.sa.toArray[rk[i]! - 1]!
          rw [hx.sa_holds.get (rk[i]! - 1) hrm,
            getElem!_pos I.sa.toArray (rk[i]! - 1) (by simpa using hrm), List.getElem_toArray]
        refine WP.exists_execWithin ?_
        wram_exec [hu₃_t0, hru₃.sl_eq, hru₃.sb_eq, hru₃.zero_eq, hmem_sa, hf_sa_rm]
        exact ⟨by wram_simp, rfl⟩
      · have hc_rm : ¬(Cond.lt t0 saLen).Holds u₃ := by
          simp only [Cond.holds_lt, hu₃_t0, hru₃.sl_eq]
          exact hrm
        have hj0 : j_val = 0 := getElem!_neg I.sa.toArray (rk[i]! - 1) (by simpa using hrm)
        have d₁ : ExecWithin (B := .standard) w (.op (.copy regj zero)) u₃ (u₃.set regj 0) 1 :=
          WP.execWithin <| by
            wram_exec [hru₃.zero_eq]
            rfl
        exact ⟨u₃.set regj 0, ExecWithin.branch_neg hc_rm d₁,
          (Data.set_regs_self u₃ regj 0).trans hj0.symm, rfl⟩
    obtain ⟨u₄, ej_load, hu₄_j, hu₄_mem⟩ := hj_load
    have hru₄ : KasaiRegs I u₄ := hru₃.kasai_exec ej_load
    set u₅ := u₄.set go 1
    have b₅ : ExecWithin (B := .standard) w (.op (.copy go one)) u₄ u₅ 1 :=
      WP.execWithin <| by
        wram_exec [hru₄.one_eq]
        rfl
    have hru₅ : KasaiRegs I u₅ := hru₄.set_scratch go 1
    have hu₅_i : u₅.regs regi = i :=
      (b₅.regs_eq (by decide)).trans ((ej_load.regs_eq (by decide)).trans hu₃_i)
    have hu₅_h : u₅.regs regh = h :=
      (b₅.regs_eq (by decide)).trans ((ej_load.regs_eq (by decide)).trans hu₃_h)
    have hu₅_j : u₅.regs regj = j_val := (b₅.regs_eq (by decide)).trans hu₄_j
    have hu₅_r : u₅.regs regr = rk[i]! :=
      (b₅.regs_eq (by decide)).trans ((ej_load.regs_eq (by decide)).trans hu₃_r)
    obtain ⟨u₆, T_ext, e_ext, hru₆, hu₆_i, hu₆_r, hu₆_h, hT_ext, hu₆_mem⟩ :=
      kasaiExt_spec I hw (n - (u₅.regs regi + u₅.regs regh)) u₅ rfl hru₅
        (Data.set_regs_self u₄ go 1) (hu₄_mem ▸ hx.txt_holds)
    rw [hu₅_i, hu₅_h, hu₅_j] at hu₆_h hT_ext
    rw [hu₅_i] at hu₆_i
    rw [hu₅_r] at hu₆_r
    set k := List.lcpLen (I.text.drop (j_val + h)) (I.text.drop (i + h))
    set h' := h + k
    have hk_bound : 0 < k → h + k ≤ n - i := by
      intro hk_pos
      have hk_len := List.lcpLen_le_length_right (I.text.drop (j_val + h)) (I.text.drop (i + h))
      simp only [List.length_drop] at hk_len
      change 0 < List.lcpLen (I.text.drop (j_val + h)) (I.text.drop (i + h)) at hk_pos
      omega
    have hlcp_store : ∃ u₇, ExecWithin w
        (ram[ if regr < textLen then [ t0 ← lcpBase + regr; *t0 ← regh ] else [ t0 ← zero ] ])
        u₆ u₇ 3 ∧
        u₇.mem (3 + 2 * n + m) = n ∧
        Block.HoldsList 3 I.text u₇.mem ∧
        Block.HoldsList (3 + n) I.sa u₇.mem ∧
        Block.HoldsList (3 + n + m) rk.toList u₇.mem ∧
        Block.HoldsList (4 + 2 * n + m) (lcp.set! rk[i]! h').toList u₇.mem := by
      let storeBr : Code .standard 20 :=
        .branch (.lt regr textLen)
          (.seq (.op (.bin .add t0 lcpBase regr)) (.op (.store t0 regh)))
          (.op (.copy t0 zero))
      have hm_eq : u₆.mem = x.mem := hu₆_mem.trans hu₄_mem
      by_cases hrlt : rk[i]! < n
      · have hf_lcp_r : Fits w (4 + 2 * I.text.length + I.sa.length + rk[i]!) := hw.of_le (by omega)
        have hstep : ∃ u₇, ExecWithin w storeBr u₆ u₇ 3 ∧
            u₇.mem = Function.update x.mem (4 + 2 * n + m + rk[i]!) h' := by
          refine WP.exists_execWithin ?_
          wram_exec [storeBr, hu₆_r, hru₆.tl_eq, hru₆.lcpb_eq, hu₆_h, hru₆.zero_eq, hf_lcp_r]
          dsimp only [n, m, h']
          simp only [Data.write_mem, Data.set_mem, hm_eq]
        obtain ⟨u₇, eu₇, hu₇_mem⟩ := hstep
        have hfr (a : ℕ) (ha : a ≤ 3 + 2 * n + m) : u₇.mem a = x.mem a := by
          rw [hu₇_mem, Function.update_of_ne (by omega)]
        refine ⟨u₇, eu₇, (hfr _ le_rfl).trans hx.out_hdr,
          hx.txt_holds.frame (fun a _ ha2 => hfr a (by omega)),
          hx.sa_holds.frame (fun a _ ha2 => hfr a (by omega)),
          hx.rk_holds.frame (fun a _ ha2 => by
            rw [Array.length_toList, size_rankArray] at ha2
            exact hfr a (by omega)),
          hu₇_mem ▸ holdsList_set!_lt hlcp_holds (by omega) h'⟩
      · have hstep : ∃ u₇, ExecWithin w storeBr u₆ u₇ 3 ∧ u₇.mem = x.mem := by
          refine WP.exists_execWithin ?_
          wram_exec [storeBr, hu₆_r, hru₆.tl_eq, hru₆.zero_eq]
          exact hm_eq
        obtain ⟨u₇, eu₇, hu₇_mem⟩ := hstep
        exact ⟨u₇, eu₇, hu₇_mem ▸ hx.out_hdr, hu₇_mem ▸ hx.txt_holds, hu₇_mem ▸ hx.sa_holds,
          hu₇_mem ▸ hx.rk_holds, hu₇_mem ▸ holdsList_set!_ge hlcp_holds (by omega) h'⟩
    obtain ⟨u₇, elcp_st, hout₇, htxt₇, hsa₇, hrk₇, hlcp₇⟩ := hlcp_store
    have hru₇ : KasaiRegs I u₇ := hru₆.kasai_exec elcp_st
    have hu₇_i : u₇.regs regi = i := (elcp_st.regs_eq (by decide)).trans hu₆_i
    have hu₇_h : u₇.regs regh = h' := (elcp_st.regs_eq (by decide)).trans hu₆_h
    have hf_hm1 : Fits w (h' - 1) := hw.of_le (by omega)
    set y := (u₇.set regh (h' - 1)).set regi (i + 1)
    have b_tail : ExecWithin w
        (.seq (.op (.bin .sub regh regh one)) (.op (.bin .add regi regi one))) u₇ y 2 :=
      WP.execWithin <| by
        wram_exec [hu₇_h, hu₇_i, hru₇.one_eq, hf_hm1, hf_i1]
        rfl
    have hy_i : y.regs regi = i + 1 := Data.set_regs_self _ regi _
    have hy_h : y.regs regh = h' - 1 :=
      (Data.set_regs_of_ne (by decide) _).trans (Data.set_regs_self u₇ regh _)
    have e_neg := b₃.seq (ej_load.seq (b₅.seq (e_ext.seq (elcp_st.seq b_tail))))
    have e_full : ExecWithin w kasaiBody x y (14 * k + 31) := by
      unfold kasaiBody
      exact (b₁.seq (b₂.seq (ExecWithin.branch_neg hc_r0 e_neg))).mono (by omega)
    refine ⟨y, 14 * k + 31, e_full, ?_, ?_⟩
    · refine ⟨hru₇.kasai_exec b_tail, by rw [hy_i]; omega,
        by
          rw [hy_h]
          dsimp only [h']
          rcases Nat.eq_zero_or_pos k with hk0 | hkpos
          · omega
          · have := hk_bound hkpos
            omega,
        hout₇, htxt₇, hsa₇, hrk₇,
        ⟨lcp.set! rk[i]! h',
         by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hlcp_sz,
         hlcp₇, ?_⟩⟩
      rw [hy_i, hy_h]
      have hstep := congrArg Array.toList
        (kasaiLoop_of_rk_ne_zero I.text.toArray I.sa.toArray rk
          (by simpa only [List.size_toArray] using hc) hr0 h lcp)
      exact hstep.symm.trans hlcp_eq
    · unfold kasaiPotential
      rw [hy_i, hy_h]
      clear hlcp_eq hlcp_holds hrk_i_mem hlcp₇ hout₇ htxt₇ hsa₇ hrk₇ e_full e_neg
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · have heq_h' : h' = h := by change h + k = h; omega
        rw [heq_h']
        omega
      · have hle_ni : h + k ≤ n - i := hk_bound hkpos
        have heq_h' : h' = h + k := rfl
        rw [heq_h']
        omega

/-- `kasaiCode` executes within `55 * |I.text| + 8 * |I.sa| + 25` instructions from
`Data.init I.encode` whenever `Fits w (3 * |I.text| + |I.sa| + 4)`, writing `kasai I.text I.sa`
as a length-prefixed array at `y.regs Reg.out = 3 + 2 * |I.text| + |I.sa|` and preserving both
`I.text` and `I.sa`. -/
theorem kasaiCode_exec (I : KasaiInput) {w : ℕ}
    (hw : Fits w (3 * I.text.length + I.sa.length + 4)) :
    ∃ y, ExecWithin w kasaiCode (Data.init I.encode) y
        (55 * I.text.length + 8 * I.sa.length + 25) ∧
      outputList y.mem (y.regs out) = kasai I.text I.sa ∧
      y.regs out = 3 + 2 * I.text.length + I.sa.length ∧
      Fits w (y.regs out + (kasai I.text I.sa).length) ∧
      Block.HoldsList 3 I.text y.mem ∧
      Block.HoldsList (3 + I.text.length) I.sa y.mem := by
  obtain ⟨x₁, ez, hrx₁, hout₁, htxt₁, hsa₁, hrk₁, hlcp₁⟩ := kasaiSetupAndZero_spec I hw
  obtain ⟨x₂, esc, hrx₂, hout₂, htxt₂, hsa₂, hrk₂, hlcp₂⟩ :=
    scatterCode_spec I hw x₁ hrx₁ hout₁ htxt₁ hsa₁ hrk₁ hlcp₁
  set s₀ := (x₂.set regi 0).set regh 0
  have e_init : ExecWithin (B := .standard) w (ram[ regi ← zero; regh ← zero ]) x₂ s₀ 2 := by
    refine WP.execWithin ?_
    wram_exec [hrx₂.zero_eq]
    rfl
  have hs₀_i : s₀.regs regi = 0 :=
    (Data.set_regs_of_ne (by decide) 0).trans (Data.set_regs_self x₂ regi 0)
  have hs₀_h : s₀.regs regh = 0 := Data.set_regs_self _ regh 0
  have hs₀_inv : KasaiLoopInv I s₀ :=
    ⟨hrx₂.kasai_exec e_init,
     by rw [hs₀_i]; exact Nat.zero_le _,
     by rw [hs₀_h]; exact Nat.zero_le _,
     hout₂, htxt₂, hsa₂, hrk₂,
     ⟨Array.replicate I.text.length 0, Array.size_replicate,
      by
        change Block.HoldsList (4 + 2 * I.text.length + I.sa.length)
          (Array.replicate I.text.length 0).toList x₂.mem
        simpa only [Array.toList_replicate] using hlcp₂,
      by rw [hs₀_i, hs₀_h]; rfl⟩⟩
  obtain ⟨y, eloop, hy_inv, hnc⟩ := ExecWithin.loop_potential (w := w)
    (cond := .lt regi textLen) (body := kasaiBody)
    (KasaiLoopInv I) (kasaiPotential I) (kasaiBody_spec I hw) hs₀_inv
  simp only [Cond.holds_lt, hy_inv.regs.tl_eq, not_lt] at hnc
  have hy_i : y.regs regi = I.text.length := le_antisymm hy_inv.i_le hnc
  have hpot₀ : kasaiPotential I s₀ = 47 * I.text.length := by
    simp only [kasaiPotential, hs₀_i, hs₀_h, Nat.sub_zero, Nat.zero_min, Nat.mul_zero]
  rw [hpot₀] at eloop
  obtain ⟨lcp_fin, _, hlcp_fin_holds, hlcp_fin_eq⟩ := hy_inv.lcp_witness
  rw [kasaiLoop_of_le _ _ _ (by simpa only [List.size_toArray, hy_i] using le_rfl)] at hlcp_fin_eq
  rw [hlcp_fin_eq] at hlcp_fin_holds
  have hout_list : outputList y.mem (y.regs out) = kasai I.text I.sa := by
    have hlcp_addr :
        3 + 2 * I.text.length + I.sa.length + 1 = 4 + 2 * I.text.length + I.sa.length := by
      omega
    rw [outputList_eq_iff, hy_inv.regs.out_eq, length_kasai]
    exact ⟨hy_inv.out_hdr, by simpa only [hlcp_addr] using hlcp_fin_holds⟩
  have hfit_out : Fits w (y.regs out + (kasai I.text I.sa).length) := by
    rw [hy_inv.regs.out_eq, length_kasai]
    exact hw.of_le (by omega)
  have emain : ExecWithin w kasaiMainCode x₂ y (47 * I.text.length + 4) := by
    unfold kasaiMainCode
    exact (e_init.seq eloop).mono (by omega)
  unfold kasaiCode
  exact ⟨y, (ez.seq (esc.seq emain)).mono (by omega),
    hout_list, hy_inv.regs.out_eq, hfit_out, hy_inv.txt_holds, hy_inv.sa_holds⟩

/-- `kasaiProgram` computes `kasai I.text I.sa` in `55 * |I.text| + 8 * |I.sa| + 26` instructions
on every `KasaiInput` at every word width `w` with `Fits w (3 * |I.text| + |I.sa| + 4)`. -/
theorem kasaiProgram_computesListInTime :
    kasaiProgram.ComputesListInTime (fun _ (I : KasaiInput) => I.encode)
      (fun I _ => 55 * I.text.length + 8 * I.sa.length + 26)
      (fun I w => Fits w (3 * I.text.length + I.sa.length + 4))
      (fun I => kasai I.text I.sa) :=
  kasaiCode.computesListInTime_program out fun I _ hw _ => by
    obtain ⟨y, hexec, hout, _, hfit, _, _⟩ := kasaiCode_exec I hw
    exact ⟨y, hexec, hout, hfit⟩

/-- **Linear-time Word-RAM Kasai LCP theorem.** On valid suffix-array inputs (`IsSuffixArray`),
`kasaiProgram` computes `lcpArray I.text I.sa` within `63 * |I.text| + 26` instructions at every
word width `w` with `Fits w (4 * |I.text| + 4)`. -/
theorem kasaiProgram_computesLcpArrayInTime :
    kasaiProgram.ComputesListInTime
      (fun _ (I : {I : KasaiInput // IsSuffixArray I.text I.sa}) => I.val.encode)
      (fun I _ => 63 * I.val.text.length + 26)
      (fun I w => Fits w (4 * I.val.text.length + 4))
      (fun I => lcpArray I.val.text I.val.sa) := by
  rintro ⟨I, hsa⟩ w hw hfits
  dsimp only at hw hfits ⊢
  have hlen := hsa.length_eq
  have hw' : Fits w (3 * I.text.length + I.sa.length + 4) := hw.of_le (by omega)
  obtain ⟨t, hexec, ht⟩ := kasaiProgram_computesListInTime I w hw' hfits
  dsimp only at hexec ht
  rw [kasai_eq_lcpArray hsa] at hexec
  exact ⟨t, hexec, by omega⟩

/-! ## Part 2: `O(|p| log |sa|)` Suffix-Array Pattern Search -/

private def encodeOrd : Ordering → ℕ
  | .lt => 0
  | .eq => 1
  | .gt => 2

private def searchSetup : Code .standard 20 := ram[
  zero ← #0;
  one ← #1;
  twoReg ← #2;
  t0 ← #3;
  textBase ← #4;
  textLen ← *one;
  saLen ← *twoReg;
  patLen ← *t0;
  saBase ← textBase + textLen;
  patBase ← saBase + saLen;
  out ← patBase + patLen;
  loReg ← zero;
  hiReg ← saLen ]

private def cmpLoads : Code .standard 20 := ram[
  t0 ← patBase + regk;
  t0 ← *t0;
  t1 ← posReg + regk;
  t1 ← textBase + t1;
  t1 ← *t1 ]

private def cmpBody : Code .standard 20 := ram[
  if regk < patLen then [
    if regk < textLen then [
      t0 ← textLen - regk;
      if posReg < t0 then [
        ⟪cmpLoads⟫;
        if t0 < t1 then [
          resReg ← zero;
          go ← zero
        ] else [
          if t1 < t0 then [
            resReg ← twoReg;
            go ← zero
          ] else [
            regk ← regk + one
          ]
        ]
      ] else [
        resReg ← twoReg;
        go ← zero
      ]
    ] else [
      resReg ← twoReg;
      go ← zero
    ]
  ] else [
    go ← zero
  ] ]

private def cmpPrep : Code .standard 20 := ram[
  t0 ← saBase + midReg;
  posReg ← *t0;
  regk ← zero;
  resReg ← one;
  go ← one ]

private def cmpSuffixCode : Code .standard 20 :=
  .seq cmpPrep (.loop (.lt zero go) cmpBody)

private def probeBelowCode : Code .standard 20 :=
  .seq cmpSuffixCode (ram[ resReg ← resReg - one ])

private def probeAtMostCode : Code .standard 20 :=
  cmpSuffixCode

private def twoBisectionsCode : Code .standard 20 := ram[
  ⟪bisectCode loReg hiReg midReg resReg zero one probeBelowCode⟫;
  savedLo ← loReg;
  loReg ← zero;
  hiReg ← saLen;
  ⟪bisectCode loReg hiReg midReg resReg zero one probeAtMostCode⟫ ]

private def rangeSearchFinish : Code .standard 20 := ram[
  *out ← twoReg;
  t0 ← out + one;
  *t0 ← savedLo;
  t0 ← out + twoReg;
  *t0 ← loReg ]

private def occCopyBody : Code .standard 20 := ram[
  t0 ← savedLo + regk;
  t0 ← saBase + t0;
  t0 ← *t0;
  t1 ← out + one;
  t1 ← t1 + regk;
  *t1 ← t0;
  regk ← regk + one ]

private def occCopyInit : Code .standard 20 := ram[
  hiReg ← loReg - savedLo;
  *out ← hiReg;
  regk ← zero ]

private def occurrencesFinish : Code .standard 20 := ram[
  if savedLo < loReg then [
    ⟪occCopyInit⟫;
    ⟪.loop (.lt regk hiReg) occCopyBody⟫
  ] else [
    *out ← zero
  ] ]

/-- Structured 20-register Word-RAM program computing the rank interval
`[(search I.text I.sa I.pat).1, (search I.text I.sa I.pat).2]` at `Reg.out`. -/
def rangeSearchCode : Code .standard 20 :=
  .seq (.seq searchSetup twoBisectionsCode) rangeSearchFinish

/-- Uniform `Basis.standard` Word-RAM program for `O(|pat| log |sa|)` suffix-array rank-interval
search. -/
def rangeSearchProgram : Program .standard 20 := rangeSearchCode.program out

/-- Structured 20-register Word-RAM program computing `occurrences I.text I.sa I.pat` at
`Reg.out`. -/
def occurrencesCode : Code .standard 20 :=
  .seq (.seq searchSetup twoBisectionsCode) occurrencesFinish

/-- Uniform `Basis.standard` Word-RAM program for suffix-array occurrence search. -/
def occurrencesProgram : Program .standard 20 := occurrencesCode.program out

private structure SearchRegs (I : SearchInput) (x : Data 20) : Prop where
  zero_eq : x.regs zero = 0
  one_eq : x.regs one = 1
  two_eq : x.regs twoReg = 2
  tb_eq : x.regs textBase = 4
  tl_eq : x.regs textLen = I.text.length
  sb_eq : x.regs saBase = 4 + I.text.length
  sl_eq : x.regs saLen = I.sa.length
  pb_eq : x.regs patBase = 4 + I.text.length + I.sa.length
  pl_eq : x.regs patLen = I.pat.length
  out_eq : x.regs out = 4 + I.text.length + I.sa.length + I.pat.length
  txt_holds : Block.HoldsList 4 I.text x.mem
  sa_holds : Block.HoldsList (4 + I.text.length) I.sa x.mem
  pat_holds : Block.HoldsList (4 + I.text.length + I.sa.length) I.pat x.mem

private theorem SearchRegs.set_scratch {I : SearchInput} {x : Data 20} (hr : SearchRegs I x)
    (d : Fin 20) (v : ℕ)
    (h0 : zero ≠ d := by decide) (h1 : one ≠ d := by decide) (h2 : twoReg ≠ d := by decide)
    (htb : textBase ≠ d := by decide) (htl : textLen ≠ d := by decide)
    (hsb : saBase ≠ d := by decide) (hsl : saLen ≠ d := by decide)
    (hpb : patBase ≠ d := by decide) (hpl : patLen ≠ d := by decide)
    (ho : out ≠ d := by decide) : SearchRegs I (x.set d v) :=
  ⟨(Data.set_regs_of_ne h0 v).trans hr.zero_eq,
   (Data.set_regs_of_ne h1 v).trans hr.one_eq,
   (Data.set_regs_of_ne h2 v).trans hr.two_eq,
   (Data.set_regs_of_ne htb v).trans hr.tb_eq,
   (Data.set_regs_of_ne htl v).trans hr.tl_eq,
   (Data.set_regs_of_ne hsb v).trans hr.sb_eq,
   (Data.set_regs_of_ne hsl v).trans hr.sl_eq,
   (Data.set_regs_of_ne hpb v).trans hr.pb_eq,
   (Data.set_regs_of_ne hpl v).trans hr.pl_eq,
   (Data.set_regs_of_ne ho v).trans hr.out_eq,
   hr.txt_holds, hr.sa_holds, hr.pat_holds⟩

private theorem SearchRegs.search_exec {I : SearchInput} {c : Code .standard 20}
    {x y : Data 20} {w T : ℕ} (hr : SearchRegs I x) (he : ExecWithin w c x y T)
    (hm : ∀ a < 4 + I.text.length + I.sa.length + I.pat.length, y.mem a = x.mem a)
    (h0 : c.Preserves zero := by decide) (h1 : c.Preserves one := by decide)
    (h2 : c.Preserves twoReg := by decide) (htb : c.Preserves textBase := by decide)
    (htl : c.Preserves textLen := by decide) (hsb : c.Preserves saBase := by decide)
    (hsl : c.Preserves saLen := by decide) (hpb : c.Preserves patBase := by decide)
    (hpl : c.Preserves patLen := by decide) (ho : c.Preserves out := by decide) :
    SearchRegs I y :=
  ⟨(he.regs_eq h0).trans hr.zero_eq, (he.regs_eq h1).trans hr.one_eq,
   (he.regs_eq h2).trans hr.two_eq, (he.regs_eq htb).trans hr.tb_eq,
   (he.regs_eq htl).trans hr.tl_eq, (he.regs_eq hsb).trans hr.sb_eq,
   (he.regs_eq hsl).trans hr.sl_eq, (he.regs_eq hpb).trans hr.pb_eq,
   (he.regs_eq hpl).trans hr.pl_eq, (he.regs_eq ho).trans hr.out_eq,
   hr.txt_holds.frame (fun a _ ha2 => hm a (by omega)),
   hr.sa_holds.frame (fun a _ ha2 => hm a (by omega)),
   hr.pat_holds.frame (fun a _ ha2 => hm a (by omega))⟩

private theorem init_searchEncode (I : SearchInput) :
    let x : Data 20 := Data.init I.encode
    x.mem 1 = I.text.length ∧ x.mem 2 = I.sa.length ∧ x.mem 3 = I.pat.length ∧
      Block.HoldsList 4 I.text x.mem ∧
      Block.HoldsList (4 + I.text.length) I.sa x.mem ∧
      Block.HoldsList (4 + I.text.length + I.sa.length) I.pat x.mem := by
  intro x
  have hhdr : Block.HoldsList 1 [I.text.length, I.sa.length, I.pat.length] x.mem := by
    simpa only [x, SearchInput.encode, List.length_nil, Nat.zero_add, List.nil_append,
      List.cons_append, List.append_assoc] using
      init_holdsList_append (r := 20) [] [I.text.length, I.sa.length, I.pat.length]
        (I.text ++ (I.sa ++ I.pat))
  obtain ⟨hm1, hhdr2⟩ := Block.holdsList_cons_iff.mp hhdr
  obtain ⟨hm2, hhdr3⟩ := Block.holdsList_cons_iff.mp hhdr2
  obtain ⟨hm3, _⟩ := Block.holdsList_cons_iff.mp hhdr3
  have hsa := init_holdsList_append (r := 20)
    ([I.text.length, I.sa.length, I.pat.length] ++ I.text) I.sa I.pat
  have hpat := init_holdsList_append (r := 20)
    ([I.text.length, I.sa.length, I.pat.length] ++ (I.text ++ I.sa)) I.pat []
  have hlen_sa : ([I.text.length, I.sa.length, I.pat.length] ++ I.text).length + 1 =
      4 + I.text.length := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hlen_pat : ([I.text.length, I.sa.length, I.pat.length] ++ (I.text ++ I.sa)).length + 1 =
      4 + I.text.length + I.sa.length := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  rw [hlen_sa] at hsa
  rw [hlen_pat] at hpat
  refine ⟨hm1, hm2, hm3, ?_, ?_, ?_⟩
  · simpa only [x, SearchInput.encode, List.length_cons, List.length_nil, List.cons_append,
      List.nil_append, List.append_assoc] using
      init_holdsList_append (r := 20) [I.text.length, I.sa.length, I.pat.length]
        I.text (I.sa ++ I.pat)
  · simpa only [x, SearchInput.encode, List.cons_append, List.nil_append, List.append_assoc]
      using hsa
  · simpa only [x, SearchInput.encode, List.append_nil, List.cons_append, List.nil_append,
      List.append_assoc] using hpat

private theorem cmpLoop_stop {I : SearchInput} {w T : ℕ} {x s₁ : Data 20} {ord : Ordering}
    (hc_go : (Cond.lt zero go).Holds x)
    (hbody : ExecWithin w cmpBody x s₁ T)
    (hT : T + 4 ≤ 18)
    (hrs₁ : SearchRegs I s₁)
    (hs₁_go : s₁.regs go = 0)
    (hs₁_lo : s₁.regs loReg = x.regs loReg)
    (hs₁_hi : s₁.regs hiReg = x.regs hiReg)
    (hs₁_mid : s₁.regs midReg = x.regs midReg)
    (hs₁_sv : s₁.regs savedLo = x.regs savedLo)
    (hs₁_res : s₁.regs resReg = encodeOrd ord)
    (hcmp : cmpSuffix I.text.toArray (I.pat.drop (x.regs regk))
      (x.regs posReg + x.regs regk) = ord) :
    ∃ y T', ExecWithin w (.loop (.lt zero go) cmpBody) x y T' ∧
      SearchRegs I y ∧
      y.regs loReg = x.regs loReg ∧
      y.regs hiReg = x.regs hiReg ∧
      y.regs midReg = x.regs midReg ∧
      y.regs savedLo = x.regs savedLo ∧
      y.regs resReg = encodeOrd (cmpSuffix I.text.toArray (I.pat.drop (x.regs regk))
        (x.regs posReg + x.regs regk)) ∧
      T' ≤ 16 * (I.pat.length - x.regs regk) + 18 := by
  have hc_stop : ¬(Cond.lt zero go).Holds s₁ := by
    simp only [Cond.holds_lt, hrs₁.zero_eq, hs₁_go]; exact Nat.lt_irrefl 0
  exact ⟨s₁, T + 4, ExecWithin.loop_once hc_go hbody hc_stop, hrs₁,
    hs₁_lo, hs₁_hi, hs₁_mid, hs₁_sv, by rw [hcmp, hs₁_res], by omega⟩

private theorem setGtStop_exec {I : SearchInput} {w : ℕ} (u : Data 20) (hru : SearchRegs I u) :
    ExecWithin (B := .standard) w (ram[ resReg ← twoReg; go ← zero ]) u
      ((u.set resReg 2).set go 0) 2 :=
  WP.execWithin <| by
    wram_exec [hru.two_eq, hru.zero_eq]
    rfl

private theorem cmpLoop_gt_stop {I : SearchInput} {w T : ℕ} {x u : Data 20}
    (hc_go : (Cond.lt zero go).Holds x)
    (hbody : ExecWithin w cmpBody x ((u.set resReg 2).set go 0) T)
    (hT : T + 4 ≤ 18)
    (hru : SearchRegs I u)
    (hu_lo : u.regs loReg = x.regs loReg)
    (hu_hi : u.regs hiReg = x.regs hiReg)
    (hu_mid : u.regs midReg = x.regs midReg)
    (hu_sv : u.regs savedLo = x.regs savedLo)
    (hcmp : cmpSuffix I.text.toArray (I.pat.drop (x.regs regk))
      (x.regs posReg + x.regs regk) = .gt) :
    ∃ y T', ExecWithin w (.loop (.lt zero go) cmpBody) x y T' ∧
      SearchRegs I y ∧
      y.regs loReg = x.regs loReg ∧
      y.regs hiReg = x.regs hiReg ∧
      y.regs midReg = x.regs midReg ∧
      y.regs savedLo = x.regs savedLo ∧
      y.regs resReg = encodeOrd (cmpSuffix I.text.toArray (I.pat.drop (x.regs regk))
        (x.regs posReg + x.regs regk)) ∧
      T' ≤ 16 * (I.pat.length - x.regs regk) + 18 :=
  cmpLoop_stop (ord := .gt) hc_go hbody hT ((hru.set_scratch resReg 2).set_scratch go 0)
    (Data.set_regs_self _ go 0)
    (((Data.set_regs_of_ne (by decide) _).trans (Data.set_regs_of_ne (by decide) _)).trans hu_lo)
    (((Data.set_regs_of_ne (by decide) _).trans (Data.set_regs_of_ne (by decide) _)).trans hu_hi)
    (((Data.set_regs_of_ne (by decide) _).trans (Data.set_regs_of_ne (by decide) _)).trans hu_mid)
    (((Data.set_regs_of_ne (by decide) _).trans (Data.set_regs_of_ne (by decide) _)).trans hu_sv)
    ((Data.set_regs_of_ne (by decide) 0).trans (Data.set_regs_self u resReg 2))
    hcmp

private theorem cmpLoop_spec (I : SearchInput) {w : ℕ}
    (hw : Fits w (I.text.length + I.sa.length + I.pat.length + 6)) :
    ∀ (rem : ℕ) (x : Data 20),
      I.pat.length - x.regs regk = rem →
      SearchRegs I x →
      x.regs resReg = 1 →
      x.regs go = 1 →
      ∃ y T, ExecWithin w (.loop (.lt zero go) cmpBody) x y T ∧
        SearchRegs I y ∧
        y.regs loReg = x.regs loReg ∧
        y.regs hiReg = x.regs hiReg ∧
        y.regs midReg = x.regs midReg ∧
        y.regs savedLo = x.regs savedLo ∧
        y.regs resReg = encodeOrd (cmpSuffix I.text.toArray (I.pat.drop (x.regs regk))
          (x.regs posReg + x.regs regk)) ∧
        T ≤ 16 * rem + 18 := by
  let n := I.text.length
  let m := I.sa.length
  let plen := I.pat.length
  intro rem
  induction rem with
  | zero =>
    intro x hrem hrx hres hgo
    have hc_go : (Cond.lt zero go).Holds x := by
      simp only [Cond.holds_lt, hrx.zero_eq, hgo]; exact Nat.zero_lt_one
    have hk_ge : plen ≤ x.regs regk := by omega
    have hc_nk : ¬(Cond.lt regk patLen).Holds x := by
      simp only [Cond.holds_lt, hrx.pl_eq]; omega
    set u₁ := x.set go 0
    have b₁ : ExecWithin (B := .standard) w (.op (.copy go zero)) x u₁ 1 := by
      simpa only [hrx.zero_eq] using
        (ExecWithin.copy (B := .standard) (d := go) (s := zero) (x := x))
    have hbody : ExecWithin w cmpBody x u₁ 3 := by
      unfold cmpBody; exact ExecWithin.branch_neg hc_nk b₁
    have hcmp : cmpSuffix I.text.toArray (I.pat.drop (x.regs regk))
        (x.regs posReg + x.regs regk) = .eq := by
      rw [List.drop_eq_nil_of_le hk_ge, cmpSuffix]
    have h1 := cmpLoop_stop (ord := .eq) hc_go hbody (by omega) (hrx.set_scratch go 0)
      (Data.set_regs_self x go 0)
      (Data.set_regs_of_ne (by decide) 0)
      (Data.set_regs_of_ne (by decide) 0)
      (Data.set_regs_of_ne (by decide) 0)
      (Data.set_regs_of_ne (by decide) 0)
      ((Data.set_regs_of_ne (by decide) 0).trans hres) hcmp
    rwa [hrem] at h1
  | succ rem ih =>
    intro x hrem hrx hres hgo
    have hc_go : (Cond.lt zero go).Holds x := by
      simp only [Cond.holds_lt, hrx.zero_eq, hgo]; exact Nat.zero_lt_one
    set k := x.regs regk
    set pos := x.regs posReg
    have hk_lt : k < plen := by omega
    have hc_k : (Cond.lt regk patLen).Holds x := by
      simp only [Cond.holds_lt, hrx.pl_eq]; exact hk_lt
    by_cases hk_n : k < n
    · have hc_kn : (Cond.lt regk textLen).Holds x := by
        simp only [Cond.holds_lt, hrx.tl_eq]; exact hk_n
      set u₁ := x.set t0 (n - k)
      have b₁ : ExecWithin w (.op (.bin .sub t0 textLen regk)) x u₁ 1 := by
        simpa only [BinOp.eval, hrx.tl_eq] using
          (ExecWithin.bin (f := .sub) (d := t0) (i := textLen) (j := regk) (x := x)
            (hw.of_le (by simp only [BinOp.eval, hrx.tl_eq]; omega)))
      have hru₁ : SearchRegs I u₁ := hrx.set_scratch t0 _
      have hu₁_pos : u₁.regs posReg = pos := Data.set_regs_of_ne (by decide) _
      by_cases hpos_lt : pos < n - k
      · have hpk_lt : pos + k < n := by omega
        have hc_pos : (Cond.lt posReg t0).Holds u₁ := by
          simp only [Cond.holds_lt, hu₁_pos, u₁, Data.set_regs_self]; exact hpos_lt
        have hread_p : u₁.mem (4 + I.text.length + I.sa.length + k) = I.pat[k] :=
          hrx.pat_holds.get k hk_lt
        have hread_t : u₁.mem (4 + (pos + k)) = I.text[pos + k] :=
          hrx.txt_holds.get (pos + k) hpk_lt
        have hf_pa : Fits w (4 + I.text.length + I.sa.length + k) := hw.of_le (by omega)
        have hf_pk : Fits w (pos + k) := hw.of_le (by omega)
        have hf_ta : Fits w (4 + (pos + k)) := hw.of_le (by omega)
        have hloads : ∃ u₂, ExecWithin w cmpLoads u₁ u₂ 5 ∧
            u₂.regs t0 = I.pat[k] ∧ u₂.regs t1 = I.text[pos + k] ∧ u₂.mem = u₁.mem := by
          have hu₁_k : u₁.regs regk = k := Data.set_regs_of_ne (by decide) _
          refine WP.exists_execWithin ?_
          unfold cmpLoads
          wram_exec [hru₁.pb_eq, hru₁.tb_eq, hu₁_k, hu₁_pos, hread_p, hread_t,
            hf_pa, hf_pk, hf_ta]
          refine ⟨?_, ?_, rfl⟩
          · wram_simp
          · wram_simp
        obtain ⟨u₂, eloads, hu₂_t0, hu₂_t1, hu₂_mem⟩ := hloads
        have hru₂ : SearchRegs I u₂ := hru₁.search_exec eloads (fun a _ => congrFun hu₂_mem a)
        have hu₂_k : u₂.regs regk = k :=
          (eloads.regs_eq (by decide)).trans (Data.set_regs_of_ne (by decide) _)
        have hu₂_pos : u₂.regs posReg = pos := (eloads.regs_eq (by decide)).trans hu₁_pos
        have hu₂_res : u₂.regs resReg = 1 :=
          (eloads.regs_eq (by decide)).trans ((Data.set_regs_of_ne (by decide) _).trans hres)
        have hu₂_go : u₂.regs go = 1 :=
          (eloads.regs_eq (by decide)).trans ((Data.set_regs_of_ne (by decide) _).trans hgo)
        have hu₂_lo : u₂.regs loReg = x.regs loReg :=
          (eloads.regs_eq (by decide)).trans (Data.set_regs_of_ne (by decide) _)
        have hu₂_hi : u₂.regs hiReg = x.regs hiReg :=
          (eloads.regs_eq (by decide)).trans (Data.set_regs_of_ne (by decide) _)
        have hu₂_mid : u₂.regs midReg = x.regs midReg :=
          (eloads.regs_eq (by decide)).trans (Data.set_regs_of_ne (by decide) _)
        have hu₂_sv : u₂.regs savedLo = x.regs savedLo :=
          (eloads.regs_eq (by decide)).trans (Data.set_regs_of_ne (by decide) _)
        by_cases hlt1 : I.pat[k] < I.text[pos + k]
        · have hc_lt1 : (Cond.lt t0 t1).Holds u₂ := by
            simp only [Cond.holds_lt, hu₂_t0, hu₂_t1]; exact hlt1
          set u₃ := (u₂.set resReg 0).set go 0
          have c_lt : ExecWithin (B := .standard) w
              (.seq (.op (.copy resReg zero)) (.op (.copy go zero))) u₂ u₃ 2 :=
            WP.execWithin <| by
              wram_exec [hru₂.zero_eq]
              rfl
          have hbody : ExecWithin w cmpBody x u₃ 12 := by
            unfold cmpBody
            exact (ExecWithin.branch_pos hc_k
              (ExecWithin.branch_pos hc_kn
                (b₁.seq (ExecWithin.branch_pos hc_pos
                  (eloads.seq (ExecWithin.branch_pos hc_lt1 c_lt)))))).mono (by omega)
          have hcmp : cmpSuffix I.text.toArray (I.pat.drop k) (pos + k) = .lt := by
            rw [List.drop_eq_getElem_cons hk_lt, cmpSuffix,
              dite_eq_left (by simpa only [List.size_toArray] using hpk_lt),
              List.getElem_toArray, compare_lt_iff_lt.mpr hlt1]
          have h1 := cmpLoop_stop (ord := .lt) hc_go hbody (by omega)
            (hru₂.search_exec c_lt (fun _ _ => rfl))
            (Data.set_regs_self _ go 0)
            (hbody.regs_eq (by decide)) (hbody.regs_eq (by decide))
            (hbody.regs_eq (by decide)) (hbody.regs_eq (by decide))
            ((Data.set_regs_of_ne (by decide) 0).trans (Data.set_regs_self u₂ resReg 0))
            hcmp
          rwa [hrem] at h1
        · have hc_nlt1 : ¬(Cond.lt t0 t1).Holds u₂ := by
            simp only [Cond.holds_lt, hu₂_t0, hu₂_t1]; exact hlt1
          by_cases hlt2 : I.text[pos + k] < I.pat[k]
          · have hc_lt2 : (Cond.lt t1 t0).Holds u₂ := by
              simp only [Cond.holds_lt, hu₂_t0, hu₂_t1]; exact hlt2
            have hbody : ExecWithin w cmpBody x ((u₂.set resReg 2).set go 0) 14 := by
              unfold cmpBody
              exact (ExecWithin.branch_pos hc_k
                (ExecWithin.branch_pos hc_kn
                  (b₁.seq (ExecWithin.branch_pos hc_pos
                    (eloads.seq (ExecWithin.branch_neg hc_nlt1
                      (ExecWithin.branch_pos hc_lt2 (setGtStop_exec u₂ hru₂)))))))).mono (by omega)
            have hcmp : cmpSuffix I.text.toArray (I.pat.drop k) (pos + k) = .gt := by
              rw [List.drop_eq_getElem_cons hk_lt, cmpSuffix,
                dite_eq_left (by simpa only [List.size_toArray] using hpk_lt),
                List.getElem_toArray, compare_gt_iff_gt.mpr hlt2]
            have h1 := cmpLoop_gt_stop hc_go hbody (by omega) hru₂ hu₂_lo hu₂_hi hu₂_mid hu₂_sv hcmp
            rwa [hrem] at h1
          · have hc_nlt2 : ¬(Cond.lt t1 t0).Holds u₂ := by
              simp only [Cond.holds_lt, hu₂_t0, hu₂_t1]; exact hlt2
            have heq_ch : I.pat[k] = I.text[pos + k] := by omega
            have hf_k1 : Fits w (k + 1) := hw.of_le (by omega)
            set u₃ := u₂.set regk (k + 1)
            have c₁ : ExecWithin w (.op (.bin .add regk regk one)) u₂ u₃ 1 :=
              WP.execWithin <| by
                wram_exec [hu₂_k, hru₂.one_eq, hf_k1]
                rfl
            have hbody : ExecWithin w cmpBody x u₃ 14 := by
              unfold cmpBody
              exact (ExecWithin.branch_pos hc_k
                (ExecWithin.branch_pos hc_kn
                  (b₁.seq (ExecWithin.branch_pos hc_pos
                    (eloads.seq (ExecWithin.branch_neg hc_nlt1
                      (ExecWithin.branch_neg hc_nlt2 c₁))))))).mono (by omega)
            obtain ⟨y, T_rec, hrec, hry, hy_lo, hy_hi, hy_mid, hy_sv, hy_res, hT_rec⟩ :=
              ih u₃ (by rw [Data.set_regs_self u₂ regk _]; omega)
                (hru₂.set_scratch regk (k + 1))
                ((c₁.regs_eq (by decide)).trans hu₂_res)
                ((c₁.regs_eq (by decide)).trans hu₂_go)
            rw [Data.set_regs_self u₂ regk _, (c₁.regs_eq (by decide)).trans hu₂_pos] at hy_res
            have hcmp_step : cmpSuffix I.text.toArray (I.pat.drop k) (pos + k) =
                cmpSuffix I.text.toArray (I.pat.drop (k + 1)) (pos + (k + 1)) := by
              rw [List.drop_eq_getElem_cons hk_lt, cmpSuffix,
                dite_eq_left (by simpa only [List.size_toArray] using hpk_lt),
                List.getElem_toArray, compare_eq_iff_eq.mpr heq_ch, ← Nat.add_assoc pos k 1]
            refine ⟨y, 14 + T_rec + 2, ExecWithin.loop_iter hc_go hbody hrec, hry,
              hy_lo.trans (hbody.regs_eq (by decide)),
              hy_hi.trans (hbody.regs_eq (by decide)),
              hy_mid.trans (hbody.regs_eq (by decide)),
              hy_sv.trans (hbody.regs_eq (by decide)),
              by rw [hcmp_step]; exact hy_res, by omega⟩
      · have hc_npos : ¬(Cond.lt posReg t0).Holds u₁ := by
          simp only [Cond.holds_lt, hu₁_pos, u₁, Data.set_regs_self]; exact hpos_lt
        have hbody : ExecWithin w cmpBody x ((u₁.set resReg 2).set go 0) 7 := by
          unfold cmpBody
          exact (ExecWithin.branch_pos hc_k
            (ExecWithin.branch_pos hc_kn
              (b₁.seq (ExecWithin.branch_neg hc_npos (setGtStop_exec u₁ hru₁))))).mono (by omega)
        have hcmp : cmpSuffix I.text.toArray (I.pat.drop k) (pos + k) = .gt := by
          rw [List.drop_eq_getElem_cons hk_lt, cmpSuffix,
            dite_eq_right (by simp only [List.size_toArray]; omega)]
        have h1 := cmpLoop_gt_stop hc_go hbody (by omega) hru₁
          (Data.set_regs_of_ne (by decide) _)
          (Data.set_regs_of_ne (by decide) _)
          (Data.set_regs_of_ne (by decide) _)
          (Data.set_regs_of_ne (by decide) _) hcmp
        rwa [hrem] at h1
    · have hc_nkn : ¬(Cond.lt regk textLen).Holds x := by
        simp only [Cond.holds_lt, hrx.tl_eq]; exact hk_n
      have hbody : ExecWithin w cmpBody x ((x.set resReg 2).set go 0) 5 := by
        unfold cmpBody
        exact (ExecWithin.branch_pos hc_k
          (ExecWithin.branch_neg hc_nkn (setGtStop_exec x hrx))).mono (by omega)
      have hcmp : cmpSuffix I.text.toArray (I.pat.drop k) (pos + k) = .gt := by
        rw [List.drop_eq_getElem_cons hk_lt, cmpSuffix,
          dite_eq_right (by simp only [List.size_toArray]; omega)]
      have h1 := cmpLoop_gt_stop hc_go hbody (by omega) hrx rfl rfl rfl rfl hcmp
      rwa [hrem] at h1

private theorem cmpSuffixCode_spec (I : SearchInput) {w : ℕ}
    (hw : Fits w (I.text.length + I.sa.length + I.pat.length + 6))
    (s : Data 20) (hs : SearchRegs I s) (hm : s.regs midReg < I.sa.length) :
    ∃ s', ExecWithin w cmpSuffixCode s s' (16 * I.pat.length + 23) ∧
      SearchRegs I s' ∧
      s'.regs loReg = s.regs loReg ∧
      s'.regs hiReg = s.regs hiReg ∧
      s'.regs midReg = s.regs midReg ∧
      s'.regs savedLo = s.regs savedLo ∧
      s'.regs resReg = encodeOrd (cmpSuffix I.text.toArray I.pat I.sa[s.regs midReg]) := by
  have hmem_sa : s.mem (4 + I.text.length + s.regs midReg) = I.sa[s.regs midReg] :=
    hs.sa_holds.get (s.regs midReg) hm
  have hf_sa_m : Fits w (4 + I.text.length + s.regs midReg) := hw.of_le (by omega)
  have hprep : ∃ u, ExecWithin w cmpPrep s u 5 ∧
      u.regs posReg = I.sa[s.regs midReg] ∧ u.regs regk = 0 ∧
      u.regs resReg = 1 ∧ u.regs go = 1 ∧ u.mem = s.mem := by
    refine WP.exists_execWithin ?_
    unfold cmpPrep
    wram_exec [hs.sb_eq, hs.zero_eq, hs.one_eq, hmem_sa, hf_sa_m]
    refine ⟨?_, ?_, ?_, ?_, rfl⟩
    · wram_simp
    · wram_simp [hs.zero_eq]
    · wram_simp [hs.one_eq]
    · wram_simp [hs.one_eq]
  obtain ⟨u, eprep, hu_pos, hu_k, hu_res, hu_go, hu_mem⟩ := hprep
  obtain ⟨s', T_loop, eloop, hrs', hs'_lo, hs'_hi, hs'_mid, hs'_sv, hs'_res, hT⟩ :=
    cmpLoop_spec I hw I.pat.length u (by rw [hu_k, Nat.sub_zero])
      (hs.search_exec eprep (fun a _ => congrFun hu_mem a)) hu_res hu_go
  rw [hu_k, hu_pos, List.drop_zero, Nat.add_zero] at hs'_res
  unfold cmpSuffixCode
  exact ⟨s', (eprep.seq eloop).mono (by omega), hrs',
    hs'_lo.trans (eprep.regs_eq (by decide)), hs'_hi.trans (eprep.regs_eq (by decide)),
    hs'_mid.trans (eprep.regs_eq (by decide)), hs'_sv.trans (eprep.regs_eq (by decide)),
    hs'_res⟩

private theorem twoBisections_spec (I : SearchInput) {w : ℕ}
    (hw : Fits w (I.text.length + I.sa.length + I.pat.length + 6)) :
    ∃ x₂, ExecWithin w (.seq searchSetup twoBisectionsCode) (Data.init I.encode) x₂
        ((32 * I.pat.length + 63) * (Nat.log 2 I.sa.length + 1) + 20) ∧
      SearchRegs I x₂ ∧
      x₂.regs savedLo = (search I.text I.sa I.pat).1 ∧
      x₂.regs loReg = (search I.text I.sa I.pat).2 := by
  let x : Data 20 := Data.init I.encode
  obtain ⟨hm1, hm2, hm3, htxt, hsa, hpat⟩ := init_searchEncode I
  let n := I.text.length
  let m := I.sa.length
  let plen := I.pat.length
  have hf_1 : Fits w 1 := hw.of_le (by omega)
  have hf_2 : Fits w 2 := hw.of_le (by omega)
  have hf_3 : Fits w 3 := hw.of_le (by omega)
  have hf_4 : Fits w 4 := hw.of_le (by omega)
  have hf_sb : Fits w (4 + I.text.length) := hw.of_le (by omega)
  have hf_pb : Fits w (4 + I.text.length + I.sa.length) := hw.of_le (by omega)
  have hf_out : Fits w (4 + I.text.length + I.sa.length + I.pat.length) := hw.of_le (by omega)
  have hf_m : Fits w m := hw.of_le (by omega)
  have hsetup : ∃ x₁, ExecWithin w searchSetup x x₁ 13 ∧
      SearchRegs I x₁ ∧ x₁.regs loReg = 0 ∧ x₁.regs hiReg = m := by
    refine WP.exists_execWithin ?_
    unfold searchSetup
    wram_exec [x, Data.init_regs, hm1, hm2, hm3, hf_1, hf_2, hf_3, hf_4, hf_sb, hf_pb, hf_out]
    exact ⟨⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
      by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
      htxt, hsa, hpat⟩, by wram_simp, by wram_simp; rfl⟩
  obtain ⟨x₁, es, hrx₁, hx₁_lo, hx₁_hi⟩ := hsetup
  have hprobe_below : ∀ s, SearchRegs I s → 0 ≤ s.regs midReg → s.regs midReg < m →
      ∃ s', ExecWithin w probeBelowCode s s' (16 * plen + 24) ∧
        SearchRegs I s' ∧ s'.regs loReg = s.regs loReg ∧ s'.regs hiReg = s.regs hiReg ∧
        s'.regs midReg = s.regs midReg ∧
        (0 < s'.regs resReg ↔
          probeBelow I.text.toArray I.sa.toArray I.pat (s.regs midReg) = true) := by
    intro s hs _ hm
    obtain ⟨u, eu, hru, hu_lo, hu_hi, hu_mid, _, hu_res⟩ := cmpSuffixCode_spec I hw s hs hm
    set s' := u.set resReg (u.regs resReg - 1)
    have esub : ExecWithin w (.op (.bin .sub resReg resReg one)) u s' 1 := by
      have hf : Fits w (u.regs resReg - 1) := by
        rw [hu_res]; cases cmpSuffix I.text.toArray I.pat I.sa[s.regs midReg] <;>
          exact hw.of_le (by simp [encodeOrd])
      simpa only [BinOp.eval, hru.one_eq] using
        (ExecWithin.bin (f := .sub) (d := resReg) (i := resReg) (j := one) (x := u)
          (by simpa only [BinOp.eval, hru.one_eq] using hf))
    unfold probeBelowCode
    refine ⟨s', eu.seq esub, hru.set_scratch resReg _,
      (Data.set_regs_of_ne (by decide) _).trans hu_lo,
      (Data.set_regs_of_ne (by decide) _).trans hu_hi,
      (Data.set_regs_of_ne (by decide) _).trans hu_mid, ?_⟩
    simp only [s', Data.set_regs_self, hu_res, probeBelow,
      getElem!_pos I.sa.toArray (s.regs midReg) (by simpa using hm), List.getElem_toArray]
    cases cmpSuffix I.text.toArray I.pat I.sa[s.regs midReg] <;> decide
  obtain ⟨u₁, ebis₁, hru₁, hu₁_lo, _⟩ :=
    bisectCode_exec (L := 0) (R := m)
      (by decide : [loReg, hiReg, midReg, resReg, zero, one].Nodup)
      (probeBelow I.text.toArray I.sa.toArray I.pat)
      (fun _ h => h.zero_eq) (fun _ h => h.one_eq)
      (fun _ v h => h.set_scratch loReg v)
      (fun _ v h => h.set_scratch hiReg v)
      (fun _ v h => h.set_scratch midReg v)
      hprobe_below x₁ hrx₁ (by rw [hx₁_lo]) (by rw [hx₁_hi]) (by rw [hx₁_hi]; exact hf_m)
  rw [hx₁_lo, hx₁_hi] at ebis₁ hu₁_lo
  rw [Nat.sub_zero] at ebis₁
  set lo_val := (search I.text I.sa I.pat).1
  change u₁.regs loReg = lo_val at hu₁_lo
  set u₂ := ((u₁.set savedLo lo_val).set loReg 0).set hiReg m
  let Inv₂ (s : Data 20) : Prop := SearchRegs I s ∧ s.regs savedLo = lo_val
  have hu₂_inv : Inv₂ u₂ :=
    ⟨((hru₁.set_scratch savedLo lo_val).set_scratch loReg 0).set_scratch hiReg m,
     by simp only [u₂, Data.set_regs_of_ne (by decide : savedLo ≠ hiReg),
          Data.set_regs_of_ne (by decide : savedLo ≠ loReg), Data.set_regs_self]⟩
  have hu₂_lo : u₂.regs loReg = 0 :=
    (Data.set_regs_of_ne (by decide) m).trans (Data.set_regs_self _ loReg 0)
  have hu₂_hi : u₂.regs hiReg = m := Data.set_regs_self _ hiReg m
  have hprobe_atmost : ∀ s, Inv₂ s → 0 ≤ s.regs midReg → s.regs midReg < m →
      ∃ s', ExecWithin w probeAtMostCode s s' (16 * plen + 23) ∧
        Inv₂ s' ∧ s'.regs loReg = s.regs loReg ∧ s'.regs hiReg = s.regs hiReg ∧
        s'.regs midReg = s.regs midReg ∧
        (0 < s'.regs resReg ↔
          probeAtMost I.text.toArray I.sa.toArray I.pat (s.regs midReg) = true) := by
    intro s ⟨hs, hsv⟩ _ hm
    obtain ⟨s', es', hrs', hs'_lo, hs'_hi, hs'_mid, hs'_sv, hs'_res⟩ :=
      cmpSuffixCode_spec I hw s hs hm
    refine ⟨s', es', ⟨hrs', hs'_sv.trans hsv⟩, hs'_lo, hs'_hi, hs'_mid, ?_⟩
    simp only [hs'_res, probeAtMost,
      getElem!_pos I.sa.toArray (s.regs midReg) (by simpa using hm), List.getElem_toArray]
    cases cmpSuffix I.text.toArray I.pat I.sa[s.regs midReg] <;> decide
  obtain ⟨x₂, ebis₂, ⟨hrx₂, hx₂_sv⟩, hx₂_lo, _⟩ :=
    bisectCode_exec (L := 0) (R := m)
      (by decide : [loReg, hiReg, midReg, resReg, zero, one].Nodup)
      (probeAtMost I.text.toArray I.sa.toArray I.pat)
      (fun _ h => h.1.zero_eq) (fun _ h => h.1.one_eq)
      (fun _ v ⟨h, hsv⟩ => ⟨h.set_scratch loReg v,
        (Data.set_regs_of_ne (by decide) v).trans hsv⟩)
      (fun _ v ⟨h, hsv⟩ => ⟨h.set_scratch hiReg v,
        (Data.set_regs_of_ne (by decide) v).trans hsv⟩)
      (fun _ v ⟨h, hsv⟩ => ⟨h.set_scratch midReg v,
        (Data.set_regs_of_ne (by decide) v).trans hsv⟩)
      hprobe_atmost u₂ hu₂_inv (by rw [hu₂_lo]) (by rw [hu₂_hi]) (by rw [hu₂_hi]; exact hf_m)
  rw [hu₂_lo, hu₂_hi] at ebis₂ hx₂_lo
  rw [Nat.sub_zero] at ebis₂
  change x₂.regs loReg = (search I.text I.sa I.pat).2 at hx₂_lo
  have etwo : ExecWithin w twoBisectionsCode x₁ x₂
      ((32 * plen + 63) * (Nat.log 2 m + 1) + 7) :=
    WP.execWithin <| by
      unfold twoBisectionsCode
      refine WP.seq (WP.of_execWithin ebis₁ ?_)
      wram_exec [hu₁_lo, hru₁.zero_eq, hru₁.sl_eq]
      refine WP.of_execWithin ebis₂ ⟨?_, rfl⟩
      linarith
  exact ⟨x₂, (es.seq etwo).mono (by dsimp only [plen, m] at *; omega), hrx₂, hx₂_sv, hx₂_lo⟩

/-- `rangeSearchCode` executes within `(32 * |I.pat| + 63) * (Nat.log 2 |I.sa| + 1) + 25`
instructions from `Data.init I.encode` whenever
`Fits w (|I.text| + |I.sa| + |I.pat| + 6)`, writing
`[(search I.text I.sa I.pat).1, (search I.text I.sa I.pat).2]` at
`y.regs Reg.out = 4 + |I.text| + |I.sa| + |I.pat|`. -/
theorem rangeSearchCode_exec (I : SearchInput) {w : ℕ}
    (hw : Fits w (I.text.length + I.sa.length + I.pat.length + 6)) :
    ∃ y, ExecWithin w rangeSearchCode (Data.init I.encode) y
        ((32 * I.pat.length + 63) * (Nat.log 2 I.sa.length + 1) + 25) ∧
      outputList y.mem (y.regs out) =
        [(search I.text I.sa I.pat).1, (search I.text I.sa I.pat).2] ∧
      y.regs out = 4 + I.text.length + I.sa.length + I.pat.length ∧
      Fits w (y.regs out + 2) ∧
      Block.HoldsList 4 I.text y.mem ∧
      Block.HoldsList (4 + I.text.length) I.sa y.mem ∧
      Block.HoldsList (4 + I.text.length + I.sa.length) I.pat y.mem := by
  obtain ⟨x₂, etwo, hrx₂, hx₂_sv, hx₂_lo⟩ := twoBisections_spec I hw
  let out₀ := 4 + I.text.length + I.sa.length + I.pat.length
  let lo := (search I.text I.sa I.pat).1
  let hi := (search I.text I.sa I.pat).2
  have hf_o1 : Fits w (out₀ + 1) := hw.of_le (by omega)
  have hf_o2 : Fits w (out₀ + 2) := hw.of_le (by omega)
  have hfin : ∃ y, ExecWithin w rangeSearchFinish x₂ y 5 ∧
      y.regs out = out₀ ∧
      y.mem out₀ = 2 ∧ y.mem (out₀ + 1) = lo ∧ y.mem (out₀ + 2) = hi ∧
      (∀ a < out₀, y.mem a = x₂.mem a) := by
    refine WP.exists_execWithin ?_
    unfold rangeSearchFinish
    wram_exec [hrx₂.out_eq, hrx₂.one_eq, hrx₂.two_eq, hx₂_sv, hx₂_lo, hf_o1, hf_o2]
    refine ⟨by wram_simp [hrx₂.out_eq]; rfl, ?_, ?_, ?_, fun a ha => ?_⟩
    · simp only [Data.write_mem, Data.set_mem]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    · simp only [Data.write_mem, Data.set_mem]
      rw [Function.update_of_ne (by omega), Function.update_self]
    · simp only [Data.write_mem, Data.set_mem]
      rw [Function.update_self]
    · simp only [Data.write_mem, Data.set_mem]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
  obtain ⟨y, efin, hy_out, hm0, hm1, hm2, hframe⟩ := hfin
  have hout_list : outputList y.mem (y.regs out) = [lo, hi] := by
    rw [outputList_eq_iff, hy_out]
    refine ⟨hm0, Block.holdsList_cons_iff.mpr ⟨hm1, Block.holdsList_cons_iff.mpr
      ⟨by simpa only [Nat.add_assoc] using hm2, Block.holdsList_nil _ _⟩⟩⟩
  unfold rangeSearchCode
  exact ⟨y, (etwo.seq efin).mono (by omega),
    hout_list, hy_out, by rw [hy_out]; exact hf_o2,
    hrx₂.txt_holds.frame (fun a _ ha2 => hframe a (by omega)),
    hrx₂.sa_holds.frame (fun a _ ha2 => hframe a (by omega)),
    hrx₂.pat_holds.frame (fun a _ ha2 => hframe a (by omega))⟩

/-- `rangeSearchProgram` computes
`[(search I.text I.sa I.pat).1, (search I.text I.sa I.pat).2]` in
`(32 * |I.pat| + 63) * (Nat.log 2 |I.sa| + 1) + 26` instructions (`O(|I.pat| log |I.sa|)`) at every
word width `w` with `Fits w (|I.text| + |I.sa| + |I.pat| + 6)`. -/
theorem rangeSearchProgram_computesListInTime :
    rangeSearchProgram.ComputesListInTime (fun _ (I : SearchInput) => I.encode)
      (fun I _ => (32 * I.pat.length + 63) * (Nat.log 2 I.sa.length + 1) + 26)
      (fun I w => Fits w (I.text.length + I.sa.length + I.pat.length + 6))
      (fun I => [(search I.text I.sa I.pat).1, (search I.text I.sa I.pat).2]) :=
  rangeSearchCode.computesListInTime_program out fun I _ hw _ => by
    obtain ⟨y, hexec, hout, _, hfit, _, _, _⟩ := rangeSearchCode_exec I hw
    exact ⟨y, hexec, hout, hfit⟩

private structure OccCopyInv (I : SearchInput) (lo hi : ℕ) (x : Data 20) : Prop where
  regs : SearchRegs I x
  sv_eq : x.regs savedLo = lo
  hi_eq : x.regs hiReg = hi - lo
  k_le : x.regs regk ≤ hi - lo
  out_hdr : x.mem (4 + I.text.length + I.sa.length + I.pat.length) = hi - lo
  out_holds : Block.HoldsList (4 + I.text.length + I.sa.length + I.pat.length + 1)
    ((occurrences I.text I.sa I.pat).take (x.regs regk)) x.mem

/-- `occurrencesCode` executes within
`(32 * |I.pat| + 63) * (Nat.log 2 |I.sa| + 1) + 9 * |occurrences I.text I.sa I.pat| + 26`
instructions from `Data.init I.encode` whenever
`Fits w (|I.text| + 2 * |I.sa| + |I.pat| + 6)`, writing `occurrences I.text I.sa I.pat` at
`y.regs Reg.out = 4 + |I.text| + |I.sa| + |I.pat|`. -/
theorem occurrencesCode_exec (I : SearchInput) {w : ℕ}
    (hw : Fits w (I.text.length + 2 * I.sa.length + I.pat.length + 6)) :
    ∃ y, ExecWithin w occurrencesCode (Data.init I.encode) y
        ((32 * I.pat.length + 63) * (Nat.log 2 I.sa.length + 1) +
          9 * (occurrences I.text I.sa I.pat).length + 26) ∧
      outputList y.mem (y.regs out) = occurrences I.text I.sa I.pat ∧
      y.regs out = 4 + I.text.length + I.sa.length + I.pat.length ∧
      Fits w (y.regs out + (occurrences I.text I.sa I.pat).length) ∧
      Block.HoldsList 4 I.text y.mem ∧
      Block.HoldsList (4 + I.text.length) I.sa y.mem ∧
      Block.HoldsList (4 + I.text.length + I.sa.length) I.pat y.mem := by
  obtain ⟨x₂, etwo, hrx₂, hx₂_sv, hx₂_lo⟩ := twoBisections_spec I (hw.of_le (by omega))
  let n := I.text.length
  let m := I.sa.length
  let plen := I.pat.length
  let out₀ := 4 + I.text.length + I.sa.length + I.pat.length
  let lo := (search I.text I.sa I.pat).1
  let hi := (search I.text I.sa I.pat).2
  let occ := occurrences I.text I.sa I.pat
  have hhi_le_m : hi ≤ m := by
    have := (lowerBound_bounds (probeAtMost I.text.toArray I.sa.toArray I.pat) 0 m).2
    simpa only [hi, search, searchArray, List.size_toArray, Nat.zero_max] using this
  have hocc_eq : occ = (I.sa.take hi).drop lo := rfl
  unfold occurrencesCode
  by_cases hlt : lo < hi
  · have hc_lt : (Cond.lt savedLo loReg).Holds x₂ := by
      simp only [Cond.holds_lt, hx₂_sv, hx₂_lo]; exact hlt
    have hocc_len : occ.length = hi - lo := by
      rw [hocc_eq, List.length_drop, List.length_take]
      omega
    have hf_cnt : Fits w (hi - lo) := hw.of_le (by omega)
    set u₁ := ((x₂.set hiReg (hi - lo)).write out₀ (hi - lo)).set regk 0
    have e_init : ExecWithin w occCopyInit x₂ u₁ 3 :=
      WP.execWithin <| by
        unfold occCopyInit
        wram_exec [hx₂_lo, hx₂_sv, hrx₂.out_eq, hrx₂.zero_eq, hf_cnt]
        rfl
    have hru₁ : SearchRegs I u₁ := hrx₂.search_exec e_init fun a ha => by
      simp only [u₁, out₀, Data.set_mem, Data.write_mem]
      rw [Function.update_of_ne (by omega)]
    have hu₁_k : u₁.regs regk = 0 := Data.set_regs_self _ regk 0
    have hu₁_inv : OccCopyInv I lo hi u₁ :=
      ⟨hru₁,
       (e_init.regs_eq (by decide)).trans hx₂_sv,
       by
         simp only [u₁, Data.set_regs_of_ne (by decide : hiReg ≠ regk), Data.write_regs,
           Data.set_regs_self],
       by rw [hu₁_k]; exact Nat.zero_le _,
       by
         dsimp only [u₁, out₀]
         simp only [Data.set_mem, Data.write_mem, Function.update_self],
       by simpa only [hu₁_k, List.take_zero] using Block.holdsList_nil (out₀ + 1) u₁.mem⟩
    have hloop := ExecWithin.loop_invariant (w := w) (cond := .lt regk hiReg) (body := occCopyBody)
      (OccCopyInv I lo hi) (fun s => (hi - lo) - s.regs regk) (T := 7)
      (fun s hs hc => by
        simp only [Cond.holds_lt, hs.hi_eq] at hc
        let k := s.regs regk
        have hlk_m : lo + k < m := by omega
        have hocc_k : occ[k]'(by omega) = I.sa[lo + k] := by
          dsimp only [occ, lo]
          simp only [occurrences, List.getElem_drop, List.getElem_take]
        have hread_sa : s.mem (4 + I.text.length + (lo + s.regs regk)) = I.sa[lo + k] :=
          hs.regs.sa_holds.get (lo + k) hlk_m
        have hf_lk : Fits w (lo + k) := hw.of_le (by omega)
        have hf_sa_lk : Fits w (4 + n + (lo + k)) := hw.of_le (by omega)
        have hf_o1 : Fits w (out₀ + 1) := hw.of_le (by omega)
        have hf_o1k : Fits w (out₀ + 1 + k) := hw.of_le (by omega)
        have hf_k1 : Fits w (k + 1) := hw.of_le (by omega)
        have hstep : ∃ s', ExecWithin w occCopyBody s s' 7 ∧
            s'.regs regk = k + 1 ∧
            s'.mem = Function.update s.mem (out₀ + 1 + k) I.sa[lo + k] := by
          refine WP.exists_execWithin ?_
          unfold occCopyBody
          wram_exec [hs.sv_eq, hs.regs.sb_eq, hs.regs.out_eq, hs.regs.one_eq, hread_sa,
            hf_lk, hf_sa_lk, hf_o1, hf_o1k, hf_k1]
          refine ⟨?_, ?_⟩
          · wram_simp [k]
          · dsimp only [out₀, k, lo] at hread_sa ⊢
            simp only [Data.set_mem, Data.write_mem]
        obtain ⟨s', es', hs'_k, hs'_mem⟩ := hstep
        have hrs' : SearchRegs I s' := hs.regs.search_exec es' fun a ha => by
          rw [hs'_mem, Function.update_of_ne (by omega)]
        refine ⟨s', es', ⟨hrs', (es'.regs_eq (by decide)).trans hs.sv_eq,
          (es'.regs_eq (by decide)).trans hs.hi_eq,
          by rw [hs'_k]; omega, ?_, ?_⟩,
          by rw [hs'_k]; omega⟩
        · rw [hs'_mem, Function.update_of_ne (by omega)]
          exact hs.out_hdr
        · rw [hs'_k, hs'_mem]
          have htake_step : occ.take (k + 1) = occ.take k ++ [I.sa[lo + k]] := by
            rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some, hocc_k]
          have htake_len : (occ.take k).length = k := List.length_take_of_le (by omega)
          have hout_addr : out₀ + 1 + k = (out₀ + 1) + (occ.take k).length := by rw [htake_len]
          rw [htake_step, hout_addr]
          exact hs.out_holds.append_one I.sa[lo + k])
      hu₁_inv
    obtain ⟨y, eloop, hy_inv, hnc⟩ := hloop
    simp only [Cond.holds_lt, hy_inv.hi_eq, not_lt] at hnc
    have hy_k : y.regs regk = hi - lo := le_antisymm hy_inv.k_le hnc
    rw [hu₁_k, Nat.sub_zero] at eloop
    have hout_holds := hy_inv.out_holds
    rw [hy_k, ← hocc_len, List.take_length] at hout_holds
    have hout_list : outputList y.mem (y.regs out) = occ := by
      rw [outputList_eq_iff, hy_inv.regs.out_eq, hocc_len]
      exact ⟨hy_inv.out_hdr, hout_holds⟩
    have efin : ExecWithin w occurrencesFinish x₂ y (9 * (hi - lo) + 6) := by
      unfold occurrencesFinish
      exact (ExecWithin.branch_pos hc_lt (e_init.seq eloop)).mono (by omega)
    refine ⟨y, (etwo.seq efin).mono (by rw [hocc_len]; omega),
      hout_list, hy_inv.regs.out_eq,
      by rw [hy_inv.regs.out_eq, hocc_len]; exact hw.of_le (by omega),
      hy_inv.regs.txt_holds, hy_inv.regs.sa_holds, hy_inv.regs.pat_holds⟩
  · have hc_nlt : ¬(Cond.lt savedLo loReg).Holds x₂ := by
      simp only [Cond.holds_lt, hx₂_sv, hx₂_lo]; exact hlt
    have hocc_nil : occ = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [hocc_eq, List.length_drop, List.length_take]
      omega
    set y := x₂.write out₀ 0
    have est : ExecWithin (B := .standard) w (.op (.store out zero)) x₂ y 1 := by
      simpa only [hrx₂.out_eq, hrx₂.zero_eq] using
        (ExecWithin.store (B := .standard) (a := out) (s := zero) (x := x₂))
    have efin : ExecWithin w occurrencesFinish x₂ y 3 := by
      unfold occurrencesFinish
      exact ExecWithin.branch_neg hc_nlt est
    have hy_out : y.regs out = out₀ := hrx₂.out_eq
    have hout_list : outputList y.mem (y.regs out) = occ := by
      rw [hocc_nil, outputList_eq_iff, hy_out]
      exact ⟨by simp only [y, Data.write_mem, Function.update_self, List.length_nil],
        Block.holdsList_nil _ _⟩
    dsimp only [occ] at hocc_nil
    refine ⟨y, (etwo.seq efin).mono (by omega),
      hout_list, hy_out,
      by rw [hy_out, hocc_nil, List.length_nil]; exact hw.of_le (by omega),
      hrx₂.txt_holds.frame (fun a _ ha2 => by
        simp only [y, Data.write_mem]; rw [Function.update_of_ne (by omega)]),
      hrx₂.sa_holds.frame (fun a _ ha2 => by
        simp only [y, Data.write_mem]; rw [Function.update_of_ne (by omega)]),
      hrx₂.pat_holds.frame (fun a _ ha2 => by
        simp only [y, Data.write_mem]; rw [Function.update_of_ne (by omega)])⟩

/-- `occurrencesProgram` computes `occurrences I.text I.sa I.pat` in
`(32 * |I.pat| + 63) * (Nat.log 2 |I.sa| + 1) + 9 * |occurrences I.text I.sa I.pat| + 27`
instructions at every word width `w` with
`Fits w (|I.text| + 2 * |I.sa| + |I.pat| + 6)`. -/
theorem occurrencesProgram_computesListInTime :
    occurrencesProgram.ComputesListInTime (fun _ (I : SearchInput) => I.encode)
      (fun I _ => (32 * I.pat.length + 63) * (Nat.log 2 I.sa.length + 1) +
        9 * (occurrences I.text I.sa I.pat).length + 27)
      (fun I w => Fits w (I.text.length + 2 * I.sa.length + I.pat.length + 6))
      (fun I => occurrences I.text I.sa I.pat) :=
  occurrencesCode.computesListInTime_program out fun I _ hw _ => by
    obtain ⟨y, hexec, hout, _, hfit, _, _, _⟩ := occurrencesCode_exec I hw
    exact ⟨y, hexec, hout, hfit⟩

/-- Worst-case input-size bound for `occurrencesProgram`: since
`|occurrences I.text I.sa I.pat| ≤ |I.sa|`, `occurrencesProgram` runs within
`(32 * |I.pat| + 63) * (Nat.log 2 |I.sa| + 1) + 9 * |I.sa| + 27` instructions. -/
theorem occurrencesProgram_computesListInTime_worstCase :
    occurrencesProgram.ComputesListInTime (fun _ (I : SearchInput) => I.encode)
      (fun I _ => (32 * I.pat.length + 63) * (Nat.log 2 I.sa.length + 1) +
        9 * I.sa.length + 27)
      (fun I w => Fits w (I.text.length + 2 * I.sa.length + I.pat.length + 6))
      (fun I => occurrences I.text I.sa I.pat) :=
  occurrencesProgram_computesListInTime.mono
    (fun I _ => by
      have hlen : (occurrences I.text I.sa I.pat).length ≤ I.sa.length := by
        simp only [occurrences, List.length_drop, List.length_take]; omega
      omega)
    (fun _ _ h => h)

end Cslib.Algorithms.WordRAM.SuffixArray

