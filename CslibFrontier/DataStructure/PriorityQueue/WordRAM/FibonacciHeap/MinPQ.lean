/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.Spec
public import CslibFrontier.Computability.WordRAM.Subroutine
public import CslibFrontier.DataStructure.WordRAM.StateTransition
public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.BasicOps
public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.Cut
public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.Consolidate
import CslibFrontier.Computability.WordRAM.SymbolicExec.CanonicalCall
import CslibFrontier.Computability.WordRAM.SymbolicExec.MemFrame

/-!
# Fibonacci Heap with Handles and Satellite Values

This file implements the relational priority-queue specification
`Cslib.DataStructure.PriorityQueue.minPQSpec`
(returning an opaque handle `h : Fin n_max` on `insert` and `(u, v, h)` on `extractMin`) as a
Word-RAM `StateTransitionImpl` over `Cslib.WordRAM.Basis.exact` (and lifted to `Basis.standard`),
layered on top of `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap`.

Over capacity `n_max` in a contiguous memory block `[base, base + 11 * n_max + 1)`:
* `[base, base + 9 * n_max + 1)` holds the inner Fibonacci heap arrays (`key`, `par`, `child`,
  `left`, `right`, `deg`, `mark`, `inHeap`, `cons`);
* `[base + (9 * n_max + 1), base + (10 * n_max + 1))` holds satellite values `val[0..n_max-1]`;
* `[base + (10 * n_max + 1), base + (11 * n_max + 1))` holds the recycled-handle stack
  `freeStack[0..n_max-1]`, paired with persistent bump pointer `freshReg` and stack height
  `freeTopReg`.

## Main definitions

* `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.MinPQ.rMinPQ`, `space`, `subroutineCode`:
  `48`-register, `(11 * n_max + 1)`-word `SubroutineCode .exact rMinPQ 1`.
* `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.MinPQ.Rep`, `charge`: relational
  representation invariant and per-operation amortized instruction charges (`O(log n + 1)` on
  `extractMin` in the current number of stored elements `n = MinPQ.size s`).
* `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.MinPQ.impl`:
  `StateTransitionImpl` certificate over `Basis.exact`.
* `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.MinPQ.RunsClient`:
  sequential `Basis.exact` flat-program execution predicate for adaptive `Client`s.

## Main results

* `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.MinPQ.amortized`,
  `run_client_amortized`: standalone `Amortized` certificate and adaptive-client bound
  over `Basis.standard`.
* `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.MinPQ.run_client_exact_fresh`,
  `run_client_exact_reusable`: standalone `Basis.exact` flat-program adaptive-client execution
  theorems.

## References

* [M. L. Fredman and R. E. Tarjan, *Fibonacci heaps and their uses in improved network optimization
  algorithms*][FredmanTarjan1987]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 19][CLRS2009]
-/

@[expose] public section

namespace Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.MinPQ

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.PriorityQueue Cslib.DataStructure.WordRAM
open scoped Cslib.WordRAM

/-! ## Register file (`rMinPQ = 48`), embedding `f42`, and footprint size -/

/-- Total register count of the key–value Fibonacci heap with handle allocation. -/
abbrev rMinPQ : ℕ := 48

/-- Outer bump-pointer frontier register (`base` before `allocSpan`, `base + space n_max` after). -/
abbrev outerFrontierReg : Fin rMinPQ := ⟨1, by decide⟩
/-- Persistent base address of `val[0..n_max-1]` (`base + 9 * n_max + 1`). Also serves as the
relocated image of the inner `FibonacciHeap.frontierReg`. -/
abbrev valBaseReg : Fin rMinPQ := ⟨42, by decide⟩
/-- Persistent base address of `freeStack[0..n_max-1]` (`base + 10 * n_max + 1`). -/
abbrev freeBaseReg : Fin rMinPQ := ⟨43, by decide⟩
/-- Persistent bump-pointer watermark `fresh` for never-allocated handles. -/
abbrev freshReg : Fin rMinPQ := ⟨44, by decide⟩
/-- Persistent stack height `freeTop` for recycled handles in `freeStack`. -/
abbrev freeTopReg : Fin rMinPQ := ⟨45, by decide⟩
/-- Caller input register carrying the satellite value `v` on `insert`. -/
abbrev inValReg : Fin rMinPQ := ⟨46, by decide⟩
/-- Output register carrying the satellite value `v` on `get` and `extractMin`. -/
abbrev outValReg : Fin rMinPQ := ⟨47, by decide⟩

/-- Injective register embedding from the inner `rFib = 42` Fibonacci heap into `rMinPQ = 48`,
mapping `FibonacciHeap.frontierReg` (`R[1]`) to `valBaseReg` (`R[42]`) so `outerFrontierReg`
(`R[1]`) remains outside `Set.range f42`. -/
def f42 (i : Fin rFib) : Fin rMinPQ :=
  if i = FibonacciHeap.frontierReg then valBaseReg else Fin.castLE (by decide) i

theorem f42_injective : Function.Injective f42 := by
  decide

theorem outerFrontierReg_notMem_range : outerFrontierReg ∉ Set.range f42 := by
  decide

theorem freeBaseReg_notMem_range : freeBaseReg ∉ Set.range f42 := by
  decide

theorem freshReg_notMem_range : freshReg ∉ Set.range f42 := by
  decide

theorem freeTopReg_notMem_range : freeTopReg ∉ Set.range f42 := by
  decide

theorem inValReg_notMem_range : inValReg ∉ Set.range f42 := by
  decide

theorem outValReg_notMem_range : outValReg ∉ Set.range f42 := by
  decide

/-- Persistent register holding handle capacity `n_max` (`R[0]`). -/
abbrev nReg : Fin rMinPQ := ⟨0, by decide⟩
/-- Persistent base address of `key[0..n_max-1]` (`R[2]`). -/
abbrev baseReg : Fin rMinPQ := ⟨2, by decide⟩
/-- Persistent constant register `0` (`R[11]`). -/
abbrev zeroP : Fin rMinPQ := ⟨11, by decide⟩
/-- Persistent constant register `1` (`R[12]`). -/
abbrev oneP : Fin rMinPQ := ⟨12, by decide⟩
/-- Caller high tag bit (`R[17]`, `≠ 0` selects `extractMin`). -/
abbrev tag2 : Fin rMinPQ := ⟨17, by decide⟩
/-- Caller middle tag bit (`R[18]`). -/
abbrev tag1 : Fin rMinPQ := ⟨18, by decide⟩
/-- Caller low tag bit (`R[19]`). -/
abbrev tag0 : Fin rMinPQ := ⟨19, by decide⟩
/-- Handle register (`R[20]`, input for `get`/`decreaseKey`, scratch for `insert`). -/
abbrev argV : Fin rMinPQ := ⟨20, by decide⟩
/-- Key input register (`R[21]`, `u` for `insert`, `u'` for `decreaseKey`). -/
abbrev argK : Fin rMinPQ := ⟨21, by decide⟩
/-- Primary output flag register (`R[22]`). -/
abbrev outFlag : Fin rMinPQ := ⟨22, by decide⟩
/-- Output handle register (`R[23]`, `h.val` for `insert` and non-empty `extractMin`). -/
abbrev outV : Fin rMinPQ := ⟨23, by decide⟩
/-- Output key register (`R[24]`, `u` for present `get` and non-empty `extractMin`). -/
abbrev outK : Fin rMinPQ := ⟨24, by decide⟩
/-- Scratch pointer register for `zeroFillCode` (`R[25]`). -/
abbrev curReg : Fin rMinPQ := ⟨25, by decide⟩
/-- Scratch zero register for `zeroFillCode` (`R[26]`). -/
abbrev zeroReg : Fin rMinPQ := ⟨26, by decide⟩
/-- Scratch one register for `zeroFillCode` (`R[27]`). -/
abbrev oneReg : Fin rMinPQ := ⟨27, by decide⟩
/-- Scratch address register (`R[35]`). -/
abbrev s0 : Fin rMinPQ := ⟨35, by decide⟩

/-- Persistent registers are `0..16` and `42..45` (`false`); caller/scratch registers are `17..41`
and `46..47` (`true`). -/
def inputReg (i : Fin rMinPQ) : Bool :=
  decide ((17 ≤ i.val ∧ i.val < 42) ∨ 46 ≤ i.val)

theorem inputReg_f42_of_false :
    ∀ i : Fin rFib, FibonacciHeap.inputReg i = false → inputReg (f42 i) = false := by
  decide

/-- Static memory footprint on capacity `n_max`: `11 * n_max + 1` words (`9 * n_max + 1` for the
inner Fibonacci heap plus `n_max` for `val` and `n_max` for `freeStack`). -/
def space (n_max : ℕ) : ℕ :=
  11 * n_max + 1

theorem space_eq_fib_add (n_max : ℕ) :
    space n_max = FibonacciHeap.space n_max + n_max + n_max := by
  unfold space FibonacciHeap.space
  omega

theorem space_lower (n_max : ℕ) : n_max + 1 ≤ space n_max := by
  unfold space
  omega

/-- Fresh-initialization instruction bound (`allocSpan` 15 + `initSetup` 18 = 33). -/
def tInit (_n_max : ℕ) : ℕ := 33
/-- Instruction bound for `isEmpty` (including dispatch). -/
def tEmpty (_n_max : ℕ) : ℕ := 12
/-- Instruction bound for `get` (including dispatch and value read). -/
def tGet (_n_max : ℕ) : ℕ := 20
/-- Amortized instruction bound for `insert` (including handle allocation, value write, and `+80`
root potential). -/
def tIns (_n_max : ℕ) : ℕ := 140
/-- Amortized instruction bound for `decreaseKey` (including dispatch and cascading cuts). -/
def tDec (_n_max : ℕ) : ℕ := 340
/-- Amortized instruction bound for `extractMin` (`420 * (Nat.log 2 n + 1)`). -/
def tExt (n : ℕ) : ℕ := 420 * (Nat.log 2 n + 1)

/-- Per-operation amortized instruction charge for the key–value Fibonacci heap, charging
`tExt (MinPQ.size s)` on `.extractMin` in terms of the current number of stored elements
`MinPQ.size s`. -/
def charge (n_max : ℕ) (s : PriorityQueue.MinPQ.State n_max) :
    PriorityQueue.MinPQ.Op n_max → ℕ
  | .isEmpty => tEmpty n_max
  | .get _ => tGet n_max
  | .insert _ _ => tIns n_max
  | .decreaseKey _ _ => tDec n_max
  | .extractMin => tExt (PriorityQueue.MinPQ.size s)

/-- Since `MinPQ.size s ≤ n_max`, `charge n_max s .extractMin ≤ tExt n_max`. -/
theorem charge_extractMin_le_tExt (n_max : ℕ) (s : PriorityQueue.MinPQ.State n_max) :
    charge n_max s .extractMin ≤ tExt n_max := by
  simp only [charge, tExt]
  have hlog : Nat.log 2 (PriorityQueue.MinPQ.size s) ≤ Nat.log 2 n_max :=
    Nat.log_mono_right (PriorityQueue.MinPQ.size_le s)
  omega

/-- Concrete integer potential `80 * (numRoots + 2 * numMarked)` inherited from the inner
Fibonacci heap. -/
def potential (x : Data rMinPQ) : ℕ :=
  FibonacciHeap.potential (x.comap f42)

/-! ## Structured `Basis.exact` subprograms and `subroutineCode` -/

/-- Copy `outerFrontierReg` into `valBaseReg`, run `FibonacciHeap.allocSpan.rename f42` to set
`baseReg = base` and `valBaseReg = base + 9 * n_max + 1`, then advance `freeBaseReg` and
`outerFrontierReg` by `n_max` each (`15` steps total). -/
def allocSpan : Code .exact rMinPQ :=
  ram_exact[
    valBaseReg ← outerFrontierReg;
    ⟪FibonacciHeap.allocSpan.rename f42⟫;
    freeBaseReg ← valBaseReg + nReg;
    outerFrontierReg ← freeBaseReg + nReg
  ]

/-- Initialize `freeBaseReg = outerFrontierReg - nReg`, `valBaseReg = freeBaseReg - nReg`,
`freshReg = 0`, `freeTopReg = 0`, and run `FibonacciHeap.initSetup.rename f42` (`18` steps
total). -/
def initSetup : Code .exact rMinPQ :=
  ram_exact[
    freeBaseReg ← outerFrontierReg - nReg;
    valBaseReg ← freeBaseReg - nReg;
    freshReg ← #0;
    freeTopReg ← #0;
    ⟪FibonacciHeap.initSetup.rename f42⟫
  ]

/-- `isEmpty`: delegates directly to `FibonacciHeap.isEmptyCode.rename f42`. -/
def isEmptyCode : Code .exact rMinPQ :=
  FibonacciHeap.isEmptyCode.rename f42

/-- `get h`: runs `FibonacciHeap.getKeyCode.rename f42` and, when `outFlag ≠ 0`, loads the
satellite value `outValReg ← val[argV]`. -/
def getCode : Code .exact rMinPQ :=
  ram_exact[
    ⟪FibonacciHeap.getKeyCode.rename f42⟫;
    if outFlag = zeroP then [
      s0 ← zeroP
    ] else [
      s0 ← valBaseReg + argV;
      outValReg ← *s0
    ]
  ]

/-- Handle-allocation branch of `insertCode`: pops a recycled handle from
`freeStack[freeTopReg - 1]` when `freeTopReg ≠ 0`, or allocates `freshReg` and increments
`freshReg` when `freeTopReg = 0`. -/
def allocHandleBranch : Code .exact rMinPQ :=
  ram_exact[
    if freeTopReg = zeroP then [
      argV ← freshReg;
      freshReg ← freshReg + oneP
    ] else [
      freeTopReg ← freeTopReg - oneP;
      s0 ← freeBaseReg + freeTopReg;
      argV ← *s0
    ]
  ]

/-- `insert u v`: allocates a handle `argV` from `freeStack` (if `freeTopReg > 0`) or bumps
`freshReg` via `allocHandleBranch`, stores `val[argV] ← inValReg`, runs
`FibonacciHeap.insertCode.rename f42` with key `argK = u`, and outputs `outV ← argV`. -/
def insertCode : Code .exact rMinPQ :=
  ram_exact[
    ⟪allocHandleBranch⟫;
    s0 ← valBaseReg + argV;
    *s0 ← inValReg;
    ⟪FibonacciHeap.insertCode.rename f42⟫;
    outV ← argV
  ]

/-- `decreaseKey h u'`: delegates directly to `FibonacciHeap.decreaseKeyCode.rename f42`. -/
def decreaseKeyCode : Code .exact rMinPQ :=
  FibonacciHeap.decreaseKeyCode.rename f42

/-- `extractMin`: runs `FibonacciHeap.extractMinCode.rename f42` and, when `outFlag ≠ 0`, loads
`outValReg ← val[outV]` and pushes `outV` onto `freeStack[freeTopReg]`. -/
def extractMinCode : Code .exact rMinPQ :=
  ram_exact[
    ⟪FibonacciHeap.extractMinCode.rename f42⟫;
    if outFlag = zeroP then [
      s0 ← zeroP
    ] else [
      s0 ← valBaseReg + outV;
      outValReg ← *s0;
      s0 ← freeBaseReg + freeTopReg;
      *s0 ← outV;
      freeTopReg ← freeTopReg + oneP
    ]
  ]

/-- Unified dispatcher over 1-bit tags `(tag2, tag1, tag0)`. -/
def dispatchCode : Code .exact rMinPQ :=
  ram_exact[
    if tag2 = zeroP then [
      if tag1 = zeroP then [
        if tag0 = zeroP then [
          ⟪isEmptyCode⟫
        ] else [
          ⟪getCode⟫
        ]
      ] else [
        if tag0 = zeroP then [
          ⟪insertCode⟫
        ] else [
          ⟪decreaseKeyCode⟫
        ]
      ]
    ] else [
      ⟪extractMinCode⟫
    ]
  ]

/-- Uniform `SubroutineCode .exact rMinPQ 1` for the key–value Fibonacci heap with handles. -/
def subroutineCode : SubroutineCode .exact rMinPQ 1 where
  allocSpan := allocSpan
  initSetup := initSetup
  code := dispatchCode
  frontierReg := outerFrontierReg
  baseReg := baseReg
  initParams := ![nReg]
  curReg := curReg
  zeroReg := zeroReg
  oneReg := oneReg
  incCur := .exactBin .add curReg curReg oneReg
  input := inputReg
  output := outFlag

/-! ## Calling convention: `encode`, `argMatch`, `decode` -/

/-- Raw register encoding for `PriorityQueue.MinPQ.Op n_max` using 1-bit tags
`(tag2, tag1, tag0)`. -/
def rawEncode {n_max : ℕ} : PriorityQueue.MinPQ.Op n_max → Fin rMinPQ → ℕ
  | .isEmpty => fun _ => 0
  | .get h => fun i => if i = tag0 then 1 else if i = argV then h.val else 0
  | .insert u v => fun i =>
      if i = tag1 then 1 else if i = argK then u else if i = inValReg then v else 0
  | .decreaseKey h u' => fun i =>
      if i = tag1 then 1 else if i = tag0 then 1
      else if i = argV then h.val else if i = argK then u' else 0
  | .extractMin => fun i => if i = tag2 then 1 else 0

/-- Register encoding for `PriorityQueue.MinPQ.Op n_max` bounded by `U` on `decreaseKey`
so `arguments_fit` holds on arbitrary states; coincides with `rawEncode` on every operation
valid in a represented state (`encode_eq_rawEncode_of_rep`). -/
def encode {n_max : ℕ} (U : ℕ) : PriorityQueue.MinPQ.Op n_max → Fin rMinPQ → ℕ
  | .decreaseKey h u' => fun i =>
      if i = tag1 then 1 else if i = tag0 then 1
      else if i = argV then h.val else if i = argK then (if u' < U then u' else 0) else 0
  | o => rawEncode o

/-- Standard argument-matching predicate for `PriorityQueue.MinPQ.Op n_max`. -/
def rawArgMatch {n_max : ℕ} : PriorityQueue.MinPQ.Op n_max → (Fin rMinPQ → ℕ) → Prop
  | .isEmpty => fun regs => regs tag2 = 0 ∧ regs tag1 = 0 ∧ regs tag0 = 0
  | .get h => fun regs =>
      regs tag2 = 0 ∧ regs tag1 = 0 ∧ regs tag0 ≠ 0 ∧ regs argV = h.val
  | .insert u v => fun regs =>
      regs tag2 = 0 ∧ regs tag1 ≠ 0 ∧ regs tag0 = 0 ∧ regs argK = u ∧ regs inValReg = v
  | .decreaseKey h u' => fun regs =>
      regs tag2 = 0 ∧ regs tag1 ≠ 0 ∧ regs tag0 ≠ 0 ∧ regs argV = h.val ∧ regs argK = u'
  | .extractMin => fun regs => regs tag2 ≠ 0

/-- Argument-matching predicate paired with `encode U` for `WordRAM.StateTransitionImpl`. -/
def argMatch {n_max : ℕ} (U : ℕ) : PriorityQueue.MinPQ.Op n_max → (Fin rMinPQ → ℕ) → Prop
  | .decreaseKey h u' => fun regs =>
      regs tag2 = 0 ∧ regs tag1 ≠ 0 ∧ regs tag0 ≠ 0 ∧ regs argV = h.val ∧
        regs argK = (if u' < U then u' else 0)
  | o => rawArgMatch o

/-- Output decoder for `minPQSpec n_max U V`. -/
def decode {n_max U V : ℕ} :
    (o : (minPQSpec n_max U V).Op) → (Fin rMinPQ → ℕ) →
      Option ((minPQSpec n_max U V).Result o)
  | .isEmpty, regs => some (decide (regs outFlag ≠ 0))
  | .get _, regs =>
      if regs outFlag = 0 then some none else some (some (regs outK, regs outValReg))
  | .insert _ _, regs =>
      if h : regs outV < n_max then some (some ⟨regs outV, h⟩) else none
  | .decreaseKey _ _, _ => some ()
  | .extractMin, regs =>
      if regs outFlag = 0 then some none
      else if h : regs outV < n_max then some (some (regs outK, regs outValReg, ⟨regs outV, h⟩))
      else none

theorem arguments_fit {n_max U V w base : ℕ}
    (hS : Fits w (base + space n_max)) (hU : Fits w U) (hV : Fits w V)
    {s : PriorityQueue.MinPQ.State n_max} (o : PriorityQueue.MinPQ.Op n_max)
    (hv : (minPQSpec n_max U V).valid s o) (i : Fin rMinPQ) :
    Fits w (encode U o i) := by
  have hsp := space_lower n_max
  have h0 : Fits w 0 := hS.of_le (Nat.zero_le _)
  have h1 : Fits w 1 := hS.of_le (by omega)
  cases o with
  | isEmpty => exact h0
  | get h =>
    simp only [encode, rawEncode]; split_ifs
    · exact h1
    · exact hS.of_le (by have := h.isLt; omega)
    · exact h0
  | insert u v =>
    obtain ⟨_, hu, hv_lt⟩ := hv
    simp only [encode, rawEncode]; split_ifs
    · exact h1
    · exact hU.of_le hu.le
    · exact hV.of_le hv_lt.le
    · exact h0
  | decreaseKey h u' =>
    simp only [encode]; split_ifs with _ _ _ _ hu'
    · exact h1
    · exact h1
    · exact hS.of_le (by have := h.isLt; omega)
    · exact hU.of_le hu'.le
    · exact h0
    · exact h0
  | extractMin =>
    simp only [encode, rawEncode]; split_ifs <;> [exact h1; exact h0]

private theorem argMatch_of_eq_encode {n_max U : ℕ} (o : PriorityQueue.MinPQ.Op n_max)
    {f : Fin rMinPQ → ℕ}
    (h2 : f tag2 = encode U o tag2) (h1 : f tag1 = encode U o tag1)
    (h0 : f tag0 = encode U o tag0) (hv : f argV = encode U o argV)
    (hk : f argK = encode U o argK) (hval : f inValReg = encode U o inValReg) :
    argMatch U o f := by
  cases o with
  | isEmpty => exact ⟨h2, h1, h0⟩
  | get _ => exact ⟨h2, h1, ne_of_eq_of_ne h0 Nat.one_ne_zero, hv⟩
  | insert _ _ => exact ⟨h2, ne_of_eq_of_ne h1 Nat.one_ne_zero, h0, hk, hval⟩
  | decreaseKey _ _ =>
    exact ⟨h2, ne_of_eq_of_ne h1 Nat.one_ne_zero, ne_of_eq_of_ne h0 Nat.one_ne_zero, hv, hk⟩
  | extractMin => exact ne_of_eq_of_ne h2 Nat.one_ne_zero

theorem encode_matches {n_max U : ℕ} (o : PriorityQueue.MinPQ.Op n_max)
    (regs : Fin rMinPQ → ℕ) :
    argMatch U o (fun i => if subroutineCode.input i then encode U o i else regs i) :=
  argMatch_of_eq_encode o rfl rfl rfl rfl rfl rfl


/-! ## Representation invariant (`AllocRep`, `Rep`) and framing lemmas -/

/-- Full machine-state representation invariant for an internal allocator state
`s : PriorityQueue.MinPQ.AllocState n_max`. -/
def AllocRep (n_max U V w base : ℕ) (s : PriorityQueue.MinPQ.AllocState n_max)
    (x : Data rMinPQ) : Prop :=
  x.Bounded w ∧
  FibonacciHeap.FibInv n_max U w base (PriorityQueue.MinPQ.toIndexed s.entries)
    (x.comap f42) ∧
  s.WellFormed ∧
  x.regs outerFrontierReg = base + space n_max ∧
  x.regs freeBaseReg = base + FibonacciHeap.space n_max + n_max ∧
  x.regs freshReg = s.fresh ∧
  x.regs freeTopReg = s.freeList.length ∧
  (∀ (h : Fin n_max) (u v : ℕ), s.entries h = some (u, v) →
    u < U ∧ v < V ∧ x.mem (base + FibonacciHeap.space n_max + h.val) = v) ∧
  (∀ (i : ℕ) (hi : i < s.freeList.length),
    x.mem (base + FibonacciHeap.space n_max + n_max + (s.freeList.length - 1 - i)) =
      (s.freeList[i]).val)

/-- Existential relational representation invariant over abstract state
`e : PriorityQueue.MinPQ.State n_max`. -/
def Rep (n_max U V w base : ℕ) (e : PriorityQueue.MinPQ.State n_max)
    (x : Data rMinPQ) : Prop :=
  ∃ s : PriorityQueue.MinPQ.AllocState n_max,
    s.entries = e ∧ AllocRep n_max U V w base s x

theorem owns_val_addr {n_max base idx : ℕ} (hidx : idx < n_max) :
    (Block.mk base (space n_max)).Owns (base + FibonacciHeap.space n_max + idx) := by
  dsimp only [Block.Owns, space, FibonacciHeap.space]
  omega

theorem owns_free_addr {n_max base idx : ℕ} (hidx : idx < n_max) :
    (Block.mk base (space n_max)).Owns (base + FibonacciHeap.space n_max + n_max + idx) := by
  dsimp only [Block.Owns, space, FibonacciHeap.space]
  omega

theorem notMem_fib_footprint_of_ge {n_max base a : ℕ} (ha : base + FibonacciHeap.space n_max ≤ a) :
    a ∉ (Block.mk base (FibonacciHeap.space n_max)).footprint := by
  rw [Block.mem_footprint, Block.Owns]
  dsimp only
  omega

theorem fib_footprint_subset {n_max base : ℕ} :
    (Block.mk base (FibonacciHeap.space n_max)).footprint ⊆
      (Block.mk base (space n_max)).footprint := by
  intro a ha
  rw [Block.mem_footprint, Block.Owns] at ha ⊢
  dsimp only [space, FibonacciHeap.space] at ha ⊢
  omega

theorem modifies_of_fib {n_max base : ℕ} {m₁ m₂ : ℕ → ℕ}
    (h : Modifies (Block.mk base (FibonacciHeap.space n_max)).footprint m₁ m₂) :
    Modifies (Block.mk base (space n_max)).footprint m₁ m₂ :=
  fun a ha => h a fun ha' => ha (fib_footprint_subset ha')

theorem AllocRep.supported {n_max U V w base : ℕ}
    {s : PriorityQueue.MinPQ.AllocState n_max} {x x' : Data rMinPQ}
    (hreg : ∀ i : Fin rMinPQ, inputReg i = false → x'.regs i = x.regs i)
    (hmem : ∀ a ∈ (Block.mk base (space n_max)).footprint, x'.mem a = x.mem a)
    (hb' : x'.Bounded w) (h : AllocRep n_max U V w base s x) :
    AllocRep n_max U V w base s x' := by
  obtain ⟨_, hfib, hwf, hfr, hfb, hfresh, htop, hval, hfree⟩ := h
  have ⟨hwf_le, _, _, _, hwf_sum⟩ := hwf
  refine ⟨hb',
    (FibonacciHeap.FibInv.supported (x := x.comap f42) (x' := x'.comap f42)
      (fun j hj => hreg (f42 j) (inputReg_f42_of_false j hj))
      (fun a ha => hmem a (fib_footprint_subset ha)) (hb'.comap f42) hfib),
    hwf,
    (hreg outerFrontierReg (by decide)).trans hfr,
    (hreg freeBaseReg (by decide)).trans hfb,
    (hreg freshReg (by decide)).trans hfresh,
    (hreg freeTopReg (by decide)).trans htop,
    fun h u v hsh => by
      obtain ⟨hu, hv, hm⟩ := hval h u v hsh
      exact ⟨hu, hv, (hmem _ (Block.mem_footprint.mpr (owns_val_addr h.isLt))).trans hm⟩,
    fun i hi => by
      have hlt : s.freeList.length - 1 - i < n_max := by omega
      exact (hmem _ (Block.mem_footprint.mpr (owns_free_addr hlt))).trans (hfree i hi)⟩

theorem Rep.supported {n_max U V w base : ℕ}
    {e : PriorityQueue.MinPQ.State n_max} {x x' : Data rMinPQ}
    (hreg : ∀ i : Fin rMinPQ, inputReg i = false → x'.regs i = x.regs i)
    (hmem : ∀ a ∈ (Block.mk base (space n_max)).footprint, x'.mem a = x.mem a)
    (hb' : x'.Bounded w) (h : Rep n_max U V w base e x) :
    Rep n_max U V w base e x' := by
  obtain ⟨s, rfl, hs⟩ := h
  exact ⟨s, rfl, hs.supported hreg hmem hb'⟩

theorem potential_supported {x x' : Data rMinPQ}
    (hreg : ∀ i : Fin rMinPQ, inputReg i = false → x'.regs i = x.regs i) :
    potential x' = potential x :=
  FibonacciHeap.potential_supported fun j hj => hreg (f42 j) (inputReg_f42_of_false j hj)

private theorem potential_extend (y_fib : Data rFib) (x : Data rMinPQ) :
    potential (y_fib.extend f42 x) = FibonacciHeap.potential y_fib := by
  unfold potential; rw [Data.comap_extend f42_injective]

private theorem regs_set_of_inputReg {x : Data rMinPQ} {r : Fin rMinPQ}
    (hr : inputReg r = true) (v : ℕ) :
    ∀ i : Fin rMinPQ, inputReg i = false → (x.set r v).regs i = x.regs i :=
  fun i hi => Data.set_regs_of_ne (by rintro rfl; cases hr.symm.trans hi) v

private theorem AllocRep.key_lt_of_entries {n_max U V w base : ℕ}
    {s : PriorityQueue.MinPQ.AllocState n_max} {x : Data rMinPQ}
    (hrep : AllocRep n_max U V w base s x) {h : Fin n_max} {u' : ℕ}
    (hv : (minPQSpec n_max U V).valid s.entries (.decreaseKey h u')) : u' < U := by
  obtain ⟨_, _, _, _, _, _, _, hval, _⟩ := hrep
  obtain ⟨u, v, hsh, hu'⟩ := hv
  exact Nat.lt_of_le_of_lt hu' (hval h u v hsh).1

theorem rawArgMatch_of_argMatch {n_max U V w base : ℕ}
    {s : PriorityQueue.MinPQ.AllocState n_max} {x : Data rMinPQ}
    {o : PriorityQueue.MinPQ.Op n_max}
    (hrep : AllocRep n_max U V w base s x)
    (hv : (minPQSpec n_max U V).valid s.entries o)
    (harg : argMatch U o x.regs) :
    rawArgMatch o x.regs := by
  cases o with
  | isEmpty | get _ | insert _ _ | extractMin => exact harg
  | decreaseKey h u' =>
    have hu'_lt := hrep.key_lt_of_entries hv
    simp only [argMatch, hu'_lt, ↓reduceIte] at harg; exact harg

theorem encode_eq_rawEncode_of_rep {n_max U V w base : ℕ}
    {e : PriorityQueue.MinPQ.State n_max} {x : Data rMinPQ}
    {o : PriorityQueue.MinPQ.Op n_max}
    (hr : Rep n_max U V w base e x)
    (hv : (minPQSpec n_max U V).valid e o) :
    encode U o = rawEncode o := by
  cases o with
  | isEmpty | get _ | insert _ _ | extractMin => rfl
  | decreaseKey h u' =>
    obtain ⟨s, rfl, hrep⟩ := hr
    funext i; simp only [encode, rawEncode, hrep.key_lt_of_entries hv, ↓reduceIte]

/-! ## Initialization: `incCur_eval`, `allocSpan_exec`, `initSetup_exec` -/

theorem incCur_eval {w : ℕ} {x : Data rMinPQ} (h1 : x.regs oneReg = 1)
    (hfit : Fits w (x.regs curReg + 1)) :
    (Op.exactBin .add curReg curReg oneReg).eval w x =
      some (x.set curReg (x.regs curReg + 1)) := by
  rw [Op.eval_exactBin]
  simp only [BinOp.evalExact, h1, Option.bind_some]
  exact Data.put_of_fits hfit

@[local wram_simps] private theorem fib_reg_numerals :
    (0 : Fin rFib) = FibonacciHeap.nReg ∧
    (1 : Fin rFib) = FibonacciHeap.frontierReg ∧
    (2 : Fin rFib) = FibonacciHeap.baseReg ∧
    (11 : Fin rFib) = FibonacciHeap.zeroP ∧
    (12 : Fin rFib) = FibonacciHeap.oneP ∧
    (20 : Fin rFib) = FibonacciHeap.argV ∧
    (21 : Fin rFib) = FibonacciHeap.argK ∧
    (22 : Fin rFib) = FibonacciHeap.outFlag ∧
    (23 : Fin rFib) = FibonacciHeap.outV ∧
    (24 : Fin rFib) = FibonacciHeap.outK ∧
    f42 FibonacciHeap.nReg = nReg ∧
    f42 FibonacciHeap.frontierReg = valBaseReg ∧
    f42 FibonacciHeap.baseReg = baseReg ∧
    f42 FibonacciHeap.argV = argV ∧
    f42 FibonacciHeap.argK = argK := by decide

theorem allocSpan_exec {n_max w base : ℕ} (hS : Fits w (base + space n_max))
    {x : Data rMinPQ} (hx : x.Bounded w) (hfr : x.regs outerFrontierReg = base)
    (hpar : ∀ j : Fin 1, x.regs (![nReg] j) = ![n_max] j) :
    ∃ x₁, ExecWithin w allocSpan x x₁ 15 ∧ x₁.mem = x.mem ∧
      x₁.regs baseReg = base ∧ x₁.regs outerFrontierReg = base + space n_max ∧
      (∀ j : Fin 1, x₁.regs (![nReg] j) = ![n_max] j) := by
  have hn : x.regs nReg = n_max := hpar 0
  have hsp := space_eq_fib_add n_max
  have hfit (v : ℕ) (hv : v ≤ base + (FibonacciHeap.space n_max + n_max + n_max)) : Fits w v :=
    hS.of_le (by omega)
  refine WP.exists_execWithin ?_
  unfold allocSpan; wram_exec [hfr]
  wram_call (FibonacciHeap.allocSpan_exec
      (show Fits w (base + FibonacciHeap.space n_max) from hfit _ (by omega))
      ((show (x.set valBaseReg base).Bounded w by wram_bounded; exact hfit _ (by omega)).comap f42)
      (by wram_simp) (fun j => by rw [Subsingleton.elim j 0]; wram_simp [hn]))
    canonical f42_injective with y_fib ⟨hm_fib, hb_fib, hfr_fib, hpar_fib⟩
  have hn_fib : y_fib.regs FibonacciHeap.nReg = n_max := hpar_fib 0
  wram_exec [hfit, hfr_fib, hn_fib]
  exact ⟨hm_fib, by wram_simp [hb_fib], by wram_simp [hsp]; omega,
    fun j => by rw [Subsingleton.elim j 0]; wram_simp [hn_fib]⟩

theorem initSetup_exec {n_max U V w base : ℕ} {x₁ : Data rMinPQ}
    (hx₁ : x₁.Bounded w) (hb₁ : x₁.regs baseReg = base)
    (hfr₁ : x₁.regs outerFrontierReg = base + space n_max)
    (hpar₁ : ∀ j : Fin 1, x₁.regs (![nReg] j) = ![n_max] j)
    (hz : ∀ a ∈ (Block.mk base (space n_max)).footprint, x₁.mem a = 0) :
    ∃ y, ExecWithin w initSetup x₁ y 18 ∧ y.regs outerFrontierReg = base + space n_max ∧
      Rep n_max U V w base (PriorityQueue.MinPQ.empty n_max) y ∧ potential y ≤ 0 ∧
      Modifies (Block.mk base (space n_max)).footprint x₁.mem y.mem := by
  have hn : x₁.regs nReg = n_max := hpar₁ 0
  have hS : Fits w (base + space n_max) := hfr₁ ▸ hx₁.1 outerFrontierReg
  have hsp := space_eq_fib_add n_max
  have hfit (v : ℕ) (hv : v ≤ base + (FibonacciHeap.space n_max + n_max + n_max)) : Fits w v :=
    hS.of_le (by omega)
  refine WP.exists_execWithin (WP.bounded hx₁ ?_)
  unfold initSetup
  wram_exec [hfit, hfr₁, hn, hsp]
  wram_call (FibonacciHeap.initSetup_exec (K_max := U)
      ((show Data.Bounded w _ by wram_bounded <;> exact hfit _ (by omega)).comap f42)
      (by wram_simp [hb₁]) (by wram_simp; omega)
      (fun j => by rw [Subsingleton.elim j 0]; wram_simp [hn])
      (fun a ha => hz a (fib_footprint_subset ha)))
    canonical f42_injective with y_fib ⟨_, hinv_fib, hpot_fib, hmod_fib⟩
  intro hby
  refine ⟨by omega, by wram_simp [hfr₁],
    ⟨PriorityQueue.MinPQ.AllocState.empty n_max, rfl, hby, ?_,
      PriorityQueue.MinPQ.AllocState.wellFormed_empty n_max, by wram_simp [hfr₁],
      by wram_simp; omega, by wram_simp; rfl, by wram_simp; rfl,
      by rintro _ _ _ ⟨⟩, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩,
    ?_, modifies_of_fib hmod_fib⟩
  · rw [Data.comap_extend f42_injective]; exact hinv_fib
  · rw [potential_extend]; exact hpot_fib

/-! ## Operation specifications: `isEmptyCode`, `getCode`, `insertCode` -/

theorem AllocRep.fits_stop {n_max U V w base : ℕ}
    {s : PriorityQueue.MinPQ.AllocState n_max} {x : Data rMinPQ}
    (hrep : AllocRep n_max U V w base s x) : Fits w (base + space n_max) := by
  obtain ⟨hb, _, _, hfr, _⟩ := hrep; exact hfr ▸ hb.1 outerFrontierReg

theorem AllocRep.valBase_eq {n_max U V w base : ℕ}
    {s : PriorityQueue.MinPQ.AllocState n_max} {x : Data rMinPQ}
    (hrep : AllocRep n_max U V w base s x) :
    x.regs valBaseReg = base + FibonacciHeap.space n_max :=
  hrep.2.1.2.1.regs_frontierReg

theorem AllocRep.zeroP_eq {n_max U V w base : ℕ}
    {s : PriorityQueue.MinPQ.AllocState n_max} {x : Data rMinPQ}
    (hrep : AllocRep n_max U V w base s x) : x.regs zeroP = 0 :=
  hrep.2.1.2.1.regs_zeroP

theorem AllocRep.oneP_eq {n_max U V w base : ℕ}
    {s : PriorityQueue.MinPQ.AllocState n_max} {x : Data rMinPQ}
    (hrep : AllocRep n_max U V w base s x) : x.regs oneP = 1 :=
  hrep.2.1.2.1.regs_oneP

private theorem AllocRep.extend_unchanged {n_max U V w base : ℕ}
    {s : PriorityQueue.MinPQ.AllocState n_max} {x : Data rMinPQ} {y_fib : Data rFib}
    (hrep : AllocRep n_max U V w base s x) (hby : (y_fib.extend f42 x).Bounded w)
    (hinv : FibonacciHeap.FibInv n_max U w base (PriorityQueue.MinPQ.toIndexed s.entries) y_fib)
    (hmod : Modifies (Block.mk base (FibonacciHeap.space n_max)).footprint x.mem y_fib.mem) :
    AllocRep n_max U V w base s (y_fib.extend f42 x) := by
  obtain ⟨_, _, hwf, hfr, hfb, hfresh, htop, hval, hfree⟩ := hrep
  have hmem_ge a (ha : base + FibonacciHeap.space n_max ≤ a) :
      (y_fib.extend f42 x).mem a = x.mem a := hmod a (notMem_fib_footprint_of_ge ha)
  refine ⟨hby, by rw [Data.comap_extend f42_injective]; exact hinv, hwf,
    by wram_simp [hfr], by wram_simp [hfb], by wram_simp [hfresh], by wram_simp [htop],
    fun h u v hsh => ⟨(hval h u v hsh).1, (hval h u v hsh).2.1,
      (hmem_ge _ (Nat.le_add_right _ _)).trans (hval h u v hsh).2.2⟩,
    fun i hi => (hmem_ge _ (by omega)).trans (hfree i hi)⟩

theorem isEmptyCode_exec {n_max U V w base : ℕ}
    {s : PriorityQueue.MinPQ.AllocState n_max} {x : Data rMinPQ}
    (hrep : AllocRep n_max U V w base s x) :
    ∃ y t, ExecWithin w isEmptyCode x y t ∧
      decode (n_max := n_max) (U := U) (V := V) .isEmpty y.regs =
        some (PriorityQueue.MinPQ.stepAlloc s .isEmpty).2 ∧
      AllocRep n_max U V w base (PriorityQueue.MinPQ.stepAlloc s .isEmpty).1 y ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem y.mem ∧
      t + potential y ≤ 3 + potential x := by
  obtain ⟨y_fib, t, he_fib, hdec_fib, hinv_fib, hmod_fib, hpot_fib⟩ :=
    FibonacciHeap.isEmptyCode_exec hrep.2.1
  have he := he_fib.rename f42_injective
  simp only [PQCode.decode, FibonacciHeap.code, PriorityQueue.MinPQ.dom_toIndexed,
    indexedMinPQSpec] at hdec_fib hinv_fib
  exact ⟨y_fib.extend f42 x, t, he,
    by wram_simp [decode, PriorityQueue.MinPQ.stepAlloc]; exact hdec_fib,
    hrep.extend_unchanged (he.bounded hrep.1) hinv_fib hmod_fib, modifies_of_fib hmod_fib,
    by rw [potential_extend]; exact hpot_fib⟩

theorem getCode_exec {n_max U V w base : ℕ}
    {s : PriorityQueue.MinPQ.AllocState n_max} {x : Data rMinPQ}
    (h : Fin n_max) (hrep : AllocRep n_max U V w base s x) (hv_reg : x.regs argV = h.val) :
    ∃ y t, ExecWithin w getCode x y t ∧
      decode (n_max := n_max) (U := U) (V := V) (.get h) y.regs =
        some (PriorityQueue.MinPQ.stepAlloc s (.get h)).2 ∧
      AllocRep n_max U V w base (PriorityQueue.MinPQ.stepAlloc s (.get h)).1 y ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem y.mem ∧
      t + potential y ≤ 11 + potential x := by
  have hS := hrep.fits_stop
  have hsp := space_eq_fib_add n_max
  obtain ⟨y_fib, t1, he_fib, hdec_fib, hinv_fib, hmod_fib, hpot_fib⟩ :=
    FibonacciHeap.getKeyCode_exec h hrep.2.1 hv_reg
  simp only [PQCode.decode, FibonacciHeap.code, PriorityQueue.MinPQ.toIndexed_apply,
    indexedMinPQSpec] at hdec_fib hinv_fib
  have hrep1 := hrep.extend_unchanged ((he_fib.rename f42_injective).bounded hrep.1)
    hinv_fib hmod_fib
  have hy_v : y_fib.regs FibonacciHeap.argV = h.val := (he_fib.regs_eq (by decide)).trans hv_reg
  have hfinish {y : Data rMinPQ} {t₂ : ℕ} (ht : t₂ ≤ 4) (hby : y.Bounded w)
      (hreg_y : ∀ i : Fin rMinPQ, inputReg i = false → y.regs i = (y_fib.extend f42 x).regs i)
      (hmem_y : y.mem = (y_fib.extend f42 x).mem)
      (hdec_y : decode (n_max := n_max) (U := U) (V := V) (.get h) y.regs =
        some (PriorityQueue.MinPQ.stepAlloc s (.get h)).2) :
      decode (n_max := n_max) (U := U) (V := V) (.get h) y.regs =
        some (PriorityQueue.MinPQ.stepAlloc s (.get h)).2 ∧
      AllocRep n_max U V w base (PriorityQueue.MinPQ.stepAlloc s (.get h)).1 y ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem y.mem ∧
      (t₂ + t1) + potential y ≤ 11 + potential x :=
    ⟨hdec_y, hrep1.supported hreg_y (fun a _ => congrFun hmem_y a) hby,
      hmem_y ▸ modifies_of_fib hmod_fib, by
        rw [potential_supported hreg_y, potential_extend]
        change t1 + FibonacciHeap.potential y_fib ≤ 7 + potential x at hpot_fib; omega⟩
  change WP w getCode x fun y t => _
  unfold getCode
  refine WP.seq (WP.of_execWithin (he_fib.rename f42_injective) (WP.bounded hrep1.1 ?_))
  cases hsh : s.entries h with
  | none =>
    simp only [hsh, Option.map_none] at hdec_fib
    have hfl0 : y_fib.regs FibonacciHeap.outFlag = 0 := by
      by_contra hne; simp only [hne, ↓reduceIte] at hdec_fib; nomatch hdec_fib
    wram_exec [hinv_fib.2.1.regs_zeroP, hfl0]
    intro hby
    exact hfinish (by omega) hby (regs_set_of_inputReg (by decide) _) rfl
      (by wram_simp [decode, PriorityQueue.MinPQ.stepAlloc, hsh, hfl0]; rfl)
  | some uv =>
    rcases uv with ⟨u, v⟩
    simp only [hsh, Option.map_some] at hdec_fib
    have hfl_ne : y_fib.regs FibonacciHeap.outFlag ≠ 0 := by
      intro h0; simp only [h0, ↓reduceIte] at hdec_fib; nomatch hdec_fib
    have hok_eq : y_fib.regs FibonacciHeap.outK = u := by
      simp only [hfl_ne, ↓reduceIte] at hdec_fib; exact Option.some.inj (Option.some.inj hdec_fib)
    obtain ⟨_, _, _, _, _, _, _, hval1, _⟩ := hrep1
    have hh_lt := h.isLt
    have hm_v : y_fib.mem (base + FibonacciHeap.space n_max + h.val) = v := (hval1 h u v hsh).2.2
    wram_exec [hinv_fib.2.1.regs_zeroP, hinv_fib.2.1.regs_frontierReg, hy_v, hm_v, hfl_ne]
    intro hby
    exact hfinish (by omega) hby
      (fun i hi => (regs_set_of_inputReg (r := outValReg) (by decide) _ i hi).trans
        (regs_set_of_inputReg (r := s0) (by decide) _ i hi)) rfl
      (by wram_simp [decode, PriorityQueue.MinPQ.stepAlloc, hsh, hfl_ne, hok_eq]; rfl)

private theorem allocHandleBranch_exec {n_max U V w base u v : ℕ}
    {s : PriorityQueue.MinPQ.AllocState n_max} {x : Data rMinPQ}
    (hrep : AllocRep n_max U V w base s x)
    (hsz : PriorityQueue.MinPQ.size s.entries < n_max) :
    ∃ h freeList' fresh' x1,
      PriorityQueue.MinPQ.allocHandle s = some (h, freeList', fresh') ∧
      s.entries h = none ∧
      (PriorityQueue.MinPQ.AllocState.mk
        (Function.update s.entries h (some (u, v))) freeList' fresh').WellFormed ∧
      ExecWithin w allocHandleBranch x x1 5 ∧
      x1.Bounded w ∧ x1.mem = x.mem ∧ x1.regs argV = h.val ∧
      x1.regs freshReg = fresh' ∧ x1.regs freeTopReg = freeList'.length ∧
      (∀ i : Fin rMinPQ, i ≠ argV → i ≠ freshReg → i ≠ freeTopReg → i ≠ s0 →
        x1.regs i = x.regs i) ∧
      (∀ (i : ℕ) (hi : i < freeList'.length),
        x.mem (base + FibonacciHeap.space n_max + n_max + (freeList'.length - 1 - i)) =
          (freeList'[i]).val) := by
  have hfit_stop := hrep.fits_stop
  have hz0 := hrep.zeroP_eq
  have ho1 := hrep.oneP_eq
  obtain ⟨hb, _, hwf, _, hfb, hfresh, htop, _, hfree⟩ := hrep
  have ⟨hwf_le, _, _, _, hwf_sum⟩ := hwf
  obtain ⟨h, freeList', fresh', halloc, hh_none, hwf'⟩ :=
    PriorityQueue.MinPQ.allocHandle_spec hwf hsz u v
  refine ⟨h, freeList', fresh', ?_⟩
  rcases hfl : s.freeList with _ | ⟨hd, tl⟩
  · have hfr_lt : s.fresh < n_max := by rw [hfl, List.length_nil, Nat.add_zero] at hwf_sum; omega
    have halloc_eq := halloc
    simp only [PriorityQueue.MinPQ.allocHandle, hfl, hfr_lt, ↓reduceDIte,
      Option.some.injEq, Prod.mk.injEq] at halloc
    obtain ⟨rfl, rfl, rfl⟩ := halloc
    have hsp := space_lower n_max
    suffices ∃ x1, ExecWithin w allocHandleBranch x x1 5 ∧
        x1.Bounded w ∧ x1.mem = x.mem ∧ x1.regs argV = s.fresh ∧
        x1.regs freshReg = s.fresh + 1 ∧ x1.regs freeTopReg = 0 ∧
        (∀ i : Fin rMinPQ, i ≠ argV → i ≠ freshReg → i ≠ freeTopReg → i ≠ s0 →
          x1.regs i = x.regs i) by
      obtain ⟨x1, he, hreg⟩ := this
      exact ⟨x1, halloc_eq, hh_none, hwf', he, hreg.1, hreg.2.1, hreg.2.2.1, hreg.2.2.2.1,
        hreg.2.2.2.2.1, hreg.2.2.2.2.2, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
    refine WP.exists_execWithin (WP.bounded hb ?_); unfold allocHandleBranch
    wram_exec [htop, hfl, List.length_nil, hz0, hfresh, ho1]; intro hb1
    exact ⟨by omega, hb1, rfl, by wram_simp, by wram_simp, by wram_simp [htop, hfl]; rfl,
      fun i h1 h2 _ _ => by wram_simp [h1, h2]⟩
  · have halloc_eq := halloc
    simp only [PriorityQueue.MinPQ.allocHandle, hfl, Option.some.injEq, Prod.mk.injEq] at halloc
    obtain ⟨rfl, rfl, rfl⟩ := halloc
    have htop_eq : x.regs freeTopReg = tl.length + 1 := by rw [htop, hfl, List.length_cons]
    have htl_lt : tl.length < n_max := by rw [hfl, List.length_cons] at hwf_sum; omega
    have hm_top : x.mem (base + FibonacciHeap.space n_max + n_max + tl.length) = hd.val := by
      simpa only [hfl, List.length_cons, Nat.add_sub_cancel, Nat.sub_zero,
        List.getElem_cons_zero] using hfree 0 (by simp only [hfl, List.length_cons]; omega)
    have hsp := space_eq_fib_add n_max
    have hfit (val : ℕ) (hv : val ≤ base + (FibonacciHeap.space n_max + n_max + n_max)) :
        Fits w val := hfit_stop.of_le (by omega)
    suffices ∃ x1, ExecWithin w allocHandleBranch x x1 5 ∧
        x1.Bounded w ∧ x1.mem = x.mem ∧ x1.regs argV = hd.val ∧
        x1.regs freshReg = s.fresh ∧ x1.regs freeTopReg = tl.length ∧
        (∀ i : Fin rMinPQ, i ≠ argV → i ≠ freshReg → i ≠ freeTopReg → i ≠ s0 →
          x1.regs i = x.regs i) by
      obtain ⟨x1, he, hreg⟩ := this
      refine ⟨x1, halloc_eq, hh_none, hwf', he, hreg.1, hreg.2.1, hreg.2.2.1, hreg.2.2.2.1,
        hreg.2.2.2.2.1, hreg.2.2.2.2.2, fun i hi => ?_⟩
      simpa only [hfl, List.length_cons, List.getElem_cons_succ,
        show tl.length + 1 - 1 - (i + 1) = tl.length - 1 - i by omega] using
        hfree (i + 1) (by simp only [hfl, List.length_cons]; omega)
    refine WP.exists_execWithin (WP.bounded hb ?_); unfold allocHandleBranch
    wram_exec [hfit, htop_eq, hz0, ho1, hfb, hm_top]; intro hb1
    exact ⟨by omega, hb1, rfl, by wram_simp, by wram_simp [hfresh], by wram_simp,
      fun i h1 _ h3 h4 => by wram_simp [h1, h3, h4]⟩

theorem insertCode_exec {n_max U V w base u v : ℕ}
    {s : PriorityQueue.MinPQ.AllocState n_max} {x : Data rMinPQ}
    (hrep : AllocRep n_max U V w base s x)
    (hv : (minPQSpec n_max U V).valid s.entries (.insert u v))
    (hk_reg : x.regs argK = u) (hval_reg : x.regs inValReg = v) :
    ∃ y t, ExecWithin w insertCode x y t ∧
      decode (n_max := n_max) (U := U) (V := V) (.insert u v) y.regs =
        some (PriorityQueue.MinPQ.stepAlloc s (.insert u v)).2 ∧
      AllocRep n_max U V w base (PriorityQueue.MinPQ.stepAlloc s (.insert u v)).1 y ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem y.mem ∧
      t + potential y ≤ 129 + potential x := by
  have hfit_stop := hrep.fits_stop
  have hsp := space_eq_fib_add n_max
  have ⟨hb, hfib, _, hfr, hfb, _, _, hval, _⟩ := hrep
  obtain ⟨hsz, hu_lt, hv_lt⟩ := hv
  obtain ⟨h, freeList', fresh', x1, halloc, hh_none, hwf', he_alloc, hb1, hm1,
    hx1_v, hx1_fresh, hx1_top, hx1_regs, hfree'⟩ :=
    allocHandleBranch_exec (u := u) (v := v) hrep hsz
  have hh_lt := h.isLt
  have hfit (val : ℕ) (hv : val ≤ base + (FibonacciHeap.space n_max + n_max + n_max)) :
      Fits w val := hfit_stop.of_le (by omega)
  have hx1_vb : x1.regs valBaseReg = base + FibonacciHeap.space n_max :=
    (hx1_regs valBaseReg (by decide) (by decide) (by decide) (by decide)).trans hrep.valBase_eq
  have hx1_inVal : x1.regs inValReg = v :=
    (hx1_regs inValReg (by decide) (by decide) (by decide) (by decide)).trans hval_reg
  have hx1_k : x1.regs argK = u :=
    (hx1_regs argK (by decide) (by decide) (by decide) (by decide)).trans hk_reg
  change WP w insertCode x fun y t => _
  unfold insertCode
  wram_call he_alloc
  wram_exec [hfit, hx1_vb, hx1_v, hx1_inVal]
  let x2 := (x1.set s0 (base + FibonacciHeap.space n_max + h.val)).write
    (base + FibonacciHeap.space n_max + h.val) v
  have hb2 : x2.Bounded w := by
    dsimp only [x2]; have : Fits w v := hval_reg ▸ hb.1 inValReg
    wram_bounded; exact hfit_stop.of_le (by omega)
  have hreg2 : ∀ j : Fin rFib, FibonacciHeap.inputReg j = false →
      (x2.comap f42).regs j = (x.comap f42).regs j := fun j hj => by
    have hj_in := inputReg_f42_of_false j hj
    have h1 : f42 j ≠ argV := fun e => by rw [e] at hj_in; cases hj_in
    have h2 : f42 j ≠ freshReg := fun e => freshReg_notMem_range ⟨j, e⟩
    have h3 : f42 j ≠ freeTopReg := fun e => freeTopReg_notMem_range ⟨j, e⟩
    have h4 : f42 j ≠ s0 := fun e => by rw [e] at hj_in; cases hj_in
    wram_simp [x2, h4, hx1_regs (f42 j) h1 h2 h3 h4]
  have hmem2_fib : ∀ a ∈ (Block.mk base (FibonacciHeap.space n_max)).footprint,
      (x2.comap f42).mem a = (x.comap f42).mem a := by dsimp only [x2]; mem_frame
  have hinv2 := FibonacciHeap.FibInv.supported hreg2 hmem2_fib (hb2.comap f42) hfib
  obtain ⟨y_fib, t_fib, he_fib, hinv_fib, hmod_fib, hpot_fib⟩ :=
    FibonacciHeap.insertCode_exec h u hinv2
      ⟨by simp only [PriorityQueue.MinPQ.toIndexed_apply, hh_none, Option.map_none], hu_lt.le⟩
      (by wram_simp [x2, hx1_v]) (by wram_simp [x2, hx1_k])
  wram_call he_fib canonical f42_injective
  have hy_v : y_fib.regs FibonacciHeap.argV = h.val :=
    (he_fib.regs_eq (by decide)).trans (by wram_simp [x2, hx1_v])
  refine WP.bounded ((he_fib.rename f42_injective).bounded hb2) ?_
  wram_exec [hy_v]; intro hby
  have hreg_y3 := regs_set_of_inputReg (x := y_fib.extend f42 x2) (r := outV) (by decide) h.val
  have hmod_x2 : Modifies (Block.mk base (space n_max)).footprint x.mem x2.mem :=
    hm1 ▸ Modifies.write_of_owns (owns_val_addr hh_lt) v
  refine ⟨by wram_simp [decode, PriorityQueue.MinPQ.stepAlloc, halloc, hh_lt, Fin.eta]; rfl, ?_,
    FibonacciHeap.modifies_block_trans hmod_x2 (modifies_of_fib hmod_fib), by
      rw [potential_supported hreg_y3, potential_extend]
      have hpot2 : potential x2 = potential x := FibonacciHeap.potential_supported hreg2
      change t_fib + FibonacciHeap.potential y_fib ≤ 121 + potential x2 at hpot_fib; omega⟩
  simp only [PriorityQueue.MinPQ.stepAlloc, halloc]
  have hx1_ofr :=
    (hx1_regs outerFrontierReg (by decide) (by decide) (by decide) (by decide)).trans hfr
  have hx1_fb := (hx1_regs freeBaseReg (by decide) (by decide) (by decide) (by decide)).trans hfb
  refine AllocRep.supported hreg_y3 (fun _ _ => rfl) hby
    ⟨(he_fib.rename f42_injective).bounded hb2, ?_, hwf',
      by wram_simp [x2, hx1_ofr], by wram_simp [x2, hx1_fb],
      by wram_simp [x2, hx1_fresh], by wram_simp [x2, hx1_top], ?_, ?_⟩
  · dsimp only
    rw [Data.comap_extend f42_injective, PriorityQueue.MinPQ.toIndexed_update_some s.entries h u v]
    exact hinv_fib
  · intro h' u' v' hsh'
    rcases eq_or_ne h' h with rfl | hne
    · simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hsh'
      obtain ⟨rfl, rfl⟩ := hsh'; exact ⟨hu_lt, hv_lt, by dsimp only [x2]; mem_frame⟩
    · simp only [Function.update_of_ne hne] at hsh'
      have := Fin.val_ne_of_ne hne
      obtain ⟨hu', hv', hm'⟩ := hval h' u' v' hsh'
      exact ⟨hu', hv', by dsimp only [x2]; mem_frame⟩
  · intro i hi
    have := hfree' i hi
    dsimp only [x2]; mem_frame

theorem decreaseKeyCode_exec {n_max U V w base : ℕ}
    {s : PriorityQueue.MinPQ.AllocState n_max} {x : Data rMinPQ}
    (h : Fin n_max) (u' : ℕ) (hrep : AllocRep n_max U V w base s x)
    (hv : (minPQSpec n_max U V).valid s.entries (.decreaseKey h u'))
    (hv_reg : x.regs argV = h.val) (hk_reg : x.regs argK = u') :
    ∃ y t, ExecWithin w decreaseKeyCode x y t ∧
      decode (n_max := n_max) (U := U) (V := V) (.decreaseKey h u') y.regs =
        some (PriorityQueue.MinPQ.stepAlloc s (.decreaseKey h u')).2 ∧
      AllocRep n_max U V w base (PriorityQueue.MinPQ.stepAlloc s (.decreaseKey h u')).1 y ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem y.mem ∧
      t + potential y ≤ 330 + potential x := by
  obtain ⟨hb, hfib, hwf, hfr, hfb, hfresh, htop, hval, hfree⟩ := hrep
  obtain ⟨u, v, hsh, hu'_le⟩ := hv
  obtain ⟨hu_lt, hv_lt, hm_v⟩ := hval h u v hsh
  have hu'_lt : u' < U := Nat.lt_of_le_of_lt hu'_le hu_lt
  obtain ⟨y_fib, t, he_fib, hinv_fib, hmod_fib, hpot_fib⟩ :=
    FibonacciHeap.decreaseKeyCode_exec h u' hfib
      ⟨⟨u, by simp only [PriorityQueue.MinPQ.toIndexed_apply, hsh, Option.map_some], hu'_le⟩,
        hu'_lt.le⟩ hv_reg hk_reg
  have he := he_fib.rename f42_injective
  have hmem_ge a (ha : base + FibonacciHeap.space n_max ≤ a) :
      (y_fib.extend f42 x).mem a = x.mem a := hmod_fib a (notMem_fib_footprint_of_ge ha)
  have hwf' :=
    (PriorityQueue.MinPQ.stepAlloc_refines_spec (U := U) (V := V) hwf
      (.decreaseKey h u') ⟨u, v, hsh, hu'_le⟩).2
  refine ⟨y_fib.extend f42 x, t, he, rfl, ?_, modifies_of_fib hmod_fib,
    by rw [potential_extend]; exact hpot_fib⟩
  simp only [PriorityQueue.MinPQ.stepAlloc, hsh] at hwf' ⊢
  refine ⟨he.bounded hb, by
      rw [Data.comap_extend f42_injective, PriorityQueue.MinPQ.toIndexed_update_some]
      exact hinv_fib,
    hwf', by wram_simp [hfr], by wram_simp [hfb], by wram_simp [hfresh], by wram_simp [htop],
    fun h' u₁ v₁ hsh' => ?_,
    fun i hi => (hmem_ge _ (by omega)).trans (hfree i hi)⟩
  rcases eq_or_ne h' h with rfl | hne
  · simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hsh'
    obtain ⟨rfl, rfl⟩ := hsh'
    exact ⟨hu'_lt, hv_lt, (hmem_ge _ (Nat.le_add_right _ _)).trans hm_v⟩
  · simp only [Function.update_of_ne hne] at hsh'
    obtain ⟨hu₁, hv₁, hm₁⟩ := hval h' u₁ v₁ hsh'
    exact ⟨hu₁, hv₁, (hmem_ge _ (Nat.le_add_right _ _)).trans hm₁⟩

private theorem extractMin_pushFree_wp {n_max U V w base : ℕ}
    {s : PriorityQueue.MinPQ.AllocState n_max} {x : Data rMinPQ} {y_fib : Data rFib}
    {h : Fin n_max} {u v : ℕ}
    (hrep : AllocRep n_max U V w base s x)
    (hinv_fib : FibonacciHeap.FibInv n_max U w base
      (Function.update (PriorityQueue.MinPQ.toIndexed s.entries) h none) y_fib)
    (hmod_fib : Modifies (Block.mk base (FibonacciHeap.space n_max)).footprint x.mem y_fib.mem)
    (hsh : s.entries h = some (u, v))
    (hfm' : PriorityQueue.MinPQ.findMin s.entries = some (u, v, h))
    (hfl_ne : y_fib.regs FibonacciHeap.outFlag ≠ 0)
    (hov_eq : y_fib.regs FibonacciHeap.outV = h.val) (hok_eq : y_fib.regs FibonacciHeap.outK = u)
    (hb1 : (y_fib.extend f42 x).Bounded w) :
    WP w (ram_exact[
        if outFlag = zeroP then [s0 ← zeroP] else [
          s0 ← valBaseReg + outV; outValReg ← *s0;
          s0 ← freeBaseReg + freeTopReg; *s0 ← outV; freeTopReg ← freeTopReg + oneP]])
      (y_fib.extend f42 x) fun y t =>
      t ≤ 8 ∧ decode (n_max := n_max) (U := U) (V := V) .extractMin y.regs =
        some (PriorityQueue.MinPQ.stepAlloc s .extractMin).2 ∧
      AllocRep n_max U V w base (PriorityQueue.MinPQ.stepAlloc s .extractMin).1 y ∧
      Modifies (Block.mk base (space n_max)).footprint (y_fib.extend f42 x).mem y.mem ∧
      potential y = FibonacciHeap.potential y_fib := by
  have hfit_stop := hrep.fits_stop
  have hsp := space_eq_fib_add n_max
  obtain ⟨_, _, hwf, hfr, hfb, hfresh, htop, hval, hfree⟩ := hrep
  have ⟨hwf_le, _, _, _, hwf_sum⟩ := hwf
  have hh_lt := h.isLt
  have hsz_pos : 1 ≤ PriorityQueue.MinPQ.size s.entries :=
    Finset.card_pos.mpr ⟨h, PriorityQueue.MinPQ.mem_dom_iff.mpr ⟨u, v, hsh⟩⟩
  have hfl_lt : s.freeList.length < n_max := by omega
  have hmem1_ge a (ha : base + FibonacciHeap.space n_max ≤ a) : y_fib.mem a = x.mem a :=
    hmod_fib a (notMem_fib_footprint_of_ge ha)
  have hm_v : y_fib.mem (base + FibonacciHeap.space n_max + h.val) = v :=
    (hmem1_ge _ (Nat.le_add_right _ _)).trans (hval h u v hsh).2.2
  have hfit (val : ℕ) (hval_le : val ≤ base + (FibonacciHeap.space n_max + n_max + n_max)) :
      Fits w val := hfit_stop.of_le (by omega)
  have hwf' :=
    (PriorityQueue.MinPQ.stepAlloc_refines_spec (U := U) (V := V) hwf .extractMin trivial).2
  refine WP.bounded hb1 ?_
  wram_exec [hfit, hinv_fib.2.1.regs_zeroP, hinv_fib.2.1.regs_oneP,
    hinv_fib.2.1.regs_frontierReg, hfb, htop, hov_eq, hm_v, hfl_ne]
  intro hby
  set x1 := y_fib.extend f42 x
  have hreg_fib : ∀ j : Fin rFib, FibonacciHeap.inputReg j = false →
      (((((x1.set s0 (base + FibonacciHeap.space n_max + h.val)).set outValReg v).set s0
        (base + FibonacciHeap.space n_max + n_max + s.freeList.length)).write
        (base + FibonacciHeap.space n_max + n_max + s.freeList.length) h.val).set
        freeTopReg (s.freeList.length + 1)).regs (f42 j) = (x1.comap f42).regs j := fun j hj => by
    have hj_in := inputReg_f42_of_false j hj
    have h1 : f42 j ≠ freeTopReg := fun e => freeTopReg_notMem_range ⟨j, e⟩
    have h2 : f42 j ≠ s0 := fun e => by rw [e] at hj_in; cases hj_in
    have h3 : f42 j ≠ outValReg := fun e => outValReg_notMem_range ⟨j, e⟩
    wram_simp [x1, h1, h2, h3]
  have hmem_fib : ∀ a ∈ (Block.mk base (FibonacciHeap.space n_max)).footprint,
      Function.update y_fib.mem (base + FibonacciHeap.space n_max + n_max + s.freeList.length)
        h.val a = y_fib.mem a := by mem_frame
  simp only [PriorityQueue.MinPQ.stepAlloc, hfm'] at hwf' ⊢
  refine ⟨by omega,
    by wram_simp [x1, decode, hfl_ne, hov_eq, hok_eq, hh_lt, Fin.eta]; rfl,
    ⟨hby, FibonacciHeap.FibInv.supported hreg_fib hmem_fib (hby.comap f42) (by
        dsimp only; rw [Data.comap_extend f42_injective, PriorityQueue.MinPQ.toIndexed_update_none]
        exact hinv_fib),
      hwf', by wram_simp [x1, hfr], by wram_simp [x1, hfb], by wram_simp [x1, hfresh],
      by wram_simp [List.length_cons], ?_, ?_⟩,
    Modifies.write_of_owns (owns_free_addr (base := base) hfl_lt) h.val,
    by unfold potential
       rw [FibonacciHeap.potential_supported hreg_fib, Data.comap_extend f42_injective]⟩
  · intro h' u' v' hsh'
    rcases eq_or_ne h' h with rfl | hne
    · simp only [Function.update_self, reduceCtorEq] at hsh'
    · simp only [Function.update_of_ne hne] at hsh'
      have := h'.isLt
      obtain ⟨hu', hv', hm'⟩ := hval h' u' v' hsh'
      exact ⟨hu', hv', by dsimp only [x1]; mem_frame⟩
  · rintro (_ | j) hi
    · wram_simp [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero, List.getElem_cons_zero]
    · simp only [List.length_cons] at hi
      have hm' := hfree j (by omega)
      rw [show (h :: s.freeList).length - 1 - (j + 1) = s.freeList.length - 1 - j by
        simp only [List.length_cons]; omega, List.getElem_cons_succ]
      dsimp only [x1]; mem_frame

theorem extractMinCode_exec {n_max U V w base : ℕ}
    {s : PriorityQueue.MinPQ.AllocState n_max} {x : Data rMinPQ}
    (hrep : AllocRep n_max U V w base s x) :
    ∃ y t, ExecWithin w extractMinCode x y t ∧
      decode (n_max := n_max) (U := U) (V := V) .extractMin y.regs =
        some (PriorityQueue.MinPQ.stepAlloc s .extractMin).2 ∧
      AllocRep n_max U V w base (PriorityQueue.MinPQ.stepAlloc s .extractMin).1 y ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem y.mem ∧
      t + potential y ≤
        418 * (Nat.log 2 (PriorityQueue.MinPQ.size s.entries) + 1) + potential x := by
  obtain ⟨y_fib, t1, he_fib, hdec_fib, hinv_fib, hmod_fib, hpot_fib⟩ :=
    FibonacciHeap.extractMinCode_exec hrep.2.1
  rw [PriorityQueue.MinPQ.dom_toIndexed] at hpot_fib
  change t1 + FibonacciHeap.potential y_fib ≤
    410 * (Nat.log 2 (PriorityQueue.MinPQ.size s.entries) + 1) + potential x at hpot_fib
  have hb1 : (y_fib.extend f42 x).Bounded w := (he_fib.rename f42_injective).bounded hrep.1
  change WP w extractMinCode x fun y t => _
  unfold extractMinCode
  refine WP.seq (WP.of_execWithin (he_fib.rename f42_injective) ?_)
  rcases hfm : IndexedMinPQ.findMin (PriorityQueue.MinPQ.toIndexed s.entries) with _ | ⟨h, u⟩
  · simp only [PQCode.decode, FibonacciHeap.code, indexedMinPQSpec, IndexedMinPQ.step,
      StateTransitionSpec.stepFn, hfm] at hdec_fib hinv_fib
    have hfl0 : y_fib.regs FibonacciHeap.outFlag = 0 := by
      by_contra hne; simp only [hne, ↓reduceIte] at hdec_fib
      by_cases hlt : y_fib.regs FibonacciHeap.outV < n_max <;>
        simp only [hlt, ↓reduceDIte] at hdec_fib <;> nomatch hdec_fib
    refine WP.bounded hb1 ?_; wram_exec [hinv_fib.2.1.regs_zeroP, hfl0]; intro hby
    have hreg_y := regs_set_of_inputReg (x := y_fib.extend f42 x) (r := s0) (by decide) 0
    have hfm' : PriorityQueue.MinPQ.findMin s.entries = none := by
      simp only [PriorityQueue.MinPQ.findMin, hfm]
    refine ⟨by wram_simp [decode, PriorityQueue.MinPQ.stepAlloc, hfm', hfl0]; rfl,
      by simp only [PriorityQueue.MinPQ.stepAlloc, hfm']
         exact (hrep.extend_unchanged hb1 hinv_fib hmod_fib).supported hreg_y (fun _ _ => rfl) hby,
      modifies_of_fib hmod_fib,
      by rw [potential_supported hreg_y, potential_extend]; omega⟩
  · obtain ⟨v, hsh, hfm', _⟩ := PriorityQueue.MinPQ.findMin_eq_some_of_indexed hfm
    simp only [PQCode.decode, FibonacciHeap.code, indexedMinPQSpec, IndexedMinPQ.step,
      StateTransitionSpec.stepFn, hfm] at hdec_fib hinv_fib
    have hfl_ne : y_fib.regs FibonacciHeap.outFlag ≠ 0 := by
      intro h0; simp only [h0, ↓reduceIte] at hdec_fib; nomatch hdec_fib
    simp only [hfl_ne, ↓reduceIte] at hdec_fib
    have hlt_ov : y_fib.regs FibonacciHeap.outV < n_max := by
      by_contra hge; simp only [hge, ↓reduceDIte] at hdec_fib; nomatch hdec_fib
    simp only [hlt_ov, ↓reduceDIte, Option.some.injEq, Prod.mk.injEq, Fin.ext_iff] at hdec_fib
    obtain ⟨y, t2, he2, ht2, hdec_y, hrep_y, hmod2, hpot_y⟩ :=
      extractMin_pushFree_wp hrep hinv_fib hmod_fib hsh hfm' hfl_ne hdec_fib.1 hdec_fib.2 hb1
    exact WP.of_execWithin he2 ⟨hdec_y, hrep_y,
      FibonacciHeap.modifies_block_trans (modifies_of_fib hmod_fib) hmod2, by omega⟩

/-! ## Unified dispatcher and `WordRAM.StateTransitionImpl` certificate -/

/-- Unified dispatcher `dispatchCode` implements all five `MinPQ` operations within
`charge n_max e o` amortized instructions over `Basis.exact`. -/
theorem dispatchCode_exec_raw {n_max U V w base : ℕ}
    {e : PriorityQueue.MinPQ.State n_max} {x : Data rMinPQ}
    (o : PriorityQueue.MinPQ.Op n_max) (hr : Rep n_max U V w base e x)
    (hv : (minPQSpec n_max U V).valid e o)
    (harg : rawArgMatch o x.regs) :
    ∃ y s' a m, Exec w dispatchCode x y m ∧
      (minPQSpec n_max U V).step e o s' a ∧
      decode (n_max := n_max) (U := U) (V := V) o y.regs = some a ∧
      Rep n_max U V w base s' y ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem y.mem ∧
      m + potential y ≤ charge n_max e o + potential x := by
  obtain ⟨s, rfl, hrep⟩ := hr
  have hz0 : x.regs zeroP = 0 := hrep.zeroP_eq
  have hstep_s :=
    (PriorityQueue.MinPQ.stepAlloc_refines_spec (U := U) (V := V) hrep.2.2.1 o hv).1
  have heq {r : Fin rMinPQ} (h : x.regs r = 0) : (Cond.eq r zeroP).Holds x := h.trans hz0.symm
  have hne {r : Fin rMinPQ} (h : x.regs r ≠ 0) : ¬(Cond.eq r zeroP).Holds x :=
    fun e => h (e.trans hz0)
  cases o with
  | isEmpty =>
    obtain ⟨ht2, ht1, ht0⟩ := harg
    obtain ⟨y, t, ⟨m, hm, he⟩, hdec, hrep_y, hmod, hpot⟩ := isEmptyCode_exec hrep
    exact ⟨y, _, _, m + 1 + 1 + 1,
      .branch_pos (heq ht2) (.branch_pos (heq ht1) (.branch_pos (heq ht0) he)),
      hstep_s, hdec, ⟨_, rfl, hrep_y⟩, hmod, by simp only [charge, tEmpty]; omega⟩
  | get h =>
    obtain ⟨ht2, ht1, ht0, hv_reg⟩ := harg
    obtain ⟨y, t, ⟨m, hm, he⟩, hdec, hrep_y, hmod, hpot⟩ := getCode_exec h hrep hv_reg
    exact ⟨y, _, _, m + 2 + 1 + 1,
      .branch_pos (heq ht2) (.branch_pos (heq ht1) (.branch_neg (hne ht0) he)),
      hstep_s, hdec, ⟨_, rfl, hrep_y⟩, hmod, by simp only [charge, tGet]; omega⟩
  | insert u v =>
    obtain ⟨ht2, ht1, ht0, hk_reg, hval_reg⟩ := harg
    obtain ⟨y, t, ⟨m, hm, he⟩, hdec, hrep_y, hmod, hpot⟩ :=
      insertCode_exec hrep hv hk_reg hval_reg
    exact ⟨y, _, _, m + 1 + 2 + 1,
      .branch_pos (heq ht2) (.branch_neg (hne ht1) (.branch_pos (heq ht0) he)),
      hstep_s, hdec, ⟨_, rfl, hrep_y⟩, hmod, by simp only [charge, tIns]; omega⟩
  | decreaseKey h u' =>
    obtain ⟨ht2, ht1, ht0, hv_reg, hk_reg⟩ := harg
    obtain ⟨y, t, ⟨m, hm, he⟩, hdec, hrep_y, hmod, hpot⟩ :=
      decreaseKeyCode_exec h u' hrep hv hv_reg hk_reg
    exact ⟨y, _, _, m + 2 + 2 + 1,
      .branch_pos (heq ht2) (.branch_neg (hne ht1) (.branch_neg (hne ht0) he)),
      hstep_s, hdec, ⟨_, rfl, hrep_y⟩, hmod, by simp only [charge, tDec]; omega⟩
  | extractMin =>
    obtain ⟨y, t, ⟨m, hm, he⟩, hdec, hrep_y, hmod, hpot⟩ := extractMinCode_exec hrep
    exact ⟨y, _, _, m + 2, .branch_neg (hne harg) he, hstep_s, hdec, ⟨_, rfl, hrep_y⟩, hmod,
      by simp only [charge, tExt]; omega⟩

theorem dispatchCode_exec {n_max U V w base : ℕ}
    {e : PriorityQueue.MinPQ.State n_max} {x : Data rMinPQ}
    (o : PriorityQueue.MinPQ.Op n_max) (hr : Rep n_max U V w base e x)
    (hv : (minPQSpec n_max U V).valid e o)
    (harg : argMatch U o x.regs) :
    ∃ y s' a m, Exec w dispatchCode x y m ∧
      (minPQSpec n_max U V).step e o s' a ∧
      decode (n_max := n_max) (U := U) (V := V) o y.regs = some a ∧
      Rep n_max U V w base s' y ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem y.mem ∧
      m + potential y ≤ charge n_max e o + potential x := by
  obtain ⟨s, rfl, hrep⟩ := hr
  exact dispatchCode_exec_raw o ⟨s, rfl, hrep⟩ hv (rawArgMatch_of_argMatch hrep hv harg)

/-- Unified standalone and inline-subroutine relational certificate for the key–value
Fibonacci heap with handles over `Basis.exact`. -/
def impl {n_max U V w base : ℕ}
    (hS : Fits w (base + space n_max)) (hU : Fits w U) (hV : Fits w V) :
    WordRAM.StateTransitionImpl subroutineCode (minPQSpec n_max U V) w base ![n_max]
      (PriorityQueue.MinPQ.empty n_max) where
  space := space n_max
  spanTime := 15
  setupTime := 18
  initPotential := 0
  charge := charge n_max
  rep := Rep n_max U V w base
  potential := potential
  encode := encode U
  argMatch := argMatch U
  decode := decode
  bounded := fun ⟨_, _, h⟩ => h.1
  arguments_fit o hv i _ := arguments_fit hS hU hV o hv i
  encode_matches := encode_matches
  rep_supported := Rep.supported
  potential_supported hreg _ _ := potential_supported hreg
  clear_nodup := by decide
  params_not_clear := by decide
  incCur_eval := incCur_eval
  span_exec := allocSpan_exec hS
  setup_exec := initSetup_exec
  step_exec := dispatchCode_exec

/-- Canonical native formats of key/value queue observations. -/
def nativeResultType (n : ℕ) : PriorityQueue.MinPQ.Op n → ResultType
  | .isEmpty => .bool
  | .get _ => .option (.prod .nat .nat)
  | .insert _ _ => .option (.fin n)
  | .decreaseKey _ _ => .unit
  | .extractMin => .option (.prod .nat (.prod .nat (.fin n)))

/-- The native format is an equality presentation of each existing result type. -/
theorem nativeResultType_eq (n U V : ℕ) (o : PriorityQueue.MinPQ.Op n) :
    (minPQSpec n U V).Result o = (nativeResultType n o).Value := by
  cases o <;> rfl

/-- One fixed result bank: presence flag, key, satellite value, and handle. -/
def nativeResultBank (i : ℕ) : Fin rMinPQ :=
  if i = 0 then outFlag else if i = 1 then outK else if i = 2 then outValReg else outV

/-- Native conversion reads the actual original operation tags from the machine. -/
def nativeResultReady {n : ℕ} : PriorityQueue.MinPQ.Op n → Data rMinPQ → Prop
  | .isEmpty, x => x.regs tag2 = 0 ∧ x.regs tag1 = 0 ∧ x.regs tag0 = 0
  | .get _, x => x.regs tag2 = 0 ∧ x.regs tag1 = 0 ∧ x.regs tag0 ≠ 0
  | .insert _ _, x => x.regs tag2 = 0 ∧ x.regs tag1 ≠ 0 ∧ x.regs tag0 = 0
  | .decreaseKey _ _, x => x.regs tag2 = 0 ∧ x.regs tag1 ≠ 0 ∧ x.regs tag0 ≠ 0
  | .extractMin, x => x.regs tag2 ≠ 0

/-- Insertion places its returned handle in the first payload slot and writes its presence tag;
all other observations retain their payloads. Every flag is normalized to zero or one. -/
def nativeResultCode : Code .standard rMinPQ :=
  .seq
    (.branch (.eq tag2 zeroP)
      (.branch (.eq tag1 zeroP)
        (.op (.copy outK outK))
        (.branch (.eq tag0 zeroP)
          (.seq (.op (.copy outK outV)) (.op (.const outFlag 1)))
          (.op (.copy outK outK))))
      (.op (.copy outK outK)))
    (.branch (.eq outFlag zeroP) (.op (.const outFlag 0)) (.op (.const outFlag 1)))

/-- Conversion pays at most nine native instructions and changes only its two output slots. -/
theorem nativeResultCode_spec {n U V w : ℕ} {x : Data rMinPQ}
    (h1 : Fits w 1) (hzero : x.regs zeroP = 0)
    (o : PriorityQueue.MinPQ.Op n) (a : (minPQSpec n U V).Result o)
    (hready : nativeResultReady o x) (hd : decode o x.regs = some a) :
    ∃ y, ExecWithin w nativeResultCode x y 9 ∧
      (nativeResultType n o).decode (y.regs ∘ nativeResultBank) 0 =
        some (cast (nativeResultType_eq n U V o) a) ∧
      y.mem = x.mem ∧
      ∀ i, i ≠ outFlag → i ≠ outK → y.regs i = x.regs i := by
  cases o <;> simp only [nativeResultReady] at hready
  all_goals
    unfold nativeResultCode
    wram_exec [hzero, hready] <;>
    simp_all only [minPQSpec, PriorityQueue.MinPQ.Op.Result, StateTransitionSpec.ofFn_result,
      decode, ne_eq, ne_comm, not_true_eq_false, not_false_eq_true, decide_false, decide_true,
      nativeResultType, ResultType.Value, Data.set, Function.update_eq_self, Function.update_idem,
      ResultType.decode, Function.comp_apply, nativeResultBank, ↓reduceIte, ↓dreduceIte,
      Function.update_self, one_ne_zero, zero_add, Fin.mk.injEq, Nat.reduceEqDiff,
      Function.update_of_ne, ResultType.words, Nat.reduceAdd, OfNat.ofNat_ne_zero,
      OfNat.ofNat_ne_one, Nat.succ_ne_self, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Option.map_bind, Option.map_some, Option.map_dite,
      implies_true, and_self, and_true] <;> try rfl
  case extractMin.neg =>
    split at hd
    · have ha := Option.some.inj hd
      rw [← ha]
      simp only [‹x.regs outV < n›, ↓reduceDIte, Option.bind_some]
      rfl
    · cases hd

/-- The fixed native suffix preserves the heap representation and its amortized potential. -/
def resultRecoding {n_max U V w base : ℕ}
    (hS : Fits w (base + space n_max)) (hU : Fits w U) (hV : Fits w V) :
    NativeResultRecoding (minPQSpec n_max U V).Result .standard rMinPQ w
      (impl hS hU hV).toStandard.decode (impl hS hU hV).toStandard.rep
      (impl hS hU hV).toStandard.potential where
  code := nativeResultCode
  resultBank := nativeResultBank
  resultType := nativeResultType n_max
  resultType_eq := nativeResultType_eq n_max U V
  time := 9
  ready := nativeResultReady
  execute {s} {x} o a hr hb hready hd := by
    have h1 : Fits w 1 := hS.of_le (by unfold space; lia)
    have hzero : x.regs zeroP = 0 := by
      obtain ⟨s₀, _, hs⟩ := hr
      exact hs.2.1.2.1.regs_zeroP
    obtain ⟨y, he, ha, hm, hregs⟩ := nativeResultCode_spec h1 hzero o a hready hd
    have hp : ∀ i, subroutineCode.toStandard.input i = false → y.regs i = x.regs i := by
      intro i hi
      apply hregs i
      · intro h
        subst i
        contradiction
      · intro h
        subst i
        contradiction
    have hmem : ∀ a ∈ (Block.mk base (space n_max)).footprint, y.mem a = x.mem a :=
      fun _ _ => congrFun hm _
    exact ⟨y, he, ha, (impl hS hU hV).toStandard.rep_supported hp hmem (he.bounded hb) hr,
      (impl hS hU hV).toStandard.potential_supported hp hmem hr, hm⟩

/-- Original operation execution preserves the opcode words consumed by native conversion. -/
theorem resultRecoding_ready {n_max U V w base : ℕ}
    (hS : Fits w (base + space n_max)) (hU : Fits w U) (hV : Fits w V)
    {s x o y m} (_hr : (impl hS hU hV).toStandard.rep s x)
    (_hv : (minPQSpec n_max U V).valid s o)
    (harg : (impl hS hU hV).toStandard.argMatch o x.regs)
    (he : Exec w subroutineCode.toStandard.code x y m) :
    (resultRecoding hS hU hV).ready o y := by
  change argMatch U o x.regs at harg
  have h2 : y.regs tag2 = x.regs tag2 := he.regs_eq (by decide)
  have h1 : y.regs tag1 = x.regs tag1 := he.regs_eq (by decide)
  have h0 : y.regs tag0 = x.regs tag0 := he.regs_eq (by decide)
  change nativeResultReady o y
  cases o with
  | isEmpty => exact ⟨h2.trans harg.1, h1.trans harg.2.1, h0.trans harg.2.2⟩
  | get _ => exact ⟨h2.trans harg.1, h1.trans harg.2.1, ne_of_eq_of_ne h0 harg.2.2.1⟩
  | insert _ _ => exact ⟨h2.trans harg.1, ne_of_eq_of_ne h1 harg.2.1, h0.trans harg.2.2.1⟩
  | decreaseKey _ _ =>
    exact ⟨h2.trans harg.1, ne_of_eq_of_ne h1 harg.2.1, ne_of_eq_of_ne h0 harg.2.2.1⟩
  | extractMin => exact ne_of_eq_of_ne h2 harg

/-! ## Standalone `Basis.standard` `DynamicProgram` and `Amortized` implementations -/

/-- Standalone `DynamicProgram` implementation of the key–value Fibonacci heap over
`Basis.standard`. -/
def dynamicProgram {n_max U V w base : ℕ}
    (hS : Fits w (base + space n_max)) (hU : Fits w U) (hV : Fits w V) :
    DynamicProgram (minPQSpec n_max U V) rMinPQ :=
  (impl (n_max := n_max) (U := U) (V := V) hS hU hV).toStandard.toDynamicProgram
    (resultRecoding hS hU hV)

/-- Standalone `DynamicCertificate` for the key–value Fibonacci heap over `Basis.standard`. -/
def certificate {n_max U V w base : ℕ}
    (hS : Fits w (base + space n_max)) (hU : Fits w U) (hV : Fits w V) :
    DynamicCertificate (dynamicProgram hS hU hV) w :=
  (impl hS hU hV).toStandard.toCertificate
    (resultRecoding hS hU hV) (resultRecoding_ready hS hU hV)

/-- Standalone `Amortized` certificate for the key–value Fibonacci heap over
`Basis.standard`, charging nine native conversion instructions and one trailing `halt`
per operation. -/
theorem amortized {n_max U V w base : ℕ}
    (hS : Fits w (base + space n_max)) (hU : Fits w U) (hV : Fits w V) :
    Amortized (certificate hS hU hV).impl
      DynamicProgram.OperationTrace.instructions
      (fun _ x => potential x)
      (fun s o => charge n_max s o + 10) :=
  (impl hS hU hV).toStandard.toAmortized
    (resultRecoding hS hU hV) (resultRecoding_ready hS hU hV)

/-- Adaptive-client amortized execution bound for any demonically admissible `MinPQ` client `p`
over `Basis.standard`. -/
theorem run_client_amortized {n_max U V w base : ℕ}
    (hS : Fits w (base + space n_max)) (hU : Fits w U) (hV : Fits w V)
    {α : Type*} (p : (minPQSpec n_max U V).Client α)
    {s : PriorityQueue.MinPQ.State n_max} {x : Data rMinPQ}
    (hr : Rep n_max U V w base s x)
    (hv : (minPQSpec n_max U V).DemonicValid s p) :
    ∃ a y traces s' tr,
      Executes ((dynamicProgram hS hU hV).ExecOp w) p x a y traces ∧
      (minPQSpec n_max U V).ClientRun s p a s' tr ∧
      Rep n_max U V w base s' y ∧
      traces.length = tr.length ∧
      DataStructure.total DynamicProgram.OperationTrace.instructions traces + potential y ≤
        (minPQSpec n_max U V).totalCostTranscript
          (fun st o => charge n_max st o + 10) s tr + potential x :=
  (impl hS hU hV).toStandard.run_client_demonic_amortized
    (resultRecoding hS hU hV) (resultRecoding_ready hS hU hV) p hr hv

/-! ## Standalone end-to-end `Basis.exact` flat-program adaptive-client theorems -/

/-- Compiled flat `Program .exact rMinPQ` for `O(1)` fresh zeroed-memory initialization. -/
def initFreshProg : Program .exact rMinPQ := subroutineCode.initFreshProg

/-- Compiled flat `Program .exact rMinPQ` for `O(n_max)` dirty-memory reusable initialization. -/
def initClearProg : Program .exact rMinPQ := subroutineCode.initClearProg

/-- Compiled flat `Program .exact rMinPQ` serving all five priority-queue operations. -/
def opProg : Program .exact rMinPQ := subroutineCode.opProg

/-- Initial register assignment supplying `n_max` in `nReg` (`R[0]`), `base` in `outerFrontierReg`
(`R[1]`), and `0` elsewhere. -/
def initRegs (n_max base : ℕ) : Fin rMinPQ → ℕ :=
  fun i => if i = nReg then n_max else if i = outerFrontierReg then base else 0

/-- Deliver operation `o`'s 3-bit tag into `tag2..tag0` (`R[17..19]`), handle/key arguments into
`argV, argK` (`R[20..21]`), and satellite value into `inValReg` (`R[46]`), leaving all other
registers unchanged. -/
def prepareRegs {n_max : ℕ} (o : PriorityQueue.MinPQ.Op n_max)
    (regs : Fin rMinPQ → ℕ) : Fin rMinPQ → ℕ :=
  fun i =>
    if i = tag2 ∨ i = tag1 ∨ i = tag0 ∨ i = argV ∨ i = argK ∨ i = inValReg then
      rawEncode o i
    else
      regs i

/-- Count `isEmpty` and `get` queries in an operation sequence. -/
def numQueries {n_max : ℕ} : List (PriorityQueue.MinPQ.Op n_max) → ℕ
  | [] => 0
  | .isEmpty :: ops | .get _ :: ops => 1 + numQueries ops
  | _ :: ops => numQueries ops

/-- Count `insert` operations in an operation sequence. -/
def numInserts {n_max : ℕ} : List (PriorityQueue.MinPQ.Op n_max) → ℕ
  | [] => 0
  | .insert _ _ :: ops => 1 + numInserts ops
  | _ :: ops => numInserts ops

/-- Count `decreaseKey` operations in an operation sequence. -/
def numDecreaseKeys {n_max : ℕ} : List (PriorityQueue.MinPQ.Op n_max) → ℕ
  | [] => 0
  | .decreaseKey _ _ :: ops => 1 + numDecreaseKeys ops
  | _ :: ops => numDecreaseKeys ops

/-- Count `extractMin` operations in an operation sequence. -/
def numExtractMins {n_max : ℕ} : List (PriorityQueue.MinPQ.Op n_max) → ℕ
  | [] => 0
  | .extractMin :: ops => 1 + numExtractMins ops
  | _ :: ops => numExtractMins ops

/-- Sum of `Nat.log 2 (MinPQ.size s) + 1` over all `extractMin` steps along a relational
transcript `tr` starting from state `s`, where `MinPQ.size s` is the number of stored elements
immediately before each `extractMin`. -/
def extractLogSum {n_max U V : ℕ} :
    PriorityQueue.MinPQ.State n_max →
      (minPQSpec n_max U V).Transcript → ℕ
  | _, [] => 0
  | s, e :: tr =>
    (match e.op with
     | .extractMin => Nat.log 2 (PriorityQueue.MinPQ.size s) + 1
     | _ => 0) + extractLogSum e.nextState tr

theorem extractLogSum_le_numExtractMins {n_max U V : ℕ} :
    ∀ (tr : (minPQSpec n_max U V).Transcript)
      (s : PriorityQueue.MinPQ.State n_max),
      extractLogSum s tr ≤ numExtractMins tr.ops * (Nat.log 2 n_max + 1)
  | [], _ => Nat.zero_le _
  | ⟨o, res, s₁⟩ :: tr, s => by
    have ih := extractLogSum_le_numExtractMins tr s₁
    have hlog := Nat.log_mono_right (b := 2) (PriorityQueue.MinPQ.size_le s)
    cases o <;>
      simp only [extractLogSum, StateTransitionSpec.Transcript.ops_cons, numExtractMins,
        Nat.add_mul, Nat.one_mul, Nat.zero_add] <;> omega

/-- Sequential flat-program execution of an adaptive client `p : (minPQSpec n_max U V).Client α`
by repeated calls to `opProg`: each `.liftBind o k` call prepares input registers via
`prepareRegs`, runs `opProg` from `pc = 0` to `halt`, decodes a valid `minPQSpec` transition
`(s₁, a)`, modifies memory only within `[base, base + space n_max)`, continues with `k a`,
records the resulting return value `v` and transcript `tr`, and accumulates total instructions
executed (including each trailing `halt`). -/
inductive RunsClient {n_max U V : ℕ} {α : Type*} (w base : ℕ) :
    PriorityQueue.MinPQ.State n_max → Data rMinPQ →
      (minPQSpec n_max U V).Client α → α →
      (minPQSpec n_max U V).Transcript →
      PriorityQueue.MinPQ.State n_max → Data rMinPQ → ℕ → Prop
  | pure {s x a} : RunsClient w base s x (.pure a) a [] s x 0
  | liftBind {s s₁ s₂ x o k a v tr pc y z steps rest} :
      Runs w opProg ⟨0, ⟨prepareRegs o x.regs, x.mem⟩⟩ ⟨pc, y⟩ steps →
      (∃ out, step w opProg ⟨pc, y⟩ = .halt out) →
      (minPQSpec n_max U V).step s o s₁ a →
      decode (n_max := n_max) (U := U) (V := V) o y.regs = some a →
      Modifies (Block.mk base (space n_max)).footprint x.mem y.mem →
      RunsClient w base s₁ y (k a) v tr s₂ z rest →
      RunsClient w base s x (.liftBind o k) v (⟨o, a, s₁⟩ :: tr) s₂ z ((steps + 1) + rest)

theorem RunsClient.pure_iff {n_max U V : ℕ} {α : Type*} {w base : ℕ}
    {s s' : PriorityQueue.MinPQ.State n_max} {x z : Data rMinPQ}
    {a v : α} {tr : (minPQSpec n_max U V).Transcript} {total : ℕ} :
    RunsClient (U := U) (V := V) w base s x (.pure a) v tr s' z total ↔
      v = a ∧ tr = [] ∧ s' = s ∧ z = x ∧ total = 0 := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    exact .pure

theorem RunsClient.liftBind_iff {n_max U V : ℕ} {α : Type*} {w base : ℕ}
    {s s₂ : PriorityQueue.MinPQ.State n_max} {x z : Data rMinPQ}
    {o : PriorityQueue.MinPQ.Op n_max}
    {k : (minPQSpec n_max U V).Result o → (minPQSpec n_max U V).Client α}
    {v : α} {tr : (minPQSpec n_max U V).Transcript} {total : ℕ} :
    RunsClient (U := U) (V := V) w base s x (.liftBind o k) v tr s₂ z total ↔
      ∃ s₁ a tr_rest pc y steps rest,
        tr = ⟨o, a, s₁⟩ :: tr_rest ∧
        total = (steps + 1) + rest ∧
        Runs w opProg ⟨0, ⟨prepareRegs o x.regs, x.mem⟩⟩ ⟨pc, y⟩ steps ∧
        (∃ out, step w opProg ⟨pc, y⟩ = .halt out) ∧
        (minPQSpec n_max U V).step s o s₁ a ∧
        decode (n_max := n_max) (U := U) (V := V) o y.regs = some a ∧
        Modifies (Block.mk base (space n_max)).footprint x.mem y.mem ∧
        RunsClient (U := U) (V := V) w base s₁ y (k a) v tr_rest s₂ z rest := by
  constructor
  · intro h
    cases h with
    | liftBind hr hh hstep hdec hmod hrest =>
      exact ⟨_, _, _, _, _, _, _, rfl, rfl, hr, hh, hstep, hdec, hmod, hrest⟩
  · rintro ⟨_, _, _, _, _, _, _, rfl, rfl, hr, hh, hstep, hdec, hmod, hrest⟩
    exact .liftBind hr hh hstep hdec hmod hrest

private theorem step_program_halt {w : ℕ} (c : Code .exact rMinPQ) (out : Fin rMinPQ)
    (y : Data rMinPQ) : step w (c.program out) ⟨0 + c.size, y⟩ = .halt (y.regs out) :=
  step_halt (by
    simp only [Code.program, Nat.zero_add,
      List.getElem?_append_right (Code.length_assemble c 0).le,
      Code.length_assemble, Nat.sub_self, List.getElem?_cons_zero])

private theorem seq_runsClient {n_max U V w base : ℕ}
    (hS : Fits w (base + space n_max)) (hU : Fits w U) (hV : Fits w V)
    {α : Type*} (p : (minPQSpec n_max U V).Client α)
    {s : PriorityQueue.MinPQ.State n_max} {x : Data rMinPQ}
    (hr : Rep n_max U V w base s x)
    (hv : (minPQSpec n_max U V).DemonicValid s p) :
    ∃ v tr s_fin z total,
      RunsClient (U := U) (V := V) w base s x p v tr s_fin z total ∧
      (minPQSpec n_max U V).ClientRun s p v s_fin tr ∧
      Rep n_max U V w base s_fin z ∧
      total + potential z ≤
        421 * (numQueries tr.ops + numInserts tr.ops + numDecreaseKeys tr.ops +
          extractLogSum s tr) + potential x := by
  induction p generalizing s x with
  | pure a =>
    exact ⟨a, [], s, x, 0, .pure, .pure (D := minPQSpec n_max U V) s a, hr, by
      simp only [StateTransitionSpec.Transcript.ops_nil, numQueries, numInserts,
        numDecreaseKeys, extractLogSum]; omega⟩
  | liftBind o k ih =>
    obtain ⟨hv_o, hv_rest⟩ := ((minPQSpec n_max U V).demonicValid_liftBind_iff s o k).mp hv
    let x' : Data rMinPQ := ⟨prepareRegs o x.regs, x.mem⟩
    have hbx : x.Bounded w := hr.choose_spec.2.1
    have henc := encode_eq_rawEncode_of_rep hr hv_o
    have hb' : x'.Bounded w := ⟨fun i => by
      change Fits w (if _ then rawEncode o i else x.regs i)
      split_ifs
      · rw [← henc]; exact arguments_fit hS hU hV o hv_o i
      · exact hbx.1 i, hbx.2⟩
    have hreg' : ∀ i, inputReg i = false → x'.regs i = x.regs i := fun i hi => by
      have hne : ¬(i = tag2 ∨ i = tag1 ∨ i = tag0 ∨ i = argV ∨ i = argK ∨ i = inValReg) := by
        rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;> exact absurd hi (by decide)
      simp only [x', prepareRegs, hne, ↓reduceIte]
    have harg' : argMatch U o x'.regs :=
      argMatch_of_eq_encode o (congrFun henc.symm tag2) (congrFun henc.symm tag1)
        (congrFun henc.symm tag0) (congrFun henc.symm argV) (congrFun henc.symm argK)
        (congrFun henc.symm inValReg)
    obtain ⟨y, s₁, a, m, he_op, hstep, hdec, hr_y, hmod, hpot_m⟩ :=
      dispatchCode_exec o (hr.supported hreg' (fun _ _ => rfl) hb') hv_o harg'
    rw [potential_supported hreg'] at hpot_m
    obtain ⟨v, tr, s_fin, z, rest, hrest, hrun_rest, hr_z, hpot_rest⟩ :=
      ih a hr_y (hv_rest s₁ a hstep)
    refine ⟨v, ⟨o, a, s₁⟩ :: tr, s_fin, z, (m + 1) + rest,
      .liftBind (he_op.runs (pc := 0) (p := opProg) (Program.Contains.self _).append_left)
        ⟨_, step_program_halt dispatchCode outFlag y⟩ hstep hdec hmod hrest,
      .liftBind (D := minPQSpec n_max U V) o k a hv_o hstep hrun_rest, hr_z, ?_⟩
    cases o <;>
      simp only [StateTransitionSpec.Transcript.ops_cons, charge, tEmpty, tGet, tIns, tDec, tExt,
        numQueries, numInserts, numDecreaseKeys, extractLogSum] at hpot_m ⊢ <;> omega

private theorem initRegs_bounded {n_max base w : ℕ} (hS : Fits w (base + space n_max))
    {mem₀ : ℕ → ℕ} (hmem : ∀ a, Fits w (mem₀ a)) :
    (⟨initRegs n_max base, mem₀⟩ : Data rMinPQ).Bounded w := by
  refine ⟨fun i => ?_, hmem⟩
  simp only [initRegs]
  split_ifs
  · exact hS.of_le (by have := space_lower n_max; omega)
  · exact hS.of_le (Nat.le_add_right base _)
  · exact hS.of_le (Nat.zero_le _)

private theorem run_client_exact_of_init {n_max U V w base t_bound : ℕ}
    (hS : Fits w (base + space n_max)) (hU : Fits w U) (hV : Fits w V)
    {mem₀ : ℕ → ℕ} {c : Code .exact rMinPQ}
    (hinit : ∃ x₀, ExecWithin w c ⟨initRegs n_max base, mem₀⟩ x₀ t_bound ∧
      x₀.regs outerFrontierReg = base + space n_max ∧
      Rep n_max U V w base (PriorityQueue.MinPQ.empty n_max) x₀ ∧
      potential x₀ ≤ 0 ∧
      Modifies (Block.mk base (space n_max)).footprint mem₀ x₀.mem)
    {α : Type*} (p : (minPQSpec n_max U V).Client α)
    (hv : (minPQSpec n_max U V).DemonicValid (PriorityQueue.MinPQ.empty n_max) p) :
    ∃ pc₀ x₀ t_init v tr s_fin z t_ops,
      Runs w (c.program outFlag) ⟨0, ⟨initRegs n_max base, mem₀⟩⟩ ⟨pc₀, x₀⟩ t_init ∧
      (∃ out, step w (c.program outFlag) ⟨pc₀, x₀⟩ = .halt out) ∧
      Modifies (Block.mk base (space n_max)).footprint mem₀ x₀.mem ∧
      RunsClient (U := U) (V := V) w base (PriorityQueue.MinPQ.empty n_max) x₀ p v tr
        s_fin z t_ops ∧
      (minPQSpec n_max U V).ClientRun (PriorityQueue.MinPQ.empty n_max) p v s_fin tr ∧
      t_init ≤ t_bound ∧
      t_ops ≤
        421 * (numQueries tr.ops + numInserts tr.ops + numDecreaseKeys tr.ops +
          extractLogSum (PriorityQueue.MinPQ.empty n_max) tr) ∧
      t_ops ≤
        421 * (numQueries tr.ops + numInserts tr.ops + numDecreaseKeys tr.ops +
          numExtractMins tr.ops * (Nat.log 2 n_max + 1)) := by
  obtain ⟨x₀, ⟨t_init, ht_init, he_init⟩, _, hr₀, hpot₀, hmod₀⟩ := hinit
  have hruns₀ : Runs w (c.program outFlag) ⟨0, ⟨initRegs n_max base, mem₀⟩⟩ ⟨0 + c.size, x₀⟩
      t_init :=
    he_init.runs (pc := 0) (p := c.program outFlag) (Program.Contains.self _).append_left
  have hhalt₀ : step w (c.program outFlag) ⟨0 + c.size, x₀⟩ = .halt (x₀.regs outFlag) :=
    step_program_halt c outFlag x₀
  obtain ⟨v, tr, s_fin, z, t_ops, hruns_ops, hrun, _, hbound⟩ := seq_runsClient hS hU hV p hr₀ hv
  have hlog_le := extractLogSum_le_numExtractMins tr (PriorityQueue.MinPQ.empty n_max)
  exact ⟨_, x₀, t_init, v, tr, s_fin, z, t_ops, hruns₀, ⟨_, hhalt₀⟩, hmod₀, hruns_ops, hrun,
    ht_init, by omega, by omega⟩

/-- Standalone `Basis.exact` adaptive-client theorem with `O(1)` fresh initialization on zeroed
`[base, base + 11 * n_max + 1)` and per-extraction `O(log n + 1)` amortized cost in the current
number of stored elements `n = MinPQ.size s`. -/
theorem run_client_exact_fresh {n_max U V w base : ℕ}
    (hS : Fits w (base + space n_max)) (hU : Fits w U) (hV : Fits w V)
    {mem₀ : ℕ → ℕ} (hmem : ∀ a, Fits w (mem₀ a))
    (hzero : ∀ a ∈ (Block.mk base (space n_max)).footprint, mem₀ a = 0)
    {α : Type*} (p : (minPQSpec n_max U V).Client α)
    (hv : (minPQSpec n_max U V).DemonicValid
      (PriorityQueue.MinPQ.empty n_max) p) :
    ∃ pc₀ x₀ t_init v tr s_fin z t_ops,
      Runs w initFreshProg ⟨0, ⟨initRegs n_max base, mem₀⟩⟩ ⟨pc₀, x₀⟩ t_init ∧
      (∃ out, step w initFreshProg ⟨pc₀, x₀⟩ = .halt out) ∧
      Modifies (Block.mk base (space n_max)).footprint mem₀ x₀.mem ∧
      RunsClient (U := U) (V := V) w base (PriorityQueue.MinPQ.empty n_max) x₀ p v tr
        s_fin z t_ops ∧
      (minPQSpec n_max U V).ClientRun
        (PriorityQueue.MinPQ.empty n_max) p v s_fin tr ∧
      t_init + 1 ≤ 421 ∧
      t_ops ≤
        421 * (numQueries tr.ops + numInserts tr.ops + numDecreaseKeys tr.ops +
          extractLogSum (PriorityQueue.MinPQ.empty n_max) tr) ∧
      t_ops ≤
        421 * (numQueries tr.ops + numInserts tr.ops + numDecreaseKeys tr.ops +
          numExtractMins tr.ops * (Nat.log 2 n_max + 1)) := by
  obtain ⟨pc₀, x₀, t_init, v, tr, s_fin, z, t_ops, hruns₀, hhalt₀, hmod₀, hruns_ops, hrun,
    ht_init, hb₁, hb₂⟩ :=
    run_client_exact_of_init hS hU hV
      ((impl hS hU hV).initFresh_exec (initRegs_bounded hS hmem)
        (by simp only [subroutineCode, initRegs,
          show outerFrontierReg ≠ nReg by decide, ↓reduceIte])
        (fun j => by fin_cases j; rfl) hzero) p hv
  exact ⟨pc₀, x₀, t_init, v, tr, s_fin, z, t_ops, hruns₀, hhalt₀, hmod₀, hruns_ops, hrun,
    by change t_init ≤ 33 at ht_init; omega, hb₁, hb₂⟩

/-- Standalone `Basis.exact` adaptive-client theorem with `O(n_max)` reusable initialization on
arbitrary `w`-bounded memory `mem₀` and per-extraction `O(log n + 1)` amortized cost in the current
number of stored elements `n = MinPQ.size s`. -/
theorem run_client_exact_reusable {n_max U V w base : ℕ}
    (hS : Fits w (base + space n_max)) (hU : Fits w U) (hV : Fits w V)
    {mem₀ : ℕ → ℕ} (hmem : ∀ a, Fits w (mem₀ a))
    {α : Type*} (p : (minPQSpec n_max U V).Client α)
    (hv : (minPQSpec n_max U V).DemonicValid
      (PriorityQueue.MinPQ.empty n_max) p) :
    ∃ pc₀ x₀ t_init v tr s_fin z t_ops,
      Runs w initClearProg ⟨0, ⟨initRegs n_max base, mem₀⟩⟩ ⟨pc₀, x₀⟩ t_init ∧
      (∃ out, step w initClearProg ⟨pc₀, x₀⟩ = .halt out) ∧
      Modifies (Block.mk base (space n_max)).footprint mem₀ x₀.mem ∧
      RunsClient (U := U) (V := V) w base (PriorityQueue.MinPQ.empty n_max) x₀ p v tr
        s_fin z t_ops ∧
      (minPQSpec n_max U V).ClientRun
        (PriorityQueue.MinPQ.empty n_max) p v s_fin tr ∧
      t_init + 1 ≤ 421 * (n_max + 1) ∧
      t_ops ≤
        421 * (numQueries tr.ops + numInserts tr.ops + numDecreaseKeys tr.ops +
          extractLogSum (PriorityQueue.MinPQ.empty n_max) tr) ∧
      t_ops ≤
        421 * (numQueries tr.ops + numInserts tr.ops + numDecreaseKeys tr.ops +
          numExtractMins tr.ops * (Nat.log 2 n_max + 1)) := by
  obtain ⟨pc₀, x₀, t_init, v, tr, s_fin, z, t_ops, hruns₀, hhalt₀, hmod₀, hruns_ops, hrun,
    ht_init, hb₁, hb₂⟩ :=
    run_client_exact_of_init hS hU hV
      ((impl hS hU hV).initClear_exec (initRegs_bounded hS hmem)
        (by simp only [subroutineCode, initRegs,
          show outerFrontierReg ≠ nReg by decide, ↓reduceIte])
        (fun j => by fin_cases j; rfl)) p hv
  exact ⟨pc₀, x₀, t_init, v, tr, s_fin, z, t_ops, hruns₀, hhalt₀, hmod₀, hruns_ops, hrun,
    by change t_init ≤ 33 + 4 * (11 * n_max + 1) + 6 at ht_init; omega, hb₁, hb₂⟩

end Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.MinPQ
