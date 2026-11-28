/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Algorithms.Lean.Dijkstra.Native.Binary
public import CslibFrontier.Algorithms.Lean.Dijkstra.Native.Fibonacci
public import CslibFrontier.Computability.WordRAM.Realization.Client.MemoryStack
import CslibFrontier.Tactic.Realize

/-!
# Tests for `word_enc_structure` and `Dijkstra.Native.Common`

Nonvacuous checked tests covering:

1. `word_enc_structure` on multi-field nested structures, flattened parent structures (`extends`),
   and dependent fields (`using`) paired with `sigmaWords`: `@[simp]` coordinate projections,
   slice equations, `_fits`, injectivity, exact layout preservation on migrated repository types,
   and end-to-end `realize` round-trips.
2. `Dijkstra.Native.Common`: shared `NativeMethods` and `NativeAllocator` kernel instantiated on
   both `Binary.nativeMethods` (width `4`) and `Fibonacci.nativeMethods` (width `2`), concrete
   nonvacuity of `NativeMethods.targetSafe` for both heaps, and a concrete `ExecWithin` run of
   `Fibonacci.nativeMethods.target_realizes` relaxing an edge into the shared distance table.
-/

public section

namespace CslibFrontierTests.WordEncStructureDijkstra

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.Memory Cslib.DataStructure.PriorityQueue
open Cslib.Algorithms.Dijkstra (ListInstance)
open Cslib.Algorithms.Lean.Dijkstra
open Cslib.Algorithms.Lean.Dijkstra.Native

/-! ## 1. Multi-field nested records, `extends`, and dependent `using` fields -/

/-- Two-word bounds record for nested `word_enc_structure` tests. -/
structure InnerPair where
  /-- Lower offset. -/
  lo : ℕ
  /-- Upper offset. -/
  hi : ℕ

/-- Faithful two-word encoding of `InnerPair`. -/
word_enc_structure innerPairWords : InnerPair where
  lo : wordWords,
  hi : wordWords

/-- Multi-field nested record combining scalar, nested structure, `Block`, and `Bool` fields. -/
structure NestedSpan where
  /-- Scalar tag word. -/
  tag : ℕ
  /-- Nested two-word bounds. -/
  bounds : InnerPair
  /-- Memory block (`base`, `length`). -/
  block : Block
  /-- Boolean flag (`2` words via `boolWords`). -/
  flag : Bool

/-- Faithful seven-word encoding of `NestedSpan`. -/
word_enc_structure nestedSpanWords : NestedSpan where
  tag : wordWords,
  bounds : innerPairWords,
  block : blockWords,
  flag : (WordEncoding.encode (α := Bool))

/-- `@[simp]` coordinate lemmas reduce every slot of `nestedSpanWords` without unfolding the
embedding body. -/
theorem nestedSpanWords_coords (t a b base len : ℕ) (flag : Bool) :
    nestedSpanWords ⟨t, ⟨a, b⟩, ⟨base, len⟩, flag⟩ 0 = t ∧
      nestedSpanWords ⟨t, ⟨a, b⟩, ⟨base, len⟩, flag⟩ 1 = a ∧
      nestedSpanWords ⟨t, ⟨a, b⟩, ⟨base, len⟩, flag⟩ 2 = b ∧
      nestedSpanWords ⟨t, ⟨a, b⟩, ⟨base, len⟩, flag⟩ 3 = base ∧
      nestedSpanWords ⟨t, ⟨a, b⟩, ⟨base, len⟩, flag⟩ 4 = len ∧
      nestedSpanWords ⟨t, ⟨a, b⟩, ⟨base, len⟩, flag⟩ 5 = WordEncoding.encode flag 0 := by
  simp

/-- Generated slice lemma extracts the nested `bounds` field at offset `1`. -/
theorem nestedSpanWords_bounds_slice (x : NestedSpan) (j : Fin 2) :
    nestedSpanWords x ⟨1 + j.val, by omega⟩ = innerPairWords x.bounds j :=
  nestedSpanWords_bounds x j

/-- Generated embedding is injective on the full nested structure. -/
theorem nestedSpanWords_inj {x y : NestedSpan}
    (h : ∀ i, nestedSpanWords x i = nestedSpanWords y i) : x = y :=
  nestedSpanWords.injective (funext h)

/-- Generated `_fits` lemma composes per-field fit proofs without `fin_cases`. -/
theorem nestedSpanWords_all_fit {w : ℕ} (hw : 2 ≤ w) :
    ∀ j, Fits w (nestedSpanWords ⟨1, ⟨0, 2⟩, ⟨3, 1⟩, false⟩ j) := by
  have hle : ∀ {c : ℕ}, c ≤ 3 → Fits w c := fun hc => by
    have h4 : 4 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide : 0 < 2) hw
    exact Nat.lt_of_lt_of_le (by omega) h4
  exact nestedSpanWords_fits
    (hle (by decide))
    (innerPairWords_fits (a := ⟨0, 2⟩) (hle (by decide)) (hle (by decide)))
    (blockWords_fits (hle (by decide)) (hle (by decide)))
    (by intro i; fin_cases i <;> exact hle (by decide))

/-- Structure inheriting a parent via `extends` (flattened parent subobject field). -/
structure ExtendedSpan extends InnerPair where
  /-- Stride word after the inherited bounds. -/
  stride : ℕ

/-- Faithful three-word encoding of `ExtendedSpan`. -/
word_enc_structure extendedSpanWords : ExtendedSpan where
  toInnerPair : innerPairWords,
  stride : wordWords

theorem extendedSpanWords_coords (a b s : ℕ) :
    extendedSpanWords ⟨⟨a, b⟩, s⟩ 0 = a ∧
      extendedSpanWords ⟨⟨a, b⟩, s⟩ 1 = b ∧
      extendedSpanWords ⟨⟨a, b⟩, s⟩ 2 = s := by
  simp

/-- Parameterized structure with a `Fin`-typed field encoded via `using Fin.val_injective`. -/
structure DepWindow (n : ℕ) where
  /-- Bounded cursor `< n + 1`. -/
  cursor : Fin (n + 1)
  /-- Backing block. -/
  table : Block

section
variable {n : ℕ}

/-- Faithful three-word encoding of `DepWindow n`. -/
word_enc_structure depWindowBodyWords : DepWindow n where
  cursor : Fin.val using Fin.val_injective,
  table : blockWords

end

/-- Faithful four-word Sigma encoding of `(n : ℕ) × DepWindow n`. -/
@[expose] def depWindowWords : (Σ n, DepWindow n) ↪ (Fin 4 → ℕ) :=
  sigmaWords wordWords fun _ => depWindowBodyWords

theorem depWindowWords_coords (n : ℕ) (c : Fin (n + 1)) (base len : ℕ) :
    depWindowWords ⟨n, ⟨c, ⟨base, len⟩⟩⟩ 0 = n ∧
      depWindowWords ⟨n, ⟨c, ⟨base, len⟩⟩⟩ 1 = c.val ∧
      depWindowWords ⟨n, ⟨c, ⟨base, len⟩⟩⟩ 2 = base ∧
      depWindowWords ⟨n, ⟨c, ⟨base, len⟩⟩⟩ 3 = len :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## 2. Exact word-layout preservation on migrated repository types -/

theorem memoryStack_layoutWords_eq (cb cl ib il : ℕ) :
    MemoryStack.layoutWords ⟨⟨cb, cl⟩, ⟨ib, il⟩⟩ = ![cb, cl, ib, il] := by
  funext i
  fin_cases i <;> rfl

theorem binaryHeap_layoutWords_eq (n sb sl ab : ℕ) :
    BinaryHeap.Native.layoutWords ⟨n, ⟨⟨sb, sl⟩, ab⟩⟩ = ![n, sb, sl, ab] := by
  funext i
  fin_cases i <;> rfl

theorem fibonacci_layoutWords_eq (n base : ℕ) :
    Fibonacci.layoutWords ⟨n, base⟩ = ![n, base] := by
  funext i
  fin_cases i <;> rfl

/-! ## 3. End-to-end `realize` round-trip over `word_enc_structure` encodings -/

/-- Read at `block.base + bounds.lo`, write `val + tag` to `block.base + bounds.hi`, and return
the updated `InnerPair` `⟨bounds.hi, bounds.lo + 1⟩`. -/
@[expose] def swapAndAdvance (x : NestedSpan) : Memory.Prog InnerPair := do
  let v ← Memory.read (x.block.base + x.bounds.lo)
  Memory.write (x.block.base + x.bounds.hi) (v + x.tag)
  pure ⟨x.bounds.hi, x.bounds.lo + 1⟩

theorem swapAndAdvance_realizes : Realizes .exact swapAndAdvance
    nestedSpanWords innerPairWords
    (fun w x s =>
      Fits w (x.block.base + x.bounds.lo) ∧
        Fits w (x.block.base + x.bounds.hi) ∧
        Fits w (s.mem (x.block.base + x.bounds.lo) + x.tag) ∧
        Fits w (x.bounds.lo + 1))
    (fun _ _ => 0) := by
  unfold swapAndAdvance
  realize
  all_goals first | exact h.1 | exact h.2.1 | exact h.2.2.1 | exact h.2.2.2

/-! ## 4. Shared `Dijkstra.Native.Common` kernel nonvacuity and execution -/

theorem nativeMethods_widths :
    Binary.nativeMethods.width = 4 ∧ Fibonacci.nativeMethods.width = 2 :=
  ⟨rfl, rfl⟩

/-- Concrete two-vertex graph `0 → 1` of weight `7` from source `0`. -/
@[expose] def twoVertexEdge : ListInstance where
  n := 2
  adj := ![[(1, 7)], []]
  source := 0

private theorem fits_twoVertexEdge :
    Fits 9 (8 * (twoVertexEdge.n + twoVertexEdge.m + 2) * (twoVertexEdge.maxWeight + 2)) := by
  decide

/-- Both `Binary.nativeMethods` and `Fibonacci.nativeMethods` inhabit the shared
`NativeMethods.targetSafe` precondition on the actual post-allocation state of `twoVertexEdge`. -/
theorem targetSafe_nonvacuous_both :
    (∃ e t s, Binary.nativeMethods.targetSafe 9 (e, t) s) ∧
      (∃ e t s, Fibonacci.nativeMethods.targetSafe 9 (e, t) s) := by
  have hGen (M : NativeMethods) (A : NativeAllocator M) :
      ∃ e t s, M.targetSafe 9 (e, t) s := by
    let f := (Memory.State.init twoVertexEdge.encode).frontier
    let e := A.allocated twoVertexEdge.n (f + twoVertexEdge.n)
    let s : Memory.State :=
      ⟨(Memory.State.init twoVertexEdge.encode).mem,
        f + twoVertexEdge.n + A.span twoVertexEdge.n⟩
    obtain ⟨hV, hInv, hAbs, hRoom, hFp⟩ := A.init_empty twoVertexEdge fits_twoVertexEdge
    refine ⟨e, ⟨⟨f, twoVertexEdge.n⟩, 1, 0, 7⟩, s, twoVertexEdge.n,
      by change 1 < twoVertexEdge.n; decide,
      twoVertexEdge.n * twoVertexEdge.maxWeight, hV, hInv, ?_, ?_, rfl, ?_,
      by change Fits 9 (0 + 7 + 1); decide, ?_⟩
    · dsimp only [s]
      rw [hRoom, Nat.add_zero]
      exact A.fits_alloc twoVertexEdge fits_twoVertexEdge
    · change f + twoVertexEdge.n ≤ f + twoVertexEdge.n + A.span twoVertexEdge.n
      omega
    · rw [Finset.disjoint_left]
      intro a ha hb
      have h1 := hFp a ha
      simp only [Block.mem_footprint, Block.Owns] at hb
      omega
    · have hdec : Dictionary.Memory.decode (s.mem (f + 1)) = none := by
        rw [zeroAbove_init twoVertexEdge.encode (f + 1) (by omega)]
        rfl
      dsimp only
      rw [hdec]
      exact ⟨hAbs ⟨1, by decide⟩, by decide⟩
  exact ⟨hGen Binary.nativeMethods Binary.nativeAllocator,
    hGen Fibonacci.nativeMethods Fibonacci.nativeAllocator⟩

/-- Executing the shared `target_realizes` emitter instantiated on `Fibonacci.nativeMethods`
on a concrete 9-bit `Data` state relaxes vertex `1` to distance `0 + 7` (encoded as `8` in the
distance table) and preserves uninvolved caller registers. -/
theorem fibonacci_target_exec :
    ∃ (r C : ℕ) (code : Code .exact r) (frontier sentinel : Fin r) (x y : Data r),
      sentinel ≠ frontier ∧
      ExecWithin 9 code x y (C * 200) ∧
      y.mem ((Memory.State.init twoVertexEdge.encode).frontier + 1) = 8 ∧
      y.regs sentinel = x.regs sentinel := by
  obtain ⟨nScratch, C, emit, hspec⟩ := Fibonacci.nativeMethods.target_realizes
  let r := 1 + 7 + (0 + nScratch + 1) + 1
  let frontier : Fin r := ⟨0, by omega⟩
  let src : Fin 7 → Fin r := fun i => ⟨1 + i.val, by omega⟩
  let tmp : Fin (0 + nScratch + 1) → Fin r := fun j => ⟨8 + j.val, by omega⟩
  let sentinel : Fin r := ⟨8 + (0 + nScratch + 1), by omega⟩
  have hTmpInj : Function.Injective tmp := by
    intro i j h
    ext
    have := congrArg Fin.val h
    dsimp only [tmp] at this
    omega
  have hDisj : ∀ i j, src i ≠ tmp j := by
    intro i j h
    have := congrArg Fin.val h
    dsimp only [src, tmp] at this
    omega
  have hTmpFr : ∀ j, tmp j ≠ frontier := by
    intro j h
    have := congrArg Fin.val h
    dsimp only [tmp, frontier] at this
    omega
  have hSrcFr : ∀ i, src i ≠ frontier := by
    intro i h
    have := congrArg Fin.val h
    dsimp only [src, frontier] at this
    omega
  let f := (Memory.State.init twoVertexEdge.encode).frontier
  let e : Fibonacci.HeapLayout := ⟨twoVertexEdge.n, f + twoVertexEdge.n⟩
  let t : TargetData := ⟨⟨f, twoVertexEdge.n⟩, 1, 0, 7⟩
  let frVal := f + twoVertexEdge.n + (9 * twoVertexEdge.n + 5)
  let inWords := appendWords Fibonacci.layoutWords targetDataWords (e, t)
  let regs : Fin r → ℕ := fun k =>
    if k.val = 0 then frVal
    else if hk : k.val - 1 < 7 then inWords ⟨k.val - 1, hk⟩
    else if k = sentinel then 42
    else 0
  let x : Data r := { regs := regs, mem := (Memory.State.init twoVertexEdge.encode).mem }
  have hfEq : f = 8 := by
    dsimp only [f]
    rw [Memory.frontier_init twoVertexEdge]
    decide
  have hBounded : x.Bounded 9 := by
    refine ⟨?_, ?_⟩
    · intro k
      dsimp only [x, regs]
      by_cases h0 : k.val = 0
      · rw [ite_eq_left h0]
        dsimp only [frVal, twoVertexEdge]
        rw [hfEq]
        decide
      · rw [ite_eq_right h0]
        by_cases hk : k.val - 1 < 7
        · rw [dite_eq_left hk]
          have hInFit : ∀ idx : Fin 7, Fits 9 (inWords idx) := by
            intro idx
            fin_cases idx <;> (dsimp only [inWords, e, t, twoVertexEdge]; rw [hfEq]; decide)
          exact hInFit ⟨k.val - 1, hk⟩
        · rw [dite_eq_right hk]
          by_cases hs : k = sentinel
          · rw [ite_eq_left hs]
            decide
          · rw [ite_eq_right hs]
            decide
    · intro a
      by_cases ha : a < f
      · have hLow : ∀ b < 8, Fits 9 ((Memory.State.init twoVertexEdge.encode).mem b) := by
          decide
        exact hLow a (hfEq ▸ ha)
      · have hz : x.mem a = 0 := zeroAbove_init twoVertexEdge.encode a (Nat.le_of_not_lt ha)
        rw [hz]
        decide
  have hIn : x.regs ∘ src = inWords := by
    funext i
    have hi0 : 1 + i.val ≠ 0 := by omega
    have hi7 : (1 + i.val) - 1 < 7 := by omega
    dsimp only [Function.comp_apply, x, regs, src]
    rw [ite_eq_right hi0, dite_eq_left hi7]
    congr 1
    ext
    dsimp only
    omega
  have hMemSt : memoryState frontier x = ⟨(Memory.State.init twoVertexEdge.encode).mem, frVal⟩ :=
    rfl
  obtain ⟨hV, hInv, hAbs, _, hFp⟩ :=
    Fibonacci.nativeAllocator.init_empty twoVertexEdge fits_twoVertexEdge
  have hSafe : Fibonacci.nativeMethods.targetSafe 9 (e, t) (memoryState frontier x) := by
    rw [hMemSt]
    refine ⟨twoVertexEdge.n, by change 1 < twoVertexEdge.n; decide,
      twoVertexEdge.n * twoVertexEdge.maxWeight, hV, hInv,
      Fibonacci.nativeAllocator.fits_alloc twoVertexEdge fits_twoVertexEdge, ?_, rfl, ?_,
      by change Fits 9 (0 + 7 + 1); decide, ?_⟩
    · change f + twoVertexEdge.n ≤ frVal
      dsimp only [frVal]
      omega
    · rw [Finset.disjoint_left]
      intro a ha hb
      have h1 : f + twoVertexEdge.n ≤ a := hFp a ha
      simp only [Block.mem_footprint, Block.Owns] at hb
      dsimp only [t] at hb
      omega
    · have hdec :
          Dictionary.Memory.decode ((Memory.State.init twoVertexEdge.encode).mem (f + 1)) =
            none := by
        rw [zeroAbove_init twoVertexEdge.encode (f + 1) (by omega)]
        rfl
      dsimp only [t]
      rw [hdec]
      exact ⟨hAbs ⟨1, by decide⟩, by decide⟩
  have hProgRun :
      let prog := relaxTarget (Fibonacci.nativeMethods.insert e)
        (Fibonacci.nativeMethods.decreaseKey e) t.table t.vertex t.dist t.weight
      (Memory.spec 9).ValidHistory (memoryState frontier x)
        ((Memory.spec 9).clientHistory (memoryState frontier x) prog) ∧
      ((Memory.spec 9).clientState (memoryState frontier x) prog).mem (f + 1) = 8 ∧
      memoryCost prog (memoryState frontier x) ≤ 199 := by
    rw [hMemSt]
    dsimp only [e, t, frVal]
    rw [hfEq]
    decide +kernel
  obtain ⟨y, hExec, hSt, _, hFrame⟩ :=
    (hspec frontier src tmp hTmpInj hDisj hTmpFr hSrcFr).2 9 (e, t) x hBounded hIn hSafe
      hProgRun.1
  have hSentFr : sentinel ≠ frontier := by
    intro h
    have := congrArg Fin.val h
    dsimp only [sentinel, frontier] at this
    omega
  have hSentTmp : ∀ j, tmp j ≠ sentinel := by
    intro j h
    have := congrArg Fin.val h
    dsimp only [tmp, sentinel] at this
    omega
  refine ⟨r, C, emit frontier src tmp, frontier, sentinel, x, y, hSentFr, ?_, ?_,
    hFrame sentinel hSentFr hSentTmp⟩
  · refine hExec.mono (Nat.mul_le_mul_left C ?_)
    have hCost := hProgRun.2.2
    dsimp only at hCost ⊢
    omega
  · have hMemEq := congrArg (fun s : Memory.State => s.mem (f + 1)) hSt
    exact hMemEq.trans hProgRun.2.1

end CslibFrontierTests.WordEncStructureDijkstra
