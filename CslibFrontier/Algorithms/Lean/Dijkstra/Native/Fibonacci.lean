/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Dijkstra.Native.Common
public import CslibFrontier.Algorithms.Lean.Dijkstra.Native.Fibonacci.Cost
public import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Backend
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Initialize
import CslibFrontier.Algorithms.Lean.Dijkstra.Native.Export
import CslibFrontier.Algorithms.WordRAM.Dijkstra.ListEncode
import CslibFrontier.Tactic.Realize

/-!
# Native Fibonacci-heap Dijkstra from the existing framed memory client

`Dijkstra.Native.Fibonacci.run` is realized by instantiating the shared
`Dijkstra.Native.NativeMethods` and `Dijkstra.Native.NativeAllocator` interfaces with the 2-word
`HeapLayout` record (`word_enc_structure layoutWords`), `FibonacciHeap.framed`, and the native
Fibonacci-heap update, extraction, and dirty-reservation certificates.

The original amortized potential pays for memory operations; the native code separately charges
arithmetic, argument copies, loop control and initialization. Flat exports retain the original
graph input and word envelope, include their real prefix and halt, and preserve the full final
memory.

## Main definitions

* `HeapLayout`, `layoutWords`: 2-word runtime Fibonacci-heap handle and its register encoding.
* `ValidHeap`: static validity witness for a runtime Fibonacci-heap handle at capacity `n`.
* `nativeMethods`, `nativeAllocator`: Fibonacci-heap instances of the shared native Dijkstra kernel.

## Main results

* `realizes_run`: one uniform emitter for the original allocated Fibonacci memory client.
* `exists_program_state`: its sharper halt-inclusive flat clock and exact whole-state export.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [M. L. Fredman and R. E. Tarjan, *Fibonacci heaps and their uses in improved network
  optimization algorithms*][FredmanTarjan1987]
-/

public section

namespace Cslib.Algorithms.Lean.Dijkstra.Native.Fibonacci

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.Memory Cslib.DataStructure.PriorityQueue
open Cslib.Algorithms.Dijkstra (ListInstance)
open Cslib.Algorithms.WordRAM.Dijkstra (encodeDist)

/-- Runtime layout of an allocated indexed Fibonacci heap: vertex capacity `capacity` and base
address `base` of its `9 * capacity + 5` contiguous cells. -/
structure HeapLayout where
  /-- Maximum number of handles `n`. -/
  capacity : ℕ
  /-- Base address of the heap's storage block. -/
  base : ℕ

/-- Faithful two-word register encoding of `HeapLayout`. -/
word_enc_structure layoutWords : HeapLayout where
  capacity : wordWords,
  base : wordWords

/-- Static validity predicate for a runtime Fibonacci-heap handle `e` at word width `w`, vertex
capacity `n`, and key bound `K`. -/
structure ValidHeap (w n K : ℕ) (e : HeapLayout) : Prop where
  /-- Handle capacity matches `n`. -/
  capacity_eq : e.capacity = n
  /-- Vertex capacity `n` fits in `w` bits. -/
  fits_n : Fits w n
  /-- Key bound `K` fits in `w` bits. -/
  fits_K : Fits w K
  /-- End of the `9 * n + 5` cell block fits in `w` bits. -/
  fits_window : Fits w (e.base + (9 * n + 5))

/-- Fibonacci-heap instance of `Dijkstra.Native.NativeMethods` over the 2-word `HeapLayout`
register encoding. -/
@[expose] def nativeMethods : NativeMethods where
  Handle := HeapLayout
  width := 2
  handleWords := layoutWords
  Valid := ValidHeap
  framed {_ _ _} {e} hV := FibonacciHeap.framed hV.fits_n hV.fits_K e.base
  insert e v k := link ((FibonacciHeap.layout e.capacity e.base).methods 0)
    (FibonacciHeap.insert v k)
  decreaseKey e v k := link ((FibonacciHeap.layout e.capacity e.base).methods 0)
    (FibonacciHeap.decreaseKey e.capacity v k)
  extractMin e := link ((FibonacciHeap.layout e.capacity e.base).methods 0)
    (FibonacciHeap.Native.extractRaw e.capacity)
  insert_eq := by
    rintro w n K ⟨_, base⟩ ⟨rfl, _, _, _⟩ v k
    exact (FibonacciHeap.Native.link_width base w (FibonacciHeap.insert v.val k)).symm
  decreaseKey_eq := by
    rintro w n K ⟨cap, base⟩ ⟨rfl, _, _, _⟩ v k
    exact (FibonacciHeap.Native.link_width base w (FibonacciHeap.decreaseKey cap v.val k)).symm
  extractMin_eq := by
    rintro w n K ⟨cap, base⟩ ⟨rfl, _, _, _⟩
    change link ((FibonacciHeap.layout cap base).methods 0)
        (FibonacciHeap.Native.extractRaw cap) =
      (pqMethods cap K w base .extractMin).map (Option.map fun p => (p.1.val, p.2))
    simp only [pqMethods, FibonacciHeap.methods,
      FibonacciHeap.Native.link_extractRaw_eq, FibonacciHeap.Native.link_width]
    rfl
  extractMin_query _ s := one_le_memoryCost_liftBind _ _ s
  realizes_insert :=
    (FibonacciHeap.Native.realizes_insert.reindex
      (fun d : HeapLayout × UpdateArgs => ![d.1.capacity, d.1.base, d.2.vertex, d.2.key])
      (appendWords layoutWords updateArgsWords) ![0, 1, 2, 3]
      (by intro d i; fin_cases i <;> rfl)).consequence
      (by
        rintro w ⟨⟨_, base⟩, v, k⟩ s _ _ ⟨n, hv, K, ⟨rfl, _, _, hwin⟩, _, _⟩
        exact ⟨hwin, hv⟩)
      (fun _ _ => le_rfl)
  realizes_decreaseKey :=
    (FibonacciHeap.Native.realizes_decreaseKey.reindex
      (fun d : HeapLayout × UpdateArgs => ![d.1.capacity, d.1.base, d.2.vertex, d.2.key])
      (appendWords layoutWords updateArgsWords) ![0, 1, 2, 3]
      (by intro d i; fin_cases i <;> rfl)).consequence
      (by
        rintro w ⟨⟨_, base⟩, v, k⟩ s _ _ ⟨n, hv, K, ⟨rfl, _, hK, hwin⟩, ⟨halloc, hI⟩,
          ⟨old, hOld, hle⟩, hkey⟩
        exact ⟨hwin, halloc, ⟨v, hv⟩, K, old, rfl, hK, hI, hOld, hle, hkey⟩)
      (fun _ _ => le_rfl)
  realizes_extractMin :=
    (FibonacciHeap.Native.realizes_extractRaw.reindex
      (fun e : HeapLayout => ![e.capacity, e.base])
      layoutWords ![0, 1] (by intro e i; fin_cases i <;> rfl)).consequence
      (by
        rintro w ⟨_, base⟩ s _ _ ⟨n, K, ⟨rfl, _, hK, hwin⟩, halloc, hI⟩
        exact ⟨hwin, halloc, K, hK, hI⟩)
      (fun _ _ => le_rfl)

private def allocHeapLayout (n : ℕ) : Memory.Prog HeapLayout := do
  let base ← Memory.allocDirty (9 * n + 5)
  pure ⟨n, base⟩

private theorem allocHeapLayout_realizes : Realizes .exact allocHeapLayout wordWords layoutWords
    (fun w n s => Fits w (s.frontier + (9 * n + 5))) (fun _ _ => 0) := by
  unfold allocHeapLayout
  realize [FibonacciHeap.Native.Initialize.realizes_reserve]
  exact h

/-- Dirty-reservation adapter connecting `Memory.allocDirty (9 * n + 5)` to `nativeMethods`. -/
@[expose] def nativeAllocator : NativeAllocator nativeMethods where
  alloc n := do
    let base ← Memory.allocDirty (9 * n + 5)
    pure ⟨n, base⟩
  span n := 9 * n + 5
  allocated n b := ⟨n, b⟩
  run_alloc _ _ := ⟨rfl, rfl⟩
  realizes_alloc := by exact allocHeapLayout_realizes
  fits_alloc G {_} hfit := by
    rw [Memory.frontier_init G]
    exact hfit.of_le (by nlinarith)
  init_empty G {w} hfit := by
    let f := (Memory.State.init G.encode).frontier
    have hn : Fits w G.n := hfit.of_le (by nlinarith)
    have hK : Fits w (G.n * G.maxWeight) := hfit.of_le (by nlinarith)
    have hwin : Fits w (f + G.n + (9 * G.n + 5)) := by
      dsimp only [f]
      rw [Memory.frontier_init G]
      exact hfit.of_le (by nlinarith)
    obtain ⟨hinv, habs⟩ := FibonacciHeap.framed_allocDirty hn hK
      ((zeroAbove_init G.encode).allocDirty G.n)
    refine ⟨⟨rfl, hn, hK, hwin⟩, hinv, fun v => congrFun habs v, rfl, ?_⟩
    intro a ha
    change a ∈ FibonacciHeap.footprint G.n (f + G.n) at ha
    simp only [FibonacciHeap.footprint, Finset.mem_Ico] at ha
    exact ha.1

/-- One native emitter realizes the original Fibonacci-heap Dijkstra memory client. Its
domain retains the unchanged graph encoding and word envelope. Arithmetic, argument delivery,
dirty allocation and early-exit loop control are included in the uniform instruction factor. -/
theorem realizes_run : Realizes .exact (fun _ : Unit => run)
    (WordEncoding.encode (α := Unit)) (WordEncoding.encode (α := Unit))
    (fun w _ s => ∃ G : ListInstance, s = Memory.State.init G.encode ∧
      Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) (fun _ _ => 0) := by
  refine nativeAllocator.realizes_runWord.congr fun _ => ?_
  refine Eq.trans ?_ runWord_eq
  unfold runWord nativeAllocator nativeMethods
  simp only [bind_assoc, pure_bind]

/-- One flat exact-basis program, chosen before all graphs and widths, computes every distance
within the sharper reachable-vertex Fibonacci bound. Its actual prefix, memory client and halt
are charged, and its entire final memory/frontier is the original memory client's final state.
As in the statement specification, placing the raw graph words in `Data.init` is uncharged. -/
theorem exists_program_state :
    ∃ r C pc : ℕ, ∃ prog : Program .exact r, ∃ frontier : Fin r,
      ∀ (G : ListInstance) (w : ℕ), Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) →
        ∃ (y : Data r) (steps : ℕ), Runs w prog (State.init G.encode) ⟨pc, y⟩ steps ∧
          step w prog ⟨pc, y⟩ = .halt 0 ∧
          memoryState frontier y =
            (Memory.spec w).clientState (Memory.State.init G.encode) run ∧
          steps + 1 ≤ C * (G.m + min G.n (G.m + 1) * (Nat.log 2 G.n + 1)) ∧
          ∀ v : Fin G.n, y.mem (G.outAddr v) = encodeDist (G.dist G.source v) := by
  obtain ⟨r, C, pc, prog, frontier, he⟩ := Native.exists_program_state
    (fun G => 400 * (G.m + min G.n (G.m + 1) * (Nat.log 2 G.n + 1))) realizes_run run_spec
  refine ⟨r, 401 * C, pc, prog, frontier, fun G w hfit => ?_⟩
  obtain ⟨y, steps, hrun, hhalt, hstate, htime, hdist⟩ := he G w hfit
  refine ⟨y, steps, hrun, hhalt, hstate, ?_, hdist⟩
  -- The bound is positive, since the source is a vertex.
  have hn : 1 ≤ G.n := by have := G.source.isLt; omega
  have hmin : 1 ≤ min G.n (G.m + 1) := le_min hn (by omega)
  have hpos : 1 ≤ G.m + min G.n (G.m + 1) * (Nat.log 2 G.n + 1) := by
    have := Nat.mul_le_mul hmin (show 1 ≤ Nat.log 2 G.n + 1 by omega)
    omega
  nlinarith [Nat.mul_le_mul_left C hpos]

end Cslib.Algorithms.Lean.Dijkstra.Native.Fibonacci
