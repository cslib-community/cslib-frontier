/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Dijkstra.Native.Common
public import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
public import CslibFrontier.DataStructure.PriorityQueue.BinaryHeap.Native.Backend
public import CslibFrontier.DataStructure.PriorityQueue.BinaryHeap.Native.Initialize
import CslibFrontier.Algorithms.Lean.Dijkstra.Native.Export
import CslibFrontier.Algorithms.WordRAM.Dijkstra.ListEncode

/-!
# Native binary-heap Dijkstra from the memory client

`Dijkstra.Memory.run` is realized by instantiating the shared `Dijkstra.Native.NativeMethods` and
`Dijkstra.Native.NativeAllocator` interfaces with `BinaryHeap.Native.HeapLayout` (`layoutWords`),
`BinaryHeap.Memory.framed`, and the native binary-heap update, extraction, and dirty-allocation
certificates.

All register layouts, emitted code and clock factors precede runtime graphs, widths and memory.
The original word envelope is unchanged. Arithmetic, copies, source initialization and control
are charged; the flat endpoint retains the entire final memory and frontier of
`Dijkstra.Memory.run`.

## Main definitions

* `ValidHeap`: static validity witness for a runtime binary-heap handle at capacity `n`.
* `nativeMethods`, `nativeAllocator`: binary-heap instances of the shared native Dijkstra kernel.

## Main results

* `realizes_run`: a uniform native realization of the original allocated memory program.
* `exists_program_state`: one flat program with a charged log-linear clock and exact final state.

The instruction factor is existential. No claim preserves the old handwritten implementation's
literal coefficients, and no Fibonacci-heap native endpoint is asserted here.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.Dijkstra.Native.Binary

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.Memory Cslib.DataStructure.PriorityQueue
open Cslib.Algorithms.Dijkstra (ListInstance)
open Cslib.Algorithms.WordRAM.Dijkstra (encodeDist)

/-- Static validity predicate for a runtime binary-heap layout `e` at word width `w`, vertex
capacity `n`, and key bound `K`. -/
structure ValidHeap (w n K : ℕ) (e : BinaryHeap.Native.HeapLayout) : Prop where
  /-- Handle capacity matches `n`. -/
  capacity_eq : e.1 = n
  /-- Underlying layout is valid at width `w` and key bound `K`. -/
  valid : (capacity_eq ▸ e.2).Valid w K

/-- Binary-heap instance of `Dijkstra.Native.NativeMethods` over the 4-word `HeapLayout` register
encoding. -/
@[expose] def nativeMethods : NativeMethods where
  Handle := BinaryHeap.Native.HeapLayout
  width := 4
  handleWords := BinaryHeap.Native.layoutWords
  Valid := ValidHeap
  framed {_ _ _ _} hV := BinaryHeap.Memory.framed hV.valid
  insert e v k := BinaryHeap.Memory.insert e.2 v k
  decreaseKey e v k := BinaryHeap.Memory.decreaseKey e.2 v k
  extractMin e := (BinaryHeap.Memory.extractMin e.2).map (Option.map fun a => (a.1.val, a.2))
  insert_eq := by
    rintro w n K ⟨_, H⟩ ⟨rfl, hH⟩ v k
    rfl
  decreaseKey_eq := by
    rintro w n K ⟨_, H⟩ ⟨rfl, hH⟩ v k
    rfl
  extractMin_eq := by
    rintro w n K ⟨_, H⟩ ⟨rfl, hH⟩
    rfl
  extractMin_query _ s := one_le_memoryCost_liftBind _ _ s
  realizes_insert :=
    (BinaryHeap.Native.realizes_insert.reindex
      (fun d : BinaryHeap.Native.HeapLayout × UpdateArgs => ((d.1, d.2.vertex), d.2.key))
      (appendWords BinaryHeap.Native.layoutWords updateArgsWords)
      ![0, 1, 2, 3, 4, 5] (by intro d i; fin_cases i <;> rfl)).consequence
      (by
        rintro w ⟨⟨_, H⟩, v, k⟩ s _ _ ⟨n, hv, K, ⟨rfl, hH⟩, hi, hop⟩
        exact ⟨hv, K, hH, hi, hop⟩)
      (fun _ _ => le_rfl)
  realizes_decreaseKey :=
    (BinaryHeap.Native.realizes_decreaseKey.reindex
      (fun d : BinaryHeap.Native.HeapLayout × UpdateArgs => ((d.1, d.2.vertex), d.2.key))
      (appendWords BinaryHeap.Native.layoutWords updateArgsWords)
      ![0, 1, 2, 3, 4, 5] (by intro d i; fin_cases i <;> rfl)).consequence
      (by
        rintro w ⟨⟨_, H⟩, v, k⟩ s _ _ ⟨n, hv, K, ⟨rfl, hH⟩, hi, hop⟩
        exact ⟨hv, K, hH, hi, hop⟩)
      (fun _ _ => le_rfl)
  realizes_extractMin :=
    BinaryHeap.Native.realizes_extractMin.consequence
      (by
        rintro w ⟨_, H⟩ s _ _ ⟨n, K, ⟨rfl, hH⟩, hi⟩
        exact ⟨K, hH, hi⟩)
      (fun _ _ => le_rfl)

/-- Dirty-allocation adapter connecting `BinaryHeap.Memory.allocLayout` to `nativeMethods`. -/
@[expose] def nativeAllocator : NativeAllocator nativeMethods where
  alloc n := do
    let H ← BinaryHeap.Memory.allocLayout n
    pure ⟨n, H⟩
  span n := 1 + BinaryHeap.space n
  allocated n b := ⟨n, BinaryHeap.Memory.allocated n b⟩
  run_alloc n s := by
    have h := BinaryHeap.Native.Initialize.allocLayout_run 0 n s
    exact ⟨congrArg Prod.fst h,
      (congrArg (Prod.fst ∘ Prod.snd) h).trans
        (by simp only [Function.comp_apply, Nat.add_assoc])⟩
  realizes_alloc :=
    BinaryHeap.Native.Initialize.realizes_allocLayout.consequence
      (fun _ _ _ _ _ h => by simpa only [Nat.add_assoc] using h)
      (fun _ _ => le_rfl)
  fits_alloc G {_} hfit := by
    rw [Memory.frontier_init G]
    exact hfit.of_le (by unfold BinaryHeap.space; nlinarith)
  init_empty G {w} hfit := by
    let f := (Memory.State.init G.encode).frontier
    let H := BinaryHeap.Memory.allocated G.n (f + G.n)
    have hH : H.Valid w (G.n * G.maxWeight) :=
      BinaryHeap.Memory.valid_allocated (hfit.of_le (by nlinarith))
        (hfit.of_le (by nlinarith))
    obtain ⟨hi, habs⟩ := BinaryHeap.Memory.inv_allocated (n := G.n)
      ((zeroAbove_init G.encode).allocDirty G.n)
    have hst : (⟨(Memory.State.init G.encode).mem, f + G.n + (1 + BinaryHeap.space G.n)⟩ :
        Memory.State) =
        ⟨(Memory.State.init G.encode).mem, f + G.n + 1 + BinaryHeap.space G.n⟩ := by
      simp only [Nat.add_assoc]
    refine ⟨⟨rfl, hH⟩, ?_, ?_, rfl,
      fun _ ha => BinaryHeap.Memory.le_of_mem_footprint_allocated ha⟩
    · change BinaryHeap.Memory.Inv H _
      rw [hst]
      exact hi
    · intro v
      change BinaryHeap.Memory.abs H _ v = none
      rw [hst]
      exact congrFun habs v

/-- One fixed native emitter realizes the original allocated binary-heap Dijkstra memory
program. The domain retains the original graph input and word-size envelope; native arithmetic,
argument delivery, initialization and control are included in its constant instruction factor. -/
theorem realizes_run : Realizes .exact (fun _ : Unit => Memory.run)
    (WordEncoding.encode (α := Unit)) (WordEncoding.encode (α := Unit))
    (fun w _ s => ∃ G : ListInstance, s = Memory.State.init G.encode ∧
      Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) (fun _ _ => 0) :=
  nativeAllocator.realizes_runWord.congr fun _ =>
    runWord_eq_binary _ _ _ (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (fun n H => BinaryHeap.Native.extractMin_observation ⟨n, H⟩)

/-- One flat exact-basis program, chosen before every graph and word size, computes the
shortest-path distances. Its charged prefix, body and halt take log-linear time, and the full
final memory/frontier is exactly the state of the original memory program. -/
theorem exists_program_state :
    ∃ r C pc : ℕ, ∃ prog : Program .exact r, ∃ frontier : Fin r,
      ∀ (G : ListInstance) (w : ℕ), Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) →
        ∃ (y : Data r) (steps : ℕ), Runs w prog (State.init G.encode) ⟨pc, y⟩ steps ∧
          step w prog ⟨pc, y⟩ = .halt 0 ∧
          memoryState frontier y =
            (Memory.spec w).clientState (Memory.State.init G.encode) Memory.run ∧
          steps + 1 ≤ C * (G.m + 1) * (Nat.log 2 G.n + 1) ∧
          ∀ v : Fin G.n, y.mem (G.outAddr v) = encodeDist (G.dist G.source v) := by
  obtain ⟨r, C, pc, prog, frontier, he⟩ :=
    Native.exists_program_state (fun G => Memory.memCost G.n G.m) realizes_run Memory.run_spec
  refine ⟨r, 53 * C, pc, prog, frontier, fun G w hfit => ?_⟩
  obtain ⟨y, steps, hrun, hhalt, hstate, htime, hdist⟩ := he G w hfit
  refine ⟨y, steps, hrun, hhalt, hstate, ?_, hdist⟩
  -- `memCost n m + 1 ≤ 53 (m + 1) (⌊log₂ n⌋ + 1)`.
  unfold Memory.memCost at htime
  have hpos : 1 ≤ (G.m + 1) * (Nat.log 2 G.n + 1) := Nat.mul_pos (by omega) (by omega)
  nlinarith [Nat.mul_le_mul_left C hpos]

end Cslib.Algorithms.Lean.Dijkstra.Native.Binary
