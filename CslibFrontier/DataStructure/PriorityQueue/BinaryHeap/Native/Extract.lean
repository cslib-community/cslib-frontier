/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.BinaryHeap.Native.SiftDown
import CslibFrontier.DataStructure.StateTransition.ClientMap
import CslibFrontier.Tactic.Realize

/-!
# Native extract-min through the original memory program

The uniform result carrier forgets the proof in a `Fin n` handle, retaining its natural value and
key. The observation back to the typed indexed-PQ answer uses the existing `Memory.entry` and is
a left inverse. This changes no query, write, history or memory cost of the original extraction.
The realization stages the computed sift arguments through the sift-down certificate.

## Main results

* `realizes_extractMin`: one native body for the original source, with an encoded natural handle.
* `extractMin_observation`, `extractMin_run`: exact typed observation and full-run transport.

These are installed-register operation certificates, not a heap initializer or a complete client
clock. The existing source correctness and logarithmic memory bound remain the supplier.
-/

@[expose] public section

namespace Cslib.DataStructure.PriorityQueue.BinaryHeap.Native

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.Memory

private def eraseResult {n : ℕ} : Option (Fin n × ℕ) → Option (ℕ × ℕ) :=
  Option.map fun a => (a.1.val, a.2)

private def observeResult (n : ℕ) (a : Option (ℕ × ℕ)) : Option (Fin n × ℕ) :=
  a.bind fun p => Memory.entry n p.1 p.2

private theorem observe_erase {n : ℕ} (a : Option (Fin n × ℕ)) :
    observeResult n (eraseResult a) = a := by
  cases a with
  | none => rfl
  | some a =>
    rcases a with ⟨v, k⟩
    simp only [observeResult, eraseResult, Option.map_some, Option.bind_some,
      Memory.entry, dite_eq_left v.isLt]

/-- Realize the original extraction after erasing only the proof in its handle. The local
sift certificate is reused as a call; its argument staging is part of the native program. -/
theorem realizes_extractMin :
    Realizes .exact (fun d : HeapLayout =>
        (Memory.extractMin d.2).map (Option.map fun a => (a.1.val, a.2))) layoutWords
      (WordEncoding.encode (α := Option (ℕ × ℕ)))
      (fun w d s => ∃ K, d.2.Valid w K ∧ Memory.Inv d.2 s) (fun _ _ => 0) := by
  realize [SiftDown.realizes_siftDown] rewriting [Memory.extractMin, Memory.entry]
  all_goals
    rcases h with ⟨K, hL, hs⟩
    have hSn := hs.heap.size_le
    have hSpos : 1 ≤ s.mem d.2.size.base := by omega
    have hroot := hs.heap.vertex_lt 1 le_rfl hSpos
    have hlast := hs.heap.vertex_lt (s.mem d.2.size.base) hSpos le_rfl
    have hA := hs.arrays_allocated
    change d.2.base + (3 * d.1 + 1) ≤ s.frontier at hA
    first
    | apply hmem.frontier_fits.of_le
      omega
    | omega
    | refine ⟨hL.n_fits, hs.arrays_allocated, (hs.heap.extract (by omega)).1, ?_⟩
      change 1 ≤ s.mem d.2.size.base - 1
      omega

/-- Forgetting only the proof in the source handle and observing it through the existing
checked entry constructor is an exact left inverse on the complete memory program. -/
theorem extractMin_observation (d : HeapLayout) :
    (((Memory.extractMin d.2).map (Option.map fun a => (a.1.val, a.2))).map
      (fun a => a.bind fun p => Memory.entry d.1 p.1 p.2)) = Memory.extractMin d.2 := by
  change ((Memory.extractMin d.2).map eraseResult).map (observeResult d.1) = _
  rw [← PFunctor.FreeM.comp_map]
  have h : observeResult d.1 ∘ eraseResult = id := funext observe_erase
  rw [h]
  exact PFunctor.FreeM.id_map _

/-- The actual encoded extraction result is the original typed answer with only the `Fin`
proof forgotten. In particular, every returned natural handle still satisfies its source bound. -/
theorem extractMin_result (w : ℕ) (d : HeapLayout) (s : Memory.State) :
    (Memory.spec w).clientResult s
        ((Memory.extractMin d.2).map (Option.map fun a => (a.1.val, a.2))) =
      ((Memory.spec w).clientResult s (Memory.extractMin d.2)).map
        (fun a => (a.1.val, a.2)) :=
  congrArg Prod.fst (StateTransitionSpec.runClient_map (D := Memory.spec w)
    (Memory.extractMin d.2) eraseResult s)

/-- The erased result transports the full interpreter run, including its state and history.
This is the actual observation contract needed by the uniform Backend. -/
theorem extractMin_run (w : ℕ) (d : HeapLayout) (s : Memory.State) :
    (Memory.spec w).runClient s (Memory.extractMin d.2) =
      Prod.map (fun a => a.bind fun p => Memory.entry d.1 p.1 p.2) id
        ((Memory.spec w).runClient s
          ((Memory.extractMin d.2).map (Option.map fun a => (a.1.val, a.2)))) := by
  exact (congrArg ((Memory.spec w).runClient s) (extractMin_observation d)).symm.trans
    (StateTransitionSpec.runClient_map _ _ _)

end Cslib.DataStructure.PriorityQueue.BinaryHeap.Native
