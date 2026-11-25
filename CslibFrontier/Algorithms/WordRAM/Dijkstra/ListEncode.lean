/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Dijkstra.HeapStatement
import Mathlib.Tactic.Linarith

/-!
# Dijkstra's algorithm: the adjacency-list input words

This file specializes the shared compressed-sparse-row layout and initial-memory lemmas of
`CslibFrontier.Algorithms.WordRAM.CSR` (`encodeWeight := id`) to
`Cslib.Algorithms.Dijkstra.ListInstance.encode`: `n`, the source, the offsets of the adjacency
lists, and the targets and weights of the edges each sit at the address used by the original linked
memory client and the retained word-RAM priority-queue interface. Memory past the input is `0`.

## Main definitions

* `Cslib.Algorithms.Dijkstra.ListInstance.dbase`: the first address past the input.

## Main results

* `Cslib.Algorithms.Dijkstra.ListInstance.encode_length`: the input has `n + 2 m + 3` words.
* `Cslib.Algorithms.Dijkstra.ListInstance.init_offset`,
  `Cslib.Algorithms.Dijkstra.ListInstance.init_target`,
  `Cslib.Algorithms.Dijkstra.ListInstance.init_weight`: the input words in the initial memory.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.Dijkstra.ListInstance

open Cslib.WordRAM Cslib.Algorithms.WordRAM

variable (G : ListInstance) {r : ℕ}

/-- The first address past the input words: the base of the distance words. -/
def dbase : ℕ := G.n + 2 * G.m + 4

/-- The input has `n + 2 m + 3` words. -/
theorem encode_length : G.encode.length = G.n + 2 * G.m + 3 :=
  CSR.encode_length G.n G.source G.adj id

/-- The offset of `u + 1` is the offset of `u` plus the length of the list of `u`. -/
theorem offset_succ {u : ℕ} (hu : u < G.n) :
    G.offset (u + 1) = G.offset u + (G.adj ⟨u, hu⟩).length :=
  CSR.offset_succ G.n G.adj hu

/-- The offset of `n` is the number of edges. -/
theorem offset_n : G.offset G.n = G.m :=
  CSR.offset_n G.n G.adj

/-- The offsets grow. -/
theorem offset_mono {u v : ℕ} (h : u ≤ v) : G.offset u ≤ G.offset v :=
  CSR.offset_mono G.n G.adj h

/-- Address `1` initially holds `n`. -/
theorem init_n : (Data.init G.encode : Data r).mem 1 = G.n :=
  CSR.init_n G.n G.source G.adj id

/-- Address `2` initially holds the source. -/
theorem init_source : (Data.init G.encode : Data r).mem 2 = G.source :=
  CSR.init_source G.n G.source G.adj id

/-- Address `u + 3` initially holds the offset of `u`, for `u ≤ n`. -/
theorem init_offset {u : ℕ} (hu : u ≤ G.n) :
    (Data.init G.encode : Data r).mem (u + 3) = G.offset u :=
  CSR.init_offset G.n G.source G.adj id hu

/-- The target of edge `i` out of `u` is initially at address `2 (offset u + i) + n + 4`. -/
theorem init_target (u : Fin G.n) {i : ℕ} (hi : i < (G.adj u).length) :
    (Data.init G.encode : Data r).mem (2 * (G.offset u + i) + G.n + 4) = ((G.adj u)[i].1 : ℕ) :=
  CSR.init_target G.n G.source G.adj id u hi

/-- The weight of edge `i` out of `u` is initially at address `2 (offset u + i) + n + 5`. -/
theorem init_weight (u : Fin G.n) {i : ℕ} (hi : i < (G.adj u).length) :
    (Data.init G.encode : Data r).mem (2 * (G.offset u + i) + G.n + 5) = (G.adj u)[i].2 :=
  CSR.init_weight G.n G.source G.adj id u hi

/-- Memory past the input is initially `0`. -/
theorem init_past {a : ℕ} (ha : G.dbase ≤ a) : (Data.init G.encode : Data r).mem a = 0 :=
  CSR.init_past G.n G.source G.adj id ha

/-- The original adjacency-list input fits whenever the advertised Dijkstra word envelope fits. -/
theorem inputFits_encode (G : ListInstance) {w : ℕ}
    (hw_in : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) :
    InputFits w G.encode :=
  CSR.inputFits_encode G.n G.source G.adj id (by change G.n + 2 * G.m + 3 ≤ _; nlinarith)
    (fun _ _ he => by dsimp only [id]; have := G.le_maxWeight he; nlinarith) hw_in

end Cslib.Algorithms.Dijkstra.ListInstance
