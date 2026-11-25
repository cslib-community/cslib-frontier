/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.IterativeCompression.OddCycleTransversal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Input encoding and workspace layout for Word-RAM odd cycle transversal

This module collects the pure input encoding (`encodeAdjMatrix`, `encodeInput`) and linear
workspace address offsets shared across the `OddCycleTransversal` Word-RAM implementation,
including the `(2n + 2)`-vertex split-network node indices `inIdx` and `outIdx`.

## Main definitions

* `Cslib.Algorithms.WordRAM.OddCycleTransversal.encodeAdjMatrix`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.encodeInput`: row-major adjacency matrix encoding
  and prefixed input list `n :: k :: encodeAdjMatrix G`.
* `Cslib.Algorithms.WordRAM.OddCycleTransversal.sepAddr`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.colAddr`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.octWorkspace`: output transversal/colouring
  addresses and total workspace frontier `5 * n ^ 2 + 21 * n + 11`.
* `Cslib.Algorithms.WordRAM.OddCycleTransversal.inIdx`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.outIdx`: split-network in/out vertex indices.

## Main results

* `Cslib.Algorithms.WordRAM.OddCycleTransversal.length_encodeAdjMatrix`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.length_encodeInput`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.getElem_encodeAdjMatrix`: length and entry
  characterizations of the adjacency-matrix encoding.
* `Cslib.Algorithms.WordRAM.OddCycleTransversal.inIdx_injective`: injectivity of `inIdx`.
-/

public section

namespace Cslib.Algorithms.WordRAM.OddCycleTransversal

/-! ### Input encoding and workspace layout -/

/-- Row-major `n * n`-word `0`/`1` adjacency matrix of `G : SimpleGraph (Fin n)`. -/
@[expose] def encodeAdjMatrix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : List ℕ :=
  List.ofFn fun idx : Fin (n * n) =>
    if G.Adj ⟨idx.1 / n, Nat.div_lt_of_lt_mul idx.2⟩
        ⟨idx.1 % n, Nat.mod_lt _ (Nat.pos_of_mul_pos_left (Nat.zero_lt_of_lt idx.2))⟩ then 1 else 0

/-- Word-RAM input word list `n :: k :: encodeAdjMatrix G`. -/
@[expose] def encodeInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    List ℕ :=
  n :: k :: encodeAdjMatrix G

@[simp]
theorem length_encodeAdjMatrix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (encodeAdjMatrix G).length = n * n := by
  simp [encodeAdjMatrix]

@[simp]
theorem length_encodeInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    (encodeInput G k).length = 2 + n * n := by
  simp only [encodeInput, List.length_cons, length_encodeAdjMatrix]
  omega

theorem getElem_encodeAdjMatrix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) :
    (encodeAdjMatrix G)[u.1 * n + v.1]'(by
      rw [length_encodeAdjMatrix]; nlinarith [u.2, v.2]) =
      if G.Adj u v then 1 else 0 := by
  simp only [encodeAdjMatrix, List.getElem_ofFn]
  have hu : u.1 * n + v.1 = v.1 + n * u.1 := by ring
  have hn_pos : 0 < n := Nat.zero_lt_of_lt u.2
  have hdiv : (u.1 * n + v.1) / n = u.1 := by
    rw [hu, Nat.add_mul_div_left _ _ hn_pos]
    simp [Nat.div_eq_of_lt v.2]
  have hmod : (u.1 * n + v.1) % n = v.1 := by
    rw [hu, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt v.2]
  have h1 : G.Adj ⟨(u.1 * n + v.1) / n,
      Nat.div_lt_of_lt_mul (by nlinarith [u.2, v.2] : u.1 * n + v.1 < n * n)⟩
      ⟨(u.1 * n + v.1) % n, Nat.mod_lt _ hn_pos⟩ ↔ G.Adj u v := by
    refine Iff.of_eq ?_
    congr 1
    · exact Fin.ext hdiv
    · exact Fin.ext hmod
  simp only [h1]

/-- Number of vertices `n + n + 2` in the vertex-split network of an `n`-vertex graph. -/
abbrev splitCount (n : ℕ) : ℕ := n + n + 2

/-- Output address storing the `0`/`1` transversal indicator of vertex `v` (`3 + n * n + v`). -/
@[expose] def sepAddr (n v : ℕ) : ℕ := 3 + n * n + v

/-- Output address storing the `0`/`1` proper colouring bit of vertex `v`
(`3 + n * n + n + v`). -/
@[expose] def colAddr (n v : ℕ) : ℕ := 3 + n * n + n + v

/-- Base address of the `0`/`1` transversal indicator slice. -/
abbrev sepBase (n : ℕ) : ℕ := 3 + n * n
/-- Base address of the `0`/`1` proper colouring slice. -/
abbrev colBase (n : ℕ) : ℕ := 3 + n * n + n
/-- Base address of the candidate-set `W` indicator slice. -/
abbrev wBase (n : ℕ) : ℕ := 3 + n * n + 2 * n
/-- Base address of the compacted vertex list `W`. -/
abbrev wListBase (n : ℕ) : ℕ := 3 + n * n + 3 * n
/-- Base address of the base-3 odometer digits for `W`. -/
abbrev digitBase (n : ℕ) : ℕ := 3 + n * n + 4 * n
/-- Base address of the unpacked guess-role slice. -/
abbrev guessBase (n : ℕ) : ℕ := 3 + n * n + 5 * n
/-- Base address of the keep-terminal indicator slice. -/
abbrev keepBase (n : ℕ) : ℕ := 3 + n * n + 6 * n
/-- Base address of the flip-terminal indicator slice. -/
abbrev flipBase (n : ℕ) : ℕ := 3 + n * n + 7 * n
/-- Base address of the flattened split-network flow matrix. -/
abbrev flowBase (n : ℕ) : ℕ := 3 + n * n + 8 * n
/-- Base address of the BFS distance array. -/
abbrev distBase (n : ℕ) : ℕ := flowBase n + splitCount n * splitCount n
/-- Base address of the BFS parent array. -/
abbrev parBase (n : ℕ) : ℕ := distBase n + splitCount n
/-- Base address of the extracted separator indicator array. -/
abbrev sepOutBase (n : ℕ) : ℕ := parBase n + splitCount n

/-- Total scratch words allocated past `3 + n * n`. -/
abbrev octScratch (n : ℕ) : ℕ :=
  9 * n + splitCount n * splitCount n + 2 * splitCount n

/-- Total memory frontier `5 * (n * n) + 21 * n + 11` (`= 3 + n * n + octScratch n`) used by the
Word-RAM odd-cycle-transversal solver. -/
@[expose] def octWorkspace (n : ℕ) : ℕ :=
  5 * (n * n) + 21 * n + 11

/-- `3 + n * n + octScratch n = octWorkspace n`. -/
theorem frontier_add_octScratch (n : ℕ) :
    3 + n * n + octScratch n = octWorkspace n := by
  unfold octWorkspace octScratch splitCount
  ring

/-- Expanded form of `splitCount n * splitCount n`. -/
theorem splitCount_sq (n : ℕ) :
    (n + n + 2) * (n + n + 2) = 4 * (n * n) + 8 * n + 4 := by
  ring

/-- In-vertex index `v + 2` inside the `(2n + 2)`-vertex split network. -/
@[expose] def inIdx {n : ℕ} (v : Fin n) : Fin (splitCount n) :=
  ⟨v.1 + 2, by dsimp only [splitCount]; omega⟩

/-- Out-vertex index `v + n + 2` inside the `(2n + 2)`-vertex split network. -/
@[expose] def outIdx {n : ℕ} (v : Fin n) : Fin (splitCount n) :=
  ⟨v.1 + n + 2, by dsimp only [splitCount]; omega⟩

/-- `inIdx` is injective. -/
theorem inIdx_injective (n : ℕ) : Function.Injective (inIdx (n := n)) := by
  intro u v h
  exact Fin.ext (by have := congrArg Fin.val h; dsimp only [inIdx] at this; omega)

end Cslib.Algorithms.WordRAM.OddCycleTransversal
