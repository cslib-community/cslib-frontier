/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Time
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Ring

/-!
# Compressed-sparse-row word encoding of weighted directed graphs

Shared input word-list layout and `Cslib.WordRAM.Data.init` memory-readback lemmas for weighted
directed multigraphs on `Fin n` given by adjacency lists `adj : Fin n → List (Fin n × W)`, a
source vertex `source : Fin n`, and an edge-weight encoder `encodeWeight : W → ℕ`.

The encoded word list (`Cslib.Algorithms.WordRAM.CSR.encode`) stores:
* `n`, the number of vertices;
* `source`, the source vertex;
* the `n + 1` cumulative edge offsets `offset 0, …, offset n`;
* the `m` edges in vertex order as pairs `(target, encodeWeight weight)`.

Used by both `CslibFrontier.Algorithms.WordRAM.Dijkstra` (`encodeWeight := id` on `ℕ`) and
`CslibFrontier.Algorithms.WordRAM.BellmanFord` (`encodeWeight := Cslib.WordRAM.Signed.encode` on
`ℤ`).

## Main definitions

* `Cslib.Algorithms.WordRAM.CSR.m`: total number of directed edges `∑ u, (adj u).length`.
* `Cslib.Algorithms.WordRAM.CSR.offset`: cumulative edge count below vertex `u`.
* `Cslib.Algorithms.WordRAM.CSR.encode`: CSR word-list encoding of `(n, source, adj)`.
* `Cslib.Algorithms.WordRAM.CSR.dbase`: first memory address past the encoded input in
  `Data.init`.

## Main results

* `Cslib.Algorithms.WordRAM.CSR.encode_length`: the encoded word list has length `n + 2 * m + 3`.
* `Cslib.Algorithms.WordRAM.CSR.offset_succ`, `Cslib.Algorithms.WordRAM.CSR.offset_n`,
  `Cslib.Algorithms.WordRAM.CSR.offset_mono`: cumulative-offset recurrences and monotonicity.
* `Cslib.Algorithms.WordRAM.CSR.init_len`, `Cslib.Algorithms.WordRAM.CSR.init_n`,
  `Cslib.Algorithms.WordRAM.CSR.init_source`, `Cslib.Algorithms.WordRAM.CSR.init_offset`,
  `Cslib.Algorithms.WordRAM.CSR.init_target`, `Cslib.Algorithms.WordRAM.CSR.init_weight`,
  `Cslib.Algorithms.WordRAM.CSR.init_past`: initial memory layout in `Data.init`.
* `Cslib.Algorithms.WordRAM.CSR.inputFits_encode`: `InputFits` certificate from an upper bound on
  `n + 2 * m + 3` and encoded weights.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.CSR

open Cslib.WordRAM

section Layout

variable {W : Type*} (n : ℕ) (source : Fin n) (adj : Fin n → List (Fin n × W))
  (encodeWeight : W → ℕ) {r : ℕ}

/-- Total number of directed edge entries across all adjacency lists. -/
def m : ℕ := ∑ u, (adj u).length

/-- Cumulative number of edges leaving vertices `< u`. -/
def offset (u : ℕ) : ℕ :=
  (((List.finRange n).take u).map fun x => (adj x).length).sum

/-- CSR word-list encoding: `n`, `source`, the `n + 1` offsets `offset 0, …, offset n`, and all
edges in vertex order as two words `(target, encodeWeight weight)`. -/
def encode : List ℕ :=
  n :: (source : ℕ) ::
    ((List.range (n + 1)).map (offset n adj) ++
      (List.finRange n).flatMap fun u =>
        (adj u).flatMap fun e => [(e.1 : ℕ), encodeWeight e.2])

/-- First memory address past the encoded input in `Data.init`. -/
def dbase : ℕ := n + 2 * m n adj + 4

private def edges : List (Fin n × W) := (List.finRange n).flatMap adj

private theorem offset_eq_length (u : ℕ) :
    offset n adj u = (((List.finRange n).take u).flatMap adj).length := by
  simp [offset, List.length_flatMap]

private theorem length_edges : (edges n adj).length = m n adj := by
  simp [edges, m, List.length_flatMap, ← Fin.sum_univ_def]

private theorem edges_eq_append (u : Fin n) :
    edges n adj = ((List.finRange n).take u).flatMap adj ++
      (adj u ++ ((List.finRange n).drop (u + 1)).flatMap adj) := by
  have hu : (u : ℕ) < (List.finRange n).length := by simp
  conv_lhs => rw [edges, ← List.take_append_drop u (List.finRange n),
    List.drop_eq_getElem_cons hu]
  simp [List.flatMap_append]

private theorem offset_add_lt_length_edges (u : Fin n) {i : ℕ} (hi : i < (adj u).length) :
    offset n adj u + i < (edges n adj).length := by
  rw [edges_eq_append n adj u, List.length_append, List.length_append, ← offset_eq_length]
  omega

theorem offset_add_lt_m (u : Fin n) {i : ℕ} (hi : i < (adj u).length) :
    offset n adj u + i < m n adj :=
  length_edges n adj ▸ offset_add_lt_length_edges n adj u hi

private theorem edges_getElem (u : Fin n) {i : ℕ} (hi : i < (adj u).length) :
    (edges n adj)[offset n adj u + i]'(offset_add_lt_length_edges n adj u hi) = (adj u)[i] := by
  simp only [edges_eq_append n adj u, offset_eq_length n adj u,
    List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem_append_left hi]

private theorem getD_flatMap_pairs (l : List (Fin n × W)) (j : ℕ) (hj : j < l.length) :
    (l.flatMap fun e => [(e.1 : ℕ), encodeWeight e.2]).getD (2 * j) 0 = l[j].1 ∧
      (l.flatMap fun e => [(e.1 : ℕ), encodeWeight e.2]).getD (2 * j + 1) 0 =
        encodeWeight l[j].2 := by
  induction l generalizing j with
  | nil => simp at hj
  | cons _ l ih =>
    cases j with
    | zero => simp
    | succ j =>
      have h := ih j (by simpa using hj)
      rw [show 2 * (j + 1) = 2 * j + 2 by ring, show 2 * j + 2 + 1 = 2 * j + 1 + 2 by ring]
      simpa only [List.flatMap_cons, List.cons_append, List.nil_append, List.getD_cons_succ,
        List.getElem_cons_succ] using h

private theorem edgeWords_eq : ((List.finRange n).flatMap fun u =>
    (adj u).flatMap fun e => [(e.1 : ℕ), encodeWeight e.2]) =
    (edges n adj).flatMap fun e => [(e.1 : ℕ), encodeWeight e.2] := by
  rw [edges, List.flatMap_assoc]

private theorem encode_getD_edge (k : ℕ) :
    (encode n source adj encodeWeight).getD (k + n + 3) 0 =
      ((edges n adj).flatMap fun e => [(e.1 : ℕ), encodeWeight e.2]).getD k 0 := by
  rw [encode, show k + n + 3 = (k + n + 1) + 1 + 1 by ring,
    List.getD_cons_succ, List.getD_cons_succ, edgeWords_eq,
    List.getD_append_right _ _ _ _ (by simp)]
  simp

/-- The encoded input has `n + 2 * m + 3` words. -/
theorem encode_length :
    (encode n source adj encodeWeight).length = n + 2 * m n adj + 3 := by
  have h : ∀ l : List (Fin n × W),
      (l.flatMap fun e => [(e.1 : ℕ), encodeWeight e.2]).length = 2 * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons _ l ih =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.length_cons, ih]
      ring
  simp only [encode, edgeWords_eq, List.length_cons, List.length_append, List.length_map,
    List.length_range, h, length_edges, Nat.add_right_cancel_iff]
  ring

/-- The offset of `u + 1` is the offset of `u` plus `(adj u).length`. -/
theorem offset_succ {u : ℕ} (hu : u < n) :
    offset n adj (u + 1) = offset n adj u + (adj ⟨u, hu⟩).length := by
  have hl : u < (List.finRange n).length := by simpa using hu
  simp [offset, List.take_add_one, List.getElem?_eq_getElem hl]

/-- The offset of `n` is the total number of edges `m`. -/
theorem offset_n : offset n adj n = m n adj := by
  rw [offset, List.take_of_length_le (by simp), ← Fin.sum_univ_def]
  rfl

/-- Offsets are monotone. -/
theorem offset_mono {u v : ℕ} (h : u ≤ v) : offset n adj u ≤ offset n adj v :=
  ((List.take_sublist_take_left h).map _).sum_le_sum fun _ _ => Nat.zero_le _

/-- Address `0` initially holds the input length `n + 2 * m + 3`. -/
theorem init_len :
    (Data.init (encode n source adj encodeWeight) : Data r).mem 0 = n + 2 * m n adj + 3 := by
  rw [Data.init_mem_zero, encode_length]

/-- Address `1` initially holds `n`. -/
theorem init_n : (Data.init (encode n source adj encodeWeight) : Data r).mem 1 = n := rfl

/-- Address `2` initially holds `source`. -/
theorem init_source :
    (Data.init (encode n source adj encodeWeight) : Data r).mem 2 = source := rfl

/-- Address `u + 3` initially holds `offset u`, for `u ≤ n`. -/
theorem init_offset {u : ℕ} (hu : u ≤ n) :
    (Data.init (encode n source adj encodeWeight) : Data r).mem (u + 3) = offset n adj u := by
  rw [Data.init_mem_succ, encode, List.getD_cons_succ, List.getD_cons_succ,
    List.getD_append _ _ _ _ (by simp; omega), List.getD_map_range _ _ (Nat.lt_succ_of_le hu)]

/-- The target of edge `i` out of `u` is initially at address `2 * (offset u + i) + n + 4`. -/
theorem init_target (u : Fin n) {i : ℕ} (hi : i < (adj u).length) :
    (Data.init (encode n source adj encodeWeight) : Data r).mem
        (2 * (offset n adj u + i) + n + 4) = ((adj u)[i].1 : ℕ) := by
  rw [show 2 * (offset n adj u + i) + n + 4 = 2 * (offset n adj u + i) + n + 3 + 1 by ring,
    Data.init_mem_succ, encode_getD_edge,
    (getD_flatMap_pairs n encodeWeight _ _ (offset_add_lt_length_edges n adj u hi)).1,
    edges_getElem n adj u hi]

/-- The encoded weight of edge `i` out of `u` is initially at address
`2 * (offset u + i) + n + 5`. -/
theorem init_weight (u : Fin n) {i : ℕ} (hi : i < (adj u).length) :
    (Data.init (encode n source adj encodeWeight) : Data r).mem
        (2 * (offset n adj u + i) + n + 5) = encodeWeight (adj u)[i].2 := by
  rw [show 2 * (offset n adj u + i) + n + 5 = (2 * (offset n adj u + i) + 1) + n + 3 + 1 by ring,
    Data.init_mem_succ, encode_getD_edge,
    (getD_flatMap_pairs n encodeWeight _ _ (offset_add_lt_length_edges n adj u hi)).2,
    edges_getElem n adj u hi]

/-- Memory at or past `dbase` is initially `0`. -/
theorem init_past {a : ℕ} (ha : dbase n adj ≤ a) :
    (Data.init (encode n source adj encodeWeight) : Data r).mem a = 0 := by
  have hz : a ≠ 0 := by unfold dbase at ha; omega
  have hl : (encode n source adj encodeWeight).length ≤ a - 1 := by
    rw [encode_length]; unfold dbase at ha; omega
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
  rw [Data.init_mem_succ, List.getD_eq_default _ _ (by simpa using hl)]

/-- `encode` satisfies `InputFits w` whenever `n + 2 * m + 3 ≤ B`, every encoded weight is at most
`B`, and `Fits w B`. -/
theorem inputFits_encode {B w : ℕ} (hlen : n + 2 * m n adj + 3 ≤ B)
    (hw_le : ∀ (u : Fin n) (e : Fin n × W), e ∈ adj u → encodeWeight e.2 ≤ B)
    (hfit : Fits w B) :
    InputFits w (encode n source adj encodeWeight) := by
  refine ⟨by rw [encode_length]; exact hfit.of_le hlen, fun x hx => ?_⟩
  simp only [encode, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
    List.mem_flatMap, List.mem_finRange, true_and] at hx
  rcases hx with rfl | rfl | ⟨⟨i, hi, rfl⟩ | ⟨u, ⟨v, c⟩, he, hx⟩⟩
  · exact hfit.of_le (by omega)
  · have := source.isLt
    exact hfit.of_le (by omega)
  · have hle : offset n adj i ≤ m n adj := offset_n n adj ▸ offset_mono n adj (by omega)
    exact hfit.of_le (by omega)
  · simp only [List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · have := v.isLt
      exact hfit.of_le (by omega)
    · exact hfit.of_le (hw_le u (v, c) he)

end Layout

end Cslib.Algorithms.WordRAM.CSR
