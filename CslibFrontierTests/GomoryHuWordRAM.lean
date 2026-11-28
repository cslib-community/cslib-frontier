/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.WordRAM.GomoryHu
import CslibFrontier.Algorithms.Lean.GomoryHu.WeightedCut

/-!
# Tests for Gusfield's Gomory–Hu tree algorithm on the Word-RAM

Instantiate `Cslib.Algorithms.WordRAM.GomoryHu.exists_gomoryHu_program`:

* on the weighted graph on `Fin 4` with edges `01:4`, `12:2`, `23:3`, `02:1`, `13:1` (the graph of
  `CslibFrontierTests.GomoryHuConstruction`), rooted at `0`, at width `8`, which fits
  `ghWorkspace 4 = 51` and `ekBound 4 4 = 141`. The root keeps itself as parent and weight `0`.
  Every vertex `u ≠ 0` gets a parent other than itself, since the output is a tree; as
  `λ(2, x) = λ(3, x) = 4` for every `x` other than `2` (respectively `3`), the recorded weights of
  `2` and `3` are `4` whichever parents the machine's minimum cuts produce, and that of `1` is
  `λ(1, 0) = 5` or `4`;
* on a zero-weight `Fin 3` multigraph (`B = 0`, `n = 3`) at width `6` (`ghWorkspace 3 = 33`,
  `ekBound 3 0 = 28`), where every tree edge has weight `0`;
* on one vertex, at width `4`.
-/

public section

namespace CslibFrontierTests.GomoryHuWordRAM

open Cslib.WeightedCut Cslib.Algorithms.Lean.GomoryHu Cslib.Algorithms.WordRAM.GomoryHu
open Cslib.Algorithms.WordRAM.EdmondsKarp Cslib.WordRAM
open SimpleGraph (parentGraph parentGraph_adj)

/-- The weighted graph on `Fin 4` with edges `01:4`, `12:2`, `23:3`, `02:1`, `13:1`. -/
def W : Fin 4 → Fin 4 → ℕ := fun u v =>
  match u.val, v.val with
  | 0, 1 => 4 | 1, 0 => 4
  | 1, 2 => 2 | 2, 1 => 2
  | 2, 3 => 3 | 3, 2 => 3
  | 0, 2 => 1 | 2, 0 => 1
  | 1, 3 => 1 | 3, 1 => 1
  | _, _ => 0

private theorem hW : IsMultigraph W := by
  unfold IsMultigraph
  decide

private theorem hWB : ∀ u v, W u v ≤ 4 := by decide

example : ghWorkspace 4 = 51 := rfl
example : ekBound 4 4 = 141 := rfl

/-- The minimum cut values at `2` and `3`, each witnessed by a minimum cut. -/
private theorem minCut_eq {s t : Fin 4} {X : Finset (Fin 4)}
    (hX : IsMinCutBetween (cutWeight W) s t X) : minCutBetween W s t = cutWeight W X :=
  ((isMinCutBetween_cutWeight_iff W).mp hX).2.2.symm

private theorem minCut_two (x : Fin 4) (hx : x ≠ 2) : minCutBetween W 2 x = 4 := by
  fin_cases x
  · rw [minCut_eq (X := {2, 3}) (by unfold IsMinCutBetween; decide)]
    decide
  · rw [minCut_eq (X := {2, 3}) (by unfold IsMinCutBetween; decide)]
    decide
  · exact absurd rfl hx
  · rw [minCut_eq (X := {0, 1, 2}) (by unfold IsMinCutBetween; decide)]
    decide

private theorem minCut_three (x : Fin 4) (hx : x ≠ 3) : minCutBetween W 3 x = 4 := by
  fin_cases x
  · rw [minCut_eq (X := {3}) (by unfold IsMinCutBetween; decide)]
    decide
  · rw [minCut_eq (X := {3}) (by unfold IsMinCutBetween; decide)]
    decide
  · rw [minCut_eq (X := {3}) (by unfold IsMinCutBetween; decide)]
    decide
  · exact absurd rfl hx

private theorem minCut_one (x : Fin 4) (hx : x ≠ 1) :
    minCutBetween W 1 x = 5 ∨ minCutBetween W 1 x = 4 := by
  fin_cases x
  · left
    rw [minCut_eq (X := {1, 2, 3}) (by unfold IsMinCutBetween; decide)]
    decide
  · exact absurd rfl hx
  · right
    rw [minCut_eq (X := {0, 1}) (by unfold IsMinCutBetween; decide)]
    decide
  · right
    rw [minCut_eq (X := {0, 1, 2}) (by unfold IsMinCutBetween; decide)]
    decide

/-- In a spanning tree that is the parent graph of `p` with root `r`, no vertex other than `r` is
its own parent: the parent edges `s(z, p z)` with `p z ≠ z` must supply `n - 1` tree edges. -/
private theorem ne_self_of_isTree {n : ℕ} {p : Fin n → Fin n} {r : Fin n}
    (hT : (parentGraph p).IsTree) (hr : p r = r) {u : Fin n} (hu : u ≠ r) : p u ≠ u := by
  classical
  intro hpu
  let S := Finset.univ.filter fun z : Fin n => p z ≠ z
  have hsub : (parentGraph p).edgeFinset ⊆ S.image fun z => s(z, p z) := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, parentGraph_adj] at he
      obtain ⟨hxy, h | h⟩ := he
      · exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, h ▸ hxy.symm⟩,
          by rw [h]⟩
      · exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, h ▸ hxy⟩,
          by rw [h, Sym2.eq_swap]⟩
  have hS : S ⊆ Finset.univ \ {r, u} := fun z hz => by
    rw [Finset.mem_filter] at hz
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨Finset.mem_univ z, fun h => h.elim (fun h => hz.2 (h ▸ hr)) (fun h => hz.2 (h ▸ hpu))⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_image_le (s := S) (f := fun z => s(z, p z))
  have h3 := Finset.card_le_card hS
  have h4 : (Finset.univ \ {r, u} : Finset (Fin n)).card = n - 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_pair hu.symm]
  have h5 := hT.card_edgeFinset
  rw [Fintype.card_fin] at h5
  have h6 : 2 ≤ n := by
    have := Finset.card_pair hu.symm
    have := Finset.card_le_univ ({u, r} : Finset (Fin n))
    rw [Fintype.card_fin] at this
    omega
  omega

/-- The Word-RAM run on the 4-vertex graph rooted at `0`, at width `8`. -/
example : ∃ (R C pc : ℕ), 0 < C ∧ ∃ prog : Program .exact R,
    ∃ (y : Data R) (steps res : ℕ) (p : Fin 4 → Fin 4),
      Runs 8 prog (State.init (encodeInput W 0)) ⟨pc, y⟩ steps ∧
      step 8 prog ⟨pc, y⟩ = .halt res ∧ steps + 1 ≤ C * 5 ^ 6 ∧
      IsGomoryHuTree (cutWeight W) (parentGraph p) ∧
      y.mem (parAddr 4 0) = 0 ∧ y.mem (wtAddr 4 0) = 0 ∧
      (y.mem (wtAddr 4 1) = 5 ∨ y.mem (wtAddr 4 1) = 4) ∧
      y.mem (wtAddr 4 2) = 4 ∧ y.mem (wtAddr 4 3) = 4 := by
  obtain ⟨R, C, pc, hC, prog, hprog⟩ := exists_gomoryHu_program
  obtain ⟨y, steps, res, p, hruns, hhalt, htime, hpar, hroot, htree, hwt⟩ :=
    hprog W 0 4 8 hW hWB (by decide) (by decide)
  have hne : ∀ u : Fin 4, u ≠ 0 → p u ≠ u := fun u hu => ne_self_of_isTree htree.isTree hroot hu
  have h0 : y.mem (parAddr 4 0) = (p 0).val := hpar 0
  have hw0 : y.mem (wtAddr 4 0) = minCutBetween W 0 (p 0) := hwt 0
  have hw1 : y.mem (wtAddr 4 1) = minCutBetween W 1 (p 1) := hwt 1
  have hw2 : y.mem (wtAddr 4 2) = minCutBetween W 2 (p 2) := hwt 2
  have hw3 : y.mem (wtAddr 4 3) = minCutBetween W 3 (p 3) := hwt 3
  refine ⟨R, C, pc, hC, prog, y, steps, res, p, hruns, hhalt, htime, htree, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0, hroot]
    rfl
  · rw [hw0, hroot, minCutBetween_self]
  · rw [hw1]
    exact minCut_one _ (hne 1 (by decide))
  · rw [hw2]
    exact minCut_two _ (hne 2 (by decide))
  · rw [hw3]
    exact minCut_three _ (hne 3 (by decide))

/-- One vertex, at width `4`: the root is its own parent with weight `0`. -/
example : ∃ (R C pc : ℕ), 0 < C ∧ ∃ prog : Program .exact R,
    ∃ (y : Data R) (steps res : ℕ),
      Runs 4 prog (State.init (encodeInput (fun _ _ : Fin 1 => 0) 0)) ⟨pc, y⟩ steps ∧
      step 4 prog ⟨pc, y⟩ = .halt res ∧ steps + 1 ≤ C * 2 ^ 6 ∧
      y.mem (parAddr 1 0) = 0 ∧ y.mem (wtAddr 1 0) = 0 := by
  obtain ⟨R, C, pc, hC, prog, hprog⟩ := exists_gomoryHu_program
  obtain ⟨y, steps, res, p, hruns, hhalt, htime, hpar, hroot, -, hwt⟩ :=
    hprog (fun _ _ : Fin 1 => 0) 0 0 4 ⟨fun _ _ => rfl, fun _ => rfl⟩ (fun _ _ => le_rfl)
      (by decide) (by decide)
  have h0 : y.mem (parAddr 1 0) = (p 0).val := hpar 0
  have hw0 : y.mem (wtAddr 1 0) = minCutBetween (fun _ _ : Fin 1 => 0) 0 (p 0) := hwt 0
  refine ⟨R, C, pc, hC, prog, y, steps, res, hruns, hhalt, htime, ?_, ?_⟩
  · rw [h0, hroot]
    rfl
  · rw [hw0, hroot, minCutBetween_self]


/-- Zero-weight 3-vertex multigraph (`B = 0`, `n = 3`), at width `6`. -/
example : ghWorkspace 3 = 33 := rfl
example : ekBound 3 0 = 28 := rfl

example : ∃ (R C pc : ℕ), 0 < C ∧ ∃ prog : Program .exact R,
    ∃ (y : Data R) (steps res : ℕ) (p : Fin 3 → Fin 3),
      Runs 6 prog (State.init (encodeInput (fun _ _ : Fin 3 => 0) 0)) ⟨pc, y⟩ steps ∧
      step 6 prog ⟨pc, y⟩ = .halt res ∧ steps + 1 ≤ C * 4 ^ 6 ∧
      IsGomoryHuTree (cutWeight fun _ _ : Fin 3 => 0) (parentGraph p) ∧
      y.mem (parAddr 3 0) = 0 ∧
      ∀ u : Fin 3, y.mem (wtAddr 3 u.val) = 0 := by
  obtain ⟨R, C, pc, hC, prog, hprog⟩ := exists_gomoryHu_program
  obtain ⟨y, steps, res, p, hruns, hhalt, htime, hpar, hroot, htree, hwt⟩ :=
    hprog (fun _ _ : Fin 3 => 0) 0 0 6 ⟨fun _ _ => rfl, fun _ => rfl⟩ (fun _ _ => le_rfl)
      (by decide) (by decide)
  have h0 : y.mem (parAddr 3 0) = (p 0).val := hpar 0
  refine ⟨R, C, pc, hC, prog, y, steps, res, p, hruns, hhalt, htime, htree,
    by rw [h0, hroot]; rfl, fun u => ?_⟩
  rw [hwt u]
  by_cases hup : u = p u
  · rw [← hup, minCutBetween_self]
  · have hmin : IsMinCutBetween (cutWeight fun _ _ : Fin 3 => 0) u (p u) {u} :=
      ⟨by simp, by simpa using Ne.symm hup, fun _ _ _ => by simp [cutWeight]⟩
    rw [← ((isMinCutBetween_cutWeight_iff _).mp hmin).2.2]
    simp [cutWeight]

end CslibFrontierTests.GomoryHuWordRAM
