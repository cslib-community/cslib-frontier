/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Reset
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.Tactic.Realize
import Mathlib.Tactic.IntervalCases

/-!
# Worked tests for `FibonacciHeap.Native.Reset`

Exercises the reusable `Memory.Prog` wrapper layer and sparse `O(touchedLen + 1)` reset:

1. Full lifecycle (`allocProg` -> `insertProg` -> `getKeyProg` -> `decreaseKeyProg` ->
   `extractRawProg` -> `isEmptyProg` -> `resetProg` with non-empty `touched` list ->
   re-inserting fresh keys on the reset heap).
2. Boundary edge cases (`resetProg` with `touchedLen = 0` at `n = 0, w = 3` and at positive
   `n = 3, w = 8`, plus empty `extractRawProg`).
3. Uniform `Realizes .exact` composition across all wrappers and lowering to a deterministic
   width-blind `Program .standard` via `exists_standard_basis_init_program_state_from_words`.
-/

public section

namespace CslibFrontierTests.FibonacciHeapReset

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.PriorityQueue FibonacciHeap FibonacciHeap.Native

/-! ## 1. Full lifecycle with non-empty reset and re-insertion -/

/-- Initial memory state with `touched = [2, 0]` stored at addresses `2, 3`. -/
@[expose] def lifecycleInit : Memory.State :=
  ⟨fun a => if a = 2 then 2 else if a = 3 then 0 else 0, 10⟩

private theorem lifecycleInit_wf : Memory.WellFormed 16 lifecycleInit :=
    { frontier_fits := by decide
      mem_fits := fun a => by
        dsimp only [lifecycleInit]
        split_ifs <;> decide }

/-- Full lifecycle: `allocProg` -> two `insertProg`s -> `getKeyProg` -> `decreaseKeyProg` ->
`extractRawProg` -> `isEmptyProg` -> sparse `resetProg` on `touched = [2, 0]` -> `getKeyProg`
returns `none` -> fresh `insertProg` -> `extractRawProg` returns fresh key. -/
theorem lifecycle_with_reset_and_reinsert :
    ∃ s₁ s₂ s₃ s₄ s₅ s₆ s₇ : Memory.State,
      s₁ = (Memory.spec 0).clientState lifecycleInit (allocProg 4) ∧
      (Memory.spec 0).clientResult lifecycleInit (allocProg 4) = 10 ∧
      s₂ = (Memory.spec 0).clientState s₁ (insertProg 4 10 2 50) ∧
      s₃ = (Memory.spec 0).clientState s₂ (insertProg 4 10 0 30) ∧
      (Memory.spec 0).clientResult s₃ (getKeyProg 4 10 2) = some 50 ∧
      s₄ = (Memory.spec 0).clientState s₃ (decreaseKeyProg 4 10 2 10) ∧
      (Memory.spec 0).clientResult s₄ (extractRawProg 4 10) = some (2, 10) ∧
      s₅ = (Memory.spec 0).clientState s₄ (extractRawProg 4 10) ∧
      (Memory.spec 0).clientResult s₅ (isEmptyProg 4 10) = false ∧
      s₆ = (Memory.spec 0).clientState s₅ (resetProg ⟨4, 10, 2, 2⟩) ∧
      potential 4 ((layout 4 10).abs s₆) = 0 ∧
      memoryCost (resetProg ⟨4, 10, 2, 2⟩) s₅ ≤ 8 ∧
      (Memory.spec 0).clientResult s₆ (getKeyProg 4 10 0) = none ∧
      (Memory.spec 0).clientResult s₆ (isEmptyProg 4 10) = true ∧
      s₇ = (Memory.spec 0).clientState s₆ (insertProg 4 10 1 7) ∧
      (Memory.spec 0).clientResult s₇ (extractRawProg 4 10) = some (1, 7) ∧
      s₆.mem 2 = 2 ∧ s₆.mem 3 = 0 ∧ s₆.frontier = 51 := by
  have hn : Fits 16 4 := by decide
  have hK : Fits 16 100 := by decide
  -- 1. allocProg 4
  obtain ⟨_, hbase, hfr₁, hwf₁, hmod₁, hinv₁, habs₁, _, _⟩ :=
    allocProg_spec lifecycleInit_wf hn hK (s := lifecycleInit) (by decide)
  obtain ⟨s₁, hs₁⟩ : ∃ s₁, s₁ = (Memory.spec 0).clientState lifecycleInit (allocProg 4) :=
    ⟨_, rfl⟩
  rw [← hs₁] at hfr₁ hwf₁ hmod₁ hinv₁ habs₁
  change (Memory.spec 0).clientResult lifecycleInit (allocProg 4) = 10 at hbase
  rw [hbase] at hmod₁ hinv₁ habs₁
  change s₁.frontier = 10 + (9 * 4 + 5) at hfr₁
  -- 2. insertProg 4 10 2 50
  obtain ⟨_, hinv₂, hfr₂, hwf₂, hmod₂, habs₂, _⟩ :=
    insertProg_spec hwf₁ hn hK hinv₁ (v := 2) (k := 50) (by decide) (by decide)
      (by rw [habs₁]; rfl)
  obtain ⟨s₂, hs₂⟩ : ∃ s₂, s₂ = (Memory.spec 0).clientState s₁ (insertProg 4 10 2 50) := ⟨_, rfl⟩
  rw [← hs₂] at hinv₂ hfr₂ hwf₂ hmod₂ habs₂
  -- 3. insertProg 4 10 0 30
  obtain ⟨_, hinv₃, hfr₃, hwf₃, hmod₃, habs₃, _⟩ :=
    insertProg_spec hwf₂ hn hK hinv₂ (v := 0) (k := 30) (by decide) (by decide)
      (by rw [habs₂, Function.update_of_ne (by decide), habs₁]; rfl)
  obtain ⟨s₃, hs₃⟩ : ∃ s₃, s₃ = (Memory.spec 0).clientState s₂ (insertProg 4 10 0 30) := ⟨_, rfl⟩
  rw [← hs₃] at hinv₃ hfr₃ hwf₃ hmod₃ habs₃
  -- 4. getKeyProg 4 10 2
  obtain ⟨_, _, _, hgk₃, _⟩ := getKeyProg_spec hwf₃ hn hK hinv₃ (v := 2) (by decide)
  have hgk₃' : (Memory.spec 0).clientResult s₃ (getKeyProg 4 10 2) = some 50 := by
    rw [hgk₃, habs₃, Function.update_of_ne (by decide), habs₂, Function.update_self]
  -- 5. decreaseKeyProg 4 10 2 10
  obtain ⟨_, hinv₄, hfr₄, hwf₄, hmod₄, habs₄, _⟩ :=
    decreaseKeyProg_spec hwf₃ hn hK hinv₃ (v := 2) (k := 10) (k₀ := 50) (by decide)
      (by rw [habs₃, Function.update_of_ne (by decide), habs₂, Function.update_self])
      (by decide) (by decide)
  obtain ⟨s₄, hs₄⟩ : ∃ s₄, s₄ = (Memory.spec 0).clientState s₃ (decreaseKeyProg 4 10 2 10) :=
    ⟨_, rfl⟩
  rw [← hs₄] at hinv₄ hfr₄ hwf₄ hmod₄ habs₄
  have h_abs₄_2 : (framed hn hK 10).abs s₄ ⟨2, by decide⟩ = some 10 := by
    rw [habs₄, Function.update_self]
  have h_abs₄_0 : (framed hn hK 10).abs s₄ ⟨0, by decide⟩ = some 30 := by
    rw [habs₄, Function.update_of_ne (by decide), habs₃, Function.update_self]
  have h_abs₄_1 : (framed hn hK 10).abs s₄ ⟨1, by decide⟩ = none := by
    rw [habs₄, Function.update_of_ne (by decide), habs₃, Function.update_of_ne (by decide),
      habs₂, Function.update_of_ne (by decide), habs₁]; rfl
  have h_abs₄_3 : (framed hn hK 10).abs s₄ ⟨3, by decide⟩ = none := by
    rw [habs₄, Function.update_of_ne (by decide), habs₃, Function.update_of_ne (by decide),
      habs₂, Function.update_of_ne (by decide), habs₁]; rfl
  -- 6. extractRawProg 4 10
  obtain ⟨_, hinv₅, hfr₅, hwf₅, hmod₅, _, hemp₅_none, hsome₅, _⟩ :=
    extractRawProg_spec hwf₄ hn hK hinv₄
  obtain ⟨s₅, hs₅⟩ : ∃ s₅, s₅ = (Memory.spec 0).clientState s₄ (extractRawProg 4 10) := ⟨_, rfl⟩
  rw [← hs₅] at hinv₅ hfr₅ hwf₅ hmod₅ hemp₅_none hsome₅
  have hext₅ : (Memory.spec 0).clientResult s₄ (extractRawProg 4 10) = some (2, 10) := by
    cases hres : (Memory.spec 0).clientResult s₄ (extractRawProg 4 10) with
    | none =>
      have h0 := congrFun (hemp₅_none hres).1 ⟨2, by decide⟩
      rw [h_abs₄_2] at h0
      cases h0
    | some pk =>
      rcases pk with ⟨y, ky⟩
      obtain ⟨hy, hy_get, hy_le, _⟩ := hsome₅ y ky hres
      have hle2 := hy_le ⟨2, by decide⟩ 10 h_abs₄_2
      interval_cases y
      · rw [h_abs₄_0] at hy_get
        cases hy_get
        omega
      · rw [h_abs₄_1] at hy_get
        cases hy_get
      · rw [h_abs₄_2] at hy_get
        cases hy_get
        rfl
      · rw [h_abs₄_3] at hy_get
        cases hy_get
  obtain ⟨_, _, _, habs₅⟩ := hsome₅ 2 10 hext₅
  -- 7. isEmptyProg 4 10 on s₅
  obtain ⟨_, _, _, hemp₅_res, _⟩ := isEmptyProg_spec hwf₅ hn hK hinv₅
  have hnot_emp₅ : (Memory.spec 0).clientResult s₅ (isEmptyProg 4 10) = false := by
    rw [hemp₅_res, decide_eq_false_iff_not]
    intro hemp
    have h0_dom : (⟨0, by decide⟩ : Fin 4) ∈ IndexedMinPQ.dom ((framed hn hK 10).abs s₅) := by
      rw [IndexedMinPQ.mem_dom_iff]
      refine ⟨30, ?_⟩
      rw [habs₅, Function.update_of_ne (by decide : (⟨0, by decide⟩ : Fin 4) ≠ ⟨2, by decide⟩)]
      exact h_abs₄_0
    rw [hemp] at h0_dom
    exact Finset.notMem_empty _ h0_dom
  -- 8. touched = [2, 0] preserved from lifecycleInit to s₅
  have hpres_buf : ∀ a, a = 2 ∨ a = 3 → s₅.mem a = lifecycleInit.mem a := by
    intro a ha
    have hfp : a ∉ footprint 4 10 := by
      simp only [footprint, Finset.mem_Ico]
      rcases ha with rfl | rfl <;> omega
    rw [hmod₅ a hfp, hmod₄ a hfp, hmod₃ a hfp, hmod₂ a hfp, hmod₁ a hfp]
  have hm2 : s₅.mem 2 = 2 := by rw [hpres_buf 2 (.inl rfl)]; rfl
  have hm3 : s₅.mem 3 = 0 := by rw [hpres_buf 3 (.inr rfl)]; rfl
  have hfr₅_val : s₅.frontier = 51 := by rw [hfr₅, hfr₄, hfr₃, hfr₂, hfr₁]
  -- 9. resetProg ⟨4, 10, 2, 2⟩ on s₅
  obtain ⟨_, _, hfr₆, hwf₆, hmod₆, hinv₆, habs₆, hpot₆, hcost₆⟩ :=
    resetProg_spec ⟨4, 10, 2, 2⟩ hwf₅ hn hK (by decide) hinv₅ (by dsimp only; rw [hfr₅_val]; omega)
      (fun i hi => by
        dsimp only at hi
        dsimp only
        interval_cases i
        · rw [hm2]; decide
        · rw [show 2 + 1 = 3 from rfl, hm3]; decide)
      (fun i hi => by dsimp only at hi ⊢; left; omega)
      (fun (v : Fin 4) hv => by
        rcases v with ⟨v, hv_lt⟩
        interval_cases v
        · exact ⟨1, by decide, hm3⟩
        · rw [habs₅, Function.update_of_ne (by decide : (⟨1, by decide⟩ : Fin 4) ≠ ⟨2, by decide⟩),
            h_abs₄_1] at hv
          cases hv
        · rw [habs₅, Function.update_self] at hv
          cases hv
        · rw [habs₅, Function.update_of_ne (by decide : (⟨3, by decide⟩ : Fin 4) ≠ ⟨2, by decide⟩),
            h_abs₄_3] at hv
          cases hv)
  obtain ⟨s₆, hs₆⟩ :
      ∃ s₆, s₆ = (Memory.spec 0).clientState s₅ (resetProg ⟨4, 10, 2, 2⟩) := ⟨_, rfl⟩
  rw [← hs₆] at hfr₆ hwf₆ hmod₆ hinv₆ habs₆ hpot₆
  dsimp only at hfr₆ hmod₆ hinv₆ habs₆ hpot₆ hcost₆
  -- 10. Verify cleared state + re-insertion + fresh extract on reset heap
  obtain ⟨_, _, _, hgk₆, _⟩ := getKeyProg_spec hwf₆ hn hK hinv₆ (v := 0) (by decide)
  have hgk₆' : (Memory.spec 0).clientResult s₆ (getKeyProg 4 10 0) = none := by
    rw [hgk₆, habs₆]; rfl
  obtain ⟨_, _, _, hemp₆_res, _⟩ := isEmptyProg_spec hwf₆ hn hK hinv₆
  have hemp₆' : (Memory.spec 0).clientResult s₆ (isEmptyProg 4 10) = true := by
    rw [hemp₆_res, habs₆, decide_eq_true_eq]
    ext v
    simp only [Finset.notMem_empty, iff_false, IndexedMinPQ.mem_dom_iff]
    rintro ⟨k, hk⟩
    exact absurd hk (by simp [IndexedMinPQ.empty])
  obtain ⟨_, hinv₇, _, hwf₇, _, habs₇, _⟩ :=
    insertProg_spec hwf₆ hn hK hinv₆ (v := 1) (k := 7) (by decide) (by decide)
      (by rw [habs₆]; rfl)
  obtain ⟨s₇, hs₇⟩ : ∃ s₇, s₇ = (Memory.spec 0).clientState s₆ (insertProg 4 10 1 7) := ⟨_, rfl⟩
  rw [← hs₇] at hinv₇ hwf₇ habs₇
  obtain ⟨_, _, _, _, _, _, hemp₇_none, hsome₇, _⟩ :=
    extractRawProg_spec hwf₇ hn hK hinv₇
  have hext₇ : (Memory.spec 0).clientResult s₇ (extractRawProg 4 10) = some (1, 7) := by
    cases hres : (Memory.spec 0).clientResult s₇ (extractRawProg 4 10) with
    | none =>
      have h0 := congrFun (hemp₇_none hres).1 ⟨1, by decide⟩
      rw [habs₇, Function.update_self] at h0
      cases h0
    | some pk =>
      rcases pk with ⟨y, ky⟩
      obtain ⟨hy, hy_get, _⟩ := hsome₇ y ky hres
      interval_cases y
      · rw [habs₇, Function.update_of_ne (by simp), habs₆] at hy_get
        cases hy_get
      · rw [habs₇, Function.update_self] at hy_get
        cases hy_get
        rfl
      · rw [habs₇, Function.update_of_ne (by simp), habs₆] at hy_get
        cases hy_get
      · rw [habs₇, Function.update_of_ne (by simp), habs₆] at hy_get
        cases hy_get
  have hm2_6 : s₆.mem 2 = 2 := by
    have := hmod₆ 2 (by simp [footprint, Finset.mem_Ico])
    omega
  have hm3_6 : s₆.mem 3 = 0 := by
    have := hmod₆ 3 (by simp [footprint, Finset.mem_Ico])
    omega
  exact ⟨s₁, s₂, s₃, s₄, s₅, s₆, s₇, hs₁, hbase, hs₂, hs₃, hgk₃', hs₄, hext₅, hs₅, hnot_emp₅,
    hs₆, hpot₆, hcost₆, hgk₆', hemp₆', hs₇, hext₇, hm2_6, hm3_6, by rw [hfr₆, hfr₅_val]⟩

/-! ## 2. Boundary edge cases (`n = 0, w = 3, touchedLen = 0` and empty extract) -/

/-- Boundary test: `n = 0`, 3-bit words (`w = 3`), empty `extractRawProg` returning `none`,
and `resetProg` with `touchedLen = 0` costing at most `4`. -/
theorem boundary_zero_capacity_three_bit :
    let s₀ : Memory.State := ⟨fun _ => 0, 2⟩
    let s₁ := (Memory.spec 0).clientState s₀ (allocProg 0)
    let s₂ := (Memory.spec 0).clientState s₁ (extractRawProg 0 2)
    let s₃ := (Memory.spec 0).clientState s₂ (resetProg ⟨0, 2, 0, 0⟩)
    (Memory.spec 0).clientResult s₀ (allocProg 0) = 2 ∧
    (Memory.spec 0).clientResult s₁ (extractRawProg 0 2) = none ∧
    (Memory.spec 0).clientResult s₁ (isEmptyProg 0 2) = true ∧
    ResetSafe 3 ⟨0, 2, 0, 0⟩ s₂ ∧
    (framed (n := 0) (K := 7) (w := 3) (by decide) (by decide) 2).inv s₃ ∧
    (framed (n := 0) (K := 7) (w := 3) (by decide) (by decide) 2).abs s₃ =
      IndexedMinPQ.empty 0 ∧
    potential 0 ((layout 0 2).abs s₃) = 0 ∧
    memoryCost (resetProg ⟨0, 2, 0, 0⟩) s₂ ≤ 4 := by
  let s₀ : Memory.State := ⟨fun _ => 0, 2⟩
  have hwf₀ : Memory.WellFormed 3 s₀ :=
    { frontier_fits := by decide
      mem_fits := fun _ => fits_zero 3 }
  have hn : Fits 3 0 := by decide
  have hK : Fits 3 7 := by decide
  obtain ⟨_, hbase, hfr₁, hwf₁, _, hinv₁, _, _, _⟩ :=
    allocProg_spec hwf₀ hn hK (s := s₀) (by decide)
  set s₁ := (Memory.spec 0).clientState s₀ (allocProg 0)
  change (Memory.spec 0).clientResult s₀ (allocProg 0) = 2 at hbase
  rw [hbase] at hinv₁
  obtain ⟨_, hinv₂, hfr₂, hwf₂, _, hsz₂, _, hsome₂, _⟩ :=
    extractRawProg_spec hwf₁ hn hK hinv₁
  set s₂ := (Memory.spec 0).clientState s₁ (extractRawProg 0 2)
  have hext₂ : (Memory.spec 0).clientResult s₁ (extractRawProg 0 2) = none := by
    cases hres : (Memory.spec 0).clientResult s₁ (extractRawProg 0 2) with
    | none => rfl
    | some pk =>
      obtain ⟨hy, _⟩ := hsome₂ pk.1 pk.2 hres
      omega
  obtain ⟨_, _, _, hemp₁, _⟩ := isEmptyProg_spec hwf₁ hn hK hinv₁
  have hemp₁' : (Memory.spec 0).clientResult s₁ (isEmptyProg 0 2) = true := by
    rw [hemp₁, decide_eq_true_eq]
    ext v
    exact Fin.elim0 v
  have hfr₂_val : s₂.frontier = 7 := by
    rw [hfr₂, hfr₁]
  obtain ⟨hsafe₃, _, _, _, _, hinv₃, habs₃, hpot₃, hcost₃⟩ :=
    resetProg_spec ⟨0, 2, 0, 0⟩ hwf₂ hn hK (by decide) hinv₂ (by dsimp only; rw [hfr₂_val]; omega)
      (fun _ hi => by dsimp only at hi; omega) (fun _ hi => by dsimp only at hi; omega)
      (fun v => Fin.elim0 v)
  exact ⟨hbase, hext₂, hemp₁', hsafe₃, hinv₃, habs₃, hpot₃, hcost₃⟩

/-- Boundary test: positive capacity (`n = 3, w = 8`) with `touchedLen = 0` on an already-empty
heap after empty extraction. -/
theorem boundary_pos_capacity_touched_zero :
    let s₀ : Memory.State := ⟨fun _ => 0, 4⟩
    let s₁ := (Memory.spec 0).clientState s₀ (allocProg 3)
    let s₂ := (Memory.spec 0).clientState s₁ (extractRawProg 3 4)
    let s₃ := (Memory.spec 0).clientState s₂ (resetProg ⟨3, 4, 0, 0⟩)
    (Memory.spec 0).clientResult s₁ (extractRawProg 3 4) = none ∧
    ResetSafe 8 ⟨3, 4, 0, 0⟩ s₂ ∧
    (framed (n := 3) (K := 200) (w := 8) (by decide) (by decide) 4).inv s₃ ∧
    (framed (n := 3) (K := 200) (w := 8) (by decide) (by decide) 4).abs s₃ =
      IndexedMinPQ.empty 3 ∧
    potential 3 ((layout 3 4).abs s₃) = 0 ∧
    memoryCost (resetProg ⟨3, 4, 0, 0⟩) s₂ ≤ 4 := by
  let s₀ : Memory.State := ⟨fun _ => 0, 4⟩
  have hwf₀ : Memory.WellFormed 8 s₀ :=
    { frontier_fits := by decide
      mem_fits := fun _ => fits_zero 8 }
  have hn : Fits 8 3 := by decide
  have hK : Fits 8 200 := by decide
  obtain ⟨_, hbase, hfr₁, hwf₁, _, hinv₁, habs₁, _, _⟩ :=
    allocProg_spec hwf₀ hn hK (s := s₀) (by decide)
  set s₁ := (Memory.spec 0).clientState s₀ (allocProg 3)
  change (Memory.spec 0).clientResult s₀ (allocProg 3) = 4 at hbase
  rw [hbase] at hinv₁ habs₁
  obtain ⟨_, hinv₂, hfr₂, hwf₂, _, _, hemp₂_none, hsome₂, _⟩ :=
    extractRawProg_spec hwf₁ hn hK hinv₁
  set s₂ := (Memory.spec 0).clientState s₁ (extractRawProg 3 4)
  have hext₂ : (Memory.spec 0).clientResult s₁ (extractRawProg 3 4) = none := by
    cases hres : (Memory.spec 0).clientResult s₁ (extractRawProg 3 4) with
    | none => rfl
    | some pk =>
      obtain ⟨hy, hy_get, _⟩ := hsome₂ pk.1 pk.2 hres
      rw [habs₁] at hy_get
      simp [IndexedMinPQ.empty] at hy_get
  have habs₂ : (framed hn hK 4).abs s₂ = IndexedMinPQ.empty 3 :=
    (hemp₂_none hext₂).2
  obtain ⟨hsafe₃, _, _, _, _, hinv₃, habs₃, hpot₃, hcost₃⟩ :=
    resetProg_spec ⟨3, 4, 0, 0⟩ hwf₂ hn hK (by decide) hinv₂
      (by dsimp only; rw [hfr₂, hfr₁]; omega) (fun _ hi => by dsimp only at hi; omega)
      (fun _ hi => by dsimp only at hi; omega)
      (fun v hv => by rw [habs₂] at hv; simp [IndexedMinPQ.empty] at hv)
  exact ⟨hext₂, hsafe₃, hinv₃, habs₃, hpot₃, hcost₃⟩

/-! ## 3. Uniform `Realizes .exact` client lowered to `Program .standard` -/

/-- Sample client exercising `allocProg`, `insertProg`, `decreaseKeyProg`, `extractRawProg`,
`resetProg`, `getKeyProg`, and `isEmptyProg` in sequence. -/
@[expose] def sampleCycleProg (k : ℕ × ℕ) : Memory.Prog ℕ := do
  let base ← allocProg 2
  insertProg 2 base 0 k.1
  insertProg 2 base 1 k.2
  decreaseKeyProg 2 base 1 1
  let ext ← extractRawProg 2 base
  resetProg ⟨2, base, 3, 2⟩
  insertProg 2 base 0 5
  let k0 ← getKeyProg 2 base 0
  let emp ← isEmptyProg 2 base
  if boolWords emp 0 = 1 then pure 0
  else match ext with
    | none => pure 0
    | some p => match k0 with
      | none => pure 0
      | some v => pure (p.1 + p.2 + v)

private def SampleCyclePre (w : ℕ) (k : ℕ × ℕ) (s : Memory.State) : Prop :=
  Fits w (s.frontier + 23) ∧ Fits w k.1 ∧ Fits w k.2 ∧
    2 ≤ k.1 ∧ 1 ≤ k.2 ∧ 5 ≤ s.frontier ∧ s.mem 3 = 1 ∧ s.mem 4 = 0

private theorem decreaseValid_of_framed {w n K base v k k₀ : ℕ} {s : Memory.State}
    (hfit : Fits w (base + (9 * n + 5))) (hn : Fits w n) (hK : Fits w K)
    (hinv : (framed hn hK base).inv s) (hv : v < n)
    (hold : (framed hn hK base).abs s ⟨v, hv⟩ = some k₀) (hle : k ≤ k₀) (hk : k ≤ K) :
    decreaseValid w ![n, base, v, k] s :=
  ⟨hfit, hinv.1, ⟨v, hv⟩, K, k₀, rfl, hK, hinv.2, hold, hle, hk⟩

private theorem extractValid_of_framed {w n K base : ℕ} {s : Memory.State}
    (hfit : Fits w (base + (9 * n + 5))) (hn : Fits w n) (hK : Fits w K)
    (hinv : (framed hn hK base).inv s) :
    extractValid w ![n, base] s :=
  ⟨hfit, hinv.1, K, hK, hinv.2⟩

private theorem sampleCycleProg_spec {w : ℕ} {k : ℕ × ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : SampleCyclePre w k s) :
    let base := (Memory.spec 0).clientResult s (allocProg 2)
    let s₁ := (Memory.spec 0).clientState s (allocProg 2)
    let s₂ := (Memory.spec 0).clientState s₁ (insertProg 2 base 0 k.1)
    let s₃ := (Memory.spec 0).clientState s₂ (insertProg 2 base 1 k.2)
    let s₄ := (Memory.spec 0).clientState s₃ (decreaseKeyProg 2 base 1 1)
    let ext := (Memory.spec 0).clientResult s₄ (extractRawProg 2 base)
    let s₅ := (Memory.spec 0).clientState s₄ (extractRawProg 2 base)
    let s₆ := (Memory.spec 0).clientState s₅ (resetProg ⟨2, base, 3, 2⟩)
    let s₇ := (Memory.spec 0).clientState s₆ (insertProg 2 base 0 5)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (sampleCycleProg k)) ∧
    (Memory.spec 0).clientResult s (sampleCycleProg k) = 7 ∧
    ((Memory.spec 0).clientState s (sampleCycleProg k)).frontier = s.frontier + 23 ∧
    Fits w (s.frontier + (9 * 2 + 5)) ∧
    Fits w (base + (9 * 2 + 5)) ∧
    decreaseValid w ![2, base, 1, 1] s₃ ∧
    extractValid w ![2, base] s₄ ∧
    ResetSafe w ⟨2, base, 3, 2⟩ s₅ ∧
    ext = some (1, 1) ∧
    (Memory.spec 0).clientResult s₇ (getKeyProg 2 base 0) = some 5 := by
  rcases hpre with ⟨hfit, hk1, hk2, hk1_ge, hk2_ge, hfr_ge, hm3, hm4⟩
  have h16_fit : Fits w 23 := hfit.of_le (by omega)
  have hn : Fits w 2 := h16_fit.of_le (by omega)
  let K := max k.1 (max k.2 5)
  have hK : Fits w K := by
    dsimp only [K]
    rcases max_cases k.1 (max k.2 5) with ⟨h, _⟩ | ⟨h, _⟩
    · rwa [h]
    · rw [h]
      rcases max_cases k.2 5 with ⟨h', _⟩ | ⟨h', _⟩
      · rwa [h']
      · rw [h']; exact h16_fit.of_le (by omega)
  have hk1_le : k.1 ≤ K := le_max_left _ _
  have hk2_le : k.2 ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have h5_le : 5 ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
  -- Step 1: allocProg 2
  obtain ⟨hv₁, hbase, hfr₁, hwf₁, hmod₁, hinv₁, habs₁, _, _⟩ :=
    allocProg_spec hwf hn hK (s := s) (hfit.of_le (by omega))
  obtain ⟨base, hbase_def⟩ : ∃ base, base = (Memory.spec 0).clientResult s (allocProg 2) :=
    ⟨_, rfl⟩
  obtain ⟨s₁, hs₁⟩ : ∃ s₁, s₁ = (Memory.spec 0).clientState s (allocProg 2) := ⟨_, rfl⟩
  rw [← hbase_def] at hbase hmod₁ hinv₁ habs₁
  rw [← hs₁] at hfr₁ hwf₁ hmod₁ hinv₁ habs₁
  have hfit_base : Fits w (base + (9 * 2 + 5)) := by rw [hbase]; exact hfit.of_le (by omega)
  have hbase_fr : base = s.frontier := hbase
  rw [hbase_fr] at hinv₁ habs₁
  -- Step 2: insertProg 2 base 0 k.1
  have hinv₁' : (framed hn hK base).inv s₁ := by simpa only [hbase_fr] using hinv₁
  have habs₁' : (framed hn hK base).abs s₁ = IndexedMinPQ.empty 2 := by
    simpa only [hbase_fr] using habs₁
  obtain ⟨hv₂, hinv₂, hfr₂, hwf₂, hmod₂, habs₂, _⟩ :=
    insertProg_spec hwf₁ hn hK hinv₁' (v := 0) (k := k.1) (by decide) hk1_le
      (by rw [habs₁']; rfl)
  obtain ⟨s₂, hs₂⟩ : ∃ s₂, s₂ = (Memory.spec 0).clientState s₁ (insertProg 2 base 0 k.1) :=
    ⟨_, rfl⟩
  rw [← hs₂] at hinv₂ hfr₂ hwf₂ hmod₂ habs₂
  -- Step 3: insertProg 2 base 1 k.2
  obtain ⟨hv₃, hinv₃, hfr₃, hwf₃, hmod₃, habs₃, _⟩ :=
    insertProg_spec hwf₂ hn hK hinv₂ (v := 1) (k := k.2) (by decide) hk2_le
      (by rw [habs₂, Function.update_of_ne (by decide), habs₁']; rfl)
  obtain ⟨s₃, hs₃⟩ : ∃ s₃, s₃ = (Memory.spec 0).clientState s₂ (insertProg 2 base 1 k.2) :=
    ⟨_, rfl⟩
  rw [← hs₃] at hinv₃ hfr₃ hwf₃ hmod₃ habs₃
  have hdec_valid : decreaseValid w ![2, base, 1, 1] s₃ :=
    decreaseValid_of_framed hfit_base hn hK hinv₃ (by decide)
      (by rw [habs₃, Function.update_self]) hk2_ge (le_trans (by decide) h5_le)
  -- Step 4: decreaseKeyProg 2 base 1 1
  obtain ⟨hv₄, hinv₄, hfr₄, hwf₄, hmod₄, habs₄, _⟩ :=
    decreaseKeyProg_spec hwf₃ hn hK hinv₃ (v := 1) (k := 1) (k₀ := k.2) (by decide)
      (by rw [habs₃, Function.update_self]) hk2_ge (le_trans (by decide) h5_le)
  obtain ⟨s₄, hs₄⟩ : ∃ s₄, s₄ = (Memory.spec 0).clientState s₃ (decreaseKeyProg 2 base 1 1) :=
    ⟨_, rfl⟩
  rw [← hs₄] at hinv₄ hfr₄ hwf₄ hmod₄ habs₄
  have hext_valid : extractValid w ![2, base] s₄ :=
    extractValid_of_framed hfit_base hn hK hinv₄
  have h_abs₄_1 : (framed hn hK base).abs s₄ ⟨1, by decide⟩ = some 1 := by
    rw [habs₄, Function.update_self]
  have h_abs₄_0 : (framed hn hK base).abs s₄ ⟨0, by decide⟩ = some k.1 := by
    rw [habs₄, Function.update_of_ne (by decide), habs₃, Function.update_of_ne (by decide),
      habs₂, Function.update_self]
  -- Step 5: extractRawProg 2 base
  obtain ⟨hv₅, hinv₅, hfr₅, hwf₅, hmod₅, _, hemp₅_none, hsome₅, _⟩ :=
    extractRawProg_spec hwf₄ hn hK hinv₄
  obtain ⟨ext, hext_def⟩ : ∃ ext, ext = (Memory.spec 0).clientResult s₄ (extractRawProg 2 base) :=
    ⟨_, rfl⟩
  obtain ⟨s₅, hs₅⟩ : ∃ s₅, s₅ = (Memory.spec 0).clientState s₄ (extractRawProg 2 base) :=
    ⟨_, rfl⟩
  rw [← hext_def] at hemp₅_none hsome₅
  rw [← hs₅] at hinv₅ hfr₅ hwf₅ hmod₅ hemp₅_none hsome₅
  have hext_eq : ext = some (1, 1) := by
    cases hres : ext with
    | none =>
      have h0 := congrFun (hemp₅_none hres).1 ⟨1, by decide⟩
      rw [h_abs₄_1] at h0
      cases h0
    | some pk =>
      rcases pk with ⟨y, ky⟩
      obtain ⟨hy, hy_get, hy_le, _⟩ := hsome₅ y ky hres
      have hle1 := hy_le ⟨1, by decide⟩ 1 h_abs₄_1
      interval_cases y
      · rw [h_abs₄_0] at hy_get
        cases hy_get
        omega
      · rw [h_abs₄_1] at hy_get
        cases hy_get
        rfl
  obtain ⟨_, _, _, habs₅⟩ := hsome₅ 1 1 hext_eq
  -- Step 6: resetProg ⟨2, base, 3, 2⟩
  have hpres_buf : ∀ a, a = 3 ∨ a = 4 → s₅.mem a = s.mem a := by
    intro a ha
    have hfp : a ∉ footprint 2 base := by
      simp only [footprint, Finset.mem_Ico]
      rcases ha with rfl | rfl <;> omega
    rw [hmod₅ a hfp, hmod₄ a hfp, hmod₃ a hfp, hmod₂ a hfp]
    exact hmod₁ a hfp
  have hm3' : s₅.mem 3 = 1 := (hpres_buf 3 (.inl rfl)).trans hm3
  have hm4' : s₅.mem 4 = 0 := (hpres_buf 4 (.inr rfl)).trans hm4
  have hfr₅_val : s₅.frontier = s.frontier + 23 := by
    rw [hfr₅, hfr₄, hfr₃, hfr₂, hfr₁]
  obtain ⟨hsafe_rst, hv₆, hfr₆, hwf₆, _, hinv₆, habs₆, _, _⟩ :=
    resetProg_spec ⟨2, base, 3, 2⟩ hwf₅ hn hK (h16_fit.of_le (by dsimp only; omega)) hinv₅
      (by dsimp only; rw [hfr₅_val]; omega)
      (fun i hi => by
        dsimp only at hi
        dsimp only
        interval_cases i
        · rw [hm3']; decide
        · rw [show 3 + 1 = 4 from rfl, hm4']; decide)
      (fun i hi => by dsimp only at hi ⊢; left; omega)
      (fun (v : Fin 2) hv => by
        rcases v with ⟨v, hv_lt⟩
        interval_cases v
        · exact ⟨1, by dsimp only; omega, by dsimp only; exact hm4'⟩
        · rw [habs₅, Function.update_self] at hv
          cases hv)
  obtain ⟨s₆, hs₆⟩ : ∃ s₆, s₆ = (Memory.spec 0).clientState s₅ (resetProg ⟨2, base, 3, 2⟩) :=
    ⟨_, rfl⟩
  rw [← hs₆] at hfr₆ hwf₆ hinv₆ habs₆
  dsimp only at hsafe_rst hfr₆ hinv₆ habs₆
  -- Step 7: insertProg 2 base 0 5
  obtain ⟨hv₇, hinv₇, hfr₇, hwf₇, _, habs₇, _⟩ :=
    insertProg_spec hwf₆ hn hK hinv₆ (v := 0) (k := 5) (by decide) h5_le
      (by rw [habs₆]; rfl)
  obtain ⟨s₇, hs₇⟩ : ∃ s₇, s₇ = (Memory.spec 0).clientState s₆ (insertProg 2 base 0 5) :=
    ⟨_, rfl⟩
  rw [← hs₇] at hfr₇ hinv₇ hwf₇ habs₇
  -- Step 8: getKeyProg 2 base 0 & isEmptyProg 2 base
  obtain ⟨hv₈, hinv₈, hst₈, hgk₈, _⟩ := getKeyProg_spec hwf₇ hn hK hinv₇ (v := 0) (by decide)
  have hk0_eq : (Memory.spec 0).clientResult s₇ (getKeyProg 2 base 0) = some 5 := by
    rw [hgk₈, habs₇, Function.update_self]
  obtain ⟨hv₉, _, hst₉, hemp₉, _⟩ := isEmptyProg_spec hwf₇ hn hK hinv₇
  have hemp_eq : (Memory.spec 0).clientResult s₇ (isEmptyProg 2 base) = false := by
    rw [hemp₉, decide_eq_false_iff_not]
    intro hemp
    have hmem0 : (⟨0, by decide⟩ : Fin 2) ∈ IndexedMinPQ.dom ((framed hn hK base).abs s₇) := by
      rw [IndexedMinPQ.mem_dom_iff]
      exact ⟨5, by rw [habs₇, Function.update_self]⟩
    rw [hemp] at hmem0
    exact Finset.notMem_empty _ hmem0
  -- Combine ValidHistory & result
  have hv_all : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (sampleCycleProg k)) := by
    dsimp only [sampleCycleProg]
    refine validHistory_bind_step hv₁ ?_
    rw [← hbase_def, ← hs₁]
    refine validHistory_bind_step hv₂ ?_
    rw [← hs₂]
    refine validHistory_bind_step hv₃ ?_
    rw [← hs₃]
    refine validHistory_bind_step hv₄ ?_
    rw [← hs₄]
    refine validHistory_bind_step hv₅ ?_
    rw [← hext_def, ← hs₅]
    refine validHistory_bind_step hv₆ ?_
    rw [← hs₆]
    refine validHistory_bind_step hv₇ ?_
    rw [← hs₇]
    refine validHistory_bind_step hv₈ ?_
    rw [hst₈]
    refine validHistory_bind_step hv₉ ?_
    rw [hst₉]
    simp only [hemp_eq, boolWords_false, Matrix.cons_val_zero, zero_ne_one, ↓reduceIte,
      hext_eq, hk0_eq]
    exact validHistory_pure w s₇ 7
  have hres_all : (Memory.spec 0).clientResult s (sampleCycleProg k) = 7 := by
    dsimp only [sampleCycleProg]
    rw [StateTransitionSpec.clientResult_bind, ← hbase_def, ← hs₁]
    rw [StateTransitionSpec.clientResult_bind, ← hs₂]
    rw [StateTransitionSpec.clientResult_bind, ← hs₃]
    rw [StateTransitionSpec.clientResult_bind, ← hs₄]
    rw [StateTransitionSpec.clientResult_bind, ← hext_def, ← hs₅]
    rw [StateTransitionSpec.clientResult_bind, ← hs₆]
    rw [StateTransitionSpec.clientResult_bind, ← hs₇]
    rw [StateTransitionSpec.clientResult_bind, hst₈, StateTransitionSpec.clientResult_bind, hst₉,
      hemp_eq]
    simp only [boolWords_false, Matrix.cons_val_zero, zero_ne_one, ↓reduceIte, hext_eq, hk0_eq]
    rfl
  have hst_all :
      ((Memory.spec 0).clientState s (sampleCycleProg k)).frontier = s.frontier + 23 := by
    dsimp only [sampleCycleProg]
    rw [StateTransitionSpec.clientState_bind, ← hbase_def, ← hs₁]
    rw [StateTransitionSpec.clientState_bind, ← hs₂]
    rw [StateTransitionSpec.clientState_bind, ← hs₃]
    rw [StateTransitionSpec.clientState_bind, ← hs₄]
    rw [StateTransitionSpec.clientState_bind, ← hext_def, ← hs₅]
    rw [StateTransitionSpec.clientState_bind, ← hs₆]
    rw [StateTransitionSpec.clientState_bind, ← hs₇]
    rw [StateTransitionSpec.clientState_bind, hst₈, StateTransitionSpec.clientState_bind, hst₉,
      hemp_eq]
    simp only [boolWords_false, Matrix.cons_val_zero, zero_ne_one, ↓reduceIte, hext_eq, hk0_eq]
    change s₇.frontier = s.frontier + 23
    rw [hfr₇, hfr₆, hfr₅_val]
  dsimp only
  rw [← hbase_def, ← hs₁, ← hs₂, ← hs₃, ← hs₄, ← hext_def, ← hs₅, ← hs₆, ← hs₇]
  exact ⟨hv_all, hres_all, hst_all, hfit.of_le (by omega), hfit_base, hdec_valid, hext_valid,
    hsafe_rst, hext_eq, hk0_eq⟩

private theorem realizes_sampleCycleProg : Realizes .exact
    sampleCycleProg (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
    SampleCyclePre (fun _ _ => 0) := by
  have hreal : Realizes .exact
      sampleCycleProg (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w k s => SampleCyclePre w k s ∧
        (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (sampleCycleProg k)))
      (fun _ _ => 0) := by
    unfold sampleCycleProg
    realize [realizes_allocProg, realizes_insertProg, realizes_decreaseKeyProg,
      realizes_extractRawProg, realizes_resetProg, realizes_getKeyProg, realizes_isEmptyProg]
    all_goals
      rcases h with ⟨hpre, _⟩
      have hfit1 : Fits w (s.frontier + (9 * 2 + 5)) := hpre.1.of_le (by omega)
      have hk1 : Fits w d.1 := hpre.2.1
      have hk2 : Fits w d.2 := hpre.2.2.1
      have hfit5 : Fits w 5 := hfit1.of_le (by omega)
      have hbase_eq : (Memory.spec 0).clientResult s (allocProg 2) = s.frontier := rfl
      try first
        | fits
        | omega
        | (rw [hbase_eq]; fits)
    · obtain ⟨_, _, _, _, _, hdec, _⟩ := sampleCycleProg_spec hmem hpre
      exact hdec
    · obtain ⟨_, _, _, _, _, _, hext, _⟩ := sampleCycleProg_spec hmem hpre
      exact hext
    · obtain ⟨_, _, _, _, _, _, _, hrst, _⟩ := sampleCycleProg_spec hmem hpre
      exact hrst
    · obtain ⟨_, _, _, _, _, _, _, _, hext_res, hk0_res⟩ := sampleCycleProg_spec hmem hpre
      rw [hext_res, hk0_res]
      have hsum : optionWordsWith WordEncoding.encode (some (1, 1)) 1 +
          optionWordsWith WordEncoding.encode (some (1, 1)) 2 + optionWords (some 5) 1 = 7 := by
        decide
      exact hfit1.of_le (by rw [hsum]; omega)
  exact hreal.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

/-- Sample end-to-end compilation to a deterministic width-blind `Program .standard r`
exercising `allocProg`, `insertProg`, `decreaseKeyProg`, `extractRawProg`, `resetProg`,
`getKeyProg`, and `isEmptyProg` together. -/
theorem exists_standard_sample_cycle_halts_7 :
    ∃ r C pc : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
      ∃ frontier : Fin r, ∃ y n,
        Runs 16 prog (State.init [10, 20, 1, 0]) ⟨pc, y⟩ n ∧
        step 16 prog ⟨pc, y⟩ = .halt 7 ∧
        (memoryState frontier y).frontier = 28 ∧
        n + 1 ≤ C * (memoryCost (sampleCycleProg (10, 20)) (Memory.State.init [10, 20, 1, 0]) + 1)
          + 1 := by
  obtain ⟨r, C, pc, prog, hnw, frontier, _, hrun⟩ :=
    realizes_sampleCycleProg.exists_standard_basis_init_program_state_from_words (0 : Fin 1)
  have hprog_rf : (stripRand prog).IsRandFree := isRandFree_stripRand prog
  have hprog_nw : ¬(stripRand prog).ReadsWidth := not_readsWidth_stripRand hnw
  have hlayout :
      ∀ j : Fin 2, [10, 20, 1, 0].getD j.val 0 = WordEncoding.encode (α := ℕ × ℕ) (10, 20) j := by
    intro j; fin_cases j <;> rfl
  have hwf : Memory.WellFormed 16 (Memory.State.init [10, 20, 1, 0]) :=
    Memory.wellFormed_init (by decide) (by decide)
  have hpre : SampleCyclePre 16 (10, 20) (Memory.State.init [10, 20, 1, 0]) :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, rfl, rfl⟩
  obtain ⟨hv, hres, hst, _⟩ := sampleCycleProg_spec hwf hpre
  obtain ⟨y, n, hruns, hhalt, hmem_eq, _, hsteps⟩ :=
    hrun 16 (10, 20) [10, 20, 1, 0] hlayout (by decide) (by decide) (by decide) hpre hv
  have hres' : ((Memory.spec 16).clientResult (Memory.State.init [10, 20, 1, 0])
      (sampleCycleProg (10, 20))) = 7 := by
    rw [clientResult_width 16]
    exact hres
  have hst' : ((Memory.spec 16).clientState (Memory.State.init [10, 20, 1, 0])
      (sampleCycleProg (10, 20))).frontier = 28 := by
    rw [clientState_width 16]
    exact hst
  have hhalt' : step 16 prog ⟨pc, y⟩ = .halt 7 := by
    rw [hres'] at hhalt
    exact hhalt
  rw [Nat.add_zero] at hsteps
  refine ⟨r, C, pc, stripRand prog, hprog_nw, hprog_rf, frontier, y, n,
    runs_stripRand hruns, step_stripRand_of_halt hhalt', ?_, hsteps⟩
  rw [hmem_eq]
  exact hst'

end CslibFrontierTests.FibonacciHeapReset
