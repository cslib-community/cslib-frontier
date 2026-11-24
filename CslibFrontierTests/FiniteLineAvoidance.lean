/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

import CslibFrontier.Foundations.Geometry.FiniteLineAvoidance
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open Classical in
-- Both moving points start at the same fixed point on the fixed horizontal line.
example {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ x y : ℂ, dist x 0 < ρ ∧ dist y 0 < ρ ∧ x ≠ y ∧
      x ∉ affineSpan ℝ ({0, 1} : Set ℂ) ∧ y ∉ affineSpan ℝ ({x, 0} : Set ℂ) := by
  let fixed : Finset ℂ := {0, 1, 2}
  obtain ⟨q, hnear, hinj, hfixed, hspans, _⟩ :=
    Cslib.exists_injective_perturbation_avoiding_spans_and_crossings
      (fun _ : Bool => 0) fixed hρ
  have h0 : (0 : ℂ) ∈ fixed := by simp [fixed]
  have h1 : (1 : ℂ) ∈ fixed := by simp [fixed]
  have hne0 (i : Bool) : q i ≠ 0 := fun he => hfixed i (he.symm ▸ h0)
  have hne1 (i : Bool) : q i ≠ 1 := fun he => hfixed i (he.symm ▸ h1)
  have hne : q false ≠ q true := hinj.ne Bool.false_ne_true
  refine ⟨q false, q true, hnear false, hnear true, hne, ?_, ?_⟩
  · exact hspans false 0 1 (Or.inl h0) (Or.inl h1) zero_ne_one (hne0 false) (hne1 false)
  · exact hspans true (q false) 0 (Or.inr ⟨false, rfl⟩) (Or.inl h0)
      (hne0 false) hne.symm (hne0 true)

open Classical in
-- The two fixed axes meet at zero. The third line originally passed through zero as well.
example {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ w, dist w (⟨-1, -1⟩ : ℂ) < ρ ∧
      (0 : ℂ) ∉ affineSpan ℝ ({⟨1, 1⟩, w} : Set ℂ) := by
  let anchor : ℂ := ⟨1, 1⟩
  let fixed : Finset ℂ := {-1, 1, -Complex.I, Complex.I, anchor}
  obtain ⟨q, hnear, _, hfixed, hspans, htriple⟩ :=
    Cslib.exists_injective_perturbation_avoiding_spans_and_crossings
      (fun _ : Unit => ⟨-1, -1⟩) fixed hρ
  let w := q ()
  refine ⟨w, hnear (), ?_⟩
  intro hw
  let a : Fin 3 → ℂ := ![-1, -Complex.I, anchor]
  let b : Fin 3 → ℂ := ![1, Complex.I, w]
  let L := fun i => affineSpan ℝ ({a i, b i} : Set ℂ)
  have hneFixed (x : ℂ) (hx : x ∈ fixed) : x ≠ w := by
    intro h
    apply hfixed ()
    change w ∈ fixed
    exact h ▸ hx
  have hanchor := hneFixed anchor (by simp [fixed])
  have him {x : ℂ} (hx : x ∈ L 0) : x.im = 0 := by
    obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hx
    simpa [a, b, AffineMap.lineMap_apply_module', Complex.real_smul] using
      (congrArg Complex.im ht).symm
  have hre {x : ℂ} (hx : x ∈ L 1) : x.re = 0 := by
    obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hx
    simpa [a, b, AffineMap.lineMap_apply_module', Complex.real_smul] using
      (congrArg Complex.re ht).symm
  have h01 : L 0 ≠ L 1 := by
    intro h
    have h1 : (1 : ℂ) ∈ L 0 := right_mem_affineSpan_pair ℝ (-1) 1
    have hc := hre (h ▸ h1)
    norm_num at hc
  have h02 : L 0 ≠ L 2 := by
    intro h
    have ha : anchor ∈ L 2 := left_mem_affineSpan_pair ℝ anchor w
    have hc := him (h.symm ▸ ha)
    norm_num [anchor] at hc
  have h12 : L 1 ≠ L 2 := by
    intro h
    have ha : anchor ∈ L 2 := left_mem_affineSpan_pair ℝ anchor w
    have hc := hre (h.symm ▸ ha)
    norm_num [anchor] at hc
  have hL : Pairwise (fun i j => L i ≠ L j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals
      first
      | contradiction
      | exact h01
      | exact h01.symm
      | exact h02
      | exact h02.symm
      | exact h12
      | exact h12.symm
  have hpoints (i : Fin 3) :
      a i ∈ (↑fixed : Set ℂ) ∪ Set.range q ∧ b i ∈ (↑fixed : Set ℂ) ∪ Set.range q ∧
        a i ≠ b i := by
    fin_cases i
    · exact ⟨Or.inl (by simp [a, fixed]), Or.inl (by simp [b, fixed]), by
        norm_num [a, b, Complex.ext_iff]⟩
    · exact ⟨Or.inl (by simp [a, fixed]), Or.inl (by simp [b, fixed]), by
        norm_num [a, b, Complex.ext_iff]⟩
    · exact ⟨Or.inl (by simp [a, fixed]), Or.inr ⟨(), rfl⟩, hanchor⟩
  have hhit (i : Fin 3) : (0 : ℂ) ∈ L i := by
    fin_cases i
    · apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
      refine ⟨1 / 2, ?_⟩
      apply Complex.ext <;> norm_num [a, b, AffineMap.lineMap_apply_module', Complex.real_smul]
    · apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
      refine ⟨1 / 2, ?_⟩
      apply Complex.ext <;> norm_num [a, b, AffineMap.lineMap_apply_module', Complex.real_smul]
    · exact hw
  have hzero : (0 : ℂ) ≠ w := by
    intro he
    apply hspans () (-1) 1 (Or.inl (by simp [fixed])) (Or.inl (by simp [fixed]))
      (by norm_num [Complex.ext_iff])
      (hneFixed (-1) (by simp [fixed])).symm (hneFixed 1 (by simp [fixed])).symm
    have hz : (0 : ℂ) ∈ affineSpan ℝ ({-1, 1} : Set ℂ) := hhit 0
    change w ∈ affineSpan ℝ ({-1, 1} : Set ℂ)
    rwa [← he]
  obtain ⟨i, hi⟩ := htriple a b 0 hpoints ⟨2, Or.inr ⟨(), rfl⟩⟩ hL hhit
  fin_cases i <;> rcases hi with h | h <;> simp [a, b, anchor, hzero, Complex.ext_iff] at h
