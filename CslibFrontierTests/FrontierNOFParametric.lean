/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Circuit.Frontier.Layouts.ParametricCut
import CslibFrontier.Computability.Circuit.Frontier.NOFFormula

/-! Checked clients for `NOFFormula` and `Layouts.ParametricCut` across the module boundary. -/

open Cslib.Circuits Cslib.Circuits.Frontier Cslib.Communication Cslib.Probability

namespace CslibFrontierTests.FrontierNOFParametric

/-! ### 1. Parametric RFIM min-cut monotonicity and `lowerKey` on cubic multigraphs -/

example (V E : Type) [Finite V] [Finite E] (G : Multigraph V E) (y : V → ℝ) :
    Monotone (G.rfimMinCut y (1 / 2)) :=
  G.rfimMinCut_mono y (by norm_num)

example (V E : Type) [DecidableEq V] [Finite V] [Finite E] (G : Multigraph V E) (y : V → ℝ)
    (A B : Finset V) (hA : G.IsRFIMMinCut y 1 0 A) (hB : G.IsRFIMMinCut y 1 1 B) :
    A ⊆ B :=
  hA.subset_of_lt hB zero_lt_one zero_lt_one

example (y : Fin 2 → ℝ) (hy : Function.Injective y) (t : ℝ) :
    let thetaGraph : Multigraph (Fin 2) (Fin 3) := { src := fun _ => 0, tgt := fun _ => 1 }
    {v : Fin 2 | thetaGraph.lowerKey y v = t}.ncard ≤ 4 ∧
      (thetaGraph.edgeCut (thetaGraph.lowerSublevel y t)).ncard +
        2 * (thetaGraph.internalEdges (thetaGraph.innerFrontierClass y t 2)).ncard =
        (thetaGraph.innerFrontierClass y t 1).ncard +
          (thetaGraph.innerFrontierClass y t 2).ncard ∧
      (thetaGraph.edgeCut (thetaGraph.lowerSublevel y t)).ncard ≤
        (Switched.innerFrontier thetaGraph.toSimpleGraph y t).card := by
  intro thetaGraph
  have hloop : thetaGraph.Loopless := fun _ => Fin.zero_ne_one
  have h3 : ∀ v : Fin 2, (thetaGraph.incidenceSet v).ncard = 3 := by
    intro v
    have : thetaGraph.incidenceSet v = Set.univ := by
      fin_cases v <;> (ext e; simp [Multigraph.incidenceSet, thetaGraph])
    rw [this, Set.ncard_univ, Nat.card_fin]
  exact ⟨thetaGraph.ncard_lowerKey_eq_le_four h3 hy t,
    thetaGraph.ncard_edgeCut_lowerSublevel_add_two_mul hloop h3 y t,
    thetaGraph.ncard_edgeCut_lowerSublevel_le_switched_innerFrontier hloop h3 y t⟩

/-! ### 2. Exact Hall balance, read-`r` formula NOF compilation, and `Ω(n log n)` discrepancy -/

example (bags : Fin 3 → Finset (Fin 12))
    (hread : ∀ i : Fin 12, (Finset.univ.filter fun j : Fin 3 => i ∈ bags j).card ≤ 2)
    (hcap : ∀ j : Fin 3, (bags j).card ≤ 8) :
    ∃ owner : Fin 12 → Fin 3,
      (∀ i : Fin 12, i ∉ bags (owner i)) ∧
      ∀ j : Fin 3, 2 ≤ (Finset.univ.filter fun i : Fin 12 => owner i = j).card :=
  exists_nof_partition_of_bag_card_le (n := 12) (r := 2) (by omega) bags hread hcap

example (σ : Signature.{0}) (I : Interpretation σ Bool) (F : Formula σ 24)
    (hfan : F.FanInAtMost 2) (hread : F.ReadAtMost 2) :
    ∃ X : Fin 3 → Finset (Fin 24),
      Pairwise (fun j₁ j₂ => Disjoint (X j₁) (X j₂)) ∧
      (∀ j : Fin 3, (X j).card = 2) ∧
      ∀ z : Fin 24 → Bool, ∃ p : NOF.Protocol (fun j : Fin 3 => X j → Bool) Bool,
        (∀ y, p.run y = F.eval I (embedBlocks X z y)) ∧
        p.depth ≤ 17 := by
  obtain ⟨X, hdisj, hcard, hprot⟩ :=
    exists_nof_protocol_of_readAtMost (n := 24) (r := 2) (by omega) (by omega) I F hfan hread
  refine ⟨X, hdisj, hcard, fun z => ?_⟩
  obtain ⟨p, hrun, -, hdepth⟩ := hprot z
  exact ⟨p, hrun, hdepth⟩

example (σ : Signature.{0}) (I : Interpretation σ Bool) :
    let F : Formula σ 64 := .input 0
    ∃ X : Fin 2 → Finset (Fin 64),
      Pairwise (fun j₁ j₂ => Disjoint (X j₁) (X j₂)) ∧
      (∀ j : Fin 2, (X j).card = 16) ∧
      ∀ z : Fin 64 → Bool, ∃ p : NOF.Protocol (fun j : Fin 2 => X j → Bool) Bool,
        (∀ y, p.run y = F.eval I (embedBlocks X z y)) ∧
        p.depth ≤ 3 := by
  intro F
  have h := exists_nof_protocol_of_formula (n := 64) (by omega) I F trivial
  have hleaf : F.leafSize = 1 := rfl
  dsimp only at h
  rwa [hleaf] at h

example (n : ℕ) :
    ∃ f : (Fin n → Bool) → Bool,
      ∀ {σ : Signature.{0}} (I : Interpretation σ Bool) {F : Formula σ n},
        F.FanInAtMost 2 → F.Computes I f → n * (Nat.log 2 n - 12) ≤ 16 * F.leafSize :=
  exists_function_mul_log_le_leafSize n

example :
    ∃ f : (Fin 65536 → Bool) → Bool,
      ∀ {σ : Signature.{0}} (I : Interpretation σ Bool) {F : Formula σ 65536},
        F.FanInAtMost 2 → F.Computes I f → 16384 ≤ F.leafSize := by
  obtain ⟨f, hf⟩ := exists_function_mul_log_le_leafSize 65536
  refine ⟨f, fun {_σ} I {_F} hfan hcomp => ?_⟩
  have h := hf I hfan hcomp
  have hlog : Nat.log 2 65536 = 16 := by decide
  rw [hlog] at h
  omega

end CslibFrontierTests.FrontierNOFParametric
