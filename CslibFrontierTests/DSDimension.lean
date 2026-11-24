/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.MachineLearning.PACLearning.DSDimension
public import CslibFrontier.MachineLearning.PACLearning.Halfspaces
import Mathlib.Tactic.NormNum

/-!
# Checks for Graph Dimension, Pseudo-Cubes, and the Daniely–Shalev-Shwartz Dimension

Exercises `CslibFrontier.MachineLearning.PACLearning.DSDimension`:

1. **Pseudo-cube boundary witnesses:** positive 6-cycle pseudo-cube on `Fin 2 → Fin 3` (`card = 6`),
   and negative checks for the empty set, a 3-element punctured Boolean square, and a 5-element
   punctured 6-cycle (`card = 5 ≥ 2 ^ 2` yet missing a coordinate neighbor).
2. **Binary consistency with halfspaces:** on `homogeneousHalfspaces 3`, `natarajanDim`, `dsDim`,
   `graphDim`, and `evcDim (conceptGraph _)` all evaluate to `3`.
3. **Graph-dimension Sauer–Shelah bound:** any class on `Fin 3 → Fin 3` with `graphDim ≤ 1` has at
   most `1 + 9 = 10` of the `27` functions, satisfied by constant functions (`graphDim = 1`).
4. **Three-label separation (`hexagonClass`) and quantitative `O(d log |β|)` bound:** checks
   `natarajanDim hexagonClass < dsDim hexagonClass` (`1 < 2`), `hexagonClass.ncard = 6`, and the
   explicit finite-label upper bound on `ℕ → Fin 4`.
5. **Infinite-label separation on `ℕ` (`revealingSetClass ℕ`):** `natarajanDim = dsDim = 1` and
   `HasFiniteDSDim` hold while `{0, 1, 2}` (and every finite subset) is G-shattered, so
   `graphDim = ⊤` and `¬ HasFiniteGraphDim`.
-/

public section

namespace CslibFrontierTests.DSDimension

open Cslib.MachineLearning.PACLearning Finset

/-! ## 1. Pseudo-cube positive and negative boundary checks -/

/-- The 6 off-diagonal maps `Fin 2 → Fin 3` form a non-Boolean 2-dimensional pseudo-cube. -/
def offDiagCube : Finset (Fin 2 → Fin 3) :=
  Finset.univ.filter fun f => f 0 ≠ f 1

theorem card_offDiagCube : offDiagCube.card = 6 := by decide

theorem isPseudoCube_offDiagCube : IsPseudoCube offDiagCube := by
  refine ⟨⟨![0, 1], by decide⟩, fun f hf i => ?_⟩
  have hex : ∀ a b : Fin 3, ∃ c : Fin 3, c ≠ a ∧ c ≠ b := by decide
  obtain ⟨b, hb0, hb1⟩ := hex (f 0) (f 1)
  refine ⟨Function.update f i b, ?_, ?_, fun j hj => Function.update_of_ne hj b f⟩
  · rw [offDiagCube, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    fin_cases i
    · simp [hb1]
    · simp [hb0.symm]
  · fin_cases i
    · simpa using hb0
    · simpa using hb1

/-- Empty families are never pseudo-cubes. -/
theorem not_isPseudoCube_empty : ¬ IsPseudoCube (∅ : Finset (Fin 2 → Bool)) :=
  fun h => not_nonempty_empty h.1

/-- Removing one corner from `{0, 1}²` breaks `IsPseudoCube` (violating `2 ^ 2 ≤ card`). -/
theorem not_isPseudoCube_puncturedSquare :
    ¬ IsPseudoCube ((Finset.univ : Finset (Fin 2 → Bool)).erase fun _ => false) := by
  intro h
  have hle := h.two_pow_card_le_card
  have hcard : ((Finset.univ : Finset (Fin 2 → Bool)).erase fun _ => false).card = 3 := by decide
  rw [Fintype.card_fin, hcard] at hle
  omega

/-- Removing `![0, 1]` from `offDiagCube` leaves `5 ≥ 2 ^ 2` labelings, yet `![2, 1]` loses its
unique coordinate-`0` neighbor inside `offDiagCube`, so `IsPseudoCube` fails. -/
theorem not_isPseudoCube_puncturedHexagon :
    (offDiagCube.erase ![0, 1]).card = 5 ∧ ¬ IsPseudoCube (offDiagCube.erase ![0, 1]) := by
  refine ⟨by decide, fun ⟨_, hnbr⟩ => ?_⟩
  have hmem : (![2, 1] : Fin 2 → Fin 3) ∈ offDiagCube.erase ![0, 1] := by decide
  obtain ⟨g, hg_mem, hg0_ne, hg1_eq⟩ := hnbr ![2, 1] hmem 0
  have hg1 : g 1 = 1 := hg1_eq 1 (by decide)
  have hg_off : g 0 ≠ g 1 := (mem_filter.mp (mem_erase.mp hg_mem).2).2
  have hg_ne01 : g ≠ ![0, 1] := (mem_erase.mp hg_mem).1
  have hg0_val : g 0 = 0 := by
    have h2 : g 0 ≠ 2 := by simpa using hg0_ne
    have h1 : g 0 ≠ 1 := hg1 ▸ hg_off
    generalize hg0 : g 0 = z at h1 h2
    fin_cases z <;> contradiction
  apply hg_ne01
  funext i
  fin_cases i
  · exact hg0_val
  · exact hg1

/-! ## 2. Binary consistency on homogeneous halfspaces in `ℝ³` -/

theorem halfspaces_three_dimensions_agree :
    natarajanDim (homogeneousHalfspaces 3) = 3 ∧
    dsDim (homogeneousHalfspaces 3) = 3 ∧
    graphDim (homogeneousHalfspaces 3) = 3 ∧
    evcDim (conceptGraph (homogeneousHalfspaces 3)) = 3 := by
  have hfin : HasFiniteVCDim (homogeneousHalfspaces 3) := by
    rw [homogeneousHalfspaces_eq_positivityClass]
    exact hasFiniteVCDim_positivityClass _
  have hevc : evcDim (homogeneousHalfspaces 3) = 3 := by
    rw [← natCast_vcDim hfin, vcDim_homogeneousHalfspaces]
    norm_num
  refine ⟨(natarajanDim_eq_evcDim _).trans hevc,
    (dsDim_eq_evcDim _).trans hevc,
    (graphDim_eq_evcDim _).trans hevc,
    (graphDim_eq_evcDim_conceptGraph _).symm.trans ((graphDim_eq_evcDim _).trans hevc)⟩

/-! ## 3. Graph-dimension Sauer–Shelah growth bound on `Fin 3 → Fin 3` -/

/-- Any class on `Fin 3 → Fin 3` with `graphDim C ≤ 1` contains at most `1 + 9 = 10` of the `27`
functions. -/
theorem ncard_le_ten_of_graphDim_le_one {C : ConceptClass (Fin 3) (Fin 3)}
    (hC : graphDim C ≤ 1) : C.ncard ≤ 10 := by
  have heq : ((· ∘ (id : Fin 3 → Fin 3)) '' C) = C := Set.image_id C
  have h := ncard_restriction_le_sum_choose_graphDim (d := 1) hC (id : Fin 3 → Fin 3)
  rw [heq, Fintype.card_fin] at h
  exact h.trans (by decide)

/-- Constant functions on `Fin 3 → Fin 3` have `graphDim = 1` and `ncard = 3 ≤ 10`. -/
def constFin3 : ConceptClass (Fin 3) (Fin 3) :=
  Set.range fun b : Fin 3 => fun _ : Fin 3 => b

theorem graphDim_constFin3_and_ncard :
    graphDim constFin3 = 1 ∧ constFin3.ncard = 3 ∧ constFin3.ncard ≤ 10 := by
  have hle1 : graphDim constFin3 ≤ 1 := by
    refine graphDim_le_iff.mpr fun W hW => ?_
    by_contra hgt
    have hnot : ¬ W.card ≤ 1 := fun h => hgt (by exact_mod_cast h)
    obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp (by omega : 1 < W.card)
    obtain ⟨f, hf⟩ := hW
    obtain ⟨_, ⟨b_all, rfl⟩, hall, _⟩ := hf ↑W Set.Subset.rfl
    obtain ⟨_, ⟨b_x, rfl⟩, hbx, hnotx⟩ := hf {x} (by simp [hx])
    have hfx : b_all = f x := hall x hx
    have hfy : b_all = f y := hall y hy
    have hbx_eq : b_x = f x := hbx x rfl
    have hby_ne : b_x ≠ f y := hnotx y ⟨hy, fun h => hxy (Set.mem_singleton_iff.mp h).symm⟩
    exact hby_ne (hbx_eq.trans (hfx.symm.trans hfy))
  have hge1 : (1 : ℕ∞) ≤ graphDim constFin3 := by
    have hsh : GraphShatters constFin3 (↑({0} : Finset (Fin 3)) : Set (Fin 3)) := by
      refine ⟨fun _ => 0, fun B hB => ?_⟩
      by_cases h0 : (0 : Fin 3) ∈ B
      · refine ⟨fun _ => 0, ⟨0, rfl⟩, fun _ _ => rfl, fun x hx => ?_⟩
        have : x = 0 := by simpa using hx.1
        subst this; exact (hx.2 h0).elim
      · refine ⟨fun _ => 1, ⟨1, rfl⟩, fun x hx => ?_, fun _ _ => by simp⟩
        have : x = 0 := by simpa using hB hx
        subst this; exact (h0 hx).elim
    simpa using hsh.card_le_graphDim
  have hdim : graphDim constFin3 = 1 := le_antisymm hle1 hge1
  have hcard : constFin3.ncard = 3 := by
    have hinj : Function.Injective (fun b : Fin 3 => fun _ : Fin 3 => b) :=
      fun b₁ b₂ h => congrFun h 0
    rw [constFin3, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
  exact ⟨hdim, hcard, ncard_le_ten_of_graphDim_le_one hle1⟩

/-! ## 4. Three-label separation (`hexagonClass`) and quantitative `O(d log |β|)` bound -/

theorem hexagonClass_strict_separation_and_card :
    natarajanDim hexagonClass < dsDim hexagonClass ∧
    dsDim hexagonClass = graphDim hexagonClass ∧
    hexagonClass.ncard = 6 := by
  have hcard : hexagonClass.ncard = 6 := by
    have heq : (offDiagCube : Set (Fin 2 → Fin 3)) = hexagonClass := by
      ext f
      simp [offDiagCube, hexagonClass]
    rw [← heq, Set.ncard_coe_finset, card_offDiagCube]
  rw [natarajanDim_hexagonClass, dsDim_hexagonClass, graphDim_hexagonClass]
  exact ⟨by decide, rfl, hcard⟩

/-- Explicit quantitative bound on `ℕ → Fin 4`: any class with `natarajanDim C ≤ 2` satisfies
`dsDim C ≤ graphDim C ≤ 4 * 2 * (⌊log₂ 4⌋ + 2) = 32`. -/
theorem nat_fin4_quantitative_bound {C : ConceptClass ℕ (Fin 4)}
    (hd : natarajanDim C ≤ 2) :
    dsDim C ≤ 32 ∧ graphDim C ≤ 32 := by
  have hlog : Nat.log 2 (Fintype.card (Fin 4)) = 2 := by
    rw [Fintype.card_fin]
    decide
  have hg : graphDim C ≤ 32 := by
    calc graphDim C
        ≤ 4 * natarajanDim C * (Nat.log 2 (Fintype.card (Fin 4)) + 2) :=
          graphDim_le_mul_natarajanDim C
      _ ≤ 4 * 2 * ((2 : ℕ) + 2) := by
          rw [hlog]
          gcongr
      _ = 32 := by norm_num
  exact ⟨(dsDim_le_graphDim C).trans hg, hg⟩

/-! ## 5. Infinite-label separation on `ℕ` (`revealingSetClass ℕ`) -/

theorem revealingSetClass_nat_separation :
    natarajanDim (revealingSetClass ℕ) = 1 ∧
    dsDim (revealingSetClass ℕ) = 1 ∧
    HasFiniteDSDim (revealingSetClass ℕ) ∧
    graphDim (revealingSetClass ℕ) = ⊤ ∧
    ¬ HasFiniteGraphDim (revealingSetClass ℕ) ∧
    GraphShatters (revealingSetClass ℕ) (↑({0, 1, 2} : Finset ℕ) : Set ℕ) ∧
    ¬ DSShatters (revealingSetClass ℕ) (↑({0, 1} : Finset ℕ) : Set ℕ) := by
  have hds : dsDim (revealingSetClass ℕ) = 1 := dsDim_revealingSetClass
  have hg : graphDim (revealingSetClass ℕ) = ⊤ := graphDim_revealingSetClass_of_infinite
  refine ⟨natarajanDim_revealingSetClass, hds, by simp [HasFiniteDSDim, hds], hg,
    by simp [HasFiniteGraphDim, hg], graphShatters_revealingSetClass {0, 1, 2}, fun hsh => ?_⟩
  have hle := card_le_one_of_dsShatters_revealingSetClass hsh
  have hcard : ({0, 1} : Finset ℕ).card = 2 := by decide
  omega

end CslibFrontierTests.DSDimension
