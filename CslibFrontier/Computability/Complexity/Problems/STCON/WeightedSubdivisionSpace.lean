/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.SeedSearchSetup
public import CslibFrontier.Computability.Complexity.Problems.STCON.WeightedSubdivisionCall
import CslibFrontier.Foundations.Data.Nat.Log

/-!
# Weighted adjacency from initialized scan IDs

## Main results

* `Cslib.Complexity.STCON.configurationWeightedSubdivisionCallback_states_le`: for any
  two in-range scan IDs, the weighted callback's live state through return fits in linear
  space in its retained context plus logarithmic overhead in the original input length.
* `Cslib.Complexity.STCON.configurationWeightedSubdivisionCallback_agrees`: the same call
  from two initialized scan IDs first halts with the generated subdivision edge verdict,
  given the Justesen code-bit agreement.
-/

public section

namespace Cslib.Complexity.STCON

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeNTM.ConfigurationGraph
open _root_.Turing.QueryMachine.Subdivision
open Cslib.Code.JustesenFamily Cslib.Reachability.Hoza Cslib.LayeredDigraph.Subdivision

variable {k : ℕ} {State Context : Type} [Fintype State]

private theorem subdivisionIndex_symm_val (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    ∀ i : Fin size.vertexCount,
      (subdivisionIndex I size.chainBound ((configurationSubdivisionIndex ntm c w).symm i)).val =
        i.val := by
  intro I size i
  rw [← configurationSubdivisionIndex_val ntm c w, Equiv.apply_symm_apply]

/-- From two IDs in the initialized carrier, the weighted callback first halts at clock
three and returns the generated subdivision edge verdict, provided the code bits for
the source column agree with the Justesen code. -/
theorem configurationWeightedSubdivisionCallback_agrees (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) (ctx : Context) (params : Context → LayeredParameters)
    (rank seedWidth : Context → ℕ) (code : Context × ℕ → ℕ → Bool)
    (hp : params ctx = layeredParameters ntm c w.length) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    let index := configurationSubdivisionIndex ntm c w
    ∀ (u v : Fin size.vertexCount) (seed : Fin (2 ^ codeLength I.n (I.n - 1))),
      rank ctx = seed.val → seedWidth ctx = codeLength I.n (I.n - 1) →
      (∀ i : Fin (codeLength I.n (I.n - 1)),
        code (ctx, (index.symm u).vertex.2.val) i.val =
          indexedCodewordMod (index.symm u).vertex.2 i) →
      let M := weightedSubdivisionCallback ntm params rank seedWidth code
      let start := flatCallbackStart ⟨ctx, size.chainBound, u.val, v.val⟩
      (∀ t < 3, M.halted (M.runFrom w start t) = false) ∧
      ∃ answer, M.runFrom w start 3 = .inl (.inr answer) ∧
        M.halted (M.runFrom w start 3) = true ∧
        (answer = true ↔ (graph (layeredDigraph I)
          (generatedWeight ((BitString.equivFin _).symm seed)) size.chainBound).Adj
          (index.symm u) (index.symm v)) := by
  intro I size index u v seed hr hs hc
  have h := weightedSubdivisionCallback_agrees ntm c w ctx params rank seedWidth code hp
    (index.symm u) (index.symm v) seed hr hs hc
  dsimp only at h
  rw [subdivisionIndex_symm_val, subdivisionIndex_symm_val] at h
  exact h

/-- The scan can charge the suspended original-edge call and decoded request to the same
budget at every clock through return. The retained context is charged separately. -/
theorem configurationWeightedSubdivisionCallback_states_le (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (encContext : Context ↪ List Bool) (params : Context → LayeredParameters)
    (rank seedWidth : Context → ℕ) (code : Context × ℕ → ℕ → Bool) :
    ∃ C, ∀ (w : List Bool) (ctx : Context), params ctx = layeredParameters ntm c w.length →
      ∀ (u v : ℕ),
        let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
        u < size.vertexCount → v < size.vertexCount →
        let q : FlatQuery Context := ⟨ctx, size.chainBound, u, v⟩
        let M := weightedSubdivisionCallback ntm params rank seedWidth code
        ∀ t ≤ 3,
          (encCallback encContext encLayeredCallback (M.runFrom w (flatCallbackStart q) t)).length ≤
            C * ((encContext ctx).length + (Nat.log2 w.length + 1)) := by
  obtain ⟨R, hR⟩ := length_configurationSubdivisionRequest_le ntm c encContext
  let D := 12 * (radixExponent State c * Fintype.card (Register k) + 1)
  refine ⟨2 * R + 2 * D + 16, fun w ctx hp u v hu hv t ht => ?_⟩
  let index := configurationSubdivisionIndex ntm c w
  have h := weightedSubdivisionCallback_states_le ntm c w encContext ctx params
    rank seedWidth code hp (index.symm ⟨u, hu⟩) (index.symm ⟨v, hv⟩) t ht
  dsimp only at h
  rw [subdivisionIndex_symm_val, subdivisionIndex_symm_val] at h
  have hsucc : Nat.log2 (w.length + 1) ≤ Nat.log2 w.length + 1 := by
    simpa only [Nat.log2_eq_log_two] using Nat.log_add_one_le 2 w.length
  let budget := (encContext ctx).length + (Nat.log2 w.length + 1)
  calc
    _ ≤ 2 * (R * budget) + D * (2 * budget) + 16 :=
      h.trans <| Nat.add_le_add_right (Nat.add_le_add
        (Nat.mul_le_mul_left 2 (hR w ctx u v hu hv).2)
        (Nat.mul_le_mul_left D (by omega))) 16
    _ = (2 * R + 2 * D) * budget + 16 := by ring
    _ ≤ (2 * R + 2 * D + 16) * budget := by
      rw [Nat.add_mul (2 * R + 2 * D) 16 budget]
      exact Nat.add_le_add_left (Nat.le_mul_of_pos_right _ (by omega)) _

end Cslib.Complexity.STCON
