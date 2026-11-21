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
# Live states of weighted adjacency from initialized scan IDs

## Main results

* `Cslib.Complexity.STCON.configurationWeightedSubdivisionCallback_states_le`: for any
  two in-range scan IDs, the weighted callback's live state through return fits in linear
  space in its retained context plus logarithmic overhead in the original input length.
-/

public section

namespace Cslib.Complexity.STCON

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeNTM.ConfigurationGraph
open _root_.Turing.QueryMachine.Subdivision

variable {k : ℕ} {State Context : Type} [Fintype State]

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
  let I := configurationInstance ntm c w
  let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
  let index := subdivisionIndex I size.chainBound
  let a := index.symm ⟨u, (configurationSeedSearchSetup_vertexCount ntm c w) ▸ hu⟩
  let b := index.symm ⟨v, (configurationSeedSearchSetup_vertexCount ntm c w) ▸ hv⟩
  have ha : (index a).val = u := Fin.val_eq_of_eq (index.apply_symm_apply _)
  have hb : (index b).val = v := Fin.val_eq_of_eq (index.apply_symm_apply _)
  have h := weightedSubdivisionCallback_states_le ntm c w encContext ctx params
    rank seedWidth code hp a b t ht
  dsimp only at h
  rw [ha, hb] at h
  have hreq := (hR w ctx u v hu hv).2
  let L := Nat.log2 w.length + 1
  let budget := (encContext ctx).length + L
  have hlog : Nat.log2 (w.length + 1) + 1 ≤ 2 * budget := by
    have hsucc : Nat.log2 (w.length + 1) ≤ Nat.log2 w.length + 1 := by
      simpa only [Nat.log2_eq_log_two] using Nat.log_add_one_le 2 w.length
    dsimp [budget, L]
    omega
  calc
    _ ≤ 2 * (R * budget) + D * (2 * budget) + 16 :=
      h.trans (Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 2 hreq)
        (Nat.mul_le_mul_left D hlog)) 16)
    _ = (2 * R + 2 * D) * budget + 16 := by ring
    _ ≤ (2 * R + 2 * D + 16) * budget := by
      rw [Nat.add_mul (2 * R + 2 * D) 16 budget]
      have hpos : 0 < budget := by dsimp [budget, L]; omega
      exact Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hpos) _

end Cslib.Complexity.STCON
