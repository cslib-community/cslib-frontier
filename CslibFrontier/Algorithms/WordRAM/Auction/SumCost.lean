/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Auction.Instance
public import CslibFrontier.Algorithms.WordRAM.Auction.Workspace
public import CslibFrontier.Computability.WordRAM.ListOutput
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Foundations.Data.Matrix.PairChunks
import CslibFrontier.Tactic.Realize
import Mathlib.Algebra.BigOperators.Fin

/-!
# Accumulating and signed-encoding the optimal assignment cost

Reads the scattered optimal permutation from `ws.outBase` and the `(n + 1)`-scaled shifted costs
from `ws.bC`, sums the unscaled shifted costs `cScaled / ws.scale`, subtracts the shift total
`n * M`, and emits `Signed.encode inst.minCost` in `≤ 2 * n` memory steps.

## Main definitions

* `Cslib.Algorithms.WordRAM.Auction.sumScaledCostProg`,
  `Cslib.Algorithms.WordRAM.Auction.SumScaledCostSafe`: cost-summing and signed-encoding program
  and its safety predicate.

## Main results

* `Cslib.Algorithms.WordRAM.Auction.sumScaledCostProg_realizes`,
  `Cslib.Algorithms.WordRAM.Auction.sumScaledCostProg_spec`: Word-RAM realization and specification
  of `sumScaledCostProg`.
-/

namespace Cslib.Algorithms.WordRAM.Auction

open Cslib.WordRAM
open Cslib.WordRAM.Realization
open Cslib.DataStructure
open Cslib.Algorithms.Lean.Assignment
open StateTransitionSpec (clientResult_bind clientResult_pure clientState_pure)

private structure SumState where
  idx : ℕ
  acc : ℕ

private word_enc_structure encSumState : SumState where
  idx : wordWords, acc : wordWords

private instance : WordEncoding SumState := ⟨2, encSumState⟩

private def sumScaledStep (x : AuctionWS × SumState) : Memory.Prog SumState := do
  let ws := x.1
  let st := x.2
  let j ← Memory.read (ws.outBase + 1 + st.idx)
  let cScaled ← Memory.read (ws.bC + (st.idx * ws.n + j))
  let cUnscaled := cScaled / ws.scale
  pure ⟨st.idx + 1, st.acc + cUnscaled⟩

private abbrev SumScaledStepSafe (w : ℕ) (x : AuctionWS × SumState) (s : Memory.State) : Prop :=
  let ws := x.1
  let st := x.2
  let j := s.mem (ws.outBase + 1 + st.idx)
  let cScaled := s.mem (ws.bC + (st.idx * ws.n + j))
  ws.scale ≠ 0 ∧ Fits w (ws.outBase + 1 + st.idx) ∧ Fits w (st.idx * ws.n) ∧
    Fits w (ws.bC + (st.idx * ws.n + j)) ∧ Fits w (st.idx + 1) ∧
    Fits w (st.acc + cScaled / ws.scale)

private theorem sumScaledStep_realizes :
    Realizes .exact sumScaledStep (appendWords encAuctionWS encSumState) encSumState
      SumScaledStepSafe (fun _ _ => 0) := by
  unfold sumScaledStep
  realize
  all_goals
    rcases h with ⟨_, _, _, _, _, _⟩
    assumption

private theorem four_n_maxMag_add_one_le_wordBound (inst : Instance) :
    4 * (inst.n * inst.maxMag) + 1 ≤ inst.wordBound := by
  unfold Instance.wordBound
  have h : 4 * (inst.n * inst.maxMag) ≤ 4 * (inst.n + 1) * inst.maxMag := by
    calc 4 * (inst.n * inst.maxMag) = 4 * inst.n * inst.maxMag := by ring
      _ ≤ 4 * (inst.n + 1) * inst.maxMag :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 (Nat.le_succ _))
  omega

public section

/-- Sum the unscaled shifted costs along the assignment written at `ws.outBase` and emit
`Signed.encode inst.minCost`. -/
def sumScaledCostProg (ws : AuctionWS) : Memory.Prog ℕ := do
  let res ← iterate sumScaledStep ws ws.n ⟨0, 0⟩
  let shiftTotal := ws.n * ws.M
  if res.acc < shiftTotal then
    pure (2 * (shiftTotal - res.acc) + 1)
  else
    pure (2 * (res.acc - shiftTotal))

/-- Word-width safety predicate for `sumScaledCostProg`. -/
def SumScaledCostSafe (w : ℕ) (ws : AuctionWS) (s : Memory.State) : Prop :=
  let res := (Memory.spec 0).clientResult s (iterate sumScaledStep ws ws.n ⟨0, 0⟩)
  let shiftTotal := ws.n * ws.M
  iterationSafe sumScaledStep SumScaledStepSafe w ws ws.n ⟨0, 0⟩ s ∧
    Fits w 1 ∧ Fits w 2 ∧ Fits w shiftTotal ∧
    (res.acc < shiftTotal →
      res.acc ≤ shiftTotal ∧ Fits w (2 * (shiftTotal - res.acc)) ∧
        Fits w (2 * (shiftTotal - res.acc) + 1)) ∧
    (¬(res.acc < shiftTotal) →
      shiftTotal ≤ res.acc ∧ Fits w (2 * (res.acc - shiftTotal)))

/-- `realize` certificate for `sumScaledCostProg`. -/
theorem sumScaledCostProg_realizes :
    Realizes .exact sumScaledCostProg encAuctionWS wordWords
      SumScaledCostSafe (fun _ _ => 0) := by
  unfold sumScaledCostProg
  realize [sumScaledStep_realizes]
  all_goals
    rcases h with ⟨_, _, _, _, _, _⟩
    tauto

/-- Specification of `sumScaledCostProg`: computes `inst.encodedMinCost` in at most `2 * inst.n`
memory steps. -/
theorem sumScaledCostProg_spec {w : ℕ} (inst : Instance) (ws : AuctionWS)
    (s₀ : Memory.State) (hws : ValidWS ws s₀)
    (hn : ws.n = inst.n) (hscale : ws.scale = inst.n + 1)
    (hM_le : ws.M ≤ inst.maxMag)
    (hM_ge : ∀ i j : Fin inst.n, (inst.cost (i, j)).natAbs ≤ ws.M)
    (hC_mem : ∀ i j : Fin inst.n,
      s₀.mem (ws.bC + (i.val * inst.n + j.val)) =
        (inst.n + 1) * (inst.cost (i, j) + (ws.M : ℤ)).toNat)
    (hout : outputList s₀.mem ws.outBase = inst.assignment)
    (hw : Fits w inst.wordBound)
    (hfit_ws : Fits w (ws.outBase + ws.n + 1)) :
    SumScaledCostSafe w ws s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (sumScaledCostProg ws)) ∧
      memoryCost (sumScaledCostProg ws) s₀ ≤ 2 * inst.n ∧
      (Memory.spec 0).clientResult s₀ (sumScaledCostProg ws) = inst.encodedMinCost := by
  obtain ⟨hbO, hbP, hbS, houtB, hfr⟩ := hws
  have hwb := four_n_maxMag_add_one_le_wordBound inst
  let C_unsc (p : Fin inst.n × Fin inst.n) : ℕ := (inst.cost p + (ws.M : ℤ)).toNat
  have hC_unsc_le : ∀ p : Fin inst.n × Fin inst.n, C_unsc p ≤ 2 * ws.M := by
    rintro ⟨i, j⟩; have := hM_ge i j; dsimp only [C_unsc]; omega
  let π := scaledAuctionPerm inst.cost
  have hmem_out : ∀ i : Fin inst.n, s₀.mem (ws.outBase + 1 + i.val) = (π i).val := fun i => by
    have hi : i.val < (outputList s₀.mem ws.outBase).length := by
      rw [hout, inst.length_assignment]; exact i.isLt
    calc s₀.mem (ws.outBase + 1 + i.val)
        = (outputList s₀.mem ws.outBase)[i.val]'hi := (getElem_outputList _ _ _ hi).symm
      _ = inst.assignment[i.val]'(by simp) := by simp [hout]
      _ = (π i).val := by simp [Instance.assignment, π]
  have hf1 : Fits w 1 := hw.of_le (by unfold Instance.wordBound; omega)
  have hf2 : Fits w 2 := hw.of_le (by unfold Instance.wordBound; omega)
  have hit := iterate_spec sumScaledStep SumScaledStepSafe w ws 2 ws.n
    (fun k st s => s = s₀ ∧ st.idx = k ∧
      st.acc = (((List.finRange inst.n).take k).map fun i => C_unsc (i, π i)).sum ∧
      st.acc ≤ k * (2 * ws.M))
    (fun _ => False)
    (fun k hk st s ⟨hs, hidx, hacc_sum, hacc_le⟩ => by
      subst s; subst hidx
      have hk' : st.idx < inst.n := hn ▸ hk
      let i₀ : Fin inst.n := ⟨st.idx, hk'⟩
      let j₀ : Fin inst.n := π i₀
      have hj_mem : s₀.mem (ws.outBase + 1 + st.idx) = j₀.val := hmem_out i₀
      have hmul_ij : st.idx * ws.n + j₀.val < ws.n * ws.n := by
        rw [hn]
        exact Cslib.Matrix.pairIndex_lt (⟨st.idx, hk'⟩, j₀)
      have hc_mem :
          s₀.mem (ws.bC + (st.idx * ws.n + s₀.mem (ws.outBase + 1 + st.idx))) =
            (inst.n + 1) * C_unsc (i₀, j₀) := by
        rw [hj_mem, hn]; exact hC_mem i₀ j₀
      have hdiv : ((inst.n + 1) * C_unsc (i₀, j₀)) / ws.scale = C_unsc (i₀, j₀) := by
        rw [hscale]; exact Nat.mul_div_right _ (Nat.succ_pos inst.n)
      have hacc_next_le : st.acc + C_unsc (i₀, j₀) ≤ (st.idx + 1) * (2 * ws.M) := by
        rw [Nat.add_mul, one_mul]
        exact Nat.add_le_add hacc_le (hC_unsc_le (i₀, j₀))
      have hacc_fit : Fits w (st.acc + C_unsc (i₀, j₀)) := by
        have hle_max : st.acc + C_unsc (i₀, j₀) ≤ 2 * (inst.n * inst.maxMag) := by
          calc st.acc + C_unsc (i₀, j₀)
              ≤ (st.idx + 1) * (2 * ws.M) := hacc_next_le
            _ ≤ inst.n * (2 * ws.M) := Nat.mul_le_mul_right _ hk'
            _ ≤ inst.n * (2 * inst.maxMag) := Nat.mul_le_mul_left _ (by omega)
            _ = 2 * (inst.n * inst.maxMag) := by ring
        exact hw.of_le (by omega)
      have hmul_idx : st.idx * ws.n ≤ ws.n * ws.n :=
        Nat.mul_le_mul_right ws.n (le_of_lt hk)
      have hsafe : SumScaledStepSafe w (ws, st) s₀ := by
        dsimp only [SumScaledStepSafe]
        refine ⟨by omega, hfit_ws.of_le (by omega),
          hfit_ws.of_le (by omega),
          hfit_ws.of_le (by rw [hj_mem]; omega),
          hfit_ws.of_le (by omega), ?_⟩
        rw [hc_mem, hdiv]
        exact hacc_fit
      have hv : (Memory.spec w).ValidHistory s₀
          ((Memory.spec w).clientHistory s₀ (sumScaledStep (ws, st))) := by
        unfold sumScaledStep
        dsimp only
        exact validHistory_read_bind (by omega)
          (validHistory_read_bind (by rw [hj_mem]; omega) (validHistory_pure w _ _))
      have hmc : memoryCost (sumScaledStep (ws, st)) s₀ ≤ 2 := by
        unfold sumScaledStep
        exact memoryCost_read_bind_le fun _ _ =>
          memoryCost_read_bind_le fun _ _ => Nat.le_refl 0
      have hst_eq : (Memory.spec 0).clientState s₀ (sumScaledStep (ws, st)) = s₀ := by
        unfold sumScaledStep
        rw [clientState_bind_read, clientState_bind_read, clientState_pure]
      refine ⟨hsafe, hv, hmc, by rw [hst_eq], fun _ _ => by rw [hst_eq], hst_eq, ?_⟩
      unfold sumScaledStep
      rw [clientResult_bind_read, clientResult_bind_read, clientResult_pure]
      dsimp only
      rw [hc_mem, hdiv]
      refine ⟨rfl, ?_, hacc_next_le⟩
      rw [hacc_sum, List.take_succ_finRange hk', List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton])
    ⟨0, 0⟩ s₀ ⟨rfl, rfl, by simp, by simp⟩
  obtain ⟨hsafe_it, hv_it, hmc_it, _, _, hs_it, _, hacc_full, hacc_le_n⟩ := hit
  let res := (Memory.spec 0).clientResult s₀ (iterate sumScaledStep ws ws.n ⟨0, 0⟩)
  change res.acc = (((List.finRange inst.n).take ws.n).map fun i => C_unsc (i, π i)).sum
    at hacc_full
  change res.acc ≤ ws.n * (2 * ws.M) at hacc_le_n
  have hsum_z : (res.acc : ℤ) = inst.minCost + ((inst.n * ws.M : ℕ) : ℤ) := by
    rw [hn, List.take_of_length_le (by simp), ← Fin.sum_univ_def] at hacc_full
    rw [hacc_full, Nat.cast_sum]
    have hcu_z : ∀ i : Fin inst.n, (C_unsc (i, π i) : ℤ) =
        inst.cost (i, π i) + (ws.M : ℤ) := fun i => by
      have := hM_ge i (π i); dsimp only [C_unsc]; omega
    simp only [hcu_z, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    dsimp only [Instance.minCost, π]
    push_cast
    ring
  have hf_st : Fits w (ws.n * ws.M) := by
    rw [hn]
    have hle : inst.n * ws.M ≤ inst.n * inst.maxMag := Nat.mul_le_mul_left _ hM_le
    exact hw.of_le (by omega)
  have hpos_safe : res.acc < ws.n * ws.M →
      res.acc ≤ ws.n * ws.M ∧ Fits w (2 * (ws.n * ws.M - res.acc)) ∧
        Fits w (2 * (ws.n * ws.M - res.acc) + 1) := fun hlt => by
    rw [hn] at hlt ⊢
    have hd : 2 * (inst.n * ws.M - res.acc) ≤ 2 * (inst.n * inst.maxMag) :=
      Nat.mul_le_mul_left 2 ((Nat.sub_le _ _).trans (Nat.mul_le_mul_left _ hM_le))
    exact ⟨le_of_lt hlt, hw.of_le (by omega), hw.of_le (by omega)⟩
  have hneg_safe : ¬(res.acc < ws.n * ws.M) →
      ws.n * ws.M ≤ res.acc ∧ Fits w (2 * (res.acc - ws.n * ws.M)) := fun hlt => by
    rw [hn] at hlt hacc_le_n ⊢
    have hd : 2 * (res.acc - inst.n * ws.M) ≤ 4 * (inst.n * inst.maxMag) := by
      calc 2 * (res.acc - inst.n * ws.M)
          ≤ 2 * (inst.n * (2 * ws.M)) :=
            Nat.mul_le_mul_left 2 ((Nat.sub_le _ _).trans hacc_le_n)
        _ ≤ 2 * (inst.n * (2 * inst.maxMag)) :=
            Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (by omega))
        _ = 4 * (inst.n * inst.maxMag) := by ring
    exact ⟨le_of_not_gt hlt, hw.of_le (by omega)⟩
  unfold sumScaledCostProg
  refine ⟨⟨hsafe_it, hf1, hf2, hf_st, hpos_safe, hneg_safe⟩,
    validHistory_bind_step hv_it
      (validHistory_ite (fun _ => validHistory_pure w _ _) (fun _ => validHistory_pure w _ _)),
    ?_, ?_⟩
  · rw [memoryCost_bind', memoryCost_ite]
    split_ifs <;> {
      rw [memoryCost_pure, Nat.add_zero]
      exact hmc_it.trans_eq (by rw [hn]) }
  · rw [clientResult_bind, hs_it]
    change (Memory.spec 0).clientResult s₀
      (if res.acc < ws.n * ws.M then pure (2 * (ws.n * ws.M - res.acc) + 1)
       else pure (2 * (res.acc - ws.n * ws.M))) = _
    unfold Instance.encodedMinCost Signed.encode
    rw [hn]
    by_cases hlt : res.acc < inst.n * ws.M
    · have hneg : inst.minCost < 0 := by omega
      have habs : inst.minCost.natAbs = inst.n * ws.M - res.acc := by omega
      rw [ite_eq_left hlt, clientResult_pure, habs, ite_eq_left hneg]
    · have hnneg : ¬inst.minCost < 0 := by omega
      have habs : inst.minCost.natAbs = res.acc - inst.n * ws.M := by omega
      rw [ite_eq_right hlt, clientResult_pure, habs, ite_eq_right hnneg, Nat.add_zero]

end

end Cslib.Algorithms.WordRAM.Auction
