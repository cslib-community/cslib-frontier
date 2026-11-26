/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Assignment.Auction
public import CslibFrontier.Algorithms.WordRAM.Auction.Instance
public import CslibFrontier.Computability.WordRAM.ListOutput
public import CslibFrontier.Computability.WordRAM.Signed.Encoding
import CslibFrontier.Algorithms.WordRAM.Auction.Solve
import CslibFrontier.Algorithms.WordRAM.Auction.SumCost
import CslibFrontier.Algorithms.WordRAM.Auction.Workspace
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontier.Tactic.Realize
import Mathlib.Tactic.Linarith

/-!
# Bertsekas's auction algorithm on the word RAM

This module re-exports the public problem instances from `Auction.Instance` and exposes the uniform
standard-basis Word-RAM running-time theorems for Bertsekas's Gauss–Seidel `ε`-auction algorithm
(`Cslib.Algorithms.Lean.Assignment.auction` and `Cslib.Algorithms.Lean.Assignment.scaledAuction`).
The `Memory.Prog` implementation and proof are organized into focused submodules under
`CslibFrontier.Algorithms.WordRAM.Auction`:

* `Auction.Instance`: public `Instance` and `EpsInstance` definitions, encodings, and fit bounds.
* `Auction.Workspace`: workspace record `AuctionWS`, `AuctionMem`, `ValidWS`, and shared
  reduced-cost readout lemma `AuctionMem.redCost_read`.
* `Auction.ScanFill`: input magnitude scan `scanMaxProg` and shifted-scaled cost fill `fillCProg`.
* `Auction.RowScan`: `O(n)` row scans `findBestProg` and `findSecondProg`.
* `Auction.BidStep`: single Gauss–Seidel bid step `bidStepProg` (`≤ 4 n + 6` memory ops).
* `Auction.Loop`: workspace array initialization and bounded-while core `auctionCoreProg`.
* `Auction.Scatter`: scattering `owner` to length-prefixed output memory (`scatterProg`).
* `Auction.SumCost`: unscaling and summing the optimal cost (`sumScaledCostProg`).
* `Auction.Solve`: end-to-end clients `epsMainProg` and `scaledSolveProg`.

## Main definitions

* `Cslib.Algorithms.WordRAM.Auction.Instance`,
  `Cslib.Algorithms.WordRAM.Auction.EpsInstance`: problem instances for the exact `(n + 1)`-scaled
  integer auction and unscaled `ε`-auction, with their encodings, `maxMag`, `rowSpread`,
  `wordBound`, and outputs (`assignment`, `minCost`, `encodedMinCost`).

## Main results

* `Cslib.Algorithms.WordRAM.Auction.exists_epsAuction_program`: uniform deterministic width-blind
  `Program .standard r` (`¬ prog.ReadsWidth`, `prog.IsRandFree`) computing `EpsInstance.assignment`
  in `K * (inst.n ^ 2 * (C / inst.eps + 1) + 1)` instructions (`ExecutesList` and
  `Program.ComputesListInTime`; `n * eps`-optimal by `sum_auctionPerm_le`).
* `Cslib.Algorithms.WordRAM.Auction.exists_scaledAuction_program`: uniform deterministic width-blind
  `Program .standard r` (`¬ prog.ReadsWidth`, `prog.IsRandFree`) computing `Instance.assignment` in
  `K * (inst.n ^ 3 * C + inst.n ^ 2 + 1)` instructions (`ExecutesList` and
  `Program.ComputesListInTime`; optimal by `sum_scaledAuctionPerm_le`).
* `Cslib.Algorithms.WordRAM.Auction.exists_scaledMinCost_program`: uniform deterministic width-blind
  `Program .standard r` (`¬ prog.ReadsWidth`, `prog.IsRandFree`) computing
  `Instance.encodedMinCost` in `K * (inst.n ^ 3 * C + inst.n ^ 2 + 1)` instructions (`Executes` and
  `Program.ComputesInTime`).

## References

* [Bertsekas1979]
* [Bertsekas1988]
* [Bertsekas1998]
-/

namespace Cslib.Algorithms.WordRAM.Auction

open Cslib.WordRAM
open Cslib.WordRAM.Realization
open Cslib.DataStructure
open StateTransitionSpec (clientResult_bind clientState_bind clientResult_pure clientState_pure)

private def scaledMainProg (n : ℕ) : Memory.Prog ℕ := do
  let ws ← scaledSolveProg n
  pure ws.outBase

private theorem scaledMainProg_realizes :
    Realizes .exact scaledMainProg wordWords wordWords ScaledSolveSafe (fun _ _ => 0) := by
  unfold scaledMainProg
  realize [scaledSolveProg_realizes]
  exact h

private def scaledMinCostMainProg (n : ℕ) : Memory.Prog ℕ := do
  let ws ← scaledSolveProg n
  sumScaledCostProg ws

private abbrev ScaledMinCostSafe (w n : ℕ) (s₀ : Memory.State) : Prop :=
  let ws := (Memory.spec 0).clientResult s₀ (scaledSolveProg n)
  let s' := (Memory.spec 0).clientState s₀ (scaledSolveProg n)
  ScaledSolveSafe w n s₀ ∧ SumScaledCostSafe w ws s'

private theorem scaledMinCostMainProg_realizes :
    Realizes .exact scaledMinCostMainProg wordWords wordWords ScaledMinCostSafe (fun _ _ => 0) := by
  unfold scaledMinCostMainProg
  realize [scaledSolveProg_realizes, sumScaledCostProg_realizes]
  exacts [h.1, h.2]

private theorem eps_poly_bound (n C eps : ℕ) (hε : 0 < eps) :
    (n * (C + eps) / eps + 1) * (4 * n + 6) + 3 * (n * n) + 5 * n + 3 + 1 ≤
      42 * (n ^ 2 * (C / eps + 1) + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hq : 1 ≤ C / eps + 1 := Nat.succ_pos _
  have hC : C + eps ≤ 2 * (C / eps + 1) * eps := by
    have := Nat.lt_div_mul_add (a := C) hε
    nlinarith
  have hdiv : n * (C + eps) / eps ≤ 2 * n * (C / eps + 1) :=
    Nat.div_le_of_le_mul (by nlinarith [Nat.mul_le_mul_left n hC])
  calc _ ≤ (2 * n * (C / eps + 1) + 1) * (4 * n + 6) + 3 * (n * n) + 5 * n + 3 + 1 := by gcongr
    _ ≤ _ := by
      nlinarith [Nat.mul_le_mul_left (n * n) hq, Nat.mul_le_mul_left (n * (C / eps + 1)) hn,
        Nat.mul_le_mul_left n hq]

private theorem scaled_poly_bound (n C : ℕ) :
    (n * ((n + 1) * C + 1) + 1) * (4 * n + 6) + 3 * (n * n) + 7 * n + 3 + 1 ≤
      34 * (n ^ 3 * C + n ^ 2 + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h : n * ((n + 1) * C + 1) + 1 ≤ 2 * n ^ 2 * C + 2 * n := by
    nlinarith [Nat.mul_le_mul_left (n * C) hn]
  calc _ ≤ (2 * n ^ 2 * C + 2 * n) * (4 * n + 6) + 3 * (n * n) + 7 * n + 3 + 1 := by gcongr
    _ ≤ _ := by nlinarith [Nat.mul_le_mul_left (n ^ 2 * C) hn, Nat.mul_le_mul_left n hn]

private theorem init_words_spec {w : ℕ} (inst : Instance) (hw : Fits w inst.wordBound) :
    InputFits w inst.encode ∧
      Fits w (inst.encode.length + 1) ∧
      (∀ j : Fin 1, inst.encode.getD j.val 0 = wordWords inst.n j) ∧
      1 ≤ inst.encode.length := by
  refine ⟨inst.inputFits_encode hw,
    hw.of_le (by rw [inst.encode_length]; unfold Instance.wordBound; nlinarith),
    ?_, by rw [inst.encode_length]; omega⟩
  rintro ⟨_ | _, hj⟩ <;> first | rfl | omega

private theorem scaled_steps_le {m C₁ mc n C : ℕ}
    (hsteps : m + 1 ≤ C₁ * (mc + 0 + 1) + 1)
    (hmc : mc ≤ (n * ((n + 1) * C + 1) + 1) * (4 * n + 6) + 3 * (n * n) + 7 * n + 2) :
    m + 1 ≤ (34 * C₁ + 1) * (n ^ 3 * C + n ^ 2 + 1) := by
  have hp := scaled_poly_bound n C
  have hmul : C₁ * (mc + 0 + 1) ≤ C₁ * (34 * (n ^ 3 * C + n ^ 2 + 1)) :=
    Nat.mul_le_mul_left C₁ (by omega)
  have hpos : 1 ≤ n ^ 3 * C + n ^ 2 + 1 := Nat.succ_pos _
  nlinarith

public section

/-- **`O(n² (C / ε + 1))` Word-RAM `ε`-auction (`ExecutesList` and `Program.ComputesListInTime`).**
There is a uniform deterministic width-blind standard-basis program (`Program .standard r`,
`¬ prog.ReadsWidth`, `prog.IsRandFree`) that, on `inst.encode` for any `inst : EpsInstance` with
`0 < inst.eps`, row cost ranges bounded by `C`, and `Fits w inst.wordBound`
(`w = O(log n + log M + log ε)`), halts within `K * (inst.n ^ 2 * (C / inst.eps + 1) + 1)`
instructions returning `inst.assignment` (`n * eps`-optimal by `sum_auctionPerm_le` and
`ε`-complementary-slack by `isEpsCompSlack_auctionPerm`; [Bertsekas1988], §1). -/
theorem exists_epsAuction_program :
    ∃ r K : ℕ, 0 < K ∧ ∃ prog : Program .standard r,
      ¬ prog.ReadsWidth ∧ prog.IsRandFree ∧
      (∀ {w C : ℕ} (inst : EpsInstance),
        0 < inst.eps →
        (∀ i j k : Fin inst.n, inst.cost (i, k) - inst.cost (i, j) ≤ (C : ℤ)) →
        Fits w inst.wordBound →
        ∃ steps, ExecutesList w prog (.init inst.encode) inst.assignment steps ∧
          steps ≤ K * (inst.n ^ 2 * (C / inst.eps + 1) + 1)) ∧
      prog.ComputesListInTime (fun _ inst => inst.encode)
        (fun inst _ => K * (inst.n ^ 2 * (inst.rowSpread / inst.eps + 1) + 1))
        (fun inst w => 0 < inst.eps ∧ Fits w inst.wordBound) EpsInstance.assignment := by
  obtain ⟨r, C₁, pc, prog₀, hnw₀, frontier, _, he⟩ :=
    epsMainProg_realizes.exists_standard_basis_init_program_state_from_words (0 : Fin 1)
  let prog := stripRand prog₀
  have hmain : ∀ {w C : ℕ} (inst : EpsInstance),
      0 < inst.eps →
      (∀ i j k : Fin inst.n, inst.cost (i, k) - inst.cost (i, j) ≤ (C : ℤ)) →
      Fits w inst.wordBound →
      ∃ steps, ExecutesList w prog (.init inst.encode) inst.assignment steps ∧
        steps ≤ (42 * C₁ + 1) * (inst.n ^ 2 * (C / inst.eps + 1) + 1) := by
    intro w C inst hε hC hw
    have hin := inst.inputFits_encode hw
    have hfit_len : Fits w (inst.encode.length + 1) :=
      hw.of_le (by rw [inst.encode_length]; unfold EpsInstance.wordBound; nlinarith)
    have hlayout : ∀ j : Fin 2, inst.encode.getD j.val 0 = pairWords (inst.n, inst.eps) j := by
      rintro ⟨_ | _ | _, hj⟩ <;> first | rfl | omega
    have hk : 2 ≤ inst.encode.length := by rw [inst.encode_length]; omega
    obtain ⟨hsafe, hv, hmc, hout, hfit_out⟩ := epsMainProg_spec inst hε hC hw
    obtain ⟨y, m, hruns₀, hhalt₀, hmem, _, hsteps⟩ :=
      he w (inst.n, inst.eps) inst.encode hlayout hk hfit_len hin hsafe hv
    rw [clientState_width w] at hmem
    simp only [clientResult_width w, wordWords] at hhalt₀
    refine ⟨m + 1, ⟨⟨pc, y⟩, m, _, runs_stripRand hruns₀, step_stripRand_of_halt hhalt₀,
      (show y.mem = _ from congrArg Memory.State.mem hmem) ▸ hout, hfit_out, rfl⟩, ?_⟩
    have hp := eps_poly_bound inst.n C inst.eps hε
    have hmul : C₁ * (memoryCost (epsMainProg (inst.n, inst.eps))
        (Memory.State.init inst.encode) + 0 + 1) ≤
        C₁ * (42 * (inst.n ^ 2 * (C / inst.eps + 1) + 1)) :=
      Nat.mul_le_mul_left C₁ (by omega)
    have hpos : 1 ≤ inst.n ^ 2 * (C / inst.eps + 1) + 1 := Nat.succ_pos _
    nlinarith
  refine ⟨r, 42 * C₁ + 1, by omega, prog, not_readsWidth_stripRand hnw₀,
    isRandFree_stripRand prog₀, @hmain, fun inst w ⟨hε, hw⟩ _ =>
      hmain inst hε inst.toInstance.sub_le_rowSpread hw⟩

/-- **`O(n³ C + n²)` Word-RAM exact `(n + 1)`-scaled integer assignment (`ExecutesList` and
`Program.ComputesListInTime`).** There is a uniform deterministic width-blind standard-basis
program (`Program .standard r`, `¬ prog.ReadsWidth`, `prog.IsRandFree`) that, on `inst.encode` for
any `inst : Instance` with row cost ranges bounded by `C` and `Fits w inst.wordBound`
(`w = O(log n + log M)`), halts within `K * (inst.n ^ 3 * C + inst.n ^ 2 + 1)` instructions
returning the exact optimal assignment `inst.assignment` (`sum_scaledAuctionPerm_le`;
[Bertsekas1988], §3). -/
theorem exists_scaledAuction_program :
    ∃ r K : ℕ, 0 < K ∧ ∃ prog : Program .standard r,
      ¬ prog.ReadsWidth ∧ prog.IsRandFree ∧
      (∀ {w C : ℕ} (inst : Instance),
        (∀ i j k : Fin inst.n, inst.cost (i, k) - inst.cost (i, j) ≤ (C : ℤ)) →
        Fits w inst.wordBound →
        ∃ steps, ExecutesList w prog (.init inst.encode) inst.assignment steps ∧
          steps ≤ K * (inst.n ^ 3 * C + inst.n ^ 2 + 1)) ∧
      prog.ComputesListInTime (fun _ inst => inst.encode)
        (fun inst _ => K * (inst.n ^ 3 * inst.rowSpread + inst.n ^ 2 + 1))
        (fun inst w => Fits w inst.wordBound) Instance.assignment := by
  obtain ⟨r, C₁, pc, prog₀, hnw₀, frontier, _, he⟩ :=
    scaledMainProg_realizes.exists_standard_basis_init_program_state_from_words (0 : Fin 1)
  let prog := stripRand prog₀
  have hmain : ∀ {w C : ℕ} (inst : Instance),
      (∀ i j k : Fin inst.n, inst.cost (i, k) - inst.cost (i, j) ≤ (C : ℤ)) →
      Fits w inst.wordBound →
      ∃ steps, ExecutesList w prog (.init inst.encode) inst.assignment steps ∧
        steps ≤ (34 * C₁ + 1) * (inst.n ^ 3 * C + inst.n ^ 2 + 1) := by
    intro w C inst hC hw
    obtain ⟨hin, hfit_len, hlayout, hk⟩ := init_words_spec inst hw
    obtain ⟨hsafe, hv_s, hmc_s, _, hws_n, _, _, _, _, hout_s, hfit_ws⟩ :=
      scaledSolveProg_spec inst hC hw
    have hv : (Memory.spec w).ValidHistory (Memory.State.init inst.encode)
        ((Memory.spec w).clientHistory (Memory.State.init inst.encode)
          (scaledMainProg inst.n)) :=
      validHistory_bind_step hv_s (validHistory_pure w _ _)
    have hmc : memoryCost (scaledMainProg inst.n) (Memory.State.init inst.encode) ≤
        (inst.n * ((inst.n + 1) * C + 1) + 1) * (4 * inst.n + 6) +
          3 * (inst.n * inst.n) + 7 * inst.n + 2 := by
      unfold scaledMainProg
      rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
      exact hmc_s.trans (by omega)
    obtain ⟨y, m, hruns₀, hhalt₀, hmem, _, hsteps⟩ :=
      he w inst.n inst.encode hlayout hk hfit_len hin hsafe hv
    rw [clientState_width w] at hmem
    simp only [clientResult_width w, wordWords] at hhalt₀
    unfold scaledMainProg at hmem hhalt₀
    rw [clientState_bind, clientState_pure] at hmem
    rw [clientResult_bind, clientResult_pure] at hhalt₀
    refine ⟨m + 1, ⟨⟨pc, y⟩, m, _, runs_stripRand hruns₀, step_stripRand_of_halt hhalt₀,
      (show y.mem = _ from congrArg Memory.State.mem hmem) ▸ hout_s, ?_, rfl⟩,
      scaled_steps_le hsteps hmc⟩
    · rw [inst.length_assignment]
      exact (hws_n ▸ hfit_ws).of_le (Nat.le_succ _)
  refine ⟨r, 34 * C₁ + 1, by omega, prog, not_readsWidth_stripRand hnw₀,
    isRandFree_stripRand prog₀, @hmain, fun inst w hw _ =>
      hmain inst inst.sub_le_rowSpread hw⟩

/-- **`O(n³ C + n²)` Word-RAM exact `(n + 1)`-scaled integer minimum assignment cost (`Executes`
and `Program.ComputesInTime`).** There is a uniform deterministic width-blind standard-basis
program (`Program .standard r`, `¬ prog.ReadsWidth`, `prog.IsRandFree`) that, on `inst.encode` for
any `inst : Instance` with row cost ranges bounded by `C` and `Fits w inst.wordBound`
(`w = O(log n + log M)`), halts within `K * (inst.n ^ 3 * C + inst.n ^ 2 + 1)` instructions
returning `inst.encodedMinCost` (`Signed.encode inst.minCost`; [Bertsekas1988], §3). -/
theorem exists_scaledMinCost_program :
    ∃ r K : ℕ, 0 < K ∧ ∃ prog : Program .standard r,
      ¬ prog.ReadsWidth ∧ prog.IsRandFree ∧
      (∀ {w C : ℕ} (inst : Instance),
        (∀ i j k : Fin inst.n, inst.cost (i, k) - inst.cost (i, j) ≤ (C : ℤ)) →
        Fits w inst.wordBound →
        ∃ steps, Executes w prog (.init inst.encode) inst.encodedMinCost steps ∧
          steps ≤ K * (inst.n ^ 3 * C + inst.n ^ 2 + 1)) ∧
      prog.ComputesInTime (fun _ inst => inst.encode)
        (fun inst _ => K * (inst.n ^ 3 * inst.rowSpread + inst.n ^ 2 + 1))
        (fun inst w => Fits w inst.wordBound) Instance.encodedMinCost := by
  obtain ⟨r, C₁, pc, prog₀, hnw₀, _, _, he⟩ :=
    scaledMinCostMainProg_realizes.exists_standard_basis_init_program_state_from_words (0 : Fin 1)
  let prog := stripRand prog₀
  have hmain : ∀ {w C : ℕ} (inst : Instance),
      (∀ i j k : Fin inst.n, inst.cost (i, k) - inst.cost (i, j) ≤ (C : ℤ)) →
      Fits w inst.wordBound →
      ∃ steps, Executes w prog (.init inst.encode) inst.encodedMinCost steps ∧
        steps ≤ (34 * C₁ + 1) * (inst.n ^ 3 * C + inst.n ^ 2 + 1) := by
    intro w C inst hC hw
    obtain ⟨hin, hfit_len, hlayout, hk⟩ := init_words_spec inst hw
    obtain ⟨hsafe_s, hv_s, hmc_s, hws_s, hws_n, hws_sc, hM_le, hM_ge, hC_s, hout_s, hfit_ws⟩ :=
      scaledSolveProg_spec inst hC hw
    obtain ⟨hsafe_sum, hv_sum, hmc_sum, hres_sum⟩ :=
      sumScaledCostProg_spec inst _ _ hws_s hws_n hws_sc hM_le hM_ge hC_s hout_s hw hfit_ws
    have hv : (Memory.spec w).ValidHistory (Memory.State.init inst.encode)
        ((Memory.spec w).clientHistory (Memory.State.init inst.encode)
          (scaledMinCostMainProg inst.n)) :=
      validHistory_bind_step hv_s hv_sum
    have hmc : memoryCost (scaledMinCostMainProg inst.n) (Memory.State.init inst.encode) ≤
        (inst.n * ((inst.n + 1) * C + 1) + 1) * (4 * inst.n + 6) +
          3 * (inst.n * inst.n) + 7 * inst.n + 2 := by
      unfold scaledMinCostMainProg
      rw [memoryCost_bind']
      exact (Nat.add_le_add hmc_s hmc_sum).trans (by omega)
    obtain ⟨y, m, hruns₀, hhalt₀, _, _, hsteps⟩ :=
      he w inst.n inst.encode hlayout hk hfit_len hin ⟨hsafe_s, hsafe_sum⟩ hv
    rw [clientResult_width w, scaledMinCostMainProg, clientResult_bind, hres_sum] at hhalt₀
    dsimp only [wordWords] at hhalt₀
    exact ⟨m + 1, ⟨⟨pc, y⟩, m, runs_stripRand hruns₀, step_stripRand_of_halt hhalt₀, rfl⟩,
      scaled_steps_le hsteps hmc⟩
  refine ⟨r, 34 * C₁ + 1, by omega, prog, not_readsWidth_stripRand hnw₀,
    isRandFree_stripRand prog₀, @hmain, fun inst w hw _ =>
      hmain inst inst.sub_le_rowSpread hw⟩

end

end Cslib.Algorithms.WordRAM.Auction
