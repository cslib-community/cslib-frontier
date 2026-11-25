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
import CslibFrontier.Algorithms.WordRAM.Auction.Loop
import CslibFrontier.Algorithms.WordRAM.Auction.ScanFill
import CslibFrontier.Algorithms.WordRAM.Auction.Scatter
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Tactic.Realize
import Mathlib.Tactic.Linarith

/-!
# End-to-end Word-RAM auction client drivers (`epsMainProg`, `scaledSolveProg`, `scaledMainProg`)

Composes workspace allocation, magnitude scanning (`ScanFill.scanMaxProg`), matrix shifting/scaling
(`ScanFill.fillCProg`), the core loop (`Loop.auctionCoreProg`), and output scattering
(`Scatter.scatterProg`) into the uniform memory-client entry points backing
`exists_epsAuction_program`, `exists_scaledAuction_program`, and `exists_scaledMinCost_program`.

The shared driver `solveAuctionProg` and its `SolveArgs` record remain `private` to this module.

## Main definitions

* `Cslib.Algorithms.WordRAM.Auction.pairWords`: two-word encoding for `(n, eps)`.
* `Cslib.Algorithms.WordRAM.Auction.epsMainProg`, `Cslib.Algorithms.WordRAM.Auction.EpsMainSafe`:
  unscaled `ε`-auction memory client and safety predicate.
* `Cslib.Algorithms.WordRAM.Auction.scaledSolveProg`,
  `Cslib.Algorithms.WordRAM.Auction.ScaledSolveSafe`: `(n + 1)`-scaled solver returning the full
  workspace `AuctionWS` (used by `exists_scaledAuction_program` and
  `exists_scaledMinCost_program`).

## Main results

* `Cslib.Algorithms.WordRAM.Auction.epsMainProg_realizes`,
  `Cslib.Algorithms.WordRAM.Auction.epsMainProg_spec`: realization and specification of
  `epsMainProg`.
* `Cslib.Algorithms.WordRAM.Auction.scaledSolveProg_realizes`,
  `Cslib.Algorithms.WordRAM.Auction.scaledSolveProg_spec`: realization and specification of
  `scaledSolveProg`.
-/

namespace Cslib.Algorithms.WordRAM.Auction

open Cslib.WordRAM
open Cslib.WordRAM.Realization
open Cslib.DataStructure
open Cslib.Algorithms.Lean.Assignment
open StateTransitionSpec (clientResult_bind clientState_bind clientResult_pure clientState_pure)

private theorem init_mem_cost_instance (inst : Instance) (i j : Fin inst.n) :
    (Memory.State.init inst.encode).mem (2 + (i.val * inst.n + j.val)) =
      Signed.encode (inst.cost (i, j)) :=
  Data.init_mem_flatMap_finRange (r := 0) [inst.n]
    (fun i' j' => Signed.encode (inst.cost (i', j'))) i j

private theorem init_mem_cost_eps (inst : EpsInstance) (i j : Fin inst.n) :
    (Memory.State.init inst.encode).mem (3 + (i.val * inst.n + j.val)) =
      Signed.encode (inst.cost (i, j)) :=
  Data.init_mem_flatMap_finRange (r := 0) [inst.n, inst.eps]
    (fun i' j' => Signed.encode (inst.cost (i', j'))) i j

private structure SolveArgs where
  n : ℕ
  eps : ℕ
  scale : ℕ
  matBase : ℕ

private word_enc_structure encSolveArgs : SolveArgs where
  n : wordWords, eps : wordWords, scale : wordWords, matBase : wordWords

private instance : WordEncoding SolveArgs := ⟨4, encSolveArgs⟩

private def solveAuctionProg (a : SolveArgs) : Memory.Prog AuctionWS := do
  let n := a.n
  let base ← Memory.allocDirty (n * n + n + n + n + n + 1)
  let M ← scanMaxProg ⟨a.matBase, n * n⟩
  let ws : AuctionWS :=
    { n := n
      eps := a.eps
      scale := a.scale
      M := M
      matBase := a.matBase
      bC := base
      bOwner := base + n * n
      bPrice := base + n * n + n
      bStack := base + n * n + n + n
      outBase := base + n * n + n + n + n }
  let _ ← fillCProg ws
  let _ ← auctionCoreProg ws
  let _ ← scatterProg ws
  pure ws

private abbrev SolveAuctionSafe (w : ℕ) (a : SolveArgs) (s₀ : Memory.State) : Prop :=
  let n := a.n
  let base := s₀.frontier
  let s₁ : Memory.State := ⟨s₀.mem, base + (n * n + n + n + n + n + 1)⟩
  let M := (Memory.spec 0).clientResult s₁ (scanMaxProg ⟨a.matBase, n * n⟩)
  let s₂ := (Memory.spec 0).clientState s₁ (scanMaxProg ⟨a.matBase, n * n⟩)
  let ws : AuctionWS :=
    ⟨n, a.eps, a.scale, M, a.matBase, base, base + n * n, base + n * n + n,
      base + n * n + n + n, base + n * n + n + n + n⟩
  let s₃ := (Memory.spec 0).clientState s₂ (fillCProg ws)
  let s₄ := (Memory.spec 0).clientState s₃ (auctionCoreProg ws)
  Fits w 1 ∧ Fits w (n * n) ∧
    Fits w (n * n + n + n + n + n + 1) ∧ Fits w (base + n * n + n + n + n) ∧
    ScanMaxSafe w ⟨a.matBase, n * n⟩ s₁ ∧
    FillCProgSafe w ws s₂ ∧
    AuctionCoreSafe w ws s₃ ∧
    ScatterProgSafe w ws s₄

private theorem solveAuctionProg_realizes :
    Realizes .exact solveAuctionProg encSolveArgs encAuctionWS SolveAuctionSafe
      (fun _ _ => 0) := by
  unfold solveAuctionProg
  realize [scanMaxProg_realizes, fillCProg_realizes, auctionCoreProg_realizes, scatterProg_realizes]
  all_goals
    rcases h with ⟨_, _, _, hfout, _, _, _, _⟩
    first
    | assumption
    | exact hfout.of_le (by omega)

private theorem solveAuctionProg_spec {w maxMag : ℕ} (a : SolveArgs)
    {cost : Fin a.n × Fin a.n → ℤ} {s₀ : Memory.State}
    (hε : 0 < a.eps) (hsc : 1 ≤ a.scale)
    (hs₀_fr : s₀.frontier = a.matBase + a.n * a.n)
    (hcost_mem : ∀ i j : Fin a.n,
      s₀.mem (a.matBase + (i.val * a.n + j.val)) = Signed.encode (cost (i, j)))
    (hmag : ∀ i j : Fin a.n, (cost (i, j)).natAbs ≤ maxMag)
    (hfit2 : Fits w 2)
    (hfit_fr : Fits w (a.matBase + 2 * (a.n * a.n) + 4 * a.n + 1))
    (hfit_p : Fits w (4 * a.scale * maxMag + 2 * a.eps)) :
    let ws := (Memory.spec 0).clientResult s₀ (solveAuctionProg a)
    let s' := (Memory.spec 0).clientState s₀ (solveAuctionProg a)
    let st_pure := auction (fun e => (a.scale : ℤ) * cost e) (a.eps : ℤ)
    SolveAuctionSafe w a s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (solveAuctionProg a)) ∧
      memoryCost (solveAuctionProg a) s₀ ≤
        st_pure.bids * (4 * a.n + 6) + 3 * (a.n * a.n) + 5 * a.n + 2 ∧
      ValidWS ws s' ∧
      ws.n = a.n ∧ ws.scale = a.scale ∧
      ws.M ≤ maxMag ∧
      (∀ i j : Fin a.n, (cost (i, j)).natAbs ≤ ws.M) ∧
      (∀ i j : Fin a.n,
        s'.mem (ws.bC + (i.val * a.n + j.val)) =
          a.scale * (cost (i, j) + (ws.M : ℤ)).toNat) ∧
      outputList s'.mem ws.outBase =
        (List.finRange a.n).map (fun i => (st_pure.objectOf i).val) ∧
      Fits w (ws.outBase + ws.n + 1) := by
  let base := s₀.frontier
  let s₁ : Memory.State := ⟨s₀.mem, base + (a.n * a.n + a.n + a.n + a.n + a.n + 1)⟩
  have hf1 : Fits w 1 := hfit2.of_le (by omega)
  have hf_fr1 : Fits w s₁.frontier :=
    hfit_fr.of_le (by dsimp only [s₁, base]; rw [hs₀_fr]; omega)
  have hscan := scanMaxProg_spec (s₀ := s₁) hcost_mem hmag
    (by dsimp only [s₁, base]; rw [hs₀_fr]; omega)
    hfit2 (hf_fr1.of_le (by dsimp only [s₁, base]; rw [hs₀_fr]; omega))
  obtain ⟨hsafe_scan, hv_scan, hmc_scan, hs₂_eq, hM_le, hM_ge⟩ := hscan
  let M := (Memory.spec 0).clientResult s₁ (scanMaxProg ⟨a.matBase, a.n * a.n⟩)
  let ws₀ : AuctionWS :=
    ⟨a.n, a.eps, a.scale, M, a.matBase, base, base + a.n * a.n, base + a.n * a.n + a.n,
      base + a.n * a.n + a.n + a.n, base + a.n * a.n + a.n + a.n + a.n⟩
  have hws₁ : ValidWS ws₀ s₁ :=
    ⟨rfl, rfl, rfl, rfl, by dsimp only [ws₀, s₁]; omega⟩
  have hfit_ws : Fits w (ws₀.outBase + ws₀.n + 1) :=
    hf_fr1.of_le (by dsimp only [ws₀, s₁]; omega)
  have hscM_le : a.scale * M ≤ a.scale * maxMag := Nat.mul_le_mul_left a.scale hM_le
  have hfit_val : Fits w (ws₀.scale * (2 * ws₀.M)) :=
    hfit_p.of_le <| by
      dsimp only [ws₀]
      calc a.scale * (2 * M) = 2 * (a.scale * M) := by ring
        _ ≤ 2 * (a.scale * maxMag) := Nat.mul_le_mul_left 2 hscM_le
        _ ≤ 4 * a.scale * maxMag + 2 * a.eps := by
          rw [show 4 * a.scale * maxMag = 4 * (a.scale * maxMag) by ring]; omega
  have hfit_core : Fits w (4 * ws₀.scale * ws₀.M + 2 * ws₀.eps) :=
    hfit_p.of_le <| by
      dsimp only [ws₀]
      calc 4 * a.scale * M + 2 * a.eps
          = 4 * (a.scale * M) + 2 * a.eps := by ring
        _ ≤ 4 * (a.scale * maxMag) + 2 * a.eps :=
            Nat.add_le_add_right (Nat.mul_le_mul_left 4 hscM_le) _
        _ = 4 * a.scale * maxMag + 2 * a.eps := by ring
  have hfill := fillC_spec ws₀ s₁ hsc
    (by dsimp only [ws₀, base]; rw [hs₀_fr])
    (by dsimp only [ws₀, s₁]; omega)
    hcost_mem hM_ge hfit2
    (hfit_ws.of_le (by dsimp only [ws₀]; omega))
    hfit_val
  obtain ⟨hsafe_fill, hv_fill, hmc_fill, hfr_fill, _, hC_filled⟩ := hfill
  let s₃ := (Memory.spec 0).clientState s₁ (fillCProg ws₀)
  have hws₃ : ValidWS ws₀ s₃ := hws₁.of_frontier_eq hfr_fill
  let C_work : Fin a.n × Fin a.n → ℕ := fun p => a.scale * (cost p + (M : ℤ)).toNat
  have hC_le : ∀ i j : Fin a.n, C_work (i, j) ≤ 2 * ws₀.scale * ws₀.M := fun i j => by
    have hle2M : (cost (i, j) + (M : ℤ)).toNat ≤ 2 * M := by have := hM_ge i j; omega
    dsimp only [C_work, ws₀]
    calc a.scale * (cost (i, j) + (M : ℤ)).toNat
        ≤ a.scale * (2 * M) := Nat.mul_le_mul_left _ hle2M
      _ = 2 * a.scale * M := by ring
  have hcore := auctionCoreProg_spec ws₀ hε hC_le s₃ hws₃ hC_filled hf1 hfit_ws hfit_core
  obtain ⟨hsafe_core, hv_core, hmc_core, hfr_core, ham_core⟩ := hcore
  let s₄ := (Memory.spec 0).clientState s₃ (auctionCoreProg ws₀)
  have hws₄ : ValidWS ws₀ s₄ := hws₃.of_frontier_eq hfr_core
  have hC_cast :
      (fun e => (C_work e : ℤ)) =
        fun e => (a.scale : ℤ) * cost e + (a.scale : ℤ) * (M : ℤ) := by
    funext ⟨i, j⟩
    have hsh : ((cost (i, j) + (M : ℤ)).toNat : ℤ) = cost (i, j) + (M : ℤ) := by
      have := hM_ge i j; omega
    dsimp only [C_work]
    push_cast
    rw [hsh]; ring
  have hs_eq : auction (fun e => (C_work e : ℤ)) (a.eps : ℤ) =
      auction (fun e => (a.scale : ℤ) * cost e) (a.eps : ℤ) := by
    rw [hC_cast]
    exact auction_add_const (fun e => (a.scale : ℤ) * cost e)
      ((a.scale : ℤ) * (M : ℤ)) (Nat.cast_pos.mpr hε)
  have hinv_fin : AuctionInv (fun e => (C_work e : ℤ)) (ws₀.eps : ℤ)
      (auction (fun e => (C_work e : ℤ)) (ws₀.eps : ℤ)) :=
    auctionInv_auction (Nat.cast_pos.mpr hε)
  have hfree_fin : (auction (fun e => (C_work e : ℤ)) (ws₀.eps : ℤ)).free = [] :=
    auction_free (Nat.cast_pos.mpr hε)
  have hscat := scatterProg_spec ws₀ hinv_fin hfree_fin s₄ hws₄ ham_core hf1 hfit_ws
  obtain ⟨hsafe_scat, hv_scat, hmc_scat, hfr_scat, _, hC_scat, hout_scat⟩ := hscat
  dsimp only [ws₀] at hmc_core hout_scat
  rw [hs_eq] at hmc_core hout_scat
  have hsafe_solve : SolveAuctionSafe w a s₀ := by
    unfold SolveAuctionSafe
    dsimp only
    rw [hs₂_eq]
    exact ⟨hf1, hf_fr1.of_le (by dsimp only [s₁, base]; omega),
      hf_fr1.of_le (by dsimp only [s₁, base]; omega),
      hfit_ws.of_le (by dsimp only [ws₀]; omega),
      hsafe_scan, hsafe_fill, hsafe_core, hsafe_scat⟩
  have hres_solve : (Memory.spec 0).clientResult s₀ (solveAuctionProg a) = ws₀ := by
    unfold solveAuctionProg
    dsimp only
    rw [clientResult_bind, clientResult_allocDirty, clientState_allocDirty]
    change (Memory.spec 0).clientResult s₁ (scanMaxProg ⟨a.matBase, a.n * a.n⟩ >>= _) = _
    rw [clientResult_bind, hs₂_eq, clientResult_bind, clientResult_bind, clientResult_bind,
      clientResult_pure]
  have hst_solve : (Memory.spec 0).clientState s₀ (solveAuctionProg a) =
      (Memory.spec 0).clientState s₄ (scatterProg ws₀) := by
    unfold solveAuctionProg
    dsimp only
    rw [clientState_bind, clientResult_allocDirty, clientState_allocDirty]
    change (Memory.spec 0).clientState s₁ (scanMaxProg ⟨a.matBase, a.n * a.n⟩ >>= _) = _
    rw [clientState_bind, hs₂_eq, clientState_bind, clientState_bind, clientState_bind,
      clientState_pure]
  refine ⟨hsafe_solve, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold solveAuctionProg
    dsimp only
    refine validHistory_allocDirty_bind hf_fr1 ?_
    refine validHistory_bind_step hv_scan ?_
    rw [hs₂_eq]
    exact validHistory_bind_step hv_fill
      (validHistory_bind_step hv_core
        (validHistory_bind_step hv_scat (validHistory_pure w _ _)))
  · unfold solveAuctionProg
    dsimp only
    rw [memoryCost_bind', memoryCost_allocDirty, clientResult_allocDirty, clientState_allocDirty]
    change 1 + memoryCost (scanMaxProg ⟨a.matBase, a.n * a.n⟩ >>= _) s₁ ≤ _
    rw [memoryCost_bind', hs₂_eq, memoryCost_bind', memoryCost_bind', memoryCost_bind',
      memoryCost_pure]
    dsimp only [ws₀, M, base, s₃, s₄] at hmc_scan hmc_fill hmc_core hmc_scat ⊢
    omega
  · rw [hres_solve, hst_solve]; exact hws₄.of_frontier_eq hfr_scat
  · rw [hres_solve]
  · rw [hres_solve]
  · rw [hres_solve]; exact hM_le
  · rw [hres_solve]; exact hM_ge
  · rw [hres_solve, hst_solve]; exact hC_scat
  · rw [hres_solve, hst_solve]; exact hout_scat
  · rw [hres_solve]; exact hfit_ws

public section

/-- Two-word encoding for a pair of natural numbers `(n, eps)`. -/
abbrev pairWords : (ℕ × ℕ) ↪ (Fin 2 → ℕ) := appendWords wordWords wordWords

/-- Top-level unscaled `ε`-auction memory client returning the output list base address. -/
def epsMainProg (ne : ℕ × ℕ) : Memory.Prog ℕ := do
  let ws ← solveAuctionProg ⟨ne.1, ne.2, 1, 3⟩
  pure ws.outBase

/-- Word-width safety predicate for `epsMainProg`. -/
def EpsMainSafe (w : ℕ) (ne : ℕ × ℕ) (s₀ : Memory.State) : Prop :=
  Fits w 1 ∧ Fits w 3 ∧ SolveAuctionSafe w ⟨ne.1, ne.2, 1, 3⟩ s₀

/-- `realize` certificate for `epsMainProg`. -/
theorem epsMainProg_realizes :
    Realizes .exact epsMainProg pairWords wordWords EpsMainSafe (fun _ _ => 0) := by
  unfold epsMainProg
  realize [solveAuctionProg_realizes]
  all_goals
    rcases h with ⟨_, _, _⟩
    assumption

/-- Specification of `epsMainProg`: writes `inst.assignment` to output memory within the
pseudo-polynomial step bound. -/
theorem epsMainProg_spec {w C : ℕ} (inst : EpsInstance) (hε : 0 < inst.eps)
    (hC : ∀ i j k : Fin inst.n, inst.cost (i, k) - inst.cost (i, j) ≤ (C : ℤ))
    (hw : Fits w inst.wordBound) :
    let s₀ := Memory.State.init inst.encode
    let d := (inst.n, inst.eps)
    let outAddr := (Memory.spec 0).clientResult s₀ (epsMainProg d)
    let s' := (Memory.spec 0).clientState s₀ (epsMainProg d)
    EpsMainSafe w d s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (epsMainProg d)) ∧
      memoryCost (epsMainProg d) s₀ ≤
        (inst.n * (C + inst.eps) / inst.eps + 1) * (4 * inst.n + 6) +
          3 * (inst.n * inst.n) + 5 * inst.n + 2 ∧
      outputList s'.mem outAddr = inst.assignment ∧
      Fits w (outAddr + inst.assignment.length) := by
  let a : SolveArgs := ⟨inst.n, inst.eps, 1, 3⟩
  have hf1 : Fits w 1 := hw.of_le (by unfold EpsInstance.wordBound; nlinarith)
  have hf3 : Fits w 3 := hw.of_le (by unfold EpsInstance.wordBound; nlinarith)
  have hsolve := solveAuctionProg_spec (w := w) (maxMag := inst.maxMag) a
    (s₀ := Memory.State.init inst.encode) hε (Nat.le_refl 1)
    (by change inst.encode.length + 1 = _; dsimp only [a]; rw [inst.encode_length]; omega)
    (init_mem_cost_eps inst) inst.toInstance.natAbs_cost_le_maxMag
    (hw.of_le (by unfold EpsInstance.wordBound; nlinarith))
    (hw.of_le (by dsimp only [a]; unfold EpsInstance.wordBound; nlinarith))
    (hw.of_le (by dsimp only [a, EpsInstance.maxMag]; unfold EpsInstance.wordBound; nlinarith))
  obtain ⟨hsafe_s, hv_s, hmc_s, _, hws_n, _, _, _, _, hout_s, hfit_ws⟩ := hsolve
  have hcost_one : (fun e => ((1 : ℕ) : ℤ) * inst.cost e) = inst.cost := by
    funext e; simp
  dsimp only [a] at hsafe_s hv_s hmc_s hws_n hout_s hfit_ws
  rw [hcost_one] at hmc_s hout_s
  have hbids_le : (auction inst.cost (inst.eps : ℤ)).bids ≤
      inst.n * (C + inst.eps) / inst.eps + 1 := by
    have hb_raw := bids_auction_le (c := inst.cost) (Nat.cast_pos.mpr hε) hC
    simpa only [bidBound, ← Nat.cast_add, Int.toNat_natCast] using hb_raw
  have hmul_le :
      (auction inst.cost (inst.eps : ℤ)).bids * (4 * inst.n + 6) ≤
        (inst.n * (C + inst.eps) / inst.eps + 1) * (4 * inst.n + 6) :=
    Nat.mul_le_mul_right _ hbids_le
  unfold epsMainProg
  dsimp only
  refine ⟨⟨hf1, hf3, hsafe_s⟩, validHistory_bind_step hv_s (validHistory_pure w _ _),
    ?_, ?_, ?_⟩
  · rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
    omega
  · rw [clientState_bind, clientState_pure, clientResult_bind, clientResult_pure]
    exact hout_s
  · rw [clientResult_bind, clientResult_pure, inst.length_assignment]
    rw [hws_n] at hfit_ws
    exact hfit_ws.of_le (Nat.le_succ _)

/-- Exact `(n + 1)`-scaled auction solver returning the workspace descriptor `AuctionWS`. -/
def scaledSolveProg (n : ℕ) : Memory.Prog AuctionWS :=
  solveAuctionProg ⟨n, 1, n + 1, 2⟩

/-- Word-width safety predicate for `scaledSolveProg` and `scaledMainProg`. -/
def ScaledSolveSafe (w n : ℕ) (s₀ : Memory.State) : Prop :=
  Fits w 1 ∧ Fits w (n + 1) ∧ Fits w 2 ∧ SolveAuctionSafe w ⟨n, 1, n + 1, 2⟩ s₀

/-- `realize` certificate for `scaledSolveProg`. -/
theorem scaledSolveProg_realizes :
    Realizes .exact scaledSolveProg wordWords encAuctionWS ScaledSolveSafe (fun _ _ => 0) := by
  unfold scaledSolveProg
  realize [solveAuctionProg_realizes]
  all_goals
    rcases h with ⟨_, _, _, _⟩
    assumption

/-- Specification of `scaledSolveProg`: returns a workspace storing the scaled shifted costs and
the scattered optimal assignment `inst.assignment`. -/
theorem scaledSolveProg_spec {w C : ℕ} (inst : Instance)
    (hC : ∀ i j k : Fin inst.n, inst.cost (i, k) - inst.cost (i, j) ≤ (C : ℤ))
    (hw : Fits w inst.wordBound) :
    let s₀ := Memory.State.init inst.encode
    let ws := (Memory.spec 0).clientResult s₀ (scaledSolveProg inst.n)
    let s' := (Memory.spec 0).clientState s₀ (scaledSolveProg inst.n)
    ScaledSolveSafe w inst.n s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (scaledSolveProg inst.n)) ∧
      memoryCost (scaledSolveProg inst.n) s₀ ≤
        (inst.n * ((inst.n + 1) * C + 1) + 1) * (4 * inst.n + 6) +
          3 * (inst.n * inst.n) + 5 * inst.n + 2 ∧
      ValidWS ws s' ∧
      ws.n = inst.n ∧ ws.scale = inst.n + 1 ∧
      ws.M ≤ inst.maxMag ∧
      (∀ i j : Fin inst.n, (inst.cost (i, j)).natAbs ≤ ws.M) ∧
      (∀ i j : Fin inst.n,
        s'.mem (ws.bC + (i.val * inst.n + j.val)) =
          (inst.n + 1) * (inst.cost (i, j) + (ws.M : ℤ)).toNat) ∧
      outputList s'.mem ws.outBase = inst.assignment ∧
      Fits w (ws.outBase + ws.n + 1) := by
  let a : SolveArgs := ⟨inst.n, 1, inst.n + 1, 2⟩
  have hf1 : Fits w 1 := hw.of_le (by unfold Instance.wordBound; nlinarith)
  have hfn1 : Fits w (inst.n + 1) := hw.of_le (by unfold Instance.wordBound; nlinarith)
  have hf2 : Fits w 2 := hw.of_le (by unfold Instance.wordBound; nlinarith)
  have hsolve := solveAuctionProg_spec (w := w) (maxMag := inst.maxMag) a
    (s₀ := Memory.State.init inst.encode) Nat.one_pos (Nat.le_add_left 1 inst.n)
    (by change inst.encode.length + 1 = _; dsimp only [a]; rw [inst.encode_length]; omega)
    (init_mem_cost_instance inst) inst.natAbs_cost_le_maxMag hf2
    (hw.of_le (by dsimp only [a]; unfold Instance.wordBound; nlinarith))
    (hw.of_le (by dsimp only [a]; unfold Instance.wordBound; nlinarith))
  obtain ⟨hsafe_s, hv_s, hmc_s, hws_s, hws_n, hws_sc, hM_le, hM_ge, hC_s, hout_s, hfit_ws⟩ :=
    hsolve
  have hsc_eq :
      auction (fun e => ((inst.n + 1 : ℕ) : ℤ) * inst.cost e) ((1 : ℕ) : ℤ) =
        scaledAuction inst.cost := by
    unfold scaledAuction; push_cast; rfl
  dsimp only [a] at hsafe_s hv_s hmc_s hws_s hws_n hws_sc hM_le hM_ge hC_s hout_s hfit_ws
  rw [hsc_eq] at hmc_s hout_s
  have hbids_le : (scaledAuction inst.cost).bids ≤
      inst.n * ((inst.n + 1) * C + 1) + 1 := by
    have hb_raw := bids_scaledAuction_le (c := inst.cost) hC
    have hcast : (((inst.n : ℤ) + 1) * (C : ℤ) + 1).toNat = (inst.n + 1) * C + 1 := by
      exact_mod_cast Int.toNat_natCast ((inst.n + 1) * C + 1)
    rwa [hcast] at hb_raw
  have hmul_le :
      (scaledAuction inst.cost).bids * (4 * inst.n + 6) ≤
        (inst.n * ((inst.n + 1) * C + 1) + 1) * (4 * inst.n + 6) :=
    Nat.mul_le_mul_right _ hbids_le
  exact ⟨⟨hf1, hfn1, hf2, hsafe_s⟩, hv_s, by unfold scaledSolveProg; omega,
    hws_s, hws_n, hws_sc, hM_le, hM_ge, hC_s, hout_s, hfit_ws⟩

end

end Cslib.Algorithms.WordRAM.Auction
