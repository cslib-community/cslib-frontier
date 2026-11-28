/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Auction.Workspace
import CslibFrontier.Algorithms.WordRAM.Auction.BidStep
import CslibFrontier.Computability.WordRAM.Realization.FramedLoop
import CslibFrontier.Computability.WordRAM.Realization.WhileAbsorb
import CslibFrontier.Foundations.Data.Matrix.PairChunks
import CslibFrontier.Tactic.Realize
import Mathlib.Tactic.Linarith

/-!
# Workspace initialization and outer auction loop (`auctionCoreProg`)

Initializes the `owner`, `price`, and reversed unassigned-person `stack` arrays for an `n × n`
auction instance and runs `boundedWhile` over `bidStepProg` from `Auction.BidStep` until the
stack empties, matching the pure `auction` loop state in `≤ bids * (4 * n + 6) + 3 * n` memory
operations.

The initialization step (`initStep`), its `realize` certificate, and the `boundedWhile` induction
remain `private` to this module.

## Main definitions

* `Cslib.Algorithms.WordRAM.Auction.auctionCoreProg`,
  `Cslib.Algorithms.WordRAM.Auction.AuctionCoreSafe`: core auction program and safety predicate.

## Main results

* `Cslib.Algorithms.WordRAM.Auction.auctionCoreProg_realizes`,
  `Cslib.Algorithms.WordRAM.Auction.auctionCoreProg_spec`: Word-RAM realization and full-loop
  specification of `auctionCoreProg`.
-/

namespace Cslib.Algorithms.WordRAM.Auction

open Cslib.WordRAM
open Cslib.WordRAM.Realization
open Cslib.DataStructure
open Cslib.Algorithms.Lean.Assignment

/-! ### Workspace state initialization -/

private def initStep (x : AuctionWS × ℕ) : Memory.Prog ℕ := do
  let ws := x.1
  let idx := x.2
  Memory.write (ws.bOwner + idx) ws.n
  Memory.write (ws.bPrice + idx) 0
  Memory.write (ws.bStack + idx) (ws.n - (idx + 1))
  pure (idx + 1)

private abbrev InitStepSafe (w : ℕ) (x : AuctionWS × ℕ) (_ : Memory.State) : Prop :=
  let ws := x.1
  let idx := x.2
  idx + 1 ≤ ws.n ∧ Fits w (ws.bOwner + idx) ∧ Fits w (ws.bPrice + idx) ∧
    Fits w (ws.bStack + idx) ∧ Fits w (idx + 1)

private theorem initStep_realizes :
    Realizes .exact initStep (appendWords encAuctionWS wordWords) wordWords
      InitStepSafe (fun _ _ => 0) := by
  unfold initStep
  realize
  all_goals
    rcases h with ⟨_, _, _, _, _⟩
    assumption

private theorem initAuction_spec {w : ℕ} (ws : AuctionWS) {C : Fin ws.n × Fin ws.n → ℕ}
    (s₀ : Memory.State) (hws : ValidWS ws s₀)
    (hC_mem : ∀ i j : Fin ws.n, s₀.mem (ws.bC + (i.val * ws.n + j.val)) = C (i, j))
    (hfit_ws : Fits w (ws.outBase + ws.n + 1)) :
    iterationSafe initStep InitStepSafe w ws ws.n 0 s₀ ∧
      Memory.FramedTriple w s₀ (iterate initStep ws ws.n 0) (3 * ws.n)
        (Set.Ico ws.bOwner ws.outBase) fun _ t =>
          t.frontier = s₀.frontier ∧ AuctionMem ws C (auctionInit ws.n) t := by
  obtain ⟨hbO, hbP, hbS, hout, hfr⟩ := hws
  refine Memory.FramedTriple.iterate (fun k idx t => idx = k ∧ t.frontier = s₀.frontier ∧
      ∀ j < k, t.mem (ws.bOwner + j) = ws.n ∧ t.mem (ws.bPrice + j) = 0 ∧
        t.mem (ws.bStack + j) = ws.n - (j + 1))
    ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    (fun k hk idx t ⟨hidx, hsfr, hprev⟩ _ => ?_) fun _ t ⟨_, hfr', hprev⟩ hmod => ?_
  · subst idx
    refine ⟨by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> region_omega, ?_⟩
    unfold initStep
    framed_triple
    refine ⟨rfl, hsfr, fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt' | rfl
    · obtain ⟨ho, hp, hst⟩ := hprev j hlt'
      refine ⟨?_, ?_, ?_⟩ <;> simp (disch := omega) only [Function.update_of_ne, ho, hp, hst]
    · refine ⟨?_, ?_, ?_⟩ <;>
        simp (disch := omega) only [Function.update_of_ne, Function.update_self]
  · refine ⟨hfr', fun i j => ?_, fun j => (hprev j.val j.isLt).1,
      fun j => (hprev j.val j.isLt).2.1, fun k hk => ?_⟩
    · have hlt : i.val * ws.n + j.val < ws.n * ws.n := Cslib.Matrix.pairIndex_lt (i, j)
      exact (hmod.2 _ (by omega) (by region_omega)).trans (hC_mem i j)
    · simp only [auctionInit, List.length_finRange] at hk ⊢
      rw [(hprev k hk).2.2, List.getElem_finRange]
      dsimp only [Fin.cast]
      omega

/-! ### Bounded-while outer loop -/

private def auctionCutoff (ws : AuctionWS) : ℕ :=
  ws.n * (2 * ws.scale * ws.M + ws.eps) + 2

private theorem bids_le_auctionLoop {n : ℕ} (c : Fin n × Fin n → ℤ) (ε : ℤ) :
    ∀ (fuel : ℕ) (st : AuctionState n), st.bids ≤ (auctionLoop c ε fuel st).bids
  | 0, _ => le_rfl
  | m + 1, st => by
    unfold auctionLoop
    rcases hf : st.free with _ | ⟨_, _⟩
    · exact le_rfl
    · exact Nat.le_of_lt ((bids_bidStep (c := c) (ε := ε) hf).symm.trans_le
        (bids_le_auctionLoop c ε m (bidStep c ε st)))

private theorem boundedWhile_auctionLoop_spec {w W : ℕ} (ws : AuctionWS)
    {C : Fin ws.n × Fin ws.n → ℕ} (hε : 0 < ws.eps)
    (hC_le : ∀ i j : Fin ws.n, C (i, j) ≤ W)
    (fuel : ℕ) (st : AuctionState ws.n) (s : Memory.State)
    (hinv : AuctionInv (fun e => (C e : ℤ)) (ws.eps : ℤ) st)
    (hp_nn : ∀ j : Fin ws.n, 0 ≤ st.price j)
    (hws : ValidWS ws s) (ham : AuctionMem ws C st s)
    (hfit1 : Fits w 1) (hfit_ws : Fits w (ws.outBase + ws.n + 1))
    (hfit_p : Fits w (2 * W + 2 * ws.eps)) :
    let cZ : Fin ws.n × Fin ws.n → ℤ := fun e => (C e : ℤ)
    let bw := boundedWhile (fun _ (sp : ℕ) => 0 < sp) bidStepProg ws fuel st.free.length
    let st_end := auctionLoop cZ (ws.eps : ℤ) fuel st
    ((st_end.free = []) →
      whileSafe (fun _ (sp : ℕ) => 0 < sp) bidStepProg
        (fun w x s => BidStepSafe w (ws, x.2) s) w ws fuel st.free.length s) ∧
      Memory.FramedTriple w s bw ((st_end.bids - st.bids) * (4 * ws.n + 6)) Set.univ
        fun _ t => t.frontier = s.frontier ∧ AuctionMem ws C st_end t := by
  induction fuel generalizing st s with
  | zero =>
    unfold boundedWhile auctionLoop
    exact ⟨fun hfree => by simp [whileSafe, hfree], Memory.FramedTriple.pure ⟨rfl, ham⟩⟩
  | succ fuel ih =>
    rcases hs_free : st.free with _ | ⟨i₀, rest⟩
    · unfold boundedWhile auctionLoop
      simp only [hs_free, List.length_nil, lt_self_iff_false, ↓reduceIte]
      exact ⟨fun _ => by simp [whileSafe], Memory.FramedTriple.pure ⟨rfl, ham⟩⟩
    · have hpos : 0 < st.free.length := by simp [hs_free]
      obtain ⟨hsafe_step, hv_step, hmc_step, hfr_step, hres_step, ham_step⟩ :=
        bidStepProg_spec ws hs_free hε hinv hp_nn hC_le s hws ham hfit1 hfit_ws hfit_p
      let cZ : Fin ws.n × Fin ws.n → ℤ := fun e => (C e : ℤ)
      let st₁ := bidStep cZ (ws.eps : ℤ) st
      let s₁ := (Memory.spec 0).clientState s (bidStepProg (ws, st.free.length))
      have hinv₁ : AuctionInv cZ (ws.eps : ℤ) st₁ := hinv.bidStep (by positivity)
      have hp_nn₁ : ∀ j, 0 ≤ st₁.price j := price_nonneg_bidStep (by positivity) hp_nn
      have hws₁ : ValidWS ws s₁ := hws.of_frontier_eq hfr_step
      obtain ⟨hwsafe_ih, hft_ih⟩ := ih st₁ s₁ hinv₁ hp_nn₁ hws₁ ham_step
      have hbids₁ : st₁.bids = st.bids + 1 := bids_bidStep hs_free
      have hbids_mono : st₁.bids ≤ (auctionLoop cZ (ws.eps : ℤ) fuel st₁).bids :=
        bids_le_auctionLoop cZ (ws.eps : ℤ) fuel st₁
      have hloop_step : auctionLoop cZ (ws.eps : ℤ) (fuel + 1) st =
          auctionLoop cZ (ws.eps : ℤ) fuel st₁ := by
        rw [auctionLoop, hs_free]
      simp only [← hs_free]
      rw [boundedWhile, ite_eq_left hpos, hloop_step]
      refine ⟨fun hfree => ?_, ?_⟩
      · rw [whileSafe, ite_eq_left hpos, hres_step]
        exact ⟨hsafe_step, hwsafe_ih hfree⟩
      · have hsub : (auctionLoop cZ (ws.eps : ℤ) fuel st₁).bids - st.bids =
            1 + ((auctionLoop cZ (ws.eps : ℤ) fuel st₁).bids - st₁.bids) := by omega
        rw [hsub, Nat.add_mul, one_mul]
        refine Memory.FramedTriple.call_eq ((Memory.FramedTriple.of_realization hv_step hfr_step
          fun _ _ => trivial).mono hmc_step fun _ _ => id) subset_rfl ?_
        rw [hres_step]
        exact hft_ih.mono le_rfl fun _ _ h => ⟨h.1.trans hfr_step, h.2⟩

public section

/-- Initialize workspace state (`owner`, `price`, `stack`) and run the Gauss–Seidel auction loop
until all persons are assigned. -/
def auctionCoreProg (ws : AuctionWS) : Memory.Prog ℕ := do
  let _ ← iterate initStep ws ws.n 0
  boundedWhile (fun _ (sp : ℕ) => 0 < sp) bidStepProg ws (auctionCutoff ws) ws.n

/-- Word-width safety predicate for `auctionCoreProg`. -/
def AuctionCoreSafe (w : ℕ) (ws : AuctionWS) (s : Memory.State) : Prop :=
  let s₁ := (Memory.spec 0).clientState s (iterate initStep ws ws.n 0)
  let bw := boundedWhile (fun _ (sp : ℕ) => 0 < sp) bidStepProg ws (auctionCutoff ws) ws.n
  iterationSafe initStep InitStepSafe w ws ws.n 0 s ∧
    ((Memory.spec w).ValidHistory s₁ ((Memory.spec w).clientHistory s₁ bw) →
      whileSafe (fun _ (sp : ℕ) => 0 < sp) bidStepProg
        (fun w x s => BidStepSafe w (ws, x.2) s) w ws (auctionCutoff ws) ws.n s₁)

/-- `realize` certificate for `auctionCoreProg`. -/
theorem auctionCoreProg_realizes :
    Realizes .exact auctionCoreProg encAuctionWS wordWords
      AuctionCoreSafe (fun _ _ => 0) := by
  have hraw : Realizes .exact auctionCoreProg encAuctionWS wordWords AuctionCoreSafe
      (fun ws s =>
        whileWork (fun _ (sp : ℕ) => 0 < sp) bidStepProg (fun _ _ => 0) ws (auctionCutoff ws)
          ws.n ((Memory.spec 0).clientState s (iterate initStep ws ws.n 0))) := by
    unfold auctionCoreProg
    realize [initStep_realizes, bidStepProg_realizes]
    all_goals
      rcases h with ⟨_, _⟩
      assumption
  refine hraw.mono_mul 1 fun ws s => ?_
  have hw := whileWork_zero_le (fun _ (sp : ℕ) => 0 < sp) bidStepProg
    one_le_memoryCost_bidStepProg ws (auctionCutoff ws) ws.n
    ((Memory.spec 0).clientState s (iterate initStep ws ws.n 0))
  unfold auctionCoreProg
  rw [memoryCost_bind']
  omega

/-- Full specification of `auctionCoreProg`: initializes arrays and reaches the exact final state
`auction (fun e => (C e : ℤ)) ws.eps` within `bids * (4 * n + 6) + 3 * n` memory steps. -/
theorem auctionCoreProg_spec {w : ℕ} (ws : AuctionWS)
    {C : Fin ws.n × Fin ws.n → ℕ} (hε : 0 < ws.eps)
    (hC_le : ∀ i j : Fin ws.n, C (i, j) ≤ 2 * ws.scale * ws.M)
    (s₀ : Memory.State) (hws : ValidWS ws s₀)
    (hC_mem : ∀ i j : Fin ws.n, s₀.mem (ws.bC + (i.val * ws.n + j.val)) = C (i, j))
    (hfit1 : Fits w 1) (hfit_ws : Fits w (ws.outBase + ws.n + 1))
    (hfit_p : Fits w (4 * ws.scale * ws.M + 2 * ws.eps)) :
    let cZ : Fin ws.n × Fin ws.n → ℤ := fun e => (C e : ℤ)
    let s' := (Memory.spec 0).clientState s₀ (auctionCoreProg ws)
    AuctionCoreSafe w ws s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (auctionCoreProg ws)) ∧
      memoryCost (auctionCoreProg ws) s₀ ≤
        (auction cZ (ws.eps : ℤ)).bids * (4 * ws.n + 6) + 3 * ws.n ∧
      s'.frontier = s₀.frontier ∧
      AuctionMem ws C (auction cZ (ws.eps : ℤ)) s' := by
  obtain ⟨hsafe_init, hft_init⟩ := initAuction_spec ws s₀ hws hC_mem hfit_ws
  obtain ⟨-, -, -, hfr_init, ham_init⟩ := framedTriple_iff_realization.mp hft_init
  let s₁ := (Memory.spec 0).clientState s₀ (iterate initStep ws ws.n 0)
  have hws₁ : ValidWS ws s₁ := hws.of_frontier_eq hfr_init
  let W := 2 * ws.scale * ws.M
  have hfit_p' : Fits w (2 * W + 2 * ws.eps) :=
    hfit_p.of_le (le_of_eq (by dsimp only [W]; ring))
  have hlen_init : (auctionInit ws.n).free.length = ws.n := by simp [auctionInit]
  obtain ⟨hwsafe_bw, hft_bw⟩ :=
    boundedWhile_auctionLoop_spec ws hε hC_le (auctionCutoff ws) (auctionInit ws.n) s₁
      auctionInv_init (fun _ => le_rfl) hws₁ ham_init hfit1 hfit_ws hfit_p'
  let cZ : Fin ws.n × Fin ws.n → ℤ := fun e => (C e : ℤ)
  have hεZ : (0 : ℤ) < (ws.eps : ℤ) := Nat.cast_pos.mpr hε
  have hC_spread : ∀ i j k : Fin ws.n, cZ (i, k) - cZ (i, j) ≤ (W : ℤ) := fun i _ k =>
    (Int.sub_le_self _ (Nat.cast_nonneg _)).trans (Int.ofNat_le.mpr (hC_le i k))
  have hcut_free : (auctionLoop cZ (ws.eps : ℤ) (auctionCutoff ws) (auctionInit ws.n)).free = [] :=
    (auctionLoop_spec hεZ hC_spread (auctionCutoff ws) (auctionInit ws.n) auctionInv_init (by
      simp only [auctionInit, Finset.sum_const_zero, sub_zero]
      have hmul := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ ws.eps by omega)
        (by positivity : (0 : ℤ) ≤ ws.n * (W + ws.eps))
      dsimp only [auctionCutoff, W] at hmul ⊢
      push_cast at hmul ⊢
      linarith)).2
  have hloop_eq :
      auctionLoop cZ (ws.eps : ℤ) (auctionCutoff ws) (auctionInit ws.n) =
        auction cZ (ws.eps : ℤ) := by
    unfold auction
    rcases le_total (auctionCutoff ws)
        (bidBound ws.n (costSpread cZ) (ws.eps : ℤ)) with hle | hle
    · rw [← Nat.add_sub_cancel' hle, auctionLoop_add hcut_free]
    · rw [← Nat.add_sub_cancel' hle, auctionLoop_add (auction_free hεZ)]
  simp only [hlen_init] at hwsafe_bw hft_bw
  have hft : Memory.FramedTriple w s₀ (auctionCoreProg ws)
      ((auction cZ (ws.eps : ℤ)).bids * (4 * ws.n + 6) + 3 * ws.n) Set.univ
      fun _ t => t.frontier = s₀.frontier ∧ AuctionMem ws C (auction cZ (ws.eps : ℤ)) t := by
    unfold auctionCoreProg
    refine (Memory.FramedTriple.seq hft_init (Set.subset_univ _) hft_bw).mono ?_
      fun _ _ h => ⟨h.1.trans hfr_init, hloop_eq ▸ h.2⟩
    rw [hloop_eq]; dsimp only [auctionInit, Nat.sub_zero]; omega
  obtain ⟨hv, hmc, -, hfr, ham⟩ := framedTriple_iff_realization.mp hft
  exact ⟨⟨hsafe_init, fun _ => hwsafe_bw hcut_free⟩, hv, hmc, hfr, ham⟩

end

end Cslib.Algorithms.WordRAM.Auction
