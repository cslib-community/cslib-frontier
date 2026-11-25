/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Auction.Workspace
import CslibFrontier.Algorithms.WordRAM.Auction.RowScan
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.Foundations.Data.Matrix.PairChunks
import CslibFrontier.Tactic.Realize

/-!
# Single Gauss–Seidel bid step for Word-RAM auction

Implements and verifies `bidStepProg`, executing one bid iteration of Bertsekas's auction
algorithm (`bidStep`) in at most `4 * n + 6` memory operations: popping an unassigned person from
`stack`, calling `findBestProg` and `findSecondProg` from `Auction.RowScan`, updating `price` and
`owner`, and pushing an evicted previous owner back onto `stack`.

## Main definitions

* `Cslib.Algorithms.WordRAM.Auction.bidStepProg`,
  `Cslib.Algorithms.WordRAM.Auction.BidStepSafe`: single-bid program and safety predicate.

## Main results

* `Cslib.Algorithms.WordRAM.Auction.bidStepProg_realizes`,
  `Cslib.Algorithms.WordRAM.Auction.one_le_memoryCost_bidStepProg`,
  `Cslib.Algorithms.WordRAM.Auction.bidStepProg_spec`: Word-RAM realization, positive memory
  cost, and single-step simulation against `bidStep`.
-/

namespace Cslib.Algorithms.WordRAM.Auction

open Cslib.WordRAM
open Cslib.WordRAM.Realization
open Cslib.DataStructure
open Cslib.Algorithms.Lean.Assignment
open StateTransitionSpec (clientResult_bind clientState_bind)

private def computeNewP (ws : AuctionWS) (rowBase bestJ : ℕ) (sec : SecondState) :
    Memory.Prog ℕ :=
  if sec.hasSecond = 0 then do
    let pj ← Memory.read (ws.bPrice + bestJ)
    pure (pj + ws.eps)
  else do
    let cij ← Memory.read (rowBase + bestJ)
    pure (sec.secondVal - cij + ws.eps)

public section

/-- Perform one Gauss–Seidel auction bid on top of the unassigned-person stack `stack[0..sp)`. -/
def bidStepProg (x : AuctionWS × ℕ) : Memory.Prog ℕ := do
  let ws := x.1
  let sp := x.2
  let curI ← Memory.read (ws.bStack + (sp - 1))
  let rowBase := ws.bC + curI * ws.n
  let best ← findBestProg ⟨ws.n, rowBase, ws.bPrice⟩
  let sec ← findSecondProg ⟨ws.n, rowBase, ws.bPrice, best.bestJ⟩
  let newP ← computeNewP ws rowBase best.bestJ sec
  Memory.write (ws.bPrice + best.bestJ) newP
  let oldOwner ← Memory.read (ws.bOwner + best.bestJ)
  Memory.write (ws.bOwner + best.bestJ) curI
  if oldOwner = ws.n then
    pure (sp - 1)
  else do
    Memory.write (ws.bStack + (sp - 1)) oldOwner
    pure sp

/-- Word-width safety predicate for `bidStepProg`. -/
def BidStepSafe (w : ℕ) (x : AuctionWS × ℕ) (s : Memory.State) : Prop :=
  let ws := x.1
  let sp := x.2
  let curI := s.mem (ws.bStack + (sp - 1))
  let rowBase := ws.bC + curI * ws.n
  let dBest : ScanRowArgs := ⟨ws.n, rowBase, ws.bPrice⟩
  let best := (Memory.spec 0).clientResult s (findBestProg dBest)
  let s₁ := (Memory.spec 0).clientState s (findBestProg dBest)
  let dSec : ScanSecondArgs := ⟨ws.n, rowBase, ws.bPrice, best.bestJ⟩
  let sec := (Memory.spec 0).clientResult s₁ (findSecondProg dSec)
  let s₂ := (Memory.spec 0).clientState s₁ (findSecondProg dSec)
  1 ≤ sp ∧ Fits w 1 ∧ Fits w (ws.bStack + (sp - 1)) ∧ Fits w (curI * ws.n) ∧
    Fits w rowBase ∧
    FindBestSafe w dBest s ∧
    FindSecondSafe w dSec s₁ ∧
    Fits w (ws.bPrice + best.bestJ) ∧ Fits w (ws.bOwner + best.bestJ) ∧
    (sec.hasSecond = 0 → Fits w (s₂.mem (ws.bPrice + best.bestJ) + ws.eps)) ∧
    (sec.hasSecond ≠ 0 →
      Fits w (rowBase + best.bestJ) ∧
        s₂.mem (rowBase + best.bestJ) ≤ sec.secondVal ∧
        Fits w (sec.secondVal - s₂.mem (rowBase + best.bestJ) + ws.eps))

/-- Every execution of `bidStepProg` performs at least one memory read (popping `curI` from
`stack`), absorbing the outer `boundedWhile` control overhead via `Realizes.while₀`. -/
theorem one_le_memoryCost_bidStepProg (x : AuctionWS × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (bidStepProg x) s := by
  unfold bidStepProg
  rw [memoryCost_bind', memoryCost_read]
  omega

/-- `realize` certificate for `bidStepProg`. -/
theorem bidStepProg_realizes :
    Realizes .exact bidStepProg (appendWords encAuctionWS wordWords) wordWords
      BidStepSafe (fun _ _ => 0) := by
  unfold bidStepProg computeNewP
  realize [findBestProg_realizes, findSecondProg_realizes]
  all_goals
    rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _⟩
    tauto

/-- Single-step simulation of `bidStepProg` against `bidStep`: maintains `AuctionMem`, keeps
`frontier` unchanged, returns `st'.free.length`, and uses at most `4 * ws.n + 6` memory ops. -/
theorem bidStepProg_spec {w W : ℕ} (ws : AuctionWS) {C : Fin ws.n × Fin ws.n → ℕ}
    {st : AuctionState ws.n} {i₀ : Fin ws.n} {rest : List (Fin ws.n)}
    (hs_free : st.free = i₀ :: rest)
    (hε : 0 < ws.eps)
    (hinv : AuctionInv (fun e => (C e : ℤ)) (ws.eps : ℤ) st)
    (hp_nn : ∀ j : Fin ws.n, 0 ≤ st.price j)
    (hC_le : ∀ i j : Fin ws.n, C (i, j) ≤ W)
    (s₀ : Memory.State) (hws : ValidWS ws s₀) (ham : AuctionMem ws C st s₀)
    (hfit1 : Fits w 1) (hfit_ws : Fits w (ws.outBase + ws.n + 1))
    (hfit_p : Fits w (2 * W + 2 * ws.eps)) :
    let sp := st.free.length
    let st' := bidStep (fun e => (C e : ℤ)) (ws.eps : ℤ) st
    let s' := (Memory.spec 0).clientState s₀ (bidStepProg (ws, sp))
    BidStepSafe w (ws, sp) s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (bidStepProg (ws, sp))) ∧
      memoryCost (bidStepProg (ws, sp)) s₀ ≤ 4 * ws.n + 6 ∧
      s'.frontier = s₀.frontier ∧
      (Memory.spec 0).clientResult s₀ (bidStepProg (ws, sp)) = st'.free.length ∧
      AuctionMem ws C st' s' := by
  obtain ⟨hbO, hbP, hbS, hout, hfr⟩ := hws
  let cZ : Fin ws.n × Fin ws.n → ℤ := fun e => (C e : ℤ)
  have hC_spread : ∀ i j k : Fin ws.n, cZ (i, k) - cZ (i, j) ≤ (W : ℤ) := fun i j k => by
    have := hC_le i k
    dsimp only [cZ]; omega
  have hp_le : ∀ j : Fin ws.n, st.price j ≤ (W + ws.eps : ℤ) := fun j =>
    hinv.price_le (by simp [hs_free]) hC_spread (by positivity) j
  have hlen_le : st.free.length ≤ ws.n := by
    have := hinv.free_nodup.length_le_card
    rwa [Fintype.card_fin] at this
  have hsp_eq : st.free.length = rest.length + 1 := by simp [hs_free]
  have hcurI : s₀.mem (ws.bStack + (st.free.length - 1)) = i₀.val := by
    have h := ham.hStack (st.free.length - 1) (by omega)
    simpa [hs_free, Nat.sub_self] using h
  have hbest := findBest_spec ws s₀ ⟨hbO, hbP, hbS, hout, hfr⟩ ham hC_le hp_nn hp_le i₀
    hfit1 hfit_ws (hfit_p.of_le (by omega))
  obtain ⟨hsafe_b, hv_b, hmc_b, hs_b, j₀, hbo, hj₀_min, hbj, hbv⟩ := hbest
  have hsec := findSecond_spec ws s₀ ⟨hbO, hbP, hbS, hout, hfr⟩ ham hC_le hp_nn hp_le i₀ j₀
    hfit1 hfit_ws (hfit_p.of_le (by omega))
  obtain ⟨hsafe_s, hv_s, hmc_s, hs_s, hsec_spec⟩ := hsec
  let rowBase := ws.bC + i₀.val * ws.n
  let dBest : ScanRowArgs := ⟨ws.n, rowBase, ws.bPrice⟩
  let best := (Memory.spec 0).clientResult s₀ (findBestProg dBest)
  have hbj' : best.bestJ = j₀.val := hbj
  let dSec : ScanSecondArgs := ⟨ws.n, rowBase, ws.bPrice, j₀.val⟩
  let sec := (Memory.spec 0).clientResult s₀ (findSecondProg dSec)
  change (match secondBest cZ st.price i₀ j₀ with
    | none => sec.hasSecond = 0
    | some wVal =>
      sec.hasSecond = 1 ∧ (sec.secondVal : ℤ) = wVal ∧ sec.secondVal ≤ 2 * W + ws.eps) at hsec_spec
  have hmul_ij : i₀.val * ws.n + j₀.val < ws.n * ws.n := Cslib.Matrix.pairIndex_lt (i₀, j₀)
  have hmul_i : i₀.val * ws.n < ws.n * ws.n := by have := j₀.isLt; omega
  let newPZ := bidPrice cZ (ws.eps : ℤ) st.price i₀ j₀
  have hnewP_nn : 0 ≤ newPZ := by
    have := le_bidPrice (c := cZ) (ε := (ws.eps : ℤ)) hj₀_min
    have := hp_nn j₀
    dsimp only [newPZ]
    omega
  let pBranch : Memory.Prog ℕ := computeNewP ws rowBase j₀.val sec
  have hpBranch :
      (sec.hasSecond = 0 → Fits w (s₀.mem (ws.bPrice + j₀.val) + ws.eps)) ∧
      (sec.hasSecond ≠ 0 →
        Fits w (rowBase + j₀.val) ∧
          s₀.mem (rowBase + j₀.val) ≤ sec.secondVal ∧
          Fits w (sec.secondVal - s₀.mem (rowBase + j₀.val) + ws.eps)) ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ pBranch) ∧
      memoryCost pBranch s₀ ≤ 1 ∧
      (Memory.spec 0).clientState s₀ pBranch = s₀ ∧
      (Memory.spec 0).clientResult s₀ pBranch = newPZ.toNat ∧
      Fits w newPZ.toNat := by
    cases hsb : secondBest cZ st.price i₀ j₀ with
    | none =>
      rw [hsb] at hsec_spec
      have hhs0 : sec.hasSecond = 0 := hsec_spec
      have hpj_mem : s₀.mem (ws.bPrice + j₀.val) = (st.price j₀).toNat := ham.hPrice j₀
      have hnp_eq : s₀.mem (ws.bPrice + j₀.val) + ws.eps = newPZ.toNat := by
        rw [hpj_mem]; have := hp_nn j₀
        dsimp only [newPZ, bidPrice]; rw [hsb]; dsimp only; omega
      have hnp_fit : Fits w (s₀.mem (ws.bPrice + j₀.val) + ws.eps) := by
        rw [hpj_mem]; have := hp_nn j₀; have := hp_le j₀
        exact hfit_p.of_le (by omega)
      refine ⟨fun _ => hnp_fit, fun hne => absurd hhs0 hne, ?_⟩
      simp only [pBranch, computeNewP, hhs0, ↓reduceIte]
      exact ⟨validHistory_read_bind (by omega) (validHistory_pure w _ _),
        memoryCost_read_bind_le fun _ _ => Nat.le_refl 0, rfl, hnp_eq, hnp_eq ▸ hnp_fit⟩
    | some wVal =>
      rw [hsb] at hsec_spec
      obtain ⟨hhs1, hsv_z, hsv_le⟩ := hsec_spec
      have hhs_ne : sec.hasSecond ≠ 0 := by omega
      have hcj_mem : s₀.mem (rowBase + j₀.val) = C (i₀, j₀) := by
        dsimp only [rowBase]; rw [Nat.add_assoc]; exact ham.hC i₀ j₀
      have hw_ge_rc : redCost cZ st.price i₀ j₀ ≤ wVal := by
        rw [secondBest, List.min?_eq_some_iff] at hsb
        obtain ⟨hmem_w, _⟩ := hsb
        obtain ⟨k_w, _, rfl⟩ := List.mem_map.mp hmem_w
        exact hj₀_min k_w
      have hcj_le : s₀.mem (rowBase + j₀.val) ≤ sec.secondVal := by
        rw [hcj_mem]; have := hp_nn j₀
        simp only [redCost, cZ] at hw_ge_rc
        omega
      have hnp_eq : sec.secondVal - s₀.mem (rowBase + j₀.val) + ws.eps = newPZ.toNat := by
        rw [hcj_mem]; dsimp only [newPZ, bidPrice, cZ] at hnewP_nn ⊢
        rw [hsb] at hnewP_nn ⊢; dsimp only at hnewP_nn ⊢; omega
      have hnp_fit : Fits w (sec.secondVal - s₀.mem (rowBase + j₀.val) + ws.eps) :=
        hfit_p.of_le (by omega)
      have hfrb_j : Fits w (rowBase + j₀.val) :=
        hfit_ws.of_le (by dsimp only [rowBase]; omega)
      refine ⟨fun h0 => absurd h0 hhs_ne, fun _ => ⟨hfrb_j, hcj_le, hnp_fit⟩, ?_⟩
      simp only [pBranch, computeNewP, hhs_ne, ↓reduceIte]
      exact ⟨validHistory_read_bind (by dsimp only [rowBase]; omega) (validHistory_pure w _ _),
        memoryCost_read_bind_le fun _ _ => Nat.le_refl 0, rfl, hnp_eq, hnp_eq ▸ hnp_fit⟩
  obtain ⟨hbr_pos, hbr_neg, hv_p, hmc_p, hs_p, hres_p, hfit_np⟩ := hpBranch
  have hsafe_all : BidStepSafe w (ws, st.free.length) s₀ := by
    unfold BidStepSafe
    dsimp only
    rw [hcurI, hs_b, hbj, hs_s]
    exact ⟨by omega, hfit1, hfit_ws.of_le (by omega),
      hfit_ws.of_le (by omega), hfit_ws.of_le (by omega),
      hsafe_b, hsafe_s, hfit_ws.of_le (by omega), hfit_ws.of_le (by omega),
      hbr_pos, hbr_neg⟩
  have hst'_eq : bidStep cZ (ws.eps : ℤ) st =
      { owner := Function.update st.owner j₀ (some i₀)
        price := Function.update st.price j₀ newPZ
        free := (st.owner j₀).toList ++ rest
        bids := st.bids + 1 } := by
    simp only [bidStep, hs_free, cZ, hbo, newPZ]
  have hold_mem : s₀.mem (ws.bOwner + j₀.val) = (st.owner j₀).elim ws.n Fin.val :=
    ham.hOwner j₀
  let s_mid : Memory.State :=
    ⟨Function.update (Function.update s₀.mem (ws.bPrice + j₀.val) newPZ.toNat)
      (ws.bOwner + j₀.val) i₀.val, s₀.frontier⟩
  have hold_s_mid : (Function.update s₀.mem (ws.bPrice + j₀.val) newPZ.toNat)
      (ws.bOwner + j₀.val) = (st.owner j₀).elim ws.n Fin.val := by
    rw [Function.update_of_ne (by omega)]
    exact hold_mem
  have hrun_state : (Memory.spec 0).clientState s₀ (bidStepProg (ws, st.free.length)) =
      if (st.owner j₀).elim ws.n Fin.val = ws.n then
        s_mid
      else
        ⟨Function.update s_mid.mem (ws.bStack + (st.free.length - 1))
          ((st.owner j₀).elim ws.n Fin.val), s₀.frontier⟩ := by
    unfold bidStepProg
    dsimp only
    rw [clientState_bind_read, hcurI, clientState_bind, hs_b, hbj, clientState_bind, hs_s]
    change (Memory.spec 0).clientState s₀ (pBranch >>= _) = _
    rw [clientState_bind, hs_p, hres_p, clientState_bind_write, clientState_bind_read]
    simp only [hold_s_mid]
    rw [clientState_bind_write]
    split_ifs <;> rfl
  have hrun_res : (Memory.spec 0).clientResult s₀ (bidStepProg (ws, st.free.length)) =
      if (st.owner j₀).elim ws.n Fin.val = ws.n then
        st.free.length - 1
      else
        st.free.length := by
    unfold bidStepProg
    dsimp only
    rw [clientResult_bind_read, hcurI, clientResult_bind, hs_b, hbj, clientResult_bind, hs_s]
    change (Memory.spec 0).clientResult s₀ (pBranch >>= _) = _
    rw [clientResult_bind, hs_p, hres_p, clientResult_bind_write, clientResult_bind_read]
    simp only [hold_s_mid]
    rw [clientResult_bind_write]
    split_ifs <;> rfl
  refine ⟨hsafe_all, ?_, ?_, ?_, ?_, ?_⟩
  · -- ValidHistory
    unfold bidStepProg
    dsimp only
    refine validHistory_read_bind (by omega) ?_
    rw [hcurI]
    refine validHistory_bind_step hv_b ?_
    rw [hs_b, hbj]
    refine validHistory_bind_step hv_s ?_
    rw [hs_s]
    change (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (pBranch >>= _))
    refine validHistory_bind_step hv_p ?_
    rw [hs_p, hres_p]
    refine validHistory_write_bind (by omega) hfit_np ?_
    refine validHistory_read_bind (by dsimp only; omega) ?_
    dsimp only
    simp only [hold_s_mid]
    refine validHistory_write_bind (by dsimp only; omega) (hfit_ws.of_le (by omega)) ?_
    refine validHistory_ite (fun _ => validHistory_pure w _ _) (fun hne => ?_)
    have hold_lt : (st.owner j₀).elim ws.n Fin.val < ws.n := by
      cases ho : st.owner j₀ with
      | none => simp [ho] at hne
      | some p => exact p.isLt
    exact validHistory_write_bind (by dsimp only; omega) (hfit_ws.of_le (by omega))
      (validHistory_pure w _ _)
  · -- memoryCost ≤ 4 * ws.n + 6
    unfold bidStepProg
    dsimp only
    rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read, hcurI,
      memoryCost_bind', hs_b, hbj, memoryCost_bind', hs_s]
    change 1 + (_ + (_ + memoryCost (pBranch >>= _) s₀)) ≤ _
    rw [memoryCost_bind', hs_p, hres_p]
    have htail_mc : memoryCost
        (Memory.write (ws.bPrice + j₀.val) newPZ.toNat >>= fun _ =>
          Memory.read (ws.bOwner + j₀.val) >>= fun oldOwner =>
            Memory.write (ws.bOwner + j₀.val) i₀.val >>= fun _ =>
              if oldOwner = ws.n then pure (st.free.length - 1)
              else Memory.write (ws.bStack + (st.free.length - 1)) oldOwner >>=
                fun _ => pure st.free.length) s₀ ≤ 4 :=
      memoryCost_write_bind_le fun _ _ =>
        memoryCost_read_bind_le fun _ _ =>
          memoryCost_write_bind_le fun _ _ =>
            memoryCost_ite_le (Nat.zero_le 1)
              (memoryCost_write_bind_le fun _ _ => Nat.le_refl 0)
    omega
  · -- frontier unchanged
    rw [hrun_state]
    split_ifs <;> rfl
  · -- clientResult = st'.free.length
    rw [hst'_eq, hrun_res]
    cases ho : st.owner j₀ with
    | none => simp [hsp_eq]
    | some prevI =>
      have hne : prevI.val ≠ ws.n := ne_of_lt prevI.isLt
      simp [hne, hsp_eq]
  · -- AuctionMem ws C st' s'
    rw [hst'_eq, hrun_state]
    have hs_mid_c : ∀ i j : Fin ws.n, s_mid.mem (ws.bC + (i.val * ws.n + j.val)) = C (i, j) :=
      fun i j => by
        have hlt_ij : i.val * ws.n + j.val < ws.n * ws.n := Cslib.Matrix.pairIndex_lt (i, j)
        dsimp only [s_mid]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact ham.hC i j
    have hs_mid_owner : ∀ j : Fin ws.n,
        s_mid.mem (ws.bOwner + j.val) =
          (Function.update st.owner j₀ (some i₀) j).elim ws.n Fin.val := fun j => by
      dsimp only [s_mid]
      by_cases hj : j = j₀
      · subst hj; simp
      · have hne : j.val ≠ j₀.val := Fin.val_ne_of_ne hj
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne hj]
        exact ham.hOwner j
    have hs_mid_price : ∀ j : Fin ws.n,
        s_mid.mem (ws.bPrice + j.val) = (Function.update st.price j₀ newPZ j).toNat := fun j => by
      dsimp only [s_mid]
      rw [Function.update_of_ne (by omega)]
      by_cases hj : j = j₀
      · subst hj; simp
      · have hne : j.val ≠ j₀.val := Fin.val_ne_of_ne hj
        rw [Function.update_of_ne (by omega), Function.update_of_ne hj]
        exact ham.hPrice j
    have hstack_tail : ∀ k (hk : k < rest.length),
        s₀.mem (ws.bStack + k) = (rest[rest.length - 1 - k]'(by omega)).val := fun k hk => by
      have hk' : k < st.free.length := by rw [hsp_eq]; omega
      have h := ham.hStack k hk'
      simp only [hs_free, List.length_cons,
        show rest.length + 1 - 1 - k = rest.length - k by omega,
        show rest.length - k = (rest.length - 1 - k) + 1 by omega,
        List.getElem_cons_succ] at h
      exact h
    cases ho : st.owner j₀ with
    | none =>
      simp only [Option.elim_none, ↓reduceIte, Option.toList_none, List.nil_append]
      refine ⟨hs_mid_c, hs_mid_owner, hs_mid_price, fun k hk => ?_⟩
      dsimp only [s_mid] at hk ⊢
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hstack_tail k hk
    | some prevI =>
      have hne : prevI.val ≠ ws.n := ne_of_lt prevI.isLt
      simp only [Option.elim_some, hne, ↓reduceIte, Option.toList_some, List.singleton_append]
      refine ⟨fun i j => ?_, fun j => ?_, fun j => ?_, fun k hk => ?_⟩
      · have hlt_ij : i.val * ws.n + j.val < ws.n * ws.n := Cslib.Matrix.pairIndex_lt (i, j)
        exact (Function.update_of_ne (by omega) _ _).trans (hs_mid_c i j)
      · exact (Function.update_of_ne (by omega) _ _).trans (hs_mid_owner j)
      · exact (Function.update_of_ne (by omega) _ _).trans (hs_mid_price j)
      · simp only [List.length_cons] at hk ⊢
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt_r | rfl
        · dsimp only [s_mid]
          rw [Function.update_of_ne (by rw [hsp_eq]; omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), hstack_tail k hlt_r]
          simp only [show rest.length + 1 - 1 - k = (rest.length - 1 - k) + 1 by omega,
            List.getElem_cons_succ]
        · rw [show st.free.length - 1 = rest.length by rw [hsp_eq]; omega, Function.update_self]
          simp only [Nat.add_sub_cancel, Nat.sub_self, List.getElem_cons_zero]

end

end Cslib.Algorithms.WordRAM.Auction
