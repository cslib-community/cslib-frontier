/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Auction.Workspace
public import CslibFrontier.Computability.WordRAM.ListOutput
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.Foundations.Data.Matrix.PairChunks
import CslibFrontier.Tactic.Realize

/-!
# Scattering object-owner map to output memory for Word-RAM auction

Writes the length-prefixed assignment list `[objectOf 0, …, objectOf (n - 1)]` at `ws.outBase`
by scattering the inverse array `owner[0..n)`. Preserves the unsigned cost matrix `C` at `ws.bC`
so `sumScaledCostProg` can read it afterward.

## Main definitions

* `Cslib.Algorithms.WordRAM.Auction.scatterProg`,
  `Cslib.Algorithms.WordRAM.Auction.ScatterProgSafe`: output-scattering program and safety
  predicate.

## Main results

* `Cslib.Algorithms.WordRAM.Auction.scatterProg_realizes`,
  `Cslib.Algorithms.WordRAM.Auction.scatterProg_spec`: Word-RAM realization and specification of
  `scatterProg`.
-/

namespace Cslib.Algorithms.WordRAM.Auction

open Cslib.WordRAM
open Cslib.WordRAM.Realization
open Cslib.DataStructure
open Cslib.Algorithms.Lean.Assignment
open StateTransitionSpec (clientResult_bind clientState_bind clientResult_pure clientState_pure)

private def scatterStep (x : AuctionWS × ℕ) : Memory.Prog ℕ := do
  let ws := x.1
  let j := x.2
  let i ← Memory.read (ws.bOwner + j)
  Memory.write (ws.outBase + 1 + i) j
  pure (j + 1)

private abbrev ScatterStepSafe (w : ℕ) (x : AuctionWS × ℕ) (s : Memory.State) : Prop :=
  let ws := x.1
  let j := x.2
  Fits w 1 ∧ Fits w (ws.bOwner + j) ∧ Fits w (ws.outBase + 1 + s.mem (ws.bOwner + j)) ∧
    Fits w (j + 1)

private theorem scatterStep_realizes :
    Realizes .exact scatterStep (appendWords encAuctionWS wordWords) wordWords
      ScatterStepSafe (fun _ _ => 0) := by
  unfold scatterStep
  realize
  all_goals
    rcases h with ⟨_, _, _, _⟩
    assumption

public section

/-- Scatter the completed `owner[0..n)` array to the length-prefixed output list at `ws.outBase`. -/
def scatterProg (ws : AuctionWS) : Memory.Prog ℕ := do
  Memory.write ws.outBase ws.n
  let _ ← iterate scatterStep ws ws.n 0
  pure ws.outBase

/-- Word-width safety predicate for `scatterProg`. -/
def ScatterProgSafe (w : ℕ) (ws : AuctionWS) (s : Memory.State) : Prop :=
  let s₁ : Memory.State := ⟨Function.update s.mem ws.outBase ws.n, s.frontier⟩
  iterationSafe scatterStep ScatterStepSafe w ws ws.n 0 s₁

/-- `realize` certificate for `scatterProg`. -/
theorem scatterProg_realizes :
    Realizes .exact scatterProg encAuctionWS wordWords ScatterProgSafe (fun _ _ => 0) := by
  unfold scatterProg
  realize [scatterStep_realizes]
  exact iterationSafe_imp h (fun _ => rfl) fun _ _ hs => hs

/-- Specification of `scatterProg`: preserves the unsigned cost matrix `C` at `ws.bC` and writes
`[objectOf 0, …, objectOf (n - 1)]` as a length-prefixed list at `ws.outBase`. -/
theorem scatterProg_spec {w : ℕ} (ws : AuctionWS) {C : Fin ws.n × Fin ws.n → ℕ}
    {st : AuctionState ws.n} (hinv : AuctionInv (fun e => (C e : ℤ)) (ws.eps : ℤ) st)
    (hfree : st.free = [])
    (s₀ : Memory.State) (hws : ValidWS ws s₀) (ham : AuctionMem ws C st s₀)
    (hfit1 : Fits w 1) (hfit_ws : Fits w (ws.outBase + ws.n + 1)) :
    let s' := (Memory.spec 0).clientState s₀ (scatterProg ws)
    ScatterProgSafe w ws s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (scatterProg ws)) ∧
      memoryCost (scatterProg ws) s₀ ≤ 2 * ws.n + 1 ∧
      s'.frontier = s₀.frontier ∧
      (Memory.spec 0).clientResult s₀ (scatterProg ws) = ws.outBase ∧
      (∀ i j : Fin ws.n, s'.mem (ws.bC + (i.val * ws.n + j.val)) = C (i, j)) ∧
      outputList s'.mem ws.outBase = (List.finRange ws.n).map fun i => (st.objectOf i).val := by
  obtain ⟨hbO, hbP, hbS, hout, hfr⟩ := hws
  have howner_some (j : Fin ws.n) : ∃ i : Fin ws.n, st.owner j = some i :=
    ⟨_, (congrArg st.owner (hinv.objectOf_personOf hfree j)).symm.trans
      (hinv.owner_objectOf hfree _)⟩
  let s₁ : Memory.State := ⟨Function.update s₀.mem ws.outBase ws.n, s₀.frontier⟩
  have hit := iterate_spec scatterStep ScatterStepSafe w ws 2 ws.n
    (fun k idx s => idx = k ∧ s.frontier = s₀.frontier ∧
      s.mem ws.outBase = ws.n ∧
      (∀ a < ws.outBase, s.mem a = s₀.mem a) ∧
      ∀ j : Fin ws.n, j.val < k → ∀ i : Fin ws.n, st.owner j = some i →
        s.mem (ws.outBase + 1 + i.val) = j.val)
    (fun a => ws.outBase + 1 ≤ a ∧ a < ws.outBase + ws.n + 1)
    (fun k hk idx s ⟨hidx, hsfr, hhdr, hlow, hscat⟩ => by
      subst idx
      let jk : Fin ws.n := ⟨k, hk⟩
      obtain ⟨ik, hik⟩ := howner_some jk
      have ho_k : s.mem (ws.bOwner + k) = ik.val := by
        rw [hlow _ (by omega), ham.hOwner jk, hik]; rfl
      have hsafe : ScatterStepSafe w (ws, k) s := by
        dsimp only [ScatterStepSafe]
        refine ⟨hfit1, hfit_ws.of_le (by omega), ?_, hfit_ws.of_le (by omega)⟩
        rw [ho_k]; exact hfit_ws.of_le (by have := ik.isLt; omega)
      have hv : (Memory.spec w).ValidHistory s
          ((Memory.spec w).clientHistory s (scatterStep (ws, k))) := by
        unfold scatterStep
        dsimp only
        exact validHistory_read_bind (by omega)
          (validHistory_write_bind (by rw [ho_k]; have := ik.isLt; omega)
            (hfit_ws.of_le (by omega)) (validHistory_pure w _ _))
      have hmc : memoryCost (scatterStep (ws, k)) s ≤ 2 :=
        memoryCost_read_bind_le fun _ _ => memoryCost_write_bind_le fun _ _ => le_rfl
      have hst_eq : (Memory.spec 0).clientState s (scatterStep (ws, k)) =
          ⟨Function.update s.mem (ws.outBase + 1 + ik.val) k, s.frontier⟩ := by
        rw [scatterStep, clientState_bind_read]
        dsimp only
        rw [ho_k, clientState_bind_write, clientState_pure]
      have hres_eq : (Memory.spec 0).clientResult s (scatterStep (ws, k)) = k + 1 := by
        rw [scatterStep, clientResult_bind_read, clientResult_bind_write, clientResult_pure]
      refine ⟨hsafe, hv, hmc, by rw [hst_eq], fun x hx => ?_, ?_⟩
      · rw [hst_eq]
        exact Function.update_of_ne (by have := ik.isLt; omega) _ _
      · rw [hst_eq, hres_eq]
        dsimp only
        refine ⟨rfl, hsfr, ?_, fun a ha => ?_, fun j hj i hi => ?_⟩
        · rw [Function.update_of_ne (by omega)]; exact hhdr
        · rw [Function.update_of_ne (by omega)]; exact hlow a ha
        · by_cases hii : i = ik
          · subst hii
            obtain rfl : j = jk := hinv.owner_inj j jk i hi hik
            exact Function.update_self _ _ _
          · have hjk : j.val ≠ k := fun h => hii (Option.some_injective _
              (hi.symm.trans ((congrArg st.owner (Fin.ext h : j = jk)).trans hik)))
            rw [Function.update_of_ne (by have := Fin.val_ne_of_ne hii; omega)]
            exact hscat j (by omega) i hi)
    0 s₁ ⟨rfl, rfl, Function.update_self _ _ _,
      fun a ha => Function.update_of_ne (by omega) _ _,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hv_it, hmc_it, hfr_it, _, _, _, hhdr, hlow, hscat⟩ := hit
  unfold scatterProg
  refine ⟨hsafe,
    validHistory_write_bind (by omega) (hfit_ws.of_le (by omega))
      (validHistory_bind_step hv_it (validHistory_pure w _ _)),
    ?_, ?_, ?_, fun i j => ?_, ?_⟩
  · rw [memoryCost_bind', memoryCost_write, clientState_write, memoryCost_bind', memoryCost_pure]
    dsimp only [s₁] at hmc_it
    omega
  · rwa [clientState_bind_write, clientState_bind, clientState_pure]
  · rw [clientResult_bind_write, clientResult_bind, clientResult_pure]
  · rw [clientState_bind_write, clientState_bind, clientState_pure]
    have hlt_ij : i.val * ws.n + j.val < ws.n * ws.n := Cslib.Matrix.pairIndex_lt (i, j)
    exact (hlow _ (by omega)).trans (ham.hC i j)
  · rw [clientState_bind_write, clientState_bind, clientState_pure, outputList_eq_iff]
    refine ⟨by simpa only [List.length_map, List.length_finRange] using hhdr, fun idx => ?_⟩
    have hi_lt : idx.val < ws.n := by simpa using idx.isLt
    let iFin : Fin ws.n := ⟨idx.val, hi_lt⟩
    change ((Memory.spec 0).clientState s₁ (iterate scatterStep ws ws.n 0)).mem
        (ws.outBase + 1 + idx.val) =
      ((List.finRange ws.n).map fun i => (st.objectOf i).val)[idx.val]
    simp only [List.getElem_map, List.getElem_finRange]
    exact hscat (st.objectOf iFin) (st.objectOf iFin).isLt iFin (hinv.owner_objectOf hfree iFin)

end

end Cslib.Algorithms.WordRAM.Auction
