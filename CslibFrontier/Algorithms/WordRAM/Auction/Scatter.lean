/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Auction.Workspace
public import CslibFrontier.Computability.WordRAM.ListOutput
import CslibFrontier.Computability.WordRAM.Realization.FramedLoop
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
  obtain ⟨hsafe, hloop⟩ := Memory.FramedTriple.iterate (w := w) (body := scatterStep)
    (safe := ScatterStepSafe)
    (s := ⟨Function.update s₀.mem ws.outBase ws.n, s₀.frontier⟩) (d := ws) (n := ws.n) (a₀ := 0)
    (c := 2) (S := Set.Ico (ws.outBase + 1) (ws.outBase + ws.n + 1))
    (fun k idx t => idx = k ∧ t.frontier = s₀.frontier ∧ ∀ j : Fin ws.n, j.val < k →
      ∀ i : Fin ws.n, st.owner j = some i → t.mem (ws.outBase + 1 + i.val) = j.val)
    ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    (fun k hk idx t ⟨hidx, hsfr, hscat⟩ hmod => by
      subst idx
      let jk : Fin ws.n := ⟨k, hk⟩
      obtain ⟨ik, hik⟩ := howner_some jk
      have hik_lt := ik.isLt
      have ho_k : t.mem (ws.bOwner + k) = ik.val := by
        rw [hmod.2 (ws.bOwner + k) (by dsimp only; omega) (by region_omega)]; dsimp only
        rw [Function.update_of_ne (by omega), ham.hOwner jk, hik]; rfl
      refine ⟨⟨hfit1, by region_omega, by rw [ho_k]; region_omega, by region_omega⟩, ?_⟩
      unfold scatterStep
      framed_triple
      refine ⟨rfl, hsfr, fun j hj i hi => ?_⟩
      dsimp only; rw [ho_k]
      by_cases hii : i = ik
      · subst hii
        obtain rfl : j = jk := hinv.owner_inj j jk i hi hik
        exact Function.update_self _ _ _
      · have hjk : j.val ≠ k := fun h => hii (Option.some_injective _
          (hi.symm.trans ((congrArg st.owner (Fin.ext h : j = jk)).trans hik)))
        rw [Function.update_of_ne (by have := Fin.val_ne_of_ne hii; omega)]
        exact hscat j (by omega) i hi)
    fun _ _ h _ => h
  have hft : Memory.FramedTriple w s₀ (scatterProg ws) (2 * ws.n + 1)
      (Set.Ico ws.outBase (ws.outBase + ws.n + 1)) fun r t => t.frontier = s₀.frontier ∧
        r = ws.outBase ∧ t.mem ws.outBase = ws.n ∧ ∀ j : Fin ws.n, ∀ i : Fin ws.n,
          st.owner j = some i → t.mem (ws.outBase + 1 + i.val) = j.val := by
    unfold scatterProg
    exact Memory.FramedTriple.mono (Memory.FramedTriple.write_bind_of_mem (by omega)
      (by region_omega) (by region_omega) (Memory.FramedTriple.call (c₂ := 0) hloop
        (by region_omega) fun _ t h hm => Memory.FramedTriple.pure ⟨h.2.1, rfl,
          (hm.2 ws.outBase (by dsimp only; omega) (by region_omega)).trans
            (Function.update_self _ _ _), fun j => h.2.2 j j.isLt⟩)) (by omega) fun _ _ => id
  obtain ⟨hv, hc, hm, hfr', hr, hhdr, hscat⟩ := framedTriple_iff_realization.mp hft
  refine ⟨hsafe, hv, hc, hfr', hr, fun i j => ?_, ?_⟩
  · have hlt_ij : i.val * ws.n + j.val < ws.n * ws.n := Cslib.Matrix.pairIndex_lt (i, j)
    exact (hm.2 _ (by omega) (by region_omega)).trans (ham.hC i j)
  · rw [outputList_eq_iff]
    refine ⟨by simpa only [List.length_map, List.length_finRange] using hhdr, fun idx => ?_⟩
    let iFin : Fin ws.n := ⟨idx.val, by simpa using idx.isLt⟩
    simp only [Fin.getElem_fin, List.getElem_map, List.getElem_finRange]
    exact hscat (st.objectOf iFin) iFin (hinv.owner_objectOf hfree iFin)

end

end Cslib.Algorithms.WordRAM.Auction
