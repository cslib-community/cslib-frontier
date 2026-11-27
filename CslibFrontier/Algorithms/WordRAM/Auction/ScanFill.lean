/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Auction.Workspace
public import CslibFrontier.Computability.WordRAM.Signed.Encoding
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.Foundations.Data.Matrix.PairChunks
import CslibFrontier.Tactic.Realize

/-!
# Input scanning and unsigned cost-matrix initialization for Word-RAM auction

First-stage memory-client subroutines of Bertsekas's auction algorithm:

* `scanMaxProg`: scans the signed `n × n` input matrix at `matBase` for an entry magnitude bound
  `M ≤ maxMag`.
* `fillCProg`: reads each signed input entry and stores the shifted, scaled unsigned integer cost
  `ws.scale * (cost (i, j) + M)` in row-major order at `ws.bC`.

All inner iteration step functions, state encodings (`ScanState`), and per-step `realize`
certificates remain `private` to this module.

## Main definitions

* `Cslib.Algorithms.WordRAM.Auction.ScanArgs`, `Cslib.Algorithms.WordRAM.Auction.encScanArgs`:
  two-word scan descriptor `(matBase, total)`.
* `Cslib.Algorithms.WordRAM.Auction.scanMaxProg`, `Cslib.Algorithms.WordRAM.Auction.ScanMaxSafe`:
  input-magnitude scan program and its safety predicate.
* `Cslib.Algorithms.WordRAM.Auction.fillCProg`, `Cslib.Algorithms.WordRAM.Auction.FillCProgSafe`:
  shifted-scaled matrix-fill program and its safety predicate.

## Main results

* `Cslib.Algorithms.WordRAM.Auction.scanMaxProg_realizes`,
  `Cslib.Algorithms.WordRAM.Auction.scanMaxProg_spec`: Word-RAM realization and specification
  of `scanMaxProg`.
* `Cslib.Algorithms.WordRAM.Auction.fillCProg_realizes`,
  `Cslib.Algorithms.WordRAM.Auction.fillC_spec`: Word-RAM realization and specification of
  `fillCProg`.
-/

namespace Cslib.Algorithms.WordRAM.Auction

open Cslib.WordRAM
open Cslib.WordRAM.Realization
open Cslib.DataStructure
open StateTransitionSpec (clientResult_bind clientState_bind clientResult_pure clientState_pure)

public section

/-- Arguments for scanning a contiguous `total`-word signed matrix starting at `matBase`. -/
structure ScanArgs where
  /-- Start address of the encoded signed matrix words. -/
  matBase : ℕ
  /-- Number of entries to scan (`n * n`). -/
  total : ℕ

/-- Faithful two-word encoding of `ScanArgs`. -/
word_enc_structure encScanArgs : ScanArgs where
  matBase : wordWords, total : wordWords

/-- Registered `WordEncoding` for `ScanArgs`. -/
instance : WordEncoding ScanArgs := ⟨2, encScanArgs⟩

end

private structure ScanState where
  idx : ℕ
  curM : ℕ

private word_enc_structure encScanState : ScanState where
  idx : wordWords, curM : wordWords

private instance : WordEncoding ScanState := ⟨2, encScanState⟩

private theorem pairIndex_of_lt {n k : ℕ} (hk : k < n * n) :
    ∃ i j : Fin n, i.val * n + j.val = k := by
  have hn_pos : 0 < n := by by_contra h0; simp [Nat.eq_zero_of_not_pos h0] at hk
  exact ⟨⟨k / n, (Nat.div_lt_iff_lt_mul hn_pos).mpr hk⟩, ⟨k % n, Nat.mod_lt _ hn_pos⟩,
    by rw [Nat.mul_comm, Nat.div_add_mod]⟩

/-! ### Scanning input costs for `M ≤ maxMag` -/

private def scanMaxStep (x : ScanArgs × ScanState) : Memory.Prog ScanState := do
  let d := x.1
  let st := x.2
  let raw ← Memory.read (d.matBase + st.idx)
  let mag := raw / 2
  if st.curM < mag then
    pure ⟨st.idx + 1, mag⟩
  else
    pure ⟨st.idx + 1, st.curM⟩

private abbrev ScanMaxStepSafe (w : ℕ) (x : ScanArgs × ScanState) (_ : Memory.State) : Prop :=
  Fits w 2 ∧ Fits w (x.1.matBase + x.2.idx) ∧ Fits w (x.2.idx + 1)

private theorem scanMaxStep_realizes :
    Realizes .exact scanMaxStep (appendWords encScanArgs encScanState) encScanState
      ScanMaxStepSafe (fun _ _ => 0) := by
  unfold scanMaxStep
  realize
  all_goals
    rcases h with ⟨_, _, _⟩
    first | assumption | omega

public section

/-- Scan `d.total` `Signed.encode` words from `d.matBase`, returning `max |cost|`. -/
def scanMaxProg (d : ScanArgs) : Memory.Prog ℕ := do
  let res ← iterate scanMaxStep d d.total ⟨0, 0⟩
  pure res.curM

/-- Word-width safety predicate for `scanMaxProg`. -/
def ScanMaxSafe (w : ℕ) (d : ScanArgs) (s : Memory.State) : Prop :=
  iterationSafe scanMaxStep ScanMaxStepSafe w d d.total ⟨0, 0⟩ s

/-- `realize` certificate for `scanMaxProg`. -/
theorem scanMaxProg_realizes :
    Realizes .exact scanMaxProg encScanArgs wordWords ScanMaxSafe (fun _ _ => 0) := by
  unfold scanMaxProg
  realize [scanMaxStep_realizes]
  exact h

/-- Specification of `scanMaxProg`: preserves memory state, incurs cost `≤ n * n`, and bounds
every entry's magnitude by the returned `M ≤ maxM`. -/
theorem scanMaxProg_spec {w n matBase maxM : ℕ} {cost : Fin n × Fin n → ℤ}
    {s₀ : Memory.State}
    (hcost_mem : ∀ i j : Fin n,
      s₀.mem (matBase + (i.val * n + j.val)) = Signed.encode (cost (i, j)))
    (hmag : ∀ i j : Fin n, (cost (i, j)).natAbs ≤ maxM)
    (hfr : matBase + n * n ≤ s₀.frontier)
    (hfit2 : Fits w 2) (hfit_end : Fits w (matBase + n * n)) :
    let d : ScanArgs := ⟨matBase, n * n⟩
    let M := (Memory.spec 0).clientResult s₀ (scanMaxProg d)
    ScanMaxSafe w d s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (scanMaxProg d)) ∧
      memoryCost (scanMaxProg d) s₀ ≤ n * n ∧
      (Memory.spec 0).clientState s₀ (scanMaxProg d) = s₀ ∧
      M ≤ maxM ∧ ∀ i j : Fin n, (cost (i, j)).natAbs ≤ M := by
  let d : ScanArgs := ⟨matBase, n * n⟩
  obtain ⟨hsafe, hv_it, hmc_it, _, _, hs_eq, _, hM_le, hprev⟩ :=
    iterate_spec scanMaxStep ScanMaxStepSafe w d 1 (n * n)
      (fun k st s => s = s₀ ∧ st.idx = k ∧ st.curM ≤ maxM ∧
        ∀ idx < k, s₀.mem (matBase + idx) / 2 ≤ st.curM)
      (fun _ => False)
      (fun k hk st s ⟨hs, hidx, hle, hprev⟩ => by
        subst s
        have hsafe : ScanMaxStepSafe w (d, st) s₀ :=
          ⟨hfit2, hfit_end.of_le (by dsimp only [d]; omega),
            hfit_end.of_le (by dsimp only [d]; omega)⟩
        let addr := matBase + st.idx
        let next : ScanState := ⟨st.idx + 1, max st.curM (s₀.mem addr / 2)⟩
        have run : (Memory.spec 0).runClient s₀ (scanMaxStep (d, st)) =
            (next, s₀, [.read addr]) := by
          unfold scanMaxStep
          rw [← PFunctor.FreeM.bind_eq_bind, StateTransitionSpec.runClient_bind, runClient_read]
          dsimp only [d, next, addr]
          split_ifs with h
          · rw [max_eq_right h.le]; rfl
          · rw [max_eq_left (Nat.le_of_not_lt h)]; rfl
        have hv : (Memory.spec w).ValidHistory s₀
            ((Memory.spec w).clientHistory s₀ (scanMaxStep (d, st))) := by
          rw [StateTransitionSpec.clientHistory, runClient_width w, run]
          exact ⟨(Nat.add_lt_add_left (hidx ▸ hk) matBase).trans_le hfr, trivial⟩
        have hmc : memoryCost (scanMaxStep (d, st)) s₀ ≤ 1 := by
          simp [memoryCost, StateTransitionSpec.clientHistory, run]
        have hst_eq : (Memory.spec 0).clientState s₀ (scanMaxStep (d, st)) = s₀ :=
          congrArg (fun r => r.2.1) run
        have hdiv_le : s₀.mem (matBase + st.idx) / 2 ≤ maxM := by
          obtain ⟨i, j, hij⟩ := pairIndex_of_lt (hidx ▸ hk)
          simpa [← hij, hcost_mem i j, Signed.encode_div_two] using hmag i j
        refine ⟨hsafe, hv, hmc, by rw [hst_eq], fun _ _ => by rw [hst_eq], hst_eq, ?_⟩
        rw [StateTransitionSpec.clientResult, run]
        refine ⟨congrArg (· + 1) hidx, max_le hle hdiv_le, fun idx hidx_lt => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hidx_lt with hlt | rfl
        · exact (hprev idx hlt).trans (le_max_left _ _)
        · exact hidx ▸ le_max_right _ _)
      ⟨0, 0⟩ s₀ ⟨rfl, rfl, Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  dsimp only [d]
  unfold scanMaxProg
  refine ⟨hsafe, validHistory_bind_step hv_it (validHistory_pure w _ _), ?_,
    by rw [clientState_bind, clientState_pure, hs_eq], ?_, fun i j => ?_⟩
  · rw [memoryCost_bind', memoryCost_pure]
    dsimp only [d] at hmc_it ⊢; omega
  · simpa only [clientResult_bind, clientResult_pure] using hM_le
  · rw [clientResult_bind, clientResult_pure]
    simpa [hcost_mem i j, Signed.encode_div_two] using
      hprev (i.val * n + j.val) (Cslib.Matrix.pairIndex_lt (i, j))

end

/-! ### Filling the shifted, scaled unsigned cost matrix -/

private def fillCStep (x : AuctionWS × ℕ) : Memory.Prog ℕ := do
  let ws := x.1
  let idx := x.2
  let raw ← Memory.read (ws.matBase + idx)
  let mag := raw / 2
  let sign := raw % 2
  if sign = 0 then
    Memory.write (ws.bC + idx) (ws.scale * (ws.M + mag))
    pure (idx + 1)
  else
    Memory.write (ws.bC + idx) (ws.scale * (ws.M - mag))
    pure (idx + 1)

private abbrev FillCStepSafe (w : ℕ) (x : AuctionWS × ℕ) (s : Memory.State) : Prop :=
  let ws := x.1
  let idx := x.2
  let mag := s.mem (ws.matBase + idx) / 2
  Fits w 2 ∧ Fits w (ws.matBase + idx) ∧ Fits w (ws.bC + idx) ∧ Fits w (idx + 1) ∧
    mag ≤ ws.M ∧ Fits w (ws.M + mag) ∧ Fits w (ws.scale * (ws.M + mag))

private theorem fillCStep_realizes :
    Realizes .exact fillCStep (appendWords encAuctionWS wordWords) wordWords
      FillCStepSafe (fun _ _ => 0) := by
  unfold fillCStep
  realize
  all_goals
    rcases h with ⟨_, _, _, _, _, _, hfsc⟩
    first
    | assumption
    | omega
    | exact hfsc.of_le (Nat.mul_le_mul_left _ (by omega))

public section

/-- Populate the shifted, scaled unsigned cost matrix at `ws.bC[0..n*n)`. -/
def fillCProg (ws : AuctionWS) : Memory.Prog ℕ :=
  iterate fillCStep ws (ws.n * ws.n) 0

/-- Word-width safety predicate for `fillCProg`. -/
def FillCProgSafe (w : ℕ) (ws : AuctionWS) (s : Memory.State) : Prop :=
  Fits w (ws.n * ws.n) ∧ iterationSafe fillCStep FillCStepSafe w ws (ws.n * ws.n) 0 s

/-- `realize` certificate for `fillCProg`. -/
theorem fillCProg_realizes :
    Realizes .exact fillCProg encAuctionWS wordWords FillCProgSafe (fun _ _ => 0) := by
  unfold fillCProg
  realize [fillCStep_realizes]
  all_goals
    rcases h with ⟨_, _⟩
    assumption

/-- Specification of `fillCProg`: writes `ws.scale * (cost (i, j) + ws.M).toNat` row-major at
`ws.bC` in at most `2 * n * n` memory steps without touching outside addresses. -/
theorem fillC_spec {w : ℕ} (ws : AuctionWS) {cost : Fin ws.n × Fin ws.n → ℤ}
    (s₀ : Memory.State)
    (hsc : 1 ≤ ws.scale)
    (hdisj : ws.matBase + ws.n * ws.n ≤ ws.bC)
    (hfr : ws.bC + ws.n * ws.n ≤ s₀.frontier)
    (hcost_mem : ∀ i j : Fin ws.n,
      s₀.mem (ws.matBase + (i.val * ws.n + j.val)) = Signed.encode (cost (i, j)))
    (hM_ge : ∀ i j : Fin ws.n, (cost (i, j)).natAbs ≤ ws.M)
    (hfit2 : Fits w 2) (hfit_addr : Fits w (ws.bC + ws.n * ws.n))
    (hfit_val : Fits w (ws.scale * (2 * ws.M))) :
    let prog := fillCProg ws
    let s' := (Memory.spec 0).clientState s₀ prog
    FillCProgSafe w ws s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
      memoryCost prog s₀ ≤ 2 * (ws.n * ws.n) ∧
      s'.frontier = s₀.frontier ∧
      (∀ a, ¬(ws.bC ≤ a ∧ a < ws.bC + ws.n * ws.n) → s'.mem a = s₀.mem a) ∧
      ∀ i j : Fin ws.n,
        s'.mem (ws.bC + (i.val * ws.n + j.val)) =
          ws.scale * (cost (i, j) + (ws.M : ℤ)).toNat := by
  obtain ⟨hsafe, hv, hmc, hfr', hmod, _, _, _, hfilled⟩ :=
    iterate_spec fillCStep FillCStepSafe w ws 2 (ws.n * ws.n)
      (fun k idx s => idx = k ∧ s.frontier = s₀.frontier ∧
        (∀ a < ws.bC, s.mem a = s₀.mem a) ∧
        ∀ i j : Fin ws.n, i.val * ws.n + j.val < k →
          s.mem (ws.bC + (i.val * ws.n + j.val)) =
            ws.scale * (cost (i, j) + (ws.M : ℤ)).toNat)
      (fun a => ws.bC ≤ a ∧ a < ws.bC + ws.n * ws.n)
      (fun k hk idx s ⟨hidx, hsfr, hlow, hfilled⟩ => by
        subst idx
        obtain ⟨i₀, j₀, hij₀⟩ := pairIndex_of_lt hk
        have hraw : s.mem (ws.matBase + k) = Signed.encode (cost (i₀, j₀)) := by
          rw [hlow _ (by omega), ← hij₀, hcost_mem i₀ j₀]
        have hmag_le : s.mem (ws.matBase + k) / 2 ≤ ws.M := by
          simpa [hraw, Signed.encode_div_two] using hM_ge i₀ j₀
        have hf_sc : Fits w (ws.scale * (ws.M + s.mem (ws.matBase + k) / 2)) :=
          hfit_val.of_le (Nat.mul_le_mul_left _ (by omega))
        have hsafe : FillCStepSafe w (ws, k) s := by
          dsimp only [FillCStepSafe]
          exact ⟨hfit2, hfit_addr.of_le (by omega), hfit_addr.of_le (by omega),
            hfit_addr.of_le (by omega), hmag_le, hf_sc.of_le (Nat.le_mul_of_pos_left _ hsc), hf_sc⟩
        let written :=
          if s.mem (ws.matBase + k) % 2 = 0 then
            ws.scale * (ws.M + s.mem (ws.matBase + k) / 2)
          else
            ws.scale * (ws.M - s.mem (ws.matBase + k) / 2)
        have hwritten : written = ws.scale * (cost (i₀, j₀) + (ws.M : ℤ)).toNat := by
          dsimp only [written]
          rw [hraw, Signed.encode_mod_two, Signed.encode_div_two]
          have hm := hM_ge i₀ j₀
          by_cases hneg : cost (i₀, j₀) < 0 <;> simp only [hneg, ↓reduceIte, one_ne_zero] <;>
            exact congrArg _ (by omega)
        have run : (Memory.spec 0).runClient s (fillCStep (ws, k)) =
            (k + 1, ⟨Function.update s.mem (ws.bC + k) written, s.frontier⟩,
              [.read (ws.matBase + k), .write (ws.bC + k) written]) := by
          unfold fillCStep
          rw [← PFunctor.FreeM.bind_eq_bind, StateTransitionSpec.runClient_bind, runClient_read]
          dsimp only [written]
          split_ifs <;> rfl
        have hv : (Memory.spec w).ValidHistory s
            ((Memory.spec w).clientHistory s (fillCStep (ws, k))) := by
          have hf_written : Fits w written := by
            dsimp only [written]
            split_ifs <;> exact hf_sc.of_le (Nat.mul_le_mul_left _ (by omega))
          rw [StateTransitionSpec.clientHistory, runClient_width w, run]
          have hread : ws.matBase + k < s.frontier := by omega
          have hwrite : ws.bC + k < s.frontier := by omega
          exact ⟨hread, ⟨hwrite, hf_written⟩, trivial⟩
        have hmc : memoryCost (fillCStep (ws, k)) s ≤ 2 := by
          simp [memoryCost, StateTransitionSpec.clientHistory, run]
        have hst_eq : (Memory.spec 0).clientState s (fillCStep (ws, k)) =
            ⟨Function.update s.mem (ws.bC + k) written, s.frontier⟩ :=
          congrArg (fun r => r.2.1) run
        refine ⟨hsafe, hv, hmc, by rw [hst_eq],
          fun x hx => hst_eq ▸ Function.update_of_ne (by omega) _ _, ?_⟩
        rw [hst_eq, StateTransitionSpec.clientResult, run]
        dsimp only
        refine ⟨rfl, hsfr,
          fun a ha => (Function.update_of_ne (by omega) _ _).trans (hlow a ha),
          fun i j hij => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hij with hlt' | heq
        · exact (Function.update_of_ne (by omega) _ _).trans (hfilled i j hlt')
        · rcases Cslib.Matrix.pairIndex_injective (a₁ := (i, j)) (a₂ := (i₀, j₀))
              (heq.trans hij₀.symm) with ⟨rfl, rfl⟩
          rw [heq, Function.update_self, hwritten])
      0 s₀ ⟨rfl, rfl, fun _ _ => rfl, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  exact ⟨⟨hfit_addr.of_le (by omega), hsafe⟩, hv, hmc, hfr', hmod,
    fun i j => hfilled i j (Cslib.Matrix.pairIndex_lt (i, j))⟩

end

end Cslib.Algorithms.WordRAM.Auction
