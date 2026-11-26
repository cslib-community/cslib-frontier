/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Auction.Workspace
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Foundations.Data.Matrix.PairChunks
import CslibFrontier.Tactic.Realize

/-!
# Row scans for best and second-best reduced costs in Word-RAM auction

Two independent read-only `O(n)` row scans over `C[i₀, ·] + price[·]`:

* `findBestProg`: computes `bestObject` (argmin of reduced cost across `j : Fin n`).
* `findSecondProg`: computes `secondBest` (minimum reduced cost over `j ≠ bestJ`).

Both loop specs share the readout lemma `AuctionMem.redCost_read` from `Auction.Workspace`. The
single-step functions and their `realize` certificates remain `private`.

## Main definitions

* `Cslib.Algorithms.WordRAM.Auction.ScanRowArgs`, `Cslib.Algorithms.WordRAM.Auction.BestState`,
  `Cslib.Algorithms.WordRAM.Auction.findBestProg`, `Cslib.Algorithms.WordRAM.Auction.FindBestSafe`:
  best-object row scan arguments, state, program, and safety predicate.
* `Cslib.Algorithms.WordRAM.Auction.ScanSecondArgs`,
  `Cslib.Algorithms.WordRAM.Auction.SecondState`,
  `Cslib.Algorithms.WordRAM.Auction.findSecondProg`,
  `Cslib.Algorithms.WordRAM.Auction.FindSecondSafe`: second-best row scan arguments, state,
  program, and safety predicate.

## Main results

* `Cslib.Algorithms.WordRAM.Auction.findBestProg_realizes`,
  `Cslib.Algorithms.WordRAM.Auction.findBest_spec`: realization and specification of the argmin
  scan.
* `Cslib.Algorithms.WordRAM.Auction.findSecondProg_realizes`,
  `Cslib.Algorithms.WordRAM.Auction.findSecond_spec`: realization and specification of the
  second-best reduced-cost scan.
-/

namespace Cslib.Algorithms.WordRAM.Auction

open Cslib.WordRAM
open Cslib.WordRAM.Realization
open Cslib.DataStructure
open Cslib.Algorithms.Lean.Assignment

public section

/-- Arguments for scanning one row `rowBase[0..n)` against `bPrice[0..n)`. -/
structure ScanRowArgs where
  /-- Number of objects in the row. -/
  n : ℕ
  /-- Base address `bC + i₀ * n` of person `i₀`'s cost row. -/
  rowBase : ℕ
  /-- Base address of object prices. -/
  bPrice : ℕ

/-- Faithful three-word encoding of `ScanRowArgs`. -/
word_enc_structure encScanRowArgs : ScanRowArgs where
  n : wordWords, rowBase : wordWords, bPrice : wordWords

/-- Registered `WordEncoding` for `ScanRowArgs`. -/
instance : WordEncoding ScanRowArgs := ⟨3, encScanRowArgs⟩

/-- Running state of the argmin row scan (`findBestProg`). -/
structure BestState where
  /-- Next object index to inspect. -/
  idx : ℕ
  /-- Best object index seen so far. -/
  bestJ : ℕ
  /-- Least reduced cost seen so far. -/
  bestVal : ℕ

/-- Faithful three-word encoding of `BestState`. -/
word_enc_structure encBestState : BestState where
  idx : wordWords, bestJ : wordWords, bestVal : wordWords

/-- Registered `WordEncoding` for `BestState`. -/
instance : WordEncoding BestState := ⟨3, encBestState⟩

/-- Arguments for the second-best row scan (skipping `bestJ`). -/
structure ScanSecondArgs where
  /-- Number of objects in the row. -/
  n : ℕ
  /-- Base address `bC + i₀ * n` of person `i₀`'s cost row. -/
  rowBase : ℕ
  /-- Base address of object prices. -/
  bPrice : ℕ
  /-- Best object index to skip. -/
  bestJ : ℕ

/-- Faithful four-word encoding of `ScanSecondArgs`. -/
word_enc_structure encScanSecondArgs : ScanSecondArgs where
  n : wordWords, rowBase : wordWords, bPrice : wordWords, bestJ : wordWords

/-- Registered `WordEncoding` for `ScanSecondArgs`. -/
instance : WordEncoding ScanSecondArgs := ⟨4, encScanSecondArgs⟩

/-- Running state of the second-best reduced-cost scan (`findSecondProg`). -/
structure SecondState where
  /-- Next object index to inspect. -/
  idx : ℕ
  /-- `0` if no object other than `bestJ` has been seen yet; `1` otherwise. -/
  hasSecond : ℕ
  /-- Minimum reduced cost seen so far over `j ≠ bestJ`. -/
  secondVal : ℕ

/-- Faithful three-word encoding of `SecondState`. -/
word_enc_structure encSecondState : SecondState where
  idx : wordWords, hasSecond : wordWords, secondVal : wordWords

/-- Registered `WordEncoding` for `SecondState`. -/
instance : WordEncoding SecondState := ⟨3, encSecondState⟩

end

/-- Both scans read a cost and a price and then update only their local accumulator. -/
private def scanCell {α : Type} (cost price : ℕ) (next : ℕ → α) : Memory.Prog α := do
  let c ← Memory.read cost
  let p ← Memory.read price
  pure (next (c + p))

private theorem scanCell_spec {α : Type} {w cost price : ℕ} {s : Memory.State}
    (next : ℕ → α) (hc : cost < s.frontier) (hp : price < s.frontier) :
    let prog := scanCell cost price next
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
      memoryCost prog s = 2 ∧ (Memory.spec 0).clientState s prog = s ∧
      (Memory.spec 0).clientResult s prog = next (s.mem cost + s.mem price) :=
  ⟨validHistory_read_bind hc (validHistory_read_bind hp (validHistory_pure w _ _)),
    rfl, rfl, rfl⟩

private theorem rowReads_before_output {ws : AuctionWS} {s : Memory.State}
    (hws : ValidWS ws s) (i j : Fin ws.n) :
    ws.bC + i.val * ws.n + j.val < ws.outBase ∧ ws.bPrice + j.val < ws.outBase := by
  have hcell : i.val * ws.n + j.val < ws.n * ws.n := Cslib.Matrix.pairIndex_lt (i, j)
  have hj := j.isLt
  obtain ⟨hbO, hbP, hbS, hout, _⟩ := hws
  exact ⟨by lia, by lia⟩

/-! ### Row scan 1: best object (`findBestProg`) -/

private def bestNext (st : BestState) (rc : ℕ) : BestState :=
  if st.idx = 0 then ⟨1, 0, rc⟩
  else if rc < st.bestVal then ⟨st.idx + 1, st.idx, rc⟩
  else ⟨st.idx + 1, st.bestJ, st.bestVal⟩

private def findBestStep (x : ScanRowArgs × BestState) : Memory.Prog BestState :=
  scanCell (x.1.rowBase + x.2.idx) (x.1.bPrice + x.2.idx) (bestNext x.2)

private abbrev FindBestStepSafe (w : ℕ) (x : ScanRowArgs × BestState) (s : Memory.State) : Prop :=
  let d := x.1
  let st := x.2
  Fits w 1 ∧ Fits w (d.rowBase + st.idx) ∧ Fits w (d.bPrice + st.idx) ∧
    Fits w (s.mem (d.rowBase + st.idx) + s.mem (d.bPrice + st.idx)) ∧ Fits w (st.idx + 1)

private theorem findBestStep_realizes :
    Realizes .exact findBestStep (appendWords encScanRowArgs encBestState) encBestState
      FindBestStepSafe (fun _ _ => 0) := by
  unfold findBestStep scanCell bestNext
  simp only [apply_ite (pure : BestState → Memory.Prog BestState)]
  realize
  all_goals
    rcases h with ⟨_, _, _, _, _⟩
    assumption

public section

/-- Scan a row of length `d.n` to find the object minimizing `C[i₀, j] + price[j]`. -/
def findBestProg (d : ScanRowArgs) : Memory.Prog BestState :=
  iterate findBestStep d d.n ⟨0, 0, 0⟩

/-- Word-width safety predicate for `findBestProg`. -/
def FindBestSafe (w : ℕ) (d : ScanRowArgs) (s : Memory.State) : Prop :=
  iterationSafe findBestStep FindBestStepSafe w d d.n ⟨0, 0, 0⟩ s

/-- `realize` certificate for `findBestProg`. -/
theorem findBestProg_realizes :
    Realizes .exact findBestProg encScanRowArgs encBestState FindBestSafe (fun _ _ => 0) := by
  unfold findBestProg
  realize [findBestStep_realizes]
  exact h

/-- Specification of `findBestProg`: preserves memory, costs at most `2 * ws.n`, and yields the
exact `bestObject` index and value matching the pure `Auction` model. -/
theorem findBest_spec {w W : ℕ} (ws : AuctionWS) {C : Fin ws.n × Fin ws.n → ℕ}
    {st : AuctionState ws.n} (s₀ : Memory.State) (hws : ValidWS ws s₀)
    (ham : AuctionMem ws C st s₀)
    (hC_le : ∀ i j : Fin ws.n, C (i, j) ≤ W)
    (hp_nn : ∀ j : Fin ws.n, 0 ≤ st.price j)
    (hp_le : ∀ j : Fin ws.n, st.price j ≤ (W + ws.eps : ℤ))
    (i₀ : Fin ws.n)
    (hfit1 : Fits w 1) (hfit_ws : Fits w (ws.outBase + ws.n + 1))
    (hfit_rc : Fits w (2 * W + ws.eps)) :
    let rowBase := ws.bC + i₀.val * ws.n
    let d : ScanRowArgs := ⟨ws.n, rowBase, ws.bPrice⟩
    let prog := findBestProg d
    let res := (Memory.spec 0).clientResult s₀ prog
    FindBestSafe w d s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
      memoryCost prog s₀ ≤ 2 * ws.n ∧
      (Memory.spec 0).clientState s₀ prog = s₀ ∧
      ∃ j₀ : Fin ws.n,
        bestObject (fun e => (C e : ℤ)) st.price i₀ = some j₀ ∧
        (∀ k : Fin ws.n,
          redCost (fun e => (C e : ℤ)) st.price i₀ j₀ ≤
            redCost (fun e => (C e : ℤ)) st.price i₀ k) ∧
        res.bestJ = j₀.val ∧
        (res.bestVal : ℤ) = redCost (fun e => (C e : ℤ)) st.price i₀ j₀ := by
  have outputFits : Fits w ws.outBase := hfit_ws.of_le (by omega)
  have outputAllocated : ws.outBase ≤ s₀.frontier := Nat.le_trans (by omega) hws.hfrontier
  let rowBase := ws.bC + i₀.val * ws.n
  let d : ScanRowArgs := ⟨ws.n, rowBase, ws.bPrice⟩
  have hn_pos : 0 < ws.n := Nat.zero_lt_of_lt i₀.isLt
  have hit := iterate_spec findBestStep FindBestStepSafe w d 2 ws.n
    (fun k b s => s = s₀ ∧ b.idx = k ∧
      (k = 0 ∨ ∃ j₀ : Fin ws.n, j₀.val < k ∧
        ((List.finRange ws.n).take k).argmin (redCost (fun e => (C e : ℤ)) st.price i₀) = some j₀ ∧
        b.bestJ = j₀.val ∧ (b.bestVal : ℤ) = redCost (fun e => (C e : ℤ)) st.price i₀ j₀))
    (fun _ => False)
    (fun k hk b s ⟨hs, hbidx, harg⟩ => by
      subst s
      subst hbidx
      let jk : Fin ws.n := ⟨b.idx, hk⟩
      obtain ⟨hrow, hprice⟩ := rowReads_before_output hws i₀ jk
      obtain ⟨hrc_le, hrc_z⟩ := ham.redCost_read hC_le hp_nn hp_le i₀ jk
      have hsafe : FindBestStepSafe w (d, b) s₀ :=
        ⟨hfit1, outputFits.of_le hrow.le, outputFits.of_le hprice.le,
          hfit_rc.of_le hrc_le, hfit_ws.of_le (by have := jk.isLt; lia)⟩
      obtain ⟨hv, hmc, hst_eq, hres⟩ :=
        scanCell_spec (w := w) (s := s₀) (cost := d.rowBase + b.idx) (price := d.bPrice + b.idx)
          (bestNext b) (hrow.trans_le outputAllocated) (hprice.trans_le outputAllocated)
      refine ⟨hsafe, hv, hmc.le, by rw [findBestStep, hst_eq],
        fun _ _ => by rw [findBestStep, hst_eq], hst_eq, ?_⟩
      rw [findBestStep, hres]
      dsimp only [d, bestNext]
      by_cases hk0 : b.idx = 0
      · rw [hk0, ite_eq_left rfl]
        exact ⟨rfl, Or.inr ⟨⟨0, hn_pos⟩, Nat.one_pos,
          by simp [List.take_succ_finRange hn_pos], rfl,
          by simpa only [jk, hk0] using hrc_z⟩⟩
      · rw [ite_eq_right hk0]
        rcases harg with h0 | ⟨j₀, hj₀_lt, htake, hbj, hbv⟩
        · omega
        · by_cases hlt : s₀.mem (rowBase + b.idx) + s₀.mem (ws.bPrice + b.idx) < b.bestVal
          · rw [ite_eq_left hlt]
            refine ⟨rfl, Or.inr ⟨jk, Nat.lt_succ_self _, ?_, rfl, hrc_z⟩⟩
            rw [List.take_succ_finRange hk, List.argmin_concat, htake]
            exact ite_eq_left (hrc_z.symm.trans_lt ((Nat.cast_lt.mpr hlt).trans_eq hbv))
          · rw [ite_eq_right hlt]
            refine ⟨rfl, Or.inr ⟨j₀, Nat.lt_succ_of_lt hj₀_lt, ?_, hbj, hbv⟩⟩
            rw [List.take_succ_finRange hk, List.argmin_concat, htake]
            exact ite_eq_right fun hz =>
              hlt (Nat.cast_lt.mp (hrc_z.trans_lt (hz.trans_eq hbv.symm))))
    ⟨0, 0, 0⟩ s₀ ⟨rfl, rfl, Or.inl rfl⟩
  rcases hit with ⟨hsafe, hv, hmc, _, _, hs_eq, _, h0 | ⟨j₀, _, htake, hbj, hbv⟩⟩
  · omega
  · rw [List.take_of_length_le (by simp)] at htake
    exact ⟨hsafe, hv, hmc, hs_eq, j₀, htake,
      fun k => List.le_of_mem_argmin (List.mem_finRange k) htake, hbj, hbv⟩

end

/-! ### Row scan 2: second-best reduced cost (`findSecondProg`) -/

private def secondNext (bestJ : ℕ) (st : SecondState) (rc : ℕ) : SecondState :=
  if st.idx = bestJ then ⟨st.idx + 1, st.hasSecond, st.secondVal⟩
  else if st.hasSecond = 0 then ⟨st.idx + 1, 1, rc⟩
  else if rc < st.secondVal then ⟨st.idx + 1, 1, rc⟩
  else ⟨st.idx + 1, st.hasSecond, st.secondVal⟩

private def findSecondStep (x : ScanSecondArgs × SecondState) : Memory.Prog SecondState :=
  scanCell (x.1.rowBase + x.2.idx) (x.1.bPrice + x.2.idx) (secondNext x.1.bestJ x.2)

private abbrev FindSecondStepSafe (w : ℕ) (x : ScanSecondArgs × SecondState)
    (s : Memory.State) : Prop :=
  let d := x.1
  let st := x.2
  Fits w 1 ∧ Fits w (d.rowBase + st.idx) ∧ Fits w (d.bPrice + st.idx) ∧
    Fits w (s.mem (d.rowBase + st.idx) + s.mem (d.bPrice + st.idx)) ∧ Fits w (st.idx + 1)

private theorem findSecondStep_realizes :
    Realizes .exact findSecondStep (appendWords encScanSecondArgs encSecondState) encSecondState
      FindSecondStepSafe (fun _ _ => 0) := by
  unfold findSecondStep scanCell secondNext
  simp only [apply_ite (pure : SecondState → Memory.Prog SecondState)]
  realize
  all_goals
    rcases h with ⟨_, _, _, _, _⟩
    assumption

public section

/-- Scan a row of length `d.n` skipping `d.bestJ` to compute the second-least reduced cost. -/
def findSecondProg (d : ScanSecondArgs) : Memory.Prog SecondState :=
  iterate findSecondStep d d.n ⟨0, 0, 0⟩

/-- Word-width safety predicate for `findSecondProg`. -/
def FindSecondSafe (w : ℕ) (d : ScanSecondArgs) (s : Memory.State) : Prop :=
  iterationSafe findSecondStep FindSecondStepSafe w d d.n ⟨0, 0, 0⟩ s

/-- `realize` certificate for `findSecondProg`. -/
theorem findSecondProg_realizes :
    Realizes .exact findSecondProg encScanSecondArgs encSecondState
      FindSecondSafe (fun _ _ => 0) := by
  unfold findSecondProg
  realize [findSecondStep_realizes]
  exact h

/-- Specification of `findSecondProg`: preserves memory, costs at most `2 * ws.n`, and matches
`secondBest` in the pure `Auction` model. -/
theorem findSecond_spec {w W : ℕ} (ws : AuctionWS) {C : Fin ws.n × Fin ws.n → ℕ}
    {st : AuctionState ws.n} (s₀ : Memory.State) (hws : ValidWS ws s₀)
    (ham : AuctionMem ws C st s₀)
    (hC_le : ∀ i j : Fin ws.n, C (i, j) ≤ W)
    (hp_nn : ∀ j : Fin ws.n, 0 ≤ st.price j)
    (hp_le : ∀ j : Fin ws.n, st.price j ≤ (W + ws.eps : ℤ))
    (i₀ j₀ : Fin ws.n)
    (hfit1 : Fits w 1) (hfit_ws : Fits w (ws.outBase + ws.n + 1))
    (hfit_rc : Fits w (2 * W + ws.eps)) :
    let rowBase := ws.bC + i₀.val * ws.n
    let d : ScanSecondArgs := ⟨ws.n, rowBase, ws.bPrice, j₀.val⟩
    let prog := findSecondProg d
    let res := (Memory.spec 0).clientResult s₀ prog
    FindSecondSafe w d s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
      memoryCost prog s₀ ≤ 2 * ws.n ∧
      (Memory.spec 0).clientState s₀ prog = s₀ ∧
      match secondBest (fun e => (C e : ℤ)) st.price i₀ j₀ with
      | none => res.hasSecond = 0
      | some wVal =>
        res.hasSecond = 1 ∧ (res.secondVal : ℤ) = wVal ∧ res.secondVal ≤ 2 * W + ws.eps := by
  have outputFits : Fits w ws.outBase := hfit_ws.of_le (by omega)
  have outputAllocated : ws.outBase ≤ s₀.frontier := Nat.le_trans (by omega) hws.hfrontier
  let cZ : Fin ws.n × Fin ws.n → ℤ := fun e => (C e : ℤ)
  let rowBase := ws.bC + i₀.val * ws.n
  let d : ScanSecondArgs := ⟨ws.n, rowBase, ws.bPrice, j₀.val⟩
  let prefList (k : ℕ) : List ℤ :=
    (((List.finRange ws.n).take k).filter fun k' => decide (k' ≠ j₀)).map (redCost cZ st.price i₀)
  have hit := iterate_spec findSecondStep FindSecondStepSafe w d 2 ws.n
    (fun k b s => s = s₀ ∧ b.idx = k ∧
      match (prefList k).min? with
      | none => b.hasSecond = 0
      | some wVal => b.hasSecond = 1 ∧ (b.secondVal : ℤ) = wVal ∧ b.secondVal ≤ 2 * W + ws.eps)
    (fun _ => False)
    (fun k hk b s ⟨hs, hbidx, hmin⟩ => by
      subst s; subst hbidx
      let jk : Fin ws.n := ⟨b.idx, hk⟩
      obtain ⟨hrow, hprice⟩ := rowReads_before_output hws i₀ jk
      obtain ⟨hrc_le, hrc_z⟩ := ham.redCost_read hC_le hp_nn hp_le i₀ jk
      have hsafe : FindSecondStepSafe w (d, b) s₀ :=
        ⟨hfit1, outputFits.of_le hrow.le, outputFits.of_le hprice.le,
          hfit_rc.of_le hrc_le, hfit_ws.of_le (by have := jk.isLt; lia)⟩
      obtain ⟨hv, hmc, hst_eq, hres⟩ :=
        scanCell_spec (w := w) (s := s₀) (cost := d.rowBase + b.idx) (price := d.bPrice + b.idx)
          (secondNext d.bestJ b) (hrow.trans_le outputAllocated) (hprice.trans_le outputAllocated)
      refine ⟨hsafe, hv, hmc.le, by rw [findSecondStep, hst_eq],
        fun _ _ => by rw [findSecondStep, hst_eq], hst_eq, ?_⟩
      rw [findSecondStep, hres]
      dsimp only [d, secondNext]
      by_cases heq_j : b.idx = j₀.val
      · have hjk_eq : jk = j₀ := Fin.ext heq_j
        have hpref_eq : prefList (b.idx + 1) = prefList b.idx := by
          simp [prefList, List.take_succ_finRange hk, List.filter_append, jk, hjk_eq]
        rw [ite_eq_left heq_j]
        exact ⟨rfl, hpref_eq.symm ▸ hmin⟩
      · have hjk_ne : jk ≠ j₀ := fun e => heq_j (congrArg Fin.val e)
        have hpref_eq : prefList (b.idx + 1) = prefList b.idx ++ [redCost cZ st.price i₀ jk] := by
          simp [prefList, List.take_succ_finRange hk, List.filter_append, jk, hjk_ne]
        rw [ite_eq_right heq_j]
        rcases hl_prev : prefList b.idx with _ | ⟨hd_prev, tl_prev⟩
        · rw [hl_prev] at hmin hpref_eq
          dsimp only [List.min?] at hmin
          rw [ite_eq_left hmin, hpref_eq, List.nil_append, List.min?_singleton]
          exact ⟨rfl, rfl, hrc_z, hrc_le⟩
        · let wPrev := tl_prev.foldl min hd_prev
          rw [hl_prev, List.min?_cons'] at hmin
          obtain ⟨hhs1, hsv_z, hsv_le⟩ := hmin
          rw [ite_eq_right (ne_of_eq_of_ne hhs1 Nat.one_ne_zero), hpref_eq, hl_prev,
            List.cons_append, List.min?_cons', List.foldl_append, List.foldl_cons, List.foldl_nil]
          by_cases hlt : s₀.mem (rowBase + b.idx) + s₀.mem (ws.bPrice + b.idx) < b.secondVal
          · have hlt_z : redCost cZ st.price i₀ jk < wPrev :=
              hrc_z.symm.trans_lt ((Nat.cast_lt.mpr hlt).trans_eq hsv_z)
            rw [ite_eq_left hlt, min_eq_right hlt_z.le]
            exact ⟨rfl, rfl, hrc_z, hrc_le⟩
          · have hle_z : wPrev ≤ redCost cZ st.price i₀ jk :=
              not_lt.mp fun hz => hlt (Nat.cast_lt.mp (hrc_z.trans_lt (hz.trans_eq hsv_z.symm)))
            rw [ite_eq_right hlt, min_eq_left hle_z]
            exact ⟨rfl, hhs1, hsv_z, hsv_le⟩)
    ⟨0, 0, 0⟩ s₀ ⟨rfl, rfl, by simp [prefList]⟩
  obtain ⟨hsafe, hv, hmc, _, _, hs_eq, _, hfinal⟩ := hit
  refine ⟨hsafe, hv, hmc, hs_eq, ?_⟩
  simpa only [cZ, d, rowBase, findSecondProg, prefList, secondBest,
    List.take_of_length_le List.length_finRange.le] using hfinal

end

end Cslib.Algorithms.WordRAM.Auction
