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
open StateTransitionSpec (clientResult_pure clientState_pure)

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

/-! ### Row scan 1: best object (`findBestProg`) -/

private def findBestStep (x : ScanRowArgs × BestState) : Memory.Prog BestState := do
  let d := x.1
  let st := x.2
  let cij ← Memory.read (d.rowBase + st.idx)
  let pj ← Memory.read (d.bPrice + st.idx)
  let rc := cij + pj
  if st.idx = 0 then
    pure ⟨1, 0, rc⟩
  else if rc < st.bestVal then
    pure ⟨st.idx + 1, st.idx, rc⟩
  else
    pure ⟨st.idx + 1, st.bestJ, st.bestVal⟩

private abbrev FindBestStepSafe (w : ℕ) (x : ScanRowArgs × BestState) (s : Memory.State) : Prop :=
  let d := x.1
  let st := x.2
  Fits w 1 ∧ Fits w (d.rowBase + st.idx) ∧ Fits w (d.bPrice + st.idx) ∧
    Fits w (s.mem (d.rowBase + st.idx) + s.mem (d.bPrice + st.idx)) ∧ Fits w (st.idx + 1)

private theorem findBestStep_realizes :
    Realizes .exact findBestStep (appendWords encScanRowArgs encBestState) encBestState
      FindBestStepSafe (fun _ _ => 0) := by
  unfold findBestStep
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
  obtain ⟨hbO, hbP, hbS, hout, hfr⟩ := hws
  let cZ : Fin ws.n × Fin ws.n → ℤ := fun e => (C e : ℤ)
  let rowBase := ws.bC + i₀.val * ws.n
  let d : ScanRowArgs := ⟨ws.n, rowBase, ws.bPrice⟩
  have hn_pos : 0 < ws.n := Nat.zero_lt_of_lt i₀.isLt
  have hit := iterate_spec findBestStep FindBestStepSafe w d 2 ws.n
    (fun k b s => s = s₀ ∧ b.idx = k ∧
      (k = 0 ∨ ∃ j₀ : Fin ws.n, j₀.val < k ∧
        ((List.finRange ws.n).take k).argmin (redCost cZ st.price i₀) = some j₀ ∧
        b.bestJ = j₀.val ∧ (b.bestVal : ℤ) = redCost cZ st.price i₀ j₀))
    (fun _ => False)
    (fun k hk b s ⟨hs, hbidx, harg⟩ => by
      subst s
      have hk' : b.idx < ws.n := hbidx ▸ hk
      let jk : Fin ws.n := ⟨b.idx, hk'⟩
      have hmul_k : i₀.val * ws.n + b.idx < ws.n * ws.n := Cslib.Matrix.pairIndex_lt (i₀, jk)
      obtain ⟨hrc_le, hrc_z⟩ := ham.redCost_read hC_le hp_nn hp_le i₀ jk
      have hsafe : FindBestStepSafe w (d, b) s₀ := by
        dsimp only [FindBestStepSafe, d]
        exact ⟨hfit1, hfit_ws.of_le (by dsimp only [rowBase]; omega),
          hfit_ws.of_le (by omega), hfit_rc.of_le hrc_le, hfit_ws.of_le (by omega)⟩
      have hv : (Memory.spec w).ValidHistory s₀
          ((Memory.spec w).clientHistory s₀ (findBestStep (d, b))) := by
        unfold findBestStep
        dsimp only [d]
        exact validHistory_read_bind (by dsimp only [rowBase]; omega)
          (validHistory_read_bind (by omega)
            (validHistory_ite (fun _ => validHistory_pure w _ _)
              (fun _ => validHistory_ite (fun _ => validHistory_pure w _ _)
                (fun _ => validHistory_pure w _ _))))
      have hmc : memoryCost (findBestStep (d, b)) s₀ ≤ 2 := by
        unfold findBestStep
        exact memoryCost_read_bind_le fun _ _ =>
          memoryCost_read_bind_le fun _ _ =>
            memoryCost_ite_le (Nat.le_refl 0)
              (memoryCost_ite_le (Nat.le_refl 0) (Nat.le_refl 0))
      have hst_eq : (Memory.spec 0).clientState s₀ (findBestStep (d, b)) = s₀ := by
        unfold findBestStep
        rw [clientState_bind_read, clientState_bind_read]
        dsimp only
        split_ifs <;> exact clientState_pure _ _
      refine ⟨hsafe, hv, hmc, by rw [hst_eq], fun _ _ => by rw [hst_eq], hst_eq, ?_⟩
      unfold findBestStep
      rw [clientResult_bind_read, clientResult_bind_read]
      dsimp only [d]
      by_cases hk0 : b.idx = 0
      · have hk_zero : k = 0 := by omega
        subst hk_zero
        have hjk0 : jk = ⟨0, hn_pos⟩ := Fin.ext hk0
        rw [ite_eq_left hk0, clientResult_pure]
        dsimp only
        refine ⟨rfl, Or.inr ⟨⟨0, hn_pos⟩, Nat.one_pos, ?_, rfl, ?_⟩⟩
        · rw [show (1 : ℕ) = 0 + 1 from rfl, List.take_succ_finRange hn_pos, List.take_zero,
            List.nil_append]
          rfl
        · rw [← hjk0]
          simpa only [jk, hk0] using hrc_z
      · rw [ite_eq_right hk0]
        rcases harg with h0 | ⟨j₀, hj₀_lt, htake, hbj, hbv⟩
        · omega
        · subst hbidx
          by_cases hlt : s₀.mem (rowBase + b.idx) + s₀.mem (ws.bPrice + b.idx) < b.bestVal
          · rw [ite_eq_left hlt, clientResult_pure]
            refine ⟨rfl, Or.inr ⟨jk, Nat.lt_succ_self _, ?_, rfl, hrc_z⟩⟩
            rw [List.take_succ_finRange hk', List.argmin_concat, htake]
            exact ite_eq_left (hrc_z.symm.trans_lt ((Nat.cast_lt.mpr hlt).trans_eq hbv))
          · rw [ite_eq_right hlt, clientResult_pure]
            refine ⟨rfl, Or.inr ⟨j₀, Nat.lt_succ_of_lt hj₀_lt, ?_, hbj, hbv⟩⟩
            rw [List.take_succ_finRange hk', List.argmin_concat, htake]
            exact ite_eq_right fun hz =>
              hlt (Nat.cast_lt.mp (hrc_z.trans_lt (hz.trans_eq hbv.symm))))
    ⟨0, 0, 0⟩ s₀ ⟨rfl, rfl, Or.inl rfl⟩
  obtain ⟨hsafe, hv, hmc, _, _, hs_eq, _, hfinal⟩ := hit
  rcases hfinal with h0 | ⟨j₀, _, htake, hbj, hbv⟩
  · omega
  · rw [List.take_of_length_le (by simp)] at htake
    exact ⟨hsafe, hv, hmc, hs_eq, j₀, htake,
      fun k => List.le_of_mem_argmin (List.mem_finRange k) htake, hbj, hbv⟩

end

/-! ### Row scan 2: second-best reduced cost (`findSecondProg`) -/

private def findSecondStep (x : ScanSecondArgs × SecondState) : Memory.Prog SecondState := do
  let d := x.1
  let st := x.2
  let cij ← Memory.read (d.rowBase + st.idx)
  let pj ← Memory.read (d.bPrice + st.idx)
  let rc := cij + pj
  if st.idx = d.bestJ then
    pure ⟨st.idx + 1, st.hasSecond, st.secondVal⟩
  else if st.hasSecond = 0 then
    pure ⟨st.idx + 1, 1, rc⟩
  else if rc < st.secondVal then
    pure ⟨st.idx + 1, 1, rc⟩
  else
    pure ⟨st.idx + 1, st.hasSecond, st.secondVal⟩

private abbrev FindSecondStepSafe (w : ℕ) (x : ScanSecondArgs × SecondState)
    (s : Memory.State) : Prop :=
  let d := x.1
  let st := x.2
  Fits w 1 ∧ Fits w (d.rowBase + st.idx) ∧ Fits w (d.bPrice + st.idx) ∧
    Fits w (s.mem (d.rowBase + st.idx) + s.mem (d.bPrice + st.idx)) ∧ Fits w (st.idx + 1)

private theorem findSecondStep_realizes :
    Realizes .exact findSecondStep (appendWords encScanSecondArgs encSecondState) encSecondState
      FindSecondStepSafe (fun _ _ => 0) := by
  unfold findSecondStep
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
  obtain ⟨hbO, hbP, hbS, hout, hfr⟩ := hws
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
      have hmul_k : i₀.val * ws.n + b.idx < ws.n * ws.n := Cslib.Matrix.pairIndex_lt (i₀, jk)
      obtain ⟨hrc_le, hrc_z⟩ := ham.redCost_read hC_le hp_nn hp_le i₀ jk
      have hsafe : FindSecondStepSafe w (d, b) s₀ := by
        dsimp only [FindSecondStepSafe, d]
        exact ⟨hfit1, hfit_ws.of_le (by dsimp only [rowBase]; omega),
          hfit_ws.of_le (by omega), hfit_rc.of_le hrc_le, hfit_ws.of_le (by omega)⟩
      have hv : (Memory.spec w).ValidHistory s₀
          ((Memory.spec w).clientHistory s₀ (findSecondStep (d, b))) := by
        unfold findSecondStep
        dsimp only [d]
        exact validHistory_read_bind (by dsimp only [rowBase]; omega)
          (validHistory_read_bind (by omega)
            (validHistory_ite (fun _ => validHistory_pure w _ _)
              (fun _ => validHistory_ite (fun _ => validHistory_pure w _ _)
                (fun _ => validHistory_ite (fun _ => validHistory_pure w _ _)
                  (fun _ => validHistory_pure w _ _)))))
      have hmc : memoryCost (findSecondStep (d, b)) s₀ ≤ 2 := by
        unfold findSecondStep
        exact memoryCost_read_bind_le fun _ _ =>
          memoryCost_read_bind_le fun _ _ =>
            memoryCost_ite_le (Nat.le_refl 0)
              (memoryCost_ite_le (Nat.le_refl 0)
                (memoryCost_ite_le (Nat.le_refl 0) (Nat.le_refl 0)))
      have hst_eq : (Memory.spec 0).clientState s₀ (findSecondStep (d, b)) = s₀ := by
        unfold findSecondStep
        rw [clientState_bind_read, clientState_bind_read]
        dsimp only
        split_ifs <;> exact clientState_pure _ _
      refine ⟨hsafe, hv, hmc, by rw [hst_eq], fun _ _ => by rw [hst_eq], hst_eq, ?_⟩
      unfold findSecondStep
      rw [clientResult_bind_read, clientResult_bind_read]
      dsimp only [d]
      by_cases heq_j : b.idx = j₀.val
      · have hjk_eq : jk = j₀ := Fin.ext heq_j
        have hpref_eq : prefList (b.idx + 1) = prefList b.idx := by
          dsimp only [prefList]
          rw [List.take_succ_finRange hk, List.filter_append, List.map_append]
          simp [jk, hjk_eq]
        rw [ite_eq_left heq_j, clientResult_pure]
        dsimp only
        refine ⟨rfl, ?_⟩
        simpa only [hpref_eq] using hmin
      · have hjk_ne : jk ≠ j₀ := fun e => heq_j (congrArg Fin.val e)
        have hpref_eq : prefList (b.idx + 1) = prefList b.idx ++ [redCost cZ st.price i₀ jk] := by
          dsimp only [prefList]
          rw [List.take_succ_finRange hk, List.filter_append, List.map_append]
          simp [jk, hjk_ne]
        rw [ite_eq_right heq_j]
        rcases hl_prev : prefList b.idx with _ | ⟨hd_prev, tl_prev⟩
        · rw [hl_prev] at hmin hpref_eq
          dsimp only [List.min?] at hmin
          rw [ite_eq_left hmin, clientResult_pure]
          dsimp only
          refine ⟨rfl, ?_⟩
          rw [hpref_eq, List.nil_append, List.min?_singleton]
          exact ⟨rfl, hrc_z, hrc_le⟩
        · have hm_some : (hd_prev :: tl_prev).min? = some (tl_prev.foldl min hd_prev) := rfl
          let wPrev := tl_prev.foldl min hd_prev
          rw [hl_prev, hm_some] at hmin
          obtain ⟨hhs1, hsv_z, hsv_le⟩ := hmin
          have hhs_ne : b.hasSecond ≠ 0 := by omega
          rw [ite_eq_right hhs_ne]
          have hmin_app : (prefList (b.idx + 1)).min? =
              some (min wPrev (redCost cZ st.price i₀ jk)) := by
            rw [hpref_eq, hl_prev, List.cons_append, List.min?_cons', List.foldl_append,
              List.foldl_cons, List.foldl_nil]
          rw [hmin_app]
          by_cases hlt : s₀.mem (rowBase + b.idx) + s₀.mem (ws.bPrice + b.idx) < b.secondVal
          · have hlt_z : redCost cZ st.price i₀ jk < wPrev :=
              hrc_z.symm.trans_lt ((Nat.cast_lt.mpr hlt).trans_eq hsv_z)
            rw [ite_eq_left hlt, clientResult_pure, min_eq_right hlt_z.le]
            exact ⟨rfl, rfl, hrc_z, hrc_le⟩
          · have hle_z : wPrev ≤ redCost cZ st.price i₀ jk :=
              not_lt.mp fun hz => hlt (Nat.cast_lt.mp (hrc_z.trans_lt (hz.trans_eq hsv_z.symm)))
            rw [ite_eq_right hlt, clientResult_pure, min_eq_left hle_z]
            exact ⟨rfl, hhs1, hsv_z, hsv_le⟩)
    ⟨0, 0, 0⟩ s₀ ⟨rfl, rfl, by simp [prefList]⟩
  obtain ⟨hsafe, hv, hmc, _, _, hs_eq, _, hfinal⟩ := hit
  have hpref_n : (prefList ws.n).min? = secondBest cZ st.price i₀ j₀ := by
    dsimp only [prefList, secondBest]
    rw [List.take_of_length_le (by simp)]
  rw [hpref_n] at hfinal
  exact ⟨hsafe, hv, hmc, hs_eq, hfinal⟩

end

end Cslib.Algorithms.WordRAM.Auction
