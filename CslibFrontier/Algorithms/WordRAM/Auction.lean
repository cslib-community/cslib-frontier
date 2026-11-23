/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Assignment.Auction
public import CslibFrontier.Computability.WordRAM.ListOutput
public import CslibFrontier.Computability.WordRAM.Signed.Encoding
import CslibFrontier.Computability.WordRAM.InputArray
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontier.Computability.WordRAM.Realization.Structure
import CslibFrontier.Computability.WordRAM.Realization.WhileAbsorb
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Foundations.Data.Matrix.PairChunks
import CslibFrontier.Tactic.Realize
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# Bertsekas's auction algorithm on the word RAM

This file implements and proves machine-level running-time bounds on the standard-basis word RAM
(`Basis.standard`) for Bertsekas's Gauss–Seidel `ε`-auction algorithm
(`Cslib.Algorithms.Lean.Assignment.auction` and `Cslib.Algorithms.Lean.Assignment.scaledAuction`),
using the memory-oracle refinement framework (`Memory.Prog` and `realize`):

1. **Private `Memory.Prog` auction refinement.** Given an `n × n` unsigned cost matrix bounded by
   `W` in workspace memory and a positive integer increment `ε > 0`, the memory client maintains
   `owner[0..n)`, nonnegative integer prices `price[0..n)`, and a reversed unassigned-person stack
   `stack[0..sp)` in `O(1)` memory operations per push/pop and `O(n)` memory operations per bid.
   By `AuctionInv.price_le` and `price_nonneg_bidStep`, active prices stay in `[0, W + ε]` and
   reduced costs stay in `[0, 2 W + ε]`, so unsigned bid updates never underflow or overflow.
2. **Unscaled `ε`-auction (`EpsInstance`, `exists_epsAuction_program`).** Scans the signed input
   costs for an entry magnitude bound `M ≤ inst.maxMag`, shifts every entry by `+ M` into
   `[0, 2 M]` (preserving the bid trajectory by `auction_add_const`), runs the memory-client
   auction, and scatters the permutation `auctionPerm` to length-prefixed output memory in
   `O(n² (C / ε + 1))` instructions ([Bertsekas1988], §1) whenever `C` bounds the row cost ranges
   (`inst.rowSpread` unconditionally) and `Fits w inst.wordBound` (`w = O(log n + log M + log ε)`).
3. **Exact `(n + 1)`-scaled integer auction (`Instance`, `exists_scaledAuction_program`,
   `exists_scaledMinCost_program`).** Scales shifted costs by `n + 1` with `ε = 1`
   ([Bertsekas1988], §3), computing the exact minimum-cost assignment `scaledAuctionPerm`
   (`sum_scaledAuctionPerm_le`) and `Signed.encode` of its minimum cost in `O(n³ C + n²)`
   instructions at logarithmic word width `Fits w inst.wordBound` (`w = O(log n + log M)`).

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
open Cslib.Algorithms.Lean.Assignment
open StateTransitionSpec (clientResult_bind clientState_bind clientResult_pure clientState_pure)

/-! ## Section 1: Problem instances and encodings -/

public section

/-- Problem instance for exact minimum-cost integer assignment via Bertsekas's `(n + 1)`-scaled
auction (`scaledAuction`, `ε = 1`). -/
structure Instance where
  /-- Common number of persons and objects. -/
  n : ℕ
  /-- Signed integer assignment cost `Fin n × Fin n → ℤ`. -/
  cost : Fin n × Fin n → ℤ

namespace Instance

/-- Maximum entry magnitude `max_{i, j} |cost (i, j)|` (`0` when `n = 0`). -/
@[expose] def maxMag (inst : Instance) : ℕ :=
  Finset.univ.sup fun p : Fin inst.n × Fin inst.n => (inst.cost p).natAbs

/-- Maximum within-row cost difference `max_{i, j, k} (cost (i, k) - cost (i, j))` (`0` when
`n = 0`). -/
@[expose] def rowSpread (inst : Instance) : ℕ :=
  Finset.univ.sup fun i : Fin inst.n =>
    Finset.univ.sup fun j : Fin inst.n =>
      Finset.univ.sup fun k : Fin inst.n =>
        (inst.cost (i, k) - inst.cost (i, j)).toNat

theorem natAbs_cost_le_maxMag (inst : Instance) (i j : Fin inst.n) :
    (inst.cost (i, j)).natAbs ≤ inst.maxMag :=
  Finset.le_sup (f := fun p : Fin inst.n × Fin inst.n => (inst.cost p).natAbs)
    (Finset.mem_univ (i, j))

theorem sub_le_rowSpread (inst : Instance) (i j k : Fin inst.n) :
    inst.cost (i, k) - inst.cost (i, j) ≤ (inst.rowSpread : ℤ) := by
  have hk : (inst.cost (i, k) - inst.cost (i, j)).toNat ≤
      Finset.univ.sup fun k' => (inst.cost (i, k') - inst.cost (i, j)).toNat :=
    Finset.le_sup (f := fun k' => (inst.cost (i, k') - inst.cost (i, j)).toNat)
      (Finset.mem_univ k)
  have hj : (Finset.univ.sup fun k' => (inst.cost (i, k') - inst.cost (i, j)).toNat) ≤
      Finset.univ.sup fun j' => Finset.univ.sup fun k' =>
        (inst.cost (i, k') - inst.cost (i, j')).toNat :=
    Finset.le_sup (f := fun j' => Finset.univ.sup fun k' =>
      (inst.cost (i, k') - inst.cost (i, j')).toNat) (Finset.mem_univ j)
  have hi : (Finset.univ.sup fun j' => Finset.univ.sup fun k' =>
      (inst.cost (i, k') - inst.cost (i, j')).toNat) ≤ inst.rowSpread :=
    Finset.le_sup (f := fun i' => Finset.univ.sup fun j' => Finset.univ.sup fun k' =>
      (inst.cost (i', k') - inst.cost (i', j')).toNat) (Finset.mem_univ i)
  exact (Int.self_le_toNat _).trans (Nat.cast_le.mpr (hk.trans (hj.trans hi)))

/-- Row-major word encoding `n :: matrixWords` (`1 + n * n` words). -/
@[expose] def encode (inst : Instance) : List ℕ :=
  inst.n :: (List.finRange inst.n).flatMap fun i =>
    (List.finRange inst.n).map fun j => Signed.encode (inst.cost (i, j))

/-- Word-value envelope covering input words, workspace addresses, `(n + 1)`-scaled shifted costs,
prices, reduced costs, and accumulated total assignment cost (`w = O(log n + log M)`). -/
@[expose] def wordBound (inst : Instance) : ℕ :=
  2 * (inst.n * inst.n) + 5 * inst.n + 4 * (inst.n + 1) * inst.maxMag + 10

/-- Optimal assignment list `[obj_0, …, obj_{n - 1}]` computed by `scaledAuction`
(`scaledAuctionPerm inst.cost`; optimal by `sum_scaledAuctionPerm_le`). -/
@[expose] def assignment (inst : Instance) : List ℕ :=
  (List.finRange inst.n).map fun i => (scaledAuctionPerm inst.cost i).val

/-- Minimum assignment cost `∑ i, inst.cost (i, scaledAuctionPerm inst.cost i)`. -/
@[expose] def minCost (inst : Instance) : ℤ :=
  ∑ i : Fin inst.n, inst.cost (i, scaledAuctionPerm inst.cost i)

/-- Minimum assignment cost encoded via `Signed.encode`. -/
@[expose] def encodedMinCost (inst : Instance) : ℕ :=
  Signed.encode inst.minCost

@[simp] theorem length_assignment (inst : Instance) : inst.assignment.length = inst.n := by
  simp [assignment]

theorem encode_length (inst : Instance) : inst.encode.length = 1 + inst.n * inst.n := by
  simp only [encode, List.length_cons, List.length_flatMap, List.length_map, List.length_finRange,
    List.map_const', List.sum_replicate, smul_eq_mul]
  omega

private theorem init_mem_cost (inst : Instance) (i j : Fin inst.n) :
    (Memory.State.init inst.encode).mem (2 + (i.val * inst.n + j.val)) =
      Signed.encode (inst.cost (i, j)) :=
  Data.init_mem_flatMap_finRange (r := 0) [inst.n]
    (fun i' j' => Signed.encode (inst.cost (i', j'))) i j

theorem inputFits_encode {w : ℕ} (inst : Instance) (hw : Fits w inst.wordBound) :
    InputFits w inst.encode :=
  InputFits.flatMap_finRange [inst.n] (fun i j => Signed.encode (inst.cost (i, j)))
    (hw.of_le (by unfold wordBound; dsimp only [List.length]; nlinarith))
    (by
      simp only [List.mem_singleton]
      rintro _ rfl
      exact hw.of_le (by unfold wordBound; nlinarith))
    (fun i j => hw.of_le ((Signed.encode_le_two_mul_add_one
      (inst.natAbs_cost_le_maxMag i j)).trans (by unfold wordBound; nlinarith)))

end Instance

/-- Problem instance for Bertsekas's Gauss–Seidel `ε`-auction on an `n × n` integer cost matrix. -/
structure EpsInstance where
  /-- Common number of persons and objects. -/
  n : ℕ
  /-- Bidding increment `ε` (admitted when `0 < eps`). -/
  eps : ℕ
  /-- Signed integer assignment cost `Fin n × Fin n → ℤ`. -/
  cost : Fin n × Fin n → ℤ

namespace EpsInstance

/-- Underlying `n × n` cost matrix instance. -/
abbrev toInstance (inst : EpsInstance) : Instance := ⟨inst.n, inst.cost⟩

/-- Maximum entry magnitude `max_{i, j} |cost (i, j)|` (`0` when `n = 0`). -/
abbrev maxMag (inst : EpsInstance) : ℕ := inst.toInstance.maxMag

/-- Maximum within-row cost difference `max_{i, j, k} (cost (i, k) - cost (i, j))` (`0` when
`n = 0`). -/
abbrev rowSpread (inst : EpsInstance) : ℕ := inst.toInstance.rowSpread

/-- Row-major word encoding `n :: eps :: matrixWords` (`2 + n * n` words). -/
@[expose] def encode (inst : EpsInstance) : List ℕ :=
  inst.n :: inst.eps :: inst.toInstance.encode.tail

/-- Word-value envelope covering input words, workspace addresses, shifted costs, reduced costs,
and object prices (`w = O(log n + log M + log ε)`). -/
@[expose] def wordBound (inst : EpsInstance) : ℕ :=
  2 * (inst.n * inst.n) + 5 * inst.n + 4 * inst.maxMag + 2 * inst.eps + 8

/-- Person-indexed assignment list `[obj_0, …, obj_{n - 1}]` computed by
`auction inst.cost inst.eps` (`auctionPerm` when `0 < inst.eps`; `n * eps`-optimal by
`sum_auctionPerm_le`). -/
@[expose] def assignment (inst : EpsInstance) : List ℕ :=
  (List.finRange inst.n).map fun i => ((auction inst.cost (inst.eps : ℤ)).objectOf i).val

@[simp] theorem length_assignment (inst : EpsInstance) : inst.assignment.length = inst.n := by
  simp [assignment]

theorem encode_length (inst : EpsInstance) : inst.encode.length = 2 + inst.n * inst.n := by
  have htail : inst.toInstance.encode.tail.length = inst.n * inst.n := by
    have := inst.toInstance.encode_length
    simp only [Instance.encode, List.length_cons] at this
    simp only [Instance.encode, List.tail_cons]
    omega
  simp only [encode, List.length_cons, htail]
  omega

private theorem init_mem_cost (inst : EpsInstance) (i j : Fin inst.n) :
    (Memory.State.init inst.encode).mem (3 + (i.val * inst.n + j.val)) =
      Signed.encode (inst.cost (i, j)) :=
  Data.init_mem_flatMap_finRange (r := 0) [inst.n, inst.eps]
    (fun i' j' => Signed.encode (inst.cost (i', j'))) i j

theorem inputFits_encode {w : ℕ} (inst : EpsInstance) (hw : Fits w inst.wordBound) :
    InputFits w inst.encode :=
  InputFits.flatMap_finRange [inst.n, inst.eps] (fun i j => Signed.encode (inst.cost (i, j)))
    (hw.of_le (by unfold wordBound; dsimp only [List.length]; nlinarith))
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl) <;> exact hw.of_le (by unfold wordBound; nlinarith))
    (fun i j => hw.of_le ((Signed.encode_le_two_mul_add_one
      (inst.toInstance.natAbs_cost_le_maxMag i j)).trans (by unfold wordBound; nlinarith)))

end EpsInstance

end

/-! ## Section 2: Private workspace and state records -/

/-- Private workspace layout and parameters for the memory-client auction solver. -/
private structure AuctionWS where
  /-- Common number of persons and objects. -/
  n : ℕ
  /-- Positive bidding increment `ε`. -/
  eps : ℕ
  /-- Cost scaling factor (`1` or `n + 1`). -/
  scale : ℕ
  /-- Scanned entry magnitude bound `M`. -/
  M : ℕ
  /-- Start address of encoded input matrix (`3` or `2`). -/
  matBase : ℕ
  /-- Base address of working unsigned `n × n` matrix `C[0..n*n)`. -/
  bC : ℕ
  /-- Base address of `owner[0..n)` (`n` denotes `none`, `i < n` denotes `some i`). -/
  bOwner : ℕ
  /-- Base address of nonnegative integer prices `price[0..n)`. -/
  bPrice : ℕ
  /-- Base address of reversed unassigned-person stack `stack[0..n)`. -/
  bStack : ℕ
  /-- Base address of length-prefixed output list (`n + 1` cells). -/
  outBase : ℕ

private word_enc_structure encAuctionWS : AuctionWS where
  n : wordWords,
  eps : wordWords,
  scale : wordWords,
  M : wordWords,
  matBase : wordWords,
  bC : wordWords,
  bOwner : wordWords,
  bPrice : wordWords,
  bStack : wordWords,
  outBase : wordWords

private instance : WordEncoding AuctionWS := ⟨10, encAuctionWS⟩

private structure ScanArgs where
  matBase : ℕ
  total : ℕ

private word_enc_structure encScanArgs : ScanArgs where
  matBase : wordWords, total : wordWords

private instance : WordEncoding ScanArgs := ⟨2, encScanArgs⟩

private structure ScanState where
  idx : ℕ
  curM : ℕ

private word_enc_structure encScanState : ScanState where
  idx : wordWords, curM : wordWords

private instance : WordEncoding ScanState := ⟨2, encScanState⟩

private structure ScanRowArgs where
  n : ℕ
  rowBase : ℕ
  bPrice : ℕ

private word_enc_structure encScanRowArgs : ScanRowArgs where
  n : wordWords, rowBase : wordWords, bPrice : wordWords

private instance : WordEncoding ScanRowArgs := ⟨3, encScanRowArgs⟩

private structure BestState where
  idx : ℕ
  bestJ : ℕ
  bestVal : ℕ

private word_enc_structure encBestState : BestState where
  idx : wordWords, bestJ : wordWords, bestVal : wordWords

private instance : WordEncoding BestState := ⟨3, encBestState⟩

private structure ScanSecondArgs where
  n : ℕ
  rowBase : ℕ
  bPrice : ℕ
  bestJ : ℕ

private word_enc_structure encScanSecondArgs : ScanSecondArgs where
  n : wordWords, rowBase : wordWords, bPrice : wordWords, bestJ : wordWords

private instance : WordEncoding ScanSecondArgs := ⟨4, encScanSecondArgs⟩

private structure SecondState where
  idx : ℕ
  hasSecond : ℕ
  secondVal : ℕ

private word_enc_structure encSecondState : SecondState where
  idx : wordWords, hasSecond : wordWords, secondVal : wordWords

private instance : WordEncoding SecondState := ⟨3, encSecondState⟩

private structure SumState where
  idx : ℕ
  acc : ℕ

private word_enc_structure encSumState : SumState where
  idx : wordWords, acc : wordWords

private instance : WordEncoding SumState := ⟨2, encSumState⟩

/-! ## Section 3: Memory-client subroutines, `realize` certificates, and simulations -/

/-! ### 3.1 Scanning input costs for `M ≤ maxMag` -/

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

private def scanMaxProg (d : ScanArgs) : Memory.Prog ℕ := do
  let res ← iterate scanMaxStep d d.total ⟨0, 0⟩
  pure res.curM

private theorem scanMaxProg_realizes :
    Realizes .exact scanMaxProg encScanArgs wordWords
      (fun w d s => iterationSafe scanMaxStep ScanMaxStepSafe w d d.total ⟨0, 0⟩ s)
      (fun _ _ => 0) := by
  unfold scanMaxProg
  realize [scanMaxStep_realizes]
  exact h

private theorem scanMaxProg_spec {w n matBase maxM : ℕ} {cost : Fin n × Fin n → ℤ}
    {s₀ : Memory.State}
    (hcost_mem : ∀ i j : Fin n,
      s₀.mem (matBase + (i.val * n + j.val)) = Signed.encode (cost (i, j)))
    (hmag : ∀ i j : Fin n, (cost (i, j)).natAbs ≤ maxM)
    (hfr : matBase + n * n ≤ s₀.frontier)
    (hfit2 : Fits w 2) (hfit_end : Fits w (matBase + n * n)) :
    let d : ScanArgs := ⟨matBase, n * n⟩
    let M := (Memory.spec 0).clientResult s₀ (scanMaxProg d)
    iterationSafe scanMaxStep ScanMaxStepSafe w d d.total ⟨0, 0⟩ s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (scanMaxProg d)) ∧
      memoryCost (scanMaxProg d) s₀ ≤ n * n ∧
      (Memory.spec 0).clientState s₀ (scanMaxProg d) = s₀ ∧
      M ≤ maxM ∧ ∀ i j : Fin n, (cost (i, j)).natAbs ≤ M := by
  let d : ScanArgs := ⟨matBase, n * n⟩
  have hit := iterate_spec scanMaxStep ScanMaxStepSafe w d 1 (n * n)
    (fun k st s => s = s₀ ∧ st.idx = k ∧ st.curM ≤ maxM ∧
      ∀ idx < k, s₀.mem (matBase + idx) / 2 ≤ st.curM)
    (fun _ => False)
    (fun k hk st s ⟨hs, hidx, hle, hprev⟩ => by
      subst s
      have hsafe : ScanMaxStepSafe w (d, st) s₀ :=
        ⟨hfit2, hfit_end.of_le (by dsimp only [d]; omega),
          hfit_end.of_le (by dsimp only [d]; omega)⟩
      have hv : (Memory.spec w).ValidHistory s₀
          ((Memory.spec w).clientHistory s₀ (scanMaxStep (d, st))) :=
        validHistory_read_bind (by dsimp only [d]; omega)
          (validHistory_ite (fun _ => validHistory_pure w _ _) (fun _ => validHistory_pure w _ _))
      have hmc : memoryCost (scanMaxStep (d, st)) s₀ ≤ 1 := by
        unfold scanMaxStep
        refine memoryCost_read_bind_le fun _ _ => ?_
        exact memoryCost_ite_le (Nat.le_refl 0) (Nat.le_refl 0)
      have hst_eq : (Memory.spec 0).clientState s₀ (scanMaxStep (d, st)) = s₀ := by
        unfold scanMaxStep
        rw [clientState_bind_read, prog_clientState_ite, clientState_pure, clientState_pure,
          ite_self]
      have hdiv_le : s₀.mem (matBase + st.idx) / 2 ≤ maxM := by
        have hn_pos : 0 < n := by by_contra h0; simp [Nat.eq_zero_of_not_pos h0] at hk
        have hlt_nn : st.idx < n * n := hidx ▸ hk
        let i : Fin n := ⟨st.idx / n, (Nat.div_lt_iff_lt_mul hn_pos).mpr hlt_nn⟩
        let j : Fin n := ⟨st.idx % n, Nat.mod_lt _ hn_pos⟩
        have hij : i.val * n + j.val = st.idx := by
          dsimp only [i, j]; rw [Nat.mul_comm, Nat.div_add_mod]
        rw [← hij, hcost_mem i j, Signed.encode_div_two]
        exact hmag i j
      refine ⟨hsafe, hv, hmc, by rw [hst_eq], fun _ _ => by rw [hst_eq], hst_eq, ?_⟩
      unfold scanMaxStep
      rw [clientResult_bind_read]
      dsimp only [d]
      by_cases hlt : st.curM < s₀.mem (matBase + st.idx) / 2
      · rw [ite_eq_left hlt, clientResult_pure]
        dsimp only
        refine ⟨by omega, hdiv_le, fun idx hidx_lt => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hidx_lt with hlt' | rfl
        · exact (hprev idx hlt').trans (le_of_lt hlt)
        · rw [← hidx]
      · rw [ite_eq_right hlt, clientResult_pure]
        dsimp only
        refine ⟨by omega, hle, fun idx hidx_lt => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hidx_lt with hlt' | rfl
        · exact hprev idx hlt'
        · rw [← hidx]; omega)
    ⟨0, 0⟩ s₀ ⟨rfl, rfl, Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hv_it, hmc_it, _, _, hs_eq, _, hM_le, hprev⟩ := hit
  dsimp only [d]
  unfold scanMaxProg
  refine ⟨hsafe, validHistory_bind_step hv_it (validHistory_pure w _ _), ?_, ?_, ?_, ?_⟩
  · rw [memoryCost_bind']
    have hp : memoryCost (pure ((Memory.spec 0).clientResult s₀
        (iterate scanMaxStep d (n * n) ⟨0, 0⟩)).curM : Memory.Prog ℕ)
        ((Memory.spec 0).clientState s₀ (iterate scanMaxStep d (n * n) ⟨0, 0⟩)) = 0 := rfl
    dsimp only [d] at hmc_it ⊢
    rw [hp]; omega
  · rw [clientState_bind, clientState_pure]
    exact hs_eq
  · rw [clientResult_bind, clientResult_pure]
    exact hM_le
  · intro i j
    rw [clientResult_bind, clientResult_pure]
    have hlt : i.val * n + j.val < n * n := Cslib.Matrix.pairIndex_lt (i, j)
    have h := hprev (i.val * n + j.val) hlt
    rwa [hcost_mem i j, Signed.encode_div_two] at h

/-! ### 3.2 Filling the shifted, scaled unsigned cost matrix -/

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

private def fillCProg (ws : AuctionWS) : Memory.Prog ℕ :=
  iterate fillCStep ws (ws.n * ws.n) 0

private abbrev FillCProgSafe (w : ℕ) (ws : AuctionWS) (s : Memory.State) : Prop :=
  Fits w (ws.n * ws.n) ∧ iterationSafe fillCStep FillCStepSafe w ws (ws.n * ws.n) 0 s

private theorem fillCProg_realizes :
    Realizes .exact fillCProg encAuctionWS wordWords FillCProgSafe (fun _ _ => 0) := by
  unfold fillCProg
  realize [fillCStep_realizes]
  all_goals
    rcases h with ⟨_, _⟩
    assumption

private theorem fillC_spec {w : ℕ} (ws : AuctionWS) {cost : Fin ws.n × Fin ws.n → ℤ}
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
  have hit := iterate_spec fillCStep FillCStepSafe w ws 2 (ws.n * ws.n)
    (fun k idx s => idx = k ∧ s.frontier = s₀.frontier ∧
      (∀ a < ws.bC, s.mem a = s₀.mem a) ∧
      ∀ i j : Fin ws.n, i.val * ws.n + j.val < k →
        s.mem (ws.bC + (i.val * ws.n + j.val)) =
          ws.scale * (cost (i, j) + (ws.M : ℤ)).toNat)
    (fun a => ws.bC ≤ a ∧ a < ws.bC + ws.n * ws.n)
    (fun k hk idx s ⟨hidx, hsfr, hlow, hfilled⟩ => by
      subst idx
      have hn_pos : 0 < ws.n := by by_contra h0; simp [Nat.eq_zero_of_not_pos h0] at hk
      let i₀ : Fin ws.n := ⟨k / ws.n, (Nat.div_lt_iff_lt_mul hn_pos).mpr hk⟩
      let j₀ : Fin ws.n := ⟨k % ws.n, Nat.mod_lt _ hn_pos⟩
      have hij₀ : i₀.val * ws.n + j₀.val = k := by
        dsimp only [i₀, j₀]; rw [Nat.mul_comm, Nat.div_add_mod]
      have hraw : s.mem (ws.matBase + k) = Signed.encode (cost (i₀, j₀)) := by
        rw [hlow _ (by omega), ← hij₀, hcost_mem i₀ j₀]
      have hmag_eq : s.mem (ws.matBase + k) / 2 = (cost (i₀, j₀)).natAbs := by
        rw [hraw, Signed.encode_div_two]
      have hmag_le : s.mem (ws.matBase + k) / 2 ≤ ws.M := hmag_eq.trans_le (hM_ge i₀ j₀)
      have hf_sc : Fits w (ws.scale * (ws.M + s.mem (ws.matBase + k) / 2)) :=
        hfit_val.of_le (Nat.mul_le_mul_left _ (by omega))
      have hf_add : Fits w (ws.M + s.mem (ws.matBase + k) / 2) :=
        hf_sc.of_le (Nat.le_mul_of_pos_left _ hsc)
      have hsafe : FillCStepSafe w (ws, k) s := by
        dsimp only [FillCStepSafe]
        exact ⟨hfit2, hfit_addr.of_le (by omega), hfit_addr.of_le (by omega),
          hfit_addr.of_le (by omega), hmag_le, hf_add, hf_sc⟩
      have hv : (Memory.spec w).ValidHistory s
          ((Memory.spec w).clientHistory s (fillCStep (ws, k))) := by
        unfold fillCStep
        dsimp only
        exact validHistory_read_bind (by omega)
          (validHistory_ite
            (fun _ => validHistory_write_bind (by omega) hf_sc (validHistory_pure w _ _))
            (fun _ => validHistory_write_bind (by omega)
              (hf_sc.of_le (Nat.mul_le_mul_left _ (by omega))) (validHistory_pure w _ _)))
      have hmc : memoryCost (fillCStep (ws, k)) s ≤ 2 := by
        unfold fillCStep
        refine memoryCost_read_bind_le fun _ _ => ?_
        exact memoryCost_ite_le
          (memoryCost_write_bind_le fun _ _ => Nat.le_refl 0)
          (memoryCost_write_bind_le fun _ _ => Nat.le_refl 0)
      let written :=
        if s.mem (ws.matBase + k) % 2 = 0 then
          ws.scale * (ws.M + s.mem (ws.matBase + k) / 2)
        else
          ws.scale * (ws.M - s.mem (ws.matBase + k) / 2)
      have hwritten : written = ws.scale * (cost (i₀, j₀) + (ws.M : ℤ)).toNat := by
        dsimp only [written]
        rw [hraw, Signed.encode_mod_two, Signed.encode_div_two]
        have hm := hM_ge i₀ j₀
        by_cases hneg : cost (i₀, j₀) < 0
        · simp only [hneg, ↓reduceIte, one_ne_zero]
          congr 1; omega
        · simp only [hneg, ↓reduceIte]
          congr 1; omega
      have hst_eq : (Memory.spec 0).clientState s (fillCStep (ws, k)) =
          ⟨Function.update s.mem (ws.bC + k) written, s.frontier⟩ := by
        unfold fillCStep
        rw [clientState_bind_read]
        dsimp only [written]
        split_ifs with hmod
        · rw [clientState_bind_write, clientState_pure]
        · rw [clientState_bind_write, clientState_pure]
      have hres_eq : (Memory.spec 0).clientResult s (fillCStep (ws, k)) = k + 1 := by
        unfold fillCStep
        rw [clientResult_bind_read]
        dsimp only
        split_ifs
        · rw [clientResult_bind_write, clientResult_pure]
        · rw [clientResult_bind_write, clientResult_pure]
      refine ⟨hsafe, hv, hmc, by rw [hst_eq], fun x hx => ?_, ?_⟩
      · rw [hst_eq]
        dsimp only
        exact Function.update_of_ne (by omega) _ _
      · rw [hst_eq, hres_eq]
        dsimp only
        refine ⟨rfl, hsfr, fun a ha => ?_, fun i j hij => ?_⟩
        · rw [Function.update_of_ne (by omega)]
          exact hlow a ha
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hij with hlt' | heq
          · rw [Function.update_of_ne (by omega)]
            exact hfilled i j hlt'
          · rw [heq, Function.update_self, hwritten]
            have hi_eq : i = i₀ := by
              ext; dsimp only [i₀]; rw [← heq, Nat.mul_comm i.val ws.n, Nat.mul_add_div hn_pos,
                Nat.div_eq_of_lt j.isLt, Nat.add_zero]
            have hj_eq : j = j₀ := by
              ext; dsimp only [j₀]; rw [← heq, Nat.mul_comm i.val ws.n, Nat.mul_add_mod,
                Nat.mod_eq_of_lt j.isLt]
            rw [hi_eq, hj_eq])
    0 s₀ ⟨rfl, rfl, fun _ _ => rfl, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hv, hmc, hfr', hmod, _, _, _, hfilled⟩ := hit
  exact ⟨⟨hfit_addr.of_le (by omega), hsafe⟩, hv, hmc, hfr', hmod,
    fun i j => hfilled i j (Cslib.Matrix.pairIndex_lt (i, j))⟩

/-! ### 3.3 Workspace representation of `AuctionState` and initialization -/

/-- Memory `s` represents pure `st : AuctionState ws.n` over unsigned cost matrix `C` at `ws`. -/
private structure AuctionMem (ws : AuctionWS) (C : Fin ws.n × Fin ws.n → ℕ)
    (st : AuctionState ws.n) (s : Memory.State) : Prop where
  /-- Unsigned matrix `C` is stored row-major at `ws.bC`. -/
  hC : ∀ i j : Fin ws.n, s.mem (ws.bC + (i.val * ws.n + j.val)) = C (i, j)
  /-- `owner[j]` stores `(st.owner j).elim ws.n Fin.val`. -/
  hOwner : ∀ j : Fin ws.n, s.mem (ws.bOwner + j.val) = (st.owner j).elim ws.n Fin.val
  /-- `price[j]` stores `(st.price j).toNat`. -/
  hPrice : ∀ j : Fin ws.n, s.mem (ws.bPrice + j.val) = (st.price j).toNat
  /-- `stack[0..st.free.length)` stores `st.free` in reverse (`top` at `st.free.length - 1`). -/
  hStack : ∀ k (hk : k < st.free.length),
    s.mem (ws.bStack + k) = (st.free[st.free.length - 1 - k]'(by omega)).val

/-- Disjointness and frontier validity of `ws : AuctionWS`. -/
private structure ValidWS (ws : AuctionWS) (s : Memory.State) : Prop where
  hbOwner : ws.bOwner = ws.bC + ws.n * ws.n
  hbPrice : ws.bPrice = ws.bOwner + ws.n
  hbStack : ws.bStack = ws.bPrice + ws.n
  houtBase : ws.outBase = ws.bStack + ws.n
  hfrontier : ws.outBase + ws.n + 1 ≤ s.frontier

private theorem ValidWS.of_frontier_eq {ws : AuctionWS} {s s' : Memory.State}
    (h : ValidWS ws s) (hfr : s'.frontier = s.frontier) : ValidWS ws s' :=
  ⟨h.hbOwner, h.hbPrice, h.hbStack, h.houtBase, hfr ▸ h.hfrontier⟩

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
    let prog := iterate initStep ws ws.n 0
    let s' := (Memory.spec 0).clientState s₀ prog
    iterationSafe initStep InitStepSafe w ws ws.n 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
      memoryCost prog s₀ ≤ 3 * ws.n ∧
      s'.frontier = s₀.frontier ∧
      (∀ a, ¬(ws.bOwner ≤ a ∧ a < ws.outBase) → s'.mem a = s₀.mem a) ∧
      AuctionMem ws C (auctionInit ws.n) s' := by
  obtain ⟨hbO, hbP, hbS, hout, hfr⟩ := hws
  have hit := iterate_spec initStep InitStepSafe w ws 3 ws.n
    (fun k idx s => idx = k ∧ s.frontier = s₀.frontier ∧
      (∀ j < k, s.mem (ws.bOwner + j) = ws.n ∧ s.mem (ws.bPrice + j) = 0 ∧
        s.mem (ws.bStack + j) = ws.n - (j + 1)))
    (fun a => ws.bOwner ≤ a ∧ a < ws.outBase)
    (fun k hk idx s ⟨hidx, hsfr, hprev⟩ => by
      subst idx
      have hsafe : InitStepSafe w (ws, k) s := by
        dsimp only [InitStepSafe]
        exact ⟨by omega, hfit_ws.of_le (by omega), hfit_ws.of_le (by omega),
          hfit_ws.of_le (by omega), hfit_ws.of_le (by omega)⟩
      have hv : (Memory.spec w).ValidHistory s
          ((Memory.spec w).clientHistory s (initStep (ws, k))) := by
        unfold initStep
        dsimp only
        exact validHistory_write_bind (by omega) (hfit_ws.of_le (by omega))
          (validHistory_write_bind (by dsimp only; omega) (fits_zero w)
            (validHistory_write_bind (by dsimp only; omega) (hfit_ws.of_le (by omega))
              (validHistory_pure w _ _)))
      have hmc : memoryCost (initStep (ws, k)) s ≤ 3 := by
        unfold initStep
        exact memoryCost_write_bind_le fun _ _ =>
          memoryCost_write_bind_le fun _ _ =>
            memoryCost_write_bind_le fun _ _ => Nat.le_refl 0
      have hst_eq : (Memory.spec 0).clientState s (initStep (ws, k)) =
          ⟨Function.update (Function.update (Function.update s.mem
            (ws.bOwner + k) ws.n) (ws.bPrice + k) 0) (ws.bStack + k) (ws.n - (k + 1)),
            s.frontier⟩ := by
        unfold initStep
        rw [clientState_bind_write, clientState_bind_write, clientState_bind_write,
          clientState_pure]
      have hres_eq : (Memory.spec 0).clientResult s (initStep (ws, k)) = k + 1 := by
        unfold initStep
        rw [clientResult_bind_write, clientResult_bind_write, clientResult_bind_write,
          clientResult_pure]
      refine ⟨hsafe, hv, hmc, by rw [hst_eq], fun x hx => ?_, ?_⟩
      · rw [hst_eq]
        dsimp only
        simp only [Function.update_of_ne (by omega : x ≠ ws.bStack + k),
          Function.update_of_ne (by omega : x ≠ ws.bPrice + k),
          Function.update_of_ne (by omega : x ≠ ws.bOwner + k)]
      · rw [hst_eq, hres_eq]
        dsimp only
        refine ⟨rfl, hsfr, fun j hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt' | rfl
        · obtain ⟨ho, hp, hst⟩ := hprev j hlt'
          refine ⟨?_, ?_, ?_⟩
          · simp only [Function.update_of_ne (by omega : ws.bOwner + j ≠ ws.bStack + k),
              Function.update_of_ne (by omega : ws.bOwner + j ≠ ws.bPrice + k),
              Function.update_of_ne (by omega : ws.bOwner + j ≠ ws.bOwner + k), ho]
          · simp only [Function.update_of_ne (by omega : ws.bPrice + j ≠ ws.bStack + k),
              Function.update_of_ne (by omega : ws.bPrice + j ≠ ws.bPrice + k),
              Function.update_of_ne (by omega : ws.bPrice + j ≠ ws.bOwner + k), hp]
          · simp only [Function.update_of_ne (by omega : ws.bStack + j ≠ ws.bStack + k),
              Function.update_of_ne (by omega : ws.bStack + j ≠ ws.bPrice + k),
              Function.update_of_ne (by omega : ws.bStack + j ≠ ws.bOwner + k), hst]
        · refine ⟨?_, ?_, ?_⟩
          · simp only [Function.update_of_ne (by omega : ws.bOwner + j ≠ ws.bStack + j),
              Function.update_of_ne (by omega : ws.bOwner + j ≠ ws.bPrice + j),
              Function.update_self]
          · simp only [Function.update_of_ne (by omega : ws.bPrice + j ≠ ws.bStack + j),
              Function.update_self]
          · simp only [Function.update_self])
    0 s₀ ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hv, hmc, hfr', hmod, _, _, hprev⟩ := hit
  refine ⟨hsafe, hv, hmc, hfr', hmod, ?_⟩
  refine ⟨fun i j => ?_, fun j => (hprev j.val j.isLt).1, fun j => (hprev j.val j.isLt).2.1,
    fun k hk => ?_⟩
  · have hlt : i.val * ws.n + j.val < ws.n * ws.n := Cslib.Matrix.pairIndex_lt (i, j)
    exact (hmod _ (by omega)).trans (hC_mem i j)
  · simp only [auctionInit, List.length_finRange] at hk ⊢
    rw [(hprev k hk).2.2, List.getElem_finRange]
    dsimp only [Fin.cast]
    omega

/-! ### 3.4 Row scan 1 (`findBestStep`) and row scan 2 (`findSecondStep`) -/

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

private def findBestProg (d : ScanRowArgs) : Memory.Prog BestState :=
  iterate findBestStep d d.n ⟨0, 0, 0⟩

private theorem findBestProg_realizes :
    Realizes .exact findBestProg encScanRowArgs encBestState
      (fun w d s => iterationSafe findBestStep FindBestStepSafe w d d.n ⟨0, 0, 0⟩ s)
      (fun _ _ => 0) := by
  unfold findBestProg
  realize [findBestStep_realizes]
  exact h

private theorem findBest_spec {w W : ℕ} (ws : AuctionWS) {C : Fin ws.n × Fin ws.n → ℕ}
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
    iterationSafe findBestStep FindBestStepSafe w d d.n ⟨0, 0, 0⟩ s₀ ∧
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
      have hC_k : s₀.mem (rowBase + b.idx) = C (i₀, jk) := by
        dsimp only [rowBase]; rw [Nat.add_assoc]; exact ham.hC i₀ jk
      have hP_k : s₀.mem (ws.bPrice + b.idx) = (st.price jk).toNat := ham.hPrice jk
      have hrc_le : s₀.mem (rowBase + b.idx) + s₀.mem (ws.bPrice + b.idx) ≤ 2 * W + ws.eps := by
        rw [hC_k, hP_k]
        have := hC_le i₀ jk; have := hp_nn jk; have := hp_le jk
        omega
      have hrc_z : ((s₀.mem (rowBase + b.idx) + s₀.mem (ws.bPrice + b.idx) : ℕ) : ℤ) =
          redCost cZ st.price i₀ jk := by
        rw [hC_k, hP_k]
        have := hp_nn jk
        dsimp only [redCost, cZ]
        omega
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
          simpa only [hk0] using hrc_z
      · rw [ite_eq_right hk0]
        rcases harg with h0 | ⟨j₀, hj₀_lt, htake, hbj, hbv⟩
        · omega
        · subst hbidx
          by_cases hlt : s₀.mem (rowBase + b.idx) + s₀.mem (ws.bPrice + b.idx) < b.bestVal
          · have hlt_z : redCost cZ st.price i₀ jk < redCost cZ st.price i₀ j₀ := by
              have hlt' : ((s₀.mem (rowBase + b.idx) + s₀.mem (ws.bPrice + b.idx) : ℕ) : ℤ) <
                  (b.bestVal : ℤ) := Nat.cast_lt.mpr hlt
              rwa [hrc_z, hbv] at hlt'
            rw [ite_eq_left hlt, clientResult_pure]
            dsimp only
            refine ⟨rfl, Or.inr ⟨jk, Nat.lt_succ_self _, ?_, rfl, hrc_z⟩⟩
            rw [List.take_succ_finRange hk', List.argmin_concat, htake]
            dsimp only
            exact ite_eq_left hlt_z
          · have hnlt_z : ¬(redCost cZ st.price i₀ jk < redCost cZ st.price i₀ j₀) := by
              intro hz
              apply hlt
              exact Nat.cast_lt.mp (by rwa [hrc_z, hbv])
            rw [ite_eq_right hlt, clientResult_pure]
            dsimp only
            refine ⟨rfl, Or.inr ⟨j₀, Nat.lt_succ_of_lt hj₀_lt, ?_, hbj, hbv⟩⟩
            rw [List.take_succ_finRange hk', List.argmin_concat, htake]
            dsimp only
            exact ite_eq_right hnlt_z)
    ⟨0, 0, 0⟩ s₀ ⟨rfl, rfl, Or.inl rfl⟩
  obtain ⟨hsafe, hv, hmc, _, _, hs_eq, _, hfinal⟩ := hit
  rcases hfinal with h0 | ⟨j₀, _, htake, hbj, hbv⟩
  · omega
  · rw [List.take_of_length_le (by simp)] at htake
    exact ⟨hsafe, hv, hmc, hs_eq, j₀, htake,
      fun k => List.le_of_mem_argmin (List.mem_finRange k) htake, hbj, hbv⟩

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

private def findSecondProg (d : ScanSecondArgs) : Memory.Prog SecondState :=
  iterate findSecondStep d d.n ⟨0, 0, 0⟩

private theorem findSecondProg_realizes :
    Realizes .exact findSecondProg encScanSecondArgs encSecondState
      (fun w d s => iterationSafe findSecondStep FindSecondStepSafe w d d.n ⟨0, 0, 0⟩ s)
      (fun _ _ => 0) := by
  unfold findSecondProg
  realize [findSecondStep_realizes]
  exact h

private theorem findSecond_spec {w W : ℕ} (ws : AuctionWS) {C : Fin ws.n × Fin ws.n → ℕ}
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
    iterationSafe findSecondStep FindSecondStepSafe w d d.n ⟨0, 0, 0⟩ s₀ ∧
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
      have hC_k : s₀.mem (rowBase + b.idx) = C (i₀, jk) := by
        dsimp only [rowBase]; rw [Nat.add_assoc]; exact ham.hC i₀ jk
      have hP_k : s₀.mem (ws.bPrice + b.idx) = (st.price jk).toNat := ham.hPrice jk
      have hrc_le : s₀.mem (rowBase + b.idx) + s₀.mem (ws.bPrice + b.idx) ≤ 2 * W + ws.eps := by
        rw [hC_k, hP_k]
        have := hC_le i₀ jk; have := hp_nn jk; have := hp_le jk
        omega
      have hrc_z : ((s₀.mem (rowBase + b.idx) + s₀.mem (ws.bPrice + b.idx) : ℕ) : ℤ) =
          redCost cZ st.price i₀ jk := by
        rw [hC_k, hP_k]
        have := hp_nn jk
        dsimp only [redCost, cZ]
        omega
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
          · have hlt_z : redCost cZ st.price i₀ jk < wPrev := by
              have hlt' : ((s₀.mem (rowBase + b.idx) + s₀.mem (ws.bPrice + b.idx) : ℕ) : ℤ) <
                  (b.secondVal : ℤ) := Nat.cast_lt.mpr hlt
              rwa [hrc_z, hsv_z] at hlt'
            rw [ite_eq_left hlt, clientResult_pure, min_eq_right (le_of_lt hlt_z)]
            exact ⟨rfl, rfl, hrc_z, hrc_le⟩
          · have hle_z : wPrev ≤ redCost cZ st.price i₀ jk := by
              by_contra hgt
              have hlt_z : redCost cZ st.price i₀ jk < wPrev := lt_of_not_ge hgt
              exact hlt (Nat.cast_lt.mp (by rwa [hrc_z, hsv_z]))
            rw [ite_eq_right hlt, clientResult_pure, min_eq_left hle_z]
            exact ⟨rfl, hhs1, hsv_z, hsv_le⟩)
    ⟨0, 0, 0⟩ s₀ ⟨rfl, rfl, by simp [prefList]⟩
  obtain ⟨hsafe, hv, hmc, _, _, hs_eq, _, hfinal⟩ := hit
  have hpref_n : (prefList ws.n).min? = secondBest cZ st.price i₀ j₀ := by
    dsimp only [prefList, secondBest]
    rw [List.take_of_length_le (by simp)]
  rw [hpref_n] at hfinal
  exact ⟨hsafe, hv, hmc, hs_eq, hfinal⟩

/-! ### 3.5 Single bid step (`bidStepProg`) and outer loop (`auctionCoreProg`) -/

private def computeNewP (ws : AuctionWS) (rowBase bestJ : ℕ) (sec : SecondState) :
    Memory.Prog ℕ :=
  if sec.hasSecond = 0 then do
    let pj ← Memory.read (ws.bPrice + bestJ)
    pure (pj + ws.eps)
  else do
    let cij ← Memory.read (rowBase + bestJ)
    pure (sec.secondVal - cij + ws.eps)

private def bidStepProg (x : AuctionWS × ℕ) : Memory.Prog ℕ := do
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

private abbrev BidStepSafe (w : ℕ) (x : AuctionWS × ℕ) (s : Memory.State) : Prop :=
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
    iterationSafe findBestStep FindBestStepSafe w dBest dBest.n ⟨0, 0, 0⟩ s ∧
    iterationSafe findSecondStep FindSecondStepSafe w dSec dSec.n ⟨0, 0, 0⟩ s₁ ∧
    Fits w (ws.bPrice + best.bestJ) ∧ Fits w (ws.bOwner + best.bestJ) ∧
    (sec.hasSecond = 0 → Fits w (s₂.mem (ws.bPrice + best.bestJ) + ws.eps)) ∧
    (sec.hasSecond ≠ 0 →
      Fits w (rowBase + best.bestJ) ∧
        s₂.mem (rowBase + best.bestJ) ≤ sec.secondVal ∧
        Fits w (sec.secondVal - s₂.mem (rowBase + best.bestJ) + ws.eps))

private theorem bidStepProg_realizes :
    Realizes .exact bidStepProg (appendWords encAuctionWS wordWords) wordWords
      BidStepSafe (fun _ _ => 0) := by
  unfold bidStepProg computeNewP
  realize [findBestProg_realizes, findSecondProg_realizes]
  all_goals
    rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _⟩
    tauto

private def auctionCutoff (ws : AuctionWS) : ℕ :=
  ws.n * (2 * ws.scale * ws.M + ws.eps) + 2

private def auctionCoreProg (ws : AuctionWS) : Memory.Prog ℕ := do
  let _ ← iterate initStep ws ws.n 0
  boundedWhile (fun _ (sp : ℕ) => 0 < sp) bidStepProg ws (auctionCutoff ws) ws.n

private abbrev AuctionCoreSafe (w : ℕ) (ws : AuctionWS) (s : Memory.State) : Prop :=
  let s₁ := (Memory.spec 0).clientState s (iterate initStep ws ws.n 0)
  let bw := boundedWhile (fun _ (sp : ℕ) => 0 < sp) bidStepProg ws (auctionCutoff ws) ws.n
  iterationSafe initStep InitStepSafe w ws ws.n 0 s ∧
    ((Memory.spec w).ValidHistory s₁ ((Memory.spec w).clientHistory s₁ bw) →
      whileSafe (fun _ (sp : ℕ) => 0 < sp) bidStepProg
        (fun w x s => BidStepSafe w (ws, x.2) s) w ws (auctionCutoff ws) ws.n s₁)

private theorem auctionCoreProg_realizes :
    Realizes .exact auctionCoreProg encAuctionWS wordWords
      AuctionCoreSafe (fun _ _ => 0) := by
  unfold auctionCoreProg
  realize [initStep_realizes, bidStepProg_realizes]
  all_goals
    rcases h with ⟨_, _⟩
    assumption

private theorem getElem_zero_of_eq_cons {α : Type*} {l : List α} {x : α} {xs : List α}
    (h : l = x :: xs) {i : ℕ} (hi : i < l.length) (hi0 : i = 0) : l[i]'hi = x := by
  subst h; subst hi0; rfl

private theorem getElem_succ_of_eq_cons {α : Type*} {l : List α} {x : α} {xs : List α}
    (h : l = x :: xs) (j : ℕ) {i : ℕ} (hi : i < l.length) (hj : j < xs.length)
    (hij : i = j + 1) : l[i]'hi = xs[j]'hj := by
  subst h; subst hij; rfl

private theorem bidStepProg_spec {w W : ℕ} (ws : AuctionWS) {C : Fin ws.n × Fin ws.n → ℕ}
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
    rw [h, getElem_zero_of_eq_cons hs_free _ (by omega)]
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
      refine ⟨fun _ => hnp_fit, fun hne => absurd hhs0 hne, ?_, ?_, ?_, ?_, hnp_eq ▸ hnp_fit⟩
      · dsimp only [pBranch, computeNewP]
        rw [ite_eq_left hhs0]
        exact validHistory_read_bind (by omega) (validHistory_pure w _ _)
      · dsimp only [pBranch, computeNewP]
        rw [ite_eq_left hhs0]
        exact memoryCost_read_bind_le fun _ _ => Nat.le_refl 0
      · dsimp only [pBranch, computeNewP]
        rw [ite_eq_left hhs0, clientState_bind_read, clientState_pure]
      · dsimp only [pBranch, computeNewP]
        rw [ite_eq_left hhs0, clientResult_bind_read, clientResult_pure, hnp_eq]
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
      refine ⟨fun h0 => absurd h0 hhs_ne, fun _ => ⟨hfrb_j, hcj_le, hnp_fit⟩,
        ?_, ?_, ?_, ?_, hnp_eq ▸ hnp_fit⟩
      · dsimp only [pBranch, computeNewP]
        rw [ite_eq_right hhs_ne]
        exact validHistory_read_bind (by dsimp only [rowBase]; omega) (validHistory_pure w _ _)
      · dsimp only [pBranch, computeNewP]
        rw [ite_eq_right hhs_ne]
        exact memoryCost_read_bind_le fun _ _ => Nat.le_refl 0
      · dsimp only [pBranch, computeNewP]
        rw [ite_eq_right hhs_ne, clientState_bind_read, clientState_pure]
      · dsimp only [pBranch, computeNewP]
        rw [ite_eq_right hhs_ne, clientResult_bind_read, clientResult_pure, hnp_eq]
  obtain ⟨hbr_pos, hbr_neg, hv_p, hmc_p, hs_p, hres_p, hfit_np⟩ := hpBranch
  have hsafe_all : BidStepSafe w (ws, st.free.length) s₀ := by
    unfold BidStepSafe
    dsimp only
    rw [hcurI]
    change 1 ≤ st.free.length ∧ Fits w 1 ∧ Fits w (ws.bStack + (st.free.length - 1)) ∧
      Fits w (i₀.val * ws.n) ∧ Fits w rowBase ∧
      iterationSafe findBestStep FindBestStepSafe w dBest dBest.n ⟨0, 0, 0⟩ s₀ ∧
      iterationSafe findSecondStep FindSecondStepSafe w ⟨ws.n, rowBase, ws.bPrice, best.bestJ⟩
        ws.n ⟨0, 0, 0⟩ ((Memory.spec 0).clientState s₀ (findBestProg dBest)) ∧
      Fits w (ws.bPrice + best.bestJ) ∧ Fits w (ws.bOwner + best.bestJ) ∧ _
    rw [hs_b, hbj']
    change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧
      (sec.hasSecond = 0 → Fits w (((Memory.spec 0).clientState s₀
          (findSecondProg dSec)).mem (ws.bPrice + j₀.val) + ws.eps)) ∧
      (sec.hasSecond ≠ 0 →
        Fits w (rowBase + j₀.val) ∧
          ((Memory.spec 0).clientState s₀ (findSecondProg dSec)).mem
            (rowBase + j₀.val) ≤ sec.secondVal ∧
          Fits w (sec.secondVal - ((Memory.spec 0).clientState s₀
            (findSecondProg dSec)).mem (rowBase + j₀.val) + ws.eps))
    rw [hs_s]
    exact ⟨by omega, hfit1, hfit_ws.of_le (by omega),
      hfit_ws.of_le (by omega), hfit_ws.of_le (by dsimp only [rowBase]; omega),
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
    rw [clientState_bind_read, hcurI, clientState_bind, hs_b]
    rw [hbj, clientState_bind, hs_s]
    change (Memory.spec 0).clientState s₀ (pBranch >>= _) = _
    rw [clientState_bind, hs_p, hres_p, clientState_bind_write, clientState_bind_read]
    dsimp only
    simp only [hold_s_mid]
    rw [clientState_bind_write]
    split_ifs
    · exact clientState_pure _ _
    · rw [clientState_bind_write, clientState_pure]
  have hrun_res : (Memory.spec 0).clientResult s₀ (bidStepProg (ws, st.free.length)) =
      if (st.owner j₀).elim ws.n Fin.val = ws.n then
        st.free.length - 1
      else
        st.free.length := by
    unfold bidStepProg
    dsimp only
    rw [clientResult_bind_read, hcurI, clientResult_bind, hs_b]
    rw [hbj, clientResult_bind, hs_s]
    change (Memory.spec 0).clientResult s₀ (pBranch >>= _) = _
    rw [clientResult_bind, hs_p, hres_p, clientResult_bind_write, clientResult_bind_read]
    dsimp only
    simp only [hold_s_mid]
    rw [clientResult_bind_write]
    split_ifs
    · exact clientResult_pure _ _
    · rw [clientResult_bind_write, clientResult_pure]
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
      memoryCost_bind']
    rw [hs_b, hbj, memoryCost_bind', hs_s]
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
    cases ho : st.owner j₀ with
    | none =>
      simp only [Option.elim_none, ↓reduceIte, Option.toList_none, List.nil_append]
      refine ⟨hs_mid_c, hs_mid_owner, hs_mid_price, fun k hk => ?_⟩
      dsimp only [s_mid] at hk ⊢
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      have hk' : k < st.free.length := by rw [hsp_eq]; omega
      rw [ham.hStack k hk',
        getElem_succ_of_eq_cons hs_free (rest.length - 1 - k) _ (by omega)
          (by rw [hsp_eq]; omega)]
    | some prevI =>
      have hne : prevI.val ≠ ws.n := ne_of_lt prevI.isLt
      simp only [Option.elim_some, hne, ↓reduceIte, Option.toList_some, List.singleton_append]
      refine ⟨fun i j => ?_, fun j => ?_, fun j => ?_, fun k hk => ?_⟩
      · have hlt_ij : i.val * ws.n + j.val < ws.n * ws.n := Cslib.Matrix.pairIndex_lt (i, j)
        dsimp only
        rw [Function.update_of_ne (by omega)]
        exact hs_mid_c i j
      · dsimp only
        rw [Function.update_of_ne (by omega)]
        exact hs_mid_owner j
      · dsimp only
        rw [Function.update_of_ne (by omega)]
        exact hs_mid_price j
      · dsimp only at hk ⊢
        simp only [List.length_cons] at hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt_r | rfl
        · dsimp only [s_mid]
          rw [Function.update_of_ne (by rw [hsp_eq]; omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]
          have hk' : k < st.free.length := by rw [hsp_eq]; omega
          rw [ham.hStack k hk',
            getElem_succ_of_eq_cons hs_free (rest.length - 1 - k) _ (by omega)
              (by rw [hsp_eq]; omega),
            getElem_succ_of_eq_cons rfl (rest.length - 1 - k) _ (by omega) (by simp; omega)]
        · rw [show st.free.length - 1 = rest.length by rw [hsp_eq]; omega, Function.update_self,
            getElem_zero_of_eq_cons rfl _ (by simp)]

private theorem bids_le_auctionLoop {n : ℕ} (c : Fin n × Fin n → ℤ) (ε : ℤ) :
    ∀ (fuel : ℕ) (st : AuctionState n), st.bids ≤ (auctionLoop c ε fuel st).bids
  | 0, _ => le_rfl
  | m + 1, st => by
    unfold auctionLoop
    rcases hf : st.free with _ | ⟨_, _⟩
    · exact le_rfl
    · dsimp only
      have hb := bids_bidStep (c := c) (ε := ε) hf
      have hm := bids_le_auctionLoop c ε m (bidStep c ε st)
      omega

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
    let s' := (Memory.spec 0).clientState s bw
    let st_end := auctionLoop cZ (ws.eps : ℤ) fuel st
    ((st_end.free = []) →
      whileSafe (fun _ (sp : ℕ) => 0 < sp) bidStepProg
        (fun w x s => BidStepSafe w (ws, x.2) s) w ws fuel st.free.length s) ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s bw) ∧
      memoryCost bw s ≤ (st_end.bids - st.bids) * (4 * ws.n + 6) ∧
      s'.frontier = s.frontier ∧
      AuctionMem ws C st_end s' := by
  induction fuel generalizing st s with
  | zero =>
    unfold boundedWhile auctionLoop
    refine ⟨fun hfree => by simp [whileSafe, hfree], validHistory_pure w _ _, ?_, rfl, ham⟩
    exact Nat.zero_le _
  | succ fuel ih =>
    rcases hs_free : st.free with _ | ⟨i₀, rest⟩
    · unfold boundedWhile auctionLoop
      simp only [hs_free, List.length_nil, lt_self_iff_false, ↓reduceIte]
      refine ⟨fun _ => by simp [whileSafe], validHistory_pure w _ _, ?_, rfl, ham⟩
      exact Nat.zero_le _
    · have hpos : 0 < st.free.length := by simp [hs_free]
      have hstep := bidStepProg_spec ws hs_free hε hinv hp_nn hC_le s hws ham
        hfit1 hfit_ws hfit_p
      obtain ⟨hsafe_step, hv_step, hmc_step, hfr_step, hres_step, ham_step⟩ := hstep
      let cZ : Fin ws.n × Fin ws.n → ℤ := fun e => (C e : ℤ)
      let st₁ := bidStep cZ (ws.eps : ℤ) st
      let s₁ := (Memory.spec 0).clientState s (bidStepProg (ws, st.free.length))
      have hinv₁ : AuctionInv cZ (ws.eps : ℤ) st₁ := hinv.bidStep (by positivity)
      have hp_nn₁ : ∀ j, 0 ≤ st₁.price j := price_nonneg_bidStep (by positivity) hp_nn
      have hws₁ : ValidWS ws s₁ := hws.of_frontier_eq hfr_step
      have hih := ih st₁ s₁ hinv₁ hp_nn₁ hws₁ ham_step
      obtain ⟨hwsafe_ih, hv_ih, hmc_ih, hfr_ih, ham_ih⟩ := hih
      have hbids₁ : st₁.bids = st.bids + 1 := bids_bidStep hs_free
      have hbids_mono : st₁.bids ≤ (auctionLoop cZ (ws.eps : ℤ) fuel st₁).bids :=
        bids_le_auctionLoop cZ (ws.eps : ℤ) fuel st₁
      have hbw_eq : boundedWhile (fun _ (sp : ℕ) => 0 < sp) bidStepProg ws (fuel + 1)
          st.free.length =
          (bidStepProg (ws, st.free.length) >>= fun a' =>
            boundedWhile (fun _ (sp : ℕ) => 0 < sp) bidStepProg ws fuel a') := by
        rw [boundedWhile, ite_eq_left hpos]
      have hloop_step : auctionLoop cZ (ws.eps : ℤ) (fuel + 1) st =
          auctionLoop cZ (ws.eps : ℤ) fuel st₁ := by
        rw [auctionLoop, hs_free]
      simp only [← hs_free]
      change ((auctionLoop cZ (ws.eps : ℤ) (fuel + 1) st).free = [] → _) ∧
        (Memory.spec w).ValidHistory s
          ((Memory.spec w).clientHistory s
            (boundedWhile (fun _ (sp : ℕ) => 0 < sp) bidStepProg ws (fuel + 1) st.free.length)) ∧
        memoryCost
          (boundedWhile (fun _ (sp : ℕ) => 0 < sp) bidStepProg ws (fuel + 1) st.free.length) s ≤
          ((auctionLoop cZ (ws.eps : ℤ) (fuel + 1) st).bids - st.bids) * (4 * ws.n + 6) ∧
        ((Memory.spec 0).clientState s
          (boundedWhile (fun _ (sp : ℕ) => 0 < sp) bidStepProg ws (fuel + 1)
            st.free.length)).frontier = s.frontier ∧
        AuctionMem ws C (auctionLoop cZ (ws.eps : ℤ) (fuel + 1) st)
          ((Memory.spec 0).clientState s
            (boundedWhile (fun _ (sp : ℕ) => 0 < sp) bidStepProg ws (fuel + 1) st.free.length))
      rw [hbw_eq, hloop_step]
      refine ⟨fun hfree => ?_, ?_, ?_, ?_, ?_⟩
      · rw [whileSafe, ite_eq_left hpos, hres_step]
        exact ⟨hsafe_step, hwsafe_ih hfree⟩
      · refine validHistory_bind_step hv_step ?_
        rwa [hres_step]
      · rw [memoryCost_bind', hres_step]
        have hsub : (auctionLoop cZ (ws.eps : ℤ) fuel st₁).bids - st.bids =
            1 + ((auctionLoop cZ (ws.eps : ℤ) fuel st₁).bids - st₁.bids) := by omega
        rw [hsub, Nat.add_mul, one_mul]
        exact Nat.add_le_add hmc_step hmc_ih
      · rw [clientState_bind, hres_step]
        exact hfr_ih.trans hfr_step
      · rw [clientState_bind, hres_step]
        exact ham_ih

private theorem auctionCoreProg_spec {w : ℕ} (ws : AuctionWS)
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
  have hinit := initAuction_spec ws s₀ hws hC_mem hfit_ws
  obtain ⟨hsafe_init, hv_init, hmc_init, hfr_init, _, ham_init⟩ := hinit
  let s₁ := (Memory.spec 0).clientState s₀ (iterate initStep ws ws.n 0)
  have hws₁ : ValidWS ws s₁ := hws.of_frontier_eq hfr_init
  let W := 2 * ws.scale * ws.M
  have hfit_p' : Fits w (2 * W + 2 * ws.eps) :=
    hfit_p.of_le (le_of_eq (by dsimp only [W]; ring))
  have hlen_init : (auctionInit ws.n).free.length = ws.n := by simp [auctionInit]
  have hbw := boundedWhile_auctionLoop_spec ws hε hC_le (auctionCutoff ws) (auctionInit ws.n) s₁
    auctionInv_init (fun _ => le_rfl) hws₁ ham_init hfit1 hfit_ws hfit_p'
  obtain ⟨hwsafe_bw, hv_bw, hmc_bw, hfr_bw, ham_bw⟩ := hbw
  let cZ : Fin ws.n × Fin ws.n → ℤ := fun e => (C e : ℤ)
  have hεZ : (0 : ℤ) < (ws.eps : ℤ) := Nat.cast_pos.mpr hε
  have hC_spread : ∀ i j k : Fin ws.n, cZ (i, k) - cZ (i, j) ≤ (W : ℤ) := fun i j k => by
    have := hC_le i k
    dsimp only [cZ]; omega
  have hcut_free : (auctionLoop cZ (ws.eps : ℤ) (auctionCutoff ws) (auctionInit ws.n)).free = [] :=
    (auctionLoop_spec hεZ hC_spread (auctionCutoff ws) (auctionInit ws.n) auctionInv_init (by
      simp only [auctionInit, Finset.sum_const_zero, sub_zero]
      have hK_nn : (0 : ℤ) ≤ (ws.n : ℤ) * ((W : ℤ) + (ws.eps : ℤ)) := by positivity
      have h1 : (1 : ℤ) ≤ (ws.eps : ℤ) := by omega
      have hmul : (ws.n : ℤ) * ((W : ℤ) + (ws.eps : ℤ)) ≤
          ((ws.n : ℤ) * ((W : ℤ) + (ws.eps : ℤ))) * (ws.eps : ℤ) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left h1 hK_nn
      have hcut_eq : ((auctionCutoff ws : ℕ) : ℤ) =
          (ws.n : ℤ) * ((W : ℤ) + (ws.eps : ℤ)) + 2 := by
        dsimp only [auctionCutoff, W]; push_cast; ring
      rw [hcut_eq, add_mul]
      linarith)).2
  have hloop_eq :
      auctionLoop cZ (ws.eps : ℤ) (auctionCutoff ws) (auctionInit ws.n) =
        auction cZ (ws.eps : ℤ) := by
    unfold auction
    have hf2 : (auctionLoop cZ (ws.eps : ℤ)
        (bidBound ws.n (costSpread cZ) (ws.eps : ℤ)) (auctionInit ws.n)).free = [] :=
      auction_free hεZ
    rcases le_total (auctionCutoff ws)
        (bidBound ws.n (costSpread cZ) (ws.eps : ℤ)) with hle | hle
    · symm
      rw [← Nat.add_sub_cancel' hle, auctionLoop_add hcut_free]
    · rw [← Nat.add_sub_cancel' hle, auctionLoop_add hf2]
  simp only [hlen_init] at hwsafe_bw hv_bw hmc_bw hfr_bw ham_bw
  have hsafe_core : AuctionCoreSafe w ws s₀ := ⟨hsafe_init, fun _ => hwsafe_bw hcut_free⟩
  unfold auctionCoreProg
  refine ⟨hsafe_core, validHistory_bind_step hv_init hv_bw, ?_, ?_, ?_⟩
  · rw [memoryCost_bind']
    rw [hloop_eq, show (auctionInit ws.n).bids = 0 from rfl, Nat.sub_zero] at hmc_bw
    dsimp only [s₁, cZ] at hmc_bw ⊢
    omega
  · rw [clientState_bind]
    exact hfr_bw.trans hfr_init
  · rw [clientState_bind]
    rwa [← hloop_eq]

/-! ### 3.6 Scattering `objectOf` to output memory (`scatterProg`) -/

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

private def scatterProg (ws : AuctionWS) : Memory.Prog ℕ := do
  Memory.write ws.outBase ws.n
  let _ ← iterate scatterStep ws ws.n 0
  pure ws.outBase

private abbrev ScatterProgSafe (w : ℕ) (ws : AuctionWS) (s : Memory.State) : Prop :=
  let s₁ : Memory.State := ⟨Function.update s.mem ws.outBase ws.n, s.frontier⟩
  iterationSafe scatterStep ScatterStepSafe w ws ws.n 0 s₁

private theorem scatterProg_realizes :
    Realizes .exact scatterProg encAuctionWS wordWords
      ScatterProgSafe (fun _ _ => 0) := by
  unfold scatterProg
  realize [scatterStep_realizes]
  exact iterationSafe_imp h (fun _ => rfl) fun _ _ hs => hs

private theorem scatterProg_spec {w : ℕ} (ws : AuctionWS) {C : Fin ws.n × Fin ws.n → ℕ}
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
  have howner_some : ∀ j : Fin ws.n, ∃ i : Fin ws.n, st.owner j = some i := fun j => by
    cases ho : st.owner j with
    | some i => exact ⟨i, rfl⟩
    | none =>
      exfalso
      have hcard : (Finset.univ.image st.objectOf).card = ws.n := by
        rw [Finset.card_image_of_injective _ fun i₁ i₂ e =>
          Option.some_injective _
            ((hinv.owner_objectOf hfree i₁).symm.trans (by
              rw [e]; exact hinv.owner_objectOf hfree i₂)),
          Finset.card_univ, Fintype.card_fin]
      have hsub : Finset.univ.image st.objectOf ⊆ Finset.univ.erase j := by
        intro x hx
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        refine Finset.mem_erase.mpr ⟨fun hEq => ?_, Finset.mem_univ _⟩
        have := hinv.owner_objectOf hfree i
        rw [hEq, ho] at this
        cases this
      have hlt := (Finset.card_le_card hsub).trans_lt
        (Finset.card_erase_lt_of_mem (Finset.mem_univ j))
      rw [hcard, Finset.card_univ, Fintype.card_fin] at hlt
      exact Nat.lt_irrefl _ hlt
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
      have hmc : memoryCost (scatterStep (ws, k)) s ≤ 2 := by
        unfold scatterStep
        exact memoryCost_read_bind_le fun _ _ =>
          memoryCost_write_bind_le fun _ _ => Nat.le_refl 0
      have hst_eq : (Memory.spec 0).clientState s (scatterStep (ws, k)) =
          ⟨Function.update s.mem (ws.outBase + 1 + ik.val) k, s.frontier⟩ := by
        unfold scatterStep
        rw [clientState_bind_read]
        dsimp only
        rw [ho_k, clientState_bind_write, clientState_pure]
      have hres_eq : (Memory.spec 0).clientResult s (scatterStep (ws, k)) = k + 1 := by
        unfold scatterStep
        rw [clientResult_bind_read, clientResult_bind_write, clientResult_pure]
      refine ⟨hsafe, hv, hmc, by rw [hst_eq], fun x hx => ?_, ?_⟩
      · rw [hst_eq]
        dsimp only
        exact Function.update_of_ne (by have := ik.isLt; omega) _ _
      · rw [hst_eq, hres_eq]
        dsimp only
        refine ⟨rfl, hsfr, ?_, fun a ha => ?_, fun j hj i hi => ?_⟩
        · rw [Function.update_of_ne (by omega)]; exact hhdr
        · rw [Function.update_of_ne (by omega)]; exact hlow a ha
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt' | heq
          · have hij_ne : i ≠ ik := fun hEq => by
              subst hEq
              have hj_eq : j = jk := hinv.owner_inj j jk i hi hik
              exact absurd (congrArg Fin.val hj_eq) (ne_of_lt hlt')
            rw [Function.update_of_ne (by have := Fin.val_ne_of_ne hij_ne; omega)]
            exact hscat j hlt' i hi
          · have hj_eq : j = jk := Fin.ext heq
            subst hj_eq
            have hi_eq : i = ik := Option.some_injective _ (hi.symm.trans hik)
            subst hi_eq
            exact Function.update_self _ _ _)
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
  · rw [clientState_bind_write, clientState_bind, clientState_pure]
    exact hfr_it
  · rw [clientResult_bind_write, clientResult_bind, clientResult_pure]
  · rw [clientState_bind_write, clientState_bind, clientState_pure]
    have hlt_ij : i.val * ws.n + j.val < ws.n * ws.n := Cslib.Matrix.pairIndex_lt (i, j)
    exact (hlow _ (by omega)).trans (ham.hC i j)
  · rw [clientState_bind_write, clientState_bind, clientState_pure, outputList_eq_iff]
    refine ⟨by simp only [List.length_map, List.length_finRange]; exact hhdr, fun idx => ?_⟩
    have hi_lt : idx.val < ws.n := by simpa using idx.isLt
    let iFin : Fin ws.n := ⟨idx.val, hi_lt⟩
    change ((Memory.spec 0).clientState s₁ (iterate scatterStep ws ws.n 0)).mem
        (ws.outBase + 1 + idx.val) =
      ((List.finRange ws.n).map fun i => (st.objectOf i).val)[idx.val]
    simp only [List.getElem_map, List.getElem_finRange]
    exact hscat (st.objectOf iFin) (st.objectOf iFin).isLt iFin (hinv.owner_objectOf hfree iFin)

/-! ### 3.7 Summing and signed-encoding optimal cost (`sumScaledCostProg`) -/

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

private def sumScaledCostProg (ws : AuctionWS) : Memory.Prog ℕ := do
  let res ← iterate sumScaledStep ws ws.n ⟨0, 0⟩
  let shiftTotal := ws.n * ws.M
  if res.acc < shiftTotal then
    pure (2 * (shiftTotal - res.acc) + 1)
  else
    pure (2 * (res.acc - shiftTotal))

private abbrev SumScaledCostSafe (w : ℕ) (ws : AuctionWS) (s : Memory.State) : Prop :=
  let res := (Memory.spec 0).clientResult s (iterate sumScaledStep ws ws.n ⟨0, 0⟩)
  let shiftTotal := ws.n * ws.M
  iterationSafe sumScaledStep SumScaledStepSafe w ws ws.n ⟨0, 0⟩ s ∧
    Fits w 1 ∧ Fits w 2 ∧ Fits w shiftTotal ∧
    (res.acc < shiftTotal →
      res.acc ≤ shiftTotal ∧ Fits w (2 * (shiftTotal - res.acc)) ∧
        Fits w (2 * (shiftTotal - res.acc) + 1)) ∧
    (¬(res.acc < shiftTotal) →
      shiftTotal ≤ res.acc ∧ Fits w (2 * (res.acc - shiftTotal)))

private theorem sumScaledCostProg_realizes :
    Realizes .exact sumScaledCostProg encAuctionWS wordWords
      SumScaledCostSafe (fun _ _ => 0) := by
  unfold sumScaledCostProg
  realize [sumScaledStep_realizes]
  all_goals
    rcases h with ⟨_, _, _, _, _, _⟩
    tauto

private theorem four_n_maxMag_add_one_le_wordBound (inst : Instance) :
    4 * (inst.n * inst.maxMag) + 1 ≤ inst.wordBound := by
  unfold Instance.wordBound
  have h : 4 * (inst.n * inst.maxMag) ≤ 4 * (inst.n + 1) * inst.maxMag := by
    calc 4 * (inst.n * inst.maxMag) = 4 * inst.n * inst.maxMag := by ring
      _ ≤ 4 * (inst.n + 1) * inst.maxMag :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 (Nat.le_succ _))
  omega

private theorem sumScaledCostProg_spec {w : ℕ} (inst : Instance) (ws : AuctionWS)
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

/-! ## Section 4: Top-level clients and Word-RAM running-time theorems -/

private abbrev pairWords : (ℕ × ℕ) ↪ (Fin 2 → ℕ) := appendWords wordWords wordWords

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
    iterationSafe scanMaxStep ScanMaxStepSafe w ⟨a.matBase, n * n⟩ (n * n) ⟨0, 0⟩ s₁ ∧
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

private def epsMainProg (ne : ℕ × ℕ) : Memory.Prog ℕ := do
  let ws ← solveAuctionProg ⟨ne.1, ne.2, 1, 3⟩
  pure ws.outBase

private abbrev EpsMainSafe (w : ℕ) (ne : ℕ × ℕ) (s₀ : Memory.State) : Prop :=
  Fits w 1 ∧ Fits w 3 ∧ SolveAuctionSafe w ⟨ne.1, ne.2, 1, 3⟩ s₀

private theorem epsMainProg_realizes :
    Realizes .exact epsMainProg pairWords wordWords EpsMainSafe (fun _ _ => 0) := by
  unfold epsMainProg
  realize [solveAuctionProg_realizes]
  all_goals
    rcases h with ⟨_, _, _⟩
    assumption

private theorem epsMainProg_spec {w C : ℕ} (inst : EpsInstance) (hε : 0 < inst.eps)
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
    inst.init_mem_cost inst.toInstance.natAbs_cost_le_maxMag
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

private def scaledSolveProg (n : ℕ) : Memory.Prog AuctionWS :=
  solveAuctionProg ⟨n, 1, n + 1, 2⟩

private abbrev ScaledSolveSafe (w n : ℕ) (s₀ : Memory.State) : Prop :=
  Fits w 1 ∧ Fits w (n + 1) ∧ Fits w 2 ∧ SolveAuctionSafe w ⟨n, 1, n + 1, 2⟩ s₀

private theorem scaledSolveProg_realizes :
    Realizes .exact scaledSolveProg wordWords encAuctionWS ScaledSolveSafe (fun _ _ => 0) := by
  unfold scaledSolveProg
  realize [solveAuctionProg_realizes]
  all_goals
    rcases h with ⟨_, _, _, _⟩
    assumption

private theorem scaledSolveProg_spec {w C : ℕ} (inst : Instance)
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
    inst.init_mem_cost inst.natAbs_cost_le_maxMag hf2
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
  all_goals
    rcases h with ⟨_, _⟩
    assumption

private theorem eps_poly_bound (n C eps : ℕ) (hε : 0 < eps) :
    (n * (C + eps) / eps + 1) * (4 * n + 6) + 3 * (n * n) + 5 * n + 3 + 1 ≤
      42 * (n ^ 2 * (C / eps + 1) + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hC_lt : C < (C / eps + 1) * eps := by
      rw [Nat.add_mul, one_mul]
      exact Nat.lt_div_mul_add hε
    have heps_le : eps ≤ (C / eps + 1) * eps :=
      Nat.le_mul_of_pos_left eps (Nat.succ_pos (C / eps))
    have hCeps_le : C + eps ≤ 2 * (C / eps + 1) * eps := by
      calc C + eps ≤ (C / eps + 1) * eps + (C / eps + 1) * eps :=
            Nat.add_le_add (le_of_lt hC_lt) heps_le
        _ = 2 * (C / eps + 1) * eps := by ring
    have hmul_le : n * (C + eps) ≤ (2 * n * (C / eps + 1)) * eps := by
      calc n * (C + eps) ≤ n * (2 * (C / eps + 1) * eps) := Nat.mul_le_mul_left n hCeps_le
        _ = (2 * n * (C / eps + 1)) * eps := by ring
    have hdiv_le : n * (C + eps) / eps ≤ 2 * n * (C / eps + 1) :=
      (Nat.div_le_div_right hmul_le).trans_eq (Nat.mul_div_cancel _ hε)
    have h1_le : 1 ≤ n * (C / eps + 1) := Nat.mul_pos hn (Nat.succ_pos _)
    have hbids_le : n * (C + eps) / eps + 1 ≤ 3 * n * (C / eps + 1) := by
      calc n * (C + eps) / eps + 1
          ≤ 2 * n * (C / eps + 1) + n * (C / eps + 1) := Nat.add_le_add hdiv_le h1_le
        _ = 3 * n * (C / eps + 1) := by ring
    have h4n : 4 * n + 6 ≤ 10 * n := by omega
    have hprod : (n * (C + eps) / eps + 1) * (4 * n + 6) ≤ 30 * (n ^ 2 * (C / eps + 1)) := by
      calc (n * (C + eps) / eps + 1) * (4 * n + 6)
          ≤ (3 * n * (C / eps + 1)) * (10 * n) := Nat.mul_le_mul hbids_le h4n
        _ = 30 * (n ^ 2 * (C / eps + 1)) := by ring
    have hquad : 3 * (n * n) + 5 * n + 4 ≤ 12 * (n ^ 2 * (C / eps + 1)) := by
      have hn2 : 3 * (n * n) + 5 * n + 4 ≤ 12 * n ^ 2 := by nlinarith
      calc 3 * (n * n) + 5 * n + 4 ≤ 12 * n ^ 2 := hn2
        _ = 12 * (n ^ 2 * 1) := by ring
        _ ≤ 12 * (n ^ 2 * (C / eps + 1)) :=
          Nat.mul_le_mul_left 12 (Nat.mul_le_mul_left _ (Nat.succ_pos _))
    linarith

private theorem scaled_poly_bound (n C : ℕ) :
    (n * ((n + 1) * C + 1) + 1) * (4 * n + 6) + 3 * (n * n) + 7 * n + 3 + 1 ≤
      34 * (n ^ 3 * C + n ^ 2 + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : (n + 1) * C + 1 ≤ 2 * n * C + 1 := by
      have : n + 1 ≤ 2 * n := by omega
      nlinarith
    have h2 : n * ((n + 1) * C + 1) + 1 ≤ 2 * n ^ 2 * C + 2 * n := by nlinarith
    have h3 : 4 * n + 6 ≤ 10 * n := by omega
    have hprod : (n * ((n + 1) * C + 1) + 1) * (4 * n + 6) ≤
        20 * (n ^ 3 * C) + 20 * n ^ 2 := by
      calc (n * ((n + 1) * C + 1) + 1) * (4 * n + 6)
          ≤ (2 * n ^ 2 * C + 2 * n) * (10 * n) := Nat.mul_le_mul h2 h3
        _ = 20 * (n ^ 3 * C) + 20 * n ^ 2 := by ring
    have hquad : 3 * (n * n) + 7 * n + 4 ≤ 14 * n ^ 2 := by nlinarith
    have hnn3 : 0 ≤ n ^ 3 * C := Nat.zero_le _
    linarith

private theorem init_words_spec {w : ℕ} (inst : Instance) (hw : Fits w inst.wordBound) :
    InputFits w inst.encode ∧
      Fits w (inst.encode.length + 1) ∧
      (∀ j : Fin 1, inst.encode.getD j.val 0 = wordWords inst.n j) ∧
      1 ≤ inst.encode.length := by
  refine ⟨inst.inputFits_encode hw,
    hw.of_le (by rw [inst.encode_length]; unfold Instance.wordBound; nlinarith),
    ?_, by rw [inst.encode_length]; omega⟩
  rintro ⟨_ | _, hj⟩
  · rfl
  · omega

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
      rintro ⟨_ | _ | _, hj⟩
      · rfl
      · rfl
      · omega
    have hk : 2 ≤ inst.encode.length := by rw [inst.encode_length]; omega
    obtain ⟨hsafe, hv, hmc, hout, hfit_out⟩ := epsMainProg_spec inst hε hC hw
    obtain ⟨y, m, hruns₀, hhalt₀, hmem, _, hsteps⟩ :=
      he w (inst.n, inst.eps) inst.encode hlayout hk hfit_len hin hsafe hv
    rw [clientState_width w] at hmem
    rw [clientResult_width w] at hhalt₀
    dsimp only [wordWords] at hhalt₀
    have hymem : y.mem =
        ((Memory.spec 0).clientState (Memory.State.init inst.encode)
          (epsMainProg (inst.n, inst.eps))).mem :=
      congrArg Memory.State.mem hmem
    refine ⟨m + 1, ⟨⟨pc, y⟩, m, _, runs_stripRand hruns₀, step_stripRand_of_halt hhalt₀,
      hymem ▸ hout, hfit_out, rfl⟩, ?_⟩
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
          (scaledMainProg inst.n)) := by
      unfold scaledMainProg
      exact validHistory_bind_step hv_s (validHistory_pure w _ _)
    have hmc : memoryCost (scaledMainProg inst.n) (Memory.State.init inst.encode) ≤
        (inst.n * ((inst.n + 1) * C + 1) + 1) * (4 * inst.n + 6) +
          3 * (inst.n * inst.n) + 7 * inst.n + 2 := by
      unfold scaledMainProg
      rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
      exact hmc_s.trans (by omega)
    obtain ⟨y, m, hruns₀, hhalt₀, hmem, _, hsteps⟩ :=
      he w inst.n inst.encode hlayout hk hfit_len hin hsafe hv
    rw [clientState_width w] at hmem
    rw [clientResult_width w] at hhalt₀
    dsimp only [wordWords] at hhalt₀
    have hymem : y.mem =
        ((Memory.spec 0).clientState (Memory.State.init inst.encode)
          (scaledMainProg inst.n)).mem :=
      congrArg Memory.State.mem hmem
    have hres_eq : (Memory.spec 0).clientResult (Memory.State.init inst.encode)
        (scaledMainProg inst.n) =
        ((Memory.spec 0).clientResult (Memory.State.init inst.encode)
          (scaledSolveProg inst.n)).outBase := by
      unfold scaledMainProg
      rw [clientResult_bind, clientResult_pure]
    have hst_eq : (Memory.spec 0).clientState (Memory.State.init inst.encode)
        (scaledMainProg inst.n) =
        (Memory.spec 0).clientState (Memory.State.init inst.encode)
          (scaledSolveProg inst.n) := by
      unfold scaledMainProg
      rw [clientState_bind, clientState_pure]
    refine ⟨m + 1, ⟨⟨pc, y⟩, m, _, runs_stripRand hruns₀, step_stripRand_of_halt hhalt₀,
      ?_, ?_, rfl⟩, scaled_steps_le hsteps hmc⟩
    · rw [hymem, hst_eq, hres_eq]; exact hout_s
    · rw [hres_eq, inst.length_assignment]
      rw [hws_n] at hfit_ws
      exact hfit_ws.of_le (Nat.le_succ _)
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
    let ws := (Memory.spec 0).clientResult (Memory.State.init inst.encode)
      (scaledSolveProg inst.n)
    let s_after := (Memory.spec 0).clientState (Memory.State.init inst.encode)
      (scaledSolveProg inst.n)
    obtain ⟨hsafe_sum, hv_sum, hmc_sum, hres_sum⟩ :=
      sumScaledCostProg_spec inst ws s_after hws_s hws_n hws_sc hM_le hM_ge hC_s hout_s hw hfit_ws
    have hsafe : ScaledMinCostSafe w inst.n (Memory.State.init inst.encode) :=
      ⟨hsafe_s, hsafe_sum⟩
    have hv : (Memory.spec w).ValidHistory (Memory.State.init inst.encode)
        ((Memory.spec w).clientHistory (Memory.State.init inst.encode)
          (scaledMinCostMainProg inst.n)) := by
      unfold scaledMinCostMainProg
      exact validHistory_bind_step hv_s hv_sum
    have hmc : memoryCost (scaledMinCostMainProg inst.n) (Memory.State.init inst.encode) ≤
        (inst.n * ((inst.n + 1) * C + 1) + 1) * (4 * inst.n + 6) +
          3 * (inst.n * inst.n) + 7 * inst.n + 2 := by
      unfold scaledMinCostMainProg
      rw [memoryCost_bind']
      exact (Nat.add_le_add hmc_s hmc_sum).trans (by omega)
    obtain ⟨y, m, hruns₀, hhalt₀, _, _, hsteps⟩ :=
      he w inst.n inst.encode hlayout hk hfit_len hin hsafe hv
    rw [clientResult_width w] at hhalt₀
    dsimp only [wordWords] at hhalt₀
    have hres_eq : (Memory.spec 0).clientResult (Memory.State.init inst.encode)
        (scaledMinCostMainProg inst.n) = inst.encodedMinCost := by
      unfold scaledMinCostMainProg
      rw [clientResult_bind]
      exact hres_sum
    rw [hres_eq] at hhalt₀
    exact ⟨m + 1, ⟨⟨pc, y⟩, m, runs_stripRand hruns₀, step_stripRand_of_halt hhalt₀, rfl⟩,
      scaled_steps_le hsteps hmc⟩
  refine ⟨r, 34 * C₁ + 1, by omega, prog, not_readsWidth_stripRand hnw₀,
    isRandFree_stripRand prog₀, @hmain, fun inst w hw _ =>
      hmain inst inst.sub_le_rowSpread hw⟩

end

end Cslib.Algorithms.WordRAM.Auction
