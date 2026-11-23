/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Lean.Assignment.Auction
import CslibFrontier.Algorithms.WordRAM.Auction
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Perm

/-!
# Auction algorithm for the assignment problem: checked instances

Kernel-checked (`decide +kernel`, no `native_decide`) pure and Word-RAM checks of Bertsekas's
auction algorithm (`CslibFrontier.Algorithms.Lean.Assignment.Auction` and
`CslibFrontier.Algorithms.WordRAM.Auction`):

1. A `3 × 3` cost matrix: the exact (scaled) auction returns the optimal assignment, checked
   against all `3! = 6` permutations; the final prices satisfy `1`-complementary slackness but not
   `0`-complementary slackness, and give the dual certificate of `sum_auctionPerm_le_rowPotential`.
2. A `2 × 2` matrix on which the unscaled auction with `ε = 1` is suboptimal by `1 < n ε = 2`, so
   the scaling by `n + 1` behind `scaledAuctionPerm` is needed for exact optimality.
3. The price-war example of [Bertsekas1998], Figs. 1.12–1.14 (three persons who all prefer two
   equally good objects to a third): the number of bids grows with `C / ε`, and the run stays
   within the bound of `bids_auction_le`.
4. Boundary cases `n = 0` (no bids) and `n = 1` (one bid, raising the price by `ε`).
5. **Word-RAM `O(n² (C / ε + 1))` `ε`-auction and `O(n³ C + n²)` exact scaled auction:** ordinary
   `module` client instantiations of `exists_epsAuction_program`, `exists_scaledAuction_program`,
   `exists_scaledMinCost_program`, and `sum_scaledAuctionPerm_le` across `n = 0` (`w = 4`),
   negative singleton `n = 1` (`w = 8`), all-zero `C = 0` ties (`n = 3`), `c2`, `c3` (at both
   `w = 16` and `w = 64`), Bertsekas's price war (`ε = 1` and `ε = 2`), and an `n = 12` instance
   (`C = 55`, `w = 64`).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.AuctionAssignment

open Cslib.Algorithms.Lean.Assignment
open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.Auction

/-! ### A `3 × 3` instance -/

/-- Costs `[[4, 1, 3], [2, 0, 5], [3, 2, 2]]`; the unique optimum `[1, 0, 2]` costs `5`. -/
def c3 : Fin 3 × Fin 3 → ℤ := fun e => ![![4, 1, 3], ![2, 0, 5], ![3, 2, 2]] e.1 e.2

/-- The exact auction returns the assignment `0 ↦ 1, 1 ↦ 0, 2 ↦ 2`. -/
example : (List.finRange 3).map (scaledAuctionPerm c3) = [1, 0, 2] := by decide +kernel

/-- Brute-force check of `sum_scaledAuctionPerm_le`: the output is optimal among all
permutations. -/
example : ∀ τ : Equiv.Perm (Fin 3), ∑ i, c3 (i, scaledAuctionPerm c3 i) ≤ ∑ i, c3 (i, τ i) := by
  decide +kernel

/-- The exact auction `scaledAuction c3` (costs scaled by `n + 1 = 4`, `ε = 1`) makes `3` bids and
ends at prices `[2, 9, 7]`. The row cost ranges of `c3` are at most `C = 5`, so
`bids_scaledAuction_le` allows `3 * (4 * 5 + 1) + 1 = 64` bids. -/
example : (scaledAuction c3).bids = 3 ∧
    (List.finRange 3).map (scaledAuction c3).price = [2, 9, 7] ∧
    (∀ i j k : Fin 3, c3 (i, k) - c3 (i, j) ≤ 5) ∧ 3 * ((3 + 1) * 5 + 1) + 1 = 64 := by
  decide +kernel

/-- The final prices satisfy `1`-complementary slackness (`isEpsCompSlack_auctionPerm`)
but not `0`-complementary slackness: person `1` could gain `1` by switching to object `1`. -/
example : IsEpsCompSlack (fun e => (3 + 1) * c3 e) 1 (scaledAuctionPerm c3)
      (auction (fun e => (3 + 1) * c3 e) 1).price ∧
    ¬ IsEpsCompSlack (fun e => (3 + 1) * c3 e) 0 (scaledAuctionPerm c3)
      (auction (fun e => (3 + 1) * c3 e) 1).price := by
  unfold IsEpsCompSlack
  decide +kernel

/-- The dual certificate of `sum_auctionPerm_le_rowPotential` on the scaled costs: row potentials
`[13, 9, 14]` and column potentials `-[2, 9, 7]` total `18`, within `n ε = 3` of the scaled cost
`20` of the output. -/
example : (List.finRange 3).map
      (rowPotential (fun e => 4 * c3 e) (auction (fun e => 4 * c3 e) 1).price) = [13, 9, 14] ∧
    ∑ i, 4 * c3 (i, scaledAuctionPerm c3 i) = 20 := by
  decide +kernel

/-! ### Scaling is needed for exact optimality -/

/-- Costs `[[1, 0], [2, 0]]`; the identity costs `1` and the swap costs `2`. -/
def c2 : Fin 2 × Fin 2 → ℤ := fun e => ![![1, 0], ![2, 0]] e.1 e.2

/-- The unscaled auction with `ε = 1` returns the swap, which costs `2 > 1`: suboptimal, but within
`n ε = 2` as `sum_auctionPerm_le` guarantees. -/
example : (List.finRange 2).map (auctionPerm c2 one_pos) = [1, 0] ∧
    ∑ i, c2 (i, auctionPerm c2 one_pos i) = 2 ∧ ∑ i, c2 (i, i) = 1 := by
  decide +kernel

/-- The exact auction returns the optimal identity assignment. -/
example : (List.finRange 2).map (scaledAuctionPerm c2) = [0, 1] := by decide +kernel

/-! ### Bertsekas's price war -/

/-- Three persons who all value objects `0` and `1` at `10` and object `2` at `0` (as costs
`-10, -10, 0`), as in [Bertsekas1998], Figs. 1.12–1.14. -/
def tie : Fin 3 × Fin 3 → ℤ := fun e => if e.2 = 2 then 0 else -10

/-- The row cost range of `tie` is `10`, and `bidBound 3 10 1 = 34`. -/
example : (∀ i j k : Fin 3, tie (i, k) - tie (i, j) ≤ 10) ∧ bidBound 3 10 1 = 34 := by decide

/-- With `ε = 1`, starting from the empty assignment, the persons bid the prices of objects `0`
and `1` up alternately, by `ε` at the first bid and then mostly by `2 ε` per bid (as in
[Bertsekas1998], Fig. 1.14, which starts instead from the partial assignment
`{(1, 1), (2, 2)}`), until both prices reach `C + ε = 11` and object `2` receives a bid: `13`
bids, within the bound `34` of `bids_auction_le`. All assignments are optimal for `tie`, and the
output is `0 ↦ 2, 1 ↦ 0, 2 ↦ 1`. -/
example : (auction tie 1).bids = 13 ∧
    (List.finRange 3).map (auctionPerm tie one_pos) = [2, 0, 1] := by
  decide +kernel

/-- Scaling the costs by `4` scales the price war: `43` bids. -/
example : (auction (fun e => 4 * tie e) 1).bids = 43 := by decide +kernel

/-! ### Boundary cases -/

/-- `n = 0`: there is nobody to assign, so no bids. -/
example : (auction (n := 0) (fun _ => 0) 1).bids = 0 := by decide +kernel

/-- `n = 1`: the single person bids once and raises the price of the single object by `ε`. -/
example : (auction (fun _ : Fin 1 × Fin 1 => 7) 1).bids = 1 ∧
    (auction (fun _ : Fin 1 × Fin 1 => 7) 1).price 0 = 1 := by
  decide +kernel

/-! ### Word-RAM `O(n² (C / ε + 1))` and `O(n³ C + n²)` checks -/

private def emptyInst : Instance := ⟨0, fun _ => 0⟩
private def singleNegInst : Instance := ⟨1, fun _ => -7⟩
private def zeroTieInst : Instance := ⟨3, fun _ => 0⟩
private def c2Inst : Instance := ⟨2, c2⟩
private def c3Inst : Instance := ⟨3, c3⟩
private def tieInst : Instance := ⟨3, tie⟩
private def large12Inst : Instance := ⟨12, fun e => (e.1.val : ℤ) * 7 - (e.2.val : ℤ) * 5⟩

private def emptyEpsInst : EpsInstance := ⟨0, 1, fun _ => 0⟩
private def singleEpsInst : EpsInstance := ⟨1, 3, fun _ => 7⟩
private def c2EpsInst : EpsInstance := ⟨2, 1, c2⟩
private def tieEpsInst : EpsInstance := ⟨3, 1, tie⟩
private def tieEps2Inst : EpsInstance := ⟨3, 2, tie⟩

/-- Ordinary `module` client instantiation of `exists_scaledAuction_program` and
`sum_scaledAuctionPerm_le` across `n = 0` (`w = 4`), negative singleton `n = 1` (`w = 8`),
all-zero `C = 0` (`n = 3`, exercising the `+ n²` term), `c2`, `c3` (at `w = 16` and `w = 64`),
`tie`, and `large12Inst` (`n = 12`, `C = 55`, `w = 64`). -/
example :
    (∀ τ : Equiv.Perm (Fin 3), c3Inst.minCost ≤ ∑ i, c3 (i, τ i)) ∧
    ∃ r K : ℕ, 0 < K ∧ ∃ prog : Program .standard r,
      ¬ prog.ReadsWidth ∧ prog.IsRandFree ∧
      (∃ t, ExecutesList 4 prog (.init emptyInst.encode) [] t ∧ t ≤ K) ∧
      (∃ t, ExecutesList 8 prog (.init singleNegInst.encode) [0] t ∧ t ≤ K * 2) ∧
      (∃ t, ExecutesList 16 prog (.init zeroTieInst.encode) [0, 1, 2] t ∧ t ≤ K * 10) ∧
      (∃ t, ExecutesList 16 prog (.init c2Inst.encode) [0, 1] t ∧ t ≤ K * 21) ∧
      (∃ t, ExecutesList 16 prog (.init c3Inst.encode) [1, 0, 2] t ∧ t ≤ K * 145) ∧
      (∃ t, ExecutesList 64 prog (.init c3Inst.encode) [1, 0, 2] t ∧ t ≤ K * 145) ∧
      (∃ t, ExecutesList 16 prog (.init tieInst.encode) [2, 0, 1] t ∧ t ≤ K * 280) ∧
      (∃ t, ExecutesList 64 prog (.init large12Inst.encode) large12Inst.assignment t ∧
        t ≤ K * 95185) := by
  refine ⟨sum_scaledAuctionPerm_le, ?_⟩
  obtain ⟨r, K, hK, prog, hnw, hrf, hrun, _⟩ := exists_scaledAuction_program
  obtain ⟨t₀, he₀, hl₀⟩ := hrun emptyInst (w := 4) (C := 0) (by decide) (by decide)
  obtain ⟨t₁, he₁, hl₁⟩ := hrun singleNegInst (w := 8) (C := 0) (by decide) (by decide)
  obtain ⟨t₂, he₂, hl₂⟩ := hrun zeroTieInst (w := 16) (C := 0) (by decide) (by decide)
  obtain ⟨t₃, he₃, hl₃⟩ := hrun c2Inst (w := 16) (C := 2) (by decide) (by decide)
  obtain ⟨t₄, he₄, hl₄⟩ := hrun c3Inst (w := 16) (C := 5) (by decide) (by decide)
  obtain ⟨t₅, he₅, hl₅⟩ := hrun c3Inst (w := 64) (C := 5) (by decide) (by decide +kernel)
  obtain ⟨t₆, he₆, hl₆⟩ := hrun tieInst (w := 16) (C := 10) (by decide) (by decide)
  obtain ⟨t₇, he₇, hl₇⟩ := hrun large12Inst (w := 64) (C := 55) (by decide +kernel)
    (by decide +kernel)
  have ha₀ : emptyInst.assignment = [] := by decide +kernel
  have ha₁ : singleNegInst.assignment = [0] := by decide +kernel
  have ha₂ : zeroTieInst.assignment = [0, 1, 2] := by decide +kernel
  have ha₃ : c2Inst.assignment = [0, 1] := by decide +kernel
  have ha₄ : c3Inst.assignment = [1, 0, 2] := by decide +kernel
  have ha₆ : tieInst.assignment = [2, 0, 1] := by decide +kernel
  refine ⟨r, K, hK, prog, hnw, hrf,
    ⟨t₀, ha₀ ▸ he₀, by simpa [emptyInst] using hl₀⟩,
    ⟨t₁, ha₁ ▸ he₁, by simpa [singleNegInst] using hl₁⟩,
    ⟨t₂, ha₂ ▸ he₂, by simpa [zeroTieInst] using hl₂⟩,
    ⟨t₃, ha₃ ▸ he₃, by simpa [c2Inst] using hl₃⟩,
    ⟨t₄, ha₄ ▸ he₄, by simpa [c3Inst] using hl₄⟩,
    ⟨t₅, ha₄ ▸ he₅, by simpa [c3Inst] using hl₅⟩,
    ⟨t₆, ha₆ ▸ he₆, by simpa [tieInst] using hl₆⟩,
    ⟨t₇, he₇, by simpa [large12Inst] using hl₇⟩⟩

/-- Ordinary `module` client instantiation of `exists_scaledMinCost_program` across `n = 0`
(`w = 4`), negative singleton `n = 1` (`cost = -7`, `w = 8`), all-zero `C = 0` (`n = 3`), `c2`,
`c3`, `tie` (`cost = -20`), and `large12Inst` (`n = 12`, `C = 55`, `w = 64`). -/
example :
    ∃ r K : ℕ, 0 < K ∧ ∃ prog : Program .standard r,
      ¬ prog.ReadsWidth ∧ prog.IsRandFree ∧
      (∃ t, Executes 4 prog (.init emptyInst.encode) (Signed.encode 0) t ∧ t ≤ K) ∧
      (∃ t, Executes 8 prog (.init singleNegInst.encode) (Signed.encode (-7)) t ∧ t ≤ K * 2) ∧
      (∃ t, Executes 16 prog (.init zeroTieInst.encode) (Signed.encode 0) t ∧ t ≤ K * 10) ∧
      (∃ t, Executes 16 prog (.init c2Inst.encode) (Signed.encode 1) t ∧ t ≤ K * 21) ∧
      (∃ t, Executes 16 prog (.init c3Inst.encode) (Signed.encode 5) t ∧ t ≤ K * 145) ∧
      (∃ t, Executes 16 prog (.init tieInst.encode) (Signed.encode (-20)) t ∧ t ≤ K * 280) ∧
      (∃ t, Executes 64 prog (.init large12Inst.encode) large12Inst.encodedMinCost t ∧
        t ≤ K * 95185) := by
  obtain ⟨r, K, hK, prog, hnw, hrf, hrun, _⟩ := exists_scaledMinCost_program
  obtain ⟨t₀, he₀, hl₀⟩ := hrun emptyInst (w := 4) (C := 0) (by decide) (by decide)
  obtain ⟨t₁, he₁, hl₁⟩ := hrun singleNegInst (w := 8) (C := 0) (by decide) (by decide)
  obtain ⟨t₂, he₂, hl₂⟩ := hrun zeroTieInst (w := 16) (C := 0) (by decide) (by decide)
  obtain ⟨t₃, he₃, hl₃⟩ := hrun c2Inst (w := 16) (C := 2) (by decide) (by decide)
  obtain ⟨t₄, he₄, hl₄⟩ := hrun c3Inst (w := 16) (C := 5) (by decide) (by decide)
  obtain ⟨t₅, he₅, hl₅⟩ := hrun tieInst (w := 16) (C := 10) (by decide) (by decide)
  obtain ⟨t₆, he₆, hl₆⟩ := hrun large12Inst (w := 64) (C := 55) (by decide +kernel)
    (by decide +kernel)
  have hm₀ : emptyInst.encodedMinCost = Signed.encode 0 := by decide +kernel
  have hm₁ : singleNegInst.encodedMinCost = Signed.encode (-7) := by decide +kernel
  have hm₂ : zeroTieInst.encodedMinCost = Signed.encode 0 := by decide +kernel
  have hm₃ : c2Inst.encodedMinCost = Signed.encode 1 := by decide +kernel
  have hm₄ : c3Inst.encodedMinCost = Signed.encode 5 := by decide +kernel
  have hm₅ : tieInst.encodedMinCost = Signed.encode (-20) := by decide +kernel
  exact ⟨r, K, hK, prog, hnw, hrf,
    ⟨t₀, hm₀ ▸ he₀, by simpa [emptyInst] using hl₀⟩,
    ⟨t₁, hm₁ ▸ he₁, by simpa [singleNegInst] using hl₁⟩,
    ⟨t₂, hm₂ ▸ he₂, by simpa [zeroTieInst] using hl₂⟩,
    ⟨t₃, hm₃ ▸ he₃, by simpa [c2Inst] using hl₃⟩,
    ⟨t₄, hm₄ ▸ he₄, by simpa [c3Inst] using hl₄⟩,
    ⟨t₅, hm₅ ▸ he₅, by simpa [tieInst] using hl₅⟩,
    ⟨t₆, he₆, by simpa [large12Inst] using hl₆⟩⟩

/-- Ordinary `module` client instantiation of `exists_epsAuction_program` across `n = 0` (`w = 4`),
`n = 1` (`ε = 3`, `w = 8`), `c2` (`ε = 1`, suboptimal swap `[1, 0]`), and Bertsekas's price war at
`ε = 1` (`[2, 0, 1]`) and `ε = 2` (`[0, 2, 1]`). -/
example :
    ∃ r K : ℕ, 0 < K ∧ ∃ prog : Program .standard r,
      ¬ prog.ReadsWidth ∧ prog.IsRandFree ∧
      (∃ t, ExecutesList 4 prog (.init emptyEpsInst.encode) [] t ∧ t ≤ K) ∧
      (∃ t, ExecutesList 8 prog (.init singleEpsInst.encode) [0] t ∧ t ≤ K * 2) ∧
      (∃ t, ExecutesList 16 prog (.init c2EpsInst.encode) [1, 0] t ∧ t ≤ K * 13) ∧
      (∃ t, ExecutesList 16 prog (.init tieEpsInst.encode) [2, 0, 1] t ∧ t ≤ K * 100) ∧
      (∃ t, ExecutesList 16 prog (.init tieEps2Inst.encode) [0, 2, 1] t ∧ t ≤ K * 55) := by
  obtain ⟨r, K, hK, prog, hnw, hrf, hrun, _⟩ := exists_epsAuction_program
  obtain ⟨t₀, he₀, hl₀⟩ := hrun emptyEpsInst (w := 4) (C := 0) (by decide) (by decide) (by decide)
  obtain ⟨t₁, he₁, hl₁⟩ := hrun singleEpsInst (w := 8) (C := 0) (by decide) (by decide) (by decide)
  obtain ⟨t₂, he₂, hl₂⟩ := hrun c2EpsInst (w := 16) (C := 2) (by decide) (by decide) (by decide)
  obtain ⟨t₃, he₃, hl₃⟩ := hrun tieEpsInst (w := 16) (C := 10) (by decide) (by decide) (by decide)
  obtain ⟨t₄, he₄, hl₄⟩ := hrun tieEps2Inst (w := 16) (C := 10) (by decide) (by decide) (by decide)
  have ha₀ : emptyEpsInst.assignment = [] := by decide +kernel
  have ha₁ : singleEpsInst.assignment = [0] := by decide +kernel
  have ha₂ : c2EpsInst.assignment = [1, 0] := by decide +kernel
  have ha₃ : tieEpsInst.assignment = [2, 0, 1] := by decide +kernel
  have ha₄ : tieEps2Inst.assignment = [0, 2, 1] := by decide +kernel
  exact ⟨r, K, hK, prog, hnw, hrf,
    ⟨t₀, ha₀ ▸ he₀, by simpa [emptyEpsInst] using hl₀⟩,
    ⟨t₁, ha₁ ▸ he₁, by simpa [singleEpsInst] using hl₁⟩,
    ⟨t₂, ha₂ ▸ he₂, by simpa [c2EpsInst] using hl₂⟩,
    ⟨t₃, ha₃ ▸ he₃, by simpa [tieEpsInst] using hl₃⟩,
    ⟨t₄, ha₄ ▸ he₄, by simpa [tieEps2Inst] using hl₄⟩⟩

end CslibFrontierTests.AuctionAssignment
