/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Lean.Assignment.Auction
import CslibFrontier.Algorithms.WordRAM.Auction
meta import CslibFrontier.Algorithms.WordRAM.Auction
meta import CslibFrontier.Computability.WordRAM.Structured.FastEval
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Perm

/-!
# Auction algorithm for the assignment problem: checked instances

Kernel-checked (`decide +kernel`, no `native_decide`) pure and Word-RAM runs of Bertsekas's
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
5. **Word-RAM `O(n² (C / ε + 1))` `ε`-auction and `O(n³ C)` exact scaled auction:** ordinary
   `module` client instantiations of `executesList_epsAuction`, `executesList_scaledAuction`,
   `executes_scaledMinCost`, and `sum_scaledAuctionPerm_le`, plus compiled
   `Program.runFast` / `Program.runFastList` runs across `n = 0`, `n = 1`, zero/tie weights,
   `c2`, `c3`, Bertsekas's price war, an `n = 12` instance at `w = 64`, width invariance, and
   narrow-width fault cases.
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

/-! ### Word-RAM `O(n² (C / ε + 1))` and `O(n³ C)` checks -/

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

/-- Ordinary `module` client instantiation of `executesList_scaledAuction`,
`executes_scaledMinCost`, and `sum_scaledAuctionPerm_le` on `c3Inst` (`C = 5`, `w = 16`). -/
example :
    (∀ τ : Equiv.Perm (Fin 3), c3Inst.minCost ≤ ∑ i, c3 (i, τ i)) ∧
    (∃ steps, ExecutesList 16 scaledAuctionProgram (.init c3Inst.encode) [1, 0, 2] steps ∧
      steps ≤ scaledAuctionTime 3 5) ∧
    (∃ steps, Executes 16 scaledMinCostProgram (.init c3Inst.encode) (Signed.encode 5) steps ∧
      steps ≤ scaledAuctionTime 3 5) := by
  have h1 := executesList_scaledAuction c3Inst (w := 16) (C := 5) (by decide) (by decide)
  have h2 := executes_scaledMinCost c3Inst (w := 16) (C := 5) (by decide) (by decide)
  have ha : c3Inst.assignment = [1, 0, 2] := by decide +kernel
  have hm : c3Inst.encodedMinCost = Signed.encode 5 := by decide +kernel
  rw [ha] at h1
  rw [hm] at h2
  exact ⟨sum_scaledAuctionPerm_le, h1, h2⟩

/-- Ordinary `module` client instantiation of `executesList_epsAuction` on Bertsekas's price-war
instance `tieEpsInst` (`C = 10`, `ε = 1`, `w = 16`). -/
example : ∃ steps,
    ExecutesList 16 epsAuctionProgram (.init tieEpsInst.encode) [2, 0, 1] steps ∧
      steps ≤ epsAuctionTime 3 10 1 := by
  have h := executesList_epsAuction tieEpsInst (w := 16) (C := 10) (by decide) (by decide)
    (by decide)
  have ha : tieEpsInst.assignment = [2, 0, 1] := by decide +kernel
  rwa [ha] at h

/-- Boundary `n = 0` (`w = 4`) and negative singleton `n = 1` (`cost = -7`, `w = 8`) Word-RAM
instantiations, plus logarithmic word width (`w = 64`) on `n = 12` (`large12Inst`). -/
example :
    (∃ steps, ExecutesList 4 scaledAuctionProgram (.init emptyInst.encode) [] steps ∧
      steps ≤ scaledAuctionTime 0 0) ∧
    (∃ steps, Executes 8 scaledMinCostProgram (.init singleNegInst.encode)
      (Signed.encode (-7)) steps ∧ steps ≤ scaledAuctionTime 1 0) ∧
    Fits 64 large12Inst.wordBound := by
  have h0 := executesList_scaledAuction emptyInst (w := 4) (C := 0) (by decide) (by decide)
  have h1 := executes_scaledMinCost singleNegInst (w := 8) (C := 0) (by decide) (by decide)
  have hm1 : singleNegInst.encodedMinCost = Signed.encode (-7) := by decide +kernel
  rw [hm1] at h1
  exact ⟨h0, h1, by decide +kernel⟩

private meta def checkScaled (w C : ℕ) (inst : Instance) (expectedAssign : List ℕ)
    (expectedCost : ℤ) : Bool :=
  let budget := scaledAuctionTime inst.n C
  match Program.runFastList w budget scaledAuctionProgram inst.encode,
      Program.runFast w budget scaledMinCostProgram inst.encode with
  | some (assign, s₁), some (encCost, s₂) =>
    assign == expectedAssign && Signed.decode encCost == expectedCost &&
      s₁ ≤ budget && s₂ ≤ budget
  | _, _ => false

private meta def checkEps (w C : ℕ) (inst : EpsInstance) (expectedAssign : List ℕ) : Bool :=
  let budget := epsAuctionTime inst.n C inst.eps
  match Program.runFastList w budget epsAuctionProgram inst.encode with
  | some (assign, steps) => assign == expectedAssign && steps ≤ budget
  | none => false

/-- info: true -/
#guard_msgs in
#eval checkScaled 16 0 emptyInst [] 0

/-- info: true -/
#guard_msgs in
#eval checkScaled 16 0 singleNegInst [0] (-7)

/-- info: true -/
#guard_msgs in
#eval checkScaled 16 0 zeroTieInst [0, 1, 2] 0

/-- info: true -/
#guard_msgs in
#eval checkScaled 16 2 c2Inst [0, 1] 1

/-- info: true -/
#guard_msgs in
#eval checkScaled 16 5 c3Inst [1, 0, 2] 5

/-- info: true -/
#guard_msgs in
#eval checkScaled 16 10 tieInst [2, 0, 1] (-20)

/-- info: true -/
#guard_msgs in
#eval checkEps 16 0 emptyEpsInst []

/-- info: true -/
#guard_msgs in
#eval checkEps 16 0 singleEpsInst [0]

/-- info: true -/
#guard_msgs in
#eval checkEps 16 2 c2EpsInst [1, 0]

/-- info: true -/
#guard_msgs in
#eval checkEps 16 10 tieEpsInst [2, 0, 1]

/-- info: true -/
#guard_msgs in
#eval checkEps 16 10 tieEps2Inst [0, 2, 1]

-- Width invariance (`w = 16` vs `w = 64`) and narrow-width fault (`w = 2`).
/-- info: true -/
#guard_msgs in
#eval decide (Program.runFastList 16 50000 scaledAuctionProgram c3Inst.encode =
    Program.runFastList 64 50000 scaledAuctionProgram c3Inst.encode ∧
  Program.runFastList 16 50000 epsAuctionProgram tieEpsInst.encode =
    Program.runFastList 64 50000 epsAuctionProgram tieEpsInst.encode ∧
  Program.runFastList 2 5000 scaledAuctionProgram c3Inst.encode = none)

end CslibFrontierTests.AuctionAssignment
