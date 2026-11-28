/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Assignment.Auction
public import CslibFrontier.Computability.WordRAM.Realization.Structure

/-!
# Shared workspace layout and memory invariants for Word-RAM auction

Internal workspace layout record (`AuctionWS`), its 10-word faithful `word_enc_structure` encoding,
and the two shared memory invariants connecting Word-RAM state to pure `AuctionState`:

* `Cslib.Algorithms.WordRAM.Auction.AuctionWS`: parameters and base addresses (`bC`, `bOwner`,
  `bPrice`, `bStack`, `outBase`).
* `Cslib.Algorithms.WordRAM.Auction.AuctionMem`: representation predicate pairing a `Memory.State`
  with an unsigned cost matrix `C` and pure `AuctionState ws.n`.
* `Cslib.Algorithms.WordRAM.Auction.ValidWS`: layout contiguity and frontier invariant.

## Main definitions

* `Cslib.Algorithms.WordRAM.Auction.AuctionWS`, `Cslib.Algorithms.WordRAM.Auction.encAuctionWS`:
  workspace record and 10-word encoding.
* `Cslib.Algorithms.WordRAM.Auction.AuctionMem`, `Cslib.Algorithms.WordRAM.Auction.ValidWS`:
  shared memory-representation and layout-validity predicates.

## Main results

* `Cslib.Algorithms.WordRAM.Auction.ValidWS.of_frontier_eq`: transport `ValidWS` across
  frontier-preserving steps.
* `Cslib.Algorithms.WordRAM.Auction.AuctionMem.redCost_read`: shared reduced-cost readout and
  range bound used by both row scans in `Auction.RowScan`.
-/

public section

namespace Cslib.Algorithms.WordRAM.Auction

open Cslib.WordRAM.Realization
open Cslib.DataStructure
open Cslib.Algorithms.Lean.Assignment

/-- Workspace layout and parameters for the memory-client auction solver. -/
structure AuctionWS where
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

/-- Faithful 10-word encoding of `AuctionWS`. -/
word_enc_structure encAuctionWS : AuctionWS where
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

/-- Registered `WordEncoding` for `AuctionWS`. -/
instance : WordEncoding AuctionWS := ⟨10, encAuctionWS⟩

/-- Memory `s` represents pure `st : AuctionState ws.n` over unsigned cost matrix `C` at `ws`. -/
structure AuctionMem (ws : AuctionWS) (C : Fin ws.n × Fin ws.n → ℕ)
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
structure ValidWS (ws : AuctionWS) (s : Memory.State) : Prop where
  /-- `owner` begins immediately after the `n × n` matrix `C`. -/
  hbOwner : ws.bOwner = ws.bC + ws.n * ws.n
  /-- `price` begins immediately after `owner`. -/
  hbPrice : ws.bPrice = ws.bOwner + ws.n
  /-- `stack` begins immediately after `price`. -/
  hbStack : ws.bStack = ws.bPrice + ws.n
  /-- Length-prefixed output array begins immediately after `stack`. -/
  houtBase : ws.outBase = ws.bStack + ws.n
  /-- Allocated frontier covers the entire output buffer (`n + 1` words). -/
  hfrontier : ws.outBase + ws.n + 1 ≤ s.frontier

/-- `ValidWS` is preserved by any memory step that leaves `frontier` unchanged. -/
theorem ValidWS.of_frontier_eq {ws : AuctionWS} {s s' : Memory.State}
    (h : ValidWS ws s) (hfr : s'.frontier = s.frontier) : ValidWS ws s' :=
  ⟨h.hbOwner, h.hbPrice, h.hbStack, h.houtBase, hfr ▸ h.hfrontier⟩

/-- Reading `C[i₀, j]` and `price[j]` in memory computes
`redCost (fun e => (C e : ℤ)) st.price i₀ j` and stays bounded by `2 * W + ws.eps`. Shared by
both row scans in `Auction.RowScan`. -/
theorem AuctionMem.redCost_read {W : ℕ} {ws : AuctionWS} {C : Fin ws.n × Fin ws.n → ℕ}
    {st : AuctionState ws.n} {s : Memory.State} (ham : AuctionMem ws C st s)
    (hC_le : ∀ i j : Fin ws.n, C (i, j) ≤ W)
    (hp_nn : ∀ j : Fin ws.n, 0 ≤ st.price j)
    (hp_le : ∀ j : Fin ws.n, st.price j ≤ (W + ws.eps : ℤ))
    (i₀ j : Fin ws.n) :
    let rc := s.mem (ws.bC + i₀.val * ws.n + j.val) + s.mem (ws.bPrice + j.val)
    rc ≤ 2 * W + ws.eps ∧
      (rc : ℤ) = redCost (fun e => (C e : ℤ)) st.price i₀ j := by
  have h1 := hC_le i₀ j
  have h2 := hp_nn j
  have h3 := hp_le j
  dsimp only [redCost]
  rw [Nat.add_assoc, ham.hC, ham.hPrice]
  omega

end Cslib.Algorithms.WordRAM.Auction
