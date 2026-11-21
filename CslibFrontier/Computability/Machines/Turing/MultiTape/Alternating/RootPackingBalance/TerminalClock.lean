/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootBalanceRequest
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Fields

/-!
# The clock of the balance-checking terminal

The three move fields have total length at most three times the binary length of the number
of edges. The terminal head rewind, native request assembly and rank-bit evaluator share a
single bound linear in the long schedule and polynomial in the public numeric metadata.
-/

public section

namespace Turing.MultiTapeATM.RootPackingBalance

open Cslib MultiTapeTM RootBalanceRequest

/-- The challenge-length prefix, ordinary word compiler and rank-bit evaluator have a common
clock for every choice of those bits, with constants fixed by the machines. -/
theorem terminal_clock (c d A D : ℕ) : ∃ C E, ∀ (p : RootBalanceRequest.Public)
    (choices : List Bool), choices.length = (QuantifiedWord.rankFlags (Nat.clog 2 p.2)).length →
    let x : RootBalanceRequest.Input := (p, choices)
    let params := (prepare x).2
    (encInput x).length + c * (p.1.raw.length + shortSize x ^ d + 1) + 8 +
      A * ((selected x).raw.length +
        (RootPredecessorQuery.shortSize (selected x) + params.count.size +
          params.query.width.size + 1) ^ D + 1) ≤
      C * (p.1.raw.length + (RootPredecessorQuery.shortSize p.1 + p.2.size + 1) ^ E + 1) := by
  let S (p : RootBalanceRequest.Public) := RootPredecessorQuery.shortSize p.1 + p.2.size + 1
  let P (m : ℕ) := 8 * (4 * m + 2) + c * ((4 * m) ^ d + 1) + 8 +
    A * ((4 * m + 2) ^ D + 1)
  have hP : PolynomiallyBounded P := by dsimp [P]; fun_prop
  obtain ⟨C, E, h⟩ := (PolyBounded.of_polynomiallyBounded S hP).exists_le_linear_add_pow
    (fun p => p.1.raw.length) (8 + c + A) (fun p => by simp [S])
  refine ⟨C, E, fun p choices hchoices => ?_⟩
  dsimp only
  let x : RootBalanceRequest.Input := (p, choices)
  have hn : Nat.clog 2 p.2 ≤ p.2.size := Nat.clog_le_of_le_pow (Nat.lt_size_self _).le
  have hw : Nat.clog 2 (Nat.clog 2 p.2) ≤ Nat.clog 2 p.2 :=
    (Nat.clog_le_of_le_pow (Nat.lt_size_self _).le).trans (Nat.size_le_self _)
  rw [QuantifiedWord.length_rankFlags] at hchoices
  have hs : shortSize x ≤ 4 * S p := by
    dsimp [shortSize, rootQuery, edgeCount, x, S]
    omega
  have hparams := RootBalanceRequest.parameter_sizes x
  have hselected := shortSize_selected_le x
  have hy : RootPredecessorQuery.shortSize (selected x) + (prepare x).2.count.size +
      (prepare x).2.query.width.size + 1 ≤ 4 * S p + 2 := by
    change RootPredecessorQuery.shortSize (selected x) ≤
      RootPredecessorQuery.shortSize p.1 + 2 * p.2.size at hselected
    change _ ≤ p.2.size ∧ _ ≤ p.2.size + 1 at hparams
    dsimp [S]
    omega
  have hraw : (selected x).raw = p.1.raw := rfl
  change (encInput x).length + c * (p.1.raw.length + shortSize x ^ d + 1) + 8 +
    A * ((selected x).raw.length + _ ^ D + 1) ≤ _
  rw [hraw]
  refine le_trans ?_ (h p)
  calc
    _ ≤ (8 * p.1.raw.length + 8 * (4 * S p + 2)) +
        c * (p.1.raw.length + (4 * S p) ^ d + 1) + 8 +
          A * (p.1.raw.length + (4 * S p + 2) ^ D + 1) := by
      have hlen := length_encInput_le x
      change (encInput x).length ≤ 8 * p.1.raw.length + 8 * (shortSize x + 2) at hlen
      gcongr
      exact hlen.trans (by gcongr)
    _ = (8 + c + A) * p.1.raw.length + P (S p) := by dsimp [P]; ring

end Turing.MultiTapeATM.RootPackingBalance
