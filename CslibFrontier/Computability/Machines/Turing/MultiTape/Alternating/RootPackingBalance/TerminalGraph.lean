/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootPackingBalance.Terminal
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootPackingBalance.Prefix

/-!
# The physical challenge game checks the given graph's seed

A padded edge wins its terminal. A genuine edge requires a fitting rank, and every valid
bit challenge reaches a count on that edge with the seed unchanged. The initial public data
can represent an empty graph, since constructing them never requires an inhabitant of the edges.
-/

public section
namespace Turing.MultiTapeATM.RootPackingBalance

open MultiTapeTM MultiTapePTM Cslib QuantifiedWord BitString
open RootPredecessorGraph (edgeCount vertexCount graphInput)
open RootBalanceRequest (Public prepare selected challenge withEdge)

/-- Initial public word for a represented graph. The seed is supplied without a balance proof. -/
@[expose] def graphPublic (k q copies σ a : ℕ)
    (seed : BalancedSchedules.SeededLabels.Seed (vertexCount k q copies) (6 * a)) : Public :=
  (RootPredecessorGraph.inputOfIndices k q copies σ a seed 0 0, edgeCount k q copies)

private theorem terminal_constant (k : ℕ) (x : RootBalanceRequest.Input) (b : Bool)
    (hb : SeededRankChallenge.run (challenge x) = .inl b) : terminalValue k x ↔ b = true := by
  cases b <;> simp [terminalValue, prepare, SeededRankRequest.run_of_terminal _ _ hb]

variable {k q copies : ℕ} {S : Type} (M : MultiTapePTM k Bool S) (input : List Bool)
  (b σ : ℕ) (code : BlockLetter k S b → Fin copies → Bool) (a : ℕ)
  (seed : BalancedSchedules.SeededLabels.Seed (vertexCount k q copies) (6 * a))

private theorem terminal_count (choices : List Bool) (e : Fin (edgeCount k q copies))
    (j : ℕ) (claim : Bool)
    (h : SeededRankChallenge.run (challenge (graphPublic k q copies σ a seed, choices)) =
      .inr ⟨e.val, j, claim⟩) : terminalValue k (graphPublic k q copies σ a seed, choices) ↔
      (PacketPacking.Seeded.rank (vertexCount k q copies) a
        (explicitVertexEquiv k q copies).toEmbedding
        (RootPredecessorGraph.rowOf M input b σ code) (RootPredecessorGraph.colOf k q copies)
        seed e).testBit j = claim := by
  simp only [terminalValue, prepare, selected, SeededRankRequest.run_of_query _ _ h]
  rw [← RootPackingRank.sum_eq_rank M input b σ code a seed e]
  rfl

/-- The quantified choices with the physical count terminals characterize balance, including
padded edges and bit indices, for all proposed seeds. -/
theorem plays_iff_balanced :
    let p := graphPublic k q copies σ a seed
    plays (fun choices => terminalValue k (p, choices)) [] (rankFlags (Nat.clog 2 p.2)) ↔
      PacketPacking.Seeded.Balanced (vertexCount k q copies) a
        (explicitVertexEquiv k q copies).toEmbedding
        (RootPredecessorGraph.rowOf M input b σ code)
        (RootPredecessorGraph.colOf k q copies) seed := by
  let n := edgeCount k q copies
  let w := Nat.clog 2 n
  let p := graphPublic k q copies σ a seed
  let rank := PacketPacking.Seeded.rank (vertexCount k q copies) a
    (explicitVertexEquiv k q copies).toEmbedding (RootPredecessorGraph.rowOf M input b σ code)
    (RootPredecessorGraph.colOf k q copies) seed
  have ht := plays_rankFlags_iff_local n w (Nat.le_pow_clog (by decide) n)
    (fun choices => terminalValue k (p, choices))
    (fun g => (g.val + 1) * 64 ^ (2 * a) ≤ 2 * n)
    (fun e g j => (rank e).testBit j.val = g.val.testBit j.val) (by
      intro e g j
      let choices := lowBits w e.val ++ lowBits w g.val ++ lowBits (Nat.clog 2 w) j.val
      have hd := SeededRankChallenge.run_lowBits n a e.val g.val j.val e.isLt g.isLt j.isLt
      change SeededRankChallenge.run (challenge (p, _)) = _ at hd
      rw [← List.append_assoc] at hd
      by_cases he : e.val < n
      · by_cases hg : (g.val + 1) * 64 ^ (2 * a) ≤ 2 * n
        · by_cases hj : j.val < w
          · have hq : SeededRankChallenge.run (challenge (p, choices)) =
                .inr ⟨e.val, j.val, g.val.testBit j.val⟩ := by
              simpa only [he, hg, show j.val < Nat.clog 2 n from hj, ↓reduceIte] using hd
            have hv := terminal_count M input b σ code a seed choices ⟨e.val, he⟩ j.val _ hq
            simpa [he, hg, hj, choices, rank] using hv
          · have hq : SeededRankChallenge.run (challenge (p, choices)) = .inl true := by
              simpa only [he, hg, show ¬j.val < Nat.clog 2 n from hj, ↓reduceIte] using hd
            simpa [he, hg, hj, choices] using terminal_constant k (p, choices) true hq
        · have hq : SeededRankChallenge.run (challenge (p, choices)) = .inl false := by
            simpa only [he, hg, ↓reduceIte] using hd
          simpa [he, hg, choices] using terminal_constant k (p, choices) false hq
      · have hq : SeededRankChallenge.run (challenge (p, choices)) = .inl true := by
          simpa only [he, ↓reduceIte] using hd
        simpa [he, choices] using terminal_constant k (p, choices) true hq)
  have hb := PacketPacking.Seeded.balanced_iff_rank_bit_checks (vertexCount k q copies) a
    (explicitVertexEquiv k q copies).toEmbedding (RootPredecessorGraph.rowOf M input b σ code)
    (RootPredecessorGraph.colOf k q copies) seed (width := w)
    (by simpa only [Fintype.card_fin] using Nat.le_pow_clog (by decide : 1 < 2) n)
    (fun e j b => (rank e).testBit j.val = b) (fun _ _ _ => Iff.rfl)
  exact ht.trans (by simpa only [Fintype.card_fin] using hb.symm)

end Turing.MultiTapeATM.RootPackingBalance
