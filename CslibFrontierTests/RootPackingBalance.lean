/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootPackingBalance.TerminalVerifier

open Turing MultiTapeATM MultiTapeTM MultiTapePTM Cslib RootPackingBalance
open RootPredecessorGraph (vertexCount)

-- The same single-tape-source verifier accepts an empty root graph and rejects an occupied
-- graph with only two edges and 4096 possible classes. Both start on the actual public word.
example : ∃ (K : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM K Bool Q) (C E : ℕ),
    ∀ {S : Type} (_M : MultiTapePTM 0 Bool S) (_input : List Bool) (b σ : ℕ)
      (_code : BlockLetter 0 S b → Fin 1 → Bool)
      (s₀ : BalancedSchedules.SeededLabels.Seed (vertexCount 0 0 1) 6)
      (s₁ : BalancedSchedules.SeededLabels.Seed (vertexCount 0 1 1) 6),
      let accepts := fun p : RootBalanceRequest.Public =>
        atm.AcceptsWithin (C * (p.1.raw.length + Initialize.shortSize p ^ E + 1))
          (atm.toPTM.toNTM.initCfg (RootBalanceRequest.encPublic p))
      accepts (graphPublic 0 0 1 σ 1 s₀) ∧ ¬ accepts (graphPublic 0 1 1 σ 1 s₁) := by
  obtain ⟨K, Q, hQ, atm, C, E, h⟩ := exists_balance_verifier 0
  refine ⟨K, Q, hQ, atm, C, E, ?_⟩
  intro S M input b σ code s₀ s₁
  constructor
  · apply (h M input b σ code 1 s₀).2.mpr
    apply (PacketPacking.Seeded.balanced_iff_rank_succ_mul_le _ _ _ _ _ _).2
    exact fun e => Fin.elim0 e
  · intro ha
    have hb := (h M input b σ code 1 s₁).2.mp ha
    have he := (PacketPacking.Seeded.balanced_iff_rank_succ_mul_le _ _ _ _ _ _).1 hb 0
    norm_num [RootPredecessorGraph.edgeCount] at he
    omega
