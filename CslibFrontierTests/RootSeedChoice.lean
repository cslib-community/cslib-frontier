/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootSeedChoice.Verifier

open Turing MultiTapeATM MultiTapeTM MultiTapePTM Cslib RootPackingBalance RootSeedChoice
open RootPredecessorGraph (vertexCount)

-- The first graph has a valid seed. On the second graph every possible coefficient choice fails.
example : ∃ (K : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM K Bool Q) (C E : ℕ),
    ∀ {S : Type} (_M : MultiTapePTM 0 Bool S) (_input : List Bool) (b σ : ℕ)
      (_code : BlockLetter 0 S b → Fin 1 → Bool),
      let accepts := fun q =>
        let p := graphPublic 0 q 1 σ 1 (zeroSeed (vertexCount 0 q 1) 1)
        atm.AcceptsWithin (C * (p.1.raw.length + Initialize.shortSize p ^ E + 1))
          (atm.toPTM.toNTM.initCfg (RootBalanceRequest.encPublic p))
      accepts 0 ∧ ¬ accepts 1 := by
  obtain ⟨K, Q, hQ, atm, C, E, h⟩ := exists_verifier 0
  refine ⟨K, Q, hQ, atm, C, E, ?_⟩
  intro S M input b σ code
  constructor
  · apply (h (q := 0) M input b σ code 1).2.mpr
    refine ⟨zeroSeed _ _, (PacketPacking.Seeded.balanced_iff_rank_succ_mul_le _ _ _ _ _ _).2 ?_⟩
    exact fun e => Fin.elim0 e
  · intro acc
    obtain ⟨seed, hb⟩ := (h (q := 1) M input b σ code 1).2.mp acc
    have he := (PacketPacking.Seeded.balanced_iff_rank_succ_mul_le _ _ _ _ _ seed).1 hb 0
    norm_num [RootPredecessorGraph.edgeCount] at he
    omega
