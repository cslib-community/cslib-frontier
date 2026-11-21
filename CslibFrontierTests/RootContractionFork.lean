/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.RootContractionSchedule

open Turing MultiTapeTM MultiTapePTM MultiTapeATM Cslib RootPackingBalance RootSeedChoice
open RootPredecessorGraph (vertexCount)

/- The nonempty two-half-edge graph has a single class at label length zero. Its branch predicate
reads the actual seeded public word and requires the original index and a positive claim. -/
example {S : Type} (M : MultiTapePTM 0 Bool S) (input : List Bool) (b σ bit : ℕ)
    (code : BlockLetter 0 S b → Fin 1 → Bool) (claim : Bool) :
    let p := queryPublic 0 1 1 σ 0 (zeroSeed (vertexCount 0 1 1) 0) bit claim
    QuantifiedWord.plays (fun choices =>
      let x := RootSeedInstall.install (p, choices)
      terminalValue 0 x ∧ (x.1.1.context.edge = bit ∧ x.1.1.context.candidate = 1)) [] (flags p) ↔
      claim = true := by
  let post := fun p' : RootBalanceRequest.Public =>
    p'.1.context.edge = bit ∧ p'.1.context.candidate = 1
  apply (plays_iff_balanced_and M input b σ code 0 bit claim post).trans
  constructor
  · rintro ⟨_, _, h⟩
    change bit = bit ∧ claim.toNat = 1 at h
    cases claim <;> simp_all
  · rintro rfl
    let seed := zeroSeed (vertexCount 0 1 1) 0
    refine ⟨seed, (PacketPacking.Seeded.balanced_iff_rank_succ_mul_le _ _ _ _ _ seed).2 ?_,
      ⟨rfl, rfl⟩⟩
    intro e
    have hr := PacketPacking.Seeded.rank_lt_card (vertexCount 0 1 1) 0
      (explicitVertexEquiv 0 1 1).toEmbedding (RootPredecessorGraph.rowOf M input b σ code)
      (RootPredecessorGraph.colOf 0 1 1) seed e
    simp only [Nat.mul_zero, pow_zero, Nat.mul_one]
    omega
