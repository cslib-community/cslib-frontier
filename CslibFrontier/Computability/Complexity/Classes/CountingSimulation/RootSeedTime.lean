/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.RootRankTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootSeedChoice.Verifier

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootSeedExistence

/-!
# Choosing and verifying a root seed within the source block budget

The public input contains the represented root schedule and metadata. The verifier chooses
the coefficients itself. All its branches halt within the square-root-logarithmic budget,
including branches whose seed fails the balance test.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM _root_.Turing.MultiTapeATM

/-- The existence of a balanced seed is checked on the actual source reduction's root graph. -/
@[expose] def SelectsRootSeed {u : ℕ} {Q : Type} (atm : MultiTapeATM u Bool Q) (k states : ℕ)
    (clock : ℕ → ℕ) : Prop :=
  ∀ {State : Type} (M : MultiTapePTM k Bool State) (st : State ≃ Fin states)
    (input : List Bool) (t σ a : ℕ) (_ha : 64 ^ a ≤ rootEdges k states t),
    let q := numBlocks t
    let m := rootCopies k states t
    let U := rootVertices k states t
    let p := RootPackingBalance.graphPublic k q m σ a (RootSeedChoice.zeroSeed U a)
    let cfg := atm.toPTM.toNTM.initCfg (RootBalanceRequest.encPublic p)
    atm.HaltsWithin (clock t) cfg ∧ (atm.AcceptsWithin (clock t) cfg ↔
      ∃ seed, PacketPacking.Seeded.Balanced U a (explicitVertexEquiv k q m).toEmbedding
        (RootPredecessorGraph.rowOf M input (blockLength t) σ (letterCode st))
        (RootPredecessorGraph.colOf k q m) seed)

/-- With the variance bound used by the packing construction, the ATM has an accepting
choice on the source graph. No supplied seed or balance certificate appears in the input. -/
theorem SelectsRootSeed.accepts_of_variance {u k states : ℕ} {Q State : Type}
    {atm : MultiTapeATM u Bool Q} {clock : ℕ → ℕ} (h : SelectsRootSeed atm k states clock)
    (M : MultiTapePTM k Bool State) (st : State ≃ Fin states) (input : List Bool) (t σ a : ℕ)
    (hsize : 2 * (2 * (3 * k + 1) * rootCopies k states t) * (64 ^ (2 * a)) ^ 2 ≤
      rootEdges k states t) :
    let U := rootVertices k states t
    let p := RootPackingBalance.graphPublic k (numBlocks t) (rootCopies k states t) σ a
      (RootSeedChoice.zeroSeed U a)
    atm.AcceptsWithin (clock t) (atm.toPTM.toNTM.initCfg (RootBalanceRequest.encPublic p)) := by
  have hc : 0 < rootCopies k states t :=
    Nat.mul_pos (by omega) (one_le_blockLength t)
  have ha : 64 ^ a ≤ rootEdges k states t := by
    have hm : 0 < 2 * (2 * (3 * k + 1) * rootCopies k states t) := by positivity
    have hg : 64 ^ a ≤ 64 ^ (2 * a) := Nat.pow_le_pow_right (by decide) (by omega)
    have hsq : 64 ^ (2 * a) ≤ (64 ^ (2 * a)) ^ 2 := by
      simpa only [pow_one] using Nat.pow_le_pow_right
        (n := 64 ^ (2 * a)) (Nat.pow_pos (by decide : 0 < 64))
        (by decide : 1 ≤ 2)
    exact hg.trans (hsq.trans ((Nat.le_mul_of_pos_left _ hm).trans hsize))
  apply (h M st input t σ a ha).2.mpr
  exact RootPredecessorGraph.exists_balanced_seed M input (blockLength t) σ (letterCode st) a
    hc hsize

/-- Ordinary-input root seed choice and balance verification fit the square-root-log clock. -/
theorem exists_rootSeed_verifier_div_sqrt_log (k states : ℕ) :
    ∃ (u : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM u Bool Q) (K : ℕ),
      SelectsRootSeed atm k states (fun t => K * (t / (Nat.log 2 (t + 2)).sqrt + 2)) := by
  obtain ⟨u, Q, hQ, atm, C, D, h⟩ := RootSeedChoice.exists_verifier k
  obtain ⟨K, hbound⟩ := zero_indices_clock_le_numBlocks k states C D
  refine ⟨u, Q, hQ, atm, K, ?_⟩
  intro State M st input t σ a ha
  obtain ⟨hh, hv⟩ := h M input (blockLength t) σ (letterCode st) a
  have ht := (hbound t σ a ha (RootSeedChoice.zeroSeed _ _)).trans
    (Nat.mul_le_mul_left K (Nat.succ_le_succ (numBlocks_le_div_sqrt_log_add_one t)))
  exact ⟨hh.mono ht, ⟨fun hx => hv.mp (hx.of_halted_stepCoins hh), fun hx => (hv.mpr hx).mono ht⟩⟩

end Cslib.Complexity.CountingSimulation
