/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.RootRankTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootPackingBalance.TerminalVerifier

/-!
# Root seed balance at the source time scale

The complete native verifier reads a schedule row for each logarithmic block of the source
computation. Its edge and seed arithmetic is polynomial in the encoded short fields and fits
within the block budget. This gives an unconditional square-root-logarithmic time bound for
checking a supplied seed at the root of the packing construction.
-/

public section
namespace Cslib.Complexity.CountingSimulation

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM _root_.Turing.MultiTapeATM

/-- A native verifier for the actual source reduction's root seed, started on the public
serialized schedule and parameters. The branch bound covers rejected seeds as well as witnesses. -/
@[expose] def VerifiesRootBalance {u : ℕ} {Q : Type} (atm : MultiTapeATM u Bool Q)
    (k states : ℕ) (clock : ℕ → ℕ) : Prop :=
  ∀ {State : Type} (M : MultiTapePTM k Bool State) (st : State ≃ Fin states)
    (input : List Bool) (t σ a : ℕ) (_ha : 64 ^ a ≤ rootEdges k states t)
    (seed : BalancedSchedules.SeededLabels.Seed (rootVertices k states t) (6 * a)),
    let q := numBlocks t
    let m := rootCopies k states t
    let p := RootPackingBalance.graphPublic k q m σ a seed
    let cfg := atm.toPTM.toNTM.initCfg (RootBalanceRequest.encPublic p)
    atm.HaltsWithin (clock t) cfg ∧ (atm.AcceptsWithin (clock t) cfg ↔
      PacketPacking.Seeded.Balanced (rootVertices k states t) a
        (explicitVertexEquiv k q m).toEmbedding
        (RootPredecessorGraph.rowOf M input (blockLength t) σ (letterCode st))
        (RootPredecessorGraph.colOf k q m) seed)

/-- Increasing the clock preserves each verdict because all branches halted by the old clock. -/
theorem VerifiesRootBalance.mono {u : ℕ} {Q : Type} {atm : MultiTapeATM u Bool Q}
    {k states : ℕ} {t₁ t₂ : ℕ → ℕ} (h : VerifiesRootBalance atm k states t₁)
    (hle : ∀ t, t₁ t ≤ t₂ t) : VerifiesRootBalance atm k states t₂ := by
  intro State M st input t σ a ha seed
  obtain ⟨hh, hv⟩ := h M st input t σ a ha seed
  exact ⟨hh.mono (hle t), ⟨fun hx => hv.mp (hx.of_halted_stepCoins hh),
    fun hx => (hv.mpr hx).mono (hle t)⟩⟩

/-- Every proposed root seed can be verified by one alternating machine in linear block time. -/
theorem exists_rootBalance_verifier_numBlocks (k states : ℕ) :
    ∃ (u : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM u Bool Q) (K : ℕ),
      VerifiesRootBalance atm k states (fun t => K * (numBlocks t + 1)) := by
  obtain ⟨u, Q, hQ, atm, C, D, h⟩ := RootPackingBalance.exists_balance_verifier k
  obtain ⟨K, hbound⟩ := zero_indices_clock_le_numBlocks k states C D
  refine ⟨u, Q, hQ, atm, K, ?_⟩
  intro State M st input t σ a ha seed
  obtain ⟨hh, hv⟩ := h M input (blockLength t) σ (letterCode st) a seed
  have ht := hbound t σ a ha seed
  exact ⟨hh.mono ht, ⟨fun hx => hv.mp (hx.of_halted_stepCoins hh), fun hx => (hv.mpr hx).mono ht⟩⟩

/-- The physical root balance verifier meets the `t / √(log₂(t + 2))` budget up to a
constant additive allowance inside the clock, including at the smallest source times. -/
theorem exists_rootBalance_verifier_div_sqrt_log (k states : ℕ) :
    ∃ (u : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM u Bool Q) (K : ℕ),
      VerifiesRootBalance atm k states (fun t => K * (t / (Nat.log 2 (t + 2)).sqrt + 2)) := by
  obtain ⟨u, Q, hQ, atm, K, h⟩ := exists_rootBalance_verifier_numBlocks k states
  exact ⟨u, Q, hQ, atm, K, h.mono fun t => Nat.mul_le_mul_left _
    (Nat.succ_le_succ (numBlocks_le_div_sqrt_log_add_one t))⟩

end Cslib.Complexity.CountingSimulation
