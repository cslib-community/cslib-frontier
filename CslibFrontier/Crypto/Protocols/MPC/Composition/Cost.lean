/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Composition.Hybrid

/-!
# The hybrid bound of a composed protocol with an arbitrary per-round cost

`Composition.replacementBound` is the sum over the oracle rounds of a composed protocol of the
expected semi-honest advantage of the round's distinguisher (`Composition.roundDistinguisher`)
against the round's subprotocol. When a subprotocol is itself a composed protocol, its advantage is
in turn bounded by an expression in other distinguishers, so stacking the hybrid argument through
nested compositions needs the same sum with that expression in place of the advantage.

`Composition.replacementCost` is that sum for an arbitrary per-round cost: a function of the
round's operation, its corrupted slots, its query tuple and its distinguisher. It is the recursion
of `Composition.replacementBound` with the cost in place of the semi-honest advantage, it is
`Composition.replacementBound` at the advantage, and it is monotone in the cost, so a pointwise
bound on the advantages of the subprotocols by a cost bounds `Composition.replacementBound`.

Everything here is original bookkeeping for stacking the hybrid argument through nested
compositions with explicit per-distinguisher reductions, not a cited statement. The bounds are
concrete: fixed states and distinguisher, no security parameter, and no efficiency claim about the
round distinguishers or about the cost.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.Composition.replacementCost`: the sum over the oracle rounds of the
  expected cost of the round distinguishers.

## Main results

* `Cslib.Crypto.Protocols.MPC.Composition.replacementBound_eq_replacementCost`: the hybrid bound
  is the cost sum at the semi-honest advantage.
* `Cslib.Crypto.Protocols.MPC.Composition.replacementCost_mono`: the cost sum is monotone in the
  cost.
* `Cslib.Crypto.Protocols.MPC.Composition.replacementBound_le_replacementCost`: a pointwise bound
  on the advantages by a cost bounds the hybrid bound by the cost sum.
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib.Probability Cslib.ProbComp
open _root_.Cslib.Crypto.Protocols.MPC.Composition
open scoped ENNReal

namespace Composition

variable {m : ℕ} {spec₁ spec₂ : MultiOracleSpec}
  {sc₂ : (op : spec₁.Op) → Schedule (spec₁.arity op) spec₂}
  {Coins₂ : (op : spec₁.Op) → Fin (spec₁.arity op) → Type}

/-- **The hybrid sum with an arbitrary per-round cost.** For the outer steps `steps` from the
states `st` and a test `D` of the kernel program's result, the sum over the oracle rounds of
`steps` of the expected value of `cost` at the round's operation, its corrupted slots
`subCoalition parties I`, its query tuple and its distinguisher (`roundDistinguisher`). The
expectation is over the real joint distributions `(Sub op).realJoint W₂` of the earlier oracle
rounds, as in `replacementBound`, which is the case where `cost` is the semi-honest advantage
against the subprotocol (`replacementBound_eq_replacementCost`). Message rounds contribute nothing.

This is original bookkeeping for stacking the hybrid argument through nested compositions with
explicit per-distinguisher reductions, not a cited statement, and it makes no efficiency claim. -/
@[expose] noncomputable def replacementCost
    (cost : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      ((s : Fin (spec₁.arity op)) → spec₁.Query op s) →
      ((((s : J) → PartyView (spec₁.Query op) (Coins₂ op) (sc₂ op) s) ×
        ((s : Fin (spec₁.arity op)) → spec₁.Answer op s)) → ProbComp Bool) → ℝ≥0∞)
    (W₁ : MultiOracleWorld spec₁) (W₂ : MultiOracleWorld spec₂)
    (Sub : (op : spec₁.Op) →
      Protocol (spec₁.arity op) spec₂ (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op))
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
    (I : Finset (Fin m)) {State Out : Fin m → Type} {sc₁ : Schedule m spec₁}
    (steps : Steps State Out sc₁) (st : (i : Fin m) → State i)
    (D : ((i : I) → Schedule.SubCoins Coins₂ sc₁ i.1 ×
      Schedule.Received (Schedule.compose sc₂ sc₁) i.1) × ((i : Fin m) → Out i) →
        ProbComp Bool) : ℝ≥0∞ :=
  match steps with
  | .done _ => 0
  | .message (sender := s₀) (receiver := r₀) send next =>
    replacementCost cost W₁ W₂ Sub S₂ I next
      (fun i => (st i, Round.deliverMessage (send (st s₀)) i))
      fun res => D (fun i : I => ((res.1 i).1,
        (Round.deliverMessage (spec := spec₂) (sender := s₀) (receiver := r₀)
          (send (st s₀)) i.1, (res.1 i).2)), res.2)
  | .oracle (op := op) (parties := parties) query next =>
    cost op (subCoalition parties I) (fun s => query s (st (parties s)))
        (roundDistinguisher W₁ S₂ I next st D) +
      ∑' r, (Sub op).realJoint W₂ (subCoalition parties I)
          (fun s => query s (st (parties s))) r *
        replacementCost cost W₁ W₂ Sub S₂ I next
          (fun i => (st i, Round.deliverOracle parties r.2 i))
          fun res => D (fun i : I =>
            ((pushTupleRestrict parties I (fun s => (r.1 s).coins) i, (res.1 i).1),
              Schedule.Received.append
                (pushScheduleReceivedRestrict parties I (sc₂ op)
                  (fun s => (r.1 s).received) i)
                (res.1 i).2),
            res.2)

/-- **The hybrid bound is the cost sum at the semi-honest advantage.** `replacementBound` is
`replacementCost` for the cost that assigns to an oracle round the semi-honest advantage of its
distinguisher against the subprotocol `Sub op` in `W₂`, for the functionality `W₁ op` with the
simulator `S₂ op`. Original bookkeeping, not a cited statement; no efficiency claim. -/
theorem replacementBound_eq_replacementCost (W₁ : MultiOracleWorld spec₁)
    (W₂ : MultiOracleWorld spec₂)
    (Sub : (op : spec₁.Op) →
      Protocol (spec₁.arity op) spec₂ (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op))
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
    (I : Finset (Fin m)) {State Out : Fin m → Type} {sc₁ : Schedule m spec₁}
    (steps : Steps State Out sc₁) (st : (i : Fin m) → State i)
    (D : ((i : I) → Schedule.SubCoins Coins₂ sc₁ i.1 ×
      Schedule.Received (Schedule.compose sc₂ sc₁) i.1) × ((i : Fin m) → Out i) →
        ProbComp Bool) :
    replacementBound W₁ W₂ Sub S₂ I steps st D =
      replacementCost
        (fun op J q D' => (semiHonestAdvantage (Sub op) W₂ (W₁ op) J (S₂ op J) q D' : ℝ≥0∞))
        W₁ W₂ Sub S₂ I steps st D := by
  induction steps with
  | done output => rw [replacementBound, replacementCost]
  | @message _ _ s₀ r₀ _ _ send next ih =>
    rw [replacementBound, replacementCost]
    exact ih _ _
  | @oracle _ _ op parties rest query next ih =>
    rw [replacementBound, replacementCost]
    simp only [ih]

/-- **The cost sum is monotone in the cost.** A pointwise bound of one per-round cost by another
bounds `replacementCost` of the first by `replacementCost` of the second, for the same worlds,
subprotocols, simulators, steps, states and test. Original bookkeeping, not a cited statement; no
efficiency claim. -/
theorem replacementCost_mono
    {cost cost' : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      ((s : Fin (spec₁.arity op)) → spec₁.Query op s) →
      ((((s : J) → PartyView (spec₁.Query op) (Coins₂ op) (sc₂ op) s) ×
        ((s : Fin (spec₁.arity op)) → spec₁.Answer op s)) → ProbComp Bool) → ℝ≥0∞}
    (h : ∀ op J q D', cost op J q D' ≤ cost' op J q D')
    (W₁ : MultiOracleWorld spec₁) (W₂ : MultiOracleWorld spec₂)
    (Sub : (op : spec₁.Op) →
      Protocol (spec₁.arity op) spec₂ (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op))
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
    (I : Finset (Fin m)) {State Out : Fin m → Type} {sc₁ : Schedule m spec₁}
    (steps : Steps State Out sc₁) (st : (i : Fin m) → State i)
    (D : ((i : I) → Schedule.SubCoins Coins₂ sc₁ i.1 ×
      Schedule.Received (Schedule.compose sc₂ sc₁) i.1) × ((i : Fin m) → Out i) →
        ProbComp Bool) :
    replacementCost cost W₁ W₂ Sub S₂ I steps st D ≤
      replacementCost cost' W₁ W₂ Sub S₂ I steps st D := by
  induction steps with
  | done output => rw [replacementCost, replacementCost]
  | @message _ _ s₀ r₀ _ _ send next ih =>
    rw [replacementCost, replacementCost]
    exact ih _ _
  | @oracle _ _ op parties rest query next ih =>
    rw [replacementCost, replacementCost]
    exact add_le_add (h _ _ _ _) (tsum_le_tsum fun r => mul_le_mul' le_rfl (ih _ _))

/-- **A pointwise bound on the advantages bounds the hybrid bound.** When the semi-honest advantage
of every distinguisher against every subprotocol `Sub op` in `W₂`, for the functionality `W₁ op`
with the simulator `S₂ op`, is at most `cost`, the hybrid bound `replacementBound` is at most
`replacementCost cost`. This is the step that stacks the hybrid argument through a nested
composition: `cost` is the bound that an inner composition theorem gives for the subprotocol.
Original bookkeeping, not a cited statement; no efficiency claim. -/
theorem replacementBound_le_replacementCost
    {cost : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      ((s : Fin (spec₁.arity op)) → spec₁.Query op s) →
      ((((s : J) → PartyView (spec₁.Query op) (Coins₂ op) (sc₂ op) s) ×
        ((s : Fin (spec₁.arity op)) → spec₁.Answer op s)) → ProbComp Bool) → ℝ≥0∞}
    {W₁ : MultiOracleWorld spec₁} {W₂ : MultiOracleWorld spec₂}
    {Sub : (op : spec₁.Op) →
      Protocol (spec₁.arity op) spec₂ (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op)}
    {S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J}
    (h : ∀ op J q D',
      (semiHonestAdvantage (Sub op) W₂ (W₁ op) J (S₂ op J) q D' : ℝ≥0∞) ≤ cost op J q D')
    (I : Finset (Fin m)) {State Out : Fin m → Type} {sc₁ : Schedule m spec₁}
    (steps : Steps State Out sc₁) (st : (i : Fin m) → State i)
    (D : ((i : I) → Schedule.SubCoins Coins₂ sc₁ i.1 ×
      Schedule.Received (Schedule.compose sc₂ sc₁) i.1) × ((i : Fin m) → Out i) →
        ProbComp Bool) :
    replacementBound W₁ W₂ Sub S₂ I steps st D ≤
      replacementCost cost W₁ W₂ Sub S₂ I steps st D := by
  rw [replacementBound_eq_replacementCost]
  exact replacementCost_mono h W₁ W₂ Sub S₂ I steps st D

end Composition

end Cslib.Crypto.Protocols.MPC
