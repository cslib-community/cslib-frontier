/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Composition.HybridGame

/-!
# The challenges that a round environment can produce

The environment `Composition.roundEnv` of a hybrid hop stops at an oracle round with a
`Composition.RoundChallenge`, whose operation, corrupted slots and query tuple are data: the slots
are `subCoalition parties I` for the parties of the challenged round and the queries are those of
the states reached. A statement about a subprotocol at a fixed coalition, such as privacy against
a corrupted receiver, applies to a challenge only once its slots are known to be that coalition.

This module gives the support statement that supplies this. `Composition.ForallChallenge I Q steps
st` says that the operation, the corrupted slots and the query tuple of every oracle round of
`steps`, from the states `st` and for all answers of the earlier rounds, satisfy `Q`; every
challenge in the support of `roundEnv`, and of `composeRoundEnv` when this holds for all sampled
outer coins, then satisfies `Q`. The kernel of the earlier rounds is arbitrary: the predicate
quantifies
over all answers, not only those in its support.

Everything here is original bookkeeping for the hybrid argument of
`CslibFrontier/Crypto/Protocols/MPC/Composition/HybridGame.lean` (#6045), not a cited statement.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.Composition.ForallChallenge`: a predicate on the operation, the
  corrupted slots and the queries of every oracle round reachable along a step sequence.

## Main results

* `Cslib.Crypto.Protocols.MPC.Composition.ForallChallenge.of_mem_support_roundEnv`,
  `Cslib.Crypto.Protocols.MPC.Composition.ForallChallenge.of_mem_support_composeRoundEnv`: the
  challenges in the support of a round environment satisfy the predicate.
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib.Probability Cslib.ProbComp
open _root_.Cslib.Crypto.Protocols.MPC.Composition

namespace Composition

variable {m : ℕ} {spec₁ spec₂ : MultiOracleSpec}
  {sc₂ : (op : spec₁.Op) → Schedule (spec₁.arity op) spec₂}
  {Coins₂ : (op : spec₁.Op) → Fin (spec₁.arity op) → Type}

/-- **A predicate on every oracle round reachable along `steps`.** From the states `st`, for the
coalition `I`: at every oracle round, the operation `op`, the corrupted slots
`subCoalition parties I` and the query tuple of the current states satisfy `Q`, and this continues
to hold after the round for every answer tuple. Message rounds are passed through. -/
@[expose] def ForallChallenge (I : Finset (Fin m))
    (Q : (op : spec₁.Op) → Finset (Fin (spec₁.arity op)) →
      ((s : Fin (spec₁.arity op)) → spec₁.Query op s) → Prop)
    {State Out : Fin m → Type} {sc₁ : Schedule m spec₁}
    (steps : Steps State Out sc₁) (st : (i : Fin m) → State i) : Prop :=
  match steps with
  | .done _ => True
  | .message (sender := s₀) send next =>
    ForallChallenge I Q next (fun i => (st i, Round.deliverMessage (send (st s₀)) i))
  | .oracle (op := op) (parties := parties) query next =>
    Q op (subCoalition parties I) (fun s => query s (st (parties s))) ∧
      ∀ ans, ForallChallenge I Q next (fun i => (st i, Round.deliverOracle parties ans i))

/-- **The challenges of a round environment satisfy a predicate that holds along the steps.** If
`Q` holds for every oracle round reachable along `steps` from `st` (`ForallChallenge`), then every
challenge `c` in the support of the environment `roundEnv … I steps j st D` of any hop `j`, on any
kernel `ν` and for any test `D`, satisfies `Q c.op c.coalition c.query`. -/
theorem ForallChallenge.of_mem_support_roundEnv (W₁ : MultiOracleWorld spec₁)
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
    (ν : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      ((s : Fin (spec₁.arity op)) → spec₁.Query op s) →
      PMF (((s : J) → PartyView (spec₁.Query op) (Coins₂ op) (sc₂ op) s) ×
        ((s : Fin (spec₁.arity op)) → spec₁.Answer op s)))
    (I : Finset (Fin m))
    {Q : (op : spec₁.Op) → Finset (Fin (spec₁.arity op)) →
      ((s : Fin (spec₁.arity op)) → spec₁.Query op s) → Prop}
    {State Out : Fin m → Type} {sc₁ : Schedule m spec₁} (steps : Steps State Out sc₁) (j : ℕ)
    (st : (i : Fin m) → State i)
    (D : ((i : I) → Schedule.SubCoins Coins₂ sc₁ i.val ×
      Schedule.Received (Schedule.compose sc₂ sc₁) i.val) × ((i : Fin m) → Out i) →
        ProbComp Bool)
    (h : ForallChallenge I Q steps st) {c : RoundChallenge sc₂ Coins₂}
    (hc : Sum.inr c ∈ (roundEnv W₁ S₂ ν I steps j st D).support) :
    Q c.op c.coalition c.query := by
  induction steps generalizing j with
  | done output =>
    rw [roundEnv, PMF.support_map] at hc
    obtain ⟨b, -, hb⟩ := hc
    cases hb
  | @message _ _ s₀ r₀ _ _ send next ih =>
    rw [roundEnv] at hc
    rw [ForallChallenge] at h
    exact ih _ _ _ h hc
  | @oracle _ _ op parties rest query next ih =>
    rw [ForallChallenge] at h
    cases j with
    | zero =>
      rw [roundEnv, PMF.support_pure, Set.mem_singleton_iff] at hc
      obtain rfl := Sum.inr.inj hc
      exact h.1
    | succ j =>
      rw [roundEnv, PMF.mem_support_bind_iff] at hc
      obtain ⟨r, -, hr⟩ := hc
      exact ih _ _ _ (h.2 r.2) hr

end Composition

variable {m : ℕ} {spec₁ spec₂ : MultiOracleSpec} {sc₁ : Schedule m spec₁}
  {sc₂ : (op : spec₁.Op) → Schedule (spec₁.arity op) spec₂} {In Coins₁ Out : Fin m → Type}
  {Coins₂ : (op : spec₁.Op) → Fin (spec₁.arity op) → Type}

/-- **The challenges of the environment of a composed protocol.** If `Q` holds for every oracle
round reachable along the steps of the outer protocol `P` on the inputs `x`, for all outer coins
in the support of the coin sampler of `P`, then every challenge `c` in the support of
`composeRoundEnv P … I x D j` satisfies
`Q c.op c.coalition c.query`. -/
theorem Composition.ForallChallenge.of_mem_support_composeRoundEnv
    (P : Protocol m spec₁ sc₁ In Coins₁ Out)
    (W₁ : MultiOracleWorld spec₁) (W₂ : MultiOracleWorld spec₂)
    (Sub : (op : spec₁.Op) →
      Protocol (spec₁.arity op) spec₂ (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op))
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
    (I : Finset (Fin m)) (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In (Schedule.ComposedCoins Coins₂ Coins₁ sc₁)
      (Schedule.compose sc₂ sc₁) i) × ((i : Fin m) → Out i) → ProbComp Bool) (j : ℕ)
    {Q : (op : spec₁.Op) → Finset (Fin (spec₁.arity op)) →
      ((s : Fin (spec₁.arity op)) → spec₁.Query op s) → Prop}
    (h : ∀ c₁ ∈ (ProbComp.eval (OracleComp.pi P.sampleCoins)).support,
      ForallChallenge I Q P.steps (fun i => (x i, c₁ i)))
    {c : RoundChallenge sc₂ Coins₂}
    (hc : Sum.inr c ∈ (composeRoundEnv P W₁ W₂ Sub S₂ I x D j).support) :
    Q c.op c.coalition c.query := by
  rw [composeRoundEnv, PMF.mem_support_bind_iff] at hc
  obtain ⟨c₁, hc₁, hc⟩ := hc
  exact (h c₁ hc₁).of_mem_support_roundEnv W₁ S₂ _ I P.steps j _ _ hc

end Cslib.Crypto.Protocols.MPC
