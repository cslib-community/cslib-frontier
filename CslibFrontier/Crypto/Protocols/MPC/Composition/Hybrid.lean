/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.Mixture
public import CslibFrontier.Crypto.Protocols.MPC.Composition.Advantage

/-!
# Hybrid argument over the oracle rounds of a composed protocol

`semiHonestAdvantage_compose_le` bounds the semi-honest advantage against a composed protocol
`P.compose Sub` by the advantage of a reduction against the outer protocol `P` plus the
subprotocol-replacement gap, and `advantage_replacement_eq_kernelRun` expresses that gap through
two runs of one kernel program, `Composition.kernelRun`, on the ideal and on the real joint
distributions of the subprotocols. This module bounds the gap by the semi-honest advantages of
explicit distinguishers against the subprotocols, by the hybrid argument that replaces the
subprotocol calls one at a time.

At an oracle round `op` of the outer protocol with query tuple `q`, the two runs differ in the
kernel that the round draws from and in the kernel of the later rounds. Changing the kernel of this
round, in front of the later rounds run on the ideal joint distributions, is a semi-honest
distinguishing game against the subprotocol `Sub op` on the input tuple `q`: its distinguisher
`Composition.roundDistinguisher` receives the views of the corrupted slots and the answers, runs
the remaining rounds with the ideal functionalities `W₁` and the subprotocol simulators `S₂`
(`Composition.kernelProg`) and applies the given test. Changing the kernel of the later rounds,
after this round has drawn from the real joint distribution, is the same question for the tail,
averaged over the real execution of this round.

Because the query tuple of a round depends on the outcome of the earlier rounds, the bound is not a
sum of advantages at fixed inputs. `Composition.replacementBound` is the sum over the oracle rounds
of the expectation, over the real executions of the earlier subprotocol calls, of the semi-honest
advantage of that round's distinguisher against its subprotocol on the round's query tuple. It is
an extended non-negative real defined by recursion on the outer steps.

Everything here is original bookkeeping for the hybrid argument in the proof of Goldreich's
composition theorem (Section 7.5.2.1, Theorem 7.5.7), not a cited statement. The bounds are
concrete: a fixed input tuple and distinguisher, no security parameter, and no efficiency claim
about `Composition.roundDistinguisher`. The asymptotic composition theorem, which needs
polynomial-time certificates for these distinguishers and a choice of the earlier rounds' outcome
as non-uniform advice, is not proved here (#6045).

## Main definitions

* `Cslib.Crypto.Protocols.MPC.Composition.kernelProg`: the kernel program as a `ProbComp`, for
  kernels that are themselves programs.
* `Cslib.Crypto.Protocols.MPC.Composition.roundDistinguisher`: the distinguisher against the
  subprotocol of an oracle round.
* `Cslib.Crypto.Protocols.MPC.Composition.replacementBound`: the sum over the oracle rounds of the
  expected advantages of the round distinguishers.

## Main results

* `Cslib.Crypto.Protocols.MPC.Composition.advantage_kernelRun_le_replacementBound`: the hybrid
  argument for the kernel program.
* `Cslib.Crypto.Protocols.MPC.Composition.replacementBound_eq_zero`: the bound vanishes for
  perfectly private subprotocols.
* `Cslib.Crypto.Protocols.MPC.advantage_replacement_le_replacementBound`: the bound on the
  subprotocol-replacement gap.
* `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_compose_le_replacementBound`: the concrete
  composition theorem, bounding the advantage against `P.compose Sub` by the advantage of
  `composeDistinguisher` against `P` plus the expected advantages of the round distinguishers
  against the subprotocols.

## References

* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004],
  Section 7.5.2.1 (Theorem 7.5.7).
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

/-- The kernel program at an oracle round, with the drawn views and answers as one pair `r`: the
round draws `r` from the kernel on the round's query tuple, the answers `r.2` are delivered, and
the corrupted slots' subprotocol coins and transcripts in `r.1` are put in front of the result of
the remaining rounds. -/
theorem kernelRun_oracle
    (μ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      ((s : Fin (spec₁.arity op)) → spec₁.Query op s) →
      PMF (((s : J) → PartyView (spec₁.Query op) (Coins₂ op) (sc₂ op) s) ×
        ((s : Fin (spec₁.arity op)) → spec₁.Answer op s)))
    (I : Finset (Fin m)) {State Out : Fin m → Type} {op : spec₁.Op}
    {parties : Fin (spec₁.arity op) ↪ Fin m} {sc₁ : Schedule m spec₁}
    (query : (s : Fin (spec₁.arity op)) → State (parties s) → spec₁.Query op s)
    (next : Steps (fun i => State i × (Round.oracle op parties).Received i) Out sc₁)
    (st : (i : Fin m) → State i) :
    kernelRun μ I (.oracle query next) st =
      (μ op (subCoalition parties I) fun s => query s (st (parties s))).bind fun r =>
        (kernelRun μ I next (fun i => (st i, Round.deliverOracle parties r.2 i))).map fun res =>
          (fun i : I =>
            ((pushTupleRestrict parties I (fun s => (r.1 s).coins) i, (res.1 i).1),
              Schedule.Received.append
                (pushScheduleReceivedRestrict parties I (sc₂ op)
                  (fun s => (r.1 s).received) i)
                (res.1 i).2),
            res.2) :=
  rfl

/-- The kernel program of `kernelRun` as a `ProbComp`, for kernels `κ` that are programs: every
oracle round `op` with query tuple `q` draws the views of the corrupted slots
`J = subCoalition parties I` and all the answers from `κ op J q`. Its distribution is `kernelRun`
on the distributions of `κ` (`eval_kernelProg`). -/
@[expose] noncomputable def kernelProg
    (κ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      ((s : Fin (spec₁.arity op)) → spec₁.Query op s) →
      ProbComp (((s : J) → PartyView (spec₁.Query op) (Coins₂ op) (sc₂ op) s) ×
        ((s : Fin (spec₁.arity op)) → spec₁.Answer op s)))
    (I : Finset (Fin m)) {State Out : Fin m → Type} {sc₁ : Schedule m spec₁}
    (steps : Steps State Out sc₁) (st : (i : Fin m) → State i) :
    ProbComp (((i : I) → Schedule.SubCoins Coins₂ sc₁ i.1 ×
      Schedule.Received (Schedule.compose sc₂ sc₁) i.1) × ((i : Fin m) → Out i)) :=
  match steps with
  | .done output => pure (fun _ => ((), ()), fun i => output i (st i))
  | .message (sender := s₀) (receiver := r₀) send next => do
    let res ← kernelProg κ I next (fun i => (st i, Round.deliverMessage (send (st s₀)) i))
    return (fun i : I => ((res.1 i).1,
      (Round.deliverMessage (spec := spec₂) (sender := s₀) (receiver := r₀)
        (send (st s₀)) i.1, (res.1 i).2)), res.2)
  | .oracle (op := op) (parties := parties) query next => do
    let r ← κ op (subCoalition parties I) fun s => query s (st (parties s))
    let res ← kernelProg κ I next (fun i => (st i, Round.deliverOracle parties r.2 i))
    return (fun i : I =>
      ((pushTupleRestrict parties I (fun s => (r.1 s).coins) i, (res.1 i).1),
        Schedule.Received.append
          (pushScheduleReceivedRestrict parties I (sc₂ op)
            (fun s => (r.1 s).received) i)
          (res.1 i).2),
      res.2)

/-- The kernel program `kernelProg κ` has the distribution of `kernelRun` on the distributions of
the kernels `κ`. -/
theorem eval_kernelProg
    (κ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      ((s : Fin (spec₁.arity op)) → spec₁.Query op s) →
      ProbComp (((s : J) → PartyView (spec₁.Query op) (Coins₂ op) (sc₂ op) s) ×
        ((s : Fin (spec₁.arity op)) → spec₁.Answer op s)))
    (I : Finset (Fin m)) {State Out : Fin m → Type} {sc₁ : Schedule m spec₁}
    (steps : Steps State Out sc₁) (st : (i : Fin m) → State i) :
    ProbComp.eval (kernelProg κ I steps st) =
      kernelRun (fun op J q => ProbComp.eval (κ op J q)) I steps st := by
  induction steps with
  | done output =>
    simp only [kernelProg, kernelRun, ProbComp.eval_pure]
  | @message _ _ s₀ r₀ _ _ send next ih =>
    simp only [kernelProg, kernelRun, bind_pure_comp, ProbComp.eval_map, ih]
  | @oracle _ _ op parties rest query next ih =>
    simp only [kernelProg, kernelRun_oracle, bind_pure_comp, ProbComp.eval_bind,
      ProbComp.eval_map, ih]

/-- **The distinguisher against the subprotocol of an oracle round.** At an oracle round
`.oracle query next` of the outer steps, reached in the states `st`, a test `D` of the kernel
program's result becomes this distinguisher of the views of the corrupted slots
`subCoalition parties I` and the answers of the subprotocol `Sub op`: it delivers the answers,
runs the remaining rounds `next` on the ideal joint distributions of the subprotocols, sampled with
the ideal functionalities `W₁` and the simulators `S₂` (`kernelProg`), puts the given views in
front of the result and runs `D`. -/
@[expose] noncomputable def roundDistinguisher (W₁ : MultiOracleWorld spec₁)
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
    (I : Finset (Fin m)) {State Out : Fin m → Type} {op : spec₁.Op}
    {parties : Fin (spec₁.arity op) ↪ Fin m} {sc₁ : Schedule m spec₁}
    (next : Steps (fun i => State i × (Round.oracle op parties).Received i) Out sc₁)
    (st : (i : Fin m) → State i)
    (D : ((i : I) → Schedule.SubCoins Coins₂ (.oracle op parties :: sc₁) i.1 ×
      Schedule.Received (Schedule.compose sc₂ (.oracle op parties :: sc₁)) i.1) ×
        ((i : Fin m) → Out i) → ProbComp Bool)
    (r : ((s : subCoalition parties I) → PartyView (spec₁.Query op) (Coins₂ op) (sc₂ op) s) ×
      ((s : Fin (spec₁.arity op)) → spec₁.Answer op s)) : ProbComp Bool := do
  let res ← kernelProg (fun op J q => idealJoint (W₁ op) J (S₂ op J) q) I next
    (fun i => (st i, Round.deliverOracle parties r.2 i))
  D (fun i : I =>
      ((pushTupleRestrict parties I (fun s => (r.1 s).coins) i, (res.1 i).1),
        Schedule.Received.append
          (pushScheduleReceivedRestrict parties I (sc₂ op)
            (fun s => (r.1 s).received) i)
          (res.1 i).2),
    res.2)

/-- **The hybrid bound on the replacement gap of a kernel program.** For the outer steps `steps`
from the states `st` and a test `D` of the kernel program's result, the sum over the oracle rounds
of `steps` of the expected semi-honest advantage of that round's distinguisher
(`roundDistinguisher`) against the round's subprotocol `Sub op` in `W₂`, for the functionality
`W₁ op` with the simulator `S₂ op`, on the round's query tuple. The expectation is over the real
joint distributions `(Sub op).realJoint W₂` of the earlier oracle rounds, which determine the query
tuple and the states of the round. Message rounds contribute nothing. -/
@[expose] noncomputable def replacementBound (W₁ : MultiOracleWorld spec₁)
    (W₂ : MultiOracleWorld spec₂)
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
    replacementBound W₁ W₂ Sub S₂ I next
      (fun i => (st i, Round.deliverMessage (send (st s₀)) i))
      fun res => D (fun i : I => ((res.1 i).1,
        (Round.deliverMessage (spec := spec₂) (sender := s₀) (receiver := r₀)
          (send (st s₀)) i.1, (res.1 i).2)), res.2)
  | .oracle (op := op) (parties := parties) query next =>
    (semiHonestAdvantage (Sub op) W₂ (W₁ op) (subCoalition parties I)
        (S₂ op (subCoalition parties I)) (fun s => query s (st (parties s)))
        (roundDistinguisher W₁ S₂ I next st D) : ℝ≥0∞) +
      ∑' r, (Sub op).realJoint W₂ (subCoalition parties I)
          (fun s => query s (st (parties s))) r *
        replacementBound W₁ W₂ Sub S₂ I next
          (fun i => (st i, Round.deliverOracle parties r.2 i))
          fun res => D (fun i : I =>
            ((pushTupleRestrict parties I (fun s => (r.1 s).coins) i, (res.1 i).1),
              Schedule.Received.append
                (pushScheduleReceivedRestrict parties I (sc₂ op)
                  (fun s => (r.1 s).received) i)
                (res.1 i).2),
            res.2)

/-- **Hybrid argument over the oracle rounds.** The advantage of a test `D` between the kernel
program of `steps` on the ideal joint distributions `idealJoint (W₁ op) J (S₂ op J) q` of the
subprotocols and on their real joint distributions `(Sub op).realJoint W₂ J q` is at most
`replacementBound`: the sum over the oracle rounds of the expected semi-honest advantage of the
round's distinguisher against the round's subprotocol. Nothing is assumed about the subprotocols,
the simulators or `D`. -/
theorem advantage_kernelRun_le_replacementBound (W₁ : MultiOracleWorld spec₁)
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
    (Game.advantage
        ((kernelRun (fun op J q => ProbComp.eval (idealJoint (W₁ op) J (S₂ op J) q)) I steps
          st).bind fun res => ProbComp.eval (D res))
        ((kernelRun (fun op J q => (Sub op).realJoint W₂ J q) I steps st).bind fun res =>
          ProbComp.eval (D res)) : ℝ≥0∞) ≤
      replacementBound W₁ W₂ Sub S₂ I steps st D := by
  induction steps with
  | done output =>
    simp only [kernelRun, Game.advantage_self, ENNReal.coe_zero, zero_le]
  | @message _ _ s₀ r₀ _ _ send next ih =>
    simp only [kernelRun, replacementBound, PMF.bind_map, Function.comp_def]
    exact ih _ _
  | @oracle _ _ op parties rest query next ih =>
    rw [kernelRun_oracle, kernelRun_oracle, replacementBound]
    simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
    refine (Game.coe_advantage_bind_bind_le _ _ _ _).trans
      (add_le_add (le_of_eq ?_) (tsum_le_tsum fun r => mul_le_mul' le_rfl (ih _ _)))
    simp only [semiHonestAdvantage, roundDistinguisher, ProbComp.eval_bind, eval_kernelProg]

/-- **The hybrid bound vanishes for perfectly private subprotocols.** When every subprotocol
`Sub op` is perfectly private in `W₂` for the functionality `W₁ op` with the simulators `S₂ op`,
every round distinguisher has advantage zero, so `replacementBound` is zero. -/
theorem replacementBound_eq_zero {W₁ : MultiOracleWorld spec₁} {W₂ : MultiOracleWorld spec₂}
    {Sub : (op : spec₁.Op) →
      Protocol (spec₁.arity op) spec₂ (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op)}
    {S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J}
    (hSub : ∀ op, PerfectSemiHonestPrivate (Sub op) W₂ (W₁ op) (S₂ op))
    (I : Finset (Fin m)) {State Out : Fin m → Type} {sc₁ : Schedule m spec₁}
    (steps : Steps State Out sc₁) (st : (i : Fin m) → State i)
    (D : ((i : I) → Schedule.SubCoins Coins₂ sc₁ i.1 ×
      Schedule.Received (Schedule.compose sc₂ sc₁) i.1) × ((i : Fin m) → Out i) →
        ProbComp Bool) :
    replacementBound W₁ W₂ Sub S₂ I steps st D = 0 := by
  induction steps with
  | done output => rw [replacementBound]
  | @message _ _ s₀ r₀ _ _ send next ih =>
    rw [replacementBound]
    exact ih _ _
  | @oracle _ _ op parties rest query next ih =>
    rw [replacementBound, (hSub op).semiHonestAdvantage_eq_zero]
    simp only [ih, mul_zero, tsum_zero, ENNReal.coe_zero, add_zero]

end Composition

variable {m : ℕ} {spec₁ spec₂ : MultiOracleSpec} {sc₁ : Schedule m spec₁}
  {sc₂ : (op : spec₁.Op) → Schedule (spec₁.arity op) spec₂} {In Coins₁ Out : Fin m → Type}
  {Coins₂ : (op : spec₁.Op) → Fin (spec₁.arity op) → Type}

/-- **The subprotocol-replacement gap is at most the hybrid bound.** The replacement gap of
`semiHonestAdvantage_compose_le` is at most the expectation, over the outer coins `c₁`, of
`Composition.replacementBound` for `P.steps` from the inputs `x` and coins `c₁`: the sum over the
oracle rounds of `P` of the expected semi-honest advantage of the round's distinguisher
(`Composition.roundDistinguisher`) against the round's subprotocol on the round's query tuple.
Nothing is assumed about `P`, `Sub`, the simulators or `D`. -/
theorem advantage_replacement_le_replacementBound (P : Protocol m spec₁ sc₁ In Coins₁ Out)
    (W₁ : MultiOracleWorld spec₁) (W₂ : MultiOracleWorld spec₂)
    (Sub : (op : spec₁.Op) →
      Protocol (spec₁.arity op) spec₂ (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op))
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
    (I : Finset (Fin m)) (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In (Schedule.ComposedCoins Coins₂ Coins₁ sc₁)
      (Schedule.compose sc₂ sc₁) i) × ((i : Fin m) → Out i) → ProbComp Bool) :
    (Game.advantage
        ((P.realJoint W₁ I x).bind fun r =>
          ProbComp.eval (composeDistinguisher P S₂ I x D r))
        (((P.compose Sub).realJoint W₂ I x).bind fun r => ProbComp.eval (D r)) : ℝ≥0∞) ≤
      ∑' c₁, ProbComp.eval (OracleComp.pi P.sampleCoins) c₁ *
        replacementBound W₁ W₂ Sub S₂ I P.steps (fun i => (x i, c₁ i))
          (fun res => D (fun i : I => ⟨x i.1, (c₁ i.1, (res.1 i).1), (res.1 i).2⟩, res.2)) := by
  rw [advantage_replacement_eq_kernelRun]
  exact (Game.coe_advantage_bind_le_tsum _ _ _).trans (tsum_le_tsum fun c₁ =>
    mul_le_mul' le_rfl (advantage_kernelRun_le_replacementBound W₁ W₂ Sub S₂ I P.steps _ _))

/-- **Concrete composition theorem.** For every outer protocol `P` in the oracle world `W₁`, outer
simulator `S₁` for coalition `I`, subprotocols `Sub` in `W₂` and subprotocol simulators `S₂`, the
semi-honest advantage of `D` against `P.compose Sub` with `composeSim P S₁ S₂` is at most the
advantage of the reduction `composeDistinguisher P S₂ I x D` against `P` with `S₁`, plus the
expectation over the outer coins of `Composition.replacementBound`: the sum over the oracle rounds
of `P` of the expected semi-honest advantage of the round's distinguisher
`Composition.roundDistinguisher` against the round's subprotocol `Sub op`, for the functionality
`W₁ op` with the simulator `S₂ op`, on the round's query tuple.

This is the concrete, per-instance form of the hybrid argument for Goldreich's Theorem 7.5.7, not
the cited theorem: nothing is assumed about `P`, `Sub` or the simulators, and no efficiency of the
distinguishers is claimed. -/
theorem semiHonestAdvantage_compose_le_replacementBound (P : Protocol m spec₁ sc₁ In Coins₁ Out)
    (W₁ : MultiOracleWorld spec₁) (W₂ : MultiOracleWorld spec₂) (f : Functionality m In Out)
    (I : Finset (Fin m)) (S₁ : CoalitionSimulator sc₁ In Coins₁ Out I)
    (Sub : (op : spec₁.Op) →
      Protocol (spec₁.arity op) spec₂ (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op))
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
    (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In (Schedule.ComposedCoins Coins₂ Coins₁ sc₁)
      (Schedule.compose sc₂ sc₁) i) × ((i : Fin m) → Out i) → ProbComp Bool) :
    (semiHonestAdvantage (P.compose Sub) W₂ f I (composeSim P S₁ S₂) x D : ℝ≥0∞) ≤
      semiHonestAdvantage P W₁ f I S₁ x (composeDistinguisher P S₂ I x D) +
        ∑' c₁, ProbComp.eval (OracleComp.pi P.sampleCoins) c₁ *
          replacementBound W₁ W₂ Sub S₂ I P.steps (fun i => (x i, c₁ i))
            (fun res => D (fun i : I => ⟨x i.1, (c₁ i.1, (res.1 i).1), (res.1 i).2⟩, res.2)) := by
  refine (ENNReal.coe_le_coe.mpr
    (semiHonestAdvantage_compose_le P W₁ W₂ f I S₁ Sub S₂ x D)).trans ?_
  rw [ENNReal.coe_add]
  exact add_le_add le_rfl (advantage_replacement_le_replacementBound P W₁ W₂ Sub S₂ I x D)

end Cslib.Crypto.Protocols.MPC
