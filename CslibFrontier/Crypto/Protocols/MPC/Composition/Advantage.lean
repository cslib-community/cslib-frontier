/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Advantage
public import CslibFrontier.Crypto.Protocols.MPC.Composition

/-!
# Concrete semi-honest advantage of a composed protocol

`PerfectSemiHonestPrivate.compose` composes a perfectly private outer protocol with perfectly
private subprotocols. This module gives the concrete, per-instance form of the composition argument
for an outer protocol that is only computationally private: it bounds
`semiHonestAdvantage (P.compose Sub)` for a coalition `I` with the composed simulator
`composeSim P S₁ S₂` through the hybrid execution that runs the outer protocol `P` in its ideal
oracle world `W₁` and expands the coalition's views with the subprotocol simulators `S₂`.

* **Ideal to hybrid** (`eval_idealJoint_composeSim_bind`). A distinguisher `D` of the composed
  protocol's views becomes the explicit distinguisher `composeDistinguisher P S₂ I x D` of the outer
  protocol's views, which expands the views with `S₂` and runs `D`. The ideal game of the composed
  protocol against `D` is the ideal game of the outer protocol against this reduction, for every
  single-coalition outer simulator `S₁` and with no assumption on the subprotocols.
* **Hybrid to real.** The remaining distance, between the outer protocol's real execution in `W₁`
  against the reduction and the composed protocol's real execution in `W₂` against `D`, is the
  subprotocol-replacement gap. `semiHonestAdvantage_compose_le` keeps it as an explicit term. It
  vanishes when the subprotocols are perfectly private (`Protocol.bind_realJoint_compose`), which
  gives the equality `semiHonestAdvantage_compose`.
* **The gap as a kernel gap.** With no assumption on the subprotocols, the two executions of the
  replacement gap are one kernel program, `Composition.kernelRun` of the outer steps after sampling
  the outer coins, run on the ideal and on the real joint distributions of the subprotocols
  (`advantage_replacement_eq_kernelRun`). The two runs differ only in the kernel that each oracle
  round draws from, which is what a hybrid argument over the oracle rounds has to bound.

Everything here is original bookkeeping around Goldreich's composition theorem (Section 7.5.2.1,
Theorem 7.5.7) rather than a cited statement: the quantities are concrete, for a fixed input tuple
and distinguisher, with no security parameter and no efficiency claim about `composeDistinguisher`.
The bound of the subprotocol-replacement gap by the semi-honest advantages against computationally
private subprotocols (the hybrid argument over the oracle rounds of the kernel program, with an
explicit distinguisher for each round) is in
`CslibFrontier/Crypto/Protocols/MPC/Composition/Hybrid.lean`. The asymptotic statement with
certified reductions is not proved (#6045).

## Main definitions

* `Cslib.Crypto.Protocols.MPC.composeDistinguisher`: the reduction from a distinguisher of the
  composed protocol to a distinguisher of the outer protocol.

## Main results

* `Cslib.Crypto.Protocols.MPC.eval_idealJoint_composeSim_bind`: the ideal games agree.
* `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_compose_le`: the advantage against the composed
  protocol is at most the advantage of the reduction against the outer protocol plus the
  subprotocol-replacement gap.
* `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_compose`: with perfectly private subprotocols the
  two advantages are equal.
* `Cslib.Crypto.Protocols.MPC.Protocol.bind_realJoint_composeDistinguisher_eq_kernelRun`,
  `Cslib.Crypto.Protocols.MPC.advantage_replacement_eq_kernelRun`: the hybrid game and the
  subprotocol-replacement gap in terms of the kernel program, with no assumption on the
  subprotocols.

## References

* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004],
  Section 7.5.2.1 (Theorem 7.5.7).
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib.Probability Cslib.ProbComp
open _root_.Cslib.Crypto.Protocols.MPC.Composition

variable {m : ℕ} {spec₁ spec₂ : MultiOracleSpec} {sc₁ : Schedule m spec₁}
  {sc₂ : (op : spec₁.Op) → Schedule (spec₁.arity op) spec₂} {In Coins₁ Out : Fin m → Type}
  {Coins₂ : (op : spec₁.Op) → Fin (spec₁.arity op) → Type}

/-- The reduction of the composition argument: from a distinguisher `D` of the coalition `I`'s views
of a composed protocol `P.compose Sub`, the distinguisher of `I`'s views of the outer protocol `P`
on the input tuple `x` that expands these views at every oracle round with the subprotocol
simulators `S₂` (`expandSimSteps`) and runs `D` on the result. -/
@[expose] noncomputable def composeDistinguisher (P : Protocol m spec₁ sc₁ In Coins₁ Out)
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
    (I : Finset (Fin m)) (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In (Schedule.ComposedCoins Coins₂ Coins₁ sc₁)
      (Schedule.compose sc₂ sc₁) i) × ((i : Fin m) → Out i) → ProbComp Bool)
    (r : ((i : I) → PartyView In Coins₁ sc₁ i) × ((i : Fin m) → Out i)) : ProbComp Bool := do
  let sub ← expandSimSteps S₂ I P.steps
    (fun i => (x i.1, (r.1 i).coins)) (fun i => (r.1 i).received)
  D (fun i => ⟨x i.1, ((r.1 i).coins, (sub i).1), (sub i).2⟩, r.2)

/-- **Ideal to hybrid.** The ideal game of a composed protocol with the composed simulator
`composeSim P S₁ S₂` against `D` is the ideal game of the outer protocol with `S₁` against the
reduction `composeDistinguisher P S₂ I x D`. No property of the simulators is used. -/
theorem eval_idealJoint_composeSim_bind (P : Protocol m spec₁ sc₁ In Coins₁ Out)
    (f : Functionality m In Out) (I : Finset (Fin m))
    (S₁ : CoalitionSimulator sc₁ In Coins₁ Out I)
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
    (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In (Schedule.ComposedCoins Coins₂ Coins₁ sc₁)
      (Schedule.compose sc₂ sc₁) i) × ((i : Fin m) → Out i) → ProbComp Bool) :
    ProbComp.eval (idealJoint f I (composeSim P S₁ S₂) x >>= D) =
      ProbComp.eval (idealJoint f I S₁ x >>= composeDistinguisher P S₂ I x D) := by
  simp only [idealJoint, composeSim, composeDistinguisher, bind_assoc, pure_bind,
    Finset.restrict_def]

/-- **Hybrid to real, for perfectly private subprotocols.** When every subprotocol `Sub op` is
perfectly private in `W₂` for the functionality `W₁ op` with simulators `S₂ op`, the real execution
of `P.compose Sub` in `W₂` against `D` is the real execution of `P` in `W₁` against the reduction
`composeDistinguisher P S₂ I x D`. -/
theorem Protocol.bind_realJoint_compose {P : Protocol m spec₁ sc₁ In Coins₁ Out}
    {W₁ : MultiOracleWorld spec₁} {W₂ : MultiOracleWorld spec₂}
    {Sub : (op : spec₁.Op) →
      Protocol (spec₁.arity op) spec₂ (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op)}
    {S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J}
    (hSub : ∀ op, PerfectSemiHonestPrivate (Sub op) W₂ (W₁ op) (S₂ op))
    (I : Finset (Fin m)) (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In (Schedule.ComposedCoins Coins₂ Coins₁ sc₁)
      (Schedule.compose sc₂ sc₁) i) × ((i : Fin m) → Out i) → ProbComp Bool) :
    (((P.compose Sub).realJoint W₂ I x).bind fun r => ProbComp.eval (D r)) =
      (P.realJoint W₁ I x).bind fun r => ProbComp.eval (composeDistinguisher P S₂ I x D r) := by
  rw [Protocol.realJoint_compose hSub I x, PMF.bind_bind]
  refine congrArg (P.realJoint W₁ I x).bind (funext fun r => ?_)
  obtain ⟨v₁, y⟩ := r
  simp only [composeDistinguisher, ProbComp.eval_bind, PMF.bind_map, Function.comp_def]

/-- **Concrete composition bound.** For every outer protocol `P` in the oracle world `W₁`, outer
simulator `S₁` for coalition `I`, subprotocols `Sub` in `W₂` and subprotocol simulators `S₂`, the
semi-honest advantage of `D` against `P.compose Sub` with `composeSim P S₁ S₂` is at most the
advantage of the reduction `composeDistinguisher P S₂ I x D` against `P` with `S₁`, plus the
subprotocol-replacement gap: the distance between the real execution of `P` in `W₁` against the
reduction and the real execution of `P.compose Sub` in `W₂` against `D`. Nothing is assumed about
`P`, `Sub` or the simulators; the gap is the term that the privacy of the subprotocols bounds. -/
theorem semiHonestAdvantage_compose_le (P : Protocol m spec₁ sc₁ In Coins₁ Out)
    (W₁ : MultiOracleWorld spec₁) (W₂ : MultiOracleWorld spec₂) (f : Functionality m In Out)
    (I : Finset (Fin m)) (S₁ : CoalitionSimulator sc₁ In Coins₁ Out I)
    (Sub : (op : spec₁.Op) →
      Protocol (spec₁.arity op) spec₂ (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op))
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
    (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In (Schedule.ComposedCoins Coins₂ Coins₁ sc₁)
      (Schedule.compose sc₂ sc₁) i) × ((i : Fin m) → Out i) → ProbComp Bool) :
    semiHonestAdvantage (P.compose Sub) W₂ f I (composeSim P S₁ S₂) x D ≤
      semiHonestAdvantage P W₁ f I S₁ x (composeDistinguisher P S₂ I x D) +
        Game.advantage
          ((P.realJoint W₁ I x).bind fun r =>
            ProbComp.eval (composeDistinguisher P S₂ I x D r))
          (((P.compose Sub).realJoint W₂ I x).bind fun r => ProbComp.eval (D r)) := by
  unfold semiHonestAdvantage
  rw [eval_idealJoint_composeSim_bind]
  exact Game.advantage_triangle _ _ _

/-- **Composition with perfectly private subprotocols preserves the advantage.** When every
subprotocol `Sub op` is perfectly private in `W₂` for the functionality `W₁ op` with simulators
`S₂ op`, the semi-honest advantage of `D` against `P.compose Sub` with `composeSim P S₁ S₂` equals
the advantage of the reduction `composeDistinguisher P S₂ I x D` against `P` with `S₁`. The outer
protocol may be only computationally private; `PerfectSemiHonestPrivate.compose` is the case where
the right-hand side vanishes for every distinguisher. -/
theorem semiHonestAdvantage_compose {P : Protocol m spec₁ sc₁ In Coins₁ Out}
    {W₁ : MultiOracleWorld spec₁} {W₂ : MultiOracleWorld spec₂}
    {Sub : (op : spec₁.Op) →
      Protocol (spec₁.arity op) spec₂ (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op)}
    {S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J}
    (hSub : ∀ op, PerfectSemiHonestPrivate (Sub op) W₂ (W₁ op) (S₂ op))
    (f : Functionality m In Out) (I : Finset (Fin m))
    (S₁ : CoalitionSimulator sc₁ In Coins₁ Out I) (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In (Schedule.ComposedCoins Coins₂ Coins₁ sc₁)
      (Schedule.compose sc₂ sc₁) i) × ((i : Fin m) → Out i) → ProbComp Bool) :
    semiHonestAdvantage (P.compose Sub) W₂ f I (composeSim P S₁ S₂) x D =
      semiHonestAdvantage P W₁ f I S₁ x (composeDistinguisher P S₂ I x D) := by
  unfold semiHonestAdvantage
  rw [eval_idealJoint_composeSim_bind, Protocol.bind_realJoint_compose hSub]

/-- **The hybrid game as a kernel game.** The real execution of the outer protocol `P` in `W₁`
against the reduction `composeDistinguisher P S₂ I x D` samples the outer coins, runs the kernel
program of `P.steps` on the ideal joint distributions of the subprotocols and runs `D` on the
resulting views and outputs. -/
theorem Protocol.bind_realJoint_composeDistinguisher_eq_kernelRun
    (P : Protocol m spec₁ sc₁ In Coins₁ Out) (W₁ : MultiOracleWorld spec₁)
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
    (I : Finset (Fin m)) (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In (Schedule.ComposedCoins Coins₂ Coins₁ sc₁)
      (Schedule.compose sc₂ sc₁) i) × ((i : Fin m) → Out i) → ProbComp Bool) :
    ((P.realJoint W₁ I x).bind fun r => ProbComp.eval (composeDistinguisher P S₂ I x D r)) =
      (ProbComp.eval (OracleComp.pi P.sampleCoins)).bind fun c₁ =>
        (kernelRun (fun op J q => ProbComp.eval (idealJoint (W₁ op) J (S₂ op J) q)) I P.steps
          (fun i => (x i, c₁ i))).bind fun res =>
            ProbComp.eval
              (D (fun i : I => ⟨x i.1, (c₁ i.1, (res.1 i).1), (res.1 i).2⟩, res.2)) := by
  have h := congrArg (fun p => p.bind fun r => ProbComp.eval (D r))
    (Protocol.realJoint_bind_expandSimSteps_eq_kernelRun P W₁ S₂ I x)
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def] at h
  rw [← h]
  refine congrArg (P.realJoint W₁ I x).bind (funext fun r => ?_)
  obtain ⟨v₁, y⟩ := r
  simp only [composeDistinguisher, ProbComp.eval_bind]

/-- **The subprotocol-replacement gap is a kernel gap.** The replacement gap of
`semiHonestAdvantage_compose_le` is the advantage of one test between two runs of the same kernel
program `kernelRun` of `P.steps`, after sampling the outer coins: on the ideal joint distributions
`idealJoint (W₁ op) J (S₂ op J) q` of the subprotocols and on their real joint distributions
`(Sub op).realJoint W₂ J q`. The two runs differ only in the kernel that each oracle round draws
from, which is the setting of the hybrid argument over the oracle rounds. Nothing is assumed about
`P`, `Sub` or the simulators, and no bound on the gap is derived here. -/
theorem advantage_replacement_eq_kernelRun (P : Protocol m spec₁ sc₁ In Coins₁ Out)
    (W₁ : MultiOracleWorld spec₁) (W₂ : MultiOracleWorld spec₂)
    (Sub : (op : spec₁.Op) →
      Protocol (spec₁.arity op) spec₂ (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op))
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
    (I : Finset (Fin m)) (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In (Schedule.ComposedCoins Coins₂ Coins₁ sc₁)
      (Schedule.compose sc₂ sc₁) i) × ((i : Fin m) → Out i) → ProbComp Bool) :
    Game.advantage
        ((P.realJoint W₁ I x).bind fun r =>
          ProbComp.eval (composeDistinguisher P S₂ I x D r))
        (((P.compose Sub).realJoint W₂ I x).bind fun r => ProbComp.eval (D r)) =
      Game.advantage
        ((ProbComp.eval (OracleComp.pi P.sampleCoins)).bind fun c₁ =>
          (kernelRun (fun op J q => ProbComp.eval (idealJoint (W₁ op) J (S₂ op J) q)) I P.steps
            (fun i => (x i, c₁ i))).bind fun res =>
              ProbComp.eval
                (D (fun i : I => ⟨x i.1, (c₁ i.1, (res.1 i).1), (res.1 i).2⟩, res.2)))
        ((ProbComp.eval (OracleComp.pi P.sampleCoins)).bind fun c₁ =>
          (kernelRun (fun op J q => (Sub op).realJoint W₂ J q) I P.steps
            (fun i => (x i, c₁ i))).bind fun res =>
              ProbComp.eval
                (D (fun i : I => ⟨x i.1, (c₁ i.1, (res.1 i).1), (res.1 i).2⟩, res.2))) := by
  rw [Protocol.bind_realJoint_composeDistinguisher_eq_kernelRun,
    Protocol.realJoint_compose_eq_kernelRun]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]

end Cslib.Crypto.Protocols.MPC
