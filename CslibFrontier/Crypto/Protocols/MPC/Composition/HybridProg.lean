/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Composition.HybridGame

/-!
# The round-hybrid environments of a composed protocol as programs

The environments `Composition.roundEnv` and `composeRoundEnv` of
`CslibFrontier/Crypto/Protocols/MPC/Composition/HybridGame.lean` are distributions (`PMF`) rather
than programs, because they draw the earlier oracle rounds from the real joint distributions
`Protocol.realJoint` of the subprotocols, which are defined by evaluating an oracle computation in
an oracle world. An oracle world answers every query with a program, so these distributions are
the distributions of programs. This module writes the programs down and proves that they have the
stated distributions.

Everything here is original bookkeeping toward the asymptotic composition theorem (#6045), not a
cited statement. The results are equalities of distributions only: no efficiency (PPT) certificate
is claimed for any of these programs, and the asymptotic composition theorem is not proved here.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.Steps.runProg`: the run of protocol steps in an oracle world, as a
  `ProbComp` that runs the program of the world at every oracle round.
* `Cslib.Crypto.Protocols.MPC.Protocol.realJointProg`: the program that samples the coins, runs the
  protocol in an oracle world and returns the views of a coalition with the outputs of all parties.
* `Cslib.Crypto.Protocols.MPC.Composition.roundEnvProg`: the environment of the `j`-th hybrid hop
  of a kernel program, as a `ProbComp`, for a kernel of programs.
* `Cslib.Crypto.Protocols.MPC.composeRoundEnvProg`: the environment of the `j`-th hybrid hop of a
  composed protocol, as a `ProbComp`, for a kernel of programs.

## Main results

* `Cslib.Crypto.Protocols.MPC.Steps.eval_runProg`: the distribution of `Steps.runProg` is
  `Steps.evalWith`.
* `Cslib.Crypto.Protocols.MPC.Protocol.eval_realJointProg`: the distribution of
  `Protocol.realJointProg` is `Protocol.realJoint`.
* `Cslib.Crypto.Protocols.MPC.Composition.eval_roundEnvProg`: the distribution of
  `Composition.roundEnvProg` is `Composition.roundEnv` on the distributions of the kernel.
* `Cslib.Crypto.Protocols.MPC.eval_composeRoundEnvProg`: for a kernel of programs with the real
  joint distributions of the subprotocols, the distribution of `composeRoundEnvProg` is
  `composeRoundEnv`.
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib.Probability Cslib.ProbComp
open _root_.Cslib.Crypto.Protocols.MPC.Composition

/-- The run of `steps` from the states `st` in the oracle world `W`, as a program: every oracle
round runs the program `W op` of the world on the round's query tuple and delivers its answers. It
returns each party's received transcript, and its distribution is `steps.evalWith W st`
(`Steps.eval_runProg`). -/
@[expose] noncomputable def Steps.runProg {m : ℕ} {spec : MultiOracleSpec}
    {State Out : Fin m → Type} {sc : Schedule m spec} (steps : Steps State Out sc)
    (W : MultiOracleWorld spec) (st : (i : Fin m) → State i) :
    ProbComp ((i : Fin m) → sc.Received i) :=
  match steps with
  | .done _ => pure (fun _ => ())
  | .message (sender := sender) send next =>
    (fun r_tail i => (Round.deliverMessage (send (st sender)) i, r_tail i)) <$>
      next.runProg W (fun i => (st i, Round.deliverMessage (send (st sender)) i))
  | .oracle (op := op) (parties := parties) query next => do
    let ans ← W op (fun s => query s (st (parties s)))
    (fun r_tail i => (Round.deliverOracle parties ans i, r_tail i)) <$>
      next.runProg W (fun i => (st i, Round.deliverOracle parties ans i))

/-- The program `steps.runProg W st` has the distribution `steps.evalWith W st` of the run of
`steps` in the oracle world `W`. -/
theorem Steps.eval_runProg {m : ℕ} {spec : MultiOracleSpec} {State Out : Fin m → Type}
    {sc : Schedule m spec} (steps : Steps State Out sc) (W : MultiOracleWorld spec)
    (st : (i : Fin m) → State i) :
    ProbComp.eval (steps.runProg W st) = steps.evalWith W st := by
  induction steps with
  | done output =>
    simp only [Steps.runProg, Steps.evalWith_done, ProbComp.eval_pure]
  | message send next ih =>
    simp only [Steps.runProg, Steps.evalWith_message, ProbComp.eval_map, ih]
  | oracle query next ih =>
    simp only [Steps.runProg, Steps.evalWith_oracle, ProbComp.eval_bind, ProbComp.eval_map, ih]

/-- The real execution of `proto` on the input tuple `x` in the oracle world `W`, as a program: it
samples each party's coins, runs the steps with `Steps.runProg`, and returns the views of the
coalition `I` with the outputs of all parties. Its distribution is `proto.realJoint W I x`
(`Protocol.eval_realJointProg`). -/
@[expose] noncomputable def Protocol.realJointProg {m : ℕ} {spec : MultiOracleSpec}
    {sc : Schedule m spec} {In Coins Out : Fin m → Type} (proto : Protocol m spec sc In Coins Out)
    (W : MultiOracleWorld spec) (I : Finset (Fin m)) (x : (i : Fin m) → In i) :
    ProbComp (((i : I) → PartyView In Coins sc i) × ((i : Fin m) → Out i)) := do
  let r ← OracleComp.pi proto.sampleCoins
  let recv ← proto.steps.runProg W (fun i => (x i, r i))
  let views : (i : Fin m) → PartyView In Coins sc i := fun i => ⟨x i, r i, recv i⟩
  return (I.restrict views, fun i => proto.outputOfView i (views i))

/-- The program `proto.realJointProg W I x` has the real joint distribution
`proto.realJoint W I x` of the views of the coalition `I` and the outputs of all parties. -/
theorem Protocol.eval_realJointProg {m : ℕ} {spec : MultiOracleSpec} {sc : Schedule m spec}
    {In Coins Out : Fin m → Type} (proto : Protocol m spec sc In Coins Out)
    (W : MultiOracleWorld spec) (I : Finset (Fin m)) (x : (i : Fin m) → In i) :
    ProbComp.eval (proto.realJointProg W I x) = proto.realJoint W I x := by
  simp only [Protocol.realJointProg, Protocol.realJoint, Protocol.evalWith_eq, bind_pure_comp,
    ProbComp.eval_bind, ProbComp.eval_map, Steps.eval_runProg, PMF.map_bind, PMF.map_comp]
  rfl

namespace Composition

variable {m : ℕ} {spec₁ spec₂ : MultiOracleSpec}
  {sc₂ : (op : spec₁.Op) → Schedule (spec₁.arity op) spec₂}
  {Coins₂ : (op : spec₁.Op) → Fin (spec₁.arity op) → Type}

/-- The environment `roundEnv` of the `j`-th hybrid hop of a kernel program as a `ProbComp`, for a
kernel `ν` of programs: it runs `steps` from the states `st`, drawing the first `j` oracle rounds
from the programs `ν`, and stops at the next oracle round with the challenge of that round, whose
guessing stage is `roundDistinguisher`. When `steps` has at most `j` oracle rounds, it runs the
test `D` itself and returns the bit. Its distribution is `roundEnv` on the distributions of `ν`
(`eval_roundEnvProg`). -/
@[expose] noncomputable def roundEnvProg (W₁ : MultiOracleWorld spec₁)
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
    (ν : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      ((s : Fin (spec₁.arity op)) → spec₁.Query op s) →
      ProbComp (((s : J) → PartyView (spec₁.Query op) (Coins₂ op) (sc₂ op) s) ×
        ((s : Fin (spec₁.arity op)) → spec₁.Answer op s)))
    (I : Finset (Fin m)) {State Out : Fin m → Type} {sc₁ : Schedule m spec₁}
    (steps : Steps State Out sc₁) (j : ℕ) (st : (i : Fin m) → State i)
    (D : ((i : I) → Schedule.SubCoins Coins₂ sc₁ i.val ×
      Schedule.Received (Schedule.compose sc₂ sc₁) i.val) × ((i : Fin m) → Out i) →
        ProbComp Bool) :
    ProbComp (Bool ⊕ RoundChallenge sc₂ Coins₂) :=
  match steps, j with
  | .done output, _ =>
    Sum.inl <$> D (fun _ => ((), ()), fun i => output i (st i))
  | .message (sender := s₀) (receiver := r₀) send next, j =>
    roundEnvProg W₁ S₂ ν I next j (fun i => (st i, Round.deliverMessage (send (st s₀)) i))
      fun res => D (fun i : I => ((res.1 i).1,
        (Round.deliverMessage (spec := spec₂) (sender := s₀) (receiver := r₀)
          (send (st s₀)) i.val, (res.1 i).2)), res.2)
  | .oracle (op := op) (parties := parties) query next, 0 =>
    pure (Sum.inr
      { op := op
        coalition := subCoalition parties I
        query := fun s => query s (st (parties s))
        guess := roundDistinguisher W₁ S₂ I next st D })
  | .oracle (op := op) (parties := parties) query next, j + 1 => do
    let r ← ν op (subCoalition parties I) fun s => query s (st (parties s))
    roundEnvProg W₁ S₂ ν I next j (fun i => (st i, Round.deliverOracle parties r.2 i))
      fun res => D (fun i : I =>
        ((pushTupleRestrict parties I (fun s => (r.1 s).coins) i, (res.1 i).1),
          Schedule.Received.append
            (pushScheduleReceivedRestrict parties I (sc₂ op)
              (fun s => (r.1 s).received) i)
            (res.1 i).2),
        res.2)

/-- The program `roundEnvProg W₁ S₂ ν I steps j st D` has the distribution of the environment
`roundEnv` on the distributions of the kernel `ν`. -/
theorem eval_roundEnvProg (W₁ : MultiOracleWorld spec₁)
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
    (ν : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      ((s : Fin (spec₁.arity op)) → spec₁.Query op s) →
      ProbComp (((s : J) → PartyView (spec₁.Query op) (Coins₂ op) (sc₂ op) s) ×
        ((s : Fin (spec₁.arity op)) → spec₁.Answer op s)))
    (I : Finset (Fin m)) {State Out : Fin m → Type} {sc₁ : Schedule m spec₁}
    (steps : Steps State Out sc₁) (j : ℕ) (st : (i : Fin m) → State i)
    (D : ((i : I) → Schedule.SubCoins Coins₂ sc₁ i.val ×
      Schedule.Received (Schedule.compose sc₂ sc₁) i.val) × ((i : Fin m) → Out i) →
        ProbComp Bool) :
    ProbComp.eval (roundEnvProg W₁ S₂ ν I steps j st D) =
      roundEnv W₁ S₂ (fun op J q => ProbComp.eval (ν op J q)) I steps j st D := by
  induction steps generalizing j with
  | done output =>
    simp only [roundEnvProg, roundEnv, ProbComp.eval_map]
  | @message _ _ s₀ r₀ _ _ send next ih =>
    rw [roundEnvProg, roundEnv, ih]
  | @oracle _ _ op parties rest query next ih =>
    cases j with
    | zero => simp only [roundEnvProg, roundEnv, ProbComp.eval_pure]
    | succ j => simp only [roundEnvProg, roundEnv, ProbComp.eval_bind, ih]

end Composition

variable {m : ℕ} {spec₁ spec₂ : MultiOracleSpec} {sc₁ : Schedule m spec₁}
  {sc₂ : (op : spec₁.Op) → Schedule (spec₁.arity op) spec₂} {In Coins₁ Out : Fin m → Type}
  {Coins₂ : (op : spec₁.Op) → Fin (spec₁.arity op) → Type}

/-- The environment `composeRoundEnv` of the `j`-th hybrid hop of a composed protocol as a
`ProbComp`, for a kernel `ν` of programs in place of the real joint distributions of the
subprotocols: it samples the outer coins and runs `Composition.roundEnvProg` on `P.steps`. For `ν`
with the real joint distributions of the subprotocols `Sub` in `W₂`, such as
`fun op J q => (Sub op).realJointProg W₂ J q`, its distribution is `composeRoundEnv`
(`eval_composeRoundEnvProg`). -/
@[expose] noncomputable def composeRoundEnvProg (P : Protocol m spec₁ sc₁ In Coins₁ Out)
    (W₁ : MultiOracleWorld spec₁)
    (ν : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      ((s : Fin (spec₁.arity op)) → spec₁.Query op s) →
      ProbComp (((s : J) → PartyView (spec₁.Query op) (Coins₂ op) (sc₂ op) s) ×
        ((s : Fin (spec₁.arity op)) → spec₁.Answer op s)))
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
    (I : Finset (Fin m)) (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In (Schedule.ComposedCoins Coins₂ Coins₁ sc₁)
      (Schedule.compose sc₂ sc₁) i) × ((i : Fin m) → Out i) → ProbComp Bool) (j : ℕ) :
    ProbComp (Bool ⊕ RoundChallenge sc₂ Coins₂) := do
  let c₁ ← OracleComp.pi P.sampleCoins
  roundEnvProg W₁ S₂ ν I P.steps j (fun i => (x i, c₁ i))
    fun res => D (fun i : I => ⟨x i.val, (c₁ i.val, (res.1 i).1), (res.1 i).2⟩, res.2)

/-- When every program `ν op J q` of the kernel has the real joint distribution
`(Sub op).realJoint W₂ J q` of the subprotocol `Sub op` in the oracle world `W₂`, the program
`composeRoundEnvProg P W₁ ν S₂ I x D j` has the distribution of the environment
`composeRoundEnv P W₁ W₂ Sub S₂ I x D j`. -/
theorem eval_composeRoundEnvProg (P : Protocol m spec₁ sc₁ In Coins₁ Out)
    (W₁ : MultiOracleWorld spec₁) (W₂ : MultiOracleWorld spec₂)
    (Sub : (op : spec₁.Op) →
      Protocol (spec₁.arity op) spec₂ (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op))
    {ν : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      ((s : Fin (spec₁.arity op)) → spec₁.Query op s) →
      ProbComp (((s : J) → PartyView (spec₁.Query op) (Coins₂ op) (sc₂ op) s) ×
        ((s : Fin (spec₁.arity op)) → spec₁.Answer op s))}
    (hν : ∀ op J q, ProbComp.eval (ν op J q) = (Sub op).realJoint W₂ J q)
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
    (I : Finset (Fin m)) (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In (Schedule.ComposedCoins Coins₂ Coins₁ sc₁)
      (Schedule.compose sc₂ sc₁) i) × ((i : Fin m) → Out i) → ProbComp Bool) (j : ℕ) :
    ProbComp.eval (composeRoundEnvProg P W₁ ν S₂ I x D j) =
      composeRoundEnv P W₁ W₂ Sub S₂ I x D j := by
  have h : (fun op J q => ProbComp.eval (ν op J q)) = fun op J q => (Sub op).realJoint W₂ J q :=
    funext fun op => funext fun J => funext fun q => hν op J q
  rw [composeRoundEnvProg, composeRoundEnv, ProbComp.eval_bind]
  refine congrArg _ (funext fun c₁ => ?_)
  rw [eval_roundEnvProg, h]

end Cslib.Crypto.Protocols.MPC
