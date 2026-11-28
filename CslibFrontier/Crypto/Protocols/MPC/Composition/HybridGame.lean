/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.Hybrid
public import CslibFrontier.Crypto.Protocols.MPC.Composition.Hybrid

/-!
# The round hybrids of a composed protocol as games of one environment

`CslibFrontier/Crypto/Protocols/MPC/Composition/Hybrid.lean` bounds the subprotocol-replacement gap
of a composed protocol by `Composition.replacementBound`, an expectation over the earlier rounds of
the advantages of distinguishers that depend on the outcome of these rounds. The absolute value is
inside that expectation, so the bound cannot be compared with the advantage of one distinguisher
that samples the earlier rounds itself: `E |X| ≥ |E X|`.

This module gives the hybrid argument with the absolute value outside. The `j`-th hybrid of the
kernel program `Composition.kernelRun` draws the first `j` oracle rounds from the real kernel and
the later ones from the ideal kernel. Consecutive hybrids differ in the kernel of one oracle round,
and both are the game of one environment, `Composition.roundEnv`: it runs the first `j` oracle
rounds on the real kernel and stops at the next one with a `Composition.RoundChallenge`: the
operation of that round, the corrupted slots, the query tuple, and a guessing stage, the program
`Composition.roundDistinguisher`, which simulates the remaining rounds and runs the given test.
`Composition.roundGame κ` draws the challenged round from the kernel `κ` and runs the guessing
stage. The environment does not depend on `κ`, so for `κ` the ideal and the real joint distribution
of a subprotocol the two games are the ideal and the real semi-honest game of that subprotocol
against one environment that chooses the input tuple.

Everything here is original bookkeeping for the hybrid argument in the proof of Goldreich's
composition theorem (Section 7.5.2.1, Theorem 7.5.7), not a cited statement. The statements are
equalities of distributions and triangle inequalities: there is no security parameter, the first
stage of an environment is a distribution rather than a program, because it draws the earlier
rounds from the real joint distributions, and nothing is claimed about the efficiency of either
stage. The asymptotic composition theorem is not proved here (#6045).

## Main definitions

* `Cslib.Crypto.Protocols.MPC.Schedule.oracleRounds`: the number of oracle rounds of a schedule.
* `Cslib.Crypto.Protocols.MPC.Composition.RoundChallenge`: a challenged oracle round with its
  guessing stage.
* `Cslib.Crypto.Protocols.MPC.Composition.roundGame`: the game that draws a challenged round from a
  kernel.
* `Cslib.Crypto.Protocols.MPC.Composition.roundEnv`: the environment of the `j`-th hybrid hop of a
  kernel program.
* `Cslib.Crypto.Protocols.MPC.composeRoundEnv`: the environment of the `j`-th hybrid hop of a
  composed protocol, which also samples the outer coins.

## Main results

* `Cslib.Crypto.Protocols.MPC.Composition.roundEnv_zero_bind_roundGame`,
  `Cslib.Crypto.Protocols.MPC.Composition.roundEnv_succ_bind_roundGame`,
  `Cslib.Crypto.Protocols.MPC.Composition.roundEnv_bind_roundGame_of_oracleRounds_le`: the hybrids
  of a kernel program are the games of `roundEnv`; the first is the ideal run, the last the real
  run, and the ideal game of hop `j + 1` is the real game of hop `j`.
* `Cslib.Crypto.Protocols.MPC.composeRoundEnv_zero_bind_roundGame`,
  `Cslib.Crypto.Protocols.MPC.composeRoundEnv_succ_bind_roundGame`,
  `Cslib.Crypto.Protocols.MPC.composeRoundEnv_bind_roundGame_of_oracleRounds_le`: the same for a
  composed protocol, between the outer protocol against `composeDistinguisher` and the composed
  protocol.
* `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_compose_le_sum_roundGame`: the advantage against
  `P.compose Sub` is at most the advantage of `composeDistinguisher` against `P` plus the sum over
  the oracle rounds of the advantage of one environment between the ideal and the real game of the
  challenged round.
* `Cslib.Crypto.Protocols.MPC.Composition.bind_elim_bind_roundGame`: an outer stage followed by an
  environment is one environment.
* `Cslib.Crypto.Protocols.MPC.advantage_bind_compose_le_add_sum_roundGame`: the same bound when the
  protocols, inputs and distinguisher depend on the outcome of a common outer stage, such as a
  trusted setup or the environment of an enclosing composition, with every absolute value outside
  the expectation over it.

## References

* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004],
  Section 7.5.2.1 (Theorem 7.5.7).
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib.Probability Cslib.ProbComp
open _root_.Cslib.Crypto.Protocols.MPC.Composition
open scoped NNReal

/-- The number of oracle rounds of a schedule. -/
@[expose] def Schedule.oracleRounds {m : ℕ} {spec : MultiOracleSpec} : Schedule m spec → ℕ
  | [] => 0
  | .message _ _ _ :: rest => Schedule.oracleRounds rest
  | .oracle _ _ :: rest => Schedule.oracleRounds rest + 1

namespace Composition

variable {m : ℕ} {spec₁ spec₂ : MultiOracleSpec}
  {sc₂ : (op : spec₁.Op) → Schedule (spec₁.arity op) spec₂}
  {Coins₂ : (op : spec₁.Op) → Fin (spec₁.arity op) → Type}

/-- **A challenged oracle round.** The oracle operation `op` of the round, the corrupted slots
`coalition`, the query tuple `query` of the slots, and the guessing stage `guess`, a program that
turns the views of the corrupted slots in a subprotocol for `op` and the answers of all slots into
a bit. -/
structure RoundChallenge (sc₂ : (op : spec₁.Op) → Schedule (spec₁.arity op) spec₂)
    (Coins₂ : (op : spec₁.Op) → Fin (spec₁.arity op) → Type) where
  /-- The oracle operation of the challenged round. -/
  op : spec₁.Op
  /-- The corrupted slots of the operation. -/
  coalition : Finset (Fin (spec₁.arity op))
  /-- The query tuple of the slots. -/
  query : (s : Fin (spec₁.arity op)) → spec₁.Query op s
  /-- The guess from the views of the corrupted slots and the answers of all slots. -/
  guess : ((s : coalition) → PartyView (spec₁.Query op) (Coins₂ op) (sc₂ op) s) ×
    ((s : Fin (spec₁.arity op)) → spec₁.Answer op s) → ProbComp Bool

/-- **The game of a challenged round on the kernel `κ`.** An environment either has already decided
its bit, or it stops at a challenged round `c`; the views of the corrupted slots and the answers of
that round are then drawn from `κ c.op c.coalition c.query` and given to the guessing stage. For
`κ` the ideal and the real joint distribution of a subprotocol, the two games on `c` are the two
games of `semiHonestAdvantage` for that subprotocol, on the input tuple `c.query` against
`c.guess`. -/
@[expose] noncomputable def roundGame
    (κ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      ((s : Fin (spec₁.arity op)) → spec₁.Query op s) →
      PMF (((s : J) → PartyView (spec₁.Query op) (Coins₂ op) (sc₂ op) s) ×
        ((s : Fin (spec₁.arity op)) → spec₁.Answer op s))) :
    Bool ⊕ RoundChallenge sc₂ Coins₂ → Game :=
  Sum.elim PMF.pure fun c =>
    (κ c.op c.coalition c.query).bind fun r => ProbComp.eval (c.guess r)

/-- **Two stages as one environment.** An outer stage `e` that either decides a bit or produces an
index `a`, followed by an environment `g a`, is one environment: its round game is the outer stage
followed by the round game of `g a`. -/
theorem bind_elim_bind_roundGame {β : Type}
    (κ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      ((s : Fin (spec₁.arity op)) → spec₁.Query op s) →
      PMF (((s : J) → PartyView (spec₁.Query op) (Coins₂ op) (sc₂ op) s) ×
        ((s : Fin (spec₁.arity op)) → spec₁.Answer op s)))
    (e : PMF (Bool ⊕ β)) (g : β → PMF (Bool ⊕ RoundChallenge sc₂ Coins₂)) :
    (e.bind (Sum.elim (fun b => PMF.pure (Sum.inl b)) g)).bind (roundGame κ) =
      e.bind (Sum.elim PMF.pure fun a => (g a).bind (roundGame κ)) := by
  rw [PMF.bind_bind]
  exact congrArg _ (funext fun | .inl _ => by simp [roundGame] | .inr _ => rfl)

/-- **The environment of the `j`-th hybrid hop of a kernel program.** It runs `steps` from the
states `st`, drawing the first `j` oracle rounds from the kernel `ν`, and stops at the next oracle
round with the challenge of that round. The guessing stage is `roundDistinguisher`: it delivers the
answers, runs the remaining rounds with the ideal functionalities `W₁` and the simulators `S₂`,
puts the given views in front of the result and runs the test `D`. When `steps` has at most `j`
oracle rounds, the environment runs `D` itself and returns the bit.

`roundGame` on the ideal joint distributions after this environment is the `j`-th hybrid of the
kernel program, and `roundGame ν` the hybrid `j + 1` (`roundEnv_succ_bind_roundGame`). -/
@[expose] noncomputable def roundEnv (W₁ : MultiOracleWorld spec₁)
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
    (ν : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      ((s : Fin (spec₁.arity op)) → spec₁.Query op s) →
      PMF (((s : J) → PartyView (spec₁.Query op) (Coins₂ op) (sc₂ op) s) ×
        ((s : Fin (spec₁.arity op)) → spec₁.Answer op s)))
    (I : Finset (Fin m)) {State Out : Fin m → Type} {sc₁ : Schedule m spec₁}
    (steps : Steps State Out sc₁) (j : ℕ) (st : (i : Fin m) → State i)
    (D : ((i : I) → Schedule.SubCoins Coins₂ sc₁ i.val ×
      Schedule.Received (Schedule.compose sc₂ sc₁) i.val) × ((i : Fin m) → Out i) →
        ProbComp Bool) :
    PMF (Bool ⊕ RoundChallenge sc₂ Coins₂) :=
  match steps, j with
  | .done output, _ =>
    (ProbComp.eval (D (fun _ => ((), ()), fun i => output i (st i)))).map Sum.inl
  | .message (sender := s₀) (receiver := r₀) send next, j =>
    roundEnv W₁ S₂ ν I next j (fun i => (st i, Round.deliverMessage (send (st s₀)) i))
      fun res => D (fun i : I => ((res.1 i).1,
        (Round.deliverMessage (spec := spec₂) (sender := s₀) (receiver := r₀)
          (send (st s₀)) i.val, (res.1 i).2)), res.2)
  | .oracle (op := op) (parties := parties) query next, 0 =>
    PMF.pure (Sum.inr
      { op := op
        coalition := subCoalition parties I
        query := fun s => query s (st (parties s))
        guess := roundDistinguisher W₁ S₂ I next st D })
  | .oracle (op := op) (parties := parties) query next, j + 1 =>
    (ν op (subCoalition parties I) fun s => query s (st (parties s))).bind fun r =>
      roundEnv W₁ S₂ ν I next j (fun i => (st i, Round.deliverOracle parties r.2 i))
        fun res => D (fun i : I =>
          ((pushTupleRestrict parties I (fun s => (r.1 s).coins) i, (res.1 i).1),
            Schedule.Received.append
              (pushScheduleReceivedRestrict parties I (sc₂ op)
                (fun s => (r.1 s).received) i)
              (res.1 i).2),
          res.2)

variable (W₁ : MultiOracleWorld spec₁)
  (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
    CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
  (ν : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
    ((s : Fin (spec₁.arity op)) → spec₁.Query op s) →
    PMF (((s : J) → PartyView (spec₁.Query op) (Coins₂ op) (sc₂ op) s) ×
      ((s : Fin (spec₁.arity op)) → spec₁.Answer op s)))
  (I : Finset (Fin m)) {State Out : Fin m → Type} {sc₁ : Schedule m spec₁}

/-- **The first hybrid is the ideal run.** The game of the environment of hop `0` on the ideal
joint distributions is the kernel program on these distributions followed by the test. -/
theorem roundEnv_zero_bind_roundGame (steps : Steps State Out sc₁) (st : (i : Fin m) → State i)
    (D : ((i : I) → Schedule.SubCoins Coins₂ sc₁ i.val ×
      Schedule.Received (Schedule.compose sc₂ sc₁) i.val) × ((i : Fin m) → Out i) →
        ProbComp Bool) :
    (roundEnv W₁ S₂ ν I steps 0 st D).bind
        (roundGame fun op J q => ProbComp.eval (idealJoint (W₁ op) J (S₂ op J) q)) =
      (kernelRun (fun op J q => ProbComp.eval (idealJoint (W₁ op) J (S₂ op J) q)) I steps
        st).bind fun res => ProbComp.eval (D res) := by
  induction steps with
  | done =>
    simp only [roundEnv, kernelRun, roundGame, PMF.bind_map, Function.comp_def, Sum.elim_inl,
      PMF.bind_pure, PMF.pure_bind]
  | message _ _ ih => rw [roundEnv, ih, kernelRun, PMF.bind_map]; rfl
  | oracle _ _ ih =>
    rw [roundEnv, PMF.pure_bind, kernelRun_oracle, PMF.bind_bind]
    simp only [roundGame, Sum.elim_inr, roundDistinguisher, ProbComp.eval_bind, eval_kernelProg,
      PMF.bind_map, Function.comp_def]

/-- **Consecutive hybrids differ in the kernel of one round.** The game of the environment of hop
`j + 1` on the ideal joint distributions is the game of the environment of hop `j` on the kernel
`ν`: both draw the first `j + 1` oracle rounds from `ν` and the later ones from the ideal joint
distributions. -/
theorem roundEnv_succ_bind_roundGame (steps : Steps State Out sc₁) (j : ℕ)
    (st : (i : Fin m) → State i)
    (D : ((i : I) → Schedule.SubCoins Coins₂ sc₁ i.val ×
      Schedule.Received (Schedule.compose sc₂ sc₁) i.val) × ((i : Fin m) → Out i) →
        ProbComp Bool) :
    (roundEnv W₁ S₂ ν I steps (j + 1) st D).bind
        (roundGame fun op J q => ProbComp.eval (idealJoint (W₁ op) J (S₂ op J) q)) =
      (roundEnv W₁ S₂ ν I steps j st D).bind (roundGame ν) := by
  induction steps generalizing j with
  | done => simp only [roundEnv, roundGame, PMF.bind_map, Function.comp_def, Sum.elim_inl]
  | message _ _ ih =>
    rw [roundEnv, roundEnv]
    exact ih _ _ _
  | oracle _ _ ih =>
    cases j with
    | zero =>
      rw [roundEnv, roundEnv, PMF.pure_bind, PMF.bind_bind]
      simp only [roundGame, Sum.elim_inr, roundDistinguisher, ProbComp.eval_bind, eval_kernelProg]
      exact congrArg _ (funext fun _ => roundEnv_zero_bind_roundGame W₁ S₂ ν I _ _ _)
    | succ j =>
      rw [roundEnv, roundEnv, PMF.bind_bind, PMF.bind_bind]
      exact congrArg _ (funext fun _ => ih _ _ _)

/-- **The last hybrid is the real run.** When `steps` has at most `j` oracle rounds, the
environment of hop `j` challenges no round, and its game on any kernel `κ` is the kernel program on
`ν` followed by the test. -/
theorem roundEnv_bind_roundGame_of_oracleRounds_le
    (κ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      ((s : Fin (spec₁.arity op)) → spec₁.Query op s) →
      PMF (((s : J) → PartyView (spec₁.Query op) (Coins₂ op) (sc₂ op) s) ×
        ((s : Fin (spec₁.arity op)) → spec₁.Answer op s)))
    (steps : Steps State Out sc₁) {j : ℕ} (hj : sc₁.oracleRounds ≤ j)
    (st : (i : Fin m) → State i)
    (D : ((i : I) → Schedule.SubCoins Coins₂ sc₁ i.val ×
      Schedule.Received (Schedule.compose sc₂ sc₁) i.val) × ((i : Fin m) → Out i) →
        ProbComp Bool) :
    (roundEnv W₁ S₂ ν I steps j st D).bind (roundGame κ) =
      (kernelRun ν I steps st).bind fun res => ProbComp.eval (D res) := by
  induction steps generalizing j with
  | done =>
    simp only [roundEnv, kernelRun, roundGame, PMF.bind_map, Function.comp_def, Sum.elim_inl,
      PMF.bind_pure, PMF.pure_bind]
  | message _ _ ih => rw [roundEnv, ih hj, kernelRun, PMF.bind_map]; rfl
  | oracle _ _ ih =>
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by rw [Schedule.oracleRounds] at hj; omega⟩
    rw [roundEnv, PMF.bind_bind, kernelRun_oracle, PMF.bind_bind]
    exact congrArg _ (funext fun _ => by rw [ih (Nat.le_of_succ_le_succ hj), PMF.bind_map]; rfl)

end Composition

variable {m : ℕ} {spec₁ spec₂ : MultiOracleSpec} {sc₁ : Schedule m spec₁}
  {sc₂ : (op : spec₁.Op) → Schedule (spec₁.arity op) spec₂} {In Coins₁ Out : Fin m → Type}
  {Coins₂ : (op : spec₁.Op) → Fin (spec₁.arity op) → Type}

/-- **The environment of the `j`-th hybrid hop of a composed protocol.** For the outer protocol `P`
on the input tuple `x` and a distinguisher `D` of the coalition `I`'s views of `P.compose Sub`, it
samples the outer coins, runs `P.steps` with the first `j` oracle rounds drawn from the real joint
distributions `(Sub op).realJoint W₂` of the subprotocols, and stops at the next oracle round with
the challenge of that round (`Composition.roundEnv`): the guessing stage
`Composition.roundDistinguisher` simulates the later rounds with `W₁` and `S₂` and runs `D`. -/
@[expose] noncomputable def composeRoundEnv (P : Protocol m spec₁ sc₁ In Coins₁ Out)
    (W₁ : MultiOracleWorld spec₁) (W₂ : MultiOracleWorld spec₂)
    (Sub : (op : spec₁.Op) →
      Protocol (spec₁.arity op) spec₂ (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op))
    (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
    (I : Finset (Fin m)) (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In (Schedule.ComposedCoins Coins₂ Coins₁ sc₁)
      (Schedule.compose sc₂ sc₁) i) × ((i : Fin m) → Out i) → ProbComp Bool) (j : ℕ) :
    PMF (Bool ⊕ RoundChallenge sc₂ Coins₂) :=
  (ProbComp.eval (OracleComp.pi P.sampleCoins)).bind fun c₁ =>
    roundEnv W₁ S₂ (fun op J q => (Sub op).realJoint W₂ J q) I P.steps j (fun i => (x i, c₁ i))
      fun res => D (fun i : I => ⟨x i.val, (c₁ i.val, (res.1 i).1), (res.1 i).2⟩, res.2)

section ComposeRoundEnv

variable (P : Protocol m spec₁ sc₁ In Coins₁ Out) (W₁ : MultiOracleWorld spec₁)
  (W₂ : MultiOracleWorld spec₂)
  (Sub : (op : spec₁.Op) →
    Protocol (spec₁.arity op) spec₂ (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op))
  (S₂ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
    CoalitionSimulator (sc₂ op) (spec₁.Query op) (Coins₂ op) (spec₁.Answer op) J)
  (I : Finset (Fin m)) (x : (i : Fin m) → In i)
  (D : ((i : I) → PartyView In (Schedule.ComposedCoins Coins₂ Coins₁ sc₁)
    (Schedule.compose sc₂ sc₁) i) × ((i : Fin m) → Out i) → ProbComp Bool)

/-- **The first hybrid of a composed protocol.** The ideal game of the environment of hop `0` is
the real execution of the outer protocol `P` in `W₁` against the reduction
`composeDistinguisher P S₂ I x D`. -/
theorem composeRoundEnv_zero_bind_roundGame :
    (composeRoundEnv P W₁ W₂ Sub S₂ I x D 0).bind
        (roundGame fun op J q => ProbComp.eval (idealJoint (W₁ op) J (S₂ op J) q)) =
      (P.realJoint W₁ I x).bind fun r => ProbComp.eval (composeDistinguisher P S₂ I x D r) := by
  rw [Protocol.bind_realJoint_composeDistinguisher_eq_kernelRun, composeRoundEnv, PMF.bind_bind]
  exact congrArg _ (funext fun c₁ => roundEnv_zero_bind_roundGame W₁ S₂ _ I P.steps _ _)

/-- **Consecutive hybrids of a composed protocol.** The ideal game of the environment of hop
`j + 1` is the real game of the environment of hop `j`. -/
theorem composeRoundEnv_succ_bind_roundGame (j : ℕ) :
    (composeRoundEnv P W₁ W₂ Sub S₂ I x D (j + 1)).bind
        (roundGame fun op J q => ProbComp.eval (idealJoint (W₁ op) J (S₂ op J) q)) =
      (composeRoundEnv P W₁ W₂ Sub S₂ I x D j).bind
        (roundGame fun op J q => (Sub op).realJoint W₂ J q) := by
  rw [composeRoundEnv, composeRoundEnv, PMF.bind_bind, PMF.bind_bind]
  exact congrArg _ (funext fun c₁ => roundEnv_succ_bind_roundGame W₁ S₂ _ I P.steps j _ _)

/-- **The last hybrid of a composed protocol.** When `P` has at most `j` oracle rounds, the game of
the environment of hop `j` on any kernel `κ` is the real execution of `P.compose Sub` in `W₂`
against `D`. -/
theorem composeRoundEnv_bind_roundGame_of_oracleRounds_le
    (κ : (op : spec₁.Op) → (J : Finset (Fin (spec₁.arity op))) →
      ((s : Fin (spec₁.arity op)) → spec₁.Query op s) →
      PMF (((s : J) → PartyView (spec₁.Query op) (Coins₂ op) (sc₂ op) s) ×
        ((s : Fin (spec₁.arity op)) → spec₁.Answer op s)))
    {j : ℕ} (hj : sc₁.oracleRounds ≤ j) :
    (composeRoundEnv P W₁ W₂ Sub S₂ I x D j).bind (roundGame κ) =
      ((P.compose Sub).realJoint W₂ I x).bind fun r => ProbComp.eval (D r) := by
  rw [Protocol.realJoint_compose_eq_kernelRun, composeRoundEnv, PMF.bind_bind, PMF.bind_bind]
  refine congrArg _ (funext fun c₁ => ?_)
  rw [roundEnv_bind_roundGame_of_oracleRounds_le W₁ S₂ _ I κ P.steps hj, PMF.bind_map]
  rfl

/-- **Composition bound with one environment per oracle round.** For every outer protocol `P` in
the oracle world `W₁`, outer simulators `S₁`, subprotocols `Sub` in `W₂` and subprotocol simulators
`S₂`, the semi-honest advantage of `D` against `P.compose Sub` with the composed simulator is at
most the advantage of the reduction `composeDistinguisher P S₂ I x D` against `P` with `S₁ I`, plus
the sum over the oracle rounds `j` of `P` of the advantage of the environment `composeRoundEnv` of
hop `j` between the ideal and the real game of its challenged round. Each summand is the absolute
difference of two acceptance probabilities of one environment, which samples the outer coins and
the earlier rounds itself; compare `semiHonestAdvantage_compose_le_replacementBound`, where the
absolute value is inside the expectation over these.

This is the concrete, per-instance form of the hybrid argument for Goldreich's Theorem 7.5.7, not
the cited theorem: nothing is assumed about `P`, `Sub` or the simulators, and no efficiency of the
environments is claimed. -/
theorem semiHonestAdvantage_compose_le_sum_roundGame (f : Functionality m In Out)
    (S₁ : (I : Finset (Fin m)) → CoalitionSimulator sc₁ In Coins₁ Out I) :
    semiHonestAdvantage (P.compose Sub) W₂ f I (composeSim P (S₁ I) S₂) x D ≤
      semiHonestAdvantage P W₁ f I (S₁ I) x (composeDistinguisher P S₂ I x D) +
        ∑ j ∈ Finset.range sc₁.oracleRounds,
          Game.advantage
            ((composeRoundEnv P W₁ W₂ Sub S₂ I x D j).bind
              (roundGame fun op J q => ProbComp.eval (idealJoint (W₁ op) J (S₂ op J) q)))
            ((composeRoundEnv P W₁ W₂ Sub S₂ I x D j).bind
              (roundGame fun op J q => (Sub op).realJoint W₂ J q)) := by
  refine (semiHonestAdvantage_compose_le P W₁ W₂ f I (S₁ I) Sub S₂ x D).trans
    (add_le_add le_rfl ?_)
  rw [← composeRoundEnv_zero_bind_roundGame P W₁ W₂ Sub S₂ I x D,
    ← composeRoundEnv_bind_roundGame_of_oracleRounds_le P W₁ W₂ Sub S₂ I x D
      (fun op J q => ProbComp.eval (idealJoint (W₁ op) J (S₂ op J) q)) le_rfl]
  refine (Game.advantage_hybrid_le_sum
    (fun j => (composeRoundEnv P W₁ W₂ Sub S₂ I x D j).bind
      (roundGame fun op J q => ProbComp.eval (idealJoint (W₁ op) J (S₂ op J) q)))
    sc₁.oracleRounds).trans_eq ?_
  exact Finset.sum_congr rfl fun j _ => by rw [composeRoundEnv_succ_bind_roundGame]

end ComposeRoundEnv

section Mixture

variable {α : Type} {m : α → ℕ} {spec₁ spec₂ : α → MultiOracleSpec}
  {sc₁ : (a : α) → Schedule (m a) (spec₁ a)}
  {sc₂ : (a : α) → (op : (spec₁ a).Op) → Schedule ((spec₁ a).arity op) (spec₂ a)}
  {In Coins₁ Out : (a : α) → Fin (m a) → Type}
  {Coins₂ : (a : α) → (op : (spec₁ a).Op) → Fin ((spec₁ a).arity op) → Type}

/-- **Composition bound under common outer randomness, with one environment per oracle round.**
Let `p` be the distribution of an outer stage that either decides a bit or produces an index `a`,
such as the description drawn by a trusted setup together with the inputs chosen by an
environment, or the challenge of an environment of an enclosing composition. Let the outer protocol
`P a`, the subprotocols, the simulators, the coalition, the inputs and the distinguisher `D a` all
depend on `a`, with at most `N` oracle rounds. The advantage between the ideal game of
`(P a).compose (Sub a)` with the composed simulator and its real game in `W₂ a`, both after the
outer stage, is at most the advantage between the ideal and the real game of the outer protocol
`P a` in `W₁ a` against `composeDistinguisher`, after the outer stage, plus the sum over `j < N` of
the advantage of one environment between the ideal and the real game of its challenged round: this
environment runs the outer stage and then `composeRoundEnv (P a) … j`. Every absolute value is
outside the expectation over the outer stage, the outer coins and the earlier rounds.

For an outer stage that never decides, take `p = q.map Sum.inr`. Nothing is assumed about the
protocols or the simulators, and no efficiency is claimed. -/
theorem advantage_bind_compose_le_add_sum_roundGame (p : PMF (Bool ⊕ α))
    (P : (a : α) → Protocol (m a) (spec₁ a) (sc₁ a) (In a) (Coins₁ a) (Out a))
    (W₁ : (a : α) → MultiOracleWorld (spec₁ a)) (W₂ : (a : α) → MultiOracleWorld (spec₂ a))
    (f : (a : α) → Functionality (m a) (In a) (Out a))
    (S₁ : (a : α) → (I : Finset (Fin (m a))) →
      CoalitionSimulator (sc₁ a) (In a) (Coins₁ a) (Out a) I)
    (Sub : (a : α) → (op : (spec₁ a).Op) →
      Protocol ((spec₁ a).arity op) (spec₂ a) (sc₂ a op) ((spec₁ a).Query op) (Coins₂ a op)
        ((spec₁ a).Answer op))
    (S₂ : (a : α) → (op : (spec₁ a).Op) → (J : Finset (Fin ((spec₁ a).arity op))) →
      CoalitionSimulator (sc₂ a op) ((spec₁ a).Query op) (Coins₂ a op) ((spec₁ a).Answer op) J)
    (I : (a : α) → Finset (Fin (m a))) (x : (a : α) → (i : Fin (m a)) → In a i)
    (D : (a : α) → ((i : I a) → PartyView (In a)
        (Schedule.ComposedCoins (Coins₂ a) (Coins₁ a) (sc₁ a))
        (Schedule.compose (sc₂ a) (sc₁ a)) i) × ((i : Fin (m a)) → Out a i) → ProbComp Bool)
    (N : ℕ) (hN : ∀ a, (sc₁ a).oracleRounds ≤ N) :
    Game.advantage
        (p.bind (Sum.elim PMF.pure fun a =>
          (ProbComp.eval (idealJoint (f a) (I a) (composeSim (P a) (S₁ a (I a)) (S₂ a))
            (x a))).bind fun r => ProbComp.eval (D a r)))
        (p.bind (Sum.elim PMF.pure fun a =>
          (((P a).compose (Sub a)).realJoint (W₂ a) (I a) (x a)).bind fun r =>
            ProbComp.eval (D a r))) ≤
      Game.advantage
          (p.bind (Sum.elim PMF.pure fun a =>
            (ProbComp.eval (idealJoint (f a) (I a) (S₁ a (I a)) (x a))).bind fun r =>
              ProbComp.eval (composeDistinguisher (P a) (S₂ a) (I a) (x a) (D a) r)))
          (p.bind (Sum.elim PMF.pure fun a =>
            ((P a).realJoint (W₁ a) (I a) (x a)).bind fun r =>
              ProbComp.eval (composeDistinguisher (P a) (S₂ a) (I a) (x a) (D a) r))) +
        ∑ j ∈ Finset.range N,
          Game.advantage
            (p.bind (Sum.elim PMF.pure fun a =>
              (composeRoundEnv (P a) (W₁ a) (W₂ a) (Sub a) (S₂ a) (I a) (x a) (D a) j).bind
                (roundGame fun op J q => ProbComp.eval (idealJoint (W₁ a op) J (S₂ a op J) q))))
            (p.bind (Sum.elim PMF.pure fun a =>
              (composeRoundEnv (P a) (W₁ a) (W₂ a) (Sub a) (S₂ a) (I a) (x a) (D a) j).bind
                (roundGame fun op J q => (Sub a op).realJoint (W₂ a) J q))) := by
  have hideal (a : α) :
      ((ProbComp.eval (idealJoint (f a) (I a) (composeSim (P a) (S₁ a (I a)) (S₂ a))
        (x a))).bind fun r => ProbComp.eval (D a r)) =
      (ProbComp.eval (idealJoint (f a) (I a) (S₁ a (I a)) (x a))).bind fun r =>
        ProbComp.eval (composeDistinguisher (P a) (S₂ a) (I a) (x a) (D a) r) := by
    rw [← ProbComp.eval_bind, ← ProbComp.eval_bind, eval_idealJoint_composeSim_bind]
  simp only [hideal]
  refine (Game.advantage_triangle _ _ _).trans (add_le_add le_rfl ?_)
  simp only [← composeRoundEnv_zero_bind_roundGame (P _) (W₁ _) (W₂ _) (Sub _) (S₂ _) (I _) (x _)
    (D _),
    ← fun a => composeRoundEnv_bind_roundGame_of_oracleRounds_le (P a) (W₁ a) (W₂ a) (Sub a)
      (S₂ a) (I a) (x a) (D a)
      (fun op J q => ProbComp.eval (idealJoint (W₁ a op) J (S₂ a op J) q)) (hN a)]
  refine (Game.advantage_hybrid_le_sum
    (fun j => p.bind (Sum.elim PMF.pure fun a =>
      (composeRoundEnv (P a) (W₁ a) (W₂ a) (Sub a) (S₂ a) (I a) (x a) (D a) j).bind
        (roundGame fun op J q => ProbComp.eval (idealJoint (W₁ a op) J (S₂ a op J) q))))
    N).trans_eq ?_
  exact Finset.sum_congr rfl fun j _ => by simp only [composeRoundEnv_succ_bind_roundGame]

end Mixture

end Cslib.Crypto.Protocols.MPC
