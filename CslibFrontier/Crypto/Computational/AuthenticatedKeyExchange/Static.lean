/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.AuthenticatedKeyExchange.Experiment
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter

/-!
# Authenticated key exchange: static security in a guarded, bounded-message model

Defines the active AKE adversary type, experiment execution (`Protocol.run`), advantage
(`Protocol.staticAdvantage`), and static security (`Protocol.StaticallySecure`). This is a
milestone toward Definition 21.1 of [BonehShoup2023] (§21.9, p. 888), not that definition. It
differs from it in three ways:

* **The guard is part of the protocol's semantics.** The challenger refuses any query that would
  hand a protocol algorithm a user identity or message longer than `P.sizeBound n`
  (`Protocol.TooLong`) before the algorithm runs. `StaticallySecure P` is therefore the security
  of `P` behind this guard, which need not be the security of the unguarded algorithms. An
  algorithm that misbehaves only on refused inputs is never exposed.
* **Inputs and stored state are bounded.** Incoming user identities and messages, long-term keys
  and instance states have at most `P.sizeBound n` bits, and each TTP call adds at most
  `P.sizeBound n` bits to the TTP state. Outgoing messages and TTP replies have no fixed cap; only
  the running time of the algorithm that produces them bounds them. The module defining
  `Protocol` compares these bounds with the book's efficient interface (Definition 2.12, p. 33)
  and poly-bounded configurations (§18.1.1, p. 718).
* **Rounds are unbounded.** `Protocol` does not require the polynomial terminal-round condition of
  §18.1.1 (p. 718), to which §21.9 refers: a session that stays `running` forever is admitted.

The textbook definition, with the §18.1.1 conditions, remains open (#5670).

As in [BonehShoup2023], §21.9, static security carries no correctness requirement: the protocol
that always aborts satisfies `Protocol.StaticallySecure` (verified in the test suite by
`abortProtocol_staticallySecure`), and no protocol that finishes a session is proved statically
secure here. `Protocol.staticAdvantage` and `Protocol.StaticallySecure` leave
`Idealization.exposed` at its default (`fun _ _ => false`).

## Main definitions

* `Cslib.Crypto.AKE.Adversary`: active AKE adversary with word-oracle queries `Op`.
* `Cslib.Crypto.AKE.Protocol.run`: execution in Experiment 0 (`ideal = none`) or Experiment 1
  (`ideal = some idl`).
* `Cslib.Crypto.AKE.Protocol.staticAdvantage`: distinguishing advantage `|Pr[W₀] − Pr[W₁]|`.
* `Cslib.Crypto.AKE.Protocol.StaticallySecureWith`, `Protocol.StaticallySecure`: static security in
  the guarded, bounded-message model, a milestone toward Definition 21.1.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 21.9, Definition 21.1, p. 888.
-/

public section

namespace Cslib.Crypto.AKE

open Probability Turing.MultiTapeTM
open scoped NNReal

/-- Active AKE adversary taking unary security parameter `n` and empty auxiliary input `[]`, with
oracle access to `Op` ([BonehShoup2023], §21.9, pp. 886–888). -/
abbrev Adversary : Type := ℕ → List Bool → WordOracleComp Op Bool

/-- Execute `adversary` at security parameter `n` against `challenger P n ideal`, returning the
adversary's output bit (`ideal = none` is Experiment 0; `ideal = some idl` is Experiment 1). -/
@[expose]
noncomputable def Protocol.run (P : Protocol) (ideal : Option Idealization)
    (adversary : Adversary) (n : ℕ) : ProbComp Bool := do
  let ttp ← P.ttpInit n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k)) (challenger P n ideal))
    (adversary n [])).run { ttp }
  pure out.1

/-- Distinguishing advantage `sKEadv[A, Π, pf] = |Pr[W₀] − Pr[W₁]|` between Experiment 0 and
Experiment 1 with partner function `pf` (leaving `Idealization.exposed` at its default). -/
@[expose]
noncomputable def Protocol.staticAdvantage (P : Protocol) (pf : PartnerFunction)
    (adversary : Adversary) (n : ℕ) : ℝ≥0 :=
  Game.advantage (ProbComp.eval (P.run none adversary n))
    (ProbComp.eval (P.run (some { partner := pf n }) adversary n))

/-- Static security of `P` with respect to a fixed partner function `pf` against all uniform
strict oracle-PPT adversaries, in the guarded, bounded-message model of this module: the
experiments of [BonehShoup2023], §21.9, p. 888, with over-long words refused before any protocol
algorithm runs. -/
@[expose]
def Protocol.StaticallySecureWith (P : Protocol) (pf : PartnerFunction) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (P.run none adversary n))
    (fun adversary n => ProbComp.eval (P.run (some { partner := pf n }) adversary n))
    (IsOraclePPT encBool)

/-- An AKE protocol `P` is statically secure in the guarded, bounded-message model if there exists a
polynomial-time partner function `pf` such that `P.StaticallySecureWith pf`. The shape is that of
Definition 21.1 ([BonehShoup2023], §21.9, p. 888), but the notion is novel to this library and is
not Definition 21.1:

* the challenger refuses over-long user identities and messages before any protocol algorithm
  runs, so this is the security of `P` behind that guard, not of its unguarded algorithms;
* incoming user identities and messages, long-term keys and instance states have at most
  `P.sizeBound n` bits, and each TTP call adds at most `P.sizeBound n` bits to the TTP state;
  outgoing messages have no fixed cap;
* `P` need not reach a terminal state within polynomially many rounds, as §18.1.1 (p. 718)
  requires.

The textbook definition remains open (#5670). As in the book, there is no
correctness clause; the protocol `abortProtocol` that immediately aborts every session satisfies
`Protocol.StaticallySecure` (`abortProtocol_staticallySecure`). -/
@[expose]
def Protocol.StaticallySecure (P : Protocol) : Prop :=
  ∃ pf : PartnerFunction,
    ComputableInPolyTime (fun input : ℕ × List LogEntry => pf input.1 input.2)
      (encPair encUnary encLog) encClassification ∧
    P.StaticallySecureWith pf

end Cslib.Crypto.AKE
