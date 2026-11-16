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
# Authenticated key exchange: static security

Defines the active AKE adversary type, experiment execution (`Protocol.run`), advantage
(`Protocol.staticAdvantage`), and static security (`Protocol.StaticallySecure`, Definition 21.1 of
[BonehShoup2023], §21.9, p. 888).

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
* `Cslib.Crypto.AKE.Protocol.StaticallySecureWith`, `Protocol.StaticallySecure`: Definition 21.1.

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
strict oracle-PPT adversaries ([BonehShoup2023], §21.9, p. 888). -/
@[expose]
def Protocol.StaticallySecureWith (P : Protocol) (pf : PartnerFunction) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (P.run none adversary n))
    (fun adversary n => ProbComp.eval (P.run (some { partner := pf n }) adversary n))
    (IsOraclePPT encBool)

/-- An AKE protocol `P` is statically secure if there exists a polynomial-time partner function
`pf` such that `P.StaticallySecureWith pf` ([BonehShoup2023], §21.9, Definition 21.1, p. 888).

`P` ranges over `Protocol`, whose algorithms are polynomial time on each call and whose stored
states obey polynomial bounds standing in for the book's efficient TTP interface and poly-bounded
instance configurations; the module defining `Protocol` compares the two.
As in the book, this definition includes no correctness clause; the protocol `abortProtocol` that
immediately aborts every session satisfies `Protocol.StaticallySecure`
(`abortProtocol_staticallySecure`). -/
@[expose]
def Protocol.StaticallySecure (P : Protocol) : Prop :=
  ∃ pf : PartnerFunction,
    ComputableInPolyTime (fun input : ℕ × List LogEntry => pf input.1 input.2)
      (encPair encUnary encLog) encClassification ∧
    P.StaticallySecureWith pf

end Cslib.Crypto.AKE
