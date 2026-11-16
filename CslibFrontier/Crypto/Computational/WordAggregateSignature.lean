/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Signature.Aggregate
public import CslibFrontier.Crypto.Computational.WordSignature
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Languages.Probabilistic.Oracle.RunState
import CslibFrontier.Tactic.PPT

/-!
# Aggregate signature schemes on bit strings

An aggregate signature scheme ([BonehShoup2023], Definition 15.4, p. 630) is a signature scheme with
two more efficient algorithms: one combines signatures by several signers into one aggregate
signature, the other verifies an aggregate signature against a vector of public keys and a vector
of messages. This module states such schemes on bit strings, with a system parameter, and their two
security notions: security against forgery (Attack Game 15.2 and Definition 15.5, p. 632) and
strong binding (Attack Game 15.3 and Definition 15.6, pp. 632–633).

Differences from the book:

* The scheme carries a system parameter `setup n`, as every algorithm of the book's formal
  framework does (Definition 2.9, p. 30; for hash functions, Section 8.1.1, p. 290). Definition 15.4
  leaves it implicit, but the collision-resistant hash of Exercise 15.11(c) has no meaning without
  it. The aggregation algorithms and both adversaries receive it; the algorithms of the underlying
  `WordSignatureScheme` do not. With `setup = fun _ => pure []` both games are the book's.
* The aggregation algorithm also receives the message vector, as the algorithm `A'` of
  Exercise 15.11(c), p. 675, does. A scheme whose aggregation ignores the messages is the book's.
* Both winning conditions require vectors of equal lengths, the domain of the aggregate
  verification algorithm in Definition 15.4.
* No bound `N` limits the length of the vectors in the games: a strict polynomial-time adversary
  outputs vectors of polynomial length. Correctness (`WordAggregateSignatureScheme.CorrectOn`) is
  stated for the lengths that a predicate allows.
* The book asks for short aggregate signatures (Section 15.5.2); this is not modelled.

## Main definitions

* `Cslib.Crypto.WordAggregateSignatureScheme`: an aggregate signature scheme on bit strings, with
  its efficiency certificates.
* `Cslib.Crypto.WordAggregateSignatureScheme.CorrectOn`: correctness for vectors of admitted
  lengths.
* `Cslib.Crypto.WordAggregateSignatureScheme.asigGame`,
  `Cslib.Crypto.WordAggregateSignatureScheme.ASIG`: Attack Game 15.2 and Definition 15.5.
* `Cslib.Crypto.WordAggregateSignatureScheme.sbAsigGame`,
  `Cslib.Crypto.WordAggregateSignatureScheme.StrongBinding`: Attack Game 15.3 and Definition 15.6.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Definition 2.9 (p. 30), Section 8.1.1 (p. 290), Section 15.5.2 (pp. 630–633) and
  Exercise 15.11(c) (p. 675).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM AggregateSignature

/-- An aggregate signature scheme on bit strings ([BonehShoup2023], Definition 15.4, p. 630): a
`WordSignatureScheme` with a system parameter, an aggregation algorithm and a deterministic
aggregate verification algorithm, each with its efficiency certificate. Short aggregate signatures
are not required. -/
structure WordAggregateSignatureScheme where
  /-- The system parameter generator on the unary security parameter (Definition 2.9, p. 30; for
  hash functions, Section 8.1.1, p. 290). -/
  setup : ℕ → ProbComp (List Bool)
  /-- `setup` is uniform strict PPT. -/
  setup_ppt : IsPPTOn encUnary encBits setup
  /-- The underlying signature scheme `(G, S, V)`; its algorithms do not receive the system
  parameter. -/
  base : WordSignatureScheme
  /-- The aggregation algorithm `aggregate param pks ms sigs`. It receives the message vector
  `ms`, as the algorithm `A'` of Exercise 15.11(c) (p. 675) does; Definition 15.4 writes
  `A(pks, sigs)`. -/
  aggregate : List Bool → List (List Bool) → List (List Bool) → List (List Bool) →
    ProbComp (List Bool)
  /-- `aggregate` is uniform strict PPT. -/
  aggregate_ppt : IsPPTOn
    (encPair encBits (encPair (encList encBits) (encPair (encList encBits) (encList encBits))))
    encBits fun t => aggregate t.1 t.2.1 t.2.2.1 t.2.2.2
  /-- The deterministic aggregate verification algorithm `aggregateVerify param pks ms sigAg`. -/
  aggregateVerify : List Bool → List (List Bool) → List (List Bool) → List Bool → Bool
  /-- `aggregateVerify` is computable in polynomial time. -/
  aggregateVerify_polyTime : ComputableInPolyTime
    (fun t : List Bool × List (List Bool) × List (List Bool) × List Bool =>
      aggregateVerify t.1 t.2.1 t.2.2.1 t.2.2.2)
    (encPair encBits (encPair (encList encBits) (encPair (encList encBits) encBits))) encBool

namespace WordAggregateSignatureScheme

attribute [program_certificate] setup_ppt aggregate_ppt aggregateVerify_polyTime

/-- An adversary of Attack Game 15.2: on the security parameter, the system parameter and the
challenge public key, it makes signing queries and outputs a candidate forgery `(pks, ms, sigAg)`.
-/
abbrev ASIGForger : Type :=
  (ℕ × List Bool) × List Bool →
    WordOracleComp Unit (List (List Bool) × List (List Bool) × List Bool)

/-- An adversary of Attack Game 15.3: on the security parameter and the system parameter, it
outputs `(pks, ms, pks', ms', sigAg)`. -/
abbrev SBAdversary : Type :=
  ℕ × List Bool →
    ProbComp (List (List Bool) × List (List Bool) × List (List Bool) × List (List Bool) × List Bool)

/-- The input encoding of an `ASIGForger`. -/
abbrev asigInputEnc : (ℕ × List Bool) × List Bool ↪ List Bool :=
  encPair (encPair encUnary encBits) encBits

/-- The output encoding of an `ASIGForger`. -/
abbrev asigOutputEnc : List (List Bool) × List (List Bool) × List Bool ↪ List Bool :=
  encPair (encList encBits) (encPair (encList encBits) encBits)

/-- The input encoding of an `SBAdversary`. -/
abbrev sbAsigInputEnc : ℕ × List Bool ↪ List Bool :=
  encPair encUnary encBits

/-- The output encoding of an `SBAdversary`. -/
abbrev sbAsigOutputEnc :
    List (List Bool) × List (List Bool) × List (List Bool) × List (List Bool) × List Bool ↪
      List Bool :=
  encPair (encList encBits)
    (encPair (encList encBits) (encPair (encList encBits) (encPair (encList encBits) encBits)))

/-- Correctness of an aggregate signature scheme ([BonehShoup2023], Definition 15.4, p. 630) for
the vector lengths that `bound n` admits: on every supported system parameter, aggregating
signatures that verify individually gives an aggregate signature that verifies. Definition 15.4
admits the lengths below a bound `N`; `bound := fun _ k => k < N` is that case. -/
@[expose]
def CorrectOn (S : WordAggregateSignatureScheme) (bound : ℕ → ℕ → Prop) : Prop :=
  ∀ (n : ℕ), ∀ param ∈ (ProbComp.eval (S.setup n)).support,
    ∀ (pks ms sigs : List (List Bool)),
      pks.length = ms.length → ms.length = sigs.length → bound n pks.length →
      (∀ (i : ℕ) (hi₁ : i < pks.length) (hi₂ : i < ms.length) (hi₃ : i < sigs.length),
        S.base.verify pks[i] ms[i] sigs[i] = true) →
      ∀ sigAg ∈ (ProbComp.eval (S.aggregate param pks ms sigs)).support,
        S.aggregateVerify param pks ms sigAg = true

/-- Attack Game 15.2 ([BonehShoup2023], p. 632): sample the system parameter and a key pair, run
the forger on `((n, param), pk)` with the signing oracle, and accept when the aggregate signature
verifies and some position of the output carries `pk` and an unqueried message (`asigFresh`). The
system parameter is the book's (Definition 2.9, p. 30); the base signing algorithm does not receive
it. -/
@[expose]
def asigGame (S : WordAggregateSignatureScheme) (A : ASIGForger) (n : ℕ) : ProbComp Bool := do
  let param ← S.setup n
  let (pk, sk) ← S.base.keyGen n
  let ((pks, ms, sigAg), queried) ←
    (ProbOracleComp.runState (A ((n, param), pk)) (S.base.signingOracle sk)).run []
  return S.aggregateVerify param pks ms sigAg && asigFresh pk pks ms queried

/-- Attack Game 15.3 ([BonehShoup2023], pp. 632–633): sample the system parameter, run the
adversary on `(n, param)`, and accept when the aggregate signature verifies for two different
pairs of equal-length vectors (`sbAsigWin`). The book's adversary takes no input; it receives the
security parameter and the system parameter here (Definition 2.9, p. 30). -/
@[expose]
def sbAsigGame (S : WordAggregateSignatureScheme) (A : SBAdversary) (n : ℕ) : ProbComp Bool := do
  let param ← S.setup n
  let (pks, ms, pks', ms', sigAg) ← A (n, param)
  return sbAsigWin (S.aggregateVerify param pks ms sigAg) (S.aggregateVerify param pks' ms' sigAg)
    pks ms pks' ms'

/-- Security of an aggregate signature scheme ([BonehShoup2023], Definition 15.5, p. 632): every
oracle-PPT forger wins Attack Game 15.2 with negligible probability. -/
@[expose]
def ASIG (S : WordAggregateSignatureScheme) : Prop :=
  Game.Indistinguishable (fun (A : ASIGForger) n => ProbComp.eval (S.asigGame A n))
    (fun _ _ => PMF.pure false) fun A => IsOraclePPTOn asigInputEnc asigOutputEnc A

/-- Strong binding ([BonehShoup2023], Definition 15.6, p. 633): every strict PPT adversary wins
Attack Game 15.3 with negligible probability. -/
@[expose]
def StrongBinding (S : WordAggregateSignatureScheme) : Prop :=
  Game.Indistinguishable (fun (A : SBAdversary) n => ProbComp.eval (S.sbAsigGame A n))
    (fun _ _ => PMF.pure false) fun A => IsPPTOn sbAsigInputEnc sbAsigOutputEnc A

end WordAggregateSignatureScheme

end Cslib.Crypto
