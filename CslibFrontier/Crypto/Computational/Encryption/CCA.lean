/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Computability.Probabilistic.Traverse
public import CslibFrontier.Computability.Probabilistic.UniformNat
public import CslibFrontier.Crypto.Computational.Encryption.Basic
public import CslibFrontier.Crypto.Game.Hybrid
public import CslibFrontier.Crypto.Encoding
import Mathlib.Data.List.GetD
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Crypto.Computational.Encryption.DecryptionBound
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation.Handler
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.BindCompare
import CslibFrontier.Probability.PMF
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.SuppCases
import CslibFrontier.Tactic.Negligible

/-!
# Chosen-ciphertext security for public-key encryption (1CCA and multi-challenge CCA / IND-CCA2)

This module defines both the single-challenge (**1CCA**, Definition 12.2) and two-phase
batch-challenge multi-challenge (**CCA**, Attack Game 12.1 and Definition 12.1 specialized to a
single batch of challenge queries between Phase 1 and Phase 2 decryption queries) adaptive
chosen-ciphertext security experiments for public-key encryption over an arbitrary message type
`Msg` and decryption output type `Out`, together with their hybrid equivalence
([Boneh and Shoup, Section 12.1, Attack Game 12.1, Definitions 12.1–12.2, and Theorem 12.1,
printed pp. 467–469][BonehShoup2023]).

## Source Statements ([BonehShoup2023], Section 12.1, printed pp. 467–469)

Verbatim from [BonehShoup2023], Section 12.1 (printed pp. 467–468):

> **Attack Game 12.1 (CCA security).** For a given public-key encryption scheme
> $\mathcal{E} = (G, E, D)$, defined over $(\mathcal{M}, \mathcal{C})$, and for a given adversary
> $\mathcal{A}$, we define two experiments.
> **Experiment $b$** ($b = 0, 1$):
> - The challenger computes $(pk, sk) \xleftarrow{R} G()$ and sends $pk$ to the adversary.
> - $\mathcal{A}$ then makes a series of queries to the challenger. Each query can be one of two
>   types:
>   - **Encryption query:** for $i = 1, 2, \ldots$, the $i$th encryption query consists of a pair
>     of messages $(m_{i0}, m_{i1}) \in \mathcal{M}^2$, of the same length. The challenger computes
>     $c_i \xleftarrow{R} E(pk, m_{ib})$ and sends $c_i$ to $\mathcal{A}$.
>   - **Decryption query:** for $j = 1, 2, \ldots$, the $j$th decryption query consists of a
>     ciphertext $\hat{c}_j \in \mathcal{C}$ that is not among the responses to the previous
>     encryption queries, i.e.,
>     $$\hat{c}_j \notin \{c_1, c_2, \ldots\}.$$
>     The challenger computes $\hat{m}_j \leftarrow D(sk, \hat{c}_j)$, and sends $\hat{m}_j$ to
>     $\mathcal{A}$.
> - At the end of the game, the adversary outputs a bit $\hat{b} \in \{0, 1\}$.
>
> Let $W_b$ be the event that $\mathcal{A}$ outputs $1$ in Experiment $b$ and define
> $\mathcal{A}$'s advantage with respect to $\mathcal{E}$ as
> $$\text{CCAadv}[\mathcal{A}, \mathcal{E}] := |\Pr[W_0] - \Pr[W_1]|.$$
>
> **Definition 12.1 (CCA Security).** A public-key encryption scheme $\mathcal{E}$ is called
> **semantically secure against a chosen ciphertext attack**, or simply **CCA secure**, if for all
> efficient adversaries $\mathcal{A}$, the value $\text{CCAadv}[\mathcal{A}, \mathcal{E}]$ is
> negligible.
>
> Just as we did in the symmetric-key setting, we can consider a restricted attack game in which
> the adversary makes only a single encryption query:
>
> **Definition 12.2 (1CCA security).** In Attack Game 12.1, if the adversary $\mathcal{A}$ is
> restricted to making a single encryption query, we denote its advantage by
> $\text{1CCAadv}[\mathcal{A}, \mathcal{E}]$. A public-key encryption scheme $\mathcal{E}$ is
> **one-time semantically secure against chosen ciphertext attack**, or simply, **1CCA secure**, if
> for all efficient adversaries $\mathcal{A}$, the value $\text{1CCAadv}[\mathcal{A}, \mathcal{E}]$
> is negligible.
>
> […]
>
> A similar result holds with respect to chosen ciphertext security, namely, that 1CCA security
> implies CCA security.
>
> **Theorem 12.1.** If a public-key encryption scheme $\mathcal{E}$ is 1CCA secure, then it is
> also CCA secure.
>
> In particular, for every CCA adversary $\mathcal{A}$ that plays Attack Game 12.1 with respect
> to $\mathcal{E}$, and which makes at most $Q_e$ encryption queries to its challenger, there
> exists a 1CCA adversary $\mathcal{B}$ as in Definition 12.2, where $\mathcal{B}$ is an
> elementary wrapper around $\mathcal{A}$, such that
> $$\text{CCAadv}[\mathcal{A}, \mathcal{E}] = Q_e \cdot \text{1CCAadv}[\mathcal{B}, \mathcal{E}].$$

And the two-phase decomposition of the 1CCA experiment (printed pp. 468–469):

> **Initialization phase:** the challenger generates $(pk, sk) \xleftarrow{R} G()$ and sends $pk$
> to the adversary.
> **Phase 1:** the adversary submits a series of decryption queries to the challenger; each such
> query is a ciphertext $\hat{c} \in \mathcal{C}$, to which the challenger responds with
> $\hat{m} \leftarrow D(sk, \hat{c})$.
> **Encryption query:** the adversary submits a single encryption query $(m_0, m_1)$ to the
> challenger; in Experiment $b$ (where $b = 0, 1$), the challenger responds with
> $c \xleftarrow{R} E(pk, m_b)$.
> **Phase 2:** the adversary again submits a series of decryption queries to the challenger; each
> such query is a ciphertext $\hat{c} \in \mathcal{C}$, subject to the restriction that
> $\hat{c} \ne c$, to which the challenger responds with $\hat{m} \leftarrow D(sk, \hat{c})$.
> **Finish:** at the end of the game, the adversary outputs a bit $\hat{b} \in \{0, 1\}$.

## Scope and Specializations

* **Single-challenge 1CCA (`Definition 12.2`) and batch-challenge multi-challenge CCA
  (non-adaptive-challenge restriction of `Attack Game 12.1` / `Definition 12.1`) vs. symmetric
  `SymmetricCipher.INDCCA` (`Definition 9.5`)**:
  `CCA2AdversaryOf Msg`, `cca2GameOn`, and `INDCCA2On` formalize the single-challenge public-key
  1CCA experiment (Definition 12.2, printed p. 468), while `MultiCCA2AdversaryOf Msg`,
  `cca2MultiGameOn`, and `INDCCA2MultiOn` formalize the **two-phase batch-challenge
  (non-adaptive-challenge) restriction** of the multi-challenge public-key CCA experiment
  (Attack Game 12.1 and Definition 12.1, printed pp. 467–468), in which all encryption queries are
  submitted in one block `challenges : List (Msg × Msg)` between Phase 1 and Phase 2 decryption
  queries (rather than adaptively interleaving individual encryption and decryption queries).
  Because anyone can encrypt under the public key `pk`, public-key 1CCA is equivalent to this
  batch-challenge multi-challenge CCA notion by a hybrid argument ([BonehShoup2023], Definition 12.2
  and the batch-challenge specialization of Theorem 12.1, printed p. 468), formalized here via
  `CCA2AdversaryOf.toMulti` (the Definition 12.2 inclusion of 1CCA adversaries as 1-challenge CCA
  adversaries) and `cca2MultiToSingle` (the Theorem 12.1 hybrid reduction with dyadic index
  sampling `sampleDyadicIndex`, scaling the advantage by `dyadicSize (Q n)` and preserving both
  Phase 1 and Phase 2 decryption query counts).
* **Phase 2 challenge-rejection convention**: in Phase 2, querying the challenge ciphertext
  (`request.2 == ct` in `cca2Phase2Oracle`, or `decide (request.2 ∈ cts)` in
  `cca2MultiPhase2Oracle`) returns `[] = encOption encOut none` (the encoding of decryption
  rejection `none`) rather than syntactically restricting the oracle domain to `ĉ ≠ c` (or
  `ĉ ∉ cts`). Because the adversary is given `ct` (or `cts`) as input to `guess` and could simulate
  the constant `[]` reply itself, this convention is equivalent to forbidding challenge queries and
  matches `SymmetricCipher.ccaOracle` in
  `CslibFrontier/Crypto/Computational/Encryption/Authenticated.lean`.
* **No associated data ($\mathcal{D} = \mathrm{Unit}$)**: encryption and decryption queries carry no
  separate associated-data argument (corresponding to $\mathcal{D} = \mathrm{Unit}$ in schemes with
  associated data such as Exercise 12.27).
* **Generic message and output types with challenge-pair admissibility**:
  `CCA2AdversaryOf (Msg : Type)` and `MultiCCA2AdversaryOf (Msg : Type)` are generic in the
  challenge message type `Msg` (`CCA2Adversary` and `MultiCCA2Adversary` specialize to `Bool`, and
  `WordCCA2Adversary` and `WordMultiCCA2Adversary` to `List Bool`). `cca2GameOn`, `INDCCA2On`,
  `cca2MultiGameOn`, and `INDCCA2MultiOn` parameterize the experiment by a challenge-pair
  admissibility predicate `valid : ℕ → List Bool → Msg → Msg → Bool` (returning `false` in both
  experiments when any chosen pair fails `valid`), while `cca2Game`, `INDCCA2Of`, `cca2MultiGame`,
  and `INDCCA2MultiOf` specialize to `fun _ _ _ _ => true` for fixed-length message spaces (such as
  `Bool`) and `WordINDCCA2` / `WordINDCCA2Multi` specialize to Attack Game 12.1's equal-length rule
  `fun _ _ m₀ m₁ => m₀.length == m₁.length`.

## Main definitions

* `Cslib.Crypto.Encryption.CCA2AdversaryOf`, `Cslib.Crypto.Encryption.CCA2Adversary`,
  `Cslib.Crypto.Encryption.WordCCA2Adversary`: two-stage 1CCA adversaries with
  `WordOracleComp Unit` decryption-oracle access in Phase 1 (`choose`) and Phase 2 (`guess`).
* `Cslib.Crypto.Encryption.CCA2AdversaryOf.IsPPT`,
  `Cslib.Crypto.Encryption.CCA2AdversaryOf.IsQueryBounded`: uniform strict oracle PPT admissibility
  and per-stage decryption-query bounds.
* `Cslib.Crypto.Encryption.cca2Phase1Oracle`, `Cslib.Crypto.Encryption.cca2Phase2Oracle`,
  `Cslib.Crypto.Encryption.cca2GameOn`, `Cslib.Crypto.Encryption.cca2Game`: Phase 1 and Phase 2
  decryption oracles and the 1CCA experiment (with and without an explicit challenge-pair
  admissibility guard).
* `Cslib.Crypto.Encryption.INDCCA2On`, `Cslib.Crypto.Encryption.INDCCA2Of`,
  `Cslib.Crypto.Encryption.INDCCA2`, `Cslib.Crypto.Encryption.WordINDCCA2`: single-challenge 1CCA
  security (Definition 12.2).
* `Cslib.Crypto.Encryption.CCA2AdversaryOf.restrict`: embedding of an adversary for the
  admissibility-restricted `cca2GameOn valid` inside the unrestricted `cca2Game`.
* `Cslib.Crypto.Encryption.CCA2AdversaryOf.ofCPA`,
  `Cslib.Crypto.Encryption.CCA2Adversary.ofCPA`: embedding of a chosen-plaintext `AdversaryOf Msg`
  as a 0-query `CCA2AdversaryOf Msg`.
* `Cslib.Crypto.Encryption.MultiCCA2AdversaryOf`, `Cslib.Crypto.Encryption.MultiCCA2Adversary`,
  `Cslib.Crypto.Encryption.WordMultiCCA2Adversary`,
  `Cslib.Crypto.Encryption.MultiCCA2AdversaryOf.IsPPT`,
  `Cslib.Crypto.Encryption.MultiCCA2AdversaryOf.IsQueryBounded`: two-phase batch-challenge
  multi-challenge CCA adversaries, strict oracle PPT admissibility, and per-stage decryption-query
  bounds.
* `Cslib.Crypto.Encryption.cca2MultiPhase2Oracle`, `Cslib.Crypto.Encryption.cca2MultiGameOn`,
  `Cslib.Crypto.Encryption.cca2MultiGame`, `Cslib.Crypto.Encryption.INDCCA2MultiOn`,
  `Cslib.Crypto.Encryption.INDCCA2MultiOf`, `Cslib.Crypto.Encryption.INDCCA2Multi`,
  `Cslib.Crypto.Encryption.WordINDCCA2Multi`: Phase 2 multi-challenge decryption oracle,
  batch-challenge multi-challenge CCA experiments, and security predicates (batch-challenge
  restriction of Attack Game 12.1 / Definition 12.1).
* `Cslib.Crypto.Encryption.CCA2AdversaryOf.toMulti`,
  `Cslib.Crypto.Encryption.cca2MultiHybridGameOn`, `Cslib.Crypto.Encryption.cca2MultiToSingleAt`,
  `Cslib.Crypto.Encryption.cca2MultiToSingle`: single-to-multi embedding (Definition 12.2) and
  multi-to-single hybrid reductions (batch-challenge specialization of Theorem 12.1).

## Main results

* `Cslib.Crypto.Encryption.CCA2AdversaryOf.IsPPT.query_bounds`,
  `Cslib.Crypto.Encryption.MultiCCA2AdversaryOf.IsPPT.query_bounds`: polynomial query,
  challenge-list, and saved-state length bounds for strict oracle PPT 1CCA and batch-challenge
  multi-challenge CCA adversaries.
* `Cslib.Crypto.Encryption.isPPTOn_run_cca2Phase1Oracle`,
  `Cslib.Crypto.Encryption.isPPTOn_run_cca2Phase2Oracle`,
  `Cslib.Crypto.Encryption.isPPTOn_cca2GameOn`,
  `Cslib.Crypto.Encryption.isPPTOn_cca2Game`,
  `Cslib.Crypto.Encryption.isPPTOn_run_cca2MultiPhase1Oracle`,
  `Cslib.Crypto.Encryption.isPPTOn_run_cca2MultiPhase2Oracle`,
  `Cslib.Crypto.Encryption.isPPTOn_cca2MultiGameOn`,
  `Cslib.Crypto.Encryption.isPPTOn_cca2MultiGame`: closed strict PPT compilation of Phase 1,
  Phase 2, and the complete 1CCA and batch-challenge multi-challenge CCA experiments via
  `IsOraclePPTOn.run_interpret_preprocess`.
* `Cslib.Crypto.Encryption.eval_cca2Game_restrict`,
  `Cslib.Crypto.Encryption.CCA2AdversaryOf.IsPPT.restrict`,
  `Cslib.Crypto.Encryption.INDCCA2Of.indcca2On`,
  `Cslib.Crypto.Encryption.INDCCA2Of.wordINDCCA2`,
  `Cslib.Crypto.Encryption.eval_cca2MultiGame_restrict`,
  `Cslib.Crypto.Encryption.MultiCCA2AdversaryOf.IsPPT.restrict`,
  `Cslib.Crypto.Encryption.INDCCA2MultiOf.indcca2MultiOn`,
  `Cslib.Crypto.Encryption.INDCCA2MultiOf.wordINDCCA2Multi`: unrestricted 1CCA / batch-challenge
  multi-challenge CCA security implies admissibility-restricted 1CCA / batch-challenge
  multi-challenge CCA security.
* `Cslib.Crypto.Encryption.CCA2AdversaryOf.isPPT_ofCPA`,
  `Cslib.Crypto.Encryption.CCA2AdversaryOf.isQueryBounded_ofCPA`,
  `Cslib.Crypto.Encryption.eval_cca2GameOn_ofCPA`,
  `Cslib.Crypto.Encryption.eval_cca2Game_ofCPA`,
  `Cslib.Crypto.Encryption.INDCCA2On.indcpaOn`,
  `Cslib.Crypto.Encryption.INDCCA2Of.indcpaOf`,
  `Cslib.Crypto.Encryption.INDCCA2Of.indcpa`,
  `Cslib.Crypto.Encryption.INDCCA2.indcpa`,
  `Cslib.Crypto.Encryption.WordINDCCA2.wordINDCPA`: 1CCA security implies IND-CPA security under
  any challenge-pair admissibility predicate.
* `Cslib.Crypto.Encryption.CCA2AdversaryOf.isPPT_toMulti`,
  `Cslib.Crypto.Encryption.CCA2AdversaryOf.isQueryBounded_toMulti`,
  `Cslib.Crypto.Encryption.eval_cca2MultiGameOn_toMulti`,
  `Cslib.Crypto.Encryption.INDCCA2MultiOn.indcca2On`,
  `Cslib.Crypto.Encryption.INDCCA2MultiOf.indcca2Of`,
  `Cslib.Crypto.Encryption.INDCCA2Multi.indcca2`,
  `Cslib.Crypto.Encryption.WordINDCCA2Multi.wordINDCCA2`: batch-challenge multi-challenge CCA
  implies single-challenge 1CCA ([BonehShoup2023], Definition 12.2, since a 1CCA adversary is a CCA
  adversary making a single encryption query).
* `Cslib.Crypto.Encryption.isPPT_cca2MultiToSingleAt`,
  `Cslib.Crypto.Encryption.isPPT_cca2MultiToSingle`,
  `Cslib.Crypto.Encryption.isQueryBounded_cca2MultiToSingleAt`,
  `Cslib.Crypto.Encryption.isQueryBounded_cca2MultiToSingle`,
  `Cslib.Crypto.Encryption.cca2MultiHybridGameOn_step_gap`,
  `Cslib.Crypto.Encryption.cca2MultiGameOn_gap`,
  `Cslib.Crypto.Encryption.advantage_cca2MultiGameOn`: the batch-challenge hybrid reduction is
  strict oracle PPT and preserves the decryption-query bounds, and the batch-challenge advantage
  is `dyadicSize (Q n)` times its 1CCA advantage.

## Steps toward Theorem 12.1

[BonehShoup2023], Theorem 12.1 (printed p. 468) concerns Attack Game 12.1 (p. 467), in which
encryption and decryption queries are adaptively interleaved. It is
`Cslib.Crypto.Encryption.INDCCA2On.indcca2InterleavedOn` and
`Cslib.Crypto.Encryption.indcca2InterleavedOn_iff_indcca2On` in
`CslibFrontier/Crypto/Computational/Encryption/CCA/Interleaved.lean`. The theorems below are its
restriction to adversaries that submit all challenge pairs in one batch between the two phases of
decryption queries; `Interleaved.lean` uses them to relate the two notions
(`indcca2InterleavedOn_iff_indcca2MultiOn`).

* `Cslib.Crypto.Encryption.INDCCA2On.indcca2MultiOn`,
  `Cslib.Crypto.Encryption.indcca2MultiOn_iff_indcca2On`,
  `Cslib.Crypto.Encryption.INDCCA2Of.indcca2MultiOf`,
  `Cslib.Crypto.Encryption.indcca2MultiOf_iff_indcca2Of`,
  `Cslib.Crypto.Encryption.INDCCA2.indcca2Multi`,
  `Cslib.Crypto.Encryption.indcca2Multi_iff_indcca2`,
  `Cslib.Crypto.Encryption.WordINDCCA2.wordINDCCA2Multi`,
  `Cslib.Crypto.Encryption.wordINDCCA2Multi_iff_wordINDCCA2`: single-challenge 1CCA implies
  batch-challenge multi-challenge CCA, and the two are equivalent.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 12.1 (Attack Game 12.1, Definitions 12.1–12.2, Theorem 12.1,
  printed pp. 467–469).
-/

@[expose] public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM

attribute [local fun_prop]
  ComputableInPolyTime.cons'
  ComputableInPolyTime.listAppend'
  ComputableInPolyTime.unary_lt'
  ComputableInPolyTime.bool_and'

private theorem mul_pow_le_of_le {a k b c d : ℕ} (h : a ≤ k * b) :
    c * a ^ d ≤ c * k ^ d * b ^ d := by
  rw [Nat.mul_assoc, ← Nat.mul_pow]
  exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left h d)

@[local fun_prop]
private theorem decrypt_fp {Out γ : Type} {encOut : Out ↪ List Bool} {enc : γ ↪ List Bool}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (hd : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) (encOption encOut))
    {n : γ → ℕ} {sk ct : γ → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hsk : ComputableInPolyTime sk enc encBits)
    (hct : ComputableInPolyTime ct enc encBits) :
    ComputableInPolyTime (fun a => encOption encOut (decrypt (n a) (sk a) (ct a))) enc encBits :=
  (hd.comp (hn.prod (hsk.prod hct))).encoding_comp

/-- A single-challenge adaptive chosen-ciphertext (1CCA, [BonehShoup2023], Section 12.1,
Attack Game 12.1 and Definition 12.2, printed pp. 467–469) adversary over message space `Msg`.
Both stages have access to the single-channel decryption oracle (`Operation = Unit`). -/
structure CCA2AdversaryOf (Msg : Type) where
  /-- Phase 1: given the unary security parameter `n` and encoded public key `pk`, make decryption
  queries, choose two challenge messages `(m₀, m₁) : Msg × Msg`, and save a state word. -/
  choose : ℕ → List Bool → WordOracleComp Unit ((Msg × Msg) × List Bool)
  /-- Phase 2: given `n`, the saved state word, and the challenge ciphertext `ct`, make decryption
  queries (where querying `ct` is rejected) and output a guess bit. -/
  guess : ℕ → List Bool → List Bool → WordOracleComp Unit Bool

/-- Uniform strict oracle PPT admissibility of both stages of a `CCA2AdversaryOf Msg` with respect
to message encoding `encMsg`. -/
structure CCA2AdversaryOf.IsPPT {Msg : Type} (encMsg : Msg ↪ List Bool)
    (adversary : CCA2AdversaryOf Msg) : Prop where
  /-- Phase 1 message selection is uniform strict oracle PPT on `(n, pk)`. -/
  choose : IsOraclePPT (Operation := Unit) (encChoiceOut encMsg) adversary.choose
  /-- Phase 2 guessing is uniform strict oracle PPT on `(n, state, ct)`. -/
  guess : IsOraclePPTOn (Operation := Unit) encGuessInput encBool
    (fun ⟨n, state, ct⟩ => adversary.guess n state ct)

/-- Per-stage decryption-query bound `(Q₁ n, Q₂ n)` for a `CCA2AdversaryOf Msg`. -/
def CCA2AdversaryOf.IsQueryBounded {Msg : Type} (adversary : CCA2AdversaryOf Msg)
    (Q₁ Q₂ : ℕ → ℕ) : Prop :=
  (∀ n pk, (adversary.choose n pk).IsQueryBounded (Q₁ n)) ∧
  (∀ n state ct, (adversary.guess n state ct).IsQueryBounded (Q₂ n))

/-- Every strict oracle PPT `CCA2AdversaryOf Msg` has polynomial bounds on its Phase 1 queries and
saved-state length in terms of `(n, pk.length)`, and on its Phase 2 queries in terms of
`(n, state.length, ct.length)` for every input state word `state`. -/
theorem CCA2AdversaryOf.IsPPT.query_bounds {Msg : Type} {encMsg : Msg ↪ List Bool}
    {adversary : CCA2AdversaryOf Msg} (hA : adversary.IsPPT encMsg) :
    ∃ c₁ d₁ c₂ d₂ cs ds : ℕ,
      (∀ n pk, (adversary.choose n pk).IsQueryBounded (c₁ * (n + pk.length + 2) ^ d₁)) ∧
      (∀ n state ct,
        (adversary.guess n state ct).IsQueryBounded
          (c₂ * (n + state.length + ct.length + 2) ^ d₂)) ∧
      (∀ n pk (State : Type)
        (oracle : Unit × List Bool → StateT State PMF (List Bool)) s s' choice,
        (choice, s') ∈ ((OracleComp.interpret
          (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m)) oracle)
            (adversary.choose n pk)).run s).support →
        choice.2.length ≤ cs * (n + pk.length + 2) ^ ds) := by
  obtain ⟨c₁, d₁, hchoose⟩ := hA.choose.query_bounds
  obtain ⟨c₂, d₂, hguess⟩ := hA.guess.query_bounds
  obtain ⟨cs, ds, hlen⟩ := hA.choose.on.length_le
  refine ⟨c₁, d₁, c₂ * 4 ^ d₂, d₂, cs * 2 ^ ds, ds, fun n pk => (hchoose n pk).1,
    fun n state ct => (hguess (n, state, ct)).1.mono (mul_pow_le_of_le (by enc_len)),
    fun n pk State oracle s s' choice hmem => ?_⟩
  rw [← ProbOracleComp.runWith_eq_run_interpret] at hmem
  have hstate : choice.2.length ≤ (encPair (encPair encMsg encMsg) encBits choice).length := by
    enc_len
  exact (hstate.trans (hlen (n, pk) State oracle s s' choice hmem)).trans
    (mul_pow_le_of_le (by enc_len))

/-- Single-bit 1CCA adversary (`Msg = Bool`). -/
abbrev CCA2Adversary : Type := CCA2AdversaryOf Bool

/-- Native uniform strict oracle PPT admissibility for a bit 1CCA adversary. -/
abbrev CCA2Adversary.IsPPT (adversary : CCA2Adversary) : Prop :=
  CCA2AdversaryOf.IsPPT encBool adversary

/-- Bit-string 1CCA adversary (`Msg = List Bool`). -/
abbrev WordCCA2Adversary : Type := CCA2AdversaryOf (List Bool)

/-- Native uniform strict oracle PPT admissibility for a bit-string 1CCA adversary. -/
abbrev WordCCA2Adversary.IsPPT (adversary : WordCCA2Adversary) : Prop :=
  CCA2AdversaryOf.IsPPT encBits adversary

/-- Phase 1 decryption oracle ([BonehShoup2023], Section 12.1, Attack Game 12.1 and Definition 12.2,
printed pp. 467–468): answer every decryption query `request.2` with
`encOption encOut (decrypt n sk request.2)`. -/
def cca2Phase1Oracle {Out : Type} (encOut : Out ↪ List Bool)
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (n : ℕ) (sk : List Bool) (request : Unit × List Bool) :
    StateT Unit ProbComp (List Bool) :=
  fun s => pure (encOption encOut (decrypt n sk request.2), s)

/-- Phase 2 decryption oracle ([BonehShoup2023], Section 12.1, Attack Game 12.1 and Definition 12.2,
printed pp. 467–468): reject the challenge ciphertext (`request.2 == ct`) with `[]`
(`encOption encOut none`), and answer all other queries `request.2 ≠ ct` with
`encOption encOut (decrypt n sk request.2)`. Since the adversary receives `ct` as input to `guess`
and can simulate the constant `[]` reply on `ct` itself, returning `[]` on `ct` is equivalent to
forbidding the query `ĉ = c` (matching `SymmetricCipher.ccaOracle` in
`CslibFrontier/Crypto/Computational/Encryption/Authenticated.lean`). -/
def cca2Phase2Oracle {Out : Type} (encOut : Out ↪ List Bool)
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (n : ℕ) (sk ct : List Bool) (request : Unit × List Bool) :
    StateT Unit ProbComp (List Bool) :=
  fun s =>
    if request.2 == ct then
      pure ([], s)
    else
      pure (encOption encOut (decrypt n sk request.2), s)

/-- Single-challenge 1CCA experiment ([BonehShoup2023], Section 12.1, Attack Game 12.1 and
Definition 12.2, printed pp. 467–468) with challenge-pair admissibility predicate
`valid : ℕ → List Bool → Msg → Msg → Bool`: sample `(pk, sk) ← keyGen n`, run Phase 1 (`choose`)
against `cca2Phase1Oracle`, check `valid n pk m₀ m₁` (returning `false` in both experiments when
invalid), encrypt `if bit then m₁ else m₀` to obtain `ct`, and run Phase 2 (`guess`) against
`cca2Phase2Oracle` rejecting `ct`. -/
noncomputable def cca2GameOn {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : CCA2AdversaryOf Msg) (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let keys ← keyGen n
  let choiceOut ← (OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (cca2Phase1Oracle encOut decrypt n keys.2))
    (adversary.choose n keys.1)).run ()
  let choice := choiceOut.1
  if valid n keys.1 (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice) then
    let ct ← encrypt n keys.1 (if bit then ChoiceOut.msg₁ choice else ChoiceOut.msg₀ choice)
    let guessOut ← (OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2Phase2Oracle encOut decrypt n keys.2 ct))
      (adversary.guess n (ChoiceOut.state choice) ct)).run ()
    return guessOut.1
  else
    return false

/-- Unconditional single-challenge 1CCA experiment (`valid := fun _ _ _ _ => true`), for
fixed-length message spaces `Msg` where every pair `(m₀, m₁) : Msg × Msg` is admissible. -/
noncomputable abbrev cca2Game {Msg Out : Type} (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : CCA2AdversaryOf Msg) (bit : Bool) (n : ℕ) : ProbComp Bool :=
  cca2GameOn (fun _ _ _ _ => true) encOut keyGen encrypt decrypt adversary bit n

/-- Single-challenge 1CCA security ([BonehShoup2023], Section 12.1, Definition 12.2, printed p. 468)
with respect to challenge-pair admissibility predicate `valid`, message encoding `encMsg`, and
decryption output encoding `encOut`. -/
def INDCCA2On {Msg Out : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encMsg : Msg ↪ List Bool) (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out) : Prop :=
  Game.Indistinguishable
    (fun adversary n =>
      ProbComp.eval (cca2GameOn valid encOut keyGen encrypt decrypt adversary false n))
    (fun adversary n =>
      ProbComp.eval (cca2GameOn valid encOut keyGen encrypt decrypt adversary true n))
    (CCA2AdversaryOf.IsPPT encMsg)

/-- Single-challenge 1CCA security ([BonehShoup2023], Section 12.1, Definition 12.2, printed p. 468)
over a fixed-length message space `Msg` (`valid := fun _ _ _ _ => true`). -/
abbrev INDCCA2Of {Msg Out : Type} (encMsg : Msg ↪ List Bool) (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out) : Prop :=
  INDCCA2On (fun _ _ _ _ => true) encMsg encOut keyGen encrypt decrypt

/-- Single-challenge 1CCA security for bit encryption (`Msg = Bool`, `Out = Bool`):
[BonehShoup2023], Definition 12.2 (p. 468), that is, Attack Game 12.1 (pp. 467–468) with one
encryption query, for the message space of single bits. A Phase 2 decryption query on the
challenge ciphertext is answered with rejection, where the source forbids it. -/
abbrev INDCCA2 (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Bool) : Prop :=
  INDCCA2Of encBool encBool keyGen encrypt decrypt

/-- Single-challenge 1CCA security for bit-string encryption (`Msg = List Bool`, `Out = List Bool`)
under Attack Game 12.1's equal-length challenge rule `m₀.length == m₁.length`: [BonehShoup2023],
Definition 12.2 (p. 468), with every bit string a message. A Phase 2 decryption query on the
challenge ciphertext is answered with rejection, where the source forbids it. -/
abbrev WordINDCCA2 (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option (List Bool)) : Prop :=
  INDCCA2On (fun _ _ m₀ m₁ => m₀.length == m₁.length) encBits encBits keyGen encrypt decrypt

private theorem isPPTOn_run_cca2Phase1Oracle_of_choose {Choice Out : Type}
    {encChoice : Choice ↪ List Bool} {encOut : Out ↪ List Bool}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    {choose : ℕ → List Bool → WordOracleComp Unit Choice}
    (hdec : ComputableInPolyTime
      (fun ⟨n, sk, ct⟩ => decrypt n sk ct)
      (encKeyedInput encBits) (encOption encOut))
    (hchoose : IsOraclePPT encChoice choose) :
    IsPPTOn encKeyPairInput (encPair encChoice (encFinEnum Unit))
      (fun ⟨n, pk, sk⟩ =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
            (cca2Phase1Oracle encOut decrypt n sk))
          (choose n pk)).run ()) :=
  hchoose.run_interpret_preprocess (operationEncoding := encFinEnum Unit)
    (prepare := fun caller : ℕ × List Bool × List Bool => (caller.1, caller.2.1))
    (initial := fun _ => ())
    (resources := fun caller req => (encOption encOut (decrypt caller.1 caller.2.2 req)).length)
    (by fun_prop) (by dsimp only [cca2Phase1Oracle]; fun_prop) (by fun_prop)
    (fun _ _ => True) (fun _ => trivial) (by fun_prop)
    (fun _ _ _ _ _ hresult => by
      dsimp only [cca2Phase1Oracle] at hresult
      supp_cases hresult
      exact ⟨trivial, le_rfl, Nat.le_add_right _ _⟩)

/-- Running Phase 1 (`adversary.choose`) against `cca2Phase1Oracle` is uniformly strict PPT in
`(n, pk, sk)` whenever `decrypt` is computable in polynomial time. -/
@[program_certificate]
theorem isPPTOn_run_cca2Phase1Oracle {Msg Out : Type} {encMsg : Msg ↪ List Bool}
    {encOut : Out ↪ List Bool} {decrypt : ℕ → List Bool → List Bool → Option Out}
    {adversary : CCA2AdversaryOf Msg}
    (hdec : ComputableInPolyTime
      (fun ⟨n, sk, ct⟩ => decrypt n sk ct)
      (encKeyedInput encBits) (encOption encOut))
    (hA : adversary.IsPPT encMsg) :
    IsPPTOn encKeyPairInput (encPair (encChoiceOut encMsg) (encFinEnum Unit))
      (fun ⟨n, pk, sk⟩ =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
            (cca2Phase1Oracle encOut decrypt n sk))
          (adversary.choose n pk)).run ()) :=
  isPPTOn_run_cca2Phase1Oracle_of_choose hdec hA.choose

/-- The shared Phase 2 certificate permits any encoded challenge container and polynomial-time
blocking test. Rejected queries return the same empty word, and accepted queries use the same
encoded decryption-reply length budget as the concrete single- and multi-challenge games. -/
private theorem isPPTOn_run_cca2Phase2Oracle_of_guess {Challenge Out : Type}
    {encChallenge : Challenge ↪ List Bool} {encOut : Out ↪ List Bool}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    {guess : ℕ → List Bool → Challenge → WordOracleComp Unit Bool}
    {blocked : List Bool → Challenge → Bool}
    (hdec : ComputableInPolyTime
      (fun ⟨n, sk, ct⟩ => decrypt n sk ct)
      (encKeyedInput encBits) (encOption encOut))
    (hguess : IsOraclePPTOn (Operation := Unit)
      (encPair encUnary (encPair encBits encChallenge)) encBool
      (fun ⟨n, state, challenge⟩ => guess n state challenge))
    (hblocked : ComputableInPolyTime
      (fun pair : List Bool × Challenge => blocked pair.1 pair.2)
      (encPair encBits encChallenge) encBool) :
    IsPPTOn (encPair encUnary (encPair encBits (encPair encBits encChallenge)))
      (encPair encBool (encFinEnum Unit))
      (fun ⟨n, sk, state, challenge⟩ =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
            (fun request s => if blocked request.2 challenge then pure ([], s)
              else pure (encOption encOut (decrypt n sk request.2), s)))
          (guess n state challenge)).run ()) := by
  let EIn := encHandlerCall (encPair encUnary (encPair encBits (encPair encBits encChallenge)))
    (encFinEnum Unit) (encFinEnum Unit)
  have : ComputableInPolyTime (fun p => blocked p.2.1.2 p.1.2.2.2) EIn encBool :=
    hblocked.comp (show ComputableInPolyTime (fun p => (p.2.1.2, p.1.2.2.2)) EIn _ by fun_prop)
  exact hguess.run_interpret_preprocess (operationEncoding := encFinEnum Unit)
    (prepare := fun caller : ℕ × List Bool × List Bool × Challenge =>
      (caller.1, caller.2.2.1, caller.2.2.2))
    (initial := fun _ => ())
    (resources := fun caller req => (encOption encOut (decrypt caller.1 caller.2.1 req)).length)
    (by fun_prop) (by fun_prop) (by fun_prop) (fun _ _ => True) (fun _ => trivial) (by fun_prop)
    (fun _ _ _ _ _ hresult => by
      split_ifs at hresult <;> supp_cases hresult <;>
        exact ⟨trivial, by simp, Nat.le_add_right _ _⟩)

/-- Running Phase 2 (`adversary.guess`) against `cca2Phase2Oracle` is uniformly strict PPT in
`(n, sk, state, ct)` whenever `decrypt` is computable in polynomial time. -/
@[program_certificate]
theorem isPPTOn_run_cca2Phase2Oracle {Msg Out : Type} {encMsg : Msg ↪ List Bool}
    {encOut : Out ↪ List Bool} {decrypt : ℕ → List Bool → List Bool → Option Out}
    {adversary : CCA2AdversaryOf Msg}
    (hdec : ComputableInPolyTime
      (fun ⟨n, sk, ct⟩ => decrypt n sk ct)
      (encKeyedInput encBits) (encOption encOut))
    (hA : adversary.IsPPT encMsg) :
    IsPPTOn (encPair encUnary (encPair encBits (encPair encBits encBits)))
      (encPair encBool (encFinEnum Unit))
      (fun ⟨n, sk, state, ct⟩ =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
            (cca2Phase2Oracle encOut decrypt n sk ct))
          (adversary.guess n state ct)).run ()) := by
  exact isPPTOn_run_cca2Phase2Oracle_of_guess
    (blocked := fun req ct => req == ct) hdec hA.guess (by fun_prop)

/-- The complete `cca2GameOn` experiment is uniformly strict PPT on the unary security parameter
whenever `valid`, `keyGen`, `encrypt`, `decrypt`, and `adversary` are admissible. -/
@[program_certificate]
theorem isPPTOn_cca2GameOn {Msg Out : Type} {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    {adversary : CCA2AdversaryOf Msg}
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, pk, msg⟩ => encrypt n pk msg))
    (hdecrypt : ComputableInPolyTime
      (fun ⟨n, sk, ct⟩ => decrypt n sk ct)
      (encKeyedInput encBits) (encOption encOut))
    (hA : adversary.IsPPT encMsg) (bit : Bool) :
    IsPPTOn encUnary encBool (cca2GameOn valid encOut keyGen encrypt decrypt adversary bit) := by
  unfold cca2GameOn
  dsimp only [ChoiceOut.msg₀, ChoiceOut.msg₁, ChoiceOut.state, ChoiceOut.msgs]
  refine hkeyGen.bind_with ((isPPTOn_run_cca2Phase1Oracle hdecrypt hA).bind_with ?_)
  refine IsPPTOn.cond (by fun_prop)
    ((show IsPPTOn _ encBits _ by cases bit <;> fun_prop).bind_with ?_) (by fun_prop)
  have hprep : ComputableInPolyTime (fun p => (p.1.1.1, p.1.1.2.2, p.1.2.1.2, p.2))
      (encPair (encPair encKeyPairInput (encPair (encChoiceOut encMsg) (encFinEnum Unit)))
        encBits) (encPair encUnary (encPair encBits (encPair encBits encBits))) := by fun_prop
  exact ((isPPTOn_run_cca2Phase2Oracle hdecrypt hA).preprocess hprep).bind
    (ComputableInPolyTime.fst _ _).isPPTOn

/-- The complete `cca2Game` experiment is uniformly strict PPT on the unary security parameter
whenever `keyGen`, `encrypt`, `decrypt`, and `adversary` are admissible. -/
@[program_certificate]
theorem isPPTOn_cca2Game {Msg Out : Type} {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    {adversary : CCA2AdversaryOf Msg}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, pk, msg⟩ => encrypt n pk msg))
    (hdecrypt : ComputableInPolyTime
      (fun ⟨n, sk, ct⟩ => decrypt n sk ct)
      (encKeyedInput encBits) (encOption encOut))
    (hA : adversary.IsPPT encMsg) (bit : Bool) :
    IsPPTOn encUnary encBool (cca2Game encOut keyGen encrypt decrypt adversary bit) :=
  isPPTOn_cca2GameOn (ComputableInPolyTime.const true)
    hkeyGen hencrypt hdecrypt hA bit

/-! ### Playing a restricted 1CCA game inside the unrestricted one -/

/-- The adversary that plays `cca2GameOn valid` inside the unrestricted `cca2Game`. Its `choose`
runs `adversary.choose n pk` and puts the bit `valid n pk m₀ m₁` in front of the saved state; its
`guess` returns `false` when that bit is `false` and otherwise runs `adversary.guess` on the rest of
the state. The challenge pair itself is passed on unchanged. -/
def CCA2AdversaryOf.restrict {Msg : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (adversary : CCA2AdversaryOf Msg) : CCA2AdversaryOf Msg where
  choose n pk := do
    let choice ← adversary.choose n pk
    return (choice.1,
      valid n pk (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice) :: ChoiceOut.state choice)
  guess n state ct :=
    if state.headD false then adversary.guess n state.tail ct else pure false

/-- Running the unrestricted `cca2Game` on `adversary.restrict valid` has the same output
distribution as running `cca2GameOn valid` on `adversary`. -/
theorem eval_cca2Game_restrict {Msg Out : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : CCA2AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval (cca2Game encOut keyGen encrypt decrypt (adversary.restrict valid) bit n) =
      ProbComp.eval (cca2GameOn valid encOut keyGen encrypt decrypt adversary bit n) := by
  simp only [cca2Game, cca2GameOn, CCA2AdversaryOf.restrict, ↓reduceIte,
    OracleComp.interpret_bind, OracleComp.interpret_pure, StateT.run_bind, StateT.run_pure,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, apply_ite ProbComp.eval]
  congr 1 with keys : 1
  congr 1 with choiceOut : 1
  cases valid n keys.1 choiceOut.1.1.1 choiceOut.1.1.2 <;>
    simp [OracleComp.interpret_pure, StateT.run_pure, ProbComp.eval_pure, PMF.bind_const]

/-- Restricting a uniform strict oracle PPT 1CCA adversary by a polynomial-time admissibility
predicate keeps it uniform strict oracle PPT: `choose` additionally evaluates `valid` and prepends
one bit to the saved state, and `guess` branches on that bit without querying the oracle when it is
`false`. -/
theorem CCA2AdversaryOf.IsPPT.restrict {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    {adversary : CCA2AdversaryOf Msg} (hadversary : CCA2AdversaryOf.IsPPT encMsg adversary) :
    CCA2AdversaryOf.IsPPT encMsg (adversary.restrict valid) where
  choose := by
    have := hadversary.choose.on
    apply IsOraclePPTOn.isOraclePPT
    dsimp only [CCA2AdversaryOf.restrict, ChoiceOut.msg₀, ChoiceOut.msg₁, ChoiceOut.state]
    fun_prop
  guess := by
    have := hadversary.guess
    dsimp only [CCA2AdversaryOf.restrict]
    fun_prop

/-- Unrestricted 1CCA security implies 1CCA security under every polynomial-time admissibility
predicate. -/
theorem INDCCA2Of.indcca2On {Msg Out : Type} {encMsg : Msg ↪ List Bool}
    {encOut : Out ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (h : INDCCA2Of encMsg encOut keyGen encrypt decrypt)
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool) :
    INDCCA2On valid encMsg encOut keyGen encrypt decrypt := by
  intro adversary hadversary
  simpa only [eval_cca2Game_restrict] using
    h (adversary.restrict valid) (hadversary.restrict hvalid)

private theorem computableInPolyTime_wordValid :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool × List Bool => p.2.2.1.length == p.2.2.2.length)
      (encChallengePairInput encBits) encBool := by fun_prop

/-- Unrestricted bit-word 1CCA security implies `WordINDCCA2`. -/
theorem INDCCA2Of.wordINDCCA2
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option (List Bool)}
    (h : INDCCA2Of encBits encBits keyGen encrypt decrypt) :
    WordINDCCA2 keyGen encrypt decrypt :=
  h.indcca2On computableInPolyTime_wordValid

/-! ### 1CCA implies IND-CPA -/

/-- Lift a chosen-plaintext `AdversaryOf Msg` to a 0-query `CCA2AdversaryOf Msg`. -/
def CCA2AdversaryOf.ofCPA {Msg : Type} (adversary : AdversaryOf Msg) : CCA2AdversaryOf Msg where
  choose n pk := ProbOracleComp.sample (adversary.choose n pk)
  guess n state ct := ProbOracleComp.sample (adversary.guess n state ct)

/-- Lift a chosen-plaintext bit `Adversary` to a 0-query `CCA2Adversary`. -/
abbrev CCA2Adversary.ofCPA (adversary : Adversary) : CCA2Adversary :=
  CCA2AdversaryOf.ofCPA adversary

/-- Lifting a strict PPT `AdversaryOf Msg` yields a strict oracle PPT `CCA2AdversaryOf Msg`. -/
theorem CCA2AdversaryOf.isPPT_ofCPA {Msg : Type} {encMsg : Msg ↪ List Bool}
    {adversary : AdversaryOf Msg} (hA : adversary.IsPPT encMsg) :
    (CCA2AdversaryOf.ofCPA adversary).IsPPT encMsg where
  choose := hA.choose.on.isOraclePPTOn.isOraclePPT
  guess := hA.guess.isOraclePPTOn

/-- Lifting a strict PPT bit `Adversary` yields a strict oracle PPT `CCA2Adversary`. -/
theorem CCA2Adversary.isPPT_ofCPA {adversary : Adversary} (hA : adversary.IsPPT) :
    (CCA2Adversary.ofCPA adversary).IsPPT :=
  CCA2AdversaryOf.isPPT_ofCPA hA

/-- A lifted CPA adversary makes `0` decryption queries in both stages. -/
theorem CCA2AdversaryOf.isQueryBounded_ofCPA {Msg : Type} (adversary : AdversaryOf Msg) :
    (CCA2AdversaryOf.ofCPA adversary).IsQueryBounded (fun _ => 0) (fun _ => 0) :=
  ⟨fun n pk => ProbOracleComp.IsQueryBounded.sample (adversary.choose n pk),
    fun n state ct => ProbOracleComp.IsQueryBounded.sample (adversary.guess n state ct)⟩

/-- A lifted bit CPA adversary makes `0` decryption queries in both stages. -/
theorem CCA2Adversary.isQueryBounded_ofCPA (adversary : Adversary) :
    (CCA2Adversary.ofCPA adversary).IsQueryBounded (fun _ => 0) (fun _ => 0) :=
  CCA2AdversaryOf.isQueryBounded_ofCPA adversary

/-- Running a lifted CPA adversary in `cca2GameOn` has the same output distribution as the CPA
`gameOn` with the same challenge-pair admissibility predicate `valid`. -/
theorem eval_cca2GameOn_ofCPA {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval
      (cca2GameOn valid encOut keyGen encrypt decrypt (CCA2AdversaryOf.ofCPA adversary) bit n) =
      ProbComp.eval (gameOn valid keyGen encrypt adversary bit n) := by
  simp only [cca2GameOn, gameOn, CCA2AdversaryOf.ofCPA, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbOracleComp.eval_run_interpret_eq_runWith, ProbOracleComp.runWith_sample, PMF.bind_map,
    PMF.bind_pure, Function.comp_def, apply_ite ProbComp.eval]

/-- Running a lifted CPA adversary in `cca2Game` has the same output distribution as the CPA
`game`. -/
theorem eval_cca2Game_ofCPA {Msg Out : Type} (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval
      (cca2Game encOut keyGen encrypt decrypt (CCA2AdversaryOf.ofCPA adversary) bit n) =
      ProbComp.eval (game keyGen encrypt adversary bit n) :=
  eval_cca2GameOn_ofCPA (fun _ _ _ _ => true) encOut keyGen encrypt decrypt adversary bit n

/-- **1CCA security implies IND-CPA security** under any challenge-pair admissibility predicate
`valid`: any encryption scheme satisfying `INDCCA2On valid` also satisfies `INDCPAOn valid`. -/
theorem INDCCA2On.indcpaOn {Msg Out : Type} {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (h : INDCCA2On valid encMsg encOut keyGen encrypt decrypt) :
    INDCPAOn valid encMsg keyGen encrypt := by
  intro adversary hA
  simpa only [eval_cca2GameOn_ofCPA] using h (CCA2AdversaryOf.ofCPA adversary)
    (CCA2AdversaryOf.isPPT_ofCPA hA)

/-- **Unrestricted 1CCA security implies unrestricted IND-CPA security**: any encryption scheme
satisfying `INDCCA2Of encMsg encOut` also satisfies `INDCPAOf encMsg`. -/
theorem INDCCA2Of.indcpaOf {Msg Out : Type} {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (h : INDCCA2Of encMsg encOut keyGen encrypt decrypt) :
    INDCPAOf encMsg keyGen encrypt :=
  INDCCA2On.indcpaOn h

/-- **1CCA security implies IND-CPA security**: any bit encryption scheme satisfying `INDCCA2Of`
also satisfies `INDCPA`. -/
theorem INDCCA2Of.indcpa {Out : Type} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (h : INDCCA2Of encBool encOut keyGen encrypt decrypt) :
    INDCPA keyGen encrypt :=
  INDCCA2On.indcpaOn h

/-- Specialization of `INDCCA2Of.indcpa` to `INDCCA2`. -/
theorem INDCCA2.indcpa {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Bool}
    (h : INDCCA2 keyGen encrypt decrypt) :
    INDCPA keyGen encrypt :=
  INDCCA2On.indcpaOn h

/-- **Word 1CCA security implies word IND-CPA security**: any bit-string encryption scheme
satisfying `WordINDCCA2` also satisfies `WordINDCPA`. -/
theorem WordINDCCA2.wordINDCPA {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option (List Bool)}
    (h : WordINDCCA2 keyGen encrypt decrypt) :
    WordINDCPA keyGen encrypt :=
  INDCCA2On.indcpaOn h

/-! ### Batch-challenge multi-challenge CCA security (Definition 12.1) -/

/-- A two-phase batch-challenge multi-challenge adaptive chosen-ciphertext adversary over message
space `Msg`, modeling the non-adaptive-challenge restriction of [BonehShoup2023], Section 12.1,
Attack Game 12.1 and Definition 12.1 (printed pp. 467–468) in which all encryption queries are
submitted in one block between Phase 1 and Phase 2 decryption queries. Both stages have access to
the single-channel decryption oracle (`Operation = Unit`). -/
structure MultiCCA2AdversaryOf (Msg : Type) where
  /-- Phase 1: given the unary security parameter `n` and encoded public key `pk`, make decryption
  queries, choose a list of challenge message pairs `challenges : List (Msg × Msg)`, and save a
  state word. -/
  choose : ℕ → List Bool → WordOracleComp Unit (List (Msg × Msg) × List Bool)
  /-- Phase 2: given `n`, the saved state word, and the list of challenge ciphertexts `cts`, make
  decryption queries (where querying any `ct ∈ cts` is rejected) and output a guess bit. -/
  guess : ℕ → List Bool → List (List Bool) → WordOracleComp Unit Bool

/-- Uniform strict oracle PPT admissibility of both stages of a `MultiCCA2AdversaryOf Msg` with
respect to message encoding `encMsg`. -/
structure MultiCCA2AdversaryOf.IsPPT {Msg : Type} (encMsg : Msg ↪ List Bool)
    (adversary : MultiCCA2AdversaryOf Msg) : Prop where
  /-- Phase 1 challenge-list selection is uniform strict oracle PPT on `(n, pk)`. -/
  choose : IsOraclePPT (Operation := Unit) (encPair (encList (encPair encMsg encMsg)) encBits)
    adversary.choose
  /-- Phase 2 guessing is uniform strict oracle PPT on `(n, state, cts)`. -/
  guess : IsOraclePPTOn (Operation := Unit)
    (encPair encUnary (encPair encBits (encList encBits))) encBool
    (fun p => adversary.guess p.1 p.2.1 p.2.2)

/-- Per-stage decryption-query bound `(Q₁ n, Q₂ n)` for a `MultiCCA2AdversaryOf Msg`. -/
def MultiCCA2AdversaryOf.IsQueryBounded {Msg : Type} (adversary : MultiCCA2AdversaryOf Msg)
    (Q₁ Q₂ : ℕ → ℕ) : Prop :=
  (∀ n pk, (adversary.choose n pk).IsQueryBounded (Q₁ n)) ∧
  (∀ n state cts, (adversary.guess n state cts).IsQueryBounded (Q₂ n))

/-- Every strict oracle PPT `MultiCCA2AdversaryOf Msg` has polynomial bounds on its Phase 1 queries,
challenge-list length, and saved-state length in terms of `(n, pk.length)`, and on its Phase 2
queries in terms of `(n, state.length, (encList encBits cts).length)` for every input state word
`state`. -/
theorem MultiCCA2AdversaryOf.IsPPT.query_bounds {Msg : Type} {encMsg : Msg ↪ List Bool}
    {adversary : MultiCCA2AdversaryOf Msg} (hA : adversary.IsPPT encMsg) :
    ∃ c₁ d₁ c₂ d₂ cs ds : ℕ,
      (∀ n pk, (adversary.choose n pk).IsQueryBounded (c₁ * (n + pk.length + 2) ^ d₁)) ∧
      (∀ n state cts,
        (adversary.guess n state cts).IsQueryBounded
          (c₂ * (n + state.length + (encList encBits cts).length + 2) ^ d₂)) ∧
      (∀ n pk (State : Type)
        (oracle : Unit × List Bool → StateT State PMF (List Bool)) s s' choice,
        (choice, s') ∈ ((OracleComp.interpret
          (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m)) oracle)
            (adversary.choose n pk)).run s).support →
        choice.1.length ≤ cs * (n + pk.length + 2) ^ ds ∧
          choice.2.length ≤ cs * (n + pk.length + 2) ^ ds) := by
  obtain ⟨c₁, d₁, hchoose⟩ := hA.choose.query_bounds
  obtain ⟨c₂, d₂, hguess⟩ := hA.guess.query_bounds
  obtain ⟨cs, ds, hlen⟩ := hA.choose.on.length_le
  refine ⟨c₁, d₁, c₂ * 4 ^ d₂, d₂, cs * 2 ^ ds, ds, fun n pk => (hchoose n pk).1,
    fun n state cts => (hguess (n, state, cts)).1.mono (mul_pow_le_of_le (by enc_len)),
    fun n pk State oracle s s' choice hmem => ?_⟩
  rw [← ProbOracleComp.runWith_eq_run_interpret] at hmem
  have hbound := (hlen (n, pk) State oracle s s' choice hmem).trans
    (mul_pow_le_of_le (k := 2) (b := n + pk.length + 2) (by enc_len))
  have hchallenges :
      choice.1.length ≤ (encPair (encList (encPair encMsg encMsg)) encBits choice).length := by
    have := length_le_length_encList (encPair encMsg encMsg) choice.1
    enc_len
  have hstate :
      choice.2.length ≤ (encPair (encList (encPair encMsg encMsg)) encBits choice).length := by
    enc_len
  exact ⟨hchallenges.trans hbound, hstate.trans hbound⟩

/-- Single-bit multi-challenge CCA adversary (`Msg = Bool`). -/
abbrev MultiCCA2Adversary : Type := MultiCCA2AdversaryOf Bool

/-- Native uniform strict oracle PPT admissibility for a bit multi-challenge CCA adversary. -/
abbrev MultiCCA2Adversary.IsPPT (adversary : MultiCCA2Adversary) : Prop :=
  MultiCCA2AdversaryOf.IsPPT encBool adversary

/-- Bit-string multi-challenge CCA adversary (`Msg = List Bool`). -/
abbrev WordMultiCCA2Adversary : Type := MultiCCA2AdversaryOf (List Bool)

/-- Native uniform strict oracle PPT admissibility for a bit-string multi-challenge CCA
adversary. -/
abbrev WordMultiCCA2Adversary.IsPPT (adversary : WordMultiCCA2Adversary) : Prop :=
  MultiCCA2AdversaryOf.IsPPT encBits adversary

/-- Multi-challenge Phase 2 decryption oracle ([BonehShoup2023], Section 12.1, Attack Game 12.1 and
Definition 12.1, printed pp. 467–468): reject any decryption query matching one of the challenge
ciphertexts (`decide (request.2 ∈ cts)`) with `[]` (`encOption encOut none`), and answer all other
queries `request.2 ∉ cts` with `encOption encOut (decrypt n sk request.2)`. -/
def cca2MultiPhase2Oracle {Out : Type} (encOut : Out ↪ List Bool)
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (n : ℕ) (sk : List Bool) (cts : List (List Bool)) (request : Unit × List Bool) :
    StateT Unit ProbComp (List Bool) :=
  fun s =>
    if decide (request.2 ∈ cts) then
      pure ([], s)
    else
      pure (encOption encOut (decrypt n sk request.2), s)

/-- On a singleton challenge list `[ct]`, `cca2MultiPhase2Oracle` coincides with
`cca2Phase2Oracle`. -/
@[simp] theorem cca2MultiPhase2Oracle_singleton {Out : Type} (encOut : Out ↪ List Bool)
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (n : ℕ) (sk ct : List Bool) :
    cca2MultiPhase2Oracle encOut decrypt n sk [ct] =
      cca2Phase2Oracle encOut decrypt n sk ct := by
  funext request s
  simp [cca2MultiPhase2Oracle, cca2Phase2Oracle]

/-- Two-phase batch-challenge multi-challenge CCA experiment (non-adaptive-challenge restriction of
[BonehShoup2023], Section 12.1, Attack Game 12.1 and Definition 12.1, printed pp. 467–468) with
challenge-pair admissibility predicate `valid : ℕ → List Bool → Msg → Msg → Bool`: sample
`(pk, sk) ← keyGen n`, run Phase 1 (`choose`) against `cca2Phase1Oracle`, check
`choice.1.all (fun p => valid n keys.1 p.1 p.2)` (returning `false` in both experiments when any
chosen pair is invalid), encrypt each pair via
`choice.1.mapM (fun p => encrypt n keys.1 (if bit then p.2 else p.1))` to obtain the challenge
ciphertext list `cts`, and run Phase 2 (`guess`) against `cca2MultiPhase2Oracle` rejecting any
query in `cts`. -/
noncomputable def cca2MultiGameOn {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : MultiCCA2AdversaryOf Msg) (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let keys ← keyGen n
  let choiceOut ← (OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (cca2Phase1Oracle encOut decrypt n keys.2))
    (adversary.choose n keys.1)).run ()
  let choice := choiceOut.1
  if choice.1.all (fun p => valid n keys.1 p.1 p.2) then
    let cts ← choice.1.mapM (fun p => encrypt n keys.1 (if bit then p.2 else p.1))
    let guessOut ← (OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2MultiPhase2Oracle encOut decrypt n keys.2 cts))
      (adversary.guess n choice.2 cts)).run ()
    return guessOut.1
  else
    return false

/-- Unconditional batch-challenge multi-challenge CCA experiment (`valid := fun _ _ _ _ => true`),
for fixed-length message spaces `Msg` where every pair `(m₀, m₁) : Msg × Msg` is admissible. -/
noncomputable abbrev cca2MultiGame {Msg Out : Type} (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : MultiCCA2AdversaryOf Msg) (bit : Bool) (n : ℕ) : ProbComp Bool :=
  cca2MultiGameOn (fun _ _ _ _ => true) encOut keyGen encrypt decrypt adversary bit n

/-- Two-phase batch-challenge multi-challenge CCA security (non-adaptive-challenge restriction of
[BonehShoup2023], Section 12.1, Definition 12.1, printed p. 468, in which all encryption queries
are submitted in one batch between Phase 1 and Phase 2 decryption queries) with respect to
challenge-pair admissibility predicate `valid`, message encoding `encMsg`, and decryption output
encoding `encOut`. -/
def INDCCA2MultiOn {Msg Out : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encMsg : Msg ↪ List Bool) (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out) : Prop :=
  Game.Indistinguishable
    (fun adversary n =>
      ProbComp.eval (cca2MultiGameOn valid encOut keyGen encrypt decrypt adversary false n))
    (fun adversary n =>
      ProbComp.eval (cca2MultiGameOn valid encOut keyGen encrypt decrypt adversary true n))
    (MultiCCA2AdversaryOf.IsPPT encMsg)

/-- Batch-challenge multi-challenge CCA security (non-adaptive-challenge restriction of
[BonehShoup2023], Section 12.1, Definition 12.1, printed p. 468) over a fixed-length message space
`Msg` (`valid := fun _ _ _ _ => true`). -/
abbrev INDCCA2MultiOf {Msg Out : Type} (encMsg : Msg ↪ List Bool) (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out) : Prop :=
  INDCCA2MultiOn (fun _ _ _ _ => true) encMsg encOut keyGen encrypt decrypt

/-- Batch-challenge multi-challenge CCA security for bit encryption (`Msg = Bool`, `Out = Bool`).
It restricts the adversaries of [BonehShoup2023], Attack Game 12.1 and Definition 12.1
(pp. 467–468): all encryption queries come in one batch between the two phases of decryption
queries, instead of being interleaved with them. For efficient algorithms it is equivalent to
`INDCCA2` (`indcca2Multi_iff_indcca2`), as CCA security is to 1CCA security by Theorem 12.1
(p. 468). -/
abbrev INDCCA2Multi (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Bool) : Prop :=
  INDCCA2MultiOf encBool encBool keyGen encrypt decrypt

/-- Batch-challenge multi-challenge CCA security for bit-string encryption (`Msg = List Bool`,
`Out = List Bool`) under Attack Game 12.1's equal-length challenge rule
`m₀.length == m₁.length`. It restricts the adversaries of [BonehShoup2023], Attack Game 12.1 and
Definition 12.1 (pp. 467–468): all encryption queries come in one batch between the two phases of
decryption queries, instead of being interleaved with them. -/
abbrev WordINDCCA2Multi (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option (List Bool)) : Prop :=
  INDCCA2MultiOn (fun _ _ m₀ m₁ => m₀.length == m₁.length) encBits encBits keyGen encrypt decrypt

/-- Running Phase 1 (`adversary.choose`) of a `MultiCCA2AdversaryOf Msg` against `cca2Phase1Oracle`
is uniformly strict PPT in `(n, pk, sk)` whenever `decrypt` is computable in polynomial time. -/
@[program_certificate]
theorem isPPTOn_run_cca2MultiPhase1Oracle {Msg Out : Type} {encMsg : Msg ↪ List Bool}
    {encOut : Out ↪ List Bool} {decrypt : ℕ → List Bool → List Bool → Option Out}
    {adversary : MultiCCA2AdversaryOf Msg}
    (hdec : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) (encOption encOut))
    (hA : adversary.IsPPT encMsg) :
    IsPPTOn encKeyPairInput
      (encPair (encPair (encList (encPair encMsg encMsg)) encBits) (encFinEnum Unit))
      (fun caller : ℕ × List Bool × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
            (cca2Phase1Oracle encOut decrypt caller.1 caller.2.2))
          (adversary.choose caller.1 caller.2.1)).run ()) :=
  isPPTOn_run_cca2Phase1Oracle_of_choose hdec hA.choose

/-- Running Phase 2 (`adversary.guess`) against `cca2MultiPhase2Oracle` is uniformly strict PPT in
`(n, sk, state, cts)` whenever `decrypt` is computable in polynomial time. -/
@[program_certificate]
theorem isPPTOn_run_cca2MultiPhase2Oracle {Msg Out : Type} {encMsg : Msg ↪ List Bool}
    {encOut : Out ↪ List Bool} {decrypt : ℕ → List Bool → List Bool → Option Out}
    {adversary : MultiCCA2AdversaryOf Msg}
    (hdec : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) (encOption encOut))
    (hA : adversary.IsPPT encMsg) :
    IsPPTOn (encPair encUnary (encPair encBits (encPair encBits (encList encBits))))
      (encPair encBool (encFinEnum Unit))
      (fun caller : ℕ × List Bool × List Bool × List (List Bool) =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
            (cca2MultiPhase2Oracle encOut decrypt caller.1 caller.2.1 caller.2.2.2))
          (adversary.guess caller.1 caller.2.2.1 caller.2.2.2)).run ()) := by
  exact isPPTOn_run_cca2Phase2Oracle_of_guess
    (blocked := fun req cts => decide (req ∈ cts)) hdec hA.guess (by fun_prop)

/-- The complete `cca2MultiGameOn` experiment is uniformly strict PPT on the unary security
parameter whenever `valid`, `keyGen`, `encrypt`, `decrypt`, and `adversary` are admissible. -/
@[program_certificate]
theorem isPPTOn_cca2MultiGameOn {Msg Out : Type} {encMsg : Msg ↪ List Bool}
    {encOut : Out ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    {adversary : MultiCCA2AdversaryOf Msg}
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg =>
        valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encChallengePairInput encMsg) encBool)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    (hdecrypt : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) (encOption encOut))
    (hA : adversary.IsPPT encMsg) (bit : Bool) :
    IsPPTOn encUnary encBool
      (cca2MultiGameOn valid encOut keyGen encrypt decrypt adversary bit) := by
  unfold cca2MultiGameOn
  dsimp only
  refine hkeyGen.bind_with ((isPPTOn_run_cca2MultiPhase1Oracle hdecrypt hA).bind_with ?_)
  refine IsPPTOn.cond (by fun_prop)
    ((IsPPTOn.mapMWith (element := encPair encMsg encMsg) (by cases bit <;> fun_prop)
      (by fun_prop)).bind_with ?_) (by fun_prop)
  have hprep : ComputableInPolyTime (fun p => (p.1.1.1, p.1.1.2.2, p.1.2.1.2, p.2))
      (encPair (encPair encKeyPairInput
        (encPair (encPair (encList (encPair encMsg encMsg)) encBits) (encFinEnum Unit)))
        (encList encBits))
      (encPair encUnary (encPair encBits (encPair encBits (encList encBits)))) := by fun_prop
  exact ((isPPTOn_run_cca2MultiPhase2Oracle hdecrypt hA).preprocess hprep).bind
    (ComputableInPolyTime.fst _ _).isPPTOn

/-- The complete `cca2MultiGame` experiment is uniformly strict PPT on the unary security parameter
whenever `keyGen`, `encrypt`, `decrypt`, and `adversary` are admissible. -/
@[program_certificate]
theorem isPPTOn_cca2MultiGame {Msg Out : Type} {encMsg : Msg ↪ List Bool}
    {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    {adversary : MultiCCA2AdversaryOf Msg}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    (hdecrypt : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) (encOption encOut))
    (hA : adversary.IsPPT encMsg) (bit : Bool) :
    IsPPTOn encUnary encBool (cca2MultiGame encOut keyGen encrypt decrypt adversary bit) :=
  isPPTOn_cca2MultiGameOn (ComputableInPolyTime.const true)
    hkeyGen hencrypt hdecrypt hA bit

/-! ### Playing a restricted multi-challenge CCA game inside the unrestricted one -/

/-- The adversary that plays `cca2MultiGameOn valid` inside the unrestricted `cca2MultiGame`. Its
`choose` runs `adversary.choose n pk` and prepends the bit
`choice.1.all (fun p => valid n pk p.1 p.2)` to the saved state; its `guess` returns `false` when
that bit is `false` and otherwise runs `adversary.guess` on the rest of the state. -/
def MultiCCA2AdversaryOf.restrict {Msg : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (adversary : MultiCCA2AdversaryOf Msg) : MultiCCA2AdversaryOf Msg where
  choose n pk := do
    let choice ← adversary.choose n pk
    return (choice.1, choice.1.all (fun p => valid n pk p.1 p.2) :: choice.2)
  guess n state cts :=
    if state.headD false then adversary.guess n state.tail cts else pure false

/-- Running the unrestricted `cca2MultiGame` on `adversary.restrict valid` has the same output
distribution as running `cca2MultiGameOn valid` on `adversary`. -/
theorem eval_cca2MultiGame_restrict {Msg Out : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : MultiCCA2AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval
      (cca2MultiGame encOut keyGen encrypt decrypt (adversary.restrict valid) bit n) =
      ProbComp.eval (cca2MultiGameOn valid encOut keyGen encrypt decrypt adversary bit n) := by
  have hall (l : List (Msg × Msg)) : (l.all fun _ => true) = true :=
    List.all_eq_true.mpr fun _ _ => rfl
  simp only [cca2MultiGame, cca2MultiGameOn, MultiCCA2AdversaryOf.restrict, hall, ↓reduceIte,
    OracleComp.interpret_bind, OracleComp.interpret_pure,
    StateT.run_bind, StateT.run_pure, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind,
    PMF.pure_bind, apply_ite ProbComp.eval]
  congr 1 with keys : 1
  congr 1 with choiceOut : 1
  cases choiceOut.1.1.all (fun p => valid n keys.1 p.1 p.2) <;>
    simp [OracleComp.interpret_pure, StateT.run_pure, ProbComp.eval_pure, PMF.bind_const]

/-- Restricting a uniform strict oracle PPT multi-challenge CCA adversary by a polynomial-time
admissibility predicate keeps it uniform strict oracle PPT. -/
theorem MultiCCA2AdversaryOf.IsPPT.restrict {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg =>
        valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encChallengePairInput encMsg) encBool)
    {adversary : MultiCCA2AdversaryOf Msg}
    (hadversary : MultiCCA2AdversaryOf.IsPPT encMsg adversary) :
    MultiCCA2AdversaryOf.IsPPT encMsg (adversary.restrict valid) where
  choose := by
    have := hadversary.choose.on
    apply IsOraclePPTOn.isOraclePPT
    dsimp only [MultiCCA2AdversaryOf.restrict]
    fun_prop
  guess := by
    have := hadversary.guess
    dsimp only [MultiCCA2AdversaryOf.restrict]
    fun_prop

/-- Unrestricted batch-challenge multi-challenge CCA security implies batch-challenge
multi-challenge CCA security under every polynomial-time admissibility predicate. -/
theorem INDCCA2MultiOf.indcca2MultiOn {Msg Out : Type} {encMsg : Msg ↪ List Bool}
    {encOut : Out ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (h : INDCCA2MultiOf encMsg encOut keyGen encrypt decrypt)
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg =>
        valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encChallengePairInput encMsg) encBool) :
    INDCCA2MultiOn valid encMsg encOut keyGen encrypt decrypt := by
  intro adversary hadversary
  simpa only [eval_cca2MultiGame_restrict] using
    h (adversary.restrict valid) (hadversary.restrict hvalid)

/-- Unrestricted bit-word batch-challenge multi-challenge CCA security implies
`WordINDCCA2Multi`. -/
theorem INDCCA2MultiOf.wordINDCCA2Multi
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option (List Bool)}
    (h : INDCCA2MultiOf encBits encBits keyGen encrypt decrypt) :
    WordINDCCA2Multi keyGen encrypt decrypt :=
  h.indcca2MultiOn computableInPolyTime_wordValid

/-! ### Batch-challenge multi-challenge CCA implies single-challenge 1CCA (Definition 12.2) -/

/-- Embed a single-challenge `CCA2AdversaryOf Msg` into a `MultiCCA2AdversaryOf Msg` by returning
a singleton challenge list `[choice.1]` in Phase 1 and reading `cts.headD []` in Phase 2
([BonehShoup2023], Section 12.1, Definition 12.2, printed p. 468: a 1CCA adversary is a CCA
adversary restricted to a single encryption query). -/
def CCA2AdversaryOf.toMulti {Msg : Type} (adversary : CCA2AdversaryOf Msg) :
    MultiCCA2AdversaryOf Msg where
  choose n pk := (fun choice => ([choice.1], choice.2)) <$> adversary.choose n pk
  guess n state cts := adversary.guess n state (cts.headD [])

/-- Embed a single-challenge bit `CCA2Adversary` into a `MultiCCA2Adversary`. -/
abbrev CCA2Adversary.toMulti (adversary : CCA2Adversary) : MultiCCA2Adversary :=
  CCA2AdversaryOf.toMulti adversary

/-- Embedding a strict oracle PPT `CCA2AdversaryOf Msg` yields a strict oracle PPT
`MultiCCA2AdversaryOf Msg`. -/
theorem CCA2AdversaryOf.isPPT_toMulti {Msg : Type} {encMsg : Msg ↪ List Bool}
    {adversary : CCA2AdversaryOf Msg} (hA : adversary.IsPPT encMsg) :
    (adversary.toMulti).IsPPT encMsg where
  choose := by
    have := hA.choose.on
    apply IsOraclePPTOn.isOraclePPT
    dsimp only [CCA2AdversaryOf.toMulti]
    fun_prop
  guess := by
    have := hA.guess
    dsimp only [CCA2AdversaryOf.toMulti]
    fun_prop

/-- Embedding a strict oracle PPT bit `CCA2Adversary` yields a strict oracle PPT
`MultiCCA2Adversary`. -/
theorem CCA2Adversary.isPPT_toMulti {adversary : CCA2Adversary} (hA : adversary.IsPPT) :
    (adversary.toMulti).IsPPT :=
  CCA2AdversaryOf.isPPT_toMulti hA

/-- Embedding a `CCA2AdversaryOf Msg` into `MultiCCA2AdversaryOf Msg` preserves its per-stage
decryption query bounds `(Q₁ n, Q₂ n)`. -/
theorem CCA2AdversaryOf.isQueryBounded_toMulti {Msg : Type} {adversary : CCA2AdversaryOf Msg}
    {Q₁ Q₂ : ℕ → ℕ} (hQ : adversary.IsQueryBounded Q₁ Q₂) :
    (adversary.toMulti).IsQueryBounded Q₁ Q₂ :=
  ⟨fun n pk => (OracleComp.isCostBounded_map_iff _ _ _).mpr (hQ.1 n pk),
    fun n state cts => hQ.2 n state (cts.headD [])⟩

/-- Running an embedded single-challenge adversary `adversary.toMulti` in `cca2MultiGameOn` has
the exact same output distribution as running `adversary` in `cca2GameOn`. -/
theorem eval_cca2MultiGameOn_toMulti {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : CCA2AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval
      (cca2MultiGameOn valid encOut keyGen encrypt decrypt adversary.toMulti bit n) =
      ProbComp.eval (cca2GameOn valid encOut keyGen encrypt decrypt adversary bit n) := by
  simp only [cca2MultiGameOn, cca2GameOn, CCA2AdversaryOf.toMulti, OracleComp.interpret_map,
    StateT.run_map, ProbComp.eval_bind, ProbComp.eval_map, PMF.bind_map,
    Function.comp_def, List.all_cons, List.all_nil, Bool.and_true]
  congr 1 with keys : 1
  congr 1 with choiceOut : 1
  by_cases h : valid n keys.1 choiceOut.1.1.1 choiceOut.1.1.2 = true
  · simp [h, cca2MultiPhase2Oracle_singleton]
  · simp [h]

/-- Running an embedded single-challenge adversary `adversary.toMulti` in `cca2MultiGame` has the
exact same output distribution as running `adversary` in `cca2Game`. -/
theorem eval_cca2MultiGame_toMulti {Msg Out : Type}
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : CCA2AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval
      (cca2MultiGame encOut keyGen encrypt decrypt adversary.toMulti bit n) =
      ProbComp.eval (cca2Game encOut keyGen encrypt decrypt adversary bit n) :=
  eval_cca2MultiGameOn_toMulti (fun _ _ _ _ => true) encOut keyGen encrypt decrypt adversary bit n

/-- **Batch-challenge multi-challenge CCA security implies single-challenge 1CCA security**
([BonehShoup2023], Section 12.1, Definition 12.2, printed p. 468, since a 1CCA adversary is a CCA
adversary restricted to a single encryption query) under any challenge-pair admissibility predicate
`valid`. -/
theorem INDCCA2MultiOn.indcca2On {Msg Out : Type}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (h : INDCCA2MultiOn valid encMsg encOut keyGen encrypt decrypt) :
    INDCCA2On valid encMsg encOut keyGen encrypt decrypt := by
  intro adversary hA
  simpa only [eval_cca2MultiGameOn_toMulti] using
    h adversary.toMulti (CCA2AdversaryOf.isPPT_toMulti hA)

/-- **Unrestricted batch-challenge multi-challenge CCA security implies unrestricted 1CCA
security** ([BonehShoup2023], Definition 12.2). -/
theorem INDCCA2MultiOf.indcca2Of {Msg Out : Type}
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (h : INDCCA2MultiOf encMsg encOut keyGen encrypt decrypt) :
    INDCCA2Of encMsg encOut keyGen encrypt decrypt :=
  INDCCA2MultiOn.indcca2On h

/-- **Bit batch-challenge multi-challenge CCA security implies bit 1CCA security**
([BonehShoup2023], Definition 12.2). -/
theorem INDCCA2Multi.indcca2
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Bool}
    (h : INDCCA2Multi keyGen encrypt decrypt) :
    INDCCA2 keyGen encrypt decrypt :=
  INDCCA2MultiOn.indcca2On h

/-- **Word batch-challenge multi-challenge CCA security implies word 1CCA security**
([BonehShoup2023], Definition 12.2). -/
theorem WordINDCCA2Multi.wordINDCCA2
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option (List Bool)}
    (h : WordINDCCA2Multi keyGen encrypt decrypt) :
    WordINDCCA2 keyGen encrypt decrypt :=
  INDCCA2MultiOn.indcca2On h

/-! ### Single-challenge 1CCA implies batch-challenge CCA (step toward Theorem 12.1) -/

open scoped NNReal

/-- Saved state passed from Phase 1 (`choose`) to Phase 2 (`guess`) of `cca2MultiToSingleAt`. -/
structure MultiCCA2State where
  /-- Whether Phase 1 accepted the challenge list and embedded the external challenge. -/
  active : Bool
  /-- State word saved by the multi-challenge adversary's `choose`. -/
  stateA : List Bool
  /-- Challenge ciphertexts before the embedded one, encrypting the right messages. -/
  ctsFront : List (List Bool)
  /-- Challenge ciphertexts after the embedded one, encrypting the left messages. -/
  ctsBack : List (List Bool)

/-- Encoding of `MultiCCA2State` as the framed tuple `(active, stateA, ctsFront, ctsBack)`. -/
enc_structure encMultiCCA2State : MultiCCA2State where
  active : encBool, stateA : encBits, ctsFront : (encList encBits), ctsBack : (encList encBits)

/-- Total polynomial-time decoder for `encMultiCCA2State`. -/
def multiCCA2StateDecoder : Decoder encMultiCCA2State :=
  (Decoder.bool.pair (Decoder.bits.pair ((Decoder.list Decoder.bits).pair
    (Decoder.list Decoder.bits)))).map
    (fun (active, stateA, ctsFront, ctsBack) => ⟨active, stateA, ctsFront, ctsBack⟩)
    (fun s => (s.active, s.stateA, s.ctsFront, s.ctsBack)) (fun _ => rfl) (fun _ => rfl)

/-- Encoded inactive state returned when `split ≥ choice.1.length` or any chosen challenge pair
fails `valid`. -/
def rejectMultiCCA2State : List Bool :=
  encMultiCCA2State ⟨false, [], [], []⟩

@[simp] theorem decode_rejectMultiCCA2State :
    multiCCA2StateDecoder.decode rejectMultiCCA2State = ⟨false, [], [], []⟩ :=
  multiCCA2StateDecoder.decode_enc ⟨false, [], [], []⟩

/-- Stateless Phase 2 filter handler for the multi-to-single CCA reduction: reject any decryption
query `request.2 ∈ cts` with `[]`, and forward all other queries `request.2 ∉ cts` to the external
single-challenge decryption oracle (truncating the reply to `decBound request.2` bits for strict
oracle PPT certification). -/
def multiPhase2FilterHandler (decBound : List Bool → ℕ) (cts : List (List Bool))
    (request : Unit × List Bool) :
    StateT Unit (WordOracleComp Unit) (List Bool) := fun s =>
  if decide (request.2 ∈ cts) then
    pure ([], s)
  else
    (fun reply => (reply, s)) <$>
      (List.take (decBound request.2) <$> ProbOracleComp.query ((), request.2))

/-- Each call to `multiPhase2FilterHandler` makes at most `1` external decryption query. -/
theorem isQueryBounded_multiPhase2FilterHandler (decBound : List Bool → ℕ)
    (cts : List (List Bool)) (request : Unit × List Bool) (s : Unit) :
    (multiPhase2FilterHandler decBound cts request s).IsQueryBounded 1 := by
  unfold multiPhase2FilterHandler
  split_ifs
  · exact OracleComp.IsCostBounded.pure ([], s) 1
  · rw [Functor.map_map]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      (ProbOracleComp.IsQueryBounded.query ((), request.2))

/-- Running a strict oracle PPT program through `multiPhase2FilterHandler` is uniformly strict
oracle PPT whenever the reply-length cap and forbidden ciphertext list are computable in polynomial
time from the caller's input. -/
theorem isOraclePPTOn_run_multiPhase2FilterHandler {Caller β : Type}
    {ECaller : Caller ↪ List Bool} {EOut : β ↪ List Bool}
    {cap : Caller → List Bool → ℕ} {cts : Caller → List (List Bool)}
    {prog : Caller → WordOracleComp Unit β}
    (hcap : ComputableInPolyTime (fun p : Caller × List Bool => cap p.1 p.2)
      (encPair ECaller encBits) encUnary)
    (hcts : ComputableInPolyTime cts ECaller (encList encBits))
    (hprog : IsOraclePPTOn (Operation := Unit) ECaller EOut prog) :
    IsOraclePPTOn (Operation := Unit) ECaller (encPair EOut (encFinEnum Unit))
      (fun a =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (multiPhase2FilterHandler (cap a) (cts a)))
          (prog a)).run ()) := by
  refine hprog.run_interpret_preprocess_open (operationEncoding := encFinEnum Unit)
    (stateEncoding := encFinEnum Unit)
    (prepare := id) (initial := fun _ => ()) (resources := cap)
    ComputableInPolyTime.id'
    (by
      have hlim : ComputableInPolyTime
          (fun x : Caller × (Unit × List Bool) × Unit => cap x.1 x.2.1.2)
          (encHandlerCall ECaller (encFinEnum Unit) (encFinEnum Unit)) encUnary :=
        hcap.comp (show ComputableInPolyTime (fun x => (x.1, x.2.1.2))
          (encHandlerCall ECaller (encFinEnum Unit) (encFinEnum Unit)) _ by fun_prop)
      dsimp only [multiPhase2FilterHandler]
      exact IsOraclePPTOn.cond (by fun_prop) (by fun_prop)
        ((IsOraclePPTOn.query_take (Operation := Unit) () (by fun_prop) hlim).map_with
          (by fun_prop)))
    (by fun_prop) (fun _ _ => True) (fun _ => trivial) hcap
    fun _ _ _ _ _ hresult => ?_
  dsimp only [multiPhase2FilterHandler] at hresult
  split_ifs at hresult
  · supp_cases hresult; exact ⟨trivial, Nat.zero_le _, Nat.le_add_right _ _⟩
  · supp_cases hresult; exact ⟨trivial, List.length_take_le _ _, Nat.le_add_right _ _⟩

/-- Interpreting `multiPhase2FilterHandler` against `cca2Phase2Oracle` on `ct ∈ cts` has the exact
same output distribution as running directly against `cca2MultiPhase2Oracle` on `cts`, whenever
`decBound` upper-bounds every encoded decryption output length. -/
theorem eval_run_multiPhase2FilterHandler {Out α : Type}
    (encOut : Out ↪ List Bool)
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : List Bool → ℕ)
    (n : ℕ) (sk ct : List Bool) (cts : List (List Bool))
    (hct : ct ∈ cts)
    (hdecBound : ∀ req, (encOption encOut (decrypt n sk req)).length ≤ decBound req)
    (prog : WordOracleComp Unit α) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2Phase2Oracle encOut decrypt n sk ct))
      (Prod.fst <$> (OracleComp.interpret
        (OracleComp.sumHandler
          (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
          (multiPhase2FilterHandler decBound cts))
        prog).run ())).run ()) =
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2MultiPhase2Oracle encOut decrypt n sk cts))
      prog).run ()) := by
  rw [OracleComp.interpret_map, StateT.run_map, ProbComp.eval_map,
    ProbOracleComp.eval_run_interpret_eq_runWith, ProbOracleComp.eval_run_interpret_eq_runWith,
    ProbOracleComp.runWith_run_interpret_map (multiPhase2FilterHandler decBound cts)
      (fun q s => ProbComp.eval (cca2Phase2Oracle encOut decrypt n sk ct q s))
      (fun q s => ProbComp.eval (cca2MultiPhase2Oracle encOut decrypt n sk cts q s))
      (fun _ => ()) (fun _ => ()) (by
      intro ⟨⟨⟩, req⟩ ⟨⟩
      change (ProbComp.eval (cca2MultiPhase2Oracle encOut decrypt n sk cts ((), req) ())).map
          (fun x => (x.1, (), ())) =
        (ProbOracleComp.runWith
            (fun q s => ProbComp.eval (cca2Phase2Oracle encOut decrypt n sk ct q s))
            (multiPhase2FilterHandler decBound cts ((), req) ()) ()).map
          (fun result => (result.1.1, result.1.2, result.2))
      by_cases hmem : req ∈ cts
      · simp [cca2MultiPhase2Oracle, multiPhase2FilterHandler, hmem, ProbComp.eval_pure]
      · have hne : (req == ct) = false :=
          beq_eq_false_iff_ne.mpr fun heq => hmem (heq ▸ hct)
        unfold cca2MultiPhase2Oracle multiPhase2FilterHandler
        simp only [hmem, decide_false, Bool.false_eq_true, ↓reduceIte, Functor.map_map,
          ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, cca2Phase2Oracle, hne,
          ProbComp.eval_pure, PMF.pure_map]
        simp only [Prod.map_apply, id_eq, List.take_of_length_le (hdecBound req)])
      prog (), PMF.map_comp]
  exact (congrArg (PMF.map · _) (funext fun _ => rfl : _ = id)).trans (PMF.map_id _)

/-- Continuation of the multi-challenge hybrid experiment at index `split : ℕ` after
`(keys, choice)` have been sampled. -/
noncomputable def cca2MultiHybridCont {Msg Out : Type}
    (encOut : Out ↪ List Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : MultiCCA2AdversaryOf Msg) (n : ℕ)
    (keys : List Bool × List Bool)
    (choice : List (Msg × Msg) × List Bool) (split : ℕ) : ProbComp Bool := do
  let ctsFront ← (choice.1.take split).mapM (fun p => encrypt n keys.1 p.2)
  let ctsBack ← (choice.1.drop split).mapM (fun p => encrypt n keys.1 p.1)
  let cts := ctsFront ++ ctsBack
  let guessOut ← (OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (cca2MultiPhase2Oracle encOut decrypt n keys.2 cts))
    (adversary.guess n choice.2 cts)).run ()
  return guessOut.1

/-- Hybrid multi-challenge CCA experiment at index `split : ℕ` ([BonehShoup2023], Section 12.1,
Theorem 12.1, printed p. 468): encrypt the first `split` challenge pairs (`choice.1.take split`)
using the right (`true`) message `p.2` and the remaining challenge pairs (`choice.1.drop split`)
using the left (`false`) message `p.1`. -/
noncomputable def cca2MultiHybridGameOn {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : MultiCCA2AdversaryOf Msg) (split n : ℕ) : ProbComp Bool := do
  let keys ← keyGen n
  let choiceOut ← (OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (cca2Phase1Oracle encOut decrypt n keys.2))
    (adversary.choose n keys.1)).run ()
  let choice := choiceOut.1
  if choice.1.all (fun p => valid n keys.1 p.1 p.2) then
    cca2MultiHybridCont encOut encrypt decrypt adversary n keys choice split
  else
    return false

/-- At `split = 0`, `cca2MultiHybridGameOn` coincides with `cca2MultiGameOn ... false`. -/
@[simp] theorem eval_cca2MultiHybridGameOn_zero {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : MultiCCA2AdversaryOf Msg) (n : ℕ) :
    ProbComp.eval (cca2MultiHybridGameOn valid encOut keyGen encrypt decrypt adversary 0 n) =
      ProbComp.eval (cca2MultiGameOn valid encOut keyGen encrypt decrypt adversary false n) := by
  simp [cca2MultiHybridGameOn, cca2MultiHybridCont, cca2MultiGameOn]

/-- Whenever every supported Phase 1 run chooses at most `split` challenge pairs,
`cca2MultiHybridGameOn` at `split` has the same output distribution as
`cca2MultiGameOn ... true`. -/
theorem eval_cca2MultiHybridGameOn_of_le {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : MultiCCA2AdversaryOf Msg) (split n : ℕ)
    (hbound : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ challenges stateA, ((challenges, stateA), ()) ∈ (ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (cca2Phase1Oracle encOut decrypt n keys.2))
        (adversary.choose n keys.1)).run ())).support →
        challenges.length ≤ split) :
    ProbComp.eval (cca2MultiHybridGameOn valid encOut keyGen encrypt decrypt adversary split n) =
      ProbComp.eval (cca2MultiGameOn valid encOut keyGen encrypt decrypt adversary true n) := by
  simp only [cca2MultiHybridGameOn, cca2MultiHybridCont, cca2MultiGameOn, ProbComp.eval_bind]
  apply PMF.bind_congr_on_support
  intro keys hkeys
  apply PMF.bind_congr_on_support
  intro choiceOut hchoice
  have hle := hbound keys hkeys choiceOut.1.1 choiceOut.1.2 hchoice
  simp [List.take_of_length_le hle, List.drop_eq_nil_of_le hle]

/-- Single-challenge `CCA2AdversaryOf Msg` reduction at fixed hybrid index `split : ℕ`
(batch-challenge specialization of [BonehShoup2023], Section 12.1, Theorem 12.1, printed
p. 468). -/
noncomputable def cca2MultiToSingleAt {Msg : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decBound : ℕ → List Bool → ℕ)
    (adversary : MultiCCA2AdversaryOf Msg) (split : ℕ) : CCA2AdversaryOf Msg where
  choose n pk := do
    let choice ← adversary.choose n pk
    if decide (split < choice.1.length) && choice.1.all (fun p => valid n pk p.1 p.2) then
      let target := choice.1.getD split (default, default)
      let ctsFront ←
        ProbOracleComp.sample ((choice.1.take split).mapM (fun p => encrypt n pk p.2))
      let ctsBack ←
        ProbOracleComp.sample ((choice.1.drop (split + 1)).mapM (fun p => encrypt n pk p.1))
      return (target, encMultiCCA2State ⟨true, choice.2, ctsFront, ctsBack⟩)
    else
      return ((default, default), rejectMultiCCA2State)
  guess n state ct :=
    let decoded := multiCCA2StateDecoder.decode state
    if decoded.active then
      let cts := decoded.ctsFront ++ ct :: decoded.ctsBack
      Prod.fst <$> (OracleComp.interpret
        (OracleComp.sumHandler
          (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
          (multiPhase2FilterHandler (decBound n) cts))
        (adversary.guess n decoded.stateA cts)).run ()
    else
      pure false

/-- Single-challenge `CCA2AdversaryOf Msg` reduction that samples a uniform dyadic hybrid index
`split ← ProbOracleComp.sample (sampleDyadicIndex (Q n))` in Phase 1 and runs
`cca2MultiToSingleAt valid encrypt decBound adversary split` (batch-challenge specialization of
[BonehShoup2023], Section 12.1, Theorem 12.1, printed p. 468). -/
noncomputable def cca2MultiToSingle {Msg : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decBound : ℕ → List Bool → ℕ) (Q : ℕ → ℕ)
    (adversary : MultiCCA2AdversaryOf Msg) : CCA2AdversaryOf Msg where
  choose n pk := do
    let split ← ProbOracleComp.sample (ProbComp.sampleDyadicIndex (Q n))
    (cca2MultiToSingleAt valid encrypt decBound adversary split).choose n pk
  guess n state ct :=
    (cca2MultiToSingleAt valid encrypt decBound adversary 0).guess n state ct

/-- Phase 1 (`choose`) of `cca2MultiToSingleAt` is uniformly strict oracle PPT in
`((n, pk), split)`. -/
theorem isOraclePPTOn_cca2MultiToSingleAt_choose {Msg : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decBound : ℕ → List Bool → ℕ}
    {adversary : MultiCCA2AdversaryOf Msg}
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg =>
        valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encChallengePairInput encMsg) encBool)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    (hA : adversary.IsPPT encMsg) :
    IsOraclePPTOn (Operation := Unit)
      (encPair (encPair encUnary encBits) encUnary)
      (encChoiceOut encMsg)
      (fun caller : (ℕ × List Bool) × ℕ =>
        (cca2MultiToSingleAt valid encrypt decBound adversary caller.2).choose
          caller.1.1 caller.1.2) := by
  dsimp only [cca2MultiToSingleAt]
  refine (hA.choose.on.preprocess (by fun_prop)).bind_with ?_
  refine IsOraclePPTOn.cond (by fun_prop) ?_ (by fun_prop)
  refine (IsPPTOn.mapMWith (element := encPair encMsg encMsg) (by fun_prop)
    (by fun_prop)).isOraclePPTOn.bind_with ?_
  refine (IsPPTOn.mapMWith (element := encPair encMsg encMsg) (by fun_prop)
    (by fun_prop)).isOraclePPTOn.bind_with ?_
  fun_prop

/-- Phase 2 (`guess`) of `cca2MultiToSingleAt` is uniformly strict oracle PPT in
`(n, state, ct)`. -/
theorem isOraclePPTOn_cca2MultiToSingleAt_guess {Msg : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    {decBound : ℕ → List Bool → ℕ}
    {adversary : MultiCCA2AdversaryOf Msg}
    (hdecBound : ComputableInPolyTime
      (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    (hA : adversary.IsPPT encMsg) (split : ℕ) :
    IsOraclePPTOn (Operation := Unit)
      encGuessInput encBool
      (fun p =>
        (cca2MultiToSingleAt valid encrypt decBound adversary split).guess
          p.1 p.2.1 p.2.2) := by
  have hrun := isOraclePPTOn_run_multiPhase2FilterHandler
    (ECaller := encGuessInput) (EOut := encBool)
    (cap := fun p req => decBound p.1 req)
    (cts := fun p => (multiCCA2StateDecoder.decode p.2.1).ctsFront ++
      p.2.2 :: (multiCCA2StateDecoder.decode p.2.1).ctsBack)
    (hdecBound.comp (show ComputableInPolyTime (fun q => (q.1.1, q.2))
      (encPair encGuessInput encBits) _ by fun_prop))
    (by fun_prop)
    (hA.guess.preprocess
      (prepare := fun p : ℕ × List Bool × List Bool =>
        (p.1, (multiCCA2StateDecoder.decode p.2.1).stateA,
          (multiCCA2StateDecoder.decode p.2.1).ctsFront ++
            p.2.2 :: (multiCCA2StateDecoder.decode p.2.1).ctsBack))
      (by fun_prop))
  dsimp only [cca2MultiToSingleAt]
  fun_prop

/-- `cca2MultiToSingleAt` preserves strict oracle PPT admissibility (`CCA2AdversaryOf.IsPPT`). -/
theorem isPPT_cca2MultiToSingleAt {Msg : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decBound : ℕ → List Bool → ℕ}
    {adversary : MultiCCA2AdversaryOf Msg}
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg =>
        valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encChallengePairInput encMsg) encBool)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    (hdecBound : ComputableInPolyTime
      (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    (hA : adversary.IsPPT encMsg) (split : ℕ) :
    (cca2MultiToSingleAt valid encrypt decBound adversary split).IsPPT encMsg where
  choose := by
    have h := (isOraclePPTOn_cca2MultiToSingleAt_choose (decBound := decBound)
      hvalid hencrypt hA).preprocess
      (ComputableInPolyTime.prod ComputableInPolyTime.id' (ComputableInPolyTime.const split))
    exact h.isOraclePPT
  guess := isOraclePPTOn_cca2MultiToSingleAt_guess valid encrypt hdecBound hA split

/-- `cca2MultiToSingle` preserves strict oracle PPT admissibility (`CCA2AdversaryOf.IsPPT`). -/
theorem isPPT_cca2MultiToSingle {Msg : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decBound : ℕ → List Bool → ℕ} {Q : ℕ → ℕ}
    {adversary : MultiCCA2AdversaryOf Msg}
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg =>
        valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encChallengePairInput encMsg) encBool)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    (hdecBound : ComputableInPolyTime
      (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hA : adversary.IsPPT encMsg) :
    (cca2MultiToSingle valid encrypt decBound Q adversary).IsPPT encMsg where
  choose := by
    have hsample : IsOraclePPTOn (Operation := Unit) (encPair encUnary encBits) encUnary
        (fun caller : ℕ × List Bool =>
          ProbOracleComp.sample (ProbComp.sampleDyadicIndex (Q caller.1))) := by fun_prop
    exact (hsample.bind_with
      (isOraclePPTOn_cca2MultiToSingleAt_choose hvalid hencrypt hA)).isOraclePPT
  guess := isOraclePPTOn_cca2MultiToSingleAt_guess valid encrypt hdecBound hA 0

/-- `cca2MultiToSingleAt` preserves both Phase 1 (`Q₁ n`) and Phase 2 (`Q₂ n`) decryption query
bounds ([BonehShoup2023], Theorem 12.1, printed p. 468). -/
theorem isQueryBounded_cca2MultiToSingleAt {Msg : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decBound : ℕ → List Bool → ℕ)
    {adversary : MultiCCA2AdversaryOf Msg} {Q₁ Q₂ : ℕ → ℕ}
    (hQ : adversary.IsQueryBounded Q₁ Q₂) (split : ℕ) :
    (cca2MultiToSingleAt valid encrypt decBound adversary split).IsQueryBounded Q₁ Q₂ := by
  refine ⟨fun n pk => ?_, fun n state ct => ?_⟩
  · unfold cca2MultiToSingleAt
    dsimp only
    exact (hQ.1 n pk).bind (m := 0) fun choice => by
      split_ifs
      · exact (ProbOracleComp.IsQueryBounded.sample _).bind (m := 0) fun ctsFront =>
          (ProbOracleComp.IsQueryBounded.sample _).bind (m := 0) fun ctsBack =>
            OracleComp.IsCostBounded.pure _ 0
      · exact OracleComp.IsCostBounded.pure _ 0
  · unfold cca2MultiToSingleAt
    dsimp only
    split_ifs
    · refine (OracleComp.isCostBounded_map_iff _ _ _).mpr ?_
      refine OracleComp.IsCostBounded.run_interpret (fun q s => ?_)
        (hQ.2 n (multiCCA2StateDecoder.decode state).stateA _) ()
      cases q with
      | inl m =>
        simpa [OracleComp.sumHandler, StateT.lift] using
          (OracleComp.isCostBounded_map_iff (·, s) (ProbOracleComp.sample (ProbComp.unifFin m))
            0).mpr (ProbOracleComp.IsQueryBounded.sample (ProbComp.unifFin m))
      | inr req =>
        exact isQueryBounded_multiPhase2FilterHandler (decBound n) _ req s
    · exact OracleComp.IsCostBounded.pure false (Q₂ n)

/-- `cca2MultiToSingle` preserves both Phase 1 (`Q₁ n`) and Phase 2 (`Q₂ n`) decryption query
bounds ([BonehShoup2023], Theorem 12.1, printed p. 468). -/
theorem isQueryBounded_cca2MultiToSingle {Msg : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decBound : ℕ → List Bool → ℕ) (Q : ℕ → ℕ)
    {adversary : MultiCCA2AdversaryOf Msg} {Q₁ Q₂ : ℕ → ℕ}
    (hQ : adversary.IsQueryBounded Q₁ Q₂) :
    (cca2MultiToSingle valid encrypt decBound Q adversary).IsQueryBounded Q₁ Q₂ := by
  have hat := isQueryBounded_cca2MultiToSingleAt valid encrypt decBound hQ
  refine ⟨fun n pk => ?_, fun n state ct => (hat 0).2 n state ct⟩
  unfold cca2MultiToSingle
  dsimp only
  simpa only [Nat.zero_add] using
    (ProbOracleComp.IsQueryBounded.sample (ProbComp.sampleDyadicIndex (Q n))).bind
      fun split => (hat split).1 n pk

/-- Running `cca2MultiToSingle` in `cca2GameOn` averages `cca2MultiToSingleAt` uniformly over
`Fin (dyadicSize (Q n))`. -/
theorem eval_cca2GameOn_cca2MultiToSingle {Msg Out : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : ℕ → List Bool → ℕ) (Q : ℕ → ℕ)
    (adversary : MultiCCA2AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval
      (cca2GameOn valid encOut keyGen encrypt decrypt
        (cca2MultiToSingle valid encrypt decBound Q adversary) bit n) =
      (PMF.uniformOfFintype (Fin (dyadicSize (Q n)))).bind
        (fun i =>
          ProbComp.eval
            (cca2GameOn valid encOut keyGen encrypt decrypt
              (cca2MultiToSingleAt valid encrypt decBound adversary i.val) bit n)) := by
  have hguess (i : ℕ) :
      (cca2MultiToSingleAt valid encrypt decBound adversary i).guess =
        (cca2MultiToSingleAt valid encrypt decBound adversary 0).guess := rfl
  simp only [cca2GameOn, cca2MultiToSingle, ProbComp.eval_sampleDyadicIndex, hguess,
    runWith_norm, pmf_norm]
  exact PMF.bind_comm _ _ _

private theorem eval_cca2GameOn_cca2MultiToSingleAt {Msg Out : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : ℕ → List Bool → ℕ)
    (adversary : MultiCCA2AdversaryOf Msg) (split : ℕ) (bit : Bool) (n : ℕ)
    (hdecBound : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ req, (encOption encOut (decrypt n keys.2 req)).length ≤ decBound n req) :
    ProbComp.eval
      (cca2GameOn valid encOut keyGen encrypt decrypt
        (cca2MultiToSingleAt valid encrypt decBound adversary split) bit n) =
    (ProbComp.eval (keyGen n)).bind fun keys =>
      (ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (cca2Phase1Oracle encOut decrypt n keys.2))
        (adversary.choose n keys.1)).run ())).bind fun choiceOut =>
          if decide (split < choiceOut.1.1.length) &&
              choiceOut.1.1.all (fun p => valid n keys.1 p.1 p.2) then
            ProbComp.eval (cca2MultiHybridCont encOut encrypt decrypt adversary n keys choiceOut.1
              (if bit then split + 1 else split))
          else
            PMF.pure false := by
  simp only [cca2GameOn, cca2MultiToSingleAt, OracleComp.interpret_bind, StateT.run_bind,
    ProbComp.eval_bind, PMF.bind_bind]
  refine PMF.bind_congr_on_support _ _ _ fun keys hkeys =>
    PMF.bind_congr_on_support _ _ _ fun choiceOut _ => ?_
  by_cases hcond :
      (decide (split < choiceOut.1.1.length) &&
        choiceOut.1.1.all (fun p => valid n keys.1 p.1 p.2)) = true
  · obtain ⟨hltDec, hall⟩ := Bool.and_eq_true_iff.mp hcond
    have hlt : split < choiceOut.1.1.length := decide_eq_true_eq.mp hltDec
    have htarget_eq : choiceOut.1.1.getD split (default, default) = choiceOut.1.1[split] :=
      List.getD_eq_getElem _ _ hlt
    have hvalid_target :
        valid n keys.1 (choiceOut.1.1.getD split (default, default)).1
          (choiceOut.1.1.getD split (default, default)).2 = true :=
      List.all_eq_true.mp hall _ (htarget_eq ▸ List.getElem_mem hlt)
    simp only [hcond, ↓reduceIte, ChoiceOut.msg₀, ChoiceOut.msg₁, ChoiceOut.state,
      ChoiceOut.msgs, ProbOracleComp.eval_run_interpret_eq_runWith, ProbOracleComp.runWith_bind,
      ProbOracleComp.runWith_sample, ProbOracleComp.runWith_pure, PMF.bind_map, Function.comp_def,
      PMF.bind_bind, PMF.pure_bind, hvalid_target, ProbComp.eval_bind,
      multiCCA2StateDecoder.decode_enc]
    have hguess (ctsFront ctsBack : List (List Bool)) (ct : List Bool) :
        (ProbOracleComp.runWith
          (fun q s => ProbComp.eval (cca2Phase2Oracle encOut decrypt n keys.2 ct q s))
          (Prod.fst <$> (OracleComp.interpret
            (OracleComp.sumHandler
              (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
              (multiPhase2FilterHandler (decBound n) (ctsFront ++ ct :: ctsBack)))
            (adversary.guess n choiceOut.1.2 (ctsFront ++ ct :: ctsBack))).run ()) ()) =
        ProbComp.eval ((OracleComp.interpret
          (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
            (cca2MultiPhase2Oracle encOut decrypt n keys.2 (ctsFront ++ ct :: ctsBack)))
          (adversary.guess n choiceOut.1.2 (ctsFront ++ ct :: ctsBack))).run ()) := by
      rw [← ProbOracleComp.eval_run_interpret_eq_runWith]
      exact eval_run_multiPhase2FilterHandler encOut decrypt (decBound n) n keys.2 ct
        (ctsFront ++ ct :: ctsBack) (List.mem_append_right _ (List.mem_cons_self ..))
        (hdecBound keys hkeys) _
    simp only [hguess]
    cases bit
    · simp only [Bool.false_eq_true, ↓reduceIte, cca2MultiHybridCont, ProbComp.eval_bind]
      congr 1 with ctsFront : 1
      rw [List.drop_eq_getElem_cons hlt, ← htarget_eq, List.mapM_cons]
      simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
      exact PMF.bind_comm _ _ _
    · simp only [↓reduceIte, cca2MultiHybridCont, ProbComp.eval_bind]
      rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, ← htarget_eq,
        List.mapM_append, List.mapM_cons, List.mapM_nil]
      simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
      congr 1 with ctsFront : 1
      rw [PMF.bind_comm]
      congr 1 with ct : 1
      congr 1 with ctsBack : 1
      rw [List.append_assoc, List.singleton_append]
  · simp only [hcond, Bool.false_eq_true, ↓reduceIte, ChoiceOut.msg₀, ChoiceOut.msg₁,
      ChoiceOut.state, ChoiceOut.msgs, OracleComp.interpret_pure, StateT.run_pure,
      ProbComp.eval_pure, PMF.pure_bind, decode_rejectMultiCCA2State]
    by_cases hv : valid n keys.1 default default = true
    · simp only [hv, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind,
        PMF.bind_const]
    · simp only [hv, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure]

/-- **Single-step hybrid identity for multi-challenge CCA** ([BonehShoup2023], Theorem 12.1,
printed p. 468): at any hybrid index `split : ℕ`, the signed success-probability gap between
`cca2MultiHybridGameOn ... split` and `cca2MultiHybridGameOn ... (split + 1)` equals the signed
1CCA gap of `cca2MultiToSingleAt ... split`. -/
theorem cca2MultiHybridGameOn_step_gap {Msg Out : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : ℕ → List Bool → ℕ)
    (adversary : MultiCCA2AdversaryOf Msg) (split n : ℕ)
    (hdecBound : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ req, (encOption encOut (decrypt n keys.2 req)).length ≤ decBound n req) :
    (Game.succProbability
        (ProbComp.eval
          (cca2MultiHybridGameOn valid encOut keyGen encrypt decrypt adversary split n)) : ℝ) -
      Game.succProbability
        (ProbComp.eval
          (cca2MultiHybridGameOn valid encOut keyGen encrypt decrypt adversary (split + 1) n)) =
      (Game.succProbability
        (ProbComp.eval
          (cca2GameOn valid encOut keyGen encrypt decrypt
            (cca2MultiToSingleAt valid encrypt decBound adversary split) false n)) : ℝ) -
      Game.succProbability
        (ProbComp.eval
          (cca2GameOn valid encOut keyGen encrypt decrypt
            (cca2MultiToSingleAt valid encrypt decBound adversary split) true n)) := by
  have hadd :
      ProbComp.eval
        (cca2MultiHybridGameOn valid encOut keyGen encrypt decrypt adversary split n) true +
      ProbComp.eval
        (cca2GameOn valid encOut keyGen encrypt decrypt
          (cca2MultiToSingleAt valid encrypt decBound adversary split) true n) true =
      ProbComp.eval
        (cca2MultiHybridGameOn valid encOut keyGen encrypt decrypt adversary (split + 1) n) true +
      ProbComp.eval
        (cca2GameOn valid encOut keyGen encrypt decrypt
          (cca2MultiToSingleAt valid encrypt decBound adversary split) false n) true := by
    rw [eval_cca2GameOn_cca2MultiToSingleAt valid encOut keyGen encrypt decrypt decBound adversary
        split false n hdecBound,
      eval_cca2GameOn_cca2MultiToSingleAt valid encOut keyGen encrypt decrypt decBound adversary
        split true n hdecBound]
    simp only [cca2MultiHybridGameOn, ProbComp.eval_bind]
    refine PMF.bind_apply_add_eq_on_support fun keys _ =>
      PMF.bind_apply_add_eq_on_support fun choiceOut _ => ?_
    by_cases hall : choiceOut.1.1.all (fun p => valid n keys.1 p.1 p.2) = true
    · by_cases hlt : split < choiceOut.1.1.length
      · simp [hall, decide_eq_true hlt, add_comm]
      · have hle : choiceOut.1.1.length ≤ split := Nat.le_of_not_lt hlt
        have hle1 : choiceOut.1.1.length ≤ split + 1 := Nat.le_add_right_of_le hle
        simp [hall, decide_eq_false hlt, cca2MultiHybridCont,
          List.take_of_length_le hle, List.take_of_length_le hle1,
          List.drop_eq_nil_of_le hle, List.drop_eq_nil_of_le hle1]
    · simp [hall, ProbComp.eval_pure]
  have hreal := congrArg ENNReal.toReal hadd
  rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _),
    ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)] at hreal
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal]
  linarith

/-- Signed hybrid gap for batch-challenge multi-challenge CCA, a step toward [BonehShoup2023],
Theorem 12.1 (printed p. 468) for batch challenges only: when every supported Phase 1 challenge
list has length at most `Q n`, the batch-challenge multi-challenge signed success-probability gap
equals `dyadicSize (Q n)` times the single-challenge 1CCA gap of `cca2MultiToSingle`. -/
theorem cca2MultiGameOn_gap {Msg Out : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : ℕ → List Bool → ℕ) (Q : ℕ → ℕ)
    (adversary : MultiCCA2AdversaryOf Msg) (n : ℕ)
    (hdecBound : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ req, (encOption encOut (decrypt n keys.2 req)).length ≤ decBound n req)
    (hQ : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ challenges stateA, ((challenges, stateA), ()) ∈ (ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (cca2Phase1Oracle encOut decrypt n keys.2))
        (adversary.choose n keys.1)).run ())).support →
        challenges.length ≤ Q n) :
    (Game.succProbability
        (ProbComp.eval
          (cca2MultiGameOn valid encOut keyGen encrypt decrypt adversary false n)) : ℝ) -
      Game.succProbability
        (ProbComp.eval
          (cca2MultiGameOn valid encOut keyGen encrypt decrypt adversary true n)) =
      (dyadicSize (Q n) : ℝ) *
        ((Game.succProbability
          (ProbComp.eval
            (cca2GameOn valid encOut keyGen encrypt decrypt
              (cca2MultiToSingle valid encrypt decBound Q adversary) false n)) : ℝ) -
        Game.succProbability
          (ProbComp.eval
            (cca2GameOn valid encOut keyGen encrypt decrypt
              (cca2MultiToSingle valid encrypt decBound Q adversary) true n))) := by
  have : NeZero (dyadicSize (Q n)) := ⟨(dyadicSize_pos (Q n)).ne'⟩
  have h0 := eval_cca2MultiHybridGameOn_zero valid encOut keyGen encrypt decrypt adversary n
  have htop := eval_cca2MultiHybridGameOn_of_le valid encOut keyGen encrypt decrypt adversary
    (dyadicSize (Q n)) n fun keys hkeys challenges stateA hchoice =>
      (hQ keys hkeys challenges stateA hchoice).trans (Nat.le_of_lt (lt_dyadicSize (Q n)))
  have hred := Game.succProbability_hybrid_reduction
    (games := fun split =>
      ProbComp.eval (cca2MultiHybridGameOn valid encOut keyGen encrypt decrypt adversary split n))
    (game1 := fun split =>
      ProbComp.eval
        (cca2GameOn valid encOut keyGen encrypt decrypt
          (cca2MultiToSingleAt valid encrypt decBound adversary split) false n))
    (game2 := fun split =>
      ProbComp.eval
        (cca2GameOn valid encOut keyGen encrypt decrypt
          (cca2MultiToSingleAt valid encrypt decBound adversary split) true n))
    (dyadicSize (Q n)) (dyadicSize (Q n)) le_rfl 1
    (fun split _ => by
      rw [one_mul]
      exact cca2MultiHybridGameOn_step_gap valid encOut keyGen encrypt decrypt decBound adversary
        split n hdecBound)
  rw [← h0, ← htop, hred, mul_one, eval_cca2GameOn_cca2MultiToSingle,
    eval_cca2GameOn_cca2MultiToSingle]
  simp only [Fin.is_lt, ↓reduceIte]

/-- Hybrid advantage identity for batch-challenge multi-challenge CCA, a step toward
[BonehShoup2023], Theorem 12.1 (printed p. 468) for batch challenges only: when every supported
Phase 1 challenge list has length at most `Q n`, the batch-challenge multi-challenge CCA advantage
equals `dyadicSize (Q n)` times the single-challenge 1CCA advantage of `cca2MultiToSingle`. -/
theorem advantage_cca2MultiGameOn {Msg Out : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : ℕ → List Bool → ℕ) (Q : ℕ → ℕ)
    (adversary : MultiCCA2AdversaryOf Msg) (n : ℕ)
    (hdecBound : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ req, (encOption encOut (decrypt n keys.2 req)).length ≤ decBound n req)
    (hQ : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ challenges stateA, ((challenges, stateA), ()) ∈ (ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (cca2Phase1Oracle encOut decrypt n keys.2))
        (adversary.choose n keys.1)).run ())).support →
        challenges.length ≤ Q n) :
    Game.advantage
      (ProbComp.eval (cca2MultiGameOn valid encOut keyGen encrypt decrypt adversary false n))
      (ProbComp.eval (cca2MultiGameOn valid encOut keyGen encrypt decrypt adversary true n)) =
      dyadicSize (Q n) *
        Game.advantage
          (ProbComp.eval
            (cca2GameOn valid encOut keyGen encrypt decrypt
              (cca2MultiToSingle valid encrypt decBound Q adversary) false n))
          (ProbComp.eval
            (cca2GameOn valid encOut keyGen encrypt decrypt
              (cca2MultiToSingle valid encrypt decBound Q adversary) true n)) := by
  apply NNReal.eq
  rw [NNReal.coe_mul, Game.coe_advantage, Game.coe_advantage, NNReal.coe_natCast,
    cca2MultiGameOn_gap valid encOut keyGen encrypt decrypt decBound Q adversary n hdecBound hQ,
    abs_mul, Nat.abs_cast]

/-- Batch-challenge step toward [BonehShoup2023], Theorem 12.1 (printed p. 468), not the cited
result: single-challenge 1CCA security implies batch-challenge multi-challenge CCA security, in
which all encryption queries come in one batch between Phase 1 and Phase 2 decryption queries,
whenever `valid`, `keyGen`, `encrypt`, and `decrypt` are polynomial-time / strict PPT. Attack
Game 12.1 (p. 467) lets the adversary interleave encryption and decryption queries adaptively;
Theorem 12.1 for that game is `INDCCA2On.indcca2InterleavedOn`
(`CslibFrontier/Crypto/Computational/Encryption/CCA/Interleaved.lean`). -/
theorem INDCCA2On.indcca2MultiOn {Msg Out : Type} [Inhabited Msg]
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg =>
        valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encChallengePairInput encMsg) encBool)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    (hdecrypt : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) (encOption encOut))
    (h : INDCCA2On valid encMsg encOut keyGen encrypt decrypt) :
    INDCCA2MultiOn valid encMsg encOut keyGen encrypt decrypt := by
  intro adversary hA
  obtain ⟨ck, dk, hlenKey⟩ := hkeyGen.length_le
  obtain ⟨decBound, hdecBoundPoly, hdecBound⟩ := exists_decryption_length_bound hkeyGen hdecrypt
  obtain ⟨_, _, _, _, cq, dq, _, _, hlenCh⟩ := hA.query_bounds
  let Q : ℕ → ℕ := fun n => cq * (n + ck * (n + 1) ^ dk + 2) ^ dq
  have hQPoly : ComputableInPolyTime Q encUnary encUnary := by
    dsimp only [Q]; fun_prop
  have hQ (n : ℕ) (keys : List Bool × List Bool)
      (hkeys : keys ∈ (ProbComp.eval (keyGen n)).support)
      (challenges : List (Msg × Msg)) (stateA : List Bool)
      (hchoice : ((challenges, stateA), ()) ∈ (ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (cca2Phase1Oracle encOut decrypt n keys.2))
        (adversary.choose n keys.1)).run ())).support) :
      challenges.length ≤ Q n := by
    have hk := hlenKey n keys hkeys
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply] at hk
    rw [ProbOracleComp.eval_run_interpret_eq_runWith] at hchoice
    rw [ProbOracleComp.runWith_eq_run_interpret] at hchoice
    have hch := (hlenCh n keys.1 Unit _ () () (challenges, stateA) hchoice).1
    exact hch.trans (Nat.mul_le_mul_left cq (Nat.pow_le_pow_left (by omega) dq))
  have hsingleNeg := h (cca2MultiToSingle valid encrypt decBound Q adversary)
    (isPPT_cca2MultiToSingle hvalid hencrypt hdecBoundPoly hQPoly hA)
  negligible using fun n => (advantage_cca2MultiGameOn valid encOut keyGen encrypt decrypt
    decBound Q adversary n (hdecBound n) (hQ n)).le

/-- Batch-challenge step toward [BonehShoup2023], Theorem 12.1 with Definition 12.2 (printed
p. 468), not the cited result: single-challenge 1CCA security and batch-challenge multi-challenge
CCA security are equivalent under any polynomial-time challenge-pair admissibility predicate
`valid`. Batch challenges restrict the adaptively interleaved queries of Attack Game 12.1
(p. 467); the equivalence for that game is `indcca2InterleavedOn_iff_indcca2On`. -/
theorem indcca2MultiOn_iff_indcca2On {Msg Out : Type} [Inhabited Msg]
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg =>
        valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encChallengePairInput encMsg) encBool)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    (hdecrypt : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) (encOption encOut)) :
    INDCCA2MultiOn valid encMsg encOut keyGen encrypt decrypt ↔
      INDCCA2On valid encMsg encOut keyGen encrypt decrypt :=
  ⟨INDCCA2MultiOn.indcca2On,
    INDCCA2On.indcca2MultiOn hvalid hkeyGen hencrypt hdecrypt⟩

/-- Batch-challenge step toward [BonehShoup2023], Theorem 12.1, not the cited result:
unrestricted single-challenge 1CCA security implies unrestricted batch-challenge multi-challenge
CCA security. Theorem 12.1 for interleaved queries is `INDCCA2Of.indcca2InterleavedOf`. -/
theorem INDCCA2Of.indcca2MultiOf {Msg Out : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    (hdecrypt : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) (encOption encOut))
    (h : INDCCA2Of encMsg encOut keyGen encrypt decrypt) :
    INDCCA2MultiOf encMsg encOut keyGen encrypt decrypt :=
  INDCCA2On.indcca2MultiOn (ComputableInPolyTime.const true)
    hkeyGen hencrypt hdecrypt h

/-- Batch-challenge step toward [BonehShoup2023], Theorem 12.1 with Definition 12.2, not the
cited result: unrestricted 1CCA and batch-challenge multi-challenge CCA security are
equivalent. -/
theorem indcca2MultiOf_iff_indcca2Of {Msg Out : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    (hdecrypt : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) (encOption encOut)) :
    INDCCA2MultiOf encMsg encOut keyGen encrypt decrypt ↔
      INDCCA2Of encMsg encOut keyGen encrypt decrypt :=
  indcca2MultiOn_iff_indcca2On (ComputableInPolyTime.const true)
    hkeyGen hencrypt hdecrypt

/-- Batch-challenge step toward [BonehShoup2023], Theorem 12.1, not the cited result: bit
single-challenge 1CCA security implies bit batch-challenge multi-challenge CCA security. Theorem
12.1 for interleaved queries is `INDCCA2.indcca2Interleaved`. -/
theorem INDCCA2.indcca2Multi
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Bool}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encBool) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    (hdecrypt : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) (encOption encBool))
    (h : INDCCA2 keyGen encrypt decrypt) :
    INDCCA2Multi keyGen encrypt decrypt :=
  INDCCA2Of.indcca2MultiOf hkeyGen hencrypt hdecrypt h

/-- Batch-challenge step toward [BonehShoup2023], Theorem 12.1 with Definition 12.2, not the
cited result: bit 1CCA and bit batch-challenge multi-challenge CCA security are equivalent. -/
theorem indcca2Multi_iff_indcca2
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Bool}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encBool) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    (hdecrypt : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) (encOption encBool)) :
    INDCCA2Multi keyGen encrypt decrypt ↔ INDCCA2 keyGen encrypt decrypt :=
  indcca2MultiOf_iff_indcca2Of hkeyGen hencrypt hdecrypt

/-- Batch-challenge step toward [BonehShoup2023], Theorem 12.1, not the cited result: word
single-challenge 1CCA security implies word batch-challenge multi-challenge CCA security. Theorem
12.1 for interleaved queries is `WordINDCCA2.wordINDCCA2Interleaved`. -/
theorem WordINDCCA2.wordINDCCA2Multi
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option (List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encBits) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    (hdecrypt : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) (encOption encBits))
    (h : WordINDCCA2 keyGen encrypt decrypt) :
    WordINDCCA2Multi keyGen encrypt decrypt :=
  INDCCA2On.indcca2MultiOn computableInPolyTime_wordValid
    hkeyGen hencrypt hdecrypt h

/-- Batch-challenge step toward [BonehShoup2023], Theorem 12.1 with Definition 12.2, not the
cited result: word 1CCA and word batch-challenge multi-challenge CCA security are equivalent. -/
theorem wordINDCCA2Multi_iff_wordINDCCA2
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option (List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encBits) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    (hdecrypt : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) (encOption encBits)) :
    WordINDCCA2Multi keyGen encrypt decrypt ↔ WordINDCCA2 keyGen encrypt decrypt :=
  indcca2MultiOn_iff_indcca2On computableInPolyTime_wordValid
    hkeyGen hencrypt hdecrypt

end Cslib.Crypto.Encryption
