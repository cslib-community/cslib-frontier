/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Crypto.Computational.ForgerBridge
public import CslibFrontier.Crypto.Computational.GeneratorReindex
public import CslibFrontier.Crypto.Computational.PseudorandomFunction
public import CslibFrontier.Crypto.Game.Forgery
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation.Handler
import CslibFrontier.Probability.PMF
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PPT

/-!
# Uniform message authentication codes and PRF-based MACs

A uniform symmetric message authentication code (`MACScheme`) consists of a polynomial-time
message-length schedule `msgLen : ℕ → ℕ` (defaulting to `id`), a strict probabilistic
polynomial-time key generator `keyGen`, a strict probabilistic polynomial-time tag generator `sign`,
and a deterministic polynomial-time tag verifier `verify` that accepts every tag produced by `sign`
on a `msgLen n`-bit message under a secret key sampled at security parameter `n`. Unlike digital
signatures (`SignatureScheme`), verification uses the same secret key as tag generation, and the
adversary receives no public key.

We formalize both strong (fresh-pair) existential unforgeability under adaptive chosen-message
attack (`sufCmaGame`, `SUFCMA`) and under one-time adaptive chosen-message attack (`sufOneTimeGame`,
`OneTimeSUFCMA`) as in
[Boneh and Shoup, Attack Game 6.1 / Definition 6.2 and Section 7.6][BonehShoup2023],
and ordinary fresh-message existential unforgeability under adaptive chosen-message attack
(`eufCmaGame`, `EUFCMA`) and under one-time adaptive chosen-message attack (`eufOneTimeGame`,
`OneTimeEUFCMA`) against uniform strict oracle-PPT forgers (`IsOraclePPT`). Both adaptive games
share the pair-logging execution core `signingPairOracle` (and `oneTimeSigningPairOracle` in the
one-time setting): `sufCmaGame` records returned
`(msg, tag)` pairs and accepts any valid `msgLen n`-bit forgery pair `(msg, tag)` that was never
returned (`!queriedPairs.contains (msg, tag)`), even on a previously queried message, whereas
`eufCmaGame` rejects any candidate forgery whose message was previously queried
(`!queried.contains msg`). We also provide schedule reindexing (`MACScheme.reindex`,
`MACScheme.reindexForger`, `SUFCMA.reindex`, `OneTimeSUFCMA.reindex`, `EUFCMA.reindex`,
`OneTimeEUFCMA.reindex`), which
adapts any `MACScheme` along a strictly monotone polynomial-time parameter schedule `ℓ : ℕ → ℕ` so
that at security parameter `n` it authenticates `M.msgLen (ℓ n)`-bit messages.
We prove the quantitative bounds
$$\Pr[\text{EUF-CMA}] \le \Pr[\text{SUF-CMA}], \qquad
  \Pr[\text{1-EUF-CMA}] \le \Pr[\text{1-SUF-CMA}]$$
(`succProbability_eufCmaGame_le_sufCmaGame`, `succProbability_eufOneTimeGame_le_sufOneTimeGame`)
and the security implications `SUFCMA → EUFCMA`, `SUFCMA → OneTimeSUFCMA`, and
`OneTimeSUFCMA → OneTimeEUFCMA` (`SUFCMA.eufCma`, `SUFCMA.oneTimeSUFCMA`,
`OneTimeSUFCMA.oneTimeEUFCMA`). For randomized `MACScheme.sign` algorithms the two notions differ;
for MACs with a unique valid tag per `(sk, msg)` (`eval_sufCmaGame_eq_eufCmaGame_of_unique_tag`,
`sufCma_iff_eufCma_of_unique_tag`, `eval_sufOneTimeGame_eq_eufOneTimeGame_of_unique_tag`,
`oneTimeSUFCMA_iff_oneTimeEUFCMA_of_unique_tag`), including `prfMAC`, fresh-message and fresh-pair
unforgeability coincide.

We then prove that any uniform `PseudorandomFunction` yields a `SUFCMA`-, `OneTimeSUFCMA`-,
`EUFCMA`-, and `OneTimeEUFCMA`-secure deterministic MAC (`prfMAC`,
`PseudorandomFunction.sufCma_prfMAC`, `PseudorandomFunction.oneTimeSUFCMA_prfMAC`,
`PseudorandomFunction.eufCma_prfMAC`, `PseudorandomFunction.oneTimeEUFCMA_prfMAC`), with the
quantitative security reduction of
[Boneh and Shoup, Section 6.3, Theorem 6.2][BonehShoup2023]:
$$\Pr[\text{Forge}] \le \mathrm{Adv}_{\mathrm{PRF}}(B(\mathcal{A}), n) + 2^{-n}.$$

## Main definitions

* `Cslib.Crypto.encBitsTriple`: three bit words, the input encoding of MAC verification and of
  nonce-based tagging.
* `Cslib.Crypto.MACScheme`: uniform symmetric message authentication code on `msgLen n`-bit
  messages (defaulting to `n`-bit messages).
* `Cslib.Crypto.MACScheme.signingPairOracle`, `sufCmaGame`, `SUFCMA`: pair-logging tagging oracle
  and strong (fresh-pair) adaptive SUF-CMA experiment and security predicate
  ([Boneh and Shoup, Attack Game 6.1 / Definition 6.2][BonehShoup2023]).
* `Cslib.Crypto.MACScheme.oneTimeSigningPairOracle`, `sufOneTimeGame`, `OneTimeSUFCMA`: one-time
  pair-logging tagging oracle and strong (fresh-pair) one-time MAC experiment and security predicate
  ([Boneh and Shoup, Section 7.6, printed p. 275][BonehShoup2023]).
* `Cslib.Crypto.MACScheme.signingOracle`, `eufCmaGame`, `EUFCMA`: fresh-message adaptive EUF-CMA
  experiment and security predicate.
* `Cslib.Crypto.MACScheme.oneTimeSigningOracle`, `eufOneTimeGame`, `OneTimeEUFCMA`: one-time
  fresh-message adaptive EUF-CMA experiment and security predicate.
* `Cslib.Crypto.MACScheme.toForgeExperiment`: `PK = Unit` typed forgery-experiment bridge for
  `MACScheme`, reusing `Forger.toTyped`.
* `Cslib.Crypto.MACScheme.reindex`, `Cslib.Crypto.MACScheme.reindexForger`: schedule reindexing of
  a `MACScheme` and its adaptive forger reduction (via `GeneratorReindex.parameter`).
* `Cslib.Crypto.prfMAC`: canonical deterministic MAC constructed from a keyed function family
  ([Boneh and Shoup, Section 6.3][BonehShoup2023]).
* `Cslib.Crypto.macLogHandler`, `Cslib.Crypto.macToPrfDistinguisher`: oracle logging handler and
  reduction turning a MAC forger into a PRF distinguisher.
* `Cslib.Crypto.encNonceTaggedMessage`: the encoding of a nonce-tagged message
  `((msg, nonce), tag)`.
* `Cslib.Crypto.NonceMACForger`, `Cslib.Crypto.NonceMACScheme`: uniform nonce-based message
  authentication code (`sign : Key → Msg → Nonce → ProbComp Tag`) and adaptive forger
  ([Boneh and Shoup, Section 7.5, Attack Game 7.4][BonehShoup2023]).
* `Cslib.Crypto.NonceMACScheme.signingPairOracle`, `sufCmaGame`, `eufCmaGame`, `SUFCMA`,
  `EUFCMA`: nonce-respecting adaptive chosen-message security experiments and predicates requiring
  distinct queried nonces (`(tr.map (fun e => e.1.2)).Nodup`).

## Main results

* `Cslib.Crypto.MACScheme.isPPTOn_run_signingOracle`, `isPPTOn_sufCmaGame`, `isPPT_sufCmaGame`,
  `isPPTOn_sufOneTimeGame`, `isPPT_sufOneTimeGame`, `isPPTOn_eufCmaGame`, `isPPT_eufCmaGame`: strict
  PPT certificates for the MAC SUF-CMA, one-time SUF-CMA, and EUF-CMA experiments.
* `Cslib.Crypto.MACScheme.eufCmaGame_eq_forgeExperiment`,
  `eufOneTimeGame_eq_forgeExperiment`, `sufCmaGame_eq_forgeExperiment`,
  `sufOneTimeGame_eq_forgeExperiment`: at each security parameter `n`, the four word-level MAC
  games have the exact distributions of `forgeExperiment` with `PK = Unit`.
* `Cslib.Crypto.MACScheme.succProbability_eufCmaGame_le_sufCmaGame`,
  `succProbability_eufOneTimeGame_le_sufOneTimeGame`,
  `SUFCMA.eufCma`, `SUFCMA.oneTimeSUFCMA`, `OneTimeSUFCMA.oneTimeEUFCMA`,
  `SUFCMA.oneTimeEUFCMA`: quantitative and asymptotic implications between strong, ordinary, and
  one-time unforgeability derived via `forgeExperiment`.
* `Cslib.Crypto.MACScheme.eval_sufCmaGame_eq_eufCmaGame_of_unique_tag`,
  `sufCma_iff_eufCma_of_unique_tag`,
  `eval_sufOneTimeGame_eq_eufOneTimeGame_of_unique_tag`,
  `oneTimeSUFCMA_iff_oneTimeEUFCMA_of_unique_tag`: equivalence of strong and fresh-message
  unforgeability (multi-query and one-time) for MACs with a unique valid tag per message.
* `Cslib.Crypto.MACScheme.isPPTOn_eufOneTimeGame`, `isPPT_eufOneTimeGame`: strict PPT certificates
  for the one-time MAC EUF-CMA experiment.
* `Cslib.Crypto.MACScheme.EUFCMA.oneTimeEUFCMA`: full EUF-CMA security implies one-time EUF-CMA
  security.
* `Cslib.Crypto.MACScheme.isOraclePPT_reindexForger`,
  `Cslib.Crypto.MACScheme.sufCmaGame_reindex`,
  `Cslib.Crypto.MACScheme.sufOneTimeGame_reindex`,
  `Cslib.Crypto.MACScheme.eufCmaGame_reindex`,
  `Cslib.Crypto.MACScheme.eufOneTimeGame_reindex`,
  `Cslib.Crypto.MACScheme.SUFCMA.reindex`,
  `Cslib.Crypto.MACScheme.OneTimeSUFCMA.reindex`,
  `Cslib.Crypto.MACScheme.EUFCMA.reindex`,
  `Cslib.Crypto.MACScheme.OneTimeEUFCMA.reindex`: schedule reindexing preserves `SUFCMA`,
  `OneTimeSUFCMA`, `EUFCMA`, and `OneTimeEUFCMA` along any strictly monotone polynomial-time
  schedule.
* `Cslib.Crypto.eval_sufCmaGame_prfMAC`, `Cslib.Crypto.sufCma_prfMAC_iff_eufCma`,
  `Cslib.Crypto.eval_sufOneTimeGame_prfMAC`,
  `Cslib.Crypto.oneTimeSUFCMA_prfMAC_iff_oneTimeEUFCMA`,
  `Cslib.Crypto.isOraclePPT_macToPrfDistinguisher`,
  `Cslib.Crypto.eval_prfRealGame_macToPrfDistinguisher`,
  `Cslib.Crypto.eval_prfRealGame_macToPrfDistinguisher_eq_sufCmaGame`,
  `Cslib.Crypto.succProbability_prfIdealGame_macToPrfDistinguisher_le`,
  `Cslib.Crypto.succProbability_eufCmaGame_prfMAC_le`,
  `Cslib.Crypto.succProbability_sufCmaGame_prfMAC_le`: quantitative PRF-to-MAC forgery reduction
  ([Boneh and Shoup, Theorem 6.2][BonehShoup2023]).
* `Cslib.Crypto.PseudorandomFunction.sufCma_prfMAC`,
  `Cslib.Crypto.PseudorandomFunction.oneTimeSUFCMA_prfMAC`,
  `Cslib.Crypto.PseudorandomFunction.eufCma_prfMAC`,
  `Cslib.Crypto.PseudorandomFunction.oneTimeEUFCMA_prfMAC`: any secure uniform
  `PseudorandomFunction` yields a `SUFCMA`-, `OneTimeSUFCMA`-, `EUFCMA`-, and
  `OneTimeEUFCMA`-secure `MACScheme`.
* `Cslib.Crypto.NonceMACScheme.isPPTOn_run_signingPairOracle`,
  `Cslib.Crypto.NonceMACScheme.isPPTOn_sufCmaGame`, `isPPT_sufCmaGame`, `isPPTOn_eufCmaGame`,
  `isPPT_eufCmaGame`, `succProbability_eufCmaGame_le_sufCmaGame`, `SUFCMA.eufCma`,
  `eval_sufCmaGame_eq_freshPair_of_unique_tag`: strict PPT certificates, quantitative /
  asymptotic implication from `SUFCMA` to `EUFCMA`, and unique-tag pair-freshness characterization
  for nonce-based MACs.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Chapter 6,
  Sections 6.1–6.3 (Definitions 6.1–6.2 and Theorem 6.2) and Chapter 7, Section 7.5 (Attack Game
  7.4).
* [O. Goldreich, S. Goldwasser, S. Micali, *How to Construct Random Functions*][GGM1986].
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-- Three bit words `(x, y, z)`; `x` and `y` are framed, `z` is not. It encodes the verification
input `(sk, msg, tag)` of a `MACScheme`, the tagging input `(sk, msg, nonce)` of a
`NonceMACScheme`, and the part `(msg, nonce, tag)` of its verification input after the key. -/
abbrev encBitsTriple : List Bool × List Bool × List Bool ↪ List Bool :=
  encPair encBits (encPair encBits encBits)

/-- A uniform symmetric message authentication code (MAC) on `msgLen n`-bit messages at security
parameter `n` (defaulting to `msgLen = id`, i.e., `n`-bit messages), with plain polynomial-time
message-length schedule, strict polynomial-time key generation and tag generation, deterministic
polynomial-time verification, and perfect completeness on supported keys, `msgLen n`-bit messages,
and tags [Boneh and Shoup, Definition 6.1][BonehShoup2023]. -/
structure MACScheme where
  /-- Message length authenticated at unary security parameter `n` (defaults to `n`). -/
  msgLen : ℕ → ℕ := fun n => n
  /-- The message-length schedule is computable in plain polynomial time in unary. -/
  msgLen_polyTime : ComputableInPolyTime msgLen encUnary encUnary := by
    exact ComputableInPolyTime.id'
  /-- Sample a secret MAC key `sk` at unary security parameter `n`. -/
  keyGen : ℕ → ProbComp (List Bool)
  /-- Compute a MAC tag on message `msg` using the secret key `sk`. -/
  sign : List Bool → List Bool → ProbComp (List Bool)
  /-- Deterministically verify a candidate `tag` on `msg` under secret key `sk`. -/
  verify : List Bool → List Bool → List Bool → Bool
  /-- Key generation is uniformly strict PPT in the unary security parameter. -/
  keyGen_ppt : IsPPTOn encUnary encBits keyGen
  /-- Tag generation is uniformly strict PPT in the encoded secret key and message. -/
  sign_ppt : IsPPTOn (encPair encBits encBits) encBits (fun p => sign p.1 p.2)
  /-- Verification is computable in plain polynomial time on `(sk, msg, tag)`. -/
  verify_polyTime : ComputableInPolyTime
    (fun p : List Bool × List Bool × List Bool => verify p.1 p.2.1 p.2.2)
    encBitsTriple encBool
  /-- Every tag produced by `sign` on a `msgLen n`-bit message under a supported secret key at
  security parameter `n` is accepted by `verify`. -/
  verify_sign : ∀ n sk, sk ∈ (ProbComp.eval (keyGen n)).support →
    ∀ msg, msg.length = msgLen n →
    ∀ tag, tag ∈ (ProbComp.eval (sign sk msg)).support →
    verify sk msg tag = true

namespace MACScheme

attribute [program_certificate] msgLen_polyTime keyGen_ppt sign_ppt verify_polyTime

/-- Composing `M.msgLen` with a plain polynomial-time unary parameter function is plain
polynomial-time. -/
@[program_certificate]
theorem computableInPolyTime_msgLen_comp (M : MACScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} (hn : ComputableInPolyTime n encIn encUnary) :
    ComputableInPolyTime (fun a => M.msgLen (n a)) encIn encUnary :=
  M.msgLen_polyTime.comp hn

/-- Composing `M.keyGen` with a plain polynomial-time unary parameter function is strict PPT. -/
@[program_certificate]
theorem isPPTOn_keyGen_comp (M : MACScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} (hn : ComputableInPolyTime n encIn encUnary) :
    IsPPTOn encIn encBits (fun a => M.keyGen (n a)) :=
  M.keyGen_ppt.preprocess hn

/-- Composing `M.sign` with plain polynomial-time key and message selectors is strict PPT. -/
@[program_certificate]
theorem isPPTOn_sign_comp (M : MACScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {sk msg : γ → List Bool}
    (hsk : ComputableInPolyTime sk encIn encBits)
    (hmsg : ComputableInPolyTime msg encIn encBits) :
    IsPPTOn encIn encBits (fun a => M.sign (sk a) (msg a)) :=
  M.sign_ppt.preprocess (hsk.prod hmsg)

/-- Composing `M.verify` with plain polynomial-time key, message, and tag selectors is plain
polynomial-time. -/
@[program_certificate]
theorem computableInPolyTime_verify_comp (M : MACScheme)
    {γ : Type} {encIn : γ ↪ List Bool} {sk msg tag : γ → List Bool}
    (hsk : ComputableInPolyTime sk encIn encBits)
    (hmsg : ComputableInPolyTime msg encIn encBits)
    (htag : ComputableInPolyTime tag encIn encBits) :
    ComputableInPolyTime (fun a => M.verify (sk a) (msg a) (tag a)) encIn encBool :=
  M.verify_polyTime.comp (hsk.prod (hmsg.prod htag))

/-! ### Policy-parameterized pair-logging oracle -/

/-- Policy-parameterized pair-logging MAC tagging oracle: answers `request` with `M.sign sk` and
prepends `(request.2, tag)` when `policy queriedPairs = true`, and answers `[]` without updating
`queriedPairs` otherwise. -/
private noncomputable def signingPairOracleOn (M : MACScheme)
    (policy : List (List Bool × List Bool) → Bool) (sk : List Bool)
    (request : Unit × List Bool) :
    StateT (List (List Bool × List Bool)) ProbComp (List Bool) :=
  fun queriedPairs =>
    if policy queriedPairs then do
      let tag ← M.sign sk request.2
      return (tag, (request.2, tag) :: queriedPairs)
    else
      return ([], queriedPairs)

private theorem isPPTOn_run_signingPairOracleOn (M : MACScheme)
    {policy : List (List Bool × List Bool) → Bool}
    (hpolicy : ComputableInPolyTime policy (encList (encPair encBits encBits)) encBool)
    {adversary : Forger} (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn (encPair encUnary encBits)
      (encPair (encPair encBits encBits) (encList (encPair encBits encBits)))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (M.signingPairOracleOn policy caller.2)) (adversary caller.1 [])).run []) := by
  obtain ⟨c, d, hlen⟩ := M.sign_ppt.length_le
  have hhandler : IsPPTOn
      (encPair (encPair encUnary encBits)
        (encPair (encPair (encFinEnum Unit) encBits) (encList (encPair encBits encBits))))
      (encPair encBits (encList (encPair encBits encBits)))
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool × List Bool)) =>
        M.signingPairOracleOn policy pair.1.2 pair.2.1 pair.2.2) := by
    unfold signingPairOracleOn
    exact IsPPTOn.ite (hpolicy.comp (by fun_prop))
      ((M.isPPTOn_sign_comp (by fun_prop) (by fun_prop)).bind_with
        (ComputableInPolyTime.isPPTOn (by fun_prop)))
      (ComputableInPolyTime.isPPTOn (by fun_prop))
  apply hadversary.run_interpret_preprocess
    (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
    (initial := fun _ => ([] : List (List Bool × List Bool)))
    (resources := fun caller query =>
      2 * (c * (2 * caller.2.length + query.length + 2) ^ d) + 4 * query.length + 6)
    (by fun_prop) hhandler (ComputableInPolyTime.const [])
    (fun _ _ => True) (fun _ => trivial) (by fun_prop)
  intro caller request queriedPairs _ result hresult
  unfold signingPairOracleOn at hresult
  split_ifs at hresult with hpol
  · simp only [ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
    obtain ⟨tag, htag, rfl⟩ := hresult
    have htagLen := hlen (caller.2, request.2) tag htag
    simp only [encBits_apply, length_encPair] at htagLen
    refine ⟨trivial, by lia, ?_⟩
    simp only [encList_cons, List.length_append, length_frame, length_encPair, encBits_apply]
    lia
  · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
    subst result
    exact ⟨trivial, by simp, by lia⟩

/-! ### Full adaptive chosen-message security (`EUFCMA`) -/

/-- Stateful MAC tagging oracle that tags the requested message under `sk` and prepends the
message to the list of queried messages. -/
noncomputable def signingOracle (M : MACScheme) (sk : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queried => do
    let tag ← M.sign sk request.2
    return (tag, request.2 :: queried)

/-- The fresh-message MAC EUF-CMA experiment: sample `sk ← M.keyGen n`, run the adaptive forger on
`(n, [])` with oracle access to `M.signingOracle sk`, and accept when the forger outputs a valid
`(msg, tag)` pair on a `M.msgLen n`-bit message `msg` that was never queried to the tagging oracle.

Unlike [Boneh and Shoup, Attack Game 6.1 / Definition 6.2][BonehShoup2023], which logs `(msg, tag)`
pairs and rejects only previously returned pairs, this experiment logs queried messages and rejects
any previously queried message (`!out.2.contains msg`). The two notions differ for randomized
`sign` algorithms, and coincide for deterministic canonical MACs such as `prfMAC`. -/
noncomputable def eufCmaGame (M : MACScheme) (adversary : Forger) (n : ℕ) :
    ProbComp Bool := do
  let sk ← M.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (M.signingOracle sk)) (adversary n [])).run []
  let (msg, tag) := out.1
  return (msg.length == M.msgLen n) && !out.2.contains msg &&
    M.verify sk msg tag

private theorem computableInPolyTime_eufPost (M : MACScheme) :
    ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × ((List Bool × List Bool) × List (List Bool)) =>
        (pair.2.1.1.length == M.msgLen pair.1.1) && !pair.2.2.contains pair.2.1.1 &&
          M.verify pair.1.2 pair.2.1.1 pair.2.1.2)
      (encPair (encPair encUnary encBits)
        (encPair (encPair encBits encBits) (encList encBits))) encBool := by
  simp only [List.contains_eq_mem]
  fun_prop

/-- Running an oracle-PPT forger against `signingOracle` is uniformly strict PPT in the unary
security parameter and secret key. -/
@[program_certificate]
theorem isPPTOn_run_signingOracle (M : MACScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn (encPair encUnary encBits)
      (encPair (encPair encBits encBits) (encList encBits))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (M.signingOracle caller.2)) (adversary caller.1 [])).run []) :=
  (SignatureScheme.isPPTOn_run_signingOracleOf M.sign_ppt hadversary).preprocess
    ((ComputableInPolyTime.fst _ _).prod
      ((ComputableInPolyTime.const []).prod (ComputableInPolyTime.snd _ _)))

/-- Run the complete MAC EUF-CMA experiment on its unary security parameter for any oracle-PPT
forger. -/
@[program_certificate]
theorem isPPTOn_eufCmaGame (M : MACScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn encUnary encBool (M.eufCmaGame adversary) :=
  M.keyGen_ppt.bind_with
    ((M.isPPTOn_run_signingOracle hadversary).bind_with M.computableInPolyTime_eufPost.isPPTOn)

/-- The MAC EUF-CMA experiment is uniformly strict PPT, independently of unused auxiliary input. -/
@[program_certificate]
theorem isPPT_eufCmaGame (M : MACScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPT encBool (fun n _ => M.eufCmaGame adversary n) :=
  ((M.isPPTOn_eufCmaGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Fresh-message existential unforgeability under adaptive chosen-message attack (`EUFCMA`) for a
symmetric MAC against uniform strict oracle-PPT adversaries.

Note that `eufCmaGame` enforces fresh-message unforgeability (`msg ∉ queried`), whereas
[Boneh and Shoup, Attack Game 6.1 / Definition 6.2][BonehShoup2023] defines the stronger fresh-pair
variant (`(msg, tag) ∉ queriedPairs`) for general (possibly randomized) signing algorithms. The
tagging oracle tags words of any length, while a forgery counts only on a `msgLen n`-bit message;
in the source, signing queries lie in the message space. With its weaker forgery condition and its
stronger oracle, the notion is incomparable with the source's; in particular, the source's notion
does not imply it. -/
def EUFCMA (M : MACScheme) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (M.eufCmaGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT (encPair encBits encBits))

/-- Full EUF-CMA security gives negligible forgery probability for every oracle-PPT forger. -/
theorem EUFCMA.negligible {M : MACScheme} (h : M.EUFCMA)
    (adversary : Forger) (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (M.eufCmaGame adversary n))) :=
  Game.Indistinguishable.negligible_succProbability h adversary hadversary

/-- Establish EUF-CMA security by bounding every oracle-PPT forger's success probability. -/
theorem EUFCMA.of_negligible {M : MACScheme}
    (h : ∀ adversary, IsOraclePPT (encPair encBits encBits) adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (M.eufCmaGame adversary n)))) :
    M.EUFCMA :=
  Game.Indistinguishable.of_negligible_succProbability h

/-! ### One-time adaptive chosen-message security (`OneTimeEUFCMA`) -/

/-- One-time MAC oracle that answers at most the first tagging query using `M.sign sk` and returns
the empty word without tagging on any subsequent query. -/
noncomputable def oneTimeSigningOracle (M : MACScheme) (sk : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queried =>
    if queried.isEmpty then do
      let tag ← M.sign sk request.2
      return (tag, [request.2])
    else
      return ([], queried)

/-- The one-time MAC EUF-CMA experiment: sample `sk ← M.keyGen n`, run the adaptive forger on
`(n, [])` with oracle access to `M.oneTimeSigningOracle sk`, and accept when the forger outputs a
valid tag on a `M.msgLen n`-bit message distinct from the queried message (if any). -/
noncomputable def eufOneTimeGame (M : MACScheme) (adversary : Forger) (n : ℕ) :
    ProbComp Bool := do
  let sk ← M.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (M.oneTimeSigningOracle sk)) (adversary n [])).run []
  let (msg, tag) := out.1
  return (msg.length == M.msgLen n) && !out.2.contains msg &&
    M.verify sk msg tag

/-- Running an oracle-PPT forger against `oneTimeSigningOracle` is uniformly strict PPT in the
unary security parameter and secret key. -/
@[program_certificate]
theorem isPPTOn_run_oneTimeSigningOracle (M : MACScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn (encPair encUnary encBits)
      (encPair (encPair encBits encBits) (encList encBits))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (M.oneTimeSigningOracle caller.2)) (adversary caller.1 [])).run []) :=
  (SignatureScheme.isPPTOn_run_oneTimeSigningOracleOf M.sign_ppt hadversary).preprocess
    ((ComputableInPolyTime.fst _ _).prod
      ((ComputableInPolyTime.const []).prod (ComputableInPolyTime.snd _ _)))

/-- Run the complete one-time MAC EUF-CMA experiment on its unary security parameter for any
oracle-PPT forger. -/
@[program_certificate]
theorem isPPTOn_eufOneTimeGame (M : MACScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn encUnary encBool (M.eufOneTimeGame adversary) :=
  M.keyGen_ppt.bind_with ((M.isPPTOn_run_oneTimeSigningOracle hadversary).bind_with
    M.computableInPolyTime_eufPost.isPPTOn)

/-- The one-time MAC EUF-CMA experiment is uniformly strict PPT, independently of unused auxiliary
input. -/
@[program_certificate]
theorem isPPT_eufOneTimeGame (M : MACScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPT encBool (fun n _ => M.eufOneTimeGame adversary n) :=
  ((M.isPPTOn_eufOneTimeGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Fresh-message existential unforgeability of a symmetric MAC under a one-time adaptive
chosen-message attack, against uniform strict oracle-PPT forgers. It is the one-time game of
[BonehShoup2023], Section 7.6 (p. 275), Attack Game 6.1 (pp. 218–219) with a single signing query,
with three differences. Section 7.6 defines unconditional security, negligible advantage for all
adversaries, even computationally unbounded ones; here the forgers are efficient, as for the
one-time secure MAC of Theorem 9.2 (p. 367). A forgery counts only on a message that was not
queried, where the source accepts any new message–tag pair (`OneTimeSUFCMA`). The oracle, which
answers only the first query, tags a word of any length, while a forgery counts only on a
`msgLen n`-bit message; in the source, signing queries lie in the message space. The notion is
therefore incomparable with the source's; in particular, because of the oracle, the source's notion
does not imply it. -/
def OneTimeEUFCMA (M : MACScheme) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (M.eufOneTimeGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT (encPair encBits encBits))

/-- One-time EUF-CMA security gives negligible forgery probability for every oracle-PPT forger. -/
theorem OneTimeEUFCMA.negligible {M : MACScheme} (h : M.OneTimeEUFCMA)
    (adversary : Forger) (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (M.eufOneTimeGame adversary n))) :=
  Game.Indistinguishable.negligible_succProbability h adversary hadversary

/-- Establish one-time EUF-CMA security by bounding every oracle-PPT forger's success
probability. -/
theorem OneTimeEUFCMA.of_negligible {M : MACScheme}
    (h : ∀ adversary, IsOraclePPT (encPair encBits encBits) adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (M.eufOneTimeGame adversary n)))) :
    M.OneTimeEUFCMA :=
  Game.Indistinguishable.of_negligible_succProbability h

private theorem exists_oneTimeTagBound (M : MACScheme) :
    ∃ bound : ℕ → ℕ → ℕ,
      ComputableInPolyTime (fun p : ℕ × ℕ => bound p.1 p.2) (encPair encUnary encUnary) encUnary ∧
      ∀ n, ∀ sk ∈ (ProbComp.eval (M.keyGen n)).support, ∀ msg tag,
        tag ∈ (ProbComp.eval (M.sign sk msg)).support → tag.length ≤ bound n msg.length := by
  obtain ⟨ck, dk, hlenk⟩ := M.keyGen_ppt.length_le
  obtain ⟨cs, ds, hlens⟩ := M.sign_ppt.length_le
  refine ⟨fun n L => cs * (2 * (ck * (n + 1) ^ dk) + L + 2) ^ ds, by fun_prop,
    fun n sk hsk msg tag htag => ?_⟩
  have hskLen := hlenk n sk hsk
  simp only [encUnary_apply, List.length_replicate, encBits_apply] at hskLen
  have h1 := hlens (sk, msg) tag htag
  simp only [length_encPair, encBits_apply] at h1
  exact h1.trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left (by lia) ds))

/-- Every `MACScheme` admits a plain polynomial-time bound `tagBound : ℕ → ℕ` on the length of tags
produced on `M.msgLen n`-bit messages under keys sampled from `M.keyGen n`. -/
theorem exists_tag_length_bound_of_length_eq (M : MACScheme) :
    ∃ tagBound : ℕ → ℕ,
      ComputableInPolyTime tagBound encUnary encUnary ∧
      ∀ n, ∀ sk ∈ (ProbComp.eval (M.keyGen n)).support,
        ∀ msg, msg.length = M.msgLen n →
        ∀ tag ∈ (ProbComp.eval (M.sign sk msg)).support, tag.length ≤ tagBound n := by
  obtain ⟨bound, hpoly, hb⟩ := M.exists_oneTimeTagBound
  have hlen := M.msgLen_polyTime
  refine ⟨fun n => bound n (M.msgLen n), by fun_prop,
    fun n sk hsk msg hmsg tag htag => by simpa only [hmsg] using hb n sk hsk msg tag htag⟩

/-! ### Strong adaptive chosen-message security (`SUFCMA`, Boneh–Shoup Attack Game 6.1) -/

/-- Stateful MAC tagging oracle that tags the requested message under `sk` and prepends the
returned `(msg, tag)` pair to the transcript of queried message/tag pairs
([Boneh and Shoup, Attack Game 6.1][BonehShoup2023]). -/
noncomputable def signingPairOracle (M : MACScheme) (sk : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool × List Bool)) ProbComp (List Bool) :=
  fun queriedPairs => do
    let tag ← M.sign sk request.2
    return (tag, (request.2, tag) :: queriedPairs)

/-- The strong (fresh-pair) MAC SUF-CMA experiment
([Boneh and Shoup, Attack Game 6.1 / Definition 6.2][BonehShoup2023]): sample `sk ← M.keyGen n`,
run the adaptive forger on `(n, [])` with oracle access to `M.signingPairOracle sk`, and accept when
the forger outputs a valid `(msg, tag)` pair on a `M.msgLen n`-bit message `msg` such that
`(msg, tag)` was never returned by the tagging oracle (`!out.2.contains out.1`). -/
noncomputable def sufCmaGame (M : MACScheme) (adversary : Forger) (n : ℕ) :
    ProbComp Bool := do
  let sk ← M.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (M.signingPairOracle sk)) (adversary n [])).run []
  let (msg, tag) := out.1
  return (msg.length == M.msgLen n) && !out.2.contains out.1 &&
    M.verify sk msg tag

/-- Running an oracle-PPT forger against `signingPairOracle` is uniformly strict PPT in the unary
security parameter and secret key. -/
@[program_certificate]
theorem isPPTOn_run_signingPairOracle (M : MACScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn (encPair encUnary encBits)
      (encPair (encPair encBits encBits) (encList (encPair encBits encBits)))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (M.signingPairOracle caller.2)) (adversary caller.1 [])).run []) :=
  M.isPPTOn_run_signingPairOracleOn (policy := fun _ => true) (by fun_prop) hadversary

private theorem computableInPolyTime_sufPost (M : MACScheme) :
    ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × ((List Bool × List Bool) × List (List Bool × List Bool)) =>
        (pair.2.1.1.length == M.msgLen pair.1.1) && !pair.2.2.contains pair.2.1 &&
          M.verify pair.1.2 pair.2.1.1 pair.2.1.2)
      (encPair (encPair encUnary encBits)
        (encPair (encPair encBits encBits) (encList (encPair encBits encBits)))) encBool := by
  simp only [List.contains_eq_mem]
  fun_prop

/-- Run the complete MAC SUF-CMA experiment on its unary security parameter for any oracle-PPT
forger. -/
@[program_certificate]
theorem isPPTOn_sufCmaGame (M : MACScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn encUnary encBool (M.sufCmaGame adversary) :=
  M.keyGen_ppt.bind_with ((M.isPPTOn_run_signingPairOracle hadversary).bind_with
    M.computableInPolyTime_sufPost.isPPTOn)

/-- The MAC SUF-CMA experiment is uniformly strict PPT, independently of unused auxiliary input. -/
@[program_certificate]
theorem isPPT_sufCmaGame (M : MACScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPT encBool (fun n _ => M.sufCmaGame adversary n) :=
  ((M.isPPTOn_sufCmaGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Strong (fresh-pair) existential unforgeability under adaptive chosen-message attack (`SUFCMA`)
for a symmetric MAC against uniform strict oracle-PPT adversaries
([Boneh and Shoup, Attack Game 6.1 / Definition 6.2][BonehShoup2023]). The tagging oracle tags
words of any length, while a forgery counts only on a `msgLen n`-bit message; in the source,
signing queries lie in the message space. -/
def SUFCMA (M : MACScheme) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (M.sufCmaGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT (encPair encBits encBits))

/-- Strong unforgeability gives negligible SUF-CMA forgery probability for every oracle-PPT
forger. -/
theorem SUFCMA.negligible {M : MACScheme} (h : M.SUFCMA)
    (adversary : Forger) (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (M.sufCmaGame adversary n))) :=
  Game.Indistinguishable.negligible_succProbability h adversary hadversary

/-- Establish SUF-CMA security by bounding every oracle-PPT forger's success probability. -/
theorem SUFCMA.of_negligible {M : MACScheme}
    (h : ∀ adversary, IsOraclePPT (encPair encBits encBits) adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (M.sufCmaGame adversary n)))) :
    M.SUFCMA :=
  Game.Indistinguishable.of_negligible_succProbability h

/-! ### Strong one-time adaptive chosen-message security (`OneTimeSUFCMA`, Boneh–Shoup Section 7.6)
-/

/-- One-time pair-logging MAC tagging oracle ([Boneh and Shoup, Section 7.6, printed
p. 275][BonehShoup2023]): answers at most the first tagging query using `M.sign sk`, recording the
returned `(msg, tag)` pair, and returns `[]` without tagging on any subsequent query. -/
noncomputable def oneTimeSigningPairOracle (M : MACScheme) (sk : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool × List Bool)) ProbComp (List Bool) :=
  fun queriedPairs =>
    if queriedPairs.isEmpty then do
      let tag ← M.sign sk request.2
      return (tag, [(request.2, tag)])
    else
      return ([], queriedPairs)

private theorem oneTimeSigningPairOracle_eq_on (M : MACScheme) (sk : List Bool) :
    M.oneTimeSigningPairOracle sk = M.signingPairOracleOn List.isEmpty sk := by
  funext request queriedPairs
  cases queriedPairs <;> rfl

/-- The strong (fresh-pair) one-time MAC experiment
([Boneh and Shoup, Attack Game 6.1 and Section 7.6, printed p. 275][BonehShoup2023]): sample
`sk ← M.keyGen n`, run the adaptive forger on `(n, [])` with oracle access to
`M.oneTimeSigningPairOracle sk` (which answers at most one signing query), and accept when the
forger outputs a valid `(msg, tag)` pair on a `M.msgLen n`-bit message `msg` distinct from the
queried `(msg, tag)` pair (if any). -/
noncomputable def sufOneTimeGame (M : MACScheme) (adversary : Forger) (n : ℕ) :
    ProbComp Bool := do
  let sk ← M.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (M.oneTimeSigningPairOracle sk)) (adversary n [])).run []
  let (msg, tag) := out.1
  return (msg.length == M.msgLen n) && !out.2.contains out.1 &&
    M.verify sk msg tag

/-- Running an oracle-PPT forger against `oneTimeSigningPairOracle` is uniformly strict PPT in the
unary security parameter and secret key. -/
@[program_certificate]
theorem isPPTOn_run_oneTimeSigningPairOracle (M : MACScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn (encPair encUnary encBits)
      (encPair (encPair encBits encBits) (encList (encPair encBits encBits)))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (M.oneTimeSigningPairOracle caller.2)) (adversary caller.1 [])).run []) := by
  simpa only [oneTimeSigningPairOracle_eq_on] using
    M.isPPTOn_run_signingPairOracleOn (policy := List.isEmpty) (by fun_prop) hadversary

/-- Run the complete strong one-time MAC experiment on its unary security parameter for any
oracle-PPT forger. -/
@[program_certificate]
theorem isPPTOn_sufOneTimeGame (M : MACScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn encUnary encBool (M.sufOneTimeGame adversary) :=
  M.keyGen_ppt.bind_with ((M.isPPTOn_run_oneTimeSigningPairOracle hadversary).bind_with
    M.computableInPolyTime_sufPost.isPPTOn)

/-- The strong one-time MAC experiment is uniformly strict PPT, independently of unused auxiliary
input. -/
@[program_certificate]
theorem isPPT_sufOneTimeGame (M : MACScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPT encBool (fun n _ => M.sufOneTimeGame adversary n) :=
  ((M.isPPTOn_sufOneTimeGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Strong (fresh-pair) existential unforgeability under one-time adaptive chosen-message attack
(`OneTimeSUFCMA`) for a symmetric MAC against uniform strict oracle-PPT adversaries: the
advantage `MAC1adv` of [BonehShoup2023], Section 7.6 (p. 275), in Attack Game 6.1 (pp. 218–219)
with a single signing query, is negligible, as for the one-time secure MAC of Theorem 9.2
(p. 367). The oracle answers only the first query. It tags a word of any length, while a forgery
counts only on a `msgLen n`-bit message; in the source, signing queries lie in the message
space. -/
def OneTimeSUFCMA (M : MACScheme) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (M.sufOneTimeGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT (encPair encBits encBits))

/-- Strong one-time unforgeability gives negligible `sufOneTimeGame` forgery probability for every
oracle-PPT forger. -/
theorem OneTimeSUFCMA.negligible {M : MACScheme} (h : M.OneTimeSUFCMA)
    (adversary : Forger) (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (M.sufOneTimeGame adversary n))) :=
  Game.Indistinguishable.negligible_succProbability h adversary hadversary

/-- Establish `OneTimeSUFCMA` security by bounding every oracle-PPT forger's success probability. -/
theorem OneTimeSUFCMA.of_negligible {M : MACScheme}
    (h : ∀ adversary, IsOraclePPT (encPair encBits encBits) adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (M.sufOneTimeGame adversary n)))) :
    M.OneTimeSUFCMA :=
  Game.Indistinguishable.of_negligible_succProbability h

/-! ### Bridge to `forgeExperiment` (`PK = Unit`) and SUF/EUF/one-time consequences -/

/-- The typed `PK = Unit` forgery experiment of `M` at security parameter `n` under signing policy
`signer` and freshness test `fresh`: sample `sk ← M.keyGen n` (with public key `()`), run
`adversary.toTyped n []` against `signer sk`, and accept when the candidate `(msg, tag)` has
`msg.length = M.msgLen n`, verifies under `sk`, and satisfies `fresh`. -/
noncomputable abbrev toForgeExperiment (M : MACScheme)
    (signer : Signer (List Bool) (List Bool) (List Bool))
    (fresh : List Bool → List Bool → List (List Bool × List Bool) → Bool)
    (adversary : Forger) (n : ℕ) : Experiment :=
  forgeExperiment (((), ·) <$> M.keyGen n) signer
    (fun () sk msg tag => (msg.length == M.msgLen n) && M.verify sk msg tag)
    fresh (fun () => adversary.toTyped n [])

private theorem eval_toForgeExperiment_eq_map (M : MACScheme) {σ : Type}
    (signer : Signer (List Bool) (List Bool) (List Bool))
    (oracle : List Bool → Unit × List Bool → StateT σ ProbComp (List Bool))
    (represent : List (List Bool × List Bool) → σ)
    (step : ∀ sk (request : Unit × List Bool) (log : List (List Bool × List Bool)),
      (ProbComp.eval (ProbOracleComp.logOracle (signer sk) request.2 log)).map
          (fun (a, log') => (a, represent log')) =
        ProbComp.eval (oracle sk request (represent log)))
    (fresh : List Bool → List Bool → List (List Bool × List Bool) → Bool)
    (check : List Bool → List Bool → σ → Bool)
    (hfresh : ∀ msg tag log, fresh msg tag log = check msg tag (represent log))
    (adversary : Forger) (n : ℕ) :
    ProbComp.eval (M.toForgeExperiment signer fresh adversary n) =
      ProbComp.eval (do
        let sk ← M.keyGen n
        let out ← (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (oracle sk)) (adversary n [])).run (represent [])
        let (msg, tag) := out.1
        return (msg.length == M.msgLen n) && check msg tag out.2 &&
          M.verify sk msg tag) := by
  simp only [toForgeExperiment, forgeExperiment, Forger.toTyped, ProbComp.eval_bind,
    ProbComp.eval_map, ProbComp.eval_pure, PMF.bind_map]
  congr 1
  funext sk
  dsimp only [Function.comp_apply]
  rw [← Forger.eval_runLogWith_rename_state (adversary n []) (fun w => w) (signer sk) (oracle sk)
    represent (step sk), PMF.bind_map]
  congr 1
  funext ⟨⟨msg, tag⟩, log⟩
  dsimp only [Function.comp_apply]
  rw [hfresh msg tag log]
  cases msg.length == M.msgLen n <;> cases M.verify sk msg tag <;> simp

/-- At each parameter `n`, `M.sufCmaGame adversary n` has the distribution of `forgeExperiment`
with `PK = Unit`, policy `Signer.ofSign M.sign`, and freshness `freshPair`. -/
theorem sufCmaGame_eq_forgeExperiment (M : MACScheme) (adversary : Forger) (n : ℕ) :
    ProbComp.eval (M.sufCmaGame adversary n) =
      ProbComp.eval (M.toForgeExperiment (Signer.ofSign M.sign) freshPair adversary n) :=
  (M.eval_toForgeExperiment_eq_map (Signer.ofSign M.sign) M.signingPairOracle List.reverse
    (fun _ _ _ => by
      simp [ProbOracleComp.logOracle, signingPairOracle, ProbComp.eval_map, PMF.map_comp,
        Function.comp_def])
    freshPair (fun msg tag pairs => !pairs.contains (msg, tag))
    (fun _ _ _ => by simp [freshPair]) adversary n).symm

/-- At each parameter `n`, `M.sufOneTimeGame adversary n` has the distribution of `forgeExperiment`
with `PK = Unit`, policy `(Signer.ofSign M.sign).oneTime`, and freshness `freshPair`. -/
theorem sufOneTimeGame_eq_forgeExperiment (M : MACScheme) (adversary : Forger) (n : ℕ) :
    ProbComp.eval (M.sufOneTimeGame adversary n) =
      ProbComp.eval
        (M.toForgeExperiment (Signer.ofSign M.sign).oneTime freshPair adversary n) :=
  (M.eval_toForgeExperiment_eq_map (Signer.ofSign M.sign).oneTime M.oneTimeSigningPairOracle
    List.reverse
    (fun _ _ log => by
      cases log <;> simp [ProbOracleComp.logOracle, oneTimeSigningPairOracle,
        show (default : List Bool) = [] from rfl, ProbComp.eval_map, PMF.map_comp,
        Function.comp_def])
    freshPair (fun msg tag pairs => !pairs.contains (msg, tag))
    (fun _ _ _ => by simp [freshPair]) adversary n).symm

/-- At each parameter `n`, `M.eufCmaGame adversary n` has the distribution of `forgeExperiment`
with `PK = Unit`, policy `Signer.ofSign M.sign`, and freshness `freshMessage`. -/
theorem eufCmaGame_eq_forgeExperiment (M : MACScheme) (adversary : Forger) (n : ℕ) :
    ProbComp.eval (M.eufCmaGame adversary n) =
      ProbComp.eval (M.toForgeExperiment (Signer.ofSign M.sign) freshMessage adversary n) :=
  (M.eval_toForgeExperiment_eq_map (Signer.ofSign M.sign) M.signingOracle
    (fun log => (log.map Prod.fst).reverse)
    (fun _ _ _ => by
      simp [ProbOracleComp.logOracle, signingOracle, ProbComp.eval_map, PMF.map_comp,
        Function.comp_def])
    freshMessage (fun msg _ msgs => !msgs.contains msg)
    (fun _ _ _ => by simp [freshMessage]) adversary n).symm

/-- At each parameter `n`, `M.eufOneTimeGame adversary n` has the distribution of `forgeExperiment`
with `PK = Unit`, policy `(Signer.ofSign M.sign).oneTime`, and freshness `freshMessage`. -/
theorem eufOneTimeGame_eq_forgeExperiment (M : MACScheme) (adversary : Forger) (n : ℕ) :
    ProbComp.eval (M.eufOneTimeGame adversary n) =
      ProbComp.eval
        (M.toForgeExperiment (Signer.ofSign M.sign).oneTime freshMessage adversary n) :=
  (M.eval_toForgeExperiment_eq_map (Signer.ofSign M.sign).oneTime M.oneTimeSigningOracle
    (fun log => (log.map Prod.fst).reverse)
    (fun _ _ log => by
      cases log <;> simp [ProbOracleComp.logOracle, oneTimeSigningOracle,
        show (default : List Bool) = [] from rfl, ProbComp.eval_map, PMF.map_comp,
        Function.comp_def])
    freshMessage (fun msg _ msgs => !msgs.contains msg)
    (fun _ _ _ => by simp [freshMessage]) adversary n).symm

private theorem run_limitToOneQuery_eq_oneTimeSigningPairOracle (M : MACScheme)
    (bound : ℕ → ℕ → ℕ) (n : ℕ) (sk : List Bool)
    (hbound : ∀ msg tag, tag ∈ (ProbComp.eval (M.sign sk msg)).support →
      tag.length ≤ bound n msg.length)
    (prog : WordOracleComp Unit (List Bool × List Bool)) :
    ProbComp.eval (Prod.map Prod.fst id <$> ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (M.signingPairOracle sk))
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          (SignatureScheme.oneTimeFilterHandler bound (n, [])))
        prog).run false)).run [])) =
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (M.oneTimeSigningPairOracle sk)) prog).run []) := by
  rw [ProbComp.eval_map, ProbOracleComp.eval_run_interpret_eq_runWith,
    ProbOracleComp.eval_run_interpret_eq_runWith]
  refine (congrArg (PMF.map _) (ProbOracleComp.runWith_run_interpret_map
    (SignatureScheme.oneTimeFilterHandler bound (n, []))
    (fun q s => ProbComp.eval (M.signingPairOracle sk q s))
    (fun q s => ProbComp.eval (M.oneTimeSigningPairOracle sk q s))
    (fun queriedPairs => !queriedPairs.isEmpty) (fun queriedPairs => queriedPairs) (by
      intro ⟨⟨⟩, msg⟩ queriedPairs
      rw [ProbOracleComp.runWith_eq_run_interpret]
      change _ = ((OracleComp.interpret (m := StateT (List (List Bool × List Bool)) PMF) _
        (SignatureScheme.oneTimeFilterHandler bound (n, []) ((), msg)
          (!queriedPairs.isEmpty))).run queriedPairs).map _
      cases queriedPairs with
      | nil =>
        simp only [oneTimeSigningPairOracle, List.isEmpty_nil, ↓reduceIte, Bool.not_true,
          SignatureScheme.oneTimeFilterHandler, Bool.false_eq_true, Functor.map_map,
          OracleComp.interpret_map, StateT.run_map, ProbOracleComp.interpret_query,
          PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def, signingPairOracle,
          ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind]
        simp only [StateT.run, PMF.map_bind]
        refine PMF.bind_congr_on_support _ _ _ fun tag htag => ?_
        simp [List.take_of_length_le (hbound msg tag htag)]
      | cons head tail =>
        simp [oneTimeSigningPairOracle, SignatureScheme.oneTimeFilterHandler,
          OracleComp.interpret_pure, StateT.run_pure, ProbComp.eval_pure])
    prog [])).trans ?_
  rw [PMF.map_comp]
  exact (congrArg (PMF.map · _) (funext fun _ => rfl : _ = id)).trans (PMF.map_id _)

private theorem eval_toForgeExperiment_limitToOneQuery (M : MACScheme)
    (bound : ℕ → ℕ → ℕ) (n : ℕ)
    (hbound : ∀ sk ∈ (ProbComp.eval (M.keyGen n)).support, ∀ msg tag,
      tag ∈ (ProbComp.eval (M.sign sk msg)).support → tag.length ≤ bound n msg.length)
    (fresh : List Bool → List Bool → List (List Bool × List Bool) → Bool)
    (adversary : Forger) :
    ProbComp.eval
        (M.toForgeExperiment (Signer.ofSign M.sign) fresh
          (SignatureScheme.limitToOneQuery bound adversary) n) =
      ProbComp.eval
        (M.toForgeExperiment (Signer.ofSign M.sign).oneTime fresh adversary n) := by
  simp only [toForgeExperiment, forgeExperiment, ProbComp.eval_bind, ProbComp.eval_map,
    ProbComp.eval_pure, PMF.bind_map]
  refine PMF.bind_congr_on_support _ _ _ fun sk hsk => ?_
  dsimp only [Function.comp_apply]
  have hrev :
      (ProbComp.eval (((SignatureScheme.limitToOneQuery bound adversary).toTyped n []).runLogWith
          (Signer.ofSign M.sign sk))).map (Prod.map id List.reverse) =
        (ProbComp.eval ((adversary.toTyped n []).runLogWith
          ((Signer.ofSign M.sign).oneTime sk))).map (Prod.map id List.reverse) := by
    change
      (ProbComp.eval (((SignatureScheme.limitToOneQuery bound adversary).toTyped n []).runLogWith
          (Signer.ofSign M.sign sk))).map (fun (a, log) => (a, log.reverse)) =
        (ProbComp.eval ((adversary.toTyped n []).runLogWith
          ((Signer.ofSign M.sign).oneTime sk))).map (fun (a, log) => (a, log.reverse))
    rw [Forger.toTyped, Forger.toTyped,
      Forger.eval_runLogWith_rename_state (SignatureScheme.limitToOneQuery bound adversary n [])
        (fun w => w) (Signer.ofSign M.sign sk) (M.signingPairOracle sk) List.reverse
        (fun _ _ => by
          simp [ProbOracleComp.logOracle, signingPairOracle, ProbComp.eval_map, PMF.map_comp,
            Function.comp_def]),
      Forger.eval_runLogWith_rename_state (adversary n []) (fun w => w)
        ((Signer.ofSign M.sign).oneTime sk) (M.oneTimeSigningPairOracle sk) List.reverse
        (fun _ log => by
          cases log <;> simp [ProbOracleComp.logOracle, oneTimeSigningPairOracle,
            show (default : List Bool) = [] from rfl, ProbComp.eval_map, PMF.map_comp,
            Function.comp_def])]
    dsimp only [List.reverse_nil]
    unfold SignatureScheme.limitToOneQuery
    rw [OracleComp.interpret_map, StateT.run_map]
    exact run_limitToOneQuery_eq_oneTimeSigningPairOracle M bound n sk (hbound sk hsk)
      (adversary n [])
  rw [Cslib.Probability.PMF.map_injective
    (Prod.map_injective.mpr ⟨Function.injective_id, List.reverse_injective⟩) hrev]

private theorem oneTime_of_full_forge (M : MACScheme)
    {fullGame oneTimeGame : Forger → ℕ → ProbComp Bool}
    (fresh : List Bool → List Bool → List (List Bool × List Bool) → Bool)
    (hfull : ∀ adversary n, ProbComp.eval (fullGame adversary n) =
      ProbComp.eval (M.toForgeExperiment (Signer.ofSign M.sign) fresh adversary n))
    (hone : ∀ adversary n, ProbComp.eval (oneTimeGame adversary n) =
      ProbComp.eval (M.toForgeExperiment (Signer.ofSign M.sign).oneTime fresh adversary n))
    (h : Game.Indistinguishable (fun A n => ProbComp.eval (fullGame A n))
      (fun _ _ => PMF.pure false) (IsOraclePPT (encPair encBits encBits))) :
    Game.Indistinguishable (fun A n => ProbComp.eval (oneTimeGame A n))
      (fun _ _ => PMF.pure false) (IsOraclePPT (encPair encBits encBits)) := by
  obtain ⟨bound, hbound_poly, htagBound⟩ := M.exists_oneTimeTagBound
  refine h.of_succProbability_reduction (SignatureScheme.limitToOneQuery bound)
    (fun _ => SignatureScheme.isOraclePPT_limitToOneQuery hbound_poly) fun adversary _ n => ?_
  refine le_of_eq (congrArg Game.succProbability ?_)
  rw [hone, hfull, M.eval_toForgeExperiment_limitToOneQuery bound n (htagBound n) fresh adversary]

/-- Full EUF-CMA security implies one-time EUF-CMA security for any `MACScheme`. -/
theorem EUFCMA.oneTimeEUFCMA {M : MACScheme} (h : M.EUFCMA) : M.OneTimeEUFCMA :=
  M.oneTime_of_full_forge freshMessage M.eufCmaGame_eq_forgeExperiment
    M.eufOneTimeGame_eq_forgeExperiment h

/-- Full strong unforgeability (`SUFCMA`) implies one-time strong unforgeability (`OneTimeSUFCMA`)
for any `MACScheme`. -/
theorem SUFCMA.oneTimeSUFCMA {M : MACScheme} (h : M.SUFCMA) : M.OneTimeSUFCMA :=
  M.oneTime_of_full_forge freshPair M.sufCmaGame_eq_forgeExperiment
    M.sufOneTimeGame_eq_forgeExperiment h

/-- **Quantitative EUF-CMA vs. SUF-CMA bound**: for every `MACScheme`, adaptive forger, and
security parameter `n`, the fresh-message EUF-CMA forgery probability is at most the strong
fresh-pair SUF-CMA forgery probability. -/
theorem succProbability_eufCmaGame_le_sufCmaGame (M : MACScheme)
    (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval (M.eufCmaGame adversary n)) ≤
      Game.succProbability (ProbComp.eval (M.sufCmaGame adversary n)) := by
  rw [M.eufCmaGame_eq_forgeExperiment, M.sufCmaGame_eq_forgeExperiment]
  exact succProbability_forgeExperiment_freshMessage_le (fun () => adversary.toTyped n [])

/-- **Quantitative one-time EUF-CMA vs. one-time SUF-CMA bound**: for every `MACScheme`, adaptive
forger, and security parameter `n`, the one-time fresh-message forgery probability is at most the
one-time fresh-pair forgery probability. -/
theorem succProbability_eufOneTimeGame_le_sufOneTimeGame (M : MACScheme)
    (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval (M.eufOneTimeGame adversary n)) ≤
      Game.succProbability (ProbComp.eval (M.sufOneTimeGame adversary n)) := by
  rw [M.eufOneTimeGame_eq_forgeExperiment, M.sufOneTimeGame_eq_forgeExperiment]
  exact succProbability_forgeExperiment_freshMessage_le (fun () => adversary.toTyped n [])

/-- Strong unforgeability (`SUFCMA`) implies ordinary fresh-message unforgeability (`EUFCMA`) for
every `MACScheme`. -/
theorem SUFCMA.eufCma {M : MACScheme} (h : M.SUFCMA) : M.EUFCMA :=
  h.of_succProbability_le fun adversary _ => M.succProbability_eufCmaGame_le_sufCmaGame adversary

/-- Strong one-time unforgeability (`OneTimeSUFCMA`) implies ordinary fresh-message one-time
unforgeability (`OneTimeEUFCMA`) for every `MACScheme`. -/
theorem OneTimeSUFCMA.oneTimeEUFCMA {M : MACScheme} (h : M.OneTimeSUFCMA) : M.OneTimeEUFCMA :=
  h.of_succProbability_le fun adversary _ =>
    M.succProbability_eufOneTimeGame_le_sufOneTimeGame adversary

/-- Strong unforgeability (`SUFCMA`) implies one-time unforgeability (`OneTimeEUFCMA`) for every
`MACScheme`. -/
theorem SUFCMA.oneTimeEUFCMA {M : MACScheme} (h : M.SUFCMA) : M.OneTimeEUFCMA :=
  h.eufCma.oneTimeEUFCMA

private theorem toForgeExperiment_freshPair_eq_freshMessage_of_unique_tag (M : MACScheme)
    {signer : Signer (List Bool) (List Bool) (List Bool)}
    (hsigner : ∀ sk log m program, signer sk log m = some program → program = M.sign sk m)
    (huniq : ∀ n sk, sk ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = M.msgLen n → ∀ tag tag',
      M.verify sk msg tag = true →
      tag' ∈ (ProbComp.eval (M.sign sk msg)).support → tag' = tag)
    (adversary : Forger) (n : ℕ) :
    ProbComp.eval (M.toForgeExperiment signer freshPair adversary n) =
      ProbComp.eval (M.toForgeExperiment signer freshMessage adversary n) := by
  refine forgeExperiment_freshPair_eq_freshMessage_of_unique
    (fun keys hkeys msg tag hver log program hprog tag' htag' => ?_)
    (fun () => adversary.toTyped n [])
  rcases keys with ⟨⟨⟩, sk⟩
  simp only [ProbComp.eval_map, PMF.mem_support_map_iff, Prod.mk.injEq, true_and] at hkeys
  obtain ⟨sk, hsk, rfl⟩ := hkeys
  simp only [Bool.and_eq_true, beq_iff_eq] at hver
  exact huniq n sk hsk msg hver.1 tag tag' hver.2 (hsigner sk log msg program hprog ▸ htag')

/-- For any `MACScheme` whose valid tags on `M.msgLen n`-bit messages under supported secret keys
agree with every tag in the support of `M.sign`, the `sufCmaGame` and `eufCmaGame` distributions
are identical. -/
theorem eval_sufCmaGame_eq_eufCmaGame_of_unique_tag (M : MACScheme)
    (huniq : ∀ n sk, sk ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = M.msgLen n → ∀ tag tag',
      M.verify sk msg tag = true →
      tag' ∈ (ProbComp.eval (M.sign sk msg)).support → tag' = tag)
    (adversary : Forger) (n : ℕ) :
    ProbComp.eval (M.sufCmaGame adversary n) =
      ProbComp.eval (M.eufCmaGame adversary n) := by
  rw [M.sufCmaGame_eq_forgeExperiment, M.eufCmaGame_eq_forgeExperiment]
  exact M.toForgeExperiment_freshPair_eq_freshMessage_of_unique_tag
    (fun _ _ _ _ h => (Option.some.inj h).symm) huniq adversary n

/-- For a `MACScheme` with unique valid tags per `(sk, msg)`, the SUF-CMA and EUF-CMA forgery
probabilities are equal for every forger and security parameter `n`. -/
theorem succProbability_sufCmaGame_eq_eufCmaGame_of_unique_tag (M : MACScheme)
    (huniq : ∀ n sk, sk ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = M.msgLen n → ∀ tag tag',
      M.verify sk msg tag = true →
      tag' ∈ (ProbComp.eval (M.sign sk msg)).support → tag' = tag)
    (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval (M.sufCmaGame adversary n)) =
      Game.succProbability (ProbComp.eval (M.eufCmaGame adversary n)) := by
  rw [M.eval_sufCmaGame_eq_eufCmaGame_of_unique_tag huniq adversary n]

/-- For a `MACScheme` with unique valid tags per `(sk, msg)`, strong unforgeability (`SUFCMA`) is
equivalent to ordinary fresh-message unforgeability (`EUFCMA`). -/
theorem sufCma_iff_eufCma_of_unique_tag (M : MACScheme)
    (huniq : ∀ n sk, sk ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = M.msgLen n → ∀ tag tag',
      M.verify sk msg tag = true →
      tag' ∈ (ProbComp.eval (M.sign sk msg)).support → tag' = tag) :
    M.SUFCMA ↔ M.EUFCMA :=
  ⟨SUFCMA.eufCma, fun h => h.of_succProbability_le fun adversary _ n =>
    (M.succProbability_sufCmaGame_eq_eufCmaGame_of_unique_tag huniq adversary n).le⟩

/-- For any `MACScheme` whose valid tags on `M.msgLen n`-bit messages under supported secret keys
agree with every tag in the support of `M.sign`, the `sufOneTimeGame` and `eufOneTimeGame`
distributions are identical. -/
theorem eval_sufOneTimeGame_eq_eufOneTimeGame_of_unique_tag (M : MACScheme)
    (huniq : ∀ n sk, sk ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = M.msgLen n → ∀ tag tag',
      M.verify sk msg tag = true →
      tag' ∈ (ProbComp.eval (M.sign sk msg)).support → tag' = tag)
    (adversary : Forger) (n : ℕ) :
    ProbComp.eval (M.sufOneTimeGame adversary n) =
      ProbComp.eval (M.eufOneTimeGame adversary n) := by
  rw [M.sufOneTimeGame_eq_forgeExperiment, M.eufOneTimeGame_eq_forgeExperiment]
  refine M.toForgeExperiment_freshPair_eq_freshMessage_of_unique_tag
    (fun sk log m program h => ?_) huniq adversary n
  unfold Signer.oneTime Signer.ofSign at h
  split_ifs at h
  exact (Option.some.inj h).symm

/-- For a `MACScheme` with unique valid tags per `(sk, msg)`, the `sufOneTimeGame` and
`eufOneTimeGame` forgery probabilities are equal for every forger and security parameter `n`. -/
theorem succProbability_sufOneTimeGame_eq_eufOneTimeGame_of_unique_tag (M : MACScheme)
    (huniq : ∀ n sk, sk ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = M.msgLen n → ∀ tag tag',
      M.verify sk msg tag = true →
      tag' ∈ (ProbComp.eval (M.sign sk msg)).support → tag' = tag)
    (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval (M.sufOneTimeGame adversary n)) =
      Game.succProbability (ProbComp.eval (M.eufOneTimeGame adversary n)) := by
  rw [M.eval_sufOneTimeGame_eq_eufOneTimeGame_of_unique_tag huniq adversary n]

/-- For a `MACScheme` with unique valid tags per `(sk, msg)`, strong one-time unforgeability
(`OneTimeSUFCMA`) is equivalent to ordinary fresh-message one-time unforgeability
(`OneTimeEUFCMA`). -/
theorem oneTimeSUFCMA_iff_oneTimeEUFCMA_of_unique_tag (M : MACScheme)
    (huniq : ∀ n sk, sk ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = M.msgLen n → ∀ tag tag',
      M.verify sk msg tag = true →
      tag' ∈ (ProbComp.eval (M.sign sk msg)).support → tag' = tag) :
    M.OneTimeSUFCMA ↔ M.OneTimeEUFCMA :=
  ⟨OneTimeSUFCMA.oneTimeEUFCMA, fun h => h.of_succProbability_le fun adversary _ n =>
    (M.succProbability_sufOneTimeGame_eq_eufOneTimeGame_of_unique_tag huniq adversary n).le⟩

/-! ### Schedule reindexing of a `MACScheme` (`reindex`, `reindexForger`) -/

/-- Reindex a `MACScheme` along a polynomial-time parameter schedule `ℓ : ℕ → ℕ`: at security
parameter `n`, `M.reindex ℓ hℓ` samples keys via `M.keyGen (ℓ n)` and authenticates messages of
length `M.msgLen (ℓ n)`. -/
noncomputable def reindex (M : MACScheme) (ℓ : ℕ → ℕ)
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) : MACScheme where
  msgLen n := M.msgLen (ℓ n)
  msgLen_polyTime := M.computableInPolyTime_msgLen_comp hℓ
  keyGen n := M.keyGen (ℓ n)
  sign := M.sign
  verify := M.verify
  keyGen_ppt := M.isPPTOn_keyGen_comp hℓ
  sign_ppt := M.sign_ppt
  verify_polyTime := M.verify_polyTime
  verify_sign := fun n sk hsk msg hmsg tag htag =>
    M.verify_sign (ℓ n) sk hsk msg hmsg tag htag

/-- Wrap a forger `adversary` against `M.reindex ℓ hℓ` into a forger against `M`: given unary
parameter `m` and auxiliary input `aux`, recover `n := GeneratorReindex.parameter ℓ m`; if
`ℓ n == m`, run `adversary n aux`, and otherwise return `([], [])` without querying the oracle. -/
def reindexForger (ℓ : ℕ → ℕ) (adversary : Forger) : Forger :=
  fun m aux =>
    let n := GeneratorReindex.parameter ℓ m
    if ℓ n == m then
      adversary n aux
    else
      pure ([], [])

/-- At any parameter `m = ℓ n` of a strictly monotone schedule `ℓ`, `reindexForger ℓ adversary`
executes `adversary n`. -/
@[simp]
theorem reindexForger_apply_of_strictMono {ℓ : ℕ → ℕ} (hmono : StrictMono ℓ)
    (adversary : Forger) (n : ℕ) (aux : List Bool) :
    reindexForger ℓ adversary (ℓ n) aux = adversary n aux := by
  simp [reindexForger, GeneratorReindex.parameter_apply_of_strictMono hmono]

/-- `reindexForger ℓ adversary` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_reindexForger {ℓ : ℕ → ℕ}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsOraclePPT (encPair encBits encBits) (reindexForger ℓ adversary) := by
  have hparam : ComputableInPolyTime
      (fun p : ℕ × List Bool => GeneratorReindex.parameter ℓ p.1)
      (encPair encUnary encBits) encUnary :=
    GeneratorReindex.isPolyTime_parameter hℓ (by polytime)
  ppt [reindexForger]

/-- For a strictly monotone schedule `ℓ`, `(M.reindex ℓ hℓ).sufCmaGame adversary n` is identical to
`M.sufCmaGame (reindexForger ℓ adversary) (ℓ n)`. -/
@[simp]
theorem sufCmaGame_reindex (M : MACScheme) {ℓ : ℕ → ℕ}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) (hmono : StrictMono ℓ)
    (adversary : Forger) (n : ℕ) :
    (M.reindex ℓ hℓ).sufCmaGame adversary n =
      M.sufCmaGame (reindexForger ℓ adversary) (ℓ n) := by
  unfold sufCmaGame signingPairOracle reindex
  rw [reindexForger_apply_of_strictMono hmono]

/-- For a strictly monotone schedule `ℓ`, `(M.reindex ℓ hℓ).sufOneTimeGame adversary n` is identical
to `M.sufOneTimeGame (reindexForger ℓ adversary) (ℓ n)`. -/
@[simp]
theorem sufOneTimeGame_reindex (M : MACScheme) {ℓ : ℕ → ℕ}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) (hmono : StrictMono ℓ)
    (adversary : Forger) (n : ℕ) :
    (M.reindex ℓ hℓ).sufOneTimeGame adversary n =
      M.sufOneTimeGame (reindexForger ℓ adversary) (ℓ n) := by
  unfold sufOneTimeGame oneTimeSigningPairOracle reindex
  rw [reindexForger_apply_of_strictMono hmono]

/-- For a strictly monotone schedule `ℓ`, `(M.reindex ℓ hℓ).eufCmaGame adversary n` is identical to
`M.eufCmaGame (reindexForger ℓ adversary) (ℓ n)`. -/
@[simp]
theorem eufCmaGame_reindex (M : MACScheme) {ℓ : ℕ → ℕ}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) (hmono : StrictMono ℓ)
    (adversary : Forger) (n : ℕ) :
    (M.reindex ℓ hℓ).eufCmaGame adversary n =
      M.eufCmaGame (reindexForger ℓ adversary) (ℓ n) := by
  unfold eufCmaGame signingOracle reindex
  rw [reindexForger_apply_of_strictMono hmono]

/-- For a strictly monotone schedule `ℓ`, `(M.reindex ℓ hℓ).eufOneTimeGame adversary n` is
identical to `M.eufOneTimeGame (reindexForger ℓ adversary) (ℓ n)`. -/
@[simp]
theorem eufOneTimeGame_reindex (M : MACScheme) {ℓ : ℕ → ℕ}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) (hmono : StrictMono ℓ)
    (adversary : Forger) (n : ℕ) :
    (M.reindex ℓ hℓ).eufOneTimeGame adversary n =
      M.eufOneTimeGame (reindexForger ℓ adversary) (ℓ n) := by
  unfold eufOneTimeGame oneTimeSigningOracle reindex
  rw [reindexForger_apply_of_strictMono hmono]

private theorem indistinguishable_reindex {G G' : Forger → ℕ → ProbComp Bool}
    {ℓ : ℕ → ℕ} (hℓ : ComputableInPolyTime ℓ encUnary encUnary) (hmono : StrictMono ℓ)
    (hgame : ∀ adversary n, G' adversary n = G (reindexForger ℓ adversary) (ℓ n))
    (h : Game.Indistinguishable (fun A n => ProbComp.eval (G A n))
      (fun _ _ => PMF.pure false) (IsOraclePPT (encPair encBits encBits))) :
    Game.Indistinguishable (fun A n => ProbComp.eval (G' A n))
      (fun _ _ => PMF.pure false) (IsOraclePPT (encPair encBits encBits)) := by
  apply Game.Indistinguishable.of_negligible_succProbability
  intro adversary hadversary
  refine ((h.negligible_succProbability (reindexForger ℓ adversary)
    (isOraclePPT_reindexForger hℓ hadversary)).comp_polynomiallyLowerBounded
      (.mono_of_le .id hmono.id_le)).congr fun n => ?_
  rw [hgame adversary n]

/-- Strong unforgeability (`SUFCMA`) is preserved under reindexing along any strictly monotone
plain polynomial-time schedule `ℓ`. -/
theorem SUFCMA.reindex {M : MACScheme} (h : M.SUFCMA) {ℓ : ℕ → ℕ}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) (hmono : StrictMono ℓ) :
    (M.reindex ℓ hℓ).SUFCMA :=
  indistinguishable_reindex hℓ hmono (M.sufCmaGame_reindex hℓ hmono) h

/-- Strong one-time unforgeability (`OneTimeSUFCMA`) is preserved under reindexing along any
strictly monotone plain polynomial-time schedule `ℓ`. -/
theorem OneTimeSUFCMA.reindex {M : MACScheme} (h : M.OneTimeSUFCMA) {ℓ : ℕ → ℕ}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) (hmono : StrictMono ℓ) :
    (M.reindex ℓ hℓ).OneTimeSUFCMA :=
  indistinguishable_reindex hℓ hmono (M.sufOneTimeGame_reindex hℓ hmono) h

/-- Ordinary fresh-message unforgeability (`EUFCMA`) is preserved under reindexing along any
strictly monotone plain polynomial-time schedule `ℓ`. -/
theorem EUFCMA.reindex {M : MACScheme} (h : M.EUFCMA) {ℓ : ℕ → ℕ}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) (hmono : StrictMono ℓ) :
    (M.reindex ℓ hℓ).EUFCMA :=
  indistinguishable_reindex hℓ hmono (M.eufCmaGame_reindex hℓ hmono) h

/-- One-time unforgeability (`OneTimeEUFCMA`) is preserved under reindexing along any strictly
monotone plain polynomial-time schedule `ℓ`. -/
theorem OneTimeEUFCMA.reindex {M : MACScheme} (h : M.OneTimeEUFCMA) {ℓ : ℕ → ℕ}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) (hmono : StrictMono ℓ) :
    (M.reindex ℓ hℓ).OneTimeEUFCMA :=
  indistinguishable_reindex hℓ hmono (M.eufOneTimeGame_reindex hℓ hmono) h

end MACScheme

/-! ### Canonical PRF-based MAC (`prfMAC`, Boneh–Shoup Section 6.3 & Theorem 6.2) -/

/-- Canonical deterministic MAC constructed from a keyed function family `family`
([Boneh and Shoup, Section 6.3][BonehShoup2023]):
* `keyGen n` samples a uniform `n`-bit key via `BitString.sampleList n`.
* `sign sk msg` returns `prfOracle family sk.length sk msg` (which evaluates `family sk msg` on
  `sk.length`-bit messages and rejects malformed queries with `[]`).
* `verify sk msg tag` checks `msg.length == sk.length` and `family sk msg == tag`. -/
noncomputable def prfMAC (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair : List Bool × List Bool => family pair.1 pair.2)
      (encPair encBits encBits) encBits) : MACScheme where
  keyGen n := BitString.sampleList n
  sign sk msg := pure (prfOracle family sk.length sk msg)
  verify sk msg tag := (msg.length == sk.length) && (family sk msg == tag)
  keyGen_ppt := by exact isPPTOn_sampleList
  sign_ppt := by
    have hbody : ComputableInPolyTime
        (fun p : List Bool × List Bool => prfOracle family p.1.length p.1 p.2)
        (encPair encBits encBits) encBits := by
      have heq : (fun p : List Bool × List Bool => prfOracle family p.1.length p.1 p.2) =
          (fun p : List Bool × List Bool =>
            if p.2.length == p.1.length then family p.1 p.2 else []) := by
        funext p
        simp [prfOracle]
      rw [heq]
      fun_prop
    exact hbody.isPPTOn
  verify_polyTime := by
    have hcall : ComputableInPolyTime
        (fun p : List Bool × List Bool × List Bool => family p.1 p.2.1)
        (encPair encBits (encPair encBits encBits)) encBits :=
      hpoly.comp (g := fun p : List Bool × List Bool × List Bool => (p.1, p.2.1)) (by fun_prop)
    fun_prop
  verify_sign := by
    intro n sk hsk msg hmsg tag htag
    rw [BitString.eval_sampleList] at hsk
    have hskLen : sk.length = n := BitString.length_of_mem_support_uniformList hsk
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at htag
    subst htag
    simp [prfOracle, hskLen, hmsg]

/-- Open stateful handler that forwards each MAC signing request to the external PRF/random-function
oracle (truncating the reply to `n` bits) and records the queried message in the query log. -/
def macLogHandler (n : ℕ) (request : Unit × List Bool) :
    StateT (List (List Bool)) (WordOracleComp Unit) (List Bool) :=
  fun queried =>
    (fun tag => (tag, request.2 :: queried)) <$>
      (List.take n <$> ProbOracleComp.query ((), request.2))

/-- Oracle reduction turning an adaptive MAC forger `adversary` into an `OracleDistinguisher` for
the PRF security game [Boneh and Shoup, Section 6.3, Theorem 6.2][BonehShoup2023]:
1. Run `adversary n []`, answering each tagging query via `macLogHandler n` and logging all queried
   messages.
2. When `adversary` outputs `((msg, tag), queried)`, if `msg.length == n` and
   `!queried.contains msg`, query the external oracle once on `msg` (reading at most `n` bits) and
   check whether the reply equals `tag`; otherwise return `false`. -/
def macToPrfDistinguisher (adversary : Forger) : OracleDistinguisher :=
  fun n _ => do
    let out ← (OracleComp.interpret
      (OracleComp.sumHandler
        (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        (macLogHandler n))
      (adversary n [])).run []
    let (msg, tag) := out.1
    if (msg.length == n) && !out.2.contains msg then
      (· == tag) <$> (List.take n <$> ProbOracleComp.query ((), msg))
    else
      pure false

/-- `macToPrfDistinguisher` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_macToPrfDistinguisher {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsOraclePPT encBool (macToPrfDistinguisher adversary) := by
  have hhandler : IsOraclePPTOn
      (encPair (encPair encUnary encBits)
        (encPair (encPair (encFinEnum Unit) encBits) (encList encBits)))
      (encPair encBits (encList encBits))
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        macLogHandler pair.1.1 pair.2.1 pair.2.2) := by
    ppt [macLogHandler]
  have hrun : IsOraclePPTOn (encPair encUnary encBits)
      (encPair (encPair encBits encBits) (encList encBits))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (macLogHandler caller.1))
          (adversary caller.1 [])).run []) := by
    apply hadversary.run_interpret_preprocess_open
      (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
      (initial := fun _ => ([] : List (List Bool)))
      (resources := fun caller query => caller.1 + 2 * query.length + 2)
      (by polytime) hhandler (ComputableInPolyTime.const [])
      (fun _ _ => True) (fun _ => trivial) (by polytime)
    intro caller request queried _ result hresult
    unfold macLogHandler at hresult
    obtain ⟨tag, htag, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
    obtain ⟨rawTag, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp htag
    refine ⟨trivial, (List.length_take_le _ _).trans (by lia), ?_⟩
    enc_len
  ppt [macToPrfDistinguisher]

private theorem run_macLogHandler_eq_signingOracle
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair : List Bool × List Bool => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (n : ℕ) (sk : List Bool) (hsk : sk.length = n)
    (prog : WordOracleComp Unit (List Bool × List Bool)) :
    ProbComp.eval (OracleComp.interpret
      (OracleComp.sumHandler ProbComp.unifFin (fun request =>
        pure (prfOracle family n sk request.2)))
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          (macLogHandler n))
        prog).run [])) =
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        ((prfMAC family hpoly).signingOracle sk)) prog).run []) := by
  have hread := ProbOracleComp.runWith_readOnly
    (fun request (_ : Unit) => PMF.pure (prfOracle family n sk request.2))
    ((OracleComp.interpret
      (OracleComp.sumHandler
        (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        (macLogHandler n))
      prog).run []) ()
  have hfst := congrArg (PMF.map Prod.fst) hread
  simp only [PMF.map_comp, Function.comp_def] at hfst
  rw [show (fun x : (List Bool × List Bool) × List (List Bool) => x) = id from rfl,
    PMF.map_id] at hfst
  simp only [ProbOracleComp.eval_interpret, ProbComp.eval_pure]
  rw [← OracleComp.evalWith_eq_interpret, ← hfst, ProbOracleComp.runWith_run_interpret,
    ProbOracleComp.eval_run_interpret_eq_runWith]
  have hsim := ProbOracleComp.runWith_map_state
    (oracle := fun q (state : List (List Bool) × Unit) =>
      (ProbOracleComp.runWith
        (fun request (u : Unit) => (PMF.pure (prfOracle family n sk request.2)).map (·, u))
        ((macLogHandler n q).run state.1) state.2).map
          (fun result => (result.1.1, result.1.2, result.2)))
    (oracle' := fun q s => ProbComp.eval ((prfMAC family hpoly).signingOracle sk q s))
    (represent := Prod.fst)
    (step := by
      intro ⟨⟨⟩, msg⟩ ⟨queried, ⟨⟩⟩
      change PMF.map (fun (a, s') => (a, s'.1))
          (((OracleComp.interpret
            (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
              (fun request (u : Unit) => (PMF.pure (prfOracle family n sk request.2)).map (·, u)))
            (macLogHandler n ((), msg) queried)).run ()).map
              (fun result => (result.1.1, result.1.2, result.2))) =
        ProbComp.eval ((prfMAC family hpoly).signingOracle sk ((), msg) queried)
      simp only [macLogHandler, Functor.map_map, OracleComp.interpret_map, StateT.run_map,
        ProbOracleComp.interpret_query, PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def,
        PMF.pure_map]
      dsimp only [StateT.run]
      simp only [MACScheme.signingOracle, prfMAC, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.pure_bind, hsk]
      by_cases hmsg : msg.length = n
      · have hlen_eq : (family sk msg).length = n := by
          rw [← hsk]
          exact hlen sk msg (hmsg.trans hsk.symm)
        simp [prfOracle, hmsg, List.take_of_length_le hlen_eq.le]
      · simp [prfOracle, hmsg])
    prog ([], ())
  simpa only [PMF.map_comp, Function.comp_def] using hsim

/-- Running `macToPrfDistinguisher adversary` in `prfRealGame id family` produces the exact same
Boolean distribution as the EUF-CMA experiment for `prfMAC family`. -/
theorem eval_prfRealGame_macToPrfDistinguisher
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair : List Bool × List Bool => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (adversary : Forger) (n : ℕ) :
    ProbComp.eval (prfRealGame id family (macToPrfDistinguisher adversary) n) =
      ProbComp.eval ((prfMAC family hpoly).eufCmaGame adversary n) := by
  simp only [prfRealGame, id_eq, ProbOracleComp.run, MACScheme.eufCmaGame, macToPrfDistinguisher,
    OracleComp.interpret_bind, ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_congr_on_support _ _ _ fun sk hsk => ?_
  have hsk' : sk ∈ (ProbComp.eval (BitString.sampleList n)).support := hsk
  rw [BitString.eval_sampleList] at hsk'
  have hskLen : sk.length = n := BitString.length_of_mem_support_uniformList hsk'
  rw [run_macLogHandler_eq_signingOracle hpoly hlen n sk hskLen (adversary n [])]
  refine PMF.bind_congr_on_support _ _ _ fun out _ => ?_
  dsimp only [prfMAC]
  by_cases hcond : ((out.1.1.length == n) && !out.2.contains out.1.1) = true
  · simp only [hcond, ↓reduceIte, Bool.true_and]
    have hmsgLen : out.1.1.length = n := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      exact hcond.1
    have hfamLen : (family sk out.1.1).length = n := by
      rw [← hskLen]
      exact hlen sk out.1.1 (hmsgLen.trans hskLen.symm)
    simp only [Functor.map_map, OracleComp.interpret_map,
      ProbOracleComp.interpret_query, ProbComp.eval_map, ProbComp.eval_pure, PMF.pure_map,
      prfOracle, hmsgLen, ↓reduceIte, List.take_of_length_le hfamLen.le, hskLen, beq_self_eq_true,
      Bool.true_and]
  · have hcondF : ((out.1.1.length == n) && !out.2.contains out.1.1) = false :=
      Bool.eq_false_iff.mpr hcond
    simp only [hcondF, Bool.false_eq_true, ↓reduceIte, Bool.false_and,
      OracleComp.interpret_pure, ProbComp.eval_pure]

/-- In the ideal random-function game, `macToPrfDistinguisher adversary` succeeds with probability
at most `1 / 2 ^ n`: any unqueried `n`-bit forgery message misses the lazy random-oracle cache and
draws a fresh uniform `n`-bit tag, matching the forger's candidate tag with probability at most
`1 / 2 ^ n`. -/
theorem succProbability_prfIdealGame_macToPrfDistinguisher_le (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval (prfIdealGame id id (macToPrfDistinguisher adversary) n)) ≤
      (1 : ℝ≥0) / 2 ^ n := by
  classical
  simp only [prfIdealGame_eq_lazy, id_eq]
  let combinedOracle : Unit × List Bool →
      StateT (List (List Bool) × RandomOracle.Cache (fun _ : BitString n => BitString n))
        PMF (List Bool) :=
    fun q state =>
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (fun request => lazyRandomFunctionOracle n n request.2))
        ((macLogHandler n q).run state.1)).run state.2).map
          (fun result => (result.1.1, result.1.2, result.2))
  let phase1 := ((OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k)) combinedOracle)
    (adversary n [])).run ([], fun _ => none))
  let phase2 : ((List Bool × List Bool) × List (List Bool) ×
      RandomOracle.Cache (fun _ : BitString n => BitString n)) → PMF Bool :=
    fun ⟨out, queried, cache⟩ =>
      if (out.1.length == n) && !queried.contains out.1 then
        ((OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
            (fun request => lazyRandomFunctionOracle n n request.2))
          ((· == out.2) <$> (List.take n <$> ProbOracleComp.query ((), out.1)))).run cache).map
            Prod.fst
      else
        PMF.pure false
  have hgame : ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (fun request => lazyRandomFunctionOracle n n request.2))
      (macToPrfDistinguisher adversary n [])).run (fun _ => none)).map Prod.fst =
      phase1.bind phase2 := by
    dsimp only [macToPrfDistinguisher, phase1, phase2, combinedOracle]
    simp only [OracleComp.interpret_bind, StateT.run_bind, PMF.monad_bind_eq_bind, PMF.map_bind,
      ProbOracleComp.run_interpret_run_interpret, PMF.bind_map, Function.comp_def]
    refine PMF.bind_congr_on_support _ _ _ fun ⟨out, queried, cache⟩ _ => ?_
    by_cases hcond : ((out.1.length == n) && !queried.contains out.1) = true
    · simp only [hcond, ↓reduceIte]
    · have hcondF : ((out.1.length == n) && !queried.contains out.1) = false :=
        Bool.eq_false_iff.mpr hcond
      simp only [hcondF, Bool.false_eq_true, ↓reduceIte, OracleComp.interpret_pure,
        StateT.run_pure, PMF.monad_pure_eq_pure, PMF.pure_map]
  have hinv : ∀ result state,
      (result, state) ∈ phase1.support →
      ∀ x : BitString n, state.2 x ≠ none → List.ofFn x ∈ state.1 := by
    intro result state hmem
    dsimp only [phase1] at hmem
    rw [← ProbOracleComp.runWith_eq_run_interpret] at hmem
    refine ProbOracleComp.runWith_invariant combinedOracle
      (fun s => ∀ x : BitString n, s.2 x ≠ none → List.ofFn x ∈ s.1)
      ?_ (adversary n []) ([], fun _ => none) (by simp) result state hmem
    intro ⟨⟨⟩, msg⟩ ⟨queried, cache⟩ hstate val ⟨queried', cache'⟩ hstep
    dsimp only [combinedOracle] at hstep
    rw [show (macLogHandler n ((), msg)).run queried = macLogHandler n ((), msg) queried from rfl]
      at hstep
    simp only [macLogHandler, Functor.map_map, OracleComp.interpret_map, StateT.run_map,
      ProbOracleComp.interpret_query, PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hstep
    obtain ⟨⟨rawTag, nextCache'⟩, hlazy, hpair⟩ := hstep
    cases hpair
    obtain ⟨⟨rawAns, nextCache⟩, hlazy, hpair0⟩ := hlazy
    cases hpair0
    intro x hx
    rw [List.mem_cons]
    unfold lazyRandomFunctionOracle randomFunctionQuery at hlazy
    by_cases hmsg : msg.length = n
    · simp only [hmsg, ↓reduceIte, OracleComp.interpret_map, ProbOracleComp.interpret_query,
        StateT.run_map, PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hlazy
      obtain ⟨⟨v, nextCache₂⟩, hans, hpair2⟩ := hlazy
      cases hpair2
      dsimp only [StateT.run] at hans
      cases hcache : cache (BitString.ofList n msg) with
      | some v0 =>
        rw [RandomOracle.answer_of_some _ _ _ _ hcache] at hans
        simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at hans
        rcases hans with ⟨_, rfl⟩
        exact Or.inr (hstate x hx)
      | none =>
        rw [RandomOracle.answer_of_none _ _ _ hcache] at hans
        simp only [PMF.mem_support_map_iff] at hans
        obtain ⟨v1, _, hupd⟩ := hans
        have hnc : nextCache₂ = Function.update cache (BitString.ofList n msg) (some v1) :=
          (Prod.mk.inj hupd).2.symm
        subst hnc
        by_cases heq : x = BitString.ofList n msg
        · subst heq
          exact Or.inl (BitString.ofFn_ofList hmsg)
        · dsimp only at hx
          rw [Function.update_of_ne heq] at hx
          exact Or.inr (hstate x hx)
    · simp only [hmsg, ↓reduceIte, OracleComp.interpret_pure, StateT.run_pure,
        PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hlazy
      rcases hlazy with ⟨_, rfl⟩
      exact Or.inr (hstate x hx)
  have hstep_bound : ∀ item ∈ phase1.support,
      phase2 item true ≤ (1 : ℝ≥0∞) / 2 ^ n := by
    rintro ⟨⟨msg, tag⟩, queried, cache⟩ hmem
    have hcache_inv := hinv (msg, tag) (queried, cache) hmem
    dsimp only [phase2]
    by_cases hcond : ((msg.length == n) && !queried.contains msg) = true
    · simp only [hcond, ↓reduceIte]
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcond
      rcases hcond with ⟨hmsgLen, hnotContains⟩
      have hnotMem : msg ∉ queried := by
        intro hmem_q
        have htrue := List.contains_iff_mem.mpr hmem_q
        rw [hnotContains] at htrue
        contradiction
      have hnone : cache (BitString.ofList n msg) = none := by
        by_contra hsome
        exact hnotMem (BitString.ofFn_ofList hmsgLen ▸ hcache_inv _ hsome)
      simp only [Functor.map_map, OracleComp.interpret_map, StateT.run_map,
        ProbOracleComp.interpret_query, PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def]
      unfold lazyRandomFunctionOracle randomFunctionQuery
      simp only [hmsgLen, ↓reduceIte, OracleComp.interpret_map, ProbOracleComp.interpret_query,
        StateT.run_map, PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def]
      dsimp only [StateT.run]
      rw [RandomOracle.answer_of_none _ _ _ hnone]
      simp only [PMF.map_comp, Function.comp_def]
      have htake : (fun x : BitString n => ((List.ofFn x).take n == tag)) =
          (fun x : BitString n => (List.ofFn x == tag)) := by
        funext x
        simp [List.take_of_length_le (List.length_ofFn (f := x)).le]
      rw [htake, ← PMF.bind_pure_comp]
      refine (PMF.uniformOfFintype_bind_pure_apply_true_le (E := fun x => List.ofFn x == tag)
        fun a ha b hb => List.ofFn_injective
          ((beq_iff_eq.mp ha).trans (beq_iff_eq.mp hb).symm)).trans_eq ?_
      simp
    · have hcondF : ((msg.length == n) && !queried.contains msg) = false :=
        Bool.eq_false_iff.mpr hcond
      simp only [hcondF, Bool.false_eq_true, ↓reduceIte, PMF.pure_apply, reduceCtorEq,
        zero_le]
  have htotal : (phase1.bind phase2) true ≤ (1 : ℝ≥0∞) / 2 ^ n := by
    rw [PMF.bind_apply]
    refine (tsum_le_tsum fun a => ?_).trans
      (PMF.tsum_mul_le_of_forall_le phase1 fun _ => le_rfl)
    by_cases ha : a ∈ phase1.support
    · exact mul_le_mul_right (hstep_bound a ha) _
    · simp [(phase1.apply_eq_zero_iff a).mpr ha]
  rw [hgame, Game.succProbability]
  have hne_top : (1 : ℝ≥0∞) / 2 ^ n ≠ ⊤ :=
    ENNReal.div_ne_top ENNReal.one_ne_top (by positivity)
  have hmono := ENNReal.toNNReal_mono hne_top htotal
  have hrhs : ((1 : ℝ≥0∞) / 2 ^ n).toNNReal = (1 : ℝ≥0) / 2 ^ n := by
    rw [ENNReal.toNNReal_div, ENNReal.toNNReal_one, ENNReal.toNNReal_pow, ENNReal.toNNReal_ofNat]
  rwa [hrhs] at hmono

private theorem unique_tag_prfMAC
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair : List Bool × List Bool => family pair.1 pair.2)
      (encPair encBits encBits) encBits) :
    ∀ n sk, sk ∈ (ProbComp.eval ((prfMAC family hpoly).keyGen n)).support →
      ∀ msg, msg.length = n → ∀ tag tag',
      (prfMAC family hpoly).verify sk msg tag = true →
      tag' ∈ (ProbComp.eval ((prfMAC family hpoly).sign sk msg)).support →
      tag' = tag := by
  intro n sk hsk msg hmsg tag tag' hver htag'
  dsimp [prfMAC] at hsk hver htag'
  rw [BitString.eval_sampleList] at hsk
  have hskLen : sk.length = n := BitString.length_of_mem_support_uniformList hsk
  simp only [Bool.and_eq_true, beq_iff_eq] at hver
  simp only [PMF.mem_support_pure_iff, prfOracle, hskLen, hmsg, ↓reduceIte] at htag'
  exact htag'.trans hver.2

/-- Because `prfMAC` is deterministic with a unique valid tag per `(sk, msg)`, its strong
fresh-pair `sufCmaGame` distribution is identical to its fresh-message `eufCmaGame`
distribution. -/
theorem eval_sufCmaGame_prfMAC
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair : List Bool × List Bool => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (adversary : Forger) (n : ℕ) :
    ProbComp.eval ((prfMAC family hpoly).sufCmaGame adversary n) =
      ProbComp.eval ((prfMAC family hpoly).eufCmaGame adversary n) :=
  (prfMAC family hpoly).eval_sufCmaGame_eq_eufCmaGame_of_unique_tag
    (unique_tag_prfMAC hpoly) adversary n

/-- For `prfMAC`, strong unforgeability (`SUFCMA`) and fresh-message unforgeability (`EUFCMA`)
coincide. -/
theorem sufCma_prfMAC_iff_eufCma
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair : List Bool × List Bool => family pair.1 pair.2)
      (encPair encBits encBits) encBits) :
    (prfMAC family hpoly).SUFCMA ↔ (prfMAC family hpoly).EUFCMA :=
  (prfMAC family hpoly).sufCma_iff_eufCma_of_unique_tag (unique_tag_prfMAC hpoly)

/-- Because `prfMAC` is deterministic with a unique valid tag per `(sk, msg)`, its strong
one-time fresh-pair `sufOneTimeGame` distribution is identical to its one-time fresh-message
`eufOneTimeGame` distribution. -/
theorem eval_sufOneTimeGame_prfMAC
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair : List Bool × List Bool => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (adversary : Forger) (n : ℕ) :
    ProbComp.eval ((prfMAC family hpoly).sufOneTimeGame adversary n) =
      ProbComp.eval ((prfMAC family hpoly).eufOneTimeGame adversary n) :=
  (prfMAC family hpoly).eval_sufOneTimeGame_eq_eufOneTimeGame_of_unique_tag
    (unique_tag_prfMAC hpoly) adversary n

/-- For `prfMAC`, strong one-time unforgeability (`OneTimeSUFCMA`) and fresh-message one-time
unforgeability (`OneTimeEUFCMA`) coincide. -/
theorem oneTimeSUFCMA_prfMAC_iff_oneTimeEUFCMA
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair : List Bool × List Bool => family pair.1 pair.2)
      (encPair encBits encBits) encBits) :
    (prfMAC family hpoly).OneTimeSUFCMA ↔ (prfMAC family hpoly).OneTimeEUFCMA :=
  (prfMAC family hpoly).oneTimeSUFCMA_iff_oneTimeEUFCMA_of_unique_tag (unique_tag_prfMAC hpoly)

/-- Running `macToPrfDistinguisher adversary` in `prfRealGame id family` produces the exact same
Boolean distribution as the strong SUF-CMA experiment for `prfMAC family`. -/
theorem eval_prfRealGame_macToPrfDistinguisher_eq_sufCmaGame
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair : List Bool × List Bool => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (adversary : Forger) (n : ℕ) :
    ProbComp.eval (prfRealGame id family (macToPrfDistinguisher adversary) n) =
      ProbComp.eval ((prfMAC family hpoly).sufCmaGame adversary n) := by
  rw [eval_sufCmaGame_prfMAC hpoly adversary n]
  exact eval_prfRealGame_macToPrfDistinguisher hpoly hlen adversary n

/-- **Quantitative PRF-to-MAC forgery bound** [Boneh and Shoup, Theorem 6.2][BonehShoup2023]:
for every adaptive MAC forger `adversary` and every security parameter `n`, the EUF-CMA forgery
probability against `prfMAC family` is at most the PRF distinguishing advantage of
`macToPrfDistinguisher adversary` plus `1 / 2 ^ n`. -/
theorem succProbability_eufCmaGame_prfMAC_le
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair : List Bool × List Bool => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval ((prfMAC family hpoly).eufCmaGame adversary n)) ≤
      Game.advantage
        (ProbComp.eval (prfRealGame id family (macToPrfDistinguisher adversary) n))
        (ProbComp.eval (prfIdealGame id id (macToPrfDistinguisher adversary) n)) +
      (1 : ℝ≥0) / 2 ^ n := by
  rw [← eval_prfRealGame_macToPrfDistinguisher hpoly hlen adversary n]
  have htri := Game.advantage_triangle
    (ProbComp.eval (prfRealGame id family (macToPrfDistinguisher adversary) n))
    (ProbComp.eval (prfIdealGame id id (macToPrfDistinguisher adversary) n))
    (PMF.pure false)
  simp only [Game.advantage_pure_false] at htri
  exact htri.trans (add_le_add_right
    (succProbability_prfIdealGame_macToPrfDistinguisher_le adversary n) _)

/-- **Quantitative PRF-to-SUF-CMA forgery bound** [Boneh and Shoup, Theorem 6.2][BonehShoup2023]:
for every adaptive MAC forger `adversary` and every security parameter `n`, the strong SUF-CMA
forgery probability against `prfMAC family` is at most the PRF distinguishing advantage of
`macToPrfDistinguisher adversary` plus `1 / 2 ^ n`. -/
theorem succProbability_sufCmaGame_prfMAC_le
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair : List Bool × List Bool => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval ((prfMAC family hpoly).sufCmaGame adversary n)) ≤
      Game.advantage
        (ProbComp.eval (prfRealGame id family (macToPrfDistinguisher adversary) n))
        (ProbComp.eval (prfIdealGame id id (macToPrfDistinguisher adversary) n)) +
      (1 : ℝ≥0) / 2 ^ n := by
  rw [eval_sufCmaGame_prfMAC hpoly adversary n]
  exact succProbability_eufCmaGame_prfMAC_le hpoly hlen adversary n

/-- **PRF-to-MAC security theorem** [Boneh and Shoup, Theorem 6.2][BonehShoup2023]:
every uniform `PseudorandomFunction` yields an `EUFCMA`-secure `MACScheme`. -/
theorem PseudorandomFunction.eufCma_prfMAC
    {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family) :
    (prfMAC family hprf.polyTime).EUFCMA := by
  apply MACScheme.EUFCMA.of_negligible
  intro adversary hadversary
  have hdist := hprf.secure (macToPrfDistinguisher adversary)
    (isOraclePPT_macToPrfDistinguisher hadversary)
  negligible using succProbability_eufCmaGame_prfMAC_le hprf.polyTime hprf.length_eq adversary

/-- **PRF-to-SUF-CMA security theorem** [Boneh and Shoup, Theorem 6.2][BonehShoup2023]:
every uniform `PseudorandomFunction` yields a strongly unforgeable (`SUFCMA`) `MACScheme`. -/
theorem PseudorandomFunction.sufCma_prfMAC
    {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family) :
    (prfMAC family hprf.polyTime).SUFCMA :=
  (sufCma_prfMAC_iff_eufCma hprf.polyTime).mpr hprf.eufCma_prfMAC

/-- Every uniform `PseudorandomFunction` also yields a `OneTimeEUFCMA`-secure `MACScheme`. -/
theorem PseudorandomFunction.oneTimeEUFCMA_prfMAC
    {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family) :
    (prfMAC family hprf.polyTime).OneTimeEUFCMA :=
  hprf.eufCma_prfMAC.oneTimeEUFCMA

/-- Every uniform `PseudorandomFunction` also yields a strongly one-time unforgeable
(`OneTimeSUFCMA`) `MACScheme`. -/
theorem PseudorandomFunction.oneTimeSUFCMA_prfMAC
    {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family) :
    (prfMAC family hprf.polyTime).OneTimeSUFCMA :=
  hprf.sufCma_prfMAC.oneTimeSUFCMA

/-! ### Nonce-based message authentication codes (`NonceMACScheme`, Boneh–Shoup Section 7.5) -/

/-- Nonce-tagged message `((msg, nonce), tag)`, the output of a nonce-based MAC forger and an
entry of the signing oracle's log: the message, the nonce and the tag as bit words. The pair
`(msg, nonce)` is framed, and within it the message. -/
abbrev encNonceTaggedMessage : (List Bool × List Bool) × List Bool ↪ List Bool :=
  encPair (encPair encBits encBits) encBits

/-- An adaptive nonce-based MAC forger receives a unary security parameter and an auxiliary word,
queries a nonce-respecting tagging oracle on encoded `(message, nonce)` pairs
(`encPair encBits encBits (msg, nonce)`), and outputs a candidate `((message, nonce), tag)` triple
([Boneh and Shoup, Section 7.5, Attack Game 7.4][BonehShoup2023]). -/
abbrev NonceMACForger :=
  ℕ → List Bool → WordOracleComp Unit ((List Bool × List Bool) × List Bool)

/-- A uniform symmetric nonce-based message authentication code (`NonceMACScheme`) on `msgLen n`-bit
messages and `nonceLen n`-bit nonces at security parameter `n` (both defaulting to `n`), with plain
polynomial-time length schedules, strict polynomial-time key generation and tag generation,
deterministic polynomial-time verification, and perfect completeness on supported keys,
`msgLen n`-bit messages, `nonceLen n`-bit nonces, and tags
([Boneh and Shoup, Section 7.5, Attack Game 7.4][BonehShoup2023]). -/
structure NonceMACScheme where
  /-- Message length authenticated at unary security parameter `n` (defaults to `n`). -/
  msgLen : ℕ → ℕ := fun n => n
  /-- The message-length schedule is computable in plain polynomial time in unary. -/
  msgLen_polyTime : ComputableInPolyTime msgLen encUnary encUnary := by
    exact ComputableInPolyTime.id'
  /-- Nonce length required at unary security parameter `n` (defaults to `n`). -/
  nonceLen : ℕ → ℕ := fun n => n
  /-- The nonce-length schedule is computable in plain polynomial time in unary. -/
  nonceLen_polyTime : ComputableInPolyTime nonceLen encUnary encUnary := by
    exact ComputableInPolyTime.id'
  /-- Sample a secret MAC key `sk` at unary security parameter `n`. -/
  keyGen : ℕ → ProbComp (List Bool)
  /-- Compute a MAC tag on message `msg` and nonce `nonce` using the secret key `sk`. -/
  sign : List Bool → List Bool → List Bool → ProbComp (List Bool)
  /-- Deterministically verify a candidate `tag` on `(msg, nonce)` under secret key `sk`. -/
  verify : List Bool → List Bool → List Bool → List Bool → Bool
  /-- Key generation is uniformly strict PPT in the unary security parameter. -/
  keyGen_ppt : IsPPTOn encUnary encBits keyGen
  /-- Tag generation is uniformly strict PPT in the encoded `(sk, msg, nonce)`. -/
  sign_ppt : IsPPTOn encBitsTriple encBits (fun p => sign p.1 p.2.1 p.2.2)
  /-- Verification is computable in plain polynomial time on `(sk, msg, nonce, tag)`. -/
  verify_polyTime : ComputableInPolyTime
    (fun p : List Bool × List Bool × List Bool × List Bool => verify p.1 p.2.1 p.2.2.1 p.2.2.2)
    (encPair encBits encBitsTriple) encBool
  /-- Every tag produced by `sign` on a `msgLen n`-bit message and `nonceLen n`-bit nonce under a
  supported secret key at security parameter `n` is accepted by `verify`. -/
  verify_sign : ∀ n sk, sk ∈ (ProbComp.eval (keyGen n)).support →
    ∀ msg, msg.length = msgLen n →
    ∀ nonce, nonce.length = nonceLen n →
    ∀ tag, tag ∈ (ProbComp.eval (sign sk msg nonce)).support →
    verify sk msg nonce tag = true

namespace NonceMACScheme

attribute [program_certificate]
  msgLen_polyTime nonceLen_polyTime keyGen_ppt sign_ppt verify_polyTime

/-- Composing `M.msgLen` with a plain polynomial-time unary parameter function is plain
polynomial-time. -/
@[program_certificate]
theorem computableInPolyTime_msgLen_comp (M : NonceMACScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} (hn : ComputableInPolyTime n encIn encUnary) :
    ComputableInPolyTime (fun a => M.msgLen (n a)) encIn encUnary :=
  M.msgLen_polyTime.comp hn

/-- Composing `M.nonceLen` with a plain polynomial-time unary parameter function is plain
polynomial-time. -/
@[program_certificate]
theorem computableInPolyTime_nonceLen_comp (M : NonceMACScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} (hn : ComputableInPolyTime n encIn encUnary) :
    ComputableInPolyTime (fun a => M.nonceLen (n a)) encIn encUnary :=
  M.nonceLen_polyTime.comp hn

/-- Composing `M.keyGen` with a plain polynomial-time unary parameter function is strict PPT. -/
@[program_certificate]
theorem isPPTOn_keyGen_comp (M : NonceMACScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} (hn : ComputableInPolyTime n encIn encUnary) :
    IsPPTOn encIn encBits (fun a => M.keyGen (n a)) :=
  M.keyGen_ppt.preprocess hn

/-- Composing `M.sign` with plain polynomial-time key, message, and nonce selectors is strict
PPT. -/
@[program_certificate]
theorem isPPTOn_sign_comp (M : NonceMACScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {sk msg nonce : γ → List Bool}
    (hsk : ComputableInPolyTime sk encIn encBits)
    (hmsg : ComputableInPolyTime msg encIn encBits)
    (hnonce : ComputableInPolyTime nonce encIn encBits) :
    IsPPTOn encIn encBits (fun a => M.sign (sk a) (msg a) (nonce a)) :=
  M.sign_ppt.preprocess (hsk.prod (hmsg.prod hnonce))

/-- Composing `M.verify` with plain polynomial-time key, message, nonce, and tag selectors is plain
polynomial-time. -/
@[program_certificate]
theorem computableInPolyTime_verify_comp (M : NonceMACScheme)
    {γ : Type} {encIn : γ ↪ List Bool} {sk msg nonce tag : γ → List Bool}
    (hsk : ComputableInPolyTime sk encIn encBits)
    (hmsg : ComputableInPolyTime msg encIn encBits)
    (hnonce : ComputableInPolyTime nonce encIn encBits)
    (htag : ComputableInPolyTime tag encIn encBits) :
    ComputableInPolyTime
      (fun a => M.verify (sk a) (msg a) (nonce a) (tag a)) encIn encBool :=
  M.verify_polyTime.comp (hsk.prod (hmsg.prod (hnonce.prod htag)))

/-- Stateful nonce-based MAC tagging oracle that decodes `(msg, nonce)` from the framed query word
`request.2`, tags `(msg, nonce)` under `sk`, and prepends the returned `((msg, nonce), tag)` triple
to the transcript ([Boneh and Shoup, Section 7.5, Attack Game 7.4][BonehShoup2023]). -/
noncomputable def signingPairOracle (M : NonceMACScheme) (sk : List Bool)
    (request : Unit × List Bool) :
    StateT (List ((List Bool × List Bool) × List Bool)) ProbComp (List Bool) :=
  fun queriedTriples => do
    let msg := unframe request.2
    let nonce := dropFrame request.2
    let tag ← M.sign sk msg nonce
    return (tag, ((msg, nonce), tag) :: queriedTriples)

/-- The strong nonce-based MAC SUF-CMA experiment
([Boneh and Shoup, Section 7.5, Attack Game 7.4][BonehShoup2023]): sample `sk ← M.keyGen n`, run
the adaptive forger on `(n, [])` with oracle access to `M.signingPairOracle sk`, and accept when:
1. the candidate message has length `M.msgLen n` and the candidate nonce has length `M.nonceLen n`,
2. all nonces queried during the signing phase are pairwise distinct
   (`decide (out.2.map (fun ⟨⟨_, qnonce⟩, _⟩ => qnonce)).Nodup`),
3. the candidate `((msg, nonce), tag)` triple was never returned by the tagging oracle
   (`!out.2.contains out.1`), and
4. `M.verify sk msg nonce tag = true`. -/
noncomputable def sufCmaGame (M : NonceMACScheme) (adversary : NonceMACForger) (n : ℕ) :
    ProbComp Bool := do
  let sk ← M.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (M.signingPairOracle sk)) (adversary n [])).run []
  let ((msg, nonce), tag) := out.1
  return (msg.length == M.msgLen n) && (nonce.length == M.nonceLen n) &&
    decide (out.2.map (fun ⟨⟨_, qnonce⟩, _⟩ => qnonce)).Nodup && !out.2.contains out.1 &&
    M.verify sk msg nonce tag

/-- The fresh-message nonce-based MAC EUF-CMA experiment: identical to `sufCmaGame` except that the
candidate message `msg` must never have been queried during the signing phase
(`!(out.2.map (fun ⟨⟨qmsg, _⟩, _⟩ => qmsg)).contains msg`). -/
noncomputable def eufCmaGame (M : NonceMACScheme) (adversary : NonceMACForger) (n : ℕ) :
    ProbComp Bool := do
  let sk ← M.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (M.signingPairOracle sk)) (adversary n [])).run []
  let ((msg, nonce), tag) := out.1
  return (msg.length == M.msgLen n) && (nonce.length == M.nonceLen n) &&
    decide (out.2.map (fun ⟨⟨_, qnonce⟩, _⟩ => qnonce)).Nodup &&
    !(out.2.map (fun ⟨⟨qmsg, _⟩, _⟩ => qmsg)).contains msg &&
    M.verify sk msg nonce tag

/-- Running an oracle-PPT nonce-MAC forger against `signingPairOracle` is uniformly strict PPT in
the unary security parameter and secret key. -/
@[program_certificate]
theorem isPPTOn_run_signingPairOracle (M : NonceMACScheme) {adversary : NonceMACForger}
    (hadversary : IsOraclePPT encNonceTaggedMessage adversary) :
    IsPPTOn (encPair encUnary encBits)
      (encPair encNonceTaggedMessage (encList encNonceTaggedMessage))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (M.signingPairOracle caller.2)) (adversary caller.1 [])).run []) := by
  obtain ⟨c, d, hlen⟩ := M.sign_ppt.length_le
  have hhandler : IsPPTOn
      (encPair (encPair encUnary encBits)
        (encPair (encPair (encFinite Unit) encBits)
          (encList (encPair (encPair encBits encBits) encBits))))
      (encPair encBits (encList (encPair (encPair encBits encBits) encBits)))
      (fun pair : (ℕ × List Bool) ×
          ((Unit × List Bool) × List ((List Bool × List Bool) × List Bool)) =>
        M.signingPairOracle pair.1.2 pair.2.1 pair.2.2) := by
    unfold signingPairOracle
    exact (M.isPPTOn_sign_comp (by fun_prop) (by fun_prop) (by fun_prop)).bind_with
      (ComputableInPolyTime.isPPTOn (by fun_prop))
  apply hadversary.run_interpret_preprocess
    (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
    (initial := fun _ => ([] : List ((List Bool × List Bool) × List Bool)))
    (resources := fun caller query =>
      2 * (c * (2 * caller.2.length + query.length + 3) ^ d) + 4 * query.length + 8)
    (by fun_prop) hhandler (ComputableInPolyTime.const [])
    (fun _ _ => True) (fun _ => trivial) (by fun_prop)
  intro caller request queriedTriples _ result hresult
  simp only [signingPairOracle, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
  obtain ⟨tag, htag, rfl⟩ := hresult
  have htagLen := hlen (caller.2, unframe request.2, dropFrame request.2) tag htag
  simp only [encBits_apply, length_encPair] at htagLen
  have hframe := length_unframe_add_dropFrame_le request.2
  have hbase : 2 * caller.2.length + 1 +
      (2 * (unframe request.2).length + 1 + (dropFrame request.2).length) + 1 ≤
      2 * caller.2.length + request.2.length + 3 := by omega
  have hpow : c * (2 * caller.2.length + 1 +
      (2 * (unframe request.2).length + 1 + (dropFrame request.2).length) + 1) ^ d ≤
      c * (2 * caller.2.length + request.2.length + 3) ^ d :=
    Nat.mul_le_mul_left c (Nat.pow_le_pow_left hbase d)
  have htag_le : tag.length ≤ c * (2 * caller.2.length + request.2.length + 3) ^ d :=
    htagLen.trans hpow
  refine ⟨trivial, by dsimp only; omega, ?_⟩
  enc_len

/-- Run the complete nonce-based MAC SUF-CMA experiment on its unary security parameter for any
oracle-PPT forger. -/
@[program_certificate]
theorem isPPTOn_sufCmaGame (M : NonceMACScheme) {adversary : NonceMACForger}
    (hadversary : IsOraclePPT encNonceTaggedMessage adversary) :
    IsPPTOn encUnary encBool (M.sufCmaGame adversary) :=
  M.keyGen_ppt.bind_with ((M.isPPTOn_run_signingPairOracle hadversary).bind_with
    (ComputableInPolyTime.isPPTOn (by
      simp only [List.contains_eq_mem]
      fun_prop)))

/-- The nonce-based MAC SUF-CMA experiment is uniformly strict PPT, independently of unused
auxiliary input. -/
@[program_certificate]
theorem isPPT_sufCmaGame (M : NonceMACScheme) {adversary : NonceMACForger}
    (hadversary : IsOraclePPT encNonceTaggedMessage adversary) :
    IsPPT encBool (fun n _ => M.sufCmaGame adversary n) :=
  ((M.isPPTOn_sufCmaGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Run the complete nonce-based MAC EUF-CMA experiment on its unary security parameter for any
oracle-PPT forger. -/
@[program_certificate]
theorem isPPTOn_eufCmaGame (M : NonceMACScheme) {adversary : NonceMACForger}
    (hadversary : IsOraclePPT encNonceTaggedMessage adversary) :
    IsPPTOn encUnary encBool (M.eufCmaGame adversary) :=
  M.keyGen_ppt.bind_with ((M.isPPTOn_run_signingPairOracle hadversary).bind_with
    (ComputableInPolyTime.isPPTOn (by
      simp only [List.contains_eq_mem]
      fun_prop)))

/-- The nonce-based MAC EUF-CMA experiment is uniformly strict PPT, independently of unused
auxiliary input. -/
@[program_certificate]
theorem isPPT_eufCmaGame (M : NonceMACScheme) {adversary : NonceMACForger}
    (hadversary : IsOraclePPT encNonceTaggedMessage adversary) :
    IsPPT encBool (fun n _ => M.eufCmaGame adversary n) :=
  ((M.isPPTOn_eufCmaGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Strong existential unforgeability under nonce-respecting adaptive chosen-message attack
(`SUFCMA`) for a `NonceMACScheme` against uniform strict oracle-PPT adversaries
([Boneh and Shoup, Section 7.5, Attack Game 7.4][BonehShoup2023]). A run that repeats a nonce
loses, as the source forbids repeated nonces. The oracle tags messages and nonces of any length,
while a forgery counts only with a `msgLen n`-bit message and a `nonceLen n`-bit nonce; in the
source, queries lie in the message and nonce spaces. -/
def SUFCMA (M : NonceMACScheme) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (M.sufCmaGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT encNonceTaggedMessage)

/-- Strong nonce-based unforgeability gives negligible SUF-CMA forgery probability for every
oracle-PPT forger. -/
theorem SUFCMA.negligible {M : NonceMACScheme} (h : M.SUFCMA)
    (adversary : NonceMACForger)
    (hadversary : IsOraclePPT encNonceTaggedMessage adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (M.sufCmaGame adversary n))) :=
  Game.Indistinguishable.negligible_succProbability h adversary hadversary

/-- Establish nonce-based SUF-CMA security by bounding every oracle-PPT forger's success
probability. -/
theorem SUFCMA.of_negligible {M : NonceMACScheme}
    (h : ∀ adversary, IsOraclePPT encNonceTaggedMessage adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (M.sufCmaGame adversary n)))) :
    M.SUFCMA :=
  Game.Indistinguishable.of_negligible_succProbability h

/-- Fresh-message existential unforgeability under nonce-respecting adaptive chosen-message attack
(`EUFCMA`) for a `NonceMACScheme` against uniform strict oracle-PPT adversaries: [BonehShoup2023],
Attack Game 7.4 and Definition 7.6 (p. 274), with two differences. A forgery counts only on a
message that was never queried, where the source accepts any new triple `(m, t, N)` (`SUFCMA`). The
oracle tags messages and nonces of any length, while a forgery counts only with a `msgLen n`-bit
message and a `nonceLen n`-bit nonce; in the source, queries lie in the message and nonce spaces.
With its weaker forgery condition and its stronger oracle, the notion is incomparable with the
source's; in particular, the source's notion does not imply it. A run that repeats a nonce loses,
as the source forbids repeated nonces. -/
def EUFCMA (M : NonceMACScheme) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (M.eufCmaGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT encNonceTaggedMessage)

/-- Nonce-based EUF-CMA security gives negligible forgery probability for every oracle-PPT
forger. -/
theorem EUFCMA.negligible {M : NonceMACScheme} (h : M.EUFCMA)
    (adversary : NonceMACForger)
    (hadversary : IsOraclePPT encNonceTaggedMessage adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (M.eufCmaGame adversary n))) :=
  Game.Indistinguishable.negligible_succProbability h adversary hadversary

/-- Establish nonce-based EUF-CMA security by bounding every oracle-PPT forger's success
probability. -/
theorem EUFCMA.of_negligible {M : NonceMACScheme}
    (h : ∀ adversary, IsOraclePPT encNonceTaggedMessage adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (M.eufCmaGame adversary n)))) :
    M.EUFCMA :=
  Game.Indistinguishable.of_negligible_succProbability h

/-- **Quantitative EUF-CMA vs. SUF-CMA bound for `NonceMACScheme`**: for every `NonceMACScheme`,
adaptive forger, and security parameter `n`, the fresh-message `eufCmaGame` forgery probability is
at most the strong fresh-triple `sufCmaGame` forgery probability. -/
theorem succProbability_eufCmaGame_le_sufCmaGame (M : NonceMACScheme)
    (adversary : NonceMACForger) (n : ℕ) :
    Game.succProbability (ProbComp.eval (M.eufCmaGame adversary n)) ≤
      Game.succProbability (ProbComp.eval (M.sufCmaGame adversary n)) := by
  apply Game.succProbability_mono
  simp only [eufCmaGame, sufCmaGame, ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_apply_mono_on_support _ _ fun sk _ => ?_
  refine PMF.bind_apply_mono_on_support _ _ fun ⟨⟨⟨msg, nonce⟩, tag⟩, tr⟩ _ => ?_
  dsimp only
  cases hpair : tr.contains ((msg, nonce), tag)
  · cases (tr.map (fun e => e.1.1)).contains msg <;>
      cases (msg.length == M.msgLen n) && (nonce.length == M.nonceLen n) &&
        decide (tr.map (fun e => e.1.2)).Nodup <;>
      cases M.verify sk msg nonce tag <;> simp
  · rw [show (tr.map (fun ⟨⟨qmsg, _⟩, _⟩ => qmsg)).contains msg = true from
        List.contains_iff_mem.mpr
          (List.mem_map_of_mem (f := fun ⟨⟨qmsg, _⟩, _⟩ => qmsg) (List.contains_iff_mem.mp hpair))]

/-- Strong unforgeability (`SUFCMA`) implies fresh-message unforgeability (`EUFCMA`) for every
`NonceMACScheme`. -/
theorem SUFCMA.eufCma {M : NonceMACScheme} (h : M.SUFCMA) : M.EUFCMA :=
  h.of_succProbability_le fun adversary _ => M.succProbability_eufCmaGame_le_sufCmaGame adversary

private theorem mem_support_signingPairOracle (M : NonceMACScheme) (sk : List Bool)
    (prog : WordOracleComp Unit ((List Bool × List Bool) × List Bool))
    (result : (List Bool × List Bool) × List Bool)
    (queriedTriples : List ((List Bool × List Bool) × List Bool))
    (hmem : (result, queriedTriples) ∈ (ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (M.signingPairOracle sk)) prog).run [])).support) :
    ∀ triple ∈ queriedTriples,
      triple.2 ∈ (ProbComp.eval (M.sign sk triple.1.1 triple.1.2)).support := by
  rw [ProbOracleComp.eval_run_interpret_eq_runWith] at hmem
  refine ProbOracleComp.runWith_invariant
    (fun q s => ProbComp.eval (M.signingPairOracle sk q s))
    (fun s => ∀ triple ∈ s,
      triple.2 ∈ (ProbComp.eval (M.sign sk triple.1.1 triple.1.2)).support)
    ?_ prog [] (by simp) result queriedTriples hmem
  intro ⟨⟨⟩, raw⟩ s hs a s' hstep triple htriple
  simp only [signingPairOracle, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hstep
  obtain ⟨tag, htag, ⟨⟩⟩ := hstep
  rcases List.mem_cons.mp htriple with rfl | htail
  · exact htag
  · exact hs triple htail

/-- For any `NonceMACScheme` whose valid tags on `M.msgLen n`-bit messages and `M.nonceLen n`-bit
nonces under supported secret keys agree with every tag in the support of `M.sign`, strong
triple-freshness (`!out.2.contains out.1`) in `sufCmaGame` is identical to `(msg, nonce)`-pair
freshness (`!(out.2.map Prod.fst).contains pair`). -/
theorem eval_sufCmaGame_eq_freshPair_of_unique_tag (M : NonceMACScheme)
    (huniq : ∀ n sk, sk ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = M.msgLen n →
      ∀ nonce, nonce.length = M.nonceLen n → ∀ tag tag',
      M.verify sk msg nonce tag = true →
      tag' ∈ (ProbComp.eval (M.sign sk msg nonce)).support → tag' = tag)
    (adversary : NonceMACForger) (n : ℕ) :
    ProbComp.eval (M.sufCmaGame adversary n) =
      ProbComp.eval (do
        let sk ← M.keyGen n
        let out ← (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (M.signingPairOracle sk)) (adversary n [])).run []
        let (pair, tag) := out.1
        let (msg, nonce) := pair
        return (msg.length == M.msgLen n) && (nonce.length == M.nonceLen n) &&
          decide (out.2.map (fun ⟨⟨_, qnonce⟩, _⟩ => qnonce)).Nodup &&
          !(out.2.map Prod.fst).contains pair &&
          M.verify sk msg nonce tag) := by
  simp only [sufCmaGame, ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_congr_on_support _ _ _ fun sk hsk => ?_
  refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨⟨msg, nonce⟩, tag⟩, queriedTriples⟩ hout => ?_
  have hinv := M.mem_support_signingPairOracle sk (adversary n [])
    ((msg, nonce), tag) queriedTriples hout
  congr 1
  cases hpre : ((msg.length == M.msgLen n) && (nonce.length == M.nonceLen n) &&
      decide (queriedTriples.map (fun ⟨⟨_, qnonce⟩, _⟩ => qnonce)).Nodup)
  · simp
  · cases hver : M.verify sk msg nonce tag
    · simp
    · simp only [Bool.and_eq_true, beq_iff_eq] at hpre
      have hmem_iff : ((msg, nonce), tag) ∈ queriedTriples ↔
          (msg, nonce) ∈ queriedTriples.map Prod.fst :=
        ⟨fun h => List.mem_map_of_mem h, fun h => by
          obtain ⟨⟨⟨_, _⟩, qtag⟩, hmemTriple, ⟨⟩⟩ := List.mem_map.mp h
          exact huniq n sk hsk msg hpre.1.1 nonce hpre.1.2 tag qtag hver
            (hinv _ hmemTriple) ▸ hmemTriple⟩
      simp [List.contains_eq_mem, decide_eq_decide.mpr hmem_iff]

end NonceMACScheme

end Cslib.Crypto
