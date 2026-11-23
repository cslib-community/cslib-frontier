/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Computability.Probabilistic.Oracle.Codec
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Languages.Probabilistic.BitString
public import CslibFrontier.Languages.Probabilistic.Oracle.Run
public import CslibFrontier.Languages.Probabilistic.RandomOracle
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic

/-!
# Uniform computational pseudorandom functions

A keyed family has `n`-bit keys, and its valid queries and answers have `inLen n` and `outLen n`
bits. An adversary receives the unary security parameter, independent private randomness and
adaptive access to one word channel. The real game samples one key; the ideal game samples one
whole function and reuses it across calls. Both games invoke the adversary with empty auxiliary
input and reject malformed queries with the empty word. The table is a semantic specification;
`prfIdealGame_eq_lazy` samples it lazily, and `RandomOracle` certifies a lazy realization of the
length-preserving game for oracle-PPT adversaries.

The keyed evaluator has a uniform deterministic TM certificate on the encoded key/query pair.
Admissible adversaries satisfy `IsOraclePPT`, charging ordinary computation and request writing,
with one machine and polynomial for all parameters and auxiliary inputs.

`PseudorandomFunction` is the length-preserving case `inLen = outLen = id`, in which keys, valid
queries and answers all have `n` bits.

## Main definitions

* `Cslib.Crypto.OracleDistinguisher`: a parameterized randomized adaptive oracle test.
* `Cslib.Crypto.prfRealGame`, `.prfIdealGame`: the keyed and random-function experiments.
* `Cslib.Crypto.PseudorandomFunctionOver`: efficient evaluation, lengths and adaptive security.
* `Cslib.Crypto.PseudorandomFunction`: its length-preserving case.

## Main results

* `Cslib.Crypto.computableInPolyTime_prfOracle_comp`: plain polynomial-time composition rule for
  `prfOracle`.
* `Cslib.Crypto.wordOracle_bitStrings`, `Cslib.Crypto.wordOracle_bitStrings_answer`: agreement of
  `OracleCodec.bitStrings` with `randomFunctionOracle` and `lazyRandomFunctionOracle`.
* `Cslib.Crypto.prfIdealGame_eq_lazy`: an exact lazy implementation of the ideal experiment.
* `Cslib.Crypto.PseudorandomFunctionOver.outLen_polyTime`: computing the unary output width
  from the unary input width schedule.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Chapter 4.
* [O. Goldreich, S. Goldwasser, S. Micali, *How to Construct Random Functions*][GGM1986].

Adapted from Crypto/Computational/PseudorandomFunction.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the shared typed interpreter and word channel.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- An adaptive test with a unary parameter, an auxiliary word and one external word channel. -/
abbrev OracleDistinguisher := ℕ → List Bool → WordOracleComp Unit Bool

/-- A keyed oracle rejects queries outside the declared domain. -/
def prfOracle (family : List Bool → List Bool → List Bool) (n : ℕ) (key query : List Bool) :
    List Bool := if query.length = n then family key query else []

/-- Evaluating `prfOracle family (n a) (key a) (query a)` is computable in plain polynomial time
whenever `family`, the unary domain width `n`, `key`, and `query` are computable in plain
polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_prfOracle_comp {γ : Type} {encIn : γ ↪ List Bool}
    {family : List Bool → List Bool → List Bool}
    (hfamily : ComputableInPolyTime
      (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits)
    {n : γ → ℕ} {key query : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hkey : ComputableInPolyTime key encIn encBits)
    (hquery : ComputableInPolyTime query encIn encBits) :
    ComputableInPolyTime
      (fun a => prfOracle family (n a) (key a) (query a))
      encIn encBits := by
  have hfam : ComputableInPolyTime (fun a => family (key a) (query a)) encIn encBits :=
    hfamily.comp (hkey.prod hquery)
  have heq : (fun a => prfOracle family (n a) (key a) (query a)) =
      (fun a => if (query a).length == n a then family (key a) (query a) else []) := by
    funext a
    simp [prfOracle]
  rw [heq]
  fun_prop

/-- Read a fixed random table on `n`-bit inputs, rejecting malformed words before interpreting
their bits. -/
def randomFunctionOracle (n : ℕ) {w : ℕ} (table : BitString n → BitString w)
    (query : List Bool) : List Bool :=
  if query.length = n then List.ofFn (table (BitString.ofList n query)) else []

/-- Adapt a valid word to the finite domain. Malformed words make no external call; this is
`(OracleCodec.bitStrings n w).wordOracle ProbOracleComp.query` on `()`, `query`. -/
def randomFunctionQuery (n : ℕ) {w : ℕ} (query : List Bool) :
    ProbOracleComp (fun _ : BitString n => BitString w) (List Bool) :=
  if query.length = n then List.ofFn <$> ProbOracleComp.query (BitString.ofList n query)
  else pure []

/-- `OracleCodec.bitStrings n w` presents `randomFunctionOracle n table` on the unit word channel:
an `n`-bit request is answered by the bits of `table` and any other request by `[]`. -/
theorem wordOracle_bitStrings {m : Type → Type*} [Monad m] [LawfulMonad m] (n w : ℕ)
    (table : BitString n → BitString w) :
    (OracleCodec.bitStrings n w).wordOracle (fun bits => (pure (table bits) : m (BitString w))) =
      fun request => pure (randomFunctionOracle n table request.2) := by
  funext ⟨⟨⟩, query⟩
  by_cases h : query.length = n <;>
    simp [OracleCodec.wordOracle, OracleCodec.bitStrings, randomFunctionOracle, h]

open Classical in
/-- A semantic random-function cache from `n`-bit to `w`-bit strings, retaining only the
finite-domain answers already used. -/
noncomputable def lazyRandomFunctionOracle (n w : ℕ) (query : List Bool) :
    StateT (RandomOracle.Cache (fun _ : BitString n => BitString w)) PMF (List Bool) :=
  OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
      (RandomOracle.answer (fun _ => PMF.uniformOfFintype (BitString w))))
        (randomFunctionQuery n query)

open Classical in
/-- `OracleCodec.bitStrings n w` lifts `RandomOracle.answer` to `lazyRandomFunctionOracle n w` on
the unit word channel. -/
theorem wordOracle_bitStrings_answer (n w : ℕ) :
    (OracleCodec.bitStrings n w).wordOracle
        (RandomOracle.answer (fun _ : BitString n => PMF.uniformOfFintype (BitString w))) =
      fun request => lazyRandomFunctionOracle n w request.2 := by
  funext ⟨⟨⟩, query⟩
  by_cases h : query.length = n <;>
    simp [OracleCodec.wordOracle, OracleCodec.bitStrings, lazyRandomFunctionOracle,
      randomFunctionQuery, h]

/-- The real experiment of a keyed family with `inLen n`-bit inputs: sample one `n`-bit key and
answer every query of `inLen n` bits with the family under that key, and any other query with the
empty word. -/
noncomputable def prfRealGame (inLen : ℕ → ℕ) (family : List Bool → List Bool → List Bool)
    (adversary : OracleDistinguisher) (n : ℕ) : ProbComp Bool := do
  let key ← BitString.sampleList n
  (adversary n []).run fun request => pure (prfOracle family (inLen n) key request.2)

/-- The ideal experiment with `inLen n`-bit inputs and `outLen n`-bit outputs: sample one uniform
function between them, independently of the adversary's private samples, and answer every query
of `inLen n` bits with its value, and any other query with the empty word. -/
noncomputable def prfIdealGame (inLen outLen : ℕ → ℕ) (adversary : OracleDistinguisher)
    (n : ℕ) : ProbComp Bool := do
  let table ← ProbComp.uniform (BitString (inLen n) → BitString (outLen n))
  (adversary n []).run fun request => pure (randomFunctionOracle (inLen n) table request.2)

/-- The ideal game admits consistent lazy answers to adaptive queries, with private randomness
independent of the table and the same rejection convention for malformed inputs. -/
theorem prfIdealGame_eq_lazy (inLen outLen : ℕ → ℕ) (adversary : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (prfIdealGame inLen outLen adversary n) =
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (fun request => lazyRandomFunctionOracle (inLen n) (outLen n) request.2))
            (adversary n [])).run (fun _ => none)).map Prod.fst := by
  classical
  have h := RandomOracle.uniform_interpret_prob_eq_lazy
    ((OracleCodec.bitStrings (inLen n) (outLen n)).adapt (adversary n []))
  have hpure (table : BitString (inLen n) → BitString (outLen n)) :
      (fun bits => PMF.pure (table bits)) =
        (fun bits => (pure (table bits) : PMF (BitString (outLen n)))) := rfl
  simpa only [prfIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform, ProbOracleComp.eval_run,
    ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, OracleCodec.interpret_adapt,
    OracleCodec.runWith_adapt, ProbOracleComp.runWith_eq_run_interpret,
    hpure, wordOracle_bitStrings, wordOracle_bitStrings_answer] using h

/-- A keyed family with `n`-bit keys, `inLen n`-bit inputs and `outLen n`-bit outputs, evaluated in
plain polynomial time and secure against every uniform adaptive oracle test: [BonehShoup2023],
Attack Game 4.2 and Definition 4.2, pp. 132–133, for a PRF defined over `(K, X, Y)`, read
asymptotically with `K`, `X` and `Y` the words of `n`, `inLen n` and `outLen n` bits. A query of
another length is answered by the empty word in both games, and deterministic polynomial-time
evaluation is part of the notion. `PseudorandomFunction` is the case `inLen = outLen = id`.

The lengths are meant to be polynomially bounded in `n`, as in the book's asymptotic definition
(Definition 4.4, Section 4.4.5, pp. 139–141), whose `X` and `Y` are families of spaces with strings
of polynomially bounded length (Definition 2.9, Section 2.3.2, p. 30). The structure does not
require this, and without it the notion degenerates:

* if `inLen n` grows faster than every polynomial (for example `2 ^ n`), each admitted test
  eventually writes only queries shorter than `inLen n` (`IsOraclePPT.query_bounds`), so both
  games answer all of them with the empty word and `secure` holds for every family: every family
  meeting `polyTime` and `length_eq` qualifies;
* if `outLen n` is not bounded by a polynomial in `n + inLen n`, `polyTime` and `length_eq`
  cannot both hold, because a polynomial-time machine writes polynomially many bits
  (`ComputableInPolyTime.polyBounded_length`), and no family qualifies.

The theorems that use the notion take the bound from their own hypotheses: a `BlockCipher`'s
`blockLen` is computable in polynomial time from unary `n` (`BlockCipher.blockLen_polyTime`);
`indistinguishable_prgFromPRF` and `PseudorandomFunctionOver.toPRG` assume the query points
computable in polynomial time from unary `n`, and the former also `outLen`; and
`MLKEM.indCPA_kpkePRF_of_decisionModuleLWEWith` assumes parameters computable in polynomial time,
with `n`, `k`, `η₁` and `η₂` encoded in unary. -/
structure PseudorandomFunctionOver (inLen outLen : ℕ → ℕ)
    (family : List Bool → List Bool → List Bool) : Prop where
  /-- One deterministic machine evaluates the family from the encoded key and query. -/
  polyTime : ComputableInPolyTime (fun pair => family pair.1 pair.2)
    (encPair encBits encBits) encBits
  /-- Valid queries receive answers of the declared width. -/
  length_eq : ∀ key query, query.length = inLen key.length →
    (family key query).length = outLen key.length
  /-- The real and ideal experiments use the common game-security calculus. -/
  secure : Game.Indistinguishable
    (fun adversary n => ProbComp.eval (prfRealGame inLen family adversary n))
    (fun adversary n => ProbComp.eval (prfIdealGame inLen outLen adversary n))
    (IsOraclePPT encBool)

/-- Evaluate the family at the all-zero key and a valid all-zero query to compute the output width
in unary. -/
theorem PseudorandomFunctionOver.outLen_polyTime {inLen outLen : ℕ → ℕ}
    {family : List Bool → List Bool → List Bool} (h : PseudorandomFunctionOver inLen outLen family)
    (hinLen : ComputableInPolyTime inLen encUnary encUnary) :
    ComputableInPolyTime outLen encUnary encUnary := by
  have hzeros := ComputableInPolyTime.bitsReplicate false
  have heval := h.polyTime.comp (hzeros.prod (hzeros.comp hinLen))
  refine (ComputableInPolyTime.length_bits.comp heval).of_enc_eq fun n => ?_
  have hwidth := h.length_eq (List.replicate n false) (List.replicate (inLen n) false)
    (by simp only [List.length_replicate])
  simpa only [List.length_replicate, Function.comp_def] using congrArg encUnary hwidth.symm

/-- A length-preserving pseudorandom function: `PseudorandomFunctionOver id id`, whose keys, valid
queries and answers all have `n` bits ([BonehShoup2023], Attack Game 4.2 and Definition 4.2,
pp. 132–133, with `K`, `X` and `Y` all the words of `n` bits). Its fields are those of
`PseudorandomFunctionOver`. -/
abbrev PseudorandomFunction (family : List Bool → List Bool → List Bool) : Prop :=
  PseudorandomFunctionOver id id family

end Cslib.Crypto
