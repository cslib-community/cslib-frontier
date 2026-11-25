/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Oracle.CachedSampler
public import CslibFrontier.Crypto.Computational.PseudorandomFunction
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic
import CslibFrontier.Probability.Product

/-!
# Word PRF games on a restricted input domain

Each game uses a parameter-indexed validity predicate. The real oracle evaluates valid queries
under a uniform key. The ideal oracle caches uniform fixed-width replies to valid queries.
Both return the empty word for an invalid query.

## Main definitions

* `Cslib.Crypto.prfRealGameOn`, `Cslib.Crypto.prfIdealGameOn`: the two games.
* `Cslib.Crypto.PseudorandomFunctionOn`: strict oracle-PPT indistinguishability with efficient
  evaluation and a declared reply length.

## Main results

* `Cslib.Crypto.eval_prfRealGameOn_length_eq`, `Cslib.Crypto.eval_prfIdealGameOn_length_eq`:
  a fixed-length domain recovers the existing fixed-length real and ideal game laws.
* `Cslib.Crypto.eval_prfIdealGameOn_eq_eager_of_codec`: a finite query codec identifies the
  cached ideal oracle with an eager table.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Attack Game 4.2 (printed p. 132) and Definitions 4.2 and 4.4.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- Memoize uniform `outLen`-bit samples on valid queries, rejecting malformed words without
altering the cache. -/
noncomputable abbrev cachedRandomFunctionOracle (valid : List Bool → Bool) (outLen : ℕ) :
    List Bool → StateT (List (List Bool × List Bool)) ProbComp (List Bool) :=
  cachedSamplerOracle valid (BitString.sampleList outLen)

/-- Keyed word oracle restricted to the message predicate `valid`: valid queries are evaluated
under `key`, and invalid queries receive `[]`. -/
@[expose]
def prfOracleOn (valid : List Bool → Bool) (family : List Bool → List Bool → List Bool)
    (key query : List Bool) : List Bool :=
  if valid query then family key query else []

/-- Real PRF experiment on the query domain `valid n` ([BonehShoup2023], Attack Game 4.2,
printed p. 132): sample a uniform `n`-bit key and answer valid queries with `family key` and
invalid queries with `[]`. -/
@[expose]
noncomputable def prfRealGameOn (valid : ℕ → List Bool → Bool)
    (family : List Bool → List Bool → List Bool)
    (adversary : OracleDistinguisher) (n : ℕ) : ProbComp Bool := do
  let key ← BitString.sampleList n
  (adversary n []).run fun request => pure (prfOracleOn (valid n) family key request.2)

/-- Ideal PRF experiment on the query domain `valid n` with `outLen n`-bit outputs
([BonehShoup2023], Attack Game 4.2, printed p. 132): answer valid queries with consistent lazy
uniform `outLen n`-bit values and invalid queries with `[]`. -/
@[expose]
noncomputable def prfIdealGameOn (valid : ℕ → List Bool → Bool) (outLen : ℕ → ℕ)
    (adversary : OracleDistinguisher) (n : ℕ) : ProbComp Bool :=
  Prod.fst <$> (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (fun request => cachedRandomFunctionOracle (valid n) (outLen n) request.2))
    (adversary n [])).run []

/-- On fixed `inLen n`-bit inputs, `prfRealGameOn` is identical in distribution to `prfRealGame`. -/
theorem eval_prfRealGameOn_length_eq (inLen : ℕ → ℕ)
    (family : List Bool → List Bool → List Bool) (adversary : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (prfRealGameOn (fun m q => q.length == inLen m) family adversary n) =
      ProbComp.eval (prfRealGame inLen family adversary n) := by
  simp only [prfRealGameOn, prfRealGame, prfOracleOn, prfOracle, beq_iff_eq]

/-- For a finite query codec with raw fixed-width replies, the lazy domain-restricted
ideal oracle has the same output law as an eagerly sampled uniform table. -/
theorem eval_prfIdealGameOn_eq_eager_of_codec {Q : Type} [Fintype Q] [DecidableEq Q]
    {valid : List Bool → Bool} {w : ℕ} (codec : OracleCodec Unit Q (fun _ => BitString w))
    (hvalid : ∀ query : List Bool, valid query = (codec.decodeQuery ((), query)).isSome)
    (hreply : ∀ q : Q, codec.encodeReply q = ⟨List.ofFn, List.ofFn_injective⟩)
    (program : WordOracleComp Unit Bool) :
    ProbComp.eval (Prod.fst <$> (OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (fun request => cachedRandomFunctionOracle valid w request.2))
      program).run []) =
    (PMF.uniformOfFintype (Q → BitString w)).bind fun table =>
      ProbComp.eval ((codec.adapt program).run fun q => pure (table q)) := by
  let keyMap : Q ↪ List Bool :=
    ⟨fun q => (codec.encodeQuery q).2, fun q₁ q₂ h =>
      codec.encodeQuery_injective (Prod.ext (Subsingleton.elim _ _) h)⟩
  let adapter : List Bool → ProbOracleComp (fun _ : Q => List Bool) (List Bool) :=
    fun query => match codec.decodeQuery ((), query) with
      | some q => ProbOracleComp.query q
      | none => pure []
  have h := RandomOracle.interpret_prob_eq_memoize_map
    keyMap List.ofFn
    (fun _ => PMF.uniformOfFintype (BitString w)) (fun _ => BitString.uniformList w)
    (fun _ => rfl)
    (ProbOracleComp.simulate (fun request : Unit × List Bool => adapter request.2) program)
  have hstep (query : List Bool) : OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (fun key => memoize (fun _ => BitString.uniformList w) (keyMap key)))
        (adapter query) =
      fun cache => ProbComp.eval (cachedRandomFunctionOracle valid w query cache) := by
    funext cache
    rw [cachedRandomFunctionOracle, cachedSamplerOracle, hvalid query]
    cases hdec : codec.decodeQuery ((), query) with
    | none =>
      simp only [adapter, hdec, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        OracleComp.interpret_pure, ProbComp.eval_pure]
      rfl
    | some q =>
      have henc : (codec.encodeQuery q).2 = query :=
        congrArg Prod.snd ((codec.decodeQuery_eq_some_iff ((), query) q).mp hdec)
      simp only [adapter, hdec, Option.isSome_some, ↓reduceIte, ProbOracleComp.interpret_query,
        ProbComp.eval_memoize, BitString.eval_sampleList]
      change memoize (fun _ => BitString.uniformList w) (codec.encodeQuery q).2 cache = _
      rw [henc]
  have heager (table : Q → BitString w) (request : Unit × List Bool) : OracleComp.interpret
      (OracleComp.sumHandler ProbComp.unifOracle (fun key => PMF.pure (List.ofFn (table key))))
        (adapter request.2) =
      codec.wordOracle (fun q => PMF.pure (table q)) request := by
    rcases request with ⟨⟨⟩, query⟩
    rw [OracleCodec.wordOracle]
    cases hdec : codec.decodeQuery ((), query) with
    | none => simp [adapter, hdec]
    | some q =>
      simp [adapter, hdec, hreply q]
  rw [ProbComp.eval_map, ProbOracleComp.eval_run_interpret]
  have hsymm := h.symm
  simpa only [ProbOracleComp.interpret_simulate, hstep, heager, PMF.pi_uniformOfFintype,
    PMF.monad_bind_eq_bind, ProbOracleComp.eval_run, ProbComp.eval_pure,
    OracleCodec.interpret_adapt] using hsymm

/-- On fixed `inLen n`-bit inputs, `prfIdealGameOn` is identical in distribution to
`prfIdealGame`. -/
theorem eval_prfIdealGameOn_length_eq (inLen outLen : ℕ → ℕ) (adversary : OracleDistinguisher)
    (n : ℕ) :
    ProbComp.eval (prfIdealGameOn (fun m q => q.length == inLen m) outLen adversary n) =
      ProbComp.eval (prfIdealGame inLen outLen adversary n) := by
  have heq := eval_prfIdealGameOn_eq_eager_of_codec
    (valid := fun q => q.length == inLen n)
    (OracleCodec.bitStrings (inLen n) (outLen n))
    (fun query => by
      by_cases hq : query.length = inLen n <;> simp [OracleCodec.bitStrings, hq])
    (fun _ => rfl)
    (adversary n [])
  rw [prfIdealGameOn, heq]
  simp only [prfIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform, ProbOracleComp.eval_run,
    ProbComp.eval_pure, ← PMF.monad_pure_eq_pure, OracleCodec.interpret_adapt,
    wordOracle_bitStrings]

/-- Uniform computational pseudorandom function over the parameter-indexed query domain `valid` with
`n`-bit keys and `outLen n`-bit outputs ([BonehShoup2023], Attack Game 4.2 and Definitions 4.2 and
4.4, printed pp. 132–133 and 139–141). -/
structure PseudorandomFunctionOn (valid : ℕ → List Bool → Bool) (outLen : ℕ → ℕ)
    (family : List Bool → List Bool → List Bool) : Prop where
  /-- Deterministic polynomial-time evaluation from `(key, query)`. -/
  polyTime : ComputableInPolyTime (fun pair => family pair.1 pair.2)
    (encPair encBits encBits) encBits
  /-- Valid queries under a key receive `outLen key.length`-bit answers. -/
  length_eq : ∀ key query, valid key.length query = true →
    (family key query).length = outLen key.length
  /-- Indistinguishability of the real and ideal domain-restricted experiments. -/
  secure : Game.Indistinguishable
    (fun adversary n => ProbComp.eval (prfRealGameOn valid family adversary n))
    (fun adversary n => ProbComp.eval (prfIdealGameOn valid outLen adversary n))
    (IsOraclePPT encBool)

end Cslib.Crypto
