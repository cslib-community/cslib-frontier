/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.BitString
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sigma
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Probabilistic.Oracle.CachedSampler
public import CslibFrontier.Crypto.Computational.KeyDerivation.RandomOracle
public import CslibFrontier.Crypto.Game.StatisticalIndistinguishability
public import CslibFrontier.Languages.Probabilistic.Oracle.Codec
public import CslibFrontier.Languages.Probabilistic.Oracle.Substitution
public import CslibFrontier.Languages.Probabilistic.UniformNat.ModIndex
import CslibFrontier.Computability.Interactive.Security.Oracle
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sigma
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.QueryBounds
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.UniformNat.ModIndex
import CslibFrontier.Foundations.Data.BitString.List
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic
import CslibFrontier.Languages.Probabilistic.RandomOracle.QueryHit
import CslibFrontier.Languages.Probabilistic.UniformNat.LowerBound
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.DensityBounds
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.Negligible

/-!
# Computational random-oracle key derivation via lazy simulation

Formalizes the computational form of [BonehShoup2023], Section 8.10.1 (Attack Game 8.3 and its
fourth motivating example, computational unpredictability of a secret source, pp. 325–326) and
Section 8.10.2 (Theorem 8.10, pp. 331–332) over general encoded finite secret families
`S : ℕ → Type`, side-information families `X : ℕ → Type`, and digest/key families `T : ℕ → Type`,
together with the specialization to `BitString (secLen n)` secrets and `BitString (outLen n)` keys.

Whereas `CslibFrontier.Crypto.Computational.KeyDerivation.RandomOracle` states eager-table
(`uniformOfFintype (S → T)`) concrete bounds and an information-theoretic (unbounded-guesser)
asymptotic transfer for arbitrary finite nonempty `S` and `T`, as steps toward Theorem 8.10,
this module constructs the elementary lazy-simulation wrappers `lazyROToListGuess` and
`lazyROToGuess` over associative-list caches (`Cslib.Probability.cachedSamplerOracle`), proves
their uniform strict PPT certificates from a word-oracle distinguisher's `IsOraclePPTOn`
certificate, and derives the asymptotic random-oracle KDF security transfer under the standard
computational unpredictability assumption `SecretGuessHard`.

## Differences from the printed book

1. **General encoded finite families, arbitrary source and side-information maps.** At security
   parameter `n`, secrets lie in a nonempty finite type `S n` encoded by `encS n : S n ↪ List Bool`
   with canonical partial decoder `decS n : List Bool → Option (S n)` (`decS n w = some s ↔
   encS n s = w`, polynomial-time `isSome` domain recognition, and a polynomial-time fallback
   element `defaultS n`); digests and keys lie in a nonempty finite type `T n` encoded by
   `encT n : T n ↪ List Bool`; and public side information lies in `X n` encoded by
   `encX n : X n ↪ List Bool`. Neither `sample n` nor `info n` is required to be efficiently
   computable; `SecretGuessHard.negligible_roAdvantage` requires only that `encX n (info n s)` has
   polynomial length in `n` on `(sample n).support`.
2. **Word-oracle distinguishers adapted to typed random-oracle games.** Distinguishers operate on
   words (`WordRODistinguisher X`) and are adapted to `RODistinguisher` by `toRODistinguisher`,
   answering canonical queries `encS n q` from the typed random oracle `S n → T n` via `encT n` and
   returning `[]` on malformed queries outside `Set.range (encS n)`.
3. **Fair-coin sampling of digests and query indices.** Because strict-PPT Turing machines flip fair
   coins, non-power-of-two digest spaces `T n` (such as `ZMod q` for an odd modulus `q`) admit no
   exact dyadic uniform sampler. The lazy simulator draws keys and cache-miss digests from a
   caller-supplied strict-PPT sampler `sampleT n` within statistical distance `εT n` of
   `uniformOfFintype (T n)`, adding `(Q n + 1) * εT n` to the concrete bounds (`0` when `sampleT n`
   is exact uniform, as for `BitString (outLen n)`), and `lazyROToGuess` selects a candidate query
   index via `ProbComp.sampleModIndex (width n) (Q n)`, adding `Q n / 2 ^ width n`. Both error terms
   are absorbed in `SecretGuessHard.negligible_roAdvantage` when `sampleT` is
   `StatisticallyIndistinguishable` from uniform and `width = id`.

## Main definitions

* `Cslib.Crypto.KeyDerivation.GuessFamilyAdversary`, `GuessFamilyAdversary.IsPPT`: families of
  singleton-guessing adversaries over `(X n, S n)` and uniform strict PPT admissibility.
* `Cslib.Crypto.KeyDerivation.ListGuessFamilyAdversary`, `ListGuessFamilyAdversary.IsPPT`:
  families of list-guessing adversaries over `(X n, S n)` and uniform strict PPT admissibility.
* `Cslib.Crypto.KeyDerivation.SecretGuessHard`: computational unpredictability of an encoded secret
  source given side information ([BonehShoup2023], Attack Game 8.3 and §8.10.1, p. 326).
* `Cslib.Crypto.KeyDerivation.WordROInput`, `encWordROInput`, `WordRODistinguisher`,
  `WordRODistinguisher.IsPPT`, `toRODistinguisher`, `toBitStringRODistinguisher`: word-oracle KDF
  distinguishers and their typed random-oracle adapters.
* `Cslib.Crypto.KeyDerivation.lazyROToListGuess`, `lazyROToGuess`: the elementary lazy-simulation
  list-guessing and singleton-guessing wrappers of Theorem 8.10.

## Main results

* `Cslib.Crypto.KeyDerivation.length_le_of_mem_support_lazyROToListGuess`: every supported list
  output by `lazyROToListGuess` has length bounded by the distinguisher's query budget.
* `Cslib.Crypto.KeyDerivation.roAdvantage_toRODistinguisher_le_listGuessAdvantage`,
  `roAdvantage_toRODistinguisher_le_listGuessAdvantage_add`: exact and approximate-sampler lazy
  list-guessing bounds of Theorem 8.10.
* `Cslib.Crypto.KeyDerivation.isPPT_lazyROToListGuess`, `isPPT_lazyROToGuess`: uniform strict PPT
  certificates for the lazy list-guessing and singleton-guessing wrappers.
* `Cslib.Crypto.KeyDerivation.roAdvantage_toRODistinguisher_le_mul_guessAdvantage_add`: concrete
  singleton-guessing bound of Theorem 8.10 with fair-coin index and digest sampling.
* `Cslib.Crypto.KeyDerivation.SecretGuessHard.negligible_roAdvantage`,
  `SecretGuessHard.negligible_roAdvantage_bitString`: computational Theorem 8.10 over general
  encoded finite families and its fixed-width bit-string specialization.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 8.10.1 (Attack Game 8.3 and fourth example, pp. 325–326) and Section 8.10.2
  (list-guessing game and Theorem 8.10, pp. 331–332).
-/

public section

open Cslib Probability Turing.MultiTapeTM
open Cslib.Probability.PMF (uniformOfFintype)
open scoped ENNReal NNReal

namespace Cslib.Crypto.KeyDerivation

/-! ### 1. Families of guessing adversaries and computational unpredictability -/

/-- A family of singleton-guessing adversaries in Attack Game 8.3 ([BonehShoup2023], §8.10.1,
p. 326) over secret family `S` and side-information family `X`. -/
abbrev GuessFamilyAdversary (X S : ℕ → Type) : Type :=
  (n : ℕ) → GuessAdversary (X n) (S n)

/-- A singleton-guessing family adversary is uniform strict PPT when one machine reads
`(1ⁿ, encX n x)` (`encSigma encUnary encX`) and writes the encoded candidate secret `encS n s`. -/
@[expose] def GuessFamilyAdversary.IsPPT {X S : ℕ → Type}
    (encX : ∀ n, X n ↪ List Bool) (encS : ∀ n, S n ↪ List Bool)
    (A : GuessFamilyAdversary X S) : Prop :=
  IsPPTOn (encSigma encUnary encX) encBits fun p => encS p.1 <$> A p.1 p.2

/-- A family of list-guessing adversaries ([BonehShoup2023], §8.10.2, p. 331) over secret family
`S` and side-information family `X`. -/
abbrev ListGuessFamilyAdversary (X S : ℕ → Type) : Type :=
  (n : ℕ) → ListGuessAdversary (X n) (S n)

/-- A list-guessing family adversary is uniform strict PPT when one machine reads
`(1ⁿ, encX n x)` (`encSigma encUnary encX`) and writes the framed list of encoded candidate
secrets. -/
@[expose] def ListGuessFamilyAdversary.IsPPT {X S : ℕ → Type}
    (encX : ∀ n, X n ↪ List Bool) (encS : ∀ n, S n ↪ List Bool)
    (B : ListGuessFamilyAdversary X S) : Prop :=
  IsPPTOn (encSigma encUnary encX) (encList encBits) fun p => List.map (encS p.1) <$> B p.1 p.2

/-- Computational unpredictability of a secret source given public side information
([BonehShoup2023], Section 8.10.1, Attack Game 8.3 and its fourth example, p. 326): every uniform
strict PPT guessing adversary (`GuessFamilyAdversary.IsPPT encX encS`) wins Attack Game 8.3 with
negligible probability.

Relative to the printed source: `sample n` and `info n` need not be efficiently computable, and
guessers are uniform strict PPT machines reading `(1ⁿ, encX n x)` and writing `encS n s`. -/
@[expose] def SecretGuessHard {X S : ℕ → Type} [∀ n, DecidableEq (S n)]
    (encX : ∀ n, X n ↪ List Bool) (encS : ∀ n, S n ↪ List Bool)
    (sample : ∀ n, PMF (S n)) (info : ∀ n, S n → X n) : Prop :=
  ∀ A : GuessFamilyAdversary X S, A.IsPPT encX encS →
    Negligible fun n => guessAdvantage (sample n) (info n) (A n)

/-! ### 2. Word-oracle KDF distinguishers and typed random-oracle adapter -/

/-- Input `(1ⁿ, x, z)` of a `WordRODistinguisher`: the security parameter `n`, the public side
information `x : X n`, and the candidate key word `z : List Bool`. -/
structure WordROInput (X : ℕ → Type) where
  /-- The security parameter. -/
  secParam : ℕ
  /-- The leaked public side information. -/
  sideInfo : X secParam
  /-- The candidate key word. -/
  key : List Bool

section WordROInputEncoding

variable {X : ℕ → Type}

/-- Field-tuple encoding of `WordROInput X`: the unary security parameter `1ⁿ` (framed), followed
by `encX n x` (framed), followed by the raw candidate key word `z` (unframed). -/
enc_structure encWordROInput (encX : ∀ n, X n ↪ List Bool) : WordROInput X where
  secParam : encUnary,
  sideInfo : (encX secParam) using (encX secParam).injective,
  key : encBits

end WordROInputEncoding

/-- A family of word-oracle KDF distinguishers in the random-oracle model: given the security
parameter `n`, public side information `x : X n`, and candidate key word `z : List Bool`, it queries
a single word oracle and outputs a bit. -/
abbrev WordRODistinguisher (X : ℕ → Type) : Type :=
  (n : ℕ) → X n → List Bool → ProbOracleComp (fun _ : Unit × List Bool => List Bool) Bool

/-- One uniform strict oracle-PPT machine reads `(1ⁿ, x, z)` (`encWordROInput encX`) and interacts
with the word oracle. -/
@[expose] def WordRODistinguisher.IsPPT {X : ℕ → Type} (encX : ∀ n, X n ↪ List Bool)
    (D : WordRODistinguisher X) : Prop :=
  IsOraclePPTOn (encWordROInput encX) encBool fun y => D y.secParam y.sideInfo y.key

/-- Adapt a word-oracle distinguisher to the typed random-oracle KDF game on `S n` and `T n`: pass
`encT n t` as the candidate key, answer canonical queries (`decS n q = some s`) by querying `s` and
encoding the reply with `encT n`, and answer malformed queries (`decS n q = none`) with `[]`. -/
@[expose] def toRODistinguisher {X S T : ℕ → Type}
    (decS : ∀ n, List Bool → Option (S n)) (encT : ∀ n, T n ↪ List Bool)
    (D : WordRODistinguisher X) (n : ℕ) : RODistinguisher (X n) (S n) (T n) :=
  fun x t => ProbOracleComp.simulate
    (fun req =>
      match decS n req.2 with
      | some s => encT n <$> ProbOracleComp.query s
      | none => pure [])
    (D n x (encT n t))

/-- Specialization of `toRODistinguisher` to `BitString (secLen n)` secrets and
`BitString (outLen n)` digests via `OracleCodec.bitString`. -/
abbrev toBitStringRODistinguisher {X : ℕ → Type} (secLen outLen : ℕ → ℕ)
    (D : WordRODistinguisher X) :
    ∀ n, RODistinguisher (X n) (BitString (secLen n)) (BitString (outLen n)) :=
  toRODistinguisher (fun n q => (OracleCodec.bitString (secLen n)).decodeQuery ((), q))
    (fun n => encBitString (outLen n)) D

/-! ### 3. Lazy list-guessing wrapper -/

/-- The elementary lazy-simulation list-guessing wrapper `B` of Theorem 8.10 ([BonehShoup2023],
§8.10.2, pp. 331–332): draw an independent candidate key `t ← sampleT n`, run
`D n x (encT n t)` against `cachedSamplerOracle (fun w => (decS n w).isSome) (encT n <$> sampleT n)`
starting from `[]`, and decode the cached valid queries via `decS n`. -/
@[expose] noncomputable def lazyROToListGuess {X S T : ℕ → Type}
    (decS : ∀ n, List Bool → Option (S n)) (encT : ∀ n, T n ↪ List Bool)
    (sampleT : ∀ n, ProbComp (T n)) (D : WordRODistinguisher X) :
    ListGuessFamilyAdversary X S :=
  fun n x => do
    let t ← sampleT n
    let (_, cache) ←
      ((D n x (encT n t)).runState fun req =>
        cachedSamplerOracle (fun w => (decS n w).isSome) (encT n <$> sampleT n) req.2).run []
    return cache.filterMap fun entry => decS n entry.1

/-- **Lazy output-size bound** ([BonehShoup2023], Theorem 8.10, §8.10.2, p. 331): if
`D n x (encT n t)` makes at most `Q` oracle queries for every supported `t` of `sampleT n`, then
every list output by `lazyROToListGuess decS encT sampleT D n x` has length at most `Q`. -/
theorem length_le_of_mem_support_lazyROToListGuess {X S T : ℕ → Type}
    {decS : ∀ n, List Bool → Option (S n)} {encT : ∀ n, T n ↪ List Bool}
    {sampleT : ∀ n, ProbComp (T n)} {D : WordRODistinguisher X} {n Q : ℕ} {x : X n}
    (hQ : ∀ t ∈ (ProbComp.eval (sampleT n)).support, (D n x (encT n t)).IsQueryBounded Q)
    {l : List (S n)}
    (hl : l ∈ (ProbComp.eval (lazyROToListGuess decS encT sampleT D n x)).support) :
    l.length ≤ Q := by
  simp only [lazyROToListGuess, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hl
  obtain ⟨t, ht, ⟨b, cache⟩, hrun, rfl⟩ := hl
  exact (List.length_filterMap_le _ cache).trans (by simpa using
    (ProbOracleComp.measure_runState_le (cost := fun _ => 1) (hQ t ht)
      (fun req => cachedSamplerOracle (fun w => (decS n w).isSome) (encT n <$> sampleT n) req.2)
      List.length (fun _ _ _ hres => (cachedSamplerOracle_support hres).1) [] (b, cache) hrun))

section LazyEquivalence

private noncomputable def idealLazyListLaw {X S T : ℕ → Type} [∀ n, Fintype (T n)]
    [∀ n, Nonempty (T n)] (decS : ∀ n, List Bool → Option (S n)) (encT : ∀ n, T n ↪ List Bool)
    (D : WordRODistinguisher X) (n : ℕ) (x : X n) : PMF (List (S n)) :=
  (uniformOfFintype (T n)).bind fun t =>
    (ProbOracleComp.runWith
      (fun req => cachedDistOracle (fun w => (decS n w).isSome)
        ((uniformOfFintype (T n)).map (encT n)) req.2)
      (D n x (encT n t)) []).map fun (_, cache) => cache.filterMap fun entry => decS n entry.1

private theorem idealLazyListLaw_eq_memoize {X S T : ℕ → Type} [∀ n, DecidableEq (S n)]
    [∀ n, Fintype (T n)] [∀ n, Nonempty (T n)]
    {encS : ∀ n, S n ↪ List Bool} {decS : ∀ n, List Bool → Option (S n)}
    (hdecS : ∀ n w s, decS n w = some s ↔ encS n s = w) (encT : ∀ n, T n ↪ List Bool)
    (D : WordRODistinguisher X) (n : ℕ) (x : X n) :
    idealLazyListLaw decS encT D n x =
      (uniformOfFintype (T n)).bind fun t =>
        (ProbOracleComp.runWith
          (memoize fun _ : S n => uniformOfFintype (T n))
          (toRODistinguisher decS encT D n x t) []).map fun (_, c) => c.map Prod.fst := by
  let d : S n → PMF (T n) := fun _ => uniformOfFintype (T n)
  unfold idealLazyListLaw
  refine congrArg ((uniformOfFintype (T n)).bind ·) (funext fun t => ?_)
  let O_typed : Unit × List Bool → StateT (List (S n × T n)) PMF (List Bool) := fun req cache =>
    match decS n req.2 with
    | some s => (memoize d s cache).map fun (v, c') => (encT n v, c')
    | none => PMF.pure ([], cache)
  have hsim : ProbOracleComp.runWith (memoize d) (toRODistinguisher decS encT D n x t) [] =
      ProbOracleComp.runWith O_typed (D n x (encT n t)) [] := by
    rw [ProbOracleComp.runWith_eq_run_interpret, ProbOracleComp.runWith_eq_run_interpret,
      toRODistinguisher, ProbOracleComp.interpret_simulate]
    congr 3; funext req cache
    cases hq : decS n req.2 <;>
      simp only [O_typed, hq, OracleComp.interpret_map, ProbOracleComp.interpret_query,
        OracleComp.interpret_pure] <;> rfl
  have hmap := ProbOracleComp.runWith_map_state O_typed
    (fun req => cachedDistOracle (fun w => (decS n w).isSome)
      ((uniformOfFintype (T n)).map (encT n)) req.2)
    (List.map fun (s, v) => (encS n s, encT n v))
    (fun req cache => by
      cases hq : decS n req.2 with
      | some s =>
        simp only [O_typed, cachedDistOracle, hq, Option.isSome_some, ↓reduceIte, PMF.map_comp,
          Function.comp_def]
        simpa only [(hdecS n req.2 s).mp hq, PMF.monad_map_eq_map] using
          Cslib.memoize_map (encS n) (encT n) d
            (fun _ => (uniformOfFintype (T n)).map (encT n)) (fun _ => rfl) s cache
      | none =>
        simp only [O_typed, cachedDistOracle, hq, Option.isSome_none, Bool.false_eq_true,
          ↓reduceIte, PMF.pure_map])
    (D n x (encT n t)) []
  rw [List.map_nil] at hmap
  rw [← hmap, ← hsim, PMF.map_comp]
  congr 1; funext ⟨_, c⟩
  have hdec_enc (s : S n) : decS n (encS n s) = some s := (hdecS n _ s).mpr rfl
  simp only [Function.comp_def, List.filterMap_map, hdec_enc]
  induction c <;> simp [*]

private theorem idealLazy_listGuessOutput_eq_eager {X S T : ℕ → Type}
    [∀ n, Fintype (S n)] [∀ n, DecidableEq (S n)] [∀ n, Fintype (T n)] [∀ n, Nonempty (T n)]
    {encS : ∀ n, S n ↪ List Bool} {decS : ∀ n, List Bool → Option (S n)}
    (hdecS : ∀ n w s, decS n w = some s ↔ encS n s = w) (encT : ∀ n, T n ↪ List Bool)
    (sample : ∀ n, PMF (S n)) (info : ∀ n, S n → X n) (D : WordRODistinguisher X) (n : ℕ) :
    ((sample n).bind fun s => (idealLazyListLaw decS encT D n (info n s)).bind fun l =>
        PMF.pure (decide (s ∈ l))) =
      listGuessOutput (sample n) (info n)
        (roToListGuess (toRODistinguisher decS encT D n)) := by
  unfold listGuessOutput roToListGuess
  refine congrArg ((sample n).bind ·) (funext fun s => ?_)
  rw [idealLazyListLaw_eq_memoize hdecS]
  simp only [ProbComp.eval_uniform, pmf_norm]
  rw [PMF.bind_comm]
  refine congrArg ((uniformOfFintype (T n)).bind ·) (funext fun t => ?_)
  simpa only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def] using
    RandomOracle.runWith_memoize_mem_eq_eager_runLog
      (toRODistinguisher decS encT D n (info n s) t) s

private theorem closeTo_idealLazyListLaw_eval_lazyROToListGuess {X S T : ℕ → Type}
    [∀ n, Fintype (T n)] [∀ n, Nonempty (T n)]
    (decS : ∀ n, List Bool → Option (S n)) (encT : ∀ n, T n ↪ List Bool)
    (sampleT : ∀ n, ProbComp (T n)) (D : WordRODistinguisher X) (n Q : ℕ) (x : X n)
    {εT : ℝ≥0} (hcloseT : CloseTo (uniformOfFintype (T n)) (ProbComp.eval (sampleT n)) εT)
    (hQ : ∀ t ∈ (ProbComp.eval (sampleT n)).support, (D n x (encT n t)).IsQueryBounded Q) :
    CloseTo (idealLazyListLaw decS encT D n x)
      (ProbComp.eval (lazyROToListGuess decS encT sampleT D n x))
      (((Q + 1 : ℕ) : ℝ≥0∞) * εT) := by
  have heval : ProbComp.eval (lazyROToListGuess decS encT sampleT D n x) =
      (ProbComp.eval (sampleT n)).bind fun t =>
        (ProbOracleComp.runWith
          (fun req => cachedDistOracle (fun w => (decS n w).isSome)
            ((ProbComp.eval (sampleT n)).map (encT n)) req.2)
          (D n x (encT n t)) []).map fun (_, cache) =>
            cache.filterMap fun entry => decS n entry.1 := by
    simp only [lazyROToListGuess, ProbComp.eval_bind, ProbOracleComp.eval_runState,
      ProbComp.eval_pure, ProbComp.eval_map, eval_cachedSamplerOracle, PMF.map]
    rfl
  rw [heval, idealLazyListLaw]
  have hring : (εT : ℝ≥0∞) + Q * (εT : ℝ≥0∞) = ((Q + 1 : ℕ) : ℝ≥0∞) * εT := by push_cast; ring
  refine (CloseTo.bind hcloseT fun t ht => ?_).mono hring.le
  apply CloseTo.map
  unfold ProbOracleComp.runWith
  apply (hQ t ht).closeTo_runWith
  rintro (k | req) cache
  · simp only [OracleComp.sumHandler, Sum.elim_inl, Nat.cast_zero, zero_mul]
    exact CloseTo.refl _
  · simp only [OracleComp.sumHandler, Sum.elim_inr, Nat.cast_one, one_mul]
    exact closeTo_cachedDistOracle _ (hcloseT.map (encT n)) req.2 cache

end LazyEquivalence

/-- **Lazy list-guessing inequality of Theorem 8.10 with approximate digest sampling**
([BonehShoup2023], §8.10.2, pp. 331–332): when `sampleT n` is within statistical distance `εT` of
`uniformOfFintype (T n)` and `D n (info n s) (encT n t)` makes at most `Q` oracle queries on
supported secrets `s` and candidate keys `t`, the random-oracle KDF advantage is at most
`listGuessAdvantage (sample n) (info n) (lazyROToListGuess decS encT sampleT D n) + (Q + 1) * εT`.
-/
theorem roAdvantage_toRODistinguisher_le_listGuessAdvantage_add {X S T : ℕ → Type}
    [∀ n, Fintype (S n)] [∀ n, DecidableEq (S n)] [∀ n, Fintype (T n)] [∀ n, Nonempty (T n)]
    {encS : ∀ n, S n ↪ List Bool} {decS : ∀ n, List Bool → Option (S n)}
    (hdecS : ∀ n w s, decS n w = some s ↔ encS n s = w) (encT : ∀ n, T n ↪ List Bool)
    (sampleT : ∀ n, ProbComp (T n)) (sample : ∀ n, PMF (S n)) (info : ∀ n, S n → X n)
    (D : WordRODistinguisher X) (n Q : ℕ) {εT : ℝ≥0}
    (hcloseT : CloseTo (uniformOfFintype (T n)) (ProbComp.eval (sampleT n)) εT)
    (hQ : ∀ s ∈ (sample n).support, ∀ t ∈ (ProbComp.eval (sampleT n)).support,
      (D n (info n s) (encT n t)).IsQueryBounded Q) :
    roAdvantage (sample n) (info n) (toRODistinguisher decS encT D n) ≤
      listGuessAdvantage (sample n) (info n) (lazyROToListGuess decS encT sampleT D n) +
        (Q + 1 : ℕ) * εT := by
  refine (roAdvantage_le_listGuessAdvantage (sample n) (info n)
    (toRODistinguisher decS encT D n)).trans ?_
  have hclose : CloseTo
      ((sample n).bind fun s => (idealLazyListLaw decS encT D n (info n s)).bind fun l =>
        PMF.pure (decide (s ∈ l)))
      (listGuessOutput (sample n) (info n) (lazyROToListGuess decS encT sampleT D n))
      (((Q + 1 : ℕ) : ℝ≥0∞) * εT) :=
    CloseTo.bind_right (sample n) fun s hs =>
      (closeTo_idealLazyListLaw_eval_lazyROToListGuess decS encT sampleT D n Q (info n s)
        hcloseT (hQ s hs)).bind_left fun l => PMF.pure (decide (s ∈ l))
  have hpt := hclose {true}
  rw [idealLazy_listGuessOutput_eq_eager hdecS encT sample info D n,
    PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_apply_singleton] at hpt
  simp only [listGuessAdvantage, Game.succProbability, ← ENNReal.coe_le_coe]
  push_cast [ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)] at hpt ⊢
  exact hpt

/-- **Exact lazy list-guessing inequality of Theorem 8.10** ([BonehShoup2023], §8.10.2,
pp. 331–332): when `sampleT n` samples `uniformOfFintype (T n)` exactly, the random-oracle KDF
distinguishing advantage of `toRODistinguisher decS encT D n` is at most the list-guessing
advantage of `lazyROToListGuess decS encT sampleT D n`, with no query-bound hypothesis. -/
theorem roAdvantage_toRODistinguisher_le_listGuessAdvantage {X S T : ℕ → Type}
    [∀ n, Fintype (S n)] [∀ n, DecidableEq (S n)] [∀ n, Fintype (T n)] [∀ n, Nonempty (T n)]
    {encS : ∀ n, S n ↪ List Bool} {decS : ∀ n, List Bool → Option (S n)}
    (hdecS : ∀ n w s, decS n w = some s ↔ encS n s = w) (encT : ∀ n, T n ↪ List Bool)
    (sampleT : ∀ n, ProbComp (T n)) (sample : ∀ n, PMF (S n)) (info : ∀ n, S n → X n)
    (D : WordRODistinguisher X) (n : ℕ)
    (hunif : ProbComp.eval (sampleT n) = uniformOfFintype (T n)) :
    roAdvantage (sample n) (info n) (toRODistinguisher decS encT D n) ≤
      listGuessAdvantage (sample n) (info n) (lazyROToListGuess decS encT sampleT D n) := by
  have heq : listGuessOutput (sample n) (info n) (lazyROToListGuess decS encT sampleT D n) =
      listGuessOutput (sample n) (info n) (roToListGuess (toRODistinguisher decS encT D n)) := by
    rw [← idealLazy_listGuessOutput_eq_eager hdecS encT sample info D n]
    unfold listGuessOutput idealLazyListLaw
    refine congrArg ((sample n).bind ·) (funext fun s => ?_)
    simp only [lazyROToListGuess, ProbOracleComp.eval_runState, eval_cachedSamplerOracle, hunif,
      PMF.map, pmf_norm]
  rw [listGuessAdvantage, heq, ← listGuessAdvantage]
  exact roAdvantage_le_listGuessAdvantage (sample n) (info n) (toRODistinguisher decS encT D n)

/-- **The lazy list-guessing wrapper is efficient**: `lazyROToListGuess decS encT sampleT D` is
uniform strict PPT whenever `(n, w) ↦ (decS n w).isSome` is computable in polynomial time,
`n ↦ encT n <$> sampleT n` is uniform strict PPT, and `D` is uniform strict oracle-PPT. -/
theorem isPPT_lazyROToListGuess {X S T : ℕ → Type}
    {encX : ∀ n, X n ↪ List Bool} {encS : ∀ n, S n ↪ List Bool}
    {decS : ∀ n, List Bool → Option (S n)} {encT : ∀ n, T n ↪ List Bool}
    {sampleT : ∀ n, ProbComp (T n)}
    (hdecS : ∀ n w s, decS n w = some s ↔ encS n s = w)
    (hisSome : ComputableInPolyTime (fun p : ℕ × List Bool => (decS p.1 p.2).isSome)
      (encPair encUnary encBits) encBool)
    (hsampleT : IsPPTOn encUnary encBits fun n => encT n <$> sampleT n)
    {D : WordRODistinguisher X} (hD : D.IsPPT encX) :
    (lazyROToListGuess decS encT sampleT D).IsPPT encX encS := by
  let E₀ := encSigma encUnary encX
  let E₁ := encPair E₀ encBits
  have hn₀ : ComputableInPolyTime (fun p : Σ n, X n => p.1) E₀ encUnary := by fun_prop
  have hz : IsPPTOn E₀ encBits (fun p : Σ n, X n => encT p.1 <$> sampleT p.1) :=
    hsampleT.preprocess hn₀
  have hview : ComputableInPolyTime (fun c : (Σ n, X n) × List Bool =>
      ((c.1.1, encX c.1.1 c.1.2), c.2)) E₁ (encPair (encPair encUnary encBits) encBits) :=
    ((ComputableInPolyTime.sigmaView encUnary encBits (fun n x => encX n x)
      (fun _ _ => rfl)).comp (ComputableInPolyTime.fst E₀ encBits)).prod
      (ComputableInPolyTime.snd E₀ encBits)
  have hreassoc : ComputableInPolyTime
      (fun q : (ℕ × List Bool) × List Bool => (q.1.1, q.1.2, q.2))
      (encPair (encPair encUnary encBits) encBits)
      (encPair encUnary (encPair encBits encBits)) := by fun_prop
  have hprep : ComputableInPolyTime
      (fun c : (Σ n, X n) × List Bool => (⟨c.1.1, c.1.2, c.2⟩ : WordROInput X))
      E₁ (encWordROInput encX) :=
    (hreassoc.comp hview).of_enc_eq fun c => by simp [encWordROInput_apply]
  have hvalid : ComputableInPolyTime
      (fun p : ((Σ n, X n) × List Bool) × List Bool => (decS p.1.1.1 p.2).isSome)
      (encPair E₁ encBits) encBool :=
    hisSome.comp (((hn₀.comp ((ComputableInPolyTime.fst E₀ encBits).comp
      (ComputableInPolyTime.fst E₁ encBits)))).prod (ComputableInPolyTime.snd E₁ encBits))
  have hsample₁ : IsPPTOn E₁ encBits
      (fun c : (Σ n, X n) × List Bool => encT c.1.1 <$> sampleT c.1.1) :=
    hsampleT.preprocess (hn₀.comp (ComputableInPolyTime.fst E₀ encBits))
  have hrun := isPPTOn_runState_cachedSamplerOracle
    (prepare := fun c : (Σ n, X n) × List Bool => (⟨c.1.1, c.1.2, c.2⟩ : WordROInput X))
    (valid := fun c q => (decS c.1.1 q).isSome)
    (sampleReply := fun c => encT c.1.1 <$> sampleT c.1.1)
    hD hprep hvalid hsample₁
  have hpost : ComputableInPolyTime
      (fun r : Bool × List (List Bool × List Bool) => r.2.map Prod.fst)
      (encPair encBool (encMemoCache encBits encBits)) (encList encBits) := by fun_prop
  have hprog : IsPPTOn E₀ (encList encBits) (fun p : Σ n, X n => do
      let z ← encT p.1 <$> sampleT p.1
      (fun r : Bool × List (List Bool × List Bool) => r.2.map Prod.fst) <$>
        (((D p.1 p.2 z).runState fun req =>
          cachedSamplerOracle (fun w => (decS p.1 w).isSome) (encT p.1 <$> sampleT p.1) req.2).run
            [])) :=
    hz.bind_with (hrun.map hpost)
  have hfilter (n : ℕ) (l : List (List Bool × List Bool))
      (hl : ∀ e ∈ l, (decS n e.1).isSome = true) :
      List.map (encS n) (l.filterMap fun entry => decS n entry.1) = l.map Prod.fst := by
    induction l with
    | nil => rfl
    | cons entry tail ih =>
      have hv := hl entry List.mem_cons_self
      cases hdec : decS n entry.1 with
      | none => simp [hdec] at hv
      | some s =>
        simp [hdec, (hdecS n entry.1 s).mp hdec,
          ih fun e he => hl e (List.mem_cons_of_mem _ he)]
  refine hprog.congr fun p => ?_
  simp only [lazyROToListGuess, pmf_norm]
  refine congrArg ((ProbComp.eval (sampleT p.1)).bind ·) (funext fun t => ?_)
  rw [PMF.map]
  refine PMF.bind_congr_on_support _ _ _ fun rc hrc => ?_
  exact congrArg PMF.pure (hfilter p.1 rc.2 (valid_of_mem_runState_cachedSamplerOracle
    (fun w => (decS p.1 w).isSome) (encT p.1 <$> sampleT p.1) (D p.1 p.2 (encT p.1 t)) hrc)).symm

/-! ### 4. Lazy singleton-guessing wrapper and computational Theorem 8.10 -/

/-- The elementary lazy-simulation singleton-guessing wrapper `B'` of Theorem 8.10
([BonehShoup2023], §8.10.2, pp. 331–332) with fair-coin modular index sampling: run
`lazyROToListGuess decS encT sampleT D n x`, draw an index from
`ProbComp.sampleModIndex (width n) (Q n)`, and return the entry at that position (or `defaultS n`
past the end of the list). -/
@[expose] noncomputable def lazyROToGuess {X S T : ℕ → Type}
    (width Q : ℕ → ℕ) (defaultS : ∀ n, S n)
    (decS : ∀ n, List Bool → Option (S n)) (encT : ∀ n, T n ↪ List Bool)
    (sampleT : ∀ n, ProbComp (T n)) (D : WordRODistinguisher X) :
    GuessFamilyAdversary X S :=
  fun n x => do
    let l ← lazyROToListGuess decS encT sampleT D n x
    let i ← ProbComp.sampleModIndex (width n) (Q n)
    return l.getD i (defaultS n)

/-- **The lazy singleton-guessing wrapper is efficient**:
`lazyROToGuess width Q defaultS decS encT sampleT D` is uniform strict PPT whenever `width` and `Q`
are computable in polynomial time in unary, `(n, w) ↦ (decS n w).isSome` and
`n ↦ encS n (defaultS n)` are computable in polynomial time, `n ↦ encT n <$> sampleT n` is uniform
strict PPT, and `D` is uniform strict oracle-PPT. -/
theorem isPPT_lazyROToGuess {X S T : ℕ → Type}
    {encX : ∀ n, X n ↪ List Bool} {encS : ∀ n, S n ↪ List Bool}
    {width Q : ℕ → ℕ} {defaultS : ∀ n, S n}
    {decS : ∀ n, List Bool → Option (S n)} {encT : ∀ n, T n ↪ List Bool}
    {sampleT : ∀ n, ProbComp (T n)}
    (hwidth : ComputableInPolyTime width encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hdefault : ComputableInPolyTime (fun n => encS n (defaultS n)) encUnary encBits)
    (hdecS : ∀ n w s, decS n w = some s ↔ encS n s = w)
    (hisSome : ComputableInPolyTime (fun p : ℕ × List Bool => (decS p.1 p.2).isSome)
      (encPair encUnary encBits) encBool)
    (hsampleT : IsPPTOn encUnary encBits fun n => encT n <$> sampleT n)
    {D : WordRODistinguisher X} (hD : D.IsPPT encX) :
    (lazyROToGuess width Q defaultS decS encT sampleT D).IsPPT encX encS := by
  let E₀ := encSigma encUnary encX
  let E₁ := encPair E₀ (encList encBits)
  have hn : ComputableInPolyTime (fun p : (Σ n, X n) × List (List Bool) => p.1.1) E₁ encUnary := by
    fun_prop
  have hsample : IsPPTOn E₁ encUnary (fun p : (Σ n, X n) × List (List Bool) =>
      ProbComp.sampleModIndex (width p.1.1) (Q p.1.1)) :=
    isPPTOn_sampleModIndex (hwidth.comp hn) (hQ.comp hn)
  let E₂ := encPair E₁ encUnary
  have hpick : ComputableInPolyTime
      (fun p : ((Σ n, X n) × List (List Bool)) × ℕ =>
        (p.1.2[p.2]?).getD (encS p.1.1.1 (defaultS p.1.1.1))) E₂ encBits :=
    ComputableInPolyTime.optionGetDWithInput
      (ComputableInPolyTime.getElem? (by fun_prop) (by fun_prop))
      (hdefault.comp (g := fun p : ((Σ n, X n) × List (List Bool)) × ℕ => p.1.1.1) (by fun_prop))
  have hprog : IsPPTOn E₀ encBits (fun p : Σ n, X n => do
      let words ← List.map (encS p.1) <$> lazyROToListGuess decS encT sampleT D p.1 p.2
      (fun i => (words[i]?).getD (encS p.1 (defaultS p.1))) <$>
        ProbComp.sampleModIndex (width p.1) (Q p.1)) :=
    (isPPT_lazyROToListGuess hdecS hisSome hsampleT hD).bind_with (hsample.map_with hpick)
  refine hprog.congr fun p => ?_
  simp only [lazyROToGuess, PMF.map, List.getD_eq_getElem?_getD, List.getElem?_map, Option.getD_map,
    pmf_norm]

/-- **Concrete singleton-guessing inequality of Theorem 8.10** ([BonehShoup2023], §8.10.2,
pp. 331–332), accounting for fair-coin index and digest sampling: when `sampleT n` is within
statistical distance `εT` of `uniformOfFintype (T n)` and `D n (info n s) (encT n t)` makes at most
`Q n` oracle queries on supported secrets `s` and candidate keys `t`, the random-oracle KDF
distinguishing advantage is at most
`Q n * guessAdvantage (sample n) (info n) (lazyROToGuess width Q defaultS decS encT sampleT D n) +
Q n / 2 ^ width n + (Q n + 1) * εT`. -/
theorem roAdvantage_toRODistinguisher_le_mul_guessAdvantage_add {X S T : ℕ → Type}
    [∀ n, Fintype (S n)] [∀ n, DecidableEq (S n)] [∀ n, Fintype (T n)] [∀ n, Nonempty (T n)]
    {encS : ∀ n, S n ↪ List Bool} {decS : ∀ n, List Bool → Option (S n)}
    (hdecS : ∀ n w s, decS n w = some s ↔ encS n s = w)
    (width Q : ℕ → ℕ) (defaultS : ∀ n, S n) (encT : ∀ n, T n ↪ List Bool)
    (sampleT : ∀ n, ProbComp (T n)) (sample : ∀ n, PMF (S n)) (info : ∀ n, S n → X n)
    (D : WordRODistinguisher X) (n : ℕ) {εT : ℝ≥0}
    (hcloseT : CloseTo (uniformOfFintype (T n)) (ProbComp.eval (sampleT n)) εT)
    (hQ : ∀ s ∈ (sample n).support, ∀ t ∈ (ProbComp.eval (sampleT n)).support,
      (D n (info n s) (encT n t)).IsQueryBounded (Q n)) :
    roAdvantage (sample n) (info n) (toRODistinguisher decS encT D n) ≤
      Q n * guessAdvantage (sample n) (info n)
          (lazyROToGuess width Q defaultS decS encT sampleT D n) +
        Q n / 2 ^ width n + (Q n + 1 : ℕ) * εT := by
  refine (roAdvantage_toRODistinguisher_le_listGuessAdvantage_add hdecS encT sampleT sample info
    D n (Q n) hcloseT hQ).trans ?_
  rw [add_le_add_iff_right]
  have hle : listGuessOutput (sample n) (info n) (lazyROToListGuess decS encT sampleT D n) true ≤
      (Q n : ℝ≥0∞) *
        guessOutput (sample n) (info n)
          (lazyROToGuess width Q defaultS decS encT sampleT D n) true +
          (Q n : ℝ≥0∞) / 2 ^ width n := by
    unfold listGuessOutput guessOutput lazyROToGuess
    simp only [pmf_norm]
    refine PMF.bind_apply_le_mul_bind_apply_add_on_support (sample n) fun s hs => ?_
    refine PMF.bind_apply_le_mul_bind_apply_add_on_support _ fun l hl => ?_
    have hlen : l.length ≤ Q n := length_le_of_mem_support_lazyROToListGuess (hQ s hs) hl
    have hmap : ((ProbComp.eval (ProbComp.sampleModIndex (width n) (Q n))).bind fun i =>
        PMF.pure (decide (l.getD i (defaultS n) = s))) =
        ((ProbComp.eval (ProbComp.sampleModIndex (width n) (Q n))).map
          fun i => l.getD i (defaultS n)).bind fun s' => PMF.pure (decide (s' = s)) := by
      rw [PMF.bind_map]
      rfl
    rw [hmap, Cslib.Probability.PMF.bind_pure_decide_eq_apply_true']
    by_cases hmem : s ∈ l
    · have htake : s ∈ l.take (Q n) := by rwa [List.take_of_length_le hlen]
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem htake
      rw [List.length_take] at hi
      have hiQ : i < Q n := hi.trans_le (min_le_left _ _)
      have hil : i < l.length := hi.trans_le (min_le_right _ _)
      rw [ProbComp.sampleModIndex_eq_sampleModNat (width n) ((Nat.zero_le i).trans_lt hiQ),
        show (PMF.pure (decide ((l.take (Q n))[i] ∈ l))) true = 1 by simp]
      refine (ProbComp.one_le_mul_eval_sampleModNat_add hiQ :
        (1 : ℝ≥0∞) ≤ (Q n : ℝ≥0∞) * ProbComp.eval (ProbComp.sampleModNat (width n) (Q n)) i +
          (Q n : ℝ≥0∞) / 2 ^ width n).trans ?_
      gcongr
      rw [show (l.take (Q n))[i] = l.getD i (defaultS n) by
        simp [List.getElem_take, List.getD_eq_getElem?_getD, hil]]
      exact PMF.le_map_apply _ (fun j => l.getD j (defaultS n)) i
    · simp [hmem]
  simp only [listGuessAdvantage, guessAdvantage, Game.succProbability, ← ENNReal.coe_le_coe]
  push_cast [ENNReal.coe_toNNReal (PMF.apply_ne_top _ _),
    ENNReal.coe_div (pow_ne_zero _ two_ne_zero)]
  exact hle

/-- **Computational Theorem 8.10** ([BonehShoup2023], §8.10.2, pp. 331–332, with §8.10.1, Attack
Game 8.3, p. 326): over encoded finite secret families `S` and digest/key families `T`, if the
secret source is computationally unpredictable (`SecretGuessHard`), `decS` is the canonical partial
decoder of `encS` with polynomial-time domain recognition and a polynomial-time fallback element
`defaultS`, `sampleT` is a uniform strict-PPT sampler statistically indistinguishable from
`uniformOfFintype (T n)`, and `encX n (info n s)` has polynomial length in `n` on
`(sample n).support`, then every uniform strict oracle-PPT word distinguisher has negligible
random-oracle KDF distinguishing advantage. -/
theorem SecretGuessHard.negligible_roAdvantage {X S T : ℕ → Type}
    [∀ n, Fintype (S n)] [∀ n, DecidableEq (S n)] [∀ n, Fintype (T n)] [∀ n, Nonempty (T n)]
    {encX : ∀ n, X n ↪ List Bool} {encS : ∀ n, S n ↪ List Bool}
    {decS : ∀ n, List Bool → Option (S n)} {defaultS : ∀ n, S n}
    {encT : ∀ n, T n ↪ List Bool} {sampleT : ∀ n, ProbComp (T n)}
    {sample : ∀ n, PMF (S n)} {info : ∀ n, S n → X n}
    (hguess : SecretGuessHard encX encS sample info)
    (hdecS : ∀ n w s, decS n w = some s ↔ encS n s = w)
    (hisSome : ComputableInPolyTime (fun p : ℕ × List Bool => (decS p.1 p.2).isSome)
      (encPair encUnary encBits) encBool)
    (hdefault : ComputableInPolyTime (fun n => encS n (defaultS n)) encUnary encBits)
    (hsampleT : IsPPTOn encUnary encBits fun n => encT n <$> sampleT n)
    (hcloseT : StatisticallyIndistinguishable (fun n => uniformOfFintype (T n))
      (fun n => ProbComp.eval (sampleT n)))
    (hinfo : ∃ c d, ∀ n, ∀ s ∈ (sample n).support,
      (encX n (info n s)).length ≤ c * (n + 1) ^ d)
    {D : WordRODistinguisher X} (hD : D.IsPPT encX) :
    Negligible fun n => roAdvantage (sample n) (info n) (toRODistinguisher decS encT D n) := by
  obtain ⟨εT, hεT, hcloseT⟩ := hcloseT
  obtain ⟨ci, di, hinfo⟩ := hinfo
  obtain ⟨cT, dT, hlenT⟩ := hsampleT.length_le
  obtain ⟨cD, dD, hbounds⟩ := hD.query_bounds
  let maxT : ℕ → ℕ := fun n => cT * (n + 1) ^ dT
  let M : ℕ → ℕ := fun n => 2 * n + 2 * (ci * (n + 1) ^ di) + maxT n + 2
  let Q : ℕ → ℕ := fun n => cD * (M n + 1) ^ dD
  have hQ : ComputableInPolyTime Q encUnary encUnary := by dsimp only [Q, M, maxT]; fun_prop
  have hDt : ∀ n, ∀ s ∈ (sample n).support, ∀ t ∈ (ProbComp.eval (sampleT n)).support,
      (D n (info n s) (encT n t)).IsQueryBounded (Q n) := by
    intro n s hs t ht
    refine (hbounds ⟨n, info n s, encT n t⟩).1.mono ?_
    have his := hinfo n s hs
    have hlt : (encT n t).length ≤ maxT n := by
      simpa only [encBits_apply, encUnary_apply, List.length_replicate, maxT] using
        hlenT n (encT n t) (by rw [ProbComp.eval_map, PMF.mem_support_map_iff]; exact ⟨t, ht, rfl⟩)
    have hlen : (encWordROInput encX ⟨n, info n s, encT n t⟩).length ≤ M n := by
      rw [encWordROInput_apply]; dsimp only [M]; enc_len
    exact Nat.mul_le_mul_left cD (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) dD)
  have hguess_red := hguess _
    (isPPT_lazyROToGuess (width := fun n => n) .id' hQ hdefault hdecS hisSome hsampleT hD)
  negligible using fun n =>
    roAdvantage_toRODistinguisher_le_mul_guessAdvantage_add hdecS (fun n => n) Q defaultS encT
      sampleT sample info D n (hcloseT n) (hDt n)

/-! ### 5. Specialization to fixed-width bit strings -/

/-- **Computational Theorem 8.10 over fixed-width bit strings** ([BonehShoup2023], §8.10.2,
pp. 331–332): specialization of `SecretGuessHard.negligible_roAdvantage` to `BitString (secLen n)`
secrets and `BitString (outLen n)` keys when `secLen` and `outLen` are computable in polynomial time
in unary. -/
theorem SecretGuessHard.negligible_roAdvantage_bitString {X : ℕ → Type}
    {encX : ∀ n, X n ↪ List Bool} {secLen outLen : ℕ → ℕ}
    {sample : ∀ n, PMF (BitString (secLen n))} {info : ∀ n, BitString (secLen n) → X n}
    (hguess : SecretGuessHard encX (fun n => encBitString (secLen n)) sample info)
    (hsec : ComputableInPolyTime secLen encUnary encUnary)
    (hout : ComputableInPolyTime outLen encUnary encUnary)
    (hinfo : ∃ c d, ∀ n, ∀ s ∈ (sample n).support,
      (encX n (info n s)).length ≤ c * (n + 1) ^ d)
    {D : WordRODistinguisher X} (hD : D.IsPPT encX) :
    Negligible fun n =>
      roAdvantage (sample n) (info n) (toBitStringRODistinguisher secLen outLen D n) := by
  let sampleT : ∀ n, ProbComp (BitString (outLen n)) :=
    fun n => BitString.ofList (outLen n) <$> BitString.sampleList (outLen n)
  have hdecS : ∀ n w s,
      (OracleCodec.bitString (secLen n)).decodeQuery ((), w) = some s ↔
        encBitString (secLen n) s = w := fun n w s => by
    simpa [OracleCodec.bitString, encBitString_apply] using
      (OracleCodec.bitString (secLen n)).decodeQuery_eq_some_iff ((), w) s
  have hisSome : ComputableInPolyTime
      (fun p : ℕ × List Bool =>
        ((OracleCodec.bitString (secLen p.1)).decodeQuery ((), p.2)).isSome)
      (encPair encUnary encBits) encBool := by
    rw [show (fun p : ℕ × List Bool =>
        ((OracleCodec.bitString (secLen p.1)).decodeQuery ((), p.2)).isSome) =
        fun p : ℕ × List Bool => p.2.length == secLen p.1 from funext fun p => by
      by_cases h : p.2.length = secLen p.1 <;> simp [OracleCodec.bitString, h]]
    fun_prop
  have hdefault : ComputableInPolyTime
      (fun n : ℕ => encBitString (secLen n) (fun _ => false)) encUnary encBits := by
    rw [show (fun n : ℕ => encBitString (secLen n) (fun _ => false)) =
        fun n : ℕ => List.replicate (secLen n) false from
      funext fun n => by simp [encBitString_apply, List.ofFn_const]]
    exact (bits_encList_polyTime encBool).2.comp (.replicate hsec (.const false))
  have hsampleT_eval (n : ℕ) :
      ProbComp.eval (sampleT n) = uniformOfFintype (BitString (outLen n)) := by
    simp only [sampleT, ProbComp.eval_map, BitString.eval_sampleList, BitString.uniformList,
      PMF.map_comp, Function.comp_def, BitString.ofList_ofFn]
    exact PMF.map_id _
  have hsampleT_ppt : IsPPTOn encUnary encBits fun n => encBitString (outLen n) <$> sampleT n :=
    hout.sampleList.congr fun n => by
      rw [ProbComp.eval_map, hsampleT_eval, BitString.eval_sampleList]; rfl
  exact hguess.negligible_roAdvantage hdecS hisSome hdefault hsampleT_ppt
    ⟨fun _ => 0, negligible_zero, fun n => by
      dsimp only; rw [hsampleT_eval n]; exact CloseTo.refl _⟩ hinfo hD

end Cslib.Crypto.KeyDerivation
