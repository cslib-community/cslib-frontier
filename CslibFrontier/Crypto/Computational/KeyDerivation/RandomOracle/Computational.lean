/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Oracle
public import CslibFrontier.Computability.Probabilistic.Sampling
public import CslibFrontier.Crypto.Computational.KeyDerivation.RandomOracle
public import CslibFrontier.Crypto.Computational.PseudorandomFunction.RandomOracle
public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Languages.Probabilistic.Oracle.Substitution
public import CslibFrontier.Languages.Probabilistic.UniformNat.ModIndex
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Probabilistic.Memoize
import CslibFrontier.Computability.Probabilistic.Oracle.RunState
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.QueryBounds
import CslibFrontier.Computability.Probabilistic.UniformNat.ModIndex
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic
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
Section 8.10.2 (Theorem 8.10, pp. 331–332) over `secLen n`-bit secrets and `outLen n`-bit keys.

Whereas `CslibFrontier.Crypto.Computational.KeyDerivation.RandomOracle` states the eager-table
(`uniformOfFintype (S → T)`) concrete bounds and the information-theoretic (unbounded-guesser)
asymptotic transfer of Theorem 8.10 for arbitrary finite nonempty `S` and `T`, this module
constructs the elementary lazy-simulation wrappers `lazyROToListGuess` and `lazyROToGuess` over
associative-list caches (`cachedRandomFunctionOracle`), proves their uniform strict PPT
certificates from a word-oracle distinguisher's `IsOraclePPTOn` certificate, and derives the
asymptotic random-oracle KDF security transfer under the standard computational unpredictability
assumption `SecretGuessHard`.

## Differences from the printed book

1. **Bit-string secrets and keys, arbitrary source and side-information maps.** Secrets have type
   `BitString (secLen n)`, random-oracle replies and keys have type `BitString (outLen n)`, and
   public side information lies in `X` encoded by `encX : X ↪ List Bool`. Neither `sample n` nor
   `info n` is required to be efficiently computable; `SecretGuessHard.negligible_roAdvantage`
   requires only that `encX (info n s)` has polynomial length in `n` on `(sample n).support`.
   General non-bit-string finite oracle domains remain open (#6039).
2. **Word-oracle distinguishers adapted to typed random-oracle games.** Distinguishers operate on
   words (`WordRODistinguisher X`) and are adapted to `RODistinguisher` by `toRODistinguisher`,
   answering queries of length `secLen n` from the random oracle and returning `[]` on malformed
   queries.
3. **Fair-coin modular index sampling.** Following `Cslib.Crypto.PrimeOrderGroupFamily` in
   `CslibFrontier/Crypto/Computational/DiffieHellman/ListCDHFamily.lean`, `lazyROToGuess` selects
   a candidate query index via `ProbComp.sampleModIndex (width n) (Q n)`, adding the sampling-bias
   term `Q n / 2 ^ width n` to the concrete singleton-guessing bound (`width = id` makes this term
   negligible when `Q` is polynomially bounded).

## Main definitions

* `Cslib.Crypto.KeyDerivation.GuessFamilyAdversary`, `GuessFamilyAdversary.IsPPT`: families of
  singleton-guessing adversaries and uniform strict PPT admissibility.
* `Cslib.Crypto.KeyDerivation.ListGuessFamilyAdversary`, `ListGuessFamilyAdversary.IsPPT`:
  families of list-guessing adversaries and uniform strict PPT admissibility.
* `Cslib.Crypto.KeyDerivation.SecretGuessHard`: computational unpredictability of a secret source
  given side information ([BonehShoup2023], Attack Game 8.3 and §8.10.1, p. 326).
* `Cslib.Crypto.KeyDerivation.WordRODistinguisher`, `WordRODistinguisher.IsPPT`,
  `toRODistinguisher`: word-oracle KDF distinguishers and their typed random-oracle adapter.
* `Cslib.Crypto.KeyDerivation.lazyROToListGuess`, `lazyROToGuess`: the elementary lazy-simulation
  list-guessing and singleton-guessing wrappers of Theorem 8.10 (built on
  `Cslib.Crypto.cachedRandomFunctionOracle`).

## Main results

* `Cslib.Crypto.KeyDerivation.length_le_of_mem_support_lazyROToListGuess`: every supported list
  output by `lazyROToListGuess` has length bounded by the distinguisher's query budget.
* `Cslib.Crypto.KeyDerivation.roAdvantage_toRODistinguisher_le_listGuessAdvantage`: lazy
  list-guessing bound of Theorem 8.10.
* `Cslib.Crypto.KeyDerivation.isPPT_lazyROToListGuess`, `isPPT_lazyROToGuess`: uniform strict PPT
  certificates for the lazy list-guessing and singleton-guessing wrappers.
* `Cslib.Crypto.KeyDerivation.roAdvantage_toRODistinguisher_le_mul_guessAdvantage_add`: concrete
  singleton-guessing bound of Theorem 8.10 with fair-coin modular index sampling.
* `Cslib.Crypto.KeyDerivation.SecretGuessHard.negligible_roAdvantage`: computational Theorem 8.10,
  transferring `SecretGuessHard` to negligible random-oracle KDF advantage for every uniform strict
  PPT word-oracle distinguisher.

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
p. 326) over `secLen n`-bit secrets and public side information `X`. -/
abbrev GuessFamilyAdversary (X : Type) (secLen : ℕ → ℕ) : Type :=
  (n : ℕ) → GuessAdversary X (BitString (secLen n))

/-- A singleton-guessing family adversary is uniform strict PPT when one machine reads
`(1ⁿ, encX x)` and writes the `secLen n` bits of its candidate secret. -/
@[expose] def GuessFamilyAdversary.IsPPT {X : Type} (encX : X ↪ List Bool) {secLen : ℕ → ℕ}
    (A : GuessFamilyAdversary X secLen) : Prop :=
  IsPPTOn (encPair encUnary encX) encBits fun p => List.ofFn <$> A p.1 p.2

/-- A family of list-guessing adversaries ([BonehShoup2023], §8.10.2, p. 331) over `secLen n`-bit
secrets and public side information `X`. -/
abbrev ListGuessFamilyAdversary (X : Type) (secLen : ℕ → ℕ) : Type :=
  (n : ℕ) → ListGuessAdversary X (BitString (secLen n))

/-- A list-guessing family adversary is uniform strict PPT when one machine reads `(1ⁿ, encX x)`
and writes the framed list of `secLen n`-bit words of its candidate secrets. -/
@[expose] def ListGuessFamilyAdversary.IsPPT {X : Type} (encX : X ↪ List Bool) {secLen : ℕ → ℕ}
    (B : ListGuessFamilyAdversary X secLen) : Prop :=
  IsPPTOn (encPair encUnary encX) (encList encBits) fun p => List.map List.ofFn <$> B p.1 p.2

/-- Computational unpredictability of a secret source given public side information
([BonehShoup2023], Section 8.10.1, Attack Game 8.3 and its fourth example, p. 326): every uniform
strict PPT guessing adversary (`GuessFamilyAdversary.IsPPT encX`) wins Attack Game 8.3 with
negligible probability.

Relative to the printed source: `sample n` and `info n` need not be efficiently computable; secrets
at security parameter `n` are `secLen n`-bit strings `BitString (secLen n)` rather than elements of
an arbitrary finite set `S`; and guessers are uniform strict PPT machines reading `(1ⁿ, encX x)`
and writing the candidate secret's `secLen n` bits. -/
@[expose] def SecretGuessHard {X : Type} (encX : X ↪ List Bool) (secLen : ℕ → ℕ)
    (sample : ∀ n, PMF (BitString (secLen n))) (info : ∀ n, BitString (secLen n) → X) : Prop :=
  ∀ A : GuessFamilyAdversary X secLen, A.IsPPT encX →
    Negligible fun n => guessAdvantage (sample n) (info n) (A n)

/-! ### 2. Word-oracle KDF distinguishers and typed random-oracle adapter -/

/-- A family of word-oracle KDF distinguishers in the random-oracle model: given the security
parameter `n`, public side information `x : X`, and candidate key word `z : List Bool`, it queries
a single word oracle and outputs a bit. -/
abbrev WordRODistinguisher (X : Type) : Type :=
  (n : ℕ) → X → List Bool → ProbOracleComp (fun _ : Unit × List Bool => List Bool) Bool

/-- One uniform strict oracle-PPT machine reads `(1ⁿ, x, z)` and interacts with the word oracle. -/
@[expose] def WordRODistinguisher.IsPPT {X : Type} (encX : X ↪ List Bool)
    (D : WordRODistinguisher X) : Prop :=
  IsOraclePPTOn (encPair encUnary (encPair encX encBits)) encBool fun p => D p.1 p.2.1 p.2.2

/-- Adapt a word-oracle distinguisher to the typed random-oracle KDF game on
`BitString (secLen n)` and `BitString (outLen n)`: pass `List.ofFn t` as the candidate key, answer
queries of length `secLen n` by querying `BitString.ofList (secLen n) q` and converting the reply
with `List.ofFn`, and answer queries of any other length with `[]`. -/
@[expose] def toRODistinguisher {X : Type} (secLen outLen : ℕ → ℕ) (D : WordRODistinguisher X)
    (n : ℕ) : RODistinguisher X (BitString (secLen n)) (BitString (outLen n)) :=
  fun x t => ProbOracleComp.simulate
    (fun ⟨_, q⟩ =>
      if q.length = secLen n then
        List.ofFn <$> ProbOracleComp.query (BitString.ofList (secLen n) q)
      else pure [])
    (D n x (List.ofFn t))

/-! ### 3. Lazy list-guessing wrapper and certified reduction -/

/-- The elementary lazy-simulation list-guessing wrapper `B` of Theorem 8.10 ([BonehShoup2023],
§8.10.2, pp. 331–332): draw an independent `outLen n`-bit key `z`, run `D n x z` against
`cachedRandomFunctionOracle (secLen n) (outLen n)` starting from `[]`, and output the cached
`secLen n`-bit queries. -/
@[expose] noncomputable def lazyROToListGuess {X : Type} (secLen outLen : ℕ → ℕ)
    (D : WordRODistinguisher X) : ListGuessFamilyAdversary X secLen :=
  fun n x => do
    let z ← BitString.sampleList (outLen n)
    let (_, cache) ←
      ((D n x z).runState fun ⟨_, q⟩ =>
        cachedRandomFunctionOracle (secLen n) (outLen n) q).run []
    return cache.map fun ⟨q, _⟩ => BitString.ofList (secLen n) q

private theorem cachedRandomFunctionOracle_support {inLen outLen : ℕ} {q : List Bool}
    {cache : List (List Bool × List Bool)} {res : List Bool × List (List Bool × List Bool)}
    (hres : res ∈ (ProbComp.eval (cachedRandomFunctionOracle inLen outLen q cache)).support) :
    res.2.length ≤ cache.length + 1 ∧
      ((∀ entry ∈ cache, entry.1.length = inLen) → ∀ entry ∈ res.2, entry.1.length = inLen) := by
  by_cases hq : q.length = inLen
  · simp only [cachedRandomFunctionOracle, hq, ↓reduceIte, ProbComp.eval_memoize] at hres
    rcases (RandomOracle.mem_support_memoize_iff _ _ _ _).mp hres with
      ⟨_, hnext⟩ | ⟨_, _, hnext⟩
    · rw [hnext]
      exact ⟨Nat.le_succ _, id⟩
    · rw [hnext]
      refine ⟨by simp, fun hcache entry hentry => ?_⟩
      rcases List.mem_cons.mp hentry with rfl | hmem
      · exact hq
      · exact hcache entry hmem
  · simp only [cachedRandomFunctionOracle, hq, ↓reduceIte, ProbComp.eval_pure,
      PMF.mem_support_pure_iff] at hres
    subst hres
    exact ⟨Nat.le_succ _, id⟩

private theorem key_length_of_mem_runState_cachedRandomFunctionOracle {α : Type}
    (inLen outLen : ℕ) (P : WordOracleComp Unit α) {res : α × List (List Bool × List Bool)}
    (hres : res ∈ (ProbComp.eval
      ((P.runState fun ⟨_, q⟩ => cachedRandomFunctionOracle inLen outLen q).run [])).support) :
    ∀ entry ∈ res.2, entry.1.length = inLen := by
  rw [ProbOracleComp.eval_runState] at hres
  exact ProbOracleComp.runWith_invariant
    (fun ⟨_, q⟩ cache => ProbComp.eval (cachedRandomFunctionOracle inLen outLen q cache))
    (fun cache => ∀ entry ∈ cache, entry.1.length = inLen)
    (fun ⟨_, q⟩ cache hcache a cache' hstep =>
      (cachedRandomFunctionOracle_support hstep).2 hcache)
    P [] (by simp) res.1 res.2 hres

/-- **Lazy output-size bound** ([BonehShoup2023], Theorem 8.10, §8.10.2, p. 331): if `D n x z`
makes at most `Q` oracle queries for every `outLen n`-bit key `z`, then every list output by
`lazyROToListGuess secLen outLen D n x` has length at most `Q`. -/
theorem length_le_of_mem_support_lazyROToListGuess {X : Type} {secLen outLen : ℕ → ℕ}
    {D : WordRODistinguisher X} {n Q : ℕ} {x : X}
    (hQ : ∀ z : List Bool, z.length = outLen n → (D n x z).IsQueryBounded Q)
    {l : List (BitString (secLen n))}
    (hl : l ∈ (ProbComp.eval (lazyROToListGuess secLen outLen D n x)).support) :
    l.length ≤ Q := by
  simp only [lazyROToListGuess, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hl
  obtain ⟨z, hz, ⟨b, cache⟩, hrun, rfl⟩ := hl
  rw [BitString.eval_sampleList] at hz
  have hzlen := BitString.length_of_mem_support_uniformList hz
  have hbound := ProbOracleComp.measure_runState_le (cost := fun _ => 1) (hQ z hzlen)
    (fun ⟨_, q⟩ => cachedRandomFunctionOracle (secLen n) (outLen n) q) List.length
    (fun ⟨_, q⟩ s res hres => (cachedRandomFunctionOracle_support hres).1) [] (b, cache) hrun
  simpa using hbound

section LazyEquivalence

private theorem lookup_isSome_eq_decide_mem_map_fst {Q V : Type} [DecidableEq Q]
    (c : List (Q × V)) (s : Q) :
    (c.lookup s).isSome = decide (s ∈ c.map Prod.fst) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.lookup_isSome_iff, beq_iff_eq, decide_eq_true_eq, List.mem_map]
  exact ⟨fun ⟨p, hp, h⟩ => ⟨p, hp, h.symm⟩, fun ⟨p, hp, h⟩ => ⟨p, hp, h.symm⟩⟩

private theorem isSome_of_mem_support_answer {Q V : Type} [DecidableEq Q]
    (d : Q → PMF V) (q s : Q) (c : RandomOracle.Cache (fun _ : Q => V))
    {ac : V × RandomOracle.Cache (fun _ : Q => V)}
    (hac : ac ∈ (RandomOracle.answer d q c).support) :
    (ac.2 s).isSome = ((c s).isSome || decide (q = s)) := by
  cases h : c q with
  | none =>
    simp only [RandomOracle.answer_of_none d c q h, PMF.mem_support_map_iff] at hac
    obtain ⟨v, -, rfl⟩ := hac
    by_cases hqs : s = q
    · subst hqs
      simp
    · simp [Function.update_of_ne hqs, Ne.symm hqs]
  | some v =>
    simp only [RandomOracle.answer_of_some d c q v h, PMF.mem_support_pure_iff] at hac
    subst hac
    by_cases hqs : q = s
    · subst hqs
      simp [h]
    · simp [hqs]

private theorem runWith_memoize_mem_eq_eager_runLog {Q V α : Type} [Fintype Q] [DecidableEq Q]
    [Fintype V] [Nonempty V] (M : ProbOracleComp (fun _ : Q => V) α) (s : Q) :
    ((ProbOracleComp.runWith (memoize fun _ : Q => uniformOfFintype V) M []).map
        fun (_, c) => decide (s ∈ c.map Prod.fst)) =
      (uniformOfFintype (Q → V)).bind fun table =>
        (ProbComp.eval (M.runLog fun q => pure (table q))).map
          fun (_, log) => decide (s ∈ log.map Prod.fst) := by
  let d : Q → PMF V := fun _ => uniformOfFintype V
  have hmem : ((ProbOracleComp.runWith (memoize d) M []).map
      fun (_, c) => decide (s ∈ c.map Prod.fst)) =
      (ProbOracleComp.runWith (RandomOracle.answer d) M (fun _ => none)).map
        fun (_, c) => (c s).isSome := by
    have h := congrArg (PMF.map fun (p : α × RandomOracle.Cache (fun _ : Q => V)) => (p.2 s).isSome)
      (RandomOracle.run_interpret_memoize_prob d M [])
    simpa only [PMF.map_comp, Function.comp_def, RandomOracle.ofList_nil, RandomOracle.ofList,
      lookup_isSome_eq_decide_mem_map_fst] using h
  rw [hmem]
  let hitOracle : Q → StateT ((Q → V) × Bool) PMF V :=
    fun q ⟨table, hit⟩ => PMF.pure (table q, (table, hit || decide (q = s)))
  let relate : RandomOracle.Cache (fun _ : Q => V) → PMF ((Q → V) × Bool) :=
    fun c => (RandomOracle.complete d c).map fun table => (table, (c s).isSome)
  have hsim := ProbOracleComp.runWith_simulation (RandomOracle.answer d) hitOracle relate
    (fun q c => by
      have hcongr : ((RandomOracle.answer d q c).bind fun ⟨a, c'⟩ =>
          (relate c').map (a, ·)) =
          ((RandomOracle.answer d q c).bind fun ⟨a, c'⟩ =>
            (RandomOracle.complete d c').map (a, ·)).map
              fun ⟨a, table⟩ => (a, (table, (c s).isSome || decide (q = s))) := by
        rw [PMF.map_bind]
        refine PMF.bind_congr_on_support _ _ _ fun ac hac => ?_
        simp only [relate, PMF.map_comp, Function.comp_def,
          isSome_of_mem_support_answer d q s c hac]
      rw [hcongr]
      have hcomp := congrArg
        (PMF.map fun ⟨a, table⟩ => (a, (table, (c s).isSome || decide (q = s))))
        (RandomOracle.answer_complete d c q)
      simpa only [relate, hitOracle, PMF.monad_bind_eq_bind, PMF.map_comp, PMF.bind_map,
        Function.comp_def, PMF.pure_bind, PMF.map, PMF.bind_bind] using hcomp)
    M (fun _ => none)
  have hproj := congrArg (PMF.map fun (_, _, hit) => hit) hsim
  have hlhs : (((ProbOracleComp.runWith (RandomOracle.answer d) M (fun _ => none)).bind
      fun ⟨a, c'⟩ => (relate c').map (a, ·)).map fun (_, _, hit) => hit) =
      (ProbOracleComp.runWith (RandomOracle.answer d) M (fun _ => none)).map
        fun (_, c') => (c' s).isSome := by
    rw [PMF.map_bind]
    have hconst (ac : α × RandomOracle.Cache (fun _ : Q => V)) :
        ((relate ac.2).map (ac.1, ·)).map (fun (_, _, hit) => hit) =
          PMF.pure (ac.2 s).isSome := by
      simp only [relate, PMF.map_comp, Function.comp_def]
      exact (RandomOracle.complete d ac.2).map_const (ac.2 s).isSome
    simp only [hconst]
    rfl
  rw [← hlhs, hproj]
  simp only [relate, RandomOracle.complete_empty, d, PMF.pi_uniformOfFintype, PMF.bind_map,
    PMF.map_bind, Function.comp_def, Option.isSome_none]
  refine congrArg ((uniformOfFintype (Q → V)).bind ·) (funext fun table => ?_)
  have hlog : ProbComp.eval (M.runLog fun q => pure (table q)) =
      ProbOracleComp.runWith (fun q log => PMF.pure (table q, log ++ [(q, table q)])) M [] := by
    rw [ProbOracleComp.runLog, ProbOracleComp.eval_runState]
    simp only [ProbComp.eval_map, ProbComp.eval_pure, PMF.pure_map]
  rw [hlog]
  have hstate := ProbOracleComp.runWith_map_state
    (fun q (log : List (Q × V)) => PMF.pure (table q, log ++ [(q, table q)]))
    hitOracle (fun log => (table, decide (s ∈ log.map Prod.fst)))
    (fun q log => by
      simp only [hitOracle, PMF.pure_map, List.map_append, List.map_cons, List.map_nil,
        List.mem_append, List.mem_singleton]
      congr 2
      cases hs : decide (s ∈ List.map Prod.fst log) <;>
        cases hq : decide (q = s) <;> simp_all [eq_comm])
    M []
  have hstate' := congrArg (PMF.map fun (_, _, hit) => hit) hstate
  simpa only [PMF.map_comp, Function.comp_def, List.map_nil, List.not_mem_nil, decide_false] using
    hstate'.symm

private theorem eval_lazyROToListGuess_eq_memoize {X : Type} (secLen outLen : ℕ → ℕ)
    (D : WordRODistinguisher X) (n : ℕ) (x : X) :
    ProbComp.eval (lazyROToListGuess secLen outLen D n x) =
      (uniformOfFintype (BitString (outLen n))).bind fun t =>
        (ProbOracleComp.runWith
          (memoize fun _ : BitString (secLen n) => uniformOfFintype (BitString (outLen n)))
          (toRODistinguisher secLen outLen D n x t) []).map fun (_, c) => c.map Prod.fst := by
  let k := secLen n
  let m := outLen n
  let d : BitString k → PMF (BitString m) := fun _ => uniformOfFintype (BitString m)
  have hkey : BitString.uniformList (outLen n) =
      (uniformOfFintype (BitString (outLen n))).map List.ofFn := rfl
  simp only [lazyROToListGuess, ProbComp.eval_bind, BitString.eval_sampleList,
    ProbOracleComp.eval_runState, ProbComp.eval_pure]
  rw [hkey, PMF.bind_map]
  refine congrArg ((uniformOfFintype (BitString m)).bind ·) (funext fun t => ?_)
  let P := D n x (List.ofFn t)
  let O_typed : Unit × List Bool → StateT (List (BitString k × BitString m)) PMF (List Bool) :=
    fun ⟨_, q⟩ cache =>
      if q.length = k then
        (memoize d (BitString.ofList k q) cache).map fun (v, c') => (List.ofFn v, c')
      else PMF.pure ([], cache)
  have hsim : ProbOracleComp.runWith (memoize d) (toRODistinguisher secLen outLen D n x t) [] =
      ProbOracleComp.runWith O_typed P [] := by
    rw [ProbOracleComp.runWith_eq_run_interpret, ProbOracleComp.runWith_eq_run_interpret]
    unfold toRODistinguisher
    rw [ProbOracleComp.interpret_simulate]
    congr 3
    funext ⟨_, q⟩ cache
    by_cases hq : q.length = k
    · simp only [k, hq, ↓reduceIte, OracleComp.interpret_map, ProbOracleComp.interpret_query,
        O_typed]
      rfl
    · simp only [k, hq, ↓reduceIte, OracleComp.interpret_pure, O_typed]
      rfl
  let represent : List (BitString k × BitString m) → List (List Bool × List Bool) :=
    List.map fun (q, v) => (List.ofFn q, List.ofFn v)
  have hmap := ProbOracleComp.runWith_map_state O_typed
    (fun ⟨_, q⟩ cache => ProbComp.eval (cachedRandomFunctionOracle k m q cache)) represent
    (fun ⟨_, q⟩ cache => by
      by_cases hq : q.length = k
      · simp only [O_typed, cachedRandomFunctionOracle, hq, ↓reduceIte, PMF.map_comp,
          Function.comp_def, ProbComp.eval_memoize, BitString.eval_sampleList]
        have hm := Cslib.memoize_map (encBitString k) List.ofFn d
          (fun _ => BitString.uniformList m) (fun _ => rfl) (BitString.ofList k q) cache
        simpa only [encBitString_apply, BitString.ofFn_ofList hq, PMF.monad_map_eq_map,
          represent] using hm
      · simp only [O_typed, cachedRandomFunctionOracle, hq, ↓reduceIte, PMF.pure_map,
          ProbComp.eval_pure])
    P []
  simp only [represent, List.map_nil] at hmap
  rw [Function.comp_apply, ← hmap, ← hsim, PMF.bind_map]
  simp only [PMF.map, Function.comp_def, List.map_map, BitString.ofList_ofFn]
  rfl

private theorem listGuessOutput_lazyROToListGuess {X : Type} (secLen outLen : ℕ → ℕ)
    (sample : ∀ n, PMF (BitString (secLen n))) (info : ∀ n, BitString (secLen n) → X)
    (D : WordRODistinguisher X) (n : ℕ) :
    listGuessOutput (sample n) (info n) (lazyROToListGuess secLen outLen D n) =
      listGuessOutput (sample n) (info n)
        (roToListGuess (toRODistinguisher secLen outLen D n)) := by
  unfold listGuessOutput
  refine congrArg ((sample n).bind ·) (funext fun s => ?_)
  rw [eval_lazyROToListGuess_eq_memoize]
  unfold roToListGuess
  simp only [ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure, PMF.bind_bind,
    PMF.bind_map, PMF.pure_bind, Function.comp_def]
  rw [PMF.bind_comm]
  refine congrArg ((uniformOfFintype (BitString (outLen n))).bind ·) (funext fun t => ?_)
  have h := runWith_memoize_mem_eq_eager_runLog
    (toRODistinguisher secLen outLen D n (info n s) t) s
  simpa only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def] using h

end LazyEquivalence

/-- **Lazy list-guessing inequality of Theorem 8.10** ([BonehShoup2023], §8.10.2, pp. 331–332):
the random-oracle KDF distinguishing advantage of `toRODistinguisher secLen outLen D n` is at most
the list-guessing advantage of the lazy-simulation wrapper `lazyROToListGuess secLen outLen D n`. -/
theorem roAdvantage_toRODistinguisher_le_listGuessAdvantage {X : Type} (secLen outLen : ℕ → ℕ)
    (sample : ∀ n, PMF (BitString (secLen n))) (info : ∀ n, BitString (secLen n) → X)
    (D : WordRODistinguisher X) (n : ℕ) :
    roAdvantage (sample n) (info n) (toRODistinguisher secLen outLen D n) ≤
      listGuessAdvantage (sample n) (info n) (lazyROToListGuess secLen outLen D n) := by
  rw [listGuessAdvantage, listGuessOutput_lazyROToListGuess, ← listGuessAdvantage]
  exact roAdvantage_le_listGuessAdvantage (sample n) (info n) (toRODistinguisher secLen outLen D n)

/-- **The lazy list-guessing wrapper is efficient**: `lazyROToListGuess secLen outLen D` is uniform
strict PPT whenever `secLen` and `outLen` are computable in polynomial time in unary and `D` is
uniform strict oracle-PPT. -/
theorem isPPT_lazyROToListGuess {X : Type} {encX : X ↪ List Bool} {secLen outLen : ℕ → ℕ}
    (hsec : ComputableInPolyTime secLen encUnary encUnary)
    (hout : ComputableInPolyTime outLen encUnary encUnary)
    {D : WordRODistinguisher X} (hD : D.IsPPT encX) :
    (lazyROToListGuess secLen outLen D).IsPPT encX := by
  let E₀ := encPair encUnary encX
  let E₁ := encPair E₀ encBits
  have hz : IsPPTOn E₀ encBits (fun p : ℕ × X => BitString.sampleList (outLen p.1)) :=
    (hout.comp (ComputableInPolyTime.fst encUnary encX)).sampleList
  have hrun : IsPPTOn E₁ (encPair encBool (encMemoCache encBits encBits))
      (fun c : (ℕ × X) × List Bool =>
        (((D c.1.1 c.1.2 c.2).runState
          fun ⟨_, q⟩ => cachedRandomFunctionOracle (secLen c.1.1) (outLen c.1.1) q).run [])) := by
    have hsec' := hsec.tidy
    have hout' := hout.tidy
    apply hD.isPPTOn_runState (operationEncoding := encFinEnum Unit)
      (prepare := fun c : (ℕ × X) × List Bool => (c.1.1, c.1.2, c.2))
      (resources := fun c q => 4 * q.length + 2 * outLen c.1.1 + 3)
      (by fun_prop) (by fun_prop) (by fun_prop)
      (fun c cache => ∀ entry ∈ cache, entry.2.length ≤ outLen c.1.1) (by simp) (by fun_prop)
    intro c request cache hcache result hresult
    by_cases hquery : request.2.length = secLen c.1.1
    · simp only [cachedRandomFunctionOracle, hquery, ↓reduceIte] at hresult
      rw [ProbComp.eval_memoize] at hresult
      obtain ⟨hreply, hcache', hgrowth⟩ := memoize_call_size_le encBits encBits
        (fun _ => ProbComp.eval (BitString.sampleList (outLen c.1.1))) request.2 cache
        (outLen c.1.1) hcache (fun value hvalue => by
          rw [BitString.eval_sampleList] at hvalue
          exact (BitString.length_of_mem_support_uniformList hvalue).le) result hresult
      exact ⟨hcache', by simpa only [encBits_apply] using hreply.trans (by lia),
        by simpa only [encBits_apply, Nat.add_assoc] using hgrowth⟩
    · simp only [cachedRandomFunctionOracle, hquery, ↓reduceIte, ProbComp.eval_pure,
        PMF.mem_support_pure_iff] at hresult
      subst hresult
      exact ⟨hcache, by simp, by lia⟩
  have hpost : ComputableInPolyTime
      (fun r : Bool × List (List Bool × List Bool) => r.2.map Prod.fst)
      (encPair encBool (encMemoCache encBits encBits)) (encList encBits) := by
    fun_prop
  have hprog : IsPPTOn E₀ (encList encBits) (fun p : ℕ × X => do
      let z ← BitString.sampleList (outLen p.1)
      (fun r : Bool × List (List Bool × List Bool) => r.2.map Prod.fst) <$>
        (((D p.1 p.2 z).runState
          fun ⟨_, q⟩ => cachedRandomFunctionOracle (secLen p.1) (outLen p.1) q).run [])) :=
    hz.bind_with (hrun.map hpost)
  refine hprog.congr fun p => ?_
  simp only [lazyROToListGuess, ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.map_bind, PMF.pure_map]
  refine congrArg ((ProbComp.eval (BitString.sampleList (outLen p.1))).bind ·) (funext fun z => ?_)
  rw [PMF.map]
  refine PMF.bind_congr_on_support _ _ _ fun rc hrc => ?_
  have hkeys := key_length_of_mem_runState_cachedRandomFunctionOracle (secLen p.1) (outLen p.1)
    (D p.1 p.2 z) hrc
  rw [Function.comp_apply]
  congr 1
  rw [List.map_map]
  exact (List.map_congr_left fun entry hentry => BitString.ofFn_ofList (hkeys entry hentry)).symm

/-! ### 4. Lazy singleton-guessing wrapper and computational Theorem 8.10 -/

/-- The elementary lazy-simulation singleton-guessing wrapper `B'` of Theorem 8.10
([BonehShoup2023], §8.10.2, pp. 331–332) with fair-coin modular index sampling: run
`lazyROToListGuess secLen outLen D n x`, draw an index from
`ProbComp.sampleModIndex (width n) (Q n)`, and return the entry at that position (or the all-`false`
`secLen n`-bit string past the end of the list). -/
@[expose] noncomputable def lazyROToGuess {X : Type} (width Q secLen outLen : ℕ → ℕ)
    (D : WordRODistinguisher X) : GuessFamilyAdversary X secLen :=
  fun n x => do
    let l ← lazyROToListGuess secLen outLen D n x
    let i ← ProbComp.sampleModIndex (width n) (Q n)
    return l.getD i (BitString.ofList (secLen n) (List.replicate (secLen n) false))

private theorem ofFn_getD {k : ℕ} (l : List (BitString k)) (i : ℕ) (fallback : BitString k) :
    List.ofFn (l.getD i fallback) = ((l.map List.ofFn)[i]?).getD (List.ofFn fallback) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Option.getD_map]

/-- **The lazy singleton-guessing wrapper is efficient**: `lazyROToGuess width Q secLen outLen D` is
uniform strict PPT whenever `width`, `Q`, `secLen`, and `outLen` are computable in polynomial time
in unary and `D` is uniform strict oracle-PPT. -/
theorem isPPT_lazyROToGuess {X : Type} {encX : X ↪ List Bool} {width Q secLen outLen : ℕ → ℕ}
    (hwidth : ComputableInPolyTime width encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hsec : ComputableInPolyTime secLen encUnary encUnary)
    (hout : ComputableInPolyTime outLen encUnary encUnary)
    {D : WordRODistinguisher X} (hD : D.IsPPT encX) :
    (lazyROToGuess width Q secLen outLen D).IsPPT encX := by
  have hlist := isPPT_lazyROToListGuess hsec hout hD
  let E₀ := encPair encUnary encX
  let E₁ := encPair E₀ (encList encBits)
  have hn : ComputableInPolyTime (fun p : (ℕ × X) × List (List Bool) => p.1.1) E₁ encUnary := by
    fun_prop
  have hsample : IsPPTOn E₁ encUnary (fun p : (ℕ × X) × List (List Bool) =>
      ProbComp.sampleModIndex (width p.1.1) (Q p.1.1)) :=
    isPPTOn_sampleModIndex (hwidth.comp hn) (hQ.comp hn)
  let E₂ := encPair E₁ encUnary
  have hn' : ComputableInPolyTime
      (fun p : ((ℕ × X) × List (List Bool)) × ℕ => p.1.1.1) E₂ encUnary := by fun_prop
  have hwords : ComputableInPolyTime
      (fun p : ((ℕ × X) × List (List Bool)) × ℕ => p.1.2) E₂ (encList encBits) := by fun_prop
  have hi : ComputableInPolyTime
      (fun p : ((ℕ × X) × List (List Bool)) × ℕ => p.2) E₂ encUnary := by fun_prop
  have hfallback : ComputableInPolyTime
      (fun p : ((ℕ × X) × List (List Bool)) × ℕ => List.replicate (secLen p.1.1.1) false)
      E₂ encBits :=
    (bits_encList_polyTime encBool).2.comp
      (ComputableInPolyTime.replicate (hsec.comp hn') (ComputableInPolyTime.const false))
  have hpick : ComputableInPolyTime
      (fun p : ((ℕ × X) × List (List Bool)) × ℕ =>
        (p.1.2[p.2]?).getD (List.replicate (secLen p.1.1.1) false)) E₂ encBits :=
    ComputableInPolyTime.optionGetDWithInput (ComputableInPolyTime.getElem? hwords hi) hfallback
  have hprog : IsPPTOn E₀ encBits (fun p : ℕ × X => do
      let words ← List.map List.ofFn <$> lazyROToListGuess secLen outLen D p.1 p.2
      (fun i => (words[i]?).getD (List.replicate (secLen p.1) false)) <$>
        ProbComp.sampleModIndex (width p.1) (Q p.1)) :=
    hlist.bind_with (hsample.map_with hpick)
  refine hprog.congr fun p => ?_
  have hrep : List.ofFn (BitString.ofList (secLen p.1) (List.replicate (secLen p.1) false)) =
      List.replicate (secLen p.1) false := BitString.ofFn_ofList (by simp)
  simp only [lazyROToGuess, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
    PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def, ofFn_getD, hrep]

/-- **Lazy singleton-guessing inequality of Theorem 8.10** ([BonehShoup2023], §8.10.2,
pp. 331–332): when `D n (info n s) z` makes at most `Q n` oracle queries on every supported secret
`s` and `outLen n`-bit key `z`, the random-oracle KDF distinguishing advantage is at most
`Q n * guessAdvantage (sample n) (info n) (lazyROToGuess width Q secLen outLen D n) +
Q n / 2 ^ width n`, where `Q n / 2 ^ width n` is the fair-coin modular index-sampling bias. -/
theorem roAdvantage_toRODistinguisher_le_mul_guessAdvantage_add {X : Type}
    (width Q secLen outLen : ℕ → ℕ) (sample : ∀ n, PMF (BitString (secLen n)))
    (info : ∀ n, BitString (secLen n) → X) (D : WordRODistinguisher X) (n : ℕ)
    (hQ : ∀ s ∈ (sample n).support, ∀ z : List Bool, z.length = outLen n →
      (D n (info n s) z).IsQueryBounded (Q n)) :
    roAdvantage (sample n) (info n) (toRODistinguisher secLen outLen D n) ≤
      Q n * guessAdvantage (sample n) (info n) (lazyROToGuess width Q secLen outLen D n) +
        Q n / 2 ^ width n := by
  refine (roAdvantage_toRODistinguisher_le_listGuessAdvantage secLen outLen sample info D n).trans
    ?_
  let fallback := BitString.ofList (secLen n) (List.replicate (secLen n) false)
  have hle : listGuessOutput (sample n) (info n) (lazyROToListGuess secLen outLen D n) true ≤
      (Q n : ℝ≥0∞) *
        guessOutput (sample n) (info n) (lazyROToGuess width Q secLen outLen D n) true +
          (Q n : ℝ≥0∞) / 2 ^ width n := by
    unfold listGuessOutput guessOutput lazyROToGuess
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
    refine PMF.bind_apply_le_mul_bind_apply_add_on_support (sample n) fun s hs => ?_
    refine PMF.bind_apply_le_mul_bind_apply_add_on_support _ fun l hl => ?_
    have hlen : l.length ≤ Q n := length_le_of_mem_support_lazyROToListGuess (hQ s hs) hl
    have hmap : ((ProbComp.eval (ProbComp.sampleModIndex (width n) (Q n))).bind fun i =>
        PMF.pure (decide (l.getD i fallback = s))) =
        ((ProbComp.eval (ProbComp.sampleModIndex (width n) (Q n))).map
          fun i => l.getD i fallback).bind fun s' => PMF.pure (decide (s' = s)) := by
      rw [PMF.bind_map]
      rfl
    rw [hmap, Cslib.Probability.PMF.bind_pure_decide_eq_apply_true']
    by_cases hmem : s ∈ l
    · have htake : s ∈ l.take (Q n) := by rwa [List.take_of_length_le hlen]
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem htake
      rw [List.length_take] at hi
      have hiQ : i < Q n := hi.trans_le (min_le_left _ _)
      have hil : i < l.length := hi.trans_le (min_le_right _ _)
      rw [ProbComp.sampleModIndex_eq_sampleModNat (width n) ((Nat.zero_le i).trans_lt hiQ)]
      have h1 : (PMF.pure (decide ((l.take (Q n))[i] ∈ l))) true = 1 := by simp
      rw [h1]
      calc (1 : ℝ≥0∞) ≤
            (Q n : ℝ≥0∞) * ProbComp.eval (ProbComp.sampleModNat (width n) (Q n)) i +
              (Q n : ℝ≥0∞) / 2 ^ width n :=
            ProbComp.one_le_mul_eval_sampleModNat_add hiQ
        _ ≤ _ := by
            gcongr
            have hget : (l.take (Q n))[i] = l.getD i fallback := by
              simp [List.getElem_take, List.getD_eq_getElem?_getD, hil]
            rw [hget]
            exact PMF.le_map_apply _ (fun j => l.getD j fallback) i
    · simp [hmem]
  simp only [listGuessAdvantage, guessAdvantage, Game.succProbability]
  rw [← ENNReal.coe_le_coe]
  push_cast [ENNReal.coe_toNNReal (PMF.apply_ne_top _ _),
    ENNReal.coe_div (pow_ne_zero _ two_ne_zero)]
  exact hle

/-- **Computational Theorem 8.10** ([BonehShoup2023], §8.10.2, pp. 331–332, with §8.10.1, Attack
Game 8.3, p. 326): if a secret source is computationally unpredictable (`SecretGuessHard`),
`secLen` and `outLen` are computable in polynomial time in unary, and `encX (info n s)` has
polynomial length in `n` on `(sample n).support`, then every uniform strict oracle-PPT word
distinguisher has negligible random-oracle KDF distinguishing advantage. -/
theorem SecretGuessHard.negligible_roAdvantage {X : Type} {encX : X ↪ List Bool}
    {secLen outLen : ℕ → ℕ} {sample : ∀ n, PMF (BitString (secLen n))}
    {info : ∀ n, BitString (secLen n) → X}
    (hguess : SecretGuessHard encX secLen sample info)
    (hsec : ComputableInPolyTime secLen encUnary encUnary)
    (hout : ComputableInPolyTime outLen encUnary encUnary)
    (hinfo : ∃ c d, ∀ n s, s ∈ (sample n).support →
      (encX (info n s)).length ≤ c * (n + 1) ^ d)
    {D : WordRODistinguisher X} (hD : D.IsPPT encX) :
    Negligible fun n => roAdvantage (sample n) (info n) (toRODistinguisher secLen outLen D n) := by
  obtain ⟨ci, di, hinfo⟩ := hinfo
  obtain ⟨cD, dD, hbounds⟩ := hD.query_bounds
  let M : ℕ → ℕ := fun n => 2 * n + 2 * (ci * (n + 1) ^ di) + outLen n + 2
  let Q : ℕ → ℕ := fun n => cD * (M n + 1) ^ dD
  have hQ : ComputableInPolyTime Q encUnary encUnary := by
    have hout' := hout.tidy
    exact .of_tidy (by fun_prop)
  have hDz : ∀ n, ∀ s ∈ (sample n).support, ∀ z : List Bool, z.length = outLen n →
      (D n (info n s) z).IsQueryBounded (Q n) := by
    intro n s hs z hz
    refine (hbounds (n, info n s, z)).1.mono ?_
    have his := hinfo n s hs
    have hlen : (encPair encUnary (encPair encX encBits) (n, info n s, z)).length ≤ M n := by
      dsimp only [M]
      enc_len [hz]
    exact Nat.mul_le_mul_left cD (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) dD)
  have hguess_red := hguess _ (isPPT_lazyROToGuess (width := fun n => n) .id' hQ hsec hout hD)
  negligible using fun n =>
    roAdvantage_toRODistinguisher_le_mul_guessAdvantage_add (fun n => n) Q secLen outLen
      sample info D n (hDz n)

end Cslib.Crypto.KeyDerivation
