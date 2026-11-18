/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.List.Binary
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.Oracle.Run
public import CslibFrontier.Languages.Probabilistic.Vector
import CslibFrontier.Foundations.Data.BitString.List.LowBits
import CslibFrontier.Foundations.Data.BitString.WordsOfLength
import CslibFrontier.Languages.Probabilistic.Oracle.Vector
import CslibFrontier.Probability.PMF.Event

/-!
# The brute-force collision finder and its `2 ^ ℓ + 1` hash evaluations

`bruteForceFinder digest ms` computes the digest of each of `s` fixed messages `ms : Fin s → M` with
the oracle program `digest` and returns the first pair of different messages with equal digests
([BonehShoup2023], §8.3, printed pp. 293–294). Like `birthdayFinder` in
`CslibFrontier.Crypto.Computational.CollisionResistant.Birthday`, it reaches the function being
attacked only through its oracle, so a bound on its oracle calls bounds evaluations of that
function; `CslibFrontier.Crypto.Computational.CollisionResistant.GenericAttacks` instead gives the
polynomial-time Turing-machine refutation when `2 ^ ℓ(n)` is polynomial in `n`.

* **Cost.** When each `digest (ms i)` makes at most `c` oracle calls, `bruteForceFinder digest ms`
  makes at most `s * c` on every path (`isQueryBounded_bruteForceFinder`). Specializing to single
  oracle queries on the first `2 ^ ℓ + 1` binary words of length `ℓ + 1` (`BitString.lowBits`),
  `bruteForceHashFinder ℓ` makes at most `2 ^ ℓ + 1` hash evaluations, for every digest length
  `ℓ : ℕ` (`isQueryBounded_bruteForceHashFinder`). Generating the messages and comparing pairs of
  digests in `collidingPair?` are not counted: this is an oracle-call count, not a running time.
* **Success.** By pigeonhole (`isSome_collidingPair?_of_card_lt`), if the `s` messages are distinct
  and their digests under `f` lie in a finite set `D` with `D.card < s`, `bruteForceFinder` run
  against a deterministic oracle realizing `f` returns a collision in `collisionOutputs f` with
  probability `1` (`bruteForceFinder_success`). For `ℓ`-bit digests
  (`D = BitString.wordsOfLength ℓ`, of size `2 ^ ℓ < 2 ^ ℓ + 1`), any `2 ^ ℓ + 1` distinct messages
  give a collision with probability `1` (`bruteForceFinder_two_pow_succ_success`), and
  `bruteForceHashFinder ℓ` finds one for every hash mapping `(ℓ + 1)`-bit words to `ℓ`-bit digests
  (`bruteForceHashFinder_success`). Whatever `s` and `ms`, every output other than `none` is a
  collision (`bruteForceFinder_sound`).

## Differences from [BonehShoup2023]

* The book states brute-force collision search for a hash `H` outputting `ℓ`-bit digests ("for some
  small `ℓ`", illustrating `ℓ = 16` and `2 ^ 16 + 1 = 65537` evaluations) over a message space with
  at least `2 ^ ℓ + 1` messages. Here `bruteForceFinder` takes any `s` messages and any oracle
  program `digest` over any finite target set `D` with `D.card < s`; the `2 ^ ℓ + 1` theorems hold
  for every `ℓ : ℕ`, with `bruteForceHashFinder ℓ` querying the first `2 ^ ℓ + 1` `(ℓ + 1)`-bit
  words (`2 ^ ℓ + 1 ≤ 2 ^ (ℓ + 1)`).
* The book counts evaluations of `H`. Here `isQueryBounded_bruteForceFinder` and
  `isQueryBounded_bruteForceHashFinder` bound external oracle calls
  (`ProbOracleComp.IsQueryBounded`) on every path; message generation and searching the `2 ^ ℓ + 1`
  digests are not counted.

## Main definitions

* `Cslib.Crypto.collidingPair?`: the first pair of different messages with equal digests.
* `Cslib.Crypto.collisionOutputs`: the outputs that are collisions of a function.
* `Cslib.Crypto.bruteForceFinder`: the brute-force collision finder as an oracle program.
* `Cslib.Crypto.bruteForceHashFinder`: single-query brute-force search on `2 ^ ℓ + 1` binary words
  of length `ℓ + 1`.

## Main results

* `Cslib.Crypto.isSome_collidingPair?_of_card_lt`: pigeonhole collision guarantee for
  `collidingPair?`.
* `Cslib.Crypto.isQueryBounded_bruteForceFinder`,
  `Cslib.Crypto.isQueryBounded_bruteForceHashFinder`: worst-case oracle-call bounds `s * c` and
  `2 ^ ℓ + 1`.
* `Cslib.Crypto.eval_run_bruteForceFinder`: deterministic run characterization.
* `Cslib.Crypto.bruteForceFinder_sound`: every output other than `none` is a collision.
* `Cslib.Crypto.bruteForceFinder_success`,
  `Cslib.Crypto.bruteForceFinder_two_pow_succ_success`,
  `Cslib.Crypto.bruteForceHashFinder_success`: probability-`1` collision finding
  ([BonehShoup2023], §8.3, printed pp. 293–294).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], §8.3 (printed pp. 293–294).
-/

public section

namespace Cslib.Crypto

section Search

variable {M T : Type} [DecidableEq M] [DecidableEq T]

/-- The first pair of positions (in lexicographic order) whose digests agree and whose messages
differ, returned as the two messages and their common digest. -/
@[expose] def collidingPair? {s : ℕ} (ms : Fin s → M) (ds : Fin s → T) : Option (M × M × T) :=
  ((List.finRange s ×ˢ List.finRange s).find? fun p => ds p.1 = ds p.2 ∧ ms p.1 ≠ ms p.2).map
    fun p => (ms p.1, ms p.2, ds p.1)

/-- An output `some (m, m', d)` of `collidingPair?` is two different messages that occur among
`ms` with digest `d`. -/
theorem collidingPair?_eq_some {s : ℕ} {ms : Fin s → M} {ds : Fin s → T} {m m' : M} {d : T}
    (h : collidingPair? ms ds = some (m, m', d)) :
    m ≠ m' ∧ ∃ i j, ms i = m ∧ ms j = m' ∧ ds i = d ∧ ds j = d := by
  obtain ⟨p, hp, heq⟩ := Option.map_eq_some_iff.mp h
  have hp' := List.find?_some hp
  simp only [decide_eq_true_eq] at hp'
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  exact ⟨hp'.2, p.1, p.2, rfl, rfl, rfl, hp'.1.symm⟩

/-- `collidingPair?` finds a pair exactly when two positions have equal digests and different
messages. -/
theorem isSome_collidingPair?_iff {s : ℕ} {ms : Fin s → M} {ds : Fin s → T} :
    (collidingPair? ms ds).isSome ↔ ∃ i j, ds i = ds j ∧ ms i ≠ ms j := by
  simp [collidingPair?]

/-- The outputs of a collision finder that are collisions of `f`: two different messages and their
common value. -/
@[expose] def collisionOutputs (f : M → T) : Set (Option (M × M × T)) :=
  {o | ∃ m m', m ≠ m' ∧ f m' = f m ∧ o = some (m, m', f m)}

/-- Any non-`none` output of `collidingPair? ms (fun i => f (ms i))` is a collision of `f` in
`collisionOutputs f`. -/
theorem collidingPair?_mem_collisionOutputs_of_isSome {s : ℕ} {ms : Fin s → M} {f : M → T}
    (h : (collidingPair? ms fun i => f (ms i)).isSome) :
    collidingPair? ms (fun i => f (ms i)) ∈ collisionOutputs f := by
  obtain ⟨⟨m, m', d⟩, hc⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨hne, i, j, rfl, rfl, rfl, hd⟩ := collidingPair?_eq_some hc
  exact ⟨_, _, hne, hd, hc⟩

/-- **Pigeonhole for `collidingPair?`**: among `s` distinct messages whose digests all lie in a
finite set `D` of cardinality strictly less than `s`, two positions have equal digests and
different messages. -/
theorem isSome_collidingPair?_of_card_lt {s : ℕ} {ms : Fin s → M} (hms : Function.Injective ms)
    {ds : Fin s → T} {D : Finset T} (hds : ∀ i, ds i ∈ D) (hlt : D.card < s) :
    (collidingPair? ms ds).isSome := by
  rw [isSome_collidingPair?_iff]
  have hcard : D.card < (Finset.univ : Finset (Fin s)).card := by simpa using hlt
  obtain ⟨i, -, j, -, hij, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard fun i _ => hds i
  exact ⟨i, j, heq, hms.ne hij⟩

end Search

section Finder

variable {Query M T : Type} {spec : Query → Type} [DecidableEq M] [DecidableEq T]

/-- The brute-force collision finder ([BonehShoup2023], §8.3, printed pp. 293–294): compute the
digest of each of `s` fixed messages `ms` with the oracle program `digest`, and return the first
pair of different messages with equal digests, together with their common digest. -/
def bruteForceFinder (digest : M → ProbOracleComp spec T) {s : ℕ} (ms : Fin s → M) :
    ProbOracleComp spec (Option (M × M × T)) := do
  let ds ← OracleComp.pi fun i => digest (ms i)
  return collidingPair? ms ds

/-- **Cost of the brute-force finder.** When each `digest (ms i)` makes at most `c` oracle calls,
the finder makes at most `s * c` on every path. Message generation and the search among the `s`
digests are not counted: this is a count of oracle calls, not a running time. -/
theorem isQueryBounded_bruteForceFinder {digest : M → ProbOracleComp spec T} {s c : ℕ}
    {ms : Fin s → M} (hdigest : ∀ i, ProbOracleComp.IsQueryBounded (digest (ms i)) c) :
    ProbOracleComp.IsQueryBounded (bruteForceFinder digest ms) (s * c) := by
  simpa [bruteForceFinder] using
    (OracleComp.isCostBounded_pi hdigest).bind (m := 0) fun ds =>
      OracleComp.IsCostBounded.pure (collidingPair? ms ds) 0

/-- Against a deterministic oracle `O` under which `digest (ms i)` returns `f (ms i)`, the finder
deterministically returns `collidingPair? ms fun i => f (ms i)`. -/
theorem eval_run_bruteForceFinder {digest : M → ProbOracleComp spec T} (O : (q : Query) → spec q)
    (f : M → T) {s : ℕ} {ms : Fin s → M}
    (hdigest : ∀ i, (digest (ms i)).run (fun x => pure (O x)) = pure (f (ms i))) :
    ProbComp.eval ((bruteForceFinder digest ms).run fun x => pure (O x)) =
      PMF.pure (collidingPair? ms fun i => f (ms i)) := by
  simp only [bruteForceFinder, ProbOracleComp.run_bind, ProbOracleComp.run_pi, hdigest,
    ProbOracleComp.run_pure, ProbComp.eval_bind, ProbComp.eval_pi_pure, ProbComp.eval_pure,
    PMF.pure_bind]

/-- The finder never returns a wrong pair: against a deterministic oracle under which
`digest (ms i)` returns `f (ms i)`, every output other than `none` is a collision of `f`. -/
theorem bruteForceFinder_sound {digest : M → ProbOracleComp spec T} (O : (q : Query) → spec q)
    (f : M → T) {s : ℕ} {ms : Fin s → M}
    (hdigest : ∀ i, (digest (ms i)).run (fun x => pure (O x)) = pure (f (ms i)))
    {o : Option (M × M × T)}
    (ho : o ∈ (ProbComp.eval ((bruteForceFinder digest ms).run
      fun x => pure (O x))).support) (hne : o ≠ none) : o ∈ collisionOutputs f := by
  rw [eval_run_bruteForceFinder O f hdigest, PMF.mem_support_pure_iff] at ho
  subst ho
  exact collidingPair?_mem_collisionOutputs_of_isSome (Option.isSome_iff_ne_none.mpr hne)

/-- **Success of the brute-force finder.** Against a deterministic oracle under which
`digest (ms i)` returns `f (ms i)`, if `ms` consists of `s` distinct messages whose digests all lie
in a finite set `D` with `D.card < s`, the finder returns a collision of `f` with probability
`1`. -/
theorem bruteForceFinder_success {digest : M → ProbOracleComp spec T} (O : (q : Query) → spec q)
    (f : M → T) {s : ℕ} {ms : Fin s → M} (hms : Function.Injective ms)
    (hdigest : ∀ i, (digest (ms i)).run (fun x => pure (O x)) = pure (f (ms i)))
    (D : Finset T) (hf : ∀ i, f (ms i) ∈ D) (hlt : D.card < s) :
    (ProbComp.eval ((bruteForceFinder digest ms).run fun x => pure (O x))).toOuterMeasure
      (collisionOutputs f) = 1 := by
  rw [eval_run_bruteForceFinder O f hdigest, PMF.toOuterMeasure_pure_apply,
    ite_eq_left (collidingPair?_mem_collisionOutputs_of_isSome
      (isSome_collidingPair?_of_card_lt hms hf hlt))]

end Finder

section BitDigests

/-- **Brute force on `2 ^ ℓ + 1` distinct messages with `ℓ`-bit digests**
([BonehShoup2023], §8.3, printed pp. 293–294): for every digest length `ℓ : ℕ`, evaluating any
`2 ^ ℓ + 1` distinct messages whose digests have length `ℓ` finds a collision of `f` with
probability `1`. With `isQueryBounded_bruteForceFinder`, this uses at most `(2 ^ ℓ + 1) * c` oracle
calls when each digest makes at most `c`. -/
theorem bruteForceFinder_two_pow_succ_success {Query M : Type} {spec : Query → Type}
    [DecidableEq M] {digest : M → ProbOracleComp spec (List Bool)} (O : (q : Query) → spec q)
    (f : M → List Bool) {ℓ : ℕ} {ms : Fin (2 ^ ℓ + 1) → M} (hms : Function.Injective ms)
    (hdigest : ∀ i, (digest (ms i)).run (fun x => pure (O x)) = pure (f (ms i)))
    (hlen : ∀ i, (f (ms i)).length = ℓ) :
    (ProbComp.eval ((bruteForceFinder digest ms).run fun x => pure (O x))).toOuterMeasure
      (collisionOutputs f) = 1 :=
  bruteForceFinder_success O f hms hdigest (BitString.wordsOfLength ℓ)
    (fun i => BitString.mem_wordsOfLength.mpr (hlen i))
    (by rw [BitString.card_wordsOfLength]; exact Nat.lt_succ_self _)

/-- Single-query brute-force collision search for `ℓ`-bit digests ([BonehShoup2023], §8.3, printed
pp. 293–294): query the hash oracle once on each of the first `2 ^ ℓ + 1` binary words of length
`ℓ + 1` (`BitString.lowBits (ℓ + 1)`) and return the first colliding pair and its digest. -/
@[expose] def bruteForceHashFinder (ℓ : ℕ) :
    ProbOracleComp (fun _ : List Bool => List Bool)
      (Option (List Bool × List Bool × List Bool)) :=
  bruteForceFinder ProbOracleComp.query fun i : Fin (2 ^ ℓ + 1) => BitString.lowBits (ℓ + 1) i

/-- **Cost of `bruteForceHashFinder`** ([BonehShoup2023], §8.3, printed pp. 293–294): for every
digest length `ℓ : ℕ`, `bruteForceHashFinder ℓ` makes at most `2 ^ ℓ + 1` hash queries on every
path. Generating the `(ℓ + 1)`-bit messages and comparing digests are not counted. -/
theorem isQueryBounded_bruteForceHashFinder (ℓ : ℕ) :
    ProbOracleComp.IsQueryBounded (bruteForceHashFinder ℓ) (2 ^ ℓ + 1) := by
  simpa [bruteForceHashFinder] using
    isQueryBounded_bruteForceFinder (spec := fun _ : List Bool => List Bool) (c := 1)
      (ms := fun i : Fin (2 ^ ℓ + 1) => BitString.lowBits (ℓ + 1) i)
      fun _ => ProbOracleComp.IsQueryBounded.query _

/-- **Success of `bruteForceHashFinder`** ([BonehShoup2023], §8.3, printed pp. 293–294): for every
digest length `ℓ : ℕ` and every hash `H : List Bool → List Bool` mapping `(ℓ + 1)`-bit words to
`ℓ`-bit digests, `bruteForceHashFinder ℓ` returns a collision of `H` with probability `1` using at
most `2 ^ ℓ + 1` evaluations of `H` (`isQueryBounded_bruteForceHashFinder`). -/
theorem bruteForceHashFinder_success (ℓ : ℕ) (H : List Bool → List Bool)
    (hlen : ∀ m, m.length = ℓ + 1 → (H m).length = ℓ) :
    (ProbComp.eval ((bruteForceHashFinder ℓ).run fun m => pure (H m))).toOuterMeasure
      (collisionOutputs H) = 1 := by
  have hle : 2 ^ ℓ + 1 ≤ 2 ^ (ℓ + 1) := by
    rw [Nat.pow_succ]
    have := Nat.one_le_two_pow (n := ℓ)
    omega
  have hinj : Function.Injective fun i : Fin (2 ^ ℓ + 1) => BitString.lowBits (ℓ + 1) i :=
    fun i j hij => Fin.ext
      (BitString.lowBits_injective_of_lt (i.isLt.trans_le hle) (j.isLt.trans_le hle) hij)
  exact bruteForceFinder_two_pow_succ_success H H hinj (fun _ => ProbOracleComp.run_query _ _)
    fun i => hlen _ (BitString.length_lowBits _ _)

end BitDigests

end Cslib.Crypto
