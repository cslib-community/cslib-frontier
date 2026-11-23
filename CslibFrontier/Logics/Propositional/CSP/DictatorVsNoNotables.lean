/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Boolean
public import CslibFrontier.Logics.Propositional.CSP.RandomizedAssignment
public import CslibFrontier.Foundations.BooleanAnalysis.StableInfluence

/-!
# Dictator-vs.-No-Notables tests

A tester for Boolean functions `f : (Fin n → Bool) → Bool` that picks one of finitely many checks
uniformly at random, queries `f` at the strings of the check and accepts when the check's
predicate holds of the answers is a CSP instance whose variables are the `2 ^ n` strings
[O'Donnell, Section 7.3, p. 187][ODonnell2014]: an assignment of the variables is a function `f`,
and the test accepts `f` with probability its value `satFraction`. A
**Dictator-vs.-No-Notables test** [O'Donnell, Definition 7.37][ODonnell2014] using a finite set
`Ψ` of predicates is a family of such tests, one for each `n ≥ 1`, whose checks apply predicates of
`Ψ`, that accepts dictators with probability at least `β` and accepts functions with no
`(ε, ε)`-notable coordinates, those whose every `(1 - ε)`-stable influence is at most `ε`, with
probability at most `α + err(ε)`, for an error `err(ε) → 0` as `ε → 0⁺` that does not depend on
`n` (`Logic.PL.CSP.IsDictatorVsNoNotables`).

`Ψ` is a fixed constraint language: a finite type `Rel` of relation symbols with arities
`arity : Rel → ℕ` and truth tables `sem : Rel → List Bool → Bool`, as in
`Logic.PL.CSP.WellFormed`. A test uses predicates from `Ψ` when it is a `CSP Rel (Fin n → Bool)`
whose scopes have the declared arities. The definition includes both amendments of
[O'Donnell, Remark 7.38][ODonnell2014]: the strings of a check need not be distinct, since scopes
may repeat variables, and soundness is required for every `g` with values in `[-1, 1]`, whose
acceptance probability is the value `expectedSatFraction` of `g` as a randomized assignment: each
query of `g` at `w` returns an independent random sign with mean `g w`
[O'Donnell, Exercise 7.22][ODonnell2014]. On Boolean functions, read as signs, this is the
soundness clause of Definition 7.37
(`Logic.PL.CSP.IsDictatorVsNoNotables.exists_error_satFraction`).

Such tests are the input to [O'Donnell, Theorem 7.40][ODonnell2014], which turns an
`(α, β)`-Dictator-vs.-No-Notables test using predicates from `Ψ` into UG-hardness of
`(α + δ, β - δ)`-approximating `Max-CSP(Ψ)`, that is NP-hardness assuming the Unique Games
Conjecture. `CslibFrontier.Computability.PCP.Approximation.LabelCover` states a form of that
conjecture, whose instances may have loops, as `Complexity.UniqueGamesConjecture` (with the gap
problem `Complexity.GapUniqueGames`); Theorem 7.40 itself is not formalized here.
Håstad's test is an instance (`Logic.PL.CSP.isDictatorVsNoNotables_hastadTest`).

## Usage

Open `Cslib.Logic.PL.CSP`. `Logic.PL.CSP.IsDictatorVsNoNotables` is a structure: use its fields
`finite`, `pos`, `lt`, `le_one`, `wellFormed`, `le_satFraction_dictator` and `exists_error`, or
`Logic.PL.CSP.IsDictatorVsNoNotables.exists_error_satFraction` for Boolean functions, rather than
unfolding it, and `Logic.PL.CSP.IsDictatorVsNoNotables.of_le` to lower `β`. The error `err` of
`exists_error` is chosen before `n` (Remark 7.39). The checked clients in
[CslibFrontierTests/BooleanAnalysisHastadTest.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisHastadTest.lean)
show that the definition is not trivial: the empty test, of value `1` on every function, is not
such a test, and neither is the Odd BLR test for any `α < 1`, since large odd parities pass it.

## Main definitions

* `Cslib.Logic.PL.CSP.IsDictatorVsNoNotables`: Dictator-vs.-No-Notables tests.

## Main results

* `Cslib.Logic.PL.CSP.IsDictatorVsNoNotables.exists_error_satFraction`: soundness for Boolean
  functions.
* `Cslib.Logic.PL.CSP.IsDictatorVsNoNotables.of_le`: lowering the completeness threshold.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.Logic.PL.CSP

open Filter Topology Cslib.BitString

variable {Rel : Type*} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool} {α β : ℝ}
  {T : ∀ n : ℕ, CSP Rel (Fin n → Bool)}

variable (arity sem α β T) in
/-- A family of tests `T n`, one on `n` bits for each `n`, each a CSP instance whose variables are
the strings `x : Fin n → Bool`, is an **`(α, β)`-Dictator-vs.-No-Notables test using the predicate
set `Ψ`** [O'Donnell, Definition 7.37 and Remark 7.38][ODonnell2014], where `Ψ` is the constraint
language `Rel` with arities `arity` and truth tables `sem`, if `Rel` is finite, `0 < α < β ≤ 1`,
and:

* for every `n ≥ 1`, the checks of `T n` apply predicates of `Ψ`: every scope has its relation's
  arity, and may repeat strings;
* **completeness**: for every `n`, every dictator `x ↦ x i` passes `T n` with probability at least
  `β`;
* **soundness**: there is an error `err(ε) → 0` as `ε → 0⁺` such that for every `0 < ε ≤ 1`, every
  `n ≥ 1` and every `g` with values in `[-1, 1]` whose `(1 - ε)`-stable influences are all at most
  `ε`, `g` passes `T n` with probability at most `α + err(ε)`; so `err` does not depend on `n`.
  Here `g` passes with the value of `g` as a randomized assignment: each query of `g` at `w`
  returns an independent random sign of mean `g w` [O'Donnell, Exercise 7.22][ODonnell2014].

Signs read `true` as `-1`, so the dictator `x ↦ x i` is the book's `x ↦ xᵢ`, and a Boolean `f` is
the randomized assignment `fun x => signVal (f x)`
(`Logic.PL.CSP.expectedSatFraction_signVal`). The book's error `λ` maps `[0, 1]` to `[0, 1]`;
since passing probabilities lie in `[0, 1]` (`Logic.PL.CSP.expectedSatFraction_mem_Icc`,
`Logic.PL.CSP.satFraction_mem_Icc`), clamping `err` to `[0, 1]` and taking `λ(0) = 1` gives such a
`λ`, as `ε = 0` is excluded here. The book takes `n ≥ 1`; the test `T 0` is unconstrained. An
empty test passes every function with probability `1`, so it meets completeness and fails
soundness. -/
structure IsDictatorVsNoNotables : Prop where
  /-- The predicate set `Ψ` is finite. -/
  finite : Finite Rel
  /-- The soundness threshold `α` is positive. -/
  pos : 0 < α
  /-- The soundness threshold is below the completeness threshold. -/
  lt : α < β
  /-- The completeness threshold is at most one. -/
  le_one : β ≤ 1
  /-- The checks apply predicates of `Ψ`, at their arities. -/
  wellFormed : ∀ n, 0 < n → (T n).WellFormed arity
  /-- **Completeness**: dictators pass with probability at least `β`. -/
  le_satFraction_dictator : ∀ n (i : Fin n), β ≤ (T n).satFraction sem fun x => x i
  /-- **Soundness**: there is an error `err(ε) → 0` as `ε → 0⁺`, independent of `n`, such that
  functions with values in `[-1, 1]` and every `(1 - ε)`-stable influence at most `ε` pass with
  probability at most `α + err(ε)`. -/
  exists_error : ∃ err : ℝ → ℝ, Tendsto err (𝓝[>] 0) (𝓝 0) ∧
    ∀ ε, 0 < ε → ε ≤ 1 → ∀ n, 0 < n → ∀ g : (Fin n → Bool) → ℝ, (∀ x, |g x| ≤ 1) →
      (∀ i, stableInfluence (1 - ε) i g ≤ ε) → (T n).expectedSatFraction sem g ≤ α + err ε

namespace IsDictatorVsNoNotables

/-- **Soundness for Boolean functions** [O'Donnell, Definition 7.37][ODonnell2014]: Boolean
functions whose signs have every `(1 - ε)`-stable influence at most `ε` pass with probability at
most `α + err(ε)`. -/
theorem exists_error_satFraction (h : IsDictatorVsNoNotables arity sem α β T) :
    ∃ err : ℝ → ℝ, Tendsto err (𝓝[>] 0) (𝓝 0) ∧
      ∀ ε, 0 < ε → ε ≤ 1 → ∀ n, 0 < n → ∀ f : (Fin n → Bool) → Bool,
        (∀ i, stableInfluence (1 - ε) i (fun x => signVal (f x)) ≤ ε) →
          (T n).satFraction sem f ≤ α + err ε := by
  obtain ⟨err, herr, hs⟩ := h.exists_error
  refine ⟨err, herr, fun ε hε hε1 n hn f hf => ?_⟩
  rw [← expectedSatFraction_signVal]
  exact hs ε hε hε1 n hn _ (fun x => (abs_signVal _).le) hf

/-- An `(α, β)`-Dictator-vs.-No-Notables test is an `(α, β')` test for every `α < β' ≤ β`. -/
theorem of_le (h : IsDictatorVsNoNotables arity sem α β T) {β' : ℝ} (hα : α < β')
    (hβ : β' ≤ β) : IsDictatorVsNoNotables arity sem α β' T where
  finite := h.finite
  pos := h.pos
  lt := hα
  le_one := hβ.trans h.le_one
  wellFormed := h.wellFormed
  le_satFraction_dictator n i := hβ.trans (h.le_satFraction_dictator n i)
  exists_error := h.exists_error

end IsDictatorVsNoNotables

end Cslib.Logic.PL.CSP
