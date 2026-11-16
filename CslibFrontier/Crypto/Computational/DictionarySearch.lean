/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.EvalPure
public import CslibFrontier.Languages.Probabilistic.QueryCount
public import CslibFrontier.Crypto.Game.Inversion
import CslibFrontier.Foundations.Control.Monad.FindM
import CslibFrontier.Languages.Probabilistic.Traverse.FindM
import CslibFrontier.Languages.Probabilistic.Traverse.SupportWith

/-!
# Dictionary searches against a hash oracle

Offline dictionary attacks `(18.1)`–`(18.3)` of [BonehShoup2023], Section 18.3.1.2–18.3.1.3
(pp. 721–723), together with the salted and secret-salt forms of Section 18.4.1–18.4.2
(pp. 724–726), modeled as programs with oracle access to `H : X → Y`.

`dictionarySearch input accept D` queries the oracle at `input w` for each `w` in `D` in list order
and stops at the first candidate whose reply satisfies `accept`. `dictionaryPreimageSearch`
specializes `accept` to equality with `vk` (`(18.1)`). `dictionaryTable` builds the preprocessing
table of `(H (input w), w)` pairs (`(18.2)`), and `dictionaryBatchSearch` runs one table lookup
per entry of `F` (`(18.3)`). `dictionaryInverter` turns `dictionaryPreimageSearch` into a `PMF`
inverter for `inversionExperiment`.

This formalization differs from the book's presentation as follows:

1. **List order.** `D` is a `List P` searched in list order rather than an unordered set; a `Finset`
   dictionary is handled via `Finset.toList`.
2. **Exact oracle-query counts.** `H` is an oracle and cost is `OracleComp.IsQueryBounded`, giving
   exact bounds `D.length` and `F.length * D.length` instead of `O(|D|)` and `O(|D| × |F|)`.
3. **Failure output.** Searches return `Option P` (`none` when no candidate passes), where `(18.1)`
   prints no output and `(18.2)` prints "fail".
4. **Parameterized input and test.** `dictionarySearch` takes `input : P → X` and
   `accept : Y → Bool`; `(18.1)` is `input := id` and `accept := fun y => decide (y = vk)`, while
   `input := (·, salt)` gives the salted search.
5. **Hash-keyed table.** `dictionaryTable` stores `(H (input w), w)` rather than `(w, H(w))` and
   is read by `List.lookup`. Lookups, comparisons, and `accept` are uncounted; no constant-time
   lookup is claimed.
6. **Batch bound.** `(18.3)`'s "attack time `O(|F|)`" appears only as `D.length` oracle calls
   regardless of `F`; `O(|D| + |F|)` vs `O(|D| × |F|)` appears as two upper bounds, without claiming
   the second bound is attained for every input.
7. **Weak-secret distribution.** `le_inversionExperiment_dictionaryInverter` formalizes choosing a
   weak secret from an arbitrary distribution `μ` over a small dictionary; the resulting
   probability lower bound `μ.toOuterMeasure {pw | pw ∈ D} ≤ ...` is this library's (the book
   states no probability, only the pointwise claim on p. 722 that if `pw ∈ D` the adversary obtains
   `pw` or some `pw'` with `H(pw) = H(pw')` in time `O(|D|)`).
8. **Total `PMF` inverter.** `dictionaryInverter` returns `default` when the search fails;
   `[Inhabited P]` is needed only there.
9. **Recovering `pw` itself.** Returning `pw` (rather than some `w ∈ D` with `H (input w) = vk`)
   is proved only under `Set.InjOn` of `w ↦ H (input w)` on `D`; "in all likelihood" is not
   claimed.
10. **Salts and peppers.** Salt and pepper spaces are parameters of the test instances; the book's
    factor `4096` is `peppers.length`.
11. **Universe `Type`.** All types live in `Type` (`0`), as `OracleComp` requires.

No machine-time bound is certified here: comparisons, `accept`, and `List.lookup` are free, and no
polynomial-time certificate is stated (`D` is a parameter, and efficiency means "`D.length` oracle
evaluations").

## Main definitions

* `Cslib.Crypto.dictionarySearch`: offline search `(18.1)` over `D` with derived input `input`
  and reply test `accept`.
* `Cslib.Crypto.dictionaryTable`: preprocessing phase of `(18.2)` producing `(H (input w), w)`
  pairs.
* `Cslib.Crypto.dictionaryPreimageSearch`: search `(18.1)` specialized to testing `y = vk`.
* `Cslib.Crypto.dictionaryBatchSearch`: batch search `(18.3)` building one table and looking up
  every entry of `F`.
* `Cslib.Crypto.dictionaryInverter`: `PMF` inverter obtained by running `dictionaryPreimageSearch`
  against `H`, returning `default` on `none`.

## Main results

* `Cslib.Crypto.evalPure_dictionarySearch`: output characterization of `dictionarySearch` against
  `H` (`List.find?`).
* `Cslib.Crypto.isQueryBounded_dictionarySearch`,
  `Cslib.Crypto.not_isQueryBounded_dictionarySearch`,
  `Cslib.Crypto.queriesSatisfy_dictionarySearch`: at most `D.length` oracle calls on every path, all
  at `input w` for `w ∈ D`; no smaller bound holds when `accept` rejects some reply.
* `Cslib.Crypto.exists_evalPure_dictionarySearch_of_mem`,
  `Cslib.Crypto.evalPure_dictionarySearch_of_unique`: success when the secret lies in `D` and
  passes `accept`.
* `Cslib.Crypto.evalPure_dictionaryTable`, `Cslib.Crypto.isQueryBounded_dictionaryTable`,
  `Cslib.Crypto.lookup_evalPure_dictionaryTable`: table correctness, cost `D.length`, and
  equivalence of `List.lookup` with `dictionaryPreimageSearch`.
* `Cslib.Crypto.evalPure_dictionaryBatchSearch`,
  `Cslib.Crypto.isQueryBounded_dictionaryBatchSearch`,
  `Cslib.Crypto.isQueryBounded_mapM_dictionaryPreimageSearch`: batch search matches separate
  searches in `D.length` calls vs `F.length * D.length`.
* `Cslib.Crypto.le_inversionExperiment_dictionaryInverter`,
  `Cslib.Crypto.dictionarySearch_inverts`: for any secret distribution `μ`, the search wins
  `inversionExperiment` with probability at least `μ {pw | pw ∈ D}` using at most `D.length`
  calls on every challenge.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 18.3.1.2–18.3.1.3, pp. 721–723, and Section 18.4.1–18.4.2, pp. 724–726.
-/

public section

namespace Cslib.Crypto

open Cslib

variable {P X Y : Type}

/-- The search (18.1) with any derived input and any test of the reply: for each candidate `w` of
`D` in order, ask the oracle at `input w` and stop at the first `w` whose reply passes
`accept`. -/
def dictionarySearch (input : P → X) (accept : Y → Bool) (D : List P) :
    OracleComp (fun _ : X => Y) (Option P) :=
  D.findM? fun w => accept <$> OracleComp.query (spec := fun _ : X => Y) (input w)

section Search

variable (H : X → Y) (input : P → X) (accept : Y → Bool) (D : List P)

/-- Against `H`, the search returns the first candidate that passes. -/
theorem evalPure_dictionarySearch :
    (dictionarySearch input accept D).evalPure H = D.find? fun w => accept (H (input w)) := by
  simp [dictionarySearch, OracleComp.evalPure_findM?, OracleComp.evalPure_map,
    OracleComp.evalPure_query]

/-- **Cost of (18.1).** At most one oracle call per candidate, on every path. -/
theorem isQueryBounded_dictionarySearch :
    OracleComp.IsQueryBounded (dictionarySearch input accept D) D.length := by
  have h := OracleComp.IsCostBounded.findM? (cost := fun _ : X => 1) (xs := D) (n := 1)
    (test := fun w => accept <$> OracleComp.query (spec := fun _ : X => Y) (input w))
    fun w _ => (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)
  rwa [Nat.mul_one] at h

/-- The search asks the oracle only at inputs of candidates. -/
theorem queriesSatisfy_dictionarySearch :
    OracleComp.QueriesSatisfy (fun x => ∃ w ∈ D, input w = x) (dictionarySearch input accept D) :=
  OracleComp.QueriesSatisfy.findM? fun w hw =>
    (OracleComp.queriesSatisfy_map_iff _ _).mpr (OracleComp.QueriesSatisfy.query ⟨w, hw, rfl⟩)

variable {H input accept D}

/-- An output is a candidate of the dictionary that passes the test. -/
theorem dictionarySearch_sound {w : P}
    (h : (dictionarySearch input accept D).evalPure H = some w) :
    w ∈ D ∧ accept (H (input w)) = true := by
  rw [evalPure_dictionarySearch] at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- The search fails exactly when no candidate passes. -/
theorem evalPure_dictionarySearch_eq_none_iff :
    (dictionarySearch input accept D).evalPure H = none ↔
      ∀ w ∈ D, accept (H (input w)) = false := by
  rw [evalPure_dictionarySearch]
  simp

/-- **Success of (18.1).** If the secret is in the dictionary and passes the test, the search
returns a candidate that passes: the secret, or another candidate the test cannot tell from
it. -/
theorem exists_evalPure_dictionarySearch_of_mem {pw : P} (hmem : pw ∈ D)
    (hpw : accept (H (input pw)) = true) :
    ∃ w ∈ D, (dictionarySearch input accept D).evalPure H = some w ∧
      accept (H (input w)) = true := by
  cases hfind : (dictionarySearch input accept D).evalPure H with
  | none => exact absurd hpw (by simp [evalPure_dictionarySearch_eq_none_iff.mp hfind pw hmem])
  | some w => exact ⟨w, (dictionarySearch_sound hfind).1, rfl, (dictionarySearch_sound hfind).2⟩

/-- When only the secret passes, the search returns the secret. -/
theorem evalPure_dictionarySearch_of_unique {pw : P} (hmem : pw ∈ D)
    (hpw : accept (H (input pw)) = true)
    (huniq : ∀ w ∈ D, accept (H (input w)) = true → w = pw) :
    (dictionarySearch input accept D).evalPure H = some pw := by
  obtain ⟨w, hw, hfind, hacc⟩ := exists_evalPure_dictionarySearch_of_mem (H := H) hmem hpw
  rw [hfind, huniq w hw hacc]

/-- One step of the search. -/
theorem dictionarySearch_cons (input : P → X) (accept : Y → Bool) (w : P) (ws : List P) :
    dictionarySearch input accept (w :: ws) =
      OracleComp.query (spec := fun _ : X => Y) (input w) >>= fun y =>
        if accept y then pure (some w) else dictionarySearch input accept ws := by
  simp only [dictionarySearch, List.findM?_cons, bind_map_left]

/-- **The count is sharp.** If `accept` rejects some reply, no budget below `D.length` bounds the
search. -/
theorem not_isQueryBounded_dictionarySearch {input : P → X} {accept : Y → Bool} {D : List P}
    {y₀ : Y} (hy : accept y₀ = false) {n : ℕ} (hn : n < D.length) :
    ¬ OracleComp.IsQueryBounded (dictionarySearch input accept D) n := by
  induction D generalizing n with
  | nil => simp at hn
  | cons w ws ih =>
    intro h
    rw [dictionarySearch_cons] at h
    obtain ⟨hle, hcont⟩ := OracleComp.IsCostBounded.liftBind_iff.mp h
    have h₀ : OracleComp.IsCostBounded (fun _ => 1)
        (if accept y₀ = true then pure (some w) else dictionarySearch input accept ws)
        (n - 1) := hcont y₀
    simp only [hy, Bool.false_eq_true, ↓reduceIte] at h₀
    exact ih (n := n - 1)
      (by simp only [List.length_cons] at hn; omega) h₀

end Search

section Table

/-- **Preprocessing phase of (18.2).** The list of pairs `(H (input w), w)` for `w` in `D`, in the
order of `D` and keyed by the hash, so that the attack phase is `List.lookup`. -/
def dictionaryTable (input : P → X) (D : List P) : OracleComp (fun _ : X => Y) (List (Y × P)) :=
  D.mapM fun w => (fun y => (y, w)) <$> OracleComp.query (spec := fun _ : X => Y) (input w)

/-- Against `H`, the table lists each candidate with its hash. -/
theorem evalPure_dictionaryTable (H : X → Y) (input : P → X) (D : List P) :
    (dictionaryTable input D).evalPure H = D.map fun w => (H (input w), w) := by
  simp [dictionaryTable, OracleComp.evalPure_map, OracleComp.evalPure_query]

/-- **Cost of the preprocessing phase.** One oracle call per candidate. -/
theorem isQueryBounded_dictionaryTable (input : P → X) (D : List P) :
    OracleComp.IsQueryBounded (dictionaryTable (Y := Y) input D) D.length := by
  have h := OracleComp.IsCostBounded.mapM (cost := fun _ : X => 1) (inputs := D) (n := 1)
    (program := fun w => (fun y : Y => (y, w)) <$>
      OracleComp.query (spec := fun _ : X => Y) (input w))
    fun w _ => (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)
  rwa [Nat.mul_one] at h

end Table

section Preimage

variable [DecidableEq Y]

/-- The search (18.1): the first `w` in `D` with `H (input w) = vk`. With `input := id` this is the
book's procedure; `input := (·, salt)` is its salted form. -/
abbrev dictionaryPreimageSearch (input : P → X) (vk : Y) (D : List P) :
    OracleComp (fun _ : X => Y) (Option P) :=
  dictionarySearch input (fun y => decide (y = vk)) D

variable (H : X → Y) (input : P → X) (D : List P)

/-- The book's claim after (18.1): if `pw ∈ D`, the search on `vk = H(pw)` returns `pw` or some
`pw'` with `H(pw') = H(pw)`. -/
theorem exists_evalPure_dictionaryPreimageSearch_of_mem {pw : P} (hmem : pw ∈ D) :
    ∃ w ∈ D, (dictionaryPreimageSearch input (H (input pw)) D).evalPure H = some w ∧
      H (input w) = H (input pw) := by
  obtain ⟨w, hw, hfind, hacc⟩ := exists_evalPure_dictionarySearch_of_mem (H := H)
    (input := input) (accept := fun y => decide (y = H (input pw))) hmem (by simp)
  exact ⟨w, hw, hfind, by simpa using hacc⟩

/-- Without collisions on the dictionary the search returns `pw`. -/
theorem evalPure_dictionaryPreimageSearch_of_injOn {pw : P} (hmem : pw ∈ D)
    (hinj : Set.InjOn (fun w => H (input w)) {w | w ∈ D}) :
    (dictionaryPreimageSearch input (H (input pw)) D).evalPure H = some pw :=
  evalPure_dictionarySearch_of_unique hmem (by simp) fun w hw hacc =>
    hinj hw hmem (by simpa using hacc)

/-- **Attack phase of (18.2).** Looking `vk` up in the table of `D` returns what the search (18.1)
returns. The lookup is core's `List.lookup`, a function of the table and `vk` alone: it has no
access to the oracle. -/
theorem lookup_evalPure_dictionaryTable (vk : Y) :
    ((dictionaryTable input D).evalPure H).lookup vk =
      (dictionaryPreimageSearch input vk D).evalPure H := by
  rw [evalPure_dictionaryTable, evalPure_dictionarySearch, List.lookup_eq_findSome?,
    List.findSome?_map, List.find?_eq_findSome?_guard]
  congr 1
  funext w
  simp [Option.guard, @eq_comm _ vk]

/-- **The batch search (18.3).** One table, then one lookup for each entry of `F`. -/
def dictionaryBatchSearch (input : P → X) (D : List P) (F : List Y) :
    OracleComp (fun _ : X => Y) (List (Option P)) :=
  (fun L => F.map fun vk => L.lookup vk) <$> dictionaryTable input D

/-- The batch search answers each entry as a separate search (18.1) would. -/
theorem evalPure_dictionaryBatchSearch (F : List Y) :
    (dictionaryBatchSearch input D F).evalPure H =
      F.map fun vk => (dictionaryPreimageSearch input vk D).evalPure H := by
  simp only [dictionaryBatchSearch, OracleComp.evalPure_map]
  exact List.map_congr_left fun vk _ => lookup_evalPure_dictionaryTable H input D vk

/-- **Cost of (18.3).** `D.length` oracle calls, whatever the number of entries. -/
theorem isQueryBounded_dictionaryBatchSearch (F : List Y) :
    OracleComp.IsQueryBounded (dictionaryBatchSearch input D F) D.length :=
  (OracleComp.isCostBounded_map_iff _ _ _).mpr (isQueryBounded_dictionaryTable input D)

/-- **Cost of separate searches.** Running (18.1) once per entry, each entry `e` with its own
derived input (for example its own salt), costs at most `F.length * D.length` calls. -/
theorem isQueryBounded_mapM_dictionaryPreimageSearch {E : Type} (inputOf : E → P → X)
    (vkOf : E → Y) (F : List E) :
    OracleComp.IsQueryBounded (F.mapM fun e => dictionaryPreimageSearch (inputOf e) (vkOf e) D)
      (F.length * D.length) :=
  OracleComp.IsCostBounded.mapM fun e _ => isQueryBounded_dictionarySearch (inputOf e) _ D

end Preimage

section Inversion

variable [DecidableEq Y]

/-- The search as an inverter for `pw ↦ H (input pw)`: it returns `default` when the search
fails. -/
noncomputable def dictionaryInverter [Inhabited P] (H : X → Y) (input : P → X) (D : List P)
    (vk : Y) : PMF P :=
  PMF.pure (((dictionaryPreimageSearch input vk D).evalPure H).getD default)

/-- The inverter is the search (18.1) evaluated against `H`: the program that
`isQueryBounded_dictionarySearch` bounds. -/
theorem dictionaryInverter_apply [Inhabited P] (H : X → Y) (input : P → X) (D : List P) (vk : Y) :
    dictionaryInverter H input D vk =
      PMF.pure (((dictionaryPreimageSearch input vk D).evalPure H).getD default) := by
  rfl

/-- **Weak secrets.** For any distribution `μ` of the secret, the search wins the inversion
experiment for `pw ↦ H (input pw)` at least as often as the secret lies in the dictionary. -/
theorem le_inversionExperiment_dictionaryInverter [Inhabited P] (μ : PMF P) (H : X → Y)
    (input : P → X) (D : List P) :
    μ.toOuterMeasure {pw | pw ∈ D} ≤
      (inversionExperiment μ (fun pw => H (input pw)) (dictionaryInverter H input D)) true := by
  have hexp : inversionExperiment μ (fun pw => H (input pw)) (dictionaryInverter H input D) =
      μ.map fun pw =>
        H (input (((dictionaryPreimageSearch input (H (input pw)) D).evalPure H).getD default)) ==
          H (input pw) := by
    rw [inversionExperiment_eq_bind_map]
    simp only [dictionaryInverter, PMF.pure_map]
    rfl
  rw [hexp, PMF.toOuterMeasure_apply, PMF.map_apply]
  refine tsum_le_tsum fun pw => ?_
  by_cases hmem : pw ∈ D
  · obtain ⟨w, -, hfind, hw⟩ := exists_evalPure_dictionaryPreimageSearch_of_mem H input D hmem
    simp [Set.indicator, hmem, hfind, hw]
  · simp [Set.indicator, hmem]

/-- **The dictionary search against a weak secret.** [BonehShoup2023], Section 18.3.1.2 (p. 722)
states that if `pw ∈ D`, the adversary obtains `pw` or some `pw'` with `H(pw) = H(pw')` in time
`O(|D|)`. Here, for every `H`, every derived input, and a secret drawn from an arbitrary
distribution `μ` on `P`, the search `(18.1)` over `D` makes at most `D.length` evaluations of `H`
on every challenge and wins `inversionExperiment` for `pw ↦ H (input pw)` with probability at
least `μ.toOuterMeasure {pw | pw ∈ D}` (this probability form is original to this library, not in
the book). -/
theorem dictionarySearch_inverts [Inhabited P] (μ : PMF P) (H : X → Y) (input : P → X)
    (D : List P) :
    (∀ vk : Y, OracleComp.IsQueryBounded (dictionaryPreimageSearch input vk D) D.length) ∧
      μ.toOuterMeasure {pw | pw ∈ D} ≤
        (inversionExperiment μ (fun pw => H (input pw)) (dictionaryInverter H input D)) true :=
  ⟨fun vk => isQueryBounded_dictionarySearch input (fun y => decide (y = vk)) D,
    le_inversionExperiment_dictionaryInverter μ H input D⟩

end Inversion

end Cslib.Crypto
