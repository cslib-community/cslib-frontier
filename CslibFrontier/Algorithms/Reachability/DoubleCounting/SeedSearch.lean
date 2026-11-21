/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.DoubleCounting.ControllerReplay
public import CslibFrontier.Foundations.Data.BitString.Binary
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Monad
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Ordered seed search over verified reachability controllers

This is a composition step for #6747, not a native workspace or NL = UL theorem.
The designated source's controller is run first to obtain its answer. The other listed
sources are then checked in order. The list can enumerate original roots within a subdivided
graph, whose auxiliary vertices remain available as walk targets. A bad controller verdict
rejects this seed; a failed controller execution rejects the branch. Seeds are tried by
increasing binary value, using the existing bit-string numbering and a bounded counter.
In `List`, duplicate successful branches remain duplicate entries.

## Applying the interface

Supply a controller callback indexed by a bit seed and source. Its exact-outcome contract
returns a bad radius witnessing failure of round uniqueness, or a decided Boolean with
all-round uniqueness and the correct reachability answer. `runController_correct` and
`runController_replay_correct` provide this boundary. The designated source is always tested,
even if it is absent from the supplied source list. For graph-wide verification the list
must cover every intended original source; the algorithm does not infer that coverage.

The seed is numbered by `BitString.equivFin`, with coordinate zero least significant.
`BitString.equivFin_symm_apply` identifies access to a seed bit with `Nat.testBit` on its
counter, so a later native implementation need not retain an array of seed words.
The selected answer concerns the graph at the selected seed. Applying it to a fixed language
also uses the reachability-preservation theorem of the weighted transport.

The outer traversal keeps a cursor and a remaining count, each at most `2 ^ length`, so each
register fits in `length + 1` binary digits. The initial count `2 ^ length` needs all of those
digits. Each tested cursor is strictly below `2 ^ length` and fits in `length` digits. The checked
client verifies these bounds for the native binary encoding. The source list specifies the inner
traversal.
The actual replay callback in the [checked client][client] is proof-level enumeration.
Native loop/state bounds, binary choice lowering, callbacks and first-halting composition
remain in #6747. Validate this client with
`scripts/build.sh CslibFrontierTests.IsolationSeedSearch --wfail --iofail`.

[client]: https://github.com/cslib-community/cslib-frontier/blob/e2e7346ce2b373cb8557c04ff0d4e24b21ded9c4/CslibFrontierTests/IsolationSeedSearch.lean

## Main results

* `testSeed_correct`: the tested sources have one exact outcome under the controller contract.
* `runSeedSearch_correct`: a good seed exists, so search returns the least passing seed and
  its correct Boolean, with one successful branch in the list interpretation.

## References

* [Hoza2026NLUL], Section 1.2, page 3, the seed-enumeration step. The proof here concerns
  monadic control flow under verified callback contracts, not the source's native theorem.
-/

public section

namespace Cslib.DoubleCounting

/-- The first seed passing the requested source checks and its designated answer. -/
structure SeedAnswer (length : ℕ) where
  /-- Binary value of the selected seed, with coordinate zero least significant. -/
  seed : Fin (2 ^ length)
  /-- The controller's answer from the designated source. -/
  reachable : Bool
  deriving DecidableEq, Repr

variable {m : Type → Type} [AlternativeMonad m] {n length : ℕ}

private def sourceGood (controller : Fin n → m (Option ControllerVerdict))
    (s : Fin n) : m Bool := do
  match ← controller s with
  | none => failure
  | some (.bad _) => pure false
  | some (.decided _) => pure true

/-- Test the designated source first, then the other listed sources in their given order.
`none` is a bad seed; controller failure is an effectful rejected branch. -/
def testSeed (controller : Fin n → m (Option ControllerVerdict))
    (sources : List (Fin n)) (source : Fin n) :
    m (Option Bool) := do
  match ← controller source with
  | none => failure
  | some (.bad _) => pure none
  | some (.decided answer) =>
    if ← (sources.filter (fun u => u != source)).allM (sourceGood controller) then
      pure (some answer)
    else pure none

-- The bound is erased. Each continuation keeps only the next cursor and remaining count.
private def findSeedFrom {N : ℕ} (test : Fin N → m (Option (SeedAnswer length))) :
    (remaining cursor : ℕ) → cursor + remaining ≤ N → m (Option (SeedAnswer length))
  | 0, _, _ => pure none
  | remaining + 1, cursor, h => do
    match ← test ⟨cursor, by omega⟩ with
    | some answer => pure (some answer)
    | none => findSeedFrom test remaining (cursor + 1) (by omega)

private theorem findSeedFrom_eq {N : ℕ} (test : Fin N → m (Option (SeedAnswer length)))
    (remaining cursor : ℕ) (h : cursor + remaining ≤ N) :
    findSeedFrom test remaining cursor h =
      (List.ofFn fun j : Fin remaining => (⟨cursor + j, by omega⟩ : Fin N)).findSomeM? test := by
  induction remaining generalizing cursor with
  | zero => simp [findSeedFrom]
  | succ remaining ih =>
    simp only [findSeedFrom, List.ofFn_succ, List.findSomeM?_cons, Fin.val_zero, Nat.add_zero]
    rw [ih]
    simp only [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]
    congr 2
    funext answer
    cases answer <;> rfl

/-- Enumerate every bit seed by increasing binary value, stopping at the first seed whose
designated and listed source controllers all pass. A successful negative answer also stops
the search. -/
def runSeedSearch
    (controller : (Fin length → Bool) → Fin n → m (Option ControllerVerdict))
    (sources : List (Fin n)) (source : Fin n) :
    m (Option (SeedAnswer length)) :=
  findSeedFrom (fun i => do
    let answer ← testSeed (controller ((BitString.equivFin length).symm i)) sources source
    pure (answer.map fun b => ⟨i, b⟩)) (2 ^ length) 0 (by simp)

variable [LawfulMonad m]

/-- The all-source test has one monadic outcome under the controller's exact-outcome
contract. In `List` this is a singleton with its multiplicity, not merely a unique value. -/
theorem testSeed_correct {r : Fin n → Fin n → Prop} {target source : Fin n}
    (sources : List (Fin n))
    {controller : Fin n → m (Option ControllerVerdict)}
    (hc : ∀ s, ∃ verdict, controller s = pure (some verdict) ∧
      match verdict with
      | .bad j => ¬ ∃! w, Passes r s j w
      | .decided b => (∀ j, ∃! w, Passes r s j w) ∧
          (b = true ↔ Relation.ReflTransGen r s target)) :
    testSeed controller sources source = pure (by
      classical
      exact if (∀ j, ∃! w, Passes r source j w) ∧
          (∀ s ∈ sources, ∀ j, ∃! w, Passes r s j w) then
        some (decide (Relation.ReflTransGen r source target)) else none) := by
  classical
  have hsource (s : Fin n) : sourceGood controller s =
      pure (decide (∀ j, ∃! w, Passes r s j w)) := by
    obtain ⟨verdict, hv, hs⟩ := hc s
    cases verdict with
    | bad j =>
      have hnot : ¬ ∀ i, ∃! w, Passes r s i w := fun h => hs (h j)
      simp [sourceGood, hv, hnot]
    | decided b => simp [sourceGood, hv, hs.1]
  have hsource' : sourceGood controller = fun s => pure (decide (∀ j, ∃! w, Passes r s j w)) :=
    funext hsource
  obtain ⟨verdict, hv, hs⟩ := hc source
  cases verdict with
  | bad j =>
    have hnot : ¬ ((∀ i, ∃! w, Passes r source i w) ∧
        ∀ s ∈ sources, ∀ i, ∃! w, Passes r s i w) := fun h => hs (h.1 j)
    simp [testSeed, hv, hnot]
  | decided b =>
    have hb : b = decide (Relation.ReflTransGen r source target) :=
      Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using hs.2)
    have hall : (sources.filter (fun u => u != source)).all
        (fun s => decide (∀ j, ∃! w, Passes r s j w)) =
        decide (∀ s ∈ sources, ∀ j, ∃! w, Passes r s j w) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, List.mem_filter,
        bne_iff_ne, decide_eq_true_eq]
      constructor
      · intro h s hmem
        by_cases heq : s = source
        · simpa only [heq] using hs.1
        · exact h s ⟨hmem, heq⟩
      · intro h s hs
        exact h s hs.1
    simp only [testSeed, hv, pure_bind, hsource', List.allM_pure, hall, hb,
      decide_eq_true_eq]
    by_cases h : ∀ s ∈ sources, ∀ j, ∃! w, Passes r s j w
    · rw [ite_eq_left h, ite_eq_left ⟨hs.1, h⟩]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.2)]

/-- Under exact controller outcomes and the existence of an all-source-good seed, the
ordered search has one outcome and selects the least binary seed that passes every source.
In `List` this asserts exactly one successful branch, including its multiplicity. -/
theorem runSeedSearch_correct (sources : List (Fin n))
    {r : (Fin length → Bool) → Fin n → Fin n → Prop} {target source : Fin n}
    {controller : (Fin length → Bool) → Fin n → m (Option ControllerVerdict)}
    (hc : ∀ seed s, ∃ verdict, controller seed s = pure (some verdict) ∧
      match verdict with
      | .bad j => ¬ ∃! w, Passes (r seed) s j w
      | .decided b => (∀ j, ∃! w, Passes (r seed) s j w) ∧
          (b = true ↔ Relation.ReflTransGen (r seed) s target))
    (hex : ∃ seed, (∀ j, ∃! w, Passes (r seed) source j w) ∧
      ∀ s ∈ sources, ∀ j, ∃! w, Passes (r seed) s j w) :
    ∃ result, runSeedSearch controller sources source = pure (some result) ∧
      ((∀ j, ∃! w, Passes (r ((BitString.equivFin length).symm result.seed)) source j w) ∧
        ∀ s ∈ sources, ∀ j,
          ∃! w, Passes (r ((BitString.equivFin length).symm result.seed)) s j w) ∧
      (∀ i < result.seed,
        ¬ ((∀ j, ∃! w, Passes (r ((BitString.equivFin length).symm i)) source j w) ∧
          ∀ s ∈ sources, ∀ j, ∃! w, Passes (r ((BitString.equivFin length).symm i)) s j w)) ∧
      (result.reachable = true ↔
        Relation.ReflTransGen
          (r ((BitString.equivFin length).symm result.seed)) source target) := by
  classical
  let bits := (BitString.equivFin length).symm
  let good (i : Fin (2 ^ length)) :=
    (∀ j, ∃! w, Passes (r (bits i)) source j w) ∧
      ∀ s ∈ sources, ∀ j, ∃! w, Passes (r (bits i)) s j w
  have hex' : ∃ i, good i := by
    obtain ⟨seed, hs⟩ := hex
    exact ⟨BitString.equivFin length seed, by simpa [good, bits] using hs⟩
  let i := Fin.find good hex'
  let makeAnswer (j : Fin (2 ^ length)) : SeedAnswer length :=
    ⟨j, decide (Relation.ReflTransGen (r (bits j)) source target)⟩
  have hfind : (List.finRange (2 ^ length)).find? (fun j => decide (good j)) = some i := by
    apply List.find?_eq_some_iff_getElem.mpr
    refine ⟨by simpa only [decide_eq_true_eq] using (show good i from Fin.find_spec hex'), i.val,
      by simpa only [List.length_finRange] using i.isLt, ?_, ?_⟩
    · simp
    · intro j hj
      have hn := Fin.find_min hex'
        (show (⟨j, by omega⟩ : Fin (2 ^ length)) < i from hj)
      simpa using hn
  have htest (j : Fin (2 ^ length)) :
      (do
        let answer ← testSeed (controller (bits j)) sources source
        pure (answer.map fun b => (⟨j, b⟩ : SeedAnswer length))) =
      pure ((Option.guard (fun j => decide (good j)) j).map makeAnswer) := by
    rw [testSeed_correct sources (hc (bits j))]
    by_cases h : good j <;> simp [Option.guard, good, makeAnswer, h]
  have hscan : runSeedSearch controller sources source =
      (List.finRange (2 ^ length)).findSomeM? (fun i => do
        let answer ← testSeed (controller (bits i)) sources source
        pure (answer.map fun b => ⟨i, b⟩)) := by
    simp only [runSeedSearch, findSeedFrom_eq, Nat.zero_add, List.finRange, bits]
  have hrun : runSeedSearch controller sources source =
      pure (((List.finRange (2 ^ length)).find? (fun j => decide (good j))).map makeAnswer) := by
    rw [hscan]
    calc
      _ = (List.finRange (2 ^ length)).findSomeM?
          (fun j => pure ((Option.guard (fun j => decide (good j)) j).map makeAnswer)) :=
        congrArg (fun f : Fin (2 ^ length) → m (Option (SeedAnswer length)) =>
          (List.finRange (2 ^ length)).findSomeM? f) (funext htest)
      _ = _ := by
        rw [List.findSomeM?_pure]
        change pure ((List.finRange (2 ^ length)).findSome?
          (Option.map makeAnswer ∘ Option.guard (fun j => decide (good j)))) = _
        rw [← List.map_findSome?, List.findSome?_guard]
  refine ⟨makeAnswer i, ?_, Fin.find_spec hex', ?_, ?_⟩
  · rw [hrun, hfind]
    rfl
  · intro j hj
    exact Fin.find_min hex' hj
  · simp only [makeAnswer, bits, decide_eq_true_eq]

end Cslib.DoubleCounting
