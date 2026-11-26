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
import CslibFrontier.Foundations.Control.Monad.Clock
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

For implicitly indexed source lists, `runSeedSearchIndexed` requests the source at each
position using a bounded cursor. It shares the seed loop and designated source handling with
`runSeedSearch`. The exact equality to the list specification holds before assuming any
controller contracts, so it covers rejection and repeated outcomes as well.

## Main results

* `runSeedSearchIndexed_eq`: indexed and list traversal have identical monadic outcomes.
* `runSeedSearchIndexed_clock`: bounds the controller clock, including a rejecting call.
* `runSeedSchedulerFrom`: resume at a seed rank and, after a designated scan, an indexed cursor.
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

-- Delay traversal until the designated controller has decided.
private def testSeedWith (controller : Fin n → m (Option ControllerVerdict))
    (source : Fin n) (checkOthers : Bool → m Bool) : m (Option Bool) := do
  match ← controller source with
  | none => failure
  | some (.bad _) => pure none
  | some (.decided answer) =>
    if ← checkOthers answer then pure (some answer) else pure none

/-- Test the designated source first, then the other listed sources in their given order.
`none` is a bad seed; controller failure is an effectful rejected branch. -/
def testSeed (controller : Fin n → m (Option ControllerVerdict))
    (sources : List (Fin n)) (source : Fin n) : m (Option Bool) :=
  testSeedWith controller source fun _ =>
    (sources.filter (fun u => u != source)).allM (sourceGood controller)

private def checkSourcesFrom {count : ℕ}
    (controller : Fin count → Fin n → m (Option ControllerVerdict))
    (source : Fin n) (sourceAt : Fin count → Fin n) :
    (remaining cursor : ℕ) → cursor + remaining ≤ count → m Bool
  | 0, _, _ => pure true
  | remaining + 1, cursor, h => do
    let position : Fin count := ⟨cursor, by omega⟩
    let u := sourceAt position
    if u == source then
      checkSourcesFrom controller source sourceAt remaining (cursor + 1) (by omega)
    else if ← sourceGood (controller position) u then
      checkSourcesFrom controller source sourceAt remaining (cursor + 1) (by omega)
    else pure false

private theorem checkSourcesFrom_eq {count : ℕ}
    (controller : Fin n → m (Option ControllerVerdict)) (source : Fin n)
    (sourceAt : Fin count → Fin n) (remaining cursor : ℕ) (h : cursor + remaining ≤ count) :
    checkSourcesFrom (fun _ => controller) source sourceAt remaining cursor h =
      ((List.ofFn fun i : Fin remaining => sourceAt ⟨cursor + i, by omega⟩).filter
        (fun u => u != source)).allM (sourceGood controller) := by
  induction remaining generalizing cursor with
  | zero => simp [checkSourcesFrom]
  | succ remaining ih =>
    simp only [checkSourcesFrom, List.ofFn_succ, Fin.val_zero, Nat.add_zero, List.filter_cons]
    rw [ih]
    simp only [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]
    by_cases heq : sourceAt ⟨cursor, by omega⟩ = source <;> simp [heq, List.allM_cons]

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

private def rankedSeedTest (test : Fin (2 ^ length) → m (Option Bool)) (i : Fin (2 ^ length)) :
    m (Option (SeedAnswer length)) := do
  let answer ← test i
  pure (answer.map fun b => ⟨i, b⟩)

private def runSeedSearchWith
    (test : Fin (2 ^ length) → m (Option Bool)) : m (Option (SeedAnswer length)) :=
  findSeedFrom (rankedSeedTest test) (2 ^ length) 0 (by simp)

/-- Enumerate every bit seed by increasing binary value, stopping at the first seed whose
designated and listed source controllers all pass. A successful negative answer also stops
the search. -/
def runSeedSearch
    (controller : (Fin length → Bool) → Fin n → m (Option ControllerVerdict))
    (sources : List (Fin n)) (source : Fin n) : m (Option (SeedAnswer length)) :=
  runSeedSearchWith fun i =>
    testSeed (controller ((BitString.equivFin length).symm i)) sources source

private def testScheduledSeed {count : ℕ}
    (scan : Fin (2 ^ length) → Option (Fin count × Bool) → Fin n → m (Option ControllerVerdict))
    (sourceAt : Fin count → Fin n) (source : Fin n) (i : Fin (2 ^ length)) :
    m (Option Bool) :=
  testSeedWith (scan i none) source fun answer =>
    checkSourcesFrom (fun position => scan i (some (position, answer))) source sourceAt count 0
      (by simp)

/-- Run the seed and source counters with a callback on the binary seed number, the
optional source position and retained designated answer, and the source ID. The absent
position denotes the designated scan. The callback's effects preserve branch multiplicity. -/
def runSeedScheduler {count : ℕ}
    (scan : Fin (2 ^ length) → Option (Fin count × Bool) → Fin n → m (Option ControllerVerdict))
    (sourceAt : Fin count → Fin n) (source : Fin n) : m (Option (SeedAnswer length)) :=
  runSeedSearchWith (testScheduledSeed scan sourceAt source)

private def findSeedFromRank {N : ℕ} (test : Fin N → m (Option (SeedAnswer length)))
    (seed : ℕ) : m (Option (SeedAnswer length)) :=
  if hs : seed ≤ N then findSeedFrom test (N - seed) seed (by omega) else pure none

private theorem findSeedFromRank_step {N : ℕ} (test : Fin N → m (Option (SeedAnswer length)))
    {seed : ℕ} (hs : seed < N) :
    findSeedFromRank test seed = (do
      match ← test ⟨seed, hs⟩ with
      | some answer => pure (some answer)
      | none => findSeedFromRank test (seed + 1)) := by
  have hcount : N - seed = (N - (seed + 1)) + 1 := by omega
  simp only [findSeedFromRank, dite_eq_left hs.le,
    dite_eq_left (Nat.succ_le_of_lt hs), hcount, findSeedFrom]

private def checkScheduledFrom {count : ℕ}
    (controller : Fin count → Fin n → m (Option ControllerVerdict))
    (sourceAt : Fin count → Fin n) (source : Fin n) (cursor : ℕ) : m Bool :=
  if hc : cursor ≤ count then
    checkSourcesFrom controller source sourceAt (count - cursor) cursor (by omega)
  else pure true

private theorem checkScheduledFrom_step {count : ℕ}
    (controller : Fin count → Fin n → m (Option ControllerVerdict))
    (sourceAt : Fin count → Fin n) (source : Fin n) {cursor : ℕ} (hc : cursor < count) :
    checkScheduledFrom controller sourceAt source cursor =
      if sourceAt ⟨cursor, hc⟩ = source then
        checkScheduledFrom controller sourceAt source (cursor + 1)
      else (do
        if ← sourceGood (controller ⟨cursor, hc⟩) (sourceAt ⟨cursor, hc⟩) then
          checkScheduledFrom controller sourceAt source (cursor + 1)
        else pure false) := by
  have hcount : count - cursor = (count - (cursor + 1)) + 1 := by omega
  simp only [checkScheduledFrom, dite_eq_left hc.le,
    dite_eq_left (Nat.succ_le_of_lt hc), hcount, checkSourcesFrom, beq_iff_eq]

/-- Resume the same monadic seed search at a binary rank. With no retained answer, start with
the designated scan. A pair of cursor and answer resumes the indexed roots for that seed,
after which later seeds still start with their designated scan. -/
def runSeedSchedulerFrom {count : ℕ}
    (scan : Fin (2 ^ length) → Option (Fin count × Bool) → Fin n → m (Option ControllerVerdict))
    (sourceAt : Fin count → Fin n) (source : Fin n) (seed : ℕ)
    (phase : Option (ℕ × Bool)) : m (Option (SeedAnswer length)) :=
  let later := findSeedFromRank (rankedSeedTest (testScheduledSeed scan sourceAt source))
  match phase with
  | none => later seed
  | some (cursor, answer) =>
    if hs : seed < 2 ^ length then do
      let i := (⟨seed, hs⟩ : Fin (2 ^ length))
      let others ← checkScheduledFrom (fun j => scan i (some (j, answer))) sourceAt source cursor
      if others then pure (some ⟨i, answer⟩) else later (seed + 1)
    else pure none

/-- Starting at the designated scan of rank zero gives the original seed search. -/
theorem runSeedSchedulerFrom_start {count : ℕ}
    (scan : Fin (2 ^ length) → Option (Fin count × Bool) → Fin n → m (Option ControllerVerdict))
    (sourceAt : Fin count → Fin n) (source : Fin n) :
    runSeedSchedulerFrom scan sourceAt source 0 none = runSeedScheduler scan sourceAt source := by
  simp [runSeedSchedulerFrom, runSeedScheduler, findSeedFromRank, runSeedSearchWith]

/-- A rank at or above the exclusive limit exhausts the seed search. -/
theorem runSeedSchedulerFrom_exhausted {count : ℕ}
    (scan : Fin (2 ^ length) → Option (Fin count × Bool) → Fin n → m (Option ControllerVerdict))
    (sourceAt : Fin count → Fin n) (source : Fin n) {seed : ℕ} (hs : 2 ^ length ≤ seed)
    (phase : Option (ℕ × Bool)) :
    runSeedSchedulerFrom scan sourceAt source seed phase = pure none := by
  rcases phase with _ | ⟨_, _⟩
  · simp only [runSeedSchedulerFrom, findSeedFromRank, Nat.sub_eq_zero_of_le hs, findSeedFrom]
    split_ifs <;> rfl
  · simp [runSeedSchedulerFrom, Nat.not_lt.mpr hs]

/-- A designated scan's pure verdict advances the seed on a tie, or starts the indexed roots
with the designated answer. -/
theorem runSeedSchedulerFrom_designated [LawfulMonad m] {count : ℕ}
    (scan : Fin (2 ^ length) → Option (Fin count × Bool) → Fin n → m (Option ControllerVerdict))
    (sourceAt : Fin count → Fin n) (source : Fin n) {seed : ℕ} (hs : seed < 2 ^ length)
    (verdict : ControllerVerdict) (hscan : scan ⟨seed, hs⟩ none source = pure (some verdict)) :
    runSeedSchedulerFrom scan sourceAt source seed none =
      match verdict with
      | .bad _ => runSeedSchedulerFrom scan sourceAt source (seed + 1) none
      | .decided b => runSeedSchedulerFrom scan sourceAt source seed (some (0, b)) := by
  simp only [runSeedSchedulerFrom, findSeedFromRank_step _ hs]
  cases verdict with
  | bad _ => simp [rankedSeedTest, testScheduledSeed, testSeedWith, hscan]
  | decided answer =>
    simp only [rankedSeedTest, testScheduledSeed, testSeedWith, hscan, pure_bind, bind_assoc,
      checkScheduledFrom, dite_eq_left hs, dite_eq_left (Nat.zero_le _), Nat.sub_zero]
    congr 1
    funext passes
    cases passes <;> simp

/-- Once all indexed roots have passed, the retained designated answer is returned at the
current seed. -/
theorem runSeedSchedulerFrom_indexed_done [LawfulMonad m] {count : ℕ}
    (scan : Fin (2 ^ length) → Option (Fin count × Bool) → Fin n → m (Option ControllerVerdict))
    (sourceAt : Fin count → Fin n) (source : Fin n) {seed cursor : ℕ}
    (hs : seed < 2 ^ length) (hc : count ≤ cursor) (answer : Bool) :
    runSeedSchedulerFrom scan sourceAt source seed (some (cursor, answer)) =
      pure (some ⟨⟨seed, hs⟩, answer⟩) := by
  simp [runSeedSchedulerFrom, hs, checkScheduledFrom, Nat.sub_eq_zero_of_le hc, checkSourcesFrom]

/-- An indexed step skips the designated source or consumes its own pure verdict. A tie
advances to the next seed. A skip or decided verdict advances the cursor with the retained
designated answer. -/
theorem runSeedSchedulerFrom_indexed [LawfulMonad m] {count : ℕ}
    (scan : Fin (2 ^ length) → Option (Fin count × Bool) → Fin n → m (Option ControllerVerdict))
    (sourceAt : Fin count → Fin n) (source : Fin n) {seed cursor : ℕ}
    (hs : seed < 2 ^ length) (hc : cursor < count) (answer : Bool)
    (reply : Option ControllerVerdict) (hskip : reply.isNone ↔ sourceAt ⟨cursor, hc⟩ = source)
    (hscan : ∀ value, reply = some value →
      scan ⟨seed, hs⟩ (some (⟨cursor, hc⟩, answer)) (sourceAt ⟨cursor, hc⟩) = pure (some value)) :
    runSeedSchedulerFrom scan sourceAt source seed (some (cursor, answer)) =
      match reply with
      | some (.bad _) => runSeedSchedulerFrom scan sourceAt source (seed + 1) none
      | _ => runSeedSchedulerFrom scan sourceAt source seed (some (cursor + 1, answer)) := by
  simp only [runSeedSchedulerFrom, dite_eq_left hs, checkScheduledFrom_step _ _ _ hc]
  cases reply with
  | none => simp [hskip.mp rfl]
  | some value =>
    have hne : sourceAt ⟨cursor, hc⟩ ≠ source := fun he => by simpa using hskip.mpr he
    cases value <;> simp [hne, sourceGood, hscan _ rfl]


/-- Search with sources supplied by their positions. The traversal keeps a cursor and
remaining count, requesting each source only after the preceding checks have passed. -/
def runSeedSearchIndexed {count : ℕ}
    (controller : (Fin length → Bool) → Fin n → m (Option ControllerVerdict))
    (sourceAt : Fin count → Fin n) (source : Fin n) : m (Option (SeedAnswer length)) :=
  runSeedScheduler (fun i _ => controller ((BitString.equivFin length).symm i)) sourceAt source

/-- The indexed search is the specialization that reads the binary seed by its bits. -/
theorem runSeedSearchIndexed_eq_scheduler {count : ℕ}
    (controller : (Fin length → Bool) → Fin n → m (Option ControllerVerdict))
    (sourceAt : Fin count → Fin n) (source : Fin n) :
    runSeedSearchIndexed controller sourceAt source =
      runSeedScheduler (fun i _ => controller ((BitString.equivFin length).symm i))
        sourceAt source := by rfl

/-- A scanner that depends only on the seed number and source ID gives the same computation
as the indexed search with the corresponding bit-seed callback. -/
theorem runSeedScheduler_eq {count : ℕ}
    (scan : Fin (2 ^ length) → Fin n → m (Option ControllerVerdict))
    (sourceAt : Fin count → Fin n) (source : Fin n) :
    runSeedScheduler (fun i _ => scan i) sourceAt source =
      runSeedSearchIndexed (fun bits => scan (BitString.equivFin length bits)) sourceAt source := by
  simp [runSeedSearchIndexed]

/-- Indexed traversal gives the same ordered computation as enumerating the source list.
In the list monad this preserves all outcomes and their multiplicities. -/
theorem runSeedSearchIndexed_eq {count : ℕ}
    (controller : (Fin length → Bool) → Fin n → m (Option ControllerVerdict))
    (sourceAt : Fin count → Fin n) (source : Fin n) :
    runSeedSearchIndexed controller sourceAt source =
      runSeedSearch controller (List.ofFn sourceAt) source := by
  unfold runSeedSearchIndexed runSeedScheduler runSeedSearch
  congr 1
  funext i
  simp [testScheduledSeed, testSeed, checkSourcesFrom_eq]

/-- The indexed search spends at most one designated call and one call per source position
for each candidate seed. A rejecting call still advances the measured state clock. This
bounds the supplied callback cost in the rejecting state monad. -/
theorem runSeedScheduler_clock {σ : Type} {count : ℕ} (clock : σ → ℕ) (cost : ℕ)
    (scan : Fin (2 ^ length) → Option (Fin count × Bool) → Fin n →
      OptionT (StateM σ) (Option ControllerVerdict))
    (sourceAt : Fin count → Fin n) (source : Fin n)
    (hc : ∀ i phase u s, clock ((scan i phase u).run s).2 ≤ clock s + cost) (s : σ) :
    clock ((runSeedScheduler scan sourceAt source).run s).2 ≤
      clock s + 2 ^ length * ((1 + count) * cost) := by
  have hgood i phase u t :
      clock ((sourceGood (scan i phase) u).run t).2 ≤ clock t + cost := by
    simpa only [sourceGood, Nat.add_zero] using bind_optionT_clock clock cost 0 _ _ (hc i phase u)
      (by rintro (_ | _ | _) _ <;> exact Nat.le_refl _) t
  have hothers i answer (remaining cursor : ℕ)
      (h : cursor + remaining ≤ count) (t : σ) :
      clock ((checkSourcesFrom (fun position => scan i (some (position, answer)))
        source sourceAt remaining cursor h).run t).2 ≤
        clock t + remaining * cost := by
    induction remaining generalizing cursor t with
    | zero => simp [checkSourcesFrom, pure, OptionT.pure, OptionT.run, OptionT.mk, StateT.pure]
    | succ remaining ih =>
      simp only [checkSourcesFrom, Nat.succ_mul]
      split
      · exact (ih _ _ _).trans (Nat.add_le_add_left (Nat.le_add_right _ _) _)
      · rw [Nat.add_comm (remaining * cost)]
        apply bind_optionT_clock clock cost (remaining * cost) _ _ (hgood i _ _)
        rintro (_ | _) _
        exacts [Nat.le_add_right _ _, ih _ _ _]
  let budget := (1 + count) * cost
  have htest i t : clock ((testScheduledSeed scan sourceAt source i).run t).2 ≤
      clock t + budget := by
    rw [testScheduledSeed, testSeedWith]
    dsimp only [budget]
    rw [Nat.add_mul, Nat.one_mul]
    apply bind_optionT_clock clock cost (count * cost) _ _ (hc i none source)
    rintro (_ | _ | answer) _
    · exact Nat.le_add_right _ _
    · exact Nat.le_add_right _ _
    · simpa only [Nat.add_zero] using bind_optionT_clock clock (count * cost) 0 _ _
        (hothers i answer count 0 (Nat.zero_add count).le)
        (fun b _ => by cases b <;> exact le_rfl) _
  let test := rankedSeedTest (testScheduledSeed scan sourceAt source)
  have hstep i t : clock ((test i).run t).2 ≤ clock t + budget := by
    simpa only [test, rankedSeedTest, Nat.add_zero] using
      bind_optionT_clock clock budget 0 _ _ (htest i) (fun _ _ => le_rfl) t
  have hloop (remaining cursor : ℕ) (h : cursor + remaining ≤ 2 ^ length) (t : σ) :
      clock ((findSeedFrom test remaining cursor h).run t).2 ≤
        clock t + remaining * budget := by
    induction remaining generalizing cursor t with
    | zero => simp [findSeedFrom, pure, OptionT.pure, OptionT.run, OptionT.mk, StateT.pure]
    | succ remaining ih =>
      rw [findSeedFrom, Nat.succ_mul, Nat.add_comm (remaining * budget)]
      apply bind_optionT_clock clock budget (remaining * budget) _ _ (hstep _)
      rintro (_ | _) _
      exacts [ih _ _ _, Nat.le_add_right _ _]
  exact hloop (2 ^ length) 0 (by simp) s

/-- The indexed search spends at most one designated call and one call per source position
for each candidate seed, including a rejecting call. -/
theorem runSeedSearchIndexed_clock {σ : Type} {count : ℕ} (clock : σ → ℕ) (cost : ℕ)
    (controller : (Fin length → Bool) → Fin n → OptionT (StateM σ) (Option ControllerVerdict))
    (sourceAt : Fin count → Fin n) (source : Fin n)
    (hc : ∀ seed u s, clock ((controller seed u).run s).2 ≤ clock s + cost) (s : σ) :
    clock ((runSeedSearchIndexed controller sourceAt source).run s).2 ≤
      clock s + 2 ^ length * ((1 + count) * cost) :=
  runSeedScheduler_clock clock cost (fun i _ => controller ((BitString.equivFin length).symm i))
    sourceAt source (fun i _ => hc ((BitString.equivFin length).symm i)) s

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
  have hsource' : sourceGood controller = fun s => pure (decide (∀ j, ∃! w, Passes r s j w)) :=
    funext fun s => by
      rcases hc s with ⟨_ | _, hv, hs⟩ <;> simp only [sourceGood, hv, pure_bind]
      · exact congrArg pure (decide_eq_false fun h => hs (h _)).symm
      · simp [hs.1]
  rcases hc source with ⟨j | b, hv, hs⟩
  · rw [testSeed, testSeedWith, hv, pure_bind, ite_eq_right fun h => hs (h.1 j)]
  · have hb : b = decide (Relation.ReflTransGen r source target) :=
      Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using hs.2)
    have hall : (sources.filter (fun u => u != source)).all
        (fun s => decide (∀ j, ∃! w, Passes r s j w)) =
        decide (∀ s ∈ sources, ∀ j, ∃! w, Passes r s j w) :=
      Bool.eq_iff_iff.mpr <| by
        simp only [List.all_eq_true, List.mem_filter, bne_iff_ne, decide_eq_true_eq]
        exact ⟨fun h s hmem => if heq : s = source then heq ▸ hs.1 else h s ⟨hmem, heq⟩,
          fun h s hs => h s hs.1⟩
    simp only [testSeed, testSeedWith, hv, pure_bind, hsource', List.allM_pure, hall, hb,
      decide_eq_true_eq, hs.1, implies_true, true_and, apply_ite pure]

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
  have hex' : ∃ i, good i :=
    hex.elim fun seed hs => ⟨BitString.equivFin length seed, by simpa [good, bits] using hs⟩
  let i := Fin.find good hex'
  let makeAnswer (j : Fin (2 ^ length)) : SeedAnswer length :=
    ⟨j, decide (Relation.ReflTransGen (r (bits j)) source target)⟩
  have hfind : (List.finRange (2 ^ length)).find? (fun j => decide (good j)) = some i := by
    refine List.find?_eq_some_iff_getElem.mpr
      ⟨decide_eq_true (Fin.find_spec hex'), i.val,
        by simpa only [List.length_finRange] using i.isLt, by simp, fun j hj => ?_⟩
    simpa using Fin.find_min hex' (j := ⟨j, by omega⟩) hj
  have htest (j : Fin (2 ^ length)) :
      rankedSeedTest (fun k => testSeed (controller (bits k)) sources source) j =
        pure ((Option.guard (fun j => decide (good j)) j).map makeAnswer) := by
    rw [rankedSeedTest, testSeed_correct sources (hc (bits j))]
    by_cases h : good j <;> simp [Option.guard, good, makeAnswer, h]
  have hscan : runSeedSearch controller sources source =
      (List.finRange (2 ^ length)).findSomeM?
        (rankedSeedTest (fun j => testSeed (controller (bits j)) sources source)) := by
    simp only [runSeedSearch, runSeedSearchWith, findSeedFrom_eq, Nat.zero_add, List.finRange, bits]
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
  exact ⟨makeAnswer i, hrun.trans (by rw [hfind]; rfl), Fin.find_spec hex',
    fun j hj => Fin.find_min hex' hj, decide_eq_true_iff⟩

end Cslib.DoubleCounting
