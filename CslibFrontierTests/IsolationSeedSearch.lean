/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Reachability.DoubleCounting.SeedSearch
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-! Ordered seeds, all-source checks, rejection and multiplicity, plus actual controller replay. -/

-- These commands check executable branch-multiplicity regressions.
set_option linter.hashCommand false

namespace CslibFrontierTests.IsolationSeedSearch

open Cslib.DoubleCounting

open Turing.MultiTapeTM in
-- A tested seed uses at most the seed width. Either loop register can reach the inclusive bound.
example (width : ℕ) (candidate : Fin (2 ^ width)) (cursor remaining : ℕ)
    (h : cursor + remaining ≤ 2 ^ width) :
    (encNat candidate.val).length ≤ width ∧
      (encNat cursor).length ≤ width + 1 ∧ (encNat remaining).length ≤ width + 1 := by
  have hnext : (2 : ℕ) ^ width < 2 ^ (width + 1) := by
    rw [pow_succ]
    have := Nat.two_pow_pos width
    omega
  exact ⟨length_encNat_le_of_lt_two_pow candidate.isLt,
    length_encNat_le_of_lt_two_pow (lt_of_le_of_lt (by omega) hnext),
    length_encNat_le_of_lt_two_pow (lt_of_le_of_lt (by omega) hnext)⟩

open Turing.MultiTapeTM in
-- In particular, the initial remaining count does not fit in the candidate's width.
example (width : ℕ) : width < (encNat (2 ^ width)).length := by
  rw [encNat_apply, Nat.size_eq_bits_len, Nat.lt_size]

private def badThenNegative (seed : Fin 1 → Bool) (_ : Fin 2) : List (Option ControllerVerdict) :=
  if seed 0 then [some (.decided false)] else [some (.bad 1)]

#guard runSeedSearch badThenNegative [0, 1] 0 = [some ⟨1, false⟩]

private def negativeThenPositive (seed : Fin 1 → Bool) (_ : Fin 2) :
    List (Option ControllerVerdict) := [some (.decided (seed 0))]

-- A negative answer stops the search at seed zero; the later positive answer is irrelevant.
#guard runSeedSearch negativeThenPositive [0, 1] 0 = [some ⟨0, false⟩]

private def failedFirst (seed : Fin 1 → Bool) (_ : Fin 2) : List (Option ControllerVerdict) :=
  if seed 0 then [some (.decided true)] else [none]

-- An invalid controller execution rejects the branch instead of masquerading as a bad seed.
#guard runSeedSearch failedFirst [0, 1] 0 = []

private def duplicatedBad (seed : Fin 1 → Bool) (_ : Fin 2) : List (Option ControllerVerdict) :=
  if seed 0 then [some (.decided false)] else [some (.bad 1), some (.bad 1)]

-- Equal answer values are not deduplicated: two bad-seed continuations give two later results.
#guard runSeedSearch duplicatedBad [0, 1] 0 = [some ⟨1, false⟩, some ⟨1, false⟩]

private def originalRoots (seed : Fin 1 → Bool) (s : Fin 3) : List (Option ControllerVerdict) :=
  if s = 2 then [some (.bad 1)]
  else if s == 1 && !seed 0 then [some (.bad 1)]
  else [some (.decided false)]

-- Source 1 rejects seed zero. Auxiliary source 2 is deliberately outside the original-root list.
#guard runSeedSearch originalRoots [0, 1] 0 = [some ⟨1, false⟩]

-- The indexed source range omits the auxiliary ID.
#guard runSeedSearchIndexed originalRoots (fun i : Fin 2 => i.castSucc) 0 = [some ⟨1, false⟩]

-- The designated source is in the indexed range. Checking it twice would yield four results.
#guard runSeedSearchIndexed
  (fun (_ : Fin 0 → Bool) s =>
    if s = (0 : Fin 2) then [some (.decided false), some (.decided false)]
    else [some (.decided true)])
  id 0 = [some ⟨0, false⟩, some ⟨0, false⟩]

-- Two passing occurrences at a nondesignated source give two results.
#guard runSeedSearchIndexed
  (fun (_ : Fin 1 → Bool) s =>
    if s = (0 : Fin 2) then [some (.decided false)]
    else [some (.decided true), some (.decided true)])
  id 0 = [some ⟨0, false⟩, some ⟨0, false⟩]

-- Failure at a reached source rejects the branch instead of advancing to the next seed.
#guard runSeedSearchIndexed
  (fun (_ : Fin 1 → Bool) s =>
    if s = (0 : Fin 2) then [some (.decided true)] else [none]) id 0 = []

private def resumeChecks (_ : Fin (2 ^ 1)) (_ : Option (Fin 2 × Bool)) (u : Fin 2) :
    List (Option ControllerVerdict) :=
  if u = 0 then [none] else [some (.decided true)]

-- Resuming skips the designated source and keeps its negative answer across a positive reply.
example : runSeedSchedulerFrom resumeChecks id (0 : Fin 2) 0 (some (0, false)) =
    [some ⟨0, false⟩] := by
  rw [runSeedSchedulerFrom_indexed resumeChecks id 0 (seed := 0) (cursor := 0)
    (by decide) (by decide) false none (by simp) (by simp)]
  rw [runSeedSchedulerFrom_indexed resumeChecks id 0 (seed := 0) (cursor := 1)
    (by decide) (by decide) false (some (.decided true)) (by decide)
    (by intro value h; cases h; rfl)]
  exact runSeedSchedulerFrom_indexed_done resumeChecks id 0 (by decide) (by decide) false

private def tickVerdict (answer : Option (Option ControllerVerdict)) :
    OptionT (StateM ℕ) (Option ControllerVerdict) :=
  OptionT.mk fun clock => (answer, clock + 1)

-- A failed nondesignated call still counts, and the branch rejects without trying another seed.
#guard
  let result := (runSeedSearchIndexed
    (fun (_ : Fin 1 → Bool) s =>
      tickVerdict (if s = (0 : Fin 2) then some (some (.decided true)) else none))
    id 0).run 0
  result.1.isNone && result.2 == 2

private def countedAnswer (seed : Fin 1 → Bool) (_ : Fin 2) :
    OptionT (StateM ℕ) (Option ControllerVerdict) :=
  tickVerdict (some (some (.decided (seed 0))))

-- The false answer stops enumeration after one seed and does not repeat the designated call.
#guard
  let result := (runSeedSearchIndexed countedAnswer id 0).run 0
  match result.1 with
  | some (some answer) => answer.seed.val == 0 && !answer.reachable && result.2 == 2
  | _ => false

example (start : ℕ) :
    ((runSeedSearchIndexed countedAnswer id 0).run start).2 ≤ start + 6 :=
  runSeedSearchIndexed_clock id 1 countedAnswer id 0 (fun _ _ _ => le_rfl) start

-- Exhausting the counter returns one unsuccessful search result, distinct from branch rejection.
#guard runSeedSearch
  (fun (_ : Fin 2 → Bool) (_ : Fin 1) => [some (ControllerVerdict.bad 1)]) [] 0 = [none]

private def emptySeed (_ : Fin 0 → Bool) (_ : Fin 1) : List (Option ControllerVerdict) :=
  [some (.decided false)]

#guard runSeedSearch emptySeed [] 0 = [some ⟨0, false⟩]

private abbrev r : Fin 2 → Fin 2 → Prop := fun _ _ => (false : Bool) = true

private theorem empty_unique (s : Fin 2) (k : ℕ) : ∃! w, Passes r s k w := by
  have hr : round r s k = round r s 0 := by
    ext v
    rw [mem_round, mem_round, Relation.reachableWithin_zero, Set.mem_singleton_iff]
    constructor
    · intro h
      exact (Relation.reflTransGen_iff_eq (fun _ => by simp [r])).mp h.reflTransGen
    · rintro rfl
      exact Relation.reachableWithin_mono (Nat.zero_le k) (by simp)
  simpa only [passes_iff, hr] using existsUnique_passes_zero r s

private noncomputable def replay (_ : Fin 2 → Bool) (s : Fin 2) :
    List (Option ControllerVerdict) :=
  runController (m := List) (fun _ _ => pure false) (replayMembership (fun _ _ => false) s) 1

/-- The actual successful typed replay enumeration supplies the controller contract. The
search selects binary seed zero and gives the correct negative reachability answer. This
uses proof-level replay semantics and does not claim native compilation. -/
example : ∃ result, runSeedSearch replay (List.finRange 2) 0 = [some result] ∧
    result.seed = 0 ∧ result.reachable = false := by
  have hc (seed : Fin 2 → Bool) (s : Fin 2) : ∃ verdict, replay seed s = [some verdict] ∧
      match verdict with
      | .bad j => ¬ ∃! w, Passes r s j w
      | .decided b => (∀ j, ∃! w, Passes r s j w) ∧
          (b = true ↔ Relation.ReflTransGen r s 1) := by
    obtain ⟨v, hv, hs⟩ := runController_replay_correct (fun _ _ : Fin 2 => false) s 1
    refine ⟨v, hv, ?_⟩
    cases v with
    | bad j => exact hs.2
    | decided b => exact hs
  obtain ⟨result, hrun, _, hmin, hans⟩ := runSeedSearch_correct (m := List)
    (r := fun _ => r) (source := 0) (target := 1) (List.finRange 2) hc
    ⟨fun _ => false, empty_unique 0, fun s _ => empty_unique s⟩
  refine ⟨result, hrun, ?_, ?_⟩
  · apply Fin.ext
    change result.seed.val = 0
    by_contra hn
    have hlt : (0 : Fin 4) < result.seed := by change 0 < result.seed.val; omega
    exact (hmin 0 hlt) ⟨empty_unique 0, fun s _ => empty_unique s⟩
  · have hn : ¬ Relation.ReflTransGen r (0 : Fin 2) 1 := by
      rw [Relation.reflTransGen_iff_eq (fun _ => by simp [r])]
      decide
    exact Bool.eq_false_iff.mpr (fun h => hn (hans.mp h))

end CslibFrontierTests.IsolationSeedSearch
