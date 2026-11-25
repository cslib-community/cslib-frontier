/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.SeedScheduler.Machine

/-!
# Successful seed scheduler traces

A successful scheduler replay is unambiguous when each requested scan has at most one
first-halting selector list with a verdict. The proof follows the exact scan and skip
suffixes and keeps the frame invariant at each resumption. When successful scan replies
agree with a pure mathematical callback, the same replay returns the mathematical search result.

## Main results

* `subsingleton_successful_firstHalting` bounds the number of successful selector lists.
* `runSeedSchedulerFor_eq_of_firstHalting` identifies the successful replay result.
-/

public section

namespace Cslib.Complexity.STCON.SeedSchedulerMachine

open Cslib.DoubleCounting
open _root_.Turing

private theorem reply_eq_some_iff {σ : Type} {s : State σ} {answer : Option Answer} :
    reply s = some answer ↔ s = .inr (some answer) := by
  cases s <;> simp [reply]

/-- Each requested scan has at most one successful trace, so the initialized scheduler also
has at most one first-halting selector list with a result. A negative answer and seed
exhaustion are successful results. -/
theorem subsingleton_successful_firstHalting {σ : Type} (setup : SeedSearchSetup)
    (scan : NondeterministicQueryMachine σ) (start : SeedScanRequest → σ)
    (verdict : σ → Option ControllerVerdict) (input : List Bool)
    (hscan : ∀ frame : SeedSchedulerFrame,
      frame.request.setup = setup → frame.Valid → frame.needsScan = true →
      {bits : List Bool | scan.FirstHalting input bits (start frame.request) ∧
        (verdict (scan.replay input bits (start frame.request))).isSome}.Subsingleton) :
    let M := machine setup scan start verdict
    {bits : List Bool | M.FirstHalting input bits M.init ∧
      (reply (M.run input bits)).isSome}.Subsingleton := by
  intro M
  have terminal (result : Option (Option Answer)) {left right : List Bool}
      (hl : M.FirstHalting input left (.inr result))
      (hr : M.FirstHalting input right (.inr result)) :
      left = right := by
    have hhalt := machine_halted setup scan start verdict (.inr result)
    exact ((M.firstHalting_iff_nil_of_halted input left _ hhalt).mp hl).trans
      ((M.firstHalting_iff_nil_of_halted input right _ hhalt).mp hr).symm
  have fromFrame (left : List Bool) :
      ∀ (frame : SeedSchedulerFrame), frame.request.setup = setup → frame.Valid →
        ∀ (right : List Bool) (a b : Option Answer),
        (M.FirstHalting input left (enter start frame) ∧
          M.replay input left (enter start frame) = .inr (some a)) →
        (M.FirstHalting input right (enter start frame) ∧
          M.replay input right (enter start frame) = .inr (some b)) → left = right := by
    induction left using (measure (List.length : List Bool → ℕ)).wf.induction with
    | h left ih =>
      intro frame hsetup hf right a b hl hr
      have fromResume (ret : Option ControllerVerdict) (l r : List Bool)
          (hlt : l.length < left.length)
          (hlr : M.FirstHalting input l (resume start frame ret) ∧
            M.replay input l (resume start frame ret) = .inr (some a))
          (hrr : M.FirstHalting input r (resume start frame ret) ∧
            M.replay input r (resume start frame ret) = .inr (some b)) : l = r := by
        unfold resume at hlr hrr
        rcases hstep : seedSchedulerStep frame ret with _ | (next | answer) <;>
          rw [hstep] at hlr hrr
        · exact terminal none hlr.1 hrr.1
        · obtain ⟨hvalid, hsame, _⟩ := seedSchedulerStep_progress hf hstep
          exact ih l hlt next (hsame.trans hsetup) hvalid r a b hlr hrr
        · exact terminal _ hlr.1 hrr.1
      by_cases hneeds : frame.needsScan = true
      · rw [enter, ite_eq_left hneeds] at hl hr
        obtain ⟨value, l, hread, hlr⟩ :=
          (firstHalting_scan_iff setup scan start verdict input frame (start frame.request)
            left a hneeds).mp hl
        obtain ⟨other, r, hread', hrr⟩ :=
          (firstHalting_scan_iff setup scan start verdict input frame (start frame.request)
            right b hneeds).mp hr
        obtain ⟨prefixBits, hleft, hright, hshared⟩ :=
          scan.readReply_commonPrefix verdict input (start frame.request)
            (hscan frame hsetup hf hneeds) hread hread'
        obtain rfl : value = other := by tauto
        rw [hleft, hright, fromResume (some value) l r
          (by rw [hleft, List.length_append, List.length_cons]; omega) hlr hrr]
      · rw [enter, ite_eq_right hneeds] at hl hr
        obtain ⟨l, hleft, hlr⟩ := (firstHalting_skip_iff setup scan start verdict input frame
          left a).mp hl
        obtain ⟨r, hright, hrr⟩ := (firstHalting_skip_iff setup scan start verdict input frame
          right b).mp hr
        rw [hleft, hright, fromResume none l r (by simp [hleft]) hlr hrr]
  rintro left ⟨hlf, hl⟩ right ⟨hrf, hr⟩
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hl
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hr
  replace ha : M.replay input left M.init = .inr (some a) := reply_eq_some_iff.mp ha
  replace hb : M.replay input right M.init = .inr (some b) := reply_eq_some_iff.mp hb
  rw [machine_init] at hlf hrf ha hb
  cases hentry : seedSchedulerCandidate setup 0 with
  | none =>
    rw [hentry] at hlf hrf
    exact terminal (some none) hlf hrf
  | some frame =>
    rw [hentry] at hlf hrf ha hb
    obtain ⟨hf, hsame, _⟩ := seedSchedulerCandidate_valid hentry
    exact fromFrame left frame hsame hf right a b ⟨hlf, ha⟩ ⟨hrf, hb⟩

/-- A successful initialized machine replay agrees with the monadic search if every
successful scan reply agrees with the search's pure callback. The replay retains the
binary rank and decision of a selected seed and preserves exhaustion. -/
theorem runSeedSchedulerFor_eq_of_firstHalting {m : Type → Type} [AlternativeMonad m]
    [LawfulMonad m] {σ : Type} (setup : SeedSearchSetup)
    (hs : setup.sourceID < setup.parameters.search.subdivision.vertexCount)
    (hr : ∀ position < setup.parameters.search.subdivision.originalCount,
      setup.originalSourceID position < setup.parameters.search.subdivision.vertexCount)
    (hlimit : setup.parameters.search.seedLimit = 2 ^ setup.parameters.search.seedWidth)
    (scan : NondeterministicQueryMachine σ) (start : SeedScanRequest → σ)
    (verdict : σ → Option ControllerVerdict) (input : List Bool)
    (oracle : SeedScanRequest → m (Option ControllerVerdict))
    (hagrees : ∀ (f : SeedSchedulerFrame), f.request.setup = setup → f.Valid →
      f.needsScan = true → ∀ (bits : List Bool) (value : ControllerVerdict),
      scan.FirstHalting input bits (start f.request) →
      verdict (scan.replay input bits (start f.request)) = some value →
      oracle f.request = pure (some value))
    (bits : List Bool) (answer : Option Answer) :
    let M := machine setup scan start verdict
    M.FirstHalting input bits M.init → reply (M.run input bits) = some answer →
    ∃ result, runSeedSchedulerFor setup hs hr (fun f => oracle f.request) = pure result ∧
      result.map (fun a => ⟨a.seed.val, a.reachable⟩) = answer := by
  intro M hfirst hreply
  let pack (a : SeedAnswer setup.parameters.search.seedWidth) : Answer := ⟨a.seed.val, a.reachable⟩
  let interpret (f : SeedSchedulerFrame) :=
    runSeedSchedulerForFrom setup hs hr oracle f.request.seed (f.answer.map fun b => (f.cursor, b))
  have terminalReply (result : Option (Option Answer)) (rest : List Bool)
      (h : M.replay input rest (.inr result) = .inr (some answer)) : result = some answer := by
    rw [M.replay_of_halted input (machine_halted setup scan start verdict (.inr result))] at h
    exact Sum.inr.inj h
  have fromFrame (selectors : List Bool) :
      ∀ (f : SeedSchedulerFrame), f.request.setup = setup → f.Valid →
        (M.FirstHalting input selectors (enter start f) ∧
          M.replay input selectors (enter start f) = .inr (some answer)) →
        ∃ result, interpret f = pure result ∧ result.map pack = answer := by
    induction selectors using (measure (List.length : List Bool → ℕ)).wf.induction with
    | h selectors ih =>
      intro f hsetup hf htrace
      have afterStep (ret : Option ControllerVerdict) (rest : List Bool)
          (hlt : rest.length < selectors.length)
          (hrest : M.FirstHalting input rest (resume start f ret) ∧
            M.replay input rest (resume start f ret) = .inr (some answer))
          (horacle : ∀ value, ret = some value → f.needsScan = true →
            oracle f.request = pure (some value)) :
          ∃ result, interpret f = pure result ∧ result.map pack = answer := by
        rw [resume] at hrest
        rcases hstep : seedSchedulerStep f ret with _ | (g | result) <;> rw [hstep] at hrest
        · cases terminalReply none rest hrest.2
        all_goals
          have hcorrect := runSeedSchedulerForFrom_step setup hs hr oracle hlimit hf hsetup hstep
            horacle
        · obtain ⟨hvalid, hsame, _⟩ := seedSchedulerStep_progress hf hstep
          obtain ⟨result, hresult, hpack⟩ := ih rest hlt g (hsame.trans hsetup) hvalid hrest
          exact ⟨result, hcorrect.trans hresult, hpack⟩
        · refine ⟨_, hcorrect, ?_⟩
          cases result <;> simpa [pack] using Option.some.inj (terminalReply _ rest hrest.2)
      by_cases hneeds : f.needsScan = true
      · rw [enter, ite_eq_left hneeds] at htrace
        obtain ⟨value, rest, hparse, hrest⟩ :=
          (firstHalting_scan_iff setup scan start verdict input f (start f.request)
            selectors answer hneeds).mp htrace
        obtain ⟨prefixBits, hselectors, hcall, hvalue⟩ :=
          (scan.readReply_iff verdict input selectors (start f.request) value rest).mp hparse
        exact afterStep (some value) rest
          (by rw [hselectors, List.length_append, List.length_cons]; omega) hrest fun _ he _ => by
            cases he; exact hagrees f hsetup hf hneeds prefixBits value hcall hvalue
      · rw [enter, ite_eq_right hneeds] at htrace
        obtain ⟨rest, hselectors, hrest⟩ :=
          (firstHalting_skip_iff setup scan start verdict input f selectors answer).mp htrace
        exact afterStep none rest (by simp [hselectors]) hrest (by intro value he; cases he)
  have hzero : 0 < setup.parameters.search.seedLimit := hlimit ▸ Nat.two_pow_pos _
  have hentry := seedSchedulerCandidate_eq_some hzero
  have hstate : M.replay input bits M.init = .inr (some answer) := reply_eq_some_iff.mp hreply
  rw [machine_init, hentry] at hfirst hstate
  obtain ⟨hf, hsetup, _⟩ := seedSchedulerCandidate_valid hentry
  obtain ⟨result, hresult, hpack⟩ := fromFrame bits _ hsetup hf ⟨hfirst, hstate⟩
  exact ⟨result, (runSeedSchedulerForFrom_start setup hs hr oracle).symm.trans hresult, hpack⟩

end Cslib.Complexity.STCON.SeedSchedulerMachine
