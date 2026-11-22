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
suffixes and keeps the frame invariant at each resumption.

## Main results

* `subsingleton_successful_firstHalting` bounds the number of successful selector lists.
-/

public section

namespace Cslib.Complexity.STCON.SeedSchedulerMachine

open Cslib.DoubleCounting
open _root_.Turing

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
  let M := machine setup scan start verdict
  have terminal (result : Option (Option Answer)) {left right : List Bool}
      (hl : M.FirstHalting input left (.inr result))
      (hr : M.FirstHalting input right (.inr result)) :
      left = right := by
    have hhalt : M.halted (.inr result) = true :=
      machine_halted setup scan start verdict (.inr result)
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
        cases hstep : seedSchedulerStep frame ret with
        | none =>
          rw [hstep] at hlr hrr
          exact terminal none hlr.1 hrr.1
        | some result =>
          rw [hstep] at hlr hrr
          cases result with
          | inr answer => exact terminal _ hlr.1 hrr.1
          | inl next =>
            obtain ⟨hvalid, hsame, _⟩ := seedSchedulerStep_progress hf hstep
            exact ih l hlt next (hsame.trans hsetup) hvalid r a b hlr hrr
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
        have heq : value = other := by tauto
        subst other
        have hlt : l.length < left.length := by
          rw [hleft, List.length_append, List.length_cons]
          omega
        rw [hleft, hright, fromResume (some value) l r hlt hlr hrr]
      · rw [enter, ite_eq_right hneeds] at hl hr
        obtain ⟨l, hleft, hlr⟩ := (firstHalting_skip_iff setup scan start verdict input frame
          left a).mp hl
        obtain ⟨r, hright, hrr⟩ := (firstHalting_skip_iff setup scan start verdict input frame
          right b).mp hr
        have hlt : l.length < left.length := by simp [hleft]
        rw [hleft, hright, fromResume none l r hlt hlr hrr]
  have returned (s : State σ) (h : (reply s).isSome) : ∃ a, s = .inr (some a) := by
    cases s with
    | inl state => simp [reply] at h
    | inr result =>
      cases result with
      | none => simp [reply] at h
      | some answer => exact ⟨answer, rfl⟩
  change {bits : List Bool | M.FirstHalting input bits M.init ∧
    (reply (M.run input bits)).isSome}.Subsingleton
  intro left hl right hr
  obtain ⟨a, ha⟩ := returned _ hl.2
  obtain ⟨b, hb⟩ := returned _ hr.2
  change M.replay input left M.init = .inr (some a) at ha
  change M.replay input right M.init = .inr (some b) at hb
  have hlf : M.FirstHalting input left M.init := hl.1
  have hrf : M.FirstHalting input right M.init := hr.1
  rw [machine_init] at hlf hrf ha hb
  cases hentry : seedSchedulerCandidate setup 0 with
  | none =>
    rw [hentry] at hlf hrf
    exact terminal (some none) hlf hrf
  | some frame =>
    rw [hentry] at hlf hrf ha hb
    obtain ⟨hf, hsame, _⟩ := seedSchedulerCandidate_valid hentry
    exact fromFrame left frame hsame hf right a b ⟨hlf, ha⟩ ⟨hrf, hb⟩

end Cslib.Complexity.STCON.SeedSchedulerMachine
