/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import CslibFrontier.Foundations.Data.Nat.FindCode
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunPropFinite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.IterateUntil
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# First matching binary candidate in native space

The search retains the predicate's context, one binary candidate, a binary remaining count
and an optional answer. The native loop stops at the first match or when the range is exhausted.
Space is linear in the encoded context, lower bound and count, including the test's workspace.

## Main results

* `Turing.MultiTapeTM.ComputableInSpace.findCode`: native linear space for bounded search.
-/

public section

namespace Turing.MultiTapeTM.ComputableInSpace

private structure SearchState (C : Type) where
  context : C
  cursor : ℕ
  remaining : ℕ
  answer : Option ℕ

variable {C : Type}

private enc_structure encSearchState (encC : C ↪ List Bool) : SearchState C where
  context : encC, cursor : encNat, remaining : encNat, answer : (encOption encNat)

private def searchDone (s : SearchState C) : Bool := s.answer.isSome || decide (s.remaining = 0)

private theorem searchDone_inSpace (encC : C ↪ List Bool) :
    ComputableInSpace searchDone (encSearchState encC) encBool
      (fun s => (encSearchState encC s).length) := by
  have hid := budget_id (BigOLe.refl fun s => (encSearchState encC s).length)
  have ha := budget_optionIsSome (encSearchState_answer_budget encC hid)
  have hz := budget_natIsZero (encSearchState_remaining_budget encC hid)
  exact budget_boolOr ha hz

private def searchStep (test : C × ℕ → Bool) (s : SearchState C) : SearchState C :=
  if searchDone s then s
  else if test (s.context, s.cursor) then
    { s with remaining := s.remaining - 1, answer := some s.cursor }
  else { s with cursor := s.cursor + 1, remaining := s.remaining - 1 }

private theorem searchStep_of_done (test : C × ℕ → Bool) {s : SearchState C}
    (h : searchDone s = true) : searchStep test s = s := by
  simp only [searchStep, h, ↓reduceIte]

private theorem searchStep_inSpace {encC : C ↪ List Bool} {test : C × ℕ → Bool}
    (ht : ComputableInSpace test (encPair encC encNat) encBool
      (fun p => (encPair encC encNat p).length)) :
    ComputableInSpace (searchStep test) (encSearchState encC) (encSearchState encC)
      (fun s => (encSearchState encC s).length) := by
  have hid := budget_id (BigOLe.refl fun s => (encSearchState encC s).length)
  have hc := encSearchState_context_budget encC hid
  have hi := encSearchState_cursor_budget encC hid
  have hr := budget_natPred (encSearchState_remaining_budget encC hid)
  have ha := encSearchState_answer_budget encC hid
  have hp := budget_comp_linear ht (budget_prod hc hi)
  exact budget_ite (searchDone_inSpace encC) hid
    (budget_ite hp (encSearchState_mk_budget encC hc hi hr (budget_optionSome hi))
      (encSearchState_mk_budget encC hc (budget_natSucc hi) hr ha))

private theorem iterate_searchStep_finish (test : C × ℕ → Bool)
    (c : C) (start count : ℕ) :
    let s := (searchStep test)^[count] ⟨c, start, count, none⟩
    searchDone s = true ∧ s.answer = Cslib.findCode (fun m => test (c, m)) start count := by
  induction count generalizing start with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    dsimp only
    rw [Function.iterate_succ_apply]
    have hlive : searchDone (⟨c, start, k + 1, none⟩ : SearchState C) = false := by
      simp [searchDone]
    cases ht : test (c, start)
    · simpa only [searchStep, hlive, Bool.false_eq_true, ht, ↓reduceIte,
        Nat.add_sub_cancel, Cslib.findCode] using ih (start + 1)
    · have hdone : searchDone (⟨c, start, k, some start⟩ : SearchState C) = true := rfl
      simp only [searchStep, hlive, Bool.false_eq_true, ht, ↓reduceIte, Nat.add_sub_cancel,
        Cslib.findCode, Function.iterate_fixed (searchStep_of_done test hdone), hdone, true_and]

private theorem iterate_searchStep_bounds (test : C × ℕ → Bool)
    (c : C) (start count k : ℕ) :
    let s := (searchStep test)^[k] ⟨c, start, count, none⟩
    s.context = c ∧ s.cursor ≤ start + k ∧ s.remaining ≤ count ∧
      s.answer.getD 0 ≤ start + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    let s := (searchStep test)^[k] ⟨c, start, count, none⟩
    change s.context = c ∧ s.cursor ≤ start + k ∧ s.remaining ≤ count ∧
      s.answer.getD 0 ≤ start + k at ih
    change (searchStep test s).context = c ∧ (searchStep test s).cursor ≤ start + (k + 1) ∧
      (searchStep test s).remaining ≤ count ∧ (searchStep test s).answer.getD 0 ≤ start + (k + 1)
    obtain ⟨hc, hi, hr, ha⟩ := ih
    by_cases hdone : searchDone s = true
    · rw [searchStep_of_done test hdone]
      exact ⟨hc, hi.trans (Nat.le_succ _), hr, ha.trans (Nat.le_succ _)⟩
    · have hremain := (Nat.sub_le s.remaining 1).trans hr
      by_cases htest : test (s.context, s.cursor) = true
      · simp only [searchStep, hdone, htest, ↓reduceIte]
        exact ⟨hc, hi.trans (Nat.le_succ _), hremain, hi.trans (Nat.le_succ _)⟩
      · simp only [searchStep, hdone, htest]
        exact ⟨hc, Nat.succ_le_succ hi, hremain, ha.trans (Nat.le_succ _)⟩

/-- Search for the first passing binary candidate, stopping on that match or exhaustion.
The cursor and answer are bounded by the end of the range, and the remaining count only
decreases. -/
theorem findCode {encC : C ↪ List Bool} {test : C × ℕ → Bool}
    (ht : ComputableInSpace test (encPair encC encNat) encBool
      (fun p => (encPair encC encNat p).length)) :
    ComputableInSpace
      (fun p : C × (ℕ × ℕ) => Cslib.findCode (fun m => test (p.1, m)) p.2.1 p.2.2)
      (encPair encC (encPair encNat encNat)) (encOption encNat)
      (fun p => (encPair encC (encPair encNat encNat) p).length) := by
  let encIn := encPair encC (encPair encNat encNat)
  have hctx := fst encC (encPair encNat encNat)
  have hpair := snd encC (encPair encNat encNat)
  have hinit := encSearchState_mk_budget encC hctx hpair.fst' hpair.snd'
    (budget_const (encB := encOption encNat) none)
  let step := searchStep test
  let initial (p : C × (ℕ × ℕ)) : SearchState C := ⟨p.1, p.2.1, p.2.2, none⟩
  have hfinish (p : C × (ℕ × ℕ)) :
      searchDone (step^[p.2.2] (initial p)) = true ∧
        (step^[p.2.2] (initial p)).answer = Cslib.findCode (fun m => test (p.1, m)) p.2.1 p.2.2 :=
    iterate_searchStep_finish test p.1 p.2.1 p.2.2
  have hex (p : C × (ℕ × ℕ)) : ∃ j, searchDone (step^[j] (initial p)) = true :=
    ⟨p.2.2, (hfinish p).1⟩
  let stop (p : C × (ℕ × ℕ)) := Nat.find (hex p)
  have hstop (p : C × (ℕ × ℕ)) : stop p ≤ p.2.2 :=
    Nat.find_min' (hex p) (hfinish p).1
  let B (p : C × (ℕ × ℕ)) := 8 * ((encIn p).length + 1)
  have hstate (p : C × (ℕ × ℕ)) (k : ℕ) (hk : k ≤ stop p) :
      (encSearchState encC (step^[k] (initial p))).length ≤ B p := by
    obtain ⟨hc, hi, hr, ha⟩ := iterate_searchStep_bounds test p.1 p.2.1 p.2.2 k
    let s := step^[k] (initial p)
    have hmono (i : ℕ) (hi : i ≤ p.2.1 + k) :
        (encNat i).length ≤ (encNat p.2.1).length + (encNat p.2.2).length + 1 := by
      exact (length_encNat_mono (hi.trans (Nat.add_le_add_left (hk.trans (hstop p)) _))).trans
        (length_encNat_add_le_add _ _)
    change s.cursor ≤ p.2.1 + k at hi
    have hcursor := hmono s.cursor hi
    change s.remaining ≤ p.2.2 at hr
    have hremaining := length_encNat_mono hr
    have hanswer : (encOption encNat s.answer).length ≤
        (encNat p.2.1).length + (encNat p.2.2).length + 2 := by
      change s.answer.getD 0 ≤ p.2.1 + k at ha
      cases h : s.answer with
      | none => simp
      | some v =>
        have hv := hmono v (by simpa only [h, Option.getD_some] using ha)
        simp only [encOption_some, List.length_cons]
        omega
    change (encPair encC (encPair encNat (encPair encNat (encOption encNat)))
      (s.context, s.cursor, s.remaining, s.answer)).length ≤ _
    change s.context = p.1 at hc
    simp only [B, encIn, length_encPair, hc]
    omega
  have hrun := iterateUntil hinit (searchStep_inSpace ht) (searchDone_inSpace encC)
    (n := stop) (Q := fun p => 2 * B p) (B := B)
    (fun p => Nat.find_spec (hex p))
    (fun p j hj => Bool.eq_false_iff.mpr (Nat.find_min (hex p) hj))
    (fun p k hk => by
      rw [two_mul]
      exact Nat.add_le_add (hstate p k hk) (hstate p k hk)) hstate
  have hl : (fun p => (encIn p).length + 2 * B p + B p) ≼ fun p => (encIn p).length :=
    .of_le_linear 25 24 fun p => by dsimp only [B]; omega
  refine (encSearchState_answer_budget encC (hrun.weaken hl)).of_enc_eq fun p => ?_
  -- Holding a completed state is only used to compare the first stop with the full range.
  have hfixed : step (step^[stop p] (initial p)) = step^[stop p] (initial p) :=
    searchStep_of_done test (Nat.find_spec (hex p))
  have heq : step^[p.2.2] (initial p) = step^[stop p] (initial p) := by
    conv_lhs => rw [← Nat.sub_add_cancel (hstop p)]
    rw [Function.iterate_add_apply, Function.iterate_fixed hfixed]
  rw [← heq, (hfinish p).2]

end Turing.MultiTapeTM.ComputableInSpace
