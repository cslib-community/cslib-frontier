/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import CslibFrontier.Foundations.Data.Nat.FindCode
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# First matching binary candidate in native space

The search retains the predicate's context, one binary candidate and an optional answer.
At a match it holds the state for the remaining clock. Space is linear in the encoded
context, lower bound and count, including the native predicate's workspace.

## Main results

* `Turing.MultiTapeTM.ComputableInSpace.findCode`: native linear space for bounded search.
-/

public section

namespace Turing.MultiTapeTM.ComputableInSpace

private structure SearchState (C : Type) where
  context : C
  cursor : ℕ
  answer : Option ℕ

variable {C : Type}

private enc_structure encSearchState (encC : C ↪ List Bool) : SearchState C where
  context : encC, cursor : encNat, answer : (encOption encNat)

private def searchStep (test : C × ℕ → Bool) (s : SearchState C) : SearchState C :=
  if s.answer.isSome then s
  else if test (s.context, s.cursor) then { s with answer := some s.cursor }
  else { s with cursor := s.cursor + 1 }

private theorem searchStep_inSpace {encC : C ↪ List Bool} {test : C × ℕ → Bool}
    (ht : ComputableInSpace test (encPair encC encNat) encBool
      (fun p => (encPair encC encNat p).length)) :
    ComputableInSpace (searchStep test) (encSearchState encC) (encSearchState encC)
      (fun s => (encSearchState encC s).length) := by
  have hid := budget_id (BigOLe.refl fun s => (encSearchState encC s).length)
  have hc := encSearchState_context_budget encC hid
  have hi := encSearchState_cursor_budget encC hid
  have ha := encSearchState_answer_budget encC hid
  have hp := budget_comp_linear ht (budget_prod hc hi)
  exact budget_ite (budget_optionIsSome ha) hid
    (budget_ite hp (encSearchState_mk_budget encC hc hi (budget_optionSome hi))
      (encSearchState_mk_budget encC hc (budget_natSucc hi) ha))

private theorem iterate_searchStep_answer (test : C × ℕ → Bool)
    (c : C) (start count : ℕ) :
    ((searchStep test)^[count] ⟨c, start, none⟩).answer =
      Cslib.findCode (fun m => test (c, m)) start count := by
  induction count generalizing start with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    cases ht : test (c, start)
    · simpa only [searchStep, Option.isSome_none, Bool.false_eq_true, ht, ↓reduceIte,
        Cslib.findCode] using ih (start + 1)
    · have hhold : searchStep test ⟨c, start, some start⟩ = ⟨c, start, some start⟩ := rfl
      simp only [searchStep, Option.isSome_none, Bool.false_eq_true, ht, ↓reduceIte,
        Cslib.findCode]
      rw [Function.iterate_fixed hhold]

private theorem iterate_searchStep_bounds (test : C × ℕ → Bool)
    (c : C) (start k : ℕ) :
    let s := (searchStep test)^[k] ⟨c, start, none⟩
    s.context = c ∧ s.cursor ≤ start + k ∧ s.answer.getD 0 ≤ start + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    let s := (searchStep test)^[k] ⟨c, start, none⟩
    change s.context = c ∧ s.cursor ≤ start + k ∧ s.answer.getD 0 ≤ start + k at ih
    change (searchStep test s).context = c ∧ (searchStep test s).cursor ≤ start + (k + 1) ∧
      (searchStep test s).answer.getD 0 ≤ start + (k + 1)
    obtain ⟨hc, hi, ha⟩ := ih
    by_cases hfound : s.answer.isSome = true
    · simp only [searchStep, hfound, ↓reduceIte]
      exact ⟨hc, hi.trans (Nat.le_succ _), ha.trans (Nat.le_succ _)⟩
    · by_cases htest : test (s.context, s.cursor) = true
      · simp only [searchStep, hfound, htest, ↓reduceIte]
        exact ⟨hc, hi.trans (Nat.le_succ _), hi.trans (Nat.le_succ _)⟩
      · simp only [searchStep, hfound, htest]
        exact ⟨hc, Nat.succ_le_succ hi, ha.trans (Nat.le_succ _)⟩

/-- Search for the first passing binary candidate. Throughout the search, the encoded
cursor and answer are bounded by the encoded end of the range. -/
theorem findCode [Inhabited C] {encC : C ↪ List Bool} {test : C × ℕ → Bool}
    (ht : ComputableInSpace test (encPair encC encNat) encBool
      (fun p => (encPair encC encNat p).length)) :
    ComputableInSpace
      (fun p : C × (ℕ × ℕ) => Cslib.findCode (fun m => test (p.1, m)) p.2.1 p.2.2)
      (encPair encC (encPair encNat encNat)) (encOption encNat)
      (fun p => (encPair encC (encPair encNat encNat) p).length) := by
  let encIn := encPair encC (encPair encNat encNat)
  have hctx := fst encC (encPair encNat encNat)
  have hpair := snd encC (encPair encNat encNat)
  have hinit := encSearchState_mk_budget encC hctx hpair.fst'
    (budget_const (encB := encOption encNat) none (.refl _))
  let step := searchStep test
  let initial (p : C × (ℕ × ℕ)) : SearchState C := ⟨p.1, p.2.1, none⟩
  let : Inhabited (SearchState C) := ⟨⟨default, 0, none⟩⟩
  have hstate (p : C × (ℕ × ℕ)) (k : ℕ) (hk : k ≤ p.2.2) :
      (encSearchState encC (step^[k] (initial p))).length ≤ 8 * ((encIn p).length + 1) := by
    obtain ⟨hc, hi, ha⟩ := iterate_searchStep_bounds test p.1 p.2.1 k
    let s := step^[k] (initial p)
    have hmono (i : ℕ) (hi : i ≤ p.2.1 + k) :
        (encNat i).length ≤ (encNat p.2.1).length + (encNat p.2.2).length + 1 := by
      exact (length_encNat_mono (hi.trans (Nat.add_le_add_left hk _))).trans
        (length_encNat_add_le_add _ _)
    change s.cursor ≤ p.2.1 + k at hi
    have hcursor := hmono s.cursor hi
    have hanswer : (encOption encNat s.answer).length ≤
        (encNat p.2.1).length + (encNat p.2.2).length + 2 := by
      change s.answer.getD 0 ≤ p.2.1 + k at ha
      cases h : s.answer with
      | none => simp
      | some v =>
        have hv := hmono v (by simpa only [h, Option.getD_some] using ha)
        simp only [encOption_some, List.length_cons]
        omega
    change (encPair encC (encPair encNat (encOption encNat))
      (s.context, s.cursor, s.answer)).length ≤ _
    change s.context = p.1 at hc
    simp only [encIn, length_encPair, hc]
    omega
  have hrun := budget_iterate hpair.snd' hinit (searchStep_inSpace ht) hstate
    (.of_le_linear 8 8 fun _ => by dsimp only [encIn]; omega)
  exact (encSearchState_answer_budget encC hrun).of_enc_eq fun p => by
    rw [iterate_searchStep_answer]

end Turing.MultiTapeTM.ComputableInSpace
