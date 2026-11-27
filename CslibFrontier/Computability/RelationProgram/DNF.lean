/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.RelationProgram
public import CslibFrontier.Logics.Propositional.DNF
public import CslibFrontier.Logics.Propositional.CNF.Encoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size

/-!
# Universal DNF certificates for relation programs

For every proposed set of ground facts, the matrix tests that the query holds or a closure
implication is violated. Each violation uses at most three literals and each fact contributes
at most two terms. All costs here are representation sizes.

## Main definitions

* `certificateMatrix`: the DNF under universal quantification.

## Main results

* `certificateMatrix_correct`, `matrix_terms`, `certificateMatrix_bits_upper`.
-/

public section

namespace Cslib.RelationProgram

open Cslib.Logic.PL Turing.MultiTapeTM

variable {r H : ℕ}

/-- Each term is one way for a truth assignment to violate this equation's
closure implication. Disjunction in the premise creates two such terms. -/
def violations (P : Program r H) (f : Fact r H) : DNF Nat :=
  let no := (name f, false)
  match P f.predicate with
  | .top => [[no]]
  | .bot => []
  | .test p b => if f.address.getLsbD p.val = b then [[no]] else []
  | .disj a b => [[(name ⟨a, f.address⟩, true), no], [(name ⟨b, f.address⟩, true), no]]
  | .conj a b => [[(name ⟨a, f.address⟩, true), (name ⟨b, f.address⟩, true), no]]
  | .write a p b => [[(name ⟨a, overwrite f.address p b⟩, true), no]]

/-- A violation term holds precisely for a missing immediate consequence. -/
theorem violations_correct (P : Program r H) (σ : Nat → Bool) (f : Fact r H) :
    (violations P f).eval σ = true ↔
      step P (fun g => σ (name g) = true) f ∧ σ (name f) = false := by
  cases h : P f.predicate <;>
    simp [violations, step, h, DNF.eval, Literal.eval] <;> tauto

/-- A DNF states that the query holds or the proposed set of facts is not closed. -/
def certificateMatrix (P : Program r H) (target : Fact r H) : DNF Nat :=
  [(name target, true)] :: (facts r H).flatMap (violations P)

/-- Universally quantifying the DNF is equivalent to the query being derivable. -/
theorem certificateMatrix_correct (P : Program r H) (target : Fact r H) :
    (∀ σ : Nat → Bool, (certificateMatrix P target).eval σ = true) ↔ derives P target := by
  rw [derives_iff_all_closed]
  have matrix (σ : Nat → Bool) :
      (certificateMatrix P target).eval σ = true ↔
        σ (name target) = true ∨
          ∃ f, step P (fun g => σ (name g) = true) f ∧ σ (name f) = false := by
    have anyViol (f : Fact r H) :
        (violations P f).any (Term.eval σ) = true ↔ _ := violations_correct P σ f
    simp [certificateMatrix, DNF.eval, Term.eval, Literal.eval, List.any_flatMap,
      List.any_eq_true, anyViol, mem_facts]
  constructor
  · intro hall X hX
    classical
    let σ (i : Nat) : Bool := decide (∃ f, name f = i ∧ X f)
    have eval (f : Fact r H) : σ (name f) = true ↔ X f := by
      simp only [σ, decide_eq_true_eq, name_injective.eq_iff, exists_eq_left]
    have eq : (fun f => σ (name f) = true) = X := funext fun f => propext (eval f)
    rcases (matrix σ).mp (hall σ) with h | ⟨f, hf, no⟩
    · exact (eval _).mp h
    · have ht : σ (name f) = true := (eval f).mpr (hX f (eq ▸ hf))
      exact (Bool.noConfusion (ht.symm.trans no))
  · intro hall σ
    apply (matrix σ).mpr
    by_cases closed : Closed P (fun f => σ (name f) = true)
    · exact Or.inl (hall _ closed)
    · right
      unfold Closed at closed
      push Not at closed
      obtain ⟨f, hf, hfalse⟩ := closed
      exact ⟨f, hf, Bool.eq_false_iff.mpr hfalse⟩

private theorem violations_names (P : Program r H) (f : Fact r H) :
    ∀ t ∈ violations P f, ∀ l ∈ t, l.1 < r * 2 ^ H := by
  unfold violations
  split
  · simp [name_lt]
  · simp
  · split <;> simp [name_lt]
  · intro t ht l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
      rcases hl with rfl | rfl <;> exact name_lt _
  · intro t ht l hl
    obtain rfl := List.mem_singleton.mp ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl <;> exact name_lt _
  · intro t ht l hl
    obtain rfl := List.mem_singleton.mp ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> exact name_lt _

/-- Every literal in the matrix refers to one of the grounded facts. -/
theorem certificateMatrix_name_lt (P : Program r H) (target : Fact r H)
    {t : Term ℕ} (ht : t ∈ certificateMatrix P target)
    {l : Literal ℕ} (hl : l ∈ t) : l.1 < r * 2 ^ H := by
  rcases List.mem_cons.mp ht with e | other
  · subst t
    obtain rfl := List.mem_singleton.mp hl
    exact name_lt target
  · obtain ⟨f, _, hf⟩ := List.mem_flatMap.mp other
    exact violations_names P f t hf l hl

/-- Quantifying only the finite block of ground variables suffices for the universal DNF. -/
theorem certificateMatrix_finite_correct (P : Program r H) (target : Fact r H) :
    (∀ σ : Fin (r * 2 ^ H) → Bool, (certificateMatrix P target).eval
      (fun v => if h : v < r * 2 ^ H then σ ⟨v, h⟩ else false) = true) ↔
      derives P target := by
  constructor
  · intro valid
    apply (certificateMatrix_correct P target).mp
    intro σ
    obtain ⟨t, ht, holds⟩ := (DNF.eval_eq_true_iff _ _).mp (valid (fun v => σ v.val))
    refine (DNF.eval_eq_true_iff _ _).mpr ⟨t, ht, (Term.eval_eq_true_iff _ _).mpr ?_⟩
    intro l hl
    have h := (Term.eval_eq_true_iff _ _).mp holds l hl
    simpa only [dite_eq_left (certificateMatrix_name_lt P target ht hl)] using h
  · intro derived σ
    exact (certificateMatrix_correct P target).mpr derived _

private theorem violations_length (P : Program r H) (f : Fact r H) :
    (violations P f).length ≤ 2 := by
  unfold violations
  split <;> simp
  split <;> simp

private theorem violations_term_length (P : Program r H) (f : Fact r H) :
    ∀ t ∈ violations P f, t.length ≤ 3 := by
  unfold violations
  split
  · simp
  · simp
  · split <;> simp
  · simp
  · simp
  · simp

/-- The universal DNF has at most two violation terms per fact plus the query. -/
theorem matrix_terms (P : Program r H) (target : Fact r H) :
    (certificateMatrix P target).length ≤ 2 * (r * 2 ^ H) + 1 := by
  have count (fs : List (Fact r H)) :
      (fs.flatMap (violations P)).length ≤ 2 * fs.length := by
    induction fs with
    | nil => simp
    | cons f fs ih =>
      have bound := violations_length P f
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega
  have h := count (facts r H)
  rw [facts_length] at h
  simp only [certificateMatrix, List.length_cons]
  omega

/-- The encoded matrix has an explicit bit bound in the number of ground facts. -/
theorem certificateMatrix_bits_upper (P : Program r H) (target : Fact r H) :
    let F := r * 2 ^ H
    let B := Nat.log2 F + 1
    (encCNFOver encNat (certificateMatrix P target)).length ≤
      (2 * F + 1) * (24 * B + 31) := by
  let F := r * 2 ^ H
  let B := Nat.log2 F + 1
  let d := certificateMatrix P target
  have clause (t : Clause Nat) (ht : t ∈ d) : ((encClause encNat) t).length ≤
      3 * (4 * B + 5) := by
    have literals (l : Literal Nat) (hl : l ∈ t) :
        ((encPair encNat encBool) l).length ≤ 2 * B + 2 := by
      have lt : l.1 < F := certificateMatrix_name_lt P target ht hl
      have size : (encNat l.1).length ≤ B := length_encNat_le_log2 lt.le
      rw [length_encPair, encBool_apply]
      change 2 * (encNat l.1).length + 1 + 1 ≤ _
      omega
    have term : t.length ≤ 3 := by
      rcases List.mem_cons.mp ht with e | other
      · subst t
        exact (by decide : 1 ≤ 3)
      · obtain ⟨f, _, hf⟩ := List.mem_flatMap.mp other
        exact violations_term_length P f t hf
    have bound := length_encList_le (encPair encNat encBool) t (b := 2 * B + 2) literals
    exact bound.trans (by
      have eq : 2 * (2 * B + 2) + 1 = 4 * B + 5 := by omega
      rw [eq]
      exact Nat.mul_le_mul_right _ term)
  change (encCNFOver encNat d).length ≤ _
  have h := length_encList_le (encClause encNat) d (b := 3 * (4 * B + 5)) clause
  have hl : d.length ≤ 2 * F + 1 := matrix_terms P target
  refine h.trans ?_
  have eq : 2 * (3 * (4 * B + 5)) + 1 = 24 * B + 31 := by omega
  rw [eq]
  exact Nat.mul_le_mul_right _ hl
end Cslib.RelationProgram
