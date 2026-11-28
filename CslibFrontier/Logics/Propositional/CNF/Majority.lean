/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Polymorphism
public import CslibFrontier.Logics.Propositional.CNF
public import CslibFrontier.Foundations.Data.BitString.Hamming
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases

/-!
# Majority preservation and 2CNF definability

A Boolean relation on finitely many coordinates is preserved by majority exactly when it is
definable by a CNF formula with clauses of width at most two. This is the bijunctive branch of
the Boolean preservation classification, [Bodirsky2026], Lemma 6.32 (September 14, 2026 version,
Section 6.6, p. 76). Finite coordinate types replace the source's numbered variables; empty
relations and nullary relations are included explicitly. The finite-projection proof here is
original, rather than the source's proof through reduced CNF. This is not Schaefer's complexity
dichotomy; [Chen2006CSP], Section 4, treats the corresponding tractability results.

Relations are `Set (V → Bool)`, and defining formulas use precisely the existing `CNF V`
semantics, with no auxiliary variables. Empty relations and empty coordinate types are allowed;
an empty clause defines falsity, and the empty CNF defines truth. No complexity certificate for
constructing the defining CNF is claimed.

## Main results

* `Cslib.Logic.PL.isPolymorphism_majority_iff`: majority preservation expressed using the
  existing coordinatewise median.
* `Cslib.Logic.PL.mem_of_pairwise_of_majority`: a nonempty majority-closed finite relation is
  determined by its projections onto at most two coordinates.
* `Cslib.Logic.PL.isPolymorphism_majority_iff_exists_twoCNF`: the characterization.
-/

public section

namespace Cslib.Logic.PL

open Cslib.BitString

variable {V : Type*}

/-- Majority preservation can equivalently be expressed by closure under coordinatewise median. -/
theorem isPolymorphism_majority_iff (R : Set (V → Bool)) :
    IsPolymorphism (Cslib.majority 3) R ↔
      ∀ x ∈ R, ∀ y ∈ R, ∀ z ∈ R, median x y z ∈ R := by
  constructor
  · intro h x hx y hy z hz
    have ht : ∀ j : Fin 3, ![x, y, z] j ∈ R := by
      intro j
      fin_cases j <;> assumption
    convert h ![x, y, z] ht using 1
    funext i
    exact median_apply_eq_majority x y z i
  · intro h a ha
    convert h (a 0) (ha 0) (a 1) (ha 1) (a 2) (ha 2) using 1
    funext i
    rw [median_apply_eq_majority]
    congr 1 with j : 1
    fin_cases j <;> rfl

private theorem medianBit_eq_iff : ∀ x y z b : Bool,
    (x && y || y && z || z && x) = b ↔
      (x = b ∧ y = b) ∨ (y = b ∧ z = b) ∨ (z = b ∧ x = b) := by
  decide

/-- A nonempty majority-closed relation on finitely many coordinates contains a tuple whenever
each of its pairs of coordinates extends to a tuple in the relation. Pairing a coordinate with
itself includes singleton projections; nonemptiness handles the empty coordinate type. -/
theorem mem_of_pairwise_of_majority [Finite V] {R : Set (V → Bool)}
    (hR : IsPolymorphism (Cslib.majority 3) R) (hne : R.Nonempty) (a : V → Bool)
    (hp : ∀ i j, ∃ b ∈ R, b i = a i ∧ b j = a j) : a ∈ R := by
  classical
  let _ := Fintype.ofFinite V
  have hclosed := (isPolymorphism_majority_iff R).mp hR
  have extend (s : Finset V) : ∃ b ∈ R, ∀ i ∈ s, b i = a i := by
    refine Finset.strongInductionOn s fun s ih => ?_
    by_cases hs : 2 < s.card
    · obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ := Finset.two_lt_card_iff.mp hs
      obtain ⟨x, hx, hxa⟩ := ih (s.erase i) (Finset.erase_ssubset hi)
      obtain ⟨y, hy, hya⟩ := ih (s.erase j) (Finset.erase_ssubset hj)
      obtain ⟨z, hz, hza⟩ := ih (s.erase k) (Finset.erase_ssubset hk)
      refine ⟨median x y z, hclosed x hx y hy z hz, fun l hl => ?_⟩
      apply (medianBit_eq_iff ..).2
      rcases eq_or_ne i l with rfl | hli
      · exact .inr (.inl ⟨hya i (Finset.mem_erase.2 ⟨hij, hi⟩),
          hza i (Finset.mem_erase.2 ⟨hik, hi⟩)⟩)
      · rcases eq_or_ne j l with rfl | hlj
        · exact .inr (.inr ⟨hza j (Finset.mem_erase.2 ⟨hjk, hj⟩),
            hxa j (Finset.mem_erase.2 ⟨hij.symm, hj⟩)⟩)
        · exact .inl ⟨hxa l (Finset.mem_erase.2 ⟨hli.symm, hl⟩),
            hya l (Finset.mem_erase.2 ⟨hlj.symm, hl⟩)⟩
    · rcases (by omega : s.card = 0 ∨ s.card = 1 ∨ s.card = 2) with hs' | hs' | hs'
      · obtain rfl := Finset.card_eq_zero.mp hs'
        obtain ⟨b, hb⟩ := hne
        exact ⟨b, hb, by simp⟩
      · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hs'
        obtain ⟨b, hb, hi, _⟩ := hp i i
        exact ⟨b, hb, by simpa using hi⟩
      · obtain ⟨i, j, _, rfl⟩ := Finset.card_eq_two.mp hs'
        obtain ⟨b, hb, hi, hj⟩ := hp i j
        exact ⟨b, hb, by simp only [Finset.mem_insert, Finset.mem_singleton]; aesop⟩
  obtain ⟨b, hb, heq⟩ := extend Finset.univ
  exact funext (fun i => heq i (Finset.mem_univ i)) ▸ hb

/-- A clause of width at most two is preserved by coordinatewise majority, including arbitrary
literal signs, repeated variables, the empty clause and unit clauses. -/
theorem Clause.eval_median_of_length_le_two {c : Clause V} (hc : c.length ≤ 2)
    {x y z : V → Bool} (hx : c.eval x = true) (hy : c.eval y = true)
    (hz : c.eval z = true) : c.eval (median x y z) = true := by
  rcases c with _ | ⟨⟨i, b⟩, _ | ⟨⟨j, d⟩, c⟩⟩
  · simp [Clause.eval] at hx
  · simp only [Clause.eval, List.any_cons, List.any_nil, Bool.or_false, Literal.eval,
      beq_iff_eq] at hx hy ⊢
    exact (medianBit_eq_iff ..).2 (.inl ⟨hx, hy⟩)
  · obtain rfl : c = [] := by simpa using hc
    -- Among three satisfying assignments, two agree with one of the two literals.
    simp only [Clause.eval, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
      Literal.eval, beq_iff_eq, median, medianBit_eq_iff] at hx hy hz ⊢
    tauto

/-- Models of a width-two CNF form a majority-preserved relation. -/
theorem CNF.isPolymorphism_majority {φ : CNF V} (hφ : ∀ c ∈ φ, c.length ≤ 2) :
    IsPolymorphism (Cslib.majority 3) {a | φ.eval a = true} := by
  rw [isPolymorphism_majority_iff]
  intro x hx y hy z hz
  exact (CNF.eval_eq_true_iff _ _).mpr fun c hc =>
    c.eval_median_of_length_le_two (hφ c hc)
      ((CNF.eval_eq_true_iff _ _).mp hx c hc)
      ((CNF.eval_eq_true_iff _ _).mp hy c hc)
      ((CNF.eval_eq_true_iff _ _).mp hz c hc)

/-- A tuple outside a majority-closed finite Boolean relation is separated from every tuple in
the relation by a clause with at most two literals. -/
theorem exists_separating_clause_of_majority [Finite V] {R : Set (V → Bool)}
    (hR : IsPolymorphism (Cslib.majority 3) R) {a : V → Bool} (ha : a ∉ R) :
    ∃ c : Clause V, c.length ≤ 2 ∧ (∀ b ∈ R, c.eval b = true) ∧ c.eval a = false := by
  classical
  by_cases hne : R.Nonempty
  · have hn : ¬ ∀ i j, ∃ b ∈ R, b i = a i ∧ b j = a j :=
      fun h => ha (mem_of_pairwise_of_majority hR hne a h)
    obtain ⟨i, j, hij⟩ : ∃ i j, ¬ ∃ b ∈ R, b i = a i ∧ b j = a j := by
      simpa only [not_forall] using hn
    refine ⟨[(i, !a i), (j, !a j)], by simp, ?_, ?_⟩
    · intro b hb
      have hn : ¬ (b i = a i ∧ b j = a j) := fun h => hij ⟨b, hb, h⟩
      simpa only [Clause.eval, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
        Literal.eval, beq_iff_eq, Bool.eq_not] using not_and_or.mp hn
    · simp only [Clause.eval, List.any_cons, List.any_nil, Literal.eval, Bool.beq_not_self,
        Bool.or_false]
  · exact ⟨[], by simp, fun b hb => (hne ⟨b, hb⟩).elim, rfl⟩

/-- **Majority preservation iff 2CNF definability.** Relations on finitely many Boolean
coordinates, including empty and nullary relations, are majority-preserved exactly when they
are the models of a CNF with clauses of width at most two, without auxiliary variables. -/
theorem isPolymorphism_majority_iff_exists_twoCNF [Finite V] (R : Set (V → Bool)) :
    IsPolymorphism (Cslib.majority 3) R ↔
      ∃ φ : CNF V, (∀ c ∈ φ, c.length ≤ 2) ∧ ∀ a, a ∈ R ↔ φ.eval a = true := by
  classical
  let _ := Fintype.ofFinite V
  constructor
  · intro hR
    let ls : List (Literal V) := Finset.univ.toList
    let cs : CNF V := [] :: (ls.map (fun p => [p]) ++
      ls.flatMap (fun p => ls.map (fun q => [p, q])))
    let φ := cs.filter (fun c => ∀ b ∈ R, c.eval b = true)
    have mem_cs (c : Clause V) (hc : c.length ≤ 2) : c ∈ cs := by
      rcases c with _ | ⟨p, _ | ⟨q, _ | ⟨r, c⟩⟩⟩
      · simp [cs]
      · simp [cs, ls]
      · simp [cs, ls]
      · simp at hc
    refine ⟨φ, ?_, fun a => ⟨?_, ?_⟩⟩
    · intro c hc
      have hc' := (List.mem_filter.mp hc).1
      simp only [cs, List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap] at hc'
      rcases hc' with rfl | ⟨p, _, rfl⟩ | ⟨p, _, q, _, rfl⟩ <;> simp
    · intro ha
      exact (CNF.eval_eq_true_iff _ _).mpr fun c hc =>
        of_decide_eq_true (List.mem_filter.mp hc).2 a ha
    · intro ha
      by_contra hn
      obtain ⟨c, hc, hmodels, hfalse⟩ := exists_separating_clause_of_majority hR hn
      have hmem : c ∈ φ := List.mem_filter.mpr ⟨mem_cs c hc, by simpa using hmodels⟩
      exact Bool.false_ne_true (hfalse.symm.trans ((CNF.eval_eq_true_iff _ _).mp ha c hmem))
  · rintro ⟨φ, hφ, heq⟩
    rw [show R = {a | φ.eval a = true} from Set.ext heq]
    exact CNF.isPolymorphism_majority hφ

end Cslib.Logic.PL
