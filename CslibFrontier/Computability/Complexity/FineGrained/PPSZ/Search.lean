/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.PPSZ.Defs
public import Mathlib.Data.List.Sections

/-!
# Deciding w-implication by a finite search

`Cslib.Complexity.PPSZ.WImplied` quantifies over subformulas and total assignments. This file
reduces it to a search over finite lists: `x = b` is w-implied under `τ` exactly when `τ` already
sets `x` to `b`, or some choice of `w` clauses of `φ` (with repetitions) has no compatible choice of
one literal per clause under `τ` with `x` set to `!b` (`Cslib.Complexity.PPSZ.wImplied_iff_test`).
A choice of literals is compatible when `τ` falsifies none of them and no two are complementary
(`Cslib.Complexity.PPSZ.compatible`); a list of clauses has an extension of a partial assignment
that satisfies it exactly when some choice of one literal per clause is compatible
(`Cslib.Complexity.PPSZ.satExt_iff`). Both choices are sections of lists (`List.sections`), the
lists picking one element from each of a list of lists, so the test is a nested search over
sections. The search is the one the word-RAM program
`Cslib.Algorithms.WordRAM.PPSZ.impliedCode` runs.

## Main definitions

* `Cslib.Complexity.PPSZ.SatExt`: some extension of a partial assignment satisfies a formula.
* `Cslib.Complexity.PPSZ.compatible`: a choice of literals can be made true by an extension of a
  partial assignment.
* `Cslib.Complexity.PPSZ.impliedTest`: the finite search deciding w-implication.

## Main results

* `Cslib.Complexity.PPSZ.satExt_iff`: satisfiability by an extension through compatible
  sections.
* `Cslib.Complexity.PPSZ.wImplied_iff_test`: w-implication is the finite search.
* `Cslib.Complexity.PPSZ.implied_eq_test`: the implied value through the search.

## References

* [R. Paturi, P. Pudlák, M. Saks, F. Zane, *An improved exponential-time algorithm for
  k-SAT*][PaturiPudlakSaksZane2005]
* [T. Hertli, *3-SAT faster and simpler*][Hertli2011]
-/

@[expose] public section

namespace Cslib.Complexity.PPSZ

open Cslib.Logic.PL

variable {n : ℕ}

/-- Some total assignment extending the partial assignment `ρ` satisfies `ψ`. -/
def SatExt (ρ : Fin n → Option Bool) (ψ : CNF (Fin n)) : Prop :=
  ∃ σ : Fin n → Bool, (∀ y c, ρ y = some c → σ y = c) ∧ ψ.eval σ = true

/-- The literals `ls` can be made true together by an extension of the partial assignment `ρ`:
`ρ` falsifies none of them, and no two of them are complementary. -/
def compatible (ρ : Fin n → Option Bool) (ls : List (Literal (Fin n))) : Bool :=
  ls.all (fun l => ρ l.1 != some (!l.2)) && ls.all fun l => ls.all fun l' => l' != (l.1, !l.2)

/-- **Satisfiability by an extension through choices of literals.** Some extension of `ρ`
satisfies the clauses `ψ` exactly when some choice of one literal from each clause is
compatible with `ρ`. -/
theorem satExt_iff (ρ : Fin n → Option Bool) (ψ : CNF (Fin n)) :
    SatExt ρ ψ ↔ ∃ ls ∈ ψ.sections, compatible ρ ls = true := by
  constructor
  · rintro ⟨σ, hσρ, hψ⟩
    -- choose a true literal in each clause
    have key : ∀ ψ : CNF (Fin n), ψ.eval σ = true →
        ∃ ls ∈ ψ.sections, ∀ l ∈ ls, σ l.1 = l.2 := by
      intro ψ h
      induction ψ with
      | nil => exact ⟨[], by simp, by simp⟩
      | cons c ψ ih =>
        simp only [CNF.eval, List.all_cons, Bool.and_eq_true] at h
        obtain ⟨ls, hls, hl⟩ := ih h.2
        obtain ⟨l, hlc, hlσ⟩ := List.any_eq_true.mp h.1
        exact ⟨l :: ls, List.mem_flatMap.2 ⟨ls, hls, List.mem_map.2 ⟨l, hlc, rfl⟩⟩,
          List.forall_mem_cons.2 ⟨by simpa [Literal.eval] using hlσ, hl⟩⟩
    obtain ⟨ls, hls, hl⟩ := key ψ hψ
    refine ⟨ls, hls, ?_⟩
    simp only [compatible, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq]
    exact ⟨fun l hl' h => by grind [hσρ _ _ h, hl l hl'],
      fun l hl' _ hl'' h => by grind [hl _ hl'', hl l hl']⟩
  · rintro ⟨ls, hls, hc⟩
    simp only [compatible, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at hc
    obtain ⟨hρ, hpair⟩ := hc
    classical
    -- the extension: the chosen literals' values, then `ρ`
    let σ : Fin n → Bool := fun v =>
      match ls.find? (fun l => l.1 = v) with
      | some l => l.2
      | none => (ρ v).getD false
    have hσl : ∀ l ∈ ls, σ l.1 = l.2 := by
      intro l hl
      simp only [σ]
      rcases hf : ls.find? (fun l' => l'.1 = l.1) with _ | l'
      · exact absurd hf fun h => List.find?_eq_none.1 h l hl (by simp)
      · have hv : l'.1 = l.1 := by simpa using List.find?_some hf
        have := hpair l hl l' (List.mem_of_find?_eq_some hf)
        cases hb : l'.2 <;> cases hb' : l.2 <;> simp_all [Prod.ext_iff]
    refine ⟨σ, fun y c hy => ?_, ?_⟩
    · simp only [σ]
      rcases hf : ls.find? (fun l' => l'.1 = y) with _ | l'
      · simp only [hf, hy, Option.getD_some]
      · have hv : l'.1 = y := by simpa using List.find?_some hf
        have := hρ l' (List.mem_of_find?_eq_some hf)
        rw [hv, hy] at this
        cases hb : l'.2 <;> cases c <;> simp_all
    · -- every clause contains its chosen literal
      have key : ∀ (ψ : CNF (Fin n)) (ls' : List (Literal (Fin n))), ls' ∈ ψ.sections →
          (∀ l ∈ ls', σ l.1 = l.2) → ψ.eval σ = true := by
        intro ψ ls' hls' hl'
        induction ψ generalizing ls' with
        | nil => rfl
        | cons c ψ ih =>
          simp only [List.sections, List.mem_flatMap, List.mem_map] at hls'
          obtain ⟨t, ht, l, hlc, rfl⟩ := hls'
          simp only [CNF.eval, List.all_cons, Bool.and_eq_true]
          refine ⟨List.any_eq_true.mpr ⟨l, hlc, ?_⟩, ih t ht fun l' h => hl' l' (by simp [h])⟩
          simpa [Literal.eval] using hl' l (by simp)
      exact key ψ ls hls hσl

/-- The empty list of clauses is satisfied by an extension of any partial assignment. -/
theorem satExt_nil (ρ : Fin n → Option Bool) : SatExt ρ [] :=
  ⟨fun v => (ρ v).getD false, fun y c hy => by simp [hy], rfl⟩

/-- Satisfiability by an extension depends only on the set of clauses. -/
theorem satExt_congr {ρ : Fin n → Option Bool} {ψ ψ' : CNF (Fin n)}
    (h : ∀ c, c ∈ ψ ↔ c ∈ ψ') : SatExt ρ ψ ↔ SatExt ρ ψ' := by
  simp only [SatExt, CNF.eval, List.all_eq_true, h]

/-- Sections of `n` copies of `l` are the lists of length `n` with entries in `l`. -/
theorem mem_sections_replicate {α : Type*} {l : List α} {k : ℕ} {f : List α} :
    f ∈ (List.replicate k l).sections ↔ f.length = k ∧ ∀ a ∈ f, a ∈ l := by
  rw [List.mem_sections]
  induction f generalizing k with
  | nil => cases k <;> simp
  | cons a f ih => cases k <;> simp [List.replicate_succ, ih, and_left_comm]

/-- **The finite search deciding w-implication**: `τ` sets `x` to `b`, or some choice of `w`
clauses of `φ` has no compatible choice of literals under `τ` with `x` set to `!b`. -/
def impliedTest (φ : CNF (Fin n)) (w : ℕ) (τ : Fin n → Option Bool) (x : Fin n) (b : Bool) :
    Bool :=
  τ x == some b || (List.replicate w φ).sections.any fun cs =>
    !cs.sections.any (compatible (Function.update τ x (some !b)))

/-- **w-implication is a finite search.** `x = b` is w-implied under `τ` exactly when
`impliedTest` accepts. -/
theorem wImplied_iff_test (φ : CNF (Fin n)) (w : ℕ) (τ : Fin n → Option Bool) (x : Fin n)
    (b : Bool) : WImplied φ w τ x b ↔ impliedTest φ w τ x b = true := by
  set ρ := Function.update τ x (some !b) with hρ
  -- implication by one subformula
  have hone : ∀ ψ : CNF (Fin n),
      (∀ σ : Fin n → Bool, (∀ y c, τ y = some c → σ y = c) → ψ.eval σ = true → σ x = b) ↔
        τ x = some b ∨ ¬SatExt ρ ψ := fun ψ => by
    constructor
    · intro h
      by_contra hc
      simp only [not_or, not_not] at hc
      obtain ⟨hτx, σ, hσρ, hψ⟩ := hc
      have hσx : σ x = !b := hσρ x _ (by simp [hρ])
      have hστ (y : Fin n) (c : Bool) (hy : τ y = some c) : σ y = c := by
        rcases eq_or_ne y x with rfl | hyx
        · cases c <;> cases b <;> simp_all
        · exact hσρ y c (by rwa [hρ, Function.update_of_ne hyx])
      grind [h σ hστ hψ]
    · rintro (hτx | hsat) σ hστ hψ
      · exact hστ x b hτx
      · by_contra hσx
        refine hsat ⟨σ, fun y c hy => ?_, hψ⟩
        rw [hρ, Function.update_apply] at hy
        split_ifs at hy with hyx
        · subst hyx
          cases h : σ y <;> cases b <;> simp_all
        · exact hστ y c hy
  have hsearch : (∃ ψ : CNF (Fin n), (∀ c ∈ ψ, c ∈ φ) ∧ ψ.length ≤ w ∧ ¬SatExt ρ ψ) ↔
      ∃ cs ∈ (List.replicate w φ).sections, ¬SatExt ρ cs := by
    constructor
    · rintro ⟨_ | ⟨c₀, ψ'⟩, hsub, hlen, hsat⟩
      · exact absurd (satExt_nil ρ) hsat
      refine ⟨c₀ :: ψ' ++ List.replicate (w - (ψ'.length + 1)) c₀, ?_, ?_⟩
      · rw [mem_sections_replicate]
        refine ⟨by simp at hlen ⊢; omega, fun c hc => ?_⟩
        exact (List.mem_append.mp hc).elim (hsub c)
          fun h => List.eq_of_mem_replicate h ▸ hsub c₀ List.mem_cons_self
      · rwa [satExt_congr fun c => ⟨fun hc => ?_, List.mem_append_left _⟩]
        exact (List.mem_append.mp hc).elim id fun h =>
          List.eq_of_mem_replicate h ▸ List.mem_cons_self
    · rintro ⟨cs, hcs, hsat⟩
      rw [mem_sections_replicate] at hcs
      exact ⟨cs, hcs.2, hcs.1.le, hsat⟩
  have hdec : ∀ cs : CNF (Fin n), ¬SatExt ρ cs ↔ (!cs.sections.any (compatible ρ)) = true := by
    grind [satExt_iff]
  unfold WImplied
  simp only [hone, impliedTest, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, ← hρ, ← hdec]
  refine ⟨?_, ?_⟩
  · rintro ⟨ψ, hsub, hlen, hτx | hsat⟩
    exacts [.inl hτx, .inr (hsearch.mp ⟨ψ, hsub, hlen, hsat⟩)]
  · rintro (hτx | h)
    exacts [⟨[], by simp, Nat.zero_le _, .inl hτx⟩,
      (hsearch.mpr h).imp fun ψ ⟨hsub, hlen, hsat⟩ => ⟨hsub, hlen, .inr hsat⟩]

/-- **The implied value through the search**: `true` if the search accepts `x = true`, otherwise
`false` if it accepts `x = false`, and none otherwise. -/
theorem implied_eq_test (φ : CNF (Fin n)) (w : ℕ) (τ : Fin n → Option Bool) (x : Fin n) :
    implied φ w τ x =
      if impliedTest φ w τ x true then some true
      else if impliedTest φ w τ x false then some false else none := by
  simp only [implied, wImplied_iff_test]

end Cslib.Complexity.PPSZ
