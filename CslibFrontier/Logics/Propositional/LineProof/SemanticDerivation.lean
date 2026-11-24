/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.LineProof
public import CslibFrontier.Logics.Propositional.SemanticDerivation

/-!
# Semantic derivations from `LineProof` derivations

Any `Cslib.Logic.PL.LineProof` whose rules have at most two premises and are sound with respect to
`models : L → Set W` reverses into a semantic derivation (`Cslib.Logic.PL.IsSemanticDerivation`) in
the sense of [Krajíček, Definition 4.1][Krajicek1997]: axioms become `Set.univ`, unary rules repeat
their single premise index twice, and binary rules intersect their two earlier premise sets. When
the derivation also contains an unsatisfiable line, the reversed sequence of model sets is a
semantic refutation (`Cslib.Logic.PL.IsSemanticRefutation`) of the same length.

## Main results

* `Cslib.Logic.PL.LineProof.toSemanticDerivation`: sound derivations of arity at most two reverse
  into semantic derivations.
* `Cslib.Logic.PL.LineProof.toSemanticRefutation`: sound derivations containing an unsatisfiable
  line reverse into semantic refutations of the same length.

## References

* [J. Krajíček, *Interpolation theorems, lower bounds for proof systems, and independence results
  for bounded arithmetic*][Krajicek1997]
-/

public section

namespace Cslib.Logic.PL.LineProof

variable {L W : Type*} {R : Set (LineRule L)} {Γ : Set L} {ls : List L}
  {init : Set (Set W)} {models : L → Set W}

/-- Line `j` of a reversed derivation lies in `init`, equals `Set.univ`, or contains the
intersection of the model sets of two earlier lines. -/
private def SemLineOK (init : Set (Set W)) (models : L → Set W)
    (rev : List L) (j : ℕ) (x : L) : Prop :=
  models x ∈ init ∨ models x = Set.univ ∨
    ∃ j₁ j₂ x₁ x₂, j₁ < j ∧ j₂ < j ∧ rev[j₁]? = some x₁ ∧ rev[j₂]? = some x₂ ∧
      models x₁ ∩ models x₂ ⊆ models x

private theorem SemLineOK.append {rev : List L} {j : ℕ} {x : L}
    (h : SemLineOK init models rev j x) (hj : j < rev.length) (rev' : List L) :
    SemLineOK init models (rev ++ rev') j x := by
  rcases h with h | h | ⟨j₁, j₂, x₁, x₂, h₁, h₂, e₁, e₂, hsub⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨j₁, j₂, x₁, x₂, h₁, h₂, ?_, ?_, hsub⟩)
    · rw [List.getElem?_append_left (by omega), e₁]
    · rw [List.getElem?_append_left (by omega), e₂]

/-- An earlier line of `ls` sits at an index `< ls.length` when read from the first line. -/
private theorem exists_lt_of_mem {x y : L} (hx : x ∈ ls) :
    ∃ j < ls.length, (ls.reverse ++ [y])[j]? = some x := by
  obtain ⟨j, hj, e⟩ := List.getElem_of_mem (List.mem_reverse.2 hx)
  refine ⟨j, by simpa using hj, ?_⟩
  rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj, e]

private theorem semLineOK_reverse_cons {ls₀ : List L} {y : L} {j : ℕ} {x : L}
    (ih : ∀ {j x}, ls₀.reverse[j]? = some x → SemLineOK init models ls₀.reverse j x)
    (hy : SemLineOK init models (ls₀.reverse ++ [y]) ls₀.length y)
    (hj : (y :: ls₀).reverse[j]? = some x) :
    SemLineOK init models (y :: ls₀).reverse j x := by
  rw [List.reverse_cons] at hj ⊢
  by_cases hjl : j < ls₀.length
  · rw [List.getElem?_append_left (by simpa using hjl)] at hj
    exact (ih hj).append (by simpa using hjl) _
  · have hjl' : j = ls₀.length := by
      have := (List.getElem?_eq_some_iff.1 hj).1
      simp only [List.length_append, List.length_reverse, List.length_singleton] at this
      omega
    subst hjl'
    rw [List.getElem?_append_right (by simp)] at hj
    simp only [List.length_reverse, Nat.sub_self, List.getElem?_cons_zero,
      Option.some.injEq] at hj
    subst hj
    exact hy

private theorem semLineOK_of_lineProof (h : LineProof R Γ ls)
    (hinit : ∀ x ∈ Γ, models x ∈ init)
    (harity : ∀ r ∈ R, r.premises.length ≤ 2)
    (hsound : ∀ r ∈ R, ∀ w, (∀ p ∈ r.premises, w ∈ models p) → w ∈ models r.concl)
    {j : ℕ} {x : L} (hj : ls.reverse[j]? = some x) :
    SemLineOK init models ls.reverse j x := by
  induction h generalizing j x with
  | nil => simp at hj
  | hyp _ hy ih => exact semLineOK_reverse_cons ih (Or.inl (hinit _ hy)) hj
  | @step ls₀ r _ hr hp ih =>
    refine semLineOK_reverse_cons ih ?_ hj
    match hm : r.premises with
    | [] =>
      exact Or.inr (Or.inl (Set.eq_univ_of_forall fun w => hsound r hr w (by simp [hm])))
    | [p₁] =>
      obtain ⟨j₁, hj₁, e₁⟩ := exists_lt_of_mem (y := r.concl) (hp p₁ (by simp [hm]))
      exact Or.inr (Or.inr ⟨j₁, j₁, p₁, p₁, hj₁, hj₁, e₁, e₁,
        fun w hw => hsound r hr w (by simp [hm, hw.1])⟩)
    | [p₁, p₂] =>
      obtain ⟨j₁, hj₁, e₁⟩ := exists_lt_of_mem (y := r.concl) (hp p₁ (by simp [hm]))
      obtain ⟨j₂, hj₂, e₂⟩ := exists_lt_of_mem (y := r.concl) (hp p₂ (by simp [hm]))
      exact Or.inr (Or.inr ⟨j₁, j₂, p₁, p₂, hj₁, hj₂, e₁, e₂,
        fun w ⟨hw₁, hw₂⟩ => hsound r hr w (by simp [hm, hw₁, hw₂])⟩)
    | _ :: _ :: _ :: _ =>
      have := harity r hr
      simp [hm] at this

/-- **Semantic derivation of a reversed `LineProof`** [Krajíček, Definition 4.1][Krajicek1997]:
for any rule set `R` whose rules have at most two premises and are sound with respect to `models`,
reading `ls` from its first line (`ls.reverse`) and taking `models` at each line yields a semantic
derivation from `init`. -/
theorem toSemanticDerivation (h : LineProof R Γ ls)
    (hinit : ∀ x ∈ Γ, models x ∈ init)
    (harity : ∀ r ∈ R, r.premises.length ≤ 2)
    (hsound : ∀ r ∈ R, ∀ w, (∀ p ∈ r.premises, w ∈ models p) → w ∈ models r.concl) :
    IsSemanticDerivation init fun j : Fin ls.reverse.length => models ls.reverse[j] := by
  intro j
  rcases semLineOK_of_lineProof h hinit harity hsound (List.getElem?_eq_getElem j.2) with
    hmem | huniv | ⟨j₁, j₂, x₁, x₂, h₁, h₂, e₁, e₂, hsub⟩
  · exact Or.inl hmem
  · exact Or.inr (Or.inl huniv)
  · obtain ⟨hj₁, e₁⟩ := List.getElem?_eq_some_iff.1 e₁
    obtain ⟨hj₂, e₂⟩ := List.getElem?_eq_some_iff.1 e₂
    refine Or.inr (Or.inr ⟨⟨j₁, hj₁⟩, ⟨j₂, hj₂⟩, h₁, h₂, ?_⟩)
    simpa only [Fin.getElem_fin, e₁, e₂] using hsub

/-- **Semantic refutation of a reversed `LineProof`**: if moreover `ls` contains an unsatisfiable
line `bot` (`∀ w, w ∉ models bot`), the reversed model sequence is a semantic refutation of `init`
with `ls.reverse.length` lines. -/
theorem toSemanticRefutation (h : LineProof R Γ ls)
    (hinit : ∀ x ∈ Γ, models x ∈ init)
    (harity : ∀ r ∈ R, r.premises.length ≤ 2)
    (hsound : ∀ r ∈ R, ∀ w, (∀ p ∈ r.premises, w ∈ models p) → w ∈ models r.concl)
    {bot : L} (hbot : bot ∈ ls) (hunsat : ∀ w, w ∉ models bot) :
    IsSemanticRefutation init fun j : Fin ls.reverse.length => models ls.reverse[j] := by
  refine ⟨h.toSemanticDerivation hinit harity hsound, ?_⟩
  obtain ⟨j, hj, e⟩ := List.getElem_of_mem (List.mem_reverse.2 hbot)
  refine ⟨⟨j, hj⟩, Set.eq_empty_of_forall_notMem fun w hw => ?_⟩
  simp only [Fin.getElem_fin, e] at hw
  exact hunsat w hw

end Cslib.Logic.PL.LineProof
