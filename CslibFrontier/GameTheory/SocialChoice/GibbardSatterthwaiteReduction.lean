/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.SocialChoice.GibbardSatterthwaite

/-!
# Nisan's reduction from Gibbard–Satterthwaite to Arrow's theorem

In §9.2.4 of [Nisan2007], Gibbard–Satterthwaite is proved by turning an onto incentive-compatible
social choice function `f : Profile V A → A` into a social welfare function on `A` and applying
Arrow's impossibility theorem. While `CslibFrontier.GameTheory.SocialChoice.GibbardSatterthwaite`
proves the stronger range-cardinality theorem via Maskin monotonicity on `Set.range f`, this
companion module exposes the standalone combinatorial primitives and induced social welfare
function of [Nisan2007]:

* **Single-voter monotonicity** (`SocialChoiceFunction.IsSingleMonotone`, [Nisan2007],
  Definition 9.5): if changing a single voter `i`'s ranking from `P i` to `Q i` changes the chosen
  alternative from `a = f P` to `a' = f Q`, then `i` ranked `a` above `a'` at `P` and ranks `a'`
  above `a` at `Q`. By Proposition 9.6 (`isSingleMonotone_iff_isStrategyProof`), this is
  equivalent to strategy-proofness for any electorate `V` (finite or infinite); composing with the
  library's `isStrategyProof_iff_isMaskinMonotone` yields the derived finite-electorate equivalence
  with Maskin monotonicity (`isSingleMonotone_iff_isMaskinMonotone`).
* **Nisan's induced social welfare function** (`SocialChoiceFunction.nisanSWF`, [Nisan2007],
  Definition 9.9): for a finite electorate `V` and a strategy-proof rule `f` onto `A`, society
  ranks `a` at least as high as `b` on profile `P` when `f (P.toTopSet {a, b}) = a`, where
  `P.toTopSet {a, b}` moves `{a, b}` to the top of every voter's ranking.
* **Lemma 9.10** ([Nisan2007], p. 215): `nisanSWF` is a well-defined social welfare function with
  no ties (antisymmetric as well as transitive and total), equivalently packaged as a strict-order
  rule `SocialChoiceFunction.nisanRanking : Profile V A → Ranking A` whose weak-ranking view is
  `nisanSWF` (`toWeakRanking_nisanRanking`).
* **Lemma 9.11** ([Nisan2007], p. 215): `nisanSWF` satisfies weak Pareto (`nisanSWF_isPareto`,
  assuming a nonempty electorate `[Nonempty V]`, or `[Nontrivial A]`, which forces `Nonempty V`
  when `f` is onto) as well as constant-profile unanimity (`nisanSWF_const`, Definition 9.2),
  satisfies independence of irrelevant alternatives (`nisanSWF_isIIA`), and has the exact same
  dictators as `f` (`nisanSWF_isDictator_iff`, `nisanSWF_isDictatorial_iff`, strengthening
  Lemma 9.11's non-dictatorship implication `¬ f.IsDictatorial → ¬ (f.nisanSWF hf hs).IsDictatorial`
  to a full equivalence).

**Implicit nonemptiness in Lemma 9.11.** [Nisan2007] (§9.2.2, p. 212) assumes an electorate of `n`
voters with `n ≥ 1` implicit (and `|A| ≥ 3` in Theorem 9.8, where surjectivity of `f` already
forces `Nonempty V`). When `V` is empty and `|A| = 1`, `Arrow.lean`'s `IsPareto` fails on the unique
alternative `a = b` because `(∀ i : V, (P i).Prefers a a)` holds vacuously while strict social
preference `(F P).Prefers a a` is irreflexive. Thus `nisanSWF_isPareto` takes `[Nonempty V]`, and
`nisanSWF_isPareto_of_nontrivial` discharges it automatically when `[Nontrivial A]`.

## Main definitions

* `SocialChoiceFunction.IsSingleMonotone`: single-voter monotonicity ([Nisan2007], Definition 9.5).
* `SocialChoiceFunction.nisanSWF`: the social welfare function extending an onto strategy-proof
  social choice function ([Nisan2007], Definition 9.9).
* `SocialChoiceFunction.nisanRanking`: the strict-ranking form `Profile V A → Ranking A` of
  `nisanSWF` ([Nisan2007], Definition 9.1 and Lemma 9.10).

## Main results

* `SocialChoiceFunction.isSingleMonotone_iff_isStrategyProof`: single-voter monotonicity is
  equivalent to strategy-proofness ([Nisan2007], Proposition 9.6).
* `SocialChoiceFunction.isSingleMonotone_iff_isMaskinMonotone`: derived finite-electorate
  equivalence between single-voter monotonicity and Maskin monotonicity (composing Proposition 9.6
  with `isStrategyProof_iff_isMaskinMonotone`).
* `SocialChoiceFunction.nisanSWF_antisymm`, `SocialChoiceFunction.toWeakRanking_nisanRanking`:
  antisymmetry and strict total-order structure of `nisanSWF` ([Nisan2007], Lemma 9.10).
* `SocialChoiceFunction.nisanSWF_isPareto`, `SocialChoiceFunction.nisanSWF_isPareto_of_nontrivial`,
  `SocialChoiceFunction.nisanSWF_const`: unanimity / weak Pareto ([Nisan2007], Lemma 9.11).
* `SocialChoiceFunction.nisanSWF_isIIA`: independence of irrelevant alternatives ([Nisan2007],
  Lemma 9.11).
* `SocialChoiceFunction.nisanSWF_isDictator_iff`,
  `SocialChoiceFunction.nisanSWF_isDictatorial_iff`: full dictator equivalence between `nisanSWF`
  and `f` (strengthening the non-dictatorship implication of [Nisan2007], Lemma 9.11).

## References

* [N. Nisan, *Introduction to mechanism design (for computer scientists)*][Nisan2007]
-/

public section

namespace Cslib.GameTheory.SocialChoice.SocialChoiceFunction

variable {V A : Type*} (f : SocialChoiceFunction V A)

/-- **Single-voter monotonicity** ([Nisan2007], Definition 9.5): if changing a single voter `i`'s
ranking from `P i` to `Q i` changes the social choice from `f P` to `f Q`, then `i` ranked `f P`
above `f Q` at `P` and ranks `f Q` above `f P` at `Q`. Note that [Nisan2007] writes `x ≺ᵢ y` for
"`y` is preferred to `x`", so its `a' ≺ᵢ a` and `a ≺'ᵢ a'` read `(P i).Prefers (f P) (f Q)` and
`(Q i).Prefers (f Q) (f P)`. -/
@[expose] def IsSingleMonotone : Prop :=
  ∀ ⦃P Q : Profile V A⦄ (i : V), (∀ j, j ≠ i → P j = Q j) → f P ≠ f Q →
    (P i).Prefers (f P) (f Q) ∧ (Q i).Prefers (f Q) (f P)

variable {f}

/-- **Proposition 9.6** of [Nisan2007]: a social choice function is single-voter monotone if and
only if it is strategy-proof (incentive compatible). No finiteness assumption on `V` or `A` is
needed. -/
theorem isSingleMonotone_iff_isStrategyProof : f.IsSingleMonotone ↔ f.IsStrategyProof := by
  constructor
  · intro hm P Q i hPQ hman
    have hne : f P ≠ f Q := ((P i).ne_of_prefers hman).symm
    exact (P i).asymm hman (hm i hPQ hne).1
  · intro hf P Q i hPQ hne
    exact ⟨(P i).prefers_of_not_prefers hne.symm (hf P Q i hPQ),
      (Q i).prefers_of_not_prefers hne (hf Q P i fun j hj => (hPQ j hj).symm)⟩

/-- Derived equivalence for finitely many voters: single-voter monotonicity is equivalent to
Maskin monotonicity, obtained by composing Proposition 9.6 (`isSingleMonotone_iff_isStrategyProof`)
with the library's `isStrategyProof_iff_isMaskinMonotone`. -/
theorem isSingleMonotone_iff_isMaskinMonotone [Finite V] :
    f.IsSingleMonotone ↔ f.IsMaskinMonotone :=
  isSingleMonotone_iff_isStrategyProof.trans isStrategyProof_iff_isMaskinMonotone

/-! ### Nisan's induced social welfare function (Definition 9.9 and Lemmas 9.10–9.11) -/

section NisanSWF

variable [Finite V]

/-- **Nisan's induced social welfare function** ([Nisan2007], Definition 9.9 and Lemma 9.10):
given a strategy-proof social choice function `f` onto `A`, society ranks `a` at least as high as
`b` on profile `P` iff `f (P.toTopSet {a, b}) = a`, where `P.toTopSet {a, b}` moves `a` and `b`
to the top of every voter's ranking. Completeness and transitivity are proved by moving two- and
three-element sets to the top ([Nisan2007], Lemma 9.10). -/
def nisanSWF (f : SocialChoiceFunction V A) (hf : f.IsStrategyProof)
    (hs : Function.Surjective f) : SocialWelfareFunction V A :=
  fun P =>
  { AtLeast := fun a b => f (P.toTopSet {a, b}) = a
    total := fun a b => by
      rcases hf.isMaskinMonotone.apply_toTopSet_pair P (b := b) (hs a) with h | h
      · exact Or.inl h
      · right
        rw [Set.pair_comm]
        exact h
    trans := fun a _ _ hab hbc =>
      hf.isMaskinMonotone.apply_toTopSet_pair_trans P (hs a) hab hbc }

@[simp] theorem nisanSWF_atLeast (hf : f.IsStrategyProof) (hs : Function.Surjective f)
    (P : Profile V A) (a b : A) :
    (f.nisanSWF hf hs P).AtLeast a b ↔ f (P.toTopSet {a, b}) = a :=
  Iff.rfl

/-- **Antisymmetry of `nisanSWF`** ([Nisan2007], Lemma 9.10): `nisanSWF` never ties distinct
alternatives, since `{b, a} = {a, b}` has a single chosen outcome `f (P.toTopSet {a, b})`. -/
theorem nisanSWF_antisymm (hf : f.IsStrategyProof) (hs : Function.Surjective f)
    (P : Profile V A) {a b : A}
    (hab : (f.nisanSWF hf hs P).AtLeast a b) (hba : (f.nisanSWF hf hs P).AtLeast b a) :
    a = b := by
  rw [nisanSWF_atLeast] at hab hba
  rw [Set.pair_comm] at hba
  exact hab.symm.trans hba

/-- Strict preference in `nisanSWF`: society strictly prefers `a` to `b` iff `a ≠ b` and `f`
chooses `a` when `{a, b}` is moved to the top. -/
theorem nisanSWF_prefers (hf : f.IsStrategyProof) (hs : Function.Surjective f)
    (P : Profile V A) (a b : A) :
    (f.nisanSWF hf hs P).Prefers a b ↔ a ≠ b ∧ f (P.toTopSet {a, b}) = a := by
  constructor
  · intro h
    have hab : a ≠ b := fun he => (f.nisanSWF hf hs P).prefers_irrefl a (he ▸ h)
    exact ⟨hab, (f.nisanSWF hf hs P).atLeast_of_prefers h⟩
  · rintro ⟨hab, ha⟩ hba
    exact hab (f.nisanSWF_antisymm hf hs P ha hba)

/-- **Strict-ranking form of Nisan's extension** ([Nisan2007], Definition 9.9 and Lemma 9.10):
for every profile `P`, `nisanRanking` produces a strict linear order (`Ranking A`), matching
[Nisan2007]'s `L`-valued definition of a social welfare function (Definition 9.1). -/
def nisanRanking (f : SocialChoiceFunction V A) (hf : f.IsStrategyProof)
    (hs : Function.Surjective f) (P : Profile V A) : Ranking A where
  Prefers a b := (f.nisanSWF hf hs P).Prefers a b
  irrefl := (f.nisanSWF hf hs P).prefers_irrefl
  trans _ _ _ := (f.nisanSWF hf hs P).prefers_trans
  total a b hab := by
    rcases (f.nisanSWF hf hs P).total a b with h | h
    · exact Or.inl ((f.nisanSWF_prefers hf hs P a b).2 ⟨hab, h⟩)
    · exact Or.inr ((f.nisanSWF_prefers hf hs P b a).2 ⟨hab.symm, h⟩)

@[simp] theorem nisanRanking_prefers (hf : f.IsStrategyProof) (hs : Function.Surjective f)
    (P : Profile V A) (a b : A) :
    (f.nisanRanking hf hs P).Prefers a b ↔ (f.nisanSWF hf hs P).Prefers a b :=
  Iff.rfl

/-- Viewing `nisanRanking` as a weak ranking recovers `nisanSWF`. -/
@[simp] theorem toWeakRanking_nisanRanking (hf : f.IsStrategyProof) (hs : Function.Surjective f)
    (P : Profile V A) :
    (f.nisanRanking hf hs P).toWeakRanking = f.nisanSWF hf hs P := by
  ext a b
  rw [Ranking.toWeakRanking_atLeast]
  change a = b ∨ (f.nisanSWF hf hs P).Prefers a b ↔ (f.nisanSWF hf hs P).AtLeast a b
  constructor
  · rintro (rfl | h)
    · exact (f.nisanSWF hf hs P).refl a
    · exact (f.nisanSWF hf hs P).atLeast_of_prefers h
  · intro h
    by_cases hab : a = b
    · exact Or.inl hab
    · exact Or.inr ((f.nisanSWF_prefers hf hs P a b).2 ⟨hab, h⟩)

/-- **Weak Pareto (unanimity)** for `nisanSWF` ([Nisan2007], Lemma 9.11): with a nonempty
electorate, if every voter ranks `a` above `b`, so does `nisanSWF`. -/
theorem nisanSWF_isPareto [Nonempty V] (hf : f.IsStrategyProof) (hs : Function.Surjective f) :
    (f.nisanSWF hf hs).IsPareto := by
  intro P a b h hba
  obtain ⟨i⟩ := ‹Nonempty V›
  have hab : a ≠ b := (P i).ne_of_prefers (h i)
  refine hf.isMaskinMonotone.apply_ne (hs a) hab (P := P.toTopSet {b, a}) (fun j => ?_) hba
  exact ((P j).toTopSet_prefers_iff_of_mem (Set.mem_insert_of_mem _ rfl)
    (Set.mem_insert _ _)).2 (h j)

/-- When `A` has at least two alternatives, surjectivity of `f` forces `V` to be nonempty, so
`nisanSWF` is weakly Pareto without an explicit `[Nonempty V]` assumption. -/
theorem nisanSWF_isPareto_of_nontrivial [Nontrivial A] (hf : f.IsStrategyProof)
    (hs : Function.Surjective f) : (f.nisanSWF hf hs).IsPareto := by
  have : Nonempty V := by
    by_contra hV
    rw [not_nonempty_iff] at hV
    obtain ⟨a, b, hab⟩ := exists_pair_ne A
    obtain ⟨P, rfl⟩ := hs a
    obtain ⟨Q, rfl⟩ := hs b
    exact hab (congrArg f (funext fun i => isEmptyElim i))
  exact f.nisanSWF_isPareto hf hs

/-- **Constant-profile unanimity** ([Nisan2007], Definition 9.2): if all voters hold the same
ranking `r`, then `nisanSWF` outputs `r.toWeakRanking`. -/
theorem nisanSWF_const [Nonempty V] (hf : f.IsStrategyProof) (hs : Function.Surjective f)
    (r : Ranking A) :
    f.nisanSWF hf hs (fun _ => r) = r.toWeakRanking := by
  ext a b
  rw [Ranking.toWeakRanking_atLeast]
  by_cases hab : a = b
  · subst hab
    exact iff_of_true ((f.nisanSWF hf hs _).refl a) (Or.inl rfl)
  · constructor
    · intro h
      refine Or.inr (r.prefers_of_not_prefers (Ne.symm hab) fun hba => ?_)
      have hP := f.nisanSWF_isPareto hf hs (fun _ => r) b a (fun _ => hba)
      exact hP h
    · rintro (rfl | h)
      · exact absurd rfl hab
      · exact (f.nisanSWF hf hs _).atLeast_of_prefers
          (f.nisanSWF_isPareto hf hs (fun _ => r) a b fun _ => h)

/-- **Independence of irrelevant alternatives** for `nisanSWF` ([Nisan2007], Lemma 9.11): the
social comparison of `a` and `b` depends only on the voters' comparisons of `a` and `b`. -/
theorem nisanSWF_isIIA (hf : f.IsStrategyProof) (hs : Function.Surjective f) :
    (f.nisanSWF hf hs).IsIIA := by
  intro P Q a b h
  change f (P.toTopSet {a, b}) = a ↔ f (Q.toTopSet {a, b}) = a
  rw [hf.isMaskinMonotone.apply_toTopSet_congr (Set.mem_insert a _) (hs a)
    (P := P) (Q := Q) fun i x y hx hy => ?_]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact iff_of_false ((P i).irrefl _) ((Q i).irrefl _)
  · exact h i
  · exact Ranking.prefers_iff_swap (h i)
  · exact iff_of_false ((P i).irrefl _) ((Q i).irrefl _)

/-- Strengthening of the dictator step in [Nisan2007], Lemma 9.11: voter `i` is a dictator for
`nisanSWF` if and only if `i` is a dictator for `f` (Lemma 9.11 uses the forward implication to
contrapositively deduce non-dictatorship). -/
theorem nisanSWF_isDictator_iff (hf : f.IsStrategyProof) (hs : Function.Surjective f) {i : V} :
    (f.nisanSWF hf hs).IsDictator i ↔ f.IsDictator i := by
  constructor
  · intro hi P x _ hxP
    refine (P i).prefers_of_not_prefers hxP fun hnx => ?_
    have hsoc := hi P x (f P) hnx
    exact hsoc (hf.isMaskinMonotone.apply_toTopSet_of_mem (Set.mem_insert (f P) {x}))
  · intro hi P a b hab hba
    have hne : a ≠ b := (P i).ne_of_prefers hab
    have hba' : f (P.toTopSet {b, a}) = b := hba
    have htop := hi (P.toTopSet {b, a}) a (hs a) (by rwa [hba'])
    rw [hba'] at htop
    have hab' := ((P i).toTopSet_prefers_iff_of_mem (Set.mem_insert b {a})
      (Set.mem_insert_of_mem b rfl)).1 htop
    exact (P i).asymm hab hab'

/-- Strengthening of the non-dictatorship conclusion of [Nisan2007], Lemma 9.11: `nisanSWF` is
dictatorial if and only if `f` is dictatorial (giving Lemma 9.11's
`¬ f.IsDictatorial → ¬ (f.nisanSWF hf hs).IsDictatorial` as the contrapositive of the forward
direction). -/
theorem nisanSWF_isDictatorial_iff (hf : f.IsStrategyProof) (hs : Function.Surjective f) :
    (f.nisanSWF hf hs).IsDictatorial ↔ f.IsDictatorial :=
  exists_congr fun _ => f.nisanSWF_isDictator_iff hf hs

end NisanSWF

end Cslib.GameTheory.SocialChoice.SocialChoiceFunction
