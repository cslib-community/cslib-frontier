/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.SocialChoice.May
public import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
# Weak-order Arrow's theorem and Fishburn's infinite-electorate ultrafilters

Two complements to `CslibFrontier.GameTheory.SocialChoice.Arrow`:

1. **Individual weak orders** ([Arrow1951]). In Arrow's original formulation, voters' preferences
   are complete preorders (`WeakRanking A`), so individuals as well as society may be indifferent.
   Restricting a weak-profile rule `G : WeakSocialWelfareFunction V A` to strict profiles yields a
   `SocialWelfareFunction V A` to which `SocialWelfareFunction.isDictatorial_of_isPareto_of_isIIA`
   applies; a four-step IIA and weak-Pareto argument through a third alternative lifts that strict
   dictator to all weak profiles (`WeakSocialWelfareFunction.isDictatorial_of_isPareto_of_isIIA`).
   Unlike the strict-profile setting, a rule with dictator `i` need not equal `dictatorship i`:
   when `i` is indifferent between `a` and `b`, a second voter `j` may break the tie
   (`WeakSocialWelfareFunction.serialDictatorship`).

2. **Infinite electorates** ([Fishburn1970]; see also [Fey2004], §3, pp. 7–8, and footnote 13,
   p. 15). Every ultrafilter `U : Ultrafilter V` defines a social welfare function
   `SocialWelfareFunction.ultrafilter U` satisfying weak Pareto and IIA on any set of alternatives.
   Voter `i` is a dictator for `ultrafilter U` if and only if `U = pure i`. On an infinite
   electorate `V`, the nonprincipal ultrafilter `Filter.hyperfilter V` extending the cofinite
   filter therefore yields a weakly Pareto, IIA social welfare function that has no dictator
   (`SocialWelfareFunction.exists_isPareto_and_isIIA_and_not_isDictatorial`), showing that the
   `[Finite V]` hypothesis of Arrow's theorem cannot be omitted.

## Main definitions

* `WeakRanking.toTopSet`: move a set of alternatives strictly to the top of a weak ranking.
* `WeakSocialWelfareFunction.IsPareto`, `WeakSocialWelfareFunction.IsIIA`,
  `WeakSocialWelfareFunction.IsDictator`, `WeakSocialWelfareFunction.IsDictatorial`,
  `WeakSocialWelfareFunction.dictatorship`, `WeakSocialWelfareFunction.serialDictatorship`.
* `SocialWelfareFunction.ultrafilter`: the ultrafilter social welfare function ([Fishburn1970]).

## Main results

* `WeakSocialWelfareFunction.isDictatorial_of_isPareto_of_isIIA`,
  `WeakSocialWelfareFunction.existsUnique_isDictator_of_isPareto_of_isIIA`: **Arrow's impossibility
  theorem** on weak individual rankings ([Arrow1951]).
* `WeakSocialWelfareFunction.serialDictatorship_ne_dictatorship`: on weak profiles with at least
  two voters and two alternatives, lexicographic tie-breaking satisfies weak Pareto, IIA, and
  `IsDictator i` without equalling `dictatorship i`.
* `SocialWelfareFunction.isDictator_ultrafilter_iff`: `i` dictates `ultrafilter U` iff `U = pure i`.
* `SocialWelfareFunction.exists_isPareto_and_isIIA_and_not_isDictatorial`: **Fishburn's
  possibility theorem** ([Fishburn1970]) for infinite electorates.

## References

* [K. J. Arrow, *Social Choice and Individual Values*][Arrow1951]
* [P. C. Fishburn, *Arrow's impossibility theorem: concise proof and infinite voters*][Fishburn1970]
* [M. Fey, *May's theorem with an infinite population*][Fey2004]
-/

public section

namespace Cslib.GameTheory.SocialChoice

variable {V A : Type*}

/-! ### Moving a set of alternatives to the top of a weak ranking -/

namespace WeakRanking

/-- Move the alternatives of `S` strictly above `Sᶜ`, keeping `R`'s weak order within `S` and
within `Sᶜ`. -/
def toTopSet (R : WeakRanking A) (S : Set A) : WeakRanking A where
  AtLeast x y := (x ∈ S ∧ y ∉ S) ∨ ((x ∈ S ↔ y ∈ S) ∧ R.AtLeast x y)
  total x y := by
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · exact (R.total x y).imp (fun h => Or.inr ⟨iff_of_true hx hy, h⟩)
        fun h => Or.inr ⟨iff_of_true hy hx, h⟩
    · exact Or.inl (Or.inl ⟨hx, hy⟩)
    · exact Or.inr (Or.inl ⟨hy, hx⟩)
    · exact (R.total x y).imp (fun h => Or.inr ⟨iff_of_false hx hy, h⟩)
        fun h => Or.inr ⟨iff_of_false hy hx, h⟩
  trans x y z := by
    rintro (⟨hx, hy⟩ | ⟨hxy, h1⟩) (⟨hy', hz⟩ | ⟨hyz, h2⟩)
    · exact absurd hy' hy
    · exact Or.inl ⟨hx, fun hz => hy (hyz.2 hz)⟩
    · exact Or.inl ⟨hxy.2 hy', hz⟩
    · exact Or.inr ⟨hxy.trans hyz, R.trans _ _ _ h1 h2⟩

theorem toTopSet_atLeast_iff_of_mem (R : WeakRanking A) {S : Set A} {x y : A}
    (hx : x ∈ S) (hy : y ∈ S) :
    (R.toTopSet S).AtLeast x y ↔ R.AtLeast x y :=
  ⟨fun h => h.elim (fun h => absurd hy h.2) And.right,
    fun h => Or.inr ⟨iff_of_true hx hy, h⟩⟩

theorem toTopSet_prefers_of_mem_of_notMem (R : WeakRanking A) {S : Set A} {x y : A}
    (hx : x ∈ S) (hy : y ∉ S) :
    (R.toTopSet S).Prefers x y := by
  rintro (⟨hy', -⟩ | ⟨hyx, -⟩)
  · exact hy hy'
  · exact hy (hyx.2 hx)

end WeakRanking

/-! ### Arrow's theorem on weak individual rankings -/

namespace WeakSocialWelfareFunction

variable (G : WeakSocialWelfareFunction V A)

/-- **Weak Pareto** on weak individual profiles ([Arrow1951]): if every voter strictly prefers `a`
to `b`, so does society. -/
@[expose] def IsPareto : Prop :=
  ∀ (P : WeakProfile V A) (a b : A), (∀ i, (P i).Prefers a b) → (G P).Prefers a b

/-- **Independence of irrelevant alternatives** on weak individual profiles ([Arrow1951]):
society's comparison of `a` and `b` depends only on the voters' weak comparisons on `{a, b}`
(both `AtLeast a b` and `AtLeast b a`, distinguishing strict preference from indifference). -/
@[expose] def IsIIA : Prop :=
  ∀ (P Q : WeakProfile V A) (a b : A),
    (∀ i, ((P i).AtLeast a b ↔ (Q i).AtLeast a b) ∧ ((P i).AtLeast b a ↔ (Q i).AtLeast b a)) →
    ((G P).AtLeast a b ↔ (G Q).AtLeast a b)

/-- Voter `i` is a **dictator** for `G`: whenever `i` strictly prefers `a` to `b`, so does
society ([Arrow1951]). -/
@[expose] def IsDictator (i : V) : Prop :=
  ∀ (P : WeakProfile V A) (a b : A), (P i).Prefers a b → (G P).Prefers a b

/-- `G` is **dictatorial** if it has a dictator. -/
@[expose] def IsDictatorial : Prop := ∃ i, G.IsDictator i

/-- The **pure dictatorship** of voter `i`: society adopts `i`'s weak ranking verbatim. -/
@[expose] def dictatorship (i : V) : WeakSocialWelfareFunction V A := fun P => P i

/-- **Serial (lexicographic) dictatorship** of voter `i` followed by voter `j`: society strictly
prefers `a` to `b` when `i` does, and adopts `j`'s comparison when `i` is indifferent. -/
@[expose] def serialDictatorship (i j : V) : WeakSocialWelfareFunction V A := fun P =>
  { AtLeast := fun a b => (P i).Prefers a b ∨ ((P i).AtLeast a b ∧ (P j).AtLeast a b)
    total := fun a b => by
      by_cases hab : (P i).Prefers a b
      · exact Or.inl (Or.inl hab)
      by_cases hba : (P i).Prefers b a
      · exact Or.inr (Or.inl hba)
      have hi_ba : (P i).AtLeast b a := not_not.1 hab
      have hi_ab : (P i).AtLeast a b := not_not.1 hba
      exact ((P j).total a b).imp (fun hj => Or.inr ⟨hi_ab, hj⟩) fun hj => Or.inr ⟨hi_ba, hj⟩
    trans := fun a b c => by
      rintro (h1 | ⟨hi1, hj1⟩) (h2 | ⟨hi2, hj2⟩)
      · exact Or.inl ((P i).prefers_trans h1 h2)
      · exact Or.inl fun hca => h1 ((P i).trans _ _ _ hi2 hca)
      · exact Or.inl fun hca => h2 ((P i).trans _ _ _ hca hi1)
      · exact Or.inr ⟨(P i).trans _ _ _ hi1 hi2, (P j).trans _ _ _ hj1 hj2⟩ }

variable {G}

theorem IsIIA.prefers_iff (hI : G.IsIIA) {P Q : WeakProfile V A} {a b : A}
    (h : ∀ i, ((P i).AtLeast a b ↔ (Q i).AtLeast a b) ∧ ((P i).AtLeast b a ↔ (Q i).AtLeast b a)) :
    (G P).Prefers a b ↔ (G Q).Prefers a b :=
  not_congr (hI P Q b a fun i => ⟨(h i).2, (h i).1⟩)

theorem IsDictator.isPareto {i : V} (hi : G.IsDictator i) : G.IsPareto :=
  fun P a b h => hi P a b (h i)

theorem isDictator_dictatorship (i : V) : (dictatorship (A := A) i).IsDictator i :=
  fun _ _ _ h => h

theorem isPareto_dictatorship (i : V) : (dictatorship (A := A) i).IsPareto :=
  (isDictator_dictatorship i).isPareto

theorem isIIA_dictatorship (i : V) : (dictatorship (A := A) i).IsIIA :=
  fun _ _ _ _ h => (h i).1

theorem isDictator_serialDictatorship (i j : V) :
    (serialDictatorship (A := A) i j).IsDictator i := by
  intro P a b hi hba
  rcases show (P i).Prefers b a ∨ ((P i).AtLeast b a ∧ (P j).AtLeast b a) from hba with
    hba' | ⟨hiba, -⟩
  · exact (P i).prefers_asymm hi hba'
  · exact hi hiba

theorem isPareto_serialDictatorship (i j : V) :
    (serialDictatorship (A := A) i j).IsPareto :=
  (isDictator_serialDictatorship i j).isPareto

theorem isIIA_serialDictatorship (i j : V) :
    (serialDictatorship (A := A) i j).IsIIA := by
  intro P Q a b h
  change ((P i).Prefers a b ∨ ((P i).AtLeast a b ∧ (P j).AtLeast a b)) ↔
    ((Q i).Prefers a b ∨ ((Q i).AtLeast a b ∧ (Q j).AtLeast a b))
  simp only [WeakRanking.Prefers, (h i).1, (h i).2, (h j).1]

/-- Unlike strict-profile dictatorships (`SocialWelfareFunction.isDictator_iff_eq_dictatorship`),
a rule on weak profiles with dictator `i` need not equal `dictatorship i`: when `i ≠ j` and `A`
is nontrivial, `serialDictatorship i j` breaks `i`'s ties using `j`. -/
theorem serialDictatorship_ne_dictatorship [Nontrivial A] {i j : V} (hij : i ≠ j) :
    serialDictatorship (A := A) i j ≠ dictatorship i := by
  classical
  intro heq
  obtain ⟨a, b, hab⟩ := exists_pair_ne A
  obtain ⟨r₀⟩ := Ranking.nonempty A
  let indiff : WeakRanking A := ⟨fun _ _ => True, fun _ _ => .inl trivial, fun _ _ _ _ _ => trivial⟩
  let P : WeakProfile V A := fun k => if k = i then indiff else (r₀.toTop a).toWeakRanking
  have h : (serialDictatorship i j P).AtLeast b a :=
    heq.symm ▸ (by simp [dictatorship, P, indiff] : (dictatorship i P).AtLeast b a)
  simp only [serialDictatorship, P, hij.symm, ite_true, ite_false, indiff,
    WeakRanking.Prefers, not_true_eq_false, true_and, false_or, Ranking.toWeakRanking_atLeast,
    hab.symm] at h
  exact (r₀.toTop a).asymm (r₀.isTop_toTop a b hab.symm) h

/-- Restrict a weak-profile social welfare function to strict profiles. -/
private def toStrict (G : WeakSocialWelfareFunction V A) : SocialWelfareFunction V A :=
  fun P => G (fun i => (P i).toWeakRanking)

private theorem isPareto_toStrict (hP : G.IsPareto) : (toStrict G).IsPareto :=
  fun P a b h => hP _ a b fun i => (P i).toWeakRanking_prefers.2 (h i)

private theorem isIIA_toStrict (hI : G.IsIIA) : (toStrict G).IsIIA :=
  fun _ _ a b h => hI _ _ a b fun i => by
    simp only [Ranking.toWeakRanking_atLeast]
    exact ⟨or_congr_right (h i), or_congr_right (Ranking.prefers_iff_swap (h i))⟩

/-- With at least two alternatives, a weak-profile rule has at most one dictator. -/
theorem IsDictator.unique [Nontrivial A] {i j : V} (hi : G.IsDictator i) (hj : G.IsDictator j) :
    i = j :=
  SocialWelfareFunction.IsDictator.unique (F := toStrict G)
    (fun P a b h => hi _ a b ((P i).toWeakRanking_prefers.2 h))
    (fun P a b h => hj _ a b ((P j).toWeakRanking_prefers.2 h))

/-- **Arrow's impossibility theorem on weak individual rankings** ([Arrow1951]): with finitely many
voters and at least three alternatives, every weakly Pareto social welfare function on weak
profiles satisfying IIA is dictatorial. -/
theorem isDictatorial_of_isPareto_of_isIIA [Finite V] (hP : G.IsPareto) (hI : G.IsIIA)
    (h3 : ∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c) : G.IsDictatorial := by
  classical
  obtain ⟨n, hn⟩ :=
    (toStrict G).isDictatorial_of_isPareto_of_isIIA (isPareto_toStrict hP) (isIIA_toStrict hI) h3
  refine ⟨n, fun P a b hab_n => ?_⟩
  have hab : a ≠ b := fun h => (P n).prefers_irrefl a (h ▸ hab_n)
  -- Pick a third alternative `c` distinct from both `a` and `b`.
  obtain ⟨c, hca, hcb⟩ : ∃ c : A, c ≠ a ∧ c ≠ b := by
    obtain ⟨x, y, z, hxy, hxz, hyz⟩ := h3
    by_cases hx : x ≠ a ∧ x ≠ b
    · exact ⟨x, hx⟩
    by_cases hy : y ≠ a ∧ y ≠ b
    · exact ⟨y, hy⟩
    refine ⟨z, ?_⟩
    rcases not_and_or.1 hx with h1 | h1 <;> rcases not_and_or.1 hy with h2 | h2 <;>
      simp_all [ne_comm]
  obtain ⟨r₀⟩ := Ranking.nonempty A
  -- Voter `n` adopts strict ranking `a ≻ c ≻ b`; others lift `{a, b}` strictly above `{a, b}ᶜ`.
  let sn : Ranking A := ((r₀.toTop b).toTop c).toTop a
  have hsn_ab : sn.Prefers a b := ((r₀.toTop b).toTop c).isTop_toTop a b hab.symm
  have hsn_ac : sn.Prefers a c := ((r₀.toTop b).toTop c).isTop_toTop a c hca
  have hsn_cb : sn.Prefers c b :=
    (((r₀.toTop b).toTop c).toTop_prefers_of_ne hca hab.symm).2
      ((r₀.toTop b).isTop_toTop c b hcb.symm)
  let Q : WeakProfile V A := fun j => if j = n then sn.toWeakRanking else (P j).toTopSet {a, b}
  have haS : a ∈ ({a, b} : Set A) := Set.mem_insert a {b}
  have hbS : b ∈ ({a, b} : Set A) := Set.mem_insert_of_mem a rfl
  have hcS : c ∉ ({a, b} : Set A) := by simp [hca, hcb]
  -- 1. Every voter strictly prefers `a` to `c` in `Q`, so society ranks `a` strictly above `c`.
  have hGQ_ac : (G Q).Prefers a c := hP Q a c fun j => by
    by_cases hj : j = n <;> simp [Q, hj, hsn_ac, (P j).toTopSet_prefers_of_mem_of_notMem haS hcS]
  -- 2. On `{c, b}`, `Q` matches the strict profile where `n` prefers `c ≻ b` and others `b ≻ c`.
  let Qs : Profile V A := fun j => if j = n then sn else r₀.toTop b
  have hGQ_cb : (G Q).Prefers c b := by
    refine (hI.prefers_iff fun j => ?_).2 (hn Qs c b (by simp [Qs, hsn_cb]))
    by_cases hj : j = n
    · simp [Q, Qs, hj]
    · simp only [Q, Qs, hj, ite_false, Ranking.toWeakRanking_atLeast]
      have hbc_Q := (P j).toTopSet_prefers_of_mem_of_notMem hbS hcS
      have hbc_Qs := r₀.isTop_toTop b c hcb
      exact ⟨iff_of_false hbc_Q fun h => h.elim hcb ((r₀.toTop b).asymm hbc_Qs),
        iff_of_true (((P j).toTopSet {a, b}).atLeast_of_prefers hbc_Q) (Or.inr hbc_Qs)⟩
  -- 3. Transitivity gives `(G Q).Prefers a b`, and `Q` agrees with `P` on `{a, b}` for all voters.
  refine (hI.prefers_iff fun j => ?_).2 ((G Q).prefers_trans hGQ_ac hGQ_cb)
  by_cases hj : j = n
  · subst hj
    exact ⟨iff_of_true ((P j).atLeast_of_prefers hab_n) (by simp [Q, hsn_ab]),
      iff_of_false hab_n fun h => by
        simp only [Q, ite_true, Ranking.toWeakRanking_atLeast] at h
        exact h.elim hab.symm (sn.asymm hsn_ab)⟩
  · simp [Q, hj, (P j).toTopSet_atLeast_iff_of_mem haS hbS,
      (P j).toTopSet_atLeast_iff_of_mem hbS haS]

/-- Under the hypotheses of weak-order Arrow's theorem, the dictator is unique. -/
theorem existsUnique_isDictator_of_isPareto_of_isIIA [Finite V] (hP : G.IsPareto)
    (hI : G.IsIIA) (h3 : ∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c) : ∃! i, G.IsDictator i := by
  obtain ⟨a, b, -, hab, -⟩ := id h3
  have : Nontrivial A := ⟨⟨a, b, hab⟩⟩
  obtain ⟨i, hi⟩ := isDictatorial_of_isPareto_of_isIIA hP hI h3
  exact ⟨i, hi, fun j hj => hj.unique hi⟩

end WeakSocialWelfareFunction

/-! ### Fishburn's infinite-electorate ultrafilter social welfare functions -/

namespace SocialWelfareFunction

/-- The **ultrafilter social welfare function** induced by `U : Ultrafilter V` ([Fishburn1970]):
society ranks `a` at least as high as `b` when `a = b` or the coalition of voters preferring `a`
to `b` belongs to `U`. -/
@[expose] def ultrafilter (U : Ultrafilter V) : SocialWelfareFunction V A := fun P =>
  { AtLeast := fun a b => a = b ∨ {i : V | (P i).Prefers a b} ∈ U
    total := fun a b => by
      by_cases hab : a = b
      · exact Or.inl (Or.inl hab)
      have huniv : {i : V | (P i).Prefers a b} ∪ {i : V | (P i).Prefers b a} = Set.univ := by
        ext i
        simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact (P i).total a b hab
      have hmem : {i : V | (P i).Prefers a b} ∪ {i : V | (P i).Prefers b a} ∈ U :=
        huniv.symm ▸ Filter.univ_mem
      exact (Ultrafilter.union_mem_iff.1 hmem).imp Or.inr Or.inr
    trans := fun a b c => by
      rintro (rfl | hab) (rfl | hbc)
      · exact Or.inl rfl
      · exact Or.inr hbc
      · exact Or.inr hab
      · exact Or.inr (Filter.mem_of_superset (Filter.inter_mem hab hbc)
          fun i ⟨h1, h2⟩ => (P i).trans _ _ _ h1 h2) }

@[simp] theorem ultrafilter_prefers (U : Ultrafilter V) (P : Profile V A) {a b : A} :
    (ultrafilter U P).Prefers a b ↔ {i : V | (P i).Prefers a b} ∈ U := by
  refine ⟨fun h => ((ultrafilter U P).atLeast_of_prefers h).resolve_left
    fun heq => h (Or.inl heq.symm), ?_⟩
  rintro h (rfl | hba)
  · exact U.empty_notMem
      ((Set.eq_empty_of_forall_notMem (s := {i | (P i).Prefers b b}) fun i => (P i).irrefl b) ▸ h)
  · obtain ⟨i, hi₁, hi₂⟩ := U.nonempty_of_mem (Filter.inter_mem h hba)
    exact (P i).asymm hi₁ hi₂

theorem isPareto_ultrafilter (U : Ultrafilter V) : (ultrafilter (A := A) U).IsPareto := by
  intro P a b h
  rw [ultrafilter_prefers, (Set.eq_univ_iff_forall (s := {i | (P i).Prefers a b})).2 h]
  exact Filter.univ_mem

theorem isIIA_ultrafilter (U : Ultrafilter V) : (ultrafilter (A := A) U).IsIIA :=
  fun P Q a b h => or_congr_right
    (by rw [(Set.ext h : {i | (P i).Prefers a b} = {i | (Q i).Prefers a b})])

/-- With at least two alternatives, voter `i` is a dictator for `ultrafilter U` if and only if `U`
is the principal ultrafilter `pure i`. -/
theorem isDictator_ultrafilter_iff [Nontrivial A] (U : Ultrafilter V) (i : V) :
    (ultrafilter (A := A) U).IsDictator i ↔ U = pure i := by
  classical
  refine ⟨fun hi => ?_, by rintro rfl P a b h; rwa [ultrafilter_prefers]⟩
  obtain ⟨a, b, hab⟩ := exists_pair_ne A
  obtain ⟨r₀⟩ := Ranking.nonempty A
  let r := r₀.toTop a
  have hr : r.Prefers a b := r₀.isTop_toTop a b hab.symm
  let P : Profile V A := fun j => if j = i then r else r.reverse
  have hsing : {j : V | (P j).Prefers a b} = {i} := by
    ext j
    by_cases hj : j = i <;> simp [P, hj, hr, r.asymm hr]
  obtain ⟨x, hx, hU⟩ := U.eq_pure_of_finite_mem (Set.finite_singleton i)
    (hsing ▸ (ultrafilter_prefers U P).1 (hi P a b (by simp [P, hr])))
  exact Set.mem_singleton_iff.1 hx ▸ hU

/-- On an infinite electorate, the social welfare function defined by `Filter.hyperfilter V`
has no dictator. -/
theorem not_isDictatorial_ultrafilter_hyperfilter [Infinite V] [Nontrivial A] :
    ¬ (ultrafilter (A := A) (Filter.hyperfilter V)).IsDictatorial := by
  rintro ⟨i, hi⟩
  rw [isDictator_ultrafilter_iff] at hi
  exact Filter.notMem_hyperfilter_of_finite (Set.finite_singleton i)
    (hi.symm ▸ Set.mem_singleton i)

/-- **Fishburn's possibility theorem** ([Fishburn1970]): on any infinite electorate `V` and
nontrivial alternative set `A`, there exists a social welfare function satisfying weak Pareto and
independence of irrelevant alternatives that is not dictatorial. -/
theorem exists_isPareto_and_isIIA_and_not_isDictatorial [Infinite V] [Nontrivial A] :
    ∃ F : SocialWelfareFunction V A, F.IsPareto ∧ F.IsIIA ∧ ¬ F.IsDictatorial :=
  ⟨ultrafilter (Filter.hyperfilter V), isPareto_ultrafilter _, isIIA_ultrafilter _,
    not_isDictatorial_ultrafilter_hyperfilter⟩

end SocialWelfareFunction

end Cslib.GameTheory.SocialChoice
