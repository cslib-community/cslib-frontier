/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.SocialChoice.Arrow
public import Mathlib.Data.Set.Card

/-!
# The Gibbard–Satterthwaite theorem

A *social choice function* (`SocialChoiceFunction V A`) picks one alternative from every profile
`V → Ranking A` of strict rankings. It is *strategy-proof* (`IsStrategyProof`) when no voter can
obtain an outcome that they strictly prefer, by their true ranking, by misreporting their ranking
while the other voters keep theirs. The Gibbard–Satterthwaite theorem ([Gibbard1973],
[Satterthwaite1975]) says that with finitely many voters, a strategy-proof social choice function
whose range contains at least three alternatives is dictatorial: some voter always gets their
favourite alternative among those in the range.

The proof is the reduction to Arrow's theorem in [Nisan2007] (§9.2.4: Theorem 9.8, Definition 9.9
and the proof of Lemmas 9.10 and 9.11). *Monotonicity:* if one voter's change of report changes
the outcome, then the voter, by one of the two reports, prefers the other outcome, so the rule is
manipulable ([Nisan2007], Proposition 9.6). Changing reports one voter at a time, a strategy-proof
rule is *Maskin monotone* (`IsMaskinMonotone`): if no voter ranks an alternative above the outcome
that they ranked below it before, the outcome does not change. For finitely many voters the two
properties are equivalent ([MullerSatterthwaite1977]). *The claim:* if every voter moves the
alternatives of a set `S` meeting the range to the top of their ranking, the outcome lies in `S`.
*The social welfare function:* society ranks `a` above `b` when the outcome after every voter moves
`a` and `b` to the top is `a`. By the claim and monotonicity, this is a social welfare function,
weakly Pareto and IIA, so Arrow's theorem
(`SocialWelfareFunction.isDictatorial_of_isPareto_of_isIIA`) gives a dictator, and that voter is a
dictator for the social choice function.

**Scope.** [Nisan2007] (Theorem 9.8) states the theorem for rules onto a set of at least three
alternatives; `isDictatorial_of_isStrategyProof_of_surjective` is that statement. The main theorem
`isDictatorial_of_isStrategyProof` assumes only that the *range* has at least three elements, the
"at least three possible outcomes" form attributed to [Gibbard1973] and [Satterthwaite1975] (not
checked against the original papers). A dictator then gets their favourite alternative of the
range. To run the reduction on the range, rankings of the range are extended to rankings of all
alternatives (`Ranking.extend`). As in `Arrow.lean`, voters' rankings are strict, the electorate
must be finite and the set of alternatives may be infinite. The tests show that the hypothesis of
three alternatives is needed: majority rule on two alternatives is strategy-proof, onto and not
dictatorial.

## Main definitions

* `Profile.toTopSet`: moves a set `S` of alternatives to the top of every voter's ranking.
* `SocialChoiceFunction V A`: functions from profiles to alternatives.
* `SocialChoiceFunction.IsStrategyProof`: no voter gains by misreporting.
* `SocialChoiceFunction.IsMaskinMonotone`: Maskin monotonicity (strong positive association).
* `SocialChoiceFunction.IsDictator`, `SocialChoiceFunction.IsDictatorial`: voter `i` always gets
  their favourite alternative of the range.
* `SocialChoiceFunction.dictatorship`: the rule choosing voter `i`'s top alternative
  (`Ranking.top`).

## Main results

* `SocialChoiceFunction.isStrategyProof_iff_isMaskinMonotone`: for finitely many voters,
  strategy-proofness is Maskin monotonicity.
* `SocialChoiceFunction.isDictatorial_of_isMaskinMonotone`: the Muller–Satterthwaite theorem, for
  a range of at least three alternatives.
* `SocialChoiceFunction.isDictatorial_of_isStrategyProof`: **the Gibbard–Satterthwaite theorem**,
  for a range of at least three alternatives; `isDictatorial_of_isStrategyProof_of_surjective` for
  rules onto at least three alternatives.
* `SocialChoiceFunction.isStrategyProof_and_surjective_iff`: with finitely many alternatives, at
  least three, the strategy-proof onto rules are exactly the dictatorships.
* `SocialChoiceFunction.IsDictator.isStrategyProof`: a rule with a dictator is strategy-proof.

## References

* [A. Gibbard, *Manipulation of voting schemes: a general result*][Gibbard1973]
* [E. Muller, M. A. Satterthwaite, *The equivalence of strong positive association and
  strategy-proofness*][MullerSatterthwaite1977]
* [N. Nisan, *Introduction to mechanism design (for computer scientists)*][Nisan2007]
* [M. A. Satterthwaite, *Strategy-proofness and Arrow's conditions*][Satterthwaite1975]
-/
public section

namespace Cslib.GameTheory.SocialChoice

variable {A : Type*}

/-- A **social choice function** chooses one alternative from every preference profile. -/
abbrev SocialChoiceFunction (V A : Type*) := Profile V A → A

namespace SocialChoiceFunction

variable {V : Type*} (f : SocialChoiceFunction V A)

/-- `f` is **strategy-proof**: it cannot be manipulated. A manipulation is a voter `i`, a profile
`P` of true rankings and a misreport giving the profile `Q` (the other voters' reports unchanged)
such that `i` strictly prefers, by their true ranking `P i`, the outcome `f Q` to `f P`
([Nisan2007], Definition 9.4, *incentive compatible*). -/
@[expose] def IsStrategyProof : Prop :=
  ∀ (P Q : Profile V A) (i : V), (∀ j, j ≠ i → P j = Q j) → ¬ (P i).Prefers (f Q) (f P)

/-- `f` is **Maskin monotone** (*strong positive association* in [MullerSatterthwaite1977]): if
no voter ranks an alternative above the outcome `f P` at `Q` that they ranked below it at `P`, the
outcome at `Q` is still `f P`. -/
@[expose] def IsMaskinMonotone : Prop :=
  ∀ ⦃P Q : Profile V A⦄, (∀ i y, (P i).Prefers (f P) y → (Q i).Prefers (f P) y) → f Q = f P

/-- Voter `i` is a **dictator** for `f`: the outcome is always `i`'s favourite alternative among
those in the range of `f` ([Nisan2007], Definition 9.7, for rules onto `A`). -/
@[expose] def IsDictator (i : V) : Prop :=
  ∀ (P : Profile V A) (x : A), x ∈ Set.range f → x ≠ f P → (P i).Prefers (f P) x

/-- `f` is **dictatorial** if it has a dictator. -/
@[expose] def IsDictatorial : Prop := ∃ i, f.IsDictator i

/-- The **dictatorship** of voter `i`: choose `i`'s top alternative. -/
@[expose] noncomputable def dictatorship [Finite A] [Nonempty A] (i : V) :
    SocialChoiceFunction V A :=
  fun P => (P i).top

variable {f}

/-- Strategy-proofness, phrased with `Function.update`: replacing voter `i`'s report by `r` does
not give `i` a better outcome. -/
theorem isStrategyProof_iff [DecidableEq V] :
    f.IsStrategyProof ↔ ∀ (P : Profile V A) (i : V) (r : Ranking A),
      ¬ (P i).Prefers (f (Function.update P i r)) (f P) := by
  refine ⟨fun h P i r => h P _ i fun j hj => (Function.update_of_ne hj r P).symm,
    fun h P Q i hPQ => ?_⟩
  have hQ : Q = Function.update P i (Q i) := funext fun (j : V) => by
    by_cases hj : j = i
    · subst hj
      exact (Function.update_self j (Q j) P).symm
    · rw [Function.update_of_ne hj, hPQ j hj]
  rw [hQ]
  exact h P i (Q i)

/-- **Monotonicity for one voter** ([Nisan2007], Proposition 9.6): if voter `i` changes their
report and every alternative ranked below `f P` by `i` stays below it, the outcome stays `f P`. -/
private theorem IsStrategyProof.apply_eq_of_single (hf : f.IsStrategyProof) {P Q : Profile V A}
    {i : V} (hPQ : ∀ j, j ≠ i → P j = Q j)
    (h : ∀ y, (P i).Prefers (f P) y → (Q i).Prefers (f P) y) : f Q = f P := by
  by_contra hne
  exact hf Q P i (fun j hj => (hPQ j hj).symm)
    (h _ ((P i).prefers_of_not_prefers hne (hf P Q i hPQ)))

/-- Apply Maskin monotonicity: if every alternative that some voter ranks below `f P` stays
below `f P` for that voter in `Q`, then `f Q = f P`. -/
theorem IsMaskinMonotone.apply_eq (hf : f.IsMaskinMonotone) {P Q : Profile V A}
    (h : ∀ i y, (P i).Prefers (f P) y → (Q i).Prefers (f P) y) : f Q = f P :=
  hf h

/-- **Strategy-proofness implies Maskin monotonicity** ([MullerSatterthwaite1977]; [Nisan2007],
proof of Lemmas 9.10 and 9.11): the reports are changed one voter at a time, and each change keeps
the outcome by single-voter monotonicity. -/
theorem IsStrategyProof.isMaskinMonotone [Finite V] (hf : f.IsStrategyProof) :
    f.IsMaskinMonotone := by
  classical
  intro P Q h
  have := Fintype.ofFinite V
  let R (s : Finset V) : Profile V A := fun j => if j ∈ s then Q j else P j
  have key (s : Finset V) : f (R s) = f P := by
    induction s using Finset.induction_on with
    | empty => exact congrArg f (funext fun _ => by simp [R])
    | insert i s hi ih =>
      refine (hf.apply_eq_of_single (i := i)
        (fun j hj => by simp only [R, Finset.mem_insert, hj, false_or]) fun y hy => ?_).trans ih
      rw [ih] at hy ⊢
      simp only [R, hi, ite_false, Finset.mem_insert, true_or, ite_true] at hy ⊢
      exact h i y hy
  simpa only [show R Finset.univ = Q from funext fun _ => by simp [R]] using key Finset.univ

/-- **Maskin monotonicity implies strategy-proofness** ([MullerSatterthwaite1977]). Suppose
voter `i` gains by reporting `Q i`, so that `i` ranks `f Q` above `f P`. Let `i` instead report
their true ranking with `f Q` and `f P` moved to the top. Monotonicity from `P` keeps the outcome
`f P`, and monotonicity from `Q` keeps it `f Q`. -/
theorem IsMaskinMonotone.isStrategyProof (hf : f.IsMaskinMonotone) : f.IsStrategyProof := by
  classical
  intro P Q i hPQ hman
  let P' : Profile V A := Function.update P i ((P i).toTopSet {f Q, f P})
  have h1 : f P' = f P := hf.apply_eq fun j y hy => by
    rcases eq_or_ne j i with rfl | hj
    · simpa only [P', Function.update_self] using
        ((P j).toTopSet_prefers_of_mem (Set.mem_insert_of_mem _ rfl)).2 (Or.inr hy)
    · simpa only [P', Function.update_of_ne hj] using hy
  have h2 : f P' = f Q := hf.apply_eq fun j y hy => by
    rcases eq_or_ne j i with rfl | hj
    · simp only [P', Function.update_self, (P j).toTopSet_prefers_of_mem (Set.mem_insert _ _),
        Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      rcases eq_or_ne y (f Q) with rfl | hneQ
      · exact absurd hy ((Q j).irrefl _)
      · exact (eq_or_ne y (f P)).elim (fun h => Or.inr (h ▸ hman)) fun hneP => Or.inl ⟨hneQ, hneP⟩
    · simpa only [P', Function.update_of_ne hj, hPQ j hj] using hy
  exact (P i).ne_of_prefers hman (h2.symm.trans h1)

/-- With finitely many voters, strategy-proofness and Maskin monotonicity are equivalent
([MullerSatterthwaite1977]). -/
theorem isStrategyProof_iff_isMaskinMonotone [Finite V] :
    f.IsStrategyProof ↔ f.IsMaskinMonotone :=
  ⟨IsStrategyProof.isMaskinMonotone, IsMaskinMonotone.isStrategyProof⟩

/-- Move the alternatives of `S` to the top of every voter's ranking ([Nisan2007],
Definition 9.9). -/
@[expose] def _root_.Cslib.GameTheory.SocialChoice.Profile.toTopSet {V : Type*}
    (P : Profile V A) (S : Set A) : Profile V A :=
  fun i => (P i).toTopSet S

/-- If `a` is in the range and every voter ranks it at the top, the outcome is `a`. -/
private theorem IsMaskinMonotone.apply_eq_of_isTop (hf : f.IsMaskinMonotone) {a : A}
    (ha : a ∈ Set.range f) {Q : Profile V A} (hQ : ∀ i, (Q i).IsTop a) : f Q = a := by
  obtain ⟨P, rfl⟩ := ha
  exact hf.apply_eq fun i y hy => hQ i y ((P i).ne_of_prefers hy).symm

/-- **Unanimity**: if `a` is in the range and every voter ranks `a` above `b`, the outcome is not
`b`. -/
theorem IsMaskinMonotone.apply_ne (hf : f.IsMaskinMonotone) {a b : A}
    (ha : a ∈ Set.range f) (hab : a ≠ b) {P : Profile V A} (h : ∀ i, (P i).Prefers a b) :
    f P ≠ b := by
  intro hPb
  have hb : b ∈ ({a, b} : Set A) := Set.mem_insert_of_mem a rfl
  -- Moving `a` and `b` to the top leaves the outcome `b`.
  have h1 : f (P.toTopSet {a, b}) = f P := hf.apply_eq fun i y hy => by
    rw [hPb] at hy ⊢
    exact ((P i).toTopSet_prefers_of_mem hb).2 (Or.inr hy)
  -- But everyone now ranks `a` at the top.
  have h2 : f (P.toTopSet {a, b}) = a := hf.apply_eq_of_isTop ha fun i x hx => by
    rcases eq_or_ne x b with rfl | hxb
    · exact ((P i).toTopSet_prefers_iff_of_mem (Set.mem_insert a _) hb).2 (h i)
    · exact (P i).toTopSet_prefers_of_mem_of_notMem (Set.mem_insert a _) (by simp [hx, hxb])
  exact hab (h2.symm.trans (h1.trans hPb))

/-- **The claim** of [Nisan2007] (proof of Lemmas 9.10 and 9.11): if every voter moves the
alternatives of a set `S` meeting the range to the top, the outcome lies in `S`. -/
theorem IsMaskinMonotone.apply_toTopSet_mem (hf : f.IsMaskinMonotone) {S : Set A}
    {a : A} (haS : a ∈ S) (ha : a ∈ Set.range f) (P : Profile V A) : f (P.toTopSet S) ∈ S := by
  by_contra hc
  exact hf.apply_ne (b := f (P.toTopSet S)) ha (fun h => hc (h ▸ haS))
    (fun i => (P i).toTopSet_prefers_of_mem_of_notMem haS hc) rfl

/-- If the outcome after moving `S` to the top lies in `T ⊆ S`, it is also the outcome after
moving `T` to the top. -/
private theorem IsMaskinMonotone.apply_toTopSet_of_subset (hf : f.IsMaskinMonotone)
    {S T : Set A} (hTS : T ⊆ S) (P : Profile V A) (hT : f (P.toTopSet S) ∈ T) :
    f (P.toTopSet T) = f (P.toTopSet S) :=
  hf.apply_eq fun i y hy => by
    have hy' := ((P i).toTopSet_prefers_of_mem (hTS hT)).1 hy
    exact ((P i).toTopSet_prefers_of_mem hT).2
      ((em (y ∈ T)).symm.imp_right fun hyT => hy'.resolve_left fun h => h (hTS hyT))

/-- If the outcome lies in `S`, it does not change when every voter moves `S` to the top. -/
theorem IsMaskinMonotone.apply_toTopSet_of_mem (hf : f.IsMaskinMonotone)
    {S : Set A} {P : Profile V A} (hP : f P ∈ S) : f (P.toTopSet S) = f P :=
  hf.apply_eq fun i _ hy => ((P i).toTopSet_prefers_of_mem hP).2 (Or.inr hy)

/-- **Independence of irrelevant alternatives** for moving a set `S` meeting the range to the
top: the outcome only depends on the voters' rankings within `S`. -/
theorem IsMaskinMonotone.apply_toTopSet_congr (hf : f.IsMaskinMonotone)
    {S : Set A} {a : A} (haS : a ∈ S) (ha : a ∈ Set.range f) {P Q : Profile V A}
    (hPQ : ∀ i x y, x ∈ S → y ∈ S → ((P i).Prefers x y ↔ (Q i).Prefers x y)) :
    f (Q.toTopSet S) = f (P.toTopSet S) := by
  have hm := hf.apply_toTopSet_mem haS ha P
  refine hf.apply_eq fun i y hy => ?_
  have hy' := ((P i).toTopSet_prefers_of_mem hm).1 hy
  exact ((Q i).toTopSet_prefers_of_mem hm).2
    ((em (y ∈ S)).symm.imp_right fun hyS =>
      (hPQ i _ y hm hyS).1 (hy'.resolve_left fun h => h hyS))

/-! ### The social welfare function induced by a strategy-proof rule -/

section Induced

variable (hf : f.IsMaskinMonotone)
include hf

/-- The outcome after every voter moves `a` and `b` to the top is `a` or `b`. -/
theorem IsMaskinMonotone.apply_toTopSet_pair (P : Profile V A) {a b : A}
    (ha : a ∈ Set.range f) : f (P.toTopSet {a, b}) = a ∨ f (P.toTopSet {a, b}) = b := by
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
    hf.apply_toTopSet_mem (Set.mem_insert a {b}) ha P

/-- Transitivity of the induced social ranking ([Nisan2007], proof of Lemma 9.10). -/
theorem IsMaskinMonotone.apply_toTopSet_pair_trans (P : Profile V A) {a b c : A}
    (ha : a ∈ Set.range f) (hab : f (P.toTopSet {a, b}) = a)
    (hbc : f (P.toTopSet {b, c}) = b) : f (P.toTopSet {a, c}) = a := by
  rcases eq_or_ne a b with rfl | h₁
  · exact hbc
  rcases eq_or_ne b c with rfl | h₂
  · exact hab
  rcases eq_or_ne a c with rfl | _
  · simpa only [Set.pair_eq_singleton, Set.mem_singleton_iff] using
      hf.apply_toTopSet_mem (Set.mem_insert a {a}) ha P
  have hsub {x y : A} (hx : x ∈ ({a, b, c} : Set A)) (hy : y ∈ ({a, b, c} : Set A)) :
      ({x, y} : Set A) ⊆ {a, b, c} := Set.insert_subset hx (Set.singleton_subset_iff.2 hy)
  have ha' : a ∈ ({a, b, c} : Set A) := by simp
  have hb' : b ∈ ({a, b, c} : Set A) := by simp
  have hc' : c ∈ ({a, b, c} : Set A) := by simp
  rcases (by simpa using hf.apply_toTopSet_mem ha' ha P :
      f (P.toTopSet {a, b, c}) = a ∨ f (P.toTopSet {a, b, c}) = b ∨
        f (P.toTopSet {a, b, c}) = c) with hx | hx | hx
  · rw [hf.apply_toTopSet_of_subset (hsub ha' hc') P (by simp [hx]), hx]
  · -- The outcome on `{a, b, c}` is `b`, so it is also the outcome on `{a, b}`.
    exact absurd (hab.symm.trans
      ((hf.apply_toTopSet_of_subset (hsub ha' hb') P (by simp [hx])).trans hx)) h₁
  · exact absurd (hbc.symm.trans
      ((hf.apply_toTopSet_of_subset (hsub hb' hc') P (by simp [hx])).trans hx)) h₂

/-- Every voter extends their ranking of the range of `f` to `A` with `Ranking.extend r₀`. -/
private def extendProfile (r₀ : Ranking A) (P : Profile V (Set.range f)) : Profile V A :=
  fun i => r₀.extend (P i)

/-- The social welfare function on the range of `f` induced by a strategy-proof rule
([Nisan2007], Definition 9.9): extend every voter's ranking of the range to `A` and rank `a` at
least as high as `b` when the outcome after every voter moves `a` and `b` to the top is `a`. -/
private noncomputable def induced (r₀ : Ranking A) : SocialWelfareFunction V (Set.range f) :=
  fun P =>
  { AtLeast := fun a b => f ((extendProfile r₀ P).toTopSet {(a : A), (b : A)}) = a
    total := fun a b => by
      rcases hf.apply_toTopSet_pair (extendProfile r₀ P) (b := (b : A)) a.2 with h | h
      · exact Or.inl h
      · right
        rw [Set.pair_comm]
        exact h
    trans := fun a _ _ hab hbc => hf.apply_toTopSet_pair_trans _ a.2 hab hbc }

/-- The induced social welfare function is weakly Pareto ([Nisan2007], proof of Lemma 9.11). -/
private theorem isPareto_induced [Nonempty V] (r₀ : Ranking A) : (induced hf r₀).IsPareto := by
  intro P a b h hba
  obtain ⟨i⟩ := ‹Nonempty V›
  have hab : (a : A) ≠ b := fun he => (P i).ne_of_prefers (h i) (Subtype.ext he)
  refine hf.apply_ne a.2 hab (P := (extendProfile r₀ P).toTopSet {(b : A), (a : A)})
    (fun j => ?_) hba
  exact ((r₀.extend (P j)).toTopSet_prefers_iff_of_mem (Set.mem_insert_of_mem _ rfl)
    (Set.mem_insert _ _)).2 ((r₀.extend_prefers_of_mem (P j) a.2 b.2).2 (h j))

/-- The induced social welfare function satisfies independence of irrelevant alternatives
([Nisan2007], proof of Lemma 9.11). -/
private theorem isIIA_induced (r₀ : Ranking A) : (induced hf r₀).IsIIA := by
  intro P Q a b h
  change f ((extendProfile r₀ P).toTopSet {(a : A), (b : A)}) = a ↔
    f ((extendProfile r₀ Q).toTopSet {(a : A), (b : A)}) = a
  rw [hf.apply_toTopSet_congr (Set.mem_insert (a : A) _) a.2 (P := extendProfile r₀ P)
    (Q := extendProfile r₀ Q) fun i x y hx hy => ?_]
  have hab : (r₀.extend (P i)).Prefers a b ↔ (r₀.extend (Q i)).Prefers a b := by
    rw [r₀.extend_prefers_of_mem _ a.2 b.2, r₀.extend_prefers_of_mem _ a.2 b.2]
    exact h i
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact iff_of_false ((r₀.extend (P i)).irrefl _) ((r₀.extend (Q i)).irrefl _)
  · exact hab
  · exact Ranking.prefers_iff_swap hab
  · exact iff_of_false ((r₀.extend (P i)).irrefl _) ((r₀.extend (Q i)).irrefl _)

end Induced

/-- **The Muller–Satterthwaite theorem** ([MullerSatterthwaite1977]; proof of [Nisan2007],
Theorem 9.8): with finitely many voters, a Maskin monotone social choice function whose range has
at least three alternatives is dictatorial. -/
theorem isDictatorial_of_isMaskinMonotone [Finite V] (hf : f.IsMaskinMonotone)
    (h3 : 3 ≤ (Set.range f).encard) : f.IsDictatorial := by
  obtain ⟨r₀⟩ := Ranking.nonempty A
  obtain ⟨t, ht, ht3⟩ := Set.exists_subset_encard_eq h3
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Set.encard_eq_three.1 ht3
  have ha : a ∈ Set.range f := ht (by simp)
  have hb : b ∈ Set.range f := ht (by simp)
  have hc : c ∈ Set.range f := ht (by simp)
  have : Nonempty V := by
    by_contra! hV
    obtain ⟨P, rfl⟩ := ha
    obtain ⟨Q, rfl⟩ := hb
    exact hab (congrArg f (Subsingleton.elim P Q))
  obtain ⟨n, hn⟩ := (induced hf r₀).isDictatorial_of_isPareto_of_isIIA (isPareto_induced hf r₀)
    (isIIA_induced hf r₀) ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, fun h => hab (congrArg Subtype.val h),
      fun h => hac (congrArg Subtype.val h), fun h => hbc (congrArg Subtype.val h)⟩
  -- Society, which follows `n`, ranks `x` above `f P` on the restriction of `P` to the range.
  refine ⟨n, fun P x hx hxP => (P n).prefers_of_not_prefers hxP fun hnx =>
    hn (fun i => (P i).restrict (Set.range f)) ⟨x, hx⟩ ⟨f P, ⟨P, rfl⟩⟩
      ((P n).restrict_prefers.2 hnx) ?_⟩
  change f ((extendProfile r₀ _).toTopSet {f P, x}) = f P
  rw [hf.apply_toTopSet_congr (Set.mem_insert (f P) _) ⟨P, rfl⟩ (P := P) fun i y z hy hz => ?_]
  · exact hf.apply_toTopSet_of_mem (Set.mem_insert _ _)
  · have hS : ({f P, x} : Set A) ⊆ Set.range f :=
      Set.insert_subset ⟨P, rfl⟩ (Set.singleton_subset_iff.2 hx)
    exact ((r₀.extend_prefers_of_mem _ (hS hy) (hS hz)).trans (P i).restrict_prefers).symm

/-- **The Gibbard–Satterthwaite theorem** ([Gibbard1973], [Satterthwaite1975]; [Nisan2007],
Theorem 9.8): with finitely many voters, a strategy-proof social choice function whose range has
at least three alternatives is dictatorial. -/
theorem isDictatorial_of_isStrategyProof [Finite V] (hf : f.IsStrategyProof)
    (h3 : 3 ≤ (Set.range f).encard) : f.IsDictatorial :=
  isDictatorial_of_isMaskinMonotone hf.isMaskinMonotone h3

/-- For a rule onto `A`, voter `i` is a dictator exactly when the outcome is always `i`'s top
alternative. -/
theorem isDictator_iff_of_surjective (hs : Function.Surjective f) {i : V} :
    f.IsDictator i ↔ ∀ P : Profile V A, (P i).IsTop (f P) :=
  ⟨fun h P x hx => h P x (hs x) hx, fun h P x _ hx => h P x hx⟩

/-- **The Gibbard–Satterthwaite theorem** for rules onto `A` ([Nisan2007], Theorem 9.8): with
finitely many voters and at least three alternatives, a strategy-proof social choice function onto
`A` is dictatorial. -/
theorem isDictatorial_of_isStrategyProof_of_surjective [Finite V] (hf : f.IsStrategyProof)
    (hs : Function.Surjective f) (h3 : ∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    f.IsDictatorial := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ := h3
  refine isDictatorial_of_isStrategyProof hf ?_
  rw [hs.range_eq, ← Set.encard_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩]
  exact Set.encard_le_encard (Set.subset_univ _)

/-! ### Dictatorships -/

@[simp] theorem dictatorship_apply [Finite A] [Nonempty A] (i : V) (P : Profile V A) :
    dictatorship i P = (P i).top := rfl

/-- A dictatorship is onto. -/
theorem surjective_dictatorship [Finite A] [Nonempty A] (i : V) :
    Function.Surjective (dictatorship (V := V) (A := A) i) := fun a =>
  let ⟨r⟩ := Ranking.nonempty A
  ⟨fun _ => r.toTop a, ((r.toTop a).isTop_iff_eq_top.1 (r.isTop_toTop a)).symm⟩

theorem isDictator_dictatorship [Finite A] [Nonempty A] (i : V) :
    (dictatorship (V := V) (A := A) i).IsDictator i :=
  fun P x _ hx => (P i).isTop_top x hx

/-- A rule with a dictator is strategy-proof. -/
theorem IsDictator.isStrategyProof {i : V} (hi : f.IsDictator i) : f.IsStrategyProof := by
  intro P Q j hPQ h
  have hne : f Q ≠ f P := (P j).ne_of_prefers h
  rcases eq_or_ne j i with rfl | hj
  · exact (P j).asymm h (hi P (f Q) ⟨Q, rfl⟩ hne)
  · exact (P i).asymm (hi P (f Q) ⟨Q, rfl⟩ hne) (hPQ i hj.symm ▸ hi Q (f P) ⟨P, rfl⟩ hne.symm)

/-- A dictatorship is strategy-proof. -/
theorem isStrategyProof_dictatorship [Finite A] [Nonempty A] (i : V) :
    (dictatorship (V := V) (A := A) i).IsStrategyProof :=
  (isDictator_dictatorship i).isStrategyProof

/-- For a rule onto `A`, voter `i` is a dictator exactly when the rule is the dictatorship of
`i`. -/
theorem isDictator_iff_eq_dictatorship [Finite A] [Nonempty A] (hs : Function.Surjective f)
    {i : V} : f.IsDictator i ↔ f = dictatorship (A := A) i := by
  rw [isDictator_iff_of_surjective hs]
  exact ⟨fun h => funext fun P => (P i).isTop_iff_eq_top.1 (h P),
    by rintro rfl P; exact (P i).isTop_top⟩

/-- With finitely many voters and finitely many alternatives, at least three, the strategy-proof
social choice functions onto `A` are exactly the dictatorships. -/
theorem isStrategyProof_and_surjective_iff [Finite V] [Finite A] [Nonempty A]
    (h3 : ∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    f.IsStrategyProof ∧ Function.Surjective f ↔ ∃ i, f = dictatorship (A := A) i := by
  refine ⟨fun ⟨hf, hs⟩ => ?_, fun ⟨i, h⟩ => h ▸ ⟨isStrategyProof_dictatorship i,
    surjective_dictatorship i⟩⟩
  obtain ⟨i, hi⟩ := isDictatorial_of_isStrategyProof_of_surjective hf hs h3
  exact ⟨i, (isDictator_iff_eq_dictatorship hs).1 hi⟩

end SocialChoiceFunction

end Cslib.GameTheory.SocialChoice
