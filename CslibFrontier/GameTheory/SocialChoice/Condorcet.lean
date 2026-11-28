/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.SocialChoice.GibbardSatterthwaite
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin

/-!
# Condorcet winners, Condorcet's paradox, plurality and the Borda count

Pairwise majority comparisons and positional voting rules on strict preference profiles
([Nisan2007], §9.2.1–9.2.2). Given a finite electorate `V`, `support P a b` counts the voters who
rank `a` above `b`, and `MajorityPrefers P a b` holds when strictly more voters prefer `a` to `b`
than `b` to `a`. An alternative that beats every other alternative in pairwise majority is a
*Condorcet winner* (`IsCondorcetWinner`).

With at least three voters and three alternatives, pairwise majority can cycle
(*Condorcet's paradox*, [Nisan2007], §9.2.1, p. 211), leaving no Condorcet winner. Positional
methods such as *plurality* (`SocialChoiceFunction.plurality`) and the *Borda count*
(`SocialWelfareFunction.borda`) aggregate every profile, at a cost ([Nisan2007], §9.2.2,
pp. 211–212): plurality can fail to select a Condorcet winner when one exists and encourages
strategic voting, while the Borda count is weakly Pareto yet violates independence of irrelevant
alternatives.

## Main definitions

* `support P a b`: the number of voters ranking `a` above `b`.
* `MajorityPrefers P a b`: strictly more voters rank `a` above `b` than `b` above `a`.
* `IsCondorcetWinner P a`: `a` beats every other alternative under `MajorityPrefers`.
* `SocialChoiceFunction.IsCondorcetConsistent`: selects every Condorcet winner.
* `pluralityCount P a`, `SocialChoiceFunction.plurality`: first-place vote counts and deterministic
  tie-broken plurality rule ([Nisan2007], §9.2.2).
* `bordaScore P a`, `SocialWelfareFunction.borda`: Borda scores and the Borda social welfare
  function ([Nisan2007], §9.2.2).

## Main results

* `IsCondorcetWinner.unique`: a profile has at most one Condorcet winner.
* `exists_condorcetCycle`, `exists_profile_forall_not_isCondorcetWinner`: **Condorcet's paradox**
  ([Nisan2007], §9.2.1, p. 211): cyclic pairwise majority (`3 ≤ |V|`, `|V| ≠ 4`) and profiles with
  no Condorcet winner (`3 ≤ |V|`).
* `SocialChoiceFunction.not_isStrategyProof_plurality`: with at least two voters and three
  alternatives, tie-broken plurality is strategically manipulable ([Nisan2007], §9.2.2,
  pp. 211–212).
* `SocialChoiceFunction.not_isCondorcetConsistent_plurality`: with `3 ≤ |V|`, `|V| ≠ 4`, and at
  least three alternatives, tie-broken plurality is not Condorcet consistent.
* `SocialWelfareFunction.isPareto_borda`, `SocialWelfareFunction.not_isIIA_borda`: the Borda count
  satisfies weak Pareto for a nonempty electorate yet violates IIA for `2 ≤ |V|` and `3 ≤ |A|`.

## References

* [N. Nisan, *Introduction to mechanism design (for computer scientists)*][Nisan2007]
-/

public section

namespace Cslib.GameTheory.SocialChoice

variable {V A : Type*}

section Pairwise

variable [Fintype V]

open Classical in
/-- The number of voters in `P` who rank `a` strictly above `b`. -/
@[expose] noncomputable def support (P : Profile V A) (a b : A) : ℕ :=
  (Finset.univ.filter fun i => (P i).Prefers a b).card

@[simp] theorem support_self (P : Profile V A) (a : A) : support P a a = 0 := by
  classical
  exact Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun i _ => (P i).irrefl a)

/-- For distinct alternatives `a` and `b`, every voter ranks either `a` above `b` or `b` above
`a`. -/
theorem support_add_support (P : Profile V A) {a b : A} (hab : a ≠ b) :
    support P a b + support P b a = Fintype.card V := by
  classical
  have hfilter : (Finset.univ.filter fun i => (P i).Prefers b a) =
      Finset.univ.filter fun i => ¬ (P i).Prefers a b :=
    Finset.filter_congr fun i _ => ((P i).not_prefers_iff hab).symm
  rw [support, support, hfilter, Finset.card_filter_add_card_filter_not, Finset.card_univ]

theorem support_eq_card_of_forall {P : Profile V A} {a b : A}
    (h : ∀ i, (P i).Prefers a b) : support P a b = Fintype.card V := by
  classical
  simp [support, Finset.filter_true_of_mem fun i _ => h i]

theorem support_eq_zero_of_forall {P : Profile V A} {a b : A}
    (h : ∀ i, (P i).Prefers a b) : support P b a = 0 := by
  classical
  exact Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun i _ => (P i).asymm (h i))

/-- Strictly more voters rank `a` above `b` than `b` above `a`. -/
@[expose] def MajorityPrefers (P : Profile V A) (a b : A) : Prop :=
  support P b a < support P a b

theorem MajorityPrefers.asymm {P : Profile V A} {a b : A} (h : MajorityPrefers P a b) :
    ¬ MajorityPrefers P b a :=
  Nat.lt_asymm h

theorem MajorityPrefers.ne {P : Profile V A} {a b : A} (h : MajorityPrefers P a b) : a ≠ b :=
  fun h' => Nat.lt_irrefl _ (h' ▸ h)

theorem majorityPrefers_iff_card_lt_two_mul {P : Profile V A} {a b : A} (hab : a ≠ b) :
    MajorityPrefers P a b ↔ Fintype.card V < 2 * support P a b := by
  have := support_add_support P hab
  simp only [MajorityPrefers]; omega

theorem majorityPrefers_of_forall [Nonempty V] {P : Profile V A} {a b : A}
    (h : ∀ i, (P i).Prefers a b) : MajorityPrefers P a b := by
  simpa [MajorityPrefers, support_eq_zero_of_forall h, support_eq_card_of_forall h] using
    Fintype.card_pos

/-- Alternative `a` is a **Condorcet winner** of `P` if a strict majority of voters prefers `a` to
every other alternative. -/
@[expose] def IsCondorcetWinner (P : Profile V A) (a : A) : Prop :=
  ∀ b, b ≠ a → MajorityPrefers P a b

/-- A preference profile has at most one Condorcet winner. -/
theorem IsCondorcetWinner.unique {P : Profile V A} {a b : A}
    (ha : IsCondorcetWinner P a) (hb : IsCondorcetWinner P b) : a = b :=
  Classical.byContradiction fun hab => (ha b (Ne.symm hab)).asymm (hb a hab)

theorem isCondorcetWinner_of_forall_isTop [Nonempty V] {P : Profile V A} {a : A}
    (h : ∀ i, (P i).IsTop a) : IsCondorcetWinner P a :=
  fun b hba => majorityPrefers_of_forall fun i => h i b hba

/-- A social choice function is **Condorcet consistent** if it chooses the Condorcet winner
whenever one exists. -/
@[expose] def SocialChoiceFunction.IsCondorcetConsistent (f : SocialChoiceFunction V A) : Prop :=
  ∀ (P : Profile V A) (a : A), IsCondorcetWinner P a → f P = a

/-! ### Three-block profile constructions and Condorcet's paradox -/

/-- Move `x`, `y`, `z` to the top three positions of `r` in the order `x ≻ y ≻ z`. -/
private def tripleTop (r : Ranking A) (x y z : A) : Ranking A :=
  ((r.toTop z).toTop y).toTop x

private theorem tripleTop_isTop (r : Ranking A) (x y z : A) :
    (tripleTop r x y z).IsTop x :=
  ((r.toTop z).toTop y).isTop_toTop x

private theorem tripleTop_prefers_second_third (r : Ranking A) {x y z : A}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (tripleTop r x y z).Prefers y z :=
  (((r.toTop z).toTop y).toTop_prefers_of_ne hxy.symm hxz.symm).2
    ((r.toTop z).isTop_toTop y z hyz.symm)

private theorem card_filter_fin_lt (e : V ≃ Fin (Fintype.card V)) {m : ℕ}
    (hm : m ≤ Fintype.card V) :
    (Finset.univ.filter fun i : V => (e i : ℕ) < m).card = m := by
  classical
  refine (Finset.card_bij (fun i hi => (⟨e i, (Finset.mem_filter.1 hi).2⟩ : Fin m))
    (fun _ _ => Finset.mem_univ _)
    (fun _ _ _ _ h => e.injective (Fin.ext (Fin.mk.inj h)))
    fun b _ => ⟨e.symm ⟨b.val, b.isLt.trans_le hm⟩, by simp [b.isLt],
      Fin.ext (by simp)⟩).trans (Finset.card_fin m)

private def threeBlockProfile (e : V ≃ Fin (Fintype.card V)) (c₀ c₁ : ℕ)
    (r₀ r₁ r₂ : Ranking A) : Profile V A :=
  fun i => if (e i : ℕ) < c₀ then r₀ else if (e i : ℕ) < c₀ + c₁ then r₁ else r₂

private theorem card_filter_threeBlock (e : V ≃ Fin (Fintype.card V)) {c₀ c₁ : ℕ}
    (hc : c₀ + c₁ ≤ Fintype.card V) (r₀ r₁ r₂ : Ranking A) (p : Ranking A → Prop)
    [DecidablePred p] :
    (Finset.univ.filter fun i => p (threeBlockProfile e c₀ c₁ r₀ r₁ r₂ i)).card =
      (if p r₀ then c₀ else 0) + (if p r₁ then c₁ else 0) +
        (if p r₂ then Fintype.card V - (c₀ + c₁) else 0) := by
  classical
  let s₀ : Finset V := Finset.univ.filter fun i => (e i : ℕ) < c₀
  let s₀₁ : Finset V := Finset.univ.filter fun i => (e i : ℕ) < c₀ + c₁
  have hsub₀ : s₀ ⊆ s₀₁ := fun i hi => by
    simp only [s₀, s₀₁, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; omega
  have hs₀ : s₀.card = c₀ := card_filter_fin_lt e (by omega)
  have hs₀₁ : s₀₁.card = c₀ + c₁ := card_filter_fin_lt e hc
  have hcongr : ∀ {t : Finset V} {r : Ranking A},
      (∀ i ∈ t, threeBlockProfile e c₀ c₁ r₀ r₁ r₂ i = r) →
      (t.filter fun i => p (threeBlockProfile e c₀ c₁ r₀ r₁ r₂ i)).card =
        if p r then t.card else 0 := fun {t r} ht => by
    rw [Finset.filter_congr fun i hi => by rw [ht i hi], Finset.filter_const]
    split_ifs <;> simp
  have hsplit {a b : Finset V} (h : a ⊆ b) :
      (b.filter fun i => p (threeBlockProfile e c₀ c₁ r₀ r₁ r₂ i)).card =
        (a.filter fun i => p (threeBlockProfile e c₀ c₁ r₀ r₁ r₂ i)).card +
          ((b \ a).filter fun i => p (threeBlockProfile e c₀ c₁ r₀ r₁ r₂ i)).card := by
    rw [← Finset.card_union_of_disjoint
      (disjoint_sdiff_self_right.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
      ← Finset.filter_union, Finset.union_sdiff_of_subset h]
  rw [hsplit (Finset.subset_univ s₀₁), hsplit hsub₀,
    hcongr (r := r₀) fun i hi => ite_eq_left (Finset.mem_filter.1 hi).2,
    hcongr (r := r₁) fun i hi => by
      simp only [s₀, s₀₁, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp [threeBlockProfile, hi.1, hi.2],
    hcongr (r := r₂) fun i hi => by
      simp only [s₀₁, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and] at hi
      have hnot0 : ¬(e i : ℕ) < c₀ := by omega
      simp [threeBlockProfile, hi, hnot0],
    Finset.card_sdiff_of_subset hsub₀, Finset.card_sdiff_of_subset (Finset.subset_univ s₀₁),
    Finset.card_univ, hs₀, hs₀₁, add_tsub_cancel_left]

/-- Common three-block cyclic construction on distinct `a, b, c`: `a` beats `b`, `b` beats `c`,
`c` receives at least `(Fintype.card V + 1) / 3 + (Fintype.card V / 3)` votes against `a`, and
every voter ranks `a` above all alternatives outside `{a, b, c}`. -/
private theorem exists_cyclicThreeBlock (hV : 3 ≤ Fintype.card V)
    {a b c : A} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ P : Profile V A, MajorityPrefers P a b ∧ MajorityPrefers P b c ∧
      support P a c = (Fintype.card V + 2) / 3 ∧
      ∀ x, x ≠ a → x ≠ b → x ≠ c → ∀ i, (P i).Prefers a x := by
  classical
  obtain ⟨r⟩ := Ranking.nonempty A
  let e := Fintype.equivFin V
  let n := Fintype.card V
  let c₀ := (n + 2) / 3
  let c₁ := (n + 1) / 3
  have hc : c₀ + c₁ ≤ n := by omega
  let r₀ := tripleTop r a b c
  let r₁ := tripleTop r b c a
  let r₂ := tripleTop r c a b
  refine ⟨threeBlockProfile e c₀ c₁ r₀ r₁ r₂, ?_, ?_, ?_, fun x hxa hxb hxc i => ?_⟩
  · rw [majorityPrefers_iff_card_lt_two_mul hab, support,
      card_filter_threeBlock e hc r₀ r₁ r₂ (fun s => s.Prefers a b)]
    simp only [r₀, r₁, r₂, tripleTop_isTop r a b c b hab.symm,
      (tripleTop r b c a).asymm (tripleTop_isTop r b c a a hab),
      tripleTop_prefers_second_third r hac.symm hbc.symm hab, ↓reduceIte, n, c₀, c₁]
    omega
  · rw [majorityPrefers_iff_card_lt_two_mul hbc, support,
      card_filter_threeBlock e hc r₀ r₁ r₂ (fun s => s.Prefers b c)]
    simp only [r₀, r₁, r₂, tripleTop_prefers_second_third r hab hac hbc,
      tripleTop_isTop r b c a c hbc.symm,
      (tripleTop r c a b).asymm (tripleTop_isTop r c a b b hbc), ↓reduceIte, n, c₀, c₁]
    omega
  · rw [support, card_filter_threeBlock e hc r₀ r₁ r₂ (fun s => s.Prefers a c)]
    simp only [r₀, r₁, r₂, tripleTop_isTop r a b c c hac.symm,
      (tripleTop r b c a).asymm (tripleTop_prefers_second_third r hbc hab.symm hac.symm),
      (tripleTop r c a b).asymm (tripleTop_isTop r c a b a hac), ↓reduceIte, n, c₀]
    omega
  · unfold threeBlockProfile
    split_ifs
    · exact tripleTop_isTop r a b c x hxa
    · exact (((r.toTop a).toTop c).toTop_prefers_of_ne hab hxb).2
        (((r.toTop a).toTop_prefers_of_ne hac hxc).2 (r.isTop_toTop a x hxa))
    · exact ((r.toTop b).toTop a).toTop_prefers_of_ne hac hxc |>.2
        ((r.toTop b).isTop_toTop a x hxa)

/-- **Condorcet's paradox** ([Nisan2007], §9.2.1, p. 211): for any finite electorate with
`3 ≤ |V|` and `|V| ≠ 4`, and any three distinct alternatives `a`, `b`, `c`, there is a profile in
which a strict majority prefers `a` to `b`, `b` to `c`, and `c` to `a`. -/
theorem exists_condorcetCycle (hV : 3 ≤ Fintype.card V) (hV4 : Fintype.card V ≠ 4)
    {a b c : A} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ P : Profile V A,
      MajorityPrefers P a b ∧ MajorityPrefers P b c ∧ MajorityPrefers P c a := by
  obtain ⟨P, hab', hbc', hsupp, -⟩ := exists_cyclicThreeBlock hV hab hac hbc
  have := support_add_support P hac
  exact ⟨P, hab', hbc', (majorityPrefers_iff_card_lt_two_mul hac.symm).2 (by omega)⟩

/-- With at least three voters and at least three alternatives, there is a preference profile that
has no Condorcet winner (including `|V| = 4`, where two alternatives tie and every alternative
fails to beat all others by a strict majority). -/
theorem exists_profile_forall_not_isCondorcetWinner (hV : 3 ≤ Fintype.card V)
    (h3 : ∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    ∃ P : Profile V A, ∀ x, ¬ IsCondorcetWinner P x := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ := h3
  obtain ⟨P, hab', hbc', hsupp, hother⟩ := exists_cyclicThreeBlock hV hab hac hbc
  have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  refine ⟨P, fun x hx => ?_⟩
  rcases eq_or_ne x a with rfl | hxa
  · have h_ac : support P c x < support P x c := hx c hac.symm
    have := support_add_support P hac
    omega
  rcases eq_or_ne x b with rfl | hxb
  · exact hab'.asymm (hx a hab)
  rcases eq_or_ne x c with rfl | hxc
  · exact hbc'.asymm (hx b hbc)
  exact (majorityPrefers_of_forall (hother x hxa hxb hxc)).asymm (hx a (Ne.symm hxa))

/-! ### Plurality rule -/

open Classical in
/-- The **plurality count** of `a` in `P`: the number of voters ranking `a` strictly first
([Nisan2007], §9.2.2, p. 211). -/
@[expose] noncomputable def pluralityCount (P : Profile V A) (a : A) : ℕ :=
  (Finset.univ.filter fun i => (P i).IsTop a).card

theorem pluralityCount_eq_card_of_forall_isTop {P : Profile V A} {a : A}
    (h : ∀ i, (P i).IsTop a) : pluralityCount P a = Fintype.card V := by
  classical
  simp [pluralityCount, Finset.filter_true_of_mem fun i _ => h i]

theorem pluralityCount_eq_zero_of_forall_isTop {P : Profile V A} {a b : A} (hab : b ≠ a)
    (h : ∀ i, (P i).IsTop a) : pluralityCount P b = 0 := by
  classical
  exact Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun _ _ hi => hab (hi.unique (h _)))

/-- Each voter ranks a unique alternative at the top, so the plurality counts sum to `|V|`. -/
theorem sum_pluralityCount [Fintype A] [Nonempty A] (P : Profile V A) :
    ∑ a, pluralityCount P a = Fintype.card V := by
  classical
  have hcongr (a : A) :
      pluralityCount P a = (Finset.univ.filter fun i : V => (P i).top = a).card :=
    congrArg Finset.card
      (Finset.filter_congr fun i _ => by simp [(P i).isTop_iff_eq_top, eq_comm])
  rw [Finset.sum_congr rfl fun a _ => hcongr a]
  exact (Finset.card_eq_sum_card_fiberwise (f := fun i : V => (P i).top)
    (s := Finset.univ) (t := Finset.univ) fun _ _ => Finset.mem_univ _).symm.trans
    Finset.card_univ

/-- Rank alternatives by descending plurality count, breaking ties according to `t`. -/
noncomputable def pluralityRanking (P : Profile V A) (t : Ranking A) : Ranking A where
  Prefers a b :=
    pluralityCount P b < pluralityCount P a ∨
      (pluralityCount P a = pluralityCount P b ∧ t.Prefers a b)
  irrefl a := by
    rintro (h | ⟨-, h⟩)
    · exact Nat.lt_irrefl _ h
    · exact t.irrefl a h
  trans a b c := by
    rintro (h1 | ⟨heq1, h1⟩) (h2 | ⟨heq2, h2⟩)
    · exact Or.inl (h2.trans h1)
    · exact Or.inl (heq2 ▸ h1)
    · exact Or.inl (heq1.symm ▸ h2)
    · exact Or.inr ⟨heq1.trans heq2, t.trans _ _ _ h1 h2⟩
  total a b hab := by
    rcases lt_trichotomy (pluralityCount P a) (pluralityCount P b) with h | h | h
    · exact Or.inr (Or.inl h)
    · exact (t.total a b hab).imp (fun ht => Or.inr ⟨h, ht⟩) (fun ht => Or.inr ⟨h.symm, ht⟩)
    · exact Or.inl (Or.inl h)

@[simp] theorem pluralityRanking_prefers (P : Profile V A) (t : Ranking A) {a b : A} :
    (pluralityRanking P t).Prefers a b ↔
      pluralityCount P b < pluralityCount P a ∨
        (pluralityCount P a = pluralityCount P b ∧ t.Prefers a b) :=
  Iff.rfl

/-- Deterministic **plurality rule** with tie-breaking ranking `t` ([Nisan2007], §9.2.2, p. 211):
choose the alternative maximizing `pluralityCount P`, breaking ties by `t`. -/
@[expose] noncomputable def SocialChoiceFunction.plurality [Finite A] [Nonempty A]
    (t : Ranking A) : SocialChoiceFunction V A :=
  fun P => (pluralityRanking P t).top

namespace SocialChoiceFunction

theorem plurality_eq_of_isTop [Finite A] [Nonempty A] (t : Ranking A) {P : Profile V A} {a : A}
    (ha : (pluralityRanking P t).IsTop a) : plurality t P = a :=
  ((pluralityRanking P t).isTop_iff_eq_top.1 ha).symm

/-- For a nonempty electorate, plurality rule is onto `A`. -/
theorem surjective_plurality [Nonempty V] [Finite A] [Nonempty A] (t : Ranking A) :
    Function.Surjective (plurality (V := V) t) := fun a =>
  ⟨fun _ => t.toTop a, plurality_eq_of_isTop t fun x hxa => Or.inl <| by
    rw [pluralityCount_eq_card_of_forall_isTop fun _ => t.isTop_toTop a,
      pluralityCount_eq_zero_of_forall_isTop hxa fun _ => t.isTop_toTop a]
    exact Fintype.card_pos⟩

/-- With at least two voters and two alternatives, plurality has no dictator. -/
theorem not_isDictator_plurality [Finite A] [Nontrivial A] (t : Ranking A)
    (hV : 2 ≤ Fintype.card V) (i : V) :
    ¬ (plurality (V := V) t).IsDictator i := fun hi => by
  classical
  have : Nonempty V := ⟨i⟩
  let m := t.top
  obtain ⟨a, ham⟩ := exists_ne m
  let P : Profile V A := fun j => if j = i then t.toTop a else t.toTop m
  have hcnt_a : pluralityCount P a = 1 := Finset.card_eq_one.2 ⟨i, Finset.ext fun j => by
    rcases eq_or_ne j i with rfl | hj
    · simp [P, t.isTop_toTop a]
    · simpa [P, hj] using fun h => ham (h.unique (t.isTop_toTop m))⟩
  have hcnt_m : pluralityCount P m = Fintype.card V - 1 := by
    have hset : (Finset.univ.filter fun j : V => (P j).IsTop m) = Finset.univ.erase i :=
      Finset.ext fun j => by
        rcases eq_or_ne j i with rfl | hj
        · simpa [P] using fun h => ham ((t.isTop_toTop a).unique h)
        · simp [P, hj, t.isTop_toTop m]
    rw [pluralityCount, hset, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
  have hPm : plurality t P = m := plurality_eq_of_isTop t fun x hxm => by
    rw [pluralityRanking_prefers, hcnt_m]
    rcases eq_or_ne x a with rfl | hxa
    · rw [hcnt_a]
      exact (lt_or_eq_of_le (by omega)).imp_right fun h => ⟨h.symm, t.isTop_top x hxm⟩
    · have hcnt0 : pluralityCount P x = 0 :=
        Finset.card_eq_zero.2 <| Finset.filter_eq_empty_iff.2 fun j _ hjx => by
          by_cases hj : j = i <;> simp only [P, hj, ↓reduceIte] at hjx
          · exact hxa (hjx.unique (t.isTop_toTop a))
          · exact hxm (hjx.unique (t.isTop_toTop m))
      exact .inl (hcnt0 ▸ by omega)
  have hdict := (isDictator_iff_of_surjective (surjective_plurality t)).1 hi P a (hPm ▸ ham)
  simp only [P, ↓reduceIte, hPm] at hdict
  exact (t.toTop a).asymm (t.isTop_toTop a m ham.symm) hdict

/-- **Plurality rule is manipulable** ([Nisan2007], §9.2.2, pp. 211–212): with at least two voters
and at least three alternatives, deterministic tie-broken plurality is not strategy-proof. -/
theorem not_isStrategyProof_plurality [Finite A] [Nonempty A] (hV : 2 ≤ Fintype.card V)
    (h3 : ∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c) (t : Ranking A) :
    ¬ (plurality (V := V) t).IsStrategyProof := fun hsp => by
  obtain ⟨a, b, -, hab, -⟩ := id h3
  have : Nontrivial A := ⟨⟨a, b, hab⟩⟩
  have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨i, hi⟩ := isDictatorial_of_isStrategyProof_of_surjective hsp (surjective_plurality t) h3
  exact not_isDictator_plurality t hV i hi

/-- With `3 ≤ |V|`, `|V| ≠ 4`, and at least three alternatives, tie-broken plurality is not
Condorcet consistent: a candidate `w` can beat every rival in pairwise majority while receiving at
most as many first-place votes as `t.top`. (At `|V| = 4` and `|A| = 3` a Condorcet winner must
receive at least two first-place votes while each rival receives at most one, so plurality is
Condorcet consistent there.) -/
theorem not_isCondorcetConsistent_plurality [Finite A] [Nonempty A] (hV : 3 ≤ Fintype.card V)
    (hV4 : Fintype.card V ≠ 4) (h3 : ∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c) (t : Ranking A) :
    ¬ (plurality (V := V) t).IsCondorcetConsistent := by
  classical
  obtain ⟨a₀, b₀, c₀, hab₀, hac₀, hbc₀⟩ := h3
  have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  let m := t.top
  -- Pick two distinct alternatives `w, y` distinct from `m`.
  obtain ⟨w, y, hwm, hym, hwy⟩ : ∃ w y : A, w ≠ m ∧ y ≠ m ∧ w ≠ y :=
    if ha : a₀ = m then ⟨b₀, c₀, ha ▸ hab₀.symm, ha ▸ hac₀.symm, hbc₀⟩
    else if hb : b₀ = m then ⟨a₀, c₀, hb ▸ hab₀, hb ▸ hbc₀.symm, hac₀⟩
    else ⟨a₀, b₀, ha, hb, hab₀⟩
  let e := Fintype.equivFin V
  let n := Fintype.card V
  let k := (n - 1) / 2
  have hk : k + k ≤ n := by omega
  let r₀ := tripleTop t m w y
  let r₁ := tripleTop t y w m
  let r₂ := tripleTop t w m y
  let P := threeBlockProfile e k k r₀ r₁ r₂
  have hcw : IsCondorcetWinner P w := fun x hxw => by
    by_cases hxm : x = m
    · rw [hxm, majorityPrefers_iff_card_lt_two_mul hwm, support,
        card_filter_threeBlock e hk r₀ r₁ r₂ (fun s => s.Prefers w m)]
      simp only [r₀, r₁, r₂, (tripleTop t m w y).asymm (tripleTop_isTop t m w y w hwm),
        tripleTop_prefers_second_third t hwy.symm hym hwm,
        tripleTop_isTop t w m y m hwm.symm, ↓reduceIte, n, k]
      omega
    by_cases hxy : x = y
    · rw [hxy, majorityPrefers_iff_card_lt_two_mul hwy, support,
        card_filter_threeBlock e hk r₀ r₁ r₂ (fun s => s.Prefers w y)]
      simp only [r₀, r₁, r₂, tripleTop_prefers_second_third t hwm.symm hym.symm hwy,
        (tripleTop t y w m).asymm (tripleTop_isTop t y w m w hwy),
        tripleTop_isTop t w m y y hwy.symm, ↓reduceIte, n, k]
      omega
    -- Every voter ranks `w` above any `x ∉ {m, w, y}`.
    refine majorityPrefers_of_forall fun i => ?_
    unfold P threeBlockProfile
    split_ifs
    · exact ((t.toTop y).toTop w).toTop_prefers_of_ne hwm hxm |>.2 ((t.toTop y).isTop_toTop w x hxw)
    · exact ((t.toTop m).toTop w).toTop_prefers_of_ne hwy hxy |>.2 ((t.toTop m).isTop_toTop w x hxw)
    · exact tripleTop_isTop t w m y x hxw
  have hcnt : ∀ z : A, pluralityCount P z =
      (if z = m then k else 0) + (if z = y then k else 0) +
        (if z = w then n - (k + k) else 0) := fun z => by
    rw [pluralityCount, card_filter_threeBlock e hk r₀ r₁ r₂ (fun s => s.IsTop z)]
    have hiff : ∀ {s : Ranking A} (u : A), s.IsTop u → (s.IsTop z ↔ z = u) :=
      fun _ hu => ⟨fun h => h.unique hu, fun h => h ▸ hu⟩
    rw [hiff m (tripleTop_isTop t m w y), hiff y (tripleTop_isTop t y w m),
      hiff w (tripleTop_isTop t w m y)]
  have htop_m : (pluralityRanking P t).IsTop m := fun x hxm => by
    rw [pluralityRanking_prefers, hcnt m, hcnt x]
    simp only [↓reduceIte, hym.symm, hwm.symm, add_zero]
    rcases eq_or_ne x y with rfl | hxy
    · simpa [hym, hwy.symm] using t.isTop_top x hym
    rcases eq_or_ne x w with rfl | hxw
    · simpa [hwm, hwy] using
        (lt_or_eq_of_le (by omega)).imp_right fun h => ⟨h.symm, t.isTop_top x hwm⟩
    · simp [hxm, hxy, hxw]; omega
  exact fun hcc => hwm ((hcc P w hcw).symm.trans (plurality_eq_of_isTop t htop_m))

end SocialChoiceFunction

end Pairwise

/-! ### The Borda count -/

section Borda

variable [Fintype V] [Fintype A]

open Classical in
/-- The **Borda score** of `a` in `P`: the total number of `(voter, rival)` pairs in which the
voter ranks `a` strictly above the rival ([Nisan2007], §9.2.2, p. 211). -/
@[expose] noncomputable def bordaScore (P : Profile V A) (a : A) : ℕ :=
  ∑ i, (Finset.univ.filter fun x => (P i).Prefers a x).card

/-- The **Borda social welfare function**: alternatives are ranked by descending Borda score, with
ties allowed ([Nisan2007], §9.2.2, p. 211). -/
@[expose] noncomputable def SocialWelfareFunction.borda : SocialWelfareFunction V A := fun P =>
  { AtLeast := fun a b => bordaScore P b ≤ bordaScore P a
    total := fun _ _ => le_total _ _
    trans := fun _ _ _ hab hbc => hbc.trans hab }

namespace SocialWelfareFunction

@[simp] theorem borda_atLeast {P : Profile V A} {a b : A} :
    (borda P).AtLeast a b ↔ bordaScore P b ≤ bordaScore P a := Iff.rfl

theorem borda_prefers {P : Profile V A} {a b : A} :
    (borda P).Prefers a b ↔ bordaScore P b < bordaScore P a := not_le

/-- For a nonempty electorate, the Borda count satisfies weak Pareto: if every voter ranks `a`
above `b`, each voter ranks `a` above strictly more alternatives than `b`. -/
theorem isPareto_borda [Nonempty V] : (borda (V := V) (A := A)).IsPareto := fun P a b h => by
  classical
  refine borda_prefers.2 (Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ =>
    Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun x hx => ?_).2
      ⟨b, by simp [h i],
        by simp [(P i).irrefl b]⟩))
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (P i).trans _ _ _ (h i) (Finset.mem_filter.1 hx).2⟩

/-- With at least two voters and two alternatives, the Borda count has no dictator: if voter `i`
ranks `a` first and `b` last while all other voters reverse that ranking, `b`'s Borda score is at
least `a`'s. -/
theorem not_isDictator_borda [Nontrivial A] (hV : 2 ≤ Fintype.card V) (i : V) :
    ¬ (borda (V := V) (A := A)).IsDictator i := fun hi => by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne A
  obtain ⟨r₀⟩ := Ranking.nonempty A
  let r := (r₀.toBottom b).toTop a
  have htop_a : r.IsTop a := (r₀.toBottom b).isTop_toTop a
  have hbot_b : r.IsBottom b := fun x hxb => by
    by_cases hxa : x = a
    · exact hxa ▸ htop_a b hab.symm
    · exact ((r₀.toBottom b).toTop_prefers_of_ne hxa hab.symm).2 (r₀.isBottom_toBottom b x hxb)
  let P : Profile V A := fun j => if j = i then r else r.reverse
  have hcard_top : ∀ {s : Ranking A} {z : A}, s.IsTop z →
      (Finset.univ.filter fun x => s.Prefers z x).card = Fintype.card A - 1 := fun {s z} hz => by
    have hset : (Finset.univ.filter fun x => s.Prefers z x) = Finset.univ.erase z :=
      Finset.ext fun x => by simp [Iff.intro (fun h => (s.ne_of_prefers h).symm) (hz x)]
    rw [hset, Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ]
  have hcard_bot : ∀ {s : Ranking A} {z : A}, s.IsBottom z →
      (Finset.univ.filter fun x => s.Prefers z x).card = 0 := fun {s z} hz =>
    Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun x _ hzx =>
      s.asymm hzx (hz x (s.ne_of_prefers hzx).symm))
  have hscore_a : bordaScore P a = Fintype.card A - 1 :=
    (Finset.sum_eq_single i
      (fun j _ hj => by
        simpa [P, hj] using hcard_bot fun x hxa => r.reverse_prefers.2 (htop_a x hxa))
      fun hi' => absurd (Finset.mem_univ i) hi').trans (by simpa [P] using hcard_top htop_a)
  have hscore_b : bordaScore P b = (Fintype.card V - 1) * (Fintype.card A - 1) := by
    have hcongr (j : V) : (Finset.univ.filter fun x => (P j).Prefers b x).card =
        if j ≠ i then Fintype.card A - 1 else 0 := by
      rcases eq_or_ne j i with rfl | hj
      · simpa [P] using hcard_bot hbot_b
      · simpa [P, hj] using hcard_top fun x hxb => r.reverse_prefers.2 (hbot_b x hxb)
    simp [bordaScore, hcongr, Finset.sum_ite, Finset.filter_ne']
  have hdict : (borda P).Prefers a b := hi P a b (by simp [P, htop_a b hab.symm])
  rw [borda_prefers, hscore_a, hscore_b] at hdict
  have := Nat.mul_le_mul_right (Fintype.card A - 1) (Nat.le_sub_of_add_le (a := 1) (b := 1) hV)
  omega

/-- With at least two voters and at least three alternatives, the Borda count violates IIA. -/
theorem not_isIIA_borda (hV : 2 ≤ Fintype.card V) (hA : 3 ≤ Fintype.card A) :
    ¬ (borda (V := V) (A := A)).IsIIA := fun hI => by
  have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  have : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨i, hi⟩ := isDictatorial_of_three_le_card isPareto_borda hI hA
  exact not_isDictator_borda hV i hi

end SocialWelfareFunction

end Borda

end Cslib.GameTheory.SocialChoice
