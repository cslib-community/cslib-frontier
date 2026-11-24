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
  unfold support
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun i _ => (P i).irrefl a

/-- For distinct alternatives `a` and `b`, every voter ranks either `a` above `b` or `b` above
`a`. -/
theorem support_add_support (P : Profile V A) {a b : A} (hab : a ≠ b) :
    support P a b + support P b a = Fintype.card V := by
  classical
  unfold support
  have hfilter : (Finset.univ.filter fun i => (P i).Prefers b a) =
      Finset.univ.filter fun i => ¬ (P i).Prefers a b := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ((P i).not_prefers_iff hab).symm
  rw [hfilter, Finset.card_filter_add_card_filter_not, Finset.card_univ]

theorem support_eq_card_of_forall {P : Profile V A} {a b : A}
    (h : ∀ i, (P i).Prefers a b) : support P a b = Fintype.card V := by
  classical
  unfold support
  rw [Finset.filter_true_of_mem fun i _ => h i, Finset.card_univ]

theorem support_eq_zero_of_forall {P : Profile V A} {a b : A}
    (h : ∀ i, (P i).Prefers a b) : support P b a = 0 := by
  classical
  unfold support
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun i _ => (P i).asymm (h i)

/-- Strictly more voters rank `a` above `b` than `b` above `a`. -/
@[expose] def MajorityPrefers (P : Profile V A) (a b : A) : Prop :=
  support P b a < support P a b

theorem MajorityPrefers.asymm {P : Profile V A} {a b : A} (h : MajorityPrefers P a b) :
    ¬ MajorityPrefers P b a :=
  Nat.lt_asymm h

theorem MajorityPrefers.ne {P : Profile V A} {a b : A} (h : MajorityPrefers P a b) : a ≠ b := by
  rintro rfl
  exact Nat.lt_irrefl _ h

theorem majorityPrefers_iff_card_lt_two_mul {P : Profile V A} {a b : A} (hab : a ≠ b) :
    MajorityPrefers P a b ↔ Fintype.card V < 2 * support P a b := by
  have hsum := support_add_support P hab
  unfold MajorityPrefers
  omega

theorem majorityPrefers_of_forall [Nonempty V] {P : Profile V A} {a b : A}
    (h : ∀ i, (P i).Prefers a b) : MajorityPrefers P a b := by
  unfold MajorityPrefers
  rw [support_eq_card_of_forall h, support_eq_zero_of_forall h]
  exact Fintype.card_pos

/-- Alternative `a` is a **Condorcet winner** of `P` if a strict majority of voters prefers `a` to
every other alternative. -/
@[expose] def IsCondorcetWinner (P : Profile V A) (a : A) : Prop :=
  ∀ b, b ≠ a → MajorityPrefers P a b

/-- A preference profile has at most one Condorcet winner. -/
theorem IsCondorcetWinner.unique {P : Profile V A} {a b : A}
    (ha : IsCondorcetWinner P a) (hb : IsCondorcetWinner P b) : a = b := by
  by_contra hab
  exact (ha b (Ne.symm hab)).asymm (hb a hab)

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
    (tripleTop r x y z).Prefers y z := by
  unfold tripleTop
  rw [((r.toTop z).toTop y).toTop_prefers_of_ne hxy.symm hxz.symm]
  exact (r.toTop z).isTop_toTop y z hyz.symm

private theorem card_filter_fin_lt (e : V ≃ Fin (Fintype.card V)) {m : ℕ}
    (hm : m ≤ Fintype.card V) :
    (Finset.univ.filter fun i : V => (e i : ℕ) < m).card = m := by
  classical
  let emb : Fin m ↪ V :=
    ⟨fun k => e.symm ⟨k.1, k.2.trans_le hm⟩, fun k₁ k₂ h =>
      Fin.ext (Fin.mk.inj (e.symm.injective h))⟩
  have hset : (Finset.univ.filter fun i : V => (e i : ℕ) < m) = Finset.univ.map emb := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro hi
      exact ⟨⟨(e i : ℕ), hi⟩, e.symm_apply_apply i⟩
    · rintro ⟨k, rfl⟩
      change (e (e.symm ⟨k.1, k.2.trans_le hm⟩) : ℕ) < m
      rw [e.apply_symm_apply]
      exact k.2
  rw [hset, Finset.card_map, Finset.card_univ, Fintype.card_fin]

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
  let s₁ : Finset V := s₀₁ \ s₀
  let s₂ : Finset V := Finset.univ \ s₀₁
  have hsub₀ : s₀ ⊆ s₀₁ := fun i hi => by
    simp only [s₀, s₀₁, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    omega
  have hs₀ : s₀.card = c₀ := card_filter_fin_lt e (by omega)
  have hs₀₁ : s₀₁.card = c₀ + c₁ := card_filter_fin_lt e hc
  have hs₁ : s₁.card = c₁ := by
    rw [Finset.card_sdiff_of_subset hsub₀, hs₀₁, hs₀]
    omega
  have hs₂ : s₂.card = Fintype.card V - (c₀ + c₁) := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ s₀₁), Finset.card_univ, hs₀₁]
  have huniv : Finset.univ = (s₀ ∪ s₁) ∪ s₂ := by
    rw [Finset.union_sdiff_of_subset hsub₀, Finset.union_sdiff_of_subset (Finset.subset_univ s₀₁)]
  have hd₀₁ : Disjoint s₀ s₁ := disjoint_sdiff_self_right
  have hd₁₂ : Disjoint (s₀ ∪ s₁) s₂ := by
    rw [Finset.union_sdiff_of_subset hsub₀]
    exact disjoint_sdiff_self_right
  have hcongr : ∀ {t : Finset V} {r : Ranking A},
      (∀ i ∈ t, threeBlockProfile e c₀ c₁ r₀ r₁ r₂ i = r) →
      (t.filter fun i => p (threeBlockProfile e c₀ c₁ r₀ r₁ r₂ i)).card =
        if p r then t.card else 0 := by
    intro t r ht
    have htf : (t.filter fun i => p (threeBlockProfile e c₀ c₁ r₀ r₁ r₂ i)) =
        t.filter fun _ => p r :=
      Finset.filter_congr fun i hi => by rw [ht i hi]
    rw [htf, Finset.filter_const]
    split_ifs <;> simp only [Finset.card_empty]
  have hd₁₂' : Disjoint ((s₀.filter fun i => p (threeBlockProfile e c₀ c₁ r₀ r₁ r₂ i)) ∪
      (s₁.filter fun i => p (threeBlockProfile e c₀ c₁ r₀ r₁ r₂ i)))
      (s₂.filter fun i => p (threeBlockProfile e c₀ c₁ r₀ r₁ r₂ i)) := by
    rw [← Finset.filter_union]
    exact hd₁₂.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  rw [huniv, Finset.filter_union, Finset.filter_union, Finset.card_union_of_disjoint hd₁₂',
    Finset.card_union_of_disjoint (hd₀₁.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
    hcongr (r := r₀), hcongr (r := r₁), hcongr (r := r₂), hs₀, hs₁, hs₂]
  · intro i hi
    simp only [s₂, s₀₁, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and] at hi
    have h0 : ¬ (e i : ℕ) < c₀ := by omega
    simp only [threeBlockProfile, h0, hi, ite_false]
  · intro i hi
    simp only [s₁, s₀₁, s₀, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [threeBlockProfile, hi.2, hi.1, ite_false, ite_true]
  · intro i hi
    simp only [s₀, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [threeBlockProfile, hi, ite_true]

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
  let P := threeBlockProfile e c₀ c₁ r₀ r₁ r₂
  have hr₀ab : r₀.Prefers a b := tripleTop_isTop r a b c b hab.symm
  have hr₀bc : r₀.Prefers b c := tripleTop_prefers_second_third r hab hac hbc
  have hr₀ac : r₀.Prefers a c := tripleTop_isTop r a b c c hac.symm
  have hr₁bc : r₁.Prefers b c := tripleTop_isTop r b c a c hbc.symm
  have hr₁ca : r₁.Prefers c a := tripleTop_prefers_second_third r hbc hab.symm hac.symm
  have hr₁ba : r₁.Prefers b a := tripleTop_isTop r b c a a hab
  have hr₂ca : r₂.Prefers c a := tripleTop_isTop r c a b a hac
  have hr₂ab : r₂.Prefers a b := tripleTop_prefers_second_third r hac.symm hbc.symm hab
  have hr₂cb : r₂.Prefers c b := tripleTop_isTop r c a b b hbc
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · rw [majorityPrefers_iff_card_lt_two_mul hab]
    have hsupp : support P a b = c₀ + (n - (c₀ + c₁)) := by
      unfold support P
      rw [card_filter_threeBlock e hc r₀ r₁ r₂ (fun s => s.Prefers a b)]
      simp only [hr₀ab, r₁.asymm hr₁ba, hr₂ab, ite_true, ite_false]
      omega
    rw [hsupp]
    omega
  · rw [majorityPrefers_iff_card_lt_two_mul hbc]
    have hsupp : support P b c = c₀ + c₁ := by
      unfold support P
      rw [card_filter_threeBlock e hc r₀ r₁ r₂ (fun s => s.Prefers b c)]
      simp only [hr₀bc, hr₁bc, r₂.asymm hr₂cb, ite_true, ite_false]
      omega
    rw [hsupp]
    omega
  · unfold support P
    rw [card_filter_threeBlock e hc r₀ r₁ r₂ (fun s => s.Prefers a c)]
    simp only [hr₀ac, r₁.asymm hr₁ca, r₂.asymm hr₂ca, ite_true, ite_false]
    omega
  · intro x hxa hxb hxc i
    unfold P threeBlockProfile
    split_ifs
    · exact tripleTop_isTop r a b c x hxa
    · unfold r₁ tripleTop
      rw [((r.toTop a).toTop c).toTop_prefers_of_ne hab hxb,
        (r.toTop a).toTop_prefers_of_ne hac hxc]
      exact r.isTop_toTop a x hxa
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
  refine ⟨P, hab', hbc', ?_⟩
  have hsum := support_add_support P hac
  unfold MajorityPrefers
  omega

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
  by_cases hxa : x = a
  · subst hxa
    have h_ac := hx c hac.symm
    have hsum := support_add_support P hac
    unfold MajorityPrefers at h_ac
    omega
  by_cases hxb : x = b
  · subst hxb
    exact hab'.asymm (hx a hab)
  by_cases hxc : x = c
  · subst hxc
    exact hbc'.asymm (hx b hbc)
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
  unfold pluralityCount
  rw [Finset.filter_true_of_mem fun i _ => h i, Finset.card_univ]

theorem pluralityCount_eq_zero_of_forall_isTop {P : Profile V A} {a b : A} (hab : b ≠ a)
    (h : ∀ i, (P i).IsTop a) : pluralityCount P b = 0 := by
  classical
  unfold pluralityCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun i _ hi => hab (hi.unique (h i))

/-- Each voter ranks a unique alternative at the top, so the plurality counts sum to `|V|`. -/
theorem sum_pluralityCount [Fintype A] [Nonempty A] (P : Profile V A) :
    ∑ a, pluralityCount P a = Fintype.card V := by
  classical
  have hcongr : (∑ a : A, pluralityCount P a) =
      ∑ a : A, (Finset.univ.filter fun i : V => (P i).top = a).card := by
    refine Finset.sum_congr rfl fun a _ => ?_
    unfold pluralityCount
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, (P i).isTop_iff_eq_top, eq_comm]
  rw [hcongr]
  exact (Finset.card_eq_sum_card_fiberwise (f := fun i : V => (P i).top)
    (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)).symm.trans
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
    Function.Surjective (plurality (V := V) t) := by
  intro a
  refine ⟨fun _ => t.toTop a, plurality_eq_of_isTop t fun x hxa => Or.inl ?_⟩
  rw [pluralityCount_eq_card_of_forall_isTop fun _ => t.isTop_toTop a,
    pluralityCount_eq_zero_of_forall_isTop hxa fun _ => t.isTop_toTop a]
  exact Fintype.card_pos

/-- With at least two voters and two alternatives, plurality has no dictator. -/
theorem not_isDictator_plurality [Finite A] [Nontrivial A] (t : Ranking A)
    (hV : 2 ≤ Fintype.card V) (i : V) :
    ¬ (plurality (V := V) t).IsDictator i := by
  classical
  have : Nonempty V := ⟨i⟩
  intro hi
  let m := t.top
  obtain ⟨a, ham⟩ := exists_ne m
  let P : Profile V A := fun j => if j = i then t.toTop a else t.toTop m
  have hcnt_a : pluralityCount P a = 1 := by
    unfold pluralityCount
    rw [Finset.card_eq_one]
    refine ⟨i, Finset.ext fun j => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    by_cases hj : j = i
    · simp only [P, hj, ite_true, iff_true]
      exact t.isTop_toTop a
    · simp only [P, hj, ite_false, iff_false]
      exact fun h => ham (h.unique (t.isTop_toTop m))
  have hcnt_m : pluralityCount P m = Fintype.card V - 1 := by
    have hset : (Finset.univ.filter fun j : V => (P j).IsTop m) = Finset.univ.erase i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq, and_true]
      by_cases hj : j = i
      · refine iff_of_false ?_ (not_not.2 hj)
        simp only [P, hj, ite_true]
        exact fun h => ham ((t.isTop_toTop a).unique h)
      · refine iff_of_true ?_ hj
        simp only [P, hj, ite_false]
        exact t.isTop_toTop m
    unfold pluralityCount
    rw [hset, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
  have hcnt_other : ∀ x, x ≠ a → x ≠ m → pluralityCount P x = 0 := by
    intro x hxa hxm
    unfold pluralityCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j _ hjx
    by_cases hj : j = i
    · simp only [P, hj, ite_true] at hjx
      exact hxa (hjx.unique (t.isTop_toTop a))
    · simp only [P, hj, ite_false] at hjx
      exact hxm (hjx.unique (t.isTop_toTop m))
  have htop_m : (pluralityRanking P t).IsTop m := by
    intro x hxm
    change pluralityCount P x < pluralityCount P m ∨
      (pluralityCount P m = pluralityCount P x ∧ t.Prefers m x)
    by_cases hxa : x = a
    · subst hxa
      rw [hcnt_a, hcnt_m]
      by_cases hgt : 1 < Fintype.card V - 1
      · exact Or.inl hgt
      · exact Or.inr ⟨by omega, t.isTop_top x hxm⟩
    · rw [hcnt_other x hxa hxm, hcnt_m]
      exact Or.inl (by omega)
  have hPm : plurality t P = m := plurality_eq_of_isTop t htop_m
  have hdict := (isDictator_iff_of_surjective (surjective_plurality t)).1 hi P a (hPm ▸ ham)
  rw [hPm] at hdict
  have hPi : P i = t.toTop a := by simp only [P, ite_true]
  rw [hPi] at hdict
  exact (t.toTop a).asymm (t.isTop_toTop a m ham.symm) hdict

/-- **Plurality rule is manipulable** ([Nisan2007], §9.2.2, pp. 211–212): with at least two voters
and at least three alternatives, deterministic tie-broken plurality is not strategy-proof. -/
theorem not_isStrategyProof_plurality [Finite A] [Nonempty A] (hV : 2 ≤ Fintype.card V)
    (h3 : ∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c) (t : Ranking A) :
    ¬ (plurality (V := V) t).IsStrategyProof := by
  obtain ⟨a, b, -, hab, -⟩ := id h3
  have : Nontrivial A := ⟨⟨a, b, hab⟩⟩
  have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  intro hsp
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
  obtain ⟨w, y, hwm, hym, hwy⟩ : ∃ w y : A, w ≠ m ∧ y ≠ m ∧ w ≠ y := by
    by_cases ha : a₀ = m
    · subst ha
      exact ⟨b₀, c₀, hab₀.symm, hac₀.symm, hbc₀⟩
    · by_cases hb : b₀ = m
      · subst hb
        exact ⟨a₀, c₀, hab₀, hbc₀.symm, hac₀⟩
      · exact ⟨a₀, b₀, ha, hb, hab₀⟩
  let e := Fintype.equivFin V
  let n := Fintype.card V
  let k := (n - 1) / 2
  have hk : k + k ≤ n := by omega
  let r₀ := tripleTop t m w y
  let r₁ := tripleTop t y w m
  let r₂ := tripleTop t w m y
  let P := threeBlockProfile e k k r₀ r₁ r₂
  have hcw : IsCondorcetWinner P w := by
    intro x hxw
    by_cases hxm : x = m
    · rw [hxm, majorityPrefers_iff_card_lt_two_mul hwm]
      have hsupp : support P w m = k + (n - (k + k)) := by
        unfold support P
        rw [card_filter_threeBlock e hk r₀ r₁ r₂ (fun s => s.Prefers w m)]
        have h0 : ¬ r₀.Prefers w m :=
          r₀.asymm (tripleTop_isTop t m w y w hwm)
        have h1 : r₁.Prefers w m :=
          tripleTop_prefers_second_third t hwy.symm hym hwm
        have h2 : r₂.Prefers w m := tripleTop_isTop t w m y m hwm.symm
        simp only [h0, h1, h2, ite_true, ite_false]
        omega
      rw [hsupp]
      omega
    by_cases hxy : x = y
    · rw [hxy, majorityPrefers_iff_card_lt_two_mul hwy]
      have hsupp : support P w y = k + (n - (k + k)) := by
        unfold support P
        rw [card_filter_threeBlock e hk r₀ r₁ r₂ (fun s => s.Prefers w y)]
        have h0 : r₀.Prefers w y :=
          tripleTop_prefers_second_third t hwm.symm hym.symm hwy
        have h1 : ¬ r₁.Prefers w y :=
          r₁.asymm (tripleTop_isTop t y w m w hwy)
        have h2 : r₂.Prefers w y := tripleTop_isTop t w m y y hwy.symm
        simp only [h0, h1, h2, ite_true, ite_false]
        omega
      rw [hsupp]
      omega
    -- Every voter ranks `w` above any `x ∉ {m, w, y}`.
    refine majorityPrefers_of_forall fun i => ?_
    unfold P threeBlockProfile
    split_ifs
    · unfold r₀ tripleTop
      rw [((t.toTop y).toTop w).toTop_prefers_of_ne hwm hxm]
      exact (t.toTop y).isTop_toTop w x hxw
    · unfold r₁ tripleTop
      rw [((t.toTop m).toTop w).toTop_prefers_of_ne hwy hxy]
      exact (t.toTop m).isTop_toTop w x hxw
    · exact tripleTop_isTop t w m y x hxw
  have hcnt : ∀ z : A, pluralityCount P z =
      (if z = m then k else 0) + (if z = y then k else 0) +
        (if z = w then n - (k + k) else 0) := by
    intro z
    unfold pluralityCount P
    rw [card_filter_threeBlock e hk r₀ r₁ r₂ (fun s => s.IsTop z)]
    have ht0 : r₀.IsTop z ↔ z = m :=
      ⟨fun h => h.unique (tripleTop_isTop t m w y), fun h => h ▸ tripleTop_isTop t m w y⟩
    have ht1 : r₁.IsTop z ↔ z = y :=
      ⟨fun h => h.unique (tripleTop_isTop t y w m), fun h => h ▸ tripleTop_isTop t y w m⟩
    have ht2 : r₂.IsTop z ↔ z = w :=
      ⟨fun h => h.unique (tripleTop_isTop t w m y), fun h => h ▸ tripleTop_isTop t w m y⟩
    simp only [ht0, ht1, ht2]
    rfl
  have htop_m : (pluralityRanking P t).IsTop m := by
    intro x hxm
    change pluralityCount P x < pluralityCount P m ∨
      (pluralityCount P m = pluralityCount P x ∧ t.Prefers m x)
    have hm_cnt : pluralityCount P m = k := by
      rw [hcnt m]
      simp only [ite_true, hym.symm, hwm.symm, ite_false]
      omega
    rw [hm_cnt, hcnt x]
    by_cases hxy : x = y
    · rw [hxy]
      simp only [hym, hwy.symm, ite_true, ite_false]
      exact Or.inr ⟨by omega, t.isTop_top y hym⟩
    by_cases hxw : x = w
    · rw [hxw]
      simp only [hwm, hwy, ite_true, ite_false]
      by_cases hlt : n - (k + k) < k
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, t.isTop_top w hwm⟩
    · simp only [hxm, hxy, hxw, ite_false]
      exact Or.inl (by omega)
  intro hcc
  exact hwm ((hcc P w hcw).symm.trans (plurality_eq_of_isTop t htop_m))

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
theorem isPareto_borda [Nonempty V] : (borda (V := V) (A := A)).IsPareto := by
  classical
  intro P a b h
  rw [borda_prefers]
  unfold bordaScore
  refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ =>
    Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun x hx => ?_).2 ⟨b, ?_, ?_⟩)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact (P i).trans _ _ _ (h i) hx
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h i
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (P i).irrefl b

/-- With at least two voters and two alternatives, the Borda count has no dictator: if voter `i`
ranks `a` first and `b` last while all other voters reverse that ranking, `b`'s Borda score is at
least `a`'s. -/
theorem not_isDictator_borda [Nontrivial A] (hV : 2 ≤ Fintype.card V) (i : V) :
    ¬ (borda (V := V) (A := A)).IsDictator i := by
  classical
  intro hi
  obtain ⟨a, b, hab⟩ := exists_pair_ne A
  obtain ⟨r₀⟩ := Ranking.nonempty A
  let r := (r₀.toBottom b).toTop a
  have htop_a : r.IsTop a := (r₀.toBottom b).isTop_toTop a
  have hbot_b : r.IsBottom b := by
    intro x hxb
    by_cases hxa : x = a
    · subst hxa
      exact htop_a b hab.symm
    · unfold r
      rw [(r₀.toBottom b).toTop_prefers_of_ne hxa hab.symm]
      exact r₀.isBottom_toBottom b x hxb
  let P : Profile V A := fun j => if j = i then r else r.reverse
  have hcard_top : ∀ {s : Ranking A} {z : A}, s.IsTop z →
      (Finset.univ.filter fun x => s.Prefers z x).card = Fintype.card A - 1 := by
    intro s z hz
    have hset : (Finset.univ.filter fun x => s.Prefers z x) = Finset.univ.erase z := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq, and_true]
      exact ⟨fun h => (s.ne_of_prefers h).symm, fun h => hz x h⟩
    rw [hset, Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ]
  have hcard_bot : ∀ {s : Ranking A} {z : A}, s.IsBottom z →
      (Finset.univ.filter fun x => s.Prefers z x).card = 0 := by
    intro s z hz
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hzx
    exact s.asymm hzx (hz x (s.ne_of_prefers hzx).symm)
  have hscore_a : bordaScore P a = Fintype.card A - 1 := by
    unfold bordaScore
    have hcongr : ∀ j : V,
        (Finset.univ.filter fun x => (P j).Prefers a x).card =
          if j = i then Fintype.card A - 1 else 0 := by
      intro j
      by_cases hj : j = i
      · simp only [P, hj, ite_true]
        exact hcard_top htop_a
      · simp only [P, hj, ite_false]
        exact hcard_bot fun x hxa => r.reverse_prefers.2 (htop_a x hxa)
    simp only [hcongr, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hscore_b : bordaScore P b = (Fintype.card V - 1) * (Fintype.card A - 1) := by
    unfold bordaScore
    have hcongr : ∀ j : V,
        (Finset.univ.filter fun x => (P j).Prefers b x).card =
          if j = i then 0 else Fintype.card A - 1 := by
      intro j
      by_cases hj : j = i
      · simp only [P, hj, ite_true]
        exact hcard_bot hbot_b
      · simp only [P, hj, ite_false]
        exact hcard_top fun x hxb => r.reverse_prefers.2 (hbot_b x hxb)
    simp only [hcongr]
    have hset : (Finset.univ.filter fun j : V => ¬ j = i) = Finset.univ.erase i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq, and_true]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, hset,
      Finset.sum_const_nat fun _ _ => rfl, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ]
  have hdict : (borda P).Prefers a b := hi P a b (by
    simp only [P, ite_true]
    exact htop_a b hab.symm)
  rw [borda_prefers, hscore_a, hscore_b] at hdict
  have hle : 1 * (Fintype.card A - 1) ≤ (Fintype.card V - 1) * (Fintype.card A - 1) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- With at least two voters and at least three alternatives, the Borda count violates IIA. -/
theorem not_isIIA_borda (hV : 2 ≤ Fintype.card V) (hA : 3 ≤ Fintype.card A) :
    ¬ (borda (V := V) (A := A)).IsIIA := by
  have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  have : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  intro hI
  obtain ⟨i, hi⟩ := isDictatorial_of_three_le_card isPareto_borda hI hA
  exact not_isDictator_borda hV i hi

end SocialWelfareFunction

end Borda

end Cslib.GameTheory.SocialChoice
