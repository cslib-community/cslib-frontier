/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.SocialChoice.Condorcet

/-!
# May's theorem characterizing majority rule

Kenneth May ([May1952]; see also [Fey2004], §1, p. 1, and §2, Definitions 1–2, pp. 5, 7) proved
that on two alternatives with a finite electorate, simple majority rule is the unique aggregation
rule satisfying three axioms:

1. **Anonymity** (`IsAnonymous`): permuting the voters does not change the social ranking.
2. **Neutrality** (`IsNeutral`): relabelling the alternatives relabels the social ranking in the
   same way.
3. **Positive responsiveness** (`IsPositivelyResponsive`): if society ranks `a` at least as high as
   `b` and a single voter strictly improves `a` relative to `b` while all other voters keep their
   ballots, society strictly prefers `a` to `b`.

We prove May's characterization on both preference models of social choice, for any finite
electorate `V` (odd, even, or empty):

* **Strict individual rankings** (`SocialWelfareFunction V A`): voters report linear orders
  `Ranking A` ([Fey2004], §2, p. 5) and `SocialWelfareFunction.twoAltMajority` compares `support`.
* **Weak individual rankings** (`WeakSocialWelfareFunction V A`): voters report complete preorders
  `WeakRanking A` (matching May's three-valued `{-1, 0, +1}` ballots with individual indifference
  [May1952]) and `WeakSocialWelfareFunction.twoAltMajority` compares `weakSupport`.

Both uniqueness proofs share a single ballot-agnostic symmetry-and-counting argument: if `a` has
strictly more votes than `b` yet society ranks `b` at least as high as `a`, reversing
`|V_a| - |V_b|` supporters of `a` produces a profile with swapped vote counts, which anonymity and
neutrality relate to `P`, contradicting positive responsiveness along those reversals.

## Main definitions

* `Ranking.relabel`, `WeakRanking.reverse`, `WeakRanking.relabel`: relabelling and reversal on
  rankings and weak rankings.
* `WeakProfile V A`, `WeakSocialWelfareFunction V A`, `weakSupport`: profiles of weak individual
  rankings, social welfare functions on them, and strict pairwise support.
* `SocialWelfareFunction.IsAnonymous`, `SocialWelfareFunction.IsNeutral`,
  `SocialWelfareFunction.IsPositivelyResponsive`, `SocialWelfareFunction.twoAltMajority`.
* `WeakSocialWelfareFunction.IsAnonymous`, `WeakSocialWelfareFunction.IsNeutral`,
  `WeakSocialWelfareFunction.IsPositivelyResponsive`, `WeakSocialWelfareFunction.twoAltMajority`.

## Main results

* `SocialWelfareFunction.isAnonymous_and_isNeutral_and_isPositivelyResponsive_iff`: **May's
  theorem** on strict profiles (`Fintype.card A = 2`).
* `WeakSocialWelfareFunction.isAnonymous_and_isNeutral_and_isPositivelyResponsive_iff`: **May's
  theorem** allowing individual indifference (`Fintype.card A = 2`).

## References

* [K. O. May, *A set of independent necessary and sufficient conditions for simple majority
  decisions*][May1952]
* [M. Fey, *May's theorem with an infinite population*][Fey2004]
-/

public section

namespace Cslib.GameTheory.SocialChoice

variable {V A B : Type*}

/-! ### Relabelling and reversal of rankings and weak rankings -/

/-- Transport a strict ranking along an equivalence of alternatives. -/
def Ranking.relabel (r : Ranking A) (e : A ≃ B) : Ranking B where
  Prefers x y := r.Prefers (e.symm x) (e.symm y)
  irrefl _ := r.irrefl _
  trans _ _ _ := r.trans _ _ _
  total _ _ hxy := r.total _ _ fun h => hxy (e.symm.injective h)

@[simp] theorem Ranking.relabel_prefers (r : Ranking A) (e : A ≃ B) {x y : B} :
    (r.relabel e).Prefers x y ↔ r.Prefers (e.symm x) (e.symm y) := Iff.rfl

/-- Reverse a weak ranking. -/
def WeakRanking.reverse (R : WeakRanking A) : WeakRanking A where
  AtLeast a b := R.AtLeast b a
  total a b := (R.total a b).symm
  trans _ _ _ hab hbc := R.trans _ _ _ hbc hab

@[simp] theorem WeakRanking.reverse_atLeast (R : WeakRanking A) {a b : A} :
    R.reverse.AtLeast a b ↔ R.AtLeast b a := Iff.rfl

@[simp] theorem WeakRanking.reverse_prefers (R : WeakRanking A) {a b : A} :
    R.reverse.Prefers a b ↔ R.Prefers b a := Iff.rfl

/-- Transport a weak ranking along an equivalence of alternatives. -/
def WeakRanking.relabel (R : WeakRanking A) (e : A ≃ B) : WeakRanking B where
  AtLeast x y := R.AtLeast (e.symm x) (e.symm y)
  total _ _ := R.total _ _
  trans _ _ _ := R.trans _ _ _

@[simp] theorem WeakRanking.relabel_atLeast (R : WeakRanking A) (e : A ≃ B) {x y : B} :
    (R.relabel e).AtLeast x y ↔ R.AtLeast (e.symm x) (e.symm y) := Iff.rfl

@[simp] theorem WeakRanking.relabel_prefers (R : WeakRanking A) (e : A ≃ B) {x y : B} :
    (R.relabel e).Prefers x y ↔ R.Prefers (e.symm x) (e.symm y) := Iff.rfl

/-- On a type with at most two elements, any three elements contain a duplicate. -/
theorem eq_or_eq_of_card_le_two [Fintype A] (hA : Fintype.card A ≤ 2) (x y z : A) :
    x = y ∨ y = z ∨ x = z := by
  by_contra! hne
  exact absurd (Fintype.two_lt_card_iff.2 ⟨x, y, z, hne.1, hne.2.2, hne.2.1⟩) (by omega)

/-! ### Shared symmetry and counting machinery -/

section SharedCore

open Classical in
private theorem card_filter_comp_perm [Fintype V] (σ : Equiv.Perm V) (p : V → Prop) :
    (Finset.univ.filter fun i => p (σ i)).card = (Finset.univ.filter p).card := by
  let emb : V ↪ V := σ.toEmbedding
  have hset : (Finset.univ.filter p) = (Finset.univ.filter fun i => p (σ i)).map emb := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    refine ⟨fun hj => ⟨σ.symm j, ?_, σ.apply_symm_apply j⟩, ?_⟩
    · simpa only [Equiv.apply_symm_apply] using hj
    · rintro ⟨i, hi, rfl⟩
      exact hi
  rw [hset, Finset.card_map]

open Classical in
private theorem card_filter_insert_of_off [Fintype V] {p q : V → Prop} {i : V}
    (hoff : ∀ j, j ≠ i → (p j ↔ q j)) (hnp : ¬ p i) (hq : q i) :
    (Finset.univ.filter q).card = (Finset.univ.filter p).card + 1 := by
  have hset : Finset.univ.filter q = insert i (Finset.univ.filter p) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hj : j = i
    · subst hj
      exact iff_of_true hq (Or.inl rfl)
    · rw [← hoff j hj]
      exact ⟨Or.inr, fun h => h.resolve_left hj⟩
  have hnotMem : i ∉ Finset.univ.filter p := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hnp
  rw [hset, Finset.card_insert_of_notMem hnotMem]

open Classical in
private theorem card_filter_le_of_off [Fintype V] {p q : V → Prop} {i : V}
    (hoff : ∀ j, j ≠ i → (p j ↔ q j)) (hnp : ¬ p i) :
    (Finset.univ.filter p).card ≤ (Finset.univ.filter q).card := by
  refine Finset.card_le_card fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  by_cases hji : j = i
  · subst hji
    exact absurd hj hnp
  · exact (hoff j hji).1 hj

open Classical in
private theorem not_or_le_of_single_improve [Fintype V] {a b : A} (hab : a ≠ b)
    {p₁ q₁ p₂ q₂ : V → Prop} {i : V}
    (hle : a = b ∨ (Finset.univ.filter q₁).card ≤ (Finset.univ.filter p₁).card)
    (hoff₁ : ∀ j, j ≠ i → (p₁ j ↔ p₂ j)) (hoff₂ : ∀ j, j ≠ i → (q₁ j ↔ q₂ j))
    (himp : (¬ p₁ i ∧ p₂ i ∧ ¬ q₂ i) ∨ (q₁ i ∧ ¬ q₂ i ∧ ¬ p₁ i)) :
    ¬ (b = a ∨ (Finset.univ.filter p₂).card ≤ (Finset.univ.filter q₂).card) := by
  have h0 := hle.resolve_left hab
  rintro (rfl | hge)
  · exact hab rfl
  · rcases himp with ⟨hnp₁, hp₂, hnq₂⟩ | ⟨hq₁, hnq₂, hnp₁⟩
    · have h1 := card_filter_insert_of_off hoff₁ hnp₁ hp₂
      have h2 := card_filter_le_of_off (fun j hj => (hoff₂ j hj).symm) hnq₂
      omega
    · have h1 := card_filter_insert_of_off (fun j hj => (hoff₂ j hj).symm) hnq₂ hq₁
      have h2 := card_filter_le_of_off hoff₁ hnp₁
      omega

/-- Given two pairs of disjoint voter sets `(s₁, t₁)` and `(s₂, t₂)` with swapped cardinalities
(`|s₁| = |t₂|` and `|t₁| = |s₂|`), there is a permutation of `V` sending `s₂` onto `t₁` and `t₂`
onto `s₁`. -/
private theorem exists_perm_swap_disjoint [Finite V] {s₁ t₁ s₂ t₂ : Finset V}
    (hd₁ : Disjoint s₁ t₁) (hd₂ : Disjoint s₂ t₂)
    (hc₁ : s₁.card = t₂.card) (hc₂ : t₁.card = s₂.card) :
    ∃ σ : Equiv.Perm V, (∀ i, i ∈ s₂ ↔ σ i ∈ t₁) ∧ (∀ i, i ∈ t₂ ↔ σ i ∈ s₁) := by
  classical
  have := Fintype.ofFinite V
  let c₁ : Finset V := Finset.univ \ (s₁ ∪ t₁)
  let c₂ : Finset V := Finset.univ \ (s₂ ∪ t₂)
  have e₂ : s₂ ≃ t₁ := Fintype.equivOfCardEq (by
    rw [Fintype.card_coe, Fintype.card_coe, hc₂])
  have e₁ : t₂ ≃ s₁ := Fintype.equivOfCardEq (by
    rw [Fintype.card_coe, Fintype.card_coe, hc₁])
  have hc₃ : c₂.card = c₁.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_union_of_disjoint hd₁, Finset.card_union_of_disjoint hd₂, hc₁, hc₂]
    omega
  have e₃ : c₂ ≃ c₁ := Fintype.equivOfCardEq (by
    rw [Fintype.card_coe, Fintype.card_coe, hc₃])
  have hmem_c₂ : ∀ {i : V}, i ∉ s₂ → i ∉ t₂ → i ∈ c₂ := fun hs ht =>
    Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun hu => (Finset.mem_union.1 hu).elim hs ht⟩
  let f : V → V := fun i =>
    if hs : i ∈ s₂ then (e₂ ⟨i, hs⟩ : V)
    else if ht : i ∈ t₂ then (e₁ ⟨i, ht⟩ : V)
    else (e₃ ⟨i, hmem_c₂ hs ht⟩ : V)
  have hmem_t₁ : ∀ i, f i ∈ t₁ ↔ i ∈ s₂ := by
    intro i
    by_cases hs : i ∈ s₂
    · simp only [f, hs, dite_true, iff_true]
      exact (e₂ ⟨i, hs⟩).2
    · by_cases ht : i ∈ t₂
      · simp only [f, hs, ht, dite_false, dite_true, iff_false]
        exact Finset.disjoint_left.1 hd₁ (e₁ ⟨i, ht⟩).2
      · simp only [f, hs, ht, dite_false, iff_false]
        have hc := (Finset.mem_sdiff.1 (e₃ ⟨i, hmem_c₂ hs ht⟩).2).2
        exact fun h => hc (Finset.mem_union_right _ h)
  have hmem_s₁ : ∀ i, f i ∈ s₁ ↔ i ∈ t₂ := by
    intro i
    by_cases hs : i ∈ s₂
    · simp only [f, hs, dite_true]
      exact iff_of_false (Finset.disjoint_right.1 hd₁ (e₂ ⟨i, hs⟩).2)
        (Finset.disjoint_left.1 hd₂ hs)
    · by_cases ht : i ∈ t₂
      · simp only [f, hs, ht, dite_false, dite_true, iff_true]
        exact (e₁ ⟨i, ht⟩).2
      · simp only [f, hs, ht, dite_false, iff_false]
        have hc := (Finset.mem_sdiff.1 (e₃ ⟨i, hmem_c₂ hs ht⟩).2).2
        exact fun h => hc (Finset.mem_union_left _ h)
  have hinj : Function.Injective f := by
    intro i j hij
    by_cases hsi : i ∈ s₂
    · have hsj : j ∈ s₂ := (hmem_t₁ j).1 (hij ▸ (hmem_t₁ i).2 hsi)
      simp only [f, hsi, hsj, dite_true] at hij
      exact congrArg Subtype.val (e₂.injective (Subtype.ext hij))
    · by_cases hti : i ∈ t₂
      · have htj : j ∈ t₂ := (hmem_s₁ j).1 (hij ▸ (hmem_s₁ i).2 hti)
        have hsj : j ∉ s₂ := fun hsj => Finset.disjoint_left.1 hd₂ hsj htj
        simp only [f, hsi, hsj, hti, htj, dite_false, dite_true] at hij
        exact congrArg Subtype.val (e₁.injective (Subtype.ext hij))
      · have hsj : j ∉ s₂ := fun hsj => hsi ((hmem_t₁ i).1 (hij.symm ▸ (hmem_t₁ j).2 hsj))
        have htj : j ∉ t₂ := fun htj => hti ((hmem_s₁ i).1 (hij.symm ▸ (hmem_s₁ j).2 htj))
        simp only [f, hsi, hsj, hti, htj, dite_false] at hij
        exact congrArg Subtype.val (e₃.injective (Subtype.ext hij))
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, rfl⟩
  exact ⟨Equiv.ofBijective f hbij, fun i => (hmem_t₁ i).symm, fun i => (hmem_s₁ i).symm⟩

open Classical in
/-- Ballot-agnostic core of May's theorem on a distinct pair `(a, b)` covering `A`. -/
private theorem may_atLeast_iff_card_le [Fintype V] {B : Type*}
    (pref : B → A → A → Prop) (rev : B → B) (relab : Equiv.Perm A → B → B)
    (F : (V → B) → WeakRanking A) {a b : A}
    (hasymm : ∀ (x : B) {u v : A}, pref x u v → ¬ pref x v u)
    (hrev : ∀ (x : B) (u v : A), pref (rev x) u v ↔ pref x v u)
    (hswap : ∀ x : B, relab (Equiv.swap a b) x = rev x)
    (hext : ∀ x y : B, (pref x a b ↔ pref y a b) → (pref x b a ↔ pref y b a) → x = y)
    (hanon : ∀ (σ : Equiv.Perm V) (P : V → B), F (P ∘ σ) = F P)
    (hneut : ∀ (e : Equiv.Perm A) (P : V → B), F (fun i => relab e (P i)) = (F P).relabel e)
    (hpr : ∀ (P Q : V → B) (u v : A) (i : V), (∀ j, j ≠ i → P j = Q j) →
      ¬ pref (P i) u v → pref (Q i) u v → (F P).AtLeast u v → (F Q).Prefers u v)
    (P : V → B) :
    (F P).AtLeast a b ↔
      (Finset.univ.filter fun i => pref (P i) b a).card ≤
        (Finset.univ.filter fun i => pref (P i) a b).card := by
  -- Repeated single-voter improvements along a nonempty finset `S`.
  have hpr_finset : ∀ {P₀ Q : V → B} {u v : A} {S : Finset V},
      S.Nonempty → (∀ j, j ∉ S → P₀ j = Q j) →
      (∀ i ∈ S, ¬ pref (P₀ i) u v ∧ pref (Q i) u v) →
      (F P₀).AtLeast u v → (F Q).Prefers u v := by
    intro P₀ Q u v S hS hagree himp hF₀
    let step : Finset V → V → B := fun t j => if j ∈ t then Q j else P₀ j
    have hkey : ∀ {t : Finset V}, t.Nonempty → t ⊆ S → (F (step t)).Prefers u v := by
      intro t ht
      induction ht using Finset.Nonempty.cons_induction with
      | singleton i =>
        intro hiS
        have hmem : i ∈ S := hiS (Finset.mem_singleton_self i)
        refine hpr P₀ (step {i}) u v i (fun j hj => ?_) (himp i hmem).1 ?_ hF₀
        · simp only [step, Finset.mem_singleton, hj, ite_false]
        · simp only [step, Finset.mem_singleton, ite_true]
          exact (himp i hmem).2
      | cons i t hit _ ih =>
        intro hsub
        have hiS : i ∈ S := hsub (Finset.mem_cons_self i t)
        have htS : t ⊆ S := fun j hj => hsub (Finset.mem_cons_of_mem hj)
        have hprev : (F (step t)).AtLeast u v := (F (step t)).atLeast_of_prefers (ih htS)
        refine hpr (step t) (step (Finset.cons i t hit)) u v i (fun j hj => ?_) ?_ ?_ hprev
        · simp only [step, Finset.mem_cons, hj, false_or]
        · simp only [step, hit, ite_false]
          exact (himp i hiS).1
        · simp only [step, Finset.mem_cons, true_or, ite_true]
          exact (himp i hiS).2
    have hstepS : step S = Q := by
      funext j
      by_cases hj : j ∈ S
      · simp only [step, hj, ite_true]
      · simp only [step, hj, ite_false, hagree j hj]
    rw [← hstepS]
    exact hkey hS Finset.Subset.rfl
  -- Two profiles with swapped `(a, b)` and `(b, a)` support counts have swapped social rankings.
  have hswap_counts : ∀ {Q₁ Q₂ : V → B},
      (Finset.univ.filter fun i => pref (Q₁ i) a b).card =
        (Finset.univ.filter fun i => pref (Q₂ i) b a).card →
      (Finset.univ.filter fun i => pref (Q₁ i) b a).card =
        (Finset.univ.filter fun i => pref (Q₂ i) a b).card →
      ((F Q₂).AtLeast a b ↔ (F Q₁).AtLeast b a) ∧
        ((F Q₂).AtLeast b a ↔ (F Q₁).AtLeast a b) := by
    intro Q₁ Q₂ hc₁ hc₂
    have hd₁ : Disjoint (Finset.univ.filter fun i => pref (Q₁ i) a b)
        (Finset.univ.filter fun i => pref (Q₁ i) b a) :=
      Finset.disjoint_left.2 fun i hi₁ hi₂ =>
        hasymm (Q₁ i) (Finset.mem_filter.1 hi₁).2 (Finset.mem_filter.1 hi₂).2
    have hd₂ : Disjoint (Finset.univ.filter fun i => pref (Q₂ i) a b)
        (Finset.univ.filter fun i => pref (Q₂ i) b a) :=
      Finset.disjoint_left.2 fun i hi₁ hi₂ =>
        hasymm (Q₂ i) (Finset.mem_filter.1 hi₁).2 (Finset.mem_filter.1 hi₂).2
    obtain ⟨σ, hσ₁, hσ₂⟩ := exists_perm_swap_disjoint hd₁ hd₂ hc₁ hc₂
    have hrel : (fun i => relab (Equiv.swap a b) (Q₁ (σ i))) = Q₂ := by
      funext i
      rw [hswap]
      refine hext _ _ ?_ ?_
      · have := hσ₁ i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        rw [hrev]
        exact this.symm
      · have := hσ₂ i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        rw [hrev]
        exact this.symm
    have hFQ : F Q₂ = (F Q₁).relabel (Equiv.swap a b) := by
      rw [← hrel]
      exact (hneut (Equiv.swap a b) (Q₁ ∘ σ)).trans (by rw [hanon σ Q₁])
    rw [hFQ]
    constructor <;>
      simp only [WeakRanking.relabel_atLeast, Equiv.symm_swap, Equiv.swap_apply_left,
        Equiv.swap_apply_right]
  -- Strict majority in either direction forces strict social preference.
  have hstrict : ∀ {u v : A}, (u = a ∧ v = b ∨ u = b ∧ v = a) →
      (Finset.univ.filter fun i => pref (P i) v u).card <
        (Finset.univ.filter fun i => pref (P i) u v).card →
      (F P).Prefers u v := by
    intro u v huv hlt hvu
    let s_uv := Finset.univ.filter fun i => pref (P i) u v
    let s_vu := Finset.univ.filter fun i => pref (P i) v u
    have hlt' : s_vu.card < s_uv.card := hlt
    obtain ⟨S, hSsub, hScard⟩ :=
      Finset.exists_subset_card_eq (s := s_uv) (Nat.sub_le s_uv.card s_vu.card)
    have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
    let P₀ : V → B := fun i => if i ∈ S then rev (P i) else P i
    have hd_P : Disjoint s_uv s_vu :=
      Finset.disjoint_left.2 fun i hi₁ hi₂ =>
        hasymm (P i) (Finset.mem_filter.1 hi₁).2 (Finset.mem_filter.1 hi₂).2
    have hcnt_uv : (Finset.univ.filter fun i => pref (P₀ i) u v) = s_uv \ S := by
      ext i
      simp only [s_uv, P₀, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
      by_cases hi : i ∈ S
      · simp only [hi, not_true_eq_false, and_false, ite_true, hrev, iff_false]
        exact hasymm (P i) (Finset.mem_filter.1 (hSsub hi)).2
      · simp only [hi, not_false_eq_true, and_true, ite_false]
    have hcnt_vu : (Finset.univ.filter fun i => pref (P₀ i) v u) = s_vu ∪ S := by
      ext i
      simp only [s_vu, P₀, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
      by_cases hi : i ∈ S
      · simp only [hi, or_true, ite_true, hrev, iff_true]
        exact (Finset.mem_filter.1 (hSsub hi)).2
      · simp only [hi, or_false, ite_false]
    have hc_uv : (Finset.univ.filter fun i => pref (P₀ i) u v).card = s_vu.card := by
      rw [hcnt_uv, Finset.card_sdiff_of_subset hSsub, hScard]
      omega
    have hc_vu : (Finset.univ.filter fun i => pref (P₀ i) v u).card = s_uv.card := by
      have hdS : Disjoint s_vu S := hd_P.symm.mono_right hSsub
      rw [hcnt_vu, Finset.card_union_of_disjoint hdS, hScard]
      omega
    have hP₀_uv : (F P₀).AtLeast u v := by
      rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (hswap_counts hc_vu.symm hc_uv.symm).1.2 hvu
      · exact (hswap_counts hc_uv.symm hc_vu.symm).2.2 hvu
    refine hpr_finset hSne (fun j hj => ?_) (fun i hi => ?_) hP₀_uv hvu
    · simp only [P₀, hj, ite_false]
    · have hi_uv : pref (P i) u v := (Finset.mem_filter.1 (hSsub hi)).2
      simp only [P₀, hi, ite_true, hrev]
      exact ⟨hasymm (P i) hi_uv, hi_uv⟩
  rcases lt_trichotomy
      (Finset.univ.filter fun i => pref (P i) b a).card
      (Finset.univ.filter fun i => pref (P i) a b).card
    with hlt | heq | hgt
  · exact iff_of_true ((F P).atLeast_of_prefers (hstrict (Or.inl ⟨rfl, rfl⟩) hlt)) hlt.le
  · have hsymm := (hswap_counts (Q₁ := P) (Q₂ := P) heq.symm heq).1
    have hall : (F P).AtLeast a b :=
      ((F P).total a b).elim id fun hba => hsymm.2 hba
    exact iff_of_true hall heq.le
  · exact iff_of_false (hstrict (Or.inr ⟨rfl, rfl⟩) hgt) (not_le_of_gt hgt)

/-- On a two-element set `{x, y}` (`x ≠ y`), swapping `x` and `y` in any symmetric binary relation
is equivalent to reversing its arguments. -/
private theorem swap_rel_iff_of_cover [DecidableEq A] {x y : A} (hxy : x ≠ y)
    (hcover : ∀ z : A, z = x ∨ z = y) {rel : A → A → Prop}
    {u v : A} (hdiag : u = v → (rel (Equiv.swap x y u) (Equiv.swap x y v) ↔ rel v u)) :
    rel (Equiv.swap x y u) (Equiv.swap x y v) ↔ rel v u := by
  by_cases huv : u = v
  · exact hdiag huv
  rcases hcover u with rfl | rfl <;> rcases hcover v with rfl | rfl
  · exact absurd rfl huv
  · rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
  · rw [Equiv.swap_apply_right, Equiv.swap_apply_left]
  · exact absurd rfl huv

end SharedCore

/-! ### May's theorem on strict profiles (`SocialWelfareFunction`) -/

namespace SocialWelfareFunction

variable (F : SocialWelfareFunction V A)

/-- `F` is **anonymous**: permuting the voters leaves the social ranking unchanged
([May1952]; [Fey2004], Definition 2, p. 7). -/
@[expose] def IsAnonymous : Prop :=
  ∀ (σ : Equiv.Perm V) (P : Profile V A), F (P ∘ σ) = F P

/-- `F` is **neutral**: relabelling the alternatives relabels the social ranking in the same way
([May1952]; [Fey2004], Definition 1, p. 5). -/
@[expose] def IsNeutral : Prop :=
  ∀ (e : Equiv.Perm A) (P : Profile V A), F (fun i => (P i).relabel e) = (F P).relabel e

/-- `F` is **positively responsive**: if society ranks `a` at least as high as `b`, and a single
voter changes their ballot to rank `a` strictly above `b` while all other voters keep their
rankings, then society strictly prefers `a` to `b` ([May1952]; [Fey2004], Definition 1, p. 5). -/
@[expose] def IsPositivelyResponsive : Prop :=
  ∀ (P Q : Profile V A) (a b : A) (i : V),
    (∀ j, j ≠ i → P j = Q j) →
    ¬ (P i).Prefers a b → (Q i).Prefers a b →
    (F P).AtLeast a b → (F Q).Prefers a b

/-- **Simple majority rule** on a domain of at most two alternatives: `a` is ranked at least as
high as `b` when `a = b` or at least as many voters prefer `a` to `b` as `b` to `a`. -/
@[expose] noncomputable def twoAltMajority [Fintype V]
    (hA : ∀ x y z : A, x = y ∨ y = z ∨ x = z) : SocialWelfareFunction V A :=
  fun P =>
  { AtLeast := fun a b => a = b ∨ support P b a ≤ support P a b
    total := fun a b => by
      by_cases hab : a = b
      · exact Or.inl (Or.inl hab)
      · exact (le_total (support P b a) (support P a b)).imp Or.inr Or.inr
    trans := fun a b c => by
      rintro (rfl | hab) (rfl | hbc)
      · exact Or.inl rfl
      · exact Or.inr hbc
      · exact Or.inr hab
      · by_cases h1 : a = b
        · subst h1; exact Or.inr hbc
        by_cases h2 : b = c
        · subst h2; exact Or.inr hab
        exact Or.inl (((hA a b c).resolve_left h1).resolve_left h2) }

theorem isAnonymous_twoAltMajority [Fintype V] (hA : ∀ x y z : A, x = y ∨ y = z ∨ x = z) :
    (twoAltMajority (V := V) hA).IsAnonymous := by
  intro σ P
  ext a b
  change (a = b ∨ support (P ∘ σ) b a ≤ support (P ∘ σ) a b) ↔
    (a = b ∨ support P b a ≤ support P a b)
  unfold support
  simp only [Function.comp_apply]
  rw [card_filter_comp_perm σ fun i => (P i).Prefers b a,
    card_filter_comp_perm σ fun i => (P i).Prefers a b]

theorem isNeutral_twoAltMajority [Fintype V] (hA : ∀ x y z : A, x = y ∨ y = z ∨ x = z) :
    (twoAltMajority (V := V) hA).IsNeutral := fun e P => by
  ext a b
  exact or_congr e.symm.injective.eq_iff.symm Iff.rfl

theorem isPositivelyResponsive_twoAltMajority [Fintype V]
    (hA : ∀ x y z : A, x = y ∨ y = z ∨ x = z) :
    (twoAltMajority (V := V) hA).IsPositivelyResponsive :=
  fun _ Q _ _ i hPQ hnP hQ hFP =>
    not_or_le_of_single_improve ((Q i).ne_of_prefers hQ) hFP
      (fun j hj => by rw [hPQ j hj]) (fun j hj => by rw [hPQ j hj])
      (Or.inl ⟨hnP, hQ, (Q i).asymm hQ⟩)

variable {F}

/-- Uniqueness direction of **May's theorem** on strict profiles ([May1952]; [Fey2004], §1, p. 1):
with finitely many voters and two alternatives, every anonymous, neutral, positively responsive
social welfare function is `twoAltMajority`. -/
theorem eq_twoAltMajority [Fintype V] [Fintype A] (h2 : Fintype.card A = 2)
    (hanon : F.IsAnonymous) (hneut : F.IsNeutral) (hpr : F.IsPositivelyResponsive) :
    F = twoAltMajority (eq_or_eq_of_card_le_two h2.le) := by
  classical
  have hA := eq_or_eq_of_card_le_two h2.le
  funext P
  ext x y
  change (F P).AtLeast x y ↔ x = y ∨ support P y x ≤ support P x y
  by_cases hxy : x = y
  · subst hxy
    exact iff_of_true ((F P).refl x) (Or.inl rfl)
  have hcover : ∀ z : A, z = x ∨ z = y := fun z =>
    (hA z x y).elim Or.inl fun h => h.elim (fun h' => absurd h' hxy) Or.inr
  have hswap : ∀ r : Ranking A, r.relabel (Equiv.swap x y) = r.reverse := fun r => by
    ext u v
    rw [Ranking.relabel_prefers, Ranking.reverse_prefers, Equiv.symm_swap]
    exact swap_rel_iff_of_cover hxy hcover fun huv => by
      subst huv; exact iff_of_false (r.irrefl _) (r.irrefl _)
  have hext : ∀ r s : Ranking A,
      (r.Prefers x y ↔ s.Prefers x y) → (r.Prefers y x ↔ s.Prefers y x) → r = s := by
    intro r s h1 h2
    ext u v
    by_cases huv : u = v
    · subst huv; exact iff_of_false (r.irrefl u) (s.irrefl u)
    rcases hcover u with rfl | rfl <;> rcases hcover v with rfl | rfl
    · exact absurd rfl huv
    · exact h1
    · exact h2
    · exact absurd rfl huv
  have hiff := may_atLeast_iff_card_le Ranking.Prefers Ranking.reverse
    (fun e r => r.relabel e) F (a := x) (b := y) (fun r _ _ => r.asymm)
    (fun r u v => r.reverse_prefers) hswap hext hanon hneut hpr P
  exact hiff.trans ⟨Or.inr, fun h => h.resolve_left hxy⟩

/-- **May's theorem** on strict profiles ([May1952]; [Fey2004], §1, p. 1): on two alternatives with
finitely many voters, simple majority rule is the unique anonymous, neutral, positively responsive
social welfare function. -/
theorem isAnonymous_and_isNeutral_and_isPositivelyResponsive_iff [Fintype V] [Fintype A]
    (h2 : Fintype.card A = 2) :
    F.IsAnonymous ∧ F.IsNeutral ∧ F.IsPositivelyResponsive ↔
      F = twoAltMajority (eq_or_eq_of_card_le_two h2.le) := by
  refine ⟨fun ⟨ha, hn, hp⟩ => eq_twoAltMajority h2 ha hn hp, ?_⟩
  rintro rfl
  exact ⟨isAnonymous_twoAltMajority _, isNeutral_twoAltMajority _,
    isPositivelyResponsive_twoAltMajority _⟩

end SocialWelfareFunction

/-! ### May's theorem with individual indifference (`WeakSocialWelfareFunction`) -/

/-- A **weak preference profile**: one weak ranking (allowing ties) for each voter. -/
abbrev WeakProfile (V A : Type*) := V → WeakRanking A

/-- A **social welfare function on weak profiles**: aggregates weak individual rankings into a
social weak ranking. -/
abbrev WeakSocialWelfareFunction (V A : Type*) := WeakProfile V A → WeakRanking A

open Classical in
/-- Strict pairwise support in a weak profile: the number of voters who strictly prefer `a` to
`b` (indifferent voters contribute to neither `weakSupport P a b` nor `weakSupport P b a`). -/
@[expose] noncomputable def weakSupport [Fintype V] (P : WeakProfile V A) (a b : A) : ℕ :=
  (Finset.univ.filter fun i => (P i).Prefers a b).card

namespace WeakSocialWelfareFunction

variable (G : WeakSocialWelfareFunction V A)

/-- `G` is **anonymous**: permuting the voters leaves the social ranking unchanged ([May1952]). -/
@[expose] def IsAnonymous : Prop :=
  ∀ (σ : Equiv.Perm V) (P : WeakProfile V A), G (P ∘ σ) = G P

/-- `G` is **neutral**: relabelling the alternatives relabels the social ranking in the same way
([May1952]). -/
@[expose] def IsNeutral : Prop :=
  ∀ (e : Equiv.Perm A) (P : WeakProfile V A), G (fun i => (P i).relabel e) = (G P).relabel e

/-- `G` is **positively responsive** on weak ballots ([May1952]): if society ranks `a` at least as
high as `b` and a single voter `i` strictly improves `a` relative to `b` (either moving to
strict preference `a ≻_i b` from indifference or `b ≻_i a`, or moving from `b ≻_i a` to
indifference or `a ≻_i b`) while all other voters keep their ballots, then society strictly
prefers `a` to `b`. -/
@[expose] def IsPositivelyResponsive : Prop :=
  ∀ (P Q : WeakProfile V A) (a b : A) (i : V),
    (∀ j, j ≠ i → P j = Q j) →
    ((¬ (P i).Prefers a b ∧ (Q i).Prefers a b) ∨ ((P i).Prefers b a ∧ ¬ (Q i).Prefers b a)) →
    (G P).AtLeast a b → (G Q).Prefers a b

/-- **Simple majority rule** on weak individual profiles over at most two alternatives ([May1952]):
`a` is ranked at least as high as `b` when `a = b` or at least as many voters strictly prefer `a`
to `b` as strictly prefer `b` to `a`. -/
@[expose] noncomputable def twoAltMajority [Fintype V]
    (hA : ∀ x y z : A, x = y ∨ y = z ∨ x = z) : WeakSocialWelfareFunction V A :=
  fun P =>
  { AtLeast := fun a b => a = b ∨ weakSupport P b a ≤ weakSupport P a b
    total := fun a b => by
      by_cases hab : a = b
      · exact Or.inl (Or.inl hab)
      · exact (le_total (weakSupport P b a) (weakSupport P a b)).imp Or.inr Or.inr
    trans := fun a b c => by
      rintro (rfl | hab) (rfl | hbc)
      · exact Or.inl rfl
      · exact Or.inr hbc
      · exact Or.inr hab
      · by_cases h1 : a = b
        · subst h1; exact Or.inr hbc
        by_cases h2 : b = c
        · subst h2; exact Or.inr hab
        exact Or.inl (((hA a b c).resolve_left h1).resolve_left h2) }

theorem isAnonymous_twoAltMajority [Fintype V] (hA : ∀ x y z : A, x = y ∨ y = z ∨ x = z) :
    (twoAltMajority (V := V) hA).IsAnonymous := by
  intro σ P
  ext a b
  change (a = b ∨ weakSupport (P ∘ σ) b a ≤ weakSupport (P ∘ σ) a b) ↔
    (a = b ∨ weakSupport P b a ≤ weakSupport P a b)
  unfold weakSupport
  simp only [Function.comp_apply]
  rw [card_filter_comp_perm σ fun i => (P i).Prefers b a,
    card_filter_comp_perm σ fun i => (P i).Prefers a b]

theorem isNeutral_twoAltMajority [Fintype V] (hA : ∀ x y z : A, x = y ∨ y = z ∨ x = z) :
    (twoAltMajority (V := V) hA).IsNeutral := fun e P => by
  ext a b
  exact or_congr e.symm.injective.eq_iff.symm Iff.rfl

theorem isPositivelyResponsive_twoAltMajority [Fintype V]
    (hA : ∀ x y z : A, x = y ∨ y = z ∨ x = z) :
    (twoAltMajority (V := V) hA).IsPositivelyResponsive := by
  intro P Q a b i hPQ himp hGP
  rcases himp with ⟨hnP, hQ⟩ | ⟨hP, hnQ⟩
  · exact not_or_le_of_single_improve (fun (h : a = b) => (Q i).prefers_irrefl a (h ▸ hQ)) hGP
      (fun j hj => by rw [hPQ j hj]) (fun j hj => by rw [hPQ j hj])
      (Or.inl ⟨hnP, hQ, (Q i).prefers_asymm hQ⟩)
  · exact not_or_le_of_single_improve (fun (h : a = b) => (P i).prefers_irrefl b (h ▸ hP)) hGP
      (fun j hj => by rw [hPQ j hj]) (fun j hj => by rw [hPQ j hj])
      (Or.inr ⟨hP, hnQ, (P i).prefers_asymm hP⟩)

variable {G}

/-- Uniqueness direction of **May's theorem** allowing individual indifference ([May1952]): with
finitely many voters and two alternatives, every anonymous, neutral, positively responsive rule on
weak profiles is `twoAltMajority`. -/
theorem eq_twoAltMajority [Fintype V] [Fintype A] (h2 : Fintype.card A = 2)
    (hanon : G.IsAnonymous) (hneut : G.IsNeutral) (hpr : G.IsPositivelyResponsive) :
    G = twoAltMajority (eq_or_eq_of_card_le_two h2.le) := by
  classical
  have hA := eq_or_eq_of_card_le_two h2.le
  funext P
  ext x y
  change (G P).AtLeast x y ↔ x = y ∨ weakSupport P y x ≤ weakSupport P x y
  by_cases hxy : x = y
  · subst hxy
    exact iff_of_true ((G P).refl x) (Or.inl rfl)
  have hcover : ∀ z : A, z = x ∨ z = y := fun z =>
    (hA z x y).elim Or.inl fun h => h.elim (fun h' => absurd h' hxy) Or.inr
  have hswap : ∀ R : WeakRanking A, R.relabel (Equiv.swap x y) = R.reverse := fun R => by
    ext u v
    rw [WeakRanking.relabel_atLeast, WeakRanking.reverse_atLeast, Equiv.symm_swap]
    exact swap_rel_iff_of_cover hxy hcover fun huv => by
      subst huv; exact iff_of_true (R.refl _) (R.refl _)
  have hext : ∀ R S : WeakRanking A,
      (R.Prefers x y ↔ S.Prefers x y) → (R.Prefers y x ↔ S.Prefers y x) → R = S := by
    intro R S h1 h2
    ext u v
    by_cases huv : u = v
    · subst huv; exact iff_of_true (R.refl u) (S.refl u)
    rcases hcover u with rfl | rfl <;> rcases hcover v with rfl | rfl
    · exact absurd rfl huv
    · exact not_iff_not.1 h2
    · exact not_iff_not.1 h1
    · exact absurd rfl huv
  have hiff := may_atLeast_iff_card_le WeakRanking.Prefers WeakRanking.reverse
    (fun e R => R.relabel e) G (a := x) (b := y) (fun R _ _ => R.prefers_asymm)
    (fun R u v => R.reverse_prefers) hswap hext hanon hneut
    (fun P₁ P₂ u v i h12 hn1 h2 => hpr P₁ P₂ u v i h12 (Or.inl ⟨hn1, h2⟩)) P
  exact hiff.trans ⟨Or.inr, fun h => h.resolve_left hxy⟩

/-- **May's theorem** allowing individual indifference ([May1952]): on two alternatives with
finitely many voters, simple majority rule is the unique anonymous, neutral, positively responsive
social welfare function on weak individual rankings. -/
theorem isAnonymous_and_isNeutral_and_isPositivelyResponsive_iff [Fintype V] [Fintype A]
    (h2 : Fintype.card A = 2) :
    G.IsAnonymous ∧ G.IsNeutral ∧ G.IsPositivelyResponsive ↔
      G = twoAltMajority (eq_or_eq_of_card_le_two h2.le) := by
  refine ⟨fun ⟨ha, hn, hp⟩ => eq_twoAltMajority h2 ha hn hp, ?_⟩
  rintro rfl
  exact ⟨isAnonymous_twoAltMajority _, isNeutral_twoAltMajority _,
    isPositivelyResponsive_twoAltMajority _⟩

end WeakSocialWelfareFunction

end Cslib.GameTheory.SocialChoice
