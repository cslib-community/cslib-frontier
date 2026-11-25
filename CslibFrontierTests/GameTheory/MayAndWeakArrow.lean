/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.SocialChoice.WeakOrder
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FinCases

/-!
# Clients for Condorcet, May's theorem, weak-order Arrow, and Fishburn ultrafilters

This is a `module` importing the public surface of
`CslibFrontier.GameTheory.SocialChoice.Condorcet`,
`CslibFrontier.GameTheory.SocialChoice.May`, and
`CslibFrontier.GameTheory.SocialChoice.WeakOrder`:

* **Condorcet's paradox (`n = 3`)** ([Nisan2007], §9.2.1, p. 211): on `Fin 3` voters and `Fin 3`
  candidates, the cyclic profile `0 ≻ 1 ≻ 2`, `1 ≻ 2 ≻ 0`, `2 ≻ 0 ≻ 1` satisfies
  `MajorityPrefers P 0 1 ∧ MajorityPrefers P 1 2 ∧ MajorityPrefers P 2 0` and has no Condorcet
  winner.
* **Plurality manipulation and Condorcet inconsistency (`n = 3`) vs the `(n = 4, |A| = 3)`
  boundary** ([Nisan2007], §9.2.2, pp. 211–212): on three voters and three candidates, candidate
  `1` is the strict Condorcet winner yet tie-broken plurality chooses `2`, and voter `0`
  (`0 ≻ 1 ≻ 2`) gains by voting for `1` instead of `0`. At `(n = 4, |A| = 3)`, by contrast, every
  Condorcet winner has at least two first-place votes while each rival has at most one, so plurality
  is Condorcet consistent (`plurality_fin4_fin3_isCondorcetConsistent`), showing that `|V| ≠ 4` in
  `SocialChoiceFunction.not_isCondorcetConsistent_plurality` is sharp.
* **May's theorem and axiom independence** ([May1952]; [Fey2004]): instantiations on `Bool` for
  strict and weak profiles, a concrete weak profile with indifferent voters, and three rules on
  `Bool` dropping anonymity, neutrality, and positive responsiveness one at a time.
* **Weak-order Arrow and serial dictatorship** ([Arrow1951]): unique dictator on `(Fin 3, Fin 3)`
  weak profiles, and `serialDictatorship 0 1 ≠ WeakSocialWelfareFunction.dictatorship 0`.
* **Fishburn's infinite-electorate ultrafilter** ([Fishburn1970]): non-dictatorial weakly Pareto,
  IIA social welfare function on `ℕ` voters and `Fin 3` alternatives.
-/

@[expose] public section

namespace CslibFrontierTests.GameTheory.MayAndWeakArrow

open Cslib.GameTheory.SocialChoice

/-! ### Score-vector rankings on `Fin 3` -/

/-- The ranking of `Fin 3` by an injective score vector: higher scores rank higher. -/
def ofScore (s : Fin 3 → ℕ) (hs : Function.Injective s) : Ranking (Fin 3) where
  Prefers x y := s y < s x
  irrefl _ := lt_irrefl _
  trans _ _ _ h1 h2 := h2.trans h1
  total x y hxy := by
    rcases lt_trichotomy (s x) (s y) with h | h | h
    · exact Or.inr h
    · exact absurd (hs h) hxy
    · exact Or.inl h

@[simp] theorem ofScore_prefers (s : Fin 3 → ℕ) (hs : Function.Injective s) {x y : Fin 3} :
    (ofScore s hs).Prefers x y ↔ s y < s x := Iff.rfl

theorem support_ofScore3 (s₀ s₁ s₂ : Fin 3 → ℕ) (h₀ : Function.Injective s₀)
    (h₁ : Function.Injective s₁) (h₂ : Function.Injective s₂) (a b : Fin 3) :
    support ![ofScore s₀ h₀, ofScore s₁ h₁, ofScore s₂ h₂] a b =
      (if s₀ b < s₀ a then 1 else 0) + (if s₁ b < s₁ a then 1 else 0) +
        (if s₂ b < s₂ a then 1 else 0) := by
  classical
  unfold support
  rw [Finset.card_filter, Fin.sum_univ_three]
  convert rfl <;> exact Iff.rfl

theorem pluralityCount_ofScore3 (s₀ s₁ s₂ : Fin 3 → ℕ) (h₀ : Function.Injective s₀)
    (h₁ : Function.Injective s₁) (h₂ : Function.Injective s₂) (a : Fin 3) :
    pluralityCount ![ofScore s₀ h₀, ofScore s₁ h₁, ofScore s₂ h₂] a =
      (if ∀ x, x ≠ a → s₀ x < s₀ a then 1 else 0) +
        (if ∀ x, x ≠ a → s₁ x < s₁ a then 1 else 0) +
        (if ∀ x, x ≠ a → s₂ x < s₂ a then 1 else 0) := by
  classical
  unfold pluralityCount Ranking.IsTop
  rw [Finset.card_filter, Fin.sum_univ_three]
  convert rfl <;> exact Iff.rfl

/-! ### Condorcet's paradox (`n = 3`, NRTV §9.2.1, p. 211) -/

section CondorcetParadox

/-- Three-voter cyclic profile: `0 ≻ 1 ≻ 2`, `1 ≻ 2 ≻ 0`, `2 ≻ 0 ≻ 1`. -/
def condorcetProfile : Profile (Fin 3) (Fin 3) :=
  ![ofScore ![2, 1, 0] (by decide), ofScore ![0, 2, 1] (by decide),
    ofScore ![1, 0, 2] (by decide)]

/-- Pairwise majority cycles `0 ≻ 1 ≻ 2 ≻ 0` on `condorcetProfile`. -/
theorem condorcetProfile_cycle :
    MajorityPrefers condorcetProfile 0 1 ∧
      MajorityPrefers condorcetProfile 1 2 ∧
      MajorityPrefers condorcetProfile 2 0 := by
  unfold MajorityPrefers condorcetProfile
  simp only [support_ofScore3]
  decide

/-- No candidate is a Condorcet winner of `condorcetProfile`. -/
theorem condorcetProfile_no_winner (a : Fin 3) : ¬ IsCondorcetWinner condorcetProfile a := by
  obtain ⟨h01, h12, h20⟩ := condorcetProfile_cycle
  intro ha
  fin_cases a
  · exact h20.asymm (ha 2 (by decide))
  · exact h01.asymm (ha 0 (by decide))
  · exact h12.asymm (ha 1 (by decide))

/-- General Condorcet cycle theorem instantiated on five voters and three alternatives, and
absence of a Condorcet winner on four voters and three alternatives. -/
example : (∃ P : Profile (Fin 5) (Fin 3),
    MajorityPrefers P 0 1 ∧ MajorityPrefers P 1 2 ∧ MajorityPrefers P 2 0) ∧
    (∃ Q : Profile (Fin 4) (Fin 3), ∀ x, ¬ IsCondorcetWinner Q x) :=
  ⟨exists_condorcetCycle (by simp) (by simp) (by decide) (by decide) (by decide),
    exists_profile_forall_not_isCondorcetWinner (by simp) ⟨0, 1, 2, by decide, by decide,
      by decide⟩⟩

end CondorcetParadox

/-! ### Plurality manipulation & Condorcet boundary (NRTV §9.2.2, pp. 211–212) -/

section Plurality

/-- Tie-breaking order `2 ≻ 1 ≻ 0`. -/
def tieBreak : Ranking (Fin 3) := ofScore ![0, 1, 2] (by decide)

/-- Truthful three-voter profile:
voter `0` ranks `0 ≻ 1 ≻ 2`, voter `1` ranks `1 ≻ 2 ≻ 0`, voter `2` ranks `2 ≻ 1 ≻ 0`. -/
def pluralityTruth : Profile (Fin 3) (Fin 3) :=
  ![ofScore ![2, 1, 0] (by decide), ofScore ![0, 2, 1] (by decide),
    ofScore ![0, 1, 2] (by decide)]

/-- Misreport profile in which voter `0` strategically votes for `1` (`1 ≻ 0 ≻ 2`). -/
def pluralityLie : Profile (Fin 3) (Fin 3) :=
  ![ofScore ![1, 2, 0] (by decide), ofScore ![0, 2, 1] (by decide),
    ofScore ![0, 1, 2] (by decide)]

/-- Candidate `1` is the strict Condorcet winner of `pluralityTruth` (beating both `0` and `2` by
2 votes to 1). -/
theorem isCondorcetWinner_pluralityTruth : IsCondorcetWinner pluralityTruth 1 := by
  intro b hb
  unfold MajorityPrefers pluralityTruth
  fin_cases b
  · simp only [support_ofScore3]; decide
  · exact absurd rfl hb
  · simp only [support_ofScore3]; decide

/-- Under truthful voting, each candidate gets one first-place vote and `tieBreak` elects `2`. -/
theorem plurality_pluralityTruth :
    SocialChoiceFunction.plurality tieBreak pluralityTruth = 2 := by
  refine SocialChoiceFunction.plurality_eq_of_isTop tieBreak fun x hx => ?_
  rw [pluralityRanking_prefers]
  unfold pluralityTruth tieBreak
  fin_cases x
  · simp only [pluralityCount_ofScore3, ofScore_prefers]; decide
  · simp only [pluralityCount_ofScore3, ofScore_prefers]; decide
  · exact absurd rfl hx

/-- When voter `0` strategically votes for `1`, candidate `1` wins outright with two votes. -/
theorem plurality_pluralityLie :
    SocialChoiceFunction.plurality tieBreak pluralityLie = 1 := by
  refine SocialChoiceFunction.plurality_eq_of_isTop tieBreak fun x hx => ?_
  rw [pluralityRanking_prefers]
  unfold pluralityLie tieBreak
  fin_cases x
  · simp only [pluralityCount_ofScore3, ofScore_prefers]; decide
  · exact absurd rfl hx
  · simp only [pluralityCount_ofScore3, ofScore_prefers]; decide

/-- Explicit three-voter witness that `plurality tieBreak` fails both Condorcet consistency and
strategy-proofness ([Nisan2007], §9.2.2, pp. 211–212). -/
theorem plurality_witness_not_consistent_and_manipulable :
    ¬ (SocialChoiceFunction.plurality (V := Fin 3) tieBreak).IsCondorcetConsistent ∧
      ¬ (SocialChoiceFunction.plurality (V := Fin 3) tieBreak).IsStrategyProof := by
  refine ⟨fun hcc => ?_, fun hsp => ?_⟩
  · have h := hcc pluralityTruth 1 isCondorcetWinner_pluralityTruth
    rw [plurality_pluralityTruth] at h
    exact absurd h (by decide)
  · refine hsp pluralityTruth pluralityLie 0 (fun j hj => ?_) ?_
    · fin_cases j
      · exact absurd rfl hj
      · rfl
      · rfl
    · rw [plurality_pluralityTruth, plurality_pluralityLie]
      change (![2, 1, 0] : Fin 3 → ℕ) 2 < (![2, 1, 0] : Fin 3 → ℕ) 1
      decide

/-- **Sharpness of `|V| ≠ 4` in `not_isCondorcetConsistent_plurality`:** with four voters and three
alternatives, every Condorcet winner beats each of its two rivals by at least 3-to-1, so each rival
has at most one first-place vote while the Condorcet winner has at least two. -/
theorem plurality_fin4_fin3_isCondorcetConsistent (t : Ranking (Fin 3)) :
    (SocialChoiceFunction.plurality (V := Fin 4) t).IsCondorcetConsistent := by
  classical
  intro P w hw
  have hle_supp : ∀ x : Fin 3, x ≠ w → pluralityCount P x ≤ 1 := by
    intro x hxw
    have hmaj : 4 < 2 * support P w x := by
      have := (majorityPrefers_iff_card_lt_two_mul hxw.symm).1 (hw x hxw)
      simpa only [Fintype.card_fin] using this
    have hsum : support P w x + support P x w = 4 := by
      simpa only [Fintype.card_fin] using support_add_support P hxw.symm
    have htop_le : pluralityCount P x ≤ support P x w :=
      Finset.card_le_card fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact hi w hxw.symm
    omega
  have htot : pluralityCount P 0 + pluralityCount P 1 + pluralityCount P 2 = 4 := by
    have h := sum_pluralityCount P
    rw [Fin.sum_univ_three, Fintype.card_fin] at h
    omega
  refine SocialChoiceFunction.plurality_eq_of_isTop t fun x hxw => ?_
  rw [pluralityRanking_prefers]
  left
  have hfin3 : ∀ z : Fin 3, z = 0 ∨ z = 1 ∨ z = 2 := by decide
  rcases hfin3 w with rfl | rfl | rfl <;> rcases hfin3 x with rfl | rfl | rfl
  · exact absurd rfl hxw
  · have := hle_supp 1 (by decide); have := hle_supp 2 (by decide); omega
  · have := hle_supp 1 (by decide); have := hle_supp 2 (by decide); omega
  · have := hle_supp 0 (by decide); have := hle_supp 2 (by decide); omega
  · exact absurd rfl hxw
  · have := hle_supp 0 (by decide); have := hle_supp 2 (by decide); omega
  · have := hle_supp 0 (by decide); have := hle_supp 1 (by decide); omega
  · have := hle_supp 0 (by decide); have := hle_supp 1 (by decide); omega
  · exact absurd rfl hxw

end Plurality

/-! ### May's theorem and independence of May's three axioms -/

section MayAxioms

/-- The strict ranking `true ≻ false` on `Bool`. -/
def trueAbove : Ranking Bool where
  Prefers a b := a = true ∧ b = false
  irrefl a h := by cases a <;> simp_all
  trans _ _ _ h1 h2 := ⟨h1.1, h2.2⟩
  total a b h := by cases a <;> cases b <;> simp_all

@[simp] theorem trueAbove_prefers {a b : Bool} :
    trueAbove.Prefers a b ↔ a = true ∧ b = false := Iff.rfl

/-- Universal indifference on `Bool`. -/
def boolIndiff : WeakRanking Bool where
  AtLeast _ _ := True
  total _ _ := Or.inl trivial
  trans _ _ _ _ _ := trivial

/-- Permuting voters preserves `support`. -/
theorem support_comp_perm {V : Type*} [Fintype V] (σ : Equiv.Perm V) (P : Profile V Bool)
    (x y : Bool) : support (P ∘ σ) x y = support P x y := by
  classical
  unfold support
  let emb : V ↪ V := σ.toEmbedding
  have hset : (Finset.univ.filter fun i => (P i).Prefers x y) =
      (Finset.univ.filter fun i => (P (σ i)).Prefers x y).map emb := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    exact ⟨fun hj => ⟨σ.symm j, by simpa only [Equiv.apply_symm_apply] using hj,
      σ.apply_symm_apply j⟩, by rintro ⟨i, hi, rfl⟩; exact hi⟩
  simpa only [Function.comp_apply, hset] using (Finset.card_map emb).symm

/-- May's theorem on `Bool` for both strict and weak profiles, including even electorates. -/
example (F : SocialWelfareFunction (Fin 4) Bool) :
    F.IsAnonymous ∧ F.IsNeutral ∧ F.IsPositivelyResponsive ↔
      F = SocialWelfareFunction.twoAltMajority (eq_or_eq_of_card_le_two (by simp)) :=
  SocialWelfareFunction.isAnonymous_and_isNeutral_and_isPositivelyResponsive_iff (by simp)

example (G : WeakSocialWelfareFunction (Fin 3) Bool) :
    G.IsAnonymous ∧ G.IsNeutral ∧ G.IsPositivelyResponsive ↔
      G = WeakSocialWelfareFunction.twoAltMajority (eq_or_eq_of_card_le_two (by simp)) :=
  WeakSocialWelfareFunction.isAnonymous_and_isNeutral_and_isPositivelyResponsive_iff (by simp)

/-- Concrete weak-profile evaluation: one voter prefers `true` to `false` and two voters are
indifferent, so weak-profile majority strictly prefers `true` to `false`. -/
example : (WeakSocialWelfareFunction.twoAltMajority
    (eq_or_eq_of_card_le_two (A := Bool) (by simp))
    (fun i : Fin 3 => if i = 0 then trueAbove.toWeakRanking else boolIndiff)).Prefers
      true false := by
  classical
  let P : WeakProfile (Fin 3) Bool :=
    fun i => if i = 0 then trueAbove.toWeakRanking else boolIndiff
  intro hft
  have hle : weakSupport P true false ≤ weakSupport P false true :=
    (show false = true ∨ _ from hft).resolve_left (by decide)
  have h1 : weakSupport P true false = 1 := by
    unfold weakSupport
    rw [Finset.card_eq_one]
    refine ⟨0, Finset.ext fun i => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    by_cases hi : i = 0
    · simp only [P, hi, ite_true, Ranking.toWeakRanking_prefers, trueAbove_prefers, and_self]
    · simp only [P, hi, ite_false, iff_false]
      exact fun h => h trivial
  have h2 : weakSupport P false true = 0 := by
    unfold weakSupport
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _
    by_cases hi : i = 0
    · simp only [P, hi, ite_true, Ranking.toWeakRanking_prefers, trueAbove_prefers]
      exact fun ⟨h, _⟩ => Bool.false_ne_true h
    · simp only [P, hi, ite_false]
      exact fun h => h trivial
  omega

/-- 1. **Dropping anonymity:** `dictatorship 0` on `(Fin 3, Bool)` is neutral and positively
responsive, but not anonymous. -/
example : (SocialWelfareFunction.dictatorship (V := Fin 3) (A := Bool) 0).IsNeutral ∧
    (SocialWelfareFunction.dictatorship (V := Fin 3) (A := Bool) 0).IsPositivelyResponsive ∧
    ¬ (SocialWelfareFunction.dictatorship (V := Fin 3) (A := Bool) 0).IsAnonymous := by
  refine ⟨fun e P => ?_, fun P Q a b i hPQ hnP hQ hFP => ?_, fun hanon => ?_⟩
  · ext a b
    simp only [SocialWelfareFunction.dictatorship, WeakRanking.relabel_atLeast,
      Ranking.toWeakRanking_atLeast, Ranking.relabel_prefers, e.symm.injective.eq_iff]
  · rw [SocialWelfareFunction.dictatorship, Ranking.toWeakRanking_prefers]
    by_cases hi : i = 0
    · subst hi; exact hQ
    · rw [← hPQ 0 (Ne.symm hi)]
      exact (show a = b ∨ (P 0).Prefers a b from hFP).resolve_left ((Q i).ne_of_prefers hQ)
  · let P : Profile (Fin 3) Bool := fun i => if i = 0 then trueAbove else trueAbove.reverse
    have h : (SocialWelfareFunction.dictatorship 0 (P ∘ Equiv.swap 0 1)).AtLeast true false ↔
        (SocialWelfareFunction.dictatorship 0 P).AtLeast true false := by
      rw [hanon (Equiv.swap 0 1) P]
    have hR : (SocialWelfareFunction.dictatorship 0 P).AtLeast true false :=
      Or.inr (by simp only [P, ite_true, trueAbove_prefers, and_self])
    have hL : true = false ∨ (P 1).Prefers true false := by
      simpa only [SocialWelfareFunction.dictatorship, Function.comp_apply,
        Equiv.swap_apply_left, Ranking.toWeakRanking_atLeast] using h.2 hR
    have h1ne0 : (1 : Fin 3) ≠ 0 := by decide
    simp only [P, h1ne0, ite_false, Ranking.reverse_prefers, trueAbove_prefers] at hL
    rcases hL with htf | ⟨hft, -⟩
    · exact Bool.false_ne_true htf.symm
    · exact Bool.false_ne_true hft

/-- 2. **Dropping neutrality:** tie-broken majority on `(Fin 2, Bool)` favouring `true` on 1-1 ties
is anonymous and positively responsive, but not neutral. -/
noncomputable def biasedMajority : SocialWelfareFunction (Fin 2) Bool := fun P =>
  { AtLeast := fun a b => a = b ∨ (a = true ∧ 1 ≤ support P true false) ∨ 2 ≤ support P a b
    total := fun a b => by
      by_cases hab : a = b
      · exact Or.inl (Or.inl hab)
      have hsum : support P true false + support P false true = 2 := by
        simpa only [Fintype.card_fin] using support_add_support P (a := true) (b := false)
          (by decide)
      cases a <;> cases b
      · exact absurd rfl hab
      · by_cases h1 : 1 ≤ support P true false
        · exact Or.inr (Or.inr (Or.inl ⟨rfl, h1⟩))
        · exact Or.inl (Or.inr (Or.inr (by omega)))
      · by_cases h1 : 1 ≤ support P true false
        · exact Or.inl (Or.inr (Or.inl ⟨rfl, h1⟩))
        · exact Or.inr (Or.inr (Or.inr (by omega)))
      · exact absurd rfl hab
    trans := fun a b c hab hbc => by
      by_cases h1 : a = b
      · subst h1; exact hbc
      by_cases h2 : b = c
      · subst h2; exact hab
      exact Or.inl (by revert h1 h2; cases a <;> cases b <;> cases c <;> simp) }

example : biasedMajority.IsAnonymous ∧ biasedMajority.IsPositivelyResponsive ∧
    ¬ biasedMajority.IsNeutral := by
  refine ⟨fun σ P => ?_, fun P Q a b i hPQ hnP hQ hFP hFQ => ?_, fun hneut => ?_⟩
  · ext a b
    change (a = b ∨ (a = true ∧ 1 ≤ support (P ∘ σ) true false) ∨ 2 ≤ support (P ∘ σ) a b) ↔
      (a = b ∨ (a = true ∧ 1 ≤ support P true false) ∨ 2 ≤ support P a b)
    rw [support_comp_perm σ P true false, support_comp_perm σ P a b]
  · classical
    have hab : a ≠ b := (Q i).ne_of_prefers hQ
    have hsumP : support P a b + support P b a = 2 := by
      simpa only [Fintype.card_fin] using support_add_support P hab
    have hsumQ : support Q a b + support Q b a = 2 := by
      simpa only [Fintype.card_fin] using support_add_support Q hab
    have hinc : support Q a b = support P a b + 1 := by
      unfold support
      rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_two, Fin.sum_univ_two]
      have hfin2 : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
      rcases hfin2 i with rfl | rfl
      · have h1 := hPQ 1 (by decide)
        simp only [← h1, hnP, hQ, ite_false, ite_true]
        omega
      · have h0 := hPQ 0 (by decide)
        simp only [← h0, hnP, hQ, ite_false, ite_true]
    change b = a ∨ (b = true ∧ 1 ≤ support Q true false) ∨ 2 ≤ support Q b a at hFQ
    cases a <;> cases b
    · exact hab rfl
    · rcases show false = true ∨ (false = true ∧ 1 ≤ support P true false) ∨
          2 ≤ support P false true from hFP with h | ⟨h, -⟩ | h2
      · exact Bool.false_ne_true h
      · exact Bool.false_ne_true h
      · omega
    · rcases hFQ with h | ⟨h, -⟩ | h2
      · exact Bool.false_ne_true h
      · exact Bool.false_ne_true h
      · omega
    · exact hab rfl
  · let P : Profile (Fin 2) Bool := fun i => if i = 0 then trueAbove else trueAbove.reverse
    have h : (biasedMajority fun i => (P i).relabel (Equiv.swap true false)).AtLeast false true ↔
        ((biasedMajority P).relabel (Equiv.swap true false)).AtLeast false true := by
      rw [hneut (Equiv.swap true false) P]
    have h1ne0 : (1 : Fin 2) ≠ 0 := by decide
    have hsupp1 : support (fun i => (P i).relabel (Equiv.swap true false)) false true = 1 := by
      classical
      unfold support
      rw [Finset.card_eq_one]
      refine ⟨0, Finset.ext fun i => ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        Ranking.relabel_prefers, Equiv.symm_swap, Equiv.swap_apply_right, Equiv.swap_apply_left]
      by_cases hi : i = 0
      · simp only [P, hi, ite_true, trueAbove_prefers, and_self]
      · simp only [P, hi, ite_false, Ranking.reverse_prefers, trueAbove_prefers, iff_false]
        exact fun ⟨hft, _⟩ => Bool.false_ne_true hft
    have hsupp2 : support P true false = 1 := by
      classical
      unfold support
      rw [Finset.card_eq_one]
      refine ⟨0, Finset.ext fun i => ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      by_cases hi : i = 0
      · simp only [P, hi, ite_true, trueAbove_prefers, and_self]
      · simp only [P, hi, ite_false, Ranking.reverse_prefers, trueAbove_prefers, iff_false]
        exact fun ⟨hft, _⟩ => Bool.false_ne_true hft
    have hR : ((biasedMajority P).relabel (Equiv.swap true false)).AtLeast false true := by
      rw [WeakRanking.relabel_atLeast, Equiv.symm_swap, Equiv.swap_apply_right,
        Equiv.swap_apply_left]
      exact Or.inr (Or.inl ⟨rfl, by omega⟩)
    rcases show false = true ∨ (false = true ∧ _) ∨
        2 ≤ support (fun i => (P i).relabel (Equiv.swap true false)) false true from h.2 hR
      with hft | ⟨hft, -⟩ | h2
    · exact Bool.false_ne_true hft
    · exact Bool.false_ne_true hft
    · omega

/-- 3. **Dropping positive responsiveness:** unanimity rule on `(Fin 3, Bool)` (strict social
preference only on 3-0 unanimity, social tie otherwise) is anonymous and neutral, but not
positively responsive. -/
noncomputable def unanimityBool : SocialWelfareFunction (Fin 3) Bool := fun P =>
  { AtLeast := fun a b => a = b ∨ support P b a < 3
    total := fun a b => by
      by_cases hab : a = b
      · exact Or.inl (Or.inl hab)
      have hsum : support P a b + support P b a = 3 := by
        simpa only [Fintype.card_fin] using support_add_support P hab
      omega
    trans := fun a b c hab hbc => by
      by_cases h1 : a = b
      · subst h1; exact hbc
      by_cases h2 : b = c
      · subst h2; exact hab
      exact Or.inl (by revert h1 h2; cases a <;> cases b <;> cases c <;> simp) }

example : unanimityBool.IsAnonymous ∧ unanimityBool.IsNeutral ∧
    ¬ unanimityBool.IsPositivelyResponsive := by
  refine ⟨fun σ P => ?_, fun e P => ?_, fun hpr => ?_⟩
  · ext a b
    change (a = b ∨ support (P ∘ σ) b a < 3) ↔ (a = b ∨ support P b a < 3)
    rw [support_comp_perm σ P b a]
  · ext a b
    have hsupp : support (fun i => (P i).relabel e) b a = support P (e.symm b) (e.symm a) := by
      classical
      unfold support
      congr 1
      ext i
      simp only [Finset.mem_filter, Ranking.relabel_prefers]
    rw [WeakRanking.relabel_atLeast]
    change (a = b ∨ support (fun i => (P i).relabel e) b a < 3) ↔
      (e.symm a = e.symm b ∨ support P (e.symm b) (e.symm a) < 3)
    rw [hsupp, e.symm.injective.eq_iff]
  · let P : Profile (Fin 3) Bool := fun i => if i = 0 then trueAbove else trueAbove.reverse
    let Q : Profile (Fin 3) Bool := fun i => if i = 2 then trueAbove.reverse else trueAbove
    have hP_ft : support P false true < 3 := by
      have hsum : support P true false + support P false true = 3 := by
        simpa only [Fintype.card_fin] using
          support_add_support P (a := true) (b := false) (by decide)
      have hpos : 0 < support P true false := by
        classical
        unfold support
        refine Finset.card_pos.2 ⟨0, Finset.mem_filter.2 ⟨Finset.mem_univ 0, ?_⟩⟩
        simp only [P, ite_true, trueAbove_prefers, and_self]
      omega
    have hQ_tf : support Q true false < 3 := by
      have hsum : support Q true false + support Q false true = 3 := by
        simpa only [Fintype.card_fin] using
          support_add_support Q (a := true) (b := false) (by decide)
      have hpos : 0 < support Q false true := by
        classical
        unfold support
        refine Finset.card_pos.2 ⟨2, Finset.mem_filter.2 ⟨Finset.mem_univ 2, ?_⟩⟩
        simp only [Q, ite_true, Ranking.reverse_prefers, trueAbove_prefers, and_self]
      omega
    have h1ne0 : (1 : Fin 3) ≠ 0 := by decide
    have h1ne2 : (1 : Fin 3) ≠ 2 := by decide
    have hnP1 : ¬ (P 1).Prefers true false := by
      simp only [P, h1ne0, ite_false, Ranking.reverse_prefers, trueAbove_prefers]
      exact fun ⟨hft, _⟩ => Bool.false_ne_true hft
    have hQ1 : (Q 1).Prefers true false := by
      simp only [Q, h1ne2, ite_false, trueAbove_prefers, and_self]
    have hPrefQ := hpr P Q true false 1 (fun j hj => by
      fin_cases j
      · rfl
      · exact absurd rfl hj
      · rfl) hnP1 hQ1 (Or.inr hP_ft)
    exact hPrefQ (Or.inr hQ_tf)

end MayAxioms

/-! ### Weak-order Arrow, serial dictatorship, and Fishburn's ultrafilter -/

/-- Weak-order Arrow's theorem on `(Fin 3, Fin 3)`: every weakly Pareto, IIA rule on weak
individual rankings has a unique dictator. -/
example (G : WeakSocialWelfareFunction (Fin 3) (Fin 3)) (hP : G.IsPareto) (hI : G.IsIIA) :
    ∃! i, G.IsDictator i :=
  WeakSocialWelfareFunction.existsUnique_isDictator_of_isPareto_of_isIIA hP hI
    ⟨0, 1, 2, by decide, by decide, by decide⟩

/-- Serial dictatorship on `(Fin 2, Fin 3)` satisfies weak Pareto, IIA, and `IsDictator 0`, yet
differs from `WeakSocialWelfareFunction.dictatorship 0`. -/
example : (WeakSocialWelfareFunction.serialDictatorship (V := Fin 2) (A := Fin 3) 0 1).IsPareto ∧
    (WeakSocialWelfareFunction.serialDictatorship (V := Fin 2) (A := Fin 3) 0 1).IsIIA ∧
    (WeakSocialWelfareFunction.serialDictatorship (V := Fin 2) (A := Fin 3) 0 1).IsDictator 0 ∧
    WeakSocialWelfareFunction.serialDictatorship (V := Fin 2) (A := Fin 3) 0 1 ≠
      WeakSocialWelfareFunction.dictatorship 0 :=
  ⟨WeakSocialWelfareFunction.isPareto_serialDictatorship 0 1,
    WeakSocialWelfareFunction.isIIA_serialDictatorship 0 1,
    WeakSocialWelfareFunction.isDictator_serialDictatorship 0 1,
    WeakSocialWelfareFunction.serialDictatorship_ne_dictatorship (by decide)⟩

/-- Fishburn's infinite-electorate theorem instantiated on `ℕ` voters and `Fin 3` alternatives:
weak Pareto and IIA admit a non-dictatorial social welfare function. -/
example : ∃ F : SocialWelfareFunction ℕ (Fin 3),
    F.IsPareto ∧ F.IsIIA ∧ ¬ F.IsDictatorial :=
  SocialWelfareFunction.exists_isPareto_and_isIIA_and_not_isDictatorial

end CslibFrontierTests.GameTheory.MayAndWeakArrow
