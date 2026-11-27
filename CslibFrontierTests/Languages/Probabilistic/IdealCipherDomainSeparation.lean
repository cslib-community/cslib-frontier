/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Languages.Probabilistic.IdealCipher.DomainSeparation
public import CslibFrontier.Crypto.Game.CloseTo

/-!
# Tests for the Domain Separation Lemma

Exercises `CslibFrontier/Languages/Probabilistic/IdealCipher/DomainSeparation.lean`:
* Theorem 4.15 in the source's form, a bound on the distinguishing advantage of a bit output;
* for injective `f` the failure probability is `0`, and so is the advantage;
* the bookkeeping of Experiment 1: a query's input and its answer go into opposite sets;
* a two-query adversary on two keys with the same image, for which the failure probability is `1`
  and the advantage is `1 / 2`, so the failure probability cannot be dropped from the bound.
-/

open Cslib Cslib.IdealCipher Cslib.RandomPermutation Cslib.Probability Cslib.Crypto
open scoped ENNReal

public section

namespace CslibFrontierTests.IdealCipherDomainSeparation

section General

variable {U V X α : Type} [DecidableEq U] [Fintype U] [Fintype V]
  [DecidableEq X] [Fintype X] [Nonempty X]

/-- Theorem 4.15 as the source states it: the distinguishing advantage `|Pr[W₀] - Pr[W₁]|` of an
adversary that outputs a bit is at most the failure probability `Pr[Z]`. -/
example (f : U → V) (A : ProbOracleComp (IdealCipher.Spec U X) Bool) :
    (Game.advantage (coalescedExperiment f A) ((splitExperiment A).map Prod.fst) : ℝ≥0∞) ≤
      (splitExperiment A).toOuterMeasure {x | DomainOverlap f x.2} :=
  Game.closeTo_iff_coe_advantage_le.mp (coalescedExperiment_closeTo_splitExperiment f A)

omit [Fintype V] [Nonempty X] in
/-- For injective `f` no two distinct keys share an image, so `Z` has probability `0`. -/
theorem failureProb_eq_zero_of_injective {f : U → V} (hf : Function.Injective f)
    (A : ProbOracleComp (IdealCipher.Spec U X) α) :
    (splitExperiment A).toOuterMeasure {x | DomainOverlap f x.2} = 0 := by
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  rintro ⟨_, dom⟩ _ ⟨μ, μ', hne, hfeq, _⟩
  exact hne (hf hfeq)

/-- For injective `f` the two experiments cannot be told apart. -/
example {f : U → V} (hf : Function.Injective f) (A : ProbOracleComp (IdealCipher.Spec U X) Bool) :
    Game.advantage (coalescedExperiment f A) ((splitExperiment A).map Prod.fst) = 0 := by
  have h := Game.closeTo_iff_coe_advantage_le.mp (coalescedExperiment_closeTo_splitExperiment f A)
  rw [failureProb_eq_zero_of_injective hf] at h
  exact_mod_cast nonpos_iff_eq_zero.mp h

/-- A forward query `(μ, +1, x)` answered with `a` adds `x` to `Dom_μ^(+1)` and `a` to
`Dom_μ^(-1)`. -/
example (dom : QueryDomains U X) (μ : U) (x a : X) :
    recordQueryDomain dom (μ, .forward x) a μ = (insert x (dom μ).1, insert a (dom μ).2) := by
  simp [recordQueryDomain]

/-- An inverse query `(μ, -1, y)` answered with `a` adds `y` to `Dom_μ^(-1)` and `a` to
`Dom_μ^(+1)`. -/
example (dom : QueryDomains U X) (μ : U) (y a : X) :
    recordQueryDomain dom (μ, .inverse y) a μ = (insert a (dom μ).1, insert y (dom μ).2) := by
  simp [recordQueryDomain]

end General

section TwoKeys

/-- Two keys `false` and `true` with the same image under `fun _ => ()`, one block `true` queried
forward under each key; the adversary outputs whether the two answers agree. -/
noncomputable def twoKeyCollidingAdversary :
    ProbOracleComp (IdealCipher.Spec Bool Bool) Bool := do
  let y₁ ← ProbOracleComp.query (false, PermQuery.forward true)
  let y₂ ← ProbOracleComp.query (true, PermQuery.forward true)
  return (y₁ == y₂)

/-- Both keys query the block `true`, so `Z` happens with probability `1`. -/
example : (splitExperiment twoKeyCollidingAdversary).toOuterMeasure
    {x | DomainOverlap (fun _ : Bool => ()) x.2} = 1 := by
  have hsup : ∀ x ∈ (splitExperiment twoKeyCollidingAdversary).support,
      x ∈ {x : Bool × QueryDomains Bool Bool | DomainOverlap (fun _ : Bool => ()) x.2} := by
    rintro ⟨b, dom⟩ hmem
    dsimp only [splitExperiment, twoKeyCollidingAdversary] at hmem
    simp only [Probability.PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hmem
    obtain ⟨πFam, _, hrun⟩ := hmem
    simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
      ProbOracleComp.runWith_pure, splitPermStep, recordQueryDomain, PermQuery.toCacheEntry,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hrun
    obtain ⟨⟨y₁, d₁⟩, h1, ⟨y₂, d₂⟩, h2, h3⟩ := hrun
    cases h1; cases h2; cases h3
    refine ⟨false, true, Bool.false_ne_true, rfl, Or.inl ⟨true, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩⟩ <;>
      simp
  rw [PMF.toOuterMeasure_apply, ← (splitExperiment twoKeyCollidingAdversary).tsum_coe]
  refine tsum_congr fun x => ?_
  by_cases hmem : x ∈ (splitExperiment twoKeyCollidingAdversary).support
  · simp [Set.indicator, hsup x hmem]
  · have hzero : splitExperiment twoKeyCollidingAdversary x = 0 := by
      simpa [PMF.mem_support_iff] using hmem
    simp [Set.indicator, hzero]

/-- In the coalesced experiment both keys use one permutation, so the answers always agree. -/
theorem coalescedExperiment_twoKeyCollidingAdversary :
    coalescedExperiment (fun _ : Bool => ()) twoKeyCollidingAdversary true = 1 := by
  simp only [coalescedExperiment, twoKeyCollidingAdversary, ProbOracleComp.query,
    OracleComp.evalWith_bind, OracleComp.evalWith_query, OracleComp.evalWith_pure,
    OracleComp.sumHandler, Probability.PMF.monad_bind_eq_bind,
    PMF.pure_bind, beq_self_eq_true, PMF.bind_const, PMF.pure_apply, ↓reduceIte]

/-- In the split experiment the two keys use independent permutations of `Bool`, so the answers
agree with probability `1 / 2`. -/
theorem splitExperiment_twoKeyCollidingAdversary :
    ((splitExperiment twoKeyCollidingAdversary).map Prod.fst) true = 1 / 2 := by
  simp only [splitExperiment, twoKeyCollidingAdversary, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure, splitPermStep,
    Probability.PMF.monad_bind_eq_bind, PMF.map_bind, PMF.pure_bind, PMF.pure_map]
  rw [PMF.bind_apply, tsum_fintype]
  have hcard : Fintype.card (Equiv.Perm Bool) = 2 := by decide
  have hpi (πFam : Bool → Equiv.Perm Bool) :
      (PMF.pi (fun _ : Bool => PMF.uniformOfFintype (Equiv.Perm Bool))) πFam =
        (1 / 4 : ℝ≥0∞) := by
    rw [PMF.pi_apply]
    simp only [PMF.uniformOfFintype_apply, hcard, Finset.prod_const, Finset.card_univ,
      Fintype.card_bool]
    rw [← ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)]
    simp
    norm_num
  simp_rw [hpi, PMF.pure_apply]
  have heqv := Fintype.sum_equiv (Equiv.boolArrowEquivProd (Equiv.Perm Bool))
    (fun πFam => (1 / 4 : ℝ≥0∞) *
      if true = (evalPerm (πFam false) (PermQuery.forward true) ==
        evalPerm (πFam true) (PermQuery.forward true)) then 1 else 0)
    (fun p => (1 / 4 : ℝ≥0∞) *
      if true = (p.1 true == p.2 true) then 1 else 0)
    (fun πFam => rfl)
  refine Eq.trans ?_ (heqv.trans ?_)
  · congr 1; funext x; congr 1; convert rfl
  · rw [Fintype.sum_prod_type]
    have huniv : (Finset.univ : Finset (Equiv.Perm Bool)) = {1, Equiv.swap false true} := by
      ext π
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      rcases eq_or_ne (π true) true with h | h
      · left; ext b; cases b
        · by_contra hb
          have hfalse : π false = true := by cases h' : π false <;> simp_all
          exact Bool.false_ne_true (π.injective (hfalse.trans h.symm))
        · exact h
      · right; ext b; cases b
        · have hfalse : π false = true := by
            by_contra hb
            have hf : π false = false := Bool.eq_false_iff.mpr hb
            have ht : π true = false := Bool.eq_false_iff.mpr h
            exact Bool.false_ne_true (π.injective (hf.trans ht.symm))
          simp [hfalse]
        · exact (Bool.eq_false_iff.mpr h).trans (by simp)
    have hne_perm : (1 : Equiv.Perm Bool) ≠ Equiv.swap false true := by
      intro h
      have h' := Equiv.congr_fun h true
      simp at h'
    rw [huniv]
    simp only [Finset.sum_pair hne_perm, Equiv.Perm.coe_one, id_eq, Equiv.swap_apply_right,
      beq_self_eq_true, ↓reduceIte, mul_one]
    norm_num
    rw [← ENNReal.toReal_eq_toReal_iff' (by simp) (by simp),
      ENNReal.toReal_add (by simp) (by simp)]
    simp
    norm_num

/-- The two-key adversary has advantage `1 / 2` although `f` collapses only two keys, so the
bound of Theorem 4.15 is not `0`. -/
example : (Game.advantage (coalescedExperiment (fun _ : Bool => ()) twoKeyCollidingAdversary)
    ((splitExperiment twoKeyCollidingAdversary).map Prod.fst) : ℝ) = 1 / 2 := by
  rw [Game.coe_advantage]
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal,
    coalescedExperiment_twoKeyCollidingAdversary, splitExperiment_twoKeyCollidingAdversary]
  norm_num [ENNReal.toReal_div]

end TwoKeys

end CslibFrontierTests.IdealCipherDomainSeparation

end
