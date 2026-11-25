/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.CramerShoup.ProjectiveHash
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.Oracle.Run

import CslibFrontier.Languages.Probabilistic.QueryCount.Congr
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.Uniform.Translate

/-!
# Standalone security games for universal and $\text{universal}_2$ projective hash functions

Formalizes Attack Games 12.4 and 12.5, Lemmas 12.6 and 12.8 ([BonehShoup2023], Sections
12.5.1–12.5.2, printed pp. 486 and 488), in the adaptive three-stage form of Exercise 12.26(a)–(b)
(printed p. 521).

Nothing else on `main` uses these standalone games: the Cramer–Shoup security proof in
`CslibFrontier/Crypto/Computational/CramerShoup/Scheme.lean` keeps its direct proofs for the two
hybrid hops from `uniform_projHash_fiber_add` and `uniform_projHash2_fiber_any_le`.

## Differences from printed statements

* Returning `pure (v, w, st₁)` (or `pure (v, w, ρ, st₁)`) from `chooseChallenge` with `(v, w)`
  (or `(v, w, ρ)`) independent of `h` (or `(h₁, h₂)`) recovers the non-adaptive Attack Games 12.4
  and 12.5; the output state `st₁` may still carry `h` (or `(h₁, h₂)`) to `guess`.
* `ProbOracleComp.QueriesSatisfy` constrains evaluation queries in `L_u` along every execution
  path of `chooseChallenge` and `guess` regardless of oracle replies, whereas the book constrains
  queries made along an execution of the game.
* `Universal2GuessAdversary.Admissible` omits the printed `(v, w) ∉ L_u` requirement on the
  challenge pair in Attack Game 12.5 / Exercise 12.26(b), because the `Q / q` bound holds uniformly
  even when `(v, w) ∈ L_u`.
* Both bounds are information-theoretic and hold for computationally unbounded admissible
  adversaries without efficiency hypotheses.

## Main definitions

* `Cslib.Crypto.ProjectiveHash.UniversalEvalSpec`,
  `Cslib.Crypto.ProjectiveHash.UniversalDistAdversary`,
  `Cslib.Crypto.ProjectiveHash.UniversalDistAdversary.Admissible`,
  `Cslib.Crypto.ProjectiveHash.universalDistExperiment`: oracle interface, three-stage adversary,
  admissibility predicate, and distinguishing experiments for Attack Game 12.4 / Exercise 12.26(a).
* `Cslib.Crypto.ProjectiveHash.Universal2EvalSpec`,
  `Cslib.Crypto.ProjectiveHash.universal2Wins`,
  `Cslib.Crypto.ProjectiveHash.Universal2GuessAdversary`,
  `Cslib.Crypto.ProjectiveHash.Universal2GuessAdversary.Admissible`,
  `Cslib.Crypto.ProjectiveHash.universal2GuessGame`: oracle interface, winning predicate,
  three-stage adversary, admissibility with `Q`-tuple output bound, and guessing game for Attack
  Game 12.5 / Exercise 12.26(b).

## Main results

* `Cslib.Crypto.ProjectiveHash.universalDistExperiment_false_eq_true`: Lemma 12.6 / Exercise
  12.26(a) (`universalDistExperiment F d A false = universalDistExperiment F d A true`).
* `Cslib.Crypto.ProjectiveHash.succProbability_universal2GuessGame_le`: Lemma 12.8 / Exercise
  12.26(b) (`Game.succProbability (universal2GuessGame F d A) ≤ Q / F.order d`).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 12.5.1–12.5.2 (printed pp. 484–488) and Exercise 12.26
  (printed p. 521).
-/

public section

namespace Cslib.Crypto.ProjectiveHash

open Probability
open scoped ENNReal NNReal

section Games

variable (F : PrimeOrderGroupFamily)

/-! ### Attack Game 12.4, Lemma 12.6, and Exercise 12.26(a) -/

/-- Oracle specification for evaluation queries `(ṽ, w̃) ↦ f_{σ,τ}(ṽ, w̃)` in Attack Game 12.4
and Exercise 12.26(a) ([BonehShoup2023], Section 12.5.1, printed p. 486, and Exercise 12.26(a),
printed p. 521). -/
abbrev UniversalEvalSpec (d : F.Desc) : OracleSpec (F.Carrier d × F.Carrier d) :=
  fun _ => F.Carrier d

/-- Adaptive three-stage adversary for Attack Game 12.4 / Exercise 12.26(a) ([BonehShoup2023],
Section 12.5.1, printed p. 486, and Exercise 12.26(a), printed p. 521). `chooseU` selects `u ∈ G`,
`chooseChallenge` receives `h` and makes evaluation queries before choosing `(v, w)`, and `guess`
receives `z_b` and continues making evaluation queries before outputting a bit. Returning
`pure (v, w, st₁)` with `(v, w)` independent of `h` (which may still be kept in `st₁`) recovers
the non-adaptive Attack Game 12.4. -/
structure UniversalDistAdversary (d : F.Desc) (State₀ State₁ : Type) where
  /-- Stage 1: sample the base group element `u ∈ G` and initial state. -/
  chooseU : ProbComp (F.Carrier d × State₀)
  /-- Stage 2: given saved state `st₀` and auxiliary information `h`, make evaluation queries and
  emit `(v, w, st₁)`. -/
  chooseChallenge : State₀ → F.Carrier d →
    ProbOracleComp (UniversalEvalSpec F d) (F.Carrier d × F.Carrier d × State₁)
  /-- Stage 3: given saved state `st₁` and challenge `z_b`, make evaluation queries and output a
  Boolean guess. -/
  guess : State₁ → F.Carrier d → ProbOracleComp (UniversalEvalSpec F d) Bool

/-- Admissibility for `UniversalDistAdversary`: for every `(u, st₀)` in `chooseU`'s support, every
evaluation query of `chooseChallenge` lies in `L_u` on every execution path regardless of replies,
every supported output `(v, w, st₁)` of `chooseChallenge` on any honest `(σ, τ)` satisfies
`(v, w) ∉ L_u`, and every evaluation query of `guess` lies in `L_u` on every execution path. -/
@[expose] def UniversalDistAdversary.Admissible {F : PrimeOrderGroupFamily} {d : F.Desc}
    {State₀ State₁ : Type} (A : UniversalDistAdversary F d State₀ State₁) : Prop :=
  ∀ u st₀, (u, st₀) ∈ (ProbComp.eval A.chooseU).support →
    (∀ h : F.Carrier d,
      (A.chooseChallenge st₀ h).QueriesSatisfy (fun (v', w') => IsDHTriple F d u v' w')) ∧
    (∀ σ τ : ZMod (F.order d), ∀ v w st₁,
      (v, w, st₁) ∈ (ProbComp.eval ((A.chooseChallenge st₀ (projHashAux F d σ τ u)).run
        (fun (v', w') => pure (projHash F d σ τ v' w')))).support →
        ¬ IsDHTriple F d u v w ∧
        ∀ z : F.Carrier d,
          (A.guess st₁ z).QueriesSatisfy (fun (v', w') => IsDHTriple F d u v' w'))

/-- Experiment `b` of Attack Game 12.4 in the adaptive form of Exercise 12.26(a) ([BonehShoup2023],
Section 12.5.1, printed p. 486, and Exercise 12.26(a), printed p. 521). In Experiment `false`
(`b = 0`), `z = projHash F d σ τ v w`; in Experiment `true` (`b = 1`), `z` is uniformly distributed
in `F.Carrier d` (`ζ • F.generator d`). -/
@[expose] noncomputable def universalDistExperiment {State₀ State₁ : Type} (d : F.Desc)
    (A : UniversalDistAdversary F d State₀ State₁) (b : Bool) : Game := do
  let (u, st₀) ← ProbComp.eval A.chooseU
  let σ ← PMF.uniformOfFintype (ZMod (F.order d))
  let τ ← PMF.uniformOfFintype (ZMod (F.order d))
  let h := projHashAux F d σ τ u
  let (v, w, st₁) ← ProbComp.eval ((A.chooseChallenge st₀ h).run
    (fun (v', w') => pure (projHash F d σ τ v' w')))
  let ζ ← PMF.uniformOfFintype (ZMod (F.order d))
  let z := if b then ζ • F.generator d else projHash F d σ τ v w
  ProbComp.eval ((A.guess st₁ z).run (fun (v', w') => pure (projHash F d σ τ v' w')))

/-- **Lemma 12.6 / Exercise 12.26(a)** ([BonehShoup2023], Section 12.5.1, printed p. 486, and
Exercise 12.26(a), printed p. 521): for every admissible adversary, Experiment `false` and
Experiment `true` of `universalDistExperiment` have the identical output distribution. -/
theorem universalDistExperiment_false_eq_true {State₀ State₁ : Type} (d : F.Desc)
    (A : UniversalDistAdversary F d State₀ State₁) (hA : A.Admissible) :
    universalDistExperiment F d A false = universalDistExperiment F d A true := by
  dsimp only [universalDistExperiment, PMF.monad_bind_eq_bind]
  refine PMF.bind_congr_on_support (ProbComp.eval A.chooseU) _ _ fun u_st hsupp => ?_
  rcases u_st with ⟨u, st₀⟩
  obtain ⟨hpreQ, hpost⟩ := hA u st₀ hsupp
  obtain ⟨α, rfl⟩ := F.smul_generator_surjective d u
  rw [← PMF.uniformOfFintype_bind_bind_sub_right _ (fun τ => α * τ)]
  conv_rhs => rw [← PMF.uniformOfFintype_bind_bind_sub_right _ (fun τ => α * τ)]
  refine congrArg _ (funext fun δ => ?_)
  simp only [projHashAux_fiber_eq]
  have hpre_congr (τ : ZMod (F.order d)) :
      ProbComp.eval ((A.chooseChallenge st₀ (δ • F.generator d)).run
        (fun (v', w') => pure (projHash F d (δ - α * τ) τ v' w'))) =
      ProbComp.eval ((A.chooseChallenge st₀ (δ • F.generator d)).run
        (fun (v', w') => pure (projHash F d δ 0 v' w'))) :=
    (hpreQ (δ • F.generator d)).eval_run_congr fun (v', w') hq => by
      dsimp only at hq ⊢
      rw [projHash_fiber_eq_of_isDHTriple F d hq]
  simp only [hpre_congr]
  rw [PMF.bind_comm]; conv_rhs => rw [PMF.bind_comm]
  refine PMF.bind_congr_on_support _ _ _ fun chal hchal => ?_
  rcases chal with ⟨v, w, st₁⟩
  have hchal' :
      (v, w, st₁) ∈ (ProbComp.eval ((A.chooseChallenge st₀ (projHashAux F d δ 0
        (α • F.generator d))).run (fun (v', w') => pure (projHash F d δ 0 v' w')))).support := by
    have haux : projHashAux F d δ 0 (α • F.generator d) = δ • F.generator d := by
      simp only [projHashAux_generator_smul, mul_zero, add_zero]
    rwa [haux]
  obtain ⟨hvw, hpostQ⟩ := hpost δ 0 v w st₁ hchal'
  have hpost_congr (τ : ZMod (F.order d)) (z : F.Carrier d) :
      ProbComp.eval ((A.guess st₁ z).run
        (fun (v', w') => pure (projHash F d (δ - α * τ) τ v' w'))) =
      ProbComp.eval ((A.guess st₁ z).run
        (fun (v', w') => pure (projHash F d δ 0 v' w'))) :=
    (hpostQ z).eval_run_congr fun (v', w') hq => by
      dsimp only at hq ⊢
      rw [projHash_fiber_eq_of_isDHTriple F d hq]
  simp only [hpost_congr]
  obtain ⟨β, rfl⟩ := F.smul_generator_surjective d v
  obtain ⟨γ, rfl⟩ := F.smul_generator_surjective d w
  have hγ : γ ≠ α * β := fun heq => hvw ((isDHTriple_generator_smul_iff F d α β γ).mpr heq)
  simp only [Bool.false_eq_true, ↓reduceIte, PMF.bind_const]
  exact uniform_projHash_fiber F d hγ δ fun z =>
    ProbComp.eval ((A.guess st₁ z).run (fun (v', w') => pure (projHash F d δ 0 v' w')))

/-! ### Attack Game 12.5, Lemma 12.8, and Exercise 12.26(b) -/

/-- Oracle specification for evaluation queries `((ṽ, w̃), ρ̃) ↦ f'_{σ₁,τ₁,σ₂,τ₂}(ṽ, w̃, ρ̃)` in
Attack Game 12.5 and Exercise 12.26(b) ([BonehShoup2023], Section 12.5.2, printed p. 488, and
Exercise 12.26(b), printed p. 521). -/
abbrev Universal2EvalSpec (d : F.Desc) :
    OracleSpec ((F.Carrier d × F.Carrier d) × ZMod (F.order d)) :=
  fun _ => F.Carrier d

/-- Winning predicate of Attack Game 12.5 and Exercise 12.26(b) ([BonehShoup2023], Section 12.5.2,
printed p. 488): some tuple `(ẑ, v̂, ŵ, ρ̂)` in the output list has `(v̂, ŵ) ∉ L_u`,
`ρ̂ ≠ ρ`, and `ẑ = f'_{σ₁,τ₁,σ₂,τ₂}(v̂, ŵ, ρ̂)`. -/
@[expose] noncomputable def universal2Wins (d : F.Desc)
    (σ₁ τ₁ σ₂ τ₂ ρ : ZMod (F.order d)) (u : F.Carrier d)
    (guesses : List (F.Carrier d × F.Carrier d × F.Carrier d × ZMod (F.order d))) : Bool := by
  classical
  exact guesses.any fun (zHat, vHat, wHat, ρHat) =>
    decide (¬ IsDHTriple F d u vHat wHat ∧ ρHat ≠ ρ ∧
      zHat = projHash2 F d σ₁ τ₁ σ₂ τ₂ ρHat vHat wHat)

/-- Adaptive three-stage adversary for Attack Game 12.5 / Exercise 12.26(b) ([BonehShoup2023],
Section 12.5.2, printed p. 488, and Exercise 12.26(b), printed p. 521). Returning
`pure (v, w, ρ, st₁)` with `(v, w, ρ)` independent of `(h₁, h₂)` (which may still be kept in
`st₁`) recovers the non-adaptive Attack Game 12.5. -/
structure Universal2GuessAdversary (d : F.Desc) (State₀ State₁ : Type) where
  /-- Stage 1: sample the base group element `u ∈ G` and initial state. -/
  chooseU : ProbComp (F.Carrier d × State₀)
  /-- Stage 2: given saved state `st₀` and auxiliary information `(h₁, h₂)`, make evaluation
  queries and emit `(v, w, ρ, st₁)`. -/
  chooseChallenge : State₀ → F.Carrier d × F.Carrier d →
    ProbOracleComp (Universal2EvalSpec F d)
      (F.Carrier d × F.Carrier d × ZMod (F.order d) × State₁)
  /-- Stage 3: given saved state `st₁` and challenge `z`, make evaluation queries and output guess
  tuples. -/
  guess : State₁ → F.Carrier d →
    ProbOracleComp (Universal2EvalSpec F d)
      (List (F.Carrier d × F.Carrier d × F.Carrier d × ZMod (F.order d)))

/-- Admissibility and `Q`-tuple output bound for `Universal2GuessAdversary`: for every supported
`(u, st₀)`, every evaluation query of `chooseChallenge` lies in `L_u` on every execution path; for
every supported output `(v, w, ρ, st₁)` of `chooseChallenge` on honest keys and every
`z : F.Carrier d`, every evaluation query of `guess st₁ z` lies in `L_u` on every path and every
supported output list of `guess st₁ z` against every honest key has length at most `Q`. Notice
`(v, w) ∉ L_u` is intentionally omitted (though printed in Attack Game 12.5) because the `Q / q`
bound holds even when `(v, w) ∈ L_u`. -/
@[expose] def Universal2GuessAdversary.Admissible {F : PrimeOrderGroupFamily} {d : F.Desc}
    {State₀ State₁ : Type} (A : Universal2GuessAdversary F d State₀ State₁) (Q : ℕ) : Prop :=
  ∀ u st₀, (u, st₀) ∈ (ProbComp.eval A.chooseU).support →
    (∀ hh : F.Carrier d × F.Carrier d,
      (A.chooseChallenge st₀ hh).QueriesSatisfy (fun ((v', w'), _) => IsDHTriple F d u v' w')) ∧
    (∀ σ₁ τ₁ σ₂ τ₂ : ZMod (F.order d), ∀ v w ρ st₁,
      (v, w, ρ, st₁) ∈ (ProbComp.eval ((A.chooseChallenge st₀
        (projHash2Aux F d σ₁ τ₁ σ₂ τ₂ u)).run
          (fun ((v', w'), ρ') => pure (projHash2 F d σ₁ τ₁ σ₂ τ₂ ρ' v' w')))).support →
        ∀ z : F.Carrier d,
          (A.guess st₁ z).QueriesSatisfy (fun ((v', w'), _) => IsDHTriple F d u v' w') ∧
          ∀ σ₁' τ₁' σ₂' τ₂' : ZMod (F.order d), ∀ guesses,
            guesses ∈ (ProbComp.eval ((A.guess st₁ z).run
              (fun ((v', w'), ρ') =>
                pure (projHash2 F d σ₁' τ₁' σ₂' τ₂' ρ' v' w')))).support →
              guesses.length ≤ Q)

/-- Attack Game 12.5 in the adaptive form of Exercise 12.26(b) ([BonehShoup2023], Section 12.5.2,
printed p. 488, and Exercise 12.26(b), printed p. 521). -/
@[expose] noncomputable def universal2GuessGame {State₀ State₁ : Type} (d : F.Desc)
    (A : Universal2GuessAdversary F d State₀ State₁) : Game := do
  let (u, st₀) ← ProbComp.eval A.chooseU
  let σ₁ ← PMF.uniformOfFintype (ZMod (F.order d))
  let τ₁ ← PMF.uniformOfFintype (ZMod (F.order d))
  let σ₂ ← PMF.uniformOfFintype (ZMod (F.order d))
  let τ₂ ← PMF.uniformOfFintype (ZMod (F.order d))
  let hh := projHash2Aux F d σ₁ τ₁ σ₂ τ₂ u
  let (v, w, ρ, st₁) ← ProbComp.eval ((A.chooseChallenge st₀ hh).run
    (fun ((v', w'), ρ') => pure (projHash2 F d σ₁ τ₁ σ₂ τ₂ ρ' v' w')))
  let z := projHash2 F d σ₁ τ₁ σ₂ τ₂ ρ v w
  let guesses ← ProbComp.eval ((A.guess st₁ z).run
    (fun ((v', w'), ρ') => pure (projHash2 F d σ₁ τ₁ σ₂ τ₂ ρ' v' w')))
  return universal2Wins F d σ₁ τ₁ σ₂ τ₂ ρ u guesses

private theorem uniform_universal2Wins_le (d : F.Desc)
    (α δ₁ δ₂ ξ ρ : ZMod (F.order d)) (Q : ℕ)
    (guesses : List (F.Carrier d × F.Carrier d × F.Carrier d × ZMod (F.order d)))
    (hlen : guesses.length ≤ Q) :
    ((PMF.uniformOfFintype (ZMod (F.order d))).map (fun τ₂ =>
      universal2Wins F d (δ₁ - α * (ξ - ρ * τ₂)) (ξ - ρ * τ₂) (δ₂ - α * τ₂) τ₂ ρ
        (α • F.generator d) guesses)) true ≤
      (Q : ℝ≥0∞) / (F.order d : ℝ≥0∞) := by
  classical
  let hchoose (x : F.Carrier d) :
      Classical.choose (F.smul_generator_surjective d x) • F.generator d = x :=
    Classical.choose_spec (F.smul_generator_surjective d x)
  let badGuesses :=
    guesses.filter fun (_, vHat, wHat, ρHat) =>
      decide (¬ IsDHTriple F d (α • F.generator d) vHat wHat ∧ ρHat ≠ ρ)
  let toTuple : F.Carrier d × F.Carrier d × F.Carrier d × ZMod (F.order d) →
      ZMod (F.order d) × ZMod (F.order d) × ZMod (F.order d) × F.Carrier d
    | (zHat, vHat, wHat, ρHat) =>
      (Classical.choose (F.smul_generator_surjective d vHat),
        Classical.choose (F.smul_generator_surjective d wHat), ρHat, zHat)
  let tuples := badGuesses.map toTuple
  have hq : ∀ t ∈ tuples,
      let (β', γ', ρ', _) := t
      γ' ≠ α * β' ∧ ρ' ≠ ρ := by
    intro t ht
    rcases List.mem_map.mp ht with ⟨⟨zHat, vHat, wHat, ρHat⟩, hq_mem, rfl⟩
    obtain ⟨hnonDH, hρ⟩ := of_decide_eq_true (List.mem_filter.mp hq_mem).2
    refine ⟨fun hEq => hnonDH ?_, hρ⟩
    rwa [← hchoose vHat, ← hchoose wHat, isDHTriple_generator_smul_iff]
  have hpoint (τ₂ : ZMod (F.order d)) :
      universal2Wins F d (δ₁ - α * (ξ - ρ * τ₂)) (ξ - ρ * τ₂) (δ₂ - α * τ₂) τ₂ ρ
        (α • F.generator d) guesses =
      tuples.any (fun (β', γ', ρ', z') =>
        decide (projHash2 F d (δ₁ - α * (ξ - ρ * τ₂)) (ξ - ρ * τ₂) (δ₂ - α * τ₂) τ₂ ρ'
          (β' • F.generator d) (γ' • F.generator d) = z')) := by
    apply Bool.eq_iff_iff.mpr
    simp only [universal2Wins, List.any_eq_true, decide_eq_true_eq, tuples,
      List.mem_map, badGuesses, List.mem_filter]
    constructor
    · rintro ⟨⟨zHat, vHat, wHat, ρHat⟩, hmem, hnonDH, hρ, hz⟩
      dsimp only at hnonDH hρ hz
      refine ⟨toTuple (zHat, vHat, wHat, ρHat),
        ⟨(zHat, vHat, wHat, ρHat), ⟨hmem, hnonDH, hρ⟩, rfl⟩, ?_⟩
      dsimp only [toTuple]
      rw [hchoose vHat, hchoose wHat, hz]
    · rintro ⟨⟨β', γ', ρ', z'⟩, ⟨⟨zHat, vHat, wHat, ρHat⟩, ⟨hmem, hfilt⟩, hto⟩, hz⟩
      cases hto
      refine ⟨_, hmem, hfilt.1, hfilt.2, ?_⟩
      rw [hchoose vHat, hchoose wHat] at hz
      exact hz.symm
  simp_rw [hpoint]
  refine (uniform_projHash2_fiber_any_le F d α ρ δ₁ δ₂ ξ tuples hq).trans ?_
  have hlen_tuples : tuples.length ≤ Q := by
    simpa only [tuples, List.length_map, badGuesses] using
      (List.length_filter_le _ guesses).trans hlen
  gcongr

/-- **Lemma 12.8 / Exercise 12.26(b)** ([BonehShoup2023], Section 12.5.2, printed p. 488, and
Exercise 12.26(b), printed p. 521): in `universal2GuessGame`, every admissible adversary that
outputs at most `Q` tuples wins with probability at most `Q / q`. -/
theorem succProbability_universal2GuessGame_le {State₀ State₁ : Type} (d : F.Desc)
    (A : Universal2GuessAdversary F d State₀ State₁) {Q : ℕ} (hA : A.Admissible Q) :
    Game.succProbability (universal2GuessGame F d A) ≤
      (Q : ℝ≥0) / (F.order d : ℝ≥0) := by
  have hbound :
      (universal2GuessGame F d A) true ≤ (Q : ℝ≥0∞) / (F.order d : ℝ≥0∞) := by
    dsimp only [universal2GuessGame, PMF.monad_bind_eq_bind]
    refine PMF.bind_apply_le_on_support _ fun u_st hsupp => ?_
    rcases u_st with ⟨u, st₀⟩
    obtain ⟨hpreQ, hpost⟩ := hA u st₀ hsupp
    obtain ⟨α, rfl⟩ := F.smul_generator_surjective d u
    rw [← PMF.uniformOfFintype_bind_bind_sub_right _ (fun τ => α * τ)]
    refine PMF.bind_apply_le_on_support _ fun δ₁ _ => ?_
    conv_lhs =>
      enter [1, 2, τ₁]; rw [← PMF.uniformOfFintype_bind_bind_sub_right _ (fun τ => α * τ)]
    rw [PMF.bind_comm]
    refine PMF.bind_apply_le_on_support _ fun δ₂ _ => ?_
    simp only [projHash2Aux_fiber_eq]
    have hpre_congr (τ₁ τ₂ : ZMod (F.order d)) :
        ProbComp.eval ((A.chooseChallenge st₀ (δ₁ • F.generator d, δ₂ • F.generator d)).run
          (fun ((v', w'), ρ') =>
            pure (projHash2 F d (δ₁ - α * τ₁) τ₁ (δ₂ - α * τ₂) τ₂ ρ' v' w'))) =
        ProbComp.eval ((A.chooseChallenge st₀ (δ₁ • F.generator d, δ₂ • F.generator d)).run
          (fun ((v', w'), ρ') => pure (projHash2 F d δ₁ 0 δ₂ 0 ρ' v' w'))) :=
      (hpreQ (δ₁ • F.generator d, δ₂ • F.generator d)).eval_run_congr fun ((v', w'), _) hq => by
        dsimp only at hq ⊢
        rw [projHash2_fiber_eq_of_isDHTriple F d hq]
    simp only [hpre_congr]
    conv_lhs => enter [1, 2, τ₁]; rw [PMF.bind_comm]
    rw [PMF.bind_comm]
    refine PMF.bind_apply_le_on_support _ fun chal hchal => ?_
    rcases chal with ⟨v, w, ρ, st₁⟩
    have hchal' :
        (v, w, ρ, st₁) ∈ (ProbComp.eval ((A.chooseChallenge st₀
          (projHash2Aux F d δ₁ 0 δ₂ 0 (α • F.generator d))).run
            (fun ((v', w'), ρ') => pure (projHash2 F d δ₁ 0 δ₂ 0 ρ' v' w')))).support := by
      simpa only [projHash2Aux, projHashAux_generator_smul, mul_zero, add_zero] using hchal
    have hpost_z := hpost δ₁ 0 δ₂ 0 v w ρ st₁ hchal'
    rw [PMF.bind_comm]
    conv_lhs =>
      enter [1, 2, τ₂]; rw [← PMF.uniformOfFintype_bind_sub_right (ρ * τ₂)]
    rw [PMF.bind_comm]
    refine PMF.bind_apply_le_on_support _ fun ξ _ => ?_
    obtain ⟨β, rfl⟩ := F.smul_generator_surjective d v
    obtain ⟨γ, rfl⟩ := F.smul_generator_surjective d w
    simp only [projHash2_fiber_challenge_eq F d α β γ δ₁ δ₂ ξ]
    set z : F.Carrier d := (β * (δ₁ + ρ * δ₂) + (γ - α * β) * ξ) • F.generator d
    have hpost_congr (τ₂ : ZMod (F.order d)) :
        ProbComp.eval ((A.guess st₁ z).run
          (fun ((v', w'), ρ') =>
            pure (projHash2 F d (δ₁ - α * (ξ - ρ * τ₂)) (ξ - ρ * τ₂)
              (δ₂ - α * τ₂) τ₂ ρ' v' w'))) =
        ProbComp.eval ((A.guess st₁ z).run
          (fun ((v', w'), ρ') => pure (projHash2 F d δ₁ 0 δ₂ 0 ρ' v' w'))) :=
      (hpost_z z).1.eval_run_congr fun ((v', w'), _) hq => by
        dsimp only at hq ⊢
        rw [projHash2_fiber_eq_of_isDHTriple F d hq]
    simp only [hpost_congr]
    rw [PMF.bind_comm]
    refine PMF.bind_apply_le_on_support _ fun guesses hguesses => ?_
    have hlen : guesses.length ≤ Q := (hpost_z z).2 δ₁ 0 δ₂ 0 guesses hguesses
    simpa only [PMF.map, Function.comp_def, PMF.monad_pure_eq_pure] using
      uniform_universal2Wins_le F d α δ₁ δ₂ ξ ρ Q guesses hlen
  have hne : ((Q : ℝ≥0∞) / (F.order d : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top Q) (Nat.cast_ne_zero.mpr (F.prime_order d).ne_zero)
  simpa only [Game.succProbability, ENNReal.toNNReal_div, ENNReal.toNNReal_natCast] using
    ENNReal.toNNReal_mono hne hbound

end Games

end Cslib.Crypto.ProjectiveHash
