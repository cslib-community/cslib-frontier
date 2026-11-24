/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Tame
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.Tactic

/-!
# Guarded branches

`tm_ite_cond`: when the condition is stable, the then-branch only needs a tier
when the condition holds. The decider runs the counter only for primes.
-/

public section

namespace Cslib.Complexity.NtimeDspace.ProgTerm

open Term

variable {w : List Bool} {L : ℕ} {env : List ℕ}

theorem tm_ite_cond {c t e : Term} {dc d : ℕ} (hc : Tm w L dc c env) (hcs : StableAt w c env)
    (ht : 0 < c.denote w env → Tm w L d t env) (he : Tm w L d e env) :
    Tm w L d (ite c t e) env := by
  by_cases h : 0 < c.denote w env
  · have htm := ht h
    intro pre hp
    have hcv : 0 < c.denote w (pre ++ env) := by rw [hcs pre]; exact h
    refine ⟨⟨(hc pre hp).1, ?_⟩, ?_⟩
    · exact (ite_eq_left (show 0 < ProgLang.Prog.eval w (c (pre ++ env).length)
        (pre ++ env) from hcv)).symm ▸ (htm pre hp).1
    · simp only [denote_ite, ite_eq_left hcv]; exact (htm pre hp).2
  · intro pre hp
    have hcv : ¬ 0 < c.denote w (pre ++ env) := by rw [hcs pre]; exact h
    refine ⟨⟨(hc pre hp).1, ?_⟩, ?_⟩
    · exact (ite_eq_right (show ¬ 0 < ProgLang.Prog.eval w (c (pre ++ env).length)
        (pre ++ env) from hcv)).symm ▸ (he pre hp).1
    · simp only [denote_ite, ite_eq_right hcv]; exact (he pre hp).2

/-- Retier a stable term by its value. -/
theorem tm_retier {t : Term} {d d' : ℕ} (h : Tm w L d t env) (hs : StableAt w t env)
    (hv : t.denote w env < 2 ^ (d' * L)) : Tm w L d' t env := fun pre hp =>
  ⟨(h pre hp).1, by rw [hs pre]; exact hv⟩

theorem TmF.mono_in {f : Term → Term} {da da' d : ℕ} (h : TmF w L f da d env) (hda : da' ≤ da) :
    TmF w L f da' d env := fun env' he x hx => h env' he x (hx.mono hda)

theorem TmF2.mono_in {f : Term → Term → Term} {da da' db db' d : ℕ} (h : TmF2 w L f da db d env)
    (hda : da' ≤ da) (hdb : db' ≤ db) : TmF2 w L f da' db' d env :=
  fun env' he x y hx hy => h env' he x y (hx.mono hda) (hy.mono hdb)

/-- Retier a term function by a value bound for all arguments. -/
theorem TmF.retier {f : Term → Term} {da d d' : ℕ} (h : TmF w L f da d env)
    (hv : ∀ env', Ext L env' env → ∀ x, (f x).denote w env' < 2 ^ (d' * L)) : TmF w L f da d' env :=
  fun env' he x hx pre hp => ⟨(h env' he x hx pre hp).1, hv _ (Ext.trans ⟨pre, hp, rfl⟩ he) x⟩

theorem TmF2.retier {f : Term → Term → Term} {da db d d' : ℕ} (h : TmF2 w L f da db d env)
    (hv : ∀ env', Ext L env' env → ∀ x y, (f x y).denote w env' < 2 ^ (d' * L)) :
    TmF2 w L f da db d' env :=
  fun env' he x y hx hy pre hp =>
    ⟨(h env' he x y hx hy pre hp).1, hv _ (Ext.trans ⟨pre, hp, rfl⟩ he) x y⟩

end Cslib.Complexity.NtimeDspace.ProgTerm
