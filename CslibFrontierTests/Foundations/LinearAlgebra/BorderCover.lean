/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.BorderCover
import Mathlib.Algebra.Polynomial.Coeff

/-! Tests of covers up to `ε` and of Lemma N.3 of [AnthropicVPVNP2026] under ordinary imports:

* exact covers are the covers up to `ε` with `D = 0`;
* a cover up to `ε` with `D = 1`: `t` is the coefficient of `ε` of `ε • t`;
* Lemma N.3 for a sum with one term, for the cover with `D = 1`, and for the unit tensor of size
  `2`, covered by two copies of `1`. -/

namespace Cslib.PartyTensorTests.BorderCover

open Cslib PartyTensor Polynomial

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

/-- A tensor covers itself exactly, hence up to `ε` with `D = 0`, and back. -/
example (t : PartyTensor K I) :
    t.BorderCoveredBy 0 (fun _ : Unit => t) ∧ t.CoveredBy fun _ : Unit => t :=
  ⟨(CoveredBy.single le_rfl).borderCoveredBy, borderCoveredBy_zero_iff.1
    (CoveredBy.single le_rfl).borderCoveredBy⟩

/-- On one party, `t` is the coefficient of `ε` of `ε • t`, a cover up to `ε` with `D = 1`, and
Lemma N.3 applies to it. -/
example (F : SpectralPoint K (Fin 1)) (t : PartyTensor K (Fin 1)) :
    t.BorderCoveredBy 1 (fun _ : Unit => t) ∧
      F t ≤ (Fintype.card Unit : ℝ) ^ F.unitExponent (id : Fin 1 → Fin 1) * F t := by
  suffices h : t.BorderCoveredBy 1 (fun _ : Unit => t) from
    ⟨h, F.apply_le_of_borderCoveredBy id t (fun q hq => absurd ⟨q, rfl⟩ hq) h fun _ => le_rfl⟩
  classical
  refine ⟨fun _ _ a c => if a = c then X else 0, fun x i hi => ?_⟩
  have hsum : (∑ k : Unit, localApply (fun (_ : Fin 1) a c => if a = c then (X : K[X]) else 0)
      (fun y => C (t.entry y)) x) = X * C (t.entry x) := by
    rw [Fintype.sum_unique, localApply, Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      obtain ⟨p, hp⟩ := Function.ne_iff.1 hy
      rw [Finset.prod_eq_zero (Finset.mem_univ p) (ite_eq_right fun h => hp h.symm), zero_mul]
    · simp
  rw [hsum]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl <;> simp

/-- Lemma N.3 for a sum with one term: `F t ≤ 1 ^ g · F t`. -/
example [Nonempty I] (F : SpectralPoint K I) (t : PartyTensor K I) :
    F t ≤ (Fintype.card Unit : ℝ) ^ F.unitExponent (id : I → I) * F t :=
  F.apply_le_of_borderCoveredBy id t (fun q hq => absurd ⟨q, rfl⟩ hq)
    (CoveredBy.single le_rfl).borderCoveredBy fun _ => le_rfl

/-- Lemma N.3 for two terms: the unit tensor of size `2` is covered by two copies of `1`, so a
spectral point is at most `2 ^ g` there, `g` the unit exponent of all parties. -/
example [Nonempty I] (F : SpectralPoint K I) :
    F (unit K I 2) ≤ (Fintype.card (Fin 2) : ℝ) ^ F.unitExponent (id : I → I) * 1 :=
  F.apply_le_of_borderCoveredBy id (unit K I 2) (fun q hq => absurd ⟨q, rfl⟩ hq)
    (coveredBy_one_of_le_unit le_rfl).borderCoveredBy fun _ => F.map_one.le

end Cslib.PartyTensorTests.BorderCover
