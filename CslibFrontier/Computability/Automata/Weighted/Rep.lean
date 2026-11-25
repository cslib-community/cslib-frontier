/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Sum

/-!
# Linear representations of series on words

A series is a function `List Ω → F`. A linear representation of dimension `n` gives the value of
the series at a word as `(row vector) · (product of matrices, one for each letter) · (column
vector)`. Sums, products, and stars (over non-empty factors) of represented series are represented,
and dimensions add up.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Tape.Rep`.

## Main definitions

* `Cslib.Automata.Weighted.Series`, `Series.mul`, `Series.one`, `Series.kstar`.
* `Cslib.Automata.Weighted.Rep`, `Rep.tail`, `Rep.series`, `Rep.add`, `Rep.mul`, `Rep.star`.

## Main results

* `Rep.add_series`, `Rep.mul_series`, `Rep.star_series`: closure of linear
  representations under sum, Cauchy product, and Kleene star over non-empty factors.
-/

public section

namespace Cslib.Automata.Weighted

open Finset Matrix

variable {F : Type*} [CommRing F] {Ω : Type*}

/-- A formal power series on words over alphabet `Ω` with coefficients in `F`. -/
abbrev Series (F Ω : Type*) := List Ω → F

namespace Series

/-- The Cauchy product of two series on words. -/
@[expose] def mul (f g : Series F Ω) : Series F Ω := fun o =>
  ∑ k ∈ range (o.length + 1), f (o.take k) * g (o.drop k)

/-- The unit series: `1` at the empty word and `0` elsewhere. -/
@[expose] def one : Series F Ω := fun o => if o = [] then 1 else 0

/-- The star over non-empty factors: the sum over all cuts of a word into non-empty factors. -/
@[expose] def kstar (f : Series F Ω) : Series F Ω
  | [] => 1
  | a :: o => ∑ k ∈ range (o.length + 1), f (a :: o.take k) * kstar f (o.drop k)
  termination_by o => o.length
  decreasing_by simp; omega

theorem kstar_nil (f : Series F Ω) : kstar f [] = 1 := by rw [kstar]

theorem kstar_cons (f : Series F Ω) (a : Ω) (o : List Ω) : kstar f (a :: o) =
    ∑ k ∈ range (o.length + 1), f (a :: o.take k) * kstar f (o.drop k) := by rw [kstar]

end Series

/-- A linear representation (weighted finite automaton) with state space `Q`. -/
structure Rep (F Ω Q : Type*) where
  /-- initial weights -/
  lam : Q → F
  /-- transition weights -/
  mu : Ω → Matrix Q Q F
  /-- final weights -/
  gam : Q → F

namespace Rep

variable {Q Q₁ Q₂ : Type*} [Fintype Q] [Fintype Q₁] [Fintype Q₂]

/-- The weights from each state to acceptance along a word. -/
@[expose] def tail (r : Rep F Ω Q) : List Ω → Q → F
  | [] => r.gam
  | a :: o => r.mu a *ᵥ tail r o

/-- The series realized by a linear representation. -/
@[expose] def series (r : Rep F Ω Q) : Series F Ω := fun o => r.lam ⬝ᵥ r.tail o

/-- Sum of two linear representations. -/
@[expose] def add (r₁ : Rep F Ω Q₁) (r₂ : Rep F Ω Q₂) : Rep F Ω (Q₁ ⊕ Q₂) where
  lam := Sum.elim r₁.lam r₂.lam
  mu a := Matrix.fromBlocks (r₁.mu a) 0 0 (r₂.mu a)
  gam := Sum.elim r₁.gam r₂.gam

theorem add_tail (r₁ : Rep F Ω Q₁) (r₂ : Rep F Ω Q₂) (o : List Ω) :
    (r₁.add r₂).tail o = Sum.elim (r₁.tail o) (r₂.tail o) := by
  induction o with
  | nil => rfl
  | cons a o ih =>
    rw [tail, ih]
    simp [add, tail, Matrix.fromBlocks_mulVec]

theorem add_series (r₁ : Rep F Ω Q₁) (r₂ : Rep F Ω Q₂) (o : List Ω) :
    (r₁.add r₂).series o = r₁.series o + r₂.series o := by
  rw [series, add_tail]
  simp [series, add]

/-- Cauchy product of two linear representations. -/
@[expose] def mul (r₁ : Rep F Ω Q₁) (r₂ : Rep F Ω Q₂) : Rep F Ω (Q₁ ⊕ Q₂) where
  lam := Sum.elim r₁.lam ((r₁.lam ⬝ᵥ r₁.gam) • r₂.lam)
  mu a := Matrix.fromBlocks (r₁.mu a)
    (Matrix.vecMulVec (r₁.mu a *ᵥ r₁.gam) r₂.lam) 0 (r₂.mu a)
  gam := Sum.elim 0 r₂.gam

theorem mul_tail (r₁ : Rep F Ω Q₁) (r₂ : Rep F Ω Q₂) (o : List Ω) :
    (r₁.mul r₂).tail o = Sum.elim
      (∑ k ∈ range o.length,
        (r₂.series (o.drop (k + 1))) • r₁.tail (o.take (k + 1))) (r₂.tail o) := by
  induction o with
  | nil => simp [tail, mul]
  | cons a o ih =>
    rw [tail, ih]
    simp only [mul, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, zero_add,
      Sum.elim_comp_inl, Sum.elim_comp_inr]
    congr 1
    rw [List.length_cons, Finset.sum_range_succ', Matrix.mulVec_sum]
    congr 1
    · exact Finset.sum_congr rfl fun _ _ => by simp [tail, Matrix.mulVec_smul]
    · ext
      simp [tail, series, Matrix.vecMulVec_mulVec, mul_comm]

theorem mul_series (r₁ : Rep F Ω Q₁) (r₂ : Rep F Ω Q₂) (o : List Ω) :
    (r₁.mul r₂).series o = Series.mul r₁.series r₂.series o := by
  rw [series, mul_tail, Series.mul, Finset.sum_range_succ']
  change Sum.elim r₁.lam ((r₁.lam ⬝ᵥ r₁.gam) • r₂.lam) ⬝ᵥ _ = _
  rw [sumElim_dotProduct_sumElim, dotProduct_sum]
  exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun _ _ => by simp [series, mul_comm])
    (by simp [series, tail])

/-- Star of a linear representation (over non-empty factors). -/
@[expose] def star (r : Rep F Ω Q) : Rep F Ω (Unit ⊕ Q) where
  lam := Sum.elim 1 0
  mu a := Matrix.fromBlocks
    (Matrix.of fun _ _ => r.lam ⬝ᵥ (r.mu a *ᵥ r.gam))
    (Matrix.of fun _ q => (r.lam ᵥ* r.mu a) q)
    (Matrix.of fun q _ => (r.mu a *ᵥ r.gam) q) (r.mu a)
  gam := Sum.elim 1 0

theorem star_tail (r : Rep F Ω Q) (o : List Ω) :
    r.star.tail o = Sum.elim (fun _ => Series.kstar r.series o)
      (∑ k ∈ range o.length,
        (Series.kstar r.series (o.drop (k + 1))) • r.tail (o.take (k + 1))) := by
  induction o with
  | nil => ext q; rcases q with q | q <;> simp [tail, star, Series.kstar_nil]
  | cons a o ih =>
    rw [tail, ih]
    simp only [star, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr]
    congr 1
    · ext ⟨⟩
      have hdot (v : Q → F) :
          ((Matrix.of fun (_ : Unit) q => (r.lam ᵥ* r.mu a) q) *ᵥ v) () =
            r.lam ⬝ᵥ (r.mu a *ᵥ v) := by
        rw [Matrix.dotProduct_mulVec]
        simp [Matrix.mulVec, dotProduct]
      rw [Series.kstar_cons, Finset.sum_range_succ', Pi.add_apply, add_comm, hdot,
        Matrix.mulVec_sum, dotProduct_sum]
      exact congrArg₂ (· + ·)
        (Finset.sum_congr rfl fun _ _ => by simp [series, tail, Matrix.mulVec_smul, mul_comm])
        (by simp [series, tail, Matrix.mulVec, dotProduct])
    · rw [List.length_cons, Finset.sum_range_succ', add_comm, Matrix.mulVec_sum]
      congr 1
      · exact Finset.sum_congr rfl fun _ _ => by simp [tail, Matrix.mulVec_smul]
      · ext
        simp [tail, Matrix.mulVec, dotProduct, mul_comm]

theorem star_series (r : Rep F Ω Q) (o : List Ω) :
    r.star.series o = Series.kstar r.series o := by
  rw [series, star_tail]
  change Sum.elim (1 : Unit → F) (0 : Q → F) ⬝ᵥ _ = _
  rw [sumElim_dotProduct_sumElim]
  simp [dotProduct]

end Rep

end Cslib.Automata.Weighted
