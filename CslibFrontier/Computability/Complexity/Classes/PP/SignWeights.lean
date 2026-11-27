/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PP
public import CslibFrontier.Computability.Complexity.Classes.SharpP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Computability.Complexity.Classes.SharpP.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Complexity.Classes.PP.Characterization
import CslibFrontier.Computability.Complexity.Classes.SharpP.Products
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Foundations.Algebra.Polynomial.DyadicSignProduct

/-!
# GapP weights for the two answers to a PP decision

For a nonzero integer gap `g`, the dyadic sign product at `g` and at `-g` assigns greater
weight to its sign. The closure of GapP under polynomially many products makes the two weights
uniform in the instance. Our factors have distinct dyadic roots. This adapts the geometric-root
product of [Newman][Newman1964], p. 11, and the dyadic product with repeated factors used in
[Fortnow and Reingold][FortnowReingold1996], §4. The weights serve both truth-table closure and
postselected quantum decisions. The single tagged function in
`exists_gapP_separation_of_mem_PP` is an original formulation of this counting argument.

## Main definitions

* `newmanPoly` is the product of the dyadic linear factors used to separate the two signs.

## Main results

* `two_mul_abs_newmanPoly_neg_le` gives a factor-two gap throughout the positive integer range.
* `exists_gapP_separation_of_mem_PP` assigns the larger positive weight to the correct answer.

## References

* [D. J. Newman, *Rational approximation to |x|*][Newman1964]
* [L. Fortnow, N. Reingold, *PP is closed under truth-table reductions*][FortnowReingold1996]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Finset

variable {α : Type} {enc : α ↪ List Bool}

/-- The dyadic sign product `∏ j ∈ range (M + 1), (2 ^ j + z)`, used to
rationalize the sign of an integer `z` with `1 ≤ |z| ≤ 2 ^ M`. -/
@[expose] def newmanPoly (M : ℕ) (z : ℤ) : ℤ :=
  ∏ j ∈ range (M + 1), ((2 : ℤ) ^ j + z)

/-- The dyadic sign product is at least `1` at every positive integer. -/
theorem one_le_newmanPoly {M : ℕ} {z : ℤ} (hz : 1 ≤ z) : 1 ≤ newmanPoly M z :=
  one_le_prod₀ fun j _ => by
    have : (0 : ℤ) ≤ (2 : ℤ) ^ j := by positivity
    omega

/-- **Sign separation for the dyadic product.** For `1 ≤ z ≤ 2 ^ M`, twice
`|newmanPoly M (-z)|` is at most `newmanPoly M z`. -/
theorem two_mul_abs_newmanPoly_neg_le {M : ℕ} {z : ℤ} (hz₁ : 1 ≤ z) (hz₂ : z ≤ (2 : ℤ) ^ M) :
    2 * |newmanPoly M (-z)| ≤ newmanPoly M z := by
  have h : 3 * |newmanPoly M (-z)| ≤ newmanPoly M z := by
    simpa only [newmanPoly, sub_eq_add_neg] using
      Polynomial.three_mul_abs_prod_two_pow_sub_le hz₁ hz₂
  exact (mul_le_mul_of_nonneg_right (by decide : (2 : ℤ) ≤ 3) (abs_nonneg _)).trans h

/-- Applying the dyadic sign product to a GapP function preserves GapP when the number of
factors is polynomial-time computable in unary. -/
theorem GapP.newmanPoly_mem {M : α → ℕ} {g : α → ℤ} (hg : g ∈ GapP enc)
    (hM : ComputableInPolyTime M enc encUnary) :
    (fun a => newmanPoly (M a) (g a)) ∈ GapP enc := by
  have htwo : (fun _ : α × ℕ => (2 : ℤ)) ∈ GapP (encPair enc encUnary) :=
    GapP.add_mem GapP.one_mem GapP.one_mem
  have hpow := GapP.pow_mem_polyTime htwo (.snd enc encUnary)
  exact GapP.prod_range_mem
    (GapP.add_mem hpow (GapP.comp_mem hg (.fst enc encUnary))) (by fun_prop)

/-- A PP language admits a single GapP function on tagged instances whose value at the correct
tag is positive and at least twice the absolute value at the other tag. The right tag denotes
membership. Both encodings consist of one bit followed by the same instance word. -/
theorem exists_gapP_separation_of_mem_PP {A : Set α} (hA : A ∈ PP enc) :
    ∃ f ∈ GapP (encSum enc enc), ∀ a,
      (a ∈ A → 0 < f (.inr a) ∧ 2 * |f (.inl a)| ≤ f (.inr a)) ∧
      (a ∉ A → 0 < f (.inl a) ∧ 2 * |f (.inr a)| ≤ f (.inl a)) := by
  obtain ⟨u, hu, hsign⟩ := mem_PP_iff_exists_GapP.mp hA
  let g (a : α) := u a + u a - 1
  have hg : g ∈ GapP enc := GapP.sub_mem' (GapP.add_mem hu hu) GapP.one_mem
  obtain ⟨p, hp⟩ := GapP.exists_abs_le_two_pow hg
  let M (a : α) := p.eval (enc a).length
  have hM : ComputableInPolyTime M enc encUnary :=
    (ComputableInPolyTime.unary_eval p).comp (ComputableInPolyTime.encoding_length enc)
  let untag : α ⊕ α → α := Sum.elim id id
  let tag : α ⊕ α → Bool := Sum.elim (fun _ => false) (fun _ => true)
  have hxt : ComputableInPolyTime untag (encSum enc enc) enc :=
    .sumElim .id' .id'
  have ht : ComputableInPolyTime tag (encSum enc enc) encBool :=
    .sumElim (.const false) (.const true)
  refine ⟨_, GapP.ite_mem ht (GapP.comp_mem (GapP.newmanPoly_mem hg hM) hxt)
    (GapP.comp_mem (GapP.newmanPoly_mem (GapP.neg_mem hg) hM) hxt), fun a => ?_⟩
  change (a ∈ A → 0 < newmanPoly (M a) (g a) ∧
      2 * |newmanPoly (M a) (-g a)| ≤ newmanPoly (M a) (g a)) ∧
    (a ∉ A → 0 < newmanPoly (M a) (-g a) ∧
      2 * |newmanPoly (M a) (g a)| ≤ newmanPoly (M a) (-g a))
  obtain ⟨hl, hr⟩ := abs_le.mp (hp a)
  constructor
  · intro ha
    have hpos := (hsign a).1 ha
    have hz : 1 ≤ g a := by dsimp [g]; omega
    exact ⟨one_le_newmanPoly hz, two_mul_abs_newmanPoly_neg_le hz hr⟩
  · intro ha
    have hneg := mt (hsign a).2 ha
    have hz : 1 ≤ -g a := by dsimp [g]; omega
    exact ⟨one_le_newmanPoly hz, by simpa using
      (two_mul_abs_newmanPoly_neg_le (M := M a) hz (by dsimp [M]; omega))⟩

end Cslib.Complexity
