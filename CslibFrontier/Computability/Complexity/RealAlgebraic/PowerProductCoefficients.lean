/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.IndexedPowerProduct
public import CslibFrontier.Computability.Complexity.RealAlgebraic.MultivariateCoefficients

/-!
# Coefficients of indexed polynomial power products

`powerProductCoefficient` obtains a coefficient of `v * ∏ i, r i ^ j i` through modular
access to `v` and the lower polynomials `r i`. It evaluates the indexed power product at
each canonical grid point, then applies the existing multivariate coefficient extractor.
It never constructs the full product polynomial or asks the caller to supply its coefficients.

Uniform `F_a` evaluation access gives an `F_(a+4)` coefficient evaluator. The variable count
is unary so that grid points have polynomial encoded length; relation indices, field moduli,
coefficient indices and power exponents remain binary. Missing list entries use the existing
zero defaults. Correctness needs the Fourier degree bounds and access only at canonical
finite-field grid points; the evaluator itself is total on all inputs.

Ported from `LeanCanny.CountingHierarchy.PowerProductCoefficients` at lean-canny commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`, as a step toward finite-residue evaluation.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM MvPolynomial
open scoped BigOperators

/-- Evaluate a coefficient of `v * product r_i^j_i` using modular
 products followed by one multivariate Fourier sum. -/
@[expose] noncomputable def powerProductCoefficient (p n : ℕ) (β j : List ℕ)
    (v : List ℕ → ℕ) (r : ℕ → List ℕ → ℕ) : ℕ :=
  multivariateCoefficientResidue p n β (fun z =>
    (v z * indexedPowerProduct p n j (fun i => r i z)) % p)

/-- A short-index modular product followed by coefficient extraction costs four levels.
Arity is unary for grid decoding; the relation index and all powers remain binary. -/
theorem powerProductCoefficient_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n : α → ℕ} {β j : α → List ℕ}
    {v : α × List ℕ → ℕ} {r : α × (ℕ × List ℕ) → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hn : ComputableInPolyTime n enc encUnary)
    (hβ : ComputableInPolyTime β enc (encList encNat))
    (hj : ComputableInPolyTime j enc (encList encNat))
    (hv : v ∈ CountingFunction a (encPair enc (encList encNat)) encNat)
    (hr : r ∈ CountingFunction a (encPair enc (encPair encNat (encList encNat))) encNat) :
    (fun w => powerProductCoefficient (p w) (n w) (β w) (j w)
      (fun z => v (w, z)) (fun i z => r (w, i, z))) ∈
        CountingFunction (a + 4) enc encNat := by
  have hr' : (fun q : (α × List ℕ) × ℕ => r (q.1.1, q.2, q.1.2)) ∈
      CountingFunction a (encPair (encPair enc (encList encNat)) encNat) encNat :=
    CountingFunction.preprocess hr (by fun_prop)
  have hp' := hp.comp (ComputableInPolyTime.fst enc (encList encNat))
  have hn' := (ComputableInPolyTime.unary_to_binary.comp hn).comp
    (ComputableInPolyTime.fst enc (encList encNat))
  have hj' := hj.comp (ComputableInPolyTime.fst enc (encList encNat))
  have hprod := indexedPowerProduct_mem (Decoder.pair E (Decoder.list Decoder.nat)) hp' hn' hj' hr'
  have hval := CountingFunction.nat_mod
    (CountingFunction.nat_mul (CountingFunction.mono (by omega : a ≤ a + 3) hv) hprod)
    (CountingFunction.of_polyTime hp')
  exact multivariateCoefficientResidue_mem E hp hn hβ hval

/-- The evaluator computes the coefficient of the actual polynomial product.
The access hypotheses are required only on canonical grid points and genuine relation indices. -/
theorem powerProductCoefficient_cast {p n : ℕ} [Fact p.Prime]
    (v : MvPolynomial (Fin n) (ZMod p)) (r : Fin n → MvPolynomial (Fin n) (ZMod p))
    (j : Fin n → ℕ) (e : Fin n →₀ ℕ) (β js : List ℕ)
    (value : List ℕ → ℕ) (rvalue : ℕ → List ℕ → ℕ)
    (hdeg : (v * ∏ i, r i ^ j i).totalDegree < p - 1)
    (he : ∀ i, e i < p - 1) (hβ : ∀ i : Fin n, β[i.val]?.getD 0 = e i)
    (hj : ∀ i : Fin n, js[i.val]?.getD 0 = j i)
    (hv : ∀ s < p ^ n, (value (gridPoint p n s) : ZMod p) =
      eval (fun i : Fin n => (((gridPoint p n s)[i.val]?.getD 0 : ℕ) : ZMod p)) v)
    (hr : ∀ i : Fin n, ∀ s < p ^ n, (rvalue i.val (gridPoint p n s) : ZMod p) =
      eval (fun k : Fin n => (((gridPoint p n s)[k.val]?.getD 0 : ℕ) : ZMod p)) (r i)) :
    (powerProductCoefficient p n β js value rvalue : ZMod p) =
      (v * ∏ i, r i ^ j i).coeff e := by
  unfold powerProductCoefficient
  apply multivariateCoefficientResidue_cast _ e β _ hdeg he hβ
  intro s hs
  rw [ZMod.natCast_mod, Nat.cast_mul, hv s hs, indexedPowerProduct_cast,
    map_mul, map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [hj i, hr i s hs, map_pow]

end Cslib.Complexity.RealAlgebraic
