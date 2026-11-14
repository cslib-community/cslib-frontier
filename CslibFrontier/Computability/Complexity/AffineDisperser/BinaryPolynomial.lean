/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryPolynomial
import Mathlib.Data.List.GetD

/-!
# Binary-polynomial power tables for the affine disperser

The explicit affine disperser represents multiplication in power bases by the coefficient lists
of the remainders of `X ^ e`, for `e` below twice the modulus degree.  `powerTable` computes those
lists with the general binary-polynomial reduction in
`CslibFrontier.Foundations.FieldTheory.Finite.BinaryPolynomial`.

## Main definitions

* `Cslib.AffineDisperser.powerTable`: the required remainders of powers of `X`.

## Main results

* `Cslib.AffineDisperser.pow_eq_sum_powerTable`: a root power has the coordinates stored in the
  table.

## References

* [E. Ben-Sasson, S. Kopparty, *Affine dispersers from subspace polynomials*]
  [BenSassonKopparty2012]
-/

@[expose] public section

namespace Cslib.AffineDisperser

open Cslib.BitString Polynomial

/-- The coefficient lists of the remainders of `X ^ e`, `e < 2 (g.length - 1)`, modulo the
polynomial with coefficient list `g`. -/
def powerTable (g : List Bool) : List (List Bool) :=
  (List.range (2 * (g.length - 1))).map fun e => modBits g (List.replicate e false ++ [true])

private theorem length_powerTable (g : List Bool) : (powerTable g).length = 2 * (g.length - 1) := by
  simp [powerTable]

/-- At a root `α` of the polynomial with coefficient list `l ++ [true]`, the power `α ^ e`,
`e < 2 l.length`, is the combination of the powers below `l.length` given by `powerTable`. -/
theorem pow_eq_sum_powerTable {A : Type*} [CommRing A] [Algebra (ZMod 2) A] (l : List Bool)
    {α : A} (hα : aeval α (polyOfBits (l ++ [true])) = 0) {e : ℕ} (he : e < 2 * l.length) :
    α ^ e = ∑ d ∈ Finset.range l.length,
      bitEquiv.symm (((powerTable (l ++ [true])).getD e []).getD d false) • α ^ d := by
  have hlen : (l ++ [true]).length - 1 = l.length := by simp
  have hget : (powerTable (l ++ [true])).getD e [] =
      modBits (l ++ [true]) (List.replicate e false ++ [true]) := by
    rw [List.getD_eq_getElem _ _ (by rw [length_powerTable, hlen]; exact he)]
    simp [powerTable]
  rw [hget, ← length_modBits l (List.replicate e false ++ [true]), ← aeval_polyOfBits]
  have h := mk_polyOfBits_modBits l (List.replicate e false ++ [true])
  rw [AdjoinRoot.mk_eq_mk, polyOfBits_replicate_append_true] at h
  have h0 := aeval_eq_zero_of_dvd_aeval_eq_zero h hα
  rw [map_sub, sub_eq_zero] at h0
  rw [h0, aeval_X_pow]

end Cslib.AffineDisperser
