/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ModGates
public import CslibFrontier.Foundations.BooleanAnalysis.LowDegree
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Smolensky's gate approximators

Over a commutative ring `R` of prime characteristic `p`, such as `ZMod p` or the fields of order
`p ^ k` in which Smolensky works [Smolensky1987], every gate of the AC⁰[p] basis has a polynomial
approximator that multiplies degrees by at most `(p - 1) ℓ`:

* `MOD_p` of bits `u₁, …, u_m` is exactly `(∑ uᵢ) ^ (p - 1)`, since the sum is the image of the
  count in the prime field `ZMod p`, where nonzero elements have `(p - 1)`-st power `1`
  (`natCast_pow_eq_bitVal`, `modApprox`);
* OR of `u₁, …, u_m` is approximated by `1 - ∏_{j < ℓ} (1 - (∑_{i ∈ T j} uᵢ) ^ (p - 1))` for a tuple
  `T` of `ℓ` sets of arguments (`orApprox`), and AND is its De Morgan dual;
* negation is exactly `1 - u`.

For a nonzero Boolean vector, adding or removing a true coordinate changes the count of a set by
one, so at most half of the sets have a count divisible by `p`, and at most a `2 ^ (-ℓ)` fraction of
the tuples err (`card_orApprox_wrong_mul_le`). Double counting over the inputs gives, for every
gate and every way its arguments depend on the input, an approximator that errs on at most
`2 ^ n / 2 ^ ℓ` inputs (`exists_gate_approx`) [Razborov1987], [Smolensky1987],
[Jukna, Chapter 12][Jukna2012].

## Main definitions

* `Cslib.Circuits.Boolean.Smolensky.orApprox`, `Cslib.Circuits.Boolean.Smolensky.andApprox`: the
  approximators of OR and AND for a tuple of sets of arguments.
* `Cslib.Circuits.Boolean.Smolensky.modApprox`: the `MOD_p` polynomial.

## Main results

* `Cslib.Circuits.Boolean.Smolensky.natCast_pow_eq_bitVal`: Fermat's little theorem for counts in
  characteristic `p`.
* `Cslib.Circuits.Boolean.Smolensky.exists_gate_approx`: the gate approximators.

## References

* [A. A. Razborov, *Lower bounds on the size of bounded depth circuits over a complete basis with
  logical addition*][Razborov1987]
* [R. Smolensky, *Algebraic methods in the theory of lower bounds for Boolean circuit
  complexity*][Smolensky1987]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Smolensky

open Finset BitString
open scoped symmDiff

variable {R : Type*} [CommRing R] {n m ℓ : ℕ}

section Approximators

variable (p : ℕ)

/-- The OR approximator of characteristic `p` for a tuple `T` of `ℓ` sets of arguments. -/
def orApprox (T : Fin ℓ → Finset (Fin m)) (u : Fin m → R) : R :=
  1 - ∏ j, (1 - (∑ i ∈ T j, u i) ^ (p - 1))

/-- The AND approximator, the De Morgan dual of `orApprox`. -/
def andApprox (T : Fin ℓ → Finset (Fin m)) (u : Fin m → R) : R :=
  1 - orApprox p T fun i => 1 - u i

/-- The `MOD_p` polynomial, exact in characteristic `p`. -/
def modApprox (u : Fin m → R) : R :=
  (∑ i, u i) ^ (p - 1)

/-- Composing `orApprox p T` with degree-`D` polynomials yields a polynomial of degree at most
`ℓ * ((p - 1) * D)`. -/
theorem orApprox_comp_mem {D : ℕ} (T : Fin ℓ → Finset (Fin m)) {v : Fin m → BitString n → R}
    (hv : ∀ k, v k ∈ lowDegree R (Fin n) D) :
    (fun x => orApprox p T fun k => v k x) ∈ lowDegree R (Fin n) (ℓ * ((p - 1) * D)) := by
  convert one_sub_mem_lowDegree (prod_mem_lowDegree (R := R) (ι := Fin n) univ
    (a := (p - 1) * D) (f := fun j => 1 - (∑ i ∈ T j, v i) ^ (p - 1)) fun j _ =>
      one_sub_mem_lowDegree (pow_mem_lowDegree (sum_mem_lowDegree (T j) fun i _ => hv i) (p - 1)))
    using 2
  · simp
  · simp [orApprox]

/-- Composing `andApprox p T` with degree-`D` polynomials yields a polynomial of degree at most
`ℓ * ((p - 1) * D)`. -/
theorem andApprox_comp_mem {D : ℕ} (T : Fin ℓ → Finset (Fin m)) {v : Fin m → BitString n → R}
    (hv : ∀ k, v k ∈ lowDegree R (Fin n) D) :
    (fun x => andApprox p T fun k => v k x) ∈ lowDegree R (Fin n) (ℓ * ((p - 1) * D)) := by
  convert one_sub_mem_lowDegree (orApprox_comp_mem p T fun k => one_sub_mem_lowDegree (hv k))
    using 1
  funext x
  simp [andApprox]

/-- Composing `modApprox p` with degree-`D` polynomials yields a polynomial of degree at most
`(p - 1) * D`. -/
theorem modApprox_comp_mem {D : ℕ} {v : Fin m → BitString n → R}
    (hv : ∀ k, v k ∈ lowDegree R (Fin n) D) :
    (fun x => modApprox p fun k => v k x) ∈ lowDegree R (Fin n) ((p - 1) * D) := by
  convert pow_mem_lowDegree (sum_mem_lowDegree univ fun i _ => hv i) (p - 1) using 1
  funext x
  simp [modApprox, Finset.sum_apply]

end Approximators

/-! ### Sums of bits -/

/-- A sum of bits is their count. -/
private theorem sum_bitVal (S : Finset (Fin m)) (u : Fin m → Bool) :
    ∑ i ∈ S, bitVal R (u i) = (#(S.filter fun i => u i = true) : R) := by
  simp only [bitVal, ← Finset.sum_boole]

/-- If some coordinate is true, at most half of the sets have a sum of bits equal to zero. -/
private theorem two_mul_card_sum_eq_zero_le [Nontrivial R] [DecidableEq R] (u : Fin m → Bool)
    {k : Fin m}
    (hk : u k = true) :
    2 * #(univ.filter fun S : Finset (Fin m) => ∑ i ∈ S, bitVal R (u i) = 0) ≤ 2 ^ m := by
  set Z := univ.filter fun S : Finset (Fin m) => ∑ i ∈ S, bitVal R (u i) = 0
  set NZ := univ.filter fun S : Finset (Fin m) => ¬∑ i ∈ S, bitVal R (u i) = 0
  have htotal : #Z + #NZ = 2 ^ m := by simp [Z, NZ, card_filter_add_card_filter_not]
  have hle : #Z ≤ #NZ :=
    Finset.card_le_card_of_injOn (· ∆ {k}) (fun S hS => by
      simp only [Z, NZ, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hS ⊢
      by_cases hkS : k ∈ S
      · rw [symmDiff_of_ge (Finset.singleton_subset_iff.2 hkS), Finset.sdiff_singleton_eq_erase,
          Finset.sum_erase_eq_sub hkS, hS, hk, bitVal_true, zero_sub]
        exact neg_ne_zero.2 one_ne_zero
      · rw [(Finset.disjoint_singleton_right.2 hkS).symmDiff_eq_sup,
          Finset.sum_union (Finset.disjoint_singleton_right.2 hkS), Finset.sum_singleton, hS, hk,
          bitVal_true, zero_add]
        exact one_ne_zero)
      fun _ _ _ _ hST => by simpa only [symmDiff_symmDiff_cancel_right] using congrArg (· ∆ {k}) hST
  omega

/-! ### Exactness in characteristic `p` -/

variable {p : ℕ} [Fact p.Prime]

private theorem orApprox_bitVal_of_forall_false (T : Fin ℓ → Finset (Fin m)) (u : Fin m → Bool)
    (hu : ∀ i, u i = false) : orApprox p T (fun i => bitVal R (u i)) = 0 := by
  have hp := (Fact.out : p.Prime).two_le
  simp [orApprox, hu, bitVal, zero_pow (show p - 1 ≠ 0 by omega)]

variable [CharP R p]

/-- The `(p - 1)`-st power of a count is whether the count is not divisible by `p`: in
characteristic `p` the count is the image of its residue in `ZMod p`, where Fermat's little
theorem applies. -/
theorem natCast_pow_eq_bitVal (c : ℕ) :
    (c : R) ^ (p - 1) = bitVal R (decide (c % p ≠ 0)) := by
  have hp := (Fact.out : p.Prime).two_le
  by_cases hc : c % p = 0
  · rw [(CharP.cast_eq_zero_iff R p c).2 (Nat.dvd_of_mod_eq_zero hc), zero_pow (by omega)]
    simp [hc, bitVal]
  · have h := congrArg (ZMod.castHom (dvd_refl p) R) (ZMod.pow_card_sub_one_eq_one
      fun h => hc (Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff c p).1 h)))
    rw [map_pow, map_natCast, map_one] at h
    simp [h, hc, bitVal]

/-- The `MOD_p` polynomial is exact on bits. -/
private theorem modApprox_bitVal (u : Fin m → Bool) :
    modApprox p (fun i => bitVal R (u i)) = bitVal R (modGate p m u) := by
  rw [modApprox, sum_bitVal, natCast_pow_eq_bitVal]
  rfl

private theorem orApprox_bitVal_of_exists (T : Fin ℓ → Finset (Fin m)) (u : Fin m → Bool)
    (hT : ∃ j, ∑ i ∈ T j, bitVal R (u i) ≠ 0) :
    orApprox p T (fun i => bitVal R (u i)) = 1 := by
  obtain ⟨j, hj⟩ := hT
  rw [sum_bitVal] at hj
  have hmod : #((T j).filter fun i => u i = true) % p ≠ 0 :=
    fun h => hj ((CharP.cast_eq_zero_iff R p _).2 (Nat.dvd_of_mod_eq_zero h))
  unfold orApprox
  rw [Finset.prod_eq_zero (Finset.mem_univ j)
    (by simp [natCast_pow_eq_bitVal, hmod, bitVal]), sub_zero]

/-! ### Counting erring tuples -/

variable [DecidableEq R]

/-- At most a `2 ^ (-ℓ)` fraction of the tuples make the OR approximator err on a fixed Boolean
vector. -/
theorem card_orApprox_wrong_mul_le (u : Fin m → Bool) :
    #(univ.filter fun T : Fin ℓ → Finset (Fin m) => orApprox p T (fun i => bitVal R (u i)) ≠
        bitVal R (decide (∃ j, u j = true))) * 2 ^ ℓ ≤ (2 ^ m) ^ ℓ := by
  by_cases hex : ∃ k, u k = true
  · obtain ⟨k, hk⟩ := hex
    set Z := univ.filter fun S : Finset (Fin m) => ∑ i ∈ S, bitVal R (u i) = 0
    have : Nontrivial R := CharP.nontrivial_of_char_ne_one (Fact.out : p.Prime).ne_one
    calc _ ≤ #(Fintype.piFinset fun _ : Fin ℓ => Z) * 2 ^ ℓ :=
          Nat.mul_le_mul_right _ <| card_le_card fun T hT => Fintype.mem_piFinset.2 fun j => by
            simp only [Z, mem_filter, mem_univ, true_and, show (∃ j, u j = true) from ⟨k, hk⟩,
              decide_true] at hT ⊢
            exact of_not_not fun hj => hT (orApprox_bitVal_of_exists T u ⟨j, hj⟩)
      _ = (2 * #Z) ^ ℓ := by simp [Fintype.card_piFinset, mul_pow, mul_comm]
      _ ≤ (2 ^ m) ^ ℓ := Nat.pow_le_pow_left (two_mul_card_sum_eq_zero_le u hk) ℓ
  · simp only [not_exists, Bool.not_eq_true] at hex
    rw [filter_false_of_mem fun T _ => by
      rw [orApprox_bitVal_of_forall_false T u hex]
      simp [hex]]
    simp

/-- **Averaging over the inputs.** For arguments `u x` depending on the input, some tuple makes the
OR approximator err on at most `2 ^ n / 2 ^ ℓ` inputs. -/
private theorem exists_orApprox (u : BitString n → Fin m → Bool) :
    ∃ T : Fin ℓ → Finset (Fin m),
      #(univ.filter fun x => orApprox p T (fun i => bitVal R (u x i)) ≠
          bitVal R (decide (∃ j, u x j = true))) * 2 ^ ℓ ≤ 2 ^ n := by
  classical
  let Wrong (T : Fin ℓ → Finset (Fin m)) (x : BitString n) :=
    orApprox p T (fun i => bitVal R (u x i)) ≠ bitVal R (decide (∃ j, u x j = true))
  refine (exists_le_of_sum_le univ_nonempty ?_).imp fun _ hT => hT.2
  calc ∑ T, #(univ.filter fun x => Wrong T x) * 2 ^ ℓ
      = ∑ x, #(univ.filter fun T => Wrong T x) * 2 ^ ℓ := by
        simp only [card_filter, sum_mul]
        exact sum_comm
    _ ≤ ∑ _x : BitString n, (2 ^ m) ^ ℓ := sum_le_sum fun x _ => card_orApprox_wrong_mul_le (u x)
    _ = ∑ _T : Fin ℓ → Finset (Fin m), 2 ^ n := by simp; ring

/-- **Gate approximators.** Over a commutative ring `R` of characteristic `p`, for every operation
of the AC⁰[p] basis and every way `u` its arguments depend on the input, some approximator
multiplies degrees by at most `(p - 1) ℓ` and errs on at most `2 ^ n / 2 ^ ℓ` inputs. -/
theorem exists_gate_approx (hℓ : 1 ≤ ℓ) (op : Unbounded.extSignature.Op)
    (u : BitString n → Fin (Unbounded.extSignature.Arity op) → Bool) :
    ∃ A : (Fin (Unbounded.extSignature.Arity op) → R) → R,
      (∀ (D : ℕ) (v : Fin (Unbounded.extSignature.Arity op) → BitString n → R),
        (∀ k, v k ∈ lowDegree R (Fin n) D) →
          (fun x => A fun k => v k x) ∈ lowDegree R (Fin n) ((p - 1) * ℓ * D)) ∧
      #(univ.filter fun x => A (fun k => bitVal R (u x k)) ≠
          bitVal R (Unbounded.extInterpretation (modGate p) op (u x))) * 2 ^ ℓ ≤ 2 ^ n := by
  have hp := (Fact.out : p.Prime).two_le
  have hdeg (D : ℕ) : ℓ * ((p - 1) * D) = (p - 1) * ℓ * D := by ring
  cases op with
  | ac op =>
    cases op with
    | not =>
      refine ⟨fun u => 1 - u 0, fun D _ hv => lowDegree_mono
        (Nat.le_mul_of_pos_left D (Nat.mul_pos (by omega) hℓ)) (one_sub_mem_lowDegree (hv 0)), ?_⟩
      simp [Unbounded.extInterpretation, Unbounded.interpretation, bitVal_not]
    | or m =>
      obtain ⟨T, hT⟩ := exists_orApprox (R := R) (p := p) (ℓ := ℓ) u
      exact ⟨orApprox p T, fun D _ hv => hdeg D ▸ orApprox_comp_mem p T hv, hT⟩
    | and m =>
      obtain ⟨T, hT⟩ := exists_orApprox (R := R) (p := p) (ℓ := ℓ) fun x k => !u x k
      refine ⟨andApprox p T, fun D _ hv => hdeg D ▸ andApprox_comp_mem p T hv, ?_⟩
      convert hT using 4 with x
      have hd : decide (∀ j, u x j = true) = !decide (∃ j, (!u x j) = true) := by
        rw [Bool.eq_iff_iff, Bool.not_eq_true', decide_eq_true_iff, decide_eq_false_iff_not,
          not_exists]
        simp
      simp [andApprox, Unbounded.extInterpretation, Unbounded.interpretation, hd, bitVal_not]
  | gate m =>
    refine ⟨modApprox p, fun D _ hv => lowDegree_mono
      (Nat.mul_le_mul_right D (Nat.le_mul_of_pos_right _ hℓ)) (modApprox_comp_mem p hv), ?_⟩
    simp [Unbounded.extInterpretation, modApprox_bitVal]

end Cslib.Circuits.Boolean.Smolensky
