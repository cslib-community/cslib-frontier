/-
Copyright (c) 2026 Bolton Bailey, Andrew Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Andrew Barnes
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.NumberTheory.Primality.StrongLiars
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Primality from a character-witness bound

This file proves a conditional algebraic criterion. Given a bound `B` for finding witnesses to
nonprincipal Dirichlet characters modulo an odd `n > 1`, primality is equivalent to every
integer base `2 ≤ a ≤ B` with `a < n` being a strong liar (`ZMod.IsStrongLiar`).

[Miller][Miller1976], Theorem 2 and the modification on pp. 308–309, gives an algorithm under
the extended Riemann hypothesis that first checks for perfect powers and then tests prime
bases. [Bach][Bach1990], p. 355 (abstract), gives the bound `2 (log n)²` for a compositeness
witness under the same hypothesis. Here `B` is a parameter and all integer bases in the stated
range are tested. Deriving the witness bound and proving an executable running-time bound
remain open in [cslib-frontier#6780](https://github.com/cslib-community/cslib-frontier/issues/6780).

Modulo an odd composite the strong liars lie in a proper subgroup `H` of the units
(`ZMod.exists_subgroup_ne_top_isStrongLiar`). A nontrivial character of the quotient by `H`
gives a nonprincipal Dirichlet character that is `1` on every strong liar, so its witness is a
base that fails the test. When the witness is not below `n`, the bound reaches `n` and the least
prime factor of `n` is a failing base instead.

## Main results

* `ZMod.prime_iff_forall_isStrongLiar_of_witness`: if each nonprincipal character has a witness
  up to `B`, an odd `n > 1` is prime if and only if all bases in the stated range are strong liars.

## References

* [G. L. Miller, *Riemann's hypothesis and tests for primality*][Miller1976]
* [E. Bach, *Explicit bounds for primality testing and related problems*][Bach1990]
-/

public section

namespace ZMod

/-- A proper subgroup of the units modulo `n ≠ 0` lies in the kernel of some nonprincipal
complex Dirichlet character modulo `n`. -/
private theorem exists_dirichletCharacter_ne_one_forall_mem {n : ℕ} [NeZero n]
    {H : Subgroup (ZMod n)ˣ} (hH : H ≠ ⊤) :
    ∃ χ : DirichletCharacter ℂ n, χ ≠ 1 ∧ ∀ u ∈ H, χ u = 1 := by
  obtain ⟨g, hg⟩ : ∃ g, g ∉ H := by
    by_contra! h
    exact hH (eq_top_iff.2 fun g _ => h g)
  have hg' : QuotientGroup.mk' H g ≠ 1 := by
    rwa [ne_eq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have : NeZero (Monoid.exponent ((ZMod n)ˣ ⧸ H)) :=
    ⟨(Monoid.exponent_pos_of_exists _ Nat.card_pos fun _ => pow_card_eq_one').ne'⟩
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity _ ℂ hg'
  refine ⟨MulChar.ofUnitHom (φ.comp (QuotientGroup.mk' H)), fun h => hφ ?_, fun u hu => ?_⟩
  · have hg1 := congrArg (fun χ : DirichletCharacter ℂ n => χ g) h
    simp only [MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulChar.one_apply_coe] at hg1
    exact Units.ext hg1
  · rw [MulChar.ofUnitHom_coe, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff u).2 hu, map_one, Units.val_one]

/-- A character separating the strong liars of a composite gives a failing base. -/
private theorem prime_of_forall_isStrongLiar_of_witness {n B : ℕ} (hodd : Odd n) (h1 : 1 < n)
    (hχ : ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 → ∃ a : ℕ, 0 < a ∧ a ≤ B ∧ χ a ≠ 1)
    (hliar : ∀ a : ℕ, 2 ≤ a → a ≤ B → a < n → IsStrongLiar n a) : n.Prime := by
  have : NeZero n := ⟨by omega⟩
  by_contra hn
  obtain ⟨H, hH, hsub⟩ := exists_subgroup_ne_top_isStrongLiar hodd h1 hn
  obtain ⟨χ, hχ1, hχH⟩ := exists_dirichletCharacter_ne_one_forall_mem hH
  obtain ⟨a, ha0, haB, ha⟩ := hχ χ hχ1
  rcases lt_or_ge a n with han | han
  · have ha2 : 2 ≤ a := by
      by_contra h
      obtain rfl : a = 1 := by omega
      exact ha (by simp)
    have hl := hliar a ha2 haB han
    have hu := hl.isUnit h1
    have h1a := hχH hu.unit (hsub hu.unit (by rwa [IsUnit.unit_spec]))
    rw [IsUnit.unit_spec] at h1a
    exact ha h1a
  · -- The bound reaches `n`, so the least prime factor of `n` is a base, and it is not a unit.
    have hp := Nat.minFac_prime h1.ne'
    have hpn := (Nat.not_prime_iff_minFac_lt h1).1 hn
    have hu := (hliar _ hp.two_le (by omega) hpn).isUnit h1
    rw [ZMod.isUnit_iff_coprime] at hu
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hu (Nat.minFac_dvd n))

/-- **Primality given a character-witness bound.** Suppose every nonprincipal complex Dirichlet
character modulo an odd `n > 1` differs from `1` at some `0 < a ≤ B`. Then `n` is prime if and
only if every base `2 ≤ a ≤ B` with `a < n` is a strong liar for `n`. -/
theorem prime_iff_forall_isStrongLiar_of_witness {n B : ℕ} (hodd : Odd n) (h1 : 1 < n)
    (hχ : ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 → ∃ a : ℕ, 0 < a ∧ a ≤ B ∧ χ a ≠ 1) :
    n.Prime ↔ ∀ a : ℕ, 2 ≤ a → a ≤ B → a < n → IsStrongLiar n a := by
  refine ⟨fun hp a ha2 _ han => ?_, prime_of_forall_isStrongLiar_of_witness hodd h1 hχ⟩
  have : Fact n.Prime := ⟨hp⟩
  exact isStrongLiar_of_prime fun h =>
    Nat.not_dvd_of_pos_of_lt (by omega) han ((ZMod.natCast_eq_zero_iff a n).1 h)

end ZMod
