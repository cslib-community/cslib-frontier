/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import Mathlib.Data.Nat.Prime.Defs
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Search
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.NumberTheory.Bertrand

/-!
# Primality and prime selection on unary naturals

A natural `p` is prime exactly when `2 ≤ p` and no `m` with `2 ≤ m < p` divides it
(`Turing.MultiTapeTM.ComputableInPolyTime.decide_prime_eq`). Testing every candidate below
`p` takes time polynomial in `p`, hence in the length of its unary encoding
(`Turing.MultiTapeTM.ComputableInPolyTime.unary_decide_prime`).

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.decide_prime_eq`: primality by trial division.
* `Turing.MultiTapeTM.ComputableInPolyTime.unary_decide_prime`: in polynomial time.
* `Cslib.bertrandPrime_spec`, `Turing.MultiTapeTM.ComputableInPolyTime.unary_bertrandPrime`:
  selecting a prime between a positive unary bound and twice that bound.
-/

public section

namespace Cslib

/-- The greatest prime at most `2 * B`, or zero for `B = 0`. -/
@[expose] def bertrandPrime (B : ℕ) : ℕ := Nat.findGreatest Nat.Prime (2 * B)

/-- For a positive lower bound, the prime selected by bounded search belongs to `(B, 2 * B]`. -/
theorem bertrandPrime_spec {B : ℕ} (hB : B ≠ 0) :
    (bertrandPrime B).Prime ∧ B < bertrandPrime B ∧ bertrandPrime B ≤ 2 * B := by
  obtain ⟨q, hq, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul B hB
  exact ⟨Nat.findGreatest_spec hle hq, hlt.trans_le (Nat.le_findGreatest hle hq),
    Nat.findGreatest_le _⟩

end Cslib

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Primality by trial division. -/
theorem decide_prime_eq (p : ℕ) : decide p.Prime =
    (decide (2 ≤ p) && (List.range p).all fun m => decide (m < 2) || decide (p % m ≠ 0)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.prime_def_lt']
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, ne_eq, Nat.dvd_iff_mod_eq_zero]
  refine and_congr_right fun _ => ⟨fun h m hm => ?_, fun h m h2 hm => ?_⟩
  · by_cases h2 : m < 2
    · exact Or.inl h2
    · exact Or.inr (h m (by omega) hm)
  · exact (h m hm).resolve_left (by omega)

/-- Primality of a unary natural, by trial division. -/
@[fun_prop]
theorem unary_decide_prime :
    ComputableInPolyTime (fun p : ℕ => decide p.Prime) encUnary encBool := by
  simp_rw [decide_prime_eq]
  fun_prop

/-- The selected prime can be computed in polynomial time when the bound is given in unary. -/
@[fun_prop]
theorem unary_bertrandPrime {α : Type} {enc : α ↪ List Bool} {B : α → ℕ}
    (hB : ComputableInPolyTime B enc encUnary) :
    ComputableInPolyTime (fun x => Cslib.bertrandPrime (B x)) enc encUnary :=
  findGreatest (by fun_prop) (unary_decide_prime.comp (.snd _ _))

end Turing.MultiTapeTM.ComputableInPolyTime
