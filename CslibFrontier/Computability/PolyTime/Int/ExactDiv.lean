/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
public import Mathlib.Data.Nat.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Plain polynomial-time signed integer division and modular reduction

Plain `Turing.MultiTapeTM.ComputableInPolyTime` certificates, exact-division identities, and
sign-magnitude code-length bounds for signed binary integer division and remainder over
`Turing.MultiTapeTM.encIntBin`:

* truncated-toward-zero division and remainder (`Int.tdiv`, `Int.tmod`);
* Euclidean division and nonnegative remainder (`Int.ediv`, `Int.emod`, and the `/` and `%`
  operators on `ℤ`);
* power-of-two modular reduction `Int.modPowTwo x ℓ = x % 2 ^ ℓ` with `ℓ` in unary
  `Turing.MultiTapeTM.encUnary`, used to recover integer counts modulo `2 ^ ℓ` in Appendix B.3
  of [OpenAI2026ETH].

All certificates are total (at divisor `0`, `a / 0 = 0`, `a.tdiv 0 = 0`, `a % 0 = a`, and
`a.tmod 0 = a`) and build on the binary natural division and modular reduction primitives of
`PolyTime/Nat/BinaryDiv` and `PolyTime/Int/BinaryDiv` without constructing new Turing machines.

## Main definitions

* `Int.modPowTwo`: least nonnegative residue `x % (2 : ℤ) ^ ℓ` modulo `2 ^ ℓ`.

## Main results

* `Int.ediv_mul_left_exact`, `Int.ediv_mul_right_exact`: exact Euclidean division of integer
  multiples `(d * q).ediv d = q` and `(q * d).ediv d = q` for `d ≠ 0`.
* `Int.modPowTwo_eq_of_dvd_sub`: unique recovery of `z ∈ [0, 2 ^ ℓ)` from any `x` with
  `2 ^ ℓ ∣ x - z`.
* `Int.size_natAbs_tdiv_le`, `Int.size_natAbs_ediv_le`, `Int.size_natAbs_emod_le_of_ne_zero`,
  `Int.size_natAbs_modPowTwo_le`, `Turing.MultiTapeTM.length_encIntBin_tdiv_le`,
  `Turing.MultiTapeTM.length_encIntBin_ediv_le`,
  `Turing.MultiTapeTM.length_encIntBin_emod_le_of_ne_zero`,
  `Turing.MultiTapeTM.length_encIntBin_emod_le_max`,
  `Turing.MultiTapeTM.length_encIntBin_modPowTwo_le`: binary magnitude and `encIntBin` code-length
  bounds.
* `Turing.MultiTapeTM.ComputableInPolyTime.intBin_tdiv`, `.intBin_tmod`, `.intBin_ediv`,
  `.intBin_emod`, `.intBin_div`, `.intBin_mod`, `.intBin_modPowTwo`: plain polynomial-time
  certificates and `@[fun_prop]` composition rules (`.intBin_tdiv'`, `.intBin_tmod'`,
  `.intBin_ediv'`, `.intBin_emod'`, `.intBin_div'`, `.intBin_mod'`, `.intBin_modPowTwo'`).

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Int

/-! ### Exact division and power-of-two modular reduction -/

/-- Least nonnegative residue of `x` modulo `2 ^ ℓ`, i.e., `x - 2 ^ ℓ * ⌊x / 2 ^ ℓ⌋`. -/
def modPowTwo (x : ℤ) (ℓ : ℕ) : ℤ :=
  x % (2 : ℤ) ^ ℓ

theorem modPowTwo_eq_emod (x : ℤ) (ℓ : ℕ) : x.modPowTwo ℓ = x.emod ((2 : ℤ) ^ ℓ) :=
  rfl

theorem modPowTwo_eq_sub_mul_ediv (x : ℤ) (ℓ : ℕ) :
    x.modPowTwo ℓ = x - (2 : ℤ) ^ ℓ * x.ediv ((2 : ℤ) ^ ℓ) :=
  Int.emod_def x ((2 : ℤ) ^ ℓ)

theorem modPowTwo_nonneg (x : ℤ) (ℓ : ℕ) : 0 ≤ x.modPowTwo ℓ :=
  Int.emod_nonneg x (by positivity)

theorem modPowTwo_lt (x : ℤ) (ℓ : ℕ) : x.modPowTwo ℓ < (2 : ℤ) ^ ℓ :=
  Int.emod_lt_of_pos x (by positivity)

theorem natAbs_modPowTwo_lt (x : ℤ) (ℓ : ℕ) : (x.modPowTwo ℓ).natAbs < 2 ^ ℓ :=
  Int.ofNat_lt.mp <| by
    rw [Int.natCast_natAbs, abs_of_nonneg (modPowTwo_nonneg x ℓ)]
    exact modPowTwo_lt x ℓ

/-- If `z ∈ [0, 2 ^ ℓ)` and `2 ^ ℓ` divides `x - z`, then `x.modPowTwo ℓ = z`. -/
theorem modPowTwo_eq_of_dvd_sub {x z : ℤ} {ℓ : ℕ} (hz₀ : 0 ≤ z) (hz₁ : z < (2 : ℤ) ^ ℓ)
    (hdvd : (2 : ℤ) ^ ℓ ∣ x - z) : x.modPowTwo ℓ = z := by
  obtain ⟨k, hk⟩ := hdvd
  rw [modPowTwo, show x = z + (2 : ℤ) ^ ℓ * k by lia, Int.add_mul_emod_self_left,
    Int.emod_eq_of_lt hz₀ hz₁]

/-- Exact Euclidean division of a left multiple `(d * q).ediv d = q` for `d ≠ 0`, stated directly
on `Int.ediv` for rewriting without folding to `/`. -/
theorem ediv_mul_left_exact {d : ℤ} (q : ℤ) (hd : d ≠ 0) : (d * q).ediv d = q :=
  Int.mul_ediv_cancel_left q hd

/-- Exact Euclidean division of a right multiple `(q * d).ediv d = q` for `d ≠ 0`, stated directly
on `Int.ediv` for rewriting without folding to `/`. -/
theorem ediv_mul_right_exact (q : ℤ) {d : ℤ} (hd : d ≠ 0) : (q * d).ediv d = q :=
  Int.mul_ediv_cancel q hd

/-! ### Sign-magnitude reductions and magnitude bounds -/

private theorem tdiv_eq_signMagnitude (a b : ℤ) :
    a.tdiv b =
      if (decide (a < 0) ^^ decide (b < 0)) then -((a.natAbs / b.natAbs : ℕ) : ℤ)
      else ((a.natAbs / b.natAbs : ℕ) : ℤ) := by
  rcases a with m | m <;> rcases b with (_ | n) | n <;>
    first
    | simp [Int.tdiv]
      done
    | dsimp only [Int.tdiv, Int.natAbs]
      split_ifs <;> lia

private theorem tmod_eq_signMagnitude (a b : ℤ) :
    a.tmod b =
      if decide (a < 0) then -((a.natAbs % b.natAbs : ℕ) : ℤ)
      else ((a.natAbs % b.natAbs : ℕ) : ℤ) := by
  rcases a with m | m <;> rcases b with (_ | n) | n <;> simp [Int.tmod]

private theorem ediv_eq_signMagnitude (a b : ℤ) :
    a.ediv b =
      if b = 0 then 0
      else if a < 0 then
        if b < 0 then (((a.natAbs - 1) / b.natAbs + 1 : ℕ) : ℤ)
        else -(((a.natAbs - 1) / b.natAbs + 1 : ℕ) : ℤ)
      else
        if b < 0 then -((a.natAbs / b.natAbs : ℕ) : ℤ)
        else ((a.natAbs / b.natAbs : ℕ) : ℤ) := by
  rcases a with m | m <;> rcases b with (_ | n) | n <;>
    first
    | simp [Int.ediv]
      done
    | simp only [Int.ediv, Int.natAbs, Int.ofNat_eq_natCast, Int.negSucc_eq]
      split_ifs <;> lia

private theorem emod_eq_signMagnitude (a b : ℤ) :
    a.emod b =
      if b = 0 then a
      else if a < 0 then (((b.natAbs - a.natAbs % b.natAbs) % b.natAbs : ℕ) : ℤ)
      else ((a.natAbs % b.natAbs : ℕ) : ℤ) := by
  change a % b = _
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hbn : a % b = a % (b.natAbs : ℤ) := by
    rcases le_or_gt 0 b with h | h
    · rw [Int.natAbs_of_nonneg h]
    · rw [show (b.natAbs : ℤ) = -b by lia, Int.emod_neg]
  simp only [hb, ↓reduceIte, hbn]
  by_cases ha : a < 0
  · simp only [ha, ↓reduceIte, Int.emod_natAbs_of_neg ha (Int.natAbs_ne_zero.mpr hb)]
    split_ifs with hdiv
    · rw [Int.emod_eq_zero_of_dvd hdiv, Nat.sub_zero, Nat.mod_self, Nat.cast_zero]
    · have := Int.emod_nonneg a (Int.natCast_ne_zero.mpr (Int.natAbs_ne_zero.mpr hb))
      have := Int.emod_lt_of_pos a (Nat.cast_pos.mpr (Int.natAbs_pos.mpr hb))
      have : a % (b.natAbs : ℤ) ≠ 0 := fun h0 => hdiv (Int.dvd_of_emod_eq_zero h0)
      rw [Nat.mod_eq_of_lt (by lia)]
      lia
  · simp only [ha, ↓reduceIte, Int.emod_natAbs_of_nonneg (not_lt.mp ha)]
    exact (Int.toNat_of_nonneg
      (Int.emod_nonneg a (Int.natCast_ne_zero.mpr (Int.natAbs_ne_zero.mpr hb)))).symm

theorem natAbs_emod_lt_of_ne_zero (a : ℤ) {b : ℤ} (hb : b ≠ 0) :
    (a.emod b).natAbs < b.natAbs :=
  Int.ofNat_lt.mp <| by
    change ((a % b).natAbs : ℤ) < (b.natAbs : ℤ)
    rw [Int.natCast_natAbs, abs_of_nonneg (Int.emod_nonneg a hb)]
    exact Int.emod_lt a hb

theorem size_natAbs_tdiv_le (a b : ℤ) : (a.tdiv b).natAbs.size ≤ a.natAbs.size :=
  Nat.size_le_size (Int.natAbs_tdiv_le_natAbs a b)

theorem size_natAbs_ediv_le (a b : ℤ) : (a.ediv b).natAbs.size ≤ a.natAbs.size :=
  Nat.size_le_size (Int.natAbs_ediv_le_natAbs a b)

theorem size_natAbs_emod_le_of_ne_zero (a : ℤ) {b : ℤ} (hb : b ≠ 0) :
    (a.emod b).natAbs.size ≤ b.natAbs.size :=
  Nat.size_le_size (natAbs_emod_lt_of_ne_zero a hb).le

theorem size_natAbs_modPowTwo_le (x : ℤ) (ℓ : ℕ) : (x.modPowTwo ℓ).natAbs.size ≤ ℓ :=
  Nat.size_le.mpr (natAbs_modPowTwo_lt x ℓ)

end Int

namespace Turing.MultiTapeTM

/-! ### Sign-magnitude `encIntBin` code-length bounds -/

/-- Truncated integer division never increases the `encIntBin` code length of the dividend. -/
theorem length_encIntBin_tdiv_le (a b : ℤ) :
    (encIntBin (a.tdiv b)).length ≤ (encIntBin a).length := by
  simp only [length_encIntBin]
  exact Nat.add_le_add_right (Int.size_natAbs_tdiv_le a b) 1

/-- Euclidean integer division never increases the `encIntBin` code length of the dividend. -/
theorem length_encIntBin_ediv_le (a b : ℤ) :
    (encIntBin (a.ediv b)).length ≤ (encIntBin a).length := by
  simp only [length_encIntBin]
  exact Nat.add_le_add_right (Int.size_natAbs_ediv_le a b) 1

/-- For `b ≠ 0`, the Euclidean remainder `a.emod b` has `encIntBin` code length at most
`(encIntBin b).length`. -/
theorem length_encIntBin_emod_le_of_ne_zero (a : ℤ) {b : ℤ} (hb : b ≠ 0) :
    (encIntBin (a.emod b)).length ≤ (encIntBin b).length := by
  simp only [length_encIntBin]
  exact Nat.add_le_add_right (Int.size_natAbs_emod_le_of_ne_zero a hb) 1

/-- Unconditionally on `b` (including `b = 0`),
`(encIntBin (a.emod b)).length ≤ max (encIntBin a).length (encIntBin b).length`. -/
theorem length_encIntBin_emod_le_max (a b : ℤ) :
    (encIntBin (a.emod b)).length ≤ max (encIntBin a).length (encIntBin b).length := by
  rcases eq_or_ne b 0 with rfl | hb
  · change (encIntBin (a % 0)).length ≤ _
    simp
  · exact (length_encIntBin_emod_le_of_ne_zero a hb).trans (le_max_right _ _)

/-- Reducing modulo `2 ^ ℓ` produces an `encIntBin` code of length at most `ℓ + 1`. -/
theorem length_encIntBin_modPowTwo_le (x : ℤ) (ℓ : ℕ) :
    (encIntBin (x.modPowTwo ℓ)).length ≤ ℓ + 1 := by
  rw [length_encIntBin]
  exact Nat.add_le_add_right (Int.size_natAbs_modPowTwo_le x ℓ) 1

end Turing.MultiTapeTM

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-! ### Plain polynomial-time certificates -/

/-- Truncated-toward-zero division of signed binary integers is computable in polynomial time. -/
@[fun_prop]
theorem intBin_tdiv :
    ComputableInPolyTime (fun p : ℤ × ℤ => p.1.tdiv p.2)
      (encPair encIntBin encIntBin) encIntBin := by
  simp only [Int.tdiv_eq_signMagnitude]
  fun_prop

/-- Truncated-toward-zero division of computed binary integers. -/
@[fun_prop]
theorem intBin_tdiv' {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime (fun a => (left a).tdiv (right a)) input encIntBin :=
  intBin_tdiv.comp (hleft.prod hright)

/-- Truncated-toward-zero remainder of signed binary integers is computable in polynomial time. -/
@[fun_prop]
theorem intBin_tmod :
    ComputableInPolyTime (fun p : ℤ × ℤ => p.1.tmod p.2)
      (encPair encIntBin encIntBin) encIntBin := by
  have : ComputableInPolyTime (fun p : ℤ × ℤ => p.1.natAbs % p.2.natAbs)
      (encPair encIntBin encIntBin) encNat := binary_mod' (by fun_prop) (by fun_prop)
  simp only [Int.tmod_eq_signMagnitude]
  fun_prop

/-- Truncated-toward-zero remainder of computed binary integers. -/
@[fun_prop]
theorem intBin_tmod' {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime (fun a => (left a).tmod (right a)) input encIntBin :=
  intBin_tmod.comp (hleft.prod hright)

/-- Euclidean division (`Int.ediv`) of signed binary integers is computable in polynomial time. -/
@[fun_prop]
theorem intBin_ediv :
    ComputableInPolyTime (fun p : ℤ × ℤ => p.1.ediv p.2)
      (encPair encIntBin encIntBin) encIntBin := by
  simp only [Int.ediv_eq_signMagnitude]
  fun_prop

/-- Euclidean division (`Int.ediv`) of computed binary integers. -/
@[fun_prop]
theorem intBin_ediv' {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime (fun a => (left a).ediv (right a)) input encIntBin :=
  intBin_ediv.comp (hleft.prod hright)

/-- Euclidean division (`/`) of signed binary integers is computable in polynomial time. -/
@[fun_prop]
theorem intBin_div :
    ComputableInPolyTime (fun p : ℤ × ℤ => p.1 / p.2)
      (encPair encIntBin encIntBin) encIntBin :=
  intBin_ediv

/-- Euclidean division (`/`) of computed binary integers. -/
@[fun_prop]
theorem intBin_div' {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime (fun a => left a / right a) input encIntBin :=
  intBin_div.comp (hleft.prod hright)

/-- Euclidean remainder (`Int.emod`) of signed binary integers is computable in polynomial time. -/
@[fun_prop]
theorem intBin_emod :
    ComputableInPolyTime (fun p : ℤ × ℤ => p.1.emod p.2)
      (encPair encIntBin encIntBin) encIntBin := by
  have : ComputableInPolyTime (fun p : ℤ × ℤ => p.1.natAbs % p.2.natAbs)
      (encPair encIntBin encIntBin) encNat := binary_mod' (by fun_prop) (by fun_prop)
  have : ComputableInPolyTime
      (fun p : ℤ × ℤ => (p.2.natAbs - p.1.natAbs % p.2.natAbs) % p.2.natAbs)
      (encPair encIntBin encIntBin) encNat := binary_mod' (by fun_prop) (by fun_prop)
  simp only [Int.emod_eq_signMagnitude]
  fun_prop

/-- Euclidean remainder (`Int.emod`) of computed binary integers. -/
@[fun_prop]
theorem intBin_emod' {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime (fun a => (left a).emod (right a)) input encIntBin :=
  intBin_emod.comp (hleft.prod hright)

/-- Euclidean remainder (`%`) of signed binary integers is computable in polynomial time. -/
@[fun_prop]
theorem intBin_mod :
    ComputableInPolyTime (fun p : ℤ × ℤ => p.1 % p.2)
      (encPair encIntBin encIntBin) encIntBin :=
  intBin_emod

/-- Euclidean remainder (`%`) of computed binary integers. -/
@[fun_prop]
theorem intBin_mod' {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime (fun a => left a % right a) input encIntBin :=
  intBin_mod.comp (hleft.prod hright)

/-- Reduction `Int.modPowTwo p.1 p.2 = p.1 % 2 ^ p.2` of a binary integer modulo `2 ^ ℓ` (with
`ℓ` in unary) is computable in polynomial time. -/
@[fun_prop]
theorem intBin_modPowTwo :
    ComputableInPolyTime (fun p : ℤ × ℕ => p.1.modPowTwo p.2)
      (encPair encIntBin encUnary) encIntBin := by
  unfold Int.modPowTwo
  fun_prop

/-- Reduction `Int.modPowTwo (value a) (exponent a)` of a computed binary integer modulo a
computed unary power of two. -/
@[fun_prop]
theorem intBin_modPowTwo' {α : Type} {input : α ↪ List Bool} {value : α → ℤ} {exponent : α → ℕ}
    (hvalue : ComputableInPolyTime value input encIntBin)
    (hexponent : ComputableInPolyTime exponent input encUnary) :
    ComputableInPolyTime (fun a => (value a).modPowTwo (exponent a)) input encIntBin :=
  intBin_modPowTwo.comp (hvalue.prod hexponent)

end Turing.MultiTapeTM.ComputableInPolyTime
