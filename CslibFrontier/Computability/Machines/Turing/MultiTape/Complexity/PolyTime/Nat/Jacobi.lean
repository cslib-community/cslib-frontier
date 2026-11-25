/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd
import CslibFrontier.Tactic.EncLen

/-!
# Polynomial-time Jacobi symbol on binary naturals

The Jacobi symbol `J(a | n)` (Mathlib's `jacobiSym`) is computable in polynomial time on binary
inputs. This is the symbol the Solovay–Strassen primality test
[Solovay and Strassen][SolovayStrassen1977] compares with `a ^ ((n - 1) / 2)` modulo `n`.

The algorithm runs a loop on states `(a, n, flip)` with `a < n`, keeping
`J(a₀ | n₀) = (-1) ^ flip · J(a | n)`. One step (`Turing.MultiTapeTM.BinaryJacobi.jacobiStep`):

* fixes the state once `a = 0`;
* for even `n`, returns `a = 0` if `a` is even too (both symbols vanish), and otherwise replaces
  `n` by `n / 2` and `a` by `a % (n / 2)`, since `J(a | 2) = 1` for odd `a`;
* for odd `n` and even `a`, halves `a`, flipping the sign when `n % 8 ∈ {3, 5}`
  (`jacobiSym.even_odd`);
* for odd `n` and odd `a`, replaces `(a, n)` by `(n % a, a)`, flipping the sign when
  `a % 4 = n % 4 = 3` (`jacobiSym.quadratic_reciprocity_if`).

Every step at least halves the product `a * n`; the odd–odd case is Euclid's halving
`Turing.MultiTapeTM.BinaryGcd.gcd_product_halving`. The initial product is below `n₀ ^ 2`, so
`2 * Nat.size n₀` steps reach `a = 0`, where `J(0 | n)` is `1` for `n = 1` and `0` otherwise
(`BinaryJacobi.jacobiReadout_iterate_jacobiStep`). The state never exceeds `max n₀ 1`, so its
encoding stays linear in the input length.

The reductions are those of Mathlib's private `fastJacobiSym`, which evaluates the symbol by
well-founded recursion. Here they are a counted loop, so that the iteration rule for
`ComputableInPolyTime` applies. The four loop definitions are exposed so that clients can run the
loop by `decide` on concrete inputs.

## Main definitions

* `Turing.MultiTapeTM.BinaryJacobi.State`, `.encState`: state `⟨num, mod, flip⟩` of the
  Jacobi-symbol loop and its framed binary encoding.
* `Turing.MultiTapeTM.BinaryJacobi.jacobiStep`: one reduction step on `State`.
* `Turing.MultiTapeTM.BinaryJacobi.jacobiInit`, `.jacobiCount`, `.jacobiReadout`: the initial
  state `⟨a % n, n, false⟩`, the step count `2 * Nat.size n`, and the final readout.

## Main results

* `Turing.MultiTapeTM.BinaryJacobi.jacobiReadout_iterate_jacobiStep`: `2 * Nat.size n` steps
  compute `J(a | n)` for every `a n : ℕ`, including even `n` and `n = 0`.
* `Turing.MultiTapeTM.ComputableInPolyTime.binary_jacobiSym`, `.binary_jacobiSym'`: the Jacobi
  symbol of binary naturals in polynomial time, as a binary signed integer.
* `Turing.MultiTapeTM.ComputableInPolyTime.intBin_jacobiSym`: the same for a binary signed
  numerator, by first reducing it modulo `n`.

## References

* [R. Solovay, V. Strassen, *A Fast Monte-Carlo Test for Primality*][SolovayStrassen1977]
-/

open NumberTheorySymbols

public section

namespace Turing.MultiTapeTM.BinaryJacobi

/-- State of the Jacobi-symbol loop: current numerator `num`, modulus `mod`, and accumulated sign
flip `flip`, representing `(-1) ^ flip · J(num | mod)` with `num < mod`. -/
@[ext] structure State where
  /-- Current numerator `a`, below `mod`. -/
  num : ℕ
  /-- Current modulus `n`. -/
  mod : ℕ
  /-- Whether the accumulated sign is `-1`. -/
  flip : Bool
  deriving DecidableEq, Repr

/-- Binary numerator and modulus, each framed, followed by the sign-flip bit. -/
enc_structure encState : State where
  num : encNat, mod : encNat, flip : encBool

/-- One step of the Jacobi-symbol loop on a state `s`, which stands for
`(-1) ^ s.flip · J(s.num | s.mod)` and satisfies `s.num < s.mod`. -/
@[expose] def jacobiStep (s : State) : State :=
  if s.num = 0 then s
  else if s.mod % 2 = 0 then
    if s.num % 2 = 0 then ⟨0, s.mod, s.flip⟩ else ⟨s.num % (s.mod / 2), s.mod / 2, s.flip⟩
  else if s.num % 2 = 0 then
    ⟨s.num / 2, s.mod, s.flip ^^ (decide (s.mod % 8 = 3) || decide (s.mod % 8 = 5))⟩
  else ⟨s.mod % s.num, s.num, s.flip ^^ (decide (s.num % 4 = 3) && decide (s.mod % 4 = 3))⟩

/-- The initial state `⟨a % n, n, false⟩` for `J(a | n)`, or `⟨0, 1, false⟩` when `n = 0`,
since `J(a | 0) = 1`. -/
@[expose] def jacobiInit (p : ℕ × ℕ) : State :=
  if p.2 = 0 then ⟨0, 1, false⟩ else ⟨p.1 % p.2, p.2, false⟩

/-- The number of loop steps for `J(a | n)`: `2 * Nat.size n`. -/
@[expose] def jacobiCount (p : ℕ × ℕ) : ℕ :=
  2 * p.2.size

/-- The value `(-1) ^ s.flip · J(0 | s.mod)` of a final state `⟨0, s.mod, s.flip⟩` with
`s.mod ≥ 1`. -/
@[expose] def jacobiReadout (s : State) : ℤ :=
  if s.mod = 1 then (if s.flip then -1 else 1) else 0

/-- The sign `(-1) ^ b`. -/
private def sign (b : Bool) : ℤ :=
  if b then -1 else 1

private theorem sign_xor (b c : Bool) : sign (b ^^ c) = sign b * sign c := by
  cases b <;> cases c <;> simp [sign]

/-- The loop invariant for the input `p`: the state stands for `J(p.1 | p.2)`, its numerator is
below its modulus, and the modulus is at most `max p.2 1`. -/
private def Invariant (p : ℕ × ℕ) (s : State) : Prop :=
  J((p.1 : ℤ) | p.2) = sign s.flip * J((s.num : ℤ) | s.mod) ∧ s.num < s.mod ∧ s.mod ≤ max p.2 1

private theorem invariant_jacobiInit (p : ℕ × ℕ) : Invariant p (jacobiInit p) := by
  obtain ⟨a, n⟩ := p
  unfold jacobiInit Invariant
  split_ifs with hn
  · subst hn
    simp [sign, jacobiSym.zero_right, jacobiSym.one_right]
  · refine ⟨?_, Nat.mod_lt _ (by omega), le_max_left _ _⟩
    simp only [sign, Bool.false_eq_true, ite_false, one_mul]
    rw [jacobiSym.mod_left, Int.natCast_mod]

/-- One step preserves the signed symbol. -/
private theorem sign_mul_jacobiSym_jacobiStep {s : State} (hs : s.num < s.mod) :
    sign (jacobiStep s).flip * J(((jacobiStep s).num : ℤ) | (jacobiStep s).mod) =
      sign s.flip * J((s.num : ℤ) | s.mod) := by
  obtain ⟨a, n, f⟩ := s
  simp only at hs
  unfold jacobiStep
  simp only
  split_ifs with ha0 hn2 ha2 ha2'
  · rfl
  · -- both even: both symbols vanish
    have hn1 : 1 < n := by omega
    have hz : J((a : ℤ) | n) = 0 := by
      refine jacobiSym.eq_zero_iff.2 ⟨by omega, fun hg => ?_⟩
      have h2 : 2 ∣ Int.gcd a n := by
        rw [Int.gcd_natCast_natCast]
        exact Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero ha2) (Nat.dvd_of_mod_eq_zero hn2)
      rw [hg] at h2
      omega
    rw [hz, Nat.cast_zero, jacobiSym.zero_left hn1]
  · -- `a` odd, `n` even: `J(a | n) = J(a | 2) · J(a | n / 2) = J(a | n / 2)`
    refine (congrArg (sign f * ·) ?_).symm
    have hodd : legendreSym 2 a = 1 := by
      simp only [legendreSym.mod 2 a, Int.ofNat_mod_ofNat, show a % 2 = 1 by omega]
      decide
    have : NeZero (n / 2) := ⟨by omega⟩
    conv_lhs => rw [show n = 2 * (n / 2) by omega]
    rw [jacobiSym.mul_right, ← jacobiSym.legendreSym.to_jacobiSym, hodd, one_mul,
      jacobiSym.mod_left, Int.natCast_mod]
  · -- `a` even, `n` odd: the second supplementary law
    rw [sign_xor, mul_assoc]
    congr 1
    rw [← jacobiSym.even_odd (a := (a : ℤ)) (b := n) (by omega) (by omega), Int.natCast_ediv,
      Nat.cast_ofNat]
    split_ifs with h8
    · rcases h8 with h8 | h8 <;> simp [sign, h8]
    · simp only [not_or] at h8
      simp [sign, h8.1, h8.2]
  · -- both odd: quadratic reciprocity
    rw [sign_xor, mul_assoc]
    congr 1
    rw [← jacobiSym.quadratic_reciprocity_if (a := a) (b := n) (by omega) (by omega),
      jacobiSym.mod_left (n : ℤ) a, ← Int.natCast_mod]
    split_ifs with h4
    · simp [sign, h4.1, h4.2]
    · simp only [not_and] at h4
      by_cases h1 : a % 4 = 3 <;> simp [sign, h1, h4]

private theorem lt_jacobiStep {s : State} (hs : s.num < s.mod) :
    (jacobiStep s).num < (jacobiStep s).mod := by
  unfold jacobiStep
  split_ifs <;> first | exact hs | exact Nat.zero_lt_of_lt hs | exact Nat.mod_lt _ (by omega) |
    exact (Nat.div_le_self _ 2).trans_lt hs

private theorem mod_jacobiStep_le {s : State} (hs : s.num < s.mod) :
    (jacobiStep s).mod ≤ s.mod := by
  unfold jacobiStep
  split_ifs <;> first | exact le_rfl | exact Nat.div_le_self _ _ | exact hs.le

/-- Every step at least halves the product `s.num * s.mod`. -/
private theorem two_mul_mul_jacobiStep_le {s : State} (hs : s.num < s.mod) :
    2 * ((jacobiStep s).num * (jacobiStep s).mod) ≤ s.num * s.mod := by
  obtain ⟨a, n, f⟩ := s
  simp only at hs
  unfold jacobiStep
  simp only
  split_ifs with ha0 hn2 ha2 ha2'
  · simp [ha0]
  · simp
  · calc 2 * (a % (n / 2) * (n / 2)) = a % (n / 2) * n := by
          rw [mul_left_comm, show 2 * (n / 2) = n by omega]
      _ ≤ a * n := Nat.mul_le_mul_right n (Nat.mod_le a (n / 2))
  · rw [← mul_assoc, show 2 * (a / 2) = a by omega]
  · exact mul_comm (n % a) a ▸ BinaryGcd.gcd_product_halving (by omega) hs.le

/-- After `i` steps the invariant holds and `2 ^ i` times the product `num * mod` is still below
`2 ^ jacobiCount p`. -/
private theorem invariant_iterate_jacobiStep (p : ℕ × ℕ) (i : ℕ) :
    Invariant p (jacobiStep^[i] (jacobiInit p)) ∧
      2 ^ i * ((jacobiStep^[i] (jacobiInit p)).num * (jacobiStep^[i] (jacobiInit p)).mod) <
        2 ^ jacobiCount p := by
  induction i with
  | zero =>
    refine ⟨invariant_jacobiInit p, ?_⟩
    obtain ⟨a, n⟩ := p
    unfold jacobiInit jacobiCount
    simp only [pow_zero, one_mul, Function.iterate_zero, id]
    split_ifs with hn
    · simp
    · have h2 : n < 2 ^ n.size := Nat.lt_size_self n
      calc a % n * n < n * n := Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (by omega)) (by omega)
        _ ≤ 2 ^ n.size * 2 ^ n.size := Nat.mul_le_mul h2.le h2.le
        _ = 2 ^ (2 * n.size) := by rw [← pow_add, two_mul]
  | succ i ih =>
    obtain ⟨⟨hJ, hlt, hle⟩, hprod⟩ := ih
    rw [Function.iterate_succ_apply']
    set s := jacobiStep^[i] (jacobiInit p)
    refine ⟨⟨hJ.trans (sign_mul_jacobiSym_jacobiStep hlt).symm, lt_jacobiStep hlt,
      (mod_jacobiStep_le hlt).trans hle⟩, ?_⟩
    calc 2 ^ (i + 1) * ((jacobiStep s).num * (jacobiStep s).mod)
        = 2 ^ i * (2 * ((jacobiStep s).num * (jacobiStep s).mod)) := by ring
      _ ≤ 2 ^ i * (s.num * s.mod) := Nat.mul_le_mul_left _ (two_mul_mul_jacobiStep_le hlt)
      _ < 2 ^ jacobiCount p := hprod

/-- **Correctness and step bound.** For all `a n : ℕ`, running `jacobiStep` for
`2 * Nat.size n` steps from `jacobiInit (a, n)` and reading out gives `J(a | n)`. -/
theorem jacobiReadout_iterate_jacobiStep (p : ℕ × ℕ) :
    jacobiReadout (jacobiStep^[jacobiCount p] (jacobiInit p)) = J((p.1 : ℤ) | p.2) := by
  obtain ⟨⟨hJ, hlt, -⟩, hprod⟩ := invariant_iterate_jacobiStep p (jacobiCount p)
  set s := jacobiStep^[jacobiCount p] (jacobiInit p)
  have hzero : s.num = 0 := by
    by_contra h
    have hpos : 1 ≤ s.num * s.mod := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero h (by omega))
    have := Nat.le_mul_of_pos_right (2 ^ jacobiCount p) hpos
    omega
  have hread : jacobiReadout s = if s.mod = 1 then sign s.flip else 0 := rfl
  rw [hread, hJ, hzero, Nat.cast_zero]
  split_ifs with h1
  · rw [h1, jacobiSym.one_right, mul_one]
  · have hn : 1 < s.mod := by omega
    rw [jacobiSym.zero_left hn, mul_zero]

/-- Every reachable state has encoding length at most `4 * |(a, n)| + 4`. -/
private theorem length_encState_iterate_jacobiStep_le (p : ℕ × ℕ) (i : ℕ) :
    (encState (jacobiStep^[i] (jacobiInit p))).length ≤
      4 * (encPair encNat encNat p).length + 4 := by
  obtain ⟨⟨-, hlt, hle⟩, -⟩ := invariant_iterate_jacobiStep p i
  set s := jacobiStep^[i] (jacobiInit p)
  have hm : (max p.2 1).size ≤ p.2.size + 1 := by
    rcases le_total p.2 1 with h | h
    · rw [max_eq_right h]
      simp
    · rw [max_eq_left h]
      omega
  have hs1 : s.num.size ≤ p.2.size + 1 := (Nat.size_le_size (hlt.le.trans hle)).trans hm
  have hs2 : s.mod.size ≤ p.2.size + 1 := (Nat.size_le_size hle).trans hm
  enc_len [encState_apply, encStateFields, encNat_apply, List.length_singleton,
    Nat.size_eq_bits_len] at hs1 hs2 ⊢

end Turing.MultiTapeTM.BinaryJacobi

namespace Turing.MultiTapeTM.ComputableInPolyTime

open BinaryJacobi

/-- **The Jacobi symbol in polynomial time.** `J(a | n)` of binary naturals `a, n`, returned as a
binary signed integer, for every `a` and `n` (even `n` and `n = 0` included). -/
@[fun_prop, program_certificate]
theorem binary_jacobiSym : ComputableInPolyTime (fun p : ℕ × ℕ => J((p.1 : ℤ) | p.2))
    (encPair encNat encNat) encIntBin := by
  have hcount : ComputableInPolyTime jacobiCount (encPair encNat encNat) encUnary := by
    unfold jacobiCount
    fun_prop
  have hinit : ComputableInPolyTime jacobiInit (encPair encNat encNat) encState := by
    have hmod := binary_mod' (fst encNat encNat) (snd encNat encNat)
    unfold jacobiInit
    fun_prop
  have hstep : ComputableInPolyTime jacobiStep encState encState := by
    have ha : ComputableInPolyTime State.num encState encNat := by fun_prop
    have hn : ComputableInPolyTime State.mod encState encNat := by fun_prop
    have ha2 := binary_mod' ha (const 2)
    have hn2 := binary_mod' hn (const 2)
    have hn4 := binary_mod' hn (const 4)
    have ha4 := binary_mod' ha (const 4)
    have hn8 := binary_mod' hn (const 8)
    have hhalf := binary_div' hn (const 2)
    have hamod := binary_mod' ha hhalf
    have hswap := binary_mod' hn ha
    unfold jacobiStep
    fun_prop
  have hread : ComputableInPolyTime jacobiReadout encState encIntBin := by
    unfold jacobiReadout
    fun_prop
  have hiter := iterate hcount hinit hstep
    (bound := fun p => 4 * (encPair encNat encNat p).length + 4)
    (((PolyBounded.const 4).mul .self).add (.const 4))
    (fun p i _ => length_encState_iterate_jacobiStep_le p i)
  simpa only [Function.comp_def, jacobiReadout_iterate_jacobiStep] using hread.comp hiter

/-- The Jacobi symbol of computed binary naturals, fixing their intermediate encodings for proof
search. -/
@[fun_prop, program_certificate]
theorem binary_jacobiSym' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun x => J((left x : ℤ) | right x)) input encIntBin := by
  simpa only [Function.comp_def] using binary_jacobiSym.comp (hleft.prod hright)

/-- The Jacobi symbol `J(a | n)` of a binary signed integer `a` and a binary natural `n`, computed
as `J(a % n | n)`. -/
@[fun_prop, program_certificate]
theorem intBin_jacobiSym : ComputableInPolyTime (fun p : ℤ × ℕ => J(p.1 | p.2))
    (encPair encIntBin encNat) encIntBin := by
  have h := binary_jacobiSym' (intBin_emodNat' (fst encIntBin encNat) (snd encIntBin encNat))
    (snd encIntBin encNat)
  refine h.of_enc_eq fun p => congrArg encIntBin ?_
  rcases Nat.eq_zero_or_pos p.2 with hn | hn
  · rw [hn, jacobiSym.zero_right, jacobiSym.zero_right]
  · rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)), ← jacobiSym.mod_left]

end Turing.MultiTapeTM.ComputableInPolyTime
