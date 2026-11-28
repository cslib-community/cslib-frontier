/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Tactic.PolyTime.Init
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Search
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives
import CslibFrontier.Tactic.EncLen
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Data.Nat.Size

/-!
# Polynomial-time integer `k`-th roots on binary naturals

`Nat.nthRoot k m` (`⌊m ^ (1 / k)⌋`) is computable in polynomial time, with `k` in unary and `m`
in binary, by a most-significant-bit-first fold over the `m.size` bit positions: at position
`i`, the candidate bit `2 ^ i` is added to the running root `acc` whenever `(acc + 2 ^ i) ^ k ≤ m`
and `acc + 2 ^ i ≤ m`. The second test is implied by the first when `k ≠ 0`, and keeps every
intermediate root at most `m` also for `k = 0`.

The square root `Turing.MultiTapeTM.ComputableInPolyTime.binary_sqrt` is the case `k = 2`.

On unary naturals, the ceiling `⌈n ^ (p / q)⌉` of a rational power is a bounded search: it is
the greatest `m ≤ n ^ p` with `(m - 1) ^ q < n ^ p`.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.binary_nthRoot`, `.binary_nthRoot'`: plain
  polynomial-time integer `k`-th root `Nat.nthRoot` with unary `k` and binary radicand.
* `Turing.MultiTapeTM.ComputableInPolyTime.unary_ceil_rpow`: the ceiling `⌈n ^ (p / q)⌉` of a
  rational power, unary in and out.
-/

@[expose] public section

namespace Turing.MultiTapeTM

section Internal

private abbrev nthRootStep (p : ℕ × ℕ) (acc i : ℕ) : ℕ :=
  if decide ((acc + 2 ^ i) ^ p.1 ≤ p.2) && decide (acc + 2 ^ i ≤ p.2) then acc + 2 ^ i else acc

private theorem foldl_nthRootStep_le (p : ℕ × ℕ) :
    ∀ (l : List ℕ) {acc : ℕ}, acc ≤ p.2 → l.foldl (nthRootStep p) acc ≤ p.2
  | [], _, h => h
  | i :: l, acc, h => foldl_nthRootStep_le p l (by
    unfold nthRootStep
    split_ifs with hc
    · exact of_decide_eq_true ((Bool.and_eq_true _ _).mp hc).2
    · exact h)

private theorem foldl_nthRootStep_bounds {k m : ℕ} (hk : k ≠ 0) :
    ∀ (j acc : ℕ), acc ^ k ≤ m → m < (acc + 2 ^ j) ^ k →
      let r := (List.range j).reverse.foldl (nthRootStep (k, m)) acc
      r ^ k ≤ m ∧ m < (r + 1) ^ k
  | 0, acc, hle, hlt => by simpa using ⟨hle, hlt⟩
  | j + 1, acc, hle, hlt => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldl_cons]
    unfold nthRootStep
    dsimp only
    by_cases hcand : (acc + 2 ^ j) ^ k ≤ m
    · simp only [hcand, (Nat.le_self_pow hk _).trans hcand, decide_true, Bool.and_self, ↓reduceIte]
      exact foldl_nthRootStep_bounds hk j (acc + 2 ^ j) hcand
        (by rwa [show acc + 2 ^ j + 2 ^ j = acc + 2 ^ (j + 1) by ring])
    · simp only [hcand, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact foldl_nthRootStep_bounds hk j acc hle (Nat.lt_of_not_ge hcand)

private theorem foldl_nthRootStep_eq_nthRoot {k : ℕ} (hk : k ≠ 0) (m : ℕ) :
    (List.range m.size).reverse.foldl (nthRootStep (k, m)) 0 = Nat.nthRoot k m := by
  obtain ⟨hle, hlt⟩ := foldl_nthRootStep_bounds hk m.size 0 (by simp [zero_pow hk])
    (by simpa only [zero_add] using (Nat.lt_size_self m).trans_le (Nat.le_self_pow hk _))
  exact (Nat.nthRoot_eq_of_le_of_lt hle hlt).symm

end Internal

namespace ComputableInPolyTime

/-- Integer `k`-th root `Nat.nthRoot k m` is polynomial-time, with `k` in unary and `m` in
binary. -/
theorem binary_nthRoot :
    ComputableInPolyTime (fun p : ℕ × ℕ => Nat.nthRoot p.1 p.2) (encPair encUnary encNat)
      encNat := by
  have hcand : ComputableInPolyTime (fun p : ((ℕ × ℕ) × ℕ) × ℕ => p.1.2 + 2 ^ p.2)
      (encPair (encPair (encPair encUnary encNat) encNat) encUnary) encNat :=
    binary_add' ((snd _ _).comp (fst _ _)) (binary_pow' (const 2) (snd _ _))
  have hm : ComputableInPolyTime (fun p : ((ℕ × ℕ) × ℕ) × ℕ => p.1.1.2)
      (encPair (encPair (encPair encUnary encNat) encNat) encUnary) encNat :=
    (snd _ _).comp ((fst _ _).comp (fst _ _))
  have hstep : ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × ℕ) × ℕ => nthRootStep p.1.1 p.1.2 p.2)
      (encPair (encPair (encPair encUnary encNat) encNat) encUnary) encNat :=
    (bool_and' (binary_le' (binary_pow' hcand ((fst _ _).comp ((fst _ _).comp (fst _ _)))) hm)
      (binary_le' hcand hm)).ite' hcand ((snd _ _).comp (fst _ _))
  have hfold := foldlWith (encP := encPair encUnary encNat) (encA := encUnary)
    (encL := encList encUnary) (encB := encNat) (par := id)
    (list := fun p : ℕ × ℕ => (List.range p.2.size).reverse)
    (init := fun _ => 0) (step := nthRootStep) id'
    (listReverseWithInput (range.comp (binary_size.comp (snd _ _)))) (const 0) hstep
    (B := fun p => (encPair encUnary encNat p).length) .self fun p j _ => by
      refine le_trans ?_ (by enc_len : (encNat p.2).length ≤ (encPair encUnary encNat p).length)
      change (Nat.bits _).length ≤ p.2.bits.length
      simpa only [← Nat.size_eq_bits_len, id] using Nat.size_le_size
        (foldl_nthRootStep_le p ((List.range p.2.size).reverse.take j) (Nat.zero_le p.2))
  refine ((unary_le' (fst _ _) (const 0)).ite' (const 1) hfold).of_enc_eq fun ⟨k, m⟩ =>
    congrArg encNat ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · simpa [Nat.not_le.mpr hk] using (foldl_nthRootStep_eq_nthRoot hk.ne' m).symm

/-- Integer `k`-th root of a computed binary natural, with a computed unary `k`. -/
@[fun_prop]
theorem binary_nthRoot' {α : Type} {input : α ↪ List Bool} {k m : α → ℕ}
    (hk : ComputableInPolyTime k input encUnary) (hm : ComputableInPolyTime m input encNat) :
    ComputableInPolyTime (fun a => Nat.nthRoot (k a) (m a)) input encNat :=
  binary_nthRoot.comp (hk.prod hm)

/-- For `q ≠ 0`, `⌈n ^ (p / q)⌉` is the greatest `m ≤ n ^ p` with `(m - 1) ^ q < n ^ p` (or `0`
when there is none), a bounded search over unary naturals. -/
private theorem ceil_rpow_eq_findGreatest (n p q : ℕ) (hq : q ≠ 0) :
    ⌈(n : ℝ) ^ ((p : ℝ) / q)⌉₊ = Nat.findGreatest (fun m => (m - 1) ^ q < n ^ p) (n ^ p) := by
  set x : ℝ := (n : ℝ) ^ ((p : ℝ) / q)
  have hx : 0 ≤ x := Real.rpow_nonneg n.cast_nonneg _
  have hxq : x ^ q = ((n ^ p : ℕ) : ℝ) := by
    rw [← Real.rpow_mul_natCast n.cast_nonneg, div_mul_cancel₀ _ (Nat.cast_ne_zero.2 hq),
      Real.rpow_natCast, Nat.cast_pow]
  have hkey (m : ℕ) : (m - 1) ^ q < n ^ p ↔ m - 1 < ⌈x⌉₊ := by
    rw [Nat.lt_ceil, ← pow_lt_pow_iff_left₀ (Nat.cast_nonneg _) hx hq, hxq, ← Nat.cast_pow,
      Nat.cast_lt]
  have hle : ⌈x⌉₊ ≤ n ^ p := by
    rw [Nat.ceil_le, ← pow_le_pow_iff_left₀ hx (Nat.cast_nonneg _) hq, hxq]
    exact_mod_cast Nat.le_self_pow hq _
  exact (Nat.findGreatest_eq_iff.2 ⟨hle, fun h => (hkey _).2 (by omega),
    fun k hk _ => mt (hkey k).1 (by omega)⟩).symm

/-- **Unary rational-power ceilings.** For naturals `p` and `q ≠ 0`, `n ↦ ⌈n ^ (p / q)⌉` is
polynomial time with unary input and output, by a bounded search below `n ^ p`. -/
theorem unary_ceil_rpow (p q : ℕ) (hq : q ≠ 0) :
    ComputableInPolyTime (fun n : ℕ => ⌈(n : ℝ) ^ ((p : ℝ) / q)⌉₊) encUnary encUnary := by
  simp only [ceil_rpow_eq_findGreatest _ p q hq]
  have := unary_pow p
  have := unary_pow q
  exact findGreatest (unary_pow p) (by fun_prop)

end ComputableInPolyTime

end Turing.MultiTapeTM
