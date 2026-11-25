/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Languages.InnerProduct
public import CslibFrontier.Computability.Machines.Turing.SingleTape.Rectangle
import CslibFrontier.Foundations.BooleanAnalysis.HadamardRectangles
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quadratic single-tape lower bounds for binary inner product

Every deterministic single-tape decider of the ordinary binary inner-product language takes
quadratic time on average under the uniform distribution on words of each sufficiently large
even length. The theorem is stated without division: the sum of any individual native halting
times, over all pairs of `n`-bit halves, is at least `2 ^ (2n) (2n)² / (64d)`, where
`d = ⌈log₂ (|Q| + 2)⌉`. Concatenation identifies these pairs with all ordinary `2n`-bit words.

Split each half into an active block of length `m = n / 2` and a suffix of length `r = n - m`.
For every fixed pair of suffixes `a, b`, the residual function is the active inner product XOR
the fixed bit `a ⬝ᵥ b`. Its monochromatic rectangles still have at most `2 ^ m` entries, so the
rectangle-to-crossing transfer gives a lower bound on the sum over the active blocks. Summing
over every suffix pair and reindexing by `Fin.appendEquiv` includes each input exactly once.

This is an original application of the existing spectral rectangle bound and native crossing
sequence transfer. The average includes both accepted and rejected inputs. Specializing to
the global time bound gives a quadratic worst-case lower bound at every sufficiently large
even length. The input and workspace share the only tape; the answer is read under the head
when the machine halts, with no restriction on the rest of the final tape.

## Main results

* `Cslib.Turing.SingleTapeTM.innerProduct_average_lower_bound`: for `n ≥ 4d + 4`,
  `2 ^ (2n) (2n)² ≤ 64d ∑ₚ time(p)` for any per-input native halting times.
* `Cslib.Turing.SingleTapeTM.innerProduct_lower_bound`: with the same threshold,
  `(2n)² ≤ 64d T(2n)`.
-/

public section

open Cslib Cslib.Turing Matrix

namespace Cslib.Turing.SingleTapeTM

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] {tm : SingleTapeTM Symbol}

/-- The uniform mean of the native halting times of an ordinary binary inner-product decider
is at least `(2n)² / (64d)` for `n ≥ 4d + 4`, where `d = ⌈log₂ (|Q| + 2)⌉`. The division-free
statement sums over all pairs of `n`-bit halves, hence all `2 ^ (2n)` ordinary words. `time`
may vary with the input and need only reach an actual halt; it need not equal the global time
bound supplied with the decider. -/
theorem innerProduct_average_lower_bound {ι : Bool → Symbol} {yes : Symbol} {T : ℕ → ℕ}
    (hdec : tm.DecidesByHeadInTime ι Cslib.Language.innerProduct yes T) {n : ℕ}
    (hn : 4 * Nat.clog 2 (Fintype.card tm.State + 2) + 4 ≤ n)
    (time : BitString n × BitString n → ℕ)
    (htime : ∀ p,
      ((tm.absInit ((List.ofFn p.1 ++ List.ofFn p.2).map ι)).run (time p)).state = none) :
    2 ^ (2 * n) * (2 * n) ^ 2 ≤
      64 * Nat.clog 2 (Fintype.card tm.State + 2) * ∑ p, time p := by
  classical
  let d := Nat.clog 2 (Fintype.card tm.State + 2)
  change 4 * d + 4 ≤ n at hn
  obtain ⟨m, hm⟩ : ∃ m, m = n / 2 := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = n - m := ⟨_, rfl⟩
  have hmmin : 2 * d + 2 ≤ m := by omega
  have hsplit : m + r = n := by omega
  subst n
  have hblock (a b : BitString r) :
      2 ^ (2 * m) * ((r + 1) * m) ≤
        4 * d * ∑ p : BitString m × BitString m,
          time (Fin.append p.1 a, Fin.append p.2 b) := by
    have h := crossing_rectangle_bit_sum_bound hdec
      (X := BitString m) (Y := BitString m) (f := fun x y => (x ⬝ᵥ y) ^^ (a ⬝ᵥ b))
      List.ofFn (List.ofFn a) (fun y => List.ofFn y ++ List.ofFn b)
      (fun x y => Cslib.Language.ofFn_blocks_mem_innerProduct_iff x a y b)
      (m := m) (fun _ => by simp) (R := 2 ^ m)
      (fun U V z hUV => by
        have hmono : ∀ x ∈ U, ∀ y ∈ V, x ⬝ᵥ y = (z ^^ (a ⬝ᵥ b)) := fun x hx y hy => by
          simpa only [Bool.xor_assoc, Bool.xor_self, Bool.xor_false] using
            congrArg (fun c : Bool => c ^^ (a ⬝ᵥ b)) (hUV x hx y hy)
        simpa only [Fintype.card_fin] using
          BitString.card_mul_le_two_pow_of_dotProduct_eq U V (z ^^ (a ⬝ᵥ b)) hmono)
      m hmmin (by simp) (fun p => time (Fin.append p.1 a, Fin.append p.2 b))
      (fun p => by
        simpa only [List.ofFn_fin_append] using htime (Fin.append p.1 a, Fin.append p.2 b))
    simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, List.length_ofFn,
      ← pow_add, ← two_mul] using h
  have htotal := Finset.sum_le_sum (s := (Finset.univ : Finset (BitString r × BitString r)))
    fun ab _ => hblock ab.1 ab.2
  let e : (BitString r × BitString r) × (BitString m × BitString m) ≃
      BitString (m + r) × BitString (m + r) :=
    ((Equiv.prodComm _ _).trans
      (Equiv.prodProdProdComm (BitString m) (BitString m) (BitString r) (BitString r))).trans
        (Equiv.prodCongr (Fin.appendEquiv m r) (Fin.appendEquiv m r))
  have hreindex :
      (∑ ab : BitString r × BitString r, ∑ xy : BitString m × BitString m,
        time (Fin.append xy.1 ab.1, Fin.append xy.2 ab.2)) = ∑ p, time p :=
    (Fintype.sum_prod_type' _).symm.trans (e.sum_comp time)
  have hcount : Fintype.card (BitString r × BitString r) * 2 ^ (2 * m) = 2 ^ (2 * (m + r)) := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← pow_add]
    exact congrArg (2 ^ ·) (by omega)
  simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul,
    ← Finset.mul_sum, hreindex] at htotal
  rw [← Nat.mul_assoc, hcount] at htotal
  have hsq : (2 * (m + r)) ^ 2 ≤ 16 * ((r + 1) * m) := by
    rcases (show r = m ∨ r = m + 1 by omega) with rfl | rfl <;> nlinarith
  calc 2 ^ (2 * (m + r)) * (2 * (m + r)) ^ 2
      ≤ 16 * (2 ^ (2 * (m + r)) * ((r + 1) * m)) := by
        nlinarith [Nat.mul_le_mul_left (2 ^ (2 * (m + r))) hsq]
    _ ≤ 16 * (4 * d * ∑ p, time p) := Nat.mul_le_mul_left 16 htotal
    _ = 64 * Nat.clog 2 (Fintype.card tm.State + 2) * ∑ p, time p := by dsimp [d]; ring

/-- Every sufficiently large even length has a quadratic worst-case time lower bound for a
single-tape decider of the ordinary binary inner-product language. The input occupies its only
tape, and the answer is read under the head at halting. The constant depends only on the finite
state set, not on the tape alphabet or the letter map. -/
theorem innerProduct_lower_bound {ι : Bool → Symbol} {yes : Symbol} {T : ℕ → ℕ}
    (hdec : tm.DecidesByHeadInTime ι Cslib.Language.innerProduct yes T) {n : ℕ}
    (hn : 4 * Nat.clog 2 (Fintype.card tm.State + 2) + 4 ≤ n) :
    (2 * n) ^ 2 ≤ 64 * Nat.clog 2 (Fintype.card tm.State + 2) * T (2 * n) := by
  classical
  have h := innerProduct_average_lower_bound hdec hn (fun _ => T (2 * n)) (fun p => by
    simpa only [List.length_append, List.length_ofFn, ← two_mul] using
      (hdec.absRun (List.ofFn p.1 ++ List.ofFn p.2)).1)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, Nat.nsmul_eq_mul, ← pow_add, ← two_mul] at h
  apply Nat.le_of_mul_le_mul_left (c := 2 ^ (2 * n)) ?_ (by positivity)
  simpa only [Nat.mul_left_comm, Nat.mul_assoc] using h

end Cslib.Turing.SingleTapeTM
