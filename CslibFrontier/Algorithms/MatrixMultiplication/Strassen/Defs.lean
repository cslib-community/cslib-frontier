/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.RingTheory.CyclicIntRing.Coefficients

/-!
# Seven-product recursion on cyclic coefficient arrays

`multiply` is the finite coefficient specification of the native explicit-stack algorithm.
It uses the existing cyclic convolution, seven recursive products, and the ordinary Strassen
signs. The arrays are functions on natural indices; only their first `4^k*p` entries matter.
No execution or resource contract is bundled into this mathematical definition.

The recursion adapts Spec/Sec3/Theorem17/Strassen.lean, lines 81–96, at Anthropic formal-math
revision 16a5ce41304fcdaea4e0be7c132e1c361dc26da5. The coefficient bound below also controls
the native intermediate operand forms and partial output accumulations.
-/

public section

namespace Cslib.Algorithms.MatrixMultiplication.Strassen

open Cslib.CyclicIntRing

/-- Read one contiguous quarter of a coefficient array. -/
@[expose] def quarter (q t : ℕ) (a : ℕ → ℤ) : ℕ → ℤ := fun i => a (t * q + i)

/-- Join four equal-length output quarters; only the first `4*q` entries are specified. -/
@[expose] def assemble (q : ℕ) (a b c d : ℕ → ℤ) (i : ℕ) : ℤ :=
  match i / q with
  | 0 => a (i % q)
  | 1 => b (i % q)
  | 2 => c (i % q)
  | _ => d (i % q)

/-- The actual seven products, with cyclic convolution at scalar matrix leaves. -/
@[expose] def multiply (p : ℕ) : ℕ → (ℕ → ℤ) → (ℕ → ℤ) → ℕ → ℤ
  | 0, a, b => convolution p a b
  | k + 1, a, b =>
    let q := 4 ^ k * p
    let a₀ := quarter q 0 a; let a₁ := quarter q 1 a
    let a₂ := quarter q 2 a; let a₃ := quarter q 3 a
    let b₀ := quarter q 0 b; let b₁ := quarter q 1 b
    let b₂ := quarter q 2 b; let b₃ := quarter q 3 b
    let m₁ := multiply p k (a₀ + a₃) (b₀ + b₃)
    let m₂ := multiply p k (a₂ + a₃) b₀
    let m₃ := multiply p k a₀ (b₁ - b₃)
    let m₄ := multiply p k a₃ (b₂ - b₀)
    let m₅ := multiply p k (a₀ + a₁) b₃
    let m₆ := multiply p k (a₂ - a₀) (b₀ + b₁)
    let m₇ := multiply p k (a₁ - a₃) (b₂ + b₃)
    assemble q (m₁ + m₄ - m₅ + m₇) (m₃ + m₅) (m₂ + m₄) (m₁ - m₂ + m₃ + m₆)

/-- A quarter read remains within the original matrix block. -/
theorem quarter_natAbs_le {q A : ℕ} {a : ℕ → ℤ}
    (ha : ∀ i < 4 * q, (a i).natAbs ≤ A) {t : ℕ} (ht : t < 4)
    {i : ℕ} (hi : i < q) : (quarter q t a i).natAbs ≤ A := by
  apply ha
  have hm := Nat.mul_le_mul_right q (show t ≤ 3 by omega)
  omega

/-- Every returned coefficient is bounded using only the original two input envelopes.
The factor `16^k` deliberately also covers all four-term output accumulations. -/
theorem multiply_natAbs_le {p A B : ℕ} (k : ℕ) (a b : ℕ → ℤ)
    (ha : ∀ i < 4 ^ k * p, (a i).natAbs ≤ A)
    (hb : ∀ i < 4 ^ k * p, (b i).natAbs ≤ B) {i : ℕ} (hi : i < 4 ^ k * p) :
    (multiply p k a b i).natAbs ≤ p * (A * B) * 16 ^ k := by
  induction k generalizing A B a b i with
  | zero =>
    simpa only [multiply, convolution, pow_zero, Nat.one_mul, Nat.mul_one] using
      partialConvolution_natAbs_le (by simpa using hi) (le_refl p)
        (by simpa using ha) (by simpa using hb)
  | succ k ih =>
    let q := 4 ^ k * p
    have hq : 0 < q := by
      have hp : 0 < p := by by_contra hc; simp [Nat.eq_zero_of_not_pos hc] at hi
      exact Nat.mul_pos (by positivity) hp
    have hs : 4 ^ (k + 1) * p = 4 * q := by dsimp [q]; rw [pow_succ]; ring
    have ha' : ∀ j < 4 * q, (a j).natAbs ≤ A := by simpa only [← hs] using ha
    have hb' : ∀ j < 4 * q, (b j).natAbs ≤ B := by simpa only [← hs] using hb
    have hchild {u v : ℕ → ℤ}
        (hu : ∀ j < q, (u j).natAbs ≤ 2 * A) (hv : ∀ j < q, (v j).natAbs ≤ 2 * B) :
        (multiply p k u v (i % q)).natAbs ≤ p * ((2 * A) * (2 * B)) * 16 ^ k :=
      ih u v hu hv (Nat.mod_lt _ hq)
    have hq1 {C : ℕ} {x : ℕ → ℤ} (hx : ∀ j < 4 * q, (x j).natAbs ≤ C)
        (t : ℕ) (ht : t < 4 := by decide) : ∀ j < q, (quarter q t x j).natAbs ≤ 2 * C :=
      fun j hj => (quarter_natAbs_le hx ht hj).trans (by omega)
    have hadd {u v : ℤ} {c₁ c₂ : ℕ} (hu : u.natAbs ≤ c₁) (hv : v.natAbs ≤ c₂) :
        (u + v).natAbs ≤ c₁ + c₂ := (Int.natAbs_add_le _ _).trans (Nat.add_le_add hu hv)
    have hsub {u v : ℤ} {c₁ c₂ : ℕ} (hu : u.natAbs ≤ c₁) (hv : v.natAbs ≤ c₂) :
        (u - v).natAbs ≤ c₁ + c₂ := (Int.natAbs_sub_le _ _).trans (Nat.add_le_add hu hv)
    have hqAdd {C : ℕ} {x : ℕ → ℤ} (hx : ∀ j < 4 * q, (x j).natAbs ≤ C)
        (t₁ t₂ : ℕ) (h₁ : t₁ < 4 := by decide) (h₂ : t₂ < 4 := by decide) :
        ∀ j < q, ((quarter q t₁ x + quarter q t₂ x) j).natAbs ≤ 2 * C := fun j hj =>
      (hadd (quarter_natAbs_le hx h₁ hj) (quarter_natAbs_le hx h₂ hj)).trans_eq (Nat.two_mul C).symm
    have hqSub {C : ℕ} {x : ℕ → ℤ} (hx : ∀ j < 4 * q, (x j).natAbs ≤ C)
        (t₁ t₂ : ℕ) (h₁ : t₁ < 4 := by decide) (h₂ : t₂ < 4 := by decide) :
        ∀ j < q, ((quarter q t₁ x - quarter q t₂ x) j).natAbs ≤ 2 * C := fun j hj =>
      (hsub (quarter_natAbs_le hx h₁ hj) (quarter_natAbs_le hx h₂ hj)).trans_eq (Nat.two_mul C).symm
    have h₁ := hchild (hqAdd ha' 0 3) (hqAdd hb' 0 3)
    have h₂ := hchild (hqAdd ha' 2 3) (hq1 hb' 0)
    have h₃ := hchild (hq1 ha' 0) (hqSub hb' 1 3)
    have h₄ := hchild (hq1 ha' 3) (hqSub hb' 2 0)
    have h₅ := hchild (hqAdd ha' 0 1) (hq1 hb' 3)
    have h₆ := hchild (hqSub ha' 2 0) (hqAdd hb' 0 1)
    have h₇ := hchild (hqSub ha' 1 3) (hqAdd hb' 2 3)
    have hqeq : 4 ^ k * p = q := rfl
    have htotal : p * (A * B) * 16 ^ (k + 1) =
        4 * (p * ((2 * A) * (2 * B)) * 16 ^ k) := by rw [pow_succ]; ring
    simp only [multiply, hqeq, assemble, Pi.add_apply, Pi.sub_apply, htotal]
    split
    · exact (hadd (hsub (hadd h₁ h₄) h₅) h₇).trans (by omega)
    · exact (hadd h₃ h₅).trans (by omega)
    · exact (hadd h₂ h₄).trans (by omega)
    · exact (hadd (hadd (hsub h₁ h₂) h₃) h₆).trans (by omega)

end Cslib.Algorithms.MatrixMultiplication.Strassen
