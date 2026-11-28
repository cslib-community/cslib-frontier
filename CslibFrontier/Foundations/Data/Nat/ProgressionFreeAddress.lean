/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: candidate

public import Mathlib.Combinatorics.Additive.AP.Three.Behrend
public import CslibFrontier.Foundations.Data.BitString.Block

/-!
# Progression-free address arithmetic

The code of a bounded digit vector uses a doubled radix and appends its squared norm.
The radix prevents carries when adding two address codes. At a midpoint equality the
two positional sums and the two norm sums agree separately. This is the arithmetic
needed for endpoint agreement in the conjunction construction of Section 5 of
[Balasubramanian and Majumdar][BalasubramanianMajumdar2026Pushdown].

## Main definitions

* `encode`: appends the squared norm to the positional code.
* `encodeBlocks`: encodes each ordered block of an address via `Cslib.BitString.block`.

## Main results

* `encode_bound`: bounds the code in terms of the digit bound and vector length.
* `encode_mod`: recovers the positional code as a remainder.
* `encode_injOn`: shows that the code determines the bounded digit vector.
* `encode_midpoint`: shows that three bounded vectors coincide at a midpoint equality.
* `threeAPFree_image_encode`: excludes nontrivial three-term progressions in the code image.
* `matched_endpoints`: recovers agreement of endpoints from their two code-sum equalities.
* `encodeBlocks_injOn`: shows that the ordered block codes determine the address.

## References

* [A. R. Balasubramanian, R. Majumdar, Pushdown Reachability Requires N² Time on Multitape Turing
  Machines][BalasubramanianMajumdar2026Pushdown], arXiv:2611.27814v2, Sections 5.1–5.2.
-/

public section

namespace Cslib.ProgressionFreeAddress

/-- Positional digits with their squared norm stored above the digit region. -/
@[expose] def encode {n : ℕ} (d : ℕ) (x : Fin n → ℕ) : ℕ :=
  Behrend.map (2 * d) x + (∑ i, x i ^ 2) * (2 * d) ^ n

private theorem positional_lt {n base : ℕ}
    (x : Fin n → ℕ) (hx : ∀ i, x i < base) : Behrend.map base x < base ^ n := by
  induction n with
  | zero => simp [Behrend.map]
  | succ n ih =>
    rw [Behrend.map_succ', pow_succ]
    have h : (Behrend.map base (x ∘ Fin.succ) + 1) * base ≤ base ^ n * base :=
      Nat.mul_le_mul_right _ (ih _ (fun i => hx i.succ))
    rw [Nat.add_mul, Nat.one_mul] at h
    have := hx 0
    omega

/-- Explicit range of the encoded digits and norm. -/
theorem encode_bound {n d : ℕ} (x : Fin n → ℕ) (hx : ∀ i, x i < d) :
    encode d x < (2 * d) ^ n * (n * (d - 1) ^ 2 + 1) := by
  have low := positional_lt (base := 2 * d) x (fun i => by have := hx i; omega)
  have high : (∑ i, x i ^ 2) ≤ n * (d - 1) ^ 2 :=
    Behrend.sum_sq_le_of_mem_box (Behrend.mem_box.mpr hx)
  unfold encode
  calc
    _ < (2 * d) ^ n + (∑ i, x i ^ 2) * (2 * d) ^ n := Nat.add_lt_add_right low _
    _ ≤ _ := by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm ((2 * d) ^ n) (n * (d - 1) ^ 2)]
      exact (Nat.add_le_add_left (Nat.mul_le_mul_right _ high) _).trans_eq (Nat.add_comm ..)

private theorem norm_midpoint {n : ℕ} (x y z : Fin n → ℕ)
    (mid : x + y = z + z)
    (norms : (∑ i, x i ^ 2) + (∑ i, y i ^ 2) = (∑ i, z i ^ 2) + (∑ i, z i ^ 2)) :
    x = y := by
  have hnorm : (∑ i, (x i : ℤ) ^ 2) + (∑ i, (y i : ℤ) ^ 2) =
      (∑ i, (z i : ℤ) ^ 2) + (∑ i, (z i : ℤ) ^ 2) := by
    exact_mod_cast norms
  have eq : (∑ i, ((x i : ℤ) - (y i : ℤ)) ^ 2) + 4 * (∑ i, (z i : ℤ) ^ 2) =
      2 * ((∑ i, (x i : ℤ) ^ 2) + (∑ i, (y i : ℤ) ^ 2)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hi : (x i : ℤ) + y i = (z i : ℤ) + z i := by
      exact_mod_cast congrFun mid i
    nlinarith
  have zero : (∑ i, ((x i : ℤ) - (y i : ℤ)) ^ 2) = 0 := by linarith
  funext i
  have each := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
    sq_nonneg ((x j : ℤ) - (y j : ℤ)))).mp zero i (Finset.mem_univ i)
  have hxy := sq_eq_zero_iff.mp each
  exact_mod_cast sub_eq_zero.mp hxy

/-- A midpoint equality can hold only when all three digit vectors agree. -/
theorem encode_midpoint {n d : ℕ} {x y z : Fin n → ℕ}
    (hx : ∀ i, x i < d) (hy : ∀ i, y i < d) (hz : ∀ i, z i < d)
    (heq : encode d x + encode d y = encode d z + encode d z) : x = y ∧ y = z := by
  let base := 2 * d
  have xy : ∀ i, (x + y) i < base := by
    intro i
    have := hx i
    have := hy i
    change x i + y i < 2 * d
    omega
  have zz : ∀ i, (z + z) i < base := by
    intro i
    have := hz i
    change z i + z i < 2 * d
    omega
  have withHigh : Behrend.map base (x + y) + ((∑ i, x i ^ 2) + (∑ i, y i ^ 2)) * base ^ n =
      Behrend.map base (z + z) + ((∑ i, z i ^ 2) + (∑ i, z i ^ 2)) * base ^ n := by
    simp only [map_add, add_mul]
    simpa only [encode, base, Nat.add_add_add_comm] using heq
  have xyLt := positional_lt _ xy
  have low := congrArg (· % base ^ n) withHigh
  simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt xyLt,
    Nat.mod_eq_of_lt (positional_lt _ zz)] at low
  have mid : x + y = z + z := Behrend.map_injOn xy zz low
  rw [low, Nat.add_right_inj] at withHigh
  have high : (∑ i, x i ^ 2) + (∑ i, y i ^ 2) = (∑ i, z i ^ 2) + (∑ i, z i ^ 2) :=
    Nat.eq_of_mul_eq_mul_right (Nat.zero_lt_of_lt xyLt) withHigh
  have same := norm_midpoint x y z mid high
  refine ⟨same, funext fun i => ?_⟩
  have h := congrFun mid i
  change x i + y i = z i + z i at h
  rw [same] at h
  omega

/-- The codes of bounded digit vectors form a three-term-progression-free set. -/
theorem threeAPFree_image_encode {n d : ℕ} :
    ThreeAPFree (encode d '' {x : Fin n → ℕ | ∀ i, x i < d}) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩ _ ⟨y, hy, rfl⟩ h
  obtain ⟨hxy, hyz⟩ := encode_midpoint hx hy hz h
  exact congrArg (encode d) (hxy.trans hyz)

/-- Remainder at the radix power recovers the low positional contribution. -/
theorem encode_mod {n d : ℕ} (x : Fin n → ℕ) (hx : ∀ i, x i < d) :
    encode d x % (2 * d) ^ n = Behrend.map (2 * d) x := by
  rw [encode, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (positional_lt _ _)]
  intro i
  have := hx i
  omega

/-- The encoded address determines every bounded digit. -/
theorem encode_injOn {n d : ℕ} :
    Set.InjOn (encode d : (Fin n → ℕ) → ℕ) {x | ∀ i, x i < d} := by
  intro x hx y hy eq
  have same := congrArg (· % (2 * d) ^ n) eq
  rw [encode_mod x hx, encode_mod y hy] at same
  exact Behrend.map_injOn (fun i => by have := hx i; omega)
    (fun i => by have := hy i; omega) same

/-- Two matching code sums determine equality of the corresponding endpoints. -/
theorem matched_endpoints {n d : ℕ} {x y x' y' q : Fin n → ℕ}
    (hx : ∀ i, x i < d) (hy : ∀ i, y i < d)
    (hx' : ∀ i, x' i < d) (hy' : ∀ i, y' i < d) (hq : ∀ i, q i < d)
    (sum : encode d x + encode d y = encode d x' + encode d y')
    (midpoint : encode d y + encode d y' = encode d q + encode d q) :
    x = x' ∧ y = y' := by
  obtain ⟨output, _⟩ := encode_midpoint hy hy' hq midpoint
  have input : encode d x = encode d x' :=
    Nat.add_right_cancel (by simpa only [output] using sum)
  exact ⟨encode_injOn hx hx' input, output⟩

/-- Encode each `w`-digit block of an `m * w`-digit address in order. -/
@[expose] def encodeBlocks {m w : ℕ} (d : ℕ) (x : Fin (m * w) → ℕ) : Fin m → ℕ :=
  fun b => encode d (Cslib.BitString.block x b)

/-- The full bounded address can be reconstructed from its ordered block codes. -/
theorem encodeBlocks_injOn {m w d : ℕ} :
    Set.InjOn (encodeBlocks d : (Fin (m * w) → ℕ) → Fin m → ℕ) {x | ∀ i, x i < d} := by
  intro x hx y hy eq
  apply Cslib.BitString.blocksEquiv.injective
  funext b
  exact encode_injOn (fun _ => hx _) (fun _ => hy _) (congrFun eq b)

end Cslib.ProgressionFreeAddress
