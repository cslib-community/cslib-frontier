/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.BooleanAnalysis.SubsetZeta
public import CslibFrontier.Foundations.Data.BitString.Binary

/-!
# Yates's algorithm on tables of size `2 ^ n`

A function on the subsets of `Fin n` is stored as a table `t : Vector M (2 ^ n)`: cell `k` holds
the value at `maskSet n k`, the set of positions of the binary digits `1` of `k`, and `maskIndex S`
is the cell of `S`. Yates's algorithm (`transform c`) makes `n` passes over the table, one per
coordinate `i`. Pass `i` (`pass c i`) writes the new value of cell `k` as
`t[k] + c • t[k ^^^ 2 ^ i]` when bit `i` of `k` is set and as `t[k]` otherwise, following
[Williams2014], Lemma 4.2, Proof 1, and [BjorklundHusfeldtKoivisto2009], Section 2.2.

The output at `maskSet n k` is `∑_{T ⊆ maskSet n k} c ^ #(maskSet n k \ T) • F T` whenever the
input table represents `F` (`getElem_transform`). The fast zeta transform `zeta` (coefficient `1`)
computes `subsetZeta F` and the fast Möbius transform `mobius` (coefficient `-1`) computes
`subsetMobius F`. For checked `O((n + 1) * 2 ^ n)` standard-basis word-RAM running-time bounds
on `ℕ` and `ℤ` tables, see `CslibFrontier.Algorithms.WordRAM.Yates`.

## Main definitions

* `Cslib.Algorithms.Lean.Yates.maskSet`, `maskIndex`: the cells of a table and the subsets of
  `Fin n`.
* `Cslib.Algorithms.Lean.Yates.pass`, `transform`: pure passes of Yates's algorithm.
* `Cslib.Algorithms.Lean.Yates.zeta`, `mobius`: the fast zeta and Möbius transforms.

## Main results

* `Cslib.Algorithms.Lean.Yates.getElem_transform`: correctness of the passes.
* `Cslib.Algorithms.Lean.Yates.getElem_zeta`, `getElem_zeta_maskIndex`: the fast zeta transform
  computes `subsetZeta`.
* `Cslib.Algorithms.Lean.Yates.getElem_mobius`, `getElem_mobius_maskIndex`: the fast Möbius
  transform computes `subsetMobius`.

## References

* [A. Björklund, T. Husfeldt, M. Koivisto, *Set Partitioning via
  Inclusion–Exclusion*][BjorklundHusfeldtKoivisto2009]
* [R. Williams, *Nonuniform ACC Circuit Lower Bounds*][Williams2014]
-/

public section

namespace Cslib.Algorithms.Lean.Yates

open Finset Cslib.BitString

/-! ### Cells and subsets -/

/-- The set of positions `i < n` of the binary digits `1` of `k`. -/
@[expose] def maskSet (n k : ℕ) : Finset (Fin n) :=
  univ.filter fun i => k.testBit i

/-- The cell of the subset `S` of `Fin n`: the number whose binary digit `i` is `1` exactly when
`i ∈ S`. -/
@[expose] def maskIndex {n : ℕ} (S : Finset (Fin n)) : Fin (2 ^ n) :=
  BitString.equivFin n fun i => decide (i ∈ S)

@[simp] theorem mem_maskSet {n k : ℕ} {i : Fin n} : i ∈ maskSet n k ↔ k.testBit i = true := by
  simp only [maskSet, mem_filter, mem_univ, true_and]

/-- Flipping a binary digit `1` of the index erases its position from the set. -/
theorem maskSet_xor_two_pow {n k : ℕ} {i : Fin n} (hi : k.testBit i = true) :
    maskSet n (k ^^^ 2 ^ (i : ℕ)) = (maskSet n k).erase i := by
  ext j
  simp only [mem_maskSet, Finset.mem_erase, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hij : (i : ℕ) = j
  · have : j = i := Fin.ext hij.symm
    subst this
    simp [hi]
  · have : j ≠ i := fun h => hij (congrArg Fin.val h).symm
    simp [hij, this]

/-- The set of a cell is the set of true coordinates of the corresponding bit string. -/
theorem maskSet_eq_filter {n : ℕ} (k : Fin (2 ^ n)) :
    maskSet n k = univ.filter fun i => (BitString.equivFin n).symm k i = true := by
  ext i
  simp only [mem_maskSet, mem_filter, mem_univ, true_and, BitString.equivFin_symm_apply]

/-- The bit string of cell `k` is the indicator of the set of cell `k`. -/
theorem equivFin_symm_eq_decide_mem_maskSet {n : ℕ} (k : Fin (2 ^ n)) :
    (BitString.equivFin n).symm k = fun i => decide (i ∈ maskSet n k) := by
  funext i
  rw [BitString.equivFin_symm_apply]
  cases h : (k : ℕ).testBit i <;> simp [h]

@[simp] theorem maskSet_maskIndex {n : ℕ} (S : Finset (Fin n)) :
    maskSet n (maskIndex S) = S := by
  ext i
  rw [mem_maskSet, ← BitString.equivFin_symm_apply, maskIndex, Equiv.symm_apply_apply,
    decide_eq_true_iff]

@[simp] theorem maskIndex_maskSet {n : ℕ} (k : Fin (2 ^ n)) : maskIndex (maskSet n k) = k := by
  rw [maskIndex, ← Equiv.eq_symm_apply]
  funext i
  rw [BitString.equivFin_symm_apply]
  cases h : (k : ℕ).testBit i <;> simp [h]

/-- Every table represents the function reading the cell of each set. -/
theorem getElem_eq_maskIndex_maskSet {α : Type*} {n : ℕ} (t : Vector α (2 ^ n)) (k : ℕ)
    (hk : k < 2 ^ n) : t[k] = t[(maskIndex (maskSet n k) : ℕ)] := by
  have := maskIndex_maskSet (⟨k, hk⟩ : Fin (2 ^ n))
  simp only [this]

/-! ### The passes -/

variable {M R : Type*} [AddCommMonoid M] [Monoid R] [DistribMulAction R M]

/-- The pass of Yates's algorithm in coordinate `i` with coefficient `c`: cell `k` becomes
`t[k] + c • t[k ^^^ 2 ^ i]` when bit `i` of `k` is set, and `t[k]` otherwise. -/
@[expose] def pass {n : ℕ} (c : R) (i : Fin n) (t : Vector M (2 ^ n)) : Vector M (2 ^ n) :=
  Vector.ofFn fun k : Fin (2 ^ n) =>
    if (k : ℕ).testBit i then
      t[(k : ℕ)] + c • t[(k : ℕ) ^^^ 2 ^ (i : ℕ)]'(Nat.xor_lt_two_pow k.isLt
        (Nat.pow_lt_pow_right (by norm_num) i.isLt))
    else
      t[(k : ℕ)]

/-- Yates's algorithm with coefficient `c`: the passes in coordinates `0, …, n - 1`. -/
@[expose] def transform {n : ℕ} (c : R) (t : Vector M (2 ^ n)) : Vector M (2 ^ n) :=
  (List.finRange n).foldl (fun acc i => pass c i acc) t

/-- The fast zeta transform: Yates's algorithm with coefficient `1`. -/
@[expose] def zeta {n : ℕ} (t : Vector M (2 ^ n)) : Vector M (2 ^ n) :=
  transform (1 : ℕ) t

theorem getElem_pass {n : ℕ} (c : R) (i : Fin n) (t : Vector M (2 ^ n))
    (F : Finset (Fin n) → M) (hF : ∀ (k : ℕ) (hk : k < 2 ^ n), t[k] = F (maskSet n k))
    (k : ℕ) (hk : k < 2 ^ n) :
    (pass c i t)[k] = yatesPass c i F (maskSet n k) := by
  rw [pass, Vector.getElem_ofFn]
  simp only [yatesPass, mem_maskSet]
  split_ifs with h
  · rw [hF, hF, maskSet_xor_two_pow h]
  · rw [hF]

private theorem getElem_foldl_pass {n : ℕ} (c : R) (l : List (Fin n))
    (t : Vector M (2 ^ n)) (F : Finset (Fin n) → M)
    (hF : ∀ (k : ℕ) (hk : k < 2 ^ n), t[k] = F (maskSet n k)) (k : ℕ) (hk : k < 2 ^ n) :
    (l.foldl (fun acc i => pass c i acc) t)[k] = yatesTransform c l F (maskSet n k) := by
  induction l generalizing t F with
  | nil => exact hF k hk
  | cons i l ih =>
    rw [List.foldl_cons, yatesTransform_cons]
    exact ih _ _ (getElem_pass c i t F hF)

/-- **Correctness of Yates's algorithm.** If the table `t` represents `F`, the output at
`maskSet n k` is `∑_{T ⊆ maskSet n k} c ^ #(maskSet n k \ T) • F T`. -/
theorem getElem_transform {n : ℕ} (c : R) (t : Vector M (2 ^ n))
    (F : Finset (Fin n) → M) (hF : ∀ (k : ℕ) (hk : k < 2 ^ n), t[k] = F (maskSet n k))
    (k : ℕ) (hk : k < 2 ^ n) :
    (transform c t)[k] = ∑ T ∈ (maskSet n k).powerset, c ^ #(maskSet n k \ T) • F T := by
  rw [transform, getElem_foldl_pass c _ t F hF k hk,
    yatesTransform_apply_of_subset c (List.nodup_finRange n) F (by simp)]

/-- **The fast zeta transform computes the zeta transform**: if the table `t` represents `F`, the
output at `maskSet n k` is `subsetZeta F (maskSet n k)`. -/
theorem getElem_zeta {n : ℕ} (t : Vector M (2 ^ n))
    (F : Finset (Fin n) → M) (hF : ∀ (k : ℕ) (hk : k < 2 ^ n), t[k] = F (maskSet n k))
    (k : ℕ) (hk : k < 2 ^ n) :
    (zeta t)[k] = subsetZeta F (maskSet n k) := by
  rw [zeta, transform, getElem_foldl_pass _ _ t F hF k hk,
    yatesTransform_one_apply (List.nodup_finRange n) F (by simp)]

/-- The fast zeta transform, read at the cell of `S`, is the zeta transform of the table read at
the cells of the subsets of `S`. -/
theorem getElem_zeta_maskIndex {n : ℕ} (t : Vector M (2 ^ n)) (S : Finset (Fin n)) :
    (zeta t)[(maskIndex S : ℕ)] = subsetZeta (fun T => t[(maskIndex T : ℕ)]) S := by
  rw [getElem_zeta t (fun T => t[(maskIndex T : ℕ)]) (getElem_eq_maskIndex_maskSet t) _
      (maskIndex S).isLt,
    maskSet_maskIndex]

end Cslib.Algorithms.Lean.Yates

namespace Cslib.Algorithms.Lean.Yates

open Finset Cslib.BitString

variable {M : Type*} [AddCommGroup M]

/-- The fast Möbius transform: Yates's algorithm with coefficient `-1`. -/
@[expose] def mobius {n : ℕ} (t : Vector M (2 ^ n)) : Vector M (2 ^ n) :=
  transform (-1 : ℤ) t

/-- **The fast Möbius transform computes the Möbius transform**: if the table `t` represents `F`,
the output at `maskSet n k` is `subsetMobius F (maskSet n k)`. -/
theorem getElem_mobius {n : ℕ} (t : Vector M (2 ^ n))
    (F : Finset (Fin n) → M) (hF : ∀ (k : ℕ) (hk : k < 2 ^ n), t[k] = F (maskSet n k))
    (k : ℕ) (hk : k < 2 ^ n) :
    (mobius t)[k] = subsetMobius F (maskSet n k) := by
  rw [mobius, transform, getElem_foldl_pass _ _ t F hF k hk,
    yatesTransform_neg_one_apply (List.nodup_finRange n) F (by simp)]

/-- The fast Möbius transform, read at the cell of `S`, is the Möbius transform of the table read
at the cells of the subsets of `S`. -/
theorem getElem_mobius_maskIndex {n : ℕ} (t : Vector M (2 ^ n)) (S : Finset (Fin n)) :
    (mobius t)[(maskIndex S : ℕ)] = subsetMobius (fun T => t[(maskIndex T : ℕ)]) S := by
  rw [getElem_mobius t (fun T => t[(maskIndex T : ℕ)]) (getElem_eq_maskIndex_maskSet t) _
      (maskIndex S).isLt,
    maskSet_maskIndex]

end Cslib.Algorithms.Lean.Yates
