/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Foundations.Data.Code.EliasBassalygo
import CslibFrontier.Foundations.Data.Code.Hadamard
import CslibFrontier.Foundations.Data.Code.ListDecoding.JohnsonBound
import CslibFrontier.Foundations.Data.Nat.Choose.Entropy
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.ComputeDegree

/-!
# Tests: combinatorial list decodability, Johnson bound, and Elias–Bassalygo rate bound

Exercises `CslibFrontier.Foundations.Data.Code.ListDecoding`,
`CslibFrontier.Foundations.Data.Code.ListDecoding.JohnsonBound`,
`CslibFrontier.Foundations.Data.Code.EliasBassalygo`, and
`CslibFrontier.Foundations.Data.Nat.Choose.Entropy` across:

1. **Analytic Johnson radius identities and `q → ∞` comparisons:** concrete evaluations of
   `johnsonRadius`, `johnsonRadiusLimit`, `johnsonRadius_nonneg`, `johnsonRadius_antitone`, and
   `tendsto_johnsonRadius_atTop`.
2. **`q`-ary (`Fin 3`) list decodability and `ListCode` equivalence:** the length-3 distance-2
   ternary code `{(a, b, a + b)}` at `ε = 1 / 3` (`L = 4`) and comparison against the boundary
   `ρ = J_3(2 / 3) = 2 / 3`.
3. **Binary Hadamard code tightness at `ρ = J_2(1 / 2) = 1 / 2`:** `(1 / 2 - ε, ⌊1 / (4 ε ^ 2)⌋)`
   list decodability for every dimension `k ≥ 1`, paired with an explicit negative witness at
   `k = 5` (`n = 32`) showing that all `32` codewords lie inside the radius-`1 / 2` ball around `0`,
   breaking `L = 16` at the exact Johnson threshold while `(3 / 8, 16)`-list-decodability holds for
   every `k`.
4. **Binary simplex code (`n = 7, d = 4`):** punctured Hadamard code with `δ = 4 / 7 > 1 / 2`,
   list-decodable at `ρ = 3 / 7` (`e = 3`) where `fun _ => true` puts all `7` nonzero codewords
   inside the ball (matching the exact finite Johnson bound `M ≤ 7`).
5. **Combinatorial Reed–Solomon list-decodability (`q → ∞`):** concrete `(ρ, L)`-list-decodable
   Reed–Solomon codes beyond unique decoding over both `ZMod 11` (`n = 11, k = 3, e = 5`) and the
   infinite field `ℚ` (`n = 7, k = 3, e = 3`) with explicit codeword witnesses (not an algorithmic
   decoder).
6. **Finite and asymptotic Elias–Bassalygo rate bounds** and `q`-ary entropy bounds.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.JohnsonBound

open Cslib Cslib.BitString Cslib.Code Finset Polynomial

/-! ### 1. Exact values and monotonicity of `johnsonRadius` and `johnsonRadiusLimit` -/

example : johnsonRadius 2 (1 / 2) = 1 / 2 := by
  rw [johnsonRadius_two]
  norm_num

example : johnsonRadius 2 (3 / 8) = 1 / 4 := by
  rw [johnsonRadius_two]
  have hsqrt : Real.sqrt (1 - 2 * ((3 : ℝ) / 8)) = 1 / 2 := by
    rw [show (1 : ℝ) - 2 * (3 / 8) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hsqrt]
  norm_num

example : johnsonRadius 4 (3 / 4) = 3 / 4 := by
  rw [johnsonRadius]
  norm_num

example : johnsonRadiusLimit (3 / 4) = 1 / 2 := by
  rw [johnsonRadiusLimit]
  have hsqrt : Real.sqrt (1 - (3 : ℝ) / 4) = 1 / 2 := by
    rw [show (1 : ℝ) - 3 / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hsqrt]
  norm_num

example : johnsonRadiusLimit (3 / 4) ≤ johnsonRadius 5 (3 / 4) ∧
    johnsonRadius 5 (3 / 4) ≤ johnsonRadius 4 (3 / 4) :=
  ⟨johnsonRadiusLimit_le_johnsonRadius (by norm_num) (by norm_num) (by norm_num),
    johnsonRadius_antitone (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩

example : 0 ≤ johnsonRadius 3 (2 / 5) :=
  johnsonRadius_nonneg (by norm_num) (by norm_num)

example : Filter.Tendsto (fun q : ℝ => johnsonRadius q (3 / 4)) Filter.atTop (nhds (1 / 2)) := by
  have hval : johnsonRadiusLimit (3 / 4) = 1 / 2 := by
    rw [johnsonRadiusLimit]
    have hsqrt : Real.sqrt (1 - (3 : ℝ) / 4) = 1 / 2 := by
      rw [show (1 : ℝ) - 3 / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hsqrt]
    norm_num
  simpa only [hval] using tendsto_johnsonRadius_atTop (3 / 4)

/-! ### 2. `q`-ary (`Fin 3`) list decodability and `ListCode` equivalence -/

/-- Encoder for the ternary length-3 distance-2 code `{(a, b, a + b)}` over `Fin 3`. -/
private def ternaryEncode (p : Fin 3 × Fin 3) : Fin 3 → Fin 3 :=
  ![p.1, p.2, p.1 + p.2]

private def ternaryFin3 : Finset (Fin 3 → Fin 3) :=
  univ.image ternaryEncode

private theorem ternaryEncode_injective : Function.Injective ternaryEncode := by
  intro p q h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  exact Prod.ext (by simpa [ternaryEncode] using h0) (by simpa [ternaryEncode] using h1)

private theorem le_minDist_ternaryFin3 :
    ((2 : ℕ) : ℕ∞) ≤ minDist (ternaryFin3 : Set (Fin 3 → Fin 3)) := by
  rw [le_minDist_iff]
  intro x hx y hy hxy
  have hdec : ∀ x ∈ ternaryFin3, ∀ y ∈ ternaryFin3, x ≠ y → 2 ≤ hammingDist x y := by decide
  exact_mod_cast hdec x hx y hy hxy

/-- At `q = 3, n = 3, d = 2`, we have `J_3(2 / 3) = 2 / 3`, so taking `ε = 1 / 3` gives
`(1 / 3, 4)`-list-decodability and a matching `ListCode`. -/
private theorem ternaryFin3_isListDecodable :
    IsListDecodable (ternaryFin3 : Set (Fin 3 → Fin 3)) (1 / 3) 4 := by
  have h := isListDecodable_of_le_johnsonRadius (α := Fin 3) (by simp)
    le_minDist_ternaryFin3 (ε := 1 / 3) (ρ := 1 / 3) (by norm_num) (by
      simp only [Fintype.card_fin, Nat.cast_ofNat, johnsonRadius]
      norm_num)
  simp only [Fintype.card_fin, Nat.cast_ofNat] at h
  convert h using 1
  symm
  exact Nat.floor_eq_iff (by norm_num) |>.2 ⟨by norm_num, by norm_num⟩

example : ∀ w : Fin 3 → Fin 3,
    #{c ∈ ternaryFin3 | (hammingDist c w : ℝ) ≤ (1 / 3 : ℝ) * Fintype.card (Fin 3)} ≤ 4 :=
  isListDecodable_finset_iff.1 ternaryFin3_isListDecodable

example : IsListDecodable (ternaryFin3 : Set (Fin 3 → Fin 3)) (1 / 4) 5 :=
  ternaryFin3_isListDecodable.mono (subset_refl _) (by norm_num) (by decide)

example : ∃ D : ListCode (Fin 3 × Fin 3) (Fin 3) (Fin 3) 4,
    D.encode = ternaryEncode ∧ D.ListDecodes (1 / 3) := by
  rw [← isListDecodable_range_iff_exists_listCode ternaryEncode_injective]
  have hrange : Set.range ternaryEncode = (ternaryFin3 : Set (Fin 3 → Fin 3)) := by
    ext x
    simp [ternaryFin3]
  rw [hrange]
  exact ternaryFin3_isListDecodable

/-- At the boundary `ρ = J_3(2 / 3) = 2 / 3`, the ball around `0` contains 7 codewords (`> 4`),
confirming the need for `ε > 0`. -/
example : #{c ∈ ternaryFin3 | (hammingDist c (fun _ => 0) : ℝ) ≤ (2 / 3 : ℝ) * 3} = 7 := by
  norm_num
  decide

/-! ### 3. Binary Hadamard code tight witnesses at `J_2(1 / 2) = 1 / 2` -/

/-- For every `k ≥ 1` (`Nonempty ι`), the binary Hadamard code of length `n = 2 ^ |ι|` and
distance `d = 2 ^ (|ι| - 1)` is `(1 / 2 - ε, ⌊1 / (4 ε ^ 2)⌋)`-list-decodable for every `ε > 0`.
In particular, at `ε = 1 / 8`, it is `(3 / 8, 16)`-list-decodable regardless of dimension. -/
theorem hadamard_isListDecodable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {ε : ℝ} (hε : 0 < ε) :
    IsListDecodable (Set.range (hadamardCode (ι := ι))) (1 / 2 - ε) ⌊1 / (4 * ε ^ 2)⌋₊ := by
  have hd : ((2 ^ (Fintype.card ι - 1) : ℕ) : ℕ∞) ≤
      minDist (Set.range (hadamardCode (ι := ι))) := by
    rw [minDist_range_hadamardCode]
  have hdiv : ((2 ^ (Fintype.card ι - 1) : ℕ) : ℝ) / Fintype.card (ι → Bool) = 1 / 2 := by
    have hn : 0 < Fintype.card ι := Fintype.card_pos
    have hpow : 2 * 2 ^ (Fintype.card ι - 1) = 2 ^ Fintype.card ι := by
      rw [← pow_succ', Nat.sub_add_cancel hn]
    rw [Fintype.card_fun, Fintype.card_bool]
    have hR : (2 : ℝ) * ((2 ^ (Fintype.card ι - 1) : ℕ) : ℝ) = ((2 ^ Fintype.card ι : ℕ) : ℝ) := by
      exact_mod_cast hpow
    push_cast at hR ⊢
    have hpos : (0 : ℝ) < (2 : ℝ) ^ Fintype.card ι := by positivity
    rw [div_eq_iff hpos.ne']
    linarith
  have h := isListDecodable_of_le_johnsonRadius (α := Bool) (by decide) hd hε (ρ := 1 / 2 - ε) (by
    rw [hdiv, Fintype.card_bool, Nat.cast_ofNat, johnsonRadius_two]
    norm_num)
  rw [hdiv, Fintype.card_bool] at h
  simpa only [Nat.cast_ofNat,
    show ((2 : ℝ) - 1) * (1 / 2) / (2 * ε ^ 2) = 1 / (4 * ε ^ 2) by ring] using h

example : IsListDecodable (Set.range (hadamardCode (ι := Fin 5))) (3 / 8) 16 := by
  have h := hadamard_isListDecodable (ι := Fin 5) (ε := 1 / 8) (by norm_num)
  have h1 : (1 / 2 - 1 / 8 : ℝ) = 3 / 8 := by norm_num
  rw [h1] at h
  convert h using 1
  symm
  exact Nat.floor_eq_iff (by norm_num) |>.2 ⟨by norm_num, by norm_num⟩

/-- **Sharpness at `ρ = J_2(1 / 2) = 1 / 2`:** all `2 ^ 5 = 32` codewords of the length-32
Hadamard code lie within relative Hamming distance `1 / 2` of `0`, so the code is NOT
`(1 / 2, 16)`-list-decodable even though it is `(3 / 8, 16)`-list-decodable for every dimension. -/
example : ¬ IsListDecodable (Set.range (hadamardCode (ι := Fin 5))) (1 / 2) 16 := by
  intro h
  have h0 := h (fun _ => false)
  have hzero : hadamardCode (0 : Fin 5 → Bool) = fun _ => false := by
    ext a
    simp [hadamardCode_apply, Bool.zero_eq_false]
  have hsub : Set.range (hadamardCode (ι := Fin 5)) ⊆
      {c ∈ Set.range (hadamardCode (ι := Fin 5)) |
        (hammingDist c (fun _ => false) : ℝ) ≤ (1 / 2 : ℝ) * Fintype.card (Fin 5 → Bool)} := by
    rintro c ⟨x, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    by_cases hx : x = 0
    · subst hx
      rw [hzero, hammingDist_self]
      norm_num
    · have h2 := two_mul_hammingDist_hadamardCode hx
      rw [hzero, Fintype.card_fin] at h2
      have hle : hammingDist (hadamardCode x) (fun _ => false) ≤ 16 := by omega
      have hleR : (hammingDist (hadamardCode x) (fun _ => false) : ℝ) ≤ 16 := by exact_mod_cast hle
      exact hleR.trans (by norm_num)
  have henc := (Set.encard_le_encard hsub).trans h0
  have hcard : (Set.range (hadamardCode (ι := Fin 5))).encard = 32 := by
    rw [← Set.image_univ, hadamardCode_injective.encard_image, Set.encard_univ,
      ENat.card_eq_coe_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    norm_num
  rw [hcard] at henc
  norm_num at henc

/-! ### 4. Binary simplex code (`n = 7, d = 4`, punctured Hadamard) tight witness -/

private def nonzeroVecs3 : Fin 7 → Fin 3 → Bool :=
  ![![true, false, false], ![false, true, false], ![false, false, true],
    ![true, true, false], ![true, false, true], ![false, true, true],
    ![true, true, true]]

/-- The length-7 binary simplex code obtained by puncturing the 3-bit Hadamard code at `0`. -/
private def simplex3 : Finset (Fin 7 → Bool) :=
  univ.image fun x j => hadamardCode x (nonzeroVecs3 j)

private theorem le_minDist_simplex3 :
    ((4 : ℕ) : ℕ∞) ≤ minDist (simplex3 : Set (Fin 7 → Bool)) := by
  have hinj : Function.Injective nonzeroVecs3 := by decide
  have himg : univ.image nonzeroVecs3 = (univ : Finset (Fin 3 → Bool)).erase 0 := by decide
  rw [le_minDist_iff]
  rintro _ hu _ hv huv
  obtain ⟨x, -, rfl⟩ := mem_image.1 hu
  obtain ⟨y, -, rfl⟩ := mem_image.1 hv
  have hxy : x ≠ y := fun h => huv (h ▸ rfl)
  have h2 := two_mul_hammingDist_hadamardCode hxy
  rw [Fintype.card_fin] at h2
  have hzero (z : Fin 3 → Bool) : hadamardCode z 0 = false := by
    rw [hadamardCode_apply, dotProduct_zero]
    rfl
  have hcard :
      hammingDist (fun j => hadamardCode x (nonzeroVecs3 j))
          (fun j => hadamardCode y (nonzeroVecs3 j)) =
        hammingDist (hadamardCode x) (hadamardCode y) := by
    simp only [hammingDist]
    rw [← card_image_of_injective _ hinj]
    congr 1
    ext a
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact hj
    · intro ha
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact ha (by rw [hzero, hzero])
      have hmem : a ∈ univ.image nonzeroVecs3 := by
        rw [himg]
        exact mem_erase.2 ⟨ha0, mem_univ a⟩
      obtain ⟨j, -, rfl⟩ := mem_image.1 hmem
      exact ⟨j, ha, rfl⟩
  rw [Nat.cast_le, hcard]
  omega

/-- At `n = 7, d = 4` (`δ = 4 / 7 > 1 / 2`), `J_2(4 / 7) = 1 / 2`, so the binary Johnson bound
guarantees `(3 / 7, 56)`-list-decodability; concretely at `e = 3` (`ρ = 3 / 7`), `fun _ => true`
places all `7` nonzero codewords in the ball, matching the sharp finite Johnson bound `M ≤ 7`. -/
example : IsListDecodable (simplex3 : Set (Fin 7 → Bool)) (3 / 7) 56 := by
  have h := isListDecodable_of_le_johnsonRadius (α := Bool) (by decide) le_minDist_simplex3
    (ε := 1 / 14) (ρ := 3 / 7) (by norm_num) (by
      rw [Fintype.card_bool, Fintype.card_fin, Nat.cast_ofNat, johnsonRadius_two]
      have hsqrt : Real.sqrt (1 - 2 * ((4 : ℕ) : ℝ) / 7) = 0 :=
        Real.sqrt_eq_zero_of_nonpos (by norm_num)
      rw [show 1 - 2 * (((4 : ℕ) : ℝ) / (7 : ℕ)) = 1 - 2 * ((4 : ℕ) : ℝ) / 7 by ring, hsqrt]
      norm_num)
  rw [Fintype.card_bool, Fintype.card_fin] at h
  convert h using 1
  symm
  exact Nat.floor_eq_iff (by norm_num) |>.2 ⟨by norm_num, by norm_num⟩

example :
    #{c ∈ simplex3 | hammingDist c (fun _ => true) ≤ 3} = 7 ∧
    #{c ∈ simplex3 | hammingDist c (fun _ => false) ≤ 4} = 8 := by
  decide

/-! ### 5. Combinatorial Reed–Solomon list-decodability (`ZMod 11` and `ℚ`) -/

instance : Fact (Nat.Prime 11) := ⟨by decide⟩

private def points11 : Fin 11 → ZMod 11 := fun i => (i : ℕ)

private theorem points11_injective : Function.Injective points11 := by
  intro i j h
  have : (i.1 : ZMod 11).val = (j.1 : ZMod 11).val := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt i.2, ZMod.val_natCast_of_lt j.2] at this
  exact Fin.ext this

/-- Over `ZMod 11`, the `[11, 3, 9]` Reed–Solomon code uniquely decodes up to `e = 4` errors, and
`isListDecodable_reedSolomon` proves `(5 / 11, 327)`-list-decodability beyond unique decoding
since `1 - √(2 / 11) - 1 / 20 ≥ 5 / 11`. -/
example : IsListDecodable (reedSolomon points11 3 : Set (Fin 11 → ZMod 11)) (5 / 11) 327 := by
  have hsqrt : Real.sqrt (((3 - 1 : ℕ) : ℝ) / Fintype.card (Fin 11)) ≤ 1 - 5 / 11 - 1 / 20 := by
    rw [Fintype.card_fin]
    refine Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have h := isListDecodable_reedSolomon points11_injective (k := 3) (by decide) (by decide)
    (ε := 1 / 20) (ρ := 5 / 11) (by norm_num) (by linarith)
  simp only [Fintype.card_fin] at h
  convert h using 1
  symm
  exact Nat.floor_eq_iff (by norm_num) |>.2 ⟨by norm_num, by norm_num⟩

/-- Over the infinite field `ℚ`, the `[7, 3, 5]` Reed–Solomon code is `(3 / 7, 642)`-list-decodable
(beyond unique decoding at `e = 2`), and the two distinct codewords `0` and `i ↦ i * (i - 1)` both
lie within distance `3` of `![0, 0, 2, 6, 12, 0, 0]`. -/
example :
    IsListDecodable (reedSolomon (fun i : Fin 7 => (i : ℚ)) 3 : Set (Fin 7 → ℚ)) (3 / 7) 642 ∧
    (∃ c₁ c₂ : Fin 7 → ℚ, c₁ ≠ c₂ ∧
      c₁ ∈ reedSolomon (fun i : Fin 7 => (i : ℚ)) 3 ∧
      c₂ ∈ reedSolomon (fun i : Fin 7 => (i : ℚ)) 3 ∧
      hammingDist c₁ ![0, 0, 2, 6, 12, 0, 0] ≤ 3 ∧
      hammingDist c₂ ![0, 0, 2, 6, 12, 0, 0] ≤ 3) := by
  have hinj : Function.Injective (fun i : Fin 7 => (i : ℚ)) := fun i j h =>
    Fin.ext (Nat.cast_injective h)
  have hsqrt : Real.sqrt (((3 - 1 : ℕ) : ℝ) / Fintype.card (Fin 7)) ≤ 1 - 3 / 7 - 1 / 30 := by
    rw [Fintype.card_fin]
    refine Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have h := isListDecodable_reedSolomon hinj (k := 3) (by decide) (by decide)
    (ε := 1 / 30) (ρ := 3 / 7) (by norm_num) (by linarith)
  simp only [Fintype.card_fin] at h
  have hlist :
      IsListDecodable (reedSolomon (fun i : Fin 7 => (i : ℚ)) 3 : Set (Fin 7 → ℚ)) (3 / 7) 642 := by
    convert h using 1
    symm
    exact Nat.floor_eq_iff (by norm_num) |>.2 ⟨by norm_num, by norm_num⟩
  refine ⟨hlist, 0, (fun i : Fin 7 => (i : ℚ) * ((i : ℚ) - 1)), ?_,
    Submodule.zero_mem _, ?_, ?_, ?_⟩
  · intro heq
    have h2 := congrFun heq 2
    norm_num at h2
  · have hfn : (fun i : Fin 7 => (i : ℚ) * ((i : ℚ) - 1)) =
        fun i : Fin 7 => (X * (X - 1) : ℚ[X]).eval (i : ℚ) := by
      ext i
      simp
    rw [hfn]
    exact eval_mem_reedSolomon _ (by compute_degree!)
  · have hsub : ({i : Fin 7 | (0 : Fin 7 → ℚ) i ≠ ![0, 0, 2, 6, 12, 0, 0] i} :
        Finset (Fin 7)) ⊆ {2, 3, 4} := by
      intro i hi
      rw [mem_filter] at hi
      fin_cases i <;> simp_all
    exact (card_le_card hsub).trans (by decide : #({2, 3, 4} : Finset (Fin 7)) ≤ 3)
  · have hsub : ({i : Fin 7 | (i : ℚ) * ((i : ℚ) - 1) ≠ ![0, 0, 2, 6, 12, 0, 0] i} :
        Finset (Fin 7)) ⊆ {5, 6} := by
      intro i hi
      rw [mem_filter] at hi
      fin_cases i <;> simp_all <;> norm_num at *
    exact (card_le_card hsub).trans (by decide : #({5, 6} : Finset (Fin 7)) ≤ 3)

/-! ### 6. Finite and asymptotic Elias–Bassalygo rate bounds -/

example (C : Finset (Fin 10 → Bool)) (hC : ((4 : ℕ) : ℕ∞) ≤ minDist (C : Set (Fin 10 → Bool))) :
    rate (C : Set (Fin 10 → Bool)) ≤
      1 - Real.qaryEntropy 2 ((2 : ℝ) / 10) / Real.log 2 +
        Real.logb 2 ((2 - 1 : ℝ) * 10 * 4 * 11) / 10 := by
  have hsqrt : Real.sqrt (1 - 2 * ((4 : ℝ) / 10)) < 1 - 2 * ((2 : ℝ) / 10) :=
    Real.sqrt_lt' (by norm_num) |>.2 (by norm_num)
  have he : ((2 : ℕ) : ℝ) / Fintype.card (Fin 10) <
      johnsonRadius (Fintype.card Bool) ((4 : ℝ) / Fintype.card (Fin 10)) := by
    rw [Fintype.card_fin, Fintype.card_bool, Nat.cast_ofNat, johnsonRadius_two]
    linarith
  have hr := rate_le_of_lt_johnsonRadius (α := Bool) (by simp) hC (by decide) he
  simpa only [Fintype.card_bool, Fintype.card_fin, Nat.cast_ofNat,
    show (10 : ℝ) + 1 = 11 by norm_num] using hr

/-- Non-vacuous concrete witness for `eventually_rate_le_one_sub_qaryEntropy_johnsonRadius`: the
binary repetition code `{fun _ => false, fun _ => true}` of length `n`, whose two distinct codewords
lie at Hamming distance `n ≥ (1 / 2) * n`. -/
example {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop,
      rate (({fun _ : Fin n => false, fun _ : Fin n => true} : Finset (Fin n → Bool)) :
        Set (Fin n → Bool)) ≤
        1 - Real.qaryEntropy 2 (johnsonRadius 2 (1 / 2)) / Real.log 2 + ε := by
  have hC : ∀ n : ℕ,
      ∀ x ∈ ({fun _ : Fin n => false, fun _ : Fin n => true} : Finset (Fin n → Bool)),
      ∀ y ∈ ({fun _ : Fin n => false, fun _ : Fin n => true} : Finset (Fin n → Bool)),
      x ≠ y → (1 / 2 : ℝ) * Fintype.card (Fin n) ≤ hammingDist x y := by
    intro n x hx y hy hxy
    simp only [mem_insert, mem_singleton] at hx hy
    have hcard : hammingDist (fun _ : Fin n => false) (fun _ : Fin n => true) = n := by
      simp [hammingDist]
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · rw [hcard, Fintype.card_fin]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    · rw [hammingDist_comm, hcard, Fintype.card_fin]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    · exact absurd rfl hxy
  have hn : Filter.Tendsto (fun n : ℕ => Fintype.card (Fin n)) Filter.atTop Filter.atTop := by
    simp only [Fintype.card_fin]
    exact Filter.tendsto_id
  simpa only [Fintype.card_bool, Nat.cast_ofNat] using
    eventually_rate_le_one_sub_qaryEntropy_johnsonRadius (α := Bool) (δ := 1 / 2)
      (by norm_num) (by simp only [Fintype.card_bool]; norm_num) hC hn hε

example {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.qaryEntropy 3 p ≤ Real.log 3 :=
  qaryEntropy_le_log (by decide) hp0 hp1

example : Real.exp (4 * Real.qaryEntropy 3 ((1 : ℝ) / 4)) ≤
    (4 + 1 : ℝ) * ((Nat.choose 4 1 : ℝ) * ((3 : ℝ) - 1) ^ 1) := by
  simpa only [Nat.cast_ofNat, Nat.cast_one] using
    exp_mul_qaryEntropy_le_succ_mul_choose_mul_pow (q := 3) (n := 4) (e := 1)
      (by decide) (by decide)

end CslibFrontierTests.JohnsonBound
