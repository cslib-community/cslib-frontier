/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.Formula

/-!
# Codes of the formula: mixed radix, pivot codes

* `Radix.enc`, `Radix.dig`: a code made of fields of widths `w 0, w 1, …` (lowest first), and its
  fields; `dig_enc`, `enc_dig`, `enc_lt`: they are inverse bijections between digit vectors and
  codes.
* `decode_pivotCode`: a pivot index is decoded from its code.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset

namespace Radix

/-- The offset of field `k`. -/
def off (w : ℕ → ℕ) (k : ℕ) : ℕ := ∑ j ∈ range k, w j

/-- Field `k` of a code. -/
def dig (w : ℕ → ℕ) (x k : ℕ) : ℕ := x / 2 ^ off w k % 2 ^ w k

/-- The code of the first `n` fields `d`. -/
def enc (w d : ℕ → ℕ) (n : ℕ) : ℕ := ∑ j ∈ range n, 2 ^ off w j * d j

@[simp] theorem off_zero (w : ℕ → ℕ) : off w 0 = 0 := by simp [off]

theorem off_succ' (w : ℕ → ℕ) (k : ℕ) : off w (k + 1) = w 0 + off (fun j => w (j + 1)) k := by
  unfold off; rw [sum_range_succ']; ring

theorem enc_succ' (w d : ℕ → ℕ) (n : ℕ) :
    enc w d (n + 1) = d 0 + 2 ^ w 0 * enc (fun j => w (j + 1)) (fun j => d (j + 1)) n := by
  simp only [enc, sum_range_succ', off_succ', pow_add, mul_sum, off_zero, pow_zero, one_mul]
  rw [add_comm]
  exact congrArg _ (sum_congr rfl fun j _ => by ring)

theorem enc_lt (n : ℕ) : ∀ (w d : ℕ → ℕ), (∀ j < n, d j < 2 ^ w j) → enc w d n < 2 ^ off w n := by
  induction n with
  | zero => intro w d _; simp [enc]
  | succ n ih =>
    intro w d hd
    rw [enc_succ', off_succ', pow_add]
    have h0 := hd 0 (by omega)
    have h1 := ih (fun j => w (j + 1)) (fun j => d (j + 1)) fun j hj => hd (j + 1) (by omega)
    have hp : 0 < 2 ^ w 0 := by positivity
    calc d 0 + 2 ^ w 0 * enc (fun j => w (j + 1)) (fun j => d (j + 1)) n
        < 2 ^ w 0 + 2 ^ w 0 * enc (fun j => w (j + 1)) (fun j => d (j + 1)) n := by omega
      _ = 2 ^ w 0 * (enc (fun j => w (j + 1)) (fun j => d (j + 1)) n + 1) := by ring
      _ ≤ 2 ^ w 0 * 2 ^ off (fun j => w (j + 1)) n := Nat.mul_le_mul_left _ h1

theorem dig_zero (w : ℕ → ℕ) (x : ℕ) : dig w x 0 = x % 2 ^ w 0 := by simp [dig]

theorem dig_succ' (w : ℕ → ℕ) (x k : ℕ) : dig w x (k + 1) = dig (fun j => w (j + 1)) (x / 2 ^ w 0)
    k := by
  unfold dig; rw [off_succ', pow_add, Nat.div_div_eq_div_mul]

theorem dig_enc (n : ℕ) : ∀ (w d : ℕ → ℕ), (∀ j < n, d j < 2 ^ w j) → ∀ k < n, dig w (enc w d n) k =
    d k := by
  induction n with
  | zero => intro w d _ k hk; omega
  | succ n ih =>
    intro w d hd k hk
    have h0 := hd 0 (by omega)
    rcases k with _ | k
    · rw [dig_zero, enc_succ', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
    · rw [dig_succ', enc_succ', Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt h0,
        zero_add]
      exact ih _ _ (fun j hj => hd (j + 1) (by omega)) k (by omega)

theorem enc_dig (n : ℕ) : ∀ (w : ℕ → ℕ) (x : ℕ), x < 2 ^ off w n → enc w (dig w x) n = x := by
  induction n with
  | zero => intro w x hx; simp at hx; simp [enc, hx]
  | succ n ih =>
    intro w x hx
    rw [enc_succ']
    have e : (fun j => dig w x (j + 1)) = dig (fun j => w (j + 1)) (x / 2 ^ w 0) := by
      funext j; exact dig_succ' w x j
    rw [e, ih _ _ (by rw [off_succ', pow_add] at hx; exact Nat.div_lt_of_lt_mul hx), dig_zero,
      Nat.mod_add_div]

theorem enc_congr {w d d' : ℕ → ℕ} {n : ℕ} (h : ∀ j < n, d j = d' j) : enc w d n = enc w d' n :=
  sum_congr rfl fun j hj => by rw [h j (mem_range.mp hj)]

theorem dig_lt (w : ℕ → ℕ) (x k : ℕ) : dig w x k < 2 ^ w k := Nat.mod_lt _ (by positivity)

end Radix

/-! ### Places -/

/-- The places of a half-routing. -/
def ValidPl (up : Bool) (p : HPlace) : Prop := ∃ k < 3, p = placeOf up k

theorem placeIdx_lt (up : Bool) (p : HPlace) : placeIdx up p < 3 := by
  unfold placeIdx; split_ifs <;> omega

theorem placeOf_placeIdx {up : Bool} {p : HPlace} (h : ValidPl up p) : placeOf up (placeIdx up p) =
    p := by
  obtain ⟨k, hk, rfl⟩ := h
  interval_cases k <;> cases up <;> simp [placeOf, placeIdx]

theorem placeIdx_placeOf {up : Bool} {k : ℕ} (hk : k < 3) : placeIdx up (placeOf up k) = k := by
  interval_cases k <;> cases up <;> simp [placeOf, placeIdx]

theorem placeOf_inj {up : Bool} {k k' : ℕ} (hk : k < 3) (hk' : k' < 3)
    (h : placeOf up k = placeOf up k') :
    k = k' := by
  rw [← placeIdx_placeOf (up := up) hk, ← placeIdx_placeOf (up := up) hk', h]

/-! ### Pivot codes -/

/-- The widths of the seven fields of a pivot code. -/
def pivW (W : ℕ) : ℕ → ℕ := fun j =>
  if j = 0 then Nat.size W else if j = 1 then Nat.size (3 * W + 3)
  else if j ≤ 4 then codeWidth W else Nat.size (2 * W)

/-- The part of `T₁` at the place `p`. -/
def partOf (up : Bool) (T₁ : Multiset (HPlace × ℕ)) (k : ℕ) : Multiset ℕ :=
  (T₁.filter fun s => s.1 = placeOf up k).map Prod.snd

/-- The seven fields of a pivot code. -/
noncomputable def pivDigits (up : Bool) (W ν : ℕ) (t : HPlace × ℕ) (T₁ : Multiset (HPlace × ℕ))
    (c₁ c₀ : ℤ) : ℕ → ℕ := fun j =>
  if j = 0 then ν else if j = 1 then placeIdx up t.1 + 3 * t.2
  else if j ≤ 4 then labelCode W (partOf up T₁ (j - 2), 0)
  else if j = 5 then (c₁ + W).toNat else (c₀ + W).toNat

theorem pivotCode_eq (up : Bool) (W ν : ℕ) (t : HPlace × ℕ) (T₁ : Multiset (HPlace × ℕ)) (c₁ c₀ : ℤ)
    :
    pivotCode up W ν t T₁ c₁ c₀ = Radix.enc (pivW W) (pivDigits up W ν t T₁ c₁ c₀) 7 := by
  simp only [pivotCode, pivWidths, Radix.enc, Radix.off, sum_range_succ, range_zero, sum_empty,
    pivW, pivDigits, partOf]
  norm_num
  ring

theorem pivWidth_eq (W : ℕ) : pivWidth W = Radix.off (pivW W) 7 := by
  simp only [pivWidth, pivWidths, Radix.off, sum_range_succ, range_zero, sum_empty, pivW]
  norm_num
  ring

theorem decodePivot_eq (up : Bool) (W i : ℕ) : decodePivot up W i =
    (Radix.dig (pivW W) i 0,
      (placeOf up (Radix.dig (pivW W) i 1 % 3), Radix.dig (pivW W) i 1 / 3),
      (match decodeLabel W (Radix.dig (pivW W) i 2) with
        | some l => located (placeOf up 0) l.1 | none => 0) +
      (match decodeLabel W (Radix.dig (pivW W) i 3) with
        | some l => located (placeOf up 1) l.1 | none => 0) +
      (match decodeLabel W (Radix.dig (pivW W) i 4) with
        | some l => located (placeOf up 2) l.1 | none => 0),
      (Radix.dig (pivW W) i 5 : ℤ) - W, (Radix.dig (pivW W) i 6 : ℤ) - W) := by
  have o : ∀ k, Radix.off (pivW W) k = ∑ j ∈ range k, pivW W j := fun k => rfl
  have h0 : Radix.dig (pivW W) i 0 = i / 2 ^ 0 % 2 ^ Nat.size W := by simp [Radix.dig, pivW]
  have h1 : Radix.dig (pivW W) i 1 = i / 2 ^ Nat.size W % 2 ^ Nat.size (3 * W + 3) := by
    simp [Radix.dig, o, sum_range_succ, pivW]
  have h2 : Radix.dig (pivW W) i 2 =
      i / 2 ^ (Nat.size W + Nat.size (3 * W + 3) + 0 * codeWidth W) % 2 ^ codeWidth W := by
    simp [Radix.dig, o, sum_range_succ, pivW]
  have h3 : Radix.dig (pivW W) i 3 =
      i / 2 ^ (Nat.size W + Nat.size (3 * W + 3) + 1 * codeWidth W) % 2 ^ codeWidth W := by
    simp [Radix.dig, o, sum_range_succ, pivW]
  have h4 : Radix.dig (pivW W) i 4 =
      i / 2 ^ (Nat.size W + Nat.size (3 * W + 3) + 2 * codeWidth W) % 2 ^ codeWidth W := by
    simp [Radix.dig, o, sum_range_succ, pivW]; ring_nf
  have h5 : Radix.dig (pivW W) i 5 =
      i / 2 ^ (Nat.size W + Nat.size (3 * W + 3) + 3 * codeWidth W) % 2 ^ Nat.size (2 * W) := by
    simp [Radix.dig, o, sum_range_succ, pivW]; ring_nf
  have h6 : Radix.dig (pivW W) i 6 =
      i / 2 ^ (Nat.size W + Nat.size (3 * W + 3) + 3 * codeWidth W + Nat.size (2 * W)) %
        2 ^ Nat.size (2 * W) := by
    simp [Radix.dig, o, sum_range_succ, pivW]; ring_nf
  rw [h0, h1, h2, h3, h4, h5, h6]
  rfl

theorem located_partOf {up : Bool} {T₁ : Multiset (HPlace × ℕ)} (k : ℕ) :
    located (placeOf up k) (partOf up T₁ k) = T₁.filter fun s => s.1 = placeOf up k := by
  unfold located partOf
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id (T₁.filter fun s => s.1 = placeOf up k)]
  refine Multiset.map_congr rfl fun s hs => ?_
  have := (Multiset.mem_filter.mp hs).2
  simp only [Function.comp_apply, id]
  rw [← this]

theorem filter_places {up : Bool} (T₁ : Multiset (HPlace × ℕ)) (hT : ∀ s ∈ T₁, ValidPl up s.1) :
    (T₁.filter fun s => s.1 = placeOf up 0) + (T₁.filter fun s => s.1 = placeOf up 1) +
      (T₁.filter fun s => s.1 = placeOf up 2) = T₁ := by
  induction T₁ using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ih := ih fun b hb => hT b (Multiset.mem_cons_of_mem hb)
    obtain ⟨k, hk, ha⟩ := hT a (Multiset.mem_cons_self _ _)
    have hne : ∀ k' < 3, k' ≠ k → a.1 ≠ placeOf up k' := fun k' hk' hne h =>
      hne (placeOf_inj hk' hk (h.symm.trans ha))
    rw [Multiset.filter_cons, Multiset.filter_cons, Multiset.filter_cons, ← Multiset.singleton_add]
    conv_rhs => rw [← ih]
    interval_cases k
    · rw [if_pos ha, if_neg (hne 1 (by omega) (by omega)), if_neg
        (hne 2 (by omega) (by omega))]; abel
    · rw [if_pos ha, if_neg (hne 0 (by omega) (by omega)), if_neg
        (hne 2 (by omega) (by omega))]; abel
    · rw [if_pos ha, if_neg (hne 0 (by omega) (by omega)), if_neg
        (hne 1 (by omega) (by omega))]; abel

theorem wt_partOf_le {up : Bool} (T₁ : Multiset (HPlace × ℕ)) (k : ℕ) :
    wt (partOf up T₁ k) ≤ (T₁.map lwt).sum := by
  have e : wt (partOf up T₁ k) = ((T₁.filter fun s => s.1 = placeOf up k).map lwt).sum := by
    simp only [wt, partOf, Multiset.map_map]; rfl
  rw [e]
  conv_rhs => rw [← Multiset.filter_add_not (fun s => s.1 = placeOf up k) T₁]
  rw [Multiset.map_add, Multiset.sum_add]
  exact Nat.le_add_right _ _

/-- **Decoding a pivot code.** -/
theorem decode_pivotCode (up : Bool) {W ν : ℕ} {t : HPlace × ℕ} {T₁ : Multiset (HPlace × ℕ)}
    {c₁ c₀ : ℤ} (hν : ν ≤ W) (ht1 : ValidPl up t.1) (ht2 : t.2 < W)
    (hT : ∀ s ∈ T₁, ValidPl up s.1) (hw : (T₁.map lwt).sum ≤ W) (hc₁ : |c₁| ≤ W) (hc₀ : |c₀| ≤ W) :
    decodePivot up W (pivotCode up W ν t T₁ c₁ c₀) = (ν, t, T₁, c₁, c₀) ∧
      pivotCode up W ν t T₁ c₁ c₀ < 2 ^ pivWidth W := by
  rw [abs_le] at hc₁ hc₀
  have hp := placeIdx_lt up t.1
  have hlw : ∀ k, labelWt (partOf up T₁ k, (0 : Multiset ℕ)) ≤ W := fun k => by
    simp only [labelWt, wt_zero, add_zero]; exact (wt_partOf_le _ _).trans hw
  have hc1 : (c₁ + W).toNat < 2 ^ Nat.size (2 * W) :=
    lt_of_le_of_lt (Int.toNat_le.mpr (by push_cast; omega)) (Nat.lt_size_self _)
  have hc0 : (c₀ + W).toNat < 2 ^ Nat.size (2 * W) :=
    lt_of_le_of_lt (Int.toNat_le.mpr (by push_cast; omega)) (Nat.lt_size_self _)
  have hb : ∀ j < 7, pivDigits up W ν t T₁ c₁ c₀ j < 2 ^ pivW W j := by
    intro j hj
    interval_cases j
    · show ν < 2 ^ Nat.size W
      exact lt_of_le_of_lt hν (Nat.lt_size_self W)
    · show placeIdx up t.1 + 3 * t.2 < 2 ^ Nat.size (3 * W + 3)
      exact lt_of_lt_of_le (by omega) (Nat.lt_size_self _).le
    · exact labelCode_lt (hlw 0)
    · exact labelCode_lt (hlw 1)
    · exact labelCode_lt (hlw 2)
    · exact hc1
    · exact hc0
  refine ⟨?_, by rw [pivotCode_eq, pivWidth_eq]; exact Radix.enc_lt 7 _ _ hb⟩
  rw [decodePivot_eq, pivotCode_eq]
  have hd : ∀ j < 7, Radix.dig (pivW W) (Radix.enc (pivW W) (pivDigits up W ν t T₁ c₁ c₀) 7) j =
      pivDigits up W ν t T₁ c₁ c₀ j := Radix.dig_enc 7 _ _ hb
  rw [hd 0 (by omega), hd 1 (by omega), hd 2 (by omega), hd 3 (by omega), hd 4 (by omega),
    hd 5 (by omega), hd 6 (by omega)]
  have e0 : pivDigits up W ν t T₁ c₁ c₀ 0 = ν := rfl
  have e1 : pivDigits up W ν t T₁ c₁ c₀ 1 = placeIdx up t.1 + 3 * t.2 := rfl
  have e2 : pivDigits up W ν t T₁ c₁ c₀ 2 = labelCode W (partOf up T₁ 0, 0) := rfl
  have e3 : pivDigits up W ν t T₁ c₁ c₀ 3 = labelCode W (partOf up T₁ 1, 0) := rfl
  have e4 : pivDigits up W ν t T₁ c₁ c₀ 4 = labelCode W (partOf up T₁ 2, 0) := rfl
  have e5 : pivDigits up W ν t T₁ c₁ c₀ 5 = (c₁ + W).toNat := rfl
  have e6 : pivDigits up W ν t T₁ c₁ c₀ 6 = (c₀ + W).toNat := rfl
  rw [e0, e1, e2, e3, e4, e5, e6]
  have hlab : ∀ k, decodeLabel W (labelCode W (partOf up T₁ k, 0)) = some (partOf up T₁ k, 0) :=
    fun k => decode_labelCode (by simp only [labelWt, wt_zero, add_zero]; exact (wt_partOf_le _ _).trans hw)
  rw [hlab 0, hlab 1, hlab 2]
  simp only [located_partOf]
  rw [filter_places T₁ hT]
  rw [show (placeIdx up t.1 + 3 * t.2) % 3 = placeIdx up t.1 by omega,
    show (placeIdx up t.1 + 3 * t.2) / 3 = t.2 by omega, placeOf_placeIdx ht1,
    Int.toNat_of_nonneg (by omega : 0 ≤ c₁ + W), Int.toNat_of_nonneg (by omega : 0 ≤ c₀ + W)]
  simp

end Cslib.Complexity.NtimeDspace.Cube
