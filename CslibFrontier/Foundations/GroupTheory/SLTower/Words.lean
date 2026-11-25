/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.GroupTheory.SLTower.Layer
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.NoncommRing

/-!
# Words in the generators

`Cslib.SLTower.WL h2 g N`: `g ∈ G h n` is a product of at most `N` generators. Elementary
matrices `1 + y E_{ij}` (Mathlib's `Matrix.SpecialLinearGroup.transvection`) are short words: first
along the superdiagonal, then for all
`i ≠ j` (using `h ≥ 3`), and for every entry `y` of `F₂[s]/(s^(n+1))` built from `1`, `s` and `t`.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Tower.Words`.

## Main definitions

* `Cslib.SLTower.WL`: being a word of length at most `N`.

## Main results

* `Cslib.SLTower.WL.mul`, `Cslib.SLTower.WL.comm`: words compose, and commutators of words are
  words.
* `Cslib.SLTower.WL.el_one`, `Cslib.SLTower.WL.el_s`, `Cslib.SLTower.WL.el_t`: elementary matrices
  with entries `1`, `s` and powers of `t` are short words.
-/

public section

namespace Cslib.SLTower

open Matrix Finset

/-- The last index. -/
def last (h : ℕ) [NeZero h] : Fin h := ⟨h - 1, Nat.sub_lt (NeZero.pos h) Nat.one_pos⟩

variable {h n : ℕ} [NeZero h] (h2 : 2 ≤ h)

/-- The element is a product of at most N generators. -/
@[expose] def WL (g : G h n) (N : ℕ) : Prop := ∃ l : List (Fin h),
    l.length ≤ N ∧ (l.map (gen h2)).prod = g

variable {h2}

theorem WL.mono {g : G h n} {N M : ℕ} (hg : WL h2 g N) (hM : N ≤ M) : WL h2 g M := by
  obtain ⟨l, h1, h3⟩ := hg
  exact ⟨l, h1.trans hM, h3⟩

theorem WL.one : WL h2 (1 : G h n) 0 := ⟨[], le_rfl, rfl⟩

theorem WL.gen (k : Fin h) : WL h2 (gen h2 k : G h n) 1 := ⟨[k], le_rfl, by simp⟩

theorem WL.mul {g g' : G h n} {N M : ℕ} (hg : WL h2 g N) (hg' : WL h2 g' M) : WL h2 (g * g')
    (N + M) := by
  obtain ⟨l, h1, rfl⟩ := hg
  obtain ⟨l', h3, rfl⟩ := hg'
  exact ⟨l ++ l', by simp; omega, by simp⟩

omit [NeZero h] in
theorem two_nsmul_mat (M : Matrix (Fin h) (Fin h) (R (n + 1))) : M + M = 0 := by
  ext a b
  exact add_self _ _

omit [NeZero h] in
/-- The commutator. -/
theorem transvection_comm (i j k : Fin h) (hik : i ≠ k) (hkj : k ≠ j) (hij : i ≠ j)
    (y y' : R (n + 1)) :
    SpecialLinearGroup.transvection hik y * SpecialLinearGroup.transvection hkj y' *
        (SpecialLinearGroup.transvection hik y * SpecialLinearGroup.transvection hkj y') =
            SpecialLinearGroup.transvection hij (y * y') := by
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
  set a := Matrix.single i k y
  set b := Matrix.single k j y'
  have haa : a * a = 0 := Matrix.single_mul_single_of_ne _ _ _ _ hik.symm _
  have hbb : b * b = 0 := Matrix.single_mul_single_of_ne _ _ _ _ hkj.symm _
  have hba : b * a = 0 := Matrix.single_mul_single_of_ne _ _ _ _ hij.symm _
  have hab : a * b = Matrix.single i j (y * y') := Matrix.single_mul_single_same _ _ _ _ _
  have e1 : (1 + a) * (1 + b) * ((1 + a) * (1 + b)) = 1 + a * b +
      ((a + b + a * b) + (a + b + a * b)) +
      (a * a + a * a * b + b * a + b * b + b * a * b + a * (b * a) + a * (b * b) +
        a * (b * a) * b) := by noncomm_ring
  rw [← hab, e1, two_nsmul_mat, haa, hba, hbb]
  simp

theorem WL.comm {i j k : Fin h} {hik : i ≠ k} {hkj : k ≠ j} (hij : i ≠ j)
    {y y' : R (n + 1)} {N M : ℕ}
    (h1 : WL h2 (SpecialLinearGroup.transvection hik y) N)
        (h3 : WL h2 (SpecialLinearGroup.transvection hkj y') M) : WL h2
            (SpecialLinearGroup.transvection hij (y * y'))
        (2 * (N + M)) := by
  rw [← transvection_comm i j k hik hkj hij]
  exact ((h1.mul h3).mul (h1.mul h3)).mono (by omega)

theorem gen_eq_El (k : Fin h) : (gen h2 k : G h n) =
    SpecialLinearGroup.transvection (sub_one_ne h2 k) (tt n k) :=
    by rfl

/-- An elementary matrix `1 + E_{i,i+1}` on the superdiagonal is a generator. -/
private theorem WL.el_succ {i j : Fin h} (hij : i ≠ j) (hd : i.1 + 1 = j.1) :
    WL h2 (SpecialLinearGroup.transvection hij 1 : G h n) 1 := by
  have hj : j ≠ 0 := fun e => by simp [e] at hd
  have h1 : j - 1 = i := Fin.ext <| by
    have h3 : (1 : Fin h) ≤ j := by
      rw [Fin.le_def, Fin.val_one', Nat.mod_eq_of_lt (show 1 < h by omega)]
      omega
    rw [Fin.sub_val_of_le h3, Fin.val_one', Nat.mod_eq_of_lt (show 1 < h by omega)]
    omega
  have h3 := WL.gen (n := n) (h2 := h2) j
  rw [gen_eq_El, tt, ite_eq_right hj] at h3
  exact h1 ▸ h3

/-- Constant elementary matrices above the diagonal. -/
theorem WL.upper (d : ℕ) (i j : Fin h) (hij : i ≠ j) (hd : i.1 + (d + 1) = j.1) :
    WL h2 (SpecialLinearGroup.transvection hij 1 : G h n) (4 ^ d) := by
  induction d generalizing j with
  | zero => exact (WL.el_succ hij (by omega)).mono (by simp)
  | succ d ih =>
    let k : Fin h := ⟨j.1 - 1, by omega⟩
    have hik : i ≠ k := fun e => by
      have := congrArg Fin.val e
      dsimp [k] at this
      omega
    have hkj : k ≠ j := fun e => by
      have := congrArg Fin.val e
      dsimp [k] at this
      omega
    have h4 := (ih k hik (by dsimp [k]; omega)).comm hij
      (WL.el_succ hkj (by dsimp [k]; omega))
    rw [one_mul] at h4
    have : 1 ≤ 4 ^ d := Nat.one_le_pow _ _ (by omega)
    exact h4.mono (by rw [pow_succ]; omega)

theorem WL.upper' (i j : Fin h)
    (hij : i < j) : WL h2 (SpecialLinearGroup.transvection hij.ne 1 : G h n) (4 ^ h) := by
  have := Fin.lt_def.1 hij
  have := j.2
  exact (WL.upper (j.1 - i.1 - 1) i j hij.ne (by omega)).mono
    (Nat.pow_le_pow_right (by omega) (by omega))

theorem zero_sub_one (h2 : 2 ≤ h) : (0 : Fin h) - 1 = last h := by
  refine Fin.ext ?_
  rw [zero_sub, Fin.val_neg', Fin.val_one', Nat.mod_eq_of_lt (show 1 < h by omega),
    Nat.mod_eq_of_lt (by omega)]
  rfl

theorem lt_last {i : Fin h} (hi : i ≠ last h) : i < last h := by
  rw [Fin.lt_def]
  have := i.2
  have : i.1 ≠ h - 1 := fun e => hi (Fin.ext e)
  simp only [last]
  omega

theorem zero_ne_last (h2 : 2 ≤ h) : last h ≠ 0 := fun e => by
  have := congrArg Fin.val e
  simp [last] at this
  omega

/-- All elementary matrices with entry t. -/
theorem WL.el_t (h3 : 3 ≤ h) (i j : Fin h) (hij : i ≠ j) :
    WL h2 (SpecialLinearGroup.transvection hij (t (n + 1)) : G h n) (4 ^ (h + 3)) := by
  have hp : 1 ≤ 4 ^ h := Nat.one_le_pow _ _ (by omega)
  have e1 : 4 ^ (h + 1) = 4 * 4 ^ h := by ring
  have e2 : 4 ^ (h + 2) = 16 * 4 ^ h := by ring
  have e3 : 4 ^ (h + 3) = 64 * 4 ^ h := by ring
  have hL0 := zero_ne_last (h := h) h2
  have c1 : WL h2 (SpecialLinearGroup.transvection hL0 (t (n + 1)) : G h n) 1 := by
    have h6 := WL.gen (n := n) (h2 := h2) 0
    have h7 : (SpecialLinearGroup.transvection (sub_one_ne h2 0) (t (n + 1)) : G h n) =
        SpecialLinearGroup.transvection hL0 (t (n + 1)) := Subtype.ext <| by
      rw [SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe, zero_sub_one h2]
    rw [gen_eq_El, tt, ite_eq_left rfl, h7] at h6
    exact h6
  have c2 (j : Fin h) (hj : last h ≠ j) :
      WL h2 (SpecialLinearGroup.transvection hj (t (n + 1)) : G h n) (4 ^ (h + 1)) := by
    rcases eq_or_ne j 0 with rfl | h0
    · exact c1.mono (by omega)
    · have h4 := c1.comm hj (WL.upper' (n := n) (h2 := h2) 0 j (Fin.pos_iff_ne_zero.2 h0))
      rw [mul_one] at h4
      exact h4.mono (by omega)
  have c3 (i j : Fin h) (hij : i ≠ j) (hi : i ≠ last h) (hj : j ≠ last h) :
      WL h2 (SpecialLinearGroup.transvection hij (t (n + 1)) : G h n) (4 ^ (h + 2)) := by
    have h4 := (WL.upper' (n := n) (h2 := h2) i (last h) (lt_last hi)).comm hij (c2 j hj.symm)
    rw [one_mul] at h4
    exact h4.mono (by omega)
  rcases eq_or_ne i (last h) with rfl | hi
  · exact (c2 j hij).mono (by omega)
  · rcases eq_or_ne j (last h) with rfl | hj
    · obtain ⟨k, hk1, hk2⟩ := Fin.exists_ne_and_ne_of_two_lt i (last h) (by omega)
      have h4 := (c3 i k hk1.symm hi hk2).comm hij
        (WL.upper' (n := n) (h2 := h2) k (last h) (lt_last hk2))
      rw [mul_one] at h4
      exact h4.mono (by omega)
    · exact (c3 i j hij hi hj).mono (by omega)

/-- Powers of the entry. -/
theorem WL.el_pow (h3 : 3 ≤ h)
    {y : R (n + 1)} {B : ℕ}
        (hy : ∀ i j (hij : i ≠ j), WL h2 (SpecialLinearGroup.transvection hij y : G h n) B)
    (m : ℕ) (hm : 1 ≤ m) (i j : Fin h)
        (hij : i ≠ j) : WL h2 (SpecialLinearGroup.transvection hij (y ^ m) : G h n)
        (B * m ^ 3) := by
  induction m using Nat.strong_induction_on generalizing i j with
  | _ m ih =>
    rcases Nat.eq_or_lt_of_le hm with rfl | h1
    · simpa using hy i j hij
    · obtain ⟨k, hk1, hk2⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
      have hab : m / 2 + (m - m / 2) = m := by omega
      have p3 := (ih (m / 2) (by omega) (by omega) i k hk1.symm).comm hij
        (ih (m - m / 2) (by omega) (by omega) k j hk2)
      rw [← pow_add, hab] at p3
      refine p3.mono ?_
      generalize ha : m / 2 = a at *
      generalize hb : m - a = b at *
      have ha1 : 1 ≤ a := by omega
      have hcube : 2 * (a ^ 3 + b ^ 3) ≤ (a + b) ^ 3 := by
        rcases (by omega : b = a ∨ b = a + 1) with rfl | rfl
        · ring_nf; omega
        · linarith [Nat.pow_le_pow_left ha1 2, Nat.pow_le_pow_left ha1 3]
      rw [← hab]
      calc 2 * (B * a ^ 3 + B * b ^ 3) = B * (2 * (a ^ 3 + b ^ 3)) := by ring
        _ ≤ B * (a + b) ^ 3 := Nat.mul_le_mul_left _ hcube

theorem one_add_pow_two_pow (m : ℕ) (y : R m) (e : ℕ) : (1 + y) ^ 2 ^ e = 1 + y ^ 2 ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, pow_mul, ih, pow_mul]
    linear_combination (y ^ 2 ^ e) * two_eq_zero m

/-- All elementary matrices with entry 1. -/
theorem WL.el_one (h3 : 3 ≤ h) (i j : Fin h) (hij : i ≠ j) :
    WL h2 (SpecialLinearGroup.transvection hij 1 : G h n) (4 ^ (h + 3) * (2 * (n + 1)) ^ 3) := by
  let e := Nat.clog 2 (n + 1)
  have he1 : n + 1 ≤ 2 ^ e := Nat.le_pow_clog (by omega) _
  have he2 : 2 ^ e ≤ 2 * (n + 1) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [e]
    · have := Nat.pow_pred_clog_lt_self (b := 2) (by omega) (show 1 < n + 1 by omega)
      obtain ⟨c, hc'⟩ := Nat.exists_eq_add_of_lt
        (Nat.clog_pos (b := 2) (by omega) (show 1 < n + 1 by omega))
      dsimp only [e]
      rw [hc'] at this ⊢
      simp only [zero_add, Nat.pred_succ] at this ⊢
      rw [pow_succ]
      omega
  have h4 := WL.el_pow (n := n) (h2 := h2) h3 (fun i j hij => WL.el_t h3 i j hij) (2 ^ e)
    (Nat.one_le_pow _ _ (by omega)) i j hij
  rw [t, one_add_pow_two_pow, s_pow_ge he1, add_zero] at h4
  exact h4.mono (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left he2 3))

/-- All elementary matrices with entry s. -/
theorem WL.el_s (h3 : 3 ≤ h) (i j : Fin h) (hij : i ≠ j) :
    WL h2 (SpecialLinearGroup.transvection hij (s (n + 1)) : G h n)
        (4 ^ (h + 3) * (9 * (n + 1) ^ 3)) := by
  have h1 := (WL.el_one (n := n) (h2 := h2) h3 i j hij).mul (WL.el_t h3 i j hij)
  rw [← SpecialLinearGroup.transvection_add, ← s_eq] at h1
  have : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  refine h1.mono ?_
  calc 4 ^ (h + 3) * (2 * (n + 1)) ^ 3 + 4 ^ (h + 3)
      = 4 ^ (h + 3) * (8 * (n + 1) ^ 3 + 1) := by ring
    _ ≤ 4 ^ (h + 3) * (9 * (n + 1) ^ 3) := Nat.mul_le_mul_left _ (by omega)

end Cslib.SLTower
