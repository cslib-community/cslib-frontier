/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.GroupTheory.SLTower.Ring
public import CslibFrontier.Foundations.GroupTheory.SLTower.UT
import Mathlib.RingTheory.WittVector.IsPoly

/-!
# The groups `SL_h(F₂[s]/(s^(n+1)))` and their `h` unitriangular subgroups

`Cslib.SLTower.G h n = SL_h(F₂[s]/(s^(n+1)))`. Conjugating `SL_h(F₂)` by the powers of a shift
weighted with `t = 1 + s` gives `h` embeddings `th0 i` (`i : Fin h`), and their restrictions
`th i` to the unitriangular group. The generators `gen k` are transvections `1 + tt k · E_{k−1,k}`
(with weight `t` for `k = 0`), involutions of type `k`; the simple root elements of the `i`-th
unitriangular subgroup are the generators of types other than `i` (`Cslib.SLTower.th_x`).

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Tower.Grp`.

## Main definitions

* `Cslib.SLTower.G h n`: the group; `Cslib.SLTower.evG`: the value at `s = 0`, onto `SL_h(F₂)`.
* `Cslib.SLTower.th0 i`, `Cslib.SLTower.th i`: the shifted embeddings of `SL_h(F₂)` and `U h`.
* `Cslib.SLTower.gen h2 k`: the generator of type `k`.

## Main results

* `Cslib.SLTower.th_injective`, `Cslib.SLTower.evG_th_eq_one`: the embeddings are injective, even
  after the value at `s = 0`.
* `Cslib.SLTower.gen_mul_self`: the generators are involutions.
* `Cslib.SLTower.th_x`: `th i (x l) = gen (i + 1 + l)`.
-/

public section

namespace Cslib.SLTower

open Matrix Finset

variable (h n : ℕ) [NeZero h]

/-- The group. -/
abbrev G : Type := Matrix.SpecialLinearGroup (Fin h) (R (n + 1))

/-- The unit t. -/
noncomputable def tu : (R (n + 1))ˣ := (isUnit_t (n + 1)).unit

theorem tu_val : ((tu n : (R (n + 1))ˣ) : R (n + 1)) = t (n + 1) := by rfl

variable {h n}

/-- The weights of the shift by i: the places that were carried over. -/
@[expose] noncomputable def wt (i a : Fin h) : (R (n + 1))ˣ := if a < i then (tu n)⁻¹ else 1

/-- Conjugation by the i-th power of the shift. -/
noncomputable def shMat (i : Fin h) (A : Matrix (Fin h) (Fin h) (ZMod 2)) : Matrix (Fin h) (Fin h)
    (R (n + 1)) :=
  diagonal (fun a => ((wt i a : (R (n + 1))ˣ) : R (n + 1))) *
    ((A.map (cst (n + 1))).submatrix (Equiv.subRight i) (Equiv.subRight i) *
      diagonal (fun a => (((wt i a)⁻¹ : (R (n + 1))ˣ) : R (n + 1))))

theorem shMat_apply (i : Fin h) (A : Matrix (Fin h) (Fin h) (ZMod 2)) (a b : Fin h) :
    (shMat i A : Matrix (Fin h) (Fin h) (R (n + 1))) a b =
      (wt i a : (R (n + 1))ˣ) * (cst (n + 1) (A (a - i) (b - i)) * ((wt i b)⁻¹ : (R (n + 1))ˣ)) :=
          by
  rw [shMat, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rfl

theorem shMat_one (i : Fin h) : (shMat i 1 : Matrix (Fin h) (Fin h) (R (n + 1))) = 1 := by
  ext a b
  rw [shMat_apply]
  by_cases hab : a = b
  · subst hab
    simp
  · rw [Matrix.one_apply_ne fun e => hab (sub_left_injective e), Matrix.one_apply_ne hab]
    simp

theorem shMat_mul (i : Fin h) (A B : Matrix (Fin h) (Fin h) (ZMod 2)) :
    (shMat i (A * B) : Matrix (Fin h) (Fin h) (R (n + 1))) = shMat i A * shMat i B := by
  ext a b
  simp only [shMat_apply, Matrix.mul_apply, map_sum, Finset.sum_mul, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight i) _ _ fun c => ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right, map_mul]
  linear_combination (-(wt i a : (R (n + 1))ˣ) * cst (n + 1) (A (a - i) c) *
    cst (n + 1) (B c (b - i)) * ((wt i b)⁻¹ : (R (n + 1))ˣ) : R (n + 1)) *
    Units.inv_mul (wt i (c + i) : (R (n + 1))ˣ)

theorem det_shMat (i : Fin h) (A : Matrix (Fin h) (Fin h) (ZMod 2)) :
    (shMat i A : Matrix (Fin h) (Fin h) (R (n + 1))).det = cst (n + 1) A.det := by
  rw [shMat, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    Matrix.det_submatrix_equiv_self, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have h1 : (∏ a, ((wt i a : (R (n + 1))ˣ) : R (n + 1))) *
      ∏ a, (((wt i a)⁻¹ : (R (n + 1))ˣ) : R (n + 1)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun a _ => Units.mul_inv _
  linear_combination (cst (n + 1) A.det) * h1

/-- The embedding of SL_h(F₂) shifted by i. -/
@[expose] noncomputable def th0 (i : Fin h) : SL2 h →* G h n where
  toFun A := ⟨shMat i A.1, by rw [det_shMat, A.2, map_one]⟩
  map_one' := Subtype.ext (shMat_one i)
  map_mul' A B := Subtype.ext (shMat_mul i A.1 B.1)

theorem th0_val (i : Fin h) (A : SL2 h) : (th0 i A : G h n).1 = shMat i A.1 := by rfl

/-- The value at s = 0. -/
noncomputable def evG : G h n →* SL2 h := Matrix.SpecialLinearGroup.map (ev n)

omit [NeZero h] in
theorem evG_apply (g : G h n) (a b : Fin h) : (evG g).1 a b = ev n (g.1 a b) := by rfl

omit [NeZero h] in
theorem ev_wt (i a : Fin h) : ev n ((wt i a : (R (n + 1))ˣ) : R (n + 1)) = 1 := by
  rw [wt]
  split_ifs
  · simpa only [map_mul, show ev n (tu n : R (n + 1)) = 1 from ev_t n, one_mul, map_one] using
      congrArg (ev n) (Units.mul_inv (tu n))
  · simp

omit [NeZero h] in
theorem ev_wt_inv (i a : Fin h) : ev n (((wt i a)⁻¹ : (R (n + 1))ˣ) : R (n + 1)) = 1 := by
  simpa only [map_mul, ev_wt, one_mul, map_one] using
    congrArg (ev n) (Units.mul_inv (wt i a : (R (n + 1))ˣ))

theorem evG_th0 (i : Fin h) (A : SL2 h) (a b : Fin h) : (evG (th0 i A : G h n)).1 a b = A.1 (a - i)
    (b - i) := by
  rw [evG_apply, th0_val, shMat_apply, map_mul, map_mul, ev_wt, ev_wt_inv, ev_cst, one_mul, mul_one]

theorem evG_th0_injective (i : Fin h) : Function.Injective fun A : SL2 h =>
    evG (th0 i A : G h n) := by
  intro A B e
  refine Subtype.ext (Matrix.ext fun a b => ?_)
  simpa only [evG_th0, add_sub_cancel_right] using
    congrFun (congrFun (congrArg Subtype.val e) (a + i)) (b + i)

/-- The h unitriangular subgroups. -/
@[expose] noncomputable def th (i : Fin h) : U h →* G h n := (th0 i).comp (U h).subtype

theorem th_injective (i : Fin h) : Function.Injective (th i : U h →* G h n) :=
  fun _ _ e => Subtype.ext (evG_th0_injective (n := n) i (congrArg evG e))

theorem evG_th_eq_one {i : Fin h} {u : U h} (e : evG (th i u : G h n) = 1) : u = 1 :=
  Subtype.ext (evG_th0_injective (n := n) i (by simpa [th] using e))

variable (n) in
/-- The entry of the generators. -/
@[expose] noncomputable def tt (k : Fin h) : R (n + 1) := if k = 0 then t (n + 1) else 1

theorem sub_one_ne (h2 : 2 ≤ h) (k : Fin h) : k - 1 ≠ k := by
  intro e
  have h1 : (1 : Fin h) = 0 := by simpa using congrArg (k - ·) e
  simp [Fin.ext_iff, Nat.mod_eq_of_lt (show 1 < h by omega)] at h1

/-- The generators: involutions of type k. -/
@[expose] noncomputable def gen (h2 : 2 ≤ h) (k : Fin h) : G h n :=
  ⟨transvection (k - 1) k (tt n k), det_transvection_of_ne _ _ (sub_one_ne h2 k) _⟩

theorem gen_val (h2 : 2 ≤ h) (k : Fin h) : (gen h2 k : G h n).1 = transvection (k - 1) k (tt n k)
    := by rfl

theorem gen_mul_self (h2 : 2 ≤ h) (k : Fin h) : (gen h2 k : G h n) * gen h2 k = 1 :=
  Subtype.ext <| (transvection_mul_transvection_same _ _ (sub_one_ne h2 k) _ _).trans <| by
    rw [add_self, transvection_zero]; rfl

/-- The type i + 1 + l. -/
def sh (i : Fin h) (l : Fin (h - 1)) : Fin h := hi l + i

theorem sh_sub_one (h2 : 2 ≤ h) (i : Fin h) (l : Fin (h - 1)) : sh i l - 1 = lo l + i := by
  have hhi : (hi l : Fin h) = lo l + 1 := Fin.ext <| by
    simp only [Fin.val_add, Fin.val_one', lo, hi, Nat.mod_eq_of_lt (by omega : 1 < h),
      Nat.mod_eq_of_lt (by omega : l.1 + 1 < h)]
  rw [sh, hhi]; abel

theorem sh_ne (i : Fin h) (l : Fin (h - 1)) : sh i l ≠ i := by
  intro e
  simpa [Fin.ext_iff, hi] using (show (hi l : Fin h) = 0 by simpa [sh] using e)

omit [NeZero h] in
theorem sh_injective (i : Fin h) : Function.Injective (sh i) := by
  intro l l' e
  have := congrArg Fin.val (show (hi l : Fin h) = hi l' by simpa [sh] using e)
  exact Fin.ext (by simp only [hi] at this; omega)

theorem exists_sh {i k : Fin h} (hk : k ≠ i) : ∃ l, sh i l = k := by
  have h1 : (k - i).1 ≠ 0 := fun e => hk (sub_eq_zero.1 (Fin.ext e))
  refine ⟨⟨(k - i).1 - 1, by omega⟩, ?_⟩
  rw [sh, show (hi ⟨(k - i).1 - 1, _⟩ : Fin h) = k - i from Fin.ext (by simp only [hi]; omega),
    sub_add_cancel]

theorem wt_sub_one (h2 : 2 ≤ h) {i k : Fin h} (hk : k ≠ i) :
    ((wt i (k - 1) : (R (n + 1))ˣ) : R (n + 1)) * ((wt i k)⁻¹ : (R (n + 1))ˣ) = tt n k := by
  by_cases h0 : k = 0
  · subst h0
    have hi0 : (0 : Fin h) < i := Fin.pos_iff_ne_zero.2 hk.symm
    have hl : ¬ ((0 : Fin h) - 1 < i) := by
      rw [Fin.lt_def, zero_sub, Fin.val_neg', Fin.val_one',
        Nat.mod_eq_of_lt (by omega : 1 < h),
        Nat.mod_eq_of_lt (by omega : h - 1 < h)]
      omega
    rw [wt, wt, ite_eq_right hl, ite_eq_left hi0, tt, ite_eq_left rfl, inv_inv, Units.val_one,
      one_mul, tu_val]
  · have hk0 : 0 < k.1 := Nat.pos_of_ne_zero fun e => h0 (Fin.ext e)
    have h1 : (k - 1).1 = k.1 - 1 := by
      have hle : (1 : Fin h) ≤ k := by
        rwa [Fin.le_def, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
      rw [Fin.sub_val_of_le hle, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
    have hki : k.1 ≠ i.1 := fun e => hk (Fin.ext e)
    have hlt_iff : k - 1 < i ↔ k < i := by rw [Fin.lt_def, Fin.lt_def, h1]; omega
    simp only [wt, tt, h0, ↓reduceIte, hlt_iff]
    split_ifs <;> simp

/-- The simple root elements of the i-th unitriangular subgroup are generators. -/
theorem th_x (h2 : 2 ≤ h) (i : Fin h) (l : Fin (h - 1)) : (th i (x h l) : G h n) =
    gen h2 (sh i l) := by
  refine Subtype.ext ?_
  have hth : (th i (x h l) : G h n).1 = shMat i (1 + Matrix.single (lo l) (hi l) 1) :=
    congrArg (shMat i) (x_val h l).symm
  rw [hth, gen_val, transvection, sh_sub_one h2]
  ext a b
  rw [shMat_apply, Matrix.add_apply, Matrix.add_apply]
  have hcond : (lo l = a - i ∧ hi l = b - i) ↔ (lo l + i = a ∧ sh i l = b) := by
    simp [sh, sub_eq_iff_eq_add, eq_comm]
  by_cases hab : a = b
  · subst hab
    have h1 : ¬ (lo l = a - i ∧ hi l = a - i) := fun e => lo_ne_hi l (e.1.trans e.2.symm)
    simp [h1, hcond.not.mp h1]
  · rw [Matrix.one_apply_ne fun e => hab (sub_left_injective e), Matrix.one_apply_ne hab,
      zero_add, zero_add]
    by_cases h1 : lo l = a - i ∧ hi l = b - i
    · obtain ⟨ha, hb⟩ := hcond.mp h1
      have hwt := wt_sub_one (n := n) h2 (sh_ne i l)
      rw [sh_sub_one h2, ha, hb] at hwt
      simpa [h1, ha, hb] using hwt
    · simp [h1, hcond.not.mp h1]

end Cslib.SLTower
