/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flag.Uni

/-!
# The block decomposition of the unitriangular group

`U (a + b)` decomposes into the two diagonal blocks `U a × U b` and the upper right block
(`Flag.blk`, a bijection by `Flag.blk_bijective`); the upper right block is the abelian
subgroup `Flag.up`.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Flag.Block`.

## Main definitions

* `Flag.up`, `Flag.blk`.

## Main results

* `Flag.up_add`, `Flag.blk_bijective`.
-/

public section

open Finset Matrix

namespace Cslib.Circuits.Arithmetic.Separation.Flag

open Cslib.SLTower (U SL2 lo hi x)

variable {a b : ℕ}

/-- The inclusion of the first window. -/
abbrev wl (a b : ℕ) : Matrix (Fin (a + b)) (Fin a) F2 := wi (hl (a := a) (b := b))

/-- The inclusion of the second window. -/
abbrev wr (a b : ℕ) : Matrix (Fin (a + b)) (Fin b) F2 := wi (hr (a := a) (b := b))

/-- The elements `1 + M` with `M` in the upper right block. -/
def up (M : Matrix (Fin a) (Fin b) F2) : U (a + b) :=
  mk (1 + wl a b * M * (wr a b)ᵀ)
    (by
      intro i j hij
      rw [Matrix.add_apply, Matrix.one_apply_ne hij.ne', zero_add, Matrix.mul_apply]
      refine sum_eq_zero fun k _ => ?_
      rw [Matrix.mul_apply, sum_mul]
      refine sum_eq_zero fun l _ => ?_
      simp only [incl_apply, weEmb_apply, Matrix.transpose_apply]
      by_cases h1 : i = we (hl (a := a) (b := b)) l
      · by_cases h2 : j = we (hr (a := a) (b := b)) k
        · exfalso
          rw [h1, h2] at hij
          simp only [we, Fin.lt_def] at hij
          omega
        · simp [h2]
      · simp [h1])
    (by
      intro i
      rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply]
      rw [sum_eq_zero, add_zero]
      intro k _
      rw [Matrix.mul_apply, sum_mul]
      refine sum_eq_zero fun l _ => ?_
      simp only [incl_apply, weEmb_apply, Matrix.transpose_apply]
      by_cases h1 : i = we (hl (a := a) (b := b)) l
      · by_cases h2 : i = we (hr (a := a) (b := b)) k
        · exfalso
          rw [h1] at h2
          simp only [we, Fin.ext_iff] at h2
          omega
        · simp [h2]
      · simp [h1])

theorem mat_up (M : Matrix (Fin a) (Fin b) F2) : mat (up M) = 1 + wl a b * M * (wr a b)ᵀ := by
  rw [up, mat_mk]

theorem up_add (M N : Matrix (Fin a) (Fin b) F2) : up (M + N) = up M * up N := by
  apply mat_inj
  rw [mat_mul, mat_up, mat_up, mat_up]
  have : wl a b * M * (wr a b)ᵀ * (wl a b * N * (wr a b)ᵀ) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((wr a b)ᵀ) (wl a b), wi_rl]
    simp
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, this]
  abel

theorem wm_l (A : Matrix (Fin a) (Fin a) F2) : wm (hl (a := a) (b := b)) A =
    wl a b * A * (wl a b)ᵀ + wr a b * (wr a b)ᵀ := by
  rw [wm, Matrix.mul_one, ← wi_add (a := a) (b := b)]
  abel

theorem wm_r (A : Matrix (Fin b) (Fin b) F2) : wm (hr (a := a) (b := b)) A =
    wr a b * A * (wr a b)ᵀ + wl a b * (wl a b)ᵀ := by
  rw [wm, Matrix.mul_one, ← wi_add (a := a) (b := b)]
  abel

/-- The element with given blocks. -/
@[expose] def blk : U a × Matrix (Fin a) (Fin b) F2 × U b → U (a + b)
  | (A, M, C) => win (hr (a := a) (b := b)) C * up M * win (hl (a := a) (b := b)) A

private theorem mat_blk' (t : U a × Matrix (Fin a) (Fin b) F2 × U b) : mat (blk t) =
    wl a b * mat t.1 * (wl a b)ᵀ + wl a b * t.2.1 * (wr a b)ᵀ + wr a b * mat t.2.2 * (wr a b)ᵀ := by
  obtain ⟨A, M, C⟩ := t
  -- a sandwich vanishes when the middle factor does, and collapses when it is the identity
  have z {k k' : ℕ} (W : Matrix (Fin (a + b)) (Fin k) F2) (V : Matrix (Fin (a + b)) (Fin k') F2)
      (h : Wᵀ * V = 0) {c d : ℕ} (P : Matrix (Fin (a + b)) (Fin c) F2)
      (Q : Matrix (Fin d) (Fin (a + b)) F2) (X : Matrix (Fin c) (Fin k) F2)
      (Y : Matrix (Fin k') (Fin d) F2) : P * X * Wᵀ * (V * Y * Q) = 0 := by
    rw [mul_sandwich, h]
    simp
  have e {k : ℕ} (W : Matrix (Fin (a + b)) (Fin k) F2) (h : Wᵀ * W = 1)
      {c d : ℕ} (P : Matrix (Fin (a + b)) (Fin c) F2) (Q : Matrix (Fin d) (Fin (a + b)) F2)
      (X : Matrix (Fin c) (Fin k) F2) (Y : Matrix (Fin k) (Fin d) F2) :
      P * X * Wᵀ * (W * Y * Q) = P * (X * Y) * Q := by
    rw [mul_sandwich, h, Matrix.mul_one]
  have s1 : wl a b * (wl a b)ᵀ = wl a b * (1 : Matrix (Fin a) (Fin a) F2) * (wl a b)ᵀ := by
    rw [Matrix.mul_one]
  have s2 : wr a b * (wr a b)ᵀ = wr a b * (1 : Matrix (Fin b) (Fin b) F2) * (wr a b)ᵀ := by
    rw [Matrix.mul_one]
  change mat (win (hr (a := a) (b := b)) C * up M * win (hl (a := a) (b := b)) A) = _
  rw [mat_mul, mat_mul, mat_win, mat_win, mat_up, wm_l, wm_r, ← wi_add (a := a) (b := b), s1, s2]
  simp only [Matrix.add_mul, Matrix.mul_add, z (wl a b) (wr a b) wi_lr, z (wr a b) (wl a b) wi_rl,
    e (wl a b) (wi_t_mul _), e (wr a b) (wi_t_mul _), add_zero, zero_add]
  simp only [Matrix.mul_one, Matrix.one_mul]
  abel

theorem mat_blk (A : U a) (M : Matrix (Fin a) (Fin b) F2) (C : U b) : mat (blk (A, M, C)) =
    wl a b * mat A * (wl a b)ᵀ + wl a b * M * (wr a b)ᵀ + wr a b * mat C * (wr a b)ᵀ :=
  mat_blk' (A, M, C)

theorem blk_injective : Function.Injective
    (blk : U a × Matrix (Fin a) (Fin b) F2 × U b → U (a + b)) := by
  intro s t hst
  have h := congrArg mat hst
  have proj (t : U a × Matrix (Fin a) (Fin b) F2 × U b) :
      ((wl a b)ᵀ * mat (blk t) * wl a b = mat t.1) ∧
      ((wl a b)ᵀ * mat (blk t) * wr a b = t.2.1) ∧
      ((wr a b)ᵀ * mat (blk t) * wr a b = mat t.2.2) := by
    refine ⟨?_, ?_, ?_⟩ <;> rw [mat_blk']
    · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, wi_t_mul, wi_rl, Matrix.mul_zero,
        Matrix.mul_one, add_zero]
      rw [← Matrix.mul_assoc, wi_t_mul, Matrix.one_mul]
    · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, wi_t_mul, wi_lr, Matrix.mul_zero,
        Matrix.mul_one, zero_add]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, wi_t_mul, wi_lr, Matrix.one_mul,
        Matrix.zero_mul, add_zero]
    · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, wi_t_mul, wi_lr, Matrix.mul_zero,
        Matrix.mul_one, zero_add]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, wi_t_mul, wi_rl, Matrix.one_mul,
        Matrix.zero_mul, zero_add]
  refine Prod.ext (mat_inj ?_) (Prod.ext ?_ (mat_inj ?_))
  · rw [← (proj s).1, ← (proj t).1, h]
  · rw [← (proj s).2.1, ← (proj t).2.1, h]
  · rw [← (proj s).2.2, ← (proj t).2.2, h]

theorem two_mul_tri (n : ℕ) : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
  Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd

theorem tri_add (a b : ℕ) : (a + b) * (a + b - 1) / 2 = a * (a - 1) / 2 + a * b + b *
    (b - 1) / 2 := by
  have h1 := two_mul_tri a
  have h2 := two_mul_tri b
  have h3 := two_mul_tri (a + b)
  have h4 : (a + b) * (a + b - 1) = a * (a - 1) + 2 * (a * b) + b * (b - 1) := by
    rcases a with _ | a
    · simp
    · rcases b with _ | b
      · simp
      · rw [show a + 1 + (b + 1) - 1 = a + b + 1 by omega, Nat.add_sub_cancel, Nat.add_sub_cancel]
        ring
  omega

theorem blk_bijective : Function.Bijective
    (blk : U a × Matrix (Fin a) (Fin b) F2 × U b → U (a + b)) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨blk_injective, ?_⟩
  have hM : Fintype.card (Matrix (Fin a) (Fin b) F2) = 2 ^ (a * b) := by
    change Fintype.card (Fin a → Fin b → F2) = _
    simp [← pow_mul, mul_comm]
  rw [Fintype.card_prod, Fintype.card_prod, hM, Cslib.SLTower.card_U, Cslib.SLTower.card_U,
      Cslib.SLTower.card_U,
    tri_add, pow_add, pow_add]
  ring

end Cslib.Circuits.Arithmetic.Separation.Flag
