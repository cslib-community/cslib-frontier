/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flag.Block
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flag.Words

/-!
# Lengths on `U n`: quotients and the two diagonal blocks

Pulling lengths back along homomorphisms (`GroupSeminorm.comp`), their root mean squares
(`Flag.Len.rms`), and the bound of a length by its restrictions to the two diagonal blocks
(`Flag.S_add_le`).

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Flag.Walk`.

## Main results

* `Flag.Contr.comp`, `Flag.Len.rms_comp`, `Flag.S_add_le`.
-/

public section

open Finset Matrix

namespace Cslib.Circuits.Arithmetic.Separation.Flag

open Cslib.SLTower (U SL2 lo hi x)

theorem three_le {T : Type*} [Fintype T] (c f g k : T → ℝ) (hc : ∀ t, 0 ≤ c t)
    (hg : ∀ t, 0 ≤ g t) (hk : ∀ t, 0 ≤ k t) (h : ∀ t, c t ≤ f t + (g t + k t)) :
    √(∑ t, c t ^ 2) ≤ √(∑ t, f t ^ 2) + (√(∑ t, g t ^ 2) + √(∑ t, k t ^ 2)) := by
  have h1 := sqrt_sum_le univ f (fun t => g t + k t) c hc h
  have h2 := sqrt_sum_le univ g k (fun t => g t + k t)
    (fun t => add_nonneg (hg t) (hk t)) fun t => le_rfl
  linarith

theorem Contr.comp {G H : Type*} [Group G] [Group H] {l : Len H} {m : ℕ} {s : ℝ}
    (h : Contr l m s) (φ : G →* H) : Contr (l.comp φ) m s := by
  intro τ hτ i
  exact h (fun M => φ (τ M)) (fun M N => by rw [hτ, map_mul]) i

/-- The root mean square of a length. -/
noncomputable def Len.rms {G : Type*} [Group G] [Fintype G] (l : Len G) : ℝ :=
  √((∑ g : G, l g ^ 2) / Fintype.card G)

theorem Len.rms_nonneg {G : Type*} [Group G] [Fintype G] (l : Len G) : 0 ≤ l.rms :=
  Real.sqrt_nonneg _

theorem Len.rms_sq {G : Type*} [Group G] [Fintype G] (l : Len G) :
    l.rms ^ 2 = (∑ g : G, l g ^ 2) / Fintype.card G :=
  Real.sq_sqrt (div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _))

/-- The mean square along a surjective homomorphism. -/
theorem Len.rms_comp {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H] (l : Len H)
    (φ : G →* H) (hφ : Function.Surjective φ) : Len.rms (l.comp φ) = l.rms := by
  classical
  unfold Len.rms
  congr 1
  have hG : (0 : ℝ) < Fintype.card G := mod_cast Fintype.card_pos
  have hH : (0 : ℝ) < Fintype.card H := mod_cast Fintype.card_pos
  rw [div_eq_div_iff hG.ne' hH.ne']
  have h1 : ∑ h : H, ∑ g : G, l (h * φ g) ^ 2 = Fintype.card G * ∑ h : H, l h ^ 2 := by
    have e (g) : ∑ h : H, l (h * φ g) ^ 2 = ∑ h : H, l h ^ 2 :=
      Equiv.sum_comp (Equiv.mulRight (φ g)) fun h => l h ^ 2
    rw [sum_comm, sum_congr rfl fun g _ => e g]
    simp
  have h2 : ∑ h : H, ∑ g : G, l (h * φ g) ^ 2 = Fintype.card H * ∑ g : G, l (φ g) ^ 2 := by
    have e (h : H) : ∑ g : G, l (h * φ g) ^ 2 = ∑ g : G, l (φ g) ^ 2 := by
      obtain ⟨k, rfl⟩ := hφ h
      exact (sum_congr rfl fun g _ => by rw [← map_mul φ]; rfl).trans
        (Equiv.sum_comp (Equiv.mulLeft k) fun g => l (φ g) ^ 2)
    rw [sum_congr rfl fun h _ => e h]
    simp
  change (∑ g : G, l (φ g) ^ 2) * _ = _
  linarith

/-- The bound of Lemma lem:first for one n with the constant κ. -/
@[expose] def Bd (m : ℕ) (s : ℝ) (n : ℕ) (κ : ℝ) : Prop :=
  ∀ l : Len (U n), Contr l m s → l.rms ≤ κ * l.S

theorem bd_one (m : ℕ) (s : ℝ) : Bd m s 1 0 := by
  intro l _
  have h1 (g : U 1) : g = 1 := mat_inj <| Matrix.ext fun i j => by
    rw [Subsingleton.elim i j, mat_diag, mat_one, Matrix.one_apply_eq]
  rw [Len.rms, sum_eq_zero fun g _ => by simp [h1 g, map_one_eq_zero l]]
  simp

theorem S_add_le {a b : ℕ} (l : Len (U (a + b))) :
    Len.S (l.comp (win (hl (a := a) (b := b)))) + Len.S (l.comp (win (hr (a := a) (b := b)))) ≤
      l.S := by
  unfold Len.S
  have hblock {p n} (hp : p + n ≤ a + b) :
      ∑ j, (l.comp (win hp)) (x n j) = ∑ k ∈ univ.image (wt hp), l (x _ k) := by
    rw [sum_image fun _ _ _ _ h => by simpa [wt, Fin.ext_iff] using h]
    exact sum_congr rfl fun _ _ => congrArg l (win_x ..)
  rw [hblock hl, hblock hr, ← sum_union]
  · exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => apply_nonneg l _
  · rw [disjoint_left]
    rintro k hk₁ hk₂
    obtain ⟨j, -, rfl⟩ := mem_image.1 hk₁
    obtain ⟨j', -, h⟩ := mem_image.1 hk₂
    simp only [wt, Fin.ext_iff] at h; omega

/-- The upper left block. -/
def tr {n n' : ℕ} (h : n ≤ n') : U n' →* U n where
  toFun A := mk (Matrix.of fun i j => mat A (Fin.castLE h i) (Fin.castLE h j))
    (fun i j hij => mat_lt A (by simpa using hij)) (fun i => mat_diag A _)
  map_one' := by
    apply mat_inj
    ext i j
    change (1 : Matrix _ _ F2) (Fin.castLE h i) (Fin.castLE h j) = (1 : Matrix _ _ F2) i j
    simp [Matrix.one_apply, Fin.ext_iff]
  map_mul' A B := by
    apply mat_inj
    ext i j
    change mat (A * B) (Fin.castLE h i) (Fin.castLE h j) = _
    rw [mat_mul, mat_mul, Matrix.mul_apply, Matrix.mul_apply]
    symm
    refine sum_bij_ne_zero (fun k _ _ => Fin.castLE h k) (fun _ _ _ => mem_univ _)
      (fun k _ _ k' _ _ hk => by simpa [Fin.ext_iff] using hk) ?_ (fun _ _ _ => rfl)
    intro k _ hk
    have hkj : k ≤ Fin.castLE h j := by
      by_contra hlt
      rw [mat_lt B (not_le.1 hlt), mul_zero] at hk
      exact hk rfl
    have hkn : k.1 < n := lt_of_le_of_lt (Fin.le_def.1 hkj) j.2
    exact ⟨⟨k.1, hkn⟩, mem_univ _, hk, rfl⟩

theorem tr_apply {n n' : ℕ} (h : n ≤ n') (A : U n') (i j : Fin n) :
    mat (tr h A) i j = mat A (Fin.castLE h i) (Fin.castLE h j) := by rfl

theorem tr_surjective {n n' : ℕ} (h : n ≤ n') : Function.Surjective (tr h) := by
  intro A
  have h0 : 0 + n ≤ n' := by omega
  refine ⟨win h0 A, mat_inj <| Matrix.ext fun i j => ?_⟩
  have e (k : Fin n) : Fin.castLE h k = we h0 k := by simp [we, Fin.ext_iff]
  rw [tr_apply, mat_win, e, e, wm, Matrix.add_apply, Matrix.sub_apply, wi_mul_we, wi_mul_we]
  simp [Matrix.one_apply, we_inj]

theorem bd_mono {m : ℕ} {s : ℝ} {n n' : ℕ} (h : n ≤ n') {κ : ℝ} (hκ : 0 ≤ κ) (hB : Bd m s n' κ) :
    Bd m s n κ := by
  intro l hC
  have h1 := hB (l.comp (tr h)) (hC.comp _)
  rw [Len.rms_comp _ _ (tr_surjective h)] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ hκ)
  unfold Len.S
  have e (j : Fin (n' - 1)) : (l.comp (tr h)) (x n' j) =
      if hj : j.1 < n - 1 then l (x n ⟨j.1, hj⟩) else 0 := by
    change l (tr h (x n' j)) = _
    split_ifs with hj
    · refine congrArg l (mat_inj <| Matrix.ext fun a b => ?_)
      simp [tr_apply, mat_x, Matrix.one_apply, Matrix.single_apply, lo, hi, Fin.ext_iff]
    · have htr : tr h (x n' j) = 1 := mat_inj <| Matrix.ext fun a b => by
        have : ¬(j.1 = a.1 ∧ j.1 + 1 = b.1) := by
          have := b.2
          omega
        simp [tr_apply, mat_x, mat_one, Matrix.one_apply, lo, hi, Fin.ext_iff, this]
      rw [htr, map_one_eq_zero l]
  rw [sum_congr rfl fun j _ => e j,
    ← sum_filter_add_sum_filter_not univ (fun j : Fin (n' - 1) => j.1 < n - 1),
    sum_eq_zero (s := univ.filter fun j : Fin (n' - 1) => ¬ j.1 < n - 1)
      (fun j hj => by simp [(mem_filter.1 hj).2]), add_zero]
  exact le_of_eq <| sum_bij' (fun j hj => ⟨j.1, (mem_filter.1 hj).2⟩)
    (fun j _ => ⟨j.1, by have := j.2; omega⟩) (fun _ _ => mem_univ _)
    (fun j _ => by simp [j.2]) (fun _ _ => rfl) (fun _ _ => rfl)
    fun j hj => by simp [(mem_filter.1 hj).2]

end Cslib.Circuits.Arithmetic.Separation.Flag
