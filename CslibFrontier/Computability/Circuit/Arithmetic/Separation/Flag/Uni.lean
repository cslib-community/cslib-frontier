/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flag.Rank
public import CslibFrontier.Foundations.GroupTheory.SLTower.UT

/-!
# The unitriangular group: matrices, windows, blocks

The matrix of an element of `U h` (`Flag.mat`) and its inverse construction (`Flag.mk`), and the
windows: the embedding `Flag.win` of `U n` into `U h` on the indices `p, …, p + n − 1`.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Flag.Uni`.

## Main definitions

* `Flag.mat`, `Flag.mk`, `Flag.win`.

## Main results

* `Flag.mat_inj`, `Flag.mat_mk`, `Flag.mat_win`, `Flag.win_x`.
-/

public section

open Finset Matrix

namespace Cslib.Circuits.Arithmetic.Separation.Flag

open Cslib.SLTower (U SL2 lo hi x)

/-- The matrix of an element. -/
abbrev mat {h : ℕ} (A : U h) : Matrix (Fin h) (Fin h) F2 := A.1.1

theorem mat_inj {h : ℕ} {A B : U h} (hAB : mat A = mat B) : A = B := Subtype.ext (Subtype.ext hAB)

theorem mat_mul {h : ℕ} (A B : U h) : mat (A * B) = mat A * mat B := rfl

theorem mat_one {h : ℕ} : mat (1 : U h) = 1 := rfl

theorem mat_x {h : ℕ} (j : Fin (h - 1)) : mat (x h j) = 1 + Matrix.single (lo j) (hi j) 1 := rfl

theorem mat_lt {h : ℕ} (A : U h) {i j : Fin h} (hij : j < i) : mat A i j = 0 :=
    (Cslib.SLTower.mem_U.mp A.2 i j).1 hij

theorem mat_diag {h : ℕ} (A : U h) (i : Fin h) : mat A i i = 1 := (Cslib.SLTower.mem_U.mp A.2 i i).2

/-- An element from its matrix. -/
@[expose] def mk {h : ℕ} (M : Matrix (Fin h) (Fin h) F2) (h0 : ∀ i j, j < i → M i j = 0)
    (h1 : ∀ i, M i i = 1) : U h :=
  ⟨⟨M, by
    rw [Matrix.det_of_isUpperTriangular]
    · simp [h1]
    · intro i j hij
      exact h0 i j hij⟩, Cslib.SLTower.mem_U.mpr fun i j => ⟨h0 i j, h1 i⟩⟩

theorem mat_mk {h : ℕ} (M : Matrix (Fin h) (Fin h) F2) (h0 : ∀ i j, j < i → M i j = 0)
    (h1 : ∀ i, M i i = 1) : mat (mk M h0 h1) = M := by rfl

/-- Regrouping a product of two sandwiches `P X Wᵀ` and `V Y Q` around the middle factor
`Wᵀ V`. -/
theorem mul_sandwich {k c d e f : ℕ} (P : Matrix (Fin k) (Fin c) F2) (X : Matrix (Fin c) (Fin d) F2)
    (W : Matrix (Fin k) (Fin d) F2) (V : Matrix (Fin k) (Fin e) F2) (Y : Matrix (Fin e) (Fin f) F2)
    (Q : Matrix (Fin f) (Fin k) F2) :
    P * X * Wᵀ * (V * Y * Q) = P * (X * (Wᵀ * V) * Y) * Q := by
  simp only [Matrix.mul_assoc]

section Win
variable {p n h : ℕ} (hp : p + n ≤ h)

/-- The place of an index of a window. -/
@[expose] def we (i : Fin n) : Fin h := ⟨p + i.1, by omega⟩

theorem we_inj {i j : Fin n} : we hp i = we hp j ↔ i = j := by
  simp only [we, Fin.ext_iff]; omega

theorem we_lt {i j : Fin n} : we hp i < we hp j ↔ i < j := by
  simp only [we, Fin.lt_def]; omega

/-- The window as an embedding. -/
@[expose] def weEmb : Fin n ↪ Fin h := ⟨we hp, fun _ _ e => (we_inj hp).1 e⟩

@[simp] theorem weEmb_apply (a : Fin n) : weEmb hp a = we hp a := rfl

/-- The inclusion matrix of a window. -/
abbrev wi : Matrix (Fin h) (Fin n) F2 := incl (weEmb hp)

theorem wi_t_mul : (wi hp)ᵀ * wi hp = 1 := incl_t_mul _

theorem wi_mul_apply (A : Matrix (Fin n) (Fin n) F2) (i j : Fin h) :
    (wi hp * A * (wi hp)ᵀ) i j =
      ∑ b, ∑ a, if i = we hp a ∧ j = we hp b then A a b else 0 := by
  simp only [Matrix.mul_apply, wi, incl_apply, weEmb_apply, Matrix.transpose_apply,
    sum_mul]
  refine sum_congr rfl fun b _ => sum_congr rfl fun a _ => ?_
  by_cases h1 : i = we hp a <;> by_cases h2 : j = we hp b <;> simp [h1, h2]

theorem wi_mul_we (A : Matrix (Fin n) (Fin n) F2) (a b : Fin n) :
    (wi hp * A * (wi hp)ᵀ) (we hp a) (we hp b) = A a b := by
  rw [wi_mul_apply, sum_eq_single b (fun c _ hc => by simp [we_inj, hc.symm]) (by simp),
    sum_eq_single a (fun c _ hc => by simp [we_inj, hc.symm]) (by simp)]
  simp

theorem wi_mul_not (A : Matrix (Fin n) (Fin n) F2) {i : Fin h} (hi : ∀ a, i ≠ we hp a)
    (j : Fin h) : (wi hp * A * (wi hp)ᵀ) i j = 0 := by
  simp [wi_mul_apply, hi]

theorem wi_mul_not' (A : Matrix (Fin n) (Fin n) F2) {j : Fin h} (hj : ∀ a, j ≠ we hp a)
    (i : Fin h) : (wi hp * A * (wi hp)ᵀ) i j = 0 := by
  simp [wi_mul_apply, hj]

/-- The matrix of a window element. -/
@[expose] def wm (A : Matrix (Fin n) (Fin n) F2) : Matrix (Fin h) (Fin h) F2 :=
  wi hp * A * (wi hp)ᵀ + (1 - wi hp * (1 : Matrix (Fin n) (Fin n) F2) * (wi hp)ᵀ)

theorem wm_one : wm hp 1 = 1 := by
  simp [wm]

theorem wm_mul (A B : Matrix (Fin n) (Fin n) F2) : wm hp (A * B) = wm hp A * wm hp B := by
  have hmul (C D : Matrix (Fin n) (Fin n) F2) :
      (wi hp * C * (wi hp)ᵀ) * (wi hp * D * (wi hp)ᵀ) = wi hp * (C * D) * (wi hp)ᵀ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((wi hp)ᵀ) (wi hp), wi_t_mul, Matrix.one_mul]
  unfold wm
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, hmul]
  simp only [Matrix.mul_one, Matrix.one_mul]
  abel

/-- The embedding of the unitriangular group of a window. -/
def win : U n →* U h where
  toFun A := mk (wm hp (mat A))
    (by
      intro i j hij
      unfold wm
      rw [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply_ne hij.ne']
      by_cases h1 : ∃ a, i = we hp a
      · obtain ⟨a, rfl⟩ := h1
        by_cases h2 : ∃ b, j = we hp b
        · obtain ⟨b, rfl⟩ := h2
          have hba : b < a := (we_lt hp).1 hij
          rw [wi_mul_we, wi_mul_we, mat_lt A hba, Matrix.one_apply_ne hba.ne']
          simp
        · push Not at h2
          rw [wi_mul_not' hp _ h2, wi_mul_not' hp _ h2]
          simp
      · push Not at h1
        rw [wi_mul_not hp _ h1, wi_mul_not hp _ h1]
        simp)
    (by
      intro i
      unfold wm
      rw [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply_eq]
      by_cases h1 : ∃ a, i = we hp a
      · obtain ⟨a, rfl⟩ := h1
        rw [wi_mul_we, wi_mul_we, mat_diag, Matrix.one_apply_eq]
        simp
      · push Not at h1
        rw [wi_mul_not hp _ h1, wi_mul_not hp _ h1]
        simp)
  map_one' := mat_inj (by rw [mat_mk, mat_one, wm_one, mat_one])
  map_mul' A B := mat_inj (by rw [mat_mk, mat_mul, wm_mul]; rfl)

theorem mat_win (A : U n) : mat (win hp A) = wm hp (mat A) := by rfl

/-- The place of a type of a window. -/
@[expose] def wt (j : Fin (n - 1)) : Fin (h - 1) := ⟨p + j.1, by omega⟩

theorem win_x (j : Fin (n - 1)) : win hp (x n j) = x h (wt hp j) := by
  apply mat_inj
  rw [mat_win, mat_x, mat_x, wm, Matrix.mul_add, Matrix.add_mul]
  have : wi hp * Matrix.single (lo j) (hi j) (1 : F2) * (wi hp)ᵀ =
      Matrix.single (lo (wt hp j)) (hi (wt hp j)) (1 : F2) := by
    ext a b
    rw [wi_mul_apply, Matrix.single_apply, sum_eq_single (hi j), sum_eq_single (lo j)]
    · rw [show we hp (lo j) = lo (wt hp j) from rfl, show we hp (hi j) = hi (wt hp j) from rfl,
        Matrix.single_apply_same]
      simp only [eq_comm]
    · intro c _ hc
      rw [Matrix.single_apply_of_ne]
      · simp
      · exact fun h => hc h.1.symm
    · simp
    · intro c _ hc
      refine sum_eq_zero fun d _ => ?_
      rw [Matrix.single_apply_of_ne]
      · simp
      · exact fun h => hc h.2.symm
    · simp
  rw [this]
  abel

end Win

section Blocks
variable {a b : ℕ}

theorem hl : 0 + a ≤ a + b := by omega
theorem hr : a + b ≤ a + b := le_rfl

theorem wi_lr : (wi (hl (a := a) (b := b)))ᵀ * wi (hr (a := a) (b := b)) = 0 :=
  incl_t_mul_eq_zero _ _ fun i j => by
    simp only [weEmb_apply, we, ne_eq, Fin.ext_iff]; omega

theorem wi_rl : (wi (hr (a := a) (b := b)))ᵀ * wi (hl (a := a) (b := b)) = 0 := by
  rw [← Matrix.transpose_transpose (wi (hl (a := a) (b := b))), ← Matrix.transpose_mul, wi_lr,
    Matrix.transpose_zero]

theorem wi_add : wi (hl (a := a) (b := b)) * (wi (hl (a := a) (b := b)))ᵀ +
    wi (hr (a := a) (b := b)) * (wi (hr (a := a) (b := b)))ᵀ = 1 := by
  have hrow {p n : ℕ} (hp : p + n ≤ a + b) (k : Fin n) (j : Fin (a + b)) :
      (wi hp * (wi hp)ᵀ) (we hp k) j =
        (1 : Matrix (Fin (a + b)) (Fin (a + b)) F2) (we hp k) j := by
    by_cases hj : ∃ l, j = we hp l
    · obtain ⟨l, rfl⟩ := hj
      have h1 := wi_mul_we hp 1 k l
      rw [Matrix.mul_one] at h1
      simp [h1, Matrix.one_apply, we_inj]
    · push Not at hj
      have h1 := wi_mul_not' hp 1 hj (we hp k)
      rw [Matrix.mul_one] at h1
      simp [h1, (hj k).symm]
  ext i j
  rw [Matrix.add_apply]
  by_cases hi : i.1 < a
  · obtain ⟨k, rfl⟩ : ∃ k, i = we (hl (a := a) (b := b)) k := ⟨⟨i.1, hi⟩, by simp [we]⟩
    have hnot (c : Fin b) : we (hl (a := a) (b := b)) k ≠ we (hr (a := a) (b := b)) c := by
      simp only [we, ne_eq, Fin.ext_iff]; omega
    have h0 := wi_mul_not (hr (a := a) (b := b)) 1 hnot j
    rw [Matrix.mul_one] at h0
    rw [hrow, h0, add_zero]
  · obtain ⟨k, rfl⟩ : ∃ k, i = we (hr (a := a) (b := b)) k :=
      ⟨⟨i.1 - a, by omega⟩, by simp only [we, Fin.ext_iff]; omega⟩
    have hnot (c : Fin a) : we (hr (a := a) (b := b)) k ≠ we (hl (a := a) (b := b)) c := by
      simp only [we, ne_eq, Fin.ext_iff]; omega
    have h0 := wi_mul_not (hl (a := a) (b := b)) 1 hnot j
    rw [Matrix.mul_one] at h0
    rw [hrow, h0, zero_add]

end Blocks

end Cslib.Circuits.Arithmetic.Separation.Flag
