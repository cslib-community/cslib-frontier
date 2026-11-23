/-
Copyright (c) 2026 Samuel Schlesinger, Shengye Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Shengye Tao
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rigidity.Hadamard
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rigidity.WalshBand
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rigidity.WalshCounts

/-!
# Finite non-rigidity of Sylvester–Hadamard matrices

Correct the exceptional rows and columns of the interpolation matrix. All surviving
disagreements lie on the counted central off-band pairs. Reindex by bit supports to
obtain total and per-row budgets for the native Sylvester matrix over any field.
`Matrix.rigidity_sylvesterHadamard_le` bounds total edits by an explicit binomial sum.
Given a bound on the sum for each central row weight,
`Matrix.exists_rank_le_sylvesterHadamard_row_edits_le_of_row_sum_le` produces a common
low-rank witness meeting the edit budget in every row. To deduce Theorem 1.1 one still
needs asymptotic estimates for the rank cutoff and the off-band tails.

See [Alman and Williams, §3][AlmanWilliams2017].
-/

public section

namespace Cslib

open Finset

/-- Correcting exceptional rows and columns costs at most one rank per exceptional index. -/
private theorem correct_rows_cols {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (H A : Matrix ι ι K) (bad : Finset ι) :
    ∃ B : Matrix ι ι K, B.rank ≤ A.rank + 2 * bad.card ∧
      ∀ x y, B x y = if x ∈ bad ∨ y ∈ bad then H x y else A x y := by
  classical
  let R : Matrix ι ι K := fun x y => if x ∈ bad then H x y - A x y else 0
  let C : Matrix ι ι K := fun x y => if x ∉ bad ∧ y ∈ bad then H x y - A x y else 0
  have hR : R.rank ≤ bad.card := by
    apply Matrix.rank_le_card_of_support_subset
    rw [Function.support_subset_iff']
    intro x hx
    ext y
    change (if x ∈ bad then H x y - A x y else 0) = 0
    exact ite_eq_right hx
  have hC : C.transpose.rank ≤ bad.card := by
    apply Matrix.rank_le_card_of_support_subset
    rw [Function.support_subset_iff']
    intro x hx
    ext y
    change (if y ∉ bad ∧ x ∈ bad then H y x - A y x else 0) = 0
    exact ite_eq_right fun h => hx h.2
  rw [Matrix.rank_transpose] at hC
  refine ⟨A + R + C, ?_, ?_⟩
  · have h₁ := Matrix.rank_add_le A R
    have h₂ := Matrix.rank_add_le (A + R) C
    omega
  · intro x y
    change A x y + R x y + C x y = _
    by_cases hx : x ∈ bad <;> by_cases hy : y ∈ bad <;>
      simp [R, C, hx, hy]

/-- Corrected entries agree on exceptional rows, exceptional columns and central on-band pairs. -/
private theorem walshBandWitness : ∀ (K : Type*) [Field K] (n lo hi k t : ℕ),
  let H : Matrix (Finset (Fin n)) (Finset (Fin n)) K :=
    Matrix.of fun x y => (-1 : K) ^ (x ∩ y).card
  let bad := ∑ a ∈ Finset.range (n + 1), if lo ≤ a ∧ a ≤ hi then 0 else n.choose a
  let r := (∑ j : Fin t, n.choose j) + 2 * bad
  ∃ B : Matrix (Finset (Fin n)) (Finset (Fin n)) K, B.rank ≤ r ∧
    ∀ x y, H x y ≠ B x y → lo ≤ x.card ∧ x.card ≤ hi ∧ lo ≤ y.card ∧ y.card ≤ hi ∧
      ((x ∩ y).card < k ∨ k + t ≤ (x ∩ y).card) := by
  intro K _ n lo hi k t
  classical
  let H : Matrix (Finset (Fin n)) (Finset (Fin n)) K := Matrix.of fun x y =>
    (-1 : K) ^ (x ∩ y).card
  let bad := univ.filter fun x : Finset (Fin n) => ¬(lo ≤ x.card ∧ x.card ≤ hi)
  obtain ⟨A, hr, hon⟩ := exists_low_rank_eq_walsh_on_band K n k t
  obtain ⟨B, hB, hentries⟩ := correct_rows_cols H A bad
  have hb : bad.card = ∑ a ∈ range (n + 1), if lo ≤ a ∧ a ≤ hi then 0 else n.choose a := by
    let g (a : ℕ) := if lo ≤ a ∧ a ≤ hi then 0 else 1
    calc
      _ = ∑ x : Finset (Fin n), g x.card := by
        have hg (a : ℕ) : g a = if ¬(lo ≤ a ∧ a ≤ hi) then 1 else 0 := by
          rw [ite_not]
        simp_rw [hg]
        simp [bad]
      _ = ∑ x ∈ (univ : Finset (Fin n)).powerset, g x.card := by simp
      _ = _ := by
        rw [sum_powerset]
        simp_rw [sum_powersetCard]
        simp [g, mul_ite]
  refine ⟨B, hB.trans (by rw [hb]; exact Nat.add_le_add_right hr _), ?_⟩
  intro x y hne
  have good : ¬(x ∈ bad ∨ y ∈ bad) := fun h => hne ((hentries x y).trans (ite_eq_left h)).symm
  have hx : lo ≤ x.card ∧ x.card ≤ hi := by simpa [bad] using (fun h => good (Or.inl h) : x ∉ bad)
  have hy : lo ≤ y.card ∧ y.card ≤ hi := by simpa [bad] using (fun h => good (Or.inr h) : y ∉ bad)
  refine ⟨hx.1, hx.2, hy.1, hy.2, ?_⟩
  by_contra! inside
  apply hne
  rw [hentries, ite_eq_right good, hon x y inside.1 inside.2]
  rfl

/-- The corrected band matrix witnesses an explicit upper bound on total rigidity. -/
private theorem walshRigidityFinite : ∀ (K : Type*) [Field K] (n lo hi k t : ℕ),
  let H : Matrix (Finset (Fin n)) (Finset (Fin n)) K :=
    Matrix.of fun x y => (-1 : K) ^ (x ∩ y).card
  let bad := ∑ a ∈ Finset.range (n + 1), if lo ≤ a ∧ a ≤ hi then 0 else n.choose a
  let r := (∑ j : Fin t, n.choose j) + 2 * bad
  H.rigidity r ≤ ∑ a ∈ Finset.range (n + 1), if lo ≤ a ∧ a ≤ hi then
    n.choose a * (∑ j ∈ Finset.range (a + 1), ∑ b ∈ Finset.range (n - a + 1),
      if lo ≤ j + b ∧ j + b ≤ hi ∧ (j < k ∨ k + t ≤ j)
      then a.choose j * (n - a).choose b else 0)
  else 0 := by
  intro K _ n lo hi k t
  classical
  obtain ⟨B, hr, hloc⟩ := walshBandWitness K n lo hi k t
  apply (Matrix.rigidity_le (B := B) hr).trans
  rw [Matrix.diffCount_eq_card_filter, ← card_off_band_pair]
  apply card_le_card
  intro ⟨x, y⟩ hp
  exact mem_filter.mpr ⟨mem_univ _, hloc x y (mem_filter.mp hp).2⟩

/-- A uniform upper bound on the central binomial row sums bounds every row of one witness. -/
private theorem walshBandRowWitness (K : Type*) [Field K] (n lo hi k t edits : ℕ)
    (hrow : ∀ a ≤ n, lo ≤ a → a ≤ hi →
      (∑ j ∈ range (a + 1), ∑ b ∈ range (n - a + 1),
        if lo ≤ j + b ∧ j + b ≤ hi ∧ (j < k ∨ k + t ≤ j)
        then a.choose j * (n - a).choose b else 0) ≤ edits) :
    let H : Matrix (Finset (Fin n)) (Finset (Fin n)) K := Matrix.of fun x y =>
      (-1 : K) ^ (x ∩ y).card
    let bad := ∑ a ∈ range (n + 1), if lo ≤ a ∧ a ≤ hi then 0 else n.choose a
    ∃ B : Matrix (Finset (Fin n)) (Finset (Fin n)) K,
      B.rank ≤ (∑ j : Fin t, n.choose j) + 2 * bad ∧
      ∀ x, ({y | H x y ≠ B x y} : Set (Finset (Fin n))).ncard ≤ edits := by
  classical
  obtain ⟨B, hr, hloc⟩ := walshBandWitness K n lo hi k t
  refine ⟨B, hr, fun x => ?_⟩
  by_cases hx : lo ≤ x.card ∧ x.card ≤ hi
  · have h := hrow x.card (by simpa using x.card_le_univ) hx.1 hx.2
    rw [← card_off_band_row n lo hi k t x] at h
    apply le_trans _ h
    rw [← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard ?_ (Finset.finite_toSet _)
    intro y hy
    exact mem_filter.mpr ⟨mem_univ _, (hloc x y hy).2.2⟩
  · have hempty : {y | _} = (∅ : Set (Finset (Fin n))) :=
      Set.eq_empty_iff_forall_notMem.mpr fun y h => hx ⟨(hloc x y h).1, (hloc x y h).2.1⟩
    rw [hempty, Set.ncard_empty]
    exact Nat.zero_le _




/-- Pulling back a matrix along an equivalence transports a minimum-edit witness. -/
private theorem rigidity_submatrix_le {ι κ K : Type*} [Fintype ι] [Fintype κ] [Field K]
    (A : Matrix ι ι K) (e : κ ≃ ι) (r : ℕ) : (A.submatrix e e).rigidity r ≤ A.rigidity r := by
  classical
  obtain ⟨B, hr, hdiff⟩ := A.exists_rigidity_eq r
  apply (Matrix.rigidity_le (B := B.submatrix e e) (by simpa using hr)).trans
  rw [← hdiff]
  let d : κ × κ ≃ ι × ι := e.prodCongr e
  simp only [Matrix.diffCount_eq_card_filter]
  apply le_of_eq
  apply card_bij (fun p _ => d p)
  · intro p hp
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hp).2⟩
  · exact fun _ _ _ _ h => d.injective h
  · intro p hp
    refine ⟨d.symm p, mem_filter.mpr ⟨mem_univ _, ?_⟩, d.apply_symm_apply _⟩
    simpa [d, Matrix.submatrix_apply] using (mem_filter.mp hp).2

/-- The native Sylvester matrix is the support-indexed Walsh matrix with permuted indices. -/
private theorem exists_sylvester_reindex (K : Type*) [Field K] (n : ℕ) :
    ∃ e : Fin (2 ^ n) ≃ Finset (Fin n), ∀ i j, Matrix.sylvesterHadamard K n i j =
      (-1 : K) ^ (e i ∩ e j).card := by
  let s (i : Fin (2 ^ n)) := univ.filter (fun b : Fin n => i.val.testBit b.val)
  have inj : Function.Injective s := by
    intro i j h
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro b
    by_cases hb : b < n
    · have hmem := congrArg (fun z : Finset (Fin n) => decide ((⟨b,hb⟩ : Fin n) ∈ z)) h
      simpa [s] using hmem
    · have hp : 2 ^ n ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow (i.isLt.trans_le hp), Nat.testBit_lt_two_pow (j.isLt.trans_le hp)]
  let e := Equiv.ofBijective s ((Fintype.bijective_iff_injective_and_card s).mpr ⟨inj, by simp⟩)
  refine ⟨e, ?_⟩
  intro i j
  rw [Matrix.sylvesterHadamard_apply,
    ← Fin.prod_univ_eq_prod_range]
  change (∏ b : Fin n, if i.val.testBit b.val && j.val.testBit b.val then (-1 : K) else 1) =
    (-1 : K) ^ (s i ∩ s j).card
  have cond (b : Fin n) : (i.val.testBit b.val && j.val.testBit b.val) = true ↔ b ∈ s i ∩ s j := by
    simp [s]
  simp_rw [cond]
  rw [← prod_filter]
  have hs : univ.filter (fun b => b ∈ s i ∩ s j) = s i ∩ s j := by ext b; simp
  rw [hs, prod_const]

/-- Finite step toward [Alman and Williams, Theorem 1.1][AlmanWilliams2017].
At the displayed rank cutoff, the number of central off-band pairs bounds the rigidity
of the native Sylvester matrix over any field. -/
theorem _root_.Matrix.rigidity_sylvesterHadamard_le (K : Type*) [Field K] (n lo hi k t : ℕ) :
    let H := Matrix.sylvesterHadamard K n
    let bad := ∑ a ∈ Finset.range (n + 1), if lo ≤ a ∧ a ≤ hi then 0 else n.choose a
    let r := (∑ j : Fin t, n.choose j) + 2 * bad
    H.rigidity r ≤ ∑ a ∈ Finset.range (n + 1), if lo ≤ a ∧ a ≤ hi then
      n.choose a * (∑ j ∈ Finset.range (a + 1), ∑ b ∈ Finset.range (n - a + 1),
        if lo ≤ j + b ∧ j + b ≤ hi ∧ (j < k ∨ k + t ≤ j)
        then a.choose j * (n - a).choose b else 0)
    else 0 := by
  obtain ⟨e, he⟩ := exists_sylvester_reindex K n
  let H : Matrix (Finset (Fin n)) (Finset (Fin n)) K := Matrix.of fun x y =>
    (-1 : K) ^ (x ∩ y).card
  have hm : Matrix.sylvesterHadamard K n = H.submatrix e e := Matrix.ext he
  dsimp only
  rw [hm]
  exact (rigidity_submatrix_le H e _).trans (walshRigidityFinite K n lo hi k t)

/-- Summing a uniform edit budget over the rows bounds the total rigidity. -/
private theorem rigidity_le_of_row_edits {ι K : Type*} [Fintype ι] [Field K]
    {H B : Matrix ι ι K} {r edits : ℕ} (hr : B.rank ≤ r)
    (hrow : ∀ x, ({y | H x y ≠ B x y} : Set ι).ncard ≤ edits) :
    H.rigidity r ≤ Fintype.card ι * edits := by
  classical
  apply (Matrix.rigidity_le (B := B) hr).trans
  rw [Matrix.diffCount_eq_card_filter]
  calc
    _ = ∑ x : ι, ∑ y : ι, if H x y ≠ B x y then 1 else 0 := by
      rw [← sum_product', ← sum_filter]
      simp
    _ ≤ ∑ _ : ι, edits := by
      apply sum_le_sum
      intro x _
      have heq : (↑(univ.filter fun y => H x y ≠ B x y) : Set ι) = {y | H x y ≠ B x y} := by
        ext y; simp
      have h := hrow x
      rw [← heq, Set.ncard_coe_finset] at h
      rw [← sum_filter]
      simpa using h
    _ = _ := by simp

/-- Conditional finite step toward [Alman and Williams, Theorem 1.1][AlmanWilliams2017].
A bound on each central row's binomial sum gives one low-rank native witness for all rows. -/
theorem _root_.Matrix.exists_rank_le_sylvesterHadamard_row_edits_le_of_row_sum_le
    (K : Type*) [Field K] (n lo hi k t edits : ℕ)
    (hrow : ∀ a ≤ n, lo ≤ a → a ≤ hi →
      (∑ j ∈ range (a + 1), ∑ b ∈ range (n - a + 1),
        if lo ≤ j + b ∧ j + b ≤ hi ∧ (j < k ∨ k + t ≤ j)
        then a.choose j * (n - a).choose b else 0) ≤ edits) :
    let H := Matrix.sylvesterHadamard K n
    let bad := ∑ a ∈ range (n + 1), if lo ≤ a ∧ a ≤ hi then 0 else n.choose a
    let r := (∑ j : Fin t, n.choose j) + 2 * bad
    H.rigidity r ≤ 2 ^ n * edits ∧
      ∃ B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) K, B.rank ≤ r ∧
        ∀ x, ({y | H x y ≠ B x y} : Set (Fin (2 ^ n))).ncard ≤ edits := by
  obtain ⟨e, he⟩ := exists_sylvester_reindex K n
  obtain ⟨B, hr, hb⟩ := walshBandRowWitness K n lo hi k t edits hrow
  let H : Matrix (Finset (Fin n)) (Finset (Fin n)) K := Matrix.of fun x y =>
    (-1 : K) ^ (x ∩ y).card
  have hm : Matrix.sylvesterHadamard K n = H.submatrix e e := Matrix.ext he
  have rows (i : Fin (2 ^ n)) :
      ({j | Matrix.sylvesterHadamard K n i j ≠ B.submatrix e e i j} : Set _).ncard ≤ edits := by
    rw [hm]
    change (e ⁻¹' {y | H (e i) y ≠ B (e i) y}).ncard ≤ edits
    rw [Set.ncard_preimage_of_injective_subset_range e.injective (by simp [e.surjective.range_eq])]
    exact hb (e i)
  refine ⟨?_, B.submatrix e e, by simpa using hr, rows⟩
  simpa using rigidity_le_of_row_edits (by simpa using hr) rows

end Cslib
