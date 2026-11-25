/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Matrix rigidity

The *rigidity* `Matrix.rigidity A r` of a matrix `A` over a field is the least number of entries
of `A` that must be changed to bring its rank down to *at most* `r`: the Hamming distance from `A`
to the set of matrices of rank at most `r`. This is [Lokam2009], Definition 2.1,
`R_A(r) = min {|C| : rank (A + C) ≤ r}`, where `|C|` is the number of nonzero entries of `C`. Here
`B = A + C` is the changed matrix, so `|C|` is the number of entries where `A` and `B` differ
(`Matrix.diffCount`). The target is rank at most `r`, as in [Lokam2009], not rank exactly `r`.
Valiant introduced rigidity [Valiant1977] to prove lower bounds on linear circuits: highly rigid
matrices have no linear circuits of linear size and logarithmic depth
(`Cslib.Circuits.Circuit.Computes.rigidity_le`).

Changing one entry changes the rank by at most one, so `A` must lose `rank A - r` rank and every
matrix needs at least `rank A - r` changes (`Matrix.rank_sub_le_rigidity`). For the identity matrix
of size `n` this is exact: `rigidity 1 r = n - r` (`Matrix.rigidity_one`). Conversely, when
`r ≤ rank A`, choosing an invertible `r × r` submatrix and replacing the complementary
`(|m| - r) × (|n| - r)` block by the Schur-complement product of the bordering blocks brings the
rank down to `r`, so `A.rigidity r ≤ (|m| - r) (|n| - r)` (`Matrix.rigidity_le_mul_sub`, and
`(|n| - r) ^ 2` for square matrices in `Matrix.rigidity_le_sq_sub`; [Lokam2009], §2.1, p. 11).

## Main definitions

* `Matrix.diffCount A B`: the number of entries where `A` and `B` differ.
* `Matrix.rigidity A r`: the least `diffCount A B` over matrices `B` of rank at most `r`.

## Main results

* `Matrix.rigidity_le`: a matrix `B` of rank at most `r` bounds the rigidity by `diffCount A B`.
* `Matrix.exists_rigidity_eq`: some matrix of rank at most `r` attains the rigidity.
* `Matrix.rigidity_antitone`: rigidity decreases as the target rank grows.
* `Matrix.rigidity_eq_zero_iff`: rigidity is zero exactly when the rank is already at most `r`.
* `Matrix.rigidity_zero`: at target rank zero, rigidity counts the nonzero entries.
* `Matrix.rigidity_le_mul_sub`, `Matrix.rigidity_le_sq_sub`: every `m × n` matrix has rigidity at
  most `(|m| - r) (|n| - r)` (and `(|n| - r) ^ 2` when square).
* `Matrix.rank_le_diffCount_zero`: the rank is at most the number of nonzero entries.
* `Matrix.rank_sub_diffCount_le_rank`, `Matrix.rank_sub_le_rigidity`: each change lowers the rank
  by at most one, so every matrix needs at least `rank A - r` changes.
* `Matrix.rigidity_one`: the identity matrix of size `n` has rigidity `n - r`.

## References

* [S. V. Lokam, *Complexity Lower Bounds using Linear Algebra*][Lokam2009], Definition 2.1 and
  §2.1, p. 11
* [L. G. Valiant, *Graph-theoretic arguments in low-level complexity*][Valiant1977]
-/

public section

namespace Matrix

variable {m n K α : Type*}

/-- The number of entries where the matrices `A` and `B` differ.

This counts differing positions with `Set.ncard`, which returns `0` on infinite sets.
`Matrix.rigidity` and all rigidity results below therefore require `[Finite m]` alongside
`[Fintype n]`, so that `diffCount` equals the true Hamming distance on `m × n`. -/
noncomputable def diffCount (A B : Matrix m n α) : ℕ :=
  {p : m × n | A p.1 p.2 ≠ B p.1 p.2}.ncard

theorem diffCount_comm (A B : Matrix m n α) : diffCount A B = diffCount B A := by
  simp only [diffCount, ne_comm]

@[simp] theorem diffCount_self (A : Matrix m n α) : diffCount A A = 0 := by
  simp [diffCount]

variable [Fintype n]

/-- Two matrices differ in at most all of their entries. -/
theorem diffCount_le_card [Fintype m] (A B : Matrix m n α) :
    diffCount A B ≤ Fintype.card m * Fintype.card n := by
  rw [diffCount, ← Fintype.card_prod, ← Nat.card_eq_fintype_card]
  exact Set.ncard_le_card _

/-- For finite matrices, `diffCount` is the size of a filtered `Finset` of positions. -/
theorem diffCount_eq_card_filter [Fintype m] [DecidableEq α] (A B : Matrix m n α) :
    diffCount A B = (Finset.univ.filter fun p : m × n => A p.1 p.2 ≠ B p.1 p.2).card := by
  rw [diffCount, ← Set.ncard_coe_finset]
  exact congrArg Set.ncard (by ext p; simp)

/-- The number of differing entries is the sum over the rows of the number of differing entries
in each row. -/
theorem diffCount_eq_sum [Fintype m] [DecidableEq α] (A B : Matrix m n α) :
    diffCount A B = ∑ i, (Finset.univ.filter fun j => A i j ≠ B i j).card := by
  classical
  rw [diffCount_eq_card_filter, Finset.card_filter, Fintype.sum_prod_type]
  simp [Finset.card_filter]

variable [Field K]

/-- **Matrix rigidity** ([Lokam2009], Definition 2.1): the least number of entries of `A` that must
be changed to make its rank at most `r`. -/
-- Finiteness restricts the public domain; `sInf` and `ncard` themselves do not require it.
@[nolint unusedArguments]
noncomputable def rigidity [Finite m] (A : Matrix m n K) (r : ℕ) : ℕ :=
  sInf (diffCount A '' {B | B.rank ≤ r})

private theorem nonempty_rigiditySet (A : Matrix m n K) (r : ℕ) :
    (diffCount A '' {B : Matrix m n K | B.rank ≤ r}).Nonempty :=
  ⟨_, 0, by simp, rfl⟩

/-- A matrix `B` of rank at most `r` that differs from `A` in `diffCount A B` entries bounds the
rigidity of `A`. -/
theorem rigidity_le [Finite m] {A B : Matrix m n K} {r : ℕ} (hB : B.rank ≤ r) :
    A.rigidity r ≤ diffCount A B :=
  Nat.sInf_le ⟨B, hB, rfl⟩

/-- Rigidity is at most the number of entries. -/
theorem rigidity_le_card [Fintype m] (A : Matrix m n K) (r : ℕ) :
    A.rigidity r ≤ Fintype.card m * Fintype.card n :=
  (rigidity_le (B := 0) (by simp)).trans (diffCount_le_card _ _)

section FiniteRows

variable [Finite m]

/-- Some matrix of rank at most `r` differs from `A` in exactly `A.rigidity r` entries. -/
theorem exists_rigidity_eq (A : Matrix m n K) (r : ℕ) :
    ∃ B : Matrix m n K, B.rank ≤ r ∧ diffCount A B = A.rigidity r :=
  Nat.sInf_mem (nonempty_rigiditySet A r)

/-- `s ≤ A.rigidity r` exactly when every matrix of rank at most `r` differs from `A` in at least
`s` entries. -/
theorem le_rigidity_iff {A : Matrix m n K} {r s : ℕ} :
    s ≤ A.rigidity r ↔ ∀ B : Matrix m n K, B.rank ≤ r → s ≤ diffCount A B :=
  ⟨fun h _ hB => h.trans (rigidity_le hB),
    fun h => let ⟨B, hB, hAB⟩ := exists_rigidity_eq A r; hAB ▸ h B hB⟩

/-- Rigidity decreases as the target rank grows. -/
theorem rigidity_antitone (A : Matrix m n K) : Antitone A.rigidity := fun r _ hr =>
  let ⟨_, hB, hAB⟩ := exists_rigidity_eq A r; hAB ▸ rigidity_le (hB.trans hr)

/-- At target rank zero, the rigidity is the number of nonzero entries. -/
theorem rigidity_zero (A : Matrix m n K) : A.rigidity 0 = diffCount A 0 :=
  let ⟨_, hB, hAB⟩ := exists_rigidity_eq A 0; (rank_eq_zero_iff.1 (Nat.le_zero.1 hB) ▸ hAB).symm

/-- No changes are needed when the rank is already at most `r`. -/
theorem rigidity_eq_zero_iff {A : Matrix m n K} {r : ℕ} : A.rigidity r = 0 ↔ A.rank ≤ r := by
  refine ⟨fun h => ?_, fun h => Nat.eq_zero_of_le_zero ((rigidity_le h).trans_eq (by simp))⟩
  obtain ⟨B, hB, hAB⟩ := exists_rigidity_eq A r
  rw [h, diffCount, Set.ncard_eq_zero] at hAB
  have hAB' : A = B := Matrix.ext fun i j => by_contra fun hij =>
    Set.eq_empty_iff_forall_notMem.1 hAB (i, j) hij
  exact hAB' ▸ hB

/-- The rank of a matrix is at most the number of its nonzero entries. -/
theorem rank_le_diffCount_zero (C : Matrix m n K) : C.rank ≤ diffCount C 0 := by
  classical
  have := Fintype.ofFinite m
  refine (rank_le_card_of_support_subset C
    ((Finset.univ.filter fun p : m × n => C p.1 p.2 ≠ 0).image Prod.fst) fun i hi => ?_).trans
    (Finset.card_image_le.trans_eq (diffCount_eq_card_filter C 0).symm)
  obtain ⟨j, hj⟩ : ∃ j, C i j ≠ 0 := by_contra fun h =>
    hi <| funext fun j => by_contra fun hj => h ⟨j, hj⟩
  exact Finset.mem_image.2 ⟨(i, j), by simpa using hj, rfl⟩

/-- **Each change lowers the rank by at most one**: the rank of `B` is at least the rank of `A`
minus the number of entries where they differ. -/
theorem rank_sub_diffCount_le_rank (A B : Matrix m n K) : A.rank - diffCount A B ≤ B.rank := by
  have h := rank_add_le B (A - B); rw [add_sub_cancel] at h
  have : diffCount (A - B) 0 = diffCount A B :=
    congrArg Set.ncard (Set.ext fun _ => not_congr sub_eq_zero)
  have := rank_le_diffCount_zero (A - B); omega

/-- **Rigidity is at least the rank deficit**: at least `rank A - r` entries must be changed to
bring the rank of `A` down to `r`. -/
theorem rank_sub_le_rigidity (A : Matrix m n K) (r : ℕ) : A.rank - r ≤ A.rigidity r := by
  obtain ⟨B, hB, hAB⟩ := exists_rigidity_eq A r
  have := rank_sub_diffCount_le_rank A B
  omega

/-- A matrix of rank at least `r` over a field contains an invertible `r × r` submatrix. -/
private theorem exists_submatrix_mul_eq_one_of_le_rank {A : Matrix m n K} {r : ℕ}
    (hr : r ≤ A.rank) :
    ∃ (f : Fin r → m) (g : Fin r → n) (M' : Matrix (Fin r) (Fin r) K),
      Function.Injective f ∧ Function.Injective g ∧
        A.submatrix f g * M' = 1 ∧ M' * A.submatrix f g = 1 := by
  classical
  have := Fintype.ofFinite m
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.row
  have : Finite κ := Finite.of_injective a ha; have := Fintype.ofFinite κ
  have hκ : r ≤ Fintype.card κ := by
    rwa [← finrank_span_eq_card hli, hspan, ← A.rank_eq_finrank_span_row]
  let e₁ : Fin r → κ := (Fintype.equivFin κ).symm ∘ Fin.castLE hκ
  have he₁ : Function.Injective e₁ := (Equiv.injective _).comp (Fin.castLE_injective hκ)
  have hf_rank : (A.submatrix (a ∘ e₁) id).rank = r :=
    ((hli.comp e₁ he₁ : LinearIndependent K (A.submatrix (a ∘ e₁) id).row).rank_matrix).trans
      (Fintype.card_fin r)
  obtain ⟨κ', b, hb, hspan', hli'⟩ := exists_linearIndependent' K (A.submatrix (a ∘ e₁) id).col
  have : Finite κ' := Finite.of_injective b hb; have := Fintype.ofFinite κ'
  have hκ' : Fintype.card κ' = r := by
    rw [← finrank_span_eq_card hli', hspan', ← rank_eq_finrank_span_cols, hf_rank]
  let e₂ : Fin r ≃ κ' := Fintype.equivOfCardEq (by rw [Fintype.card_fin, hκ'])
  obtain ⟨M', hMM'⟩ := exists_mul_eq_one_of_rank_eq_card <|
    (rank_transpose (A.submatrix (a ∘ e₁) (b ∘ e₂))).symm.trans
      (hli'.comp e₂ e₂.injective).rank_matrix
  exact ⟨a ∘ e₁, b ∘ e₂, M', ha.comp he₁, hb.comp e₂.injective, hMM', mul_eq_one_comm.mp hMM'⟩

end FiniteRows

/-- **Upper bound on matrix rigidity** ([Valiant1977]; [Lokam2009], §2.1, p. 11, for square
matrices). Every `m × n` matrix over a field has rigidity at most `(|m| - r) (|n| - r)` at target
rank `r`: if `rank A ≤ r` no changes are needed, and if `r < rank A` then `A` contains an
invertible `r × r` submatrix `A_{I, J}`, so `A_{·, J} A_{I, J}⁻¹ A_{I, ·}` has rank at most `r`
and agrees with `A` on all of `I × n` and `m × J`. -/
theorem rigidity_le_mul_sub [Fintype m] (A : Matrix m n K) (r : ℕ) :
    A.rigidity r ≤ (Fintype.card m - r) * (Fintype.card n - r) := by
  rcases le_or_gt A.rank r with hle | hlt
  · simp [rigidity_eq_zero_iff.mpr hle]
  obtain ⟨f, g, M', hf, hg, hMM', hM'M⟩ := exists_submatrix_mul_eq_one_of_le_rank hlt.le
  let B : Matrix m n K := A.submatrix id g * M' * A.submatrix f id
  have hBf : B.submatrix f id = A.submatrix f id := by
    change A.submatrix f g * M' * A.submatrix f id = _; rw [hMM', Matrix.one_mul]
  have hBg : B.submatrix id g = A.submatrix id g := by
    change A.submatrix id g * M' * A.submatrix f g = _
    rw [Matrix.mul_assoc, hM'M, Matrix.mul_one]
  have hsub : {p : m × n | A p.1 p.2 ≠ B p.1 p.2} ⊆ (Set.range f)ᶜ ×ˢ (Set.range g)ᶜ :=
    fun ⟨_, _⟩ hij => ⟨fun ⟨a, ha⟩ => hij (ha ▸ congr_fun₂ hBf.symm a _),
      fun ⟨b, hb⟩ => hij (hb ▸ congr_fun₂ hBg.symm _ b)⟩
  refine (rigidity_le <| (rank_mul_le_right _ _).trans
    ((rank_le_card_height _).trans_eq (Fintype.card_fin r))).trans
    ((Set.ncard_le_ncard hsub).trans_eq ?_)
  rw [Set.ncard_prod, Set.ncard_compl, Set.ncard_compl, Set.ncard_range_of_injective hf,
    Set.ncard_range_of_injective hg]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]

/-- **Upper bound on the rigidity of a square matrix** ([Valiant1977]; [Lokam2009], §2.1, p. 11).
Every `n × n` matrix over a field has rigidity at most `(|n| - r) ^ 2` at target rank `r`. -/
theorem rigidity_le_sq_sub (A : Matrix n n K) (r : ℕ) :
    A.rigidity r ≤ (Fintype.card n - r) ^ 2 :=
  sq (Fintype.card n - r) ▸ A.rigidity_le_mul_sub r

section One

variable [DecidableEq n]

/-- **The identity matrix of size `n`** has rigidity exactly `n - r`: zeroing all but `r` diagonal
entries attains the lower bound `Matrix.rank_sub_le_rigidity`. -/
theorem rigidity_one (r : ℕ) : (1 : Matrix n n K).rigidity r = Fintype.card n - r := by
  classical
  refine le_antisymm ?_ (by simpa [rank_one] using rank_sub_le_rigidity (1 : Matrix n n K) r)
  rcases le_total (Fintype.card n) r with h | h
  · simp [Nat.sub_eq_zero_of_le h, rigidity_eq_zero_iff.2 (rank_one.trans_le h)]
  obtain ⟨S, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset n)) h
  let w : n → K := fun i => if i ∈ S then 1 else 0
  have hrank : (diagonal w).rank = r := by
    rw [rank_diagonal, Fintype.card_subtype, ← hS.2]; exact congrArg Finset.card (by ext; simp [w])
  refine (rigidity_le (B := diagonal w) hrank.le).trans_eq ?_
  have hset : {p : n × n | (1 : Matrix n n K) p.1 p.2 ≠ diagonal w p.1 p.2} =
      (fun i => (i, i)) '' ((Sᶜ : Finset n) : Set n) := by
    ext ⟨i, j⟩
    by_cases hij : i = j
    · subst hij; by_cases hi : i ∈ S <;> simp [w, hi]
    · simp [one_apply_ne hij, hij, Ne.symm hij]
  rw [diffCount, hset, Set.ncard_image_of_injective _ (fun _ _ h => (Prod.ext_iff.1 h).1),
    Set.ncard_coe_finset, Finset.card_compl, hS.2]

end One

end Matrix
