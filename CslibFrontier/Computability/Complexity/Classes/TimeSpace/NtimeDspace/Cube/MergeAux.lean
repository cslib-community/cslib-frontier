/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.Clique
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.Pieces

/-!
# Helpers for the merge (§6.1)

General bookkeeping used by the proof of Lemma 6.2 in `Cslib.Complexity.NtimeDspace.Cube.Merge`.

* `prod_pairs`, `prod_offDiag`, `prod_rect`: products over the pairs `A < A'` of `Fin g`, over the
  ordered pairs of distinct elements, and over the rectangles (a rectangle is a pair of rows and a
  pair of columns, `mkRect`).
* `sum_piFinset_prod`: a sum over functions into product sets is a double sum.
* `eval_one_eq_sum`: evaluating a Laurent polynomial at `1` sums its coefficients.
* `pairStart`, `card_pairs`: counting the pairs `B < B'` of `Fin g` (used for the lexicographic
  numbering of the pairs in `Cslib.Complexity.NtimeDspace.Cube.Merge`).
* `sum_valid_unpack`: the packing bijection of (eq:pack) as an identity of sums. For a numbering
  `σ` of the streams `1, …, L - 1` by an index type `I`, a sum over the valid labels of weight
  `L ∑ w` of a product of factors of the unpacked streams is the product of the sums over the
  streams, provided each factor vanishes outside a finite set of labels of weight at most `w i`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset

/-! ### Products over pairs and rectangles -/

theorem prod_pairs {M : Type*} [CommMonoid M] {g : ℕ} (f : Fin g → Fin g → M) :
    ∏ p : Pairs g, f p.1.1 p.1.2 = ∏ A, ∏ A', if A < A' then f A A' else 1 := by
  calc ∏ p : Pairs g, f p.1.1 p.1.2
      = ∏ p ∈ univ.filter (fun p : Fin g × Fin g => p.1 < p.2), f p.1 p.2 :=
        (Finset.prod_subtype (p := fun p : Fin g × Fin g => p.1 < p.2) _ (by simp)
          (fun p => f p.1 p.2)).symm
    _ = _ := by rw [Finset.prod_filter, Fintype.prod_prod_type]

theorem prod_offDiag {M : Type*} [CommMonoid M] {g : ℕ} (f : Fin g → Fin g → M) :
    ∏ A, ∏ A', (if A' ≠ A then f A A' else 1) = ∏ p : Pairs g, f p.1.1 p.1.2 * f p.1.2 p.1.1 := by
  rw [Finset.prod_mul_distrib, prod_pairs, prod_pairs (fun A A' => f A' A),
    Finset.prod_comm (f := fun A A' => if A < A' then f A' A else 1), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun A _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun A' _ => ?_
  rcases lt_trichotomy A A' with h | h | h
  · simp [h, h.ne', not_lt_of_gt h]
  · simp [h]
  · simp [h, h.ne, not_lt_of_gt h]

/-- The rectangle with rows `p` and columns `q`. -/
def mkRect {g : ℕ} (p q : Pairs g) : Rect g := ⟨(p.1, q.1), p.2, q.2⟩

/-- Rectangles are pairs of row pairs and column pairs. -/
def rectEquiv (g : ℕ) : Pairs g × Pairs g ≃ Rect g where
  toFun pq := mkRect pq.1 pq.2
  invFun r := (⟨r.1.1, r.2.1⟩, ⟨r.1.2, r.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl

theorem prod_rect {M : Type*} [CommMonoid M] {g : ℕ} (f : Rect g → M) :
    ∏ r, f r = ∏ p, ∏ q, f (mkRect p q) := by
  rw [← Fintype.prod_prod_type']
  exact (Fintype.prod_equiv (rectEquiv g) (fun pq => f (mkRect pq.1 pq.2)) f fun _ => rfl).symm

theorem prod_hor_form {g : ℕ} (e : Fin g → Fin g → Fin g → Prop) [∀ A B B', Decidable (e A B B')] :
    (∏ A, ∏ B, ∏ B', if B < B' ∧ ¬ e A B B' then (0 : ℤ) else 1) =
      ∏ p : Pairs g, ∏ A, if e A p.1.1 p.1.2 then (1 : ℤ) else 0 := by
  rw [prod_pairs (fun B B' => ∏ A, if e A B B' then (1 : ℤ) else 0), Finset.prod_comm]
  refine Finset.prod_congr rfl fun B _ => ?_
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun B' _ => ?_
  by_cases h : B < B' <;> simp [h]

/-! ### Sums over product sets -/

theorem sum_piFinset_prod {ι α β M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    (s : ι → Finset α) (t : ι → Finset β)
    (F : (ι → α × β) → M) :
    ∑ x ∈ Fintype.piFinset (fun i => s i ×ˢ t i), F x =
      ∑ k ∈ Fintype.piFinset s, ∑ c ∈ Fintype.piFinset t, F fun i => (k i, c i) := by
  classical
  refine Eq.trans ?_ (Finset.sum_product' (Fintype.piFinset s) (Fintype.piFinset t)
    (fun k c => F fun i => (k i, c i)))
  refine Finset.sum_nbij' (fun x => (fun i => (x i).1, fun i => (x i).2))
    (fun kc i => (kc.1 i, kc.2 i)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Fintype.mem_piFinset, Finset.mem_product] at hx ⊢
    exact ⟨fun i => (hx i).1, fun i => (hx i).2⟩
  · intro kc hkc
    simp only [Fintype.mem_piFinset, Finset.mem_product] at hkc ⊢
    exact fun i => ⟨hkc.1 i, hkc.2 i⟩
  · intro x _; rfl
  · intro kc _; rfl
  · intro x _; rfl

/-! ### Evaluation at one -/

open LaurentPolynomial in
theorem eval_one_eq_finsuppSum (f : Lp) :
    eval₂ (RingHom.id ℤ) 1 f = f.coeff.sum fun _ a => a := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, hp, hq, AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index'] <;> simp
  | C_mul_T n a =>
    rw [eval₂_C_mul_T, ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
      Finsupp.sum_single_index] <;> simp

open LaurentPolynomial in
theorem eval_one_eq_sum (f : Lp) (s : Finset ℤ) (hs : ∀ k, f.coeff k ≠ 0 → k ∈ s) :
    eval₂ (RingHom.id ℤ) 1 f = ∑ k ∈ s, f.coeff k := by
  rw [eval_one_eq_finsuppSum, Finsupp.sum]
  exact Finset.sum_subset (fun k hk => hs k (Finsupp.mem_support_iff.mp hk))
    (fun k _ hk => Finsupp.notMem_support_iff.mp hk)

/-! ### Numbering the pairs -/

/-- `∑_{b < B} (g - 1 - b)`, the number of pairs with first element below `B`. -/
def pairStart (g B : ℕ) : ℕ := ∑ b ∈ range B, (g - 1 - b)

theorem pairStart_mono (g : ℕ) {B₁ B₂ : ℕ} (h : B₁ ≤ B₂) : pairStart g B₁ ≤ pairStart g B₂ :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

theorem pairStart_succ (g B : ℕ) : pairStart g (B + 1) = pairStart g B + (g - 1 - B) :=
  Finset.sum_range_succ _ _

theorem pairStart_self (g : ℕ) : pairStart g g = g.choose 2 := by
  rw [pairStart, Finset.sum_range_reflect (fun b => b) g, Finset.sum_range_id,
    Nat.choose_two_right]

theorem card_pairs (g : ℕ) : Fintype.card (Pairs g) = g.choose 2 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  have : ∀ B : Fin g, (∑ B' : Fin g, if B < B' then 1 else 0) = g - 1 - B.val := by
    intro B
    rw [← Finset.card_filter, Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  simp only [this]
  rw [Fin.sum_univ_eq_sum_range (fun b => g - 1 - b) g, ← pairStart, pairStart_self]

/-! ### Packing as an identity of sums -/

theorem pack_congr {L a : ℕ} {s₁ s₂ : ℕ → Label} (h : ∀ s ∈ Ioo 0 L, s₁ s = s₂ s) :
    pack L a s₁ = pack L a s₂ := by
  have h1 : packDir L (fun s => (s₁ s).1) = packDir L (fun s => (s₂ s).1) :=
    Finset.sum_congr rfl fun s hs => by simp only [h s hs]
  have h2 : packDir L (fun s => (s₁ s).2) = packDir L (fun s => (s₂ s).2) :=
    Finset.sum_congr rfl fun s hs => by simp only [h s hs]
  simp only [pack, h1, h2]

theorem sum_valid_unpack {L : ℕ} (hL : 2 ≤ L) {I : Type*} [Fintype I]
    (σ : I → ℕ) (hσ : Function.Injective σ) (hσI : univ.image σ = Ioo 0 L)
    (S : I → Finset Label) (w : I → ℕ) (hw : ∀ i, ∀ m ∈ S i, labelWt m ≤ w i)
    (F : I → Label → ℤ) (hF : ∀ i m, F i m ≠ 0 → m ∈ S i) :
    ∑ l ∈ labelsEq (L * ∑ i, w i), (if validLabel L l then ∏ i, F i (unpack L l (σ i)) else 0) =
      ∏ i, ∑ m ∈ S i, F i m := by
  classical
  have hσmem : ∀ i, σ i ∈ Ioo 0 L := fun i => hσI ▸ mem_image_of_mem σ (mem_univ i)
  have hmem : ∀ s ∈ Ioo 0 L, ∃ i, σ i = s := by
    intro s hs; rw [← hσI] at hs; simpa using hs
  let st : (I → Label) → ℕ → Label := fun M s => if h : ∃ i, σ i = s then M h.choose else (0, 0)
  have hst : ∀ M i, st M (σ i) = M i := by
    intro M i
    have h : ∃ j, σ j = σ i := ⟨i, rfl⟩
    simp only [st, dite_eq_left h]; rw [hσ h.choose_spec]
  have hsum : ∀ h : ℕ → ℕ, ∑ s ∈ Ioo 0 L, h s = ∑ i, h (σ i) := by
    intro h; rw [← hσI, sum_image (fun x _ y _ hxy => hσ hxy)]
  have hbound : ∀ M ∈ Fintype.piFinset S,
      labelWt (packDir L (fun s => (st M s).1), packDir L fun s => (st M s).2) ≤ L * ∑ i, w i := by
    intro M hM
    refine (labelWt_packDir_le L (st M)).trans (Nat.mul_le_mul_left _ ?_)
    rw [hsum (fun s => labelWt (st M s))]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hst]; exact hw i _ (Fintype.mem_piFinset.mp hM i)
  rw [prod_univ_sum]
  symm
  refine Finset.sum_bij_ne_zero (fun M _ _ => pack L (L * ∑ i, w i) (st M)) ?_ ?_ ?_ ?_
  · intro M hM _
    exact mem_labelsEq.mpr (pack_valid L hL (st M) (hbound M hM)).2
  · intro M₁ hM₁ _ M₂ hM₂ _ heq
    funext i
    have := congrArg (fun l => unpack L l (σ i)) heq
    rwa [unpack_pack L hL _ (hbound M₁ hM₁) (hσmem i), unpack_pack L hL _ (hbound M₂ hM₂) (hσmem i),
      hst, hst] at this
  · intro l hl hne
    have hw' := mem_labelsEq.mp hl
    by_cases hv : validLabel L l
    · rw [ite_eq_left hv] at hne
      have hne' := Finset.prod_ne_zero_iff.mp hne
      refine ⟨fun i => unpack L l (σ i), ?_, ?_, ?_⟩
      · exact Fintype.mem_piFinset.mpr fun i => hF i _ (hne' i (mem_univ i))
      · exact hne
      · rw [pack_congr (s₂ := unpack L l), pack_unpack L hL l hv hw']
        intro s hs
        obtain ⟨i, rfl⟩ := hmem s hs
        exact hst (fun i => unpack L l (σ i)) i
    · rw [ite_eq_right hv] at hne; exact absurd rfl hne
  · intro M hM _
    rw [ite_eq_left (pack_valid L hL (st M) (hbound M hM)).1]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [unpack_pack L hL _ (hbound M hM) (hσmem i), hst]

end Cslib.Complexity.NtimeDspace.Cube
