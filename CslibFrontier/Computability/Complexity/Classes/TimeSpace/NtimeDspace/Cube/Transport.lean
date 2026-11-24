/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.PieceFacts
public import Mathlib.Data.Int.Interval
import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.RowCut
import Mathlib.Data.List.GetD

/-!
# The transport recursion (Lemma 5.6)

For a list of sources `l` and a multiset of targets `T` (each a place and a type of weight
`type + 1`), `transportL l T R` is the transport sum with the sources in the order of `l`. Its
weight is `W(l, T)`, the total weight of the sources and targets. Splitting every assignment at the
first source `l[ν]` at which the running weight of the sources and their targets reaches `W/2`
gives the recursion of the proof of Lemma 5.6 (Appendix A):

  `[z^c] N(l, T) = ∑_{ν, t, T₁} [W(l₁,T₁) < W/2 ≤ W(l₁,T₁) + wt l[ν] + wt t]
      ∑_{c₁, c₀} [z^{c₁}] N(l₁, T₁) · [z^{c₀}] R(l[ν], t) · [z^{c - c₁ - c₀}] N(l₂, T - T₁ - t)`,

with `l₁ = take ν l`, `l₂ = drop (ν+1) l`, `t` a target (place and type) of `T`, and `T₁` a
sub-multiset of `T - {t}`. Both subproblems weigh at most `W/2`. If every rule has exponents at
most the weights of its ends in absolute value, every exponent of `N(l, T)` is at most `W(l, T)` in
absolute value, so `c₁` and `c₀` range over `[-W, W]`.

## Main results

* `transportL_nil`: the empty source list.
* `transportL_exp_le`: the exponent bound.
* `transportL_pivot`: the pivot recursion.
* `pivot_halves`: both subproblems of a contributing term weigh at most `W/2`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset

variable {P : Type} [DecidableEq P]

/-- The weight of a located request: its type plus one. -/
def lwt (s : P × ℕ) : ℕ := s.2 + 1

/-- The weight of sources and targets. -/
def tWt (l : List (P × ℕ)) (T : Multiset (P × ℕ)) : ℕ := (l.map lwt).sum + (T.map lwt).sum

/-- The transport sum with sources listed in the order of `l`. -/
noncomputable def transportL (l : List (P × ℕ)) (T : Multiset (P × ℕ)) (R : P → ℕ → P → ℕ → Lp) :
    Lp :=
  transport (↑l) T R

/-- The rules are bounded: every exponent of `R s t` is at most `wt s + wt t` in absolute value. -/
def RuleBounded (R : P → ℕ → P → ℕ → Lp) : Prop :=
  ∀ p i p' j e, (R p i p' j).coeff e ≠ 0 → |e| ≤ (i + 1 : ℤ) + (j + 1)

/-! ### Source forms over a larger set of targets -/

theorem transportL_cons (s : P × ℕ) (l : List (P × ℕ)) (T : Multiset (P × ℕ))
    (R : P → ℕ → P → ℕ → Lp) :
    transportL (s :: l) T R = ∑ t ∈ T.toFinset, R s.1 s.2 t.1 t.2 * transportL l (T - {t}) R := by
  simp only [transportL, Multiset.sub_singleton]
  exact transport_cons s (↑l) T R

theorem transportL_perm {l l' : List (P × ℕ)} (h : l.Perm l') (T : Multiset (P × ℕ))
    (R : P → ℕ → P → ℕ → Lp) : transportL l T R = transportL l' T R := by
  unfold transportL
  rw [Multiset.coe_eq_coe.mpr h]

/-- **The last-source recursion.** -/
theorem transportL_concat (l : List (P × ℕ)) (s : P × ℕ) (T : Multiset (P × ℕ))
    (R : P → ℕ → P → ℕ → Lp) :
    transportL (l ++ [s]) T R = ∑ t ∈ T.toFinset, R s.1 s.2 t.1 t.2 * transportL l (T - {t}) R := by
  rw [transportL_perm (List.perm_append_singleton s l), transportL_cons]

theorem transportL_nil (T : Multiset (P × ℕ)) (R : P → ℕ → P → ℕ → Lp) :
    transportL [] T R = if T = 0 then 1 else 0 := by
  unfold transportL transport
  rw [Multiset.coe_nil, Multiset.map_zero, Multiset.prod_zero, MvPolynomial.coeff_one]
  have h : (0 = Multiset.toFinsupp T) ↔ T = 0 := by
    rw [eq_comm, ← Multiset.toFinsupp_zero (α := P × ℕ)]
    exact Multiset.toFinsupp.injective.eq_iff
  simp only [h]

/-! ### The exponent bound -/

/-- Laurent polynomials whose exponents are at most `n` in absolute value. -/
private def absGroup (n : ℕ) : AddSubgroup Lp where
  carrier := {f | ∀ e, f.coeff e ≠ 0 → |e| ≤ n}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg e he
    simp only [Set.mem_ofPred_eq, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at hf hg he
    by_cases h : f.coeff e = 0
    · rw [h, zero_add] at he; exact hg e he
    · exact hf e h
  neg_mem' := by
    intro f hf e he
    simp only [Set.mem_ofPred_eq, AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, ne_eq,
      neg_eq_zero] at hf he
    exact hf e he

private theorem absGroup_mul {a b : ℕ} {x y : Lp} (hx : x ∈ absGroup a) (hy : y ∈ absGroup b) :
    x * y ∈ absGroup (a + b) := by
  classical
  intro e he
  obtain ⟨e₁, h₁, e₂, h₂, rfl⟩ :=
    Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset x y
        (Finsupp.mem_support_iff.mpr he))
  have q₁ := hx e₁ (Finsupp.mem_support_iff.mp h₁)
  have q₂ := hy e₂ (Finsupp.mem_support_iff.mp h₂)
  rw [abs_le] at q₁ q₂ ⊢
  push_cast
  constructor <;> omega

private theorem one_mem_absGroup : (1 : Lp) ∈ absGroup 0 := by
  intro e he
  rw [← LaurentPolynomial.T_zero, LaurentPolynomial.T_apply] at he
  split_ifs at he with h
  · subst h; simp
  · exact absurd rfl he

theorem transportL_exp_le {R : P → ℕ → P → ℕ → Lp} (hR : RuleBounded R) (l : List (P × ℕ))
    (T : Multiset (P × ℕ)) (e : ℤ) (h : (transportL l T R).coeff e ≠ 0) :
    |e| ≤ tWt l T := by
  have hmem := transportG_mem absGroup (fun _ _ _ _ => absGroup_mul) one_mem_absGroup lwt (↑l) T R
    (fun s _ t _ e he => by
      have := hR s.1 s.2 t.1 t.2 e he
      simp only [lwt]; exact_mod_cast this)
  have hw : ((↑l : Multiset (P × ℕ)).map lwt).sum + (T.map lwt).sum = tWt l T := by
    simp [tWt]
  rw [hw] at hmem
  exact hmem e h

/-! ### The pivot recursion -/

/-- The pivot condition: the source `l[ν]` with target `t`, after the prefix sent to `T₁`, is the
first at which the running weight reaches half of `W`. -/
def PivotCond (l : List (P × ℕ)) (T : Multiset (P × ℕ)) (ν : ℕ) (t : P × ℕ)
    (T₁ : Multiset (P × ℕ)) : Prop :=
  2 * tWt (l.take ν) T₁ < tWt l T ∧ tWt l T ≤ 2 * (tWt (l.take ν) T₁ + lwt (l.getD ν t) + lwt t)

instance (l : List (P × ℕ)) (T : Multiset (P × ℕ)) (ν : ℕ) (t : P × ℕ) (T₁ : Multiset (P × ℕ)) :
    Decidable (PivotCond l T ν t T₁) := by unfold PivotCond; infer_instance

/-- Splitting the weight at a source `l[k]` sent to `t ∈ T`, after the prefix sent to `T₁`. -/
theorem tWt_split {l : List (P × ℕ)} {T : Multiset (P × ℕ)} {k : ℕ} {t : P × ℕ}
    {T₁ : Multiset (P × ℕ)} (hk : k < l.length) (ht : t ∈ T) (hT₁ : T₁ ≤ T - {t}) :
    tWt l T = tWt (l.take k) T₁ + lwt (l.getD k t) + lwt t + tWt (l.drop (k + 1))
        (T - T₁ - {t}) := by
  have hle : T₁ + {t} ≤ T := (le_tsub_iff_right (Multiset.singleton_le.mpr ht)).mp hT₁
  have hT : T = T₁ + {t} + (T - T₁ - {t}) := by
    rw [← tsub_add_eq_tsub_tsub, add_tsub_cancel_of_le hle]
  have hTs : (T.map lwt).sum = (T₁.map lwt).sum + lwt t + ((T - T₁ - {t}).map lwt).sum := by
    conv_lhs => rw [hT]
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_singleton, Multiset.sum_singleton]
  have hl : (l.map lwt).sum =
      ((l.take k).map lwt).sum + lwt l[k] + ((l.drop (k + 1)).map lwt).sum := by
    conv_lhs => rw [← List.take_append_drop k l, List.drop_eq_getElem_cons hk]
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    omega
  unfold tWt
  rw [List.getD_eq_getElem _ _ hk, hl, hTs]
  omega

private theorem ite_sum_zero {ι M : Type*} [AddCommMonoid M] (p : Prop) [Decidable p]
    (s : Finset ι) (f : ι → M) :
    (if p then ∑ i ∈ s, f i else 0) = ∑ i ∈ s, if p then f i else 0 := by
  split_ifs <;> simp

private theorem mem_sub_iff {α : Type*} [DecidableEq α] {T T₁ : Multiset α} {t : α} :
    (T₁ ≤ T ∧ t ∈ T - T₁) ↔ T₁ + {t} ≤ T := by
  constructor
  · rintro ⟨h1, h2⟩
    exact (le_tsub_iff_left h1).mp (Multiset.singleton_le.mpr h2)
  · intro h
    have h1 : T₁ ≤ T := le_trans (Multiset.le_add_right _ _) h
    exact ⟨h1, Multiset.singleton_le.mp ((le_tsub_iff_left h1).mpr h)⟩

private theorem le_sub_singleton_iff {α : Type*} [DecidableEq α] {T T₁ : Multiset α} {t : α} :
    (T₁ ≤ T - {t} ∧ t ∈ T) ↔ T₁ + {t} ≤ T := by
  constructor
  · rintro ⟨h1, h2⟩
    exact (le_tsub_iff_right (Multiset.singleton_le.mpr h2)).mp h1
  · intro h
    have h1 : {t} ≤ T := le_trans (Multiset.le_add_left _ _) h
    exact ⟨(le_tsub_iff_right h1).mpr h, Multiset.singleton_le.mp h1⟩

/-- Sums over a sub-multiset and one of its elements, reindexed by the element and the rest. -/
private theorem sum_powerset_mem {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (T : Multiset α) (F : Multiset α → α → M) :
    ∑ T₁ ∈ T.powerset.toFinset, ∑ t ∈ T₁.toFinset, F T₁ t =
      ∑ t ∈ T.toFinset, ∑ T₁ ∈ (T - {t}).powerset.toFinset, F (T₁ + {t}) t := by
  have himg : ∀ t, ∑ T₁ ∈ (T - {t}).powerset.toFinset, F (T₁ + {t}) t =
      ∑ T₁ ∈ (T - {t}).powerset.toFinset.image (· + {t}), F T₁ t := by
    intro t
    rw [Finset.sum_image fun a _ b _ h => add_right_cancel h]
  simp only [himg]
  refine Finset.sum_comm' fun T₁ t => ?_
  simp only [Multiset.mem_toFinset, Multiset.mem_powerset, Finset.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨T₁ - {t}, tsub_le_tsub_right h1 _,
      tsub_add_cancel_of_le (Multiset.singleton_le.mpr h2)⟩, Multiset.mem_of_le h1 h2⟩
  · rintro ⟨⟨T₂, h1, rfl⟩, h2⟩
    exact ⟨le_sub_singleton_iff.mp ⟨h1, h2⟩, Multiset.mem_add.mpr
        (Or.inr (Multiset.mem_singleton_self _))⟩

/-- The terms whose running weight after the first `k` sources is below half of `W`. -/
private noncomputable def partialSum (l : List (P × ℕ)) (T : Multiset (P × ℕ))
    (R : P → ℕ → P → ℕ → Lp) (k : ℕ) : Lp :=
  ∑ T₁ ∈ T.powerset.toFinset, if 2 * tWt (l.take k) T₁ < tWt l T then
    transportL (l.take k) T₁ R * transportL (l.drop k) (T - T₁) R else 0

/-- The terms whose pivot is the source `l[k]`. -/
private noncomputable def pivotTerm (l : List (P × ℕ)) (T : Multiset (P × ℕ))
    (R : P → ℕ → P → ℕ → Lp) (k : ℕ) : Lp :=
  ∑ t ∈ T.toFinset, ∑ T₁ ∈ (T - {t}).powerset.toFinset,
    if PivotCond l T k t T₁ then
      transportL (l.take k) T₁ R * R (l.getD k t).1 (l.getD k t).2 t.1 t.2 *
        transportL (l.drop (k + 1)) (T - T₁ - {t}) R
    else 0

private theorem partialSum_zero {l : List (P × ℕ)} (hl : l ≠ []) (T : Multiset (P × ℕ))
    (R : P → ℕ → P → ℕ → Lp) : partialSum l T R 0 = transportL l T R := by
  have hW : 0 < tWt l T := by
    obtain ⟨s, l', rfl⟩ := List.exists_cons_of_ne_nil hl
    simp [tWt, lwt]
  unfold partialSum
  rw [Finset.sum_eq_single (0 : Multiset (P × ℕ))]
  · have h0 : tWt [] (0 : Multiset (P × ℕ)) = 0 := by simp [tWt]
    simp [transportL_nil, h0, hW]
  · intro T₁ _ h
    simp [transportL_nil, h]
  · intro h
    exact absurd (by simp) h

private theorem partialSum_length (l : List (P × ℕ)) (T : Multiset (P × ℕ))
    (R : P → ℕ → P → ℕ → Lp) : partialSum l T R l.length = 0 := by
  unfold partialSum
  refine Finset.sum_eq_zero fun T₁ hT₁ => ?_
  rw [Multiset.mem_toFinset, Multiset.mem_powerset] at hT₁
  rw [List.take_length, List.drop_length, transportL_nil]
  by_cases h : T₁ = T
  · subst h
    have : ¬ 2 * tWt l T₁ < tWt l T₁ := by omega
    simp [this]
  · have : T - T₁ ≠ 0 := fun h' => h (le_antisymm hT₁ (tsub_eq_zero_iff_le.mp h'))
    simp [this]

private theorem partialSum_sub (l : List (P × ℕ)) (T : Multiset (P × ℕ))
    (R : P → ℕ → P → ℕ → Lp) {k : ℕ} (hk : k < l.length) :
    partialSum l T R k - partialSum l T R (k + 1) = pivotTerm l T R k := by
  have e1 : partialSum l T R k = ∑ t ∈ T.toFinset, ∑ T₁ ∈ (T - {t}).powerset.toFinset,
      if 2 * tWt (l.take k) T₁ < tWt l T then
        transportL (l.take k) T₁ R * (R l[k].1 l[k].2 t.1 t.2 *
          transportL (l.drop (k + 1)) (T - T₁ - {t}) R) else 0 := by
    unfold partialSum
    rw [List.drop_eq_getElem_cons hk]
    simp only [transportL_cons, Finset.mul_sum, ite_sum_zero]
    refine Finset.sum_comm' fun T₁ t => ?_
    simp only [Multiset.mem_toFinset, Multiset.mem_powerset]
    rw [mem_sub_iff, le_sub_singleton_iff]
  have e2 : partialSum l T R (k + 1) = ∑ t ∈ T.toFinset, ∑ T₁ ∈ (T - {t}).powerset.toFinset,
      if 2 * tWt (l.take k ++ [l[k]]) (T₁ + {t}) < tWt l T then
        R l[k].1 l[k].2 t.1 t.2 * transportL (l.take k) (T₁ + {t} - {t}) R *
          transportL (l.drop (k + 1)) (T - (T₁ + {t})) R else 0 := by
    unfold partialSum
    rw [List.take_succ_eq_append_getElem hk]
    simp only [transportL_concat, Finset.sum_mul, ite_sum_zero]
    exact sum_powerset_mem T _
  rw [e1, e2, ← Finset.sum_sub_distrib]
  unfold pivotTerm
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun T₁ _ => ?_
  have hsplit : tWt (l.take k ++ [l[k]]) (T₁ + {t}) = tWt (l.take k) T₁ + lwt l[k] + lwt t := by
    simp only [tWt, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Multiset.map_add, Multiset.sum_add, Multiset.map_singleton,
      Multiset.sum_singleton]
    omega
  rw [hsplit, add_tsub_cancel_right, tsub_add_eq_tsub_tsub]
  simp only [PivotCond, List.getD_eq_getElem _ _ hk]
  split_ifs <;> first | (exfalso; omega) | ring1

/-- Coefficients of a product, with the exponents of the left factor restricted to `I`. -/
private theorem coeff_mul_of_support (I : Finset ℤ) {f : Lp} (hf : ∀ e, f.coeff e ≠ 0 → e ∈ I)
    (g : Lp) (x : ℤ) : (f * g).coeff x = ∑ a ∈ I, f.coeff a * g.coeff (x - a) := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left,
    Finsupp.sum_of_support_subset _ (fun e he => hf e (Finsupp.mem_support_iff.mp he)) _
      (by simp)]
  simp [neg_add_eq_sub]

private theorem coeff_sum' {ι : Type*} (s : Finset ι) (f : ι → Lp) (c : ℤ) :
    (∑ i ∈ s, f i).coeff c = ∑ i ∈ s, (f i).coeff c := by
  rw [AddMonoidAlgebra.coeff_sum]
  exact map_sum (Finsupp.applyAddHom c) (fun i => (f i).coeff) s

/-- **The pivot recursion** (Lemma 5.6). -/
theorem transportL_pivot {R : P → ℕ → P → ℕ → Lp} (hR : RuleBounded R) (l : List (P × ℕ))
    (hl : l ≠ []) (T : Multiset (P × ℕ)) (c : ℤ) :
    (transportL l T R).coeff c =
      ∑ ν ∈ range l.length, ∑ t ∈ T.toFinset, ∑ T₁ ∈ (T - {t}).powerset.toFinset,
        if PivotCond l T ν t T₁ then
          ∑ c₁ ∈ Icc (-(tWt l T : ℤ)) (tWt l T), ∑ c₀ ∈ Icc (-(tWt l T : ℤ)) (tWt l T),
            (transportL (l.take ν) T₁ R).coeff c₁ *
              (R (l.getD ν t).1 (l.getD ν t).2 t.1 t.2).coeff c₀ *
              (transportL (l.drop (ν + 1)) (T - T₁ - {t}) R).coeff (c - c₁ - c₀)
        else 0 := by
  have htel : transportL l T R = ∑ k ∈ range l.length, pivotTerm l T R k := by
    rw [Finset.sum_congr rfl fun k hk => (partialSum_sub l T R (mem_range.mp hk)).symm,
      Finset.sum_range_sub', partialSum_zero hl, partialSum_length, sub_zero]
  rw [htel, coeff_sum']
  refine Finset.sum_congr rfl fun k hk => ?_
  unfold pivotTerm
  rw [coeff_sum']
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [coeff_sum']
  refine Finset.sum_congr rfl fun T₁ hT₁ => ?_
  rw [Finset.mem_range] at hk
  rw [Multiset.mem_toFinset] at ht
  rw [Multiset.mem_toFinset, Multiset.mem_powerset] at hT₁
  split_ifs with hPC
  · have hs := tWt_split hk ht hT₁
    simp only [lwt] at hs
    obtain ⟨h1, -⟩ := hPC
    have hA : ∀ e, (transportL (l.take k) T₁ R).coeff e ≠ 0 →
        e ∈ Icc (-(tWt l T : ℤ)) (tWt l T) := by
      intro e he
      have := transportL_exp_le hR _ _ e he
      rw [abs_le] at this
      rw [Finset.mem_Icc]
      omega
    have hB : ∀ e, (R (l.getD k t).1 (l.getD k t).2 t.1 t.2).coeff e ≠ 0 →
        e ∈ Icc (-(tWt l T : ℤ)) (tWt l T) := by
      intro e he
      have := hR _ _ _ _ e he
      rw [abs_le] at this
      rw [Finset.mem_Icc]
      omega
    rw [mul_assoc, coeff_mul_of_support _ hA]
    refine Finset.sum_congr rfl fun c₁ _ => ?_
    rw [coeff_mul_of_support _ hB, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c₀ _ => ?_
    ring
  · simp

/-- Both subproblems of a contributing term weigh at most half of `W`. -/
theorem pivot_halves (l : List (P × ℕ)) (T : Multiset (P × ℕ)) (ν : ℕ) (t : P × ℕ)
    (T₁ : Multiset (P × ℕ)) (hν : ν < l.length) (ht : t ∈ T) (hT₁ : T₁ ≤ T - {t})
    (h : PivotCond l T ν t T₁) :
    2 * tWt (l.take ν) T₁ ≤ tWt l T ∧ 2 * tWt (l.drop (ν + 1)) (T - T₁ - {t}) ≤ tWt l T := by
  have hs := tWt_split hν ht hT₁
  obtain ⟨h1, h2⟩ := h
  constructor <;> omega

end Cslib.Complexity.NtimeDspace.Cube
