/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SetFamily/Bollobas.lean`)

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Defs.LinearOrder

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Rat.Cast.Order
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bollobás set-pairs inequalities

We formalize two classical extremal set-theory bounds for cross-intersecting pairs of finite
sets `(A i, B i)`:

* **Bollobás's two-families inequality** [Bollobas1965] (see also [Jukna2011, Section 8.4]): if
  `A i` and `B i` are disjoint for each `i ∈ s`, and `¬ Disjoint (A i) (B j)` whenever `i ≠ j` in
  `s`, then
  `∑ i ∈ s, ((#(A i) + #(B i)).choose #(A i) : K)⁻¹ ≤ 1`,
  yielding `#s ≤ (r + t).choose r` whenever `#(A i) ≤ r` and `#(B i) ≤ t` on `s`. Proved by
  element-deletion induction on `|⋃ i ∈ s, A i ∪ B i|`.
* **Frankl's skew Bollobás theorem** [Frankl1982] (see also [Jukna2011, Section 8.4]): for a
  linearly ordered finite index type `ι`, weakening the off-diagonal condition to the one-sided
  requirement `i < j → ¬ Disjoint (A i) (B j)` still yields `Fintype.card ι ≤ (r + s).choose r`
  when `#(A i) ≤ r` and `#(B i) ≤ s`. Proved via the rational moment curve in `Fin (r + s) → ℚ`,
  exterior powers `⋀[ℚ]^s (Fin (r + s) → ℚ)`, and the Vandermonde determinant. (Unlike the
  symmetric case, the LYM sum `∑ ((#(A i) + #(B i)).choose #(A i))⁻¹ ≤ 1` fails under the skew
  hypothesis, e.g. for `({0}, ∅), (∅, {0})` with sum `2 > 1`.)

Notice that `hdiag` together with `hoff` (respectively `hskew`) forces the map `i ↦ (A i, B i)`
and `A` itself to be injective on `s` (respectively `ι`), so bounds on the index cardinality apply
equally to the number of distinct pairs. Exact theorem numbers and page locators in
[Bollobas1965], [Frankl1982], and [Jukna2011] were not checked against the primary sources.

## Main results

* `Finset.sum_inv_choose_le_one_of_disjoint`: Bollobás's LYM-type two-families inequality.
* `Finset.card_le_choose_of_disjoint`: bounded-size corollary `#s ≤ (r + t).choose r`.
* `Fintype.card_le_choose_of_lt_not_disjoint`: Frankl's skew two-families inequality.

## References

* [B. Bollobás, *On Generalized Graphs*][Bollobas1965]
* [P. Frankl, *An Extremal Problem for Two Families of Sets*][Frankl1982]
* [S. Jukna, *Extremal Combinatorics*][Jukna2011]
-/

public section

open Finset

section Symmetric

private theorem inv_choose_add_step {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a b u : ℕ} (ha : 1 ≤ a) (habu : a + b ≤ u) :
    (a : K) * (((a - 1 + b).choose (a - 1) : ℕ) : K)⁻¹ +
        ((u - (a + b) : ℕ) : K) * (((a + b).choose a : ℕ) : K)⁻¹ =
      (u : K) * (((a + b).choose a : ℕ) : K)⁻¹ := by
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
  have h1 : ((k + b).choose k : K) ≠ 0 := mod_cast (Nat.choose_pos (Nat.le_add_right k b)).ne'
  have h2 : (((k + 1 + b).choose (k + 1) : ℕ) : K) ≠ 0 :=
    mod_cast (Nat.choose_pos (Nat.le_add_right (k + 1) b)).ne'
  have hid : ((k : K) + 1 + b) * ((k + b).choose k : K) =
      ((k + 1 + b).choose (k + 1) : K) * ((k : K) + 1) := by
    exact_mod_cast (Nat.add_right_comm k b 1 ▸ Nat.add_one_mul_choose_eq (k + b) k)
  rw [Nat.add_sub_cancel_right, Nat.cast_sub habu]
  push_cast
  field_simp
  calc
    ((k : K) + 1) * ((k + 1 + b).choose (k + 1) : K) +
        ((k + b).choose k : K) * ((u : K) - ((k : K) + 1 + b))
      = ((k : K) + 1 + b) * ((k + b).choose k : K) +
          ((k + b).choose k : K) * ((u : K) - ((k : K) + 1 + b)) := by
        rw [mul_comm ((k : K) + 1), ← hid]
    _ = ((k + b).choose k : K) * (u : K) := by ring

private theorem sum_inv_choose_le_one_aux {ι α K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (n : ℕ) {U : Finset α} {s : Finset ι} {A B : ι → Finset α}
    (hUn : #U ≤ n)
    (hU : ∀ i ∈ s, A i ⊆ U ∧ B i ⊆ U)
    (hdiag : ∀ i ∈ s, Disjoint (A i) (B i))
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ Disjoint (A i) (B j)) :
    ∑ i ∈ s, ((#(A i) + #(B i)).choose #(A i) : K)⁻¹ ≤ 1 := by
  classical
  rcases Nat.eq_zero_or_pos #s with hs0 | hs_pos
  · simp [Finset.card_eq_zero.mp hs0]
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hs_pos) with hs1 | hs1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hs1.symm
    simpa using inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr (Nat.choose_pos (Nat.le_add_right _ _)))
  cases n with
  | zero =>
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hs1
    have hAi : A i = ∅ := Finset.subset_empty.mp
      (Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hUn) ▸ (hU i hi).1)
    exact absurd (by simp [hAi]) (hoff i hi j hj hij)
  | succ n =>
    have hA_pos (i) (hi : i ∈ s) : 1 ≤ #(A i) := by
      obtain ⟨j, hj, hij⟩ := Finset.exists_mem_ne hs1 i
      exact Finset.card_pos.mpr
        ((Finset.not_disjoint_iff.mp (hoff i hi j hj hij.symm)).imp fun _ h => h.1)
    obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (Nat.zero_lt_one.trans hs1)
    have hU_pos : 0 < #U := (hA_pos i₀ hi₀).trans (Finset.card_le_card (hU i₀ hi₀).1)
    have hU_step (x) (hx : x ∈ U) : ∑ i ∈ s with x ∉ B i,
        ((#((A i).erase x) + #(B i)).choose #((A i).erase x) : K)⁻¹ ≤ 1 := by
      refine sum_inv_choose_le_one_aux n (U := U.erase x)
        (by have := Finset.card_erase_lt_of_mem hx; omega) (fun i hi => ?_) (fun i hi => ?_)
        (fun i hi j hj hij => ?_)
      · rw [Finset.mem_filter] at hi
        exact ⟨Finset.erase_subset_erase x (hU i hi.1).1,
          Finset.subset_erase.mpr ⟨(hU i hi.1).2, hi.2⟩⟩
      · exact (hdiag i (Finset.mem_filter.mp hi).1).mono_left (Finset.erase_subset x _)
      · rw [Finset.mem_filter] at hi hj
        obtain ⟨y, hyA, hyB⟩ := Finset.not_disjoint_iff.mp (hoff i hi.1 j hj.1 hij)
        exact Finset.not_disjoint_iff.mpr
          ⟨y, Finset.mem_erase.mpr ⟨fun h => hj.2 (h ▸ hyB), hyA⟩, hyB⟩
    have hinner (i) (hi : i ∈ s) :
        (∑ x ∈ U, if x ∉ B i then
            ((#((A i).erase x) + #(B i)).choose #((A i).erase x) : K)⁻¹ else 0) =
          (#U : K) * ((#(A i) + #(B i)).choose #(A i) : K)⁻¹ := by
      obtain ⟨hAU, hBU⟩ := hU i hi
      have hBA : B i ⊆ U \ A i := Finset.subset_sdiff.mpr ⟨hBU, (hdiag i hi).symm⟩
      have hs1 : ∑ x ∈ A i,
          (if x ∉ B i then
            ((#((A i).erase x) + #(B i)).choose #((A i).erase x) : K)⁻¹ else 0) =
          (#(A i) : K) * (((#(A i) - 1 + #(B i)).choose (#(A i) - 1) : ℕ) : K)⁻¹ := by
        rw [← nsmul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_congr rfl fun x hx => by
          simp [Finset.disjoint_left.mp (hdiag i hi) hx, Finset.card_erase_of_mem hx]
      have hs2 : ∑ x ∈ B i,
          (if x ∉ B i then
            ((#((A i).erase x) + #(B i)).choose #((A i).erase x) : K)⁻¹ else 0) = 0 :=
        Finset.sum_eq_zero fun x hx => by simp [hx]
      have hs3 : ∑ x ∈ (U \ A i) \ B i,
          (if x ∉ B i then
            ((#((A i).erase x) + #(B i)).choose #((A i).erase x) : K)⁻¹ else 0) =
          ((#U - (#(A i) + #(B i)) : ℕ) : K) *
            (((#(A i) + #(B i)).choose #(A i) : ℕ) : K)⁻¹ := by
        rw [← Nat.sub_sub, ← Finset.card_sdiff_of_subset hAU, ← Finset.card_sdiff_of_subset hBA,
          ← nsmul_eq_mul, ← Finset.sum_const]
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [Finset.mem_sdiff, Finset.mem_sdiff] at hx
        simp [hx.2, Finset.erase_eq_of_notMem hx.1.2]
      rw [← Finset.sum_sdiff hAU, ← Finset.sum_sdiff hBA, hs3, hs2, hs1, add_zero, add_comm]
      exact inv_choose_add_step (hA_pos i hi)
        (Finset.card_union_of_disjoint (hdiag i hi) ▸
          Finset.card_le_card (Finset.union_subset hAU hBU))
    have hsum : ∑ x ∈ U, ∑ i ∈ s with x ∉ B i,
        ((#((A i).erase x) + #(B i)).choose #((A i).erase x) : K)⁻¹ ≤ (#U : K) :=
      calc
        ∑ x ∈ U, ∑ i ∈ s with x ∉ B i,
            ((#((A i).erase x) + #(B i)).choose #((A i).erase x) : K)⁻¹
          ≤ ∑ _x ∈ U, (1 : K) := Finset.sum_le_sum hU_step
        _ = (#U : K) := by simp
    refine (mul_le_iff_le_one_right (Nat.cast_pos.mpr hU_pos)).mp ?_
    calc
      (#U : K) * ∑ i ∈ s, ((#(A i) + #(B i)).choose #(A i) : K)⁻¹
        = ∑ i ∈ s, (#U : K) * ((#(A i) + #(B i)).choose #(A i) : K)⁻¹ := Finset.mul_sum _ _ _
      _ = ∑ i ∈ s, ∑ x ∈ U, if x ∉ B i then
            ((#((A i).erase x) + #(B i)).choose #((A i).erase x) : K)⁻¹ else 0 :=
          Finset.sum_congr rfl fun i hi => (hinner i hi).symm
      _ = ∑ x ∈ U, ∑ i ∈ s with x ∉ B i,
            ((#((A i).erase x) + #(B i)).choose #((A i).erase x) : K)⁻¹ := by
          rw [Finset.sum_comm]
          simp_rw [Finset.sum_filter]
      _ ≤ (#U : K) := hsum

/-- **Bollobás's two-families inequality** [Bollobas1965] (LYM unequal-size form):
if `(A i, B i)` for `i ∈ s` are disjoint pairs of finite sets satisfying `¬ Disjoint (A i) (B j)`
for all `i ≠ j` in `s`, then `∑ i ∈ s, ((#(A i) + #(B i)).choose #(A i) : K)⁻¹ ≤ 1`. -/
theorem Finset.sum_inv_choose_le_one_of_disjoint {ι α K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {s : Finset ι} {A B : ι → Finset α}
    (hdiag : ∀ i ∈ s, Disjoint (A i) (B i))
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ Disjoint (A i) (B j)) :
    ∑ i ∈ s, ((#(A i) + #(B i)).choose #(A i) : K)⁻¹ ≤ 1 := by
  classical
  let U : Finset α := s.biUnion fun i => A i ∪ B i
  exact sum_inv_choose_le_one_aux (#U) le_rfl (fun i hi =>
    ⟨Finset.subset_union_left.trans (Finset.subset_biUnion_of_mem (fun i => A i ∪ B i) hi),
      Finset.subset_union_right.trans (Finset.subset_biUnion_of_mem (fun i => A i ∪ B i) hi)⟩)
    hdiag hoff

/-- **Bollobás's two-families inequality** [Bollobas1965] (bounded-size form):
if `(A i, B i)` for `i ∈ s` satisfy `#(A i) ≤ r`, `#(B i) ≤ t`, `Disjoint (A i) (B i)`, and
`¬ Disjoint (A i) (B j)` for all `i ≠ j` in `s`, then `#s ≤ (r + t).choose r`. -/
theorem Finset.card_le_choose_of_disjoint {ι α : Type*}
    {s : Finset ι} {A B : ι → Finset α} {r t : ℕ}
    (hA : ∀ i ∈ s, #(A i) ≤ r) (hB : ∀ i ∈ s, #(B i) ≤ t)
    (hdiag : ∀ i ∈ s, Disjoint (A i) (B i))
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ Disjoint (A i) (B j)) :
    #s ≤ (r + t).choose r := by
  have hterm (i) (hi : i ∈ s) :
      (((r + t).choose r : ℕ) : ℚ)⁻¹ ≤ ((#(A i) + #(B i)).choose #(A i) : ℚ)⁻¹ := by
    refine inv_anti₀ (Nat.cast_pos.mpr (Nat.choose_pos (Nat.le_add_right _ _))) (mod_cast ?_)
    calc (#(A i) + #(B i)).choose #(A i)
      _ ≤ (r + #(B i)).choose r := by
          rw [Nat.choose_symm_add, Nat.choose_symm_add]
          exact Nat.choose_le_choose #(B i) (Nat.add_le_add_right (hA i hi) _)
      _ ≤ (r + t).choose r := Nat.choose_le_choose r (Nat.add_le_add_left (hB i hi) r)
  have hsum : (#s : ℚ) * (((r + t).choose r : ℕ) : ℚ)⁻¹ ≤ 1 := by
    calc
      (#s : ℚ) * (((r + t).choose r : ℕ) : ℚ)⁻¹
        = ∑ _i ∈ s, (((r + t).choose r : ℕ) : ℚ)⁻¹ := by simp
      _ ≤ ∑ i ∈ s, ((#(A i) + #(B i)).choose #(A i) : ℚ)⁻¹ := Finset.sum_le_sum hterm
      _ ≤ 1 := Finset.sum_inv_choose_le_one_of_disjoint hdiag hoff
  exact_mod_cast (show (#s : ℚ) ≤ (r + t).choose r by
    simpa using (mul_inv_le_iff₀ (Nat.cast_pos.mpr (Nat.choose_pos (Nat.le_add_right r t)))).mp
      hsum)

end Symmetric

section Skew

private noncomputable def padWith {α : Type*} (tag : ℕ → ℕ ⊕ ℕ) (htag : Function.Injective tag)
    (m : ℕ) (S : Finset α) : Finset (α ⊕ ℕ ⊕ ℕ) :=
  open Classical in
  S.map ⟨@Sum.inl α (ℕ ⊕ ℕ), Sum.inl_injective⟩ ∪
    (Finset.range (m - #S)).map ⟨fun k => Sum.inr (tag k), Sum.inr_injective.comp htag⟩

private theorem card_padWith {α : Type*} {tag : ℕ → ℕ ⊕ ℕ} {htag : Function.Injective tag}
    {m : ℕ} {S : Finset α} (hS : #S ≤ m) :
    #(padWith tag htag m S) = m := by
  classical
  rw [padWith, Finset.card_union_of_disjoint (Finset.disjoint_left.mpr fun _ hx1 hx2 => by
      rcases Finset.mem_map.mp hx1 with ⟨_, _, rfl⟩
      rcases Finset.mem_map.mp hx2 with ⟨_, _, ⟨⟩⟩),
    Finset.card_map, Finset.card_map, Finset.card_range, Nat.add_sub_cancel' hS]

private theorem disjoint_padWith_iff {α : Type*} {r s : ℕ} {S T : Finset α} :
    Disjoint (padWith Sum.inl Sum.inl_injective r S)
        (padWith Sum.inr Sum.inr_injective s T) ↔
      Disjoint S T := by
  classical
  simp only [padWith, Finset.disjoint_left, Finset.mem_union, Finset.mem_map]
  refine ⟨fun h x hxS hxT => h (.inl ⟨x, hxS, rfl⟩) (.inl ⟨x, hxT, rfl⟩), ?_⟩
  rintro h _ (⟨a, ha, rfl⟩ | ⟨_, _, rfl⟩) (⟨b, hb, hab⟩ | ⟨_, _, hab⟩)
  · exact h ha (Sum.inl_injective hab ▸ hb)
  all_goals cases hab

private noncomputable def enumFinset {β : Type*} (S : Finset β) {k : ℕ} (hS : #S = k) :
    Fin k → β := fun i =>
  open Classical in
  (S.equivFin.symm (i.cast hS.symm)).1

private theorem enumFinset_injective {β : Type*} {S : Finset β} {k : ℕ} (hS : #S = k) :
    Function.Injective (enumFinset S hS) := fun i j h => by
  classical
  exact Fin.ext <| by simpa using congrArg Fin.val (S.equivFin.symm.injective (Subtype.ext h))

private theorem enumFinset_mem {β : Type*} {S : Finset β} {k : ℕ} (hS : #S = k) (i : Fin k) :
    enumFinset S hS i ∈ S := by
  classical
  exact (S.equivFin.symm (i.cast hS.symm)).2

private theorem range_enumFinset {β : Type*} {S : Finset β} {k : ℕ} (hS : #S = k) :
    Set.range (enumFinset S hS) = (S : Set β) := by
  classical
  ext x
  exact ⟨fun ⟨i, h⟩ => h ▸ enumFinset_mem hS i,
    fun hx => ⟨(S.equivFin ⟨x, hx⟩).cast hS, by simp [enumFinset]⟩⟩

private theorem fin_append_injective {α : Type*} {r s : ℕ}
    {f : Fin r → α} {g : Fin s → α} (hf : Function.Injective f) (hg : Function.Injective g)
    (hdisj : Disjoint (Set.range f) (Set.range g)) :
    Function.Injective (Fin.append f g) := by
  rw [Set.disjoint_iff] at hdisj
  intro a b hab
  refine Fin.addCases (fun p => Fin.addCases (fun p' hp => ?_) (fun q' hq => ?_) b)
    (fun q => Fin.addCases (fun p' hp => ?_) (fun q' hq => ?_) b) a hab
  · exact congrArg (Fin.castAdd s) (hf (by simpa using hp))
  · exact False.elim (hdisj ⟨⟨p, rfl⟩, ⟨q', by simpa using hq.symm⟩⟩)
  · exact False.elim (hdisj ⟨⟨p', rfl⟩, ⟨q, by simpa using hp⟩⟩)
  · exact congrArg (Fin.natAdd r) (hg (by simpa using hq))

/-- **Frankl's skew Bollobás theorem** [Frankl1982] (see also [Jukna2011, Section 8.4]):
if `ι` is a linearly ordered finite type and `(A i, B i)` satisfy `#(A i) ≤ r`, `#(B i) ≤ s`,
`Disjoint (A i) (B i)` for all `i`, and the one-sided condition `i < j → ¬ Disjoint (A i) (B j)`,
then `Fintype.card ι ≤ (r + s).choose r`. -/
theorem Fintype.card_le_choose_of_lt_not_disjoint {ι α : Type*}
    [Fintype ι] [LinearOrder ι] (A B : ι → Finset α) {r s : ℕ}
    (hA : ∀ i, #(A i) ≤ r) (hB : ∀ i, #(B i) ≤ s)
    (hdiag : ∀ i, Disjoint (A i) (B i))
    (hskew : ∀ ⦃i j : ι⦄, i < j → ¬ Disjoint (A i) (B j)) :
    Fintype.card ι ≤ (r + s).choose r := by
  classical
  let β := α ⊕ ℕ ⊕ ℕ
  let pA : ι → Finset β := fun i => padWith Sum.inl Sum.inl_injective r (A i)
  let pB : ι → Finset β := fun i => padWith Sum.inr Sum.inr_injective s (B i)
  have hpA_card : ∀ i, #(pA i) = r := fun i => card_padWith (hA i)
  have hpB_card : ∀ i, #(pB i) = s := fun i => card_padWith (hB i)
  let U : Finset β := Finset.univ.biUnion fun i => pA i ∪ pB i
  let coord : β → ℚ := fun x =>
    if hx : x ∈ U then ((U.equivFin ⟨x, hx⟩ : Fin #U).val : ℚ) else 0
  have hcoord_inj : ∀ {x y : β}, x ∈ U → y ∈ U → coord x = coord y → x = y := fun hx hy hxy => by
    simp only [coord, hx, hy, ↓reduceDIte, Nat.cast_inj] at hxy
    exact congrArg Subtype.val (U.equivFin.injective (Fin.ext hxy))
  let M := Fin (r + s) → ℚ
  let v : β → M := fun x k => (coord x) ^ (k : ℕ)
  let enumA : ι → Fin r → β := fun i => enumFinset (pA i) (hpA_card i)
  let enumB : ι → Fin s → β := fun j => enumFinset (pB j) (hpB_card j)
  let detForm : ExteriorAlgebra ℚ M →ₗ[ℚ] ℚ :=
    ExteriorAlgebra.liftAlternating fun k =>
      if hk : k = r + s then
        (Matrix.detRowAlternating (R := ℚ) (n := Fin (r + s))).domDomCongr (finCongr hk.symm)
      else 0
  let a : ι → ExteriorAlgebra ℚ M := fun i => ExteriorAlgebra.ιMulti ℚ r (v ∘ enumA i)
  let b : ι → ⋀[ℚ]^s M := fun j => exteriorPower.ιMulti ℚ s (v ∘ enumB j)
  let Φ : ι → (⋀[ℚ]^s M) →ₗ[ℚ] ℚ := fun i =>
    detForm.comp ((LinearMap.mulLeft ℚ (a i)).comp (⋀[ℚ]^s M).subtype)
  have hΦ_eval : ∀ i j,
      Φ i (b j) = (Matrix.vandermonde (coord ∘ Fin.append (enumA i) (enumB j))).det := by
    intro i j
    simp only [Φ, detForm, LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.mulLeft_apply,
      b, exteriorPower.ιMulti_apply_coe, a, ExteriorAlgebra.ιMulti_mul_ιMulti,
      ExteriorAlgebra.liftAlternating_apply_ιMulti, dite_true, AlternatingMap.domDomCongr_apply]
    have hrow : Fin.append (v ∘ enumA i) (v ∘ enumB j) ∘ ⇑(finCongr (rfl : r + s = r + s)) =
        v ∘ Fin.append (enumA i) (enumB j) :=
      funext fun x => Fin.addCases (fun _ => by simp [finCongr]) (fun _ => by simp [finCongr]) x
    rw [hrow]; rfl
  have hAppend_memU (i j k) : Fin.append (enumA i) (enumB j) k ∈ U :=
    Fin.addCases
      (fun p => by simpa [U, Fin.append_left] using ⟨i, Or.inl (enumFinset_mem (hpA_card i) p)⟩)
      (fun q => by simpa [U, Fin.append_right] using ⟨j, Or.inr (enumFinset_mem (hpB_card j) q)⟩) k
  have hΦ_diag : ∀ i, Φ i (b i) ≠ 0 := fun i => by
    rw [hΦ_eval, Matrix.det_vandermonde_ne_zero_iff]
    have hinj := fin_append_injective (enumFinset_injective (hpA_card i))
      (enumFinset_injective (hpB_card i)) (by
        rw [range_enumFinset, range_enumFinset, Finset.disjoint_coe]
        exact disjoint_padWith_iff.mpr (hdiag i))
    exact fun k₁ k₂ hk => hinj (hcoord_inj (hAppend_memU i i k₁) (hAppend_memU i i k₂) hk)
  have hΦ_upper : ∀ {i j : ι}, i < j → Φ i (b j) = 0 := fun {i j} hij => by
    rw [hΦ_eval, Matrix.det_vandermonde_eq_zero_iff]
    obtain ⟨x, hxA, hxB⟩ :=
      Finset.not_disjoint_iff.mp (disjoint_padWith_iff.not.mpr (hskew hij))
    obtain ⟨p, hp⟩ : x ∈ Set.range (enumA i) :=
      (range_enumFinset (hpA_card i)).symm ▸ (hxA : x ∈ pA i)
    obtain ⟨q, hq⟩ : x ∈ Set.range (enumB j) :=
      (range_enumFinset (hpB_card j)).symm ▸ (hxB : x ∈ pB j)
    exact ⟨Fin.castAdd s p, Fin.natAdd r q, by simp [Fin.append_left, Fin.append_right, hp, hq],
      fun h => by rw [Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at h; omega⟩
  have hlin : LinearIndependent ℚ b := Fintype.linearIndependent_iff.mpr fun c hc i => by
    by_contra hci
    let S : Finset ι := Finset.univ.filter fun j => c j ≠ 0
    have hS_ne : S.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hci⟩⟩
    let i₀ : ι := S.min' hS_ne
    have hzero : ∑ j : ι, c j * Φ i₀ (b j) = 0 := by
      simpa [map_sum, smul_eq_mul] using congrArg (Φ i₀) hc
    rw [Finset.sum_eq_single i₀ (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ _) h)] at hzero
    · exact (mul_eq_zero.mp hzero).elim
        (Finset.mem_filter.mp (Finset.min'_mem S hS_ne)).2 (hΦ_diag i₀)
    · rcases lt_trichotomy j i₀ with hlt | rfl | hgt
      · have hcj : c j = 0 := by_contra fun hcj => not_lt_of_ge
          (Finset.min'_le S j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcj⟩)) hlt
        simp [hcj]
      · exact absurd rfl hj
      · simp [hΦ_upper hgt]
  calc
    Fintype.card ι
      ≤ Module.finrank ℚ (⋀[ℚ]^s M) := hlin.fintype_card_le_finrank
    _ = (Module.finrank ℚ M).choose s := exteriorPower.finrank_eq ℚ M (n := s)
    _ = (r + s).choose s := by simp [M]
    _ = (r + s).choose r := Nat.choose_symm_add.symm

end Skew

end
