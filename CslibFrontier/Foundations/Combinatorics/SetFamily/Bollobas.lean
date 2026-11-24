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
  have hk_add : (k + 1 - 1 + b).choose (k + 1 - 1) = (k + b).choose k := by simp
  have hchoose_pos1 : ((k + b).choose k : K) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_right k b)).ne'
  have hchoose_pos2 : (((k + 1 + b).choose (k + 1) : ℕ) : K) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_right (k + 1) b)).ne'
  have hchoose_id :
      (k + 1 + b) * (k + b).choose k = (k + 1 + b).choose (k + 1) * (k + 1) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Nat.add_one_mul_choose_eq (k + b) k
  rw [hk_add, Nat.cast_sub habu]
  push_cast
  have hchoose_idK :
      ((k : K) + 1 + b) * ((k + b).choose k : K) =
        ((k + 1 + b).choose (k + 1) : K) * ((k : K) + 1) := by
    exact_mod_cast hchoose_id
  field_simp
  calc
    ((k : K) + 1) * ((k + 1 + b).choose (k + 1) : K) +
        ((k + b).choose k : K) * ((u : K) - ((k : K) + 1 + b))
      = ((k + 1 + b).choose (k + 1) : K) * ((k : K) + 1) +
          ((k + b).choose k : K) * ((u : K) - ((k : K) + 1 + b)) := by ring
    _ = ((k : K) + 1 + b) * ((k + b).choose k : K) +
          ((k + b).choose k : K) * ((u : K) - ((k : K) + 1 + b)) := by rw [← hchoose_idK]
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
  · rw [Finset.card_eq_zero.mp hs0]
    simp
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hs_pos) with hs1 | hs1
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hs1.symm
      have hpos : 0 < (#(A i) + #(B i)).choose #(A i) :=
        Nat.choose_pos (Nat.le_add_right _ _)
      simpa using inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr hpos)
    · cases n with
      | zero =>
        have hU_empty : U = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hUn)
        subst hU_empty
        obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hs1
        have hAi : A i = ∅ := Finset.subset_empty.mp (hU i hi).1
        exact absurd (by simp [hAi]) (hoff i hi j hj hij)
      | succ n =>
        have hA_pos : ∀ i ∈ s, 1 ≤ #(A i) := by
          intro i hi
          obtain ⟨j, hj, hij⟩ := Finset.exists_mem_ne hs1 i
          obtain ⟨x, hx, _⟩ := Finset.not_disjoint_iff.mp (hoff i hi j hj hij.symm)
          exact Finset.card_pos.mpr ⟨x, hx⟩
        obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (lt_trans Nat.zero_lt_one hs1)
        have hU_pos : 0 < #U := lt_of_lt_of_le (hA_pos i₀ hi₀) (Finset.card_le_card (hU i₀ hi₀).1)
        have hU_step :
            ∀ x ∈ U,
              ∑ i ∈ s with x ∉ B i,
                  ((#((A i).erase x) + #(B i)).choose #((A i).erase x) : K)⁻¹ ≤ 1 := by
          intro x hx
          refine sum_inv_choose_le_one_aux n
            (U := U.erase x) (s := s.filter (fun i => x ∉ B i))
            (A := fun i => (A i).erase x) (B := B)
            ?_ ?_ ?_ ?_
          · have := Finset.card_erase_lt_of_mem hx
            omega
          · intro i hi
            rw [Finset.mem_filter] at hi
            exact ⟨Finset.erase_subset_erase x (hU i hi.1).1,
              Finset.subset_erase.mpr ⟨(hU i hi.1).2, hi.2⟩⟩
          · intro i hi
            rw [Finset.mem_filter] at hi
            exact (hdiag i hi.1).mono_left (Finset.erase_subset x _)
          · intro i hi j hj hij
            rw [Finset.mem_filter] at hi hj
            obtain ⟨y, hyA, hyB⟩ := Finset.not_disjoint_iff.mp (hoff i hi.1 j hj.1 hij)
            refine Finset.not_disjoint_iff.mpr ⟨y, Finset.mem_erase.mpr ⟨?_, hyA⟩, hyB⟩
            rintro rfl
            exact hj.2 hyB
        have hsum :
            ∑ x ∈ U, ∑ i ∈ s with x ∉ B i,
                ((#((A i).erase x) + #(B i)).choose #((A i).erase x) : K)⁻¹ ≤ (#U : K) := by
          calc
            ∑ x ∈ U, ∑ i ∈ s with x ∉ B i,
                ((#((A i).erase x) + #(B i)).choose #((A i).erase x) : K)⁻¹
              ≤ ∑ _x ∈ U, (1 : K) := Finset.sum_le_sum hU_step
            _ = (#U : K) := by simp
        have hinner :
            ∀ i ∈ s,
              (∑ x ∈ U, if x ∉ B i then
                  ((#((A i).erase x) + #(B i)).choose #((A i).erase x) : K)⁻¹ else 0) =
                (#U : K) * ((#(A i) + #(B i)).choose #(A i) : K)⁻¹ := by
          intro i hi
          have hAU : A i ⊆ U := (hU i hi).1
          have hBU : B i ⊆ U := (hU i hi).2
          have hBA : B i ⊆ U \ A i := Finset.subset_sdiff.mpr ⟨hBU, (hdiag i hi).symm⟩
          rw [← Finset.sum_sdiff hAU, ← Finset.sum_sdiff hBA]
          have hs1_term :
              ∑ x ∈ A i,
                  (if x ∉ B i then
                      ((#((A i).erase x) + #(B i)).choose #((A i).erase x) : K)⁻¹ else 0) =
                (#(A i) : K) * (((#(A i) - 1 + #(B i)).choose (#(A i) - 1) : ℕ) : K)⁻¹ := by
            rw [← nsmul_eq_mul, ← Finset.sum_const]
            refine Finset.sum_congr rfl fun x hx => ?_
            have hxB : x ∉ B i := Finset.disjoint_left.mp (hdiag i hi) hx
            simp [hxB, Finset.card_erase_of_mem hx]
          have hs2_term :
              ∑ x ∈ B i,
                  (if x ∉ B i then
                      ((#((A i).erase x) + #(B i)).choose #((A i).erase x) : K)⁻¹ else 0) = 0 :=
            Finset.sum_eq_zero fun x hx => by simp [hx]
          have hs3_term :
              ∑ x ∈ (U \ A i) \ B i,
                  (if x ∉ B i then
                      ((#((A i).erase x) + #(B i)).choose #((A i).erase x) : K)⁻¹ else 0) =
                ((#U - (#(A i) + #(B i)) : ℕ) : K) *
                  (((#(A i) + #(B i)).choose #(A i) : ℕ) : K)⁻¹ := by
            have hcard : #((U \ A i) \ B i) = #U - (#(A i) + #(B i)) := by
              rw [Finset.card_sdiff_of_subset hBA, Finset.card_sdiff_of_subset hAU, Nat.sub_sub]
            rw [← hcard, ← nsmul_eq_mul, ← Finset.sum_const]
            refine Finset.sum_congr rfl fun x hx => ?_
            rw [Finset.mem_sdiff, Finset.mem_sdiff] at hx
            simp [hx.2, Finset.erase_eq_of_notMem hx.1.2]
          have habu : #(A i) + #(B i) ≤ #U := by
            have hdisj := hdiag i hi
            rw [← Finset.card_union_of_disjoint hdisj]
            exact Finset.card_le_card (Finset.union_subset hAU hBU)
          rw [hs3_term, hs2_term, hs1_term, add_zero, add_comm]
          exact inv_choose_add_step (hA_pos i hi) habu
        have hswap :
            (#U : K) * ∑ i ∈ s, ((#(A i) + #(B i)).choose #(A i) : K)⁻¹ ≤ (#U : K) := by
          calc
            (#U : K) * ∑ i ∈ s, ((#(A i) + #(B i)).choose #(A i) : K)⁻¹
              = ∑ i ∈ s, (#U : K) * ((#(A i) + #(B i)).choose #(A i) : K)⁻¹ := by
                rw [Finset.mul_sum]
            _ = ∑ i ∈ s, ∑ x ∈ U, if x ∉ B i then
                  ((#((A i).erase x) + #(B i)).choose #((A i).erase x) : K)⁻¹ else 0 :=
                Finset.sum_congr rfl fun i hi => (hinner i hi).symm
            _ = ∑ x ∈ U, ∑ i ∈ s with x ∉ B i,
                  ((#((A i).erase x) + #(B i)).choose #((A i).erase x) : K)⁻¹ := by
                rw [Finset.sum_comm]
                simp_rw [Finset.sum_filter]
            _ ≤ (#U : K) := hsum
        have hU_Kpos : (0 : K) < (#U : K) := Nat.cast_pos.mpr hU_pos
        exact (mul_le_iff_le_one_right hU_Kpos).mp hswap

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
  refine sum_inv_choose_le_one_aux (#U) (U := U) (s := s) (A := A) (B := B) le_rfl ?_ hdiag hoff
  intro i hi
  exact ⟨Finset.subset_union_left.trans (Finset.subset_biUnion_of_mem (fun i => A i ∪ B i) hi),
    Finset.subset_union_right.trans (Finset.subset_biUnion_of_mem (fun i => A i ∪ B i) hi)⟩

/-- **Bollobás's two-families inequality** [Bollobas1965] (bounded-size form):
if `(A i, B i)` for `i ∈ s` satisfy `#(A i) ≤ r`, `#(B i) ≤ t`, `Disjoint (A i) (B i)`, and
`¬ Disjoint (A i) (B j)` for all `i ≠ j` in `s`, then `#s ≤ (r + t).choose r`. -/
theorem Finset.card_le_choose_of_disjoint {ι α : Type*}
    {s : Finset ι} {A B : ι → Finset α} {r t : ℕ}
    (hA : ∀ i ∈ s, #(A i) ≤ r) (hB : ∀ i ∈ s, #(B i) ≤ t)
    (hdiag : ∀ i ∈ s, Disjoint (A i) (B i))
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ Disjoint (A i) (B j)) :
    #s ≤ (r + t).choose r := by
  have hlym :
      ∑ i ∈ s, ((#(A i) + #(B i)).choose #(A i) : ℚ)⁻¹ ≤ 1 :=
    Finset.sum_inv_choose_le_one_of_disjoint hdiag hoff
  have hterm :
      ∀ i ∈ s, (((r + t).choose r : ℕ) : ℚ)⁻¹ ≤
        ((#(A i) + #(B i)).choose #(A i) : ℚ)⁻¹ := by
    intro i hi
    have hchoose_pos : (0 : ℚ) < ((#(A i) + #(B i)).choose #(A i) : ℚ) :=
      Nat.cast_pos.mpr (Nat.choose_pos (Nat.le_add_right _ _))
    refine inv_anti₀ hchoose_pos ?_
    exact_mod_cast calc
      (#(A i) + #(B i)).choose #(A i)
        ≤ (r + #(B i)).choose r := by
          rw [Nat.choose_symm_add, Nat.choose_symm_add]
          exact Nat.choose_le_choose #(B i) (Nat.add_le_add_right (hA i hi) _)
      _ ≤ (r + t).choose r := Nat.choose_le_choose r (Nat.add_le_add_left (hB i hi) r)
  have hsum : (#s : ℚ) * (((r + t).choose r : ℕ) : ℚ)⁻¹ ≤ 1 := by
    calc
      (#s : ℚ) * (((r + t).choose r : ℕ) : ℚ)⁻¹
        = ∑ _i ∈ s, (((r + t).choose r : ℕ) : ℚ)⁻¹ := by simp
      _ ≤ ∑ i ∈ s, ((#(A i) + #(B i)).choose #(A i) : ℚ)⁻¹ := Finset.sum_le_sum hterm
      _ ≤ 1 := hlym
  have hrt_pos : (0 : ℚ) < (((r + t).choose r : ℕ) : ℚ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (Nat.le_add_right r t))
  have hcast : (#s : ℚ) ≤ ((r + t).choose r : ℚ) := by
    simpa using (mul_inv_le_iff₀ hrt_pos).mp hsum
  exact_mod_cast hcast

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
  have hdisj :
      Disjoint (S.map ⟨@Sum.inl α (ℕ ⊕ ℕ), Sum.inl_injective⟩)
        ((Finset.range (m - #S)).map ⟨fun k => Sum.inr (tag k),
          Sum.inr_injective.comp htag⟩) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_map] at hx1 hx2
    rcases hx1 with ⟨_, _, rfl⟩
    rcases hx2 with ⟨_, _, h⟩
    cases h
  rw [padWith, Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map,
    Finset.card_range, Nat.add_sub_cancel' hS]

private theorem disjoint_padWith_iff {α : Type*} {r s : ℕ} {S T : Finset α} :
    Disjoint (padWith Sum.inl Sum.inl_injective r S)
        (padWith Sum.inr Sum.inr_injective s T) ↔
      Disjoint S T := by
  classical
  rw [Finset.disjoint_left, Finset.disjoint_left]
  constructor
  · intro h x hxS hxT
    exact h (Finset.mem_union_left _ (Finset.mem_map.mpr ⟨x, hxS, rfl⟩))
      (Finset.mem_union_left _ (Finset.mem_map.mpr ⟨x, hxT, rfl⟩))
  · intro h x hx1 hx2
    rw [padWith, Finset.mem_union, Finset.mem_map, Finset.mem_map] at hx1 hx2
    rcases hx1 with ⟨a, ha, rfl⟩ | ⟨k, _, rfl⟩
    · rcases hx2 with ⟨b, hb, hab⟩ | ⟨k, _, hab⟩
      · exact h ha (Sum.inl_injective hab ▸ hb)
      · cases hab
    · rcases hx2 with ⟨b, _, hba⟩ | ⟨l, _, hkl⟩
      · cases hba
      · cases hkl

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
  simp only [Set.mem_range, Finset.mem_coe]
  constructor
  · rintro ⟨i, rfl⟩
    exact enumFinset_mem hS i
  · intro hx
    refine ⟨(S.equivFin ⟨x, hx⟩).cast hS, ?_⟩
    simp [enumFinset]

private theorem fin_append_injective {α : Type*} {r s : ℕ}
    {f : Fin r → α} {g : Fin s → α} (hf : Function.Injective f) (hg : Function.Injective g)
    (hdisj : Disjoint (Set.range f) (Set.range g)) :
    Function.Injective (Fin.append f g) := by
  rw [Set.disjoint_iff] at hdisj
  intro a b hab
  refine Fin.addCases (fun p => Fin.addCases (fun p' hp => ?_) (fun q' hq => ?_) b)
    (fun q => Fin.addCases (fun p' hp => ?_) (fun q' hq => ?_) b) a hab
  · simp only [Fin.append_left] at hp
    exact congrArg (Fin.castAdd s) (hf hp)
  · simp only [Fin.append_left, Fin.append_right] at hq
    exact False.elim (hdisj ⟨⟨p, rfl⟩, ⟨q', hq.symm⟩⟩)
  · simp only [Fin.append_left, Fin.append_right] at hp
    exact False.elim (hdisj ⟨⟨p', rfl⟩, ⟨q, hp⟩⟩)
  · simp only [Fin.append_right] at hq
    exact congrArg (Fin.natAdd r) (hg hq)

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
  have hcoord_inj : ∀ {x y : β}, x ∈ U → y ∈ U → coord x = coord y → x = y := by
    intro x y hx hy hxy
    simp only [coord, hx, hy, ↓reduceDIte] at hxy
    have hfin : U.equivFin ⟨x, hx⟩ = U.equivFin ⟨y, hy⟩ := Fin.ext (Nat.cast_inj.mp hxy)
    exact congrArg Subtype.val ((U.equivFin).injective hfin)
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
    have hrow :
        Fin.append (v ∘ enumA i) (v ∘ enumB j) ∘ ⇑(finCongr (rfl : r + s = r + s)) =
          v ∘ Fin.append (enumA i) (enumB j) := by
      ext x
      have hx : (finCongr (rfl : r + s = r + s)) x = x := Fin.ext rfl
      rw [Function.comp_apply, Function.comp_apply, hx]
      refine Fin.addCases (fun q => ?_) (fun q => ?_) x
      · rw [Fin.append_left, Function.comp_apply, Fin.append_left]
      · rw [Fin.append_right, Function.comp_apply, Fin.append_right]
    rw [hrow]
    rfl
  have hAppend_memU : ∀ i j k, Fin.append (enumA i) (enumB j) k ∈ U := by
    intro i j k
    refine Fin.addCases (fun p => ?_) (fun q => ?_) k
    · rw [Fin.append_left]
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
        Finset.mem_union_left _ (enumFinset_mem (hpA_card i) p)⟩
    · rw [Fin.append_right]
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
        Finset.mem_union_right _ (enumFinset_mem (hpB_card j) q)⟩
  have hΦ_diag : ∀ i, Φ i (b i) ≠ 0 := by
    intro i
    rw [hΦ_eval, Matrix.det_vandermonde_ne_zero_iff]
    have hdisj : Disjoint (Set.range (enumA i)) (Set.range (enumB i)) := by
      rw [range_enumFinset, range_enumFinset, Finset.disjoint_coe]
      exact disjoint_padWith_iff.mpr (hdiag i)
    have hinj := fin_append_injective (enumFinset_injective (hpA_card i))
      (enumFinset_injective (hpB_card i)) hdisj
    intro k₁ k₂ hk
    exact hinj (hcoord_inj (hAppend_memU i i k₁) (hAppend_memU i i k₂) hk)
  have hΦ_upper : ∀ {i j : ι}, i < j → Φ i (b j) = 0 := by
    intro i j hij
    rw [hΦ_eval, Matrix.det_vandermonde_eq_zero_iff]
    obtain ⟨x, hxA, hxB⟩ :=
      Finset.not_disjoint_iff.mp (disjoint_padWith_iff.not.mpr (hskew hij))
    have ⟨p, hp⟩ : x ∈ Set.range (enumA i) := (range_enumFinset (hpA_card i)).symm ▸ hxA
    have ⟨q, hq⟩ : x ∈ Set.range (enumB j) := (range_enumFinset (hpB_card j)).symm ▸ hxB
    refine ⟨Fin.castAdd s p, Fin.natAdd r q, ?_, ?_⟩
    · simp only [Function.comp_apply, Fin.append_left, Fin.append_right, enumA, enumB, hp, hq]
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
  have hlin : LinearIndependent ℚ b := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    by_contra hci
    let S : Finset ι := Finset.univ.filter fun j => c j ≠ 0
    have hS_ne : S.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hci⟩⟩
    let i₀ : ι := S.min' hS_ne
    have hi₀_mem : i₀ ∈ S := Finset.min'_mem S hS_ne
    have hzero : Φ i₀ (∑ j : ι, c j • b j) = 0 := by rw [hc, map_zero]
    rw [map_sum] at hzero
    simp_rw [map_smul, smul_eq_mul] at hzero
    have hsum_single : ∑ j : ι, c j * Φ i₀ (b j) = c i₀ * Φ i₀ (b i₀) := by
      refine Finset.sum_eq_single i₀ (fun j _ hj => ?_) (fun hi₀_univ => ?_)
      · rcases lt_trichotomy j i₀ with hlt | rfl | hgt
        · have hjS : j ∉ S := fun h => not_lt_of_ge (Finset.min'_le S j h) hlt
          have hcj : c j = 0 := by
            simpa [S, Finset.mem_filter] using hjS
          simp [hcj]
        · exact absurd rfl hj
        · simp [hΦ_upper hgt]
      · exact absurd (Finset.mem_univ _) hi₀_univ
    rw [hsum_single] at hzero
    rcases mul_eq_zero.mp hzero with hci₀ | hdiag₀
    · exact (Finset.mem_filter.mp hi₀_mem).2 hci₀
    · exact hΦ_diag i₀ hdiag₀
  calc
    Fintype.card ι
      ≤ Module.finrank ℚ (⋀[ℚ]^s M) := hlin.fintype_card_le_finrank
    _ = (Module.finrank ℚ M).choose s := exteriorPower.finrank_eq ℚ M (n := s)
    _ = (r + s).choose s := by simp [M]
    _ = (r + s).choose r := Nat.choose_symm_add.symm

end Skew

end
