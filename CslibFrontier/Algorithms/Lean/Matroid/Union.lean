/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Combinatorics.Matroid.Rank.ENat
public import Mathlib.Data.Finset.Card
import CslibFrontier.Algorithms.Lean.Matroid.Intersection
import CslibFrontier.Algorithms.Lean.Matroid.Intersection.Konig
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Combinatorics.Matroid.Sum

/-!
# Edmonds' matroid union, partitioning, and base-packing theorems

Given a finite family of matroids `M : ι → Matroid α`, a set `I : Set α` is **union-independent**
(`Cslib.Algorithms.Lean.Matroid.IsUnionIndep`) when `I = ⋃ i, f i` for sets `f i` independent in
`M i`. On finite subsets (and everywhere when the ground sets `(M i).E` are finite), this
predicate forms the finitary matroid `Cslib.Algorithms.Lean.Matroid.matroidUnion M`.

The proofs reduce matroid union to Edmonds' matroid intersection theorem
(`CslibFrontier.Algorithms.Lean.Matroid.Intersection`) between the disjoint sum `Matroid.sum' M`
and the unit-capacity partition matroid `unitPartitionMatroid Prod.snd` on `ι × α`:

* **Finite augmentation** (`IsUnionIndep.exists_insert`) follows from shortest augmenting walks in
  the exchange digraph of `(Matroid.sum' M, unitPartitionMatroid Prod.snd)`, where every `M₂`-arc
  preserving injectivity on non-sink vertices keeps the second projection fixed.
* **Edmonds' matroid union min–max theorem** (`exists_isUnionIndep_card_eq`,
  `matroidUnion_eRk_eq_iInf`, `iSup_encard_isUnionIndep_eq_iInf`) follows from
  `exists_commonIndep_card_eq_eRk_add_eRk` by projecting any separator `U ⊆ Finset.univ ×ˢ S`
  down to `T := {x ∈ S | ∀ i, (i, x) ∈ U}`.
* **Edmonds–Fulkerson matroid partitioning theorem** (`exists_partition_indep_iff`,
  `exists_partition_indep_const_iff`) and **Edmonds' disjoint bases theorem**
  (`exists_disjoint_isBase_iff`) follow directly.

## Main definitions

* `Cslib.Algorithms.Lean.Matroid.IsUnionIndep`: union-independent sets `⋃ i, f i` with
  `(M i).Indep (f i)`.
* `Cslib.Algorithms.Lean.Matroid.matroidUnion`: the finitary matroid union on `⋃ i, (M i).E`.

## Main results

* `Cslib.Algorithms.Lean.Matroid.IsUnionIndep.encard_le_encard_sdiff_add_sum_eRk`: weak duality
  for matroid union.
* `Cslib.Algorithms.Lean.Matroid.exists_isUnionIndep_card_eq`,
  `Cslib.Algorithms.Lean.Matroid.matroidUnion_eRk_eq_iInf`,
  `Cslib.Algorithms.Lean.Matroid.iSup_encard_isUnionIndep_eq_iInf`: **Edmonds' matroid union
  min–max theorem** in witness, rank, and `ℕ∞` supremum/infimum forms.
* `Cslib.Algorithms.Lean.Matroid.exists_partition_indep_iff`,
  `Cslib.Algorithms.Lean.Matroid.exists_partition_indep_const_iff`: **Edmonds–Fulkerson matroid
  partitioning theorem**.
* `Cslib.Algorithms.Lean.Matroid.exists_disjoint_isBase_iff`: **Edmonds' base-packing theorem**
  characterizing when a finite matroid has `k` pairwise disjoint bases.

## References

* [A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*][Schrijver2003] (matroid
  union, partitioning, and base packing; exact chapter and page locator not verified against a
  primary PDF).
* [A. Schrijver, *A Course in Combinatorial Optimization*][Schrijver2017] (exact section, theorem
  number, and page locator not verified against a primary PDF).
-/

public section

namespace Cslib.Algorithms.Lean.Matroid

open Set Finset
open scoped symmDiff

section UnionIndep

variable {ι α : Type*}

/-- `I : Set α` is union-independent for `M : ι → Matroid α` when it equals `⋃ i, f i` for
subsets `f i` independent in `M i`. -/
@[expose] def IsUnionIndep (M : ι → Matroid α) (I : Set α) : Prop :=
  ∃ f : ι → Set α, (∀ i, (M i).Indep (f i)) ∧ I = ⋃ i, f i

/-- The empty set is union-independent for any family of matroids. -/
@[simp] theorem isUnionIndep_empty (M : ι → Matroid α) : IsUnionIndep M ∅ :=
  ⟨fun _ => ∅, fun i => (M i).empty_indep, by simp⟩

/-- Union-independence is downward closed under inclusion. -/
theorem IsUnionIndep.subset {M : ι → Matroid α} {I J : Set α}
    (hJ : IsUnionIndep M J) (hIJ : I ⊆ J) : IsUnionIndep M I := by
  obtain ⟨f, hf, rfl⟩ := hJ
  refine ⟨fun i => I ∩ f i, fun i => (hf i).subset Set.inter_subset_right, ?_⟩
  rw [← Set.inter_iUnion, Set.inter_eq_self_of_subset_left hIJ]

/-- Every union-independent set lies inside the union of the ground sets `(M i).E`. -/
theorem IsUnionIndep.subset_ground {M : ι → Matroid α} {I : Set α}
    (hI : IsUnionIndep M I) : I ⊆ ⋃ i, (M i).E := by
  obtain ⟨f, hf, rfl⟩ := hI
  exact Set.iUnion_mono fun i => (hf i).subset_ground

/-- **Weak duality for matroid union**: any union-independent subset `I ⊆ X` satisfies
`I.encard ≤ (X \ T).encard + ∑ i, (M i).eRk T` for every `T : Set α`. -/
theorem IsUnionIndep.encard_le_encard_sdiff_add_sum_eRk [Fintype ι] {M : ι → Matroid α}
    {X I : Set α} (hI : IsUnionIndep M I) (hIX : I ⊆ X) (T : Set α) :
    I.encard ≤ (X \ T).encard + ∑ i : ι, (M i).eRk T := by
  classical
  obtain ⟨f, hf, rfl⟩ := hI
  have hsplit : (⋃ i, f i) = ((⋃ i, f i) \ T) ∪ (⋃ i, (f i ∩ T)) := by
    rw [← Set.iUnion_inter, Set.sdiff_union_inter]
  have hUnion_le : ∀ s : Finset ι, (⋃ i ∈ s, (f i ∩ T)).encard ≤ ∑ i ∈ s, (M i).eRk T := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
      refine (Set.encard_union_le _ _).trans (add_le_add ?_ ih)
      rw [← ((hf a).subset Set.inter_subset_left).eRk_eq_encard]
      exact (M a).eRk_mono Set.inter_subset_right
  have h1 := Set.encard_union_le ((⋃ i, f i) \ T) (⋃ i, f i ∩ T)
  rw [← hsplit] at h1
  calc (⋃ i, f i).encard
      ≤ ((⋃ i, f i) \ T).encard + (⋃ i, f i ∩ T).encard := h1
    _ ≤ (X \ T).encard + ∑ i : ι, (M i).eRk T := by
        refine add_le_add (Set.encard_mono (Set.sdiff_subset_sdiff_left hIX)) ?_
        simpa only [Finset.mem_univ, Set.iUnion_true] using hUnion_le Finset.univ

end UnionIndep

section ReductionHelpers

variable {ι α : Type*}

/-- A finite set `I : Finset α` is union-independent for `M` iff it is the `Prod.snd`-image of
a common independent set `K` of `Matroid.sum' M` and `unitPartitionMatroid Prod.snd`. -/
private theorem isUnionIndep_iff_exists_commonIndep [DecidableEq α]
    (M : ι → Matroid α) (I : Finset α) :
    IsUnionIndep M (I : Set α) ↔ ∃ K : Finset (ι × α), K.image Prod.snd = I ∧
      IsCommonIndep (Matroid.sum' M) (unitPartitionMatroid Prod.snd) K := by
  classical
  constructor
  · rintro ⟨f, hf, hI⟩
    let pick : {x : α // x ∈ I} → ι := fun x =>
      Classical.choose (Set.mem_iUnion.1 (hI ▸ Finset.mem_coe.2 x.2))
    have hpick : ∀ x : {x : α // x ∈ I}, (x : α) ∈ f (pick x) := fun x =>
      Classical.choose_spec (Set.mem_iUnion.1 (hI ▸ Finset.mem_coe.2 x.2))
    let K : Finset (ι × α) := I.attach.image fun x => (pick x, x.1)
    refine ⟨K, ?_, ?_, ?_⟩
    · ext y
      simp [K]
    · rw [Matroid.sum'_indep_iff]
      intro i
      refine (hf i).subset ?_
      intro x hx
      simp only [Set.mem_preimage, Finset.mem_coe, K, Finset.mem_image, Finset.mem_attach,
        true_and, Prod.mk.injEq, Subtype.exists] at hx
      obtain ⟨y, hy, hi, rfl⟩ := hx
      simpa [← hi] using hpick ⟨y, hy⟩
    · rw [unitPartitionMatroid_indep_iff]
      rintro ⟨i₁, x₁⟩ hx₁ ⟨i₂, x₂⟩ hx₂ hsnd
      simp only [Finset.mem_coe, K, Finset.mem_image, Finset.mem_attach, true_and, Prod.mk.injEq,
        Subtype.exists] at hx₁ hx₂
      obtain ⟨y₁, hy₁, hi₁, rfl⟩ := hx₁
      obtain ⟨y₂, hy₂, hi₂, rfl⟩ := hx₂
      dsimp only at hsnd
      subst hsnd
      rw [← hi₁, ← hi₂]
  · rintro ⟨K, hKI, hsum, -⟩
    rw [Matroid.sum'_indep_iff] at hsum
    refine ⟨fun i => Prod.mk i ⁻¹' (K : Set (ι × α)), hsum, ?_⟩
    ext x
    simp only [Finset.mem_coe, Set.mem_iUnion, Set.mem_preimage]
    rw [← hKI, Finset.mem_image]
    constructor
    · rintro ⟨⟨i, y⟩, hK, hy⟩
      dsimp only at hy
      exact ⟨i, hy ▸ hK⟩
    · rintro ⟨i, hK⟩
      exact ⟨(i, x), hK, rfl⟩

/-- Any finite witness `I ⊆ S` lifts to a common independent subset of `univ ×ˢ S`. -/
private theorem exists_commonIndep_lift [Fintype ι] [DecidableEq α]
    (M : ι → Matroid α) {S I : Finset α}
    (hIS : I ⊆ S) (hI : IsUnionIndep M (I : Set α)) :
    ∃ K : Finset (ι × α), K ⊆ Finset.univ ×ˢ S ∧ K.image Prod.snd = I ∧
      IsCommonIndep (Matroid.sum' M) (unitPartitionMatroid Prod.snd) K ∧ K.card = I.card := by
  classical
  obtain ⟨K, hKI, hK⟩ := (isUnionIndep_iff_exists_commonIndep M I).1 hI
  have hKE : K ⊆ Finset.univ ×ˢ S := by
    intro ⟨i, x⟩ hxK
    exact Finset.mem_product.2 ⟨Finset.mem_univ i, hIS (hKI ▸ Finset.mem_image_of_mem _ hxK)⟩
  have hinj : Set.InjOn Prod.snd (K : Set (ι × α)) :=
    unitPartitionMatroid_indep_iff.1 hK.indep_right
  have hcard : K.card = I.card := by
    rw [← hKI, Finset.card_image_of_injOn hinj]
  exact ⟨K, hKE, hKI, hK, hcard⟩

private theorem encard_iUnion_disjoint_finset {β : Type*} (s : Finset ι) (g : ι → Set β)
    (hdisj : Pairwise (Function.onFun Disjoint g)) :
    (⋃ i ∈ s, g i).encard = ∑ i ∈ s, (g i).encard := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha, Set.encard_union_eq, ih]
    rw [Set.disjoint_iUnion₂_right]
    intro b hb
    exact hdisj (fun h => ha (h ▸ hb))

/-- Rank of any set in `Matroid.sum' M` is the sum of the ranks of its coordinate fibers. -/
private theorem sum'_eRk [Fintype ι] (M : ι → Matroid α) (X : Set (ι × α)) :
    (Matroid.sum' M).eRk X = ∑ i : ι, (M i).eRk (Prod.mk i ⁻¹' X) := by
  classical
  let N := Matroid.sum' M
  let X' := X ∩ N.E
  obtain ⟨J, hJ⟩ := N.exists_isBasis X'
  have hJi : ∀ i : ι, (M i).IsBasis (Prod.mk i ⁻¹' J) (Prod.mk i ⁻¹' X') :=
    Matroid.sum'_isBasis_iff.1 hJ
  have hfib : ∀ i : ι, Prod.mk i ⁻¹' X' = (Prod.mk i ⁻¹' X) ∩ (M i).E := by
    intro i
    ext x
    simp [X', N, Matroid.sum'_ground_eq]
  have hJ_eq : J = ⋃ i ∈ (Finset.univ : Finset ι), Prod.mk i '' (Prod.mk i ⁻¹' J) := by
    ext ⟨i, x⟩
    simp
  have hdisj :
      Pairwise (Function.onFun Disjoint fun i : ι => Prod.mk i '' (Prod.mk i ⁻¹' J)) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    rintro ⟨i', x⟩ ⟨y, _, hy⟩ ⟨z, _, hz⟩
    have h1 : i = i' := by simpa using congrArg Prod.fst hy
    have h2 : j = i' := by simpa using congrArg Prod.fst hz
    exact hij (h1.trans h2.symm)
  calc (Matroid.sum' M).eRk X
      = N.eRk X' := (N.eRk_inter_ground X).symm
    _ = J.encard := hJ.eRk_eq_encard
    _ = ∑ i ∈ (Finset.univ : Finset ι), (Prod.mk i '' (Prod.mk i ⁻¹' J)).encard := by
        rw [← encard_iUnion_disjoint_finset Finset.univ _ hdisj, ← hJ_eq]
    _ = ∑ i : ι, (Prod.mk i ⁻¹' J).encard := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact (Prod.mk_right_injective i).encard_image _
    _ = ∑ i : ι, (M i).eRk (Prod.mk i ⁻¹' X') := by
        refine Finset.sum_congr rfl fun i _ => (hJi i).eRk_eq_encard.symm
    _ = ∑ i : ι, (M i).eRk (Prod.mk i ⁻¹' X) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hfib i, (M i).eRk_inter_ground]

/-- Finite augmentation for `IsUnionIndep` via shortest augmenting walks in `Matroid.sum' M` and
`unitPartitionMatroid Prod.snd`. -/
private theorem isUnionIndep_exists_insert [Finite ι] [DecidableEq α]
    (M : ι → Matroid α) {I J : Finset α}
    (hI : IsUnionIndep M (I : Set α)) (hJ : IsUnionIndep M (J : Set α)) (hlt : I.card < J.card) :
    ∃ e ∈ J, e ∉ I ∧ IsUnionIndep M ((insert e I : Finset α) : Set α) := by
  classical
  have := Fintype.ofFinite ι
  let S : Finset α := I ∪ J
  let E : Finset (ι × α) := Finset.univ ×ˢ S
  let M₁ : Matroid (ι × α) := Matroid.sum' M
  let M₂ : Matroid (ι × α) := unitPartitionMatroid Prod.snd
  obtain ⟨K, hKE, hKI, hK, hKcard⟩ := exists_commonIndep_lift M Finset.subset_union_left hI
  obtain ⟨KJ, hKJE, -, hKJ, hKJcard⟩ := exists_commonIndep_lift M Finset.subset_union_right hJ
  have hex : ∃ p : List (ι × α), IsExchAugWalk M₁ M₂ E K p := by
    by_contra hno
    obtain ⟨U, -, heq⟩ := exists_separator_of_not_exists_exchAugWalk hKE hK hno
    have hmax := isMaxCommonIndep_of_card_eq_eRk_add_eRk hKE hK heq
    have := hmax.2.2 KJ hKJE hKJ
    omega
  obtain ⟨p, hshort⟩ := exists_isShortestExchAugWalk hex
  obtain ⟨hK'E, hK', hK'card⟩ := hshort.augment hKE
  let K' : Finset (ι × α) := K ∆ p.toFinset
  have hinj_K : Set.InjOn Prod.snd (K : Set (ι × α)) :=
    unitPartitionMatroid_indep_iff.1 hK.indep_right
  have hinj_K' : Set.InjOn Prod.snd (K' : Set (ι × α)) :=
    unitPartitionMatroid_indep_iff.1 hK'.indep_right
  have hI_sub : I ⊆ K'.image Prod.snd := by
    intro x hxI
    obtain ⟨v, hvK, hvx⟩ := Finset.mem_image.1 (hKI ▸ hxI)
    by_cases hvp : v ∈ p
    · obtain ⟨t, ht, hvt⟩ := List.mem_iff_getElem.1 hvp
      obtain ⟨hne, hX1, hX2, hmemE, hchain⟩ := hshort.1
      have ht_pos : 0 < t := by
        by_contra ht0
        have hzero : t = 0 := by omega
        subst hzero
        have hv_head : v = p.head hne := by rw [← hvt, List.head_eq_getElem]
        exact (Finset.mem_sdiff.1 hX1.1).2 (hv_head ▸ hvK)
      have ht_lt_pred : t < p.length - 1 := by
        by_contra hge
        have hlast_idx : t = p.length - 1 := by omega
        subst hlast_idx
        have hv_last : v = p.getLast hne := by rw [← hvt, List.getLast_eq_getElem]
        exact (Finset.mem_sdiff.1 hX2.1).2 (hv_last ▸ hvK)
      let u : ι × α := p[t - 1]'(by omega)
      have harc : IsExchArc M₁ M₂ E K u v := by
        have harc' := List.IsChain.getElem hchain (t - 1) (by omega)
        have hidx : (t - 1) + 1 = t := by omega
        simpa only [u, hvt, hidx] using harc'
      have hu_sdiff :
          u ∈ E \ K ∧ M₂.Indep ((insert u (K.erase v) : Finset (ι × α)) : Set (ι × α)) := by
        rcases harc with ⟨_, hvEI, _⟩ | ⟨huE, _, hind₂⟩
        · exact absurd hvK (Finset.mem_sdiff.1 hvEI).2
        · exact ⟨huE, hind₂⟩
      have hu_not_K : u ∉ K := (Finset.mem_sdiff.1 hu_sdiff.1).2
      have hu_K' : u ∈ K' :=
        Finset.mem_symmDiff.2 (.inr ⟨List.mem_toFinset.2 (List.getElem_mem _), hu_not_K⟩)
      have hu_snd_mem_I : u.2 ∈ I := by
        by_contra hu_not_I
        have hins₂ : M₂.Indep ((insert u K : Finset (ι × α)) : Set (ι × α)) := by
          rw [unitPartitionMatroid_indep_iff]
          intro a ha b hb hab
          simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
          rcases ha with rfl | haK <;> rcases hb with rfl | hbK
          · rfl
          · exact absurd (hab ▸ (hKI ▸ Finset.mem_image_of_mem _ hbK)) hu_not_I
          · exact absurd (hab.symm ▸ (hKI ▸ Finset.mem_image_of_mem _ haK)) hu_not_I
          · exact hinj_K haK hbK hab
        let q := p.take t
        have hq_ne : q ≠ [] := by
          intro hnil
          have := congrArg List.length hnil
          simp [q, Nat.min_eq_left ht.le] at this
          omega
        have hq_aug : IsExchAugWalk M₁ M₂ E K q := by
          refine ⟨hq_ne, ?_, ?_, fun z hz => hmemE z (List.mem_of_mem_take hz), hchain.take t⟩
          · rwa [List.head_take]
          · have hlast : q.getLast hq_ne = u := by
              rw [List.getLast_eq_getElem]
              simp only [q, List.length_take, Nat.min_eq_left ht.le]
              exact List.getElem_take
            rw [hlast]
            exact ⟨hu_sdiff.1, hins₂⟩
        have hlen := hshort.2 q hq_aug
        simp only [q, List.length_take, Nat.min_eq_left ht.le] at hlen
        omega
      have huv_eq : u.2 = v.2 := by
        by_contra hne_snd
        obtain ⟨w, hwK, hwsnd⟩ := Finset.mem_image.1 (hKI ▸ hu_snd_mem_I)
        have hw_ne_v : w ≠ v := fun h => hne_snd (hwsnd.symm.trans (congrArg Prod.snd h))
        have hw_erase : w ∈ K.erase v := Finset.mem_erase.2 ⟨hw_ne_v, hwK⟩
        have hu_inj :
            Set.InjOn Prod.snd ((insert u (K.erase v) : Finset (ι × α)) : Set (ι × α)) :=
          unitPartitionMatroid_indep_iff.1 hu_sdiff.2
        have huw := hu_inj
          (Finset.mem_coe.2 (Finset.mem_insert_self u (K.erase v)))
          (Finset.mem_coe.2 (Finset.mem_insert_of_mem hw_erase))
          hwsnd.symm
        exact hu_not_K (huw ▸ hwK)
      exact Finset.mem_image.2 ⟨u, hu_K', huv_eq.trans hvx⟩
    · have hv_K' : v ∈ K' := Finset.mem_symmDiff.2 (.inl ⟨hvK, by simp [hvp]⟩)
      exact Finset.mem_image.2 ⟨v, hv_K', hvx⟩
  have hK'_img_card : (K'.image Prod.snd).card = I.card + 1 := by
    rw [Finset.card_image_of_injOn hinj_K', hK'card, hKcard]
  have hsdiff_card : (K'.image Prod.snd \ I).card = 1 := by
    rw [Finset.card_sdiff_of_subset hI_sub, hK'_img_card]
    omega
  obtain ⟨e, he_eq⟩ := Finset.card_eq_one.1 hsdiff_card
  have he_mem : e ∈ K'.image Prod.snd \ I := by rw [he_eq]; exact Finset.mem_singleton_self e
  have he_img : e ∈ K'.image Prod.snd := (Finset.mem_sdiff.1 he_mem).1
  have he_not_I : e ∉ I := (Finset.mem_sdiff.1 he_mem).2
  have he_S : e ∈ S := by
    obtain ⟨⟨i, x⟩, hxK', rfl⟩ := Finset.mem_image.1 he_img
    exact (Finset.mem_product.1 (hK'E hxK')).2
  have he_J : e ∈ J := Or.resolve_left (Finset.mem_union.1 he_S) he_not_I
  have hK'_img_eq : K'.image Prod.snd = insert e I := by
    ext x
    by_cases hxI : x ∈ I
    · simp [hxI, hI_sub hxI]
    · have hx_sdiff : x ∈ K'.image Prod.snd \ I ↔ x = e := by rw [he_eq, Finset.mem_singleton]
      have hx_img : x ∈ K'.image Prod.snd ↔ x = e :=
        ⟨fun h => hx_sdiff.1 (Finset.mem_sdiff.2 ⟨h, hxI⟩),
         fun h => (Finset.mem_sdiff.1 (hx_sdiff.2 h)).1⟩
      simpa [hxI] using hx_img
  refine ⟨e, he_J, he_not_I,
    (isUnionIndep_iff_exists_commonIndep M (insert e I)).2 ⟨K', hK'_img_eq, hK'⟩⟩

end ReductionHelpers

section MatroidUnion

variable {ι α : Type*} [Finite ι]

/-- The finitary **matroid union** of a finite family `M : ι → Matroid α` on ground set
`⋃ i, (M i).E`, whose independent sets are those whose finite subsets are `IsUnionIndep M`. On all
finite subsets (and everywhere when all `M i` have finite ground sets), independence in
`matroidUnion M` coincides with `IsUnionIndep M`. -/
noncomputable def matroidUnion (M : ι → Matroid α) : Matroid α :=
  letI := Classical.decEq α
  (IndepMatroid.ofFinset (⋃ i, (M i).E) (fun I : Finset α => IsUnionIndep M (I : Set α))
    (by simp)
    (fun I J hJ hIJ => hJ.subset (Finset.coe_subset.2 hIJ))
    (fun I J hI hJ hlt => isUnionIndep_exists_insert M hI hJ hlt)
    (fun I hI => hI.subset_ground)).matroid

/-- The ground set of `matroidUnion M` is `⋃ i, (M i).E`. -/
@[simp] theorem matroidUnion_ground (M : ι → Matroid α) :
    (matroidUnion M).E = ⋃ i, (M i).E := by
  classical
  dsimp only [matroidUnion]
  rw [IndepMatroid.matroid_E, IndepMatroid.ofFinset_E]

/-- On finite sets `I : Set α`, independence in `matroidUnion M` coincides with
`IsUnionIndep M I`. -/
theorem matroidUnion_indep_iff_of_finite (M : ι → Matroid α) {I : Set α} (hI : I.Finite) :
    (matroidUnion M).Indep I ↔ IsUnionIndep M I := by
  classical
  dsimp only [matroidUnion]
  rw [IndepMatroid.matroid_Indep, IndepMatroid.ofFinset_indep']
  constructor
  · intro h
    simpa only [Set.Finite.coe_toFinset] using h hI.toFinset (by simp)
  · intro h J hJI
    exact h.subset hJI

/-- When every `M i` is a finite matroid, `(matroidUnion M).Indep I ↔ IsUnionIndep M I` holds for
all sets `I : Set α`. -/
theorem matroidUnion_indep_iff (M : ι → Matroid α) [∀ i, (M i).Finite] {I : Set α} :
    (matroidUnion M).Indep I ↔ IsUnionIndep M I := by
  have hE : (⋃ i, (M i).E).Finite := Set.finite_iUnion fun i => (M i).ground_finite
  constructor
  · intro h
    exact (matroidUnion_indep_iff_of_finite M (hE.subset h.subset_ground)).1 h
  · intro h
    exact (matroidUnion_indep_iff_of_finite M (hE.subset h.subset_ground)).2 h

end MatroidUnion

section MinMaxAndPartitioning

variable {ι α : Type*} [Fintype ι]

/-- **Edmonds' matroid union theorem** (witness form; [Schrijver2017]; [Schrijver2003]): for a
finite family `M : ι → Matroid α` and a finite set `S : Finset α`, some union-independent subset
`I ⊆ S` and subset `T ⊆ S` attain equality in weak duality:
`(I.card : ℕ∞) = (S \ T).card + ∑ i : ι, (M i).eRk ↑T`. -/
theorem exists_isUnionIndep_card_eq [DecidableEq α] (M : ι → Matroid α) (S : Finset α) :
    ∃ I T : Finset α, I ⊆ S ∧ T ⊆ S ∧ IsUnionIndep M (I : Set α) ∧
      (I.card : ℕ∞) = ((S \ T).card : ℕ∞) + ∑ i : ι, (M i).eRk (T : Set α) := by
  classical
  let E : Finset (ι × α) := Finset.univ ×ˢ S
  obtain ⟨K, U, hUE, hmax, heq⟩ :=
    exists_commonIndep_card_eq_eRk_add_eRk (Matroid.sum' M) (unitPartitionMatroid Prod.snd) E
  let I : Finset α := K.image Prod.snd
  let T : Finset α := S.filter fun x => ∀ i : ι, (i, x) ∈ U
  have hIS : I ⊆ S := by
    intro x hx
    obtain ⟨⟨i, y⟩, hyK, rfl⟩ := Finset.mem_image.1 hx
    exact (Finset.mem_product.1 (hmax.1 hyK)).2
  have hTS : T ⊆ S := Finset.filter_subset _ S
  have hI : IsUnionIndep M (I : Set α) :=
    (isUnionIndep_iff_exists_commonIndep M I).2 ⟨K, rfl, hmax.2.1⟩
  have hI_card : I.card = K.card :=
    Finset.card_image_of_injOn (unitPartitionMatroid_indep_iff.1 hmax.2.1.indep_right)
  have hUT : Finset.univ ×ˢ T ⊆ U := by
    rintro ⟨i, x⟩ hx
    rw [Finset.mem_product] at hx
    exact (Finset.mem_filter.1 hx.2).2 i
  have hsum_rk :
      ∑ i : ι, (M i).eRk (T : Set α) ≤ (Matroid.sum' M).eRk (U : Set (ι × α)) := by
    have hfib :
        ∀ i : ι, Prod.mk i ⁻¹' ((Finset.univ ×ˢ T : Finset (ι × α)) : Set (ι × α)) = T := by
      intro i
      ext x
      simp
    calc ∑ i : ι, (M i).eRk (T : Set α)
        = ∑ i : ι,
            (M i).eRk (Prod.mk i ⁻¹' ((Finset.univ ×ˢ T : Finset (ι × α)) : Set (ι × α))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hfib i]
      _ = (Matroid.sum' M).eRk ((Finset.univ ×ˢ T : Finset (ι × α)) : Set (ι × α)) :=
          (sum'_eRk M _).symm
      _ ≤ (Matroid.sum' M).eRk (U : Set (ι × α)) :=
          (Matroid.sum' M).eRk_mono (Finset.coe_subset.2 hUT)
  have hsdiff_eq : (E \ U).image Prod.snd = S \ T := by
    ext x
    simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_product, Finset.mem_univ,
      true_and, E, T, Finset.mem_filter, not_and, not_forall, Prod.exists]
    constructor
    · rintro ⟨i, x', ⟨hx'S, hiU⟩, rfl⟩
      exact ⟨hx'S, fun _ => ⟨i, hiU⟩⟩
    · rintro ⟨hxS, hnot⟩
      obtain ⟨i, hiU⟩ := hnot hxS
      exact ⟨i, x, ⟨hxS, hiU⟩, rfl⟩
  have hpart_rk :
      (unitPartitionMatroid Prod.snd).eRk ((E \ U : Finset (ι × α)) : Set (ι × α)) =
        ((S \ T).card : ℕ∞) := by
    rw [unitPartitionMatroid_eRk, ← Finset.coe_image, hsdiff_eq, Set.encard_coe_eq_coe_finsetCard]
  have hle : ((S \ T).card : ℕ∞) + ∑ i : ι, (M i).eRk (T : Set α) ≤ (I.card : ℕ∞) := by
    calc ((S \ T).card : ℕ∞) + ∑ i : ι, (M i).eRk (T : Set α)
        ≤ (unitPartitionMatroid Prod.snd).eRk ((E \ U : Finset (ι × α)) : Set (ι × α)) +
            (Matroid.sum' M).eRk (U : Set (ι × α)) := add_le_add hpart_rk.symm.le hsum_rk
      _ = (K.card : ℕ∞) := by rw [add_comm, ← heq]
      _ = (I.card : ℕ∞) := by rw [hI_card]
  have hge : (I.card : ℕ∞) ≤ ((S \ T).card : ℕ∞) + ∑ i : ι, (M i).eRk (T : Set α) := by
    have hweak := hI.encard_le_encard_sdiff_add_sum_eRk (Finset.coe_subset.2 hIS) (T : Set α)
    rwa [← Finset.coe_sdiff, Set.encard_coe_eq_coe_finsetCard,
      Set.encard_coe_eq_coe_finsetCard] at hweak
  exact ⟨I, T, hIS, hTS, hI, le_antisymm hge hle⟩

/-- **Edmonds' matroid union rank theorem** ([Schrijver2017]; [Schrijver2003]): for any finite
family `M : ι → Matroid α` and finite set `X : Set α`, the rank `(matroidUnion M).eRk X` equals
`⨅ T ⊆ X, (X \ T).encard + ∑ i, (M i).eRk T`. -/
theorem matroidUnion_eRk_eq_iInf (M : ι → Matroid α) {X : Set α} (hX : X.Finite) :
    (matroidUnion M).eRk X =
      ⨅ (T : Set α) (_ : T ⊆ X), (X \ T).encard + ∑ i : ι, (M i).eRk T := by
  classical
  refine le_antisymm ?_ ?_
  · rw [Matroid.eRk_le_iff]
    intro I hIX hI
    rw [matroidUnion_indep_iff_of_finite M (hX.subset hIX)] at hI
    exact le_iInf₂ fun T _ => hI.encard_le_encard_sdiff_add_sum_eRk hIX T
  · obtain ⟨I, T, hIS, hTS, hI, heq⟩ := exists_isUnionIndep_card_eq M hX.toFinset
    have hTX : (T : Set α) ⊆ X := fun x hx => (Set.Finite.mem_toFinset hX).1 (hTS hx)
    have hIX : (I : Set α) ⊆ X := fun x hx => (Set.Finite.mem_toFinset hX).1 (hIS hx)
    have hI_indep : (matroidUnion M).Indep (I : Set α) :=
      (matroidUnion_indep_iff_of_finite M I.finite_toSet).2 hI
    have hsd : X \ (T : Set α) = ((hX.toFinset \ T : Finset α) : Set α) := by
      rw [Finset.coe_sdiff, Set.Finite.coe_toFinset]
    calc ⨅ (T : Set α) (_ : T ⊆ X), (X \ T).encard + ∑ i : ι, (M i).eRk T
        ≤ (X \ (T : Set α)).encard + ∑ i : ι, (M i).eRk (T : Set α) :=
          iInf₂_le (T : Set α) hTX
      _ = (I.card : ℕ∞) := by
          rw [hsd, Set.encard_coe_eq_coe_finsetCard, ← heq]
      _ = (I : Set α).encard := (Set.encard_coe_eq_coe_finsetCard I).symm
      _ ≤ (matroidUnion M).eRk X := hI_indep.encard_le_eRk_of_subset hIX

/-- **Edmonds' matroid union min–max theorem** (sup–inf form; [Schrijver2017]; [Schrijver2003]):
for any finite family `M : ι → Matroid α` and finite set `X : Set α`, the maximum cardinality of a
union-independent subset of `X` equals `⨅ T ⊆ X, (X \ T).encard + ∑ i, (M i).eRk T`. -/
theorem iSup_encard_isUnionIndep_eq_iInf (M : ι → Matroid α) {X : Set α} (hX : X.Finite) :
    ⨆ (I : Set α) (_ : I ⊆ X ∧ IsUnionIndep M I), I.encard =
      ⨅ (T : Set α) (_ : T ⊆ X), (X \ T).encard + ∑ i : ι, (M i).eRk T := by
  refine le_antisymm (iSup₂_le fun I hI => le_iInf₂ fun T _ =>
    hI.2.encard_le_encard_sdiff_add_sum_eRk hI.1 T) ?_
  rw [← matroidUnion_eRk_eq_iInf M hX]
  obtain ⟨I, hIX⟩ := (matroidUnion M).exists_isBasis' X
  have hIfin : I.Finite := hX.subset hIX.subset
  have hI_indep : IsUnionIndep M I :=
    (matroidUnion_indep_iff_of_finite M hIfin).1 hIX.indep
  rw [hIX.eRk_eq_encard]
  exact le_iSup₂ (f := fun (I : Set α) (_ : I ⊆ X ∧ IsUnionIndep M I) => I.encard)
    I ⟨hIX.subset, hI_indep⟩

/-- Lift a union-independent `Finset α` to a pairwise disjoint partition into independent
`Finset`s. -/
private theorem exists_partition_of_isUnionIndep [DecidableEq α] {M : ι → Matroid α}
    {S : Finset α} (hS : IsUnionIndep M (S : Set α)) :
    ∃ P : ι → Finset α, (∀ i, (M i).Indep (P i : Set α)) ∧
      Pairwise (Function.onFun Disjoint P) ∧ Finset.univ.biUnion P = S := by
  classical
  obtain ⟨K, hKS, hK⟩ := (isUnionIndep_iff_exists_commonIndep M S).1 hS
  let P : ι → Finset α := fun i => (K.filter fun p => p.1 = i).image Prod.snd
  refine ⟨P, ?_, ?_, ?_⟩
  · intro i
    have hsum := Matroid.sum'_indep_iff.1 hK.indep_left i
    refine hsum.subset ?_
    intro x hx
    simp only [P, Finset.coe_image, Finset.coe_filter, Set.mem_image, Set.mem_ofPred_eq,
      Prod.exists] at hx
    obtain ⟨j, y, ⟨hyK, rfl⟩, rfl⟩ := hx
    exact hyK
  · intro i j hij
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxi hxj
    simp only [P, Finset.mem_image, Finset.mem_filter, Prod.exists] at hxi hxj
    obtain ⟨i', y₁, ⟨hy₁K, rfl⟩, rfl⟩ := hxi
    obtain ⟨j', y₂, ⟨hy₂K, rfl⟩, hy⟩ := hxj
    have hinj : Set.InjOn Prod.snd (K : Set (ι × α)) :=
      unitPartitionMatroid_indep_iff.1 hK.indep_right
    have heq := hinj hy₁K hy₂K hy.symm
    exact hij (congrArg Prod.fst heq)
  · ext x
    simp only [P, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_filter, Prod.exists]
    constructor
    · rintro ⟨i, j, y, ⟨hyK, _⟩, rfl⟩
      exact hKS ▸ Finset.mem_image_of_mem _ hyK
    · intro hxS
      obtain ⟨⟨i, y⟩, hyK, hy⟩ := Finset.mem_image.1 (hKS.symm ▸ hxS)
      exact ⟨i, i, y, ⟨hyK, rfl⟩, hy⟩

/-- **Edmonds–Fulkerson matroid partitioning theorem** ([Schrijver2017]; [Schrijver2003]): a
finite set `S : Finset α` can be partitioned into pairwise disjoint sets `P i` with
`(M i).Indep (P i : Set α)` if and only if `(T.card : ℕ∞) ≤ ∑ i : ι, (M i).eRk ↑T` for every
`T ⊆ S`. -/
theorem exists_partition_indep_iff [DecidableEq α] (M : ι → Matroid α) (S : Finset α) :
    (∃ P : ι → Finset α, (∀ i, (M i).Indep (P i : Set α)) ∧
      Pairwise (Function.onFun Disjoint P) ∧ Finset.univ.biUnion P = S) ↔
      ∀ T ⊆ S, (T.card : ℕ∞) ≤ ∑ i : ι, (M i).eRk (T : Set α) := by
  constructor
  · rintro ⟨P, hP_indep, -, hP_union⟩ T hTS
    have hT_eq : T = Finset.univ.biUnion fun i => T ∩ P i := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_inter]
      constructor
      · intro hxT
        obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.1 (hP_union.symm ▸ hTS hxT)
        exact ⟨i, hxT, hi⟩
      · rintro ⟨i, hxT, _⟩
        exact hxT
    have hcard_le : T.card ≤ ∑ i : ι, (T ∩ P i).card := by
      conv_lhs => rw [hT_eq]
      exact Finset.card_biUnion_le
    calc (T.card : ℕ∞)
        ≤ ((∑ i : ι, (T ∩ P i).card : ℕ) : ℕ∞) := Nat.cast_le.2 hcard_le
      _ = ∑ i : ι, ((T ∩ P i).card : ℕ∞) := by rw [Nat.cast_sum]
      _ ≤ ∑ i : ι, (M i).eRk (T : Set α) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← Set.encard_coe_eq_coe_finsetCard]
          exact ((hP_indep i).subset
            (Finset.coe_subset.2 Finset.inter_subset_right)).encard_le_eRk_of_subset
            (Finset.coe_subset.2 Finset.inter_subset_left)
  · intro hcond
    obtain ⟨I, T, hIS, hTS, hI, heq⟩ := exists_isUnionIndep_card_eq M S
    have hT := hcond T hTS
    have hcard_le : (S.card : ℕ∞) ≤ (I.card : ℕ∞) := by
      calc (S.card : ℕ∞)
          = ((S \ T).card : ℕ∞) + (T.card : ℕ∞) := by
            rw [← Nat.cast_add, Finset.card_sdiff_add_card_eq_card hTS]
        _ ≤ ((S \ T).card : ℕ∞) + ∑ i : ι, (M i).eRk (T : Set α) := add_le_add le_rfl hT
        _ = (I.card : ℕ∞) := heq.symm
    have hIS_eq : I = S := Finset.eq_of_subset_of_card_le hIS (Nat.cast_le.1 hcard_le)
    exact exists_partition_of_isUnionIndep (hIS_eq ▸ hI)

/-- **Edmonds' matroid covering / partitioning theorem** ([Schrijver2017]; [Schrijver2003]): a
finite set `S : Finset α` can be partitioned into `k` pairwise disjoint `M`-independent subsets if
and only if `(T.card : ℕ∞) ≤ k * M.eRk ↑T` for every `T ⊆ S`. -/
theorem exists_partition_indep_const_iff [DecidableEq α]
    (M : Matroid α) (k : ℕ) (S : Finset α) :
    (∃ P : Fin k → Finset α, (∀ i, M.Indep (P i : Set α)) ∧
      Pairwise (Function.onFun Disjoint P) ∧ Finset.univ.biUnion P = S) ↔
      ∀ T ⊆ S, (T.card : ℕ∞) ≤ (k : ℕ∞) * M.eRk (T : Set α) := by
  simpa only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] using
    exists_partition_indep_iff (fun _ : Fin k => M) S

/-- **Edmonds' disjoint bases (base-packing) theorem** ([Schrijver2017]; [Schrijver2003]): a finite
matroid `M : Matroid α` (`hE : M.E.Finite`) admits `k` pairwise disjoint bases if and only if
`k * M.eRank ≤ (M.E \ T).encard + k * M.eRk T` for every `T ⊆ M.E`. -/
theorem exists_disjoint_isBase_iff (M : Matroid α) (hE : M.E.Finite) (k : ℕ) :
    (∃ B : Fin k → Set α, (∀ i, M.IsBase (B i)) ∧ Pairwise (Function.onFun Disjoint B)) ↔
      ∀ T ⊆ M.E, (k : ℕ∞) * M.eRank ≤ (M.E \ T).encard + (k : ℕ∞) * M.eRk T := by
  classical
  have : M.Finite := ⟨hE⟩
  have hrank_ne : M.eRank ≠ ⊤ := M.eRank_ne_top_iff.2 (Matroid.rankFinite_of_finite M)
  constructor
  · rintro ⟨B, hB_base, hB_disj⟩ T hTE
    have hI : IsUnionIndep (fun _ : Fin k => M) (⋃ i, B i) :=
      ⟨B, fun i => (hB_base i).indep, rfl⟩
    have hIE : (⋃ i, B i) ⊆ M.E := Set.iUnion_subset fun i => (hB_base i).subset_ground
    have hcard : (⋃ i, B i).encard = (k : ℕ∞) * M.eRank := by
      have hbi : (⋃ i, B i) = ⋃ i ∈ (Finset.univ : Finset (Fin k)), B i := by simp
      rw [hbi, encard_iUnion_disjoint_finset Finset.univ B hB_disj]
      simp only [(hB_base _).encard_eq_eRank, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    simpa only [hcard, Finset.sum_const, Finset.card_fin, nsmul_eq_mul] using
      hI.encard_le_encard_sdiff_add_sum_eRk hIE T
  · intro hcond
    let E := hE.toFinset
    obtain ⟨I, T, -, hTE, hI, heq⟩ := exists_isUnionIndep_card_eq (fun _ : Fin k => M) E
    have hTE' : (T : Set α) ⊆ M.E := fun x hx => (Set.Finite.mem_toFinset hE).1 (hTE hx)
    have hsd : M.E \ (T : Set α) = ((E \ T : Finset α) : Set α) := by
      rw [Finset.coe_sdiff, Set.Finite.coe_toFinset]
    have hk_le_I : (k : ℕ∞) * M.eRank ≤ (I.card : ℕ∞) := by
      calc (k : ℕ∞) * M.eRank
          ≤ (M.E \ (T : Set α)).encard + (k : ℕ∞) * M.eRk (T : Set α) := hcond (T : Set α) hTE'
        _ = ((E \ T).card : ℕ∞) + ∑ _i : Fin k, M.eRk (T : Set α) := by
            rw [hsd, Set.encard_coe_eq_coe_finsetCard, Finset.sum_const, Finset.card_fin,
              nsmul_eq_mul]
        _ = (I.card : ℕ∞) := heq.symm
    obtain ⟨P, hP_indep, hP_disj, hP_union⟩ := exists_partition_of_isUnionIndep hI
    have hI_sum : I.card = ∑ i : Fin k, (P i).card := by
      rw [← hP_union, Finset.card_biUnion fun i _ j _ hij => hP_disj hij]
    have hP_le : ∀ i : Fin k, (P i).card ≤ M.eRank.toNat := by
      intro i
      have hle := (hP_indep i).encard_le_eRank
      rw [Set.encard_coe_eq_coe_finsetCard, ← ENat.natCast_toNat hrank_ne] at hle
      exact Nat.cast_le.1 hle
    have hsum_ge : k * M.eRank.toNat ≤ ∑ i : Fin k, (P i).card := by
      rw [← hI_sum]
      have h' := hk_le_I
      rw [← ENat.natCast_toNat hrank_ne, ← Nat.cast_mul] at h'
      exact Nat.cast_le.1 h'
    have hsum_eq : ∑ i : Fin k, (P i).card = ∑ _i : Fin k, M.eRank.toNat := by
      refine le_antisymm (Finset.sum_le_sum fun i _ => hP_le i) ?_
      simpa only [Finset.sum_const, Finset.card_fin, smul_eq_mul] using hsum_ge
    have hP_eq : ∀ i : Fin k, (P i).card = M.eRank.toNat := fun i =>
      (Finset.sum_eq_sum_iff_of_le fun j _ => hP_le j).1 hsum_eq i (Finset.mem_univ i)
    refine ⟨fun i => (P i : Set α), fun i => ?_, fun i j hij => Finset.disjoint_coe.2 (hP_disj hij)⟩
    refine (hP_indep i).isBase_of_eRk_ge (Finset.finite_toSet _) ?_
    rw [(hP_indep i).eRk_eq_encard, Set.encard_coe_eq_coe_finsetCard, hP_eq i,
      ENat.natCast_toNat hrank_ne]

end MinMaxAndPartitioning

end Cslib.Algorithms.Lean.Matroid

end
