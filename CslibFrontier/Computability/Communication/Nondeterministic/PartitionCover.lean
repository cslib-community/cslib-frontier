/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Nondeterministic.CoverNumber
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.NonnegRank
import CslibFrontier.Foundations.Data.ENat.IInf
import Mathlib.Data.Fintype.Sigma

/-!
# Unambiguous (partition) covers and SUM-rank

An *unambiguous* or *partition* `z`-cover of a relation `R : X → Y → Bool → Prop` on `A × B`
(`Nondeterministic.IsPartitionCover`) is a `z`-cover (`Nondeterministic.IsCover`) in which every
pair `(x, y) ∈ A × B` where `!z` is unacceptable (`¬ R x y (!z)`) belongs to **exactly one**
rectangle. Rectangles may still overlap on "don't-care" pairs (`*`-entries of a partially defined
Boolean matrix) where both `z` and `!z` are acceptable.

The *partition cover number* `Nondeterministic.partitionCoverNumber z R A B` is the minimum number
of rectangles in a partition `z`-cover, or `⊤` if none exists. Every partition cover is a cover, so
`coverNumber z R A B ≤ partitionCoverNumber z R A B` (`coverNumber_le_partitionCoverNumber`). On all
of `X × Y`, `partitionCoverNumber z R Set.univ Set.univ` equals the minimum `(ℕ, +, ·)`-rank
(`Matrix.nonnegRank` over `ℕ`) over all matrices `M : Matrix X Y ℕ` completing `R` with `1` on
required `z`-entries and `0` on forbidden entries (`partitionCoverNumber_eq_iInf_nonnegRank_nat`),
matching the SUM-rank / partition rank `rk_+` of [Sergeev2026UniqueDisjointness, §1, p. 2] and
unambiguous nondeterministic covers of [KushilevitzNisan1997, Chapter 2].

## Main definitions

* `Cslib.Communication.Nondeterministic.IsPartitionCover`: unambiguous / partition `z`-covers by
  rectangles.
* `Cslib.Communication.Nondeterministic.partitionCoverNumber`,
  `Cslib.Communication.Nondeterministic.partitionCoverNumberFun`: the minimum number of rectangles
  in a partition `z`-cover.

## Main results

* `Cslib.Communication.Nondeterministic.IsPartitionCover.isCover`,
  `Cslib.Communication.Nondeterministic.coverNumber_le_partitionCoverNumber`: every partition cover
  is a cover (`rk_∨ ≤ rk_+`).
* `Cslib.Communication.Nondeterministic.IsPartitionCover.partitionCoverNumber_le`,
  `Cslib.Communication.Nondeterministic.partitionCoverNumber_le_iff`,
  `Cslib.Communication.Nondeterministic.le_partitionCoverNumber_iff`: bounds through partition
  covers.
* `Cslib.Communication.Nondeterministic.coverNumber_le_sum_fibers`,
  `Cslib.Communication.Nondeterministic.partitionCoverNumber_le_sum_fibers`: subadditivity over
  row-and-column fiber decompositions.
* `Cslib.Communication.Nondeterministic.partitionCoverNumber_eq_iInf_nonnegRank_nat`: exact
  equality between `partitionCoverNumber` and the minimum `(ℕ, +, ·)` factorization rank over
  matrix completions of `R`.

## References

* [E. Kushilevitz, N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
* [I. S. Sergeev, *Upper Bounds for the Monotone Rank of the Unique Disjointness Matrix*]
  [Sergeev2026UniqueDisjointness], §1, p. 2
-/

public section

namespace Cslib.Communication

namespace Nondeterministic

open Finset Matrix

variable {X Y : Type*}

/-- `C` is a partition (or unambiguous) `z`-cover of `R` on `A × B` by rectangles indexed by `κ`:
`z` is an acceptable answer on the part of each rectangle inside `A × B`, and every pair of `A × B`
on which `!z` is not acceptable lies in **exactly one** rectangle
[Sergeev2026UniqueDisjointness, §1, p. 2]. -/
@[expose] def IsPartitionCover (z : Bool) (R : X → Y → Bool → Prop) (A : Set X) (B : Set Y)
    {κ : Type*} (C : κ → Set X × Set Y) : Prop :=
  (∀ w, ∀ x ∈ A, x ∈ (C w).1 → ∀ y ∈ B, y ∈ (C w).2 → R x y z) ∧
    ∀ x ∈ A, ∀ y ∈ B, ¬R x y (!z) → ∃! w, x ∈ (C w).1 ∧ y ∈ (C w).2

/-- The partition `z`-cover number of `R` on `A × B`: the least number of rectangles in a partition
`z`-cover of `R` on `A × B`, or `⊤` if there is none. -/
noncomputable def partitionCoverNumber (z : Bool) (R : X → Y → Bool → Prop)
    (A : Set X) (B : Set Y) : ℕ∞ :=
  ⨅ r : {r : ℕ // ∃ C : Fin r → Set X × Set Y, IsPartitionCover z R A B C}, (r.1 : ℕ∞)

/-- The partition `z`-cover number of a function `f : X → Y → Bool` on `A × B`. -/
@[expose] noncomputable def partitionCoverNumberFun (z : Bool) (f : X → Y → Bool)
    (A : Set X) (B : Set Y) : ℕ∞ :=
  partitionCoverNumber z (fun x y b => f x y = b) A B

variable {R : X → Y → Bool → Prop} {f : X → Y → Bool} {z : Bool} {A : Set X} {B : Set Y}
  {κ κ' : Type*}

/-- Every partition `z`-cover is a `z`-cover. -/
theorem IsPartitionCover.isCover {C : κ → Set X × Set Y}
    (hC : IsPartitionCover z R A B C) : IsCover z R A B C :=
  ⟨hC.1, fun x hx y hy hR => (hC.2 x hx y hy hR).exists⟩

/-- A partition cover can be reindexed along an embedding of index types, padding new indices with
empty rectangles. -/
theorem IsPartitionCover.of_embedding {C : κ → Set X × Set Y}
    (hC : IsPartitionCover z R A B C) (e : κ ↪ κ') :
    IsPartitionCover z R A B (Function.extend e C fun _ => (∅, ∅)) := by
  obtain ⟨hmem, hcov⟩ := hC
  refine ⟨fun w' x hx hxC y hy hyC => ?_, fun x hx y hy hR => ?_⟩
  · by_cases hw' : ∃ w, e w = w'
    · obtain ⟨w, rfl⟩ := hw'
      rw [e.injective.extend_apply] at hxC hyC
      exact hmem w x hx hxC y hy hyC
    · rw [Function.extend_apply' _ _ _ hw'] at hxC
      exact hxC.elim
  · obtain ⟨w, hw, hunique⟩ := hcov x hx y hy hR
    refine ⟨e w, by dsimp only; rwa [e.injective.extend_apply], fun w' hw' => ?_⟩
    dsimp only at hw'
    by_cases hex : ∃ u, e u = w'
    · obtain ⟨u, rfl⟩ := hex
      exact congrArg e (hunique u (by rwa [e.injective.extend_apply] at hw'))
    · rw [Function.extend_apply' _ _ _ hex] at hw'
      exact hw'.1.elim

/-- A partition cover indexed by a finite type `κ` bounds `partitionCoverNumber` by `|κ|`. -/
theorem IsPartitionCover.partitionCoverNumber_le [Fintype κ] {C : κ → Set X × Set Y}
    (hC : IsPartitionCover z R A B C) :
    partitionCoverNumber z R A B ≤ Fintype.card κ := by
  classical
  exact ENat.iInf_subtype_natCast_le (d := id)
    ⟨_, hC.of_embedding (Fintype.equivFin κ).toEmbedding⟩

/-- Lower bounds on `partitionCoverNumber` are lower bounds on the size of every partition cover. -/
theorem le_partitionCoverNumber_iff {c : ℕ∞} :
    c ≤ partitionCoverNumber z R A B ↔
      ∀ r (C : Fin r → Set X × Set Y), IsPartitionCover z R A B C → c ≤ r :=
  (ENat.le_iInf_subtype_natCast_iff (d := id)).trans
    ⟨fun h r C hC => h r ⟨C, hC⟩, fun h r ⟨C, hC⟩ => h r C hC⟩

/-- `R` has partition `z`-cover number at most `r` iff it has a partition `z`-cover by `r`
rectangles. -/
theorem partitionCoverNumber_le_iff {r : ℕ} :
    partitionCoverNumber z R A B ≤ r ↔
      ∃ C : Fin r → Set X × Set Y, IsPartitionCover z R A B C := by
  classical
  exact (ENat.iInf_subtype_natCast_le_natCast_iff (d := id)).trans
    ⟨fun ⟨_, ⟨C, hC⟩, hsr⟩ => ⟨_, hC.of_embedding (Fin.castLEEmb hsr)⟩,
      fun ⟨C, hC⟩ => ⟨r, ⟨C, hC⟩, le_rfl⟩⟩

/-- **Covering rank is at most partition rank** (`rk_∨ ≤ rk_+`,
[Sergeev2026UniqueDisjointness, §1, p. 2]). -/
theorem coverNumber_le_partitionCoverNumber :
    coverNumber z R A B ≤ partitionCoverNumber z R A B :=
  le_partitionCoverNumber_iff.2 fun _ _ hC =>
    hC.isCover.coverNumber_le.trans_eq (by rw [Fintype.card_fin])

/-- `coverNumber_le_partitionCoverNumber` for functions. -/
theorem coverNumberFun_le_partitionCoverNumberFun :
    coverNumberFun z f A B ≤ partitionCoverNumberFun z f A B :=
  coverNumber_le_partitionCoverNumber

/-! ### Subadditivity across row and column partitions -/

private theorem le_sum_prod_of_eq_natCast {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {c : ℕ∞}
    {F : ι₁ → ι₂ → ℕ∞}
    (h : ∀ r : ι₁ → ι₂ → ℕ, (∀ i j, (r i j : ℕ∞) = F i j) →
      c ≤ ((∑ i : ι₁, ∑ j : ι₂, r i j : ℕ) : ℕ∞)) :
    c ≤ ∑ i : ι₁, ∑ j : ι₂, F i j := by
  classical
  by_cases htop : ∃ i j, F i j = ⊤
  · obtain ⟨i₀, j₀, hij⟩ := htop
    exact le_top.trans <|
      (hij ▸ single_le_sum (f := F i₀) (fun _ _ => zero_le) (mem_univ j₀)).trans
        (single_le_sum (f := fun i => ∑ j, F i j) (fun _ _ => zero_le) (mem_univ i₀))
  · push Not at htop
    choose r hr using fun i j => ENat.ne_top_iff_exists.1 (htop i j)
    refine (h r hr).trans_eq ?_
    push_cast
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => hr i j

/-- Partitioning `A` by `f : X → ι₁` and `B` by `g : Y → ι₂` bounds `coverNumber` by the sum of the
fiberwise cover numbers. -/
theorem coverNumber_le_sum_fibers {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (f : X → ι₁) (g : Y → ι₂) :
    coverNumber z R A B ≤
      ∑ i : ι₁, ∑ j : ι₂, coverNumber z R (A ∩ f ⁻¹' {i}) (B ∩ g ⁻¹' {j}) := by
  refine le_sum_prod_of_eq_natCast fun r hr => ?_
  choose C hC using fun i j => coverNumber_le_iff.1 (hr i j).ge
  have hcov : IsCover z R A B
      (fun w : Σ p : ι₁ × ι₂, Fin (r p.1 p.2) => (f ⁻¹' {w.1.1} ∩ (C w.1.1 w.1.2 w.2).1,
        g ⁻¹' {w.1.2} ∩ (C w.1.1 w.1.2 w.2).2)) :=
    ⟨fun ⟨⟨i, j⟩, w⟩ x hxA hxC y hyB hyC =>
      (hC i j).1 w x ⟨hxA, hxC.1⟩ hxC.2 y ⟨hyB, hyC.1⟩ hyC.2, fun x hxA y hyB hR =>
      let ⟨w, hw1, hw2⟩ := (hC (f x) (g y)).2 x ⟨hxA, rfl⟩ y ⟨hyB, rfl⟩ hR
      ⟨⟨(f x, g y), w⟩, ⟨rfl, hw1⟩, ⟨rfl, hw2⟩⟩⟩
  exact hcov.coverNumber_le.trans_eq (congrArg Nat.cast
    (by simp only [Fintype.card_sigma, Fintype.sum_prod_type, Fintype.card_fin]))

/-- Partitioning `A` by `f : X → ι₁` and `B` by `g : Y → ι₂` bounds `partitionCoverNumber` by the
sum of the fiberwise partition cover numbers. -/
theorem partitionCoverNumber_le_sum_fibers {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (f : X → ι₁) (g : Y → ι₂) :
    partitionCoverNumber z R A B ≤
      ∑ i : ι₁, ∑ j : ι₂, partitionCoverNumber z R (A ∩ f ⁻¹' {i}) (B ∩ g ⁻¹' {j}) := by
  refine le_sum_prod_of_eq_natCast fun r hr => ?_
  choose C hC using fun i j => partitionCoverNumber_le_iff.1 (hr i j).ge
  have hcov : IsPartitionCover z R A B
      (fun w : Σ p : ι₁ × ι₂, Fin (r p.1 p.2) => (f ⁻¹' {w.1.1} ∩ (C w.1.1 w.1.2 w.2).1,
        g ⁻¹' {w.1.2} ∩ (C w.1.1 w.1.2 w.2).2)) := by
    refine ⟨fun ⟨⟨i, j⟩, w⟩ x hxA hxC y hyB hyC =>
      (hC i j).1 w x ⟨hxA, hxC.1⟩ hxC.2 y ⟨hyB, hyC.1⟩ hyC.2, fun x hxA y hyB hR => ?_⟩
    obtain ⟨w, ⟨hw1, hw2⟩, hunique⟩ := (hC (f x) (g y)).2 x ⟨hxA, rfl⟩ y ⟨hyB, rfl⟩ hR
    refine ⟨⟨(f x, g y), w⟩, ⟨⟨rfl, hw1⟩, ⟨rfl, hw2⟩⟩, ?_⟩
    rintro ⟨⟨i', j'⟩, w'⟩ ⟨⟨rfl, hxC'⟩, ⟨rfl, hyC'⟩⟩
    exact congrArg (Sigma.mk _) (hunique w' ⟨hxC', hyC'⟩)
  exact hcov.partitionCoverNumber_le.trans_eq (congrArg Nat.cast
    (by simp only [Fintype.card_sigma, Fintype.sum_prod_type, Fintype.card_fin]))

/-! ### Equivalence with `(ℕ, +, ·)`-semiring rank (`rk_+`) -/

private theorem existsUnique_ne_zero_of_sum_eq_one {ι : Type*} [Fintype ι] {g : ι → ℕ}
    (hsum : ∑ i : ι, g i = 1) : ∃! i : ι, g i ≠ 0 := by
  classical
  obtain ⟨i₀, _, hi₀⟩ := exists_ne_zero_of_sum_ne_zero (hsum.symm ▸ one_ne_zero)
  exact ⟨i₀, hi₀, fun j hj => of_not_not fun hji => by
    have := add_le_sum (f := g) (fun _ _ => Nat.zero_le _) (mem_univ j) (mem_univ i₀) hji
    omega⟩

/-- **Equivalence with `(ℕ, +, ·)`-rank (`rk_+`)** ([Sergeev2026UniqueDisjointness, §1, p. 2]): on
`X × Y`, `partitionCoverNumber z R Set.univ Set.univ` equals the infimum of `M.nonnegRank` over all
`ℕ`-valued matrices `M : Matrix X Y ℕ` that take value `1` where `!z` is unacceptable and `0` where
`z` is unacceptable. -/
theorem partitionCoverNumber_eq_iInf_nonnegRank_nat (z : Bool) (R : X → Y → Bool → Prop) :
    partitionCoverNumber z R Set.univ Set.univ =
      ⨅ (M : Matrix X Y ℕ)
        (_ : (∀ x y, ¬R x y (!z) → M x y = 1) ∧ (∀ x y, ¬R x y z → M x y = 0)),
        M.nonnegRank := by
  classical
  refine le_antisymm ?_ ?_
  · refine le_iInf fun M => le_iInf fun ⟨h1, h0⟩ => le_nonnegRank_iff.2 fun r ⟨T, U, _, _, hTU⟩ =>
      partitionCoverNumber_le_iff.2 ⟨fun i => ({x | T x i ≠ 0}, {y | U i y ≠ 0}), ?_, ?_⟩
    · intro i x _ hx y _ hy
      refine of_not_not fun hRz => ?_
      have hM0 : M x y = 0 := h0 x y hRz
      rw [← hTU, Matrix.mul_apply] at hM0
      have := single_le_sum (f := fun k => T x k * U k y) (fun _ _ => Nat.zero_le _) (mem_univ i)
      have := Nat.mul_pos (Nat.pos_of_ne_zero hx) (Nat.pos_of_ne_zero hy)
      omega
    · intro x _ y _ hRnz
      have hM1 : ∑ k : Fin r, T x k * U k y = 1 := by
        rw [← Matrix.mul_apply, hTU]
        exact h1 x y hRnz
      obtain ⟨k, hk, huniq⟩ := existsUnique_ne_zero_of_sum_eq_one hM1
      exact ⟨k, mul_ne_zero_iff.1 hk, fun k' hk' => huniq k' (mul_ne_zero hk'.1 hk'.2)⟩
  · refine le_partitionCoverNumber_iff.2 fun r C hC => ?_
    let T : Matrix X (Fin r) ℕ := fun x i => if x ∈ (C i).1 then 1 else 0
    let U : Matrix (Fin r) Y ℕ := fun i y => if y ∈ (C i).2 then 1 else 0
    let M : Matrix X Y ℕ := T * U
    have hM1 (x : X) (y : Y) (hRnz : ¬R x y (!z)) : M x y = 1 := by
      obtain ⟨i₀, ⟨hx₀, hy₀⟩, huniq⟩ := hC.2 x ⟨⟩ y ⟨⟩ hRnz
      dsimp only [M]
      rw [Matrix.mul_apply, sum_eq_single i₀]
      · simp only [T, U, hx₀, hy₀, ↓reduceIte, mul_one]
      · intro i _ hi
        by_cases hx : x ∈ (C i).1
        · simp only [T, U, hx, show y ∉ (C i).2 from fun hy => hi (huniq i ⟨hx, hy⟩),
            ↓reduceIte, mul_zero]
        · simp only [T, hx, ↓reduceIte, zero_mul]
      · exact fun h => absurd (mem_univ i₀) h
    have hM0 (x : X) (y : Y) (hRz : ¬R x y z) : M x y = 0 := by
      dsimp only [M]
      rw [Matrix.mul_apply]
      refine sum_eq_zero fun i _ => ?_
      by_cases hx : x ∈ (C i).1
      · simp only [T, U, hx, show y ∉ (C i).2 from fun hy => hRz (hC.1 i x ⟨⟩ hx y ⟨⟩ hy),
          ↓reduceIte, mul_zero]
      · simp only [T, hx, ↓reduceIte, zero_mul]
    have hfac : M.HasNonnegFactorization (Fin r) :=
      ⟨T, U, fun _ _ => Nat.zero_le _, fun _ _ => Nat.zero_le _, rfl⟩
    exact iInf_le_of_le M (iInf_le_of_le ⟨hM1, hM0⟩
      (hfac.nonnegRank_le.trans_eq (by rw [Fintype.card_fin])))

end Nondeterministic

end Cslib.Communication
