/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.PMF.Expect
public import CslibFrontier.Probability.PMF.Uniform
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Log
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Multi-Round Unit-Circle Dynamic Matching

This file formalizes the multi-round consistent-hashing dynamic matching scheme of Tianxiao Li,
Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic Dictionary with Subconstant Wasted Bits per
Key* ([LiLiangYuZhou2024, Section 3.1, Problem 3.1, Algorithm 1, Lemma 3.2, and Claims 3.3–3.4];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF pp. 6–9 / printed pp. 5–8), building
on consistent hashing on the unit circle ([KargerLehmanLeightonPanigrahyLevineLewin1997]) and
memoryless worker-task assignment ([BergerKuszmaulPolakTidorWein2022]).

Given a key-ID (ball) universe `Fin U'` and a slot (bin) universe `Fin n'` (`n' ≤ U'`), a matching
scheme `h : Scheme U' n'` consists of `U'` permutations on `Fin (U' + n')` (matching the
independent Fisher–Yates permutations sampled at initialization on the Word RAM). In round `i`, all
remaining balls `A_i ⊆ Fin U'` and bins `B_i ⊆ Fin n'` are placed on the discrete circle
`Fin (U' + n')` via `h i`; each ball `a ∈ A_i` whose clockwise-next occupied circle position belongs
to a bin `b ∈ B_i` is matched to `b`, and both `a` and `b` are removed before round `i + 1`.

Because `h` is fixed in advance, the resulting assignment `matching h A` (for `B = Finset.univ` of
all `n'` slots, or more generally `matchOptOn h A B` for any `B` with `A.card ≤ B.card`) depends
solely on `h` and the current active set `A`. For any fixed `h` with `T := rounds h A`, when active
cardinality stays `≤ n'`, a single insertion or deletion changes at most `2 * (T + 1)` ball
assignments ([LiLiangYuZhou2024, Claim 3.4]), and an atomic replacement `insert y (A.erase x)`
changes at most `4 * T + 6` assignments ([LiLiangYuZhou2024, Section 5.2 via Claim 3.4]). Under
uniform independent permutations (`schemePMF`), the expected round count is at most
`⌈log₂ |A|⌉ + 2 = O(log (max |A| 2))` ([LiLiangYuZhou2024, Claim 3.3]), giving expected
`O(log (max |A| 2))` single-update relocation cost ([LiLiangYuZhou2024, Lemma 3.2]).

## Scope note

This module supplies the pure mathematical dynamic-matching primitive for the
large-parameter-regime dynamic dictionary of [LiLiangYuZhou2024, Section 5]. Word-RAM Fisher–Yates
permutation sampling, precomputed lookup-table evaluation, variable-length `B`-way word/bit
adapters (Section 3.3), adapter trees (Section 4), strong history independence, dynamic resizing,
and super-polynomial key universes are not formalized here.

## Main definitions

* `Cslib.DataStructure.Dictionary.DynamicMatching.RoundPerm`, `Scheme`, `schemePMF`: single-round
  permutation on `Fin (U' + n')`, `U'`-round matching scheme, and uniform distribution on schemes.
* `Cslib.DataStructure.Dictionary.DynamicMatching.roundMatchOpt`, `roundStep`, `stateAt`,
  `roundsOn`, `rounds`, `matchOptOn`, `matchOpt`, `matching`, `relocDist`: Algorithm 1 round
  transition, round count `T`, partial assignment `Fin U' → Option (Fin n')`, canonical injection
  `A ↪ Fin n'`, and ball-relocation distance `Δ`.

## Main results

* `card_balls_roundStep_lt`, `stateAt_balls_eq_empty`, `roundsOn_le_card`, `rounds_le_card`,
  `matchOptOn_isSome_iff`, `matchOptOn_injective`, `matchOpt_isSome_iff`, `matchOpt_injective`,
  `matching_apply`: termination within `A.card` rounds and canonical injection properties.
* `expect_roundsOn_le`, `expect_rounds_le`: expected round bound
  `𝔼[T] ≤ ⌈log₂ |A|⌉ + 2 ≤ 3 * ⌈log₂ (max |A| 2)⌉` ([LiLiangYuZhou2024, Claim 3.3]).
* `expect_le_of_le_add_mul_rounds`: a cost bounded by `a + b * T` has expectation at most
  `(a + 3 b) * ⌈log₂ (max |A| 2)⌉`.
* `relocDist_insert_le`, `relocDist_delete_le`, `relocDist_replace_le`,
  `expect_relocDist_insert_le`, `expect_relocDist_delete_le`, `expect_relocDist_replace_le`:
  deterministic `O(T)` and expected `O(log (max |A| 2))` relocation bounds
  ([LiLiangYuZhou2024, Claim 3.4 and Lemma 3.2]).

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
* [D. R. Karger, E. Lehman, F. T. Leighton, R. Panigrahy, M. S. Levine, and D. Lewin,
  *Consistent Hashing and Random Trees: Distributed Caching Protocols for Relieving Hot Spots on
  the World Wide Web*][KargerLehmanLeightonPanigrahyLevineLewin1997]
* [A. Berger, W. Kuszmaul, A. Polak, J. Tidor, and N. Wein,
  *Memoryless Worker-Task Assignment with Polylogarithmic Switching
  Cost*][BergerKuszmaulPolakTidorWein2022]
-/

public section

namespace Cslib.DataStructure.Dictionary.DynamicMatching

open Finset
open scoped symmDiff BigOperators ENNReal

/-- Single-round permutation on the combined universe `Fin (U' + n')` of `U'` balls and `n'`
bins. -/
abbrev RoundPerm (U' n' : ℕ) := Equiv.Perm (Fin (U' + n'))

/-- Predetermined `U'`-round dynamic matching scheme (`Algorithm 1`, line 1). -/
abbrev Scheme (U' n' : ℕ) := Fin U' → RoundPerm U' n'

/-- Uniform distribution over `U'` independent permutations on `Fin (U' + n')`. -/
@[expose]
noncomputable def schemePMF (U' n' : ℕ) : PMF (Scheme U' n') :=
  Cslib.Probability.PMF.uniformOfFintype (Scheme U' n')

theorem schemePMF_eq_uniformOfFintype (U' n' : ℕ) :
    schemePMF U' n' = Cslib.Probability.PMF.uniformOfFintype (Scheme U' n') :=
  rfl

/-- Embed ball `a : Fin U'` into the combined item space `Fin (U' + n')`. -/
private def ballItem {U' : ℕ} (n' : ℕ) (a : Fin U') : Fin (U' + n') :=
  Fin.castAdd n' a

/-- Embed bin `b : Fin n'` into the combined item space `Fin (U' + n')`. -/
private def binItem (U' : ℕ) {n' : ℕ} (b : Fin n') : Fin (U' + n') :=
  Fin.natAdd U' b

private theorem ballItem_injective (U' n' : ℕ) : Function.Injective (ballItem (U' := U') n') :=
  Fin.castAdd_injective U' n'

private theorem binItem_injective (U' n' : ℕ) : Function.Injective (binItem U' (n' := n')) :=
  Fin.natAdd_injective n' U'

@[simp]
private theorem ballItem_ne_binItem {U' n' : ℕ} (a : Fin U') (b : Fin n') :
    ballItem n' a ≠ binItem U' b := fun h => by
  have := congrArg Fin.val h; simp only [ballItem, binItem, Fin.val_castAdd, Fin.val_natAdd] at this
  omega

/-- Test whether a combined item `z : Fin (U' + n')` is a bin `binItem U' b`. -/
def asBin? {U' n' : ℕ} (z : Fin (U' + n')) : Option (Fin n') :=
  if h : U' ≤ z.val then some ⟨z.val - U', by omega⟩ else none

@[simp]
private theorem asBin?_ballItem {U' n' : ℕ} (a : Fin U') : asBin? (ballItem n' a) = none := by
  simp [asBin?, ballItem, Nat.not_le_of_gt a.isLt]

@[simp]
private theorem asBin?_binItem {U' n' : ℕ} (b : Fin n') : asBin? (binItem U' b) = some b := by
  ext; simp [asBin?, binItem]

private theorem asBin?_eq_some_iff {U' n' : ℕ} {z : Fin (U' + n')} {b : Fin n'} :
    asBin? z = some b ↔ z = binItem U' b :=
  ⟨fun h => by
    dsimp only [asBin?] at h; split_ifs at h with hle
    exact Fin.ext (by
      have hb := congrArg Fin.val (Option.some.inj h)
      simp only [binItem, Fin.val_natAdd] at hb ⊢; omega),
   fun h => h ▸ asBin?_binItem b⟩

/-- Combined active item set `A ⊕ B` inside `Fin (U' + n')`. -/
private def activeItems {U' n' : ℕ} (A : Finset (Fin U')) (B : Finset (Fin n')) :
    Finset (Fin (U' + n')) :=
  A.map ⟨ballItem n', ballItem_injective U' n'⟩ ∪ B.map ⟨binItem U', binItem_injective U' n'⟩

@[simp]
private theorem ballItem_mem_activeItems {U' n' : ℕ} {A : Finset (Fin U')} {B : Finset (Fin n')}
    {a : Fin U'} : ballItem n' a ∈ activeItems A B ↔ a ∈ A := by
  simp only [activeItems, mem_union, mem_map, Function.Embedding.coeFn_mk]
  exact ⟨fun | .inl ⟨_, ha, h⟩ => ballItem_injective U' n' h ▸ ha
             | .inr ⟨b, _, h⟩ => absurd h.symm (ballItem_ne_binItem a b),
         fun ha => .inl ⟨a, ha, rfl⟩⟩

@[simp]
private theorem binItem_mem_activeItems {U' n' : ℕ} {A : Finset (Fin U')} {B : Finset (Fin n')}
    {b : Fin n'} : binItem U' b ∈ activeItems A B ↔ b ∈ B := by
  simp only [activeItems, mem_union, mem_map, Function.Embedding.coeFn_mk]
  exact ⟨fun | .inl ⟨a, _, h⟩ => absurd h (ballItem_ne_binItem a b)
             | .inr ⟨_, hb, h⟩ => binItem_injective U' n' h ▸ hb,
         fun hb => .inr ⟨b, hb, rfl⟩⟩

private theorem mem_activeItems_iff {U' n' : ℕ} {A : Finset (Fin U')} {B : Finset (Fin n')}
    {z : Fin (U' + n')} :
    z ∈ activeItems A B ↔
      (∃ a ∈ A, z = ballItem n' a) ∨ (∃ b ∈ B, z = binItem U' b) := by
  simp only [activeItems, mem_union, mem_map, Function.Embedding.coeFn_mk, eq_comm]

private theorem card_activeItems {U' n' : ℕ} (A : Finset (Fin U')) (B : Finset (Fin n')) :
    (activeItems A B).card = A.card + B.card := by
  rw [activeItems, card_union_of_disjoint, card_map, card_map]
  refine disjoint_left.mpr fun z hA hB => ?_
  obtain ⟨a, _, rfl⟩ := mem_map.mp hA; obtain ⟨b, _, h⟩ := mem_map.mp hB
  exact ballItem_ne_binItem a b h.symm

/-- With no active item there are no balls and no bins. -/
private theorem eq_empty_of_not_nonempty_activeItems {U' n' : ℕ} {A : Finset (Fin U')}
    {B : Finset (Fin n')} (h : ¬(activeItems A B).Nonempty) : A = ∅ ∧ B = ∅ := by
  have := card_activeItems A B
  rw [not_nonempty_iff_eq_empty.mp h, card_empty] at this
  exact ⟨card_eq_zero.mp (by omega), card_eq_zero.mp (by omega)⟩

/-! ### Clockwise successor on a finite circle subset -/

/-- Clockwise successor of `p` inside `P : Finset (Fin M)`: the smallest element of `P` strictly
greater than `p`, wrapping around to `P.min'` when `p` is at or above all elements of `P`. -/
private def clockwiseNextPos {M : ℕ} (P : Finset (Fin M)) (p : Fin M) : Fin M :=
  let gt := P.filter (p < ·)
  if hgt : gt.Nonempty then gt.min' hgt
  else if hP : P.Nonempty then P.min' hP
  else p

private theorem clockwiseNextPos_mem {M : ℕ} {P : Finset (Fin M)} (hP : P.Nonempty) (p : Fin M) :
    clockwiseNextPos P p ∈ P := by
  dsimp only [clockwiseNextPos]
  split_ifs with hgt
  · exact (mem_filter.mp (min'_mem _ hgt)).1
  · exact min'_mem P hP

private theorem clockwiseNextPos_eq_imp_le {M : ℕ} {P : Finset (Fin M)}
    {p₁ p₂ : Fin M} (hp₁ : p₁ ∈ P) (hp₂ : p₂ ∈ P)
    (heq : clockwiseNextPos P p₁ = clockwiseNextPos P p₂) : p₁ ≤ p₂ := by
  by_contra hlt; replace hlt := lt_of_not_ge hlt
  have hgt₂ : (P.filter (p₂ < ·)).Nonempty := ⟨p₁, mem_filter.mpr ⟨hp₁, hlt⟩⟩
  have hP : P.Nonempty := ⟨p₂, hp₂⟩
  dsimp only [clockwiseNextPos] at heq
  simp only [hgt₂, hP, ↓reduceDIte] at heq
  split_ifs at heq with hgt₁
  · exact ((mem_filter.mp (min'_mem _ hgt₁)).2.trans_le
      (heq ▸ min'_le _ p₁ (mem_filter.mpr ⟨hp₁, hlt⟩))).false
  · exact ((mem_filter.mp (min'_mem _ hgt₂)).2.trans_le
      (heq ▸ min'_le P p₂ hp₂)).false

private theorem clockwiseNextPos_injective {M : ℕ} (P : Finset (Fin M)) :
    Set.InjOn (clockwiseNextPos P) (P : Set (Fin M)) := fun _ hp₁ _ hp₂ heq =>
  le_antisymm (clockwiseNextPos_eq_imp_le hp₁ hp₂ heq)
    (clockwiseNextPos_eq_imp_le hp₂ hp₁ heq.symm)

private theorem exists_clockwiseNextPos_notMem {M : ℕ} {P Q : Finset (Fin M)}
    (hQ : Q.Nonempty) (hdiff : (P \ Q).Nonempty) :
    ∃ q ∈ Q, clockwiseNextPos P q ∉ Q := by
  by_contra hclosed; push Not at hclosed
  by_cases habove : ((P \ Q).filter (Q.min' hQ < ·)).Nonempty
  · set b := ((P \ Q).filter (Q.min' hQ < ·)).min' habove
    obtain ⟨hbPQ, hmin_lt⟩ := mem_filter.mp (min'_mem _ habove)
    obtain ⟨hbP, hbnotQ⟩ := mem_sdiff.mp hbPQ
    have hQlt : (Q.filter (· < b)).Nonempty := ⟨Q.min' hQ, mem_filter.mpr ⟨min'_mem Q hQ, hmin_lt⟩⟩
    set q := (Q.filter (· < b)).max' hQlt
    obtain ⟨hqQ, hqb⟩ := mem_filter.mp (max'_mem _ hQlt)
    have hgt : (P.filter (q < ·)).Nonempty := ⟨b, mem_filter.mpr ⟨hbP, hqb⟩⟩
    have hnext_eq : clockwiseNextPos P q = (P.filter (q < ·)).min' hgt := by
      simp [clockwiseNextPos, hgt]
    have hnext_lt : clockwiseNextPos P q < b := lt_of_le_of_ne
      (hnext_eq ▸ min'_le _ b (mem_filter.mpr ⟨hbP, hqb⟩)) fun h =>
        hbnotQ (by convert hclosed q hqQ using 1; exact h.symm)
    exact ((hnext_eq ▸ (mem_filter.mp (min'_mem _ hgt)).2).trans_le
      (le_max' _ _ (mem_filter.mpr ⟨hclosed q hqQ, hnext_lt⟩))).false
  · rcases hdiff with ⟨b₀, hb₀⟩
    have hall_lt : ∀ b ∈ P \ Q, b < Q.min' hQ := fun b hb =>
      lt_of_le_of_ne (le_of_not_gt fun h => habove ⟨b, mem_filter.mpr ⟨hb, h⟩⟩)
        fun h => (mem_sdiff.mp hb).2 (h ▸ min'_mem Q hQ)
    have hP : P.Nonempty := ⟨b₀, (mem_sdiff.mp hb₀).1⟩
    have hmin_notQ : P.min' hP ∉ Q := fun hm =>
      ((min'_le Q _ hm).trans_lt ((min'_le P b₀ (mem_sdiff.mp hb₀).1).trans_lt
        (hall_lt b₀ hb₀))).false
    set qMax := Q.max' hQ
    have hgt_empty : ¬(P.filter (qMax < ·)).Nonempty := by
      rintro ⟨y, hy⟩; obtain ⟨hyP, hlt⟩ := mem_filter.mp hy
      by_cases hyQ : y ∈ Q
      · exact (hlt.trans_le (le_max' Q y hyQ)).false
      · exact (((min'_le Q _ (max'_mem Q hQ)).trans_lt hlt).trans
          (hall_lt y (mem_sdiff.mpr ⟨hyP, hyQ⟩))).false
    have hnext : clockwiseNextPos P qMax = P.min' hP := by
      simp only [clockwiseNextPos, hgt_empty, hP, ↓reduceDIte]
    exact hmin_notQ (hnext ▸ hclosed _ (max'_mem Q hQ))

/-- Inserting one new point `pStar ∉ P` into a nonempty circle subset `P` splices `pStar`
immediately after a unique predecessor `x₀ ∈ P`, leaving `clockwiseNextPos` unchanged on every
`x ∈ P \ {x₀}`. -/
private theorem exists_insert_clockwiseNextPos {M : ℕ} {P : Finset (Fin M)} (hP : P.Nonempty)
    {pStar : Fin M} (hp : pStar ∉ P) :
    ∃ x₀ ∈ P,
      clockwiseNextPos (insert pStar P) x₀ = pStar ∧
      clockwiseNextPos (insert pStar P) pStar = clockwiseNextPos P x₀ ∧
      ∀ x ∈ P, x ≠ x₀ → clockwiseNextPos (insert pStar P) x = clockwiseNextPos P x := by
  have hP' : (insert pStar P).Nonempty := insert_nonempty pStar P
  by_cases hlt_ne : (P.filter (· < pStar)).Nonempty
  · set x₀ := (P.filter (· < pStar)).max' hlt_ne
    obtain ⟨hx₀_P, hx₀_lt⟩ := mem_filter.mp (max'_mem _ hlt_ne)
    have hgap : ∀ z ∈ P, x₀ < z → pStar < z := fun z hz hxz =>
      lt_of_le_of_ne (le_of_not_gt fun hzp =>
        (hxz.trans_le (le_max' _ z (mem_filter.mpr ⟨hz, hzp⟩))).false) fun h => hp (h ▸ hz)
    have hmin_eq : (insert pStar P).min' hP' = P.min' hP :=
      (min'_insert pStar P hP).trans (min_eq_right ((min'_le P x₀ hx₀_P).trans hx₀_lt.le))
    refine ⟨x₀, hx₀_P, ?_, ?_, fun x hx hxne => ?_⟩
    · have hfilt : (insert pStar P).filter (x₀ < ·) = insert pStar (P.filter (x₀ < ·)) := by
        rw [filter_insert, ite_eq_left_iff.mpr fun h => absurd hx₀_lt h]
      simp only [clockwiseNextPos, hfilt, insert_nonempty, ↓reduceDIte]
      refine le_antisymm (min'_le _ pStar (mem_insert_self _ _)) (le_min' _ _ _ fun z hz => ?_)
      rcases mem_insert.mp hz with rfl | hzP
      · exact le_rfl
      · exact (hgap z (mem_filter.mp hzP).1 (mem_filter.mp hzP).2).le
    · have hfilt_eq : (insert pStar P).filter (pStar < ·) = P.filter (x₀ < ·) := by
        ext z; simp only [filter_insert, lt_irrefl, ↓reduceIte, mem_filter]
        exact ⟨fun ⟨hz, hpz⟩ => ⟨hz, hx₀_lt.trans hpz⟩, fun ⟨hz, hxz⟩ => ⟨hz, hgap z hz hxz⟩⟩
      dsimp only [clockwiseNextPos]; simp only [hfilt_eq]
      split_ifs <;> [rfl; exact hmin_eq]
    · rcases lt_or_gt_of_ne hxne with hxx₀ | hx₀x
      · have hgtP : (P.filter (x < ·)).Nonempty := ⟨x₀, mem_filter.mpr ⟨hx₀_P, hxx₀⟩⟩
        have hfilt : (insert pStar P).filter (x < ·) = insert pStar (P.filter (x < ·)) := by
          simp [filter_insert, hxx₀.trans hx₀_lt]
        simp only [clockwiseNextPos, hfilt, insert_nonempty, hgtP, ↓reduceDIte, min'_insert]
        exact min_eq_right ((min'_le _ x₀ (mem_filter.mpr ⟨hx₀_P, hxx₀⟩)).trans hx₀_lt.le)
      · have hfilt_eq : (insert pStar P).filter (x < ·) = P.filter (x < ·) := by
          simp [filter_insert, not_lt_of_ge (hgap x hx hx₀x).le]
        dsimp only [clockwiseNextPos]; simp only [hfilt_eq]
        split_ifs <;> [rfl; exact hmin_eq]
  · have hall_gt : ∀ z ∈ P, pStar < z := fun z hz =>
      lt_of_le_of_ne (le_of_not_gt fun hzp => hlt_ne ⟨z, mem_filter.mpr ⟨hz, hzp⟩⟩)
        fun h => hp (h ▸ hz)
    set x₀ := P.max' hP
    have hgt_empty : P.filter (x₀ < ·) = ∅ :=
      filter_eq_empty_iff.mpr fun z hz => not_lt_of_ge (le_max' P z hz)
    refine ⟨x₀, max'_mem P hP, ?_, ?_, fun x hx hxne => ?_⟩
    · have hfilt : (insert pStar P).filter (x₀ < ·) = ∅ := by
        simp only [filter_insert, not_lt_of_ge (hall_gt x₀ (max'_mem P hP)).le, ↓reduceIte,
          hgt_empty]
      simp only [clockwiseNextPos, hfilt, Finset.not_nonempty_empty, hP', ↓reduceDIte,
        min'_insert pStar P hP]
      exact min_eq_left (le_min' P hP pStar fun z hz => (hall_gt z hz).le)
    · have hfilt : (insert pStar P).filter (pStar < ·) = P := by
        simp [filter_insert, filter_true_of_mem hall_gt]
      simp only [clockwiseNextPos, hfilt, hgt_empty, Finset.not_nonempty_empty, hP, ↓reduceDIte]
    · have hgtP : (P.filter (x < ·)).Nonempty :=
        ⟨x₀, mem_filter.mpr ⟨max'_mem P hP, lt_of_le_of_ne (le_max' P x hx) hxne⟩⟩
      simp only [clockwiseNextPos, filter_insert, not_lt_of_ge (hall_gt x hx).le, ↓reduceIte,
        hgtP, ↓reduceDIte]

/-! ### Permuted item circle and single-round matching -/

/-- Clockwise next active item in `S : Finset (Fin (U' + n'))` after `z`, ordered along the circle
by permutation `π`. -/
private def nextItem {M : ℕ} (π : Equiv.Perm (Fin M)) (S : Finset (Fin M)) (z : Fin M) : Fin M :=
  π.symm (clockwiseNextPos (S.map π.toEmbedding) (π z))

private theorem nextItem_mem {M : ℕ} (π : Equiv.Perm (Fin M)) {S : Finset (Fin M)} (hS : S.Nonempty)
    (z : Fin M) : nextItem π S z ∈ S := by
  obtain ⟨w, hw, heq⟩ := mem_map.mp (clockwiseNextPos_mem (Finset.map_nonempty.mpr hS) (π z))
  dsimp only [nextItem]; rw [← heq]; simpa using hw

private theorem nextItem_injective {M : ℕ} (π : Equiv.Perm (Fin M)) (S : Finset (Fin M)) :
    Set.InjOn (nextItem π S) (S : Set (Fin M)) := fun _ hz₁ _ hz₂ heq =>
  π.injective <| clockwiseNextPos_injective _ (mem_map.mpr ⟨_, hz₁, rfl⟩)
    (mem_map.mpr ⟨_, hz₂, rfl⟩) (π.symm.injective heq)

private theorem exists_nextItem_notMem {M : ℕ} (π : Equiv.Perm (Fin M)) {S Q : Finset (Fin M)}
    (hQ : Q.Nonempty) (hdiff : (S \ Q).Nonempty) :
    ∃ q ∈ Q, nextItem π S q ∉ Q := by
  obtain ⟨b, hb⟩ := hdiff
  have hdiffP : (S.map π.toEmbedding \ Q.map π.toEmbedding).Nonempty :=
    ⟨π b, mem_sdiff.mpr ⟨mem_map.mpr ⟨b, (mem_sdiff.mp hb).1, rfl⟩,
      fun h => let ⟨_, hq, heq⟩ := mem_map.mp h; (mem_sdiff.mp hb).2 (π.injective heq ▸ hq)⟩⟩
  obtain ⟨_, hpQ, hpnot⟩ := exists_clockwiseNextPos_notMem (Finset.map_nonempty.mpr hQ) hdiffP
  obtain ⟨q, hq, rfl⟩ := mem_map.mp hpQ
  exact ⟨q, hq, fun h => hpnot (mem_map.mpr ⟨_, h, by simp [nextItem]⟩)⟩

private theorem exists_insert_nextItem {M : ℕ} (π : Equiv.Perm (Fin M)) {S : Finset (Fin M)}
    (hS : S.Nonempty) {zStar : Fin M} (hz : zStar ∉ S) :
    ∃ x₀ ∈ S,
      nextItem π (insert zStar S) x₀ = zStar ∧
      nextItem π (insert zStar S) zStar = nextItem π S x₀ ∧
      ∀ w ∈ S, w ≠ x₀ → nextItem π (insert zStar S) w = nextItem π S w := by
  have hpStar : π zStar ∉ S.map π.toEmbedding :=
    fun h => let ⟨_, hw, heq⟩ := mem_map.mp h; hz (π.injective heq ▸ hw)
  obtain ⟨_, hp₀, h1, h2, h3⟩ :=
    exists_insert_clockwiseNextPos (Finset.map_nonempty.mpr hS) hpStar
  obtain ⟨x₀, hx₀, rfl⟩ := mem_map.mp hp₀
  have hm := map_insert π.toEmbedding zStar S
  simp only [Equiv.coe_toEmbedding] at h1 h2 h3
  exact ⟨x₀, hx₀, by simp [nextItem, hm, h1], by simp [nextItem, hm, h2], fun w hw hne => by
    simp [nextItem, hm, h3 (π w) (mem_map.mpr ⟨w, hw, rfl⟩) (π.injective.ne hne)]⟩

/-- Swapping two active items `y₁, y₂ ∈ S \ {x}` on the right of `π` permutes `nextItem π S x` by
`Equiv.swap y₁ y₂` without changing the occupied circle set `S.map π`. -/
private theorem nextItem_mul_swap {M : ℕ} [DecidableEq (Fin M)] (π : Equiv.Perm (Fin M))
    {S : Finset (Fin M)} {x y₁ y₂ : Fin M}
    (hy₁ : y₁ ∈ S) (hy₂ : y₂ ∈ S) (hx₁ : x ≠ y₁) (hx₂ : x ≠ y₂) :
    nextItem (π * Equiv.swap y₁ y₂) S x = (Equiv.swap y₁ y₂) (nextItem π S x) := by
  have hswap : ∀ {z}, z ∈ S → Equiv.swap y₁ y₂ z ∈ S := fun {z} hz => by
    rw [Equiv.swap_apply_def]; split_ifs <;> assumption
  have hmap : S.map (π * Equiv.swap y₁ y₂).toEmbedding = S.map π.toEmbedding := by
    ext p; simp only [mem_map, Equiv.coe_toEmbedding, Equiv.Perm.mul_apply]
    exact ⟨fun ⟨z, hz, h⟩ => ⟨_, hswap hz, h⟩, fun ⟨z, hz, h⟩ => ⟨_, hswap hz, by simpa using h⟩⟩
  dsimp only [nextItem]
  rw [hmap, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hx₁ hx₂,
    Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap]

/-- Single-round match attempt (`Algorithm 1`, lines 7–9): ball `a` matches to bin `b` iff `a ∈ A`
and the clockwise-next active item in `activeItems A B` under `π` is `binItem U' b`. -/
def roundMatchOpt {U' n' : ℕ} (π : RoundPerm U' n') (A : Finset (Fin U')) (B : Finset (Fin n'))
    (a : Fin U') : Option (Fin n') :=
  if a ∈ A then asBin? (nextItem π (activeItems A B) (ballItem n' a)) else none

/-- Single-round state update (`Algorithm 1`, lines 5–10): remove matched balls from `A` and
matched bins from `B`. -/
def roundStep {U' n' : ℕ} (π : RoundPerm U' n') (AB : Finset (Fin U') × Finset (Fin n')) :
    Finset (Fin U') × Finset (Fin n') :=
  let A := AB.1
  let B := AB.2
  let matchedBalls := A.filter fun a => (roundMatchOpt π A B a).isSome
  let matchedBins := B.filter fun b => ∃ a ∈ A, roundMatchOpt π A B a = some b
  (A \ matchedBalls, B \ matchedBins)

private theorem roundMatchOpt_mem_bins {U' n' : ℕ} {π : RoundPerm U' n'} {A : Finset (Fin U')}
    {B : Finset (Fin n')} {a : Fin U'} {b : Fin n'} (hm : roundMatchOpt π A B a = some b) :
    a ∈ A ∧ b ∈ B := by
  dsimp only [roundMatchOpt] at hm; split_ifs at hm with ha
  exact ⟨ha, binItem_mem_activeItems.mp <| asBin?_eq_some_iff.mp hm ▸
    nextItem_mem π ⟨ballItem n' a, ballItem_mem_activeItems.mpr ha⟩ _⟩

private theorem roundMatchOpt_injective {U' n' : ℕ} (π : RoundPerm U' n') (A : Finset (Fin U'))
    (B : Finset (Fin n')) {a₁ a₂ : Fin U'} {b : Fin n'}
    (h₁ : roundMatchOpt π A B a₁ = some b) (h₂ : roundMatchOpt π A B a₂ = some b) :
    a₁ = a₂ := by
  have ha₁ := (roundMatchOpt_mem_bins h₁).1; have ha₂ := (roundMatchOpt_mem_bins h₂).1
  simp only [roundMatchOpt, ha₁, ha₂, ↓reduceIte] at h₁ h₂
  exact ballItem_injective U' n' <| nextItem_injective π (activeItems A B)
    (ballItem_mem_activeItems.mpr ha₁) (ballItem_mem_activeItems.mpr ha₂)
    ((asBin?_eq_some_iff.mp h₁).trans (asBin?_eq_some_iff.mp h₂).symm)

private theorem card_balls_le_card_bins_roundStep {U' n' : ℕ} (π : RoundPerm U' n')
    {A : Finset (Fin U')} {B : Finset (Fin n')} (hle : A.card ≤ B.card) :
    (roundStep π (A, B)).1.card ≤ (roundStep π (A, B)).2.card := by
  have hcard : (A.filter fun a => (roundMatchOpt π A B a).isSome).card =
      (B.filter fun b => ∃ a ∈ A, roundMatchOpt π A B a = some b).card := by
    refine card_bij (fun a ha => (roundMatchOpt π A B a).get (mem_filter.mp ha).2)
      (fun a ha => mem_filter.mpr ⟨(roundMatchOpt_mem_bins (Option.some_get _).symm).2,
        a, (mem_filter.mp ha).1, (Option.some_get _).symm⟩)
      (fun a₁ ha₁ a₂ ha₂ heq => roundMatchOpt_injective π A B
        ((Option.some_get _).symm.trans (congrArg some heq)) (Option.some_get _).symm)
      fun b hb => let ⟨a, ha, hab⟩ := (mem_filter.mp hb).2
        ⟨a, mem_filter.mpr ⟨ha, by simp [hab]⟩, by simp [hab]⟩
  dsimp only [roundStep]
  rw [card_sdiff_of_subset (filter_subset _ A), card_sdiff_of_subset (filter_subset _ B), hcard]
  exact Nat.sub_le_sub_right hle _

/-- Every round with `A.Nonempty` and `B.Nonempty` matches at least one ball (`Algorithm 1`
termination property, [LiLiangYuZhou2024, Section 3.1]). -/
theorem card_balls_roundStep_lt {U' n' : ℕ} (π : RoundPerm U' n')
    {A : Finset (Fin U')} {B : Finset (Fin n')} (hA : A.Nonempty) (hB : B.Nonempty) :
    (roundStep π (A, B)).1.card < A.card := by
  set Q := A.map ⟨ballItem n', ballItem_injective U' n'⟩
  have hdiff : (activeItems A B \ Q).Nonempty := by
    rcases hB with ⟨b, hb⟩
    refine ⟨binItem U' b, mem_sdiff.mpr ⟨binItem_mem_activeItems.mpr hb, fun hm => ?_⟩⟩
    obtain ⟨a, _, heq⟩ := mem_map.mp hm; exact ballItem_ne_binItem a b heq
  obtain ⟨_, hqQ, hnot⟩ := exists_nextItem_notMem π (Finset.map_nonempty.mpr hA) hdiff
  obtain ⟨a, haA, rfl⟩ := mem_map.mp hqQ
  rcases mem_activeItems_iff.mp (nextItem_mem π ⟨_, ballItem_mem_activeItems.mpr haA⟩
      (ballItem n' a)) with ⟨a', ha', heq⟩ | ⟨b, _, heq⟩
  · exact absurd (heq ▸ mem_map.mpr ⟨a', ha', rfl⟩) hnot
  · have ha_in : a ∈ A.filter fun x => (roundMatchOpt π A B x).isSome :=
      mem_filter.mpr ⟨haA, by simp [roundMatchOpt, haA, heq]⟩
    exact card_lt_card (sdiff_ssubset (filter_subset _ A) ⟨a, ha_in⟩)

/-! ### Multi-round execution, canonical injection, and round count -/

/-- Remaining `(A_i, B_i)` state just before round `i` (0-indexed) when running `Algorithm 1` on
`(A, B)` under scheme `h`. -/
def stateAt {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U')) (B : Finset (Fin n')) :
    ℕ → Finset (Fin U') × Finset (Fin n')
  | 0 => (A, B)
  | i + 1 =>
    if hi : i < U' then roundStep (h ⟨i, hi⟩) (stateAt h A B i) else stateAt h A B i

/-- Partial matching accumulated during the first `k` rounds of `Algorithm 1`. -/
private def matchAux {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U')) (B : Finset (Fin n')) :
    ℕ → Fin U' → Option (Fin n')
  | 0, _ => none
  | i + 1, a =>
    match matchAux h A B i a with
    | some b => some b
    | none =>
      if hi : i < U' then roundMatchOpt (h ⟨i, hi⟩) (stateAt h A B i).1 (stateAt h A B i).2 a
      else none

/-- Partial matching `σ_{A, B} : Fin U' → Option (Fin n')` after all `U'` rounds of `Algorithm 1`
on `(A, B)`. -/
def matchOptOn {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U')) (B : Finset (Fin n')) :
    Fin U' → Option (Fin n') :=
  matchAux h A B U'

/-- Partial matching `σ_A : Fin U' → Option (Fin n')` against all `n'` slots (`B = Finset.univ`). -/
def matchOpt {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U')) : Fin U' → Option (Fin n') :=
  matchOptOn h A Finset.univ

/-- Number of active rounds `T` executed by `Algorithm 1` on `(A, B)`. -/
def roundsOn {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U')) (B : Finset (Fin n')) : ℕ :=
  ((Finset.range U').filter fun i => (stateAt h A B i).1.Nonempty).card

/-- Number of active rounds `T` executed by `Algorithm 1` on `(A, Finset.univ)`. -/
def rounds {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U')) : ℕ :=
  roundsOn h A Finset.univ

/-- Ball-relocation distance `Δ(σ, σ') = #{a : Fin U' | σ a ≠ σ' a}` (`Problem 3.1`,
[LiLiangYuZhou2024, Section 3.1]). -/
@[expose]
def relocDist {U' n' : ℕ} (σ σ' : Fin U' → Option (Fin n')) : ℕ :=
  (Finset.univ.filter fun a => σ a ≠ σ' a).card

theorem relocDist_self {U' n' : ℕ} (σ : Fin U' → Option (Fin n')) : relocDist σ σ = 0 := by
  simp [relocDist]

theorem relocDist_comm {U' n' : ℕ} (σ σ' : Fin U' → Option (Fin n')) :
    relocDist σ σ' = relocDist σ' σ := by
  simp [relocDist, ne_comm]

theorem relocDist_triangle {U' n' : ℕ} (σ₁ σ₂ σ₃ : Fin U' → Option (Fin n')) :
    relocDist σ₁ σ₃ ≤ relocDist σ₁ σ₂ + relocDist σ₂ σ₃ := by
  refine (card_le_card fun a ha => ?_).trans (card_union_le _ _)
  simp only [mem_filter, mem_univ, true_and, mem_union] at ha ⊢
  by_contra h; push Not at h; exact ha (h.1.trans h.2)

private theorem stateAt_balls_subset {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U'))
    (B : Finset (Fin n')) (i : ℕ) : (stateAt h A B i).1 ⊆ A := by
  induction i with
  | zero => exact Subset.rfl
  | succ i ih => dsimp only [stateAt]; split_ifs <;> [exact sdiff_subset.trans ih; exact ih]

private theorem stateAt_bins_subset {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U'))
    (B : Finset (Fin n')) (i : ℕ) : (stateAt h A B i).2 ⊆ B := by
  induction i with
  | zero => exact Subset.rfl
  | succ i ih => dsimp only [stateAt]; split_ifs <;> [exact sdiff_subset.trans ih; exact ih]

private theorem stateAt_balls_mono {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U'))
    (B : Finset (Fin n')) {i j : ℕ} (hij : i ≤ j) :
    (stateAt h A B j).1 ⊆ (stateAt h A B i).1 := by
  induction j with
  | zero => exact Nat.le_zero.mp hij ▸ Subset.rfl
  | succ j ih =>
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact Subset.rfl
    · refine Subset.trans ?_ (ih (Nat.lt_succ_iff.mp hlt))
      dsimp only [stateAt]; split_ifs <;> [exact sdiff_subset; exact Subset.rfl]

private theorem card_balls_le_card_bins_stateAt {U' n' : ℕ} (h : Scheme U' n')
    {A : Finset (Fin U')} {B : Finset (Fin n')} (hle : A.card ≤ B.card) (i : ℕ) :
    (stateAt h A B i).1.card ≤ (stateAt h A B i).2.card := by
  induction i with
  | zero => exact hle
  | succ i ih =>
    dsimp only [stateAt]; split_ifs with hi
    · exact card_balls_le_card_bins_roundStep (h ⟨i, hi⟩) ih
    · exact ih

private theorem roundStep_empty_balls {U' n' : ℕ} (π : RoundPerm U' n')
    (B : Finset (Fin n')) : roundStep π (∅, B) = (∅, B) := by ext <;> simp [roundStep]

private theorem card_stateAt_balls_succ_le_pred {U' n' : ℕ} (h : Scheme U' n')
    {A : Finset (Fin U')} {B : Finset (Fin n')} (hle : A.card ≤ B.card)
    {i : ℕ} (hi : i < U') :
    (stateAt h A B (i + 1)).1.card ≤ (stateAt h A B i).1.card - 1 := by
  simp only [stateAt, hi, ↓reduceDIte]
  by_cases hne : (stateAt h A B i).1.Nonempty
  · have hlt := card_balls_roundStep_lt (h ⟨i, hi⟩) hne
      (card_pos.mp <| lt_of_lt_of_le (card_pos.mpr hne) (card_balls_le_card_bins_stateAt h hle i))
    rw [Prod.mk.eta] at hlt; omega
  · have he : (stateAt h A B i).1 = ∅ := not_nonempty_iff_eq_empty.mp hne
    simp [roundStep, he]

private theorem card_stateAt_balls_le_sub {U' n' : ℕ} (h : Scheme U' n')
    {A : Finset (Fin U')} {B : Finset (Fin n')} (hle : A.card ≤ B.card) {i : ℕ} (hi : i ≤ U') :
    (stateAt h A B i).1.card ≤ A.card - i := by
  induction i with
  | zero => simp [stateAt]
  | succ i ih =>
    have := ih (Nat.le_of_succ_le hi)
    have := card_stateAt_balls_succ_le_pred h hle (Nat.lt_of_succ_le hi)
    omega

/-- `Algorithm 1` matches all balls within `A.card` rounds whenever `A.card ≤ B.card`. -/
theorem stateAt_balls_eq_empty {U' n' : ℕ} (h : Scheme U' n')
    {A : Finset (Fin U')} {B : Finset (Fin n')} (hle : A.card ≤ B.card)
    {i : ℕ} (hi : A.card ≤ i) : (stateAt h A B i).1 = ∅ := by
  have h0 : (stateAt h A B A.card).1 = ∅ := card_eq_zero.mp <| Nat.le_zero.mp <|
    Nat.sub_self A.card ▸ card_stateAt_balls_le_sub h hle (by simpa using A.card_le_univ)
  exact subset_empty.mp (h0 ▸ stateAt_balls_mono h A B hi)

private theorem roundsOn_le_of_stateAt_balls_eq_empty {U' n' : ℕ} (h : Scheme U' n')
    {A : Finset (Fin U')} {B : Finset (Fin n')} {k : ℕ}
    (hk : (stateAt h A B k).1 = ∅) : roundsOn h A B ≤ k :=
  (card_le_card fun i hi => mem_range.mpr <| by_contra fun hge =>
    (mem_filter.mp hi).2.ne_empty <| subset_empty.mp <|
      hk ▸ stateAt_balls_mono h A B (Nat.le_of_not_lt hge)).trans (by simp)

theorem roundsOn_le_card {U' n' : ℕ} (h : Scheme U' n')
    {A : Finset (Fin U')} {B : Finset (Fin n')} (hle : A.card ≤ B.card) :
    roundsOn h A B ≤ A.card :=
  roundsOn_le_of_stateAt_balls_eq_empty h (stateAt_balls_eq_empty h hle le_rfl)

private theorem matchAux_spec {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U'))
    (B : Finset (Fin n')) (k : ℕ) :
    (∀ a, (matchAux h A B k a).isSome ↔ a ∈ A \ (stateAt h A B k).1) ∧
    (∀ a b, matchAux h A B k a = some b → b ∈ B \ (stateAt h A B k).2) ∧
    (∀ a₁ a₂ b, matchAux h A B k a₁ = some b → matchAux h A B k a₂ = some b → a₁ = a₂) := by
  induction k with
  | zero => simp [matchAux, stateAt]
  | succ k ih =>
    obtain ⟨hdom, hran, hinj⟩ := ih
    refine ⟨fun a => ?_, fun a b hab => ?_, fun a₁ a₂ b h₁ h₂ => ?_⟩
    · dsimp only [matchAux, stateAt]
      cases hmk : matchAux h A B k a with
      | some _ =>
        have ha := (hdom a).mp (by simp [hmk])
        split_ifs <;> [exact ⟨fun _ => mem_sdiff.mpr ⟨(mem_sdiff.mp ha).1,
          fun hm => (mem_sdiff.mp ha).2 (sdiff_subset hm)⟩, fun _ => rfl⟩; simpa using ha]
      | none =>
        have hnot : a ∉ A \ (stateAt h A B k).1 := by simp [← hdom a, hmk]
        split_ifs with hk
        · by_cases haA : a ∈ A
          · have ha_rem : a ∈ (stateAt h A B k).1 := by
              by_contra hni; exact hnot (mem_sdiff.mpr ⟨haA, hni⟩)
            cases hrm : roundMatchOpt (h ⟨k, hk⟩) (stateAt h A B k).1 (stateAt h A B k).2 a <;>
              simp [roundStep, hrm, haA, ha_rem]
          · simp [roundMatchOpt, haA,
            show a ∉ (stateAt h A B k).1 from fun hm => haA (stateAt_balls_subset h A B k hm)]
        · simp [hnot]
    · dsimp only [matchAux, stateAt] at hab ⊢
      cases hmk : matchAux h A B k a with
      | some b' =>
        rw [hmk] at hab; obtain rfl := Option.some.inj hab
        have hb := hran a b' hmk
        split_ifs <;> [exact mem_sdiff.mpr ⟨(mem_sdiff.mp hb).1,
          fun hm => (mem_sdiff.mp hb).2 (sdiff_subset hm)⟩; exact hb]
      | none =>
        rw [hmk] at hab; split_ifs at hab with hk
        simp only [hk, ↓reduceDIte, roundStep, mem_sdiff]
        have hm := roundMatchOpt_mem_bins hab
        exact ⟨stateAt_bins_subset h A B k hm.2,
          fun h' => h'.2 (mem_filter.mpr ⟨hm.2, a, hm.1, hab⟩)⟩
    · have hcase {x} (hx : matchAux h A B (k + 1) x = some b) : matchAux h A B k x = some b ∨
          ∃ hk : k < U',
            roundMatchOpt (h ⟨k, hk⟩) (stateAt h A B k).1 (stateAt h A B k).2 x = some b := by
        dsimp only [matchAux] at hx
        cases hm : matchAux h A B k x <;> simp only [hm] at hx
        · split_ifs at hx with hk; exact .inr ⟨hk, hx⟩
        · exact .inl hx
      rcases hcase h₁ with h₁ | ⟨hk, h₁⟩ <;> rcases hcase h₂ with h₂ | ⟨_, h₂⟩
      · exact hinj a₁ a₂ b h₁ h₂
      · exact ((mem_sdiff.mp (hran a₁ b h₁)).2 (roundMatchOpt_mem_bins h₂).2).elim
      · exact ((mem_sdiff.mp (hran a₂ b h₂)).2 (roundMatchOpt_mem_bins h₁).2).elim
      · exact roundMatchOpt_injective (h ⟨k, hk⟩) _ _ h₁ h₂

theorem matchOptOn_isSome_iff {U' n' : ℕ} (h : Scheme U' n')
    {A : Finset (Fin U')} {B : Finset (Fin n')} (hle : A.card ≤ B.card)
    (a : Fin U') : (matchOptOn h A B a).isSome ↔ a ∈ A := by
  have hAU : A.card ≤ U' := by simpa using A.card_le_univ
  rw [matchOptOn, (matchAux_spec h A B U').1 a,
    stateAt_balls_eq_empty h hle hAU, sdiff_empty]

theorem matchOptOn_injective {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U'))
    (B : Finset (Fin n')) {a₁ a₂ : Fin U'} {b : Fin n'}
    (h₁ : matchOptOn h A B a₁ = some b) (h₂ : matchOptOn h A B a₂ = some b) : a₁ = a₂ :=
  (matchAux_spec h A B U').2.2 a₁ a₂ b h₁ h₂

theorem matchOpt_isSome_iff {U' n' : ℕ} (h : Scheme U' n')
    {A : Finset (Fin U')} (hA : A.card ≤ n') (a : Fin U') :
    (matchOpt h A a).isSome ↔ a ∈ A :=
  matchOptOn_isSome_iff h (by simpa using hA) a

theorem matchOpt_injective {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U'))
    {a₁ a₂ : Fin U'} {b : Fin n'}
    (h₁ : matchOpt h A a₁ = some b) (h₂ : matchOpt h A a₂ = some b) : a₁ = a₂ :=
  matchOptOn_injective h A Finset.univ h₁ h₂

theorem rounds_le_card {U' n' : ℕ} (h : Scheme U' n')
    {A : Finset (Fin U')} (hA : A.card ≤ n') : rounds h A ≤ A.card :=
  roundsOn_le_card h (by simpa using hA)

/-- Canonical history-independent dynamic matching `σ_A : A ↪ Fin n'` (`Problem 3.1`,
`Algorithm 1`) for any active ball set `A ⊆ Fin U'` of size `A.card ≤ n'`. -/
def matching {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U'))
    (hA : A.card ≤ n') : A ↪ Fin n' where
  toFun a := (matchOpt h A a.val).get <|
    (matchOptOn_isSome_iff h (by simpa using hA) a.val).mpr a.property
  inj' a₁ a₂ heq := Subtype.ext <|
    matchOptOn_injective h A Finset.univ
      ((Option.some_get _).symm.trans (congrArg some heq))
      (Option.some_get _).symm

@[simp]
theorem matching_apply {U' n' : ℕ} (h : Scheme U' n') (A : Finset (Fin U'))
    (hA : A.card ≤ n') (a : A) :
    matchOpt h A a.val = some (matching h A hA a) :=
  (Option.some_get _).symm

/-! ### Expected round bound (`Claim 3.3`) -/

private theorem clockwiseNextPos_ne_self {M : ℕ} {P : Finset (Fin M)} (hcard : 2 ≤ P.card)
    {p : Fin M} (hp : p ∈ P) : clockwiseNextPos P p ≠ p := by
  have hP : P.Nonempty := ⟨p, hp⟩
  simp only [clockwiseNextPos, hP, ↓reduceDIte]
  split_ifs with hgt
  · exact (mem_filter.mp (min'_mem _ hgt)).2.ne'
  · obtain ⟨q, hq⟩ := card_pos.mp (by rw [card_erase_of_mem hp]; omega : 0 < (P.erase p).card)
    have hqP := mem_of_mem_erase hq
    have hle : q ≤ p := le_of_not_gt fun hlt => hgt ⟨q, mem_filter.mpr ⟨hqP, hlt⟩⟩
    exact ((min'_le P q hqP).trans_lt (lt_of_le_of_ne hle (ne_of_mem_erase hq))).ne

private theorem nextItem_mem_erase {M : ℕ} (π : Equiv.Perm (Fin M)) {S : Finset (Fin M)}
    (hcard : 2 ≤ S.card) {z : Fin M} (hz : z ∈ S) : nextItem π S z ∈ S.erase z :=
  mem_erase.mpr ⟨fun heq => by
    have hne := clockwiseNextPos_ne_self (P := S.map π.toEmbedding) (by simpa using hcard)
      (mem_map.mpr ⟨z, hz, rfl⟩)
    exact hne (by simpa [nextItem] using congrArg π heq),
    nextItem_mem π ⟨z, hz⟩ z⟩

/-- Single-round symmetry bound (`Claim 3.3` core): over a uniform permutation `π`, the expected
number of balls remaining unmatched after one round is at most `A.card / 2`. Stated in exact `ℕ`
counting form without division. -/
private theorem two_mul_sum_card_balls_roundStep_le {U' n' : ℕ} {A : Finset (Fin U')}
    {B : Finset (Fin n')} (hle : A.card ≤ B.card) :
    2 * ∑ π : RoundPerm U' n', (roundStep π (A, B)).1.card ≤
      A.card * Fintype.card (RoundPerm U' n') := by
  have hpoint (π : RoundPerm U' n') : (roundStep π (A, B)).1.card =
      ∑ a ∈ A, if roundMatchOpt π A B a = none then 1 else 0 := by
    rw [← card_filter]; congr 1; ext a; simp +contextual [roundStep]
  simp_rw [hpoint]; rw [sum_comm, mul_sum, ← sum_const_nat
    (f := fun _ => Fintype.card (RoundPerm U' n')) fun _ _ => rfl]
  refine sum_le_sum fun a ha => ?_
  set S := activeItems A B
  obtain ⟨b₀, hb₀⟩ := card_pos.mp (lt_of_lt_of_le (card_pos.mpr ⟨a, ha⟩) hle)
  have hApos : 1 ≤ A.card := card_pos.mpr ⟨a, ha⟩
  have hScard : 2 ≤ S.card := by rw [card_activeItems]; omega
  set x := ballItem n' a; have hxS : x ∈ S := ballItem_mem_activeItems.mpr ha
  set y₀ := binItem U' b₀
  have hy₀ : y₀ ∈ S.erase x :=
    mem_erase.mpr ⟨(ballItem_ne_binItem a b₀).symm, binItem_mem_activeItems.mpr hb₀⟩
  let fiber (y : Fin (U' + n')) := Finset.univ.filter fun π : RoundPerm U' n' => nextItem π S x = y
  have hfiber_card : ∀ y ∈ S.erase x, (fiber y).card = (fiber y₀).card := fun y hy => by
    refine card_equiv (Equiv.mulRight (Equiv.swap y y₀)) fun π => ?_
    simp only [fiber, mem_filter, mem_univ, true_and]
    change nextItem π S x = y ↔ nextItem (π * Equiv.swap y y₀) S x = y₀
    rw [nextItem_mul_swap π (mem_of_mem_erase hy) (mem_of_mem_erase hy₀)
      (mem_erase.mp hy).1.symm (mem_erase.mp hy₀).1.symm]
    exact ⟨fun h => h ▸ Equiv.swap_apply_left _ _,
      fun h => (Equiv.swap y y₀).injective (h.trans (Equiv.swap_apply_left _ _).symm)⟩
  have htot : Fintype.card (RoundPerm U' n') = (A.card + B.card - 1) * (fiber y₀).card := by
    have hcard := card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (RoundPerm U' n')))
      (t := S.erase x) (f := fun π => nextItem π S x) fun π _ => nextItem_mem_erase π hScard hxS
    rw [← card_univ, hcard, sum_congr rfl fun y hy => hfiber_card y hy, sum_const, smul_eq_mul,
      card_erase_of_mem hxS, card_activeItems]
  set badY := (A.erase a).map ⟨ballItem n', ballItem_injective U' n'⟩
  have hbadY_sub : badY ⊆ S.erase x := fun y hy => by
    obtain ⟨a', ha', rfl⟩ := mem_map.mp hy
    exact mem_erase.mpr ⟨fun h => (mem_erase.mp ha').1 (ballItem_injective U' n' h),
      ballItem_mem_activeItems.mpr (mem_of_mem_erase ha')⟩
  set badP := Finset.univ.filter fun π : RoundPerm U' n' => roundMatchOpt π A B a = none
  have hbad_maps : ∀ π ∈ badP, nextItem π S x ∈ badY := fun π hπ => by
    have hmem := nextItem_mem_erase π hScard hxS
    rcases mem_activeItems_iff.mp (mem_of_mem_erase hmem) with ⟨a', ha', heq⟩ | ⟨b, _, heq⟩
    · exact heq ▸ mem_map.mpr ⟨a', mem_erase.mpr ⟨fun h => (mem_erase.mp hmem).1
        (by simp [heq, x, h]), ha'⟩, rfl⟩
    · exact absurd (mem_filter.mp hπ).2 (by simp [roundMatchOpt, ha, S, x, heq])
  have hbad_le : badP.card ≤ (A.card - 1) * (fiber y₀).card := by
    rw [card_eq_sum_card_fiberwise hbad_maps]
    calc ∑ y ∈ badY, (badP.filter fun π => nextItem π S x = y).card
        ≤ ∑ y ∈ badY, (fiber y).card :=
          sum_le_sum fun y _ => card_le_card (monotone_filter_left _ (subset_univ _))
      _ = badY.card * (fiber y₀).card := by
          rw [sum_congr rfl fun y hy => hfiber_card y (hbadY_sub hy), sum_const, smul_eq_mul]
      _ = (A.card - 1) * (fiber y₀).card := by rw [card_map, card_erase_of_mem ha]
  rw [← card_filter, htot]
  calc 2 * badP.card ≤ (2 * (A.card - 1)) * (fiber y₀).card := by
        rw [mul_assoc]; exact Nat.mul_le_mul_left 2 hbad_le
    _ ≤ (A.card + B.card - 1) * (fiber y₀).card := Nat.mul_le_mul_right _ (by omega)

private theorem stateAt_congr {U' n' : ℕ} {h₁ h₂ : Scheme U' n'} (A : Finset (Fin U'))
    (B : Finset (Fin n')) {k : ℕ} (heq : ∀ (i : Fin U'), i.val < k → h₁ i = h₂ i) :
    stateAt h₁ A B k = stateAt h₂ A B k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hp := ih fun i hi => heq i (Nat.lt_succ_of_lt hi)
    dsimp only [stateAt]; split_ifs with hk
    · rw [hp, heq ⟨k, hk⟩ (Nat.lt_succ_self k)]
    · exact hp

/-- Multi-round geometric contraction in `ℕ`: after `k ≤ U'` rounds, the sum of `(stateAt h A B k)`
ball counts across all `h : Scheme U' n'`, multiplied by `2 ^ k`, is at most `A.card * |Scheme|`. -/
private theorem two_pow_mul_sum_card_stateAt_le {U' n' : ℕ} {A : Finset (Fin U')}
    {B : Finset (Fin n')} (hle : A.card ≤ B.card) {k : ℕ} (hk : k ≤ U') :
    2 ^ k * ∑ h : Scheme U' n', (stateAt h A B k).1.card ≤
      A.card * Fintype.card (Scheme U' n') := by
  induction k with
  | zero => simp [stateAt, Nat.mul_comm]
  | succ k ih =>
    have hk' : k < U' := Nat.lt_of_succ_le hk
    let e := Equiv.piSplitAt ⟨k, hk'⟩ (fun _ : Fin U' => RoundPerm U' n')
    have hconst (π : RoundPerm U' n') (rest : _) :
        stateAt (e.symm (π, rest)) A B k = stateAt (e.symm (1, rest)) A B k :=
      stateAt_congr A B fun i hik => by
        simp [e, Equiv.piSplitAt_symm_apply, show i ≠ ⟨k, hk'⟩ from fun h => by
          subst h; exact Nat.lt_irrefl k hik]
    have hsum_le : 2 * ∑ h : Scheme U' n', (stateAt h A B (k + 1)).1.card ≤
        ∑ h : Scheme U' n', (stateAt h A B k).1.card := by
      have hL := (Equiv.sum_comp e.symm fun h => (stateAt h A B (k + 1)).1.card).symm
      have hR := (Equiv.sum_comp e.symm fun h => (stateAt h A B k).1.card).symm
      rw [hL, hR, Fintype.sum_prod_type_right, Fintype.sum_prod_type_right, mul_sum]
      refine sum_le_sum fun rest _ => ?_
      have hst : (∑ π, (stateAt (e.symm (π, rest)) A B (k + 1)).1.card) =
          ∑ π, (roundStep π (stateAt (e.symm (1, rest)) A B k)).1.card :=
        sum_congr rfl fun π _ => by simp [stateAt, hk', e, hconst π rest]
      rw [hst]
      have hs := two_mul_sum_card_balls_roundStep_le
        (card_balls_le_card_bins_stateAt (e.symm (1, rest)) hle k)
      rw [Prod.mk.eta] at hs
      exact hs.trans_eq (by simp [hconst _ rest, Nat.mul_comm])
    calc 2 ^ (k + 1) * ∑ h : Scheme U' n', (stateAt h A B (k + 1)).1.card
        = 2 ^ k * (2 * ∑ h : Scheme U' n', (stateAt h A B (k + 1)).1.card) := by ring
      _ ≤ 2 ^ k * ∑ h : Scheme U' n', (stateAt h A B k).1.card := Nat.mul_le_mul_left _ hsum_le
      _ ≤ A.card * Fintype.card (Scheme U' n') := ih hk'.le

/-- Real-valued expectation of remaining balls after `k ≤ U'` rounds under `schemePMF`:
`𝔼_h[|A_k|] ≤ |A| / 2 ^ k`. -/
private theorem expect_card_balls_stateAt_le {U' n' : ℕ} {A : Finset (Fin U')}
    {B : Finset (Fin n')} (hle : A.card ≤ B.card) {k : ℕ} (hk : k ≤ U') :
    (∑ h : Scheme U' n', ((schemePMF U' n' h).toReal * ((stateAt h A B k).1.card : ℝ))) ≤
      (A.card : ℝ) / (2 : ℝ) ^ k := by
  have hnat : (2 : ℝ) ^ k * ∑ h : Scheme U' n', ((stateAt h A B k).1.card : ℝ) ≤
      (A.card : ℝ) * Fintype.card (Scheme U' n') := by
    exact_mod_cast two_pow_mul_sum_card_stateAt_le (U' := U') hle hk
  simp_rw [schemePMF, Cslib.Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ← mul_sum]
  rw [inv_mul_le_iff₀ (by positivity), ← mul_div_assoc, le_div_iff₀ (by positivity)]
  linarith

/-- **Claim 3.3** ([LiLiangYuZhou2024, Section 3.1]): for any `A ⊆ Fin U'`
and `B ⊆ Fin n'` with `A.card ≤ B.card`, the expected number of rounds `T = roundsOn h A B` under
uniform independent permutations is at most `⌈log₂ |A|⌉ + 2`. -/
theorem expect_roundsOn_le {U' n' : ℕ} {A : Finset (Fin U')} {B : Finset (Fin n')}
    (hle : A.card ≤ B.card) :
    (∑ h : Scheme U' n', (schemePMF U' n' h).toReal * (roundsOn h A B : ℝ)) ≤
      (Nat.clog 2 A.card : ℝ) + 2 := by
  rcases A.eq_empty_or_nonempty with rfl | _
  · have hz (h : Scheme U' n') : roundsOn h ∅ B = 0 :=
      Nat.le_zero.mp (roundsOn_le_of_stateAt_balls_eq_empty h rfl)
    simp [hz]
  set L := Nat.clog 2 A.card
  have hrounds_eq (h : Scheme U' n') : (roundsOn h A B : ℝ) =
      ∑ i ∈ Finset.range U', if (stateAt h A B i).1.Nonempty then (1 : ℝ) else 0 := by
    simp only [roundsOn, ← sum_boole]
  simp_rw [hrounds_eq, mul_sum]; rw [sum_comm]
  let bound (i : ℕ) : ℝ := if i < L then 1 else (1 / 2 : ℝ) ^ (i - L)
  have hterm : ∀ i ∈ Finset.range U',
      ∑ h : Scheme U' n', (schemePMF U' n' h).toReal *
        (if (stateAt h A B i).1.Nonempty then (1 : ℝ) else 0) ≤ bound i := fun i hi => by
    dsimp only [bound]; split_ifs with hiL
    · exact Cslib.Probability.PMF.sum_mul_le _ _ 1 fun _ => by split_ifs <;> norm_num
    · have hLi : L ≤ i := Nat.le_of_not_lt hiL
      have h1 : ∑ h : Scheme U' n', (schemePMF U' n' h).toReal *
          (if (stateAt h A B i).1.Nonempty then (1 : ℝ) else 0) ≤
          ∑ h : Scheme U' n', (schemePMF U' n' h).toReal * ((stateAt h A B i).1.card : ℝ) :=
        sum_le_sum fun h _ => mul_le_mul_of_nonneg_left (by
          split_ifs with hne
          · exact_mod_cast card_pos.mpr hne
          · positivity) ENNReal.toReal_nonneg
      refine h1.trans ((expect_card_balls_stateAt_le hle (mem_range.mp hi).le).trans ?_)
      have hAL : (A.card : ℝ) ≤ (2 : ℝ) ^ L := by
        exact_mod_cast Nat.le_pow_clog Nat.one_lt_two A.card
      calc (A.card : ℝ) / (2 : ℝ) ^ i ≤ (2 : ℝ) ^ L / (2 : ℝ) ^ i := by gcongr
        _ = (1 / 2 : ℝ) ^ (i - L) := by
            rw [show (2 : ℝ) ^ i = (2 : ℝ) ^ L * (2 : ℝ) ^ (i - L) by
              rw [← pow_add, Nat.add_sub_of_le hLi], div_mul_eq_div_div,
              div_self (by positivity), one_div_pow, one_div]
  refine (sum_le_sum hterm).trans ?_
  have hgeom : ∑ j ∈ Finset.range U', (1 / 2 : ℝ) ^ j = 2 - 2 * (1 / 2 : ℝ) ^ U' := by
    rw [geom_sum_eq (by norm_num)]; ring
  calc ∑ i ∈ Finset.range U', bound i ≤ ∑ i ∈ Finset.range (L + U'), bound i :=
        sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) fun i _ _ => by
          dsimp only [bound]; split_ifs <;> positivity
    _ = L + (2 - 2 * (1 / 2 : ℝ) ^ U') := by
        rw [sum_range_add, ← hgeom, sum_congr rfl fun i hi => show bound i = 1 by
          simp [bound, mem_range.mp hi]]
        simp [bound]
    _ ≤ L + 2 := by linarith [show (0 : ℝ) ≤ 2 * (1 / 2 : ℝ) ^ U' by positivity]

/-- Specialization of **Claim 3.3** to all `n'` slots (`B = Finset.univ`): for `A.card ≤ n'`,
`𝔼[rounds h A] ≤ ⌈log₂ |A|⌉ + 2 ≤ 3 * ⌈log₂ (max |A| 2)⌉`. -/
theorem expect_rounds_le {U' n' : ℕ} {A : Finset (Fin U')} (hA : A.card ≤ n') :
    (∑ h : Scheme U' n', (schemePMF U' n' h).toReal * (rounds h A : ℝ)) ≤
      3 * (Nat.clog 2 (max A.card 2) : ℝ) := by
  have h1 := expect_roundsOn_le (U' := U') (B := (Finset.univ : Finset (Fin n')))
    (by simpa using hA)
  have hpos1 : (1 : ℝ) ≤ Nat.clog 2 (max A.card 2) := by
    exact_mod_cast Nat.clog_pos Nat.one_lt_two (by omega : 1 < max A.card 2)
  have hmonoR : (Nat.clog 2 A.card : ℝ) ≤ Nat.clog 2 (max A.card 2) := by
    exact_mod_cast Nat.clog_mono_right 2 (le_max_left _ _)
  dsimp only [rounds]
  linarith

/-! ### Single-operation relocation bounds (`Claim 3.4` and `Lemma 3.2`) -/

/-- Total symmetric-difference size `|A ∆ A'| + |B ∆ B'|` between two `(balls, bins)` states. -/
private def pairDiff {U' n' : ℕ} (AB AB' : Finset (Fin U') × Finset (Fin n')) : ℕ :=
  (AB.1 ∆ AB'.1).card + (AB.2 ∆ AB'.2).card

private theorem pairDiff_comm {U' n' : ℕ} (AB AB' : Finset (Fin U') × Finset (Fin n')) :
    pairDiff AB AB' = pairDiff AB' AB := by
  simp [pairDiff, symmDiff_comm]

private theorem card_symmDiff_insert_le_one {α : Type*} [DecidableEq α]
    (s : Finset α) (x : α) : (s ∆ insert x s).card ≤ 1 := by
  refine (card_le_card fun z hz => ?_).trans (card_singleton x).le
  simp only [mem_symmDiff, mem_insert, mem_singleton] at hz ⊢
  grind

private theorem card_symmDiff_erase_le_one {α : Type*} [DecidableEq α]
    (s : Finset α) (x : α) : (s ∆ s.erase x).card ≤ 1 := by
  refine (card_le_card fun z hz => ?_).trans (card_singleton x).le
  simp only [mem_symmDiff, mem_erase, mem_singleton] at hz ⊢
  grind

private theorem mem_sdiff_filter {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop)
    [DecidablePred p] (x : α) : x ∈ s \ s.filter p ↔ x ∈ s ∧ ¬p x := by
  simp only [mem_sdiff, mem_filter]; tauto

private theorem roundMatchOpt_eq_none_of_bins_empty {U' n' : ℕ} (π : RoundPerm U' n')
    (A : Finset (Fin U')) (a : Fin U') :
    roundMatchOpt π A ∅ a = none := by
  cases h : roundMatchOpt π A ∅ a with
  | none => rfl
  | some b => exact absurd (roundMatchOpt_mem_bins h).2 (notMem_empty b)

private theorem roundStep_empty_bins {U' n' : ℕ} (π : RoundPerm U' n')
    (A : Finset (Fin U')) : roundStep π (A, ∅) = (A, ∅) := by
  ext <;> simp [roundStep, roundMatchOpt_eq_none_of_bins_empty]

@[simp]
private theorem mem_roundStep_fst {U' n' : ℕ} (π : RoundPerm U' n')
    (A : Finset (Fin U')) (B : Finset (Fin n')) (a : Fin U') :
    a ∈ (roundStep π (A, B)).1 ↔ a ∈ A ∧ roundMatchOpt π A B a = none := by
  simp only [roundStep, mem_sdiff_filter]
  cases roundMatchOpt π A B a <;> simp

private theorem mem_roundStep_snd {U' n' : ℕ} (π : RoundPerm U' n')
    (A : Finset (Fin U')) (B : Finset (Fin n')) (b : Fin n') :
    b ∈ (roundStep π (A, B)).2 ↔ b ∈ B ∧ ∀ a, roundMatchOpt π A B a ≠ some b := by
  simp only [roundStep, mem_sdiff_filter]
  exact and_congr_right fun _ =>
    ⟨fun h a hab => h ⟨a, (roundMatchOpt_mem_bins hab).1, hab⟩,
     fun h ⟨a, _, hab⟩ => h a hab⟩

private theorem card_filter_ne_le {α β : Type*} [Fintype α] [DecidableEq β]
    {f g : α → β} (s : Finset α) (h : ∀ a, a ∉ s → g a = f a) :
    (Finset.univ.filter fun a => f a ≠ g a).card ≤ s.card := by
  refine card_le_card fun a ha => ?_
  simp only [mem_filter, mem_univ, true_and] at ha
  by_contra hns
  exact ha (h a hns).symm

/-- Inserting a single bin `bStar ∉ B` preserves `pairDiff ≤ 1` across `roundStep` and changes
at most `1` ball's single-round match (`Claim 3.4` bin-insertion case,
[LiLiangYuZhou2024, Section 3.1]). -/
private theorem roundStep_insert_bin {U' n' : ℕ} (π : RoundPerm U' n') (A : Finset (Fin U'))
    {B : Finset (Fin n')} {bStar : Fin n'} (hbStar : bStar ∉ B) :
    pairDiff (roundStep π (A, B)) (roundStep π (A, insert bStar B)) ≤ 1 ∧
      (Finset.univ.filter fun a =>
        roundMatchOpt π A B a ≠ roundMatchOpt π A (insert bStar B) a).card ≤ 1 := by
  set S := activeItems A B
  have hS_ins : activeItems A (insert bStar B) = insert (binItem U' bStar) S := by
    ext z; simp only [S, activeItems, map_insert, mem_union, mem_insert]; tauto
  by_cases hSne : S.Nonempty
  · have hzStar : binItem U' bStar ∉ S := by simpa [S] using hbStar
    obtain ⟨x₀, hx₀S, hnx₀, _, hnw⟩ := exists_insert_nextItem π hSne hzStar
    have hsame (a : Fin U') (hne : ballItem n' a ≠ x₀) :
        roundMatchOpt π A (insert bStar B) a = roundMatchOpt π A B a := by
      by_cases ha : a ∈ A
      · simp [roundMatchOpt, ha, hS_ins, S, hnw _ (ballItem_mem_activeItems.mpr ha) hne]
      · simp [roundMatchOpt, ha]
    rcases mem_activeItems_iff.mp hx₀S with ⟨a₀, ha₀A, rfl⟩ | ⟨b₀, _, rfl⟩
    · have hsame' (a : Fin U') (h : a ≠ a₀) := hsame a fun e => h (ballItem_injective U' n' e)
      have ha₀_new : roundMatchOpt π A (insert bStar B) a₀ = some bStar := by
        simp [roundMatchOpt, ha₀A, hS_ins, hnx₀]
      refine ⟨?_, (card_filter_ne_le {a₀} fun a ha =>
        hsame' a (mem_singleton.not.mp ha)).trans_eq (card_singleton a₀)⟩
      have hbins_iff (b : Fin n') : b ∈ (roundStep π (A, insert bStar B)).2 ↔
          b ∈ (roundStep π (A, B)).2 ∨ roundMatchOpt π A B a₀ = some b := by
        simp only [mem_roundStep_snd, mem_insert]
        constructor
        · rintro ⟨rfl | hbB, hno⟩
          · exact absurd ha₀_new (hno a₀)
          · by_cases hm : roundMatchOpt π A B a₀ = some b
            · exact .inr hm
            · exact .inl ⟨hbB, fun a => by
                rcases eq_or_ne a a₀ with rfl | h
                exacts [hm, by simpa [hsame' a h] using hno a]⟩
        · rintro (⟨hbB, hno⟩ | hm)
          · refine ⟨.inr hbB, fun a => ?_⟩
            rcases eq_or_ne a a₀ with rfl | h
            · rw [ha₀_new]; exact fun e => hbStar (Option.some.inj e ▸ hbB)
            · simpa [hsame' a h] using hno a
          · have hbB := (roundMatchOpt_mem_bins hm).2
            refine ⟨.inr hbB, fun a => ?_⟩
            rcases eq_or_ne a a₀ with rfl | h
            · rw [ha₀_new]; exact fun e => hbStar (Option.some.inj e ▸ hbB)
            · rw [hsame' a h]; exact fun hab => h (roundMatchOpt_injective π A B hab hm)
      cases hold : roundMatchOpt π A B a₀ with
      | none =>
        have hballs : (roundStep π (A, insert bStar B)).1 = (roundStep π (A, B)).1.erase a₀ := by
          ext a; simp only [mem_roundStep_fst, mem_erase]
          rcases eq_or_ne a a₀ with rfl | h
          exacts [by simp [ha₀_new], by simp [hsame' a h, h]]
        have hbins : (roundStep π (A, insert bStar B)).2 = (roundStep π (A, B)).2 := by
          ext b; simp [hbins_iff, hold]
        simpa [pairDiff, hballs, hbins] using card_symmDiff_erase_le_one _ a₀
      | some b₁ =>
        have hballs : (roundStep π (A, insert bStar B)).1 = (roundStep π (A, B)).1 := by
          ext a; simp only [mem_roundStep_fst]
          rcases eq_or_ne a a₀ with rfl | h
          exacts [by simp [hold, ha₀_new], by simp [hsame' a h]]
        have hbins : (roundStep π (A, insert bStar B)).2 = insert b₁ (roundStep π (A, B)).2 := by
          ext b; simp [hbins_iff, hold, or_comm, eq_comm]
        simpa [pairDiff, hballs, hbins] using card_symmDiff_insert_le_one _ b₁
    · have hall (a : Fin U') := hsame a (ballItem_ne_binItem a b₀)
      have hballs : (roundStep π (A, insert bStar B)).1 = (roundStep π (A, B)).1 := by
        ext a; simp [mem_roundStep_fst, hall]
      have hbins : (roundStep π (A, insert bStar B)).2 = insert bStar (roundStep π (A, B)).2 := by
        ext b; simp only [mem_roundStep_snd, mem_insert, hall]
        exact ⟨fun | ⟨.inl rfl, _⟩ => .inl rfl | ⟨.inr hb, hn⟩ => .inr ⟨hb, hn⟩,
          fun | .inl rfl => ⟨.inl rfl, fun _ h => hbStar (roundMatchOpt_mem_bins h).2⟩
              | .inr ⟨hb, hn⟩ => ⟨.inr hb, hn⟩⟩
      exact ⟨by simpa [pairDiff, hballs, hbins] using card_symmDiff_insert_le_one _ bStar,
        by simp [hall]⟩
  · obtain ⟨rfl, rfl⟩ := eq_empty_of_not_nonempty_activeItems hSne
    exact ⟨by simpa [roundStep_empty_balls, pairDiff] using card_symmDiff_insert_le_one ∅ bStar,
      by simp [roundMatchOpt]⟩

/-- Inserting a single ball `aStar ∉ A` preserves `pairDiff ≤ 1` across `roundStep` and changes
at most `2` balls' single-round matches (`Claim 3.4` ball-insertion case). -/
private theorem roundStep_insert_ball {U' n' : ℕ} (π : RoundPerm U' n') {A : Finset (Fin U')}
    {aStar : Fin U'} (haStar : aStar ∉ A) (B : Finset (Fin n')) :
    pairDiff (roundStep π (A, B)) (roundStep π (insert aStar A, B)) ≤ 1 ∧
      (Finset.univ.filter fun a =>
        roundMatchOpt π A B a ≠ roundMatchOpt π (insert aStar A) B a).card ≤ 2 := by
  set S := activeItems A B
  have hS_ins : activeItems (insert aStar A) B = insert (ballItem n' aStar) S := by
    ext z; simp only [S, activeItems, map_insert, mem_union, mem_insert]; tauto
  by_cases hSne : S.Nonempty
  · have hzStar : ballItem n' aStar ∉ S := by simpa [S] using haStar
    obtain ⟨x₀, hx₀S, hnx₀, hnz, hnw⟩ := exists_insert_nextItem π hSne hzStar
    have hsame (a : Fin U') (h₁ : a ≠ aStar) (h₂ : ballItem n' a ≠ x₀) :
        roundMatchOpt π (insert aStar A) B a = roundMatchOpt π A B a := by
      by_cases ha : a ∈ A
      · simp [roundMatchOpt, ha, mem_insert_of_mem ha, hS_ins, S,
          hnw _ (ballItem_mem_activeItems.mpr ha) h₂]
      · simp [roundMatchOpt, ha, h₁]
    rcases mem_activeItems_iff.mp hx₀S with ⟨a₀, ha₀A, rfl⟩ | ⟨b₀, _, rfl⟩
    · have ha₀ne : a₀ ≠ aStar := fun h => haStar (h ▸ ha₀A)
      have ha₀_new : roundMatchOpt π (insert aStar A) B a₀ = none := by
        simp [roundMatchOpt, mem_insert_of_mem ha₀A, hS_ins, hnx₀]
      have haStar_new : roundMatchOpt π (insert aStar A) B aStar = roundMatchOpt π A B a₀ := by
        simp [roundMatchOpt, ha₀A, hS_ins, S, hnz]
      have hsame' (a : Fin U') (h₁ : a ≠ aStar) (h₂ : a ≠ a₀) :=
        hsame a h₁ fun e => h₂ (ballItem_injective U' n' e)
      refine ⟨?_, (card_filter_ne_le {aStar, a₀} fun a ha => by
        simp only [mem_insert, mem_singleton, not_or] at ha; exact hsame' a ha.1 ha.2).trans
          Finset.card_le_two⟩
      have hbins : (roundStep π (insert aStar A, B)).2 = (roundStep π (A, B)).2 := by
        ext b; simp only [mem_roundStep_snd]
        refine and_congr_right fun _ => ⟨fun hno a => ?_, fun hno a => ?_⟩
        · rcases eq_or_ne a aStar with rfl | h₁
          · exact fun hab => haStar (roundMatchOpt_mem_bins hab).1
          · rcases eq_or_ne a a₀ with rfl | h₂
            exacts [haStar_new ▸ hno aStar, by simpa [hsame' a h₁ h₂] using hno a]
        · rcases eq_or_ne a aStar with rfl | h₁
          · exact haStar_new ▸ hno a₀
          · rcases eq_or_ne a a₀ with rfl | h₂
            exacts [by simp [ha₀_new], by simpa [hsame' a h₁ h₂] using hno a]
      cases hold : roundMatchOpt π A B a₀ with
      | none =>
        have hballs : (roundStep π (insert aStar A, B)).1 =
            insert aStar (roundStep π (A, B)).1 := by
          ext a; simp only [mem_roundStep_fst, mem_insert]
          rcases eq_or_ne a aStar with rfl | h₁; · simp [haStar_new, hold]
          rcases eq_or_ne a a₀ with rfl | h₂
          exacts [by simp [ha₀ne, ha₀A, ha₀_new, hold], by simp [hsame' a h₁ h₂, h₁]]
        simpa [pairDiff, hballs, hbins] using card_symmDiff_insert_le_one _ aStar
      | some b₁ =>
        have hballs : (roundStep π (insert aStar A, B)).1 = insert a₀ (roundStep π (A, B)).1 := by
          ext a; simp only [mem_roundStep_fst, mem_insert]
          rcases eq_or_ne a aStar with rfl | h₁; · simp [ha₀ne.symm, haStar_new, hold, haStar]
          rcases eq_or_ne a a₀ with rfl | h₂
          exacts [by simp [ha₀A, ha₀_new], by simp [hsame' a h₁ h₂, h₁, h₂]]
        simpa [pairDiff, hballs, hbins] using card_symmDiff_insert_le_one _ a₀
    · have hsame_A (a : Fin U') (h : a ≠ aStar) := hsame a h (ballItem_ne_binItem a b₀)
      have haStar_new : roundMatchOpt π (insert aStar A) B aStar =
          asBin? (nextItem π S (binItem U' b₀)) := by simp [roundMatchOpt, hS_ins, hnz]
      refine ⟨?_, ((card_filter_ne_le {aStar} fun a ha =>
        hsame_A a (mem_singleton.not.mp ha)).trans_eq (card_singleton aStar)).trans (by omega)⟩
      cases hbin : asBin? (nextItem π S (binItem U' b₀)) with
      | none =>
        have hall (a : Fin U') : roundMatchOpt π (insert aStar A) B a = roundMatchOpt π A B a := by
          rcases eq_or_ne a aStar with rfl | h
          · rw [haStar_new, hbin]; simp [roundMatchOpt, haStar]
          · exact hsame_A a h
        have hballs : (roundStep π (insert aStar A, B)).1 =
            insert aStar (roundStep π (A, B)).1 := by
          ext a; simp only [mem_roundStep_fst, mem_insert, hall]
          by_cases ha : a = aStar <;> simp [ha, roundMatchOpt, haStar]
        have hbins : (roundStep π (insert aStar A, B)).2 = (roundStep π (A, B)).2 := by
          ext b; simp [mem_roundStep_snd, hall]
        simpa [pairDiff, hballs, hbins] using card_symmDiff_insert_le_one _ aStar
      | some b₁ =>
        have hballs : (roundStep π (insert aStar A, B)).1 = (roundStep π (A, B)).1 := by
          ext a; simp only [mem_roundStep_fst, mem_insert]
          rcases eq_or_ne a aStar with rfl | h
          exacts [by simp [haStar_new, hbin, haStar], by simp [hsame_A a h, h]]
        have hbins : (roundStep π (insert aStar A, B)).2 = (roundStep π (A, B)).2.erase b₁ := by
          ext b; simp only [mem_roundStep_snd, mem_erase]
          constructor
          · rintro ⟨hbB, hno⟩
            refine ⟨fun h => absurd (haStar_new.trans hbin) (h ▸ hno aStar), hbB, fun a => ?_⟩
            by_cases ha : a = aStar
            exacts [by simp [ha, roundMatchOpt, haStar], by simpa [hsame_A a ha] using hno a]
          · rintro ⟨hbb₁, hbB, hno⟩
            refine ⟨hbB, fun a => ?_⟩
            by_cases ha : a = aStar
            · rw [ha, haStar_new, hbin]; exact fun h => hbb₁ (Option.some.inj h).symm
            · simpa [hsame_A a ha] using hno a
        simpa [pairDiff, hballs, hbins] using card_symmDiff_erase_le_one _ b₁
  · obtain ⟨rfl, rfl⟩ := eq_empty_of_not_nonempty_activeItems hSne
    exact ⟨by simpa [roundStep_empty_bins, pairDiff] using card_symmDiff_insert_le_one ∅ aStar,
      by simp [roundMatchOpt_eq_none_of_bins_empty]⟩

private theorem insert_eq_of_symmDiff_eq_singleton {α : Type*} [DecidableEq α] {s t : Finset α}
    {x : α} (hx : s ∆ t = {x}) (hxt : x ∈ t) : t = insert x s := by
  ext z
  have := congrArg (z ∈ ·) hx
  simp only [mem_symmDiff, mem_singleton, mem_insert] at this ⊢
  grind

private theorem symmDiff_card_eq_one_cases {α : Type*} [DecidableEq α] {s t : Finset α}
    (h : (s ∆ t).card = 1) :
    (∃ x ∉ s, t = insert x s) ∨ (∃ x ∉ t, s = insert x t) := by
  rcases card_eq_one.mp h with ⟨x, hx⟩
  have hmem : x ∈ s ∆ t := hx ▸ mem_singleton_self x
  rcases mem_symmDiff.mp hmem with ⟨hxs, hxt⟩ | ⟨hxt, hxs⟩
  · exact Or.inr ⟨x, hxt, insert_eq_of_symmDiff_eq_singleton (symmDiff_comm s t ▸ hx) hxs⟩
  · exact Or.inl ⟨x, hxs, insert_eq_of_symmDiff_eq_singleton hx hxt⟩

/-- Single-round invariant of **Claim 3.4**: whenever `pairDiff AB AB' ≤ 1`, `roundStep π`
preserves `pairDiff ≤ 1` and alters at most `2` balls' single-round match assignments. -/
private theorem pairDiff_roundStep_le_one {U' n' : ℕ} (π : RoundPerm U' n')
    {AB AB' : Finset (Fin U') × Finset (Fin n')} (hp : pairDiff AB AB' ≤ 1) :
    pairDiff (roundStep π AB) (roundStep π AB') ≤ 1 ∧
      (Finset.univ.filter fun a =>
        roundMatchOpt π AB.1 AB.2 a ≠ roundMatchOpt π AB'.1 AB'.2 a).card ≤ 2 := by
  rcases AB with ⟨A, B⟩; rcases AB' with ⟨A', B'⟩; dsimp only [pairDiff] at hp
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp with h0 | h1
  · obtain rfl : A = A' := symmDiff_eq_bot.mp (card_eq_zero.mp (by omega))
    obtain rfl : B = B' := symmDiff_eq_bot.mp (card_eq_zero.mp (by omega))
    simp [pairDiff]
  · rcases (by omega : ((A ∆ A').card = 1 ∧ (B ∆ B').card = 0) ∨
        ((A ∆ A').card = 0 ∧ (B ∆ B').card = 1)) with ⟨hA1, hB0⟩ | ⟨hA0, hB1⟩
    · obtain rfl : B = B' := symmDiff_eq_bot.mp (card_eq_zero.mp hB0)
      rcases symmDiff_card_eq_one_cases hA1 with ⟨_, ha, rfl⟩ | ⟨_, ha, rfl⟩
      exacts [roundStep_insert_ball π ha B,
        by simpa only [pairDiff_comm, ne_comm] using roundStep_insert_ball π ha B]
    · obtain rfl : A = A' := symmDiff_eq_bot.mp (card_eq_zero.mp hA0)
      rcases symmDiff_card_eq_one_cases hB1 with ⟨_, hb, rfl⟩ | ⟨_, hb, rfl⟩
      · have h := roundStep_insert_bin π A hb; exact ⟨h.1, h.2.trans (by decide)⟩
      · have h := roundStep_insert_bin π A hb
        simpa only [pairDiff_comm, ne_comm] using And.intro h.1 (h.2.trans (by decide))

private theorem pairDiff_stateAt_le_one {U' n' : ℕ} (h : Scheme U' n')
    {A A' : Finset (Fin U')} {B B' : Finset (Fin n')}
    (hp : pairDiff (A, B) (A', B') ≤ 1) (i : ℕ) :
    pairDiff (stateAt h A B i) (stateAt h A' B' i) ≤ 1 := by
  induction i with
  | zero => exact hp
  | succ i ih =>
    dsimp only [stateAt]; split_ifs with hi
    exacts [(pairDiff_roundStep_le_one (h ⟨i, hi⟩) ih).1, ih]

private theorem stateAt_balls_eq_empty_of_roundsOn_le {U' n' : ℕ} (h : Scheme U' n')
    {A : Finset (Fin U')} {B : Finset (Fin n')} (hle : A.card ≤ B.card)
    {i : ℕ} (hi : roundsOn h A B ≤ i) : (stateAt h A B i).1 = ∅ := by
  by_cases hiU : i < U'
  · by_contra hne
    have hcard := card_le_card (s := Finset.range (i + 1))
      (t := (Finset.range U').filter fun j => (stateAt h A B j).1.Nonempty) fun j hj =>
      have hjle := Nat.lt_succ_iff.mp (mem_range.mp hj)
      mem_filter.mpr ⟨mem_range.mpr (hjle.trans_lt hiU),
        (ne_empty_iff_nonempty.mp hne).mono (stateAt_balls_mono h A B hjle)⟩
    rw [card_range] at hcard; dsimp only [roundsOn] at hi; omega
  · exact stateAt_balls_eq_empty h hle
      ((show A.card ≤ U' by simpa using A.card_le_univ).trans (Nat.le_of_not_lt hiU))

/-- **Claim 3.4** round-count stability ([LiLiangYuZhou2024, Section 3.1]): under a single-element
change `pairDiff (A, B) (A', B') ≤ 1`, `roundsOn h A' B' ≤ roundsOn h A B + 1`. -/
private theorem roundsOn_le_succ_of_pairDiff_le_one {U' n' : ℕ} (h : Scheme U' n')
    {A A' : Finset (Fin U')} {B B' : Finset (Fin n')}
    (hle : A.card ≤ B.card) (hle' : A'.card ≤ B'.card) (hp : pairDiff (A, B) (A', B') ≤ 1) :
    roundsOn h A' B' ≤ roundsOn h A B + 1 := by
  set T := roundsOn h A B
  have hpd := pairDiff_stateAt_le_one h hp T
  have hAT : (stateAt h A B T).1 = ∅ := stateAt_balls_eq_empty_of_roundsOn_le h hle le_rfl
  dsimp only [pairDiff] at hpd
  rw [hAT, show (∅ : Finset _) ∆ (stateAt h A' B' T).1 = (stateAt h A' B' T).1 from
    bot_symmDiff _] at hpd
  by_cases hTU : T < U'
  · have := card_stateAt_balls_succ_le_pred h hle' hTU
    exact roundsOn_le_of_stateAt_balls_eq_empty h (card_eq_zero.mp (by omega))
  · have : roundsOn h A' B' ≤ U' := (card_le_card (filter_subset _ _)).trans (by simp)
    omega

private theorem matchAux_eq_of_roundsOn_le {U' n' : ℕ} (h : Scheme U' n')
    {A : Finset (Fin U')} {B : Finset (Fin n')} (hle : A.card ≤ B.card)
    {M k : ℕ} (hRM : roundsOn h A B ≤ M) (hMk : M ≤ k) (hkU : k ≤ U') :
    matchAux h A B k = matchAux h A B M := by
  induction k with
  | zero => rw [Nat.le_zero.mp hMk]
  | succ k ih =>
    rcases eq_or_lt_of_le hMk with rfl | hMlt
    · rfl
    · have hkU' := Nat.lt_of_succ_le hkU; funext a; dsimp only [matchAux]
      rw [ih (Nat.lt_succ_iff.mp hMlt) hkU'.le]
      cases matchAux h A B M a with
      | some _ => rfl
      | none => simp [hkU', roundMatchOpt, stateAt_balls_eq_empty_of_roundsOn_le h hle
          (hRM.trans (Nat.lt_succ_iff.mp hMlt))]

/-- **Claim 3.4** relocation bound ([LiLiangYuZhou2024, Section 3.1]): under
`pairDiff (A, B) (A', B') ≤ 1`, at most `2 * (roundsOn h A B + 1)` balls change their assigned bin
(including any inserted or deleted ball). -/
private theorem relocDist_le_of_pairDiff_le_one {U' n' : ℕ} (h : Scheme U' n')
    {A A' : Finset (Fin U')} {B B' : Finset (Fin n')}
    (hle : A.card ≤ B.card) (hle' : A'.card ≤ B'.card)
    (hp : pairDiff (A, B) (A', B') ≤ 1) :
    relocDist (matchOptOn h A B) (matchOptOn h A' B') ≤ 2 * (roundsOn h A B + 1) := by
  set M := min U' (max (roundsOn h A B) (roundsOn h A' B'))
  have haux_diff : ∀ k ≤ M, relocDist (matchAux h A B k) (matchAux h A' B' k) ≤ 2 * k := by
    intro k hkM; induction k with
    | zero => simp [relocDist, matchAux]
    | succ k ih =>
      have hkU : k < U' := Nat.lt_of_succ_le (hkM.trans (min_le_left _ _))
      have hsub : (univ.filter fun a => matchAux h A B (k + 1) a ≠ matchAux h A' B' (k + 1) a) ⊆
          (univ.filter fun a => matchAux h A B k a ≠ matchAux h A' B' k a) ∪
          (univ.filter fun a =>
            roundMatchOpt (h ⟨k, hkU⟩) (stateAt h A B k).1 (stateAt h A B k).2 a ≠
              roundMatchOpt (h ⟨k, hkU⟩) (stateAt h A' B' k).1 (stateAt h A' B' k).2 a) := by
        intro a ha; simp only [mem_filter, mem_univ, true_and, mem_union] at ha ⊢
        by_contra hnot; push Not at hnot; apply ha; dsimp only [matchAux]; rw [hnot.1]
        cases matchAux h A' B' k a <;> simp [hkU, hnot.2]
      have hRk := (pairDiff_roundStep_le_one (h ⟨k, hkU⟩) (pairDiff_stateAt_le_one h hp k)).2
      exact (card_le_card hsub).trans ((card_union_le _ _).trans <| by
        have := ih (Nat.le_of_succ_le hkM); dsimp only [relocDist] at this; omega)
  have hf : matchAux h A B U' = matchAux h A B M ∧ matchAux h A' B' U' = matchAux h A' B' M := by
    by_cases hMU : M = U'
    · rw [hMU]; exact ⟨rfl, rfl⟩
    · have hmax : max (roundsOn h A B) (roundsOn h A' B') = M := (min_eq_right
        (by have := min_le_left U' (max (roundsOn h A B) (roundsOn h A' B')); omega)).symm
      exact ⟨matchAux_eq_of_roundsOn_le h hle ((le_max_left _ _).trans_eq hmax)
          (min_le_left _ _) le_rfl,
        matchAux_eq_of_roundsOn_le h hle' ((le_max_right _ _).trans_eq hmax)
          (min_le_left _ _) le_rfl⟩
  rw [matchOptOn, matchOptOn, hf.1, hf.2]
  exact (haux_diff M le_rfl).trans (Nat.mul_le_mul_left 2 <| (min_le_right _ _).trans <|
    max_le (Nat.le_succ _) (roundsOn_le_succ_of_pairDiff_le_one h hle hle' hp))

/-- Single-key insertion relocation bound (`Claim 3.4`, `B = Finset.univ`). -/
theorem relocDist_insert_le {U' n' : ℕ} (h : Scheme U' n')
    {A : Finset (Fin U')} (x : Fin U') (hins : (insert x A).card ≤ n') :
    relocDist (matchOpt h A) (matchOpt h (insert x A)) ≤ 2 * (rounds h A + 1) :=
  relocDist_le_of_pairDiff_le_one h
    (by simpa using (card_le_card (subset_insert x A)).trans hins)
    (by simpa using hins) (by simpa [pairDiff] using card_symmDiff_insert_le_one A x)

/-- Single-key deletion relocation bound (`Claim 3.4`, `B = Finset.univ`). -/
theorem relocDist_delete_le {U' n' : ℕ} (h : Scheme U' n')
    {A : Finset (Fin U')} (x : Fin U') (hA : A.card ≤ n') :
    relocDist (matchOpt h A) (matchOpt h (A.erase x)) ≤ 2 * (rounds h A + 1) :=
  relocDist_le_of_pairDiff_le_one h (by simpa using hA)
    (by simpa using card_erase_le.trans hA)
    (by simpa [pairDiff] using card_symmDiff_erase_le_one A x)

/-- Atomic key-replacement relocation bound (`Section 5.2` leaf minimap replacement
`(A \ {x}) ∪ {y}` at fixed capacity `A.card ≤ n'`): decomposes through `A.erase x` without ever
exceeding `n'` active balls. -/
theorem relocDist_replace_le {U' n' : ℕ} (h : Scheme U' n')
    {A : Finset (Fin U')} (x y : Fin U') (hA : A.card ≤ n')
    (hrep : (insert y (A.erase x)).card ≤ n') :
    relocDist (matchOpt h A) (matchOpt h (insert y (A.erase x))) ≤ 4 * rounds h A + 6 := by
  have h1 := relocDist_delete_le h x hA
  have h2 := relocDist_insert_le h (A := A.erase x) y hrep
  have hT : rounds h (A.erase x) ≤ rounds h A + 1 :=
    roundsOn_le_succ_of_pairDiff_le_one h (by simpa using hA)
      (by simpa using card_erase_le.trans hA)
      (by simpa [pairDiff] using card_symmDiff_erase_le_one A x)
  have htri := relocDist_triangle (matchOpt h A) (matchOpt h (A.erase x))
    (matchOpt h (insert y (A.erase x)))
  omega

/-- A scheme-indexed cost bounded by `a + b * rounds h A` for every scheme `h` has expectation at
most `(a + 3 b) * ⌈log₂ (max |A| 2)⌉`: average the pointwise bound and apply `expect_rounds_le`. -/
theorem expect_le_of_le_add_mul_rounds {U' n' : ℕ} {A : Finset (Fin U')}
    (hA : A.card ≤ n') (cost : Scheme U' n' → ℕ) (a b : ℕ)
    (hcost : ∀ h, cost h ≤ a + b * rounds h A) :
    (∑ h : Scheme U' n', (schemePMF U' n' h).toReal * (cost h : ℝ)) ≤
      ((a + 3 * b : ℕ) : ℝ) * (Nat.clog 2 (max A.card 2) : ℝ) := by
  have hpt : ∀ h, (cost h : ℝ) ≤ (a : ℝ) + (b : ℝ) * (rounds h A : ℝ) := fun h => by
    exact_mod_cast hcost h
  have h1 := Cslib.Probability.PMF.sum_le_affine (schemePMF U' n') hpt
  have h2 := expect_rounds_le (U' := U') hA
  have hclog1 : (1 : ℝ) ≤ Nat.clog 2 (max A.card 2) := by
    exact_mod_cast Nat.clog_pos Nat.one_lt_two (by omega : 1 < max A.card 2)
  have hb := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) b)
  have ha := mul_le_mul_of_nonneg_left hclog1 (Nat.cast_nonneg (α := ℝ) a)
  push_cast
  linarith

/-- **Lemma 3.2** ([LiLiangYuZhou2024, Section 3.1]) for ball insertion:
expected relocation cost is `O(log (max |A| 2))`. -/
theorem expect_relocDist_insert_le {U' n' : ℕ} {A : Finset (Fin U')} (x : Fin U')
    (hins : (insert x A).card ≤ n') :
    (∑ h : Scheme U' n',
      (schemePMF U' n' h).toReal * (relocDist (matchOpt h A) (matchOpt h (insert x A)) : ℝ)) ≤
      8 * (Nat.clog 2 (max A.card 2) : ℝ) := by
  have hA : A.card ≤ n' := (card_le_card (subset_insert x A)).trans hins
  refine (expect_le_of_le_add_mul_rounds hA _ 2 2 fun h => ?_).trans_eq (by norm_num)
  have := relocDist_insert_le h x hins
  omega

/-- **Lemma 3.2** for ball deletion: expected relocation cost is `O(log (max |A| 2))`. -/
theorem expect_relocDist_delete_le {U' n' : ℕ} {A : Finset (Fin U')} (x : Fin U')
    (hA : A.card ≤ n') :
    (∑ h : Scheme U' n',
      (schemePMF U' n' h).toReal * (relocDist (matchOpt h A) (matchOpt h (A.erase x)) : ℝ)) ≤
      8 * (Nat.clog 2 (max A.card 2) : ℝ) := by
  refine (expect_le_of_le_add_mul_rounds hA _ 2 2 fun h => ?_).trans_eq (by norm_num)
  have := relocDist_delete_le h x hA
  omega

/-- **Lemma 3.2** for atomic ball replacement `(A.erase x) ∪ {y}`: expected relocation cost is
`O(log (max |A| 2))`. -/
theorem expect_relocDist_replace_le {U' n' : ℕ} {A : Finset (Fin U')}
    (x y : Fin U') (hA : A.card ≤ n') (hrep : (insert y (A.erase x)).card ≤ n') :
    (∑ h : Scheme U' n',
      (schemePMF U' n' h).toReal *
        (relocDist (matchOpt h A) (matchOpt h (insert y (A.erase x))) : ℝ)) ≤
      18 * (Nat.clog 2 (max A.card 2) : ℝ) := by
  refine (expect_le_of_le_add_mul_rounds hA _ 6 4 fun h => ?_).trans_eq (by norm_num)
  have := relocDist_replace_le h x y hA hrep
  omega

end Cslib.DataStructure.Dictionary.DynamicMatching
