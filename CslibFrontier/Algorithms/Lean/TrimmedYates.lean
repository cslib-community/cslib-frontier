/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.BooleanAnalysis.CoveringProduct
public import Mathlib.Data.List.Sublists
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Trimmed Yates passes and selected entries of the subset convolution

Selected entries of the ranked subset convolution by the trimmed fast zeta transform, following
the proof of [ChanItakuraMaYu2026], Theorem 2.2 (Section 2.1), after
[BjorklundHusfeldtKaskiKoivisto2007] and the trimmed transform of
[BjorklundHusfeldtKaskiKoivisto2010] cited there.

Fix a duplicate-free list `l` of coordinates and a threshold `s`. Stage `k` of Yates's algorithm on
`F` is `yatesTransform c (l.take k) F`; its value at `X` reads stage `k - 1` only at `X` and at `X`
minus one coordinate.

* **Preprocessing** (`preprocess`) runs every stage of the zeta transforms of `f` and `g`, of
  their pointwise product and of its Möbius transform on the *low* sets: the subsets of `l` with at
  most `s` elements (`layers l 0 s`), keeping every stage (`Tables`).
* **A query** `C` (`query`) runs the same stages on the *high* sets of `C`: its subsets with at
  least `s` elements (`layers (l.filter (· ∈ C)) s #C`). A value at a set with fewer than `s`
  elements is read from the preprocessed stage of the same index (`stages`).

The query returns the covering product `coveringProduct f g C` (`query_preprocess`), which for
ranked inputs and `#C = t₁ + t₂` is the subset convolution
(`query_preprocess_eq_subsetConvolution`). `solve` answers a list of queries after one
preprocessing (`solve_eq_subsetConvolution`).

This module defines the pure mathematical algorithm and proves its correctness over any commutative
ring. The Word-RAM implementation and running-time bound of [ChanItakuraMaYu2026], Theorem 2.2 are
in `CslibFrontier.Algorithms.WordRAM.TrimmedYates`.

## Main definitions

* `Cslib.Algorithms.Lean.TrimmedYates.tabulate`: finite association-list lookup table on a domain.
* `Cslib.Algorithms.Lean.TrimmedYates.layers`: the subsets of a list with a given range of sizes.
* `Cslib.Algorithms.Lean.TrimmedYates.stages`: Yates's passes on a domain of sets, with a
  fallback table for small sets.
* `Cslib.Algorithms.Lean.TrimmedYates.Tables`, `preprocess`, `query`, `solve`: selected
  entries of the covering product and ranked subset convolution.

## Main results

* `Cslib.Algorithms.Lean.TrimmedYates.getD_stages`: correctness of the trimmed passes.
* `Cslib.Algorithms.Lean.TrimmedYates.query_preprocess`,
  `query_preprocess_eq_subsetConvolution`, `solve_eq_subsetConvolution`: the queries return selected
  entries of the covering product, and of the subset convolution for ranked inputs.

## References

* [A. Björklund, T. Husfeldt, P. Kaski, M. Koivisto, *Fourier meets Möbius: fast subset
  convolution*][BjorklundHusfeldtKaskiKoivisto2007]
* [A. Björklund, T. Husfeldt, P. Kaski, M. Koivisto, *Trimmed Moebius inversion and graphs of
  bounded degree*][BjorklundHusfeldtKaskiKoivisto2010]
* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.Lean.TrimmedYates

open Finset Cslib.BitString

/-! ### Tables -/

section Tabulate

variable {κ M : Type*} [DecidableEq κ] [Zero M]

/-- The lookup table of `cell` on the keys `dom`: a finite association-list map from each key of
`dom` to its value, read as `0` off `dom`. -/
@[expose] def tabulate (dom : List κ) (cell : κ → M) : κ → M :=
  let tbl := dom.zip (dom.map cell)
  fun X : κ => (tbl.lookup X).getD 0

/-- The table of `cell` reads `cell X` at every key `X` of `dom`. -/
theorem tabulate_apply {dom : List κ} (cell : κ → M) {X : κ} (hX : X ∈ dom) :
    tabulate dom cell X = cell X := by
  dsimp only [tabulate]
  induction dom with
  | nil => simp at hX
  | cons Y dom ih =>
    rw [List.map_cons, List.zip_cons_cons, List.lookup_cons]
    by_cases h : X = Y
    · subst h
      simp
    · rw [beq_false_of_ne h]
      exact ih ((List.mem_cons.mp hX).resolve_left h)

end Tabulate

/-! ### Layers of subsets -/

section Layers

variable {ι : Type*} [DecidableEq ι]

/-- The subsets of the elements of `L` with at least `lo` and at most `hi` elements, layer by
layer, each as the set of a sublist of `L`. -/
@[expose] def layers (L : List ι) (lo hi : ℕ) : List (Finset ι) :=
  (List.range' lo (hi + 1 - lo)).flatMap fun j => (L.sublistsLen j).map List.toFinset

theorem mem_layers {L : List ι} (hL : L.Nodup) {lo hi : ℕ} {X : Finset ι} :
    X ∈ layers L lo hi ↔ X ⊆ L.toFinset ∧ lo ≤ #X ∧ #X ≤ hi := by
  simp only [layers, List.mem_flatMap, List.mem_range'_1, List.mem_map, List.mem_sublistsLen]
  constructor
  · rintro ⟨j, hj, L', ⟨hsub, hlen⟩, rfl⟩
    have hnd : L'.Nodup := hL.sublist hsub
    rw [List.toFinset_card_of_nodup hnd, hlen]
    exact ⟨fun x hx => List.mem_toFinset.mpr (hsub.subset (List.mem_toFinset.mp hx)),
      hj.1, by omega⟩
  · rintro ⟨hX, hlo, hhi⟩
    refine ⟨#X, ⟨hlo, by omega⟩, L.filter (· ∈ X), ⟨List.filter_sublist, ?_⟩, ?_⟩
    · rw [← List.toFinset_card_of_nodup (hL.filter _), List.toFinset_filter]
      congr 1
      ext x
      simp only [mem_filter, List.mem_toFinset, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (hX h), h⟩⟩
    · ext x
      simp only [List.toFinset_filter, mem_filter, List.mem_toFinset, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (hX h), h⟩⟩

/-- There are `∑_{lo ≤ j ≤ hi} (L.length choose j)` layered subsets. -/
theorem length_layers (L : List ι) (lo hi : ℕ) :
    (layers L lo hi).length = ∑ j ∈ Icc lo hi, L.length.choose j := by
  rw [layers, List.length_flatMap]
  simp only [List.length_map, List.length_sublistsLen]
  rw [← List.sum_toFinset _ List.nodup_range']
  congr 1
  ext j
  simp only [List.mem_toFinset, List.mem_range'_1, mem_Icc]
  omega

end Layers

/-! ### Trimmed passes -/

section Stages

variable {ι M R : Type*} [DecidableEq ι] [AddCommMonoid M] [Monoid R] [DistribMulAction R M]

/-- Yates's passes with coefficient `c` in the coordinates `l`, on the cells `dom`, returning
every stage: stage `0` is `t`, and stage `k + 1` is the pass in coordinate `k` of `l` applied to
stage `k`. A cell reads stage `k` at sets with at least `s` elements and the `k`-th table of `fb`
at smaller sets. -/
@[expose] def stages (c : R) (s : ℕ) (dom : List (Finset ι)) :
    List ι → List (Finset ι → M) → (Finset ι → M) → List (Finset ι → M)
  | [], _, t => [t]
  | i :: l, fb, t =>
    let t' := tabulate dom (yatesPass c i fun Y => if s ≤ #Y then t Y else fb.headD 0 Y)
    t :: stages c s dom l fb.tail t'

/-- **Correctness of the trimmed passes.** Suppose that every cell of `dom` has at least `s`
elements, that `t` agrees with `G` on `dom`, and that removing a coordinate of `l` from a cell gives
a cell or a set satisfying `P` with fewer than `s` elements. If the `k`-th table of `fb` agrees
with stage `k` of `G` on the sets satisfying `P` with fewer than `s` elements, then every returned
stage `k ≤ l.length` agrees with stage `k` of `G` on `dom`. -/
theorem getD_stages (c : R) {s : ℕ} {dom : List (Finset ι)} (P : Finset ι → Prop)
    (hs : ∀ X ∈ dom, s ≤ #X)
    (hdom : ∀ X ∈ dom, ∀ i, i ∈ X → (s ≤ #(X.erase i) → X.erase i ∈ dom) ∧
      (#(X.erase i) < s → P (X.erase i))) :
    ∀ (l : List ι) (fb : List (Finset ι → M)) (t G : Finset ι → M),
      (∀ X ∈ dom, t X = G X) →
      (∀ k < l.length, ∀ Y, #Y < s → P Y → fb.getD k 0 Y = yatesTransform c (l.take k) G Y) →
      ∀ k ≤ l.length, ∀ X ∈ dom,
        (stages c s dom l fb t).getD k 0 X = yatesTransform c (l.take k) G X
  | [], _, t, G, ht, _, k, hk, X, hX => by
    obtain rfl : k = 0 := by simpa using hk
    simpa [stages] using ht X hX
  | i :: l, fb, t, G, ht, hfb, k, hk, X, hX => by
    set rd : Finset ι → M := fun Y => if s ≤ #Y then t Y else fb.headD 0 Y
    have hrd : ∀ Y, (s ≤ #Y → Y ∈ dom) → (#Y < s → P Y) → rd Y = G Y := by
      intro Y hY hP
      by_cases h : s ≤ #Y
      · simp only [rd, h, ↓reduceIte]
        exact ht Y (hY h)
      · simp only [rd, h, ↓reduceIte]
        have := hfb 0 (by simp) Y (by omega) (hP (by omega))
        simpa [List.getD_eq_getElem?_getD, List.head?_eq_getElem?] using this
    have ht' : ∀ X ∈ dom, tabulate dom (yatesPass c i rd) X = yatesPass c i G X := by
      intro X hX
      rw [tabulate_apply _ hX, yatesPass, yatesPass,
        hrd X (fun _ => hX) fun h => absurd (hs X hX) (by omega)]
      split_ifs with hiX
      · rw [hrd (X.erase i) (hdom X hX i hiX).1 (hdom X hX i hiX).2]
      · rfl
    have hfb' : ∀ k < l.length, ∀ Y, #Y < s → P Y →
        fb.tail.getD k 0 Y = yatesTransform c (l.take k) (yatesPass c i G) Y := by
      intro k hk Y hY hP
      have := hfb (k + 1) (by simp; omega) Y hY hP
      rw [List.take_succ_cons, yatesTransform_cons] at this
      rw [← this, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_tail]
    dsimp only [stages]
    rcases k with _ | k
    · simpa using ht X hX
    · rw [List.getD_cons_succ, List.take_succ_cons, yatesTransform_cons]
      exact getD_stages c P hs hdom l fb.tail _ _ ht' hfb' k (by simpa using hk) X hX

end Stages

/-! ### Selected entries of the covering product -/

/-- The tables kept by the preprocessing phase: every stage of the trimmed transforms on the sets
with at most `s` elements. -/
structure Tables (ι M : Type*) where
  /-- Stage `k` of the zeta transform of the left input. -/
  zetaLeft : List (Finset ι → M)
  /-- Stage `k` of the zeta transform of the right input. -/
  zetaRight : List (Finset ι → M)
  /-- Stage `k` of the Möbius transform of the pointwise product of the two zeta transforms. -/
  cover : List (Finset ι → M)

variable {ι R : Type*} [DecidableEq ι] [CommRing R]

/-- The **preprocessing phase**: every stage of the zeta transforms of `f` and `g`, and of the
Möbius transform of their pointwise product, on the subsets of `l` with at most `s` elements. -/
@[expose] def preprocess (l : List ι) (s : ℕ) (f g : Finset ι → R) : Tables ι R :=
  let low := layers l 0 s
  let f₀ := tabulate low f
  let fs := stages (1 : ℕ) 0 low l [] f₀
  let g₀ := tabulate low g
  let gs := stages (1 : ℕ) 0 low l [] g₀
  let h₀ := tabulate low fun X => fs.getD l.length 0 X * gs.getD l.length 0 X
  let hs := stages (-1 : ℤ) 0 low l [] h₀
  ⟨fs, gs, hs⟩

/-- The **query phase** for `C`: the same stages on the subsets of `C` with at least `s` elements,
reading the preprocessed stages `T` at smaller sets. Returns the last stage at `C`. -/
@[expose] def query (l : List ι) (s : ℕ) (T : Tables ι R) (f g : Finset ι → R)
    (C : Finset ι) : R :=
  let high := layers (l.filter (· ∈ C)) s #C
  let f₀ := tabulate high f
  let fs := stages (1 : ℕ) s high l T.zetaLeft f₀
  let g₀ := tabulate high g
  let gs := stages (1 : ℕ) s high l T.zetaRight g₀
  let h₀ := tabulate high fun X => fs.getD l.length 0 X * gs.getD l.length 0 X
  let hs := stages (-1 : ℤ) s high l T.cover h₀
  hs.getD l.length 0 C

/-- **Selected entries of the covering product**: preprocess once, then answer each query. -/
@[expose] def solve (l : List ι) (s : ℕ) (f g : Finset ι → R) (Cs : List (Finset ι)) :
    List R :=
  let T := preprocess l s f g
  Cs.map (query l s T f g)

/-! #### Correctness -/

/-- The stages of the zeta transform reach `subsetZeta` once every coordinate is processed. -/
private theorem yatesTransform_one_take_length {l : List ι} (hl : l.Nodup) (F : Finset ι → R)
    {X : Finset ι} (hX : X ⊆ l.toFinset) :
    yatesTransform (1 : ℕ) (l.take l.length) F X = subsetZeta F X := by
  rw [List.take_length, yatesTransform_one_apply hl F hX]

/-- What the preprocessed tables hold: stage `k` of each transform on the subsets of `l` with at
most `s` elements. -/
private theorem preprocess_spec {l : List ι} (hl : l.Nodup) (s : ℕ) (f g : Finset ι → R) :
    let T := preprocess l s f g
    let H : Finset ι → R := fun S => subsetZeta f S * subsetZeta g S
    ∀ k ≤ l.length, ∀ X, X ⊆ l.toFinset → #X ≤ s →
      T.zetaLeft.getD k 0 X = yatesTransform (1 : ℕ) (l.take k) f X ∧
      T.zetaRight.getD k 0 X = yatesTransform (1 : ℕ) (l.take k) g X ∧
      T.cover.getD k 0 X = yatesTransform (-1 : ℤ) (l.take k) H X := by
  intro T H k hk X hXl hXs
  have hlow : ∀ {Y}, Y ∈ layers l 0 s ↔ Y ⊆ l.toFinset ∧ #Y ≤ s := by
    intro Y; rw [mem_layers hl]; simp
  have hs : ∀ X ∈ layers l 0 s, 0 ≤ #X := fun _ _ => Nat.zero_le _
  have hdom : ∀ X ∈ layers l 0 s, ∀ i, i ∈ X → (0 ≤ #(X.erase i) → X.erase i ∈ layers l 0 s) ∧
      (#(X.erase i) < 0 → False) := by
    intro X hX i _
    refine ⟨fun _ => hlow.mpr ⟨(erase_subset i X).trans (hlow.mp hX).1, ?_⟩, by omega⟩
    exact (card_erase_le).trans (hlow.mp hX).2
  have hX : X ∈ layers l 0 s := hlow.mpr ⟨hXl, hXs⟩
  have stage := fun {R' : Type _} [Monoid R'] [DistribMulAction R' R] (c' : R') (t G : Finset ι → R)
      (ht : ∀ X ∈ layers l 0 s, t X = G X) =>
    getD_stages (M := R) c' (fun _ => False) hs hdom l [] t G ht
      (fun _ _ _ hY _ => absurd hY (Nat.not_lt_zero _))
  have hf := stage (1 : ℕ) _ f fun Y hY => tabulate_apply f hY
  have hg := stage (1 : ℕ) _ g fun Y hY => tabulate_apply g hY
  refine ⟨hf k hk X hX, hg k hk X hX, stage (-1 : ℤ) _ H (fun Y hY => ?_) k hk X hX⟩
  rw [tabulate_apply _ hY, hf _ le_rfl Y hY, hg _ le_rfl Y hY,
    yatesTransform_one_take_length hl f (hlow.mp hY).1,
    yatesTransform_one_take_length hl g (hlow.mp hY).1]

/-- **Correctness of a query**: if `C` is a set of coordinates of `l` with at least `s` elements,
the query after preprocessing returns the covering product `coveringProduct f g C`. -/
theorem query_preprocess {l : List ι} (hl : l.Nodup) {s : ℕ} (f g : Finset ι → R)
    {C : Finset ι} (hC : C ⊆ l.toFinset) (hsC : s ≤ #C) :
    query l s (preprocess l s f g) f g C = coveringProduct f g C := by
  have pre := preprocess_spec hl s f g
  set T := preprocess l s f g
  set H : Finset ι → R := fun S => subsetZeta f S * subsetZeta g S
  have hCl : (l.filter (· ∈ C)).toFinset = C := by
    ext x
    simp only [List.toFinset_filter, mem_filter, List.mem_toFinset, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (hC h), h⟩⟩
  have hhigh : ∀ {Y}, Y ∈ layers (l.filter (· ∈ C)) s #C ↔ Y ⊆ C ∧ s ≤ #Y := by
    intro Y
    rw [mem_layers (hl.filter _), hCl]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, card_le_card h.1⟩⟩
  have hs : ∀ X ∈ layers (l.filter (· ∈ C)) s #C, s ≤ #X := fun X hX => (hhigh.mp hX).2
  let P : Finset ι → Prop := fun Y => Y ⊆ l.toFinset ∧ #Y ≤ s
  have hdom : ∀ X ∈ layers (l.filter (· ∈ C)) s #C, ∀ i, i ∈ X →
      (s ≤ #(X.erase i) → X.erase i ∈ layers (l.filter (· ∈ C)) s #C) ∧
      (#(X.erase i) < s → P (X.erase i)) := by
    intro X hX i _
    have hXC := (hhigh.mp hX).1
    exact ⟨fun h => hhigh.mpr ⟨(erase_subset i X).trans hXC, h⟩,
      fun h => ⟨(erase_subset i X).trans (hXC.trans hC), by omega⟩⟩
  have hYl : ∀ {Y}, Y ∈ layers (l.filter (· ∈ C)) s #C → Y ⊆ l.toFinset :=
    fun hY => (hhigh.mp hY).1.trans hC
  have hf := getD_stages (1 : ℕ) P hs hdom l T.zetaLeft
    (tabulate (layers (l.filter (· ∈ C)) s #C) f) f
    (fun Y hY => tabulate_apply f hY) fun k hk Y _ hP => (pre k hk.le Y hP.1 hP.2).1
  have hg := getD_stages (1 : ℕ) P hs hdom l T.zetaRight
    (tabulate (layers (l.filter (· ∈ C)) s #C) g) g
    (fun Y hY => tabulate_apply g hY) fun k hk Y _ hP => (pre k hk.le Y hP.1 hP.2).2.1
  have hCmem : C ∈ layers (l.filter (· ∈ C)) s #C := hhigh.mpr ⟨subset_rfl, hsC⟩
  dsimp only [query]
  rw [getD_stages (-1 : ℤ) P hs hdom l T.cover _ H ?_
      (fun k hk Y _ hP => (pre k hk.le Y hP.1 hP.2).2.2) _ le_rfl C hCmem,
    List.take_length, yatesTransform_neg_one_apply hl H hC, coveringProduct_eq_subsetMobius]
  intro Y hY
  rw [tabulate_apply _ hY, hf _ le_rfl Y hY, hg _ le_rfl Y hY,
    yatesTransform_one_take_length hl f (hYl hY), yatesTransform_one_take_length hl g (hYl hY)]

/-- **Ranked queries** ([ChanItakuraMaYu2026], Problem 2.1): if `f` is supported on sets with `t₁`
elements and `g` on sets with `t₂` elements, a query at a set `C` of `t₁ + t₂` coordinates of `l`
returns the subset convolution `∑_{A ⊆ C} f A * g (C \ A)`, for every threshold
`s ≤ t₁ + t₂`. -/
theorem query_preprocess_eq_subsetConvolution {l : List ι} (hl : l.Nodup) {s t₁ t₂ : ℕ}
    {f g : Finset ι → R} (hf : ∀ A, f A ≠ 0 → #A = t₁) (hg : ∀ B, g B ≠ 0 → #B = t₂)
    {C : Finset ι} (hC : C ⊆ l.toFinset) (hCcard : #C = t₁ + t₂) (hs : s ≤ t₁ + t₂) :
    query l s (preprocess l s f g) f g C = subsetConvolution f g C := by
  rw [query_preprocess hl f g hC (hCcard ▸ hs),
    coveringProduct_eq_subsetConvolution hf hg hCcard]

/-- **Correctness of `solve`**: for queries at sets of `t₁ + t₂` coordinates of `l`, the answers
are the selected entries of the subset convolution of ranked inputs. -/
theorem solve_eq_subsetConvolution {l : List ι} (hl : l.Nodup) {s t₁ t₂ : ℕ} {f g : Finset ι → R}
    (hf : ∀ A, f A ≠ 0 → #A = t₁) (hg : ∀ B, g B ≠ 0 → #B = t₂) {Cs : List (Finset ι)}
    (hCs : ∀ C ∈ Cs, C ⊆ l.toFinset ∧ #C = t₁ + t₂) (hs : s ≤ t₁ + t₂) :
    solve l s f g Cs = Cs.map (subsetConvolution f g) := by
  dsimp only [solve]
  refine List.map_congr_left fun C hC => ?_
  exact query_preprocess_eq_subsetConvolution hl hf hg (hCs C hC).1 (hCs C hC).2 hs

end Cslib.Algorithms.Lean.TrimmedYates
