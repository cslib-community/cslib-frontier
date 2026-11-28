/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.MachineLearning.PACLearning.NatarajanDimension
public import CslibFrontier.MachineLearning.PACLearning.Halfspaces

/-!
# Checks for the Natarajan dimension

Exercises `CslibFrontier.MachineLearning.PACLearning.NatarajanDimension`:

* **All labelings:** with two distinct labels, the class of all functions N-shatters every set.
  On a finite domain its Natarajan dimension is the number of points, and with `Bool` labels on
  three points Natarajan's lemma is attained.
* **Constant functions:** they N-shatter a single point and never two points, so their Natarajan
  dimension is `1`. Natarajan's lemma then bounds every class on four points with three labels and
  Natarajan dimension at most `1` by `13`, far below the `81` functions.
* **Two labels (`Bool` and `Fin 2`):** the Natarajan dimension of homogeneous halfspaces in the
  plane (and their `Fin 2`-relabeled copy) is their VC dimension `2`, and at `k = 2` labels
  Natarajan's lemma reduces directly via `natarajanSum_two` to the standard Sauer–Shelah bound.
* **Multiclass point indicators (`k = 3`):** single-point spikes over default label `0` N-shatter
  every singleton and no two-point set (`natarajanDim = 1`), with `9` concepts on `Fin 4`
  (exceeding binary Sauer–Shelah's `5` while bounded by `natarajanSum 4 3 1 = 13`).
* **Ordered two-threshold linear classifiers (`k = 3`):** `x ↦ 0 / 1 / 2` on `ℤ` N-shatter `{0, 1}`
  using all three labels (`f₀ = (0, 1)`, `f₁ = (1, 2)`) and never three points, giving
  `natarajanDim = 2`.
* **Growth counterexamples (`k = 3`):** unlike `k = 2`, `natarajanSum 1 3 1 = 4` strictly exceeds
  `|Fin 1 → Fin 3| = 3`, and the 6-cycle class `cycleSix : ConceptClass (Fin 2) (Fin 3)` has
  `6 > 2 ^ 2` labelings on two points while having `natarajanDim = 1`.
-/

public section

namespace CslibFrontierTests.NatarajanDimension

open Cslib.MachineLearning.PACLearning

variable {α β : Type*}

/-- With two distinct labels the class of all functions N-shatters every set: the constant
labelings witness it, and for `B ⊆ W` the indicator of `B` realizes `B`. -/
theorem natarajanShatters_univ {b₀ b₁ : β} (hb : b₀ ≠ b₁) (W : Set α) :
    NatarajanShatters (Set.univ : ConceptClass α β) W := by
  classical
  refine ⟨fun _ => b₀, fun _ => b₁, fun _ _ => hb, fun B _ => ?_⟩
  exact ⟨fun x => if x ∈ B then b₀ else b₁, Set.mem_univ _, fun x hx => by simp [hx],
    fun x hx => by simp [hx.2]⟩

/-- On a finite domain, the class of all functions to a type with two labels has Natarajan
dimension equal to the number of points. -/
theorem natarajanDim_univ [Fintype α] {b₀ b₁ : β} (hb : b₀ ≠ b₁) :
    natarajanDim (Set.univ : ConceptClass α β) = Fintype.card α :=
  le_antisymm (natarajanDim_le_iff.mpr fun W _ => Nat.cast_le.mpr W.card_le_univ)
    (by simpa using (natarajanShatters_univ hb _).card_le_natarajanDim (W := Finset.univ))

/-- All Boolean functions on the naturals shatter finite sets of every size. -/
example : evcDim (Set.univ : ConceptClass ℕ Bool) = ⊤ := by
  rw [← natarajanDim_eq_evcDim]
  apply ENat.eq_top_iff_forall_ge.mpr
  intro n
  simpa using (natarajanShatters_univ Bool.false_ne_true _).card_le_natarajanDim
    (W := Finset.range n)

example : natarajanDim (Set.univ : ConceptClass (Fin 5) (Fin 3)) = 5 := by
  simpa using natarajanDim_univ (α := Fin 5) (β := Fin 3) (b₀ := 0) (b₁ := 1) (by decide)

/-- With `Bool` labels on three points the bound of Natarajan's lemma is attained by the class of
all `8` functions. -/
example : (Set.univ : ConceptClass (Fin 3) Bool).ncard = natarajanSum 3 (Fintype.card Bool) 3 := by
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool]
  decide

/-- The constant functions. -/
def constants (β : Type*) : ConceptClass α β := Set.range fun b : β => fun _ : α => b

/-- The constant functions N-shatter no two-point set: the labeling that agrees with the first
witness at one point and with the second at the other cannot be constant. -/
theorem not_natarajanShatters_constants_pair {x y : α} (hxy : x ≠ y) :
    ¬ NatarajanShatters (constants (α := α) β) {x, y} := by
  rintro ⟨f₀, f₁, hne, h⟩
  obtain ⟨_, ⟨b, rfl⟩, -, h₁⟩ := h ∅ (Set.empty_subset _)
  obtain ⟨_, ⟨b', rfl⟩, h₀', h₁'⟩ := h {x} (by simp)
  have hx : b = f₁ x := h₁ x ⟨by simp, Set.notMem_empty x⟩
  have hy : b = f₁ y := h₁ y ⟨by simp, Set.notMem_empty y⟩
  have hx' : b' = f₀ x := h₀' x rfl
  have hy' : b' = f₁ y := h₁' y ⟨by simp, fun h => hxy (Set.mem_singleton_iff.1 h).symm⟩
  exact hne x (by simp) (by rw [← hx', hy', ← hy, hx])

/-- With two distinct labels the constant functions N-shatter every single point. -/
theorem natarajanShatters_constants_singleton {b₀ b₁ : β} (hb : b₀ ≠ b₁) (x : α) :
    NatarajanShatters (constants (α := α) β) {x} := by
  classical
  refine ⟨fun _ => b₀, fun _ => b₁, fun _ _ => hb, fun B hB => ?_⟩
  by_cases hx : x ∈ B
  · refine ⟨fun _ => b₀, ⟨b₀, rfl⟩, fun _ _ => rfl, fun y hy => ?_⟩
    exact absurd (Set.mem_singleton_iff.1 hy.1 ▸ hx) hy.2
  · refine ⟨fun _ => b₁, ⟨b₁, rfl⟩, fun y hy => ?_, fun _ _ => rfl⟩
    exact absurd (Set.mem_singleton_iff.1 (hB hy) ▸ hy) hx

/-- Every finite set N-shattered by the constant functions has at most one point. -/
theorem card_le_one_of_natarajanShatters_constants {W : Finset α}
    (hW : NatarajanShatters (constants (α := α) β) ↑W) : W.card ≤ 1 := by
  by_contra h
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (not_le.1 h)
  exact not_natarajanShatters_constants_pair hxy
    (hW.subset (by simp [Set.insert_subset_iff, hx, hy]))

/-- With at least two labels the constant functions on a nonempty domain have Natarajan
dimension `1`. -/
theorem natarajanDim_constants [Nonempty α] {b₀ b₁ : β} (hb : b₀ ≠ b₁) :
    natarajanDim (constants (α := α) β) = 1 := by
  obtain ⟨x⟩ := ‹Nonempty α›
  refine le_antisymm (natarajanDim_le_iff.mpr fun W hW => ?_) ?_
  · exact_mod_cast card_le_one_of_natarajanShatters_constants hW
  have h := natarajanShatters_constants_singleton (α := α) hb x
  rw [← Finset.coe_singleton] at h
  simpa using h.card_le_natarajanDim

/-- Natarajan's lemma on four points with three labels: a class whose N-shattered sets have at
most one point has at most `1 + 4 · 3 = 13` of the `81` functions. -/
theorem ncard_le_thirteen {C : ConceptClass (Fin 4) (Fin 3)}
    (hC : ∀ W : Finset (Fin 4), NatarajanShatters C ↑W → W.card ≤ 1) : C.ncard ≤ 13 :=
  (ncard_le_natarajanSum hC).trans (by rw [Fintype.card_fin]; decide)

/-- The constant functions on four points satisfy the hypothesis of `ncard_le_thirteen`. -/
example : (constants (α := Fin 4) (Fin 3)).ncard ≤ 13 :=
  ncard_le_thirteen fun _ hW => card_le_one_of_natarajanShatters_constants hW

/-- All `81` functions from four points to three labels N-shatter a two-point set, so
`ncard_le_thirteen` does not apply to them. -/
example : NatarajanShatters (Set.univ : ConceptClass (Fin 4) (Fin 3)) ↑({0, 1} : Finset (Fin 4)) :=
  natarajanShatters_univ (b₀ := 0) (b₁ := 1) (by decide) _

/-- With two labels the Natarajan dimension is the VC dimension: homogeneous halfspaces in the
plane have Natarajan dimension `2`. -/
example : natarajanDim (homogeneousHalfspaces 2) = 2 := by
  rw [natarajanDim_eq_evcDim, ← natCast_vcDim, vcDim_homogeneousHalfspaces]
  · norm_num
  · rw [homogeneousHalfspaces_eq_positivityClass]
    exact hasFiniteVCDim_positivityClass _

/-! ### Binary (`k = 2` / `Fin 2`) consistency with VC dimension and Sauer–Shelah -/

/-- For `Fin 2`-valued concept classes, `natarajanDim` agrees with `evcDim` via `finTwoEquiv`. -/
theorem natarajanDim_fin_two_eq_evcDim (C : ConceptClass α (Fin 2)) :
    natarajanDim C = evcDim ((finTwoEquiv ∘ ·) '' C) :=
  natarajanDim_eq_evcDim_of_equiv C finTwoEquiv

/-- Relabeling planar homogeneous halfspaces to `Fin 2` preserves Natarajan dimension `2`. -/
example : natarajanDim ((finTwoEquiv.symm ∘ ·) '' homogeneousHalfspaces 2) = 2 := by
  rw [natarajanDim_image_equiv_comp, natarajanDim_eq_evcDim, ← natCast_vcDim,
    vcDim_homogeneousHalfspaces]
  · norm_num
  · rw [homogeneousHalfspaces_eq_positivityClass]
    exact hasFiniteVCDim_positivityClass _

/-- At `k = 2` (`Bool`), `ncard_restriction_le_natarajanSum` reduces cleanly via
`natarajanShatters_iff_setShatters` and `natarajanSum_two` to the standard Sauer–Shelah bound
`∑_{i ≤ d} (m choose i)`. -/
theorem ncard_restriction_bool_le_sauer_via_natarajan {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) {m : ℕ} (x : Fin m → α) :
    ((· ∘ x) '' C).ncard ≤ ∑ i ∈ Finset.range (d + 1), m.choose i := by
  simpa [Fintype.card_bool, natarajanSum_two] using
    ncard_restriction_le_natarajanSum
      (fun W hW => hC W (natarajanShatters_iff_setShatters.1 hW)) x

/-! ### Multiclass singleton / point-indicator class (`k = 3`) -/

/-- Multiclass point-indicator concepts with background label `0`: the all-`0` function together
with every single-point spike `x ↦ if x = a then b else 0`. -/
def pointIndicators (α : Type*) [DecidableEq α] (k : ℕ) [NeZero k] : ConceptClass α (Fin k) :=
  {fun _ => 0} ∪ Set.range fun p : α × Fin k => fun x => if x = p.1 then p.2 else 0

/-- With a nonzero label `b ≠ 0`, `pointIndicators` N-shatters every singleton `{x}`. -/
theorem natarajanShatters_pointIndicators_singleton [DecidableEq α] {k : ℕ} [NeZero k]
    {b : Fin k} (hb : b ≠ 0) (x : α) :
    NatarajanShatters (pointIndicators α k) {x} := by
  classical
  refine ⟨fun _ => b, fun _ => 0, fun _ _ => hb, fun B hB => ?_⟩
  by_cases hx : x ∈ B
  · refine ⟨fun z => if z = x then b else 0, Or.inr ⟨(x, b), rfl⟩, fun z hz => ?_, fun z hz => ?_⟩
    · simp [Set.mem_singleton_iff.1 (hB hz)]
    · exact absurd (Set.mem_singleton_iff.1 hz.1 ▸ hx) hz.2
  · refine ⟨fun _ => 0, Or.inl rfl, fun z hz => ?_, fun _ _ => rfl⟩
    exact absurd (Set.mem_singleton_iff.1 (hB hz) ▸ hz) hx

/-- `pointIndicators` never N-shatters two distinct points: every concept is `0` at one of `x, y`,
whereas any N-shattering pair `(f₀, f₁)` admits a target labeling nonzero at both `x` and `y`. -/
theorem not_natarajanShatters_pointIndicators_pair [DecidableEq α] {k : ℕ} [NeZero k] {x y : α}
    (hxy : x ≠ y) : ¬ NatarajanShatters (pointIndicators α k) {x, y} := by
  rintro ⟨f₀, f₁, hne, h⟩
  obtain ⟨c, hc, h₀, h₁⟩ :=
    h {z ∈ ({x, y} : Set α) | f₀ z ≠ 0} (fun _ hz => hz.1)
  have hcz : ∀ z ∈ ({x, y} : Set α), c z ≠ 0 := by
    intro z hz
    by_cases hfz : f₀ z ≠ 0
    · rw [h₀ z ⟨hz, hfz⟩]
      exact hfz
    · push Not at hfz
      have hz' : c z = f₁ z := h₁ z ⟨hz, fun hB => hB.2 hfz⟩
      rw [hz']
      exact fun h1 => hne z hz (hfz.trans h1.symm)
  have hcx : c x ≠ 0 := hcz x (by simp)
  have hcy : c y ≠ 0 := hcz y (by simp)
  rcases hc with rfl | ⟨⟨a, b⟩, rfl⟩
  · exact hcx rfl
  · by_cases hxa : x = a
    · subst hxa
      exact hcy (ite_eq_right hxy.symm)
    · exact hcx (ite_eq_right hxa)

/-- Every finite set N-shattered by `pointIndicators α k` has at most one element. -/
theorem card_le_one_of_natarajanShatters_pointIndicators [DecidableEq α] {k : ℕ} [NeZero k]
    {W : Finset α} (hW : NatarajanShatters (pointIndicators α k) ↑W) : W.card ≤ 1 := by
  by_contra h
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (not_le.1 h)
  exact not_natarajanShatters_pointIndicators_pair hxy
    (hW.subset (by simp [Set.insert_subset_iff, hx, hy]))

/-- For `k ≥ 2` on a nonempty domain, `pointIndicators α k` has Natarajan dimension `1`. -/
theorem natarajanDim_pointIndicators [DecidableEq α] [Nonempty α] {k : ℕ} [NeZero k]
    {b : Fin k} (hb : b ≠ 0) : natarajanDim (pointIndicators α k) = 1 := by
  obtain ⟨x⟩ := ‹Nonempty α›
  refine le_antisymm (natarajanDim_le_iff.mpr fun W hW => ?_) ?_
  · exact_mod_cast card_le_one_of_natarajanShatters_pointIndicators hW
  · have h := natarajanShatters_pointIndicators_singleton (α := α) hb x
    rw [← Finset.coe_singleton] at h
    simpa using h.card_le_natarajanDim

example : natarajanDim (pointIndicators ℕ 3) = 1 :=
  natarajanDim_pointIndicators (b := (1 : Fin 3)) (by decide)

/-- On four points with `k = 3` labels, `pointIndicators (Fin 4) 3` has `9` functions: strictly
more than the binary `d = 1` Sauer–Shelah bound `natarajanSum 4 2 1 = 5`, while bounded by
`natarajanSum 4 3 1 = 13`. -/
theorem ncard_pointIndicators_fin4_three : (pointIndicators (Fin 4) 3).ncard = 9 := by
  classical
  rw [Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
  have hcard :
      (Finset.univ.filter fun c : Fin 4 → Fin 3 =>
        ∃ a b, ∀ x, (if x = a then b else 0) = c x).card = 9 := by
    decide
  convert hcard
  ext c
  simp only [Set.Finite.mem_toFinset, pointIndicators, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_range, Prod.exists, funext_iff, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, fun ⟨a, b, h⟩ => Or.inr ⟨a, b, h⟩⟩
  rintro (h0 | ⟨a, b, h⟩)
  · exact ⟨0, 0, fun x => by simp [h0 x]⟩
  · exact ⟨a, b, h⟩

/-! ### Ordered two-threshold 3-class linear classifiers (`k = 3`, `natarajanDim = 2`) -/

/-- One-dimensional 3-class ordered threshold classifiers on `ℤ`: `x < t₁ ↦ 0`,
`t₁ ≤ x < t₂ ↦ 1`, `t₂ ≤ x ↦ 2`. Equivalently, linear argmax classifiers over ordered slopes. -/
def orderedThresholds3 : ConceptClass ℤ (Fin 3) :=
  Set.range fun p : ℤ × ℤ => fun x => if x < p.1 then 0 else if x < p.2 then 1 else 2

private theorem monotone_of_mem_orderedThresholds3 {c : ℤ → Fin 3} (hc : c ∈ orderedThresholds3) :
    Monotone c := by
  obtain ⟨⟨t₁, t₂⟩, rfl⟩ := hc
  intro x y hxy
  by_cases hx1 : x < t₁ <;> by_cases hx2 : x < t₂ <;>
    by_cases hy1 : y < t₁ <;> by_cases hy2 : y < t₂ <;>
    simp only [hx1, hx2, hy1, hy2, ↓reduceIte] <;> omega

/-- `orderedThresholds3` N-shatters `{0, 1}` using non-constant witnesses `f₀ = (0, 1)` and
`f₁ = (1, 2)` spanning all three labels. -/
theorem natarajanShatters_orderedThresholds3_pair :
    NatarajanShatters orderedThresholds3 ({0, 1} : Set ℤ) := by
  classical
  refine ⟨fun x => if x = 0 then 0 else 1, fun x => if x = 0 then 1 else 2, ?_, fun B hB => ?_⟩
  · intro x hx
    rcases hx with rfl | rfl <;> decide
  · refine ⟨fun x =>
        if x < (if (0 : ℤ) ∈ B then 1 else 0) then 0
        else if x < (if (1 : ℤ) ∈ B then 2 else 1) then 1 else 2,
      ⟨(_, _), rfl⟩, fun x hx => ?_, fun x hx => ?_⟩
    · rcases hB hx with rfl | rfl
      · simp [hx]
      · by_cases h0 : (0 : ℤ) ∈ B <;> simp [h0, hx]
    · rcases hx.1 with rfl | rfl
      · have h0 : (0 : ℤ) ∉ B := hx.2
        by_cases h1 : (1 : ℤ) ∈ B <;> simp [h0, h1]
      · have h1 : (1 : ℤ) ∉ B := hx.2
        by_cases h0 : (0 : ℤ) ∈ B <;> simp [h0, h1]

/-- `orderedThresholds3` N-shatters no 3-element chain `x₀ < x₁ < x₂`, hence no finite set of
size at least `3`. -/
theorem card_le_two_of_natarajanShatters_orderedThresholds3 {W : Finset ℤ}
    (hW : NatarajanShatters orderedThresholds3 ↑W) : W.card ≤ 2 := by
  classical
  by_contra hlt
  have h3 : 3 ≤ W.card := by omega
  set x₀ := W.min' (Finset.card_pos.1 (by omega))
  have hx₀W : x₀ ∈ W := W.min'_mem _
  set W₁ := W.erase x₀
  have hW₁ : 2 ≤ W₁.card := by rw [Finset.card_erase_of_mem hx₀W]; omega
  set x₁ := W₁.min' (Finset.card_pos.1 (by omega))
  have hx₁W₁ : x₁ ∈ W₁ := W₁.min'_mem _
  set W₂ := W₁.erase x₁
  have hW₂ : 1 ≤ W₂.card := by rw [Finset.card_erase_of_mem hx₁W₁]; omega
  set x₂ := W₂.min' (Finset.card_pos.1 hW₂)
  have hx₂W₂ : x₂ ∈ W₂ := W₂.min'_mem _
  have hx₁W : x₁ ∈ W := Finset.mem_of_mem_erase hx₁W₁
  have hx₂W₁ : x₂ ∈ W₁ := Finset.mem_of_mem_erase hx₂W₂
  have hx₂W : x₂ ∈ W := Finset.mem_of_mem_erase hx₂W₁
  have hx01 : x₀ < x₁ :=
    lt_of_le_of_ne (W.min'_le x₁ hx₁W) (Finset.ne_of_mem_erase hx₁W₁).symm
  have hx12 : x₁ < x₂ :=
    lt_of_le_of_ne (W₁.min'_le x₂ hx₂W₁) (Finset.ne_of_mem_erase hx₂W₂).symm
  have hsub : ({x₀, x₁, x₂} : Set ℤ) ⊆ ↑W := by
    intro z hz
    rcases hz with rfl | rfl | rfl <;> simpa using ‹_›
  obtain ⟨f₀, f₁, hne, h⟩ := hW.subset hsub
  set hi : ℤ → Fin 3 := fun z => max (f₀ z) (f₁ z)
  set lo : ℤ → Fin 3 := fun z => min (f₀ z) (f₁ z)
  have hlohi : ∀ z ∈ ({x₀, x₁, x₂} : Set ℤ), lo z < hi z := by
    intro z hz
    rcases lt_or_gt_of_ne (hne z hz) with hlt' | hgt'
    · simpa [lo, hi, min_eq_left hlt'.le, max_eq_right hlt'.le] using hlt'
    · simpa [lo, hi, min_eq_right hgt'.le, max_eq_left hgt'.le] using hgt'
  have hreal (t : ℤ → Fin 3) (ht : ∀ z, t z = f₀ z ∨ t z = f₁ z) :
      ∃ c ∈ orderedThresholds3, ∀ z ∈ ({x₀, x₁, x₂} : Set ℤ), c z = t z := by
    obtain ⟨c, hc, h₀, h₁⟩ :=
      h {z ∈ ({x₀, x₁, x₂} : Set ℤ) | t z = f₀ z} (fun _ hz => hz.1)
    refine ⟨c, hc, fun z hz => ?_⟩
    by_cases htz : t z = f₀ z
    · exact (h₀ z ⟨hz, htz⟩).trans htz.symm
    · exact (h₁ z ⟨hz, fun hB => htz hB.2⟩).trans ((ht z).resolve_left htz).symm
  obtain ⟨c₁, hc₁, hc₁v⟩ := hreal (fun z => if z = x₀ then hi z else lo z) fun z => by
    split_ifs
    · exact max_choice _ _
    · exact min_choice _ _
  obtain ⟨c₂, hc₂, hc₂v⟩ := hreal (fun z => if z = x₁ then hi z else lo z) fun z => by
    split_ifs
    · exact max_choice _ _
    · exact min_choice _ _
  have hle1 : hi x₀ ≤ lo x₁ := by
    have hm := monotone_of_mem_orderedThresholds3 hc₁ hx01.le
    rw [hc₁v x₀ (by simp), hc₁v x₁ (by simp), ite_eq_left rfl, ite_eq_right hx01.ne'] at hm
    exact hm
  have hle2 : hi x₁ ≤ lo x₂ := by
    have hm := monotone_of_mem_orderedThresholds3 hc₂ hx12.le
    rw [hc₂v x₁ (by simp), hc₂v x₂ (by simp), ite_eq_left rfl, ite_eq_right hx12.ne'] at hm
    exact hm
  have hlt0 : lo x₀ < hi x₀ := hlohi x₀ (by simp)
  have hlt1 : lo x₁ < hi x₁ := hlohi x₁ (by simp)
  have hlt2 : lo x₂ < hi x₂ := hlohi x₂ (by simp)
  omega

/-- `orderedThresholds3` has exact Natarajan dimension `2`. -/
theorem natarajanDim_orderedThresholds3 : natarajanDim orderedThresholds3 = 2 := by
  refine le_antisymm (natarajanDim_le_iff.mpr fun W hW => ?_) ?_
  · exact_mod_cast card_le_two_of_natarajanShatters_orderedThresholds3 hW
  · have h : NatarajanShatters orderedThresholds3 ↑({0, 1} : Finset ℤ) := by
      simpa using natarajanShatters_orderedThresholds3_pair
    simpa using h.card_le_natarajanDim

/-! ### Growth counterexamples for `k = 3` -/

/-- Counterexample 1: unlike binary Sauer–Shelah (where `natarajanSum d 2 d = 2 ^ d` is attained by
`Set.univ`), for `k = 3` labels `natarajanSum 1 3 1 = 4` strictly exceeds the total number `3` of
functions `Fin 1 → Fin 3`. -/
example : (Set.univ : ConceptClass (Fin 1) (Fin 3)).ncard <
    natarajanSum 1 (Fintype.card (Fin 3)) 1 := by
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin]
  decide

/-- Counterexample 2: the 6-cycle class `{(a, b) : Fin 3 × Fin 3 | b = a ∨ b = a + 1}` on two
points has `6 > 2 ^ 2` concepts (exceeding both `2 ^ |W|` and the binary `d = 1` Sauer–Shelah bound
`3`), yet N-shatters no two-point set (`natarajanDim = 1`). -/
def cycleSix : ConceptClass (Fin 2) (Fin 3) :=
  {c | c 1 = c 0 ∨ c 1 = c 0 + 1}

theorem ncard_cycleSix : cycleSix.ncard = 6 := by
  classical
  rw [Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
  have hcard : (Finset.univ.filter fun c : Fin 2 → Fin 3 => c 1 = c 0 ∨ c 1 = c 0 + 1).card = 6 :=
    by decide
  convert hcard
  ext c
  simp [cycleSix]

theorem not_natarajanShatters_cycleSix_univ :
    ¬ NatarajanShatters cycleSix (Set.univ : Set (Fin 2)) := by
  rintro ⟨f₀, f₁, hne, h⟩
  obtain ⟨c₀₀, hc₀₀, -, h₀₀⟩ := h ∅ (Set.empty_subset _)
  obtain ⟨c₀₁, hc₀₁, h₀₁a, h₀₁b⟩ := h {1} (Set.subset_univ _)
  obtain ⟨c₁₀, hc₁₀, h₁₀a, h₁₀b⟩ := h {0} (Set.subset_univ _)
  obtain ⟨c₁₁, hc₁₁, h₁₁, -⟩ := h Set.univ subset_rfl
  have hne0 : f₀ 0 ≠ f₁ 0 := hne 0 (Set.mem_univ _)
  have hne1 : f₀ 1 ≠ f₁ 1 := hne 1 (Set.mem_univ _)
  have e00 : f₁ 1 = f₁ 0 ∨ f₁ 1 = f₁ 0 + 1 := by
    have h0 := h₀₀ 0 ⟨Set.mem_univ _, Set.notMem_empty _⟩
    have h1 := h₀₀ 1 ⟨Set.mem_univ _, Set.notMem_empty _⟩
    simpa only [cycleSix, Set.mem_ofPred_eq, h0, h1] using hc₀₀
  have e01 : f₀ 1 = f₁ 0 ∨ f₀ 1 = f₁ 0 + 1 := by
    have h0 := h₀₁b 0 ⟨Set.mem_univ _, by decide⟩
    have h1 := h₀₁a 1 rfl
    simpa only [cycleSix, Set.mem_ofPred_eq, h0, h1] using hc₀₁
  have e10 : f₁ 1 = f₀ 0 ∨ f₁ 1 = f₀ 0 + 1 := by
    have h0 := h₁₀a 0 rfl
    have h1 := h₁₀b 1 ⟨Set.mem_univ _, by decide⟩
    simpa only [cycleSix, Set.mem_ofPred_eq, h0, h1] using hc₁₀
  have e11 : f₀ 1 = f₀ 0 ∨ f₀ 1 = f₀ 0 + 1 := by
    have h0 := h₁₁ 0 (Set.mem_univ _)
    have h1 := h₁₁ 1 (Set.mem_univ _)
    simpa only [cycleSix, Set.mem_ofPred_eq, h0, h1] using hc₁₁
  generalize f₀ 0 = a₀, f₁ 0 = a₁, f₀ 1 = b₀, f₁ 1 = b₁ at hne0 hne1 e00 e01 e10 e11
  revert a₀ a₁ b₀ b₁
  decide

theorem natarajanDim_cycleSix : natarajanDim cycleSix = 1 := by
  refine le_antisymm (natarajanDim_le_iff.mpr fun W hW => ?_) ?_
  · have hle : W.card ≤ 1 := by
      by_contra hgt
      have h2 : W.card = 2 := le_antisymm W.card_le_univ (by omega)
      have hWuniv : W = Finset.univ := Finset.eq_univ_of_card W h2
      rw [hWuniv, Finset.coe_univ] at hW
      exact not_natarajanShatters_cycleSix_univ hW
    exact_mod_cast hle
  · have h0 : NatarajanShatters cycleSix ↑({0} : Finset (Fin 2)) := by
      refine ⟨fun _ => 0, fun _ => 1, fun _ _ => by simp, fun B hB => ?_⟩
      by_cases h0B : (0 : Fin 2) ∈ B
      · refine ⟨fun _ => 0, Or.inl rfl, fun x hx => ?_, fun x hx => ?_⟩
        · have := Finset.mem_singleton.1 (hB hx); simp
        · exact absurd (Finset.mem_singleton.1 (Finset.mem_coe.1 hx.1) ▸ h0B) hx.2
      · refine ⟨fun _ => 1, Or.inl rfl, fun x hx => ?_, fun _ _ => rfl⟩
        exact absurd (Finset.mem_singleton.1 (Finset.mem_coe.1 (hB hx)) ▸ hx) h0B
    simpa using h0.card_le_natarajanDim

end CslibFrontierTests.NatarajanDimension
