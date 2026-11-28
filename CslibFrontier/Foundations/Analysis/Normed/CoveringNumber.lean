/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib)

public import CslibFrontier.Init
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Data.ENat.Lattice
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Metric covering and packing numbers

For a subset `s` of a pseudometric space `X` and a scale `ε : ℝ`, we define three fundamental
`ℕ∞`-valued complexity measures (`⊤` represents an infinite count):

* `Cslib.Metric.coveringNumber s ε`: the minimum cardinality of a finite `ε`-net `T : Finset X`
  (external centers allowed) covering `s` by closed balls of radius `ε`.
* `Cslib.Metric.internalCoveringNumber s ε`: the minimum cardinality of a finite proper
  (internal) `ε`-net `T : Finset X` with `T ⊆ s` covering `s`.
* `Cslib.Metric.packingNumber s ε`: the supremum cardinality of a finite strictly `ε`-separated
  subset `P ⊆ s` (`∀ x ∈ P, ∀ y ∈ P, x ≠ y → ε < dist x y`).

## Main definitions

* `Cslib.Metric.coveringNumber`: external covering number in `ℕ∞`.
* `Cslib.Metric.internalCoveringNumber`: internal (proper) covering number in `ℕ∞`.
* `Cslib.Metric.packingNumber`: packing number in `ℕ∞` (strict `ε`-separation).

## Main results

* `Cslib.Metric.coveringNumber_le_internalCoveringNumber`: external ≤ internal.
* `Cslib.Metric.internalCoveringNumber_le_packingNumber`: internal `ε`-covering number is at most
  the `ε`-packing number for `ε ≥ 0` [Vershynin2018, Lemma 4.2.8].
* `Cslib.Metric.packingNumber_two_mul_le_coveringNumber`: `2ε`-packing number is at most the
  external `ε`-covering number [Vershynin2018, Lemma 4.2.8].
* `Cslib.Metric.internalCoveringNumber_le_coveringNumber_half`: `N_int(s, ε) ≤ N_ext(s, ε / 2)`.
* `Cslib.Metric.internalCoveringNumber_lt_top_of_totallyBounded`: total boundedness implies
  finiteness of `internalCoveringNumber s ε` and `coveringNumber s ε` for every `ε > 0`.
* `Cslib.Metric.internalCoveringNumber_image_le_of_lipschitz`: Lipschitz contraction preserves
  internal covering numbers (scaling `ε` by the Lipschitz constant `L`).
* `Cslib.Metric.packingNumber_closedBall_toNat_le`,
  `Cslib.Metric.internalCoveringNumber_closedBall_toNat_le`,
  `Cslib.Metric.coveringNumber_closedBall_toNat_le_three_pow`: volumetric bounds `(1 + 2 R / ε) ^ d`
  and `(3 R / ε) ^ d` for closed balls in any finite-dimensional real normed space
  [Vershynin2018, Corollary 4.2.13].

## References

* [R. Vershynin, *High-Dimensional Probability*][Vershynin2018], Section 4.2 (Lemma 4.2.8 and
  Corollary 4.2.13; locators unverified)
-/

public section

open scoped ENNReal

namespace Cslib.Metric

section PseudoMetric

variable {X : Type*} [PseudoMetricSpace X]

/-- **External covering number** `N(s, ε) : ℕ∞`: the minimum cardinality of a finite subset
`T : Finset X` whose closed `ε`-balls cover `s` (`⊤` if no finite cover exists). -/
noncomputable def coveringNumber (s : Set X) (ε : ℝ) : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ T : Finset X, (T.card : ℕ∞) = n ∧ ∀ x ∈ s, ∃ y ∈ T, dist x y ≤ ε}

/-- **Internal (proper) covering number** `N_int(s, ε) : ℕ∞`: the minimum cardinality of a finite
subset `T ⊆ s` whose closed `ε`-balls cover `s` (`⊤` if no finite internal cover exists). -/
noncomputable def internalCoveringNumber (s : Set X) (ε : ℝ) : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ T : Finset X,
    (T.card : ℕ∞) = n ∧ (∀ y ∈ T, y ∈ s) ∧ ∀ x ∈ s, ∃ y ∈ T, dist x y ≤ ε}

/-- **Packing number** `M(s, ε) : ℕ∞`: the supremum cardinality of a finite subset `P ⊆ s` whose
distinct points are strictly `ε`-separated (`ε < dist x y`). -/
noncomputable def packingNumber (s : Set X) (ε : ℝ) : ℕ∞ :=
  sSup {n : ℕ∞ | ∃ P : Finset X,
    (P.card : ℕ∞) = n ∧ (∀ x ∈ P, x ∈ s) ∧ ∀ x ∈ P, ∀ y ∈ P, x ≠ y → ε < dist x y}

private theorem enat_sInf_mem_of_lt_top {S : Set ℕ∞} (h : sInf S < ⊤) : sInf S ∈ S :=
  let ⟨x, hx, _⟩ := sInf_lt_iff.1 h
  csInf_mem ⟨x, hx⟩

/-! ### Basic order and membership lemmas -/

theorem coveringNumber_le_card {s : Set X} {ε : ℝ} {T : Finset X}
    (hT : ∀ x ∈ s, ∃ y ∈ T, dist x y ≤ ε) : coveringNumber s ε ≤ T.card :=
  sInf_le ⟨T, rfl, hT⟩

theorem internalCoveringNumber_le_card {s : Set X} {ε : ℝ} {T : Finset X}
    (hTs : ∀ y ∈ T, y ∈ s) (hT : ∀ x ∈ s, ∃ y ∈ T, dist x y ≤ ε) :
    internalCoveringNumber s ε ≤ T.card :=
  sInf_le ⟨T, rfl, hTs, hT⟩

theorem le_internalCoveringNumber {s : Set X} {ε : ℝ} {n : ℕ∞}
    (h : ∀ T : Finset X, (∀ y ∈ T, y ∈ s) →
      (∀ x ∈ s, ∃ y ∈ T, dist x y ≤ ε) → n ≤ T.card) :
    n ≤ internalCoveringNumber s ε :=
  le_sInf fun _ ⟨T, hcard, hTs, hT⟩ => hcard ▸ h T hTs hT

theorem card_le_packingNumber {s : Set X} {ε : ℝ} {P : Finset X}
    (hPs : ∀ x ∈ P, x ∈ s) (hsep : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → ε < dist x y) :
    (P.card : ℕ∞) ≤ packingNumber s ε :=
  le_sSup ⟨P, rfl, hPs, hsep⟩

/-- Any finite external covering number is attained by a `Finset X` of that exact cardinality. -/
theorem exists_cover_of_coveringNumber_lt_top {s : Set X} {ε : ℝ}
    (h : coveringNumber s ε < ⊤) :
    ∃ T : Finset X, (T.card : ℕ∞) = coveringNumber s ε ∧ ∀ x ∈ s, ∃ y ∈ T, dist x y ≤ ε :=
  enat_sInf_mem_of_lt_top h

/-- Any finite internal covering number is attained by a `Finset X` contained in `s`. -/
theorem exists_internalCover_of_lt_top {s : Set X} {ε : ℝ}
    (h : internalCoveringNumber s ε < ⊤) :
    ∃ T : Finset X, (T.card : ℕ∞) = internalCoveringNumber s ε ∧
      (∀ y ∈ T, y ∈ s) ∧ ∀ x ∈ s, ∃ y ∈ T, dist x y ≤ ε :=
  enat_sInf_mem_of_lt_top h

@[simp]
theorem coveringNumber_empty (ε : ℝ) : coveringNumber (∅ : Set X) ε = 0 :=
  le_antisymm (coveringNumber_le_card (T := ∅) fun _ hx => hx.elim) bot_le

@[simp]
theorem internalCoveringNumber_empty (ε : ℝ) : internalCoveringNumber (∅ : Set X) ε = 0 :=
  le_antisymm (internalCoveringNumber_le_card (T := ∅) (fun _ hx => (Finset.notMem_empty _ hx).elim)
    fun _ hx => hx.elim) bot_le

@[simp]
theorem packingNumber_empty (ε : ℝ) : packingNumber (∅ : Set X) ε = 0 := by
  refine le_antisymm (sSup_le fun _ ⟨P, hcard, hPs, _⟩ => ?_) bot_le
  simp [← hcard, Finset.eq_empty_of_forall_notMem hPs]

theorem one_le_coveringNumber {s : Set X} (hs : s.Nonempty) (ε : ℝ) :
    1 ≤ coveringNumber s ε := by
  obtain ⟨x, hx⟩ := hs
  exact le_sInf fun _ ⟨T, hcard, hT⟩ =>
    let ⟨y, hy, _⟩ := hT x hx
    hcard ▸ mod_cast Finset.card_pos.2 ⟨y, hy⟩

theorem coveringNumber_le_one_of_subset_closedBall {s : Set X} {x₀ : X} {ε : ℝ}
    (hs : ∀ x ∈ s, dist x x₀ ≤ ε) : coveringNumber s ε ≤ 1 := by
  simpa using coveringNumber_le_card (T := {x₀}) fun x hx =>
    ⟨x₀, Finset.mem_singleton_self _, hs x hx⟩

theorem coveringNumber_le_internalCoveringNumber (s : Set X) (ε : ℝ) :
    coveringNumber s ε ≤ internalCoveringNumber s ε :=
  le_sInf fun _ ⟨_, hcard, _, hT⟩ => hcard ▸ coveringNumber_le_card hT

theorem coveringNumber_anti (s : Set X) {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    coveringNumber s ε₂ ≤ coveringNumber s ε₁ :=
  le_sInf fun _ ⟨_, hcard, hT⟩ => hcard ▸ coveringNumber_le_card fun x hx =>
    let ⟨y, hy, hxy⟩ := hT x hx
    ⟨y, hy, hxy.trans hε⟩

theorem internalCoveringNumber_anti (s : Set X) {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    internalCoveringNumber s ε₂ ≤ internalCoveringNumber s ε₁ :=
  le_sInf fun _ ⟨_, hcard, hTs, hT⟩ => hcard ▸ internalCoveringNumber_le_card hTs fun x hx =>
    let ⟨y, hy, hxy⟩ := hT x hx
    ⟨y, hy, hxy.trans hε⟩

theorem packingNumber_anti (s : Set X) {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    packingNumber s ε₂ ≤ packingNumber s ε₁ :=
  sSup_le fun _ ⟨_, hcard, hPs, hsep⟩ => hcard ▸ card_le_packingNumber hPs fun x hx y hy hxy =>
    lt_of_le_of_lt hε (hsep x hx y hy hxy)

theorem coveringNumber_mono {s t : Set X} (hst : s ⊆ t) (ε : ℝ) :
    coveringNumber s ε ≤ coveringNumber t ε :=
  le_sInf fun _ ⟨_, hcard, hT⟩ => hcard ▸ coveringNumber_le_card fun x hx => hT x (hst hx)

theorem packingNumber_mono {s t : Set X} (hst : s ⊆ t) (ε : ℝ) :
    packingNumber s ε ≤ packingNumber t ε :=
  sSup_le fun _ ⟨_, hcard, hPs, hsep⟩ =>
    hcard ▸ card_le_packingNumber (fun x hx => hst (hPs x hx)) hsep

theorem packingNumber_le_of_forall_card_le {s : Set X} {ε : ℝ} {M : ℕ∞}
    (hM : ∀ P : Finset X, (∀ x ∈ P, x ∈ s) →
      (∀ x ∈ P, ∀ y ∈ P, x ≠ y → ε < dist x y) → (P.card : ℕ∞) ≤ M) :
    packingNumber s ε ≤ M :=
  sSup_le fun _ ⟨P, hcard, hPs, hsep⟩ => hcard ▸ hM P hPs hsep

/-! ### Packing–covering duality -/

/-- **Internal covering is bounded by packing** [Vershynin2018, Lemma 4.2.8] (locator unverified):
for every `ε ≥ 0`, a maximal strictly `ε`-separated subset of `s` is an internal `ε`-net, so
`internalCoveringNumber s ε ≤ packingNumber s ε`. -/
theorem internalCoveringNumber_le_packingNumber (s : Set X) {ε : ℝ} (hε : 0 ≤ ε) :
    internalCoveringNumber s ε ≤ packingNumber s ε := by
  classical
  rcases eq_top_or_lt_top (packingNumber s ε) with htop | hlt
  · exact htop ▸ le_top
  have _ : Nonempty {n : ℕ∞ | ∃ P : Finset X, (P.card : ℕ∞) = n ∧ (∀ x ∈ P, x ∈ s) ∧
      ∀ x ∈ P, ∀ y ∈ P, x ≠ y → ε < dist x y} := ⟨⟨0, ∅, rfl, by simp, by simp⟩⟩
  obtain ⟨P, hPcard : (P.card : ℕ∞) = packingNumber s ε, hPs, hsep⟩ :=
    ENat.sSup_mem_of_nonempty_of_lt_top hlt
  rw [← hPcard]
  refine internalCoveringNumber_le_card hPs fun x hx => ?_
  by_contra! hfar
  have hxP : x ∉ P := fun hmem => (hfar x hmem).not_ge ((dist_self x).trans_le hε)
  have hle : ((insert x P).card : ℕ∞) ≤ packingNumber s ε := by
    refine card_le_packingNumber (fun y hy => (Finset.mem_insert.1 hy).elim (· ▸ hx) (hPs y))
      fun y hy z hz hyz => ?_
    rcases Finset.mem_insert.1 hy with rfl | hy' <;> rcases Finset.mem_insert.1 hz with rfl | hz'
    exacts [(hyz rfl).elim, hfar z hz', (hfar y hy').trans_eq (dist_comm _ _),
      hsep y hy' z hz' hyz]
  rw [Finset.card_insert_of_notMem hxP, ← hPcard] at hle
  exact ((Nat.lt_succ_self P.card).not_ge (by exact_mod_cast hle)).elim

/-- **Packing is bounded by external covering at half scale** [Vershynin2018, Lemma 4.2.8]
(locator unverified): no closed `ε`-ball can contain two points that are more than `2 ε` apart, so
`packingNumber s (2 * ε) ≤ coveringNumber s ε`. -/
theorem packingNumber_two_mul_le_coveringNumber (s : Set X) (ε : ℝ) :
    packingNumber s (2 * ε) ≤ coveringNumber s ε := by
  refine packingNumber_le_of_forall_card_le fun P hPs hsep => le_sInf ?_
  rintro _ ⟨T, rfl, hT⟩
  choose! φ hφT hφd using fun x (hx : x ∈ P) => hT x (hPs x hx)
  exact Nat.cast_le.2 <| Finset.card_le_card_of_injOn φ hφT fun x hx y hy hxy => by
    by_contra hne
    linarith [hsep x hx y hy hne, hxy ▸ hφd x hx, hφd y hy, dist_triangle_right x y (φ y)]

/-- Comparison between internal and external covering numbers at half scale. -/
theorem internalCoveringNumber_le_coveringNumber_half (s : Set X) {ε : ℝ} (hε : 0 ≤ ε) :
    internalCoveringNumber s ε ≤ coveringNumber s (ε / 2) := by
  calc internalCoveringNumber s ε
      ≤ packingNumber s ε := internalCoveringNumber_le_packingNumber s hε
    _ = packingNumber s (2 * (ε / 2)) := by ring_nf
    _ ≤ coveringNumber s (ε / 2) := packingNumber_two_mul_le_coveringNumber s (ε / 2)

/-- Every totally bounded set has finite external covering number at every positive scale `ε`. -/
theorem coveringNumber_lt_top_of_totallyBounded {s : Set X} (hs : TotallyBounded s)
    {ε : ℝ} (hε : 0 < ε) : coveringNumber s ε < ⊤ := by
  classical
  obtain ⟨t, hfin, hcov⟩ := Metric.totallyBounded_iff.1 hs ε hε
  exact lt_of_le_of_lt (coveringNumber_le_card (T := hfin.toFinset) fun x hx =>
    let ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcov hx)
    ⟨y, hfin.mem_toFinset.2 hy, (Metric.mem_ball.1 hxy).le⟩) (ENat.natCast_lt_top _)

/-- Every totally bounded set has finite internal covering number at every positive scale `ε`. -/
theorem internalCoveringNumber_lt_top_of_totallyBounded {s : Set X} (hs : TotallyBounded s)
    {ε : ℝ} (hε : 0 < ε) : internalCoveringNumber s ε < ⊤ :=
  lt_of_le_of_lt (internalCoveringNumber_le_coveringNumber_half s hε.le)
    (coveringNumber_lt_top_of_totallyBounded hs (half_pos hε))

/-- **Lipschitz invariance of internal covering numbers**: if `f` is `L`-Lipschitz on `s`
(`0 ≤ L`), then `N_int(f '' s, L * ε) ≤ N_int(s, ε)`. -/
theorem internalCoveringNumber_image_le_of_lipschitz {Y : Type*} [PseudoMetricSpace Y]
    {s : Set X} {f : X → Y} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ L * dist x y) (ε : ℝ) :
    internalCoveringNumber (f '' s) (L * ε) ≤ internalCoveringNumber s ε := by
  classical
  refine le_sInf fun _ ⟨T, hcard, hTs, hT⟩ => hcard ▸
    (internalCoveringNumber_le_card (s := f '' s) (T := T.image f)
      (Finset.forall_mem_image.2 fun y hy => ⟨y, hTs y hy, rfl⟩) ?_).trans
      (Nat.cast_le.2 Finset.card_image_le)
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hT x hx
  exact ⟨f y, Finset.mem_image_of_mem f hy,
    (hf x hx y (hTs y hy)).trans (mul_le_mul_of_nonneg_left hxy hL)⟩

end PseudoMetric

section NormedGroup

variable {E : Type*} [NormedAddCommGroup E]

/-- Translating a set preserves its external covering number. -/
theorem coveringNumber_vadd (c : E) (s : Set E) (ε : ℝ) :
    coveringNumber ((fun x => x + c) '' s) ε = coveringNumber s ε := by
  classical
  have hle (d : E) (t : Set E) : coveringNumber ((fun x => x + d) '' t) ε ≤ coveringNumber t ε := by
    refine le_sInf fun _ ⟨T, hcard, hT⟩ => hcard ▸
      (coveringNumber_le_card (T := T.image fun y => y + d) ?_).trans
        (Nat.cast_le.2 Finset.card_image_le)
    rintro _ ⟨x, hx, rfl⟩
    let ⟨y, hy, hxy⟩ := hT x hx
    exact ⟨y + d, Finset.mem_image_of_mem _ hy, by simpa only [dist_add_right] using hxy⟩
  exact le_antisymm (hle c s) (by
    simpa only [Set.image_image, add_neg_cancel_right, Set.image_id'] using
      hle (-c) ((fun x => x + c) '' s))

end NormedGroup

section Volumetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open MeasureTheory

/-- **Volumetric packing bound for a finite-dimensional ball** [Vershynin2018, Corollary 4.2.13]
(locator unverified): in any finite-dimensional real normed space `E` of dimension `d`, every
strictly `ε`-separated finite subset `P ⊆ Metric.closedBall x₀ R` (`0 ≤ R`, `0 < ε`) satisfies
`P.card ≤ (1 + 2 * R / ε) ^ d`. -/
theorem card_le_of_separated_closedBall {x₀ : E} {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    {P : Finset E} (hP : ∀ x ∈ P, x ∈ Metric.closedBall x₀ R)
    (hsep : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → ε < dist x y) :
    (P.card : ℝ) ≤ (1 + 2 * R / ε) ^ Module.finrank ℝ E := by
  classical
  rcases subsingleton_or_nontrivial E with hsub | hnt
  · exact (((Nat.cast_le (α := ℝ)).2
      (Finset.card_le_one.2 fun a _ b _ => Subsingleton.elim a b)).trans_eq Nat.cast_one).trans
      (one_le_pow₀ (le_add_of_nonneg_right (div_nonneg (mul_nonneg zero_le_two hR) hε.le)))
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  let μ : Measure E := Measure.addHaar
  have hdisj : Set.PairwiseDisjoint (P : Set E) fun y => Metric.ball y (ε / 2) :=
    fun y₁ hy₁ y₂ hy₂ hne => Set.disjoint_left.2 fun z hz₁ hz₂ => by
      linarith [hsep y₁ hy₁ y₂ hy₂ hne, dist_triangle y₁ z y₂, dist_comm y₁ z,
        Metric.mem_ball.1 hz₁, Metric.mem_ball.1 hz₂]
  have hsub : (⋃ y ∈ P, Metric.ball y (ε / 2)) ⊆ Metric.ball x₀ (R + ε / 2) :=
    Set.iUnion₂_subset fun y hy z hzy => Metric.mem_ball.2 (by
      linarith [dist_triangle z y x₀, Metric.mem_ball.1 hzy, Metric.mem_closedBall.1 (hP y hy)])
  have hball_eq (y : E) {r : ℝ} (hr : 0 ≤ r) :
      μ (Metric.ball y r) = ENNReal.ofReal r ^ Module.finrank ℝ E * μ (Metric.ball 0 1) := by
    rw [μ.addHaar_ball y hr, ENNReal.ofReal_pow hr]
  have hpos1 : 0 < μ (Metric.ball (0 : E) 1) :=
    IsOpen.measure_pos μ Metric.isOpen_ball ⟨0, Metric.mem_ball_self zero_lt_one⟩
  have hlt1 : μ (Metric.ball (0 : E) 1) < ⊤ :=
    ProperSpace.isCompact_closedBall (0 : E) 1 |>.measure_lt_top.trans_le'
      (measure_mono Metric.ball_subset_closedBall)
  have hhalf_pos : 0 < ε / 2 := by positivity
  have hbig_pos : 0 < R + ε / 2 := by linarith
  have hineq :
      ((P.card : ℝ≥0∞) * ENNReal.ofReal (ε / 2) ^ Module.finrank ℝ E) * μ (Metric.ball 0 1) ≤
        ENNReal.ofReal (R + ε / 2) ^ Module.finrank ℝ E * μ (Metric.ball 0 1) := by
    calc _ = ∑ _y ∈ P, ENNReal.ofReal (ε / 2) ^ Module.finrank ℝ E * μ (Metric.ball 0 1) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ = ∑ y ∈ P, μ (Metric.ball y (ε / 2)) :=
          Finset.sum_congr rfl fun y _ => (hball_eq y hhalf_pos.le).symm
      _ ≤ μ (Metric.ball x₀ (R + ε / 2)) :=
          (measure_biUnion_finset hdisj fun _ _ => measurableSet_ball).symm.trans_le
            (measure_mono hsub)
      _ = ENNReal.ofReal (R + ε / 2) ^ Module.finrank ℝ E * μ (Metric.ball 0 1) :=
          hball_eq x₀ hbig_pos.le
  have hreal := (ENNReal.mul_le_mul_iff_left hpos1.ne' hlt1.ne).1 hineq
  rw [← ENNReal.ofReal_pow hhalf_pos.le, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_pow hbig_pos.le,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hreal
  exact ((le_div_iff₀ (pow_pos hhalf_pos _)).2 hreal).trans_eq
    ((div_pow _ _ _).symm.trans (congrArg (· ^ _) (by field_simp; ring)))

/-- Finite real bound on `packingNumber (Metric.closedBall x₀ R) ε` for `R ≥ 0, ε > 0`. -/
theorem packingNumber_closedBall_lt_top (x₀ : E) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    packingNumber (Metric.closedBall x₀ R) ε < ⊤ := by
  refine lt_of_le_of_lt
    (packingNumber_le_of_forall_card_le (M := ⌊(1 + 2 * R / ε) ^ Module.finrank ℝ E⌋₊)
      fun P hP hsep => ?_) (ENat.natCast_lt_top _)
  exact_mod_cast Nat.le_floor (card_le_of_separated_closedBall hR hε hP hsep)

/-- **Volumetric packing bound** [Vershynin2018, Corollary 4.2.13] (locator unverified):
`(packingNumber (closedBall x₀ R) ε).toNat ≤ (1 + 2 * R / ε) ^ dim E`. -/
theorem packingNumber_closedBall_toNat_le (x₀ : E) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    ((packingNumber (Metric.closedBall x₀ R) ε).toNat : ℝ) ≤
      (1 + 2 * R / ε) ^ Module.finrank ℝ E := by
  exact (Nat.cast_le.2 (ENat.toNat_le_of_le_natCast (packingNumber_le_of_forall_card_le
    fun P hP hsep => Nat.cast_le.2
      (Nat.le_floor (card_le_of_separated_closedBall hR hε hP hsep))))).trans
    (Nat.floor_le (by positivity))

/-- **Volumetric internal covering bound** [Vershynin2018, Corollary 4.2.13] (locator unverified):
`internalCoveringNumber (closedBall x₀ R) ε ≤ (1 + 2 * R / ε) ^ dim E` for `R ≥ 0, ε > 0`. -/
theorem internalCoveringNumber_closedBall_toNat_le (x₀ : E) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    ((internalCoveringNumber (Metric.closedBall x₀ R) ε).toNat : ℝ) ≤
      (1 + 2 * R / ε) ^ Module.finrank ℝ E :=
  (Nat.cast_le.2 (ENat.toNat_le_toNat
    (internalCoveringNumber_le_packingNumber _ hε.le)
    (packingNumber_closedBall_lt_top x₀ hR hε).ne)).trans
    (packingNumber_closedBall_toNat_le x₀ hR hε)

/-- **Volumetric external covering bound**: for `0 < ε ≤ R`,
`coveringNumber (closedBall x₀ R) ε ≤ (3 * R / ε) ^ dim E`. -/
theorem coveringNumber_closedBall_toNat_le_three_pow (x₀ : E) {R ε : ℝ} (hε : 0 < ε)
    (hεR : ε ≤ R) :
    ((coveringNumber (Metric.closedBall x₀ R) ε).toNat : ℝ) ≤
      (3 * R / ε) ^ Module.finrank ℝ E := by
  have hR : 0 ≤ R := hε.le.trans hεR
  have hlt := (internalCoveringNumber_le_packingNumber _ hε.le).trans_lt
    (packingNumber_closedBall_lt_top x₀ hR hε)
  refine (Nat.cast_le.2 (ENat.toNat_le_toNat (coveringNumber_le_internalCoveringNumber _ _)
    hlt.ne)).trans ((internalCoveringNumber_closedBall_toNat_le x₀ hR hε).trans
    (pow_le_pow_left₀ (by positivity) ?_ _))
  rw [one_add_div hε.ne', div_le_div_iff_of_pos_right hε]; linarith

end Volumetric

end Cslib.Metric
