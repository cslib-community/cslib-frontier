/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Successive minima and Minkowski's bound

For a `ℤ`-submodule `L` of a real normed space `E`, the *first minimum* `λ₁(L)`
(`ZLattice.minimum`) is the infimum of the norms of the nonzero vectors of `L`, and the
`k`-th *successive minimum* `λ_k(L)` (`ZLattice.successiveMinimum`) is the infimum of the radii
`r ≥ 0` for which the vectors of `L` of norm at most `r` span a real subspace of dimension at
least `k` ([MicciancioGoldwasser2002], Chapter 1).

When `E` is proper and `L` is discrete, the first minimum is attained by a nonzero lattice vector
(`ZLattice.exists_norm_eq_minimum`), so it is positive for nonzero `L`, and it agrees with
`λ₁` from the second definition (`ZLattice.successiveMinimum_one`). Successive minima are monotone
in `k` up to the rank of a full-rank lattice (`ZLattice.successiveMinimum_mono`), and `k`
linearly independent lattice vectors of norm at most `r` bound `λ_k(L)` by `r`
(`ZLattice.successiveMinimum_le_of_linearIndependent`).

Minkowski's first theorem bounds `λ₁` by the covolume. In any finite-dimensional normed space,
if the closed ball of radius `r` has measure at least `2ⁿ` times the covolume, then `L` has a
nonzero vector of norm at most `r` (`ZLattice.exists_ne_zero_mem_norm_le`); this specializes
Mathlib's `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure`. For a
full-rank lattice in `ℝⁿ` with the supremum norm this gives `λ₁(L) ≤ det(L)^{1/n}`
(`ZLattice.minimum_le_covolume_rpow`), and in `EuclideanSpace ℝ (Fin n)` it gives the bound
`λ₁(L) ≤ √n · det(L)^{1/n}` ([MicciancioGoldwasser2002], Chapter 1)
(`ZLattice.minimum_le_sqrt_mul_covolume_rpow`).

## Main definitions

* `ZLattice.minimum`: the first minimum `λ₁(L)`.
* `ZLattice.successiveMinimum`: the successive minima `λ_k(L)`.

## Main results

* `ZLattice.exists_norm_eq_minimum`: a discrete nonzero lattice has a shortest nonzero vector.
* `ZLattice.successiveMinimum_one`: `λ₁` agrees with the first minimum.
* `ZLattice.successiveMinimum_mono`: `λ_j(L) ≤ λ_k(L)` for `j ≤ k ≤ n`.
* `ZLattice.exists_linearIndependent_norm_le_successiveMinimum`: a full-rank discrete lattice has
  `k` linearly independent vectors of norm at most `λ_k(L)`.
* `ZLattice.exists_ne_zero_mem_norm_le`: Minkowski's first theorem for closed balls.
* `ZLattice.minimum_le_sqrt_mul_covolume_rpow`: `λ₁(L) ≤ √n · det(L)^{1/n}` in the Euclidean
  norm.

## References

* [D. Micciancio and S. Goldwasser, *Complexity of Lattice Problems: A Cryptographic
  Perspective*][MicciancioGoldwasser2002]
-/

public section

open Module Metric MeasureTheory

namespace ZLattice

section Minimum

variable {E : Type*} [NormedAddCommGroup E]

/-- The first minimum `λ₁(L)`: the infimum of the norms of the nonzero vectors of `L`. It is `0`
for the zero submodule. -/
noncomputable def minimum (L : Submodule ℤ E) : ℝ :=
  sInf (norm '' {v : E | v ∈ L ∧ v ≠ 0})

private theorem bddBelow_norm_image (L : Submodule ℤ E) :
    BddBelow (norm '' {v : E | v ∈ L ∧ v ≠ 0}) :=
  ⟨0, by rintro _ ⟨v, -, rfl⟩; exact norm_nonneg v⟩

theorem minimum_nonneg (L : Submodule ℤ E) : 0 ≤ minimum L :=
  Real.sInf_nonneg (by rintro _ ⟨v, -, rfl⟩; exact norm_nonneg v)

/-- Every nonzero lattice vector is at least as long as the first minimum. -/
theorem minimum_le_norm {L : Submodule ℤ E} {v : E} (hv : v ∈ L) (h0 : v ≠ 0) :
    minimum L ≤ ‖v‖ :=
  csInf_le (bddBelow_norm_image L) ⟨v, ⟨hv, h0⟩, rfl⟩

/-- Distinct lattice vectors are at distance at least the first minimum. -/
theorem minimum_le_norm_sub {L : Submodule ℤ E} {u v : E} (hu : u ∈ L) (hv : v ∈ L)
    (huv : u ≠ v) : minimum L ≤ ‖u - v‖ :=
  minimum_le_norm (L.sub_mem hu hv) (sub_ne_zero.2 huv)

@[simp]
theorem minimum_bot : minimum (⊥ : Submodule ℤ E) = 0 := by
  simp [minimum]

/-- A lower bound for every nonzero lattice vector bounds the first minimum. -/
theorem le_minimum_iff {L : Submodule ℤ E} (hL : L ≠ ⊥) {r : ℝ} :
    r ≤ minimum L ↔ ∀ v ∈ L, v ≠ 0 → r ≤ ‖v‖ := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL
  rw [minimum, le_csInf_iff (bddBelow_norm_image L) ⟨_, w, ⟨hw, hw0⟩, rfl⟩]
  exact ⟨fun h v hv hv0 => h _ ⟨v, ⟨hv, hv0⟩, rfl⟩,
    by rintro h _ ⟨v, ⟨hv, hv0⟩, rfl⟩; exact h v hv hv0⟩

variable [ProperSpace E]

private theorem finite_mem_and_norm_le (L : Submodule ℤ E) [DiscreteTopology L] (r : ℝ) :
    {v : E | v ∈ L ∧ ‖v‖ ≤ r}.Finite :=
  (finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
    (isBounded_closedBall (x := (0 : E)) (r := r))
    L.toAddSubgroup.isClosed_of_discreteTopology).subset fun _ hv =>
    ⟨by simpa only [mem_closedBall, dist_zero_right] using hv.2, hv.1⟩

/-- A discrete nonzero lattice in a proper space has a shortest nonzero vector. -/
theorem exists_norm_eq_minimum {L : Submodule ℤ E} [DiscreteTopology L] (hL : L ≠ ⊥) :
    ∃ v ∈ L, v ≠ 0 ∧ ‖v‖ = minimum L := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL
  obtain ⟨v, ⟨hvL, hv0, hvw⟩, hmin⟩ := Set.exists_min_image
    {v | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ ‖w‖} norm
    ((finite_mem_and_norm_le L ‖w‖).subset fun _ h => ⟨h.1, h.2.2⟩) ⟨w, hw, hw0, le_rfl⟩
  refine ⟨v, hvL, hv0, le_antisymm ((le_minimum_iff hL).2 fun u hu hu0 => ?_)
    (minimum_le_norm hvL hv0)⟩
  exact if huw : ‖u‖ ≤ ‖w‖ then hmin u ⟨hu, hu0, huw⟩ else hvw.trans (le_of_not_ge huw)

/-- The first minimum of a discrete nonzero lattice is positive. -/
theorem minimum_pos {L : Submodule ℤ E} [DiscreteTopology L] (hL : L ≠ ⊥) : 0 < minimum L := by
  obtain ⟨v, -, hv0, hv⟩ := exists_norm_eq_minimum hL
  exact hv ▸ norm_pos_iff.2 hv0

/-- The first minimum is at most `r` exactly when some nonzero lattice vector has norm at
most `r`. -/
theorem minimum_le_iff {L : Submodule ℤ E} [DiscreteTopology L] (hL : L ≠ ⊥) {r : ℝ} :
    minimum L ≤ r ↔ ∃ v ∈ L, v ≠ 0 ∧ ‖v‖ ≤ r := by
  refine ⟨fun h => ?_, fun ⟨v, hv, hv0, hvr⟩ => (minimum_le_norm hv hv0).trans hvr⟩
  obtain ⟨v, hv, hv0, hvm⟩ := exists_norm_eq_minimum hL
  exact ⟨v, hv, hv0, hvm ▸ h⟩

end Minimum

section SuccessiveMinimum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `k`-th successive minimum `λ_k(L)`: the infimum of the radii `r ≥ 0` such that the
vectors of `L` of norm at most `r` span a real subspace of dimension at least `k`. When `k` exceeds
the dimension of the real span of `L`, the set is empty and `successiveMinimum L k = 0`; this is why
`successiveMinimum_mono` assumes `k ≤ finrank ℝ E` and a full-rank lattice. -/
noncomputable def successiveMinimum (L : Submodule ℤ E) (k : ℕ) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ k ≤ finrank ℝ (Submodule.span ℝ {v : E | v ∈ L ∧ ‖v‖ ≤ r})}

theorem successiveMinimum_nonneg (L : Submodule ℤ E) (k : ℕ) : 0 ≤ successiveMinimum L k :=
  Real.sInf_nonneg fun _ hr => hr.1

@[simp]
theorem successiveMinimum_zero (L : Submodule ℤ E) : successiveMinimum L 0 = 0 := by
  have h : {r : ℝ | 0 ≤ r ∧ 0 ≤ finrank ℝ (Submodule.span ℝ {v : E | v ∈ L ∧ ‖v‖ ≤ r})} =
      Set.Ici 0 := by
    ext r; simp
  rw [successiveMinimum, h, csInf_Ici]

variable [FiniteDimensional ℝ E]

/-- `k` linearly independent lattice vectors of norm at most `r ≥ 0` give `λ_k(L) ≤ r`. -/
theorem successiveMinimum_le_of_linearIndependent {L : Submodule ℤ E} {k : ℕ} {v : Fin k → E}
    (hli : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ L) {r : ℝ} (hr : 0 ≤ r)
    (hvr : ∀ i, ‖v i‖ ≤ r) : successiveMinimum L k ≤ r := by
  refine csInf_le ⟨0, fun _ hs => hs.1⟩ ⟨hr, ?_⟩
  rw [← Fintype.card_fin k, ← finrank_span_eq_card hli]
  exact Submodule.finrank_mono
    (Submodule.span_mono (Set.range_subset_iff.2 fun i => ⟨hvL i, hvr i⟩))

/-- For a full-rank lattice, some radius makes the short lattice vectors span the whole space. -/
private theorem exists_radius_finrank (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (k : ℕ) (hk : k ≤ finrank ℝ E) :
    ∃ r, 0 ≤ r ∧ k ≤ finrank ℝ (Submodule.span ℝ {v : E | v ∈ L ∧ ‖v‖ ≤ r}) := by
  let b := (Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  refine ⟨∑ i, ‖b i‖, Finset.sum_nonneg fun i _ => norm_nonneg _, ?_⟩
  have htop : Submodule.span ℝ {v : E | v ∈ L ∧ ‖v‖ ≤ ∑ i, ‖b i‖} = ⊤ :=
    eq_top_iff.2 (b.span_eq.symm.le.trans (Submodule.span_mono <| by
      rintro _ ⟨i, rfl⟩
      exact ⟨by simp [b], Finset.single_le_sum (fun j _ => norm_nonneg (b j)) (Finset.mem_univ i)⟩))
  rwa [htop, finrank_top]

/-- Successive minima are monotone up to the rank of a full-rank lattice. -/
theorem successiveMinimum_mono (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ finrank ℝ E) :
    successiveMinimum L j ≤ successiveMinimum L k := by
  obtain ⟨r, hr⟩ := exists_radius_finrank L k hk
  exact csInf_le_csInf ⟨0, fun _ hs => hs.1⟩ ⟨r, hr⟩ fun s hs => ⟨hs.1, hjk.trans hs.2⟩

/-- A full-rank discrete lattice has `k` linearly independent vectors of norm at most `λ_k(L)`
for every `k ≤ finrank ℝ E`. -/
theorem exists_linearIndependent_norm_le_successiveMinimum
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {k : ℕ} (hk : k ≤ finrank ℝ E) :
    ∃ v : Fin k → E, LinearIndependent ℝ v ∧ (∀ i, v i ∈ L) ∧
      ∀ i, ‖v i‖ ≤ successiveMinimum L k := by
  classical
  have : ProperSpace E := FiniteDimensional.proper ℝ E
  let A : Set E := {v : E | v ∈ L ∧ ‖v‖ ≤ successiveMinimum L k}
  have hspan : k ≤ finrank ℝ (Submodule.span ℝ A) := by
    obtain ⟨R, hR0, hRk⟩ := exists_radius_finrank L k hk
    let T : Set E := {v : E | (v ∈ L ∧ ‖v‖ ≤ R) ∧ successiveMinimum L k < ‖v‖}
    by_cases hTe : T.Nonempty
    · obtain ⟨u, ⟨huR, hsu⟩, humin⟩ := T.exists_min_image norm
        ((finite_mem_and_norm_le L R).subset fun _ hv => hv.1) hTe
      rw [successiveMinimum] at hsu
      obtain ⟨r, ⟨_, hrk⟩, hru⟩ := exists_lt_of_csInf_lt
        (⟨R, hR0, hRk⟩ : {r : ℝ | 0 ≤ r ∧
          k ≤ finrank ℝ (Submodule.span ℝ {v : E | v ∈ L ∧ ‖v‖ ≤ r})}.Nonempty) hsu
      exact hrk.trans <| Submodule.finrank_mono <| Submodule.span_mono fun v ⟨hvL, hvr⟩ =>
        ⟨hvL, le_of_not_gt fun hgt =>
          (hvr.trans_lt hru).not_ge (humin v ⟨⟨hvL, (hvr.trans hru.le).trans huR.2⟩, hgt⟩)⟩
    · exact hRk.trans <| Submodule.finrank_mono <| Submodule.span_mono fun v hv =>
        ⟨hv.1, le_of_not_gt fun hgt => hTe ⟨v, hv, hgt⟩⟩
  obtain ⟨B, hBA, hspB, hliB⟩ := exists_linearIndependent ℝ A
  have := hliB.finite
  have : Fintype B := Fintype.ofFinite B
  have hkB : k ≤ Fintype.card B := by
    rwa [← hspB, ← Subtype.range_coe (s := B), finrank_span_eq_card hliB] at hspan
  let f : Fin k ↪ B := (Fin.castLEEmb hkB).trans (Fintype.equivFin B).symm.toEmbedding
  exact ⟨fun i => f i, hliB.comp f f.injective, fun i => (hBA (f i).2).1, fun i => (hBA (f i).2).2⟩

variable [ProperSpace E]

/-- The first successive minimum is the first minimum. -/
theorem successiveMinimum_one (L : Submodule ℤ E) [DiscreteTopology L] (hL : L ≠ ⊥) :
    successiveMinimum L 1 = minimum L := by
  have h : {r : ℝ | 0 ≤ r ∧ 1 ≤ finrank ℝ (Submodule.span ℝ {v : E | v ∈ L ∧ ‖v‖ ≤ r})} =
      Set.Ici (minimum L) := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_Ici, Nat.one_le_iff_ne_zero, ne_eq,
      Submodule.finrank_eq_zero, Submodule.span_eq_bot, not_forall, minimum_le_iff hL]
    constructor
    · rintro ⟨-, v, ⟨hv, hvr⟩, hv0⟩; exact ⟨v, hv, hv0, hvr⟩
    · rintro ⟨v, hv, hv0, hvr⟩; exact ⟨(norm_nonneg v).trans hvr, v, ⟨hv, hvr⟩, hv0⟩
  rw [successiveMinimum, h, csInf_Ici]

/-- The first minimum is at most every positive successive minimum of a full-rank lattice. -/
theorem minimum_le_successiveMinimum (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : L ≠ ⊥) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ finrank ℝ E) :
    minimum L ≤ successiveMinimum L k :=
  successiveMinimum_one L hL ▸ successiveMinimum_mono L hk1 hk

end SuccessiveMinimum

section Minkowski

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Minkowski's first theorem for closed balls: if the closed ball of radius `r` has measure at
least `2ⁿ` times the covolume of `L`, then `L` has a nonzero vector of norm at most `r`. -/
theorem exists_ne_zero_mem_norm_le [Nontrivial E] (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (μ : Measure E) [μ.IsAddHaarMeasure] {r : ℝ}
    (h : ENNReal.ofReal (covolume L μ) * 2 ^ finrank ℝ E ≤ μ (closedBall 0 r)) :
    ∃ v ∈ L, v ≠ 0 ∧ ‖v‖ ≤ r := by
  let b := Free.chooseBasis ℤ L
  have hF := ZLattice.isAddFundamentalDomain b μ
  have hμF : μ (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) = ENNReal.ofReal (covolume L μ) := by
    rw [covolume_eq_measure_fundamentalDomain L μ hF, measureReal_def, ENNReal.ofReal_toReal]
    exact (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have : Countable L.toAddSubgroup := inferInstanceAs (Countable L)
  have : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
  obtain ⟨⟨v, hv⟩, hv0, hvr⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (L := L.toAddSubgroup) hF (fun x hx => by simpa using hx) (convex_closedBall 0 r)
    (isCompact_closedBall 0 r) (hμF ▸ h)
  exact ⟨v, hv, by simpa using hv0, by simpa using hvr⟩

/-- Minkowski's bound in the supremum norm: a full-rank lattice in `ℝⁿ`, `n ≥ 1`, has a nonzero
vector of supremum norm at most `det(L)^{1/n}`. -/
theorem exists_ne_zero_mem_norm_le_covolume_rpow {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ v ∈ L, v ≠ 0 ∧ ‖v‖ ≤ covolume L ^ ((Fintype.card ι : ℝ)⁻¹) := by
  refine exists_ne_zero_mem_norm_le L volume (le_of_eq ?_)
  have hc := (covolume_pos L volume).le
  have hn : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  rw [Real.volume_pi_closedBall _ (Real.rpow_nonneg hc _), mul_pow,
    Real.rpow_inv_natCast_pow hc hn, Module.finrank_fintype_fun_eq_card, mul_comm,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]

/-- `λ₁(L) ≤ det(L)^{1/n}` for a full-rank lattice in `ℝⁿ` with the supremum norm. -/
theorem minimum_le_covolume_rpow {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L] :
    minimum L ≤ covolume L ^ ((Fintype.card ι : ℝ)⁻¹) := by
  obtain ⟨v, hv, hv0, hvr⟩ := exists_ne_zero_mem_norm_le_covolume_rpow L
  exact (minimum_le_norm hv hv0).trans hvr

/-- Minkowski's bound in the Euclidean norm ([MicciancioGoldwasser2002], Chapter 1): a
full-rank lattice in `EuclideanSpace ℝ ι` of dimension `n ≥ 1` has a nonzero vector of norm at
most `√n · det(L)^{1/n}`. -/
theorem exists_ne_zero_mem_norm_le_sqrt_mul_covolume_rpow {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ v ∈ L, v ≠ 0 ∧
      ‖v‖ ≤ Real.sqrt (Fintype.card ι) * covolume L ^ ((Fintype.card ι : ℝ)⁻¹) := by
  let e : (ι → ℝ) ≃L[ℝ] EuclideanSpace ℝ ι := (EuclideanSpace.equiv ι ℝ).symm
  obtain ⟨u, hu, hu0, hur⟩ :=
    exists_ne_zero_mem_norm_le_covolume_rpow (ZLattice.comap ℝ L e.toLinearMap)
  rw [covolume_comap L volume volume (PiLp.volume_preserving_toLp ι)] at hur
  refine ⟨e u, hu, by simpa [e] using hu0, ?_⟩
  calc ‖e u‖ = Real.sqrt (∑ i, ‖u i‖ ^ 2) := by simp [e, EuclideanSpace.norm_eq]
    _ ≤ Real.sqrt (∑ _i : ι, ‖u‖ ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ =>
          pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm u i) 2)
    _ = Real.sqrt (Fintype.card ι) * ‖u‖ := by
        simp [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    _ ≤ _ := by gcongr

/-- `λ₁(L) ≤ √n · det(L)^{1/n}` for a full-rank lattice in `EuclideanSpace ℝ ι` of dimension
`n ≥ 1` ([MicciancioGoldwasser2002], Chapter 1). -/
theorem minimum_le_sqrt_mul_covolume_rpow {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L] [IsZLattice ℝ L] :
    minimum L ≤ Real.sqrt (Fintype.card ι) * covolume L ^ ((Fintype.card ι : ℝ)⁻¹) := by
  obtain ⟨v, hv, hv0, hvr⟩ := exists_ne_zero_mem_norm_le_sqrt_mul_covolume_rpow L
  exact (minimum_le_norm hv hv0).trans hvr

end Minkowski

end ZLattice
