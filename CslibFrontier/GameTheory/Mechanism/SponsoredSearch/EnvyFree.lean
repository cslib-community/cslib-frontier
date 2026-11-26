/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Locally envy-free assignments for sponsored search auctions

Static position-auction model with bidder-independent click-through rates (CTRs) `μ : Fin k → ℝ`
and unit weights `wⱼ = 1` ([LahaiePennockSaberiVohra2007], Chapter 28, §28.3, pp. 702–707). There
are `k` ad slots indexed by `0, …, k - 1` (slot `0` is the highest) and a finite bidder type `ι`
with per-click values `v : ι → ℝ`. An assignment `σ : Fin k ↪ ι` fills all `k` slots with
distinct bidders; existence requires `k ≤ Fintype.card ι`. (If there are fewer bidders than slots,
one restricts to the top slots; with nonnegative values filling all `k` slots is without loss in
the assignment LP (28.1)–(28.4) on p. 703. LP integrality is not proved here.)

We adopt the standard dummy-slot boundary convention for **local envy-freeness**
(`IsLocallyEnvyFree`): unassigned bidders sit in a fictitious slot `k` with CTR `0` and price `0`.
In [LahaiePennockSaberiVohra2007], §28.3.2, equations (28.9)–(28.10) (p. 705) are written only for
matched pairs `xᵢⱼ = 1`, without an explicit constraint on unassigned bidders. Read literally when
`k < Fintype.card ι`, a non-optimal assignment can satisfy the matched-pair inequalities; see the
checked counterexample in `CslibFrontierTests.GameTheory.SponsoredSearch`.

Under strictly decreasing positive CTRs (`StrictAnti μ` and `∀ i, 0 < μ i`), an assignment is
welfare-optimal iff it is assortative (`isOptimal_iff_isAssortative`) iff it admits locally
envy-free slot prices `p : Fin k → ℝ` (`isOptimal_iff_exists_isLocallyEnvyFree`, Theorem 28.1,
p. 706). Local envy-freeness also propagates by telescoping to global envy-freeness and individual
rationality (`IsLocallyEnvyFree.noEnvy`, `IsLocallyEnvyFree.utility_nonneg`,
`IsLocallyEnvyFree.unassigned_noEnvy_slot`).

The explicit formula `minEnvyFreePrice μ v σ i` defines the minimal nonnegative locally envy-free
slot prices (called the *Vickrey prices* in [LahaiePennockSaberiVohra2007], §28.3.2, p. 706;
identified with the Clarke-pivot payments of `Cslib.GameTheory.Mechanism.vcg` in
`CslibFrontier.GameTheory.Mechanism.SponsoredSearch.VCG`). No running-time claim is made.

## Main definitions

* `Cslib.GameTheory.SponsoredSearch.slotAlloc`: CTR allocated to bidder `j` by assignment `σ`.
* `Cslib.GameTheory.SponsoredSearch.welfare`: social welfare `∑ i, μ i * v (σ i)`.
* `Cslib.GameTheory.SponsoredSearch.IsOptimal`: welfare-maximizing assignment over all `Fin k ↪ ι`.
* `Cslib.GameTheory.SponsoredSearch.IsAssortative`: values non-increasing along `σ` and unassigned
  bidders weakly below assigned bidders (the "Northwest corner rule", p. 704).
* `Cslib.GameTheory.SponsoredSearch.IsLocallyEnvyFree`: locally envy-free slot prices
  `(28.9)–(28.10)` under the dummy-slot convention (`noEnvyAbove`, `noEnvyBelow`,
  `lastSlot_nonneg`, `unassigned_noEnvy`).
* `Cslib.GameTheory.SponsoredSearch.maxUnassignedValue`: maximum value among unassigned bidders
  (`0` if every bidder is assigned).
* `Cslib.GameTheory.SponsoredSearch.nextSlotValue`: value in the next lower slot (`v (σ (i + 1))`
  or a fallback `base` at the last slot).
* `Cslib.GameTheory.SponsoredSearch.minEnvyFreePrice`: explicit revenue-minimal nonnegative
  locally envy-free total slot price vector.

## Main results

* `Cslib.GameTheory.SponsoredSearch.isOptimal_iff_isAssortative`: under strictly decreasing
  positive CTRs, an assignment is optimal iff it is assortative (p. 704).
* `Cslib.GameTheory.SponsoredSearch.IsLocallyEnvyFree.noEnvy`: local envy-freeness implies global
  envy-freeness between all pairs of slots.
* `Cslib.GameTheory.SponsoredSearch.isOptimal_iff_exists_isLocallyEnvyFree`: **Theorem 28.1**
  ([LahaiePennockSaberiVohra2007], §28.3.2, p. 706): an assignment is optimal iff it is locally
  envy-free.
* `Cslib.GameTheory.SponsoredSearch.isLocallyEnvyFree_minEnvyFreePrice` and
  `Cslib.GameTheory.SponsoredSearch.minEnvyFreePrice_le`: for nonnegative values, `minEnvyFreePrice`
  is the pointwise least nonnegative locally envy-free price vector (base model of Exercise
  28.4(c), p. 715).

## References

* [S. Lahaie, D. M. Pennock, A. Saberi, and R. V. Vohra, *Sponsored Search Auctions*, Ch. 28 in
  *Algorithmic Game Theory*][LahaiePennockSaberiVohra2007]
-/

public section

namespace Cslib.GameTheory.SponsoredSearch

variable {k : ℕ} {ι : Type*}

/-- Total expected click-through rate assigned to bidder `j` by the assignment `σ : Fin k ↪ ι`
(`μ i` if `σ i = j`, and `0` if `j ∉ Set.range σ`). -/
@[expose] def slotAlloc [DecidableEq ι] (μ : Fin k → ℝ) (σ : Fin k ↪ ι) (j : ι) : ℝ :=
  ∑ i : Fin k, if σ i = j then μ i else 0

/-- An assigned bidder `σ i` receives click-through rate `μ i`. -/
@[simp]
theorem slotAlloc_apply_slot [DecidableEq ι] (μ : Fin k → ℝ) (σ : Fin k ↪ ι) (i : Fin k) :
    slotAlloc μ σ (σ i) = μ i := by
  simp only [slotAlloc, σ.injective.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- An unassigned bidder `j ∉ Set.range σ` receives click-through rate `0`. -/
theorem slotAlloc_of_not_mem_range [DecidableEq ι] (μ : Fin k → ℝ) (σ : Fin k ↪ ι) {j : ι}
    (hj : j ∉ Set.range σ) : slotAlloc μ σ j = 0 :=
  Finset.sum_eq_zero fun i _ => by
    have hne : σ i ≠ j := fun h => hj ⟨i, h⟩
    simp only [hne, ↓reduceIte]

private theorem slotAlloc_nonneg [DecidableEq ι] {μ : Fin k → ℝ} (hμ : ∀ i, 0 ≤ μ i)
    (σ : Fin k ↪ ι) (j : ι) : 0 ≤ slotAlloc μ σ j :=
  Finset.sum_nonneg fun i _ => by split_ifs <;> simp [hμ i]

/-- Total social welfare `∑ i, μ i * v (σ i)` of assignment `σ : Fin k ↪ ι` under CTRs `μ` and
per-click values `v` ([LahaiePennockSaberiVohra2007], §28.3.1, (28.1), p. 703). -/
@[expose] def welfare (μ : Fin k → ℝ) (v : ι → ℝ) (σ : Fin k ↪ ι) : ℝ :=
  ∑ i : Fin k, μ i * v (σ i)

/-- Rewrites welfare as a bidder-indexed sum of `slotAlloc μ σ j * v j`. -/
theorem sum_slotAlloc_mul [Fintype ι] [DecidableEq ι] (μ : Fin k → ℝ) (v : ι → ℝ)
    (σ : Fin k ↪ ι) : ∑ j : ι, slotAlloc μ σ j * v j = welfare μ v σ := by
  simp only [slotAlloc, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- An assignment `σ : Fin k ↪ ι` is **optimal** if it maximizes social welfare `welfare μ v` over
all full assignments of `k` distinct bidders to the `k` slots. -/
@[expose] def IsOptimal (μ : Fin k → ℝ) (v : ι → ℝ) (σ : Fin k ↪ ι) : Prop :=
  ∀ τ : Fin k ↪ ι, welfare μ v τ ≤ welfare μ v σ

/-- An assignment `σ : Fin k ↪ ι` is **assortative** for values `v` if values are non-increasing
along the slots and every unassigned bidder has value at most that of every assigned bidder
([LahaiePennockSaberiVohra2007], §28.3.1, p. 704). -/
structure IsAssortative (v : ι → ℝ) (σ : Fin k ↪ ι) : Prop where
  /-- Higher slots (smaller indices) receive weakly higher values. -/
  antitone : Antitone (v ∘ σ)
  /-- Every unassigned bidder has value at most that of every assigned bidder. -/
  unassigned_le : ∀ (i : Fin k) (j : ι), j ∉ Set.range σ → v j ≤ v (σ i)

private theorem antitone_fin_of_succ {f : Fin k → ℝ}
    (h : ∀ (i : ℕ) (hi : i + 1 < k), f ⟨i + 1, hi⟩ ≤ f ⟨i, by omega⟩) : Antitone f := by
  intro a b hab
  have hdiff : ∀ d (ha : a.val + d < k), f ⟨a.val + d, ha⟩ ≤ f a := by
    intro d
    induction d with
    | zero => intro ha; exact le_of_eq (by congr 1)
    | succ n ih => intro ha; exact (h (a.val + n) ha).trans (ih (by omega))
  simpa [Fin.ext_iff, Nat.add_sub_of_le hab] using hdiff (b.val - a.val) (by omega)

private theorem exists_perm_comp_eq [Finite ι] (σ τ : Fin k ↪ ι) :
    ∃ π : Equiv.Perm ι, ∀ i : Fin k, π (σ i) = τ i := by
  have := Fintype.ofFinite ι
  classical
  let s : Finset ι := Finset.univ.map σ
  let t : Finset ι := Finset.univ.map τ
  let eσ : Fin k ≃ {x : ι // x ∈ s} :=
    Equiv.ofBijective (fun i => ⟨σ i, Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
      ⟨fun _ _ h => σ.injective (congrArg Subtype.val h), fun ⟨_, hx⟩ => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx; exact ⟨i, rfl⟩⟩
  let eτ : Fin k ≃ {y : ι // y ∈ t} :=
    Equiv.ofBijective (fun i => ⟨τ i, Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
      ⟨fun _ _ h => τ.injective (congrArg Subtype.val h), fun ⟨_, hy⟩ => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hy; exact ⟨i, rfl⟩⟩
  let eIn : {x : ι // x ∈ s} ≃ {y : ι // y ∈ t} := eσ.symm.trans eτ
  have hcompl : Fintype.card {x : ι // ¬x ∈ s} = Fintype.card {y : ι // ¬y ∈ t} := by
    simp only [Fintype.card_subtype_compl, Fintype.card_coe, s, t, Finset.card_map, Finset.card_fin]
  let eOut : {x : ι // ¬x ∈ s} ≃ {y : ι // ¬y ∈ t} := Fintype.equivOfCardEq hcompl
  let π : Equiv.Perm ι :=
    (Equiv.sumCompl (· ∈ s)).symm.trans ((eIn.sumCongr eOut).trans (Equiv.sumCompl (· ∈ t)))
  refine ⟨π, fun i => ?_⟩
  have hL : (Equiv.sumCompl (· ∈ s)).symm (σ i) = Sum.inl (eσ i) :=
    (Equiv.symm_apply_eq _).mpr rfl
  change Equiv.sumCompl (· ∈ t) ((eIn.sumCongr eOut) ((Equiv.sumCompl (· ∈ s)).symm (σ i))) = τ i
  simp only [hL, Equiv.sumCongr_apply, Sum.map_inl, eIn, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

/-- **Northwest corner rule** ([LahaiePennockSaberiVohra2007], §28.3.1, p. 704): every assortative
assignment is optimal for weakly decreasing nonnegative CTRs (proved via Mathlib's rearrangement
inequality `Monovary.sum_mul_comp_perm_le_sum_mul`). -/
theorem IsAssortative.isOptimal [Finite ι] {μ : Fin k → ℝ} {v : ι → ℝ}
    {σ : Fin k ↪ ι} (hσ : IsAssortative v σ) (hμ : Antitone μ) (hμ_nonneg : ∀ i, 0 ≤ μ i) :
    IsOptimal μ v σ := by
  have := Fintype.ofFinite ι
  classical
  intro τ
  obtain ⟨π, hπ⟩ := exists_perm_comp_eq σ τ
  have hmono : Monovary (slotAlloc μ σ) v := by
    intro x y hxy
    by_cases hx : x ∈ Set.range σ
    · obtain ⟨i, rfl⟩ := hx
      by_cases hy : y ∈ Set.range σ
      · obtain ⟨r, rfl⟩ := hy
        rw [slotAlloc_apply_slot, slotAlloc_apply_slot]
        refine hμ (le_of_not_ge fun hir => ?_)
        exact not_lt_of_ge (hσ.antitone hir) hxy
      · exact absurd (hσ.unassigned_le i y hy) (not_le_of_gt hxy)
    · rw [slotAlloc_of_not_mem_range μ σ hx]
      exact slotAlloc_nonneg hμ_nonneg σ y
  have hrearr := hmono.sum_mul_comp_perm_le_sum_mul (σ := π)
  have hlhs : ∑ j : ι, slotAlloc μ σ j * v (π j) = welfare μ v τ := by
    calc ∑ j : ι, slotAlloc μ σ j * v (π j)
        = welfare μ (v ∘ π) σ := sum_slotAlloc_mul μ (v ∘ π) σ
      _ = welfare μ v τ := Finset.sum_congr rfl fun i _ => by
          simp only [Function.comp_apply, hπ i]
  rw [hlhs, sum_slotAlloc_mul] at hrearr
  exact hrearr

/-- Under strictly decreasing positive CTRs, every optimal assignment is assortative. -/
theorem IsOptimal.isAssortative {μ : Fin k → ℝ} {v : ι → ℝ} {σ : Fin k ↪ ι}
    (hσ : IsOptimal μ v σ) (hμ : StrictAnti μ) (hμ_pos : ∀ i, 0 < μ i) :
    IsAssortative v σ := by
  classical
  refine ⟨fun i₁ i₂ hle => ?_, fun i j hj => ?_⟩
  · rcases eq_or_lt_of_le hle with rfl | hlt
    · exact le_rfl
    · let τ : Fin k ↪ ι := (Equiv.swap i₁ i₂).toEmbedding.trans σ
      have hne : i₁ ≠ i₂ := ne_of_lt hlt
      have hdiff : welfare μ v τ - welfare μ v σ =
          (μ i₁ - μ i₂) * (v (σ i₂) - v (σ i₁)) := by
        simp only [welfare, ← Finset.sum_sub_distrib]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₁),
          ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ i₂⟩),
          Finset.sum_eq_zero fun r hr => by
            simp [τ, Equiv.swap_apply_of_ne_of_ne
              (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hr)) (Finset.ne_of_mem_erase hr)]]
        simp only [τ, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
          Equiv.swap_apply_left, Equiv.swap_apply_right, add_zero]
        ring
      change v (σ i₂) ≤ v (σ i₁)
      nlinarith [hσ τ, hμ hlt]
  · let τ : Fin k ↪ ι :=
      { toFun := fun r => if r = i then j else σ r
        inj' := fun a b hab => by
          dsimp only at hab
          split_ifs at hab with ha hb
          · exact ha.trans hb.symm
          · exact absurd ⟨b, hab.symm⟩ hj
          · exact absurd ⟨a, hab⟩ hj
          · exact σ.injective hab }
    have hdiff : welfare μ v τ - welfare μ v σ = μ i * (v j - v (σ i)) := by
      have hτ (r : Fin k) : τ r = if r = i then j else σ r := rfl
      simp only [welfare, ← Finset.sum_sub_distrib, hτ]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
        Finset.sum_eq_zero fun r hr => by simp [Finset.ne_of_mem_erase hr]]
      simp only [↓reduceIte, add_zero]; ring
    nlinarith [hσ τ, hμ_pos i]

/-- Under strictly decreasing positive CTRs, an assignment is optimal iff it is assortative
([LahaiePennockSaberiVohra2007], §28.3.1, p. 704). -/
theorem isOptimal_iff_isAssortative [Finite ι] {μ : Fin k → ℝ} {v : ι → ℝ}
    {σ : Fin k ↪ ι} (hμ : StrictAnti μ) (hμ_pos : ∀ i, 0 < μ i) :
    IsOptimal μ v σ ↔ IsAssortative v σ :=
  ⟨fun h => h.isAssortative hμ hμ_pos,
    fun h => h.isOptimal hμ.antitone fun i => (hμ_pos i).le⟩

/-- An optimal assignment exists whenever there are at least `k` bidders. -/
theorem exists_isOptimal [Fintype ι] (μ : Fin k → ℝ) (v : ι → ℝ) (hk : k ≤ Fintype.card ι) :
    ∃ σ : Fin k ↪ ι, IsOptimal μ v σ := by
  classical
  have hne : Nonempty (Fin k ↪ ι) :=
    ⟨(Fin.castLEEmb hk).trans (Fintype.equivFin ι).symm.toEmbedding⟩
  obtain ⟨σ, -, hσ⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin k ↪ ι))
    (welfare μ v) Finset.univ_nonempty
  exact ⟨σ, fun τ => hσ τ (Finset.mem_univ τ)⟩

/-- An assortative assignment exists whenever there are at least `k` bidders. -/
theorem exists_isAssortative [Fintype ι] (v : ι → ℝ) (hk : k ≤ Fintype.card ι) :
    ∃ σ : Fin k ↪ ι, IsAssortative v σ := by
  let μ₀ : Fin k → ℝ := fun i => (k : ℝ) - (i.val : ℝ)
  have hμ₀ : StrictAnti μ₀ := fun _ _ hab => sub_lt_sub_left (Nat.cast_lt.mpr hab) _
  have hμ₀_pos : ∀ i : Fin k, 0 < μ₀ i := fun i => sub_pos.mpr (Nat.cast_lt.mpr i.isLt)
  exact (exists_isOptimal μ₀ v hk).imp fun _ hσ => hσ.isAssortative hμ₀ hμ₀_pos

/-- An assignment `σ : Fin k ↪ ι` with slot prices `p : Fin k → ℝ` (expected payments per
impression) is **locally envy-free** with respect to CTRs `μ` and per-click values `v`
([LahaiePennockSaberiVohra2007], §28.3.2, (28.9)–(28.10), pp. 705–706) under the standard
dummy-slot convention, treating every unassigned bidder as sitting in a fictitious slot `k` with
CTR `0` and price `0`:

* `noEnvyAbove` (28.9): the bidder in slot `i + 1` weakly prefers slot `i + 1` to slot `i`;
* `noEnvyBelow` (28.10): the bidder in slot `i` weakly prefers slot `i` to slot `i + 1`;
* `lastSlot_nonneg` (boundary of (28.10)): the bidder in the last real slot `k - 1` gets
  nonnegative utility (`μ (k - 1) * v (σ (k - 1)) - p (k - 1) ≥ 0`);
* `unassigned_noEnvy` (boundary of (28.9)): no unassigned bidder prefers slot `k - 1` to the dummy
  slot (`μ (k - 1) * v j - p (k - 1) ≤ 0`).

*Deviation from the printed source*: (28.9)–(28.10) in [LahaiePennockSaberiVohra2007] are written
only for matched pairs `xᵢⱼ = 1` without explicitly adding the dummy-slot condition on unassigned
bidders. When `k < Fintype.card ι`, omitting `unassigned_noEnvy` falsifies Theorem 28.1
(`IsLocallyEnvyFree → IsOptimal`); see `CslibFrontierTests.GameTheory.SponsoredSearch`. -/
structure IsLocallyEnvyFree (μ : Fin k → ℝ) (v : ι → ℝ) (σ : Fin k ↪ ι) (p : Fin k → ℝ) :
    Prop where
  /-- Bidder in slot `i + 1` does not envy slot `i` above it (`(28.9)`). -/
  noEnvyAbove : ∀ (i : ℕ) (h : i + 1 < k),
    μ ⟨i, by omega⟩ * v (σ ⟨i + 1, h⟩) - p ⟨i, by omega⟩ ≤
      μ ⟨i + 1, h⟩ * v (σ ⟨i + 1, h⟩) - p ⟨i + 1, h⟩
  /-- Bidder in slot `i` does not envy slot `i + 1` below it (`(28.10)`). -/
  noEnvyBelow : ∀ (i : ℕ) (h : i + 1 < k),
    μ ⟨i + 1, h⟩ * v (σ ⟨i, by omega⟩) - p ⟨i + 1, h⟩ ≤
      μ ⟨i, by omega⟩ * v (σ ⟨i, by omega⟩) - p ⟨i, by omega⟩
  /-- Bidder in the last slot `k - 1` weakly prefers it to the dummy slot (CTR `0`, price `0`). -/
  lastSlot_nonneg : ∀ (h : 0 < k),
    0 ≤ μ ⟨k - 1, by omega⟩ * v (σ ⟨k - 1, by omega⟩) - p ⟨k - 1, by omega⟩
  /-- Every unassigned bidder weakly prefers the dummy slot to the last real slot `k - 1`. -/
  unassigned_noEnvy : ∀ (h : 0 < k) (j : ι), j ∉ Set.range σ →
    μ ⟨k - 1, by omega⟩ * v j - p ⟨k - 1, by omega⟩ ≤ 0

/-- Under strictly decreasing positive CTRs, every locally envy-free assignment is assortative
([LahaiePennockSaberiVohra2007], Theorem 28.1, forward step, p. 706). -/
theorem IsLocallyEnvyFree.isAssortative {μ : Fin k → ℝ} {v : ι → ℝ} {σ : Fin k ↪ ι}
    {p : Fin k → ℝ} (hlef : IsLocallyEnvyFree μ v σ p)
    (hμ : StrictAnti μ) (hμ_pos : ∀ i, 0 < μ i) : IsAssortative v σ := by
  have hanti : Antitone (v ∘ σ) := antitone_fin_of_succ fun i hi => by
    have hμlt : μ ⟨i + 1, hi⟩ < μ ⟨i, by omega⟩ := hμ (by simp [Fin.lt_def])
    change v (σ ⟨i + 1, hi⟩) ≤ v (σ ⟨i, by omega⟩)
    nlinarith [hlef.noEnvyAbove i hi, hlef.noEnvyBelow i hi]
  refine ⟨hanti, fun i j hj => ?_⟩
  have hk : 0 < k := Fin.pos i
  refine (?_ : v j ≤ v (σ ⟨k - 1, by omega⟩)).trans
    (hanti (Fin.le_def.mpr (Nat.le_sub_one_of_lt i.isLt)))
  nlinarith [hlef.lastSlot_nonneg hk, hlef.unassigned_noEnvy hk j hj, hμ_pos ⟨k - 1, by omega⟩]

/-- Under strictly decreasing positive CTRs, local envy-freeness implies **global envy-freeness**
between any two slots: bidder `σ i` weakly prefers slot `i` to every slot `r`. -/
theorem IsLocallyEnvyFree.noEnvy {μ : Fin k → ℝ} {v : ι → ℝ} {σ : Fin k ↪ ι} {p : Fin k → ℝ}
    (hlef : IsLocallyEnvyFree μ v σ p) (hμ : StrictAnti μ) (hμ_pos : ∀ i, 0 < μ i)
    (i r : Fin k) :
    μ r * v (σ i) - p r ≤ μ i * v (σ i) - p i := by
  have hanti := (hlef.isAssortative hμ hμ_pos).antitone
  rcases le_total i r with hir | hri
  · have hstep (d : ℕ) : ∀ hd : i.val + d < k,
        μ ⟨i.val + d, hd⟩ * v (σ i) - p ⟨i.val + d, hd⟩ ≤ μ i * v (σ i) - p i := by
      induction d with
      | zero => intro hd; exact le_of_eq (by congr 2)
      | succ n ih =>
        intro hd
        have hv : v (σ ⟨i.val + n, by omega⟩) ≤ v (σ i) :=
          hanti (Fin.le_def.mpr (Nat.le_add_right _ _))
        have hμle : μ ⟨i.val + n + 1, hd⟩ ≤ μ ⟨i.val + n, by omega⟩ :=
          (hμ (Fin.lt_def.mpr (Nat.lt_succ_self _))).le
        change μ ⟨i.val + n + 1, hd⟩ * v (σ i) - p ⟨i.val + n + 1, hd⟩ ≤ _
        nlinarith [hlef.noEnvyBelow (i.val + n) hd, ih (by omega)]
    simpa [Fin.ext_iff, Nat.add_sub_of_le hir] using hstep (r.val - i.val) (by omega)
  · have hstep (d : ℕ) : ∀ hd : d ≤ i.val,
        μ ⟨i.val - d, by omega⟩ * v (σ i) - p ⟨i.val - d, by omega⟩ ≤ μ i * v (σ i) - p i := by
      induction d with
      | zero => intro hd; exact le_of_eq (by congr 2)
      | succ n ih =>
        intro hd
        have hs := hlef.noEnvyAbove (i.val - (n + 1)) (by omega)
        have hfinEq : (⟨i.val - (n + 1) + 1, by omega⟩ : Fin k) = ⟨i.val - n, by omega⟩ :=
          Fin.ext (by dsimp; omega)
        rw [hfinEq] at hs
        have hv : v (σ i) ≤ v (σ ⟨i.val - n, by omega⟩) :=
          hanti (Fin.le_def.mpr (Nat.sub_le _ _))
        have hμle : μ ⟨i.val - n, by omega⟩ ≤ μ ⟨i.val - (n + 1), by omega⟩ :=
          (hμ (Fin.lt_def.mpr (by dsimp; omega))).le
        nlinarith [ih (by omega)]
    simpa [Fin.ext_iff, Nat.sub_sub_self hri] using hstep (i.val - r.val) (by omega)

/-- Under strictly decreasing positive CTRs, every assigned bidder gets nonnegative utility under a
locally envy-free price vector (individual rationality). -/
theorem IsLocallyEnvyFree.utility_nonneg {μ : Fin k → ℝ} {v : ι → ℝ} {σ : Fin k ↪ ι}
    {p : Fin k → ℝ} (hlef : IsLocallyEnvyFree μ v σ p) (hμ : StrictAnti μ)
    (hμ_pos : ∀ i, 0 < μ i) (i : Fin k) : 0 ≤ μ i * v (σ i) - p i := by
  have hk : 0 < k := Fin.pos i
  let last : Fin k := ⟨k - 1, by omega⟩
  have hv : v (σ last) ≤ v (σ i) :=
    (hlef.isAssortative hμ hμ_pos).antitone (Fin.le_def.mpr (Nat.le_sub_one_of_lt i.isLt))
  nlinarith [hlef.lastSlot_nonneg hk, (hμ_pos last).le, hlef.noEnvy hμ hμ_pos i last]

private theorem fin_rev_induction {P : Fin k → Prop} (hk : 0 < k)
    (hlast : P ⟨k - 1, by omega⟩)
    (hstep : ∀ (i : ℕ) (hi : i + 1 < k), P ⟨i + 1, hi⟩ → P ⟨i, by omega⟩)
    (r : Fin k) : P r := by
  have hdown : ∀ d (hd : d < k), P ⟨k - 1 - d, by omega⟩ := by
    intro d
    induction d with
    | zero => intro _; exact hlast
    | succ n ih =>
      intro hd
      have hfinEq : (⟨k - 1 - (n + 1) + 1, by omega⟩ : Fin k) = ⟨k - 1 - n, by omega⟩ := by
        apply Fin.ext; dsimp; omega
      exact hstep (k - 1 - (n + 1)) (by omega) (hfinEq.symm ▸ ih (by omega))
  simpa [Fin.ext_iff, Nat.sub_sub_self (Nat.le_sub_one_of_lt r.isLt)] using
    hdown (k - 1 - r.val) (by omega)

/-- Under strictly decreasing positive CTRs, no unassigned bidder envies *any* slot under a locally
envy-free price vector. -/
theorem IsLocallyEnvyFree.unassigned_noEnvy_slot {μ : Fin k → ℝ} {v : ι → ℝ} {σ : Fin k ↪ ι}
    {p : Fin k → ℝ} (hlef : IsLocallyEnvyFree μ v σ p) (hμ : StrictAnti μ)
    (hμ_pos : ∀ i, 0 < μ i) {j : ι} (hj : j ∉ Set.range σ) (r : Fin k) :
    μ r * v j - p r ≤ 0 := by
  have hσ := hlef.isAssortative hμ hμ_pos
  have hk : 0 < k := Fin.pos r
  refine fin_rev_induction (P := fun s => μ s * v j - p s ≤ 0) hk
    (hlef.unassigned_noEnvy hk j hj) (fun i hi hih => ?_) r
  have hμle : μ ⟨i + 1, hi⟩ ≤ μ ⟨i, by omega⟩ := (hμ (Fin.lt_def.mpr (Nat.lt_succ_self i))).le
  nlinarith [hlef.noEnvyAbove i hi, hσ.unassigned_le ⟨i + 1, hi⟩ j hj]

/-- The highest value `v j` among unassigned bidders `j ∉ Set.range σ`, or `0` if every bidder is
assigned (`Fintype.card ι = k`). -/
@[expose] noncomputable def maxUnassignedValue [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (σ : Fin k ↪ ι) : ℝ :=
  if h : (Finset.univ \ Finset.univ.map σ).Nonempty then
    (Finset.univ \ Finset.univ.map σ).sup' h v
  else 0

private theorem mem_unassigned_iff [Fintype ι] [DecidableEq ι] (σ : Fin k ↪ ι) (j : ι) :
    j ∈ Finset.univ \ Finset.univ.map σ ↔ j ∉ Set.range σ := by
  simp [Set.mem_range]

/-- Every unassigned bidder's value is at most `maxUnassignedValue v σ`. -/
theorem le_maxUnassignedValue [Fintype ι] [DecidableEq ι] (v : ι → ℝ) (σ : Fin k ↪ ι) {j : ι}
    (hj : j ∉ Set.range σ) : v j ≤ maxUnassignedValue v σ := by
  have hmem := (mem_unassigned_iff σ j).mpr hj
  unfold maxUnassignedValue
  split_ifs with hne
  exacts [Finset.le_sup' v hmem, (hne ⟨j, hmem⟩).elim]

/-- If all bidder values are nonnegative, then `maxUnassignedValue v σ` is nonnegative. -/
theorem maxUnassignedValue_nonneg [Fintype ι] [DecidableEq ι] {v : ι → ℝ} (hv : ∀ j, 0 ≤ v j)
    (σ : Fin k ↪ ι) : 0 ≤ maxUnassignedValue v σ := by
  unfold maxUnassignedValue
  split_ifs with h
  · obtain ⟨j, hj⟩ := h
    exact (hv j).trans (Finset.le_sup' v hj)
  · exact le_rfl

/-- Upper bound for `maxUnassignedValue v σ` by splitting on whether an unassigned bidder
exists. -/
theorem maxUnassignedValue_le [Fintype ι] [DecidableEq ι] {v : ι → ℝ} {σ : Fin k ↪ ι} {c : ℝ}
    (hc0 : (Finset.univ \ Finset.univ.map σ).Nonempty → ∀ j, j ∉ Set.range σ → v j ≤ c)
    (hcEmpty : ¬(Finset.univ \ Finset.univ.map σ).Nonempty → 0 ≤ c) :
    maxUnassignedValue v σ ≤ c := by
  unfold maxUnassignedValue
  split_ifs with h
  · exact Finset.sup'_le h v fun j hj => hc0 h j ((mem_unassigned_iff σ j).mp hj)
  · exact hcEmpty h

/-- `maxUnassignedValue` depends only on the values of unassigned bidders. -/
theorem maxUnassignedValue_congr [Fintype ι] [DecidableEq ι] {v₁ v₂ : ι → ℝ} {σ : Fin k ↪ ι}
    (h : ∀ j, j ∉ Set.range σ → v₁ j = v₂ j) :
    maxUnassignedValue v₁ σ = maxUnassignedValue v₂ σ := by
  unfold maxUnassignedValue
  split_ifs with hne
  · exact Finset.sup'_congr hne rfl fun j hj => h j ((mem_unassigned_iff σ j).mp hj)
  · rfl

/-- The value directly below slot `i : Fin k` under assignment `σ`: `v (σ (i + 1))` when
`i.val + 1 < k`, and the fallback `base` at the last slot `i = k - 1`. -/
@[expose] def nextSlotValue (v : ι → ℝ) (σ : Fin k ↪ ι) (base : ℝ) (i : Fin k) : ℝ :=
  if h : i.val + 1 < k then v (σ ⟨i.val + 1, h⟩) else base

private def priceFromBase (μ : Fin k → ℝ) (v : ι → ℝ) (σ : Fin k ↪ ι) (base : ℝ)
    (i : Fin k) : ℝ :=
  ∑ r ∈ Finset.Ici i,
    (μ r - (if h : r.val + 1 < k then μ ⟨r.val + 1, h⟩ else 0)) * nextSlotValue v σ base r

private theorem priceFromBase_sub_succ (μ : Fin k → ℝ) (v : ι → ℝ) (σ : Fin k ↪ ι) (base : ℝ)
    (i : ℕ) (hi : i + 1 < k) :
    priceFromBase μ v σ base ⟨i, by omega⟩ - priceFromBase μ v σ base ⟨i + 1, hi⟩ =
      (μ ⟨i, by omega⟩ - μ ⟨i + 1, hi⟩) * v (σ ⟨i + 1, hi⟩) := by
  have hIci : Finset.Ici (⟨i, by omega⟩ : Fin k) =
      insert ⟨i, by omega⟩ (Finset.Ici ⟨i + 1, hi⟩) := by
    ext r
    simp only [Finset.mem_Ici, Finset.mem_insert, Fin.le_def, Fin.ext_iff]
    omega
  have hnotmem : (⟨i, by omega⟩ : Fin k) ∉ Finset.Ici ⟨i + 1, hi⟩ := by
    simp [Fin.le_def]
  unfold priceFromBase
  rw [hIci, Finset.sum_insert hnotmem, add_sub_cancel_right]
  simp only [nextSlotValue, hi, ↓reduceDIte]

private theorem priceFromBase_last (μ : Fin k → ℝ) (v : ι → ℝ) (σ : Fin k ↪ ι) (base : ℝ)
    (hk : 0 < k) :
    priceFromBase μ v σ base ⟨k - 1, by omega⟩ = μ ⟨k - 1, by omega⟩ * base := by
  have hIci : Finset.Ici (⟨k - 1, by omega⟩ : Fin k) = {⟨k - 1, by omega⟩} := by
    ext r
    simp only [Finset.mem_Ici, Finset.mem_singleton, Fin.le_def, Fin.ext_iff]
    omega
  have hnot : ¬(k - 1 + 1 < k) := by omega
  simp only [priceFromBase, hIci, Finset.sum_singleton, nextSlotValue, hnot, ↓reduceDIte, sub_zero]

private theorem isLocallyEnvyFree_priceFromBase {μ : Fin k → ℝ} {v : ι → ℝ} {σ : Fin k ↪ ι}
    {base : ℝ} (hσ : IsAssortative v σ) (hμ : Antitone μ) (hμ_nonneg : ∀ i, 0 ≤ μ i)
    (hbase_hi : ∀ hk : 0 < k, base ≤ v (σ ⟨k - 1, by omega⟩))
    (hbase_lo : ∀ j : ι, j ∉ Set.range σ → v j ≤ base) :
    IsLocallyEnvyFree μ v σ (priceFromBase μ v σ base) where
  noEnvyAbove i hi := by
    linarith [priceFromBase_sub_succ μ v σ base i hi]
  noEnvyBelow i hi := by
    have hle : (⟨i, by omega⟩ : Fin k) ≤ ⟨i + 1, hi⟩ := Fin.le_def.mpr (Nat.le_succ i)
    have hv : v (σ ⟨i + 1, hi⟩) ≤ v (σ ⟨i, by omega⟩) := hσ.antitone hle
    nlinarith [priceFromBase_sub_succ μ v σ base i hi, hμ hle]
  lastSlot_nonneg hk := by
    rw [priceFromBase_last μ v σ base hk]
    nlinarith [hμ_nonneg ⟨k - 1, by omega⟩, hbase_hi hk]
  unassigned_noEnvy hk j hj := by
    rw [priceFromBase_last μ v σ base hk]
    nlinarith [hμ_nonneg ⟨k - 1, by omega⟩, hbase_lo j hj]

/-- The minimal nonnegative locally envy-free total slot price vector for assignment `σ`:
`minEnvyFreePrice μ v σ i = ∑ r ≥ i, (μ r - μ (r + 1)) * v (σ (r + 1))`
(with `μ k = 0` and the value for `r = k - 1` equal to `maxUnassignedValue v σ`).

In [LahaiePennockSaberiVohra2007], §28.3.2, p. 706, these are called the *Vickrey prices*;
`CslibFrontier.GameTheory.Mechanism.SponsoredSearch.VCG` proves they equal the Clarke-pivot
payments of `Cslib.GameTheory.Mechanism.vcg`. -/
noncomputable def minEnvyFreePrice [Fintype ι] [DecidableEq ι]
    (μ : Fin k → ℝ) (v : ι → ℝ) (σ : Fin k ↪ ι) (i : Fin k) : ℝ :=
  priceFromBase μ v σ (maxUnassignedValue v σ) i

/-- Explicit sum expansion of `minEnvyFreePrice`. -/
theorem minEnvyFreePrice_eq_sum [Fintype ι] [DecidableEq ι]
    (μ : Fin k → ℝ) (v : ι → ℝ) (σ : Fin k ↪ ι) (i : Fin k) :
    minEnvyFreePrice μ v σ i =
      ∑ r ∈ Finset.Ici i,
        (μ r - (if h : r.val + 1 < k then μ ⟨r.val + 1, h⟩ else 0)) *
          nextSlotValue v σ (maxUnassignedValue v σ) r := by
  simp only [minEnvyFreePrice, priceFromBase]

/-- Adjacent slot difference for `minEnvyFreePrice`. -/
theorem minEnvyFreePrice_sub_succ [Fintype ι] [DecidableEq ι] (μ : Fin k → ℝ) (v : ι → ℝ)
    (σ : Fin k ↪ ι) (i : ℕ) (hi : i + 1 < k) :
    minEnvyFreePrice μ v σ ⟨i, by omega⟩ - minEnvyFreePrice μ v σ ⟨i + 1, hi⟩ =
      (μ ⟨i, by omega⟩ - μ ⟨i + 1, hi⟩) * v (σ ⟨i + 1, hi⟩) :=
  priceFromBase_sub_succ μ v σ (maxUnassignedValue v σ) i hi

/-- Last-slot formula for `minEnvyFreePrice`: `μ (k - 1) * maxUnassignedValue v σ`. -/
theorem minEnvyFreePrice_last [Fintype ι] [DecidableEq ι] (μ : Fin k → ℝ) (v : ι → ℝ)
    (σ : Fin k ↪ ι) (hk : 0 < k) :
    minEnvyFreePrice μ v σ ⟨k - 1, by omega⟩ = μ ⟨k - 1, by omega⟩ * maxUnassignedValue v σ :=
  priceFromBase_last μ v σ (maxUnassignedValue v σ) hk

/-- For weakly decreasing nonnegative CTRs and nonnegative values, `minEnvyFreePrice` is
nonnegative. -/
theorem minEnvyFreePrice_nonneg [Fintype ι] [DecidableEq ι] {μ : Fin k → ℝ} {v : ι → ℝ}
    (hμ : Antitone μ) (hμ_nonneg : ∀ i, 0 ≤ μ i) (hv : ∀ j, 0 ≤ v j) (σ : Fin k ↪ ι)
    (i : Fin k) : 0 ≤ minEnvyFreePrice μ v σ i := by
  refine Finset.sum_nonneg fun r _ => mul_nonneg ?_ ?_
  · split_ifs with h
    · exact sub_nonneg.mpr (hμ (show r ≤ ⟨r.val + 1, h⟩ by change r.val ≤ r.val + 1; omega))
    · rw [sub_zero]; exact hμ_nonneg r
  · unfold nextSlotValue
    split_ifs
    · exact hv _
    · exact maxUnassignedValue_nonneg hv σ

/-- For any assortative assignment and nonnegative values, `minEnvyFreePrice` is a locally
envy-free slot price vector. -/
theorem isLocallyEnvyFree_minEnvyFreePrice [Fintype ι] [DecidableEq ι] {μ : Fin k → ℝ}
    {v : ι → ℝ} {σ : Fin k ↪ ι} (hσ : IsAssortative v σ) (hμ : Antitone μ)
    (hμ_nonneg : ∀ i, 0 ≤ μ i) (hv : ∀ j, 0 ≤ v j) :
    IsLocallyEnvyFree μ v σ (minEnvyFreePrice μ v σ) :=
  isLocallyEnvyFree_priceFromBase hσ hμ hμ_nonneg
    (fun hk => maxUnassignedValue_le (fun _ j hj => hσ.unassigned_le ⟨k - 1, by omega⟩ j hj)
      (fun _ => hv _))
    (fun j hj => le_maxUnassignedValue v σ hj)

/-- `minEnvyFreePrice` is the pointwise least nonnegative locally envy-free price vector
(base unit-weight model of [LahaiePennockSaberiVohra2007], Exercise 28.4(c), p. 715). -/
theorem minEnvyFreePrice_le [Fintype ι] [DecidableEq ι] {μ : Fin k → ℝ} {v : ι → ℝ}
    {σ : Fin k ↪ ι} {p : Fin k → ℝ} (hp : IsLocallyEnvyFree μ v σ p) (hp_nonneg : ∀ i, 0 ≤ p i)
    (i : Fin k) : minEnvyFreePrice μ v σ i ≤ p i := by
  have hk : 0 < k := Fin.pos i
  refine fin_rev_induction (P := fun r => minEnvyFreePrice μ v σ r ≤ p r) hk ?_
    (fun r hr hih => ?_) i
  · rw [minEnvyFreePrice_last μ v σ hk]
    unfold maxUnassignedValue
    split_ifs with hne
    · obtain ⟨j, hjmem, hj⟩ := Finset.exists_mem_eq_sup' hne v
      rw [hj]; linarith [hp.unassigned_noEnvy hk j ((mem_unassigned_iff σ j).mp hjmem)]
    · rw [mul_zero]; exact hp_nonneg ⟨k - 1, by omega⟩
  · linarith [minEnvyFreePrice_sub_succ μ v σ r hr, hp.noEnvyAbove r hr]

/-- **Theorem 28.1** ([LahaiePennockSaberiVohra2007], §28.3.2, p. 706): under strictly decreasing
positive click-through rates `μ`, a full assignment `σ : Fin k ↪ ι` is optimal if and only if
there exist slot prices `p : Fin k → ℝ` making `(σ, p)` locally envy-free.

*Scope and deviation*: works with `αᵢⱼ = μᵢ` (bidder-independent CTRs), arbitrary real values
`v : ι → ℝ`, and `IsLocallyEnvyFree` with the dummy-slot boundary convention for unassigned bidders
(see `IsLocallyEnvyFree`). Over *full* embeddings `Fin k ↪ ι` all `k` slots remain filled even if
some `v j < 0` (witnessed with possibly negative slot prices `p` shifted by the last-slot bidder's
value when `k = Fintype.card ι`); over partial matchings without forcing all slots filled, dropping
negative-value bidders would increase welfare, so nonnegative values `∀ j, 0 ≤ v j` ensure full
assignments are without loss. When `∀ j, 0 ≤ v j`, `isLocallyEnvyFree_minEnvyFreePrice` supplies
the explicit nonnegative witness `minEnvyFreePrice μ v σ`. Both `StrictAnti μ` and `∀ i, 0 < μ i`
are necessary; counterexamples when either is weakened appear in
`CslibFrontierTests.GameTheory.SponsoredSearch`. -/
theorem isOptimal_iff_exists_isLocallyEnvyFree [Finite ι] {μ : Fin k → ℝ}
    {v : ι → ℝ} {σ : Fin k ↪ ι} (hμ : StrictAnti μ) (hμ_pos : ∀ i, 0 < μ i) :
    IsOptimal μ v σ ↔ ∃ p : Fin k → ℝ, IsLocallyEnvyFree μ v σ p := by
  have := Fintype.ofFinite ι
  classical
  constructor
  · intro hopt
    have hσ := hopt.isAssortative hμ hμ_pos
    let base : ℝ :=
      if h : (Finset.univ \ Finset.univ.map σ).Nonempty then
        (Finset.univ \ Finset.univ.map σ).sup' h v
      else if hk : 0 < k then v (σ ⟨k - 1, by omega⟩) else 0
    refine ⟨priceFromBase μ v σ base, isLocallyEnvyFree_priceFromBase hσ hμ.antitone
      (fun i => (hμ_pos i).le) (fun hk => ?_) (fun j hj => ?_)⟩
    · dsimp only [base]
      split_ifs with hne
      · exact Finset.sup'_le hne v fun j hj => hσ.unassigned_le _ j ((mem_unassigned_iff σ j).mp hj)
      · exact le_rfl
    · have hmem := (mem_unassigned_iff σ j).mpr hj
      have hne : (Finset.univ \ Finset.univ.map σ).Nonempty := ⟨j, hmem⟩
      simpa only [base, hne, ↓reduceDIte] using Finset.le_sup' v hmem
  · rintro ⟨p, hlef⟩
    exact (hlef.isAssortative hμ hμ_pos).isOptimal hμ.antitone fun i => (hμ_pos i).le

end Cslib.GameTheory.SponsoredSearch
