/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Beck–Fiala discrepancy and integer-making theorems

Let `A : ι → Finset κ` be a finite family of subsets of a ground type `κ` in which every
element `v : κ` belongs to at most `t` sets (`#{i : ι | v ∈ A i} ≤ t`).

* **Integer-making / fractional rounding** (`Cslib.Combinatorics.beckFiala_rounding`): over any
  linearly ordered field `𝕜`, when `0 < t`, every weighting `x : κ → 𝕜` with `0 ≤ x v ≤ 1` can be
  rounded to `χ : κ → ℤ` with `χ v ∈ {0, 1}`, fixing every coordinate already in `{0, 1}`, so that
  every set's sum changes by strictly less than `t`: `|∑ v ∈ A i, ((χ v : 𝕜) - x v)| < t`.
* **Combinatorial discrepancy** (`Cslib.Combinatorics.beckFiala`): there exists a two-coloring
  `χ : κ → ℤ` with `χ v ∈ {-1, 1}` such that every set satisfies
  `(∑ v ∈ A i, χ v).natAbs ≤ 2 * t - 1` (yielding `0` when `t = 0`, and
  `|∑ v ∈ A i, χ v| ≤ 2 * t - 1` for `t ≥ 1`).

The proof iteratively updates `x` inside the hypercube over the finite union `U = ⋃ i, A i` along a
nonzero kernel vector of the incidence matrix restricted to active sets `{i | t < #(A i ∩ F)}` on
the floating variables `F = {v ∈ U | 0 < x v ∧ x v < 1}`. Double counting incidences against `F`
gives `(t + 1) * #𝒮 ≤ t * #F`, so `#𝒮 < #F` whenever `F` is nonempty; moving to
the first cube face fixes at least one coordinate in `{0, 1}` while keeping every active set's
sum invariant, and once a set drops to at most `t` floating elements its total future change is
strictly bounded by `t`.

## Main results

* `Cslib.Combinatorics.beckFiala_rounding`: Beck–Fiala `[0, 1] → {0, 1}` integer-making theorem
  over any linearly ordered field `𝕜` (in particular `ℝ` and `ℚ`) with error `< t`.
* `Cslib.Combinatorics.beckFiala`: Beck–Fiala `2 * t - 1` signed discrepancy theorem.

## References

* [N. Alon, J. H. Spencer, *The Probabilistic Method*][AlonSpencer2016] (Beck–Fiala theorem and
  iterative linear-algebra rounding; exact theorem number and page locator not verified against a
  primary PDF).
-/

public section

namespace Cslib.Combinatorics

open Finset

section Helpers

/-- The floating coordinates `v ∈ U` with `0 < x v < 1`. -/
private noncomputable def floating {κ 𝕜 : Type*} [Preorder 𝕜] [Zero 𝕜] [One 𝕜]
    (U : Finset κ) (x : κ → 𝕜) : Finset κ :=
  letI := Classical.decPred fun v : κ => 0 < x v ∧ x v < 1
  U.filter fun v => 0 < x v ∧ x v < 1

/-- The active sets containing strictly more than `t` floating coordinates. -/
private def activeSets {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (A : ι → Finset κ) (t : ℕ) (F : Finset κ) : Finset ι :=
  univ.filter fun i => t < #(A i ∩ F)

private theorem mem_floating_iff {κ 𝕜 : Type*} [Preorder 𝕜] [Zero 𝕜] [One 𝕜]
    {U : Finset κ} {x : κ → 𝕜} {v : κ} :
    v ∈ floating U x ↔ v ∈ U ∧ 0 < x v ∧ x v < 1 := by
  classical
  simp [floating]

private theorem mem_activeSets_iff {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    {A : ι → Finset κ} {t : ℕ} {F : Finset κ} {i : ι} :
    i ∈ activeSets A t F ↔ t < #(A i ∩ F) := by
  simp [activeSets]

/-- Double counting shows strictly fewer active sets than floating variables when `F` is nonempty
and each element belongs to at most `t` sets. -/
private theorem card_activeSets_lt {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (A : ι → Finset κ) {t : ℕ} (hdeg : ∀ v : κ, #{i : ι | v ∈ A i} ≤ t)
    {F : Finset κ} (hF : F.Nonempty) :
    #(activeSets A t F) < #F := by
  classical
  set S := activeSets A t F
  have hcount : ∑ i ∈ S, #(A i ∩ F) = ∑ v ∈ F, #(S.filter fun i => v ∈ A i) := by
    have hcard (i : ι) : #(A i ∩ F) = ∑ v ∈ F, if v ∈ A i then 1 else 0 := by
      rw [inter_comm, ← filter_mem_eq_inter, card_filter]
    rw [sum_congr rfl fun i _ => hcard i, sum_comm]
    refine sum_congr rfl fun v _ => ?_
    rw [← card_filter]
  have hlow : #S * (t + 1) ≤ ∑ i ∈ S, #(A i ∩ F) := by
    calc #S * (t + 1) = ∑ _i ∈ S, (t + 1) := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ i ∈ S, #(A i ∩ F) :=
        sum_le_sum fun i hi => Nat.succ_le_of_lt (mem_activeSets_iff.1 hi)
  have hupp : ∑ v ∈ F, #(S.filter fun i => v ∈ A i) ≤ #F * t := by
    calc ∑ v ∈ F, #(S.filter fun i => v ∈ A i)
        ≤ ∑ v ∈ F, #{i : ι | v ∈ A i} :=
          sum_le_sum fun v _ => card_le_card (filter_subset_filter _ (subset_univ _))
      _ ≤ ∑ _v ∈ F, t := sum_le_sum fun v _ => hdeg v
      _ = #F * t := by rw [sum_const, smul_eq_mul]
  have hpos : 0 < #F := hF.card_pos
  nlinarith

/-- Since `#(activeSets A t F) < #F`, the homogeneous incidence system on `F` has a nonzero
solution supported on `F`. -/
private theorem exists_kernel_step {ι κ 𝕜 : Type*} [Fintype ι] [DecidableEq κ] [Field 𝕜]
    (A : ι → Finset κ) {t : ℕ} (hdeg : ∀ v : κ, #{i : ι | v ∈ A i} ≤ t)
    {F : Finset κ} (hF : F.Nonempty) :
    ∃ d : κ → 𝕜, d ≠ 0 ∧ (∀ v ∉ F, d v = 0) ∧
      ∀ i ∈ activeSets A t F, ∑ v ∈ A i, d v = 0 := by
  classical
  set S := activeSets A t F
  let L : (F → 𝕜) →ₗ[𝕜] (S → 𝕜) :=
    { toFun := fun y i => ∑ v : F, if (v : κ) ∈ A (i : ι) then y v else 0
      map_add' := fun y₁ y₂ => by
        ext i
        simp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun v _ => ?_
        split_ifs <;> ring
      map_smul' := fun c y => by
        ext i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        split_ifs <;> ring }
  have hlt : Module.finrank 𝕜 (S → 𝕜) < Module.finrank 𝕜 (F → 𝕜) := by
    rw [Module.finrank_pi, Module.finrank_pi, Fintype.card_coe, Fintype.card_coe]
    exact card_activeSets_lt A hdeg hF
  obtain ⟨y, hy_ker, hy_ne⟩ :=
    (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := L) hlt)
  let d : κ → 𝕜 := fun v => if hv : v ∈ F then y ⟨v, hv⟩ else 0
  refine ⟨d, ?_, ?_, ?_⟩
  · intro hd
    apply hy_ne
    ext ⟨v, hv⟩
    have := congrFun hd v
    simpa [d, hv] using this
  · intro v hv
    simp [d, hv]
  · intro i hi
    have hyi : L y ⟨i, hi⟩ = 0 := congrFun (LinearMap.mem_ker.1 hy_ker) ⟨i, hi⟩
    have hsum1 : ∑ v ∈ A i, d v = ∑ v ∈ F, if v ∈ A i then d v else 0 := by
      have hsub : ∑ v ∈ A i, d v = ∑ v ∈ A i ∩ F, d v :=
        (sum_subset inter_subset_left fun v _ hv => by
          have hvnf : v ∉ F := fun h => hv (mem_inter.2 ⟨‹v ∈ A i›, h⟩)
          simp [d, hvnf]).symm
      rw [hsub, inter_comm, ← filter_mem_eq_inter, sum_filter]
    have hsum2 : ∑ v ∈ F, (if v ∈ A i then d v else 0) = L y ⟨i, hi⟩ := by
      rw [← sum_coe_sort F]
      refine sum_congr rfl fun v _ => ?_
      simp [d, v.property]
    rw [hsum1, hsum2, hyi]

private theorem beckFiala_rounding_aux {ι κ 𝕜 : Type*} [Fintype ι] [DecidableEq κ]
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : ι → Finset κ) {t : ℕ} (ht : 0 < t) (hdeg : ∀ v : κ, #{i : ι | v ∈ A i} ≤ t)
    (x : κ → 𝕜) (hx0 : ∀ v, 0 ≤ x v) (hx1 : ∀ v, x v ≤ 1) :
    ∃ χ : κ → ℤ, (∀ v, χ v = 0 ∨ χ v = 1) ∧
      (∀ v, x v = 0 → χ v = 0) ∧ (∀ v, x v = 1 → χ v = 1) ∧
      ∀ i : ι, |∑ v ∈ A i, ((χ v : 𝕜) - x v)| < t := by
  classical
  let U : Finset κ := univ.biUnion A
  let F : Finset κ := floating U x
  have h01 (v : κ) (hvU : v ∈ U) (hvF : v ∉ F) : x v = 0 ∨ x v = 1 := by
    rcases (hx0 v).eq_or_lt with h | h
    · exact Or.inl h.symm
    · exact Or.inr ((hx1 v).antisymm (not_lt.1 fun hlt => hvF (mem_floating_iff.2 ⟨hvU, h, hlt⟩)))
  by_cases hF : F.Nonempty
  · obtain ⟨d, hd_ne, hd_supp, hd_active⟩ := exists_kernel_step (𝕜 := 𝕜) A hdeg hF
    let M : Finset κ := F.filter fun v => d v ≠ 0
    have hM : M.Nonempty := by
      obtain ⟨v, hv⟩ := Function.ne_iff.1 hd_ne
      exact ⟨v, mem_filter.2 ⟨by_contra fun h => hv (hd_supp v h), hv⟩⟩
    let ratio : κ → 𝕜 := fun v => if 0 < d v then (1 - x v) / d v else x v / (-d v)
    obtain ⟨v₀, hv₀M, hv₀_min⟩ := exists_min_image M ratio hM
    let lam : 𝕜 := ratio v₀
    have hratio_pos : ∀ v ∈ M, 0 < ratio v := by
      intro v hv
      obtain ⟨hvF, hdv⟩ := mem_filter.1 hv
      obtain ⟨_, hxpos, hxlt⟩ := mem_floating_iff.1 hvF
      dsimp only [ratio]
      split_ifs with hpos
      · exact div_pos (sub_pos.mpr hxlt) hpos
      · exact div_pos hxpos (neg_pos.mpr (lt_of_le_of_ne (not_lt.1 hpos) hdv))
    have hlam_pos : 0 < lam := hratio_pos v₀ hv₀M
    have hdM (v : κ) (hv : v ∉ M) : d v = 0 :=
      by_contra fun h => hv (mem_filter.2 ⟨by_contra fun hF' => h (hd_supp v hF'), h⟩)
    let x' : κ → 𝕜 := fun v => x v + lam * d v
    have hx'0 : ∀ v, 0 ≤ x' v := by
      intro v
      dsimp only [x']
      by_cases hv : v ∈ M
      · obtain ⟨hvF, hdv⟩ := mem_filter.1 hv
        obtain ⟨_, hxpos, _⟩ := mem_floating_iff.1 hvF
        by_cases hpos : 0 < d v
        · positivity
        · have hneg : d v < 0 := lt_of_le_of_ne (not_lt.1 hpos) hdv
          have hratio : ratio v = x v / (-d v) := by simp [ratio, hpos]
          have hle : lam ≤ x v / (-d v) := (hv₀_min v hv).trans_eq hratio
          rw [le_div_iff₀ (neg_pos.mpr hneg)] at hle
          linarith
      · simp [hdM v hv, hx0 v]
    have hx'1 : ∀ v, x' v ≤ 1 := by
      intro v
      dsimp only [x']
      by_cases hv : v ∈ M
      · obtain ⟨hvF, hdv⟩ := mem_filter.1 hv
        obtain ⟨_, _, hxlt⟩ := mem_floating_iff.1 hvF
        by_cases hpos : 0 < d v
        · have hratio : ratio v = (1 - x v) / d v := by simp [ratio, hpos]
          have hle : lam ≤ (1 - x v) / d v := (hv₀_min v hv).trans_eq hratio
          rw [le_div_iff₀ hpos] at hle
          linarith
        · have hneg : d v < 0 := lt_of_le_of_ne (not_lt.1 hpos) hdv
          linarith [mul_nonpos_of_nonneg_of_nonpos hlam_pos.le hneg.le, hx1 v]
      · simp [hdM v hv, hx1 v]
    have hv₀_bnd : x' v₀ = 0 ∨ x' v₀ = 1 := by
      obtain ⟨_, hdv₀⟩ := mem_filter.1 hv₀M
      dsimp only [x', lam, ratio]
      split_ifs with hpos
      · rw [div_mul_cancel₀ _ hdv₀]; right; ring
      · have hnd : -d v₀ ≠ 0 := neg_ne_zero.mpr hdv₀
        have : (x v₀ / (-d v₀)) * d v₀ = -x v₀ := by field_simp [hdv₀]
        left; linarith
    have hF_sub : floating U x' ⊆ F := by
      intro v hv'
      by_contra hv
      have hdv : d v = 0 := hd_supp v hv
      have hxv : x' v = x v := by simp [x', hdv]
      exact hv (mem_floating_iff.2 (hxv ▸ mem_floating_iff.1 hv'))
    have hcard_lt : #(floating U x') < #F := by
      refine card_lt_card ⟨hF_sub, fun hsub => ?_⟩
      have hv₀F : v₀ ∈ F := (mem_filter.1 hv₀M).1
      have hv₀_not : v₀ ∉ floating U x' := by
        intro hmem
        obtain ⟨_, h0, h1⟩ := mem_floating_iff.1 hmem
        rcases hv₀_bnd with h | h <;> linarith
      exact hv₀_not (hsub hv₀F)
    obtain ⟨χ, hχ01, hχ0, hχ1, hχ_sum⟩ :=
      beckFiala_rounding_aux A ht hdeg x' hx'0 hx'1
    refine ⟨χ, hχ01, ?_, ?_, ?_⟩
    · intro v hv0
      have hvF : v ∉ F := by simp [F, mem_floating_iff, hv0]
      exact hχ0 v (by simp [x', hd_supp v hvF, hv0])
    · intro v hv1
      have hvF : v ∉ F := by simp [F, mem_floating_iff, hv1]
      exact hχ1 v (by simp [x', hd_supp v hvF, hv1])
    · intro i
      by_cases hi : i ∈ activeSets A t F
      · have hx'_eq : ∑ v ∈ A i, x' v = ∑ v ∈ A i, x v := by
          simp only [x', sum_add_distrib, ← mul_sum, hd_active i hi, mul_zero, add_zero]
        simpa only [sum_sub_distrib, hx'_eq] using hχ_sum i
      · have hle_t : #(A i ∩ F) ≤ t := Nat.le_of_not_lt (mt mem_activeSets_iff.2 hi)
        have hzero : ∀ v ∈ A i, v ∉ F → (χ v : 𝕜) - x v = 0 := by
          intro v hvAi hvF
          rcases h01 v (mem_biUnion.2 ⟨i, mem_univ i, hvAi⟩) hvF with hv0 | hv1
          · have := hχ0 v (by simp [x', hd_supp v hvF, hv0])
            simp [this, hv0]
          · have := hχ1 v (by simp [x', hd_supp v hvF, hv1])
            simp [this, hv1]
        have hsplit : ∑ v ∈ A i, ((χ v : 𝕜) - x v) = ∑ v ∈ A i ∩ F, ((χ v : 𝕜) - x v) :=
          (sum_subset inter_subset_left fun v hv hvn =>
            hzero v hv fun hvF => hvn (mem_inter.2 ⟨hv, hvF⟩)).symm
        rw [hsplit]
        rcases (A i ∩ F).eq_empty_or_nonempty with hempty | hne
        · rw [hempty, sum_empty, abs_zero]
          exact_mod_cast ht
        · have hterm : ∀ v ∈ A i ∩ F, |(χ v : 𝕜) - x v| < 1 := by
            intro v hv
            obtain ⟨_, hxpos, hxlt⟩ := mem_floating_iff.1 (mem_inter.1 hv).2
            rcases hχ01 v with h | h <;> simp only [h, Int.cast_zero, Int.cast_one, abs_lt] <;>
              constructor <;> linarith
          calc |∑ v ∈ A i ∩ F, ((χ v : 𝕜) - x v)|
              ≤ ∑ v ∈ A i ∩ F, |(χ v : 𝕜) - x v| := abs_sum_le_sum_abs _ _
            _ < ∑ _v ∈ A i ∩ F, (1 : 𝕜) := sum_lt_sum_of_nonempty hne hterm
            _ = #(A i ∩ F) := by simp
            _ ≤ t := by exact_mod_cast hle_t
  · rw [not_nonempty_iff_eq_empty] at hF
    refine ⟨fun v => if x v = 1 then 1 else 0, ?_, ?_, ?_, ?_⟩
    · intro v; dsimp only; split_ifs <;> simp
    · intro v hv; simp [hv]
    · intro v hv; simp [hv]
    · intro i
      have hzero : ∑ v ∈ A i, ((↑(if x v = 1 then (1 : ℤ) else 0) : 𝕜) - x v) = 0 := by
        refine sum_eq_zero fun v hvAi => ?_
        rcases h01 v (mem_biUnion.2 ⟨i, mem_univ i, hvAi⟩) (by simp [hF]) with hv | hv <;>
          simp [hv]
      rw [hzero, abs_zero]
      exact_mod_cast ht
termination_by (floating (univ.biUnion A) x).card
decreasing_by exact hcard_lt

end Helpers

/-- **Beck–Fiala integer-making (fractional rounding) theorem** ([AlonSpencer2016]; exact theorem
number and page locator not verified against a primary PDF). Given a finite set family
`A : ι → Finset κ` in which every element belongs to at most `t` sets (`0 < t`) and weights
`x : κ → 𝕜` in `[0, 1]` over a linearly ordered field `𝕜` (for example `ℝ` or `ℚ`), there exists
a `{0, 1}` rounding `χ : κ → ℤ` fixing all already-integral `0`/`1` coordinates such that every
set's sum changes by strictly less than `t`: `|∑ v ∈ A i, ((χ v : 𝕜) - x v)| < t`. -/
theorem beckFiala_rounding {ι κ 𝕜 : Type*} [Fintype ι] [DecidableEq κ]
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : ι → Finset κ) {t : ℕ} (ht : 0 < t) (hdeg : ∀ v : κ, #{i : ι | v ∈ A i} ≤ t)
    (x : κ → 𝕜) (hx0 : ∀ v, 0 ≤ x v) (hx1 : ∀ v, x v ≤ 1) :
    ∃ χ : κ → ℤ, (∀ v, χ v = 0 ∨ χ v = 1) ∧
      (∀ v, x v = 0 → χ v = 0) ∧ (∀ v, x v = 1 → χ v = 1) ∧
      ∀ i : ι, |∑ v ∈ A i, ((χ v : 𝕜) - x v)| < t :=
  beckFiala_rounding_aux A ht hdeg x hx0 hx1

/-- **Beck–Fiala discrepancy theorem** ([AlonSpencer2016]; exact theorem number and page locator
not verified against a primary PDF). Every finite set family `A : ι → Finset κ` in which each
element belongs to at most `t` sets admits a two-coloring `χ : κ → ℤ` with `χ v ∈ {-1, 1}` such
that `(∑ v ∈ A i, χ v).natAbs ≤ 2 * t - 1` for every `i : ι`. -/
theorem beckFiala {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (A : ι → Finset κ) {t : ℕ} (hdeg : ∀ v : κ, #{i : ι | v ∈ A i} ≤ t) :
    ∃ χ : κ → ℤ, (∀ v, χ v = 1 ∨ χ v = -1) ∧
      ∀ i : ι, (∑ v ∈ A i, χ v).natAbs ≤ 2 * t - 1 := by
  classical
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · refine ⟨fun _ => 1, fun _ => Or.inl rfl, fun i => ?_⟩
    have hempty : A i = ∅ := Finset.eq_empty_of_forall_notMem fun v hv => by
      have := hdeg v
      have hpos : 0 < #{j : ι | v ∈ A j} := Finset.card_pos.2 ⟨i, by simpa using hv⟩
      omega
    simp [hempty]
  · obtain ⟨χ₀, hχ01, -, -, hbound⟩ := beckFiala_rounding A ht hdeg
      (fun _ => (1 / 2 : ℚ)) (fun _ => by norm_num) (fun _ => by norm_num)
    refine ⟨fun v => 2 * χ₀ v - 1, fun v => ?_, fun i => ?_⟩
    · rcases hχ01 v with h | h <;> simp [h]
    · have hsum_q :
          ((∑ v ∈ A i, (2 * χ₀ v - 1) : ℤ) : ℚ) =
            2 * ∑ v ∈ A i, ((χ₀ v : ℚ) - 1 / 2) := by
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => by ring
      have habs_q : |((∑ v ∈ A i, (2 * χ₀ v - 1) : ℤ) : ℚ)| < (2 * t : ℚ) := by
        rw [hsum_q, abs_mul, abs_of_pos (by norm_num : (0 : ℚ) < 2)]
        have hi := hbound i
        linarith
      have habs_int : |(∑ v ∈ A i, (2 * χ₀ v - 1) : ℤ)| < 2 * (t : ℤ) := by
        exact_mod_cast habs_q
      obtain ⟨_, _⟩ := abs_lt.1 habs_int
      dsimp only
      omega

end Cslib.Combinatorics

end
