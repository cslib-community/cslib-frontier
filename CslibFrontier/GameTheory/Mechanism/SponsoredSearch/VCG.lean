/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.LinearValuation
public import CslibFrontier.GameTheory.Mechanism.SponsoredSearch.EnvyFree
public import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# VCG (Clarke-pivot) payment identification for sponsored search

On the finite outcome space `Ω = Fin k ↪ ι` of full assignments of `k` distinct bidders to `k`
slots (nonempty when `k ≤ Fintype.card ι`), each bidder `j`'s linear valuation of an assignment `ω`
with scalar value `v j` is `v j * slotAlloc μ ω j` (`Mechanism.linearProfile (slotAlloc μ) v`,
`CslibFrontier.GameTheory.Mechanism.LinearValuation`).

This module identifies the Clarke-pivot payments of the library's general VCG mechanism
`Cslib.GameTheory.Mechanism.vcg` (`CslibFrontier.GameTheory.Mechanism.VCG`) on this environment with
the minimal nonnegative locally envy-free slot prices `minEnvyFreePrice` from
`CslibFrontier.GameTheory.Mechanism.SponsoredSearch.EnvyFree` ([LahaiePennockSaberiVohra2007],
§28.3.1–28.3.2, pp. 703–706).

In particular, for a bidder in slot `i` (`i : Fin k`) under an assortative/optimal outcome `σ` and
nonnegative values `v`, the VCG payment is
`∑ r ≥ i, (μ r - μ (r + 1)) * v (σ (r + 1))` (with `μ k = 0` and the last term using
`maxUnassignedValue v σ`), and every unassigned bidder pays `0`. For the three-bidder two-slot
example (`v₁ > v₂ > v₃ ≥ 0`, `μ₁ > μ₂ > 0`), bidder 1's total VCG payment is
`(μ₁ - μ₂) * v₂ + μ₂ * v₃` (per-click charge `(1 - μ₂/μ₁) * v₂ + (μ₂/μ₁) * v₃`), contrasting with
the printed formula `(1 - μ₂/μ₁) * v₂` on p. 704 of [LahaiePennockSaberiVohra2007] which omits the
`+(μ₂/μ₁) * v₃` term when `v₃ > 0`.

## Main results

* `Cslib.GameTheory.SponsoredSearch.vcg_payment_slot_eq_minEnvyFreePrice`: for any outcome rule
  `f` choosing an assortative assignment `σ` on `linearProfile (slotAlloc μ) v`, bidder `σ i` pays
  `minEnvyFreePrice μ v σ i`.
* `Cslib.GameTheory.SponsoredSearch.vcg_payment_unassigned_eq_zero`: every unassigned bidder pays
  `0`.

## References

* [S. Lahaie, D. M. Pennock, A. Saberi, and R. V. Vohra, *Sponsored Search Auctions*, Ch. 28 in
  *Algorithmic Game Theory*][LahaiePennockSaberiVohra2007]
-/

public section

namespace Cslib.GameTheory.SponsoredSearch

open Cslib.GameTheory.Mechanism

variable {k : ℕ} {ι : Type*}

private theorem sum_erase_linearProfile [Fintype ι] [DecidableEq ι] (μ : Fin k → ℝ) (v : ι → ℝ)
    (x : ι) (ω : Fin k ↪ ι) :
    ∑ j ∈ Finset.univ.erase x, linearProfile (slotAlloc μ) v j ω =
      welfare μ (Function.update v x 0) ω := by
  have heq : ∑ j : ι, slotAlloc μ ω j * Function.update v x 0 j =
      ∑ j ∈ Finset.univ.erase x, linearProfile (slotAlloc μ) v j ω := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), Function.update_self, mul_zero, zero_add]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hne : j ≠ x := Finset.ne_of_mem_erase hj
    simp only [Function.update_of_ne hne, linearProfile_apply, linearValuation_apply, mul_comm]
  rw [← heq, sum_slotAlloc_mul]

/-- The assignment obtained from `σ` by dropping slot `t`, shifting slots `t + 1, …, k - 1` up by
one position, and placing `tail` into the last slot `k - 1`. -/
private def shiftUp (σ : Fin k ↪ ι) (t : Fin k) (tail : ι)
    (htail : ∀ r : Fin k, r ≠ t → tail ≠ σ r) : Fin k ↪ ι where
  toFun r :=
    if h : r.val < t.val then σ r
    else if h2 : r.val + 1 < k then σ ⟨r.val + 1, h2⟩
    else tail
  inj' a b hab := by
    have ha_case : ∀ r : Fin k,
        (r.val < t.val ∧ (if h : r.val < t.val then σ r
          else if h2 : r.val + 1 < k then σ ⟨r.val + 1, h2⟩ else tail) = σ r) ∨
        (t.val ≤ r.val ∧ ∃ h2 : r.val + 1 < k, (if h : r.val < t.val then σ r
          else if h2 : r.val + 1 < k then σ ⟨r.val + 1, h2⟩ else tail) = σ ⟨r.val + 1, h2⟩) ∨
        (t.val ≤ r.val ∧ r.val + 1 = k ∧ (if h : r.val < t.val then σ r
          else if h2 : r.val + 1 < k then σ ⟨r.val + 1, h2⟩ else tail) = tail) := by
      intro r
      by_cases h1 : r.val < t.val
      · left; exact ⟨h1, by simp only [h1, ↓reduceDIte]⟩
      · by_cases h2 : r.val + 1 < k
        · right; left; exact ⟨by omega, h2, by simp only [h1, h2, ↓reduceDIte]⟩
        · right; right; exact ⟨by omega, by omega, by simp only [h1, h2, ↓reduceDIte]⟩
    dsimp only at hab
    rcases ha_case a with ⟨ha1, ha⟩ | ⟨ha1, ha2, ha⟩ | ⟨ha1, ha2, ha⟩ <;>
      rcases ha_case b with ⟨hb1, hb⟩ | ⟨hb1, hb2, hb⟩ | ⟨hb1, hb2, hb⟩
    · exact σ.injective (ha.symm.trans (hab.trans hb))
    · have := congrArg Fin.val (σ.injective (ha.symm.trans (hab.trans hb)))
      exact absurd this (by dsimp; omega)
    · exact absurd (ha.symm.trans (hab.trans hb)).symm
        (htail a (Fin.ne_of_val_ne (by omega)))
    · have := congrArg Fin.val (σ.injective (ha.symm.trans (hab.trans hb)))
      exact absurd this (by dsimp; omega)
    · have h := congrArg Fin.val (σ.injective (ha.symm.trans (hab.trans hb)))
      apply Fin.ext; dsimp at h; omega
    · exact absurd (ha.symm.trans (hab.trans hb)).symm
        (htail ⟨a.val + 1, ha2⟩ (Fin.ne_of_val_ne (by dsimp; omega)))
    · exact absurd (ha.symm.trans (hab.trans hb))
        (htail b (Fin.ne_of_val_ne (by omega)))
    · exact absurd (ha.symm.trans (hab.trans hb))
        (htail ⟨b.val + 1, hb2⟩ (Fin.ne_of_val_ne (by dsimp; omega)))
    · apply Fin.ext; omega

private theorem shiftUp_lt (σ : Fin k ↪ ι) (t : Fin k) (tail : ι)
    (htail : ∀ r : Fin k, r ≠ t → tail ≠ σ r) {r : Fin k} (hr : r.val < t.val) :
    shiftUp σ t tail htail r = σ r := by
  change (if h : r.val < t.val then σ r
    else if h2 : r.val + 1 < k then σ ⟨r.val + 1, h2⟩ else tail) = σ r
  simp only [hr, ↓reduceDIte]

private theorem shiftUp_mid (σ : Fin k ↪ ι) (t : Fin k) (tail : ι)
    (htail : ∀ r : Fin k, r ≠ t → tail ≠ σ r) {r : Fin k} (hge : t.val ≤ r.val)
    (h2 : r.val + 1 < k) :
    shiftUp σ t tail htail r = σ ⟨r.val + 1, h2⟩ := by
  change (if h : r.val < t.val then σ r
    else if h2 : r.val + 1 < k then σ ⟨r.val + 1, h2⟩ else tail) = σ ⟨r.val + 1, h2⟩
  have hnot : ¬(r.val < t.val) := by omega
  simp only [hnot, h2, ↓reduceDIte]

private theorem shiftUp_last (σ : Fin k ↪ ι) (t : Fin k) (tail : ι)
    (htail : ∀ r : Fin k, r ≠ t → tail ≠ σ r) {r : Fin k} (hlast : r.val + 1 = k) :
    shiftUp σ t tail htail r = tail := by
  change (if h : r.val < t.val then σ r
    else if h2 : r.val + 1 < k then σ ⟨r.val + 1, h2⟩ else tail) = tail
  have h1 : ¬(r.val < t.val) := by omega
  have h2 : ¬(r.val + 1 < k) := by omega
  simp only [h1, h2, ↓reduceDIte]

private theorem shiftUp_value [DecidableEq ι] (v : ι → ℝ) (σ : Fin k ↪ ι) (t : Fin k) (tail : ι)
    (htail : ∀ r : Fin k, r ≠ t → tail ≠ σ r) (r : Fin k) :
    Function.update v (σ t) 0 (shiftUp σ t tail htail r) =
      if r.val < t.val then v (σ r)
      else if h : r.val + 1 < k then v (σ ⟨r.val + 1, h⟩)
      else Function.update v (σ t) 0 tail := by
  by_cases h1 : r.val < t.val
  · rw [shiftUp_lt σ t tail htail h1]
    simp only [h1, ↓reduceIte]
    exact Function.update_of_ne (σ.injective.ne (Fin.ne_of_val_ne (by omega))) 0 v
  · by_cases h2 : r.val + 1 < k
    · rw [shiftUp_mid σ t tail htail (by omega) h2]
      simp only [h1, h2, ↓reduceIte, ↓reduceDIte]
      exact Function.update_of_ne (σ.injective.ne (Fin.ne_of_val_ne (by dsimp; omega))) 0 v
    · rw [shiftUp_last σ t tail htail (by omega)]
      simp only [h1, h2, ↓reduceIte, ↓reduceDIte]

private theorem clarkePivot_unassigned [Fintype ι] [DecidableEq ι]
    [Fintype (Fin k ↪ ι)] [Nonempty (Fin k ↪ ι)]
    {μ : Fin k → ℝ} {v : ι → ℝ} {σ : Fin k ↪ ι}
    (hσ : IsAssortative v σ) (hμ : Antitone μ) (hμ_nonneg : ∀ i, 0 ≤ μ i)
    (hv : ∀ j, 0 ≤ v j) {x : ι} (hx : x ∉ Set.range σ) :
    clarkePivot x (linearProfile (slotAlloc μ) v) =
      ∑ j ∈ Finset.univ.erase x, linearProfile (slotAlloc μ) v j σ := by
  let v' := Function.update v x 0
  have hσ' : IsAssortative v' σ := by
    refine ⟨fun a b hab => ?_, fun i j hj => ?_⟩
    · have ha : σ a ≠ x := fun h => hx ⟨a, h⟩
      have hb : σ b ≠ x := fun h => hx ⟨b, h⟩
      simp only [Function.comp_apply, v', Function.update_of_ne ha, Function.update_of_ne hb]
      exact hσ.antitone hab
    · have hi : σ i ≠ x := fun h => hx ⟨i, h⟩
      rw [show v' (σ i) = v (σ i) from Function.update_of_ne hi 0 v]
      by_cases hjx : j = x
      · subst hjx; rw [show v' j = 0 from Function.update_self j 0 v]; exact hv _
      · rw [show v' j = v j from Function.update_of_ne hjx 0 v]; exact hσ.unassigned_le i j hj
  have hopt : IsOptimal μ v' σ := hσ'.isOptimal hμ hμ_nonneg
  refine le_antisymm (Finset.sup'_le _ _ fun ω _ => ?_)
    (Finset.le_sup' (fun ω => ∑ j ∈ Finset.univ.erase x, linearProfile (slotAlloc μ) v j ω)
      (Finset.mem_univ σ))
  rw [sum_erase_linearProfile, sum_erase_linearProfile]
  exact hopt ω

private theorem welfare_shiftUp_sub [Fintype ι] [DecidableEq ι]
    (μ : Fin k → ℝ) (v : ι → ℝ) (σ : Fin k ↪ ι) (t : Fin k)
    (tail : ι) (htail : ∀ r : Fin k, r ≠ t → tail ≠ σ r)
    (hval : Function.update v (σ t) 0 tail = maxUnassignedValue v σ) :
    welfare μ (Function.update v (σ t) 0) (shiftUp σ t tail htail) -
      ∑ j ∈ Finset.univ.erase (σ t), linearProfile (slotAlloc μ) v j σ =
      minEnvyFreePrice μ v σ t := by
  let v' := Function.update v (σ t) 0
  rw [sum_erase_linearProfile μ v (σ t) σ]
  have hold_eq : welfare μ v' σ = ∑ r : Fin k, if r = t then 0 else μ r * v (σ r) := by
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hr : r = t
    · subst hr; simp only [v', Function.update_self, mul_zero, ↓reduceIte]
    · simp only [hr, ↓reduceIte, v', Function.update_of_ne (σ.injective.ne hr)]
  have hsplit : (Finset.univ : Finset (Fin k)) = Finset.Iio t ∪ Finset.Ici t := by
    ext r; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_Iio, Finset.mem_Ici, true_iff]
    exact lt_or_ge r t
  have hdisj : Disjoint (Finset.Iio t) (Finset.Ici t) :=
    Finset.disjoint_left.mpr fun r hr1 hr2 =>
      not_le_of_gt (Finset.mem_Iio.mp hr1) (Finset.mem_Ici.mp hr2)
  have hbelow_eq : ∑ r : Fin k, (if r = t then (0 : ℝ) else μ r * v (σ r)) =
      ∑ r : Fin k,
        (if r.val < t.val then μ r * v (σ r)
         else if h : r.val + 1 < k then μ ⟨r.val + 1, h⟩ * v (σ ⟨r.val + 1, h⟩) else 0) := by
    rw [hsplit, Finset.sum_union hdisj, Finset.sum_union hdisj]
    congr 1
    · refine Finset.sum_congr rfl fun r hr => ?_
      have hlt : r < t := Finset.mem_Iio.mp hr
      have hne : r ≠ t := ne_of_lt hlt
      have hltv : r.val < t.val := hlt
      simp only [hne, hltv, ↓reduceIte]
    · have hIci_split : Finset.Ici t = insert t (Finset.Ioi t) := by
        ext r; simp only [Finset.mem_Ici, Finset.mem_insert, Finset.mem_Ioi, Fin.le_def,
          Fin.lt_def, Fin.ext_iff]; omega
      have hnot_mem : t ∉ Finset.Ioi t := by
        simp only [Finset.mem_Ioi, lt_self_iff_false, not_false_eq_true]
      rw [hIci_split, Finset.sum_insert hnot_mem]
      simp only [↓reduceIte, zero_add]
      have hL : ∑ r ∈ Finset.Ioi t, (if r = t then (0 : ℝ) else μ r * v (σ r)) =
          ∑ r ∈ Finset.Ioi t, μ r * v (σ r) :=
        Finset.sum_congr rfl fun r hr => by
          have hne : r ≠ t := ne_of_gt (Finset.mem_Ioi.mp hr)
          simp only [hne, ↓reduceIte]
      rw [hL, ← hIci_split]
      have hk : 0 < k := Fin.pos t
      have hlast_mem : (⟨k - 1, by omega⟩ : Fin k) ∈ Finset.Ici t := by
        simp only [Finset.mem_Ici, Fin.le_def]; omega
      rw [← Finset.add_sum_erase _ _ hlast_mem]
      have hnot_lt_last : ¬(k - 1 < t.val) := by omega
      have hnot_succ_last : ¬(k - 1 + 1 < k) := by omega
      simp only [hnot_lt_last, hnot_succ_last, ↓reduceDIte, ↓reduceIte, zero_add]
      refine (Finset.sum_bij (fun r (hr : r ∈ (Finset.Ici t).erase ⟨k - 1, by omega⟩) =>
        (⟨r.val + 1, by
          have hne := Finset.ne_of_mem_erase hr
          have hvalne : r.val ≠ k - 1 := fun h => hne (by apply Fin.ext; dsimp; exact h)
          omega⟩ : Fin k)) ?_ ?_ ?_ ?_).symm
      · intro r hr
        have hmem : t ≤ r := Finset.mem_Ici.mp (Finset.mem_of_mem_erase hr)
        simp only [Finset.mem_Ioi, Fin.lt_def]
        exact Nat.lt_succ_of_le hmem
      · intro a _ b _ hab
        have h := congrArg Fin.val hab
        apply Fin.ext; dsimp at h; omega
      · intro b hb
        have hbt : t < b := Finset.mem_Ioi.mp hb
        refine ⟨⟨b.val - 1, by omega⟩, Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by dsimp; omega),
          Finset.mem_Ici.mpr (by change t.val ≤ b.val - 1; exact Nat.le_sub_one_of_lt hbt)⟩,
          by apply Fin.ext; dsimp; omega⟩
      · intro r hr
        have hmem : t ≤ r := Finset.mem_Ici.mp (Finset.mem_of_mem_erase hr)
        have hne : r.val ≠ k - 1 :=
          fun h => Finset.ne_of_mem_erase hr (by apply Fin.ext; dsimp; exact h)
        have hnotlt : ¬(r.val < t.val) := Nat.not_lt.mpr hmem
        have hsucc : r.val + 1 < k := by omega
        simp only [hnotlt, hsucc, ↓reduceIte, ↓reduceDIte]
  rw [welfare, hold_eq, hbelow_eq, ← Finset.sum_sub_distrib, hsplit, Finset.sum_union hdisj]
  have hlt_zero : ∑ r ∈ Finset.Iio t,
      (μ r * v' (shiftUp σ t tail htail r) -
        (if r.val < t.val then μ r * v (σ r)
         else if h : r.val + 1 < k then μ ⟨r.val + 1, h⟩ * v (σ ⟨r.val + 1, h⟩) else 0)) = 0 := by
    refine Finset.sum_eq_zero fun r hr => ?_
    have hlt : r < t := Finset.mem_Iio.mp hr
    have hltv : r.val < t.val := hlt
    dsimp only [v']
    rw [shiftUp_value v σ t tail htail r]
    simp only [hltv, ↓reduceIte, sub_self]
  rw [hlt_zero, zero_add, minEnvyFreePrice_eq_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hge : t ≤ r := Finset.mem_Ici.mp hr
  have hnotlt : ¬(r.val < t.val) := Nat.not_lt.mpr hge
  rw [shiftUp_value v σ t tail htail r]
  by_cases hsucc : r.val + 1 < k
  · simp only [nextSlotValue, hnotlt, hsucc, ↓reduceIte, ↓reduceDIte]
    ring
  · simp only [nextSlotValue, hnotlt, hsucc, ↓reduceIte, ↓reduceDIte, hval]
    ring

private theorem shiftUp_isAssortative [DecidableEq ι] {v : ι → ℝ} {σ : Fin k ↪ ι}
    (hσ : IsAssortative v σ) (t : Fin k) (tail : ι)
    (htail : ∀ r : Fin k, r ≠ t → tail ≠ σ r)
    (htail_le : ∀ r : Fin k, Function.update v (σ t) 0 tail ≤ v (σ r))
    (hunassigned : ∀ j : ι, j ∉ Set.range (shiftUp σ t tail htail) →
      Function.update v (σ t) 0 j ≤ Function.update v (σ t) 0 tail) :
    IsAssortative (Function.update v (σ t) 0) (shiftUp σ t tail htail) := by
  refine ⟨fun a b hab => ?_, fun i j hj => ?_⟩
  · change Function.update v (σ t) 0 (shiftUp σ t tail htail b) ≤
      Function.update v (σ t) 0 (shiftUp σ t tail htail a)
    rw [shiftUp_value v σ t tail htail a, shiftUp_value v σ t tail htail b]
    by_cases ha1 : a.val < t.val
    · simp only [ha1, ↓reduceIte]
      by_cases hb1 : b.val < t.val
      · simp only [hb1, ↓reduceIte]; exact hσ.antitone hab
      · by_cases hb2 : b.val + 1 < k
        · simp only [hb1, hb2, ↓reduceIte, ↓reduceDIte]
          exact hσ.antitone (show a ≤ ⟨b.val + 1, hb2⟩ by change a.val ≤ b.val + 1; omega)
        · simp only [hb1, hb2, ↓reduceIte, ↓reduceDIte]; exact htail_le a
    · by_cases ha2 : a.val + 1 < k
      · have hb1 : ¬(b.val < t.val) := by have : a.val ≤ b.val := hab; omega
        simp only [ha1, ha2, hb1, ↓reduceIte, ↓reduceDIte]
        by_cases hb2 : b.val + 1 < k
        · simp only [hb2, ↓reduceDIte]
          exact hσ.antitone (show (⟨a.val + 1, ha2⟩ : Fin k) ≤ ⟨b.val + 1, hb2⟩ by
            change a.val + 1 ≤ b.val + 1; exact Nat.succ_le_succ hab)
        · simp only [hb2, ↓reduceDIte]; exact htail_le ⟨a.val + 1, ha2⟩
      · have hb1 : ¬(b.val < t.val) := by have : a.val ≤ b.val := hab; omega
        have hb2 : ¬(b.val + 1 < k) := by have : a.val ≤ b.val := hab; omega
        simp only [ha1, ha2, hb1, hb2, ↓reduceIte, ↓reduceDIte, le_rfl]
  · have hle := hunassigned j hj
    rw [shiftUp_value v σ t tail htail i]
    by_cases hi1 : i.val < t.val
    · simp only [hi1, ↓reduceIte]; exact hle.trans (htail_le i)
    · by_cases hi2 : i.val + 1 < k
      · simp only [hi1, hi2, ↓reduceIte, ↓reduceDIte]; exact hle.trans (htail_le ⟨i.val + 1, hi2⟩)
      · simp only [hi1, hi2, ↓reduceIte, ↓reduceDIte]; exact hle

private theorem mem_range_shiftUp_of_ne {σ : Fin k ↪ ι} {t : Fin k} {tail : ι}
    {htail : ∀ r : Fin k, r ≠ t → tail ≠ σ r} {r : Fin k} (hrt : r ≠ t) :
    σ r ∈ Set.range (shiftUp σ t tail htail) := by
  rcases lt_or_gt_of_ne hrt with hlt | hgt
  · exact ⟨r, shiftUp_lt σ t tail htail hlt⟩
  · have h1 : t.val ≤ r.val - 1 := by have : t.val < r.val := hgt; omega
    have h2 : r.val - 1 + 1 < k := by omega
    refine ⟨⟨r.val - 1, by omega⟩, ?_⟩
    rw [shiftUp_mid σ t tail htail h1 h2]
    congr 1; apply Fin.ext; dsimp; omega

/-- **VCG payment equals `minEnvyFreePrice`** ([LahaiePennockSaberiVohra2007], §28.3.1–28.3.2,
pp. 703–706): on the outcome space `Ω = Fin k ↪ ι` with linear valuations
`v j * slotAlloc μ ω j`, for any outcome rule `f` returning an assortative assignment `σ` on
nonnegative values `v` with weakly decreasing nonnegative CTRs `μ`, bidder `σ t`'s Clarke-pivot
VCG payment equals `minEnvyFreePrice μ v σ t`. -/
theorem vcg_payment_slot_eq_minEnvyFreePrice [Fintype ι] [DecidableEq ι]
    [Fintype (Fin k ↪ ι)] [Nonempty (Fin k ↪ ι)]
    (f : (ι → (Fin k ↪ ι) → ℝ) → Fin k ↪ ι) {μ : Fin k → ℝ} {v : ι → ℝ} {σ : Fin k ↪ ι}
    (hfσ : f (linearProfile (slotAlloc μ) v) = σ) (hσ : IsAssortative v σ)
    (hμ : Antitone μ) (hμ_nonneg : ∀ i, 0 ≤ μ i) (hv : ∀ j, 0 ≤ v j) (t : Fin k) :
    (vcg f).payment (linearProfile (slotAlloc μ) v) (σ t) = minEnvyFreePrice μ v σ t := by
  simp only [vcg, groves, hfσ]
  have hsolve : ∀ (tail : ι) (htail : ∀ r : Fin k, r ≠ t → tail ≠ σ r),
      Function.update v (σ t) 0 tail = maxUnassignedValue v σ →
      IsAssortative (Function.update v (σ t) 0) (shiftUp σ t tail htail) →
      clarkePivot (σ t) (linearProfile (slotAlloc μ) v) -
        ∑ j ∈ Finset.univ.erase (σ t), linearProfile (slotAlloc μ) v j σ =
        minEnvyFreePrice μ v σ t := by
    intro tail htail hval hassort
    have hpivot : clarkePivot (σ t) (linearProfile (slotAlloc μ) v) =
        welfare μ (Function.update v (σ t) 0) (shiftUp σ t tail htail) := by
      refine le_antisymm (Finset.sup'_le _ _ fun ω _ => ?_) ?_
      · rw [sum_erase_linearProfile]; exact hassort.isOptimal hμ hμ_nonneg ω
      · rw [← sum_erase_linearProfile μ v (σ t) (shiftUp σ t tail htail)]
        exact Finset.le_sup' (fun ω => ∑ j ∈ Finset.univ.erase (σ t),
          linearProfile (slotAlloc μ) v j ω) (Finset.mem_univ _)
    rw [hpivot]
    exact welfare_shiftUp_sub μ v σ t tail htail hval
  by_cases hne : (Finset.univ \ Finset.univ.map σ).Nonempty
  · obtain ⟨jstar, hjmem, hjval⟩ := Finset.exists_mem_eq_sup' hne v
    have hjrange : jstar ∉ Set.range σ := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_map, true_and, not_exists] at hjmem
      rintro ⟨r, rfl⟩; exact hjmem r rfl
    have htail : ∀ r : Fin k, r ≠ t → jstar ≠ σ r := fun r _ h => hjrange ⟨r, h.symm⟩
    have hjt : jstar ≠ σ t := fun h => hjrange ⟨t, h.symm⟩
    have hval : Function.update v (σ t) 0 jstar = maxUnassignedValue v σ := by
      rw [Function.update_of_ne hjt]
      simp only [maxUnassignedValue, hne, ↓reduceDIte, hjval]
    refine hsolve jstar htail hval (shiftUp_isAssortative hσ t jstar htail ?_ ?_)
    · intro r; rw [Function.update_of_ne hjt]; exact hσ.unassigned_le r jstar hjrange
    · intro j hj
      rw [hval]
      by_cases hje : j = σ t
      · subst hje; rw [Function.update_self]; exact maxUnassignedValue_nonneg hv σ
      · rw [Function.update_of_ne hje]
        refine le_maxUnassignedValue v σ ?_
        rintro ⟨r, rfl⟩
        exact hj (mem_range_shiftUp_of_ne (fun h => hje (by rw [h])))
  · have htail : ∀ r : Fin k, r ≠ t → σ t ≠ σ r := fun r hr h => hr (σ.injective h).symm
    have hval : Function.update v (σ t) 0 (σ t) = maxUnassignedValue v σ := by
      rw [Function.update_self]
      simp only [maxUnassignedValue, hne, ↓reduceDIte]
    refine hsolve (σ t) htail hval (shiftUp_isAssortative hσ t (σ t) htail ?_ ?_)
    · intro r; rw [Function.update_self]; exact hv (σ r)
    · intro j hj
      exfalso
      have hsurj : j ∈ Set.range σ := by
        by_contra hnot
        apply hne
        refine ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, ?_⟩⟩
        simp only [Finset.mem_map, Finset.mem_univ, true_and, not_exists]
        exact fun r hr => hnot ⟨r, hr⟩
      obtain ⟨r, rfl⟩ := hsurj
      by_cases hrt : r = t
      · subst hrt
        have hk : 0 < k := Fin.pos r
        exact hj ⟨⟨k - 1, by omega⟩, shiftUp_last σ r (σ r) htail (by dsimp; omega)⟩
      · exact hj (mem_range_shiftUp_of_ne hrt)

/-- Every unassigned bidder pays `0` under the VCG mechanism on `Fin k ↪ ι`. -/
theorem vcg_payment_unassigned_eq_zero [Fintype ι] [DecidableEq ι]
    [Fintype (Fin k ↪ ι)] [Nonempty (Fin k ↪ ι)]
    (f : (ι → (Fin k ↪ ι) → ℝ) → Fin k ↪ ι) {μ : Fin k → ℝ} {v : ι → ℝ} {σ : Fin k ↪ ι}
    (hfσ : f (linearProfile (slotAlloc μ) v) = σ) (hσ : IsAssortative v σ)
    (hμ : Antitone μ) (hμ_nonneg : ∀ i, 0 ≤ μ i) (hv : ∀ j, 0 ≤ v j)
    {x : ι} (hx : x ∉ Set.range σ) :
    (vcg f).payment (linearProfile (slotAlloc μ) v) x = 0 := by
  simp only [vcg, groves, hfσ]
  rw [clarkePivot_unassigned hσ hμ hμ_nonneg hv hx, sub_self]

end Cslib.GameTheory.SponsoredSearch
