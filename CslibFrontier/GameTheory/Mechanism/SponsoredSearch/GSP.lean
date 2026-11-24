/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.SponsoredSearch.EnvyFree
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Generalized second price (GSP) sponsored search auction

The unit-weight generalized second price (GSP) auction ("rank by bid", Overture mechanism) in the
static full-information model with bidder-independent click-through rates `μ : Fin k → ℝ`
([LahaiePennockSaberiVohra2007], Chapter 28, §§28.2–28.3, pp. 701–707).

Rather than choosing a fixed tie-breaking bid-ranking function, the auction is formulated via the
outcome relation `IsAssortative b σ` (`EnvyFree`): an assignment `σ : Fin k ↪ ι` is a valid
unit-weight GSP outcome of a bid profile `b : ι → ℝ` whenever bids are non-increasing along the
slots and every unassigned bidder bids at most every assigned bidder's bid (ties may be broken
arbitrarily). The per-click price charged to slot `i` is `gspPerClickPrice b σ i`: the bid of the
bidder in slot `i + 1`, or the highest unassigned bid (`0` if all bidders are assigned) for the
last slot (`nextSlotValue b σ (maxUnassignedValue b σ) i`).

A bid profile and outcome `(b, σ)` form a **tie-robust full-information (Nash) equilibrium**
(`IsGSPEquilibrium`) if `b` is nonnegative, `σ` is a GSP outcome of `b`, and no bidder can raise its
utility by deviating to any nonnegative bid `z ≥ 0` under *any* consistent GSP outcome `σ'` of the
modified profile `Function.update b j z`.

The main theorem `exists_isGSPEquilibrium_locallyEnvyFree` formalizes **Theorem 28.2**
([LahaiePennockSaberiVohra2007], §28.3.2, pp. 706–707): under strictly decreasing positive CTRs
and nonnegative bidder values (`k ≤ Fintype.card ι`), the explicit bid profile `minEnvyFreeBid`
(slot `0` bids `v (σ 0)`, slot `i` (`i ≥ 1`) bids `minEnvyFreePrice μ v σ (i - 1) / μ (i - 1)`,
and every unassigned bidder bids its true value `v j`) supports a tie-robust Nash equilibrium whose
allocation is optimal and locally envy-free, and whose total slot payments equal `minEnvyFreePrice`
(the Vickrey prices identified in `CslibFrontier.GameTheory.Mechanism.SponsoredSearch.VCG`).

*Notes on the printed proof of Theorem 28.2*: in [LahaiePennockSaberiVohra2007], p. 706, the
displayed inequality `p*_{j-1}/μ_{j-1} ≥ p*_{j-1}/μ_j` has the wrong direction because
`μ_{j-1} > μ_j > 0`; monotonicity `p*_{j-1}/μ_{j-1} ≥ p*_j/μ_j` holds instead by multiplying the
local envy-freeness inequality (28.9) by `μ_j` and using individual rationality
`μ_j v_j - p*_j ≥ 0`. Also, the printed proof omits the explicit unilateral deviation check on
p. 707; we prove it in full (independently of tie-breaking) via a pigeonhole lower bound on
`gspPerClickPrice` after any deviation. No running-time claim is made.

## Main definitions

* `Cslib.GameTheory.SponsoredSearch.gspPerClickPrice`: per-click price charged to slot `i`.
* `Cslib.GameTheory.SponsoredSearch.gspSlotPrice`: total expected payment `μ i * gspPerClickPrice`.
* `Cslib.GameTheory.SponsoredSearch.gspUtility`: quasilinear utility of bidder `j`.
* `Cslib.GameTheory.SponsoredSearch.IsGSPEquilibrium`: tie-robust full-information Nash equilibrium.
* `Cslib.GameTheory.SponsoredSearch.minEnvyFreeBid`: equilibrium bid profile implementing
  `minEnvyFreePrice`.

## Main results

* `Cslib.GameTheory.SponsoredSearch.gspSlotPrice_minEnvyFreeBid`: the GSP slot payments under
  `minEnvyFreeBid` equal `minEnvyFreePrice`.
* `Cslib.GameTheory.SponsoredSearch.isGSPEquilibrium_minEnvyFreeBid`: for every assortative
  assignment `σ`, `(minEnvyFreeBid μ v σ, σ)` is a tie-robust GSP equilibrium.
* `Cslib.GameTheory.SponsoredSearch.exists_isGSPEquilibrium_locallyEnvyFree`: **Theorem 28.2**
  ([LahaiePennockSaberiVohra2007], §28.3.2, pp. 706–707).

## References

* [S. Lahaie, D. M. Pennock, A. Saberi, and R. V. Vohra, *Sponsored Search Auctions*, Ch. 28 in
  *Algorithmic Game Theory*][LahaiePennockSaberiVohra2007]
-/

public section

namespace Cslib.GameTheory.SponsoredSearch

variable {k : ℕ} {ι : Type*}

/-- Per-click price charged to slot `i : Fin k` under the unit-weight GSP auction with bids `b`
and assignment `σ`: the bid of the bidder in slot `i + 1`, or the highest unassigned bid
(`maxUnassignedValue b σ`, which is `0` when all bidders are assigned) for the last slot
([LahaiePennockSaberiVohra2007], §28.2, p. 702). -/
@[expose] noncomputable def gspPerClickPrice [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) (σ : Fin k ↪ ι) (i : Fin k) : ℝ :=
  nextSlotValue b σ (maxUnassignedValue b σ) i

/-- Total expected payment per impression for slot `i : Fin k` under GSP
(`μ i * gspPerClickPrice`). -/
@[expose] noncomputable def gspSlotPrice [Fintype ι] [DecidableEq ι]
    (μ : Fin k → ℝ) (b : ι → ℝ) (σ : Fin k ↪ ι) (i : Fin k) : ℝ :=
  μ i * gspPerClickPrice b σ i

/-- Quasilinear expected utility per impression of bidder `j` in the GSP auction with CTRs `μ`,
per-click values `v`, bids `b`, and assignment `σ`: `μ i * (v j - gspPerClickPrice b σ i)` if
`j` sits in slot `i`, and `0` if `j` is unassigned. -/
@[expose] noncomputable def gspUtility [Fintype ι] [DecidableEq ι]
    (μ : Fin k → ℝ) (v b : ι → ℝ) (σ : Fin k ↪ ι) (j : ι) : ℝ :=
  ∑ i : Fin k, if σ i = j then μ i * (v j - gspPerClickPrice b σ i) else 0

/-- Quasilinear utility of the assigned bidder `σ i` under GSP. -/
@[simp]
theorem gspUtility_apply_slot [Fintype ι] [DecidableEq ι]
    (μ : Fin k → ℝ) (v b : ι → ℝ) (σ : Fin k ↪ ι) (i : Fin k) :
    gspUtility μ v b σ (σ i) = μ i * (v (σ i) - gspPerClickPrice b σ i) := by
  simp only [gspUtility, σ.injective.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- An unassigned bidder receives utility `0` under GSP. -/
theorem gspUtility_of_not_mem_range [Fintype ι] [DecidableEq ι]
    (μ : Fin k → ℝ) (v b : ι → ℝ) (σ : Fin k ↪ ι) {j : ι} (hj : j ∉ Set.range σ) :
    gspUtility μ v b σ j = 0 :=
  Finset.sum_eq_zero fun i _ => by
    have hne : σ i ≠ j := fun h => hj ⟨i, h⟩
    simp only [hne, ↓reduceIte]

private theorem gspPerClickPrice_nonneg [Fintype ι] [DecidableEq ι]
    {b : ι → ℝ} (hb : ∀ j, 0 ≤ b j) (σ : Fin k ↪ ι) (i : Fin k) :
    0 ≤ gspPerClickPrice b σ i := by
  unfold gspPerClickPrice nextSlotValue
  split_ifs
  · exact hb _
  · exact maxUnassignedValue_nonneg hb σ

/-- Pigeonhole lower bound on the per-click price of slot `s` in any GSP outcome `σ'` of `b'`:
if `x` sits in slot `s` and there is a set `T` of at least `s + 1` *other* bidders each bidding
at least `c`, then the per-click price paid by slot `s` is at least `c` (any tie-breaking). -/
private theorem le_gspPerClickPrice_of_card_le [Fintype ι] [DecidableEq ι]
    {b' : ι → ℝ} {σ' : Fin k ↪ ι} (hσ' : IsAssortative b' σ') {s : Fin k} {x : ι}
    (hsx : σ' s = x) {T : Finset ι} (hxT : x ∉ T) (hcard : s.val + 1 ≤ T.card)
    {c : ℝ} (hbid : ∀ y ∈ T, c ≤ b' y) :
    c ≤ gspPerClickPrice b' σ' s := by
  let above : Finset (Fin k) := Finset.univ.filter (· < s)
  let U : Finset ι := above.map σ'
  have habove_card : above.card = s.val := by
    have heq : above = Finset.Iio s := by ext r; simp only [above, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_Iio]
    rw [heq, Fin.card_Iio]
  have hU_card : U.card < T.card := by
    rw [Finset.card_map, habove_card]
    omega
  obtain ⟨y, hyT, hyU⟩ : ∃ y ∈ T, y ∉ U := by
    by_contra hall
    have hsub : T ⊆ U := fun z hz => by
      by_contra hzu
      exact hall ⟨z, hz, hzu⟩
    exact absurd (Finset.card_le_card hsub) (not_le_of_gt hU_card)
  have hyx : y ≠ x := fun h => hxT (h ▸ hyT)
  have hcb : c ≤ b' y := hbid y hyT
  by_cases hyrange : y ∈ Set.range σ'
  · obtain ⟨r, rfl⟩ := hyrange
    have hr_not_lt : ¬r < s := by
      intro hlt
      apply hyU
      exact Finset.mem_map.mpr ⟨r, by
        simp only [above, Finset.mem_filter, Finset.mem_univ, true_and]; exact hlt, rfl⟩
    have hr_ne : r ≠ s := fun h => hyx (by rw [h, hsx])
    have hrs : s < r := lt_of_le_of_ne (not_lt.mp hr_not_lt) hr_ne.symm
    have hlt : s.val + 1 < k := lt_of_le_of_lt hrs r.isLt
    have hle : (⟨s.val + 1, hlt⟩ : Fin k) ≤ r := by change s.val + 1 ≤ r.val; exact hrs
    simp only [gspPerClickPrice, nextSlotValue, hlt, ↓reduceDIte]
    exact hcb.trans (hσ'.antitone hle)
  · unfold gspPerClickPrice nextSlotValue
    split_ifs with hlt
    · exact hcb.trans (hσ'.unassigned_le ⟨s.val + 1, hlt⟩ y hyrange)
    · exact hcb.trans (le_maxUnassignedValue b' σ' hyrange)

/-- A bid profile `b : ι → ℝ` and assignment `σ : Fin k ↪ ι` form a **tie-robust full-information
(Nash) equilibrium** of the unit-weight GSP auction ([LahaiePennockSaberiVohra2007], §28.3.2,
pp. 705–707) if bids are nonnegative, `σ` is a valid unit-weight GSP outcome of `b` (i.e.,
`IsAssortative b σ`: bids are non-increasing along the slots and unassigned bidders bid at most
every assigned bidder's bid, breaking ties arbitrarily), and no bidder can strictly improve its
utility by changing its bid to any `z ≥ 0` under *any* consistent GSP outcome `σ'`
(`IsAssortative (Function.update b j z) σ'`). -/
structure IsGSPEquilibrium [Fintype ι] [DecidableEq ι]
    (μ : Fin k → ℝ) (v b : ι → ℝ) (σ : Fin k ↪ ι) : Prop where
  /-- Every bid is nonnegative. -/
  nonneg : ∀ j, 0 ≤ b j
  /-- `σ` is a valid unit-weight GSP outcome of `b` (`IsAssortative b σ`). -/
  outcome : IsAssortative b σ
  /-- No unilateral deviation to a nonnegative bid `z` helps under any tie-breaking outcome `σ'`. -/
  noDeviation : ∀ (j : ι) (z : ℝ), 0 ≤ z → ∀ (σ' : Fin k ↪ ι),
    IsAssortative (Function.update b j z) σ' →
    gspUtility μ v (Function.update b j z) σ' j ≤ gspUtility μ v b σ j

/-- Explicit equilibrium bid profile implementing `minEnvyFreePrice μ v σ`
([LahaiePennockSaberiVohra2007], §28.3.2, proof of Theorem 28.2, p. 706):
* slot `0` bids its value `v (σ 0)`;
* slot `i` (`i ≥ 1`) bids `minEnvyFreePrice μ v σ (i - 1) / μ (i - 1)`;
* every unassigned bidder `j ∉ Set.range σ` bids its value `v j`. -/
@[expose] noncomputable def minEnvyFreeBid [Fintype ι] [DecidableEq ι]
    (μ : Fin k → ℝ) (v : ι → ℝ) (σ : Fin k ↪ ι) (j : ι) : ℝ :=
  if h : ∃ i : Fin k, σ i = j then
    let i := Classical.choose h
    if hi : 0 < i.val then
      minEnvyFreePrice μ v σ ⟨i.val - 1, by omega⟩ / μ ⟨i.val - 1, by omega⟩
    else v j
  else v j

/-- The top-slot bidder bids its true value `v (σ 0)` under `minEnvyFreeBid`. -/
theorem minEnvyFreeBid_slot_zero [Fintype ι] [DecidableEq ι] (μ : Fin k → ℝ) (v : ι → ℝ)
    (σ : Fin k ↪ ι) (hk : 0 < k) :
    minEnvyFreeBid μ v σ (σ ⟨0, hk⟩) = v (σ ⟨0, hk⟩) := by
  have h : ∃ i : Fin k, σ i = σ ⟨0, hk⟩ := ⟨⟨0, hk⟩, rfl⟩
  have hch : Classical.choose h = ⟨0, hk⟩ := σ.injective (Classical.choose_spec h)
  have hpos : ¬(0 < (Classical.choose h).val) := by rw [hch]; dsimp; omega
  simp only [minEnvyFreeBid, h, ↓reduceDIte, hpos]

/-- Under `minEnvyFreeBid`, the bidder in slot `i + 1` bids the per-click price
`minEnvyFreePrice μ v σ i / μ i` of slot `i`. -/
theorem minEnvyFreeBid_slot_succ [Fintype ι] [DecidableEq ι] (μ : Fin k → ℝ) (v : ι → ℝ)
    (σ : Fin k ↪ ι) (i : ℕ) (hi : i + 1 < k) :
    minEnvyFreeBid μ v σ (σ ⟨i + 1, hi⟩) =
      minEnvyFreePrice μ v σ ⟨i, by omega⟩ / μ ⟨i, by omega⟩ := by
  have h : ∃ r : Fin k, σ r = σ ⟨i + 1, hi⟩ := ⟨⟨i + 1, hi⟩, rfl⟩
  have hch : Classical.choose h = ⟨i + 1, hi⟩ := σ.injective (Classical.choose_spec h)
  have hval : (Classical.choose h).val = i + 1 := by rw [hch]
  have hpos : 0 < (Classical.choose h).val := by omega
  simp only [minEnvyFreeBid, h, ↓reduceDIte, hpos]
  have hfin : (⟨(Classical.choose h).val - 1, by omega⟩ : Fin k) = ⟨i, by omega⟩ := by
    apply Fin.ext; dsimp; omega
  rw [hfin]

/-- Under `minEnvyFreeBid`, every unassigned bidder bids its true value `v j`. -/
theorem minEnvyFreeBid_of_not_mem_range [Fintype ι] [DecidableEq ι] (μ : Fin k → ℝ) (v : ι → ℝ)
    (σ : Fin k ↪ ι) {j : ι} (hj : j ∉ Set.range σ) :
    minEnvyFreeBid μ v σ j = v j := by
  have h : ¬∃ i : Fin k, σ i = j := fun ⟨i, hi⟩ => hj ⟨i, hi⟩
  simp only [minEnvyFreeBid, h, ↓reduceDIte]

/-- On the bid profile `minEnvyFreeBid μ v σ`, the GSP per-click price at slot `i` is
`minEnvyFreePrice μ v σ i / μ i`. -/
theorem gspPerClickPrice_minEnvyFreeBid [Fintype ι] [DecidableEq ι] {μ : Fin k → ℝ} {v : ι → ℝ}
    {σ : Fin k ↪ ι} (hμ_pos : ∀ i, 0 < μ i) (i : Fin k) :
    gspPerClickPrice (minEnvyFreeBid μ v σ) σ i = minEnvyFreePrice μ v σ i / μ i := by
  unfold gspPerClickPrice nextSlotValue
  split_ifs with hlt
  · exact minEnvyFreeBid_slot_succ μ v σ i.val hlt
  · have heq : i = ⟨k - 1, by omega⟩ := by apply Fin.ext; dsimp; omega
    rw [heq, minEnvyFreePrice_last μ v σ (Fin.pos i)]
    have hcongr : maxUnassignedValue (minEnvyFreeBid μ v σ) σ = maxUnassignedValue v σ :=
      maxUnassignedValue_congr fun j hj => minEnvyFreeBid_of_not_mem_range μ v σ hj
    rw [hcongr, mul_div_cancel_left₀ _ (ne_of_gt (hμ_pos ⟨k - 1, by omega⟩))]

/-- Under `minEnvyFreeBid`, the total expected GSP slot payment equals `minEnvyFreePrice`. -/
theorem gspSlotPrice_minEnvyFreeBid [Fintype ι] [DecidableEq ι] {μ : Fin k → ℝ} {v : ι → ℝ}
    {σ : Fin k ↪ ι} (hμ_pos : ∀ i, 0 < μ i) :
    gspSlotPrice μ (minEnvyFreeBid μ v σ) σ = minEnvyFreePrice μ v σ := by
  funext i
  rw [gspSlotPrice, gspPerClickPrice_minEnvyFreeBid hμ_pos i,
    mul_div_cancel₀ _ (ne_of_gt (hμ_pos i))]

private theorem price_div_ctr_antitone {μ : Fin k → ℝ} {v : ι → ℝ} {σ : Fin k ↪ ι}
    {p : Fin k → ℝ} (hlef : IsLocallyEnvyFree μ v σ p) (hμ : StrictAnti μ)
    (hμ_pos : ∀ i, 0 < μ i) (i : ℕ) (hi : i + 1 < k) :
    p ⟨i + 1, hi⟩ / μ ⟨i + 1, hi⟩ ≤ p ⟨i, by omega⟩ / μ ⟨i, by omega⟩ := by
  have h1 : 0 < μ ⟨i, by omega⟩ := hμ_pos ⟨i, by omega⟩
  have h2 : 0 < μ ⟨i + 1, hi⟩ := hμ_pos ⟨i + 1, hi⟩
  have hμlt : μ ⟨i + 1, hi⟩ < μ ⟨i, by omega⟩ := hμ (by simp [Fin.lt_def])
  have habove := hlef.noEnvyAbove i hi
  have hir := hlef.utility_nonneg hμ hμ_pos ⟨i + 1, hi⟩
  rw [div_le_div_iff₀ h2 h1]
  nlinarith

private theorem isAssortative_minEnvyFreeBid [Fintype ι] [DecidableEq ι] {μ : Fin k → ℝ}
    {v : ι → ℝ} {σ : Fin k ↪ ι} (hσ : IsAssortative v σ) (hμ : StrictAnti μ)
    (hμ_pos : ∀ i, 0 < μ i) (hv : ∀ j, 0 ≤ v j) :
    IsAssortative (minEnvyFreeBid μ v σ) σ := by
  have hlef : IsLocallyEnvyFree μ v σ (minEnvyFreePrice μ v σ) :=
    isLocallyEnvyFree_minEnvyFreePrice hσ hμ.antitone (fun i => (hμ_pos i).le) hv
  have hanti : Antitone (minEnvyFreeBid μ v σ ∘ σ) := by
    intro a b hab
    have hsucc : ∀ (i : ℕ) (hi : i + 1 < k),
        minEnvyFreeBid μ v σ (σ ⟨i + 1, hi⟩) ≤ minEnvyFreeBid μ v σ (σ ⟨i, by omega⟩) := by
      intro i hi
      cases i with
      | zero =>
        rw [minEnvyFreeBid_slot_succ μ v σ 0 hi, minEnvyFreeBid_slot_zero μ v σ (by omega)]
        rw [div_le_iff₀ (hμ_pos ⟨0, by omega⟩)]
        have hir := hlef.utility_nonneg hμ hμ_pos ⟨0, by omega⟩
        linarith
      | succ m =>
        rw [minEnvyFreeBid_slot_succ μ v σ (m + 1) hi,
          minEnvyFreeBid_slot_succ μ v σ m (by omega)]
        exact price_div_ctr_antitone hlef hμ hμ_pos m (by omega)
    have hdiff : ∀ d (hd : a.val + d < k),
        minEnvyFreeBid μ v σ (σ ⟨a.val + d, hd⟩) ≤ minEnvyFreeBid μ v σ (σ a) := by
      intro d
      induction d with
      | zero => intro _; exact le_of_eq (by congr 2)
      | succ n ih => intro hd; exact (hsucc (a.val + n) hd).trans (ih (by omega))
    have heq : (⟨a.val + (b.val - a.val), by omega⟩ : Fin k) = b := by
      apply Fin.ext; dsimp; omega
    have hfin := hdiff (b.val - a.val) (by omega)
    simpa only [Function.comp_apply, heq] using hfin
  refine ⟨hanti, fun i j hj => ?_⟩
  rw [minEnvyFreeBid_of_not_mem_range μ v σ hj]
  have hk : 0 < k := Fin.pos i
  have hlast : v j ≤ minEnvyFreeBid μ v σ (σ ⟨k - 1, by omega⟩) := by
    by_cases hk1 : k = 1
    · have h0 : (⟨k - 1, by omega⟩ : Fin k) = ⟨0, hk⟩ := by apply Fin.ext; dsimp; omega
      rw [h0, minEnvyFreeBid_slot_zero μ v σ hk]
      exact hσ.unassigned_le ⟨0, hk⟩ j hj
    · have hlast' : k - 2 + 1 = k - 1 := by omega
      have hfin : (⟨k - 1, by omega⟩ : Fin k) = ⟨k - 2 + 1, by omega⟩ := Fin.ext hlast'.symm
      rw [hfin, minEnvyFreeBid_slot_succ μ v σ (k - 2) (by omega)]
      have hstep := price_div_ctr_antitone hlef hμ hμ_pos (k - 2) (by omega)
      have hbot : v j ≤ minEnvyFreePrice μ v σ ⟨k - 2 + 1, by omega⟩ /
          μ ⟨k - 2 + 1, by omega⟩ := by
        have hmem : (⟨k - 2 + 1, by omega⟩ : Fin k) = ⟨k - 1, by omega⟩ := Fin.ext hlast'
        rw [hmem, minEnvyFreePrice_last μ v σ hk,
          mul_div_cancel_left₀ _ (ne_of_gt (hμ_pos ⟨k - 1, by omega⟩))]
        exact le_maxUnassignedValue v σ hj
      exact hbot.trans hstep
  exact hlast.trans (hanti (show i ≤ ⟨k - 1, by omega⟩ by change i.val ≤ k - 1; omega))

/-- For any assortative assignment `σ`, the bid profile `minEnvyFreeBid μ v σ` together with `σ`
is a tie-robust full-information Nash equilibrium of the unit-weight GSP auction. -/
theorem isGSPEquilibrium_minEnvyFreeBid [Fintype ι] [DecidableEq ι] {μ : Fin k → ℝ} {v : ι → ℝ}
    {σ : Fin k ↪ ι} (hσ : IsAssortative v σ) (hμ : StrictAnti μ) (hμ_pos : ∀ i, 0 < μ i)
    (hv : ∀ j, 0 ≤ v j) :
    IsGSPEquilibrium μ v (minEnvyFreeBid μ v σ) σ := by
  let b := minEnvyFreeBid μ v σ
  let p := minEnvyFreePrice μ v σ
  have hlef : IsLocallyEnvyFree μ v σ p :=
    isLocallyEnvyFree_minEnvyFreePrice hσ hμ.antitone (fun i => (hμ_pos i).le) hv
  have hb_out : IsAssortative b σ := isAssortative_minEnvyFreeBid hσ hμ hμ_pos hv
  have hb_nonneg : ∀ j, 0 ≤ b j := fun j => by
    dsimp only [b, minEnvyFreeBid]
    split_ifs
    · exact div_nonneg (minEnvyFreePrice_nonneg hμ.antitone (fun i => (hμ_pos i).le) hv σ _)
        (hμ_pos _).le
    · exact hv j
    · exact hv j
  refine ⟨hb_nonneg, hb_out, fun x z hz σ' hσ' => ?_⟩
  let b' := Function.update b x z
  have hb'_nonneg : ∀ j, 0 ≤ b' j := fun j => by
    by_cases hj : j = x
    · subst hj; change 0 ≤ Function.update b j z j; rw [Function.update_self]; exact hz
    · change 0 ≤ Function.update b x z j; rw [Function.update_of_ne hj]; exact hb_nonneg j
  by_cases hx' : x ∈ Set.range σ'
  · obtain ⟨s, hsx⟩ := hx'
    have hutil_new : gspUtility μ v b' σ' x = μ s * (v x - gspPerClickPrice b' σ' s) := by
      rw [← hsx, gspUtility_apply_slot]
    rw [hutil_new]
    -- Shared upward-deviation bound: if `x` was not among the top `s + 1` slots (`σ 0, …, σ s`),
    -- then moving into slot `s` pays at least `b (σ s)` per click, so its utility is at most any
    -- nonnegative baseline `u` dominating slot `s - 1` (for `s > 0`).
    have hclimb : ∀ (u : ℝ), 0 ≤ u → (∀ r : Fin k, r ≤ s → σ r ≠ x) →
        v x ≤ v (σ ⟨0, Fin.pos s⟩) →
        (∀ hpos : 0 < s.val,
          μ ⟨s.val - 1, by omega⟩ * v x - p ⟨s.val - 1, by omega⟩ ≤ u) →
        μ s * (v x - gspPerClickPrice b' σ' s) ≤ u := by
      intro u hu hnot hv0 hprev
      let T : Finset ι := (Finset.Iic s).map σ
      have hxT : x ∉ T := by
        simp only [T, Finset.mem_map, Finset.mem_Iic, not_exists, not_and]
        exact fun r hr heq => hnot r hr heq
      have hTcard : s.val + 1 ≤ T.card := by rw [Finset.card_map, Fin.card_Iic]
      have hTbid : ∀ y ∈ T, b (σ s) ≤ b' y := by
        intro y hy
        obtain ⟨r, hr, rfl⟩ := Finset.mem_map.mp hy
        have hup : b' (σ r) = b (σ r) :=
          Function.update_of_ne (hnot r (Finset.mem_Iic.mp hr)) z b
        rw [hup]
        exact hb_out.antitone (Finset.mem_Iic.mp hr)
      have hppc : b (σ s) ≤ gspPerClickPrice b' σ' s :=
        le_gspPerClickPrice_of_card_le hσ' hsx hxT hTcard hTbid
      have hμs_pos : 0 < μ s := hμ_pos s
      rcases Nat.eq_zero_or_pos s.val with hs0 | hspos
      · have hs_eq : s = ⟨0, Fin.pos s⟩ := Fin.ext hs0
        have hval : b (σ s) = v (σ ⟨0, Fin.pos s⟩) := by
          rw [hs_eq]; exact minEnvyFreeBid_slot_zero μ v σ (Fin.pos s)
        nlinarith
      · let s' : Fin k := ⟨s.val - 1, by omega⟩
        have hs_eq : s = ⟨s'.val + 1, by dsimp [s']; omega⟩ := by
          apply Fin.ext; dsimp [s']; omega
        have hval : b (σ s) = p s' / μ s' := by
          conv_lhs => rw [hs_eq]
          exact minEnvyFreeBid_slot_succ μ v σ s'.val (by dsimp [s']; omega)
        have hμs'_pos : 0 < μ s' := hμ_pos s'
        have hμ_lt : μ s < μ s' := hμ (show s' < s by change s.val - 1 < s.val; omega)
        have hratio_pos : 0 < μ s / μ s' := div_pos hμs_pos hμs'_pos
        have hratio_le : μ s / μ s' ≤ 1 := (div_le_one hμs'_pos).mpr hμ_lt.le
        have hkey : μ s * (v x - gspPerClickPrice b' σ' s) ≤
            (μ s / μ s') * (μ s' * v x - p s') := by
          have h1 : μ s * (v x - gspPerClickPrice b' σ' s) ≤ μ s * (v x - p s' / μ s') := by
            rw [← hval]; nlinarith
          have h2 : μ s * (v x - p s' / μ s') = (μ s / μ s') * (μ s' * v x - p s') := by
            have hne : μ s' ≠ 0 := ne_of_gt hμs'_pos
            field_simp
          exact h2 ▸ h1
        calc μ s * (v x - gspPerClickPrice b' σ' s)
            ≤ (μ s / μ s') * (μ s' * v x - p s') := hkey
          _ ≤ (μ s / μ s') * u := mul_le_mul_of_nonneg_left (hprev hspos) hratio_pos.le
          _ ≤ 1 * u := mul_le_mul_of_nonneg_right hratio_le hu
          _ = u := one_mul u
    by_cases hx : x ∈ Set.range σ
    · obtain ⟨t, htx⟩ := hx
      have hutil_old : gspUtility μ v b σ x = μ t * v (σ t) - p t := by
        rw [← htx, gspUtility_apply_slot, gspPerClickPrice_minEnvyFreeBid hμ_pos t]
        have hne : μ t ≠ 0 := ne_of_gt (hμ_pos t)
        dsimp only [p]
        field_simp
      rw [hutil_old]
      rcases lt_or_ge s t with hst | hts
      · refine hclimb (μ t * v (σ t) - p t) (hlef.utility_nonneg hμ hμ_pos t)
          (fun r hr heq => not_le_of_gt hst (σ.injective (heq.trans htx.symm) ▸ hr))
          (htx ▸ hσ.antitone (show (⟨0, Fin.pos s⟩ : Fin k) ≤ t by change 0 ≤ t.val; omega))
          (fun _ => htx ▸ hlef.noEnvy hμ hμ_pos t _)
      · rw [← htx]
        -- Staying or moving down: `t ≤ s`.
        have hppc : p s / μ s ≤ gspPerClickPrice b' σ' s := by
          by_cases hlt : s.val + 1 < k
          · let s1 : Fin k := ⟨s.val + 1, hlt⟩
            let T : Finset ι := ((Finset.Iic s1).map σ).erase (σ t)
            have htmem : σ t ∈ (Finset.Iic s1).map σ :=
              Finset.mem_map.mpr ⟨t, Finset.mem_Iic.mpr (by
                change t.val ≤ s.val + 1; exact Nat.le_succ_of_le hts), rfl⟩
            have hTcard : s.val + 1 ≤ T.card := by
              rw [Finset.card_erase_of_mem htmem, Finset.card_map, Fin.card_Iic]
              dsimp [s1]; omega
            have hTbid : ∀ y ∈ T, p s / μ s ≤ b' y := by
              intro y hy
              have hne : y ≠ σ t := Finset.ne_of_mem_erase hy
              obtain ⟨r, hr, rfl⟩ := Finset.mem_map.mp (Finset.mem_of_mem_erase hy)
              have hup : b' (σ r) = b (σ r) := Function.update_of_ne (htx ▸ hne) z b
              rw [hup]
              calc p s / μ s = b (σ s1) := (minEnvyFreeBid_slot_succ μ v σ s.val hlt).symm
                _ ≤ b (σ r) := hb_out.antitone (Finset.mem_Iic.mp hr)
            exact le_gspPerClickPrice_of_card_le hσ' hsx
              (htx ▸ Finset.notMem_erase (σ t) _) hTcard hTbid
          · have hs_eq : s = ⟨k - 1, by omega⟩ := by apply Fin.ext; dsimp; omega
            rw [hs_eq, show p ⟨k - 1, by omega⟩ = μ ⟨k - 1, by omega⟩ * maxUnassignedValue v σ from
              minEnvyFreePrice_last μ v σ (Fin.pos s),
              mul_div_cancel_left₀ _ (ne_of_gt (hμ_pos ⟨k - 1, by omega⟩))]
            rw [← hs_eq]
            by_cases hne : (Finset.univ \ Finset.univ.map σ).Nonempty
            · obtain ⟨jstar, hjmem, hjval⟩ := Finset.exists_mem_eq_sup' hne v
              have hjrange : jstar ∉ Set.range σ := by
                simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_map, true_and,
                  not_exists] at hjmem
                rintro ⟨r, rfl⟩
                exact hjmem r rfl
              have hmax_eq : maxUnassignedValue v σ = v jstar := by
                simp only [maxUnassignedValue, hne, ↓reduceDIte, hjval]
              let T : Finset ι := insert jstar ((Finset.univ.map σ).erase (σ t))
              have hjt_ne : jstar ≠ σ t := fun h => hjrange ⟨t, h.symm⟩
              have hjnot : jstar ∉ (Finset.univ.map σ).erase (σ t) := by
                intro h
                obtain ⟨r, -, hr⟩ := Finset.mem_map.mp (Finset.mem_of_mem_erase h)
                exact hjrange ⟨r, hr⟩
              have htmem : σ t ∈ Finset.univ.map σ :=
                Finset.mem_map.mpr ⟨t, Finset.mem_univ _, rfl⟩
              have hTcard : s.val + 1 ≤ T.card := by
                rw [Finset.card_insert_of_notMem hjnot, Finset.card_erase_of_mem htmem,
                  Finset.card_map, Finset.card_fin]
                omega
              have hxT : x ∉ T := by
                rw [← htx]
                simp only [T, Finset.mem_insert, not_or]
                exact ⟨hjt_ne.symm, Finset.notMem_erase _ _⟩
              have hTbid : ∀ y ∈ T, maxUnassignedValue v σ ≤ b' y := by
                intro y hy
                rw [hmax_eq]
                rcases Finset.mem_insert.mp hy with rfl | hy'
                · have hup : b' y = b y := Function.update_of_ne (htx ▸ hjt_ne) z b
                  rw [hup]
                  exact le_of_eq (minEnvyFreeBid_of_not_mem_range μ v σ hjrange).symm
                · have hne_t : y ≠ σ t := Finset.ne_of_mem_erase hy'
                  obtain ⟨r, -, rfl⟩ := Finset.mem_map.mp (Finset.mem_of_mem_erase hy')
                  have hup : b' (σ r) = b (σ r) := Function.update_of_ne (htx ▸ hne_t) z b
                  rw [hup]
                  calc v jstar = b jstar := (minEnvyFreeBid_of_not_mem_range μ v σ hjrange).symm
                    _ ≤ b (σ r) := hb_out.unassigned_le r jstar hjrange
              exact le_gspPerClickPrice_of_card_le hσ' hsx hxT hTcard hTbid
            · have hzero : maxUnassignedValue v σ = 0 := by
                simp only [maxUnassignedValue, hne, ↓reduceDIte]
              rw [hzero]
              exact gspPerClickPrice_nonneg hb'_nonneg σ' s
        have hμs_pos : 0 < μ s := hμ_pos s
        have hmul : p s ≤ μ s * gspPerClickPrice b' σ' s := by
          rwa [div_le_iff₀' hμs_pos] at hppc
        have hne_s : μ s * v (σ t) - p s ≤ μ t * v (σ t) - p t :=
          hlef.noEnvy hμ hμ_pos t s
        linarith
    · -- `x` was unassigned (`x ∉ Set.range σ`), moves into slot `s`.
      rw [gspUtility_of_not_mem_range μ v b σ hx]
      exact hclimb 0 le_rfl (fun r _ heq => hx ⟨r, heq⟩)
        (hσ.unassigned_le ⟨0, Fin.pos s⟩ x hx)
        (fun _ => hlef.unassigned_noEnvy_slot hμ hμ_pos hx _)
  · -- `x` is unassigned under `σ'`: utility is `0`.
    rw [gspUtility_of_not_mem_range μ v b' σ' hx']
    by_cases hx : x ∈ Set.range σ
    · obtain ⟨t, rfl⟩ := hx
      rw [gspUtility_apply_slot, gspPerClickPrice_minEnvyFreeBid hμ_pos t]
      have hne : μ t ≠ 0 := ne_of_gt (hμ_pos t)
      have hir := hlef.utility_nonneg hμ hμ_pos t
      have heq : μ t * (v (σ t) - p t / μ t) = μ t * v (σ t) - p t := by field_simp
      linarith
    · rw [gspUtility_of_not_mem_range μ v b σ hx]

/-- **Theorem 28.2** ([LahaiePennockSaberiVohra2007], §28.3.2, pp. 706–707): under strictly
decreasing positive click-through rates `μ` and nonnegative bidder values `v` with at least `k`
bidders, the unit-weight GSP auction admits a tie-robust full-information Nash equilibrium `(b, σ)`
whose allocation `σ` is optimal and locally envy-free at the auction's actual slot payments
`gspSlotPrice μ b σ`, which coincide with the minimal nonnegative locally envy-free (Vickrey)
prices `minEnvyFreePrice μ v σ`.

*Scope*: bidder-independent CTRs `αᵢⱼ = μᵢ`, unit weights `wⱼ = 1`, all `k` slots filled
(`k ≤ Fintype.card ι`), nonnegative bids/values, and tie-robust Nash equilibrium
(`IsGSPEquilibrium`, quantifying over all consistent tie-breaking outcomes `σ'` after every
deviation `z ≥ 0`). -/
theorem exists_isGSPEquilibrium_locallyEnvyFree [Fintype ι] [DecidableEq ι]
    {μ : Fin k → ℝ} {v : ι → ℝ} (hμ : StrictAnti μ) (hμ_pos : ∀ i, 0 < μ i)
    (hv : ∀ j, 0 ≤ v j) (hk : k ≤ Fintype.card ι) :
    ∃ (b : ι → ℝ) (σ : Fin k ↪ ι),
      IsGSPEquilibrium μ v b σ ∧
      IsOptimal μ v σ ∧
      IsLocallyEnvyFree μ v σ (gspSlotPrice μ b σ) ∧
      gspSlotPrice μ b σ = minEnvyFreePrice μ v σ := by
  obtain ⟨σ, hσ⟩ := exists_isAssortative v hk
  have hprice : gspSlotPrice μ (minEnvyFreeBid μ v σ) σ = minEnvyFreePrice μ v σ :=
    gspSlotPrice_minEnvyFreeBid hμ_pos
  refine ⟨minEnvyFreeBid μ v σ, σ,
    isGSPEquilibrium_minEnvyFreeBid hσ hμ hμ_pos hv,
    hσ.isOptimal hμ.antitone (fun i => (hμ_pos i).le),
    ?_, hprice⟩
  rw [hprice]
  exact isLocallyEnvyFree_minEnvyFreePrice hσ hμ.antitone (fun i => (hμ_pos i).le) hv

end Cslib.GameTheory.SponsoredSearch
