/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.DigitalGoods.ProfitExtraction
public import CslibFrontier.GameTheory.Mechanism.MultiUnit
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Digital goods auctions: impossibility, competitive lower bounds, and limited-supply reduction

This module formalizes the impossibility results, competitive-ratio lower bounds, and
limited-supply reduction for prior-free digital goods auctions from [HartlineKarlin2007], Chapter 13
(§§13.3.1, 13.4.2–13.4.3, and Exercises 13.8–13.9, pp. 340–341, 345–347, 361):

* **Symmetric deterministic impossibility (`Theorem 13.24`, p. 341; `Corollary 13.35`, p. 345):**
  A mechanism is *symmetric* (`IsSymmetric`, Footnote 1, p. 340) when permuting nonnegative bids
  permutes allocations and payments identically. Using an inductive threshold-forcing argument on
  two-valued bid profiles `(h, …, h, 1, …, 1)`:
  - For every finite bidder pool with `n ≥ 2` bidders, every symmetric deterministic (`IsBinary`)
    DSIC and IR auction has competitive ratio at least `n` with respect to `ℱ⁽²⁾`
    (`card_le_of_isCompetitive_symmetric`), so no uniform constant `β` works across all `n ≥ 2`
    (**Corollary 13.35**, `not_exists_const_competitive_symmetric`).
  - The bound `n` is exact for every `n ≥ 2`: the symmetric second-price digital goods auction
    `symmetricSecondPrice` (awarding to every bidder meeting the highest other bid at that price) is
    DSIC, IR, normalized, binary, symmetric, and has competitive ratio **exact `n`**
    (`isLeast_symmetricSecondPrice_competitiveRatio`; in particular `2` for `n = 2`, p. 347).
  - For every `β > 0` and `γ : ℝ`, there exist `n ≥ 2` and `h ≥ 1` such that no symmetric
    deterministic DSIC, IR auction on `Fin n` achieves profit at least `ℱ(b) / β - h * γ` on all
    profiles in `[1, h]ⁿ` (**Theorem 13.24**, `exists_not_approx_symmetric_deterministic`).
* **Randomized competitive lower bounds (`Lemma 13.38` & `n = 3` `13/6` bound, pp. 346–347;
  `Exercise 13.8`, p. 361):**
  A truthful-in-expectation randomized digital goods auction (Definition 13.5, p. 334) is
  represented directly by its expected allocation (`IsUnitAlloc`, values in `[0, 1]`) and expected
  payment as a `SingleParameter.Mechanism ι` satisfying `IsDSIC` and `IsIR`. Using a finite
  equal-revenue grid distribution `z_j = (m + j) / m` (`0 ≤ j ≤ m (H - 1)`) and discrete Abel
  summation, every `n`-bidder `IsDSIC ∧ IsIR ∧ IsUnitAlloc` mechanism has expected profit at most
  `n` on the grid, yielding:
  - **Lemma 13.38** (`two_le_of_isCompetitive_two`, pp. 346–347): no `2`-bidder truthful IR
    digital goods auction has competitive ratio less than `2` against `ℱ⁽²⁾` (tight via
    `symmetricSecondPrice`).
  - **`n = 3` lower bound** (`thirteen_div_six_le_of_isCompetitive_three`, p. 347): no `3`-bidder
    truthful IR digital goods auction has competitive ratio less than `13 / 6` against `ℱ⁽²⁾`.
  - **Exercise 13.8** (`exists_strictly_higher_profit_two`, p. 361): for every `2`-bidder truthful
    IR digital goods auction `M`, there is a deterministic DSIC, IR, normalized auction `M'` and a
    nonnegative bid profile `b` on which `M'` earns strictly more profit than `M`.
* **Limited-supply reduction (`Exercise 13.9`, p. 361):**
  For `k` identical units and benchmark `ℱ⁽²˒ᵏ⁾(v) = max_{2 ≤ m ≤ min k n} m · v_(m)`
  (`optimalProfitTwoLimited`), running any `β`-competitive DSIC, normalized, `[0, 1]`-allocated
  digital goods auction `A` on the top `min k n` bidders (indexed in their original `[LinearOrder
  ι]` order) and applying Myerson's payment rule (`limitedSupplyMechanism`) yields a DSIC, IR,
  normalized `k`-unit auction (`∑ i, alloc b i ≤ k`, binary when `A` is binary) that is
  `β`-competitive against `ℱ⁽²˒ᵏ⁾` (`limitedSupplyMechanism_isCompetitive`).

The general-`n` asymptotic lower bound `2.42` of Theorem 13.37 (p. 346) is not proved here and
remains open under issue `#7789`. No running-time claim is made.

## Main definitions

* `IsSymmetric`: permutation invariance of a single-parameter mechanism on nonnegative bids
  ([HartlineKarlin2007], Footnote 1, p. 340).
* `IsUnitAlloc`: allocations lie in `[0, 1]` on nonnegative bids (capturing both deterministic
  `0`-`1` rules and expected allocations of randomized digital goods auctions).
* `symmetricSecondPrice`: deterministic symmetric second-price digital goods auction.
* `optimalProfitTwoLimited`: limited-supply benchmark `ℱ⁽²˒ᵏ⁾` ([HartlineKarlin2007],
  Exercise 13.9, p. 361).
* `limitedSupplyAlloc`, `limitedSupplyMechanism`: `k`-unit auction constructed from a digital
  goods auction on the top `k` bidders.

## Main results

* `card_le_of_isCompetitive_symmetric`, `not_exists_const_competitive_symmetric`: exact `n`-bidder
  lower bound and **Corollary 13.35** ([HartlineKarlin2007], §13.4.2, p. 345).
* `symmetricSecondPrice_isDSIC`, `symmetricSecondPrice_isIR`, `symmetricSecondPrice_isNormalized`,
  `symmetricSecondPrice_isBinary`, `symmetricSecondPrice_isSymmetric`,
  `isLeast_symmetricSecondPrice_competitiveRatio`: exact tightness (`n`, and `2` for `n = 2`).
* `exists_not_approx_symmetric_deterministic`: **Theorem 13.24** ([HartlineKarlin2007], §13.3.1,
  p. 341).
* `two_le_of_isCompetitive_two`: **Lemma 13.38** ([HartlineKarlin2007], §13.4.3, pp. 346–347).
* `thirteen_div_six_le_of_isCompetitive_three`: `13 / 6` lower bound for `n = 3`
  ([HartlineKarlin2007], §13.4.3, p. 347).
* `exists_strictly_higher_profit_two`: **Exercise 13.8** ([HartlineKarlin2007], p. 361).
* `limitedSupplyMechanism_isDSIC`, `limitedSupplyMechanism_isIR`,
  `limitedSupplyMechanism_isNormalized`, `sum_limitedSupplyAlloc_le`,
  `limitedSupplyAlloc_mem_multiUnitFeasible`, `limitedSupplyMechanism_isCompetitive`:
  **Exercise 13.9** ([HartlineKarlin2007], p. 361).

## References

* [J. D. Hartline and A. R. Karlin, *Profit Maximization in Mechanism Design*, Chapter 13 of
  *Algorithmic Game Theory*][HartlineKarlin2007]
-/

open Finset
open scoped BigOperators

public section

namespace Cslib.GameTheory.SingleParameter.DigitalGoods

/-! ### Symmetry and `[0, 1]`-allocation predicates -/

section Predicates

variable {ι : Type*}

/-- A single-parameter mechanism is *symmetric* if permuting any nonnegative bid profile permutes
allocations and payments in the same way ([HartlineKarlin2007], §13.3.1, Footnote 1, p. 340). -/
@[expose] def IsSymmetric (M : Mechanism ι) : Prop :=
  ∀ (σ : Equiv.Perm ι) (b : ι → ℝ) (i : ι), 0 ≤ b →
    M.allocation (b ∘ σ) i = M.allocation b (σ i) ∧
      M.payment (b ∘ σ) i = M.payment b (σ i)

/-- A single-parameter allocation rule takes values in `[0, 1]` on nonnegative bid profiles. This
holds for every deterministic `0`-`1` rule (`IsBinary`) and for the expected allocation rule of
every randomized digital goods auction (selling at most one copy per bidder). -/
@[expose] def IsUnitAlloc (x : (ι → ℝ) → ι → ℝ) : Prop :=
  ∀ b, 0 ≤ b → ∀ i, 0 ≤ x b i ∧ x b i ≤ 1

/-- Every `0`-`1` allocation rule takes values in `[0, 1]`. -/
theorem IsBinary.isUnitAlloc {x : (ι → ℝ) → ι → ℝ} (hx : IsBinary x) : IsUnitAlloc x := by
  intro b hb i
  rcases hx b hb i with h | h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩

/-- Transport a mechanism along an equivalence of bidder index types. -/
private def reindexMechanism {ι' : Type*} (e : ι' ≃ ι) (M : Mechanism ι) : Mechanism ι' where
  allocation b i := M.allocation (b ∘ e.symm) (e i)
  payment b i := M.payment (b ∘ e.symm) (e i)

private theorem reindexMechanism_isDSIC {ι' : Type*} [DecidableEq ι] [DecidableEq ι']
    (e : ι' ≃ ι) {M : Mechanism ι} (hDSIC : M.IsDSIC) : (reindexMechanism e M).IsDSIC := by
  intro i b v hb hv
  have hb' : 0 ≤ b ∘ e.symm := fun j => hb (e.symm j)
  have hupd : Function.update b i v ∘ e.symm = Function.update (b ∘ e.symm) (e i) v := by
    ext j
    simp only [Function.comp_apply]
    by_cases hj : j = e i
    · rw [hj, Equiv.symm_apply_apply, Function.update_self, Function.update_self]
    · have hne : e.symm j ≠ i := fun h => hj (by rw [← h, Equiv.apply_symm_apply])
      rw [Function.update_of_ne hne, Function.update_of_ne hj]
      rfl
  have h := hDSIC (e i) (b ∘ e.symm) v hb' hv
  simpa only [Mechanism.utility, reindexMechanism, hupd] using h

private theorem reindexMechanism_isIR {ι' : Type*} (e : ι' ≃ ι) {M : Mechanism ι} (hIR : M.IsIR) :
    (reindexMechanism e M).IsIR := by
  intro i b hb
  have h := hIR (e i) (b ∘ e.symm) (fun j => hb (e.symm j))
  simpa only [Mechanism.utility, reindexMechanism, Function.comp_apply,
    Equiv.symm_apply_apply] using h

private theorem reindexMechanism_isBinary {ι' : Type*} (e : ι' ≃ ι) {M : Mechanism ι}
    (hBin : IsBinary M.allocation) : IsBinary (reindexMechanism e M).allocation :=
  fun b hb i => hBin (b ∘ e.symm) (fun j => hb (e.symm j)) (e i)

private theorem reindexMechanism_isUnitAlloc {ι' : Type*} (e : ι' ≃ ι) {M : Mechanism ι}
    (hUnit : IsUnitAlloc M.allocation) : IsUnitAlloc (reindexMechanism e M).allocation :=
  fun b hb i => hUnit (b ∘ e.symm) (fun j => hb (e.symm j)) (e i)

private theorem reindexMechanism_isSymmetric {ι' : Type*} (e : ι' ≃ ι) {M : Mechanism ι}
    (hSym : IsSymmetric M) : IsSymmetric (reindexMechanism e M) := by
  intro σ b i hb
  let τ : Equiv.Perm ι := (e.symm.trans σ).trans e
  have hcomp : (b ∘ σ) ∘ e.symm = (b ∘ e.symm) ∘ τ := by
    ext j
    simp only [Function.comp_apply, τ, Equiv.trans_apply, Equiv.symm_apply_apply]
  have h := hSym τ (b ∘ e.symm) (e i) (fun j => hb (e.symm j))
  have hτ : τ (e i) = e (σ i) := by
    simp only [τ, Equiv.trans_apply, Equiv.symm_apply_apply]
  simpa only [reindexMechanism, hcomp, hτ] using h

private theorem sum_payment_reindexMechanism {ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι' ≃ ι)
    (M : Mechanism ι) (b : ι' → ℝ) :
    ∑ i : ι', (reindexMechanism e M).payment b i = ∑ j : ι, M.payment (b ∘ e.symm) j :=
  Fintype.sum_equiv e _ _ fun _ => rfl

private theorem optimalProfitTwo_comp_equiv {ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι' ≃ ι)
    {b : ι → ℝ} (hb : 0 ≤ b) : optimalProfitTwo (b ∘ e) = optimalProfitTwo b := by
  classical
  have hcard : ∀ j : ι',
      (univ.filter fun i : ι' => b (e j) ≤ b (e i)).card =
        (univ.filter fun i : ι => b (e j) ≤ b i).card := fun j =>
    Finset.card_bij (fun i _ => e i)
      (fun i hi => mem_filter.2 ⟨mem_univ _, (mem_filter.1 hi).2⟩)
      (fun _ _ _ _ h => e.injective h)
      (fun i hi => ⟨e.symm i, mem_filter.2 ⟨mem_univ _, by
        simpa only [Equiv.apply_symm_apply] using (mem_filter.1 hi).2⟩, e.apply_symm_apply i⟩)
  apply le_antisymm
  · refine singlePriceProfitOn_le (singlePriceProfitOn_nonneg fun i _ => hb i) fun j _ hj => ?_
    dsimp only [Function.comp_apply] at hj ⊢
    have hcard_ge : 2 ≤ (univ.filter fun i : ι => b (e j) ≤ b i).card := by
      rwa [← hcard j]
    rw [hcard j]
    unfold optimalProfitTwo singlePriceProfitOn
    have hne : (univ.filter fun k : ι => 2 ≤ (univ.filter fun i : ι => b k ≤ b i).card).Nonempty :=
      ⟨e j, mem_filter.2 ⟨mem_univ _, hcard_ge⟩⟩
    rw [dite_eq_left hne]
    exact le_sup' (fun k : ι => b k * ((univ.filter fun i : ι => b k ≤ b i).card : ℝ))
      (mem_filter.2 ⟨mem_univ _, hcard_ge⟩)
  · refine singlePriceProfitOn_le (singlePriceProfitOn_nonneg fun i _ => hb (e i)) fun j _ hj => ?_
    have hcard_eq : (univ.filter fun i : ι => b j ≤ b i).card =
        (univ.filter fun i : ι' => (b ∘ e) (e.symm j) ≤ (b ∘ e) i).card := by
      have hc := (hcard (e.symm j)).symm
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hc
    have hcard_ge : 2 ≤ (univ.filter fun i : ι' => (b ∘ e) (e.symm j) ≤ (b ∘ e) i).card :=
      hcard_eq ▸ hj
    rw [hcard_eq]
    unfold optimalProfitTwo singlePriceProfitOn
    have hne : (univ.filter fun k : ι' =>
        2 ≤ (univ.filter fun i : ι' => (b ∘ e) k ≤ (b ∘ e) i).card).Nonempty :=
      ⟨e.symm j, mem_filter.2 ⟨mem_univ _, hcard_ge⟩⟩
    rw [dite_eq_left hne]
    have hmem : e.symm j ∈ univ.filter fun k : ι' =>
        2 ≤ (univ.filter fun i : ι' => (b ∘ e) k ≤ (b ∘ e) i).card :=
      mem_filter.2 ⟨mem_univ _, hcard_ge⟩
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      le_sup' (fun k : ι' =>
        (b ∘ e) k * ((univ.filter fun i : ι' => (b ∘ e) k ≤ (b ∘ e) i).card : ℝ)) hmem

private theorem reindexMechanism_isCompetitive {ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι' ≃ ι)
    {M : Mechanism ι} {β : ℝ}
    (hComp : IsCompetitive optimalProfitTwo (fun b => ∑ i, M.payment b i) β) :
    IsCompetitive optimalProfitTwo (fun b => ∑ i, (reindexMechanism e M).payment b i) β := by
  refine ⟨hComp.1, fun b hb => ?_⟩
  dsimp only
  rw [sum_payment_reindexMechanism]
  have h := hComp.2 (b ∘ e.symm) (fun j => hb (e.symm j))
  have hbench : optimalProfitTwo (b ∘ e.symm) = optimalProfitTwo b :=
    optimalProfitTwo_comp_equiv e.symm hb
  rwa [hbench] at h

end Predicates

/-! ### Symmetric deterministic impossibility (`Theorem 13.24` & `Corollary 13.35`) -/

section SymmetricDeterministic

/-- Two-valued test profile on `Fin n`: the first `k` bidders bid `h` and the remaining `n - k`
bidders bid `1`. -/
private def twoValProfile (n k : ℕ) (h : ℝ) : Fin n → ℝ :=
  fun i => if i.val < k then h else 1

private theorem twoValProfile_nonneg (n k : ℕ) {h : ℝ} (hh : 1 ≤ h) :
    0 ≤ twoValProfile n k h := fun i => by
  change (0 : ℝ) ≤ twoValProfile n k h i
  dsimp only [twoValProfile]
  split_ifs <;> linarith

private theorem twoValProfile_bounds (n k : ℕ) {h : ℝ} (hh : 1 ≤ h) (i : Fin n) :
    1 ≤ twoValProfile n k h i ∧ twoValProfile n k h i ≤ h := by
  dsimp only [twoValProfile]
  split_ifs <;> exact ⟨by linarith, by linarith⟩

private theorem twoValProfile_update_succ (n : ℕ) {k : ℕ} (hk : k < n) (h : ℝ) :
    Function.update (twoValProfile n k h) ⟨k, hk⟩ h = twoValProfile n (k + 1) h := by
  ext i
  by_cases hi : i = ⟨k, hk⟩
  · subst hi
    simp only [Function.update_self, twoValProfile, Nat.lt_succ_self, ↓reduceIte]
  · rw [Function.update_of_ne hi]
    have hval : i.val ≠ k := fun hEq => hi (Fin.ext hEq)
    dsimp only [twoValProfile]
    by_cases hlt : i.val < k
    · have hlt' : i.val < k + 1 := Nat.lt_succ_of_lt hlt
      simp only [hlt, hlt', ↓reduceIte]
    · have hlt' : ¬ i.val < k + 1 := by omega
      simp only [hlt, hlt', ↓reduceIte]

private theorem payment_le_zero_of_alloc_zero {ι : Type*} {M : Mechanism ι} (hIR : M.IsIR)
    {b : ι → ℝ} (hb : 0 ≤ b) {i : ι} (h0 : M.allocation b i = 0) : M.payment b i ≤ 0 := by
  have h := hIR i b hb
  simp only [Mechanism.utility, h0, mul_zero, zero_sub] at h
  linarith

private theorem payment_le_bid_of_isBinary {ι : Type*} {M : Mechanism ι} (hIR : M.IsIR)
    (hBin : IsBinary M.allocation) {b : ι → ℝ} (hb : 0 ≤ b) (i : ι) : M.payment b i ≤ b i := by
  have h := hIR i b hb
  have hbi : 0 ≤ b i := hb i
  simp only [Mechanism.utility] at h
  rcases hBin b hb i with h0 | h1
  · rw [h0, mul_zero] at h
    linarith
  · rw [h1, mul_one] at h
    linarith

private theorem payment_update_le_of_win {ι : Type*} [DecidableEq ι] {M : Mechanism ι}
    (hDSIC : M.IsDSIC) (hIR : M.IsIR) (hBin : IsBinary M.allocation) {b : ι → ℝ} (hb : 0 ≤ b)
    {i : ι} {z : ℝ} (hz : 0 ≤ z) (hwin : M.allocation b i = 1) :
    M.payment (Function.update b i z) i ≤ b i := by
  have hb' : 0 ≤ Function.update b i z := update_nonneg hb i hz
  rcases hBin _ hb' i with h0 | h1
  · exact (payment_le_zero_of_alloc_zero hIR hb' h0).trans (hb i)
  · have h1' := hDSIC.utility_update_le i hb (hb i) hz
    have h2' := hDSIC.utility_update_le i hb hz (hb i)
    rw [Function.update_eq_self, hwin, h1] at h1' h2'
    have hpay_eq : M.payment (Function.update b i z) i = M.payment b i := by linarith
    rw [hpay_eq]
    exact payment_le_bid_of_isBinary hIR hBin hb i

private theorem symm_eq_of_bid_eq {ι : Type*} {M : Mechanism ι}
    (hSym : IsSymmetric M) {b : ι → ℝ} (hb : 0 ≤ b) {i j : ι} (heq : b i = b j) :
    M.allocation b i = M.allocation b j ∧ M.payment b i = M.payment b j := by
  classical
  have hcomp : b ∘ Equiv.swap i j = b := by
    ext k
    simp only [Function.comp_apply]
    by_cases hki : k = i
    · subst hki; simp only [Equiv.swap_apply_left, heq]
    · by_cases hkj : k = j
      · subst hkj; simp only [Equiv.swap_apply_right, heq]
      · simp only [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have h := hSym (Equiv.swap i j) b i hb
  simpa only [hcomp, Equiv.swap_apply_left] using h

/-- Number of indices in `Fin n` with value strictly below `k ≤ n`. -/
private theorem card_filter_val_lt {n k : ℕ} (hkn : k ≤ n) :
    (univ.filter fun i : Fin n => i.val < k).card = k := by
  have heq : (univ.filter fun i : Fin n => i.val < k) =
      (Finset.range k).attach.image
        fun x => ⟨x.1, lt_of_lt_of_le (Finset.mem_range.1 x.2) hkn⟩ := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_attach, Subtype.exists]
    exact ⟨fun hi => ⟨i.val, Finset.mem_range.2 hi, Fin.ext rfl⟩,
      fun ⟨_, hx, h⟩ => h ▸ Finset.mem_range.1 hx⟩
  rw [heq, Finset.card_image_of_injective _ fun _ _ hab => Subtype.ext (congrArg Fin.val hab),
    Finset.card_attach, Finset.card_range]

/-- Inductive dichotomy for symmetric deterministic DSIC, IR mechanisms on `twoValProfile n k h`:
for any `m ≤ n` and `1 ≤ h`, either at some stage `k < m` every `1`-bidder loses and total profit
is at most `k`, or at stage `m` every bidder pays at most `1` and total profit is at most `n`. -/
private theorem symmetric_twoVal_dichotomy {n m : ℕ} (hmn : m ≤ n) {h : ℝ} (hh : 1 ≤ h)
    {M : Mechanism (Fin n)} (hDSIC : M.IsDSIC) (hIR : M.IsIR) (hBin : IsBinary M.allocation)
    (hSym : IsSymmetric M) :
    (∃ k : ℕ, k < m ∧ ∑ i : Fin n, M.payment (twoValProfile n k h) i ≤ (k : ℝ)) ∨
      ∑ i : Fin n, M.payment (twoValProfile n m h) i ≤ (n : ℝ) := by
  have hstep : ∀ k : ℕ, k ≤ m →
      (∃ r : ℕ, r < k ∧ ∑ i : Fin n, M.payment (twoValProfile n r h) i ≤ (r : ℝ)) ∨
        (∀ i : Fin n, i.val < k → M.payment (twoValProfile n k h) i ≤ 1) := by
    intro k
    induction k with
    | zero =>
        intro _
        exact Or.inr fun i hi => absurd hi (Nat.not_lt_zero _)
    | succ k ih =>
        intro hk
        rcases ih (Nat.le_of_succ_le hk) with ⟨r, hr, hsum⟩ | hpay
        · exact Or.inl ⟨r, Nat.lt_succ_of_lt hr, hsum⟩
        · have hkn : k < n := lt_of_lt_of_le (Nat.lt_of_succ_le hk) hmn
          let ik : Fin n := ⟨k, hkn⟩
          have hbk0 : 0 ≤ twoValProfile n k h := twoValProfile_nonneg n k hh
          have hbik : twoValProfile n k h ik = 1 := by
            simp only [twoValProfile, ik, lt_self_iff_false, ↓reduceIte]
          rcases hBin _ hbk0 ik with h0 | h1
          · left
            refine ⟨k, Nat.lt_succ_self k, ?_⟩
            have hbound : ∀ i : Fin n,
                M.payment (twoValProfile n k h) i ≤ if i.val < k then (1 : ℝ) else 0 := by
              intro i
              split_ifs with hik
              · exact hpay i hik
              · have hbi : twoValProfile n k h i = 1 := by
                  simp only [twoValProfile, hik, ↓reduceIte]
                have hal := (symm_eq_of_bid_eq hSym hbk0 (hbi.trans hbik.symm)).1
                exact payment_le_zero_of_alloc_zero hIR hbk0 (hal.trans h0)
            calc ∑ i : Fin n, M.payment (twoValProfile n k h) i
                ≤ ∑ i : Fin n, if i.val < k then (1 : ℝ) else 0 :=
                  Finset.sum_le_sum fun i _ => hbound i
              _ = ((univ.filter fun i : Fin n => i.val < k).card : ℝ) := by
                  simp only [Finset.sum_boole]
              _ = (k : ℝ) := by rw [card_filter_val_lt hkn.le]
          · right
            have hpay_ik : M.payment (twoValProfile n (k + 1) h) ik ≤ 1 := by
              rw [← twoValProfile_update_succ n hkn h, ← hbik]
              exact payment_update_le_of_win hDSIC hIR hBin hbk0 (by linarith) h1
            have hbk10 : 0 ≤ twoValProfile n (k + 1) h := twoValProfile_nonneg n (k + 1) hh
            have hbik1 : twoValProfile n (k + 1) h ik = h := by
              simp only [twoValProfile, ik, Nat.lt_succ_self, ↓reduceIte]
            intro i hi
            have hbi1 : twoValProfile n (k + 1) h i = h := by
              simp only [twoValProfile, hi, ↓reduceIte]
            rw [(symm_eq_of_bid_eq hSym hbk10 (hbi1.trans hbik1.symm)).2]
            exact hpay_ik
  rcases hstep m le_rfl with hleft | hpay
  · exact Or.inl hleft
  · right
    have hbm0 : 0 ≤ twoValProfile n m h := twoValProfile_nonneg n m hh
    calc ∑ i : Fin n, M.payment (twoValProfile n m h) i
        ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
          by_cases hi : i.val < m
          · exact hpay i hi
          · have hbi : twoValProfile n m h i = 1 := by
              simp only [twoValProfile, hi, ↓reduceIte]
            exact (payment_le_bid_of_isBinary hIR hBin hbm0 i).trans_eq hbi
      _ = (n : ℝ) := by
          simp only [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

private theorem natCast_le_singlePriceProfitOn_twoVal {n k r : ℕ} (hr : r ≤ n) {h : ℝ}
    (hh : 1 ≤ h) :
    (n : ℝ) ≤ singlePriceProfitOn r (univ : Finset (Fin n)) (twoValProfile n k h) := by
  have hle := mul_card_le_singlePriceProfitOn (m := r) (s := univ) (W := univ)
    (b := twoValProfile n k h) (p := 1)
    (fun i _ => twoValProfile_nonneg n k hh i) subset_rfl
    (by simpa only [card_univ, Fintype.card_fin] using hr)
    fun i _ => (twoValProfile_bounds n k hh i).1
  simpa only [card_univ, Fintype.card_fin, one_mul] using hle

private theorem mul_le_singlePriceProfitOn_twoVal {n m r : ℕ} (hrm : r ≤ m) (hmn : m ≤ n)
    {h : ℝ} (hh : 1 ≤ h) :
    (m : ℝ) * h ≤ singlePriceProfitOn r (univ : Finset (Fin n)) (twoValProfile n m h) := by
  let W : Finset (Fin n) := univ.filter fun i => i.val < m
  have hWcard : W.card = m := card_filter_val_lt hmn
  have hle := mul_card_le_singlePriceProfitOn (m := r) (s := univ) (W := W)
    (b := twoValProfile n m h) (p := h)
    (fun i _ => twoValProfile_nonneg n m hh i) (subset_univ _) (hWcard ▸ hrm)
    fun i hi => by
      simp only [twoValProfile, (mem_filter.1 hi).2, ↓reduceIte, le_refl]
  rw [hWcard, mul_comm] at hle
  exact hle

/-- **Exact `n`-bidder lower bound for symmetric deterministic auctions** ([HartlineKarlin2007],
§13.4.2, Corollary 13.35, p. 345): on any finite bidder type with `n ≥ 2` bidders, every symmetric
deterministic (`IsBinary`) DSIC, IR digital goods auction has competitive ratio at least `n`
against `ℱ⁽²⁾`. -/
theorem card_le_of_isCompetitive_symmetric {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) {M : Mechanism ι} (hDSIC : M.IsDSIC) (hIR : M.IsIR)
    (hBin : IsBinary M.allocation) (hSym : IsSymmetric M) {β : ℝ}
    (hComp : IsCompetitive optimalProfitTwo (fun b => ∑ i, M.payment b i) β) :
    (Fintype.card ι : ℝ) ≤ β := by
  set n := Fintype.card ι
  let e : Fin n ≃ ι := (Fintype.equivFin ι).symm
  let M' : Mechanism (Fin n) := reindexMechanism e M
  have hDSIC' : M'.IsDSIC := reindexMechanism_isDSIC e hDSIC
  have hIR' : M'.IsIR := reindexMechanism_isIR e hIR
  have hBin' : IsBinary M'.allocation := reindexMechanism_isBinary e hBin
  have hSym' : IsSymmetric M' := reindexMechanism_isSymmetric e hSym
  have hComp' : IsCompetitive optimalProfitTwo (fun b => ∑ i, M'.payment b i) β :=
    reindexMechanism_isCompetitive e hComp
  set h : ℝ := max 1 (β * (n : ℝ) + 1)
  have hh1 : 1 ≤ h := le_max_left _ _
  have hhn : β * (n : ℝ) + 1 ≤ h := le_max_right _ _
  rcases symmetric_twoVal_dichotomy hcard hh1 hDSIC' hIR' hBin' hSym' with ⟨k, hk2, hsum⟩ | hsum
  · have hbench : (n : ℝ) ≤ optimalProfitTwo (twoValProfile n k h) :=
      natCast_le_singlePriceProfitOn_twoVal hcard hh1
    have hcompk := hComp'.2 (twoValProfile n k h) (twoValProfile_nonneg n k hh1)
    have hle : (n : ℝ) ≤ β * (k : ℝ) :=
      hbench.trans (hcompk.trans (mul_le_mul_of_nonneg_left hsum hComp'.1))
    interval_cases k
    · norm_num at hle
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcard
      linarith
    · simpa only [Nat.cast_one, mul_one] using hle
  · have hbench : (2 : ℝ) * h ≤ optimalProfitTwo (twoValProfile n 2 h) := by
      simpa only [Nat.cast_ofNat] using mul_le_singlePriceProfitOn_twoVal le_rfl hcard hh1
    have hcomp2 := hComp'.2 (twoValProfile n 2 h) (twoValProfile_nonneg n 2 hh1)
    have hle : (2 : ℝ) * h ≤ β * (n : ℝ) :=
      hbench.trans (hcomp2.trans (mul_le_mul_of_nonneg_left hsum hComp'.1))
    have hbn0 : 0 ≤ β * (n : ℝ) := mul_nonneg hComp'.1 (Nat.cast_nonneg _)
    linarith

/-- **Corollary 13.35** ([HartlineKarlin2007], §13.4.2, p. 345): no uniform constant `β` is a
competitive ratio against `ℱ⁽²⁾` for symmetric deterministic truthful digital goods auctions across
all `n ≥ 2`. -/
theorem not_exists_const_competitive_symmetric :
    ¬ ∃ β : ℝ, ∀ n : ℕ, 2 ≤ n →
      ∃ M : Mechanism (Fin n), M.IsDSIC ∧ M.IsIR ∧ IsBinary M.allocation ∧ IsSymmetric M ∧
        IsCompetitive optimalProfitTwo (fun b => ∑ i, M.payment b i) β := by
  rintro ⟨β, hβ⟩
  set n : ℕ := max 2 (⌊max β 0⌋₊ + 1)
  obtain ⟨M, hDSIC, hIR, hBin, hSym, hComp⟩ := hβ n (le_max_left _ _)
  have hle : (n : ℝ) ≤ β := by
    simpa only [Fintype.card_fin] using
      card_le_of_isCompetitive_symmetric (by simpa only [Fintype.card_fin] using le_max_left 2 _)
        hDSIC hIR hBin hSym hComp
  have hlt : max β 0 < (n : ℝ) :=
    lt_of_lt_of_le (Nat.lt_floor_add_one _) (by exact_mod_cast le_max_right 2 (⌊max β 0⌋₊ + 1))
  linarith [le_max_left β 0]

/-- **Theorem 13.24** ([HartlineKarlin2007], §13.3.1, p. 341): for every multiplicative factor
`β > 0` and additive coefficient `γ : ℝ`, there exist a bidder count `n ≥ 2` and upper bid bound
`h ≥ 1` such that every symmetric deterministic (`IsBinary`) DSIC, IR digital goods auction on
`Fin n` fails `optimalProfit b / β - h * γ ≤ ∑ i, M.payment b i` on some profile in `[1, h]ⁿ`. -/
theorem exists_not_approx_symmetric_deterministic {β : ℝ} (hβ : 0 < β) (γ : ℝ) :
    ∃ n : ℕ, 2 ≤ n ∧ ∃ h : ℝ, 1 ≤ h ∧
      ∀ M : Mechanism (Fin n), M.IsDSIC → M.IsIR → IsBinary M.allocation → IsSymmetric M →
        ∃ b : Fin n → ℝ, (∀ i, 1 ≤ b i ∧ b i ≤ h) ∧
          ∑ i, M.payment b i < optimalProfit b / β - h * γ := by
  set γ' : ℝ := max γ 0
  have hγ'0 : 0 ≤ γ' := le_max_right γ 0
  have hγle : γ ≤ γ' := le_max_left γ 0
  set m : ℕ := max 2 ⌈β * ((1 + β) * γ' + 1)⌉₊
  have hm2 : 2 ≤ m := le_max_left _ _
  have hm_ge : β * ((1 + β) * γ' + 1) ≤ (m : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 2 _)
  have hslope : 1 ≤ (m : ℝ) / β - γ' - β * γ' := by
    have hdiv : (1 + β) * γ' + 1 ≤ (m : ℝ) / β := (le_div_iff₀ hβ).2 (by linarith)
    linarith
  set h : ℝ := max 1 (β * (m : ℝ) + (m : ℝ) + 2)
  have hh1 : 1 ≤ h := le_max_left _ _
  have hh_big : β * (m : ℝ) + (m : ℝ) + 2 ≤ h := le_max_right _ _
  set n : ℕ := max m (⌊β * ((m : ℝ) + h * γ')⌋₊ + 1) with hn
  have hmn : m ≤ n := le_max_left _ _
  have hn2 : 2 ≤ n := hm2.trans hmn
  have hfloor_lt : β * ((m : ℝ) + h * γ') < (n : ℝ) :=
    lt_of_lt_of_le (Nat.lt_floor_add_one _) (by exact_mod_cast le_max_right m _)
  have hn_lt_hi : (n : ℝ) < h * ((m : ℝ) / β - γ') := by
    have hgap : β * ((m : ℝ) + h * γ') + (m : ℝ) + 2 ≤ h * ((m : ℝ) / β - γ') := by
      have h1 : h ≤ h * ((m : ℝ) / β - γ' - β * γ') := by nlinarith
      nlinarith
    have hnonneg : 0 ≤ β * ((m : ℝ) + h * γ') := by positivity
    have hn_le : (n : ℝ) ≤ β * ((m : ℝ) + h * γ') + (m : ℝ) + 1 := by
      rcases max_cases m (⌊β * ((m : ℝ) + h * γ')⌋₊ + 1) with ⟨hEq, _⟩ | ⟨hEq, _⟩
      · rw [hn, hEq]; linarith
      · rw [hn, hEq]; push_cast
        have hfl : (⌊β * ((m : ℝ) + h * γ')⌋₊ : ℝ) ≤ β * ((m : ℝ) + h * γ') :=
          Nat.floor_le hnonneg
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
        linarith
    linarith
  refine ⟨n, hn2, h, hh1, fun M hDSIC hIR hBin hSym => ?_⟩
  rcases symmetric_twoVal_dichotomy hmn hh1 hDSIC hIR hBin hSym with ⟨k, hkm, hsum⟩ | hsum
  · refine ⟨twoValProfile n k h, twoValProfile_bounds n k hh1, ?_⟩
    have hbench : (n : ℝ) ≤ optimalProfit (twoValProfile n k h) :=
      natCast_le_singlePriceProfitOn_twoVal (by omega) hh1
    have hkmR : (k : ℝ) < (m : ℝ) := by exact_mod_cast hkm
    have hm_lt : (m : ℝ) < (n : ℝ) / β - h * γ' := by
      have h1 : (m : ℝ) + h * γ' < (n : ℝ) / β := (lt_div_iff₀ hβ).2 (by linarith)
      linarith
    have hdiv_le : (n : ℝ) / β ≤ optimalProfit (twoValProfile n k h) / β :=
      div_le_div_of_nonneg_right hbench hβ.le
    have hγh : h * γ ≤ h * γ' := mul_le_mul_of_nonneg_left hγle (by linarith)
    linarith
  · refine ⟨twoValProfile n m h, twoValProfile_bounds n m hh1, ?_⟩
    have hbench : (m : ℝ) * h ≤ optimalProfit (twoValProfile n m h) :=
      mul_le_singlePriceProfitOn_twoVal (by omega) hmn hh1
    have hdiv_le : (m : ℝ) * h / β ≤ optimalProfit (twoValProfile n m h) / β :=
      div_le_div_of_nonneg_right hbench hβ.le
    have hγh : h * γ ≤ h * γ' := mul_le_mul_of_nonneg_left hγle (by linarith)
    have hrw : h * ((m : ℝ) / β - γ') = (m : ℝ) * h / β - h * γ' := by ring
    linarith

/-! ### Tight symmetric deterministic auction (`symmetricSecondPrice`) -/

section SymmetricSecondPrice

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
/-- Highest bid among bidders other than `i`, clamped below at `0`. -/
private noncomputable def maxOtherBid (b : ι → ℝ) (i : ι) : ℝ :=
  (univ.erase i).fold max 0 b

private theorem maxOtherBid_nonneg (b : ι → ℝ) (i : ι) : 0 ≤ maxOtherBid b i :=
  (Finset.le_fold_max _).2 (Or.inl le_rfl)

private theorem le_maxOtherBid {b : ι → ℝ} {i j : ι} (hj : j ≠ i) : b j ≤ maxOtherBid b i :=
  (Finset.le_fold_max _).2 (Or.inr ⟨j, mem_erase.2 ⟨hj, mem_univ j⟩, le_rfl⟩)

private theorem maxOtherBid_le_iff {b : ι → ℝ} {i : ι} {c : ℝ} :
    maxOtherBid b i ≤ c ↔ 0 ≤ c ∧ ∀ j, j ≠ i → b j ≤ c := by
  simp only [maxOtherBid, Finset.fold_max_le, mem_erase, mem_univ, and_true]

private theorem maxOtherBid_update (b : ι → ℝ) (i : ι) (z : ℝ) :
    maxOtherBid (Function.update b i z) i = maxOtherBid b i :=
  Finset.fold_congr fun _ hj => Function.update_of_ne (ne_of_mem_erase hj) _ _

private theorem maxOtherBid_comp_perm (σ : Equiv.Perm ι) (b : ι → ℝ) (i : ι) :
    maxOtherBid (b ∘ σ) i = maxOtherBid b (σ i) := by
  apply le_antisymm
  · refine maxOtherBid_le_iff.2 ⟨maxOtherBid_nonneg b (σ i), fun j hj => ?_⟩
    exact le_maxOtherBid (fun h => hj (σ.injective h))
  · refine maxOtherBid_le_iff.2 ⟨maxOtherBid_nonneg (b ∘ σ) i, fun j hj => ?_⟩
    have hne : σ.symm j ≠ i := fun h => hj (by rw [← h, Equiv.apply_symm_apply])
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      le_maxOtherBid (b := b ∘ σ) hne

open Classical in
/-- The **symmetric second-price digital goods auction**: every bidder `i` whose bid is at least
the highest other bid (`max 0 (max_{j ≠ i} b j)`) receives one copy and pays that threshold; all
other bidders receive `0` and pay `0`. On `n ≥ 2` bidders this is symmetric, deterministic, DSIC,
IR, normalized, and achieves the optimal symmetric deterministic competitive ratio `n` against
`ℱ⁽²⁾` (in particular `2` for `n = 2`, matching [HartlineKarlin2007], §13.4.3, p. 347). -/
@[expose] noncomputable def symmetricSecondPrice : Mechanism ι where
  allocation b i := if (univ.erase i).fold max 0 b ≤ b i then 1 else 0
  payment b i := if (univ.erase i).fold max 0 b ≤ b i then (univ.erase i).fold max 0 b else 0

private theorem symmetricSecondPrice_allocation_eq (b : ι → ℝ) (i : ι) :
    symmetricSecondPrice.allocation b i = if maxOtherBid b i ≤ b i then 1 else 0 :=
  rfl

private theorem symmetricSecondPrice_payment_eq (b : ι → ℝ) (i : ι) :
    symmetricSecondPrice.payment b i = if maxOtherBid b i ≤ b i then maxOtherBid b i else 0 :=
  rfl

theorem symmetricSecondPrice_isBinary : IsBinary (symmetricSecondPrice (ι := ι)).allocation :=
  fun b _ i => by
    rw [symmetricSecondPrice_allocation_eq]
    split_ifs <;> simp

theorem symmetricSecondPrice_isSymmetric : IsSymmetric (symmetricSecondPrice (ι := ι)) := by
  intro σ b i _
  simp only [symmetricSecondPrice_allocation_eq, symmetricSecondPrice_payment_eq,
    maxOtherBid_comp_perm, Function.comp_apply, and_self]

theorem symmetricSecondPrice_isDSIC : (symmetricSecondPrice (ι := ι)).IsDSIC := by
  intro i b v _ _
  simp only [Mechanism.utility, symmetricSecondPrice_allocation_eq, symmetricSecondPrice_payment_eq,
    maxOtherBid_update, Function.update_self]
  split_ifs with h1 h2 <;> linarith

theorem symmetricSecondPrice_isIR : (symmetricSecondPrice (ι := ι)).IsIR := by
  intro i b _
  simp only [Mechanism.utility, symmetricSecondPrice_allocation_eq, symmetricSecondPrice_payment_eq]
  split_ifs with h <;> linarith

theorem symmetricSecondPrice_isNormalized : (symmetricSecondPrice (ι := ι)).IsNormalized := by
  intro i b _
  simp only [symmetricSecondPrice_payment_eq, maxOtherBid_update, Function.update_self]
  split_ifs with h
  · exact le_antisymm h (maxOtherBid_nonneg b i)
  · rfl

/-- `symmetricSecondPrice` is `|ι|`-competitive against `ℱ⁽²⁾` for every finite bidder type. -/
theorem symmetricSecondPrice_isCompetitive :
    IsCompetitive (optimalProfitTwo (ι := ι))
      (fun b => ∑ i, symmetricSecondPrice.payment b i) (Fintype.card ι) := by
  refine ⟨Nat.cast_nonneg _, fun b hb => ?_⟩
  rcases lt_or_ge (Fintype.card ι) 2 with hlt | hcard
  · dsimp only [optimalProfitTwo]
    rw [singlePriceProfitOn_eq_zero_of_card_lt b ((card_univ (α := ι)).symm ▸ hlt)]
    refine mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => ?_)
    rw [symmetricSecondPrice_payment_eq]
    split_ifs
    · exact maxOtherBid_nonneg b i
    · exact le_rfl
  · have hne : (univ : Finset ι).Nonempty := Finset.card_pos.1 (by rw [card_univ]; omega)
    obtain ⟨imax, -, himax⟩ := univ.exists_max_image b hne
    have hwin_max : maxOtherBid b imax ≤ b imax :=
      maxOtherBid_le_iff.2 ⟨hb imax, fun j _ => himax j (mem_univ j)⟩
    have hpay_ge : maxOtherBid b imax ≤ ∑ i : ι, symmetricSecondPrice.payment b i := by
      have hnonneg : ∀ i ∈ (univ : Finset ι), 0 ≤ symmetricSecondPrice.payment b i := fun i _ => by
        rw [symmetricSecondPrice_payment_eq]
        split_ifs
        · exact maxOtherBid_nonneg b i
        · exact le_rfl
      have hsingle := Finset.single_le_sum hnonneg (mem_univ imax)
      simpa only [symmetricSecondPrice_payment_eq, hwin_max, ↓reduceIte] using hsingle
    refine singlePriceProfitOn_le (mul_nonneg (Nat.cast_nonneg _)
        ((maxOtherBid_nonneg b imax).trans hpay_ge)) fun j _ hj => ?_
    have hcard_le : ((univ.filter fun i => b j ≤ b i).card : ℝ) ≤ (Fintype.card ι : ℝ) := by
      exact_mod_cast (card_filter_le (univ : Finset ι) _).trans_eq card_univ
    have hex_ne : ∃ k : ι, k ≠ imax ∧ b j ≤ b k := by
      have hsub : 1 ≤ ((univ.filter fun i => b j ≤ b i).erase imax).card := by
        have := card_erase_le (s := univ.filter fun i => b j ≤ b i) (a := imax)
        by_cases hm : imax ∈ univ.filter fun i => b j ≤ b i
        · rw [card_erase_of_mem hm]; omega
        · rw [erase_eq_of_notMem hm]; omega
      obtain ⟨k, hk⟩ := Finset.card_pos.1 hsub
      exact ⟨k, (mem_erase.1 hk).1, (mem_filter.1 (mem_erase.1 hk).2).2⟩
    obtain ⟨k, hkne, hjk⟩ := hex_ne
    have hbj_le : b j ≤ maxOtherBid b imax := hjk.trans (le_maxOtherBid hkne)
    calc b j * ((univ.filter fun i => b j ≤ b i).card : ℝ)
        ≤ maxOtherBid b imax * (Fintype.card ι : ℝ) :=
          mul_le_mul hbj_le hcard_le (Nat.cast_nonneg _) (maxOtherBid_nonneg b imax)
      _ = (Fintype.card ι : ℝ) * maxOtherBid b imax := mul_comm _ _
      _ ≤ (Fintype.card ι : ℝ) * ∑ i, symmetricSecondPrice.payment b i :=
          mul_le_mul_of_nonneg_left hpay_ge (Nat.cast_nonneg _)

/-- For every finite bidder type with `n ≥ 2` bidders, the competitive ratio of
`symmetricSecondPrice` with respect to `ℱ⁽²⁾` is **exactly `n`** (in particular `2` for `n = 2`,
showing tightness of both Corollary 13.35 and Lemma 13.38). -/
theorem isLeast_symmetricSecondPrice_competitiveRatio (hcard : 2 ≤ Fintype.card ι) :
    IsLeast
      {β : ℝ | IsCompetitive (optimalProfitTwo (ι := ι))
        (fun b => ∑ i, symmetricSecondPrice.payment b i) β}
      (Fintype.card ι : ℝ) :=
  ⟨symmetricSecondPrice_isCompetitive, fun _ hβ =>
    card_le_of_isCompetitive_symmetric hcard symmetricSecondPrice_isDSIC
      symmetricSecondPrice_isIR symmetricSecondPrice_isBinary
      symmetricSecondPrice_isSymmetric hβ⟩

end SymmetricSecondPrice

end SymmetricDeterministic

/-! ### Randomized competitive lower bounds
(`Lemma 13.38`, `13 / 6` for `n = 3`, `Exercise 13.8`) -/

section RandomizedLowerBounds

/-- Grid points `z_j = (m + j) / m` for `0 ≤ j ≤ N`, starting at `z_0 = 1` with step `1 / m`. -/
private noncomputable def gridVal (m : ℕ) (j : ℕ) : ℝ :=
  ((m + j : ℕ) : ℝ) / (m : ℝ)

/-- Discrete equal-revenue weights on `Fin (N + 1)` with tail probability
`Pr[X ≥ z_j] = 1 / z_j = m / (m + j)`. -/
private noncomputable def equalRevWeight (m N : ℕ) (j : Fin (N + 1)) : ℝ :=
  if j.val < N then
    1 / gridVal m j.val - 1 / gridVal m (j.val + 1)
  else
    1 / gridVal m N

private theorem gridVal_pos {m : ℕ} (hm : 0 < m) (j : ℕ) : 0 < gridVal m j := by
  unfold gridVal
  positivity

private theorem gridVal_zero {m : ℕ} (hm : 0 < m) : gridVal m 0 = 1 := by
  unfold gridVal
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [add_zero, div_self hm']

private theorem gridVal_mono {m : ℕ} {j k : ℕ} (hjk : j ≤ k) :
    gridVal m j ≤ gridVal m k := by
  unfold gridVal
  exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.add_le_add_left hjk m)
    (Nat.cast_nonneg m)

private theorem equalRevWeight_nonneg {m : ℕ} (hm : 0 < m) (N : ℕ) (j : Fin (N + 1)) :
    0 ≤ equalRevWeight m N j := by
  unfold equalRevWeight
  split_ifs with hj
  · have hle : 1 / gridVal m (j.val + 1) ≤ 1 / gridVal m j.val :=
      one_div_le_one_div_of_le (gridVal_pos hm j.val) (gridVal_mono (Nat.le_succ _))
    linarith
  · exact div_nonneg zero_le_one (gridVal_pos hm N).le

private theorem sum_equalRevWeight_tail {m : ℕ} (N k : ℕ) (hk : k ≤ N) :
    ∑ j ∈ (univ : Finset (Fin (N + 1))).filter (fun j => k ≤ j.val), equalRevWeight m N j =
      1 / gridVal m k := by
  have hbij : ∑ j ∈ (univ : Finset (Fin (N + 1))).filter (fun j => k ≤ j.val),
        equalRevWeight m N j =
      ∑ j ∈ Finset.Icc k N,
        (if j < N then 1 / gridVal m j - 1 / gridVal m (j + 1) else 1 / gridVal m N) := by
    refine Finset.sum_bij (fun j _ => j.val)
      (fun j hj => mem_Icc.2 ⟨(mem_filter.1 hj).2, Nat.lt_succ_iff.1 j.isLt⟩)
      (fun _ _ _ _ h => Fin.ext h)
      (fun j hj => ⟨⟨j, Nat.lt_succ_of_le (mem_Icc.1 hj).2⟩,
        mem_filter.2 ⟨mem_univ _, (mem_Icc.1 hj).1⟩, rfl⟩)
      (fun _ _ => rfl)
  rw [hbij, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_succ_top hk]
  simp only [lt_self_iff_false, ↓reduceIte]
  have hsum : (∑ j ∈ Finset.Ico k N,
      if j < N then 1 / gridVal m j - 1 / gridVal m (j + 1) else 1 / gridVal m N) =
      ∑ j ∈ Finset.Ico k N, (1 / gridVal m j - 1 / gridVal m (j + 1)) :=
    Finset.sum_congr rfl fun j hj => ite_eq_left (Finset.mem_Ico.1 hj).2
  have htel : (∑ j ∈ Finset.Ico k N, (1 / gridVal m j - 1 / gridVal m (j + 1))) =
      1 / gridVal m k - 1 / gridVal m N := by
    simpa only [neg_sub_neg] using Finset.sum_Ico_sub (fun j => -(1 / gridVal m j)) hk
  rw [hsum, htel, sub_add_cancel]

private theorem sum_equalRevWeight {m : ℕ} (hm : 0 < m) (N : ℕ) :
    ∑ j : Fin (N + 1), equalRevWeight m N j = 1 := by
  have hfilt : (univ : Finset (Fin (N + 1))).filter (fun j => 0 ≤ j.val) = univ :=
    filter_true_of_mem fun _ _ => Nat.zero_le _
  rw [← hfilt, sum_equalRevWeight_tail N 0 (Nat.zero_le N), gridVal_zero hm, div_one]

/-- Summation by parts on `Fin (N + 1)`: for any `a, p : ℕ → ℝ`,
`∑_{j < N} (a j - a (j + 1)) p j + a N p N = a 0 p 0 + ∑_{j < N} a (j + 1) (p (j + 1) - p j)`. -/
private theorem abel_sum_equalRev (a p : ℕ → ℝ) (N : ℕ) :
    ∑ j : Fin (N + 1), (if j.val < N then a j.val - a (j.val + 1) else a N) * p j.val =
      a 0 * p 0 + ∑ j ∈ Finset.range N, a (j + 1) * (p (j + 1) - p j) := by
  rw [Fin.sum_univ_castSucc]
  have hlt (j : Fin N) : j.val < N := j.isLt
  simp only [Fin.val_castSucc, Fin.val_last, hlt, lt_self_iff_false, ↓reduceIte]
  rw [Fin.sum_univ_eq_sum_range (fun j => (a j - a (j + 1)) * p j)]
  have hshift := (Finset.sum_range_succ' (fun j => a j * p j) N).symm.trans
    (Finset.sum_range_succ (fun j => a j * p j) N)
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  linarith

/-- One-bidder expectation bound on the fine equal-revenue grid: fixing nonnegative `b_{-i}`,
for any DSIC, IR, `[0, 1]`-allocated mechanism `M`, the expected payment of bidder `i` under
`equalRevWeight m N` is at most `1`. -/
private theorem single_bidder_expected_payment_le_one {ι : Type*} [DecidableEq ι]
    {M : Mechanism ι} (hDSIC : M.IsDSIC) (hIR : M.IsIR) (hUnit : IsUnitAlloc M.allocation)
    {m : ℕ} (hm : 0 < m) (N : ℕ) (i : ι) {b : ι → ℝ} (hb : 0 ≤ b) :
    ∑ k : Fin (N + 1),
        equalRevWeight m N k * M.payment (Function.update b i (gridVal m k.val)) i ≤ 1 := by
  let x : ℕ → ℝ := fun k => M.allocation (Function.update b i (gridVal m k)) i
  let p : ℕ → ℝ := fun k => M.payment (Function.update b i (gridVal m k)) i
  have hsum_eq :
      ∑ k : Fin (N + 1),
          equalRevWeight m N k * M.payment (Function.update b i (gridVal m k.val)) i =
        (1 / gridVal m 0) * p 0 +
          ∑ j ∈ Finset.range N, (1 / gridVal m (j + 1)) * (p (j + 1) - p j) := by
    simpa only [equalRevWeight, p] using abel_sum_equalRev (fun k => 1 / gridVal m k) p N
  rw [hsum_eq]
  have hp0 : (1 / gridVal m 0) * p 0 ≤ x 0 := by
    rw [gridVal_zero hm, div_one, one_mul]
    have h0_ir := hIR i (Function.update b i 0) (update_nonneg hb i le_rfl)
    simp only [Mechanism.utility, Function.update_self, zero_mul, zero_sub] at h0_ir
    have hx0_nonneg : 0 ≤ M.allocation (Function.update b i 0) i :=
      (hUnit _ (update_nonneg hb i le_rfl) i).1
    have hdsic := hDSIC.utility_update_le i hb (gridVal_pos hm 0).le le_rfl
    rw [gridVal_zero hm, one_mul, one_mul] at hdsic
    dsimp only [p, x]
    rw [gridVal_zero hm]
    linarith
  have hstep : ∀ j ∈ Finset.range N,
      (1 / gridVal m (j + 1)) * (p (j + 1) - p j) ≤ x (j + 1) - x j := by
    intro j _
    have hpos : 0 < gridVal m (j + 1) := gridVal_pos hm (j + 1)
    have hdsic := hDSIC.utility_update_le i hb hpos.le (gridVal_pos hm j).le
    have hdiff : p (j + 1) - p j ≤ gridVal m (j + 1) * (x (j + 1) - x j) := by
      dsimp only [p, x]; linarith
    calc (1 / gridVal m (j + 1)) * (p (j + 1) - p j)
        ≤ (1 / gridVal m (j + 1)) * (gridVal m (j + 1) * (x (j + 1) - x j)) :=
          mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = x (j + 1) - x j := by field_simp [hpos.ne']
  have htele : ∑ j ∈ Finset.range N, (x (j + 1) - x j) = x N - x 0 :=
    Finset.sum_range_sub x N
  have hxN : x N ≤ 1 := (hUnit _ (update_nonneg hb i (gridVal_pos hm N).le) i).2
  calc (1 / gridVal m 0) * p 0 +
        ∑ j ∈ Finset.range N, (1 / gridVal m (j + 1)) * (p (j + 1) - p j)
      ≤ x 0 + ∑ j ∈ Finset.range N, (x (j + 1) - x j) :=
        add_le_add hp0 (Finset.sum_le_sum hstep)
    _ = x N := by rw [htele]; ring
    _ ≤ 1 := hxN

/-- **General `n`-bidder equal-revenue expectation bound**: under the i.i.d. product of the fine
equal-revenue grid distribution `equalRevWeight m N`, every DSIC, IR, `[0, 1]`-allocated
mechanism on `ι` has expected total payment at most `|ι|`. -/
private theorem expected_sum_payment_equalRevGrid_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Mechanism ι} (hDSIC : M.IsDSIC) (hIR : M.IsIR) (hUnit : IsUnitAlloc M.allocation)
    {m : ℕ} (hm : 0 < m) (N : ℕ) :
    ∑ c : ι → Fin (N + 1), (∏ j : ι, equalRevWeight m N (c j)) *
        (∑ i : ι, M.payment (fun j => gridVal m (c j).val) i) ≤
      (Fintype.card ι : ℝ) := by
  have hswap :
      ∑ c : ι → Fin (N + 1), (∏ j : ι, equalRevWeight m N (c j)) *
          (∑ i : ι, M.payment (fun j => gridVal m (c j).val) i) =
        ∑ i : ι, ∑ c : ι → Fin (N + 1),
          (∏ j : ι, equalRevWeight m N (c j)) * M.payment (fun j => gridVal m (c j).val) i := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  rw [hswap]
  calc ∑ i : ι, ∑ c : ι → Fin (N + 1),
          (∏ j : ι, equalRevWeight m N (c j)) * M.payment (fun j => gridVal m (c j).val) i
      ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => ?_
    _ = (Fintype.card ι : ℝ) := by simp only [Finset.sum_const, card_univ, nsmul_eq_mul, mul_one]
  let eSplit : (ι → Fin (N + 1)) ≃ Fin (N + 1) × ({j : ι // j ≠ i} → Fin (N + 1)) :=
    Equiv.piSplitAt i (fun _ => Fin (N + 1))
  rw [← eSplit.symm.sum_comp, Fintype.sum_prod_type_right]
  have hprod : ∀ (rest : {j : ι // j ≠ i} → Fin (N + 1)) (k : Fin (N + 1)),
      ∏ j : ι, equalRevWeight m N (eSplit.symm (k, rest) j) =
        (∏ j : {j : ι // j ≠ i}, equalRevWeight m N (rest j)) * equalRevWeight m N k := by
    intro rest k
    rw [← Finset.mul_prod_erase univ _ (mem_univ i), mul_comm]
    congr 1
    · refine Finset.prod_bij (fun j hj => ⟨j, (mem_erase.1 hj).1⟩)
        (fun _ _ => mem_univ _)
        (fun _ _ _ _ h => congrArg Subtype.val h)
        (fun j _ => ⟨j.1, mem_erase.2 ⟨j.2, mem_univ _⟩, rfl⟩)
        fun j hj => by
          dsimp only [eSplit]
          rw [Equiv.piSplitAt_symm_apply, dite_eq_right (mem_erase.1 hj).1]
    · dsimp only [eSplit]
      rw [Equiv.piSplitAt_symm_apply, dite_eq_left rfl]
  have hupd : ∀ (rest : {j : ι // j ≠ i} → Fin (N + 1)) (k : Fin (N + 1)),
      (fun j => gridVal m (eSplit.symm (k, rest) j).val) =
        Function.update
          (fun j => if h : j = i then 1 else gridVal m (rest ⟨j, h⟩).val)
          i (gridVal m k.val) := by
    intro rest k
    ext j
    by_cases hj : j = i
    · subst hj
      simp only [eSplit, Equiv.piSplitAt_symm_apply, Function.update_self, ↓reduceDIte]
    · simp only [eSplit, Equiv.piSplitAt_symm_apply, Function.update_of_ne hj, hj, ↓reduceDIte]
  have hrest_nonneg : ∀ rest : {j : ι // j ≠ i} → Fin (N + 1),
      0 ≤ ∏ j : {j : ι // j ≠ i}, equalRevWeight m N (rest j) :=
    fun rest => Finset.prod_nonneg fun j _ => equalRevWeight_nonneg hm N (rest j)
  calc ∑ rest : {j : ι // j ≠ i} → Fin (N + 1), ∑ k : Fin (N + 1),
        (∏ j : ι, equalRevWeight m N (eSplit.symm (k, rest) j)) *
          M.payment (fun j => gridVal m (eSplit.symm (k, rest) j).val) i
      = ∑ rest : {j : ι // j ≠ i} → Fin (N + 1),
          (∏ j : {j : ι // j ≠ i}, equalRevWeight m N (rest j)) *
            ∑ k : Fin (N + 1), equalRevWeight m N k *
              M.payment (Function.update
                (fun j => if h : j = i then 1 else gridVal m (rest ⟨j, h⟩).val)
                i (gridVal m k.val)) i := by
        refine Finset.sum_congr rfl fun rest _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hprod rest k, hupd rest k, mul_assoc]
    _ ≤ ∑ rest : {j : ι // j ≠ i} → Fin (N + 1),
          (∏ j : {j : ι // j ≠ i}, equalRevWeight m N (rest j)) * 1 := by
        refine Finset.sum_le_sum fun rest _ =>
          mul_le_mul_of_nonneg_left
            (single_bidder_expected_payment_le_one hDSIC hIR hUnit hm N i fun j => by
              split_ifs
              · norm_num
              · exact (gridVal_pos hm _).le)
            (hrest_nonneg rest)
    _ = 1 := by
        simp only [mul_one, ← Fintype.prod_sum, sum_equalRevWeight hm N, Finset.prod_const_one]

/-- Telescoping sum `∑_{s ∈ Icc a b} (f s - f (s + 1)) = f a - f (b + 1)` for `a ≤ b`. -/
private theorem sum_Icc_sub_succ (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ s ∈ Finset.Icc a b, (f s - f (s + 1)) = f a - f (b + 1) := by
  simpa only [neg_sub_neg] using Finset.sum_Icc_sub hab (fun j => -f j)

/-- Index shift `∑ r ∈ Icc a b, f (r + d) = ∑ s ∈ Icc (a + d) (b + d), f s`. -/
private theorem sum_Icc_shift_add (a b d : ℕ) (f : ℕ → ℝ) :
    ∑ r ∈ Finset.Icc a b, f (r + d) = ∑ s ∈ Finset.Icc (a + d) (b + d), f s := by
  rw [← Finset.map_add_right_Icc, Finset.sum_map]
  rfl

/-- Product equal-revenue weights sum to `1`. -/
private theorem sum_prod_equalRevWeight {n m N : ℕ} (hm : 0 < m) :
    ∑ c : Fin n → Fin (N + 1), (∏ j : Fin n, equalRevWeight m N (c j)) = 1 := by
  rw [← Fintype.prod_sum]
  simp only [sum_equalRevWeight hm N, Finset.prod_const_one]

/-- Pointwise lower bound by an affine sum of indicators lifts to an expectation lower bound over
the product equal-revenue grid. -/
private theorem expected_add_sum_indicator_le {n m N : ℕ} (hm : 0 < m) (a d : ℝ) (S : Finset ℕ)
    (P : ℕ → (Fin n → Fin (N + 1)) → Prop) [∀ r c, Decidable (P r c)]
    {f : (Fin n → Fin (N + 1)) → ℝ}
    (hf : ∀ c, a + d * ∑ r ∈ S, (if P r c then (1 : ℝ) else 0) ≤ f c) :
    a + d * ∑ r ∈ S, ∑ c : Fin n → Fin (N + 1), (∏ j : Fin n, equalRevWeight m N (c j)) *
        (if P r c then (1 : ℝ) else 0) ≤
      ∑ c : Fin n → Fin (N + 1), (∏ j : Fin n, equalRevWeight m N (c j)) * f c := by
  have hexp : ∀ c : Fin n → Fin (N + 1),
      (∏ j : Fin n, equalRevWeight m N (c j)) *
        (a + d * ∑ r ∈ S, if P r c then (1 : ℝ) else 0) =
      a * (∏ j : Fin n, equalRevWeight m N (c j)) +
        d * ∑ r ∈ S, (∏ j : Fin n, equalRevWeight m N (c j)) *
          (if P r c then (1 : ℝ) else 0) := fun c => by
    rw [← Finset.mul_sum]; ring
  calc a + d * ∑ r ∈ S, ∑ c : Fin n → Fin (N + 1), (∏ j : Fin n, equalRevWeight m N (c j)) *
          (if P r c then (1 : ℝ) else 0)
      = ∑ c : Fin n → Fin (N + 1), (∏ j : Fin n, equalRevWeight m N (c j)) *
          (a + d * ∑ r ∈ S, if P r c then (1 : ℝ) else 0) := by
        simp_rw [hexp, Finset.sum_add_distrib]
        rw [← Finset.mul_sum, sum_prod_equalRevWeight hm, mul_one, ← Finset.mul_sum,
          Finset.sum_comm]
    _ ≤ ∑ c : Fin n → Fin (N + 1), (∏ j : Fin n, equalRevWeight m N (c j)) * f c :=
        Finset.sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_left (hf c)
            (Finset.prod_nonneg fun j _ => equalRevWeight_nonneg hm N (c j))

/-- For any `β`-competitive truthful IR `[0, 1]`-allocated auction on `n` bidders, the expected
benchmark `ℱ⁽²⁾` under the product equal-revenue grid is at most `n * β`. -/
private theorem expected_optimalProfitTwo_equalRevGrid_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hcard : Fintype.card ι = n) {M : Mechanism ι} (hDSIC : M.IsDSIC) (hIR : M.IsIR)
    (hUnit : IsUnitAlloc M.allocation) {β : ℝ}
    (hComp : IsCompetitive optimalProfitTwo (fun b => ∑ i, M.payment b i) β)
    {m : ℕ} (hm : 0 < m) (N : ℕ) :
    ∑ c : Fin n → Fin (N + 1), (∏ j : Fin n, equalRevWeight m N (c j)) *
        optimalProfitTwo (fun j => gridVal m (c j).val) ≤
      (n : ℝ) * β := by
  let e : Fin n ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
  let M' : Mechanism (Fin n) := reindexMechanism e M
  have hDSIC' := reindexMechanism_isDSIC e hDSIC
  have hIR' := reindexMechanism_isIR e hIR
  have hUnit' := reindexMechanism_isUnitAlloc e hUnit
  have hComp' := reindexMechanism_isCompetitive e hComp
  have hexp_pay : ∑ c : Fin n → Fin (N + 1), (∏ j : Fin n, equalRevWeight m N (c j)) *
      (∑ i : Fin n, M'.payment (fun j => gridVal m (c j).val) i) ≤ (n : ℝ) := by
    simpa only [Fintype.card_fin] using
      expected_sum_payment_equalRevGrid_le hDSIC' hIR' hUnit' hm N
  calc ∑ c : Fin n → Fin (N + 1), (∏ j : Fin n, equalRevWeight m N (c j)) *
          optimalProfitTwo (fun j => gridVal m (c j).val)
      ≤ ∑ c : Fin n → Fin (N + 1), (∏ j : Fin n, equalRevWeight m N (c j)) *
          (β * ∑ i : Fin n, M'.payment (fun j => gridVal m (c j).val) i) :=
        Finset.sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_left
            (hComp'.2 (fun j => gridVal m (c j).val) fun j => (gridVal_pos hm _).le)
            (Finset.prod_nonneg fun j _ => equalRevWeight_nonneg hm N (c j))
    _ = β * ∑ c : Fin n → Fin (N + 1), (∏ j : Fin n, equalRevWeight m N (c j)) *
          (∑ i : Fin n, M'.payment (fun j => gridVal m (c j).val) i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => by ring
    _ ≤ β * (n : ℝ) := mul_le_mul_of_nonneg_left hexp_pay hComp'.1
    _ = (n : ℝ) * β := mul_comm β _

/-- Telescoping lower bound `∑_{s ∈ Icc a b} 1 / s² ≥ 1 / a - 1 / (b + 1)` for `1 ≤ a ≤ b`. -/
private theorem sum_inv_sq_ge {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (1 : ℝ) / (a : ℝ) - 1 / ((b + 1 : ℕ) : ℝ) ≤
      ∑ s ∈ Finset.Icc a b, (1 : ℝ) / ((s : ℝ) ^ 2) := by
  rw [← sum_Icc_sub_succ (fun s => (1 : ℝ) / (s : ℝ)) hab]
  refine Finset.sum_le_sum fun s hs => ?_
  have hs1 : 1 ≤ s := ha.trans (mem_Icc.1 hs).1
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs1
  have hs1pos : (0 : ℝ) < ((s + 1 : ℕ) : ℝ) := by positivity
  have hdiff : (1 : ℝ) / (s : ℝ) - 1 / ((s + 1 : ℕ) : ℝ) = 1 / ((s : ℝ) * ((s + 1 : ℕ) : ℝ)) := by
    push_cast
    field_simp
    ring
  rw [hdiff]
  refine one_div_le_one_div_of_le (by positivity) ?_
  push_cast
  nlinarith

/-- Telescoping upper bound `∑_{s ∈ Icc a b} 1 / s³ ≤ 1 / (2 (a - 1) a)` for `2 ≤ a ≤ b`. -/
private theorem sum_inv_cube_le {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∑ s ∈ Finset.Icc a b, (1 : ℝ) / ((s : ℝ) ^ 3) ≤
      1 / (2 * ((a - 1 : ℕ) : ℝ) * (a : ℝ)) := by
  have htele : ∑ s ∈ Finset.Icc a b,
      ((1 : ℝ) / (2 * ((s - 1 : ℕ) : ℝ) * (s : ℝ)) -
        1 / (2 * (s : ℝ) * ((s + 1 : ℕ) : ℝ))) =
      1 / (2 * ((a - 1 : ℕ) : ℝ) * (a : ℝ)) - 1 / (2 * (b : ℝ) * ((b + 1 : ℕ) : ℝ)) := by
    simpa only [Nat.add_sub_cancel] using
      sum_Icc_sub_succ (fun s => (1 : ℝ) / (2 * ((s - 1 : ℕ) : ℝ) * (s : ℝ))) hab
  have hterm : ∀ s ∈ Finset.Icc a b,
      (1 : ℝ) / ((s : ℝ) ^ 3) ≤
        1 / (2 * ((s - 1 : ℕ) : ℝ) * (s : ℝ)) - 1 / (2 * (s : ℝ) * ((s + 1 : ℕ) : ℝ)) := by
    intro s hs
    have hs2 : 2 ≤ s := ha.trans (mem_Icc.1 hs).1
    have hs_sub : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one]
    have hsm1 : (0 : ℝ) < (s : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs2
      linarith
    have hspos : (0 : ℝ) < (s : ℝ) := by linarith
    have hsp1 : (0 : ℝ) < (s : ℝ) + 1 := by linarith
    rw [hs_sub]
    push_cast
    have hdiff : (1 : ℝ) / (2 * ((s : ℝ) - 1) * (s : ℝ)) -
        1 / (2 * (s : ℝ) * ((s : ℝ) + 1)) =
        1 / (((s : ℝ) - 1) * (s : ℝ) * ((s : ℝ) + 1)) := by
      field_simp
      ring
    rw [hdiff]
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith
  have htail_nonneg : 0 ≤ (1 : ℝ) / (2 * (b : ℝ) * ((b + 1 : ℕ) : ℝ)) := by positivity
  calc ∑ s ∈ Finset.Icc a b, (1 : ℝ) / ((s : ℝ) ^ 3)
      ≤ ∑ s ∈ Finset.Icc a b,
          ((1 : ℝ) / (2 * ((s - 1 : ℕ) : ℝ) * (s : ℝ)) -
            1 / (2 * (s : ℝ) * ((s + 1 : ℕ) : ℝ))) := Finset.sum_le_sum hterm
    _ = 1 / (2 * ((a - 1 : ℕ) : ℝ) * (a : ℝ)) - 1 / (2 * (b : ℝ) * ((b + 1 : ℕ) : ℝ)) := htele
    _ ≤ 1 / (2 * ((a - 1 : ℕ) : ℝ) * (a : ℝ)) := by linarith

/-- **Lemma 13.38** ([HartlineKarlin2007], §13.4.3, pp. 346–347): no `2`-bidder truthful
(DSIC and IR, deterministic or truthful-in-expectation randomized) digital goods auction has
competitive ratio less than `2` with respect to `ℱ⁽²⁾`. Tight via `symmetricSecondPrice`. -/
theorem two_le_of_isCompetitive_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 2) {M : Mechanism ι} (hDSIC : M.IsDSIC) (hIR : M.IsIR)
    (hUnit : IsUnitAlloc M.allocation) {β : ℝ}
    (hComp : IsCompetitive optimalProfitTwo (fun b => ∑ i, M.payment b i) β) :
    2 ≤ β := by
  by_contra hlt
  push Not at hlt
  set ε : ℝ := 4 - 2 * β with hε_def
  have hε : 0 < ε := by linarith
  set m : ℕ := ⌈4 / ε⌉₊ + 1
  set H : ℕ := max 2 (⌈4 / ε⌉₊ + 1)
  have hm : 0 < m := Nat.succ_pos _
  have hH2 : 2 ≤ H := le_max_left _ _
  set N : ℕ := m * (H - 1)
  have hm_eps : 2 / ((m + 1 : ℕ) : ℝ) < ε / 2 := by
    have h1 : 4 / ε < ((m + 1 : ℕ) : ℝ) := by
      have : 4 / ε ≤ (⌈4 / ε⌉₊ : ℝ) := Nat.le_ceil _
      push_cast [m]; linarith
    have hm1pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    rw [div_lt_iff₀ hm1pos]
    have := (div_lt_iff₀ hε).1 h1
    linarith
  have hH_eps : 2 / (H : ℝ) < ε / 2 := by
    have h1 : 4 / ε < (H : ℝ) := by
      have hceil : 4 / ε ≤ (⌈4 / ε⌉₊ : ℝ) := Nat.le_ceil _
      have hHge : ((⌈4 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast le_max_right 2 _
      push_cast at hHge; linarith
    have hHpos : (0 : ℝ) < (H : ℝ) := by positivity
    rw [div_lt_iff₀ hHpos]
    have := (div_lt_iff₀ hε).1 h1
    linarith
  have hexp_le : ∑ c : Fin 2 → Fin (N + 1), (∏ j : Fin 2, equalRevWeight m N (c j)) *
      optimalProfitTwo (fun j => gridVal m (c j).val) ≤ 2 * β := by
    simpa only [Nat.cast_ofNat] using
      expected_optimalProfitTwo_equalRevGrid_le hcard hDSIC hIR hUnit hComp hm N
  -- Lower bound `E[F^{(2)}(c)] ≥ 4 - 2 / (m + 1) - 2 / H` via tail sum of `min(c 0, c 1)`.
  have hF2_ge : ∀ c : Fin 2 → Fin (N + 1),
      2 * (1 + (∑ r ∈ Finset.Icc 1 N,
          if r ≤ min (c 0).val (c 1).val then (1 : ℝ) else 0) / (m : ℝ)) ≤
        optimalProfitTwo (fun j => gridVal m (c j).val) := by
    intro c
    have hmin_eq : ((min (c 0).val (c 1).val : ℕ) : ℝ) =
        ∑ r ∈ Finset.Icc 1 N, if r ≤ min (c 0).val (c 1).val then (1 : ℝ) else 0 := by
      have hleN : min (c 0).val (c 1).val ≤ N :=
        (min_le_left _ _).trans (Nat.lt_succ_iff.1 (c 0).isLt)
      rw [Finset.sum_boole]
      have hfilt : (Finset.Icc 1 N).filter (fun r => r ≤ min (c 0).val (c 1).val) =
          Finset.Icc 1 (min (c 0).val (c 1).val) := by
        ext r; simp only [mem_filter, mem_Icc]; omega
      rw [hfilt, Nat.card_Icc]
      simp only [Nat.add_sub_cancel]
    have hval_eq : 1 + ((min (c 0).val (c 1).val : ℕ) : ℝ) / (m : ℝ) =
        gridVal m (min (c 0).val (c 1).val) := by
      unfold gridVal
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      push_cast
      field_simp
    rw [← hmin_eq, hval_eq]
    have hle := mul_card_le_singlePriceProfitOn (m := 2) (s := univ) (W := univ)
      (b := fun j : Fin 2 => gridVal m (c j).val) (p := gridVal m (min (c 0).val (c 1).val))
      (fun j _ => (gridVal_pos hm _).le) subset_rfl (by decide) fun j _ => by
        fin_cases j
        · exact gridVal_mono (min_le_left _ _)
        · exact gridVal_mono (min_le_right _ _)
    simpa only [card_univ, Fintype.card_fin, Nat.cast_ofNat, mul_comm] using hle
  have htail_prob : ∀ r ∈ Finset.Icc 1 N,
      ∑ c : Fin 2 → Fin (N + 1), (∏ j : Fin 2, equalRevWeight m N (c j)) *
          (if r ≤ min (c 0).val (c 1).val then (1 : ℝ) else 0) =
        (1 / gridVal m r) ^ 2 := by
    intro r hr
    have hrN : r ≤ N := (mem_Icc.1 hr).2
    let e2 : (Fin 2 → Fin (N + 1)) ≃ Fin (N + 1) × Fin (N + 1) :=
      { toFun := fun c => (c 0, c 1)
        invFun := fun ⟨a, b⟩ => ![a, b]
        left_inv := fun c => by ext i; fin_cases i <;> rfl
        right_inv := fun ⟨_, _⟩ => rfl }
    have hfactor : ∑ c : Fin 2 → Fin (N + 1), (∏ j : Fin 2, equalRevWeight m N (c j)) *
        (if r ≤ min (c 0).val (c 1).val then (1 : ℝ) else 0) =
        (∑ a : Fin (N + 1), if r ≤ a.val then equalRevWeight m N a else 0) *
          (∑ b : Fin (N + 1), if r ≤ b.val then equalRevWeight m N b else 0) := by
      rw [← e2.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      have h0 : e2.symm (a, b) 0 = a := rfl
      have h1 : e2.symm (a, b) 1 = b := rfl
      rw [Fin.prod_univ_two, h0, h1]
      by_cases ha : r ≤ a.val <;> by_cases hb : r ≤ b.val <;>
        simp only [le_min_iff, ha, hb, and_self, and_false, false_and, ↓reduceIte,
          mul_one, mul_zero, zero_mul]
    rw [hfactor, ← Finset.sum_filter, sum_equalRevWeight_tail N r hrN, sq]
  have hexp_F2_ge : 4 - 2 / ((m + 1 : ℕ) : ℝ) - 2 / (H : ℝ) ≤
      ∑ c : Fin 2 → Fin (N + 1), (∏ j : Fin 2, equalRevWeight m N (c j)) *
        optimalProfitTwo (fun j => gridVal m (c j).val) := by
    have hstep : 2 + (2 / (m : ℝ)) * ∑ r ∈ Finset.Icc 1 N, (1 / gridVal m r) ^ 2 ≤
        ∑ c : Fin 2 → Fin (N + 1), (∏ j : Fin 2, equalRevWeight m N (c j)) *
          optimalProfitTwo (fun j => gridVal m (c j).val) := by
      have hle := expected_add_sum_indicator_le hm 2 (2 / (m : ℝ)) (Finset.Icc 1 N)
        (fun r c => r ≤ min (c 0).val (c 1).val)
        (f := fun c => optimalProfitTwo (fun j => gridVal m (c j).val))
        fun c => (by ring : 2 + (2 / (m : ℝ)) * _ = 2 * (1 + _ / (m : ℝ))).trans_le (hF2_ge c)
      rwa [Finset.sum_congr rfl htail_prob] at hle
    have hsum_sq : (m : ℝ) * (1 / ((m + 1 : ℕ) : ℝ) - 1 / ((m * H + 1 : ℕ) : ℝ)) ≤
        (1 / (m : ℝ)) * ∑ r ∈ Finset.Icc 1 N, (1 / gridVal m r) ^ 2 := by
      have hmN : N + m = m * H := by
        dsimp only [N]
        have : 1 ≤ H := by omega
        calc m * (H - 1) + m = m * (H - 1) + m * 1 := by ring
          _ = m * (H - 1 + 1) := by rw [← mul_add]
          _ = m * H := by rw [Nat.sub_add_cancel this]
      have hshift : ∑ r ∈ Finset.Icc 1 N, (1 / gridVal m r) ^ 2 =
          (m : ℝ) ^ 2 * ∑ s ∈ Finset.Icc (m + 1) (m * H), (1 : ℝ) / ((s : ℝ) ^ 2) := by
        have hterm : ∀ r : ℕ, (1 / gridVal m r) ^ 2 =
            (m : ℝ) ^ 2 * ((1 : ℝ) / (((r + m : ℕ) : ℝ) ^ 2)) := fun r => by
          unfold gridVal
          have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
          have hr0 : ((m + r : ℕ) : ℝ) ≠ 0 := by positivity
          rw [Nat.add_comm r m]
          field_simp
        simp_rw [hterm, ← Finset.mul_sum]
        rw [sum_Icc_shift_add 1 N m (fun s => (1 : ℝ) / ((s : ℝ) ^ 2)), Nat.add_comm 1 m, hmN]
      rw [hshift]
      have hbound := sum_inv_sq_ge (a := m + 1) (b := m * H) (by omega)
        (by nlinarith : m + 1 ≤ m * H)
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      calc (m : ℝ) * (1 / ((m + 1 : ℕ) : ℝ) - 1 / ((m * H + 1 : ℕ) : ℝ))
          ≤ (m : ℝ) * ∑ s ∈ Finset.Icc (m + 1) (m * H), (1 : ℝ) / ((s : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hbound hmpos.le
        _ = (1 / (m : ℝ)) *
              ((m : ℝ) ^ 2 * ∑ s ∈ Finset.Icc (m + 1) (m * H), (1 : ℝ) / ((s : ℝ) ^ 2)) := by
            field_simp [hmpos.ne']
    have hm1_id : (m : ℝ) / ((m + 1 : ℕ) : ℝ) = 1 - 1 / ((m + 1 : ℕ) : ℝ) := by
      push_cast; field_simp; ring
    have hmH_le : (m : ℝ) / ((m * H + 1 : ℕ) : ℝ) ≤ 1 / (H : ℝ) := by
      have hpos : (0 : ℝ) < (m : ℝ) * (H : ℝ) := by positivity
      have hle : (m : ℝ) * (H : ℝ) ≤ ((m * H + 1 : ℕ) : ℝ) := by push_cast; linarith
      calc (m : ℝ) / ((m * H + 1 : ℕ) : ℝ)
          ≤ (m : ℝ) / ((m : ℝ) * (H : ℝ)) :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg m) hpos hle
        _ = 1 / (H : ℝ) := by
            have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
            field_simp [hm0]
    have hcomb : 2 - 2 / ((m + 1 : ℕ) : ℝ) - 2 / (H : ℝ) ≤
        (2 / (m : ℝ)) * ∑ r ∈ Finset.Icc 1 N, (1 / gridVal m r) ^ 2 := by
      have h1 : 2 * ((m : ℝ) / ((m + 1 : ℕ) : ℝ) - (m : ℝ) / ((m * H + 1 : ℕ) : ℝ)) ≤
          (2 / (m : ℝ)) * ∑ r ∈ Finset.Icc 1 N, (1 / gridVal m r) ^ 2 := by
        calc 2 * ((m : ℝ) / ((m + 1 : ℕ) : ℝ) - (m : ℝ) / ((m * H + 1 : ℕ) : ℝ))
            = 2 * ((m : ℝ) * (1 / ((m + 1 : ℕ) : ℝ) - 1 / ((m * H + 1 : ℕ) : ℝ))) := by ring
          _ ≤ 2 * ((1 / (m : ℝ)) * ∑ r ∈ Finset.Icc 1 N, (1 / gridVal m r) ^ 2) :=
              mul_le_mul_of_nonneg_left hsum_sq (by norm_num)
          _ = (2 / (m : ℝ)) * ∑ r ∈ Finset.Icc 1 N, (1 / gridVal m r) ^ 2 := by ring
      have h2 : 2 - 2 / ((m + 1 : ℕ) : ℝ) - 2 / (H : ℝ) ≤
          2 * ((m : ℝ) / ((m + 1 : ℕ) : ℝ) - (m : ℝ) / ((m * H + 1 : ℕ) : ℝ)) := by
        rw [hm1_id]
        have hmul1 : 2 * (1 / ((m + 1 : ℕ) : ℝ)) = 2 / ((m + 1 : ℕ) : ℝ) := by ring
        have hmul2 : 2 * (1 / (H : ℝ)) = 2 / (H : ℝ) := by ring
        linarith [hmH_le]
      exact h2.trans h1
    linarith [hstep]
  linarith

/-- Lower bound on `Pr[X ≥ t]` for the equal-revenue grid when `1 ≤ t ≤ H`:
`1 / (t + 1 / m) ≤ ∑_{k : t ≤ gridVal m k} equalRevWeight m N k`. -/
private theorem equalRev_tail_ge {m H : ℕ} (hm : 0 < m) (hH : 1 ≤ H) {t : ℝ}
    (ht1 : 1 ≤ t) (htH : t ≤ (H : ℝ)) :
    1 / (t + 1 / (m : ℝ)) ≤
      ∑ j ∈ (univ : Finset (Fin (m * (H - 1) + 1))).filter (fun j => t ≤ gridVal m j.val),
        equalRevWeight m (m * (H - 1)) j := by
  set N : ℕ := m * (H - 1)
  set K : ℕ := ⌈(m : ℝ) * t⌉₊
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hKm : m ≤ K := by
    have : (m : ℝ) ≤ (m : ℝ) * t := by nlinarith
    exact_mod_cast this.trans (Nat.le_ceil _)
  have hKH : K ≤ m * H := Nat.ceil_le.2 (by
    push_cast; exact mul_le_mul_of_nonneg_left htH hmpos.le)
  have hkN : K - m ≤ N := by
    have : m + N = m * H := by
      dsimp only [N]
      calc m + m * (H - 1) = m * 1 + m * (H - 1) := by ring
        _ = m * (1 + (H - 1)) := by rw [← mul_add]
        _ = m * H := by rw [Nat.add_sub_cancel' hH]
    omega
  have hfilt : (univ : Finset (Fin (N + 1))).filter (fun j => t ≤ gridVal m j.val) =
      (univ : Finset (Fin (N + 1))).filter (fun j => K - m ≤ j.val) := by
    ext j
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [mem_univ, true_and, gridVal]
    constructor
    · intro hle
      have hmul : (m : ℝ) * t ≤ ((m + j.val : ℕ) : ℝ) := by
        have := (le_div_iff₀ hmpos).1 hle
        linarith
      have hK : K ≤ m + j.val := Nat.ceil_le.2 hmul
      omega
    · intro hle
      have hK : K ≤ m + j.val := by omega
      have hmul : (m : ℝ) * t ≤ ((m + j.val : ℕ) : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hK)
      exact (le_div_iff₀ hmpos).2 (by linarith)
  rw [hfilt, sum_equalRevWeight_tail N (K - m) hkN]
  have hgrid : gridVal m (K - m) ≤ t + 1 / (m : ℝ) := by
    unfold gridVal
    rw [Nat.add_sub_cancel' hKm]
    have hKlt : (K : ℝ) < (m : ℝ) * t + 1 := Nat.ceil_lt_add_one (by positivity)
    rw [div_le_iff₀ hmpos]
    have hmul : (t + 1 / (m : ℝ)) * (m : ℝ) = (m : ℝ) * t + 1 := by
      field_simp [hmpos.ne']
    linarith
  exact one_div_le_one_div_of_le (gridVal_pos hm _) hgrid

/-- Algebraic identity for the union of "at least 2 of 3 are in `A`" and "all 3 are in `B`" when
`A ⊆ B` on a product space: with `p = Pr[A]` and `q = Pr[B]`, the probability equals
`3 p² (1 - q) + q³`. -/
private theorem three_union_prob {α : Type*} [Fintype α] (w : α → ℝ) (hw : ∑ a, w a = 1)
    (A B : α → Prop) [DecidablePred A] [DecidablePred B] (hAB : ∀ a, A a → B a) :
    let p := ∑ a, if A a then w a else 0
    let q := ∑ a, if B a then w a else 0
    ∑ c : Fin 3 → α, (∏ j : Fin 3, w (c j)) *
        (if ((A (c 0) ∧ A (c 1)) ∨ (A (c 0) ∧ A (c 2)) ∨ (A (c 1) ∧ A (c 2))) ∨
            (B (c 0) ∧ B (c 1) ∧ B (c 2)) then (1 : ℝ) else 0) =
      3 * p ^ 2 * (1 - q) + q ^ 3 := by
  intro p q
  let I : α → ℝ := fun a => if A a then 1 else 0
  let J : α → ℝ := fun a => if B a ∧ ¬ A a then 1 else 0
  let K : α → ℝ := fun a => if ¬ B a then 1 else 0
  have hpt : ∀ a b d : α,
      (if ((A a ∧ A b) ∨ (A a ∧ A d) ∨ (A b ∧ A d)) ∨ (B a ∧ B b ∧ B d) then (1 : ℝ) else 0) =
        I a * I b * K d + I a * K b * I d + K a * I b * I d +
          (I a + J a) * (I b + J b) * (I d + J d) := by
    intro a b d
    dsimp only [I, J, K]
    by_cases ha : A a <;> by_cases hb : A b <;> by_cases hd : A d <;>
      by_cases hba : B a <;> by_cases hbb : B b <;> by_cases hbd : B d
    all_goals
      first
      | exact absurd (hAB a ha) hba
      | exact absurd (hAB b hb) hbb
      | exact absurd (hAB d hd) hbd
      | (simp only [ha, hb, hd, hba, hbb, hbd, and_true, and_false, or_true, or_false,
          not_true_eq_false, not_false_eq_true, ↓reduceIte]; norm_num)
  have hsumI : ∑ a : α, w a * I a = p :=
    Finset.sum_congr rfl fun a _ => by dsimp only [I]; split_ifs <;> ring
  have hsumIJ : ∑ a : α, w a * (I a + J a) = q := by
    refine Finset.sum_congr rfl fun a _ => ?_
    dsimp only [I, J]
    by_cases ha : A a <;> by_cases hba : B a
    · simp only [ha, hba, not_true_eq_false, and_false, ↓reduceIte]; ring
    · exact absurd (hAB a ha) hba
    · simp only [ha, hba, not_false_eq_true, and_true, ↓reduceIte]; ring
    · simp only [ha, hba, false_and, ↓reduceIte]; ring
  have hsumK : ∑ a : α, w a * K a = 1 - q := by
    have hsplit : ∑ a : α, w a * K a + q = ∑ a : α, w a := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      dsimp only [K]; by_cases hba : B a <;> simp only [hba, not_true_eq_false, not_false_eq_true,
        ↓reduceIte] <;> ring
    linarith [hw]
  let e3 : (Fin 3 → α) ≃ α × α × α :=
    { toFun := fun c => (c 0, c 1, c 2)
      invFun := fun ⟨a, b, d⟩ => ![a, b, d]
      left_inv := fun c => by ext i; fin_cases i <;> rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }
  have hprod3 : ∀ (f g h : α → ℝ),
      ∑ x : α × α × α, (w x.1 * w x.2.1 * w x.2.2) * (f x.1 * g x.2.1 * h x.2.2) =
        (∑ a, w a * f a) * (∑ b, w b * g b) * (∑ d, w d * h d) := by
    intro f g h
    calc ∑ x : α × α × α, (w x.1 * w x.2.1 * w x.2.2) * (f x.1 * g x.2.1 * h x.2.2)
        = ∑ a : α, ∑ b : α, ∑ d : α, (w a * f a) * ((w b * g b) * (w d * h d)) := by
            simp only [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
              Finset.sum_congr rfl fun d _ => by ring
      _ = ∑ a : α, (w a * f a) * ∑ b : α, (w b * g b) * ∑ d : α, (w d * h d) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            have hinner : ∀ b : α,
                ∑ d : α, (w a * f a) * ((w b * g b) * (w d * h d)) =
                  (w a * f a) * ((w b * g b) * ∑ d : α, (w d * h d)) := fun b => by
              rw [← Finset.mul_sum, ← Finset.mul_sum]
            simp_rw [hinner, ← Finset.mul_sum]
      _ = (∑ a, w a * f a) * (∑ b, w b * g b) * (∑ d, w d * h d) := by
            rw [← Finset.sum_mul, ← Finset.sum_mul, mul_assoc]
  rw [← e3.symm.sum_comp]
  have hrew : ∀ x : α × α × α,
      (∏ j : Fin 3, w (e3.symm x j)) *
        (if ((A (e3.symm x 0) ∧ A (e3.symm x 1)) ∨ (A (e3.symm x 0) ∧ A (e3.symm x 2)) ∨
            (A (e3.symm x 1) ∧ A (e3.symm x 2))) ∨
            (B (e3.symm x 0) ∧ B (e3.symm x 1) ∧ B (e3.symm x 2)) then (1 : ℝ) else 0) =
      (w x.1 * w x.2.1 * w x.2.2) * (I x.1 * I x.2.1 * K x.2.2) +
        (w x.1 * w x.2.1 * w x.2.2) * (I x.1 * K x.2.1 * I x.2.2) +
        (w x.1 * w x.2.1 * w x.2.2) * (K x.1 * I x.2.1 * I x.2.2) +
        (w x.1 * w x.2.1 * w x.2.2) *
          ((I x.1 + J x.1) * (I x.2.1 + J x.2.1) * (I x.2.2 + J x.2.2)) := by
    intro ⟨a, b, d⟩
    have h0 : e3.symm (a, b, d) 0 = a := rfl
    have h1 : e3.symm (a, b, d) 1 = b := rfl
    have h2 : e3.symm (a, b, d) 2 = d := rfl
    rw [Fin.prod_univ_three, h0, h1, h2, hpt a b d]
    ring
  simp_rw [hrew, Finset.sum_add_distrib]
  rw [hprod3 I I K, hprod3 I K I, hprod3 K I I,
    hprod3 (fun a => I a + J a) (fun a => I a + J a) (fun a => I a + J a), hsumI, hsumIJ, hsumK]
  ring

/-- **3-bidder randomized competitive lower bound (`13 / 6`)** ([HartlineKarlin2007], §13.4.3,
p. 347): no `3`-bidder truthful (DSIC and IR, deterministic or truthful-in-expectation randomized)
digital goods auction has competitive ratio less than `13 / 6` with respect to `ℱ⁽²⁾`. -/
theorem thirteen_div_six_le_of_isCompetitive_three {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 3) {M : Mechanism ι} (hDSIC : M.IsDSIC) (hIR : M.IsIR)
    (hUnit : IsUnitAlloc M.allocation) {β : ℝ}
    (hComp : IsCompetitive optimalProfitTwo (fun b => ∑ i, M.payment b i) β) :
    (13 : ℝ) / 6 ≤ β := by
  by_contra hlt
  push Not at hlt
  set ε : ℝ := 13 / 2 - 3 * β with hε_def
  have hε : 0 < ε := by dsimp only [ε]; linarith
  set m : ℕ := ⌈16 / ε⌉₊ + 1
  set H : ℕ := max 2 (⌈12 / ε⌉₊ + 1)
  have hm : 0 < m := Nat.succ_pos _
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hH2 : 2 ≤ H := le_max_left _ _
  have hH1 : 1 ≤ H := by omega
  set N : ℕ := m * (H - 1)
  have hm_eps : 16 / ((3 * m + 4 : ℕ) : ℝ) < ε / 2 := by
    have h1 : 16 / ε < (m : ℝ) := by
      have : 16 / ε ≤ (⌈16 / ε⌉₊ : ℝ) := Nat.le_ceil _
      push_cast [m]; linarith
    have hpos : (0 : ℝ) < ((3 * m + 4 : ℕ) : ℝ) := by positivity
    rw [div_lt_iff₀ hpos]
    have h2 := (div_lt_iff₀ hε).1 h1
    push_cast
    nlinarith
  have hH_eps : 6 / (H : ℝ) < ε / 2 := by
    have h1 : 12 / ε < (H : ℝ) := by
      have hceil : 12 / ε ≤ (⌈12 / ε⌉₊ : ℝ) := Nat.le_ceil _
      have hHge : ((⌈12 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast le_max_right 2 _
      push_cast at hHge; linarith
    have hHpos : (0 : ℝ) < (H : ℝ) := by positivity
    rw [div_lt_iff₀ hHpos]
    have := (div_lt_iff₀ hε).1 h1
    linarith
  have hexp_le : ∑ c : Fin 3 → Fin (N + 1), (∏ j : Fin 3, equalRevWeight m N (c j)) *
      optimalProfitTwo (fun j => gridVal m (c j).val) ≤ 3 * β := by
    simpa only [Nat.cast_ofNat] using
      expected_optimalProfitTwo_equalRevGrid_le hcard hDSIC hIR hUnit hComp hm N
  let ev (r : ℕ) (c : Fin 3 → Fin (N + 1)) : Prop :=
    let A : Fin (N + 1) → Prop := fun a => (r : ℝ) / (2 * (m : ℝ)) ≤ gridVal m a.val
    let B : Fin (N + 1) → Prop := fun a => (r : ℝ) / (3 * (m : ℝ)) ≤ gridVal m a.val
    ((A (c 0) ∧ A (c 1)) ∨ (A (c 0) ∧ A (c 2)) ∨ (A (c 1) ∧ A (c 2))) ∨
      (B (c 0) ∧ B (c 1) ∧ B (c 2))
  have hF2_ge_step : ∀ c : Fin 3 → Fin (N + 1),
      3 + (∑ r ∈ Finset.Icc (3 * m + 1) (2 * m * H),
          if ev r c then (1 : ℝ) else 0) / (m : ℝ) ≤
        optimalProfitTwo (fun j => gridVal m (c j).val) := by
    intro c
    let a0 : ℕ := m + (c 0).val
    let a1 : ℕ := m + (c 1).val
    let a2 : ℕ := m + (c 2).val
    let K : ℕ := max (max (2 * min a0 a1) (max (2 * min a0 a2) (2 * min a1 a2)))
      (3 * min a0 (min a1 a2))
    have hK3m : 3 * m ≤ K := by
      have : m ≤ min a0 (min a1 a2) := le_min (Nat.le_add_right _ _)
        (le_min (Nat.le_add_right _ _) (Nat.le_add_right _ _))
      exact (Nat.mul_le_mul_left 3 this).trans (le_max_right _ _)
    have hK_le_F2 : (K : ℝ) / (m : ℝ) ≤ optimalProfitTwo (fun j => gridVal m (c j).val) := by
      have hpair : ∀ (i j : Fin 3), i ≠ j →
          ((2 * min (m + (c i).val) (m + (c j).val) : ℕ) : ℝ) / (m : ℝ) ≤
            optimalProfitTwo (fun l => gridVal m (c l).val) := by
        intro i j hij
        have hle := mul_card_le_singlePriceProfitOn (m := 2) (s := univ) (W := {i, j})
          (b := fun l : Fin 3 => gridVal m (c l).val)
          (p := gridVal m (min (c i).val (c j).val))
          (fun l _ => (gridVal_pos hm _).le) (subset_univ _) (by rw [card_pair hij])
          fun l hl => by
            rcases mem_insert.1 hl with rfl | hl'
            · exact gridVal_mono (min_le_left _ _)
            · rw [mem_singleton.1 hl']; exact gridVal_mono (min_le_right _ _)
        rw [card_pair hij] at hle
        have heq : gridVal m (min (c i).val (c j).val) * ((2 : ℕ) : ℝ) =
            ((2 * min (m + (c i).val) (m + (c j).val) : ℕ) : ℝ) / (m : ℝ) := by
          unfold gridVal
          have hmin : m + min (c i).val (c j).val = min (m + (c i).val) (m + (c j).val) :=
            (Nat.add_min_add_left m (c i).val (c j).val).symm
          rw [hmin]
          push_cast; ring
        rwa [heq] at hle
      have htriple : ((3 * min a0 (min a1 a2) : ℕ) : ℝ) / (m : ℝ) ≤
          optimalProfitTwo (fun l => gridVal m (c l).val) := by
        have hle := mul_card_le_singlePriceProfitOn (m := 2) (s := univ) (W := univ)
          (b := fun l : Fin 3 => gridVal m (c l).val)
          (p := gridVal m (min (c 0).val (min (c 1).val (c 2).val)))
          (fun l _ => (gridVal_pos hm _).le) subset_rfl (by decide) fun l _ => by
            fin_cases l
            · exact gridVal_mono (min_le_left _ _)
            · exact gridVal_mono ((min_le_right _ _).trans (min_le_left _ _))
            · exact gridVal_mono ((min_le_right _ _).trans (min_le_right _ _))
        have heq : gridVal m (min (c 0).val (min (c 1).val (c 2).val)) *
            ((univ : Finset (Fin 3)).card : ℝ) =
            ((3 * min a0 (min a1 a2) : ℕ) : ℝ) / (m : ℝ) := by
          unfold gridVal
          have hmin : m + min (c 0).val (min (c 1).val (c 2).val) = min a0 (min a1 a2) := by
            dsimp only [a0, a1, a2]
            rw [Nat.add_min_add_left, Nat.add_min_add_left]
          rw [hmin, card_univ, Fintype.card_fin]
          push_cast; ring
        rwa [heq] at hle
      rw [div_le_iff₀ hmpos]
      dsimp only [K]
      rw [Nat.cast_max, Nat.cast_max, Nat.cast_max]
      exact max_le (max_le ((div_le_iff₀ hmpos).1 (hpair 0 1 (by decide)))
        (max_le ((div_le_iff₀ hmpos).1 (hpair 0 2 (by decide)))
          ((div_le_iff₀ hmpos).1 (hpair 1 2 (by decide)))))
        ((div_le_iff₀ hmpos).1 htriple)
    have hev_le_K : ∀ r : ℕ, ev r c → r ≤ K := by
      intro r hr
      have hmul : ∀ (k : ℕ) (a : Fin (N + 1)), 0 < k →
          (r : ℝ) / ((k : ℝ) * (m : ℝ)) ≤ gridVal m a.val → r ≤ k * (m + a.val) := by
        intro k a hk hle
        unfold gridVal at hle
        have hkm : (0 : ℝ) < (k : ℝ) * (m : ℝ) := by positivity
        have h1 : (r : ℝ) ≤ ((m + a.val : ℕ) : ℝ) / (m : ℝ) * ((k : ℝ) * (m : ℝ)) :=
          (div_le_iff₀ hkm).1 hle
        have h2 : ((m + a.val : ℕ) : ℝ) / (m : ℝ) * ((k : ℝ) * (m : ℝ)) =
            ((k * (m + a.val) : ℕ) : ℝ) := by
          push_cast; field_simp [hmpos.ne']
        exact_mod_cast h1.trans_eq h2
      rcases hr with (⟨h0, h1⟩ | ⟨h0, h2⟩ | ⟨h1, h2⟩) | ⟨h0, h1, h2⟩
      · have h0' := hmul 2 (c 0) (by decide) (by simpa only [Nat.cast_ofNat] using h0)
        have h1' := hmul 2 (c 1) (by decide) (by simpa only [Nat.cast_ofNat] using h1)
        dsimp only [K, a0, a1] at *; omega
      · have h0' := hmul 2 (c 0) (by decide) (by simpa only [Nat.cast_ofNat] using h0)
        have h2' := hmul 2 (c 2) (by decide) (by simpa only [Nat.cast_ofNat] using h2)
        dsimp only [K, a0, a2] at *; omega
      · have h1' := hmul 2 (c 1) (by decide) (by simpa only [Nat.cast_ofNat] using h1)
        have h2' := hmul 2 (c 2) (by decide) (by simpa only [Nat.cast_ofNat] using h2)
        dsimp only [K, a1, a2] at *; omega
      · have h0' := hmul 3 (c 0) (by decide) (by simpa only [Nat.cast_ofNat] using h0)
        have h1' := hmul 3 (c 1) (by decide) (by simpa only [Nat.cast_ofNat] using h1)
        have h2' := hmul 3 (c 2) (by decide) (by simpa only [Nat.cast_ofNat] using h2)
        dsimp only [K, a0, a1, a2] at *; omega
    have hcount : ((Finset.Icc (3 * m + 1) (2 * m * H)).filter (fun r => ev r c)).card ≤
        K - 3 * m := by
      have hsub : (Finset.Icc (3 * m + 1) (2 * m * H)).filter (fun r => ev r c) ⊆
          Finset.Icc (3 * m + 1) K := fun r hr =>
        mem_Icc.2 ⟨(mem_Icc.1 (mem_filter.1 hr).1).1, hev_le_K r (mem_filter.1 hr).2⟩
      exact (card_le_card hsub).trans (by rw [Nat.card_Icc]; omega)
    have hsum_le : 3 + (∑ r ∈ Finset.Icc (3 * m + 1) (2 * m * H),
        if ev r c then (1 : ℝ) else 0) / (m : ℝ) ≤ (K : ℝ) / (m : ℝ) := by
      rw [Finset.sum_boole]
      have hcountR : (((Finset.Icc (3 * m + 1) (2 * m * H)).filter (fun r => ev r c)).card : ℝ) ≤
          (K : ℝ) - 3 * (m : ℝ) := by
        have h := (Nat.cast_le (α := ℝ)).2 hcount
        rw [Nat.cast_sub hK3m, Nat.cast_mul, Nat.cast_ofNat] at h
        exact h
      have hdiv := div_le_div_of_nonneg_right hcountR hmpos.le
      have hrew : 3 + ((K : ℝ) - 3 * (m : ℝ)) / (m : ℝ) = (K : ℝ) / (m : ℝ) := by
        field_simp [hmpos.ne']; ring
      linarith
    exact hsum_le.trans hK_le_F2
  -- Lower bound each tail probability `Pr[ev r] ≥ 12 m² / (r + 3)² - 9 m³ / (r + 3)³`.
  have hprob_ge : ∀ r ∈ Finset.Icc (3 * m + 1) (2 * m * H),
      12 * (m : ℝ) ^ 2 / (((r + 3 : ℕ) : ℝ) ^ 2) - 9 * (m : ℝ) ^ 3 / (((r + 3 : ℕ) : ℝ) ^ 3) ≤
        ∑ c : Fin 3 → Fin (N + 1), (∏ j : Fin 3, equalRevWeight m N (c j)) *
          (if ev r c then (1 : ℝ) else 0) := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := mem_Icc.1 hr
    let A : Fin (N + 1) → Prop := fun a => (r : ℝ) / (2 * (m : ℝ)) ≤ gridVal m a.val
    let B : Fin (N + 1) → Prop := fun a => (r : ℝ) / (3 * (m : ℝ)) ≤ gridVal m a.val
    have hAB : ∀ a, A a → B a := fun a ha => by
      have hdiv : (r : ℝ) / (3 * (m : ℝ)) ≤ (r : ℝ) / (2 * (m : ℝ)) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg r) (by positivity) (by linarith)
      exact hdiv.trans ha
    have heq := three_union_prob (equalRevWeight m N) (sum_equalRevWeight hm N) A B hAB
    dsimp only [ev]
    rw [heq]
    set p : ℝ := ∑ a : Fin (N + 1), if A a then equalRevWeight m N a else 0
    set q : ℝ := ∑ a : Fin (N + 1), if B a then equalRevWeight m N a else 0
    have hpq : p ≤ q := Finset.sum_le_sum fun a _ => by
      by_cases ha : A a
      · simp only [ha, hAB a ha, ↓reduceIte, le_refl]
      · by_cases hb : B a
        · simp only [ha, hb, ↓reduceIte, equalRevWeight_nonneg hm N a]
        · simp only [ha, hb, ↓reduceIte, le_refl]
    have hq1 : q ≤ 1 := by
      rw [← sum_equalRevWeight hm N]
      refine Finset.sum_le_sum fun a _ => ?_
      split_ifs
      · exact le_rfl
      · exact equalRevWeight_nonneg hm N a
    set s : ℝ := ((r + 3 : ℕ) : ℝ)
    have hs3m : 3 * (m : ℝ) ≤ s := by
      dsimp only [s]; push_cast
      have : (3 * m + 1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
      linarith
    have hspos : 0 < s := by linarith
    set p0 : ℝ := 2 * (m : ℝ) / s
    set q0 : ℝ := 3 * (m : ℝ) / s
    have htail_k : ∀ k : ℕ, 2 ≤ k → k ≤ 3 →
        (k : ℝ) * (m : ℝ) / s ≤
          ∑ a : Fin (N + 1), if (r : ℝ) / ((k : ℝ) * (m : ℝ)) ≤ gridVal m a.val then
            equalRevWeight m N a else 0 := by
      intro k hk2 hk3
      have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
      have hk_le3 : (k : ℝ) ≤ 3 := by exact_mod_cast hk3
      have hk_ge2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
      have h1 : 1 ≤ (r : ℝ) / ((k : ℝ) * (m : ℝ)) := by
        rw [le_div_iff₀ (by positivity)]
        have : (3 * m + 1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
        nlinarith
      have h2 : (r : ℝ) / ((k : ℝ) * (m : ℝ)) ≤ (H : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        have : (r : ℝ) ≤ ((2 * m * H : ℕ) : ℝ) := by exact_mod_cast hr2
        push_cast at this; nlinarith
      have htail := equalRev_tail_ge hm hH1 h1 h2
      have hsub : (k : ℝ) * (m : ℝ) / s ≤
          1 / ((r : ℝ) / ((k : ℝ) * (m : ℝ)) + 1 / (m : ℝ)) := by
        have hrhs : 1 / ((r : ℝ) / ((k : ℝ) * (m : ℝ)) + 1 / (m : ℝ)) =
            (k : ℝ) * (m : ℝ) / ((r : ℝ) + (k : ℝ)) := by
          field_simp [hmpos.ne', hk_pos.ne']
        rw [hrhs]
        refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
        dsimp only [s]; push_cast; linarith
      simpa only [← Finset.sum_filter] using hsub.trans htail
    have hp0_ge : p0 ≤ p := by
      simpa only [p0, p, A, Nat.cast_ofNat] using htail_k 2 (by decide) (by decide)
    have hq0_ge : q0 ≤ q := by
      simpa only [q0, q, B, Nat.cast_ofNat] using htail_k 3 (by decide) (by decide)
    have hmono : 3 * p0 ^ 2 * (1 - q0) + q0 ^ 3 ≤ 3 * p ^ 2 * (1 - q) + q ^ 3 := by
      have hp0_nn : 0 ≤ p0 := by positivity
      have hp0_le_q0 : p0 ≤ q0 := div_le_div_of_nonneg_right (by linarith) hspos.le
      have hdiff : (3 * p ^ 2 * (1 - q) + q ^ 3) - (3 * p0 ^ 2 * (1 - q0) + q0 ^ 3) =
          3 * (p ^ 2 - p0 ^ 2) * (1 - q) + (q - q0) * (q ^ 2 + q * q0 + q0 ^ 2 - 3 * p0 ^ 2) := by
        ring
      have hp2 : 0 ≤ p ^ 2 - p0 ^ 2 := by nlinarith
      have hq2 : 0 ≤ q ^ 2 + q * q0 + q0 ^ 2 - 3 * p0 ^ 2 := by nlinarith
      have h1 : 0 ≤ 3 * (p ^ 2 - p0 ^ 2) * (1 - q) :=
        mul_nonneg (by linarith) (by linarith)
      have h2 : 0 ≤ (q - q0) * (q ^ 2 + q * q0 + q0 ^ 2 - 3 * p0 ^ 2) :=
        mul_nonneg (by linarith) hq2
      linarith
    have hid : 3 * p0 ^ 2 * (1 - q0) + q0 ^ 3 =
        12 * (m : ℝ) ^ 2 / s ^ 2 - 9 * (m : ℝ) ^ 3 / s ^ 3 := by
      dsimp only [p0, q0]; field_simp [hspos.ne']; ring
    linarith [hmono, hid]
  -- Combine expectation lower bound with telescoping sums.
  have hexp_F2_ge : 13 / 2 - 16 / ((3 * m + 4 : ℕ) : ℝ) - 6 / (H : ℝ) ≤
      ∑ c : Fin 3 → Fin (N + 1), (∏ j : Fin 3, equalRevWeight m N (c j)) *
        optimalProfitTwo (fun j => gridVal m (c j).val) := by
    have hstep : 3 + (1 / (m : ℝ)) * ∑ r ∈ Finset.Icc (3 * m + 1) (2 * m * H),
          ∑ c : Fin 3 → Fin (N + 1), (∏ j : Fin 3, equalRevWeight m N (c j)) *
            (if ev r c then (1 : ℝ) else 0) ≤
        ∑ c : Fin 3 → Fin (N + 1), (∏ j : Fin 3, equalRevWeight m N (c j)) *
          optimalProfitTwo (fun j => gridVal m (c j).val) :=
      expected_add_sum_indicator_le hm 3 (1 / (m : ℝ)) (Finset.Icc (3 * m + 1) (2 * m * H)) ev
        fun c => (by ring : 3 + (1 / (m : ℝ)) * _ = 3 + _ / (m : ℝ)).trans_le (hF2_ge_step c)
    have hstep3 :
        12 * (m : ℝ) * ∑ s ∈ Finset.Icc (3 * m + 4) (2 * m * H + 3), (1 : ℝ) / ((s : ℝ) ^ 2) -
          9 * (m : ℝ) ^ 2 *
            ∑ s ∈ Finset.Icc (3 * m + 4) (2 * m * H + 3), (1 : ℝ) / ((s : ℝ) ^ 3) ≤
        (1 / (m : ℝ)) * ∑ r ∈ Finset.Icc (3 * m + 1) (2 * m * H),
          ∑ c : Fin 3 → Fin (N + 1), (∏ j : Fin 3, equalRevWeight m N (c j)) *
            (if ev r c then (1 : ℝ) else 0) := by
      have hshift :
          (1 / (m : ℝ)) * ∑ r ∈ Finset.Icc (3 * m + 1) (2 * m * H),
            (12 * (m : ℝ) ^ 2 / (((r + 3 : ℕ) : ℝ) ^ 2) -
              9 * (m : ℝ) ^ 3 / (((r + 3 : ℕ) : ℝ) ^ 3)) =
          12 * (m : ℝ) * ∑ s ∈ Finset.Icc (3 * m + 4) (2 * m * H + 3), (1 : ℝ) / ((s : ℝ) ^ 2) -
            9 * (m : ℝ) ^ 2 *
              ∑ s ∈ Finset.Icc (3 * m + 4) (2 * m * H + 3), (1 : ℝ) / ((s : ℝ) ^ 3) := by
        rw [sum_Icc_shift_add (3 * m + 1) (2 * m * H) 3
          (fun s => 12 * (m : ℝ) ^ 2 / ((s : ℝ) ^ 2) - 9 * (m : ℝ) ^ 3 / ((s : ℝ) ^ 3))]
        have hlo : 3 * m + 1 + 3 = 3 * m + 4 := by omega
        rw [hlo, Finset.sum_sub_distrib, mul_sub, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
          Finset.mul_sum]
        congr 1 <;> exact Finset.sum_congr rfl fun s _ => by field_simp [hmpos.ne']
      rw [← hshift]
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hprob_ge) (by positivity)
    have hAB : 3 * m + 4 ≤ 2 * m * H + 3 := by nlinarith
    have hsq := sum_inv_sq_ge (a := 3 * m + 4) (b := 2 * m * H + 3) (by omega) hAB
    have hcu := sum_inv_cube_le (a := 3 * m + 4) (b := 2 * m * H + 3) (by omega) hAB
    have hsq_bound : 4 - 16 / ((3 * m + 4 : ℕ) : ℝ) - 6 / (H : ℝ) ≤
        12 * (m : ℝ) * (1 / ((3 * m + 4 : ℕ) : ℝ) - 1 / ((2 * m * H + 3 + 1 : ℕ) : ℝ)) := by
      have hid1 : 12 * (m : ℝ) / ((3 * m + 4 : ℕ) : ℝ) = 4 - 16 / ((3 * m + 4 : ℕ) : ℝ) := by
        push_cast; field_simp; ring
      have hid2 : 12 * (m : ℝ) / ((2 * m * H + 3 + 1 : ℕ) : ℝ) ≤ 6 / (H : ℝ) := by
        have hpos : (0 : ℝ) < 2 * (m : ℝ) * (H : ℝ) := by positivity
        have hle : 2 * (m : ℝ) * (H : ℝ) ≤ ((2 * m * H + 3 + 1 : ℕ) : ℝ) := by
          push_cast; linarith
        calc 12 * (m : ℝ) / ((2 * m * H + 3 + 1 : ℕ) : ℝ)
            ≤ 12 * (m : ℝ) / (2 * (m : ℝ) * (H : ℝ)) :=
              div_le_div_of_nonneg_left (by positivity) hpos hle
          _ = 6 / (H : ℝ) := by field_simp [hmpos.ne']; ring
      have hmul : 12 * (m : ℝ) * (1 / ((3 * m + 4 : ℕ) : ℝ) - 1 / ((2 * m * H + 3 + 1 : ℕ) : ℝ)) =
          12 * (m : ℝ) / ((3 * m + 4 : ℕ) : ℝ) - 12 * (m : ℝ) / ((2 * m * H + 3 + 1 : ℕ) : ℝ) := by
        ring
      linarith
    have hcu_bound :
        9 * (m : ℝ) ^ 2 * (1 / (2 * ((3 * m + 4 - 1 : ℕ) : ℝ) * ((3 * m + 4 : ℕ) : ℝ))) ≤
          1 / 2 := by
      have hsub : 3 * m + 4 - 1 = 3 * m + 3 := by omega
      rw [hsub]
      have hden_pos : (0 : ℝ) < 2 * ((3 * m + 3 : ℕ) : ℝ) * ((3 * m + 4 : ℕ) : ℝ) := by positivity
      have hden_ge : 18 * (m : ℝ) ^ 2 ≤ 2 * ((3 * m + 3 : ℕ) : ℝ) * ((3 * m + 4 : ℕ) : ℝ) := by
        push_cast; nlinarith
      calc 9 * (m : ℝ) ^ 2 * (1 / (2 * ((3 * m + 3 : ℕ) : ℝ) * ((3 * m + 4 : ℕ) : ℝ)))
          = 9 * (m : ℝ) ^ 2 / (2 * ((3 * m + 3 : ℕ) : ℝ) * ((3 * m + 4 : ℕ) : ℝ)) := by ring
        _ ≤ 9 * (m : ℝ) ^ 2 / (18 * (m : ℝ) ^ 2) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hden_ge
        _ = 1 / 2 := by field_simp [hmpos.ne']; ring
    have h12 : 12 * (m : ℝ) * (1 / ((3 * m + 4 : ℕ) : ℝ) - 1 / ((2 * m * H + 3 + 1 : ℕ) : ℝ)) ≤
        12 * (m : ℝ) * ∑ s ∈ Finset.Icc (3 * m + 4) (2 * m * H + 3), (1 : ℝ) / ((s : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have h9 :
        9 * (m : ℝ) ^ 2 *
            ∑ s ∈ Finset.Icc (3 * m + 4) (2 * m * H + 3), (1 : ℝ) / ((s : ℝ) ^ 3) ≤
          9 * (m : ℝ) ^ 2 * (1 / (2 * ((3 * m + 4 - 1 : ℕ) : ℝ) * ((3 * m + 4 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hcu (by positivity)
    linarith [hstep, hstep3]
  linarith [hε_def]

/-- Fixed posted-price digital goods auction offering bidder `i` the price `p i`. -/
private noncomputable def postedPriceMechanism {ι : Type*} (p : ι → ℝ) : Mechanism ι where
  allocation b i := open Classical in if p i ≤ b i then 1 else 0
  payment b i := open Classical in if p i ≤ b i then p i else 0

private theorem postedPriceMechanism_isDSIC {ι : Type*} [DecidableEq ι] (p : ι → ℝ) :
    (postedPriceMechanism p).IsDSIC := by
  intro i b v _ _
  simp only [Mechanism.utility, postedPriceMechanism, Function.update_self]
  split_ifs <;> linarith

private theorem postedPriceMechanism_isIR {ι : Type*} (p : ι → ℝ) :
    (postedPriceMechanism p).IsIR := by
  intro i b _
  simp only [Mechanism.utility, postedPriceMechanism]
  split_ifs <;> linarith

private theorem postedPriceMechanism_isNormalized {ι : Type*} [DecidableEq ι] {p : ι → ℝ}
    (hp : 0 ≤ p) : (postedPriceMechanism p).IsNormalized := by
  intro i b _
  simp only [postedPriceMechanism, Function.update_self]
  split_ifs with h
  · exact le_antisymm h (hp i)
  · rfl

private theorem postedPriceMechanism_isBinary {ι : Type*} (p : ι → ℝ) :
    IsBinary (postedPriceMechanism p).allocation := fun _ _ _ => by
  dsimp only [postedPriceMechanism]; split_ifs <;> simp

/-- **Exercise 13.8** ([HartlineKarlin2007], p. 361): no `2`-bidder truthful IR digital goods
auction is best. For every `2`-bidder `IsDSIC ∧ IsIR ∧ IsUnitAlloc` mechanism `M`, there exists a
deterministic DSIC, IR, normalized, binary auction `M'` and a nonnegative bid profile `b` on which
`M'` obtains strictly higher total profit than `M`. -/
theorem exists_strictly_higher_profit_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 2) {M : Mechanism ι} (hDSIC : M.IsDSIC) (hIR : M.IsIR)
    (hUnit : IsUnitAlloc M.allocation) :
    ∃ M' : Mechanism ι, M'.IsDSIC ∧ M'.IsIR ∧ M'.IsNormalized ∧ IsBinary M'.allocation ∧
      ∃ b : ι → ℝ, 0 ≤ b ∧ ∑ i, M.payment b i < ∑ i, M'.payment b i := by
  let e : Fin 2 ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
  let i₀ : ι := e 0
  let i₁ : ι := e 1
  have hne : i₀ ≠ i₁ := fun h => by have := e.injective h; simp at this
  have huniv : (univ : Finset ι) = {i₀, i₁} := by
    ext i
    simp only [mem_univ, mem_insert, mem_singleton, true_iff]
    have hi : e (e.symm i) = i := e.apply_symm_apply i
    match h : e.symm i with
    | ⟨0, _⟩ => left; exact hi.symm.trans (congrArg e (h.trans (Fin.ext rfl)))
    | ⟨1, _⟩ => right; exact hi.symm.trans (congrArg e (h.trans (Fin.ext rfl)))
  let b11 : ι → ℝ := fun _ => 1
  have hb11 : 0 ≤ b11 := fun _ => zero_le_one
  have hpay_le1 : ∀ i : ι, M.payment b11 i ≤ 1 := fun i => by
    have hir := hIR i b11 hb11
    have hu := (hUnit b11 hb11 i).2
    simp only [Mechanism.utility, b11, one_mul] at hir
    linarith
  by_cases hlt2 : ∑ i, M.payment b11 i < 2
  · refine ⟨postedPriceMechanism b11, postedPriceMechanism_isDSIC b11,
      postedPriceMechanism_isIR b11, postedPriceMechanism_isNormalized hb11,
      postedPriceMechanism_isBinary b11, b11, hb11, ?_⟩
    have hsum' : ∑ i, (postedPriceMechanism b11).payment b11 i = 2 := by
      rw [huniv, Finset.sum_pair hne]
      simp only [postedPriceMechanism, b11, le_refl, ↓reduceIte]
      norm_num
    linarith
  · push Not at hlt2
    have hsum11 : ∑ i, M.payment b11 i = M.payment b11 i₀ + M.payment b11 i₁ := by
      rw [huniv, Finset.sum_pair hne]
    have hp0 : M.payment b11 i₀ = 1 := by linarith [hpay_le1 i₀, hpay_le1 i₁]
    have ha0 : M.allocation b11 i₀ = 1 := by
      have hir := hIR i₀ b11 hb11
      have hu := (hUnit b11 hb11 i₀).2
      simp only [Mechanism.utility, b11, one_mul, hp0] at hir
      linarith
    let b21 : ι → ℝ := Function.update b11 i₀ 2
    have hb21 : 0 ≤ b21 := update_nonneg hb11 i₀ (by norm_num)
    have hp21_0 : M.payment b21 i₀ ≤ 1 := by
      have hdsic := hDSIC.utility_update_le i₀ hb11 (by norm_num : (0 : ℝ) ≤ 2) zero_le_one
      have hu := (hUnit b21 hb21 i₀).2
      have hupd1 : Function.update b11 i₀ 1 = b11 := Function.update_eq_self i₀ b11
      rw [hupd1, ha0, hp0] at hdsic
      dsimp only [b21] at hu ⊢
      linarith
    have hp21_1 : M.payment b21 i₁ ≤ 1 := by
      have hir := hIR i₁ b21 hb21
      have hu := (hUnit b21 hb21 i₁).2
      have hb21_i1 : b21 i₁ = 1 := by
        simp only [b21, Function.update_of_ne hne.symm, b11]
      simp only [Mechanism.utility, hb21_i1, one_mul] at hir
      linarith
    refine ⟨postedPriceMechanism b21, postedPriceMechanism_isDSIC b21,
      postedPriceMechanism_isIR b21, postedPriceMechanism_isNormalized hb21,
      postedPriceMechanism_isBinary b21, b21, hb21, ?_⟩
    have hsumM : ∑ i, M.payment b21 i ≤ 2 := by
      rw [huniv, Finset.sum_pair hne]; linarith
    have hsum' : ∑ i, (postedPriceMechanism b21).payment b21 i = 3 := by
      rw [huniv, Finset.sum_pair hne]
      simp only [postedPriceMechanism, le_refl, ↓reduceIte, b21, Function.update_self,
        Function.update_of_ne hne.symm, b11]
      norm_num
    linarith

end RandomizedLowerBounds

/-! ### Limited-supply `k`-unit reduction (`Exercise 13.9`, p. 361) -/

section LimitedSupply

variable {ι : Type*} [Fintype ι]

/-- **Limited-supply single-price benchmark `ℱ⁽²˒ᵏ⁾`** ([HartlineKarlin2007], Exercise 13.9,
p. 361): `max_{2 ≤ m ≤ min k |ι|} m · v_(m)`, where `v_(m)` is the `m`-th largest valuation
(`Fintype.orderStatistic b (|ι| - m)`), or `0` when fewer than `2` items or bidders exist. -/
@[expose] noncomputable def optimalProfitTwoLimited (k : ℕ) (b : ι → ℝ) : ℝ :=
  if h : 2 ≤ min k (Fintype.card ι) then
    haveI : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    (Finset.Icc 2 (min k (Fintype.card ι))).sup' (nonempty_Icc.2 h) fun m =>
      (m : ℝ) * Fintype.orderStatistic b (Fintype.card ι - m)
  else 0

variable [LinearOrder ι]

open Classical in
/-- The set of the top `min k |ι|` bidders under `MultiUnit.Wins k b`. -/
private noncomputable def topKSet (k : ℕ) (b : ι → ℝ) : Finset ι :=
  univ.filter fun i => MultiUnit.Wins k b i

private theorem card_topKSet (k : ℕ) (b : ι → ℝ) :
    (topKSet k b).card = min k (Fintype.card ι) :=
  MultiUnit.card_wins k b

open Classical in
/-- Order-preserving bijection between `Fin (min k |ι|)` and `topKSet k b`. -/
private noncomputable def topKOrderIso (k : ℕ) (b : ι → ℝ) :
    Fin (min k (Fintype.card ι)) ≃o topKSet k b :=
  (topKSet k b).orderIsoOfFin (card_topKSet k b)

/-- Restricted bid profile of the top `min k |ι|` bidders in their original index order. -/
private noncomputable def topKBids (k : ℕ) (b : ι → ℝ) : Fin (min k (Fintype.card ι)) → ℝ :=
  fun r => b (topKOrderIso k b r).1

private theorem topKBids_nonneg (k : ℕ) {b : ι → ℝ} (hb : 0 ≤ b) : 0 ≤ topKBids k b :=
  fun r => hb (topKOrderIso k b r).1

/-- Crucially, when bidder `i` remains in the top `k` under both `b` and `Function.update b i z`,
the top-`k` bidder set itself is unchanged. -/
private theorem topKSet_update_eq {k : ℕ} {b : ι → ℝ} {i : ι} {z : ℝ}
    (h1 : MultiUnit.Wins k b i) (h2 : MultiUnit.Wins k (Function.update b i z) i) :
    topKSet k (Function.update b i z) = topKSet k b := by
  classical
  have hchar : ∀ (c : ι → ℝ), MultiUnit.Wins k c i → ∀ j : ι, j ≠ i →
      (MultiUnit.Wins k c j ↔
        ((univ.erase i).filter fun m => MultiUnit.Beats c m j).card < k - 1) := by
    intro c hci j hji
    have hsplit : MultiUnit.rank c j =
        ((univ.erase i).filter fun m => MultiUnit.Beats c m j).card +
          if MultiUnit.Beats c i j then 1 else 0 := by
      rw [MultiUnit.rank_def]
      have huniv : (univ : Finset ι) = insert i (univ.erase i) := (insert_erase (mem_univ i)).symm
      conv_lhs => rw [huniv]
      rw [filter_insert]
      split_ifs with hbeat
      · rw [card_insert_of_notMem (fun hm => (mem_erase.1 (mem_filter.1 hm).1).1 rfl)]
      · rw [add_zero]
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 fun h0 => Nat.not_lt_zero _ (h0 ▸ hci)
    by_cases hbeat : MultiUnit.Beats c i j
    · simp only [MultiUnit.Wins, hsplit, hbeat, ↓reduceIte]
      omega
    · have hji_beat : MultiUnit.Beats c j i :=
        (MultiUnit.beats_trichotomous hji).resolve_right hbeat
      have hrank_lt : MultiUnit.rank c j < MultiUnit.rank c i := MultiUnit.rank_lt_of_beats hji_beat
      simp only [MultiUnit.Wins, hsplit, hbeat, ↓reduceIte, add_zero] at hrank_lt ⊢
      have hci' : MultiUnit.rank c i < k := hci
      constructor <;> intro _ <;> omega
  ext j
  simp only [topKSet, mem_filter, mem_univ, true_and]
  by_cases hji : j = i
  · subst hji; exact ⟨fun _ => h1, fun _ => h2⟩
  · rw [hchar (Function.update b i z) h2 j hji, hchar b h1 j hji]
    have hfilt : ((univ.erase i).filter fun m => MultiUnit.Beats (Function.update b i z) m j) =
        (univ.erase i).filter fun m => MultiUnit.Beats b m j :=
      filter_congr fun m hm => by
        have hmi : m ≠ i := (mem_erase.1 hm).1
        simp only [MultiUnit.Beats, Function.update_of_ne hji, Function.update_of_ne hmi]
    rw [hfilt]

/-- On `topKBids k b`, every order statistic matches the corresponding top order statistic of `b`,
so `optimalProfitTwo (topKBids k b) = optimalProfitTwoLimited k b`. -/
private theorem optimalProfitTwo_topKBids (k : ℕ) {b : ι → ℝ} (hb : 0 ≤ b) :
    optimalProfitTwo (topKBids k b) = optimalProfitTwoLimited k b := by
  classical
  set n := Fintype.card ι
  set m := min k n
  unfold optimalProfitTwoLimited
  by_cases hm2 : 2 ≤ m
  · have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
    rw [dite_eq_left hm2]
    dsimp only [optimalProfitTwo]
    rw [singlePriceProfitOn_eq_sup_orderStatistic (m := 2) (by decide)
      (by simpa only [Fintype.card_fin] using hm2) (topKBids_nonneg k hb)]
    simp only [Fintype.card_fin]
    refine Finset.sup'_congr (nonempty_Icc.2 hm2) rfl fun t ht => ?_
    obtain ⟨ht2, htm⟩ := mem_Icc.1 ht
    congr 1
    -- Both order statistics equal `b i*` where `i*` has `MultiUnit.rank b i* = t - 1`.
    have ht1_lt_n : t - 1 < n := by omega
    obtain ⟨istar, histar⟩ := MultiUnit.exists_rank_eq (b := b) ht1_lt_n
    have histar_top : istar ∈ topKSet k b :=
      mem_filter.2 ⟨mem_univ _, by rw [MultiUnit.Wins, histar]; omega⟩
    let rstar : Fin m := (topKOrderIso k b).symm ⟨istar, histar_top⟩
    have hrstar_bid : topKBids k b rstar = b istar := by
      dsimp only [topKBids, rstar]
      rw [(topKOrderIso k b).apply_symm_apply]
    have hcard_full : ∀ c : ℕ, c ≤ n →
        (univ.filter fun j : ι => c ≤ MultiUnit.rank b j).card = n - c := by
      intro c hc
      have hinj : Set.InjOn (MultiUnit.rank b)
          ↑(univ.filter fun j : ι => c ≤ MultiUnit.rank b j) :=
        (MultiUnit.rank_injective b).injOn
      rw [← Finset.card_image_of_injOn hinj]
      have himg :
          (univ.filter fun j : ι => c ≤ MultiUnit.rank b j).image (MultiUnit.rank b) =
            Finset.Ico c n := by
        ext r
        simp only [mem_image, mem_filter, mem_univ, true_and, mem_Ico]
        constructor
        · rintro ⟨j, hj, rfl⟩; exact ⟨hj, MultiUnit.rank_lt_card b j⟩
        · rintro ⟨hrc, hrn⟩
          obtain ⟨j, hj⟩ := MultiUnit.exists_rank_eq (b := b) hrn
          exact ⟨j, by omega, hj⟩
      rw [himg, Nat.card_Ico]
    have hcard_top : ∀ c : ℕ, c ≤ m →
        (univ.filter fun r : Fin m => c ≤ MultiUnit.rank b (topKOrderIso k b r).1).card =
          m - c := by
      intro c hc
      have hinj : Set.InjOn (fun r : Fin m => MultiUnit.rank b (topKOrderIso k b r).1)
          ↑(univ.filter fun r : Fin m => c ≤ MultiUnit.rank b (topKOrderIso k b r).1) :=
        fun _ _ _ _ h => (topKOrderIso k b).injective (Subtype.ext (MultiUnit.rank_injective b h))
      rw [← Finset.card_image_of_injOn hinj]
      have himg :
          (univ.filter fun r : Fin m => c ≤ MultiUnit.rank b (topKOrderIso k b r).1).image
            (fun r : Fin m => MultiUnit.rank b (topKOrderIso k b r).1) = Finset.Ico c m := by
        ext s
        simp only [mem_image, mem_filter, mem_univ, true_and, mem_Ico]
        constructor
        · rintro ⟨r, hr, rfl⟩
          have hlt_k : MultiUnit.rank b (topKOrderIso k b r).1 < k :=
            (mem_filter.1 (topKOrderIso k b r).2).2
          exact ⟨hr, lt_min hlt_k (MultiUnit.rank_lt_card b _)⟩
        · rintro ⟨hsc, hsm⟩
          obtain ⟨j, hj⟩ :=
            MultiUnit.exists_rank_eq (b := b) (lt_of_lt_of_le hsm (min_le_right _ _))
          have hj_top : j ∈ topKSet k b := mem_filter.2
            ⟨mem_univ _, by rw [MultiUnit.Wins, hj]; exact lt_of_lt_of_le hsm (min_le_left _ _)⟩
          refine ⟨(topKOrderIso k b).symm ⟨j, hj_top⟩, ?_, ?_⟩
          · rw [(topKOrderIso k b).apply_symm_apply]; dsimp only; omega
          · rw [(topKOrderIso k b).apply_symm_apply]; exact hj
      rw [himg, Nat.card_Ico]
    have hos_full : Fintype.IsOrderStatistic b (n - t) (b istar) := by
      refine ⟨⟨istar, rfl⟩, ?_, ?_⟩
      · have hsub : (univ.filter fun j : ι => b j < b istar) ⊆
            univ.filter fun j : ι => t ≤ MultiUnit.rank b j := fun j hj =>
          mem_filter.2 ⟨mem_univ _, by
            have := MultiUnit.rank_lt_of_beats (Or.inl (mem_filter.1 hj).2)
            omega⟩
        exact (card_le_card hsub).trans_eq (hcard_full t (by omega))
      · have hsup : (univ.filter fun j : ι => t - 1 ≤ MultiUnit.rank b j) ⊆
            univ.filter fun j : ι => b j ≤ b istar := fun j hj =>
          mem_filter.2 ⟨mem_univ _, by
            by_contra hlt; push Not at hlt
            have := MultiUnit.rank_lt_of_beats (Or.inl hlt)
            have := (mem_filter.1 hj).2
            omega⟩
        have hlt_card : n - t < n - (t - 1) := by omega
        exact hlt_card.trans_le (hcard_full (t - 1) (by omega) ▸ card_le_card hsup)
    have hos_top : Fintype.IsOrderStatistic (topKBids k b) (m - t) (b istar) := by
      refine ⟨⟨rstar, hrstar_bid⟩, ?_, ?_⟩
      · have hsub : (univ.filter fun r : Fin m => topKBids k b r < b istar) ⊆
            univ.filter fun r : Fin m => t ≤ MultiUnit.rank b (topKOrderIso k b r).1 :=
          fun r hr => mem_filter.2 ⟨mem_univ _, by
            have hlt : b (topKOrderIso k b r).1 < b istar := (mem_filter.1 hr).2
            have := MultiUnit.rank_lt_of_beats (Or.inl hlt)
            omega⟩
        exact (card_le_card hsub).trans_eq (hcard_top t (by omega))
      · have hsup :
            (univ.filter fun r : Fin m => t - 1 ≤ MultiUnit.rank b (topKOrderIso k b r).1) ⊆
              univ.filter fun r : Fin m => topKBids k b r ≤ b istar := fun r hr =>
          mem_filter.2 ⟨mem_univ _, by
            by_contra hlt; push Not at hlt
            have := MultiUnit.rank_lt_of_beats (Or.inl hlt)
            have := (mem_filter.1 hr).2
            omega⟩
        have hlt_card : m - t < m - (t - 1) := by omega
        exact hlt_card.trans_le (hcard_top (t - 1) (by omega) ▸ card_le_card hsup)
    have hmt : m - t < Fintype.card (Fin m) := by
      simpa only [Fintype.card_fin] using (by omega : m - t < m)
    rw [Fintype.orderStatistic_eq_of_isOrderStatistic hmt hos_top,
      Fintype.orderStatistic_eq_of_isOrderStatistic (by omega : n - t < n) hos_full]
  · rw [dite_eq_right hm2]
    dsimp only [optimalProfitTwo]
    exact singlePriceProfitOn_eq_zero_of_card_lt _ (by rw [card_univ, Fintype.card_fin]; omega)

open Classical in
/-- Top-`k` allocation rule induced by running a digital goods auction `A` on the top `min k |ι|`
bidders (in their original index order) and rejecting all lower-ranked bidders
([HartlineKarlin2007], Exercise 13.9, p. 361). -/
noncomputable def limitedSupplyAlloc (k : ℕ)
    (A : Mechanism (Fin (min k (Fintype.card ι)))) (b : ι → ℝ) (i : ι) : ℝ :=
  if h : i ∈ topKSet k b then
    A.allocation (topKBids k b) ((topKOrderIso k b).symm ⟨i, h⟩)
  else 0

/-- **Limited-supply `k`-unit auction reduction** ([HartlineKarlin2007], Exercise 13.9, p. 361):
pairs `limitedSupplyAlloc k A` with Myerson's payment rule. -/
@[expose] noncomputable def limitedSupplyMechanism (k : ℕ)
    (A : Mechanism (Fin (min k (Fintype.card ι)))) : Mechanism ι :=
  myerson (limitedSupplyAlloc k A)

/-- When bidder `i` stays in `topKSet k`, updating `i`'s bid to `z` updates `topKBids k b` solely
at `i`'s fixed slot `r = (topKOrderIso k b).symm ⟨i, hi⟩`. -/
private theorem topKBids_update_eq {k : ℕ} {b : ι → ℝ} {i : ι} {z : ℝ}
    (h1 : i ∈ topKSet k b) (h2 : i ∈ topKSet k (Function.update b i z)) :
    let r := (topKOrderIso k b).symm ⟨i, h1⟩
    topKBids k (Function.update b i z) = Function.update (topKBids k b) r z ∧
      (topKOrderIso k (Function.update b i z)).symm ⟨i, h2⟩ = r := by
  classical
  have hw1 : MultiUnit.Wins k b i := (mem_filter.1 h1).2
  have hw2 : MultiUnit.Wins k (Function.update b i z) i := (mem_filter.1 h2).2
  have hset : topKSet k (Function.update b i z) = topKSet k b := topKSet_update_eq hw1 hw2
  have hiso : ∀ s : Fin (min k (Fintype.card ι)),
      (topKOrderIso k (Function.update b i z) s).1 = (topKOrderIso k b s).1 := by
    intro s
    have h1' : topKSet k (Function.update b i z) = topKSet k b := hset
    dsimp only [topKOrderIso]
    generalize_proofs hp1 hp2
    revert hp1
    rw [h1']
    intro hp1
    rfl
  have hslot : (topKOrderIso k (Function.update b i z)).symm ⟨i, h2⟩ =
      (topKOrderIso k b).symm ⟨i, h1⟩ := by
    apply (topKOrderIso k b).injective
    apply Subtype.ext
    rw [← hiso, (topKOrderIso k (Function.update b i z)).apply_symm_apply,
      (topKOrderIso k b).apply_symm_apply]
  refine ⟨?_, hslot⟩
  ext s
  dsimp only [topKBids]
  rw [hiso s]
  by_cases hs : s = (topKOrderIso k b).symm ⟨i, h1⟩
  · subst hs
    rw [Function.update_self, (topKOrderIso k b).apply_symm_apply, Function.update_self]
  · rw [Function.update_of_ne hs]
    have hne : (topKOrderIso k b s).1 ≠ i := fun hEq => by
      have : topKOrderIso k b s = ⟨i, h1⟩ := Subtype.ext hEq
      exact hs (by rw [← this, (topKOrderIso k b).symm_apply_apply])
    rw [Function.update_of_ne hne]
    rfl

theorem limitedSupplyAlloc_isUnitAlloc (k : ℕ) {A : Mechanism (Fin (min k (Fintype.card ι)))}
    (hUnit : IsUnitAlloc A.allocation) : IsUnitAlloc (limitedSupplyAlloc k A) := by
  intro b hb i
  dsimp only [limitedSupplyAlloc]
  split_ifs with h
  · exact hUnit (topKBids k b) (topKBids_nonneg k hb) _
  · exact ⟨le_rfl, zero_le_one⟩

theorem limitedSupplyAlloc_isBinary (k : ℕ) {A : Mechanism (Fin (min k (Fintype.card ι)))}
    (hBin : IsBinary A.allocation) : IsBinary (limitedSupplyAlloc k A) := by
  intro b hb i
  dsimp only [limitedSupplyAlloc]
  split_ifs with h
  · exact hBin (topKBids k b) (topKBids_nonneg k hb) _
  · exact Or.inl rfl

/-- Total allocation of `limitedSupplyAlloc k A` never exceeds the `k`-unit supply limit. -/
theorem sum_limitedSupplyAlloc_le (k : ℕ) {A : Mechanism (Fin (min k (Fintype.card ι)))}
    (hUnit : IsUnitAlloc A.allocation) {b : ι → ℝ} (hb : 0 ≤ b) :
    ∑ i : ι, limitedSupplyAlloc k A b i ≤ (k : ℝ) := by
  calc ∑ i : ι, limitedSupplyAlloc k A b i
      = ∑ i ∈ topKSet k b, limitedSupplyAlloc k A b i := by
        refine (Finset.sum_subset (subset_univ _) fun i _ hi => ?_).symm
        simp only [limitedSupplyAlloc, hi, ↓reduceDIte]
    _ ≤ ∑ _i ∈ topKSet k b, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => (limitedSupplyAlloc_isUnitAlloc k hUnit b hb i).2
    _ = ((topKSet k b).card : ℝ) := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (k : ℝ) := by rw [card_topKSet]; exact_mod_cast min_le_left k (Fintype.card ι)

/-- When `A` is binary, `limitedSupplyAlloc k A` belongs to `MultiUnit.multiUnitFeasible k`. -/
theorem limitedSupplyAlloc_mem_multiUnitFeasible (k : ℕ)
    {A : Mechanism (Fin (min k (Fintype.card ι)))} (hBin : IsBinary A.allocation)
    {b : ι → ℝ} (hb : 0 ≤ b) :
    limitedSupplyAlloc k A b ∈ MultiUnit.multiUnitFeasible k :=
  MultiUnit.mem_multiUnitFeasible.2
    ⟨limitedSupplyAlloc_isBinary k hBin b hb,
      sum_limitedSupplyAlloc_le k (IsBinary.isUnitAlloc hBin) hb⟩

/-- `limitedSupplyAlloc k A` is monotone whenever `A` is DSIC with nonnegative allocations. -/
theorem limitedSupplyAlloc_isMonotone (k : ℕ) {A : Mechanism (Fin (min k (Fintype.card ι)))}
    (hDSIC : A.IsDSIC) (hUnit : IsUnitAlloc A.allocation) :
    IsMonotone (limitedSupplyAlloc k A) := by
  classical
  intro i b hb z hz z' hz' hzz'
  change limitedSupplyAlloc k A (Function.update b i z) i ≤
    limitedSupplyAlloc k A (Function.update b i z') i
  by_cases h1 : i ∈ topKSet k (Function.update b i z)
  · have hmono_mu := MultiUnit.isMonotone_allocation (ι := ι) k i b hb hz hz' hzz'
    dsimp only at hmono_mu
    have h2 : i ∈ topKSet k (Function.update b i z') := by
      have hw1 : MultiUnit.Wins k (Function.update b i z) i := (mem_filter.1 h1).2
      rw [MultiUnit.allocation_eq_one_iff.2 hw1] at hmono_mu
      have hw2 : MultiUnit.allocation k (Function.update b i z') i = 1 :=
        (MultiUnit.isBinary_allocation k _ (update_nonneg hb i hz') i).resolve_left fun h0 => by
          rw [h0] at hmono_mu; norm_num at hmono_mu
      exact mem_filter.2 ⟨mem_univ _, MultiUnit.allocation_eq_one_iff.1 hw2⟩
    have hupd_eq : Function.update (Function.update b i z) i z' = Function.update b i z' := by
      simp only [Function.update_idem]
    have h2' : i ∈ topKSet k (Function.update (Function.update b i z) i z') := hupd_eq ▸ h2
    obtain ⟨hbids, hslot⟩ := topKBids_update_eq h1 h2'
    dsimp only [limitedSupplyAlloc]
    rw [dite_eq_left h1, dite_eq_left h2]
    have hslot' : (topKOrderIso k (Function.update b i z')).symm ⟨i, h2⟩ =
        (topKOrderIso k (Function.update b i z)).symm ⟨i, h1⟩ := by
      revert h2' hslot
      rw [hupd_eq]
      intro _ hslot
      exact hslot
    have hbids' : topKBids k (Function.update b i z') =
        Function.update (topKBids k (Function.update b i z))
          ((topKOrderIso k (Function.update b i z)).symm ⟨i, h1⟩) z' := by
      simpa only [hupd_eq] using hbids
    rw [hslot', hbids']
    set r := (topKOrderIso k (Function.update b i z)).symm ⟨i, h1⟩
    have hself : topKBids k (Function.update b i z) r = z := by
      dsimp only [topKBids, r]
      rw [(topKOrderIso k (Function.update b i z)).apply_symm_apply, Function.update_self]
    have hmonoA := hDSIC.isMonotone r (topKBids k (Function.update b i z))
      (topKBids_nonneg k (update_nonneg hb i hz)) hz hz' hzz'
    dsimp only at hmonoA
    have hupdate_self :
        Function.update (topKBids k (Function.update b i z)) r z =
          topKBids k (Function.update b i z) := by
      ext s
      by_cases hs : s = r
      · subst hs; rw [Function.update_self, hself]
      · rw [Function.update_of_ne hs]
    rwa [hupdate_self] at hmonoA
  · dsimp only [limitedSupplyAlloc]
    rw [dite_eq_right h1]
    exact (limitedSupplyAlloc_isUnitAlloc k hUnit _ (update_nonneg hb i hz') i).1

theorem limitedSupplyMechanism_isDSIC (k : ℕ) {A : Mechanism (Fin (min k (Fintype.card ι)))}
    (hDSIC : A.IsDSIC) (hUnit : IsUnitAlloc A.allocation) :
    (limitedSupplyMechanism k A).IsDSIC :=
  myerson_isDSIC (limitedSupplyAlloc_isMonotone k hDSIC hUnit)

theorem limitedSupplyMechanism_isIR (k : ℕ) {A : Mechanism (Fin (min k (Fintype.card ι)))}
    (hUnit : IsUnitAlloc A.allocation) : (limitedSupplyMechanism k A).IsIR :=
  myerson_isIR fun b hb i => (limitedSupplyAlloc_isUnitAlloc k hUnit b hb i).1

theorem limitedSupplyMechanism_isNormalized (k : ℕ)
    (A : Mechanism (Fin (min k (Fintype.card ι)))) :
    (limitedSupplyMechanism k A).IsNormalized :=
  myerson_isNormalized (limitedSupplyAlloc k A)

/-- **Exercise 13.9** ([HartlineKarlin2007], p. 361): if `A` is a DSIC, normalized,
`[0, 1]`-allocated digital goods auction that is `β`-competitive against `ℱ⁽²⁾` on `min k |ι|`
bidders, then `limitedSupplyMechanism k A` is `β`-competitive against the `k`-unit benchmark
`ℱ⁽²˒ᵏ⁾` (`optimalProfitTwoLimited k`). -/
theorem limitedSupplyMechanism_isCompetitive (k : ℕ)
    {A : Mechanism (Fin (min k (Fintype.card ι)))} (hDSIC : A.IsDSIC) (hNorm : A.IsNormalized)
    (hUnit : IsUnitAlloc A.allocation) {β : ℝ}
    (hComp : IsCompetitive optimalProfitTwo (fun c => ∑ r, A.payment c r) β) :
    IsCompetitive (optimalProfitTwoLimited k)
      (fun b => ∑ i, (limitedSupplyMechanism k A).payment b i) β := by
  refine ⟨hComp.1, fun b hb => ?_⟩
  rw [← optimalProfitTwo_topKBids k hb]
  refine (hComp.2 (topKBids k b) (topKBids_nonneg k hb)).trans
    (mul_le_mul_of_nonneg_left ?_ hComp.1)
  have hmono_k : IsMonotone (limitedSupplyAlloc k A) :=
    limitedSupplyAlloc_isMonotone k hDSIC hUnit
  -- Each top-`k` bidder pays at least as much in `limitedSupplyMechanism k A` as in `A(topKBids)`.
  have hterm : ∀ r : Fin (min k (Fintype.card ι)),
      A.payment (topKBids k b) r ≤
        (limitedSupplyMechanism k A).payment b (topKOrderIso k b r).1 := by
    intro r
    set i : ι := (topKOrderIso k b r).1
    have hi : i ∈ topKSet k b := (topKOrderIso k b r).2
    have hr_eq : (topKOrderIso k b).symm ⟨i, hi⟩ = r := (topKOrderIso k b).symm_apply_apply r
    rw [hDSIC.payment_eq_myersonPayment hNorm r (topKBids_nonneg k hb)]
    dsimp only [limitedSupplyMechanism, myerson, myersonPayment]
    have hbi_eq : topKBids k b r = b i := rfl
    have halloc_eq : limitedSupplyAlloc k A b i = A.allocation (topKBids k b) r := by
      simp only [limitedSupplyAlloc, hi, ↓reduceDIte, hr_eq]
    rw [hbi_eq, halloc_eq]
    have hint_le :
        ∫ z in (0 : ℝ)..b i, limitedSupplyAlloc k A (Function.update b i z) i ≤
          ∫ z in (0 : ℝ)..b i, A.allocation (Function.update (topKBids k b) r z) r := by
      have hint1 : IntervalIntegrable (fun z => limitedSupplyAlloc k A (Function.update b i z) i)
          MeasureTheory.volume 0 (b i) :=
        ((hmono_k i b hb).mono fun c (hc : c ∈ Set.uIcc 0 (b i)) =>
          le_trans (le_inf le_rfl (hb i)) hc.1).intervalIntegrable
      have hint2 : IntervalIntegrable (fun z => A.allocation (Function.update (topKBids k b) r z) r)
          MeasureTheory.volume 0 (b i) :=
        ((hDSIC.isMonotone r (topKBids k b) (topKBids_nonneg k hb)).mono
          fun c (hc : c ∈ Set.uIcc 0 (b i)) =>
            le_trans (le_inf le_rfl (hb i)) hc.1).intervalIntegrable
      refine intervalIntegral.integral_mono_on (hb i) hint1 hint2 fun z hz => ?_
      by_cases hz_top : i ∈ topKSet k (Function.update b i z)
      · obtain ⟨hbids, hslot⟩ := topKBids_update_eq hi hz_top
        dsimp only [limitedSupplyAlloc]
        rw [dite_eq_left hz_top, hslot, hr_eq, hbids, hr_eq]
      · dsimp only [limitedSupplyAlloc]
        rw [dite_eq_right hz_top]
        exact (hUnit _ (update_nonneg (topKBids_nonneg k hb) r hz.1) r).1
    linarith
  calc ∑ r : Fin (min k (Fintype.card ι)), A.payment (topKBids k b) r
      ≤ ∑ r : Fin (min k (Fintype.card ι)),
          (limitedSupplyMechanism k A).payment b (topKOrderIso k b r).1 :=
        Finset.sum_le_sum fun r _ => hterm r
    _ = ∑ i ∈ topKSet k b, (limitedSupplyMechanism k A).payment b i :=
        Finset.sum_bij (fun r _ => (topKOrderIso k b r).1)
          (fun r _ => (topKOrderIso k b r).2)
          (fun _ _ _ _ h => (topKOrderIso k b).injective (Subtype.ext h))
          (fun i hi => ⟨(topKOrderIso k b).symm ⟨i, hi⟩, mem_univ _, by
            rw [(topKOrderIso k b).apply_symm_apply]⟩)
          fun _ _ => rfl
    _ ≤ ∑ i : ι, (limitedSupplyMechanism k A).payment b i :=
        Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ =>
          myersonPayment_nonneg hmono_k hb i

end LimitedSupply

end Cslib.GameTheory.SingleParameter.DigitalGoods
