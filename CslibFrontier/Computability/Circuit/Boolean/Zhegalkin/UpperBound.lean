/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Boolean.Complexity
public import Cslib.Computability.Circuit.Simulation
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.Basis
public import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.Complexity
import CslibFrontier.Computability.Circuit.Simulation
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.Synthesis
import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.SectionPairing
import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.BlockCols
import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.ParameterBounds
import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.Decomposition
import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.StageParts
import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.StageStep

/-!
# Explicit and asymptotic Theorem 1 upper bounds over `{⊕, ∧, 1}`

Proves the staged synthesis upper bound `Zhegalkin.exists_circuit_of_andCost_le_bound` and its
asymptotic corollary `Zhegalkin.exists_circuit_of_andCost_le`
([Sergeev, Theorem 1 (upper bound), pp. 1, 3][Sergeev2013AdditiveMultiplicative]).

## Main results

* `Cslib.Circuits.Boolean.Zhegalkin.exists_circuit_of_andCost_le_bound`: explicit staged acyclic
  `{⊕, ∧, 1}`-circuit synthesis bound preserving conjunction count
  ([Sergeev, Theorem 1 (upper bound), p. 3][Sergeev2013AdditiveMultiplicative]).
* `Cslib.Circuits.Boolean.Zhegalkin.exists_circuit_of_andCost_le`,
  `Cslib.Circuits.Boolean.Zhegalkin.complexity_le_of_multiplicativeComplexity_le`: asymptotic
  `(1 / 2 + ε) * M * (M + 2 * n) / log₂ M` synthesis and complexity upper bounds
  ([Sergeev, Theorem 1 (upper bound), p. 1][Sergeev2013AdditiveMultiplicative]).

## References

* [I. S. Sergeev, *A relation between additive and multiplicative complexity of Boolean
  functions*][Sergeev2013AdditiveMultiplicative]
-/

public section

open Finset

namespace Cslib.Circuits.Boolean.Zhegalkin

section Synthesis

variable {n M k : ℕ} {f : BooleanFunction n}

private inductive OutPartIdx (n M : ℕ) where
  | constOne
  | inX (j : Fin n)
  | gateG (ℓ : Fin M)
  deriving DecidableEq

private def outParts (d : PaddedDecomp f M k) : Finset (OutPartIdx n M) :=
  (if d.outC then {.constOne} else ∅) ∪
    ((univ.filter fun j : Fin n => d.outX j = true).map ⟨.inX, fun _ _ h => by injection h⟩) ∪
    ((univ.filter fun ℓ : Fin M => d.outG ℓ = true).map ⟨.gateG, fun _ _ h => by injection h⟩)

private def outPartVal (d : PaddedDecomp f M k) : OutPartIdx n M → BooleanFunction n
  | .constOne => Boolean.Zhegalkin.constOne n
  | .inX j => fun x => x j
  | .gateG ℓ => d.gFn ℓ

private theorem card_outParts_le (d : PaddedDecomp f M k) :
    #(outParts d) ≤ n + M + 1 := by
  have h1 : #(if d.outC then {.constOne} else ∅ : Finset (OutPartIdx n M)) ≤ 1 := by
    split_ifs <;> simp
  unfold outParts
  refine (card_union_le _ _).trans <| (add_le_add ((card_union_le _ _).trans <| add_le_add h1
    ((card_map _).trans_le <| (card_filter_le _ _).trans_eq (card_fin n)))
    ((card_map _).trans_le <| (card_filter_le _ _).trans_eq (card_fin M))).trans ?_
  omega

private theorem sum_outParts_eq (d : PaddedDecomp f M k) (x : Fin n → Bool) :
    (∑ idx ∈ outParts d, outPartVal d idx x) = f x := by
  rw [d.out_eq x]
  unfold outParts linForm
  set p1 : Finset (OutPartIdx n M) := if d.outC then {.constOne} else ∅
  set p2 : Finset (OutPartIdx n M) :=
    (univ.filter fun j : Fin n => d.outX j = true).map ⟨.inX, fun _ _ h => by injection h⟩
  set p3 : Finset (OutPartIdx n M) :=
    (univ.filter fun ℓ : Fin M => d.outG ℓ = true).map ⟨.gateG, fun _ _ h => by injection h⟩
  have hd : Disjoint p1 p2 ∧ Disjoint (p1 ∪ p2) p3 := by
    simp only [p1, p2, p3]
    split_ifs <;> simp [disjoint_right]
  rw [sum_union hd.2, sum_union hd.1, sum_map, sum_map]
  have hs1 : (∑ z ∈ p1, outPartVal d z x) = if d.outC then true else (0 : Bool) := by
    dsimp only [p1]
    split_ifs <;> simp [outPartVal, constOne]
  rw [hs1, ← sum_filter, ← sum_filter]
  rfl

/-- **Explicit staged multiplicative-to-total synthesis bound over `{⊕, ∧, 1}`**
([Sergeev, Theorem 1 (upper bound), p. 3][Sergeev2013AdditiveMultiplicative]):
every `n`-input Boolean function `f` computed by a `{⊕, ∧, 1}`-circuit `c` with at most `M`
conjunction gates (`c.program.cost andCost ≤ M`) can be computed by an acyclic `{⊕, ∧, 1}`-circuit
`c'` using no more conjunction gates (`c'.program.cost andCost ≤ c.program.cost andCost`) and total
size at most `totalBound n M s p`, for any block/stage width `0 < s` and horizontal section height
`0 < p`. -/
theorem exists_circuit_of_andCost_le_bound {n M : ℕ} {f : BooleanFunction n}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hM : c.program.cost andCost ≤ M) {s p : ℕ} (hs : 0 < s) (hp : 0 < p) :
    ∃ c' : Circuit signature n 1,
      c'.Computes interpretation (single f) ∧
      c'.program.cost andCost ≤ c.program.cost andCost ∧
      c'.size ≤ totalBound n M s p := by
  classical
  let k := c.program.cost andCost
  obtain ⟨d⟩ := exists_paddedDecomp c hc hM
  -- Stage 0 setup: `{constZero, constOne}` and `xGroupSet`.
  have hconsts := synth_consts n
  have hxgroup := all_group_subSums (G := Bool) (I := interpretation) (w := andCost)
    (addOp := Op.xor) (s := inputs n) hs rfl (fun _ => rfl) rfl
    (fun j x => x j) (fun j => ⟨j, rfl⟩)
  have hstage0 : CostSynthesis interpretation andCost (inputs n) (stageSet d s p 0)
      (2 + (n * 2 ^ s) / s) 0 := by
    have h0 := ((CostSynthesis.of_subset Set.Subset.rfl).union hconsts).union hxgroup
    refine h0.mono Set.Subset.rfl ?_ (by omega) (by simp)
    intro g hg
    rcases hg with (((((hg | hg) | hg) | ⟨_, hi, _⟩) | ⟨_, hi, _⟩) | ⟨_, _, hi, _⟩)
    exacts [Or.inl (Or.inl hg), Or.inl (Or.inr hg), Or.inr hg, (Nat.not_lt_zero _ hi).elim,
      (Nat.not_lt_zero _ hi).elim, (Nat.not_lt_zero _ hi).elim]
  -- Inductive run across stages `q₀ = 0 .. M / s` (`Q = M / s + 1` stages).
  let Q := M / s + 1
  let stageTC (q₀ : ℕ) : ℕ :=
    (∑ up ∈ (zhegPairIdx d s p).filter (fun up => (up.2.1.1 / 2) / s = q₀),
        (#(pairedCols (hasZhegCol d s) p up.1 up.2.1 up.2.2) - 1)) +
      (∑ r ∈ (zhegOddIdx d s p).filter (fun r => (r.1 / 2) / s = q₀),
        (#(oddCols (hasZhegCol d s) p r) - 1)) +
      (∑ _ ∈ (univ : Finset (Fin M)).filter (fun i => i.1 / s = q₀), (2 * (p + s) + 1)) +
      (if q₀ < M / s then 2 ^ s - s - 1 else 0)
  let stageWC (q₀ : ℕ) : ℕ :=
    ∑ i ∈ (univ : Finset (Fin M)).filter (fun i => i.1 / s = q₀),
      if i.1 < k then 1 else 0
  have hstages : ∀ T : ℕ,
      CostSynthesis interpretation andCost (stageSet d s p 0) (stageSet d s p T)
        (∑ q₀ ∈ range T, stageTC q₀) (∑ q₀ ∈ range T, stageWC q₀) := by
    intro T
    induction T with
    | zero =>
      simpa only [range_zero, sum_empty] using CostSynthesis.of_subset Set.Subset.rfl
    | succ T ih =>
      rw [sum_range_succ, sum_range_succ]
      exact ih.trans
        ((synth_stage_step d hs hp T).mono Set.subset_union_right Set.Subset.rfl le_rfl le_rfl)
  have hall_stages := hstage0.trans
    ((hstages Q).mono Set.subset_union_right Set.Subset.rfl le_rfl le_rfl)
  -- Final output linear form from `stageSet d s p Q`.
  have hdiv_Q {j : ℕ} (hj : j ≤ M) : j / s < Q :=
    Nat.lt_succ_of_le (Nat.div_le_div_right hj)
  have hzero_Q : constZero n ∈ stageSet d s p Q :=
    Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl rfl)))))
  have hout_mem : ∀ idx ∈ outParts d, outPartVal d idx ∈ stageSet d s p Q := by
    intro idx _
    cases idx with
    | constOne => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr rfl)))))
    | inX j => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨j, rfl⟩))))
    | gateG ℓ => exact Or.inl (Or.inl (Or.inr ⟨ℓ, hdiv_Q ℓ.isLt.le, rfl⟩))
  have hout_raw := sum_of_mem_of_zero (G := Bool) (I := interpretation) (w := andCost)
    (addOp := Op.xor) rfl (fun _ => rfl) rfl hzero_Q (outParts d) (outPartVal d) hout_mem
  have hout_fn : (fun x => ∑ idx ∈ outParts d, outPartVal d idx x) = f :=
    funext (sum_outParts_eq d)
  rw [hout_fn] at hout_raw
  have hout_card := card_outParts_le d
  have hout : CostSynthesis interpretation andCost (stageSet d s p Q) {f} (n + M) 0 :=
    hout_raw.mono Set.Subset.rfl Set.Subset.rfl (by omega) le_rfl
  have hfull_synth := hall_stages.trans
    (hout.mono Set.subset_union_right Set.Subset.rfl le_rfl le_rfl)
  -- Sum the stage gate budgets and compare with `totalBound n M s p` and `k`.
  have hpair_sum :
      (∑ q₀ ∈ range Q,
        ∑ up ∈ (zhegPairIdx d s p).filter (fun up => (up.2.1.1 / 2) / s = q₀),
          (#(pairedCols (hasZhegCol d s) p up.1 up.2.1 up.2.2) - 1)) ≤
      (M * (M + 2 * n)) / (2 * s) := by
    have hmaps : ∀ up ∈ zhegPairIdx d s p, (up.2.1.1 / 2) / s ∈ range Q := fun up _ =>
      mem_range.mpr (hdiv_Q (by omega))
    rw [sum_fiberwise_of_maps_to hmaps]
    have h₁ : ∑ up ∈ zhegPairIdx d s p,
          (#(pairedCols (hasZhegCol d s) p up.1 up.2.1 up.2.2) - 1) ≤
        ∑ u ∈ range ((2 * M) ⌈/⌉ p), ∑ pair : Fin (2 * M) × Fin (2 * M),
          #(pairedCols (hasZhegCol d s) p u pair.1 pair.2) :=
      ((sum_le_sum_of_subset (filter_subset _ _)).trans
        (sum_le_sum fun _ _ => Nat.sub_le _ _)).trans_eq (sum_product _ _ _)
    apply (Nat.le_div_iff_mul_le (Nat.mul_pos two_pos hs)).mpr
    have h₂ := two_mul_sum_card_pairedCols_le (hasZhegCol d s) hp
    have h₃ := mul_sum_hasZhegCol_le d s
    nlinarith only [h₁, h₂, h₃]
  have hodd_sum :
      (∑ q₀ ∈ range Q,
        ∑ r ∈ (zhegOddIdx d s p).filter (fun r => (r.1 / 2) / s = q₀),
          (#(oddCols (hasZhegCol d s) p r) - 1)) ≤
      ((2 * M) ⌈/⌉ p) * 2 ^ s * ((n + M) ⌈/⌉ s) := by
    have hmaps : ∀ r ∈ zhegOddIdx d s p, (r.1 / 2) / s ∈ range Q := fun r _ =>
      mem_range.mpr (hdiv_Q (by omega))
    rw [sum_fiberwise_of_maps_to hmaps]
    calc ∑ r ∈ zhegOddIdx d s p, (#(oddCols (hasZhegCol d s) p r) - 1)
        ≤ ∑ r : Fin (2 * M), #(oddCols (hasZhegCol d s) p r) :=
          (sum_le_sum_of_subset (filter_subset _ _)).trans
            (sum_le_sum fun _ _ => Nat.sub_le _ _)
      _ ≤ ((2 * M) ⌈/⌉ p) * Fintype.card (ZhegCol n M s) :=
          sum_card_oddCols_le (hasZhegCol d s) hp
      _ ≤ ((2 * M) ⌈/⌉ p) * (2 ^ s * ((n + M) ⌈/⌉ s)) :=
          Nat.mul_le_mul_left _ (card_zhegCol_le n M s hs)
      _ = ((2 * M) ⌈/⌉ p) * 2 ^ s * ((n + M) ⌈/⌉ s) := by ring
  have hmapsM : ∀ i ∈ (univ : Finset (Fin M)), i.1 / s ∈ range Q := fun i _ =>
    mem_range.mpr (hdiv_Q i.isLt.le)
  have hgates_sum :
      (∑ q₀ ∈ range Q,
        ∑ _ ∈ (univ : Finset (Fin M)).filter (fun i => i.1 / s = q₀), (2 * (p + s) + 1)) ≤
      2 * M * (p + s + 1) := by
    rw [sum_fiberwise_of_maps_to hmapsM, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    nlinarith
  have hgblock_sum :
      (n * 2 ^ s) / s +
        (∑ q₀ ∈ range Q, if q₀ < M / s then 2 ^ s - s - 1 else 0) ≤
      ((n + M) * 2 ^ s) / s := by
    have hsub_sum :
        (∑ q₀ ∈ range Q, if q₀ < M / s then 2 ^ s - s - 1 else 0) =
          (M / s) * (2 ^ s - s - 1) := by
      rw [← sum_filter]
      have hfilt : (range Q).filter (fun q₀ => q₀ < M / s) = range (M / s) := by
        ext q₀
        simp only [Q, mem_filter, mem_range]
        omega
      rw [hfilt, sum_const, card_range, smul_eq_mul]
    rw [hsub_sum]
    have hMs : (M / s) * (2 ^ s - s - 1) ≤ (M * 2 ^ s) / s := by
      rw [mul_comm M, mul_comm (M / s)]
      exact (Nat.mul_le_mul_right _ ((Nat.sub_le _ _).trans (Nat.sub_le _ _))).trans
        (Nat.mul_div_le_mul_div_assoc _ _ _)
    exact (Nat.add_le_add_left hMs _).trans (add_mul n M (2 ^ s) ▸ Nat.div_add_div_le_add_div)
  have hwc_sum : (∑ q₀ ∈ range Q, stageWC q₀) ≤ k := by
    dsimp only [stageWC]
    rw [sum_fiberwise_of_maps_to hmapsM, sum_boole, Nat.cast_id]
    have hinj : Set.InjOn Fin.val
        ((univ.filter fun i : Fin M => i.1 < k) : Set (Fin M)) :=
      fun _ _ _ _ h => Fin.ext h
    exact (card_le_card_of_injOn Fin.val
      (fun i hi => mem_range.mpr (mem_filter.mp hi).2) hinj).trans_eq (card_range _)
  have htc_total :
      (2 + (n * 2 ^ s) / s + ∑ q₀ ∈ range Q, stageTC q₀) + (n + M) ≤ totalBound n M s p := by
    dsimp only [stageTC]
    rw [sum_add_distrib, sum_add_distrib, sum_add_distrib]
    unfold totalBound
    linarith only [hpair_sum, hodd_sum, hgates_sum, hgblock_sum]
  obtain ⟨c', hc', hsize, hcost⟩ :=
    (hfull_synth.mono Set.Subset.rfl Set.Subset.rfl htc_total
      (by linarith only [hwc_sum])).exists_circuit
  exact ⟨c', hc', hcost, hsize⟩

end Synthesis

/-- **Asymptotic multiplicative-to-total circuit synthesis upper bound over `{⊕, ∧, 1}`**
([Sergeev, Theorem 1 (upper bound), p. 1][Sergeev2013AdditiveMultiplicative]):
for every `ε > 0`, there exists `M₀` such that for all `M ≥ M₀`, all `n : ℕ`, and every Boolean
function `f : BooleanFunction n` computed by a `{⊕, ∧, 1}`-circuit `c` with at most `M` conjunction
gates, `f` is computed by a `{⊕, ∧, 1}`-circuit `c'` with no more conjunction gates than `c` and
total gate count at most `(1 / 2 + ε) * M * (M + 2 * n) / Real.logb 2 M`.

Sergeev states Theorem 1 under `M = Ω(n)` and separately notes asymptotic optimality on pp. 1–2;
bounding the explicit `(s, p)` synthesis budget `totalBound n M s p` directly gives a uniform
threshold in `M` for all `n : ℕ` and recovers the published upper bound when `M = Ω(n)`. -/
theorem exists_circuit_of_andCost_le {ε : ℝ} (hε : 0 < ε) :
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ {n M : ℕ}, M₀ ≤ M →
      ∀ {f : BooleanFunction n} (c : Circuit signature n 1),
        c.Computes interpretation (single f) →
        c.program.cost andCost ≤ M →
        ∃ c' : Circuit signature n 1,
          c'.Computes interpretation (single f) ∧
          c'.program.cost andCost ≤ c.program.cost andCost ∧
          (c'.size : ℝ) ≤
            (1 / 2 + ε) * (M : ℝ) * (M + 2 * n : ℝ) / Real.logb 2 M := by
  let C : ℕ := ⌈((4 + 2 * 88 : ℕ) : ℝ) / ε⌉₊ + 10
  obtain ⟨L₁, hL₁8, _, hL₁⟩ := exists_log_threshold C
  let M₀ : ℕ := 2 ^ L₁
  have hM₀_ge2 : 2 ≤ M₀ := le_self_pow (by norm_num) (by omega)
  refine ⟨M₀, hM₀_ge2, fun {n M} hMM₀ {f} c hc hM => ?_⟩
  have hL_ge : L₁ ≤ Nat.log 2 M := Nat.le_log_of_pow_le one_lt_two hMM₀
  obtain ⟨hClog, h6log, hpow2⟩ := hL₁ hL_ge
  have hL8 : 8 ≤ Nat.log 2 M := hL₁8.trans hL_ge
  obtain ⟨hs_pos, _, _, _, _, _⟩ := log_param_props hL8 h6log hpow2
  set L := Nat.log 2 M
  set s := L - 3 * Nat.log 2 L
  set p := (2 * M) / L ^ 2 + 1
  obtain ⟨c', hc', hcost, hsize⟩ :=
    exists_circuit_of_andCost_le_bound c hc hM hs_pos (Nat.succ_pos _)
  refine ⟨c', hc', hcost, (Nat.cast_le.mpr hsize).trans ?_⟩
  set W : ℕ := M * (M + 2 * n)
  set rem : ℕ := ((n + M) * 2 ^ s) / s + 2 * M * (p + s + 1) +
    ((2 * M) ⌈/⌉ p) * 2 ^ s * ((n + M) ⌈/⌉ s) + n + M + 2
  have htb_eq : totalBound n M s p = W / (2 * s) + rem := by
    unfold totalBound W rem
    ring
  rw [htb_eq, Nat.cast_add]
  have hbound := div_two_sub_add_rem_le hε hL8 h6log hpow2 hClog (le_refl W)
    (zhegRem_mul_sq_le n M hL8 h6log hpow2)
  have hW_cast : (W : ℝ) = (M : ℝ) * (M + 2 * n : ℝ) := by
    dsimp only [W]
    push_cast
    ring
  refine hbound.trans_eq ?_
  rw [hW_cast]
  ring

/-- **Multiplicative-to-total complexity upper bound over `{⊕, ∧, 1}`**
([Sergeev, Theorem 1 (upper bound), p. 1][Sergeev2013AdditiveMultiplicative]):
for every `ε > 0`, there exists `M₀` such that for all `M ≥ M₀`, all `n : ℕ`, and every
`n`-variable Boolean function `f` of multiplicative complexity at most `M`
(`multiplicativeComplexity (single f) ≤ M`), the total `{⊕, ∧, 1}` circuit complexity satisfies
`complexity interpretation (single f) ≤ (1 / 2 + ε) * M * (M + 2 * n) / Real.logb 2 M`. -/
theorem complexity_le_of_multiplicativeComplexity_le {ε : ℝ} (hε : 0 < ε) :
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ {n M : ℕ}, M₀ ≤ M →
      ∀ (f : BooleanFunction n),
        multiplicativeComplexity (single f) ≤ M →
        (complexity interpretation (single f) : ℝ) ≤
          (1 / 2 + ε) * (M : ℝ) * (M + 2 * n : ℝ) / Real.logb 2 M := by
  obtain ⟨M₀, hM₀, hsynth⟩ := exists_circuit_of_andCost_le hε
  refine ⟨M₀, hM₀, fun {n M} hMM₀ f hmc => ?_⟩
  obtain ⟨c, hc, hcost⟩ := multiplicativeComplexity_le_iff.mp hmc
  obtain ⟨c', hc', -, hsize⟩ := hsynth hMM₀ c hc hcost
  exact (Nat.cast_le.mpr (complexity_le_of_computes c' hc')).trans hsize

end Cslib.Circuits.Boolean.Zhegalkin
