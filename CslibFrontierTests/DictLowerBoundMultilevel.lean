/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.CellProbe.OuterGame
public import CslibFrontier.DataStructure.Dictionary.CellProbe.LowerBound
public import CslibFrontier.Foundations.Data.BitString.List.PrefixFree
public import CslibFrontierTests.DictLowerBoundDist
import CslibFrontier.Foundations.Data.Nat.Choose
import CslibFrontier.Foundations.Data.Nat.Choose.Real
import CslibFrontier.Probability.Entropy
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Multi-Level Cell-Probe Lower Bounds, Lemma 8.1, and Bridge Lemma Tests

Kernel-checked concrete scheme instantiations, non-vacuity witnesses, and bridge checks for
`CslibFrontier.DataStructure.Dictionary.CellProbe.OuterGame`,
`CslibFrontier.DataStructure.Dictionary.CellProbe.LowerBound`, and supporting combinatorial,
prefix-free, and entropy helpers:

1. **Concrete 2-cell packed dictionary scheme (`twoCellDictScheme`, `twoCellDictImpl`):**
   encodes all valid `Dynamic.spec U V n` states (`BoundedDict U V n`) into `Mem 2 w` whenever
   `Fintype.card (BoundedDict U V n) ≤ 2 ^ (2 * w)`, discharging `validHistoriesUpTo` for all
   horizons `M` on both deterministic `IndexedScheme` and zero-error `Randomized.Scheme`, alongside
   `det_expectedSeqProbes_ge_linear` on `directDictScheme.toIndexed`.
2. **Lemma 8.1 (`queryFreeInnerDist`) concrete instantiation:** instantiates
   `prob_isModeSeedConsistent_queryFreeInnerDist_le` and
   `expected_card_modeConsistent_segmentRest_lt_half_le` on `twoCellDictScheme` at
   `(U = 16, V = 2 ^ 40, n = 4, m = 2, cells = 2, w = 86)`.
3. **Concrete instantiations of Theorems 1.1 & 1.2 (all 8 deterministic and randomized theorems):**
   instantiates `twoCellDictScheme` at `(U = 9, V = 2, n = 2, k = 1, cells = 2, w = 4, R = 1)`
   (`163 ≤ 256` states, `4 ≤ log₂ 9 + log₂ 2`, `8 ≤ benchmarkBits 9 2 2 + 1`), discharging every
   hypothesis with strictly positive lower bounds (`log₂(2 / max 1 1) = 1`).
4. **Concrete instantiations of Theorem 1.3(1)–(2) (all 8 update-only theorems):**
   instantiates `twoCellDictScheme` at `(U = 6, V = 128, n = 2, k = 1, cells = 2, w = 9, R = 1)`
   (`246529 ≤ 262144` states, `6 ^ 3 ≤ 128 * 2 ^ 2`, `9 ≤ log₂ 6 + log₂ 128`,
   `18 ≤ benchmarkBits 6 128 2 + 1`), discharging every hypothesis with strictly positive bounds.
5. **Space-benchmark, binomial, prefix-free, and expectation bridges:** concrete checks for
   `optBits_le_benchmarkBits_add`, `optBits_two_pow_le_benchmarkBits_add_one`,
   `Nat.prod_choose_partition_mul_pow_factorial`,
   `Nat.choose_le_two_pow_mul_choose_sub_of_two_mul_le`,
   `Cslib.logb_choose_sub_logb_sub_three_mul_choose_sub_le`,
   `Cslib.BitString.length_encodeRestr_bool`, `Cslib.BitString.length_encodeRestr_fin_two_pow`,
   `PMF.conditionalEntropy_le_add_conditionalEntropy`, and `PMF.tsum_toReal_map_mul_natCast`.
-/

public section

namespace CslibFrontierTests.DictLowerBoundMultilevel

open Cslib Cslib.BitString Cslib.CellProbe Cslib.DataStructure
open Cslib.DataStructure.Dictionary Cslib.DataStructure.Dictionary.CellProbe
open Cslib.Probability
open CslibFrontierTests.DictLowerBoundDist
open scoped BigOperators ENNReal

/-! ### 1. Concrete 2-Cell Packed Dictionary Scheme and Linear Lower Bounds -/

/-- Concrete exact instantiation of `det_expectedSeqProbes_ge_linear` in query-inclusive mode
on `directDictScheme.toIndexed` at `U = 4, V = 2, n = 2`, discharging every hypothesis. -/
theorem det_linear_bound_query_inclusive_directDict :
    (1 : ℝ) ≤
      ∑' ops, (insertQueryDeleteDist 4 2 2 (by omega) (by omega) ops).toReal *
        (directDictScheme.toIndexed.seqProbes ops : ℝ) := by
  have hl := det_expectedSeqProbes_ge_linear true (U := 4) (V := 2) (n := 2)
    (by omega) (by omega) (D_det := directDictScheme.toIndexed)
    (directDictScheme_all_histories 9)
  have h_mode : modeDist true 4 2 2 (by omega) (by omega) =
      insertQueryDeleteDist 4 2 2 (by omega) (by omega) := modeDist_true 4 2 2 (by omega) (by omega)
  rw [h_mode] at hl
  norm_num at hl ⊢
  exact hl

/-- Concrete exact instantiation of `det_expectedSeqProbes_ge_linear` in update-only mode
on `directDictScheme.toIndexed` at `U = 4, V = 2, n = 2`, discharging every hypothesis. -/
theorem det_linear_bound_update_only_directDict :
    (1 : ℝ) ≤
      ∑' ops, (insertDeleteDist 4 2 2 (by omega) (by omega) ops).toReal *
        (directDictScheme.toIndexed.seqProbes ops : ℝ) := by
  have hl := det_expectedSeqProbes_ge_linear false (U := 4) (V := 2) (n := 2)
    (by omega) (by omega) (D_det := directDictScheme.toIndexed)
    (directDictScheme_all_histories 7)
  have h_mode : modeDist false 4 2 2 (by omega) (by omega) =
      insertDeleteDist 4 2 2 (by omega) (by omega) := modeDist_false 4 2 2 (by omega) (by omega)
  rw [h_mode] at hl
  norm_num at hl ⊢
  exact hl

/-- Exact distribution equivalence between mode distributions and the concrete
`insertQueryDeleteDist` and `insertDeleteDist` samplers. -/
theorem outerGame_modeDist_concrete :
    modeDist true 4 2 2 (by omega) (by omega) =
      insertQueryDeleteDist 4 2 2 (by omega) (by omega) ∧
    modeDist false 4 2 2 (by omega) (by omega) =
      insertDeleteDist 4 2 2 (by omega) (by omega) :=
  ⟨modeDist_true 4 2 2 (by omega) (by omega), modeDist_false 4 2 2 (by omega) (by omega)⟩

/-- Valid dictionary states of capacity at most `n` with keys in `Fin U` and values in `Fin V`. -/
abbrev BoundedDict (U V n : ℕ) : Type :=
  Σ k : Fin (n + 1), SizedDict U V k.val

private theorem card_boundedDict (U V n : ℕ) :
    Fintype.card (BoundedDict U V n) = ∑ k : Fin (n + 1), U.choose k.val * V ^ k.val := by
  simp [BoundedDict, Fintype.card_sigma, card_sizedDict]

private theorem card_mem_two (w : ℕ) : Fintype.card (Mem 2 w) = 2 ^ (2 * w) := by
  simp only [Mem, Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ]
  rw [← pow_mul, mul_comm]

private noncomputable def boundedDictEmb {U V n w : ℕ}
    (hfit : Fintype.card (BoundedDict U V n) ≤ 2 ^ (2 * w)) :
    BoundedDict U V n ↪ Mem 2 w :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (hfit.trans_eq (card_mem_two w).symm))

private def mkBoundedDict {U V n : ℕ} (s : Dictionary.State U)
    (hcard : (Dictionary.dom s).card ≤ n) (hbnd : Dictionary.ValuesBounded V s) :
    BoundedDict U V n :=
  ⟨⟨(Dictionary.dom s).card, Nat.lt_succ_of_le hcard⟩, ⟨s, rfl, hbnd⟩⟩

private noncomputable def decodeBoundedMem {U V n w : ℕ}
    (hfit : Fintype.card (BoundedDict U V n) ≤ 2 ^ (2 * w)) (m : Mem 2 w) :
    Dictionary.State U :=
  open Classical in
  if h : ∃ x : BoundedDict U V n, boundedDictEmb hfit x = m then
    (Classical.choose h).2.1
  else
    Dictionary.empty U

private theorem decodeBoundedMem_apply {U V n w : ℕ}
    (hfit : Fintype.card (BoundedDict U V n) ≤ 2 ^ (2 * w))
    {s : Dictionary.State U} (hcard : (Dictionary.dom s).card ≤ n)
    (hbnd : Dictionary.ValuesBounded V s) :
    decodeBoundedMem hfit (boundedDictEmb hfit (mkBoundedDict s hcard hbnd)) = s := by
  classical
  have hex : ∃ x : BoundedDict U V n,
      boundedDictEmb hfit x = boundedDictEmb hfit (mkBoundedDict s hcard hbnd) :=
    ⟨mkBoundedDict s hcard hbnd, rfl⟩
  dsimp only [decodeBoundedMem]
  rw [dite_eq_left hex]
  exact congrArg (fun x : BoundedDict U V n => x.2.1)
    ((boundedDictEmb hfit).injective (Classical.choose_spec hex))

private def readMem2 {w : ℕ} : ProbeTree 2 w (Mem 2 w) := do
  let c0 ← ProbeTree.read 0
  let c1 ← ProbeTree.read 1
  pure fun i => if i = 0 then c0 else c1

private theorem run_readMem2 {w : ℕ} (m : Mem 2 w) :
    readMem2.run m = (m, m) := by
  simp only [readMem2, ProbeTree.run_bind, ProbeTree.run_read, ProbeTree.run_pure,
    Prod.mk.injEq, and_true]
  funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · rfl
  · obtain rfl : j = 0 := Subsingleton.elim j 0
    rfl

private theorem probes_readMem2 {w : ℕ} (m : Mem 2 w) :
    readMem2.probes m = 2 := by
  simp [readMem2, ProbeTree.probes_bind, ProbeTree.probes_read, ProbeTree.run_read]

private def writeMem2 {w : ℕ} (m' : Mem 2 w) : ProbeTree 2 w PUnit := do
  ProbeTree.write 0 (m' 0)
  ProbeTree.write 1 (m' 1)

private theorem run_writeMem2 {w : ℕ} (m m' : Mem 2 w) :
    (writeMem2 m').run m = (PUnit.unit, m') := by
  simp only [writeMem2, ProbeTree.run_bind, ProbeTree.run_write, Prod.mk.injEq, true_and]
  funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · simp [Function.update]
  · obtain rfl : j = 0 := Subsingleton.elim j 0
    simp [Function.update]

private theorem probes_writeMem2 {w : ℕ} (m m' : Mem 2 w) :
    (writeMem2 m').probes m = 2 := by
  simp [writeMem2, ProbeTree.probes_bind, ProbeTree.probes_write, ProbeTree.run_write]

/-- Packed 2-cell deterministic scheme implementing `Dynamic.spec U V n` in `Mem 2 w`. -/
noncomputable def twoCellDictScheme {U V n w : ℕ}
    (hfit : Fintype.card (BoundedDict U V n) ≤ 2 ^ (2 * w)) :
    Scheme (Dynamic.Op U) Dynamic.Op.Result 2 w where
  init := boundedDictEmb hfit
    (mkBoundedDict (Dictionary.empty U) (by simp) (Dictionary.valuesBounded_empty U V))
  step o := do
    let m ← readMem2
    let stepOut := Dynamic.step (decodeBoundedMem hfit m) o
    let m' :=
      open Classical in
      if h : (Dictionary.dom stepOut.1).card ≤ n ∧ Dictionary.ValuesBounded V stepOut.1 then
        boundedDictEmb hfit (mkBoundedDict stepOut.1 h.1 h.2)
      else
        m
    writeMem2 m'
    pure stepOut.2

private theorem twoCellDictScheme_step_run {U V n w : ℕ}
    (hfit : Fintype.card (BoundedDict U V n) ≤ 2 ^ (2 * w))
    {s : Dictionary.State U} (hcard : (Dictionary.dom s).card ≤ n)
    (hbnd : Dictionary.ValuesBounded V s) {o : Dynamic.Op U}
    (hvalid : (Dynamic.spec U V n).valid s o) :
    let m := boundedDictEmb hfit (mkBoundedDict s hcard hbnd)
    let hcard' := Dynamic.card_dom_step_le_of_valid hcard hvalid
    let hbnd' := Dynamic.valuesBounded_step_of_valid hbnd hvalid
    ((twoCellDictScheme hfit).step o).run m =
      ((Dynamic.step s o).2,
       boundedDictEmb hfit (mkBoundedDict (Dynamic.step s o).1 hcard' hbnd')) ∧
      ((twoCellDictScheme hfit).step o).probes m ≤ 4 := by
  classical
  dsimp only
  have hcard' := Dynamic.card_dom_step_le_of_valid hcard hvalid
  have hbnd' := Dynamic.valuesBounded_step_of_valid hbnd hvalid
  have hcond : (Dictionary.dom (Dynamic.step s o).1).card ≤ n ∧
      Dictionary.ValuesBounded V (Dynamic.step s o).1 := ⟨hcard', hbnd'⟩
  refine ⟨?_, ?_⟩
  · simp [twoCellDictScheme, ProbeTree.run_bind, run_readMem2,
      decodeBoundedMem_apply hfit hcard hbnd, dite_eq_left hcond, run_writeMem2]
  · simp [twoCellDictScheme, ProbeTree.probes_bind, probes_readMem2, run_readMem2,
      probes_writeMem2]

/-- Certified `StateTransitionImpl` bundling `twoCellDictScheme` with worst-case charge `4`. -/
noncomputable def twoCellDictImpl {U V n w : ℕ}
    (hfit : Fintype.card (BoundedDict U V n) ≤ 2 ^ (2 * w)) :
    DataStructure.CellProbe.StateTransitionImpl (Dynamic.spec U V n) (twoCellDictScheme hfit)
      (Dictionary.empty U) :=
  DataStructure.CellProbe.StateTransitionImpl.ofFn
    (fun s m => ∃ (hcard : (Dictionary.dom s).card ≤ n) (hbnd : Dictionary.ValuesBounded V s),
      m = boundedDictEmb hfit (mkBoundedDict s hcard hbnd))
    (fun _ _ => 4)
    ⟨by simp, Dictionary.valuesBounded_empty U V, rfl⟩
    (step_exec := fun s m o hrep hvalid => by
      rcases hrep with ⟨hcard, hbnd, rfl⟩
      obtain ⟨hrun, hpr⟩ := twoCellDictScheme_step_run hfit hcard hbnd hvalid
      exact ⟨congrArg Prod.fst hrun, ⟨Dynamic.card_dom_step_le_of_valid hcard hvalid,
        Dynamic.valuesBounded_step_of_valid hbnd hvalid, congrArg Prod.snd hrun⟩, hpr⟩)

/-- `(twoCellDictScheme hfit).toIndexed` is exact on `validHistoriesUpTo U V n M` for every `M`. -/
theorem twoCellDictScheme_all_histories {U V n w : ℕ}
    (hfit : Fintype.card (BoundedDict U V n) ≤ 2 ^ (2 * w)) (M : ℕ) :
    ∀ ops ∈ validHistoriesUpTo U V n M,
      ((twoCellDictScheme hfit).toIndexed.runSeq ops).1 =
        ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2 :=
  fun ops hops => ((twoCellDictImpl hfit).runSeq_ofFn ops hops.1).1

/-- Zero-error oblivious sequence contract for `Randomized.Scheme.ofDeterministic` on
`twoCellDictScheme`. -/
theorem twoCellDict_contract {U V n w : ℕ}
    (hfit : Fintype.card (BoundedDict U V n) ≤ 2 ^ (2 * w)) (M : ℕ) :
    ∀ ops ∈ validHistoriesUpTo U V n M,
      ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
        ops (((Cslib.CellProbe.Randomized.Scheme.ofDeterministic (twoCellDictScheme hfit)).runSeq
          ops).map Prod.fst) := by
  have hC :=
    ((twoCellDictImpl hfit).toObliviousSequenceImpl (fun _ => 4)
      (fun _ _ _ => le_rfl)).contract_runSeq
  intro ops hops
  exact hC (by simpa [StateTransitionSpec.toObliviousSequenceSpec] using hops.1)

/-! ### 2. Concrete Instantiation of Section 8.1 Lemma 8.1 (`queryFreeInnerDist`) -/

/-- State-count capacity fit for `(U = 16, V = 2 ^ 40, n = 4, w = 86)`. -/
theorem hfit_16_40_4 : Fintype.card (BoundedDict 16 (2 ^ 40) 4) ≤ 2 ^ (2 * 86) := by
  rw [card_boundedDict]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ]
  have hc0 : (16 : ℕ).choose 0 = 1 := by decide
  have hc1 : (16 : ℕ).choose 1 = 16 := by decide
  have hc2 : (16 : ℕ).choose 2 = 120 := by decide
  have hc3 : (16 : ℕ).choose 3 = 560 := by decide
  have hc4 : (16 : ℕ).choose 4 = 1820 := by decide
  rw [hc0, hc1, hc2, hc3, hc4]; norm_num

open Classical in
/-- Concrete ground instantiation of Lemma 8.1 (`prob_isModeSeedConsistent_queryFreeInnerDist_le`)
and Claim 4.2 (`expected_card_modeConsistent_segmentRest_lt_half_le`) on `twoCellDictScheme` at
`(U = 16, V = 2 ^ 40, n = 4, m = 2, cells = 2, w = 86)` in update-only mode (`withQueries = false`),
discharging every space, budget, and correctness premise. -/
theorem lemma8_1_queryFreeInnerDist_concrete :
    let D := (twoCellDictScheme hfit_16_40_4).toIndexed
    (((queryFreeInnerDist (V := 2 ^ 40) 0 2 0 (by decide : 3 * 4 ≤ 16) Nat.one_le_two_pow
        (by decide : 0 ≤ 2) (by decide : 0 + 2 ≤ 4)).map fun sb =>
          decide (IsModeSeedConsistent false D 0 2 (by decide) (1 / 100) 1 sb.1 sb.2))
        true).toReal ≤ (16 : ℝ) ^ (-(1 / 100 : ℝ) * (2 : ℝ)) ∧
    (haveI : Nonempty (HardKeyValSeed 16 (2 ^ 40) 4) :=
      ⟨⟨Fin.castLEEmb (by decide), fun _ => ⟨0, Nat.two_pow_pos 40⟩, 1⟩⟩
     (∑ s : HardKeyValSeed 16 (2 ^ 40) 4,
        ((PMF.uniformOfFintype (HardKeyValSeed 16 (2 ^ 40) 4)) s).toReal *
          ((((((s.insertedSet 0 4 (by decide)).powersetCard 2).filter fun B =>
            (s.insertedSet 0 2 (by decide) ∩ B).card < 2 / 2).filter
            (IsModeSeedConsistent false D 0 2 (by decide) (1 / 100) 1 s)).card : ℕ) : ℝ)) ≤
        ((4 : ℕ).choose 2 : ℝ) * (16 : ℝ) ^ (-(1 / 100 : ℝ) * (2 : ℝ))) := by
  intro D
  have hlog16 : Real.logb 2 ((16 : ℕ) : ℝ) = 4 := by
    rw [Nat.cast_ofNat, show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num), mul_one]; norm_num
  have hlogV : Real.logb 2 ((2 ^ 40 : ℕ) : ℝ) = 40 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num), mul_one]; norm_num
  have hlog4 : Real.logb 2 ((16 : ℝ) / (4 : ℝ)) = 2 := by
    rw [show (16 : ℝ) / (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num), mul_one]; norm_num
  have hspace : ((2 * 86 : ℕ) : ℝ) ≤ benchmarkBits 16 (2 ^ 40) 4 + 2 := by
    have hc4 : (16 : ℕ).choose 4 = 1820 := by decide
    have hch : (10 : ℝ) ≤ Real.logb 2 ((16 : ℕ).choose 4 : ℝ) := by
      have hle : ((2 : ℝ) ^ (10 : ℕ)) ≤ ((16 : ℕ).choose 4 : ℝ) := by rw [hc4]; norm_num
      have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hle
      rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one, Nat.cast_ofNat] at hl
    rw [benchmarkBits_eq, hlogV]
    push_cast at hch ⊢; linarith
  have hbudget : 2 * (2 : ℝ) + 7 * (2 : ℝ) + 2 * (2 : ℝ) * (1 : ℝ) +
      (1 / 100 : ℝ) * (2 : ℝ) * ((86 : ℕ) : ℝ) +
      2 * (1 / 100 : ℝ) * (2 : ℝ) * Real.logb 2 (16 : ℕ) ≤
      ((2 : ℝ) / 2) * Real.logb 2 (2 ^ 40 : ℕ) - (2 : ℝ) * Real.logb 2 ((16 : ℝ) / (4 : ℝ)) := by
    rw [hlog16, hlogV, hlog4]; norm_num
  have hcorr := twoCellDictScheme_all_histories hfit_16_40_4 13
  exact ⟨prob_isModeSeedConsistent_queryFreeInnerDist_le false (by decide) Nat.one_le_two_pow
      le_rfl (by decide) (by decide) (by decide) hspace hbudget hcorr,
    expected_card_modeConsistent_segmentRest_lt_half_le false (by decide) Nat.one_le_two_pow
      le_rfl (by decide) (by decide) (by decide) hspace hbudget hcorr⟩

/-! ### 3. Concrete Instantiations for Theorems 1.1 & 1.2
(`U = 9, V = 2, n = 2, cells = 2, w = 4`) -/

/-- State-count capacity fit for `(U = 9, V = 2, n = 2, w = 4)`: `1 + 18 + 144 = 163 ≤ 256`. -/
theorem hfit_9_2_2 : Fintype.card (BoundedDict 9 2 2) ≤ 2 ^ (2 * 4) := by
  rw [card_boundedDict]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ]
  have hc0 : (9 : ℕ).choose 0 = 1 := by decide
  have hc1 : (9 : ℕ).choose 1 = 9 := by decide
  have hc2 : (9 : ℕ).choose 2 = 36 := by decide
  rw [hc0, hc1, hc2]; norm_num

private theorem hw_9_2 : ((4 : ℕ) : ℝ) ≤ 1 * (Real.logb 2 (9 : ℕ) + Real.logb 2 (2 : ℕ)) := by
  have hlog9 : (3 : ℝ) ≤ Real.logb 2 (9 : ℝ) := by
    have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity)
      (show ((2 : ℝ) ^ (3 : ℕ)) ≤ (9 : ℝ) by norm_num)
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one, Nat.cast_ofNat] at hl
  have hlog2 : Real.logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
  push_cast; linarith

private theorem hspace_9_2_2 : ((2 * 4 : ℕ) : ℝ) ≤ benchmarkBits 9 2 2 + 1 := by
  have hc2 : (9 : ℕ).choose 2 = 36 := by decide
  have hch : (5 : ℝ) ≤ Real.logb 2 ((9 : ℕ).choose 2 : ℝ) := by
    have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity)
      (show ((2 : ℝ) ^ (5 : ℕ)) ≤ ((9 : ℕ).choose 2 : ℝ) by rw [hc2]; norm_num)
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one, Nat.cast_ofNat] at hl
  have hlog2 : Real.logb 2 ((2 : ℕ) : ℝ) = 1 := by
    rw [Nat.cast_ofNat]; exact Real.logb_self_eq_one (by norm_num)
  rw [benchmarkBits_eq, hlog2]; push_cast at hch ⊢; linarith

/-- Concrete instantiations of all four Theorem 1.1 / 3.1 endpoints
(`det_expectedSeqProbes_ge_of_iterLog_redundancy`, `expectedSeqProbes_ge_of_iterLog_redundancy`,
`det_expectedSeqProbes_ge_iterLogStar`, `expectedSeqProbes_ge_iterLogStar`) on `twoCellDictScheme`
at `(U = 9, V = 2, n = 2, k = 1, cells = 2, w = 4)` discharging every hypothesis. -/
theorem theorem1_1_concrete_instantiations :
    let D := (twoCellDictScheme hfit_9_2_2).toIndexed
    let P := Cslib.CellProbe.Randomized.Scheme.ofDeterministic (twoCellDictScheme hfit_9_2_2)
    (∃ c > 0, c * 2 ≤
      ∑' ops, (insertQueryDeleteDist 9 2 2 (by decide) (by decide) ops).toReal *
        (D.seqProbes ops : ℝ)) ∧
    (∃ c > 0, ENNReal.ofReal (c * 2) ≤
      ∑' ops, insertQueryDeleteDist 9 2 2 (by decide) (by decide) ops *
        P.expectedSeqProbes ops) ∧
    (∃ c > 0, c * 2 * (Nat.logStar 2 : ℝ) ≤
      ∑' ops, (insertQueryDeleteDist 9 2 2 (by decide) (by decide) ops).toReal *
        (D.seqProbes ops : ℝ)) ∧
    (∃ c > 0, ENNReal.ofReal (c * 2 * (Nat.logStar 2 : ℝ)) ≤
      ∑' ops, insertQueryDeleteDist 9 2 2 (by decide) (by decide) ops *
        P.expectedSeqProbes ops) := by
  dsimp only
  have hpoly : (2 : ℝ) ^ ((1 : ℝ) + 1) ≤ (9 : ℝ) := by norm_num
  have hk_hi : 1 ≤ Nat.logStar 2 := by decide
  have hsp_iter : ((2 * 4 : ℕ) : ℝ) ≤
      benchmarkBits 9 2 2 + 1 * (2 : ℝ) * ((max (Nat.iterLog 1 2) 1 : ℕ) : ℝ) := by
    have h1 : (1 : ℝ) ≤ 1 * (2 : ℝ) * ((max (Nat.iterLog 1 2) 1 : ℕ) : ℝ) := by
      have : 1 ≤ max (Nat.iterLog 1 2) 1 := le_max_right _ _
      have hr : (1 : ℝ) ≤ ((max (Nat.iterLog 1 2) 1 : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    linarith [hspace_9_2_2]
  have hsp_star : ((2 * 4 : ℕ) : ℝ) ≤ benchmarkBits 9 2 2 + 1 * (2 : ℝ) := by
    linarith [hspace_9_2_2]
  have hcorrD := twoCellDictScheme_all_histories hfit_9_2_2 9
  have hcorrP := twoCellDict_contract hfit_9_2_2 9
  let P := Cslib.CellProbe.Randomized.Scheme.ofDeterministic (twoCellDictScheme hfit_9_2_2)
  obtain ⟨c₁, hc₁, hd₁⟩ := det_expectedSeqProbes_ge_of_iterLog_redundancy
    (α := 1) (c_R := 1) (c_w := 1) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨c₂, hc₂, hr₁⟩ := expectedSeqProbes_ge_of_iterLog_redundancy
    (α := 1) (c_R := 1) (c_w := 1) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨c₃, hc₃, hd₂⟩ := det_expectedSeqProbes_ge_iterLogStar
    (α := 1) (c_R := 1) (c_w := 1) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨c₄, hc₄, hr₂⟩ := expectedSeqProbes_ge_iterLogStar
    (α := 1) (c_R := 1) (c_w := 1) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨⟨c₁, hc₁, ?_⟩, ⟨c₂, hc₂, ?_⟩, ⟨c₃, hc₃, ?_⟩, ⟨c₄, hc₄, ?_⟩⟩
  · have h := hd₁ (by decide : 2 ≤ 2) (by decide : 4 * 2 ≤ 9) hpoly (by decide : 1 ≤ 2)
      le_rfl hk_hi hw_9_2 hsp_iter hcorrD
    rw [Nat.cast_ofNat, Nat.cast_one, mul_one] at h; exact h
  · have h := hr₁ (by decide : 2 ≤ 2) (by decide : 4 * 2 ≤ 9) hpoly (by decide : 1 ≤ 2)
      le_rfl hk_hi hw_9_2 hsp_iter P hcorrP
    rw [Nat.cast_ofNat, Nat.cast_one, mul_one] at h; exact h
  · have h := hd₂ (by decide : 2 ≤ 2) (by decide : 4 * 2 ≤ 9) hpoly (by decide : 1 ≤ 2)
      hw_9_2 hsp_star hcorrD
    rw [Nat.cast_ofNat] at h; exact h
  · have h := hr₂ (by decide : 2 ≤ 2) (by decide : 4 * 2 ≤ 9) hpoly (by decide : 1 ≤ 2)
      hw_9_2 hsp_star P hcorrP
    rw [Nat.cast_ofNat] at h; exact h

/-- Concrete instantiations of all four Theorem 1.2 / 6.1 and combined endpoints
(`det_expectedSeqProbes_ge_of_sublinear_redundancy`,
`expectedSeqProbes_ge_of_sublinear_redundancy`,
`det_expectedSeqProbes_ge_iterLogStar_add_log_div`,
`expectedSeqProbes_ge_iterLogStar_add_log_div`) on `twoCellDictScheme` at
`(U = 9, V = 2, n = 2, cells = 2, w = 4, R = 1)` where `log₂(2 / max 1 1) = 1 > 0`. -/
theorem theorem1_2_concrete_instantiations :
    let D := (twoCellDictScheme hfit_9_2_2).toIndexed
    let P := Cslib.CellProbe.Randomized.Scheme.ofDeterministic (twoCellDictScheme hfit_9_2_2)
    (∃ c > 0, c * 2 ≤
      ∑' ops, (insertQueryDeleteDist 9 2 2 (by decide) (by decide) ops).toReal *
        (D.seqProbes ops : ℝ)) ∧
    (∃ c > 0, ENNReal.ofReal (c * 2) ≤
      ∑' ops, insertQueryDeleteDist 9 2 2 (by decide) (by decide) ops *
        P.expectedSeqProbes ops) ∧
    (∃ c > 0, c * 4 ≤
      ∑' ops, (insertQueryDeleteDist 9 2 2 (by decide) (by decide) ops).toReal *
        (D.seqProbes ops : ℝ)) ∧
    (∃ c > 0, ENNReal.ofReal (c * 4) ≤
      ∑' ops, insertQueryDeleteDist 9 2 2 (by decide) (by decide) ops *
        P.expectedSeqProbes ops) := by
  dsimp only
  have hpoly : (2 : ℝ) ^ ((1 : ℝ) + 1) ≤ (9 : ℝ) := by norm_num
  have hlog_div : Real.logb 2 (((2 : ℕ) : ℝ) / max (1 : ℝ) 1) = 1 := by
    rw [max_self, Nat.cast_ofNat, div_one]; exact Real.logb_self_eq_one (by norm_num)
  have hls2 : Nat.logStar 2 = 1 := by decide
  have hcorrD := twoCellDictScheme_all_histories hfit_9_2_2 9
  have hcorrP := twoCellDict_contract hfit_9_2_2 9
  let P := Cslib.CellProbe.Randomized.Scheme.ofDeterministic (twoCellDictScheme hfit_9_2_2)
  obtain ⟨c₁, hc₁, hd₁⟩ := det_expectedSeqProbes_ge_of_sublinear_redundancy
    (α := 1) (c_w := 1) (by norm_num) (by norm_num)
  obtain ⟨c₂, hc₂, hr₁⟩ := expectedSeqProbes_ge_of_sublinear_redundancy
    (α := 1) (c_w := 1) (by norm_num) (by norm_num)
  obtain ⟨c₃, hc₃, hd₂⟩ := det_expectedSeqProbes_ge_iterLogStar_add_log_div
    (α := 1) (c_R := 1) (c_w := 1) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨c₄, hc₄, hr₂⟩ := expectedSeqProbes_ge_iterLogStar_add_log_div
    (α := 1) (c_R := 1) (c_w := 1) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨⟨c₁, hc₁, ?_⟩, ⟨c₂, hc₂, ?_⟩, ⟨c₃, hc₃, ?_⟩, ⟨c₄, hc₄, ?_⟩⟩
  · have h := hd₁ (R := 1) (by decide : 2 ≤ 2) (by decide : 4 * 2 ≤ 9) hpoly (by decide : 1 ≤ 2)
      (by norm_num) hw_9_2 hspace_9_2_2 hcorrD
    rw [hlog_div, Nat.cast_ofNat, mul_one] at h; exact h
  · have h := hr₁ (R := 1) (by decide : 2 ≤ 2) (by decide : 4 * 2 ≤ 9) hpoly (by decide : 1 ≤ 2)
      (by norm_num) hw_9_2 hspace_9_2_2 P hcorrP
    rw [hlog_div, Nat.cast_ofNat, mul_one] at h; exact h
  · have h := hd₂ (R := 1) (by decide : 2 ≤ 2) (by decide : 4 * 2 ≤ 9) hpoly (by decide : 1 ≤ 2)
      (by norm_num) hw_9_2 hspace_9_2_2 hcorrD
    rw [hlog_div, hls2, Nat.cast_ofNat, Nat.cast_one, max_eq_right zero_le_one] at h
    linarith
  · have h := hr₂ (R := 1) (by decide : 2 ≤ 2) (by decide : 4 * 2 ≤ 9) hpoly (by decide : 1 ≤ 2)
      (by norm_num) hw_9_2 hspace_9_2_2 P hcorrP
    rw [hlog_div, hls2, Nat.cast_ofNat, Nat.cast_one, max_eq_right zero_le_one,
      show c₄ * 2 * (1 + 1) = c₄ * 4 by ring] at h
    exact h

/-! ### 4. Concrete Instantiations for Theorem 1.3 (`U = 6, V = 128, n = 2, cells = 2, w = 9`) -/

/-- State-count capacity fit for `(U = 6, V = 128, n = 2, w = 9)`: `246529 ≤ 262144`. -/
theorem hfit_6_128_2 : Fintype.card (BoundedDict 6 128 2) ≤ 2 ^ (2 * 9) := by
  rw [card_boundedDict]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ]
  have hc0 : (6 : ℕ).choose 0 = 1 := by decide
  have hc1 : (6 : ℕ).choose 1 = 6 := by decide
  have hc2 : (6 : ℕ).choose 2 = 15 := by decide
  rw [hc0, hc1, hc2]; norm_num

private theorem hw_6_128 : ((9 : ℕ) : ℝ) ≤ 1 * (Real.logb 2 (6 : ℕ) + Real.logb 2 (128 : ℕ)) := by
  have hlog6 : (2 : ℝ) ≤ Real.logb 2 (6 : ℝ) := by
    have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity)
      (show ((2 : ℝ) ^ (2 : ℕ)) ≤ (6 : ℝ) by norm_num)
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one, Nat.cast_ofNat] at hl
  have hlog128 : Real.logb 2 (128 : ℝ) = 7 := by
    rw [show (128 : ℝ) = (2 : ℝ) ^ (7 : ℕ) by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num), mul_one]; norm_num
  push_cast; linarith

private theorem hspace_6_128_2 : ((2 * 9 : ℕ) : ℝ) ≤ benchmarkBits 6 128 2 + 1 := by
  have hc2 : (6 : ℕ).choose 2 = 15 := by decide
  have hch : (3 : ℝ) ≤ Real.logb 2 ((6 : ℕ).choose 2 : ℝ) := by
    have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity)
      (show ((2 : ℝ) ^ (3 : ℕ)) ≤ ((6 : ℕ).choose 2 : ℝ) by rw [hc2]; norm_num)
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one, Nat.cast_ofNat] at hl
  have hlog128 : Real.logb 2 ((128 : ℕ) : ℝ) = 7 := by
    rw [Nat.cast_ofNat, show (128 : ℝ) = (2 : ℝ) ^ (7 : ℕ) by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num), mul_one]; norm_num
  rw [benchmarkBits_eq, hlog128]; push_cast at hch ⊢; linarith

/-- Concrete instantiations of all eight Theorem 1.3(1)–(2) update-only endpoints on
`twoCellDictScheme` at `(U = 6, V = 128, n = 2, k = 1, cells = 2, w = 9, R = 1)` discharging every
hypothesis (`6 ^ 3 = 216 ≤ 512 = 128 * 2 ^ 2`, `3 * 2 ≤ 6`, `9 ≤ log₂ 6 + log₂ 128`,
`18 ≤ benchmarkBits 6 128 2 + 1`, and `log₂(2 / max 1 1) = 1 > 0`). -/
theorem theorem1_3_concrete_instantiations :
    let D := (twoCellDictScheme hfit_6_128_2).toIndexed
    let P := Cslib.CellProbe.Randomized.Scheme.ofDeterministic (twoCellDictScheme hfit_6_128_2)
    (∃ c > 0, c * 2 ≤
      ∑' ops, (insertDeleteDist 6 128 2 (by decide) (by decide) ops).toReal *
        (D.seqProbes ops : ℝ)) ∧
    (∃ c > 0, ENNReal.ofReal (c * 2) ≤
      ∑' ops, insertDeleteDist 6 128 2 (by decide) (by decide) ops *
        P.expectedSeqProbes ops) ∧
    (∃ c > 0, c * 2 * (Nat.logStar 2 : ℝ) ≤
      ∑' ops, (insertDeleteDist 6 128 2 (by decide) (by decide) ops).toReal *
        (D.seqProbes ops : ℝ)) ∧
    (∃ c > 0, ENNReal.ofReal (c * 2 * (Nat.logStar 2 : ℝ)) ≤
      ∑' ops, insertDeleteDist 6 128 2 (by decide) (by decide) ops *
        P.expectedSeqProbes ops) ∧
    (∃ c > 0, c * 2 ≤
      ∑' ops, (insertDeleteDist 6 128 2 (by decide) (by decide) ops).toReal *
        (D.seqProbes ops : ℝ)) ∧
    (∃ c > 0, ENNReal.ofReal (c * 2) ≤
      ∑' ops, insertDeleteDist 6 128 2 (by decide) (by decide) ops *
        P.expectedSeqProbes ops) ∧
    (∃ c > 0, c * 4 ≤
      ∑' ops, (insertDeleteDist 6 128 2 (by decide) (by decide) ops).toReal *
        (D.seqProbes ops : ℝ)) ∧
    (∃ c > 0, ENNReal.ofReal (c * 4) ≤
      ∑' ops, insertDeleteDist 6 128 2 (by decide) (by decide) ops *
        P.expectedSeqProbes ops) := by
  dsimp only
  have hV_lo : (6 : ℝ) ^ ((2 : ℝ) + 1) ≤ (128 : ℝ) * (2 : ℝ) ^ 2 := by norm_num
  have hk_hi : 1 ≤ Nat.logStar 2 := by decide
  have hls2 : Nat.logStar 2 = 1 := by decide
  have hlog_div : Real.logb 2 (((2 : ℕ) : ℝ) / max (1 : ℝ) 1) = 1 := by
    rw [max_self, Nat.cast_ofNat, div_one]; exact Real.logb_self_eq_one (by norm_num)
  have hsp_iter : ((2 * 9 : ℕ) : ℝ) ≤
      benchmarkBits 6 128 2 + 1 * (2 : ℝ) * ((max (Nat.iterLog 1 2) 1 : ℕ) : ℝ) := by
    have h1 : (1 : ℝ) ≤ 1 * (2 : ℝ) * ((max (Nat.iterLog 1 2) 1 : ℕ) : ℝ) := by
      have : 1 ≤ max (Nat.iterLog 1 2) 1 := le_max_right _ _
      have hr : (1 : ℝ) ≤ ((max (Nat.iterLog 1 2) 1 : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    linarith [hspace_6_128_2]
  have hsp_star : ((2 * 9 : ℕ) : ℝ) ≤ benchmarkBits 6 128 2 + 1 * (2 : ℝ) := by
    linarith [hspace_6_128_2]
  have hcorrD := twoCellDictScheme_all_histories hfit_6_128_2 7
  have hcorrP := twoCellDict_contract hfit_6_128_2 7
  let P := Cslib.CellProbe.Randomized.Scheme.ofDeterministic (twoCellDictScheme hfit_6_128_2)
  obtain ⟨c₁, hc₁, hd₁⟩ := det_expectedSeqProbes_update_ge_iterLog
    (α_V := 1) (c_R := 1) (c_w := 1) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨c₂, hc₂, hr₁⟩ := expectedSeqProbes_update_ge_iterLog
    (α_V := 1) (c_R := 1) (c_w := 1) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨c₃, hc₃, hd₂⟩ := det_expectedSeqProbes_update_ge_iterLogStar
    (α_V := 1) (c_R := 1) (c_w := 1) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨c₄, hc₄, hr₂⟩ := expectedSeqProbes_update_ge_iterLogStar
    (α_V := 1) (c_R := 1) (c_w := 1) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨c₅, hc₅, hd₃⟩ := det_expectedSeqProbes_update_ge_sublinear
    (α_V := 1) (c_w := 1) (by norm_num) (by norm_num)
  obtain ⟨c₆, hc₆, hr₃⟩ := expectedSeqProbes_update_ge_sublinear
    (α_V := 1) (c_w := 1) (by norm_num) (by norm_num)
  obtain ⟨c₇, hc₇, hd₄⟩ := det_expectedSeqProbes_update_ge_iterLogStar_add_log_div
    (α_V := 1) (c_R := 1) (c_w := 1) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨c₈, hc₈, hr₄⟩ := expectedSeqProbes_update_ge_iterLogStar_add_log_div
    (α_V := 1) (c_R := 1) (c_w := 1) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨⟨c₁, hc₁, ?_⟩, ⟨c₂, hc₂, ?_⟩, ⟨c₃, hc₃, ?_⟩, ⟨c₄, hc₄, ?_⟩,
    ⟨c₅, hc₅, ?_⟩, ⟨c₆, hc₆, ?_⟩, ⟨c₇, hc₇, ?_⟩, ⟨c₈, hc₈, ?_⟩⟩
  · have h := hd₁ (by decide : 2 ≤ 2) (by decide : 3 * 2 ≤ 6) (by decide : 1 ≤ 128) hV_lo
      le_rfl hk_hi hw_6_128 hsp_iter hcorrD
    rw [Nat.cast_ofNat, Nat.cast_one, mul_one] at h; exact h
  · have h := hr₁ (by decide : 2 ≤ 2) (by decide : 3 * 2 ≤ 6) (by decide : 1 ≤ 128) hV_lo
      le_rfl hk_hi hw_6_128 hsp_iter P hcorrP
    rw [Nat.cast_ofNat, Nat.cast_one, mul_one] at h; exact h
  · have h := hd₂ (by decide : 2 ≤ 2) (by decide : 3 * 2 ≤ 6) (by decide : 1 ≤ 128) hV_lo
      hw_6_128 hsp_star hcorrD
    rw [Nat.cast_ofNat] at h; exact h
  · have h := hr₂ (by decide : 2 ≤ 2) (by decide : 3 * 2 ≤ 6) (by decide : 1 ≤ 128) hV_lo
      hw_6_128 hsp_star P hcorrP
    rw [Nat.cast_ofNat] at h; exact h
  · have h := hd₃ (R := 1) (by decide : 2 ≤ 2) (by decide : 3 * 2 ≤ 6) (by decide : 1 ≤ 128) hV_lo
      (by norm_num) hw_6_128 hspace_6_128_2 hcorrD
    rw [hlog_div, Nat.cast_ofNat, mul_one] at h; exact h
  · have h := hr₃ (R := 1) (by decide : 2 ≤ 2) (by decide : 3 * 2 ≤ 6) (by decide : 1 ≤ 128) hV_lo
      (by norm_num) hw_6_128 hspace_6_128_2 P hcorrP
    rw [hlog_div, Nat.cast_ofNat, mul_one] at h; exact h
  · have h := hd₄ (R := 1) (by decide : 2 ≤ 2) (by decide : 3 * 2 ≤ 6) (by decide : 1 ≤ 128) hV_lo
      (by norm_num) hw_6_128 hspace_6_128_2 hcorrD
    rw [hlog_div, hls2, Nat.cast_ofNat, Nat.cast_one, max_eq_right zero_le_one] at h
    linarith
  · have h := hr₄ (R := 1) (by decide : 2 ≤ 2) (by decide : 3 * 2 ≤ 6) (by decide : 1 ≤ 128) hV_lo
      (by norm_num) hw_6_128 hspace_6_128_2 P hcorrP
    rw [hlog_div, hls2, Nat.cast_ofNat, Nat.cast_one, max_eq_right zero_le_one,
      show c₈ * 2 * (1 + 1) = c₈ * 4 by ring] at h
    exact h

/-! ### 5. Space-Benchmark, Combinatorial, Prefix-Free, and Entropy Bridge Checks -/

/-- Concrete checks of `optBits_le_benchmarkBits_add` (general `V = 3`) and
`optBits_two_pow_le_benchmarkBits_add_one` (power-of-two `V = 2 ^ 3` and key-only `V = 2 ^ 0`). -/
theorem optBits_bridge_checks_concrete :
    (Dynamic.optBits 8 3 4 : ℝ) ≤ benchmarkBits 8 3 4 + 4 + 1 ∧
      (Dynamic.optBits 8 (2 ^ 3) 4 : ℝ) ≤ benchmarkBits 8 (2 ^ 3) 4 + 1 ∧
      (Dynamic.optBits 8 (2 ^ 0) 4 : ℝ) ≤ benchmarkBits 8 (2 ^ 0) 4 + 1 :=
  ⟨optBits_le_benchmarkBits_add (by decide) (by decide),
   optBits_two_pow_le_benchmarkBits_add_one (by decide),
   optBits_two_pow_le_benchmarkBits_add_one (by decide)⟩

/-- Concrete checks of `Nat.prod_choose_partition_mul_pow_factorial`,
`Nat.choose_le_two_pow_mul_choose_sub_of_two_mul_le`,
`Cslib.logb_choose_sub_logb_sub_three_mul_choose_sub_le`,
`Cslib.BitString.length_encodeRestr_bool`, `Cslib.BitString.length_encodeRestr_fin_two_pow`,
`PMF.conditionalEntropy_le_add_conditionalEntropy`, and `PMF.tsum_toReal_map_mul_natCast`. -/
theorem combinatorics_coding_entropy_bridge_checks :
    (∏ i : Fin 2, ((2 - i.val) * 2).choose 2) * Nat.factorial 2 ^ 2 = (2 * 2).factorial ∧
    (10 : ℕ).choose 3 ≤ 2 ^ 2 * (10 - 2).choose 3 ∧
    Real.logb 2 ((12 : ℕ).choose 4) - Real.logb 2 ((12 - 3 * 2 : ℕ).choose (4 - 2)) ≤
      2 * Real.logb 2 ((12 : ℝ) / (4 : ℝ)) + 5 * 2 ∧
    (encodeRestr ({0, 1} : Finset (Fin 3)) (fun _ => true)).length =
      ({0, 1} : Finset (Fin 3)).card ∧
    (encodeRestr ({0, 1} : Finset (Fin 3)) (fun _ : Fin 3 => (0 : Fin (2 ^ 4)))).length =
      4 * ({0, 1} : Finset (Fin 3)).card ∧
    PMF.conditionalEntropy ((PMF.uniformOfFintype (Bool × Bool)).map fun x => (x.1, x.2)) ≤
      PMF.conditionalEntropy ((PMF.uniformOfFintype (Bool × Bool)).map fun x => (x.1, x.1 && x.2)) +
        PMF.conditionalEntropy
          ((PMF.uniformOfFintype (Bool × Bool)).map fun x => ((x.1, x.1 && x.2), x.2)) ∧
    (∑' n : ℕ, (((PMF.uniformOfFintype Bool).map fun b => if b then 3 else 1) n).toReal *
        (n : ℝ)) =
      ∑ b : Bool, ((PMF.uniformOfFintype Bool) b).toReal *
        ((if b then (3 : ℕ) else 1 : ℕ) : ℝ) :=
  ⟨Nat.prod_choose_partition_mul_pow_factorial 2 2,
   Nat.choose_le_two_pow_mul_choose_sub_of_two_mul_le (by decide) (by decide),
   by simpa using logb_choose_sub_logb_sub_three_mul_choose_sub_le (U := 12) (n := 4) (m := 2)
        (by decide) (by decide) (by decide),
   length_encodeRestr_bool _ _,
   length_encodeRestr_fin_two_pow _ 4 _,
   PMF.conditionalEntropy_le_add_conditionalEntropy (PMF.uniformOfFintype (Bool × Bool))
     Prod.fst (fun x => x.1 && x.2) Prod.snd,
   PMF.tsum_toReal_map_mul_natCast (PMF.uniformOfFintype Bool) (fun b => if b then 3 else 1) id⟩

end CslibFrontierTests.DictLowerBoundMultilevel
