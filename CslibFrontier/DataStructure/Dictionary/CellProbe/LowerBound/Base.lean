/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.CellProbe.OuterGame
import CslibFrontier.Foundations.Data.BitString.List.PrefixFree
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map

/-!
# Base `Ω(n)` Bound, `MetaTree` Aggregation, and `optBits` Bridges

Information-theoretic `optBits` bridges, `ENNReal`-to-`ℝ` expectation conversion, the linear base
lower bound `det_expectedSeqProbes_ge_linear`, and the multi-level `MetaTree` probe aggregation
theorem `det_expectedSeqProbes_ge_of_outer_tree`. Depends only on `OuterGame` (zero dependency on
Section 8.1 `ModifiedInner`).

## Main results

* `Cslib.DataStructure.Dictionary.CellProbe.optBits_le_benchmarkBits_add`,
  `Cslib.DataStructure.Dictionary.CellProbe.optBits_two_pow_le_benchmarkBits_add_one`: bridges from
  `Dynamic.optBits` to `benchmarkBits`.
* `Cslib.DataStructure.Dictionary.CellProbe.ofReal_le_tsum_seqProbes_of_toReal_le`: expectation
  transfer from `ℝ` sums to `ENNReal` `tsum`.
* `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_ge_linear`: `Ω(n)` lower bound.
* `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_ge_of_outer_tree`: multi-level
  `MetaTree` aggregation theorem.
-/

public section

open scoped BigOperators ENNReal

namespace Cslib.DataStructure.Dictionary.CellProbe

open Cslib.CellProbe Cslib.DataStructure Cslib.DataStructure.Dictionary
open Cslib.BitString Cslib.Probability

/-! ### Part B: Base `Ω(n)` Bound, Multi-Level `MetaTree` Aggregation, and `optBits` Bridges -/

/-- Bridge from `Dynamic.optBits` to `benchmarkBits` for general `1 ≤ V` (`n ≤ U`). -/
theorem optBits_le_benchmarkBits_add {U V n : ℕ} (hn : n ≤ U) (hV : 1 ≤ V) :
    (Dynamic.optBits U V n : ℝ) ≤ benchmarkBits U V n + (n : ℝ) + 1 := by
  have hc1 := (clog_two_lt_logb_add_one (Nat.choose_pos hn)).le
  have hc2 := (clog_two_lt_logb_add_one hV).le
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn_mul : (n : ℝ) * (Nat.clog 2 V : ℝ) ≤ (n : ℝ) * Real.logb 2 V + (n : ℝ) := by nlinarith
  simp only [Dynamic.optBits, benchmarkBits_eq, Nat.cast_add, Nat.cast_mul]
  linarith

/-- Tight `+ 1`-bit bridge from `Dynamic.optBits` to `benchmarkBits` when `V = 2 ^ b` (including
key-only dictionaries `V = 1 = 2 ^ 0`). -/
theorem optBits_two_pow_le_benchmarkBits_add_one {U b n : ℕ} (hn : n ≤ U) :
    (Dynamic.optBits U (2 ^ b) n : ℝ) ≤ benchmarkBits U (2 ^ b) n + 1 := by
  have hc1 := (clog_two_lt_logb_add_one (Nat.choose_pos hn)).le
  have hc2 : Nat.clog 2 (2 ^ b) = b := Nat.clog_pow 2 b Nat.one_lt_two
  have hl2 : Real.logb 2 ((2 ^ b : ℕ) : ℝ) = (b : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  simp only [Dynamic.optBits, benchmarkBits_eq, Nat.cast_add, Nat.cast_mul, hc2]
  rw [hl2]
  linarith

/-- Lift a real-valued expected probe-count lower bound `L ≤ ∑' ops, (dist ops).toReal *
(D_det.seqProbes ops : ℝ)` into `ℝ≥0∞`: `ENNReal.ofReal L ≤ ∑' ops, dist ops *
(D_det.seqProbes ops : ℝ≥0∞)`. -/
theorem ofReal_le_tsum_seqProbes_of_toReal_le {Op : Type*} {Result : Op → Type}
    {cells w : ℕ} (dist : PMF (List Op)) (D_det : IndexedScheme Op Result cells w) {L : ℝ}
    (hL : L ≤ ∑' ops, (dist ops).toReal * (D_det.seqProbes ops : ℝ)) :
    ENNReal.ofReal L ≤ ∑' ops, dist ops * (D_det.seqProbes ops : ℝ≥0∞) := by
  set S : ℝ≥0∞ := ∑' ops, dist ops * (D_det.seqProbes ops : ℝ≥0∞)
  by_cases htop : S = ⊤
  · rw [htop]; exact le_top
  · rw [← ENNReal.ofReal_toReal htop]
    have htsum := ENNReal.tsum_toReal_eq (f := fun ops => dist ops * (D_det.seqProbes ops : ℝ≥0∞))
      fun ops => ENNReal.mul_ne_top (PMF.apply_ne_top dist ops) (ENNReal.natCast_ne_top _)
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at htsum
    exact ENNReal.ofReal_le_ofReal (hL.trans_eq htsum.symm)

private def swapInitKeySeed {U V n : ℕ} (i : Fin n) :
    HardKeyValSeed U V n ≃ HardKeyValSeed U V n :=
  let σ : Equiv.Perm (Fin (2 * n)) :=
    Equiv.swap ⟨i.val, by have := i.isLt; omega⟩ ⟨n + i.val, by have := i.isLt; omega⟩
  have hinv (s : HardKeyValSeed U V n) :
      (⟨σ.toEmbedding.trans (σ.toEmbedding.trans s.keys), s.kv, s.delPerm⟩ :
        HardKeyValSeed U V n) = s := by
    have hσm (m : Fin (2 * n)) : σ (σ m) = m := by
      dsimp only [σ]
      by_cases h1 : m = ⟨i.val, by have := i.isLt; omega⟩
      · subst h1; simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
      · by_cases h2 : m = ⟨n + i.val, by have := i.isLt; omega⟩
        · subst h2; simp only [Equiv.swap_apply_right, Equiv.swap_apply_left]
        · simp only [Equiv.swap_apply_of_ne_of_ne h1 h2]
    cases s; simp only [HardKeyValSeed.mk.injEq, and_true]
    refine DFunLike.ext _ _ fun m => ?_
    simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, hσm m]
  { toFun := fun s => ⟨σ.toEmbedding.trans s.keys, s.kv, s.delPerm⟩
    invFun := fun s => ⟨σ.toEmbedding.trans s.keys, s.kv, s.delPerm⟩
    left_inv := hinv
    right_inv := hinv }

@[simp]
private theorem swapInitKeySeed_keys {U V n : ℕ} (i : Fin n) (s : HardKeyValSeed U V n) :
    (swapInitKeySeed i s).keys =
      (Equiv.swap ⟨i.val, by have := i.isLt; omega⟩
        ⟨n + i.val, by have := i.isLt; omega⟩).toEmbedding.trans s.keys := rfl

@[simp]
private theorem swapInitKeySeed_kv {U V n : ℕ} (i : Fin n) (s : HardKeyValSeed U V n) :
    (swapInitKeySeed i s).kv = s.kv := rfl

@[simp]
private theorem swapInitKeySeed_delPerm {U V n : ℕ} (i : Fin n) (s : HardKeyValSeed U V n) :
    (swapInitKeySeed i s).delPerm = s.delPerm := rfl

private theorem take_n_modeOps_eq_initInsertSeq (withQueries : Bool) {U V n : ℕ}
    (s : HardKeyValSeed U V n) :
    (s.modeOps withQueries).take n = initInsertSeq s.keys (fun idx => s.kv (s.keys idx)) := by
  cases withQueries <;> exact List.take_left' (length_initInsertSeq _ _)

/-- Base unconditional `Ω(n)` expected cell-probe lower bound across all `2 * n ≤ U`, `1 ≤ V`,
`cells`, and `w`: every initial insertion `i : Fin n` must probe at least one cell on either `s`
or `swapInitKeySeed i s` in order for step-`n` memory to distinguish whether `s.keys i` was
inserted. -/
theorem det_expectedSeqProbes_ge_linear (withQueries : Bool) {U V n cells w : ℕ}
    (hU : 2 * n ≤ U) (hV : 1 ≤ V)
    {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (modeHorizon withQueries n + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) :
    ((n : ℝ) / 2) ≤
      ∑' ops, (modeDist withQueries U V n hU hV ops).toReal * (D_det.seqProbes ops : ℝ) := by
  classical
  let _ : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb hU, fun _ => ⟨0, hV⟩, 1⟩⟩
  let μ := PMF.uniformOfFintype (HardKeyValSeed U V n)
  have hexp : (∑' ops, (modeDist withQueries U V n hU hV ops).toReal * (D_det.seqProbes ops : ℝ)) =
      ∑ s, (μ s).toReal * (D_det.seqProbes (s.modeOps withQueries) : ℝ) := by
    rw [← map_modeOps_uniformOfFintype_hardKeyValSeed]
    exact PMF.tsum_toReal_map_mul_natCast μ (HardKeyValSeed.modeOps withQueries) _
  rw [hexp]
  let stepProbe (s : HardKeyValSeed U V n) (k : ℕ) : ℕ :=
    rangeProbes D_det 0 1 (s.modeOps withQueries) k (k + 1)
  have hsum_le_seq (s : HardKeyValSeed U V n) :
      (∑ i : Fin n, stepProbe s i.val) ≤ D_det.seqProbes (s.modeOps withQueries) := by
    have htel : ∀ m : ℕ, (∑ k ∈ Finset.range m, stepProbe s k) =
        rangeProbes D_det 0 1 (s.modeOps withQueries) 0 m := fun m => by
      induction m with
      | zero =>
        simp only [Finset.range_zero, Finset.sum_empty, rangeProbes, elemSlice, Nat.mul_zero,
          Nat.add_zero, Nat.sub_self, List.take_zero, List.drop_zero,
          IndexedScheme.probesInterval_nil]
      | succ m ih =>
        rw [Finset.sum_range_succ, ih,
          ← rangeProbes_append D_det 0 1 (s.modeOps withQueries) (Nat.zero_le m) (Nat.le_succ m)]
    rw [Fin.sum_univ_eq_sum_range, htel n]
    exact rangeProbes_le_seqProbes D_det 0 1 (s.modeOps withQueries) 0 n
  have hone_le_pair (i : Fin n) (s : HardKeyValSeed U V n) :
      1 ≤ stepProbe s i.val + stepProbe (swapInitKeySeed i s) i.val := by
    by_contra h0
    have hp₁ : stepProbe s i.val = 0 := by omega
    have hp₂ : stepProbe (swapInitKeySeed i s) i.val = 0 := by omega
    let s₂ := swapInitKeySeed i s
    let ops₁ := s.modeOps withQueries
    let ops₂ := s₂.modeOps withQueries
    have hget_eq (j : ℕ) (hj : j < n) (hne : j ≠ i.val) :
        (initInsertSeq s.keys (fun idx => s.kv (s.keys idx)))[j]? =
          (initInsertSeq s₂.keys (fun idx => s₂.kv (s₂.keys idx)))[j]? := by
      have hkey : s₂.keys ⟨j, by omega⟩ = s.keys ⟨j, by omega⟩ := by
        dsimp only [s₂]; rw [swapInitKeySeed_keys]
        simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
        congr 1
        refine Equiv.swap_apply_of_ne_of_ne (fun h => hne (congrArg Fin.val h)) fun h => ?_
        have hv := congrArg Fin.val h; dsimp only at hv; omega
      have hfr : (List.finRange n)[j]? = some ⟨j, hj⟩ := by
        rw [List.getElem?_eq_getElem (by simp only [List.length_finRange]; exact hj),
          List.getElem_finRange]
        rfl
      simp only [initInsertSeq, List.getElem?_map, hfr, Option.map_some, s₂, swapInitKeySeed_kv,
        hkey]
    have hops_raw {k : ℕ} (hk : k < n) (hne : k ≠ i.val) : ops₁[k]? = ops₂[k]? := by
      have h : (ops₁.take n)[k]? = (ops₂.take n)[k]? := by
        rw [take_n_modeOps_eq_initInsertSeq, take_n_modeOps_eq_initInsertSeq]
        exact hget_eq k hk hne
      rwa [List.getElem?_take_of_lt hk, List.getElem?_take_of_lt hk] at h
    have htake_i : ops₁.take i.val = ops₂.take i.val := List.ext_getElem? fun j => by
      rw [List.getElem?_take, List.getElem?_take]
      split_ifs with hj
      exacts [hops_raw (hj.trans i.isLt) hj.ne, rfl]
    have hslice_after : elemSlice 0 1 ops₁ (i.val + 1) n = elemSlice 0 1 ops₂ (i.val + 1) n := by
      simp only [elemSlice, Nat.zero_add, Nat.one_mul]
      refine List.ext_getElem? fun k => ?_
      rw [List.getElem?_take, List.getElem?_take, List.getElem?_drop, List.getElem?_drop]
      split_ifs with hk
      exacts [hops_raw (by omega) (by omega), rfl]
    have hmem_step_zero (s' : HardKeyValSeed U V n) (hp : stepProbe s' i.val = 0) :
        memAt D_det (s'.modeOps withQueries) (i.val + 1) =
          memAt D_det (s'.modeOps withQueries) i.val := by
      have hcard0 : (rangeProbedCells D_det 0 1 (s'.modeOps withQueries) i.val (i.val + 1)).card =
          0 := Nat.eq_zero_of_le_zero ((card_rangeProbedCells_le_rangeProbes D_det 0 1 _ _ _).trans
            hp.le)
      have hemp := Finset.card_eq_zero.mp hcard0
      have hm := memAt_eq_runInterval_elemSlice D_det 0 1 (s'.modeOps withQueries)
        (show i.val ≤ i.val + 1 by omega)
      simp only [Nat.zero_add, Nat.one_mul] at hm
      rw [hm]
      refine funext fun cell => D_det.nextMem_runInterval_eq_of_notMem_probedCellsInterval i.val _ _
        ?_
      have hnot : cell ∉ rangeProbedCells D_det 0 1 (s'.modeOps withQueries) i.val (i.val + 1) := by
        simp only [hemp, Finset.notMem_empty, not_false_eq_true]
      simpa only [rangeProbedCells, Nat.zero_add, Nat.one_mul] using hnot
    have hmem_i1 : memAt D_det ops₁ (i.val + 1) = memAt D_det ops₂ (i.val + 1) :=
      (hmem_step_zero s hp₁).trans
        ((congrArg (fun l => (D_det.runSeq l).2) htake_i :
            memAt D_det ops₁ i.val = memAt D_det ops₂ i.val).trans
          (hmem_step_zero s₂ hp₂).symm)
    have hmem_n : memAt D_det ops₁ n = memAt D_det ops₂ n := by
      have hm1 := memAt_eq_runInterval_elemSlice D_det 0 1 ops₁ i.isLt
      have hm2 := memAt_eq_runInterval_elemSlice D_det 0 1 ops₂ i.isLt
      simp only [Nat.zero_add, Nat.one_mul] at hm1 hm2
      rw [hm1, hm2, hmem_i1, hslice_after]
    have hdec (s' : HardKeyValSeed U V n) :
        decodeDict D_det n (memAt D_det (s'.modeOps withQueries) n) =
          (windowDict s'.permKeyEmb (fun idx => s'.kv (s'.permKeyEmb idx))
            0 (Nat.zero_le n)).val := by
      have hlen : ((s'.modeOps withQueries).take n).length = n := by
        simpa only [Nat.mul_zero, Nat.add_zero] using
          s'.length_take_modeOps withQueries (Nat.zero_le n)
      have hdec' := decodeDict_runSeq_eq hcorr
        (by simpa only [Nat.mul_zero, Nat.add_zero] using
          s'.validHistory_take_modeOps withQueries (Nat.zero_le n))
        (by rw [hlen]; cases withQueries <;>
          simp only [modeHorizon, modeStride, ↓reduceIte, Bool.false_eq_true] <;> omega)
      rw [hlen] at hdec'
      exact hdec'.trans (by
        simpa only [Nat.mul_zero, Nat.add_zero] using
          s'.run_take_modeOps_fst withQueries (Nat.zero_le n))
    have hdict_eq : (windowDict s.permKeyEmb (fun idx => s.kv (s.permKeyEmb idx)) 0
        (Nat.zero_le n)).val =
        (windowDict s₂.permKeyEmb (fun idx => s₂.kv (s₂.permKeyEmb idx)) 0 (Nat.zero_le n)).val :=
      (hdec s).symm.trans ((congrArg (decodeDict D_det n) hmem_n).trans (hdec s₂))
    let u := s.keys ⟨i.val, by have := i.isLt; omega⟩
    have hu1 : (windowDict s.permKeyEmb (fun idx => s.kv (s.permKeyEmb idx)) 0
        (Nat.zero_le n)).val u = some (s.kv u).val := by
      rw [windowDict_coe]
      let k₀ : Fin n := s.delPerm.symm i
      have hk₀ : windowEmb s.permKeyEmb 0 (Nat.zero_le n) k₀ = u := by
        simp only [windowEmb_apply, Nat.zero_add, HardKeyValSeed.permKeyEmb,
          Function.Embedding.trans_apply, Equiv.coe_toEmbedding, k₀,
          liftDelPerm_apply_lt s.delPerm k₀.isLt, s.delPerm.apply_symm_apply, u]
      rw [← hk₀, dictOfEmb_apply_self]
      simp only [windowVals_apply, windowEmb_apply]
    have hu2 : (windowDict s₂.permKeyEmb (fun idx => s₂.kv (s₂.permKeyEmb idx)) 0
        (Nat.zero_le n)).val u = none := by
      rw [windowDict_coe]
      refine dictOfEmb_apply_eq_none _ _ fun k heq => ?_
      dsimp only [s₂] at heq
      simp only [windowEmb_apply, Nat.zero_add, HardKeyValSeed.permKeyEmb, swapInitKeySeed_keys,
        swapInitKeySeed_delPerm, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
        liftDelPerm_apply_lt s.delPerm k.isLt, u] at heq
      have hinj := s.keys.injective heq
      have := i.isLt; have := (s.delPerm k).isLt
      rw [Equiv.swap_apply_def] at hinj
      split_ifs at hinj with h1 h2
      · simp only [Fin.ext_iff] at hinj; omega
      · simp only [Fin.ext_iff] at h2; omega
      · exact h1 hinj
    have hcon := (congrFun hdict_eq u).symm.trans hu1
    rw [hu2] at hcon; cases hcon
  have hstep_ge (i : Fin n) : (1 / 2 : ℝ) ≤ ∑ s, (μ s).toReal * (stepProbe s i.val : ℝ) := by
    have hswap_sum : (∑ s, (μ s).toReal * (stepProbe (swapInitKeySeed i s) i.val : ℝ)) =
        ∑ s, (μ s).toReal * (stepProbe s i.val : ℝ) := by
      conv_rhs => rw [← Equiv.sum_comp (swapInitKeySeed i)]
      simp only [μ, PMF.uniformOfFintype_apply]
    have h1 : (1 : ℝ) ≤ ∑ s, (μ s).toReal *
        ((stepProbe s i.val : ℝ) + (stepProbe (swapInitKeySeed i s) i.val : ℝ)) :=
      (PMF.sum_toReal μ).symm.le.trans (Finset.sum_le_sum fun s _ =>
        le_mul_of_one_le_right ENNReal.toReal_nonneg (by exact_mod_cast hone_le_pair i s))
    simp only [mul_add, Finset.sum_add_distrib, hswap_sum] at h1
    linarith
  calc ((n : ℝ) / 2) = ∑ _i : Fin n, (1 / 2 : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ ∑ i : Fin n, ∑ s, (μ s).toReal * (stepProbe s i.val : ℝ) :=
        Finset.sum_le_sum fun i _ => hstep_ge i
    _ = ∑ s, (μ s).toReal * (∑ i : Fin n, (stepProbe s i.val : ℝ)) := by
        rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
    _ ≤ ∑ s, (μ s).toReal * (D_det.seqProbes (s.modeOps withQueries) : ℝ) :=
        Finset.sum_le_sum fun s _ =>
          mul_le_mul_of_nonneg_left (by exact_mod_cast hsum_le_seq s) ENNReal.toReal_nonneg

/-- Multi-level `MetaTree` aggregation theorem ([LiLiangYuZhou2023], Section 3, Proof of
Theorem 3.1, p. 12 / PDF p. 13 and Section 6, Proof of Theorem 6.1, p. 26 / PDF p. 27): if across
levels `ℓ ∈ [1, H)` (`2 ≤ H`, with `T.blockSize (ℓ + 1) ≤ n / 2` so packed blocks cover `≥ n / 2`
meta-operations at every level) every node `(ℓ + 1, b)` satisfies the `OuterLemma` dichotomy at
`(γ, t = (H - 1) * (4 * γ / 25))`, then `E[seqProbes] ≥ (H - 1) * (γ / 400) * n`. -/
theorem det_expectedSeqProbes_ge_of_outer_tree (withQueries : Bool) {U V n cells w : ℕ}
    (hU : 2 * n ≤ U) (hV : 1 ≤ V)
    (T : MetaTree) (hT_hor : T.horizon = n) {H : ℕ} (hH : 2 ≤ H)
    (hblock_half : ∀ ℓ ∈ Finset.Ico 1 H, T.blockSize (ℓ + 1) ≤ n / 2)
    {γ : ℝ} (hγ : 0 < γ)
    {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (houter : ∀ ℓ ∈ Finset.Ico 1 H, ∀ b < T.nodeCount (ℓ + 1),
      (γ / 100) * (T.blockSize (ℓ + 1) : ℝ) ≤
          ∑' ops, (modeDist withQueries U V n hU hV ops).toReal *
            (T.nodeCost D_det n (modeStride withQueries) ops ℓ b : ℝ) ∨
        (1 / 16) * (T.blockSize (ℓ + 1) : ℝ) * (((H - 1 : ℕ) : ℝ) * (4 * γ / 25)) ≤
          ∑' ops, (modeDist withQueries U V n hU hV ops).toReal *
            (T.nodeProbes D_det n (modeStride withQueries) ops (ℓ + 1) b : ℝ)) :
    ((H - 1 : ℕ) : ℝ) * (γ / 400) * (n : ℝ) ≤
      ∑' ops, (modeDist withQueries U V n hU hV ops).toReal * (D_det.seqProbes ops : ℝ) := by
  classical
  let _ : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb hU, fun _ => ⟨0, hV⟩, 1⟩⟩
  let μ := PMF.uniformOfFintype (HardKeyValSeed U V n)
  let stride := modeStride withQueries
  let h1_real : ℝ := ((H - 1 : ℕ) : ℝ)
  have hh1_pos : 0 < h1_real := by dsimp [h1_real]; exact_mod_cast (show 0 < H - 1 by omega)
  have hexp_eq (c : List (Dynamic.Op U) → ℕ) :
      (∑' ops, (modeDist withQueries U V n hU hV ops).toReal * (c ops : ℝ)) =
        ∑ s, (μ s).toReal * (c (s.modeOps withQueries) : ℝ) := by
    rw [← map_modeOps_uniformOfFintype_hardKeyValSeed]
    exact PMF.tsum_toReal_map_mul_natCast μ (HardKeyValSeed.modeOps withQueries) c
  have hnode_comb (ℓ : ℕ) (hℓ : ℓ ∈ Finset.Ico 1 H) (b : ℕ)
      (hb : b ∈ Finset.range (T.nodeCount (ℓ + 1))) :
      (γ / 100) * (T.blockSize (ℓ + 1) : ℝ) ≤
        (∑ s, (μ s).toReal * (T.nodeCost D_det n stride (s.modeOps withQueries) ℓ b : ℝ)) +
          (1 / h1_real) *
            (∑ s, (μ s).toReal *
              (T.nodeProbes D_det n stride (s.modeOps withQueries) (ℓ + 1) b : ℝ)) := by
    have hcost_nn : 0 ≤ ∑ s, (μ s).toReal *
        (T.nodeCost D_det n stride (s.modeOps withQueries) ℓ b : ℝ) :=
      Finset.sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)
    have hprobe_nn : 0 ≤ ∑ s, (μ s).toReal *
        (T.nodeProbes D_det n stride (s.modeOps withQueries) (ℓ + 1) b : ℝ) :=
      Finset.sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)
    rcases houter ℓ hℓ b (Finset.mem_range.mp hb) with hc | hp
    · rw [hexp_eq] at hc
      have hnn : 0 ≤ (1 / h1_real) * ∑ s, (μ s).toReal *
          (T.nodeProbes D_det n stride (s.modeOps withQueries) (ℓ + 1) b : ℝ) :=
        mul_nonneg (by positivity) hprobe_nn
      linarith
    · rw [hexp_eq] at hp
      have hid : (1 / h1_real) *
          ((1 / 16) * (T.blockSize (ℓ + 1) : ℝ) * (h1_real * (4 * γ / 25))) =
          (γ / 100) * (T.blockSize (ℓ + 1) : ℝ) := by
        have hne : h1_real ≠ 0 := hh1_pos.ne'
        field_simp; ring
      have hdiv := mul_le_mul_of_nonneg_left hp (show 0 ≤ 1 / h1_real by positivity)
      dsimp only [h1_real] at hid hdiv
      linarith
  have hlevel_cover (ℓ : ℕ) (hℓ : ℓ ∈ Finset.Ico 1 H) :
      ((n : ℝ) / 2) ≤ ((T.nodeCount (ℓ + 1) * T.blockSize (ℓ + 1) : ℕ) : ℝ) := by
    have hbh : T.blockSize (ℓ + 1) ≤ T.horizon :=
      (hblock_half ℓ hℓ).trans ((Nat.div_le_self n 2).trans_eq hT_hor.symm)
    have hn_le : n ≤ 2 * (T.nodeCount (ℓ + 1) * T.blockSize (ℓ + 1)) :=
      hT_hor ▸ T.horizon_le_two_mul_nodeCount_mul_blockSize hbh
    have hn_r : (n : ℝ) ≤ 2 * ((T.nodeCount (ℓ + 1) * T.blockSize (ℓ + 1) : ℕ) : ℝ) := by
      exact_mod_cast hn_le
    linarith
  have hlhs_le : h1_real * (γ / 200) * (n : ℝ) ≤
      ∑ ℓ ∈ Finset.Ico 1 H, ∑ b ∈ Finset.range (T.nodeCount (ℓ + 1)),
        (γ / 100) * (T.blockSize (ℓ + 1) : ℝ) := by
    have hrow (ℓ : ℕ) (hℓ : ℓ ∈ Finset.Ico 1 H) :
        (γ / 200) * (n : ℝ) ≤
          ∑ _b ∈ Finset.range (T.nodeCount (ℓ + 1)), (γ / 100) * (T.blockSize (ℓ + 1) : ℝ) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hcov := hlevel_cover ℓ hℓ
      push_cast at hcov
      nlinarith
    calc h1_real * (γ / 200) * (n : ℝ)
        = ∑ _ℓ ∈ Finset.Ico 1 H, (γ / 200) * (n : ℝ) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]; dsimp [h1_real]; ring
      _ ≤ _ := Finset.sum_le_sum hrow
  have hcost_tot :
      (∑ ℓ ∈ Finset.Ico 1 H, ∑ b ∈ Finset.range (T.nodeCount (ℓ + 1)),
        ∑ s, (μ s).toReal * (T.nodeCost D_det n stride (s.modeOps withQueries) ℓ b : ℝ)) ≤
      ∑ s, (μ s).toReal * (D_det.seqProbes (s.modeOps withQueries) : ℝ) := by
    have hsub : Finset.Ico 1 H ⊆ Finset.range H := fun x hx =>
      Finset.mem_range.mpr (Finset.mem_Ico.mp hx).2
    have hpt (s : HardKeyValSeed U V n) :
        (∑ ℓ ∈ Finset.Ico 1 H, ∑ b ∈ Finset.range (T.nodeCount (ℓ + 1)),
          (T.nodeCost D_det n stride (s.modeOps withQueries) ℓ b : ℝ)) ≤
        (D_det.seqProbes (s.modeOps withQueries) : ℝ) := by
      have hnat : (∑ ℓ ∈ Finset.Ico 1 H, ∑ b ∈ Finset.range (T.nodeCount (ℓ + 1)),
          T.nodeCost D_det n stride (s.modeOps withQueries) ℓ b) ≤
          D_det.seqProbes (s.modeOps withQueries) :=
        (Finset.sum_le_sum_of_subset hsub).trans
          (T.sum_nodeCost_le_seqProbes_of_height D_det n stride (s.modeOps withQueries) H)
      exact_mod_cast hnat
    calc _ = ∑ s, (μ s).toReal *
            (∑ ℓ ∈ Finset.Ico 1 H, ∑ b ∈ Finset.range (T.nodeCount (ℓ + 1)),
              (T.nodeCost D_det n stride (s.modeOps withQueries) ℓ b : ℝ)) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ ≤ _ := Finset.sum_le_sum fun s _ =>
          mul_le_mul_of_nonneg_left (hpt s) ENNReal.toReal_nonneg
  have hprobe_tot :
      (∑ ℓ ∈ Finset.Ico 1 H, ∑ b ∈ Finset.range (T.nodeCount (ℓ + 1)),
        (1 / h1_real) * ∑ s, (μ s).toReal *
          (T.nodeProbes D_det n stride (s.modeOps withQueries) (ℓ + 1) b : ℝ)) ≤
      ∑ s, (μ s).toReal * (D_det.seqProbes (s.modeOps withQueries) : ℝ) := by
    have hrow (ℓ : ℕ) (_hℓ : ℓ ∈ Finset.Ico 1 H) :
        (∑ b ∈ Finset.range (T.nodeCount (ℓ + 1)),
          ∑ s, (μ s).toReal *
            (T.nodeProbes D_det n stride (s.modeOps withQueries) (ℓ + 1) b : ℝ)) ≤
        ∑ s, (μ s).toReal * (D_det.seqProbes (s.modeOps withQueries) : ℝ) := by
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun s _ => ?_
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      exact_mod_cast T.sum_nodeProbes_le_seqProbes D_det n stride (s.modeOps withQueries) (ℓ + 1)
    calc _ = (1 / h1_real) * ∑ ℓ ∈ Finset.Ico 1 H, ∑ b ∈ Finset.range (T.nodeCount (ℓ + 1)),
            ∑ s, (μ s).toReal *
              (T.nodeProbes D_det n stride (s.modeOps withQueries) (ℓ + 1) b : ℝ) := by
          simp_rw [← Finset.mul_sum]
      _ ≤ (1 / h1_real) * ∑ _ℓ ∈ Finset.Ico 1 H,
            ∑ s, (μ s).toReal * (D_det.seqProbes (s.modeOps withQueries) : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hrow) (by positivity)
      _ = ∑ s, (μ s).toReal * (D_det.seqProbes (s.modeOps withQueries) : ℝ) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
          have hne : h1_real ≠ 0 := hh1_pos.ne'
          dsimp [h1_real] at hne ⊢; field_simp
  have hsum_all :
      (∑ ℓ ∈ Finset.Ico 1 H, ∑ b ∈ Finset.range (T.nodeCount (ℓ + 1)),
        (γ / 100) * (T.blockSize (ℓ + 1) : ℝ)) ≤
      2 * ∑ s, (μ s).toReal * (D_det.seqProbes (s.modeOps withQueries) : ℝ) := by
    have h1 := Finset.sum_le_sum fun ℓ hℓ => Finset.sum_le_sum (hnode_comb ℓ hℓ)
    simp_rw [Finset.sum_add_distrib] at h1
    linarith
  rw [hexp_eq]
  linarith

end Cslib.DataStructure.Dictionary.CellProbe
