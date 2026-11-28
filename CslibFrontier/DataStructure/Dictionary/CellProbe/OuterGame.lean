/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.CellProbe.InnerGame
public import CslibFrontier.Probability.Entropy
import CslibFrontier.Foundations.Data.BitString.List.PrefixFree
import CslibFrontier.Foundations.Data.List.Counting
import CslibFrontier.Foundations.Data.Nat.Choose
import CslibFrontier.Foundations.Data.Nat.Choose.Real
import CslibFrontier.Probability.Coding.PrefixFreeEntropy
import CslibFrontier.Probability.Conditioning
import CslibFrontier.Probability.Divergence
import CslibFrontier.Probability.MinEntropy
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Multi-Round Outer Communication Game and Outer Lemma

Protocol 1, Claims 4.1–4.6, and Lemma 3.2 (`OuterLemma`) from Section 4 (with mode-parametric
support for Section 8's update-only game) of Li, Liang, Yu, and Zhou ([LiLiangYuZhou2023]; locators
below follow `arXiv:2306.02253v3`, where printed page `p` is PDF page `p + 1`).

Pinned source: [LiLiangYuZhou2023] (`arXiv:2306.02253v3`), Section 3, Lemma 3.2, p. 12 (PDF p. 13);
Section 4.1, Eq. (1), pp. 13–14 (PDF pp. 14–15); Section 4.2, Protocol 1 and Eqs. (2)–(3),
pp. 14–16 (PDF pp. 15–17); Section 4.3, Eq. (4), Claim 4.1, Eq. (5), Claim 4.2, Eq. (6),
Definition 4.3, Lemma 4.4, Claim 4.6, Eq. (7), and Eqs. (8)–(9), pp. 16–20 (PDF pp. 17–21);
Section 8, p. 27 (PDF p. 28).

Original formalization adaptations:
1. **Deterministic `c = 1` probe cap (`Sections 4.2, 5.1, and 5.2`):** `MetaTree.IsGoodSeg`,
   `IsQualified`, and `IsCappedConsistent` incorporate `|S_A^{[i]}|, |S_B| ≤ m_ℓ * t` directly,
   superseding Claim 4.5's per-segment expectation filtering while preventing conditional probe
   inflation on `{W = 1}` in Section 5.2 Eq. (11) and Section 8.1 Step 5 (`≤ (1 / 16) * λ_{ℓ+1}`
   probe-cap loss via Markov's inequality on `nodeProbes` in `MetaTree.sum_prob_not_isGoodSeg_le`).
2. **Independent `R_outer` and `R_inner` and child-segment `m_ℓ` alignment:**
   `outer_node_lower_bound` and `outer_lemma_insertQueryDelete` separate Step 1's end-memory
   entropy budget `R_outer` from the inner-game redundancy `R_inner`, and state the inner-game
   hypotheses at child-segment length `m_ℓ = T.blockSize ℓ` (matching Section 5 Lemma 5.1, p. 21 /
   PDF p. 22, where Lemma 3.2/4.4 on pp. 12, 18 / PDF pp. 13, 19 wrote `m_{ℓ+1}`).
3. **Mode-parametric `withQueries : Bool` (`stride = 3` vs. `stride = 2`):** sharing
   `kv : Fin U → Fin V` in Bob's prior observation (as in Section 8, p. 27 / PDF p. 28) leaves
   Eq. (1)'s partition entropy `log₂ m_{ℓ+1}! - λ_{ℓ+1} log₂ m_ℓ!` unchanged while reconstructing
   `S_end` uniformly across both `insertQueryDeleteDist` and `insertDeleteDist`.

## Main definitions

* `Cslib.DataStructure.Dictionary.CellProbe.benchmarkBits`: real-valued space benchmark
  `log₂ C(U, n) + n * log₂ V`.
* `Cslib.DataStructure.Dictionary.CellProbe.IsModeSeedConsistent`: mode-parametric inner-game
  seed consistency predicate (`withQueries : Bool`).

## Main results

* `Cslib.DataStructure.Dictionary.CellProbe.nodeStart_add_rest_le`: remaining child-segments
  horizon bound under `T.nodeStop (ℓ + 1) b ≤ n`.
* `Cslib.DataStructure.Dictionary.CellProbe.outer_node_lower_bound`,
  `Cslib.DataStructure.Dictionary.CellProbe.outer_lemma_insertQueryDelete`: mode-parametric Outer
  Lemma and Lemma 3.2 on `insertQueryDeleteDist` with independent `R_outer` and `R_inner`.

## References

* [T. Li, J. Liang, H. Yu and R. Zhou, *Tight Cell-Probe Lower Bounds for Dynamic Succinct
  Dictionaries*][LiLiangYuZhou2023], Sections 3, 4.1–4.3, 5.1, 5.2, and 8 (`arXiv:2306.02253v3`).
* [T. M. Cover, J. A. Thomas, *Elements of Information Theory*][CoverThomas2006]
* [L. G. Kraft, *A Device for Quantizing, Grouping, and Coding Amplitude-Modulated
  Pulses*][Kraft1949]
* [P. B. Miltersen, *Cell Probe Complexity — a Survey*][Miltersen1999]
* [A. C.-C. Yao, *Probabilistic Computations: Toward a Unified Measure of Complexity*][Yao1977]
-/

public section

namespace Cslib.DataStructure.Dictionary.CellProbe

open Cslib.CellProbe Cslib.DataStructure Cslib.DataStructure.Dictionary
open Cslib.BitString Cslib.Probability Cslib.Probability.Coding InformationTheory
open Finset (orderSubset orderSubset_apply image_orderSubset orderSubset_congr
  orderSubset_eq_of_embSetPermEquiv_fst image_perm_trans embSetPermEquiv
  embSetPermEquiv_symm_apply embSetPermEquiv_fst embSetPermEquiv_perm_trans)
open scoped BigOperators ENNReal

/-- Information-theoretic space benchmark `log₂ C(U, n) + n * log₂ V` in real bits
([LiLiangYuZhou2023], Section 3, p. 11 / PDF p. 12 and Section 7, p. 26 / PDF p. 27). -/
noncomputable def benchmarkBits (U V n : ℕ) : ℝ :=
  Real.logb 2 (U.choose n) + (n : ℝ) * Real.logb 2 V

@[simp]
theorem benchmarkBits_eq (U V n : ℕ) :
    benchmarkBits U V n = Real.logb 2 (U.choose n) + (n : ℝ) * Real.logb 2 V := by rfl

/-! ### Outer Game observations, Eq. (2) end-memory entropy, and Eq. (1) partition entropy -/

/-- Bob's prior observation at node `(ℓ + 1, b)` in the Outer Game ([LiLiangYuZhou2023],
Section 4.1, p. 14 / PDF p. 15 and Section 8, p. 27 / PDF p. 28):
`(C_st, A, d, π, kv)`. -/
private abbrev BobOuterObs (U V cells w F m : ℕ) : Type :=
  Mem cells w × Finset (Fin U) × (Fin (F * m) → Fin U) ×
    (Fin F → Equiv.Perm (Fin m)) × (Fin U → Fin V)

/-- Bob's observation extracted from `s : HardKeyValSeed U V n` at `[t_st, t_st + F * m)`. -/
private noncomputable def bobOuterObsOf (withQueries : Bool) {U V n cells w : ℕ}
    (D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w)
    (t_st F m : ℕ) (ht_end : t_st + F * m ≤ n) (s : HardKeyValSeed U V n) :
    BobOuterObs U V cells w F m :=
  (memAt D_det (s.modeOps withQueries) (n + modeStride withQueries * t_st),
   s.insertedSet t_st (F * m) ht_end,
   fun r => segDeletedKeys s.keys s.delPerm t_st (F * m) ht_end r,
   fun i => (embSetPermEquiv (Fin U) m
     (segInsertedKeys s.keys (t_st + i.val * m) m
       (by have := i.isLt; nlinarith))).2,
   s.kv)

/-- Ordered partition `(A^{[0]}, …, A^{[F - 1]})` of `A` that Bob must learn in Protocol 1. -/
private def outerTarget {U V n : ℕ} (t_st F m : ℕ) (ht_end : t_st + F * m ≤ n)
    (s : HardKeyValSeed U V n) : Fin F → Finset (Fin U) :=
  fun i => s.insertedSet (t_st + i.val * m) m (by have := i.isLt; nlinarith)

open Classical in
/-- Eq. (2) of [LiLiangYuZhou2023] (Section 4.2, p. 15 / PDF p. 16): given Bob's observation
`bobOuterObsOf`, the end-of-node memory `C_end` has conditional entropy at most `R_outer` whenever
`cells * w ≤ benchmarkBits U V n + R_outer`. -/
private theorem conditionalEntropy_endMem_le (withQueries : Bool) {U V n cells w : ℕ} {R_outer : ℝ}
    (hU : 2 * n ≤ U) (hV : 1 ≤ V)
    (hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R_outer)
    {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (modeHorizon withQueries n + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2)
    (t_st F m : ℕ) (ht_end : t_st + F * m ≤ n) :
    letI : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb hU, fun _ => ⟨0, hV⟩, 1⟩⟩
    let μ := PMF.uniformOfFintype (HardKeyValSeed U V n)
    let endMem (s : HardKeyValSeed U V n) :=
      memAt D_det (s.modeOps withQueries) (n + modeStride withQueries * (t_st + F * m))
    PMF.conditionalEntropy
      (μ.map fun s => (bobOuterObsOf withQueries D_det t_st F m ht_end s, endMem s)) ≤
      R_outer := by
  let _ : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb hU, fun _ => ⟨0, hV⟩, 1⟩⟩
  dsimp only
  set μ := PMF.uniformOfFintype (HardKeyValSeed U V n)
  set t_end := t_st + F * m
  set endMem := fun s : HardKeyValSeed U V n =>
    memAt D_det (s.modeOps withQueries) (n + modeStride withQueries * t_end)
  have hnU : n ≤ U := by omega
  let kvEndOfMem (C : Mem cells w) :=
    extractKeySetVals hnU hV (decodeDict D_det (n + modeStride withQueries * t_end) C)
  let inferKvEnd (o : BobOuterObs U V cells w F m) :=
    let s_st := decodeDict D_det (n + modeStride withQueries * t_st) o.1
    let D_set : Finset (Fin U) := Finset.univ.image o.2.2.1
    extractKeySetVals hnU hV (fun u =>
      if u ∈ o.2.1 then some (o.2.2.2.2 u).val
      else if u ∈ D_set then none
      else s_st u)
  have hdec_at (s : HardKeyValSeed U V n) (t : ℕ) (ht : t ≤ n) :
      decodeDict D_det (n + modeStride withQueries * t)
        (memAt D_det (s.modeOps withQueries) (n + modeStride withQueries * t)) =
      (windowDict s.permKeyEmb (fun idx => s.kv (s.permKeyEmb idx)) t ht).val := by
    have hvh := s.validHistory_take_modeOps withQueries ht
    have hlen := s.length_take_modeOps withQueries ht
    have hle : ((s.modeOps withQueries).take (n + modeStride withQueries * t)).length ≤
        modeHorizon withQueries n := by
      rw [hlen]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ ht) n
    have hdec := decodeDict_runSeq_eq hcorr hvh hle
    rw [hlen] at hdec
    exact hdec.trans (s.run_take_modeOps_fst withQueries ht)
  have hinfer_eq (s : HardKeyValSeed U V n) :
      inferKvEnd (bobOuterObsOf withQueries D_det t_st F m ht_end s) =
        kvEndOfMem (endMem s) := by
    dsimp only [inferKvEnd, bobOuterObsOf, kvEndOfMem, endMem]
    rw [hdec_at s t_st (by omega), hdec_at s t_end ht_end]
    congr 1; funext u
    set pk := s.permKeyEmb
    set pvals := fun idx => s.kv (pk idx)
    have hA_iff : u ∈ s.insertedSet t_st (F * m) ht_end ↔
        ∃ r : Fin (F * m), pk ⟨n + (t_st + r.val), by have := r.isLt; omega⟩ = u := by
      simp only [HardKeyValSeed.insertedSet, segInsertedKeys_apply, Finset.mem_image,
        Finset.mem_univ, true_and]
      have hpk_ge (r : Fin (F * m)) :
          pk ⟨n + (t_st + r.val), by have := r.isLt; omega⟩ =
            s.keys ⟨n + (t_st + r.val), by have := r.isLt; omega⟩ := by
        simp only [pk, HardKeyValSeed.permKeyEmb, Function.Embedding.trans_apply,
          Equiv.coe_toEmbedding]
        rw [liftDelPerm_apply_ge s.delPerm (by omega) (by have := r.isLt; omega)]
      exact ⟨fun ⟨r, hr⟩ => ⟨r, (hpk_ge r).trans hr⟩,
        fun ⟨r, hr⟩ => ⟨r, (hpk_ge r).symm.trans hr⟩⟩
    have hD_iff : u ∈ Finset.univ.image
          (fun r => segDeletedKeys s.keys s.delPerm t_st (F * m) ht_end r) ↔
        ∃ r : Fin (F * m), pk ⟨t_st + r.val, by have := r.isLt; omega⟩ = u := by
      simp only [segDeletedKeys_apply, pk, HardKeyValSeed.permKeyEmb, Finset.mem_image,
        Finset.mem_univ, true_and, Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
      refine ⟨fun ⟨r, hr⟩ => ⟨r, ?_⟩, fun ⟨r, hr⟩ => ⟨r, ?_⟩⟩ <;>
        [rw [← hr]; rw [← hr]] <;>
        rw [liftDelPerm_apply_lt s.delPerm (by have := r.isLt; omega)]
    rw [windowDict_coe, windowDict_coe]
    by_cases hA : u ∈ s.insertedSet t_st (F * m) ht_end
    · simp only [hA, ↓reduceIte]
      obtain ⟨r, rfl⟩ := hA_iff.mp hA
      let k₀ : Fin n := ⟨n - F * m + r.val, by have := r.isLt; omega⟩
      have hk : windowEmb pk t_end ht_end k₀ =
          pk ⟨n + (t_st + r.val), by have := r.isLt; omega⟩ := by
        rw [windowEmb_apply]
        exact congrArg pk (Fin.ext (by have := r.isLt; dsimp [k₀, t_end]; omega))
      rw [← hk, dictOfEmb_apply_self, windowVals_apply, windowEmb_apply]
    · simp only [hA, ↓reduceIte]
      by_cases hD : u ∈ Finset.univ.image
          (fun r => segDeletedKeys s.keys s.delPerm t_st (F * m) ht_end r)
      · simp only [hD, ↓reduceIte]
        obtain ⟨r, rfl⟩ := hD_iff.mp hD
        symm; refine dictOfEmb_apply_eq_none _ _ fun k => ?_
        rw [windowEmb_apply]; intro heq
        have hval := congrArg Fin.val (pk.injective heq); have := r.isLt; have := k.isLt
        change t_end + k.val = t_st + r.val at hval; omega
      · simp only [hD, ↓reduceIte]
        by_cases hst : ∃ k : Fin n, windowEmb pk t_st (by omega) k = u
        · obtain ⟨k, rfl⟩ := hst
          have hk_ge : F * m ≤ k.val := by
            by_contra hlt; push Not at hlt
            exact hD (hD_iff.mpr ⟨⟨k.val, hlt⟩, by rw [windowEmb_apply]⟩)
          let k' : Fin n := ⟨k.val - F * m, by omega⟩
          have hk' : windowEmb pk t_end ht_end k' = windowEmb pk t_st (by omega) k := by
            simp only [windowEmb_apply]
            exact congrArg pk (Fin.ext (by dsimp [k', t_end]; omega))
          rw [dictOfEmb_apply_self, ← hk', dictOfEmb_apply_self, windowVals_apply, windowVals_apply]
          exact congrArg some (congrArg Fin.val (congrArg s.kv
            (congrArg pk (Fin.ext (by dsimp [k', t_end]; omega)))))
        · push Not at hst
          rw [dictOfEmb_apply_eq_none _ _ hst]
          symm; refine dictOfEmb_apply_eq_none _ _ fun k => ?_
          intro heq; rw [windowEmb_apply] at heq
          by_cases hk_lt : k.val < n - F * m
          · exact hst ⟨F * m + k.val, by omega⟩ (by
              rw [windowEmb_apply, ← heq]
              exact congrArg pk (Fin.ext (by dsimp [t_end]; omega)))
          · exact hA (hA_iff.mpr ⟨⟨k.val - (n - F * m), by have := k.isLt; omega⟩, by
              rw [← heq]; exact congrArg pk (Fin.ext (by dsimp [t_end]; omega))⟩)
  have hce_step :
      PMF.conditionalEntropy
        (μ.map fun s => (bobOuterObsOf withQueries D_det t_st F m ht_end s, endMem s)) ≤
      PMF.conditionalEntropy (μ.map fun s => (kvEndOfMem (endMem s), endMem s)) := by
    have h1 := PMF.conditionalEntropy_map_fst_ge
      (μ.map fun s => (bobOuterObsOf withQueries D_det t_st F m ht_end s, endMem s)) inferKvEnd
    simpa only [_root_.PMF.map_comp, Function.comp_def, hinfer_eq] using h1
  have hinj_mem : PMF.entropy (μ.map fun s => (kvEndOfMem (endMem s), endMem s)) =
      PMF.entropy (μ.map endMem) := by
    have hcomp : μ.map (fun s => (kvEndOfMem (endMem s), endMem s)) =
        (μ.map endMem).map (fun C => (kvEndOfMem C, C)) := by
      rw [_root_.PMF.map_comp]; rfl
    rw [hcomp]
    exact PMF.entropy_map_of_injective _ fun _ _ h => congrArg Prod.snd h
  have hmem_le : PMF.entropy (μ.map endMem) ≤ ((cells * w : ℕ) : ℝ) := by
    refine (PMF.entropy_le_log_card _).trans ?_
    have hcard : Fintype.card (Mem cells w) = 2 ^ (cells * w) := by
      simp only [Mem, Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ]
      rw [← pow_mul, mul_comm]
    rw [hcard, Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  have hunif_kv : μ.map (fun s => kvEndOfMem (endMem s)) =
      (haveI : Nonempty ({ K : Finset (Fin U) // K.card = n } × (Fin n → Fin V)) :=
        ⟨sizedDictEquiv U V n (nonempty_sizedDict hnU hV).some⟩
       PMF.uniformOfFintype ({ K : Finset (Fin U) // K.card = n } × (Fin n → Fin V))) := by
    have hfn : (fun s : HardKeyValSeed U V n => kvEndOfMem (endMem s)) =
        (fun ops => extractKeySetVals hnU hV
          ((Dynamic.spec U V n).run (Dictionary.empty U)
            (ops.take (n + modeStride withQueries * t_end))).1) ∘
          HardKeyValSeed.modeOps withQueries := by
      funext s; dsimp only [Function.comp_apply, kvEndOfMem, endMem]
      rw [hdec_at s t_end ht_end, s.run_take_modeOps_fst withQueries ht_end]
    rw [hfn, ← _root_.PMF.map_comp,
      map_modeOps_uniformOfFintype_hardKeyValSeed withQueries hU hV]
    cases withQueries
    · simpa only [modeDist_false, modeStride, Bool.false_eq_true, ↓reduceIte] using
        map_extractKeySetVals_insertDeleteDist hU hV ht_end hnU
    · simpa only [modeDist_true, modeStride, ↓reduceIte] using
        map_extractKeySetVals_insertQueryDeleteDist hU hV ht_end hnU
  have hkv_ent : PMF.entropy ((μ.map fun s => (kvEndOfMem (endMem s), endMem s)).map Prod.fst) =
      benchmarkBits U V n := by
    have hfst : (μ.map fun s => (kvEndOfMem (endMem s), endMem s)).map Prod.fst =
        μ.map (fun s => kvEndOfMem (endMem s)) := by rw [_root_.PMF.map_comp]; rfl
    let _ : Nonempty ({ K : Finset (Fin U) // K.card = n } × (Fin n → Fin V)) :=
      ⟨sizedDictEquiv U V n (nonempty_sizedDict hnU hV).some⟩
    rw [hfst, hunif_kv, PMF.entropy_uniform]
    have hcard : Fintype.card ({ K : Finset (Fin U) // K.card = n } × (Fin n → Fin V)) =
        U.choose n * V ^ n := by
      rw [← Fintype.ofEquiv_card (sizedDictEquiv U V n).symm]; exact card_sizedDict U V n
    have hc1 : (0 : ℝ) < (U.choose n : ℝ) := by exact_mod_cast Nat.choose_pos hnU
    have hc2 : (0 : ℝ) < (V : ℝ) ^ n := pow_pos (by exact_mod_cast hV) n
    rw [hcard, Nat.cast_mul, Nat.cast_pow, Real.logb_mul hc1.ne' hc2.ne', Real.logb_pow]
    rfl
  have hrhs : PMF.conditionalEntropy (μ.map fun s => (kvEndOfMem (endMem s), endMem s)) ≤
      R_outer := by
    rw [PMF.conditionalEntropy, hinj_mem, hkv_ent]; linarith
  exact hce_step.trans hrhs

private def insKeyOffsetEmb {n : ℕ} (t_st N : ℕ) (h : t_st + N ≤ n) :
    Fin N ↪ Fin (2 * n) where
  toFun r := ⟨n + t_st + r.val, by have := r.isLt; omega⟩
  inj' _ _ heq := Fin.ext (by have := congrArg Fin.val heq; dsimp only at this; omega)

private noncomputable def actInsKeyPerm {n : ℕ} (t_st N : ℕ) (h : t_st + N ≤ n)
    (γ : Equiv.Perm (Fin N)) : Equiv.Perm (Fin (2 * n)) :=
  γ.viaEmbedding (insKeyOffsetEmb t_st N h)

private noncomputable def actInsSeed {U V n : ℕ} (t_st N : ℕ) (h : t_st + N ≤ n)
    (γ : Equiv.Perm (Fin N)) : HardKeyValSeed U V n ≃ HardKeyValSeed U V n where
  toFun s := ⟨(actInsKeyPerm t_st N h γ).toEmbedding.trans s.keys, s.kv, s.delPerm⟩
  invFun s := ⟨(actInsKeyPerm t_st N h γ).symm.toEmbedding.trans s.keys, s.kv, s.delPerm⟩
  left_inv s := HardKeyValSeed.ext (Function.Embedding.ext fun j =>
    congrArg s.keys ((actInsKeyPerm t_st N h γ).apply_symm_apply j)) rfl rfl
  right_inv s := HardKeyValSeed.ext (Function.Embedding.ext fun j =>
    congrArg s.keys ((actInsKeyPerm t_st N h γ).symm_apply_apply j)) rfl rfl

private theorem actInsKeyPerm_lt {n t_st N : ℕ} (h : t_st + N ≤ n)
    (γ : Equiv.Perm (Fin N)) {j : Fin (2 * n)} (hj : j.val < n + t_st) :
    actInsKeyPerm t_st N h γ j = j := by
  refine Equiv.Perm.viaEmbedding_apply_of_notMem γ (insKeyOffsetEmb t_st N h) j ?_
  rintro ⟨r, hr⟩
  have hval : n + t_st + r.val = j.val := congrArg Fin.val hr
  omega

private theorem actInsKeyPerm_ins {n t_st N : ℕ} (h : t_st + N ≤ n)
    (γ : Equiv.Perm (Fin N)) (r : Fin N) :
    actInsKeyPerm t_st N h γ ⟨n + t_st + r.val, by have := r.isLt; omega⟩ =
      ⟨n + t_st + (γ r).val, by have := (γ r).isLt; omega⟩ :=
  Equiv.Perm.viaEmbedding_apply γ (insKeyOffsetEmb t_st N h) r

private def blockProdPerm {F : ℕ} {m : ℕ} (δ : Fin F → Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin F × Fin m) where
  toFun p := (p.1, δ p.1 p.2)
  invFun p := (p.1, (δ p.1).symm p.2)
  left_inv := fun ⟨i, r⟩ => Prod.ext rfl ((δ i).symm_apply_apply r)
  right_inv := fun ⟨i, r⟩ => Prod.ext rfl ((δ i).apply_symm_apply r)

private def blockPerm {F m : ℕ} (δ : Fin F → Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin (F * m)) :=
  finProdFinEquiv.symm.trans ((blockProdPerm δ).trans finProdFinEquiv)

private theorem blockPerm_apply {F m : ℕ} (δ : Fin F → Equiv.Perm (Fin m))
    (i : Fin F) (r : Fin m) :
    blockPerm δ (finProdFinEquiv (i, r)) = finProdFinEquiv (i, δ i r) := by
  simp [blockPerm, blockProdPerm]

open Classical in
/-- Averaging the uniform distribution over a family of permutations `act`: `|G|` times the
probability of `f = b` is the expected number of `γ` with `f (act γ s) = b`. -/
private theorem toReal_map_uniform_mul_card {Ω β G : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype G] (act : G → Equiv.Perm Ω) (f : Ω → β) (b : β) :
    (((PMF.uniformOfFintype Ω).map f) b).toReal * (Fintype.card G : ℝ) =
      ∑ s, ((PMF.uniformOfFintype Ω) s).toReal *
        ((Finset.univ.filter fun γ : G => f (act γ s) = b).card : ℝ) := by
  have hperm (γ : G) : (((PMF.uniformOfFintype Ω).map f) b).toReal =
      ∑ s, ((PMF.uniformOfFintype Ω) s).toReal * (if f (act γ s) = b then 1 else 0) := by
    rw [PMF.map_apply_toReal, ← Equiv.sum_comp (act γ)]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [PMF.uniformOfFintype_apply, eq_comm]
  rw [mul_comm, ← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const,
    Finset.sum_congr rfl fun γ _ => hperm γ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.mul_sum, Finset.card_filter]; push_cast; rfl

open Classical in
/-- Eq. (1) of [LiLiangYuZhou2023] (Section 4.1, p. 14 / PDF p. 15): given Bob's observation
`bobOuterObsOf`, the ordered partition `outerTarget` has conditional entropy at least
`∑_{i < F} log₂ C((F - i) * m, m) = log₂ (F * m)! - F * log₂ m!`. -/
private theorem sum_logb_choose_le_conditionalEntropy_outerTarget (withQueries : Bool)
    {U V n cells w : ℕ} (hU : 2 * n ≤ U) (hV : 1 ≤ V)
    (D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w)
    (t_st F m : ℕ) (ht_end : t_st + F * m ≤ n) :
    letI : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb hU, fun _ => ⟨0, hV⟩, 1⟩⟩
    let μ := PMF.uniformOfFintype (HardKeyValSeed U V n)
    (∑ i : Fin F, Real.logb 2 (((F - i.val) * m).choose m)) ≤
      PMF.conditionalEntropy (μ.map fun s =>
        (bobOuterObsOf withQueries D_det t_st F m ht_end s,
         outerTarget t_st F m ht_end s)) := by
  let _ : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb hU, fun _ => ⟨0, hV⟩, 1⟩⟩
  dsimp only
  set μ := PMF.uniformOfFintype (HardKeyValSeed U V n)
  set obs := bobOuterObsOf withQueries D_det t_st F m ht_end
  set tgt := outerTarget t_st F m ht_end
  set M_nat : ℕ := ∏ i : Fin F, ((F - i.val) * m).choose m
  have hM_pos_nat : 0 < M_nat := Finset.prod_pos fun i _ =>
    Nat.choose_pos (Nat.le_mul_of_pos_left m (by have := i.isLt; omega))
  have hM_pos : (0 : ℝ) < (M_nat : ℝ) := Nat.cast_pos.mpr hM_pos_nat
  have hlog_M : Real.logb 2 (M_nat : ℝ) =
      ∑ i : Fin F, Real.logb 2 (((F - i.val) * m).choose m) := by
    dsimp only [M_nat]
    rw [Nat.cast_prod]
    exact Real.logb_prod Finset.univ _ fun i _ => by
      exact_mod_cast (Nat.choose_pos (Nat.le_mul_of_pos_left m (by have := i.isLt; omega))).ne'
  rw [← hlog_M]
  refine logb_le_conditionalEntropy_of_fiber_le μ obs tgt hM_pos fun o P => ?_
  let G := Equiv.Perm (Fin (F * m))
  let H := Fin F → Equiv.Perm (Fin m)
  have htake_eq (γ : G) (s : HardKeyValSeed U V n) :
      ((actInsSeed t_st (F * m) ht_end γ s).modeOps withQueries).take
          (n + modeStride withQueries * t_st) =
        (s.modeOps withQueries).take (n + modeStride withQueries * t_st) := by
    have hinit : initInsertSeq (actInsSeed t_st (F * m) ht_end γ s).keys
          (fun idx => s.kv ((actInsSeed t_st (F * m) ht_end γ s).keys idx)) =
        initInsertSeq s.keys (fun idx => s.kv (s.keys idx)) := by
      have hk : ∀ idx : Fin (2 * n), idx.val < n →
          (actInsSeed t_st (F * m) ht_end γ s).keys idx = s.keys idx := fun idx hlt =>
        congrArg s.keys (actInsKeyPerm_lt ht_end γ (by omega))
      dsimp only [initInsertSeq]; refine List.map_congr_left fun i _ => ?_
      rw [hk ⟨i.val, by omega⟩ i.isLt]
    cases withQueries <;>
      simp only [HardKeyValSeed.modeOps, Bool.false_eq_true, ↓reduceIte, HardKeyValSeed.ops,
        HardKeyValSeed.updateOps, modeStride, take_insertDeleteSeq, take_insertQueryDeleteSeq] <;>
      rw [show (actInsSeed t_st (F * m) ht_end γ s).kv = s.kv from rfl,
        show (actInsSeed t_st (F * m) ht_end γ s).delPerm = s.delPerm from rfl, hinit] <;>
      congr 1 <;> refine List.flatMap_congr fun j hj => ?_
    all_goals
      have hj_lt : j.val < t_st := by
        obtain ⟨r, hr, heq⟩ := List.mem_take_iff_getElem.mp hj
        have hfr : ((List.finRange n)[r]'(by simp at hr; omega)).val = r := by simp
        have hval := congrArg Fin.val heq; rw [hfr] at hval; simp at hr; omega
      have h1 : (actInsSeed t_st (F * m) ht_end γ s).keys ⟨(s.delPerm j).val, by omega⟩ =
          s.keys ⟨(s.delPerm j).val, by omega⟩ :=
        congrArg s.keys (actInsKeyPerm_lt ht_end γ
          (show (s.delPerm j).val < n + t_st by have := (s.delPerm j).isLt; omega))
      have h2 : (actInsSeed t_st (F * m) ht_end γ s).keys ⟨n + j.val, by omega⟩ =
          s.keys ⟨n + j.val, by omega⟩ :=
        congrArg s.keys (actInsKeyPerm_lt ht_end γ (show n + j.val < n + t_st by omega))
      dsimp only [deleteInsertMetaOp, queryDeleteInsertMetaOp]; rw [h1, h2]
  have hseg_eq (γ : G) (s : HardKeyValSeed U V n) (i : Fin F) (r : Fin m) :
      segInsertedKeys (actInsSeed t_st (F * m) ht_end γ s).keys (t_st + i.val * m) m
          (by have := i.isLt; nlinarith) r =
        segInsertedKeys s.keys t_st (F * m) ht_end (γ (finProdFinEquiv (i, r))) := by
    simp only [actInsSeed, segInsertedKeys_apply, Equiv.coe_fn_mk,
      Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
    have hidx : (⟨n + (t_st + i.val * m + r.val), by have := i.isLt; nlinarith [r.isLt]⟩ :
        Fin (2 * n)) =
        ⟨n + t_st + (finProdFinEquiv (i, r)).val,
          by have := (finProdFinEquiv (i, r)).isLt; omega⟩ :=
      Fin.ext (by simp [finProdFinEquiv]; ring)
    rw [hidx, actInsKeyPerm_ins ht_end γ]
    exact congrArg s.keys (Fin.ext (by ring))
  have hA_inv (γ : G) (s : HardKeyValSeed U V n) :
      (actInsSeed t_st (F * m) ht_end γ s).insertedSet t_st (F * m) ht_end =
        s.insertedSet t_st (F * m) ht_end := by
    have hseg : segInsertedKeys (actInsSeed t_st (F * m) ht_end γ s).keys t_st (F * m) ht_end =
        γ.toEmbedding.trans (segInsertedKeys s.keys t_st (F * m) ht_end) :=
      Function.Embedding.ext fun r => by
        simp only [actInsSeed, segInsertedKeys_apply, Equiv.coe_fn_mk,
          Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
        have hidx : (⟨n + (t_st + r.val), by have := r.isLt; omega⟩ : Fin (2 * n)) =
            ⟨n + t_st + r.val, by have := r.isLt; omega⟩ := Fin.ext (by dsimp; omega)
        rw [hidx, actInsKeyPerm_ins ht_end γ]
        exact congrArg s.keys (Fin.ext (by dsimp; omega))
    rw [HardKeyValSeed.insertedSet, HardKeyValSeed.insertedSet, hseg, image_perm_trans]
  have hd_inv (γ : G) (s : HardKeyValSeed U V n) :
      (fun r => segDeletedKeys (actInsSeed t_st (F * m) ht_end γ s).keys s.delPerm
        t_st (F * m) ht_end r) =
        fun r => segDeletedKeys s.keys s.delPerm t_st (F * m) ht_end r := by
    funext r; simp only [segDeletedKeys_apply, actInsSeed, Equiv.coe_fn_mk,
      Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
    exact congrArg s.keys (actInsKeyPerm_lt ht_end γ
      (by have := (s.delPerm ⟨t_st + r.val, by have := r.isLt; omega⟩).isLt; dsimp; omega))
  let piOf (s : HardKeyValSeed U V n) : H := fun i =>
    (embSetPermEquiv (Fin U) m
      (segInsertedKeys s.keys (t_st + i.val * m) m (by have := i.isLt; nlinarith))).2
  have hobs_eq (γ : G) (s : HardKeyValSeed U V n) :
      obs (actInsSeed t_st (F * m) ht_end γ s) =
        ((obs s).1, (obs s).2.1, (obs s).2.2.1, piOf (actInsSeed t_st (F * m) ht_end γ s),
         (obs s).2.2.2.2) := by
    dsimp only [obs, bobOuterObsOf, memAt]
    rw [htake_eq γ s, hA_inv γ s,
      show (actInsSeed t_st (F * m) ht_end γ s).delPerm = s.delPerm from rfl,
      show (actInsSeed t_st (F * m) ht_end γ s).kv = s.kv from rfl,
      hd_inv γ s]
  have hinj_orbit (s : HardKeyValSeed U V n) :
      Function.Injective (fun γ : G =>
        (piOf (actInsSeed t_st (F * m) ht_end γ s),
         tgt (actInsSeed t_st (F * m) ht_end γ s))) := by
    intro γ₁ γ₂ heq
    rcases Prod.mk.inj heq with ⟨hpi, htgt⟩
    ext x
    obtain ⟨⟨i, r⟩, rfl⟩ := finProdFinEquiv.surjective x
    have hset_i : (actInsSeed t_st (F * m) ht_end γ₁ s).insertedSet (t_st + i.val * m) m
          (by have := i.isLt; nlinarith) =
        (actInsSeed t_st (F * m) ht_end γ₂ s).insertedSet (t_st + i.val * m) m
          (by have := i.isLt; nlinarith) := congrFun htgt i
    have hpi_i : piOf (actInsSeed t_st (F * m) ht_end γ₁ s) i =
        piOf (actInsSeed t_st (F * m) ht_end γ₂ s) i := congrFun hpi i
    set f₁ := segInsertedKeys (actInsSeed t_st (F * m) ht_end γ₁ s).keys (t_st + i.val * m) m
      (by have := i.isLt; nlinarith)
    set f₂ := segInsertedKeys (actInsSeed t_st (F * m) ht_end γ₂ s).keys (t_st + i.val * m) m
      (by have := i.isLt; nlinarith)
    have hc₁ : (Finset.univ.image f₁).card = m :=
      by simp [Finset.card_image_of_injective _ f₁.injective]
    have hc₂ : (Finset.univ.image f₂).card = m :=
      by simp [Finset.card_image_of_injective _ f₂.injective]
    have ho₁ : orderSubset (Finset.univ.image f₁) hc₁ (embSetPermEquiv (Fin U) m f₁).2 = f₁ :=
      orderSubset_eq_of_embSetPermEquiv_fst (Subtype.ext (embSetPermEquiv_fst m f₁))
    have ho₂ : orderSubset (Finset.univ.image f₂) hc₂ (embSetPermEquiv (Fin U) m f₂).2 = f₂ :=
      orderSubset_eq_of_embSetPermEquiv_fst (Subtype.ext (embSetPermEquiv_fst m f₂))
    have hfeq : f₁ r = f₂ r := by
      rw [← ho₁, ← ho₂]
      exact congrArg (fun e : Fin m ↪ Fin U => e r)
        (orderSubset_congr hset_i hpi_i)
    have hseq := (hseg_eq γ₁ s i r).symm.trans (hfeq.trans (hseg_eq γ₂ s i r))
    exact congrArg Fin.val ((segInsertedKeys s.keys t_st (F * m) ht_end).injective hseq)
  have hpi_block (δ : H) (γ : G) (s : HardKeyValSeed U V n) :
      piOf (actInsSeed t_st (F * m) ht_end ((blockPerm δ).trans γ) s) =
        fun i => (δ i).trans (piOf (actInsSeed t_st (F * m) ht_end γ s) i) := by
    funext i
    have hseg_b : segInsertedKeys
          (actInsSeed t_st (F * m) ht_end ((blockPerm δ).trans γ) s).keys
          (t_st + i.val * m) m (by have := i.isLt; nlinarith) =
        (δ i).toEmbedding.trans (segInsertedKeys
          (actInsSeed t_st (F * m) ht_end γ s).keys
          (t_st + i.val * m) m (by have := i.isLt; nlinarith)) := by
      apply Function.Embedding.ext; intro r
      rw [hseg_eq ((blockPerm δ).trans γ) s i r, Function.Embedding.trans_apply,
        Equiv.coe_toEmbedding, hseg_eq γ s i (δ i r), Equiv.trans_apply,
        blockPerm_apply δ i r]
    dsimp only [piOf]; rw [hseg_b]
    exact embSetPermEquiv_perm_trans (δ i) _
  have hcard_pi_fiber (s : HardKeyValSeed U V n) (π₀ : H) :
      (Finset.univ.filter fun γ : G => piOf (actInsSeed t_st (F * m) ht_end γ s) = π₀).card =
        M_nat := by
    have hconst (π₁ π₂ : H) :
        (Finset.univ.filter fun γ : G =>
            piOf (actInsSeed t_st (F * m) ht_end γ s) = π₁).card =
          (Finset.univ.filter fun γ : G =>
            piOf (actInsSeed t_st (F * m) ht_end γ s) = π₂).card := by
      let δ : H := fun i => (π₂ i).trans (π₁ i).symm
      refine Finset.card_equiv (Equiv.mulRight (blockPerm δ)) fun γ => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_mulRight]
      rw [show γ * blockPerm δ = (blockPerm δ).trans γ from rfl, hpi_block]
      refine ⟨fun h => h ▸ funext fun i => ?_, fun h => funext fun i => ?_⟩
      · ext r; simp [δ]
      · exact Equiv.ext fun r => by
          simpa [δ] using congrArg (fun e => e ((π₂ i).symm (π₁ i r))) (congrFun h i)
    have hpart : ∑ π' : H,
        (Finset.univ.filter fun γ : G => piOf (actInsSeed t_st (F * m) ht_end γ s) = π').card =
          Fintype.card G := by
      simpa using Finset.card_eq_sum_card_fiberwise
        (f := fun γ : G => piOf (actInsSeed t_st (F * m) ht_end γ s))
        (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _) |>.symm
    simp_rw [fun π' => hconst π' π₀, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hpart
    have hcardH : Fintype.card H = m.factorial ^ F := by
      simp [H, Fintype.card_perm]
    have hcardG : Fintype.card G = (F * m).factorial := by
      simp [G, Fintype.card_perm]
    have hprod := Nat.prod_choose_partition_mul_pow_factorial F m
    rw [hcardH, hcardG, ← hprod, mul_comm M_nat] at hpart
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.factorial_pos m) F) hpart
  have horbit_ineq (s : HardKeyValSeed U V n) :
      ((Finset.univ.filter fun γ : G =>
          obs (actInsSeed t_st (F * m) ht_end γ s) = o ∧
            tgt (actInsSeed t_st (F * m) ht_end γ s) = P).card : ℝ) * (M_nat : ℝ) ≤
        ((Finset.univ.filter fun γ : G =>
          obs (actInsSeed t_st (F * m) ht_end γ s) = o).card : ℝ) := by
    by_cases hbase : (obs s).1 = o.1 ∧ (obs s).2.1 = o.2.1 ∧ (obs s).2.2.1 = o.2.2.1 ∧
        (obs s).2.2.2.2 = o.2.2.2.2
    · have hiff (γ : G) :
          obs (actInsSeed t_st (F * m) ht_end γ s) = o ↔
            piOf (actInsSeed t_st (F * m) ht_end γ s) = o.2.2.2.1 := by
        rw [hobs_eq γ s]
        rcases o with ⟨o1, o2, o3, o4, o5⟩
        rcases hbase with ⟨rfl, rfl, rfl, rfl⟩
        simp
      have hcard_o : (Finset.univ.filter fun γ : G =>
          obs (actInsSeed t_st (F * m) ht_end γ s) = o).card = M_nat := by
        simp_rw [hiff]; exact hcard_pi_fiber s o.2.2.2.1
      have hcard_le1 : (Finset.univ.filter fun γ : G =>
          obs (actInsSeed t_st (F * m) ht_end γ s) = o ∧
            tgt (actInsSeed t_st (F * m) ht_end γ s) = P).card ≤ 1 := by
        rw [Finset.card_le_one_iff]; intro γ₁ γ₂ h₁ h₂
        rw [Finset.mem_filter] at h₁ h₂
        have hp₁ := (hiff γ₁).mp h₁.2.1; have hp₂ := (hiff γ₂).mp h₂.2.1
        exact hinj_orbit s (Prod.ext (hp₁.trans hp₂.symm) (h₁.2.2.trans h₂.2.2.symm))
      rw [hcard_o]
      exact_mod_cast (Nat.mul_le_mul_right M_nat hcard_le1).trans_eq (Nat.one_mul M_nat)
    · have hemp : (Finset.univ.filter fun γ : G =>
          obs (actInsSeed t_st (F * m) ht_end γ s) = o ∧
            tgt (actInsSeed t_st (F * m) ht_end γ s) = P) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro γ _; rintro ⟨ho, _⟩
        rw [hobs_eq γ s] at ho
        rcases o with ⟨o1, o2, o3, o4, o5⟩
        simp only [Prod.mk.injEq] at ho
        exact hbase ⟨ho.1, ho.2.1, ho.2.2.1, ho.2.2.2.2⟩
      rw [hemp, Finset.card_empty, Nat.cast_zero, zero_mul]
      exact Nat.cast_nonneg _
  rw [le_div_iff₀ hM_pos]
  have havg_pair := toReal_map_uniform_mul_card (fun γ : G => actInsSeed t_st (F * m) ht_end γ)
    (fun s => (obs s, tgt s)) (o, P)
  have havg_obs := toReal_map_uniform_mul_card (fun γ : G => actInsSeed t_st (F * m) ht_end γ) obs o
  simp only [Prod.mk.injEq] at havg_pair
  refine le_of_mul_le_mul_right ?_ (Nat.cast_pos.mpr Fintype.card_pos : (0 : ℝ) < Fintype.card G)
  rw [mul_right_comm, havg_pair, havg_obs, Finset.sum_mul]
  exact Finset.sum_le_sum fun s _ => by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (by convert horbit_ineq s)
      ENNReal.toReal_nonneg

/-! ### Protocol 1 candidate sets, message encoding, and Claims 4.1–4.2 -/

/-- Mode-parametric inner-game seed consistency (`withQueries = true` recovers `IsSeedConsistent`;
`withQueries = false` gives the update-only consistency predicate of Section 8, p. 28 / PDF p. 29,
adapted with the `c = 1` deterministic probe cap). -/
@[expose] def IsModeSeedConsistent (withQueries : Bool) {U V n cells w : ℕ}
    (D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w)
    (t₀ m : ℕ) (ht₀ : t₀ + m ≤ n) (γ t : ℝ) (s : HardKeyValSeed U V n) (B : Finset (Fin U)) :
    Prop :=
  let stride := modeStride withQueries
  let ops := s.modeOps withQueries
  ∃ hB : B.card = m,
    IsCappedConsistent D_det (n + stride * t₀) (memAt D_det ops (n + stride * t₀)) γ m t
      (elemSlice n stride ops t₀ (t₀ + m)) (s.modeCandidateOps withQueries t₀ m ht₀ B hB)

@[simp]
theorem isModeSeedConsistent_true_iff {U V n cells w : ℕ}
    (D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w)
    (t₀ m : ℕ) (ht₀ : t₀ + m ≤ n) (γ t : ℝ) (s : HardKeyValSeed U V n) (B : Finset (Fin U)) :
    IsModeSeedConsistent true D_det t₀ m ht₀ γ t s B ↔
      IsSeedConsistent D_det t₀ m ht₀ γ t s B := by
  simp [IsModeSeedConsistent, IsSeedConsistent, memAt, modeStride, HardKeyValSeed.modeOps,
    HardKeyValSeed.modeCandidateOps_eq]

private theorem HardKeyValSeed.modeCandidateOps_insertedSet_eq_elemSlice (withQueries : Bool)
    {U V n : ℕ} (s : HardKeyValSeed U V n) (t₀ m : ℕ) (ht : t₀ + m ≤ n)
    (hcard : (s.insertedSet t₀ m ht).card = m) :
    s.modeCandidateOps withQueries t₀ m ht (s.insertedSet t₀ m ht) hcard =
      elemSlice n (modeStride withQueries) (s.modeOps withQueries) t₀ (t₀ + m) :=
  (s.elemSlice_modeOps_eq_trueCandidate withQueries ht).symm

/-- Remaining child-segments end bound
`nodeStart (ℓ + 1) b + k * blockSize ℓ + (fanout (ℓ + 1) - k) * blockSize ℓ ≤ n` when
`nodeStop (ℓ + 1) b ≤ n` and `k ≤ fanout (ℓ + 1)`. -/
theorem nodeStart_add_rest_le (T : MetaTree) {n ℓ b : ℕ}
    (ht_stop : T.nodeStop (ℓ + 1) b ≤ n) (k : ℕ) (hk : k ≤ T.fanout (ℓ + 1)) :
    T.nodeStart (ℓ + 1) b + k * T.blockSize ℓ + (T.fanout (ℓ + 1) - k) * T.blockSize ℓ ≤ n := by
  have hsum : k * T.blockSize ℓ + (T.fanout (ℓ + 1) - k) * T.blockSize ℓ =
      T.fanout (ℓ + 1) * T.blockSize ℓ := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hk]
  have hstop : T.nodeStart (ℓ + 1) b + T.fanout (ℓ + 1) * T.blockSize ℓ =
      T.nodeStop (ℓ + 1) b := by
    simp only [MetaTree.nodeStart, MetaTree.nodeStop, MetaTree.blockSize_succ]; ring
  omega

/-- Child-segment end bound `nodeStart (ℓ + 1) b + i * blockSize ℓ + blockSize ℓ ≤ n` when
`nodeStop (ℓ + 1) b ≤ n`. -/
private theorem seg_stop_le (T : MetaTree) {n ℓ b : ℕ}
    (ht_stop : T.nodeStop (ℓ + 1) b ≤ n) (i : Fin (T.fanout (ℓ + 1))) :
    T.nodeStart (ℓ + 1) b + i.val * T.blockSize ℓ + T.blockSize ℓ ≤ n := by
  have h := nodeStart_add_rest_le T ht_stop (i.val + 1) i.isLt
  have h2 : T.nodeStart (ℓ + 1) b + i.val * T.blockSize ℓ + T.blockSize ℓ =
      T.nodeStart (ℓ + 1) b + (i.val + 1) * T.blockSize ℓ := by ring
  omega

/-- Candidate family `F_all^{[i]}` of all `m_ℓ`-subsets of the remaining inserted-key pool `A_rest`
at round `i` of Protocol 1 ([LiLiangYuZhou2023], Section 4.2, Protocol 1 Line 5, p. 14 / PDF
p. 15). -/
private noncomputable def outerAllCandidates {U V n : ℕ} (T : MetaTree) (ℓ b : ℕ)
    (ht_stop : T.nodeStop (ℓ + 1) b ≤ n) (s : HardKeyValSeed U V n)
    (i : Fin (T.fanout (ℓ + 1))) : Finset (Finset (Fin U)) :=
  (s.insertedSet (T.nodeStart (ℓ + 1) b + i.val * T.blockSize ℓ)
    ((T.fanout (ℓ + 1) - i.val) * T.blockSize ℓ)
    (nodeStart_add_rest_le T ht_stop i.val i.isLt.le)).powersetCard (T.blockSize ℓ)

open Classical in
/-- Qualified candidate family `F_qual^{[i]}` at round `i` of Protocol 1 ([LiLiangYuZhou2023],
Section 4.2, Protocol 1 Line 9, p. 14 / PDF p. 15, adapted with the `c = 1` probe cap in
`IsQualified`). -/
private noncomputable def outerQualCandidates (withQueries : Bool) {U V n cells w : ℕ}
    (T : MetaTree) (D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w) (γ t : ℝ)
    (ℓ b : ℕ) (ht_stop : T.nodeStop (ℓ + 1) b ≤ n) (s : HardKeyValSeed U V n)
    (i : Fin (T.fanout (ℓ + 1))) : Finset (Finset (Fin U)) :=
  let stride := modeStride withQueries
  let ops := s.modeOps withQueries
  let t₀ := T.nodeStart (ℓ + 1) b + i.val * T.blockSize ℓ
  have ht₀ : t₀ + T.blockSize ℓ ≤ n := seg_stop_le T ht_stop i
  (outerAllCandidates T ℓ b ht_stop s i).filter fun B =>
    ∃ hB : B.card = T.blockSize ℓ,
      IsQualified D_det (n + stride * t₀) (memAt D_det ops (n + stride * t₀))
        (memAt D_det ops (n + stride * T.nodeStop (ℓ + 1) b)) γ (T.blockSize ℓ) t
        (s.modeCandidateOps withQueries t₀ (T.blockSize ℓ) ht₀ B hB)

/-- Neighbor candidate family `F_nbr^{[i]} = {B ∈ F_all^{[i]} | m_ℓ / 2 ≤ |A^{[i]} ∩ B|}`
([LiLiangYuZhou2023], Section 4.3, p. 16 / PDF p. 17). -/
private noncomputable def outerNbrCandidates {U V n : ℕ} (T : MetaTree) (ℓ b : ℕ)
    (ht_stop : T.nodeStop (ℓ + 1) b ≤ n) (s : HardKeyValSeed U V n)
    (i : Fin (T.fanout (ℓ + 1))) : Finset (Finset (Fin U)) :=
  let t₀ := T.nodeStart (ℓ + 1) b + i.val * T.blockSize ℓ
  have ht₀ : t₀ + T.blockSize ℓ ≤ n := seg_stop_le T ht_stop i
  (outerAllCandidates T ℓ b ht_stop s i).filter fun B =>
    T.blockSize ℓ / 2 ≤ (s.insertedSet t₀ (T.blockSize ℓ) ht₀ ∩ B).card

open Classical in
/-- Round-`i` message `M_i` sent by Alice in Protocol 1 ([LiLiangYuZhou2023], Section 4.2,
Protocol 1 Lines 6–12, pp. 14–16 / PDF pp. 15–17): 1 indicator bit `X_i` followed by a fixed-width
index in `F_qual^{[i]}` when `X_i = 1` or in `F_all^{[i]}` when `X_i = 0`. -/
private noncomputable def outerRoundMsg (withQueries : Bool) {U V n cells w : ℕ} (T : MetaTree)
    (D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w) (γ t : ℝ) (ℓ b : ℕ)
    (ht_stop : T.nodeStop (ℓ + 1) b ≤ n) (s : HardKeyValSeed U V n)
    (i : Fin (T.fanout (ℓ + 1))) : List Bool :=
  let t₀ := T.nodeStart (ℓ + 1) b + i.val * T.blockSize ℓ
  have ht₀ : t₀ + T.blockSize ℓ ≤ n := seg_stop_le T ht_stop i
  let A_i := s.insertedSet t₀ (T.blockSize ℓ) ht₀
  if T.IsGoodSeg D_det n (modeStride withQueries) (s.modeOps withQueries) γ t ℓ b i then
    let FQ := outerQualCandidates withQueries T D_det γ t ℓ b ht_stop s i
    true :: encodeMemFinset FQ FQ.card A_i
  else
    let FA := outerAllCandidates T ℓ b ht_stop s i
    false :: encodeMemFinset FA FA.card A_i

/-- Concatenated `λ_{ℓ+1}`-round transcript `(M_1, …, M_{λ_{ℓ+1}})` of Protocol 1 after `C_end`
([LiLiangYuZhou2023], Section 4.2, Eq. (3), p. 16 / PDF p. 17). -/
private noncomputable def outerProtocolMsg (withQueries : Bool) {U V n cells w : ℕ} (T : MetaTree)
    (D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w) (γ t : ℝ) (ℓ b : ℕ)
    (ht_stop : T.nodeStop (ℓ + 1) b ≤ n) (s : HardKeyValSeed U V n) : List Bool :=
  (List.finRange (T.fanout (ℓ + 1))).flatMap
    (outerRoundMsg withQueries T D_det γ t ℓ b ht_stop s)

private theorem mem_outerAllCandidates_self {U V n : ℕ} (T : MetaTree) (ℓ b : ℕ)
    (ht_stop : T.nodeStop (ℓ + 1) b ≤ n) (s : HardKeyValSeed U V n)
    (i : Fin (T.fanout (ℓ + 1))) :
    s.insertedSet (T.nodeStart (ℓ + 1) b + i.val * T.blockSize ℓ) (T.blockSize ℓ)
      (seg_stop_le T ht_stop i) ∈ outerAllCandidates T ℓ b ht_stop s i := by
  dsimp only [outerAllCandidates]
  rw [Finset.mem_powersetCard]
  refine ⟨?_, (Finset.card_image_of_injective _ (segInsertedKeys _ _ _ _).injective).trans
    (by simp)⟩
  intro u hu
  simp only [HardKeyValSeed.insertedSet, segInsertedKeys_apply, Finset.mem_image,
    Finset.mem_univ, true_and] at hu ⊢
  obtain ⟨r, rfl⟩ := hu
  have hle : T.blockSize ℓ ≤ (T.fanout (ℓ + 1) - i.val) * T.blockSize ℓ :=
    Nat.le_mul_of_pos_left _ (by omega)
  exact ⟨⟨r.val, lt_of_lt_of_le r.isLt hle⟩, rfl⟩

private theorem mem_outerQualCandidates_self (withQueries : Bool) {U V n cells w : ℕ}
    (T : MetaTree) (D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w)
    (γ t : ℝ) (ℓ b : ℕ) (ht_stop : T.nodeStop (ℓ + 1) b ≤ n) (s : HardKeyValSeed U V n)
    (i : Fin (T.fanout (ℓ + 1)))
    (hgood : T.IsGoodSeg D_det n (modeStride withQueries) (s.modeOps withQueries) γ t ℓ b i) :
    s.insertedSet (T.nodeStart (ℓ + 1) b + i.val * T.blockSize ℓ) (T.blockSize ℓ)
      (seg_stop_le T ht_stop i) ∈
      outerQualCandidates withQueries T D_det γ t ℓ b ht_stop s i := by
  classical
  dsimp only [outerQualCandidates]
  rw [Finset.mem_filter]
  refine ⟨mem_outerAllCandidates_self T ℓ b ht_stop s i, ?_⟩
  have hcard : (s.insertedSet (T.nodeStart (ℓ + 1) b + i.val * T.blockSize ℓ)
      (T.blockSize ℓ) (seg_stop_le T ht_stop i)).card = T.blockSize ℓ :=
    (Finset.card_image_of_injective _ (segInsertedKeys _ _ _ _).injective).trans (by simp)
  refine ⟨hcard, ?_⟩
  rw [s.modeCandidateOps_insertedSet_eq_elemSlice withQueries _ _ _ hcard]
  have hq := T.isQualified_elemSlice_of_isGoodSeg D_det n (modeStride withQueries)
    (s.modeOps withQueries) ℓ b i hgood
  dsimp only at hq
  have hst := T.nodeStart_child ℓ b i.val
  have hsp : T.nodeStop ℓ (b * T.fanout (ℓ + 1) + i.val) =
      T.nodeStart (ℓ + 1) b + i.val * T.blockSize ℓ + T.blockSize ℓ := by
    rw [T.nodeStop_child]; ring
  rwa [hst, hsp] at hq

open Classical in
/-- Claim 4.2 ([LiLiangYuZhou2023], Section 4.3, Claim 4.2 and Eq. (6), pp. 17–18 / PDF pp. 18–19):
if the expected far-consistent candidate count on segment `i` is bounded by
`C((F - i) * m_ℓ, m_ℓ) * U ^ (-γ * m_ℓ)`, `2 ^ 64 ≤ F`, `2 ≤ U`, and `F ≤ (γ / 2) * log₂ U`, then
`Pr[¬ (F_qual^{[i]} ⊆ F_nbr^{[i]}) ∧ IsGoodSeg(i)] ≤ 1 / 8`. -/
private theorem prob_not_qualSubsetNbr_and_isGoodSeg_le_one_eighth (withQueries : Bool)
    {U V n cells w : ℕ} (hU : 2 * n ≤ U) (hU2 : 2 ≤ U) (hV : 1 ≤ V)
    (T : MetaTree) (D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w)
    {γ t : ℝ} (ℓ b : ℕ) (ht_stop : T.nodeStop (ℓ + 1) b ≤ n)
    (hF_lo : 2 ^ 64 ≤ T.fanout (ℓ + 1))
    (hF_hi : (T.fanout (ℓ + 1) : ℝ) ≤ (γ / 2) * Real.logb 2 U)
    (i : Fin (T.fanout (ℓ + 1)))
    (hexp :
      haveI : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb hU, fun _ => ⟨0, hV⟩, 1⟩⟩
      (∑ s : HardKeyValSeed U V n, ((PMF.uniformOfFintype (HardKeyValSeed U V n)) s).toReal *
        (((((outerAllCandidates T ℓ b ht_stop s i).filter fun B =>
          (s.insertedSet (T.nodeStart (ℓ + 1) b + i.val * T.blockSize ℓ) (T.blockSize ℓ)
            (seg_stop_le T ht_stop i) ∩ B).card < T.blockSize ℓ / 2).filter
          (IsModeSeedConsistent withQueries D_det
            (T.nodeStart (ℓ + 1) b + i.val * T.blockSize ℓ) (T.blockSize ℓ)
            (seg_stop_le T ht_stop i) γ t s)).card : ℕ) : ℝ)) ≤
        (((T.fanout (ℓ + 1) - i.val) * T.blockSize ℓ).choose (T.blockSize ℓ) : ℝ) *
          (U : ℝ) ^ (-γ * (T.blockSize ℓ : ℝ))) :
    haveI : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb hU, fun _ => ⟨0, hV⟩, 1⟩⟩
    (∑ s : HardKeyValSeed U V n, ((PMF.uniformOfFintype (HardKeyValSeed U V n)) s).toReal *
      (if ¬ (outerQualCandidates withQueries T D_det γ t ℓ b ht_stop s i ⊆
            outerNbrCandidates T ℓ b ht_stop s i) ∧
          T.IsGoodSeg D_det n (modeStride withQueries) (s.modeOps withQueries) γ t ℓ b i
        then (1 : ℝ) else 0)) ≤ 1 / 8 := by
  let _ : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb hU, fun _ => ⟨0, hV⟩, 1⟩⟩
  let μ := PMF.uniformOfFintype (HardKeyValSeed U V n)
  let F := T.fanout (ℓ + 1)
  let m := T.blockSize ℓ
  let t₀ := T.nodeStart (ℓ + 1) b + i.val * m
  let ht₀ : t₀ + m ≤ n := seg_stop_le T ht_stop i
  have hpt (s : HardKeyValSeed U V n) :
      (if ¬ (outerQualCandidates withQueries T D_det γ t ℓ b ht_stop s i ⊆
            outerNbrCandidates T ℓ b ht_stop s i) ∧
          T.IsGoodSeg D_det n (modeStride withQueries) (s.modeOps withQueries) γ t ℓ b i
        then (1 : ℝ) else 0) ≤
      (((((outerAllCandidates T ℓ b ht_stop s i).filter fun B =>
        (s.insertedSet t₀ m ht₀ ∩ B).card < m / 2).filter
        (IsModeSeedConsistent withQueries D_det t₀ m ht₀ γ t s)).card : ℕ) : ℝ) := by
    split_ifs with hbad
    · rcases hbad with ⟨hnsub, hgood⟩
      obtain ⟨B, hBQ, hBnbr⟩ := Finset.not_subset.mp hnsub
      have hB_all : B ∈ outerAllCandidates T ℓ b ht_stop s i := (Finset.mem_filter.mp hBQ).1
      obtain ⟨hB_card, hB_qual⟩ := (Finset.mem_filter.mp hBQ).2
      have hlt : (s.insertedSet t₀ m ht₀ ∩ B).card < m / 2 := by
        by_contra hge; push Not at hge
        exact hBnbr (Finset.mem_filter.mpr ⟨hB_all, hge⟩)
      have hcons : IsModeSeedConsistent withQueries D_det t₀ m ht₀ γ t s B := by
        refine ⟨hB_card, ?_⟩
        have hcc := T.isCappedConsistent_of_isGoodSeg D_det n (modeStride withQueries)
          (s.modeOps withQueries) ℓ b i (ops_B := s.modeCandidateOps withQueries t₀ m ht₀ B hB_card)
          hgood (by rwa [T.nodeStart_child])
        have hsp : T.nodeStop ℓ (b * F + i.val) = t₀ + m := by rw [T.nodeStop_child]; ring
        rwa [T.nodeStart_child, hsp] at hcc
      exact_mod_cast Finset.card_pos.mpr ⟨B, Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hB_all, hlt⟩, hcons⟩⟩
    · exact Nat.cast_nonneg _
  have hsum_le : (∑ s, (μ s).toReal *
      (if ¬ (outerQualCandidates withQueries T D_det γ t ℓ b ht_stop s i ⊆
            outerNbrCandidates T ℓ b ht_stop s i) ∧
          T.IsGoodSeg D_det n (modeStride withQueries) (s.modeOps withQueries) γ t ℓ b i
        then (1 : ℝ) else 0)) ≤
      (((F - i.val) * m).choose m : ℝ) * (U : ℝ) ^ (-γ * (m : ℝ)) :=
    (Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hpt s) ENNReal.toReal_nonneg).trans
      hexp
  have hchoose_le : (((F - i.val) * m).choose m : ℝ) ≤ (2 : ℝ) ^ ((F : ℝ) * (m : ℝ)) := by
    have h1 : ((F - i.val) * m).choose m ≤ 2 ^ (F * m) :=
      (Nat.choose_le_choose m (Nat.mul_le_mul_right m (Nat.sub_le F i.val))).trans
        (Nat.choose_le_two_pow (F * m) m)
    rw [show (F : ℝ) * (m : ℝ) = ((F * m : ℕ) : ℝ) by push_cast; rfl, Real.rpow_natCast]
    exact_mod_cast h1
  have hU_pos : (0 : ℝ) < (U : ℝ) := by exact_mod_cast (show 0 < U by omega)
  have hUrpow : (U : ℝ) ^ (-γ * (m : ℝ)) = (2 : ℝ) ^ (-(γ * (m : ℝ) * Real.logb 2 U)) := by
    conv_lhs => rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hU_pos]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1; ring
  have hm_ge1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast T.blockSize_pos ℓ
  have hF_ge : (2 : ℝ) ^ 64 ≤ (F : ℝ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr hF_lo
  have h2_64 : (6 : ℝ) ≤ (2 : ℝ) ^ 64 := by norm_num
  have hexp_le : (F : ℝ) * (m : ℝ) - γ * (m : ℝ) * Real.logb 2 U ≤ -3 := by
    have h1 : (F : ℝ) * (m : ℝ) ≤ ((γ / 2) * Real.logb 2 U) * (m : ℝ) :=
      mul_le_mul_of_nonneg_right hF_hi (by positivity)
    have h2 : (3 : ℝ) * 1 ≤ ((γ / 2) * Real.logb 2 U) * (m : ℝ) :=
      mul_le_mul (by linarith) hm_ge1 (by norm_num) (by linarith)
    nlinarith
  calc (∑ s, (μ s).toReal *
        (if ¬ (outerQualCandidates withQueries T D_det γ t ℓ b ht_stop s i ⊆
              outerNbrCandidates T ℓ b ht_stop s i) ∧
            T.IsGoodSeg D_det n (modeStride withQueries) (s.modeOps withQueries) γ t ℓ b i
          then (1 : ℝ) else 0))
      ≤ ((2 : ℝ) ^ ((F : ℝ) * (m : ℝ))) * ((U : ℝ) ^ (-γ * (m : ℝ))) :=
        hsum_le.trans (mul_le_mul_of_nonneg_right hchoose_le (Real.rpow_nonneg hU_pos.le _))
    _ = (2 : ℝ) ^ ((F : ℝ) * (m : ℝ) - γ * (m : ℝ) * Real.logb 2 U) := by
        rw [hUrpow, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), sub_eq_add_neg]
    _ ≤ (2 : ℝ) ^ (-3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le
    _ = 1 / 8 := by norm_num

/-! ### Protocol 1 decodability, Eq. (3), and Lemma 3.2 (`OuterLemma`) -/

private theorem nodeStart_add_fanout_mul_eq_nodeStop (T : MetaTree) (ℓ b : ℕ) :
    T.nodeStart (ℓ + 1) b + T.fanout (ℓ + 1) * T.blockSize ℓ = T.nodeStop (ℓ + 1) b := by
  simp only [MetaTree.nodeStart, MetaTree.nodeStop, MetaTree.blockSize_succ]; ring

private theorem modeCandidateOps_eq_of_bobOuterObs_eq (withQueries : Bool) {U V n cells w : ℕ}
    (T : MetaTree) (D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w)
    (ℓ b : ℕ) (ht_stop : T.nodeStop (ℓ + 1) b ≤ n) {s₁ s₂ : HardKeyValSeed U V n}
    (hobs : bobOuterObsOf withQueries D_det (T.nodeStart (ℓ + 1) b) (T.fanout (ℓ + 1))
      (T.blockSize ℓ) ((nodeStart_add_fanout_mul_eq_nodeStop T ℓ b).trans_le ht_stop) s₁ =
      bobOuterObsOf withQueries D_det (T.nodeStart (ℓ + 1) b) (T.fanout (ℓ + 1))
      (T.blockSize ℓ) ((nodeStart_add_fanout_mul_eq_nodeStop T ℓ b).trans_le ht_stop) s₂)
    (i : Fin (T.fanout (ℓ + 1))) (B : Finset (Fin U)) (hB : B.card = T.blockSize ℓ) :
    s₁.modeCandidateOps withQueries (T.nodeStart (ℓ + 1) b + i.val * T.blockSize ℓ)
      (T.blockSize ℓ) (seg_stop_le T ht_stop i) B hB =
    s₂.modeCandidateOps withQueries (T.nodeStart (ℓ + 1) b + i.val * T.blockSize ℓ)
      (T.blockSize ℓ) (seg_stop_le T ht_stop i) B hB := by
  have hd_full := congrArg (fun o : BobOuterObs U V cells w _ _ => o.2.2.1) hobs
  have hpi := congrFun (congrArg (fun o : BobOuterObs U V cells w _ _ => o.2.2.2.1) hobs) i
  have hkv := congrArg (fun o : BobOuterObs U V cells w _ _ => o.2.2.2.2) hobs
  dsimp only [bobOuterObsOf] at hd_full hpi hkv
  have hd : segDeletedKeys s₁.keys s₁.delPerm (T.nodeStart (ℓ + 1) b + i.val * T.blockSize ℓ)
      (T.blockSize ℓ) (seg_stop_le T ht_stop i) =
      segDeletedKeys s₂.keys s₂.delPerm (T.nodeStart (ℓ + 1) b + i.val * T.blockSize ℓ)
      (T.blockSize ℓ) (seg_stop_le T ht_stop i) := by
    refine Function.Embedding.ext fun r => ?_
    have hr := congrFun hd_full ⟨i.val * T.blockSize ℓ + r.val,
      by have := i.isLt; nlinarith [r.isLt]⟩
    simp only [segDeletedKeys_apply] at hr ⊢
    have hidx (s : HardKeyValSeed U V n) :
        (⟨(s.delPerm ⟨T.nodeStart (ℓ + 1) b + i.val * T.blockSize ℓ + r.val,
          by have := seg_stop_le T ht_stop i; omega⟩).val,
          by have := (s.delPerm ⟨T.nodeStart (ℓ + 1) b + i.val * T.blockSize ℓ + r.val,
            by have := seg_stop_le T ht_stop i; omega⟩).isLt; omega⟩ : Fin (2 * n)) =
        ⟨(s.delPerm ⟨T.nodeStart (ℓ + 1) b + (i.val * T.blockSize ℓ + r.val),
          by have := seg_stop_le T ht_stop i; omega⟩).val,
          by have := (s.delPerm ⟨T.nodeStart (ℓ + 1) b + (i.val * T.blockSize ℓ + r.val),
            by have := seg_stop_le T ht_stop i; omega⟩).isLt; omega⟩ := by
      apply Fin.ext; dsimp
      exact congrArg Fin.val (congrArg s.delPerm (Fin.ext (by dsimp; omega)))
    rw [hidx s₁, hidx s₂]; exact hr
  rw [HardKeyValSeed.modeCandidateOps_eq, HardKeyValSeed.modeCandidateOps_eq]
  cases withQueries
  · simp only [Bool.false_eq_true, ↓reduceIte, HardKeyValSeed.candidateUpdateOps_eq, hd, hpi, hkv]
  · simp only [↓reduceIte, HardKeyValSeed.candidateOps_eq, hd, hpi, hkv]

private theorem outerAll_and_qual_eq_of_prev (withQueries : Bool) {U V n cells w : ℕ}
    (T : MetaTree) (D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w)
    (γ t : ℝ) (ℓ b : ℕ) (ht_stop : T.nodeStop (ℓ + 1) b ≤ n)
    {s₁ s₂ : HardKeyValSeed U V n}
    (hobs : bobOuterObsOf withQueries D_det (T.nodeStart (ℓ + 1) b) (T.fanout (ℓ + 1))
      (T.blockSize ℓ) ((nodeStart_add_fanout_mul_eq_nodeStop T ℓ b).trans_le ht_stop) s₁ =
      bobOuterObsOf withQueries D_det (T.nodeStart (ℓ + 1) b) (T.fanout (ℓ + 1))
      (T.blockSize ℓ) ((nodeStart_add_fanout_mul_eq_nodeStop T ℓ b).trans_le ht_stop) s₂)
    (hend : memAt D_det (s₁.modeOps withQueries)
      (n + modeStride withQueries * T.nodeStop (ℓ + 1) b) =
      memAt D_det (s₂.modeOps withQueries)
      (n + modeStride withQueries * T.nodeStop (ℓ + 1) b))
    (i : Fin (T.fanout (ℓ + 1)))
    (hprev : ∀ j : Fin (T.fanout (ℓ + 1)), j.val < i.val →
      outerTarget (T.nodeStart (ℓ + 1) b) (T.fanout (ℓ + 1)) (T.blockSize ℓ)
        ((nodeStart_add_fanout_mul_eq_nodeStop T ℓ b).trans_le ht_stop) s₁ j =
      outerTarget (T.nodeStart (ℓ + 1) b) (T.fanout (ℓ + 1)) (T.blockSize ℓ)
        ((nodeStart_add_fanout_mul_eq_nodeStop T ℓ b).trans_le ht_stop) s₂ j) :
    outerAllCandidates T ℓ b ht_stop s₁ i = outerAllCandidates T ℓ b ht_stop s₂ i ∧
      outerQualCandidates withQueries T D_det γ t ℓ b ht_stop s₁ i =
        outerQualCandidates withQueries T D_det γ t ℓ b ht_stop s₂ i := by
  classical
  let t_st := T.nodeStart (ℓ + 1) b
  let F := T.fanout (ℓ + 1)
  let m := T.blockSize ℓ
  let stride := modeStride withQueries
  have ht_end : t_st + F * m ≤ n :=
    (nodeStart_add_fanout_mul_eq_nodeStop T ℓ b).trans_le ht_stop
  have hmem_k : ∀ k : ℕ, k ≤ i.val →
      memAt D_det (s₁.modeOps withQueries) (n + stride * (t_st + k * m)) =
        memAt D_det (s₂.modeOps withQueries) (n + stride * (t_st + k * m)) := by
    intro k hk
    induction k with
    | zero =>
      have h1 := congrArg Prod.fst hobs
      dsimp only [bobOuterObsOf] at h1
      simpa only [Nat.zero_mul, Nat.add_zero] using h1
    | succ k ih =>
      let j : Fin F := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) (hk.trans i.isLt.le)⟩
      have hle_j : t_st + k * m ≤ t_st + (k + 1) * m := by nlinarith
      rw [memAt_eq_runInterval_elemSlice D_det n stride _ hle_j,
        memAt_eq_runInterval_elemSlice D_det n stride _ hle_j, ih (Nat.le_of_succ_le hk)]
      have hsp : t_st + (k + 1) * m = t_st + j.val * m + m := by dsimp [j]; ring
      have hc₁ : (s₁.insertedSet (t_st + j.val * m) m (seg_stop_le T ht_stop j)).card = m :=
        (Finset.card_image_of_injective _ (segInsertedKeys _ _ _ _).injective).trans (by simp)
      have hc₂ : (s₂.insertedSet (t_st + j.val * m) m (seg_stop_le T ht_stop j)).card = m :=
        (Finset.card_image_of_injective _ (segInsertedKeys _ _ _ _).injective).trans (by simp)
      have hset_j : s₁.insertedSet (t_st + j.val * m) m (seg_stop_le T ht_stop j) =
          s₂.insertedSet (t_st + j.val * m) m (seg_stop_le T ht_stop j) :=
        hprev j (lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      have hslice : elemSlice n stride (s₁.modeOps withQueries)
            (t_st + j.val * m) (t_st + j.val * m + m) =
          elemSlice n stride (s₂.modeOps withQueries)
            (t_st + j.val * m) (t_st + j.val * m + m) := by
        rw [← s₁.modeCandidateOps_insertedSet_eq_elemSlice withQueries _ _ _ hc₁,
          ← s₂.modeCandidateOps_insertedSet_eq_elemSlice withQueries _ _ _ hc₂]
        have hcand := modeCandidateOps_eq_of_bobOuterObs_eq withQueries T D_det ℓ b ht_stop hobs j
          (s₂.insertedSet (t_st + j.val * m) m (seg_stop_le T ht_stop j)) hc₂
        convert hcand using 2
      change (D_det.runInterval _ _
          (elemSlice n stride (s₁.modeOps withQueries) (t_st + j.val * m) (t_st + (k + 1) * m))).2 =
        (D_det.runInterval _ _
          (elemSlice n stride (s₂.modeOps withQueries) (t_st + j.val * m) (t_st + (k + 1) * m))).2
      rw [hsp, hslice]
  have hrest_eq (s : HardKeyValSeed U V n) :
      s.insertedSet (t_st + i.val * m) ((F - i.val) * m)
        (nodeStart_add_rest_le T ht_stop i.val i.isLt.le) =
      s.insertedSet t_st (F * m) ht_end \
        (Finset.univ.filter fun j : Fin F => j.val < i.val).biUnion
          (outerTarget t_st F m ht_end s) := by
    ext u
    simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
      true_and, outerTarget, HardKeyValSeed.insertedSet, segInsertedKeys_apply,
      Finset.mem_image]
    constructor
    · rintro ⟨r, rfl⟩
      refine ⟨⟨⟨i.val * m + r.val, by
          have hr := r.isLt; have hi := i.isLt
          have hfm : i.val * m + (F - i.val) * m = F * m := by
            rw [← Nat.add_mul, Nat.add_sub_of_le hi.le]
          omega⟩, congrArg s.keys (Fin.ext (by dsimp; ring))⟩, ?_⟩
      rintro ⟨j, hj, r', heq⟩
      have hval := congrArg Fin.val (s.keys.injective heq); dsimp at hval
      have hj_le : (j.val + 1) * m ≤ i.val * m := Nat.mul_le_mul_right m hj
      have := r'.isLt; nlinarith
    · rintro ⟨⟨x, rfl⟩, hnot⟩
      obtain ⟨⟨j, r'⟩, hx⟩ := finProdFinEquiv.surjective x
      have hx_val : x.val = j.val * m + r'.val := by
        rw [← hx]; simp [finProdFinEquiv]; ring
      by_cases hj : j.val < i.val
      · exfalso; exact hnot ⟨j, hj, r', congrArg s.keys (Fin.ext (by dsimp; omega))⟩
      · have hij : i.val ≤ j.val := Nat.le_of_not_lt hj
        have hlt : x.val - i.val * m < (F - i.val) * m := by
          have h0 : i.val * m ≤ j.val * m := Nat.mul_le_mul_right m hij
          have h1 : j.val * m + r'.val < (j.val + 1) * m := by have := r'.isLt; nlinarith
          have h2 : (j.val + 1) * m ≤ F * m := Nat.mul_le_mul_right m j.isLt
          have h3 : i.val * m + (F - i.val) * m = F * m := by
            rw [← Nat.add_mul, Nat.add_sub_of_le i.isLt.le]
          rw [hx_val]; omega
        exact ⟨⟨x.val - i.val * m, hlt⟩, congrArg s.keys (Fin.ext (by
          have : i.val * m ≤ x.val := by
            rw [hx_val]; exact (Nat.mul_le_mul_right m hij).trans (Nat.le_add_right _ _)
          dsimp; omega))⟩
  have hA_eq : s₁.insertedSet t_st (F * m) ht_end = s₂.insertedSet t_st (F * m) ht_end :=
    congrArg (fun o : BobOuterObs U V cells w F m => o.2.1) hobs
  have hbi_eq : (Finset.univ.filter fun j : Fin F => j.val < i.val).biUnion
        (outerTarget t_st F m ht_end s₁) =
      (Finset.univ.filter fun j : Fin F => j.val < i.val).biUnion
        (outerTarget t_st F m ht_end s₂) := by
    ext u; simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨j, hj, hu⟩ => ⟨j, hj, hprev j hj ▸ hu⟩,
      fun ⟨j, hj, hu⟩ => ⟨j, hj, (hprev j hj).symm ▸ hu⟩⟩
  have hall : outerAllCandidates T ℓ b ht_stop s₁ i = outerAllCandidates T ℓ b ht_stop s₂ i := by
    dsimp only [outerAllCandidates]; rw [hrest_eq s₁, hrest_eq s₂, hA_eq, hbi_eq]
  refine ⟨hall, ?_⟩
  dsimp only [outerQualCandidates]
  rw [hall, hmem_k i.val le_rfl, hend]
  refine Finset.filter_congr fun B _ => exists_congr fun hB => ?_
  rw [modeCandidateOps_eq_of_bobOuterObs_eq withQueries T D_det ℓ b ht_stop hobs i B hB]

private theorem outerProtocolMsg_prefix_imp (withQueries : Bool) {U V n cells w : ℕ}
    (T : MetaTree) (D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w)
    (γ t : ℝ) (ℓ b : ℕ) (ht_stop : T.nodeStop (ℓ + 1) b ≤ n)
    {s₁ s₂ : HardKeyValSeed U V n}
    (hobs : bobOuterObsOf withQueries D_det (T.nodeStart (ℓ + 1) b) (T.fanout (ℓ + 1))
      (T.blockSize ℓ) ((nodeStart_add_fanout_mul_eq_nodeStop T ℓ b).trans_le ht_stop) s₁ =
      bobOuterObsOf withQueries D_det (T.nodeStart (ℓ + 1) b) (T.fanout (ℓ + 1))
      (T.blockSize ℓ) ((nodeStart_add_fanout_mul_eq_nodeStop T ℓ b).trans_le ht_stop) s₂)
    (hend : memAt D_det (s₁.modeOps withQueries)
      (n + modeStride withQueries * T.nodeStop (ℓ + 1) b) =
      memAt D_det (s₂.modeOps withQueries)
      (n + modeStride withQueries * T.nodeStop (ℓ + 1) b))
    (hpref : outerProtocolMsg withQueries T D_det γ t ℓ b ht_stop s₁ <+:
      outerProtocolMsg withQueries T D_det γ t ℓ b ht_stop s₂) :
    outerProtocolMsg withQueries T D_det γ t ℓ b ht_stop s₁ =
      outerProtocolMsg withQueries T D_det γ t ℓ b ht_stop s₂ ∧
    outerTarget (T.nodeStart (ℓ + 1) b) (T.fanout (ℓ + 1)) (T.blockSize ℓ)
      ((nodeStart_add_fanout_mul_eq_nodeStop T ℓ b).trans_le ht_stop) s₁ =
    outerTarget (T.nodeStart (ℓ + 1) b) (T.fanout (ℓ + 1)) (T.blockSize ℓ)
      ((nodeStart_add_fanout_mul_eq_nodeStop T ℓ b).trans_le ht_stop) s₂ := by
  classical
  let F := T.fanout (ℓ + 1)
  let tailMsg (s : HardKeyValSeed U V n) (k : ℕ) : List Bool :=
    ((List.finRange F).drop k).flatMap (outerRoundMsg withQueries T D_det γ t ℓ b ht_stop s)
  let tgt : HardKeyValSeed U V n → Fin F → Finset (Fin U) :=
    outerTarget (T.nodeStart (ℓ + 1) b) F (T.blockSize ℓ)
      ((nodeStart_add_fanout_mul_eq_nodeStop T ℓ b).trans_le ht_stop)
  have hstep : ∀ k : ℕ, k ≤ F →
      (∀ j : Fin F, j.val < k →
        outerRoundMsg withQueries T D_det γ t ℓ b ht_stop s₁ j =
          outerRoundMsg withQueries T D_det γ t ℓ b ht_stop s₂ j ∧
        tgt s₁ j = tgt s₂ j) ∧
      tailMsg s₁ k <+: tailMsg s₂ k := by
    intro k hk
    induction k with
    | zero =>
      exact ⟨fun _ hj => absurd hj (Nat.not_lt_zero _),
        by simpa [tailMsg, outerProtocolMsg]⟩
    | succ k ih =>
      obtain ⟨hprev, htk⟩ := ih (Nat.le_of_succ_le hk)
      let i : Fin F := ⟨k, hk⟩
      have hdrop (s : HardKeyValSeed U V n) :
          tailMsg s k = outerRoundMsg withQueries T D_det γ t ℓ b ht_stop s i ++
            tailMsg s (k + 1) := by
        dsimp only [tailMsg]
        rw [List.drop_eq_getElem_cons (by simp; omega), List.flatMap_cons]
        simp [i]
      rw [hdrop s₁, hdrop s₂] at htk
      obtain ⟨hall_eq, hqual_eq⟩ :
        outerAllCandidates T ℓ b ht_stop s₁ i = outerAllCandidates T ℓ b ht_stop s₂ i ∧
          outerQualCandidates withQueries T D_det γ t ℓ b ht_stop s₁ i =
            outerQualCandidates withQueries T D_det γ t ℓ b ht_stop s₂ i :=
        outerAll_and_qual_eq_of_prev withQueries T D_det γ t ℓ b ht_stop hobs hend i
          fun j hj => (hprev j hj).2
      set g₁ := T.IsGoodSeg D_det n (modeStride withQueries) (s₁.modeOps withQueries) γ t ℓ b i
      set g₂ := T.IsGoodSeg D_det n (modeStride withQueries) (s₂.modeOps withQueries) γ t ℓ b i
      have hg_iff : g₁ ↔ g₂ := by
        obtain ⟨r, hr⟩ := htk
        by_cases h1 : g₁ <;> by_cases h2 : g₂
        · exact ⟨fun _ => h2, fun _ => h1⟩
        · exfalso
          simp only [outerRoundMsg, g₁, g₂, h1, h2, ↓reduceIte, List.cons_append] at hr
          exact Bool.noConfusion (List.cons.inj hr).1
        · exfalso
          simp only [outerRoundMsg, g₁, g₂, h1, h2, ↓reduceIte, List.cons_append] at hr
          exact Bool.noConfusion (List.cons.inj hr).1
        · exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
      have hlen_eq : (outerRoundMsg withQueries T D_det γ t ℓ b ht_stop s₁ i).length =
          (outerRoundMsg withQueries T D_det γ t ℓ b ht_stop s₂ i).length := by
        by_cases h1 : g₁
        · have h2 : g₂ := hg_iff.mp h1
          simp [outerRoundMsg, g₁, g₂, h1, h2, hqual_eq]
        · have h2 : ¬ g₂ := fun h => h1 (hg_iff.mpr h)
          simp [outerRoundMsg, g₁, g₂, h1, h2, hall_eq]
      obtain ⟨hmsg_i, htk1⟩ := prefix_append_of_length_eq hlen_eq htk
      have htgt_i : tgt s₁ i = tgt s₂ i := by
        by_cases h1 : g₁
        · have h2 : g₂ := hg_iff.mp h1
          have hmem₁ := mem_outerQualCandidates_self withQueries T D_det γ t ℓ b ht_stop s₁ i h1
          have hmem₂ := hqual_eq ▸
            mem_outerQualCandidates_self withQueries T D_det γ t ℓ b ht_stop s₂ i h2
          simp only [outerRoundMsg, g₁, g₂, h1, h2, ↓reduceIte, ← hqual_eq, List.cons.injEq,
            true_and] at hmsg_i
          exact encodeMemFinset_inj hmem₁ hmem₂ le_rfl hmsg_i
        · have h2 : ¬ g₂ := fun h => h1 (hg_iff.mpr h)
          have hmem₁ := mem_outerAllCandidates_self T ℓ b ht_stop s₁ i
          have hmem₂ := hall_eq ▸ mem_outerAllCandidates_self T ℓ b ht_stop s₂ i
          simp only [outerRoundMsg, g₁, g₂, h1, h2, ↓reduceIte, ← hall_eq, List.cons.injEq,
            true_and] at hmsg_i
          exact encodeMemFinset_inj hmem₁ hmem₂ le_rfl hmsg_i
      refine ⟨fun j hj => ?_, htk1⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
      · exact hprev j hlt
      · have hji : j = i := Fin.ext heq
        rw [hji]; exact ⟨hmsg_i, htgt_i⟩
  obtain ⟨hall_j, _⟩ := hstep F le_rfl
  refine ⟨List.flatMap_congr fun j _ => (hall_j j j.isLt).1, funext fun j => (hall_j j j.isLt).2⟩

open Classical in
/-- Mode-parametric Outer Lemma ([LiLiangYuZhou2023], Section 3, Lemma 3.2, p. 12 / PDF p. 13 and
Section 4, pp. 13–20 / PDF pp. 14–21): at any internal node `(ℓ + 1, b)` (`1 ≤ ℓ`,
`T.nodeStop (ℓ + 1) b ≤ n`) with `2 ^ 64 ≤ λ_{ℓ+1} ≤ (γ / 2) * log₂ U` and
`100 * R_outer ≤ m_{ℓ+1} * log₂ λ_{ℓ+1}`, if every first-half child segment satisfies the
inner-game expected far-consistent candidate bound, then either
`E[nodeCost] ≥ (γ / 100) * m_{ℓ+1}` or `E[nodeProbes] ≥ (1 / 16) * m_{ℓ+1} * t`. -/
theorem outer_node_lower_bound (withQueries : Bool) {U V n cells w : ℕ} {R_outer γ t : ℝ}
    (hU : 2 * n ≤ U) (hU2 : 2 ≤ U) (hV : 1 ≤ V)
    (hspace_outer : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R_outer)
    (T : MetaTree) {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (modeHorizon withQueries n + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2)
    (hγ : 0 < γ) (ht : 0 < t) {ℓ b : ℕ} (hℓ : 1 ≤ ℓ)
    (ht_stop : T.nodeStop (ℓ + 1) b ≤ n)
    (hF_lo : 2 ^ 64 ≤ T.fanout (ℓ + 1))
    (hF_hi : (T.fanout (ℓ + 1) : ℝ) ≤ (γ / 2) * Real.logb 2 U)
    (hR_outer : 100 * R_outer ≤ (T.blockSize (ℓ + 1) : ℝ) * Real.logb 2 (T.fanout (ℓ + 1)))
    (hinner : ∀ i : Fin (T.fanout (ℓ + 1)), i.val < T.fanout (ℓ + 1) / 2 →
      let t₀ := T.nodeStart (ℓ + 1) b + i.val * T.blockSize ℓ
      let r_rest := (T.fanout (ℓ + 1) - i.val) * T.blockSize ℓ
      let hrest : t₀ + r_rest ≤ n := nodeStart_add_rest_le T ht_stop i.val i.isLt.le
      let ht₀ : t₀ + T.blockSize ℓ ≤ n := by
        have := Nat.le_mul_of_pos_left (T.blockSize ℓ) (Nat.sub_pos_of_lt i.isLt)
        omega
      letI : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb hU, fun _ => ⟨0, hV⟩, 1⟩⟩
      (∑ s : HardKeyValSeed U V n, ((PMF.uniformOfFintype (HardKeyValSeed U V n)) s).toReal *
        ((((((s.insertedSet t₀ r_rest hrest).powersetCard (T.blockSize ℓ)).filter fun B =>
          (s.insertedSet t₀ (T.blockSize ℓ) ht₀ ∩ B).card < T.blockSize ℓ / 2).filter
          (IsModeSeedConsistent withQueries D_det t₀ (T.blockSize ℓ) ht₀ γ t s)).card : ℕ) : ℝ)) ≤
        (r_rest.choose (T.blockSize ℓ) : ℝ) * (U : ℝ) ^ (-γ * (T.blockSize ℓ : ℝ))) :
    (γ / 100) * (T.blockSize (ℓ + 1) : ℝ) ≤
        ∑' ops, (modeDist withQueries U V n hU hV ops).toReal *
          (T.nodeCost D_det n (modeStride withQueries) ops ℓ b : ℝ) ∨
      (1 / 16) * (T.blockSize (ℓ + 1) : ℝ) * t ≤
        ∑' ops, (modeDist withQueries U V n hU hV ops).toReal *
          (T.nodeProbes D_det n (modeStride withQueries) ops (ℓ + 1) b : ℝ) := by
  classical
  let _ : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb hU, fun _ => ⟨0, hV⟩, 1⟩⟩
  let μ := PMF.uniformOfFintype (HardKeyValSeed U V n)
  let F := T.fanout (ℓ + 1)
  let m := T.blockSize ℓ
  let t_st := T.nodeStart (ℓ + 1) b
  let stride := modeStride withQueries
  have hF_pos_nat : 0 < F := (Nat.pow_pos (by omega : 0 < 2)).trans_le hF_lo
  have hF_20 : 2 ^ 20 ≤ F :=
    (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 20 ≤ 64)).trans hF_lo
  have ht_end : t_st + F * m ≤ n :=
    (nodeStart_add_fanout_mul_eq_nodeStop T ℓ b).trans_le ht_stop
  have hm_even : 2 ∣ m := T.even_blockSize hℓ
  have hm_ge2 : 2 ≤ m :=
    (Nat.pow_le_pow_right (by omega) hℓ).trans (T.two_pow_le_blockSize ℓ)
  have hF_even : 2 ∣ F := T.even_fanout (ℓ + 1) (Nat.le_add_left 1 ℓ)
  have hexp (f : List (Dynamic.Op U) → ℕ) :
      ∑' ops, (modeDist withQueries U V n hU hV ops).toReal * (f ops : ℝ) =
        ∑ s, (μ s).toReal * (f (s.modeOps withQueries) : ℝ) := by
    rw [← map_modeOps_uniformOfFintype_hardKeyValSeed]
    exact PMF.tsum_toReal_map_mul_natCast μ (HardKeyValSeed.modeOps withQueries) _
  rw [hexp, hexp]
  by_contra hnot
  push Not at hnot
  rcases hnot with ⟨hcost_lt, hprobe_lt⟩
  let obs (s : HardKeyValSeed U V n) := bobOuterObsOf withQueries D_det t_st F m ht_end s
  let endMem (s : HardKeyValSeed U V n) :=
    memAt D_det (s.modeOps withQueries) (n + stride * (t_st + F * m))
  let tgt (s : HardKeyValSeed U V n) := outerTarget t_st F m ht_end s
  let msg (s : HardKeyValSeed U V n) := outerProtocolMsg withQueries T D_det γ t ℓ b ht_stop s
  have hend_eq (s : HardKeyValSeed U V n) :
      endMem s = memAt D_det (s.modeOps withQueries) (n + stride * T.nodeStop (ℓ + 1) b) := by
    dsimp only [endMem, t_st, F, m]; rw [nodeStart_add_fanout_mul_eq_nodeStop]
  -- Eq. (1), Eq. (2), and prefix-free compression -> Eq. (3)
  have heq1 := sum_logb_choose_le_conditionalEntropy_outerTarget withQueries hU hV D_det t_st F m
    ht_end
  have heq2 := conditionalEntropy_endMem_le withQueries hU hV hspace_outer hcorr t_st F m ht_end
  have hchain := PMF.conditionalEntropy_le_add_conditionalEntropy μ obs endMem tgt
  have hpf_len : PMF.conditionalEntropy (μ.map fun s => ((obs s, endMem s), tgt s)) ≤
      ∑ s, (μ s).toReal * ((msg s).length : ℝ) := by
    refine conditionalEntropy_map_le_expected_length_of_isPrefixFree μ
      (fun s => (obs s, endMem s)) tgt msg (fun oc => ?_) (fun s₁ _ s₂ _ hoc hm => ?_)
    · rintro _ ⟨s₁, ⟨_, hs₁⟩, rfl⟩ _ ⟨s₂, ⟨_, hs₂⟩, rfl⟩ hp
      have hoc_eq := hs₁.trans hs₂.symm
      exact (outerProtocolMsg_prefix_imp withQueries T D_det γ t ℓ b ht_stop
        (Prod.mk.inj hoc_eq).1 ((hend_eq s₁).symm.trans ((Prod.mk.inj hoc_eq).2.trans
          (hend_eq s₂))) hp).1
    · exact (outerProtocolMsg_prefix_imp withQueries T D_det γ t ℓ b ht_stop
        (Prod.mk.inj hoc).1 ((hend_eq s₁).symm.trans ((Prod.mk.inj hoc).2.trans (hend_eq s₂)))
        (show msg s₁ <+: msg s₂ by rw [hm])).2
  have heq3 : (∑ i : Fin F, Real.logb 2 (((F - i.val) * m).choose m)) - R_outer ≤
      ∑ s, (μ s).toReal * ((msg s).length : ℝ) := by linarith
  -- Upper bound E[|msg|] via Eq. (4) + Claims 4.1, 4.2, and 4.6
  set halfSet := Finset.univ.filter fun i : Fin F => i.val < F / 2
  let goodXY (s : HardKeyValSeed U V n) (i : Fin F) : Prop :=
    T.IsGoodSeg D_det n stride (s.modeOps withQueries) γ t ℓ b i ∧
      outerQualCandidates withQueries T D_det γ t ℓ b ht_stop s i ⊆
        outerNbrCandidates T ℓ b ht_stop s i
  have hrest_card (s : HardKeyValSeed U V n) (i : Fin F) :
      (s.insertedSet (T.nodeStart (ℓ + 1) b + i.val * T.blockSize ℓ)
        ((T.fanout (ℓ + 1) - i.val) * T.blockSize ℓ)
        (nodeStart_add_rest_le T ht_stop i.val i.isLt.le)).card = (F - i.val) * m := by
    dsimp only [HardKeyValSeed.insertedSet]
    exact (Finset.card_image_of_injective _ (segInsertedKeys _ _ _ _).injective).trans
      (by simp [F, m])
  have hFA_card (s : HardKeyValSeed U V n) (i : Fin F) :
      (outerAllCandidates T ℓ b ht_stop s i).card = ((F - i.val) * m).choose m := by
    dsimp only [outerAllCandidates]
    rw [Finset.card_powersetCard, hrest_card]
  have hround_le (s : HardKeyValSeed U V n) (i : Fin F) :
      ((outerRoundMsg withQueries T D_det γ t ℓ b ht_stop s i).length : ℝ) ≤
        2 + Real.logb 2 (((F - i.val) * m).choose m) -
          (if i ∈ halfSet ∧ goodXY s i then (1 / 4) * (m : ℝ) * Real.logb 2 F else 0) := by
    have hFA_pos : 1 ≤ (outerAllCandidates T ℓ b ht_stop s i).card :=
      Finset.card_pos.mpr ⟨_, mem_outerAllCandidates_self T ℓ b ht_stop s i⟩
    by_cases hgood : T.IsGoodSeg D_det n stride (s.modeOps withQueries) γ t ℓ b i
    · have hFQ_pos : 1 ≤ (outerQualCandidates withQueries T D_det γ t ℓ b ht_stop s i).card :=
        Finset.card_pos.mpr ⟨_, mem_outerQualCandidates_self withQueries T D_det γ t ℓ b ht_stop
          s i hgood⟩
      have hlen_g : (outerRoundMsg withQueries T D_det γ t ℓ b ht_stop s i).length =
          1 + Nat.clog 2 (outerQualCandidates withQueries T D_det γ t ℓ b ht_stop s i).card := by
        dsimp only [outerRoundMsg]
        rw [ite_eq_left hgood, List.length_cons, length_encodeMemFinset, Nat.add_comm]
      have hclog_Q := (clog_two_lt_logb_add_one hFQ_pos).le
      by_cases hhi : i ∈ halfSet ∧
          outerQualCandidates withQueries T D_det γ t ℓ b ht_stop s i ⊆
            outerNbrCandidates T ℓ b ht_stop s i
      · have hxy : i ∈ halfSet ∧ goodXY s i := ⟨hhi.1, hgood, hhi.2⟩
        have hQ_le_N : (outerQualCandidates withQueries T D_det γ t ℓ b ht_stop s i).card ≤
            (outerNbrCandidates T ℓ b ht_stop s i).card := Finset.card_le_card hhi.2
        have hlog_QN : Real.logb 2
            (outerQualCandidates withQueries T D_det γ t ℓ b ht_stop s i).card ≤
            Real.logb 2 (outerNbrCandidates T ℓ b ht_stop s i).card :=
          Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hFQ_pos)
            (by exact_mod_cast hQ_le_N)
        have hmA := Finset.mem_powersetCard.mp (mem_outerAllCandidates_self T ℓ b ht_stop s i)
        have hi_lt : i.val < F / 2 := (Finset.mem_filter.mp hhi.1).2
        have hFh_le : F / 2 ≤ F - i.val := by obtain ⟨q, hq⟩ := hF_even; omega
        have hgap := quarter_mul_logb_le_logb_powersetCard_sub_nbr hm_even hm_ge2 hF_even
          hF_20 hmA.1 hmA.2
          (by rw [hrest_card]; exact Nat.mul_le_mul_right m hFh_le)
          (by rw [hrest_card]; exact Nat.mul_le_mul_right m (Nat.sub_le F i.val))
        change (1 / 4 : ℝ) * (m : ℝ) * Real.logb 2 F ≤
          Real.logb 2 (outerAllCandidates T ℓ b ht_stop s i).card -
            Real.logb 2 (outerNbrCandidates T ℓ b ht_stop s i).card at hgap
        rw [hFA_card s i] at hgap
        rw [hlen_g, ite_eq_left hxy]; push_cast; linarith
      · have hnxy : ¬ (i ∈ halfSet ∧ goodXY s i) := fun h => hhi ⟨h.1, h.2.2⟩
        have hQ_le_A : (outerQualCandidates withQueries T D_det γ t ℓ b ht_stop s i).card ≤
            (outerAllCandidates T ℓ b ht_stop s i).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        have hlog_QA : Real.logb 2
            (outerQualCandidates withQueries T D_det γ t ℓ b ht_stop s i).card ≤
            Real.logb 2 (((F - i.val) * m).choose m) := by
          rw [← hFA_card s i]
          exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hFQ_pos)
            (by exact_mod_cast hQ_le_A)
        rw [hlen_g, ite_eq_right hnxy]; push_cast; linarith
    · have hnxy : ¬ (i ∈ halfSet ∧ goodXY s i) := fun h => hgood h.2.1
      have hlen_b : (outerRoundMsg withQueries T D_det γ t ℓ b ht_stop s i).length =
          1 + Nat.clog 2 (outerAllCandidates T ℓ b ht_stop s i).card := by
        dsimp only [outerRoundMsg]
        rw [ite_eq_right hgood, List.length_cons, length_encodeMemFinset, Nat.add_comm]
      have hclog_A := (clog_two_lt_logb_add_one hFA_pos).le
      rw [hFA_card s i] at hlen_b hclog_A
      rw [hlen_b, ite_eq_right hnxy]; push_cast; linarith
  have hmsg_len (s : HardKeyValSeed U V n) :
      ((msg s).length : ℝ) =
        ∑ i : Fin F, ((outerRoundMsg withQueries T D_det γ t ℓ b ht_stop s i).length : ℝ) := by
    dsimp only [msg, outerProtocolMsg]
    rw [List.length_flatMap, ← Fin.sum_univ_def, Nat.cast_sum]
  set gap : ℝ := (1 / 4) * (m : ℝ) * Real.logb 2 F
  have hF_pos : (0 : ℝ) < (F : ℝ) := Nat.cast_pos.mpr hF_pos_nat
  have hlogF_ge : (64 : ℝ) ≤ Real.logb 2 F := by
    rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hF_pos,
      show (64 : ℝ) = ((64 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr hF_lo
  have hgap_pos : 0 < gap := by
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    dsimp only [gap]; nlinarith
  have hexp_msg_le : (∑ s, (μ s).toReal * ((msg s).length : ℝ)) ≤
      2 * (F : ℝ) + (∑ i : Fin F, Real.logb 2 (((F - i.val) * m).choose m)) -
        (∑ i ∈ halfSet, ∑ s, (μ s).toReal * (if goodXY s i then (1 : ℝ) else 0)) * gap := by
    have hsum_s : (∑ s, (μ s).toReal * ((msg s).length : ℝ)) ≤
        ∑ i : Fin F, ∑ s, (μ s).toReal *
          (2 + Real.logb 2 (((F - i.val) * m).choose m) -
            (if i ∈ halfSet ∧ goodXY s i then gap else 0)) := by
      simp_rw [hmsg_len, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun s _ =>
        mul_le_mul_of_nonneg_left (hround_le s i) ENNReal.toReal_nonneg
    have hrhs_eq : (∑ i : Fin F, ∑ s, (μ s).toReal *
          (2 + Real.logb 2 (((F - i.val) * m).choose m) -
            (if i ∈ halfSet ∧ goodXY s i then gap else 0))) =
        2 * (F : ℝ) + (∑ i : Fin F, Real.logb 2 (((F - i.val) * m).choose m)) -
          (∑ i ∈ halfSet, ∑ s, (μ s).toReal * (if goodXY s i then (1 : ℝ) else 0)) * gap := by
      have h1 (i : Fin F) : (∑ s, (μ s).toReal *
            (2 + Real.logb 2 (((F - i.val) * m).choose m) -
              (if i ∈ halfSet ∧ goodXY s i then gap else 0))) =
          (2 + Real.logb 2 (((F - i.val) * m).choose m)) -
            (if i ∈ halfSet then
              (∑ s, (μ s).toReal * (if goodXY s i then (1 : ℝ) else 0)) * gap else 0) := by
        rw [Finset.sum_congr rfl fun s _ => mul_sub _ _ _, Finset.sum_sub_distrib,
          ← Finset.sum_mul, PMF.sum_toReal μ, one_mul]
        congr 1
        by_cases hi : i ∈ halfSet
        · simp only [hi, true_and, ↓reduceIte, Finset.sum_mul]
          refine Finset.sum_congr rfl fun s _ => ?_
          split_ifs <;> ring
        · simp [hi]
      simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm (F : ℝ) 2]
      rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_mul]
    exact hsum_s.trans_eq hrhs_eq
  -- Bound ∑_{i ∈ halfSet} E[goodXY] ≥ (3 / 16) * F
  have hclaim41 := T.quarter_fanout_le_sum_prob_isGoodSeg D_det n stride μ
    (HardKeyValSeed.modeOps withQueries) hγ ht ℓ b hcost_lt.le hprobe_lt.le
  have hhalf_card : (halfSet.card : ℝ) ≤ (F : ℝ) / 2 := by
    have hc : halfSet.card = F / 2 := Fin.card_filter_val_lt.trans (by omega)
    obtain ⟨q, hq⟩ := hF_even
    rw [hc, hq, Nat.mul_div_cancel_left q (by omega)]; push_cast; linarith
  have hclaim42_sum : (∑ i ∈ halfSet, ∑ s, (μ s).toReal *
      (if ¬ (outerQualCandidates withQueries T D_det γ t ℓ b ht_stop s i ⊆
            outerNbrCandidates T ℓ b ht_stop s i) ∧
          T.IsGoodSeg D_det n stride (s.modeOps withQueries) γ t ℓ b i
        then (1 : ℝ) else 0)) ≤ (F : ℝ) / 16 := by
    calc _ ≤ ∑ _i ∈ halfSet, (1 / 8 : ℝ) := Finset.sum_le_sum fun i hi =>
          prob_not_qualSubsetNbr_and_isGoodSeg_le_one_eighth withQueries hU hU2 hV T D_det ℓ b
            ht_stop hF_lo hF_hi i (hinner i (Finset.mem_filter.mp hi).2)
      _ = (halfSet.card : ℝ) * (1 / 8) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (F : ℝ) / 16 := by linarith
  have hgoodXY_ge : (3 / 16 : ℝ) * (F : ℝ) ≤
      ∑ i ∈ halfSet, ∑ s, (μ s).toReal * (if goodXY s i then (1 : ℝ) else 0) := by
    have hpt_id (i : Fin F) (s : HardKeyValSeed U V n) :
        (if T.IsGoodSeg D_det n stride (s.modeOps withQueries) γ t ℓ b i then (1 : ℝ) else 0) -
          (if ¬ (outerQualCandidates withQueries T D_det γ t ℓ b ht_stop s i ⊆
                outerNbrCandidates T ℓ b ht_stop s i) ∧
              T.IsGoodSeg D_det n stride (s.modeOps withQueries) γ t ℓ b i
            then (1 : ℝ) else 0) =
        (if goodXY s i then (1 : ℝ) else 0) := by
      dsimp only [goodXY]
      by_cases h1 : T.IsGoodSeg D_det n stride (s.modeOps withQueries) γ t ℓ b i <;>
        by_cases h2 : outerQualCandidates withQueries T D_det γ t ℓ b ht_stop s i ⊆
          outerNbrCandidates T ℓ b ht_stop s i <;> simp [h1, h2]
    have hdiff : (∑ i ∈ halfSet, ∑ s, (μ s).toReal * (if goodXY s i then (1 : ℝ) else 0)) =
        (∑ i ∈ halfSet, ∑ s, (μ s).toReal *
          (if T.IsGoodSeg D_det n stride (s.modeOps withQueries) γ t ℓ b i then (1 : ℝ) else 0)) -
        (∑ i ∈ halfSet, ∑ s, (μ s).toReal *
          (if ¬ (outerQualCandidates withQueries T D_det γ t ℓ b ht_stop s i ⊆
                outerNbrCandidates T ℓ b ht_stop s i) ∧
              T.IsGoodSeg D_det n stride (s.modeOps withQueries) γ t ℓ b i
            then (1 : ℝ) else 0)) := by
      simp_rw [← Finset.sum_sub_distrib, ← mul_sub, hpt_id]
    linarith
  have hblock : (T.blockSize (ℓ + 1) : ℝ) = (m : ℝ) * (F : ℝ) := by simp [m, F]
  have hm_real : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_ge2
  have hslack : 2 * (F : ℝ) ≤ (1 / 64) * ((m : ℝ) * (F : ℝ)) * Real.logb 2 F := by nlinarith
  have hprod_ge := mul_le_mul_of_nonneg_right hgoodXY_ge hgap_pos.le
  dsimp only [gap] at hprod_ge hexp_msg_le
  nlinarith

/-- **Lemma 3.2 (`OuterLemma`)** on `insertQueryDeleteDist` ([LiLiangYuZhou2023], Section 3,
Lemma 3.2, p. 12 / PDF p. 13 and Section 4, pp. 13–20 / PDF pp. 14–21, with independent
`R_outer`, `R_inner`, and child-segment `m_ℓ` alignment): either
`E[nodeCost] ≥ (γ / 100) * m_{ℓ+1}` or `E[nodeProbes] ≥ (1 / 16) * m_{ℓ+1} * t`. -/
theorem outer_lemma_insertQueryDelete {U V n cells w : ℕ} {R_outer R_inner γ t : ℝ}
    (hU : 4 * n ≤ U) (hV : 1 ≤ V)
    (hspace_outer : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R_outer)
    (hspace_inner : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R_inner)
    (T : MetaTree) {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2)
    (hγ : 0 < γ) (ht : 0 < t) {ℓ b : ℕ} (hℓ : 1 ≤ ℓ)
    (ht_stop : T.nodeStop (ℓ + 1) b ≤ n)
    (hm_lo : (n : ℝ) ^ (1 - γ / 2) ≤ (T.blockSize ℓ : ℝ))
    (hF_lo : 2 ^ 64 ≤ T.fanout (ℓ + 1))
    (hF_hi : (T.fanout (ℓ + 1) : ℝ) ≤ (γ / 2) * Real.logb 2 U)
    (hR_outer : 100 * R_outer ≤ (T.blockSize (ℓ + 1) : ℝ) * Real.logb 2 (T.fanout (ℓ + 1)))
    (hbudget_inner : R_inner + 11 * (T.blockSize ℓ : ℝ) + 6 * (T.blockSize ℓ : ℝ) * t +
      γ * (T.blockSize ℓ : ℝ) * (w : ℝ) + (3 / 2) * γ * (T.blockSize ℓ : ℝ) * Real.logb 2 U ≤
      ((T.blockSize ℓ : ℝ) / 2) * Real.logb 2 ((U : ℝ) / (n : ℝ))) :
    (γ / 100) * (T.blockSize (ℓ + 1) : ℝ) ≤
        ∑' ops, (insertQueryDeleteDist U V n (by omega) hV ops).toReal *
          (T.nodeCost D_det n 3 ops ℓ b : ℝ) ∨
      (1 / 16) * (T.blockSize (ℓ + 1) : ℝ) * t ≤
        ∑' ops, (insertQueryDeleteDist U V n (by omega) hV ops).toReal *
          (T.nodeProbes D_det n 3 ops (ℓ + 1) b : ℝ) := by
  have hm_ge2 : 2 ≤ T.blockSize ℓ :=
    (Nat.pow_le_pow_right (by omega) hℓ).trans (T.two_pow_le_blockSize ℓ)
  have hF_ge2 : 2 ≤ T.fanout (ℓ + 1) := T.two_le_fanout (Nat.le_add_left 1 ℓ)
  have hm_n : 2 * T.blockSize ℓ ≤ n := by
    have h1 : 2 * T.blockSize ℓ ≤ T.blockSize ℓ * T.fanout (ℓ + 1) := by
      rw [mul_comm 2]; exact Nat.mul_le_mul_left _ hF_ge2
    have h2 : T.blockSize (ℓ + 1) ≤ T.nodeStop (ℓ + 1) b :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos b)
    rw [T.blockSize_succ] at h2; omega
  have hU2 : 2 ≤ U := by omega
  exact
    outer_node_lower_bound true (by omega) hU2 hV hspace_outer T
      (by simpa only [modeHorizon, modeStride, ↓reduceIte,
        show n + 3 * n = 4 * n by ring] using hcorr)
      hγ ht hℓ ht_stop hF_lo hF_hi hR_outer fun i hi => by
        have hFh : 2 ≤ T.fanout (ℓ + 1) - i.val := by
          have h4 : 2 ^ 2 ≤ T.fanout (ℓ + 1) :=
            (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 2 ≤ 64)).trans hF_lo
          omega
        have hrest_ge : 2 * T.blockSize ℓ ≤ (T.fanout (ℓ + 1) - i.val) * T.blockSize ℓ :=
          Nat.mul_le_mul_right _ hFh
        classical
        dsimp only
        have hfilt (t₀ m : ℕ) (h : t₀ + m ≤ n) (s : HardKeyValSeed U V n)
            (P : Finset (Finset (Fin U))) :
            P.filter (IsModeSeedConsistent true D_det t₀ m h γ t s) =
              P.filter (IsSeedConsistent D_det t₀ m h γ t s) :=
          Finset.filter_congr fun B _ => isModeSeedConsistent_true_iff D_det _ _ _ γ t s B
        simp_rw [hfilt]
        exact expected_card_cappedConsistent_segmentRest_lt_half_le hU hV hm_n hγ hm_lo
          hspace_inner hbudget_inner hcorr hm_ge2 hrest_ge
          (nodeStart_add_rest_le T ht_stop i.val i.isLt.le)

end Cslib.DataStructure.Dictionary.CellProbe
