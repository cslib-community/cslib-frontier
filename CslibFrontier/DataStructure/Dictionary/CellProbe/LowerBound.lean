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
import CslibFrontier.Foundations.Data.Finset.OrderEmb
import CslibFrontier.Foundations.Data.List.Counting
import CslibFrontier.Foundations.Data.Nat.Choose.Real
import CslibFrontier.Probability.Coding.PrefixFreeEntropy
import CslibFrontier.Probability.Conditioning
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Logic.Equiv.Fintype

/-!
# Multi-Level Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries

End-to-end cell-probe lower bounds for dynamic succinct dictionaries from Li, Liang, Yu, and Zhou
([LiLiangYuZhou2023]; locators below follow `arXiv:2306.02253v3`, where printed page `p` is PDF
page `p + 1`):

* **Section 8.1 Modified Inner Game (Lemma 8.1, pp. 28–30 / PDF pp. 29–31):** query-free inner
  communication protocol recovering `(K \ D, v_{A ∪ B}, v_K)` from `(a, b, d)` via `C_mix` and
  `C_B`, yielding both the update-only `OuterLemma` (`outer_lemma_insertDelete`) and large-value
  coverage (`V > U ^ 3`) for the query-inclusive bounds (`outer_lemma_largeVal_insertQueryDelete`).
* **Theorem 1.1 / Theorem 3.1 (pp. 1, 10–13 / PDF pp. 2, 11–14):** `Ω(k)` amortized cell probes
  under `R ≤ O(n log^{(k)} n)` bits of redundancy (`1 ≤ k ≤ log* n`), specializing at `k = log* n`
  to `Ω(log* n)` expected probes per operation for `R = O(n)`.
* **Theorem 1.2 / Theorem 6.1 (pp. 2, 25–26 / PDF pp. 3, 26–27):** `Ω(log(n / max R 1))` amortized
  cell probes for `R`-redundancy dynamic dictionaries (`0 ≤ R ≤ n`), together with the combined
  `Ω(log* n + log(n / max R 1))` trade-off across `0 ≤ R ≤ O(n)` and all `V ≥ 1` (Section 7,
  pp. 26–27 / PDF pp. 27–28).
* **Theorem 1.3(1)–(2) (pp. 2, 27–30 / PDF pp. 3, 28–31):** update-only `Ω(k)` and
  `Ω(log(n / max R 1))` cell-probe lower bounds on `insertDeleteDist` for `U ≥ 3 * n` and
  `V ≥ U ^ (2 + α_V) / n ^ 2` without any query-time constraint.

Original formalization adaptations of [LiLiangYuZhou2023] (`arXiv:2306.02253v3`):
1. **Deterministic `c = 1` probe cap (`Sections 4.2, 5.1, 5.2, and 8.1`):** `IsModeSeedConsistent`
   enforces `|S_A|, |S_B| ≤ m * t` directly inside the consistency event (incurring
   `≤ (1 / 16) * λ_{ℓ+1}` probe-cap loss via Markov's inequality on `nodeProbes` in
   `MetaTree.sum_prob_not_isGoodSeg_le`), so Step 5 of Lemma 8.1 encodes `S_A ∩ S_B ⊆ S_B` and
   `Diff ⊆ S_A ∩ S_B` in `≤ 2 * m * t` bits deterministically on every consistent outcome without
   conditional expectation inflation on `{W = 1}`.
2. **Internal Markov sub-conditioning in Step 6 (`Section 8.1`):** to encode `C_B` prefix-freely
   within its decoded dictionary fiber `stateFiber` on `{W = 1}`, Lemma 8.1 sub-conditions on
   `c(T_B) ≤ 2 ^ (R + 1) * U ^ (γ * m)` over the uniform marginal of `T_B` (`Pr[bad] ≤
   (1 / 2) * U ^ (-γ * m)`), costing `R + 2 + γ * m * log₂ U` bits in Step 6 and tightening Lemma
   8.1's value budget by `2 * γ * m * log₂ U` while leaving Theorem 1.3's asymptotic hypothesis
   `V ≥ U ^ (2 + α_V) / n ^ 2` unchanged (choosing `(5 + c_w) * γ ≤ min (1 / 4) (α_V / 16)`).
3. **Public deterministic `IndexedScheme` endpoints (`Section 3`):** every headline theorem is
   exported first for deterministic step-indexed schemes `D_det : CellProbe.IndexedScheme ...` exact
   on `validHistoriesUpTo`, followed by its zero-error `CellProbe.Randomized.Scheme` corollary via
   Yao coin-fixing (`exists_det_indexedScheme_insertQueryDeleteDist` /
   `exists_det_indexedScheme_insertDeleteDist`).

Model and boundary conventions:
* **Zero-error oblivious randomization:** randomized lower bounds (`expectedSeqProbes_*`) apply to
  zero-error (Las Vegas) `CellProbe.Randomized.Scheme`s on oblivious operation distributions;
  bounded-error (Monte Carlo) schemes and adaptive sequence adversaries are out of scope.
* **Trailing `+ 1` correctness horizon (`4 * n + 1` and `3 * n + 1`):** on `insertDeleteDist`
  (`3 * n` update steps returning `PUnit`), requiring correctness up to length `3 * n + 1` ensures
  one trailing admissible `.query` step can witness `decodeDict` at every step `≤ 3 * n` while
  charging probes only on the `3 * n` update sequence itself.
* **`R = n` boundary in Theorem 1.2 / 1.3(2):** at `R = n` (`n ≥ 1`), `log₂(n / max R 1) = 0`, so
  the standalone sublinear-redundancy bounds reduce to `0 ≤ E[seqProbes]`; the `Ω(n * log* n)` and
  combined `Ω(n * (log* n + log₂(n / max R 1)))` theorems supply the active lower bound for
  `R = Θ(n)`.

## Main definitions

* `Cslib.DataStructure.Dictionary.CellProbe.queryFreeInnerDist`: conditional `(seed, B)`
  distribution for the query-free inner game of Section 8.1 (Lemma 8.1).

## Main results

* `Cslib.DataStructure.Dictionary.CellProbe.prob_isModeSeedConsistent_queryFreeInnerDist_le`,
  `Cslib.DataStructure.Dictionary.CellProbe.expected_card_modeConsistent_segmentRest_lt_half_le`,
  `Cslib.DataStructure.Dictionary.CellProbe.outer_lemma_insertDelete`,
  `Cslib.DataStructure.Dictionary.CellProbe.outer_lemma_largeVal_insertQueryDelete`: Lemma 8.1 and
  the update-only and large-value Outer Lemmas.
* `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_ge_linear`,
  `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_ge_of_outer_tree`,
  `Cslib.DataStructure.Dictionary.CellProbe.optBits_le_benchmarkBits_add`,
  `Cslib.DataStructure.Dictionary.CellProbe.optBits_two_pow_le_benchmarkBits_add_one`: base `Ω(n)`
  bound, multi-level `MetaTree` probe aggregation, and `Dynamic.optBits` bridges.
* `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_ge_of_iterLog_redundancy`,
  `Cslib.DataStructure.Dictionary.CellProbe.expectedSeqProbes_ge_of_iterLog_redundancy`,
  `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_ge_iterLogStar`,
  `Cslib.DataStructure.Dictionary.CellProbe.expectedSeqProbes_ge_iterLogStar`: Theorem 1.1 / 3.1.
* `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_ge_of_sublinear_redundancy`,
  `Cslib.DataStructure.Dictionary.CellProbe.expectedSeqProbes_ge_of_sublinear_redundancy`,
  `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_ge_iterLogStar_add_log_div`,
  `Cslib.DataStructure.Dictionary.CellProbe.expectedSeqProbes_ge_iterLogStar_add_log_div`:
  Theorem 1.2 / 6.1 and combined `Ω(log* n + log(n / max R 1))` bound.
* `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_update_ge_iterLog`,
  `Cslib.DataStructure.Dictionary.CellProbe.expectedSeqProbes_update_ge_iterLog`,
  `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_update_ge_iterLogStar`,
  `Cslib.DataStructure.Dictionary.CellProbe.expectedSeqProbes_update_ge_iterLogStar`,
  `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_update_ge_sublinear`,
  `Cslib.DataStructure.Dictionary.CellProbe.expectedSeqProbes_update_ge_sublinear`:
  Theorem 1.3(1)–(2).
* `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_update_ge_iterLogStar_add_log_div`
* `Cslib.DataStructure.Dictionary.CellProbe.expectedSeqProbes_update_ge_iterLogStar_add_log_div`:
  combined update-only trade-off.

## References

* [T. Li, J. Liang, H. Yu and R. Zhou, *Tight Cell-Probe Lower Bounds for Dynamic Succinct
  Dictionaries*][LiLiangYuZhou2023], Sections 1, 3, 4.2, 5.1, 5.2, 6, 7, and 8
  (`arXiv:2306.02253v3`).
* [M. L. Fredman and M. E. Saks, *The cell probe complexity of dynamic data
  structures*][FredmanSaks1989]
* [P. B. Miltersen, *Cell Probe Complexity — a Survey*][Miltersen1999]
* [A. C.-C. Yao, *Probabilistic Computations: Toward a Unified Measure of Complexity*][Yao1977]
-/

public section

open scoped BigOperators ENNReal

namespace Cslib.DataStructure.Dictionary.CellProbe

open Cslib.CellProbe Cslib.DataStructure Cslib.DataStructure.Dictionary
open Cslib.BitString Cslib.Probability Cslib.Probability.Coding InformationTheory
open Finset (orderSubset orderSubset_apply image_orderSubset embSetPermEquiv)

/-! ### Part A: Section 8.1 Modified Inner Game (Lemma 8.1) -/

/-! #### Candidate segment replay and dictionary-state multiplicity fibers -/

open Classical in
private noncomputable def stateFiber {U cells w : ℕ}
    (D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w) (stepIdx : ℕ)
    (st : Dictionary.State U) : Finset (Mem cells w) :=
  Finset.univ.filter fun C => decodeDict D_det stepIdx C = st

open Classical in
private theorem sum_card_stateFiber_le {U V n cells w : ℕ}
    (D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w) (stepIdx : ℕ) :
    (∑ p : SizedDict U V n, (stateFiber D_det stepIdx p.val).card) ≤
      2 ^ (cells * w) := by
  have hdisj : ((Finset.univ : Finset (SizedDict U V n)) :
      Set (SizedDict U V n)).PairwiseDisjoint
      (fun p => stateFiber D_det stepIdx p.val) := by
    intro p₁ _ p₂ _ hne
    refine Finset.disjoint_left.mpr fun C h₁ h₂ => hne (Subtype.ext ?_)
    dsimp only [stateFiber] at h₁ h₂
    rw [Finset.mem_filter] at h₁ h₂
    exact h₁.2.symm.trans h₂.2
  calc (∑ p : SizedDict U V n, (stateFiber D_det stepIdx p.val).card)
      = ((Finset.univ : Finset (SizedDict U V n)).biUnion
          (fun p => stateFiber D_det stepIdx p.val)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.univ : Finset (Mem cells w)).card := Finset.card_le_univ _
    _ = 2 ^ (cells * w) := by
        simp only [Finset.card_univ, Mem, Fintype.card_pi, Fintype.card_fin,
          Finset.prod_const]
        rw [← pow_mul, mul_comm]

private def modeCandUnit (withQueries : Bool) {U V m : ℕ}
    (d b : Fin m → Fin U) (kv : Fin U → Fin V) (r : Fin m) : List (Dynamic.Op U) :=
  if withQueries then
    [.query (d r), .delete (d r), .insert (b r) (kv (b r)).val]
  else
    [.delete (d r), .insert (b r) (kv (b r)).val]

private def modeCandPrefix (withQueries : Bool) {U V m : ℕ}
    (d b : Fin m → Fin U) (kv : Fin U → Fin V) (k : ℕ) : List (Dynamic.Op U) :=
  ((List.finRange m).take k).flatMap (modeCandUnit withQueries d b kv)

private theorem modeCandPrefix_full (withQueries : Bool) {U V m : ℕ}
    (d b : Fin m → Fin U) (kv : Fin U → Fin V) :
    modeCandPrefix withQueries d b kv m =
      if withQueries then candidateQueryDeleteInsertOps d b kv
      else candidateDeleteInsertOps d b kv := by
  have htk : (List.finRange m).take m = List.finRange m := List.take_of_length_le (by simp)
  cases withQueries <;> (dsimp only [modeCandPrefix, ↓reduceIte, Bool.false_eq_true]; rw [htk]; rfl)

private theorem modeCandPrefix_succ (withQueries : Bool) {U V m : ℕ}
    (d b : Fin m → Fin U) (kv : Fin U → Fin V) {k : ℕ} (hk : k < m) :
    modeCandPrefix withQueries d b kv (k + 1) =
      modeCandPrefix withQueries d b kv k ++ modeCandUnit withQueries d b kv ⟨k, hk⟩ := by
  dsimp only [modeCandPrefix]
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [hk]), Option.toList_some,
    List.flatMap_append, List.flatMap_singleton]
  simp

private theorem validHistory_and_run_modeCandidateOps (withQueries : Bool) {U V n t₀ m : ℕ}
    (s : HardKeyValSeed U V n) (ht₀ : t₀ + m ≤ n) {B : Finset (Fin U)} (hB : B.card = m)
    (hdisj : Disjoint B (s.activeKeys t₀ (Nat.le_of_add_right_le ht₀))) :
    let stride := modeStride withQueries
    let pref_bef := (s.modeOps withQueries).take (n + stride * t₀)
    let ops_B := s.modeCandidateOps withQueries t₀ m ht₀ B hB
    let D_set := Finset.univ.image (segDeletedKeys s.keys s.delPerm t₀ m ht₀)
    (Dynamic.spec U V n).ValidHistory (Dictionary.empty U) (pref_bef ++ ops_B) ∧
      (pref_bef ++ ops_B).length = n + stride * (t₀ + m) ∧
      ((Dynamic.spec U V n).run (Dictionary.empty U) (pref_bef ++ ops_B)).1 =
        fun u => if u ∈ (s.activeKeys t₀ (Nat.le_of_add_right_le ht₀) \ D_set) ∪ B
          then some (s.kv u).val else none := by
  let stride := modeStride withQueries
  let ht₀_n : t₀ ≤ n := Nat.le_of_add_right_le ht₀
  let pref_bef := (s.modeOps withQueries).take (n + stride * t₀)
  let d := segDeletedKeys s.keys s.delPerm t₀ m ht₀
  let π := (embSetPermEquiv (Fin U) m (segInsertedKeys s.keys t₀ m ht₀)).2
  let b := orderSubset B hB π
  let K := s.activeKeys t₀ ht₀_n
  have hpref_vh : (Dynamic.spec U V n).ValidHistory (Dictionary.empty U) pref_bef :=
    s.validHistory_take_modeOps withQueries ht₀_n
  have hpref_len : pref_bef.length = n + stride * t₀ := s.length_take_modeOps withQueries ht₀_n
  have hpref_st : ((Dynamic.spec U V n).run (Dictionary.empty U) pref_bef).1 =
      fun u => if u ∈ K then some (s.kv u).val else none := by
    rw [s.run_take_modeOps_fst withQueries ht₀_n, windowDict_coe]
    funext u
    by_cases hu : u ∈ K
    · simp only [hu, ↓reduceIte]
      dsimp only [K, HardKeyValSeed.activeKeys] at hu
      rw [Finset.mem_map] at hu
      obtain ⟨k, _, rfl⟩ := hu
      rw [dictOfEmb_apply_self, windowVals_apply, windowEmb_apply]
    · simp only [hu, ↓reduceIte]
      refine dictOfEmb_apply_eq_none _ _ fun k heq => hu ?_
      dsimp only [K, HardKeyValSeed.activeKeys]
      exact Finset.mem_map.mpr ⟨k, Finset.mem_univ k, heq⟩
  have hd_mem_K (r : Fin m) : d r ∈ K := by
    dsimp only [K, HardKeyValSeed.activeKeys]
    refine Finset.mem_map.mpr ⟨⟨r.val, by omega⟩, Finset.mem_univ _, ?_⟩
    rw [windowEmb_apply]
    simp only [d, segDeletedKeys_apply, HardKeyValSeed.permKeyEmb,
      Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
    rw [liftDelPerm_apply_lt s.delPerm (by have := r.isLt; omega)]
  have hb_mem_B (r : Fin m) : b r ∈ B := by
    dsimp only [b]; rw [orderSubset_apply]; exact Finset.orderEmbOfFin_mem B hB (π r)
  have hloop : ∀ k : ℕ, (hk : k ≤ m) →
      let D_k := (Finset.univ.filter fun r : Fin m => r.val < k).image d
      let B_k := (Finset.univ.filter fun r : Fin m => r.val < k).image b
      (Dynamic.spec U V n).ValidHistory (Dictionary.empty U)
        (pref_bef ++ modeCandPrefix withQueries d b s.kv k) ∧
      ((Dynamic.spec U V n).run (Dictionary.empty U)
        (pref_bef ++ modeCandPrefix withQueries d b s.kv k)).1 =
        (fun u => if u ∈ (K \ D_k) ∪ B_k then some (s.kv u).val else none) := by
    intro k hk
    induction k with
    | zero =>
      have hempD : (Finset.univ.filter fun r : Fin m => r.val < 0).image d = ∅ := by simp
      have hempB : (Finset.univ.filter fun r : Fin m => r.val < 0).image b = ∅ := by simp
      simp only [modeCandPrefix, List.take_zero, List.flatMap_nil, List.append_nil,
        hempD, hempB, Finset.sdiff_empty, Finset.union_empty]
      exact ⟨hpref_vh, hpref_st⟩
    | succ k ih =>
      have hk_lt : k < m := hk
      obtain ⟨hvh_k, hst_k⟩ := ih (Nat.le_of_succ_le hk)
      set D_k := (Finset.univ.filter fun r : Fin m => r.val < k).image d
      set B_k := (Finset.univ.filter fun r : Fin m => r.val < k).image b
      set s_k := ((Dynamic.spec U V n).run (Dictionary.empty U)
        (pref_bef ++ modeCandPrefix withQueries d b s.kv k)).1
      let r₀ : Fin m := ⟨k, hk_lt⟩
      have hdr_not_Dk : d r₀ ∉ D_k := by
        simp only [D_k, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        rintro ⟨r', hr', heq⟩
        have := congrArg Fin.val (d.injective heq); dsimp [r₀] at this; omega
      have hdr_in : d r₀ ∈ (K \ D_k) ∪ B_k :=
        Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hd_mem_K r₀, hdr_not_Dk⟩)
      have hdr_some : (s_k (d r₀)).isSome := by
        rw [hst_k]; simp [hdr_in]
      have hflt_lt : (Finset.univ.filter fun r : Fin m => r.val < k) = Finset.Iio r₀ := by
        simpa only [Fin.lt_def] using (Finset.filter_gt_eq_Iio :
          Finset.univ.filter (· < r₀) = Finset.Iio r₀)
      have hflt_le : (Finset.univ.filter fun r : Fin m => r.val < k + 1) = Finset.Iic r₀ := by
        simpa only [Nat.lt_succ_iff, Fin.le_def] using (Finset.filter_ge_eq_Iic :
          Finset.univ.filter (· ≤ r₀) = Finset.Iic r₀)
      have hcard_D : D_k.card = k := by
        rw [Finset.card_image_of_injective _ d.injective, hflt_lt, Fin.card_Iio]
      have hcard_B : B_k.card = k := by
        rw [Finset.card_image_of_injective _ b.injective, hflt_lt, Fin.card_Iio]
      have hdom_sk : Dictionary.dom s_k = (K \ D_k) ∪ B_k := by
        ext u; rw [Dictionary.mem_dom_iff]
        rw [show s_k = _ from hst_k]
        by_cases h : u ∈ (K \ D_k) ∪ B_k <;> simp [h]
      have hcard_sk : (Dictionary.dom s_k).card = n := by
        rw [hdom_sk, Finset.card_union_of_disjoint, Finset.card_sdiff]
        · have hsubD : D_k ⊆ K := by
            intro x hx; obtain ⟨r', _, rfl⟩ := Finset.mem_image.mp hx; exact hd_mem_K r'
          have hK_card : K.card = n := by simp [K, HardKeyValSeed.activeKeys]
          rw [Finset.inter_eq_left.mpr hsubD, hK_card, hcard_D, hcard_B]; omega
        · refine Finset.disjoint_left.mpr fun x hxK hxB => ?_
          obtain ⟨r', _, rfl⟩ := Finset.mem_image.mp hxB
          exact Finset.disjoint_left.mp hdisj (hb_mem_B r') (Finset.mem_sdiff.mp hxK).1
      have hcard_del : (Dictionary.dom (Function.update s_k (d r₀) none)).card < n := by
        rw [Dynamic.card_dom_delete_eq_of_isSome hdr_some, hcard_sk]; omega
      have hupd_st : Function.update (Function.update s_k (d r₀) none) (b r₀)
          (some (s.kv (b r₀)).val) =
          (fun u => if u ∈ (K \ (Finset.univ.filter fun r : Fin m => r.val < k + 1).image d) ∪
            (Finset.univ.filter fun r : Fin m => r.val < k + 1).image b
            then some (s.kv u).val else none) := by
        funext u
        have himg_succ (f : Fin m ↪ Fin U) :
            (Finset.univ.filter fun r : Fin m => r.val < k + 1).image f =
              insert (f r₀) ((Finset.univ.filter fun r : Fin m => r.val < k).image f) := by
          rw [hflt_le, hflt_lt, ← Finset.insert_Iio, Finset.image_insert]
        have hD1 : (Finset.univ.filter fun r : Fin m => r.val < k + 1).image d =
            insert (d r₀) D_k := himg_succ d
        have hB1 : (Finset.univ.filter fun r : Fin m => r.val < k + 1).image b =
            insert (b r₀) B_k := himg_succ b
        rw [hD1, hB1]
        by_cases hub : u = b r₀
        · subst hub; simp
        · rw [Function.update_of_ne hub]
          by_cases hud : u = d r₀
          · subst hud
            have hnotB : d r₀ ∉ B_k := fun hxB => by
              obtain ⟨r', _, heq⟩ := Finset.mem_image.mp hxB
              exact Finset.disjoint_left.mp hdisj (heq ▸ hb_mem_B r') (hd_mem_K r₀)
            simp [hub, hnotB]
          · rw [Function.update_of_ne hud, show s_k = _ from hst_k]
            simp [hub, hud]
      rw [modeCandPrefix_succ withQueries d b s.kv hk_lt, ← List.append_assoc,
        StateTransitionSpec.validHistory_append,
        (Dynamic.spec U V n).run_append (Dictionary.empty U)
          (pref_bef ++ modeCandPrefix withQueries d b s.kv k)]
      dsimp only
      cases withQueries
      · simp only [modeCandUnit, Bool.false_eq_true, ↓reduceIte,
          StateTransitionSpec.validHistory_cons, StateTransitionSpec.validHistory_nil,
          Dynamic.spec]
        exact ⟨⟨hvh_k, trivial, ⟨Or.inl hcard_del, (s.kv (b r₀)).isLt⟩, trivial⟩, hupd_st⟩
      · simp only [modeCandUnit, ↓reduceIte,
          StateTransitionSpec.validHistory_cons, StateTransitionSpec.validHistory_nil,
          Dynamic.spec]
        exact ⟨⟨hvh_k, trivial, trivial, ⟨Or.inl hcard_del, (s.kv (b r₀)).isLt⟩, trivial⟩,
          hupd_st⟩
  obtain ⟨hvh_m, hst_m⟩ := hloop m le_rfl
  have hfull : modeCandPrefix withQueries d b s.kv m =
      s.modeCandidateOps withQueries t₀ m ht₀ B hB := by
    rw [modeCandPrefix_full, HardKeyValSeed.modeCandidateOps_eq]
    cases withQueries
    · simp only [Bool.false_eq_true, ↓reduceIte, HardKeyValSeed.candidateUpdateOps_eq]; rfl
    · simp only [↓reduceIte, HardKeyValSeed.candidateOps_eq]; rfl
  have hDm : (Finset.univ.filter fun r : Fin m => r.val < m).image d = Finset.univ.image d := by
    congr 1; ext r; simp
  have hBm : (Finset.univ.filter fun r : Fin m => r.val < m).image b = B := by
    have h1 : (Finset.univ.filter fun r : Fin m => r.val < m) = Finset.univ := by
      ext r; simp
    rw [h1]
    exact image_orderSubset B hB π
  rw [hfull] at hvh_m hst_m
  rw [hDm, hBm] at hst_m
  have hlen_B : (s.modeCandidateOps withQueries t₀ m ht₀ B hB).length = stride * m := by
    rw [← hfull]
    have htk : (List.finRange m).take m = List.finRange m := List.take_of_length_le (by simp)
    dsimp only [modeCandPrefix, stride, modeStride]
    rw [htk]
    cases withQueries
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [List.length_flatMap_of_forall_length_eq (k := 2) (fun _ _ => rfl),
        List.length_finRange, Nat.mul_comm]
    · simp only [↓reduceIte]
      rw [List.length_flatMap_of_forall_length_eq (k := 3) (fun _ _ => rfl),
        List.length_finRange, Nat.mul_comm]
  refine ⟨hvh_m, ?_, hst_m⟩
  rw [List.length_append, hpref_len, hlen_B]; ring

/-! #### Query-free inner pool symmetry, `T_B` uniformity, and Markov sub-conditioning -/

private def actSeed8Equiv {U V n : ℕ} [NeZero V] (τ : Equiv.Perm (Fin U)) (δ : Fin U → Fin V) :
    HardKeyValSeed U V n ≃ HardKeyValSeed U V n where
  toFun s :=
    { keys := s.keys.trans τ.toEmbedding
      kv := fun u => s.kv (τ.symm u) + δ u
      delPerm := s.delPerm }
  invFun s :=
    { keys := s.keys.trans τ.symm.toEmbedding
      kv := fun u => s.kv (τ u) - δ (τ u)
      delPerm := s.delPerm }
  left_inv s := by
    cases s
    simp only [HardKeyValSeed.mk.injEq, and_true]
    exact ⟨by ext i; simp, by funext u; simp⟩
  right_inv s := by
    cases s
    simp only [HardKeyValSeed.mk.injEq, and_true]
    exact ⟨by ext i; simp, by funext u; simp⟩

private theorem actSeed8Equiv_activeKeys {U V n : ℕ} [NeZero V] (τ : Equiv.Perm (Fin U))
    (δ : Fin U → Fin V) (s : HardKeyValSeed U V n) (t₀ : ℕ) (ht : t₀ ≤ n) :
    (actSeed8Equiv τ δ s).activeKeys t₀ ht = (s.activeKeys t₀ ht).map τ.toEmbedding := by
  ext u
  simp only [HardKeyValSeed.activeKeys, HardKeyValSeed.permKeyEmb, actSeed8Equiv,
    Equiv.coe_fn_mk, Finset.mem_map, windowEmb_apply, Function.Embedding.trans_apply,
    Equiv.coe_toEmbedding]
  exact ⟨fun ⟨k, _, hk⟩ => ⟨_, ⟨k, Finset.mem_univ k, rfl⟩, hk⟩,
    fun ⟨_, ⟨k, _, rfl⟩, hk⟩ => ⟨k, Finset.mem_univ k, hk⟩⟩

private theorem actSeed8Equiv_insertedSet {U V n : ℕ} [NeZero V] (τ : Equiv.Perm (Fin U))
    (δ : Fin U → Fin V) (s : HardKeyValSeed U V n) (t₀ r : ℕ) (hr : t₀ + r ≤ n) :
    (actSeed8Equiv τ δ s).insertedSet t₀ r hr = (s.insertedSet t₀ r hr).map τ.toEmbedding := by
  ext u
  simp only [HardKeyValSeed.insertedSet, segInsertedKeys_apply, actSeed8Equiv, Equiv.coe_fn_mk,
    Finset.mem_map, Finset.mem_image, Finset.mem_univ, true_and,
    Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
  exact ⟨fun ⟨j, hj⟩ => ⟨_, ⟨j, rfl⟩, hj⟩, fun ⟨_, ⟨j, rfl⟩, hj⟩ => ⟨j, hj⟩⟩

private theorem actSeed8Equiv_deletedSet {U V n : ℕ} [NeZero V] (τ : Equiv.Perm (Fin U))
    (δ : Fin U → Fin V) (s : HardKeyValSeed U V n) (t₀ m : ℕ) (ht₀ : t₀ + m ≤ n) :
    Finset.univ.image (segDeletedKeys (actSeed8Equiv τ δ s).keys (actSeed8Equiv τ δ s).delPerm
        t₀ m ht₀) =
      (Finset.univ.image (segDeletedKeys s.keys s.delPerm t₀ m ht₀)).map τ.toEmbedding := by
  ext u
  simp only [segDeletedKeys_apply, actSeed8Equiv, Equiv.coe_fn_mk,
    Finset.mem_map, Finset.mem_image, Finset.mem_univ, true_and,
    Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
  exact ⟨fun ⟨j, hj⟩ => ⟨_, ⟨j, rfl⟩, hj⟩, fun ⟨_, ⟨j, rfl⟩, hj⟩ => ⟨j, hj⟩⟩

open Classical in
private noncomputable def sizedDictOfFinset {U V n : ℕ} (S : Finset (Fin U)) (hS : S.card = n)
    (kv : Fin U → Fin V) : SizedDict U V n :=
  ⟨fun u => if u ∈ S then some (kv u).val else none,
   by
     have hdom : Dictionary.dom (fun u => if u ∈ S then some (kv u).val else none) = S := by
       ext u; by_cases hu : u ∈ S <;> simp [Dictionary.dom, hu]
     rw [hdom]; exact hS,
   fun u w hw => by
     by_cases hu : u ∈ S
     · simp only [hu, ↓reduceIte, Option.some.injEq] at hw
       exact hw ▸ (kv u).isLt
     · simp [hu] at hw⟩

open Classical in
private noncomputable def pairBOf {U V n : ℕ} (t₀ m : ℕ) (ht₀ : t₀ + m ≤ n)
    (sb : HardKeyValSeed U V n × Finset (Fin U)) : SizedDict U V n :=
  let K_cand := (sb.1.activeKeys t₀ (Nat.le_of_add_right_le ht₀) \
    Finset.univ.image (segDeletedKeys sb.1.keys sb.1.delPerm t₀ m ht₀)) ∪ sb.2
  if hK : K_cand.card = n then
    sizedDictOfFinset K_cand hK sb.1.kv
  else
    sizedDictOfFinset (sb.1.activeKeys t₀ (Nat.le_of_add_right_le ht₀))
      (by simp [HardKeyValSeed.activeKeys]) sb.1.kv

private theorem card_sdiff_deleted_union_eq {U V n t₀ m : ℕ} (s : HardKeyValSeed U V n)
    (ht₀ : t₀ + m ≤ n) {B : Finset (Fin U)} (hB : B.card = m)
    (hdisj : Disjoint B (s.activeKeys t₀ (Nat.le_of_add_right_le ht₀))) :
    ((s.activeKeys t₀ (Nat.le_of_add_right_le ht₀) \
      Finset.univ.image (segDeletedKeys s.keys s.delPerm t₀ m ht₀)) ∪ B).card = n := by
  let ht₀_n : t₀ ≤ n := Nat.le_of_add_right_le ht₀
  let K := s.activeKeys t₀ ht₀_n
  let D := Finset.univ.image (segDeletedKeys s.keys s.delPerm t₀ m ht₀)
  have hsubD : D ⊆ K := by
    intro u hu
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hu
    dsimp only [K, HardKeyValSeed.activeKeys]
    refine Finset.mem_map.mpr ⟨⟨r.val, by omega⟩, Finset.mem_univ _, ?_⟩
    rw [windowEmb_apply]
    simp only [segDeletedKeys_apply, HardKeyValSeed.permKeyEmb,
      Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
    rw [liftDelPerm_apply_lt s.delPerm (by have := r.isLt; omega)]
  have hD_card : D.card = m :=
    (Finset.card_image_of_injective _ (segDeletedKeys s.keys s.delPerm t₀ m ht₀).injective).trans
      (by simp)
  have hK_card : K.card = n := by simp [K, HardKeyValSeed.activeKeys]
  have hdisj' : Disjoint (K \ D) B :=
    Finset.disjoint_of_subset_left Finset.sdiff_subset hdisj.symm
  rw [Finset.card_union_of_disjoint hdisj', Finset.card_sdiff,
    Finset.inter_eq_left.mpr hsubD, hK_card, hD_card, hB]
  omega

open Classical in
private theorem val_pairBOf_eq {U V n t₀ m : ℕ} (s : HardKeyValSeed U V n)
    (ht₀ : t₀ + m ≤ n) {B : Finset (Fin U)} (hB : B.card = m)
    (hdisj : Disjoint B (s.activeKeys t₀ (Nat.le_of_add_right_le ht₀))) :
    (pairBOf t₀ m ht₀ (s, B)).val =
      fun u => if u ∈ (s.activeKeys t₀ (Nat.le_of_add_right_le ht₀) \
          Finset.univ.image (segDeletedKeys s.keys s.delPerm t₀ m ht₀)) ∪ B
        then some (s.kv u).val else none := by
  have hK := card_sdiff_deleted_union_eq s ht₀ hB hdisj
  dsimp only [pairBOf]
  rw [dite_eq_left hK]
  rfl

open Classical in
private theorem toReal_innerPoolDist_actSeed8Equiv {U V n t₀ m g P_size : ℕ} [NeZero V]
    (hU : 2 * n ≤ U) (hV : 1 ≤ V) (ht₀ : t₀ + m ≤ n)
    (pool : HardKeyValSeed U V n → Finset (Fin U))
    (hcard_pool : ∀ s, (pool s).card = P_size)
    (hA_pool : ∀ s, s.insertedSet t₀ m ht₀ ⊆ pool s)
    (hpool_act : ∀ (τ : Equiv.Perm (Fin U)) (δ : Fin U → Fin V) s,
      pool (actSeed8Equiv τ δ s) = (pool s).map τ.toEmbedding)
    (Fg : HardKeyValSeed U V n → Finset (Finset (Fin U)))
    (hFg : ∀ s, Fg s = ((pool s).powersetCard m).filter fun B =>
      (s.insertedSet t₀ m ht₀ ∩ B).card = g)
    (hne : ∀ s, (Fg s).Nonempty)
    (τ : Equiv.Perm (Fin U)) (δ : Fin U → Fin V)
    (s : HardKeyValSeed U V n) (B : Finset (Fin U)) :
    (innerPoolDist hU hV Fg hne (actSeed8Equiv τ δ s, B.map τ.toEmbedding)).toReal =
      (innerPoolDist hU hV Fg hne (s, B)).toReal := by
  have hFg_card : ∀ s', (Fg s').card = m.choose g * (P_size - m).choose (m - g) := fun s' => by
    rw [hFg s', card_inter_filter_powersetCard (hA_pool s')
      ((Finset.card_image_of_injective _
        (segInsertedKeys s'.keys t₀ m ht₀).injective).trans (by simp)),
      hcard_pool s']
  have hmem_iff : B.map τ.toEmbedding ∈ Fg (actSeed8Equiv τ δ s) ↔ B ∈ Fg s := by
    rw [hFg, hFg, hpool_act τ δ s, actSeed8Equiv_insertedSet]
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.card_map,
      ← Finset.map_inter, Finset.map_subset_map]
  let _ : Nonempty (HardKeyValSeed U V n) := ⟨s⟩
  rw [toReal_innerPoolDist_apply, toReal_innerPoolDist_apply, hFg_card, hFg_card]
  have hunif_s : ((PMF.uniformOfFintype (HardKeyValSeed U V n)) (actSeed8Equiv τ δ s)) =
      (PMF.uniformOfFintype (HardKeyValSeed U V n)) s := by
    simp [PMF.uniformOfFintype_apply]
  rw [hunif_s]
  by_cases hB : B ∈ Fg s
  · rw [ite_eq_left (hmem_iff.mpr hB), ite_eq_left hB]
  · rw [ite_eq_right (mt hmem_iff.mp hB), ite_eq_right hB]

open Classical in
private theorem prob_gt_cap_stateFiber_le {U V n t₀ m g P_size cells w : ℕ} {γ R : ℝ}
    (hU : 2 * n ≤ U) (hU_pos_nat : 1 ≤ U) (hV : 1 ≤ V) (ht₀ : t₀ + m ≤ n)
    (hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
    (pool : HardKeyValSeed U V n → Finset (Fin U))
    (hcard_pool : ∀ s, (pool s).card = P_size)
    (hA_pool : ∀ s, s.insertedSet t₀ m ht₀ ⊆ pool s)
    (hpool_act : ∀ [NeZero V] (τ : Equiv.Perm (Fin U)) (δ : Fin U → Fin V) s,
      pool (actSeed8Equiv τ δ s) = (pool s).map τ.toEmbedding)
    (Fg : HardKeyValSeed U V n → Finset (Finset (Fin U)))
    (hFg : ∀ s, Fg s = ((pool s).powersetCard m).filter fun B =>
      (s.insertedSet t₀ m ht₀ ∩ B).card = g)
    (hne : ∀ s, (Fg s).Nonempty)
    (D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w) (stepIdx : ℕ) :
    let μ_g := innerPoolDist hU hV Fg hne
    let M_cap := (2 : ℝ) ^ (R + 1) * (U : ℝ) ^ (γ * (m : ℝ))
    (((μ_g.map fun sb => decide (M_cap <
      ((stateFiber D_det stepIdx (pairBOf t₀ m ht₀ sb).val).card : ℝ))) true).toReal) ≤
      (1 / 2) * (U : ℝ) ^ (-γ * (m : ℝ)) := by
  let _ : NeZero V := ⟨by omega⟩
  let _ : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb hU, fun _ => ⟨0, hV⟩, 1⟩⟩
  let _ : DecidableEq (SizedDict U V n) := Classical.decEq _
  let μ_g := innerPoolDist hU hV Fg hne
  let M_cap := (2 : ℝ) ^ (R + 1) * (U : ℝ) ^ (γ * (m : ℝ))
  have hunif_pair : ∀ p₁ p₂ : SizedDict U V n,
      ((μ_g.map (pairBOf t₀ m ht₀)) p₁).toReal = ((μ_g.map (pairBOf t₀ m ht₀)) p₂).toReal := by
    intro p₁ p₂
    let K₁ : Finset (Fin U) := Dictionary.dom p₁.val
    have hK₁ : K₁.card = n := p₁.2.1
    let K₂ : Finset (Fin U) := Dictionary.dom p₂.val
    have hK₂ : K₂.card = n := p₂.2.1
    let f₁ (u : ↥K₁) : Fin V :=
      let his : (p₁.val u.1).isSome := Dictionary.mem_dom_iff_isSome.mp u.2
      ⟨(p₁.val u.1).get his, p₁.2.2 u.1 _ (Option.some_get his).symm⟩
    let f₂ (u : ↥K₂) : Fin V :=
      let his : (p₂.val u.1).isSome := Dictionary.mem_dom_iff_isSome.mp u.2
      ⟨(p₂.val u.1).get his, p₂.2.2 u.1 _ (Option.some_get his).symm⟩
    have hp₁ (u : Fin U) : p₁.val u = if hu : u ∈ K₁ then some (f₁ ⟨u, hu⟩).val else none := by
      by_cases hu : u ∈ K₁
      · rw [dite_eq_left hu]
        exact (Option.some_get (Dictionary.mem_dom_iff_isSome.mp hu)).symm
      · rw [dite_eq_right hu]
        exact Dictionary.notMem_dom_iff.mp hu
    have hp₂ (u : Fin U) : p₂.val u = if hu : u ∈ K₂ then some (f₂ ⟨u, hu⟩).val else none := by
      by_cases hu : u ∈ K₂
      · rw [dite_eq_left hu]
        exact (Option.some_get (Dictionary.mem_dom_iff_isSome.mp hu)).symm
      · rw [dite_eq_right hu]
        exact Dictionary.notMem_dom_iff.mp hu
    obtain ⟨τ, hτ_map⟩ := Equiv.Perm.exists_map_finset_eq K₁ K₂ (hK₁.trans hK₂.symm)
    have hτ_mem : ∀ x : Fin U, x ∈ K₁ ↔ τ x ∈ K₂ := fun x => by
      rw [← hτ_map]; exact (Finset.mem_map' τ.toEmbedding).symm
    have hτ_symm_mem : ∀ y : Fin U, y ∈ K₂ → τ.symm y ∈ K₁ := fun y hy =>
      (hτ_mem (τ.symm y)).mpr (by simpa using hy)
    let δ : Fin U → Fin V := fun u =>
      if hu : u ∈ K₂ then f₂ ⟨u, hu⟩ - f₁ ⟨τ.symm u, hτ_symm_mem u hu⟩ else 0
    let e_sb : (HardKeyValSeed U V n × Finset (Fin U)) ≃
        (HardKeyValSeed U V n × Finset (Fin U)) :=
      (actSeed8Equiv τ δ).prodCongr
        { toFun := fun B => B.map τ.toEmbedding
          invFun := fun B => B.map τ.symm.toEmbedding
          left_inv := fun B => by ext x; simp
          right_inv := fun B => by ext x; simp }
    have hμ_inv (sb : HardKeyValSeed U V n × Finset (Fin U)) :
        (μ_g (e_sb sb)).toReal = (μ_g sb).toReal :=
      toReal_innerPoolDist_actSeed8Equiv hU hV ht₀ pool hcard_pool hA_pool
        (fun τ' δ' s' => hpool_act τ' δ' s') Fg hFg hne τ δ sb.1 sb.2
    have hpair_act (sb : HardKeyValSeed U V n × Finset (Fin U)) :
        pairBOf t₀ m ht₀ (e_sb sb) = p₂ ↔
          pairBOf t₀ m ht₀ sb = p₁ := by
      rcases sb with ⟨s, B⟩
      rw [← Subtype.val_injective.eq_iff, ← Subtype.val_injective.eq_iff]
      let S₀ := (s.activeKeys t₀ (Nat.le_of_add_right_le ht₀) \
        Finset.univ.image (segDeletedKeys s.keys s.delPerm t₀ m ht₀)) ∪ B
      let S_def := if S₀.card = n then S₀ else s.activeKeys t₀ (Nat.le_of_add_right_le ht₀)
      have hst1 (u : Fin U) :
          (pairBOf t₀ m ht₀ (s, B)).val u =
            if u ∈ S_def then some (s.kv u).val else none := by
        by_cases hc : S₀.card = n
        · have hSd : S_def = S₀ := ite_eq_left hc
          simp only [hSd]; dsimp only [pairBOf, S₀]; rw [dite_eq_left hc]; rfl
        · have hSd : S_def = s.activeKeys t₀ (Nat.le_of_add_right_le ht₀) := ite_eq_right hc
          simp only [hSd]; dsimp only [pairBOf, S₀]; rw [dite_eq_right hc]; rfl
      have hst2 (u : Fin U) :
          (pairBOf t₀ m ht₀ (e_sb (s, B))).val u =
            if u ∈ S_def.map τ.toEmbedding then some (s.kv (τ.symm u) + δ u).val else none := by
        change (pairBOf t₀ m ht₀ (actSeed8Equiv τ δ s, B.map τ.toEmbedding)).val u = _
        have hmap_S₀ : (((actSeed8Equiv τ δ s).activeKeys t₀ (Nat.le_of_add_right_le ht₀) \
              Finset.univ.image (segDeletedKeys (actSeed8Equiv τ δ s).keys
                (actSeed8Equiv τ δ s).delPerm t₀ m ht₀)) ∪ B.map τ.toEmbedding) =
            S₀.map τ.toEmbedding := by
          dsimp only [S₀]
          rw [actSeed8Equiv_activeKeys, actSeed8Equiv_deletedSet,
            Finset.map_union, Finset.map_sdiff]
        by_cases hc : S₀.card = n
        · have hSd : S_def = S₀ := ite_eq_left hc
          simp only [hSd]
          have hc' : (((actSeed8Equiv τ δ s).activeKeys t₀ (Nat.le_of_add_right_le ht₀) \
              Finset.univ.image (segDeletedKeys (actSeed8Equiv τ δ s).keys
                (actSeed8Equiv τ δ s).delPerm t₀ m ht₀)) ∪ B.map τ.toEmbedding).card = n := by
            rw [hmap_S₀, Finset.card_map]; exact hc
          dsimp only [pairBOf]; rw [dite_eq_left hc']
          dsimp only [sizedDictOfFinset]
          by_cases hu : u ∈ (((actSeed8Equiv τ δ s).activeKeys t₀ (Nat.le_of_add_right_le ht₀) \
              Finset.univ.image (segDeletedKeys (actSeed8Equiv τ δ s).keys
                (actSeed8Equiv τ δ s).delPerm t₀ m ht₀)) ∪ B.map τ.toEmbedding)
          · have hu' : u ∈ S₀.map τ.toEmbedding := hmap_S₀ ▸ hu
            rw [ite_eq_left hu, ite_eq_left hu']; rfl
          · have hu' : u ∉ S₀.map τ.toEmbedding := hmap_S₀ ▸ hu
            rw [ite_eq_right hu, ite_eq_right hu']
        · have hSd : S_def = s.activeKeys t₀ (Nat.le_of_add_right_le ht₀) := ite_eq_right hc
          simp only [hSd]
          have hc' : (((actSeed8Equiv τ δ s).activeKeys t₀ (Nat.le_of_add_right_le ht₀) \
              Finset.univ.image (segDeletedKeys (actSeed8Equiv τ δ s).keys
                (actSeed8Equiv τ δ s).delPerm t₀ m ht₀)) ∪ B.map τ.toEmbedding).card ≠ n := by
            rw [hmap_S₀, Finset.card_map]; exact hc
          dsimp only [pairBOf]; rw [dite_eq_right hc']
          dsimp only [sizedDictOfFinset]
          by_cases hu : u ∈ (actSeed8Equiv τ δ s).activeKeys t₀ (Nat.le_of_add_right_le ht₀)
          · have hu' : u ∈ (s.activeKeys t₀ (Nat.le_of_add_right_le ht₀)).map τ.toEmbedding :=
              actSeed8Equiv_activeKeys τ δ s _ _ ▸ hu
            rw [ite_eq_left hu, ite_eq_left hu']; rfl
          · have hu' : u ∉ (s.activeKeys t₀ (Nat.le_of_add_right_le ht₀)).map τ.toEmbedding :=
              actSeed8Equiv_activeKeys τ δ s _ _ ▸ hu
            rw [ite_eq_right hu, ite_eq_right hu']
      rw [funext_iff, funext_iff]
      simp_rw [hst1, hst2, hp₁, hp₂]
      constructor
      · intro h2 x
        have hy := h2 (τ x)
        have hmem_map : τ x ∈ S_def.map τ.toEmbedding ↔ x ∈ S_def := by simp
        simp only [hmem_map, Equiv.symm_apply_apply] at hy
        by_cases hxS : x ∈ S_def
        · rw [ite_eq_left hxS] at hy ⊢
          by_cases hxK : x ∈ K₁
          · have hτK : τ x ∈ K₂ := (hτ_mem x).mp hxK
            rw [dite_eq_left hτK] at hy
            rw [dite_eq_left hxK]
            have hval : s.kv x + δ (τ x) = f₂ ⟨τ x, hτK⟩ := Fin.ext (Option.some.inj hy)
            dsimp only [δ] at hval
            rw [dite_eq_left hτK] at hval
            have hsub : f₁ ⟨τ.symm (τ x), hτ_symm_mem (τ x) hτK⟩ = f₁ ⟨x, hxK⟩ := by
              congr 1; exact Subtype.ext (τ.symm_apply_apply x)
            rw [hsub] at hval
            have hf1 : s.kv x = f₁ ⟨x, hxK⟩ := by
              calc s.kv x = (s.kv x + (f₂ ⟨τ x, hτK⟩ - f₁ ⟨x, hxK⟩)) -
                    (f₂ ⟨τ x, hτK⟩ - f₁ ⟨x, hxK⟩) := (add_sub_cancel_right _ _).symm
                _ = f₂ ⟨τ x, hτK⟩ - (f₂ ⟨τ x, hτK⟩ - f₁ ⟨x, hxK⟩) := by rw [hval]
                _ = f₁ ⟨x, hxK⟩ := sub_sub_cancel _ _
            exact congrArg (fun v : Fin V => some v.val) hf1
          · have hτK : τ x ∉ K₂ := mt (hτ_mem x).mpr hxK
            rw [dite_eq_right hτK] at hy; simp at hy
        · rw [ite_eq_right hxS] at hy ⊢
          by_cases hxK : x ∈ K₁
          · have hτK : τ x ∈ K₂ := (hτ_mem x).mp hxK
            rw [dite_eq_left hτK] at hy; simp at hy
          · rw [dite_eq_right hxK]
      · intro h1 y
        have hx := h1 (τ.symm y)
        have hmem_map : y ∈ S_def.map τ.toEmbedding ↔ τ.symm y ∈ S_def := by
          simp only [Finset.mem_map, Equiv.coe_toEmbedding]
          exact ⟨fun ⟨z, hz, hzy⟩ => by rwa [← hzy, τ.symm_apply_apply],
            fun h => ⟨τ.symm y, h, τ.apply_symm_apply y⟩⟩
        simp only [hmem_map]
        by_cases hxS : τ.symm y ∈ S_def
        · rw [ite_eq_left hxS] at hx ⊢
          by_cases hyK : y ∈ K₂
          · have hxK : τ.symm y ∈ K₁ := hτ_symm_mem y hyK
            rw [dite_eq_left hxK] at hx
            rw [dite_eq_left hyK]
            have hf1 : s.kv (τ.symm y) = f₁ ⟨τ.symm y, hxK⟩ := Fin.ext (Option.some.inj hx)
            dsimp only [δ]
            rw [dite_eq_left hyK, hf1, add_sub_cancel]
          · have hxK : τ.symm y ∉ K₁ := fun h => hyK (by simpa using (hτ_mem (τ.symm y)).mp h)
            rw [dite_eq_right hxK] at hx; simp at hx
        · rw [ite_eq_right hxS] at hx ⊢
          by_cases hyK : y ∈ K₂
          · have hxK : τ.symm y ∈ K₁ := hτ_symm_mem y hyK
            rw [dite_eq_left hxK] at hx; simp at hx
          · rw [dite_eq_right hyK]
    rw [PMF.map_apply_toReal, PMF.map_apply_toReal]
    conv_rhs => rw [← e_sb.sum_comp]
    refine Finset.sum_congr rfl fun sb _ => ?_
    by_cases h1 : p₁ = pairBOf t₀ m ht₀ sb
    · have h2 : p₂ = pairBOf t₀ m ht₀ (e_sb sb) :=
        ((hpair_act sb).mpr h1.symm).symm
      rw [ite_eq_left h1, ite_eq_left h2, hμ_inv sb]
    · have h2 : p₂ ≠ pairBOf t₀ m ht₀ (e_sb sb) :=
        fun h => h1 ((hpair_act sb).mp h.symm).symm
      rw [ite_eq_right h1, ite_eq_right h2]
  let N_tot := Fintype.card (SizedDict U V n)
  have hN_eq : N_tot = U.choose n * V ^ n := card_sizedDict U V n
  have hN_pos : (0 : ℝ) < (N_tot : ℝ) := by
    rw [hN_eq]; exact_mod_cast Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.pow_pos hV)
  have hpair_prob (p : SizedDict U V n) :
      ((μ_g.map (pairBOf t₀ m ht₀)) p).toReal = (N_tot : ℝ)⁻¹ := by
    have hsum := PMF.sum_toReal (μ_g.map (pairBOf t₀ m ht₀))
    have hconst : (∑ q : SizedDict U V n, ((μ_g.map (pairBOf t₀ m ht₀)) q).toReal) =
        (N_tot : ℝ) * ((μ_g.map (pairBOf t₀ m ht₀)) p).toReal := by
      rw [Finset.sum_congr rfl fun q _ => hunif_pair q p, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    rw [hconst] at hsum
    exact eq_inv_of_mul_eq_one_right hsum
  have hexp_fiber : (∑ sb : HardKeyValSeed U V n × Finset (Fin U),
      (μ_g sb).toReal *
        ((stateFiber D_det stepIdx (pairBOf t₀ m ht₀ sb).val).card : ℝ)) ≤
      (2 : ℝ) ^ R := by
    have hpush : (∑ sb, (μ_g sb).toReal *
          ((stateFiber D_det stepIdx (pairBOf t₀ m ht₀ sb).val).card : ℝ)) =
        ∑ p : SizedDict U V n, ((μ_g.map (pairBOf t₀ m ht₀)) p).toReal *
          ((stateFiber D_det stepIdx p.val).card : ℝ) := by
      simp_rw [PMF.map_apply_toReal, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun sb _ => ?_
      have h1 (p : SizedDict U V n) :
          (if p = pairBOf t₀ m ht₀ sb then (μ_g sb).toReal else 0) *
            ((stateFiber D_det stepIdx p.val).card : ℝ) =
          if p = pairBOf t₀ m ht₀ sb then
            (μ_g sb).toReal * ((stateFiber D_det stepIdx p.val).card : ℝ)
          else 0 := by
        split_ifs <;> ring
      simp_rw [h1]
      rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _)]
    rw [hpush]
    simp_rw [hpair_prob, ← Finset.mul_sum]
    have hsum_le : (∑ p : SizedDict U V n,
        ((stateFiber D_det stepIdx p.val).card : ℝ)) ≤ (2 : ℝ) ^ (cells * w) := by
      exact_mod_cast sum_card_stateFiber_le D_det stepIdx
    have h2cw : (2 : ℝ) ^ (cells * w) ≤ (N_tot : ℝ) * (2 : ℝ) ^ R := by
      have hc_ne : ((U.choose n : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos (by omega)).ne'
      have hv_ne : ((V : ℝ) ^ n) ≠ 0 := by positivity
      have hlogN : Real.logb 2 (N_tot : ℝ) = benchmarkBits U V n := by
        rw [hN_eq, Nat.cast_mul, Nat.cast_pow, Real.logb_mul hc_ne hv_ne,
          Real.logb_pow, benchmarkBits_eq]
      have hrpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hspace
      rw [Real.rpow_natCast] at hrpow
      rw [← hlogN, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hN_pos] at hrpow
      exact hrpow
    calc (N_tot : ℝ)⁻¹ * ∑ p : SizedDict U V n, ((stateFiber D_det stepIdx p.val).card : ℝ)
        ≤ (N_tot : ℝ)⁻¹ * (2 : ℝ) ^ (cells * w) :=
          mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr hN_pos.le)
      _ ≤ (N_tot : ℝ)⁻¹ * ((N_tot : ℝ) * (2 : ℝ) ^ R) :=
          mul_le_mul_of_nonneg_left h2cw (inv_nonneg.mpr hN_pos.le)
      _ = (2 : ℝ) ^ R := inv_mul_cancel_left₀ hN_pos.ne' _
  have hU_pos : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hU_pos_nat
  have hM_pos : 0 < M_cap := mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.rpow_pos_of_pos hU_pos _)
  have hmarkov : (((μ_g.map fun sb => decide (M_cap <
      ((stateFiber D_det stepIdx (pairBOf t₀ m ht₀ sb).val).card : ℝ))) true).toReal) *
        M_cap ≤
      ∑ sb, (μ_g sb).toReal *
        ((stateFiber D_det stepIdx (pairBOf t₀ m ht₀ sb).val).card : ℝ) := by
    rw [PMF.map_apply_toReal, Finset.sum_mul]
    refine Finset.sum_le_sum fun sb _ => ?_
    by_cases hgt : M_cap < ((stateFiber D_det stepIdx (pairBOf t₀ m ht₀ sb).val).card : ℝ)
    · simp only [hgt, decide_true, ↓reduceIte]
      exact mul_le_mul_of_nonneg_left hgt.le ENNReal.toReal_nonneg
    · simp only [hgt, decide_false, Bool.true_eq_false, ↓reduceIte, zero_mul]
      exact mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)
  have hdiv : (2 : ℝ) ^ R / M_cap = (1 / 2) * (U : ℝ) ^ (-γ * (m : ℝ)) := by
    dsimp only [M_cap]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
      show -γ * (m : ℝ) = -(γ * (m : ℝ)) by ring, Real.rpow_neg hU_pos.le]
    field_simp
  rw [← hdiv, le_div_iff₀ hM_pos]
  exact hmarkov.trans hexp_fiber

/-! #### Section 8 observation/target fiber bound and 6-piece prefix-free message -/

private def obs8 {U V n : ℕ} (t₀ m : ℕ) (ht₀ : t₀ + m ≤ n)
    (sb : HardKeyValSeed U V n × Finset (Fin U)) :
    (Fin m → Fin U) × Finset (Fin U) × (Fin m → Fin U) :=
  (fun r => segInsertedKeys sb.1.keys t₀ m ht₀ r,
   sb.2,
   fun r => segDeletedKeys sb.1.keys sb.1.delPerm t₀ m ht₀ r)

private def obsFixedSet {U m : ℕ}
    (o : (Fin m → Fin U) × Finset (Fin U) × (Fin m → Fin U)) : Finset (Fin U) :=
  Finset.univ.image o.1 ∪ o.2.1 ∪ Finset.univ.image o.2.2

private def target8 {U V n : ℕ} (t₀ m : ℕ) (ht₀ : t₀ + m ≤ n)
    (sb : HardKeyValSeed U V n × Finset (Fin U)) :
    Finset (Fin U) × (Fin U → Option (Fin V)) :=
  (sb.1.activeKeys t₀ (Nat.le_of_add_right_le ht₀) \
      Finset.univ.image (segDeletedKeys sb.1.keys sb.1.delPerm t₀ m ht₀),
   fun u => if u ∈ sb.1.activeKeys t₀ (Nat.le_of_add_right_le ht₀) ∪
       sb.1.insertedSet t₀ m ht₀ ∪ sb.2 then some (sb.1.kv u) else none)

open Classical in
private theorem fiber_le_queryFreePoolDist {U V n t₀ m g P_size : ℕ}
    (hU : 3 * n ≤ U) (hV : 1 ≤ V) (hm_n : 2 * m ≤ n) (hg : g < m / 2) (ht₀ : t₀ + m ≤ n)
    (pool : HardKeyValSeed U V n → Finset (Fin U))
    (hcard_pool : ∀ s, (pool s).card = P_size)
    (hA_pool : ∀ s, s.insertedSet t₀ m ht₀ ⊆ pool s)
    (hdisj_pool : ∀ s, Disjoint (pool s) (s.activeKeys t₀ (Nat.le_of_add_right_le ht₀)))
    (hpool_act : ∀ [NeZero V] (τ : Equiv.Perm (Fin U)) (δ : Fin U → Fin V) s,
      pool (actSeed8Equiv τ δ s) = (pool s).map τ.toEmbedding)
    (Fg : HardKeyValSeed U V n → Finset (Finset (Fin U)))
    (hFg : ∀ s, Fg s = ((pool s).powersetCard m).filter fun B =>
      (s.insertedSet t₀ m ht₀ ∩ B).card = g)
    (hne : ∀ s, (Fg s).Nonempty)
    (o : (Fin m → Fin U) × Finset (Fin U) × (Fin m → Fin U))
    (T : Finset (Fin U) × (Fin U → Option (Fin V))) :
    let μ_g := innerPoolDist (by omega) hV Fg hne
    let M_nat := (U - 3 * m).choose (n - m) * V ^ (n + 2 * m - g)
    ((μ_g.map fun sb => (obs8 t₀ m ht₀ sb, target8 t₀ m ht₀ sb)) (o, T)).toReal ≤
      ((μ_g.map (obs8 t₀ m ht₀)) o).toReal / (M_nat : ℝ) := by
  dsimp only
  let _ : NeZero V := ⟨by omega⟩
  let _ : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb (by omega), fun _ => ⟨0, hV⟩, 1⟩⟩
  let μ_g := innerPoolDist (by omega : 2 * n ≤ U) hV Fg hne
  let M_nat := (U - 3 * m).choose (n - m) * V ^ (n + 2 * m - g)
  have hM_pos : (0 : ℝ) < (M_nat : ℝ) := by
    dsimp only [M_nat]
    exact_mod_cast Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.pow_pos hV)
  rw [le_div_iff₀ hM_pos]
  by_cases ho_card : o.2.1.card = m
  · let S_comp := Finset.univ \ obsFixedSet o
    let G := Equiv.Perm ↥S_comp × (Fin U → Fin V)
    let actG (γ : G) :
        (HardKeyValSeed U V n × Finset (Fin U)) ≃ (HardKeyValSeed U V n × Finset (Fin U)) :=
      (actSeed8Equiv (Equiv.Perm.ofSubtype γ.1) γ.2).prodCongr (Equiv.refl _)
    have hfix (π_sub : Equiv.Perm ↥S_comp) {x : Fin U} (hx : x ∈ obsFixedSet o) :
        Equiv.Perm.ofSubtype π_sub x = x :=
      Equiv.Perm.ofSubtype_apply_of_not_mem π_sub (by simp [S_comp, hx])
    have hobs_fwd (γ : G) (sb : HardKeyValSeed U V n × Finset (Fin U))
        (ho : obs8 t₀ m ht₀ sb = o) : obs8 t₀ m ht₀ (actG γ sb) = o := by
      rcases sb with ⟨s, B⟩
      rcases o with ⟨a_fn, B_set, d_fn⟩
      dsimp only [obs8] at ho
      rcases Prod.mk.inj ho with ⟨ha, hBd⟩
      rcases Prod.mk.inj hBd with ⟨hB, hd⟩
      subst hB
      change obs8 t₀ m ht₀ (actSeed8Equiv (Equiv.Perm.ofSubtype γ.1) γ.2 s, B) =
        (a_fn, B, d_fn)
      dsimp only [obs8]
      refine Prod.ext (funext fun r => ?_) (Prod.ext rfl (funext fun r => ?_))
      · dsimp only
        have hr_mem : segInsertedKeys s.keys t₀ m ht₀ r ∈ obsFixedSet (a_fn, B, d_fn) := by
          dsimp only [obsFixedSet]
          exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨r, Finset.mem_univ r, congrFun ha.symm r⟩))
        have h1 : segInsertedKeys (actSeed8Equiv (Equiv.Perm.ofSubtype γ.1) γ.2 s).keys
            t₀ m ht₀ r = Equiv.Perm.ofSubtype γ.1 (segInsertedKeys s.keys t₀ m ht₀ r) := by
          simp [segInsertedKeys_apply, actSeed8Equiv]
        rw [h1, hfix γ.1 hr_mem, ← ha]
      · dsimp only
        have hr_mem : segDeletedKeys s.keys s.delPerm t₀ m ht₀ r ∈
            obsFixedSet (a_fn, B, d_fn) := by
          dsimp only [obsFixedSet]
          exact Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨r, Finset.mem_univ r, congrFun hd.symm r⟩)
        have h1 : segDeletedKeys (actSeed8Equiv (Equiv.Perm.ofSubtype γ.1) γ.2 s).keys
            (actSeed8Equiv (Equiv.Perm.ofSubtype γ.1) γ.2 s).delPerm t₀ m ht₀ r =
            Equiv.Perm.ofSubtype γ.1 (segDeletedKeys s.keys s.delPerm t₀ m ht₀ r) := by
          simp [segDeletedKeys_apply, actSeed8Equiv]
        rw [h1, hfix γ.1 hr_mem, ← hd]
    have hobs_iff (γ : G) (sb : HardKeyValSeed U V n × Finset (Fin U)) :
        obs8 t₀ m ht₀ (actG γ sb) = o ↔ obs8 t₀ m ht₀ sb = o := by
      refine ⟨fun h => ?_, hobs_fwd γ sb⟩
      let γ_inv : G := (γ.1.symm, fun u => -γ.2 (Equiv.Perm.ofSubtype γ.1 u))
      have hsymm : actG γ_inv (actG γ sb) = sb := by
        rcases sb with ⟨s, B⟩
        have hperm : (Equiv.Perm.ofSubtype γ.1.symm : Equiv.Perm (Fin U)) =
            (Equiv.Perm.ofSubtype γ.1).symm :=
          Equiv.ext fun u => (Equiv.Perm.ofSubtype γ.1).injective (by
            rw [Equiv.apply_symm_apply]
            by_cases hu : u ∈ S_comp
            · rw [Equiv.Perm.ofSubtype_apply_of_mem _ hu,
                Equiv.Perm.ofSubtype_apply_of_mem _ (γ.1.symm ⟨u, hu⟩).2]
              simp
            · rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hu,
                Equiv.Perm.ofSubtype_apply_of_not_mem _ hu])
        change (actSeed8Equiv (Equiv.Perm.ofSubtype γ.1.symm) γ_inv.2
          (actSeed8Equiv (Equiv.Perm.ofSubtype γ.1) γ.2 s), B) = (s, B)
        rw [hperm]
        refine Prod.ext ?_ rfl
        cases s
        simp only [actSeed8Equiv, Equiv.coe_fn_mk, HardKeyValSeed.mk.injEq, and_true]
        exact ⟨by ext i; simp, by funext u; simp [γ_inv]⟩
      simpa only [hsymm] using hobs_fwd γ_inv (actG γ sb) h
    have hμ_obs (γ : G) (sb : HardKeyValSeed U V n × Finset (Fin U))
        (ho : obs8 t₀ m ht₀ sb = o) : (μ_g (actG γ sb)).toReal = (μ_g sb).toReal := by
      rcases sb with ⟨s, B⟩
      have hBo : B = o.2.1 := (Prod.mk.inj (Prod.mk.inj ho).2).1
      let τ := Equiv.Perm.ofSubtype γ.1
      have hB_map : B.map τ.toEmbedding = B := by
        ext x; simp only [Finset.mem_map, Equiv.coe_toEmbedding]
        refine ⟨fun ⟨y, hy, hyx⟩ => ?_, fun hx => ⟨x, hx, ?_⟩⟩
        · have hy_fix : τ y = y := hfix γ.1 (Finset.mem_union_left _
            (Finset.mem_union_right _ (hBo ▸ hy)))
          rwa [← hyx, hy_fix]
        · exact hfix γ.1 (Finset.mem_union_left _ (Finset.mem_union_right _ (hBo ▸ hx)))
      change (μ_g (actSeed8Equiv τ γ.2 s, B)).toReal = (μ_g (s, B)).toReal
      conv_lhs => rw [← hB_map]
      exact toReal_innerPoolDist_actSeed8Equiv (by omega : 2 * n ≤ U) hV ht₀ pool
        hcard_pool hA_pool (fun τ' δ' s' => hpool_act τ' δ' s') Fg hFg hne τ γ.2 s B
    -- Orbit bound for any supported sb with obs8 sb = o
    have horbit_le (sb : HardKeyValSeed U V n × Finset (Fin U))
        (ho : obs8 t₀ m ht₀ sb = o) (hB_Fg : sb.2 ∈ Fg sb.1) :
        ((Finset.univ.filter fun γ : G => target8 t₀ m ht₀ (actG γ sb) = T).card : ℝ) *
          (M_nat : ℝ) ≤ (Fintype.card G : ℝ) := by
      rcases sb with ⟨s, B⟩
      rcases T with ⟨K_rem, kv_opt⟩
      dsimp only at hB_Fg
      have hB_fg_props := Finset.mem_filter.mp (hFg s ▸ hB_Fg)
      have hB_pool : B ⊆ pool s := (Finset.mem_powersetCard.mp hB_fg_props.1).1
      have hB_card : B.card = m := (Finset.mem_powersetCard.mp hB_fg_props.1).2
      have hAB_card : (s.insertedSet t₀ m ht₀ ∩ B).card = g := hB_fg_props.2
      let ht₀_n : t₀ ≤ n := Nat.le_of_add_right_le ht₀
      let K₀ := s.activeKeys t₀ ht₀_n \ Finset.univ.image (segDeletedKeys s.keys s.delPerm t₀ m ht₀)
      have hK₀_card : K₀.card = n - m := by
        have hsubD : Finset.univ.image (segDeletedKeys s.keys s.delPerm t₀ m ht₀) ⊆
            s.activeKeys t₀ ht₀_n := by
          intro u hu; obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hu
          dsimp only [HardKeyValSeed.activeKeys]
          refine Finset.mem_map.mpr ⟨⟨r.val, by omega⟩, Finset.mem_univ _, ?_⟩
          rw [windowEmb_apply]
          simp only [segDeletedKeys_apply, HardKeyValSeed.permKeyEmb,
            Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
          rw [liftDelPerm_apply_lt s.delPerm (by have := r.isLt; omega)]
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsubD,
          Finset.card_image_of_injective _ (segDeletedKeys s.keys s.delPerm t₀ m ht₀).injective]
        simp [HardKeyValSeed.activeKeys]
      have hK₀_sub : K₀ ⊆ S_comp := by
        intro u hu
        obtain ⟨huK, huD⟩ := Finset.mem_sdiff.mp hu
        rw [Finset.mem_sdiff]
        refine ⟨Finset.mem_univ u, fun hu_fix => ?_⟩
        dsimp only [obsFixedSet] at hu_fix
        rcases Finset.mem_union.mp hu_fix with huAB | huD'
        · rcases Finset.mem_union.mp huAB with huA | huB
          · have ha_eq : o.1 = fun r => segInsertedKeys s.keys t₀ m ht₀ r :=
              (Prod.mk.inj ho).1.symm
            rw [ha_eq] at huA
            have hu_ins : u ∈ s.insertedSet t₀ m ht₀ := huA
            exact Finset.disjoint_left.mp (hdisj_pool s) (hA_pool s hu_ins) huK
          · have hBo : o.2.1 = B := (Prod.mk.inj (Prod.mk.inj ho).2).1.symm
            rw [hBo] at huB
            exact Finset.disjoint_left.mp (hdisj_pool s) (hB_pool huB) huK
        · have hd_eq : o.2.2 = fun r => segDeletedKeys s.keys s.delPerm t₀ m ht₀ r :=
              (Prod.mk.inj (Prod.mk.inj ho).2).2.symm
          rw [hd_eq] at huD'
          exact huD huD'
      -- Bound S_comp.card ≥ U - 3 * m
      have hS_comp_ge : U - 3 * m ≤ S_comp.card := by
        have ho_le : (obsFixedSet o).card ≤ 3 * m := by
          calc (obsFixedSet o).card
              ≤ (Finset.univ.image o.1 ∪ o.2.1).card + (Finset.univ.image o.2.2).card :=
                Finset.card_union_le _ _
            _ ≤ (Finset.univ.image o.1).card + o.2.1.card + (Finset.univ.image o.2.2).card :=
                Nat.add_le_add_right (Finset.card_union_le _ _) _
            _ ≤ m + m + m := by
                have h1 : (Finset.univ.image o.1).card ≤ m :=
                  Finset.card_image_le.trans (by simp)
                have h3 : (Finset.univ.image o.2.2).card ≤ m :=
                  Finset.card_image_le.trans (by simp)
                omega
            _ = 3 * m := by ring
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _),
          Finset.card_univ, Fintype.card_fin]
        omega
      -- Perm-stabilizer bound: stab(K_rem).card * C(U - 3m, n - m) ≤ card (Perm S_comp)
      let stab (K' : Finset (Fin U)) := Finset.univ.filter fun π_sub : Equiv.Perm ↥S_comp =>
        K₀.map (Equiv.Perm.ofSubtype π_sub).toEmbedding = K'
      have hstab_le : (stab K_rem).card * (U - 3 * m).choose (n - m) ≤
          Fintype.card (Equiv.Perm ↥S_comp) := by
        by_cases hKr : K_rem ∈ S_comp.powersetCard (n - m)
        · have hstab_eq (K' : Finset (Fin U)) (hK' : K' ∈ S_comp.powersetCard (n - m)) :
              (stab K_rem).card = (stab K').card := by
            obtain ⟨hKr_sub, hKr_card⟩ := Finset.mem_powersetCard.mp hKr
            obtain ⟨hK'_sub, hK'_card⟩ := Finset.mem_powersetCard.mp hK'
            let Kr_s : Finset ↥S_comp := Finset.univ.filter fun x => x.1 ∈ K_rem
            let K'_s : Finset ↥S_comp := Finset.univ.filter fun x => x.1 ∈ K'
            have hcard_Krs : Kr_s.card = n - m := by
              rw [← hKr_card]
              refine Finset.card_bij (fun x _ => x.1) (fun x hx => (Finset.mem_filter.mp hx).2)
                (fun _ _ _ _ h => Subtype.ext h) fun y hy =>
                  ⟨⟨y, hKr_sub hy⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩, rfl⟩
            have hcard_K's : K'_s.card = n - m := by
              rw [← hK'_card]
              refine Finset.card_bij (fun x _ => x.1) (fun x hx => (Finset.mem_filter.mp hx).2)
                (fun _ _ _ _ h => Subtype.ext h) fun y hy =>
                  ⟨⟨y, hK'_sub hy⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩, rfl⟩
            obtain ⟨σ_sub, hσ_sub_map⟩ :=
              Equiv.Perm.exists_map_finset_eq Kr_s K'_s (hcard_Krs.trans hcard_K's.symm)
            have hσ_map : K_rem.map (Equiv.Perm.ofSubtype σ_sub).toEmbedding = K' := by
              ext y; simp only [Finset.mem_map, Equiv.coe_toEmbedding]
              constructor
              · rintro ⟨x, hx, rfl⟩
                have hxS : x ∈ S_comp := hKr_sub hx
                have hxKr : (⟨x, hxS⟩ : ↥S_comp) ∈ Kr_s :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
                rw [Equiv.Perm.ofSubtype_apply_of_mem σ_sub hxS]
                have hmem : σ_sub ⟨x, hxS⟩ ∈ K'_s := by
                  rw [← hσ_sub_map]
                  exact Finset.mem_map.mpr ⟨⟨x, hxS⟩, hxKr, rfl⟩
                exact (Finset.mem_filter.mp hmem).2
              · intro hy
                have hyS : y ∈ S_comp := hK'_sub hy
                have hyK' : (⟨y, hyS⟩ : ↥S_comp) ∈ K'_s :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
                rw [← hσ_sub_map] at hyK'
                obtain ⟨x_sub, hxKr, hx_eq⟩ := Finset.mem_map.mp hyK'
                refine ⟨x_sub.1, (Finset.mem_filter.mp hxKr).2, ?_⟩
                rw [Equiv.Perm.ofSubtype_apply_of_mem σ_sub x_sub.2]
                exact congrArg Subtype.val hx_eq
            refine Finset.card_bij (fun π_sub _ => π_sub.trans σ_sub) (fun π_sub hπ => ?_)
              (fun _ _ _ _ h => Equiv.Perm.ext fun x => σ_sub.injective (Equiv.Perm.ext_iff.mp h x))
              (fun π' hπ' => ⟨π'.trans σ_sub.symm, ?_, by ext x; simp⟩)
            · rw [Finset.mem_filter] at hπ ⊢
              refine ⟨Finset.mem_univ _, ?_⟩
              have hcomp : (Equiv.Perm.ofSubtype (π_sub.trans σ_sub)).toEmbedding =
                  (Equiv.Perm.ofSubtype π_sub).toEmbedding.trans
                    (Equiv.Perm.ofSubtype σ_sub).toEmbedding := by
                ext z
                by_cases hz : z ∈ S_comp
                · simp [Equiv.Perm.ofSubtype_apply_of_mem, hz, (π_sub ⟨z, hz⟩).2]
                · simp [Equiv.Perm.ofSubtype_apply_of_not_mem, hz]
              rw [hcomp, ← Finset.map_map, hπ.2, hσ_map]
            · rw [Finset.mem_filter] at hπ' ⊢
              refine ⟨Finset.mem_univ _, ?_⟩
              have hcomp : (Equiv.Perm.ofSubtype (π'.trans σ_sub.symm)).toEmbedding.trans
                  (Equiv.Perm.ofSubtype σ_sub).toEmbedding =
                  (Equiv.Perm.ofSubtype π').toEmbedding := by
                ext z
                by_cases hz : z ∈ S_comp
                · simp [Equiv.Perm.ofSubtype_apply_of_mem, hz]
                · simp [Equiv.Perm.ofSubtype_apply_of_not_mem, hz]
              apply Finset.map_injective (Equiv.Perm.ofSubtype σ_sub).toEmbedding
              rw [Finset.map_map, hcomp, hπ'.2, hσ_map]
          have hdisj : ((S_comp.powersetCard (n - m) : Set (Finset (Fin U)))).PairwiseDisjoint
              stab := fun K₁ _ K₂ _ hne =>
            Finset.disjoint_left.mpr fun π_sub h₁ h₂ =>
              hne ((Finset.mem_filter.mp h₁).2.symm.trans (Finset.mem_filter.mp h₂).2)
          have hsum_le : (∑ K' ∈ S_comp.powersetCard (n - m), (stab K').card) ≤
              Fintype.card (Equiv.Perm ↥S_comp) := by
            rw [← Finset.card_biUnion hdisj]
            exact Finset.card_le_univ _
          have hsum_eq : (∑ K' ∈ S_comp.powersetCard (n - m), (stab K').card) =
              (S_comp.powersetCard (n - m)).card * (stab K_rem).card := by
            rw [Finset.sum_congr rfl fun K' hK' => (hstab_eq K' hK').symm,
              Finset.sum_const, smul_eq_mul]
          have hchoose_le : (U - 3 * m).choose (n - m) ≤ (S_comp.powersetCard (n - m)).card := by
            rw [Finset.card_powersetCard]
            exact Nat.choose_le_choose (n - m) hS_comp_ge
          calc (stab K_rem).card * (U - 3 * m).choose (n - m)
              ≤ (stab K_rem).card * (S_comp.powersetCard (n - m)).card :=
                Nat.mul_le_mul_left _ hchoose_le
            _ = (S_comp.powersetCard (n - m)).card * (stab K_rem).card := mul_comm _ _
            _ ≤ Fintype.card (Equiv.Perm ↥S_comp) := hsum_eq ▸ hsum_le
        · have hemp : stab K_rem = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro π_sub hπ
            apply hKr
            rw [← (Finset.mem_filter.mp hπ).2, Finset.mem_powersetCard, Finset.card_map]
            refine ⟨fun y hy => ?_, hK₀_card⟩
            rcases Finset.mem_map.mp hy with ⟨x, hx, rfl⟩
            have hxS : x ∈ S_comp := hK₀_sub hx
            change Equiv.Perm.ofSubtype π_sub x ∈ S_comp
            rw [Equiv.Perm.ofSubtype_apply_of_mem π_sub hxS]
            exact (π_sub ⟨x, hxS⟩).2
          rw [hemp, Finset.card_empty, zero_mul]
          exact Nat.zero_le _
      -- Value-shift bound for each fixed π_sub
      have hval_le (π_sub : Equiv.Perm ↥S_comp) :
          ((Finset.univ.filter fun δ : Fin U → Fin V =>
              (target8 t₀ m ht₀ (actG (π_sub, δ) (s, B))).2 = kv_opt).card) *
            V ^ (n + 2 * m - g) ≤ Fintype.card (Fin U → Fin V) := by
        let τ := Equiv.Perm.ofSubtype π_sub
        let U_cov := (s.activeKeys t₀ ht₀_n).map τ.toEmbedding ∪
          (s.insertedSet t₀ m ht₀).map τ.toEmbedding ∪ B
        have hB_map : B.map τ.toEmbedding = B := by
          have hBo : B = o.2.1 := (Prod.mk.inj (Prod.mk.inj ho).2).1
          ext x; simp only [Finset.mem_map, Equiv.coe_toEmbedding]
          refine ⟨fun ⟨y, hy, hyx⟩ => ?_, fun hx => ⟨x, hx, ?_⟩⟩
          · have hy_fix : τ y = y := hfix π_sub (Finset.mem_union_left _
              (Finset.mem_union_right _ (hBo ▸ hy)))
            rwa [← hyx, hy_fix]
          · exact hfix π_sub (Finset.mem_union_left _ (Finset.mem_union_right _ (hBo ▸ hx)))
        have hU_cov_card : U_cov.card = n + 2 * m - g := by
          have hmap_all : U_cov =
              (s.activeKeys t₀ ht₀_n ∪ (s.insertedSet t₀ m ht₀ ∪ B)).map τ.toEmbedding := by
            dsimp only [U_cov]
            rw [Finset.union_assoc, Finset.map_union, Finset.map_union, hB_map]
          have hAB_u : (s.insertedSet t₀ m ht₀ ∪ B).card = 2 * m - g := by
            have hu := Finset.card_union_add_card_inter (s.insertedSet t₀ m ht₀) B
            have hA_c : (s.insertedSet t₀ m ht₀).card = m :=
              (Finset.card_image_of_injective _
                (segInsertedKeys s.keys t₀ m ht₀).injective).trans (by simp)
            rw [hA_c, hB_card, hAB_card] at hu
            omega
          have hdisj_KAB : Disjoint (s.activeKeys t₀ ht₀_n)
              (s.insertedSet t₀ m ht₀ ∪ B) :=
            Finset.disjoint_union_right.mpr
              ⟨((hdisj_pool s).mono_left (hA_pool s)).symm,
               ((hdisj_pool s).mono_left hB_pool).symm⟩
          rw [hmap_all, Finset.card_map, Finset.card_union_of_disjoint hdisj_KAB, hAB_u]
          have hK_c : (s.activeKeys t₀ ht₀_n).card = n := by simp [HardKeyValSeed.activeKeys]
          rw [hK_c]; omega
        let F_δ := Finset.univ.filter fun δ : Fin U → Fin V =>
          (target8 t₀ m ht₀ (actG (π_sub, δ) (s, B))).2 = kv_opt
        have hinj : Set.InjOn (fun (δ : Fin U → Fin V) (u : ↥(Finset.univ \ U_cov)) => δ u.1)
            (F_δ : Set (Fin U → Fin V)) := by
          intro δ₁ h₁ δ₂ h₂ hrest
          funext u
          by_cases hu : u ∈ U_cov
          · have heq1 := congrFun (Finset.mem_filter.mp h₁).2 u
            have heq2 := congrFun (Finset.mem_filter.mp h₂).2 u
            change (if u ∈ (actSeed8Equiv τ δ₁ s).activeKeys t₀ ht₀_n ∪
                (actSeed8Equiv τ δ₁ s).insertedSet t₀ m ht₀ ∪ B
              then some ((actSeed8Equiv τ δ₁ s).kv u) else none) = kv_opt u at heq1
            change (if u ∈ (actSeed8Equiv τ δ₂ s).activeKeys t₀ ht₀_n ∪
                (actSeed8Equiv τ δ₂ s).insertedSet t₀ m ht₀ ∪ B
              then some ((actSeed8Equiv τ δ₂ s).kv u) else none) = kv_opt u at heq2
            rw [actSeed8Equiv_activeKeys, actSeed8Equiv_insertedSet] at heq1 heq2
            change (if u ∈ U_cov then some (s.kv (τ.symm u) + δ₁ u) else none) = kv_opt u at heq1
            change (if u ∈ U_cov then some (s.kv (τ.symm u) + δ₂ u) else none) = kv_opt u at heq2
            rw [ite_eq_left hu] at heq1 heq2
            have hsum_eq : s.kv (τ.symm u) + δ₁ u = s.kv (τ.symm u) + δ₂ u :=
              Option.some.inj (heq1.trans heq2.symm)
            exact add_left_cancel hsum_eq
          · exact congrFun hrest ⟨u, Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, hu⟩⟩
        have hcard_Fδ : F_δ.card ≤ V ^ (U - (n + 2 * m - g)) := by
          have h1 : F_δ.card ≤ Fintype.card (↥(Finset.univ \ U_cov) → Fin V) :=
            Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj
          have h2 : Fintype.card (↥(Finset.univ \ U_cov) → Fin V) =
              V ^ (U - (n + 2 * m - g)) := by
            rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Finset.card_sdiff,
              Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ,
              Fintype.card_fin, hU_cov_card]
          exact h1.trans_eq h2
        calc F_δ.card * V ^ (n + 2 * m - g)
            ≤ V ^ (U - (n + 2 * m - g)) * V ^ (n + 2 * m - g) :=
              Nat.mul_le_mul_right _ hcard_Fδ
          _ = V ^ U := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
          _ = Fintype.card (Fin U → Fin V) := by simp
      -- Combine stab and F_δ over G = Perm S_comp × (Fin U → Fin V)
      have hsplit_sum : (Finset.univ.filter fun γ : G =>
            target8 t₀ m ht₀ (actG γ (s, B)) = (K_rem, kv_opt)).card =
          ∑ π_sub ∈ stab K_rem,
            (Finset.univ.filter fun δ : Fin U → Fin V =>
              (target8 t₀ m ht₀ (actG (π_sub, δ) (s, B))).2 = kv_opt).card := by
        have hfst (π_sub : Equiv.Perm ↥S_comp) (δ : Fin U → Fin V) :
            (target8 t₀ m ht₀ (actG (π_sub, δ) (s, B))).1 =
              K₀.map (Equiv.Perm.ofSubtype π_sub).toEmbedding := by
          change (actSeed8Equiv (Equiv.Perm.ofSubtype π_sub) δ s).activeKeys t₀ ht₀_n \
              Finset.univ.image (segDeletedKeys
                (actSeed8Equiv (Equiv.Perm.ofSubtype π_sub) δ s).keys
                (actSeed8Equiv (Equiv.Perm.ofSubtype π_sub) δ s).delPerm t₀ m ht₀) =
            K₀.map (Equiv.Perm.ofSubtype π_sub).toEmbedding
          dsimp only [K₀]
          rw [actSeed8Equiv_activeKeys, actSeed8Equiv_deletedSet, Finset.map_sdiff]
        rw [← Finset.card_sigma]
        refine Finset.card_bij (fun γ _ => ⟨γ.1, γ.2⟩)
          (fun γ hγ => ?_) (fun ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h => by
            injection h with ha hb; exact Prod.ext ha hb)
          (fun ⟨π_sub, δ⟩ hσ => ⟨(π_sub, δ), ?_, rfl⟩)
        · have hpair := Prod.mk.inj (Finset.mem_filter.mp hγ).2
          have h1 : (target8 t₀ m ht₀ (actG (γ.1, γ.2) (s, B))).1 = K_rem := hpair.1
          rw [hfst] at h1
          exact Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpair.2⟩⟩
        · obtain ⟨hπ, hδ⟩ := Finset.mem_sigma.mp hσ
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Prod.ext ?_
            (Finset.mem_filter.mp hδ).2⟩
          rw [hfst]; exact (Finset.mem_filter.mp hπ).2
      have hnat_ineq : (Finset.univ.filter fun γ : G =>
            target8 t₀ m ht₀ (actG γ (s, B)) = (K_rem, kv_opt)).card * M_nat ≤
          Fintype.card G := by
        dsimp only [M_nat, G]
        rw [Fintype.card_prod, hsplit_sum, mul_comm ((U - 3 * m).choose (n - m)),
          ← mul_assoc, Finset.sum_mul]
        calc (∑ π_sub ∈ stab K_rem,
              (Finset.univ.filter fun δ : Fin U → Fin V =>
                (target8 t₀ m ht₀ (actG (π_sub, δ) (s, B))).2 = kv_opt).card *
                  V ^ (n + 2 * m - g)) * (U - 3 * m).choose (n - m)
            ≤ (∑ _π_sub ∈ stab K_rem, Fintype.card (Fin U → Fin V)) *
                (U - 3 * m).choose (n - m) :=
              Nat.mul_le_mul_right _ (Finset.sum_le_sum fun π_sub _ => hval_le π_sub)
          _ = ((stab K_rem).card * (U - 3 * m).choose (n - m)) *
                Fintype.card (Fin U → Fin V) := by
              rw [Finset.sum_const, smul_eq_mul]; ring
          _ ≤ Fintype.card (Equiv.Perm ↥S_comp) * Fintype.card (Fin U → Fin V) :=
              Nat.mul_le_mul_right _ hstab_le
      exact_mod_cast hnat_ineq
    -- Average horbit_le over G to deduce fiber bound
    have havg_pair : (((μ_g.map fun sb => (obs8 t₀ m ht₀ sb, target8 t₀ m ht₀ sb)) (o, T)).toReal) *
        (Fintype.card G : ℝ) =
        ∑ sb, (μ_g sb).toReal *
          ((Finset.univ.filter fun γ : G =>
            obs8 t₀ m ht₀ sb = o ∧ target8 t₀ m ht₀ (actG γ sb) = T).card : ℝ) := by
      have hperm (γ : G) :
          ((μ_g.map fun sb => (obs8 t₀ m ht₀ sb, target8 t₀ m ht₀ sb)) (o, T)).toReal =
            ∑ sb, (μ_g sb).toReal *
              (if obs8 t₀ m ht₀ sb = o ∧ target8 t₀ m ht₀ (actG γ sb) = T then 1 else 0) := by
        rw [PMF.map_apply_toReal, ← (actG γ).sum_comp]
        refine Finset.sum_congr rfl fun sb _ => ?_
        by_cases ho_sb : obs8 t₀ m ht₀ sb = o
        · have ho_act : obs8 t₀ m ht₀ (actG γ sb) = o := (hobs_iff γ sb).mpr ho_sb
          rw [hμ_obs γ sb ho_sb]
          by_cases ht_act : target8 t₀ m ht₀ (actG γ sb) = T
          · have heq : (o, T) = (obs8 t₀ m ht₀ (actG γ sb), target8 t₀ m ht₀ (actG γ sb)) :=
              Prod.ext ho_act.symm ht_act.symm
            rw [ite_eq_left heq, ite_eq_left ⟨ho_sb, ht_act⟩, mul_one]
          · have hne_p : (o, T) ≠ (obs8 t₀ m ht₀ (actG γ sb), target8 t₀ m ht₀ (actG γ sb)) :=
              fun h => ht_act (Prod.mk.inj h).2.symm
            rw [ite_eq_right hne_p, ite_eq_right (fun h => ht_act h.2), mul_zero]
        · have ho_act : obs8 t₀ m ht₀ (actG γ sb) ≠ o := mt (hobs_iff γ sb).mp ho_sb
          have hne_p : (o, T) ≠ (obs8 t₀ m ht₀ (actG γ sb), target8 t₀ m ht₀ (actG γ sb)) :=
            fun h => ho_act (Prod.mk.inj h).1.symm
          rw [ite_eq_right hne_p, ite_eq_right (fun h => ho_sb h.1), mul_zero]
      calc (((μ_g.map fun sb => (obs8 t₀ m ht₀ sb, target8 t₀ m ht₀ sb)) (o, T)).toReal) *
            (Fintype.card G : ℝ)
          = ∑ _γ : G, ((μ_g.map fun sb => (obs8 t₀ m ht₀ sb, target8 t₀ m ht₀ sb))
              (o, T)).toReal := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
        _ = ∑ γ : G, ∑ sb, (μ_g sb).toReal *
              (if obs8 t₀ m ht₀ sb = o ∧ target8 t₀ m ht₀ (actG γ sb) = T then 1 else 0) :=
              Finset.sum_congr rfl fun γ _ => hperm γ
        _ = ∑ sb, (μ_g sb).toReal * ∑ γ : G,
              (if obs8 t₀ m ht₀ sb = o ∧ target8 t₀ m ht₀ (actG γ sb) = T then (1 : ℝ) else 0) := by
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun sb _ => (Finset.mul_sum _ _ _).symm
        _ = _ := by
              refine Finset.sum_congr rfl fun sb _ => ?_
              rw [Finset.card_filter]; push_cast; rfl
    have havg_obs : ((μ_g.map (obs8 t₀ m ht₀)) o).toReal * (Fintype.card G : ℝ) =
        ∑ sb, (μ_g sb).toReal * (if obs8 t₀ m ht₀ sb = o then (Fintype.card G : ℝ) else 0) := by
      rw [PMF.map_apply_toReal, Finset.sum_mul]
      refine Finset.sum_congr rfl fun sb _ => ?_
      by_cases ho_sb : obs8 t₀ m ht₀ sb = o
      · rw [ite_eq_left ho_sb.symm, ite_eq_left ho_sb]
      · rw [ite_eq_right (Ne.symm ho_sb), zero_mul, ite_eq_right ho_sb, mul_zero]
    have hG_pos : (0 : ℝ) < (Fintype.card G : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
    refine le_of_mul_le_mul_right ?_ hG_pos
    calc ((((μ_g.map fun sb => (obs8 t₀ m ht₀ sb, target8 t₀ m ht₀ sb)) (o, T)).toReal) *
            (M_nat : ℝ)) * (Fintype.card G : ℝ)
        = ((((μ_g.map fun sb => (obs8 t₀ m ht₀ sb, target8 t₀ m ht₀ sb)) (o, T)).toReal) *
            (Fintype.card G : ℝ)) * (M_nat : ℝ) := by ring
      _ = ∑ sb, (μ_g sb).toReal *
            (((Finset.univ.filter fun γ : G =>
              obs8 t₀ m ht₀ sb = o ∧ target8 t₀ m ht₀ (actG γ sb) = T).card : ℝ) *
                (M_nat : ℝ)) := by
            rw [havg_pair, Finset.sum_mul]
            exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ ∑ sb, (μ_g sb).toReal * (if obs8 t₀ m ht₀ sb = o then (Fintype.card G : ℝ) else 0) := by
            refine Finset.sum_le_sum fun sb _ => ?_
            by_cases hsupp : sb.2 ∈ Fg sb.1
            · by_cases ho_sb : obs8 t₀ m ht₀ sb = o
              · rw [ite_eq_left ho_sb]
                have hfilt_eq : (Finset.univ.filter fun γ : G =>
                    obs8 t₀ m ht₀ sb = o ∧ target8 t₀ m ht₀ (actG γ sb) = T) =
                    Finset.univ.filter fun γ : G => target8 t₀ m ht₀ (actG γ sb) = T := by
                  ext γ; simp [ho_sb]
                rw [hfilt_eq]
                exact mul_le_mul_of_nonneg_left (horbit_le sb ho_sb hsupp) ENNReal.toReal_nonneg
              · simp [ho_sb]
            · have h0 : (μ_g sb).toReal = 0 := by
                dsimp only [μ_g]
                rw [toReal_innerPoolDist_apply, ite_eq_right hsupp]
              rw [h0, zero_mul, zero_mul]
      _ = ((μ_g.map (obs8 t₀ m ht₀)) o).toReal * (Fintype.card G : ℝ) := havg_obs.symm
  · have hzero : ((μ_g.map fun sb => (obs8 t₀ m ht₀ sb, target8 t₀ m ht₀ sb)) (o, T)).toReal =
        0 := by
      rw [PMF.map_apply_toReal]
      refine Finset.sum_eq_zero fun sb _ => ?_
      by_cases heq : (o, T) = (obs8 t₀ m ht₀ sb, target8 t₀ m ht₀ sb)
      · have hBo : o.2.1 = sb.2 := (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj heq).1).2).1
        have hnFg : sb.2 ∉ Fg sb.1 := fun h => ho_card (hBo ▸
          (Finset.mem_powersetCard.mp (Finset.mem_filter.mp (hFg sb.1 ▸ h)).1).2)
        rw [ite_eq_left heq]
        dsimp only [μ_g]
        rw [toReal_innerPoolDist_apply, ite_eq_right hnFg]
      · rw [ite_eq_right heq]
    rw [hzero, zero_mul]
    exact ENNReal.toReal_nonneg

private theorem modeCandidateOps_congr (withQueries : Bool) {U V n t₀ m : ℕ}
    {s₁ s₂ : HardKeyValSeed U V n} (ht₀ : t₀ + m ≤ n) {B₁ B₂ : Finset (Fin U)}
    (hB₁ : B₁.card = m) (hB₂ : B₂.card = m)
    (ha : (fun r => segInsertedKeys s₁.keys t₀ m ht₀ r) =
      fun r => segInsertedKeys s₂.keys t₀ m ht₀ r)
    (hB : B₁ = B₂)
    (hd : (fun r => segDeletedKeys s₁.keys s₁.delPerm t₀ m ht₀ r) =
      fun r => segDeletedKeys s₂.keys s₂.delPerm t₀ m ht₀ r)
    (hkv : ∀ x ∈ B₁, s₁.kv x = s₂.kv x) :
    s₁.modeCandidateOps withQueries t₀ m ht₀ B₁ hB₁ =
      s₂.modeCandidateOps withQueries t₀ m ht₀ B₂ hB₂ := by
  subst hB
  have ha_emb : segInsertedKeys s₁.keys t₀ m ht₀ = segInsertedKeys s₂.keys t₀ m ht₀ :=
    Function.Embedding.ext (congrFun ha)
  have hd_emb : segDeletedKeys s₁.keys s₁.delPerm t₀ m ht₀ =
      segDeletedKeys s₂.keys s₂.delPerm t₀ m ht₀ :=
    Function.Embedding.ext (congrFun hd)
  rw [HardKeyValSeed.modeCandidateOps_eq, HardKeyValSeed.modeCandidateOps_eq]
  cases withQueries
  · simp only [Bool.false_eq_true, ↓reduceIte, HardKeyValSeed.candidateUpdateOps_eq,
      ha_emb, hd_emb, candidateDeleteInsertOps]
    refine List.flatMap_congr fun r _ => ?_
    rw [hkv _ (by rw [orderSubset_apply]; exact Finset.orderEmbOfFin_mem B₁ hB₁ _)]
  · simp only [↓reduceIte, HardKeyValSeed.candidateOps_eq, ha_emb, hd_emb]
    exact candidateQueryDeleteInsertOps_congr _ hB₁ _ hkv

private theorem decodeDict_modeCandidateOps_eq (withQueries : Bool) {U V n t₀ m cells w : ℕ}
    {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (modeHorizon withQueries n + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2)
    (s : HardKeyValSeed U V n) (ht₀ : t₀ + m ≤ n) {B : Finset (Fin U)} (hB : B.card = m)
    (hdisj : Disjoint B (s.activeKeys t₀ (Nat.le_of_add_right_le ht₀))) :
    let stride := modeStride withQueries
    let step₀ := n + stride * t₀
    let C_bef := memAt D_det (s.modeOps withQueries) step₀
    let C_post := (D_det.runInterval step₀ C_bef (s.modeCandidateOps withQueries t₀ m ht₀ B hB)).2
    decodeDict D_det (n + stride * (t₀ + m)) C_post =
      (fun u => if u ∈ (s.activeKeys t₀ (Nat.le_of_add_right_le ht₀) \
          Finset.univ.image (segDeletedKeys s.keys s.delPerm t₀ m ht₀)) ∪ B
        then some (s.kv u).val else none) := by
  dsimp only
  let stride := modeStride withQueries
  let step₀ := n + stride * t₀
  let pref_bef := (s.modeOps withQueries).take step₀
  have hlen_bef : pref_bef.length = step₀ :=
    s.length_take_modeOps withQueries (Nat.le_of_add_right_le ht₀)
  obtain ⟨hvh, hlen, hst⟩ := validHistory_and_run_modeCandidateOps withQueries s ht₀ hB hdisj
  have hpost_eq : (D_det.runInterval step₀ (memAt D_det (s.modeOps withQueries) step₀)
      (s.modeCandidateOps withQueries t₀ m ht₀ B hB)).2 =
      (D_det.runSeq (pref_bef ++ s.modeCandidateOps withQueries t₀ m ht₀ B hB)).2 := by
    symm
    dsimp only [memAt, pref_bef, step₀]
    rw [IndexedScheme.runSeq, IndexedScheme.runInterval_append, Nat.zero_add,
      s.length_take_modeOps withQueries (Nat.le_of_add_right_le ht₀)]
    rfl
  have hle : (pref_bef ++ s.modeCandidateOps withQueries t₀ m ht₀ B hB).length ≤
      modeHorizon withQueries n := by
    rw [hlen]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ ht₀) n
  have hdec := decodeDict_runSeq_eq hcorr hvh hle
  rw [hlen, ← hpost_eq] at hdec
  exact hdec.trans hst

open Classical in
private theorem prob_queryFreePool_eq_le (withQueries : Bool) {U V n t₀ m g P_size cells w : ℕ}
    {γ R t : ℝ} (hU : 3 * n ≤ U) (hV : 1 ≤ V) (hm : 2 ≤ m) (hm_n : 2 * m ≤ n)
    (hg : g < m / 2) (ht₀ : t₀ + m ≤ n)
    (hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
    (hbudget : 2 * R + 7 * (m : ℝ) + 2 * (m : ℝ) * t + γ * (m : ℝ) * (w : ℝ) +
      2 * γ * (m : ℝ) * Real.logb 2 U ≤
      ((m : ℝ) / 2) * Real.logb 2 V - (m : ℝ) * Real.logb 2 ((U : ℝ) / (n : ℝ)))
    {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (modeHorizon withQueries n + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2)
    (pool : HardKeyValSeed U V n → Finset (Fin U))
    (hcard_pool : ∀ s, (pool s).card = P_size)
    (hA_pool : ∀ s, s.insertedSet t₀ m ht₀ ⊆ pool s)
    (hdisj_pool : ∀ s, Disjoint (pool s) (s.activeKeys t₀ (Nat.le_of_add_right_le ht₀)))
    (hpool_act : ∀ [NeZero V] (τ : Equiv.Perm (Fin U)) (δ : Fin U → Fin V) s,
      pool (actSeed8Equiv τ δ s) = (pool s).map τ.toEmbedding)
    (Fg : HardKeyValSeed U V n → Finset (Finset (Fin U)))
    (hFg : ∀ s, Fg s = ((pool s).powersetCard m).filter fun B =>
      (s.insertedSet t₀ m ht₀ ∩ B).card = g)
    (hne : ∀ s, (Fg s).Nonempty) :
    (((innerPoolDist (by omega) hV Fg hne).map fun sb =>
      decide (IsModeSeedConsistent withQueries D_det t₀ m ht₀ γ t sb.1 sb.2)) true).toReal ≤
      (U : ℝ) ^ (-γ * (m : ℝ)) := by
  let _ : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb (by omega), fun _ => ⟨0, hV⟩, 1⟩⟩
  let Ω := HardKeyValSeed U V n × Finset (Fin U)
  let μ_g : PMF Ω := innerPoolDist (by omega : 2 * n ≤ U) hV Fg hne
  let stride := modeStride withQueries
  let step₀ := n + stride * t₀
  let step_end := n + stride * (t₀ + m)
  let M_cap : ℝ := (2 : ℝ) ^ (R + 1) * (U : ℝ) ^ (γ * (m : ℝ))
  let K_cap : ℕ := Nat.floor M_cap
  have hU_pos_nat : 1 ≤ U := by omega
  have hU_gt1 : (1 : ℝ) < (U : ℝ) := by exact_mod_cast (show 1 < U by omega)
  have hU_pos : (0 : ℝ) < (U : ℝ) := by positivity
  by_contra hgt
  push Not at hgt
  -- Sub-condition on stateFiber.card ≤ M_cap using prob_gt_cap_stateFiber_le
  let W_cons (sb : Ω) : Bool :=
    decide (IsModeSeedConsistent withQueries D_det t₀ m ht₀ γ t sb.1 sb.2)
  let W_bad (sb : Ω) : Bool :=
    decide (M_cap < ((stateFiber D_det step_end (pairBOf t₀ m ht₀ sb).val).card : ℝ))
  let W (sb : Ω) : Bool :=
    decide (IsModeSeedConsistent withQueries D_det t₀ m ht₀ γ t sb.1 sb.2 ∧
      ((stateFiber D_det step_end (pairBOf t₀ m ht₀ sb).val).card : ℝ) ≤ M_cap)
  have hbad_le : ((μ_g.map W_bad) true).toReal ≤ (1 / 2) * (U : ℝ) ^ (-γ * (m : ℝ)) :=
    prob_gt_cap_stateFiber_le (by omega) hU_pos_nat hV ht₀ hspace pool hcard_pool hA_pool
      hpool_act Fg hFg hne D_det step_end
  have hunion : ((μ_g.map W_cons) true).toReal ≤
      ((μ_g.map W) true).toReal + ((μ_g.map W_bad) true).toReal := by
    rw [PMF.map_apply_toReal, PMF.map_apply_toReal, PMF.map_apply_toReal, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun sb _ => ?_
    dsimp only [W_cons, W, W_bad]
    by_cases hc : IsModeSeedConsistent withQueries D_det t₀ m ht₀ γ t sb.1 sb.2
    · by_cases hle :
          ((stateFiber D_det step_end (pairBOf t₀ m ht₀ sb).val).card : ℝ) ≤ M_cap
      · have hnot : ¬ M_cap <
            ((stateFiber D_det step_end (pairBOf t₀ m ht₀ sb).val).card : ℝ) :=
          not_lt.mpr hle
        simp [hc, hle, hnot]
      · have hlt : M_cap <
            ((stateFiber D_det step_end (pairBOf t₀ m ht₀ sb).val).card : ℝ) :=
          lt_of_not_ge hle
        simp [hc, hle, hlt]
    · by_cases hlt :
          M_cap < ((stateFiber D_det step_end (pairBOf t₀ m ht₀ sb).val).card : ℝ) <;>
        simp [hc, hlt, ENNReal.toReal_nonneg]
  have hpW_gt : (1 / 2) * (U : ℝ) ^ (-γ * (m : ℝ)) < ((μ_g.map W) true).toReal := by
    change (U : ℝ) ^ (-γ * (m : ℝ)) < ((μ_g.map W_cons) true).toReal at hgt
    linarith
  have hpW_pos : 0 < ((μ_g.map W) true).toReal :=
    lt_trans (by positivity) hpW_gt
  have hW0 : (μ_g.map W) true ≠ 0 := fun h0 => by simp [h0] at hpW_pos
  have hlog_pW : -γ * (m : ℝ) * Real.logb 2 U - 1 < Real.logb 2 (((μ_g.map W) true).toReal) := by
    have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by positivity) hpW_gt
    rw [Real.logb_mul (by norm_num) (Real.rpow_pos_of_pos hU_pos _).ne',
      show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.logb_inv,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
      Real.logb_rpow_eq_mul_logb_of_pos hU_pos] at hlog
    linarith
  let p : PMF Ω := PMF.conditionalSnd (μ_g.map fun sb => (W sb, sb)) true
  have hp_supp (sb : Ω) (hsb : sb ∈ p.support) :
      sb.2 ∈ Fg sb.1 ∧ IsModeSeedConsistent withQueries D_det t₀ m ht₀ γ t sb.1 sb.2 ∧
        ((stateFiber D_det step_end (pairBOf t₀ m ht₀ sb).val).card : ℝ) ≤ M_cap := by
    have hW_mem : true ∈ ((μ_g.map fun x => (W x, x)).map Prod.fst).support := by
      rw [_root_.PMF.map_comp]; exact (_root_.PMF.mem_support_iff _ _).mpr hW0
    have hp_ne : p sb ≠ 0 := (_root_.PMF.mem_support_iff p sb).mp hsb
    rw [PMF.conditionalSnd_apply _ _ hW_mem] at hp_ne
    have hmap_ne : (μ_g.map fun x => (W x, x)) (true, sb) ≠ 0 :=
      fun h0 => hp_ne (by simp [h0])
    obtain ⟨x, hx_supp, hx_eq⟩ := (_root_.PMF.mem_support_map_iff _ _ (true, sb)).mp
      ((_root_.PMF.mem_support_iff _ _).mpr hmap_ne)
    obtain ⟨hWx, hxsb⟩ := Prod.mk.inj hx_eq
    subst hxsb
    have hW_true : IsModeSeedConsistent withQueries D_det t₀ m ht₀ γ t x.1 x.2 ∧
        ((stateFiber D_det step_end (pairBOf t₀ m ht₀ x).val).card : ℝ) ≤ M_cap :=
      of_decide_eq_true hWx
    have hx_Fg : x.2 ∈ Fg x.1 := by
      have hμ_ne : μ_g x ≠ 0 := (_root_.PMF.mem_support_iff μ_g x).mp hx_supp
      by_contra hnFg
      have h0 : (μ_g x).toReal = 0 := by
        dsimp only [μ_g]
        rw [toReal_innerPoolDist_apply, ite_eq_right hnFg]
      exact (ENNReal.toReal_pos hμ_ne (PMF.apply_ne_top μ_g x)).ne' h0
    exact ⟨hx_Fg, hW_true.1, hW_true.2⟩
  -- Define execution objects and 6-piece codeword on Ω
  let ht₀_n : t₀ ≤ n := Nat.le_of_add_right_le ht₀
  let C_bef (sb : Ω) := memAt D_det (sb.1.modeOps withQueries) step₀
  let ops_A (sb : Ω) := elemSlice n stride (sb.1.modeOps withQueries) t₀ (t₀ + m)
  let ops_B (sb : Ω) : List (Dynamic.Op U) :=
    if hB : sb.2.card = m then sb.1.modeCandidateOps withQueries t₀ m ht₀ sb.2 hB else []
  let S_A (sb : Ω) := D_det.probedCellsInterval step₀ (C_bef sb) (ops_A sb)
  let C_A (sb : Ω) := (D_det.runInterval step₀ (C_bef sb) (ops_A sb)).2
  let S_B (sb : Ω) := D_det.probedCellsInterval step₀ (C_bef sb) (ops_B sb)
  let C_B (sb : Ω) := (D_det.runInterval step₀ (C_bef sb) (ops_B sb)).2
  let C_mix (sb : Ω) := mixMem (C_bef sb) (C_A sb) (S_B sb)
  let SB_sim (sb : Ω) := D_det.probedCellsInterval step₀ (C_mix sb) (ops_B sb)
  let CB_sim (sb : Ω) := (D_det.runInterval step₀ (C_mix sb) (ops_B sb)).2
  let I_AB (sb : Ω) := S_A sb ∩ SB_sim sb
  let Δ_set (sb : Ω) := (I_AB sb).filter fun j => C_A sb j ≠ CB_sim sb j
  let dict_B (sb : Ω) := (pairBOf t₀ m ht₀ sb).val
  let m₁ (sb : Ω) := encodeRestr sb.2 sb.1.kv
  let m₂ (sb : Ω) := encodeFintype (C_mix sb)
  let m₃ (sb : Ω) := encodeRestr (SB_sim sb) (fun j => decide (j ∈ I_AB sb))
  let m₄ (sb : Ω) := encodeRestr (I_AB sb) (fun j => decide (j ∈ Δ_set sb))
  let m₅ (sb : Ω) := encodeRestr (Δ_set sb) (C_A sb)
  let m₆ (sb : Ω) := encodeMemFinset (stateFiber D_det step_end (dict_B sb)) K_cap (C_B sb)
  let msg (sb : Ω) := m₁ sb ++ (m₂ sb ++ (m₃ sb ++ (m₄ sb ++ (m₅ sb ++ m₆ sb))))
  -- Decoded state facts for any sb with sb.2 ∈ Fg sb.1
  have hstate (sb : Ω) (hFg_sb : sb.2 ∈ Fg sb.1) :
      let K := sb.1.activeKeys t₀ ht₀_n
      let D := Finset.univ.image (segDeletedKeys sb.1.keys sb.1.delPerm t₀ m ht₀)
      let A := sb.1.insertedSet t₀ m ht₀
      sb.2.card = m ∧ Disjoint sb.2 K ∧ Disjoint A K ∧
        decodeDict D_det step₀ (C_bef sb) =
          (fun u => if u ∈ K then some (sb.1.kv u).val else none) ∧
        decodeDict D_det step_end (C_A sb) =
          (fun u => if u ∈ (K \ D) ∪ A then some (sb.1.kv u).val else none) ∧
        C_B sb ∈ stateFiber D_det step_end (dict_B sb) := by
    dsimp only
    have hB_mp := Finset.mem_powersetCard.mp (Finset.mem_filter.mp (hFg sb.1 ▸ hFg_sb)).1
    have hB_card : sb.2.card = m := hB_mp.2
    have hdisj_B : Disjoint sb.2 (sb.1.activeKeys t₀ ht₀_n) :=
      (hdisj_pool sb.1).mono_left hB_mp.1
    have hdisj_A : Disjoint (sb.1.insertedSet t₀ m ht₀) (sb.1.activeKeys t₀ ht₀_n) :=
      (hdisj_pool sb.1).mono_left (hA_pool sb.1)
    have hA_card : (sb.1.insertedSet t₀ m ht₀).card = m :=
      (Finset.card_image_of_injective _
        (segInsertedKeys sb.1.keys t₀ m ht₀).injective).trans (by simp)
    -- (1) decodeDict step₀ C_bef
    have hdec_bef : decodeDict D_det step₀ (C_bef sb) =
        fun u => if u ∈ sb.1.activeKeys t₀ ht₀_n then some (sb.1.kv u).val else none := by
      have hvh_b := sb.1.validHistory_take_modeOps withQueries ht₀_n
      have hlen_b := sb.1.length_take_modeOps withQueries ht₀_n
      have hle_b : ((sb.1.modeOps withQueries).take step₀).length ≤ modeHorizon withQueries n := by
        rw [hlen_b]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ ht₀_n) n
      have hd := decodeDict_runSeq_eq hcorr hvh_b hle_b
      rw [hlen_b] at hd
      have hst := hd.trans (sb.1.run_take_modeOps_fst withQueries ht₀_n)
      change decodeDict D_det step₀ (C_bef sb) = _ at hst
      rw [hst, windowDict_coe]
      funext u
      by_cases hu : u ∈ sb.1.activeKeys t₀ ht₀_n
      · simp only [hu, ↓reduceIte]
        rw [HardKeyValSeed.activeKeys, Finset.mem_map] at hu
        obtain ⟨k, _, rfl⟩ := hu
        rw [dictOfEmb_apply_self, windowVals_apply, windowEmb_apply]
      · simp only [hu, ↓reduceIte]
        exact dictOfEmb_apply_eq_none _ _ fun k heq => hu
          (Finset.mem_map.mpr ⟨k, Finset.mem_univ k, heq⟩)
    -- (2) decodeDict step_end C_A
    have hdec_A : decodeDict D_det step_end (C_A sb) =
        fun u => if u ∈ (sb.1.activeKeys t₀ ht₀_n \
            Finset.univ.image (segDeletedKeys sb.1.keys sb.1.delPerm t₀ m ht₀)) ∪
            sb.1.insertedSet t₀ m ht₀
          then some (sb.1.kv u).val else none := by
      have hopsA_cand : ops_A sb =
          sb.1.modeCandidateOps withQueries t₀ m ht₀ (sb.1.insertedSet t₀ m ht₀) hA_card :=
        sb.1.elemSlice_modeOps_eq_trueCandidate withQueries ht₀
      dsimp only [C_A]
      rw [hopsA_cand]
      exact decodeDict_modeCandidateOps_eq withQueries hcorr sb.1 ht₀ hA_card hdisj_A
    -- (3) C_B ∈ stateFiber
    have hCB_mem : C_B sb ∈ stateFiber D_det step_end (dict_B sb) := by
      have hopsB_eq : ops_B sb = sb.1.modeCandidateOps withQueries t₀ m ht₀ sb.2 hB_card :=
        dite_eq_left hB_card
      rw [stateFiber, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      dsimp only [C_B, dict_B]
      rw [hopsB_eq, val_pairBOf_eq sb.1 ht₀ hB_card hdisj_B]
      exact decodeDict_modeCandidateOps_eq withQueries hcorr sb.1 ht₀ hB_card hdisj_B
    exact ⟨hB_card, hdisj_B, hdisj_A, hdec_bef, hdec_A, hCB_mem⟩
  -- Prefix-freeness and target8 injectivity on each obs8 fiber of p.support
  have hdecode (sb₁ : Ω) (hsb₁ : sb₁ ∈ p.support) (sb₂ : Ω) (hsb₂ : sb₂ ∈ p.support)
      (hobs : obs8 t₀ m ht₀ sb₁ = obs8 t₀ m ht₀ sb₂) (hpref : msg sb₁ <+: msg sb₂) :
      msg sb₁ = msg sb₂ ∧ target8 t₀ m ht₀ sb₁ = target8 t₀ m ht₀ sb₂ := by
    obtain ⟨hFg₁, _, hcap₁⟩ := hp_supp sb₁ hsb₁
    obtain ⟨hFg₂, _, hcap₂⟩ := hp_supp sb₂ hsb₂
    obtain ⟨hBc₁, hdisjB₁, hdisjA₁, hdec_bef₁, hdec_A₁, hCB_mem₁⟩ := hstate sb₁ hFg₁
    obtain ⟨hBc₂, hdisjB₂, hdisjA₂, hdec_bef₂, hdec_A₂, hCB_mem₂⟩ := hstate sb₂ hFg₂
    have ha : (fun r => segInsertedKeys sb₁.1.keys t₀ m ht₀ r) =
        fun r => segInsertedKeys sb₂.1.keys t₀ m ht₀ r := (Prod.mk.inj hobs).1
    have hB : sb₁.2 = sb₂.2 := (Prod.mk.inj (Prod.mk.inj hobs).2).1
    have hd : (fun r => segDeletedKeys sb₁.1.keys sb₁.1.delPerm t₀ m ht₀ r) =
        fun r => segDeletedKeys sb₂.1.keys sb₂.1.delPerm t₀ m ht₀ r :=
      (Prod.mk.inj (Prod.mk.inj hobs).2).2
    have hA_eq : sb₁.1.insertedSet t₀ m ht₀ = sb₂.1.insertedSet t₀ m ht₀ := by
      dsimp only [HardKeyValSeed.insertedSet]
      have ha_emb : segInsertedKeys sb₁.1.keys t₀ m ht₀ = segInsertedKeys sb₂.1.keys t₀ m ht₀ :=
        Function.Embedding.ext (congrFun ha)
      rw [ha_emb]
    obtain ⟨hm₁, hp2⟩ := prefix_append_of_length_eq (by simp [m₁, length_encodeRestr, hB]) hpref
    have hkvB : ∀ x ∈ sb₁.2, sb₁.1.kv x = sb₂.1.kv x := encodeRestr_inj hB hm₁
    have hopsB : ops_B sb₁ = ops_B sb₂ := by
      dsimp only [ops_B]
      rw [dite_eq_left hBc₁, dite_eq_left hBc₂]
      exact modeCandidateOps_congr withQueries ht₀ hBc₁ hBc₂ ha hB hd hkvB
    obtain ⟨hm₂, hp3⟩ := prefix_append_of_length_eq (by simp [m₂, length_encodeFintype]) hp2
    have hcm : C_mix sb₁ = C_mix sb₂ := encodeFintype_injective hm₂
    have hSB_sim : SB_sim sb₁ = SB_sim sb₂ := by dsimp only [SB_sim]; rw [hcm, hopsB]
    have hSB_eq (sb : Ω) : SB_sim sb = S_B sb :=
      (runInterval_mixMem_eq_of_probedCellsInterval_subset D_det step₀ (C_bef sb) (C_A sb)
        (S_B sb) (ops_B sb) subset_rfl).2.2.1
    have hSB : S_B sb₁ = S_B sb₂ := (hSB_eq sb₁).symm.trans (hSB_sim.trans (hSB_eq sb₂))
    obtain ⟨hm₃, hp4⟩ := prefix_append_of_length_eq (by simp [m₃, length_encodeRestr, hSB_sim]) hp3
    have hI_AB : I_AB sb₁ = I_AB sb₂ :=
      encodeRestr_subset_inj Finset.inter_subset_right Finset.inter_subset_right hSB_sim hm₃
    obtain ⟨hm₄, hp5⟩ := prefix_append_of_length_eq (by simp [m₄, length_encodeRestr, hI_AB]) hp4
    have hΔ : Δ_set sb₁ = Δ_set sb₂ :=
      encodeRestr_subset_inj (Finset.filter_subset _ _) (Finset.filter_subset _ _) hI_AB hm₄
    obtain ⟨hm₅, hp6⟩ := prefix_append_of_length_eq (by simp [m₅, length_encodeRestr, hΔ]) hp5
    have hm₆ : m₆ sb₁ = m₆ sb₂ := (prefix_append_of_length_eq (v₁ := []) (v₂ := [])
      (by simp [m₆, length_encodeMemFinset]) (by simpa using hp6)).1
    have hCA : C_A sb₁ = C_A sb₂ := by
      funext j
      by_cases hjΔ : j ∈ Δ_set sb₁
      · exact encodeRestr_inj hΔ hm₅ j hjΔ
      · by_cases hjI : j ∈ I_AB sb₁
        · have hj₁ : ¬ C_A sb₁ j ≠ CB_sim sb₁ j :=
            fun hne => hjΔ (Finset.mem_filter.mpr ⟨hjI, hne⟩)
          have hj₂ : ¬ C_A sb₂ j ≠ CB_sim sb₂ j :=
            fun hne => (hΔ ▸ hjΔ) (Finset.mem_filter.mpr ⟨hI_AB ▸ hjI, hne⟩)
          push Not at hj₁ hj₂
          dsimp only [CB_sim] at hj₁ hj₂
          rw [hj₁, hj₂, hcm, hopsB]
        · have hrec (sb : Ω) (hnot : j ∉ I_AB sb) : C_A sb j = C_mix sb j :=
            (mixMem_eq_postMem_of_notMem_inter D_det step₀ (C_bef sb) (ops_A sb)
              (S_B sb) (S_B sb) Finset.inter_subset_left
              (by dsimp only [I_AB] at hnot; rwa [hSB_eq sb] at hnot)).symm
          rw [hrec sb₁ hjI, hrec sb₂ (hI_AB ▸ hjI), hcm]
    -- Recover K \ D and kv on (K \ D) ∪ A from C_A
    let KD₁ := sb₁.1.activeKeys t₀ ht₀_n \
      Finset.univ.image (segDeletedKeys sb₁.1.keys sb₁.1.delPerm t₀ m ht₀)
    let KD₂ := sb₂.1.activeKeys t₀ ht₀_n \
      Finset.univ.image (segDeletedKeys sb₂.1.keys sb₂.1.delPerm t₀ m ht₀)
    have hdecA_eq : decodeDict D_det step_end (C_A sb₁) = decodeDict D_det step_end (C_A sb₂) :=
      congrArg (decodeDict D_det step_end) hCA
    rw [hdec_A₁, hdec_A₂] at hdecA_eq
    have hKDA_eq : KD₁ ∪ sb₁.1.insertedSet t₀ m ht₀ = KD₂ ∪ sb₂.1.insertedSet t₀ m ht₀ := by
      ext u
      have hu := congrFun hdecA_eq u
      change (if u ∈ KD₁ ∪ sb₁.1.insertedSet t₀ m ht₀ then some (sb₁.1.kv u).val else none) =
        (if u ∈ KD₂ ∪ sb₂.1.insertedSet t₀ m ht₀ then some (sb₂.1.kv u).val else none) at hu
      by_cases h1 : u ∈ KD₁ ∪ sb₁.1.insertedSet t₀ m ht₀ <;>
        by_cases h2 : u ∈ KD₂ ∪ sb₂.1.insertedSet t₀ m ht₀
      · exact iff_of_true h1 h2
      · rw [ite_eq_left h1, ite_eq_right h2] at hu; cases hu
      · rw [ite_eq_right h1, ite_eq_left h2] at hu; cases hu
      · exact iff_of_false h1 h2
    have hKD_eq : KD₁ = KD₂ := by
      have hs₁ : (KD₁ ∪ sb₁.1.insertedSet t₀ m ht₀) \ sb₁.1.insertedSet t₀ m ht₀ = KD₁ :=
        Finset.union_sdiff_cancel_right
          (Finset.disjoint_of_subset_left Finset.sdiff_subset hdisjA₁.symm)
      have hs₂ : (KD₂ ∪ sb₂.1.insertedSet t₀ m ht₀) \ sb₂.1.insertedSet t₀ m ht₀ = KD₂ :=
        Finset.union_sdiff_cancel_right
          (Finset.disjoint_of_subset_left Finset.sdiff_subset hdisjA₂.symm)
      rw [← hs₁, ← hs₂, hKDA_eq, hA_eq]
    have hkv_KDA (u : Fin U) (hu : u ∈ KD₁ ∪ sb₁.1.insertedSet t₀ m ht₀) :
        sb₁.1.kv u = sb₂.1.kv u := by
      have hu₂ : u ∈ KD₂ ∪ sb₂.1.insertedSet t₀ m ht₀ := hKDA_eq ▸ hu
      have heq := congrFun hdecA_eq u
      change (if u ∈ KD₁ ∪ sb₁.1.insertedSet t₀ m ht₀ then some (sb₁.1.kv u).val else none) =
        (if u ∈ KD₂ ∪ sb₂.1.insertedSet t₀ m ht₀ then some (sb₂.1.kv u).val else none) at heq
      rw [ite_eq_left hu, ite_eq_left hu₂] at heq
      exact Fin.ext (Option.some.inj heq)
    -- Recover dict_B, C_B, and C_bef
    have hdictB : dict_B sb₁ = dict_B sb₂ := by
      dsimp only [dict_B]
      rw [val_pairBOf_eq sb₁.1 ht₀ hBc₁ hdisjB₁,
        val_pairBOf_eq sb₂.1 ht₀ hBc₂ hdisjB₂]
      funext u
      change (if u ∈ KD₁ ∪ sb₁.2 then some (sb₁.1.kv u).val else none) =
        (if u ∈ KD₂ ∪ sb₂.2 then some (sb₂.1.kv u).val else none)
      have hun_eq : KD₁ ∪ sb₁.2 = KD₂ ∪ sb₂.2 := by rw [hKD_eq, hB]
      by_cases hu : u ∈ KD₁ ∪ sb₁.2
      · have hu₂ : u ∈ KD₂ ∪ sb₂.2 := hun_eq ▸ hu
        rw [ite_eq_left hu, ite_eq_left hu₂]
        rcases Finset.mem_union.mp hu with huKD | huB
        · rw [hkv_KDA u (Finset.mem_union_left _ huKD)]
        · rw [hkvB u huB]
      · have hu₂ : u ∉ KD₂ ∪ sb₂.2 := hun_eq ▸ hu
        rw [ite_eq_right hu, ite_eq_right hu₂]
    have hfib_le₁ : (stateFiber D_det step_end (dict_B sb₁)).card ≤ K_cap :=
      Nat.le_floor hcap₁
    have hCB : C_B sb₁ = C_B sb₂ :=
      encodeMemFinset_inj hCB_mem₁ (hdictB ▸ hCB_mem₂) hfib_le₁
        (by simpa only [m₆, hdictB] using hm₆)
    have hCbef : C_bef sb₁ = C_bef sb₂ := by
      funext j
      by_cases hj : j ∈ S_B sb₁
      · have h1 : C_mix sb₁ j = C_bef sb₁ j := mixMem_of_mem hj
        have h2 : C_mix sb₂ j = C_bef sb₂ j := mixMem_of_mem (hSB ▸ hj)
        rw [← h1, ← h2, hcm]
      · have h1 : C_B sb₁ j = C_bef sb₁ j :=
          D_det.nextMem_runInterval_eq_of_notMem_probedCellsInterval step₀ (C_bef sb₁)
            (ops_B sb₁) hj
        have h2 : C_B sb₂ j = C_bef sb₂ j :=
          D_det.nextMem_runInterval_eq_of_notMem_probedCellsInterval step₀ (C_bef sb₂)
            (ops_B sb₂) (show j ∉ S_B sb₂ from hSB ▸ hj)
        rw [← h1, ← h2, hCB]
    have hdec_bef_eq : decodeDict D_det step₀ (C_bef sb₁) = decodeDict D_det step₀ (C_bef sb₂) :=
      congrArg (decodeDict D_det step₀) hCbef
    rw [hdec_bef₁, hdec_bef₂] at hdec_bef_eq
    have hK_eq : sb₁.1.activeKeys t₀ ht₀_n = sb₂.1.activeKeys t₀ ht₀_n := by
      ext u
      have hu := congrFun hdec_bef_eq u
      by_cases h1 : u ∈ sb₁.1.activeKeys t₀ ht₀_n <;>
        by_cases h2 : u ∈ sb₂.1.activeKeys t₀ ht₀_n
      · exact iff_of_true h1 h2
      · rw [ite_eq_left h1, ite_eq_right h2] at hu; cases hu
      · rw [ite_eq_right h1, ite_eq_left h2] at hu; cases hu
      · exact iff_of_false h1 h2
    have hkv_K (u : Fin U) (hu : u ∈ sb₁.1.activeKeys t₀ ht₀_n) :
        sb₁.1.kv u = sb₂.1.kv u := by
      have hu₂ : u ∈ sb₂.1.activeKeys t₀ ht₀_n := hK_eq ▸ hu
      have heq := congrFun hdec_bef_eq u
      change (if u ∈ sb₁.1.activeKeys t₀ ht₀_n then some (sb₁.1.kv u).val else none) =
        (if u ∈ sb₂.1.activeKeys t₀ ht₀_n then some (sb₂.1.kv u).val else none) at heq
      rw [ite_eq_left hu, ite_eq_left hu₂] at heq
      exact Fin.ext (Option.some.inj heq)
    refine ⟨by dsimp only [msg]; rw [hm₁, hm₂, hm₃, hm₄, hm₅, hm₆],
      Prod.ext hKD_eq (funext fun u => ?_)⟩
    dsimp only [target8]
    have hcov_eq : sb₁.1.activeKeys t₀ ht₀_n ∪ sb₁.1.insertedSet t₀ m ht₀ ∪ sb₁.2 =
        sb₂.1.activeKeys t₀ ht₀_n ∪ sb₂.1.insertedSet t₀ m ht₀ ∪ sb₂.2 := by
      rw [hK_eq, hA_eq, hB]
    by_cases hu : u ∈ sb₁.1.activeKeys t₀ ht₀_n ∪ sb₁.1.insertedSet t₀ m ht₀ ∪ sb₁.2
    · have hu₂ : u ∈ sb₂.1.activeKeys t₀ ht₀_n ∪ sb₂.1.insertedSet t₀ m ht₀ ∪ sb₂.2 :=
        hcov_eq ▸ hu
      rw [ite_eq_left hu, ite_eq_left hu₂]
      rcases Finset.mem_union.mp hu with huKA | huB
      · rcases Finset.mem_union.mp huKA with huK | huA
        · rw [hkv_K u huK]
        · rw [hkv_KDA u (Finset.mem_union_right _ huA)]
      · rw [hkvB u huB]
    · have hu₂ : u ∉ sb₂.1.activeKeys t₀ ht₀_n ∪ sb₂.1.insertedSet t₀ m ht₀ ∪ sb₂.2 :=
        hcov_eq ▸ hu
      rw [ite_eq_right hu, ite_eq_right hu₂]
  -- Prefix-free entropy compression vs conditioned fiber entropy lower bound
  let joint_ot := p.map fun sb => (obs8 t₀ m ht₀ sb, target8 t₀ m ht₀ sb)
  have hcomp_bound : PMF.conditionalEntropy joint_ot ≤
      ∑ sb : Ω, (p sb).toReal * ((msg sb).length : ℝ) :=
    conditionalEntropy_map_le_expected_length_of_isPrefixFree p (obs8 t₀ m ht₀) (target8 t₀ m ht₀)
      msg (fun _ _ ⟨sb₁, ⟨h₁, ho₁⟩, hy₁⟩ _ ⟨sb₂, ⟨h₂, ho₂⟩, hy₂⟩ hp => by
        subst hy₁; subst hy₂; exact (hdecode sb₁ h₁ sb₂ h₂ (ho₁.trans ho₂.symm) hp).1)
      (fun sb₁ h₁ sb₂ h₂ hobs heq =>
        (hdecode sb₁ h₁ sb₂ h₂ hobs ⟨[], by simpa using heq⟩).2)
  let M_nat := (U - 3 * m).choose (n - m) * V ^ (n + 2 * m - g)
  have hM_pos : (0 : ℝ) < (M_nat : ℝ) := by
    dsimp only [M_nat]
    exact_mod_cast Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.pow_pos hV)
  have hent_lo : Real.logb 2 (((μ_g.map W) true).toReal) + Real.logb 2 (M_nat : ℝ) ≤
      PMF.conditionalEntropy joint_ot :=
    logb_prob_add_logb_le_conditionalEntropy_of_fiber_le μ_g W (obs8 t₀ m ht₀) (target8 t₀ m ht₀)
      hM_pos hW0 (fiber_le_queryFreePoolDist hU hV hm_n hg ht₀ pool hcard_pool hA_pool hdisj_pool
        hpool_act Fg hFg hne)
  -- Lower bound Real.logb 2 M_nat
  have hlog_M : benchmarkBits U V n + (3 / 2) * (m : ℝ) * Real.logb 2 V -
      (m : ℝ) * Real.logb 2 ((U : ℝ) / (n : ℝ)) - 5 * (m : ℝ) ≤ Real.logb 2 (M_nat : ℝ) := by
    have hc_pos : (0 : ℝ) < ((U - 3 * m).choose (n - m) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    have hv_pos : (0 : ℝ) < ((V ^ (n + 2 * m - g) : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_pos hV
    have hM_split : Real.logb 2 (M_nat : ℝ) =
        Real.logb 2 ((U - 3 * m).choose (n - m)) +
          ((n + 2 * m - g : ℕ) : ℝ) * Real.logb 2 V := by
      dsimp only [M_nat]
      rw [Nat.cast_mul, Real.logb_mul hc_pos.ne' hv_pos.ne', Nat.cast_pow, Real.logb_pow]
    have hchoose_gap := logb_choose_sub_logb_sub_three_mul_choose_sub_le hU
      (by omega : 1 ≤ m) (by omega : m ≤ n)
    have h2g : 2 * g ≤ m := by omega
    have hexp_ge : (n : ℝ) + (3 / 2) * (m : ℝ) ≤ ((n + 2 * m - g : ℕ) : ℝ) := by
      have : g ≤ 2 * m := by omega
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      have : 2 * (g : ℝ) ≤ (m : ℝ) := by exact_mod_cast h2g
      linarith
    have hlogV_nn : 0 ≤ Real.logb 2 V := Real.logb_nonneg (by norm_num) (by exact_mod_cast hV)
    have hv_gap := mul_le_mul_of_nonneg_right hexp_ge hlogV_nn
    rw [hM_split, benchmarkBits_eq]
    linarith
  -- Pointwise length bound on p.support
  have hlen_pt (sb : Ω) (hsb : sb ∈ p.support) :
      ((msg sb).length : ℝ) ≤ benchmarkBits U V n + (m : ℝ) * Real.logb 2 V + 2 * R +
        2 * (m : ℝ) * t + γ * (m : ℝ) * (w : ℝ) + γ * (m : ℝ) * Real.logb 2 U + 3 := by
    obtain ⟨hFg_sb, hcons, hcap⟩ := hp_supp sb hsb
    obtain ⟨hBc, _, _, _, _, hCB_mem⟩ := hstate sb hFg_sb
    obtain ⟨hBc', hΔ_le_raw, _, hSB_le_raw⟩ := hcons
    have hopsB_eq : ops_B sb = sb.1.modeCandidateOps withQueries t₀ m ht₀ sb.2 hBc' :=
      dite_eq_left hBc'
    obtain ⟨_, _, hSB_eq, hCB_on⟩ := runInterval_mixMem_eq_of_probedCellsInterval_subset D_det
      step₀ (C_bef sb) (C_A sb) (S_B sb) (ops_B sb) subset_rfl
    have hSB_cap : ((S_B sb).card : ℝ) ≤ (m : ℝ) * t := by
      dsimp only [S_B]; rw [hopsB_eq]; exact hSB_le_raw
    have hΔ_cap : ((Δ_set sb).card : ℝ) ≤ γ * (m : ℝ) := by
      have heq_set : Δ_set sb = (S_A sb ∩ S_B sb).filter fun j => C_A sb j ≠ C_B sb j := by
        dsimp only [Δ_set, I_AB, SB_sim, CB_sim, C_mix]
        rw [hSB_eq]
        exact Finset.filter_congr fun j hj => by rw [hCB_on j (Finset.inter_subset_right hj)]
      rw [heq_set]
      dsimp only [S_A, S_B, C_A, C_B]
      simp only [hopsB_eq]
      exact hΔ_le_raw
    have hm1 : ((m₁ sb).length : ℝ) ≤ (m : ℝ) * Real.logb 2 V + 1 := by
      dsimp only [m₁]
      rw [length_encodeRestr, Fintype.card_fin, hBc]
      refine (clog_two_lt_logb_add_one (pow_pos (by omega : 0 < V) m)).le.trans ?_
      rw [Nat.cast_pow, Real.logb_pow]
    have hm2 : ((m₂ sb).length : ℝ) ≤ benchmarkBits U V n + R := by
      dsimp only [m₂]
      rw [length_encodeFintype, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
        ← pow_mul, Nat.clog_pow _ _ (by norm_num), mul_comm]
      exact hspace
    have hm3 : ((m₃ sb).length : ℝ) ≤ (m : ℝ) * t := by
      simpa only [m₃, SB_sim, C_mix, length_encodeRestr_bool, hSB_eq] using hSB_cap
    have hm4 : ((m₄ sb).length : ℝ) ≤ (m : ℝ) * t := by
      simpa only [m₄, I_AB, SB_sim, C_mix, length_encodeRestr_bool, hSB_eq] using
        (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right)).trans hSB_cap
    have hm5 : ((m₅ sb).length : ℝ) ≤ γ * (m : ℝ) * (w : ℝ) := by
      dsimp only [m₅]
      rw [length_encodeRestr_fin_two_pow, Nat.cast_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right hΔ_cap (Nat.cast_nonneg w)
    have hm6 : ((m₆ sb).length : ℝ) ≤ R + 2 + γ * (m : ℝ) * Real.logb 2 U := by
      dsimp only [m₆]
      rw [length_encodeMemFinset]
      have hfib_pos : 1 ≤ (stateFiber D_det step_end (dict_B sb)).card :=
        Finset.card_pos.mpr ⟨C_B sb, hCB_mem⟩
      have hK_pos : 1 ≤ K_cap := hfib_pos.trans (Nat.le_floor hcap)
      have hclog := (clog_two_lt_logb_add_one hK_pos).le
      have hK_le_M : (K_cap : ℝ) ≤ M_cap := Nat.floor_le (by dsimp only [M_cap]; positivity)
      have hlogK : Real.logb 2 (K_cap : ℝ) ≤ R + 1 + γ * (m : ℝ) * Real.logb 2 U := by
        refine (Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hK_pos) hK_le_M).trans_eq
          ?_
        dsimp only [M_cap]
        rw [Real.logb_mul (by positivity) (by positivity),
          Real.logb_rpow (by norm_num) (by norm_num),
          Real.logb_rpow_eq_mul_logb_of_pos hU_pos]
      linarith
    simp only [msg, List.length_append, Nat.cast_add]
    linarith
  set C_upper := benchmarkBits U V n + (m : ℝ) * Real.logb 2 V + 2 * R +
    2 * (m : ℝ) * t + γ * (m : ℝ) * (w : ℝ) + γ * (m : ℝ) * Real.logb 2 U + 3
  have hexp_msg : (∑ sb : Ω, (p sb).toReal * ((msg sb).length : ℝ)) ≤ C_upper := by
    calc (∑ sb : Ω, (p sb).toReal * ((msg sb).length : ℝ))
        ≤ ∑ sb : Ω, (p sb).toReal * C_upper := by
          refine Finset.sum_le_sum fun sb _ => ?_
          by_cases h0 : (p sb).toReal = 0
          · simp [h0]
          · have hsb : sb ∈ p.support :=
              (_root_.PMF.mem_support_iff p sb).mpr fun h => h0 (by simp [h])
            exact mul_le_mul_of_nonneg_left (hlen_pt sb hsb) ENNReal.toReal_nonneg
      _ = C_upper := by rw [← Finset.sum_mul, PMF.sum_toReal p, one_mul]
  have hm_real : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  dsimp only [C_upper] at hexp_msg
  linarith

/-! #### Public Section 8.1 theorems (Lemma 8.1 and update-only / large-value `OuterLemma`) -/

private theorem disjoint_insertedSet_activeKeys {U V n t₀ r : ℕ} (s : HardKeyValSeed U V n)
    (hr : t₀ + r ≤ n) :
    Disjoint (s.insertedSet t₀ r hr) (s.activeKeys t₀ (Nat.le_of_add_right_le hr)) := by
  refine Finset.disjoint_left.mpr fun u hu hact => ?_
  simp only [HardKeyValSeed.insertedSet, segInsertedKeys_apply, HardKeyValSeed.activeKeys,
    HardKeyValSeed.permKeyEmb, Finset.mem_image, Finset.mem_map, Finset.mem_univ, true_and,
    windowEmb_apply, Function.Embedding.trans_apply, Equiv.coe_toEmbedding] at hu hact
  obtain ⟨j, rfl⟩ := hu
  obtain ⟨k, hk⟩ := hact
  have hge : s.keys (liftDelPerm s.delPerm ⟨n + (t₀ + j.val), by have := j.isLt; omega⟩) =
      s.keys ⟨n + (t₀ + j.val), by have := j.isLt; omega⟩ := by
    rw [liftDelPerm_apply_ge s.delPerm (by omega) (by have := j.isLt; omega)]
  rw [← hge] at hk
  have hidx := congrArg Fin.val ((liftDelPerm s.delPerm).injective (s.keys.injective hk))
  dsimp only at hidx
  have := k.isLt; omega

open Classical in
/-- Query-free inner-game conditional `(seed, B)` distribution sampling `B ⊆ Finset.univ \ K`
uniformly among `m`-subsets with `(A ∩ B).card = g` under `3 * n ≤ U` ([LiLiangYuZhou2023],
Section 8.1, Lemma 8.1, p. 28 / PDF p. 29). -/
noncomputable def queryFreeInnerDist {U V n : ℕ} (t₀ m g : ℕ) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
    (hg : g ≤ m) (ht₀ : t₀ + m ≤ n) :
    PMF (HardKeyValSeed U V n × Finset (Fin U)) :=
  innerPoolDist (by omega) hV
    (fun s => (((Finset.univ \ s.activeKeys t₀ (Nat.le_of_add_right_le ht₀)).powersetCard m).filter
      fun B => (s.insertedSet t₀ m ht₀ ∩ B).card = g))
    (fun s => by
      have ht₀_n : t₀ ≤ n := Nat.le_of_add_right_le ht₀
      have hsub : s.insertedSet t₀ m ht₀ ⊆ Finset.univ \ s.activeKeys t₀ ht₀_n :=
        Finset.subset_sdiff.mpr ⟨Finset.subset_univ _, disjoint_insertedSet_activeKeys s ht₀⟩
      have hcard_pool : (Finset.univ \ s.activeKeys t₀ ht₀_n).card = U - n := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ,
          Fintype.card_fin]
        simp [HardKeyValSeed.activeKeys]
      rw [← Finset.card_pos, card_inter_filter_powersetCard hsub
        ((Finset.card_image_of_injective _
          (segInsertedKeys s.keys t₀ m ht₀).injective).trans (by simp)), hcard_pool]
      exact mul_pos (Nat.choose_pos hg) (Nat.choose_pos (by omega)))

open Classical in
/-- **Lemma 8.1** ([LiLiangYuZhou2023], Section 8.1, pp. 28–30 / PDF pp. 29–31, adapted with the
deterministic `c = 1` probe cap and Step 6 internal Markov sub-conditioning): under `3 * n ≤ U`,
`2 ≤ m`, `2 * m ≤ n`, and `g < m / 2`, the probability of `IsModeSeedConsistent` on
`queryFreeInnerDist` (`|A ∩ B| = g`) is at most `U ^ (-γ * m)`. -/
theorem prob_isModeSeedConsistent_queryFreeInnerDist_le (withQueries : Bool)
    {U V n t₀ m g cells w : ℕ} {γ R t : ℝ}
    (hU : 3 * n ≤ U) (hV : 1 ≤ V) (hm : 2 ≤ m) (hm_n : 2 * m ≤ n)
    (hg : g < m / 2) (ht₀ : t₀ + m ≤ n)
    (hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
    (hbudget : 2 * R + 7 * (m : ℝ) + 2 * (m : ℝ) * t + γ * (m : ℝ) * (w : ℝ) +
      2 * γ * (m : ℝ) * Real.logb 2 U ≤
      ((m : ℝ) / 2) * Real.logb 2 V - (m : ℝ) * Real.logb 2 ((U : ℝ) / (n : ℝ)))
    {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (modeHorizon withQueries n + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) :
    (((queryFreeInnerDist t₀ m g hU hV (by omega) ht₀).map fun sb =>
      decide (IsModeSeedConsistent withQueries D_det t₀ m ht₀ γ t sb.1 sb.2)) true).toReal ≤
      (U : ℝ) ^ (-γ * (m : ℝ)) := by
  let ht₀_n : t₀ ≤ n := Nat.le_of_add_right_le ht₀
  let pool (s : HardKeyValSeed U V n) := Finset.univ \ s.activeKeys t₀ ht₀_n
  have hcard_pool (s : HardKeyValSeed U V n) : (pool s).card = U - n := by
    dsimp only [pool]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin]
    simp [HardKeyValSeed.activeKeys]
  have hA_pool (s : HardKeyValSeed U V n) : s.insertedSet t₀ m ht₀ ⊆ pool s :=
    Finset.subset_sdiff.mpr ⟨Finset.subset_univ _, disjoint_insertedSet_activeKeys s ht₀⟩
  have hpool_act [NeZero V] (τ : Equiv.Perm (Fin U)) (δ : Fin U → Fin V)
      (s : HardKeyValSeed U V n) : pool (actSeed8Equiv τ δ s) = (pool s).map τ.toEmbedding := by
    dsimp only [pool]
    rw [actSeed8Equiv_activeKeys, Finset.map_sdiff]
    congr 1; ext x; simp only [Finset.mem_univ, Finset.mem_map, Equiv.coe_toEmbedding, true_iff]
    exact ⟨τ.symm x, trivial, τ.apply_symm_apply x⟩
  exact prob_queryFreePool_eq_le withQueries hU hV hm hm_n hg ht₀ hspace hbudget hcorr pool
    hcard_pool hA_pool (fun _ => Finset.sdiff_disjoint) hpool_act _ (fun _ => rfl) _

open Classical in
/-- Claim 4.2 far-candidate expectation bound for `IsModeSeedConsistent` over the remaining
inserted-key pool `s.insertedSet t₀ r_rest hrest` ([LiLiangYuZhou2023], Section 4.3, Claim 4.2,
p. 17 / PDF p. 18 and Section 8.1, Lemma 8.1, p. 28 / PDF p. 29). -/
theorem expected_card_modeConsistent_segmentRest_lt_half_le (withQueries : Bool)
    {U V n t₀ m r_rest cells w : ℕ} {γ R t : ℝ}
    (hU : 3 * n ≤ U) (hV : 1 ≤ V) (hm : 2 ≤ m) (hm_n : 2 * m ≤ n)
    (hrest_ge : 2 * m ≤ r_rest) (hrest : t₀ + r_rest ≤ n)
    (hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
    (hbudget : 2 * R + 7 * (m : ℝ) + 2 * (m : ℝ) * t + γ * (m : ℝ) * (w : ℝ) +
      2 * γ * (m : ℝ) * Real.logb 2 U ≤
      ((m : ℝ) / 2) * Real.logb 2 V - (m : ℝ) * Real.logb 2 ((U : ℝ) / (n : ℝ)))
    {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (modeHorizon withQueries n + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) :
    let ht₀ : t₀ + m ≤ n := by omega
    letI : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb (by omega), fun _ => ⟨0, hV⟩, 1⟩⟩
    (∑ s : HardKeyValSeed U V n, ((PMF.uniformOfFintype (HardKeyValSeed U V n)) s).toReal *
      ((((((s.insertedSet t₀ r_rest hrest).powersetCard m).filter fun B =>
        (s.insertedSet t₀ m ht₀ ∩ B).card < m / 2).filter
        (IsModeSeedConsistent withQueries D_det t₀ m ht₀ γ t s)).card : ℕ) : ℝ)) ≤
      (r_rest.choose m : ℝ) * (U : ℝ) ^ (-γ * (m : ℝ)) := by
  dsimp only
  let ht₀ : t₀ + m ≤ n := by omega
  let ht₀_n : t₀ ≤ n := Nat.le_of_add_right_le ht₀
  let pool (s : HardKeyValSeed U V n) := s.insertedSet t₀ r_rest hrest
  have hcard_pool (s : HardKeyValSeed U V n) : (pool s).card = r_rest :=
    (Finset.card_image_of_injective _ (segInsertedKeys s.keys t₀ r_rest hrest).injective).trans
      (by simp)
  have hA_pool (s : HardKeyValSeed U V n) : s.insertedSet t₀ m ht₀ ⊆ pool s := by
    intro u hu
    simp only [pool, HardKeyValSeed.insertedSet, segInsertedKeys_apply, Finset.mem_image,
      Finset.mem_univ, true_and] at hu ⊢
    obtain ⟨r, rfl⟩ := hu
    exact ⟨⟨r.val, by have := r.isLt; omega⟩, rfl⟩
  have hdisj_pool (s : HardKeyValSeed U V n) : Disjoint (pool s) (s.activeKeys t₀ ht₀_n) :=
    disjoint_insertedSet_activeKeys s hrest
  have hpool_act [NeZero V] (τ : Equiv.Perm (Fin U)) (δ : Fin U → Fin V)
      (s : HardKeyValSeed U V n) : pool (actSeed8Equiv τ δ s) = (pool s).map τ.toEmbedding :=
    actSeed8Equiv_insertedSet τ δ s t₀ r_rest hrest
  have hne : ∀ s : HardKeyValSeed U V n,
      (((pool s).powersetCard m).filter fun B =>
        (s.insertedSet t₀ m ht₀ ∩ B).card < m / 2).Nonempty := fun s => by
    have h0 : (((pool s).powersetCard m).filter fun B =>
        (s.insertedSet t₀ m ht₀ ∩ B).card = 0).Nonempty := by
      rw [← Finset.card_pos, card_inter_filter_powersetCard (hA_pool s)
        ((Finset.card_image_of_injective _
          (segInsertedKeys s.keys t₀ m ht₀).injective).trans (by simp)), hcard_pool]
      exact mul_pos (Nat.choose_pos (Nat.zero_le m)) (Nat.choose_pos (by omega))
    obtain ⟨B, hB⟩ := h0
    exact ⟨B, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hB).1,
      by rw [(Finset.mem_filter.mp hB).2]; omega⟩⟩
  exact (prob_and_expect_innerPoolDist_lt_half_le (by omega) hV ht₀ hrest_ge
    (Real.rpow_nonneg (Nat.cast_nonneg U) _) pool hcard_pool hA_pool
    (IsModeSeedConsistent withQueries D_det t₀ m ht₀ γ t)
    (fun g hg hne_g => prob_queryFreePool_eq_le withQueries hU hV hm hm_n hg ht₀ hspace
      hbudget hcorr pool hcard_pool hA_pool hdisj_pool hpool_act _ (fun _ => rfl) hne_g) hne).2

private theorem outer_lemma_of_val_budget (withQueries : Bool) {U V n cells w : ℕ}
    {R_outer R_inner γ t : ℝ} (hU : 3 * n ≤ U) (hV : 1 ≤ V)
    (hspace_outer : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R_outer)
    (hspace_inner : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R_inner)
    (T : MetaTree) {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (modeHorizon withQueries n + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2)
    (hγ : 0 < γ) (ht : 0 < t) {ℓ b : ℕ} (hℓ : 1 ≤ ℓ)
    (ht_stop : T.nodeStop (ℓ + 1) b ≤ n)
    (hF_lo : 2 ^ 64 ≤ T.fanout (ℓ + 1))
    (hF_hi : (T.fanout (ℓ + 1) : ℝ) ≤ (γ / 2) * Real.logb 2 U)
    (hR_outer : 100 * R_outer ≤ (T.blockSize (ℓ + 1) : ℝ) * Real.logb 2 (T.fanout (ℓ + 1)))
    (hbudget_inner : 2 * R_inner + 7 * (T.blockSize ℓ : ℝ) + 2 * (T.blockSize ℓ : ℝ) * t +
      γ * (T.blockSize ℓ : ℝ) * (w : ℝ) + 2 * γ * (T.blockSize ℓ : ℝ) * Real.logb 2 U ≤
      ((T.blockSize ℓ : ℝ) / 2) * Real.logb 2 V -
        (T.blockSize ℓ : ℝ) * Real.logb 2 ((U : ℝ) / (n : ℝ))) :
    (γ / 100) * (T.blockSize (ℓ + 1) : ℝ) ≤
        ∑' ops, (modeDist withQueries U V n
          (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
          (T.nodeCost D_det n (modeStride withQueries) ops ℓ b : ℝ) ∨
      (1 / 16) * (T.blockSize (ℓ + 1) : ℝ) * t ≤
        ∑' ops, (modeDist withQueries U V n
          (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
          (T.nodeProbes D_det n (modeStride withQueries) ops (ℓ + 1) b : ℝ) := by
  have hm_ge2 : 2 ≤ T.blockSize ℓ :=
    (Nat.pow_le_pow_right (by decide) hℓ).trans (T.two_pow_le_blockSize ℓ)
  have hF_ge2 : 2 ≤ T.fanout (ℓ + 1) := T.two_le_fanout (Nat.le_add_left 1 ℓ)
  have hm_n : 2 * T.blockSize ℓ ≤ n := by
    clear hF_lo
    have h1 : 2 * T.blockSize ℓ ≤ T.blockSize ℓ * T.fanout (ℓ + 1) := by
      rw [mul_comm 2]; exact Nat.mul_le_mul_left _ hF_ge2
    have h2 : T.blockSize (ℓ + 1) ≤ T.nodeStop (ℓ + 1) b :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos b)
    rw [T.blockSize_succ] at h2; omega
  have hU2 : 2 ≤ U := by clear hF_lo; omega
  exact outer_node_lower_bound withQueries
    (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hU2 hV hspace_outer T hcorr
    hγ ht hℓ ht_stop hF_lo hF_hi hR_outer fun i _ => by
      clear hF_lo
      have hFh : 2 ≤ T.fanout (ℓ + 1) - i.val := by omega
      exact expected_card_modeConsistent_segmentRest_lt_half_le withQueries hU hV hm_ge2 hm_n
        (Nat.mul_le_mul_right _ hFh) (nodeStart_add_rest_le T ht_stop i.val i.isLt.le)
        hspace_inner hbudget_inner hcorr

/-- Update-only **Outer Lemma** on `insertDeleteDist` ([LiLiangYuZhou2023], Section 8.1, pp. 27–30 /
PDF pp. 28–31, combining Protocol 1 `outer_node_lower_bound false` with Lemma 8.1). -/
theorem outer_lemma_insertDelete {U V n cells w : ℕ} {R_outer R_inner γ t : ℝ}
    (hU : 3 * n ≤ U) (hV : 1 ≤ V)
    (hspace_outer : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R_outer)
    (hspace_inner : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R_inner)
    (T : MetaTree) {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2)
    (hγ : 0 < γ) (ht : 0 < t) {ℓ b : ℕ} (hℓ : 1 ≤ ℓ)
    (ht_stop : T.nodeStop (ℓ + 1) b ≤ n)
    (hF_lo : 2 ^ 64 ≤ T.fanout (ℓ + 1))
    (hF_hi : (T.fanout (ℓ + 1) : ℝ) ≤ (γ / 2) * Real.logb 2 U)
    (hR_outer : 100 * R_outer ≤ (T.blockSize (ℓ + 1) : ℝ) * Real.logb 2 (T.fanout (ℓ + 1)))
    (hbudget_inner : 2 * R_inner + 7 * (T.blockSize ℓ : ℝ) + 2 * (T.blockSize ℓ : ℝ) * t +
      γ * (T.blockSize ℓ : ℝ) * (w : ℝ) + 2 * γ * (T.blockSize ℓ : ℝ) * Real.logb 2 U ≤
      ((T.blockSize ℓ : ℝ) / 2) * Real.logb 2 V -
        (T.blockSize ℓ : ℝ) * Real.logb 2 ((U : ℝ) / (n : ℝ))) :
    (γ / 100) * (T.blockSize (ℓ + 1) : ℝ) ≤
        ∑' ops, (insertDeleteDist U V n (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU)
          hV ops).toReal * (T.nodeCost D_det n 2 ops ℓ b : ℝ) ∨
      (1 / 16) * (T.blockSize (ℓ + 1) : ℝ) * t ≤
        ∑' ops, (insertDeleteDist U V n (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU)
          hV ops).toReal * (T.nodeProbes D_det n 2 ops (ℓ + 1) b : ℝ) := by
  exact
    outer_lemma_of_val_budget false hU hV hspace_outer hspace_inner T
      (by simpa only [modeHorizon, modeStride, Bool.false_eq_true, ↓reduceIte,
        show n + 2 * n = 3 * n by ring] using hcorr)
      hγ ht hℓ ht_stop hF_lo hF_hi hR_outer hbudget_inner

/-- Large-value **Outer Lemma** on `insertQueryDeleteDist` ([LiLiangYuZhou2023], Sections 7 and 8.1,
combining `outer_node_lower_bound true` with Lemma 8.1 so word sizes `w = Θ(log U + log V)` remain
covered when `V > U ^ 3` without secondary hash-table reductions). -/
theorem outer_lemma_largeVal_insertQueryDelete {U V n cells w : ℕ} {R_outer R_inner γ t : ℝ}
    (hU : 3 * n ≤ U) (hV : 1 ≤ V)
    (hspace_outer : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R_outer)
    (hspace_inner : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R_inner)
    (T : MetaTree) {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2)
    (hγ : 0 < γ) (ht : 0 < t) {ℓ b : ℕ} (hℓ : 1 ≤ ℓ)
    (ht_stop : T.nodeStop (ℓ + 1) b ≤ n)
    (hF_lo : 2 ^ 64 ≤ T.fanout (ℓ + 1))
    (hF_hi : (T.fanout (ℓ + 1) : ℝ) ≤ (γ / 2) * Real.logb 2 U)
    (hR_outer : 100 * R_outer ≤ (T.blockSize (ℓ + 1) : ℝ) * Real.logb 2 (T.fanout (ℓ + 1)))
    (hbudget_inner : 2 * R_inner + 7 * (T.blockSize ℓ : ℝ) + 2 * (T.blockSize ℓ : ℝ) * t +
      γ * (T.blockSize ℓ : ℝ) * (w : ℝ) + 2 * γ * (T.blockSize ℓ : ℝ) * Real.logb 2 U ≤
      ((T.blockSize ℓ : ℝ) / 2) * Real.logb 2 V -
        (T.blockSize ℓ : ℝ) * Real.logb 2 ((U : ℝ) / (n : ℝ))) :
    (γ / 100) * (T.blockSize (ℓ + 1) : ℝ) ≤
        ∑' ops, (insertQueryDeleteDist U V n
          (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
          (T.nodeCost D_det n 3 ops ℓ b : ℝ) ∨
      (1 / 16) * (T.blockSize (ℓ + 1) : ℝ) * t ≤
        ∑' ops, (insertQueryDeleteDist U V n
          (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
          (T.nodeProbes D_det n 3 ops (ℓ + 1) b : ℝ) := by
  exact
    outer_lemma_of_val_budget true hU hV hspace_outer hspace_inner T
      (by simpa only [modeHorizon, modeStride, ↓reduceIte,
        show n + 3 * n = 4 * n by ring] using hcorr)
      hγ ht hℓ ht_stop hF_lo hF_hi hR_outer hbudget_inner

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
  { toFun s := ⟨σ.toEmbedding.trans s.keys, s.kv, s.delPerm⟩
    invFun s := ⟨σ.toEmbedding.trans s.keys, s.kv, s.delPerm⟩
    left_inv s := by
      cases s
      simp only [HardKeyValSeed.mk.injEq, and_true]
      ext m; simp [σ, Equiv.swap_apply_self]
    right_inv s := by
      cases s
      simp only [HardKeyValSeed.mk.injEq, and_true]
      ext m; simp [σ, Equiv.swap_apply_self] }

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
  have hlen : (initInsertSeq s.keys (fun idx => s.kv (s.keys idx))).length = n :=
    length_initInsertSeq _ _
  cases withQueries
  · exact List.take_left' hlen
  · exact List.take_left' hlen

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
        rangeProbes D_det 0 1 (s.modeOps withQueries) 0 m := by
      intro m
      induction m with
      | zero => simp
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
        dsimp only [s₂]
        rw [swapInitKeySeed_keys]
        simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
        congr 1
        refine Equiv.swap_apply_of_ne_of_ne (fun h => hne (congrArg Fin.val h)) fun h => ?_
        have hv := congrArg Fin.val h; dsimp only at hv; omega
      have hfr : (List.finRange n)[j]? = some ⟨j, hj⟩ := by
        rw [List.getElem?_eq_getElem (by simp [hj])]; simp
      simp only [initInsertSeq, List.getElem?_map, hfr, Option.map_some, s₂, swapInitKeySeed_kv]
      rw [hkey]
    have htake_i : ops₁.take i.val = ops₂.take i.val := by
      have hi_le : i.val ≤ n := i.isLt.le
      have htk (xs : List (Dynamic.Op U)) : xs.take i.val = (xs.take n).take i.val := by
        rw [List.take_take, Nat.min_eq_left hi_le]
      rw [htk ops₁, htk ops₂, take_n_modeOps_eq_initInsertSeq, take_n_modeOps_eq_initInsertSeq]
      refine List.ext_getElem (by simp [hi_le]) fun j hj1 hj2 => ?_
      have hj_lt_i : j < i.val := by simp [List.length_take] at hj1; omega
      rw [List.getElem_take, List.getElem_take]
      have hopt := hget_eq j (hj_lt_i.trans i.isLt) hj_lt_i.ne
      rw [List.getElem?_eq_getElem (by simp [hj_lt_i.trans i.isLt]),
        List.getElem?_eq_getElem (by simp [hj_lt_i.trans i.isLt])] at hopt
      exact Option.some.inj hopt
    have hslice_after : elemSlice 0 1 ops₁ (i.val + 1) n = elemSlice 0 1 ops₂ (i.val + 1) n := by
      have h_eq (ops : List (Dynamic.Op U)) :
          elemSlice 0 1 ops (i.val + 1) n = (ops.take n).drop (i.val + 1) := by
        simp only [elemSlice, Nat.zero_add, Nat.one_mul, List.drop_take]
      rw [h_eq ops₁, h_eq ops₂, take_n_modeOps_eq_initInsertSeq, take_n_modeOps_eq_initInsertSeq]
      refine List.ext_getElem (by simp) fun k hk1 hk2 => ?_
      have hk_lt : i.val + 1 + k < n := by simp at hk1; omega
      rw [List.getElem_drop, List.getElem_drop]
      have hopt := hget_eq (i.val + 1 + k) hk_lt (by omega)
      rw [List.getElem?_eq_getElem (by simp [hk_lt]),
        List.getElem?_eq_getElem (by simp [hk_lt])] at hopt
      exact Option.some.inj hopt
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
      funext cell
      have hnot : cell ∉ rangeProbedCells D_det 0 1 (s'.modeOps withQueries) i.val (i.val + 1) := by
        simp [hemp]
      simp only [rangeProbedCells, Nat.zero_add, Nat.one_mul] at hnot
      exact D_det.nextMem_runInterval_eq_of_notMem_probedCellsInterval i.val _ _ hnot
    have hmem_i : memAt D_det ops₁ i.val = memAt D_det ops₂ i.val := by
      simp only [memAt, htake_i]
    have hmem_i1 : memAt D_det ops₁ (i.val + 1) = memAt D_det ops₂ (i.val + 1) :=
      (hmem_step_zero s hp₁).trans (hmem_i.trans (hmem_step_zero s₂ hp₂).symm)
    have hmem_n : memAt D_det ops₁ n = memAt D_det ops₂ n := by
      have hm1 := memAt_eq_runInterval_elemSlice D_det 0 1 ops₁ i.isLt
      have hm2 := memAt_eq_runInterval_elemSlice D_det 0 1 ops₂ i.isLt
      simp only [Nat.zero_add, Nat.one_mul] at hm1 hm2
      rw [hm1, hm2, hmem_i1, hslice_after]
    have hlen1 : (ops₁.take n).length = n := by
      simpa using s.length_take_modeOps withQueries (Nat.zero_le n)
    have hlen2 : (ops₂.take n).length = n := by
      simpa using s₂.length_take_modeOps withQueries (Nat.zero_le n)
    have hdec1 := decodeDict_runSeq_eq hcorr
      (by simpa using s.validHistory_take_modeOps withQueries (Nat.zero_le n))
      (by rw [hlen1]; simp [modeHorizon])
    have hdec2 := decodeDict_runSeq_eq hcorr
      (by simpa using s₂.validHistory_take_modeOps withQueries (Nat.zero_le n))
      (by rw [hlen2]; simp [modeHorizon])
    rw [hlen1] at hdec1; rw [hlen2] at hdec2
    have hst1 := s.run_take_modeOps_fst withQueries (Nat.zero_le n)
    have hst2 := s₂.run_take_modeOps_fst withQueries (Nat.zero_le n)
    simp only [Nat.mul_zero, Nat.add_zero] at hst1 hst2
    have hdict_eq : (windowDict s.permKeyEmb (fun idx => s.kv (s.permKeyEmb idx)) 0
        (Nat.zero_le n)).1 =
        (windowDict s₂.permKeyEmb (fun idx => s₂.kv (s₂.permKeyEmb idx)) 0 (Nat.zero_le n)).1 :=
      hst1.symm.trans (hdec1.symm.trans ((congrArg (decodeDict D_det n) hmem_n).trans
        (hdec2.trans hst2)))
    let u := s.keys ⟨i.val, by have := i.isLt; omega⟩
    have hu1 : (windowDict s.permKeyEmb (fun idx => s.kv (s.permKeyEmb idx)) 0
        (Nat.zero_le n)).1 u = some (s.kv u).val := by
      rw [windowDict_coe]
      let k₀ : Fin n := s.delPerm.symm i
      have hk₀ : windowEmb s.permKeyEmb 0 (Nat.zero_le n) k₀ = u := by
        simp [k₀, HardKeyValSeed.permKeyEmb, u]
      rw [← hk₀, dictOfEmb_apply_self]
      simp [windowVals_apply, windowEmb_apply]
    have hu2 : (windowDict s₂.permKeyEmb (fun idx => s₂.kv (s₂.permKeyEmb idx)) 0
        (Nat.zero_le n)).1 u = none := by
      rw [windowDict_coe]
      refine dictOfEmb_apply_eq_none _ _ fun k heq => ?_
      dsimp only [s₂] at heq
      simp only [windowEmb_apply, Nat.zero_add, HardKeyValSeed.permKeyEmb, swapInitKeySeed_keys,
        swapInitKeySeed_delPerm, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
        liftDelPerm_apply_lt s.delPerm k.isLt, u] at heq
      have hinj := s.keys.injective heq
      by_cases hk : s.delPerm k = i
      · have hidx : (⟨(s.delPerm k).val, by have := (s.delPerm k).isLt; omega⟩ : Fin (2 * n)) =
            ⟨i.val, by have := i.isLt; omega⟩ := by
          ext; exact congrArg (Fin.val (n := n)) hk
        rw [hidx, Equiv.swap_apply_left] at hinj
        have hv := congrArg Fin.val hinj; dsimp only at hv; omega
      · have hne1 : (⟨(s.delPerm k).val, by have := (s.delPerm k).isLt; omega⟩ : Fin (2 * n)) ≠
            ⟨i.val, by have := i.isLt; omega⟩ :=
          fun h => hk (Fin.ext (congrArg (Fin.val (n := 2 * n)) h))
        have hne2 : (⟨(s.delPerm k).val, by have := (s.delPerm k).isLt; omega⟩ : Fin (2 * n)) ≠
            ⟨n + i.val, by have := i.isLt; omega⟩ := by
          intro h; have hv := congrArg Fin.val h; dsimp only at hv
          have := (s.delPerm k).isLt; omega
        rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2] at hinj
        exact hne1 hinj
    have hcon := (congrFun hdict_eq u).symm.trans hu1
    rw [hu2] at hcon; cases hcon
  have hstep_ge (i : Fin n) : (1 / 2 : ℝ) ≤ ∑ s, (μ s).toReal * (stepProbe s i.val : ℝ) := by
    have hμ_const (s : HardKeyValSeed U V n) : (μ (swapInitKeySeed i s)).toReal = (μ s).toReal := by
      simp [μ, PMF.uniformOfFintype_apply]
    have hswap_sum : (∑ s, (μ s).toReal * (stepProbe (swapInitKeySeed i s) i.val : ℝ)) =
        ∑ s, (μ s).toReal * (stepProbe s i.val : ℝ) := by
      conv_rhs => rw [← Equiv.sum_comp (swapInitKeySeed i)]
      exact Finset.sum_congr rfl fun s _ => by rw [hμ_const]
    have h2 : (1 : ℝ) ≤ 2 * ∑ s, (μ s).toReal * (stepProbe s i.val : ℝ) := by
      calc (1 : ℝ) = (∑ s, (μ s).toReal) * 1 := by rw [PMF.sum_toReal, one_mul]
        _ = ∑ s, (μ s).toReal * 1 := Finset.sum_mul _ _ _
        _ ≤ ∑ s, (μ s).toReal *
              ((stepProbe s i.val : ℝ) + (stepProbe (swapInitKeySeed i s) i.val : ℝ)) := by
            refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
            exact_mod_cast hone_le_pair i s
        _ = (∑ s, (μ s).toReal * (stepProbe s i.val : ℝ)) +
              (∑ s, (μ s).toReal * (stepProbe (swapInitKeySeed i s) i.val : ℝ)) := by
            simp_rw [mul_add, Finset.sum_add_distrib]
        _ = 2 * ∑ s, (μ s).toReal * (stepProbe s i.val : ℝ) := by rw [hswap_sum]; ring
    linarith
  calc ((n : ℝ) / 2) = ∑ _i : Fin n, (1 / 2 : ℝ) := by simp; ring
    _ ≤ ∑ i : Fin n, ∑ s, (μ s).toReal * (stepProbe s i.val : ℝ) :=
        Finset.sum_le_sum fun i _ => hstep_ge i
    _ = ∑ s, (μ s).toReal * (∑ i : Fin n, (stepProbe s i.val : ℝ)) := by
        rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
    _ ≤ ∑ s, (μ s).toReal * (D_det.seqProbes (s.modeOps withQueries) : ℝ) := by
        refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        exact_mod_cast hsum_le_seq s

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

/-! ### Part C: Multi-Level Cell-Probe Lower Bounds (Theorems 1.1, 1.2, and 1.3) -/

private theorem floorLogStar_sub_one_le_logb {n U : ℕ} (hn : 2 ≤ n) (hnU : n ≤ U) :
    ((Nat.floorLogStar n - 1 : ℕ) : ℝ) ≤ Real.logb 2 U := by
  have hf : Nat.floorLogStar n = Nat.floorLogStar (Nat.log 2 n) + 1 :=
    Nat.floorLogStar_of_gt_one (by omega)
  have hle1 : Nat.floorLogStar n - 1 ≤ Nat.log 2 n := by
    rw [hf, Nat.add_sub_cancel]; exact Nat.floorLogStar_le_self _
  have hle2 : (Nat.log 2 n : ℝ) ≤ Real.logb 2 n := Real.natLog_le_logb n 2
  have hle3 : Real.logb 2 n ≤ Real.logb 2 U :=
    Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast (show 0 < n by omega))
      (by exact_mod_cast hnU)
  exact (show ((Nat.floorLogStar n - 1 : ℕ) : ℝ) ≤ (Nat.log 2 n : ℝ) by exact_mod_cast hle1).trans
    (hle2.trans hle3)

private theorem eight_mul_le_two_pow {q : ℕ} (hq : 6 ≤ q) : 8 * q ≤ 2 ^ q := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hq
  induction d with
  | zero => decide
  | succ d ih =>
    have hpow : 6 + (d + 1) = (6 + d) + 1 := by omega
    rw [hpow, Nat.pow_succ]; omega

private theorem logb_le_rpow_of_ge_pow {γ : ℝ} (hγ : 0 < γ) {n : ℕ}
    (hn_big : 2 ^ (2 * (Nat.ceil (4 / γ) + 1) * (2 * (Nat.ceil (4 / γ) + 1) + 2)) ≤ n) :
    Real.logb 2 n ≤ (n : ℝ) ^ (γ / 2) := by
  generalize hM_def : Nat.ceil (4 / γ) + 1 = M at hn_big
  have hM_pos : 1 ≤ M := by rw [← hM_def]; exact Nat.le_add_left 1 _
  have hc : 4 / γ ≤ (M : ℝ) := by
    rw [← hM_def]; exact (Nat.le_ceil (4 / γ)).trans (by push_cast; linarith)
  clear hM_def
  have hn1 : 1 ≤ n := (Nat.one_le_pow _ _ Nat.two_pos).trans hn_big
  set L := Nat.log 2 n
  have hL_ge : 2 * M * (2 * M + 2) ≤ L := by
    have h1 := Nat.log_mono_right (b := 2) hn_big
    rwa [Nat.log_pow Nat.one_lt_two] at h1
  set q := L / (2 * M)
  have hq_ge : 2 * M + 2 ≤ q := (Nat.le_div_iff_mul_le (by positivity)).mpr
    (by rw [mul_comm]; exact hL_ge)
  have hL1_le : L + 1 ≤ (2 * M + 1) * (q + 1) := by
    have hdiv := Nat.div_add_mod L (2 * M)
    have hmod := Nat.mod_lt L (show 0 < 2 * M by positivity)
    dsimp only [q] at *; nlinarith
  have hq1_pow : q + 1 ≤ 2 ^ q := Nat.lt_two_pow_self
  have h2M_pow : 2 * M + 1 ≤ 2 ^ q :=
    (Nat.lt_two_pow_self (n := 2 * M)).trans_le (Nat.pow_le_pow_right Nat.two_pos (by omega))
  have hL1_pow : L + 1 ≤ 2 ^ (2 * q) := by
    calc L + 1 ≤ (2 * M + 1) * (q + 1) := hL1_le
      _ ≤ 2 ^ q * 2 ^ q := Nat.mul_le_mul h2M_pow hq1_pow
      _ = 2 ^ (2 * q) := by rw [← Nat.pow_add, two_mul]
  have hlog_lt : Real.logb 2 n ≤ ((L + 1 : ℕ) : ℝ) := by
    have hn_lt : (n : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by
      exact_mod_cast (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le
    have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast hn1) hn_lt
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hl
  have hpow_le_n : ((2 : ℝ) ^ (2 * M * q : ℕ)) ≤ (n : ℝ) := by
    have h1 : 2 * M * q ≤ L := Nat.mul_div_le L (2 * M)
    have h2 : 2 ^ (2 * M * q) ≤ n :=
      (Nat.pow_le_pow_right Nat.two_pos h1).trans (Nat.pow_log_le_self 2 (by omega))
    exact_mod_cast h2
  have hrpow1 : (2 : ℝ) ^ (2 * q : ℕ) ≤ (n : ℝ) ^ (1 / (M : ℝ)) := by
    have hM_ne : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
    have h := Real.rpow_le_rpow (by positivity) hpow_le_n (show 0 ≤ 1 / (M : ℝ) by positivity)
    rw [← Real.rpow_natCast (2 : ℝ) (2 * M * q), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at h
    have hexp_eq : ((2 * M * q : ℕ) : ℝ) * (1 / (M : ℝ)) = ((2 * q : ℕ) : ℝ) := by
      push_cast; field_simp
    rw [hexp_eq, Real.rpow_natCast] at h
    exact h
  have hrpow2 : (n : ℝ) ^ (1 / (M : ℝ)) ≤ (n : ℝ) ^ (γ / 2) := by
    refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) ?_
    have hM_pos_r : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
    rw [div_le_iff₀ hM_pos_r]
    have hmul := (div_le_iff₀ hγ).mp hc
    nlinarith
  have hcast_pow : ((L + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * q : ℕ) := by exact_mod_cast hL1_pow
  exact hlog_lt.trans (hcast_pow.trans (hrpow1.trans hrpow2))

/-- Shared `iterLogMetaTree` structural bounds across Theorems 1.1 and 1.3(1). -/
private theorem iterLog_tree_bounds {γ c_R : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hcR : 0 ≤ c_R)
    {c_tree s_off n U k k' : ℕ}
    (hct8 : 8 ≤ c_tree) (hct_ceil : 808 * (c_R + 1) / γ ≤ (c_tree : ℝ))
    (hs_off : s_off = Nat.logStar (max 71 (4 * c_tree * (4 * c_tree + 71))) + 2)
    (hn : 2 ≤ n) (hnU : n ≤ U) (hfls : 4 ≤ Nat.floorLogStar n)
    (hk_lo : 2 * s_off + 6 ≤ k) (hk_hi : k ≤ Nat.logStar n)
    (hk' : k' = min k (Nat.floorLogStar n - 1)) :
    2 ≤ k' - s_off ∧ (k : ℝ) / 4 ≤ ((k' - s_off - 1 : ℕ) : ℝ) ∧
      ((k' - s_off - 1 : ℕ) : ℝ) ≤ Real.logb 2 U ∧
      ((max (Nat.iterLog k n) 1 : ℕ) : ℝ) ≤ (Nat.iterLog k' n : ℝ) ∧
      (n : ℝ) ≤ ((iterLogMetaTree n k' c_tree).blockSize 1 : ℝ) * Real.logb 2 n ∧
      (∀ ℓ ∈ Finset.Ico 1 (k' - s_off),
        (iterLogMetaTree n k' c_tree).blockSize (ℓ + 1) ≤ n / 2 ∧
          2 ^ 64 ≤ (iterLogMetaTree n k' c_tree).fanout (ℓ + 1) ∧
          ((iterLogMetaTree n k' c_tree).fanout (ℓ + 1) : ℝ) ≤ (γ / 2) * Real.logb 2 U ∧
          100 * (c_R * (n : ℝ) * (Nat.iterLog k' n : ℝ)) ≤
            ((iterLogMetaTree n k' c_tree).blockSize (ℓ + 1) : ℝ) *
              Real.logb 2 ((iterLogMetaTree n k' c_tree).fanout (ℓ + 1)) ∧
          c_R * (n : ℝ) * (Nat.iterLog k' n : ℝ) ≤
            (γ / 2) * ((iterLogMetaTree n k' c_tree).blockSize ℓ : ℝ) * Real.logb 2 U) := by
  generalize hs_def : Nat.logStar (max 71 (4 * c_tree * (4 * c_tree + 71))) = s at hs_off
  have hM_le_tw : max 71 (4 * c_tree * (4 * c_tree + 71)) ≤ Nat.twoTower (s + 1) :=
    (Nat.logStar_le_iff.mp (hs_def.le)).trans (Nat.twoTower_lt_twoTower_succ s).le
  have hct_808 : 808 * (c_R + 1) ≤ (c_tree : ℝ) := by
    have hmul := (div_le_iff₀ hγ).mp hct_ceil
    nlinarith
  have hk_le_fls : k ≤ (Nat.floorLogStar n - 1) + 2 := by
    have h1 := Nat.logStar_le_floorLogStar_add_one n
    omega
  have hk'_ge : 2 * s_off + 4 ≤ k' := by omega
  have hH_ge : 2 ≤ k' - s_off := by omega
  have hk_le_4H : k ≤ 4 * (k' - s_off - 1) := by omega
  have hk_r : (k : ℝ) / 4 ≤ ((k' - s_off - 1 : ℕ) : ℝ) := by
    have : (k : ℝ) ≤ 4 * ((k' - s_off - 1 : ℕ) : ℝ) := by exact_mod_cast hk_le_4H
    linarith
  have hH1_le_fls : k' - s_off - 1 ≤ Nat.floorLogStar n - 1 := by omega
  have hH1_logU : ((k' - s_off - 1 : ℕ) : ℝ) ≤ Real.logb 2 U :=
    (show ((k' - s_off - 1 : ℕ) : ℝ) ≤ ((Nat.floorLogStar n - 1 : ℕ) : ℝ) by
      exact_mod_cast hH1_le_fls).trans (floorLogStar_sub_one_le_logb hn hnU)
  have hk'_lt_fls : k' < Nat.floorLogStar n := by omega
  have hiter_k'_gt1 : 1 < Nat.iterLog k' n := Nat.lt_floorLogStar_iff.mp hk'_lt_fls
  have hmax_le : max (Nat.iterLog k n) 1 ≤ Nat.iterLog k' n :=
    max_le (Nat.iterLog_anti_left n (by omega)) (by omega)
  have hlog1_le_n : Nat.iterLog 1 n ≤ n := Nat.iterLog_le_self 1 n
  have h2n_le : 2 * Nat.iterLog 1 n ≤ 2 * n * Nat.iterLog k' n :=
    (Nat.mul_le_mul_left 2 hlog1_le_n).trans (Nat.le_mul_of_pos_right _ (by omega))
  have h2log1_le : 2 * Nat.iterLog 1 n ≤ c_tree * n * Nat.iterLog k' n :=
    h2n_le.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right n (by omega)))
  have hH_le_height : k' - s_off ≤ (iterLogMetaTree n k' c_tree).height := by
    have hh := le_height_iterLogMetaTree_add (c := c_tree) hn (by omega) h2log1_le
    rw [hs_def] at hh; omega
  clear hs_def
  generalize hT_def : iterLogMetaTree n k' c_tree = T at hH_le_height ⊢
  have hb1_mul : (c_tree - 2) * n * Nat.iterLog k' n ≤ T.blockSize 1 * Nat.iterLog 1 n := by
    have hm := mul_iterLog_le_blockSize_one_add_iterLogMetaTree hn k' c_tree
    rw [hT_def] at hm
    have hsub : (c_tree - 2) * (n * Nat.iterLog k' n) + 2 * (n * Nat.iterLog k' n) =
        c_tree * (n * Nat.iterLog k' n) := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
    have h1 : (c_tree - 2) * n * Nat.iterLog k' n + 2 * Nat.iterLog 1 n ≤
        c_tree * n * Nat.iterLog k' n := by
      calc (c_tree - 2) * n * Nat.iterLog k' n + 2 * Nat.iterLog 1 n
          = (c_tree - 2) * (n * Nat.iterLog k' n) + 2 * Nat.iterLog 1 n := by
            rw [mul_assoc]
        _ ≤ (c_tree - 2) * (n * Nat.iterLog k' n) + 2 * (n * Nat.iterLog k' n) :=
            Nat.add_le_add_left (h2n_le.trans_eq (mul_assoc 2 n _)) _
        _ = c_tree * (n * Nat.iterLog k' n) := hsub
        _ = c_tree * n * Nat.iterLog k' n := by rw [← mul_assoc]
    omega
  have hn_le_b1 : (n : ℝ) ≤ (T.blockSize 1 : ℝ) * Real.logb 2 n := by
    have h1 : n ≤ T.blockSize 1 * Nat.iterLog 1 n :=
      (Nat.le_mul_of_pos_left n (show 0 < c_tree - 2 by omega)).trans
        ((Nat.le_mul_of_pos_right _ (by omega)).trans hb1_mul)
    have h2 : (n : ℝ) ≤ (T.blockSize 1 : ℝ) * (Nat.log 2 n : ℝ) := by
      simpa only [Nat.iterLog_succ, Nat.iterLog_zero, Nat.cast_mul] using
        (show (n : ℝ) ≤ ((T.blockSize 1 * Nat.iterLog 1 n : ℕ) : ℝ) by exact_mod_cast h1)
    exact h2.trans (mul_le_mul_of_nonneg_left (Real.natLog_le_logb n 2) (Nat.cast_nonneg _))
  refine ⟨hH_ge, hk_r, hH1_logU, by exact_mod_cast hmax_le, hn_le_b1, fun ℓ hℓ => ?_⟩
  have hℓ_ge : 1 ≤ ℓ := (Finset.mem_Ico.mp hℓ).1
  have hℓ1_le_H : ℓ + 1 ≤ k' - s_off := (Finset.mem_Ico.mp hℓ).2
  have hblock_half : T.blockSize (ℓ + 1) ≤ n / 2 := by
    have h := (le_height_iterLogMetaTree_iff hn k' c_tree (ℓ + 1)).mp
      (hℓ1_le_H.trans (hT_def ▸ hH_le_height))
    rwa [hT_def] at h
  have hF_lo : 2 ^ 64 ≤ T.fanout (ℓ + 1) := by
    rw [← hT_def]; exact two_pow_le_fanout_iterLogMetaTree n k' c_tree (by omega)
  have hx_ge_M : max 71 (4 * c_tree * (4 * c_tree + 71)) ≤ Nat.iterLog (ℓ + 1) n := by
    refine hM_le_tw.trans ?_
    by_contra hlt; push Not at hlt
    have hle1 : Nat.iterLog s (Nat.iterLog (ℓ + 1) n) ≤ 1 :=
      Nat.iterLog_le_one_iff_lt_twoTower.mpr hlt
    have hstep_le : (s + 1) + (ℓ + 1) ≤ k' := by clear hF_lo; omega
    have h0 : Nat.iterLog ((s + 1) + (ℓ + 1)) n = 0 := by
      rw [Nat.iterLog_add, Nat.iterLog_succ]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle1 with hz | ho
      · rw [hz]; rfl
      · rw [ho]; rfl
    have hle0 := (Nat.iterLog_anti_left n hstep_le).trans_eq h0
    clear hF_lo; omega
  have hx71 : 71 ≤ Nat.iterLog (ℓ + 1) n := (_root_.le_max_left 71 _).trans hx_ge_M
  have hy71 : 71 ≤ Nat.iterLog ℓ n :=
    hx71.trans (Nat.iterLog_anti_left n (Nat.le_succ ℓ))
  have hx_ge_ct : c_tree ≤ Nat.iterLog (ℓ + 1) n := by
    have h1 : c_tree ≤ 4 * c_tree * (4 * c_tree + 71) :=
      (Nat.le_mul_of_pos_left _ (by decide)).trans
        (Nat.le_mul_of_pos_right _ (by clear hF_lo; omega))
    exact (h1.trans (_root_.le_max_right 71 _)).trans hx_ge_M
  have hlog1_logU : (Nat.iterLog 1 n : ℝ) ≤ Real.logb 2 U := by
    simpa only [Nat.iterLog_succ, Nat.iterLog_zero, Nat.cast_ofNat] using
      (Real.natLog_le_logb n 2).trans
        (Real.logb_le_logb_of_le (by norm_num)
          (by exact_mod_cast (show 0 < n by clear hF_lo; omega))
          (by exact_mod_cast hnU))
  have hF_hi : (T.fanout (ℓ + 1) : ℝ) ≤ (γ / 2) * Real.logb 2 U := by
    have hfm := fanout_mul_iterLog_le_iterLogMetaTree n k' c_tree
      (show 2 ≤ ℓ + 1 by clear hF_lo; omega) hx71
    rw [hT_def, Nat.add_sub_cancel] at hfm
    have hfm1 : T.fanout (ℓ + 1) * Nat.iterLog (ℓ + 1) n ≤ Nat.iterLog 1 n :=
      hfm.trans (Nat.iterLog_anti_left n hℓ_ge)
    have h2_div : 2 / γ ≤ (Nat.iterLog (ℓ + 1) n : ℝ) := by
      have h1 : 2 / γ ≤ 808 * (c_R + 1) / γ :=
        div_le_div_of_nonneg_right (by linarith) hγ.le
      exact (h1.trans hct_ceil).trans (by exact_mod_cast hx_ge_ct)
    have hmul : (T.fanout (ℓ + 1) : ℝ) * (2 / γ) ≤ Real.logb 2 U := by
      have hcast : (T.fanout (ℓ + 1) : ℝ) * (Nat.iterLog (ℓ + 1) n : ℝ) ≤ Real.logb 2 U := by
        rw [← Nat.cast_mul]
        exact (show ((T.fanout (ℓ + 1) * Nat.iterLog (ℓ + 1) n : ℕ) : ℝ) ≤ _ by
          exact_mod_cast hfm1).trans hlog1_logU
      exact (mul_le_mul_of_nonneg_left h2_div (Nat.cast_nonneg _)).trans hcast
    have hpos : 0 < 2 / γ := by positivity
    have hdiv := (le_div_iff₀ hpos).mpr hmul
    have hid : Real.logb 2 U / (2 / γ) = (γ / 2) * Real.logb 2 U := by field_simp
    linarith
  have hct_sub : ((c_tree - 2 : ℕ) : ℝ) = (c_tree : ℝ) - 2 := by
    rw [Nat.cast_sub (by clear hF_lo; omega)]; norm_num
  set R := c_R * (n : ℝ) * (Nat.iterLog k' n : ℝ)
  have hR_in : R ≤ (γ / 2) * (T.blockSize ℓ : ℝ) * Real.logb 2 U := by
    have htel := blockSize_one_mul_iterLog_le_two_mul_iterLogMetaTree n k' c_tree hℓ_ge hy71
    rw [hT_def] at htel
    have h1 : (c_tree - 2) * n * Nat.iterLog k' n ≤ 2 * (T.blockSize ℓ * Nat.iterLog 1 n) :=
      (hb1_mul.trans htel).trans
        (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (Nat.iterLog_anti_left n hℓ_ge)))
    have h1_r : ((c_tree - 2 : ℕ) : ℝ) * (n : ℝ) * (Nat.iterLog k' n : ℝ) ≤
        2 * ((T.blockSize ℓ : ℝ) * (Nat.iterLog 1 n : ℝ)) := by exact_mod_cast h1
    have hct_r : 4 * c_R / γ ≤ ((c_tree - 2 : ℕ) : ℝ) := by
      have h2γ : 2 ≤ 8 / γ := by rw [le_div_iff₀ hγ]; linarith
      have : 4 * c_R / γ + 8 / γ ≤ 808 * (c_R + 1) / γ :=
        (add_div _ _ _).symm.trans_le (div_le_div_of_nonneg_right (by linarith) hγ.le)
      linarith
    have hmul : (4 / γ) * R ≤ 2 * ((T.blockSize ℓ : ℝ) * Real.logb 2 U) := by
      calc (4 / γ) * R = (4 * c_R / γ) * (n : ℝ) * (Nat.iterLog k' n : ℝ) := by
            dsimp [R]; ring
        _ ≤ ((c_tree - 2 : ℕ) : ℝ) * (n : ℝ) * (Nat.iterLog k' n : ℝ) := by gcongr
        _ ≤ 2 * ((T.blockSize ℓ : ℝ) * (Nat.iterLog 1 n : ℝ)) := h1_r
        _ ≤ 2 * ((T.blockSize ℓ : ℝ) * Real.logb 2 U) := by gcongr
    have hpos : 0 < 4 / γ := by positivity
    have hmul_comm : R * (4 / γ) ≤ 2 * ((T.blockSize ℓ : ℝ) * Real.logb 2 U) := by
      rw [mul_comm]; exact hmul
    have hdiv : R ≤ 2 * ((T.blockSize ℓ : ℝ) * Real.logb 2 U) / (4 / γ) :=
      (le_div_iff₀ hpos).mpr hmul_comm
    have hid : 2 * ((T.blockSize ℓ : ℝ) * Real.logb 2 U) / (4 / γ) =
        (γ / 2) * (T.blockSize ℓ : ℝ) * Real.logb 2 U := by
      have : γ ≠ 0 := hγ.ne'
      field_simp; ring
    exact hdiv.trans_eq hid
  have hR_out : 100 * R ≤ (T.blockSize (ℓ + 1) : ℝ) * Real.logb 2 (T.fanout (ℓ + 1)) := by
    set x := Nat.iterLog (ℓ + 1) n
    have hx : 71 ≤ x := hx71
    set q := x / 3
    have hq6 : 6 ≤ q := by dsimp [q]; omega
    have h8q : 8 * q ≤ 2 ^ q := eight_mul_le_two_pow hq6
    have h2x_le : 2 * x ≤ 2 ^ q := by
      have : 2 * x ≤ 8 * q := by dsimp [q]; omega
      exact this.trans h8q
    have hpow_y : 2 ^ x ≤ Nat.iterLog ℓ n := by
      have hne : Nat.iterLog ℓ n ≠ 0 := by
        intro h0; have : x = 0 := by simp [x, Nat.iterLog_succ, h0]
        omega
      exact Nat.pow_log_le_self 2 hne
    have hmul_pow : 2 * x * 2 ^ q ≤ Nat.iterLog ℓ n := by
      calc 2 * x * 2 ^ q ≤ 2 ^ q * 2 ^ q := Nat.mul_le_mul_right _ h2x_le
        _ = 2 ^ (2 * q) := by rw [← Nat.pow_add, two_mul]
        _ ≤ 2 ^ x := Nat.pow_le_pow_right Nat.two_pos (by dsimp [q]; omega)
        _ ≤ Nat.iterLog ℓ n := hpow_y
    have hpow_le_F : 2 ^ q ≤ T.fanout (ℓ + 1) := by
      have hdiv_ge : 2 ^ q ≤ Nat.iterLog ℓ n / (2 * x) :=
        (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact hmul_pow)
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hℓ_ge
      have hF_eq : T.fanout (ℓ + 1) =
          2 * max (2 ^ 63) (Nat.iterLog ℓ n / (2 * x)) := by
        rw [← hT_def, iterLogMetaTree_fanout]
        have hidx : ℓ + 1 = d + 2 := by clear hF_lo h8q; omega
        rw [hidx]
        have hd1 : d + 1 = ℓ := by clear hF_lo h8q; omega
        have hd2 : d + 2 = ℓ + 1 := by clear hF_lo h8q; omega
        simp only [iterLogFanout, hd1, hd2, x]
      rw [hF_eq]
      exact (hdiv_ge.trans (_root_.le_max_right _ _)).trans (Nat.le_mul_of_pos_left _ Nat.two_pos)
    have hlog_F : (x : ℝ) / 4 ≤ Real.logb 2 (T.fanout (ℓ + 1)) := by
      have hq_log : (q : ℝ) ≤ Real.logb 2 (T.fanout (ℓ + 1)) := by
        have hp : (2 : ℝ) ^ q ≤ (T.fanout (ℓ + 1) : ℝ) := by exact_mod_cast hpow_le_F
        have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hp
        rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hl
      have hx_4q : x ≤ 4 * q := by clear hF_lo h8q; dsimp [q]; omega
      have hx_r : (x : ℝ) ≤ 4 * (q : ℝ) := by exact_mod_cast hx_4q
      linarith
    have htel1 := blockSize_one_mul_iterLog_le_two_mul_iterLogMetaTree n k' c_tree
      (show 1 ≤ ℓ + 1 by clear hF_lo h8q; omega) hx71
    rw [hT_def] at htel1
    have h1_r : ((c_tree - 2 : ℕ) : ℝ) * (n : ℝ) * (Nat.iterLog k' n : ℝ) ≤
        2 * ((T.blockSize (ℓ + 1) : ℝ) * (x : ℝ)) := by
      exact_mod_cast hb1_mul.trans htel1
    have h800 : 800 * c_R ≤ ((c_tree - 2 : ℕ) : ℝ) := by linarith
    have hmul1 : 800 * R ≤ 2 * ((T.blockSize (ℓ + 1) : ℝ) * (x : ℝ)) := by
      calc 800 * R = (800 * c_R) * (n : ℝ) * (Nat.iterLog k' n : ℝ) := by dsimp [R]; ring
        _ ≤ ((c_tree - 2 : ℕ) : ℝ) * (n : ℝ) * (Nat.iterLog k' n : ℝ) := by gcongr
        _ ≤ 2 * ((T.blockSize (ℓ + 1) : ℝ) * (x : ℝ)) := h1_r
    have hmul2 := mul_le_mul_of_nonneg_left hlog_F (Nat.cast_nonneg (T.blockSize (ℓ + 1)))
    linarith
  exact ⟨hblock_half, hF_lo, hF_hi, hR_out, hR_in⟩

/-- Unified single-node `OuterLemma` on `insertQueryDeleteDist` across both `V ≤ U ^ 3` (Section 5)
and `V > U ^ 3` (Section 8.1) under `w ≤ c_w * (log₂ U + log₂ V)`. -/
private theorem outer_lemma_both_val_regimes {U V n cells w : ℕ} {α c_w γ R t : ℝ}
    (hα : 0 < α) (hcw : 0 ≤ c_w) (hγ : 0 < γ)
    (hγ_eq : (20 + 24 * c_w) * γ = α / (1 + α))
    (hn : 2 ≤ n) (hU : 4 * n ≤ U) (hU_poly : (n : ℝ) ^ (1 + α) ≤ (U : ℝ)) (hV : 1 ≤ V)
    (hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
    (hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
    (T : MetaTree) {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2)
    (ht : 0 < t) {ℓ b : ℕ} (hℓ : 1 ≤ ℓ) (ht_stop : T.nodeStop (ℓ + 1) b ≤ n)
    (hF_lo : 2 ^ 64 ≤ T.fanout (ℓ + 1))
    (h11 : 11 / γ ≤ Real.logb 2 U)
    (ht_hi : 6 * t ≤ γ * Real.logb 2 U)
    (hm_lo : (n : ℝ) ^ (1 - γ / 2) ≤ (T.blockSize ℓ : ℝ))
    (hF_hi : (T.fanout (ℓ + 1) : ℝ) ≤ (γ / 2) * Real.logb 2 U)
    (hR_outer : 100 * R ≤ (T.blockSize (ℓ + 1) : ℝ) * Real.logb 2 (T.fanout (ℓ + 1)))
    (hR_in : R ≤ (γ / 2) * (T.blockSize ℓ : ℝ) * Real.logb 2 U) :
    (γ / 100) * (T.blockSize (ℓ + 1) : ℝ) ≤
        ∑' ops, (insertQueryDeleteDist U V n
          (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
          (T.nodeCost D_det n 3 ops ℓ b : ℝ) ∨
      (1 / 16) * (T.blockSize (ℓ + 1) : ℝ) * t ≤
        ∑' ops, (insertQueryDeleteDist U V n
          (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
          (T.nodeProbes D_det n 3 ops (ℓ + 1) b : ℝ) := by
  have hα_frac : α / (1 + α) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by clear hF_lo; omega)
  have hU_pos : (0 : ℝ) < (U : ℝ) := by exact_mod_cast (show 0 < U by clear hF_lo; omega)
  have hV_pos : (0 : ℝ) < (V : ℝ) := by exact_mod_cast hV
  have hlogU_nn : 0 ≤ Real.logb 2 U :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ U by clear hF_lo; omega))
  have hlogn_nn : 0 ≤ Real.logb 2 n :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ n by clear hF_lo; omega))
  have h11_mul : 11 ≤ γ * Real.logb 2 U := by
    have := (div_le_iff₀ hγ).mp h11; linarith
  set m := (T.blockSize ℓ : ℝ)
  have hm_nn : 0 ≤ m := Nat.cast_nonneg _
  by_cases hV3 : (V : ℝ) ≤ (U : ℝ) ^ 3
  · have hbud : R + 11 * m + 6 * m * t + γ * m * (w : ℝ) + (3 / 2) * γ * m * Real.logb 2 U ≤
        (m / 2) * Real.logb 2 ((U : ℝ) / (n : ℝ)) := by
      clear hF_lo
      have hlogV : Real.logb 2 V ≤ 3 * Real.logb 2 U := by
        have h1 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hV_pos hV3
        rwa [Real.logb_pow] at h1
      have hw_le : (w : ℝ) ≤ 4 * c_w * Real.logb 2 U := by
        calc (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V) := hw
          _ ≤ c_w * (Real.logb 2 U + 3 * Real.logb 2 U) := by gcongr
          _ = 4 * c_w * Real.logb 2 U := by ring
      have hlog_poly : (1 + α) * Real.logb 2 n ≤ Real.logb 2 U := by
        have h1 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
          (Real.rpow_pos_of_pos hn_pos _) hU_poly
        rwa [Real.logb_rpow_eq_mul_logb_of_pos hn_pos] at h1
      have hlog_div : (α / (1 + α)) * Real.logb 2 U ≤ Real.logb 2 ((U : ℝ) / (n : ℝ)) := by
        rw [Real.logb_div hU_pos.ne' hn_pos.ne']
        have hpos1 : 0 < 1 + α := by positivity
        have h1 : Real.logb 2 n ≤ Real.logb 2 U / (1 + α) :=
          (le_div_iff₀ hpos1).mpr (by linarith)
        have hid : Real.logb 2 U - Real.logb 2 U / (1 + α) = (α / (1 + α)) * Real.logb 2 U := by
          field_simp; ring
        linarith
      have hcoef : (4 + 4 * c_w) * γ ≤ α / (2 * (1 + α)) := by
        have h1 : 2 * ((4 + 4 * c_w) * γ) ≤ (20 + 24 * c_w) * γ := by nlinarith [hcw, hγ]
        have h2 : α / (1 + α) / 2 = α / (2 * (1 + α)) := by
          rw [div_div, mul_comm (1 + α) 2]
        linarith
      have h1 : 11 * m ≤ γ * m * Real.logb 2 U := by
        have := mul_le_mul_of_nonneg_right h11_mul hm_nn; linarith
      have h2 : 6 * m * t ≤ γ * m * Real.logb 2 U := by
        have := mul_le_mul_of_nonneg_left ht_hi hm_nn; linarith
      have h3 : γ * m * (w : ℝ) ≤ 4 * c_w * γ * m * Real.logb 2 U := by
        have := mul_le_mul_of_nonneg_left hw_le (show 0 ≤ γ * m by positivity); linarith
      have h4 : ((4 + 4 * c_w) * γ) * (m * Real.logb 2 U) ≤
          (α / (2 * (1 + α))) * (m * Real.logb 2 U) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      have h5 : (α / (2 * (1 + α))) * (m * Real.logb 2 U) ≤
          (m / 2) * Real.logb 2 ((U : ℝ) / (n : ℝ)) := by
        have h5a := mul_le_mul_of_nonneg_left hlog_div (show 0 ≤ m / 2 by positivity)
        have heq : (α / (2 * (1 + α))) * (m * Real.logb 2 U) =
            (m / 2) * ((α / (1 + α)) * Real.logb 2 U) := by
          have h1 : 2 * (1 + α) ≠ 0 := by positivity
          have h2 : 1 + α ≠ 0 := by positivity
          field_simp
        rw [heq]
        exact h5a
      linarith
    exact outer_lemma_insertQueryDelete hU hV hspace hspace T hcorr hγ ht hℓ ht_stop hm_lo hF_lo
      hF_hi hR_outer hbud
  · push Not at hV3
    have hbud : 2 * R + 7 * m + 2 * m * t + γ * m * (w : ℝ) + 2 * γ * m * Real.logb 2 U ≤
        (m / 2) * Real.logb 2 V - m * Real.logb 2 ((U : ℝ) / (n : ℝ)) := by
      clear hF_lo
      have hlogV : 3 * Real.logb 2 U ≤ Real.logb 2 V := by
        have h1 := (Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by positivity) hV3).le
        rwa [Real.logb_pow] at h1
      have hw_le : (w : ℝ) ≤ 2 * c_w * Real.logb 2 V := by
        have hU_le_V : Real.logb 2 U + Real.logb 2 V ≤ 2 * Real.logb 2 V := by linarith
        exact hw.trans ((mul_le_mul_of_nonneg_left hU_le_V hcw).trans_eq (by ring))
      have hγ20 : 5 * γ ≤ 1 / 4 := by
        have : 20 * γ ≤ (20 + 24 * c_w) * γ :=
          mul_le_mul_of_nonneg_right (by linarith) hγ.le
        linarith
      have hcw12 : 2 * c_w * γ ≤ 1 / 12 := by
        have : 24 * c_w * γ ≤ (20 + 24 * c_w) * γ :=
          mul_le_mul_of_nonneg_right (by linarith) hγ.le
        linarith
      have hgap_V : (1 / 4) * Real.logb 2 U + (1 / 12) * Real.logb 2 V ≤
          (1 / 2) * Real.logb 2 V - Real.logb 2 ((U : ℝ) / (n : ℝ)) := by
        rw [Real.logb_div hU_pos.ne' hn_pos.ne']
        linarith
      have h1 : 7 * m ≤ γ * m * Real.logb 2 U := by
        have h7 : 7 ≤ γ * Real.logb 2 U := by linarith
        have := mul_le_mul_of_nonneg_right h7 hm_nn; linarith
      have h2 : 2 * m * t ≤ γ * m * Real.logb 2 U := by
        have h2t : 2 * t ≤ γ * Real.logb 2 U := by linarith
        have := mul_le_mul_of_nonneg_left h2t hm_nn; linarith
      have h3 : γ * m * (w : ℝ) ≤ (2 * c_w * γ) * (m * Real.logb 2 V) := by
        have := mul_le_mul_of_nonneg_left hw_le (show 0 ≤ γ * m by positivity); linarith
      have h4 : (5 * γ) * (m * Real.logb 2 U) ≤ (1 / 4) * (m * Real.logb 2 U) :=
        mul_le_mul_of_nonneg_right hγ20 (by positivity)
      have h5 : (2 * c_w * γ) * (m * Real.logb 2 V) ≤ (1 / 12) * (m * Real.logb 2 V) :=
        mul_le_mul_of_nonneg_right hcw12 (mul_nonneg hm_nn (by linarith))
      have h6 := mul_le_mul_of_nonneg_left hgap_V hm_nn
      linarith
    exact outer_lemma_largeVal_insertQueryDelete
      (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV hspace hspace T hcorr hγ
      ht hℓ ht_stop hF_lo hF_hi hR_outer hbud

private theorem exists_gamma_query {α c_w : ℝ} (hα : 0 < α) (hcw : 0 ≤ c_w) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ (20 + 24 * c_w) * γ = α / (1 + α) := by
  refine ⟨α / ((20 + 24 * c_w) * (1 + α)), by positivity, ?_, ?_⟩
  · have h1 : α / ((20 + 24 * c_w) * (1 + α)) ≤ (1 + α) / (1 * (1 + α)) :=
      div_le_div₀ (by positivity) (by linarith) (by positivity)
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    exact h1.trans_eq (by field_simp)
  · have : (20 + 24 * c_w) ≠ 0 := by positivity
    have : (1 + α) ≠ 0 := by positivity
    field_simp

private theorem exists_gamma_update {α_V c_w : ℝ} (hα_V : 0 < α_V) (hcw : 0 ≤ c_w) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ (5 + c_w) * γ ≤ min (1 / 4) (α_V / 16) := by
  set η := min (1 / 4) (α_V / 16)
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨min (1 / 20) (η / (5 + c_w)), by positivity,
    (min_le_left _ _).trans (by norm_num), ?_⟩
  exact (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)).trans_eq
    (mul_div_cancel₀ _ (by positivity))

private theorem le_expectedSeqProbes_query_of_det {U V n cells w : ℕ}
    (hU : 2 * n ≤ U) (hV : 1 ≤ V) {B : ℝ}
    (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
      ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
        ops ((P.runSeq ops).map Prod.fst))
    (hdet : ∀ {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w},
      (∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
        (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) →
      B ≤ ∑' ops, (insertQueryDeleteDist U V n hU hV ops).toReal * (D_det.seqProbes ops : ℝ)) :
    ENNReal.ofReal B ≤
      ∑' ops, insertQueryDeleteDist U V n hU hV ops * P.expectedSeqProbes ops := by
  obtain ⟨D_det, _, hcorr_det, hle_exp⟩ :=
    exists_det_indexedScheme_insertQueryDeleteDist hU hV P hcorr
  exact (ofReal_le_tsum_seqProbes_of_toReal_le _ D_det (hdet hcorr_det)).trans hle_exp

private theorem le_expectedSeqProbes_update_of_det {U V n cells w : ℕ}
    (hU : 2 * n ≤ U) (hV : 1 ≤ V) {B : ℝ}
    (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
      ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
        ops ((P.runSeq ops).map Prod.fst))
    (hdet : ∀ {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w},
      (∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
        (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2) →
      B ≤ ∑' ops, (insertDeleteDist U V n hU hV ops).toReal * (D_det.seqProbes ops : ℝ)) :
    ENNReal.ofReal B ≤
      ∑' ops, insertDeleteDist U V n hU hV ops * P.expectedSeqProbes ops := by
  obtain ⟨D_det, _, hcorr_det, hle_exp⟩ :=
    exists_det_indexedScheme_insertDeleteDist hU hV P hcorr
  exact (ofReal_le_tsum_seqProbes_of_toReal_le _ D_det (hdet hcorr_det)).trans hle_exp

private theorem iterLog_logStar_space_le {U V n cells w : ℕ} {c_R : ℝ} (hn : 2 ≤ n)
    (hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + c_R * (n : ℝ)) :
    1 ≤ Nat.logStar n ∧
      ((cells * w : ℕ) : ℝ) ≤
        benchmarkBits U V n +
          c_R * (n : ℝ) * ((max (Nat.iterLog (Nat.logStar n) n) 1 : ℕ) : ℝ) := by
  have hk1 : 1 ≤ Nat.logStar n := by
    have : Nat.logStar 2 = 1 := by decide
    exact this ▸ Nat.logStar_mono hn
  have hiter1 : max (Nat.iterLog (Nat.logStar n) n) 1 = 1 := by
    have hle : Nat.iterLog (Nat.logStar n) n ≤ 1 :=
      (Nat.iterLog_anti_left n (Nat.floorLogStar_le_logStar n)).trans
        (Nat.iterLog_floorLogStar_le_one n)
    omega
  exact ⟨hk1, by rw [hiter1, Nat.cast_one, mul_one]; exact hspace⟩

private theorem combine_iterLogStar_and_sublinear {c₁ c₂ L R E : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (hL_nn : 0 ≤ L) (hE_nn : 0 ≤ E)
    (hb₁ : c₁ * (n : ℝ) * L ≤ E)
    (hb₂ : R ≤ (n : ℝ) → c₂ * (n : ℝ) * Real.logb 2 ((n : ℝ) / max R 1) ≤ E) :
    (min c₁ c₂ / 2) * (n : ℝ) * (L + max 0 (Real.logb 2 ((n : ℝ) / max R 1))) ≤ E := by
  have hm₁ : min c₁ c₂ * (n : ℝ) * L ≤ E :=
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_left c₁ c₂) (Nat.cast_nonneg n)) hL_nn).trans hb₁
  have hm₂ : min c₁ c₂ * (n : ℝ) * max 0 (Real.logb 2 ((n : ℝ) / max R 1)) ≤ E := by
    by_cases hRn : R ≤ (n : ℝ)
    · have hdiv1 : 1 ≤ (n : ℝ) / max R 1 :=
        (one_le_div (lt_of_lt_of_le zero_lt_one (_root_.le_max_right R 1))).mpr
          (max_le hRn (by exact_mod_cast (show 1 ≤ n by omega)))
      have hlog_nn : 0 ≤ Real.logb 2 ((n : ℝ) / max R 1) := Real.logb_nonneg (by norm_num) hdiv1
      rw [max_eq_right hlog_nn]
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (min_le_right c₁ c₂) (Nat.cast_nonneg n)) hlog_nn).trans
        (hb₂ hRn)
    · push Not at hRn
      have hdiv_le : (n : ℝ) / max R 1 ≤ 1 :=
        (div_le_one (lt_of_lt_of_le zero_lt_one (_root_.le_max_right R 1))).mpr
          (hRn.le.trans (_root_.le_max_left R 1))
      have hlog_np : Real.logb 2 ((n : ℝ) / max R 1) ≤ 0 :=
        Real.logb_nonpos (by norm_num) (div_nonneg (Nat.cast_nonneg n)
          (le_trans zero_le_one (_root_.le_max_right R 1))) hdiv_le
      rw [max_eq_left hlog_np, mul_zero]
      exact hE_nn
  linarith

private theorem det_expectedSeqProbes_mode_ge_iterLog (withQueries : Bool)
    {γ c_R : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hcR : 0 ≤ c_R) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n k cells w : ℕ} (_hn : 2 ≤ n) (hU : 2 * n ≤ U) (hV : 1 ≤ V)
        (_hk_lo : 1 ≤ k) (_hk_hi : k ≤ Nat.logStar n)
        (_hspace : ((cells * w : ℕ) : ℝ) ≤
          benchmarkBits U V n + c_R * (n : ℝ) * ((max (Nat.iterLog k n) 1 : ℕ) : ℝ))
        {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (modeHorizon withQueries n + 1),
          (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2)
        (_hnode : ∀ {R t : ℝ} (_hspace_R : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
          (T : MetaTree) (_ht : 0 < t) {ℓ b : ℕ} (_hℓ : 1 ≤ ℓ)
          (_ht_stop : T.nodeStop (ℓ + 1) b ≤ n)
          (_hF_lo : 2 ^ 64 ≤ T.fanout (ℓ + 1))
          (_h11 : 11 / γ ≤ Real.logb 2 U)
          (_ht_hi : 6 * t ≤ γ * Real.logb 2 U)
          (_hm_lo : (n : ℝ) ^ (1 - γ / 2) ≤ (T.blockSize ℓ : ℝ))
          (_hF_hi : (T.fanout (ℓ + 1) : ℝ) ≤ (γ / 2) * Real.logb 2 U)
          (_hR_out : 100 * R ≤ (T.blockSize (ℓ + 1) : ℝ) * Real.logb 2 (T.fanout (ℓ + 1)))
          (_hR_in : R ≤ (γ / 2) * (T.blockSize ℓ : ℝ) * Real.logb 2 U),
          (γ / 100) * (T.blockSize (ℓ + 1) : ℝ) ≤
              ∑' ops, (modeDist withQueries U V n hU hV ops).toReal *
                (T.nodeCost D_det n (modeStride withQueries) ops ℓ b : ℝ) ∨
            (1 / 16) * (T.blockSize (ℓ + 1) : ℝ) * t ≤
              ∑' ops, (modeDist withQueries U V n hU hV ops).toReal *
                (T.nodeProbes D_det n (modeStride withQueries) ops (ℓ + 1) b : ℝ)),
        c * (n : ℝ) * (k : ℝ) ≤
          ∑' ops, (modeDist withQueries U V n hU hV ops).toReal * (D_det.seqProbes ops : ℝ) := by
  generalize hc_tree : max 8 (Nat.ceil (808 * (c_R + 1) / γ)) = c_tree
  have hct8 : 8 ≤ c_tree := hc_tree ▸ _root_.le_max_left 8 _
  have hct_ceil : 808 * (c_R + 1) / γ ≤ (c_tree : ℝ) :=
    (Nat.le_ceil _).trans (by rw [← hc_tree]; exact_mod_cast _root_.le_max_right 8 _)
  clear hc_tree
  generalize hs_off : Nat.logStar (max 71 (4 * c_tree * (4 * c_tree + 71))) + 2 = s_off
  generalize hM_exp : max 32 (max (Nat.ceil (11 / γ))
    (2 * (Nat.ceil (4 / γ) + 1) * (2 * (Nat.ceil (4 / γ) + 1) + 2))) = M_exp
  have hM32 : 32 ≤ M_exp := hM_exp ▸ _root_.le_max_left 32 _
  have hM11 : Nat.ceil (11 / γ) ≤ M_exp :=
    hM_exp ▸ (_root_.le_max_left _ _).trans (_root_.le_max_right 32 _)
  have hMrpow : 2 * (Nat.ceil (4 / γ) + 1) * (2 * (Nat.ceil (4 / γ) + 1) + 2) ≤ M_exp :=
    hM_exp ▸ (_root_.le_max_right _ _).trans (_root_.le_max_right 32 _)
  clear hM_exp
  generalize hN₀ : 2 ^ M_exp = N₀
  generalize hK_cap : max (2 * s_off + 6) (Nat.logStar N₀ + 1) = K_cap
  have hK_pos : 1 ≤ K_cap := by rw [← hK_cap]; exact le_trans (by omega) (_root_.le_max_left _ _)
  refine ⟨min (1 / (2 * (K_cap : ℝ))) (γ / 1600), by positivity, ?_⟩
  intro U V n k cells w hn hU hV hk_lo hk_hi hspace D_det hcorr hnode
  generalize hc_def : min (1 / (2 * (K_cap : ℝ))) (γ / 1600) = c
  have hc1 : c ≤ 1 / (2 * (K_cap : ℝ)) := hc_def ▸ min_le_left _ _
  have hc2 : c ≤ γ / 1600 := hc_def ▸ min_le_right _ _
  clear hc_def
  have hnU : n ≤ U := Nat.le_trans (Nat.le_mul_of_pos_left n (by decide)) hU
  by_cases hbig : N₀ ≤ n ∧ 2 * s_off + 6 ≤ k
  · obtain ⟨hn_N₀, hk_s⟩ := hbig
    have hpow_N₀ : 2 ^ M_exp ≤ n := hN₀ ▸ hn_N₀
    have hfls : 4 ≤ Nat.floorLogStar n :=
      (Nat.four_le_floorLogStar_two_pow (le_rfl : 32 ≤ 32)).trans
        (Nat.floorLogStar_mono ((Nat.pow_le_pow_right Nat.two_pos hM32).trans hpow_N₀))
    generalize hk' : min k (Nat.floorLogStar n - 1) = k'
    obtain ⟨hH_ge, hk_r, hH1_logU, hmax_le, hn_le_b1, hlevels⟩ :=
      iterLog_tree_bounds hγ hγ1 hcR hct8 hct_ceil hs_off.symm hn hnU hfls hk_s hk_hi hk'.symm
    clear hs_off hK_cap hN₀
    set T := iterLogMetaTree n k' c_tree
    set H := k' - s_off
    set R := c_R * (n : ℝ) * (Nat.iterLog k' n : ℝ)
    set t := ((H - 1 : ℕ) : ℝ) * (4 * γ / 25)
    have hspace_R : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R :=
      hspace.trans (by dsimp [R]; gcongr)
    have h11_logU : 11 / γ ≤ Real.logb 2 U := by
      have hp : 2 ^ Nat.ceil (11 / γ) ≤ U :=
        ((Nat.pow_le_pow_right Nat.two_pos hM11).trans hpow_N₀).trans hnU
      have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity)
        (show (2 : ℝ) ^ Nat.ceil (11 / γ) ≤ (U : ℝ) by exact_mod_cast hp)
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hl
      exact (Nat.le_ceil _).trans hl
    have ht_pos : 0 < t := by
      dsimp [t]
      have : (0 : ℝ) < ((H - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < H - 1 by omega)
      positivity
    have ht_hi : 6 * t ≤ γ * Real.logb 2 U := by
      dsimp [t]
      calc 6 * (((H - 1 : ℕ) : ℝ) * (4 * γ / 25))
          ≤ 1 * (γ * ((H - 1 : ℕ) : ℝ)) := by
            have : (0 : ℝ) ≤ γ * ((H - 1 : ℕ) : ℝ) := by positivity
            linarith
        _ = γ * ((H - 1 : ℕ) : ℝ) := one_mul _
        _ ≤ γ * Real.logb 2 U := mul_le_mul_of_nonneg_left hH1_logU hγ.le
    have hm_lo_1 : (n : ℝ) ^ (1 - γ / 2) ≤ (T.blockSize 1 : ℝ) := by
      have hlog_rpow := logb_le_rpow_of_ge_pow hγ
        ((Nat.pow_le_pow_right Nat.two_pos hMrpow).trans hpow_N₀)
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hrpow_eq : (n : ℝ) ^ (1 - γ / 2) * (n : ℝ) ^ (γ / 2) = (n : ℝ) := by
        rw [← Real.rpow_add hn_pos]; ring_nf; exact Real.rpow_one _
      have hlogn_pos : 0 < Real.logb 2 n :=
        Real.logb_pos (by norm_num) (by exact_mod_cast (show 1 < n by omega))
      have hm1 : (n : ℝ) ^ (1 - γ / 2) * Real.logb 2 n ≤ (T.blockSize 1 : ℝ) * Real.logb 2 n := by
        calc (n : ℝ) ^ (1 - γ / 2) * Real.logb 2 n
            ≤ (n : ℝ) ^ (1 - γ / 2) * (n : ℝ) ^ (γ / 2) :=
              mul_le_mul_of_nonneg_left hlog_rpow (Real.rpow_nonneg hn_pos.le _)
          _ = (n : ℝ) := hrpow_eq
          _ ≤ (T.blockSize 1 : ℝ) * Real.logb 2 n := hn_le_b1
      exact le_of_mul_le_mul_right hm1 hlogn_pos
    have htree := det_expectedSeqProbes_ge_of_outer_tree withQueries hU hV T
      (iterLogMetaTree_horizon n k' c_tree) hH_ge
      (fun ℓ hℓ => (hlevels ℓ hℓ).1) hγ (D_det := D_det) fun ℓ hℓ b hb => by
        obtain ⟨_, hF_lo, hF_hi, hR_out, hR_in⟩ := hlevels ℓ hℓ
        have hℓ_ge : 1 ≤ ℓ := (Finset.mem_Ico.mp hℓ).1
        have hm_lo : (n : ℝ) ^ (1 - γ / 2) ≤ (T.blockSize ℓ : ℝ) :=
          hm_lo_1.trans (by exact_mod_cast T.blockSize_strictMono.monotone hℓ_ge)
        have ht_stop : T.nodeStop (ℓ + 1) b ≤ n :=
          (T.nodeStop_le_horizon hb).trans_eq (iterLogMetaTree_horizon n k' c_tree)
        exact hnode hspace_R T ht_pos hℓ_ge ht_stop hF_lo h11_logU ht_hi hm_lo hF_hi hR_out hR_in
    refine (?_ : c * (n : ℝ) * (k : ℝ) ≤ ((H - 1 : ℕ) : ℝ) * (γ / 400) * (n : ℝ)).trans htree
    calc c * (n : ℝ) * (k : ℝ)
        ≤ (γ / 1600) * (n : ℝ) * (k : ℝ) := by gcongr
      _ = ((k : ℝ) / 4) * (γ / 400) * (n : ℝ) := by ring
      _ ≤ ((H - 1 : ℕ) : ℝ) * (γ / 400) * (n : ℝ) := by gcongr
  · have hk_le_K : k ≤ K_cap := by
      rw [← hK_cap]
      by_cases hn_lt : n < N₀
      · exact (hk_hi.trans (Nat.logStar_mono hn_lt.le)).trans
          ((Nat.le_succ _).trans (_root_.le_max_right _ _))
      · have hn_ge : N₀ ≤ n := Nat.not_lt.mp hn_lt
        have hk_lt : k < 2 * s_off + 6 :=
          Nat.lt_of_not_ge fun hge => hbig ⟨hn_ge, hge⟩
        exact hk_lt.le.trans (_root_.le_max_left _ _)
    clear hs_off hK_cap hN₀
    have hlin := det_expectedSeqProbes_ge_linear withQueries hU hV (D_det := D_det) hcorr
    refine (?_ : c * (n : ℝ) * (k : ℝ) ≤ (n : ℝ) / 2).trans hlin
    have hK_pos_r : (0 : ℝ) < (K_cap : ℝ) := by exact_mod_cast hK_pos
    have hk_r : (k : ℝ) ≤ (K_cap : ℝ) := by exact_mod_cast hk_le_K
    have hck : c * (k : ℝ) ≤ 1 / 2 := by
      calc c * (k : ℝ) ≤ (1 / (2 * (K_cap : ℝ))) * (K_cap : ℝ) :=
            mul_le_mul hc1 hk_r (Nat.cast_nonneg k) (by positivity)
        _ = 1 / 2 := by field_simp
    calc c * (n : ℝ) * (k : ℝ) = (c * (k : ℝ)) * (n : ℝ) := by ring
      _ ≤ (1 / 2) * (n : ℝ) := mul_le_mul_of_nonneg_right hck (Nat.cast_nonneg n)
      _ = (n : ℝ) / 2 := by ring

private theorem fanout_geomMetaTree_of_two_le (n m₁_half : ℕ) {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    (geomMetaTree n m₁_half).fanout ℓ = 2 ^ 64 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hℓ
  rw [Nat.add_comm 2 d, geomMetaTree_fanout]
  rfl

private theorem height_geomMetaTree_le_logb {n : ℕ} (hn : 2 ≤ n) (m₁_half : ℕ) :
    ((geomMetaTree n m₁_half).height : ℝ) ≤ Real.logb 2 n := by
  set T := geomMetaTree n m₁_half
  set H := T.height
  rcases Nat.eq_zero_or_pos H with h0 | hpos
  · rw [h0, Nat.cast_zero]
    exact Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ n by omega))
  · have hb : T.blockSize H ≤ n :=
      ((le_height_geomMetaTree_iff hn m₁_half H).mp le_rfl).trans (Nat.div_le_self n 2)
    have hpow : (2 : ℝ) ^ H ≤ (n : ℝ) := by
      exact_mod_cast (T.two_pow_le_blockSize H).trans hb
    have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hpow
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hl

private theorem det_expectedSeqProbes_mode_ge_sublinear (withQueries : Bool)
    {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} {R : ℝ} (_hn : 2 ≤ n) (hU : 2 * n ≤ U) (hV : 1 ≤ V)
        (_hR_hi : R ≤ (n : ℝ))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
        {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (modeHorizon withQueries n + 1),
          (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2)
        (_hnode : ∀ {R' t : ℝ} (_hspace_R : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R')
          (T : MetaTree) (_ht : 0 < t) {ℓ b : ℕ} (_hℓ : 1 ≤ ℓ)
          (_ht_stop : T.nodeStop (ℓ + 1) b ≤ n)
          (_hF_lo : 2 ^ 64 ≤ T.fanout (ℓ + 1))
          (_h11 : 11 / γ ≤ Real.logb 2 U)
          (_ht_hi : 6 * t ≤ γ * Real.logb 2 U)
          (_hm_lo : (n : ℝ) ^ (1 - γ / 2) ≤ (T.blockSize ℓ : ℝ))
          (_hF_hi : (T.fanout (ℓ + 1) : ℝ) ≤ (γ / 2) * Real.logb 2 U)
          (_hR_out : 100 * R' ≤ (T.blockSize (ℓ + 1) : ℝ) * Real.logb 2 (T.fanout (ℓ + 1)))
          (_hR_in : R' ≤ (γ / 2) * (T.blockSize ℓ : ℝ) * Real.logb 2 U),
          (γ / 100) * (T.blockSize (ℓ + 1) : ℝ) ≤
              ∑' ops, (modeDist withQueries U V n hU hV ops).toReal *
                (T.nodeCost D_det n (modeStride withQueries) ops ℓ b : ℝ) ∨
            (1 / 16) * (T.blockSize (ℓ + 1) : ℝ) * t ≤
              ∑' ops, (modeDist withQueries U V n hU hV ops).toReal *
                (T.nodeProbes D_det n (modeStride withQueries) ops (ℓ + 1) b : ℝ)),
        c * (n : ℝ) * Real.logb 2 ((n : ℝ) / max R 1) ≤
          ∑' ops, (modeDist withQueries U V n hU hV ops).toReal * (D_det.seqProbes ops : ℝ) := by
  generalize hM_exp : max (Nat.ceil (2 * ((2 ^ 64 : ℕ) : ℝ) / γ)) (Nat.ceil (11 / γ)) = M_exp
  have hM_fan : ((2 ^ 64 : ℕ) : ℝ) ≤ (γ / 2) * (M_exp : ℝ) := by
    have h1 : 2 * ((2 ^ 64 : ℕ) : ℝ) / γ ≤ (M_exp : ℝ) :=
      (Nat.le_ceil _).trans (by rw [← hM_exp]; exact_mod_cast _root_.le_max_left _ _)
    calc ((2 ^ 64 : ℕ) : ℝ)
      _ = (2 * ((2 ^ 64 : ℕ) : ℝ) / γ) * (γ / 2) := by
        have : γ ≠ 0 := ne_of_gt hγ
        field_simp
      _ ≤ (M_exp : ℝ) * (γ / 2) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (γ / 2) * (M_exp : ℝ) := mul_comm _ _
  have hM11 : 11 / γ ≤ (M_exp : ℝ) :=
    (Nat.le_ceil _).trans (by rw [← hM_exp]; exact_mod_cast _root_.le_max_right _ _)
  clear hM_exp
  generalize hN₀ : 2 ^ M_exp = N₀
  generalize hK_log : max ((M_exp : ℝ) + 1) (268 / γ) = K_log
  have hK_pos : 0 < K_log := by
    have : 0 < 268 / γ := by positivity
    exact this.trans_le (hK_log ▸ _root_.le_max_right _ _)
  have hK_M : (M_exp : ℝ) ≤ K_log :=
    (by linarith : (M_exp : ℝ) ≤ (M_exp : ℝ) + 1).trans (hK_log ▸ _root_.le_max_left _ _)
  have hK_γ : 134 / γ ≤ K_log :=
    (div_le_div_of_nonneg_right (by norm_num) hγ.le).trans (hK_log ▸ _root_.le_max_right _ _)
  clear hK_log
  refine ⟨min (1 / (2 * K_log)) (γ ^ 2 / 104800), by positivity, ?_⟩
  intro U V n cells w R hn hU hV hR_hi hspace D_det hcorr hnode
  generalize hc_def : min (1 / (2 * K_log)) (γ ^ 2 / 104800) = c
  have hc1 : c ≤ 1 / (2 * K_log) := hc_def ▸ min_le_left _ _
  have hc2 : c ≤ γ ^ 2 / 104800 := hc_def ▸ min_le_right _ _
  clear hc_def
  set R₁ := max R 1
  have hR1_ge : 1 ≤ R₁ := _root_.le_max_right R 1
  have hR_le_R1 : R ≤ R₁ := _root_.le_max_left R 1
  have hR1_le_n : R₁ ≤ (n : ℝ) :=
    max_le hR_hi (by exact_mod_cast (show 1 ≤ n by clear hM_fan; omega))
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by clear hM_fan; omega)
  have hdiv_ge1 : 1 ≤ (n : ℝ) / R₁ := (one_le_div (by positivity)).mpr hR1_le_n
  have hlog_div_nn : 0 ≤ Real.logb 2 ((n : ℝ) / R₁) := Real.logb_nonneg (by norm_num) hdiv_ge1
  generalize hm₁ : max (Nat.ceil R₁) (Nat.ceil ((n : ℝ) ^ (1 - γ / 2))) = m₁_half
  have hm₁_R : R₁ ≤ (m₁_half : ℝ) :=
    (Nat.le_ceil R₁).trans (by rw [← hm₁]; exact_mod_cast _root_.le_max_left _ _)
  have hm₁_n : (n : ℝ) ^ (1 - γ / 2) ≤ (m₁_half : ℝ) :=
    (Nat.le_ceil _).trans (by rw [← hm₁]; exact_mod_cast _root_.le_max_right _ _)
  have hm₁_pos : 1 ≤ m₁_half := by
    have : 1 ≤ Nat.ceil R₁ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
    exact this.trans (hm₁ ▸ _root_.le_max_left _ _)
  have hm₁_ub : (m₁_half : ℝ) ≤ 2 * max R₁ ((n : ℝ) ^ (1 - γ / 2)) := by
    have hcR1 : (Nat.ceil R₁ : ℝ) ≤ 2 * R₁ := by
      have hlt := (Nat.ceil_lt_add_one (show 0 ≤ R₁ by positivity)).le
      exact hlt.trans (by linarith [hR1_ge, _root_.le_max_left R₁ ((n : ℝ) ^ (1 - γ / 2))])
    have hcn : (Nat.ceil ((n : ℝ) ^ (1 - γ / 2)) : ℝ) ≤ 2 * (n : ℝ) ^ (1 - γ / 2) := by
      have hr1 : 1 ≤ (n : ℝ) ^ (1 - γ / 2) :=
        Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by clear hM_fan; omega)) (by linarith)
      have hlt := (Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) ^ (1 - γ / 2) by positivity)).le
      linarith
    rw [← hm₁, Nat.cast_max]
    exact max_le
      ((by linarith : (Nat.ceil R₁ : ℝ) ≤ 2 * R₁).trans
        (mul_le_mul_of_nonneg_left (_root_.le_max_left _ _) (by norm_num)))
      (hcn.trans (mul_le_mul_of_nonneg_left (_root_.le_max_right _ _) (by norm_num)))
  clear hm₁
  set T := geomMetaTree n m₁_half
  set H := T.height
  have hlog_H : Real.logb 2 ((n : ℝ) / R₁) ≤ (2 / γ) * (3 + 64 * (H : ℝ)) := by
    have hlt_nat := lt_mul_pow_height_geomMetaTree n m₁_half
    rw [max_eq_right hm₁_pos] at hlt_nat
    have hle_r : (n : ℝ) ≤ 4 * (m₁_half : ℝ) * ((2 ^ 64 : ℕ) : ℝ) ^ H := by
      exact_mod_cast hlt_nat.le
    have hpow_eq : (8 : ℝ) * (((2 ^ 64 : ℕ) : ℝ) ^ H) = (2 : ℝ) ^ (3 + 64 * H) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num,
        ← pow_add]
    have hle_max : (n : ℝ) ≤ max R₁ ((n : ℝ) ^ (1 - γ / 2)) * (2 : ℝ) ^ (3 + 64 * H) := by
      calc (n : ℝ)
          ≤ 4 * (2 * max R₁ ((n : ℝ) ^ (1 - γ / 2))) * (((2 ^ 64 : ℕ) : ℝ) ^ H) :=
            hle_r.trans (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hm₁_ub (by norm_num)) (by positivity))
        _ = max R₁ ((n : ℝ) ^ (1 - γ / 2)) * ((8 : ℝ) * (((2 ^ 64 : ℕ) : ℝ) ^ H)) := by ring
        _ = max R₁ ((n : ℝ) ^ (1 - γ / 2)) * (2 : ℝ) ^ (3 + 64 * H) := by rw [hpow_eq]
    rcases le_total ((n : ℝ) ^ (1 - γ / 2)) R₁ with hmax | hmax
    · rw [max_eq_left hmax] at hle_max
      have hdiv_pow : (n : ℝ) / R₁ ≤ (2 : ℝ) ^ (3 + 64 * H) :=
        (div_le_iff₀ (by positivity)).mpr (by linarith)
      have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hdiv_pow
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one,
        Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hl
      have h2γ : 1 ≤ 2 / γ := (one_le_div hγ).mpr (by linarith)
      exact hl.trans ((one_mul _).symm.trans_le (mul_le_mul_of_nonneg_right h2γ (by positivity)))
    · rw [max_eq_right hmax] at hle_max
      have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hn_pos hle_max
      rw [Real.logb_mul (by positivity) (by positivity),
        Real.logb_rpow_eq_mul_logb_of_pos hn_pos, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one,
        Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hl
      have hγ_log : (γ / 2) * Real.logb 2 n ≤ 3 + 64 * (H : ℝ) := by linarith
      have hlogn : Real.logb 2 n ≤ (2 / γ) * (3 + 64 * (H : ℝ)) := by
        have hpos : 0 < γ / 2 := by positivity
        have hd : Real.logb 2 n ≤ (3 + 64 * (H : ℝ)) / (γ / 2) :=
          (le_div_iff₀ hpos).mpr (by rw [mul_comm]; exact hγ_log)
        have hid : (3 + 64 * (H : ℝ)) / (γ / 2) = (2 / γ) * (3 + 64 * (H : ℝ)) := by
          field_simp
        exact hd.trans_eq hid
      have hdiv_le_n : (n : ℝ) / R₁ ≤ (n : ℝ) := div_le_self hn_pos.le hR1_ge
      exact (Real.logb_le_logb_of_le (by norm_num) (by positivity) hdiv_le_n).trans hlogn
  have hnU : n ≤ U := Nat.le_trans (Nat.le_mul_of_pos_left n (by decide)) hU
  by_cases hbig : N₀ ≤ n ∧ 2 ≤ H
  · obtain ⟨hn_N₀, hH_ge⟩ := hbig
    have hpow_N₀ : 2 ^ M_exp ≤ n := hN₀ ▸ hn_N₀
    clear hN₀
    have hM_logU : (M_exp : ℝ) ≤ Real.logb 2 U := by
      have hp : (2 : ℝ) ^ M_exp ≤ (U : ℝ) := by exact_mod_cast hpow_N₀.trans hnU
      have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hp
      rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hl
    have h11_logU : 11 / γ ≤ Real.logb 2 U := hM11.trans hM_logU
    have hfan_U : ((2 ^ 64 : ℕ) : ℝ) ≤ (γ / 2) * Real.logb 2 U :=
      hM_fan.trans (mul_le_mul_of_nonneg_left hM_logU (by positivity))
    clear hM_fan
    have hH_logU : ((H - 1 : ℕ) : ℝ) ≤ Real.logb 2 U := by
      have h1 : ((H - 1 : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast Nat.sub_le H 1
      exact (h1.trans (height_geomMetaTree_le_logb hn m₁_half)).trans
        (Real.logb_le_logb_of_le (by norm_num) hn_pos (by exact_mod_cast hnU))
    set t := ((H - 1 : ℕ) : ℝ) * (4 * γ / 25)
    have ht_pos : 0 < t := by
      dsimp [t]
      have : (0 : ℝ) < ((H - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < H - 1 by omega)
      positivity
    have ht_hi : 6 * t ≤ γ * Real.logb 2 U := by
      dsimp [t]
      calc 6 * (((H - 1 : ℕ) : ℝ) * (4 * γ / 25))
          ≤ 1 * (γ * ((H - 1 : ℕ) : ℝ)) := by
            have : (0 : ℝ) ≤ γ * ((H - 1 : ℕ) : ℝ) := by positivity
            linarith
        _ = γ * ((H - 1 : ℕ) : ℝ) := one_mul _
        _ ≤ γ * Real.logb 2 U := mul_le_mul_of_nonneg_left hH_logU hγ.le
    have hspace_R1 : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R₁ :=
      hspace.trans (by linarith)
    have hb1_ge : 2 * (m₁_half : ℝ) ≤ (T.blockSize 1 : ℝ) := by
      have hb1 := blockSize_geomMetaTree n m₁_half le_rfl
      rw [Nat.sub_self, pow_zero, mul_one, max_eq_right hm₁_pos] at hb1
      exact_mod_cast hb1.symm.le
    have htree := det_expectedSeqProbes_ge_of_outer_tree withQueries hU hV T
      (geomMetaTree_horizon n m₁_half) hH_ge
      (fun ℓ hℓ => (le_height_geomMetaTree_iff hn m₁_half (ℓ + 1)).mp (Finset.mem_Ico.mp hℓ).2)
      hγ (D_det := D_det) fun ℓ hℓ b hb => by
        have hℓ_ge : 1 ≤ ℓ := (Finset.mem_Ico.mp hℓ).1
        have hfan : T.fanout (ℓ + 1) = 2 ^ 64 :=
          fanout_geomMetaTree_of_two_le n m₁_half (by omega)
        have hF_lo : 2 ^ 64 ≤ T.fanout (ℓ + 1) := by rw [hfan]
        have hF_hi : (T.fanout (ℓ + 1) : ℝ) ≤ (γ / 2) * Real.logb 2 U := by
          rw [hfan]; exact hfan_U
        have hbℓ_ge : 2 * (m₁_half : ℝ) ≤ (T.blockSize ℓ : ℝ) :=
          hb1_ge.trans (by exact_mod_cast T.blockSize_strictMono.monotone hℓ_ge)
        have hm_lo : (n : ℝ) ^ (1 - γ / 2) ≤ (T.blockSize ℓ : ℝ) := by
          have : 0 ≤ (m₁_half : ℝ) := Nat.cast_nonneg _
          linarith
        have hR_outer : 100 * R₁ ≤ (T.blockSize (ℓ + 1) : ℝ) * Real.logb 2 (T.fanout (ℓ + 1)) := by
          have hb1_next : 2 * R₁ ≤ (T.blockSize (ℓ + 1) : ℝ) :=
            (mul_le_mul_of_nonneg_left hm₁_R (by norm_num)).trans
              (hb1_ge.trans (by exact_mod_cast T.blockSize_strictMono.monotone (by omega)))
          have hlog_fan : Real.logb 2 (T.fanout (ℓ + 1)) = 64 := by
            rw [hfan, Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
              Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one, Nat.cast_ofNat]
          rw [hlog_fan]
          linarith
        have hR_in : R₁ ≤ (γ / 2) * (T.blockSize ℓ : ℝ) * Real.logb 2 U := by
          have hγU : 1 ≤ (γ / 2) * Real.logb 2 U := by
            have := (div_le_iff₀ hγ).mp h11_logU; linarith
          have hmR : R₁ ≤ (T.blockSize ℓ : ℝ) := by
            have : 0 ≤ (m₁_half : ℝ) := Nat.cast_nonneg _
            linarith
          calc R₁ = 1 * R₁ := (one_mul R₁).symm
            _ ≤ ((γ / 2) * Real.logb 2 U) * (T.blockSize ℓ : ℝ) :=
              mul_le_mul hγU hmR (by positivity) (by positivity)
            _ = (γ / 2) * (T.blockSize ℓ : ℝ) * Real.logb 2 U := by ring
        have ht_stop : T.nodeStop (ℓ + 1) b ≤ n :=
          (T.nodeStop_le_horizon hb).trans_eq (geomMetaTree_horizon n m₁_half)
        exact hnode hspace_R1 T ht_pos hℓ_ge ht_stop hF_lo h11_logU ht_hi hm_lo hF_hi hR_outer
          hR_in
    refine (?_ : c * (n : ℝ) * Real.logb 2 ((n : ℝ) / R₁) ≤
      ((H - 1 : ℕ) : ℝ) * (γ / 400) * (n : ℝ)).trans htree
    have hH_sub : (H : ℝ) - 1 = ((H - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    have hH1_ge1 : 1 ≤ ((H - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ H - 1 by omega)
    have h3_64 : 3 + 64 * (H : ℝ) ≤ 131 * ((H - 1 : ℕ) : ℝ) := by linarith
    have hlog_H1 : Real.logb 2 ((n : ℝ) / R₁) ≤ (262 / γ) * ((H - 1 : ℕ) : ℝ) := by
      calc Real.logb 2 ((n : ℝ) / R₁)
          ≤ (2 / γ) * (3 + 64 * (H : ℝ)) := hlog_H
        _ ≤ (2 / γ) * (131 * ((H - 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left h3_64 (by positivity)
        _ = (262 / γ) * ((H - 1 : ℕ) : ℝ) := by ring
    calc c * (n : ℝ) * Real.logb 2 ((n : ℝ) / R₁)
        ≤ (γ ^ 2 / 104800) * (n : ℝ) * ((262 / γ) * ((H - 1 : ℕ) : ℝ)) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_right hc2 hn_pos.le)
            hlog_H1 hlog_div_nn (by positivity)
      _ = ((H - 1 : ℕ) : ℝ) * (γ / 400) * (n : ℝ) := by field_simp; ring
  · clear hM_fan
    have hlog_le_K : Real.logb 2 ((n : ℝ) / R₁) ≤ K_log := by
      by_cases hn_lt : n < N₀
      · have hdiv_le_N : (n : ℝ) / R₁ ≤ (2 : ℝ) ^ M_exp := by
          have hn_le : (n : ℝ) ≤ (2 : ℝ) ^ M_exp := by
            have : n ≤ 2 ^ M_exp := hN₀ ▸ hn_lt.le
            exact_mod_cast this
          exact (div_le_self hn_pos.le hR1_ge).trans hn_le
        have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hdiv_le_N
        rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hl
        exact hl.trans hK_M
      · have hn_ge : N₀ ≤ n := Nat.not_lt.mp hn_lt
        have hH_lt : H < 2 := Nat.lt_of_not_ge fun hge => hbig ⟨hn_ge, hge⟩
        have hH_le1 : (H : ℝ) ≤ 1 := by exact_mod_cast (show H ≤ 1 by omega)
        calc Real.logb 2 ((n : ℝ) / R₁)
            ≤ (2 / γ) * (3 + 64 * (H : ℝ)) := hlog_H
          _ ≤ (2 / γ) * (3 + 64 * 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ = 134 / γ := by ring
          _ ≤ K_log := hK_γ
    clear hN₀
    have hlin := det_expectedSeqProbes_ge_linear withQueries hU hV (D_det := D_det) hcorr
    refine (?_ : c * (n : ℝ) * Real.logb 2 ((n : ℝ) / R₁) ≤ (n : ℝ) / 2).trans hlin
    have hck : c * Real.logb 2 ((n : ℝ) / R₁) ≤ 1 / 2 := by
      calc c * Real.logb 2 ((n : ℝ) / R₁)
          ≤ (1 / (2 * K_log)) * K_log :=
            mul_le_mul hc1 hlog_le_K hlog_div_nn (by positivity)
        _ = 1 / 2 := by field_simp
    calc c * (n : ℝ) * Real.logb 2 ((n : ℝ) / R₁)
        = (c * Real.logb 2 ((n : ℝ) / R₁)) * (n : ℝ) := by ring
      _ ≤ (1 / 2) * (n : ℝ) := mul_le_mul_of_nonneg_right hck hn_pos.le
      _ = (n : ℝ) / 2 := by ring

/-- Deterministic **Theorem 1.1 / Theorem 3.1** ([LiLiangYuZhou2023], Section 1, p. 1 / PDF p. 2 and
Section 3, pp. 10–13 / PDF pp. 11–14; Section 7, pp. 26–27 / PDF pp. 27–28): for any `α > 0`,
`c_R ≥ 0`, and `c_w ≥ 0`, there exists `c > 0` such that any step-indexed `IndexedScheme` exact on
admissible histories up to `4 * n + 1` with space
`≤ benchmarkBits U V n + c_R * n * max 1 (log^{(k)} n)` incurs at least `c * n * k` expected cell
probes on `insertQueryDeleteDist`. -/
theorem det_expectedSeqProbes_ge_of_iterLog_redundancy {α c_R c_w : ℝ}
    (hα : 0 < α) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n k cells w : ℕ} (hn : 2 ≤ n) (hU : 4 * n ≤ U)
        (_hU_poly : (n : ℝ) ^ (1 + α) ≤ (U : ℝ)) (hV : 1 ≤ V)
        (_hk_lo : 1 ≤ k) (_hk_hi : k ≤ Nat.logStar n)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤
          benchmarkBits U V n + c_R * (n : ℝ) * ((max (Nat.iterLog k n) 1 : ℕ) : ℝ))
        {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
          (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2),
        c * (n : ℝ) * (k : ℝ) ≤
          ∑' ops, (insertQueryDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
            (D_det.seqProbes ops : ℝ) := by
  obtain ⟨γ, hγ, hγ1, hγ_eq⟩ := exists_gamma_query hα hcw
  obtain ⟨c, hc, hmode⟩ := det_expectedSeqProbes_mode_ge_iterLog true hγ hγ1 hcR
  refine ⟨c, hc, fun {_U _V n _k _cells _w} hn hU hU_poly hV hk_lo hk_hi hw hspace {_D_det} hcorr =>
    ?_⟩
  exact
    hmode hn (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV hk_lo hk_hi hspace
      (by simpa only [modeHorizon, modeStride, ↓reduceIte, show n + 3 * n = 4 * n by ring]
        using hcorr)
      fun {_R _t} hspace_R T ht {_ℓ _b} hℓ ht_stop hF_lo h11 ht_hi hm_lo hF_hi hR_out hR_in =>
        outer_lemma_both_val_regimes hα hcw hγ hγ_eq hn hU hU_poly hV hw hspace_R T hcorr ht hℓ
          ht_stop hF_lo h11 ht_hi hm_lo hF_hi hR_out hR_in

/-- Zero-error randomized **Theorem 1.1 / Theorem 3.1** ([LiLiangYuZhou2023], Section 1, p. 1 /
PDF p. 2 and Section 3, pp. 10–13 / PDF pp. 11–14): any zero-error (Las Vegas)
`CellProbe.Randomized.Scheme` on oblivious `insertQueryDeleteDist` storing `n` keys in `[U]`
(`U ≥ n ^ (1 + α)`) with `≤ benchmarkBits U V n + c_R * n * max 1 (log^{(k)} n)` bits of memory
incurs `≥ c * n * k` expected cell probes (bounded-error Monte Carlo schemes and adaptive
adversaries are not covered). -/
theorem expectedSeqProbes_ge_of_iterLog_redundancy {α c_R c_w : ℝ}
    (hα : 0 < α) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n k cells w : ℕ} (hn : 2 ≤ n) (hU : 4 * n ≤ U)
        (_hU_poly : (n : ℝ) ^ (1 + α) ≤ (U : ℝ)) (hV : 1 ≤ V)
        (_hk_lo : 1 ≤ k) (_hk_hi : k ≤ Nat.logStar n)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤
          benchmarkBits U V n + c_R * (n : ℝ) * ((max (Nat.iterLog k n) 1 : ℕ) : ℝ))
        (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
          ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
            ops ((P.runSeq ops).map Prod.fst)),
        ENNReal.ofReal (c * (n : ℝ) * (k : ℝ)) ≤
          ∑' ops, insertQueryDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
            P.expectedSeqProbes ops := by
  obtain ⟨c, hc, hdet⟩ := det_expectedSeqProbes_ge_of_iterLog_redundancy hα hcR hcw
  exact ⟨c, hc, fun hn hU hU_poly hV hk_lo hk_hi hw hspace P hcorr =>
    le_expectedSeqProbes_query_of_det _ hV P hcorr (hdet hn hU hU_poly hV hk_lo hk_hi hw hspace)⟩

/-- Deterministic `Ω(n * log* n)` specialization of Theorem 1.1 at `k = Nat.logStar n` (`O(n)`
redundancy). -/
theorem det_expectedSeqProbes_ge_iterLogStar {α c_R c_w : ℝ}
    (hα : 0 < α) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} (hn : 2 ≤ n) (hU : 4 * n ≤ U)
        (_hU_poly : (n : ℝ) ^ (1 + α) ≤ (U : ℝ)) (hV : 1 ≤ V)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + c_R * (n : ℝ))
        {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
          (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2),
        c * (n : ℝ) * (Nat.logStar n : ℝ) ≤
          ∑' ops, (insertQueryDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
            (D_det.seqProbes ops : ℝ) := by
  obtain ⟨c, hc, hdet⟩ := det_expectedSeqProbes_ge_of_iterLog_redundancy hα hcR hcw
  refine ⟨c, hc, fun hn hU hU_poly hV hw hspace _ hcorr => ?_⟩
  obtain ⟨hk1, hspace'⟩ := iterLog_logStar_space_le hn hspace
  exact hdet hn hU hU_poly hV hk1 le_rfl hw hspace' hcorr

/-- Zero-error randomized `Ω(n * log* n)` specialization of Theorem 1.1 at `k = Nat.logStar n`
(`O(n)` bits of redundancy, Las Vegas oblivious model). -/
theorem expectedSeqProbes_ge_iterLogStar {α c_R c_w : ℝ}
    (hα : 0 < α) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} (hn : 2 ≤ n) (hU : 4 * n ≤ U)
        (_hU_poly : (n : ℝ) ^ (1 + α) ≤ (U : ℝ)) (hV : 1 ≤ V)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + c_R * (n : ℝ))
        (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
          ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
            ops ((P.runSeq ops).map Prod.fst)),
        ENNReal.ofReal (c * (n : ℝ) * (Nat.logStar n : ℝ)) ≤
          ∑' ops, insertQueryDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
            P.expectedSeqProbes ops := by
  obtain ⟨c, hc, hdet⟩ := det_expectedSeqProbes_ge_iterLogStar hα hcR hcw
  exact ⟨c, hc, fun hn hU hU_poly hV hw hspace P hcorr =>
    le_expectedSeqProbes_query_of_det _ hV P hcorr (hdet hn hU hU_poly hV hw hspace)⟩

/-- Deterministic **Theorem 1.2 / Theorem 6.1** ([LiLiangYuZhou2023], Section 1, p. 2 / PDF p. 3 and
Section 6, pp. 25–26 / PDF pp. 26–27): for any `α > 0` and `c_w ≥ 0`, there exists `c > 0` such that
any step-indexed `IndexedScheme` exact on admissible histories up to `4 * n + 1` with `R ≤ n` bits
of redundancy (`cells * w ≤ benchmarkBits U V n + R`) incurs at least
`c * n * log₂(n / max R 1)` expected cell probes on `insertQueryDeleteDist` (at the `R = n`
boundary `log₂(n / max R 1) = 0`; see `det_expectedSeqProbes_ge_iterLogStar_add_log_div` for the
combined bound across `R ≤ c_R * n`). -/
theorem det_expectedSeqProbes_ge_of_sublinear_redundancy {α c_w : ℝ}
    (hα : 0 < α) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} {R : ℝ} (hn : 2 ≤ n) (hU : 4 * n ≤ U)
        (_hU_poly : (n : ℝ) ^ (1 + α) ≤ (U : ℝ)) (hV : 1 ≤ V)
        (_hR_hi : R ≤ (n : ℝ))
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
        {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
          (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2),
        c * (n : ℝ) * Real.logb 2 ((n : ℝ) / max R 1) ≤
          ∑' ops, (insertQueryDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
            (D_det.seqProbes ops : ℝ) := by
  obtain ⟨γ, hγ, hγ1, hγ_eq⟩ := exists_gamma_query hα hcw
  obtain ⟨c, hc, hmode⟩ := det_expectedSeqProbes_mode_ge_sublinear true hγ hγ1
  refine ⟨c, hc, fun {_U _V n _cells _w} {_R} hn hU hU_poly hV hR_hi hw hspace {_D_det} hcorr => ?_⟩
  exact
    hmode hn (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV hR_hi hspace
      (by simpa only [modeHorizon, modeStride, ↓reduceIte, show n + 3 * n = 4 * n by ring]
        using hcorr)
      fun {_R _t} hspace_R T ht {_ℓ _b} hℓ ht_stop hF_lo h11 ht_hi hm_lo hF_hi hR_out hR_in =>
        outer_lemma_both_val_regimes hα hcw hγ hγ_eq hn hU hU_poly hV hw hspace_R T hcorr ht hℓ
          ht_stop hF_lo h11 ht_hi hm_lo hF_hi hR_out hR_in

/-- Zero-error randomized **Theorem 1.2 / Theorem 6.1** ([LiLiangYuZhou2023], Section 1, p. 2 /
PDF p. 3 and Section 6, pp. 25–26 / PDF pp. 26–27): any zero-error (Las Vegas)
`CellProbe.Randomized.Scheme` on oblivious `insertQueryDeleteDist` storing `n` keys in `[U]`
(`U ≥ n ^ (1 + α)`) with `R ≤ n` bits of redundancy incurs at least `c * n * log₂(n / max R 1)`
expected cell probes (vanishing at `R = n`). -/
theorem expectedSeqProbes_ge_of_sublinear_redundancy {α c_w : ℝ}
    (hα : 0 < α) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} {R : ℝ} (hn : 2 ≤ n) (hU : 4 * n ≤ U)
        (_hU_poly : (n : ℝ) ^ (1 + α) ≤ (U : ℝ)) (hV : 1 ≤ V)
        (_hR_hi : R ≤ (n : ℝ))
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
        (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
          ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
            ops ((P.runSeq ops).map Prod.fst)),
        ENNReal.ofReal (c * (n : ℝ) * Real.logb 2 ((n : ℝ) / max R 1)) ≤
          ∑' ops, insertQueryDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
            P.expectedSeqProbes ops := by
  obtain ⟨c, hc, hdet⟩ := det_expectedSeqProbes_ge_of_sublinear_redundancy hα hcw
  exact ⟨c, hc, fun hn hU hU_poly hV hR_hi hw hspace P hcorr =>
    le_expectedSeqProbes_query_of_det _ hV P hcorr (hdet hn hU hU_poly hV hR_hi hw hspace)⟩

/-- Combined deterministic **Theorems 1.1 & 1.2** (`Ω(n * (log* n + log₂(n / max R 1)))`) across
all `R ≤ c_R * n` ([LiLiangYuZhou2023], Section 1, pp. 1–2 / PDF pp. 2–3). -/
theorem det_expectedSeqProbes_ge_iterLogStar_add_log_div {α c_R c_w : ℝ}
    (hα : 0 < α) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} {R : ℝ} (hn : 2 ≤ n) (hU : 4 * n ≤ U)
        (_hU_poly : (n : ℝ) ^ (1 + α) ≤ (U : ℝ)) (hV : 1 ≤ V)
        (_hR_hi : R ≤ c_R * (n : ℝ))
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
        {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
          (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2),
        c * (n : ℝ) * ((Nat.logStar n : ℝ) + max 0 (Real.logb 2 ((n : ℝ) / max R 1))) ≤
          ∑' ops, (insertQueryDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
            (D_det.seqProbes ops : ℝ) := by
  obtain ⟨c₁, hc₁, hdet₁⟩ := det_expectedSeqProbes_ge_iterLogStar hα hcR hcw
  obtain ⟨c₂, hc₂, hdet₂⟩ := det_expectedSeqProbes_ge_of_sublinear_redundancy hα hcw
  refine ⟨min c₁ c₂ / 2, by positivity, fun hn hU hU_poly hV hR_hi hw hspace _ hcorr => ?_⟩
  exact combine_iterLogStar_and_sublinear hn (Nat.cast_nonneg _)
    (tsum_nonneg fun _ => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _))
    (hdet₁ hn hU hU_poly hV hw (hspace.trans (by linarith)) hcorr)
    fun hRn => hdet₂ hn hU hU_poly hV hRn hw hspace hcorr

/-- Combined zero-error randomized **Theorems 1.1 & 1.2**
(`Ω(n * (log* n + log₂(n / max R 1)))`) across all `R ≤ c_R * n` in the Las Vegas oblivious model
([LiLiangYuZhou2023], Section 1, pp. 1–2 / PDF pp. 2–3). -/
theorem expectedSeqProbes_ge_iterLogStar_add_log_div {α c_R c_w : ℝ}
    (hα : 0 < α) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} {R : ℝ} (hn : 2 ≤ n) (hU : 4 * n ≤ U)
        (_hU_poly : (n : ℝ) ^ (1 + α) ≤ (U : ℝ)) (hV : 1 ≤ V)
        (_hR_hi : R ≤ c_R * (n : ℝ))
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
        (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (4 * n + 1),
          ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
            ops ((P.runSeq ops).map Prod.fst)),
        ENNReal.ofReal (c * (n : ℝ) *
          ((Nat.logStar n : ℝ) + max 0 (Real.logb 2 ((n : ℝ) / max R 1)))) ≤
          ∑' ops, insertQueryDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
            P.expectedSeqProbes ops := by
  obtain ⟨c, hc, hdet⟩ := det_expectedSeqProbes_ge_iterLogStar_add_log_div hα hcR hcw
  exact ⟨c, hc, fun hn hU hU_poly hV hR_hi hw hspace P hcorr =>
    le_expectedSeqProbes_query_of_det _ hV P hcorr (hdet hn hU hU_poly hV hR_hi hw hspace)⟩

/-- Unified single-node update-only `OuterLemma` on `insertDeleteDist` under
`U ^ (2 + α_V) ≤ V * n ^ 2` and `w ≤ c_w * (log₂ U + log₂ V)` ([LiLiangYuZhou2023], Section 8,
pp. 27–30 / PDF pp. 28–31). -/
private theorem outer_lemma_update_of_val_ge {U V n cells w : ℕ} {α_V c_w γ R t : ℝ}
    (hα_V : 0 < α_V) (hγ : 0 < γ)
    (hγ_le : (5 + c_w) * γ ≤ min (1 / 4) (α_V / 16))
    (hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
    (hV_lo : (U : ℝ) ^ (2 + α_V) ≤ (V : ℝ) * (n : ℝ) ^ 2)
    (hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
    (hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
    (T : MetaTree) {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
    (hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
      (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2)
    (ht : 0 < t) {ℓ b : ℕ} (hℓ : 1 ≤ ℓ) (ht_stop : T.nodeStop (ℓ + 1) b ≤ n)
    (hF_lo : 2 ^ 64 ≤ T.fanout (ℓ + 1))
    (h11 : 11 / γ ≤ Real.logb 2 U)
    (ht_hi : 6 * t ≤ γ * Real.logb 2 U)
    (hF_hi : (T.fanout (ℓ + 1) : ℝ) ≤ (γ / 2) * Real.logb 2 U)
    (hR_outer : 100 * R ≤ (T.blockSize (ℓ + 1) : ℝ) * Real.logb 2 (T.fanout (ℓ + 1)))
    (hR_in : R ≤ (γ / 2) * (T.blockSize ℓ : ℝ) * Real.logb 2 U) :
    (γ / 100) * (T.blockSize (ℓ + 1) : ℝ) ≤
        ∑' ops, (insertDeleteDist U V n
          (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
          (T.nodeCost D_det n 2 ops ℓ b : ℝ) ∨
      (1 / 16) * (T.blockSize (ℓ + 1) : ℝ) * t ≤
        ∑' ops, (insertDeleteDist U V n
          (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
          (T.nodeProbes D_det n 2 ops (ℓ + 1) b : ℝ) := by
  have hbud : 2 * R + 7 * (T.blockSize ℓ : ℝ) + 2 * (T.blockSize ℓ : ℝ) * t +
      γ * (T.blockSize ℓ : ℝ) * (w : ℝ) + 2 * γ * (T.blockSize ℓ : ℝ) * Real.logb 2 U ≤
      ((T.blockSize ℓ : ℝ) / 2) * Real.logb 2 V -
        (T.blockSize ℓ : ℝ) * Real.logb 2 ((U : ℝ) / (n : ℝ)) := by
    clear hF_lo
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hU_pos : (0 : ℝ) < (U : ℝ) := by exact_mod_cast (show 0 < U by omega)
    have hV_pos : (0 : ℝ) < (V : ℝ) := by exact_mod_cast hV
    have hlogU_nn : 0 ≤ Real.logb 2 U :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ U by omega))
    have hlogV_nn : 0 ≤ Real.logb 2 V :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast hV)
    have hlogn_nn : 0 ≤ Real.logb 2 n :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ n by omega))
    have hlog_V_lo : (2 + α_V) * Real.logb 2 U ≤ Real.logb 2 V + 2 * Real.logb 2 n := by
      have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        (Real.rpow_pos_of_pos hU_pos _) hV_lo
      rw [Real.logb_rpow_eq_mul_logb_of_pos hU_pos,
        Real.logb_mul hV_pos.ne' (pow_ne_zero 2 hn_pos.ne'), Real.logb_pow, Nat.cast_ofNat] at hl
      exact hl
    set gap := (1 / 2) * Real.logb 2 V - Real.logb 2 U + Real.logb 2 n
    have hgap1 : (α_V / 2) * Real.logb 2 U ≤ gap := by dsimp [gap]; linarith
    have hgap2 : (1 / 2) * Real.logb 2 V - Real.logb 2 U ≤ gap := by dsimp [gap]; linarith
    set η := min (1 / 4) (α_V / 16)
    have hη_pos : 0 < η := by dsimp [η]; positivity
    have hη_4 : η ≤ 1 / 4 := min_le_left _ _
    have hη_α : 8 * η ≤ α_V / 2 := by
      have : η ≤ α_V / 16 := min_le_right _ _
      linarith
    have hconv1 : 4 * η * Real.logb 2 U ≤ (1 - 2 * η) * gap := by
      have h1 : 4 * η ≤ (1 - 2 * η) * (α_V / 2) :=
        calc 4 * η = (1 / 2) * (8 * η) := by ring
          _ ≤ (1 - 2 * η) * (α_V / 2) :=
            mul_le_mul (by linarith) hη_α (by positivity) (by linarith)
      exact (by ring_nf : 4 * η * Real.logb 2 U = (4 * η) * Real.logb 2 U).trans_le
        ((mul_le_mul_of_nonneg_right h1 hlogU_nn).trans
          ((mul_assoc _ _ _).trans_le (mul_le_mul_of_nonneg_left hgap1 (by linarith))))
    have hconv2 : η * Real.logb 2 V - 2 * η * Real.logb 2 U ≤ 2 * η * gap := by
      have hm := mul_le_mul_of_nonneg_left hgap2 (show 0 ≤ 2 * η by positivity)
      linarith
    have hgap_lb : η * (Real.logb 2 U + Real.logb 2 V) ≤ gap := by
      have h1 : η * (Real.logb 2 U + Real.logb 2 V) ≤
          (4 * η * Real.logb 2 U) + (η * Real.logb 2 V - 2 * η * Real.logb 2 U) := by
        calc η * (Real.logb 2 U + Real.logb 2 V)
          _ = η * Real.logb 2 U + η * Real.logb 2 V := by ring
          _ ≤ (η * Real.logb 2 U + η * Real.logb 2 U) + η * Real.logb 2 V := by
            have : 0 ≤ η * Real.logb 2 U := by positivity
            linarith
          _ = (4 * η * Real.logb 2 U) + (η * Real.logb 2 V - 2 * η * Real.logb 2 U) := by ring
      have h2 : (4 * η * Real.logb 2 U) + (η * Real.logb 2 V - 2 * η * Real.logb 2 U) ≤
          (1 - 2 * η) * gap + 2 * η * gap := add_le_add hconv1 hconv2
      have h3 : (1 - 2 * η) * gap + 2 * η * gap = gap := by ring
      exact h1.trans (h2.trans_eq h3)
    set m := (T.blockSize ℓ : ℝ)
    have hm_nn : 0 ≤ m := Nat.cast_nonneg _
    have h11_mul : 11 ≤ γ * Real.logb 2 U := by
      have := (div_le_iff₀ hγ).mp h11; linarith
    have h1 : 7 * m ≤ γ * m * Real.logb 2 U := by
      have h7 : 7 ≤ γ * Real.logb 2 U := by linarith
      have := mul_le_mul_of_nonneg_right h7 hm_nn; linarith
    have h2 : 2 * m * t ≤ γ * m * Real.logb 2 U := by
      have h2t : 2 * t ≤ γ * Real.logb 2 U := by linarith
      have := mul_le_mul_of_nonneg_left h2t hm_nn; linarith
    have h3 : γ * m * (w : ℝ) ≤ c_w * γ * m * (Real.logb 2 U + Real.logb 2 V) := by
      have := mul_le_mul_of_nonneg_left hw (show 0 ≤ γ * m by positivity); linarith
    have h4 : 5 * γ * m * Real.logb 2 U ≤ 5 * γ * m * (Real.logb 2 U + Real.logb 2 V) := by
      have := mul_le_mul_of_nonneg_left (show Real.logb 2 U ≤ Real.logb 2 U + Real.logb 2 V by
        linarith) (show 0 ≤ 5 * γ * m by positivity)
      linarith
    have h5 : ((5 + c_w) * γ) * (m * (Real.logb 2 U + Real.logb 2 V)) ≤
        η * (m * (Real.logb 2 U + Real.logb 2 V)) :=
      mul_le_mul_of_nonneg_right hγ_le (by positivity)
    have h6 : η * (m * (Real.logb 2 U + Real.logb 2 V)) ≤ m * gap := by
      have hm := mul_le_mul_of_nonneg_left hgap_lb hm_nn
      linarith
    have hrhs : (m / 2) * Real.logb 2 V - m * Real.logb 2 ((U : ℝ) / (n : ℝ)) = m * gap := by
      rw [Real.logb_div hU_pos.ne' hn_pos.ne']; dsimp [gap]; ring
    rw [hrhs]
    linarith
  exact outer_lemma_insertDelete hU hV hspace hspace T hcorr hγ ht hℓ ht_stop hF_lo hF_hi
    hR_outer hbud

/-- Deterministic **Theorem 1.3(1)** ([LiLiangYuZhou2023], Section 1, p. 2 / PDF p. 3 and
Section 8, pp. 27–30 / PDF pp. 28–31): update-only (`insertDeleteDist`) `Ω(n * k)` cell-probe
lower bound for `3 * n ≤ U` and `U ^ (2 + α_V) ≤ V * n ^ 2` under redundancy
`≤ c_R * n * max 1 (log^{(k)} n)` (correctness up to `3 * n + 1` allows one trailing `.query` step
so `decodeDict` is well-defined after the `3 * n` `PUnit`-returning updates). -/
theorem det_expectedSeqProbes_update_ge_iterLog {α_V c_R c_w : ℝ}
    (hα_V : 0 < α_V) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n k cells w : ℕ} (hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
        (_hV_lo : (U : ℝ) ^ (2 + α_V) ≤ (V : ℝ) * (n : ℝ) ^ 2)
        (_hk_lo : 1 ≤ k) (_hk_hi : k ≤ Nat.logStar n)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤
          benchmarkBits U V n + c_R * (n : ℝ) * ((max (Nat.iterLog k n) 1 : ℕ) : ℝ))
        {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
          (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2),
        c * (n : ℝ) * (k : ℝ) ≤
          ∑' ops, (insertDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
            (D_det.seqProbes ops : ℝ) := by
  obtain ⟨γ, hγ, hγ1, hγ_le⟩ := exists_gamma_update hα_V hcw
  obtain ⟨c, hc, hmode⟩ := det_expectedSeqProbes_mode_ge_iterLog false hγ hγ1 hcR
  refine ⟨c, hc, fun {_U _V n _k _cells _w} hn hU hV hV_lo hk_lo hk_hi hw hspace {_D_det} hcorr =>
    ?_⟩
  exact
    hmode hn (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV hk_lo hk_hi hspace
      (by simpa only [modeHorizon, modeStride, Bool.false_eq_true, ↓reduceIte,
        show n + 2 * n = 3 * n by ring] using hcorr)
      fun {_R _t} hspace_R T ht {_ℓ _b} hℓ ht_stop hF_lo h11 ht_hi _hm_lo hF_hi hR_out hR_in =>
        outer_lemma_update_of_val_ge hα_V hγ hγ_le hn hU hV hV_lo hw hspace_R T hcorr ht hℓ
          ht_stop hF_lo h11 ht_hi hF_hi hR_out hR_in

/-- Zero-error randomized **Theorem 1.3(1)** ([LiLiangYuZhou2023], Section 1, p. 2 / PDF p. 3 and
Section 8, pp. 27–30 / PDF pp. 28–31) in the Las Vegas oblivious model (`3 * n + 1` correctness
horizon for `decodeDict` on update-only `insertDeleteDist`). -/
theorem expectedSeqProbes_update_ge_iterLog {α_V c_R c_w : ℝ}
    (hα_V : 0 < α_V) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n k cells w : ℕ} (hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
        (_hV_lo : (U : ℝ) ^ (2 + α_V) ≤ (V : ℝ) * (n : ℝ) ^ 2)
        (_hk_lo : 1 ≤ k) (_hk_hi : k ≤ Nat.logStar n)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤
          benchmarkBits U V n + c_R * (n : ℝ) * ((max (Nat.iterLog k n) 1 : ℕ) : ℝ))
        (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
          ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
            ops ((P.runSeq ops).map Prod.fst)),
        ENNReal.ofReal (c * (n : ℝ) * (k : ℝ)) ≤
          ∑' ops, insertDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
            P.expectedSeqProbes ops := by
  obtain ⟨c, hc, hdet⟩ := det_expectedSeqProbes_update_ge_iterLog hα_V hcR hcw
  exact ⟨c, hc, fun hn hU hV hV_lo hk_lo hk_hi hw hspace P hcorr =>
    le_expectedSeqProbes_update_of_det _ hV P hcorr (hdet hn hU hV hV_lo hk_lo hk_hi hw hspace)⟩

/-- Deterministic `Ω(n * log* n)` specialization of Theorem 1.3(1) at `k = Nat.logStar n` (`O(n)`
redundancy). -/
theorem det_expectedSeqProbes_update_ge_iterLogStar {α_V c_R c_w : ℝ}
    (hα_V : 0 < α_V) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} (hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
        (_hV_lo : (U : ℝ) ^ (2 + α_V) ≤ (V : ℝ) * (n : ℝ) ^ 2)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + c_R * (n : ℝ))
        {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
          (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2),
        c * (n : ℝ) * (Nat.logStar n : ℝ) ≤
          ∑' ops, (insertDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
            (D_det.seqProbes ops : ℝ) := by
  obtain ⟨c, hc, hdet⟩ := det_expectedSeqProbes_update_ge_iterLog hα_V hcR hcw
  refine ⟨c, hc, fun hn hU hV hV_lo hw hspace _ hcorr => ?_⟩
  obtain ⟨hk1, hspace'⟩ := iterLog_logStar_space_le hn hspace
  exact hdet hn hU hV hV_lo hk1 le_rfl hw hspace' hcorr

/-- Zero-error randomized `Ω(n * log* n)` specialization of Theorem 1.3(1) at `k = Nat.logStar n`
(Las Vegas oblivious model). -/
theorem expectedSeqProbes_update_ge_iterLogStar {α_V c_R c_w : ℝ}
    (hα_V : 0 < α_V) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} (hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
        (_hV_lo : (U : ℝ) ^ (2 + α_V) ≤ (V : ℝ) * (n : ℝ) ^ 2)
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + c_R * (n : ℝ))
        (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
          ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
            ops ((P.runSeq ops).map Prod.fst)),
        ENNReal.ofReal (c * (n : ℝ) * (Nat.logStar n : ℝ)) ≤
          ∑' ops, insertDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
            P.expectedSeqProbes ops := by
  obtain ⟨c, hc, hdet⟩ := det_expectedSeqProbes_update_ge_iterLogStar hα_V hcR hcw
  exact ⟨c, hc, fun hn hU hV hV_lo hw hspace P hcorr =>
    le_expectedSeqProbes_update_of_det _ hV P hcorr (hdet hn hU hV hV_lo hw hspace)⟩

/-- Deterministic **Theorem 1.3(2)** ([LiLiangYuZhou2023], Section 1, p. 2 / PDF p. 3 and
Section 8, pp. 27–30 / PDF pp. 28–31): update-only (`insertDeleteDist`)
`Ω(n * log₂(n / max R 1))` cell-probe lower bound for `3 * n ≤ U`, `U ^ (2 + α_V) ≤ V * n ^ 2`,
and `R ≤ n` (vanishing at the `R = n` boundary, with `3 * n + 1` correctness horizon for
`decodeDict`). -/
theorem det_expectedSeqProbes_update_ge_sublinear {α_V c_w : ℝ}
    (hα_V : 0 < α_V) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} {R : ℝ} (hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
        (_hV_lo : (U : ℝ) ^ (2 + α_V) ≤ (V : ℝ) * (n : ℝ) ^ 2)
        (_hR_hi : R ≤ (n : ℝ))
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
        {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
          (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2),
        c * (n : ℝ) * Real.logb 2 ((n : ℝ) / max R 1) ≤
          ∑' ops, (insertDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
            (D_det.seqProbes ops : ℝ) := by
  obtain ⟨γ, hγ, hγ1, hγ_le⟩ := exists_gamma_update hα_V hcw
  obtain ⟨c, hc, hmode⟩ := det_expectedSeqProbes_mode_ge_sublinear false hγ hγ1
  refine ⟨c, hc, fun {_U _V n _cells _w} {_R} hn hU hV hV_lo hR_hi hw hspace {_D_det} hcorr => ?_⟩
  exact
    hmode hn (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV hR_hi hspace
      (by simpa only [modeHorizon, modeStride, Bool.false_eq_true, ↓reduceIte,
        show n + 2 * n = 3 * n by ring] using hcorr)
      fun {_R _t} hspace_R T ht {_ℓ _b} hℓ ht_stop hF_lo h11 ht_hi _hm_lo hF_hi hR_out hR_in =>
        outer_lemma_update_of_val_ge hα_V hγ hγ_le hn hU hV hV_lo hw hspace_R T hcorr ht hℓ
          ht_stop hF_lo h11 ht_hi hF_hi hR_out hR_in

/-- Zero-error randomized **Theorem 1.3(2)** ([LiLiangYuZhou2023], Section 1, p. 2 / PDF p. 3 and
Section 8, pp. 27–30 / PDF pp. 28–31) in the Las Vegas oblivious model (vanishing at `R = n`). -/
theorem expectedSeqProbes_update_ge_sublinear {α_V c_w : ℝ}
    (hα_V : 0 < α_V) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} {R : ℝ} (hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
        (_hV_lo : (U : ℝ) ^ (2 + α_V) ≤ (V : ℝ) * (n : ℝ) ^ 2)
        (_hR_hi : R ≤ (n : ℝ))
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
        (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
          ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
            ops ((P.runSeq ops).map Prod.fst)),
        ENNReal.ofReal (c * (n : ℝ) * Real.logb 2 ((n : ℝ) / max R 1)) ≤
          ∑' ops, insertDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
            P.expectedSeqProbes ops := by
  obtain ⟨c, hc, hdet⟩ := det_expectedSeqProbes_update_ge_sublinear hα_V hcw
  exact ⟨c, hc, fun hn hU hV hV_lo hR_hi hw hspace P hcorr =>
    le_expectedSeqProbes_update_of_det _ hV P hcorr (hdet hn hU hV hV_lo hR_hi hw hspace)⟩

/-- Combined deterministic **Theorem 1.3(1)–(2)**
(`Ω(n * (log* n + log₂(n / max R 1)))`) on `insertDeleteDist` across all `R ≤ c_R * n`
([LiLiangYuZhou2023], Section 1, p. 2 / PDF p. 3 and Section 8, p. 27 / PDF p. 28). -/
theorem det_expectedSeqProbes_update_ge_iterLogStar_add_log_div {α_V c_R c_w : ℝ}
    (hα_V : 0 < α_V) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} {R : ℝ} (hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
        (_hV_lo : (U : ℝ) ^ (2 + α_V) ≤ (V : ℝ) * (n : ℝ) ^ 2)
        (_hR_hi : R ≤ c_R * (n : ℝ))
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
        {D_det : IndexedScheme (Dynamic.Op U) Dynamic.Op.Result cells w}
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
          (D_det.runSeq ops).1 = ((Dynamic.spec U V n).run (Dictionary.empty U) ops).2),
        c * (n : ℝ) * ((Nat.logStar n : ℝ) + max 0 (Real.logb 2 ((n : ℝ) / max R 1))) ≤
          ∑' ops, (insertDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops).toReal *
            (D_det.seqProbes ops : ℝ) := by
  obtain ⟨c₁, hc₁, hdet₁⟩ := det_expectedSeqProbes_update_ge_iterLogStar hα_V hcR hcw
  obtain ⟨c₂, hc₂, hdet₂⟩ := det_expectedSeqProbes_update_ge_sublinear hα_V hcw
  refine ⟨min c₁ c₂ / 2, by positivity, fun hn hU hV hV_lo hR_hi hw hspace _ hcorr => ?_⟩
  exact combine_iterLogStar_and_sublinear hn (Nat.cast_nonneg _)
    (tsum_nonneg fun _ => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _))
    (hdet₁ hn hU hV hV_lo hw (hspace.trans (by linarith)) hcorr)
    fun hRn => hdet₂ hn hU hV hV_lo hRn hw hspace hcorr

/-- Combined zero-error randomized **Theorem 1.3(1)–(2)**
(`Ω(n * (log* n + log₂(n / max R 1)))`) on `insertDeleteDist` across all `R ≤ c_R * n` in the
Las Vegas oblivious model ([LiLiangYuZhou2023], Section 1, p. 2 / PDF p. 3 and Section 8, p. 27 /
PDF p. 28). -/
theorem expectedSeqProbes_update_ge_iterLogStar_add_log_div {α_V c_R c_w : ℝ}
    (hα_V : 0 < α_V) (hcR : 0 ≤ c_R) (hcw : 0 ≤ c_w) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {U V n cells w : ℕ} {R : ℝ} (hn : 2 ≤ n) (hU : 3 * n ≤ U) (hV : 1 ≤ V)
        (_hV_lo : (U : ℝ) ^ (2 + α_V) ≤ (V : ℝ) * (n : ℝ) ^ 2)
        (_hR_hi : R ≤ c_R * (n : ℝ))
        (_hw : (w : ℝ) ≤ c_w * (Real.logb 2 U + Real.logb 2 V))
        (_hspace : ((cells * w : ℕ) : ℝ) ≤ benchmarkBits U V n + R)
        (P : Cslib.CellProbe.Randomized.Scheme (Dynamic.Op U) Dynamic.Op.Result cells w)
        (_hcorr : ∀ ops ∈ validHistoriesUpTo U V n (3 * n + 1),
          ((Dynamic.spec U V n).toObliviousSequenceSpec (Dictionary.empty U)).Contract
            ops ((P.runSeq ops).map Prod.fst)),
        ENNReal.ofReal (c * (n : ℝ) *
          ((Nat.logStar n : ℝ) + max 0 (Real.logb 2 ((n : ℝ) / max R 1)))) ≤
          ∑' ops, insertDeleteDist U V n
            (Nat.le_trans (Nat.mul_le_mul_right n (by decide)) hU) hV ops *
            P.expectedSeqProbes ops := by
  obtain ⟨c, hc, hdet⟩ := det_expectedSeqProbes_update_ge_iterLogStar_add_log_div hα_V hcR hcw
  exact ⟨c, hc, fun hn hU hV hV_lo hR_hi hw hspace P hcorr =>
    le_expectedSeqProbes_update_of_det _ hV P hcorr (hdet hn hU hV hV_lo hR_hi hw hspace)⟩

end Cslib.DataStructure.Dictionary.CellProbe
