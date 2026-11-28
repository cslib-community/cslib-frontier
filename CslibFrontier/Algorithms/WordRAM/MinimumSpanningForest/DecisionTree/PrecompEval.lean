/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.DecisionTree.Layout
public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.DecisionTree.PrecompKruskal
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.UpdateSimp
import CslibFrontier.Tactic.WramOmega
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.GeomSum

/-!
# Skeleton Evaluation and Table-Entry Writers for DT Precomputation

Defines the shared workspace layout (`DTPrecompBufA`, `DTPrecompBufB`, `DTPrecompBufC`,
`DTPrecompEnv`, `DTEnvLayout`), entry validity/input invariants (`DTMaskEntryValid`, `DTMaskIn`),
and verified Word-RAM evaluation and table-entry writers (`dtTestSkelProg`, `dtWriteFoundEntry`,
`dtWriteTrivialEntry`) consumed by `DecisionTree.PrecompSearch` as steps toward
[PettieRamachandran2002], Theorem 5.8 (#8624; Section 4.1, p. 23 and Section 5.1, pp. 25–26,
Corollary 5.6 and Theorem 5.8).

## Main definitions

* `DTPrecompBufA`, `DTPrecompBufB`, `DTPrecompBufC`, `DTPrecompEnv`, `DTCheckPermEnv`,
  `DTSkelEnv`: word-encoded workspace handles and search-environment records.
* `DTEnvLayout`, `DTMaskEntryValid`, `DTMaskIn`, `CodeIsPerm`, `permOfCode`: scratch-workspace
  disjointness invariants, table-entry predicates, and base-`e` permutation decoding.
* `dtTestSkelProg`, `dtTestSkelProgSafe`: clears `leafSeen` and `leafAns`, then loops over
  `0 .. d.2 - 1` reading stored answers from `permAns` (`0` as skip marker) and checking leaf
  consistency; under `dtTestSkelProg_spec`'s precomputed `DTMaskIn` table, disjoint `DTEnvLayout`
  workspace, initialized `powSkelArr`/`powEArr` power tables, and `d.2 = e ^ e`, returns `1` iff
  the skeleton determines `Cslib.Multigraph.msf` at every leaf (writing `leafAns`).
* `dtWriteFoundEntry`, `dtWriteFoundEntrySafe`, `dtWriteTrivialEntry`, `dtWriteTrivialEntrySafe`:
  allocates and writes complete decision-tree table entries (`e ≥ 2` and `e ≤ 1`).

## Main results

* `dtMaskEntryValid_preserve`, `dtMaskIn_of_modifies`: frame preservation for table and mask state.
* `dtTestSkelProg_spec`, `realizes_dtTestSkelProg`: framed specification and `work = 0`
  Word-RAM realization of `dtTestSkelProg`.
* `dtWriteFoundEntry_spec`, `realizes_dtWriteFoundEntry`: framed specification and `work = 0`
  Word-RAM realization of `dtWriteFoundEntry`.
* `dtWriteTrivialEntry_spec`, `realizes_dtWriteTrivialEntry`: framed specification and `work = 0`
  Word-RAM realization of `dtWriteTrivialEntry`.

## References

* [Seth Pettie and Vijaya Ramachandran, *An Optimal Minimum Spanning Tree Algorithm*,
  Journal of the ACM 49(1), pp. 16–34, 2002][PettieRamachandran2002]
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization
open Cslib.Query.MinimumSpanningForest

/-! ## Section 1: Word-Encoded Environments, Permutation Coding, and Framed Plumbing -/

/-- Workspace buffer group A (table base, pair index buffers, decoded edge buffers). -/
structure DTPrecompBufA where
  /-- Base address of the top-level mask pointer table. -/
  tableBase : ℕ
  /-- Base address of `r0` pair first endpoints (`allPairs r0`). -/
  r0PairA : ℕ
  /-- Base address of `r0` pair second endpoints (`allPairs r0`). -/
  r0PairB : ℕ
  /-- Base address of decoded edge first endpoints. -/
  edgeU : ℕ
  /-- Base address of decoded edge second endpoints. -/
  edgeV : ℕ
  /-- Base address of decoded edge pair indices. -/
  edgePair : ℕ
  deriving DecidableEq

/-- Six-word encoding of `DTPrecompBufA`. -/
word_enc_structure dtPrecompBufAWords : DTPrecompBufA where
  tableBase : wordWords, r0PairA : wordWords, r0PairB : wordWords,
  edgeU : wordWords, edgeV : wordWords, edgePair : wordWords

instance : WordEncoding DTPrecompBufA := ⟨6, dtPrecompBufAWords⟩

/-- Workspace buffer group B (per-mask pairs, leaf tables, permutation buffers). -/
structure DTPrecompBufB where
  /-- Base address of `e` pair first endpoints (`allPairs e`). -/
  allPairA : ℕ
  /-- Base address of `e` pair second endpoints (`allPairs e`). -/
  allPairB : ℕ
  /-- Base address of leaf MSF bitmask buffer (`2 ^ maxD` words). -/
  leafAns : ℕ
  /-- Base address of leaf seen-flag buffer (`2 ^ maxD` words). -/
  leafSeen : ℕ
  /-- Base address of permutation rank array (`maxE` words). -/
  rankArr : ℕ
  /-- Base address of permutation order array (`maxE` words). -/
  orderArr : ℕ
  deriving DecidableEq

/-- Six-word encoding of `DTPrecompBufB`. -/
word_enc_structure dtPrecompBufBWords : DTPrecompBufB where
  allPairA : wordWords, allPairB : wordWords, leafAns : wordWords,
  leafSeen : wordWords, rankArr : wordWords, orderArr : wordWords

instance : WordEncoding DTPrecompBufB := ⟨6, dtPrecompBufBWords⟩

/-- Workspace buffer group C (seen flags, Union-Find buffer, and power tables). -/
structure DTPrecompBufC where
  /-- Base address of permutation digit seen flags (`maxE` words). -/
  seenArr : ℕ
  /-- Base address of Union-Find component array (`r0` words). -/
  compArr : ℕ
  /-- Base address of `e ^ j` powers table (`maxE + 1` words). -/
  powEArr : ℕ
  /-- Base address of `(e.choose 2) ^ k` powers table (`2 ^ maxD` words). -/
  powSkelArr : ℕ
  deriving DecidableEq

/-- Four-word encoding of `DTPrecompBufC`. -/
word_enc_structure dtPrecompBufCWords : DTPrecompBufC where
  seenArr : wordWords, compArr : wordWords, powEArr : wordWords, powSkelArr : wordWords

instance : WordEncoding DTPrecompBufC := ⟨4, dtPrecompBufCWords⟩

/-- Global precomputation environment holding vertex bound `r0` and buffer addresses. -/
structure DTPrecompEnv where
  /-- Maximum vertex count `r0`. -/
  r0 : ℕ
  /-- Maximum edge count `r0.choose 2`. -/
  maxE : ℕ
  /-- Number of canonical graph bitmasks `2 ^ maxE`. -/
  numMasks : ℕ
  /-- Maximum tree depth `maxE.choose 2`. -/
  maxD : ℕ
  /-- Workspace buffer group A. -/
  bufA : DTPrecompBufA
  /-- Workspace buffer group B. -/
  bufB : DTPrecompBufB
  /-- Workspace buffer group C. -/
  bufC : DTPrecompBufC
  deriving DecidableEq

/-- Twenty-word encoding of `DTPrecompEnv`. -/
word_enc_structure dtPrecompEnvWords : DTPrecompEnv where
  r0 : wordWords, maxE : wordWords, numMasks : wordWords, maxD : wordWords,
  bufA : dtPrecompBufAWords, bufB : dtPrecompBufBWords, bufC : dtPrecompBufCWords

instance : WordEncoding DTPrecompEnv := ⟨20, dtPrecompEnvWords⟩

private structure DTSkelWalkEnv where
  allPairA : ℕ
  allPairB : ℕ
  powSkelArr : ℕ
  powEArr : ℕ
  numPairs : ℕ
  e : ℕ
  skelCode : ℕ
  code : ℕ
  deriving DecidableEq

private word_enc_structure dtSkelWalkEnvWords : DTSkelWalkEnv where
  allPairA : wordWords, allPairB : wordWords, powSkelArr : wordWords,
  powEArr : wordWords, numPairs : wordWords, e : wordWords,
  skelCode : wordWords, code : wordWords

private instance : WordEncoding DTSkelWalkEnv := ⟨8, dtSkelWalkEnvWords⟩

/-- Environment record for testing one candidate skeleton across all base-`e` codes. -/
structure DTCheckPermEnv where
  /-- Precomputation workspace environment. -/
  env : DTPrecompEnv
  /-- Edge count `e` of the current graph mask. -/
  e : ℕ
  /-- Candidate tree depth `d`. -/
  d : ℕ
  /-- Precomputed `2 ^ d`. -/
  pow2d : ℕ
  /-- Number of unordered edge pairs `e.choose 2`. -/
  numPairs : ℕ
  /-- Base address of precomputed permutation MSF answers. -/
  permAns : ℕ
  /-- Candidate base-`numPairs` skeleton integer. -/
  skelCode : ℕ
  deriving DecidableEq

/-- Twenty-six-word encoding of `DTCheckPermEnv`. -/
word_enc_structure dtCheckPermEnvWords : DTCheckPermEnv where
  env : dtPrecompEnvWords, e : wordWords, d : wordWords, pow2d : wordWords,
  numPairs : wordWords, permAns : wordWords, skelCode : wordWords

instance : WordEncoding DTCheckPermEnv := ⟨26, dtCheckPermEnvWords⟩

private structure DTWriteIntEnv where
  intBase : ℕ
  allPairA : ℕ
  allPairB : ℕ
  powSkelArr : ℕ
  numPairs : ℕ
  skelCode : ℕ
  deriving DecidableEq

private word_enc_structure dtWriteIntEnvWords : DTWriteIntEnv where
  intBase : wordWords, allPairA : wordWords, allPairB : wordWords,
  powSkelArr : wordWords, numPairs : wordWords, skelCode : wordWords

private instance : WordEncoding DTWriteIntEnv := ⟨6, dtWriteIntEnvWords⟩

/-- Search environment for finding and writing a valid depth-`d` skeleton. -/
structure DTSkelEnv where
  /-- Precomputation workspace environment. -/
  env : DTPrecompEnv
  /-- Canonical graph bitmask under inspection. -/
  mask : ℕ
  /-- Edge count `e` of the graph mask. -/
  e : ℕ
  /-- Candidate decision-tree depth `d`. -/
  d : ℕ
  /-- Precomputed `2 ^ d`. -/
  pow2d : ℕ
  /-- Number of unordered edge pairs `e.choose 2`. -/
  numPairs : ℕ
  /-- Base address of precomputed permutation MSF answers. -/
  permAns : ℕ
  /-- Precomputed `e ^ e`. -/
  powE : ℕ
  /-- Total number of skeletons `numPairs ^ (2 ^ d - 1)`. -/
  numSkels : ℕ
  deriving DecidableEq

/-- Twenty-eight-word encoding of `DTSkelEnv`. -/
word_enc_structure dtSkelEnvWords : DTSkelEnv where
  env : dtPrecompEnvWords, mask : wordWords, e : wordWords, d : wordWords,
  pow2d : wordWords, numPairs : wordWords, permAns : wordWords,
  powE : wordWords, numSkels : wordWords

instance : WordEncoding DTSkelEnv := ⟨28, dtSkelEnvWords⟩

private theorem geom_sum_pred_lt (B N : ℕ) (hB : 1 ≤ B) :
    ∑ k ∈ Finset.range N, (B - 1) * B ^ k < B ^ N := by
  rw [← Finset.mul_sum, mul_comm, geom_sum_mul_of_one_le hB]
  exact Nat.sub_lt (pow_pos (by omega) _) Nat.zero_lt_one

private def permCode {e : ℕ} (p : Equiv.Perm (Fin e)) : ℕ :=
  ∑ i ∈ Finset.range e, (if h : i < e then (p ⟨i, h⟩).val else 0) * e ^ i

private theorem permCode_lt {e : ℕ} (p : Equiv.Perm (Fin e)) : permCode p < e ^ e := by
  by_cases he : e = 0
  · subst he; simp only [permCode, Finset.range_zero, Finset.sum_empty, pow_zero, zero_lt_one]
  · refine Nat.lt_of_le_of_lt (Finset.sum_le_sum fun k _ => Nat.mul_le_mul_right _ ?_)
      (geom_sum_pred_lt e e (Nat.one_le_iff_ne_zero.mpr he))
    split_ifs with hk
    · exact Nat.le_pred_of_lt (p ⟨k, hk⟩).isLt
    · exact Nat.zero_le _

private theorem permCode_digit {e : ℕ} (p : Equiv.Perm (Fin e)) {i : ℕ} (hi : i < e) :
    (permCode p / e ^ i) % e = (p ⟨i, hi⟩).val := by
  have he : 1 ≤ e := by omega
  let f : ℕ → ℕ := fun k => if h : k < e then (p ⟨k, h⟩).val else 0
  let low : ℕ := ∑ k ∈ Finset.range i, f k * e ^ k
  let high : ℕ := ∑ k ∈ Finset.Ico (i + 1) e, f k * e ^ (k - (i + 1))
  have hlow : low < e ^ i := by
    refine Nat.lt_of_le_of_lt (Finset.sum_le_sum fun k hk => Nat.mul_le_mul_right _ ?_)
      (geom_sum_pred_lt e i he)
    have hke : k < e := (Finset.mem_range.mp hk).trans hi
    simpa only [f, hke, ↓reduceDIte] using Nat.le_sub_one_of_lt (p ⟨k, hke⟩).isLt
  have hhigh : ∑ k ∈ Finset.Ico (i + 1) e, f k * e ^ k = e * high * e ^ i := by
    simp only [high, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hki : i + 1 ≤ k := (Finset.mem_Ico.mp hk).1
    calc f k * e ^ k = f k * e ^ (k - (i + 1) + 1 + i) := by
          rw [show k - (i + 1) + 1 + i = k by omega]
      _ = e * (f k * e ^ (k - (i + 1))) * e ^ i := by
          rw [pow_add, pow_add, pow_one]; ring
  have hsplit : permCode p = low + ((p ⟨i, hi⟩).val + e * high) * e ^ i := by
    have h1 : permCode p = ∑ k ∈ Finset.range (i + 1), f k * e ^ k +
        ∑ k ∈ Finset.Ico (i + 1) e, f k * e ^ k :=
      (Finset.sum_range_add_sum_Ico (fun k => f k * e ^ k) (by omega : i + 1 ≤ e)).symm
    rw [h1, Finset.sum_range_succ, hhigh]
    have hfi : f i = (p ⟨i, hi⟩).val := by simp only [f, hi, ↓reduceDIte]
    dsimp only [low]; rw [hfi]; ring
  rw [hsplit, Nat.add_mul_div_right _ _ (pow_pos he i), Nat.div_eq_of_lt hlow, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (p ⟨i, hi⟩).isLt]

/-- Predicate characterizing base-`e` integers whose `e` digits are pairwise distinct. -/
@[expose] def CodeIsPerm (e code : ℕ) : Prop :=
  ∀ j₁ < e, ∀ j₂ < e, j₁ ≠ j₂ → (code / e ^ j₁) % e ≠ (code / e ^ j₂) % e

/-- Decode a valid base-`e` permutation integer `code` into `Equiv.Perm (Fin e)`. -/
@[expose] noncomputable def permOfCode {e : ℕ} (he : 1 ≤ e) (code : ℕ)
    (hcp : CodeIsPerm e code) : Equiv.Perm (Fin e) :=
  let f : Fin e → Fin e := fun i => ⟨(code / e ^ i.val) % e, Nat.mod_lt _ he⟩
  have hinj : Function.Injective f := fun i₁ i₂ h => by
    by_contra hne
    exact hcp i₁.val i₁.isLt i₂.val i₂.isLt (fun h12 => hne (Fin.ext h12)) (congrArg Fin.val h)
  Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, rfl⟩)

/-- Underlying `Nat` digit at index `i` of `permOfCode he code hcp`. -/
theorem permOfCode_apply_val {e : ℕ} (he : 1 ≤ e) (code : ℕ)
    (hcp : CodeIsPerm e code) (i : Fin e) :
    (permOfCode he code hcp i).val = (code / e ^ i.val) % e := rfl

private theorem codeIsPerm_permCode {e : ℕ} (p : Equiv.Perm (Fin e)) :
    CodeIsPerm e (permCode p) := fun j₁ hj₁ j₂ hj₂ hne h => by
  rw [permCode_digit p hj₁, permCode_digit p hj₂] at h
  exact hne (congrArg Fin.val (p.injective (Fin.ext h)))

private theorem permOfCode_permCode {e : ℕ} (he : 1 ≤ e) (p : Equiv.Perm (Fin e)) :
    permOfCode he (permCode p) (codeIsPerm_permCode p) = p := by
  ext ⟨i, hi⟩
  rw [permOfCode_apply_val, permCode_digit p hi]

/-- Self-power upper bounds `e ≤ e ^ e`, `e.choose 2 ≤ e ^ e`, and `e * (e - 1) ≤ e ^ e`
for `2 ≤ e`. -/
theorem dtPow_le_self_bounds {e : ℕ} (he : 2 ≤ e) :
    e ≤ e ^ e ∧ e.choose 2 ≤ e ^ e ∧ e * (e - 1) ≤ e ^ e := by
  have h1 : e ≤ e ^ e := Nat.le_self_pow (by omega) e
  have h2 : e.choose 2 ≤ e ^ e := by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self _ 2).trans ((Nat.mul_le_mul_left e (Nat.sub_le e 1)).trans
      (by rw [← sq]; exact Nat.pow_le_pow_right (by omega) he))
  have h3 : e * (e - 1) ≤ e ^ e := by
    rcases eq_or_ne e 2 with rfl | hne
    · decide
    · calc e * (e - 1) ≤ e * e := Nat.mul_le_mul_left e (Nat.sub_le e 1)
        _ = e ^ 2 := (sq e).symm
        _ ≤ e ^ e := Nat.pow_le_pow_right (by omega) (by omega)
  exact ⟨h1, h2, h3⟩

/-! ## Section 2: Layout Invariants, Skeleton Evaluation, and Tree-Entry Writers -/

/-- Exact contiguous scratch-workspace layout invariant for `env` ending at `wsEnd`. -/
@[expose] def DTEnvLayout (env : DTPrecompEnv) (wsEnd : ℕ) : Prop :=
  2 ≤ env.r0 ∧ env.maxE = env.r0.choose 2 ∧ env.numMasks = 2 ^ env.maxE ∧
  env.maxD = env.maxE.choose 2 ∧ env.bufA.tableBase + env.numMasks ≤ env.bufA.r0PairA ∧
  env.bufA.r0PairB = env.bufA.r0PairA + env.maxE ∧
  env.bufA.edgeU = env.bufA.r0PairB + env.maxE ∧
  env.bufA.edgeV = env.bufA.edgeU + env.maxE ∧
  env.bufA.edgePair = env.bufA.edgeV + env.maxE ∧
  env.bufB.allPairA = env.bufA.edgePair + env.maxE ∧
  env.bufB.allPairB = env.bufB.allPairA + env.maxD ∧
  env.bufB.leafAns = env.bufB.allPairB + env.maxD ∧
  env.bufB.leafSeen = env.bufB.leafAns + 2 ^ env.maxD ∧
  env.bufB.rankArr = env.bufB.leafSeen + 2 ^ env.maxD ∧
  env.bufB.orderArr = env.bufB.rankArr + env.maxE ∧
  env.bufC.seenArr = env.bufB.orderArr + env.maxE ∧
  env.bufC.compArr = env.bufC.seenArr + env.maxE ∧
  env.bufC.powEArr = env.bufC.compArr + env.r0 ∧
  env.bufC.powSkelArr = env.bufC.powEArr + (env.maxE + 1) ∧
  env.bufC.powSkelArr + 2 ^ env.maxD ≤ wsEnd

/-- Lower bound `2 ≤ env.r0` extracted from `DTEnvLayout`. -/
theorem DTEnvLayout.r0_ge {env : DTPrecompEnv} {wsEnd : ℕ}
    (h : DTEnvLayout env wsEnd) : 2 ≤ env.r0 := h.1

private theorem DTEnvLayout.maxE_pos {env : DTPrecompEnv} {wsEnd : ℕ}
    (h : DTEnvLayout env wsEnd) : 1 ≤ env.maxE := by
  have hr := h.1; rw [h.2.1, Nat.choose_two_right]
  exact Nat.div_pos (Nat.mul_le_mul hr (Nat.sub_le_sub_right hr 1)) (by decide)

/-- Address ordering and non-overlap bounds for `bufA` edge arrays in `DTEnvLayout`. -/
theorem DTEnvLayout.edges_bounds {env : DTPrecompEnv} {wsEnd : ℕ}
    (h : DTEnvLayout env wsEnd) :
    env.bufA.tableBase + env.numMasks ≤ env.bufA.r0PairA ∧
    env.bufA.r0PairA + env.maxE ≤ env.bufA.r0PairB ∧
    env.bufA.r0PairB + env.maxE ≤ env.bufA.edgeU ∧
    env.bufA.edgeU + env.maxE ≤ env.bufA.edgeV ∧
    env.bufA.edgeV + env.maxE ≤ env.bufA.edgePair ∧
    env.bufA.edgePair + env.maxE ≤ env.bufB.allPairA ∧
    env.bufA.edgePair + env.maxE ≤ env.bufC.powEArr ∧
    env.bufA.edgePair + env.maxE ≤ env.bufB.leafSeen ∧
    env.bufA.edgePair + env.maxE ≤ wsEnd ∧
    env.bufA.r0PairB + env.maxE ≤ env.bufC.powEArr := by
  rcases h with ⟨_, _, _, _, htb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  have hp2d : 1 ≤ 2 ^ env.maxD := Nat.one_le_two_pow
  have hp2e : 1 ≤ 2 ^ env.maxE := Nat.one_le_two_pow
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Address ordering and non-overlap bounds for `bufB` and table regions in `DTEnvLayout`. -/
theorem DTEnvLayout.buf_bounds {env : DTPrecompEnv} {wsEnd : ℕ}
    (h : DTEnvLayout env wsEnd) :
    1 ≤ 2 ^ env.maxD ∧ 1 ≤ 2 ^ env.maxE ∧
    env.bufA.tableBase + env.numMasks ≤ env.bufB.allPairA ∧
    env.bufA.tableBase + env.numMasks ≤ env.bufB.leafSeen ∧
    env.bufA.tableBase + env.numMasks ≤ env.bufC.powEArr ∧
    env.bufA.tableBase + env.numMasks ≤ wsEnd ∧
    env.bufB.allPairA + env.maxD ≤ env.bufB.allPairB ∧
    env.bufB.allPairB + env.maxD ≤ env.bufB.leafAns ∧
    env.bufB.allPairB + env.maxD ≤ env.bufB.leafSeen ∧
    env.bufB.allPairB + env.maxD ≤ env.bufC.powEArr ∧
    env.bufB.allPairB + env.maxD ≤ env.bufC.powSkelArr ∧
    env.bufB.allPairB + env.maxD ≤ wsEnd ∧
    env.bufB.leafAns + 2 ^ env.maxD ≤ env.bufB.leafSeen ∧
    env.bufB.leafSeen + 2 ^ env.maxD ≤ env.bufB.rankArr ∧
    env.bufB.leafSeen + 2 ^ env.maxD ≤ env.bufC.powEArr ∧
    env.bufB.leafSeen + 2 ^ env.maxD ≤ env.bufC.powSkelArr ∧
    env.bufB.leafSeen + 2 ^ env.maxD ≤ wsEnd := by
  rcases h with ⟨_, _, _, _, htb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  have hp2d : 1 ≤ 2 ^ env.maxD := Nat.one_le_two_pow
  have hp2e : 1 ≤ 2 ^ env.maxE := Nat.one_le_two_pow
  refine ⟨hp2d, hp2e, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Address ordering and non-overlap bounds for `bufC` scratch arrays in `DTEnvLayout`. -/
theorem DTEnvLayout.work_bounds {env : DTPrecompEnv} {wsEnd : ℕ}
    (h : DTEnvLayout env wsEnd) :
    env.bufB.rankArr + env.maxE ≤ env.bufB.orderArr ∧
    env.bufB.orderArr + env.maxE ≤ env.bufC.seenArr ∧
    env.bufC.seenArr + env.maxE ≤ env.bufC.compArr ∧
    env.bufC.compArr + env.r0 ≤ env.bufC.powEArr ∧
    env.bufC.powEArr + (env.maxE + 1) ≤ env.bufC.powSkelArr ∧
    env.bufC.powSkelArr + 2 ^ env.maxD ≤ wsEnd ∧
    env.bufC.powEArr + (env.maxE + 1) ≤ wsEnd ∧
    env.bufB.leafAns + 2 ^ env.maxD ≤ env.bufC.powSkelArr ∧
    env.bufA.edgeU ≤ env.bufB.allPairA ∧
    env.bufA.edgePair + env.maxE ≤ env.bufB.leafAns ∧
    env.bufB.allPairB + env.maxD ≤ env.bufB.rankArr := by
  rcases h with ⟨_, _, _, _, htb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  have hp2d : 1 ≤ 2 ^ env.maxD := Nat.one_le_two_pow
  have hp2e : 1 ≤ 2 ^ env.maxE := Nat.one_le_two_pow
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Per-mask table-entry correctness and frontier-bounds invariant at depth `d`. -/
@[expose] def DTMaskEntryValid (r0 tableBase mask d : ℕ) (s : Memory.State) : Prop :=
  let entryPtr := s.mem (tableBase + mask)
  let pairs := maskEdgePairs r0 mask
  let e := pairs.length
  let intBase := entryPtr + 2 + e
  let leafBase := intBase + 2 * (2 ^ d - 1)
  s.mem entryPtr = e ∧ s.mem (entryPtr + 1) = d ∧
  (∀ j (hj : j < e), s.mem (entryPtr + 2 + j) = pairIdx (pairs[j]).1.val (pairs[j]).2.val) ∧
  (∃ T : MSFDT e, T.IsComplete d ∧ T.Correct (endsOfMask r0 mask) ∧
    HoldsCompleteTree d intBase leafBase d 1 s.mem T) ∧
  entryPtr + 2 + e + 2 * (2 ^ d - 1) + 2 ^ d ≤ s.frontier

/-- Preserves `DTMaskEntryValid` when the entry pointer and memory block `[entryPtr, frontier)`
remain unchanged. -/
theorem dtMaskEntryValid_preserve {r0 tableBase mask d : ℕ} {s₁ s₂ : Memory.State}
    (hv : DTMaskEntryValid r0 tableBase mask d s₁) (hfr : s₁.frontier ≤ s₂.frontier)
    (hptr : s₂.mem (tableBase + mask) = s₁.mem (tableBase + mask))
    (hent : ∀ a, s₁.mem (tableBase + mask) ≤ a → a < s₁.frontier → s₂.mem a = s₁.mem a) :
    DTMaskEntryValid r0 tableBase mask d s₂ := by
  dsimp only [DTMaskEntryValid] at hv ⊢
  rcases hv with ⟨he, hd, hep, ⟨T, hc, hcor, hh⟩, hbd⟩
  have h2d : 1 ≤ 2 ^ d := Nat.two_pow_pos d
  rw [hptr]
  refine ⟨by rw [hent _ le_rfl (by omega), he], by rw [hent _ (by omega) (by omega), hd],
    fun j hj => by rw [hent _ (by omega) (by omega), hep j hj], ⟨T, hc, hcor, ?_⟩, by omega⟩
  exact HoldsCompleteTree.congr (fun k _ _ => hent _ (by omega) (by omega))
    (fun l _ _ => hent _ (by omega) (by omega)) le_rfl le_rfl (by simp) hh

/-- Per-mask precomputed input invariant holding `e`-powers, pair tables, edge indices, and
the `e ^ e` permutation MSF table in `permAns`. -/
@[expose] def DTMaskIn (env : DTPrecompEnv) {mask e : ℕ}
    (he_eq : e = (maskEdgePairs env.r0 mask).length) (permAns : ℕ) (he1 : 1 ≤ e)
    (s : Memory.State) : Prop :=
  (∀ j ≤ e, s.mem (env.bufC.powEArr + j) = e ^ j) ∧
  (∀ pk (hpk : pk < e.choose 2),
    s.mem (env.bufB.allPairA + pk) =
      ((allPairs e)[pk]'(by rw [length_allPairs]; exact hpk)).1.val ∧
    s.mem (env.bufB.allPairB + pk) =
      ((allPairs e)[pk]'(by rw [length_allPairs]; exact hpk)).2.val) ∧
  (∀ j (hj : j < (maskEdgePairs env.r0 mask).length),
    s.mem (env.bufA.edgePair + j) =
      pairIdx (maskEdgePairs env.r0 mask)[j].1.val (maskEdgePairs env.r0 mask)[j].2.val) ∧
  (∀ code < e ^ e,
    (s.mem (permAns + code) = 0 ↔ ¬CodeIsPerm e code) ∧
    ∀ hcp : CodeIsPerm e code,
      let p := permOfCode he1 code hcp
      let σ : Fin e ≃ Fin (maskEdgePairs env.r0 mask).length := (Fin.castOrderIso he_eq).toEquiv
      let p' : Equiv.Perm (Fin (maskEdgePairs env.r0 mask).length) := σ.symm.trans (p.trans σ)
      s.mem (permAns + code) =
        maskOfFinset (Cslib.Multigraph.msf (endsOfMask env.r0 mask) p' Finset.univ) + 1)

/-- Frame preservation for `DTMaskIn` across any `Memory.Modifies S` disjoint from the mask's
read-only tables. -/
theorem dtMaskIn_of_modifies {env : DTPrecompEnv} {mask e permAns : ℕ}
    {he_eq : e = (maskEdgePairs env.r0 mask).length} {he1 : 1 ≤ e}
    {S : Set ℕ} {s₁ s₂ : Memory.State} (hm : DTMaskIn env he_eq permAns he1 s₁)
    (hmod : Memory.Modifies S s₁ s₂)
    (hpe_f : env.bufC.powEArr + (e + 1) ≤ s₁.frontier)
    (hpa_f : env.bufB.allPairA + e.choose 2 ≤ s₁.frontier)
    (hpb_f : env.bufB.allPairB + e.choose 2 ≤ s₁.frontier)
    (hep_f : env.bufA.edgePair + e ≤ s₁.frontier)
    (hpm_f : permAns + e ^ e ≤ s₁.frontier)
    (hdisj : ∀ a,
      ((env.bufC.powEArr ≤ a ∧ a < env.bufC.powEArr + (e + 1)) ∨
       (env.bufB.allPairA ≤ a ∧ a < env.bufB.allPairA + e.choose 2) ∨
       (env.bufB.allPairB ≤ a ∧ a < env.bufB.allPairB + e.choose 2) ∨
       (env.bufA.edgePair ≤ a ∧ a < env.bufA.edgePair + e) ∨
       (permAns ≤ a ∧ a < permAns + e ^ e)) → a ∉ S) :
    DTMaskIn env he_eq permAns he1 s₂ :=
  ⟨fun j hj => (hmod.mem_eq_of_not_mem (by omega)
      (hdisj _ (Or.inl ⟨by omega, by omega⟩))).trans (hm.1 j hj),
   fun pk hpk => ⟨(hmod.mem_eq_of_not_mem (by omega)
      (hdisj _ (Or.inr (Or.inl ⟨by omega, by omega⟩)))).trans (hm.2.1 pk hpk).1,
     (hmod.mem_eq_of_not_mem (by omega)
      (hdisj _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))).trans (hm.2.1 pk hpk).2⟩,
   fun j hj => (hmod.mem_eq_of_not_mem (by have := he_eq ▸ hj; omega)
      (hdisj _ (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨by have := he_eq ▸ hj; omega, by have := he_eq ▸ hj; omega⟩)))))).trans (hm.2.2.1 j hj),
   fun code hc => by
     rw [hmod.mem_eq_of_not_mem (by omega)
       (hdisj _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))))]
     exact hm.2.2.2 code hc⟩

private def dtEvalSkelWalkStep (x : DTSkelWalkEnv × ℕ) : Memory.Prog ℕ := do
  let pw ← Memory.read (x.1.powSkelArr + (x.2 - 1))
  let pk := (x.1.skelCode / pw) % x.1.numPairs
  let a ← Memory.read (x.1.allPairA + pk)
  let b ← Memory.read (x.1.allPairB + pk)
  let pwa ← Memory.read (x.1.powEArr + a)
  let pwb ← Memory.read (x.1.powEArr + b)
  if (x.1.code / pwa) % x.1.e < (x.1.code / pwb) % x.1.e then
    pure (2 * x.2)
  else
    pure (2 * x.2 + 1)

private def dtEvalSkelWalkStepSafe (w : ℕ) (x : DTSkelWalkEnv × ℕ)
    (s : Memory.State) : Prop :=
  let pw := s.mem (x.1.powSkelArr + (x.2 - 1))
  let pk := (x.1.skelCode / pw) % x.1.numPairs
  let a := s.mem (x.1.allPairA + pk)
  let b := s.mem (x.1.allPairB + pk)
  Fits w 2 ∧ 1 ≤ x.2 ∧ 1 ≤ x.1.numPairs ∧ 1 ≤ x.1.e ∧ Fits w (2 * x.2 + 1) ∧
  pw ≠ 0 ∧ s.mem (x.1.powEArr + a) ≠ 0 ∧ s.mem (x.1.powEArr + b) ≠ 0 ∧
  (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (dtEvalSkelWalkStep x))

private theorem realizes_dtEvalSkelWalkStep : Realizes .exact
    dtEvalSkelWalkStep (appendWords dtSkelWalkEnvWords WordEncoding.encode)
    WordEncoding.encode dtEvalSkelWalkStepSafe (fun _ _ => 0) := by
  unfold dtEvalSkelWalkStep
  realize
  all_goals
    obtain ⟨h2, h1, hnp, he, h2n, hpw, hpa, hpb, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [dtEvalSkelWalkStep, StateTransitionSpec.clientHistory] at hv
    simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.read, Memory.step_read, Memory.valid] at hv
    first | exact hpw | exact hpa | exact hpb | omega | fits [h2n]

private theorem dtEvalSkelWalk_loop_spec {w powSkelArr allPairA allPairB powEArr e d skelCode
    code : ℕ} {s : Memory.State} (h2 : Fits w 2) (hwf : Memory.WellFormed w s)
    (he2 : 2 ≤ e) (h2d1_fit : Fits w (2 ^ (d + 1)))
    (hps : powSkelArr + (2 ^ d - 1) ≤ s.frontier) (haa : allPairA + e.choose 2 ≤ s.frontier)
    (hab : allPairB + e.choose 2 ≤ s.frontier) (hpe : powEArr + e ≤ s.frontier)
    (hpows : ∀ k ≤ 2 ^ d - 1, s.mem (powSkelArr + k) = (e.choose 2) ^ k)
    (hpowe : ∀ j ≤ e, s.mem (powEArr + j) = e ^ j)
    (hpairs_e : ∀ pk (hpk : pk < e.choose 2),
      s.mem (allPairA + pk) = ((allPairs e)[pk]'(by rw [length_allPairs]; exact hpk)).1.val ∧
      s.mem (allPairB + pk) = ((allPairs e)[pk]'(by rw [length_allPairs]; exact hpk)).2.val)
    (hcp : CodeIsPerm e code) :
    let wEnv : DTSkelWalkEnv :=
      ⟨allPairA, allPairB, powSkelArr, powEArr, e.choose 2, e, skelCode, code⟩
    let prog := iterate dtEvalSkelWalkStep wEnv d 1
    iterationSafe dtEvalSkelWalkStep dtEvalSkelWalkStepSafe w wEnv d 1 s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    memoryCost prog s ≤ 5 * d ∧
    (Memory.spec 0).clientResult s prog =
      walkSkelNode e he2 skelCode d 1 (permOfCode (by omega : 1 ≤ e) code hcp) ∧
    (Memory.spec 0).clientState s prog = s := by
  let p := permOfCode (by omega : 1 ≤ e) code hcp
  let wEnv : DTSkelWalkEnv :=
    ⟨allPairA, allPairB, powSkelArr, powEArr, e.choose 2, e, skelCode, code⟩
  have hnp_pos : 1 ≤ e.choose 2 := Nat.choose_pos he2
  let inv (k node : ℕ) (t : Memory.State) : Prop := t = s ∧ 1 ≤ node ∧ node < 2 ^ (k + 1) ∧
    walkSkelNode e he2 skelCode (d - k) node p = walkSkelNode e he2 skelCode d 1 p
  have hstep : ∀ k < d, ∀ node t, inv k node t →
      dtEvalSkelWalkStepSafe w (wEnv, node) t ∧
      Memory.FramedTriple w t (dtEvalSkelWalkStep (wEnv, node)) 5 ∅ (inv (k + 1)) := by
    intro k hk node t ⟨ht_eq, h1_node, hnode_lt, hwalk⟩; subst ht_eq
    have hpow_le : 2 ^ (k + 1) ≤ 2 ^ d := Nat.pow_le_pow_right (by decide) hk
    have hpw : t.mem (powSkelArr + (node - 1)) = (e.choose 2) ^ (node - 1) :=
      hpows (node - 1) (by omega)
    have hpw_nz : t.mem (powSkelArr + (node - 1)) ≠ 0 := by
      rw [hpw]; exact Nat.ne_of_gt (Nat.pow_pos hnp_pos)
    let pk := (skelCode / t.mem (powSkelArr + (node - 1))) % e.choose 2
    have hpk_lt : pk < e.choose 2 := Nat.mod_lt _ hnp_pos
    let pr := (allPairs e)[pk]'(by rw [length_allPairs]; exact hpk_lt)
    have hpa_eq : t.mem (allPairA + pk) = pr.1.val := (hpairs_e pk hpk_lt).1
    have hpb_eq : t.mem (allPairB + pk) = pr.2.val := (hpairs_e pk hpk_lt).2
    have h2n1_fit : Fits w (2 * node + 1) := h2d1_fit.of_le (by
      calc 2 * node + 1 ≤ 2 ^ (k + 1 + 1) := by rw [Nat.pow_succ']; omega
        _ ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by decide) (by omega))
    have hpk_all : pk < (allPairs e).length := by rw [length_allPairs]; exact hpk_lt
    have htri_pre : Memory.FramedTriple w t (dtEvalSkelWalkStep (wEnv, node)) 5 ∅ fun a' t' =>
        t' = t ∧ a' = if (p pr.1).val < (p pr.2).val then 2 * node else 2 * node + 1 := by
      dsimp only [dtEvalSkelWalkStep, wEnv]
      refine Memory.FramedTriple.read_bind (by omega) ?_
      change Memory.FramedTriple w t (Memory.read (allPairA + pk) >>= fun a =>
        Memory.read (allPairB + pk) >>= fun b =>
          Memory.read (powEArr + a) >>= fun pwa => Memory.read (powEArr + b) >>= fun pwb => _)
        4 ∅ _
      refine Memory.FramedTriple.read_bind (by omega) ?_; rw [hpa_eq]
      refine Memory.FramedTriple.read_bind (by omega) ?_; rw [hpb_eq]
      refine Memory.FramedTriple.read_bind (by have := pr.1.isLt; omega) ?_
      refine Memory.FramedTriple.read_bind (by have := pr.2.isLt; omega) ?_
      rw [hpowe pr.1.val pr.1.isLt.le, hpowe pr.2.val pr.2.isLt.le]
      have h1 : (code / e ^ pr.1.val) % e = (p pr.1).val := rfl
      have h2' : (code / e ^ pr.2.val) % e = (p pr.2).val := rfl
      rw [h1, h2']
      split_ifs <;> exact Memory.FramedTriple.pure ⟨rfl, rfl⟩
    have hwalk_unfold : walkSkelNode e he2 skelCode (d - k) node p =
        if (p pr.1).val < (p pr.2).val then
          walkSkelNode e he2 skelCode (d - (k + 1)) (2 * node) p
        else walkSkelNode e he2 skelCode (d - (k + 1)) (2 * node + 1) p := by
      rw [show d - k = (d - (k + 1)) + 1 by omega]
      dsimp only [walkSkelNode]
      rw [show (skelCode / (e.choose 2) ^ (node - 1)) % e.choose 2 = pk from
        by dsimp only [pk]; rw [hpw]]
      simp only [hpk_all, ↓reduceDIte, pr]
    have htri : Memory.FramedTriple w t (dtEvalSkelWalkStep (wEnv, node)) 5 ∅ (inv (k + 1)) :=
      htri_pre.mono le_rfl fun a' t' ⟨ht't, ha'⟩ => by
        subst ht't
        refine ⟨rfl, by split_ifs at ha' <;> omega,
          by rw [Nat.pow_succ']; split_ifs at ha' <;> omega, ?_⟩
        rw [← hwalk, hwalk_unfold]
        split_ifs at ha' ⊢ with hltp <;> simp_all
    exact ⟨⟨h2, h1_node, hnp_pos, by dsimp only [wEnv]; omega, h2n1_fit, hpw_nz,
        by have := pr.1.isLt; dsimp only [wEnv]; rw [hpa_eq, hpowe pr.1.val pr.1.isLt.le]
           exact Nat.ne_of_gt (Nat.pow_pos (by omega)),
        by have := pr.2.isLt; dsimp only [wEnv]; rw [hpb_eq, hpowe pr.2.val pr.2.isLt.le]
           exact Nat.ne_of_gt (Nat.pow_pos (by omega)),
        (framedTriple_iff_realization.mp htri).1⟩, htri⟩
  obtain ⟨hs, hv, hc, _, hst_end, _, _, hw_end⟩ := iterate_potential_spec dtEvalSkelWalkStep
    dtEvalSkelWalkStepSafe w wEnv 5 d inv (fun _ _ _ => 0) ∅
    (fun k hk a s ha => let ⟨hs', ht'⟩ := hstep k hk a s ha
      let ⟨hv', hc', hm', hi'⟩ := framedTriple_iff_realization.mp ht'
      ⟨hs', hv', by omega, hm', hi'⟩)
    1 s ⟨rfl, le_rfl, by rw [Nat.pow_one]; decide, rfl⟩
  exact ⟨hs, hv, by simpa only [Nat.add_zero, Nat.zero_add, Nat.mul_comm] using hc,
    by simpa [walkSkelNode] using hw_end, hst_end⟩

private def dtLeafUpdate (x : DTCheckPermEnv × ℕ × ℕ × ℕ) : Memory.Prog (ℕ × ℕ) := do
  let seen ← Memory.read (x.1.env.bufB.leafSeen + x.2.2.1)
  if seen = 0 then
    Memory.write (x.1.env.bufB.leafSeen + x.2.2.1) 1
    Memory.write (x.1.env.bufB.leafAns + x.2.2.1) (x.2.2.2 - 1)
    pure (x.2.1 + 1, 1)
  else
    let cur ← Memory.read (x.1.env.bufB.leafAns + x.2.2.1)
    pure (x.2.1 + 1, if cur = x.2.2.2 - 1 then 1 else 0)

private def dtLeafUpdateSafe (w : ℕ) (x : DTCheckPermEnv × ℕ × ℕ × ℕ) (s : Memory.State) : Prop :=
  Fits w 2 ∧ 1 ≤ x.2.2.2 ∧ Fits w (x.2.1 + 1) ∧
  (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (dtLeafUpdate x))

private theorem realizes_dtLeafUpdate : Realizes .exact
    dtLeafUpdate (appendWords dtCheckPermEnvWords WordEncoding.encode)
    WordEncoding.encode dtLeafUpdateSafe (fun _ _ => 0) := by
  unfold dtLeafUpdate
  realize
  all_goals
    obtain ⟨h2, hpa, hidx, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [dtLeafUpdate, StateTransitionSpec.clientHistory] at hv
    by_cases h0 : s.mem (d.1.env.bufB.leafSeen + d.2.2.1) = 0
    · simp only [h0, ↓reduceIte, StateTransitionSpec.runClient_lift_bind',
        StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
        Memory.write, Memory.step_read, Memory.step_write, Memory.valid] at hv
      first | exact hpa | fits
    · simp only [h0, ↓reduceIte, StateTransitionSpec.runClient_lift_bind',
        StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
        Memory.step_read, Memory.valid] at hv
      first | exact hpa | fits

private theorem dtLeafUpdate_spec {w : ℕ} {cenv : DTCheckPermEnv} {idx l pa : ℕ}
    {s : Memory.State} (h2 : Fits w 2) (hwf : Memory.WellFormed w s)
    (hpa1 : 1 ≤ pa) (hpa_fit : Fits w pa) (hidx_fit : Fits w (idx + 1))
    (hls_lt : cenv.env.bufB.leafSeen + l < s.frontier)
    (hla_lt : cenv.env.bufB.leafAns + l < s.frontier)
    (hdisj : cenv.env.bufB.leafAns + l ≠ cenv.env.bufB.leafSeen + l) :
    let S := ({cenv.env.bufB.leafSeen + l, cenv.env.bufB.leafAns + l} : Set ℕ)
    dtLeafUpdateSafe w (cenv, idx, l, pa) s ∧
    Memory.FramedTriple w s (dtLeafUpdate (cenv, idx, l, pa)) 3 S fun res s' =>
      s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
      (∀ a < s.frontier, a ≠ cenv.env.bufB.leafSeen + l → a ≠ cenv.env.bufB.leafAns + l →
        s'.mem a = s.mem a) ∧
      (s.mem (cenv.env.bufB.leafSeen + l) = 0 →
        res = (idx + 1, 1) ∧ s'.mem (cenv.env.bufB.leafSeen + l) = 1 ∧
        s'.mem (cenv.env.bufB.leafAns + l) = pa - 1) ∧
      (s.mem (cenv.env.bufB.leafSeen + l) ≠ 0 →
        s' = s ∧ res = if s.mem (cenv.env.bufB.leafAns + l) = pa - 1
          then (idx + 1, 1) else (idx + 1, 0)) := by
  let S : Set ℕ := {cenv.env.bufB.leafSeen + l, cenv.env.bufB.leafAns + l}
  have htri_raw : Memory.FramedTriple w s (dtLeafUpdate (cenv, idx, l, pa)) 3 S fun res s' =>
      s'.frontier = s.frontier ∧
      (∀ a < s.frontier, a ≠ cenv.env.bufB.leafSeen + l → a ≠ cenv.env.bufB.leafAns + l →
        s'.mem a = s.mem a) ∧
      (s.mem (cenv.env.bufB.leafSeen + l) = 0 →
        res = (idx + 1, 1) ∧ s'.mem (cenv.env.bufB.leafSeen + l) = 1 ∧
        s'.mem (cenv.env.bufB.leafAns + l) = pa - 1) ∧
      (s.mem (cenv.env.bufB.leafSeen + l) ≠ 0 →
        s' = s ∧ res = if s.mem (cenv.env.bufB.leafAns + l) = pa - 1
          then (idx + 1, 1) else (idx + 1, 0)) := by
    dsimp only [dtLeafUpdate]; rw [show (3 : ℕ) = 2 + 1 by omega]
    refine Memory.FramedTriple.read_bind hls_lt (Memory.FramedTriple.ite (c := 2) ?_ ?_)
    · intro h0
      refine Memory.FramedTriple.write_bind_of_mem hls_lt (by fits) (Set.mem_insert _ _) ?_
      refine Memory.FramedTriple.write_bind_of_mem (by dsimp only; omega)
        (hpa_fit.of_le (by omega)) (Set.mem_insert_of_mem _ (Set.mem_singleton _)) ?_
      refine Memory.FramedTriple.pure ⟨rfl, fun a _ ha1 ha2 => by update_simp,
          fun _ => ⟨rfl, by
            dsimp only; rw [Function.update_of_ne hdisj.symm, Function.update_self],
            by dsimp only; exact Function.update_self _ _ _⟩, fun hne => absurd h0 hne⟩
    · intro hne
      refine Memory.FramedTriple.mono (Memory.FramedTriple.read_bind (c := 0) hla_lt ?_)
        (by omega) fun _ _ h => h
      split_ifs with hcur <;> exact Memory.FramedTriple.pure ⟨rfl, fun _ _ _ _ => rfl,
        fun h0 => absurd h0 hne, fun _ => ⟨rfl, rfl⟩⟩
  have htri : Memory.FramedTriple w s (dtLeafUpdate (cenv, idx, l, pa)) 3 S fun res s' =>
      s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
      (∀ a < s.frontier, a ≠ cenv.env.bufB.leafSeen + l → a ≠ cenv.env.bufB.leafAns + l →
        s'.mem a = s.mem a) ∧
      (s.mem (cenv.env.bufB.leafSeen + l) = 0 →
        res = (idx + 1, 1) ∧ s'.mem (cenv.env.bufB.leafSeen + l) = 1 ∧
        s'.mem (cenv.env.bufB.leafAns + l) = pa - 1) ∧
      (s.mem (cenv.env.bufB.leafSeen + l) ≠ 0 →
        s' = s ∧ res = if s.mem (cenv.env.bufB.leafAns + l) = pa - 1
          then (idx + 1, 1) else (idx + 1, 0)) :=
    (htri_raw.wellFormed hwf).mono le_rfl fun _ _ ⟨⟨hfr, hmod, h0, hne⟩, hwf'⟩ =>
      ⟨hfr, hwf', hmod, h0, hne⟩
  exact ⟨⟨h2, hpa1, hidx_fit, (framedTriple_iff_realization.mp htri).1⟩, htri⟩

private def dtCheckOnePermStep (x : DTCheckPermEnv × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let pa ← Memory.read (x.1.permAns + x.2.1)
  if x.2.2 = 0 then pure (x.2.1 + 1, 0)
  else if pa = 0 then pure (x.2.1 + 1, 1)
  else
    let node ← iterate dtEvalSkelWalkStep
      ⟨x.1.env.bufB.allPairA, x.1.env.bufB.allPairB, x.1.env.bufC.powSkelArr,
        x.1.env.bufC.powEArr, x.1.numPairs, x.1.e, x.1.skelCode, x.2.1⟩ x.1.d 1
    dtLeafUpdate (x.1, x.2.1, node - x.1.pow2d, pa)

private def dtCheckOnePermStepSafe (w : ℕ) (x : DTCheckPermEnv × (ℕ × ℕ))
    (s : Memory.State) : Prop :=
  let pa := s.mem (x.1.permAns + x.2.1)
  let wEnv : DTSkelWalkEnv := ⟨x.1.env.bufB.allPairA, x.1.env.bufB.allPairB,
    x.1.env.bufC.powSkelArr, x.1.env.bufC.powEArr, x.1.numPairs, x.1.e, x.1.skelCode, x.2.1⟩
  let node := (Memory.spec 0).clientResult s (iterate dtEvalSkelWalkStep wEnv x.1.d 1)
  Fits w 2 ∧ Fits w (x.2.1 + 1) ∧ x.1.permAns + x.2.1 < s.frontier ∧
  (x.2.2 ≠ 0 → pa ≠ 0 →
    x.1.pow2d ≤ node ∧
    iterationSafe dtEvalSkelWalkStep dtEvalSkelWalkStepSafe w wEnv x.1.d 1 s ∧
    dtLeafUpdateSafe w (x.1, x.2.1, node - x.1.pow2d, pa)
      ((Memory.spec 0).clientState s (iterate dtEvalSkelWalkStep wEnv x.1.d 1)))

private theorem realizes_dtCheckOnePermStep : Realizes .exact
    dtCheckOnePermStep (appendWords dtCheckPermEnvWords WordEncoding.encode)
    WordEncoding.encode dtCheckOnePermStepSafe (fun _ _ => 0) := by
  unfold dtCheckOnePermStep
  realize [realizes_dtEvalSkelWalkStep, realizes_dtLeafUpdate]
  all_goals
    obtain ⟨h2, hidx, hlt, hbr⟩ := h
    have hfront := hmem.frontier_fits
    first
    | exact (hbr (by tauto) (by tauto)).1
    | exact iterationSafe_imp (hbr (by tauto) (by tauto)).2.1 (fun _ => rfl) (fun _ _ hs => hs)
    | exact (hbr (by tauto) (by tauto)).2.2
    | fits

/-- Clears `leafSeen` and `leafAns`, then evaluates candidate skeleton `d.1.skelCode` across
`0 .. d.2 - 1` by reading stored answers from `d.1.permAns` (using `0` as a skip marker) and
checking leaf consistency in `leafSeen`/`leafAns`; returns `1` iff no two nonzero `permAns`
entries reaching the same leaf disagree. Under the hypotheses of `dtTestSkelProg_spec`
(precomputed permutation-answer table `DTMaskIn`, disjoint `DTEnvLayout` workspace, initialized
power tables `powEArr`/`powSkelArr`, and `d.2 = e ^ e`), returns `1` iff `skelCode` uniquely
determines `Cslib.Multigraph.msf` at every leaf (and writes leaf MSF masks to `leafAns`). -/
def dtTestSkelProg (d : DTCheckPermEnv × ℕ) : Memory.Prog ℕ := do
  let _ ← fillConstProg d.1.env.bufB.leafSeen 0 d.1.pow2d
  let _ ← fillConstProg d.1.env.bufB.leafAns 0 d.1.pow2d
  let res ← iterate dtCheckOnePermStep d.1 d.2 (0, 1)
  pure res.2

/-- Word-RAM safety precondition for `dtTestSkelProg`. -/
def dtTestSkelProgSafe (w : ℕ) (d : DTCheckPermEnv × ℕ) (s : Memory.State) : Prop :=
  let s1 := (Memory.spec 0).clientState s (fillConstProg d.1.env.bufB.leafSeen 0 d.1.pow2d)
  let s2 := (Memory.spec 0).clientState s1 (fillConstProg d.1.env.bufB.leafAns 0 d.1.pow2d)
  Fits w 2 ∧ Fits w d.1.pow2d ∧
  d.1.env.bufB.leafSeen + d.1.pow2d ≤ s.frontier ∧
  d.1.env.bufB.leafAns + d.1.pow2d ≤ s1.frontier ∧
  iterationSafe dtCheckOnePermStep dtCheckOnePermStepSafe w d.1 d.2 (0, 1) s2

/-- Uniform `Realizes .exact` certificate for `dtTestSkelProg` with `work = 0`. -/
theorem realizes_dtTestSkelProg : Realizes .exact
    dtTestSkelProg (appendWords dtCheckPermEnvWords WordEncoding.encode)
    WordEncoding.encode dtTestSkelProgSafe (fun _ _ => 0) := by
  unfold dtTestSkelProg
  realize [realizes_fillConstProg, realizes_dtCheckOnePermStep]
  all_goals
    obtain ⟨h2, hp2d, hls, hla, hchk⟩ := h
    have hfront := hmem.frontier_fits
    first
    | exact hls
    | exact hla
    | exact iterationSafe_imp hchk (fun _ => rfl) (fun _ _ hs => hs)
    | fits

/-- Framed specification of `dtTestSkelProg`: given a disjoint `DTEnvLayout` workspace,
initialized `powSkelArr` power table, precomputed `DTMaskIn` permutation-answer table, and full
`e ^ e` range, proves `dtTestSkelProg` returns `1` whenever `skelCode` determines
`Cslib.Multigraph.msf` at every leaf, and when `res = 1` writes each permutation's
`maskOfFinset` MSF mask into `leafAns`. -/
theorem dtTestSkelProg_spec {w baseFront mask e d permAns skelCode : ℕ}
    {env : DTPrecompEnv} {s : Memory.State}
    (h2 : Fits w 2) (hwf : Memory.WellFormed w s)
    (hlay : DTEnvLayout env baseFront) (hbf : baseFront ≤ permAns)
    (hpa_lt : permAns + e ^ e ≤ s.frontier)
    (he2 : 2 ≤ e) (he_le : e ≤ env.maxE) (he_eq : e = (maskEdgePairs env.r0 mask).length)
    (hd_le : d ≤ env.maxD) (hfit_ee : Fits w (e ^ e + 1))
    (hpows : ∀ k ≤ 2 ^ d - 1, s.mem (env.bufC.powSkelArr + k) = (e.choose 2) ^ k)
    (hm_in : DTMaskIn env he_eq permAns (by omega) s) :
    let cEnv : DTCheckPermEnv := ⟨env, e, d, 2 ^ d, e.choose 2, permAns, skelCode⟩
    let prog := dtTestSkelProg (cEnv, e ^ e)
    let S := Set.Ico env.bufB.leafSeen (env.bufB.leafSeen + 2 ^ d) ∪
      Set.Ico env.bufB.leafAns (env.bufB.leafAns + 2 ^ d)
    dtTestSkelProgSafe w (cEnv, e ^ e) s ∧
    Memory.FramedTriple w s prog (2 * 2 ^ d + e ^ e * (4 + 5 * d)) S fun res s' =>
      (res = 0 ∨ res = 1) ∧ s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
      (∀ l < 2 ^ d, s'.mem (env.bufB.leafAns + l) < 2 ^ e) ∧
      (res = 1 → ∀ p : Equiv.Perm (Fin e),
        let σ : Fin e ≃ Fin (maskEdgePairs env.r0 mask).length := (Fin.castOrderIso he_eq).toEquiv
        let p' : Equiv.Perm (Fin (maskEdgePairs env.r0 mask).length) := σ.symm.trans (p.trans σ)
        s'.mem (env.bufB.leafAns + (walkSkelNode e he2 skelCode d 1 p - 2 ^ d)) =
          maskOfFinset (Cslib.Multigraph.msf (endsOfMask env.r0 mask) p' Finset.univ)) ∧
      ((∀ p q : Equiv.Perm (Fin e),
        walkSkelNode e he2 skelCode d 1 p = walkSkelNode e he2 skelCode d 1 q →
        let σ : Fin e ≃ Fin (maskEdgePairs env.r0 mask).length := (Fin.castOrderIso he_eq).toEquiv
        Cslib.Multigraph.msf (endsOfMask env.r0 mask) (σ.symm.trans (p.trans σ)) Finset.univ =
          Cslib.Multigraph.msf (endsOfMask env.r0 mask) (σ.symm.trans (q.trans σ)) Finset.univ) →
        res = 1) := by
  have hr2 := hlay.r0_ge
  have hmaxE := hlay.2.1
  have hnm := hlay.2.2.1
  have hmaxD := hlay.2.2.2.1
  obtain ⟨hbr0, hbr1, hbe0, hbe1, hbe2, hbe3, hbe4, hbe5, hbe6, hbr2⟩ := hlay.edges_bounds
  obtain ⟨hp2d_lay, hp2e_lay, hbb0, hbb1, hbb2, hbb3, hbb4, hbb5, hbb6, hbb7, hbb8, hbb9,
    hbb10, hbb11, hbb12, hbb13, hbb14⟩ := hlay.buf_bounds
  obtain ⟨hbw0, hbw1, hbw2, hbw3, hbw4, hbw5, hbw6, hbw7, hbw8, hbw9, hbw10⟩ := hlay.work_bounds
  obtain ⟨hpowe, hpairs_e, _, hperm⟩ := hm_in
  have he_le_ee := (dtPow_le_self_bounds he2).1
  have hnp_le : e.choose 2 ≤ env.maxD := by rw [hmaxD]; exact Nat.choose_le_choose 2 he_le
  have h2d_pos : 1 ≤ 2 ^ d := Nat.two_pow_pos d
  have h2d_le : 2 ^ d ≤ 2 ^ env.maxD := Nat.pow_le_pow_right (by decide) hd_le
  have h2d1_fit : Fits w (2 ^ (d + 1)) := by
    rw [Nat.pow_succ']; exact hwf.frontier_fits.of_le (by omega)
  have h2d_fit : Fits w (2 ^ d) := h2d1_fit.of_le (by rw [Nat.pow_succ']; omega)
  let cEnv : DTCheckPermEnv := ⟨env, e, d, 2 ^ d, e.choose 2, permAns, skelCode⟩
  let S := Set.Ico env.bufB.leafSeen (env.bufB.leafSeen + 2 ^ d) ∪
    Set.Ico env.bufB.leafAns (env.bufB.leafAns + 2 ^ d)
  let s1 := (Memory.spec 0).clientState s (fillConstProg env.bufB.leafSeen 0 (2 ^ d))
  have hfc1 := fillConstProg_spec (w := w) (base := env.bufB.leafSeen) (val := 0)
    (count := 2 ^ d) hwf (by fits) h2d_fit (by omega)
  obtain ⟨hfc1_vh, hfc1_cost, hfc1_mod, hfc1_fr, hfc1_wf, hfc1_arr⟩ :=
    framedTriple_iff_realization.mp hfc1
  have hfc2 := fillConstProg_spec (w := w) (base := env.bufB.leafAns) (val := 0)
    (count := 2 ^ d) hfc1_wf (by fits) h2d_fit (by rw [hfc1_fr]; omega)
  let s2 := (Memory.spec 0).clientState s1 (fillConstProg env.bufB.leafAns 0 (2 ^ d))
  obtain ⟨hfc2_vh, hfc2_cost, hfc2_mod, hfc2_fr, hfc2_wf, hfc2_arr⟩ :=
    framedTriple_iff_realization.mp hfc2
  have hs2_fr : s2.frontier = s.frontier := hfc2_fr.trans hfc1_fr
  have hs2_seen0 : ∀ l < 2 ^ d, s2.mem (env.bufB.leafSeen + l) = 0 := fun l hl => by
    rw [hfc2_mod.mem_eq_of_not_mem (by rw [hfc1_fr]; omega) (by simp only [Set.mem_Ico]; omega)]
    exact hfc1_arr l hl
  have hleaf_of_lt : ∀ c (hc : CodeIsPerm e c),
      walkSkelNode e he2 skelCode d 1 (permOfCode (by omega : 1 ≤ e) c hc) - 2 ^ d < 2 ^ d :=
    fun c hc => by
      have hb := walkSkelNode_bounds e he2 skelCode (permOfCode (by omega : 1 ≤ e) c hc) d 1 le_rfl
      rw [Nat.one_mul, show 2 * 2 ^ d = 2 ^ (d + 1) by rw [Nat.pow_succ']] at hb; omega
  let leafOf (c : ℕ) (hc : CodeIsPerm e c) : ℕ :=
    walkSkelNode e he2 skelCode d 1 (permOfCode (by omega : 1 ≤ e) c hc) - 2 ^ d
  let inv (k : ℕ) (st : ℕ × ℕ) (t : Memory.State) : Prop :=
    st.1 = k ∧ (st.2 = 0 ∨ st.2 = 1) ∧ t.frontier = s.frontier ∧ Memory.WellFormed w t ∧
    Memory.Modifies S s2 t ∧
    (∀ l < 2 ^ d, t.mem (env.bufB.leafSeen + l) = 0 ∨ t.mem (env.bufB.leafSeen + l) = 1) ∧
    (∀ l < 2 ^ d, t.mem (env.bufB.leafAns + l) < 2 ^ e) ∧
    (∀ l < 2 ^ d, t.mem (env.bufB.leafSeen + l) = 1 → ∃ c < k, ∃ hc : CodeIsPerm e c,
      leafOf c hc = l ∧ t.mem (env.bufB.leafAns + l) = s.mem (permAns + c) - 1) ∧
    (st.2 = 1 → ∀ c < k, ∀ hc : CodeIsPerm e c,
      t.mem (env.bufB.leafSeen + leafOf c hc) = 1 ∧
      t.mem (env.bufB.leafAns + leafOf c hc) = s.mem (permAns + c) - 1) ∧
    (st.2 = 0 → ∃ c₁ < k, ∃ c₂ < k, ∃ h₁ : CodeIsPerm e c₁, ∃ h₂ : CodeIsPerm e c₂,
      leafOf c₁ h₁ = leafOf c₂ h₂ ∧ s.mem (permAns + c₁) ≠ s.mem (permAns + c₂))
  have hs2_mod_s : Memory.Modifies S s s2 :=
    (hfc1_mod.mono Set.subset_union_left).trans (hfc2_mod.mono Set.subset_union_right)
  have hstep : ∀ k < e ^ e, ∀ st t, inv k st t → dtCheckOnePermStepSafe w (cEnv, st) t ∧
      Memory.FramedTriple w t (dtCheckOnePermStep (cEnv, st)) (4 + 5 * d) S (inv (k + 1)) := by
    intro k hk ⟨sidx, sacc⟩ t ⟨hidx, hacc01, htfr, hwt, htmod, hs01, hla_lt, hls1, hacc1, hacc0⟩
    dsimp only at hidx hacc01 hacc1 hacc0; subst sidx
    have ht_s : ∀ a < s.frontier, a ∉ S → t.mem a = s.mem a := fun a ha haS =>
      (htmod.mem_eq_of_not_mem (by omega) haS).trans (hs2_mod_s.mem_eq_of_not_mem ha haS)
    have hpa_eq : t.mem (permAns + k) = s.mem (permAns + k) :=
      ht_s _ (by omega) (by simp only [S, Set.mem_union, Set.mem_Ico]; omega)
    have hstutter : ∀ sacc' : ℕ, (sacc' = 0 ∨ sacc' = 1) → (sacc' = 1 → sacc = 1) →
        (sacc' = 1 → ∀ hc : CodeIsPerm e k,
          t.mem (env.bufB.leafSeen + leafOf k hc) = 1 ∧
          t.mem (env.bufB.leafAns + leafOf k hc) = s.mem (permAns + k) - 1) →
        (sacc' = 0 → ∃ c₁ < k + 1, ∃ c₂ < k + 1, ∃ h₁ : CodeIsPerm e c₁,
          ∃ h₂ : CodeIsPerm e c₂, leafOf c₁ h₁ = leafOf c₂ h₂ ∧
            s.mem (permAns + c₁) ≠ s.mem (permAns + c₂)) →
        inv (k + 1) (k + 1, sacc') t := fun sacc' hs01' hs_imp hk1 hk0 =>
      ⟨rfl, hs01', htfr, hwt, htmod, hs01, hla_lt,
        fun l hl h1 => let ⟨c, hck, hcp, hlc, hac⟩ := hls1 l hl h1; ⟨c, by omega, hcp, hlc, hac⟩,
        fun h1 c hc hcp => if hck : c < k then hacc1 (hs_imp h1) c hck hcp
          else by
            have hce : c = k := by omega
            subst hce; exact hk1 h1 hcp,
        hk0⟩
    rcases hacc01 with rfl | rfl
    · have htri : Memory.FramedTriple w t (dtCheckOnePermStep (cEnv, (k, 0))) (4 + 5 * d) S
          (inv (k + 1)) := by
        dsimp only [dtCheckOnePermStep, cEnv]
        refine Memory.FramedTriple.mono (Memory.FramedTriple.read_bind (c := 0) (by omega) ?_)
          (by omega) fun _ _ h => h
        simp only [↓reduceIte]
        exact Memory.FramedTriple.pure (hstutter 0 (.inl rfl)
          (fun h => absurd h Nat.zero_ne_one) (fun h => absurd h Nat.zero_ne_one) fun _ =>
            let ⟨c₁, hc₁, c₂, hc₂, h₁, h₂, hleq, hne⟩ := hacc0 rfl
            ⟨c₁, by omega, c₂, by omega, h₁, h₂, hleq, hne⟩)
      exact ⟨⟨h2, hfit_ee.of_le (by dsimp only; omega), by dsimp only [cEnv]; omega,
        fun hnz => absurd rfl hnz⟩, htri⟩
    · by_cases hpa0 : t.mem (permAns + k) = 0
      · have htri : Memory.FramedTriple w t (dtCheckOnePermStep (cEnv, (k, 1))) (4 + 5 * d) S
            (inv (k + 1)) := by
          dsimp only [dtCheckOnePermStep, cEnv]
          refine Memory.FramedTriple.mono (Memory.FramedTriple.read_bind (c := 0) (by omega) ?_)
            (by omega) fun _ _ h => h
          simp only [Nat.one_ne_zero, ↓reduceIte, hpa0]
          exact Memory.FramedTriple.pure (hstutter 1 (.inr rfl) (fun _ => rfl)
            (fun _ hcp => absurd hcp ((hperm k hk).1.mp (hpa_eq ▸ hpa0)))
            fun h => absurd h Nat.one_ne_zero)
        exact ⟨⟨h2, hfit_ee.of_le (by dsimp only; omega), by dsimp only [cEnv]; omega,
          fun _ h0 => absurd hpa0 h0⟩, htri⟩
      · have hcp : CodeIsPerm e k := by
          by_contra hncp; exact hpa0 (hpa_eq ▸ (hperm k hk).1.mpr hncp)
        have hpa_mask := (hperm k hk).2 hcp
        have hpa1 : 1 ≤ s.mem (permAns + k) := by rw [hpa_mask]; omega
        have hpa_lt_2e : s.mem (permAns + k) - 1 < 2 ^ e := by
          rw [hpa_mask]; simp only [Nat.add_sub_cancel]
          exact (maskOfFinset_lt _).trans_le (by rw [← he_eq])
        have hnotS : ∀ a, (env.bufC.powEArr ≤ a ∧ a < env.bufC.powEArr + (e + 1)) ∨
            (env.bufC.powSkelArr ≤ a ∧ a < env.bufC.powSkelArr + 2 ^ d) ∨
            (env.bufB.allPairA ≤ a ∧ a < env.bufB.allPairA + env.maxD) ∨
            (env.bufB.allPairB ≤ a ∧ a < env.bufB.allPairB + env.maxD) → a ∉ S := fun a ha => by
          simp only [S, Set.mem_union, Set.mem_Ico]; omega
        obtain ⟨hwk_safe, hwk_vh, hwk_cost, hwk_res, hwk_st⟩ := dtEvalSkelWalk_loop_spec
          (w := w) (powSkelArr := env.bufC.powSkelArr) (allPairA := env.bufB.allPairA)
          (allPairB := env.bufB.allPairB) (powEArr := env.bufC.powEArr) (e := e) (d := d)
          (skelCode := skelCode) (code := k) h2 hwt he2 h2d1_fit (by omega) (by omega) (by omega)
          (by omega)
          (fun j hj => (ht_s _ (by omega)
            (hnotS _ (Or.inr (Or.inl ⟨by omega, by omega⟩)))).trans (hpows j hj))
          (fun j hj => (ht_s _ (by omega) (hnotS _ (Or.inl ⟨by omega, by omega⟩))).trans
            (hpowe j hj))
          (fun pk hpk => ⟨(ht_s _ (by omega)
              (hnotS _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))).trans
              (hpairs_e pk hpk).1,
            (ht_s _ (by omega)
              (hnotS _ (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))).trans
              (hpairs_e pk hpk).2⟩) hcp
        have hleaf_lt : leafOf k hcp < 2 ^ d := hleaf_of_lt k hcp
        have hwk_bounds := walkSkelNode_bounds e he2 skelCode
          (permOfCode (by omega : 1 ≤ e) k hcp) d 1 le_rfl
        rw [Nat.one_mul] at hwk_bounds
        obtain ⟨hlu_safe, hlu_tri⟩ := dtLeafUpdate_spec (w := w) (cenv := cEnv)
          (idx := k) (l := leafOf k hcp) (pa := t.mem (permAns + k)) h2 hwt (hpa_eq ▸ hpa1)
          (hpa_eq ▸ hwf.mem_fits _) (hfit_ee.of_le (by omega))
          (by dsimp only [cEnv]; omega) (by dsimp only [cEnv]; omega) (by dsimp only [cEnv]; omega)
        have hlu_tri_t : Memory.FramedTriple w t
            (dtLeafUpdate (cEnv, k, leafOf k hcp, t.mem (permAns + k))) 3 S (inv (k + 1)) := by
          refine (hlu_tri.frame_mono fun a ha => by
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha; dsimp only [cEnv] at ha
            rcases ha with rfl | rfl
            · exact Set.mem_union_left _ ⟨by omega, by omega⟩
            · exact Set.mem_union_right _ ⟨by omega, by omega⟩).mono
            le_rfl fun res t' ⟨ht'fr, hwf', ht'mod, hz, hnz⟩ => ?_
          dsimp only [cEnv] at ht'mod hz hnz
          by_cases h0 : t.mem (env.bufB.leafSeen + leafOf k hcp) = 0
          · obtain ⟨rfl, hls1', hla1'⟩ := hz h0
            have hmod_t' : Memory.Modifies S t t' := ⟨by omega, fun a ha haS => ht'mod a ha
              (fun h => haS (h ▸ Set.mem_union_left _ ⟨Nat.le_add_right _ _, by omega⟩))
              (fun h => haS (h ▸ Set.mem_union_right _ ⟨Nat.le_add_right _ _, by omega⟩))⟩
            refine ⟨rfl, .inr rfl, ht'fr.trans htfr, hwf', htmod.trans hmod_t',
              fun l hl => if hll : l = leafOf k hcp then hll ▸ hls1' ▸ .inr rfl
                else by rw [ht'mod _ (by omega) (by omega) (by omega)]; exact hs01 l hl,
              fun l hl => if hll : l = leafOf k hcp then hll ▸ hla1' ▸ hpa_eq ▸ hpa_lt_2e
                else by rw [ht'mod _ (by omega) (by omega) (by omega)]; exact hla_lt l hl,
              fun l hl hl1 => if hll : l = leafOf k hcp then by
                  subst hll; rw [hla1', hpa_eq]; exact ⟨k, by omega, hcp, rfl, rfl⟩
                else by
                  rw [ht'mod _ (by omega) (by omega) (by omega)] at hl1 ⊢
                  obtain ⟨c, hck, hcp', hlc, hac⟩ := hls1 l hl hl1
                  exact ⟨c, by omega, hcp', hlc, hac⟩,
              fun _ c hc hcp' => if hck : c < k then by
                  obtain ⟨hs_c, ha_c⟩ := hacc1 rfl c hck hcp'
                  have hl_c : leafOf c hcp' < 2 ^ d := hleaf_of_lt c hcp'
                  have hne_l : leafOf c hcp' ≠ leafOf k hcp := fun heq => by
                    have : t.mem (env.bufB.leafSeen + leafOf c hcp') = 0 := heq ▸ h0; omega
                  rw [ht'mod _ (by omega) (by omega) (by omega),
                    ht'mod _ (by omega) (by omega) (by omega)]; exact ⟨hs_c, ha_c⟩
                else by
                  have hck_eq : c = k := by omega
                  subst hck_eq
                  rw [show leafOf c hcp' = leafOf c hcp from rfl, hls1', hla1', hpa_eq]
                  exact ⟨rfl, rfl⟩,
              fun hbad => absurd hbad Nat.one_ne_zero⟩
          · obtain ⟨ht'_eq, hres_eq⟩ := hnz h0
            have hs1 : t.mem (env.bufB.leafSeen + leafOf k hcp) = 1 :=
              (hs01 (leafOf k hcp) hleaf_lt).resolve_left h0
            obtain ⟨c₀, hc₀, hcp₀, hl₀, ha₀⟩ := hls1 (leafOf k hcp) hleaf_lt hs1
            by_cases hmatch : t.mem (env.bufB.leafAns + leafOf k hcp) = t.mem (permAns + k) - 1
            · rw [ht'_eq, hres_eq]; simp only [hmatch, ↓reduceIte]
              exact hstutter 1 (.inr rfl) (fun _ => rfl) (fun _ hcp' => by
                rw [show leafOf k hcp' = leafOf k hcp from rfl]
                exact ⟨hs1, by rw [hmatch, hpa_eq]⟩) fun hbad => absurd hbad Nat.one_ne_zero
            · rw [ht'_eq, hres_eq]; simp only [hmatch, ↓reduceIte]
              exact hstutter 0 (.inl rfl) (fun h => absurd h Nat.zero_ne_one)
                (fun hbad => absurd hbad Nat.zero_ne_one) fun _ => ⟨c₀, by omega, k, by omega,
                  hcp₀, hcp, hl₀, fun heq => hmatch (by rw [ha₀, heq, hpa_eq])⟩
        have hbody_tri : Memory.FramedTriple w t (dtCheckOnePermStep (cEnv, (k, 1)))
            (4 + 5 * d) S (inv (k + 1)) := by
          dsimp only [dtCheckOnePermStep, cEnv]
          refine Memory.FramedTriple.mono (Memory.FramedTriple.read_bind (c := 5 * d + 3)
            (by omega) ?_) (by omega) fun _ _ h => h
          simp only [Nat.one_ne_zero, ↓reduceIte, hpa0]
          exact ((framedTriple_iff_realization.mpr
            ⟨hwk_vh, hwk_cost, by simpa [hwk_st] using Memory.Modifies.refl S t,
             by rw [hwk_res, hwk_st]; exact hlu_tri_t⟩).bind_same).mono (by omega) fun _ _ h => h
        exact ⟨⟨h2, hfit_ee.of_le (by dsimp only; omega), by dsimp only [cEnv]; omega, fun _ _ =>
          ⟨by rw [hwk_res]; exact hwk_bounds.1, hwk_safe,
            by dsimp only; rw [hwk_res, hwk_st]; exact hlu_safe⟩⟩, hbody_tri⟩
  have hinit : inv 0 (0, 1) s2 :=
    ⟨rfl, .inr rfl, hs2_fr, hfc2_wf, Memory.Modifies.refl S s2,
      fun l hl => .inl (hs2_seen0 l hl),
      fun l hl => by rw [hfc2_arr l hl]; exact Nat.two_pow_pos _,
      fun l hl h1 => by rw [hs2_seen0 l hl] at h1; omega,
      fun _ c hc => absurd hc (Nat.not_lt_zero _), fun h0 => absurd h0 Nat.one_ne_zero⟩
  obtain ⟨hchk_safe, hchk_vh, hchk_cost, hchk_mod, hchk_post⟩ :=
    iterate_potential_spec dtCheckOnePermStep dtCheckOnePermStepSafe w cEnv (4 + 5 * d) (e ^ e)
      inv (fun _ _ _ => 0) S (fun k hk a s ha => let ⟨hs', ht'⟩ := hstep k hk a s ha
        let ⟨hv', hc', hm', hi'⟩ := framedTriple_iff_realization.mp ht'
        ⟨hs', hv', by omega, hm', hi'⟩) (0, 1) s2 hinit
  have hchk_tri : Memory.FramedTriple w s2 (iterate dtCheckOnePermStep cEnv (e ^ e) (0, 1) >>=
      fun res => pure res.2) (e ^ e * (4 + 5 * d)) S fun res s' => (res = 0 ∨ res = 1) ∧
      s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
      (∀ l < 2 ^ d, s'.mem (env.bufB.leafAns + l) < 2 ^ e) ∧
      (res = 1 → ∀ p : Equiv.Perm (Fin e),
        let σ : Fin e ≃ Fin (maskEdgePairs env.r0 mask).length := (Fin.castOrderIso he_eq).toEquiv
        let p' : Equiv.Perm (Fin (maskEdgePairs env.r0 mask).length) := σ.symm.trans (p.trans σ)
        s'.mem (env.bufB.leafAns + (walkSkelNode e he2 skelCode d 1 p - 2 ^ d)) =
          maskOfFinset (Cslib.Multigraph.msf (endsOfMask env.r0 mask) p' Finset.univ)) ∧
      ((∀ p q : Equiv.Perm (Fin e),
        walkSkelNode e he2 skelCode d 1 p = walkSkelNode e he2 skelCode d 1 q →
        let σ : Fin e ≃ Fin (maskEdgePairs env.r0 mask).length := (Fin.castOrderIso he_eq).toEquiv
        Cslib.Multigraph.msf (endsOfMask env.r0 mask) (σ.symm.trans (p.trans σ)) Finset.univ =
          Cslib.Multigraph.msf (endsOfMask env.r0 mask) (σ.symm.trans (q.trans σ)) Finset.univ) →
        res = 1) := by
    refine Memory.FramedTriple.mono (Memory.FramedTriple.bind_same (c₁ := e ^ e * (4 + 5 * d))
      (c₂ := 0) ?_) (by omega) fun _ _ h => h
    exact (framedTriple_iff_realization.mpr ⟨hchk_vh,
      by simpa only [Nat.add_zero, Nat.zero_add, Nat.mul_comm] using hchk_cost,
      hchk_mod, hchk_post⟩).mono le_rfl fun _ _ ⟨_, h01, hfr, hwf', _, _, hlt, _, h1m, h0m⟩ =>
      Memory.FramedTriple.pure ⟨h01, hfr, hwf', hlt, fun hres1 p => by
          have hmem := h1m hres1 (permCode p) (permCode_lt p) (codeIsPerm_permCode p)
          have hpa := (hperm (permCode p) (permCode_lt p)).2 (codeIsPerm_permCode p)
          dsimp only [leafOf] at hmem; dsimp only at hpa
          rw [permOfCode_permCode _ p] at hmem; rw [hmem.2, hpa, permOfCode_permCode _ p]; simp,
        fun hgood => by
          rcases h01 with h0 | h1
          · obtain ⟨c₁, hc₁, c₂, hc₂, h₁, h₂, hl_eq, hne⟩ := h0m h0
            let p₁ := permOfCode (by omega : 1 ≤ e) c₁ h₁
            let p₂ := permOfCode (by omega : 1 ≤ e) c₂ h₂
            have hb₁ := walkSkelNode_bounds e he2 skelCode p₁ d 1 le_rfl
            have hb₂ := walkSkelNode_bounds e he2 skelCode p₂ d 1 le_rfl
            rw [Nat.one_mul] at hb₁ hb₂
            change walkSkelNode e he2 skelCode d 1 p₁ - 2 ^ d =
              walkSkelNode e he2 skelCode d 1 p₂ - 2 ^ d at hl_eq
            have hmsf := hgood p₁ p₂ (by omega)
            have hp1 := (hperm c₁ hc₁).2 h₁; have hp2 := (hperm c₂ hc₂).2 h₂
            dsimp only [p₁] at hmsf; dsimp only [p₂] at hmsf
            exfalso; exact hne (by dsimp only at hp1 hp2; rw [hp1, hp2, hmsf])
          · exact h1⟩
  obtain ⟨hchk_vh', hchk_cost', hchk_mod', hchk_q'⟩ := framedTriple_iff_realization.mp hchk_tri
  refine ⟨⟨h2, h2d_fit, by dsimp only [cEnv]; omega, by dsimp only [cEnv]; rw [hfc1_fr]; omega,
      hchk_safe⟩, framedTriple_iff_realization.mpr ?_⟩
  dsimp only [dtTestSkelProg]
  refine ⟨(validHistory_bind' w _ _ _).mpr ⟨hfc1_vh, (validHistory_bind' w _ _ _).mpr
      ⟨hfc2_vh, hchk_vh'⟩⟩,
    by rw [memoryCost_bind', memoryCost_bind']
       exact (Nat.add_le_add hfc1_cost (Nat.add_le_add hfc2_cost hchk_cost')).trans_eq (by ring),
    ?_, ?_⟩
  · rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
    exact (hfc1_mod.mono Set.subset_union_left).trans
      ((hfc2_mod.mono Set.subset_union_right).trans hchk_mod')
  · rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
    exact hchk_q'

private def dtWriteIntNodesStep (x : DTWriteIntEnv × ℕ) : Memory.Prog ℕ := do
  let pw ← Memory.read (x.1.powSkelArr + x.2)
  let pk := (x.1.skelCode / pw) % x.1.numPairs
  let a ← Memory.read (x.1.allPairA + pk)
  let b ← Memory.read (x.1.allPairB + pk)
  Memory.write (x.1.intBase + 2 * x.2) a
  Memory.write (x.1.intBase + 2 * x.2 + 1) b
  pure (x.2 + 1)

private def dtWriteIntNodesStepSafe (w : ℕ) (x : DTWriteIntEnv × ℕ) (s : Memory.State) : Prop :=
  Fits w 2 ∧ 1 ≤ x.1.numPairs ∧ Fits w (x.2 + 1) ∧ s.mem (x.1.powSkelArr + x.2) ≠ 0 ∧
  (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (dtWriteIntNodesStep x))

private theorem realizes_dtWriteIntNodesStep : Realizes .exact
    dtWriteIntNodesStep (appendWords dtWriteIntEnvWords WordEncoding.encode)
    WordEncoding.encode dtWriteIntNodesStepSafe (fun _ _ => 0) := by
  unfold dtWriteIntNodesStep
  realize
  all_goals
    obtain ⟨h2, hnp, hidx, hnz, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [dtWriteIntNodesStep, StateTransitionSpec.clientHistory] at hv
    simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.read, Memory.write, Memory.step_read, Memory.step_write,
      Memory.valid] at hv
    first | exact hnz | omega | fits

private theorem dtWriteIntNodes_loop_spec {w intBase allPairA allPairB powSkelArr e skelCode
    len : ℕ} {s : Memory.State} (h2 : Fits w 2) (hwf : Memory.WellFormed w s)
    (he2 : 2 ≤ e) (hlen : Fits w len)
    (hib : intBase + 2 * len ≤ s.frontier) (haa : allPairA + e.choose 2 ≤ s.frontier)
    (hab : allPairB + e.choose 2 ≤ s.frontier) (hpows_lt : powSkelArr + len ≤ s.frontier)
    (hdisjA : allPairA + e.choose 2 ≤ intBase ∨ intBase + 2 * len ≤ allPairA)
    (hdisjB : allPairB + e.choose 2 ≤ intBase ∨ intBase + 2 * len ≤ allPairB)
    (hdisjP : powSkelArr + len ≤ intBase ∨ intBase + 2 * len ≤ powSkelArr)
    (hpows : ∀ k < len, s.mem (powSkelArr + k) = (e.choose 2) ^ k) :
    let env : DTWriteIntEnv := ⟨intBase, allPairA, allPairB, powSkelArr, e.choose 2, skelCode⟩
    let prog := iterate dtWriteIntNodesStep env len 0
    let S := Set.Ico intBase (intBase + 2 * len)
    iterationSafe dtWriteIntNodesStep dtWriteIntNodesStepSafe w env len 0 s ∧
    Memory.FramedTriple w s prog (5 * len) S fun _ s' =>
      s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
      ∀ k < len,
        s'.mem (intBase + 2 * k) =
          s.mem (allPairA + (skelCode / (e.choose 2) ^ k) % e.choose 2) ∧
        s'.mem (intBase + 2 * k + 1) =
          s.mem (allPairB + (skelCode / (e.choose 2) ^ k) % e.choose 2) := by
  let env : DTWriteIntEnv := ⟨intBase, allPairA, allPairB, powSkelArr, e.choose 2, skelCode⟩
  let S : Set ℕ := Set.Ico intBase (intBase + 2 * len)
  have hnp_pos : 1 ≤ e.choose 2 := Nat.choose_pos he2
  let inv (k st : ℕ) (t : Memory.State) : Prop :=
    st = k ∧ t.frontier = s.frontier ∧ Memory.WellFormed w t ∧ Memory.Modifies S s t ∧
    ∀ j < k, ∀ (_ : j < len),
      t.mem (intBase + 2 * j) = s.mem (allPairA + (skelCode / (e.choose 2) ^ j) % e.choose 2) ∧
      t.mem (intBase + 2 * j + 1) = s.mem (allPairB + (skelCode / (e.choose 2) ^ j) % e.choose 2)
  have hstep : ∀ k < len, ∀ st t, inv k st t →
      dtWriteIntNodesStepSafe w (env, st) t ∧
      Memory.FramedTriple w t (dtWriteIntNodesStep (env, st)) 5 S (inv (k + 1)) := by
    intro k hk st t ⟨hidx, htfr, hwt, htmod, hprev⟩; subst st
    have hpw : t.mem (powSkelArr + k) = (e.choose 2) ^ k :=
      (htmod.mem_eq_of_not_mem (by omega)
        (by simp only [S, Set.mem_Ico]; rcases hdisjP with h | h <;> omega)).trans (hpows k hk)
    have hpw_nz : t.mem (powSkelArr + k) ≠ 0 := by
      rw [hpw]; exact Nat.ne_of_gt (Nat.pow_pos hnp_pos)
    let pk := (skelCode / (e.choose 2) ^ k) % e.choose 2
    have hpk_lt : pk < e.choose 2 := Nat.mod_lt _ hnp_pos
    have hpa_eq : t.mem (allPairA + pk) = s.mem (allPairA + pk) := htmod.mem_eq_of_not_mem
      (by omega) (by simp only [S, Set.mem_Ico]; rcases hdisjA with h | h <;> omega)
    have hpb_eq : t.mem (allPairB + pk) = s.mem (allPairB + pk) := htmod.mem_eq_of_not_mem
      (by omega) (by simp only [S, Set.mem_Ico]; rcases hdisjB with h | h <;> omega)
    have htri_raw : Memory.FramedTriple w t (dtWriteIntNodesStep (env, k)) 5 S fun a' t' =>
        a' = k + 1 ∧ t'.frontier = s.frontier ∧ (∀ a < t.frontier, a ∉ S → t'.mem a = t.mem a) ∧
        ∀ j < k + 1, ∀ (_ : j < len),
          t'.mem (intBase + 2 * j) =
            s.mem (allPairA + (skelCode / (e.choose 2) ^ j) % e.choose 2) ∧
          t'.mem (intBase + 2 * j + 1) =
            s.mem (allPairB + (skelCode / (e.choose 2) ^ j) % e.choose 2) := by
      dsimp only [dtWriteIntNodesStep, env]
      refine Memory.FramedTriple.read_bind (by omega) ?_; rw [hpw]
      change Memory.FramedTriple w t (Memory.read (allPairA + pk) >>= fun a =>
        Memory.read (allPairB + pk) >>= fun b =>
          Memory.write (intBase + 2 * k) a >>= fun _ =>
            Memory.write (intBase + 2 * k + 1) b >>= fun _ => pure (k + 1)) 4 S _
      refine Memory.FramedTriple.read_bind (by omega) ?_
      refine Memory.FramedTriple.read_bind (by omega) ?_
      refine Memory.FramedTriple.write_bind_of_mem (by omega) (hwt.mem_fits _)
        ⟨by omega, by omega⟩ ?_
      refine Memory.FramedTriple.write_bind_of_mem (by dsimp only; omega) (hwt.mem_fits _)
        ⟨by omega, by omega⟩ ?_
      refine Memory.FramedTriple.pure ⟨rfl, htfr, fun a _ haS => ?_, fun j hj hjl => ?_⟩
      · simp only [S, Set.mem_Ico] at haS; update_simp
      · by_cases hjk : j < k
        · update_simp; exact hprev j hjk hjl
        · have hjeq : j = k := by omega
          subst hjeq; update_simp; exact ⟨hpa_eq, hpb_eq⟩
    have htri : Memory.FramedTriple w t (dtWriteIntNodesStep (env, k)) 5 S (inv (k + 1)) :=
      (htri_raw.wellFormed hwt).mono le_rfl fun _ _ ⟨⟨rfl, ht'fr, ht'mod, hvals⟩, hwf'⟩ =>
        ⟨rfl, ht'fr, hwf', htmod.trans ⟨by omega, ht'mod⟩, hvals⟩
    exact ⟨⟨h2, hnp_pos, hlen.of_le (by omega), hpw_nz,
      (framedTriple_iff_realization.mp htri).1⟩, htri⟩
  obtain ⟨hsafe, hv, hc, hmod, hpost⟩ := iterate_potential_spec dtWriteIntNodesStep
    dtWriteIntNodesStepSafe w env 5 len inv (fun _ _ _ => 0) S
    (fun k hk a s ha => let ⟨hs', ht'⟩ := hstep k hk a s ha
      let ⟨hv', hc', hm', hi'⟩ := framedTriple_iff_realization.mp ht'
      ⟨hs', hv', by omega, hm', hi'⟩)
    0 s ⟨rfl, rfl, hwf, Memory.Modifies.refl S s, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  exact ⟨hsafe, framedTriple_iff_realization.mpr
    ⟨hv, by simpa only [Nat.add_zero, Nat.zero_add, Nat.mul_comm] using hc, hmod,
      hpost.2.1, hpost.2.2.1, fun k hk => hpost.2.2.2.2 k hk hk⟩⟩

private theorem dtHoldsCompleteTreeCast {e₁ e₂ : ℕ} (he : e₁ = e₂)
    {dInit intBase leafBase d node : ℕ} {mem : ℕ → ℕ} (T : MSFDT e₁)
    (hcomp : T.IsComplete d) (hhold : HoldsCompleteTree dInit intBase leafBase d node mem T) :
    let σ := (Fin.castOrderIso he).toEquiv
    ((T.mapLeaves (Finset.map σ.toEmbedding)).liftEmb σ).IsComplete d ∧
    HoldsCompleteTree dInit intBase leafBase d node mem
      ((T.mapLeaves (Finset.map σ.toEmbedding)).liftEmb σ) := by
  subst he
  have hσ : (Fin.castOrderIso rfl).toEquiv = Equiv.refl (Fin e₁) := by ext x; rfl
  have hid : (T.mapLeaves (Finset.map (Fin.castOrderIso rfl).toEquiv.toEmbedding)).liftEmb
      (Fin.castOrderIso rfl).toEquiv = T := by
    rw [hσ]
    have hm : Finset.map (Equiv.refl (Fin e₁)).toEmbedding = id := by ext s x; simp
    rw [hm, MSFTree.mapLeaves_id]
    exact MSFTree.liftEmb_id T
  dsimp only
  rw [hid]
  exact ⟨hcomp, hhold⟩

/-- Allocates and writes a depth-`d` decision-tree table entry for skeleton `d.2`. -/
def dtWriteFoundEntry (d : DTSkelEnv × ℕ) : Memory.Prog Unit := do
  let epBlk ← Memory.allocBlockDirty (2 + d.1.e + 2 * (d.1.pow2d - 1) + d.1.pow2d)
  Memory.write (d.1.env.bufA.tableBase + d.1.mask) epBlk.base
  Memory.write epBlk.base d.1.e
  Memory.write (epBlk.base + 1) d.1.d
  Memory.copy d.1.env.bufA.edgePair (epBlk.base + 2) d.1.e
  let _ ← iterate dtWriteIntNodesStep
    ⟨epBlk.base + 2 + d.1.e, d.1.env.bufB.allPairA, d.1.env.bufB.allPairB,
      d.1.env.bufC.powSkelArr, d.1.numPairs, d.2⟩ (d.1.pow2d - 1) 0
  Memory.copy d.1.env.bufB.leafAns (epBlk.base + 2 + d.1.e + 2 * (d.1.pow2d - 1)) d.1.pow2d

/-- Word-RAM safety precondition for `dtWriteFoundEntry`. -/
def dtWriteFoundEntrySafe (w : ℕ) (d : DTSkelEnv × ℕ) (s : Memory.State) : Prop :=
  let sz := 2 + d.1.e + 2 * (d.1.pow2d - 1) + d.1.pow2d
  let ep := s.frontier
  let s0 : Memory.State := ⟨Function.update (Function.update (Function.update s.mem
    (d.1.env.bufA.tableBase + d.1.mask) ep) ep d.1.e) (ep + 1) d.1.d, s.frontier + sz⟩
  let s1 := (Memory.spec 0).clientState s0 (Memory.copy d.1.env.bufA.edgePair (ep + 2) d.1.e)
  let intEnv : DTWriteIntEnv := ⟨ep + 2 + d.1.e, d.1.env.bufB.allPairA, d.1.env.bufB.allPairB,
    d.1.env.bufC.powSkelArr, d.1.numPairs, d.2⟩
  let s2 := (Memory.spec 0).clientState s1
    (iterate dtWriteIntNodesStep intEnv (d.1.pow2d - 1) 0)
  Fits w 2 ∧ 1 ≤ d.1.pow2d ∧ Fits w (s.frontier + sz) ∧
  d.1.env.bufA.tableBase + d.1.mask < s.frontier + sz ∧ ep + 1 < s.frontier + sz ∧
  d.1.env.bufA.edgePair + d.1.e ≤ s.frontier + sz ∧ ep + 2 + d.1.e ≤ s.frontier + sz ∧
  iterationSafe dtWriteIntNodesStep dtWriteIntNodesStepSafe w intEnv (d.1.pow2d - 1) 0 s1 ∧
  d.1.env.bufB.leafAns + d.1.pow2d ≤ s2.frontier ∧
  ep + 2 + d.1.e + 2 * (d.1.pow2d - 1) + d.1.pow2d ≤ s2.frontier

/-- Uniform `Realizes .exact` certificate for `dtWriteFoundEntry` with `work = 0`. -/
theorem realizes_dtWriteFoundEntry : Realizes .exact
    dtWriteFoundEntry (appendWords dtSkelEnvWords WordEncoding.encode)
    WordEncoding.encode dtWriteFoundEntrySafe (fun _ _ => 0) := by
  unfold dtWriteFoundEntry
  realize [realizes_allocBlockDirty, realizes_copy, realizes_dtWriteIntNodesStep]
  all_goals
    repeat rw [Memory.clientState_allocBlockDirty] at *
    simp only [Memory.clientResult_allocBlockDirty] at *
    obtain ⟨h2, hp2d, hfr, htb, hep1, heps, hepd, hint, hls, hld⟩ := h
    have hfront := hmem.frontier_fits
    first
    | exact hp2d
    | exact heps
    | exact hepd
    | exact iterationSafe_imp hint (fun _ => rfl) (fun _ _ hs => ⟨by dsimp only; fits, hs⟩)
    | exact hls
    | exact hld
    | fits [hp2d, hfr]

/-- Framed specification of `dtWriteFoundEntry` establishing `DTMaskEntryValid`. -/
theorem dtWriteFoundEntry_spec {w baseFront mask e d permAns powE numSkels skelCode : ℕ}
    {env : DTPrecompEnv} {s : Memory.State}
    (h2 : Fits w 2) (hwf : Memory.WellFormed w s)
    (hlay : DTEnvLayout env baseFront) (hbf : baseFront ≤ s.frontier)
    (he2 : 2 ≤ e) (he_le : e ≤ env.maxE) (he_eq : e = (maskEdgePairs env.r0 mask).length)
    (hd_le : d ≤ env.maxD) (hmask : mask < env.numMasks)
    (hfit_fr : Fits w (s.frontier + (2 + e + 2 * (2 ^ d - 1) + 2 ^ d)))
    (hpows : ∀ k < 2 ^ d - 1, s.mem (env.bufC.powSkelArr + k) = (e.choose 2) ^ k)
    (hpairs_e : ∀ pk (hpk : pk < e.choose 2),
      s.mem (env.bufB.allPairA + pk) =
        ((allPairs e)[pk]'(by rw [length_allPairs]; exact hpk)).1.val ∧
      s.mem (env.bufB.allPairB + pk) =
        ((allPairs e)[pk]'(by rw [length_allPairs]; exact hpk)).2.val)
    (hmask_ep : ∀ j (hj : j < (maskEdgePairs env.r0 mask).length),
      s.mem (env.bufA.edgePair + j) =
        pairIdx (maskEdgePairs env.r0 mask)[j].1.val (maskEdgePairs env.r0 mask)[j].2.val)
    (hleaf_lt : ∀ l < 2 ^ d, s.mem (env.bufB.leafAns + l) < 2 ^ e)
    (hleaf_good : ∀ p : Equiv.Perm (Fin e),
      let σ : Fin e ≃ Fin (maskEdgePairs env.r0 mask).length := (Fin.castOrderIso he_eq).toEquiv
      let p' : Equiv.Perm (Fin (maskEdgePairs env.r0 mask).length) := σ.symm.trans (p.trans σ)
      s.mem (env.bufB.leafAns + (walkSkelNode e he2 skelCode d 1 p - 2 ^ d)) =
        maskOfFinset (Cslib.Multigraph.msf (endsOfMask env.r0 mask) p' Finset.univ)) :
    let sEnv : DTSkelEnv := ⟨env, mask, e, d, 2 ^ d, e.choose 2, permAns, powE, numSkels⟩
    let prog := dtWriteFoundEntry (sEnv, skelCode)
    let sz := 2 + e + 2 * (2 ^ d - 1) + 2 ^ d
    let S : Set ℕ := {env.bufA.tableBase + mask} ∪ Set.Ico s.frontier (s.frontier + sz)
    dtWriteFoundEntrySafe w (sEnv, skelCode) s ∧
    Memory.FramedTriple w s prog (4 + 2 * e + 7 * 2 ^ d) S fun _ s' =>
      s'.frontier = s.frontier + sz ∧ Memory.WellFormed w s' ∧
      DTMaskEntryValid env.r0 env.bufA.tableBase mask d s' ∧
      s'.mem (env.bufA.tableBase + mask) = s.frontier := by
  have hr2 := hlay.r0_ge
  have hmaxE := hlay.2.1
  have hnm := hlay.2.2.1
  have hmaxD := hlay.2.2.2.1
  obtain ⟨hbr0, hbr1, hbe0, hbe1, hbe2, hbe3, hbe4, hbe5, hbe6, hbr2⟩ := hlay.edges_bounds
  obtain ⟨hp2d_lay, hp2e_lay, hbb0, hbb1, hbb2, hbb3, hbb4, hbb5, hbb6, hbb7, hbb8, hbb9,
    hbb10, hbb11, hbb12, hbb13, hbb14⟩ := hlay.buf_bounds
  obtain ⟨hbw0, hbw1, hbw2, hbw3, hbw4, hbw5, hbw6, hbw7, hbw8, hbw9, hbw10⟩ := hlay.work_bounds
  have h2d_le : 2 ^ d ≤ 2 ^ env.maxD := Nat.pow_le_pow_right (by decide) hd_le
  have h2d_pos : 1 ≤ 2 ^ d := Nat.two_pow_pos d
  have hnp_pos : 1 ≤ e.choose 2 := Nat.choose_pos he2
  have hnp_le : e.choose 2 ≤ env.maxD := by rw [hmaxD]; exact Nat.choose_le_choose 2 he_le
  let ep := s.frontier; let sz := 2 + e + 2 * (2 ^ d - 1) + 2 ^ d
  let S : Set ℕ := {env.bufA.tableBase + mask} ∪ Set.Ico ep (ep + sz)
  let sEnv : DTSkelEnv := ⟨env, mask, e, d, 2 ^ d, e.choose 2, permAns, powE, numSkels⟩
  let s0 : Memory.State := ⟨Function.update (Function.update (Function.update s.mem
    (env.bufA.tableBase + mask) ep) ep e) (ep + 1) d, s.frontier + sz⟩
  have hwf_s : Memory.WellFormed w ⟨s.mem, s.frontier + sz⟩ := ⟨hfit_fr, hwf.mem_fits⟩
  have hhdr_wf : Memory.FramedTriple w ⟨s.mem, s.frontier + sz⟩
      (Memory.write (env.bufA.tableBase + mask) ep >>= fun _ =>
        Memory.write ep e >>= fun _ => Memory.write (ep + 1) d)
      3 S (fun _ t => t = s0 ∧ Memory.WellFormed w t) :=
    (Memory.FramedTriple.write_bind_of_mem (by dsimp only [ep, sz]; omega)
      hwf.frontier_fits (Set.mem_union_left _ rfl)
      (Memory.FramedTriple.write_bind_of_mem (by dsimp only [ep, sz]; omega)
        (hfit_fr.of_le (by omega))
        (by dsimp only [S, sz]; right; exact ⟨le_rfl, by omega⟩)
        (Memory.FramedTriple.write (by dsimp only [ep, sz]; omega)
          (hfit_fr.of_le (by have := Nat.lt_two_pow_self (n := d); omega))
          (by dsimp only [S, sz]; right; exact ⟨by omega, by omega⟩) rfl))).wellFormed hwf_s
  have hwf0 : Memory.WellFormed w s0 := by
    obtain ⟨_, _, _, hs0_eq, hwf'⟩ := framedTriple_iff_realization.mp hhdr_wf
    exact hs0_eq ▸ hwf'
  have hc1 := (Memory.FramedTriple.copy (w := w) (s := s0) (src := env.bufA.edgePair)
    (dst := ep + 2) (n := e) (by left; omega) (by dsimp only [s0]; omega)
    (by dsimp only [s0, sz]; omega) (fun _ _ => hwf0.mem_fits _)
    (Q := fun _ t => t = ⟨ArrayCopy.copyPrefix s0.mem env.bufA.edgePair (ep + 2) e,
      s.frontier + sz⟩) rfl).wellFormed hwf0
  let s1 := (Memory.spec 0).clientState s0 (Memory.copy env.bufA.edgePair (ep + 2) e)
  obtain ⟨_, _, _, hs1_eq, hs1_wf⟩ := framedTriple_iff_realization.mp hc1
  have hs1_mem : s1.mem = ArrayCopy.copyPrefix s0.mem env.bufA.edgePair (ep + 2) e :=
    congrArg Memory.State.mem hs1_eq
  have hs1_fr : s1.frontier = s.frontier + sz := congrArg Memory.State.frontier hs1_eq
  have hs1_below : ∀ a < ep, a ≠ env.bufA.tableBase + mask → s1.mem a = s.mem a :=
    fun a ha hne => by
      rw [hs1_mem, ArrayCopy.copyPrefix_outside (by omega)]; dsimp only [s0]; update_simp
  have hs1_ptr : s1.mem (env.bufA.tableBase + mask) = ep := by
    rw [hs1_mem, ArrayCopy.copyPrefix_outside (by omega)]; dsimp only [s0]; update_simp
  have hs1_e : s1.mem ep = e := by
    rw [hs1_mem, ArrayCopy.copyPrefix_outside (by omega)]; dsimp only [s0]; update_simp
  have hs1_d : s1.mem (ep + 1) = d := by
    rw [hs1_mem, ArrayCopy.copyPrefix_outside (by omega)]; dsimp only [s0]; update_simp
  have hs1_ep : ∀ j (hj : j < (maskEdgePairs env.r0 mask).length), s1.mem (ep + 2 + j) =
      pairIdx (maskEdgePairs env.r0 mask)[j].1.val (maskEdgePairs env.r0 mask)[j].2.val :=
    fun j hj => by
      rw [hs1_mem, ArrayCopy.copyPrefix_read (he_eq ▸ hj)]; dsimp only [s0]
      update_simp; exact hmask_ep j hj
  obtain ⟨hint_safe, hint_tri⟩ := dtWriteIntNodes_loop_spec (w := w) (intBase := ep + 2 + e)
    (allPairA := env.bufB.allPairA) (allPairB := env.bufB.allPairB)
    (powSkelArr := env.bufC.powSkelArr) (e := e) (skelCode := skelCode) (len := 2 ^ d - 1)
    h2 hs1_wf he2 (hfit_fr.of_le (by omega)) (by rw [hs1_fr]; dsimp only [sz]; omega)
    (by rw [hs1_fr]; dsimp only [sz]; omega) (by rw [hs1_fr]; dsimp only [sz]; omega)
    (by rw [hs1_fr]; dsimp only [sz]; omega) (by left; omega) (by left; omega) (by left; omega)
    (fun k hk => by rw [hs1_below _ (by omega) (by omega)]; exact hpows k hk)
  let s2 := (Memory.spec 0).clientState s1 (iterate dtWriteIntNodesStep
    ⟨ep + 2 + e, env.bufB.allPairA, env.bufB.allPairB, env.bufC.powSkelArr, e.choose 2,
      skelCode⟩ (2 ^ d - 1) 0)
  obtain ⟨hint_vh, hint_cost, hs2_mod, hs2_fr, hs2_wf, hint_arr⟩ :=
    framedTriple_iff_realization.mp hint_tri
  have hs2_fr' : s2.frontier = s.frontier + sz := hs2_fr.trans hs1_fr
  have hs2_below : ∀ a < ep + 2 + e, s2.mem a = s1.mem a := fun a ha =>
    hs2_mod.mem_eq_of_not_mem (by rw [hs1_fr]; omega) (by simp only [Set.mem_Ico]; omega)
  have hc2 := (Memory.FramedTriple.copy (w := w) (s := s2) (src := env.bufB.leafAns)
    (dst := ep + 2 + e + 2 * (2 ^ d - 1)) (n := 2 ^ d) (by left; omega) (by rw [hs2_fr']; omega)
    (by rw [hs2_fr']; dsimp only [sz]; omega) (fun _ _ => hs2_wf.mem_fits _)
    (Q := fun _ t => t = ⟨ArrayCopy.copyPrefix s2.mem env.bufB.leafAns
      (ep + 2 + e + 2 * (2 ^ d - 1)) (2 ^ d), s2.frontier⟩) rfl).wellFormed hs2_wf
  let s3 := (Memory.spec 0).clientState s2
    (Memory.copy env.bufB.leafAns (ep + 2 + e + 2 * (2 ^ d - 1)) (2 ^ d))
  obtain ⟨hc2_vh, hc2_cost, hc2_mod, hs3_eq, hwf3⟩ := framedTriple_iff_realization.mp hc2
  have htri_pre : Memory.FramedTriple w s0 (Memory.copy env.bufA.edgePair (ep + 2) e >>= fun _ =>
      iterate dtWriteIntNodesStep ⟨ep + 2 + e, env.bufB.allPairA, env.bufB.allPairB,
        env.bufC.powSkelArr, e.choose 2, skelCode⟩ (2 ^ d - 1) 0 >>= fun _ =>
      Memory.copy env.bufB.leafAns (ep + 2 + e + 2 * (2 ^ d - 1)) (2 ^ d))
      (2 * e + 5 * (2 ^ d - 1) + 2 * 2 ^ d) S fun _ s' =>
        s'.frontier = s.frontier + sz ∧ Memory.WellFormed w s' ∧
        DTMaskEntryValid env.r0 env.bufA.tableBase mask d s' ∧
        s'.mem (env.bufA.tableBase + mask) = s.frontier := by
    have ht1 : Memory.FramedTriple w s1 (iterate dtWriteIntNodesStep ⟨ep + 2 + e,
          env.bufB.allPairA, env.bufB.allPairB, env.bufC.powSkelArr, e.choose 2, skelCode⟩
          (2 ^ d - 1) 0 >>= fun _ =>
        Memory.copy env.bufB.leafAns (ep + 2 + e + 2 * (2 ^ d - 1)) (2 ^ d))
        (5 * (2 ^ d - 1) + 2 * 2 ^ d)
        (Set.Ico (ep + 2 + e) (ep + 2 + e + 2 * (2 ^ d - 1)) ∪
          Set.Ico (ep + 2 + e + 2 * (2 ^ d - 1))
            (ep + 2 + e + 2 * (2 ^ d - 1) + 2 ^ d)) fun _ s' =>
          s'.frontier = s.frontier + sz ∧ Memory.WellFormed w s' ∧
          DTMaskEntryValid env.r0 env.bufA.tableBase mask d s' ∧
          s'.mem (env.bufA.tableBase + mask) = s.frontier := by
      refine framedTriple_iff_realization.mpr
        ⟨(validHistory_bind' w _ _ _).mpr ⟨hint_vh, hc2_vh⟩,
          by rw [memoryCost_bind']; exact Nat.add_le_add hint_cost hc2_cost, ?_, ?_⟩
      · rw [StateTransitionSpec.clientState_bind]
        exact (hs2_mod.mono Set.subset_union_left).trans (hc2_mod.mono Set.subset_union_right)
      · rw [StateTransitionSpec.clientState_bind]
        have hs3_mem : s3.mem = ArrayCopy.copyPrefix s2.mem env.bufB.leafAns
            (ep + 2 + e + 2 * (2 ^ d - 1)) (2 ^ d) := congrArg Memory.State.mem hs3_eq
        have hs3_before : ∀ a < ep + 2 + e + 2 * (2 ^ d - 1), s3.mem a = s2.mem a :=
          fun a ha => hs3_mem ▸ ArrayCopy.copyPrefix_outside (by omega)
        have hs3_below : ∀ a < ep + 2 + e, s3.mem a = s1.mem a := fun a ha =>
          (hs3_before a (by omega)).trans (hs2_below a ha)
        have hs3_fr : s3.frontier = s.frontier + sz :=
          (congrArg Memory.State.frontier hs3_eq).trans hs2_fr'
        have hptr : s3.mem (env.bufA.tableBase + mask) = ep := by
          rw [hs3_below _ (by omega), hs1_ptr]
        refine ⟨hs3_fr, hwf3, ?_, hptr⟩
        dsimp only [DTMaskEntryValid]
        rw [hptr, hs3_below _ (by omega), hs1_e, hs3_below _ (by omega), hs1_d]
        refine ⟨he_eq ▸ rfl, rfl, fun j hj => by
            rw [hs3_below _ (by have := he_eq ▸ hj; omega)]; exact hs1_ep j hj,
          ?_, by rw [hs3_fr]; dsimp only [ep, sz]; omega⟩
        let leafMask : ℕ → ℕ := fun l => s.mem (env.bufB.leafAns + l)
        let σ : Fin e ≃ Fin (maskEdgePairs env.r0 mask).length := (Fin.castOrderIso he_eq).toEquiv
        let T₀ : MSFDT e := skelToTree e he2 d skelCode leafMask d 1
        have hT₀_hold : HoldsCompleteTree d (ep + 2 + e) (ep + 2 + e + 2 * (2 ^ d - 1)) d 1
            s3.mem T₀ := holdsCompleteTree_skelToTree he2 leafMask hleaf_lt
          (fun pk hpk => ⟨by
              rw [hs3_below (env.bufB.allPairA + pk) (by omega),
                hs1_below (env.bufB.allPairA + pk) (by omega) (by omega)]
              exact (hpairs_e pk hpk).1,
            by
              rw [hs3_below (env.bufB.allPairB + pk) (by omega),
                hs1_below (env.bufB.allPairB + pk) (by omega) (by omega)]
              exact (hpairs_e pk hpk).2⟩)
          (fun k hk => by
            have hpk_lt : skelCode / e.choose 2 ^ k % e.choose 2 < e.choose 2 :=
              Nat.mod_lt _ hnp_pos
            have h1 := hint_arr k hk
            exact ⟨(hs3_before _ (by omega)).trans (h1.1.trans (by
                rw [hs3_below (env.bufB.allPairA + skelCode / e.choose 2 ^ k % e.choose 2)
                    (by omega),
                  hs1_below (env.bufB.allPairA + skelCode / e.choose 2 ^ k % e.choose 2)
                    (by omega) (by omega)])),
              (hs3_before _ (by omega)).trans (h1.2.trans (by
                rw [hs3_below (env.bufB.allPairB + skelCode / e.choose 2 ^ k % e.choose 2)
                    (by omega),
                  hs1_below (env.bufB.allPairB + skelCode / e.choose 2 ^ k % e.choose 2)
                    (by omega) (by omega)]))⟩)
          (fun l hl => by
            rw [hs3_mem, ArrayCopy.copyPrefix_read hl, hs2_below _ (by omega),
              hs1_below _ (by omega) (by omega)])
          d 1 le_rfl (by rw [Nat.sub_self, Nat.pow_zero])
          (by rw [Nat.sub_self, Nat.zero_add, Nat.pow_one]; decide)
        obtain ⟨hT_comp, hT_hold⟩ := dtHoldsCompleteTreeCast he_eq T₀
          (skelToTree_isComplete e he2 d skelCode leafMask d 1) hT₀_hold
        refine ⟨(T₀.mapLeaves (Finset.map σ.toEmbedding)).liftEmb σ, hT_comp,
          (MSFDT.correct_iff _ _).mpr fun p' => ?_, by simpa [σ, ← he_eq] using hT_hold⟩
        let p : Equiv.Perm (Fin e) := σ.trans (p'.trans σ.symm)
        have hσp : σ.symm.trans (p.trans σ) = p' := by ext x; simp [p]
        rw [MSFTree.liftEmb_eval σ _ p p' (fun a b => by simp [p, σ]), MSFTree.mapLeaves_eval,
          skelToTree_eval_eq_leafMask]
        have hlg := hleaf_good p; dsimp only at hlg; rw [hσp] at hlg
        ext i; simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Equiv.coe_toEmbedding, leafMask, hlg, testBit_maskOfFinset, decide_eq_true_eq]
        exact ⟨fun ⟨a, ⟨ha_lt, hm⟩, ha_eq⟩ =>
            (congrArg (· ∈ _) (Fin.ext (congrArg Fin.val ha_eq))).mp hm,
          fun hi => ⟨σ.symm i, ⟨(σ.symm i).isLt.trans_eq he_eq,
            (congrArg (· ∈ _) (Fin.ext (by simp [σ]))).mpr hi⟩, σ.apply_symm_apply i⟩⟩
    exact ((Memory.FramedTriple.bind (hc1.mono le_rfl fun _ t ⟨ht_eq, _⟩ => by
        have hts : t = s1 := ht_eq.trans hs1_eq.symm
        exact hts ▸ ht1)).frame_mono fun a ha => by
      dsimp only [S, sz]
      simp only [Set.mem_union, Set.mem_Ico] at ha ⊢; omega).mono (by omega) fun _ _ h => h
  refine ⟨⟨h2, h2d_pos, hfit_fr, by dsimp only [sz]; omega, by dsimp only [ep, sz]; omega,
      by dsimp only [sz]; omega, by dsimp only [ep, sz]; omega, hint_safe,
      by rw [hs2_fr']; dsimp only [sz]; omega, by rw [hs2_fr']; dsimp only [ep, sz]; omega⟩, ?_⟩
  dsimp only [dtWriteFoundEntry, sEnv]
  have h5_2d : 5 * (2 ^ d - 1) ≤ 5 * 2 ^ d := Nat.mul_le_mul_left 5 (Nat.sub_le _ 1)
  refine Memory.FramedTriple.mono (Memory.FramedTriple.allocBlockDirty_bind hfit_fr
    (c := 2 * e + 5 * (2 ^ d - 1) + 2 * 2 ^ d + 3) ?_)
    (by omega) fun _ _ h => h
  refine Memory.FramedTriple.write_bind_of_mem (by dsimp only [ep, sz]; omega) hwf.frontier_fits
    (Set.mem_union_left _ rfl) ?_
  refine Memory.FramedTriple.write_bind_of_mem (by dsimp only [ep, sz]; omega)
    (hfit_fr.of_le (by omega))
    (Set.mem_union_right _ ⟨by dsimp only; omega, by dsimp only [sz]; omega⟩) ?_
  exact Memory.FramedTriple.write_bind_of_mem (by dsimp only [ep, sz]; omega)
    (hfit_fr.of_le (by have := Nat.lt_two_pow_self (n := d); omega))
    (Set.mem_union_right _ ⟨by dsimp only; omega, by dsimp only [sz]; omega⟩) htri_pre

/-- Allocates and writes a depth-`0` decision-tree table entry for `e ≤ 1` edges. -/
def dtWriteTrivialEntry (x : ℕ × ℕ × ℕ × ℕ) : Memory.Prog Unit := do
  let (tableBase, mask, e, edgePair) := x
  let epBlk ← Memory.allocBlockDirty (2 + e + 1)
  Memory.write (tableBase + mask) epBlk.base
  Memory.write epBlk.base e
  Memory.write (epBlk.base + 1) 0
  if e = 1 then
    let p ← Memory.read edgePair
    Memory.write (epBlk.base + 2) p
    Memory.write (epBlk.base + 3) 1
  else
    Memory.write (epBlk.base + 2) 0

/-- Word-RAM safety precondition for `dtWriteTrivialEntry`. -/
def dtWriteTrivialEntrySafe (w : ℕ) (x : ℕ × ℕ × ℕ × ℕ) (s : Memory.State) : Prop :=
  let (tableBase, mask, e, edgePair) := x
  let sz := 2 + e + 1
  Fits w 2 ∧ e ≤ 1 ∧ Fits w (s.frontier + sz) ∧
  tableBase + mask < s.frontier + sz ∧ s.frontier + 1 < s.frontier + sz ∧
  (e = 1 → edgePair < s.frontier + sz)

/-- Uniform `Realizes .exact` certificate for `dtWriteTrivialEntry` with `work = 0`. -/
theorem realizes_dtWriteTrivialEntry : Realizes .exact
    dtWriteTrivialEntry WordEncoding.encode WordEncoding.encode
    dtWriteTrivialEntrySafe (fun _ _ => 0) := by
  unfold dtWriteTrivialEntry
  realize [realizes_allocBlockDirty]
  all_goals
    try simp only [Memory.clientResult_allocBlockDirty] at *
    obtain ⟨h2, he1, hfr, htb, hep1, hed⟩ := h
    have hfront := hmem.frontier_fits
    fits

/-- Framed specification of `dtWriteTrivialEntry` establishing `DTMaskEntryValid` at depth `0`. -/
theorem dtWriteTrivialEntry_spec {w r0 tableBase mask e edgePair : ℕ}
    {s : Memory.State} (h2 : Fits w 2) (hwf : Memory.WellFormed w s)
    (he_le : e ≤ 1) (he_eq : e = (maskEdgePairs r0 mask).length)
    (htb : tableBase + 2 ^ r0.choose 2 ≤ s.frontier) (hmask : mask < 2 ^ r0.choose 2)
    (hep : edgePair + e ≤ s.frontier)
    (hdisj : tableBase + 2 ^ r0.choose 2 ≤ edgePair ∨ edgePair + e ≤ tableBase)
    (hfit : Fits w (s.frontier + 4))
    (hpairs : ∀ j (hj : j < (maskEdgePairs r0 mask).length),
      s.mem (edgePair + j) =
        pairIdx (maskEdgePairs r0 mask)[j].1.val (maskEdgePairs r0 mask)[j].2.val) :
    let prog := dtWriteTrivialEntry (tableBase, mask, e, edgePair)
    let sz := 2 + e + 1
    let S : Set ℕ := {tableBase + mask} ∪ Set.Ico s.frontier (s.frontier + sz)
    dtWriteTrivialEntrySafe w (tableBase, mask, e, edgePair) s ∧
    Memory.FramedTriple w s prog 8 S fun _ s' =>
      s'.frontier = s.frontier + sz ∧ Memory.WellFormed w s' ∧
      s'.mem (tableBase + mask) = s.frontier ∧ DTMaskEntryValid r0 tableBase mask 0 s' := by
  let ep := s.frontier; let sz := 2 + e + 1
  have hfit_sz : Fits w (s.frontier + sz) := hfit.of_le (by dsimp only [sz]; omega)
  let S : Set ℕ := {tableBase + mask} ∪ Set.Ico ep (ep + sz)
  let s0 : Memory.State := ⟨Function.update (Function.update (Function.update s.mem
    (tableBase + mask) ep) ep e) (ep + 1) 0, s.frontier + sz⟩
  have htri_raw : Memory.FramedTriple w s (dtWriteTrivialEntry (tableBase, mask, e, edgePair)) 7 S
      fun _ s' => s'.frontier = s.frontier + sz ∧ s'.mem (tableBase + mask) = ep ∧
        s'.mem ep = e ∧ s'.mem (ep + 1) = 0 ∧
        (e = 1 → s'.mem (ep + 2) = s.mem edgePair ∧ s'.mem (ep + 3) = 1) ∧
        (e = 0 → s'.mem (ep + 2) = 0) := by
    dsimp only [dtWriteTrivialEntry]
    refine Memory.FramedTriple.allocBlockDirty_bind hfit_sz ?_
    refine Memory.FramedTriple.write_bind_of_mem (by dsimp only [ep, sz]; omega)
      hwf.frontier_fits (Set.mem_union_left _ rfl) ?_
    refine Memory.FramedTriple.write_bind_of_mem (by dsimp only [ep, sz]; omega)
      (h2.of_le (by omega))
      (Set.mem_union_right _ ⟨by dsimp only [ep, sz]; omega, by dsimp only [ep, sz]; omega⟩) ?_
    refine Memory.FramedTriple.write_bind_of_mem (by dsimp only [ep, sz]; omega) (by fits)
      (Set.mem_union_right _ ⟨by dsimp only [ep, sz]; omega, by dsimp only [ep, sz]; omega⟩) ?_
    refine Memory.FramedTriple.ite (c := 3) ?_ ?_
    · intro he1
      refine Memory.FramedTriple.read_bind (by dsimp only [sz]; omega) ?_
      have hp_eq : s0.mem edgePair = s.mem edgePair := by
        dsimp only [s0]; rcases hdisj with h | h <;> update_simp
      rw [hp_eq]
      refine Memory.FramedTriple.write_bind_of_mem (by dsimp only [ep, sz]; omega) (hwf.mem_fits _)
        (Set.mem_union_right _ ⟨by dsimp only [ep, sz]; omega, by dsimp only [ep, sz]; omega⟩) ?_
      refine Memory.FramedTriple.write_bind_of_mem (by dsimp only [ep, sz]; omega) (by fits)
        (Set.mem_union_right _ ⟨by dsimp only [ep, sz]; omega, by dsimp only [ep, sz]; omega⟩) ?_
      refine Memory.FramedTriple.pure ⟨rfl, ?_, ?_, ?_, fun _ => ?_, fun h0 => by omega⟩
      · update_simp
      · update_simp
      · update_simp
      · update_simp; exact ⟨rfl, rfl⟩
    · intro hne1
      refine Memory.FramedTriple.mono (Memory.FramedTriple.write_bind_of_mem (c := 0)
        (by dsimp only [ep, sz]; omega) (by fits)
        (Set.mem_union_right _ ⟨by dsimp only [ep, sz]; omega, by dsimp only [ep, sz]; omega⟩) ?_)
        (by omega) fun _ _ h => h
      refine Memory.FramedTriple.pure ⟨rfl, ?_, ?_, ?_, fun h1 => absurd h1 hne1, fun _ => ?_⟩ <;>
        update_simp
  refine ⟨⟨h2, he_le, hfit_sz, by omega, by omega,
      fun _ => by omega⟩, ((htri_raw.wellFormed hwf).mono (by omega) ?_)⟩
  rintro _ s' ⟨⟨hfr, hptr, hep_m, hd_m, h1m, h0m⟩, hwf'⟩
  refine ⟨hfr, hwf', hptr, ?_⟩
  dsimp only [DTMaskEntryValid]; rw [hptr, hep_m, hd_m]
  refine ⟨he_eq ▸ rfl, rfl, fun j hj => ?_, ?_, by rw [hfr]; dsimp only [ep, sz]; omega⟩
  · by_cases he1 : e = 1
    · have hj0 : j = 0 := by omega
      subst hj0; rw [Nat.add_zero, (h1m he1).1]; exact hpairs 0 hj
    · omega
  · by_cases he1 : e = 1
    · let i0 : Fin (maskEdgePairs r0 mask).length := ⟨0, by omega⟩
      refine ⟨.leaf {i0}, MSFTree.isComplete_leaf, (MSFDT.correct_iff _ _).mpr fun p => ?_,
        holdsCompleteTree_leaf.mpr ⟨le_rfl, by decide, ?_⟩⟩
      · dsimp only [MSFTree.eval]; ext x
        have hx0 : x = i0 := Fin.ext (by omega); subst hx0
        simp only [Finset.mem_singleton, true_iff]
        rw [Cslib.Multigraph.mem_msf_iff p (Quot.out_eq (endsOfMask r0 mask i0)).symm]
        refine ⟨Finset.mem_univ _, fun hc => ?_⟩
        have hflt : {f | f ∈ (Finset.univ : Finset (Fin (maskEdgePairs r0 mask).length)) ∧
            p f < p i0} = ∅ := by
          ext f; simp only [Finset.mem_univ, true_and, Set.mem_empty_iff_false,
            iff_false]
          exact not_lt.mpr (Fin.le_of_eq (Fin.ext (by omega)))
        rw [hflt, Cslib.Multigraph.joins_empty_iff] at hc
        have hns := ((isSimple_iff _).mp (endsOfMask_isSimple r0 mask)).1 i0
        rw [← Quot.out_eq (endsOfMask r0 mask i0), Sym2.mk_isDiag_iff] at hns
        exact hns hc
      · rw [show ep + 2 + (maskEdgePairs r0 mask).length + 2 * (2 ^ 0 - 1) + (1 - 2 ^ 0) =
          ep + 3 by omega, (h1m he1).2]; simp [maskOfFinset, i0]
    · refine ⟨.leaf ∅, MSFTree.isComplete_leaf,
        (MSFDT.correct_iff _ _).mpr fun p => by ext x; exact absurd x.isLt (by omega),
        holdsCompleteTree_leaf.mpr ⟨le_rfl, by decide, ?_⟩⟩
      rw [show ep + 2 + (maskEdgePairs r0 mask).length + 2 * (2 ^ 0 - 1) + (1 - 2 ^ 0) =
        ep + 2 by omega, h0m (by omega)]; simp [maskOfFinset]

end Cslib.Algorithms.WordRAM.MinimumSpanningForest

end
