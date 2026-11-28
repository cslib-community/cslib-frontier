/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module

import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Crypto.Primitives.UHF.CBCMAC
import CslibFrontier.Crypto.Primitives.UHF.Cascade

/-!
# Tests for the prefix-free collision wrapper

Use a proper-prefix pair in the CBC word domain with a two-block cap. Its queries use the
three-block domain. The advantage bound uses the CBC chaining identity for its real game.
A repeated valid guess makes no external query. The batch wrapper also skips repeated and
malformed guesses and respects a cap on the batch.
-/

set_option linter.privateModule false

open Cslib Cslib.Crypto Cslib.Crypto.UHF Cslib.Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

private def properPrefixGuess : CollisionGuess (List Bool) :=
  ⟨[true, false], [true, false, false, false]⟩

private theorem aligned_of_cbcBlockValid {cap : ℕ → ℕ} {n : ℕ} {word : List Bool}
    (hv : cbcBlockValid cap n word = true) : 0 < n ∧ n ∣ word.length := by
  simp only [cbcBlockValid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
  obtain ⟨⟨hNonempty, hMod⟩, hCap⟩ := hv
  refine ⟨?_, Nat.dvd_of_mod_eq_zero hMod⟩
  cases n with
  | zero => exact False.elim (Nat.not_le_of_gt hNonempty (by simpa using hCap))
  | succ n => exact Nat.zero_lt_succ n

private theorem blockCount_le_of_cbcBlockValid {cap : ℕ → ℕ} {n : ℕ} {word : List Bool}
    (hWord : cbcBlockValid cap n word = true) : word.length / n ≤ cap n := by
  simp only [cbcBlockValid, Bool.and_eq_true, decide_eq_true_eq] at hWord
  exact Nat.div_le_of_le_mul (by simpa only [Nat.mul_comm] using hWord.2)

private theorem cbcBlockValid_append {cap : ℕ → ℕ} {n : ℕ} {word block : List Bool}
    (hWord : cbcBlockValid cap n word = true) (hBlock : block.length = n) :
    cbcBlockValid (fun k => cap k + 1) n (word ++ block) = true := by
  simp only [cbcBlockValid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hWord ⊢
  obtain ⟨⟨hPos, hMod⟩, hCap⟩ := hWord
  rw [List.length_append, hBlock, Nat.add_mul, one_mul]
  refine ⟨⟨hPos.trans_le (Nat.le_add_right _ _), ?_⟩, Nat.add_le_add_right hCap _⟩
  rw [Nat.add_mod, hMod, Nat.mod_self, Nat.zero_add, Nat.zero_mod]

private theorem cbcMacFamily_extend (family : List Bool → List Bool → List Bool)
    {cap : ℕ → ℕ} {n : ℕ} {key left right block : List Bool} (hKey : key.length = n)
    (hLeft : cbcBlockValid cap n left = true) (hRight : cbcBlockValid cap n right = true)
    (hBlock : block.length = n)
    (hEq : cbcMacFamily family key left = cbcMacFamily family key right) :
    cbcMacFamily family key (left ++ block) = cbcMacFamily family key (right ++ block) := by
  obtain ⟨hPos, hl⟩ := aligned_of_cbcBlockValid hLeft
  have hr := (aligned_of_cbcBlockValid hRight).2
  simp only [cbcMacFamily, hKey] at hEq ⊢
  rw [cbcMacWord_append_block family hPos key hl hBlock,
    cbcMacWord_append_block family hPos key hr hBlock, hEq]

example : IsPrefixFreeOraclePPT (cbcBlockValid (fun _ => 3)) id
    (prefixFreeCollisionReduction id id (cbcBlockValid (fun _ => 2))
      (fun _ => pure properPrefixGuess)) := by
  exact isPrefixFreeOraclePPT_prefixFreeCollisionReduction ComputableInPolyTime.id'
    ComputableInPolyTime.id' (computableInPolyTime_cbcBlockValid (ComputableInPolyTime.const 2))
    (fun _ _ => aligned_of_cbcBlockValid) (ComputableInPolyTime.const properPrefixGuess).isPPTOn

example :
    wordQueryRunDist id
      (prefixFreeCollisionReduction id id (cbcBlockValid (fun _ => 2))
        (fun _ => pure properPrefixGuess) 2 []) =
    PMF.pure (true, [[true, false, true, true], [true, false, false, false, true, true]]) := by
  have hvalid : (cbcBlockValid (fun _ => 2) 2 properPrefixGuess.first &&
      cbcBlockValid (fun _ => 2) 2 properPrefixGuess.second &&
      decide (properPrefixGuess.first ≠ properPrefixGuess.second)) = true := by decide
  simp only [prefixFreeCollisionReduction, prefixFreeCollisionReductionWithCap,
    wordQueryRunDist_sample_bind, ProbComp.eval_pure, PMF.pure_bind, ite_eq_left hvalid,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, wordQueryRunDist_query_bind,
    wordQueryRunDist_pure, PMF.pure_map]
  rfl

example :
    wordQueryRunDist id
      (prefixFreeCollisionReduction id id (cbcBlockValid (fun _ => 2))
        (fun _ => pure ⟨[true, false], [true, false]⟩) 2 []) = PMF.pure (false, []) := by
  simp [prefixFreeCollisionReduction, prefixFreeCollisionReductionWithCap]

example (family : List Bool → List Bool → List Bool) :
    Game.succProbability (collisionGame pure (fun _ => cbcBlockValid (fun _ => 2))
      (fun _ d (key : BitString d) => cbcMacFamily family (List.ofFn key))
      (fun _ => pure properPrefixGuess) 2) ≤
    let reduction := prefixFreeCollisionReduction id id (cbcBlockValid (fun _ => 2))
      (fun _ => pure properPrefixGuess)
    Game.advantage
      (ProbComp.eval (prfRealGameOn (cbcBlockValid (fun _ => 3)) (cbcMacFamily family) reduction 2))
      (ProbComp.eval (prfIdealGameOn (cbcBlockValid (fun _ => 3)) id reduction 2)) +
      ((2 : ℝ≥0) ^ 2)⁻¹ := by
  exact succProbability_collisionGame_le_prefixFreeCollisionReduction
    (cbcMacFamily family) _ _ cbcBlockValid_append (cbcMacFamily_extend family)

private def batchGuesses : List (List Bool) :=
  [[false, false], [false, false], [false, true], [true], [true, true]]

example : IsPrefixFreeOraclePPT (cbcBlockValid (fun _ => 3)) id
    (prefixFreeBatchReduction id id (fun _ => 4) (cbcBlockValid (fun _ => 2))
      (fun _ => pure batchGuesses)) :=
  isPrefixFreeOraclePPT_prefixFreeBatchReduction ComputableInPolyTime.id' ComputableInPolyTime.id'
    (ComputableInPolyTime.const 4)
    (computableInPolyTime_cbcBlockValid (ComputableInPolyTime.const 2))
    (fun _ _ => aligned_of_cbcBlockValid)
    (ComputableInPolyTime.const batchGuesses).isPPTOn

example :
    wordQueryRunDist id
      (prefixFreeBatchReduction id (fun _ => 1) (fun _ => 4) (cbcBlockValid (fun _ => 2))
        (fun _ => pure batchGuesses) 2 []) =
    PMF.pure (true, [[false, false, true, false], [false, true, true, false]]) := by
  have hqueries : prefixFreeBatchQueries 2 4 (cbcBlockValid (fun _ => 2) 2) batchGuesses =
      [[false, false, true, false], [false, true, true, false]] := by
    unfold prefixFreeBatchQueries
    dsimp only
    rw [PRF.freshBatchWordBlock_eq_map_freshBatchBlock]
    decide
  simp only [prefixFreeBatchReduction, wordQueryRunDist_sample_bind, ProbComp.eval_pure,
    PMF.pure_bind, id_eq, hqueries, wordQueryRunDist_mapM_query_pure]
  rfl

/-- A width-one batch containing a proper-prefix pair uses the remaining block even when
the total block count exceeds the alphabet size. -/
example : InformationTheory.IsPrefixFree
    ((fun word => word ++ [true]) '' {word | word ∈ [[false], [false, false]]}) :=
  PRF.isPrefixFree_append_of_freshBatchWordBlock_eq_some (width := 1) (by decide) (by simp) (by
    rw [PRF.freshBatchWordBlock_eq_map_freshBatchBlock]
    decide)

/-- The combined bound applies to the CBC domain with a proper-prefix pair and extra block. -/
example (family : List Bool → List Bool → List Bool) :
    let guessBatch : ℕ × ℕ → ProbComp (List (List Bool)) :=
      fun _ => pure [[false, false, false], [false, false, false, true, false, false]]
    let wrapper := prefixFreeBatchReduction id id (fun _ => 2) (cbcBlockValid (fun _ => 2))
      guessBatch
    Game.succProbability (multiQueryGame pure (fun _ d => cbcBlockValid (fun _ => 2) d)
      (fun _ d (key : BitString d) => cbcMacFamily family (List.ofFn key)) guessBatch 3) ≤
    Game.advantage
      (ProbComp.eval (prfRealGameOn (cbcBlockValid (fun _ => 3)) (cbcMacFamily family) wrapper 3))
      (ProbComp.eval (prfIdealGameOn (cbcBlockValid (fun _ => 3)) id wrapper 3)) +
      (2 : ℕ).choose 2 / (2 : ℝ≥0) ^ 3 := by
  dsimp only
  refine succProbability_multiQueryGame_le_prefixFreeBatchReduction
    (cbcMacFamily family) _ 3 2 ?_ ?_ (by decide) cbcBlockValid_append (cbcMacFamily_extend family)
  · intro guesses hguesses
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hguesses
    subst guesses
    decide
  · exact fun _ => blockCount_le_of_cbcBlockValid

/-- The ideal bound allows repeated and malformed guesses before batch preparation. -/
example :
    let guessBatch : ℕ × ℕ → ProbComp (List (List Bool)) := fun _ =>
      pure [[false, false, false], [false, false, false], [true],
        [false, false, false, true, false, false]]
    ProbComp.eval (prfIdealGameOn (cbcBlockValid (fun _ => 3)) id
      (prefixFreeBatchReduction id id (fun _ => 4) (cbcBlockValid (fun _ => 2)) guessBatch)
      3) true ≤ (4 : ℕ).choose 2 / (2 : ℝ≥0∞) ^ 3 := by
  dsimp only
  exact eval_prfIdealGameOn_prefixFreeBatchReduction_le _ _ cbcBlockValid_append

example {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family)
    {cap : ℕ → ℕ} (hcap : ComputableInPolyTime cap encUnary encUnary) :
    IsComputationalUHF encUnary encBits pure (fun _ d => cbcBlockValid cap d)
      (fun _ d (key : BitString d) => cbcMacFamily family (List.ofFn key)) := by
  have hPRF := hF.prefixFreePRF_cbcMac (hcap.unary_add' (ComputableInPolyTime.const 1))
  exact isComputationalUHF_of_extendable_prefixFreePRF hPRF ComputableInPolyTime.id'
    (computableInPolyTime_cbcBlockValid hcap) (fun _ _ => aligned_of_cbcBlockValid)
    cbcBlockValid_append (cbcMacFamily_extend family) negligible_inv_two_pow

/-- The CBC-MAC application allows empty messages in the hash domain. -/
example {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family) :
    IsMultiQueryUHF encUnary encBits pure (fun _ d => lpBlockValid (fun _ => 2) d)
      (fun _ d (key : BitString d) => cbcMacFamily family (List.ofFn key)) := by
  exact hF.isMultiQueryUHF_cbcMac (.const 2)

example {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family) :
    IsComputationalUHF encUnary encBits pure (fun _ d => lpBlockValid (fun _ => 2) d)
      (fun _ d (key : BitString d) => cbcMacFamily family (List.ofFn key)) :=
  hF.isComputationalUHF_cbcMac (.const 2)

private def emptyWordPair : ℕ × ℕ → ProbComp (CollisionGuess (List Bool)) :=
  fun _ => pure ⟨[], [false, false, false]⟩

example : IsOraclePPT encBool
    (cbcMacMultiQueryReduction (fun _ => 4) (fun _ => 2)
      (fun p => collisionPairToBatch (emptyWordPair p))) :=
  isOraclePPT_cbcMacMultiQueryReduction (.const 4) (.const 2)
    (isPPTOn_collisionPairToBatch
      (ComputableInPolyTime.const
        (⟨[], [false, false, false]⟩ : CollisionGuess (List Bool))).isPPTOn)

/-- The pair bound specializes (7.10) to two messages, one of which can be empty. -/
example {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family) (n : ℕ) :
    let reduction := cbcMacMultiQueryReduction (fun _ => 4) (fun _ => 2)
      (fun p => collisionPairToBatch (emptyWordPair p))
    Game.succProbability (collisionGame pure (fun _ d => lpBlockValid (fun _ => 4) d)
      (fun _ d (key : BitString d) => cbcMacFamily family (List.ofFn key)) emptyWordPair n) ≤
    Game.advantage (ProbComp.eval (prfRealGame id family reduction n))
      (ProbComp.eval (prfIdealGame id id reduction n)) +
      (2 : ℝ≥0) ^ 2 * (4 + 1) ^ 2 / (2 * 2 ^ n) + 1 / (2 : ℝ≥0) ^ n :=
  succProbability_collisionGame_cbcMac_le hF.length_eq (fun _ => 4) emptyWordPair n

private def emptyWordBatch : ℕ × ℕ → ProbComp (List (List Bool)) :=
  fun _ => pure [[], [false, false, false]]

example : IsOraclePPT encBool
    (cbcMacMultiQueryReduction (fun _ => 4) (fun _ => 2) emptyWordBatch) :=
  isOraclePPT_cbcMacMultiQueryReduction (.const 4) (.const 2)
    (ComputableInPolyTime.const [[], [false, false, false]]).isPPTOn

/-- The concrete CBC bound applies at zero and at an exhausted alphabet budget (width three). -/
example {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family) (n : ℕ) :
    let reduction := cbcMacMultiQueryReduction (fun _ => 4) (fun _ => 2) emptyWordBatch
    Game.succProbability (multiQueryGame pure (fun _ d => lpBlockValid (fun _ => 4) d)
      (fun _ d (key : BitString d) => cbcMacFamily family (List.ofFn key)) emptyWordBatch n) ≤
    Game.advantage (ProbComp.eval (prfRealGame id family reduction n))
      (ProbComp.eval (prfIdealGame id id reduction n)) +
      (2 : ℝ≥0) ^ 2 * (4 + 1) ^ 2 / (2 * 2 ^ n) + (2 : ℕ).choose 2 / (2 : ℝ≥0) ^ n := by
  dsimp only
  refine succProbability_multiQueryGame_cbcMac_le hF.length_eq (fun _ => 4) (fun _ => 2)
    emptyWordBatch ?_
  intro guesses hGuesses
  simp only [emptyWordBatch, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hGuesses
  subst guesses
  decide

example : lpBlockValid (fun _ => 2) 3 [] = true ∧
    (prefixFreeBatchQueries 3 2 (lpBlockValid (fun _ => 2) 3) [[], [false, false, false]]).length =
      2 := by
  constructor
  · decide
  · have hFresh : PRF.freshBatchWordBlock 3 [[], [false, false, false]] =
        some [true, false, false] := by
      rw [PRF.freshBatchWordBlock_eq_map_freshBatchBlock]
      decide
    change (if (PRF.freshBatchWordBlock 3 [[], [false, false, false]]).isSome then
      [[], [false, false, false]].map (fun w => w ++
        (PRF.freshBatchWordBlock 3 [[], [false, false, false]]).getD []) else []).length = 2
    rw [hFresh]
    rfl

-- The cascade bound accepts the empty message and its one-block extension in the same batch.
example {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family) :
    ∃ reduction : OracleDistinguisher, IsOraclePPT encBool reduction ∧
      (reduction 3 []).IsQueryBounded 2 ∧
      Game.succProbability (multiQueryGame pure (fun _ d => lpBlockValid (fun _ => 2) d)
        (fun _ d (key : BitString d) => cascadeFamily id family (List.ofFn key)) emptyWordBatch 3) ≤
      (6 : ℕ) * Game.advantage (ProbComp.eval (prfRealGame id family reduction 3))
        (ProbComp.eval (prfIdealGame id id reduction 3)) + (2 : ℕ).choose 2 / (2 : ℝ≥0) ^ 3 := by
  have hFacts (cap : ℕ) {word : List Bool} (hWord : lpBlockValid (fun _ => cap) 3 word = true) :
      3 ∣ word.length ∧ word.length ≤ cap * 3 := by
    simp only [lpBlockValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hWord
    exact ⟨Nat.dvd_of_mod_eq_zero hWord.1, hWord.2⟩
  refine succProbability_multiQueryGame_cascade_le_pointwise emptyWordBatch 3 2 2
    ComputableInPolyTime.id' (computableInPolyTime_lpBlockValid (.const 2))
    (computableInPolyTime_lpBlockValid (.const 3)) hF.length_eq hF.polyTime
    (ComputableInPolyTime.const [[], [false, false, false]]).isPPTOn (by decide)
    (fun _ hWord => (hFacts 2 hWord).1) (fun _ hWord => (hFacts 2 hWord).2)
    (fun _ hWord => (hFacts 3 hWord).1) (fun _ hWord => (hFacts 3 hWord).2)
    (by decide) ?_ ?_
  · intro word block hWord hBlock
    obtain ⟨hdiv, hcap⟩ := hFacts 2 hWord
    have hBlockLength : block.length = 3 := hBlock
    simp only [lpBlockValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.length_append,
      hBlockLength, Nat.add_mod_right, Nat.mod_eq_zero_of_dvd hdiv, true_and]
    omega
  · intro guesses hGuesses
    simp only [emptyWordBatch, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hGuesses
    subst guesses
    decide
