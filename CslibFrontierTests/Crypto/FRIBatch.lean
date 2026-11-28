/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module

import CslibFrontier.Crypto.Protocols.FRI.BatchProtocol
import CslibFrontierTests.Crypto.FRI
import Mathlib.Tactic.NormNum

/-!
# Concrete Nonvacuous Tests for Batched Multi-Round FRI (`BatchProtocol.lean`)

Exercises every public definition and theorem of
`CslibFrontier.Crypto.Protocols.FRI.BatchProtocol` from an ordinary `module` client (no
`import all`), sharing the `ZMod 257` (`d = 3`, `|L_0| = 8`, `m = 2` folding rounds / `4` total
batched IOP rounds, `kFinal = 1`, `q = 6`) fixture and degree-`4` root-count lemma
`card_agree_farWord_le_four` from `CslibFrontierTests.Crypto.FRI`:

1. **Structures, committed-opening count, direct-read schedule & locality.** Checks `FRIBatchStmt`
   (`eval`, `linear`, `equivProd`), `FRIBatchChal` (`toFRIChal`, `equivProd`, `card_friBatchChal`),
   the exact committed-proof-oracle opening count (`proofOracleQueries = 49`), the `q = 6`
   direct-read position schedule and `(t + 1) * q = 18` / `67` budgets (`batchInputWordReads`,
   `batchTotalWordQueries`), round-`0` non-opening (`round_ne_zero_of_mem_friBatchQueries`), and
   input-query locality (`friBatchDecide_congr_inputQueries`) on two distinct statements agreeing at
   the scheduled positions.
2. **Multi-round batched `PublicCoinIOP` completeness & BCS / ROM composition.** Certifies honest
   completeness (`friBatchIOP_complete`) on both an affine `3`-word statement `honestBatchStmt` and
   a homogeneous linear `2`-word statement `honestLinearStmt` (`f₀⁽⁰⁾ = 0`), pointwise
   `friBatchSingleAccepts` (`iopVerify_friBatchIOP_eq_true_iff`), deterministic BCS verification
   (`friBatchBCS_verify_prove_eq_true`), two-channel BCS ROM completeness
   (`friBatchBCS_honestROMGame_eq_pure_true`), and verifier Merkle query cost bounds
   (`isCostBounded_bcsMTCost_friBatchVerifyROM`).
3. **Nonvacuous false tuples & cheating-prover rejections.** Reuses `card_agree_farWord_le_four` to
   certify `badBatchStmt ∉ params257.batchProximityLang 2 2` and
   `badBatchStmt ∉ params257.batchCorrAgreeLang 2 (3 / 4 : ℝ)`, delegates honest-folding rejection
   directly to `farWord_iopVerify_eq_false`, and verifies batched cheating-prover rejection when a
   malicious prover substitutes the valid folded Reed–Solomon tables of `honestBatchStmt` (failing
   the round-`1` batching check).
4. **Language & exact-threshold rounding bridges.** Exercises `mem_batchProximityLang_zero_iff`
   (`t = 0`), `batchCorrAgreeLang_eq_batchProximityLang`, `batchCeilThreshold_bounds`, and
   `batchFloorThreshold_bounds` at the exact integer product boundary `n = 8, α = 5 / 8`
   (`α * 8 = 5`).
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.FRIBatch

open scoped BigOperators
open Polynomial
open Cslib Cslib.Code Cslib.OracleComp
open Cslib.Crypto.Protocols.BCS Cslib.Crypto.Protocols.FRI
open CslibFrontierTests.Crypto.FRI

/-! ### Part 1: Shared `ZMod 257` Fixture, Generator Words & Schedule / Opening Checks -/

-- Exact committed-opening count (`49`) and direct-read / combined word-query budgets (`18`, `67`)
-- at batch size `t = 2` (`3` input words).
example : params257.proofOracleQueries = 49 := rfl
example : params257.batchInputWordReads 2 = 18 := rfl
example : params257.batchTotalWordQueries 2 = 67 := rfl
example : params257.batchTotalWordQueries 2 =
    params257.kFinal + params257.q * (3 * params257.m + 2 + 3) :=
  params257.batchTotalWordQueries_eq 2

-- Challenge cardinality and definitional `equivProd` projections.
example : Fintype.card (FRIBatchChal (ZMod 257) 3 6 2) = 257 ^ 3 * (2 ^ 3) ^ 6 := by
  simpa only [ZMod.card] using card_friBatchChal (F := ZMod 257) 3 6 2

example (c : FRIBatchChal (ZMod 257) 3 6 2) :
    (FRIBatchChal.equivProd (ZMod 257) 3 6 2 c).1 = c.batchCoeffs ∧
      (FRIBatchChal.equivProd (ZMod 257) 3 6 2 c).2 = c.toFRIChal :=
  ⟨rfl, rfl⟩

-- Statement equivalence round-trip.
example (s : FRIBatchStmt (ZMod 257) 3 2) :
    (FRIBatchStmt.equivProd (ZMod 257) 3 2).symm (FRIBatchStmt.equivProd (ZMod 257) 3 2 s) = s :=
  rfl

/-- First generator degree-`< 4` codeword `1 + 4 X + 2 X^2` on `L_0`. -/
def termWord0 : OracleTable params257.d (ZMod 257) :=
  fun idx =>
    let x := params257.eval 0 idx
    1 + 4 * x + 2 * x ^ 2

/-- Second generator degree-`< 4` codeword `9 + 6 X^3` on `L_0`. -/
def termWord1 : OracleTable params257.d (ZMod 257) :=
  fun idx =>
    let x := params257.eval 0 idx
    9 + 6 * x ^ 3

theorem termWord0_mem_initialCode : termWord0 ∈ params257.initialCode := by
  refine mem_reedSolomon.mpr ⟨C 1 + C 4 * X + C 2 * X ^ 2 + C 0 * X ^ 3,
    poly_cubic_degree_lt 1 4 2 0, ?_⟩
  ext idx
  simp only [termWord0, eval_add, eval_mul, eval_pow, eval_C, eval_X, zero_mul, add_zero]

theorem termWord1_mem_initialCode : termWord1 ∈ params257.initialCode := by
  refine mem_reedSolomon.mpr ⟨C 9 + C 0 * X + C 0 * X ^ 2 + C 6 * X ^ 3,
    poly_cubic_degree_lt 9 0 0 6, ?_⟩
  ext idx
  simp only [termWord1, eval_add, eval_mul, eval_pow, eval_C, eval_X, zero_mul, add_zero]

/-- Concrete honest `3`-word affine batch statement `(honestWord, termWord0, termWord1)`. -/
def honestBatchStmt : FRIBatchStmt (ZMod 257) params257.d 2 where
  base := honestWord
  terms := ![termWord0, termWord1]

/-- Concrete honest homogeneous linear batch statement (`f₀⁽⁰⁾ = 0`). -/
def honestLinearStmt : FRIBatchStmt (ZMod 257) params257.d 2 :=
  FRIBatchStmt.linear ![termWord0, termWord1]

theorem honestBatchStmt_completeRel :
    params257.batchCompletenessRel 2 honestBatchStmt () := by
  refine ⟨honestWord_mem_initialCode, fun j => ?_⟩
  fin_cases j
  · exact termWord0_mem_initialCode
  · exact termWord1_mem_initialCode

theorem honestLinearStmt_completeRel :
    params257.batchCompletenessRel 2 honestLinearStmt () := by
  refine ⟨params257.initialCode.zero_mem, fun j => ?_⟩
  fin_cases j
  · exact termWord0_mem_initialCode
  · exact termWord1_mem_initialCode

theorem honestBatchStmt_mem_batchProximityLang :
    honestBatchStmt ∈ params257.batchProximityLang 2 2 :=
  params257.mem_batchProximityLang_of_batchCompletenessRel 2 honestBatchStmt_completeRel

/-- Combine a round-`0` batching vector `x : Fin 2 → ZMod 257` with the shared `3`-round single-word
challenge vector `sampleChals` so that `friTailChals (mkBatchChals x) = sampleChals` definitionally.
-/
def mkBatchChals (x : Fin 2 → ZMod 257) :
    Fin (params257.m + 2) → FRIBatchChal (ZMod 257) params257.d params257.q 2 :=
  Fin.cases
    ⟨x, 0, (sampleChals 0).queryIdxs⟩
    (fun j => ⟨![0, 0], (sampleChals j).foldScalar, (sampleChals j).queryIdxs⟩)

/-- Concrete `4`-round challenge vector with round-`0` batching scalars `![7, 13]` and tail
`sampleChals` (querying positions `1, 2, 3, 4, 5, 6` and leaving position `0` unscheduled). -/
def sampleBatchChals :
    Fin (params257.m + 2) → FRIBatchChal (ZMod 257) params257.d params257.q 2 :=
  mkBatchChals ![7, 13]

example (x : Fin 2 → ZMod 257) : friTailChals (mkBatchChals x) = sampleChals := rfl

-- Exact committed-opening list length (`49`), direct-read schedule length (`6`), and round-`0`
-- non-opening checks.
example : ((friBatchIOP params257 2).queries honestBatchStmt sampleBatchChals).length = 49 :=
  length_friBatchIOP_queries params257 2 honestBatchStmt sampleBatchChals

example : (friBatchInputQueries params257 2 sampleBatchChals).length = 6 :=
  length_friBatchInputQueries params257 2 sampleBatchChals

example :
    ((friBatchIOP params257 2).queries honestBatchStmt sampleBatchChals).all
      (fun p => p.1 != 0) = true := by
  rw [List.all_eq_true]
  intro p hp
  exact bne_iff_ne.mpr (round_ne_zero_of_mem_friBatchQueries params257 2 sampleBatchChals hp)

/-- Perturbed batch statement modifying `base` at unscheduled position `0 : Fin 8`. -/
def perturbedBatchStmt : FRIBatchStmt (ZMod 257) params257.d 2 where
  base := fun s => if s = ⟨0, by decide⟩ then honestWord s + 1 else honestWord s
  terms := ![termWord0, termWord1]

theorem perturbedBatchStmt_ne_honestBatchStmt : perturbedBatchStmt ≠ honestBatchStmt := by
  intro h
  have h0 : perturbedBatchStmt.base ⟨0, by decide⟩ = honestBatchStmt.base ⟨0, by decide⟩ :=
    congrFun (congrArg FRIBatchStmt.base h) ⟨0, by decide⟩
  exact absurd h0 (by decide)

-- Input-query locality: `friBatchDecide` gives the same decision on `perturbedBatchStmt` and
-- `honestBatchStmt` because they agree at all `6` scheduled positions in `friBatchInputQueries`.
example (answers : List (ZMod 257)) :
    friBatchDecide params257 2 perturbedBatchStmt sampleBatchChals answers =
      friBatchDecide params257 2 honestBatchStmt sampleBatchChals answers := by
  refine friBatchDecide_congr_inputQueries params257 2 sampleBatchChals (fun s hs => ?_) answers
  have hs_ne : s ≠ ⟨0, by decide⟩ := by
    intro h0
    subst h0
    exact absurd hs (by decide)
  exact ⟨by simp only [perturbedBatchStmt, honestBatchStmt, hs_ne, ↓reduceIte], fun _ => rfl⟩

/-! ### Part 2: Batched `PublicCoinIOP` Completeness, BCS Verification & ROM Composition -/

example :
    iopVerify (friBatchIOP params257 2) honestBatchStmt sampleBatchChals
      (iopProverOracles (friBatchIOP params257 2) honestBatchStmt () sampleBatchChals) = true :=
  friBatchIOP_complete params257 2 honestBatchStmt () honestBatchStmt_completeRel sampleBatchChals

example :
    iopVerify (friBatchIOP params257 2) honestLinearStmt sampleBatchChals
      (iopProverOracles (friBatchIOP params257 2) honestLinearStmt () sampleBatchChals) = true :=
  friBatchIOP_complete params257 2 honestLinearStmt () honestLinearStmt_completeRel sampleBatchChals

-- Pointwise `friBatchSingleAccepts` check on all `6` queried indices.
example (a : Fin params257.q) :
    friBatchSingleAccepts params257 2 honestBatchStmt sampleBatchChals
      (iopProverOracles (friBatchIOP params257 2) honestBatchStmt () sampleBatchChals)
      ((sampleBatchChals (Fin.last (params257.m + 1))).queryIdxs a) :=
  (iopVerify_friBatchIOP_eq_true_iff params257 2 honestBatchStmt sampleBatchChals _).mp
    (friBatchIOP_complete params257 2 honestBatchStmt () honestBatchStmt_completeRel
      sampleBatchChals) a

def constBatchFS (_ : FRIBatchStmt (ZMod 257) params257.d 2) (rts : List (List Bool)) :
    FRIBatchChal (ZMod 257) params257.d params257.q 2 :=
  sampleBatchChals ⟨rts.length % 4, Nat.mod_lt _ (by decide)⟩

-- Deterministic BCS verification of the honest batched FRI proof (sharing `idHash` from `FRI`).
example :
    bcsVerify (friBatchIOP params257 2) (fun _ => idHash) [] (encZMod (p := 257)) constBatchFS
      honestBatchStmt
      (bcsProve (friBatchIOP params257 2) (fun _ => idHash) [] (encZMod (p := 257)) constBatchFS
        honestBatchStmt ()) = true :=
  friBatchBCS_verify_prove_eq_true params257 2 (fun _ => idHash) []
    CslibFrontierTests.Crypto.MerkleTestHash.length_polyHash (encZMod (p := 257))
    constBatchFS honestBatchStmt_completeRel

-- Perfect completeness in the lazy two-channel BCS random-oracle model for every digest length `σ`.
example (σ : ℕ) :
    bcsHonestROMGame (friBatchIOP params257 2) (encZMod (p := 257)) honestBatchStmt () σ =
      PMF.pure true :=
  friBatchBCS_honestROMGame_eq_pure_true params257 2 (encZMod (p := 257))
    honestBatchStmt_completeRel σ

-- Verifier Merkle query cost bound (`49 * (3 + 1) = 196`, independent of `t = 2`).
example (prf : BCSProof (params257.m + 2) (ZMod 257))
    (hops : ∀ op ∈ prf.openings, op.path.length ≤ params257.d) :
    IsCostBounded bcsMTCost
      (bcsVerifyROM (friBatchIOP params257 2) (encZMod (p := 257)) honestBatchStmt prf) 196 :=
  isCostBounded_bcsMTCost_friBatchVerifyROM params257 2 (encZMod (p := 257)) honestBatchStmt prf
    hops

/-! ### Part 3: Nonvacuous False Tuples & Cheating-Prover Rejections -/

/-- Affine batch statement replacing the second generator word by `farWord`. -/
def badBatchStmt : FRIBatchStmt (ZMod 257) params257.d 2 where
  base := honestWord
  terms := ![termWord0, farWord]

/-- Linear batch statement `[honestWord, farWord]`. -/
def badLinearStmt : FRIBatchStmt (ZMod 257) params257.d 2 :=
  FRIBatchStmt.linear ![honestWord, farWord]

/-- `badBatchStmt` has correlated agreement on at most `4 < 6 = 8 - 2` points (by the shared
degree-`4` root-count lemma `card_agree_farWord_le_four`), so it lies outside
`params257.batchProximityLang 2 2`. -/
theorem badBatchStmt_not_mem_batchProximityLang :
    badBatchStmt ∉ params257.batchProximityLang 2 2 := by
  rintro ⟨D', hcard, _, _, v, hv, hagree⟩
  have hle : D'.card ≤ 4 := card_agree_farWord_le_four (hv 1) fun s hs => (hagree s hs).2 1
  change 2 ^ 3 - 2 ≤ D'.card at hcard
  omega

theorem badLinearStmt_not_mem_batchProximityLang :
    badLinearStmt ∉ params257.batchProximityLang 2 2 := by
  rintro ⟨D', hcard, _, _, v, hv, hagree⟩
  have hle : D'.card ≤ 4 := card_agree_farWord_le_four (hv 1) fun s hs => (hagree s hs).2 1
  change 2 ^ 3 - 2 ≤ D'.card at hcard
  omega

-- Exercise `lt_two_pow_of_not_mem_batchProximityLang`.
example : 2 < 2 ^ params257.d :=
  params257.lt_two_pow_of_not_mem_batchProximityLang badBatchStmt_not_mem_batchProximityLang

/-- `badBatchStmt` also lies outside the real-density language
`params257.batchCorrAgreeLang 2 (3 / 4)` via the ceiling `Set` equality (`⌈(3 / 4) * 8⌉₊ = 6`). -/
theorem badBatchStmt_not_mem_batchCorrAgreeLang :
    badBatchStmt ∉ params257.batchCorrAgreeLang 2 (3 / 4 : ℝ) := by
  rw [batchCorrAgreeLang_eq_batchProximityLang params257 2 (by norm_num)]
  have hceil : ⌈(3 / 4 : ℝ) * (2 ^ params257.d : ℝ)⌉₊ = 6 := by
    change ⌈(3 / 4 : ℝ) * (2 ^ 3 : ℝ)⌉₊ = 6
    norm_num
  rw [hceil]
  exact badBatchStmt_not_mem_batchProximityLang

-- Rejection 1 (delegated to `FRI.farWord_iopVerify_eq_false` with zero repeated folding proof):
-- folding `badLinearStmt` at batching vector `![0, 1]` evaluates `farWord` on `sampleChals`.
theorem badLinearStmt_iopVerify_eq_false :
    iopVerify (friBatchIOP params257 2) badLinearStmt (mkBatchChals ![0, 1])
      (iopProverOracles (friBatchIOP params257 2) badLinearStmt () (mkBatchChals ![0, 1])) =
      false := by
  rw [iopVerify_friBatchIOP_eq_iopVerify_friIOP]
  have hor_eq :
      (fun j => iopProverOracles (friBatchIOP params257 2) badLinearStmt () (mkBatchChals ![0, 1])
        j.succ) =
      iopProverOracles (friIOP params257)
        (badLinearStmt.eval (mkBatchChals ![0, 1] 0).batchCoeffs) ()
        (friTailChals (mkBatchChals ![0, 1])) := by
    funext j
    exact iopProverOracles_friBatchIOP_succ params257 2 badLinearStmt (mkBatchChals ![0, 1]) j
  have heval : badLinearStmt.eval (mkBatchChals ![0, 1] 0).batchCoeffs = farWord := by
    have h0 : (mkBatchChals ![0, 1] 0).batchCoeffs = ![0, 1] := rfl
    rw [h0]
    ext s
    simp only [FRIBatchStmt.eval_apply, badLinearStmt, FRIBatchStmt.linear, Fin.sum_univ_two]
    change 0 + (0 * honestWord s + 1 * farWord s) = farWord s
    simp only [zero_mul, one_mul, zero_add]
  rw [hor_eq, heval]
  exact farWord_iopVerify_eq_false

-- Rejection 2 (batched cheating-prover regression): a malicious prover who commits the valid
-- Reed–Solomon folded tables of `honestBatchStmt` (passing all folding checks and the final
-- Lagrange check) is rejected by the round-`1` affine batching check!
theorem badBatchStmt_cheatingProver_iopVerify_eq_false :
    iopVerify (friBatchIOP params257 2) badBatchStmt sampleBatchChals
      (iopProverOracles (friBatchIOP params257 2) honestBatchStmt () sampleBatchChals) = false := by
  by_contra hne
  have htrue :
      iopVerify (friBatchIOP params257 2) badBatchStmt sampleBatchChals
        (iopProverOracles (friBatchIOP params257 2) honestBatchStmt () sampleBatchChals) = true :=
    Bool.eq_true_of_not_eq_false hne
  have hbatch := ((iopVerify_friBatchIOP_eq_true_iff params257 2 badBatchStmt sampleBatchChals _).mp
    htrue ⟨0, by decide⟩).1
  have hs : (sampleBatchChals (Fin.last (params257.m + 1))).queryIdxs ⟨0, by decide⟩ =
      ⟨1, by decide⟩ := rfl
  rw [hs] at hbatch
  have hor : iopProverOracles (friBatchIOP params257 2) honestBatchStmt () sampleBatchChals
      (⟨0, Nat.zero_lt_succ params257.m⟩ : Fin (params257.m + 1)).succ ⟨1, by decide⟩ =
      honestBatchStmt.eval (sampleBatchChals 0).batchCoeffs ⟨1, by decide⟩ := by
    rw [iopProverOracles_friBatchIOP_succ]
    change padOracle (i := 0) (honestBatchStmt.eval (sampleBatchChals 0).batchCoeffs)
        ⟨1, by decide⟩ = _
    exact padOracle_apply_of_lt _ _ (by decide : (1 : ℕ) < 2 ^ (params257.d - 0))
  change iopProverOracles (friBatchIOP params257 2) honestBatchStmt () sampleBatchChals
      (⟨0, Nat.zero_lt_succ params257.m⟩ : Fin (params257.m + 1)).succ ⟨1, by decide⟩ =
    badBatchStmt.eval (sampleBatchChals 0).batchCoeffs ⟨1, by decide⟩ at hbatch
  rw [hor] at hbatch
  have h0 : (sampleBatchChals 0).batchCoeffs = ![7, 13] := rfl
  rw [h0] at hbatch
  have hdiff : honestBatchStmt.eval ![7, 13] ⟨1, by decide⟩ ≠
      badBatchStmt.eval ![7, 13] ⟨1, by decide⟩ := by
    simp only [FRIBatchStmt.eval, honestBatchStmt, badBatchStmt, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    decide
  exact hdiff hbatch

/-! ### Part 4: `t = 0` Equivalence & Ceiling / Floor Exact-Threshold Rounding Bridges -/

-- Exercise `mem_batchProximityLang_zero_iff` on both a close word and a far word.
example : (⟨honestWord, Fin.elim0⟩ : FRIBatchStmt (ZMod 257) params257.d 0) ∈
    params257.batchProximityLang 0 2 := by
  rw [mem_batchProximityLang_zero_iff]
  exact honestWord_mem_proximityLang

example : (⟨farWord, Fin.elim0⟩ : FRIBatchStmt (ZMod 257) params257.d 0) ∉
    params257.batchProximityLang 0 2 := by
  rw [mem_batchProximityLang_zero_iff]
  exact farWord_not_mem_proximityLang

-- Exercise `batchCeilThreshold_bounds` on both dyadic (`α = 3 / 4`) and non-dyadic (`α = 5 / 7`)
-- densities.
example :
    let e := 2 ^ params257.d - ⌈(3 / 4 : ℝ) * (2 ^ params257.d : ℝ)⌉₊
    e = 2 ∧ e < 2 ^ params257.d ∧
      (((2 ^ params257.d - e - 1 : ℕ) : ℝ) / (2 ^ params257.d : ℝ)) < (3 / 4 : ℝ) ∧
      (e : ℝ) / (2 ^ params257.d : ℝ) ≤ 1 - (3 / 4 : ℝ) := by
  have h := batchCeilThreshold_bounds params257 (α := (3 / 4 : ℝ)) (by norm_num) (by norm_num)
  have he : 2 ^ params257.d - ⌈(3 / 4 : ℝ) * (2 ^ params257.d : ℝ)⌉₊ = 2 := by
    change 2 ^ 3 - ⌈(3 / 4 : ℝ) * (2 ^ 3 : ℝ)⌉₊ = 2
    norm_num
  exact ⟨he, h.1, h.2.1, h.2.2⟩

example :
    let e := 2 ^ params257.d - ⌈(5 / 7 : ℝ) * (2 ^ params257.d : ℝ)⌉₊
    e < 2 ^ params257.d ∧
      (((2 ^ params257.d - e - 1 : ℕ) : ℝ) / (2 ^ params257.d : ℝ)) < (5 / 7 : ℝ) ∧
      (e : ℝ) / (2 ^ params257.d : ℝ) ≤ 1 - (5 / 7 : ℝ) :=
  batchCeilThreshold_bounds params257 (α := (5 / 7 : ℝ)) (by norm_num) (by norm_num)

-- Exercise `batchFloorThreshold_bounds` at the exact integer product boundary `n = 8, α = 5 / 8`
-- (`α * 8 = 5 ∈ ℤ`, so `B = 5`, `e = 2`, and `2 / 8 < 3 / 8 = 1 - 5 / 8` strictly), certifying that
-- every shared agreement set of `badBatchStmt` with `params257.initialCode` has density `≤ 5 / 8`.
example :
    (∀ (D' : Finset (Fin (2 ^ params257.d))) (v₀ : OracleTable params257.d (ZMod 257)),
      v₀ ∈ params257.initialCode →
      ∀ v : Fin 2 → OracleTable params257.d (ZMod 257),
        (∀ j, v j ∈ params257.initialCode) →
        (∀ s ∈ D', badBatchStmt.base s = v₀ s ∧ ∀ j, badBatchStmt.terms j s = v j s) →
        (D'.card : ℝ) / (2 ^ params257.d : ℝ) ≤ (5 / 8 : ℝ)) ∧
    ((2 ^ params257.d - 1 - ⌊(5 / 8 : ℝ) * (2 ^ params257.d : ℝ)⌋₊ : ℕ) : ℝ) /
      (2 ^ params257.d : ℝ) < 1 - (5 / 8 : ℝ) := by
  have h := batchFloorThreshold_bounds params257 2 badBatchStmt (α := (5 / 8 : ℝ))
    (by norm_num) (by norm_num)
  have he : 2 ^ params257.d - 1 - ⌊(5 / 8 : ℝ) * (2 ^ params257.d : ℝ)⌋₊ = 2 := by
    change 2 ^ 3 - 1 - ⌊(5 / 8 : ℝ) * (2 ^ 3 : ℝ)⌋₊ = 2
    norm_num
  refine ⟨h.1.mpr ?_, h.2.2.2.2⟩
  rw [he]
  exact badBatchStmt_not_mem_batchProximityLang

end CslibFrontierTests.Crypto.FRIBatch
