/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module

public import CslibFrontier.Crypto.Protocols.FRI.BatchProtocol
public import CslibFrontierTests.Crypto.FRI
import CslibFrontier.Foundations.Data.Hamming
import Mathlib.Tactic.NormNum

/-!
# Concrete Nonvacuous Tests for Smooth `2^{sᵢ}`-to-1 FRI & Batched FRI Protocol

Exercises all smooth folding, protocol, completeness, BCS composition, query-accounting, and
binary-equivalence APIs added across `Folding.lean`, `Protocol.lean`, and `BatchProtocol.lean`
from an ordinary `module` client (no `import all`), over `ZMod 257` on a `32`-point multiplicative
coset (`d = 5`, `ω = 15` primitive `32`-nd root of unity since `15 ^ 16 ≡ -1 (mod 257)`,
`kFinal = 1`, `dim 0 = 16`, rate `ρ = 1 / 2`, `q = 6`):

1. **Two smooth folding schedules (`![2, 2]` pure 4-to-1 and `![3, 1]` mixed 8-to-1 + 2-to-1):**
   * `params257Fold4x4`: `stepLog = ![2, 2]` (`32 → 8 → 2`, `dim: 16 → 4 → 1`,
     `proofOracleQueries = 73`, `totalWordQueries = 79`, `batchTotalWordQueries 2 = 91`,
     per-round curve budgets `(24, 6)` telescoping to `30 = 32 - 2`, round-`0` max `24`).
   * `params257Fold8x2`: `stepLog = ![3, 1]` (`32 → 4 → 2`, `dim: 16 → 2 → 1`,
     `proofOracleQueries = 85`, `totalWordQueries = 91`, `batchTotalWordQueries 2 = 103`,
     per-round curve budgets `(28, 2)` telescoping to `30 = 32 - 2`, round-`0` max `28`).
2. **Smooth coset folding (`Folding.lean`) & honest prover (`Protocol.lean`):**
   Certifies `cosetEval_pow_two_pow`, `foldFiber`, `foldWord_apply_eq_foldFiber`,
   `foldFiber_two_eq_fold2Fiber`, `friCumLog_eq_sum_fin`, `friSmoothHonestWord_mem_rsCode`,
   `friSmoothFinalCodeword_mem_rsCode`, exact query lengths (`length_friSmoothIOP_queries`,
   `length_friSmoothInputQueries`), input locality (`friSmoothDecide_congr_inputQueries`), IOP /
   deterministic BCS / BCS ROM completeness, and verifier Merkle query cost
   (`isCostBounded_bcsMTCost_friSmoothVerifyROM`) for both schedules.
3. **Far-from-Reed–Solomon word (`X ^ 16`) & concrete rejection for 4-to-1 and 8+2 folding:**
   Proves `card_agree_farWord32_le_16` via `Cslib.Code.card_filter_eval_eq_eval_le` (`farWord32 ∉
   proximityLang 7`) and proves concrete verifier rejection `iopVerify (friSmoothIOP _) farWord32
   sampleChals32 ... = false` on BOTH `params257Fold4x4` and `params257Fold8x2`.
4. **Batched smooth FRI (`t = 2`, `BatchProtocol.lean`):**
   Certifies round-`0` non-opening, exact opening counts, input locality, affine and homogeneous
   linear completeness, BCS / ROM completeness, Merkle cost, far-tuple non-membership, and all
   shared code-parameterized language / ceiling / floor threshold bridges
   (`mem_friBatchProximityLang_zero_iff`, `friBatchCorrAgreeLang_eq_proximityLang`,
   `friBatchCeilThreshold_bounds`, `friBatchFloorThreshold_bounds`).
5. **Exact binary equivalence (`FRIParams.toSmooth`):**
   Verifies `friIOP params257 = friSmoothIOP params257.toSmooth`,
   `friBatchIOP params257 2 = friSmoothBatchIOP params257.toSmooth 2`, and exact malformed-list
   agreement `friDecide params257 ... = friSmoothDecide params257.toSmooth ...`.
-/

namespace CslibFrontierTests.Crypto.FRISmooth

open scoped BigOperators
open Polynomial
open Cslib Cslib.Code Cslib.OracleComp
open Cslib.Crypto.Protocols.BCS Cslib.Crypto.Protocols.FRI
open CslibFrontierTests.Crypto.FRI
open CslibFrontierTests.Crypto.MerkleTestHash

/-! ### Part 1: Concrete `ZMod 257` Smooth Fixtures (`32`-Point Coset, `![2, 2]` & `![3, 1]`) -/

/-- `15` is a primitive `32`-nd (`2 ^ 5`-th) root of unity in `ZMod 257` (`15 ^ 16 = -1`). -/
public theorem isPrimitiveRoot_fifteen_32 : IsPrimitiveRoot (15 : ZMod 257) (2 ^ 5) := by
  refine IsPrimitiveRoot.mk (by decide : (15 : ZMod 257) ^ 32 = 1) ?_
  intro l hl
  have h32 : (15 : ZMod 257) ^ 32 = 1 := by decide
  have hmod : (15 : ZMod 257) ^ (l % 32) = 1 := by
    have hsplit : (15 : ZMod 257) ^ (32 * (l / 32)) * (15 : ZMod 257) ^ (l % 32) = 1 := by
      rw [← pow_add, Nat.div_add_mod]
      exact hl
    rw [pow_mul, h32, one_pow, one_mul] at hsplit
    exact hsplit
  have hlt : l % 32 < 32 := Nat.mod_lt l (by omega)
  have hr_zero : ∀ r : Fin 32, (15 : ZMod 257) ^ r.val = 1 → r.val = 0 := by
    intro r hr
    fin_cases r <;> first | rfl | exact absurd hr (by decide)
  exact Nat.dvd_of_mod_eq_zero (hr_zero ⟨l % 32, hlt⟩ hmod)

/-- Shared builder for 2-round smooth FRI instances on the `32`-point coset `⟨15⟩ ⊆ (ZMod 257)ˣ`
(`d = 5`, `m = 2`, `totalLog = 4`, `kFinal = 1`, `q = 6`). -/
public abbrev mkParams257Smooth (stepLog : Fin 2 → ℕ) (hstepPos : ∀ i : Fin 2, 1 ≤ stepLog i)
    (htot : friCumLog stepLog 2 = 4) : FRISmoothParams (ZMod 257) where
  d := 5
  m := 2
  stepLog := stepLog
  kFinal := 1
  q := 6
  g := 1
  ω := 15
  hstepPos := hstepPos
  htotal := by omega
  hkPos := by omega
  hkLe := by rw [htot]; decide
  hg := one_ne_zero
  h2 := by decide
  hω := isPrimitiveRoot_fifteen_32

/-- Pure 4-to-1 smooth FRI parameters over `ZMod 257`: `|L_0| = 32 → 8 → 2`, `dim: 16 → 4 → 1`,
`stepLog = ![2, 2]`, `kFinal = 1`, `q = 6`. -/
@[expose] public def params257Fold4x4 : FRISmoothParams (ZMod 257) :=
  mkParams257Smooth ![2, 2] (fun i => by fin_cases i <;> decide) rfl

/-- Mixed 8-to-1 then 2-to-1 smooth FRI parameters over `ZMod 257`: `|L_0| = 32 → 4 → 2`,
`dim: 16 → 2 → 1`, `stepLog = ![3, 1]`, `kFinal = 1`, `q = 6`. -/
@[expose] public def params257Fold8x2 : FRISmoothParams (ZMod 257) :=
  mkParams257Smooth ![3, 1] (fun i => by fin_cases i <;> decide) rfl

-- Schedule, domain-size, dimension, query-count, telescoping, and round-0 maximality checks.
example : params257Fold4x4.totalLog = 4 := rfl
example : params257Fold4x4.domainSize 0 = 32 := rfl
example : params257Fold4x4.domainSize 1 = 8 := rfl
example : params257Fold4x4.domainSize 2 = 2 := rfl
example : params257Fold4x4.dim 0 = 16 := rfl
example : params257Fold4x4.dim 1 = 4 := rfl
example : params257Fold4x4.dim 2 = 1 := rfl
example : params257Fold4x4.aritySum = 8 := by decide
example : params257Fold4x4.proofOracleQueries = 73 := by decide
example : params257Fold4x4.totalWordQueries = 79 := by decide
example : params257Fold4x4.batchTotalWordQueries 2 = 91 := by decide
example : params257Fold4x4.firstStepLog = 2 := rfl
example :
    (∑ i : Fin params257Fold4x4.m,
      (params257Fold4x4.arity i - 1) * params257Fold4x4.domainSize (i.val + 1)) = 30 :=
  params257Fold4x4.sum_arity_sub_one_mul_domainSize
example (i : Fin params257Fold4x4.m) :
    (params257Fold4x4.arity i - 1) * params257Fold4x4.domainSize (i.val + 1) ≤ 24 :=
  params257Fold4x4.arity_sub_one_mul_domainSize_le_first i

example : params257Fold8x2.totalLog = 4 := rfl
example : params257Fold8x2.domainSize 0 = 32 := rfl
example : params257Fold8x2.domainSize 1 = 4 := rfl
example : params257Fold8x2.domainSize 2 = 2 := rfl
example : params257Fold8x2.dim 0 = 16 := rfl
example : params257Fold8x2.dim 1 = 2 := rfl
example : params257Fold8x2.dim 2 = 1 := rfl
example : params257Fold8x2.aritySum = 10 := by decide
example : params257Fold8x2.proofOracleQueries = 85 := by decide
example : params257Fold8x2.totalWordQueries = 91 := by decide
example : params257Fold8x2.batchTotalWordQueries 2 = 103 := by decide
example : params257Fold8x2.firstStepLog = 3 := rfl
example :
    (∑ i : Fin params257Fold8x2.m,
      (params257Fold8x2.arity i - 1) * params257Fold8x2.domainSize (i.val + 1)) = 30 :=
  params257Fold8x2.sum_arity_sub_one_mul_domainSize
example (i : Fin params257Fold8x2.m) :
    (params257Fold8x2.arity i - 1) * params257Fold8x2.domainSize (i.val + 1) ≤ 28 :=
  params257Fold8x2.arity_sub_one_mul_domainSize_le_first i
example : params257Fold4x4.totalWordQueries =
    params257Fold4x4.kFinal +
      params257Fold4x4.q * (params257Fold4x4.aritySum + params257Fold4x4.m + 3) :=
  params257Fold4x4.totalWordQueries_eq
example : params257Fold8x2.batchTotalWordQueries 2 =
    params257Fold8x2.kFinal +
      params257Fold8x2.q * (params257Fold8x2.aritySum + params257Fold8x2.m + 2 + 3) :=
  params257Fold8x2.batchTotalWordQueries_eq 2

-- Exercise `cosetEval_pow_two_pow`, `foldWord_apply_eq_foldFiber`, `foldFiber_two_eq_fold2Fiber`,
-- `friCumLog_eq_sum_fin`, and `friSmoothFinalCodeword_mem_rsCode`.
example (j : Fin 32) :
    (cosetEval (1 : ZMod 257) 15 5 0 j) ^ (2 ^ 2) =
      cosetEval (1 : ZMod 257) 15 5 2 ⟨j.val % 8, Nat.mod_lt _ (by omega)⟩ :=
  cosetEval_pow_two_pow (d := 5) (i := 0) (s := 2) isPrimitiveRoot_fifteen_32 (by omega) j

example (j : Fin 32) :
    (cosetEval (1 : ZMod 257) 15 5 0 j) ^ (2 ^ 3) =
      cosetEval (1 : ZMod 257) 15 5 3 ⟨j.val % 4, Nat.mod_lt _ (by omega)⟩ :=
  cosetEval_pow_two_pow (d := 5) (i := 0) (s := 3) isPrimitiveRoot_fifteen_32 (by omega) j

example : friCumLog params257Fold8x2.stepLog 2 = ∑ k : Fin 2, params257Fold8x2.stepLog k :=
  friCumLog_eq_sum_fin params257Fold8x2.stepLog

example (πFinal : OracleTable 5 (ZMod 257)) :
    friSmoothFinalCodeword params257Fold4x4 πFinal ∈ params257Fold4x4.rsCode 2 :=
  friSmoothFinalCodeword_mem_rsCode params257Fold4x4 πFinal

example (f : Fin (4 * 8) → ZMod 257) (z : ZMod 257) (j : Fin 8) :
    foldWord (1 : ZMod 257) 15 f z j =
      foldFiber (1 : ZMod 257) 15 (fun t => f (fiberIdx j t)) j z :=
  foldWord_apply_eq_foldFiber 1 15 f z j

example (ys : Fin 2 → ZMod 257) (j : Fin 4) (z : ZMod 257) :
    foldFiber (1 : ZMod 257) 4 ys j z =
      fold2Fiber (ys 0) (ys 1) (cosetPoint (1 : ZMod 257) 4 8 ⟨j.val, by omega⟩) z :=
  foldFiber_two_eq_fold2Fiber (by omega) isPrimitiveRoot_four_eight ys j z

/-! ### Part 2: Honest Codewords, Smooth IOP & BCS Completeness for `![2, 2]` and `![3, 1]` -/

/-- Concrete degree-`< 16` polynomial `3 + 5 X + 2 X^7 + 9 X^15 ∈ (ZMod 257)[X]`. -/
noncomputable def honestPoly32 : Polynomial (ZMod 257) :=
  C 3 + C 5 * X + C 2 * X ^ 7 + C 9 * X ^ 15

/-- Concrete degree-`< 16` codeword on the `32`-point coset `⟨15⟩ ⊆ (ZMod 257)ˣ`. -/
@[expose] public def honestWord32 : OracleTable 5 (ZMod 257) :=
  fun idx =>
    let x := cosetEval (1 : ZMod 257) 15 5 0 idx
    3 + 5 * x + 2 * x ^ 7 + 9 * x ^ 15

/-- Second degree-`< 16` codeword `7 + 4 X^3 + 6 X^11` on the `32`-point coset. -/
@[expose] public def termWord32_0 : OracleTable 5 (ZMod 257) :=
  fun idx =>
    let x := cosetEval (1 : ZMod 257) 15 5 0 idx
    7 + 4 * x ^ 3 + 6 * x ^ 11

/-- Third degree-`< 16` codeword `2 + 11 X^5 + 8 X^13` on the `32`-point coset. -/
@[expose] public def termWord32_1 : OracleTable 5 (ZMod 257) :=
  fun idx =>
    let x := cosetEval (1 : ZMod 257) 15 5 0 idx
    2 + 11 * x ^ 5 + 8 * x ^ 13

private theorem degree_C_mul_X_pow_lt16 (c : ZMod 257) {k : ℕ} (hk : k < 16) :
    (C c * X ^ k).degree < (16 : WithBot ℕ) := by
  refine lt_of_le_of_lt (degree_mul_le _ _) ?_
  refine lt_of_le_of_lt (add_le_add degree_C_le (degree_X_pow_le k)) ?_
  rw [zero_add]
  exact_mod_cast hk

public theorem honestWord32_mem_initialCode_4x4 : honestWord32 ∈ params257Fold4x4.initialCode := by
  have hdeg : honestPoly32.degree < (16 : WithBot ℕ) := by
    have h0 : (C (3 : ZMod 257)).degree < (16 : WithBot ℕ) :=
      lt_of_le_of_lt degree_C_le (by decide)
    have h1 : (C (5 : ZMod 257) * X).degree < (16 : WithBot ℕ) := by
      simpa only [pow_one] using degree_C_mul_X_pow_lt16 5 (k := 1) (by omega)
    have h2 := degree_C_mul_X_pow_lt16 2 (k := 7) (by omega)
    have h3 := degree_C_mul_X_pow_lt16 9 (k := 15) (by omega)
    exact lt_of_le_of_lt (degree_add_le _ _)
      (max_lt (lt_of_le_of_lt (degree_add_le _ _)
        (max_lt (lt_of_le_of_lt (degree_add_le _ _) (max_lt h0 h1)) h2)) h3)
  refine mem_reedSolomon.mpr ⟨honestPoly32, hdeg, ?_⟩
  ext idx
  simp only [honestWord32, honestPoly32, FRISmoothParams.eval, friCumLog_zero, params257Fold4x4,
    eval_add, eval_mul, eval_pow, eval_C, eval_X]

public theorem honestWord32_mem_initialCode_8x2 : honestWord32 ∈ params257Fold8x2.initialCode :=
  honestWord32_mem_initialCode_4x4

public theorem termWord32_0_mem_initialCode : termWord32_0 ∈ params257Fold4x4.initialCode := by
  let p : Polynomial (ZMod 257) := C 7 + C 4 * X ^ 3 + C 6 * X ^ 11
  have hdeg : p.degree < (16 : WithBot ℕ) := by
    have h0 : (C (7 : ZMod 257)).degree < (16 : WithBot ℕ) :=
      lt_of_le_of_lt degree_C_le (by decide)
    have h1 := degree_C_mul_X_pow_lt16 4 (k := 3) (by omega)
    have h2 := degree_C_mul_X_pow_lt16 6 (k := 11) (by omega)
    exact lt_of_le_of_lt (degree_add_le _ _)
      (max_lt (lt_of_le_of_lt (degree_add_le _ _) (max_lt h0 h1)) h2)
  refine mem_reedSolomon.mpr ⟨p, hdeg, ?_⟩
  ext idx
  simp only [termWord32_0, p, FRISmoothParams.eval, friCumLog_zero, params257Fold4x4, eval_add,
    eval_mul, eval_pow, eval_C, eval_X]

public theorem termWord32_1_mem_initialCode : termWord32_1 ∈ params257Fold4x4.initialCode := by
  let p : Polynomial (ZMod 257) := C 2 + C 11 * X ^ 5 + C 8 * X ^ 13
  have hdeg : p.degree < (16 : WithBot ℕ) := by
    have h0 : (C (2 : ZMod 257)).degree < (16 : WithBot ℕ) :=
      lt_of_le_of_lt degree_C_le (by decide)
    have h1 := degree_C_mul_X_pow_lt16 11 (k := 5) (by omega)
    have h2 := degree_C_mul_X_pow_lt16 8 (k := 13) (by omega)
    exact lt_of_le_of_lt (degree_add_le _ _)
      (max_lt (lt_of_le_of_lt (degree_add_le _ _) (max_lt h0 h1)) h2)
  refine mem_reedSolomon.mpr ⟨p, hdeg, ?_⟩
  ext idx
  simp only [termWord32_1, p, FRISmoothParams.eval, friCumLog_zero, params257Fold4x4, eval_add,
    eval_mul, eval_pow, eval_C, eval_X]

/-- Concrete 3-round challenge vector on the `32`-point coset (`q = 6`, querying indices
`1, 2, 3, 4, 5, 6` and leaving index `0` unscheduled). -/
@[expose] public def sampleChals32 : Fin 3 → FRIChal (ZMod 257) 5 6
  | ⟨0, _⟩ => ⟨11, fun a => ⟨a.val + 1, by omega⟩⟩
  | ⟨1, _⟩ => ⟨19, fun a => ⟨a.val + 1, by omega⟩⟩
  | ⟨2, _⟩ => ⟨23, fun a => ⟨a.val + 1, by omega⟩⟩

-- Honest smooth folding preserves Reed–Solomon membership at every round for both schedules.
example :
    friSmoothHonestWord params257Fold4x4 honestWord32 1 (by decide) (fun _ => 11) ∈
      params257Fold4x4.rsCode 1 :=
  friSmoothHonestWord_mem_rsCode params257Fold4x4 honestWord32_mem_initialCode_4x4 1 (by decide) _

example :
    friSmoothHonestWord params257Fold8x2 honestWord32 1 (by decide) (fun _ => 11) ∈
      params257Fold8x2.rsCode 1 :=
  friSmoothHonestWord_mem_rsCode params257Fold8x2 honestWord32_mem_initialCode_8x2 1 (by decide) _

-- Exact query-list length and input-query locality for both schedules.
example : ((friSmoothIOP params257Fold4x4).queries honestWord32 sampleChals32).length = 73 :=
  (length_friSmoothIOP_queries params257Fold4x4 honestWord32 sampleChals32).trans (by decide)

example : ((friSmoothIOP params257Fold8x2).queries honestWord32 sampleChals32).length = 85 :=
  (length_friSmoothIOP_queries params257Fold8x2 honestWord32 sampleChals32).trans (by decide)

example : (friSmoothInputQueries params257Fold4x4 sampleChals32).length = 6 :=
  length_friSmoothInputQueries params257Fold4x4 sampleChals32

example (answers : List (ZMod 257)) :
    friSmoothDecide params257Fold4x4
        (fun s => if s = ⟨0, by decide⟩ then honestWord32 s + 1 else honestWord32 s)
        sampleChals32 answers =
      friSmoothDecide params257Fold4x4 honestWord32 sampleChals32 answers := by
  refine friSmoothDecide_congr_inputQueries params257Fold4x4 sampleChals32 (fun s hs => ?_) answers
  have hs_ne : s ≠ ⟨0, by decide⟩ := by
    intro h0
    subst h0
    exact absurd hs (by decide)
  simp only [hs_ne, ↓reduceIte]

-- Honest IOP completeness for both 4-to-1 and 8+2 folding.
example :
    iopVerify (friSmoothIOP params257Fold4x4) honestWord32 sampleChals32
      (iopProverOracles (friSmoothIOP params257Fold4x4) honestWord32 () sampleChals32) = true :=
  friSmoothIOP_complete params257Fold4x4 honestWord32 () honestWord32_mem_initialCode_4x4
    sampleChals32

example :
    iopVerify (friSmoothIOP params257Fold8x2) honestWord32 sampleChals32
      (iopProverOracles (friSmoothIOP params257Fold8x2) honestWord32 () sampleChals32) = true :=
  friSmoothIOP_complete params257Fold8x2 honestWord32 () honestWord32_mem_initialCode_8x2
    sampleChals32

private def constSmoothFS (_ : OracleTable 5 (ZMod 257)) (rts : List (List Bool)) :
    FRIChal (ZMod 257) 5 6 :=
  sampleChals32 ⟨rts.length % 3, Nat.mod_lt _ (by omega)⟩

-- Deterministic BCS and two-channel BCS ROM completeness + Merkle cost for both schedules.
example :
    bcsVerify (friSmoothIOP params257Fold4x4) (fun _ => idHash) [] (encZMod (p := 257))
      constSmoothFS honestWord32
      (bcsProve (friSmoothIOP params257Fold4x4) (fun _ => idHash) [] (encZMod (p := 257))
        constSmoothFS honestWord32 ()) = true :=
  friSmoothBCS_verify_prove_eq_true params257Fold4x4 (fun _ => idHash) [] length_polyHash
    (encZMod (p := 257)) constSmoothFS honestWord32_mem_initialCode_4x4

example (σ : ℕ) :
    bcsHonestROMGame (friSmoothIOP params257Fold8x2) (encZMod (p := 257)) honestWord32 () σ =
      PMF.pure true :=
  friSmoothBCS_honestROMGame_eq_pure_true params257Fold8x2 (encZMod (p := 257))
    honestWord32_mem_initialCode_8x2 σ

example (prf : BCSProof 3 (ZMod 257)) (hops : ∀ op ∈ prf.openings, op.path.length ≤ 5) :
    IsCostBounded bcsMTCost
      (bcsVerifyROM (friSmoothIOP params257Fold4x4) (encZMod (p := 257)) honestWord32 prf)
      (params257Fold4x4.proofOracleQueries * 6) :=
  isCostBounded_bcsMTCost_friSmoothVerifyROM params257Fold4x4 (encZMod (p := 257)) honestWord32 prf
    hops

/-! ### Part 3: Far-from-Reed–Solomon Word (`X ^ 16`) & Rejection on `![2, 2]` and `![3, 1]` -/

/-- Non-codeword evaluating `X ^ 16` on the `32`-point coset `⟨15⟩` (alternating `1, -1, …`). -/
@[expose] public def farWord32 : OracleTable 5 (ZMod 257) :=
  fun idx => (cosetEval (1 : ZMod 257) 15 5 0 idx) ^ 16

private theorem farWord32_eq_neg_one_pow (idx : Fin 32) :
    farWord32 idx = (-1 : ZMod 257) ^ idx.val := by
  have h16 : (15 : ZMod 257) ^ 16 = -1 := by decide
  simp only [farWord32, cosetEval, cosetPoint, pow_zero, pow_one, one_mul]
  rw [← pow_mul, mul_comm, pow_mul, h16]

/-- `farWord32` agrees with any degree-`< 16` codeword on at most `16` points of the `32`-point
coset (reusing `Cslib.Code.card_filter_eval_eq_eval_le`). -/
public theorem card_agree_farWord32_le_16 {c : OracleTable 5 (ZMod 257)}
    (hc_rs : c ∈ params257Fold4x4.initialCode) {D' : Finset (Fin 32)}
    (hagree : ∀ s ∈ D', farWord32 s = c s) :
    D'.card ≤ 16 := by
  classical
  obtain ⟨p, hp_deg, hpeq⟩ := mem_reedSolomon.mp hc_rs
  have hP_natDeg : (X ^ 16 : Polynomial (ZMod 257)).natDegree ≤ 16 := (natDegree_X_pow 16).le
  have hQ_natDeg : p.natDegree ≤ 16 := by
    by_cases hp0 : p = 0
    · simp [hp0]
    · exact le_of_lt ((natDegree_lt_iff_degree_lt hp0).mpr hp_deg)
  have hne : (X ^ 16 : Polynomial (ZMod 257)) ≠ p := by
    intro heq
    rw [← heq, degree_X_pow] at hp_deg
    exact absurd hp_deg (by decide)
  have hα_inj : Function.Injective (params257Fold4x4.eval 0) :=
    cosetEval_injective params257Fold4x4.hg params257Fold4x4.hω
      (params257Fold4x4.cumLog_le_d (by omega))
  have hsub : D' ⊆ Finset.univ.filter (fun s : Fin 32 =>
      (X ^ 16 : Polynomial (ZMod 257)).eval (params257Fold4x4.eval 0 s) =
        p.eval (params257Fold4x4.eval 0 s)) := by
    intro s hs
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ s, ?_⟩
    rw [eval_pow, eval_X, congrFun hpeq s]
    exact hagree s hs
  exact (Finset.card_le_card hsub).trans
    (card_filter_eval_eq_eval_le hα_inj hP_natDeg hQ_natDeg hne)

/-- `farWord32` has Hamming distance at least `16 > 7` from every degree-`< 16` codeword. -/
public theorem farWord32_not_mem_proximityLang_4x4 :
    farWord32 ∉ params257Fold4x4.proximityLang 7 := by
  rintro ⟨c, hc_rs, hdist⟩
  let c' : OracleTable 5 (ZMod 257) := c
  have hS_le : (Finset.univ.filter fun s : Fin (2 ^ 5) => farWord32 s = c' s).card ≤ 16 :=
    card_agree_farWord32_le_16 hc_rs fun s hs => (Finset.mem_filter.mp hs).2
  have htot := card_filter_eq_add_hammingDist farWord32 c'
  rw [Fintype.card_fin] at htot
  have hdist' : hammingDist farWord32 c' ≤ 7 := hdist
  omega

public theorem farWord32_not_mem_proximityLang_8x2 :
    farWord32 ∉ params257Fold8x2.proximityLang 7 :=
  farWord32_not_mem_proximityLang_4x4

private theorem foldFiber_const {g ω : ZMod 257} {a N : ℕ} (hg : g ≠ 0)
    (ha : (a : ZMod 257) ≠ 0) (hN : 0 < N) (hω : IsPrimitiveRoot ω (a * N))
    (y : ZMod 257) (j : Fin N) (z : ZMod 257) :
    foldFiber g ω (fun _ : Fin a => y) j z = y := by
  have ha_pos : 0 < a := by
    by_contra h
    have ha0 : a = 0 := by omega
    subst ha0
    exact ha (by simp)
  have heval := foldWord_eval hg ha hN hω (C y) z j
  simp only [eval_C] at heval
  rw [foldWord_apply_eq_foldFiber] at heval
  rw [heval, eval_foldPoly]
  have hcomp : ∀ r : Fin a, (polyComp a (C y) r).eval (cosetPoint (g ^ a) (ω ^ a) N j) =
      if r = ⟨0, ha_pos⟩ then y else 0 := by
    intro r
    have hpoly : polyComp a (C y) r = if r = ⟨0, ha_pos⟩ then C y else 0 := by
      ext n
      rw [coeff_polyComp ha_pos]
      split_ifs with hr
      · subst hr
        by_cases hn : n = 0
        · subst hn; simp
        · have hne : a * n + 0 ≠ 0 := by
            have : 0 < a * n := Nat.mul_pos ha_pos (Nat.pos_of_ne_zero hn)
            omega
          simp only [coeff_C, hne, hn, ↓reduceIte]
      · have hr0 : r.val ≠ 0 := fun h0 => hr (Fin.ext h0)
        have hne : a * n + r.val ≠ 0 := by omega
        simp only [coeff_C, hne, ↓reduceIte, coeff_zero]
    rw [hpoly]
    split_ifs <;> simp
  simp only [hcomp, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    pow_zero, one_mul]

private theorem farWord32_smooth_reject (stepLog : Fin 2 → ℕ)
    (hstepPos : ∀ i : Fin 2, 1 ≤ stepLog i) (htot : friCumLog stepLog 2 = 4)
    (heven1 : Even (2 ^ (5 - friCumLog stepLog 1)))
    (chals : Fin 3 → FRIChal (ZMod 257) 5 6)
    (hodd : ∃ a : Fin 6, ((chals (Fin.last 2)).queryIdxs a).val % 2 = 1) :
    let params := mkParams257Smooth stepLog hstepPos htot
    iopVerify (friSmoothIOP params) farWord32 chals
      (iopProverOracles (friSmoothIOP params) farWord32 () chals) = false := by
  intro params
  obtain ⟨a, ha_odd⟩ := hodd
  by_contra hne
  have htrue := Bool.eq_true_of_not_eq_false hne
  have hfin := ((iopVerify_friSmoothIOP_eq_true_iff params farWord32 chals _).mp htrue a).2.2
  let zs : Fin 2 → ZMod 257 :=
    fun k => (prefixChallenges chals (Fin.last 2) k).foldScalar
  have h1le : 1 ≤ params.m := by change 1 ≤ 2; omega
  have h0m : 0 < params.m := by change 0 < 2; omega
  have h1m : 1 < params.m := by change 1 < 2; omega
  have hw1 : ∀ (zs1 : Fin 1 → ZMod 257) (j : Fin (2 ^ (5 - params.cumLog 1))),
      friSmoothHonestWord params farWord32 1 h1le zs1 j = (-1 : ZMod 257) ^ j.val := by
    intro zs1 j
    rw [friSmoothHonestWord_succ_apply]
    have hsplit : 2 ^ (5 - params.cumLog 0) =
        params.arity ⟨0, h0m⟩ * 2 ^ (5 - params.cumLog 1) :=
      params.domainSize_eq_arity_mul_succ ⟨0, h0m⟩
    have hω0 : IsPrimitiveRoot ((15 : ZMod 257) ^ (2 ^ params.cumLog 0))
        (params.arity ⟨0, h0m⟩ * 2 ^ (5 - params.cumLog 1)) := by
      simpa only [← hsplit] using
        isPrimitiveRoot_pow_two_pow params.hω (params.cumLog_le_d (by omega))
    have hfib :
        (fun t : Fin (params.arity ⟨0, h0m⟩) =>
          friSmoothHonestWord params farWord32 0 (by omega) (fun k => zs1 k.castSucc)
            ⟨j.val + t.val * 2 ^ (5 - params.cumLog 1),
              lt_of_lt_of_eq (fiberIdx j t).isLt hsplit.symm⟩) =
        fun _ => (-1 : ZMod 257) ^ j.val := by
      funext t
      change farWord32 ⟨j.val + t.val * 2 ^ (5 - params.cumLog 1), _⟩ = (-1 : ZMod 257) ^ j.val
      rw [farWord32_eq_neg_one_pow]
      rcases heven1 with ⟨k, hk2⟩
      have h2t : t.val * 2 ^ (5 - params.cumLog 1) = 2 * (t.val * k) := by
        change t.val * 2 ^ (5 - friCumLog stepLog 1) = _
        rw [hk2]
        ring
      change (-1 : ZMod 257) ^ (j.val + t.val * 2 ^ (5 - params.cumLog 1)) = _
      rw [pow_add, h2t, pow_mul]
      norm_num
    rw [hfib, foldFiber_const (pow_ne_zero _ one_ne_zero)
      (params.arity_cast_ne_zero ⟨0, h0m⟩) (Nat.pow_pos (by omega)) hω0]
  have hw2 : ∀ j : Fin (2 ^ (5 - params.cumLog 2)),
      friSmoothHonestWord params farWord32 2 le_rfl zs j = (-1 : ZMod 257) ^ j.val := by
    intro j
    rw [friSmoothHonestWord_succ_apply]
    have hsplit : 2 ^ (5 - params.cumLog 1) =
        params.arity ⟨1, h1m⟩ * 2 ^ (5 - params.cumLog 2) :=
      params.domainSize_eq_arity_mul_succ ⟨1, h1m⟩
    have hω1 : IsPrimitiveRoot ((15 : ZMod 257) ^ (2 ^ params.cumLog 1))
        (params.arity ⟨1, h1m⟩ * 2 ^ (5 - params.cumLog 2)) := by
      simpa only [← hsplit] using
        isPrimitiveRoot_pow_two_pow params.hω (params.cumLog_le_d (by omega))
    have hdom2 : 2 ^ (5 - params.cumLog 2) = 2 := by
      change 2 ^ (5 - friCumLog stepLog 2) = 2
      rw [htot]
      rfl
    have hfib :
        (fun t : Fin (params.arity ⟨1, h1m⟩) =>
          friSmoothHonestWord params farWord32 1 h1le (fun k => zs k.castSucc)
            ⟨j.val + t.val * 2 ^ (5 - params.cumLog 2),
              lt_of_lt_of_eq (fiberIdx j t).isLt hsplit.symm⟩) =
        fun _ => (-1 : ZMod 257) ^ j.val := by
      funext t
      rw [hw1]
      have h2t : t.val * 2 ^ (5 - params.cumLog 2) = 2 * t.val := by
        rw [hdom2]
        ring
      change (-1 : ZMod 257) ^ (j.val + t.val * 2 ^ (5 - params.cumLog 2)) = _
      rw [pow_add, h2t, pow_mul]
      norm_num
    rw [hfib, foldFiber_const (pow_ne_zero _ one_ne_zero)
      (params.arity_cast_ne_zero ⟨1, h1m⟩) (Nat.pow_pos (by omega)) hω1]
  set s := (chals (Fin.last 2)).queryIdxs a
  have hdom2 : 2 ^ (5 - params.totalLog) = 2 := by
    change 2 ^ (5 - friCumLog stepLog 2) = 2
    rw [htot]
    rfl
  have hsmod : s.val % 2 ^ (5 - params.totalLog) = 1 := by rw [hdom2]; exact ha_odd
  have hfin_lt : (friSmoothFinalIdx params s).val < 2 ^ (5 - params.totalLog) :=
    (friSmoothFinalFin params s).isLt
  have hlhs :
      iopProverOracles (friSmoothIOP params) farWord32 () chals (Fin.last 2)
        (friSmoothFinalIdx params s) = -1 := by
    simp only [iopProverOracles, friSmoothIOP, Fin.val_last, padOracle_apply_of_lt _ _ hfin_lt]
    rw [hw2]
    change (-1 : ZMod 257) ^ (s.val % 2 ^ (5 - params.totalLog)) = -1
    rw [hsmod, pow_one]
  have hrhs :
      friSmoothFinalCodeword params
        (iopProverOracles (friSmoothIOP params) farWord32 () chals (Fin.last 2))
        (friSmoothFinalFin params s) = 1 := by
    simp only [friSmoothFinalCodeword, evalLagrange, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_singleton, Finset.erase_singleton, Finset.prod_empty, mul_one]
    have h0lt : (⟨0, by decide⟩ : Fin (2 ^ 5)).val < 2 ^ (5 - params.totalLog) :=
      Nat.pow_pos (by omega)
    change padOracle (friSmoothHonestWord params farWord32 2 le_rfl zs)
      (⟨0, by decide⟩ : Fin (2 ^ 5)) = 1
    rw [padOracle_apply_of_lt _ (⟨0, by decide⟩ : Fin (2 ^ 5)) h0lt, hw2]
    rfl
  rw [hlhs, hrhs] at hfin
  exact absurd hfin (by decide)

/-- Concrete smooth FRI rejection of `farWord32` under pure 4-to-1 folding (`![2, 2]`). -/
public theorem farWord32_iopVerify_eq_false_4x4 :
    iopVerify (friSmoothIOP params257Fold4x4) farWord32 sampleChals32
      (iopProverOracles (friSmoothIOP params257Fold4x4) farWord32 () sampleChals32) = false :=
  farWord32_smooth_reject ![2, 2] (fun i => by fin_cases i <;> decide) rfl ⟨4, rfl⟩
    sampleChals32 ⟨⟨0, by decide⟩, rfl⟩

/-- Concrete smooth FRI rejection of `farWord32` under mixed 8-to-1 + 2-to-1 folding (`![3, 1]`).
-/
public theorem farWord32_iopVerify_eq_false_8x2 :
    iopVerify (friSmoothIOP params257Fold8x2) farWord32 sampleChals32
      (iopProverOracles (friSmoothIOP params257Fold8x2) farWord32 () sampleChals32) = false :=
  farWord32_smooth_reject ![3, 1] (fun i => by fin_cases i <;> decide) rfl ⟨2, rfl⟩
    sampleChals32 ⟨⟨0, by decide⟩, rfl⟩

/-! ### Part 4: Batched Smooth FRI (`t = 2`) & Threshold Bridges -/

/-- Honest `3`-word affine batch statement on the `32`-point coset. -/
@[expose] public def honestBatchStmt32 : FRIBatchStmt (ZMod 257) 5 2 where
  base := honestWord32
  terms := ![termWord32_0, termWord32_1]

/-- Honest homogeneous linear batch statement (`f₀⁽⁰⁾ = 0`) on the `32`-point coset. -/
def honestLinearStmt32 : FRIBatchStmt (ZMod 257) 5 2 :=
  FRIBatchStmt.linear ![termWord32_0, termWord32_1]

/-- Far `3`-word affine batch statement replacing the second generator word by `farWord32`. -/
@[expose] public def badBatchStmt32 : FRIBatchStmt (ZMod 257) 5 2 where
  base := honestWord32
  terms := ![termWord32_0, farWord32]

public theorem honestBatchStmt32_completeRel_4x4 :
    params257Fold4x4.batchCompletenessRel 2 honestBatchStmt32 () := by
  refine ⟨honestWord32_mem_initialCode_4x4, fun j => ?_⟩
  fin_cases j
  · exact termWord32_0_mem_initialCode
  · exact termWord32_1_mem_initialCode

public theorem honestBatchStmt32_completeRel_8x2 :
    params257Fold8x2.batchCompletenessRel 2 honestBatchStmt32 () :=
  honestBatchStmt32_completeRel_4x4

private theorem honestLinearStmt32_completeRel_4x4 :
    params257Fold4x4.batchCompletenessRel 2 honestLinearStmt32 () := by
  refine ⟨params257Fold4x4.initialCode.zero_mem, fun j => ?_⟩
  fin_cases j
  · exact termWord32_0_mem_initialCode
  · exact termWord32_1_mem_initialCode

public theorem badBatchStmt32_not_mem_batchProximityLang_4x4 :
    badBatchStmt32 ∉ params257Fold4x4.batchProximityLang 2 7 := by
  rintro ⟨D', hcard, _, _, v, hv, hagree⟩
  have hle : D'.card ≤ 16 :=
    card_agree_farWord32_le_16 (hv 1) fun s hs => by
      simpa only [badBatchStmt32, Matrix.cons_val_one, Matrix.cons_val_fin_one] using
        (hagree s hs).2 1
  have hcard' : 32 - 7 ≤ D'.card := hcard
  omega

public theorem badBatchStmt32_not_mem_batchProximityLang_8x2 :
    badBatchStmt32 ∉ params257Fold8x2.batchProximityLang 2 7 :=
  badBatchStmt32_not_mem_batchProximityLang_4x4

/-- Concrete 4-round batched challenge vector on the `32`-point coset. -/
def sampleBatchChals32 : Fin 4 → FRIBatchChal (ZMod 257) 5 6 2 :=
  Fin.cases
    ⟨![7, 13], 0, (sampleChals32 0).queryIdxs⟩
    (fun j => ⟨![0, 0], (sampleChals32 j).foldScalar, (sampleChals32 j).queryIdxs⟩)

-- Exact committed-opening count, round-0 non-opening, input-query locality, and completeness.
example :
    ((friSmoothBatchIOP params257Fold4x4 2).queries honestBatchStmt32 sampleBatchChals32).length =
      73 :=
  (length_friSmoothBatchIOP_queries params257Fold4x4 2 honestBatchStmt32 sampleBatchChals32).trans
    (by decide)

example :
    ((friSmoothBatchIOP params257Fold8x2 2).queries honestBatchStmt32 sampleBatchChals32).length =
      85 :=
  (length_friSmoothBatchIOP_queries params257Fold8x2 2 honestBatchStmt32 sampleBatchChals32).trans
    (by decide)

example : (friSmoothBatchInputQueries params257Fold4x4 2 sampleBatchChals32).length = 6 :=
  length_friSmoothBatchInputQueries params257Fold4x4 2 sampleBatchChals32

example :
    ((friSmoothBatchIOP params257Fold4x4 2).queries honestBatchStmt32 sampleBatchChals32).all
      (fun p => p.1 != 0) = true := by
  rw [List.all_eq_true]
  intro p hp
  exact bne_iff_ne.mpr
    (round_ne_zero_of_mem_friSmoothBatchQueries params257Fold4x4 2 sampleBatchChals32 hp)

example (answers : List (ZMod 257)) :
    friSmoothBatchDecide params257Fold4x4 2
        ⟨fun s => if s = ⟨0, by decide⟩ then honestWord32 s + 1 else honestWord32 s,
          ![termWord32_0, termWord32_1]⟩
        sampleBatchChals32 answers =
      friSmoothBatchDecide params257Fold4x4 2 honestBatchStmt32 sampleBatchChals32 answers := by
  refine friSmoothBatchDecide_congr_inputQueries params257Fold4x4 2 sampleBatchChals32
    (fun s hs => ?_) answers
  have hs_ne : s ≠ ⟨0, by decide⟩ := by
    intro h0
    subst h0
    exact absurd hs (by decide)
  exact ⟨by simp only [honestBatchStmt32, hs_ne, ↓reduceIte], fun _ => rfl⟩

example :
    iopVerify (friSmoothBatchIOP params257Fold4x4 2) honestBatchStmt32 sampleBatchChals32
      (iopProverOracles (friSmoothBatchIOP params257Fold4x4 2) honestBatchStmt32 ()
        sampleBatchChals32) = true :=
  friSmoothBatchIOP_complete params257Fold4x4 2 honestBatchStmt32 ()
    honestBatchStmt32_completeRel_4x4 sampleBatchChals32

example :
    iopVerify (friSmoothBatchIOP params257Fold4x4 2) honestLinearStmt32 sampleBatchChals32
      (iopProverOracles (friSmoothBatchIOP params257Fold4x4 2) honestLinearStmt32 ()
        sampleBatchChals32) = true :=
  friSmoothBatchIOP_complete params257Fold4x4 2 honestLinearStmt32 ()
    honestLinearStmt32_completeRel_4x4 sampleBatchChals32

example :
    iopVerify (friSmoothBatchIOP params257Fold8x2 2) honestBatchStmt32 sampleBatchChals32
      (iopProverOracles (friSmoothBatchIOP params257Fold8x2 2) honestBatchStmt32 ()
        sampleBatchChals32) = true :=
  friSmoothBatchIOP_complete params257Fold8x2 2 honestBatchStmt32 ()
    honestBatchStmt32_completeRel_8x2 sampleBatchChals32

example (a : Fin 6) :
    friSmoothBatchSingleAccepts params257Fold8x2 2 honestBatchStmt32 sampleBatchChals32
      (iopProverOracles (friSmoothBatchIOP params257Fold8x2 2) honestBatchStmt32 ()
        sampleBatchChals32)
      ((sampleBatchChals32 (Fin.last 3)).queryIdxs a) :=
  (iopVerify_friSmoothBatchIOP_eq_true_iff params257Fold8x2 2 honestBatchStmt32
    sampleBatchChals32 _).mp
    (friSmoothBatchIOP_complete params257Fold8x2 2 honestBatchStmt32 ()
      honestBatchStmt32_completeRel_8x2 sampleBatchChals32) a

private def constSmoothBatchFS (_ : FRIBatchStmt (ZMod 257) 5 2) (rts : List (List Bool)) :
    FRIBatchChal (ZMod 257) 5 6 2 :=
  sampleBatchChals32 ⟨rts.length % 4, Nat.mod_lt _ (by omega)⟩

example :
    bcsVerify (friSmoothBatchIOP params257Fold4x4 2) (fun _ => idHash) [] (encZMod (p := 257))
      constSmoothBatchFS honestBatchStmt32
      (bcsProve (friSmoothBatchIOP params257Fold4x4 2) (fun _ => idHash) [] (encZMod (p := 257))
        constSmoothBatchFS honestBatchStmt32 ()) = true :=
  friSmoothBatchBCS_verify_prove_eq_true params257Fold4x4 2 (fun _ => idHash) [] length_polyHash
    (encZMod (p := 257)) constSmoothBatchFS honestBatchStmt32_completeRel_4x4

example (σ : ℕ) :
    bcsHonestROMGame (friSmoothBatchIOP params257Fold8x2 2) (encZMod (p := 257))
      honestBatchStmt32 () σ = PMF.pure true :=
  friSmoothBatchBCS_honestROMGame_eq_pure_true params257Fold8x2 2 (encZMod (p := 257))
    honestBatchStmt32_completeRel_8x2 σ

example (prf : BCSProof 4 (ZMod 257)) (hops : ∀ op ∈ prf.openings, op.path.length ≤ 5) :
    IsCostBounded bcsMTCost
      (bcsVerifyROM (friSmoothBatchIOP params257Fold8x2 2) (encZMod (p := 257))
        honestBatchStmt32 prf)
      (params257Fold8x2.proofOracleQueries * 6) :=
  isCostBounded_bcsMTCost_friSmoothBatchVerifyROM params257Fold8x2 2 (encZMod (p := 257))
    honestBatchStmt32 prf hops

-- Shared code-parameterized language & threshold bridges exercised on smooth batched FRI.
example : honestBatchStmt32 ∈ params257Fold4x4.batchProximityLang 2 7 :=
  mem_friBatchProximityLang_of_completenessRel 7 honestBatchStmt32_completeRel_4x4

example : 7 < 2 ^ params257Fold4x4.d :=
  lt_two_pow_of_not_mem_friBatchProximityLang badBatchStmt32_not_mem_batchProximityLang_4x4

example (stmt0 : FRIBatchStmt (ZMod 257) 5 0) :
    stmt0 ∈ params257Fold4x4.batchProximityLang 0 7 ↔
      stmt0.base ∈ params257Fold4x4.proximityLang 7 :=
  mem_friBatchProximityLang_zero_iff params257Fold4x4.initialCode 7 stmt0

example :
    params257Fold4x4.batchCorrAgreeLang 2 (3 / 4 : ℝ) =
      params257Fold4x4.batchProximityLang 2 (2 ^ 5 - ⌈(3 / 4 : ℝ) * (2 ^ 5 : ℝ)⌉₊) :=
  friBatchCorrAgreeLang_eq_proximityLang params257Fold4x4.initialCode 2 (by norm_num)

example :
    let e := 2 ^ 5 - ⌈(3 / 4 : ℝ) * (2 ^ 5 : ℝ)⌉₊
    e < 2 ^ 5 ∧ (((2 ^ 5 - e - 1 : ℕ) : ℝ) / (2 ^ 5 : ℝ)) < (3 / 4 : ℝ) ∧
      (e : ℝ) / (2 ^ 5 : ℝ) ≤ 1 - (3 / 4 : ℝ) :=
  friBatchCeilThreshold_bounds 5 (by norm_num) (by norm_num)

example :
    let B := ⌊(3 / 4 : ℝ) * (2 ^ 5 : ℝ)⌋₊
    let e := 2 ^ 5 - 1 - B
    ((∀ (D' : Finset (Fin 32)) (v₀ : OracleTable 5 (ZMod 257)),
        v₀ ∈ params257Fold4x4.initialCode →
        ∀ v : Fin 2 → OracleTable 5 (ZMod 257),
          (∀ j, v j ∈ params257Fold4x4.initialCode) →
          (∀ s ∈ D', badBatchStmt32.base s = v₀ s ∧ ∀ j, badBatchStmt32.terms j s = v j s) →
          (D'.card : ℝ) / (2 ^ 5 : ℝ) ≤ (3 / 4 : ℝ)) ↔
      badBatchStmt32 ∉ params257Fold4x4.batchProximityLang 2 e) ∧
      B < 2 ^ 5 ∧ 2 ^ 5 - e - 1 = B ∧
      (B : ℝ) / (2 ^ 5 : ℝ) ≤ (3 / 4 : ℝ) ∧ (e : ℝ) / (2 ^ 5 : ℝ) < 1 - (3 / 4 : ℝ) :=
  friBatchFloorThreshold_bounds params257Fold4x4.initialCode 2 badBatchStmt32
    (by norm_num) (by norm_num)

/-! ### Part 5: Exact Binary Specialization Equivalence (`FRIParams.toSmooth`) -/

example : friIOP params257 = friSmoothIOP params257.toSmooth :=
  friIOP_eq_friSmoothIOP params257

example : friBatchIOP params257 2 = friSmoothBatchIOP params257.toSmooth 2 :=
  friBatchIOP_eq_friSmoothBatchIOP params257 2

-- Exact agreement on malformed short answer lists (`[]`, `[0]`, `[0, 1]`).
example (answers : List (ZMod 257)) :
    friDecide params257 honestWord sampleChals answers =
      friSmoothDecide params257.toSmooth honestWord sampleChals answers :=
  rfl

example :
    friDecide params257 honestWord sampleChals [0, 1] =
      friSmoothDecide params257.toSmooth honestWord sampleChals [0, 1] :=
  rfl

end CslibFrontierTests.Crypto.FRISmooth
