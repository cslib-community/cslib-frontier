/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module

import CslibFrontier.Crypto.Protocols.FRI.BatchProtocol
import CslibFrontier.Crypto.Protocols.FRI.Soundness
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

/-!
# Concrete Nonvacuous Tests for Batched Multi-Round FRI (`BatchProtocol.lean`)

Exercises every public definition and theorem of
`CslibFrontier.Crypto.Protocols.FRI.BatchProtocol` from an ordinary `module` client (no
`import all`) over `ZMod 257` (`d = 3`, initial coset size `8`, `m = 2` folding rounds / `4` total
IOP rounds, `kFinal = 1`, rate `1 / 2`, `q = 6` batched queries, batch size `t = 2` representing
`3` affine input words):

1. **Structures, query accounting & locality.** Checks `FRIBatchStmt` (`eval`, `linear`,
   `equivProd`), `FRIBatchChal` (`toFRIChal`, `equivProd`, `card_friBatchChal`), exact query counts
   (`proofOracleQueries = 49`, `batchInputWordReads 2 = 18`, `batchTotalWordQueries 2 = 67`),
   round-`0` non-opening (`round_ne_zero_of_mem_friBatchQueries`), and input-query locality
   (`friBatchDecide_congr_inputQueries`) on two distinct statements agreeing on queried indices.
2. **Multi-round batched `PublicCoinIOP` completeness & BCS / ROM composition.** Certifies honest
   completeness (`friBatchIOP_complete`) on both an affine `3`-word statement `honestBatchStmt` and
   a homogeneous linear `2`-word statement `honestLinearStmt` (`f₀⁽⁰⁾ = 0`), pointwise
   `friBatchSingleAccepts` (`iopVerify_friBatchIOP_eq_true_iff`), deterministic BCS verification
   (`friBatchBCS_verify_prove_eq_true`), two-channel BCS ROM completeness
   (`friBatchBCS_honestROMGame_eq_pure_true`), and verifier Merkle query cost bounds
   (`isCostBounded_bcsMTCost_friBatchVerifyROM`).
3. **Nonvacuous false tuples & cheating-prover rejection.** Constructs `badBatchStmt` whose second
   generator word `farWord` (`X ^ 4` on the `8`-point coset) has distance `≥ 4` from
   `params257.initialCode`, proves `badBatchStmt ∉ params257.batchProximityLang 2 2` and
   `badBatchStmt ∉ params257.batchCorrAgreeLang 2 (3 / 4 : ℝ)`, and verifies rejection both when
   folding the bad combination honestly and when a malicious prover substitutes valid folded
   codewords violating the round-`1` batching check (`oracles 1 s = f₀(s) + ∑ x_j f_j(s)`).
4. **Language & real-`α` threshold bridges.** Exercises `mem_batchProximityLang_zero_iff` (`t = 0`),
   `batchCorrAgreeLang_eq_batchProximityLang`, `batchCeilThreshold_bounds`, and
   `batchFloorThreshold_bounds` (including the exact integer boundary `α * 8 = 5`).
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.FRIBatch

open scoped BigOperators
open Polynomial
open Cslib Cslib.Code Cslib.OracleComp
open Cslib.Crypto.Protocols.BCS Cslib.Crypto.Protocols.FRI

/-! ### Part 1: Concrete `ZMod 257` Parameters, Input Words & Query Accounting -/

instance instPrime257 : Fact (Nat.Prime 257) := ⟨by norm_num⟩

private theorem isPrimitiveRoot_four_eight : IsPrimitiveRoot (4 : ZMod 257) (2 ^ 3) := by
  refine IsPrimitiveRoot.mk (by decide : (4 : ZMod 257) ^ 8 = 1) ?_
  intro l hl
  have h8 : (4 : ZMod 257) ^ 8 = 1 := by decide
  have hmod : (4 : ZMod 257) ^ (l % 8) = 1 := by
    have hsplit : (4 : ZMod 257) ^ (8 * (l / 8)) * (4 : ZMod 257) ^ (l % 8) = 1 := by
      rw [← pow_add, Nat.div_add_mod]
      exact hl
    rw [pow_mul, h8, one_pow, one_mul] at hsplit
    exact hsplit
  have hlt : l % 8 < 8 := Nat.mod_lt l (by omega)
  have hr_zero : ∀ r : Fin 8, (4 : ZMod 257) ^ r.val = 1 → r.val = 0 := by
    intro r hr
    fin_cases r <;> first | rfl | exact absurd hr (by decide)
  exact Nat.dvd_of_mod_eq_zero (hr_zero ⟨l % 8, hlt⟩ hmod)

/-- Concrete `2`-folding-round (`m = 2`, so `m + 2 = 4` total batched IOP rounds), depth-`3`
(`|L_0| = 8`), rate-`1/2` (`kFinal = 1`, `dim 0 = 4`), `q = 6` query FRI parameters over
`ZMod 257`. -/
def params257 : FRIParams (ZMod 257) where
  d := 3
  m := 2
  kFinal := 1
  q := 6
  g := 1
  ω := 4
  hm := by omega
  hkPos := by omega
  hkLe := by omega
  hg := one_ne_zero
  h2 := by decide
  hω := isPrimitiveRoot_four_eight

-- Exact query-count checks for batch size `t = 2` (`3` input words).
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

/-- Base degree-`< 4` Reed–Solomon codeword `5 + 3 X + 7 X^2 + 2 X^3` on `L_0`. -/
def baseWord : OracleTable params257.d (ZMod 257) :=
  fun idx =>
    let x := params257.eval 0 idx
    5 + 3 * x + 7 * x ^ 2 + 2 * x ^ 3

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

private theorem poly_cubic_degree_lt (c0 c1 c2 c3 : ZMod 257) :
    (C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3).degree < (4 : WithBot ℕ) := by
  have h0 : (C c0).degree < (4 : WithBot ℕ) := lt_of_le_of_lt degree_C_le (by decide)
  have h1 : (C c1 * X).degree < (4 : WithBot ℕ) :=
    lt_of_le_of_lt (degree_mul_le _ _) (lt_of_le_of_lt (add_le_add degree_C_le degree_X_le)
      (by decide))
  have h2 : (C c2 * X ^ 2).degree < (4 : WithBot ℕ) :=
    lt_of_le_of_lt (degree_mul_le _ _) (lt_of_le_of_lt (add_le_add degree_C_le (degree_X_pow_le 2))
      (by decide))
  have h3 : (C c3 * X ^ 3).degree < (4 : WithBot ℕ) :=
    lt_of_le_of_lt (degree_mul_le _ _) (lt_of_le_of_lt (add_le_add degree_C_le (degree_X_pow_le 3))
      (by decide))
  have hadd : ∀ {p q : Polynomial (ZMod 257)},
      p.degree < (4 : WithBot ℕ) → q.degree < (4 : WithBot ℕ) →
      (p + q).degree < (4 : WithBot ℕ) :=
    fun hp hq => lt_of_le_of_lt (degree_add_le _ _) (max_lt hp hq)
  exact hadd (hadd (hadd h0 h1) h2) h3

theorem baseWord_mem_initialCode : baseWord ∈ params257.initialCode := by
  refine mem_reedSolomon.mpr ⟨C 5 + C 3 * X + C 7 * X ^ 2 + C 2 * X ^ 3,
    poly_cubic_degree_lt 5 3 7 2, ?_⟩
  ext idx
  simp only [baseWord, eval_add, eval_mul, eval_pow, eval_C, eval_X]

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

/-- Concrete honest `3`-word affine batch statement `(baseWord, termWord0, termWord1)`. -/
def honestBatchStmt : FRIBatchStmt (ZMod 257) params257.d 2 where
  base := baseWord
  terms := ![termWord0, termWord1]

/-- Concrete honest homogeneous linear batch statement (`f₀⁽⁰⁾ = 0`). -/
def honestLinearStmt : FRIBatchStmt (ZMod 257) params257.d 2 :=
  FRIBatchStmt.linear ![termWord0, termWord1]

theorem honestBatchStmt_completeRel :
    params257.batchCompletenessRel 2 honestBatchStmt () := by
  refine ⟨baseWord_mem_initialCode, fun j => ?_⟩
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

/-- Concrete `4`-round challenge vector for `friBatchIOP params257 2`:
* Round `0` supplies batching scalars `x = ![7, 13]`,
* Rounds `1, 2` supply folding scalars `11, 19`, and
* Round `3` supplies `6` query positions `1, 2, 3, 4, 5, 6` (leaving index `0` unqueried). -/
def sampleBatchChals : Fin (params257.m + 2) → FRIBatchChal (ZMod 257) params257.d params257.q 2
  | ⟨0, _⟩ => ⟨![7, 13], 0, fun a => ⟨(a.val + 1) % 8, Nat.mod_lt _ (by omega)⟩⟩
  | ⟨1, _⟩ => ⟨![0, 0], 11, fun a => ⟨(a.val + 1) % 8, Nat.mod_lt _ (by omega)⟩⟩
  | ⟨2, _⟩ => ⟨![0, 0], 19, fun a => ⟨(a.val + 2) % 8, Nat.mod_lt _ (by omega)⟩⟩
  | ⟨3, _⟩ => ⟨![0, 0], 23, fun a => ⟨(a.val + 1) % 8, Nat.mod_lt _ (by omega)⟩⟩

-- Query list length & round-0 non-opening checks.
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

/-- Perturbed batch statement modifying `base` at unqueried position `0 : Fin 8`. -/
def perturbedBatchStmt : FRIBatchStmt (ZMod 257) params257.d 2 where
  base := fun s => if s = ⟨0, by decide⟩ then baseWord s + 1 else baseWord s
  terms := ![termWord0, termWord1]

theorem perturbedBatchStmt_ne_honestBatchStmt : perturbedBatchStmt ≠ honestBatchStmt := by
  intro h
  have h0 : perturbedBatchStmt.base ⟨0, by decide⟩ = honestBatchStmt.base ⟨0, by decide⟩ :=
    congrFun (congrArg FRIBatchStmt.base h) ⟨0, by decide⟩
  exact absurd h0 (by decide)

-- Input-query locality: `friBatchDecide` produces identical decisions on `perturbedBatchStmt` and
-- `honestBatchStmt` because position `0` is outside `friBatchInputQueries`.
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

-- Concrete IOP verification on both affine (`honestBatchStmt`) and linear (`honestLinearStmt`)
-- statements.
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

/-- Deterministic Merkle hash and Fiat–Shamir oracle for concrete BCS compilation checks. -/
def idHash (msg : List Bool) : List Bool := msg

def constBatchFS (_ : FRIBatchStmt (ZMod 257) params257.d 2) (rts : List (List Bool)) :
    FRIBatchChal (ZMod 257) params257.d params257.q 2 :=
  sampleBatchChals ⟨rts.length % 4, Nat.mod_lt _ (by decide)⟩

-- Deterministic BCS verification of the honest batched FRI proof.
example :
    bcsVerify (friBatchIOP params257 2) (fun _ => idHash) [] (encZMod (p := 257)) constBatchFS
      honestBatchStmt
      (bcsProve (friBatchIOP params257 2) (fun _ => idHash) [] (encZMod (p := 257)) constBatchFS
        honestBatchStmt ()) = true :=
  friBatchBCS_verify_prove_eq_true params257 2 (fun _ => idHash) [] (encZMod (p := 257))
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

/-! ### Part 3: Nonvacuous False Tuple & Concrete Cheating-Prover Rejections -/

/-- Non-codeword evaluating `X ^ 4` on `L_0` (Hamming distance `≥ 4` from `params257.initialCode`).
-/
def farWord : OracleTable params257.d (ZMod 257) :=
  fun idx => (params257.eval 0 idx) ^ 4

private theorem farWord_eq_neg_one_pow (idx : Fin (2 ^ params257.d)) :
    farWord idx = (-1 : ZMod 257) ^ idx.val := by
  have h4 : (4 : ZMod 257) ^ 4 = -1 := by decide
  simp only [farWord, FRIParams.eval, cosetEval, cosetPoint, params257, pow_zero, pow_one, one_mul]
  rw [← pow_mul, mul_comm, pow_mul, h4]

private theorem card_filter_congr_decidable {α : Type*} (s : Finset α) (p : α → Prop)
    (h₁ h₂ : DecidablePred p) :
    (@Finset.filter α p h₁ s).card = (@Finset.filter α p h₂ s).card :=
  congrArg (fun h => (@Finset.filter α p h s).card) (Subsingleton.elim h₁ h₂)

/-- `farWord` agrees with any degree-`< 4` codeword on at most `4` points of the `8`-point coset. -/
theorem card_agree_farWord_le_four {c : OracleTable params257.d (ZMod 257)}
    (hc_rs : c ∈ params257.initialCode) {D' : Finset (Fin (2 ^ params257.d))}
    (hagree : ∀ s ∈ D', farWord s = c s) :
    D'.card ≤ 4 := by
  classical
  obtain ⟨p, hp_deg, hpeq⟩ := mem_reedSolomon.mp hc_rs
  let q : Polynomial (ZMod 257) := X ^ 4 - p
  have hp_lt : p.degree < (X ^ 4 : Polynomial (ZMod 257)).degree := by
    rw [degree_X_pow]
    exact hp_deg
  have hq_deg : q.degree = (4 : ℕ) := by
    dsimp only [q]
    rw [degree_sub_eq_left_of_degree_lt hp_lt, degree_X_pow]
  have hq_ne : q ≠ 0 := by
    intro h0
    rw [h0, degree_zero] at hq_deg
    exact absurd hq_deg (by decide)
  have hq_natDeg : q.natDegree = 4 := natDegree_eq_of_degree_eq_some hq_deg
  have hα_inj : Function.Injective (params257.eval 0) :=
    cosetEval_injective params257.hg params257.hω (by omega)
  have himg_sub : D'.image (params257.eval 0) ⊆ q.roots.toFinset := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hroot : q.eval (params257.eval 0 j) = 0 := by
      have hcval : c j = p.eval (params257.eval 0 j) := (congrFun hpeq j).symm
      dsimp only [q]
      rw [eval_sub, eval_pow, eval_X, ← hcval]
      exact sub_eq_zero.mpr (hagree j hj)
    exact Multiset.mem_toFinset.mpr ((mem_roots hq_ne).mpr hroot)
  calc D'.card
      = (D'.image (params257.eval 0)).card := (Finset.card_image_of_injective D' hα_inj).symm
    _ ≤ q.roots.toFinset.card := Finset.card_le_card himg_sub
    _ ≤ q.roots.card := Multiset.toFinset_card_le q.roots
    _ ≤ q.natDegree := card_roots' q
    _ = 4 := hq_natDeg

theorem farWord_not_mem_proximityLang : farWord ∉ params257.proximityLang 2 := by
  classical
  rintro ⟨c, hc_rs, hdist⟩
  let S_eq : Finset (Fin (2 ^ params257.d)) :=
    Finset.univ.filter fun j => farWord j = c j
  have hS_le : S_eq.card ≤ 4 :=
    card_agree_farWord_le_four hc_rs fun j hj => (Finset.mem_filter.mp hj).2
  have hpart : S_eq.card + hammingDist farWord c = 8 := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (2 ^ params257.d)))) (fun j => farWord j = c j)
    have hcard : (Finset.univ : Finset (Fin (2 ^ params257.d))).card = 8 := by
      rw [Finset.card_univ, Fintype.card_fin]
      rfl
    have hfilt : (Finset.univ.filter (fun j : Fin (2 ^ params257.d) => ¬farWord j = c j)).card =
        hammingDist farWord c :=
      card_filter_congr_decidable _ _ _ _
    rw [hcard, hfilt] at h
    exact h
  have hdist' : hammingDist farWord c ≤ 2 := hdist
  omega

/-- Batch statement replacing the second generator word by `farWord`. -/
def badBatchStmt : FRIBatchStmt (ZMod 257) params257.d 2 where
  base := baseWord
  terms := ![termWord0, farWord]

/-- `badBatchStmt` has correlated agreement on at most `4 < 6 = 8 - 2` points, so it lies outside
`params257.batchProximityLang 2 2`. -/
theorem badBatchStmt_not_mem_batchProximityLang :
    badBatchStmt ∉ params257.batchProximityLang 2 2 := by
  rintro ⟨D', hcard, _, _, v, hv, hagree⟩
  have hle : D'.card ≤ 4 :=
    card_agree_farWord_le_four (hv 1) fun s hs => by
      simpa only [badBatchStmt, Matrix.cons_val_one, Matrix.cons_val_fin_one] using
        (hagree s hs).2 1
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

private theorem fold2Fiber_add (a₁ b₁ a₂ b₂ x z : ZMod 257) :
    fold2Fiber (a₁ + b₁) (a₂ + b₂) x z = fold2Fiber a₁ a₂ x z + fold2Fiber b₁ b₂ x z := by
  simp only [fold2Fiber]
  ring

private theorem fold2Fiber_same (y x z : ZMod 257) : fold2Fiber y y x z = y := by
  have h2 : (2 : ZMod 257) ≠ 0 := by decide
  simp only [fold2Fiber, sub_self, zero_div, mul_zero, add_zero]
  rw [← two_mul, mul_div_cancel_left₀ y h2]

private theorem friHonestWord_add (u v : OracleTable params257.d (ZMod 257)) :
    ∀ (i : ℕ) (hi : i ≤ params257.m) (zs : Fin i → ZMod 257) (j : Fin (2 ^ (params257.d - i))),
      friHonestWord params257 (u + v) i hi zs j =
        friHonestWord params257 u i hi zs j + friHonestWord params257 v i hi zs j
  | 0, _, _, _ => rfl
  | i + 1, hi, zs, j => by
    rw [friHonestWord_succ_apply, friHonestWord_succ_apply, friHonestWord_succ_apply,
      friHonestWord_add u v i (Nat.le_of_succ_le hi) (fun k => zs k.castSucc),
      friHonestWord_add u v i (Nat.le_of_succ_le hi) (fun k => zs k.castSucc),
      fold2Fiber_add]

-- Rejection 1: folding the non-codeword combination `badBatchStmt.eval ![7, 13]` fails the final
-- constant-codeword Lagrange check because `13 • farWord` folds to `(13, -13)` on `L_2`.
theorem badBatchStmt_iopVerify_eq_false :
    iopVerify (friBatchIOP params257 2) badBatchStmt sampleBatchChals
      (iopProverOracles (friBatchIOP params257 2) badBatchStmt () sampleBatchChals) = false := by
  by_contra hne
  have htrue :
      iopVerify (friBatchIOP params257 2) badBatchStmt sampleBatchChals
        (iopProverOracles (friBatchIOP params257 2) badBatchStmt () sampleBatchChals) = true :=
    Bool.eq_true_of_not_eq_false hne
  rw [iopVerify_friBatchIOP_eq_iopVerify_friIOP] at htrue
  have hor_eq :
      (fun j => iopProverOracles (friBatchIOP params257 2) badBatchStmt () sampleBatchChals
        j.succ) =
      iopProverOracles (friIOP params257) (badBatchStmt.eval (sampleBatchChals 0).batchCoeffs) ()
        (friTailChals sampleBatchChals) := by
    ext j idx
    exact congrFun (iopProverOracles_friBatchIOP_succ params257 2 badBatchStmt sampleBatchChals j)
      idx
  rw [hor_eq] at htrue
  have hfin := ((iopVerify_friIOP_eq_true_iff params257
    (badBatchStmt.eval (sampleBatchChals 0).batchCoeffs) (friTailChals sampleBatchChals) _).mp
    htrue ⟨0, by decide⟩).2.2
  let uGood : OracleTable params257.d (ZMod 257) := baseWord + (7 : ZMod 257) • termWord0
  have huGood : uGood ∈ params257.initialCode :=
    params257.initialCode.add_mem baseWord_mem_initialCode
      (params257.initialCode.smul_mem 7 termWord0_mem_initialCode)
  have hcoeffs : (sampleBatchChals 0).batchCoeffs = ![7, 13] := rfl
  have heval : badBatchStmt.eval (sampleBatchChals 0).batchCoeffs =
      uGood + (13 : ZMod 257) • farWord := by
    rw [hcoeffs]
    ext s
    simp only [FRIBatchStmt.eval, badBatchStmt, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, uGood, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  let zs : Fin 2 → ZMod 257 :=
    fun k => (prefixChallenges (friTailChals sampleBatchChals) (Fin.last 2) k).foldScalar
  have h1le : 1 ≤ params257.m := by decide
  have h2le : 2 ≤ params257.m := by decide
  have hw1 : ∀ (zs1 : Fin 1 → ZMod 257) (j : Fin (2 ^ (params257.d - 1))),
      friHonestWord params257 ((13 : ZMod 257) • farWord) 1 h1le zs1 j =
        13 * (-1 : ZMod 257) ^ j.val := by
    intro zs1 j
    have hj : j.val < 4 := j.isLt
    change fold2Fiber (13 * farWord ⟨j.val, by dsimp [params257]; omega⟩)
      (13 * farWord ⟨j.val + 4, by dsimp [params257]; omega⟩) _ _ = _
    rw [farWord_eq_neg_one_pow ⟨j.val, by dsimp [params257]; omega⟩,
      farWord_eq_neg_one_pow ⟨j.val + 4, by dsimp [params257]; omega⟩]
    have hpow4 : (-1 : ZMod 257) ^ (j.val + 4) = (-1 : ZMod 257) ^ j.val := by
      rw [pow_add]
      norm_num
    rw [hpow4, fold2Fiber_same]
  have hw2_far : ∀ j : Fin (2 ^ (params257.d - 2)),
      friHonestWord params257 ((13 : ZMod 257) • farWord) 2 h2le zs j =
        13 * (-1 : ZMod 257) ^ j.val := by
    intro j
    have hj : j.val < 2 := j.isLt
    change fold2Fiber
        (friHonestWord params257 ((13 : ZMod 257) • farWord) 1 h1le
          (fun k => zs ⟨k.val, by omega⟩) ⟨j.val, by dsimp [params257]; omega⟩)
        (friHonestWord params257 ((13 : ZMod 257) • farWord) 1 h1le
          (fun k => zs ⟨k.val, by omega⟩) ⟨j.val + 2, by dsimp [params257]; omega⟩) _ _ = _
    rw [hw1 _ ⟨j.val, by dsimp [params257]; omega⟩,
      hw1 _ ⟨j.val + 2, by dsimp [params257]; omega⟩]
    have hpow2 : (-1 : ZMod 257) ^ (j.val + 2) = (-1 : ZMod 257) ^ j.val := by
      rw [pow_add]
      norm_num
    rw [hpow2, fold2Fiber_same]
  have hw2_good_const :
      friHonestWord params257 uGood 2 h2le zs ⟨1, by decide⟩ =
        friHonestWord params257 uGood 2 h2le zs ⟨0, by decide⟩ := by
    have hrs : friHonestWord params257 uGood params257.m le_rfl zs ∈
        reedSolomon (params257.eval params257.m) params257.kFinal :=
      friHonestWord_mem_rsCode params257 huGood params257.m le_rfl zs
    have hrec := evalLagrange_eq_of_mem_reedSolomon params257.hkLe
      (cosetEval_injective params257.hg params257.hω params257.hm) hrs ⟨1, by decide⟩
    exact hrec.symm.trans (by
      dsimp only [evalLagrange, params257]
      simp only [Finset.univ_unique, Finset.sum_singleton, Finset.erase_singleton,
        Finset.prod_empty, mul_one]
      rfl)
  let c0 := friHonestWord params257 uGood 2 h2le zs ⟨0, by decide⟩
  have hor0 :
      iopProverOracles (friIOP params257) (badBatchStmt.eval (sampleBatchChals 0).batchCoeffs)
        () (friTailChals sampleBatchChals) (Fin.last params257.m) ⟨0, by decide⟩ = c0 + 13 := by
    change padOracle (i := 2)
      (friHonestWord params257 (badBatchStmt.eval (sampleBatchChals 0).batchCoeffs) 2 h2le zs)
      ⟨0, by decide⟩ = c0 + 13
    rw [padOracle_apply_of_lt _ _ (by decide : (0 : ℕ) < 2 ^ (params257.d - 2)), heval,
      friHonestWord_add, hw2_far]
    simp only [c0, pow_zero, mul_one]
  have hor1 :
      iopProverOracles (friIOP params257) (badBatchStmt.eval (sampleBatchChals 0).batchCoeffs)
        () (friTailChals sampleBatchChals) (Fin.last params257.m) ⟨1, by decide⟩ = c0 - 13 := by
    change padOracle (i := 2)
      (friHonestWord params257 (badBatchStmt.eval (sampleBatchChals 0).batchCoeffs) 2 h2le zs)
      ⟨1, by decide⟩ = c0 - 13
    rw [padOracle_apply_of_lt _ _ (by decide : (1 : ℕ) < 2 ^ (params257.d - 2)), heval,
      friHonestWord_add, hw2_far]
    have hidx1 : (⟨(⟨1, by decide⟩ : Fin (2 ^ params257.d)).val,
        (by decide : (1 : ℕ) < 2 ^ (params257.d - 2))⟩ : Fin (2 ^ (params257.d - 2))) =
        ⟨1, by decide⟩ := rfl
    rw [hidx1, hw2_good_const]
    dsimp only [c0]
    ring
  have hlag :
      friFinalCodeword params257
        (iopProverOracles (friIOP params257) (badBatchStmt.eval (sampleBatchChals 0).batchCoeffs)
          () (friTailChals sampleBatchChals) (Fin.last params257.m))
        ⟨1, by decide⟩ = c0 + 13 := by
    change ∑ t : Fin 1,
        iopProverOracles (friIOP params257) (badBatchStmt.eval (sampleBatchChals 0).batchCoeffs)
          () (friTailChals sampleBatchChals) (Fin.last params257.m)
          ⟨t.val, by dsimp [params257]; omega⟩ *
        ∏ u ∈ Finset.univ.erase t,
          (params257.eval 2 ⟨1, by decide⟩ - params257.finalAnchorPoints u) /
          (params257.finalAnchorPoints t - params257.finalAnchorPoints u) = c0 + 13
    simp only [Finset.univ_unique, Finset.sum_singleton, Finset.erase_singleton,
      Finset.prod_empty, mul_one]
    exact hor0
  change iopProverOracles (friIOP params257) (badBatchStmt.eval (sampleBatchChals 0).batchCoeffs)
      () (friTailChals sampleBatchChals) (Fin.last params257.m)
      (friFinalIdx params257 ⟨1, by decide⟩) =
    friFinalCodeword params257
      (iopProverOracles (friIOP params257) (badBatchStmt.eval (sampleBatchChals 0).batchCoeffs)
        () (friTailChals sampleBatchChals) (Fin.last params257.m))
      (friFinalFin params257 ⟨1, by decide⟩) at hfin
  have hfinIdx : friFinalIdx params257 ⟨1, by decide⟩ = ⟨1, by decide⟩ := rfl
  have hfinFin : friFinalFin params257 ⟨1, by decide⟩ = ⟨1, by decide⟩ := rfl
  rw [hfinIdx, hfinFin, hor1, hlag] at hfin
  have h26 : (26 : ZMod 257) = 0 := by
    calc (26 : ZMod 257) = (c0 + 13) - (c0 - 13) := by ring
      _ = 0 := sub_eq_zero.mpr hfin.symm
  exact absurd h26 (by decide)

-- Rejection 2: a malicious prover who commits the valid Reed–Solomon tables of `honestBatchStmt`
-- (passing all folding checks and the final Lagrange check) is rejected by the round-1 affine
-- batching check `oracles 1 s = badBatchStmt.base s + ∑ x_j * badBatchStmt.terms j s`!
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
      (0 : Fin (params257.m + 1)).succ ⟨1, by decide⟩ =
      honestBatchStmt.eval (sampleBatchChals 0).batchCoeffs ⟨1, by decide⟩ := by
    rw [iopProverOracles_friBatchIOP_succ]
    change padOracle (i := 0) (honestBatchStmt.eval (sampleBatchChals 0).batchCoeffs)
        ⟨1, by decide⟩ = _
    exact padOracle_apply_of_lt _ _ (by decide : (1 : ℕ) < 2 ^ (params257.d - 0))
  have hidx : (⟨1, by omega⟩ : Fin (params257.m + 2)) = (0 : Fin (params257.m + 1)).succ := rfl
  rw [hidx, hor] at hbatch
  change honestBatchStmt.eval (sampleBatchChals 0).batchCoeffs ⟨1, by decide⟩ =
      badBatchStmt.eval (sampleBatchChals 0).batchCoeffs ⟨1, by decide⟩ at hbatch
  have hdiff : honestBatchStmt.eval (sampleBatchChals 0).batchCoeffs ⟨1, by decide⟩ ≠
      badBatchStmt.eval (sampleBatchChals 0).batchCoeffs ⟨1, by decide⟩ := by
    simp only [FRIBatchStmt.eval, honestBatchStmt, badBatchStmt, sampleBatchChals,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    decide
  exact hdiff hbatch

/-! ### Part 4: `t = 0` Equivalence & Concrete Ceiling / Floor Real-`α` Threshold Bridges -/

-- Exercise `mem_batchProximityLang_zero_iff` on both a close word and a far word.
example : (⟨baseWord, Fin.elim0⟩ : FRIBatchStmt (ZMod 257) params257.d 0) ∈
    params257.batchProximityLang 0 2 := by
  rw [mem_batchProximityLang_zero_iff]
  refine ⟨baseWord, baseWord_mem_initialCode, ?_⟩
  change hammingDist baseWord baseWord ≤ 2
  rw [hammingDist_self]
  omega

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

-- Exercise `batchFloorThreshold_bounds` at the exact integer product boundary `α = 5 / 8`
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
