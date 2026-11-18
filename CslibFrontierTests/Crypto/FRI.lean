/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module

public import CslibFrontier.Crypto.Protocols.FRI.Soundness
import CslibFrontier.Languages.Probabilistic.QueryCount.Support
import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic.NormNum.Prime
public import CslibFrontierTests.Crypto.MerkleTestHash

/-!
# Concrete Nonvacuous Tests for Multi-Round FRI and BCS-FRI ROM Soundness

Exercises the Milestone 5 FRI modules (`CslibFrontier.Crypto.Protocols.FRI.Folding`, `Protocol`,
and `Soundness`) from an ordinary `module` client (no `import all`) over the prime field
`ZMod 257` (`d = 3`, initial coset size `8`, `m = 2` folding rounds, `kFinal = 1`, rate `1 / 2`,
`q = 6` batched queries, unique-decoding radius `e = 2`):

1. **Concrete parameter construction & coset folding (`Folding.lean`).** Certifies
   `Fact (Nat.Prime 257)`, `IsPrimitiveRoot (4 : ZMod 257) 8`, fiber-representative invariance
   `fold2Fiber_swap`, codeword preservation `fold2_mem_reedSolomon`, unsigned little-endian binary
   symbol encoding `encZMod`/`decZMod` (built on `Nat.bits`/`Turing.MultiTapeTM.ofBits`), and
   Lagrange recovery `evalLagrange_eq_of_mem_reedSolomon` (bridged to `Lagrange.interpolate`) on
   an explicit cubic Reed–Solomon codeword `honestWord`.
2. **Multi-round `PublicCoinIOP` completeness & BCS instantiation (`Protocol.lean`).** Evaluates
   committed-proof-oracle openings (`49`), direct input-word reads (`6`), and total word queries
   (`55`) by `rfl`, checks `friDecide_congr_inputQueries`, and certifies honest IOP acceptance
   (`friIOP_complete`), deterministic BCS verification (`friBCS_verify_prove_eq_true`), perfect
   BCS ROM completeness (`friBCS_honestROMGame_eq_pure_true`), and verifier Merkle query cost
   bounds (`isCostBounded_bcsMTCost_friVerifyROM`).
3. **Far-from-Reed–Solomon rejection & nonvacuity.** Proves that `farWord` (evaluating `X ^ 4` on
   the 8-point coset) has Hamming distance at least `4 > 2` from every codeword in
   `params257.initialCode` (hence `farWord ∉ params257.proximityLang 2`), and proves concrete
   verifier rejection `iopVerify (friIOP params257) farWord sampleChals ... = false`.
4. **Unconditional quantitative BCS-FRI ROM soundness `< 1 / 3 < 1` (`Soundness.lean`).** Proves
   `UniqueLineGapHypothesis params257 2` unconditionally for the fixed `params257` client by
   finite-field pigeonhole and discharges `leftInverse_decZMod_encZMod 257`, yielding:
   * an unconditional adaptive BCS-FRI ROM soundness bound strictly `< 1 / 3 < 1` for every bounded
     adversary (`t_FS = 2`, whole-game `Q_MT = 1000`, `σ = 32`) via
     `friBCS_romSoundness_bound_of_uniqueLineGap` — where `Q_MT = 1000` strictly exceeds the
     `49 * (3 + 1) = 196` verifier Merkle hash queries required for depth-3 accepting-shaped proofs
     (directly witnessed by instantiating the universal bound on `friCheater257`);
   * an explicit out-of-order adaptive cheating prover `friCheater257` (`t_FS = 2`, `t_MT = 2`,
     `L_path = 3`) certified strictly `< 1 / 2 < 1` at `σ = 20` via
     `friBCS_romSoundness_bound_of_prover_verifier_of_weightedLineGap`.
5. **Per-round shrinking budgets, `iopInteractiveGame`, and `friCommitGame` (`BCS.Interactive` and
   `Soundness.lean`).**
   Certifies `iopInteractiveGame_ofCausal_eq` (`= PMF.pure true` on `honestWord`), shrinking
   unique-decoding round budgets `(4, 2)` summing to `6 < 2 * 4 = 8` via
   `weightedLineGapPerRound_of_uniqueLineGap` and `FRIParams.sum_domainSize_succ`, commit-phase
   bound `< 1 / 40` via `friCommitGame_le_of_weightedLineGapPerRound`, summed interactive IOP
   soundness `< 1 / 11` via `friIOP_interactiveGame_le_of_weightedLineGapPerRound`, and `sup`-based
   BCS ROM soundness via
   `friBCS_romSoundness_bound_of_prover_verifier_of_weightedLineEscapePerRound`.
-/

-- Exports the concrete `ZMod 257` fixture and degree-4 root-count helper shared with
-- `CslibFrontierTests/Crypto/FRIBatch.lean`.

namespace CslibFrontierTests.Crypto.FRI

open scoped BigOperators NNReal ENNReal
open Polynomial
open Cslib Cslib.Code Cslib.OracleComp Cslib.Probability
open CslibFrontierTests.Crypto.MerkleTestHash
open Cslib.Crypto.Protocols.BCS Cslib.Crypto.Protocols.FRI

/-! ### Part 1: Concrete `ZMod 257` FRI Parameters & Folding Checks -/

public instance instPrime257 : Fact (Nat.Prime 257) := ⟨by norm_num⟩

public theorem isPrimitiveRoot_four_eight : IsPrimitiveRoot (4 : ZMod 257) (2 ^ 3) := by
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

/-- Concrete 2-folding-round (`m = 2`, 3 total IOP rounds), depth-3 (`|L_0| = 8`), rate-`1/2`
(`kFinal = 1`, `dim 0 = 4`), `q = 6` batched-query FRI instance over `ZMod 257`. -/
@[expose] public def params257 : FRIParams (ZMod 257) where
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

example : params257.dim 0 = 4 := rfl
example : params257.dim 1 = 2 := rfl
example : params257.dim 2 = 1 := rfl
example : params257.proofOracleQueries = 49 := rfl
example : params257.inputWordReads = 6 := rfl
example : params257.totalWordQueries = 55 := rfl

-- Concrete binary symbol encoding word-layout and round-trip evaluations.
example : encZMod (0 : ZMod 257) = [] := by decide
example : encZMod (42 : ZMod 257) = [false, true, false, true, false, true] := by decide
example : decZMod 257 (encZMod (42 : ZMod 257)) = 42 := leftInverse_decZMod_encZMod 257 42
example : decZMod 257 (encZMod (256 : ZMod 257)) = 256 := leftInverse_decZMod_encZMod 257 256

/-- Concrete degree-3 polynomial `5 + 3 X + 7 X^2 + 2 X^3 ∈ (ZMod 257)[X]`. -/
noncomputable def honestPoly : Polynomial (ZMod 257) :=
  C 5 + C 3 * X + C 7 * X ^ 2 + C 2 * X ^ 3

/-- Concrete degree-`< 4` Reed–Solomon codeword on `L_0` (`|L_0| = 8`). -/
@[expose] public def honestWord : OracleTable 3 (ZMod 257) :=
  fun idx =>
    let x := params257.eval 0 idx
    5 + 3 * x + 7 * x ^ 2 + 2 * x ^ 3

theorem honestPoly_eval (x : ZMod 257) :
    honestPoly.eval x = 5 + 3 * x + 7 * x ^ 2 + 2 * x ^ 3 := by
  simp only [honestPoly, eval_add, eval_mul, eval_pow, eval_C, eval_X]

public theorem poly_cubic_degree_lt (c0 c1 c2 c3 : ZMod 257) :
    (C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3).degree < (4 : WithBot ℕ) := by
  have h0 : (C c0).degree < (4 : WithBot ℕ) :=
    lt_of_le_of_lt degree_C_le (by decide)
  have h1 : (C c1 * X).degree < (4 : WithBot ℕ) := by
    refine lt_of_le_of_lt (degree_mul_le _ _) ?_
    refine lt_of_le_of_lt (add_le_add degree_C_le degree_X_le) (by decide)
  have h2 : (C c2 * X ^ 2).degree < (4 : WithBot ℕ) := by
    refine lt_of_le_of_lt (degree_mul_le _ _) ?_
    refine lt_of_le_of_lt (add_le_add degree_C_le (degree_X_pow_le 2)) (by decide)
  have h3 : (C c3 * X ^ 3).degree < (4 : WithBot ℕ) := by
    refine lt_of_le_of_lt (degree_mul_le _ _) ?_
    refine lt_of_le_of_lt (add_le_add degree_C_le (degree_X_pow_le 3)) (by decide)
  have hadd : ∀ {p q : Polynomial (ZMod 257)},
      p.degree < (4 : WithBot ℕ) → q.degree < (4 : WithBot ℕ) →
      (p + q).degree < (4 : WithBot ℕ) :=
    fun hp hq => lt_of_le_of_lt (degree_add_le _ _) (max_lt hp hq)
  exact hadd (hadd (hadd h0 h1) h2) h3

theorem honestPoly_degree_lt : honestPoly.degree < (4 : WithBot ℕ) :=
  poly_cubic_degree_lt 5 3 7 2

public theorem honestWord_mem_initialCode : honestWord ∈ params257.initialCode := by
  refine mem_reedSolomon.mpr ⟨honestPoly, honestPoly_degree_lt, ?_⟩
  ext idx
  exact honestPoly_eval (params257.eval 0 idx)

public theorem honestWord_mem_proximityLang : honestWord ∈ params257.proximityLang 2 := by
  refine ⟨honestWord, honestWord_mem_initialCode, ?_⟩
  change hammingDist honestWord honestWord ≤ 2
  rw [hammingDist_self]
  omega

-- Fiber-representative invariance check on concrete values from `honestWord`.
example :
    fold2Fiber (honestWord ⟨4, by decide⟩) (honestWord ⟨0, by decide⟩)
      (-(params257.eval 0 ⟨0, by decide⟩)) (11 : ZMod 257) =
    fold2Fiber (honestWord ⟨0, by decide⟩) (honestWord ⟨4, by decide⟩)
      (params257.eval 0 ⟨0, by decide⟩) (11 : ZMod 257) :=
  fold2Fiber_swap (honestWord ⟨0, by decide⟩) (honestWord ⟨4, by decide⟩)
    (params257.eval 0 ⟨0, by decide⟩) (11 : ZMod 257)

-- Concrete 2-to-1 coset folding preserves Reed–Solomon membership at half dimension.
example :
    fold2 params257.g params257.ω (N := 4) honestWord (11 : ZMod 257) ∈
      reedSolomon (cosetPoint (params257.g ^ 2) (params257.ω ^ 2) 4) 2 := by
  have hf0 : honestWord ∈ reedSolomon (cosetPoint params257.g params257.ω (2 * 4)) (2 * 2) := by
    have h := honestWord_mem_initialCode
    change honestWord ∈ reedSolomon (cosetEval 1 4 3 0) 4 at h
    simp only [cosetEval, pow_zero, pow_one] at h
    exact h
  exact fold2_mem_reedSolomon params257.hg params257.h2 (by omega : 0 < 4)
    params257.hω hf0 (11 : ZMod 257)

/-! ### Part 2: Multi-Round `PublicCoinIOP` Execution, Completeness & BCS Composition -/

/-- Concrete challenge vector for the 3 rounds of `friIOP params257`. -/
@[expose] public def sampleChals : Fin 3 → FRIChal (ZMod 257) 3 6
  | ⟨0, _⟩ => ⟨11, fun a => ⟨(a.val + 1) % 8, Nat.mod_lt _ (by omega)⟩⟩
  | ⟨1, _⟩ => ⟨19, fun a => ⟨(a.val + 2) % 8, Nat.mod_lt _ (by omega)⟩⟩
  | ⟨2, _⟩ => ⟨23, fun a => ⟨(a.val + 1) % 8, Nat.mod_lt _ (by omega)⟩⟩

-- Concrete succinct query list length checks: 49 committed-proof-oracle openings plus 6 direct
-- input-word reads (55 total word queries).
example : ((friIOP params257).queries honestWord sampleChals).length = 49 :=
  length_friIOP_queries params257 honestWord sampleChals
example : (friInputQueries params257 sampleChals).length = 6 :=
  length_friInputQueries params257 sampleChals
example (stmt' : OracleTable 3 (ZMod 257))
    (hagree : ∀ s ∈ friInputQueries params257 sampleChals, honestWord s = stmt' s)
    (answers : List (ZMod 257)) :
    friDecide params257 honestWord sampleChals answers =
      friDecide params257 stmt' sampleChals answers :=
  friDecide_congr_inputQueries params257 sampleChals hagree answers

-- Concrete honest IOP acceptance on `honestWord` and `sampleChals`.
example :
    iopVerify (friIOP params257) honestWord sampleChals
      (iopProverOracles (friIOP params257) honestWord () sampleChals) = true :=
  friIOP_complete params257 honestWord () honestWord_mem_initialCode sampleChals

/-- A deterministic Merkle hash with sixteen-bit digests. -/
public abbrev idHash : List Bool → List Bool := polyHash

/-- Deterministic Fiat–Shamir oracle returning `sampleChals` by root-list length. -/
def constFRIFS (_ : OracleTable 3 (ZMod 257)) (rts : List (List Bool)) :
    FRIChal (ZMod 257) 3 6 :=
  sampleChals ⟨rts.length % 3, Nat.mod_lt _ (by omega)⟩

-- Concrete deterministic BCS verification of the honest FRI proof.
example :
    bcsVerify (friIOP params257) (fun _ => idHash) [] (encZMod (p := 257)) constFRIFS honestWord
      (bcsProve (friIOP params257) (fun _ => idHash) [] (encZMod (p := 257)) constFRIFS
        honestWord ()) = true :=
  friBCS_verify_prove_eq_true params257 (fun _ => idHash) [] length_polyHash (encZMod (p := 257))
    constFRIFS honestWord_mem_initialCode

-- Perfect completeness in the two-channel lazy BCS random-oracle model for every digest length `σ`.
example (σ : ℕ) :
    bcsHonestROMGame (friIOP params257) (encZMod (p := 257)) honestWord () σ = PMF.pure true :=
  friBCS_honestROMGame_eq_pure_true params257 (encZMod (p := 257)) honestWord_mem_initialCode σ

-- Concrete round-2 Lagrange recovery on the honest folded word.
example (j : Fin 2) :
    evalLagrange params257.finalAnchorPoints
      (fun t : Fin 1 =>
        friHonestWord params257 honestWord 2 le_rfl
          (fun i => (sampleChals ⟨i.val, by omega⟩).foldScalar)
          ⟨t.val, Nat.lt_trans t.isLt (by decide : 1 < 2 ^ (params257.d - 2))⟩)
      (params257.eval 2 j) =
    friHonestWord params257 honestWord 2 le_rfl
      (fun i => (sampleChals ⟨i.val, by omega⟩).foldScalar) j :=
  evalLagrange_eq_of_mem_reedSolomon params257.hkLe
    (cosetEval_injective params257.hg params257.hω params257.hm)
    (friHonestWord_mem_rsCode params257 honestWord_mem_initialCode 2 le_rfl _) j

/-! ### Part 3: Far-from-Reed–Solomon Word & Concrete Rejection -/

/-- Non-codeword evaluating `X ^ 4` on `L_0` (taking alternating values `1, -1, 1, -1, ...`). -/
@[expose] public def farWord : OracleTable 3 (ZMod 257) :=
  fun idx => (params257.eval 0 idx) ^ 4

private theorem farWord_eq_neg_one_pow (idx : Fin 8) :
    farWord idx = (-1 : ZMod 257) ^ idx.val := by
  have h4 : (4 : ZMod 257) ^ 4 = -1 := by decide
  simp only [farWord, FRIParams.eval, cosetEval, cosetPoint, params257, pow_zero, pow_one, one_mul]
  rw [← pow_mul, mul_comm, pow_mul, h4]

private theorem card_filter_congr_decidable {α : Type*} (s : Finset α) (p : α → Prop)
    (h₁ h₂ : DecidablePred p) :
    (@Finset.filter α p h₁ s).card = (@Finset.filter α p h₂ s).card :=
  congrArg (fun h => (@Finset.filter α p h s).card) (Subsingleton.elim h₁ h₂)

/-- `farWord` agrees with any degree-`< 4` codeword on at most `4` points of the `8`-point coset. -/
public theorem card_agree_farWord_le_four {c : OracleTable params257.d (ZMod 257)}
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

/-- `farWord` has Hamming distance at least `4` from every degree-`< 4` codeword, hence lies
outside `params257.proximityLang 2`. -/
public theorem farWord_not_mem_proximityLang : farWord ∉ params257.proximityLang 2 := by
  classical
  rintro ⟨c, hc_rs, hdist⟩
  let S_eq : Finset (Fin (2 ^ params257.d)) :=
    Finset.univ.filter (fun j : Fin (2 ^ params257.d) => farWord j = c j)
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

private theorem fold2Fiber_same (y x z : ZMod 257) : fold2Fiber y y x z = y := by
  have h2 : (2 : ZMod 257) ≠ 0 := by decide
  simp only [fold2Fiber, sub_self, zero_div, mul_zero, add_zero]
  rw [← two_mul, mul_div_cancel_left₀ y h2]

/-- Concrete verifier rejection: the multi-round FRI verifier rejects `farWord` on `sampleChals`
(since folding `X ^ 4` twice yields the alternating word `(1, -1)` on `L_2`, which fails the
constant-polynomial Lagrange check at query index `1`). -/
public theorem farWord_iopVerify_eq_false :
    iopVerify (friIOP params257) farWord sampleChals
      (iopProverOracles (friIOP params257) farWord () sampleChals) = false := by
  by_contra hne
  have htrue :
      iopVerify (friIOP params257) farWord sampleChals
        (iopProverOracles (friIOP params257) farWord () sampleChals) = true :=
    Bool.eq_true_of_not_eq_false hne
  have hiff := (iopVerify_friIOP_eq_true_iff params257 farWord sampleChals
    (iopProverOracles (friIOP params257) farWord () sampleChals)).mp htrue
  have hfin := (hiff ⟨0, by decide⟩).2.2
  have hs : (sampleChals (Fin.last params257.m)).queryIdxs ⟨0, by decide⟩ = ⟨1, by decide⟩ := rfl
  let zs : Fin 2 → ZMod 257 :=
    fun k => (prefixChallenges sampleChals (Fin.last 2) k).foldScalar
  have h1le : 1 ≤ params257.m := by decide
  have hw1 : ∀ (zs1 : Fin 1 → ZMod 257) (j : Fin (2 ^ (params257.d - 1))),
      friHonestWord params257 farWord 1 h1le zs1 j = (-1 : ZMod 257) ^ j.val := by
    intro zs1 j
    have hj : j.val < 4 := j.isLt
    change fold2Fiber (farWord ⟨j.val, by omega⟩) (farWord ⟨j.val + 4, by omega⟩) _ _ = _
    rw [farWord_eq_neg_one_pow ⟨j.val, by omega⟩, farWord_eq_neg_one_pow ⟨j.val + 4, by omega⟩]
    have hpow4 : (-1 : ZMod 257) ^ (j.val + 4) = (-1 : ZMod 257) ^ j.val := by
      rw [pow_add]
      norm_num
    rw [hpow4, fold2Fiber_same]
  have hw2 : ∀ j : Fin (2 ^ (params257.d - 2)),
      friHonestWord params257 farWord 2 le_rfl zs j = (-1 : ZMod 257) ^ j.val := by
    intro j
    have hj : j.val < 2 := j.isLt
    change fold2Fiber
        (friHonestWord params257 farWord 1 h1le (fun k => zs ⟨k.val, by omega⟩)
          ⟨j.val, by dsimp [params257]; omega⟩)
        (friHonestWord params257 farWord 1 h1le (fun k => zs ⟨k.val, by omega⟩)
          ⟨j.val + 2, by dsimp [params257]; omega⟩) _ _ = _
    rw [hw1 _ ⟨j.val, by dsimp [params257]; omega⟩,
      hw1 _ ⟨j.val + 2, by dsimp [params257]; omega⟩]
    have hpow2 : (-1 : ZMod 257) ^ (j.val + 2) = (-1 : ZMod 257) ^ j.val := by
      rw [pow_add]
      norm_num
    rw [hpow2, fold2Fiber_same]
  have hor0 : iopProverOracles (friIOP params257) farWord () sampleChals (Fin.last params257.m)
      ⟨0, by decide⟩ = 1 := by
    change padOracle (i := 2) (friHonestWord params257 farWord 2 le_rfl zs) ⟨0, by decide⟩ = 1
    rw [padOracle_apply_of_lt _ _ (by decide : (0 : ℕ) < 2 ^ (params257.d - 2))]
    exact hw2 ⟨0, by decide⟩
  have hor1 : iopProverOracles (friIOP params257) farWord () sampleChals (Fin.last params257.m)
      ⟨1, by decide⟩ = -1 := by
    change padOracle (i := 2) (friHonestWord params257 farWord 2 le_rfl zs) ⟨1, by decide⟩ = -1
    rw [padOracle_apply_of_lt _ _ (by decide : (1 : ℕ) < 2 ^ (params257.d - 2))]
    simpa only [pow_one] using hw2 ⟨1, by decide⟩
  have hlag :
      friFinalCodeword params257
        (iopProverOracles (friIOP params257) farWord () sampleChals (Fin.last params257.m))
        ⟨1, by decide⟩ = 1 := by
    change ∑ t : Fin 1,
        iopProverOracles (friIOP params257) farWord () sampleChals (Fin.last params257.m)
          ⟨t.val, by dsimp [params257]; omega⟩ *
        ∏ u ∈ Finset.univ.erase t,
          (params257.eval 2 ⟨1, by decide⟩ - params257.finalAnchorPoints u) /
          (params257.finalAnchorPoints t - params257.finalAnchorPoints u) = 1
    simp only [Finset.univ_unique, Finset.sum_singleton, Finset.erase_singleton,
      Finset.prod_empty, mul_one]
    exact hor0
  change iopProverOracles (friIOP params257) farWord () sampleChals (Fin.last params257.m)
      (friFinalIdx params257 ⟨1, by decide⟩) =
    friFinalCodeword params257
      (iopProverOracles (friIOP params257) farWord () sampleChals (Fin.last params257.m))
      (friFinalFin params257 ⟨1, by decide⟩) at hfin
  have hfinIdx : friFinalIdx params257 ⟨1, by decide⟩ = ⟨1, by decide⟩ := rfl
  have hfinFin : friFinalFin params257 ⟨1, by decide⟩ = ⟨1, by decide⟩ := rfl
  rw [hfinIdx, hfinFin, hor1, hlag] at hfin
  exact absurd hfin (by decide)

/-! ### Part 4: Unconditional Pigeonhole Unique-Decoding Line Gap for `params257` -/

/-- For any two distinct scalars `z₁ ≠ z₂` on a line `u₀ + z • u₁`, two codewords `v₁', v₂'`
agreeing with the line on a common index set `D'` linearly solve for codewords `v₀, v₁` agreeing
with `(u₀, u₁)` on `D'`. -/
private theorem solve_line_two_points {ι : Type*} {α : ι → ZMod 257} {k : ℕ}
    {u₀ u₁ v₁' v₂' : ι → ZMod 257} {z₁ z₂ : ZMod 257} (hne : z₁ ≠ z₂)
    (hv₁ : v₁' ∈ reedSolomon α k) (hv₂ : v₂' ∈ reedSolomon α k)
    {D' : Finset ι}
    (h1 : ∀ j ∈ D', (u₀ + z₁ • u₁) j = v₁' j)
    (h2 : ∀ j ∈ D', (u₀ + z₂ • u₁) j = v₂' j) :
    ∃ v₀ ∈ reedSolomon α k, ∃ v₁ ∈ reedSolomon α k,
      ∀ j ∈ D', u₀ j = v₀ j ∧ u₁ j = v₁ j := by
  let inv := (z₁ - z₂)⁻¹
  let v₁ : ι → ZMod 257 := inv • (v₁' - v₂')
  let v₀ : ι → ZMod 257 := v₁' - z₁ • v₁
  have hv₁_mem : v₁ ∈ reedSolomon α k :=
    (reedSolomon α k).smul_mem inv ((reedSolomon α k).sub_mem hv₁ hv₂)
  have hv₀_mem : v₀ ∈ reedSolomon α k :=
    (reedSolomon α k).sub_mem hv₁ ((reedSolomon α k).smul_mem z₁ hv₁_mem)
  refine ⟨v₀, hv₀_mem, v₁, hv₁_mem, fun j hj => ?_⟩
  have hsub_ne : z₁ - z₂ ≠ 0 := sub_ne_zero.mpr hne
  have heq1 : u₀ j + z₁ * u₁ j = v₁' j := h1 j hj
  have heq2 : u₀ j + z₂ * u₁ j = v₂' j := h2 j hj
  have hdiff : (z₁ - z₂) * u₁ j = v₁' j - v₂' j := by
    calc (z₁ - z₂) * u₁ j
        = (u₀ j + z₁ * u₁ j) - (u₀ j + z₂ * u₁ j) := by ring
      _ = v₁' j - v₂' j := by rw [heq1, heq2]
  have hu₁ : u₁ j = v₁ j := by
    dsimp only [v₁, inv, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [← hdiff, inv_mul_cancel_left₀ hsub_ne]
  have hu₀ : u₀ j = v₀ j := by
    dsimp only [v₀, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hu₁, ← heq1]
    ring
  exact ⟨hu₀, hu₁⟩

/-- Unconditional unique-decoding line proximity gap for `params257` at radius `e = 2`:
round `0` has `e / 2 = 1` (solved by pigeonhole over the `4` coordinates since `4 < Z.card`), and
round `1` has `e / 4 = 0` (solved directly from any two distinct scalars in `Z`). -/
theorem uniqueLineGap_params257 : UniqueLineGapHypothesis params257 2 := by
  classical
  intro i u₀ u₁ Z hZ_gt hZ_close
  fin_cases i
  · -- Round 0: `N = 4`, radius `2 / 2 = 1`, `4 < Z.card`.
    have hZ_gt4 : 4 < Z.card := hZ_gt
    have hex_bad : ∀ z ∈ Z, ∃ j₀ : Fin 4, ∃ v ∈ params257.rsCode 1,
        ∀ j : Fin 4, j ≠ j₀ → (u₀ + z • u₁) j = v j := by
      intro z hz
      obtain ⟨v, hv_rs, hv_dist⟩ := hZ_close z hz
      let badSet : Finset (Fin 4) :=
        Finset.univ.filter (fun j : Fin 4 => (u₀ + z • u₁) j ≠ v j)
      have hbad_card : badSet.card ≤ 1 := by
        have hEq : badSet.card = hammingDist (u₀ + z • u₁) v :=
          card_filter_congr_decidable _ _ _ _
        have hle : hammingDist (u₀ + z • u₁) v ≤ 2 / 2 ^ (0 + 1) := hv_dist
        omega
      by_cases hemp : badSet = ∅
      · refine ⟨⟨0, by decide⟩, v, hv_rs, fun j _ => ?_⟩
        by_contra hne
        have hmem : j ∈ badSet := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne⟩
        rw [hemp] at hmem
        exact Finset.notMem_empty j hmem
      · obtain ⟨j₀, hj₀⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
        refine ⟨j₀, v, hv_rs, fun j hj_ne => ?_⟩
        by_contra hne
        have hj_mem : j ∈ badSet := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne⟩
        have hpair : ({j₀, j} : Finset (Fin 4)) ⊆ badSet := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hj₀
          · exact hj_mem
        have h2le : 2 ≤ badSet.card := by
          have hpair_card : ({j₀, j} : Finset (Fin 4)).card = 2 :=
            Finset.card_pair hj_ne.symm
          exact hpair_card ▸ Finset.card_le_card hpair
        omega
    let badIdx : ZMod 257 → Fin 4 := fun z =>
      if hz : z ∈ Z then (hex_bad z hz).choose else ⟨0, by decide⟩
    have hlt_card : (Finset.univ : Finset (Fin 4)).card < Z.card := by
      simpa only [Finset.card_univ, Fintype.card_fin] using hZ_gt4
    obtain ⟨z₁, hz₁, z₂, hz₂, hne, hsame⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt_card
        (f := badIdx) (fun z _ => Finset.mem_univ _)
    let j₀ := badIdx z₁
    have hj1 : j₀ = (hex_bad z₁ hz₁).choose := by simp only [j₀, badIdx, hz₁, ↓reduceDIte]
    have hj2 : j₀ = (hex_bad z₂ hz₂).choose := by
      dsimp only [j₀]
      rw [hsame]
      simp only [badIdx, hz₂, ↓reduceDIte]
    obtain ⟨v₁', hv₁', hagree1⟩ := (hex_bad z₁ hz₁).choose_spec
    obtain ⟨v₂', hv₂', hagree2⟩ := (hex_bad z₂ hz₂).choose_spec
    let D' : Finset (Fin 4) := Finset.univ.erase j₀
    obtain ⟨v₀, hv₀, v₁, hv₁, hD'⟩ :=
      solve_line_two_points hne hv₁' hv₂' (D' := D')
        (fun j hj => hagree1 j (by rw [← hj1]; exact (Finset.mem_erase.mp hj).1))
        (fun j hj => hagree2 j (by rw [← hj2]; exact (Finset.mem_erase.mp hj).1))
    refine ⟨D', v₀, hv₀, v₁, hv₁, ?_, hD'⟩
    have hcard : D'.card = 3 := by
      simp only [D', Finset.card_erase_of_mem (Finset.mem_univ j₀), Finset.card_univ,
        Fintype.card_fin]
    change 4 - 1 ≤ D'.card
    omega
  · -- Round 1: `N = 2`, radius `2 / 4 = 0`, `2 < Z.card`.
    have hZ_gt2 : 2 < Z.card := hZ_gt
    obtain ⟨z₁, hz₁, z₂, hz₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < Z.card)
    obtain ⟨v₁', hv₁', hd₁⟩ := hZ_close z₁ hz₁
    obtain ⟨v₂', hv₂', hd₂⟩ := hZ_close z₂ hz₂
    have heq₁ : u₀ + z₁ • u₁ = v₁' := hammingDist_eq_zero.mp (Nat.eq_zero_of_le_zero hd₁)
    have heq₂ : u₀ + z₂ • u₁ = v₂' := hammingDist_eq_zero.mp (Nat.eq_zero_of_le_zero hd₂)
    obtain ⟨v₀, hv₀, v₁, hv₁, hD'⟩ :=
      solve_line_two_points hne hv₁' hv₂' (D' := Finset.univ)
        (fun j _ => congrFun heq₁ j) (fun j _ => congrFun heq₂ j)
    refine ⟨Finset.univ, v₀, hv₀, v₁, hv₁, ?_, hD'⟩
    simp only [Finset.card_univ, Fintype.card_fin]
    change 2 - 0 ≤ 2
    omega

/-! ### Part 5: Unconditional Quantitative BCS-FRI ROM Soundness `< 1 / 3` & Cheating Prover -/

private theorem fri257_rbrError_eq :
    friRBRError params257 2 (2 ^ (params257.d - 1)) =
      ((15625 : ℝ≥0∞) / (262144 : ℝ≥0∞)) := by
  have hle_nn : (4 / 257 : ℝ≥0) ≤ 15625 / 262144 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    norm_num
  have hle : (4 : ℝ≥0∞) / 257 ≤ 15625 / 262144 := by
    simpa only [ENNReal.coe_div (by norm_num : (257 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (262144 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using
      ENNReal.coe_le_coe.mpr hle_nn
  have hpow : (((5 : ℝ≥0∞) / (8 : ℝ≥0∞)) ^ 6) = (15625 : ℝ≥0∞) / (262144 : ℝ≥0∞) := by
    have hnn : ((5 / 8 : ℝ≥0) ^ 6) = 15625 / 262144 := by
      rw [← NNReal.coe_inj]
      push_cast
      norm_num
    simpa only [ENNReal.coe_pow, ENNReal.coe_div (by norm_num : (8 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (262144 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using
      congrArg ENNReal.ofNNReal hnn
  have hcard : (Fintype.card (ZMod 257) : ℝ≥0∞) = 257 := by
    simp only [ZMod.card, Nat.cast_ofNat]
  simp only [friRBRError, params257, hcard,
    (by norm_num : ((2 ^ (3 - 1) : ℕ) : ℝ≥0∞) = 4),
    (by norm_num : ((2 ^ 3 - 2 - 1 : ℕ) : ℝ≥0∞) = 5),
    (by norm_num : (2 : ℝ≥0∞) ^ 3 = 8), hpow]
  exact max_eq_right hle

private theorem card_friChal257 :
    (Fintype.card (FRIChal (ZMod 257) params257.d params257.q) : ℝ≥0∞) = 67371008 := by
  rw [card_friChal, ZMod.card]
  norm_num [params257]

private theorem fri257_universal_rhs_lt_one_third :
    ((2 + (params257.m + 1) : ℕ) : ℝ≥0∞) *
        (friRBRError params257 2 (2 ^ (params257.d - 1)) +
          ((2 + (params257.m + 1) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / Fintype.card (FRIChal (ZMod 257) params257.d params257.q))) +
      ((1000 : ℕ) : ℝ≥0∞) *
        (((3 * 1000 + (params257.m + 1) * (2 + (params257.m + 1)) : ℕ) : ℝ≥0∞) *
          ((1 : ℝ≥0∞) / 2 ^ 32)) < 1 / 3 := by
  rw [fri257_rbrError_eq, card_friChal257]
  have hnn :
      (5 * (15625 / 262144 + 5 * (1 / 67371008)) +
        1000 * (3015 * (1 / 4294967296)) : ℝ≥0) < 1 / 3 := by
    rw [← NNReal.coe_lt_coe]
    push_cast
    norm_num
  have hcast := ENNReal.coe_lt_coe.mpr hnn
  simp only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_one,
    ENNReal.coe_div (by norm_num : (262144 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (67371008 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (4294967296 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (3 : ℝ≥0) ≠ 0)] at hcast
  simpa only [params257,
    (by norm_num : ((2 + (2 + 1) : ℕ) : ℝ≥0∞) = 5),
    (by norm_num : ((1000 : ℕ) : ℝ≥0∞) = 1000),
    (by norm_num : ((3 * 1000 + (2 + 1) * (2 + (2 + 1)) : ℕ) : ℝ≥0∞) = 3015),
    (by norm_num : (2 : ℝ≥0∞) ^ 32 = 4294967296)] using hcast

/-- **Unconditional quantitative BCS-FRI ROM soundness (`< 1 / 3 < 1`)**: for every adaptive
prover `P` making at most `2` Fiat–Shamir queries and whole-game `1000` Merkle queries in the
soundness game over `ZMod 257` with digest length `σ = 32`, the adaptive soundness error against
`params257.proximityLang 2` is strictly less than `1 / 3`. The whole-game budget `1000` strictly
exceeds the `49 * (3 + 1) = 196` verifier Merkle hash queries required for depth-3 accepting-shaped
proofs, leaving `804` prover Merkle queries. -/
theorem fri257_romSoundness_lt_one_third
    (P : OracleComp (BCSROMSpec (OracleTable 3 (ZMod 257)) (FRIChal (ZMod 257) 3 6))
      (OracleTable 3 (ZMod 257) × BCSProof 3 (ZMod 257)))
    (hFS : IsCostBounded bcsFSCost P 2)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friIOP params257) (encZMod (p := 257)) (params257.proximityLang 2) P)
        1000) :
    bcsSoundnessGame (friIOP params257) (encZMod (p := 257)) (params257.proximityLang 2) P 32
      true < 1 / 3 :=
  lt_of_le_of_lt
    (friBCS_romSoundness_bound_of_uniqueLineGap params257
      (by decide : 2 * 2 + params257.dim 0 ≤ 2 ^ params257.d)
      uniqueLineGap_params257 (leftInverse_decZMod_encZMod 257) 32 hFS hMT)
    fri257_universal_rhs_lt_one_third

/-- Default zero challenge used inside the explicit out-of-order cheating prover. -/
private def zeroChal257 : FRIChal (ZMod 257) 3 6 :=
  ⟨0, fun _ => ⟨0, by decide⟩⟩

/-- Explicit adaptive out-of-order cheating prover (`t_FS = 2`, `t_MT = 2`, `L_path = 3`) attempting
to forge a BCS-FRI proof for the far-from-Reed–Solomon word `farWord`. -/
def friCheater257 :
    OracleComp (BCSROMSpec (OracleTable 3 (ZMod 257)) (FRIChal (ZMod 257) 3 6))
      (OracleTable 3 (ZMod 257) × BCSProof 3 (ZMod 257)) := do
  let d₀ ← query (spec := BCSROMSpec (OracleTable 3 (ZMod 257)) (FRIChal (ZMod 257) 3 6))
    (.inl [false])
  let c₁ ← query (spec := BCSROMSpec (OracleTable 3 (ZMod 257)) (FRIChal (ZMod 257) 3 6))
    (.inr (farWord, [d₀, d₀], [zeroChal257]))
  let c₀ ← query (spec := BCSROMSpec (OracleTable 3 (ZMod 257)) (FRIChal (ZMod 257) 3 6))
    (.inr (farWord, [d₀], []))
  let sib ← query (spec := BCSROMSpec (OracleTable 3 (ZMod 257)) (FRIChal (ZMod 257) 3 6))
    (.inl [decide (c₀.foldScalar = c₁.foldScalar)])
  return (farWord,
    { roots := fun _ => d₀
      openings := List.replicate params257.proofOracleQueries ⟨0, [sib, sib, sib]⟩ })

theorem isCostBounded_FS_friCheater257 :
    IsCostBounded bcsFSCost friCheater257 2 :=
  IsCostBounded.liftBind (cost := bcsFSCost) (Sum.inl [false]) _ 2 fun d₀ =>
    IsCostBounded.liftBind (cost := bcsFSCost)
        (Sum.inr (farWord, [d₀, d₀], [zeroChal257])) _ 1 fun (c₁ : FRIChal (ZMod 257) 3 6) =>
      IsCostBounded.liftBind (cost := bcsFSCost)
          (Sum.inr (farWord, [d₀], [])) _ 0 fun (c₀ : FRIChal (ZMod 257) 3 6) =>
        IsCostBounded.liftBind (cost := bcsFSCost)
            (Sum.inl [decide (c₀.foldScalar = c₁.foldScalar)]) _ 0 fun _ =>
          IsCostBounded.pure (cost := bcsFSCost) _ 0

theorem isCostBounded_MT_friCheater257 :
    IsCostBounded bcsMTCost friCheater257 2 :=
  IsCostBounded.liftBind (cost := bcsMTCost) (Sum.inl [false]) _ 1 fun d₀ =>
    IsCostBounded.liftBind (cost := bcsMTCost)
        (Sum.inr (farWord, [d₀, d₀], [zeroChal257])) _ 1 fun (c₁ : FRIChal (ZMod 257) 3 6) =>
      IsCostBounded.liftBind (cost := bcsMTCost)
          (Sum.inr (farWord, [d₀], [])) _ 1 fun (c₀ : FRIChal (ZMod 257) 3 6) =>
        IsCostBounded.liftBind (cost := bcsMTCost)
            (Sum.inl [decide (c₀.foldScalar = c₁.foldScalar)]) _ 0 fun _ =>
          IsCostBounded.pure (cost := bcsMTCost) _ 0

theorem friCheater257_openings_le
    (x : OracleTable 3 (ZMod 257)) (prf : BCSProof 3 (ZMod 257))
    (hmem : (x, prf) ∈ friCheater257.support) :
    ∀ op ∈ prf.openings, op.path.length ≤ 3 := by
  simp only [friCheater257, mem_supportWith_bind_iff, supportWith_query, Set.mem_univ,
    true_and, supportWith_pure, Set.mem_singleton_iff] at hmem
  obtain ⟨d₀, c₁, c₀, sib, h⟩ := hmem
  cases h
  intro op hop
  rw [(List.mem_replicate.mp hop).2]
  simp only [List.length_cons, List.length_nil, le_refl]

-- Direct check of the FRI verifier's Merkle query budget on any proof in `friCheater257.support`.
example (x : OracleTable 3 (ZMod 257)) (prf : BCSProof 3 (ZMod 257))
    (hmem : (x, prf) ∈ friCheater257.support) :
    IsCostBounded bcsMTCost (bcsVerifyROM (friIOP params257) (encZMod (p := 257)) x prf)
      (params257.proofOracleQueries * (3 + 1)) :=
  isCostBounded_bcsMTCost_friVerifyROM params257 (encZMod (p := 257)) x prf
    (friCheater257_openings_le x prf hmem)

-- Direct witness that `fri257_romSoundness_lt_one_third` admits accepting-shaped proofs (49 depth-3
-- openings costing 196 verifier Merkle queries plus prover queries `2 + 196 = 198 ≤ 1000`).
example :
    bcsSoundnessGame (friIOP params257) (encZMod (p := 257)) (params257.proximityLang 2)
      friCheater257 32 true < 1 / 3 :=
  fri257_romSoundness_lt_one_third friCheater257 isCostBounded_FS_friCheater257
    ((isCostBounded_bcsMTCost_bcsSoundnessProg (friIOP params257) (encZMod (p := 257))
      (params257.proximityLang 2) isCostBounded_MT_friCheater257 fun x prf hmem =>
        isCostBounded_bcsMTCost_friVerifyROM params257 (encZMod (p := 257)) x prf
          (friCheater257_openings_le x prf hmem)).mono
      (by decide : 2 + params257.proofOracleQueries * (3 + 1) ≤ 1000))

private theorem fri257_cheater_rhs_lt_half :
    ((2 + (params257.m + 1) : ℕ) : ℝ≥0∞) *
        (friRBRError params257 2 (2 ^ (params257.d - 1)) +
          ((2 + (params257.m + 1) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / Fintype.card (FRIChal (ZMod 257) params257.d params257.q))) +
      ((2 + params257.proofOracleQueries * (3 + 1) : ℕ) : ℝ≥0∞) *
        (((3 * (2 + params257.proofOracleQueries * (3 + 1)) +
            (params257.m + 1) * (2 + (params257.m + 1)) : ℕ) : ℝ≥0∞) *
          ((1 : ℝ≥0∞) / 2 ^ 20)) < 1 / 2 := by
  rw [fri257_rbrError_eq, card_friChal257]
  have hnn :
      (5 * (15625 / 262144 + 5 * (1 / 67371008)) + 198 * (609 * (1 / 1048576)) : ℝ≥0) < 1 / 2 := by
    rw [← NNReal.coe_lt_coe]
    push_cast
    norm_num
  have hcast := ENNReal.coe_lt_coe.mpr hnn
  simp only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_one,
    ENNReal.coe_div (by norm_num : (262144 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (67371008 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (1048576 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0)] at hcast
  simpa only [params257, FRIParams.proofOracleQueries,
    (by norm_num : ((2 + (2 + 1) : ℕ) : ℝ≥0∞) = 5),
    (by norm_num : ((2 + (1 + 6 * (3 * 2 + 2)) * (3 + 1) : ℕ) : ℝ≥0∞) = 198),
    (by norm_num :
      ((3 * (2 + (1 + 6 * (3 * 2 + 2)) * (3 + 1)) + (2 + 1) * (2 + (2 + 1)) : ℕ) : ℝ≥0∞) = 609),
    (by norm_num : (2 : ℝ≥0∞) ^ 20 = 1048576)] using hcast

/-- End-to-end concrete adaptive BCS-FRI ROM soundness bound (`< 1 / 2 < 1`) for the explicit
out-of-order cheating prover `friCheater257` at digest length `σ = 20`, discharging both prover
and verifier Merkle query budgets via
`friBCS_romSoundness_bound_of_prover_verifier_of_weightedLineGap`. -/
theorem friCheater257_romSoundness_lt_half :
    bcsSoundnessGame (friIOP params257) (encZMod (p := 257)) (params257.proximityLang 2)
      friCheater257 20 true < 1 / 2 :=
  lt_of_le_of_lt
    (friBCS_romSoundness_bound_of_prover_verifier_of_weightedLineGap params257
      (weightedLineGapBound_of_uniqueLineGap params257
        (by decide : 2 * 2 + params257.dim 0 ≤ 2 ^ params257.d)
        uniqueLineGap_params257)
      (leftInverse_decZMod_encZMod 257) 20 isCostBounded_MT_friCheater257
      isCostBounded_FS_friCheater257 friCheater257_openings_le)
    fri257_cheater_rhs_lt_half

/-! ### Part 5: Per-Round Shrinking Budgets, `friCommitGame`, and `iopInteractiveGame` -/

-- Exact geometric domain-size sum across the 2 folding rounds of `params257`: `4 + 2 = 6 < 2 * 4`.
example : (∑ i : Fin params257.m, 2 ^ (params257.d - (i.val + 1))) = 6 :=
  params257.sum_domainSize_succ

example (r : ℕ) (hr : r ≤ params257.m) : params257.dim r ≤ 2 ^ (params257.d - r) :=
  params257.dim_le_domainSize hr

/-- Honest causal IOP prover for `honestWord` accepts with probability `1` (`PMF.pure true`) in
`iopInteractiveGame`. -/
theorem honestCausal257_interactiveGame_eq_pure_true :
    iopInteractiveGame (friIOP params257) honestWord
      (InteractiveIOPProver.ofCausal fun j prev =>
        (friIOP params257).proveRound j honestWord () prev) =
      PMF.pure true := by
  refine (iopInteractiveGame_ofCausal_eq (friIOP params257) honestWord _).trans ?_
  have hacc :
      (fun chals : Fin (params257.m + 1) → FRIChal (ZMod 257) params257.d params257.q =>
        iopVerify (friIOP params257) honestWord chals
          (fun j => (friIOP params257).proveRound j honestWord ()
            fun i => chals ⟨i.val, lt_trans i.isLt j.isLt⟩)) =
      Function.const _ true := by
    funext chals
    exact friIOP_complete params257 honestWord () honestWord_mem_initialCode chals
  rw [hacc, PMF.map_const]

private theorem sum_uniqueRoundEscape_257 :
    (∑ i : Fin params257.m,
      ((2 ^ (params257.d - (i.val + 1)) : ℕ) : ℝ≥0∞) /
        (Fintype.card (ZMod 257) : ℝ≥0∞)) = (6 : ℝ≥0∞) / 257 := by
  simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum]
  rw [params257.sum_domainSize_succ]
  norm_num [ZMod.card, params257]

/-- Shrinking per-round unique-decoding commit-phase bound (`≤ 6 / 257 < 1 / 40`) on `farWord` via
`friCommitGame_le_of_weightedLineGapPerRound` and `weightedLineGapPerRound_of_uniqueLineGap`. -/
theorem fri257_commitGame_lt_one_40th
    (P : InteractiveIOPProver 3 (ZMod 257) (FRIChal (ZMod 257) 3 6)) :
    friCommitGame params257 (2 ^ params257.d - 2 - 1) farWord P true < 1 / 40 := by
  refine lt_of_le_of_lt
    (friCommitGame_le_of_weightedLineGapPerRound params257
      (weightedLineGapPerRound_of_uniqueLineGap params257
        (by decide : 2 * 2 + params257.dim 0 ≤ 2 ^ params257.d) uniqueLineGap_params257)
      farWord_not_mem_proximityLang P) ?_
  rw [sum_uniqueRoundEscape_257]
  have hlt : (6 / 257 : ℝ≥0) < 1 / 40 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  simpa only [ENNReal.coe_div (by norm_num : (257 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (40 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat, ENNReal.coe_one] using
    ENNReal.coe_lt_coe.mpr hlt

/-- Summed interactive soundness (`< 1 / 11`, from `6 / 257 + (5 / 8) ^ 6 ≈ 0.08336 < 1 / 11`) for
any adaptive prover `P` on `farWord ∉ params257.proximityLang 2`. -/
theorem fri257_interactiveGame_lt_one_11th
    (P : InteractiveIOPProver 3 (ZMod 257) (FRIChal (ZMod 257) 3 6)) :
    iopInteractiveGame (friIOP params257) farWord P true < 1 / 11 := by
  refine lt_of_le_of_lt
    (friIOP_interactiveGame_le_of_weightedLineGapPerRound params257
      (weightedLineGapPerRound_of_uniqueLineGap params257
        (by decide : 2 * 2 + params257.dim 0 ≤ 2 ^ params257.d) uniqueLineGap_params257)
      farWord_not_mem_proximityLang P) ?_
  rw [friSumError, sum_uniqueRoundEscape_257]
  simp only [params257]
  have hnn : (6 / 257 + (5 / 8) ^ 6 : ℝ≥0) < 1 / 11 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  have hcast := ENNReal.coe_lt_coe.mpr hnn
  simpa only [ENNReal.coe_add, ENNReal.coe_pow,
    ENNReal.coe_div (by norm_num : (257 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (8 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (11 : ℝ≥0) ≠ 0),
    ENNReal.coe_ofNat, ENNReal.coe_one,
    (by norm_num : ((2 ^ 3 - 2 - 1 : ℕ) : ℝ≥0∞) = 5),
    (by norm_num : (2 : ℝ≥0∞) ^ 3 = 8)] using hcast

/-- Explicit causal cheating prover folding `farWord` honestly in each round, certified `< 1 / 11`
in `iopInteractiveGame`. -/
example :
    iopInteractiveGame (friIOP params257) farWord
      (InteractiveIOPProver.ofCausal fun j prev =>
        (friIOP params257).proveRound j farWord () prev) true < 1 / 11 :=
  fri257_interactiveGame_lt_one_11th _

/-- Per-round `sup` BCS-FRI ROM soundness bound
(`friBCS_romSoundness_bound_of_prover_verifier_of_weightedLineEscapePerRound`) instantiated directly
on `friCheater257` (`< 1 / 2` at `σ = 20`). -/
example :
    bcsSoundnessGame (friIOP params257) (encZMod (p := 257)) (params257.proximityLang 2)
      friCheater257 20 true < 1 / 2 := by
  have hgap := weightedLineGapPerRound_of_uniqueLineGap params257
    (by decide : 2 * 2 + params257.dim 0 ≤ 2 ^ params257.d) uniqueLineGap_params257
  have hesc := (weightedLineEscapePerRound_of_gapPerRound params257 hgap).mono
    fun i => ENNReal.div_le_div_right
      (Nat.cast_le.mpr (Nat.pow_le_pow_right (by omega)
        (Nat.sub_le_sub_left (Nat.succ_le_succ (Nat.zero_le _)) _))) _
  refine lt_of_le_of_lt
    (friBCS_romSoundness_bound_of_prover_verifier_of_weightedLineEscapePerRound params257
      hesc (leftInverse_decZMod_encZMod 257) 20 isCostBounded_MT_friCheater257
      isCostBounded_FS_friCheater257 friCheater257_openings_le) ?_
  refine lt_of_le_of_lt ?_ fri257_cheater_rhs_lt_half
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (add_le_add (friSupRBRError_const_le_friRBRError params257 2 (2 ^ (params257.d - 1))) le_rfl)
      zero_le)
    le_rfl

end CslibFrontierTests.Crypto.FRI
