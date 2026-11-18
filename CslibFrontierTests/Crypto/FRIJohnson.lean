/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module

public import CslibFrontier.Crypto.Protocols.FRI.JohnsonSoundness
import CslibFrontier.Languages.Probabilistic.QueryCount.Support
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

/-!
# Concrete Nonvacuous Tests for Unconditional Unique & Johnson-Bound FRI / BCS-FRI ROM Soundness

Exercises every public declaration of `CslibFrontier.Crypto.Protocols.FRI.JohnsonSoundness` from an
ordinary `module` client (no `import all`, zero gap-assumption premises) across four prime fields:

1. **Unconditional unique-decoding (`ZMod 257`, `d = 3, m = 2, kFinal = 1, q = 6, e = 2`).**
   Directly instantiates `weightedLineGapPerRound_of_unique`, `weightedLineGapBound_of_unique`,
   `friCommitGame_le_of_unique` (`< 1 / 40`), `friIOP_interactiveGame_le_of_unique` (`< 1 / 11`),
   `friIOP_rbrSound_of_unique`, `friBCS_romSoundness_bound_of_unique` (`< 1 / 3` at `t_FS = 2,
   Q_MT = 1000, σ = 32`, instantiated on an explicit accepting-shaped client of whole-game cost
   `198 ≤ 1000`), and `friBCS_romSoundness_bound_of_prover_verifier_of_unique` (`< 1 / 2` at
   `t_MT = 2, t_FS = 2, L_path = 3, σ = 20`), with zero hand-rolled proximity-gap proof.
2. **Beyond-unique-decoding 3-round FRI (`ZMod 65537`, `d = 4, m = 3, kFinal = 1, q = 7, e = 5`).**
   Certifies `2 * 5 + 8 > 16` (strictly beyond unique decoding), exhibits a far word `X ^ 8` outside
   `params65537.proximityLang 5`, discharges `weightedLineGapPerRound_of_johnson_discrete` and
   `weightedLineGapBound_of_johnson_discrete` with exact `johnsonCurveBound` budgets
   `(2610, 2204, 85)` (whose sum `4899` beats uniform `3 * 2610 = 7830`, certifying
   `friCommitGame < 2 / 25` and `iopInteractiveGame < 1 / 8`), and proves adaptive BCS-FRI ROM
   soundness strictly `< 1 / 4` (`t_FS = 2, Q_MT = 1000, σ = 32`).
3. **Beyond-Sudan (`m = 2` required) 2-round FRI (`ZMod 998244353`, `d = 4, m = 2, kFinal = 1,
   q = 6, e = 8`).** Certifies `δ = 1 / 2 = 1 - √(1 / 4)` strictly beyond both unique decoding and
   Sudan `m = 1` in round 1, exhibits a far word `X ^ 4` outside `params998.proximityLang 8`,
   discharges `weightedLineGapPerRound_of_johnson_discrete` with `(mRound, DRound) =`
   `[(1, 3), (2, 3)]` and exact `johnsonCurveBound` budgets `(21270, 16065)` (`iopInteractiveGame <
   1 / 140`), and proves adaptive BCS-FRI ROM soundness strictly `< 1 / 25`.
4. **Closed-form asymptotic Johnson FRI over the Goldilocks field (`ZMod (2 ^ 64 - 2 ^ 32 + 1)`,
   `d = 5, m = 2, kFinal = 1, q = 6, e = 17, mJ = 2`).** Certifies `2 * 17 + 4 > 32` and
   `17 / 32 ≤ 1 - √(1 / 8) - √(1 / 8) / 4`, exhibits a far word `X ^ 4` outside
   `paramsGoldilocks.proximityLang 17` alongside honest completeness, verifies geometric halving of
   `friJohnsonRoundBound` (`5374771200, 2687385600`), and directly exercises
   `weightedLineGapPerRound_of_johnson`, `weightedLineGapBound_of_johnson`,
   `friCommitGame_le_of_johnson` (`< 1 / 10 ^ 9`), `friIOP_interactiveGame_le_of_johnson`
   (`< 1 / 140` on universal, randomized transcript-ignoring, and prefix-dependent adaptive
   randomized provers), `friIOP_rbrSound_of_johnson`, `friBCS_romSoundness_bound_of_johnson`
   (`< 1 / 25`), and `friBCS_romSoundness_bound_of_prover_verifier_of_johnson` (`< 1 / 3`).
-/

-- Exports the primitive-root and monomial far-word helpers shared with
-- `CslibFrontierTests/Crypto/FRIBatchSoundness.lean`.

namespace CslibFrontierTests.Crypto.FRIJohnson

open scoped BigOperators NNReal ENNReal
open Polynomial
open Cslib Cslib.Code Cslib.OracleComp Cslib.Probability
open Cslib.Crypto.Protocols.BCS Cslib.Crypto.Protocols.FRI

/-! ### Reusable Primality, Root-of-Unity, and Far-Word Helpers -/

section Helpers

/-- Fuel-bounded modular binary exponentiation for fast kernel reduction in `ZMod p`. -/
private def modPowAux (p : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, acc, _ => acc % p
  | fuel + 1, base, acc, e =>
    if e = 0 then acc % p
    else
      let acc' := if e % 2 = 1 then (acc * base) % p else acc % p
      modPowAux p fuel ((base * base) % p) acc' (e / 2)

private theorem modPowAux_zmod (p : ℕ) :
    ∀ fuel base acc e : ℕ, e < 2 ^ fuel →
      (modPowAux p fuel base acc e : ZMod p) = (acc : ZMod p) * (base : ZMod p) ^ e
  | 0, base, acc, e, he => by
    have he0 : e = 0 := by omega
    subst he0
    simp only [modPowAux, ZMod.natCast_mod, pow_zero, mul_one]
  | fuel + 1, base, acc, e, he => by
    unfold modPowAux
    split_ifs with h0 hodd
    · subst h0
      simp only [ZMod.natCast_mod, pow_zero, mul_one]
    · have hhalf : e / 2 < 2 ^ fuel := by omega
      rw [modPowAux_zmod p fuel ((base * base) % p) ((acc * base) % p) (e / 2) hhalf]
      simp only [ZMod.natCast_mod, Nat.cast_mul]
      have hdecomp : e = 2 * (e / 2) + 1 := by omega
      conv_rhs => rw [hdecomp]
      rw [pow_succ, pow_mul, sq]
      ring
    · have hhalf : e / 2 < 2 ^ fuel := by omega
      rw [modPowAux_zmod p fuel ((base * base) % p) (acc % p) (e / 2) hhalf]
      simp only [ZMod.natCast_mod, Nat.cast_mul]
      have hdecomp : e = 2 * (e / 2) := by omega
      conv_rhs => rw [hdecomp]
      rw [pow_mul, sq]

private theorem zmod_pow_eq_modPowAux (p fuel a e : ℕ) (he : e < 2 ^ fuel) :
    (a : ZMod p) ^ e = (modPowAux p fuel a 1 e : ZMod p) := by
  rw [modPowAux_zmod p fuel a 1 e he, Nat.cast_one, one_mul]

/-- Iterated modular squaring `a ^ (2 ^ k) mod p` in `k` steps. -/
private def modSq (p : ℕ) : ℕ → ℕ → ℕ
  | 0, a => a % p
  | k + 1, a => modSq p k ((a * a) % p)

private theorem modSq_zmod (p : ℕ) :
    ∀ k a : ℕ, (modSq p k a : ZMod p) = (a : ZMod p) ^ (2 ^ k)
  | 0, a => by simp only [modSq, ZMod.natCast_mod, pow_zero, pow_one]
  | k + 1, a => by
    rw [modSq, modSq_zmod p k ((a * a) % p)]
    simp only [ZMod.natCast_mod, Nat.cast_mul]
    rw [pow_succ', pow_mul, sq]

/-- 64-bit modular exponentiation split into four 16-bit chunks (each ≤ 16 kernel steps) given
pre-verified bases `b16 = a ^ 2^16`, `b32 = a ^ 2^32`, `b48 = a ^ 2^48` in `ZMod p`. -/
private theorem zmod_pow_chunks16 {p a b16 b32 b48 e : ℕ}
    (hb16 : (a : ZMod p) ^ (2 ^ 16) = (b16 : ZMod p))
    (hb32 : (a : ZMod p) ^ (2 ^ 32) = (b32 : ZMod p))
    (hb48 : (a : ZMod p) ^ (2 ^ 48) = (b48 : ZMod p))
    (he : e < 2 ^ 64) :
    (a : ZMod p) ^ e =
      (((modPowAux p 16 b48 1 (e / 2 ^ 48) *
          modPowAux p 16 b32 1 ((e / 2 ^ 32) % 2 ^ 16)) % p *
        ((modPowAux p 16 b16 1 ((e / 2 ^ 16) % 2 ^ 16) *
          modPowAux p 16 a 1 (e % 2 ^ 16)) % p)) % p : ZMod p) := by
  have h3 : e / 2 ^ 48 < 2 ^ 16 := by omega
  have h2 : (e / 2 ^ 32) % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by omega)
  have h1 : (e / 2 ^ 16) % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by omega)
  have h0 : e % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by omega)
  simp only [ZMod.natCast_mod, Nat.cast_mul, ← zmod_pow_eq_modPowAux p 16 _ _ h3,
    ← zmod_pow_eq_modPowAux p 16 _ _ h2, ← zmod_pow_eq_modPowAux p 16 _ _ h1,
    ← zmod_pow_eq_modPowAux p 16 _ _ h0, ← hb48, ← hb32, ← hb16, ← pow_mul, ← pow_add]
  congr 1
  omega

/-- Over any field of characteristic `≠ 2`, `ω ^ (2 ^ (d - 1)) = -1` implies `ω` is a primitive
`2 ^ d`-th root of unity. -/
public theorem isPrimitiveRoot_two_pow_of_neg_one {F : Type*} [Field F]
    {ω : F} {d : ℕ} (hd : 1 ≤ d) (h2 : (2 : F) ≠ 0) (hneg : ω ^ (2 ^ (d - 1)) = -1) :
    IsPrimitiveRoot ω (2 ^ d) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : d - 1 + 1 = d := Nat.sub_add_cancel hd
  have hpow : ω ^ (2 ^ d) = 1 := by
    rw [← hsub, pow_succ, pow_mul, hneg, neg_one_sq]
  have hnot : ¬ ω ^ (2 ^ (d - 1)) = 1 := by
    rw [hneg]
    intro h1
    apply h2
    have hzero : (1 : F) + 1 = 0 := by
      calc (1 : F) + 1 = 1 + (-1) := congrArg (1 + ·) h1.symm
        _ = 0 := add_neg_cancel 1
    simpa only [one_add_one_eq_two] using hzero
  have hord : orderOf ω = 2 ^ d := by
    simpa only [hsub] using orderOf_eq_prime_pow (p := 2) (n := d - 1) hnot (by rwa [hsub])
  refine IsPrimitiveRoot.mk hpow fun l hl => ?_
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one hl

private theorem card_filter_congr_decidable {α : Type*} (s : Finset α) (p : α → Prop)
    (h₁ h₂ : DecidablePred p) :
    (@Finset.filter α p h₁ s).card = (@Finset.filter α p h₂ s).card :=
  congrArg (fun h => (@Finset.filter α p h s).card) (Subsingleton.elim h₁ h₂)

/-- Evaluating `X ^ (params.dim 0)` on the initial coset `L_0` yields a word at Hamming distance at
least `2 ^ d - params.dim 0` from every codeword in `params.initialCode`, hence outside
`params.proximityLang e` whenever `e + params.dim 0 < 2 ^ d`. -/
public theorem monomial_far_not_mem_proximityLang {F : Type} [Field F] [DecidableEq F]
    (params : FRIParams F) {e : ℕ} (hgap : e + params.dim 0 < 2 ^ params.d) :
    (fun idx : Fin (2 ^ params.d) => (params.eval 0 idx) ^ params.dim 0) ∉
      params.proximityLang e := by
  classical
  rintro ⟨c, hc_rs, hdist⟩
  obtain ⟨p, hp_deg, hpeq⟩ := mem_reedSolomon.mp hc_rs
  let k0 : ℕ := params.dim 0
  let q : Polynomial F := X ^ k0 - p
  have hp_lt : p.degree < (X ^ k0 : Polynomial F).degree := by
    rw [degree_X_pow]
    exact hp_deg
  have hq_deg : q.degree = (k0 : ℕ) := by
    dsimp only [q]
    rw [degree_sub_eq_left_of_degree_lt hp_lt, degree_X_pow]
  have hq_ne : q ≠ 0 := by
    intro h0
    rw [h0, degree_zero] at hq_deg
    exact WithBot.bot_ne_coe hq_deg
  have hq_natDeg : q.natDegree = k0 := natDegree_eq_of_degree_eq_some hq_deg
  let f : OracleTable params.d F := fun idx => (params.eval 0 idx) ^ k0
  let S_eq : Finset (Fin (2 ^ params.d)) :=
    Finset.univ.filter (fun j : Fin (2 ^ params.d) => f j = c j)
  have hα_inj : Function.Injective (params.eval 0) :=
    cosetEval_injective params.hg params.hω (Nat.zero_le _)
  have himg_sub : S_eq.image (params.eval 0) ⊆ q.roots.toFinset := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hEq : f j = c j := (Finset.mem_filter.mp hj).2
    have hroot : q.eval (params.eval 0 j) = 0 := by
      have hcval : c j = p.eval (params.eval 0 j) := (congrFun hpeq j).symm
      dsimp only [q]
      rw [eval_sub, eval_pow, eval_X, ← hcval]
      exact sub_eq_zero.mpr hEq
    exact Multiset.mem_toFinset.mpr ((mem_roots hq_ne).mpr hroot)
  have hS_le : S_eq.card ≤ k0 := by
    calc S_eq.card
        = (S_eq.image (params.eval 0)).card := (Finset.card_image_of_injective S_eq hα_inj).symm
      _ ≤ q.roots.toFinset.card := Finset.card_le_card himg_sub
      _ ≤ q.roots.card := Multiset.toFinset_card_le q.roots
      _ ≤ q.natDegree := card_roots' q
      _ = k0 := hq_natDeg
  have hpart : S_eq.card + hammingDist f c = 2 ^ params.d := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (2 ^ params.d)))) (fun j => f j = c j)
    have hcard : (Finset.univ : Finset (Fin (2 ^ params.d))).card = 2 ^ params.d := by
      rw [Finset.card_univ, Fintype.card_fin]
    have hfilt : (Finset.univ.filter (fun j : Fin (2 ^ params.d) => ¬ f j = c j)).card =
        hammingDist f c :=
      card_filter_congr_decidable _ _ _ _
    rw [hcard, hfilt] at h
    exact h
  have hdist' : hammingDist f c ≤ e := hdist
  omega

/-- The constant-zero word lies in `params.initialCode` for every `FRIParams F`. -/
private theorem zero_mem_initialCode {F : Type} [Field F] (params : FRIParams F) :
    (fun _ : Fin (2 ^ params.d) => (0 : F)) ∈ params.initialCode := by
  refine mem_reedSolomon.mpr ⟨0, ?_, ?_⟩
  · rw [degree_zero]
    exact WithBot.bot_lt_coe _
  · ext _
    exact eval_zero

/-- Parametric adaptive out-of-order accepting-shaped cheating prover (`t_FS = 2`, `t_MT = 2`,
`params.proofOracleQueries` depth-`params.d` openings) for any `FRIParams F`. -/
def mkAcceptingCheater {F : Type} [Field F] [DecidableEq F] (params : FRIParams F)
    (farWord : OracleTable params.d F) :
    OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F) := do
  let zeroChal : FRIChal F params.d params.q := ⟨0, fun _ => ⟨0, Nat.two_pow_pos _⟩⟩
  let d₀ ← query
    (spec := BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
    (.inl [false])
  let c₁ ← query
    (spec := BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
    (.inr (farWord, [d₀, d₀], [zeroChal]))
  let c₀ ← query
    (spec := BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
    (.inr (farWord, [d₀], []))
  let sib ← query
    (spec := BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
    (.inl [decide (c₀.foldScalar = c₁.foldScalar)])
  return (farWord,
    { roots := fun _ => d₀
      openings := List.replicate params.proofOracleQueries ⟨0, List.replicate params.d sib⟩ })

theorem isCostBounded_FS_mkAcceptingCheater {F : Type} [Field F] [DecidableEq F]
    (params : FRIParams F) (farWord : OracleTable params.d F) :
    IsCostBounded bcsFSCost (mkAcceptingCheater params farWord) 2 :=
  IsCostBounded.liftBind (cost := bcsFSCost) (Sum.inl [false]) _ 2 fun d₀ =>
    IsCostBounded.liftBind (cost := bcsFSCost)
        (Sum.inr (farWord, [d₀, d₀],
          [(⟨0, fun _ => ⟨0, Nat.two_pow_pos _⟩⟩ : FRIChal F params.d params.q)])) _ 1
        fun (c₁ : FRIChal F params.d params.q) =>
      IsCostBounded.liftBind (cost := bcsFSCost)
          (Sum.inr (farWord, [d₀], [])) _ 0
          fun (c₀ : FRIChal F params.d params.q) =>
        IsCostBounded.liftBind (cost := bcsFSCost)
            (Sum.inl [decide (c₀.foldScalar = c₁.foldScalar)]) _ 0 fun _ =>
          IsCostBounded.pure (cost := bcsFSCost) _ 0

theorem isCostBounded_MT_mkAcceptingCheater {F : Type} [Field F] [DecidableEq F]
    (params : FRIParams F) (farWord : OracleTable params.d F) :
    IsCostBounded bcsMTCost (mkAcceptingCheater params farWord) 2 :=
  IsCostBounded.liftBind (cost := bcsMTCost) (Sum.inl [false]) _ 1 fun d₀ =>
    IsCostBounded.liftBind (cost := bcsMTCost)
        (Sum.inr (farWord, [d₀, d₀],
          [(⟨0, fun _ => ⟨0, Nat.two_pow_pos _⟩⟩ : FRIChal F params.d params.q)])) _ 1
        fun (c₁ : FRIChal F params.d params.q) =>
      IsCostBounded.liftBind (cost := bcsMTCost)
          (Sum.inr (farWord, [d₀], [])) _ 1
          fun (c₀ : FRIChal F params.d params.q) =>
        IsCostBounded.liftBind (cost := bcsMTCost)
            (Sum.inl [decide (c₀.foldScalar = c₁.foldScalar)]) _ 0 fun _ =>
          IsCostBounded.pure (cost := bcsMTCost) _ 0

theorem mkAcceptingCheater_openings_le {F : Type} [Field F] [DecidableEq F]
    (params : FRIParams F) (farWord : OracleTable params.d F)
    (x : OracleTable params.d F) (prf : BCSProof (params.m + 1) F)
    (hmem : (x, prf) ∈ (mkAcceptingCheater params farWord).support) :
    ∀ op ∈ prf.openings, op.path.length ≤ params.d := by
  simp only [mkAcceptingCheater, mem_supportWith_bind_iff, supportWith_query, Set.mem_univ,
    true_and, supportWith_pure, Set.mem_singleton_iff] at hmem
  obtain ⟨d₀, c₁, c₀, sib, h⟩ := hmem
  cases h
  intro op hop
  rw [(List.mem_replicate.mp hop).2, List.length_replicate]

theorem isCostBounded_soundnessProg_mkAcceptingCheater {F : Type} [Field F] [DecidableEq F]
    (params : FRIParams F) (encSym : F → List Bool) (e : ℕ)
    (farWord : OracleTable params.d F) {Q_MT : ℕ}
    (hQ : 2 + params.proofOracleQueries * (params.d + 1) ≤ Q_MT) :
    IsCostBounded bcsMTCost
      (bcsSoundnessProg (friIOP params) encSym (params.proximityLang e)
        (mkAcceptingCheater params farWord)) Q_MT :=
  (isCostBounded_bcsMTCost_bcsSoundnessProg (friIOP params) encSym (params.proximityLang e)
    (isCostBounded_MT_mkAcceptingCheater params farWord) fun x prf hmem =>
      isCostBounded_bcsMTCost_friVerifyROM params encSym x prf
        (mkAcceptingCheater_openings_le params farWord x prf hmem)).mono hQ

end Helpers

/-! ### Suite 1: Unconditional Unique-Decoding FRI & BCS-FRI ROM Soundness (`ZMod 257`) -/

section Unique257

instance instPrime257 : Fact (Nat.Prime 257) := ⟨by norm_num⟩

/-- 2-folding-round, rate-`1 / 2`, `q = 6` FRI instance over `ZMod 257`. -/
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
  hω := isPrimitiveRoot_two_pow_of_neg_one (by omega) (by decide) (by decide)

-- Unconditional round-by-round soundness via `friIOP_rbrSound_of_unique` (zero gap premise).
theorem fri257_rbrSound_unconditional :
    IOPRoundByRoundSoundness (friIOP params257) (params257.proximityLang 2)
      (friDoomed params257 (2 ^ params257.d - 2 - 1))
      (friGoodStep params257 (2 ^ params257.d - 2 - 1)) ∧
    ∀ stmt ∉ params257.proximityLang 2, ∀ pref π,
      friDoomed params257 (2 ^ params257.d - 2 - 1) stmt pref →
      (PMF.uniformOfFintype (FRIChal (ZMod 257) params257.d params257.q)).toOuterMeasure
        {c | ¬ friGoodStep params257 (2 ^ params257.d - 2 - 1) stmt pref π c} ≤
      friRBRError params257 2 (2 ^ (params257.d - 1)) :=
  friIOP_rbrSound_of_unique params257 (by decide)

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

/-- **Unconditional unique-decoding BCS-FRI ROM soundness (`< 1 / 3`)** over `ZMod 257`, directly
via `friBCS_romSoundness_bound_of_unique` with zero hand-rolled gap proof (`t_FS = 2, Q_MT = 1000,
σ = 32`, strictly exceeding the `49 * 4 = 196` verifier Merkle hash queries of depth-3 openings and
leaving `804` prover Merkle queries). -/
theorem fri257_unique_romSoundness_lt_one_third
    (P : OracleComp (BCSROMSpec (OracleTable 3 (ZMod 257)) (FRIChal (ZMod 257) 3 6))
      (OracleTable 3 (ZMod 257) × BCSProof 3 (ZMod 257)))
    (hFS : IsCostBounded bcsFSCost P 2)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friIOP params257) (encZMod (p := 257)) (params257.proximityLang 2) P)
        1000) :
    bcsSoundnessGame (friIOP params257) (encZMod (p := 257)) (params257.proximityLang 2) P 32
      true < 1 / 3 := by
  refine lt_of_le_of_lt
    (friBCS_romSoundness_bound_of_unique params257 (by decide)
      (leftInverse_decZMod_encZMod 257) 32 hFS hMT) ?_
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

-- Nonvacuity: `X ^ 4` lies outside `params257.proximityLang 2` (Hamming distance ≥ 4 > 2).
theorem farWord257_not_mem :
    (fun idx : Fin 8 => (params257.eval 0 idx) ^ 4) ∉ params257.proximityLang 2 :=
  monomial_far_not_mem_proximityLang params257 (by decide)

-- Direct instantiation of `fri257_unique_romSoundness_lt_one_third` on an explicit feasible
-- accepting-shaped client (`2 + 49 * 4 = 198 ≤ 1000` whole-game Merkle queries).
example :
    bcsSoundnessGame (friIOP params257) (encZMod (p := 257)) (params257.proximityLang 2)
      (mkAcceptingCheater params257 (fun idx => (params257.eval 0 idx) ^ 4)) 32 true < 1 / 3 :=
  fri257_unique_romSoundness_lt_one_third
    (mkAcceptingCheater params257 (fun idx => (params257.eval 0 idx) ^ 4))
    (isCostBounded_FS_mkAcceptingCheater params257 _)
    (isCostBounded_soundnessProg_mkAcceptingCheater params257 (encZMod (p := 257)) 2 _
      (by decide : 2 + params257.proofOracleQueries * (params257.d + 1) ≤ 1000))

/-- **Unconditional unique-decoding prover/verifier-split BCS-FRI ROM soundness (`< 1 / 2`)** over
`ZMod 257`, directly via `friBCS_romSoundness_bound_of_prover_verifier_of_unique`. -/
theorem fri257_unique_prover_verifier_lt_half
    (P : OracleComp (BCSROMSpec (OracleTable 3 (ZMod 257)) (FRIChal (ZMod 257) 3 6))
      (OracleTable 3 (ZMod 257) × BCSProof 3 (ZMod 257)))
    (hMT : IsCostBounded bcsMTCost P 2)
    (hFS : IsCostBounded bcsFSCost P 2)
    (hops : ∀ x prf, (x, prf) ∈ P.support → ∀ op ∈ prf.openings, op.path.length ≤ 3) :
    bcsSoundnessGame (friIOP params257) (encZMod (p := 257)) (params257.proximityLang 2) P 20
      true < 1 / 2 := by
  refine lt_of_le_of_lt
    (friBCS_romSoundness_bound_of_prover_verifier_of_unique params257 (by decide)
      (leftInverse_decZMod_encZMod 257) 20 hMT hFS hops) ?_
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

-- Direct instantiation of `fri257_unique_prover_verifier_lt_half` on the accepting-shaped client.
example :
    bcsSoundnessGame (friIOP params257) (encZMod (p := 257)) (params257.proximityLang 2)
      (mkAcceptingCheater params257 (fun idx => (params257.eval 0 idx) ^ 4)) 20 true < 1 / 2 :=
  fri257_unique_prover_verifier_lt_half
    (mkAcceptingCheater params257 (fun idx => (params257.eval 0 idx) ^ 4))
    (isCostBounded_MT_mkAcceptingCheater params257 _)
    (isCostBounded_FS_mkAcceptingCheater params257 _)
    (mkAcceptingCheater_openings_le params257 _)

-- Exact geometric unique-decoding commit error identity `∑ (2 ^ (d - (i + 1)) / 257) = ofReal ...`.
example :
    (∑ i : Fin params257.m,
      ((2 ^ (params257.d - (i.val + 1)) : ℕ) : ℝ≥0∞) /
        (Fintype.card (ZMod 257) : ℝ≥0∞)) =
    ENNReal.ofReal (friUniqueCommitError params257) :=
  sum_friUniqueRoundEscape_eq params257

/-- Unconditional shrinking unique-decoding commit-phase bound (`≤ 6 / 257 < 1 / 40`) via
`friCommitGame_le_of_unique`. -/
theorem fri257_commitGame_unique_lt_one_40th
    (P : InteractiveIOPProver 3 (ZMod 257) (FRIChal (ZMod 257) 3 6)) :
    friCommitGame params257 (2 ^ params257.d - 2 - 1)
      (fun idx => (params257.eval 0 idx) ^ 4) P true < 1 / 40 := by
  refine lt_of_le_of_lt
    (friCommitGame_le_of_unique params257 (by decide) farWord257_not_mem P) ?_
  simp only [ZMod.card, params257]
  have hlt : (6 / 257 : ℝ≥0) < 1 / 40 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  simpa only [ENNReal.coe_div (by norm_num : (257 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (40 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat, ENNReal.coe_one,
    (by norm_num : ((2 ^ 3 - 2 ^ (3 - 2) : ℕ) : ℝ≥0∞) = 6),
    (by norm_num : ((257 : ℕ) : ℝ≥0∞) = 257)] using ENNReal.coe_lt_coe.mpr hlt

/-- Unconditional summed interactive soundness (`< 1 / 11`) via
`friIOP_interactiveGame_le_of_unique`. -/
theorem fri257_interactiveGame_unique_lt_one_11th
    (P : InteractiveIOPProver 3 (ZMod 257) (FRIChal (ZMod 257) 3 6)) :
    iopInteractiveGame (friIOP params257)
      (fun idx => (params257.eval 0 idx) ^ 4) P true < 1 / 11 := by
  refine lt_of_le_of_lt
    (friIOP_interactiveGame_le_of_unique params257 (by decide) farWord257_not_mem P) ?_
  simp only [ZMod.card, params257]
  have hlt : (6 / 257 + (5 / 8) ^ 6 : ℝ≥0) < 1 / 11 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_pow,
    ENNReal.coe_div (by norm_num : (257 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (8 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (11 : ℝ≥0) ≠ 0),
    ENNReal.coe_ofNat, ENNReal.coe_one,
    (by norm_num : ((2 ^ 3 - 2 ^ (3 - 2) : ℕ) : ℝ≥0∞) = 6),
    (by norm_num : ((257 : ℕ) : ℝ≥0∞) = 257),
    (by norm_num : ((2 ^ 3 - 2 - 1 : ℕ) : ℝ≥0∞) = 5),
    (by norm_num : (2 : ℝ≥0∞) ^ 3 = 8)] using ENNReal.coe_lt_coe.mpr hlt

end Unique257

/-! ### Suite 2: Beyond-Unique-Decoding 3-Round FRI (`ZMod 65537`, `e = 5 > e_uniq = 4`) -/

section Johnson65537

theorem prime_65537 : Nat.Prime 65537 := by
  refine lucas_primality 65537 (3 : ZMod 65537) ?_ ?_
  · rw [show (3 : ZMod 65537) = ((3 : ℕ) : ZMod 65537) from rfl,
      zmod_pow_eq_modPowAux 65537 17 3 65536 (by omega)]
    decide
  · intro q hq hdvd
    have hpow : q ∣ 2 ^ 16 := hdvd
    have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
      (hq.dvd_of_dvd_pow hpow)
    subst hq2
    rw [show (3 : ZMod 65537) = ((3 : ℕ) : ZMod 65537) from rfl,
      zmod_pow_eq_modPowAux 65537 17 3 (65536 / 2) (by omega)]
    decide

instance instPrime65537 : Fact (Nat.Prime 65537) := ⟨prime_65537⟩

/-- 3-folding-round (`m = 3`, 4 total IOP rounds), depth-4 (`|L_0| = 16`), rate-`1 / 2`
(`kFinal = 1`, `dim 0 = 8`), `q = 7` FRI instance over `ZMod 65537`. -/
def params65537 : FRIParams (ZMod 65537) where
  d := 4
  m := 3
  kFinal := 1
  q := 7
  g := 1
  ω := 4
  hm := by omega
  hkPos := by omega
  hkLe := by omega
  hg := one_ne_zero
  h2 := by decide
  hω := isPrimitiveRoot_two_pow_of_neg_one (by omega) (by decide) (by decide)

-- Radius `e = 5` is strictly beyond unique decoding (`2 * 5 + 8 = 18 > 16`).
theorem params65537_beyond_unique :
    ¬ (2 * 5 + params65537.dim 0 ≤ 2 ^ params65537.d) := by
  decide

-- Nonvacuity: `X ^ 8` lies outside `params65537.proximityLang 5` (Hamming distance ≥ 8 > 5).
theorem farWord65537_not_mem :
    (fun idx : Fin 16 => (params65537.eval 0 idx) ^ 8) ∉ params65537.proximityLang 5 :=
  monomial_far_not_mem_proximityLang params65537 (by decide)

/-- Per-round Guruswami–Sudan multiplicities `(1, 1, 1)` for `params65537` at `e = 5`. -/
private def mRound65537 : Fin 3 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1

/-- Per-round `(1, k_i - 1)`-weighted degrees `(5, 2, 1)` for `params65537` at `e = 5`. -/
private def DRound65537 : Fin 3 → ℕ
  | ⟨0, _⟩ => 5
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 1

/-- Unconditional beyond-unique-decoding `WeightedLineGapBound` for 3-round FRI over `ZMod 65537`
with exact commit budget `2610 = max(2610, 2204, 85)`. -/
theorem weightedLineGapBound_65537 :
    WeightedLineGapBound params65537 (2 ^ params65537.d - 5 - 1) 2610 := by
  refine weightedLineGapBound_of_johnson_discrete params65537 (e := 5) (B_commit := 2610)
    (by decide) mRound65537 DRound65537 ?_ ?_ ?_ ?_ ?_
  · intro i; fin_cases i <;> decide
  · intro i; fin_cases i <;> decide
  · intro i; fin_cases i <;> decide
  · intro i; fin_cases i <;> decide
  · intro i; fin_cases i <;> decide

private theorem fri65537_rbrError_eq :
    friRBRError params65537 5 2610 = ((2610 : ℝ≥0∞) / (65537 : ℝ≥0∞)) := by
  have hle_nn : (78125 / 2097152 : ℝ≥0) ≤ 2610 / 65537 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    norm_num
  have hle : (78125 : ℝ≥0∞) / 2097152 ≤ 2610 / 65537 := by
    simpa only [ENNReal.coe_div (by norm_num : (2097152 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (65537 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using
      ENNReal.coe_le_coe.mpr hle_nn
  have hpow : (((10 : ℝ≥0∞) / (16 : ℝ≥0∞)) ^ 7) = (78125 : ℝ≥0∞) / (2097152 : ℝ≥0∞) := by
    have hnn : ((10 / 16 : ℝ≥0) ^ 7) = 78125 / 2097152 := by
      rw [← NNReal.coe_inj]
      push_cast
      norm_num
    simpa only [ENNReal.coe_pow, ENNReal.coe_div (by norm_num : (16 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (2097152 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using
      congrArg ENNReal.ofNNReal hnn
  have hcard : (Fintype.card (ZMod 65537) : ℝ≥0∞) = 65537 := by
    simp only [ZMod.card, Nat.cast_ofNat]
  simp only [friRBRError, params65537, hcard,
    (by norm_num : ((2610 : ℕ) : ℝ≥0∞) = 2610),
    (by norm_num : ((2 ^ 4 - 5 - 1 : ℕ) : ℝ≥0∞) = 10),
    (by norm_num : (2 : ℝ≥0∞) ^ 4 = 16), hpow]
  exact max_eq_left hle

private theorem card_friChal65537 :
    (Fintype.card (FRIChal (ZMod 65537) params65537.d params65537.q) : ℝ≥0∞) = 17592454479872 := by
  rw [card_friChal, ZMod.card]
  norm_num [params65537]

/-- **Unconditional beyond-unique-decoding 3-round BCS-FRI ROM soundness (`< 1 / 4`)** over
`ZMod 65537` at radius `e = 5 > e_uniq = 4` (`t_FS = 2, Q_MT = 1000, σ = 32`, strictly exceeding
the `78 * 5 = 390` verifier Merkle hash queries of depth-4 openings and leaving `610` prover Merkle
queries). -/
theorem fri65537_johnson_romSoundness_lt_quarter
    (P : OracleComp (BCSROMSpec (OracleTable 4 (ZMod 65537)) (FRIChal (ZMod 65537) 4 7))
      (OracleTable 4 (ZMod 65537) × BCSProof 4 (ZMod 65537)))
    (hFS : IsCostBounded bcsFSCost P 2)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friIOP params65537) (encZMod (p := 65537))
        (params65537.proximityLang 5) P) 1000) :
    bcsSoundnessGame (friIOP params65537) (encZMod (p := 65537)) (params65537.proximityLang 5)
      P 32 true < 1 / 4 := by
  refine lt_of_le_of_lt
    (friBCS_romSoundness_bound_of_weightedLineGap params65537 weightedLineGapBound_65537
      (leftInverse_decZMod_encZMod 65537) 32 hFS hMT) ?_
  rw [fri65537_rbrError_eq, card_friChal65537]
  have hnn :
      (6 * (2610 / 65537 + 6 * (1 / 17592454479872)) +
        1000 * (3024 * (1 / 4294967296)) : ℝ≥0) < 1 / 4 := by
    rw [← NNReal.coe_lt_coe]
    push_cast
    norm_num
  have hcast := ENNReal.coe_lt_coe.mpr hnn
  simp only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_one,
    ENNReal.coe_div (by norm_num : (65537 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (17592454479872 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (4294967296 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0)] at hcast
  simpa only [params65537,
    (by norm_num : ((2 + (3 + 1) : ℕ) : ℝ≥0∞) = 6),
    (by norm_num : ((1000 : ℕ) : ℝ≥0∞) = 1000),
    (by norm_num : ((3 * 1000 + (3 + 1) * (2 + (3 + 1)) : ℕ) : ℝ≥0∞) = 3024),
    (by norm_num : (2 : ℝ≥0∞) ^ 32 = 4294967296)] using hcast

-- Direct instantiation of `fri65537_johnson_romSoundness_lt_quarter` on an explicit feasible
-- accepting-shaped client (`2 + 78 * 5 = 392 ≤ 1000` whole-game Merkle queries).
example :
    bcsSoundnessGame (friIOP params65537) (encZMod (p := 65537)) (params65537.proximityLang 5)
      (mkAcceptingCheater params65537 (fun idx => (params65537.eval 0 idx) ^ 8)) 32 true < 1 / 4 :=
  fri65537_johnson_romSoundness_lt_quarter
    (mkAcceptingCheater params65537 (fun idx => (params65537.eval 0 idx) ^ 8))
    (isCostBounded_FS_mkAcceptingCheater params65537 _)
    (isCostBounded_soundnessProg_mkAcceptingCheater params65537 (encZMod (p := 65537)) 5 _
      (by decide : 2 + params65537.proofOracleQueries * (params65537.d + 1) ≤ 1000))

private theorem sum_johnsonCurveBound_65537 :
    (∑ i : Fin params65537.m,
      ProximityGap.johnsonCurveBound (2 ^ (params65537.d - (i.val + 1))) (mRound65537 i)
        (params65537.dim (i.val + 1) - 1) (DRound65537 i) 1 (2 ^ params65537.d)) = 4899 := by
  decide

/-- Discrete per-round Johnson commit-phase bound (`4899 / 65537 < 2 / 25`, strictly tighter than
uniform `3 * 2610 / 65537 = 7830 / 65537 > 2 / 25`) over `ZMod 65537`. -/
theorem fri65537_commitGame_lt_two_25ths
    (P : InteractiveIOPProver 4 (ZMod 65537) (FRIChal (ZMod 65537) 4 7)) :
    friCommitGame params65537 (2 ^ params65537.d - 5 - 1)
      (fun idx => (params65537.eval 0 idx) ^ 8) P true < 2 / 25 := by
  refine lt_of_le_of_lt
    (friCommitGame_le_of_johnson_discrete params65537 (e := 5) (by decide) mRound65537 DRound65537
      (fun i => by fin_cases i <;> decide)
      (fun i => by fin_cases i <;> decide)
      (fun i => by fin_cases i <;> decide)
      (fun i => by fin_cases i <;> decide)
      farWord65537_not_mem P) ?_
  rw [sum_johnsonCurveBound_65537]
  simp only [ZMod.card]
  have hlt : (4899 / 65537 : ℝ≥0) < 2 / 25 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  simpa only [ENNReal.coe_div (by norm_num : (65537 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (25 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat,
    (by norm_num : ((4899 : ℕ) : ℝ≥0∞) = 4899),
    (by norm_num : ((65537 : ℕ) : ℝ≥0∞) = 65537)] using
    ENNReal.coe_lt_coe.mpr hlt

/-- Discrete per-round Johnson summed interactive soundness (`< 1 / 8`, from
`4899 / 65537 + (10 / 16) ^ 7 ≈ 0.1120 < 1 / 8`) over `ZMod 65537`. -/
theorem fri65537_interactiveGame_lt_eighth
    (P : InteractiveIOPProver 4 (ZMod 65537) (FRIChal (ZMod 65537) 4 7)) :
    iopInteractiveGame (friIOP params65537)
      (fun idx => (params65537.eval 0 idx) ^ 8) P true < 1 / 8 := by
  refine lt_of_le_of_lt
    (friIOP_interactiveGame_le_of_johnson_discrete params65537 (e := 5) (by decide)
      mRound65537 DRound65537
      (fun i => by fin_cases i <;> decide)
      (fun i => by fin_cases i <;> decide)
      (fun i => by fin_cases i <;> decide)
      (fun i => by fin_cases i <;> decide)
      farWord65537_not_mem P) ?_
  rw [sum_johnsonCurveBound_65537]
  simp only [ZMod.card, params65537]
  have hlt : (4899 / 65537 + (10 / 16) ^ 7 : ℝ≥0) < 1 / 8 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_pow,
    ENNReal.coe_div (by norm_num : (65537 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (16 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (8 : ℝ≥0) ≠ 0),
    ENNReal.coe_ofNat, ENNReal.coe_one,
    (by norm_num : ((4899 : ℕ) : ℝ≥0∞) = 4899),
    (by norm_num : ((65537 : ℕ) : ℝ≥0∞) = 65537),
    (by norm_num : ((2 ^ 4 - 5 - 1 : ℕ) : ℝ≥0∞) = 10),
    (by norm_num : (2 : ℝ≥0∞) ^ 4 = 16)] using ENNReal.coe_lt_coe.mpr hlt

end Johnson65537

/-! ### Suite 3: Beyond-Sudan (`m = 2`) 2-Round FRI (`ZMod 998244353`, `e = 8, δ = 1 - √(1/4)`) -/

section Johnson998244353

theorem prime_998244353 : Nat.Prime 998244353 := by
  refine lucas_primality 998244353 (3 : ZMod 998244353) ?_ ?_
  · rw [show (3 : ZMod 998244353) = ((3 : ℕ) : ZMod 998244353) from rfl,
      zmod_pow_eq_modPowAux 998244353 31 3 998244352 (by omega)]
    decide
  · intro q hq hdvd
    have hfac : q ∣ 2 ^ 23 * 7 * 17 := hdvd
    rcases hq.dvd_mul.mp hfac with h1 | h17
    · rcases hq.dvd_mul.mp h1 with h2pow | h7
      · have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
          (hq.dvd_of_dvd_pow h2pow)
        subst hq2
        rw [show (3 : ZMod 998244353) = ((3 : ℕ) : ZMod 998244353) from rfl,
          zmod_pow_eq_modPowAux 998244353 31 3 (998244352 / 2) (by omega)]
        decide
      · have hq7 : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h7
        subst hq7
        rw [show (3 : ZMod 998244353) = ((3 : ℕ) : ZMod 998244353) from rfl,
          zmod_pow_eq_modPowAux 998244353 31 3 (998244352 / 7) (by omega)]
        decide
    · have hq17 : q = 17 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h17
      subst hq17
      rw [show (3 : ZMod 998244353) = ((3 : ℕ) : ZMod 998244353) from rfl,
        zmod_pow_eq_modPowAux 998244353 31 3 (998244352 / 17) (by omega)]
      decide

instance instPrime998244353 : Fact (Nat.Prime 998244353) := ⟨prime_998244353⟩

private theorem omega998_pow_eight : (929031873 : ZMod 998244353) ^ 8 = -1 := by
  rw [show (929031873 : ZMod 998244353) = ((929031873 : ℕ) : ZMod 998244353) from rfl,
    zmod_pow_eq_modPowAux 998244353 4 929031873 8 (by omega)]
  decide

/-- 2-folding-round, depth-4 (`|L_0| = 16`), rate-`1 / 4` (`kFinal = 1`, `dim 0 = 4`), `q = 6`
FRI instance over the NTT prime field `ZMod 998244353`. -/
def params998 : FRIParams (ZMod 998244353) where
  d := 4
  m := 2
  kFinal := 1
  q := 6
  g := 1
  ω := 929031873
  hm := by omega
  hkPos := by omega
  hkLe := by omega
  hg := one_ne_zero
  h2 := by decide
  hω := isPrimitiveRoot_two_pow_of_neg_one (by omega) (by decide) omega998_pow_eight

-- Radius `e = 8` (`δ = 1 / 2 = 1 - √(1 / 4)`) is strictly beyond unique decoding (`20 > 16`).
theorem params998_beyond_unique :
    ¬ (2 * 8 + params998.dim 0 ≤ 2 ^ params998.d) := by
  decide

-- Nonvacuity: `X ^ 4` lies outside `params998.proximityLang 8` (Hamming distance ≥ 12 > 8).
theorem farWord998_not_mem :
    (fun idx : Fin 16 => (params998.eval 0 idx) ^ 4) ∉ params998.proximityLang 8 :=
  monomial_far_not_mem_proximityLang params998 (by decide)

/-- Per-round multiplicities `(1, 2)` for `params998` at `e = 8`: round 1 genuinely requires
Guruswami–Sudan multiplicity `m = 2` (Sudan `m = 1` fails at `N = 4, k = 1, e_1 = 2`). -/
private def mRound998 : Fin 2 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2

/-- Per-round weighted degrees `(3, 3)` for `params998` at `e = 8`. -/
private def DRound998 : Fin 2 → ℕ
  | ⟨0, _⟩ => 3
  | ⟨1, _⟩ => 3

/-- Unconditional beyond-Sudan `WeightedLineGapBound` over `ZMod 998244353` at the exact Johnson
boundary `δ = 1 - √ρ = 1 / 2`, with exact commit budget `21270 = max(21270, 16065)`. -/
theorem weightedLineGapBound_998 :
    WeightedLineGapBound params998 (2 ^ params998.d - 8 - 1) 21270 := by
  refine weightedLineGapBound_of_johnson_discrete params998 (e := 8) (B_commit := 21270)
    (by decide) mRound998 DRound998 ?_ ?_ ?_ ?_ ?_
  · intro i; fin_cases i <;> decide
  · intro i; fin_cases i <;> decide
  · intro i; fin_cases i <;> decide
  · intro i; fin_cases i <;> decide
  · intro i; fin_cases i <;> decide

private theorem fri998_rbrError_eq :
    friRBRError params998 8 21270 = ((117649 : ℝ≥0∞) / (16777216 : ℝ≥0∞)) := by
  have hle_nn : (21270 / 998244353 : ℝ≥0) ≤ 117649 / 16777216 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    norm_num
  have hle : (21270 : ℝ≥0∞) / 998244353 ≤ 117649 / 16777216 := by
    simpa only [ENNReal.coe_div (by norm_num : (998244353 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (16777216 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using
      ENNReal.coe_le_coe.mpr hle_nn
  have hpow : (((7 : ℝ≥0∞) / (16 : ℝ≥0∞)) ^ 6) = (117649 : ℝ≥0∞) / (16777216 : ℝ≥0∞) := by
    have hnn : ((7 / 16 : ℝ≥0) ^ 6) = 117649 / 16777216 := by
      rw [← NNReal.coe_inj]
      push_cast
      norm_num
    simpa only [ENNReal.coe_pow, ENNReal.coe_div (by norm_num : (16 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (16777216 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using
      congrArg ENNReal.ofNNReal hnn
  have hcard : (Fintype.card (ZMod 998244353) : ℝ≥0∞) = 998244353 := by
    simp only [ZMod.card, Nat.cast_ofNat]
  simp only [friRBRError, params998, hcard,
    (by norm_num : ((21270 : ℕ) : ℝ≥0∞) = 21270),
    (by norm_num : ((2 ^ 4 - 8 - 1 : ℕ) : ℝ≥0∞) = 7),
    (by norm_num : (2 : ℝ≥0∞) ^ 4 = 16), hpow]
  exact max_eq_right hle

private theorem card_friChal998 :
    (Fintype.card (FRIChal (ZMod 998244353) params998.d params998.q) : ℝ≥0∞) = 16747761131061248 :=
  by
  rw [card_friChal, ZMod.card]
  norm_num [params998]

/-- **Unconditional beyond-Sudan (`m = 2`) 2-round BCS-FRI ROM soundness (`< 1 / 25`)** over
`ZMod 998244353` at radius `e = 8` (`δ = 1 / 2 = 1 - √(1 / 4)`, `t_FS = 2, Q_MT = 1000, σ = 32`,
strictly exceeding the `49 * 5 = 245` verifier Merkle hash queries of depth-4 openings and leaving
`755` prover Merkle queries). -/
theorem fri998_johnson_romSoundness_lt_one_25th
    (P : OracleComp (BCSROMSpec (OracleTable 4 (ZMod 998244353)) (FRIChal (ZMod 998244353) 4 6))
      (OracleTable 4 (ZMod 998244353) × BCSProof 3 (ZMod 998244353)))
    (hFS : IsCostBounded bcsFSCost P 2)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friIOP params998) (encZMod (p := 998244353))
        (params998.proximityLang 8) P) 1000) :
    bcsSoundnessGame (friIOP params998) (encZMod (p := 998244353)) (params998.proximityLang 8)
      P 32 true < 1 / 25 := by
  refine lt_of_le_of_lt
    (friBCS_romSoundness_bound_of_weightedLineGap params998 weightedLineGapBound_998
      (leftInverse_decZMod_encZMod 998244353) 32 hFS hMT) ?_
  rw [fri998_rbrError_eq, card_friChal998]
  have hnn :
      (5 * (117649 / 16777216 + 5 * (1 / 16747761131061248)) +
        1000 * (3015 * (1 / 4294967296)) : ℝ≥0) < 1 / 25 := by
    rw [← NNReal.coe_lt_coe]
    push_cast
    norm_num
  have hcast := ENNReal.coe_lt_coe.mpr hnn
  simp only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_one,
    ENNReal.coe_div (by norm_num : (16777216 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (16747761131061248 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (4294967296 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (25 : ℝ≥0) ≠ 0)] at hcast
  simpa only [params998,
    (by norm_num : ((2 + (2 + 1) : ℕ) : ℝ≥0∞) = 5),
    (by norm_num : ((1000 : ℕ) : ℝ≥0∞) = 1000),
    (by norm_num : ((3 * 1000 + (2 + 1) * (2 + (2 + 1)) : ℕ) : ℝ≥0∞) = 3015),
    (by norm_num : (2 : ℝ≥0∞) ^ 32 = 4294967296)] using hcast

-- Direct instantiation of `fri998_johnson_romSoundness_lt_one_25th` on an explicit feasible
-- accepting-shaped client (`2 + 49 * 5 = 247 ≤ 1000` whole-game Merkle queries).
example :
    bcsSoundnessGame (friIOP params998) (encZMod (p := 998244353)) (params998.proximityLang 8)
      (mkAcceptingCheater params998 (fun idx => (params998.eval 0 idx) ^ 4)) 32 true < 1 / 25 :=
  fri998_johnson_romSoundness_lt_one_25th
    (mkAcceptingCheater params998 (fun idx => (params998.eval 0 idx) ^ 4))
    (isCostBounded_FS_mkAcceptingCheater params998 _)
    (isCostBounded_soundnessProg_mkAcceptingCheater params998 (encZMod (p := 998244353)) 8 _
      (by decide : 2 + params998.proofOracleQueries * (params998.d + 1) ≤ 1000))

private theorem sum_johnsonCurveBound_998 :
    (∑ i : Fin params998.m,
      ProximityGap.johnsonCurveBound (2 ^ (params998.d - (i.val + 1))) (mRound998 i)
        (params998.dim (i.val + 1) - 1) (DRound998 i) 1 (2 ^ params998.d)) = 37335 := by
  decide

/-- Beyond-Sudan (`m = 2`) discrete Johnson summed interactive soundness (`< 1 / 140`, from
`(21270 + 16065) / 998244353 + (7 / 16) ^ 6 ≈ 0.00705 < 1 / 140`) over `ZMod 998244353`. -/
theorem fri998_interactiveGame_lt_one_140th
    (P : InteractiveIOPProver 4 (ZMod 998244353) (FRIChal (ZMod 998244353) 4 6)) :
    iopInteractiveGame (friIOP params998)
      (fun idx => (params998.eval 0 idx) ^ 4) P true < 1 / 140 := by
  refine lt_of_le_of_lt
    (friIOP_interactiveGame_le_of_johnson_discrete params998 (e := 8) (by decide)
      mRound998 DRound998
      (fun i => by fin_cases i <;> decide)
      (fun i => by fin_cases i <;> decide)
      (fun i => by fin_cases i <;> decide)
      (fun i => by fin_cases i <;> decide)
      farWord998_not_mem P) ?_
  rw [sum_johnsonCurveBound_998]
  simp only [ZMod.card, params998]
  have hlt : (37335 / 998244353 + (7 / 16) ^ 6 : ℝ≥0) < 1 / 140 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_pow,
    ENNReal.coe_div (by norm_num : (998244353 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (16 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (140 : ℝ≥0) ≠ 0),
    ENNReal.coe_ofNat, ENNReal.coe_one,
    (by norm_num : ((37335 : ℕ) : ℝ≥0∞) = 37335),
    (by norm_num : ((998244353 : ℕ) : ℝ≥0∞) = 998244353),
    (by norm_num : ((2 ^ 4 - 8 - 1 : ℕ) : ℝ≥0∞) = 7),
    (by norm_num : (2 : ℝ≥0∞) ^ 4 = 16)] using ENNReal.coe_lt_coe.mpr hlt

end Johnson998244353

/-! ### Suite 4: Closed-Form Asymptotic Johnson FRI over Goldilocks (`2 ^ 64 - 2 ^ 32 + 1`) -/

section JohnsonGoldilocks

/-- The 64-bit Goldilocks prime `p = 2 ^ 64 - 2 ^ 32 + 1 = 18446744069414584321`. -/
public abbrev goldilocksP : ℕ := 18446744069414584321

private theorem goldilocks_seven_pow16 :
    (7 : ZMod goldilocksP) ^ (2 ^ 16) = ((11156834669773791359 : ℕ) : ZMod goldilocksP) := by
  rw [show (7 : ZMod goldilocksP) = ((7 : ℕ) : ZMod goldilocksP) from rfl, ← modSq_zmod]
  decide

private theorem goldilocks_seven_pow32 :
    (7 : ZMod goldilocksP) ^ (2 ^ 32) = ((12275445934081160404 : ℕ) : ZMod goldilocksP) := by
  have h32 : 2 ^ 32 = 2 ^ 16 * 2 ^ 16 := by norm_num
  rw [h32, pow_mul, goldilocks_seven_pow16, ← modSq_zmod]
  decide

private theorem goldilocks_seven_pow48 :
    (7 : ZMod goldilocksP) ^ (2 ^ 48) = ((5647278486080789199 : ℕ) : ZMod goldilocksP) := by
  have h48 : 2 ^ 48 = 2 ^ 32 * 2 ^ 16 := by norm_num
  rw [h48, pow_mul, goldilocks_seven_pow32, ← modSq_zmod]
  decide

theorem prime_goldilocks : Nat.Prime goldilocksP := by
  refine lucas_primality goldilocksP (7 : ZMod goldilocksP) ?_ ?_
  · rw [show (7 : ZMod goldilocksP) = ((7 : ℕ) : ZMod goldilocksP) from rfl,
      zmod_pow_chunks16 goldilocks_seven_pow16 goldilocks_seven_pow32 goldilocks_seven_pow48
        (by decide)]
    decide
  · intro q hq hdvd
    have hfac : q ∣ 2 ^ 32 * 3 * 5 * 17 * 257 * 65537 := hdvd
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 17 ∨ q = 257 ∨ q = 65537 := by
      rcases hq.dvd_mul.mp hfac with h1 | h65537
      · rcases hq.dvd_mul.mp h1 with h2 | h257
        · rcases hq.dvd_mul.mp h2 with h3 | h17
          · rcases hq.dvd_mul.mp h3 with h4 | h5
            · rcases hq.dvd_mul.mp h4 with h2pow | h3p
              · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
                  (hq.dvd_of_dvd_pow h2pow))
              · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h3p))
            · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h5)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl
              ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h17))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h257)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ((Nat.prime_dvd_prime_iff_eq hq prime_65537).mp h65537)))))
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    · rw [show (7 : ZMod goldilocksP) = ((7 : ℕ) : ZMod goldilocksP) from rfl,
        zmod_pow_chunks16 goldilocks_seven_pow16 goldilocks_seven_pow32 goldilocks_seven_pow48
          (by decide)]
      decide

instance instPrimeGoldilocks : Fact (Nat.Prime goldilocksP) := ⟨prime_goldilocks⟩

private theorem omegaGoldilocks_pow_16 : (64 : ZMod goldilocksP) ^ 16 = -1 := by
  rw [show (64 : ZMod goldilocksP) = ((64 : ℕ) : ZMod goldilocksP) from rfl,
    zmod_pow_eq_modPowAux goldilocksP 5 64 16 (by omega)]
  decide

/-- 2-folding-round, depth-5 (`|L_0| = 32`), rate-`1 / 8` (`kFinal = 1`, `dim 0 = 4`), `q = 6`
FRI instance over the Goldilocks prime field `ZMod (2 ^ 64 - 2 ^ 32 + 1)`. -/
def paramsGoldilocks : FRIParams (ZMod goldilocksP) where
  d := 5
  m := 2
  kFinal := 1
  q := 6
  g := 1
  ω := 64
  hm := by omega
  hkPos := by omega
  hkLe := by omega
  hg := one_ne_zero
  h2 := by decide
  hω := isPrimitiveRoot_two_pow_of_neg_one (by omega) (by decide) omegaGoldilocks_pow_16

-- Radius `e = 17` is strictly beyond unique decoding (`2 * 17 + 4 = 38 > 32`).
theorem paramsGoldilocks_beyond_unique :
    ¬ (2 * 17 + paramsGoldilocks.dim 0 ≤ 2 ^ paramsGoldilocks.d) := by
  decide

-- Exact evaluation of the closed-form uniform Johnson commit budget (`mJ = 2`).
example : friJohnsonCommitBound paramsGoldilocks 2 = 5374771200 := rfl

-- Honest completeness over Goldilocks holds simultaneously with Johnson soundness.
example (σ : ℕ) :
    bcsHonestROMGame (friIOP paramsGoldilocks) (encZMod (p := goldilocksP))
      (fun _ => 0) () σ = PMF.pure true :=
  friBCS_honestROMGame_eq_pure_true paramsGoldilocks (encZMod (p := goldilocksP))
    (zero_mem_initialCode paramsGoldilocks) σ

/-- Non-codeword `X ^ 4` on `L_0` (`|L_0| = 32`), at Hamming distance `≥ 28 > 17` from
`paramsGoldilocks.initialCode`. -/
def farWordGoldilocks : OracleTable 5 (ZMod goldilocksP) :=
  fun idx => (paramsGoldilocks.eval 0 idx) ^ 4

theorem farWordGoldilocks_not_mem :
    farWordGoldilocks ∉ paramsGoldilocks.proximityLang 17 :=
  monomial_far_not_mem_proximityLang paramsGoldilocks (by decide)

/-- Verifies the closed-form Johnson slack inequality `17 / 32 ≤ 1 - √(1 / 8) - √(1 / 8) / 4`. -/
theorem goldilocks_johnson_slack :
    ((17 : ℕ) : ℝ) / (2 ^ paramsGoldilocks.d : ℝ) ≤
      1 - Real.sqrt ((paramsGoldilocks.dim 0 : ℝ) / (2 ^ paramsGoldilocks.d : ℝ)) -
        Real.sqrt ((paramsGoldilocks.dim 0 : ℝ) / (2 ^ paramsGoldilocks.d : ℝ)) /
          (2 * ((2 : ℕ) : ℝ)) := by
  have hsq : Real.sqrt ((1 : ℝ) / 8) ≤ (3 : ℝ) / 8 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hrate :
      ((paramsGoldilocks.dim 0 : ℝ) / (2 ^ paramsGoldilocks.d : ℝ)) = (1 : ℝ) / 8 := by
    norm_num [paramsGoldilocks, FRIParams.dim]
  rw [hrate]
  have h17 : ((17 : ℕ) : ℝ) / (2 ^ paramsGoldilocks.d : ℝ) = (17 : ℝ) / 32 := by
    norm_num [paramsGoldilocks]
  have h4 : 2 * ((2 : ℕ) : ℝ) = 4 := by norm_num
  rw [h17, h4]
  linarith

-- Direct check of `friIOP_rbrSound_of_johnson` (closed-form unconditional RBR soundness).
theorem friGoldilocks_rbrSound_of_johnson :
    IOPRoundByRoundSoundness (friIOP paramsGoldilocks) (paramsGoldilocks.proximityLang 17)
      (friDoomed paramsGoldilocks (2 ^ paramsGoldilocks.d - 17 - 1))
      (friGoodStep paramsGoldilocks (2 ^ paramsGoldilocks.d - 17 - 1)) ∧
    ∀ stmt ∉ paramsGoldilocks.proximityLang 17, ∀ pref π,
      friDoomed paramsGoldilocks (2 ^ paramsGoldilocks.d - 17 - 1) stmt pref →
      (PMF.uniformOfFintype
          (FRIChal (ZMod goldilocksP) paramsGoldilocks.d paramsGoldilocks.q)).toOuterMeasure
        {c | ¬ friGoodStep paramsGoldilocks (2 ^ paramsGoldilocks.d - 17 - 1) stmt pref π c} ≤
      friRBRError paramsGoldilocks 17 (friJohnsonCommitBound paramsGoldilocks 2) :=
  friIOP_rbrSound_of_johnson paramsGoldilocks (by omega) goldilocks_johnson_slack

private theorem friGoldilocks_rbrError_eq :
    friRBRError paramsGoldilocks 17 (friJohnsonCommitBound paramsGoldilocks 2) =
      ((117649 : ℝ≥0∞) / (16777216 : ℝ≥0∞)) := by
  have hle_nn : (5374771200 / 18446744069414584321 : ℝ≥0) ≤ 117649 / 16777216 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    norm_num
  have hle : (5374771200 : ℝ≥0∞) / 18446744069414584321 ≤ 117649 / 16777216 := by
    simpa only [ENNReal.coe_div (by norm_num : (18446744069414584321 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (16777216 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using
      ENNReal.coe_le_coe.mpr hle_nn
  have hpow : (((14 : ℝ≥0∞) / (32 : ℝ≥0∞)) ^ 6) = (117649 : ℝ≥0∞) / (16777216 : ℝ≥0∞) := by
    have hnn : ((14 / 32 : ℝ≥0) ^ 6) = 117649 / 16777216 := by
      rw [← NNReal.coe_inj]
      push_cast
      norm_num
    simpa only [ENNReal.coe_pow, ENNReal.coe_div (by norm_num : (32 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (16777216 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using
      congrArg ENNReal.ofNNReal hnn
  have hcard : (Fintype.card (ZMod goldilocksP) : ℝ≥0∞) = 18446744069414584321 := by
    simp only [ZMod.card, goldilocksP, Nat.cast_ofNat]
  rw [show friJohnsonCommitBound paramsGoldilocks 2 = 5374771200 from rfl]
  simp only [friRBRError, hcard, paramsGoldilocks,
    (by norm_num : ((5374771200 : ℕ) : ℝ≥0∞) = 5374771200),
    (by norm_num : ((2 ^ 5 - 17 - 1 : ℕ) : ℝ≥0∞) = 14),
    (by norm_num : (2 : ℝ≥0∞) ^ 5 = 32), hpow]
  exact max_eq_right hle

private theorem card_friChalGoldilocks :
    (Fintype.card (FRIChal (ZMod goldilocksP) paramsGoldilocks.d paramsGoldilocks.q) : ℝ≥0∞) =
      19807040623954398381032341504 := by
  rw [card_friChal, ZMod.card]
  norm_num [paramsGoldilocks, goldilocksP]

/-- **Unconditional closed-form Johnson-bound BCS-FRI ROM soundness (`< 1 / 25`)** over Goldilocks
at radius `e = 17 > e_uniq = 14` (`mJ = 2, t_FS = 2, Q_MT = 1000, σ = 32`, strictly exceeding the
`49 * 6 = 294` verifier Merkle hash queries of depth-5 openings and leaving `706` prover Merkle
queries), directly via `friBCS_romSoundness_bound_of_johnson`. -/
theorem friGoldilocks_johnson_romSoundness_lt_one_25th
    (P : OracleComp
      (BCSROMSpec (OracleTable 5 (ZMod goldilocksP)) (FRIChal (ZMod goldilocksP) 5 6))
      (OracleTable 5 (ZMod goldilocksP) × BCSProof 3 (ZMod goldilocksP)))
    (hFS : IsCostBounded bcsFSCost P 2)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friIOP paramsGoldilocks) (encZMod (p := goldilocksP))
        (paramsGoldilocks.proximityLang 17) P) 1000) :
    bcsSoundnessGame (friIOP paramsGoldilocks) (encZMod (p := goldilocksP))
      (paramsGoldilocks.proximityLang 17) P 32 true < 1 / 25 := by
  refine lt_of_le_of_lt
    (friBCS_romSoundness_bound_of_johnson paramsGoldilocks (by omega) goldilocks_johnson_slack
      (leftInverse_decZMod_encZMod goldilocksP) 32 hFS hMT) ?_
  rw [friGoldilocks_rbrError_eq, card_friChalGoldilocks]
  have hnn :
      (5 * (117649 / 16777216 + 5 * (1 / 19807040623954398381032341504)) +
        1000 * (3015 * (1 / 4294967296)) : ℝ≥0) < 1 / 25 := by
    rw [← NNReal.coe_lt_coe]
    push_cast
    norm_num
  have hcast := ENNReal.coe_lt_coe.mpr hnn
  simp only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_one,
    ENNReal.coe_div (by norm_num : (16777216 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (19807040623954398381032341504 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (4294967296 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (25 : ℝ≥0) ≠ 0)] at hcast
  simpa only [paramsGoldilocks,
    (by norm_num : ((2 + (2 + 1) : ℕ) : ℝ≥0∞) = 5),
    (by norm_num : ((1000 : ℕ) : ℝ≥0∞) = 1000),
    (by norm_num : ((3 * 1000 + (2 + 1) * (2 + (2 + 1)) : ℕ) : ℝ≥0∞) = 3015),
    (by norm_num : (2 : ℝ≥0∞) ^ 32 = 4294967296)] using hcast

/-- Explicit adaptive out-of-order cheating prover (`t_FS = 2, t_MT = 2, L_path = 5`) attempting
to forge a Goldilocks BCS-FRI proof for `farWordGoldilocks ∉ paramsGoldilocks.proximityLang 17`,
instantiating `mkAcceptingCheater` at `paramsGoldilocks` and `farWordGoldilocks`. -/
abbrev friCheaterGoldilocks :
    OracleComp
      (BCSROMSpec (OracleTable 5 (ZMod goldilocksP)) (FRIChal (ZMod goldilocksP) 5 6))
      (OracleTable 5 (ZMod goldilocksP) × BCSProof 3 (ZMod goldilocksP)) :=
  mkAcceptingCheater paramsGoldilocks farWordGoldilocks

-- Direct instantiation of `friGoldilocks_johnson_romSoundness_lt_one_25th` on the explicit
-- accepting-shaped adaptive client `friCheaterGoldilocks` (`2 + 49 * 6 = 296 ≤ 1000`).
example :
    bcsSoundnessGame (friIOP paramsGoldilocks) (encZMod (p := goldilocksP))
      (paramsGoldilocks.proximityLang 17) friCheaterGoldilocks 32 true < 1 / 25 :=
  friGoldilocks_johnson_romSoundness_lt_one_25th friCheaterGoldilocks
    (isCostBounded_FS_mkAcceptingCheater paramsGoldilocks farWordGoldilocks)
    (isCostBounded_soundnessProg_mkAcceptingCheater paramsGoldilocks
      (encZMod (p := goldilocksP)) 17 farWordGoldilocks
      (by decide : 2 + paramsGoldilocks.proofOracleQueries * (paramsGoldilocks.d + 1) ≤ 1000))

/-- **End-to-end unconditional closed-form Johnson-bound BCS-FRI ROM soundness (`< 1 / 3`)** for
the explicit adaptive out-of-order cheating prover `friCheaterGoldilocks` at digest length
`σ = 20`, via `friBCS_romSoundness_bound_of_prover_verifier_of_johnson`. -/
theorem friCheaterGoldilocks_romSoundness_lt_one_third :
    bcsSoundnessGame (friIOP paramsGoldilocks) (encZMod (p := goldilocksP))
      (paramsGoldilocks.proximityLang 17) friCheaterGoldilocks 20 true < 1 / 3 := by
  refine lt_of_le_of_lt
    (friBCS_romSoundness_bound_of_prover_verifier_of_johnson paramsGoldilocks (by omega)
      goldilocks_johnson_slack (leftInverse_decZMod_encZMod goldilocksP) 20
      (isCostBounded_MT_mkAcceptingCheater paramsGoldilocks farWordGoldilocks)
      (isCostBounded_FS_mkAcceptingCheater paramsGoldilocks farWordGoldilocks)
      (mkAcceptingCheater_openings_le paramsGoldilocks farWordGoldilocks)) ?_
  rw [friGoldilocks_rbrError_eq, card_friChalGoldilocks]
  have hnn :
      (5 * (117649 / 16777216 + 5 * (1 / 19807040623954398381032341504)) +
        296 * (903 * (1 / 1048576)) : ℝ≥0) < 1 / 3 := by
    rw [← NNReal.coe_lt_coe]
    push_cast
    norm_num
  have hcast := ENNReal.coe_lt_coe.mpr hnn
  simp only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_one,
    ENNReal.coe_div (by norm_num : (16777216 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (19807040623954398381032341504 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (1048576 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (3 : ℝ≥0) ≠ 0)] at hcast
  simpa only [paramsGoldilocks, FRIParams.proofOracleQueries,
    (by norm_num : ((2 + (2 + 1) : ℕ) : ℝ≥0∞) = 5),
    (by norm_num : ((2 + (1 + 6 * (3 * 2 + 2)) * (5 + 1) : ℕ) : ℝ≥0∞) = 296),
    (by norm_num :
      ((3 * (2 + (1 + 6 * (3 * 2 + 2)) * (5 + 1)) + (2 + 1) * (2 + (2 + 1)) : ℕ) : ℝ≥0∞) = 903),
    (by norm_num : (2 : ℝ≥0∞) ^ 20 = 1048576)] using hcast

-- Geometric halving of `friJohnsonRoundBound` across Goldilocks folding rounds (`mJ = 2`):
-- round 0 = 5374771200 (= `friJohnsonCommitBound`), round 1 = 2687385600, sum = 8062156800.
example : friJohnsonRoundBound paramsGoldilocks 2 ⟨0, by decide⟩ = 5374771200 :=
  friJohnsonRoundBound_zero paramsGoldilocks 2 (by decide)
example : friJohnsonRoundBound paramsGoldilocks 2 ⟨1, by decide⟩ = 2687385600 := rfl
example :
    (∑ i : Fin paramsGoldilocks.m, friJohnsonRoundBound paramsGoldilocks 2 i) ≤ 8062156800 :=
  sum_friJohnsonRoundBound_le paramsGoldilocks 2

private theorem friGoldilocks_commitError_lt :
    friJohnsonCommitError paramsGoldilocks 2 < (1 : ℝ) / 1000000000 := by
  simp only [friJohnsonCommitError, ZMod.card, paramsGoldilocks, FRIParams.dim, goldilocksP]
  norm_num

/-- Closed-form geometric Johnson commit-phase bound (`< 1 / 10 ^ 9`) over Goldilocks via
`friCommitGame_le_of_johnson`. -/
theorem friGoldilocks_commitGame_lt_billionth
    (P : InteractiveIOPProver 5 (ZMod goldilocksP) (FRIChal (ZMod goldilocksP) 5 6)) :
    friCommitGame paramsGoldilocks (2 ^ paramsGoldilocks.d - 17 - 1) farWordGoldilocks P true <
      1 / 1000000000 := by
  refine lt_of_le_of_lt
    (friCommitGame_le_of_johnson paramsGoldilocks (by omega) goldilocks_johnson_slack
      farWordGoldilocks_not_mem P) ?_
  have hof :
      ENNReal.ofReal (friJohnsonCommitError paramsGoldilocks 2) <
        ENNReal.ofReal ((1 : ℝ) / 1000000000) :=
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr friGoldilocks_commitError_lt
  have hrhs : ENNReal.ofReal ((1 : ℝ) / 1000000000) = (1 : ℝ≥0∞) / 1000000000 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
    norm_num
  rwa [hrhs] at hof

/-- Closed-form geometric Johnson summed interactive soundness (`< 1 / 140`) over Goldilocks via
`friIOP_interactiveGame_le_of_johnson`. -/
theorem friGoldilocks_interactiveGame_lt_one_140th
    (P : InteractiveIOPProver 5 (ZMod goldilocksP) (FRIChal (ZMod goldilocksP) 5 6)) :
    iopInteractiveGame (friIOP paramsGoldilocks) farWordGoldilocks P true < 1 / 140 := by
  refine lt_of_le_of_lt
    (friIOP_interactiveGame_le_of_johnson paramsGoldilocks (by omega) goldilocks_johnson_slack
      farWordGoldilocks_not_mem P) ?_
  have hcommit :
      ENNReal.ofReal (friJohnsonCommitError paramsGoldilocks 2) ≤ (1 : ℝ≥0∞) / 1000000000 := by
    have hof := ENNReal.ofReal_le_ofReal friGoldilocks_commitError_lt.le
    have hrhs : ENNReal.ofReal ((1 : ℝ) / 1000000000) = (1 : ℝ≥0∞) / 1000000000 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
      norm_num
    rwa [hrhs] at hof
  refine lt_of_le_of_lt (add_le_add hcommit le_rfl) ?_
  simp only [paramsGoldilocks]
  have hlt : (1 / 1000000000 + (14 / 32) ^ 6 : ℝ≥0) < 1 / 140 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_pow,
    ENNReal.coe_div (by norm_num : (1000000000 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (32 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (140 : ℝ≥0) ≠ 0),
    ENNReal.coe_ofNat, ENNReal.coe_one,
    (by norm_num : ((2 ^ 5 - 17 - 1 : ℕ) : ℝ≥0∞) = 14),
    (by norm_num : (2 : ℝ≥0∞) ^ 5 = 32)] using ENNReal.coe_lt_coe.mpr hlt

/-- Randomized transcript-ignoring `InteractiveIOPProver` (mixing `farWordGoldilocks` and `0`
uniformly each round independently of the prefix) certified `< 1 / 140` in `iopInteractiveGame`
over Goldilocks. -/
noncomputable def randProverGoldilocks :
    InteractiveIOPProver 5 (ZMod goldilocksP) (FRIChal (ZMod goldilocksP) 5 6) :=
  fun _ => (PMF.uniformOfFintype Bool).map fun b => if b then farWordGoldilocks else fun _ => 0

example :
    iopInteractiveGame (friIOP paramsGoldilocks) farWordGoldilocks randProverGoldilocks true <
      1 / 140 :=
  friGoldilocks_interactiveGame_lt_one_140th randProverGoldilocks

/-- Prefix-dependent (adaptive) randomized `InteractiveIOPProver` over Goldilocks: in round `0`
(`pref = []`), mixes `farWordGoldilocks` and `0` uniformly; after receiving `(π₀, c₀)` in round `0`,
adapts its committed oracle distribution to the observed verifier scalar `c₀.foldScalar` and prior
oracle `π₀` (shifting `π₀` by `c₀.foldScalar` vs. the constant table `fun _ => c₀.foldScalar + 1`).
-/
noncomputable def adaptiveProverGoldilocks :
    InteractiveIOPProver 5 (ZMod goldilocksP) (FRIChal (ZMod goldilocksP) 5 6)
  | [] =>
    (PMF.uniformOfFintype Bool).map fun b =>
      if b then farWordGoldilocks else fun _ => 0
  | (π₀, c₀) :: _ =>
    (PMF.uniformOfFintype Bool).map fun b =>
      if b then fun idx => π₀ idx + c₀.foldScalar else fun _ => c₀.foldScalar + 1

/-- Witness that `adaptiveProverGoldilocks` genuinely depends on the transcript prefix: at
`pref = []`, the constant-zero table is in its support, whereas after observing challenge scalar
`c₀.foldScalar = 1` on `π₀ = 0`, every supported table evaluates to `1` or `2` (never `0`). -/
theorem adaptiveProverGoldilocks_prefix_dependent :
    let c₀ : FRIChal (ZMod goldilocksP) 5 6 := ⟨1, fun _ => ⟨0, by decide⟩⟩
    adaptiveProverGoldilocks [] ≠ adaptiveProverGoldilocks [(fun _ => 0, c₀)] := by
  intro c₀ heq
  have hmem_nil : (fun _ : Fin 32 => (0 : ZMod goldilocksP)) ∈
      (adaptiveProverGoldilocks []).support := by
    rw [adaptiveProverGoldilocks, PMF.mem_support_map_iff]
    exact ⟨false, PMF.mem_support_uniformOfFintype false, rfl⟩
  have hmem_cons : (fun _ : Fin 32 => (0 : ZMod goldilocksP)) ∈
      (adaptiveProverGoldilocks [(fun _ => 0, c₀)]).support := heq ▸ hmem_nil
  rw [adaptiveProverGoldilocks, PMF.mem_support_map_iff] at hmem_cons
  obtain ⟨b, _, hb⟩ := hmem_cons
  have h0 := congrFun hb ⟨0, by decide⟩
  cases b
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)

example :
    friCommitGame paramsGoldilocks (2 ^ paramsGoldilocks.d - 17 - 1) farWordGoldilocks
      adaptiveProverGoldilocks true < 1 / 1000000000 :=
  friGoldilocks_commitGame_lt_billionth adaptiveProverGoldilocks

example :
    iopInteractiveGame (friIOP paramsGoldilocks) farWordGoldilocks adaptiveProverGoldilocks true <
      1 / 140 :=
  friGoldilocks_interactiveGame_lt_one_140th adaptiveProverGoldilocks

end JohnsonGoldilocks

end CslibFrontierTests.Crypto.FRIJohnson
