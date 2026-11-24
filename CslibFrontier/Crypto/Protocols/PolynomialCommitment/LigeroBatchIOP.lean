/-
Copyright (c) 2026 Mayank Rathee, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.BCS.Interactive
public import CslibFrontier.Crypto.Protocols.BCS.ROM
public import CslibFrontier.Crypto.Protocols.PolynomialCommitment.LigeroProximity
public import CslibFrontier.Foundations.Data.Code.InterleavedCurve
import CslibFrontier.Foundations.Data.Hamming
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.UniformBound
import Mathlib.Algebra.Polynomial.OfFn

/-!
# Batched Reed–Solomon proximity IOPs, curve-batched Ligero reductions, and BCS/ROM soundness

`CslibFrontier.Crypto.Protocols.PolynomialCommitment.LigeroProximity` formalizes full-vector
(`r : Fin m → F`) Ligero proximity testing in `Cslib.Interactive.Reduction` up to `d / 3` for
general linear codes and up to unique decoding (`2 * e + k ≤ n`) for Reed–Solomon codes, together
with column-query soundness of `ligeroEvalCheck` assuming `M` is already `e`-close to `U * G`.
This module advances `#5968` and `#643` in three steps (after
[AmesHazayIshaiVenkitasubramaniam2017], [BenSassonCarmonIshaiKoppartySaraf2020], and
[BenSassonChiesaSpooner2016]; locator for [AmesHazayIshaiVenkitasubramaniam2017] not re-verified
against primary PDF):

1. **Weight-parameterized Ligero proximity reductions, single-scalar curve batching, and
   Johnson-bound (`1 - √ρ`) soundness** (`ligeroBatchProximityReduction`,
   `ligeroCurveProximityReduction`): one reduction parameterized by `weights : BatchChal →
   (Fin m → F)` specializes at `ligeroPowWeights m` (`z ↦ (1, z, …, z ^ (m - 1))`) to single-scalar
   curve batching. Combining these reductions with
   `CslibFrontier.Foundations.Data.Code.InterleavedCurve` yields round-by-round and plain-model
   soundness:
   * for full-vector `ligeroBatchProximityReduction m id` (`Fin m → F`) up to the Johnson bound
     `1 - √ρ` with **row-count-independent** batching error (explicit `(m_GS, D)` Guruswami–Sudan
     bound and closed-form `1 - √ρ - η` Siegel bound);
   * for `ligeroCurveProximityReduction` (`z : F`, compressing randomness from `m` field elements to
     one scalar) in both the unique-decoding regime (`2 * e + k ≤ n`, error
     `((m - 1) * n) / |F| + ((n - (e + 1)) / n) ^ q`) and the Johnson regime (`1 - √ρ`).
2. **Combined proximity-and-evaluation interactive reduction** (`LigeroEvalClaim`,
   `ligeroBatchEvalReduction`): discharges **both** interleaved `e`-proximity and a bilinear
   evaluation claim `(b ᵥ* U) ⬝ᵥ c = w` over the same `q` queried columns of `M` against arbitrary
   matrices and arbitrary cheating provers without extra query-round error, and characterizes the
   accepted unique-decoding language `ligeroEvalProximityLang` constructively via
   `Cslib.Code.berlekampWelchInterleaved` (`mem_ligeroEvalProximityLang_reedSolomon_iff`).
3. **Direct batched Reed–Solomon proximity `PublicCoinIOP` and two-channel BCS/ROM compilation**
   (`rsBatchProximityIOP`, `rsAffineBatchProximityIOP`, `rsCurveBatchProximityIOP`): compiles the
   2-round batched Reed–Solomon proximity test over `Fin (2 ^ d)` (`k ≤ 2 ^ d`) as a
   `Cslib.Crypto.Protocols.BCS.PublicCoinIOP` issuing **exact** `k` committed message openings and
   `q` scheduled column reads, proving perfect IOP and two-channel ROM completeness
   (`rsBatchProximityBCS_honestROMGame_eq_pure_true`), `IOPRoundByRoundSoundness`, interactive
   soundness (`rsBatchProximityIOP_interactive_le`), and adaptive two-channel random-oracle
   soundness (`rsBatchProximityBCS_romSoundness_bound`) across both the unique-decoding and Johnson
   regimes.

## Main definitions

* `Cslib.Crypto.Protocols.ligeroPowWeights`: Vandermonde power weights `i ↦ z ^ (i : ℕ)` compressing
  `m`-row batching to a single scalar `z : F`.
* `Cslib.Crypto.Protocols.ligeroBatchProximityReduction`,
  `Cslib.Crypto.Protocols.ligeroCurveProximityReduction`: weight-parameterized and single-scalar
  curve-batched Ligero proximity reductions.
* `Cslib.Crypto.Protocols.LigeroEvalClaim`, `Cslib.Crypto.Protocols.LigeroEvalReply`,
  `Cslib.Crypto.Protocols.ligeroEvalCodewordRel`, `Cslib.Crypto.Protocols.ligeroEvalProximityLang`,
  `Cslib.Crypto.Protocols.ligeroBatchEvalReduction`: combined proximity-and-evaluation claim,
  prover reply, relations/language, and `q`-column public-coin reduction.
* `Cslib.Crypto.Protocols.LigeroIOPChal`, `Cslib.Crypto.Protocols.rsBatchProximityIOP`,
  `Cslib.Crypto.Protocols.rsAffineBatchProximityIOP`,
  `Cslib.Crypto.Protocols.rsCurveBatchProximityIOP`: challenge record and 2-round `PublicCoinIOP`
  instantiations of batched Reed–Solomon proximity testing.

## Main results

* `Cslib.Crypto.Protocols.ligeroBatchProximityReduction_outputOn_congr`,
  `Cslib.Crypto.Protocols.ligeroBatchProximityReduction_complete`: `q`-column query locality and
  perfect completeness for any batching weight family.
* `Cslib.Crypto.Protocols.ligeroAffineProximityReduction_reedSolomon_rbrSound_johnson_exact`,
  `Cslib.Crypto.Protocols.ligeroAffineProximityReduction_reedSolomon_rbrSound_johnson_of_eta`,
  `Cslib.Crypto.Protocols.ligeroAffineProximityReduction_reedSolomon_sound_johnson_of_eta`:
  row-count-independent Johnson-bound soundness of full-vector `ligeroBatchProximityReduction`.
* `Cslib.Crypto.Protocols.ligeroCurveProximityReduction_reedSolomon_rbrSound`,
  `Cslib.Crypto.Protocols.ligeroCurveProximityReduction_reedSolomon_sound`,
  `Cslib.Crypto.Protocols.ligeroCurveProximityReduction_reedSolomon_rbrSound_johnson_exact`,
  `Cslib.Crypto.Protocols.ligeroCurveProximityReduction_reedSolomon_rbrSound_johnson_of_eta`,
  `Cslib.Crypto.Protocols.ligeroCurveProximityReduction_reedSolomon_sound_johnson_of_eta`:
  unique-decoding and Johnson-bound soundness of single-scalar `ligeroCurveProximityReduction`.
* `Cslib.Crypto.Protocols.mem_ligeroEvalProximityLang_reedSolomon_iff`,
  `Cslib.Crypto.Protocols.ligeroBatchEvalReduction_complete`,
  `Cslib.Crypto.Protocols.ligeroAffineEvalReduction_reedSolomon_rbrSound`,
  `Cslib.Crypto.Protocols.ligeroAffineEvalReduction_reedSolomon_sound`,
  `Cslib.Crypto.Protocols.ligeroCurveEvalReduction_reedSolomon_rbrSound`,
  `Cslib.Crypto.Protocols.ligeroCurveEvalReduction_reedSolomon_sound`: Berlekamp–Welch
  characterization, completeness, and unique-decoding soundness of combined proximity-and-evaluation
  testing.
* `Cslib.Crypto.Protocols.rsBatchProximityIOP_complete`,
  `Cslib.Crypto.Protocols.rsBatchProximityBCS_honestROMGame_eq_pure_true`,
  `Cslib.Crypto.Protocols.isCostBounded_bcsMTCost_rsBatchProximityVerifyROM`,
  `Cslib.Crypto.Protocols.rsAffineBatchProximityBCS_romSoundness_unique`,
  `Cslib.Crypto.Protocols.rsAffineBatchProximityBCS_romSoundness_johnson_of_eta`,
  `Cslib.Crypto.Protocols.rsCurveBatchProximityBCS_romSoundness_unique`,
  `Cslib.Crypto.Protocols.rsCurveBatchProximityBCS_romSoundness_johnson_of_eta`: completeness,
  verifier Merkle query budget `k * (L_path + 1)`, and adaptive two-channel BCS random-oracle
  soundness of batched Reed–Solomon proximity testing.

## References

* [S. Ames, C. Hazay, Y. Ishai, M. Venkitasubramaniam, *Ligero: Lightweight Sublinear Arguments
  Without a Trusted Setup*][AmesHazayIshaiVenkitasubramaniam2017]
* [E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf,
  *Proximity Gaps for Reed–Solomon Codes*][BenSassonCarmonIshaiKoppartySaraf2020]
* [E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive Oracle Proofs*][BenSassonChiesaSpooner2016]
* [A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024]
-/

public section

namespace Cslib.Crypto.Protocols

open Cslib.Code Cslib.Crypto.Protocols.BCS Cslib.Interactive Cslib.Interactive.Spec
  Cslib.OracleComp Cslib.Probability
open scoped BigOperators ENNReal Matrix Polynomial

/-! ### Part 1: Weight-parameterized and curve-batched Ligero proximity reductions -/

section BatchProximityReduction

/-- Vandermonde power weights `i ↦ z ^ (i : ℕ)` compressing an `m`-row linear combination to a
single scalar challenge `z : F`. -/
@[expose] def ligeroPowWeights {F : Type*} [Semiring F] (m : ℕ) (z : F) : Fin m → F :=
  fun i => z ^ (i : ℕ)

@[simp]
theorem ligeroPowWeights_apply {F : Type*} [Semiring F] (m : ℕ) (z : F) (i : Fin m) :
    ligeroPowWeights m z i = z ^ (i : ℕ) :=
  rfl

private lemma vecMul_eq_sum_smul_swap {F : Type*} [CommSemiring F] {m n : ℕ}
    (r : Fin m → F) (M : Matrix (Fin m) (Fin n) F) :
    r ᵥ* M = fun j => ∑ i : Fin m, r i • Function.swap M j i := by
  funext j
  simp only [Matrix.vecMul, dotProduct, Function.swap, smul_eq_mul]

private lemma vecMul_ligeroPowWeights_eq_sum_pow {F : Type*} [CommSemiring F] {m n : ℕ}
    (z : F) (M : Matrix (Fin m) (Fin n) F) :
    ligeroPowWeights m z ᵥ* M = fun j => ∑ i : Fin m, z ^ (i : ℕ) • Function.swap M j i :=
  vecMul_eq_sum_smul_swap (ligeroPowWeights m z) M

/-- Round specification of a weight-parameterized batched proximity reduction with batching
challenge space `BatchChal`, message length `l`, codeword length `n`, and `q` column queries. -/
abbrev ligeroBatchProximitySpec (BatchChal : Type) (l n q : ℕ) (F : Type) : Spec :=
  [.verifier BatchChal,
   .prover (Fin l → F) (OracleInterface.full (Fin l → F)),
   .verifier (Fin q → Fin n)]

/-- **Weight-parameterized Ligero interleaved proximity reduction**: samples a uniform challenge
`chal : BatchChal`, forms row weights `weights chal : Fin m → F`, receives a purported message
combination `v : Fin l → F`, and checks `ligeroColumnCheck G M (weights chal) v (Q t)` at `q`
independent uniform column indices `Q : Fin q → Fin n`. -/
noncomputable def ligeroBatchProximityReduction {F BatchChal : Type}
    [Field F] [DecidableEq F] [Fintype BatchChal] [Nonempty BatchChal]
    (m : ℕ) (weights : BatchChal → (Fin m → F)) {l n : ℕ} [NeZero n]
    (G : Matrix (Fin l) (Fin n) F) (q : ℕ) :
    Reduction OracleSpec.empty OracleSpec.empty (ligeroBatchProximitySpec BatchChal l n q F)
      (Matrix (Fin m) (Fin n) F) (Matrix (Fin m) (Fin l) F) Unit Unit where
  prover _ U :=
    pure (show BatchChal → ProbOracleComp OracleSpec.empty
        (ProbOracleComp OracleSpec.empty
          ((Fin l → F) × ((Fin q → Fin n) → ProbOracleComp OracleSpec.empty (Unit × Unit)))) from
      fun chal => pure (pure (ligeroRowComb (weights chal) U, fun _ => pure ((), ()))))
  verifier :=
    { samplers := (ProbComp.uniform BatchChal, ProbComp.uniform (Fin q → Fin n), ())
      decide := fun M (chal, Q, _) => do
        let v ← OracleComp.query
          (spec := OracleSpec.empty ⊕ₒ msgSpec (ligeroBatchProximitySpec BatchChal l n q F))
          (.inr (.inl ()))
        return if ∀ t : Fin q, ligeroColumnCheck G M (weights chal) v (Q t) = true then some ()
          else none }

/-- **Single-scalar curve-batched Ligero proximity reduction**: tests proximity to
`interleavedLinear (Fin m) (codeOfGenerator G)` using powers `1, z, …, z ^ (m - 1)` of a single
uniform scalar `z : F` and `q` uniform column queries. -/
noncomputable abbrev ligeroCurveProximityReduction {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (m : ℕ) {l n : ℕ} [NeZero n] (G : Matrix (Fin l) (Fin n) F) (q : ℕ) :
    Reduction OracleSpec.empty OracleSpec.empty (ligeroBatchProximitySpec F l n q F)
      (Matrix (Fin m) (Fin n) F) (Matrix (Fin m) (Fin l) F) Unit Unit :=
  ligeroBatchProximityReduction m (ligeroPowWeights m) G q

theorem ligeroBatchProximityReduction_outputOn {F BatchChal : Type}
    [Field F] [DecidableEq F] [Fintype BatchChal] [Nonempty BatchChal]
    (m : ℕ) (weights : BatchChal → (Fin m → F)) {l n : ℕ} [NeZero n]
    (G : Matrix (Fin l) (Fin n) F) (q : ℕ)
    (M : Matrix (Fin m) (Fin n) F) (chal : BatchChal) (v : Fin l → F) (Q : Fin q → Fin n) :
    (ligeroBatchProximityReduction m weights G q).verifier.outputOn M (chal, v, Q, ()) =
      if ∀ t : Fin q, ligeroColumnCheck G M (weights chal) v (Q t) = true then some ()
      else none := by
  rfl

/-- **Query locality**: `ligeroBatchProximityReduction` reads `M` only at the `q` queried columns
`Q t` (`t : Fin q`). -/
theorem ligeroBatchProximityReduction_outputOn_congr {F BatchChal : Type}
    [Field F] [DecidableEq F] [Fintype BatchChal] [Nonempty BatchChal]
    (m : ℕ) (weights : BatchChal → (Fin m → F)) {l n : ℕ} [NeZero n]
    (G : Matrix (Fin l) (Fin n) F) (q : ℕ)
    {M₁ M₂ : Matrix (Fin m) (Fin n) F} (chal : BatchChal) (v : Fin l → F) (Q : Fin q → Fin n)
    (hcols : ∀ t : Fin q, ∀ i : Fin m, M₁ i (Q t) = M₂ i (Q t)) :
    (ligeroBatchProximityReduction m weights G q).verifier.outputOn M₁ (chal, v, Q, ()) =
      (ligeroBatchProximityReduction m weights G q).verifier.outputOn M₂ (chal, v, Q, ()) := by
  rw [ligeroBatchProximityReduction_outputOn, ligeroBatchProximityReduction_outputOn]
  have hiff : (∀ t : Fin q, ligeroColumnCheck G M₁ (weights chal) v (Q t) = true) ↔
      (∀ t : Fin q, ligeroColumnCheck G M₂ (weights chal) v (Q t) = true) :=
    forall_congr' fun t => by
      simp only [ligeroColumnCheck, decide_eq_true_eq,
        Matrix.vecMul_apply_eq_sum (weights chal) _ (Q t)]
      rw [Finset.sum_congr rfl fun i _ => by rw [hcols t i]]
  by_cases h₁ : ∀ t : Fin q, ligeroColumnCheck G M₁ (weights chal) v (Q t) = true
  · rw [ite_eq_left h₁, ite_eq_left (hiff.1 h₁)]
  · rw [ite_eq_right h₁, ite_eq_right (h₁ ∘ hiff.2)]

/-- **Completeness of `ligeroBatchProximityReduction`**: every honestly encoded matrix `M = U * G`
is accepted with error `0`. -/
theorem ligeroBatchProximityReduction_complete {F BatchChal : Type}
    [Field F] [DecidableEq F] [Fintype BatchChal] [Nonempty BatchChal]
    (m : ℕ) (weights : BatchChal → (Fin m → F)) {l n : ℕ} [NeZero n]
    (G : Matrix (Fin l) (Fin n) F) (q : ℕ) :
    (ligeroBatchProximityReduction m weights G q).Complete
      World.plain (ligeroCodewordRel m G) Accept 0 := by
  intro M U hrel
  subst hrel
  rw [Reduction.run, World.plain_eval_execute, PMF.toOuterMeasure_map_apply]
  simp only [ligeroBatchProximityReduction, runStrategy, plainLaw_bind, plainLaw_pure,
    plainLaw_sample, PMF.pure_bind, PMF.bind_bind]
  rw [PMF.toOuterMeasure_bind_apply]
  refine Cslib.Probability.PMF.tsum_mul_le_of_forall_le _ fun chal => ?_
  rw [PMF.toOuterMeasure_bind_apply]
  refine Cslib.Probability.PMF.tsum_mul_le_of_forall_le _ fun Q => le_of_eq ?_
  have hchk : ∀ t : Fin q,
      ligeroColumnCheck G (U * G) (weights chal) (ligeroRowComb (weights chal) U) (Q t) = true :=
    fun t => ligeroColumnCheck_honest G U (weights chal) (Q t)
  refine (PMF.toOuterMeasure_pure_apply _ _).trans (ite_eq_right fun h => h ⟨?_, trivial⟩)
  exact (ligeroBatchProximityReduction_outputOn m weights G q (U * G) chal
    (ligeroRowComb (weights chal) U) Q).trans (ite_eq_left hchk)

private lemma ligeroBatchProximityReduction_rbrSound_of_rowBound
    {F BatchChal : Type} [Field F] [DecidableEq F]
    [Fintype BatchChal] [Nonempty BatchChal]
    (m : ℕ) (weights : BatchChal → (Fin m → F)) {l n q e : ℕ} [NeZero n]
    (G : Matrix (Fin l) (Fin n) F) (ε₁ : ℝ≥0∞)
    (hrow : ∀ M : Matrix (Fin m) (Fin n) F, M ∉ ligeroProximityLang m G e →
      (PMF.uniformOfFintype BatchChal).toOuterMeasure
        {chal | ∃ c ∈ codeOfGenerator G, hammingDist (weights chal ᵥ* M) c ≤ e} ≤ ε₁) :
    (ligeroBatchProximityReduction m weights G q).verifier.RbrSound
      (ligeroProximityLang m G e) Set.univ
      (ε₁, (((n - (e + 1) : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) ^ q, ()) := by
  refine ⟨fun M pfx => match pfx with
    | none => M ∈ ligeroProximityLang m G e
    | some (chal, none) => ∃ c ∈ codeOfGenerator G, hammingDist (weights chal ᵥ* M) c ≤ e
    | some (chal, some (_, none)) => ∃ c ∈ codeOfGenerator G, hammingDist (weights chal ᵥ* M) c ≤ e
    | some (chal, some (v, some (Q, _))) =>
        ∀ t : Fin q, ligeroColumnCheck G M (weights chal) v (Q t) = true,
    fun M hM => hM,
    fun M => ⟨fun hM => ?_, fun chal => ⟨fun hS _ h => hS h, fun v => ⟨fun hS => ?_,
      fun Q hS ⟨_, _, hout⟩ => ?_⟩⟩⟩⟩
  · change (ProbComp.eval (ProbComp.uniform BatchChal)).toOuterMeasure
      {chal | ∃ c ∈ codeOfGenerator G, hammingDist (weights chal ᵥ* M) c ≤ e} ≤ ε₁
    rw [ProbComp.eval_uniform]
    exact hrow M hM
  · have hfar : e < hammingDist (weights chal ᵥ* M) (v ᵥ* G) := by
      by_contra hle
      exact hS ⟨v ᵥ* G, vecMul_mem_codeOfGenerator G v, Nat.le_of_not_lt hle⟩
    change (ProbComp.eval (ProbComp.uniform (Fin q → Fin n))).toOuterMeasure
      {Q | ∀ t : Fin q, ligeroColumnCheck G M (weights chal) v (Q t) = true} ≤ _
    rw [ProbComp.eval_uniform]
    exact toOuterMeasure_ligeroColumnCheck_all_le G M (weights chal) v hfar
  · rw [ligeroBatchProximityReduction_outputOn] at hout
    split_ifs at hout with hchk
    exact hS hchk

private lemma forall_lt_interleaved_reedSolomon_of_not_mem {F : Type} [Field F] [DecidableEq F]
    {m k n e : ℕ} {α : Fin n → F} {M : Matrix (Fin m) (Fin n) F}
    (hM : M ∉ ligeroProximityLang m (reedSolomonGenerator α k) e) :
    ∀ V ∈ interleavedLinear (Fin m) (reedSolomon α k), e < hammingDist (Function.swap M) V := by
  intro V hV
  by_contra hle
  refine hM ⟨V, ?_, Nat.le_of_not_lt hle⟩
  rwa [codeOfGenerator_reedSolomonGenerator]

/-- **Explicit-parameter Guruswami–Sudan round-by-round soundness of full-vector
`ligeroBatchProximityReduction` up to the Johnson bound** (in the setting of
[BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.2 and 1.6]): the affine-vector batching round
has escape probability at most `johnsonCurveBound n m_GS (k - 1) D 1 n / |F|`, with **zero
dependence on the row count `m`**. -/
theorem ligeroAffineProximityReduction_reedSolomon_rbrSound_johnson_exact
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (m : ℕ) {k n q e m_GS D : ℕ} [NeZero n] {α : Fin n → F}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hm_GS : 1 ≤ m_GS)
    (hk_le : k ≤ n - e)
    (hinterp : n * (m_GS * (m_GS + 1) / 2) < (Sudan.monomials (k - 1) D).card)
    (hroot : D < m_GS * (n - e)) :
    (ligeroBatchProximityReduction m (id : (Fin m → F) → (Fin m → F))
      (reedSolomonGenerator α k) q).verifier.RbrSound
      (ligeroProximityLang m (reedSolomonGenerator α k) e) Set.univ
      ((ProximityGap.johnsonCurveBound n m_GS (k - 1) D 1 n : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞),
       (((n - (e + 1) : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) ^ q, ()) := by
  refine ligeroBatchProximityReduction_rbrSound_of_rowBound m id (reedSolomonGenerator α k) _
    fun M hM => ?_
  have hbound := toOuterMeasure_sum_smul_reedSolomon_close_le_johnson_exact hα hk hm_GS
    (by simpa only [Fintype.card_fin] using hk_le)
    (by simpa only [Fintype.card_fin] using hinterp)
    (by simpa only [Fintype.card_fin] using hroot)
    (forall_lt_interleaved_reedSolomon_of_not_mem hM)
  simpa only [codeOfGenerator_reedSolomonGenerator, vecMul_eq_sum_smul_swap, id_eq,
    Fintype.card_fin] using hbound

/-- **Round-by-round soundness of full-vector `ligeroBatchProximityReduction` up to `1 - √ρ - η`
(original explicit-constant variant)** (in the setting of
[BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.2 and 1.6]): for `1 ≤ k ≤ n`, `η > 0`, and
`(e : ℝ) / n ≤ 1 - √(k / n) - η`, the row-batching round has `m`-independent escape probability at
most `115200 * n ^ 2 / ((k / n) * η ^ 6 * |F|)` (using this library's explicit Siegel constant) and
the `q`-column query round has escape probability at most `((n - (e + 1)) / n) ^ q`. -/
theorem ligeroAffineProximityReduction_reedSolomon_rbrSound_johnson_of_eta
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (m : ℕ) {k n q e : ℕ} {η : ℝ} [NeZero n] {α : Fin n → F}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ n) (hη : 0 < η)
    (he : (e : ℝ) / (n : ℝ) ≤ 1 - Real.sqrt ((k : ℝ) / (n : ℝ)) - η) :
    (ligeroBatchProximityReduction m (id : (Fin m → F) → (Fin m → F))
      (reedSolomonGenerator α k) q).verifier.RbrSound
      (ligeroProximityLang m (reedSolomonGenerator α k) e) Set.univ
      (ENNReal.ofReal
        (115200 * ((n : ℝ) ^ 2) / (((k : ℝ) / (n : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ))),
       (((n - (e + 1) : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) ^ q, ()) := by
  refine ligeroBatchProximityReduction_rbrSound_of_rowBound m id (reedSolomonGenerator α k) _
    fun M hM => ?_
  have hbound := toOuterMeasure_sum_smul_reedSolomon_close_le_johnson_of_eta hα hk
    (by simpa only [Fintype.card_fin] using hkn) hη
    (by simpa only [Fintype.card_fin] using he)
    (forall_lt_interleaved_reedSolomon_of_not_mem hM)
  simpa only [codeOfGenerator_reedSolomonGenerator, vecMul_eq_sum_smul_swap, id_eq,
    Fintype.card_fin] using hbound

/-- **Plain-model soundness of full-vector `ligeroBatchProximityReduction` up to `1 - √ρ - η`
(original explicit-constant variant)** against every adaptive prover strategy. -/
theorem ligeroAffineProximityReduction_reedSolomon_sound_johnson_of_eta
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (m : ℕ) {k n q e : ℕ} {η : ℝ} [NeZero n] {α : Fin n → F}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ n) (hη : 0 < η)
    (he : (e : ℝ) / (n : ℝ) ≤ 1 - Real.sqrt ((k : ℝ) / (n : ℝ)) - η) :
    (ligeroBatchProximityReduction m (id : (Fin m → F) → (Fin m → F))
      (reedSolomonGenerator α k) q).verifier.Sound
      (oP := OracleSpec.empty) World.plain
      (ligeroProximityLang m (reedSolomonGenerator α k) e) Set.univ
      (ENNReal.ofReal
        (115200 * ((n : ℝ) ^ 2) / (((k : ℝ) / (n : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ))) +
       (((n - (e + 1) : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) ^ q) := by
  have h :=
    (ligeroAffineProximityReduction_reedSolomon_rbrSound_johnson_of_eta m (q := q)
      hα hk hkn hη he).sound
  simpa only [PerChallenge.sum, add_zero] using h

/-- **Round-by-round soundness of single-scalar `ligeroCurveProximityReduction` in the
unique-decoding regime** (`2 * e + k ≤ n`, derived via
[BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.5 and 6.1]): the single-scalar challenge round
has escape probability at most `((m - 1) * n) / |F|` and the `q`-column query round has escape
probability at most `((n - (e + 1)) / n) ^ q`. -/
theorem ligeroCurveProximityReduction_reedSolomon_rbrSound
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (m : ℕ) {k n q e : ℕ} [NeZero n] {α : Fin n → F}
    (hα : Function.Injective α) (hunique : 2 * e + k ≤ n) :
    (ligeroCurveProximityReduction m (reedSolomonGenerator α k) q).verifier.RbrSound
      (ligeroProximityLang m (reedSolomonGenerator α k) e) Set.univ
      ((((m - 1) * n : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞),
       (((n - (e + 1) : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) ^ q, ()) := by
  refine ligeroBatchProximityReduction_rbrSound_of_rowBound m (ligeroPowWeights m)
    (reedSolomonGenerator α k) _ fun M hM => ?_
  have hbound := toOuterMeasure_sum_pow_smul_reedSolomon_close_le hα
    (by simpa only [Fintype.card_fin] using hunique)
    (forall_lt_interleaved_reedSolomon_of_not_mem hM)
  simpa only [codeOfGenerator_reedSolomonGenerator, vecMul_ligeroPowWeights_eq_sum_pow,
    Fintype.card_fin] using hbound

/-- **Plain-model soundness of single-scalar `ligeroCurveProximityReduction` in the
unique-decoding regime** (`2 * e + k ≤ n`) against every adaptive prover strategy. -/
theorem ligeroCurveProximityReduction_reedSolomon_sound
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (m : ℕ) {k n q e : ℕ} [NeZero n] {α : Fin n → F}
    (hα : Function.Injective α) (hunique : 2 * e + k ≤ n) :
    (ligeroCurveProximityReduction m (reedSolomonGenerator α k) q).verifier.Sound
      (oP := OracleSpec.empty) World.plain
      (ligeroProximityLang m (reedSolomonGenerator α k) e) Set.univ
      ((((m - 1) * n : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) +
       (((n - (e + 1) : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) ^ q) := by
  have h := (ligeroCurveProximityReduction_reedSolomon_rbrSound m (q := q) hα hunique).sound
  simpa only [PerChallenge.sum, add_zero] using h

/-- **Explicit-parameter Guruswami–Sudan round-by-round soundness of single-scalar
`ligeroCurveProximityReduction` up to the Johnson bound** (in the setting of
[BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.5 and 6.2]). -/
theorem ligeroCurveProximityReduction_reedSolomon_rbrSound_johnson_exact
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (m : ℕ) {k n q e m_GS D : ℕ} [NeZero n] {α : Fin n → F}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hm_GS : 1 ≤ m_GS)
    (hk_le : k ≤ n - e)
    (hinterp : n * (m_GS * (m_GS + 1) / 2) < (Sudan.monomials (k - 1) D).card)
    (hroot : D < m_GS * (n - e)) :
    (ligeroCurveProximityReduction m (reedSolomonGenerator α k) q).verifier.RbrSound
      (ligeroProximityLang m (reedSolomonGenerator α k) e) Set.univ
      ((ProximityGap.johnsonCurveBound n m_GS (k - 1) D (m - 1) n : ℝ≥0∞) /
         (Fintype.card F : ℝ≥0∞),
       (((n - (e + 1) : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) ^ q, ()) := by
  refine ligeroBatchProximityReduction_rbrSound_of_rowBound m (ligeroPowWeights m)
    (reedSolomonGenerator α k) _ fun M hM => ?_
  have hbound := toOuterMeasure_sum_pow_smul_reedSolomon_close_le_johnson_exact hα hk hm_GS
    (by simpa only [Fintype.card_fin] using hk_le)
    (by simpa only [Fintype.card_fin] using hinterp)
    (by simpa only [Fintype.card_fin] using hroot)
    (forall_lt_interleaved_reedSolomon_of_not_mem hM)
  simpa only [codeOfGenerator_reedSolomonGenerator, vecMul_ligeroPowWeights_eq_sum_pow,
    Fintype.card_fin] using hbound

/-- **Round-by-round soundness of single-scalar `ligeroCurveProximityReduction` up to `1 - √ρ - η`
(original explicit-constant variant)** (in the setting of
[BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.5 and 6.2]). -/
theorem ligeroCurveProximityReduction_reedSolomon_rbrSound_johnson_of_eta
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (m : ℕ) {k n q e : ℕ} {η : ℝ} [NeZero n] {α : Fin n → F}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ n) (hη : 0 < η)
    (he : (e : ℝ) / (n : ℝ) ≤ 1 - Real.sqrt ((k : ℝ) / (n : ℝ)) - η) :
    (ligeroCurveProximityReduction m (reedSolomonGenerator α k) q).verifier.RbrSound
      (ligeroProximityLang m (reedSolomonGenerator α k) e) Set.univ
      (ENNReal.ofReal
        (115200 * ((m - 1 : ℕ) : ℝ) * ((n : ℝ) ^ 2) /
          (((k : ℝ) / (n : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ))),
       (((n - (e + 1) : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) ^ q, ()) := by
  refine ligeroBatchProximityReduction_rbrSound_of_rowBound m (ligeroPowWeights m)
    (reedSolomonGenerator α k) _ fun M hM => ?_
  have hbound := toOuterMeasure_sum_pow_smul_reedSolomon_close_le_johnson_of_eta hα hk
    (by simpa only [Fintype.card_fin] using hkn) hη
    (by simpa only [Fintype.card_fin] using he)
    (forall_lt_interleaved_reedSolomon_of_not_mem hM)
  simpa only [codeOfGenerator_reedSolomonGenerator, vecMul_ligeroPowWeights_eq_sum_pow,
    Fintype.card_fin] using hbound

/-- **Plain-model soundness of single-scalar `ligeroCurveProximityReduction` up to `1 - √ρ - η`
(original explicit-constant variant)** against every adaptive prover strategy. -/
theorem ligeroCurveProximityReduction_reedSolomon_sound_johnson_of_eta
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (m : ℕ) {k n q e : ℕ} {η : ℝ} [NeZero n] {α : Fin n → F}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ n) (hη : 0 < η)
    (he : (e : ℝ) / (n : ℝ) ≤ 1 - Real.sqrt ((k : ℝ) / (n : ℝ)) - η) :
    (ligeroCurveProximityReduction m (reedSolomonGenerator α k) q).verifier.Sound
      (oP := OracleSpec.empty) World.plain
      (ligeroProximityLang m (reedSolomonGenerator α k) e) Set.univ
      (ENNReal.ofReal
        (115200 * ((m - 1 : ℕ) : ℝ) * ((n : ℝ) ^ 2) /
          (((k : ℝ) / (n : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ))) +
       (((n - (e + 1) : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) ^ q) := by
  have h :=
    (ligeroCurveProximityReduction_reedSolomon_rbrSound_johnson_of_eta m (q := q)
      hα hk hkn hη he).sound
  simpa only [PerChallenge.sum, add_zero] using h

end BatchProximityReduction

/-! ### Part 2: Combined Ligero proximity-and-evaluation reduction -/

section BatchEvalReduction

/-- A Ligero bilinear evaluation claim on an `m × n` purported codeword matrix `matrix`: asserts
that `matrix` encodes an `m × l` witness matrix `U` satisfying
`ligeroEval U rowWeights colWeights = value` (`(rowWeights ᵥ* U) ⬝ᵥ colWeights = value`). -/
@[ext] structure LigeroEvalClaim (F : Type) (m l n : ℕ) where
  /-- Purported `m × n` encoded codeword matrix accessed via column queries. -/
  matrix : Matrix (Fin m) (Fin n) F
  /-- Row-combination evaluation weights `b : Fin m → F`. -/
  rowWeights : Fin m → F
  /-- Column-combination evaluation weights `c : Fin l → F`. -/
  colWeights : Fin l → F
  /-- Claimed scalar evaluation `w : F`. -/
  value : F

/-- Prover's message in `ligeroBatchEvalReduction`: the pre-encoded proximity row combination
`proxComb` and the pre-encoded evaluation row combination `evalComb`. -/
@[ext] structure LigeroEvalReply (F : Type) (l : ℕ) where
  /-- Purported pre-encoded combination `weights chal ᵥ* U` for the proximity check. -/
  proxComb : Fin l → F
  /-- Purported pre-encoded combination `claim.rowWeights ᵥ* U` for the linear evaluation check. -/
  evalComb : Fin l → F

/-- Honest completeness relation for `LigeroEvalClaim`: `claim.matrix = U * G` and
`ligeroEval U claim.rowWeights claim.colWeights = claim.value`. -/
@[expose] def ligeroEvalCodewordRel {F : Type} [Semiring F] {m l n : ℕ}
    (G : Matrix (Fin l) (Fin n) F) :
    LigeroEvalClaim F m l n → Matrix (Fin m) (Fin l) F → Prop :=
  fun claim U =>
    claim.matrix = U * G ∧ ligeroEval U claim.rowWeights claim.colWeights = claim.value

/-- Proximity-and-evaluation language for `G` at radius `e`: claims whose matrix lies within
column-Hamming distance `e` of `U * G` for some `m × l` witness matrix `U` satisfying
`ligeroEval U claim.rowWeights claim.colWeights = claim.value`. -/
@[expose] def ligeroEvalProximityLang {F : Type} [CommSemiring F] [DecidableEq F] {m l n : ℕ}
    (G : Matrix (Fin l) (Fin n) F) (e : ℕ) : Set (LigeroEvalClaim F m l n) :=
  {claim | ∃ U : Matrix (Fin m) (Fin l) F,
    hammingDist (Function.swap claim.matrix) (Function.swap (U * G)) ≤ e ∧
    ligeroEval U claim.rowWeights claim.colWeights = claim.value}

/-- Every honest claim satisfying `ligeroEvalCodewordRel G` belongs to
`ligeroEvalProximityLang G e` for all `e : ℕ`. -/
theorem mem_ligeroEvalProximityLang_of_rel {F : Type} [CommSemiring F] [DecidableEq F]
    {m l n : ℕ} {G : Matrix (Fin l) (Fin n) F} {claim : LigeroEvalClaim F m l n}
    {U : Matrix (Fin m) (Fin l) F} (hrel : ligeroEvalCodewordRel G claim U) (e : ℕ) :
    claim ∈ ligeroEvalProximityLang G e :=
  ⟨U, by rw [hrel.1, hammingDist_self]; exact Nat.zero_le e, hrel.2⟩

private lemma poly_eval_eq_coeff_vecMul_reedSolomonGenerator {F : Type*} [Field F] {n k : ℕ}
    (α : Fin n → F) {p : F[X]} (hp : p.degree < k) (j : Fin n) :
    p.eval (α j) = ((fun d : Fin k => p.coeff (d : ℕ)) ᵥ* reedSolomonGenerator α k) j := by
  by_cases hp0 : p = 0
  · subst hp0
    simp [Matrix.vecMul, dotProduct]
  · have hlt : p.natDegree < k := (Polynomial.natDegree_lt_iff_degree_lt hp0).2 hp
    rw [Polynomial.eval_eq_sum_range' hlt, ← Fin.sum_univ_eq_sum_range]
    simp only [Matrix.vecMul, dotProduct, reedSolomonGenerator_apply]

/-- **Berlekamp–Welch characterization of `ligeroEvalProximityLang` in the unique-decoding regime**
(`2 * e + k ≤ n`): with distinct evaluation points `α : Fin n → F`, a claim belongs to
`ligeroEvalProximityLang (reedSolomonGenerator α k) e` if and only if
`berlekampWelchInterleaved α e k (Function.swap claim.matrix)` returns a polynomial family `P`
whose coefficient matrix evaluates to `claim.value`. -/
theorem mem_ligeroEvalProximityLang_reedSolomon_iff {F : Type} [Field F] [DecidableEq F]
    {m k n e : ℕ} {α : Fin n → F} (hα : Function.Injective α) (hunique : 2 * e + k ≤ n)
    {claim : LigeroEvalClaim F m k n} :
    claim ∈ ligeroEvalProximityLang (reedSolomonGenerator α k) e ↔
      ∃ P : Fin m → F[X],
        berlekampWelchInterleaved α e k (Function.swap claim.matrix) = some P ∧
        ligeroEval (Matrix.of fun i d => (P i).coeff (d : ℕ))
          claim.rowWeights claim.colWeights = claim.value := by
  have hunique' : 2 * e + k ≤ Fintype.card (Fin n) := by simpa only [Fintype.card_fin] using hunique
  constructor
  · rintro ⟨U, hclose, heval⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · let P : Fin m → F[X] := fun _ => 0
      have hUG : Function.swap (U * reedSolomonGenerator α 0) = fun _ _ => 0 := by
        funext j i
        simp [Function.swap, Matrix.mul_apply]
      have hbw : berlekampWelchInterleaved α e 0 (Function.swap claim.matrix) = some P :=
        (berlekampWelchInterleaved_eq_some_iff hα hunique').2
          ⟨fun _ => WithBot.bot_lt_coe 0, by
            simpa only [P, Polynomial.eval_zero, hUG, hammingDist_comm] using hclose⟩
      refine ⟨P, hbw, ?_⟩
      have hU_eq : (Matrix.of fun i (d : Fin 0) => (P i).coeff (d : ℕ)) = U :=
        Matrix.ext fun _ d => d.elim0
      rwa [hU_eq]
    · let P : Fin m → F[X] := fun i => Polynomial.ofFn k (U i)
      have hdeg : ∀ i : Fin m, (P i).degree < k := fun i => Polynomial.ofFn_degree_lt (U i)
      have heval_UG : (fun j i => (P i).eval (α j)) =
          Function.swap (U * reedSolomonGenerator α k) := by
        funext j i
        simp only [P, Function.swap, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum,
          Polynomial.eval_monomial, Matrix.mul_apply, reedSolomonGenerator_apply]
      have hbw : berlekampWelchInterleaved α e k (Function.swap claim.matrix) = some P :=
        (berlekampWelchInterleaved_eq_some_iff hα hunique').2
          ⟨hdeg, by rwa [heval_UG, hammingDist_comm]⟩
      have hcoeff : (Matrix.of fun i (d : Fin k) => (P i).coeff (d : ℕ)) = U :=
        Matrix.ext fun i d => Polynomial.ofFn_coeff_eq_val_of_lt (U i) d.isLt
      exact ⟨P, hbw, by rwa [hcoeff]⟩
  · rintro ⟨P, hbw, heval⟩
    let U : Matrix (Fin m) (Fin k) F := Matrix.of fun i d => (P i).coeff (d : ℕ)
    have hdeg := degree_lt_of_berlekampWelchInterleaved_eq_some hbw
    have hdist := hammingDist_le_of_berlekampWelchInterleaved_eq_some hbw
    have heval_UG : (fun j i => (P i).eval (α j)) =
        Function.swap (U * reedSolomonGenerator α k) := by
      funext j i
      rw [poly_eval_eq_coeff_vecMul_reedSolomonGenerator α (hdeg i) j]
      rfl
    exact ⟨U, by rwa [heval_UG, hammingDist_comm] at hdist, heval⟩

/-- Round specification of `ligeroBatchEvalReduction`. -/
abbrev ligeroBatchEvalSpec (BatchChal : Type) (l n q : ℕ) (F : Type) : Spec :=
  [.verifier BatchChal,
   .prover (LigeroEvalReply F l) (OracleInterface.full (LigeroEvalReply F l)),
   .verifier (Fin q → Fin n)]

/-- Boolean verification predicate for `ligeroBatchEvalReduction`: checks the claimed dot product
upfront and verifies both `ligeroColumnCheck` (proximity) and `ligeroEvalCheck` (linear evaluation)
at all `q` queried columns. -/
@[expose] def ligeroBatchEvalVerify {F : Type} [Semiring F] [DecidableEq F] {m l n q : ℕ}
    (G : Matrix (Fin l) (Fin n) F) (claim : LigeroEvalClaim F m l n) (r : Fin m → F)
    (reply : LigeroEvalReply F l) (Q : Fin q → Fin n) : Bool :=
  decide (reply.evalComb ⬝ᵥ claim.colWeights = claim.value) &&
    decide (∀ t : Fin q,
      ligeroColumnCheck G claim.matrix r reply.proxComb (Q t) = true ∧
      ligeroEvalCheck G claim.matrix claim.rowWeights claim.colWeights claim.value
        reply.evalComb (Q t) = true)

/-- **Combined Ligero proximity-and-evaluation interactive reduction**: tests both interleaved
`e`-proximity of `claim.matrix` and `ligeroEval U claim.rowWeights claim.colWeights = claim.value`
using a single `q`-column query batch. -/
noncomputable def ligeroBatchEvalReduction {F BatchChal : Type}
    [Field F] [DecidableEq F] [Fintype BatchChal] [Nonempty BatchChal]
    (m : ℕ) (weights : BatchChal → (Fin m → F)) {l n : ℕ} [NeZero n]
    (G : Matrix (Fin l) (Fin n) F) (q : ℕ) :
    Reduction OracleSpec.empty OracleSpec.empty (ligeroBatchEvalSpec BatchChal l n q F)
      (LigeroEvalClaim F m l n) (Matrix (Fin m) (Fin l) F) Unit Unit where
  prover claim U :=
    pure (show BatchChal → ProbOracleComp OracleSpec.empty
        (ProbOracleComp OracleSpec.empty
          (LigeroEvalReply F l ×
            ((Fin q → Fin n) → ProbOracleComp OracleSpec.empty (Unit × Unit)))) from
      fun chal => pure (pure
        (⟨ligeroRowComb (weights chal) U, ligeroRowComb claim.rowWeights U⟩,
         fun _ => pure ((), ()))))
  verifier :=
    { samplers := (ProbComp.uniform BatchChal, ProbComp.uniform (Fin q → Fin n), ())
      decide := fun claim (chal, Q, _) => do
        let reply ← OracleComp.query
          (spec := OracleSpec.empty ⊕ₒ msgSpec (ligeroBatchEvalSpec BatchChal l n q F))
          (.inr (.inl ()))
        return if ligeroBatchEvalVerify G claim (weights chal) reply Q = true then some ()
          else none }

theorem ligeroBatchEvalReduction_outputOn {F BatchChal : Type}
    [Field F] [DecidableEq F] [Fintype BatchChal] [Nonempty BatchChal]
    (m : ℕ) (weights : BatchChal → (Fin m → F)) {l n : ℕ} [NeZero n]
    (G : Matrix (Fin l) (Fin n) F) (q : ℕ)
    (claim : LigeroEvalClaim F m l n) (chal : BatchChal) (reply : LigeroEvalReply F l)
    (Q : Fin q → Fin n) :
    (ligeroBatchEvalReduction m weights G q).verifier.outputOn claim (chal, reply, Q, ()) =
      if ligeroBatchEvalVerify G claim (weights chal) reply Q = true then some () else none := by
  rfl

/-- **Query locality of `ligeroBatchEvalReduction`**: the verifier accesses `claim.matrix` only at
the `q` queried columns `Q t` (`t : Fin q`). -/
theorem ligeroBatchEvalReduction_outputOn_congr {F BatchChal : Type}
    [Field F] [DecidableEq F] [Fintype BatchChal] [Nonempty BatchChal]
    {m l n : ℕ} [NeZero n] (weights : BatchChal → (Fin m → F))
    (G : Matrix (Fin l) (Fin n) F) (q : ℕ)
    {M₁ M₂ : Matrix (Fin m) (Fin n) F} (b : Fin m → F) (c : Fin l → F) (w : F)
    (chal : BatchChal) (reply : LigeroEvalReply F l) (Q : Fin q → Fin n)
    (hcols : ∀ t : Fin q, ∀ i : Fin m, M₁ i (Q t) = M₂ i (Q t)) :
    (ligeroBatchEvalReduction m weights G q).verifier.outputOn ⟨M₁, b, c, w⟩ (chal, reply, Q, ()) =
      (ligeroBatchEvalReduction m weights G q).verifier.outputOn
        ⟨M₂, b, c, w⟩ (chal, reply, Q, ()) := by
  rw [ligeroBatchEvalReduction_outputOn, ligeroBatchEvalReduction_outputOn]
  have hcol_eq (r : Fin m → F) (t : Fin q) : (r ᵥ* M₁) (Q t) = (r ᵥ* M₂) (Q t) := by
    rw [Matrix.vecMul_apply_eq_sum, Matrix.vecMul_apply_eq_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hcols t i]
  have hiff :
      (∀ t : Fin q,
        ligeroColumnCheck G M₁ (weights chal) reply.proxComb (Q t) = true ∧
        ligeroEvalCheck G M₁ b c w reply.evalComb (Q t) = true) ↔
      (∀ t : Fin q,
        ligeroColumnCheck G M₂ (weights chal) reply.proxComb (Q t) = true ∧
        ligeroEvalCheck G M₂ b c w reply.evalComb (Q t) = true) :=
    forall_congr' fun t => by
      simp only [ligeroColumnCheck, ligeroEvalCheck, decide_eq_true_eq, hcol_eq _ t]
  have hver_eq : ligeroBatchEvalVerify G ⟨M₁, b, c, w⟩ (weights chal) reply Q =
      ligeroBatchEvalVerify G ⟨M₂, b, c, w⟩ (weights chal) reply Q := by
    unfold ligeroBatchEvalVerify
    dsimp only
    rw [decide_eq_decide.2 hiff]
  rw [hver_eq]

/-- **Completeness of `ligeroBatchEvalReduction`**: every honest claim `claim.matrix = U * G` with
`ligeroEval U claim.rowWeights claim.colWeights = claim.value` is accepted with error `0`. -/
theorem ligeroBatchEvalReduction_complete {F BatchChal : Type}
    [Field F] [DecidableEq F] [Fintype BatchChal] [Nonempty BatchChal]
    (m : ℕ) (weights : BatchChal → (Fin m → F)) {l n : ℕ} [NeZero n]
    (G : Matrix (Fin l) (Fin n) F) (q : ℕ) :
    (ligeroBatchEvalReduction m weights G q).Complete
      World.plain (ligeroEvalCodewordRel G) Accept 0 := by
  rintro ⟨M, b, c, w⟩ U ⟨hM, hval⟩
  dsimp only at hM hval
  subst hM hval
  rw [Reduction.run, World.plain_eval_execute, PMF.toOuterMeasure_map_apply]
  simp only [ligeroBatchEvalReduction, runStrategy, plainLaw_bind, plainLaw_pure,
    plainLaw_sample, PMF.pure_bind, PMF.bind_bind]
  rw [PMF.toOuterMeasure_bind_apply]
  refine Cslib.Probability.PMF.tsum_mul_le_of_forall_le _ fun chal => ?_
  rw [PMF.toOuterMeasure_bind_apply]
  refine Cslib.Probability.PMF.tsum_mul_le_of_forall_le _ fun Q => le_of_eq ?_
  have hver : ligeroBatchEvalVerify G ⟨U * G, b, c, ligeroEval U b c⟩ (weights chal)
      ⟨ligeroRowComb (weights chal) U, ligeroRowComb b U⟩ Q = true := by
    simp only [ligeroBatchEvalVerify, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨rfl, fun t => ⟨ligeroColumnCheck_honest G U (weights chal) (Q t),
      ligeroEvalCheck_honest G U b c (Q t)⟩⟩
  refine (PMF.toOuterMeasure_pure_apply _ _).trans (ite_eq_right fun h => h ⟨?_, trivial⟩)
  exact (ligeroBatchEvalReduction_outputOn m weights G q _ chal _ Q).trans (ite_eq_left hver)

private lemma ligeroBatchEvalReduction_rbrSound_of_rowBound
    {F BatchChal : Type} [Field F] [DecidableEq F]
    [Fintype BatchChal] [Nonempty BatchChal]
    (m : ℕ) (weights : BatchChal → (Fin m → F)) {l n q e : ℕ} [NeZero n]
    (G : Matrix (Fin l) (Fin n) F)
    (hmin : 2 * (e : ℕ∞) < minDist (codeOfGenerator G : Set (Fin n → F)))
    (hinj : Function.Injective (fun v : Fin l → F => v ᵥ* G))
    (ε₁ : ℝ≥0∞)
    (hrow : ∀ M : Matrix (Fin m) (Fin n) F, M ∉ ligeroProximityLang m G e →
      (PMF.uniformOfFintype BatchChal).toOuterMeasure
        {chal | ∃ cw ∈ codeOfGenerator G, hammingDist (weights chal ᵥ* M) cw ≤ e} ≤ ε₁) :
    (ligeroBatchEvalReduction m weights G q).verifier.RbrSound
      (ligeroEvalProximityLang G e) Set.univ
      (ε₁, (((n - (e + 1) : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) ^ q, ()) := by
  let round1Lucky (claim : LigeroEvalClaim F m l n) (chal : BatchChal) : Prop :=
    claim ∈ ligeroEvalProximityLang G e ∨
      (claim.matrix ∉ ligeroProximityLang m G e ∧
        ∃ cw ∈ codeOfGenerator G, hammingDist (weights chal ᵥ* claim.matrix) cw ≤ e)
  refine ⟨fun claim pfx => match pfx with
    | none => claim ∈ ligeroEvalProximityLang G e
    | some (chal, none) => round1Lucky claim chal
    | some (chal, some (_, none)) => round1Lucky claim chal
    | some (chal, some (reply, some (Q, _))) =>
        ligeroBatchEvalVerify G claim (weights chal) reply Q = true,
    fun claim hclaim => hclaim,
    fun claim => ⟨fun hnot => ?_, fun chal => ⟨fun hS _ h => hS h, fun reply => ⟨fun hS => ?_,
      fun Q hS ⟨_, _, hout⟩ => ?_⟩⟩⟩⟩
  · change (ProbComp.eval (ProbComp.uniform BatchChal)).toOuterMeasure
      {chal | round1Lucky claim chal} ≤ ε₁
    rw [ProbComp.eval_uniform]
    by_cases hprox : claim.matrix ∈ ligeroProximityLang m G e
    · have hemp : {chal : BatchChal | round1Lucky claim chal} = ∅ := by
        ext chal
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, round1Lucky, not_or,
          not_and]
        exact ⟨hnot, fun h => False.elim (h hprox)⟩
      simp only [hemp, MeasureTheory.measure_empty, zero_le]
    · refine ((PMF.uniformOfFintype BatchChal).toOuterMeasure.mono fun chal h => ?_).trans
        (hrow claim.matrix hprox)
      exact (h.resolve_left hnot).2
  · change (ProbComp.eval (ProbComp.uniform (Fin q → Fin n))).toOuterMeasure
      {Q | ligeroBatchEvalVerify G claim (weights chal) reply Q = true} ≤ _
    rw [ProbComp.eval_uniform]
    by_cases hprox : claim.matrix ∈ ligeroProximityLang m G e
    · obtain ⟨V, hV, hdist⟩ := hprox
      have hexU : ∀ i : Fin m, ∃ u : Fin l → F, u ᵥ* G = fun j => V j i :=
        fun i => mem_codeOfGenerator.1 (mem_interleavedLinear.1 hV i)
      let U : Matrix (Fin m) (Fin l) F := Matrix.of fun i d => (hexU i).choose d
      have hUG : Function.swap (U * G) = V := by
        funext j i
        change (U * G) i j = V j i
        have hi := congrFun (hexU i).choose_spec j
        simpa only [Matrix.mul_apply, Matrix.vecMul, dotProduct, U, Matrix.of_apply] using hi
      have hclose : hammingDist (Function.swap claim.matrix) (Function.swap (U * G)) ≤ e := by
        rwa [hUG]
      have hfalse : ligeroEval U claim.rowWeights claim.colWeights ≠ claim.value := fun heval =>
        hS (Or.inl ⟨U, hclose, heval⟩)
      refine ((PMF.uniformOfFintype (Fin q → Fin n)).toOuterMeasure.mono fun Q hQ => ?_).trans
        (toOuterMeasure_ligeroEvalCheck_false_le G hmin hinj hclose
          claim.rowWeights claim.colWeights claim.value hfalse reply.evalComb)
      simp only [Set.mem_ofPred_eq, ligeroBatchEvalVerify, Bool.and_eq_true,
        decide_eq_true_eq] at hQ ⊢
      exact fun t => (hQ.2 t).2
    · have hfar : e < hammingDist (weights chal ᵥ* claim.matrix) (reply.proxComb ᵥ* G) := by
        by_contra hle
        exact hS (Or.inr ⟨hprox, reply.proxComb ᵥ* G,
          vecMul_mem_codeOfGenerator G reply.proxComb, Nat.le_of_not_lt hle⟩)
      refine ((PMF.uniformOfFintype (Fin q → Fin n)).toOuterMeasure.mono fun Q hQ => ?_).trans
        (toOuterMeasure_ligeroColumnCheck_all_le G claim.matrix (weights chal) reply.proxComb hfar)
      simp only [Set.mem_ofPred_eq, ligeroBatchEvalVerify, Bool.and_eq_true,
        decide_eq_true_eq] at hQ ⊢
      exact fun t => (hQ.2 t).1
  · rw [ligeroBatchEvalReduction_outputOn] at hout
    split_ifs at hout with hver
    exact hS hver

private lemma two_mul_lt_minDist_reedSolomonGenerator {F : Type} [Field F] [DecidableEq F]
    {k n e : ℕ} {α : Fin n → F} (hα : Function.Injective α) (hunique : 2 * e + k ≤ n) :
    2 * (e : ℕ∞) < minDist (codeOfGenerator (reedSolomonGenerator α k) : Set (Fin n → F)) := by
  rw [codeOfGenerator_reedSolomonGenerator]
  refine lt_of_lt_of_le ?_ (le_minDist_reedSolomon hα k)
  rw [Fintype.card_fin]
  exact_mod_cast (by omega : 2 * e < n - k + 1)

/-- **Round-by-round soundness of full-vector `ligeroBatchEvalReduction` across the Reed–Solomon
unique-decoding radius** (`2 * e + k ≤ n`): rejects every claim outside
`ligeroEvalProximityLang (reedSolomonGenerator α k) e` with per-round errors `n / |F|` and
`((n - (e + 1)) / n) ^ q`. -/
theorem ligeroAffineEvalReduction_reedSolomon_rbrSound
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (m : ℕ) {k n q e : ℕ} [NeZero n] {α : Fin n → F}
    (hα : Function.Injective α) (hunique : 2 * e + k ≤ n) :
    (ligeroBatchEvalReduction m (id : (Fin m → F) → (Fin m → F))
      (reedSolomonGenerator α k) q).verifier.RbrSound
      (ligeroEvalProximityLang (reedSolomonGenerator α k) e) Set.univ
      ((n : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞),
       (((n - (e + 1) : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) ^ q, ()) := by
  refine ligeroBatchEvalReduction_rbrSound_of_rowBound m id (reedSolomonGenerator α k)
    (two_mul_lt_minDist_reedSolomonGenerator hα hunique)
    (vecMul_reedSolomonGenerator_injective hα (by omega)) _ fun M hM => ?_
  have hbound := toOuterMeasure_sum_smul_reedSolomon_close_le hα
    (by simpa only [Fintype.card_fin] using hunique)
    (forall_lt_interleaved_reedSolomon_of_not_mem hM)
  simpa only [codeOfGenerator_reedSolomonGenerator, vecMul_eq_sum_smul_swap, id_eq,
    Fintype.card_fin] using hbound

/-- **Plain-model soundness of full-vector `ligeroBatchEvalReduction` across the Reed–Solomon
unique-decoding radius** (`2 * e + k ≤ n`). -/
theorem ligeroAffineEvalReduction_reedSolomon_sound
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (m : ℕ) {k n q e : ℕ} [NeZero n] {α : Fin n → F}
    (hα : Function.Injective α) (hunique : 2 * e + k ≤ n) :
    (ligeroBatchEvalReduction m (id : (Fin m → F) → (Fin m → F))
      (reedSolomonGenerator α k) q).verifier.Sound
      (oP := OracleSpec.empty) World.plain
      (ligeroEvalProximityLang (reedSolomonGenerator α k) e) Set.univ
      ((n : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) +
       (((n - (e + 1) : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) ^ q) := by
  have h := (ligeroAffineEvalReduction_reedSolomon_rbrSound m (q := q) hα hunique).sound
  simpa only [PerChallenge.sum, add_zero] using h

/-- **Round-by-round soundness of single-scalar `ligeroBatchEvalReduction` across the Reed–Solomon
unique-decoding radius** (`2 * e + k ≤ n`): rejects every claim outside
`ligeroEvalProximityLang (reedSolomonGenerator α k) e` with per-round errors
`((m - 1) * n) / |F|` and `((n - (e + 1)) / n) ^ q`. -/
theorem ligeroCurveEvalReduction_reedSolomon_rbrSound
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (m : ℕ) {k n q e : ℕ} [NeZero n] {α : Fin n → F}
    (hα : Function.Injective α) (hunique : 2 * e + k ≤ n) :
    (ligeroBatchEvalReduction m (ligeroPowWeights m)
      (reedSolomonGenerator α k) q).verifier.RbrSound
      (ligeroEvalProximityLang (reedSolomonGenerator α k) e) Set.univ
      ((((m - 1) * n : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞),
       (((n - (e + 1) : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) ^ q, ()) := by
  refine ligeroBatchEvalReduction_rbrSound_of_rowBound m (ligeroPowWeights m)
    (reedSolomonGenerator α k) (two_mul_lt_minDist_reedSolomonGenerator hα hunique)
    (vecMul_reedSolomonGenerator_injective hα (by omega)) _ fun M hM => ?_
  have hbound := toOuterMeasure_sum_pow_smul_reedSolomon_close_le hα
    (by simpa only [Fintype.card_fin] using hunique)
    (forall_lt_interleaved_reedSolomon_of_not_mem hM)
  simpa only [codeOfGenerator_reedSolomonGenerator, vecMul_ligeroPowWeights_eq_sum_pow,
    Fintype.card_fin] using hbound

/-- **Plain-model soundness of single-scalar `ligeroBatchEvalReduction` across the Reed–Solomon
unique-decoding radius** (`2 * e + k ≤ n`). -/
theorem ligeroCurveEvalReduction_reedSolomon_sound
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (m : ℕ) {k n q e : ℕ} [NeZero n] {α : Fin n → F}
    (hα : Function.Injective α) (hunique : 2 * e + k ≤ n) :
    (ligeroBatchEvalReduction m (ligeroPowWeights m)
      (reedSolomonGenerator α k) q).verifier.Sound
      (oP := OracleSpec.empty) World.plain
      (ligeroEvalProximityLang (reedSolomonGenerator α k) e) Set.univ
      ((((m - 1) * n : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) +
       (((n - (e + 1) : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) ^ q) := by
  have h := (ligeroCurveEvalReduction_reedSolomon_rbrSound m (q := q) hα hunique).sound
  simpa only [PerChallenge.sum, add_zero] using h

end BatchEvalReduction

/-! ### Part 3: Direct Batched Reed–Solomon Proximity `PublicCoinIOP` & Two-Channel BCS/ROM -/

section BatchProximityIOP

/-- Per-round public-coin challenge record for `rsBatchProximityIOP`: carries a row-batching
challenge `batchChal : BatchChal` (consumed after round `0`) and `q` column query indices
`queryIdxs : Fin q → Fin (2 ^ d)` (consumed at verification after round `1`). -/
@[ext] structure LigeroIOPChal (BatchChal : Type) (d q : ℕ) where
  /-- Row-combination batching challenge sampled after round `0`. -/
  batchChal : BatchChal
  /-- `q` column query indices sampled in the final round. -/
  queryIdxs : Fin q → Fin (2 ^ d)

/-- Equivalence between `LigeroIOPChal BatchChal d q` and `BatchChal × (Fin q → Fin (2 ^ d))`. -/
@[expose] def LigeroIOPChal.equivProd (BatchChal : Type) (d q : ℕ) :
    LigeroIOPChal BatchChal d q ≃ BatchChal × (Fin q → Fin (2 ^ d)) where
  toFun c := (c.batchChal, c.queryIdxs)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance {BatchChal : Type} [DecidableEq BatchChal] {d q : ℕ} :
    DecidableEq (LigeroIOPChal BatchChal d q) :=
  (LigeroIOPChal.equivProd BatchChal d q).decidableEq

instance {BatchChal : Type} [Fintype BatchChal] {d q : ℕ} :
    Fintype (LigeroIOPChal BatchChal d q) :=
  Fintype.ofEquiv _ (LigeroIOPChal.equivProd BatchChal d q).symm

instance {BatchChal : Type} [Nonempty BatchChal] {d q : ℕ} :
    Nonempty (LigeroIOPChal BatchChal d q) :=
  ⟨⟨Classical.arbitrary BatchChal, fun _ => ⟨0, Nat.two_pow_pos d⟩⟩⟩

/-- Exact cardinality of `LigeroIOPChal BatchChal d q`. -/
theorem card_ligeroIOPChal {BatchChal : Type} [Fintype BatchChal] (d q : ℕ) :
    Fintype.card (LigeroIOPChal BatchChal d q) = Fintype.card BatchChal * (2 ^ d) ^ q := by
  rw [Fintype.card_congr (LigeroIOPChal.equivProd BatchChal d q), Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- Verifier decision function of `rsBatchProximityIOP`: checks that `answers` has length `k` and
verifies `ligeroColumnCheck` at all `q` queried columns `(chals 1).queryIdxs s`. -/
@[expose] def rsBatchProximityDecide {F BatchChal : Type} [Semiring F] [DecidableEq F]
    {m d : ℕ} (k : ℕ) (α : Fin (2 ^ d) → F) (q : ℕ) (weights : BatchChal → (Fin m → F))
    (M : Matrix (Fin m) (Fin (2 ^ d)) F)
    (chals : Fin 2 → LigeroIOPChal BatchChal d q) (answers : List F) : Bool :=
  decide (answers.length = k) &&
    let v : Fin k → F := fun t => answers.getD t.val 0
    (List.finRange q).all fun s =>
      ligeroColumnCheck (reedSolomonGenerator α k) M (weights (chals 0).batchChal) v
        ((chals 1).queryIdxs s)

/-- **Query locality of `rsBatchProximityDecide`**: the decision depends on `M` only at the `q`
queried columns `(chals 1).queryIdxs s` (`s : Fin q`). -/
theorem rsBatchProximityDecide_congr_cols {F BatchChal : Type} [Semiring F] [DecidableEq F]
    {m d : ℕ} (k : ℕ) (α : Fin (2 ^ d) → F) (q : ℕ) (weights : BatchChal → (Fin m → F))
    {M₁ M₂ : Matrix (Fin m) (Fin (2 ^ d)) F}
    (chals : Fin 2 → LigeroIOPChal BatchChal d q) (answers : List F)
    (hcols : ∀ s : Fin q, ∀ i : Fin m,
      M₁ i ((chals 1).queryIdxs s) = M₂ i ((chals 1).queryIdxs s)) :
    rsBatchProximityDecide k α q weights M₁ chals answers =
      rsBatchProximityDecide k α q weights M₂ chals answers := by
  simp only [rsBatchProximityDecide]
  refine congrArg (decide (answers.length = k) && ·)
    (congrArg (List.all (List.finRange q)) (funext fun s => ?_))
  simp only [ligeroColumnCheck, decide_eq_decide]
  have hsum : (weights (chals 0).batchChal ᵥ* M₁) ((chals 1).queryIdxs s) =
      (weights (chals 0).batchChal ᵥ* M₂) ((chals 1).queryIdxs s) := by
    rw [Matrix.vecMul_apply_eq_sum, Matrix.vecMul_apply_eq_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hcols s i]
  rw [hsum]

/-- **2-round batched Reed–Solomon proximity `PublicCoinIOP`** (`k ≤ 2 ^ d` over domain
`Fin (2 ^ d)`):
* **Round `0`:** zero announcement table (`0` openings), followed by batching challenge
  `(chals 0).batchChal`.
* **Round `1`:** honest prover commits the combined message `ligeroRowComb r U : Fin k → F` in the
  first `k` positions of `OracleTable d F`; verifier opens those `k` positions
  (`queries.length = k`) and checks `ligeroColumnCheck` at the `q` columns `(chals 1).queryIdxs`. -/
@[expose] def rsBatchProximityIOP {F BatchChal : Type} [Semiring F] [DecidableEq F]
    (m : ℕ) {d k : ℕ} (hk : k ≤ 2 ^ d) (α : Fin (2 ^ d) → F) (q : ℕ)
    (weights : BatchChal → (Fin m → F)) :
    PublicCoinIOP 2 d (Matrix (Fin m) (Fin (2 ^ d)) F) (Matrix (Fin m) (Fin k) F) F
      (LigeroIOPChal BatchChal d q) where
  proveRound j _ U prev :=
    match j with
    | ⟨0, _⟩ => fun _ => 0
    | ⟨1, _⟩ =>
      let r := weights (prev ⟨0, Nat.zero_lt_one⟩).batchChal
      fun idx => if h : idx.val < k then ligeroRowComb r U ⟨idx.val, h⟩ else 0
  queries _ _ :=
    List.ofFn fun t : Fin k => ((1 : Fin 2), ⟨t.val, lt_of_lt_of_le t.isLt hk⟩)
  decide M chals answers :=
    rsBatchProximityDecide k α q weights M chals answers

/-- Full-vector (`Fin m → F`) specialization of `rsBatchProximityIOP`. -/
abbrev rsAffineBatchProximityIOP {F : Type} [Semiring F] [DecidableEq F]
    (m : ℕ) {d k : ℕ} (hk : k ≤ 2 ^ d) (α : Fin (2 ^ d) → F) (q : ℕ) :
    PublicCoinIOP 2 d (Matrix (Fin m) (Fin (2 ^ d)) F) (Matrix (Fin m) (Fin k) F) F
      (LigeroIOPChal (Fin m → F) d q) :=
  rsBatchProximityIOP m hk α q id

/-- Single-scalar power (`z : F`) specialization of `rsBatchProximityIOP`. -/
abbrev rsCurveBatchProximityIOP {F : Type} [Semiring F] [DecidableEq F]
    (m : ℕ) {d k : ℕ} (hk : k ≤ 2 ^ d) (α : Fin (2 ^ d) → F) (q : ℕ) :
    PublicCoinIOP 2 d (Matrix (Fin m) (Fin (2 ^ d)) F) (Matrix (Fin m) (Fin k) F) F
      (LigeroIOPChal F d q) :=
  rsBatchProximityIOP m hk α q (ligeroPowWeights m)

@[simp]
theorem length_rsBatchProximityIOP_queries {F BatchChal : Type} [Semiring F] [DecidableEq F]
    (m : ℕ) {d k : ℕ} (hk : k ≤ 2 ^ d) (α : Fin (2 ^ d) → F) (q : ℕ)
    (weights : BatchChal → (Fin m → F)) (M : Matrix (Fin m) (Fin (2 ^ d)) F)
    (chals : Fin 2 → LigeroIOPChal BatchChal d q) :
    ((rsBatchProximityIOP m hk α q weights).queries M chals).length = k := by
  simp [rsBatchProximityIOP]

/-- Pointwise characterization of `iopVerify` for `rsBatchProximityIOP`. -/
theorem iopVerify_rsBatchProximityIOP_eq_true_iff {F BatchChal : Type} [Semiring F] [DecidableEq F]
    (m : ℕ) {d k : ℕ} (hk : k ≤ 2 ^ d) (α : Fin (2 ^ d) → F) (q : ℕ)
    (weights : BatchChal → (Fin m → F)) (M : Matrix (Fin m) (Fin (2 ^ d)) F)
    (chals : Fin 2 → LigeroIOPChal BatchChal d q) (oracles : Fin 2 → OracleTable d F) :
    iopVerify (rsBatchProximityIOP m hk α q weights) M chals oracles = true ↔
      ∀ s : Fin q,
        ligeroColumnCheck (reedSolomonGenerator α k) M (weights (chals 0).batchChal)
          (fun t : Fin k => oracles 1 ⟨t.val, lt_of_lt_of_le t.isLt hk⟩)
          ((chals 1).queryIdxs s) = true := by
  have hget (t : Fin k) :
      (iopAnswers (rsBatchProximityIOP m hk α q weights) M chals oracles).getD t.val 0 =
        oracles 1 ⟨t.val, lt_of_lt_of_le t.isLt hk⟩ := by
    have hlt :
        t.val < (iopAnswers (rsBatchProximityIOP m hk α q weights) M chals oracles).length := by
      simpa only [length_iopAnswers, length_rsBatchProximityIOP_queries] using t.isLt
    rw [List.getD_eq_getElem _ _ hlt]
    simp [iopAnswers, rsBatchProximityIOP]
  have hv :
      (fun t : Fin k =>
        (iopAnswers (rsBatchProximityIOP m hk α q weights) M chals oracles).getD t.val 0) =
      (fun t : Fin k => oracles 1 ⟨t.val, lt_of_lt_of_le t.isLt hk⟩) :=
    funext hget
  have hdec : (iopVerify (rsBatchProximityIOP m hk α q weights) M chals oracles) =
      rsBatchProximityDecide k α q weights M chals
        (iopAnswers (rsBatchProximityIOP m hk α q weights) M chals oracles) := rfl
  rw [hdec]
  simp only [rsBatchProximityDecide, length_iopAnswers, length_rsBatchProximityIOP_queries,
    decide_true, Bool.true_and, hv, List.all_eq_true, List.mem_finRange, forall_true_left]

/-- **Perfect IOP completeness of `rsBatchProximityIOP`**. -/
theorem rsBatchProximityIOP_complete {F BatchChal : Type} [Semiring F] [DecidableEq F]
    (m : ℕ) {d k : ℕ} (hk : k ≤ 2 ^ d) (α : Fin (2 ^ d) → F) (q : ℕ)
    (weights : BatchChal → (Fin m → F)) :
    IOPCompleteness (rsBatchProximityIOP m hk α q weights)
      (ligeroCodewordRel m (reedSolomonGenerator α k)) := by
  intro M U hrel chals
  subst hrel
  rw [iopVerify_rsBatchProximityIOP_eq_true_iff]
  intro s
  have horacle :
      (fun t : Fin k =>
        iopProverOracles (rsBatchProximityIOP m hk α q weights)
          (U * reedSolomonGenerator α k) U chals 1 ⟨t.val, lt_of_lt_of_le t.isLt hk⟩) =
      ligeroRowComb (weights (chals 0).batchChal) U := by
    funext t
    simp only [iopProverOracles, rsBatchProximityIOP, prefixChallenges, t.isLt, ↓reduceDIte,
      Fin.eta]
    rfl
  rw [horacle]
  exact ligeroColumnCheck_honest (reedSolomonGenerator α k) U (weights (chals 0).batchChal)
    ((chals 1).queryIdxs s)

/-- **Two-channel BCS random-oracle completeness of `rsBatchProximityIOP`**. -/
theorem rsBatchProximityBCS_honestROMGame_eq_pure_true {F BatchChal : Type}
    [Semiring F] [DecidableEq F] [DecidableEq BatchChal] [Fintype BatchChal] [Nonempty BatchChal]
    (m : ℕ) {d k : ℕ} (hk : k ≤ 2 ^ d) (α : Fin (2 ^ d) → F) (q : ℕ)
    (weights : BatchChal → (Fin m → F)) (encSym : F → List Bool)
    {M : Matrix (Fin m) (Fin (2 ^ d)) F} {U : Matrix (Fin m) (Fin k) F}
    (hrel : ligeroCodewordRel m (reedSolomonGenerator α k) M U) (σ : ℕ) :
    bcsHonestROMGame (rsBatchProximityIOP m hk α q weights) encSym M U σ = PMF.pure true :=
  bcsHonestROMGame_eq_pure_true (rsBatchProximityIOP_complete m hk α q weights) encSym hrel σ

/-- **BCS random-oracle verifier Merkle hash query bound for `rsBatchProximityIOP`**: when all
opened authentication paths have length at most `L_path`, `bcsVerifyROM` makes at most
`k * (L_path + 1)` Merkle hash queries. -/
theorem isCostBounded_bcsMTCost_rsBatchProximityVerifyROM {F BatchChal : Type}
    [Semiring F] [DecidableEq F]
    (m : ℕ) {d k : ℕ} (hk : k ≤ 2 ^ d) (α : Fin (2 ^ d) → F) (q : ℕ)
    (weights : BatchChal → (Fin m → F)) (encSym : F → List Bool)
    (M : Matrix (Fin m) (Fin (2 ^ d)) F) (prf : BCSProof 2 F) {L_path : ℕ}
    (hops : ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    IsCostBounded bcsMTCost
      (bcsVerifyROM (rsBatchProximityIOP m hk α q weights) encSym M prf)
      (k * (L_path + 1)) :=
  isCostBounded_bcsMTCost_bcsVerifyROM_of_queries_le _ encSym M prf
    (fun chals => (length_rsBatchProximityIOP_queries m hk α q weights M chals).le) hops

/-- Doomed-prefix predicate for `rsBatchProximityIOP`. -/
@[expose] def rsBatchDoomed {F BatchChal : Type} [Field F] [DecidableEq F]
    (m : ℕ) {d k : ℕ} (hk : k ≤ 2 ^ d) (α : Fin (2 ^ d) → F) (q e : ℕ)
    (weights : BatchChal → (Fin m → F))
    (M : Matrix (Fin m) (Fin (2 ^ d)) F) :
    List (OracleTable d F × LigeroIOPChal BatchChal d q) → Prop
  | [] => M ∉ ligeroProximityLang m (reedSolomonGenerator α k) e
  | [(_, chal₀)] => ∀ cw ∈ reedSolomon α k, e < hammingDist (weights chal₀.batchChal ᵥ* M) cw
  | [(_, chal₀), (π₁, chal₁)] =>
      ¬ ∀ s : Fin q,
        ligeroColumnCheck (reedSolomonGenerator α k) M (weights chal₀.batchChal)
          (fun t : Fin k => π₁ ⟨t.val, lt_of_lt_of_le t.isLt hk⟩) (chal₁.queryIdxs s) = true
  | _ :: _ :: _ :: _ => True

/-- Non-escaping round step predicate for `rsBatchProximityIOP`. -/
@[expose] def rsBatchGoodStep {F BatchChal : Type} [Field F] [DecidableEq F]
    (m : ℕ) {d k : ℕ} (hk : k ≤ 2 ^ d) (α : Fin (2 ^ d) → F) (q e : ℕ)
    (weights : BatchChal → (Fin m → F))
    (M : Matrix (Fin m) (Fin (2 ^ d)) F)
    (pref : List (OracleTable d F × LigeroIOPChal BatchChal d q))
    (π : OracleTable d F) (chal : LigeroIOPChal BatchChal d q) : Prop :=
  match pref with
  | [] => ∀ cw ∈ reedSolomon α k, e < hammingDist (weights chal.batchChal ᵥ* M) cw
  | [(_, chal₀)] =>
      ¬ ∀ s : Fin q,
        ligeroColumnCheck (reedSolomonGenerator α k) M (weights chal₀.batchChal)
          (fun t : Fin k => π ⟨t.val, lt_of_lt_of_le t.isLt hk⟩) (chal.queryIdxs s) = true
  | _ :: _ :: _ => True

/-- **Unconditional `IOPRoundByRoundSoundness` of `rsBatchProximityIOP`** at any proximity radius
`e : ℕ`. -/
theorem rsBatchProximityIOP_rbrSound {F BatchChal : Type} [Field F] [DecidableEq F]
    (m : ℕ) {d k : ℕ} (hk : k ≤ 2 ^ d) (α : Fin (2 ^ d) → F) (q e : ℕ)
    (weights : BatchChal → (Fin m → F)) :
    IOPRoundByRoundSoundness (rsBatchProximityIOP m hk α q weights)
      (ligeroProximityLang m (reedSolomonGenerator α k) e)
      (rsBatchDoomed m hk α q e weights)
      (rsBatchGoodStep m hk α q e weights) where
  init_doomed _ hM := hM
  step_doomed M pref π chal _ hgood := by
    rcases pref with _ | ⟨e₀, _ | ⟨e₁, rest⟩⟩
    · exact hgood
    · exact hgood
    · rw [List.cons_append, List.cons_append]
      rcases h : rest ++ [(π, chal)] with _ | ⟨_, _⟩
      · simp at h
      · trivial
  reject_of_doomed M oracles chals hd := by
    have hofFn : (List.ofFn fun j : Fin 2 => (oracles j, chals j)) =
        [(oracles 0, chals 0), (oracles 1, chals 1)] := rfl
    rw [hofFn] at hd
    exact Bool.eq_false_iff.2 fun hver =>
      hd ((iopVerify_rsBatchProximityIOP_eq_true_iff m hk α q weights M chals oracles).1 hver)

private lemma rsBatchProximityIOP_round0_escape_le {F BatchChal : Type}
    [Field F] [DecidableEq F] [Fintype BatchChal] [Nonempty BatchChal]
    (m : ℕ) {d k : ℕ} (hk : k ≤ 2 ^ d) (α : Fin (2 ^ d) → F) (q e : ℕ)
    (weights : BatchChal → (Fin m → F)) {ε_row : ℝ≥0∞}
    {M : Matrix (Fin m) (Fin (2 ^ d)) F}
    (hrowM : (PMF.uniformOfFintype BatchChal).toOuterMeasure
      {b | ∃ cw ∈ reedSolomon α k, hammingDist (weights b ᵥ* M) cw ≤ e} ≤ ε_row)
    (π : OracleTable d F) :
    (PMF.uniformOfFintype (LigeroIOPChal BatchChal d q)).toOuterMeasure
      {chal | ¬ rsBatchGoodStep m hk α q e weights M [] π chal} ≤ ε_row := by
  let P_row : BatchChal → Prop :=
    fun b => ∃ cw ∈ reedSolomon α k, hammingDist (weights b ᵥ* M) cw ≤ e
  have hset : {chal : LigeroIOPChal BatchChal d q |
        ¬ rsBatchGoodStep m hk α q e weights M [] π chal} =
      {chal | P_row (LigeroIOPChal.equivProd BatchChal d q chal).1} := by
    ext chal
    simp only [Set.mem_ofPred_eq, rsBatchGoodStep, P_row, LigeroIOPChal.equivProd,
      Equiv.coe_fn_mk, not_forall, not_lt]
    exact ⟨fun ⟨cw, hcw, hle⟩ => ⟨cw, hcw, hle⟩, fun ⟨cw, hcw, hle⟩ => ⟨cw, hcw, hle⟩⟩
  rw [hset, Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_fst
    (LigeroIOPChal.equivProd BatchChal d q) P_row]
  exact hrowM

private lemma rsBatchProximityIOP_round1_escape_le {F BatchChal : Type}
    [Field F] [DecidableEq F] [Fintype BatchChal] [Nonempty BatchChal]
    (m : ℕ) {d k : ℕ} (hk : k ≤ 2 ^ d) (α : Fin (2 ^ d) → F) (q e : ℕ)
    (weights : BatchChal → (Fin m → F))
    {M : Matrix (Fin m) (Fin (2 ^ d)) F}
    (π₀ : OracleTable d F) (chal₀ : LigeroIOPChal BatchChal d q) (π : OracleTable d F)
    (hd : rsBatchDoomed m hk α q e weights M [(π₀, chal₀)]) :
    (PMF.uniformOfFintype (LigeroIOPChal BatchChal d q)).toOuterMeasure
      {chal | ¬ rsBatchGoodStep m hk α q e weights M [(π₀, chal₀)] π chal} ≤
      (((2 ^ d - (e + 1) : ℕ) : ℝ≥0∞) / (2 ^ d : ℝ≥0∞)) ^ q := by
  have : NeZero (2 ^ d) := ⟨Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos d)⟩
  let v : Fin k → F := fun t => π ⟨t.val, lt_of_lt_of_le t.isLt hk⟩
  have hv_mem : v ᵥ* reedSolomonGenerator α k ∈ reedSolomon α k := by
    rw [← codeOfGenerator_reedSolomonGenerator]
    exact vecMul_mem_codeOfGenerator _ v
  let eSwap := (LigeroIOPChal.equivProd BatchChal d q).trans (Equiv.prodComm _ _)
  let P_col : (Fin q → Fin (2 ^ d)) → Prop := fun Q =>
    ∀ s : Fin q,
      ligeroColumnCheck (reedSolomonGenerator α k) M (weights chal₀.batchChal) v (Q s) = true
  have hset : {chal : LigeroIOPChal BatchChal d q |
        ¬ rsBatchGoodStep m hk α q e weights M [(π₀, chal₀)] π chal} =
      {chal | P_col (eSwap chal).1} := by
    ext chal
    simp only [Set.mem_ofPred_eq, rsBatchGoodStep, P_col, not_not, eSwap, Equiv.trans_apply,
      LigeroIOPChal.equivProd, Equiv.coe_fn_mk, Equiv.prodComm_apply, Prod.fst_swap, v]
  rw [hset, Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_fst eSwap P_col]
  simpa only [P_col, Nat.cast_pow, Nat.cast_ofNat] using
    toOuterMeasure_ligeroColumnCheck_all_le (q := q) (reedSolomonGenerator α k) M
      (weights chal₀.batchChal) v (hd _ hv_mem)

private lemma rsBatchProximityIOP_escape_le {F BatchChal : Type}
    [Field F] [DecidableEq F] [Fintype BatchChal] [Nonempty BatchChal]
    (m : ℕ) {d k : ℕ} (hk : k ≤ 2 ^ d) (α : Fin (2 ^ d) → F) (q e : ℕ)
    (weights : BatchChal → (Fin m → F)) {ε_row : ℝ≥0∞}
    (hrow : ∀ M : Matrix (Fin m) (Fin (2 ^ d)) F,
      M ∉ ligeroProximityLang m (reedSolomonGenerator α k) e →
      (PMF.uniformOfFintype BatchChal).toOuterMeasure
        {b | ∃ cw ∈ reedSolomon α k, hammingDist (weights b ᵥ* M) cw ≤ e} ≤ ε_row) :
    ∀ M ∉ ligeroProximityLang m (reedSolomonGenerator α k) e, ∀ pref π,
      rsBatchDoomed m hk α q e weights M pref →
      (PMF.uniformOfFintype (LigeroIOPChal BatchChal d q)).toOuterMeasure
        {chal | ¬ rsBatchGoodStep m hk α q e weights M pref π chal} ≤
      max ε_row ((((2 ^ d - (e + 1) : ℕ) : ℝ≥0∞) / (2 ^ d : ℝ≥0∞)) ^ q) := by
  intro M hM pref π hd
  rcases pref with _ | ⟨⟨π₀, chal₀⟩, _ | ⟨e₁, rest⟩⟩
  · exact (rsBatchProximityIOP_round0_escape_le m hk α q e weights (hrow M hM) π).trans
      (le_max_left _ _)
  · exact (rsBatchProximityIOP_round1_escape_le m hk α q e weights π₀ chal₀ π hd).trans
      (le_max_right _ _)
  · have hemp : {chal : LigeroIOPChal BatchChal d q |
        ¬ rsBatchGoodStep m hk α q e weights M ((π₀, chal₀) :: e₁ :: rest) π chal} = ∅ := by
      ext chal
      simp [rsBatchGoodStep]
    simp only [hemp, MeasureTheory.measure_empty, zero_le]

/-- **Interactive IOP soundness of `rsBatchProximityIOP`** against any adaptive (possibly
randomized) cheating IOP prover `P` given row-batching escape bound `ε_row`. -/
theorem rsBatchProximityIOP_interactive_le {F BatchChal : Type}
    [Field F] [DecidableEq F] [Fintype BatchChal] [Nonempty BatchChal]
    (m : ℕ) {d k : ℕ} (hk : k ≤ 2 ^ d) (α : Fin (2 ^ d) → F) (q e : ℕ)
    (weights : BatchChal → (Fin m → F)) {ε_row : ℝ≥0∞}
    (hrow : ∀ M : Matrix (Fin m) (Fin (2 ^ d)) F,
      M ∉ ligeroProximityLang m (reedSolomonGenerator α k) e →
      (PMF.uniformOfFintype BatchChal).toOuterMeasure
        {b | ∃ cw ∈ reedSolomon α k, hammingDist (weights b ᵥ* M) cw ≤ e} ≤ ε_row)
    {M : Matrix (Fin m) (Fin (2 ^ d)) F}
    (hM : M ∉ ligeroProximityLang m (reedSolomonGenerator α k) e)
    (P : InteractiveIOPProver d F (LigeroIOPChal BatchChal d q)) :
    iopInteractiveGame (rsBatchProximityIOP m hk α q weights) M P true ≤
      ε_row + (((2 ^ d - (e + 1) : ℕ) : ℝ≥0∞) / (2 ^ d : ℝ≥0∞)) ^ q := by
  let ε_round : Fin 2 → ℝ≥0∞ :=
    ![ε_row, (((2 ^ d - (e + 1) : ℕ) : ℝ≥0∞) / (2 ^ d : ℝ≥0∞)) ^ q]
  refine (iopInteractiveGame_le_sum (rsBatchProximityIOP_rbrSound m hk α q e weights) ε_round
    (fun M' hM' j pref π hlen hd => ?_) hM P).trans_eq (Fin.sum_univ_two ε_round)
  fin_cases j
  · rcases pref with _ | ⟨_, _⟩
    · simpa only [Fin.zero_eta, ε_round, Matrix.cons_val_zero] using
        rsBatchProximityIOP_round0_escape_le m hk α q e weights (hrow M' hM') π
    · simp at hlen
  · rcases pref with _ | ⟨⟨π₀, chal₀⟩, _ | ⟨_, _⟩⟩
    · simp at hlen
    · simpa only [Fin.mk_one, ε_round, Matrix.cons_val_one, Matrix.cons_val_zero] using
        rsBatchProximityIOP_round1_escape_le m hk α q e weights π₀ chal₀ π hd
    · simp at hlen

/-- **General adaptive two-channel BCS random-oracle soundness bound for `rsBatchProximityIOP`**
given any row-batching escape bound `ε_row`. -/
theorem rsBatchProximityBCS_romSoundness_bound {F BatchChal : Type}
    [Field F] [DecidableEq F]
    [DecidableEq BatchChal] [Fintype BatchChal] [Nonempty BatchChal]
    (m : ℕ) {d k : ℕ} (hk : k ≤ 2 ^ d) (α : Fin (2 ^ d) → F) (q e : ℕ)
    (weights : BatchChal → (Fin m → F)) {ε_row : ℝ≥0∞}
    (hrow : ∀ M : Matrix (Fin m) (Fin (2 ^ d)) F,
      M ∉ ligeroProximityLang m (reedSolomonGenerator α k) e →
      (PMF.uniformOfFintype BatchChal).toOuterMeasure
        {b | ∃ cw ∈ reedSolomon α k, hammingDist (weights b ᵥ* M) cw ≤ e} ≤ ε_row)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : F) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (Matrix (Fin m) (Fin (2 ^ d)) F) (LigeroIOPChal BatchChal d q))
      (Matrix (Fin m) (Fin (2 ^ d)) F × BCSProof 2 F)}
    {t_MT t_FS q_V : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hV : ∀ M prf, (M, prf) ∈ P.support →
      IsCostBounded bcsMTCost
        (bcsVerifyROM (rsBatchProximityIOP m hk α q weights) encSym M prf) q_V) :
    bcsSoundnessGame (rsBatchProximityIOP m hk α q weights) encSym
        (ligeroProximityLang m (reedSolomonGenerator α k) e) P σ true ≤
      ((t_FS + 2 : ℕ) : ℝ≥0∞) *
          (max ε_row ((((2 ^ d - (e + 1) : ℕ) : ℝ≥0∞) / (2 ^ d : ℝ≥0∞)) ^ q) +
            ((t_FS + 2 : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / (Fintype.card BatchChal * (2 ^ d) ^ q : ℕ))) +
        ((t_MT + q_V : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + q_V) + 2 * (t_FS + 2) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  simpa only [card_ligeroIOPChal] using
    bcsROMSoundness_bound_of_prover_verifier
      (rsBatchProximityIOP_rbrSound m hk α q e weights)
      (rsBatchProximityIOP_escape_le m hk α q e weights hrow)
      hdec defaultSym σ hMT hFS hV

/-- **Two-channel BCS/ROM soundness of `rsAffineBatchProximityIOP` across the unique-decoding
radius** (`2 * e + k ≤ 2 ^ d`). -/
theorem rsAffineBatchProximityBCS_romSoundness_unique {F : Type}
    [Field F] [Fintype F] [DecidableEq F]
    (m : ℕ) {d k q e : ℕ} (hk : k ≤ 2 ^ d) {α : Fin (2 ^ d) → F}
    (hα : Function.Injective α) (hunique : 2 * e + k ≤ 2 ^ d)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : F) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (Matrix (Fin m) (Fin (2 ^ d)) F) (LigeroIOPChal (Fin m → F) d q))
      (Matrix (Fin m) (Fin (2 ^ d)) F × BCSProof 2 F)}
    {t_MT t_FS q_V : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hV : ∀ M prf, (M, prf) ∈ P.support →
      IsCostBounded bcsMTCost
        (bcsVerifyROM (rsAffineBatchProximityIOP m hk α q) encSym M prf) q_V) :
    bcsSoundnessGame (rsAffineBatchProximityIOP m hk α q) encSym
        (ligeroProximityLang m (reedSolomonGenerator α k) e) P σ true ≤
      ((t_FS + 2 : ℕ) : ℝ≥0∞) *
          (max ((2 ^ d : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
              ((((2 ^ d - (e + 1) : ℕ) : ℝ≥0∞) / (2 ^ d : ℝ≥0∞)) ^ q) +
            ((t_FS + 2 : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / (Fintype.card F ^ m * (2 ^ d) ^ q : ℕ))) +
        ((t_MT + q_V : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + q_V) + 2 * (t_FS + 2) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  have hbound := rsBatchProximityBCS_romSoundness_bound m hk α q e id
    (ε_row := (2 ^ d : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
    (fun M hM => by
      have hb := toOuterMeasure_sum_smul_reedSolomon_close_le hα
        (by simpa only [Fintype.card_fin] using hunique)
        (forall_lt_interleaved_reedSolomon_of_not_mem hM)
      simpa only [vecMul_eq_sum_smul_swap, id_eq, Fintype.card_fin, Nat.cast_pow,
        Nat.cast_ofNat] using hb)
    hdec defaultSym σ hMT hFS hV
  simpa only [Fintype.card_fun, Fintype.card_fin] using hbound

/-- **Two-channel BCS/ROM soundness of `rsAffineBatchProximityIOP` up to `1 - √ρ - η` (original
explicit-constant variant)** (`1 ≤ k ≤ 2 ^ d`, `m`-independent proximity escape error). -/
theorem rsAffineBatchProximityBCS_romSoundness_johnson_of_eta {F : Type}
    [Field F] [Fintype F] [DecidableEq F]
    (m : ℕ) {d k q e : ℕ} {η : ℝ} (hk_pos : 1 ≤ k) (hk : k ≤ 2 ^ d) {α : Fin (2 ^ d) → F}
    (hα : Function.Injective α) (hη : 0 < η)
    (he : (e : ℝ) / ((2 ^ d : ℕ) : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / ((2 ^ d : ℕ) : ℝ)) - η)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : F) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (Matrix (Fin m) (Fin (2 ^ d)) F) (LigeroIOPChal (Fin m → F) d q))
      (Matrix (Fin m) (Fin (2 ^ d)) F × BCSProof 2 F)}
    {t_MT t_FS q_V : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hV : ∀ M prf, (M, prf) ∈ P.support →
      IsCostBounded bcsMTCost
        (bcsVerifyROM (rsAffineBatchProximityIOP m hk α q) encSym M prf) q_V) :
    bcsSoundnessGame (rsAffineBatchProximityIOP m hk α q) encSym
        (ligeroProximityLang m (reedSolomonGenerator α k) e) P σ true ≤
      ((t_FS + 2 : ℕ) : ℝ≥0∞) *
          (max (ENNReal.ofReal
              (115200 * (((2 ^ d : ℕ) : ℝ) ^ 2) /
                (((k : ℝ) / ((2 ^ d : ℕ) : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ))))
              ((((2 ^ d - (e + 1) : ℕ) : ℝ≥0∞) / (2 ^ d : ℝ≥0∞)) ^ q) +
            ((t_FS + 2 : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / (Fintype.card F ^ m * (2 ^ d) ^ q : ℕ))) +
        ((t_MT + q_V : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + q_V) + 2 * (t_FS + 2) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  have hbound := rsBatchProximityBCS_romSoundness_bound m hk α q e id
    (fun M hM => by
      have hb := toOuterMeasure_sum_smul_reedSolomon_close_le_johnson_of_eta hα hk_pos
        (by simpa only [Fintype.card_fin] using hk) hη
        (by simpa only [Fintype.card_fin] using he)
        (forall_lt_interleaved_reedSolomon_of_not_mem hM)
      simpa only [vecMul_eq_sum_smul_swap, id_eq, Fintype.card_fin] using hb)
    hdec defaultSym σ hMT hFS hV
  simpa only [Fintype.card_fun, Fintype.card_fin] using hbound

/-- **Two-channel BCS/ROM soundness of single-scalar `rsCurveBatchProximityIOP` across the
unique-decoding radius** (`2 * e + k ≤ 2 ^ d`). -/
theorem rsCurveBatchProximityBCS_romSoundness_unique {F : Type}
    [Field F] [Fintype F] [DecidableEq F]
    (m : ℕ) {d k q e : ℕ} (hk : k ≤ 2 ^ d) {α : Fin (2 ^ d) → F}
    (hα : Function.Injective α) (hunique : 2 * e + k ≤ 2 ^ d)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : F) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (Matrix (Fin m) (Fin (2 ^ d)) F) (LigeroIOPChal F d q))
      (Matrix (Fin m) (Fin (2 ^ d)) F × BCSProof 2 F)}
    {t_MT t_FS q_V : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hV : ∀ M prf, (M, prf) ∈ P.support →
      IsCostBounded bcsMTCost
        (bcsVerifyROM (rsCurveBatchProximityIOP m hk α q) encSym M prf) q_V) :
    bcsSoundnessGame (rsCurveBatchProximityIOP m hk α q) encSym
        (ligeroProximityLang m (reedSolomonGenerator α k) e) P σ true ≤
      ((t_FS + 2 : ℕ) : ℝ≥0∞) *
          (max ((((m - 1) * 2 ^ d : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
              ((((2 ^ d - (e + 1) : ℕ) : ℝ≥0∞) / (2 ^ d : ℝ≥0∞)) ^ q) +
            ((t_FS + 2 : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / (Fintype.card F * (2 ^ d) ^ q : ℕ))) +
        ((t_MT + q_V : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + q_V) + 2 * (t_FS + 2) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  rsBatchProximityBCS_romSoundness_bound m hk α q e (ligeroPowWeights m)
    (fun M hM => by
      have hb := toOuterMeasure_sum_pow_smul_reedSolomon_close_le hα
        (by simpa only [Fintype.card_fin] using hunique)
        (forall_lt_interleaved_reedSolomon_of_not_mem hM)
      simpa only [vecMul_ligeroPowWeights_eq_sum_pow, Fintype.card_fin] using hb)
    hdec defaultSym σ hMT hFS hV

/-- **Two-channel BCS/ROM soundness of single-scalar `rsCurveBatchProximityIOP` up to `1 - √ρ - η`
(original explicit-constant variant)**. -/
theorem rsCurveBatchProximityBCS_romSoundness_johnson_of_eta {F : Type}
    [Field F] [Fintype F] [DecidableEq F]
    (m : ℕ) {d k q e : ℕ} {η : ℝ} (hk_pos : 1 ≤ k) (hk : k ≤ 2 ^ d) {α : Fin (2 ^ d) → F}
    (hα : Function.Injective α) (hη : 0 < η)
    (he : (e : ℝ) / ((2 ^ d : ℕ) : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / ((2 ^ d : ℕ) : ℝ)) - η)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : F) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (Matrix (Fin m) (Fin (2 ^ d)) F) (LigeroIOPChal F d q))
      (Matrix (Fin m) (Fin (2 ^ d)) F × BCSProof 2 F)}
    {t_MT t_FS q_V : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hV : ∀ M prf, (M, prf) ∈ P.support →
      IsCostBounded bcsMTCost
        (bcsVerifyROM (rsCurveBatchProximityIOP m hk α q) encSym M prf) q_V) :
    bcsSoundnessGame (rsCurveBatchProximityIOP m hk α q) encSym
        (ligeroProximityLang m (reedSolomonGenerator α k) e) P σ true ≤
      ((t_FS + 2 : ℕ) : ℝ≥0∞) *
          (max (ENNReal.ofReal
              (115200 * ((m - 1 : ℕ) : ℝ) * (((2 ^ d : ℕ) : ℝ) ^ 2) /
                (((k : ℝ) / ((2 ^ d : ℕ) : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ))))
              ((((2 ^ d - (e + 1) : ℕ) : ℝ≥0∞) / (2 ^ d : ℝ≥0∞)) ^ q) +
            ((t_FS + 2 : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / (Fintype.card F * (2 ^ d) ^ q : ℕ))) +
        ((t_MT + q_V : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + q_V) + 2 * (t_FS + 2) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  rsBatchProximityBCS_romSoundness_bound m hk α q e (ligeroPowWeights m)
    (fun M hM => by
      have hb := toOuterMeasure_sum_pow_smul_reedSolomon_close_le_johnson_of_eta hα hk_pos
        (by simpa only [Fintype.card_fin] using hk) hη
        (by simpa only [Fintype.card_fin] using he)
        (forall_lt_interleaved_reedSolomon_of_not_mem hM)
      simpa only [vecMul_ligeroPowWeights_eq_sum_pow, Fintype.card_fin] using hb)
    hdec defaultSym σ hMT hFS hV

end BatchProximityIOP

end Cslib.Crypto.Protocols
