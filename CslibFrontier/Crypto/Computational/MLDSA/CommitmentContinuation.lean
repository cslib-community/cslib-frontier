/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.PrivateMaskExpansion
public import CslibFrontier.Crypto.Computational.MLDSA.DigestSigningQueries
import all CslibFrontier.Crypto.Computational.MLDSA.DigestSigningQueries
import all CslibFrontier.Crypto.Computational.MLDSA.PrivateMaskExpansion
import all CslibFrontier.Crypto.Computational.MLDSA.PrivateMaskSeedGame
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204Signing
import all CslibFrontier.Crypto.Computational.MLDSA.SignedMatrix
import all CslibFrontier.Crypto.Computational.MLDSA.SigningROM
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumCommitmentRegister
import CslibFrontier.Computability.Circuit.Quantum.Oracle.QueryDisturbance
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Analysis.MeanInequalitiesPow
import all CslibFrontier.Crypto.Computational.MLDSA.SigningQueryComparison
import all CslibFrontier.Crypto.Computational.MLDSA.SigningHedges
import all CslibFrontier.Crypto.Computational.MLDSA.MaskSeedQuery
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning

/-!
# Changing one commitment digest during a quantum ML-DSA execution

Fix the current device, transcript and remaining private mask-expansion rows before drawing a
fresh mask. Change the digest of its rounded commitment in the shared SHAKE256 stream. A coherent
query contributes at most `4 * √δ` to the expected absolute change in fresh-digest forgery
probability, where `δ` is the largest atom of the rounded commitment for the fixed matrix.
A later signing request contributes `815 * δ`, and final verification contributes `2 * δ`.

The query estimate uses the quantum query disturbance argument of [BBBV1997]. The composition
with the adaptive controller and the capped signer and verifier of [NISTFIPS204], Algorithms 7
and 8 and Appendix C, is an original game comparison.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204
open Cslib.Probability Cslib.Quantum
open scoped ENNReal

private theorem query_change_event (H : Xofs) (s : Level) (A : PublicMatrix s)
    (m : BitString 512) (D) (a b : ℕ) (x : BitString (a + 2)) :
    (signingMaskLaw s.params (by cases s <;> decide)).toOuterMeasure
      {y | ∃ v, (H.withDigestRegister s
          (Function.update D (maskCommitmentAddress s A m y) v)).queryTable a b x ≠
        (H.withDigestRegister s D).queryTable a b x} ≤
      commitmentGuessProbability s.params (by cases s <;> decide) A := by
  classical
  let mask := signingMaskLaw s.params (by cases s <;> decide)
  have mass := maskCommitmentAddress_mass_le s A m (Xofs.digestLookup s x)
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply] at mass
  refine le_trans (mask.toOuterMeasure.mono ?_) mass
  rintro y ⟨v, hv⟩
  by_contra off
  apply hv
  have ne : Xofs.digestLookup s x ≠ maskCommitmentAddress s A m y := fun h => off h.symm
  rw [queryTable_register, queryTable_register]
  dsimp only
  rw [Function.update_of_ne ne]

/-- Mean squared change of the square root of an observable probability after one coherent
SHAKE query when a fresh ML-DSA mask selects the digest to change. The final measurement may
depend on the mask and the input device may carry an arbitrary entangled reference. -/
theorem Xofs.sq_sqrt_readout_after_maskCommitment_le
    (H : Xofs) (s : Level) (A : PublicMatrix s) (m : BitString 512) (D)
    (replacement : (Fin s.params.ℓ → Poly) → BitString (8 * digestBytes s))
    (a b w : ℕ) {κ σ α : Type} [Fintype κ] [DecidableEq κ] [Fintype α]
    (st : DeviceState (a + 2 + 8 * b + w) κ σ)
    (M : (Fin s.params.ℓ → Poly) → POVM α ((Fin (a + 2 + 8 * b + w) → Bool) × κ))
    (outcome : α) :
    let μ := signingMaskLaw s.params (by cases s <;> decide)
    let base := (H.withDigestRegister s D).queryTable a b
    let write y := (H.withDigestRegister s (Function.update D (maskCommitmentAddress s A m y)
      (replacement y))).queryTable a b
    let p y T := (M y).densityProb (st.instruction T .query).density outcome
    ∑ y, (μ y).toReal * (√(p y (write y)) - √(p y base)) ^ 2 ≤
      4 * (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal := by
  classical
  intro μ base write p
  apply (st.mean_sq_sqrt_query_readout_sub_le μ M outcome write base).trans
  apply mean_xorQueryDisturbance_le μ write base _ st.isDensityMatrix
  intro x
  have finite : commitmentGuessProbability s.params (by cases s <;> decide) A ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun _ => PMF.coe_le_one _ _)
  apply ENNReal.toReal_mono finite
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  apply le_trans (μ.toOuterMeasure.mono ?_) (query_change_event H s A m D a b x)
  exact fun y hy => ⟨replacement y, of_decide_eq_true hy⟩

namespace QuantumSigningForger

private abbrev prob (p : PMF Bool) := (p true).toReal

private theorem mean_abs_of_root {ι : Type} [Fintype ι] (μ : PMF ι) (p q : ι → PMF Bool)
    (B : ℝ) (hB : 0 ≤ B)
    (h : ∑ y, (μ y).toReal * (√(prob (p y)) - √(prob (q y))) ^ 2 ≤ B ^ 2) :
    ∑ y, (μ y).toReal * |prob (p y) - prob (q y)| ≤ 2 * B := by
  let root y := |√(prob (p y)) - √(prob (q y))|
  have avg := Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun y => (μ y).toReal) root
    (fun _ _ => ENNReal.toReal_nonneg) (PMF.sum_toReal μ) (fun _ _ => abs_nonneg _) 2
  have avg_le : ∑ y, (μ y).toReal * root y ≤ B := by
    apply le_of_abs_le
    rw [← Real.sqrt_sq_eq_abs]
    exact (Real.sqrt_le_sqrt (avg.trans (by simpa only [root, sq_abs] using h))).trans_eq
      (Real.sqrt_sq hB)
  have each (y) : |prob (p y) - prob (q y)| ≤ 2 * root y := by
    let u := √(prob (p y))
    let v := √(prob (q y))
    have hu : u ≤ 1 := (Real.sqrt_le_one).mpr (PMF.toReal_apply_le_one ..)
    have hv : v ≤ 1 := (Real.sqrt_le_one).mpr (PMF.toReal_apply_le_one ..)
    have eq : prob (p y) - prob (q y) = (u + v) * (u - v) := by
      nlinarith only [Real.sq_sqrt (show 0 ≤ prob (p y) from ENNReal.toReal_nonneg),
        Real.sq_sqrt (show 0 ≤ prob (q y) from ENNReal.toReal_nonneg)]
    rw [eq, abs_mul, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    exact mul_le_mul_of_nonneg_right (by linarith : u + v ≤ 2) (abs_nonneg _)
  calc
    _ ≤ ∑ y, (μ y).toReal * (2 * root y) :=
      Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (each y) ENNReal.toReal_nonneg
    _ = 2 * ∑ y, (μ y).toReal * root y := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => mul_left_comm ..
    _ ≤ _ := mul_le_mul_of_nonneg_left avg_le (by norm_num)

private theorem meanGap_of_agree {ι : Type} [Fintype ι] (μ : PMF ι) (p q : ι → PMF Bool)
    (bad : Set ι) (same : ∀ y, y ∉ bad → p y = q y) :
    PMF.meanAbsDiffAt μ true p q ≤ (μ.toOuterMeasure bad).toReal := by
  classical
  rw [PMF.toOuterMeasure_toReal_eq_sum_ite]
  refine Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  by_cases h : y ∈ bad
  · simp only [h, ↓reduceIte, abs_le]
    constructor <;> linarith [PMF.toReal_apply_le_one (p y) true,
      PMF.toReal_apply_le_one (q y) true,
      show 0 ≤ prob (p y) from ENNReal.toReal_nonneg,
      show 0 ≤ prob (q y) from ENNReal.toReal_nonneg]
  · simp [h, same y h]

private noncomputable abbrev stepState {C : QuantumSigningForger} (H : Xofs) (d : Device C) :=
  d.instruction (H.queryTable C.addressBits C.responseBytes) .query

private noncomputable abbrev observe {C : QuantumSigningForger} (M : Test C) (d : Device C) :=
  M.measureDensity d.density d.isDensityMatrix

private theorem scored_meanGap_le {C : QuantumSigningForger} {α V ι : Type} [Zero V] [Fintype ι]
    (μ : PMF ι) (base : Xofs) (write : ι → Xofs)
    (sign : V → SigningQuery → Option (List Byte))
    (sign' : ι → V → SigningQuery → Option (List Byte))
    (test : α → List Forgery → List V → Test C) (test' : ι → α → List Forgery → List V → Test C)
    {Q S T : ℝ} (nonQ : 0 ≤ Q) (nonS : 0 ≤ S)
    (coherent : ∀ (d : Device C) (M : ι → Test C),
      PMF.meanAbsDiffAt μ true (fun y => observe (M y) (stepState (write y) d))
        (fun y => observe (M y) (stepState base d)) ≤ Q)
    (signing : ∀ v q, (μ.toOuterMeasure {y | sign' y v q ≠ sign v q}).toReal ≤ S)
    (terminal : ∀ x log tape d, PMF.meanAbsDiffAt μ true (fun y => observe (test' y x log tape) d)
      (fun _ => observe (test x log tape) d) ≤ T)
    {prog : Program C α} {m n : ℕ}
    (cost : OracleComp.IsCostBounded (fun q => (isXofQuery q).toNat) prog m)
    (calls : OracleComp.IsCostBounded (fun q => (isSigningCall q).toNat) prog n)
    (d : Device C) (log : List Forgery) (tape : List V) :
    PMF.meanAbsDiffAt μ true (fun y => scored prog (write y) (sign' y) (test' y) d log tape)
      (fun _ => scored prog base sign test d log tape) ≤ m * Q + n * S + T := by
  classical
  induction cost generalizing n d log tape with
  | pure x m =>
    simpa only [scored, interp_norm, pmf_norm, observe] using
      (terminal x log tape d).trans (le_add_of_nonneg_left
        (add_nonneg (mul_nonneg (Nat.cast_nonneg m) nonQ) (mul_nonneg (Nat.cast_nonneg n) nonS)))
  | liftBind q k m _ ih =>
    obtain ⟨fits, cont⟩ := OracleComp.IsCostBounded.liftBind_iff.mp calls
    rcases q with coin | cmd | ask
    · simp only [scored_coin (C := C) (coin := coin) (k := k), isXofQuery,
        Bool.toNat_false, Nat.add_zero]
      apply PMF.meanAbsDiffAt_bind_le μ (ProbComp.unifOracle coin) true
      exact fun i => ih i (cont i) d log tape
    · cases cmd with
      | service op _ => exact op.elim
      | gate g =>
        let next := d.instruction (base.queryTable C.addressBits C.responseBytes) (.gate g)
        simpa only [scored_gate (C := C) (code := g) (k := k), next,
          DeviceState.instruction_apply, OracleGateCode.toPlacedGate?,
          isXofQuery, isSigningCall, Sum.elim_inr, Sum.elim_inl, Bool.toNat_false, Nat.sub_zero,
          Nat.add_zero] using ih [] (cont []) next log tape
      | measure wire =>
        obtain ⟨ν, next, hm⟩ := measure_map d wire
        simp only [scored_measure (C := C) (wire := wire) (k := k), hm, PMF.bind_map,
          Function.comp_def, isXofQuery,
          Bool.toNat_false, Nat.add_zero]
        apply PMF.meanAbsDiffAt_bind_le μ ν true
        exact fun b => ih [b] (cont [b]) (next b) log tape
      | query =>
        let tail y st := scored (k []) (write y) (sign' y) (test' y) st log tape
        have readout (y) := scored_readout (k []) (write y) (sign' y) (test' y) log tape
        choose M law using readout
        have one : PMF.meanAbsDiffAt μ true (fun y => tail y (stepState (write y) d))
            (fun y => tail y (stepState base d)) ≤ Q := by
          simpa only [tail, law, observe] using coherent d M
        have rest := ih [] (cont []) (stepState base d) log tape
        simp only [isSigningCall, Sum.elim_inr, Sum.elim_inl, Bool.toNat_false,
          Nat.sub_zero] at rest
        simp only [scored_query (C := C) (k := k), isXofQuery, Bool.toNat_true, Nat.cast_add_one]
        exact (PMF.meanAbsDiffAt_triangle μ true _ _ _).trans
          ((add_le_add one rest).trans_eq (by ring))
    · let sig := sign (tape.headD 0) ask
      let sig' y := sign' y (tape.headD 0) ask
      let tail y v := scored (k v) (write y) (sign' y) (test' y) d (ask.logReply v log) tape.tail
      have one : PMF.meanAbsDiffAt μ true (fun y => tail y (sig' y)) (fun y => tail y sig) ≤ S :=
        (meanGap_of_agree μ _ _ {y | sig' y ≠ sig} fun y h => by
          rw [show sig' y = sig from not_not.mp h]).trans (signing _ ask)
      have rest := ih sig (cont sig) d (ask.logReply sig log) tape.tail
      simp only [scored_sign (C := C) (ask := ask) (k := k), isXofQuery,
        Bool.toNat_false, Nat.add_zero]
      have len : n = n - 1 + 1 := by
        change 1 ≤ n at fits
        lia
      have eq : S + (m * Q + (n - 1 : ℕ) * S + T) = m * Q + n * S + T := by
        conv_rhs => rw [len, Nat.cast_add_one]
        ring
      exact (PMF.meanAbsDiffAt_triangle μ true _ _ _).trans ((add_le_add one rest).trans_eq eq)

private theorem prob_row_changes (H : Xofs) (s : Level) (A : PublicMatrix s) (m : BitString 512)
    (D) (key : List Byte) (q : SigningQuery) (row : ExpansionRow (maskPolyBytes s)) :
    let sign T := (H.withDigestRegister s T).signWithExpansionRow s key q row
    (signingMaskLaw s.params (by cases s <;> decide)).toOuterMeasure
      {y | ∃ v, sign (Function.update D (maskCommitmentAddress s A m y) v) ≠ sign D} ≤
      815 * commitmentGuessProbability s.params (by cases s <;> decide) A := by
  simpa only [Xofs.evalPure_signDigestQueriesWithMask, Xofs.signWithExpansionRow, Nat.cast_ofNat]
    using prob_response_changes s A m D _
      (H.signDigestQueriesWithMask_bounded s key q (fun _ _ => row) (maskFromRow s))

/-- Resume the fresh-digest forgery game with a retained device, the successful signing log,
and fixed remaining rows of Algorithm 34 bytes. Device queries, later signatures and final
verification all use the same raw XOF streams. -/
noncomputable def expansionContinuation (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (A : PublicMatrix s) (keys : KeyPair) (prog : Program C Forgery) (d : Device C)
    (log : List Forgery) (tape : List (FixedBytes 2 → FixedBytes (maskPolyBytes s))) : Game :=
  scored prog H (fun row q => H.signWithExpansionRow s keys.secretKey q row)
    (fun f history _ => POVM.const (SignedMatrixTrial.newDigestWin
      ⟨H, A, keys.publicKey, f, history⟩))
    d log tape

/-- For any remaining adaptive program, changing the digest at one fresh mask commitment changes
the probability of a verified fresh-digest strong forgery by at most the coherent-query, signing
and verification terms shown. The initial state and remaining tape are fixed before the mask
is drawn. The replacement digest can depend on the mask. -/
theorem mean_expansionContinuation_gap_le (C : QuantumSigningForger) (s : Level)
    (H : Xofs) (A : PublicMatrix s) (m : BitString 512) (D)
    (replacement : (Fin s.params.ℓ → Poly) → BitString (8 * digestBytes s))
    (keys : KeyPair) (prog : Program C Forgery) (d : Device C) (log : List Forgery)
    (tape : List (FixedBytes 2 → FixedBytes (maskPolyBytes s))) {qH qS : ℕ}
    (hash : OracleComp.IsCostBounded (fun q => (isXofQuery q).toNat) prog qH)
    (calls : OracleComp.IsCostBounded (fun q => (isSigningCall q).toNat) prog qS) :
    let μ := signingMaskLaw s.params (by cases s <;> decide)
    let δ := (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal
    let win T := Game.succProbability (C.expansionContinuation s (H.withDigestRegister s T)
      A keys prog d log tape)
    ∑ y, (μ y).toReal * |(win (Function.update D (maskCommitmentAddress s A m y)
        (replacement y)) : ℝ) -
      (win D : ℝ)| ≤ 4 * qH * √δ + (815 * qS + 2) * δ := by
  classical
  intro μ δ win
  let base := H.withDigestRegister s D
  let write y := H.withDigestRegister s (Function.update D (maskCommitmentAddress s A m y)
    (replacement y))
  have finite : commitmentGuessProbability s.params (by cases s <;> decide) A ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun _ => PMF.coe_le_one _ _)
  simp only [win, Game.coe_succProbability]
  change PMF.meanAbsDiffAt μ true _ _ ≤ _
  have bound := scored_meanGap_le (C := C) μ base write
    (fun row q => base.signWithExpansionRow s keys.secretKey q row)
    (fun y row q => (write y).signWithExpansionRow s keys.secretKey q row)
    (fun f history _ => POVM.const (SignedMatrixTrial.newDigestWin
      ⟨base, A, keys.publicKey, f, history⟩))
    (fun y f history _ => POVM.const (SignedMatrixTrial.newDigestWin
      ⟨write y, A, keys.publicKey, f, history⟩))
    (Q := 4 * √δ) (S := 815 * δ) (T := 2 * δ) (by positivity) (by positivity)
    (prog := prog) (m := qH) (n := qS) (d := d) (log := log) (tape := tape)
  apply le_trans (bound ?_ ?_ ?_ hash calls)
  · ring_nf
    rfl
  · intro dev M
    apply (mean_abs_of_root μ _ _ (2 * √δ) (by positivity) ?_).trans_eq
    · ring
    · have born (T : Xofs) (y) : prob (observe (M y) (stepState T dev)) =
          (M y).densityProb (stepState T dev).density true := by
        rw [prob, observe, POVM.measureDensity_apply, ENNReal.toReal_ofReal
          ((M y).densityProb_nonneg (stepState T dev).isDensityMatrix.posSemidef true)]
      simp only [born]
      rw [mul_pow, Real.sq_sqrt (show 0 ≤ δ from ENNReal.toReal_nonneg)]
      rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
      exact H.sq_sqrt_readout_after_maskCommitment_le s A m D replacement C.addressBits
        C.responseBytes C.workQubits dev M true
  · intro row q
    have h := prob_row_changes H s A m D keys.secretKey q row
    have le : μ.toOuterMeasure {y | (write y).signWithExpansionRow s keys.secretKey q row ≠
        base.signWithExpansionRow s keys.secretKey q row} ≤
        815 * commitmentGuessProbability s.params (by cases s <;> decide) A := by
      refine le_trans (μ.toOuterMeasure.mono ?_) h
      exact fun y hy => ⟨replacement y, hy⟩
    simpa only [δ, ENNReal.toReal_mul, ENNReal.toReal_ofNat] using
      ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) finite) le
  · intro f history rest dev
    let bad := {y | (write y).verify s keys.publicKey f.message f.context f.signature ≠
      base.verify s keys.publicKey f.message f.context f.signature}
    refine (meanGap_of_agree μ _ _ bad ?_).trans ?_
    · intro y off
      have eq : (write y).verify s keys.publicKey f.message f.context f.signature =
          base.verify s keys.publicKey f.message f.context f.signature := not_not.mp off
      simp only [observe, SignedMatrixTrial.newDigestWin, SignedMatrixTrial.wins, Xofs.winsForgery,
        SignedMatrixTrial.repeatsDigest, eq]
    · have h := H.prob_verify_changes_at_maskCommitment_le s A m D keys.publicKey f
      have le : μ.toOuterMeasure bad ≤
          2 * commitmentGuessProbability s.params (by cases s <;> decide) A := by
        refine le_trans (μ.toOuterMeasure.mono ?_) h
        exact fun y hy => ⟨replacement y, hy⟩
      simpa only [δ, ENNReal.toReal_mul, ENNReal.toReal_ofNat] using
        ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) finite) le

/-- Running the resumed comparison at the initial device with independent mask-expansion
rows gives the fresh-digest game in the original forgery bound, including failed key
generation or public-matrix expansion. -/
theorem freshExpansionGame_eq_expansionContinuation (C : QuantumSigningForger) (s : Level)
    (base : Xofs) (a b : ℕ) {n : ℕ} (hn : C.SigningCallsLe n) :
    C.freshExpansionGame s base a b = (do
      let H ← base.uniformPrefixes a b
      let seed ← PMF.uniformOfFintype (FixedBytes 32)
      let some keys := H.keyGen s seed | return false
      let some A := H.expandA s (keys.publicKey.take 32) | return false
      let rows ← PMF.uniformOfFintype (Fin n → FixedBytes 2 → FixedBytes (maskPolyBytes s))
      C.expansionContinuation s H A keys (C.program keys.publicKey) C.initialDevice []
        (List.ofFn rows)) := by
  simp only [freshExpansionGame, PMF.monad_bind_eq_bind]
  apply congrArg (PMF.bind (base.uniformPrefixes a b) ·)
  funext H
  apply congrArg (PMF.bind (PMF.uniformOfFintype (FixedBytes 32)) ·)
  funext seed
  simp only [scoreTranscript, withTrialSetup]
  cases key : H.keyGen s seed with
  | none => rfl
  | some keys =>
    dsimp only
    cases mat : H.expandA s (keys.publicKey.take 32) with
    | none => rfl
    | some A =>
      dsimp only
      rw [freshExpansionTranscript, ← C.uniform_signingTapeTranscript _ _ _ hn, PMF.map_bind]
      apply congrArg (PMF.bind _ ·)
      funext rows
      simp only [expansionContinuation, scored, signingTapeTranscript, POVM.measureDensity_const,
        PMF.map_comp, Function.comp_def]
      rfl

end QuantumSigningForger
end Cslib.Crypto.MLDSA.FIPS204
