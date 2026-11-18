/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.MeasuredPrefix
public import CslibFrontier.Crypto.Computational.MLDSA.FIPS204Signing
public import CslibFrontier.Crypto.Computational.MLDSA.SplitMatrix
import CslibFrontier.Probability.PMF.Expect

/-!
# Refreshing a signing digest after adaptive quantum and signing queries

The prefix can measure the adversary's state, answer measured signing calls and resume
coherent XOR queries on the same digest table. Capped signing uses Algorithm 7's actual
ExpandMask loop. Its internal commitment queries count even when they precede a rejection.

At the distinguished attempt an independent uniform signing mask is drawn after the
representative has been chosen. The retained mask and digest go through SampleInBall, the
response and hint checks, and signature encoding. Refreshing the digest for the attempt
and all subsequent operations costs the prefix's query disturbance times the FIPS
commitment entropy factor. For an erased rejected write, a second bound counts future
signer queries and the following measured quantum interaction without revealing the rejected mask.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Quantum Finset
open scoped BigOperators ENNReal

variable (s : Level) (extra : Finset (List Bool))

/-- Capped FIPS signatures have exactly this finite outward register, including the error. -/
abbrev SigningReply := Option (FixedBytes (signatureBytes s))

private def recordReply (out : Option (List Byte)) : SigningReply s :=
  out.map fun sig i => sig.getD i.val 0

private theorem recordReply_some {sig : List Byte} (h : sig.length = signatureBytes s) :
    (recordReply s (some sig)).map FixedBytes.toList = some sig := by
  simp only [recordReply, Option.map_some, Option.some.injEq]
  obtain ⟨v, rfl⟩ := FixedBytes.exists_toList h
  congr 1
  funext i
  exact FixedBytes.getD_toList v i 0

/-- The deterministic commitment table obtained by putting the literal SHAKE256 bits at
every raw address of the quantum register. -/
def shakeDigestTable (i : commitmentAddresses s extra) : DigestRegister s :=
  BitString.ofList _ (Keccak.bytesToBitsLE
    (Keccak.bitSponge Keccak.shake256Layout [true, true, true, true] i.val (digestBytes s)))

private theorem read_shake (m : BitString 512) (w : Fin s.params.k → Poly) :
    registerBytes s (shakeDigestTable s extra (commitmentAddress s extra m w)) =
      commitmentDigest s (highBitsVec s.params w) (List.ofFn m) := by
  unfold shakeDigestTable
  rw [registerBytes_ofList _ _ (Keccak.length_bitSponge ..), val_commitmentAddress]
  rfl

/-- A signing request by context and original message, with explicit hedging coins. The
returned register contains every signature byte. The commitment oracle is shared with the
coherent register. All other FIPS SHAKE calls in this service use their literal implementation. -/
def signingRequestQueries (key : List Byte) (q : SigningQuery) (rnd : FixedBytes 32) :
    OracleComp (fun _ : commitmentAddresses s extra => DigestRegister s) (SigningReply s) :=
  if q.context.length ≤ 255 then
    match decodePrivate s key with
    | none => pure none
    | some sk =>
      match expandA s sk.rho with
      | none => pure none
      | some A =>
        let μ := representativeFromTr sk.tr (formatMessage q.message q.context)
        let seed := Keccak.bitSponge Keccak.shake256Layout [true, true, true, true]
          (Keccak.bytesToBitsLE (sk.key ++ rnd.toList) ++ μ) 64
        signingQueries s sk A seed (commitmentAddress s extra (BitString.ofList 512 μ))
          (registerBytes s) (recordReply s) 814 0
  else pure none

private theorem request_bounded (key : List Byte) (q : SigningQuery) (rnd : FixedBytes 32) :
    (signingRequestQueries s extra key q rnd).IsQueryBounded 814 := by
  unfold signingRequestQueries
  split <;> first | exact .pure _ _ | split
  all_goals first | exact .pure _ _ | split
  all_goals first | exact .pure _ _ | apply signingQueries_bounded

private theorem eval_loop (sk : PrivateKey s) (A : PublicMatrix s) (m : BitString 512)
    (seed : List Byte) (fuel κ : ℕ) :
    (OracleComp.evalPure (shakeDigestTable s extra)
      (signingQueries s sk A seed (commitmentAddress s extra m) (registerBytes s)
        (recordReply s) fuel κ)).map FixedBytes.toList =
      OracleComp.evalPure (fun w => commitmentDigest s (highBitsVec s.params w) (List.ofFn m))
        (signingQueries s sk A seed id id id fuel κ) := by
  induction fuel generalizing κ with
  | zero => rfl
  | succ n ih =>
    simp only [signingQueries, OracleComp.evalPure_bind, OracleComp.evalPure_query,
      id_eq, read_shake]
    split
    · rfl
    · rename_i sig he
      exact recordReply_some s (length_finishSigningAttempt (length_commitmentDigest ..) he)
    · apply ih

/-- At literal SHAKE every adaptive measured signing call returns exactly the external FIPS
signer's bytes or its error, including invalid contexts, secret keys and XOF exhaustion. -/
theorem evalPure_signingRequestQueries (key : List Byte) (q : SigningQuery) (rnd : FixedBytes 32) :
    (OracleComp.evalPure (shakeDigestTable s extra) (signingRequestQueries s extra key q rnd)).map
      FixedBytes.toList = sign s key q.message q.context rnd := by
  unfold signingRequestQueries sign
  by_cases hc : q.context.length ≤ 255
  · simp only [hc, ↓reduceIte, guard, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      signInternal]
    cases hs : decodePrivate s key with
    | none => rfl
    | some sk =>
      simp only [Option.bind_some]
      cases ha : expandA s sk.rho with
      | none => rfl
      | some A =>
        let μ := representativeFromTr sk.tr (formatMessage q.message q.context)
        let seed := Keccak.bitSponge Keccak.shake256Layout [true, true, true, true]
          (Keccak.bytesToBitsLE (sk.key ++ rnd.toList) ++ μ) 64
        simpa only [μ, seed, Option.bind_some, ha,
          BitString.ofFn_ofList (length_representativeFromTr ..)]
          using eval_loop s extra sk A (BitString.ofList 512 μ) seed 814 0
  · simp [hc, guard]

/-- A retained-state interaction with a finite classical outward history and a coherent FIPS
digest register over raw bit-string inputs. -/
abbrev SigningInteraction (W B : Type) [Fintype W] [Fintype B] :=
  MeasuredPrefix (commitmentAddresses s extra) (DigestRegister s) (DigestRegister s) W B

/-- Append the actual external signing service to an interaction. Each message and context
can depend on all previous measurements and complete signing replies. The explicit hedging
tape may be fixed first and averaged independently. -/
noncomputable def measuredSigningCall {B W : Type} [Fintype B] [Fintype W]
    (p : SigningInteraction s extra W B) (key : List Byte)
    (request : B → SigningQuery) (rnd : B → FixedBytes 32) :
    SigningInteraction s extra W (B × SigningReply s) :=
  p.service (fun b => signingRequestQueries s extra key (request b) (rnd b)) 814
    (fun b => request_bounded s extra key (request b) (rnd b))

/-- Finishing the request after the distinguished attempt. A rejected mask resumes the
bounded ExpandMask loop on the selected oracle. Failure aborts and acceptance returns bytes. -/
private def finishRequest (sk : PrivateKey s) (A : PublicMatrix s) (m : BitString 512)
    (seed : List Byte) (fuel κ : ℕ) (result : Option (Option (List Byte))) :
    OracleComp (fun _ : commitmentAddresses s extra => DigestRegister s) (SigningReply s) :=
  match result with
  | none => pure none
  | some (some sig) => pure (recordReply s (some sig))
  | some none => signingQueries s sk A seed (commitmentAddress s extra m)
      (registerBytes s) (recordReply s) fuel κ

/-- The three commitment-table treatments for the distinguished trial. -/
inductive TrialRefresh where
  /-- Read the ambient table. -/
  | ambient
  /-- Overwrite this entry and keep it on every outcome. -/
  | persistent
  /-- Overwrite, and restore the previous entry if the mask is rejected and the signer retries. -/
  | eraseRejected
  deriving DecidableEq

/-- Final decision after a measured interaction, one distinguished fresh-mask trial,
the remaining capped signing trials and an adaptive measured continuation. Only the complete
signing reply is passed to the adversary. The digest table persists across all these stages. -/
noncomputable def signingAttemptRefreshProbability {B W O : Type} [Fintype B] [Fintype W]
    [Fintype O] (refresh : TrialRefresh) (A : PublicMatrix s) (sk : PrivateKey s)
    (p : SigningInteraction s extra W B)
    (ψ : ValueState (commitmentAddresses s extra) (DigestRegister s) W)
    (msg : B → BitString 512) (seed : B → List Byte) (fuel nonce : ℕ)
    (next : B → SigningReply s → SigningInteraction s extra W O)
    (accept : B → SigningReply s →
      Finset (O × (commitmentAddresses s extra × DigestRegister s × W))) : ℝ :=
  𝔼 hv : (commitmentAddresses s extra → DigestRegister s) × DigestRegister s,
    ∑ b, ∑ y, (signingMaskLaw s.params (by cases s <;> decide) y).toReal *
      let w := moduleSISMap A y
      let i := commitmentAddress s extra (msg b) w
      let H := if refresh = .ambient then hv.1 else Function.update hv.1 i hv.2
      let result := finishSigningAttempt s sk y w (registerBytes s (H i))
      let resume := if refresh = .eraseRejected ∧ result = some none then hv.1 else H
      MeasuredPrefix.serviceAcceptance addStep
        (finishRequest s extra sk A (msg b) (seed b) fuel nonce result) (next b) (accept b)
        resume (p.state addStep ψ hv.1 b)

private theorem abs_signingAttemptRefreshProbability_sub_le {B W O : Type} [Fintype B] [Fintype W]
    [Fintype O] (A : PublicMatrix s) (sk : PrivateKey s) (p ψ msg seed fuel nonce next accept)
    (hψ : ‖ψ‖ = 1) :
    |signingAttemptRefreshProbability s extra (B := B) (W := W) (O := O) .persistent A sk p ψ msg
      seed fuel nonce next accept -
      signingAttemptRefreshProbability s extra .ambient A sk p ψ msg seed fuel nonce next accept| ≤
      p.updateCost * Real.sqrt
        (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal := by
  classical
  let addr (b : B) (y : Fin s.params.ℓ → Poly) :=
    commitmentAddress s extra (msg b) (moduleSISMap A y)
  let reply (H : commitmentAddresses s extra → DigestRegister s) (b : B) (y : Fin s.params.ℓ → Poly)
      := OracleComp.evalPure H (finishRequest s extra sk A (msg b) (seed b) fuel nonce
        (finishSigningAttempt s sk y (moduleSISMap A y) (registerBytes s (H (addr b y)))))
  let mass := commitmentGuessProbability s.params (by cases s <;> decide) A
  have finite : mass ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun _ => PMF.coe_le_one _ _)
  have norm (H) : ∑ b, ‖p.state addStep ψ H b‖ ^ 2 = 1 := by rw [p.sum_sq_state, hψ, one_pow]
  simpa only [signingAttemptRefreshProbability, reduceCtorEq, false_and, ↓reduceIte, true_and,
    MeasuredPrefix.serviceAcceptance, addr, reply, mass, ENNReal.toReal] using
    abs_branch_refresh_le (p.state addStep ψ) norm p.updateCost_nonneg
    (p.sum_sq_state_update_sub_le addStep ψ hψ)
    (fun _ => signingMaskLaw s.params (by cases s <;> decide)) addr (δ := mass.toNNReal)
    (fun b i => ENNReal.toReal_mono finite (signingAddressLaw_le s extra A (msg b) i))
    (fun H b y => (next b (reply H b y)).outcomeIsometry addStep H)
    (fun H b y => accept b (reply H b y))

private theorem abs_eraseRejected_sub_persistent {B W O : Type} [Fintype B] [Fintype W]
    [Fintype O] (A : PublicMatrix s) (sk : PrivateKey s) (p ψ msg seed fuel nonce next accept)
    {F : ℝ} (hψ : ‖ψ‖ = 1) (future : ∀ b r, (next b r).updateCost ≤ F) :
    |signingAttemptRefreshProbability s extra (B := B) (W := W) (O := O) .eraseRejected A sk p
        ψ msg seed fuel nonce next accept -
      signingAttemptRefreshProbability s extra .persistent A sk p ψ msg seed fuel nonce
        next accept| ≤
      Real.sqrt (fuel + F ^ 2) * Real.sqrt
        (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal := by
  classical
  let mask := signingMaskLaw s.params (by cases s <;> decide)
  let addr (b : B) (y : Fin s.params.ℓ → Poly) :=
    commitmentAddress s extra (msg b) (moduleSISMap A y)
  let mass := (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal
  let C := Real.sqrt (fuel + F ^ 2) * Real.sqrt mass
  have finite : commitmentGuessProbability s.params (by cases s <;> decide) A ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun _ => PMF.coe_le_one _ _)
  unfold signingAttemptRefreshProbability
  rw [← expect_sub_distrib]
  refine (abs_expect_le _ _).trans (expect_le univ_nonempty fun hv _ => ?_)
  obtain ⟨H, v⟩ := hv
  let G (i : commitmentAddresses s extra) := Function.update H i v
  let u (b : B) := p.state addStep ψ H b
  simp only [reduceCtorEq, false_and, true_and, ↓reduceIte, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ b, ‖u b‖ ^ 2 * C := by
      refine sum_le_sum fun b _ => ?_
      let run := finishRequest s extra sk A (msg b) (seed b) fuel nonce (some none)
      let score (result : Option (Option (List Byte))) (T : commitmentAddresses s extra →
          DigestRegister s) := MeasuredPrefix.serviceAcceptance addStep
        (finishRequest s extra sk A (msg b) (seed b) fuel nonce result) (next b) (accept b) T (u b)
      let result (y : Fin s.params.ℓ → Poly) := finishSigningAttempt s sk y (moduleSISMap A y)
        (registerBytes s ((G (addr b y)) (addr b y)))
      have row (y : Fin s.params.ℓ → Poly) :
          |(mask y).toReal * score (result y) (if result y = some none then H else G (addr b y)) -
            (mask y).toReal * score (result y) (G (addr b y))| ≤
            (mask y).toReal * |score (some none) (G (addr b y)) - score (some none) H| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        by_cases he : result y = some none
        · rw [ite_eq_left he, he, abs_sub_comm]
        · simp [he]
      refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun y _ => row y).trans ?_)
      rw [← Probability.PMF.sum_map_mul mask (addr b)
        (fun i => |score (some none) (G i) - score (some none) H|)]
      have h := MeasuredPrefix.mean_abs_serviceAcceptance_update_sub_le addStep run
        (next b) (accept b) H v (u b) (K := fuel) (signingQueries_bounded ..) (mask.map (addr b))
        (δ := mass) (fun i => ENNReal.toReal_mono finite (signingAddressLaw_le s extra A (msg b) i))
      refine h.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
      rw [Real.sqrt_mul ENNReal.toReal_nonneg, mul_comm]
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (add_le_add le_rfl
        (pow_le_pow_left₀ (next b _).updateCost_nonneg (future b _) 2))) (Real.sqrt_nonneg _)
    _ = _ := by
      have total : ∑ b, ‖u b‖ ^ 2 = 1 := by simpa [u, hψ] using p.sum_sq_state addStep ψ H
      rw [← sum_mul, total, one_mul]

/-- Compare an honest read with a fresh digest that persists only on a terminal trial.
On mask rejection the digest is restored before the signer retries. Earlier measured signing
calls, coherent reads, the remaining retries and the actual adaptive continuation all contribute
to the bound. The coefficient matrix is uniformly sampled at the designated FIPS level. -/
theorem abs_mean_signingAttemptRefreshProbability_sub_le {B W O : Type} [Fintype B] [Fintype W]
    [Fintype O] (sk : PublicMatrix s → PrivateKey s)
    (p : PublicMatrix s → SigningInteraction s extra W B)
    (ψ : PublicMatrix s → ValueState (commitmentAddresses s extra) (DigestRegister s) W)
    (msg : PublicMatrix s → B → BitString 512) (seed : PublicMatrix s → B → List Byte)
    (fuel nonce : ℕ) (next : PublicMatrix s → B → SigningReply s → SigningInteraction s extra W O)
    (accept : PublicMatrix s → B → SigningReply s →
      Finset (O × (commitmentAddresses s extra × DigestRegister s × W))) {C F : ℝ}
    (hψ : ∀ A, ‖ψ A‖ = 1) (budget : ∀ A, (p A).updateCost ≤ C)
    (future : ∀ A b r, (next A b r).updateCost ≤ F) :
    |(𝔼 A, signingAttemptRefreshProbability s extra .eraseRejected A (sk A) (p A) (ψ A) (msg A)
      (seed A) fuel nonce (next A) (accept A)) -
      (𝔼 A, signingAttemptRefreshProbability s extra .ambient A (sk A) (p A) (ψ A) (msg A)
        (seed A) fuel nonce (next A) (accept A))| ≤
      (C + Real.sqrt (fuel + F ^ 2)) * ((11 / 10) / Real.sqrt (2 ^ s.commitmentBoxBits)) := by
  let L := C + Real.sqrt (fuel + F ^ 2)
  have hL : 0 ≤ L := add_nonneg ((p 0).updateCost_nonneg.trans (budget 0)) (Real.sqrt_nonneg _)
  rw [← expect_sub_distrib]
  refine (abs_expect_le _ _).trans ((expect_le_expect (g := fun A =>
    L * (Real.sqrt (commitmentKernelSize s A) / Real.sqrt (2 ^ s.commitmentBoxBits)))
    fun A _ => ?_).trans ?_)
  · have erase := abs_eraseRejected_sub_persistent s extra A (sk A) (p A) (ψ A) (msg A) (seed A)
      fuel nonce (next A) (accept A) (hψ A) (future A)
    have persist := abs_signingAttemptRefreshProbability_sub_le s extra A (sk A) (p A) (ψ A)
      (msg A) (seed A) fuel nonce (next A) (accept A) (hψ A)
    refine (abs_sub_le _ _ _).trans ((add_le_add erase persist).trans ?_)
    rw [← add_mul]
    apply mul_le_mul (by dsimp [L]; linarith [budget A]) _ (Real.sqrt_nonneg _) hL
    rw [← Real.sqrt_div (Nat.cast_nonneg _)]
    exact Real.sqrt_le_sqrt (commitmentGuessProbability_le_kernel_div_pow s A)
  · rw [← mul_expect]
    apply mul_le_mul_of_nonneg_left _ hL
    simp_rw [div_eq_mul_inv]
    rw [← expect_mul]
    gcongr
    exact (mean_sqrt_commitmentKernelSize_lt s).le

end Cslib.Crypto.MLDSA.FIPS204
