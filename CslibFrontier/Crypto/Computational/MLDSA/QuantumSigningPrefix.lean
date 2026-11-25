/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.MeasuredPrefix
public import CslibFrontier.Crypto.Computational.MLDSA.FIPS204Signing
public import CslibFrontier.Crypto.Computational.MLDSA.QuantumCommitment
import CslibFrontier.Probability.PMF.Expect

/-!
# Refreshing a signing digest after adaptive quantum and signing queries

The prefix can measure the adversary's state, answer measured signing calls and resume
coherent XOR queries on the same digest table. Capped signing uses Algorithm 7's actual
ExpandMask loop. All SHAKE256 roles read the same prefix-consistent XOF, including calls
to expand masks and challenges that are eventually rejected.

At the distinguished attempt an independent uniform signing mask is drawn after the
representative has been chosen. The retained mask and digest go through SampleInBall, the
response and hint checks, and signature encoding. Refreshing the digest for the attempt
and all subsequent operations costs the prefix's query disturbance times the FIPS
commitment entropy factor. For an erased rejected write, a second bound counts future
signer queries and the following measured quantum interaction without revealing the rejected mask.
The numerical estimate averages over a uniform coefficient matrix and a fresh independent mask
at the distinguished trial. The joint seeded key and ExpandMask law and the full reduction are
tracked in [#4987](https://github.com/cslib-community/cslib-frontier/issues/4987) and
[#5683](https://github.com/cslib-community/cslib-frontier/issues/5683).

The single-trial bound is an original finite-query estimate. Rejected-transcript oracle entries
are central to the CMA-to-NMA arguments of [BarbosaEtAl2023] and [FallahpourFehrHuang2025].
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
  simp [FixedBytes.toList]

/-- Install one digest-sized prefix per raw input in the finite quantum register. Bytes
after the installed prefix, raw inputs outside the register and the SHAKE128 component come
from the supplied XOFs. Requests from different protocol roles share the installed prefix. -/
@[expose] noncomputable def sharedXofs (base : Xofs)
    (table : commitmentAddresses s extra → DigestRegister s) : Xofs :=
  { base with h256 := base.h256.withPrefixes fun x =>
      if h : x ∈ commitmentAddresses s extra then some (registerBytes s (table ⟨x, h⟩)) else none }

/-- The literal digest register values of any chosen SHAKE256 stream. -/
def Xofs.digestTable (base : Xofs) (i : commitmentAddresses s extra) : DigestRegister s :=
  BitString.ofList _ (Keccak.bytesToBitsLE (base.h256.read i.val (digestBytes s)))

/-- Filling the finite register from the underlying stream preserves the entire pair of
XOFs at every raw input and requested length, including at literal FIPS SHAKE. -/
theorem sharedXofs_digestTable (base : Xofs) :
    sharedXofs s extra base (base.digestTable s extra) = base := by
  refine Xofs.ext rfl (ExtendableOutput.ext (funext fun x => funext fun n => ?_))
  unfold sharedXofs ExtendableOutput.withPrefixes
  by_cases h : x ∈ commitmentAddresses s extra
  · simp only [h, ↓reduceDIte, Xofs.digestTable,
      registerBytes_ofList _ _ (base.h256.length_read ..)]
    exact base.h256.readWithPrefix_self x n _
  · simp [h]

/-- At the actual commitment input every use of SHAKE256 reads precisely the digest
in the coherent register, even when another protocol role has used that raw input. -/
theorem commitmentDigest_sharedXofs (base : Xofs)
    (T : commitmentAddresses s extra → DigestRegister s) (m : BitString 512)
    (w : Fin s.params.k → Poly) :
    (sharedXofs s extra base T).commitmentDigest s (highBitsVec s.params w) (List.ofFn m) =
      registerBytes s (T (commitmentAddress s extra m w)) := by
  unfold Xofs.commitmentDigest
  rw [← val_commitmentAddress s extra m w]
  simp [sharedXofs, ExtendableOutput.withPrefixes, ExtendableOutput.readWithPrefix,
    (commitmentAddress s extra m w).property, List.take_of_length_le, base.h256.length_read]

/-- Serve a raw SHAKE256 read by consulting the coherent table once for its stored digest
prefix and using the fixed underlying XOF bytes for the rest. -/
noncomputable def read256 (base : Xofs) (q : ExtendableOutput.Request) :
    OracleComp (fun _ : commitmentAddresses s extra => DigestRegister s) (List Byte) :=
  if h : q.input ∈ commitmentAddresses s extra then do
    let d ← OracleComp.query ⟨q.input, h⟩
    return base.h256.readWithPrefix q.input q.count (registerBytes s d)
  else pure (base.h256.read q.input q.count)

/-- A raw SHAKE256 read needs at most one query to the shared digest-prefix register. -/
theorem bounded_read256 (base : Xofs) (q : ExtendableOutput.Request) :
    (read256 s extra base q).IsQueryBounded 1 := by
  unfold read256
  split
  · exact .liftBind _ _ 0 fun _ => .pure _ _
  · exact .pure _ _

/-- Interpreting any adaptive raw SHAKE256 program using the finite table agrees with
evaluating that program against the resulting shared, prefix-consistent XOF. -/
theorem eval_shared_reads (base : Xofs) (T : commitmentAddresses s extra → DigestRegister s)
    {R : Type} (run : ExtendableOutput.Reads R) :
    OracleComp.evalPure T (OracleComp.interpret (read256 s extra base) run) =
      OracleComp.evalPure (ExtendableOutput.Request.answer (sharedXofs s extra base T).h256)
        run := by
  induction run using OracleComp.induction with
  | pure r => rfl
  | query_bind q cont ih =>
    simp only [PFunctor.FreeM.bind_eq_bind, OracleComp.interpret_bind, OracleComp.interpret_query,
      OracleComp.evalPure_bind, OracleComp.evalPure_query, ih]
    congr 1
    unfold read256 sharedXofs ExtendableOutput.Request.answer ExtendableOutput.withPrefixes
    by_cases h : q.input ∈ commitmentAddresses s extra <;> simp [h]

/-- A signing request on the same raw SHAKE256 table as coherent queries. The finite reply
register carries the entire encoded signature or the FIPS error. -/
noncomputable def signingRequestQueries (base : Xofs) (key : List Byte) (q : SigningQuery)
    (rnd : FixedBytes 32) :
    OracleComp (fun _ : commitmentAddresses s extra => DigestRegister s) (SigningReply s) :=
  if q.context.length ≤ 255 then OracleComp.interpret (read256 s extra base)
    (base.signInternalReads s key (formatMessage q.message q.context) rnd (recordReply s))
  else pure none

private theorem request_bounded (base : Xofs) (key : List Byte) (q : SigningQuery)
    (rnd : FixedBytes 32) :
    (signingRequestQueries s extra base key q rnd).IsQueryBounded ((s.params.ℓ + 2) * 814 + 2) := by
  unfold signingRequestQueries
  split
  · exact (base.signInternalReads_bounded ..).interpret (bounded_read256 s extra base)
  · exact .pure _ _

/-- At every table, the measured request returns exactly Algorithm 2's bytes under the shared
pair of XOFs, including malformed inputs, XOF exhaustion and exhausting the retry cap. -/
theorem evalPure_signingRequestQueries (base : Xofs)
    (T : commitmentAddresses s extra → DigestRegister s) (key : List Byte) (q : SigningQuery)
    (rnd : FixedBytes 32) :
    (OracleComp.evalPure T (signingRequestQueries s extra base key q rnd)).map FixedBytes.toList =
      (sharedXofs s extra base T).sign s key q.message q.context rnd := by
  let H := sharedXofs s extra base T
  by_cases hc : q.context.length ≤ 255
  · simp only [signingRequestQueries, hc, ↓reduceIte, eval_shared_reads, Xofs.sign,
      guard, Option.pure_def, Option.bind_eq_bind, Option.bind_some]
    rw [base.evalPure_signInternalReads_of_h128 H rfl]
    cases hs : H.signInternal s key (formatMessage q.message q.context) rnd with
    | none => rfl
    | some sig => exact recordReply_some s (H.length_signInternal hs)
  · simp [signingRequestQueries, Xofs.sign, hc, guard]

/-- A retained-state interaction with a finite classical outward history and a coherent FIPS
digest register over raw bit-string inputs. -/
abbrev SigningInteraction (W B : Type) [Fintype W] [Fintype B] :=
  MeasuredPrefix (commitmentAddresses s extra) (DigestRegister s) (DigestRegister s) W B

/-- Append the actual external signing service to an interaction. Each message and context
can depend on all previous measurements and complete signing replies. The explicit hedging
tape may be fixed first and averaged independently. -/
noncomputable def measuredSigningCall {B W : Type} [Fintype B] [Fintype W]
    (p : SigningInteraction s extra W B) (base : Xofs) (key : B → List Byte)
    (request : B → SigningQuery) (rnd : B → FixedBytes 32) :
    SigningInteraction s extra W (B × SigningReply s) :=
  p.service (fun b => signingRequestQueries s extra base (key b) (request b) (rnd b))
    ((s.params.ℓ + 2) * 814 + 2) (fun b => request_bounded s extra base (key b) (request b) (rnd b))

/-- The measured call charges the two initial SHAKE256 reads and at most ℓ + 2 per trial. -/
@[simp] theorem updateCost_measuredSigningCall {B W : Type} [Fintype B] [Fintype W]
    (p : SigningInteraction s extra W B) (base : Xofs) (key : B → List Byte)
    (request : B → SigningQuery) (rnd : B → FixedBytes 32) :
    (measuredSigningCall s extra p base key request rnd).updateCost =
      p.updateCost + Real.sqrt (2 * (((s.params.ℓ + 2) * 814 + 2 : ℕ) : ℝ)) := by
  simp only [measuredSigningCall, MeasuredPrefix.updateCost]

/-- Finishing the request after the distinguished attempt. A rejected mask resumes the
bounded ExpandMask loop on the selected oracle. Failure aborts and acceptance returns bytes. -/
private noncomputable def finishRequest (base : Xofs) (sk : PrivateKey s) (A : PublicMatrix s)
    (m : BitString 512) (seed : List Byte) (fuel κ : ℕ) (result : Option (Option (List Byte))) :
    OracleComp (fun _ : commitmentAddresses s extra => DigestRegister s) (SigningReply s) :=
  match result with
  | none => pure none
  | some (some sig) => pure (recordReply s (some sig))
  | some none => OracleComp.interpret (read256 s extra base)
      (signingQueries s sk A (List.ofFn m) seed (recordReply s) fuel κ)

private theorem retry_bounded (base : Xofs) (sk : PrivateKey s) (A : PublicMatrix s)
    (m : BitString 512) (seed : List Byte) (fuel κ : ℕ) :
    (finishRequest s extra base sk A m seed fuel κ (some none)).IsQueryBounded
      ((s.params.ℓ + 2) * fuel) :=
  (signingQueries_bounded ..).interpret (bounded_read256 s extra base)

private noncomputable def trialResult (base : Xofs) (sk : PrivateKey s) (A : PublicMatrix s)
    (T : commitmentAddresses s extra → DigestRegister s) (m : BitString 512)
    (y : Fin s.params.ℓ → Poly) :=
  let w := moduleSISMap A y
  let digest := registerBytes s (T (commitmentAddress s extra m w))
  finishSigningAttempt s sk y w digest ((sharedXofs s extra base T).sampleInBall s digest)

/-- Finish a signing request from the current mask. The mask determines the commitment;
the selected XOF table determines the digest, the challenge expansion and all retries. -/
noncomputable def completeSigningTrial (base : Xofs) (sk : PrivateKey s) (A : PublicMatrix s)
    (T : commitmentAddresses s extra → DigestRegister s) (m : BitString 512) (seed : List Byte)
    (fuel nonce : ℕ) (y : Fin s.params.ℓ → Poly) : SigningReply s :=
  OracleComp.evalPure T (finishRequest s extra base sk A m seed fuel (nonce + s.params.ℓ)
    (trialResult s extra base sk A T m y))

/-- Supplying the mask derived from the real seed and nonce recovers the entire remaining
Algorithm 7 loop, including errors and all subsequent retries. The fresh ideal mask in the
refresh estimate replaces exactly this value. -/
theorem completeSigningTrial_expandMask (base : Xofs) (sk : PrivateKey s) (A : PublicMatrix s)
    (T : commitmentAddresses s extra → DigestRegister s) (m : BitString 512) (seed : List Byte)
    (fuel nonce : ℕ) :
    let H := sharedXofs s extra base T
    (completeSigningTrial s extra base sk A T m seed fuel nonce
      (ringVectorCoeffs (H.expandMask s seed nonce))).map FixedBytes.toList =
      OracleComp.evalPure (ExtendableOutput.Request.answer H.h256)
        (signingQueries s sk A (List.ofFn m) seed id (fuel + 1) nonce) := by
  intro H
  let y := ringVectorCoeffs (H.expandMask s seed nonce)
  let w := moduleSISMap A y
  let d := registerBytes s (T (commitmentAddress s extra m w))
  have dig : H.commitmentDigest s (highBitsVec s.params w) (List.ofFn m) = d :=
    commitmentDigest_sharedXofs s extra base T m w
  rw [evalPure_signingQueries_succ]
  dsimp only
  rw [dig]
  unfold completeSigningTrial trialResult
  dsimp only
  rcases h : finishSigningAttempt s sk y w d (H.sampleInBall s d) with _ | _ | sig
  · rfl
  · simp only [finishRequest, eval_shared_reads]
    rw [evalPure_signingQueries]
    cases hrem : OracleComp.evalPure (ExtendableOutput.Request.answer H.h256)
        (signingQueries s sk A (List.ofFn m) seed id fuel (nonce + s.params.ℓ)) with
    | none => rfl
    | some sig => exact recordReply_some s (length_of_evalPure_signingQueries hrem)
  · exact recordReply_some s (length_finishSigningAttempt
      (dig ▸ length_commitmentDigest (H := H) ..) h)

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
signing reply reaches the adversary. The distinguished trial uses the key recorded by its prefix.
The mode selects the table for retries and later queries. -/
noncomputable def signingAttemptRefreshProbability {B W O : Type} [Fintype B] [Fintype W]
    [Fintype O] (refresh : TrialRefresh) (base : Xofs) (A : PublicMatrix s) (sk : B → PrivateKey s)
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
      let result := trialResult s extra base (sk b) A H (msg b) y
      let resume := if refresh = .eraseRejected ∧ result = some none then hv.1 else H
      MeasuredPrefix.serviceAcceptance addStep
        (finishRequest s extra base (sk b) A (msg b) (seed b) fuel (nonce + s.params.ℓ) result)
        (next b) (accept b)
        resume (p.state addStep ψ hv.1 b)

private theorem abs_signingAttemptRefreshProbability_sub_le {B W O : Type} [Fintype B] [Fintype W]
    [Fintype O] (base : Xofs) (A : PublicMatrix s) (sk : B → PrivateKey s)
    (p ψ msg seed fuel nonce next accept) (hψ : ‖ψ‖ = 1) :
    |signingAttemptRefreshProbability s extra (B := B) (W := W) (O := O) .persistent base A sk p ψ
      msg seed fuel nonce next accept -
      signingAttemptRefreshProbability s extra .ambient base A sk p ψ msg seed fuel nonce
        next accept| ≤
      p.updateCost * Real.sqrt
        (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal := by
  classical
  let addr (b : B) (y : Fin s.params.ℓ → Poly) :=
    commitmentAddress s extra (msg b) (moduleSISMap A y)
  let reply (H : commitmentAddresses s extra → DigestRegister s) (b : B) (y : Fin s.params.ℓ → Poly)
      := OracleComp.evalPure H (finishRequest s extra base (sk b) A (msg b) (seed b) fuel
        (nonce + s.params.ℓ) (trialResult s extra base (sk b) A H (msg b) y))
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
    [Fintype O] (base : Xofs) (A : PublicMatrix s) (sk : B → PrivateKey s)
    (p ψ msg seed fuel nonce next accept) {F : ℝ} (hψ : ‖ψ‖ = 1)
    (future : ∀ b r, (next b r).updateCost ≤ F) :
    |signingAttemptRefreshProbability s extra (B := B) (W := W) (O := O) .eraseRejected base A sk p
        ψ msg seed fuel nonce next accept -
      signingAttemptRefreshProbability s extra .persistent base A sk p ψ msg seed fuel nonce
        next accept| ≤
      Real.sqrt (((s.params.ℓ + 2) * fuel : ℕ) + F ^ 2) * Real.sqrt
        (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal := by
  classical
  let mask := signingMaskLaw s.params (by cases s <;> decide)
  let addr (b : B) (y : Fin s.params.ℓ → Poly) :=
    commitmentAddress s extra (msg b) (moduleSISMap A y)
  let mass := (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal
  let C := Real.sqrt (((s.params.ℓ + 2) * fuel : ℕ) + F ^ 2) * Real.sqrt mass
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
      let run := finishRequest s extra base (sk b) A (msg b) (seed b) fuel
        (nonce + s.params.ℓ) (some none)
      let score (result : Option (Option (List Byte))) (T : commitmentAddresses s extra →
          DigestRegister s) := MeasuredPrefix.serviceAcceptance addStep
        (finishRequest s extra base (sk b) A (msg b) (seed b) fuel (nonce + s.params.ℓ) result)
        (next b) (accept b)
          T (u b)
      let result (y : Fin s.params.ℓ → Poly) :=
        trialResult s extra base (sk b) A (G (addr b y)) (msg b) y
      have row (y : Fin s.params.ℓ → Poly) :
          |(mask y).toReal * score (result y) (if result y = some none then H else G (addr b y)) -
            (mask y).toReal * score (result y) (G (addr b y))| ≤
            (mask y).toReal * |score (some none) (G (addr b y)) - score (some none) H| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
        refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        by_cases he : result y = some none
        · rw [ite_eq_left he, he, abs_sub_comm]
        · simp [he]
      refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun y _ => row y).trans ?_)
      rw [← Probability.PMF.sum_map_mul mask (addr b)
        (fun i => |score (some none) (G i) - score (some none) H|)]
      refine (MeasuredPrefix.mean_abs_serviceAcceptance_update_sub_le addStep run
        (next b) (accept b) H v (u b) (retry_bounded ..) (mask.map (addr b))
        (δ := mass) (fun i => ENNReal.toReal_mono finite
          (signingAddressLaw_le s extra A (msg b) i))).trans
        (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
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
    [Fintype O] (base : PublicMatrix s → Xofs) (sk : PublicMatrix s → B → PrivateKey s)
    (p : PublicMatrix s → SigningInteraction s extra W B)
    (ψ : PublicMatrix s → ValueState (commitmentAddresses s extra) (DigestRegister s) W)
    (msg : PublicMatrix s → B → BitString 512) (seed : PublicMatrix s → B → List Byte)
    (fuel nonce : ℕ) (next : PublicMatrix s → B → SigningReply s → SigningInteraction s extra W O)
    (accept : PublicMatrix s → B → SigningReply s →
      Finset (O × (commitmentAddresses s extra × DigestRegister s × W))) {C F : ℝ}
    (hψ : ∀ A, ‖ψ A‖ = 1) (budget : ∀ A, (p A).updateCost ≤ C)
    (future : ∀ A b r, (next A b r).updateCost ≤ F) :
    |(𝔼 A, signingAttemptRefreshProbability s extra .eraseRejected (base A) A (sk A) (p A) (ψ A)
      (msg A) (seed A) fuel nonce (next A) (accept A)) -
      (𝔼 A, signingAttemptRefreshProbability s extra .ambient (base A) A (sk A) (p A) (ψ A) (msg A)
        (seed A) fuel nonce (next A) (accept A))| ≤
      (C + Real.sqrt (((s.params.ℓ + 2) * fuel : ℕ) + F ^ 2)) *
        ((11 / 10) / Real.sqrt (2 ^ s.commitmentBoxBits)) := by
  let L := C + Real.sqrt (((s.params.ℓ + 2) * fuel : ℕ) + F ^ 2)
  have hL : 0 ≤ L := add_nonneg ((p 0).updateCost_nonneg.trans (budget 0)) (Real.sqrt_nonneg _)
  rw [← expect_sub_distrib]
  refine (abs_expect_le _ _).trans ((expect_le_expect (g := fun A =>
    L * (Real.sqrt (commitmentKernelSize s A) / Real.sqrt (2 ^ s.commitmentBoxBits)))
    fun A _ => ?_).trans ?_)
  · refine (abs_sub_le _ _ _).trans ((add_le_add
      (abs_eraseRejected_sub_persistent s extra (base A) A (sk A) (p A) (ψ A) (msg A)
        (seed A) fuel nonce (next A) (accept A) (hψ A) (future A))
      (abs_signingAttemptRefreshProbability_sub_le s extra (base A) A (sk A) (p A)
        (ψ A) (msg A) (seed A) fuel nonce (next A) (accept A) (hψ A))).trans ?_)
    rw [← add_mul, ← Real.sqrt_div (Nat.cast_nonneg _)]
    exact mul_le_mul (by dsimp [L]; linarith [budget A])
      (Real.sqrt_le_sqrt (commitmentGuessProbability_le_kernel_div_pow s A))
      (Real.sqrt_nonneg _) hL
  · simp_rw [← mul_expect, div_eq_mul_inv, ← expect_mul]
    gcongr
    exact (mean_sqrt_commitmentKernelSize_lt s).le

end Cslib.Crypto.MLDSA.FIPS204
