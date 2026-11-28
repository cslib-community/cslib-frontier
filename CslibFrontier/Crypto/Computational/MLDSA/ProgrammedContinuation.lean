/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.AdaptiveCommitmentCall
import all CslibFrontier.Crypto.Computational.MLDSA.AdaptiveCommitmentCall
import all CslibFrontier.Crypto.Computational.MLDSA.CommitmentContinuation
import all CslibFrontier.Crypto.Computational.MLDSA.DigestSigningQueries
import all CslibFrontier.Crypto.Computational.MLDSA.PriorCommitmentRefresh
import all CslibFrontier.Crypto.Computational.MLDSA.PublicPairSigning
import all CslibFrontier.Crypto.Computational.MLDSA.RejectedCommitmentWrites
import all CslibFrontier.Crypto.Computational.MLDSA.SigningQueryComparison
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning

/-!
# Later ML-DSA signing requests on a programmed digest register

A terminal signing write changes the common SHAKE stream before the forger's next instruction.
The verifier reads the stream left by all later requests. We use the 814-attempt signing option
from [NISTFIPS204], Appendix C. This is an original bound on the fresh-digest forgery event.
The coherent-query estimate uses the query disturbance argument of [BBBV1997].
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204.QuantumSigningForger
open Cslib.Probability Cslib.Quantum

private noncomputable def simulated (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (A : PublicMatrix s) (sk : PrivateKey s) (pk : List Byte) :
    C.Program Forgery → Register s → C.Device → List Forgery → Game
  | .pure f, D, _, log => pure (SignedMatrixTrial.newDigestWin ⟨H.withDigestRegister s D,
      A, pk, f, log⟩)
  | .liftBind (.inl coin) k, D, dev, log =>
    (ProbComp.unifOracle coin).bind fun i => simulated C s H A sk pk (k i) D dev log
  | .liftBind (.inr (.inl cmd)) k, D, dev, log =>
    (C.deviceCommand (H.withDigestRegister s D) cmd (dev, log)).bind fun (r, next, _) =>
      simulated C s H A sk pk (k r) D next log
  | .liftBind (.inr (.inr q)) k, D, dev, log =>
    registerRequest s H A sk q D false fun T r =>
      simulated C s H A sk pk (k r) T dev (q.logReply r log)

-- Scoring the continuation of the public-pair reduction uses only the current stream and log.
-- The history additionally certifies every terminal write for the downstream extractor.
private theorem simulated_eq_run (C : QuantumSigningForger) (s : Level) (H base : Xofs)
    (A : PublicMatrix s) (sk : PrivateKey s) (pk : List Byte) (prog : C.Program Forgery)
    (D : Register s) (dev : C.Device) (st : History s base sk.tr)
    (current : st.xofs = H.withDigestRegister s D) :
    C.simulated s H A sk pk prog D dev st.log =
      (ProbOracleComp.runWith (C.programmedCommands s base sk.tr (freshMaskDraw s A sk)) prog
        (dev, st)).bind fun (f, _, state) => PMF.pure (SignedMatrixTrial.newDigestWin
          ⟨state.xofs, A, pk, f, state.log⟩) := by
  induction prog generalizing D dev st with
  | pure f => simp [simulated, interp_norm, pmf_norm, current]
  | liftBind cmd k ih =>
    rw [show PFunctor.FreeM.liftBind cmd k = (OracleComp.query cmd >>= k) from rfl]
    simp only [ProbOracleComp.runWith, OracleComp.runWith_bind, OracleComp.runWith_query,
      OracleComp.sumHandler, PMF.bind_bind]
    rcases cmd with coin | cmd | ask
    · change (ProbComp.unifOracle coin).bind _ = _
      simp only [PMF.bind_map, Function.comp_def]
      exact congrArg (PMF.bind _ ·) (funext fun i => ih i D dev st current)
    · change (C.deviceCommand (H.withDigestRegister s D) cmd (dev, st.log)).bind _ = _
      simp only [programmedCommands, statefulSigningCommands, deviceCommand, OracleComp.sumHandler,
        PMF.bind_map, Function.comp_def, current]
      apply congrArg (PMF.bind _ ·)
      funext ⟨r, next⟩
      exact ih r D next st current
    · simp only [programmedCommands, statefulSigningCommands, OracleComp.sumHandler, PMF.bind_map,
        Function.comp_def]
      let next r (t : History s base sk.tr) :=
        (ProbOracleComp.runWith (C.programmedCommands s base sk.tr (freshMaskDraw s A sk))
          (k r) (dev, t)).bind fun (f, _, u) => PMF.pure (SignedMatrixTrial.newDigestWin
            ⟨u.xofs, A, pk, f, u.log⟩)
      change registerRequest s H A sk ask D false _ = _
      refine registerRequest_eq_signingCall s H base A sk ask D st current _ next ?_
      intro T r state table log
      rw [← log]
      exact ih r T dev state table

-- Charge the representative read once. Conditional on the same representative, both retry loops
-- draw the same sequence of masks and digests. A coinciding terminal write removes the difference.
private theorem registerRequest_gap (s : Level) (H : Xofs) (A : PublicMatrix s)
    (sk : PrivateKey s) (q : SigningQuery) (m : BitString 512) (D : Register s)
    (rep : Mask s → Digest s) (done : Register s → Option (List Byte) → Game) {B : ℝ}
    (tail : ∀ T (value : Mask s → Digest s) r, PMF.meanAbsDiffAt
      (signingMaskLaw s.params (by cases s <;> decide)) true
      (fun y => done (Function.update T (maskCommitmentAddress s A m y) (value y)) r)
      (fun _ => done T r) ≤ B) :
    let μ := signingMaskLaw s.params (by cases s <;> decide)
    let δ := (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal
    let W y := Function.update D (maskCommitmentAddress s A m y) (rep y)
    PMF.meanAbsDiffAt μ true (fun y => registerRequest s H A sk q (W y) false done)
      (fun _ => registerRequest s H A sk q D false done) ≤ δ + B := by
  classical
  intro μ δ W
  unfold registerRequest
  by_cases big : 255 < q.context.length
  · simpa only [big, ↓reduceIte] using
      (tail D rep none).trans (le_add_of_nonneg_left ENNReal.toReal_nonneg)
  simp only [big, ↓reduceIte, installedAttempt_eq]
  let cmd := representativeQuery H s sk.tr (formatMessage q.message q.context)
  let point T := BitString.ofList 512 (OracleComp.evalPure T cmd).toList
  let retry (p : BitString 512) T := runRetries μ (PMF.uniformOfFintype _)
    (maskCommitmentAddress s A p) (attemptResult s H A sk) done false 814 T
  have point_eq T : point T = BitString.ofList 512 ((H.withDigestRegister s T).representativeFromTr
      sk.tr (formatMessage q.message q.context)) := by simp only [point, cmd, eval_rep]
  change PMF.meanAbsDiffAt μ true (fun y => retry _ (W y)) (fun _ => retry _ D) ≤ δ + B
  simp_rw [← point_eq]
  let bad := {y | OracleComp.evalPure (W y) cmd ≠ OracleComp.evalPure D cmd}
  have one : PMF.meanAbsDiffAt μ true (fun y => retry (point (W y)) (W y))
      (fun y => retry (point D) (W y)) ≤ δ := by
    apply (meanGap_of_agree μ _ _ bad _).trans
    · have h := prob_response_changes s A m D cmd (rep_bounded ..)
      have le : μ.toOuterMeasure bad ≤
          commitmentGuessProbability s.params (by cases s <;> decide) A := by
        simp only [Nat.cast_one, one_mul] at h
        apply le_trans _ h
        exact μ.toOuterMeasure.mono (fun y (hy : y ∈ bad) => ⟨rep y, hy⟩)
      exact ENNReal.toReal_mono
        (ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun _ => PMF.coe_le_one _ _)) le
    · intro y off
      simp only [bad, Set.mem_ofPred_eq, not_not] at off
      simp only [point, off]
  exact (PMF.meanAbsDiffAt_triangle μ true _ (fun y => retry (point D) (W y)) _).trans
    (add_le_add one (terminalRetries_stable μ _ _ _ done tail 814 D rep))

private theorem simulated_readout (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (A : PublicMatrix s) (sk : PrivateKey s) (pk : List Byte) (prog : C.Program Forgery)
    (D : Register s) (log : List Forgery) :
    ∃ M : Test C, ∀ d, C.simulated s H A sk pk prog D d log = observe M d := by
  classical
  induction prog generalizing D log with
  | pure f => exact ⟨POVM.const (SignedMatrixTrial.newDigestWin
      ⟨H.withDigestRegister s D, A, pk, f, log⟩), fun d => by
      simp [simulated, observe, POVM.measureDensity_const]⟩
  | liftBind cmd k ih =>
    choose M law using ih
    let G := H.withDigestRegister s D
    rcases cmd with coin | cmd | q
    · exact ⟨POVM.mixture (ProbComp.unifOracle coin) (fun i => M i D log), fun d => by
        simp only [simulated, law, observe, POVM.measureDensity_mixture]⟩
    · simp only [simulated]
      exact device_readout G cmd log _ (fun r => ⟨M r D log, law r D log⟩)
    · by_cases big : 255 < q.context.length
      · exact ⟨M none D (q.logReply none log), fun d => by
          simp only [simulated, registerRequest, big, ↓reduceIte, law]⟩
      · simp only [simulated, registerRequest, big, ↓reduceIte]
        apply retries_readout
        intro T r
        exact ⟨_, law r T (q.logReply r log)⟩

private theorem simulated_gap (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (A : PublicMatrix s) (sk : PrivateKey s) (pk : List Byte) (m : BitString 512)
    (prog : C.Program Forgery) {qH n : ℕ}
    (hash : OracleComp.IsCostBounded (fun q => (isXofQuery q).toNat) prog qH)
    (calls : OracleComp.IsCostBounded (fun q => (isSigningCall q).toNat) prog n)
    (D : Register s) (rep : Mask s → Digest s) (d : C.Device) (log : List Forgery) :
    let μ := signingMaskLaw s.params (by cases s <;> decide)
    let δ := (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal
    let W y := Function.update D (maskCommitmentAddress s A m y) (rep y)
    PMF.meanAbsDiffAt μ true (fun y => C.simulated s H A sk pk prog (W y) d log)
      (fun _ => C.simulated s H A sk pk prog D d log) ≤ qH * (4 * √δ) + n * δ + 2 * δ := by
  classical
  intro μ δ W
  induction hash generalizing n D rep d log with
  | pure f qH =>
    exact (mean_verify_gap_le s H A m D rep pk f log).trans (le_add_of_nonneg_left (by positivity))
  | liftBind q k qH _ ih =>
    obtain ⟨fits, cont⟩ := OracleComp.IsCostBounded.liftBind_iff.mp calls
    change PMF.meanAbsDiffAt μ true (fun y => C.simulated s H A sk pk (.liftBind q k) (W y) d log)
      (fun _ => C.simulated s H A sk pk (.liftBind q k) D d log) ≤ _
    rcases q with coin | cmd | ask
    · simp only [simulated, isXofQuery, Bool.toNat_false, Nat.add_zero]
      apply PMF.meanAbsDiffAt_bind_le μ (ProbComp.unifOracle coin) true
      exact fun i => ih i (cont i) D rep d log
    · simp only [simulated]
      let G := H.withDigestRegister s D
      let K y := H.withDigestRegister s (W y)
      let left y r st := C.simulated s H A sk pk (k r) (W y) st log
      let right (_ : Mask s) r st := C.simulated s H A sk pk (k r) D st log
      apply (device_meanGap_le μ G K cmd left right d log
        (Q := 4 * √δ) (B := qH * (4 * √δ) + n * δ + 2 * δ)
        (fun y r => C.simulated_readout s H A sk pk (k r) (W y) log) ?_ ?_).trans_eq
      · rw [Nat.cast_add]
        ring
      · intro M
        exact mean_query_gap_of_root μ G K d M ENNReal.toReal_nonneg
          (H.sq_sqrt_readout_after_maskCommitment_le s A m D rep C.addressBits C.responseBytes
            C.workQubits d M true)
      · intro r st
        simpa only [left, right, isSigningCall, Sum.elim_inr, Sum.elim_inl, Bool.toNat_false,
          Nat.sub_zero, δ] using ih r (cont r) D rep st log
    · let done T r := C.simulated s H A sk pk (k r) T d (ask.logReply r log)
      have bound := registerRequest_gap s H A sk ask m D rep done
        (B := qH * (4 * √δ) + ((n - 1 : ℕ) : ℝ) * δ + 2 * δ) (fun T value r => by
          simpa only [isSigningCall, Sum.elim_inr, Sum.elim_inl, Bool.toNat_true, done, δ]
            using ih r (cont r) T value d (ask.logReply r log))
      have len : n = n - 1 + 1 := by
        change 1 ≤ n at fits
        lia
      simp only [simulated, isXofQuery, Bool.toNat_false, Nat.add_zero]
      apply bound.trans_eq
      conv_rhs => rw [len, Nat.cast_add_one]
      ring

-- The encoded public key has a different input length from every row of the digest register.
private theorem simulated_eq_publicPair (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (rho : FixedBytes 32) (pair : MLDSA.SecretKey s.params)
    (h₁ : ∀ i j, |(pair.s₁ i j).valMinAbs| ≤ s.params.η)
    (h₂ : ∀ i j, |(pair.s₂ i j).valMinAbs| ≤ s.params.η) (D : Register s) :
    let pk := encodePublic s rho.toList pair.publicKey.t
    let tr := H.h256.readBytes pk 64
    let sk : PrivateKey s := ⟨rho.toList, List.replicate 32 0, tr, pair.s₁, pair.s₂,
      publicKeyLowPart s.params 13 pair.publicKey⟩
    C.simulated s H pair.A sk pk (C.program pk) D C.initialDevice [] =
      (C.publicPairSigning s (H.withDigestRegister s D) rho pair.publicKey).map
        (·.trial.newDigestWin) := by
  intro pk tr sk
  let G := H.withDigestRegister s D
  have len : pk.length = 32 + 320 * s.params.k := by simp [pk, encodePublic]
  have sep : 8 * pk.length ≠ s.commitmentInputBits := by rw [len]; cases s <;> decide
  have key : G.h256.readBytes pk 64 = tr := by
    simp only [G, tr, ExtendableOutput.readBytes, Xofs.withDigestRegister, Xofs.withPrefixRegister,
      Xofs.withPrefixLists, ExtendableOutput.withPrefixes, Keccak.length_bytesToBitsLE,
      sep, ↓reduceIte]
  let st : History s G sk.tr := ⟨G, [], [], .initial, by simp, by simp⟩
  have runs := C.simulated_eq_run s H G pair.A sk pk (C.program pk) D C.initialDevice st rfl
  have draws : freshMaskDraw s pair.A sk = publicDraw s pair.publicKey :=
    funext fun T => freshMaskDraw_eq s pair rho.toList (List.replicate 32 0) tr T h₁ h₂
  rw [draws] at runs
  change _ = (C.runProgrammed s G pair.A pk (G.h256.readBytes pk 64)
    (publicDraw s pair.publicKey)).map (·.trial.newDigestWin)
  rw [key]
  simp only [runProgrammed, runSigningProgram, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.map_bind, PMF.pure_map]
  exact runs

/-- A fresh mask chooses one commitment in the initial SHAKE table. Even when every subsequent
signing request uses the public-pair simulator and updates that same table, replacing this digest
costs at most one classical lookup per request, two for final verification, and four times the
square root of the commitment guess probability per coherent query. The public pair here is the
real pair of a short ML-DSA key, before the decision-MLWE switch. -/
theorem mean_publicPairSigning_gap_le (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (rho : FixedBytes 32) (pair : MLDSA.SecretKey s.params)
    (h₁ : ∀ i j, |(pair.s₁ i j).valMinAbs| ≤ s.params.η)
    (h₂ : ∀ i j, |(pair.s₂ i j).valMinAbs| ≤ s.params.η) (m : BitString 512)
    (D : BitString s.commitmentInputBits → BitString (8 * digestBytes s))
    (replacement : (Fin s.params.ℓ → Poly) → BitString (8 * digestBytes s))
    {qH n : ℕ} (hash : C.XofCallsLe qH) (calls : C.SigningCallsLe n) :
    let μ := signingMaskLaw s.params (by cases s <;> decide)
    let δ := (commitmentGuessProbability s.params (by cases s <;> decide) pair.A).toReal
    let win T := Game.succProbability ((C.publicPairSigning s (H.withDigestRegister s T)
      rho pair.publicKey).map (·.trial.newDigestWin))
    ∑ y, (μ y).toReal * |(win (Function.update D (maskCommitmentAddress s pair.A m y)
      (replacement y)) : ℝ) - (win D : ℝ)| ≤ 4 * qH * √δ + (n + 2) * δ := by
  intro μ δ win
  let pk := encodePublic s rho.toList pair.publicKey.t
  let sk : PrivateKey s := ⟨rho.toList, List.replicate 32 0, H.h256.readBytes pk 64,
    pair.s₁, pair.s₂, publicKeyLowPart s.params 13 pair.publicKey⟩
  have bound := C.simulated_gap s H pair.A sk pk m (C.program pk) (hash pk) (calls pk)
    D replacement C.initialDevice []
  have law := C.simulated_eq_publicPair s H rho pair h₁ h₂
  change ∀ T, C.simulated s H pair.A sk pk (C.program pk) T C.initialDevice [] = _ at law
  simp only [PMF.meanAbsDiffAt, law] at bound
  apply bound.trans_eq
  dsimp only [δ]
  ring

end Cslib.Crypto.MLDSA.FIPS204.QuantumSigningForger
