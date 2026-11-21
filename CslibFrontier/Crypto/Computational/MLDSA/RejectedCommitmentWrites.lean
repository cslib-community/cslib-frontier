/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.CommitmentContinuation
public import CslibFrontier.Crypto.Computational.MLDSA.PublicPairSigning
import all CslibFrontier.Crypto.Computational.MLDSA.PublicPairSigning
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumCommitmentRegister
import all CslibFrontier.Crypto.Computational.MLDSA.CommitmentContinuation
import all CslibFrontier.Crypto.Computational.MLDSA.SigningQueryComparison
import all CslibFrontier.Crypto.Computational.MLDSA.SigningHedges
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204Signing
import all CslibFrontier.Crypto.Computational.MLDSA.DigestSigningQueries

/-!
# Erasing rejected commitment writes in one ML-DSA signing request

Both experiments refresh the mask and commitment digest on each attempt. They use the minimum
signing cap of 814 in [NISTFIPS204], Appendix C, Table 3. The persistent experiment installs the
digest on the shared SHAKE256 stream, reads it through the native attempt, and retains the write
on rejection. The other experiment runs the terminal-write handler used in the public-pair
simulation. Algorithm 29 exhaustion terminates and publishes a digest in both.

For the expanded public matrix let `δ` be the largest mass of a rounded mask commitment.
Erasure changes the success probability of a subsequent fresh-digest forgery by at most
`814 * (4 * qH * √δ + (815 * qS + 2) * δ)`. The program may branch on the signature or error
and retains its current quantum state. The comparison sums over masks before conditioning on a
rejection, and later overwrites of the same raw address supersede the earlier value in both games.
This is an original single-request comparison for the FIPS instantiation. The rejection issue in
the CMA reduction for Fiat–Shamir with aborts is analyzed in [BarbosaEtAl2023], §3.1, Figure 2.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

/-- Installing a replacement digest in the bit table gives precisely the same full SHAKE pair
as writing its byte prefix on the corresponding raw stream, including beyond the digest. -/
theorem Xofs.withDigestRegister_update (H : Xofs) (s : Level) (D)
    (i : BitString s.commitmentInputBits) (v : FixedBytes (digestBytes s)) :
    H.withDigestRegister s (Function.update D i ((Keccak.fixedBytesEquivBitsLE _) v)) =
      (H.withDigestRegister s D).writeCommitment (List.ofFn i) v.toList := by
  classical
  apply congrArg (Xofs.mk H.h128)
  apply ExtendableOutput.ext_byteAt
  intro x j
  by_cases eq : x = List.ofFn i
  · subst x
    simp only [Xofs.withDigestRegister, ExtendableOutput.byteAt_withPrefixes,
      List.length_ofFn, ↓reduceIte, BitString.ofList_ofFn, Function.update_self,
      Equiv.symm_apply_apply, Option.bind_some]
    by_cases hj : j < digestBytes s
    · simp [getElem?_pos, hj, FixedBytes.length_toList]
    · simp [getElem?_neg, hj, FixedBytes.length_toList]
  · by_cases len : x.length = s.commitmentInputBits
    · have ne : BitString.ofList _ x ≠ i := fun h => eq
        ((BitString.ofFn_ofList len).symm.trans (congrArg List.ofFn h))
      simp [Xofs.withDigestRegister, ExtendableOutput.byteAt_withPrefixes,
        eq, len, Function.update_of_ne ne]
    · simp [Xofs.withDigestRegister, ExtendableOutput.byteAt_withPrefixes,
        eq, len]

namespace QuantumSigningForger
open Cslib.Probability Cslib.Quantum

section Retry
variable {Y I V R : Type} [Fintype Y] [Finite V] [DecidableEq I]

private noncomputable def runRegisterRetries (μ : PMF Y) (ν : PMF V) (addr : Y → I)
    (out : (I → V) → Y → V → Option (Option R)) (done : (I → V) → Option R → Game) (keep : Bool) :
    ℕ → (I → V) → Game
  | 0, D => done D none
  | n + 1, D => do
    let v ← ν
    let y ← μ
    let write := Function.update D (addr y) v
    match out D y v with
    | some r => done write r
    | none => runRegisterRetries μ ν addr out done keep n (if keep then write else D)

private noncomputable abbrev runRetries (μ : PMF Y) (ν : PMF V) (addr : Y → I)
    (out : Y → V → Option (Option R)) (done : (I → V) → Option R → Game) (keep : Bool) :=
  runRegisterRetries μ ν addr (fun _ => out) done keep

omit [Finite V] in
private theorem update_then_write (D : I → V) (x i : I) (v w : V) :
    Function.update (Function.update D x v) i w =
      Function.update (Function.update D i w) x (if x = i then w else v) := by
  by_cases h : x = i
  · subst i
    simp [Function.update_idem]
  · rw [ite_eq_right h, Function.update_comm h]

-- A later terminal write at the sampled address removes the earlier change on both branches.
private theorem terminalRetries_stable (μ : PMF Y) (ν : PMF V) (addr : Y → I)
    {target : Y → I} (out : Y → V → Option (Option R)) (done : (I → V) → Option R → Game) {B : ℝ}
    (tail : ∀ D (rep : Y → V) r,
      PMF.meanAbsDiffAt μ true (fun y => done (Function.update D (target y) (rep y)) r)
        (fun _ => done D r) ≤ B)
    (fuel : ℕ) (D : I → V) (rep : Y → V) :
    PMF.meanAbsDiffAt μ true (fun y => runRetries μ ν addr out done false fuel
        (Function.update D (target y) (rep y)))
      (fun _ => runRetries μ ν addr out done false fuel D) ≤ B := by
  induction fuel generalizing D with
  | zero => exact tail D rep none
  | succ fuel ih =>
    simp only [runRegisterRetries, PMF.monad_bind_eq_bind, Bool.false_eq_true, ↓reduceIte]
    apply PMF.meanAbsDiffAt_bind_le μ ν true
    intro v
    apply PMF.meanAbsDiffAt_bind_le μ μ true
    intro z
    cases h : out z v with
    | none => exact ih D
    | some r =>
      simp only [update_then_write D _ (addr z) _ v]
      exact tail _ _ r

private theorem eraseRetries_le (μ : PMF Y) (ν : PMF V) (addr : Y → I)
    (out : Y → V → Option (Option R)) (done : (I → V) → Option R → Game) {B : ℝ} (hb : 0 ≤ B)
    (tail : ∀ D (rep : Y → V) r,
      PMF.meanAbsDiffAt μ true (fun y => done (Function.update D (addr y) (rep y)) r)
        (fun _ => done D r) ≤ B)
    (fuel : ℕ) (D : I → V) :
    |(runRetries μ ν addr out done true fuel D true).toReal -
      (runRetries μ ν addr out done false fuel D true).toReal| ≤ fuel * B := by
  let _ := Fintype.ofFinite V
  induction fuel generalizing D with
  | zero => simp [runRegisterRetries]
  | succ fuel ih =>
    simp only [runRegisterRetries, PMF.monad_bind_eq_bind, Bool.false_eq_true, ↓reduceIte,
      Nat.cast_add_one]
    apply (PMF.abs_bind_sub_le_meanAbsDiffAt ν true _ _).trans
    apply PMF.sum_mul_le
    intro v
    apply (PMF.abs_bind_sub_le_meanAbsDiffAt μ true _ _).trans
    let W y := Function.update D (addr y) v
    let go keep T := runRetries μ ν addr out done keep fuel T
    let mid y := match out y v with
      | some r => done (W y) r
      | none => go false (W y)
    refine (PMF.meanAbsDiffAt_triangle μ true _ mid _).trans ?_
    have h₁ : PMF.meanAbsDiffAt μ true (fun y => match out y v with
        | some r => done (W y) r | none => go true (W y)) mid ≤ fuel * B := by
      apply PMF.sum_mul_le
      intro y
      cases e : out y v with
      | none => simpa only [mid, e] using ih (W y)
      | some r => simpa only [mid, e, sub_self, abs_zero] using mul_nonneg (Nat.cast_nonneg fuel) hb
    -- Charge the fresh mask at its original mass even if the norm or hint test rejects it.
    have h₂ : PMF.meanAbsDiffAt μ true mid (fun y => match out y v with
        | some r => done (W y) r | none => go false D) ≤ B := by
      apply le_trans _ (terminalRetries_stable μ ν addr out done tail fuel D (fun _ => v))
      apply Finset.sum_le_sum
      intro y _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      cases e : out y v with
      | none => simp only [mid, e, go, W, le_refl]
      | some r => simp [mid, e]
    exact (add_le_add h₁ h₂).trans_eq (by ring)
end Retry

private def attemptResult (s : Level) (H : Xofs) (A : PublicMatrix s) (sk : PrivateKey s)
    (y : Fin s.params.ℓ → Poly) (v : BitString (8 * digestBytes s)) :=
  let d := (Keccak.fixedBytesEquivBitsLE (digestBytes s)).symm v
  terminalReply (finishSigningAttempt s sk y (moduleSISMap A y) d.toList
    (H.sampleInBall s d.toList))

private def installedAttempt (s : Level) (H : Xofs) (A : PublicMatrix s) (sk : PrivateKey s)
    (m : BitString 512) (D : BitString s.commitmentInputBits → BitString (8 * digestBytes s))
    (y : Fin s.params.ℓ → Poly) (v : BitString (8 * digestBytes s)) :=
  let T := Function.update D (maskCommitmentAddress s A m y) v
  terminalReply ((H.withDigestRegister s T).attemptWithMask s sk A (List.ofFn m) y)

private theorem installedAttempt_eq (s : Level) (H : Xofs) (A : PublicMatrix s)
    (sk : PrivateKey s) (m : BitString 512) :
    installedAttempt s H A sk m = fun _ => attemptResult s H A sk := by
  funext D y v
  simp only [installedAttempt, Xofs.attemptWithMask, AttemptCommitment.ofMask,
    tabulateRingVector_eq, digest_at H s _ _ List.length_ofFn, maskCommitmentAddress,
    Function.update_self, challenge_off, attemptResult, digestBytesAt]

-- The continuation sees the final digest register on every exit, including exhaustion.
private noncomputable def registerRequest (s : Level) (H : Xofs) (A : PublicMatrix s)
    (sk : PrivateKey s) (q : SigningQuery)
    (D : BitString s.commitmentInputBits → BitString (8 * digestBytes s)) (keepRejected : Bool)
    (done : (BitString s.commitmentInputBits → BitString (8 * digestBytes s)) →
      Option (List Byte) → Game) : Game :=
  if 255 < q.context.length then done D none else
    let m := BitString.ofList 512 ((H.withDigestRegister s D).representativeFromTr sk.tr
      (formatMessage q.message q.context))
    runRegisterRetries (signingMaskLaw s.params (by cases s <;> decide)) (PMF.uniformOfFintype _)
      (maskCommitmentAddress s A m) (installedAttempt s H A sk m) done keepRejected 814 D

/-- Resume the current signing request from its decoded key and matrix. Each attempt draws a
fresh mask and digest. The two rules differ only on norm or hint rejection. Sparse-challenge
exhaustion is terminal and publishes the attempted digest, as does a successful signature. -/
private noncomputable def retryCall (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (A : PublicMatrix s) (keys : KeyPair) (sk : PrivateKey s) (q : SigningQuery)
    (D : BitString s.commitmentInputBits → BitString (8 * digestBytes s)) (keepRejected : Bool)
    (k : Option (List Byte) → C.Program Forgery) (dev : C.Device) (log : List Forgery)
    (rows : List (FixedBytes 2 → FixedBytes (maskPolyBytes s))) : Game :=
  registerRequest s H A sk q D keepRejected fun T r =>
    C.expansionContinuation s (H.withDigestRegister s T) A keys (k r) dev (q.logReply r log) rows

/-- Erasing every rejected digest of one entire capped FIPS signing request changes the
fresh-digest forgery probability by at most 814 times the native future-observation bound.
All later signing replies, coherent queries, measurements and verification run on the
resulting stream. The rejection decision uses the sampled mask, digest and actual secret key. -/
private theorem abs_retryCall_keep_sub_erase_le (C : QuantumSigningForger) (s : Level)
    (H : Xofs) (A : PublicMatrix s) (keys : KeyPair) (sk : PrivateKey s) (q : SigningQuery)
    (D : BitString s.commitmentInputBits → BitString (8 * digestBytes s))
    (k : Option (List Byte) → C.Program Forgery) (dev : C.Device) (log : List Forgery)
    (rows : List (FixedBytes 2 → FixedBytes (maskPolyBytes s))) {qH qS : ℕ}
    (hash : ∀ r, OracleComp.IsCostBounded (fun cmd => (isXofQuery cmd).toNat) (k r) qH)
    (calls : ∀ r, OracleComp.IsCostBounded (fun cmd => (isSigningCall cmd).toNat) (k r) qS) :
    let δ := (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal
    let p keep := Game.succProbability (C.retryCall s H A keys sk q D keep k dev log rows)
    |(p true : ℝ) - (p false : ℝ)| ≤ 814 * (4 * qH * √δ + (815 * qS + 2) * δ) := by
  classical
  intro δ p
  simp only [p, Game.coe_succProbability, retryCall, registerRequest, installedAttempt_eq]
  split
  · simp only [sub_self, abs_zero]
    positivity
  · apply eraseRetries_le _ _ _ _ _ (by positivity)
    intro T rep r
    exact C.mean_expansionContinuation_gap_le s H A _ T rep keys (k r) dev
      (q.logReply r log) rows (hash r) (calls r)

private theorem score_recordBytes (s : Level) (H : Xofs) (w : Fin s.params.k → Fin 256 → ℤ)
    (d : FixedBytes (digestBytes s)) (raw : Option (List Byte)) (h)
    (miss : Game) (ret : (Fin s.params.k → Fin 256 → ℤ) → FixedBytes (digestBytes s) →
      Option (List Byte) → Game) :
    (match recordBytes (H := H) d w raw h with
     | none => miss | some t => ret t.point t.digest t.reply) =
    raw.elim miss (fun sig => ret w d (some sig)) := by
  cases raw <;> rfl

private theorem score_freshMaskDraw (s : Level) (H : Xofs) (A : PublicMatrix s)
    (sk : PrivateKey s) (D : BitString s.commitmentInputBits → BitString (8 * digestBytes s))
    (miss : Game) (ret : (Fin s.params.k → Fin 256 → ℤ) → FixedBytes (digestBytes s) →
      Option (List Byte) → Game) :
    let G := H.withDigestRegister s D
    let bits := Keccak.fixedBytesEquivBitsLE (digestBytes s)
    let μ := signingMaskLaw s.params (by cases s <;> decide)
    (freshMaskDraw s A sk G).bind (fun | none => miss | some t => ret t.point t.digest t.reply) =
    (PMF.uniformOfFintype _).bind fun v => μ.bind fun y =>
      match attemptResult s H A sk y v with
      | some r => ret (highBitsVec s.params (moduleSISMap A y)) (bits.symm v) r
      | none => miss := by
  classical
  intro G bits μ
  rw [← PMF.uniformOfFintype_map_equiv bits, PMF.bind_map]
  simp only [freshMaskDraw, draw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind]
  apply congrArg (PMF.bind (PMF.uniformOfFintype (FixedBytes (digestBytes s))) ·)
  funext d
  have same : G.sampleInBall s d.toList = H.sampleInBall s d.toList := challenge_off H s D d
  split
  · rename_i hg
    have hc := same.symm.trans hg
    simp only [PMF.bind_bind, PMF.pure_bind, Function.comp_def, bits, Equiv.symm_apply_apply,
      attemptResult, hc, finishSigningAttempt, Option.bind_eq_bind, Option.bind_none, terminalReply]
    rfl
  · rename_i c hg
    have hc := same.symm.trans hg
    simp only [PMF.bind_bind, PMF.pure_bind, Function.comp_def, bits, Equiv.symm_apply_apply,
      attemptResult, hc]
    apply congrArg (PMF.bind μ ·)
    funext y
    rw [score_recordBytes]
    cases h : compressedResponse s.params (hintLimit s) sk.s₁ sk.s₂ sk.t₀ y (moduleSISMap A y)
        (Vector.ofFn c).get with
    | none => simp [finishSigningAttempt, h, terminalReply]
    | some sig => simp [finishSigningAttempt, h, terminalReply]

private theorem erase_eq_freshMaskDraw (s : Level) (H : Xofs) (A : PublicMatrix s)
    (sk : PrivateKey s) (m : BitString 512)
    (D : BitString s.commitmentInputBits → BitString (8 * digestBytes s))
    (done : (BitString s.commitmentInputBits → BitString (8 * digestBytes s)) →
      Option (List Byte) → Game) (xs : List ℕ) :
    let G := H.withDigestRegister s D
    let bits := Keccak.fixedBytesEquivBitsLE (digestBytes s)
    let μ := signingMaskLaw s.params (by cases s <;> decide)
    runRetries μ (PMF.uniformOfFintype _) (maskCommitmentAddress s A m)
      (attemptResult s H A sk) done false xs.length D =
    (xs.findSomeM? fun _ => freshMaskDraw s A sk G).bind fun
      | none => done D none
      | some t => done (Function.update D
          (BitString.ofList _ (commitmentInput s t.point (List.ofFn m))) (bits t.digest))
            t.reply := by
  classical
  intro G bits μ
  induction xs with
  | nil =>
    simp only [List.length_nil, runRegisterRetries, List.findSomeM?_nil, PMF.monad_pure_eq_pure,
      PMF.pure_bind]
  | cons x xs ih =>
    rw [List.length_cons, runRetries, runRegisterRetries, List.findSomeM?_cons]
    simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
      Bool.false_eq_true, ↓reduceIte]
    let miss := runRetries μ (PMF.uniformOfFintype _) (maskCommitmentAddress s A m)
      (attemptResult s H A sk) done false xs.length D
    let ret w (d : FixedBytes (digestBytes s)) r := done (Function.update D
      (BitString.ofList _ (commitmentInput s w (List.ofFn m))) (bits d)) r
    trans (freshMaskDraw s A sk G).bind (fun
      | none => miss | some t => ret t.point t.digest t.reply)
    · rw [score_freshMaskDraw]
      apply congrArg (PMF.bind _ ·)
      funext v
      apply congrArg (PMF.bind _ ·)
      funext y
      cases e : attemptResult s H A sk y v <;>
        simp only [ret, bits, Equiv.apply_symm_apply, maskCommitmentAddress, miss, μ]
    · apply congrArg (PMF.bind _ ·)
      funext t
      cases t with
      | none => exact ih
      | some t => simp only [PMF.pure_bind, ret]

private theorem registerRequest_eq_signingCall (s : Level) (H base : Xofs)
    (A : PublicMatrix s) (sk : PrivateKey s) (q : SigningQuery)
    (D : BitString s.commitmentInputBits → BitString (8 * digestBytes s))
    (st : History s base sk.tr) (current : st.xofs = H.withDigestRegister s D)
    (done : (BitString s.commitmentInputBits → BitString (8 * digestBytes s)) →
      Option (List Byte) → Game) (next : Option (List Byte) → History s base sk.tr → Game)
    (agree : ∀ T r state, state.xofs = H.withDigestRegister s T →
      state.log = q.logReply r st.log → done T r = next r state) :
    registerRequest s H A sk q D false done =
      (signingCall s sk.tr (freshMaskDraw s A sk) q st).bind fun (r, state) => next r state := by
  classical
  obtain ⟨X, log, writes, hist, exhausted, signed⟩ := st
  change X = H.withDigestRegister s D at current
  subst X
  let G := H.withDigestRegister s D
  let fmt := formatMessage q.message q.context
  let m := BitString.ofList 512 (G.representativeFromTr sk.tr fmt)
  have mEq : List.ofFn m = G.representativeFromTr sk.tr fmt := BitString.ofFn_ofList
    (by simp only [Xofs.representativeFromTr, Keccak.length_bytesToBitsLE, G.h256.length_read])
  by_cases ctx : 255 < q.context.length
  · simp only [registerRequest, signingCall, ctx, ↓reduceIte, PMF.monad_pure_eq_pure, PMF.pure_bind]
    exact agree D none _ rfl rfl
  · simp only [registerRequest, signingCall, ctx, ↓reduceIte, installedAttempt_eq,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind]
    have runs := erase_eq_freshMaskDraw s H A sk m D done (List.range 814)
    rw [List.length_range] at runs
    refine runs.trans ?_
    apply congrArg (PMF.bind ((List.range 814).findSomeM? fun _ => freshMaskDraw s A sk G) ·)
    funext t
    cases t with
    | none =>
      simp only [PMF.pure_bind]
      exact agree D none _ rfl rfl
    | some t =>
      simp only [PMF.pure_bind]
      apply agree _ _ _ _ rfl
      have length := commitmentInput_length s t.point (μ := List.ofFn m) List.length_ofFn
      rw [Xofs.withDigestRegister_update, BitString.ofFn_ofList length, mEq]

/-- Compare the two ways to handle rejected commitment writes in one hedged signing request
after masks and digests have been refreshed. With `keepRejected = false` the request is served
by the handler from `freshMaskSigning`. A successful reply is logged before the retained
quantum program resumes. Setup uses the encoded secret key and its expanded public matrix. -/
noncomputable def freshDigestSigningCall (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (keys : KeyPair) (q : SigningQuery) (D : BitString s.commitmentInputBits →
      BitString (8 * digestBytes s)) (keepRejected : Bool)
    (k : Option (List Byte) → C.Program Forgery) (dev : C.Device) (log : List Forgery)
    (rows : List (FixedBytes 2 → FixedBytes (maskPolyBytes s))) : Game :=
  match decodePrivate s keys.secretKey with
  | none => pure false
  | some sk => match H.expandA s sk.rho with
    | none => pure false
    | some A =>
      if keepRejected then C.retryCall s H A keys sk q D true k dev log rows else
        let G := H.withDigestRegister s D
        let st : History s G sk.tr := ⟨G, log, [], .initial, by simp, by simp⟩
        (signingCall s sk.tr (freshMaskDraw s A sk) q st).bind fun (r, state) =>
          C.expansionContinuation s state.xofs A keys (k r) dev state.log rows

/-- Restoring all rejected digest writes in one capped request costs at most 814 times the
one-write observation bound for its remaining program. Both games decode the supplied keys
and expand their matrix. A setup failure loses in both. The expectation includes every mask,
digest, rejection and terminal error, and the remaining native forgery experiment. -/
theorem abs_freshDigestSigningCall_keep_sub_erase_le (C : QuantumSigningForger) (s : Level)
    (H : Xofs) (keys : KeyPair) (q : SigningQuery) (D : BitString s.commitmentInputBits →
      BitString (8 * digestBytes s)) (k : Option (List Byte) → C.Program Forgery)
    (dev : C.Device) (log : List Forgery)
    (rows : List (FixedBytes 2 → FixedBytes (maskPolyBytes s)))
    {qH qS : ℕ}
    (hash : ∀ r, OracleComp.IsCostBounded (fun cmd => (isXofQuery cmd).toNat) (k r) qH)
    (calls : ∀ r, OracleComp.IsCostBounded (fun cmd => (isSigningCall cmd).toNat) (k r) qS) :
    let p keep := Game.succProbability (C.freshDigestSigningCall s H keys q D keep k dev log rows)
    |(p true : ℝ) - (p false : ℝ)| ≤ ((do
      let sk ← decodePrivate s keys.secretKey
      let A ← H.expandA s sk.rho
      let δ := (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal
      return 814 * (4 * qH * √δ + (815 * qS + 2) * δ)) : Option ℝ).getD 0 := by
  classical
  intro p
  simp only [p, freshDigestSigningCall]
  cases hsk : decodePrivate s keys.secretKey with
  | none => simp
  | some sk =>
    cases hm : H.expandA s sk.rho with
    | none => simp [hm]
    | some A =>
      let G := H.withDigestRegister s D
      let st : History s G sk.tr := ⟨G, log, [], .initial, by simp, by simp⟩
      have same := registerRequest_eq_signingCall s H G A sk q D st rfl
        (fun T r => C.expansionContinuation s (H.withDigestRegister s T) A keys
          (k r) dev (q.logReply r st.log) rows)
        (fun r state => C.expansionContinuation s state.xofs A keys (k r) dev state.log rows)
        (fun T r state table log => by rw [table, log])
      have bound := abs_retryCall_keep_sub_erase_le C s H A keys sk q D k dev st.log rows hash calls
      dsimp only at bound
      unfold retryCall at bound
      rw [same] at bound
      simpa only [retryCall, hm, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
        Option.getD_some, Bool.false_eq_true, ↓reduceIte, st, G] using bound

private theorem scored_no_sign (C : QuantumSigningForger) (s : Level) (base : Xofs)
    (A : PublicMatrix s) (keys : KeyPair) (sk : PrivateKey s) (prog : C.Program Forgery)
    (nosign : OracleComp.IsCostBounded (fun cmd => (isSigningCall cmd).toNat) prog 0)
    (d : C.Device) (st : History s base sk.tr) :
    C.expansionContinuation s st.xofs A keys prog d st.log [] =
      (ProbOracleComp.runWith (C.programmedCommands s base sk.tr (freshMaskDraw s A sk)) prog
        (d, st)).bind fun (f, _, state) => PMF.pure (SignedMatrixTrial.newDigestWin
          ⟨state.xofs, A, keys.publicKey, f, state.log⟩) := by
  classical
  induction prog using OracleComp.induction generalizing d st with
  | pure f => simp [expansionContinuation, scored, interp_norm, pmf_norm, POVM.measureDensity_const]
  | query_bind cmd k ih =>
    obtain ⟨fits, tail⟩ := OracleComp.IsCostBounded.liftBind_iff.mp nosign
    simp only [PFunctor.FreeM.bind_eq_bind]
    rcases cmd with coin | cmd | ask
    · simp only [expansionContinuation, scored_coin (C := C) (coin := coin) (k := k),
        ProbOracleComp.runWith, OracleComp.runWith_bind, OracleComp.runWith_query,
        OracleComp.sumHandler, PMF.bind_map, PMF.bind_bind, Function.comp_def]
      exact congrArg (PMF.bind _ ·) (funext fun i => ih i (tail i) d st)
    · simp only [ProbOracleComp.runWith, OracleComp.runWith_bind, OracleComp.runWith_query,
        OracleComp.sumHandler]
      simp only [programmedCommands, OracleComp.sumHandler, PMF.bind_map, PMF.bind_bind,
        Function.comp_def, expansionContinuation, scored_step (C := C) (q := .inr (.inl cmd))
          (k := k), OracleComp.withSampleListWhen,
        isSigningCall, Sum.elim_inr, Sum.elim_inl, Bool.false_eq_true, ↓reduceIte,
        signingCommand, deviceCommand, StateT.run, pmf_norm]
      apply congrArg (PMF.bind _ ·)
      funext ⟨bits, next⟩
      exact ih bits (tail bits) next st
    · simp [isSigningCall] at fits

/-- For a forger whose first instruction requests the only signature, the terminal-write
experiment on encoded keys has exactly the fresh-digest win law of `freshMaskSigning`.
The continuation may branch on the reply, toss coins, measure and query SHAKE coherently. -/
theorem freshDigestSigningCall_eq_freshMaskSigning_of_single_call
    (C : QuantumSigningForger) (s : Level) (H : Xofs) (keys : KeyPair) (q : SigningQuery)
    (D : BitString s.commitmentInputBits → BitString (8 * digestBytes s))
    (k : Option (List Byte) → C.Program Forgery)
    (first : C.program keys.publicKey = OracleComp.query (.inr (.inr q)) >>= k)
    (last : ∀ r, OracleComp.IsCostBounded (fun cmd => (isSigningCall cmd).toNat) (k r) 0) :
    C.freshDigestSigningCall s H keys q D false k C.initialDevice [] [] =
      (C.freshMaskSigning s (H.withDigestRegister s D) keys).map
        (·.any (·.trial.newDigestWin)) := by
  classical
  let G := H.withDigestRegister s D
  have matrix (rho) : G.expandA s rho = H.expandA s rho := rfl
  simp only [freshDigestSigningCall, freshMaskSigning, ← show G = H.withDigestRegister s D from rfl,
    matrix, Bool.false_eq_true, ↓reduceIte]
  cases hd : decodePrivate s keys.secretKey with
  | none => simp [pmf_norm]
  | some sk =>
    cases ha : H.expandA s sk.rho with
    | none => simp [ha, pmf_norm]
    | some A =>
      simp only [ha, runProgrammed, first, ProbOracleComp.runWith, OracleComp.runWith_bind,
        OracleComp.runWith_query, OracleComp.sumHandler, programmedCommands, PMF.map_bind,
        PMF.bind_map, Function.comp_def, pmf_norm]
      apply congrArg (PMF.bind _ ·)
      funext ⟨r, state⟩
      exact scored_no_sign C s G A keys sk (k r) (last r) C.initialDevice state

end QuantumSigningForger
end Cslib.Crypto.MLDSA.FIPS204
