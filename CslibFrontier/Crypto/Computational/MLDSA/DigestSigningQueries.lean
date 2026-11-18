/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.QuantumCommitmentRegister
public import CslibFrontier.Crypto.Computational.MLDSA.SigningROM
public import CslibFrontier.Languages.Probabilistic.Oracle.EvalPure
public import CslibFrontier.Languages.Probabilistic.QueriesWith
import CslibFrontier.Languages.Probabilistic.Traverse.FindM
import CslibFrontier.Probability.PMF.Union
import all CslibFrontier.Crypto.Computational.MLDSA.SigningROM
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204Signing
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumCommitmentRegister

/-!
# Commitment-table queries of a complete FIPS 204 signing request

After fixing the background SHAKE streams and hedge, the signer needs at most one commitment-table
lookup per retry and one for the representative. Its mask seed, per-nonce masks and sparse
challenge expansion use other input lengths. The program below returns the bytes or error of
[NISTFIPS204], Algorithms 2 and 7. The query count concerns the register of commitment-length
SHAKE256 prefixes. Local computation and reads of the fixed background streams are free.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability

/-- Classical oracle programs on the raw SHAKE256 commitment-length digest prefixes. -/
abbrev DigestReads (s : Level) :=
  OracleComp (fun _ : BitString s.commitmentInputBits => BitString (8 * digestBytes s))

private theorem read_off (H : Xofs) (s : Level) (D) (x : List Bool) (n : ℕ)
    (h : x.length ≠ s.commitmentInputBits) :
    (H.withDigestRegister s D).h256.read x n = H.h256.read x n := by
  simp [Xofs.withDigestRegister, ExtendableOutput.withPrefixes, h]

private theorem challenge_off (H : Xofs) (s : Level) (D) (v : FixedBytes (digestBytes s)) :
    (H.withDigestRegister s D).sampleInBall s v.toList = H.sampleInBall s v.toList := by
  unfold Xofs.sampleInBall ExtendableOutput.readBytes
  rw [read_off H s D _ _ (by
    rw [Keccak.length_bytesToBitsLE, FixedBytes.length_toList]
    cases s <;> decide)]

private def digestBytesAt (s : Level) (v : BitString (8 * digestBytes s)) :=
  (Keccak.fixedBytesEquivBitsLE _).symm v

private theorem digest_at (H : Xofs) (s : Level) (D) (w : Fin s.params.k → Fin 256 → ℤ)
    {μ : List Bool} (hμ : μ.length = 512) :
    (H.withDigestRegister s D).commitmentDigest s w μ =
      (digestBytesAt s (D (BitString.ofList _ (commitmentInput s w μ)))).toList := by
  apply Keccak.bytesToBitsLE_injective
  rw [H.commitmentDigest_withDigestRegister s D w hμ, ← Keccak.ofFn_fixedBytesEquivBitsLE]
  simp [digestBytesAt]

private def attemptQuery (H : Xofs) (s : Level) (sk : PrivateKey s) (A : PublicMatrix s)
    (μ : List Bool) (y : Fin s.params.ℓ → Poly) : DigestReads s (Option (Option (List Byte))) := do
  let prep := AttemptCommitment.ofMask s A y
  let point := commitmentInput s (highBitsVec s.params prep.product) μ
  let v ← OracleComp.query (BitString.ofList _ point)
  let d := (digestBytesAt s v).toList
  return terminalReply (finishSigningAttempt s sk prep.mask prep.product d (H.sampleInBall s d))

-- Preserve the distinction between running out of attempts and a terminal challenge failure
-- when a caller pauses the signer partway through its retry loop.
private def terminalDigestQueries (H : Xofs) (s : Level) (sk : PrivateKey s) (A : PublicMatrix s)
    (μ : List.Vector Bool 512) (mask : ℕ → Vector (Vector (ZMod 8380417) 256) s.params.ℓ)
    (fuel nonce : ℕ) : DigestReads s (Option (Option (List Byte))) :=
  (List.finRange fuel).findSomeM? fun i =>
    attemptQuery H s sk A μ.toList (ringVectorCoeffs (mask (nonce + i.val * s.params.ℓ)))

private theorem terminalDigestQueries_bounded (H : Xofs) (s : Level)
    (sk A μ mask) (fuel nonce : ℕ) :
    (terminalDigestQueries H s sk A μ mask fuel nonce).IsQueryBounded fuel := by
  simpa only [terminalDigestQueries, List.length_finRange, Nat.mul_one] using
    (OracleComp.IsCostBounded.findSomeM? (cost := fun _ => 1) (n := 1)
      (xs := List.finRange fuel) (f := fun i => attemptQuery H s sk A μ.toList
        (ringVectorCoeffs (mask (nonce + i.val * s.params.ℓ))))
      (fun _ _ => .liftBind _ _ 0 fun _ => .pure _ _))

/-- Run the remaining FIPS signing attempts with a supplied mask schedule. Each retry consults
the table on the literal commitment input. The other SHAKE reads use the background streams. -/
def Xofs.retryDigestQueries (H : Xofs) (s : Level) (sk : PrivateKey s) (A : PublicMatrix s)
    (μ : List.Vector Bool 512) (mask : ℕ → Vector (Vector (ZMod 8380417) 256) s.params.ℓ)
    (fuel nonce : ℕ) :
    DigestReads s (Option (List Byte)) :=
  Option.join <$> terminalDigestQueries H s sk A μ mask fuel nonce

/-- The retry program makes at most one digest lookup per available attempt. -/
theorem Xofs.retryDigestQueries_bounded (H : Xofs) (s : Level) (sk A μ mask) (fuel nonce : ℕ) :
    (H.retryDigestQueries s sk A μ mask fuel nonce).IsQueryBounded fuel := by
  rw [Xofs.retryDigestQueries, ← bind_pure_comp]
  exact OracleComp.IsCostBounded.bind (n := fuel) (m := 0)
    (terminalDigestQueries_bounded ..) (fun _ => .pure _ _)

private theorem eval_attemptQuery (H : Xofs) (s : Level) (D) (sk A) (m : List Bool)
    (len : m.length = 512) (y) :
    OracleComp.evalPure D (attemptQuery H s sk A m y) =
      terminalReply ((H.withDigestRegister s D).attemptWithMask s sk A m y) := by
  simp only [attemptQuery, OracleComp.evalPure_bind, OracleComp.evalPure_query,
    OracleComp.evalPure_pure, Xofs.attemptWithMask, digest_at H s D _ len, challenge_off]

private theorem eval_terminalDigestQueries (H : Xofs) (s : Level) (D) (sk A)
    (μ : List.Vector Bool 512) (mask) (fuel nonce : ℕ) :
    OracleComp.evalPure D (terminalDigestQueries H s sk A μ mask fuel nonce) =
      (List.finRange fuel).findSome? fun i => terminalReply
        ((H.withDigestRegister s D).attemptWithMask s sk A μ.toList
          (ringVectorCoeffs (mask (nonce + i.val * s.params.ℓ)))) := by
  rw [terminalDigestQueries, OracleComp.evalPure_findSomeM?]
  simp only [eval_attemptQuery H s D sk A μ.toList μ.toList_length]

private theorem eval_retries (H : Xofs) (s : Level) (D) (sk A) (μ : List.Vector Bool 512)
    (mask) (fuel nonce : ℕ) :
    OracleComp.evalPure D (H.retryDigestQueries s sk A μ mask fuel nonce) =
      firstAccepted s.params.ℓ (fun n => (H.withDigestRegister s D).attemptWithMask s sk A μ.toList
        (ringVectorCoeffs (mask n))) fuel nonce := by
  rw [Xofs.retryDigestQueries, OracleComp.evalPure_map, eval_terminalDigestQueries,
    firstAccepted_eq_terminal, Fin.findSome?_eq_findSome?_finRange]

/-- The full 814-attempt native signer with any fixed mask schedule computes exactly the
table program's reply. Sparse-challenge exhaustion and reaching the retry cap both return error. -/
theorem Xofs.evalPure_retryDigestQueries (H : Xofs) (s : Level) (D) (sk A)
    (μ : List.Vector Bool 512) (mask) :
    OracleComp.evalPure D (H.retryDigestQueries s sk A μ mask 814 0) =
      (H.withDigestRegister s D).signingRetries s sk A μ.toList mask :=
  eval_retries H s D sk A μ mask 814 0

private def representativeQuery (H : Xofs) (s : Level) (tr : List Byte) (fmt : List Bool) :
    DigestReads s (List.Vector Bool 512) :=
  let x := representativeInput tr fmt
  if x.length = s.commitmentInputBits then do
    let v ← OracleComp.query (BitString.ofList _ x)
    return ⟨Keccak.bytesToBitsLE (H.h256.readWithPrefix x 64 (digestBytesAt s v).toList), by
      simp only [Keccak.length_bytesToBitsLE, ExtendableOutput.readWithPrefix, List.length_append,
        List.length_take, List.length_drop, H.h256.length_read]
      lia⟩
  else pure ⟨H.representativeFromTr tr fmt, by
    simp [Xofs.representativeFromTr, Keccak.length_bytesToBitsLE, H.h256.length_read]⟩

private theorem eval_rep (H : Xofs) (s : Level) (D) (tr fmt) :
    (OracleComp.evalPure D (representativeQuery H s tr fmt)).toList =
      (H.withDigestRegister s D).representativeFromTr tr fmt := by
  by_cases hx : (representativeInput tr fmt).length = s.commitmentInputBits <;>
    simp only [representativeQuery, Xofs.representativeFromTr, Xofs.withDigestRegister,
      ExtendableOutput.withPrefixes, hx, ↓reduceIte, digestBytesAt] <;> rfl

/-- A signing request on the digest register. Prepare the mask seed or row once from the decoded
key and message representative, then expand the mask at each retry counter. The representative
query keeps the SHAKE256 suffix beyond the digest prefix when its input has commitment length. -/
def Xofs.signDigestQueriesWithMask {α : Type} (H : Xofs) (s : Level) (key : List Byte)
    (q : SigningQuery) (prepare : PrivateKey s → List Bool → α)
    (expand : α → ℕ → Vector (Vector (ZMod 8380417) 256) s.params.ℓ) :
    DigestReads s (Option (List Byte)) :=
  if q.context.length ≤ 255 then
    match decodePrivate s key with
    | none => pure none
    | some sk =>
      match H.expandA s sk.rho with
      | none => pure none
      | some A => do
        let μ ← representativeQuery H s sk.tr (formatMessage q.message q.context)
        let source := prepare sk μ.toList
        H.retryDigestQueries s sk A μ (expand source) 814 0
  else pure none

/-- A full hedged FIPS signing request with its mask seed derived from the key, hedge, and
representative and its per-counter masks generated by Algorithm 34. -/
def Xofs.signDigestQueries (H : Xofs) (s : Level) (key : List Byte) (q : SigningQuery)
    (rnd : FixedBytes 32) : DigestReads s (Option (List Byte)) :=
  H.signDigestQueriesWithMask s key q
    (fun sk μ => H.h256.read (maskSeedInput sk.key rnd μ) 64) (H.expandMask s)

private theorem rep_bounded (H : Xofs) (s : Level) (tr fmt) :
    (representativeQuery H s tr fmt).IsQueryBounded 1 := by
  by_cases hx : (representativeInput tr fmt).length = s.commitmentInputBits <;>
    simp only [representativeQuery, hx, ↓reduceIte]
  · exact .liftBind _ _ 0 fun _ => .pure _ _
  · exact .pure _ _

/-- One representative query and the 814-trial cap bound every mask schedule, including
the schedule derived from a native hedge and a schedule decoded from a supplied expansion row. -/
theorem Xofs.signDigestQueriesWithMask_bounded {α : Type} (H : Xofs) (s : Level) (key q)
    (prepare : PrivateKey s → List Bool → α) (expand) :
    (H.signDigestQueriesWithMask s key q prepare expand).IsQueryBounded 815 := by
  unfold Xofs.signDigestQueriesWithMask
  split
  · split
    · exact .pure _ _
    · split
      · exact .pure _ _
      · apply OracleComp.IsCostBounded.bind (n := 1) (m := 814)
        · apply rep_bounded
        · intro μ
          apply Xofs.retryDigestQueries_bounded
  · exact .pure _ _

/-- A native hedge selects one mask schedule and hence has the same 815-query bound. -/
theorem Xofs.signDigestQueries_bounded (H : Xofs) (s : Level) (key q rnd) :
    (H.signDigestQueries s key q rnd).IsQueryBounded 815 :=
  H.signDigestQueriesWithMask_bounded s key q _ _

/-- The register interpreter runs the FIPS signing retries on the installed streams with the
chosen mask schedule. It returns an error for an overlong context, invalid key, or failed
matrix expansion before entering those retries. -/
theorem Xofs.evalPure_signDigestQueriesWithMask {α : Type} (H : Xofs) (s : Level) (D) (key q)
    (prepare : PrivateKey s → List Bool → α) (expand) :
    OracleComp.evalPure D (H.signDigestQueriesWithMask s key q prepare expand) = (do
      guard (q.context.length ≤ 255)
      let sk ← decodePrivate s key
      let G := H.withDigestRegister s D
      let A ← G.expandA s sk.rho
      let μ := G.representativeFromTr sk.tr (formatMessage q.message q.context)
      G.signingRetries s sk A μ (expand (prepare sk μ))) := by
  by_cases hc : q.context.length ≤ 255
  · simp only [Xofs.signDigestQueriesWithMask, hc, guard, ↓reduceIte, Option.pure_def,
      Option.bind_eq_bind, Option.bind_some,
      Xofs.expandA_congr (K := H.withDigestRegister s D) (H := H) rfl s]
    cases decodePrivate s key with
    | none => rfl
    | some sk =>
      simp only [Option.bind_some]
      cases H.expandA s sk.rho with
      | none => rfl
      | some A =>
        simp only [Option.bind_some, OracleComp.evalPure_bind, Xofs.evalPure_retryDigestQueries,
          eval_rep]
  · simp [Xofs.signDigestQueriesWithMask, hc, guard]

private theorem mask_off (H : Xofs) (s : Level) (D) (seed : List Byte) (hn : seed.length = 64) :
    (H.withDigestRegister s D).expandMask s seed = H.expandMask s seed := by
  funext κ
  unfold Xofs.expandMask
  congr 1
  funext nonce
  apply read_off
  rw [Keccak.length_bytesToBitsLE]
  simp only [nonceInput, List.length_append, hn, List.length_cons, List.length_nil]
  cases s <;> decide

/-- Evaluating the bounded program under the installed register returns the actual FIPS
signature bytes or error, for any signing request and each fixed hedge. -/
theorem Xofs.evalPure_signDigestQueries (H : Xofs) (s : Level) (D) (key : List Byte)
    (q : SigningQuery) (rnd : FixedBytes 32) :
    OracleComp.evalPure D (H.signDigestQueries s key q rnd) =
      (H.withDigestRegister s D).sign s key q.message q.context rnd := by
  let G := H.withDigestRegister s D
  simp only [Xofs.signDigestQueries, Xofs.evalPure_signDigestQueriesWithMask, Xofs.sign,
    Xofs.signInternal, Xofs.runSigning, Xofs.startSigning, Xofs.startSigningWithSeed,
    bind_assoc, pure_bind]
  apply Option.bind_congr
  intro _ _
  apply Option.bind_congr
  intro sk hd
  apply Option.bind_congr
  intro A _
  let μ := G.representativeFromTr sk.tr (formatMessage q.message q.context)
  have len : μ.length = 512 := by
    simp [μ, Xofs.representativeFromTr, Keccak.length_bytesToBitsLE, G.h256.length_read]
  have keyLen := (lengths_of_decodePrivate hd).2.1
  have seed := read_off H s D (maskSeedInput sk.key rnd μ) 64 (by
    rw [length_maskSeedInput, len]
    have lower : 1024 < s.commitmentInputBits := by cases s <;> decide
    lia)
  change G.signingRetries s sk A μ (H.expandMask s _) = G.signingRetries s sk A μ _
  rw [seed, mask_off H s D _ (H.h256.length_read ..)]

/-- The native signing service samples one hedge, executes the bounded register program,
and appends exactly the successful replies to the strong-forgery log. -/
theorem Xofs.signingOracle_eq_digestQueries (H : Xofs) (s : Level) (D) (key : List Byte)
    (q : SigningQuery) (log : List Forgery) :
    (H.withDigestRegister s D).signingOracle s key q log =
      (PMF.uniformOfFintype (FixedBytes 32)).map fun rnd =>
        let reply := OracleComp.evalPure D (H.signDigestQueries s key q rnd)
        (reply, q.logReply reply log) := by
  simp only [Xofs.evalPure_signDigestQueries]
  rfl

/-- Run the full FIPS verifier on the digest register. Only the representative and the
recomputed commitment can consult an installed row. Invalid encodings reject and exhausted
matrix or sparse-challenge expansions return the FIPS error. -/
def Xofs.verifyDigestQueries (H : Xofs) (s : Level) (pk : List Byte) (f : Forgery) :
    DigestReads s (Option Bool) :=
  if f.context.length > 255 then pure none else
  if pk.length != 32 + 320 * s.params.k then pure (some false) else
  match sigDecode s f.signature with
  | none => pure (some false)
  | some σ =>
    match H.expandA s (pk.take 32), H.sampleInBall s σ.digest with
    | some A, some c => do
      let μ ← representativeQuery H s (H.h256.readBytes pk 64) (formatMessage f.message f.context)
      let pair := publicKey s pk A
      let x := commitmentInput s (hintedCommitment s pair σ c) μ.toList
      let v ← OracleComp.query (BitString.ofList _ x)
      return some (σ.acceptDigest fun _ => (digestBytesAt s v).toList)
    | _, _ => pure none

/-- Two classical digest-table queries suffice to evaluate a candidate forgery, including
a representative input that itself has the commitment length. -/
theorem Xofs.verifyDigestQueries_bounded (H : Xofs) (s : Level) (pk f) :
    (H.verifyDigestQueries s pk f).IsQueryBounded 2 := by
  unfold Xofs.verifyDigestQueries
  split
  · exact .pure _ _
  split
  · exact .pure _ _
  split
  · exact .pure _ _
  split
  · apply (rep_bounded ..).bind (m := 1)
    exact fun _ => .liftBind _ _ 0 fun _ => .pure _ _
  · exact .pure _ _

/-- The two-read verifier preserves all three possible FIPS results at the installed raw XOFs. -/
theorem Xofs.evalPure_verifyDigestQueries (H : Xofs) (s : Level) (D) (pk : List Byte)
    (f : Forgery) :
    OracleComp.evalPure D (H.verifyDigestQueries s pk f) =
      (H.withDigestRegister s D).verify s pk f.message f.context f.signature := by
  let G := H.withDigestRegister s D
  by_cases hc : f.context.length ≤ 255
  · simp only [Xofs.verifyDigestQueries, not_lt_of_ge hc, ↓reduceIte, Xofs.verify,
      Xofs.verifyWithExpansion, guard, hc, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      Xofs.verifyInternalWith]
    by_cases hk : pk.length = 32 + 320 * s.params.k
    · simp only [hk, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      cases hd : sigDecode s f.signature with
      | none => rfl
      | some σ =>
        have len : σ.digest.length ≤ digestBytes s := by rw [← digest_of_sigDecode hd]; simp
        have small : digestBytes s ≤ 64 := by cases s <;> decide
        have big : 512 < s.commitmentInputBits := by cases s <;> decide
        have ch : G.sampleInBall s σ.digest = H.sampleInBall s σ.digest := by
          unfold Xofs.sampleInBall ExtendableOutput.readBytes
          rw [read_off H s D _ _ (by rw [Keccak.length_bytesToBitsLE]; lia)]
        have hash : G.h256.readBytes pk 64 = H.h256.readBytes pk 64 := by
          apply read_off
          rw [Keccak.length_bytesToBitsLE, hk]
          cases s <;> decide
        have mat := Xofs.expandA_congr (K := H.withDigestRegister s D) (H := H) rfl s (pk.take 32)
        dsimp only [G] at ch hash
        simp only [mat, ch]
        cases ha : H.expandA s (pk.take 32) with
        | none => rfl
        | some A =>
          cases hch : H.sampleInBall s σ.digest with
          | none => rfl
          | some c =>
            simp only [OracleComp.evalPure_bind, OracleComp.evalPure_query,
              OracleComp.evalPure_pure, eval_rep, Xofs.messageRepresentative, hash,
              Option.bind_some]
            let μ := (H.withDigestRegister s D).representativeFromTr (H.h256.readBytes pk 64)
              (formatMessage f.message f.context)
            have hμ : μ.length = 512 := by
              rw [show μ = Keccak.bytesToBitsLE ((H.withDigestRegister s D).h256.read
                (representativeInput (H.h256.readBytes pk 64) (formatMessage f.message f.context))
                64) from rfl, Keccak.length_bytesToBitsLE, ExtendableOutput.length_read]
            let w := hintedCommitment s (publicKey s pk A) σ c
            exact congrArg (fun bytes => some (σ.acceptDigest fun _ => bytes))
              (digest_at H s D w hμ).symm
    · simp [hk, bne_iff_ne]
  · simp [Xofs.verifyDigestQueries, Xofs.verify, Xofs.verifyWithExpansion, hc, guard,
      Nat.lt_of_not_ge hc]

open scoped ENNReal

/-- Raw SHAKE256 address chosen by an ML-DSA mask after the representative has been fixed. -/
def maskCommitmentAddress (s : Level) (A : PublicMatrix s) (m : BitString 512)
    (y : Fin s.params.ℓ → Poly) : BitString s.commitmentInputBits :=
  BitString.ofList _ (commitmentInput s (highBitsVec s.params (moduleSISMap A y)) (List.ofFn m))

/-- Packing the real mask commitment into SHAKE input bits preserves the largest-atom
bound for its rounded product. This holds for every fixed coefficient matrix. -/
theorem maskCommitmentAddress_mass_le (s : Level) (A : PublicMatrix s) (m : BitString 512)
    (i : BitString s.commitmentInputBits) :
    ((signingMaskLaw s.params (by cases s <;> decide)).map (maskCommitmentAddress s A m)) i ≤
      commitmentGuessProbability s.params (by cases s <;> decide) A := by
  classical
  let mask := signingMaskLaw s.params (by cases s <;> decide)
  let w := fun y : Fin s.params.ℓ → Poly => highBitsVec s.params (moduleSISMap A y)
  let addr := maskCommitmentAddress s A m
  change mask.map addr i ≤ _
  by_cases hi : i ∈ (mask.map addr).support
  · obtain ⟨y, _, rfl⟩ := (PMF.mem_support_map_iff ..).mp hi
    refine le_trans ?_ (le_iSup (fun v => mask.map w v) (w y))
    rw [← PMF.toOuterMeasure_apply_singleton, ← PMF.toOuterMeasure_apply_singleton,
      PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
    apply mask.toOuterMeasure.mono
    intro z hz
    have eq : addr z = addr y := hz
    have bits := congrArg List.ofFn eq
    simp only [addr, maskCommitmentAddress, BitString.ofFn_ofList
      (commitmentInput_length s _ List.length_ofFn)] at bits
    have range (v : Fin s.params.ℓ → Poly) (j k) : 0 ≤ w v j k ∧
        w v j k < (((s.params.q - 1) / (2 * s.params.γ₂) : ℕ) : ℤ) :=
      ⟨highBits_nonneg (by cases s <;> decide) _,
        highBits_lt (by cases s <;> decide) (by cases s <;> decide) (by cases s <;> decide) _⟩
    exact eq_of_commitmentInput_eq (range z) (range y) bits
  · simp [(PMF.apply_eq_zero_iff ..).mpr hi]

private theorem maskCommitmentAddress_singleton_le (s : Level) (A : PublicMatrix s)
    (m : BitString 512) (i : BitString s.commitmentInputBits) :
    (signingMaskLaw s.params (by cases s <;> decide)).toOuterMeasure
      {y | maskCommitmentAddress s A m y = i} ≤
        commitmentGuessProbability s.params (by cases s <;> decide) A := by
  change _root_.PMF.toOuterMeasure _ (maskCommitmentAddress s A m ⁻¹' {i}) ≤ _
  rw [← PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton]
  exact maskCommitmentAddress_mass_le s A m i

-- Only a raw address in the original execution trace can expose a change confined to one
-- block. Single-cell writes use identity blocks. Refreshing a packed commitment drops the
-- representative prefix before comparing block addresses.
private theorem prob_mask_trace_changes {R V : Type} (s : Level) (A : PublicMatrix s)
    (m : BitString 512) (D) (run : DigestReads s R) {K : ℕ} (bound : run.IsQueryBounded K)
    (block : BitString s.commitmentInputBits → BitString s.commitmentInputBits)
    (changed : (Fin s.params.ℓ → Poly) → V →
      BitString s.commitmentInputBits → BitString (8 * digestBytes s))
    (off : ∀ y v i, block i ≠ maskCommitmentAddress s A m y → changed y v i = D i) :
    (signingMaskLaw s.params (by cases s <;> decide)).toOuterMeasure
      {y | ∃ v, OracleComp.evalPure (changed y v) run ≠ OracleComp.evalPure D run} ≤
      K * commitmentGuessProbability s.params (by cases s <;> decide) A := by
  classical
  let μ := signingMaskLaw s.params (by cases s <;> decide)
  let addr := maskCommitmentAddress s A m
  let reads := (OracleComp.queriesWith D run).map block
  refine (μ.toOuterMeasure.mono (s₂ := {y | addr y ∈ reads}) ?_).trans
    ((PMF.toOuterMeasure_mem_list_le μ addr
      (δ := commitmentGuessProbability s.params (by cases s <;> decide) A)
      (maskCommitmentAddress_singleton_le s A m) reads).trans ?_)
  · rintro y ⟨v, different⟩
    by_contra miss
    apply different
    apply (OracleComp.interpret_id_congr D (changed y v) run ?_).1
    intro i hi
    apply off y v i
    intro eq
    exact miss (show maskCommitmentAddress s A m y ∈ reads from
      eq ▸ List.mem_map_of_mem (f := block) hi)
  · simp only [reads, List.length_map]
    gcongr
    exact_mod_cast bound.length_queriesWith_le D

private theorem prob_response_changes {R : Type} (s : Level) (A : PublicMatrix s)
    (m : BitString 512) (D) (run : DigestReads s R) {K : ℕ} (bound : run.IsQueryBounded K) :
    (signingMaskLaw s.params (by cases s <;> decide)).toOuterMeasure
      {y | ∃ v, OracleComp.evalPure (Function.update D (maskCommitmentAddress s A m y) v) run ≠
        OracleComp.evalPure D run} ≤
      K * commitmentGuessProbability s.params (by cases s <;> decide) A := by
  exact prob_mask_trace_changes s A m D run bound id
    (fun y v => Function.update D (maskCommitmentAddress s A m y) v)
    (fun _ _ _ ne => Function.update_of_ne ne ..)

/-- Changing the entry at a fresh mask commitment can affect one whole native signing
reply with probability at most 815 times the largest rounded-commitment atom. The digest
written there may depend on the mask. The message being signed may use a different
representative from the one used to draw the changed address. -/
theorem Xofs.prob_sign_changes_at_maskCommitment_le (H : Xofs) (s : Level)
    (A : PublicMatrix s) (m : BitString 512) (D) (key : List Byte) (q : SigningQuery)
    (rnd : FixedBytes 32) :
    let sign := fun T => (H.withDigestRegister s T).sign s key q.message q.context rnd
    (signingMaskLaw s.params (by cases s <;> decide)).toOuterMeasure
      {y | ∃ v, sign (Function.update D (maskCommitmentAddress s A m y) v) ≠ sign D} ≤
      815 * commitmentGuessProbability s.params (by cases s <;> decide) A := by
  simpa only [Xofs.evalPure_signDigestQueries, Nat.cast_ofNat] using
    prob_response_changes s A m D _ (H.signDigestQueries_bounded s key q rnd)

/-- A fresh mask commitment can change a completed candidate's verification result with
probability at most twice the largest rounded-commitment atom. This includes errors and
the raw representative lookup used for adaptive messages. -/
theorem Xofs.prob_verify_changes_at_maskCommitment_le (H : Xofs) (s : Level)
    (A : PublicMatrix s) (m : BitString 512) (D) (pk : List Byte) (f : Forgery) :
    let verify := fun T => (H.withDigestRegister s T).verify s pk f.message f.context f.signature
    (signingMaskLaw s.params (by cases s <;> decide)).toOuterMeasure
      {y | ∃ v, verify (Function.update D (maskCommitmentAddress s A m y) v) ≠ verify D} ≤
      2 * commitmentGuessProbability s.params (by cases s <;> decide) A := by
  simpa only [Xofs.evalPure_verifyDigestQueries, Nat.cast_ofNat] using
    prob_response_changes s A m D _ (H.verifyDigestQueries_bounded s pk f)

end Cslib.Crypto.MLDSA.FIPS204
