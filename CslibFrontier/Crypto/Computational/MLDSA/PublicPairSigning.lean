/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning
public import CslibFrontier.Crypto.Computational.MLDSA.SigningSimulation
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204Signing
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204
import all CslibFrontier.Crypto.Computational.MLDSA.Basic
import all CslibFrontier.Crypto.Primitives.ByteString
import all CslibFrontier.Crypto.Computational.MLDSA.SignedMatrix
import CslibFrontier.Probability.PMF.Bind

/-!
# Public-pair signing after refreshing masks and commitment digests

[Barbosa et al.][BarbosaEtAl2023], Figure 7, construct an accepting-transcript simulator
from the full pair `(A,t)`. Here the forger receives the rounded FIPS public-key bytes and
retains its quantum register across queries and classical signing requests. In the compared
hybrid every attempt draws an independent ideal mask and digest. A norm or hint rejection
leaves the raw table unchanged. A signature or Algorithm 29 exhaustion writes the new digest
at the full commitment input. This implementation chooses the minimum limits permitted by
[NISTFIPS204], Appendix C, Table 3, of 814 signing attempts and 221 challenge-expansion bytes.

The exact comparison below starts after those replacements. Bounding the cost of refreshing
actual seeded masks and digests in the device's prior quantum state is a separate game hop.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability Cslib.Quantum

/-- Replace the specified commitment's SHAKE256 prefix, preserving the suffix, the other
SHAKE256 input rows and the SHAKE128 stream. -/
@[expose] def Xofs.writeCommitment (H : Xofs) (input : List Bool) (value : List Byte) : Xofs :=
  { H with h256 := H.h256.withPrefixes fun x => if x = input then some value else none }

/-- A write at a commitment input leaves the complete bounded expansion of every digest unchanged.
The FIPS input lengths separate these roles at all three parameter sets. -/
theorem Xofs.sampleInBall_writeCommitment (s : Level) (H : Xofs)
    (μ : List Bool) (hμ : μ.length = 512) (w : Fin s.params.k → Fin 256 → ℤ) (value : List Byte)
    (d : FixedBytes (digestBytes s)) :
    (H.writeCommitment (commitmentInput s w μ) value).sampleInBall s d.toList =
      H.sampleInBall s d.toList := by
  have sep := (commitmentInput_ne_digestInput w hμ (FixedBytes.length_toList d)).symm
  have row : (H.writeCommitment (commitmentInput s w μ) value).h256.readBytes d.toList 221 =
      H.h256.readBytes d.toList 221 := by
    simp [Xofs.writeCommitment, ExtendableOutput.withPrefixes, ExtendableOutput.readBytes, sep]
  unfold Xofs.sampleInBall
  rw [row]

/-- One raw commitment write retained when a signing attempt terminates its request. -/
structure TerminalSigningWrite (s : Level) where
  /-- The measured request that caused the write. -/
  request : SigningQuery
  /-- High-order commitment coefficients of this attempt. -/
  point : Fin s.params.k → Fin 256 → ℤ
  /-- Actual untagged SHAKE256 commitment input. -/
  address : List Bool
  /-- Digest installed at this address. -/
  digest : FixedBytes (digestBytes s)
  /-- A signature, or the public error following expansion exhaustion. -/
  reply : Option (List Byte)

/-- Chronological signing writes starting at `base`. Each address contains the message
representative read from the *current* table using the public-key hash stored at setup. -/
inductive TerminalSigningWrite.History (s : Level) (base : Xofs) (tr : List Byte) :
    List (TerminalSigningWrite s) → Xofs → Prop where
  /-- No prefix has been changed. -/
  | initial : History s base tr [] base
  /-- Append the measured request's terminal write and use the resulting table thereafter. -/
  | append {past G} (previous : History s base tr past G) (q : SigningQuery)
      (w : Fin s.params.k → Fin 256 → ℤ) (d : FixedBytes (digestBytes s))
      (r : Option (List Byte)) (x : List Bool)
      (address : x = commitmentInput s w (G.representativeFromTr tr
        (formatMessage q.message q.context))) :
      History s base tr (past ++ [⟨q, w, x, d, r⟩]) (G.writeCommitment x d.toList)

/-- A terminal commitment write preserves the entire public-key hash stream. -/
private theorem keyRead (s : Level) (G : Xofs) (rho : FixedBytes 32)
    (t : Fin s.params.k → Poly) (tr : List Byte) (m : List Bool)
    (w : Fin s.params.k → Fin 256 → ℤ) (v : List Byte) (n : ℕ) :
    (Xofs.writeCommitment G (commitmentInput s w (G.representativeFromTr tr m)) v).h256.readBytes
        (encodePublic s rho.toList t) n = G.h256.readBytes (encodePublic s rho.toList t) n := by
  have sep : Keccak.bytesToBitsLE (encodePublic s rho.toList t) ≠
      commitmentInput s w (G.representativeFromTr tr m) := by
    intro e
    have len := congrArg List.length e
    simp only [commitmentInput, Xofs.representativeFromTr, List.length_append, encodePublic,
      Keccak.length_bytesToBitsLE, G.h256.length_read] at len
    rw [FixedBytes.length_toList, length_packCoeffs, length_packCoeffs] at len
    cases s <;> contradiction
  simp [Xofs.writeCommitment, ExtendableOutput.readBytes, ExtendableOutput.withPrefixes, sep]

/-- If the request has no 64-byte match, its write cannot affect any representative read. -/
private theorem repRead (s : Level) (G : Xofs) (tr : List Byte) (ht : tr.length = 64)
    (m : List Bool) (w : Fin s.params.k → Fin 256 → ℤ) (v : List Byte)
    (miss : G.h256.read (representativeInput tr m) 64 ≠ tr) (other : List Bool) (n : ℕ) :
    (Xofs.writeCommitment G (commitmentInput s w (G.representativeFromTr tr m)) v).h256.read
      (representativeInput tr other) n = G.h256.read (representativeInput tr other) n := by
  have sep : representativeInput tr other ≠ commitmentInput s w (G.representativeFromTr tr m) := by
    intro overlap
    have hl : (Keccak.bytesToBitsLE tr).length = (G.representativeFromTr tr m).length := by
      simp only [Xofs.representativeFromTr, Keccak.length_bytesToBitsLE, ht, G.h256.length_read]
    exact miss (Keccak.bytesToBitsLE_injective (List.append_inj overlap hl).1.symm)
  simp [Xofs.writeCommitment, ExtendableOutput.withPrefixes, sep]


/-- Every terminal commitment update leaves the encoded FIPS public key's raw SHAKE256
stream unchanged. This includes fatal signing requests. -/
theorem TerminalSigningWrite.History.read_publicKey {s : Level} {base G : Xofs} {tr : List Byte}
    {writes : List (TerminalSigningWrite s)} (history : History s base tr writes G)
    (rho : FixedBytes 32) (t : Fin s.params.k → Poly) (n : ℕ) :
    G.h256.readBytes (encodePublic s rho.toList t) n =
      base.h256.readBytes (encodePublic s rho.toList t) n := by
  induction history with
  | initial => rfl
  | @append past G prev q w d r x address ih =>
    subst x
    exact (keyRead s G rho t tr (formatMessage q.message q.context) w d.toList n).trans ih

/-- If the ambient oracle has no representative equal to the stored public-key hash on a
terminal signing request, every representative read, including final verification, sees the
ambient stream. Requests may have been chosen after earlier writes and coherent queries. -/
theorem TerminalSigningWrite.History.read_representative {s : Level} {base G : Xofs}
    {tr : List Byte} {writes : List (TerminalSigningWrite s)}
    (history : History s base tr writes G) (ht : tr.length = 64)
    (miss : ∀ w ∈ writes, base.h256.read (representativeInput tr
      (formatMessage w.request.message w.request.context)) 64 ≠ tr)
    (formatted : List Bool) (n : ℕ) :
    G.h256.read (representativeInput tr formatted) n =
      base.h256.read (representativeInput tr formatted) n := by
  induction history generalizing formatted n with
  | initial => rfl
  | @append past G prev q w d r x address ih =>
    have last := miss ⟨q, w, x, d, r⟩ (List.mem_append_right past List.mem_cons_self)
    subst x
    have prior := ih (fun z hz => miss z (List.mem_append_left _ hz))
    have current : G.h256.read (representativeInput tr
        (formatMessage q.message q.context)) 64 ≠ tr := by
      rw [prior]
      exact last
    exact (repRead s G tr ht (formatMessage q.message q.context) w d.toList current
      formatted n).trans (prior _ _)

/-- A signing experiment at the original FIPS seeded law of `(ρ,A,t)`. A setup error
returns false. The continuation receives the matrix and full vector before public-key rounding. -/
noncomputable def Xofs.fullPairExperiment (H : Xofs) (s : Level)
    (run : FixedBytes 32 → MLDSA.PublicKey s.params → Game) : Game :=
  H.keyExperiment s fun keys =>
    ((do
      let sk ← decodePrivate s keys.secretKey
      let A ← H.expandA s sk.rho
      let pair : MLDSA.SecretKey s.params := ⟨A, sk.s₁, sk.s₂⟩
      return run (fun j => sk.rho[j.val]!) pair.publicKey) : Option Game).getD (pure false)

/-- Draw the FIPS seed and form the unrounded pair directly from the two expansions of Algorithm
6. This is the same experiment as generating and decoding the private and public key bytes. -/
theorem Xofs.fullPairExperiment_eq_expand (H : Xofs) (s : Level)
    (run : FixedBytes 32 → MLDSA.PublicKey s.params → Game) :
    H.fullPairExperiment s run = (PMF.uniformOfFintype (FixedBytes 32)).bind fun seed =>
      let ex := H.expandKeySeed s seed
      let rho := ex.take 32
      ((do
        let A ← H.expandA s rho
        let (x, e) ← H.expandS s ((ex.drop 32).take 64)
        return run (fun i => rho[i.val]!) ⟨A, ModuleLWE.sample A x e⟩) : Option Game).getD
          (PMF.pure false) := by
  unfold Xofs.fullPairExperiment Xofs.keyExperiment
  apply congrArg (PMF.bind (PMF.uniformOfFintype (FixedBytes 32)) ·)
  funext seed
  cases kg : H.keyGen s seed with
  | none =>
    unfold Xofs.keyGen at kg
    cases ha : H.expandA s ((H.expandKeySeed s seed).take 32) <;>
      cases hs : H.expandS s (((H.expandKeySeed s seed).drop 32).take 64) <;>
      simp_all
  | some keys =>
    obtain ⟨rho, sk, mat, pk, hd, _, _, exp⟩ := privateKey_of_keyGen kg
    have seedEq : (H.expandKeySeed s seed).take 32 = rho.toList := by
      rw [← publicSeed_of_keyGen kg, pk, take_encodePublic]
    simp only [hd, seedEq, mat, exp, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.getD_some]
    rfl

namespace QuantumSigningForger

/-- The final shared XOFs, public bytes, forgery and successful signing log, together with
writes on fatal expansions and the complete residual quantum device. -/
structure ProgrammedSigningResult (C : QuantumSigningForger) (s : Level) (base : Xofs) where
  /-- Public outcome checked by the FIPS fresh-digest forgery predicate. -/
  trial : SignedMatrixTrial s
  /-- Public-key hash held constant during signing. -/
  tr : List Byte
  /-- Chronological terminal writes, including expansion failures. -/
  writes : List (TerminalSigningWrite s)
  /-- Every recorded address is the actual input at that point in the execution. -/
  history : TerminalSigningWrite.History s base tr writes trial.xofs
  /-- Every fatal digest still exhausts Algorithm 29 on the final shared table. -/
  stillExhausted : ∀ w ∈ writes, w.reply = none → trial.xofs.sampleInBall s w.digest.toList = none
  /-- Successful writes have the installed digest prefix in the real signing log. -/
  signed : ∀ w ∈ writes, ∀ sig, w.reply = some sig →
    sig.take (digestBytes s) = w.digest.toList ∧
      ⟨w.request.context, w.request.message, sig⟩ ∈ trial.log
  /-- Device after all coherent queries, measurements and signing calls. -/
  device : DeviceState (C.addressBits + 2 + 8 * C.responseBytes + C.workQubits) Unit Unit

/-- An accepted forgery's digest differs from every terminal write on which a previous call
returned the expansion error, even if other signing calls changed the table in between. -/
theorem ProgrammedSigningResult.ne_failed_digest {C : QuantumSigningForger} {s : Level}
    {base : Xofs}
    (result : ProgrammedSigningResult C s base) {w : TerminalSigningWrite s}
    (hw : w ∈ result.writes) (failed : w.reply = none)
    (hv : result.trial.xofs.verify s result.trial.publicKey result.trial.forgery.message
      result.trial.forgery.context result.trial.forgery.signature = some true) :
    result.trial.forgery.signature.take (digestBytes s) ≠ w.digest.toList := by
  obtain ⟨_, σ, c, _, hd, hc, _⟩ := parsed_of_verifyWithExpansion (f := result.trial.forgery) hv
  intro same
  rw [← digest_of_sigDecode hd, same, result.stillExhausted w hw failed] at hc
  contradiction

/-- A winning fresh digest differs from every digest installed by the simulator. Successful
writes appear in the signed log; fatal writes remain failed Algorithm 29 inputs. -/
theorem ProgrammedSigningResult.ne_written_digest_of_newDigestWin {C : QuantumSigningForger}
    {s : Level} {base : Xofs} (result : ProgrammedSigningResult C s base)
    (win : result.trial.newDigestWin) {w : TerminalSigningWrite s} (hw : w ∈ result.writes) :
    result.trial.forgery.signature.take (digestBytes s) ≠ w.digest.toList := by
  obtain ⟨win, fresh⟩ := Bool.and_eq_true_iff.mp win
  cases hr : w.reply with
  | none =>
    have hv := (Bool.and_eq_true_iff.mp win).1
    apply result.ne_failed_digest hw hr
    cases h : result.trial.xofs.verify s result.trial.publicKey result.trial.forgery.message
        result.trial.forgery.context result.trial.forgery.signature <;> simp_all
  | some sig =>
    obtain ⟨pref, mem⟩ := result.signed w hw sig hr
    intro eq
    have repeated : result.trial.repeatsDigest := List.any_eq_true.mpr
      ⟨_, mem, beq_iff_eq.mpr (pref.trans eq.symm)⟩
    simp [repeated] at fresh

private structure Terminal (s : Level) (H : Xofs) where
  point : Fin s.params.k → Fin 256 → ℤ
  digest : FixedBytes (digestBytes s)
  reply : Option (List Byte)
  exhausted : reply = none → H.sampleInBall s digest.toList = none
  signaturePrefix : ∀ sig, reply = some sig → sig.take (digestBytes s) = digest.toList

private def accepted {s : Level} {H : Xofs} (d : FixedBytes (digestBytes s))
    (w : Fin s.params.k → Fin 256 → ℤ) (sig : List Byte)
    (pref : sig.take (digestBytes s) = d.toList) : Terminal s H :=
  ⟨w, d, some sig, by simp, fun _ h => Option.some.inj h ▸ pref⟩

private theorem encoded_prefix (s : Level) (d : FixedBytes (digestBytes s))
    (z h) : (encodeSignature s ⟨d.toList, z, h⟩).take (digestBytes s) = d.toList := by
  rw [encodeSignature, List.append_assoc, List.take_left' (FixedBytes.length_toList d)]

private theorem finish_prefix (s : Level) (sk : PrivateKey s) (y w c)
    (d : FixedBytes (digestBytes s)) {sig} (hr :
      (finishSigningAttempt s sk y w d.toList (some c)).join = some sig) :
    sig.take (digestBytes s) = d.toList := by
  simp only [finishSigningAttempt, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.join_some, Option.map_eq_some_iff] at hr
  obtain ⟨σ, _, rfl⟩ := hr
  exact encoded_prefix s d σ.z σ.h

private def packTranscript (s : Level) (H : Xofs) (d : FixedBytes (digestBytes s))
    (t : AttemptTranscript s.params) : Terminal s H :=
  accepted d t.commitment (encodeSignature s ⟨d.toList, t.signature.z, t.signature.h⟩)
    (encoded_prefix ..)

private def recordBytes {s : Level} {H : Xofs} (d : FixedBytes (digestBytes s))
    (w : Fin s.params.k → Fin 256 → ℤ) (raw : Option (List Byte))
    (h : ∀ sig, raw = some sig → sig.take (digestBytes s) = d.toList) : Option (Terminal s H) :=
  match raw with
  | none => none
  | some sig => some (accepted d w sig (h sig rfl))

private theorem recordBytes_map {s : Level} (H : Xofs) (d : FixedBytes (digestBytes s))
    (w : Fin s.params.k → Fin 256 → ℤ) {raw : Option (List Byte)}
    {out : Option (CompressedSignature s.params)} (h) (eq : raw = out.map fun σ =>
      encodeSignature s ⟨d.toList, σ.z, σ.h⟩) :
    recordBytes d w raw h = (out.map fun σ => ⟨w, σ⟩).map (packTranscript s H d) := by
  subst raw
  cases out <;> rfl

private noncomputable def draw (s : Level) (A : PublicMatrix s) (H : Xofs)
    (onSuccess : (d : FixedBytes (digestBytes s)) → (c : Poly) →
      H.sampleInBall s d.toList = some c → PMF (Option (Terminal s H))) :
    PMF (Option (Terminal s H)) := do
  let d ← PMF.uniformOfFintype (FixedBytes (digestBytes s))
  match h : H.sampleInBall s d.toList with
  | none =>
    let y ← signingMaskLaw s.params (by cases s <;> decide)
    return some ⟨highBitsVec s.params (moduleSISMap A y), d, none, fun _ => h, by simp⟩
  | some c => onSuccess d c h

private noncomputable def freshMaskDraw (s : Level) (A : PublicMatrix s) (sk : PrivateKey s)
    (H : Xofs) : PMF (Option (Terminal s H)) := draw s A H fun d c _ => do
  let y ← signingMaskLaw s.params (by cases s <;> decide)
  let w := moduleSISMap A y
  let out := finishSigningAttempt s sk y w d.toList (some c)
  return recordBytes d (highBitsVec s.params w) out.join fun _ h => finish_prefix s sk y w c d h

private noncomputable def publicDraw (s : Level) (pk : MLDSA.PublicKey s.params) (H : Xofs) :
    PMF (Option (Terminal s H)) := draw s pk.A H fun d c _ => do
  let out ← simulateFreshSigningAttempt s.params 13 (hintLimit s) (by cases s <;> decide) pk c
  return out.map (packTranscript s H d)

private theorem freshMaskDraw_eq (s : Level) (sk : MLDSA.SecretKey s.params)
    (rho key tr : List Byte) (H : Xofs)
    (h₁ : ∀ i j, |(sk.s₁ i j).valMinAbs| ≤ s.params.η)
    (h₂ : ∀ i j, |(sk.s₂ i j).valMinAbs| ≤ s.params.η) :
    freshMaskDraw s sk.A ⟨rho, key, tr, sk.s₁, sk.s₂, publicKeyLowPart s.params 13 sk.publicKey⟩ H =
      publicDraw s sk.publicKey H := by
  unfold freshMaskDraw publicDraw
  congr 1
  funext d c hc
  have valid := s.valid
  have eq := freshSigningAttempt_eq_simulate s.params valid (by cases s <;> decide)
    (by cases s <;> decide) 13 (hintLimit s) sk h₁ h₂ (inBall_of_sampleInBall hc)
  rw [← eq]
  simp only [freshSigningAttempt, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    _root_.PMF.bind_map]
  congr 1
  funext y
  apply congrArg _root_.PMF.pure
  apply recordBytes_map
  have tab : (Vector.ofFn c).get = c := funext (Vector.get_ofFn c)
  simp only [finishSigningAttempt, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.join_some, compressedSignAttempt, tab]

private structure History (s : Level) (base : Xofs) (tr : List Byte) where
  xofs : Xofs
  log : List Forgery
  writes : List (TerminalSigningWrite s)
  trace : TerminalSigningWrite.History s base tr writes xofs
  exhausted : ∀ w ∈ writes, w.reply = none → xofs.sampleInBall s w.digest.toList = none
  signed : ∀ w ∈ writes, ∀ sig, w.reply = some sig →
    sig.take (digestBytes s) = w.digest.toList ∧ ⟨w.request.context, w.request.message, sig⟩ ∈ log

private noncomputable def signingCall (s : Level) {base : Xofs} (tr : List Byte)
    (draw : (H : Xofs) → PMF (Option (Terminal s H))) (q : SigningQuery) (st : History s base tr) :
    PMF (Option (List Byte) × History s base tr) := do
  if 255 < q.context.length then return (none, st)
  let μ := st.xofs.representativeFromTr tr (formatMessage q.message q.context)
  let some w ← (List.range 814).findSomeM? (fun _ => draw st.xofs) | return (none, st)
  let input := commitmentInput s w.point μ
  let G := st.xofs.writeCommitment input w.digest.toList
  let writes : List (TerminalSigningWrite s) :=
    st.writes ++ [⟨q, w.point, input, w.digest, w.reply⟩]
  have hμ : μ.length = 512 := by
    simp only [μ, Xofs.representativeFromTr, Keccak.length_bytesToBitsLE, st.xofs.h256.length_read]
  have stable (d : FixedBytes (digestBytes s)) : G.sampleInBall s d.toList =
      st.xofs.sampleInBall s d.toList := Xofs.sampleInBall_writeCommitment s st.xofs μ hμ ..
  have exhausted : ∀ v ∈ writes, v.reply = none → G.sampleInBall s v.digest.toList = none := by
    intro v hv hr
    rw [stable]
    rcases List.mem_append.mp hv with old | last
    · exact st.exhausted v old hr
    · obtain rfl := List.mem_singleton.mp last
      exact w.exhausted hr
  have signed : ∀ v ∈ writes, ∀ sig, v.reply = some sig →
      sig.take (digestBytes s) = v.digest.toList ∧
        ⟨v.request.context, v.request.message, sig⟩ ∈ q.logReply w.reply st.log := by
    intro v hv sig hr
    rcases List.mem_append.mp hv with old | last
    · obtain ⟨pref, mem⟩ := st.signed v old sig hr
      exact ⟨pref, by cases w.reply <;> simp [SigningQuery.logReply, mem]⟩
    · obtain rfl := List.mem_singleton.mp last
      change w.reply = some sig at hr
      exact ⟨w.signaturePrefix sig hr, by simp [SigningQuery.logReply, hr]⟩
  return (w.reply, ⟨G, q.logReply w.reply st.log, writes,
    st.trace.append q w.point w.digest w.reply input rfl, exhausted, signed⟩)

private noncomputable def runProgrammed (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (A : PublicMatrix s) (pk tr : List Byte) (draw : (H : Xofs) → PMF (Option (Terminal s H))) :
    PMF (ProgrammedSigningResult C s H) := do
  let commands := OracleComp.sumHandler (m := StateT (Device C × History s H tr) PMF)
    (spec₁ := fun _ : DeviceRequest (Width C) Empty => List Bool)
    (spec₂ := fun _ : SigningQuery => Option (List Byte))
    (fun cmd st => C.deviceCommand st.2.xofs cmd st)
    (fun q st => (signingCall s tr draw q st.2).map fun (r, history) => (r, st.1, history))
  let (f, dev, state) ← ProbOracleComp.runWith commands (C.program pk)
    (C.initial.1, ⟨H, [], [], .initial, by simp, by simp⟩)
  return ⟨⟨state.xofs, A, pk, f, state.log⟩, tr, state.writes, state.trace, state.exhausted,
    state.signed, dev⟩

/-- Run the public-pair signing simulator on an externally supplied `(A,t)` and matrix seed.
Only the rounded encoded key reaches the forger. Every terminal commitment write is visible to
all subsequent raw queries and to the final verifier. -/
noncomputable def publicPairSigning (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (rho : FixedBytes 32) (pair : MLDSA.PublicKey s.params) : PMF (ProgrammedSigningResult C s H) :=
  let pk := encodePublic s rho.toList pair.t
  C.runProgrammed s H pair.A pk (H.h256.readBytes pk 64) (publicDraw s pair)

/-- The external public pair determines the rounded key given to the forger and the stored
key hash used by every request, including after earlier raw writes. -/
theorem publicPairSigning_key_of_mem {C : QuantumSigningForger} {s : Level} {base : Xofs}
    {rho : FixedBytes 32} {pair : MLDSA.PublicKey s.params}
    {result : ProgrammedSigningResult C s base}
    (hr : result ∈ (C.publicPairSigning s base rho pair).support) :
    result.trial.publicKey = encodePublic s rho.toList pair.t ∧
      result.tr = base.h256.readBytes result.trial.publicKey 64 := by
  simp only [publicPairSigning, runProgrammed, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    _root_.PMF.mem_support_bind_iff, _root_.PMF.mem_support_pure_iff] at hr
  obtain ⟨⟨f, dev, st⟩, _, rfl⟩ := hr
  exact ⟨rfl, rfl⟩

/-- The refreshed signing hybrid initialized from generated byte keys. The signing service
uses their decoded private fields, its stored public-key hash and the expanded matrix. It draws
an ideal mask and digest at each attempt and retains terminal commitment writes. -/
noncomputable def freshMaskSigning (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (keys : KeyPair) : PMF (Option (ProgrammedSigningResult C s H)) :=
  match decodePrivate s keys.secretKey with
  | none => pure none
  | some sk => match H.expandA s sk.rho with
    | none => pure none
    | some A => (C.runProgrammed s H A keys.publicKey sk.tr (freshMaskDraw s A sk)).map some

private theorem freshMaskSigning_eq_of_decoded (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (keys : KeyPair) (rho : FixedBytes 32) (sk : MLDSA.SecretKey s.params) (key : List Byte)
    (ha : H.expandA s rho.toList = some sk.A)
    (pk : keys.publicKey = encodePublic s rho.toList sk.publicKey.t)
    (hd : decodePrivate s keys.secretKey = some ⟨rho.toList, key,
      H.h256.readBytes keys.publicKey 64, sk.s₁, sk.s₂, publicKeyLowPart s.params 13 sk.publicKey⟩)
    (h₁ : ∀ i j, |(sk.s₁ i j).valMinAbs| ≤ s.params.η)
    (h₂ : ∀ i j, |(sk.s₂ i j).valMinAbs| ≤ s.params.η) :
    C.freshMaskSigning s H keys = (C.publicPairSigning s H rho sk.publicKey).map some := by
  simp only [freshMaskSigning, hd, ha, publicPairSigning, pk]
  congr 2
  funext G
  exact freshMaskDraw_eq s sk _ key _ G h₁ h₂

/-- For a generated FIPS key, both services induce the same joint law of the forgery, residual
device, successful signing log, terminal writes and final shared XOFs.
The pair on the public side is the matrix and full public vector of the generated key. -/
theorem freshMaskSigning_eq_publicPair_of_keyGen (C : QuantumSigningForger) {s : Level} {H : Xofs}
    {seed : FixedBytes 32} {keys : KeyPair} (hg : H.keyGen s seed = some keys) :
    ∃ (rho : FixedBytes 32) (sk : MLDSA.SecretKey s.params),
      H.expandA s rho.toList = some sk.A ∧
      keys.publicKey = encodePublic s rho.toList sk.publicKey.t ∧
      C.freshMaskSigning s H keys = (C.publicPairSigning s H rho sk.publicKey).map some := by
  obtain ⟨rho, sk, ha, hpk, hd, h₁, h₂, _⟩ := privateKey_of_keyGen hg
  exact ⟨rho, sk, ha, hpk, C.freshMaskSigning_eq_of_decoded s H keys rho sk _ ha hpk hd h₁ h₂⟩

/-- Fresh-digest **winning game** for the ideal-mask, fresh-digest signing hybrid: replace
its secret-dependent byte signing service by the public-pair simulator. Both sides first sample
the finite raw SHAKE streams and the FIPS key seed. Final verification runs on the actual XOFs
left by signing. This equality preserves the fatal errors and the 814-attempt cutoff. -/
theorem freshMask_newDigestGame_eq_publicPair (C : QuantumSigningForger) (s : Level)
    (base : Xofs) (a b : ℕ) :
    ((base.uniformPrefixes a b).bind fun H => H.keyExperiment s fun keys =>
      (C.freshMaskSigning s H keys).map (·.any fun r => r.trial.newDigestWin)) =
    ((base.uniformPrefixes a b).bind fun H => H.fullPairExperiment s fun ρ pair =>
      (C.publicPairSigning s H ρ pair).map fun r => r.trial.newDigestWin) := by
  apply congrArg (base.uniformPrefixes a b).bind
  funext H
  unfold Xofs.fullPairExperiment Xofs.keyExperiment
  apply congrArg (PMF.uniformOfFintype (FixedBytes 32)).bind
  funext seed
  cases hg : H.keyGen s seed with
  | none => rfl
  | some keys =>
    obtain ⟨ρ, sk, ha, pk, hd, h₁, h₂, _⟩ := privateKey_of_keyGen hg
    have rho : (fun i : Fin 32 => ρ.toList[i.val]!) = ρ := by
      funext i
      simp only [FixedBytes.toList, List.length_ofFn, getElem!_pos, i.isLt, List.getElem_ofFn]
    have same := C.freshMaskSigning_eq_of_decoded s H keys ρ sk _ ha pk hd h₁ h₂
    dsimp only
    rw [same, _root_.PMF.map_comp]
    simp only [hd, ha, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.getD_some,
      rho]
    rfl

/-- A changed message representative in a real output of the public-pair simulator yields a
terminal request whose representative in the original oracle equals the original public-key
hash. The search checks fatal and successful writes in order. -/
theorem publicPairSigning_match_of_changed_representative {C : QuantumSigningForger} {s : Level}
    {base : Xofs} {rho : FixedBytes 32} {pair : MLDSA.PublicKey s.params}
    {result : ProgrammedSigningResult C s base}
    (hr : result ∈ (C.publicPairSigning s base rho pair).support) (formatted : List Bool)
    (changed : result.trial.xofs.messageRepresentative result.trial.publicKey formatted ≠
      base.messageRepresentative result.trial.publicKey formatted) :
    let tr := base.h256.readBytes result.trial.publicKey 64
    let addr (w : TerminalSigningWrite s) :=
      representativeInput tr (formatMessage w.request.message w.request.context)
    ∃ w, result.writes.find? (fun z => base.h256.read (addr z) 64 == tr) = some w ∧
      base.h256.read (addr w) 64 = tr := by
  intro tr addr
  obtain ⟨pk, hash⟩ := publicPairSigning_key_of_mem hr
  have ht : result.tr.length = 64 := hash ▸ base.h256.length_read ..
  have pkread := result.history.read_publicKey rho pair.t 64
  rw [← pk] at pkread
  cases found : result.writes.find? (fun z => base.h256.read (addr z) 64 == tr) with
  | some w => exact ⟨w, rfl,
      beq_iff_eq.mp (List.find?_some (p := fun z => base.h256.read (addr z) 64 == tr) found)⟩
  | none =>
    exfalso
    apply changed
    have clean (w) (hw : w ∈ result.writes) :
        base.h256.read (representativeInput result.tr
          (formatMessage w.request.message w.request.context)) 64 ≠ result.tr := by
      have miss := List.find?_eq_none.mp found w hw
      simpa only [hash, addr, tr, beq_iff_eq] using miss
    have same := result.history.read_representative ht clean formatted 64
    rw [hash] at same
    simp only [Xofs.messageRepresentative, Xofs.representativeFromTr, pkread, same]

end QuantumSigningForger

end Cslib.Crypto.MLDSA.FIPS204
