/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.RandomXofMatrix
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Probability.StatisticalDistance
public import CslibFrontier.Crypto.Primitives.ByteString.Uniform
-- Reads private `State`, `commands`, `deviceCommand`, `runAtSetup`, and unexposed `matrixTrial`.
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning
-- Reads private `Xofs.signAndLog` and unexposed `Xofs.signingOracle` internals.
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204Signing
import CslibFrontier.Languages.Probabilistic.Presample
import CslibFrontier.Probability.UniformEmbedding
import CslibFrontier.Tactic.PMFSwap

/-!
# Distinct signing hedges in the ML-DSA forgery game

Algorithm 2 of [FIPS 204][NISTFIPS204] samples 32 random bytes per call. For a forger making
at most `n` adaptive signing requests, use one uniformly sampled injection to provide those
bytes in request order. The change in strong-forgery probability is at most
`n (n − 1) / 2²⁵⁷`. Both experiments evaluate the mask-seed derivation and every signing
attempt on the same raw XOFs that the persistent quantum device accesses.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204.QuantumSigningForger

open Cslib.Probability Cslib.Quantum
open scoped Cslib.Probability.PMF

private abbrev Request (C : QuantumSigningForger) :=
  ℕ ⊕ DeviceRequest (Width C) Empty ⊕ SigningQuery

/-- The requests charged against the classical signing budget in the quantum forgery game. -/
abbrev isSigningCall {width : ℕ} : ℕ ⊕ DeviceRequest width Empty ⊕ SigningQuery → Bool :=
  Sum.elim (fun _ => false) (Sum.elim (fun _ => false) (fun _ => true))

/-- The maximum number of classical signing requests on each path, for every published key.
Private samples, measurements, gates and coherent XOF calls have zero signing cost. -/
@[expose] def SigningCallsLe (C : QuantumSigningForger) (n : ℕ) : Prop :=
  ∀ pk, OracleComp.IsCostBounded (fun q => (isSigningCall q).toNat) (C.program pk) n

private noncomputable def signingCommand (C : QuantumSigningForger) (device : Xofs)
    (sign : SigningQuery → Option (List Byte)) :=
  OracleComp.sumHandler (m := StateT (State C) PMF)
    (fun k => StateT.lift (ProbComp.unifOracle k))
    (OracleComp.sumHandler (spec₁ := fun _ : DeviceRequest (Width C) Empty => List Bool)
      (spec₂ := fun _ : SigningQuery => Option (List Byte))
      (C.deviceCommand device)
      (fun q st => PMF.pure <| let sig := sign q
        (sig, st.1, q.logReply sig st.2)))

private noncomputable def hedgeCommand (C : QuantumSigningForger) (device H : Xofs) (s : Level)
    (sk : List Byte) (r : FixedBytes 32) :=
  C.signingCommand device fun q => H.sign s sk q.message q.context r

/-- The honest signed transcript with the hedge for each call read from the supplied list.
The quantum device uses `device`, and signing uses `H`. The fallback supplies zero bytes.
The signing budget ensures sufficient tape for the comparison with honest signing. -/
noncomputable def transcriptWithHedges (C : QuantumSigningForger) (device H : Xofs) (s : Level)
    (keys : KeyPair) (tape : List (FixedBytes 32)) : PMF (Forgery × List Forgery) :=
  ((OracleComp.interpret (OracleComp.withSampleListWhen isSigningCall (fun _ => 0)
    (C.hedgeCommand device H s keys.secretKey)) (C.program keys.publicKey)).run
      (C.initial, tape)).map
      fun (f, st, _) => (f, st.2)

/-- Uniform hedges drawn before the first instruction give the joint law of the adaptive
forgery and the entire signing log under the original XOFs. -/
theorem uniform_transcriptWithHedges (C : QuantumSigningForger) (H : Xofs) (s : Level)
    (keys : KeyPair) {n : ℕ} (hn : C.SigningCallsLe n) :
    (PMF.uniformOfFintype (Fin n → FixedBytes 32)).bind
      (fun t => C.transcriptWithHedges H H s keys (List.ofFn t)) = C.transcript H s keys := by
  let U := PMF.uniformOfFintype (FixedBytes 32)
  let online := OracleComp.sumHandler (m := StateT (State C) PMF)
    (fun k => StateT.lift (ProbComp.unifOracle k)) (C.commands H s keys.secretKey)
  have step (q : Request C) (st : State C) :
      (if isSigningCall q then U.bind fun r => C.hedgeCommand H H s keys.secretKey r q st
       else C.hedgeCommand H H s keys.secretKey (fun _ => 0) q st) = online q st := by
    rcases q with k | cmd | sign
    · rfl
    · rfl
    · simp only [isSigningCall, Sum.elim_inr, hedgeCommand, signingCommand, Xofs.signAndLog,
        online, commands, statefulSigningCommands, OracleComp.sumHandler,
        Xofs.signingOracle, U, PMF.map_comp, Function.comp_def, ↓reduceIte]
      rfl
  have joint := OracleComp.IsCostBounded.run_interpret_presample_when isSigningCall
    (hn keys.publicKey) U (fun _ => 0) (C.hedgeCommand H H s keys.secretKey) C.initial
  simp_rw [step] at joint
  rw [PMF.iid_uniformOfFintype] at joint
  have logLaw := congrArg (PMF.map fun (f, st) => (f, st.2)) joint
  simpa only [transcriptWithHedges, transcript, PMF.bind_map, PMF.map_bind, PMF.map_comp,
    Function.comp_def, ProbOracleComp.runWith_eq_run_interpret, online] using logLaw

/-- The 256-bit hedge space supplies a distinct hedge for each of at most `2^256` slots. -/
theorem hedgeEmbedding_nonempty {n : ℕ} (hn : n ≤ 2 ^ 256) :
    Nonempty (Fin n ↪ FixedBytes 32) :=
  Function.Embedding.nonempty_of_card_le
    (by simpa only [Fintype.card_fin, FixedBytes.card] using hn)

private noncomputable def withTrialSetup {α κ : Type} (H : Xofs) (s : Level)
    (publicKey : κ → List Byte) (keys : Option κ)
    (failure : α) (run : κ → PublicMatrix s → PMF α) : PMF α :=
  match keys with
  | none => PMF.pure failure
  | some keys =>
    match H.expandA s ((publicKey keys).take 32) with
    | none => PMF.pure failure
    | some A => run keys A

private noncomputable def scoreTranscript (H : Xofs) (s : Level)
    (score : SignedMatrixTrial s → Bool) (keys : Option KeyPair)
    (run : KeyPair → PMF (Forgery × List Forgery)) : Game :=
  withTrialSetup H s KeyPair.publicKey keys false fun k A =>
    (run k).map fun (f, log) => score ⟨H, A, k.publicKey, f, log⟩

private noncomputable def scoreWithSetup (C : QuantumSigningForger) (s : Level)
    (device H : Xofs) (keys : Option KeyPair) (tape : List (FixedBytes 32))
    (score : SignedMatrixTrial s → Bool) : Game :=
  scoreTranscript H s score keys fun k => C.transcriptWithHedges device H s k tape

private noncomputable def fixedHedgeGame (C : QuantumSigningForger) (s : Level)
    (base : Xofs) (a b : ℕ) (score : SignedMatrixTrial s → Bool)
    (tape : List (FixedBytes 32)) : Game :=
  (base.uniformPrefixes a b).bind fun H => (PMF.uniformOfFintype (FixedBytes 32)).bind fun seed =>
    C.scoreWithSetup s H H (H.keyGen s seed) tape score

/-- Run honest seeded key generation, signing and final scoring with a uniform injection
providing the successive 32-byte signing hedges. The key, matrix, raw XOFs, adversary's
output and log used for scoring all come from this execution. -/
noncomputable def distinctHedgeGame (C : QuantumSigningForger) (s : Level)
    (base : Xofs) (a b : ℕ) {n : ℕ} (_hn : C.SigningCallsLe n) (hsize : n ≤ 2 ^ 256)
    (score : SignedMatrixTrial s → Bool) : Game :=
  let _ : Nonempty (Fin n ↪ FixedBytes 32) := hedgeEmbedding_nonempty hsize
  (PMF.uniformOfFintype (Fin n ↪ FixedBytes 32)).bind fun t =>
    C.fixedHedgeGame s base a b score (List.ofFn t)

private theorem uniform_fixedHedgeGame (C : QuantumSigningForger) (s : Level) (base : Xofs)
    {a b n : ℕ} (ha : 272 ≤ a) (hb : 894 ≤ b) (hn : C.SigningCallsLe n)
    (score : SignedMatrixTrial s → Bool) :
    ((PMF.uniformOfFintype (Fin n → FixedBytes 32)).bind fun t =>
      C.fixedHedgeGame s base a b score (List.ofFn t)) =
      ((base.uniformPrefixes a b).bind (C.matrixTrial s)).map (·.any score) := by
  let eval := fun z => (C.runAtSetup s z).map (·.any score)
  have eq := congrArg (PMF.bind · eval) (uniformPrefixes_matrixSetup base s ha hb)
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def] at eq
  simp only [matrixTrial, PMF.monad_bind_eq_bind, PMF.map_bind]
  rw [show (fun H => (matrixSetup H s).bind fun z => (C.runAtSetup s z).map (·.any score)) =
    (fun H => (matrixSetup H s).bind eval) from rfl, eq]
  unfold fixedHedgeGame scoreWithSetup scoreTranscript withTrialSetup
  pmf_swap with H
  pmf_swap with seed
  dsimp only [eval]
  rcases hg : H.keyGen s seed with _ | keys
  · simp [runAtSetup]
  · rcases hm : H.expandA s (keys.publicKey.take 32) with _ | A
    · simp [runAtSetup, hm]
    · have law := congrArg (PMF.map fun (f, log) => score ⟨H, A, keys.publicKey, f, log⟩)
        (C.uniform_transcriptWithHedges H s keys hn)
      simpa [hm, runAtSetup, PMF.map_comp, Function.comp_def, PMF.map_bind] using law

/-- Sampling the signing hedges without replacement changes the probability of any signed
trial event by at most `n(n−1)/2²⁵⁷`. In particular the bound applies to the exact
`SignedMatrixTrial.newDigestWin` term in `randomPrefixGame_forgery_le`. -/
theorem dist_matrixTrial_distinctHedges (C : QuantumSigningForger) (s : Level)
    (base : Xofs) {a b n : ℕ} (ha : 272 ≤ a) (hb : 894 ≤ b) (hn : C.SigningCallsLe n)
    (hsize : n ≤ 2 ^ 256) (score : SignedMatrixTrial s → Bool) :
    dist (((base.uniformPrefixes a b).bind (C.matrixTrial s)).map (·.any score))
      (C.distinctHedgeGame s base a b hn hsize score) ≤ ((n * (n - 1) : ℕ) : ℝ) / 2 ^ 257 := by
  classical
  have hcard : Fintype.card (Fin n) ≤ Fintype.card (FixedBytes 32) := by
    simpa only [Fintype.card_fin, FixedBytes.card] using hsize
  let _ := Function.Embedding.nonempty_of_card_le hcard
  rw [← C.uniform_fixedHedgeGame s base ha hb hn score, dist_comm]
  simpa only [distinctHedgeGame, PMF.bind_map, Function.comp_def, Fintype.card_fin, FixedBytes.card,
    Nat.cast_pow, Nat.cast_ofNat, ← pow_succ'] using
    (PMF.dist_bind_le _ _ (fun t => C.fixedHedgeGame s base a b score (List.ofFn t))).trans
      (dist_uniform_embedding_to_fun hcard)

end Cslib.Crypto.MLDSA.FIPS204.QuantumSigningForger

namespace Cslib.Crypto.MLDSA.FIPS204

/-- At a fixed signing key the raw Algorithm 7 input determines the hedge, whatever
message representative follows it. -/
theorem hedge_eq_of_maskSeedInput_eq {key : List Byte} {r r' : FixedBytes 32} {μ ν : List Bool}
    (h : maskSeedInput key r μ = maskSeedInput key r' ν) : r = r' := by
  unfold maskSeedInput at h
  have hbytes := (List.append_inj h (by simp [Keccak.length_bytesToBitsLE, FixedBytes.toList])).1
  exact List.ofFn_inj.mp (List.append_cancel_left (Keccak.bytesToBitsLE_injective hbytes))

end Cslib.Crypto.MLDSA.FIPS204
