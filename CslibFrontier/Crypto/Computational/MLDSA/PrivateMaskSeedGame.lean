/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.SigningMaskSeeds
-- Reads private `withMaskSeedOracles` and `read_ne_maskSeed_length`, plus `maskSeedGame`.
import all CslibFrontier.Crypto.Computational.MLDSA.SigningMaskSeeds
import CslibFrontier.Crypto.Game.CloseTo.UntilBad
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Crypto.Game.Statistical
import CslibFrontier.Languages.Probabilistic.Presample
import CslibFrontier.Probability.StatisticalDistance.ClosedForm
import CslibFrontier.Tactic.PMFSwap

/-!
# Private mask seeds in the background-oracle ML-DSA forgery game

In the fresh-digest reduction, replace the mask seed of [FIPS 204][NISTFIPS204] Algorithm 7,
line 7 by a fresh 64-byte draw at each signing request. All remaining reads, including the
expansion of that seed, use the same background oracle as the quantum adversary and verifier.

`dist_maskSeedGame_privateMaskSeedGame` proves the full scored game changes by at most
`n / 2^256` for `n` signing calls. `randomPrefixGame_forgery_le_privateMaskSeedGame` substitutes
this comparison into the strong-forgery bound and retains the coherent-oracle comparison.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability Cslib.Quantum
open scoped Cslib.Probability.PMF

private abbrev Row := BitString 512 → FixedBytes 64

private def Xofs.signWithRow (H : Xofs) (s : Level) (key : List Byte) (q : SigningQuery)
    (row : Row) : Option (List Byte) := do
  guard (q.context.length ≤ 255)
  H.runSigning s (H.startSigningWithSeed s key (formatMessage q.message q.context) fun _ μ =>
    (row (BitString.ofList 512 μ)).toList)

private abbrev Unchanged (H G : Xofs) (bits : ℕ) :=
  ∀ x : List Bool, x.length ≠ bits → ∀ k, H.h256.read x k = G.h256.read x k

private theorem commitmentInput_length_ne_maskSeed (s : Level)
    (w : Fin s.params.k → Fin 256 → ℤ) {μ : List Bool} (hμ : μ.length = 512) :
    (commitmentInput s w μ).length ≠ 1024 := by
  rw [commitmentInput_length s w hμ]
  cases s <;> decide

private theorem challenge_unchanged {H G : Xofs} {bits : ℕ} (raw : Unchanged H G bits) (s : Level)
    {d : List Byte} (hd : 8 * d.length ≠ bits) : H.sampleInBall s d = G.sampleInBall s d :=
  congrArg (sampleInBallBytes s) (raw _ (by rwa [Keccak.length_bytesToBitsLE]) _)

/-- A signing attempt is insensitive to changes at a single input length disjoint from
its mask-expansion, commitment-hash and sparse-challenge inputs. -/
private theorem attempt_congr_of_read {H G : Xofs} {bits : ℕ} {s : Level} {sk : PrivateKey s}
    {A : PublicMatrix s} {μ : List Bool} {r : FixedBytes 64} {κ : ℕ} (raw : Unchanged H G bits)
    (hn : 528 ≠ bits) (hw : ∀ w, (commitmentInput s w μ).length ≠ bits)
    (hc : 8 * digestBytes s ≠ bits) :
    H.attempt s sk A μ r.toList κ = G.attempt s sk A μ r.toList κ := by
  have nonce (i k : ℕ) : H.h256.readBytes (nonceInput r.toList i) k =
      G.h256.readBytes (nonceInput r.toList i) k :=
    raw _ (by simpa only [Keccak.length_bytesToBitsLE, nonceInput, List.length_append,
      FixedBytes.toList, List.length_ofFn, List.length_cons, List.length_nil] using hn) _
  have digest w : H.commitmentDigest s w μ = G.commitmentDigest s w μ := raw _ (hw w) _
  have challenge w : H.sampleInBall s (G.commitmentDigest s w μ) =
      G.sampleInBall s (G.commitmentDigest s w μ) :=
    challenge_unchanged raw s (by rwa [length_commitmentDigest])
  simp only [Xofs.attempt, Xofs.attemptWithMask, Xofs.expandMask, nonce, digest, challenge]

private theorem verify_eq_of_reads {G H : Xofs} {bits : ℕ} (s : Level) (pk : List Byte)
    (hA : G.h128 = H.h128) (raw : Unchanged G H bits) (hb : 512 < bits)
    (hw : ∀ w {μ : List Bool}, μ.length = 512 → (commitmentInput s w μ).length ≠ bits)
    (good : ∀ m, G.messageRepresentative pk m = H.messageRepresentative pk m) (f : Forgery) :
    G.verify s pk f.message f.context f.signature =
      H.verify s pk f.message f.context f.signature := by
  apply Xofs.verify_congr_of_reads
  · exact Xofs.expandA_congr hA s _
  · intro d hd
    have : digestBytes s ≤ 64 := by cases s <;> decide
    exact challenge_unchanged raw s (by lia)
  · exact fun _ _ => good _
  · exact fun w => raw _ (hw w (length_messageRepresentative ..)) _

section Coupled

variable {base : Xofs} {s : Level} {seed : FixedBytes 32} {a b n : ℕ}
  {t : Fin n ↪ FixedBytes 32} {ha : 1024 ≤ a} {hb : 64 ≤ b} {rows : SigningMaskSeeds n}
  {p : SigningMaskSeedOracles} (hp : p ∈ (base.sampleSigningMaskSeeds s seed t ha hb rows).support)

include hp

private theorem sign_eq_row {keys : KeyPair} (hg : p.background.keyGen s seed = some keys)
    (good : ∀ m, p.shared.messageRepresentative keys.publicKey m =
      p.background.messageRepresentative keys.publicKey m) (i : Fin n) (q : SigningQuery) :
    p.shared.sign s keys.secretKey q.message q.context (t i) =
      p.background.signWithRow s keys.secretKey q (fun μ => rows (i, μ)) := by
  obtain ⟨rho, sk, mat, _, dec, _⟩ :=
    privateKey_of_keyGen ((keyGen_eq_of_mem_sampleSigningMaskSeeds hp s seed).trans hg)
  have bgMat :=
    (Xofs.expandA_congr (agree_off_sampleSigningMaskSeeds hp).1 s rho.toList).symm.trans mat
  let m := formatMessage q.message q.context
  let μ := p.background.messageRepresentative keys.publicKey m
  have rep : p.shared.representativeFromTr (p.shared.h256.readBytes keys.publicKey 64) m = μ :=
    good m
  have rep' : p.background.representativeFromTr (p.shared.h256.readBytes keys.publicKey 64) m = μ :=
    congrArg (p.background.representativeFromTr · m)
      (publicKeyHash_eq_of_mem_sampleSigningMaskSeeds hp hg)
  have len : μ.length = 512 := length_messageRepresentative ..
  have seedRead := read_of_mem_sampleSigningMaskSeeds hp i (BitString.ofList 512 μ)
  rw [BitString.ofFn_ofList len] at seedRead
  by_cases ctx : q.context.length ≤ 255
  · simp only [Xofs.sign, Xofs.signWithRow, Xofs.signInternal, Xofs.runSigning, Xofs.startSigning,
      Xofs.startSigningWithSeed, Xofs.startDecodedSigning, guard, ctx, ↓reduceIte, Option.pure_def,
      Option.bind_eq_bind, Option.bind_some, dec,
      ← show m = formatMessage q.message q.context from rfl, rep, rep', seedRead, mat, bgMat]
    exact congrArg (firstAccepted s.params.ℓ · 814 0) (funext fun κ =>
      attempt_congr_of_read (r := rows (i, BitString.ofList 512 μ)) (κ := κ)
        (read_ne_maskSeed_length hp) (by decide)
        (fun w => commitmentInput_length_ne_maskSeed s w len) (by cases s <;> decide))
  · simp [Xofs.sign, Xofs.signWithRow, guard, ctx]


end Coupled


namespace QuantumSigningForger

private noncomputable def signingTapeTranscript (C : QuantumSigningForger) {V : Type} [Zero V]
    (H : Xofs) (pk : List Byte) (sign : V → SigningQuery → Option (List Byte))
    (tape : List V) : PMF (Forgery × List Forgery) :=
  ((OracleComp.interpret (OracleComp.withSampleListWhen isSigningCall (0 : V)
    (fun r => C.signingCommand H (sign r))) (C.program pk)).run (C.initial, tape)).map
    fun (f, st, _) => (f, st.2)

private noncomputable def sampledSigningTranscript (C : QuantumSigningForger)
    {V : Type} [Fintype V] [Zero V] (H : Xofs) (pk : List Byte)
    (sign : V → SigningQuery → Option (List Byte)) : PMF (Forgery × List Forgery) :=
  let command := fun r => C.signingCommand H (sign r)
  ((OracleComp.interpret (m := StateT (State C) PMF) (fun q st =>
    if isSigningCall q then (PMF.uniformOfFintype V).bind fun r => command r q st
    else command 0 q st) (C.program pk)).run C.initial).map fun (f, st) => (f, st.2)

private theorem uniform_signingTapeTranscript (C : QuantumSigningForger) {V : Type}
    [Fintype V] [Zero V] (H : Xofs) (pk : List Byte) (sign : V → SigningQuery → Option (List Byte))
    {n : ℕ} (hn : C.SigningCallsLe n) :
    ((PMF.uniformOfFintype (Fin n → V)).bind fun r =>
      C.signingTapeTranscript H pk sign (List.ofFn r)) = C.sampledSigningTranscript H pk sign := by
  have law := OracleComp.IsCostBounded.run_interpret_presample_when isSigningCall
    (hn pk) (PMF.uniformOfFintype V) 0 (fun r => C.signingCommand H (sign r)) C.initial
  rw [PMF.iid_uniformOfFintype] at law
  simpa only [signingTapeTranscript, sampledSigningTranscript, PMF.map_bind, PMF.bind_map,
    PMF.map_comp, Function.comp_def] using congrArg (PMF.map fun x => (x.1, x.2.2)) law

private noncomputable def rowCommand (C : QuantumSigningForger) (H : Xofs) (s : Level)
    (keys : KeyPair) (row : Row) :=
  C.signingCommand H (fun q => H.signWithRow s keys.secretKey q row)

private noncomputable def rowTranscript (C : QuantumSigningForger) (H : Xofs) (s : Level)
    (keys : KeyPair) (tape : List Row) : PMF (Forgery × List Forgery) :=
  C.signingTapeTranscript H keys.publicKey (fun row q => H.signWithRow s keys.secretKey q row) tape

private theorem run_eq_rows (C : QuantumSigningForger) {base : Xofs} {s : Level}
    {seed : FixedBytes 32} {a b n : ℕ} {t : Fin n ↪ FixedBytes 32} {ha : 1024 ≤ a}
    {hb : 64 ≤ b} {rows : SigningMaskSeeds n} {p : SigningMaskSeedOracles}
    (hp : p ∈ (base.sampleSigningMaskSeeds s seed t ha hb rows).support)
    {keys : KeyPair} (hg : p.background.keyGen s seed = some keys)
    (good : ∀ m, p.shared.messageRepresentative keys.publicKey m =
      p.background.messageRepresentative keys.publicKey m)
    {α : Type} {program : ProbOracleComp (OracleSpec.sum
      (fun _ : DeviceRequest (Width C) Empty => List Bool)
      (fun _ : SigningQuery => Option (List Byte))) α}
    (hn : OracleComp.IsCostBounded (fun q => (isSigningCall q).toNat) program n) :
    ((OracleComp.interpret (OracleComp.withSampleListWhen isSigningCall (fun _ => 0)
      (C.hedgeCommand p.background p.shared s keys.secretKey)) program).run
      (C.initial, List.ofFn t)).map (fun (a, st, _) => (a, st)) =
    ((OracleComp.interpret (OracleComp.withSampleListWhen isSigningCall (fun _ _ => 0)
      (C.rowCommand p.background s keys)) program).run
      (C.initial, List.ofFn fun i μ => rows (i, μ))).map (fun (a, st, _) => (a, st)) := by
  let f := C.hedgeCommand p.background p.shared s keys.secretKey
  let g := C.rowCommand p.background s keys
  refine OracleComp.IsCostBounded.run_interpret_sampleListWhen_congr isSigningCall
    hn (fun _ => 0) (fun _ _ => 0) f g (by rintro (k | cmd | sign) h <;> first | contradiction |
      simp only [f, g, hedgeCommand, rowCommand, signingCommand, OracleComp.sumHandler])
    (List.ofFn t) (List.ofFn fun i μ => rows (i, μ)) (by simp) ?_ C.initial
  refine List.forall₂_of_length_eq_of_get (by simp) fun j h₁ h₂ q on => ?_
  rcases q with k | cmd | sign <;> first | contradiction |
    simp only [List.get_ofFn, Fin.cast_mk, f, g, hedgeCommand, rowCommand, signingCommand,
      OracleComp.sumHandler, sign_eq_row hp hg good]

private theorem transcript_eq_rows (C : QuantumSigningForger) {base : Xofs} {s : Level}
    {seed : FixedBytes 32} {a b n : ℕ} {t : Fin n ↪ FixedBytes 32} {ha : 1024 ≤ a}
    {hb : 64 ≤ b} {rows : SigningMaskSeeds n} {p : SigningMaskSeedOracles}
    (hp : p ∈ (base.sampleSigningMaskSeeds s seed t ha hb rows).support)
    {keys : KeyPair} (hg : p.background.keyGen s seed = some keys)
    (good : ∀ m, p.shared.messageRepresentative keys.publicKey m =
      p.background.messageRepresentative keys.publicKey m) (hn : C.SigningCallsLe n) :
    C.transcriptWithHedges p.background p.shared s keys (List.ofFn t) =
      C.rowTranscript p.background s keys (List.ofFn fun i μ => rows (i, μ)) := by
  have cmd : C.rowCommand p.background s keys = fun r =>
      C.signingCommand p.background fun q => p.background.signWithRow s keys.secretKey q r := rfl
  simpa only [transcriptWithHedges, rowTranscript, signingTapeTranscript, cmd,
    show (0 : Row) = fun _ _ => 0 from rfl, PMF.map_comp, Function.comp_def, probOracleSpec,
    unifSpec, Width, Row] using
    congrArg (PMF.map fun x => (x.1, x.2.2)) (run_eq_rows C hp hg good (hn keys.publicKey))

private noncomputable def privateTranscript (C : QuantumSigningForger) (H : Xofs) (s : Level)
    (keys : KeyPair) : PMF (Forgery × List Forgery) :=
  C.sampledSigningTranscript (V := FixedBytes 64) H keys.publicKey
    fun r q => H.signWithRow s keys.secretKey q (fun _ => r)

private theorem uniform_row_reply (H : Xofs) (s : Level) (key : List Byte) (q : SigningQuery)
    {α : Type} (k : Option (List Byte) → PMF α) :
    (PMF.uniformOfFintype Row).bind (fun row => k (H.signWithRow s key q row)) =
    (PMF.uniformOfFintype (FixedBytes 64)).bind
      (fun r => k (H.signWithRow s key q (fun _ => r))) := by
  classical
  let tr := ((decodePrivate s key).map PrivateKey.tr).getD []
  let i := BitString.ofList 512 (H.representativeFromTr tr (formatMessage q.message q.context))
  have hit (row : Row) : H.signWithRow s key q row = H.signWithRow s key q (fun _ => row i) := by
    cases dec : decodePrivate s key with
    | none => simp [Xofs.signWithRow, Xofs.runSigning, Xofs.startSigningWithSeed, dec]
    | some sk => simp [Xofs.signWithRow, Xofs.runSigning, Xofs.startSigningWithSeed,
        Xofs.startDecodedSigning, dec, i, tr]
  have law : (PMF.uniformOfFintype Row).map (fun row => row i) =
      PMF.uniformOfFintype (FixedBytes 64) := by
    rw [← PMF.pi_uniformOfFintype (ι := BitString 512) (α := fun _ => FixedBytes 64)]
    exact PMF.pi_map_eval _ i
  rw [← law, PMF.bind_map]
  exact congrArg (PMF.bind _ ·) (funext fun row => congrArg k (hit row))

private theorem uniform_rows_transcript (C : QuantumSigningForger) (H : Xofs) (s : Level)
    (keys : KeyPair) {n : ℕ} (hn : C.SigningCallsLe n) :
    (PMF.uniformOfFintype (SigningMaskSeeds n)).bind
        (fun rows => C.rowTranscript H s keys (List.ofFn fun i μ => rows (i, μ))) =
      C.privateTranscript H s keys := by
  let U := PMF.uniformOfFintype Row
  have joint := OracleComp.IsCostBounded.run_interpret_presample_when isSigningCall
    (hn keys.publicKey) U (fun _ _ => 0) (C.rowCommand H s keys) C.initial
  have convert (q : Request C) (st : State C) :
      (if isSigningCall q then U.bind fun row => C.rowCommand H s keys row q st
       else C.rowCommand H s keys (fun _ _ => 0) q st) =
      (if isSigningCall q then (PMF.uniformOfFintype (FixedBytes 64)).bind fun r =>
        C.rowCommand H s keys (fun _ => r) q st
       else C.rowCommand H s keys (fun _ _ => 0) q st) := by
    rcases q with k | cmd | q <;> simp only [isSigningCall, Sum.elim_inl, Sum.elim_inr,
      Bool.false_eq_true, ↓reduceIte]
    exact uniform_row_reply H s keys.secretKey q
      fun sig => PMF.pure (sig, st.1, q.logReply sig st.2)
  rw [PMF.iid_uniformOfFintype] at joint
  simp_rw [convert] at joint
  have eq := congrArg (PMF.map fun (out, st) => (out, st.2)) joint
  rw [← PMF.uniformOfFintype_map_equiv (Equiv.curry (Fin n) (BitString 512) (FixedBytes 64))] at eq
  simp only [rowTranscript, privateTranscript, signingTapeTranscript, sampledSigningTranscript,
    rowCommand, PMF.bind_map, PMF.map_bind, PMF.map_comp,
    Function.comp_def, Equiv.curry_apply, SigningMaskSeeds, Row, Width,
    probOracleSpec] at eq ⊢
  convert eq using 1
  congr 1

/-- Fresh-digest forgery in the finite random-XOF game when Algorithm 7 draws a private
64-byte mask seed on each signing call. Expansion, rejection sampling, coherent queries and
verification use the same sampled pair of XOFs throughout. -/
noncomputable def privateMaskSeedGame (C : QuantumSigningForger) (s : Level) (base : Xofs)
    (a b : ℕ) : Game := do
  let H ← base.uniformPrefixes a b
  let seed ← PMF.uniformOfFintype (FixedBytes 32)
  scoreTranscript H s SignedMatrixTrial.newDigestWin (H.keyGen s seed) (C.privateTranscript H s)

private def representativeBad (s : Level) (seed : FixedBytes 32) (p : SigningMaskSeedOracles) :=
  ∃ keys, p.background.keyGen s seed = some keys ∧ ∃ m,
    p.shared.messageRepresentative keys.publicKey m ≠
      p.background.messageRepresentative keys.publicKey m

private theorem score_eq_rows (C : QuantumSigningForger) {base : Xofs} {s : Level}
    {seed : FixedBytes 32} {a b n : ℕ} {t : Fin n ↪ FixedBytes 32} {ha : 1024 ≤ a}
    {hb : 64 ≤ b} {rows : SigningMaskSeeds n} {p : SigningMaskSeedOracles}
    (hp : p ∈ (base.sampleSigningMaskSeeds s seed t ha hb rows).support)
    (good : ¬representativeBad s seed p) (hn : C.SigningCallsLe n) :
    C.scoreWithSetup s p.background p.shared (p.background.keyGen s seed)
      (List.ofFn t) SignedMatrixTrial.newDigestWin =
    scoreTranscript p.background s SignedMatrixTrial.newDigestWin (p.background.keyGen s seed)
      (fun keys => C.rowTranscript p.background s keys (List.ofFn fun i μ => rows (i, μ))) := by
  cases hg : p.background.keyGen s seed with
  | none => rfl
  | some keys =>
    have rep (m) : p.shared.messageRepresentative keys.publicKey m =
        p.background.messageRepresentative keys.publicKey m :=
      by_contra fun ne => good ⟨keys, hg, m, ne⟩
    simp only [scoreWithSetup, scoreTranscript, withTrialSetup,
      Xofs.expandA_congr (agree_off_sampleSigningMaskSeeds hp).1,
      transcript_eq_rows C hp hg rep hn]
    cases p.background.expandA s (keys.publicKey.take 32) with
    | none => rfl
    | some A =>
      refine congrArg (PMF.map · _) (funext fun ⟨f, log⟩ => congrArg
        (fun v : Option Bool => (v.getD false && !log.contains f) &&
          !log.any fun g => g.signature.take (digestBytes s) == f.signature.take (digestBytes s))
        (verify_eq_of_reads s keys.publicKey (agree_off_sampleSigningMaskSeeds hp).1
          (read_ne_maskSeed_length hp) (by decide) (commitmentInput_length_ne_maskSeed s) rep f))

private theorem avg_score_rows (C : QuantumSigningForger) (H : Xofs) (s : Level)
    (keys : Option KeyPair) {n : ℕ} (hn : C.SigningCallsLe n) :
    (PMF.uniformOfFintype (SigningMaskSeeds n)).bind (fun rows =>
      scoreTranscript H s SignedMatrixTrial.newDigestWin keys
        (fun k => C.rowTranscript H s k (List.ofFn fun i μ => rows (i, μ)))) =
    scoreTranscript H s SignedMatrixTrial.newDigestWin keys (C.privateTranscript H s) := by
  cases keys with
  | none => exact PMF.bind_const _ _
  | some k =>
    simp only [scoreTranscript, withTrialSetup]
    cases H.expandA s (k.publicKey.take 32) <;> dsimp only
    · exact PMF.bind_const _ _
    · rw [← PMF.map_bind, uniform_rows_transcript C H s k hn]

private theorem fixed_rows_bound (C : QuantumSigningForger) (s : Level) (base : Xofs)
    (seed : FixedBytes 32) {a b n : ℕ} (ha : 1024 ≤ a) (hb : 64 ≤ b)
    (hn : C.SigningCallsLe n) (hsize : n ≤ 2 ^ 256) (rows : SigningMaskSeeds n) :
    let _ : Nonempty (Fin n ↪ FixedBytes 32) := hedgeEmbedding_nonempty hsize
    (Game.advantage
      ((PMF.uniformOfFintype (Fin n ↪ FixedBytes 32)).bind fun t =>
        (base.sampleSigningMaskSeeds s seed t ha hb rows).bind fun p =>
          C.scoreWithSetup s p.background p.shared (p.background.keyGen s seed)
            (List.ofFn t) SignedMatrixTrial.newDigestWin)
      ((base.uniformPrefixes a b).bind fun H =>
        scoreTranscript H s SignedMatrixTrial.newDigestWin (H.keyGen s seed)
          (fun k => C.rowTranscript H s k (List.ofFn fun i μ => rows (i, μ)))) : ℝ) ≤
      n / 2 ^ 256 := by
  classical
  let _ : Nonempty (Fin n ↪ FixedBytes 32) := hedgeEmbedding_nonempty hsize
  let tapes := PMF.uniformOfFintype (Fin n ↪ FixedBytes 32)
  let draw := fun t => base.sampleSigningMaskSeeds s seed t ha hb rows
  let joint := tapes.bind fun t => (draw t).map (t, ·)
  let right (H : Xofs) := scoreTranscript H s SignedMatrixTrial.newDigestWin (H.keyGen s seed)
    fun k => C.rowTranscript H s k (List.ofFn fun i μ => rows (i, μ))
  have close := Interactive.CloseTo.bind_of_eq_on joint
    (fun z => C.scoreWithSetup s z.2.background z.2.shared (z.2.background.keyGen s seed)
      (List.ofFn z.1) SignedMatrixTrial.newDigestWin)
    (fun z => right z.2.background) (Prod.snd ⁻¹' {p | representativeBad s seed p}) (by
      rintro ⟨t, p⟩ hj hgood
      obtain ⟨_, _, hp⟩ := (PMF.mem_support_bind_iff ..).mp hj
      obtain ⟨_, hp, ⟨⟩⟩ := (PMF.mem_support_map_iff ..).mp hp
      exact score_eq_rows C hp hgood hn)
  have marg : joint.map Prod.snd = tapes.bind draw := by
    simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
    exact congrArg tapes.bind (funext fun t => PMF.map_id (draw t))
  have ref : joint.bind (fun z => right z.2.background) =
      (base.uniformPrefixes a b).bind right := by
    have eq (t) : (draw t).bind (fun p => right p.background) =
        (base.uniformPrefixes a b).bind right := by
      rw [← base.background_sampleSigningMaskSeeds s seed t ha hb rows, PMF.bind_map]; rfl
    simp only [joint, PMF.bind_bind, PMF.bind_map, Function.comp_def, eq, PMF.bind_const]
  rw [ref, ← PMF.toOuterMeasure_map_apply, marg] at close
  have adv := ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _)
    (Game.closeTo_iff_coe_advantage_le.mp close)
  simpa only [ENNReal.coe_toReal, joint, PMF.bind_bind, PMF.bind_map, Function.comp_def,
    tapes, draw, right] using
    adv.trans (base.prob_representative_ne_sampleSigningMaskSeeds s seed ha hb hsize rows)

/-- Replacing Algorithm 7's mask-seed hash with one fresh private seed per signing call in
the background-device fresh-digest game costs at most the signing budget divided by
`2^256`. The device can make coherent queries and choose signing requests adaptively. -/
theorem dist_maskSeedGame_privateMaskSeedGame (C : QuantumSigningForger) (s : Level)
    (base : Xofs) {a b n : ℕ} (ha : 1024 ≤ a) (hb : 64 ≤ b) (hn : C.SigningCallsLe n)
    (hsize : n ≤ 2 ^ 256) :
    dist (C.maskSeedGame s base ha hb hn hsize false SignedMatrixTrial.newDigestWin)
      (C.privateMaskSeedGame s base a b) ≤ (n : ℝ) / 2 ^ 256 := by
  let _ : Nonempty (Fin n ↪ FixedBytes 32) := hedgeEmbedding_nonempty hsize
  let seeds := PMF.uniformOfFintype (FixedBytes 32)
  let tables := PMF.uniformOfFintype (SigningMaskSeeds n)
  let L (seed : FixedBytes 32) (rows : SigningMaskSeeds n) :=
    (PMF.uniformOfFintype (Fin n ↪ FixedBytes 32)).bind fun t =>
      (base.sampleSigningMaskSeeds s seed t ha hb rows).bind fun p =>
        C.scoreWithSetup s p.background p.shared (p.background.keyGen s seed) (List.ofFn t)
          SignedMatrixTrial.newDigestWin
  let T (seed : FixedBytes 32) (rows : SigningMaskSeeds n) :=
    (base.uniformPrefixes a b).bind fun H =>
      scoreTranscript H s SignedMatrixTrial.newDigestWin (H.keyGen s seed) fun k =>
        C.rowTranscript H s k (List.ofFn fun i μ => rows (i, μ))
  have actual : C.maskSeedGame s base ha hb hn hsize false SignedMatrixTrial.newDigestWin =
      seeds.bind fun seed => tables.bind (L seed) := by
    simp only [maskSeedGame, withMaskSeedOracles, PMF.monad_bind_eq_bind, Bool.false_eq_true,
      ↓reduceIte, seeds, tables, L]
    pmf_swap with seed
    pmf_swap with rows
    rfl
  have ideal : (seeds.bind fun seed => tables.bind (T seed)) =
      C.privateMaskSeedGame s base a b := by
    simp only [privateMaskSeedGame, PMF.monad_bind_eq_bind, seeds, tables, T]
    pmf_swap with H
    exact congrArg _ (funext fun _ => avg_score_rows C H s _ hn)
  rw [actual, ← ideal, ← coe_nndist, ← Game.advantage_eq_nndist]
  exact Game.advantage_bind_le seeds _ _ fun seed => Game.advantage_bind_le tables _ _ fun rows =>
    fixed_rows_bound C s base seed ha hb hn hsize rows

private theorem dist_matrixTrial_sharedMaskSeedGame (C : QuantumSigningForger) (s : Level)
    (base : Xofs) {a b n : ℕ} (ha : 1024 ≤ a) (hb : 894 ≤ b) (hn : C.SigningCallsLe n)
    (hsize : n ≤ 2 ^ 256) (score : SignedMatrixTrial s → Bool) :
    dist (((base.uniformPrefixes a b).bind (C.matrixTrial s)).map (·.any score))
      (C.maskSeedGame s base ha ((by decide : 64 ≤ 894).trans hb) hn hsize true score) ≤
      ((n * (n - 1) : ℕ) : ℝ) / 2 ^ 257 := by
  rw [C.shared_maskSeedGame_eq_distinctHedgeGame]
  exact C.dist_matrixTrial_distinctHedges s base ((by decide : 272 ≤ 1024).trans ha) hb hn hsize _

/-- A concrete decomposition of the finite random-XOF strong-forgery probability. Its open
terms are the private-seed fresh-digest game, the effect of coherent access to the programmed
rows, a raw hash collision and the success of the repeated-digest Hermite Module-SIS solver.
The explicit losses cover hedge repetition and message-representative changes. -/
theorem randomPrefixGame_forgery_le_privateMaskSeedGame (C : QuantumSigningForger) (s : Level)
    (base : Xofs) {a b n : ℕ} (ha : 1024 ≤ a) (hb : 894 ≤ b) (hn : C.SigningCallsLe n)
    (hsize : n ≤ 2 ^ 256) :
    let R := base.uniformPrefixes a b
    let trial := R.bind (C.matrixTrial s)
    let view (shared : Bool) := C.maskSeedGame s base ha ((by decide : 64 ≤ 894).trans hb)
      hn hsize shared SignedMatrixTrial.newDigestWin
    (Game.succProbability (C.randomPrefixGame s base a b) : ℝ) ≤
      Game.succProbability (C.privateMaskSeedGame s base a b) + dist (view true) (view false) +
      ((n * (n - 1) : ℕ) : ℝ) / 2 ^ 257 + n / 2 ^ 256 +
      Game.succProbability (trial.map (·.any SignedMatrixTrial.hashCollision)) +
      Game.succProbability ((PMF.uniformOfFintype (PublicMatrix s)).bind fun A =>
        (R.bind fun H => C.matrixSolver s H A).map fun v => decide (ModuleSIS.IsSolution
          (ModuleSIS.hermiteMatrix A)
          (max (2 * (s.params.γ₁ - s.params.β)) (4 * s.params.γ₂ + 2)) v)) := by
  intro R trial view
  let fresh := trial.map (·.any SignedMatrixTrial.newDigestWin)
  let priv := C.privateMaskSeedGame s base a b
  have birthday : dist fresh (view true) ≤ ((n * (n - 1) : ℕ) : ℝ) / 2 ^ 257 :=
    C.dist_matrixTrial_sharedMaskSeedGame s base ha hb hn hsize _
  have privateSeed : dist (view false) priv ≤ n / 2 ^ 256 :=
    C.dist_maskSeedGame_privateMaskSeedGame s base ha _ hn hsize
  have loss : dist fresh priv ≤ ((n * (n - 1) : ℕ) : ℝ) / 2 ^ 257 +
      dist (view true) (view false) + n / 2 ^ 256 := by
    calc
      _ ≤ dist fresh (view false) + dist (view false) priv := dist_triangle ..
      _ ≤ (dist fresh (view true) + dist (view true) (view false)) + n / 2 ^ 256 :=
        add_le_add (dist_triangle ..) privateSeed
      _ ≤ _ := add_le_add (add_le_add birthday le_rfl) le_rfl
  rw [← coe_nndist, ← Game.advantage_eq_nndist] at loss
  have branch := NNReal.coe_le_coe.mpr
    (C.randomPrefixGame_forgery_le s base ((by decide : 272 ≤ 1024).trans ha) hb)
  simp only [NNReal.coe_add] at branch
  refine branch.trans ((add_le_add
    (Game.coe_succProbability_le_add_of_advantage_le loss) le_rfl).trans_eq ?_)
  abel


end QuantumSigningForger

end Cslib.Crypto.MLDSA.FIPS204
