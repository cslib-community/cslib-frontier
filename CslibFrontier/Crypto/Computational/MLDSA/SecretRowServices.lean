/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.SecretRowPrediction
import all CslibFrontier.Crypto.Computational.MLDSA.SecretRowPrediction
import all CslibFrontier.Crypto.Computational.MLDSA.SharedSecretExpansion
import all CslibFrontier.Crypto.Computational.MLDSA.PublicPairSigning
import all CslibFrontier.Crypto.Computational.MLDSA.RandomXof
import all CslibFrontier.Crypto.Computational.MLDSA.MaskSeedQuery
import all CslibFrontier.Crypto.Computational.MLDSA.KeySeedSearch
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204
import all CslibFrontier.Crypto.Computational.MLDSA.SignedMatrix
import CslibFrontier.Probability.IID.FirstSome
import Batteries.Data.Fin.Lemmas
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204Signing

/-!
# Private expansion rows in the adaptive public-pair signing experiment

[FIPS 204][NISTFIPS204], Algorithms 3, 6 and 8, use the raw SHAKE256 stream for key generation,
message representatives and commitment digests. The signing simulator retains terminal writes.
When two streams differ only on private expansion inputs, identical terminal writes preserve
agreement everywhere else. The public hash matching the secret seed is the one exceptional
honest read. The controller can still query the private inputs in superposition.
-/

public section
namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability ExtendableOutput
open scoped ENNReal

private def RowAgreement {s : Level} (v : SecretExpansionViews s) (L R : Xofs) : Prop :=
  L.h128 = R.h128 ∧ ∀ x, x ≠ keySeedInput s v.keySeed →
    (∀ j : Fin (s.params.ℓ + s.params.k), x ≠ Keccak.bytesToBitsLE
      (nonceInput v.secretSeed.toList j.val)) → ∀ i, L.h256.byteAt x i = R.h256.byteAt x i

private theorem agree_at_setup {s : Level} {base : Xofs} {a b : ℕ} {ha : 528 ≤ a} {hb : 481 ≤ b}
    {v : SecretExpansionViews s} (hv : v ∈ (base.sampleSecretExpansionViews s ha hb).support)
    {H : Xofs} (hH : H ∈ v.refreshKeySeed.support) (share : Bool) :
    RowAgreement v (if share then v.shared else v.background) H := by
  obtain ⟨out, _, rfl⟩ := (by
    simpa only [SecretExpansionViews.refreshKeySeed, PMF.mem_support_map_iff] using hH)
  have original := v.agree_of_mem hv
  constructor
  · cases share <;> first | rfl | exact original.1
  · intro x key short i
    simp only [Xofs.withKeySeedExpansion, byteAt_withPrefixes, key, ↓reduceIte, Option.bind_none,
      Option.getD_none]
    cases share
    · rfl
    · exact original.2 x i (Or.inr short)

private theorem RowAgreement.write {s : Level} {v : SecretExpansionViews s} {L R : Xofs}
    (h : RowAgreement v L R) (x : List Bool) (out : List Byte) :
    RowAgreement v (L.writeCommitment x out) (R.writeCommitment x out) := by
  refine ⟨h.1, ?_⟩
  intro y key short i
  simp only [Xofs.writeCommitment, byteAt_withPrefixes, h.2 y key short i]

private theorem RowAgreement.read {s : Level} {v : SecretExpansionViews s} {L R : Xofs}
    (h : RowAgreement v L R) {x : List Bool} (hk : x.length ≠ 272) (hn : x.length ≠ 528)
    (n : ℕ) : L.h256.read x n = R.h256.read x n := by
  apply read_eq_of_byteAt_eq
  intro i _
  exact h.2 x (fun e => hk (e ▸ length_keySeedInput ..))
    (fun _ e => hn (e ▸ length_nonceInput_bits ..)) i

private theorem RowAgreement.publicKey {s : Level} {v : SecretExpansionViews s} {L R : Xofs}
    (h : RowAgreement v L R) (pk : MLDSA.PublicKey s.params) :
    L.h256.readBytes (encodePublic s v.publicSeed.toList pk.t) 64 =
      R.h256.readBytes (encodePublic s v.publicSeed.toList pk.t) 64 := by
  apply h.read <;> rw [Keccak.length_bytesToBitsLE, length_encodePublic, FixedBytes.length_toList]
    <;> cases s <;> decide

private theorem RowAgreement.challenge {s : Level} {v : SecretExpansionViews s} {L R : Xofs}
    (h : RowAgreement v L R) {d : List Byte} (hd : d.length = digestBytes s) :
    L.sampleInBall s d = R.sampleInBall s d := by
  apply congrArg (sampleInBallBytes s)
  apply h.read <;> rw [Keccak.length_bytesToBitsLE, hd] <;> cases s <;> decide

private theorem RowAgreement.rep {s : Level} {v : SecretExpansionViews s} {L R : Xofs}
    (h : RowAgreement v L R) {tr : List Byte} (size : tr.length = 64)
    (safe : tr ≠ v.secretSeed.toList)
    (q : SigningQuery) :
    L.representativeFromTr tr (formatMessage q.message q.context) =
      R.representativeFromTr tr (formatMessage q.message q.context) := by
  apply congrArg Keccak.bytesToBitsLE
  apply read_eq_of_byteAt_eq
  intro i _
  apply h.2 _ _ _ i
  · intro same
    have bad := congrArg List.length same
    simp only [representativeInput, List.length_append, Keccak.length_bytesToBitsLE,
      size, length_keySeedInput] at bad
    lia
  · intro j same
    obtain ⟨t, rfl⟩ := FixedBytes.exists_toList size
    have fit : s.params.ℓ + s.params.k ≤ 65536 := by cases s <;> decide
    have hit := (representativeInput_eq_nonceInput_iff t v.secretSeed q.context q.message
      (j.castLE fit)).mp same
    exact safe (congrArg FixedBytes.toList hit.1)

private theorem RowAgreement.digest {s : Level} {v : SecretExpansionViews s} {L R : Xofs}
    (h : RowAgreement v L R) (w : Fin s.params.k → Fin 256 → ℤ)
    {μ : List Bool} (hm : μ.length = 512) :
    L.commitmentDigest s w μ = R.commitmentDigest s w μ := by
  apply h.read <;> rw [commitmentInput_length s w hm] <;> cases s <;> decide

/-- Apply the exact recorded prefix writes in chronological order to a second raw oracle. -/
def TerminalSigningWrite.replay {s : Level} (H : Xofs) (writes : List (TerminalSigningWrite s)) :
    Xofs :=
  writes.foldl (fun G w => G.writeCommitment w.address w.digest.toList) H

private theorem RowAgreement.replay {s : Level} {v : SecretExpansionViews s} {L R : Xofs}
    (h : RowAgreement v L R) (ws : List (TerminalSigningWrite s)) :
    RowAgreement v (TerminalSigningWrite.replay L ws) (TerminalSigningWrite.replay R ws) := by
  induction ws generalizing L R with
  | nil => exact h
  | cons w ws ih => exact ih (h.write w.address w.digest.toList)

/-- Replaying a certified signing history's terminal writes recovers its final oracle. -/
theorem TerminalSigningWrite.History.replay_eq {s : Level} {H G : Xofs}
    {tr : List Byte} {ws : List (TerminalSigningWrite s)} (history : History s H tr ws G) :
    TerminalSigningWrite.replay H ws = G := by
  induction history with
  | initial => rfl
  | append past q w d r x addr ih =>
    simp only [TerminalSigningWrite.replay, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact congrArg (fun G : Xofs => G.writeCommitment x d.toList) ih

private theorem RowAgreement.freshWin {s : Level} {v : SecretExpansionViews s} {L R : Xofs}
    (h : RowAgreement v L R) (pk : MLDSA.PublicKey s.params) (f : Forgery) (log : List Forgery)
    (safe : R.h256.readBytes (encodePublic s v.publicSeed.toList pk.t) 64 ≠ v.secretSeed.toList) :
    let bytes := encodePublic s v.publicSeed.toList pk.t
    SignedMatrixTrial.newDigestWin ⟨L, pk.A, bytes, f, log⟩ =
      SignedMatrixTrial.newDigestWin ⟨R, pk.A, bytes, f, log⟩ := by
  intro bytes
  have reads := Xofs.verify_congr_of_reads (H := L) (G := R) s bytes f.message f.context f.signature
    (Xofs.expandA_congr h.1 s _) (fun _ hd => h.challenge hd)
    (fun _ _ => by
      simp only [Xofs.messageRepresentative, bytes, h.publicKey pk]
      exact h.rep (R.h256.length_read ..) safe ⟨f.context, f.message⟩)
    (fun w => h.digest w (length_messageRepresentative ..))
  simp only [SignedMatrixTrial.newDigestWin, SignedMatrixTrial.wins, Xofs.winsForgery, reads]
  rfl

namespace QuantumSigningForger

private def carryTerminal {s : Level} {L R : Xofs}
    (same : ∀ d : FixedBytes (digestBytes s), L.sampleInBall s d.toList = R.sampleInBall s d.toList)
    (t : Terminal s L) : Terminal s R :=
  ⟨t.point, t.digest, t.reply, fun hn => (same t.digest).symm.trans (t.exhausted hn),
    t.signaturePrefix⟩

private theorem draw_eq_map {s : Level} {L R : Xofs} (pair : MLDSA.PublicKey s.params)
    (same : ∀ d : FixedBytes (digestBytes s),
      L.sampleInBall s d.toList = R.sampleInBall s d.toList) :
    publicDraw s pair R = (publicDraw s pair L).map (Option.map (carryTerminal same)) := by
  simp only [publicDraw, draw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind]
  apply congrArg (PMF.bind _ ·)
  funext d
  have eq := same d
  split
  next hr =>
    split
    next hl =>
      simp only [PMF.map_bind, PMF.pure_map, Option.map_some]
      rfl
    next c hl => simp [hl, hr] at eq
  next c hr =>
    split
    next hl => simp [hl, hr] at eq
    next c' hl =>
      have e : c' = c := Option.some.inj (hl.symm.trans (eq.trans hr))
      subst c'
      simp only [PMF.map_bind, PMF.pure_map]
      apply congrArg (PMF.bind _ ·)
      funext out
      cases out <;> rfl

private theorem retries_eq_map {α β ι : Type} (p : PMF (Option α)) (f : α → β) (l : List ι) :
    (l.findSomeM? fun _ => p.map (Option.map f)) =
      (l.findSomeM? fun _ => p).map (Option.map f) := by
  have identity := PMF.iid_map_findSome p id l
  simp only [PMF.map_id, id_eq] at identity
  rw [← PMF.iid_map_findSome, ← identity, PMF.map_comp]
  exact congrArg (fun h => (PMF.iid p l.length).map h)
    (funext fun v => (Fin.map_findSome? v f).symm)

-- Both calls use the same matrix, full pair, and public-key hash, with their own raw streams
-- and certified write histories. The continuation can observe every write and the full reply.
private theorem publicCall_congr {s : Level} {v : SecretExpansionViews s} {base₁ base₂ : Xofs}
    {tr : List Byte} (st₁ : History s base₁ tr) (st₂ : History s base₂ tr)
    (h : RowAgreement v st₁.xofs st₂.xofs) (log : st₁.log = st₂.log)
    (writes : st₁.writes = st₂.writes) (size : tr.length = 64) (safe : tr ≠ v.secretSeed.toList)
    (pair : MLDSA.PublicKey s.params) (q : SigningQuery) {α : Type}
    (left : Option (List Byte) → History s base₁ tr → PMF α)
    (right : Option (List Byte) → History s base₂ tr → PMF α)
    (next : ∀ r t₁ t₂, RowAgreement v t₁.xofs t₂.xofs → t₁.log = t₂.log →
      t₁.writes = t₂.writes → left r t₁ = right r t₂) :
    ((signingCall s tr (publicDraw s pair) q st₁).bind fun x => left x.1 x.2) =
      ((signingCall s tr (publicDraw s pair) q st₂).bind fun x => right x.1 x.2) := by
  have same (d : FixedBytes (digestBytes s)) :=
    h.challenge (FixedBytes.length_toList d)
  by_cases bad : 255 < q.context.length
  · simpa only [signingCall, bad, ↓reduceIte, PMF.monad_pure_eq_pure, PMF.pure_bind] using
      next none st₁ st₂ h log writes
  simp only [signingCall, bad, ↓reduceIte, PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind,
    PMF.bind_bind]
  generalize List.range 814 = tries
  rw [draw_eq_map pair same, retries_eq_map, PMF.bind_map]
  apply congrArg (PMF.bind (tries.findSomeM? fun _ => publicDraw s pair st₁.xofs) ·)
  funext x
  cases x with
  | none =>
    simpa only [Function.comp_def, Option.map_none, PMF.pure_bind] using
      (next none st₁ st₂ h log writes)
  | some t =>
    simp only [Function.comp_def, Option.map_some, PMF.pure_bind]
    apply next
    · change RowAgreement v (st₁.xofs.writeCommitment _ _) (st₂.xofs.writeCommitment _ _)
      rw [h.rep size safe q]
      exact h.write _ _
    · change q.logReply t.reply st₁.log = q.logReply t.reply st₂.log
      rw [log]
    · change st₁.writes ++ [_] = st₂.writes ++ [_]
      rw [writes, h.rep size safe q]
      rfl

private noncomputable def scoreProgram (C : QuantumSigningForger) (s : Level) (base : Xofs)
    (rho : FixedBytes 32) (pair : MLDSA.PublicKey s.params) (tr : List Byte)
    (raw : History s base tr → Xofs) (prog : Program C Forgery) (dev : Device C)
    (st : History s base tr) : Game :=
  (ProbOracleComp.runWith (C.programmedCommands s base tr (publicDraw s pair) raw) prog
    (dev, st)).map fun (f, _, t) =>
      SignedMatrixTrial.newDigestWin ⟨t.xofs, pair.A, encodePublic s rho.toList pair.t, f, t.log⟩

private theorem scoreProgram_congr (C : QuantumSigningForger) {s : Level}
    {v : SecretExpansionViews s} {base₁ base₂ : Xofs}
    (pair : MLDSA.PublicKey s.params) (prog : Program C Forgery) {tr : List Byte}
    (key : base₂.h256.readBytes (encodePublic s v.publicSeed.toList pair.t) 64 = tr)
    (safe : tr ≠ v.secretSeed.toList) (dev : Device C)
    (st₁ : History s base₁ tr) (st₂ : History s base₂ tr)
    (h : RowAgreement v st₁.xofs st₂.xofs) (log : st₁.log = st₂.log)
    (writes : st₁.writes = st₂.writes) :
    C.scoreProgram s base₁ v.publicSeed pair tr (·.xofs) prog dev st₁ =
      C.scoreProgram s base₂ v.publicSeed pair tr
        (fun t => TerminalSigningWrite.replay base₁ t.writes) prog dev st₂ := by
  have size : tr.length = 64 := key ▸ base₂.h256.length_read ..
  induction prog generalizing st₁ st₂ dev with
  | pure f =>
    rw [show PFunctor.FreeM.pure f = (pure f : Program C Forgery) from rfl]
    simpa only [scoreProgram, ProbOracleComp.runWith_pure,
      PMF.pure_map, log] using congrArg PMF.pure (h.freshWin pair f st₂.log (by
        rw [st₂.trace.read_publicKey, key]
        exact safe))
  | liftBind cmd k ih =>
    rw [show PFunctor.FreeM.liftBind cmd k = (OracleComp.query cmd >>= k) from rfl]
    simp only [scoreProgram, ProbOracleComp.runWith, OracleComp.runWith_bind,
      OracleComp.runWith_query, PMF.map_bind, OracleComp.sumHandler]
    rcases cmd with coin | cmd | ask
    · simp only [PMF.bind_map, Function.comp_def]
      exact congrArg (PMF.bind _ ·) (funext fun i => ih i dev st₁ st₂ h log writes)
    · have raw : st₁.xofs = TerminalSigningWrite.replay base₁ st₂.writes :=
        st₁.trace.replay_eq.symm.trans (congrArg (TerminalSigningWrite.replay base₁) writes)
      simp only [programmedCommands, statefulSigningCommands, OracleComp.sumHandler, deviceCommand,
        PMF.bind_map, Function.comp_def, raw]
      apply congrArg (PMF.bind _ ·)
      funext ⟨reply, device⟩
      exact ih reply device st₁ st₂ h log writes
    · simp only [programmedCommands, statefulSigningCommands, OracleComp.sumHandler, PMF.bind_map,
        Function.comp_def]
      exact publicCall_congr st₁ st₂ h log writes size safe pair ask
        (fun r t => C.scoreProgram s base₁ v.publicSeed pair tr (·.xofs) (k r) dev t)
        (fun r t => C.scoreProgram s base₂ v.publicSeed pair tr
          (fun z => TerminalSigningWrite.replay base₁ z.writes) (k r) dev t)
        (fun r u t hu hl hw => ih r dev u t hu hl hw)

/-- Run public-pair signing and final verification on `honest`. The query device uses
`device` with every prior terminal signing write applied in the same order. -/
noncomputable def publicPairWinWithDevice (C : QuantumSigningForger) (s : Level)
    (device honest : Xofs) (rho : FixedBytes 32) (pair : MLDSA.PublicKey s.params) : Game :=
  let pk := encodePublic s rho.toList pair.t
  let tr := honest.h256.readBytes pk 64
  C.scoreProgram s honest rho pair tr (fun t => TerminalSigningWrite.replay device t.writes)
    (C.program pk) C.initial.1 ⟨honest, [], [], .initial, by simp, by simp⟩

private theorem separate_device {s : Level} {base : Xofs} {a b : ℕ} {ha : 528 ≤ a} {hb : 481 ≤ b}
    {v : SecretExpansionViews s} (hv : v ∈ (base.sampleSecretExpansionViews s ha hb).support)
    {H : Xofs} (hH : H ∈ v.refreshKeySeed.support) (share : Bool) {pair : MLDSA.PublicKey s.params}
    (hp : v.pair = some pair) (safe : v.publicHashMatch = false) (C : QuantumSigningForger) :
    let G := if share then v.shared else v.background
    (C.publicPairSigning s G v.publicSeed pair).map (·.trial.newDigestWin) =
      C.publicPairWinWithDevice s G H v.publicSeed pair := by
  intro G
  let pk := encodePublic s v.publicSeed.toList pair.t
  let tr := H.h256.readBytes pk 64
  have agree : RowAgreement v G H := agree_at_setup hv hH share
  have key : G.h256.readBytes pk 64 = tr := agree.publicKey pair
  have hash : v.shared.h256.readBytes pk 64 = tr := (agree_at_setup hv hH true).publicKey pair
  have good : tr ≠ v.secretSeed.toList := by
    simpa only [SecretExpansionViews.publicHashMatch, hp, Option.any_some, ← hash,
      beq_eq_false_iff_ne, pk] using safe
  let st₁ : History s G tr := ⟨G, [], [], .initial, by simp, by simp⟩
  let st₂ : History s H tr := ⟨H, [], [], .initial, by simp, by simp⟩
  have eq := C.scoreProgram_congr (v := v) pair (C.program pk) rfl good C.initial.1
    st₁ st₂ agree rfl rfl
  change (C.runProgrammed s G pair.A pk (G.h256.readBytes pk 64) _).map _ = _
  rw [key]
  simpa only [scoreProgram, publicPairWinWithDevice, runProgrammed, runSigningProgram,
    PMF.map_bind, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_map, PMF.map,
    Function.comp_def, PMF.bind_bind, PMF.pure_bind] using eq

/-- The honest simulator and verifier use the refreshed oracle. The forger's queries use the
chosen view with the same signing writes. Failed setup and the exceptional public-key hash
match return false before the interaction. -/
noncomputable def secretRowDeviceGame (C : QuantumSigningForger) (s : Level) (base : Xofs)
    {a b : ℕ} (ha : 528 ≤ a) (hb : 481 ≤ b) (share : Bool) : Game :=
  (base.sampleSecretExpansionViews s ha hb).bind fun v =>
    if v.publicHashMatch then PMF.pure false else
    v.refreshKeySeed.bind fun H =>
      (v.pair.map (C.publicPairWinWithDevice s (if share then v.shared else v.background)
        H v.publicSeed)).getD (PMF.pure false)

private theorem good_view {s : Level} {base : Xofs} {a b : ℕ} {ha : 528 ≤ a} {hb : 481 ≤ b}
    {v : SecretExpansionViews s} (hv : v ∈ (base.sampleSecretExpansionViews s ha hb).support)
    (share : Bool) (safe : v.publicHashMatch = false) (C : QuantumSigningForger) :
    let G := if share then v.shared else v.background
    (v.pair.map (fun pk => (C.publicPairSigning s G v.publicSeed pk).map
      (·.trial.newDigestWin))).getD (PMF.pure false) =
    v.refreshKeySeed.bind fun H =>
      (v.pair.map (C.publicPairWinWithDevice s G H v.publicSeed)).getD (PMF.pure false) := by
  intro G
  rw [← PMF.bind_const (p := v.refreshKeySeed)
    (q := (v.pair.map (fun pk => (C.publicPairSigning s G v.publicSeed pk).map
      (·.trial.newDigestWin))).getD (PMF.pure false))]
  apply PMF.bind_congr_on_support
  intro H hH
  cases hp : v.pair with
  | none => rfl
  | some pk => exact separate_device hv hH share hp safe C

/-- Transfer every adaptive signing request and final byte verification to the same refreshed
oracle. Only the coherent query device varies between the two middle games. The public-hash
exception costs at most 2⁻⁵¹² once over the whole comparison at every FIPS level. -/
theorem secretRowDeviceGame_bounds (C : QuantumSigningForger) (s : Level) (base : Xofs)
    {a b : ℕ} (ha : 528 ≤ a) (hb : 481 ≤ b) :
    let native := (base.uniformPrefixes a b).bind fun H => H.fullPairExperiment s
      (fun rho pk => (C.publicPairSigning s H rho pk).map (·.trial.newDigestWin))
    native true ≤ C.secretRowDeviceGame s base ha hb true true + (2 ^ 512 : ℝ≥0∞)⁻¹ ∧
      C.secretRowDeviceGame s base ha hb false true ≤ C.independentExpandSGame s base a b true := by
  intro native
  obtain ⟨shared, detached⟩ := C.secretExpansionViews_games s base ha hb
  let V := base.sampleSecretExpansionViews s ha hb
  constructor
  · change ((base.uniformPrefixes a b).bind _) true ≤ _
    rw [shared]
    refine le_trans ?_ (add_le_add_right (publicHashMatch_le s base ha hb) _)
    apply PMF.bind_apply_le_add_on_support V true
    intro v hv
    cases safe : v.publicHashMatch with
    | false =>
      simpa [Function.comp_def, safe] using
        (congrArg (fun g : Game => g true) (good_view hv true safe C)).le
    | true =>
      simpa [Function.comp_def, safe] using PMF.coe_le_one _ true
  · rw [detached]
    apply PMF.bind_apply_mono_on_support V true
    intro v hv
    cases safe : v.publicHashMatch with
    | false =>
      exact (congrArg (fun g : Game => g true) (good_view hv false safe C)).symm.le
    | true => simp

private def queryChanged (C : QuantumSigningForger) {s : Level} (device reference : Xofs)
    (observation : List (TerminalSigningWrite s) × Option (Address C)) : Bool :=
  let table (H : Xofs) := (TerminalSigningWrite.replay H observation.1).queryTable
    C.addressBits C.responseBytes
  observation.2.any fun addr => decide (table device addr ≠ table reference addr)

private theorem hit_of_change (C : QuantumSigningForger) {s : Level} {v : SecretExpansionViews s}
    {L R : Xofs} (h : RowAgreement v L R) (o : List (TerminalSigningWrite s) × Option (Address C))
    (diff : C.queryChanged L R o = true) :
    hitsExpansionInput s v.keySeed v.secretSeed (Xofs.shake256QueryInput o.2) = true := by
  obtain ⟨ws, addr⟩ := o
  have agree := h.replay ws
  obtain ⟨x, hx, ne⟩ := Xofs.shake256QueryInput_of_queryTable_ne agree.1 diff
  simp only [hx, hitsExpansionInput, Option.any_some, decide_eq_true_eq]
  by_contra! miss
  exact ne (read_eq_of_byteAt_eq fun i _ => agree.2 x miss.1 miss.2 i)

/-- Measure a selected query in the reference public-pair signing experiment and test whether
replaying the signing writes on the other device changes the XOR response at that address. -/
noncomputable def publicPairResponseChange (C : QuantumSigningForger) (s : Level) (j : ℕ)
    (device reference : Xofs) (rho : FixedBytes 32) (pair : MLDSA.PublicKey s.params) : Game :=
  (C.queryWrites s j reference rho pair).map (C.queryChanged device reference)

/-- At a chosen coherent query in the refreshed reference execution, measuring the address
finds a different XOR response on either source device with probability at most 2⁻²⁵⁶.
Both sides replay every prior terminal signature or exhaustion write before comparing all the
response bytes requested by the controller. -/
theorem secretRow_changedResponse_le (C : QuantumSigningForger) (s : Level) (base : Xofs)
    {a b : ℕ} (ha : 528 ≤ a) (hb : 481 ≤ b) (share : Bool) (j : ℕ) :
    ((base.sampleSecretExpansionViews s ha hb).bind fun v => v.refreshKeySeed.bind fun H =>
      match v.pair with
      | none => PMF.pure false
      | some pk => C.publicPairResponseChange s j (if share then v.shared else v.background)
          H v.publicSeed pk) true ≤
      (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  refine le_trans ?_ (C.publicPairQueryHit_le s j base ha hb)
  apply PMF.bind_apply_mono_on_support
  intro v hv
  apply PMF.bind_apply_mono_on_support
  intro H hH
  cases hp : v.pair with
  | none => exact le_rfl
  | some pk =>
    simp only [publicPairResponseChange, publicPairQueryAddress, PMF.map_comp, Function.comp_def]
    apply PMF.map_true_mono
    exact fun o _ => C.hit_of_change (agree_at_setup hv hH share) o

end QuantumSigningForger

end Cslib.Crypto.MLDSA.FIPS204
