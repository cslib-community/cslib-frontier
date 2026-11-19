/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Crypto.Computational.MLDSA.RejectedCommitmentWrites

/-!
# ML-DSA digest-register clients

Check the native signing oracle and forgery score, a nonconstant little-endian digest, and two
coherent reads past the digest.
-/

set_option linter.privateModule false

open Cslib Cslib.Crypto Cslib.Crypto.MLDSA.FIPS204 Cslib.Quantum Cslib.Probability

example : Level.mlDSA44.commitmentInputBits = 6656 ∧
    Level.mlDSA65.commitmentInputBits = 6656 ∧ Level.mlDSA87.commitmentInputBits = 8704 := by
  decide

-- A digest with only bit 8 set tests the byte boundary at the raw commitment address.
example (H : Xofs) (s : Level) (w : Fin s.params.k → Fin 256 → ℤ) (μ : BitString 512) :
    let D := fun (_ : BitString s.commitmentInputBits) (j : Fin (8 * digestBytes s)) =>
      decide (j.val = 8)
    Keccak.bytesToBitsLE ((H.withDigestRegister s D).commitmentDigest s w (List.ofFn μ)) =
      List.ofFn (fun j : Fin (8 * digestBytes s) => decide (j.val = 8)) :=
  H.commitmentDigest_withDigestRegister s _ w List.length_ofFn

-- The ML-DSA-44 device XORs 33 bytes, one past the installed digest. Two different wire
-- placements share the same clean scratch registers on an arbitrary initial superposition.
example (H : Xofs) (D : BitString Level.mlDSA44.commitmentInputBits → BitString 256)
    {m : ℕ} (p q : Fin (6656 + 2 + 8 * 33) ↪ Fin m) (ψ : Qubits m) :
    let native := (H.withDigestRegister .mlDSA44 D).queryTable 6656 33
    let run := fun wires state => runValue addStep
      (lookupXorSteps wires (Xofs.digestLookup .mlDSA44) (H.digestResponse .mlDSA44 6656 33))
      state D 2
    run q (run p (cleanLookupState ψ)) =
      cleanLookupState ((xorQuery native q).eval ((xorQuery native p).eval ψ)) := by
  intro native run
  exact (congrArg (run q ·) (H.xorQuery_withDigestRegister .mlDSA44 D 6656 33 m p ψ)).trans
    (H.xorQuery_withDigestRegister .mlDSA44 D 6656 33 m q ((xorQuery native p).eval ψ))

-- At an adaptive signing call the service samples the real hedge, returns the exact reply and
-- logs only a success. This is the handler used by the retained-state controller.
example {R : Type} (H : Xofs) (s : Level) (D) (key : List Byte) (q : SigningQuery)
    (log : List Forgery) (next : Option (List Byte) × List Forgery → PMF R) :
    ((H.withDigestRegister s D).signingOracle s key q log).bind next =
      (PMF.uniformOfFintype (FixedBytes 32)).bind fun rnd =>
        let reply := OracleComp.evalPure D (H.signDigestQueries s key q rnd)
        next (reply, q.logReply reply log) := by
  rw [H.signingOracle_eq_digestQueries, PMF.bind_map]
  rfl

-- Score the candidate and its complete log with the two-query verifier in the original game.
example (C : QuantumSigningForger) (H : Xofs) (s : Level) {a b : ℕ}
    (ha : s.commitmentInputBits ≤ a) (hb : digestBytes s ≤ b) :
    C.randomPrefixGame s H a b =
      (H.uniformPrefixes a b).bind fun base => base.keyExperiment s fun keys =>
        (PMF.uniformOfFintype
          (BitString s.commitmentInputBits → BitString (8 * digestBytes s))).bind fun D =>
          (C.transcript (base.withDigestRegister s D) s keys).map fun (f, log) =>
            (OracleComp.evalPure D (base.verifyDigestQueries s keys.publicKey f)).getD false &&
              !log.contains f := by
  rw [C.randomPrefixGame_eq_digestRegister H s ha hb]
  simp only [Xofs.winsForgery, Xofs.evalPure_verifyDigestQueries]

-- A coherent query and a measurement select the message sent to the signer. The program
-- chooses between two independent candidates according to whether signing succeeded.
open Cslib.Crypto.MLDSA

example (C : QuantumSigningForger) (s : Level) (H : Xofs) (A : PublicMatrix s)
    (m : BitString 512) (D : BitString s.commitmentInputBits → BitString (8 * digestBytes s))
    (keys : KeyPair) (onSignature onError : Forgery)
    (w : Fin C.Width) (d : C.Device) (log : List Forgery)
    (row : FixedBytes 2 → FixedBytes (maskPolyBytes s)) :
    let μ := signingMaskLaw s.params (by cases s <;> decide)
    let r y j := !(D (maskCommitmentAddress s A m y) j)
    let δ := (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal
    let prog : C.Program Forgery :=
      .liftBind (.inr (.inl .query)) fun _ =>
        .liftBind (.inr (.inl (.measure w))) fun bits =>
          .liftBind (.inr (.inr ⟨[], bits⟩)) fun sig =>
            .pure (if sig.isSome then onSignature else onError)
    let win T := Game.succProbability (C.expansionContinuation s (H.withDigestRegister s T)
      A keys prog d log [row])
    ∑ y, (μ y).toReal * |(win (Function.update D (maskCommitmentAddress s A m y) (r y)) : ℝ) -
        (win D : ℝ)| ≤ 4 * √δ + 817 * δ := by
  classical
  intro μ r δ prog win
  have hH : OracleComp.IsCostBounded (fun x => (QuantumSigningForger.isXofQuery x).toNat)
      prog 1 :=
    .liftBind _ _ 0 fun _ => .liftBind _ _ 0 fun _ => .liftBind _ _ 0 fun _ => .pure _ _
  have hS : OracleComp.IsCostBounded (fun x => (QuantumSigningForger.isSigningCall x).toNat)
      prog 1 :=
    .liftBind _ _ 1 fun _ => .liftBind _ _ 1 fun _ => .liftBind _ _ 0 fun _ => .pure _ _
  simpa [μ, δ, win, show (815 : ℝ) + 2 = 817 by norm_num] using
    C.mean_expansionContinuation_gap_le s H A m D r keys prog d log [row] hH hS

-- Start with a genuine seeded key. A signature or an error selects an independent candidate,
-- and the actual verifier scores it on the stream left by the capped request.
example (C : QuantumSigningForger) (s : Level) (H : Xofs) (seed : FixedBytes 32)
    (keys : KeyPair) (hg : H.keyGen s seed = some keys) (A : PublicMatrix s)
    (hm : H.expandA s (keys.publicKey.take 32) = some A) (q : SigningQuery) (D)
    (dev : C.Device) (log : List Forgery)
    (rows : List (FixedBytes 2 → FixedBytes (maskPolyBytes s)))
    (onReply onError : Forgery) :
    let k (r : Option (List Byte)) : C.Program Forgery :=
      .pure (if r.isSome then onReply else onError)
    let p keep := Game.succProbability (C.freshDigestSigningCall s H keys q D keep k dev log rows)
    let δ := (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal
    |(p true : ℝ) - (p false : ℝ)| ≤ 1628 * δ := by
  classical
  intro k p δ
  obtain ⟨rho, pair, ha, pk, sk, _⟩ := privateKey_of_keyGen hg
  rw [pk, take_encodePublic, ha] at hm
  cases hm
  have bound := C.abs_freshDigestSigningCall_keep_sub_erase_le s H keys q D k dev log rows
    (qH := 0) (qS := 0) (fun r => .pure _ 0) (fun r => .pure _ 0)
  simpa [p, δ, sk, ha, ← mul_assoc, show (814 : ℝ) * 2 = 1628 by norm_num] using bound

-- Wires 0 and 1 encode SHAKE256 and the delimiter of a full-length address. A Hadamard on
-- wire 2 gives two possible commitment-table inputs. Measure the first XOR response bit and
-- use it together with the signing result to select independently supplied candidates.
private def afterOnlySignature (s : Level) (fresh replay : Forgery) (sig : Option (List Byte)) :
    ProbOracleComp (OracleSpec.sum
      (fun _ : DeviceRequest (s.commitmentInputBits + 2 + 8 * 1 + 0) Empty => List Bool)
      (fun _ : SigningQuery => Option (List Byte))) Forgery :=
  .liftBind (.inr (.inl (.gate (false, false, 0, [])))) fun _ =>
    .liftBind (.inr (.inl (.gate (false, false, 1, [])))) fun _ =>
      .liftBind (.inr (.inl (.gate (false, true, 2, [])))) fun _ =>
        .liftBind (.inr (.inl .query)) fun _ =>
          .liftBind (.inr (.inl (.measure ⟨s.commitmentInputBits + 2, by lia⟩))) fun bits =>
            .pure (if bits.headD false = sig.isSome then fresh else replay)

private def onceForger (s : Level) (q : SigningQuery) (fresh replay : Forgery) :
    QuantumSigningForger :=
  ⟨s.commitmentInputBits, 1, 0, fun _ => .liftBind (.inr (.inr q))
    (afterOnlySignature s fresh replay)⟩

example (s : Level) (H : Xofs) (keys : KeyPair) (q : SigningQuery) (fresh replay : Forgery) :
    let C := onceForger s q fresh replay
    C.freshDigestSigningCall s H keys q (H.readDigestRegister s) false
        (afterOnlySignature s fresh replay) C.initialDevice [] [] =
      (C.freshMaskSigning s H keys).map (·.any (·.trial.newDigestWin)) := by
  intro C
  have h := C.freshDigestSigningCall_eq_freshMaskSigning_of_single_call s H keys q
    (H.readDigestRegister s) (afterOnlySignature s fresh replay) rfl (fun _ =>
      .liftBind _ _ 0 fun _ => .liftBind _ _ 0 fun _ => .liftBind _ _ 0 fun _ =>
        .liftBind _ _ 0 fun _ => .liftBind _ _ 0 fun _ => .pure _ 0)
  let score (G : Xofs) := (C.freshMaskSigning s G keys).map (·.any (·.trial.newDigestWin))
  exact h.trans (congrArg score (H.withDigestRegister_readDigestRegister s))
