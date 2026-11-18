/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.PublicPairSigning
import all CslibFrontier.Crypto.Computational.MLDSA.PublicPairSigning
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204
import all CslibFrontier.Crypto.Computational.MLDSA.SignedMatrix
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Bind

/-!
# Checking a fresh ML-DSA forgery with the original random oracle

The public signing simulator writes challenge digests into the shared SHAKE256 stream. A
fresh-digest win under the modified verifier is lost under the original verifier only if a
terminal request has a message representative equal to the public-key hash under the original
stream. Both verifiers use the same key, forgery and signing log. We check both hash reads in
[FIPS 204][NISTFIPS204],
Algorithm 8. At the commitment address the final digest must come from the original stream
or a surviving write. A fresh accepted digest differs from every written digest, including
writes followed by an expansion error. At the representative address the first write that
could change its value gives the stated match in the original stream.

This is a game comparison for the capped, retained-controller public signing simulator.
The comparison and its error event are original deductions for the FIPS encodings.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

/-- Does a terminal signing request hash to the public-key hash on the original SHAKE256
stream? The search includes requests that returned an expansion error. -/
@[expose] def Xofs.terminalRepresentativeMatch (H : Xofs) {s : Level} (pk : List Byte)
    (writes : List (TerminalSigningWrite s)) : Bool :=
  let tr := H.h256.readBytes pk 64
  writes.any fun w =>
    let m := formatMessage w.request.message w.request.context
    H.h256.read (representativeInput tr m) 64 == tr

private theorem TerminalSigningWrite.History.matrix {s : Level} {base G : Xofs} {tr writes}
    (history : History s base tr writes G) (seed : List Byte) :
    G.expandA s seed = base.expandA s seed := by
  induction history with
  | initial => rfl
  | append previous q w d r x address ih => exact ih

private theorem TerminalSigningWrite.History.challenge {s : Level} {base G : Xofs} {tr writes}
    (history : History s base tr writes G) (d : FixedBytes (digestBytes s)) :
    G.sampleInBall s d.toList = base.sampleInBall s d.toList := by
  induction history with
  | initial => rfl
  | @append past G previous q w val r x address ih =>
    subst x
    have hμ : (G.representativeFromTr tr (formatMessage q.message q.context)).length = 512 := by
      simp [Xofs.representativeFromTr, Keccak.length_bytesToBitsLE, G.h256.length_read]
    exact (Xofs.sampleInBall_writeCommitment s G _ hμ w val.toList d).trans ih

private theorem TerminalSigningWrite.History.read_digest {s : Level} {base G : Xofs} {tr writes}
    (history : History s base tr writes G) (x : List Bool) :
    G.h256.read x (digestBytes s) = base.h256.read x (digestBytes s) ∨
      ∃ w ∈ writes, G.h256.read x (digestBytes s) = w.digest.toList := by
  induction history with
  | initial => exact Or.inl rfl
  | @append past G previous q w d r addr address ih =>
    by_cases eq : x = addr
    · subst x
      refine Or.inr ⟨⟨q, w, addr, d, r⟩, List.mem_append_right past List.mem_cons_self, ?_⟩
      have drop := List.drop_eq_nil_of_le (G.h256.length_read addr (digestBytes s)).le
      have take := List.take_of_length_le (FixedBytes.length_toList d).le
      simp [Xofs.writeCommitment, ExtendableOutput.withPrefixes, ExtendableOutput.readWithPrefix,
        FixedBytes.length_toList, take, drop]
    · have unchanged : (G.writeCommitment addr d.toList).h256.read x (digestBytes s) =
          G.h256.read x (digestBytes s) := by
        simp [Xofs.writeCommitment, ExtendableOutput.withPrefixes, eq]
      rw [unchanged]
      exact ih.imp_right fun ⟨z, hz, he⟩ => ⟨z, List.mem_append_left _ hz, he⟩

namespace QuantumSigningForger

/-- For an accepted fresh digest in a programmed signing result, equality of the final
message representative suffices to recover acceptance by the original FIPS verifier. -/
private theorem verify_of_sameRepresentative {C : QuantumSigningForger} {s : Level} {base : Xofs}
    (r : ProgrammedSigningResult C s base) (win : r.trial.newDigestWin)
    (rep : r.trial.xofs.messageRepresentative r.trial.publicKey (formattedMessage r.trial.forgery) =
      base.messageRepresentative r.trial.publicKey (formattedMessage r.trial.forgery)) :
    base.verify s r.trial.publicKey r.trial.forgery.message r.trial.forgery.context
      r.trial.forgery.signature = some true := by
  let G := r.trial.xofs
  let pk := r.trial.publicKey
  let f := r.trial.forgery
  have hv : G.verify s pk f.message f.context f.signature = some true := by
    have accepted := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp win).1).1
    change (G.verify s pk f.message f.context f.signature).getD false = true at accepted
    cases h : G.verify s pk f.message f.context f.signature <;> simp_all
  obtain ⟨A, σ, c, hA, hd, hc, check⟩ := parsed_of_verifyWithExpansion (f := f) hv
  have chk := check
  simp only [Xofs.check, Bool.and_eq_true, decide_eq_true_eq] at chk
  obtain ⟨short, hash⟩ := chk
  let w := hintedCommitment s (publicKey s pk A) σ c
  let μ := G.messageRepresentative pk (formattedMessage f)
  change G.h256.read (commitmentInput s w μ) (digestBytes s) = σ.digest at hash
  have len : σ.digest.length = digestBytes s := by rw [← hash, G.h256.length_read]
  obtain ⟨d, val⟩ := FixedBytes.exists_toList len
  have agree := r.history.challenge d
  change G.sampleInBall s d.toList = base.sampleInBall s d.toList at agree
  rw [val] at agree
  have challenge : base.sampleInBall s σ.digest = some c := agree ▸ hc
  have mat : base.expandA s (pk.take 32) = some A := (r.history.matrix _).symm.trans hA
  have unchanged : base.h256.read (commitmentInput s w μ) (digestBytes s) = σ.digest := by
    rcases r.history.read_digest (commitmentInput s w μ) with he | ⟨written, mem, he⟩
    · exact he.symm.trans hash
    · exact False.elim (r.ne_written_digest_of_newDigestWin win mem
        ((digest_of_sigDecode hd).trans (hash.symm.trans he)))
  have checked : base.check s (publicKey s pk A)
      (base.messageRepresentative pk (formattedMessage f)) σ c := by
    simp only [Xofs.check, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨short, rep ▸ unchanged⟩
  change base.verify s pk f.message f.context f.signature = some true
  simp only [formattedMessage] at check checked
  simp only [Xofs.verify, Xofs.verifyWithExpansion, Xofs.verifyInternalWith, hd, hA, hc,
    Option.bind_eq_bind, Option.bind_some, check] at hv
  simpa only [Xofs.verify, Xofs.verifyWithExpansion, Xofs.verifyInternalWith, hd, mat, challenge,
    Option.bind_eq_bind, Option.bind_some, checked] using hv

/-- Check an accepted fresh digest under the raw oracles from before signing. The excess
over the original verifier on the very same forgery and log is bounded by a computable event
on the simulator's terminal requests, including those which returned an error. -/
theorem publicPairSigning_freshDigest_le (C : QuantumSigningForger) (s : Level) (base : Xofs)
    (rho : FixedBytes 32) (pair : MLDSA.PublicKey s.params) :
    let run := C.publicPairSigning s base rho pair
    Game.succProbability (run.map fun r => r.trial.newDigestWin) ≤
      Game.succProbability (run.map fun r =>
        ({r.trial with xofs := base} : SignedMatrixTrial s).newDigestWin) +
      Game.succProbability (run.map fun r =>
        base.terminalRepresentativeMatch r.trial.publicKey r.writes) := by
  intro run
  apply ENNReal.coe_le_coe.mp
  simp only [Game.succProbability, ENNReal.coe_add, ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)]
  apply Cslib.Probability.PMF.map_true_le_add
  intro r hr win
  by_cases eq : r.trial.xofs.messageRepresentative r.trial.publicKey
      (formattedMessage r.trial.forgery) =
      base.messageRepresentative r.trial.publicKey (formattedMessage r.trial.forgery)
  · left
    obtain ⟨strong, fresh⟩ := Bool.and_eq_true_iff.mp win
    have unseen := (Bool.and_eq_true_iff.mp strong).2
    have accepted := verify_of_sameRepresentative r win eq
    exact Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨by simp [accepted], unseen⟩, fresh⟩
  · right
    obtain ⟨w, found, same⟩ := publicPairSigning_match_of_changed_representative hr _ eq
    exact List.any_eq_true.mpr ⟨w, List.mem_of_find?_eq_some found, beq_iff_eq.mpr same⟩


/-- In the seeded ideal-mask signing hybrid, bound a fresh forgery by the public signing
simulator's success checked on the original SHAKE tables plus the probability of an ambient
representative match. Setup failure loses in all three games. -/
theorem freshMask_freshDigest_le_ambient (C : QuantumSigningForger) (s : Level)
    (base : Xofs) (a b : ℕ) :
    let run (test : (H : Xofs) → ProgrammedSigningResult C s H → Bool) : Game :=
      (base.uniformPrefixes a b).bind fun H => H.fullPairExperiment s fun rho pair =>
        (C.publicPairSigning s H rho pair).map (test H)
    Game.succProbability ((base.uniformPrefixes a b).bind fun H => H.keyExperiment s fun keys =>
      (C.freshMaskSigning s H keys).map (·.any fun r => r.trial.newDigestWin)) ≤
      Game.succProbability (run fun H r =>
        ({r.trial with xofs := H} : SignedMatrixTrial s).newDigestWin) +
      Game.succProbability (run fun H r =>
        H.terminalRepresentativeMatch r.trial.publicKey r.writes) := by
  intro run
  rw [C.freshMask_newDigestGame_eq_publicPair]
  apply ENNReal.coe_le_coe.mp
  simp only [Game.succProbability, ENNReal.coe_add, ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)]
  apply Cslib.Probability.PMF.bind_apply_le_add_on_support
  intro H _
  unfold Xofs.fullPairExperiment Xofs.keyExperiment
  apply Cslib.Probability.PMF.bind_apply_le_add_on_support
  intro seed _
  cases hk : H.keyGen s seed with
  | none => simp
  | some keys =>
    cases hd : decodePrivate s keys.secretKey with
    | none => simp [hd]
    | some sk =>
      cases ha : H.expandA s sk.rho with
      | none => simp [hd, ha]
      | some A =>
        have bound := C.publicPairSigning_freshDigest_le s H
          (fun j : Fin 32 => sk.rho[j.val]!) (MLDSA.SecretKey.mk A sk.s₁ sk.s₂).publicKey
        have bound' := ENNReal.coe_le_coe.mpr bound
        simpa only [Game.succProbability, ENNReal.coe_add,
          ENNReal.coe_toNNReal (PMF.apply_ne_top _ _), hd, ha,
          Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.getD_some] using bound'

end QuantumSigningForger

end Cslib.Crypto.MLDSA.FIPS204
