/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.AmbientVerification
import all CslibFrontier.Crypto.Computational.MLDSA.CompressedKeyOnly
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204
import all CslibFrontier.Crypto.Computational.MLDSA.PublicPairSigning
import all CslibFrontier.Crypto.Computational.MLDSA.SignedMatrix
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Bind

/-!
# Extracting the corrected short witness after ML-DSA signing

[Dilithium v3.1][BaiEtAl2021Dilithium], §6.2.1, equations (9)–(10), correct the low
component of a forged response using the full lattice pair `(A,t)`. The public key exposed
to the forger contains its rounded high part. For the signing simulator we run the
[FIPS 204][NISTFIPS204] byte verifier and perform extraction on its original raw XOFs.

The output is checked on the full product `u + Az − ct`. Its high bits encode that product
exactly, and Algorithm 29 on the commitment's full digest must return the witness challenge.
The game bound uses the joint law of FIPS key generation and its raw XOFs. Identifying it
with the literature's independent matrix and sparse challenge oracle requires a further reduction.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

/-- Check a corrected short witness on the original raw FIPS streams. Recover the complete
commitment digest only when the representative is 512 bits, the product is on the commitment
grid, the low part and response obey the extraction bound, and Algorithm 29 returns the
witness challenge. An exhausted expansion fails the check. -/
def Xofs.openFullWitness (H : Xofs) (s : Level) (pk : MLDSA.PublicKey s.params)
    (y : SelfTargetCandidate s.params) : Option (List Byte) := do
  let v := selfTargetMap s.params pk y.u y.z y.c
  let w := highBitsVec s.params v
  let radius := compressedSelfTargetRadius s.params 13
  guard (y.msg.length = 512)
  guard (ModuleSIS.inInfNormBound radius y.u ∧ ModuleSIS.inInfNormBound radius y.z)
  guard (SharedDigest.OnCommitmentGrid s v)
  let digest := H.commitmentDigest s w y.msg
  guard (H.sampleInBall s digest = some y.c)
  return digest

/-- A raw opening is equivalent to a short-vector solution on the canonical grid, with
the exact commitment digest and a successful sparse expansion at that digest. -/
theorem openFullWitness_eq_some_iff {H : Xofs} {s : Level}
    {pk : MLDSA.PublicKey s.params} {y : SelfTargetCandidate s.params} {d : List Byte} :
    H.openFullWitness s pk y = some d ↔
      let v := selfTargetMap s.params pk y.u y.z y.c
      y.msg.length = 512 ∧ SharedDigest.OnCommitmentGrid s v ∧
        H.commitmentDigest s (highBitsVec s.params v) y.msg = d ∧
        H.sampleInBall s d = some y.c ∧
        IsSelfTargetSolution s.params (selfTargetHash s.params (H.algebraicHash s))
          (compressedSelfTargetRadius s.params 13) pk y := by
  simp only [Xofs.openFullWitness, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.guard_eq_some', Option.pure_def, Option.some.injEq, exists_const]
  constructor
  · rintro ⟨len, ⟨hu, hz⟩, grid, hc, rfl⟩
    refine ⟨len, grid, rfl, hc, hu, hz, inBall_of_sampleInBall hc, ?_⟩
    exact congrArg (fun x => Option.getD x 0) hc
  · rintro ⟨len, grid, rfl, hc, sol⟩
    exact ⟨len, ⟨sol.1, sol.2.1⟩, grid, hc, rfl⟩

/-- An accepting byte signature gives a short witness whose raw opening recovers exactly the
digest bytes in that signature. The matrix at the public seed and the full public vector are
those of the lattice pair supplied to the extractor. -/
theorem opening_extractFull_of_verify {H : Xofs} {s : Level} {rho : FixedBytes 32}
    {pk : MLDSA.PublicKey s.params} {f : Forgery} (hA : H.expandA s rho.toList = some pk.A)
    (hv : H.verify s (encodePublic s rho.toList pk.t) f.message f.context f.signature = some true) :
    ∃ y, H.extractFull s rho pk.A pk.t f = some y ∧
      H.openFullWitness s pk y = some (f.signature.take (digestBytes s)) := by
  obtain ⟨y, hy, bounded⟩ := extractFull_of_verifyWithExpansion hA hv
  obtain ⟨σ, c, hs, hc, _, hd⟩ := verifiedSignature_of_verifyWithExpansion hA hv
  let μ := H.messageRepresentative (encodePublic s rho.toList pk.t) (formattedMessage f)
  let sig : CompressedSignature s.params := ⟨σ.z, σ.h, c⟩
  let u := compressedForgeryLowPart s.params 13 pk sig
  have ey : candidate s pk μ σ c = y := by
    simpa only [Xofs.extractFull, hs, hc, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq, μ] using hy
  subst y
  refine ⟨_, hy, ?_⟩
  have high := highBits_selfTargetMap_compressedForgeryLowPart s.valid
    (by cases s <;> decide) 13 pk sig
  have grid : SharedDigest.OnCommitmentGrid s (selfTargetMap s.params pk u σ.z c) := by
    intro i j
    rw [show highBitsVec s.params (selfTargetMap s.params pk u σ.z c) = _ from high]
    exact congrFun (congrFun (selfTargetMap_compressedForgeryLowPart 13 pk sig) i) j
  have digest : H.commitmentDigest s
      (highBitsVec s.params (selfTargetMap s.params pk u σ.z c)) μ = σ.digest := by
    rw [show highBitsVec s.params (selfTargetMap s.params pk u σ.z c) = _ from high]
    exact hd
  rw [openFullWitness_eq_some_iff, digest_of_sigDecode hs]
  exact ⟨length_messageRepresentative .., grid, digest, hc, bounded⟩

namespace QuantumSigningForger

/-- Run the simulator on a supplied full lattice pair and parse its final classical output
once using the original XOFs. The retained forger receives the rounded public bytes and
keeps coherent access throughout the signing interaction. -/
noncomputable def publicPairWitness (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (rho : FixedBytes 32) (pk : MLDSA.PublicKey s.params) :
    PMF (Option (SelfTargetCandidate s.params)) :=
  (C.publicPairSigning s H rho pk).map fun r => H.extractFull s rho pk.A pk.t r.trial.forgery

private theorem ambient_le_witness (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (rho : FixedBytes 32) (pk : MLDSA.PublicKey s.params)
    (hA : H.expandA s rho.toList = some pk.A) :
    ((C.publicPairSigning s H rho pk).map fun r =>
      ({r.trial with xofs := H} : SignedMatrixTrial s).newDigestWin) true ≤
    ((C.publicPairWitness s H rho pk).map fun o =>
      (o.bind (H.openFullWitness s pk)).isSome) true := by
  rw [publicPairWitness, PMF.map_comp]
  apply Cslib.Probability.PMF.map_true_mono
  intro r hr win
  obtain ⟨hpk, _⟩ := publicPairSigning_key_of_mem hr
  have accepted := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp win).1).1
  let f := r.trial.forgery
  change (H.verify s r.trial.publicKey f.message f.context f.signature).getD false at accepted
  rw [hpk] at accepted
  have good : H.verify s (encodePublic s rho.toList pk.t) f.message f.context f.signature =
      some true := by
    cases h : H.verify s (encodePublic s rho.toList pk.t) f.message f.context f.signature <;>
      simp_all
  obtain ⟨y, get, opened⟩ := opening_extractFull_of_verify hA good
  change ((H.extractFull s rho pk.A pk.t f).bind (H.openFullWitness s pk)).isSome
  rw [get, Option.bind_some, opened]
  rfl

/-- From the seeded ideal-mask signing hybrid to a short witness on the generated full pair.
The output checker recomputes the digest and the sparse challenge on the original raw oracles.
The additive event is a 64-byte hash match on a terminal signing request in that same run. -/
theorem freshMask_freshDigest_le_openFullWitness (C : QuantumSigningForger) (s : Level)
    (base : Xofs) (a b : ℕ) :
    Game.succProbability ((base.uniformPrefixes a b).bind fun H => H.keyExperiment s fun keys =>
      (C.freshMaskSigning s H keys).map (·.any fun r => r.trial.newDigestWin)) ≤
      Game.succProbability ((base.uniformPrefixes a b).bind fun H => H.fullPairExperiment s
        fun rho pk => (C.publicPairWitness s H rho pk).map fun o =>
          (o.bind (H.openFullWitness s pk)).isSome) +
      Game.succProbability ((base.uniformPrefixes a b).bind fun H => H.fullPairExperiment s
        fun rho pk => (C.publicPairSigning s H rho pk).map fun r => r.writes.any fun w =>
          let tr := H.h256.readBytes r.trial.publicKey 64
          let m := formatMessage w.request.message w.request.context
          H.h256.read (representativeInput tr m) 64 == tr) := by
  apply le_trans (C.freshMask_freshDigest_le_ambient s base a b)
  apply add_le_add
  swap
  · exact le_rfl
  apply ENNReal.toNNReal_mono (PMF.apply_ne_top _ _)
  apply Cslib.Probability.PMF.bind_apply_mono_on_support
  intro H _
  unfold Xofs.fullPairExperiment Xofs.keyExperiment
  apply Cslib.Probability.PMF.bind_apply_mono_on_support
  intro seed _
  cases h : H.keyGen s seed with
  | none => exact le_rfl
  | some keys =>
    obtain ⟨rho, sk, key, ha, _, hd, _, _⟩ := privateKey_of_keyGen h
    have seed_eq : (fun i : Fin 32 => rho.toList[i.val]!) = rho := by
      funext i
      simp only [FixedBytes.toList, List.length_ofFn, getElem!_pos, i.isLt, List.getElem_ofFn]
    simpa only [hd, ha, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.getD_some,
      seed_eq] using C.ambient_le_witness s H rho sk.publicKey ha

end QuantumSigningForger

end Cslib.Crypto.MLDSA.FIPS204
