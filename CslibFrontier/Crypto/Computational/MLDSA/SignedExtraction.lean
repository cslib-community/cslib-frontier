/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.AmbientVerification
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
  refine Cslib.Probability.PMF.map_true_mono _ fun r hr win => ?_
  obtain ⟨hpk, _⟩ := publicPairSigning_key_of_mem hr
  have accepted := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp win).1).1
  let f := r.trial.forgery
  change (H.verify s r.trial.publicKey f.message f.context f.signature).getD false at accepted
  rw [hpk] at accepted
  have good : H.verify s (encodePublic s rho.toList pk.t) f.message f.context f.signature =
      some true := by
    cases h : H.verify s (encodePublic s rho.toList pk.t) f.message f.context f.signature <;>
      simp_all
  obtain ⟨_, get, opened⟩ := opening_extractFull_of_verifyWithExpansion (pk := pk) hA good
  simp [Function.comp_apply, f, get, opened]

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
        fun rho pk => (C.publicPairSigning s H rho pk).map fun r =>
          H.terminalRepresentativeMatch r.trial.publicKey r.writes) := by
  refine (C.freshMask_freshDigest_le_ambient s base a b).trans
    (add_le_add_left (ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_) _)
  apply Cslib.Probability.PMF.bind_apply_mono_on_support
  intro H _
  unfold Xofs.fullPairExperiment Xofs.keyExperiment
  apply Cslib.Probability.PMF.bind_apply_mono_on_support
  intro seed _
  cases h : H.keyGen s seed with
  | none => exact le_rfl
  | some keys =>
    obtain ⟨rho, sk, ha, _, hd, _, _⟩ := privateKey_of_keyGen h
    have seed_eq : (fun i : Fin 32 => rho.toList[i.val]!) = rho := funext fun i => by
      simp only [FixedBytes.toList, List.length_ofFn, getElem!_pos, i.isLt, List.getElem_ofFn]
    simpa only [hd, ha, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.getD_some,
      seed_eq] using C.ambient_le_witness s H rho sk.publicKey ha

end QuantumSigningForger

end Cslib.Crypto.MLDSA.FIPS204
