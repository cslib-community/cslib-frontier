/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Computational.SchnorrProtocol
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.SchnorrSignature
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Probability.PMF
import CslibFrontier.Tactic.PPT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip

/-!
# Computational Schnorr signatures under the discrete-logarithm assumption

Schnorr's signature scheme ([Schnorr1991]; [BonehShoup2023], Sections 19.2–19.3) applies the
Fiat–Shamir transform ([FiatShamir1986]; [PointchevalStern2000]) to Schnorr's identification
protocol over a `PrimeOrderGroupFamily` `F`:

1. **Bit-encoded Schnorr signature operations and strict-PPT certificates**:
   * **Key generation** (`schnorrSigKeyGen`): at security parameter `n` and group description `d`,
     samples `sk ← F.sampleExp n d` (`ProbComp.sampleModNat`) and outputs the encoded public key
     `F.smul (d, sk, F.encode d (F.generator d))` (`encode (sk • g)`) and encoded secret key
     `(sk % F.order d).bits`. It is uniform strict PPT (`isPPTOn_schnorrSigKeyGen`) and within
     statistical distance `1 / 2 ^ n` of the ideal encoded Schnorr key generator
     (`closeTo_schnorrSigKeyGen`).
   * **Commitment, response, and signing** (`schnorrCommitBits`, `schnorrRespondBits`,
     `schnorrSignCoins`): given the description `d`, encoded secret key `sk`, message `msg`,
     commitment randomness `r`, and `k n`-bit random-oracle challenge `roOut`, computes the encoded
     commitment `t = r • g` and response `z = (r + roOut * sk) mod q`, both certified in
     `ComputableInPolyTime` and `IsPPTOn`.
   * **Verification and commitment recovery** (`schnorrSigVerifyBits`, `schnorrRecoverCommitBits`):
     compares the commitment word with the canonical recovery of `z • g - roOut • pk`.
     Under a canonical public key, acceptance forces a canonical commitment without a decoder.
     Both operations run in polynomial time (`computableInPolyTime_schnorrSigVerifyBits`,
     `computableInPolyTime_schnorrRecoverCommitBits`), with exact completeness on honest signatures
     (`schnorrSigVerifyBits_schnorrSignCoins`).

2. **The discrete-logarithm game in one group**: in `F.Carrier d`, the one-way game of the typed key
   generator `schnorrKeyGen (F.generator d)` is the exact discrete-logarithm experiment
   (`oneWayGame_schnorrKeyGen_eq`).

**Scope.** This module provides the algorithms and their certificates. EUF-CMA security of the
native scheme under `F.DiscreteLog`, for every oracle-PPT forger, is
`DiscreteLog.eufCma_schnorrNativeROMScheme` in
`CslibFrontier.Crypto.Computational.SchnorrSignature.Security`, through a certified native forking
reduction; that proof uses `oneWayGame_schnorrKeyGen_eq`. The concrete typed bound for any group,
challenge set and call-bounded forger is `schnorr_succProbability_eufCmaGame_le_ideal` in
`CslibFrontier.Crypto.Protocols.SigmaProtocol.SchnorrSignature`. Strict-PPT identification and
eavesdropping security under `F.DiscreteLog` are `negligible_schnorrDirectProbGame` and
`schnorr_isProbEavesdropSecure_of_discreteLogHard` in `SchnorrEavesdrop`.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrSignCoins`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrSigVerifyBits`: bit-encoded Schnorr signature
  signing and verification (built on `schnorrSigKeyGen`, `schnorrCommitBits`, `schnorrRespondBits`,
  `schnorrRecoverCommitBits`, and `encodeSchnorrVerify` from `SchnorrProtocol`).

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_schnorrSignCoins`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_schnorrSigVerifyBits`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrSigVerifyBits_schnorrSignCoins`: polynomial-time and
  strict-PPT certificates and completeness of the bit-encoded signature operations.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrSigVerifyBits_eq_true_iff`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrSigVerifyBits_commitment_mem_range`: acceptance under
  a canonical public key forces the exact recovered encoding, for arbitrary response and challenge
  words.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 19.2–19.3.
* [D. Pointcheval, J. Stern, *Security Arguments for Digital Signatures and Blind
  Signatures*][PointchevalStern2000].
* [C.-P. Schnorr, *Efficient Signature Generation by Smart Cards*][Schnorr1991].
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Protocols Protocols.SigmaProtocol Protocols.ROMSignature
  Interactive
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)

/-! ### 1. Bit-encoded Schnorr signature algorithms and strict-PPT certificates -/

/-- Deterministic bit-encoded Schnorr signing from explicit coins and a random-oracle challenge
([BonehShoup2023], Section 19.2): given `(d, sk, msg, r, roOut)` where `r` is the commitment
randomness and `roOut` is the random-oracle digest on `(msg, encode (r • g))`, output the encoded
signature `(t, z) = (schnorrCommitBits (d, r), schnorrRespondBits (d, sk, r, roOut))`.
This arithmetic kernel takes `roOut` as an input; its caller must obtain it from the shared hash
oracle. The message is not used again once that challenge has been supplied. -/
def schnorrSignCoins
    (input : F.Desc × List Bool × List Bool × List Bool × List Bool) : List Bool × List Bool :=
  let (d, sk, _msg, r, roOut) := input
  (F.schnorrCommitBits (d, r), F.schnorrRespondBits (d, sk, r, roOut))

/-- On encoded scalars `α, r : ZMod (F.order d)`, `schnorrSignCoins` outputs the encoded commitment
`r • g` and response `r + c * α`. -/
@[simp] theorem schnorrSignCoins_encScalar (d : F.Desc) (α r : ZMod (F.order d))
    (msg roOut : List Bool) :
    F.schnorrSignCoins (d, F.encScalar d α, msg, F.encScalar d r, roOut) =
      (F.encode d (r • F.generator d),
        F.encScalar d (r + (ofBits roOut : ZMod (F.order d)) * α)) := by
  simp only [schnorrSignCoins, schnorrCommitBits_encScalar, schnorrRespondBits_encScalar]

/-- **Deterministic bit-level Schnorr signing `schnorrSignCoins` is computable in polynomial
time**. -/
theorem computableInPolyTime_schnorrSignCoins :
    ComputableInPolyTime F.schnorrSignCoins
      (encPair F.encDesc (encPair encBits (encPair encBits (encPair encBits encBits))))
      (encPair encBits encBits) := by
  let encIn := encPair F.encDesc (encPair encBits (encPair encBits (encPair encBits encBits)))
  have hd : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool × List Bool => p.1)
      encIn F.encDesc := by fun_prop
  have hsk : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool × List Bool => p.2.1)
      encIn encBits := by fun_prop
  have hr : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool × List Bool => p.2.2.2.1)
      encIn encBits := by fun_prop
  have hro : ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool × List Bool => p.2.2.2.2)
      encIn encBits := by fun_prop
  have hcommit := F.computableInPolyTime_schnorrCommitBits.comp (hd.prod hr)
  have hresp := F.computableInPolyTime_schnorrRespondBits.comp (hd.prod (hsk.prod (hr.prod hro)))
  exact hcommit.prod hresp

/-- `schnorrSignCoins` lifted to `ProbComp` is uniform strict PPT. -/
theorem isPPTOn_schnorrSignCoins :
    IsPPTOn (encPair F.encDesc (encPair encBits (encPair encBits (encPair encBits encBits))))
      (encPair encBits encBits) (fun input => pure (F.schnorrSignCoins input)) :=
  F.computableInPolyTime_schnorrSignCoins.isPPTOn

/-- Bit-encoded Schnorr signature verification ([BonehShoup2023], Section 19.2): given
`(d, pk, msg, (t, z), roOut)` where `roOut` is the random-oracle challenge for `(msg, t)`, compare
`t` with the canonical encoding of `z • g - roOut • pk` via `encodeSchnorrVerify`. For a canonical
public key this rejects noncanonical commitments without requiring a group-membership decoder. This
checks the algebraic equation for a supplied challenge; the caller must enforce `roOut = H(msg, t)`
in the same oracle world used by the signer and adversary. -/
def schnorrSigVerifyBits
    (input : F.Desc × List Bool × List Bool × (List Bool × List Bool) × List Bool) : Bool :=
  let (d, pk, _msg, (t, z), roOut) := input
  F.encodeSchnorrVerify d pk t roOut z

/-- **Bit-level Schnorr signature verification `schnorrSigVerifyBits` is computable in polynomial
time**. -/
theorem computableInPolyTime_schnorrSigVerifyBits :
    ComputableInPolyTime F.schnorrSigVerifyBits
      (encPair F.encDesc
        (encPair encBits (encPair encBits (encPair (encPair encBits encBits) encBits))))
      encBool := by
  fun_prop [PrimeOrderGroupFamily.schnorrSigVerifyBits]

/-- `schnorrSigVerifyBits` lifted to `ProbComp` is uniform strict PPT. -/
theorem isPPTOn_schnorrSigVerifyBits :
    IsPPTOn
      (encPair F.encDesc
        (encPair encBits (encPair encBits (encPair (encPair encBits encBits) encBits))))
      encBool (fun input => pure (F.schnorrSigVerifyBits input)) :=
  F.computableInPolyTime_schnorrSigVerifyBits.isPPTOn

/-- On encoded group elements `pk = F.encode d u` and `t = F.encode d T`, `schnorrSigVerifyBits`
decides Schnorr's verification equation `z • g = T + c • u`. -/
theorem schnorrSigVerifyBits_encode (d : F.Desc) (u T : F.Carrier d)
    (msg z roOut : List Bool) :
    F.schnorrSigVerifyBits (d, F.encode d u, msg, (F.encode d T, z), roOut) =
      decide ((ofBits z : ZMod (F.order d)) • F.generator d =
        T + (ofBits roOut : ZMod (F.order d)) • u) := by
  simp only [schnorrSigVerifyBits, encodeSchnorrVerify_encode,
    (F.encode_injective d).eq_iff, eq_sub_iff_add_eq, eq_comm]

/-- **Completeness of bit-encoded Schnorr signing and verification**: every signature produced by
`schnorrSignCoins` on a key pair `(encode (α • g), encScalar α)` verifies under
`schnorrSigVerifyBits` with the same random-oracle challenge `roOut`. -/
theorem schnorrSigVerifyBits_schnorrSignCoins (d : F.Desc) (α r : ZMod (F.order d))
    (msg roOut : List Bool) :
    F.schnorrSigVerifyBits
      (d, F.encode d (α • F.generator d), msg,
        F.schnorrSignCoins (d, F.encScalar d α, msg, F.encScalar d r, roOut), roOut) =
      true := by
  rw [schnorrSignCoins_encScalar, schnorrSigVerifyBits_encode]
  simp only [encScalar, Function.Embedding.coeFn_mk, encNat_apply, ofBits_bits,
    ZMod.natCast_zmod_val, add_smul, mul_smul, decide_true]

/-- Verification compares the supplied commitment with public commitment recovery on all words,
including malformed inputs. -/
theorem schnorrSigVerifyBits_eq_decide_recover (d : F.Desc)
    (pk msg t z roOut : List Bool) :
    F.schnorrSigVerifyBits (d, pk, msg, (t, z), roOut) =
      decide (t = F.schnorrRecoverCommitBits (d, pk, roOut, z)) := by
  simp only [schnorrSigVerifyBits, encodeSchnorrVerify, beq_eq_decide]

/-- Under a canonical public key, acceptance forces the exact canonical recovered commitment.
The response and supplied challenge are arbitrary words, interpreted as scalars modulo the order.
No encoding-range conclusion is asserted for malformed public keys. -/
theorem schnorrSigVerifyBits_eq_true_iff (d : F.Desc) (u : F.Carrier d)
    (msg t z roOut : List Bool) :
    F.schnorrSigVerifyBits (d, F.encode d u, msg, (t, z), roOut) = true ↔
      t = F.encode d ((ofBits z : ZMod (F.order d)) • F.generator d -
        (ofBits roOut : ZMod (F.order d)) • u) :=
  F.encodeSchnorrVerify_eq_true_iff d u t roOut z

/-- Every accepted commitment is in the encoding range when the public key is canonical. -/
theorem schnorrSigVerifyBits_commitment_mem_range (d : F.Desc) (u : F.Carrier d)
    (msg t z roOut : List Bool)
    (h : F.schnorrSigVerifyBits (d, F.encode d u, msg, (t, z), roOut) = true) :
    t ∈ Set.range (F.encode d) := by
  exact ⟨_, ((F.schnorrSigVerifyBits_eq_true_iff d u msg t z roOut).mp h).symm⟩

/-! ### 2. The discrete-logarithm game in one group -/

/-- In `F.Carrier d`, the one-way game for `schnorrKeyGen (F.generator d)` is the exact
discrete-logarithm experiment: draw `α ← PMF.uniformOfFintype (ZMod (F.order d))`, run `B (α • g)`,
and accept when the output equals `α`. -/
theorem oneWayGame_schnorrKeyGen_eq (d : F.Desc) (B : F.Carrier d → PMF (ZMod (F.order d))) :
    oneWayGame (schnorrKeyGen (F.generator d)) (fun α u => α • F.generator d = u) B =
      (PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        (B (α • F.generator d)).map fun α' => decide (α' = α) := by
  simp only [oneWayGame, schnorrKeyGen, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_map, Function.comp_def, (F.smul_generator_injective d).eq_iff]
  rfl

end Cslib.Crypto.PrimeOrderGroupFamily
