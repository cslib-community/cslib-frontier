/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SchnorrProtocol
public import CslibFrontier.Computability.Interactive.Security.Repeat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Foundations.Data.ZMod.NatCast
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.Uniform.Translate
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PPT

/-!
# Direct and eavesdropping security of Schnorr identification in the strict-PPT model

In an eavesdropping attack on an identification scheme ([BonehShoup2023], Section 18.5, Attack
Game 18.2), the adversary first overhears `Q n` honest conversations between the prover and the
verifier for the public key `u = α • g` before attempting impersonation. For an idealized simulator
that samples `ZMod q` uniformly, special HVZK makes simulated conversations identically distributed
to honest ones ([BonehShoup2023], Theorems 19.3 and 19.5;
`schnorr_eavesdropAttack_eq_directAttack_ideal` in
`CslibFrontier.Crypto.Protocols.SigmaProtocol.SchnorrIdentification`).

In the uniform strict-PPT model, fair-coin machines with a fixed polynomial clock cannot sample
`ZMod q` exactly when the prime group order `q` is not a power of two. Instead, exponent sampling
uses `F.sampleExp n d` (`ProbComp.sampleModNat`), which is within statistical distance `1 / 2 ^ n`
of uniform on `ZMod q` (`closeTo_uniform_sampleExp`). Consequently:

* **Per-conversation statistical closeness**:
  * A strict-PPT simulated conversation `schnorrSimulatedTranscript` (using `schnorrSimulateWord` on
    the public key without the secret key) is within statistical distance (`CloseTo`)
    `1 / 2 ^ n` of an ideal honest conversation `schnorrHonestTranscript`
    (`closeTo_schnorrHonestTranscript_simulated`).
  * A strict-PPT honest conversation `schnorrRealTranscript` (where the honest prover also samples
    its commitment exponent with `sampleExp`) is within `1 / 2 ^ n` of `schnorrHonestTranscript`
    (`closeTo_schnorrRealTranscript_honest`) and hence within `2 / 2 ^ n` of
    `schnorrSimulatedTranscript` (`closeTo_schnorrRealTranscript_simulated`).
* **Multi-conversation statistical closeness**:
  * Across `Q` independent conversations over the infinite word space
    `List (List Bool × List Bool × List Bool)`, `CloseTo.iid`, `CloseTo.iid_replicate`, and
    `CloseTo.eval_replicate` bound the statistical distance by `Q / 2 ^ n` against ideal honest
    conversations (`closeTo_iid_schnorrHonestTranscript_replicate_simulated`) and by
    `2 * Q / 2 ^ n` against strict-PPT honest conversations
    (`closeTo_replicate_schnorrRealTranscript_simulated`).
* **Reduction to direct attacks and discrete logarithms**:
  * `SchnorrEavesdropAdversary.toDirect` converts any eavesdropping adversary `A` into a direct
    impersonator that generates `Q n` simulated conversations on the public key before running
    `A.commit`. It is uniform strict PPT whenever `A`, the challenge length `k`, and the
    conversation count `Q` are (`isPPT_toDirect`, `isPPTOn_rewind_toDirect`). It runs the generic
    reduction `SigmaProtocol.Impersonator.withSimulatedViews`: its typed view is that reduction
    applied to the typed view of `A`, with the law `schnorrSampledSimulate` of the strict-PPT
    simulator as the simulator, since `Q n` strict-PPT simulated conversations are `Q n` typed
    simulated conversations written as words (`eval_replicate_schnorrSimulatedTranscript`).
* **Native games and security under the discrete-logarithm assumption**:
  * `schnorrDirectProbGame` and `schnorrEavesdropProbGame` are the direct and eavesdropping attack
    games ([BonehShoup2023], Attack Games 18.1 and 18.2) with the native key generator
    `schnorrSigKeyGen` (from `SchnorrProtocol`), which samples the secret exponent with
    `F.sampleExp n d` and outputs the encoded public key with the binary secret key
    `(sk % F.order d).bits` (`isPPTOn_schnorrSigKeyGen`, `advantage_bind_schnorrSigKeyGen_le`).
    Their executable `ProbComp Bool` experiments `schnorrDirectProbExperiment` and
    `schnorrEavesdropProbExperiment` check acceptance with `encodeSchnorrVerify` and are certified
    `IsPPTOn` (`isPPTOn_schnorrDirectProbExperiment`, `isPPTOn_schnorrEavesdropProbExperiment`).
  * At each security parameter where every supported group has order at least `2 ^ k n`,
    `succProbability_schnorrDirectProbGame_le` and `succProbability_schnorrEavesdropProbGame_le`
    give the explicit bounds

      `ε ≤ 1 / 2 ^ n + 1 / 2 ^ k n + √ε'`   and   `ε ≤ (2 * Q n + 1) / 2 ^ n + 1 / 2 ^ k n + √ε'`,

    where `ε'` is the discrete-logarithm success probability of the rewinding adversary
    `A.rewind k` or `(A.toDirect k Q).rewind k`.
  * Under the discrete-logarithm assumption `F.DiscreteLog setup`, for any polynomial-time `k` and
    `Q` with negligible `1 / 2 ^ k n`, every uniform strict PPT impersonator and every uniform
    strict PPT eavesdropping adversary succeeds with negligible probability
    (`negligible_schnorrDirectProbGame`, [BonehShoup2023], Theorem 19.1;
    `negligible_schnorrEavesdropProbGame` and `schnorr_isProbEavesdropSecure_of_discreteLogHard`,
    Theorems 19.1 and 19.5 combined). Each applies the assumption to the rewinding adversary
    through `isPPTOn_rewind`.
* **Ideal-sampling steps**: the concrete bounds pass through the ideal-key games
  `schnorrDirectGame` and `schnorrEavesdropGame`, which draw the secret key with
  `PMF.uniformOfFintype` (`advantage_schnorrDirectProbGame_schnorrDirectGame_le`,
  `advantage_schnorrEavesdropProbGame_schnorrEavesdropGame_le`,
  `advantage_schnorrEavesdropGame_schnorrDirectGame_le` and
  `succProbability_schnorrDirectGame_le_ideal`). No theorem here states security of an ideal-key
  game.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.SchnorrEavesdropAdversary`,
  `Cslib.Crypto.PrimeOrderGroupFamily.SchnorrEavesdropAdversary.IsPPT`: two-stage eavesdropping
  adversaries and uniform strict PPT admissibility.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrHonestTranscript`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrRealTranscript`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrSimulatedTranscript`: ideal honest, strict-PPT honest,
  and strict-PPT simulated Schnorr conversations with `m`-bit challenges.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrSampledSimulate`,
  `Cslib.Crypto.PrimeOrderGroupFamily.transcriptWords`: the law of the strict-PPT simulator at a
  typed challenge, and the word view of a typed conversation.
* `Cslib.Crypto.PrimeOrderGroupFamily.SchnorrEavesdropAdversary.toDirect`: reduction from an
  eavesdropping adversary to a direct impersonator by simulating `Q n` conversations.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrDirectProbGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrDirectProbExperiment`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrEavesdropProbGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorrEavesdropProbExperiment`: native direct and
  eavesdropping games and experiments using `schnorrSigKeyGen` and `encodeSchnorrVerify`.
* `Cslib.Crypto.PrimeOrderGroupFamily.IsProbEavesdropSecure`: security against all uniform strict
  PPT eavesdropping adversaries for all polynomial-time conversation counts.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrEavesdropGame`: the eavesdropping game with an ideal
  key, an intermediate game of the reduction.

## Main results

* `Cslib.Probability.CloseTo.iid`, `Cslib.Probability.CloseTo.iid_replicate`,
  `Cslib.Probability.CloseTo.eval_replicate`: statistical closeness of `k` independent draws and
  `OracleComp.replicate` runs without finiteness assumptions.
* `Cslib.Crypto.PrimeOrderGroupFamily.closeTo_schnorrRealTranscript_honest`,
  `Cslib.Crypto.PrimeOrderGroupFamily.closeTo_schnorrHonestTranscript_simulated`,
  `Cslib.Crypto.PrimeOrderGroupFamily.closeTo_schnorrRealTranscript_simulated`: per-conversation
  statistical closeness (`1 / 2 ^ n` and `2 / 2 ^ n`).
* `Cslib.Crypto.PrimeOrderGroupFamily.closeTo_iid_schnorrHonestTranscript_replicate_simulated`,
  `Cslib.Crypto.PrimeOrderGroupFamily.closeTo_replicate_schnorrRealTranscript_simulated`:
  `Q`-conversation statistical closeness (`Q / 2 ^ n` and `2 * Q / 2 ^ n`).
* `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_schnorrRealTranscript`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_schnorrSimulatedTranscript`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_toDirect`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_rewind_toDirect`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_schnorrDirectProbExperiment`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_schnorrEavesdropProbExperiment`: strict-PPT
  certificates for conversation generation, the direct-attack reduction, the composed rewinding DL
  adversary, and the executable direct and eavesdropping experiments.
* `Cslib.Crypto.PrimeOrderGroupFamily.succProbability_schnorrDirectProbGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.succProbability_schnorrEavesdropProbGame_le`: concrete
  direct-to-DL and eavesdropping-to-DL bounds for the native games.
* `Cslib.Crypto.PrimeOrderGroupFamily.negligible_schnorrDirectProbGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.negligible_schnorrEavesdropProbGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.schnorr_isProbEavesdropSecure_of_discreteLogHard`:
  direct and eavesdropping security of Schnorr identification under the discrete-logarithm
  assumption ([BonehShoup2023], Theorem 19.1, and Theorems 19.1 and 19.5 combined).

## Ideal-sampling steps

* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_schnorrDirectProbGame_schnorrDirectGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_schnorrEavesdropProbGame_schnorrEavesdropGame_le`:
  the native key generator is within `1 / 2 ^ n` of the ideal key.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_schnorrEavesdropGame_schnorrDirectGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_schnorrEavesdropProbGame_schnorrDirectGame_le`:
  simulating the overheard conversations changes the advantage by at most `2 * Q n / 2 ^ n`, or
  `(2 * Q n + 1) / 2 ^ n` from the native game.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 18.3, 18.5 and 19.1 (Attack Games 18.1 and 18.2,
  Definition 18.6, and Theorems 19.1, 19.3 and 19.5).
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Theorem 13.2.
* [C.-P. Schnorr, *Efficient Signature Generation by Smart Cards*][Schnorr1991]
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Protocols Interactive
open scoped ENNReal NNReal

variable {F : PrimeOrderGroupFamily}

/-- Encoding of a single Schnorr conversation `(t, c, z)` of bit words. -/
abbrev encTranscript : (List Bool × List Bool × List Bool) ↪ List Bool :=
  encPair encBits (encPair encBits encBits)

/-- The word view of a typed conversation `(t, c, z)`: the challenge as its list of bits. -/
@[expose] def transcriptWords {m : ℕ} :
    List Bool × BitString m × List Bool → List Bool × List Bool × List Bool
  | (t, c, z) => (t, List.ofFn c, z)

variable (F) in
/-- A uniform eavesdropping adversary against Schnorr identification ([BonehShoup2023], Attack
Game 18.2). Its first stage sees the security parameter, the group description, the encoded public
key, and a list of overheard conversations `(t, c, z)`, and returns a commitment word and a state
word; its second stage sees the security parameter, the state and the challenge word. -/
structure SchnorrEavesdropAdversary where
  /-- Commit from the group description, encoded public key and overheard conversations, keeping a
  state word. -/
  commit : ℕ → F.Desc × List Bool × List (List Bool × List Bool × List Bool) →
    ProbComp (List Bool × List Bool)
  /-- Respond to a challenge word from the state word. -/
  respond : ℕ → List Bool × List Bool → ProbComp (List Bool)

/-- Both stages of an eavesdropping adversary are uniform strict PPT in their whole inputs. -/
@[expose] def SchnorrEavesdropAdversary.IsPPT (A : F.SchnorrEavesdropAdversary) : Prop :=
  IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encList encTranscript))))
      (encPair encBits encBits) (fun input => A.commit input.1 input.2) ∧
    IsPPTOn (encPair encUnary (encPair encBits encBits)) encBits
      (fun input => A.respond input.1 input.2)

/-! ### Ideal honest, strict-PPT honest, and strict-PPT simulated conversations -/

variable (F) in
/-- An ideal honest Schnorr conversation with an `m`-bit challenge ([BonehShoup2023], Section 19.1):
sample a uniform commitment exponent `r : ZMod (F.order d)` and a uniform `m`-bit challenge `c`,
and output the encoded commitment `r • g`, the challenge `c`, and the binary response
`(r + c * α).val.bits`. -/
noncomputable def schnorrHonestTranscript (d : F.Desc) (α : ZMod (F.order d)) (m : ℕ) :
    PMF (List Bool × List Bool × List Bool) := do
  let r ← PMF.uniformOfFintype (ZMod (F.order d))
  let c ← BitString.uniformList m
  return (F.encode d (r • F.generator d), c,
    (r + (ofBits c : ZMod (F.order d)) * α).val.bits)

variable (F) in
/-- A strict-PPT honest Schnorr conversation at security parameter `n` with an `m`-bit challenge:
sample the commitment exponent `r` with `F.sampleExp n d` and the challenge `c` with
`BitString.sampleList m`, and output `(encode (r • g), c, ((r + ofBits c * α) % q).bits)`. -/
noncomputable def schnorrRealTranscript (n : ℕ) (d : F.Desc) (α : ZMod (F.order d)) (m : ℕ) :
    ProbComp (List Bool × List Bool × List Bool) := do
  let r ← F.sampleExp n d
  let c ← BitString.sampleList m
  return (F.smul (d, r, F.encode d (F.generator d)), c,
    ((r + ofBits c * α.val) % F.order d).bits)

variable (F) in
/-- A strict-PPT simulated Schnorr conversation at security parameter `n` with an `m`-bit
challenge ([BonehShoup2023], Example 19.3 and Theorem 19.3): sample a uniform `m`-bit challenge `c`
and run `F.schnorrSimulateWord ((n, d), u, c)` on the encoded public key `u` to obtain `(t, z)`,
returning `(t, c, z)` without using the secret key. -/
noncomputable def schnorrSimulatedTranscript (n : ℕ) (d : F.Desc) (u : List Bool) (m : ℕ) :
    ProbComp (List Bool × List Bool × List Bool) := do
  let c ← BitString.sampleList m
  let tz ← F.schnorrSimulateWord ((n, d), u, c)
  return (tz.1, c, tz.2)

/-! ### Statistical closeness of single and repeated conversations -/

private theorem eval_schnorrRealTranscript (n : ℕ) (d : F.Desc) (α : ZMod (F.order d)) (m : ℕ) :
    ProbComp.eval (F.schnorrRealTranscript n d α m) =
      ((ProbComp.eval (F.sampleExp n d)).map (Nat.cast : ℕ → ZMod (F.order d))).bind fun r =>
        (BitString.uniformList m).map fun c =>
          (F.encode d (r • F.generator d), c,
            (r + (ofBits c : ZMod (F.order d)) * α).val.bits) := by
  have hresp (r : ℕ) (c : List Bool) :
      (r + ofBits c * α.val) % F.order d =
        ((r : ZMod (F.order d)) + (ofBits c : ZMod (F.order d)) * α).val := by
    rw [← ZMod.val_natCast (F.order d), Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
  simp only [pmf_norm, schnorrRealTranscript, BitString.eval_sampleList, F.smul_encode, hresp]
  refine congrArg (PMF.bind _) (funext fun r => ?_)
  rw [← PMF.bind_pure_comp]
  rfl

private theorem eval_schnorrSimulateWord_bits (n : ℕ) (d : F.Desc) (u : F.Carrier d)
    (c : List Bool) :
    ProbComp.eval (F.schnorrSimulateWord ((n, d), F.encode d u, c)) =
      ((ProbComp.eval (F.sampleExp n d)).map (Nat.cast : ℕ → ZMod (F.order d))).map
        fun z => (F.encode d (z • F.generator d - (ofBits c : ZMod (F.order d)) • u),
          z.val.bits) := by
  rw [schnorrSimulateWord, ProbComp.eval_bind, PMF.map_comp]
  simp only [ProbComp.eval_pure, F.smul_encode, F.add_encode, ZMod.natCast_sub_mod_eq_neg,
    neg_smul, ← sub_eq_add_neg]
  rw [← PMF.bind_pure_comp]
  congr 1 with a : 1
  simp only [Function.comp_apply, ZMod.val_natCast]

/-- The law of one strict-PPT simulated conversation on a canonical public key `encode u`: a
uniform `m`-bit challenge `c`, a sampled scalar response `z`, and the commitment
`encode (z • g - c • u)`. -/
theorem eval_schnorrSimulatedTranscript (n : ℕ) (d : F.Desc) (u : F.Carrier d) (m : ℕ) :
    ProbComp.eval (F.schnorrSimulatedTranscript n d (F.encode d u) m) =
      (BitString.uniformList m).bind fun c =>
        ((ProbComp.eval (F.sampleExp n d)).map (Nat.cast : ℕ → ZMod (F.order d))).map
          fun z => (F.encode d (z • F.generator d - (ofBits c : ZMod (F.order d)) • u),
            c, z.val.bits) := by
  rw [schnorrSimulatedTranscript, ProbComp.eval_bind, BitString.eval_sampleList]
  refine congrArg (PMF.bind _) (funext fun c => ?_)
  rw [ProbComp.eval_bind, eval_schnorrSimulateWord_bits, PMF.bind_map, ← PMF.bind_pure_comp]
  rfl

/-- The law of the strict-PPT Schnorr simulator at a typed challenge: a sampled scalar response `z`
and the commitment `z • g - c • u`, with the challenge read as a binary number. -/
@[expose] noncomputable def schnorrSampledSimulate (n : ℕ) (d : F.Desc) {m : ℕ} (u : F.Carrier d)
    (c : BitString m) : PMF (List Bool × List Bool) :=
  ((ProbComp.eval (F.sampleExp n d)).map (Nat.cast : ℕ → ZMod (F.order d))).map fun z =>
    (F.encode d (z • F.generator d - (ofBits (List.ofFn c) : ZMod (F.order d)) • u), z.val.bits)

/-- A strict-PPT simulated transcript is a typed simulated conversation, written as words. -/
theorem eval_schnorrSimulatedTranscript_eq_map (n : ℕ) (d : F.Desc) (m : ℕ) (u : F.Carrier d) :
    ProbComp.eval (F.schnorrSimulatedTranscript n d (F.encode d u) m) =
      (SigmaProtocol.simulateConversation (schnorrSampledSimulate n d (m := m)) u).map
        transcriptWords := by
  rw [eval_schnorrSimulatedTranscript, BitString.uniformList, PMF.bind_map]
  simp only [SigmaProtocol.simulateConversation, schnorrSampledSimulate, pmf_norm]
  congr 1 with c : 1

/-- `k` strict-PPT simulated transcripts are `k` typed simulated conversations, written as
words. -/
theorem eval_replicate_schnorrSimulatedTranscript (n : ℕ) (d : F.Desc) (m k : ℕ)
    (u : F.Carrier d) :
    ProbComp.eval (OracleComp.replicate k (F.schnorrSimulatedTranscript n d (F.encode d u) m)) =
      (PMF.iid (SigmaProtocol.simulateConversation (schnorrSampledSimulate n d (m := m)) u) k).map
        fun transcripts => (List.ofFn transcripts).map transcriptWords := by
  rw [ProbComp.eval_replicate_iid, eval_schnorrSimulatedTranscript_eq_map, PMF.iid_map,
    PMF.map_comp]
  congr 1 with transcripts : 1
  simp [List.map_ofFn, Function.comp_def]

private theorem schnorrHonestTranscript_eq_bind_uniform (d : F.Desc) (α : ZMod (F.order d))
    (m : ℕ) :
    F.schnorrHonestTranscript d α m =
      (BitString.uniformList m).bind fun c =>
        (PMF.uniformOfFintype (ZMod (F.order d))).map fun z =>
          (F.encode d (z • F.generator d - (ofBits c : ZMod (F.order d)) • (α • F.generator d)),
            c, z.val.bits) := by
  simp only [schnorrHonestTranscript, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rw [PMF.bind_comm]
  refine congrArg (PMF.bind _) (funext fun c => ?_)
  conv_lhs =>
    rw [← PMF.uniformOfFintype_map_sub_right ((ofBits c : ZMod (F.order d)) * α)]
  rw [PMF.bind_map, ← PMF.bind_pure_comp]
  congr 1 with z : 1
  simp only [Function.comp_apply, sub_smul, mul_smul, sub_add_cancel]

variable (F) in
/-- A strict-PPT honest Schnorr conversation is within statistical distance `1 / 2 ^ n` of an ideal
honest conversation. -/
theorem closeTo_schnorrRealTranscript_honest (n : ℕ) (d : F.Desc)
    (α : ZMod (F.order d)) (m : ℕ) :
    CloseTo (ProbComp.eval (F.schnorrRealTranscript n d α m))
      (F.schnorrHonestTranscript d α m) (1 / 2 ^ n : ℝ≥0) := by
  rw [eval_schnorrRealTranscript, schnorrHonestTranscript]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, ← PMF.bind_pure_comp]
  exact (F.closeTo_uniform_sampleExp n d).symm.bind_left _

variable (F) in
/-- An ideal honest Schnorr conversation is within statistical distance `1 / 2 ^ n` of a strict-PPT
simulated conversation on the public key `encode (α • g)`. -/
theorem closeTo_schnorrHonestTranscript_simulated (n : ℕ) (d : F.Desc)
    (α : ZMod (F.order d)) (m : ℕ) :
    CloseTo (F.schnorrHonestTranscript d α m)
      (ProbComp.eval (F.schnorrSimulatedTranscript n d (F.encode d (α • F.generator d)) m))
      (1 / 2 ^ n : ℝ≥0) := by
  rw [schnorrHonestTranscript_eq_bind_uniform, eval_schnorrSimulatedTranscript]
  exact CloseTo.bind_right (BitString.uniformList m) fun c _ =>
    (F.closeTo_uniform_sampleExp n d).map _

variable (F) in
/-- A strict-PPT honest Schnorr conversation is within statistical distance `2 / 2 ^ n` of a
strict-PPT simulated conversation on the public key `encode (α • g)`. -/
theorem closeTo_schnorrRealTranscript_simulated (n : ℕ) (d : F.Desc)
    (α : ZMod (F.order d)) (m : ℕ) :
    CloseTo (ProbComp.eval (F.schnorrRealTranscript n d α m))
      (ProbComp.eval (F.schnorrSimulatedTranscript n d (F.encode d (α • F.generator d)) m))
      (2 / 2 ^ n : ℝ≥0) := by
  convert (F.closeTo_schnorrRealTranscript_honest n d α m).trans
    (F.closeTo_schnorrHonestTranscript_simulated n d α m) using 1
  rw [← ENNReal.coe_add]
  congr 1
  ring

variable (F) in
/-- `Q` independent ideal honest Schnorr conversations are within statistical distance `Q / 2 ^ n`
of `Q` strict-PPT simulated conversations on the public key `encode (α • g)`. -/
theorem closeTo_iid_schnorrHonestTranscript_replicate_simulated (n : ℕ) (d : F.Desc)
    (α : ZMod (F.order d)) (m Q : ℕ) :
    CloseTo ((PMF.iid (F.schnorrHonestTranscript d α m) Q).map List.ofFn)
      (ProbComp.eval (OracleComp.replicate Q
        (F.schnorrSimulatedTranscript n d (F.encode d (α • F.generator d)) m)))
      (Q / 2 ^ n : ℝ≥0) := by
  convert (F.closeTo_schnorrHonestTranscript_simulated n d α m).iid_replicate Q using 1
  rw [← ENNReal.coe_natCast, ← ENNReal.coe_mul, mul_one_div]

variable (F) in
/-- `Q` independent strict-PPT honest Schnorr conversations are within statistical distance
`2 * Q / 2 ^ n` of `Q` strict-PPT simulated conversations on the public key `encode (α • g)`. -/
theorem closeTo_replicate_schnorrRealTranscript_simulated (n : ℕ) (d : F.Desc)
    (α : ZMod (F.order d)) (m Q : ℕ) :
    CloseTo
      (ProbComp.eval (OracleComp.replicate Q (F.schnorrRealTranscript n d α m)))
      (ProbComp.eval (OracleComp.replicate Q
        (F.schnorrSimulatedTranscript n d (F.encode d (α • F.generator d)) m)))
      (2 * Q / 2 ^ n : ℝ≥0) := by
  convert (F.closeTo_schnorrRealTranscript_simulated n d α m).eval_replicate Q using 1
  rw [← ENNReal.coe_natCast, ← ENNReal.coe_mul]
  congr 1
  ring

/-! ### Eavesdropping games and reduction to direct attacks -/

variable (F) in
/-- The eavesdropping impersonation attack on Schnorr identification ([BonehShoup2023], Attack
Game 18.2) with an ideal key: the secret key is drawn with `PMF.uniformOfFintype`, which a strict
PPT machine cannot do. Before committing, the adversary overhears `Q n` independent conversations
generated by the strict-PPT honest prover (`schnorrRealTranscript`) with `k n`-bit challenges. This
game is the intermediate step between `schnorrEavesdropProbGame`, with the native key generator,
and the direct attack `schnorrDirectGame`. -/
noncomputable def schnorrEavesdropGame (setup : ℕ → PMF F.Desc) (k Q : ℕ → ℕ)
    (A : F.SchnorrEavesdropAdversary) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let views ← ProbComp.eval (OracleComp.replicate (Q n) (F.schnorrRealTranscript n d α (k n)))
  let ts ← ProbComp.eval (A.commit n (d, F.encode d (α • F.generator d), views))
  let c ← BitString.uniformList (k n)
  let z ← ProbComp.eval (A.respond n (ts.2, c))
  return decide (ts.1 = F.encode d ((ofBits z : ZMod (F.order d)) • F.generator d -
    (ofBits c : ZMod (F.order d)) • (α • F.generator d)))

/-- Turn an eavesdropping adversary into a direct impersonator ([BonehShoup2023], Theorem 19.3 and
Figure 19.2): before committing, simulate `Q n` conversations on the public key using
`schnorrSimulatedTranscript`. -/
noncomputable def SchnorrEavesdropAdversary.toDirect (k Q : ℕ → ℕ)
    (A : F.SchnorrEavesdropAdversary) : F.SchnorrImpersonator where
  commit n := fun (d, u) => do
    let views ← OracleComp.replicate (Q n) (F.schnorrSimulatedTranscript n d u (k n))
    A.commit n (d, u, views)
  respond := A.respond

/-- The typed view of an eavesdropping adversary at security parameter `n`, with `m`-bit challenges
and `Q` overheard conversations. Like `SchnorrImpersonator.typed`, it sees the statement encoded
and the challenge as a word; it also reads each typed conversation as words (`transcriptWords`). -/
private noncomputable def SchnorrEavesdropAdversary.typed (A : F.SchnorrEavesdropAdversary)
    (n m Q : ℕ) :
    SigmaProtocol.Impersonator (((d : F.Desc) × F.Carrier d) ×
      (Fin Q → List Bool × BitString m × List Bool)) (List Bool) (BitString m) (List Bool) where
  State := List Bool
  commit := fun (y, views) =>
    ProbComp.eval (A.commit n (y.1, F.encode y.1 y.2, (List.ofFn views).map transcriptWords))
  respond s c := ProbComp.eval (A.respond n (s, List.ofFn c))

/-- The word reduction `A.toDirect k Q` runs the generic reduction `withSimulatedViews`: at each
security parameter `n`, its typed view is that reduction applied to the typed view of `A`, with the
law of the strict-PPT simulator (`schnorrSampledSimulate`) as the simulator. -/
private theorem SchnorrEavesdropAdversary.typed_toDirect (k Q : ℕ → ℕ)
    (A : F.SchnorrEavesdropAdversary) (n : ℕ) :
    (A.toDirect k Q).typed n (k n) =
      (A.typed n (k n) (Q n)).withSimulatedViews fun y => schnorrSampledSimulate n y.1 y.2 := by
  simp only [SchnorrImpersonator.typed, SigmaProtocol.Impersonator.withSimulatedViews,
    SchnorrEavesdropAdversary.typed, SchnorrEavesdropAdversary.toDirect]
  congr 1
  funext y
  rw [ProbComp.eval_bind, eval_replicate_schnorrSimulatedTranscript, PMF.bind_map]
  rfl

/-- Ideal-sampling step: in the ideal-key games, replacing `Q n` strict-PPT honest conversations by
strict-PPT simulated ones changes the game advantage by at most `2 * Q n / 2 ^ n`. -/
theorem advantage_schnorrEavesdropGame_schnorrDirectGame_le
    (setup : ℕ → PMF F.Desc) (k Q : ℕ → ℕ) (A : F.SchnorrEavesdropAdversary) (n : ℕ) :
    Game.advantage (F.schnorrEavesdropGame setup k Q A n)
      (F.schnorrDirectGame setup k (A.toDirect k Q) n) ≤ 2 * Q n / 2 ^ n := by
  simp only [pmf_norm, schnorrEavesdropGame, schnorrDirectGame, SchnorrEavesdropAdversary.toDirect]
  refine Game.advantage_bind_le_nnreal (setup n) _ _ fun d => ?_
  refine Game.advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _ fun α => ?_
  exact Game.advantage_bind_le_of_closeTo
    (F.closeTo_replicate_schnorrRealTranscript_simulated n d α (k n) (Q n)) _

/-! ### Efficiency of conversation generation and the eavesdropping reduction -/

/-- `schnorrRealTranscript` is uniform strict PPT when the security parameter, group description,
secret exponent, and challenge length are computable in polynomial time. -/
theorem isPPTOn_schnorrRealTranscript {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {d : γ → F.Desc} {α : γ → ℕ} {m : γ → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hd : ComputableInPolyTime d encIn F.encDesc)
    (hα : ComputableInPolyTime α encIn encNat)
    (hm : ComputableInPolyTime m encIn encUnary) :
    IsPPTOn encIn encTranscript
      (fun a => F.schnorrRealTranscript (n a) (d a) (α a) (m a)) := by
  have hα_val (a : γ) : ((α a : ZMod (F.order (d a)))).val = α a % F.order (d a) :=
    ZMod.val_natCast (F.order (d a)) (α a)
  unfold schnorrRealTranscript
  simp only [hα_val]
  refine (F.isPPTOn_sampleExp hn hd).bind_with ?_
  have hm' : ComputableInPolyTime (fun p : γ × ℕ => m p.1) (encPair encIn encNat) encUnary :=
    hm.comp (by fun_prop)
  refine hm'.sampleList.bind_with ?_
  let encMid := encPair (encPair encIn encNat) encBits
  have hd' : ComputableInPolyTime (fun p : (γ × ℕ) × List Bool => d p.1.1) encMid F.encDesc :=
    hd.comp (by fun_prop)
  have hα' : ComputableInPolyTime (fun p : (γ × ℕ) × List Bool => α p.1.1) encMid encNat :=
    hα.comp (by fun_prop)
  have hr : ComputableInPolyTime (fun p : (γ × ℕ) × List Bool => p.1.2) encMid encNat := by
    fun_prop
  have hc : ComputableInPolyTime (fun p : (γ × ℕ) × List Bool => p.2) encMid encBits := by
    fun_prop
  have hq := F.computableInPolyTime_order.comp hd'
  have hg := F.computableInPolyTime_generator.comp hd'
  have ht := F.computableInPolyTime_smul.comp (hd'.prod (hr.prod hg))
  have hc_nat : ComputableInPolyTime (fun p : (γ × ℕ) × List Bool => ofBits p.2)
      encMid encNat :=
    ComputableInPolyTime.bitsToNat.comp hc
  have hz : ComputableInPolyTime
      (fun p : (γ × ℕ) × List Bool =>
        ((p.1.2 + ofBits p.2 * (α p.1.1 % F.order (d p.1.1))) % F.order (d p.1.1)).bits)
      encMid encBits :=
    (ComputableInPolyTime.binary_mod'
      (.binary_add' hr (.binary_mul' hc_nat (.binary_mod' hα' hq))) hq).of_enc_eq
        fun _ => rfl
  exact (ht.prod (hc.prod hz)).isPPTOn

/-- `schnorrSimulatedTranscript` is uniform strict PPT when the security parameter, group
description, encoded public key, and challenge length are computable in polynomial time. -/
theorem isPPTOn_schnorrSimulatedTranscript {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {d : γ → F.Desc} {u : γ → List Bool} {m : γ → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hd : ComputableInPolyTime d encIn F.encDesc)
    (hu : ComputableInPolyTime u encIn encBits)
    (hm : ComputableInPolyTime m encIn encUnary) :
    IsPPTOn encIn encTranscript
      (fun a => F.schnorrSimulatedTranscript (n a) (d a) (u a) (m a)) := by
  unfold schnorrSimulatedTranscript
  refine hm.sampleList.bind_with ?_
  refine (F.isPPTOn_schnorrSimulateWord.preprocess
    (prepare := fun p : γ × List Bool => ((n p.1, d p.1), u p.1, p.2))
    (by fun_prop)).bind_with ?_
  exact ComputableInPolyTime.isPPTOn (by fun_prop)

/-- **The direct impersonator `A.toDirect k Q` is uniform strict PPT** when the eavesdropping
adversary `A` is and both `k` and `Q` are computable in polynomial time. -/
theorem isPPT_toDirect {k Q : ℕ → ℕ}
    (hk : ComputableInPolyTime k encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    {A : F.SchnorrEavesdropAdversary} (hA : A.IsPPT) :
    (A.toDirect k Q).IsPPT := by
  refine ⟨?_, hA.2⟩
  let encIn := encPair encUnary (encPair F.encDesc encBits)
  have hrep : IsPPTOn encIn (encList encTranscript)
      (fun p : ℕ × F.Desc × List Bool =>
        OracleComp.replicate (Q p.1)
          (F.schnorrSimulatedTranscript p.1 p.2.1 p.2.2 (k p.1))) :=
    (F.isPPTOn_schnorrSimulatedTranscript
      (by fun_prop)
      (by fun_prop)
      (by fun_prop)
      (by fun_prop)).replicate (by fun_prop)
  exact hrep.bind_with (hA.1.preprocess
    (prepare := fun p : (ℕ × F.Desc × List Bool) × List (List Bool × List Bool × List Bool) =>
      (p.1.1, (p.1.2.1, p.1.2.2, p.2))) (by fun_prop))

/-- **The rewinding discrete-logarithm adversary built from an eavesdropper is uniform strict PPT**
when the eavesdropper is and `k` and `Q` are computable in polynomial time. -/
theorem isPPTOn_rewind_toDirect {k Q : ℕ → ℕ}
    (hk : ComputableInPolyTime k encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    {A : F.SchnorrEavesdropAdversary} (hA : A.IsPPT) :
    IsPPTOn (encPair encUnary (encPair F.encDesc encBits)) encBits
      (fun input => (A.toDirect k Q).rewind k input.1 input.2) :=
  isPPTOn_rewind hk (isPPT_toDirect hk hQ hA)

/-! ### Native games and security under the discrete-logarithm assumption -/

variable (F) in
/-- The direct impersonation attack on Schnorr identification ([BonehShoup2023], Attack Game 18.1)
with `k n`-bit challenges and the native key generator: the key pair comes from
`F.schnorrSigKeyGen n d`, whose exponent `F.sampleExp n d` is within statistical distance
`1 / 2 ^ n` of uniform on `ZMod (F.order d)`. The verifier accepts when the commitment encodes
`z • g - c • u`. -/
noncomputable def schnorrDirectProbGame (setup : ℕ → PMF F.Desc) (k : ℕ → ℕ)
    (A : F.SchnorrImpersonator) (n : ℕ) : Game := do
  let d ← setup n
  let (pk, sk) ← ProbComp.eval (F.schnorrSigKeyGen n d)
  let ts ← ProbComp.eval (A.commit n (d, pk))
  let c ← BitString.uniformList (k n)
  let z ← ProbComp.eval (A.respond n (ts.2, c))
  return decide (ts.1 = F.encode d ((ofBits z : ZMod (F.order d)) • F.generator d -
    (ofBits c : ZMod (F.order d)) • ((ofBits sk : ZMod (F.order d)) • F.generator d)))

variable (F) in
/-- Executable `ProbComp Bool` direct impersonation experiment at group description `d`: sample
the key pair with `schnorrSigKeyGen n d`, run `A.commit`, sample `c ← BitString.sampleList (k n)`,
run `A.respond`, and check acceptance with `encodeSchnorrVerify`. -/
noncomputable def schnorrDirectProbExperiment (k : ℕ → ℕ) (A : F.SchnorrImpersonator)
    (n : ℕ) (d : F.Desc) : ProbComp Bool := do
  let (pk, _) ← F.schnorrSigKeyGen n d
  let ts ← A.commit n (d, pk)
  let c ← BitString.sampleList (k n)
  let z ← A.respond n (ts.2, c)
  return F.encodeSchnorrVerify d pk ts.1 c z

/-- Averaging `schnorrDirectProbExperiment` over `d ← setup n` yields `schnorrDirectProbGame`. -/
theorem bind_eval_schnorrDirectProbExperiment (setup : ℕ → PMF F.Desc) (k : ℕ → ℕ)
    (A : F.SchnorrImpersonator) (n : ℕ) :
    ((setup n).bind fun d => ProbComp.eval (F.schnorrDirectProbExperiment k A n d)) =
      F.schnorrDirectProbGame setup k A n := by
  simp only [schnorrDirectProbExperiment, schnorrDirectProbGame, schnorrSigKeyGen,
    BitString.eval_sampleList, F.smul_encode, F.encodeSchnorrVerify_encode, ofBits_bits,
    ZMod.natCast_mod, pmf_norm]

/-- `schnorrDirectProbExperiment` is uniformly strict PPT in `(n, d)` whenever `k` is computable in
polynomial time and `A` is a uniform strict PPT `SchnorrImpersonator`. -/
theorem isPPTOn_schnorrDirectProbExperiment {k : ℕ → ℕ}
    (hk : ComputableInPolyTime k encUnary encUnary)
    {A : F.SchnorrImpersonator} (hA : A.IsPPT) :
    IsPPTOn (encPair encUnary F.encDesc) encBool
      (fun p : ℕ × F.Desc => F.schnorrDirectProbExperiment k A p.1 p.2) := by
  let E0 := encPair encUnary F.encDesc
  let E1 := encPair E0 (encPair encBits encBits)
  let E2 := encPair E1 (encPair encBits encBits)
  let E3 := encPair E2 encBits
  let E4 := encPair E3 encBits
  have hk_t := hk
  have hcommit : IsPPTOn E1 (encPair encBits encBits)
      (fun p : (ℕ × F.Desc) × (List Bool × List Bool) => A.commit p.1.1 (p.1.2, p.2.1)) :=
    hA.1.preprocess
      (prepare := fun p : (ℕ × F.Desc) × (List Bool × List Bool) => (p.1.1, (p.1.2, p.2.1)))
      (by fun_prop)
  have hchal : IsPPTOn E2 encBits
      (fun q : ((ℕ × F.Desc) × (List Bool × List Bool)) × (List Bool × List Bool) =>
        BitString.sampleList (k q.1.1.1)) :=
    ComputableInPolyTime.sampleList (by fun_prop)
  have hresp : IsPPTOn E3 encBits
      (fun r : (((ℕ × F.Desc) × (List Bool × List Bool)) × (List Bool × List Bool)) × List Bool =>
        A.respond r.1.1.1.1 (r.1.2.2, r.2)) :=
    hA.2.preprocess
      (prepare := fun r : (((ℕ × F.Desc) × (List Bool × List Bool)) × (List Bool × List Bool)) ×
          List Bool =>
        (r.1.1.1.1, (r.1.2.2, r.2)))
      (by fun_prop)
  have hver : ComputableInPolyTime
      (fun s : ((((ℕ × F.Desc) × (List Bool × List Bool)) × (List Bool × List Bool)) × List Bool) ×
          List Bool =>
        F.encodeSchnorrVerify s.1.1.1.1.2 s.1.1.1.2.1 s.1.1.2.1 s.1.2 s.2)
      E4 encBool := by
    fun_prop
  unfold schnorrDirectProbExperiment
  exact F.isPPTOn_schnorrSigKeyGen.bind_with
    (hcommit.bind_with (hchal.bind_with (hresp.bind_with hver.isPPTOn)))

/-- Replacing `schnorrSigKeyGen` with ideal uniform key generation in `schnorrDirectProbGame`
changes the game advantage by at most `1 / 2 ^ n`. -/
theorem advantage_schnorrDirectProbGame_schnorrDirectGame_le
    (setup : ℕ → PMF F.Desc) (k : ℕ → ℕ) (A : F.SchnorrImpersonator) (n : ℕ) :
    Game.advantage (F.schnorrDirectProbGame setup k A n)
      (F.schnorrDirectGame setup k A n) ≤ 1 / 2 ^ n := by
  simp only [schnorrDirectProbGame, schnorrDirectGame, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure]
  refine Game.advantage_bind_le_nnreal (setup n) _ _ fun d => ?_
  exact F.advantage_bind_schnorrSigKeyGen_le n d fun pk α =>
    (ProbComp.eval (A.commit n (d, pk))).bind fun ts =>
      (BitString.uniformList (k n)).bind fun c =>
        (ProbComp.eval (A.respond n (ts.2, c))).bind fun z =>
          pure (decide (ts.1 = F.encode d ((ofBits z : ZMod (F.order d)) • F.generator d -
            (ofBits c : ZMod (F.order d)) • (α • F.generator d))))

/-- Concrete bound for the native direct attack, the bound (19.2) of [BonehShoup2023],
Theorem 19.1, plus the key generator's statistical distance: at each security parameter where every
supported group has at least `2 ^ k n` elements, an impersonator's success probability in
`schnorrDirectProbGame` is at most `1 / 2 ^ n + 1 / 2 ^ k n + √ε'`, where `ε'` is the
discrete-logarithm success probability of the rewinding adversary `A.rewind k`. -/
theorem succProbability_schnorrDirectProbGame_le (setup : ℕ → PMF F.Desc) (k : ℕ → ℕ)
    (A : F.SchnorrImpersonator) (n : ℕ) (hkq : ∀ d ∈ (setup n).support, 2 ^ k n ≤ F.order d) :
    (Game.succProbability (F.schnorrDirectProbGame setup k A n) : ℝ) ≤
      1 / 2 ^ n + 1 / 2 ^ k n +
        √(Game.succProbability (F.discreteLogGame setup (A.rewind k) n)) := by
  have hhop : (Game.succProbability (F.schnorrDirectProbGame setup k A n) : ℝ) ≤
      (Game.succProbability (F.schnorrDirectGame setup k A n) : ℝ) + 1 / 2 ^ n := by
    exact_mod_cast Game.succProbability_le_add_of_advantage_le
      (F.advantage_schnorrDirectProbGame_schnorrDirectGame_le setup k A n)
  linarith [succProbability_schnorrDirectGame_le_ideal setup k A n hkq]

/-- **Schnorr identification is secure against direct attacks under the discrete-logarithm
assumption** ([BonehShoup2023], Theorem 19.1), with its native key generator `schnorrSigKeyGen`.
Suppose the challenge length `k` is computable in polynomial time, every group the setup can
produce at parameter `n` has at least `2 ^ k n` elements, and `1 / 2 ^ k n` is negligible (the
source's super-poly `N := |C|`). Then every uniform strict PPT impersonator succeeds in
`schnorrDirectProbGame` with negligible probability. The proof applies `F.DiscreteLog setup` to
the rewinding adversary `A.rewind k` through its certificate `isPPTOn_rewind`.

Differences from the source: challenges are `k n`-bit words read as numbers modulo `q`, which embed
injectively when `2 ^ k n ≤ q` (`challengeEmbedding`), where the source takes any `C ⊆ ℤ_q`;
commitments and responses are words, and the verifier accepts when the commitment encodes
`z • g - c • u`; the key exponent comes from the strict-PPT sampler `sampleExp` rather than exactly
uniformly; and the setup law is arbitrary, so `F.DiscreteLog setup` is the source's assumption
when an efficient algorithm samples the setup (see `DiscreteLog`). -/
theorem negligible_schnorrDirectProbGame {setup : ℕ → PMF F.Desc} (hDL : F.DiscreteLog setup)
    {k : ℕ → ℕ} (hk : ComputableInPolyTime k encUnary encUnary)
    (hkq : ∀ n, ∀ d ∈ (setup n).support, 2 ^ k n ≤ F.order d)
    (hchallenge : Negligible fun n => 1 / 2 ^ k n) {A : F.SchnorrImpersonator} (hA : A.IsPPT) :
    Negligible fun n => Game.succProbability (F.schnorrDirectProbGame setup k A n) := by
  have hrewind := hDL _ (isPPTOn_rewind hk hA)
  negligible using fun n => succProbability_schnorrDirectProbGame_le setup k A n (hkq n)

variable (F) in
/-- The eavesdropping impersonation attack on Schnorr identification ([BonehShoup2023], Attack
Game 18.2) with its native algorithms: the key pair comes from `schnorrSigKeyGen` and the `Q n`
overheard honest conversations from the strict-PPT honest prover `schnorrRealTranscript`, both of
which sample exponents with `F.sampleExp n d`. -/
noncomputable def schnorrEavesdropProbGame (setup : ℕ → PMF F.Desc) (k Q : ℕ → ℕ)
    (A : F.SchnorrEavesdropAdversary) (n : ℕ) : Game := do
  let d ← setup n
  let (pk, sk) ← ProbComp.eval (F.schnorrSigKeyGen n d)
  let views ← ProbComp.eval
    (OracleComp.replicate (Q n) (F.schnorrRealTranscript n d (ofBits sk : ZMod (F.order d)) (k n)))
  let ts ← ProbComp.eval (A.commit n (d, pk, views))
  let c ← BitString.uniformList (k n)
  let z ← ProbComp.eval (A.respond n (ts.2, c))
  return decide (ts.1 = F.encode d ((ofBits z : ZMod (F.order d)) • F.generator d -
    (ofBits c : ZMod (F.order d)) • ((ofBits sk : ZMod (F.order d)) • F.generator d)))

variable (F) in
/-- Executable `ProbComp Bool` eavesdropping experiment at group description `d`: sample
`(pk, sk) ← schnorrSigKeyGen n d`, generate `Q n` honest transcripts with `schnorrRealTranscript`,
run `A.commit`, sample `c ← BitString.sampleList (k n)`, run `A.respond`, and verify with
`encodeSchnorrVerify`. -/
noncomputable def schnorrEavesdropProbExperiment (k Q : ℕ → ℕ)
    (A : F.SchnorrEavesdropAdversary) (n : ℕ) (d : F.Desc) : ProbComp Bool := do
  let (pk, sk) ← F.schnorrSigKeyGen n d
  let views ← OracleComp.replicate (Q n)
    (F.schnorrRealTranscript n d (ofBits sk : ZMod (F.order d)) (k n))
  let ts ← A.commit n (d, pk, views)
  let c ← BitString.sampleList (k n)
  let z ← A.respond n (ts.2, c)
  return F.encodeSchnorrVerify d pk ts.1 c z

/-- Averaging `schnorrEavesdropProbExperiment` over `d ← setup n` yields
`schnorrEavesdropProbGame`. -/
theorem bind_eval_schnorrEavesdropProbExperiment (setup : ℕ → PMF F.Desc) (k Q : ℕ → ℕ)
    (A : F.SchnorrEavesdropAdversary) (n : ℕ) :
    ((setup n).bind fun d => ProbComp.eval (F.schnorrEavesdropProbExperiment k Q A n d)) =
      F.schnorrEavesdropProbGame setup k Q A n := by
  simp only [schnorrEavesdropProbExperiment, schnorrEavesdropProbGame, schnorrSigKeyGen,
    BitString.eval_sampleList, F.smul_encode, F.encodeSchnorrVerify_encode, ofBits_bits,
    ZMod.natCast_mod, pmf_norm]

/-- `schnorrEavesdropProbExperiment` is uniformly strict PPT in `(n, d)` whenever `k` and `Q` are
computable in polynomial time and `A` is a uniform strict PPT `SchnorrEavesdropAdversary`. -/
theorem isPPTOn_schnorrEavesdropProbExperiment {k Q : ℕ → ℕ}
    (hk : ComputableInPolyTime k encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    {A : F.SchnorrEavesdropAdversary} (hA : A.IsPPT) :
    IsPPTOn (encPair encUnary F.encDesc) encBool
      (fun p : ℕ × F.Desc => F.schnorrEavesdropProbExperiment k Q A p.1 p.2) := by
  let E0 := encPair encUnary F.encDesc
  let E1 := encPair E0 (encPair encBits encBits)
  let E2 := encPair E1 (encList encTranscript)
  let E3 := encPair E2 (encPair encBits encBits)
  let E4 := encPair E3 encBits
  let E5 := encPair E4 encBits
  have hk_t := hk
  have hQ_t := hQ
  have hsk_nat : ComputableInPolyTime
      (fun p : (ℕ × F.Desc) × (List Bool × List Bool) => ofBits p.2.2) E1 encNat :=
    (ComputableInPolyTime.bitsToNat.comp
      (by fun_prop : ComputableInPolyTime
        (fun p : (ℕ × F.Desc) × (List Bool × List Bool) => p.2.2) E1 encBits))
  have hviews : IsPPTOn E1 (encList encTranscript)
      (fun p : (ℕ × F.Desc) × (List Bool × List Bool) =>
        OracleComp.replicate (Q p.1.1)
          (F.schnorrRealTranscript p.1.1 p.1.2 (ofBits p.2.2 : ZMod (F.order p.1.2)) (k p.1.1))) :=
    (F.isPPTOn_schnorrRealTranscript
      (n := fun p : (ℕ × F.Desc) × (List Bool × List Bool) => p.1.1)
      (d := fun p : (ℕ × F.Desc) × (List Bool × List Bool) => p.1.2)
      (α := fun p : (ℕ × F.Desc) × (List Bool × List Bool) => ofBits p.2.2)
      (m := fun p : (ℕ × F.Desc) × (List Bool × List Bool) => k p.1.1)
      (by fun_prop) (by fun_prop) hsk_nat (by fun_prop)).replicate (by fun_prop)
  have hcommit : IsPPTOn E2 (encPair encBits encBits)
      (fun q : ((ℕ × F.Desc) × (List Bool × List Bool)) ×
          List (List Bool × List Bool × List Bool) =>
        A.commit q.1.1.1 (q.1.1.2, q.1.2.1, q.2)) :=
    hA.1.preprocess
      (prepare := fun q : ((ℕ × F.Desc) × (List Bool × List Bool)) ×
          List (List Bool × List Bool × List Bool) =>
        (q.1.1.1, (q.1.1.2, q.1.2.1, q.2)))
      (by fun_prop)
  have hchal : IsPPTOn E3 encBits
      (fun r : (((ℕ × F.Desc) × (List Bool × List Bool)) ×
          List (List Bool × List Bool × List Bool)) × (List Bool × List Bool) =>
        BitString.sampleList (k r.1.1.1.1)) :=
    ComputableInPolyTime.sampleList (by fun_prop)
  have hresp : IsPPTOn E4 encBits
      (fun s : ((((ℕ × F.Desc) × (List Bool × List Bool)) ×
          List (List Bool × List Bool × List Bool)) × (List Bool × List Bool)) × List Bool =>
        A.respond s.1.1.1.1.1 (s.1.2.2, s.2)) :=
    hA.2.preprocess
      (prepare := fun s : ((((ℕ × F.Desc) × (List Bool × List Bool)) ×
          List (List Bool × List Bool × List Bool)) × (List Bool × List Bool)) × List Bool =>
        (s.1.1.1.1.1, (s.1.2.2, s.2)))
      (by fun_prop)
  have hver : ComputableInPolyTime
      (fun u : (((((ℕ × F.Desc) × (List Bool × List Bool)) ×
          List (List Bool × List Bool × List Bool)) × (List Bool × List Bool)) × List Bool) ×
          List Bool =>
        F.encodeSchnorrVerify u.1.1.1.1.1.2 u.1.1.1.1.2.1 u.1.1.2.1 u.1.2 u.2)
      E5 encBool := by
    fun_prop
  unfold schnorrEavesdropProbExperiment
  exact F.isPPTOn_schnorrSigKeyGen.bind_with
    (hviews.bind_with (hcommit.bind_with (hchal.bind_with (hresp.bind_with hver.isPPTOn))))

/-- Replacing `schnorrSigKeyGen` with ideal uniform key generation in `schnorrEavesdropProbGame`
changes the game advantage by at most `1 / 2 ^ n`. -/
theorem advantage_schnorrEavesdropProbGame_schnorrEavesdropGame_le
    (setup : ℕ → PMF F.Desc) (k Q : ℕ → ℕ) (A : F.SchnorrEavesdropAdversary) (n : ℕ) :
    Game.advantage (F.schnorrEavesdropProbGame setup k Q A n)
      (F.schnorrEavesdropGame setup k Q A n) ≤ 1 / 2 ^ n := by
  simp only [schnorrEavesdropProbGame, schnorrEavesdropGame, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure]
  refine Game.advantage_bind_le_nnreal (setup n) _ _ fun d => ?_
  exact F.advantage_bind_schnorrSigKeyGen_le n d fun pk α =>
    (ProbComp.eval (OracleComp.replicate (Q n) (F.schnorrRealTranscript n d α (k n)))).bind
      fun views =>
        (ProbComp.eval (A.commit n (d, pk, views))).bind fun ts =>
          (BitString.uniformList (k n)).bind fun c =>
            (ProbComp.eval (A.respond n (ts.2, c))).bind fun z =>
              pure (decide (ts.1 = F.encode d ((ofBits z : ZMod (F.order d)) • F.generator d -
                (ofBits c : ZMod (F.order d)) • (α • F.generator d))))

/-- Replacing both `schnorrSigKeyGen` and the `Q n` strict-PPT honest conversations in
`schnorrEavesdropProbGame` with ideal key generation and simulated conversations in
`schnorrDirectGame setup k (A.toDirect k Q)` changes the game advantage by at most
`(2 * Q n + 1) / 2 ^ n`. -/
theorem advantage_schnorrEavesdropProbGame_schnorrDirectGame_le
    (setup : ℕ → PMF F.Desc) (k Q : ℕ → ℕ) (A : F.SchnorrEavesdropAdversary) (n : ℕ) :
    Game.advantage (F.schnorrEavesdropProbGame setup k Q A n)
      (F.schnorrDirectGame setup k (A.toDirect k Q) n) ≤ (2 * Q n + 1) / 2 ^ n := by
  refine (Game.advantage_triangle _ (F.schnorrEavesdropGame setup k Q A n) _).trans ?_
  calc _ ≤ (1 : ℝ≥0) / 2 ^ n + 2 * Q n / 2 ^ n :=
      add_le_add
        (F.advantage_schnorrEavesdropProbGame_schnorrEavesdropGame_le setup k Q A n)
        (F.advantage_schnorrEavesdropGame_schnorrDirectGame_le setup k Q A n)
    _ = (2 * Q n + 1) / 2 ^ n := by ring

/-- Concrete bound for the native eavesdropping attack: at each security parameter where every
supported group has at least `2 ^ k n` elements, an eavesdropper's success probability in
`schnorrEavesdropProbGame` is at most `(2 * Q n + 1) / 2 ^ n + 1 / 2 ^ k n + √ε'`, where `ε'` is
the discrete-logarithm success probability of the rewinding adversary `(A.toDirect k Q).rewind k`.
The term `(2 * Q n + 1) / 2 ^ n` is the statistical distance of the native key generator and the
`Q n` simulated conversations from ideal ones, where [BonehShoup2023], Theorem 19.5 has an exact
equality. -/
theorem succProbability_schnorrEavesdropProbGame_le
    (setup : ℕ → PMF F.Desc) (k Q : ℕ → ℕ) (A : F.SchnorrEavesdropAdversary) (n : ℕ)
    (hkq : ∀ d ∈ (setup n).support, 2 ^ k n ≤ F.order d) :
    (Game.succProbability (F.schnorrEavesdropProbGame setup k Q A n) : ℝ) ≤
      (2 * Q n + 1) / 2 ^ n + 1 / 2 ^ k n +
        √(Game.succProbability (F.discreteLogGame setup ((A.toDirect k Q).rewind k) n)) := by
  have hhop : (Game.succProbability (F.schnorrEavesdropProbGame setup k Q A n) : ℝ) ≤
      (Game.succProbability (F.schnorrDirectGame setup k (A.toDirect k Q) n) : ℝ) +
        (2 * Q n + 1) / 2 ^ n := by
    exact_mod_cast Game.succProbability_le_add_of_advantage_le
      (F.advantage_schnorrEavesdropProbGame_schnorrDirectGame_le setup k Q A n)
  linarith [succProbability_schnorrDirectGame_le_ideal setup k (A.toDirect k Q) n hkq]

variable (F) in
/-- Schnorr identification with challenge length `k` is secure against eavesdropping attacks
([BonehShoup2023], Definition 18.6) with its native algorithms (`schnorrEavesdropProbGame`): for
every polynomial-time conversation count `Q` and every uniform strict PPT eavesdropping adversary
`A`, the success probability is negligible. The source's adversary chooses how many conversations
to request; quantifying over every polynomial-time count `Q` covers an adversary that requests at
most `Q n` of them. -/
def IsProbEavesdropSecure (setup : ℕ → PMF F.Desc) (k : ℕ → ℕ) : Prop :=
  ∀ (Q : ℕ → ℕ), ComputableInPolyTime Q encUnary encUnary →
    ∀ (A : F.SchnorrEavesdropAdversary), A.IsPPT →
      Negligible fun n => Game.succProbability (F.schnorrEavesdropProbGame setup k Q A n)

/-- **Schnorr identification is secure against eavesdropping attacks under the discrete-logarithm
assumption** ([BonehShoup2023], Theorems 19.1 and 19.5 combined), with its native algorithms.
Under the premises of `negligible_schnorrDirectProbGame` and a conversation count `Q` computable in
polynomial time, every uniform strict PPT eavesdropping adversary succeeds in
`schnorrEavesdropProbGame` with negligible probability. The proof applies `F.DiscreteLog setup` to
the rewinding adversary of the direct impersonator `A.toDirect k Q`, which simulates the `Q n`
conversations, through the certificates `isPPT_toDirect` and `isPPTOn_rewind`. Where
Theorem 19.5 has an exact equality, the strict-PPT simulator and key generator add the statistical
term `(2 * Q n + 1) / 2 ^ n` (`succProbability_schnorrEavesdropProbGame_le`). The other
differences from the source are those of `negligible_schnorrDirectProbGame`. -/
theorem negligible_schnorrEavesdropProbGame {setup : ℕ → PMF F.Desc} (hDL : F.DiscreteLog setup)
    {k Q : ℕ → ℕ} (hk : ComputableInPolyTime k encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hkq : ∀ n, ∀ d ∈ (setup n).support, 2 ^ k n ≤ F.order d)
    (hchallenge : Negligible fun n => 1 / 2 ^ k n)
    {A : F.SchnorrEavesdropAdversary} (hA : A.IsPPT) :
    Negligible fun n => Game.succProbability (F.schnorrEavesdropProbGame setup k Q A n) := by
  have hrewind := hDL _ (isPPTOn_rewind hk (isPPT_toDirect hk hQ hA))
  negligible using fun n => succProbability_schnorrEavesdropProbGame_le setup k Q A n (hkq n)

/-- **Schnorr identification satisfies `IsProbEavesdropSecure` under the discrete-logarithm
assumption** ([BonehShoup2023], Theorems 19.1 and 19.5 combined): this is
`negligible_schnorrEavesdropProbGame` for every polynomial-time conversation count and every
uniform strict PPT eavesdropper. -/
theorem schnorr_isProbEavesdropSecure_of_discreteLogHard
    {setup : ℕ → PMF F.Desc} (hDL : F.DiscreteLog setup)
    {k : ℕ → ℕ} (hk : ComputableInPolyTime k encUnary encUnary)
    (hkq : ∀ n, ∀ d ∈ (setup n).support, 2 ^ k n ≤ F.order d)
    (hchallenge : Negligible fun n => 1 / 2 ^ k n) :
    F.IsProbEavesdropSecure setup k :=
  fun _ hQ _ hA => negligible_schnorrEavesdropProbGame hDL hk hQ hkq hchallenge hA

end Cslib.Crypto.PrimeOrderGroupFamily
