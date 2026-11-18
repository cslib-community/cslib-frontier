/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiscreteLog.Extract
public import CslibFrontier.Probability.BitString
public import CslibFrontier.Languages.Probabilistic.BitString
public import Cslib.Foundations.Data.BitString
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Identification
import CslibFrontier.Foundations.Data.BitString.Counter
import CslibFrontier.Foundations.Data.Nat.Bits
import CslibFrontier.Probability.PMF
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.PPT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits

/-!
# Schnorr identification and its rewinding discrete-logarithm reduction

Schnorr's identification scheme ([BonehShoup2023], Section 19.1) over a `PrimeOrderGroupFamily`:
the key is a description `d`, drawn from a setup law, a uniform secret `α` and the public key
`u = α • g`. An impersonator sees the description and the encoded public key and sends a
commitment word `t`; the verifier draws a uniform challenge word `c` of `k n` bits; the
impersonator answers with a word `z`. Challenges and responses are read as binary numbers modulo
the group order `q`, and the verifier accepts when `t` encodes `z • g - c • u`; on genuine group
elements this is Schnorr's check `z • g = t + c • u`.

Rewinding an impersonator gives a discrete-logarithm adversary, `SchnorrImpersonator.rewind`. It
runs the impersonator to its commitment, answers two independent uniform challenges from the same
state, and computes `(c - c')⁻¹ (z - z')` modulo `q` with `extractNat`, inverting by Fermat's little
theorem. For each security parameter, if `2 ^ k ≤ q` for every description the setup can produce,

  `ε ≤ 1 / 2 ^ k + √ε'`,

where `ε` is the impersonator's success probability and `ε'` the discrete-logarithm success
probability of the rewinding adversary (`succProbability_schnorrDirectGame_le_ideal`, the
bound (19.2) of [BonehShoup2023], Theorem 19.1). `schnorrDirectGame` draws the secret key with
`PMF.uniformOfFintype`, which a strict PPT machine cannot do, so this bound is an ideal-sampling
step. The rewinding adversary is uniform strict PPT whenever the impersonator is and `k` is
computable in polynomial time (`isPPTOn_rewind`).

Theorem 19.1 itself, for the native key generator `schnorrSigKeyGen`, is
`negligible_schnorrDirectProbGame` in `CslibFrontier.Crypto.Computational.SchnorrEavesdrop`. It
applies the discrete-logarithm assumption to the rewinding adversary through `isPPTOn_rewind`.

The impersonator may use fresh randomness in its second stage; its state is a word. Challenges
are bit strings because strict PPT machines sample them exactly; they cannot sample `ZMod q`
exactly, which matters for the honest prover and for simulation but not for this reduction.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.SchnorrImpersonator`: a two-stage word adversary.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrDirectGame`: the direct impersonation attack, with
  an ideal key.
* `Cslib.Crypto.PrimeOrderGroupFamily.SchnorrImpersonator.rewind`: the rewinding
  discrete-logarithm adversary.
* `Cslib.Crypto.PrimeOrderGroupFamily.SchnorrImpersonator.typed`: an impersonator's typed view,
  which the exact bound runs through the generic Sigma-protocol results.
* `Cslib.Crypto.PrimeOrderGroupFamily.challengeEmbedding`: `m`-bit challenges as scalars modulo
  the group order, injective when `2 ^ m ≤ q`.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_rewind`: the rewinding adversary is uniform strict
  PPT.

## Ideal-sampling step

* `Cslib.Crypto.PrimeOrderGroupFamily.succProbability_schnorrDirectGame_le_ideal`:
  `ε ≤ 1 / 2 ^ k + √ε'` at each security parameter, in the ideal-key game.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 19.1.
* [C.-P. Schnorr, *Efficient Signature Generation by Smart Cards*][Schnorr1991]
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Protocols

variable {F : PrimeOrderGroupFamily}

variable (F) in
/-- A uniform impersonator against Schnorr identification. Its first stage sees the security
parameter, the group description and the encoded public key, and returns a commitment word and a
state word; its second stage sees the security parameter, the state and the challenge word. -/
structure SchnorrImpersonator where
  /-- Commit, keeping a state word. -/
  commit : ℕ → F.Desc × List Bool → ProbComp (List Bool × List Bool)
  /-- Respond to a challenge word from the state word. -/
  respond : ℕ → List Bool × List Bool → ProbComp (List Bool)

/-- Both stages of an impersonator are uniform strict PPT in their whole inputs. -/
def SchnorrImpersonator.IsPPT (A : F.SchnorrImpersonator) : Prop :=
  IsPPTOn (encPair encUnary (encPair F.encDesc encBits)) (encPair encBits encBits)
      (fun input => A.commit input.1 input.2) ∧
    IsPPTOn (encPair encUnary (encPair encBits encBits)) encBits
      (fun input => A.respond input.1 input.2)

variable (F) in
/-- The direct impersonation attack on Schnorr identification ([BonehShoup2023], Attack
Game 18.1), with challenges of `k n` bits and an ideal key: the secret key is drawn with
`PMF.uniformOfFintype`, which a strict PPT machine cannot do. The verifier accepts when the
commitment encodes `z • g - c • u`. The game with the native key generator `schnorrSigKeyGen` is
`schnorrDirectProbGame`. -/
noncomputable def schnorrDirectGame (setup : ℕ → PMF F.Desc) (k : ℕ → ℕ)
    (A : F.SchnorrImpersonator) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let ts ← ProbComp.eval (A.commit n (d, F.encode d (α • F.generator d)))
  let c ← BitString.uniformList (k n)
  let z ← ProbComp.eval (A.respond n (ts.2, c))
  return decide (ts.1 = F.encode d ((ofBits z : ZMod (F.order d)) • F.generator d -
    (ofBits c : ZMod (F.order d)) • (α • F.generator d)))

/-- The rewinding discrete-logarithm adversary (proof of [BonehShoup2023], Theorem 19.1): run the
impersonator to its commitment, answer two independent uniform `k n`-bit challenges from the same
state, and output the extracted witness in binary. -/
noncomputable def SchnorrImpersonator.rewind (k : ℕ → ℕ) (A : F.SchnorrImpersonator) (n : ℕ)
    (input : F.Desc × List Bool) : ProbComp (List Bool) := do
  let ts ← A.commit n input
  let c ← BitString.sampleList (k n)
  let c' ← BitString.sampleList (k n)
  let z ← A.respond n (ts.2, c)
  let z' ← A.respond n (ts.2, c')
  return (extractNat (F.order input.1) (ofBits c) (ofBits z) (ofBits c') (ofBits z')).bits

/-! ### Bit challenges as scalars -/

variable (F) in
/-- When `2 ^ m ≤ F.order d`, `m`-bit challenges `BitString m` embed injectively into
`ZMod (F.order d)` via their binary values. -/
def challengeEmbedding (d : F.Desc) {m : ℕ} (hm : 2 ^ m ≤ F.order d) :
    BitString m ↪ ZMod (F.order d) where
  toFun c := (ofBits (List.ofFn c) : ZMod (F.order d))
  inj' c c' h := by
    have hlt (c : BitString m) : ofBits (List.ofFn c) < F.order d :=
      (ofBits_lt_two_pow _).trans_le (by simpa using hm)
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hlt c), Nat.mod_eq_of_lt (hlt c')] at h
    exact List.ofFn_injective (ofBits_injective_of_length_eq (by simp) h)

/-! ### The exact bound -/

/-- Schnorr's protocol on encoded commitments and binary responses, with statements carrying their
group description; only its verifier is used. -/
private noncomputable def wordProtocol (F : PrimeOrderGroupFamily) (m : ℕ) :
    SigmaProtocol ℕ ((d : F.Desc) × F.Carrier d) (List Bool) (BitString m) (List Bool) where
  State := Unit
  commit _ _ := PMF.pure ([], ())
  respond _ _ _ _ := []
  verify y t c z := decide (t = F.encode y.1 ((ofBits z : ZMod (F.order y.1)) • F.generator y.1 -
    (ofBits (List.ofFn c) : ZMod (F.order y.1)) • y.2))

/-- Schnorr key generation at a security parameter, with the description in the statement. -/
private noncomputable def wordKeyGen (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc)
    (n : ℕ) : PMF (ℕ × (d : F.Desc) × F.Carrier d) := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  return (α.val, ⟨d, α • F.generator d⟩)

/-- The relation: `x` is a discrete logarithm of the public key. -/
private def wordRelation (F : PrimeOrderGroupFamily) (x : ℕ) (y : (d : F.Desc) × F.Carrier d) :
    Prop :=
  (x : ZMod (F.order y.1)) • F.generator y.1 = y.2

private noncomputable instance (F : PrimeOrderGroupFamily) :
    DecidableRel (wordRelation F) := fun _ _ => Classical.propDecidable _

/-- The extractor of `wordProtocol`. -/
private def wordExtract (F : PrimeOrderGroupFamily) (m : ℕ) (y : (d : F.Desc) × F.Carrier d)
    (_ : List Bool) (c : BitString m) (z : List Bool) (c' : BitString m) (z' : List Bool) : ℕ :=
  extractNat (F.order y.1) (ofBits (List.ofFn c)) (ofBits z) (ofBits (List.ofFn c')) (ofBits z')

/-- The typed view of an impersonator at security parameter `n` with `m`-bit challenges: a
`SigmaProtocol.Impersonator` whose statements pair a group description with a group element,
which it sees encoded, and whose challenges are typed bit strings. -/
noncomputable def SchnorrImpersonator.typed (A : F.SchnorrImpersonator) (n m : ℕ) :
    SigmaProtocol.Impersonator ((d : F.Desc) × F.Carrier d) (List Bool) (BitString m)
      (List Bool) where
  State := List Bool
  commit y := ProbComp.eval (A.commit n (y.1, F.encode y.1 y.2))
  respond s c := ProbComp.eval (A.respond n (s, List.ofFn c))

private theorem schnorrDirectGame_eq (setup : ℕ → PMF F.Desc) (k : ℕ → ℕ)
    (A : F.SchnorrImpersonator) (n : ℕ) :
    F.schnorrDirectGame setup k A n =
      (wordProtocol F (k n)).directAttack (wordKeyGen F setup n) (A.typed n (k n)) := by
  simp only [schnorrDirectGame, SigmaProtocol.directAttack, wordKeyGen, wordProtocol,
    SchnorrImpersonator.typed, BitString.uniformList, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind, PMF.bind_map,
    Function.comp_def]

private theorem specialSoundOn (setup : ℕ → PMF F.Desc) {k : ℕ → ℕ} {n : ℕ}
    (hkq : ∀ d ∈ (setup n).support, 2 ^ k n ≤ F.order d) :
    (wordProtocol F (k n)).SpecialSoundOn (wordKeyGen F setup n) (wordRelation F)
      (wordExtract F (k n)) := by
  rintro ⟨x, d, u⟩ hkey t c z c' z' hc hz hz'
  have hd : d ∈ (setup n).support := by
    simp only [wordKeyGen, Probability.PMF.monad_bind_eq_bind,
      Probability.PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff,
      Prod.mk.injEq, Sigma.mk.injEq] at hkey
    obtain ⟨d', hd', -, -, -, hdd, -⟩ := hkey
    exact hdd ▸ hd'
  simp only [SigmaProtocol.Accepts, wordProtocol, decide_eq_true_eq] at hz hz'
  have heq := F.encode_injective d (hz.symm.trans hz')
  have hcne : (ofBits (List.ofFn c) : ZMod (F.order d)) ≠ ofBits (List.ofFn c') :=
    (F.challengeEmbedding d (hkq d hd)).injective.ne hc
  simp only [wordRelation, wordExtract, extractNat_cast hcne, mul_smul]
  rw [sub_smul, sub_eq_sub_iff_sub_eq_sub.mp heq, ← sub_smul,
    inv_smul_smul₀ (sub_ne_zero.mpr hcne)]

/-- The rewinding adversary wins the discrete-logarithm game exactly when its output is a witness
for the generated statement. -/
private theorem decide_wordRelation (d : F.Desc) (α : ZMod (F.order d)) (r : ℕ) :
    decide (wordRelation F r ⟨d, α • F.generator d⟩) =
      decide (((ofBits r.bits : ℕ) : ZMod (F.order d)) = α) := by
  rw [ofBits_bits]
  exact decide_eq_decide.mpr ⟨fun h => F.smul_generator_injective d h, fun h => by
    simp only [wordRelation, h]⟩

private theorem oneWayGame_eq (setup : ℕ → PMF F.Desc) (k : ℕ → ℕ) (A : F.SchnorrImpersonator)
    (n : ℕ) :
    SigmaProtocol.oneWayGame (wordKeyGen F setup n) (wordRelation F)
        ((A.typed n (k n)).rewind (wordExtract F (k n))) =
      F.discreteLogGame setup (A.rewind k) n := by
  simp only [SigmaProtocol.oneWayGame, wordKeyGen, discreteLogGame,
    SigmaProtocol.Impersonator.rewind, SchnorrImpersonator.rewind, SchnorrImpersonator.typed,
    ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList, BitString.uniformList,
    Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure, PMF.bind_bind,
    PMF.pure_bind, PMF.bind_map, Function.comp_def, wordExtract, decide_wordRelation]

/-- Ideal-sampling step toward [BonehShoup2023], Theorem 19.1, not the cited result: in the
ideal-key game `schnorrDirectGame`, at each security parameter where every possible group has at
least `2 ^ k n` elements, an impersonator's success probability is at most `1 / 2 ^ k n + √ε'`,
where `ε'` is the discrete-logarithm success probability of the rewinding adversary (the
bound (19.2)). The native-key bound is `succProbability_schnorrDirectProbGame_le`, and
Theorem 19.1 is `negligible_schnorrDirectProbGame`. -/
theorem succProbability_schnorrDirectGame_le_ideal (setup : ℕ → PMF F.Desc) (k : ℕ → ℕ)
    (A : F.SchnorrImpersonator) (n : ℕ) (hkq : ∀ d ∈ (setup n).support, 2 ^ k n ≤ F.order d) :
    (Game.succProbability (F.schnorrDirectGame setup k A n) : ℝ) ≤
      1 / 2 ^ k n + √(Game.succProbability (F.discreteLogGame setup (A.rewind k) n)) := by
  have h := SigmaProtocol.succProbability_directAttack_le (specialSoundOn setup hkq)
    (A.typed n (k n))
  rw [oneWayGame_eq] at h
  rw [schnorrDirectGame_eq]
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat] using h

/-! ### Efficiency of the rewinding adversary -/

/-- **The rewinding adversary is uniform strict PPT** when the impersonator is and the challenge
length is computable in polynomial time. -/
theorem isPPTOn_rewind {k : ℕ → ℕ} (hk : ComputableInPolyTime k encUnary encUnary)
    {A : F.SchnorrImpersonator} (hA : A.IsPPT) :
    IsPPTOn (encPair encUnary (encPair F.encDesc encBits)) encBits
      (fun input => A.rewind k input.1 input.2) := by
  have hk' := hk.tidy
  have hrespond := hA.2
  unfold SchnorrImpersonator.rewind
  refine hA.1.bind_with ?_
  refine (ComputableInPolyTime.sampleList (by fun_prop)).bind_with ?_
  refine (ComputableInPolyTime.sampleList (by fun_prop)).bind_with ?_
  refine (hrespond.preprocess
    (prepare := fun p : (((ℕ × F.Desc × List Bool) × List Bool × List Bool) × List Bool) ×
      List Bool => (p.1.1.1.1, (p.1.1.2.2, p.1.2))) (by fun_prop)).bind_with ?_
  refine (hrespond.preprocess
    (prepare := fun p : ((((ℕ × F.Desc × List Bool) × List Bool × List Bool) × List Bool) ×
      List Bool) × List Bool => (p.1.1.1.1.1, (p.1.1.1.2.2, p.1.2))) (by fun_prop)).bind_with ?_
  exact (ComputableInPolyTime.tidy (by fun_prop)).isPPTOn

end Cslib.Crypto.PrimeOrderGroupFamily
