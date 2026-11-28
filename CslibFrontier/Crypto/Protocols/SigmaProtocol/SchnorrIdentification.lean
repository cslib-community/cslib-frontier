/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Identification
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Linear

/-!
# Schnorr identification

Schnorr's identification scheme ([BonehShoup2023], Section 19.1) is Schnorr's Sigma protocol
with the key generator that draws `α` uniformly from `ZMod q` and publishes `u = α • g`. The
one-way game for this key generator is the discrete-logarithm experiment for `g`: the adversary
wins when it outputs some `α'` with `α' • g = u`. When `g` generates a group of prime order `q`,
this `α'` is the sampled `α`.

The two theorems here are ideal-sampling steps toward Boneh and Shoup's Theorems 19.1 and 19.5,
not the cited results. At a fixed group, with the key drawn from `ZMod q` at the `PMF` level
(`schnorrKeyGen`), they state the relations of those theorems' "in particular" clauses, the bound
(19.2) and the equality `ID2adv[A, I_sch] = ID1adv[B, I_sch]`, for reductions written out here.
They prove neither that these reductions are efficient nor an asymptotic security statement, which
needs a group family with efficient operations and, for Theorem 19.1, the discrete-logarithm
assumption (#5293). Over a `PrimeOrderGroupFamily` with fair-coin key generation, the asymptotic
theorems are `PrimeOrderGroupFamily.negligible_schnorrDirectProbGame` and
`PrimeOrderGroupFamily.negligible_schnorrEavesdropProbGame` (eavesdropping security under the
discrete-logarithm assumption) in `CslibFrontier/Crypto/Computational/SchnorrEavesdrop.lean`; the
rewinding adversary and the simulated-view impersonator are certified by
`PrimeOrderGroupFamily.isPPTOn_rewind` and `PrimeOrderGroupFamily.isPPT_toDirect`.
As for the identification experiments they instantiate, the group and challenge types are in
`Type`.

## Main definitions

* `SigmaProtocol.schnorrKeyGen`: a uniform secret `α` and the public key `α • g`.

## Ideal-sampling steps toward Theorems 19.1 and 19.5

* `SigmaProtocol.schnorr_succProbability_directAttack_le_ideal`: `ε ≤ 1 / N + √ε'`, with `ε'` the
  rewinding extractor's discrete-logarithm success probability (the bound (19.2) of Theorem 19.1).
* `SigmaProtocol.schnorr_eavesdropAttack_eq_directAttack_ideal`: an eavesdropper is no stronger than
  the direct impersonator that simulates its views (the equality of Theorem 19.5).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 19.1.
* [C.-P. Schnorr, *Efficient Signature Generation by Smart Cards*][Schnorr1991]
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability

variable {q : ℕ} [NeZero q] {G C : Type} [AddCommGroup G] [Module (ZMod q) G]

/-- Schnorr key generation ([BonehShoup2023], Section 19.1): a uniform secret `α` and the
verification key `α • g`. -/
noncomputable def schnorrKeyGen (g : G) : PMF (ZMod q × G) :=
  (PMF.uniformOfFintype (ZMod q)).map fun α => (α, α • g)

/-- Every Schnorr key pair is in Schnorr's relation. -/
theorem mem_support_schnorrKeyGen {g : G} {key : ZMod q × G}
    (h : key ∈ (schnorrKeyGen g).support) : key.1 • g = key.2 := by
  obtain ⟨α, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  rfl

variable [DecidableEq G] [Fintype C] [Nonempty C] {ι : C ↪ ZMod q} {g : G}

/-- Ideal-sampling step toward [BonehShoup2023], Theorem 19.1, not the cited result: at a fixed
group, with the key drawn at the `PMF` level by `schnorrKeyGen`, an impersonator's success
probability is at most `1 / N + √ε'` (the bound (19.2)), where `ε'` is the probability that
rewinding it computes a discrete logarithm of the key and `N` is the number of challenges. Missing
are the efficiency of the rewinding adversary `A.rewind (linearExtract ι)` and the asymptotic
statement (#5293). Over a `PrimeOrderGroupFamily`, `PrimeOrderGroupFamily.isPPTOn_rewind`
certifies the rewinding adversary and `PrimeOrderGroupFamily.negligible_schnorrDirectProbGame` is
the asymptotic theorem. -/
theorem schnorr_succProbability_directAttack_le_ideal [Fact q.Prime]
    (A : Impersonator G G C (ZMod q)) :
    (Game.succProbability ((schnorr ι g).directAttack (schnorrKeyGen g) A) : ℝ) ≤
      1 / Fintype.card C + √(Game.succProbability
        (oneWayGame (schnorrKeyGen g) (fun α u => α • g = u) (A.rewind (linearExtract ι)))) :=
  succProbability_directAttack_le (schnorr_specialSoundness.specialSoundOn _) A

/-- Ideal-sampling step toward [BonehShoup2023], Theorem 19.5, not the cited result: at a fixed
group, with the key drawn at the `PMF` level by `schnorrKeyGen`, an eavesdropper succeeds with
exactly the probability of the direct impersonator that simulates its `Q` conversations (the
equality `ID2adv[A, I_sch] = ID1adv[B, I_sch]`). Missing is the efficiency of that simulated-view
impersonator, `A.withSimulatedViews (linearSimulate …)`, whose simulator draws its response
uniformly from `ZMod q` at the `PMF` level; nothing here certifies it as an efficient wrapper
around `A` (#5293). Over a `PrimeOrderGroupFamily`, `PrimeOrderGroupFamily.isPPT_toDirect`
certifies a simulated-view impersonator whose simulator samples with fair coins, and
`PrimeOrderGroupFamily.negligible_schnorrEavesdropProbGame` proves eavesdropping security under the
discrete-logarithm assumption. -/
theorem schnorr_eavesdropAttack_eq_directAttack_ideal {Q : ℕ}
    (A : Impersonator (G × (Fin Q → G × C × ZMod q)) G C (ZMod q)) :
    (schnorr ι g).eavesdropAttack (schnorrKeyGen g) Q A =
      (schnorr ι g).directAttack (schnorrKeyGen g)
        (A.withSimulatedViews
          (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod q) G g) id ι)) :=
  eavesdropAttack_eq_directAttack schnorr_specialHVZK (fun _ => mem_support_schnorrKeyGen) A

end Cslib.Crypto.Protocols.SigmaProtocol
