/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Composition.HybridGame
public import CslibFrontier.Languages.Probabilistic.UniformNat

/-!
# The round hybrids of a composed protocol with one environment that draws the hop

`CslibFrontier/Crypto/Protocols/MPC/Composition/HybridGame.lean` bounds the subprotocol-replacement
gap of a composed protocol by a sum, over the oracle rounds `j`, of the advantage of the
environment `composeRoundEnv … j`. Each summand is an absolute value, so the sum is not bounded by
a multiple of the advantage of one environment: the differences of consecutive hybrids may have
different signs.

This module keeps the signs. The differences of consecutive hybrids telescope before any absolute
value is taken (`Game.advantage_hybrid_average`), so the gap is exactly `2 ^ L` times the advantage
of the one environment that draws the hop `j` below `2 ^ L` with `L` fair coins
(`ProbComp.sampleBinaryNat L`) and then runs `composeRoundEnv … j`, whenever the protocol has at
most `2 ^ L` oracle rounds. An environment of a hop past the last oracle round challenges nothing
and its two games coincide, so no hop is rejected and the count is exact; the factor is `2 ^ L`
rather than the number of rounds because a program of fair coins draws an exactly uniform index
only below a power of two.

This is original bookkeeping for the hybrid argument in the proof of Goldreich's composition
theorem (Section 7.5.2.1, Theorem 7.5.7), not a cited statement: there is no security parameter,
nothing is assumed about the protocols or the simulators, and no efficiency of the environment is
claimed. The asymptotic composition theorem is not proved here (#6045).

## Main results

* `Cslib.Crypto.Protocols.MPC.advantage_bind_compose_le_add_mul_roundGame`: under a common outer
  stage, the advantage against a composed protocol is at most the advantage of
  `composeDistinguisher` against the outer protocol plus `2 ^ L` times the advantage of the one
  environment that draws the hop, between the ideal and the real game of its challenged round.

## References

* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004],
  Section 7.5.2.1 (Theorem 7.5.7).
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib.Probability Cslib.ProbComp
open _root_.Cslib.Crypto.Protocols.MPC.Composition
open scoped NNReal

variable {α : Type} {m : α → ℕ} {spec₁ spec₂ : α → MultiOracleSpec}
  {sc₁ : (a : α) → Schedule (m a) (spec₁ a)}
  {sc₂ : (a : α) → (op : (spec₁ a).Op) → Schedule ((spec₁ a).arity op) (spec₂ a)}
  {In Coins₁ Out : (a : α) → Fin (m a) → Type}
  {Coins₂ : (a : α) → (op : (spec₁ a).Op) → Fin ((spec₁ a).arity op) → Type}

/-- **Composition bound under common outer randomness, with one environment that draws the hop.**
Let `p` be the distribution of an outer stage that either decides a bit or produces an index `a`,
and let the outer protocol `P a`, the subprotocols, the simulators, the coalition, the inputs and
the distinguisher `D a` all depend on `a`, with at most `N ≤ 2 ^ L` oracle rounds. The advantage
between the ideal game of `(P a).compose (Sub a)` with the composed simulator and its real game in
`W₂ a`, both after the outer stage, is at most the advantage between the ideal and the real game
of the outer protocol `P a` in `W₁ a` against `composeDistinguisher`, after the outer stage, plus
`2 ^ L` times the advantage of one environment between the ideal and the real game of its
challenged round: this environment draws the hop `j` below `2 ^ L` with `L` fair coins
(`ProbComp.sampleBinaryNat L`), runs the outer stage and then `composeRoundEnv (P a) … j`.

Compare `advantage_bind_compose_le_add_sum_roundGame`, which has one environment and one absolute
value per oracle round. Here the signed differences of consecutive hybrids telescope, and the
second term is an equality in the proof: the hops `j ≥ N` challenge no round and contribute
nothing. The factor is `2 ^ L`, not `N`; with `L = Nat.clog 2 N` it is less than `2 * N` for
`N ≥ 1`, and it is `1` for `N = 0`. Nothing is assumed about the protocols or the simulators, and
no efficiency is claimed. -/
theorem advantage_bind_compose_le_add_mul_roundGame (p : PMF (Bool ⊕ α))
    (P : (a : α) → Protocol (m a) (spec₁ a) (sc₁ a) (In a) (Coins₁ a) (Out a))
    (W₁ : (a : α) → MultiOracleWorld (spec₁ a)) (W₂ : (a : α) → MultiOracleWorld (spec₂ a))
    (f : (a : α) → Functionality (m a) (In a) (Out a))
    (S₁ : (a : α) → (I : Finset (Fin (m a))) →
      CoalitionSimulator (sc₁ a) (In a) (Coins₁ a) (Out a) I)
    (Sub : (a : α) → (op : (spec₁ a).Op) →
      Protocol ((spec₁ a).arity op) (spec₂ a) (sc₂ a op) ((spec₁ a).Query op) (Coins₂ a op)
        ((spec₁ a).Answer op))
    (S₂ : (a : α) → (op : (spec₁ a).Op) → (J : Finset (Fin ((spec₁ a).arity op))) →
      CoalitionSimulator (sc₂ a op) ((spec₁ a).Query op) (Coins₂ a op) ((spec₁ a).Answer op) J)
    (I : (a : α) → Finset (Fin (m a))) (x : (a : α) → (i : Fin (m a)) → In a i)
    (D : (a : α) → ((i : I a) → PartyView (In a)
        (Schedule.ComposedCoins (Coins₂ a) (Coins₁ a) (sc₁ a))
        (Schedule.compose (sc₂ a) (sc₁ a)) i) × ((i : Fin (m a)) → Out a i) → ProbComp Bool)
    (N L : ℕ) (hN : ∀ a, (sc₁ a).oracleRounds ≤ N) (hL : N ≤ 2 ^ L) :
    Game.advantage
        (p.bind (Sum.elim PMF.pure fun a =>
          (ProbComp.eval (idealJoint (f a) (I a) (composeSim (P a) (S₁ a (I a)) (S₂ a))
            (x a))).bind fun r => ProbComp.eval (D a r)))
        (p.bind (Sum.elim PMF.pure fun a =>
          (((P a).compose (Sub a)).realJoint (W₂ a) (I a) (x a)).bind fun r =>
            ProbComp.eval (D a r))) ≤
      Game.advantage
          (p.bind (Sum.elim PMF.pure fun a =>
            (ProbComp.eval (idealJoint (f a) (I a) (S₁ a (I a)) (x a))).bind fun r =>
              ProbComp.eval (composeDistinguisher (P a) (S₂ a) (I a) (x a) (D a) r)))
          (p.bind (Sum.elim PMF.pure fun a =>
            ((P a).realJoint (W₁ a) (I a) (x a)).bind fun r =>
              ProbComp.eval (composeDistinguisher (P a) (S₂ a) (I a) (x a) (D a) r))) +
        2 ^ L * Game.advantage
          ((ProbComp.eval (ProbComp.sampleBinaryNat L)).bind fun j =>
            p.bind (Sum.elim PMF.pure fun a =>
              (composeRoundEnv (P a) (W₁ a) (W₂ a) (Sub a) (S₂ a) (I a) (x a) (D a) j).bind
                (roundGame fun op J q => ProbComp.eval (idealJoint (W₁ a op) J (S₂ a op J) q))))
          ((ProbComp.eval (ProbComp.sampleBinaryNat L)).bind fun j =>
            p.bind (Sum.elim PMF.pure fun a =>
              (composeRoundEnv (P a) (W₁ a) (W₂ a) (Sub a) (S₂ a) (I a) (x a) (D a) j).bind
                (roundGame fun op J q => (Sub a op).realJoint (W₂ a) J q))) := by
  have hideal (a : α) :
      ((ProbComp.eval (idealJoint (f a) (I a) (composeSim (P a) (S₁ a (I a)) (S₂ a))
        (x a))).bind fun r => ProbComp.eval (D a r)) =
      (ProbComp.eval (idealJoint (f a) (I a) (S₁ a (I a)) (x a))).bind fun r =>
        ProbComp.eval (composeDistinguisher (P a) (S₂ a) (I a) (x a) (D a) r) := by
    rw [← ProbComp.eval_bind, ← ProbComp.eval_bind, eval_idealJoint_composeSim_bind]
  simp only [hideal]
  refine (Game.advantage_triangle _ _ _).trans (add_le_add le_rfl (le_of_eq ?_))
  simp only [← composeRoundEnv_zero_bind_roundGame (P _) (W₁ _) (W₂ _) (Sub _) (S₂ _) (I _) (x _)
    (D _),
    ← fun a => composeRoundEnv_bind_roundGame_of_oracleRounds_le (P a) (W₁ a) (W₂ a) (Sub a)
      (S₂ a) (I a) (x a) (D a)
      (fun op J q => ProbComp.eval (idealJoint (W₁ a op) J (S₂ a op J) q)) ((hN a).trans hL)]
  refine (Game.advantage_hybrid_average
    (fun j => p.bind (Sum.elim PMF.pure fun a =>
      (composeRoundEnv (P a) (W₁ a) (W₂ a) (Sub a) (S₂ a) (I a) (x a) (D a) j).bind
        (roundGame fun op J q => ProbComp.eval (idealJoint (W₁ a op) J (S₂ a op J) q))))
    (2 ^ L) (2 ^ L) le_rfl).trans ?_
  simp only [Fin.is_lt, ↓reduceIte, Nat.cast_pow, Nat.cast_ofNat, ProbComp.eval_sampleBinaryNat,
    PMF.bind_map, Function.comp_def, composeRoundEnv_succ_bind_roundGame]

end Cslib.Crypto.Protocols.MPC
