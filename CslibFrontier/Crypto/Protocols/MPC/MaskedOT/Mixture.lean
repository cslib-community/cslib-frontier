/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Composition.HybridIndex
public import CslibFrontier.Crypto.Protocols.MPC.MaskedOT

/-!
# Sequential masked transfers under a common outer stage

`semiHonestAdvantage_compose_seqBatchOT_maskedOT_le_sum_roundGame` bounds the semi-honest advantage
against an outer protocol over the batched transfer run by sequential masked transfers
(`seqBatchOT k M` over `maskedOT`) over a substituted pad transfer, for one fixed instance. This
module proves the same bounds when every component is indexed by the outcome `a` of a common outer
stage `p : PMF (Bool ⊕ α)`, such as the group description drawn by a trusted setup: the type of
the pads, the masks, the pad-transfer protocol with its world, schedule and coins, the outer
protocol, the simulators, the coalition, the inputs and the distinguisher may all depend on `a`.
Every game of the fixed-instance bound becomes the outer stage followed by that game at the index
`a`, and every absolute value (`Game.advantage`) is outside the expectation over the outer stage,
so each term is the absolute difference of two acceptance probabilities of one environment.

This is original bookkeeping, a step toward the asymptotic composition theorem (#6045), and not a
cited theorem. The statements are triangle inequalities between distributions: nothing is assumed
about the protocols, the simulators or the distinguishers, no term of a bound is bounded here, and
no efficiency of the environments is claimed.

## Main results

* `Cslib.Crypto.Protocols.MPC.advantage_bind_compose_seqBatchOT_compose_le_sum_roundGame`: an outer
  protocol over `seqBatchOT k M` over a substituted single transfer, under a common outer stage:
  the advantage of `composeDistinguisher` against the outer protocol with the ideal batched
  transfer, plus, per call and transfer, the advantage of one environment against the single
  transfer.
* `Cslib.Crypto.Protocols.MPC.advantage_bind_compose_seqBatchOT_maskedOT_le_sum_roundGame`: the
  same with every single transfer run by `maskedOT` over a substituted pad transfer: per call and
  transfer, the advantage of one environment against `maskedOT` with the ideal pad transfer and
  against the pad transfer.
* `Cslib.Crypto.Protocols.MPC.advantage_bind_compose_seqBatchOT_compose_le_add_mul_roundGame`,
  `Cslib.Crypto.Protocols.MPC.advantage_bind_compose_seqBatchOT_maskedOT_le_add_mul_roundGame`: the
  same two bounds with, per call, one environment that draws the transfer below `2 ^ L` with fair
  coins, and the factor `2 ^ L ≥ k`: the signed differences of the hybrids over the transfers
  telescope before the absolute value is taken.
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib Cslib.Probability Cslib.ProbComp Cslib.Crypto
open _root_.Cslib.Crypto.Protocols.MPC.Composition
open scoped ENNReal

/-- An outer stage `p` followed by an environment `e a` that depends on its index `a`, as one
outer stage whose index is the pair of `a` and the index produced by `e a`. -/
private noncomputable def bindSigma {α : Type} {β : α → Type} (p : PMF (Bool ⊕ α))
    (e : (a : α) → PMF (Bool ⊕ β a)) : PMF (Bool ⊕ Σ a, β a) :=
  p.bind (Sum.elim (fun b => PMF.pure (Sum.inl b)) fun a => (e a).map (Sum.map id (Sigma.mk a)))

/-- A game after `bindSigma p e` is the outer stage `p` followed by `e a` and the game at the
pair. -/
private theorem bindSigma_bind_elim {α : Type} {β : α → Type} (p : PMF (Bool ⊕ α))
    (e : (a : α) → PMF (Bool ⊕ β a)) (g : (Σ a, β a) → PMF Bool) :
    (bindSigma p e).bind (Sum.elim PMF.pure g) =
      p.bind (Sum.elim PMF.pure fun a => (e a).bind (Sum.elim PMF.pure fun c => g ⟨a, c⟩)) := by
  rw [bindSigma, PMF.bind_bind]
  refine congrArg _ (funext fun s => ?_)
  cases s with
  | inl _ => simp only [Sum.elim_inl, PMF.pure_bind]
  | inr _ =>
    rw [Sum.elim_inr, PMF.bind_map]
    exact congrArg _ (funext fun t => by cases t <;> rfl)

variable {α : Type} {m : α → ℕ} {spec₂ : α → MultiOracleSpec}
  {sc₂ : (a : α) → Schedule 2 (spec₂ a)} {Coins₂ : α → Fin 2 → Type}

/-- **An outer protocol over the batched transfer run by sequential single transfers, under a
common outer stage.** Let `p` be the distribution of an outer stage that either decides a bit or
produces an index `a`, such as the description drawn by a trusted setup. Let the outer protocol
`P a`, which calls the batched transfer `batchOTSpec k M` in at most `N` oracle rounds, the
protocol `Sub a` for the single transfer in the world `W₂ a`, the simulators, the coalition, the
inputs and the distinguisher `D a` all depend on `a`, with every call of `P a` run by
`seqBatchOT k M` over `Sub a`. The advantage between the ideal game of the composed protocol with
the composed simulator and its real game, both after the outer stage, is at most the advantage
between the ideal and the real game of `P a` with the ideal batched transfer against
`composeDistinguisher`, after the outer stage, plus the sum over the calls `i < N` and the
transfers `j < k` of the advantage of one environment between the ideal game of that transfer, for
`otFunctionality M` with `S₂ a`, and its real game with `Sub a`: this environment runs the outer
stage and then `composeSeqBatchOTRoundEnv` of transfer `j` of call `i`. Every absolute value is
outside the expectation over the outer stage.

This is `semiHonestAdvantage_compose_seqBatchOT_compose_le_sum_roundGame` under a common outer
stage; for an outer stage that never decides, take `p = q.map Sum.inr`. Nothing is assumed about
the protocols, the simulators or the distinguishers, and no efficiency of the environments is
claimed. -/
theorem advantage_bind_compose_seqBatchOT_compose_le_sum_roundGame (p : PMF (Bool ⊕ α)) (k : ℕ)
    (M : Type) {sc₁ : (a : α) → Schedule (m a) (batchOTSpec k M)}
    {In Coins₁ Out : (a : α) → Fin (m a) → Type}
    (P : (a : α) → Protocol (m a) (batchOTSpec k M) (sc₁ a) (In a) (Coins₁ a) (Out a))
    (W₂ : (a : α) → MultiOracleWorld (spec₂ a))
    (Sub : (a : α) → Protocol 2 (spec₂ a) (sc₂ a) (OTIn M) (Coins₂ a) (OTOut M))
    (S₂ : (a : α) → (J : Finset (Fin 2)) →
      CoalitionSimulator (sc₂ a) (OTIn M) (Coins₂ a) (OTOut M) J)
    (f : (a : α) → Functionality (m a) (In a) (Out a))
    (S₁ : (a : α) → (I : Finset (Fin (m a))) →
      CoalitionSimulator (sc₁ a) (In a) (Coins₁ a) (Out a) I)
    (I : (a : α) → Finset (Fin (m a))) (x : (a : α) → (i : Fin (m a)) → In a i)
    (D : (a : α) → ((i : I a) → PartyView (In a)
        (Schedule.ComposedCoins
          (fun _ => Schedule.ComposedCoins (fun _ => Coins₂ a) (fun _ => Unit)
            (seqBatchOTSchedule k M)) (Coins₁ a) (sc₁ a))
        (Schedule.compose
          (fun _ => Schedule.compose (fun _ => sc₂ a) (seqBatchOTSchedule k M)) (sc₁ a)) i) ×
      ((i : Fin (m a)) → Out a i) → ProbComp Bool)
    (N : ℕ) (hN : ∀ a, (sc₁ a).oracleRounds ≤ N) :
    Game.advantage
        (p.bind (Sum.elim PMF.pure fun a =>
          (ProbComp.eval (idealJoint (f a) (I a)
            (composeSim (P a) (S₁ a (I a))
              (fun _ J => composeSim (seqBatchOT k M) (seqBatchOTSim k M J) (fun _ => S₂ a)))
            (x a))).bind fun r => ProbComp.eval (D a r)))
        (p.bind (Sum.elim PMF.pure fun a =>
          (((P a).compose fun _ => (seqBatchOT k M).compose fun _ => Sub a).realJoint (W₂ a)
            (I a) (x a)).bind fun r => ProbComp.eval (D a r))) ≤
      Game.advantage
          (p.bind (Sum.elim PMF.pure fun a =>
            (ProbComp.eval (idealJoint (f a) (I a) (S₁ a (I a)) (x a))).bind fun r =>
              ProbComp.eval (composeDistinguisher (P a)
                (fun _ J => composeSim (seqBatchOT k M) (seqBatchOTSim k M J) (fun _ => S₂ a))
                (I a) (x a) (D a) r)))
          (p.bind (Sum.elim PMF.pure fun a =>
            ((P a).realJoint (batchOTWorld k M) (I a) (x a)).bind fun r =>
              ProbComp.eval (composeDistinguisher (P a)
                (fun _ J => composeSim (seqBatchOT k M) (seqBatchOTSim k M J) (fun _ => S₂ a))
                (I a) (x a) (D a) r))) +
        ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range k,
          Game.advantage
            (p.bind (Sum.elim PMF.pure fun a =>
              (composeSeqBatchOTRoundEnv k M (P a) (W₂ a) (Sub a) (S₂ a) (I a) (x a) (D a) i
                j).bind
                (roundGame fun op J q => ProbComp.eval (idealJoint (otWorld M op) J (S₂ a J) q))))
            (p.bind (Sum.elim PMF.pure fun a =>
              (composeSeqBatchOTRoundEnv k M (P a) (W₂ a) (Sub a) (S₂ a) (I a) (x a) (D a) i
                j).bind
                (roundGame fun _ J q => (Sub a).realJoint (W₂ a) J q))) := by
  refine (advantage_bind_compose_le_add_sum_roundGame p P (fun _ => batchOTWorld k M) W₂ f S₁
    (fun a _ => (seqBatchOT k M).compose fun _ => Sub a)
    (fun a _ J => composeSim (seqBatchOT k M) (seqBatchOTSim k M J) (fun _ => S₂ a)) I x D N
    hN).trans (add_le_add le_rfl (Finset.sum_le_sum fun i _ => ?_))
  have h := advantage_bind_compose_le_add_sum_roundGame
    (bindSigma p fun a =>
      composeRoundEnv (P a) (batchOTWorld k M) (W₂ a)
        (fun _ => (seqBatchOT k M).compose fun _ => Sub a)
        (fun _ J => composeSim (seqBatchOT k M) (seqBatchOTSim k M J) (fun _ => S₂ a)) (I a)
        (x a) (D a) i)
    (fun _ => seqBatchOT k M) (fun _ => otWorld M) (fun c => W₂ c.1)
    (fun _ => batchOTFunctionality k M) (fun _ => seqBatchOTSim k M) (fun c _ => Sub c.1)
    (fun c _ => S₂ c.1) (fun c => c.2.coalition) (fun c => c.2.query) (fun c => c.2.guess) k
    (fun _ => (oracleRounds_seqBatchOTSchedule k M).le)
  have h₀ := perfectSemiHonestPrivate_seqBatchOT k M
  dsimp only [PerfectSemiHonestPrivate] at h₀
  simp only [h₀, Game.advantage_self, zero_add, bindSigma_bind_elim] at h
  simp only [composeSeqBatchOTRoundEnv, bind_elim_bind_roundGame]
  exact h

/-- **An outer protocol over sequential masked transfers over a substituted pad transfer, under a
common outer stage.** Let `p` be the distribution of an outer stage that either decides a bit or
produces an index `a`, such as the group description drawn by a trusted setup. Let the type `G a`
of the pads, the masks, the distribution of the pads, the protocol `Sub a` for the pad transfer in
the world `W₂ a`, the outer protocol `P a`, which calls the batched transfer `batchOTSpec k M` in
at most `N` oracle rounds, the simulators, the coalition, the inputs and the distinguisher `D a`
all depend on `a`, with every call of `P a` run by `seqBatchOT k M` over `maskedOT` over `Sub a`.
The advantage between the ideal game of the composed protocol with the composed simulator and its
real game, both after the outer stage, is at most the advantage between the ideal and the real
game of `P a` with the ideal batched transfer against `composeDistinguisher`, after the outer
stage, plus, for every call `i < N` and every transfer `j < k`, two advantages of the environment
that runs the outer stage and then `composeSeqBatchOTRoundEnv` of that transfer, followed by one
further stage:

* between the ideal and the real game of `maskedOT` with the ideal pad transfer, against
  `composeDistinguisher`;
* between the ideal game of the pad transfer, with the simulator `S₂ a`, and its real game with
  `Sub a` (`composeRoundEnv` of `maskedOT`).

Every absolute value is outside the expectation over the outer stage. This is
`semiHonestAdvantage_compose_seqBatchOT_maskedOT_le_sum_roundGame` under a common outer stage; for
an outer stage that never decides, take `p = q.map Sum.inr`. Nothing is assumed about the
protocols, the masks, the simulators or the distinguishers; no term is bounded here and no
efficiency of the environments is claimed. -/
theorem advantage_bind_compose_seqBatchOT_maskedOT_le_sum_roundGame {G : α → Type} {M : Type}
    (p : PMF (Bool ⊕ α)) (k : ℕ) {sc₁ : (a : α) → Schedule (m a) (batchOTSpec k M)}
    {In Coins₁ Out : (a : α) → Fin (m a) → Type}
    (P : (a : α) → Protocol (m a) (batchOTSpec k M) (sc₁ a) (In a) (Coins₁ a) (Out a))
    (mask unmask : (a : α) → G a → M → M) (samplePads : (a : α) → ProbComp (G a × G a))
    (W₂ : (a : α) → MultiOracleWorld (spec₂ a))
    (Sub : (a : α) → Protocol 2 (spec₂ a) (sc₂ a) (OTIn (G a)) (Coins₂ a) (OTOut (G a)))
    (Sm : (a : α) → (J : Finset (Fin 2)) →
      CoalitionSimulator (maskedOTSchedule (G a) M) (OTIn M) (MaskedOTCoins (G a)) (OTOut M) J)
    (S₂ : (a : α) → (J : Finset (Fin 2)) →
      CoalitionSimulator (sc₂ a) (OTIn (G a)) (Coins₂ a) (OTOut (G a)) J)
    (f : (a : α) → Functionality (m a) (In a) (Out a))
    (S₁ : (a : α) → (I : Finset (Fin (m a))) →
      CoalitionSimulator (sc₁ a) (In a) (Coins₁ a) (Out a) I)
    (I : (a : α) → Finset (Fin (m a))) (x : (a : α) → (i : Fin (m a)) → In a i)
    (D : (a : α) → ((i : I a) → PartyView (In a)
        (Schedule.ComposedCoins
          (fun _ => Schedule.ComposedCoins
            (fun _ => Schedule.ComposedCoins (fun _ => Coins₂ a) (MaskedOTCoins (G a))
              (maskedOTSchedule (G a) M))
            (fun _ => Unit) (seqBatchOTSchedule k M)) (Coins₁ a) (sc₁ a))
        (Schedule.compose
          (fun _ => Schedule.compose
            (fun _ => Schedule.compose (fun _ => sc₂ a) (maskedOTSchedule (G a) M))
            (seqBatchOTSchedule k M)) (sc₁ a)) i) ×
      ((i : Fin (m a)) → Out a i) → ProbComp Bool)
    (N : ℕ) (hN : ∀ a, (sc₁ a).oracleRounds ≤ N) :
    Game.advantage
        (p.bind (Sum.elim PMF.pure fun a =>
          (ProbComp.eval (idealJoint (f a) (I a)
            (composeSim (P a) (S₁ a (I a))
              (fun _ J => composeSim (seqBatchOT k M) (seqBatchOTSim k M J)
                (fun _ J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a J)
                  (fun _ => S₂ a)))) (x a))).bind fun r => ProbComp.eval (D a r)))
        (p.bind (Sum.elim PMF.pure fun a =>
          (((P a).compose fun _ => (seqBatchOT k M).compose fun _ =>
            (maskedOT (mask a) (unmask a) (samplePads a)).compose fun _ => Sub a).realJoint
              (W₂ a) (I a) (x a)).bind fun r => ProbComp.eval (D a r))) ≤
      Game.advantage
          (p.bind (Sum.elim PMF.pure fun a =>
            (ProbComp.eval (idealJoint (f a) (I a) (S₁ a (I a)) (x a))).bind fun r =>
              ProbComp.eval (composeDistinguisher (P a)
                (fun _ J => composeSim (seqBatchOT k M) (seqBatchOTSim k M J)
                  (fun _ J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a J)
                    (fun _ => S₂ a)))
                (I a) (x a) (D a) r)))
          (p.bind (Sum.elim PMF.pure fun a =>
            ((P a).realJoint (batchOTWorld k M) (I a) (x a)).bind fun r =>
              ProbComp.eval (composeDistinguisher (P a)
                (fun _ J => composeSim (seqBatchOT k M) (seqBatchOTSim k M J)
                  (fun _ J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a J)
                    (fun _ => S₂ a)))
                (I a) (x a) (D a) r))) +
        ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range k,
          (Game.advantage
              (p.bind (Sum.elim PMF.pure fun a =>
                (composeSeqBatchOTRoundEnv k M (P a) (W₂ a)
                  ((maskedOT (mask a) (unmask a) (samplePads a)).compose fun _ => Sub a)
                  (fun J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a J)
                    (fun _ => S₂ a))
                  (I a) (x a) (D a) i j).bind (Sum.elim PMF.pure fun c =>
                (ProbComp.eval (idealJoint (otFunctionality M) c.coalition (Sm a c.coalition)
                  c.query)).bind fun r =>
                    ProbComp.eval (composeDistinguisher
                      (maskedOT (mask a) (unmask a) (samplePads a)) (fun _ => S₂ a) c.coalition
                      c.query c.guess r))))
              (p.bind (Sum.elim PMF.pure fun a =>
                (composeSeqBatchOTRoundEnv k M (P a) (W₂ a)
                  ((maskedOT (mask a) (unmask a) (samplePads a)).compose fun _ => Sub a)
                  (fun J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a J)
                    (fun _ => S₂ a))
                  (I a) (x a) (D a) i j).bind (Sum.elim PMF.pure fun c =>
                ((maskedOT (mask a) (unmask a) (samplePads a)).realJoint (otWorld (G a))
                  c.coalition c.query).bind fun r =>
                    ProbComp.eval (composeDistinguisher
                      (maskedOT (mask a) (unmask a) (samplePads a)) (fun _ => S₂ a) c.coalition
                      c.query c.guess r)))) +
            Game.advantage
              (p.bind (Sum.elim PMF.pure fun a =>
                (composeSeqBatchOTRoundEnv k M (P a) (W₂ a)
                  ((maskedOT (mask a) (unmask a) (samplePads a)).compose fun _ => Sub a)
                  (fun J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a J)
                    (fun _ => S₂ a))
                  (I a) (x a) (D a) i j).bind (Sum.elim PMF.pure fun c =>
                (composeRoundEnv (maskedOT (mask a) (unmask a) (samplePads a)) (otWorld (G a))
                  (W₂ a) (fun _ => Sub a) (fun _ => S₂ a) c.coalition c.query c.guess 0).bind
                    (roundGame fun op J q =>
                      ProbComp.eval (idealJoint (otWorld (G a) op) J (S₂ a J) q)))))
              (p.bind (Sum.elim PMF.pure fun a =>
                (composeSeqBatchOTRoundEnv k M (P a) (W₂ a)
                  ((maskedOT (mask a) (unmask a) (samplePads a)).compose fun _ => Sub a)
                  (fun J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a J)
                    (fun _ => S₂ a))
                  (I a) (x a) (D a) i j).bind (Sum.elim PMF.pure fun c =>
                (composeRoundEnv (maskedOT (mask a) (unmask a) (samplePads a)) (otWorld (G a))
                  (W₂ a) (fun _ => Sub a) (fun _ => S₂ a) c.coalition c.query c.guess 0).bind
                    (roundGame fun _ J q => (Sub a).realJoint (W₂ a) J q))))) := by
  refine (advantage_bind_compose_seqBatchOT_compose_le_sum_roundGame p k M P W₂
    (fun a => (maskedOT (mask a) (unmask a) (samplePads a)).compose fun _ => Sub a)
    (fun a J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a J)
      (fun _ => S₂ a))
    f S₁ I x D N hN).trans
    (add_le_add le_rfl (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_))
  have h := advantage_bind_compose_le_add_sum_roundGame
    (bindSigma p fun a =>
      composeSeqBatchOTRoundEnv k M (P a) (W₂ a)
        ((maskedOT (mask a) (unmask a) (samplePads a)).compose fun _ => Sub a)
        (fun J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a J)
          (fun _ => S₂ a))
        (I a) (x a) (D a) i j)
    (fun c => maskedOT (mask c.1) (unmask c.1) (samplePads c.1)) (fun c => otWorld (G c.1))
    (fun c => W₂ c.1) (fun _ => otFunctionality M) (fun c => Sm c.1) (fun c _ => Sub c.1)
    (fun c _ => S₂ c.1) (fun c => c.2.coalition) (fun c => c.2.query) (fun c => c.2.guess) 1
    (fun _ => le_rfl)
  simp only [Finset.sum_range_one, bindSigma_bind_elim] at h
  exact h

/-- **An outer protocol over the batched transfer run by sequential single transfers, under a
common outer stage, with one environment that draws the transfer.** In the setting of
`advantage_bind_compose_seqBatchOT_compose_le_sum_roundGame` and for `k ≤ 2 ^ L`, the advantage
between the ideal and the real game of the composed protocol, both after the outer stage, is at
most the advantage between the ideal and the real game of `P a` with the ideal batched transfer
against `composeDistinguisher`, plus, for every call `i < N`, `2 ^ L` times the advantage of one
environment between the ideal game of its challenged transfer, for `otFunctionality M` with
`S₂ a`, and its real game with `Sub a`: this environment draws the transfer `j` below `2 ^ L` with
`L` fair coins (`ProbComp.sampleBinaryNat L`), runs the outer stage and then
`composeSeqBatchOTRoundEnv` of transfer `j` of call `i`.

The signed differences of the hybrids over the transfers of one call telescope
(`advantage_bind_compose_le_add_mul_roundGame`), so there is one absolute value per call instead of
one per transfer; a transfer `j ≥ k` challenges nothing. The calls are still summed, each with its
own environment: for an outer protocol with one call, such as Yao's, the bound has one
environment. Nothing is assumed about the protocols, the simulators or the distinguishers, and no
efficiency of the environments is claimed. -/
theorem advantage_bind_compose_seqBatchOT_compose_le_add_mul_roundGame (p : PMF (Bool ⊕ α)) (k : ℕ)
    (M : Type) {sc₁ : (a : α) → Schedule (m a) (batchOTSpec k M)}
    {In Coins₁ Out : (a : α) → Fin (m a) → Type}
    (P : (a : α) → Protocol (m a) (batchOTSpec k M) (sc₁ a) (In a) (Coins₁ a) (Out a))
    (W₂ : (a : α) → MultiOracleWorld (spec₂ a))
    (Sub : (a : α) → Protocol 2 (spec₂ a) (sc₂ a) (OTIn M) (Coins₂ a) (OTOut M))
    (S₂ : (a : α) → (J : Finset (Fin 2)) →
      CoalitionSimulator (sc₂ a) (OTIn M) (Coins₂ a) (OTOut M) J)
    (f : (a : α) → Functionality (m a) (In a) (Out a))
    (S₁ : (a : α) → (I : Finset (Fin (m a))) →
      CoalitionSimulator (sc₁ a) (In a) (Coins₁ a) (Out a) I)
    (I : (a : α) → Finset (Fin (m a))) (x : (a : α) → (i : Fin (m a)) → In a i)
    (D : (a : α) → ((i : I a) → PartyView (In a)
        (Schedule.ComposedCoins
          (fun _ => Schedule.ComposedCoins (fun _ => Coins₂ a) (fun _ => Unit)
            (seqBatchOTSchedule k M)) (Coins₁ a) (sc₁ a))
        (Schedule.compose
          (fun _ => Schedule.compose (fun _ => sc₂ a) (seqBatchOTSchedule k M)) (sc₁ a)) i) ×
      ((i : Fin (m a)) → Out a i) → ProbComp Bool)
    (N : ℕ) (hN : ∀ a, (sc₁ a).oracleRounds ≤ N) (L : ℕ) (hL : k ≤ 2 ^ L) :
    Game.advantage
        (p.bind (Sum.elim PMF.pure fun a =>
          (ProbComp.eval (idealJoint (f a) (I a)
            (composeSim (P a) (S₁ a (I a))
              (fun _ J => composeSim (seqBatchOT k M) (seqBatchOTSim k M J) (fun _ => S₂ a)))
            (x a))).bind fun r => ProbComp.eval (D a r)))
        (p.bind (Sum.elim PMF.pure fun a =>
          (((P a).compose fun _ => (seqBatchOT k M).compose fun _ => Sub a).realJoint (W₂ a)
            (I a) (x a)).bind fun r => ProbComp.eval (D a r))) ≤
      Game.advantage
          (p.bind (Sum.elim PMF.pure fun a =>
            (ProbComp.eval (idealJoint (f a) (I a) (S₁ a (I a)) (x a))).bind fun r =>
              ProbComp.eval (composeDistinguisher (P a)
                (fun _ J => composeSim (seqBatchOT k M) (seqBatchOTSim k M J) (fun _ => S₂ a))
                (I a) (x a) (D a) r)))
          (p.bind (Sum.elim PMF.pure fun a =>
            ((P a).realJoint (batchOTWorld k M) (I a) (x a)).bind fun r =>
              ProbComp.eval (composeDistinguisher (P a)
                (fun _ J => composeSim (seqBatchOT k M) (seqBatchOTSim k M J) (fun _ => S₂ a))
                (I a) (x a) (D a) r))) +
        ∑ i ∈ Finset.range N, 2 ^ L *
          Game.advantage
            ((ProbComp.eval (ProbComp.sampleBinaryNat L)).bind fun j =>
              p.bind (Sum.elim PMF.pure fun a =>
              (composeSeqBatchOTRoundEnv k M (P a) (W₂ a) (Sub a) (S₂ a) (I a) (x a) (D a) i
                j).bind
                (roundGame fun op J q => ProbComp.eval (idealJoint (otWorld M op) J (S₂ a J) q))))
            ((ProbComp.eval (ProbComp.sampleBinaryNat L)).bind fun j =>
              p.bind (Sum.elim PMF.pure fun a =>
              (composeSeqBatchOTRoundEnv k M (P a) (W₂ a) (Sub a) (S₂ a) (I a) (x a) (D a) i
                j).bind
                (roundGame fun _ J q => (Sub a).realJoint (W₂ a) J q))) := by
  refine (advantage_bind_compose_le_add_sum_roundGame p P (fun _ => batchOTWorld k M) W₂ f S₁
    (fun a _ => (seqBatchOT k M).compose fun _ => Sub a)
    (fun a _ J => composeSim (seqBatchOT k M) (seqBatchOTSim k M J) (fun _ => S₂ a)) I x D N
    hN).trans (add_le_add le_rfl (Finset.sum_le_sum fun i _ => ?_))
  have h := advantage_bind_compose_le_add_mul_roundGame
    (bindSigma p fun a =>
      composeRoundEnv (P a) (batchOTWorld k M) (W₂ a)
        (fun _ => (seqBatchOT k M).compose fun _ => Sub a)
        (fun _ J => composeSim (seqBatchOT k M) (seqBatchOTSim k M J) (fun _ => S₂ a)) (I a)
        (x a) (D a) i)
    (fun _ => seqBatchOT k M) (fun _ => otWorld M) (fun c => W₂ c.1)
    (fun _ => batchOTFunctionality k M) (fun _ => seqBatchOTSim k M) (fun c _ => Sub c.1)
    (fun c _ => S₂ c.1) (fun c => c.2.coalition) (fun c => c.2.query) (fun c => c.2.guess) k L
    (fun _ => (oracleRounds_seqBatchOTSchedule k M).le) hL
  have h₀ := perfectSemiHonestPrivate_seqBatchOT k M
  dsimp only [PerfectSemiHonestPrivate] at h₀
  simp only [h₀, Game.advantage_self, zero_add, bindSigma_bind_elim] at h
  simp only [composeSeqBatchOTRoundEnv, bind_elim_bind_roundGame]
  exact h

/-- **An outer protocol over sequential masked transfers over a substituted pad transfer, under a
common outer stage, with one environment that draws the transfer.** In the setting of
`advantage_bind_compose_seqBatchOT_maskedOT_le_sum_roundGame` and for `k ≤ 2 ^ L`, the advantage
between the ideal and the real game of the composed protocol, both after the outer stage, is at
most the advantage between the ideal and the real game of `P a` with the ideal batched transfer
against `composeDistinguisher`, plus, for every call `i < N`, `2 ^ L` times the sum of two
advantages of the one environment that draws the transfer `j` below `2 ^ L` with `L` fair coins
(`ProbComp.sampleBinaryNat L`), runs the outer stage and then `composeSeqBatchOTRoundEnv` of
transfer `j` of call `i`, followed by one further stage:

* between the ideal and the real game of `maskedOT` with the ideal pad transfer, against
  `composeDistinguisher`;
* between the ideal game of the pad transfer, with the simulator `S₂ a`, and its real game with
  `Sub a` (`composeRoundEnv` of `maskedOT`).

There is one absolute value per call and stage instead of one per transfer; the factor is `2 ^ L`,
not `k`, because fair coins draw an exactly uniform index only below a power of two. Nothing is
assumed about the protocols, the masks, the simulators or the distinguishers; no term is bounded
here and no efficiency of the environments is claimed. -/
theorem advantage_bind_compose_seqBatchOT_maskedOT_le_add_mul_roundGame {G : α → Type} {M : Type}
    (p : PMF (Bool ⊕ α)) (k : ℕ) {sc₁ : (a : α) → Schedule (m a) (batchOTSpec k M)}
    {In Coins₁ Out : (a : α) → Fin (m a) → Type}
    (P : (a : α) → Protocol (m a) (batchOTSpec k M) (sc₁ a) (In a) (Coins₁ a) (Out a))
    (mask unmask : (a : α) → G a → M → M) (samplePads : (a : α) → ProbComp (G a × G a))
    (W₂ : (a : α) → MultiOracleWorld (spec₂ a))
    (Sub : (a : α) → Protocol 2 (spec₂ a) (sc₂ a) (OTIn (G a)) (Coins₂ a) (OTOut (G a)))
    (Sm : (a : α) → (J : Finset (Fin 2)) →
      CoalitionSimulator (maskedOTSchedule (G a) M) (OTIn M) (MaskedOTCoins (G a)) (OTOut M) J)
    (S₂ : (a : α) → (J : Finset (Fin 2)) →
      CoalitionSimulator (sc₂ a) (OTIn (G a)) (Coins₂ a) (OTOut (G a)) J)
    (f : (a : α) → Functionality (m a) (In a) (Out a))
    (S₁ : (a : α) → (I : Finset (Fin (m a))) →
      CoalitionSimulator (sc₁ a) (In a) (Coins₁ a) (Out a) I)
    (I : (a : α) → Finset (Fin (m a))) (x : (a : α) → (i : Fin (m a)) → In a i)
    (D : (a : α) → ((i : I a) → PartyView (In a)
        (Schedule.ComposedCoins
          (fun _ => Schedule.ComposedCoins
            (fun _ => Schedule.ComposedCoins (fun _ => Coins₂ a) (MaskedOTCoins (G a))
              (maskedOTSchedule (G a) M))
            (fun _ => Unit) (seqBatchOTSchedule k M)) (Coins₁ a) (sc₁ a))
        (Schedule.compose
          (fun _ => Schedule.compose
            (fun _ => Schedule.compose (fun _ => sc₂ a) (maskedOTSchedule (G a) M))
            (seqBatchOTSchedule k M)) (sc₁ a)) i) ×
      ((i : Fin (m a)) → Out a i) → ProbComp Bool)
    (N : ℕ) (hN : ∀ a, (sc₁ a).oracleRounds ≤ N) (L : ℕ) (hL : k ≤ 2 ^ L) :
    Game.advantage
        (p.bind (Sum.elim PMF.pure fun a =>
          (ProbComp.eval (idealJoint (f a) (I a)
            (composeSim (P a) (S₁ a (I a))
              (fun _ J => composeSim (seqBatchOT k M) (seqBatchOTSim k M J)
                (fun _ J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a J)
                  (fun _ => S₂ a)))) (x a))).bind fun r => ProbComp.eval (D a r)))
        (p.bind (Sum.elim PMF.pure fun a =>
          (((P a).compose fun _ => (seqBatchOT k M).compose fun _ =>
            (maskedOT (mask a) (unmask a) (samplePads a)).compose fun _ => Sub a).realJoint
              (W₂ a) (I a) (x a)).bind fun r => ProbComp.eval (D a r))) ≤
      Game.advantage
          (p.bind (Sum.elim PMF.pure fun a =>
            (ProbComp.eval (idealJoint (f a) (I a) (S₁ a (I a)) (x a))).bind fun r =>
              ProbComp.eval (composeDistinguisher (P a)
                (fun _ J => composeSim (seqBatchOT k M) (seqBatchOTSim k M J)
                  (fun _ J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a J)
                    (fun _ => S₂ a)))
                (I a) (x a) (D a) r)))
          (p.bind (Sum.elim PMF.pure fun a =>
            ((P a).realJoint (batchOTWorld k M) (I a) (x a)).bind fun r =>
              ProbComp.eval (composeDistinguisher (P a)
                (fun _ J => composeSim (seqBatchOT k M) (seqBatchOTSim k M J)
                  (fun _ J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a J)
                    (fun _ => S₂ a)))
                (I a) (x a) (D a) r))) +
        ∑ i ∈ Finset.range N, 2 ^ L *
          (Game.advantage
              ((ProbComp.eval (ProbComp.sampleBinaryNat L)).bind fun j =>
                p.bind (Sum.elim PMF.pure fun a =>
                (composeSeqBatchOTRoundEnv k M (P a) (W₂ a)
                  ((maskedOT (mask a) (unmask a) (samplePads a)).compose fun _ => Sub a)
                  (fun J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a J)
                    (fun _ => S₂ a))
                  (I a) (x a) (D a) i j).bind (Sum.elim PMF.pure fun c =>
                (ProbComp.eval (idealJoint (otFunctionality M) c.coalition (Sm a c.coalition)
                  c.query)).bind fun r =>
                    ProbComp.eval (composeDistinguisher
                      (maskedOT (mask a) (unmask a) (samplePads a)) (fun _ => S₂ a) c.coalition
                      c.query c.guess r))))
              ((ProbComp.eval (ProbComp.sampleBinaryNat L)).bind fun j =>
                p.bind (Sum.elim PMF.pure fun a =>
                (composeSeqBatchOTRoundEnv k M (P a) (W₂ a)
                  ((maskedOT (mask a) (unmask a) (samplePads a)).compose fun _ => Sub a)
                  (fun J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a J)
                    (fun _ => S₂ a))
                  (I a) (x a) (D a) i j).bind (Sum.elim PMF.pure fun c =>
                ((maskedOT (mask a) (unmask a) (samplePads a)).realJoint (otWorld (G a))
                  c.coalition c.query).bind fun r =>
                    ProbComp.eval (composeDistinguisher
                      (maskedOT (mask a) (unmask a) (samplePads a)) (fun _ => S₂ a) c.coalition
                      c.query c.guess r)))) +
            Game.advantage
              ((ProbComp.eval (ProbComp.sampleBinaryNat L)).bind fun j =>
                p.bind (Sum.elim PMF.pure fun a =>
                (composeSeqBatchOTRoundEnv k M (P a) (W₂ a)
                  ((maskedOT (mask a) (unmask a) (samplePads a)).compose fun _ => Sub a)
                  (fun J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a J)
                    (fun _ => S₂ a))
                  (I a) (x a) (D a) i j).bind (Sum.elim PMF.pure fun c =>
                (composeRoundEnv (maskedOT (mask a) (unmask a) (samplePads a)) (otWorld (G a))
                  (W₂ a) (fun _ => Sub a) (fun _ => S₂ a) c.coalition c.query c.guess 0).bind
                    (roundGame fun op J q =>
                      ProbComp.eval (idealJoint (otWorld (G a) op) J (S₂ a J) q)))))
              ((ProbComp.eval (ProbComp.sampleBinaryNat L)).bind fun j =>
                p.bind (Sum.elim PMF.pure fun a =>
                (composeSeqBatchOTRoundEnv k M (P a) (W₂ a)
                  ((maskedOT (mask a) (unmask a) (samplePads a)).compose fun _ => Sub a)
                  (fun J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a J)
                    (fun _ => S₂ a))
                  (I a) (x a) (D a) i j).bind (Sum.elim PMF.pure fun c =>
                (composeRoundEnv (maskedOT (mask a) (unmask a) (samplePads a)) (otWorld (G a))
                  (W₂ a) (fun _ => Sub a) (fun _ => S₂ a) c.coalition c.query c.guess 0).bind
                    (roundGame fun _ J q => (Sub a).realJoint (W₂ a) J q))))) := by
  refine (advantage_bind_compose_seqBatchOT_compose_le_add_mul_roundGame p k M P W₂
    (fun a => (maskedOT (mask a) (unmask a) (samplePads a)).compose fun _ => Sub a)
    (fun a J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a J)
      (fun _ => S₂ a))
    f S₁ I x D N hN L hL).trans
    (add_le_add le_rfl (Finset.sum_le_sum fun i _ => ?_))
  have h := advantage_bind_compose_le_add_sum_roundGame
    ((ProbComp.eval (ProbComp.sampleBinaryNat L)).bind fun j => bindSigma p fun a =>
      composeSeqBatchOTRoundEnv k M (P a) (W₂ a)
        ((maskedOT (mask a) (unmask a) (samplePads a)).compose fun _ => Sub a)
        (fun J => composeSim (maskedOT (mask a) (unmask a) (samplePads a)) (Sm a J)
          (fun _ => S₂ a))
        (I a) (x a) (D a) i j)
    (fun c => maskedOT (mask c.1) (unmask c.1) (samplePads c.1)) (fun c => otWorld (G c.1))
    (fun c => W₂ c.1) (fun _ => otFunctionality M) (fun c => Sm c.1) (fun c _ => Sub c.1)
    (fun c _ => S₂ c.1) (fun c => c.2.coalition) (fun c => c.2.query) (fun c => c.2.guess) 1
    (fun _ => le_rfl)
  simp only [Finset.sum_range_one, PMF.bind_bind, bindSigma_bind_elim] at h
  exact mul_le_mul' le_rfl h

end Cslib.Crypto.Protocols.MPC
