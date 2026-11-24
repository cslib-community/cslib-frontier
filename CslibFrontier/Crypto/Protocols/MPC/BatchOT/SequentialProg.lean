/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.BatchOT.Sequential
public import CslibFrontier.Crypto.Protocols.MPC.Composition.HybridChallenge
public import CslibFrontier.Crypto.Protocols.MPC.Composition.HybridProg

/-!
# The environments of the sequential batched transfer as programs, and their challenges

`CslibFrontier/Crypto/Protocols/MPC/BatchOT/Sequential.lean` bounds the advantage against an outer
protocol over the batched transfer, run by sequential single transfers over a protocol `Sub`, by a
sum of advantages of the environments `composeSeqBatchOTRoundEnv`, one per transfer of every call.
These environments are distributions. This module gives a program with the distribution of each
environment, and describes the challenges an environment can produce when the outer protocol
corrupts the same slots of every call and offers words of one length.

Everything here is original bookkeeping toward the asymptotic composition theorem (#6045), not a
cited statement. The results are an equality of distributions and a statement about supports: no
efficiency (PPT) certificate is claimed for the program, and the asymptotic composition theorem is
not proved here.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.composeSeqBatchOTRoundEnvProg`: the environment
  `composeSeqBatchOTRoundEnv` of transfer `j` of call `i` as a `ProbComp`.

## Main results

* `Cslib.Crypto.Protocols.MPC.eval_composeSeqBatchOTRoundEnvProg`: the distribution of
  `composeSeqBatchOTRoundEnvProg` is `composeSeqBatchOTRoundEnv`.
* `Cslib.Crypto.Protocols.MPC.coalition_length_of_mem_support_composeSeqBatchOTRoundEnv`: for
  transfers of bit strings, if at every call of the outer protocol the corrupted slots are `J₀`
  and both words offered in every transfer have length `L`, then every challenge of the
  environment has the corrupted slots `J₀` and the transferred word has length `L`.
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib.Probability Cslib.ProbComp
open _root_.Cslib.Crypto.Protocols.MPC.Composition

variable {spec₂ : MultiOracleSpec} {sc₂ : Schedule 2 spec₂} {Coins₂ : Fin 2 → Type}

/-- The environment `composeSeqBatchOTRoundEnv` of transfer `j` of call `i` as a `ProbComp`: it
runs the environment program `composeRoundEnvProg` of the outer protocol `P`, with the earlier
calls run by the program `Protocol.realJointProg` of `seqBatchOT k M` over `Sub` in `W₂`, and on
the challenged call the environment program of `seqBatchOT k M`, with the earlier transfers run by
the program `Sub.realJointProg W₂`. Its distribution is `composeSeqBatchOTRoundEnv`
(`eval_composeSeqBatchOTRoundEnvProg`). -/
@[expose] noncomputable def composeSeqBatchOTRoundEnvProg {m : ℕ} (k : ℕ) (M : Type)
    {sc₁ : Schedule m (batchOTSpec k M)} {In Coins₁ Out : Fin m → Type}
    (P : Protocol m (batchOTSpec k M) sc₁ In Coins₁ Out)
    (W₂ : MultiOracleWorld spec₂) (Sub : Protocol 2 spec₂ sc₂ (OTIn M) Coins₂ (OTOut M))
    (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator sc₂ (OTIn M) Coins₂ (OTOut M) J)
    (I : Finset (Fin m)) (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In
        (Schedule.ComposedCoins
          (fun _ => Schedule.ComposedCoins (fun _ => Coins₂) (fun _ => Unit)
            (seqBatchOTSchedule k M)) Coins₁ sc₁)
        (Schedule.compose
          (fun _ => Schedule.compose (fun _ => sc₂) (seqBatchOTSchedule k M)) sc₁) i) ×
      ((i : Fin m) → Out i) → ProbComp Bool) (i j : ℕ) :
    ProbComp (Bool ⊕ RoundChallenge (spec₁ := otSpec M) (fun _ => sc₂) (fun _ => Coins₂)) :=
  composeRoundEnvProg P (batchOTWorld k M)
    (fun _ J q => ((seqBatchOT k M).compose fun _ => Sub).realJointProg W₂ J q)
    (fun _ J => composeSim (seqBatchOT k M) (seqBatchOTSim k M J) (fun _ => S₂)) I x D i >>=
      Sum.elim (fun b => pure (Sum.inl b)) fun c =>
        composeRoundEnvProg (seqBatchOT k M) (otWorld M) (fun _ J q => Sub.realJointProg W₂ J q)
          (fun _ => S₂) c.coalition c.query c.guess j

/-- The program `composeSeqBatchOTRoundEnvProg k M P W₂ Sub S₂ I x D i j` has the distribution of
the environment `composeSeqBatchOTRoundEnv k M P W₂ Sub S₂ I x D i j`. -/
theorem eval_composeSeqBatchOTRoundEnvProg {m : ℕ} (k : ℕ) (M : Type)
    {sc₁ : Schedule m (batchOTSpec k M)} {In Coins₁ Out : Fin m → Type}
    (P : Protocol m (batchOTSpec k M) sc₁ In Coins₁ Out)
    (W₂ : MultiOracleWorld spec₂) (Sub : Protocol 2 spec₂ sc₂ (OTIn M) Coins₂ (OTOut M))
    (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator sc₂ (OTIn M) Coins₂ (OTOut M) J)
    (I : Finset (Fin m)) (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In
        (Schedule.ComposedCoins
          (fun _ => Schedule.ComposedCoins (fun _ => Coins₂) (fun _ => Unit)
            (seqBatchOTSchedule k M)) Coins₁ sc₁)
        (Schedule.compose
          (fun _ => Schedule.compose (fun _ => sc₂) (seqBatchOTSchedule k M)) sc₁) i) ×
      ((i : Fin m) → Out i) → ProbComp Bool) (i j : ℕ) :
    ProbComp.eval (composeSeqBatchOTRoundEnvProg k M P W₂ Sub S₂ I x D i j) =
      composeSeqBatchOTRoundEnv k M P W₂ Sub S₂ I x D i j := by
  rw [composeSeqBatchOTRoundEnvProg, composeSeqBatchOTRoundEnv, ProbComp.eval_bind]
  refine congrArg₂ PMF.bind
    (eval_composeRoundEnvProg P (batchOTWorld k M) W₂
      (fun _ => (seqBatchOT k M).compose fun _ => Sub)
      (fun _ J q => Protocol.eval_realJointProg _ W₂ J q)
      (fun _ J => composeSim (seqBatchOT k M) (seqBatchOTSim k M J) (fun _ => S₂)) I x D i)
    (funext fun r => ?_)
  cases r with
  | inl b => simp only [Sum.elim_inl, ProbComp.eval_pure]
  | inr c =>
    simp only [Sum.elim_inr]
    exact eval_composeRoundEnvProg (seqBatchOT k M) (otWorld M) W₂ (fun _ => Sub)
      (fun _ J q => Sub.eval_realJointProg W₂ J q) (fun _ => S₂) c.coalition c.query c.guess j

/-- A predicate `Q` holds at every round of `seqOTSteps` from the states `st`, for the coalition
`J`, when it holds for `J` and the query tuple of every transfer: the states of the parties in the
queries never change, and with both parties in their own slots the corrupted slots are `J`. -/
private theorem forallChallenge_seqOTSteps {M : Type} {Out : Fin 2 → Type} (J : Finset (Fin 2))
    (Q : (op : (otSpec M).Op) → Finset (Fin ((otSpec M).arity op)) →
      ((s : Fin ((otSpec M).arity op)) → (otSpec M).Query op s) → Prop)
    (k : ℕ) {State : Fin 2 → Type}
    (query : Fin k → (s : Fin 2) → State s → OTIn M s)
    (output : (s : Fin 2) → State s → (Fin k → OTOut M s) → Out s)
    (st : (i : Fin 2) → State i)
    (h : ∀ t : Fin k, Q () J (fun s => query t s (st s))) :
    ForallChallenge J Q (seqOTSteps k query output) st := by
  have hJ : subCoalition (Function.Embedding.refl (Fin 2)) J = J :=
    Finset.ext fun _ => mem_subCoalition
  induction k generalizing State with
  | zero => simp only [seqOTSteps, ForallChallenge]
  | succ k ih =>
    rw [seqOTSteps, ForallChallenge]
    refine ⟨?_, fun ans => ih _ _ _ fun t => h t.succ⟩
    have h0 := h 0
    rw [← hJ] at h0
    exact h0

/-- In transfer `t` of a batched transfer of bit strings in which both words offered in every
transfer have length `L`, the word transferred to the receiver has length `L`. -/
private theorem length_otOutputs_batchOTQueryAt {k L : ℕ}
    (q : (s : Fin 2) → (batchOTSpec k (List Bool)).Query () s)
    (hq : ∀ (t : Fin k) (b : Bool), (q 0 t b).length = L) (t : Fin k) :
    (otOutputs (fun s => batchOTQueryAt t s (q s)) 1 : List Bool).length = L := by
  change (if q 1 t then q 0 t true else q 0 t false).length = L
  split <;> exact hq t _

/-- **The challenges of the environment of a transfer, for fixed corrupted slots and words of one
length.** Let `P` call the batched transfer of bit strings so that, for all coins in the support
of the coin sampler of `P` and at every call reachable on the inputs `x`, the corrupted slots are
`J₀` (the receiver slot `{1}` alone, or the sender slot `{0}` alone, say) and
both words that the sender offers in every transfer have length `L`. Then every challenge `c` in
the support of the environment `composeSeqBatchOTRoundEnv` of any transfer `j` of any call `i`
has the corrupted slots `J₀`, and the word `otOutputs c.query 1` that the challenged single
transfer gives to the receiver has length `L`. Nothing is assumed about `Sub`, `S₂` or `D`. -/
theorem coalition_length_of_mem_support_composeSeqBatchOTRoundEnv {m : ℕ} (k : ℕ)
    {sc₁ : Schedule m (batchOTSpec k (List Bool))} {In Coins₁ Out : Fin m → Type}
    (P : Protocol m (batchOTSpec k (List Bool)) sc₁ In Coins₁ Out)
    (W₂ : MultiOracleWorld spec₂)
    (Sub : Protocol 2 spec₂ sc₂ (OTIn (List Bool)) Coins₂ (OTOut (List Bool)))
    (S₂ : (J : Finset (Fin 2)) →
      CoalitionSimulator sc₂ (OTIn (List Bool)) Coins₂ (OTOut (List Bool)) J)
    (I : Finset (Fin m)) (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In
        (Schedule.ComposedCoins
          (fun _ => Schedule.ComposedCoins (fun _ => Coins₂) (fun _ => Unit)
            (seqBatchOTSchedule k (List Bool))) Coins₁ sc₁)
        (Schedule.compose
          (fun _ => Schedule.compose (fun _ => sc₂) (seqBatchOTSchedule k (List Bool))) sc₁) i) ×
      ((i : Fin m) → Out i) → ProbComp Bool) (i j : ℕ) (J₀ : Finset (Fin 2)) (L : ℕ)
    (h : ∀ c₁ ∈ (ProbComp.eval (OracleComp.pi P.sampleCoins)).support, ForallChallenge I
      (fun _ J (q : (s : Fin 2) → (batchOTSpec k (List Bool)).Query () s) =>
        J = J₀ ∧ ∀ (t : Fin k) (b : Bool), (q 0 t b).length = L)
      P.steps (fun i => (x i, c₁ i)))
    {c : RoundChallenge (spec₁ := otSpec (List Bool)) (fun _ => sc₂) (fun _ => Coins₂)}
    (hc : Sum.inr c ∈
      (composeSeqBatchOTRoundEnv k (List Bool) P W₂ Sub S₂ I x D i j).support) :
    c.coalition = J₀ ∧ (otOutputs c.query 1 : List Bool).length = L := by
  rw [composeSeqBatchOTRoundEnv, PMF.mem_support_bind_iff] at hc
  obtain ⟨r, hr, hc⟩ := hc
  cases r with
  | inl b =>
    rw [Sum.elim_inl, PMF.support_pure, Set.mem_singleton_iff] at hc
    cases hc
  | inr c' =>
    rw [Sum.elim_inr] at hc
    have h₁ := ForallChallenge.of_mem_support_composeRoundEnv P (batchOTWorld k (List Bool)) W₂
      _ _ I x D i h hr
    exact ForallChallenge.of_mem_support_composeRoundEnv (seqBatchOT k (List Bool))
      (otWorld (List Bool)) W₂ (fun _ => Sub) (fun _ => S₂) c'.coalition c'.query c'.guess j
      (Q := fun _ J q => J = J₀ ∧ (otOutputs q 1 : List Bool).length = L)
      (fun c₁ _ => forallChallenge_seqOTSteps c'.coalition _ k _ _ _ fun t =>
        ⟨h₁.1, length_otOutputs_batchOTQueryAt c'.query h₁.2 t⟩) hc

end Cslib.Crypto.Protocols.MPC
