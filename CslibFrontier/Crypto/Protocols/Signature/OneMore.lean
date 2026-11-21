/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Signature.Scheme
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Data.Fintype.Card

/-!
# Random-target and one-more certification games

The interface of `Signature.Scheme` also describes a many-to-one trapdoor preimage sampler:
the message is the target, the signature is a preimage, and verification checks its image.
Using this interface imposes neither injectivity nor EUF-CMA security.

`targetExperiment` samples a target independently of a secret preimage. `multiTargetExperiment`
publishes an indexed target vector and asks for one valid preimage. `oneMoreExperiment` gives
the same vector and a chosen-target signing oracle, and asks for `budget + 1` valid answers at
distinct **indices**, after at most `budget` oracle calls. Every call is logged, including
repeated queries; queries need not be among the targets. Programs exceeding the budget lose.
The target sampler is explicit: PoMFRIT uses independent uniform targets, while other samplers
define different games. Target values may collide.

These are finite classical program experiments, not assertions of hardness or polynomial time.
The source VOLE-IHAT reduction additionally requires proof extraction and random-oracle
programming; those composition obligations are tracked in issue #7068.

## Main results

* `oneMoreAccept_implies_budget_lt`: the winning condition really requires more target slots
  than oracle calls.
* `eval_oneMore_collisionAttack`: querying one of two targets and reusing its answer wins
  exactly when the targets collide and that answer verifies. Inversion failures remain visible.
* `succProbability_collisionAttack_uniform`: the collision strategy's success is the signer's
  validation probability divided by the target-space cardinality.

## References

* [Baum et al., *PoMFRIT*][PoMFRIT2026], Definition 3.1 in the USENIX prepublication.
* [*VOLE-IHAT*][VOLEIHAT2026], Security Considerations, one-more trapdoor-preimage assumption.
-/

@[expose] public section

namespace Cslib.Crypto.Signature

open Probability
open scoped NNReal ENNReal

variable {PK SK M Sig : Type} {N : ℕ}

/-- A candidate preimage for one of `N` published target slots. -/
structure PreimageClaim (N : ℕ) (Sig : Type) where
  /-- The challenged slot, rather than a target value chosen by the attacker. -/
  index : Fin N
  /-- The proposed certificate or preimage. -/
  preimage : Sig

/-- Invert an independently sampled target; any verifying answer wins. -/
def targetExperiment (S : Scheme PK SK M Sig) (target : PK → ProbComp M)
    (A : PK → M → ProbComp Sig) : Experiment := do
  let keys ← S.keyGen
  let y ← target keys.1
  let s ← A keys.1 y
  return S.verify keys.1 y s

/-- Solve one slot of an explicitly sampled target vector, without a signing oracle. -/
def multiTargetExperiment (S : Scheme PK SK M Sig)
    (targets : PK → ProbComp (Fin N → M))
    (A : PK → (Fin N → M) → ProbComp (PreimageClaim N Sig)) : Experiment := do
  let keys ← S.keyGen
  let ys ← targets keys.1
  let out ← A keys.1 ys
  return S.verify keys.1 (ys out.index) out.preimage

/-- The fixed-budget one-more test. Calls count with multiplicity; only output indices must
be distinct. In particular, the test does not impose freshness relative to oracle queries. -/
def oneMoreAccept (S : Scheme PK SK M Sig) (pk : PK) (targets : Fin N → M)
    (budget : ℕ) (claims : List (PreimageClaim N Sig)) (log : List (M × Sig)) : Bool :=
  decide (log.length ≤ budget ∧ claims.length = budget + 1 ∧
    (claims.map PreimageClaim.index).Nodup) &&
  claims.all (fun claim => S.verify pk (targets claim.index) claim.preimage)

/-- The fixed-budget one-more game. Its signer answers arbitrary targets using the supplied
algorithm, whose distribution is retained exactly. Excess-query executions lose. -/
def oneMoreExperiment (S : Scheme PK SK M Sig)
    (targets : PK → ProbComp (Fin N → M)) (budget : ℕ)
    (A : PK → (Fin N → M) →
      ProbOracleComp (fun _ : M => Sig) (List (PreimageClaim N Sig))) : Experiment := do
  let keys ← S.keyGen
  let ys ← targets keys.1
  let (out, log) ← (A keys.1 ys).runLog (S.sign keys.2)
  return oneMoreAccept S keys.1 ys budget out log

/-- Winning requires at least `budget + 1` different slots. The game is impossible when
`N ≤ budget`, independently of the signer or attacker. -/
theorem oneMoreAccept_implies_budget_lt {S : Scheme PK SK M Sig} {pk : PK}
    {targets : Fin N → M} {budget : ℕ} {claims : List (PreimageClaim N Sig)}
    {log : List (M × Sig)} (h : oneMoreAccept S pk targets budget claims log = true) :
    budget < N := by
  simp only [oneMoreAccept, Bool.and_eq_true, decide_eq_true_eq] at h
  have hcard := h.1.2.2.length_le_card
  simp only [List.length_map, Fintype.card_fin] at hcard
  omega

/-- Regard a one-target solution as a singleton output in the zero-query one-more game. -/
def liftMultiTarget (A : PK → (Fin N → M) → ProbComp (PreimageClaim N Sig))
    (pk : PK) (ys : Fin N → M) :
    ProbOracleComp (fun _ : M => Sig) (List (PreimageClaim N Sig)) :=
  ProbOracleComp.sample ((fun claim => [claim]) <$> A pk ys)

/-- This embedding makes no signing query, regardless of the attacker's private randomness. -/
theorem liftMultiTarget_queryBounded
    (A : PK → (Fin N → M) → ProbComp (PreimageClaim N Sig)) (pk : PK) (ys : Fin N → M) :
    (liftMultiTarget A pk ys).IsQueryBounded 0 :=
  ProbOracleComp.IsQueryBounded.sample _

/-- The zero-query one-more game includes the ordinary multiple-target game with no loss. -/
theorem oneMore_liftMultiTarget (S : Scheme PK SK M Sig)
    (targets : PK → ProbComp (Fin N → M))
    (A : PK → (Fin N → M) → ProbComp (PreimageClaim N Sig)) :
    oneMoreExperiment S targets 0 (liftMultiTarget A) = multiTargetExperiment S targets A := by
  simp only [oneMoreExperiment, liftMultiTarget, ProbOracleComp.runLog_sample]
  simp [multiTargetExperiment, oneMoreAccept]

/-- A single slot is the ordinary independently sampled target experiment. -/
theorem multiTarget_singleton (S : Scheme PK SK M Sig) (target : PK → ProbComp M)
    (A : PK → M → ProbComp Sig) :
    multiTargetExperiment S (fun pk => (fun y (_ : Fin 1) => y) <$> target pk)
      (fun pk ys => (fun s => (⟨0, s⟩ : PreimageClaim 1 Sig)) <$> A pk (ys 0)) =
    targetExperiment S target A := by
  simp [multiTargetExperiment, targetExperiment]

/-! ## A concrete collision strategy -/

/-- Measure the signer's validation rate on an explicitly sampled target. Unlike `Scheme.Correct`,
this experiment retains invalid answers and explicit failures encoded in the signature type. -/
def signingCorrectnessExperiment (S : Scheme PK SK M Sig) (target : PK → ProbComp M) :
    Experiment := do
  let keys ← S.keyGen
  let y ← target keys.1
  let s ← S.sign keys.2 y
  return S.verify keys.1 y s

/-- Make one signing query for the first target and use its answer for both slots. -/
def collisionAttack (_ : PK) (targets : Fin 2 → M) :
    ProbOracleComp (fun _ : M => Sig) (List (PreimageClaim 2 Sig)) := do
  let s ← ProbOracleComp.query (targets 0)
  return [⟨0, s⟩, ⟨1, s⟩]

/-- The collision strategy makes at most one signing call on every path. -/
theorem collisionAttack_queryBounded (pk : PK) (targets : Fin 2 → M) :
    (collisionAttack (Sig := Sig) pk targets).IsQueryBounded 1 := by
  simpa only [collisionAttack, Nat.add_zero] using
    (ProbOracleComp.IsQueryBounded.query (spec := fun _ : M => Sig) (targets 0)).bind
      (fun s => OracleComp.IsCostBounded.pure ([⟨0, s⟩, ⟨1, s⟩] :
        List (PreimageClaim 2 Sig)) 0)

private theorem runLog_collisionAttack (pk : PK) (targets : Fin 2 → M)
    (oracle : M → ProbComp Sig) :
    (collisionAttack pk targets).runLog oracle =
      (fun s => ([⟨0, s⟩, ⟨1, s⟩], [(targets 0, s)])) <$> oracle (targets 0) := by
  simp only [collisionAttack, ProbOracleComp.runLog, bind_pure_comp,
    ProbOracleComp.runState_map, ProbOracleComp.runState_query, StateT.run_map]
  simp [StateT.run]

/-- For a verifier assigning at most one target to each answer, the one-query collision attack
succeeds exactly when the two targets agree and the oracle's answer verifies. In particular,
no perfect-correctness premise excludes degenerate UOV keys or inversion failures. -/
theorem eval_oneMore_collisionAttack [DecidableEq M] (S : Scheme PK SK M Sig)
    (hfunctional : ∀ pk y z s, S.verify pk y s = true → S.verify pk z s = true → y = z)
    (targets : PK → ProbComp (Fin 2 → M)) :
    ProbComp.eval (oneMoreExperiment S targets 1 collisionAttack) =
      ProbComp.eval (do
        let keys ← S.keyGen
        let ys ← targets keys.1
        let s ← S.sign keys.2 (ys 0)
        return decide (ys 0 = ys 1) && S.verify keys.1 (ys 0) s) := by
  simp only [oneMoreExperiment, runLog_collisionAttack, ProbComp.eval_bind,
    ProbComp.eval_map, ProbComp.eval_pure, PMF.bind_map]
  refine PMF.bind_congr_on_support _ _ _ fun keys _ => ?_
  refine PMF.bind_congr_on_support _ _ _ fun ys _ => ?_
  refine PMF.bind_congr_on_support _ _ _ fun s _ => ?_
  cases hsver : S.verify keys.1 (ys 0) s with
  | false => simp [oneMoreAccept, hsver]
  | true =>
    have hver : S.verify keys.1 (ys 1) s = decide (ys 0 = ys 1) := by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      exact ⟨hfunctional _ _ _ _ hsver, fun h => h ▸ hsver⟩
    simp [oneMoreAccept, hsver, hver]

/-- On two independent uniform targets, the collision strategy succeeds with the signer's
validation probability divided by `card M`. For UOV targets `M = Fin m → F`, the collision
factor is `|F|⁻ᵐ`; the separate validation factor retains failed preimage derivations. -/
theorem succProbability_collisionAttack_uniform [Fintype M] [Nonempty M]
    (S : Scheme PK SK M Sig)
    (hfunctional : ∀ pk y z s, S.verify pk y s = true → S.verify pk z s = true → y = z) :
    Experiment.succProbability (oneMoreExperiment S (fun _ => do
      let y ← ProbComp.uniform M
      let z ← ProbComp.uniform M
      return fun i : Fin 2 => if i.val = 0 then y else z) 1 collisionAttack) =
        (Fintype.card M : ℝ≥0)⁻¹ *
        Experiment.succProbability (signingCorrectnessExperiment S
          (fun _ => ProbComp.uniform M)) := by
  classical
  simp only [Experiment.succProbability]
  rw [eval_oneMore_collisionAttack S hfunctional]
  have hcoin (y : M) (b : Bool) :
      ((PMF.uniformOfFintype M).bind fun z => PMF.pure (decide (y = z) && b)) true =
        (Fintype.card M : ℝ≥0∞)⁻¹ * PMF.pure b true := by
    cases b <;> simp [PMF.bind_apply, PMF.uniformOfFintype_apply, tsum_fintype]
  have hinner (pk : PK) (sk : SK) (y : M) :
      ((PMF.uniformOfFintype M).bind fun z =>
        (ProbComp.eval (S.sign sk y)).bind fun s =>
          PMF.pure (decide (y = z) && S.verify pk y s)) true =
      (Fintype.card M : ℝ≥0∞)⁻¹ *
        ((ProbComp.eval (S.sign sk y)).bind fun s => PMF.pure (S.verify pk y s)) true := by
    rw [PMF.bind_comm]
    simp only [PMF.bind_apply, hcoin]
    simp only [ENNReal.tsum_mul_left, mul_left_comm]
  simp only [signingCorrectnessExperiment, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  unfold Game.succProbability
  conv_lhs =>
    arg 1
    rw [PMF.bind_apply]
    arg 1
    ext keys
    arg 2
    rw [PMF.bind_apply]
    arg 1
    ext y
    arg 2
    erw [hinner]
  simp only [PMF.bind_apply, mul_left_comm, ENNReal.tsum_mul_left]
  simp [ENNReal.toNNReal_mul, ENNReal.toNNReal_inv]

end Cslib.Crypto.Signature
