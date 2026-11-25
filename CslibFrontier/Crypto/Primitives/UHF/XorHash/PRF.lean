/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.PRF.Finite
public import CslibFrontier.Crypto.Primitives.UHF.Finite
public import CslibFrontier.Crypto.Primitives.UHF.XorHash
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Languages.Probabilistic.Traverse.SupportWith
import CslibFrontier.Probability.PMF.Bind

/-!
# Finite PRF reductions for XOR-hash collisions

The distinguisher runs a single-pair collision adversary, queries the table at the tagged
blocks of both messages, and checks whether the two sums collide. Each message needs at most
`ℓ` calls. The real experiment has the same law as the collision game under the keyed table.
The ideal experiment uses a uniform table and has the statistical bound `1 / |Y|`.
The multi-query distinguisher tests a list of up to `Q` messages using at most `Q * ℓ` calls.
Its ideal collision bound multiplies `1 / |Y|` by the number of unordered pairs.

## Main definitions

* `Cslib.Crypto.UHF.xorHashQueries`: compute the sum with one oracle query for each block.
* `Cslib.Crypto.UHF.xorHashCollisionReduction`: distinguish by checking the guessed collision.
* `Cslib.Crypto.UHF.xorHashMultiQueryReduction`: distinguish by checking up to `Q` messages.

## Main results

* `Cslib.Crypto.UHF.isQueryBounded_xorHashCollisionReduction`: the wrapper makes at most
  `2 * ℓ` external calls.
* `Cslib.Crypto.UHF.eval_realExperiment_xorHashCollisionReduction`: a keyed-table run gives
  the collision game's output distribution.
* `Cslib.Crypto.UHF.eval_collisionExperiment_xorHash_le_prfAdvantage`: the finite bound of
  the hybrid step. The uniform strict PPT reduction and asymptotic theorem are tracked in #5790.
* `Cslib.Crypto.UHF.eval_multiQueryExperiment_xorHash_le_prfAdvantage`: the finite multi-query
  bound, with `Q.choose 2` in the ideal-table term.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 7.2.3, Theorem 7.6 and equation (7.12), printed pp. 261–262, and Exercise 7.28, p. 285.
-/

public section

namespace Cslib.Crypto.UHF

open Cslib.Probability
open scoped ENNReal

section Queries

variable {X Y K : Type} {ℓ : ℕ} [AddCommMonoid Y]

/-- Look up each position-tagged block and add the answers. -/
@[expose] def xorHashQueries (m : {xs : List X // xs.length ≤ ℓ}) :
    ProbOracleComp (fun _ : X × Fin ℓ => Y) Y :=
  List.sum <$> (List.ofFn (xorHashQueryAt m)).mapM ProbOracleComp.query

/-- With a fixed table as oracle, the program computes the XOR-hash under that table. -/
theorem run_xorHashQueries (f : X × Fin ℓ → Y) (m : {xs : List X // xs.length ≤ ℓ}) :
    (xorHashQueries m).run (fun x => pure (f x)) = pure (xorHash f m) := by
  simp [xorHashQueries, ProbOracleComp.run_mapM_query, xorHash, List.map_ofFn, List.sum_ofFn]

/-- Each block gives one query, so a message of length at most `ℓ` has budget `ℓ`. -/
theorem isQueryBounded_xorHashQueries (m : {xs : List X // xs.length ≤ ℓ}) :
    (xorHashQueries (Y := Y) m).IsQueryBounded ℓ := by
  apply (OracleComp.isCostBounded_map_iff _ _ _).mpr
  refine (OracleComp.IsCostBounded.mapM (inputs := List.ofFn (xorHashQueryAt m)) (fun x _ =>
    ProbOracleComp.IsQueryBounded.query (spec := fun _ : X × Fin ℓ => Y) x)).mono ?_
  simpa only [List.length_ofFn, Nat.mul_one] using m.property

/-- Run the collision adversary and accept if its two distinct messages give equal sums.
The same oracle answers the queries for both messages. -/
@[expose] def xorHashCollisionReduction [DecidableEq X] [DecidableEq Y]
    (A : ProbComp (CollisionGuess {xs : List X // xs.length ≤ ℓ})) :
    ProbOracleComp (fun _ : X × Fin ℓ => Y) Bool := do
  let guess ← ProbOracleComp.sample A
  let first ← xorHashQueries guess.first
  let second ← xorHashQueries guess.second
  return decide (guess.first ≠ guess.second ∧ first = second)

/-- The collision distinguisher queries at most `ℓ` blocks from each of its two messages. -/
theorem isQueryBounded_xorHashCollisionReduction [DecidableEq X] [DecidableEq Y]
    (A : ProbComp (CollisionGuess {xs : List X // xs.length ≤ ℓ})) :
    (xorHashCollisionReduction (Y := Y) A).IsQueryBounded (2 * ℓ) := by
  rw [xorHashCollisionReduction]
  exact ((ProbOracleComp.IsQueryBounded.sample A).bind fun guess =>
    (isQueryBounded_xorHashQueries guess.first).bind fun _ =>
      (isQueryBounded_xorHashQueries guess.second).bind fun _ =>
        OracleComp.IsCostBounded.pure _ 0).mono (by omega)

/-- Running the wrapper against the keyed function has the same law as the single-pair
collision game for the hash induced by that keyed function. -/
theorem eval_realExperiment_xorHashCollisionReduction [Fintype K] [Nonempty K]
    [DecidableEq X] [DecidableEq Y] (F : K → X × Fin ℓ → Y)
    (A : ProbComp (CollisionGuess {xs : List X // xs.length ≤ ℓ})) :
    ProbComp.eval (PRF.realExperiment F (xorHashCollisionReduction A)) =
      ProbComp.eval (collisionExperiment (fun k => xorHash (F k)) A) := by
  simp only [PRF.realExperiment, xorHashCollisionReduction, collisionExperiment,
    ProbOracleComp.run_bind, ProbOracleComp.run_sample, run_xorHashQueries, ProbOracleComp.run_pure,
    pure_bind, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  rw [PMF.bind_comm]

/-- Run the list adversary and hash its first `Q` messages. A collision requires different
messages with equal digests. Limiting the input list enforces the query budget on every run. -/
@[expose] def xorHashMultiQueryReduction [DecidableEq X] [DecidableEq Y] (Q : ℕ)
    (A : ProbComp (List {xs : List X // xs.length ≤ ℓ})) :
    ProbOracleComp (fun _ : X × Fin ℓ => Y) Bool := do
  let ms ← ProbOracleComp.sample A
  let tagged ← (ms.take Q).mapM fun m => (m, ·) <$> xorHashQueries m
  return decide (∃ a ∈ tagged, ∃ b ∈ tagged, a.1 ≠ b.1 ∧ a.2 = b.2)

/-- The wrapper makes at most `Q * ℓ` oracle queries, including on outputs longer than `Q`. -/
theorem isQueryBounded_xorHashMultiQueryReduction [DecidableEq X] [DecidableEq Y] (Q : ℕ)
    (A : ProbComp (List {xs : List X // xs.length ≤ ℓ})) :
    (xorHashMultiQueryReduction (Y := Y) Q A).IsQueryBounded (Q * ℓ) := by
  rw [xorHashMultiQueryReduction, ← Nat.zero_add (Q * ℓ)]
  refine (ProbOracleComp.IsQueryBounded.sample A).bind fun ms => ?_
  have htraverse := OracleComp.IsCostBounded.mapM (inputs := ms.take Q) fun m _ =>
    (OracleComp.isCostBounded_map_iff (m, ·) (xorHashQueries (Y := Y) m) ℓ).mpr
      (isQueryBounded_xorHashQueries m)
  refine (htraverse.bind fun _ => OracleComp.IsCostBounded.pure _ 0).mono ?_
  simpa only [Nat.add_zero] using Nat.mul_le_mul_right ℓ (List.length_take_le Q ms)

private theorem run_xorHashMultiQueryReduction [DecidableEq X] [DecidableEq Y]
    (f : X × Fin ℓ → Y) (Q : ℕ) (A : ProbComp (List {xs : List X // xs.length ≤ ℓ})) :
    (xorHashMultiQueryReduction Q A).run (fun x => pure (f x)) = do
      let ms ← A
      return decide (∃ m ∈ ms.take Q, ∃ m' ∈ ms.take Q, m ≠ m' ∧ xorHash f m = xorHash f m') := by
  simp only [xorHashMultiQueryReduction, ProbOracleComp.run_bind, ProbOracleComp.run_sample]
  refine bind_congr fun ms => ?_
  simp only [ProbOracleComp.run_mapM, ProbOracleComp.run_map, run_xorHashQueries,
    map_pure, List.mapM_pure, pure_bind, ProbOracleComp.run_pure, List.mem_map,
    exists_exists_and_eq_and]

/-- For a bounded list adversary, the real PRF experiment has the same law as the full
multi-query game. Every supported message list is evaluated in full. -/
theorem eval_realExperiment_xorHashMultiQueryReduction [Fintype K] [Nonempty K]
    [DecidableEq X] [DecidableEq Y] (F : K → X × Fin ℓ → Y)
    (A : ProbComp (List {xs : List X // xs.length ≤ ℓ})) {Q : ℕ}
    (hQ : ∀ ms ∈ (ProbComp.eval A).support, ms.length ≤ Q) :
    ProbComp.eval (PRF.realExperiment F (xorHashMultiQueryReduction Q A)) =
      ProbComp.eval (multiQueryExperiment (fun k => xorHash (F k)) A) := by
  simp only [PRF.realExperiment, multiQueryExperiment, run_xorHashMultiQueryReduction,
    ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  rw [PMF.bind_comm]
  refine Probability.PMF.bind_congr_on_support _ _ _ fun ms hms => ?_
  rw [List.take_of_length_le (hQ ms hms)]

end Queries

variable {X Y K : Type} {ℓ : ℕ} [Fintype K] [Nonempty K] [Fintype X] [DecidableEq X]
  [Fintype Y] [AddCommGroup Y] [DecidableEq Y]

/-- A finite-game step toward Theorem 7.6 ([BonehShoup2023], v0.6, §7.2.3, (7.12)).
The explicit wrapper bounds collision success by its PRF advantage plus `1 / |Y|`.
Its external queries are bounded by `2 * ℓ`. The uniform strict PPT result remains open. -/
theorem eval_collisionExperiment_xorHash_le_prfAdvantage (F : K → X × Fin ℓ → Y)
    (A : ProbComp (CollisionGuess {xs : List X // xs.length ≤ ℓ})) :
    ProbComp.eval (collisionExperiment (fun k => xorHash (F k)) A) true ≤
      (PRF.advantage F (xorHashCollisionReduction A) : ℝ≥0∞) +
        (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  let B := xorHashCollisionReduction (Y := Y) A
  have hideal : ProbComp.eval (PRF.idealExperiment B) =
      ProbComp.eval (collisionExperiment (fun f : X × Fin ℓ → Y => xorHash f) A) :=
    eval_realExperiment_xorHashCollisionReduction (fun f => f) A
  have hbound := (isUniversalHash_iff_eval_collisionExperiment_le
    (xorHash (X := X) (Y := Y) (ℓ := ℓ)) _).mp isDeltaUniversalHash_xorHash.isUniversalHash A
  rw [← eval_realExperiment_xorHashCollisionReduction F A]
  refine (Game.apply_true_le_of_advantage_le (c := PRF.advantage F B) le_rfl).1.trans ?_
  rw [hideal, add_comm]
  exact add_le_add_right hbound _

/-- A finite-game step toward Exercise 7.28 ([BonehShoup2023], v0.6, p. 285). The explicit
wrapper uses at most `Q * ℓ` queries. Its ideal-table loss is `Q.choose 2 / |Y|` because a
collision uses one unordered pair. The asymptotic efficiency certificate remains open. -/
theorem eval_multiQueryExperiment_xorHash_le_prfAdvantage (F : K → X × Fin ℓ → Y)
    (A : ProbComp (List {xs : List X // xs.length ≤ ℓ})) {Q : ℕ}
    (hQ : ∀ ms ∈ (ProbComp.eval A).support, ms.length ≤ Q) :
    ProbComp.eval (multiQueryExperiment (fun k => xorHash (F k)) A) true ≤
      (PRF.advantage F (xorHashMultiQueryReduction Q A) : ℝ≥0∞) +
        (Q.choose 2 : ℕ) * (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  let B := xorHashMultiQueryReduction (Y := Y) Q A
  have hideal : ProbComp.eval (PRF.idealExperiment B) =
      ProbComp.eval (multiQueryExperiment (fun f : X × Fin ℓ → Y => xorHash f) A) :=
    eval_realExperiment_xorHashMultiQueryReduction (fun f => f) A hQ
  have hbound := eval_multiQueryExperiment_le
    (isDeltaUniversalHash_xorHash (X := X) (Y := Y) (ℓ := ℓ)).isUniversalHash hQ
  rw [← eval_realExperiment_xorHashMultiQueryReduction F A hQ]
  refine (Game.apply_true_le_of_advantage_le (c := PRF.advantage F B) le_rfl).1.trans ?_
  rw [hideal, add_comm]
  exact add_le_add_right hbound _

end Cslib.Crypto.UHF
