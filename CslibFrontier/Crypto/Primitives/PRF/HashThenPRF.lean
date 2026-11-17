/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.PRF.Finite
public import CslibFrontier.Crypto.Primitives.UHF.Finite
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Languages.Probabilistic.Memoize
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm
import CslibFrontier.Languages.Probabilistic.Oracle.RunState
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.QueryCount
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.RunWith
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic
import CslibFrontier.Languages.Probabilistic.RandomOracle.Through
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.UniformPoint

/-!
# Composition of a pseudorandom function with a universal hash function

Applying a pseudorandom function `F` to the digest of a keyed hash function `H` gives
`F'((k₁, k₂), m) = F(k₂, H(k₁, m))` (`Cslib.Crypto.PRF.hashThenPRF`; [BonehShoup2023],
Section 7.3, equation (7.18), p. 262). For finite key, message, digest and output types,
`Cslib.Crypto.PRF.advantage_hashThenPRF_le_add_multiQuery` (equation (7.20), p. 263) bounds the
PRF advantage of any adaptive adversary `A` against `hashThenPRF H F` by the PRF advantage of
`Cslib.Crypto.PRF.hashReduction H A` (`B_F`) against `F` plus the winning probability of
`Cslib.Crypto.PRF.idealQueries A` (`B'_H`) in the multi-query universal-hash game
`Cslib.Crypto.UHF.multiQueryExperiment H`. When `H` is `ε`-universal against every adversary
(`Cslib.Probability.IsUniversalHash`) and `A` makes at most `Q` queries on every path,
`Cslib.Crypto.PRF.advantage_hashThenPRF_le` bounds that second term by `Q.choose 2 * ε`.

This module stays at the finite query-bound level without running-time certificates:
`hashReduction` and `idealQueries` carry query-count / output-length certificates
(`Cslib.Crypto.PRF.isQueryBounded_hashReduction`,
`Cslib.Crypto.PRF.length_le_of_mem_support_idealQueries`), not `IsPPT` or `IsOraclePPT`
certificates, and `IsUniversalHash` is statistical rather than a computational UHF
(Definition 7.2). No asymptotic negligible-advantage theorem is proved here: these are concrete,
finite-type bounds, `hashReduction` has no efficiency witness yet, and the asymptotic Theorem 7.7
with that witness is owned by
[#5790](https://github.com/cslib-community/cslib-frontier/issues/5790).

Conversely, `Cslib.Crypto.PRF.toOuterMeasure_collision_le_advantage_collisionDistinguisher`
formalizes the observation of Section 7.3 (p. 263) that two distinct messages colliding with
probability `δ` give a two-query distinguisher (`Cslib.Crypto.PRF.collisionDistinguisher`) of
advantage at least `δ - 1 / |Z|` against `hashThenPRF H F`.

## Main definitions

* `Cslib.Crypto.PRF.hashThenPRF`: `(7.18)`, `F'((k₁, k₂), m) = F(k₂, H(k₁, m))`.
* `Cslib.Crypto.PRF.hashReduction`: the PRF reduction `B_F` for Theorem 7.7.
* `Cslib.Crypto.PRF.idealQueries`: the multi-query UHF adversary `B'_H` simulating an ideal PRF.
* `Cslib.Crypto.PRF.collisionDistinguisher`: the two-query collision test.

## Main results

* `Cslib.Crypto.PRF.isQueryBounded_hashReduction`: `B_F` preserves query budgets.
* `Cslib.Crypto.PRF.length_le_of_mem_support_idealQueries`: `B'_H` outputs at most `Q` messages.
* `Cslib.Crypto.PRF.eval_realExperiment_hashThenPRF`: Game 0 is the real experiment of `B_F`, a
  step toward `(7.21)`.
* `Cslib.Crypto.PRF.advantage_idealExperiment_hashReduction_le`: Game 1 to Game 2, `(7.22)`.
* `Cslib.Crypto.PRF.advantage_hashThenPRF_le_add_multiQuery`: equation `(7.20)`.
* `Cslib.Crypto.PRF.advantage_hashThenPRF_le`: Theorem 7.7 for a statistical `ε`-UHF.
* `Cslib.Crypto.PRF.isQueryBounded_collisionDistinguisher`: the collision distinguisher makes `2`
  queries.
* `Cslib.Crypto.PRF.toOuterMeasure_collision_le_advantage_collisionDistinguisher`: collision lower
  bound on advantage against `hashThenPRF H F`.

## Implementation notes

`collisionDistinguisher` is not exposed. For `module` callers,
`Cslib.Crypto.PRF.eval_realExperiment_collisionDistinguisher` and
`Cslib.Crypto.PRF.eval_idealExperiment_collisionDistinguisher` give its output laws in the two
experiments.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 7.3, equations (7.18), (7.20)–(7.22), and Theorem 7.7,
  pp. 262–265.
-/

public section

namespace Cslib.Crypto.PRF

open Cslib.Probability
open scoped ENNReal NNReal

variable {K₁ K₂ M Y Z : Type}

/-- Equation (7.18) ([BonehShoup2023], Version 0.6, Section 7.3, p. 262):
`F'((k₁, k₂), m) = F(k₂, H(k₁, m))`. -/
@[expose] def hashThenPRF (H : K₁ → M → Y) (F : K₂ → Y → Z) (k : K₁ × K₂) (m : M) : Z :=
  F k.2 (H k.1 m)

/-- The adversary `B_F` of Theorem 7.7 ([BonehShoup2023], Version 0.6, Section 7.3, p. 263):
sample a hash key, run `A`, and forward each query through `H k`. -/
noncomputable def hashReduction [Fintype K₁] [Nonempty K₁] (H : K₁ → M → Y)
    (A : Adversary M Z) : ProbOracleComp (fun _ : Y => Z) Bool := do
  let k ← ProbOracleComp.sample (ProbComp.uniform K₁)
  ProbOracleComp.simulate (fun m => ProbOracleComp.query (H k m)) A

/-- `B_F` makes one query per query of `A`. -/
theorem isQueryBounded_hashReduction [Fintype K₁] [Nonempty K₁] (H : K₁ → M → Y)
    {A : Adversary M Z} {Q : ℕ} (hQ : A.IsQueryBounded Q) :
    (hashReduction H A).IsQueryBounded Q := by
  rw [hashReduction, ← Nat.zero_add Q]
  exact (ProbOracleComp.IsQueryBounded.sample (ProbComp.uniform K₁)).bind fun k =>
    hQ.simulate fun m => ProbOracleComp.IsQueryBounded.query (H k m)

/-- The adversary `B'_H` named in (7.20) (p. 263) and constructed in Game 2 (p. 264) of
[BonehShoup2023] (Version 0.6, Section 7.3): run `A` against a lazily sampled random function on
`M` and output the list of distinct queries it cached. -/
noncomputable def idealQueries [DecidableEq M] [Fintype Z] [Nonempty Z]
    (A : Adversary M Z) : ProbComp (List M) :=
  (fun z => z.2.map Prod.fst) <$>
    (A.runState (memoize fun _ : M => ProbComp.uniform Z)).run []

/-- `B'_H` outputs at most as many messages as `A` makes queries. -/
theorem length_le_of_mem_support_idealQueries [DecidableEq M] [Fintype Z] [Nonempty Z]
    {A : Adversary M Z} {Q : ℕ} (hQ : A.IsQueryBounded Q) {ms : List M}
    (hms : ms ∈ (ProbComp.eval (idealQueries A)).support) : ms.length ≤ Q := by
  rw [idealQueries, ProbComp.eval_map, PMF.mem_support_map_iff] at hms
  rcases hms with ⟨⟨r, cache⟩, hmem, rfl⟩
  rw [ProbOracleComp.eval_runState] at hmem
  have hmem' : (r, cache) ∈ (ProbOracleComp.runWith
      (memoize fun _ : M => PMF.uniformOfFintype Z) A []).support := by
    simpa only [ProbComp.eval_memoize, ProbComp.eval_uniform] using hmem
  have hbounds := (RandomOracle.memoize_cache_bounds_prob
    (fun _ : M => PMF.uniformOfFintype Z) A (fun _ => 0) Q 0 hQ
    (ProbOracleComp.QueriesSatisfy.of_forall (fun _ => le_rfl) A) [] cache r hmem').1
  simpa only [List.length_map, List.length_nil, Nat.zero_add] using hbounds

/-- Law of `idealQueries A` in terms of `ProbOracleComp.runWith (memoize _)`. -/
private theorem eval_idealQueries [DecidableEq M] [Fintype Z] [Nonempty Z] (A : Adversary M Z) :
    ProbComp.eval (idealQueries A) =
      (ProbOracleComp.runWith (memoize fun _ : M => PMF.uniformOfFintype Z) A
        []).map fun z => z.2.map Prod.fst := by
  simp only [idealQueries, ProbComp.eval_map, ProbOracleComp.eval_runState,
    ProbComp.eval_memoize, ProbComp.eval_uniform]

/-- Game 0 of the proof of Theorem 7.7 ([BonehShoup2023], Version 0.6, Section 7.3, pp. 263–264),
a step toward equation (7.21): the real experiment of `A` against `hashThenPRF H F` has the same
distribution as the real experiment of `hashReduction H A` (`B_F`) against `F`. -/
theorem eval_realExperiment_hashThenPRF [Fintype K₁] [Nonempty K₁] [Fintype K₂] [Nonempty K₂]
    (H : K₁ → M → Y) (F : K₂ → Y → Z) (A : Adversary M Z) :
    ProbComp.eval (realExperiment (hashThenPRF H F) A) =
      ProbComp.eval (realExperiment F (hashReduction H A)) := by
  rw [eval_realExperiment, eval_realExperiment, hashReduction, ← PMF.uniformOfFintype_prod,
    PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]
  rw [PMF.bind_comm]
  refine congrArg ((PMF.uniformOfFintype K₂).bind) (funext fun k₂ => ?_)
  simp only [interp_norm, pmf_norm, ProbComp.eval_uniform, ProbOracleComp.interpret_simulate,
    hashThenPRF]

/-- The ideal experiment of `B_F` evaluated via `RandomOracle.answer` on the simulated program. -/
private theorem eval_idealExperiment_hashReduction [Fintype K₁] [Nonempty K₁] [Fintype Y]
    [DecidableEq Y] [Fintype Z] [Nonempty Z] (H : K₁ → M → Y) (A : Adversary M Z) :
    ProbComp.eval (idealExperiment (hashReduction H A)) =
      (PMF.uniformOfFintype K₁).bind fun k =>
        (ProbOracleComp.runWith (RandomOracle.answer fun _ : Y => PMF.uniformOfFintype Z)
          (ProbOracleComp.simulate (fun m => ProbOracleComp.query (H k m)) A)
          (fun _ => none)).map Prod.fst := by
  rw [eval_idealExperiment]
  refine (RandomOracle.uniform_interpret_prob_eq_lazy (Response := fun _ : Y => Z)
    (hashReduction H A)).trans ?_
  rw [hashReduction, ProbOracleComp.runWith_sample_bind, PMF.map_bind, ProbComp.eval_uniform]

/-- Winning Attack Game 7.2 with `idealQueries A` expressed as the average over hash keys of
an image collision in the lazy memoization cache. -/
private theorem eval_multiQueryExperiment_idealQueries_true [Fintype K₁] [Nonempty K₁]
    [DecidableEq M] [DecidableEq Y] [Fintype Z] [Nonempty Z] (H : K₁ → M → Y)
    (A : Adversary M Z) :
    ProbComp.eval (UHF.multiQueryExperiment H (idealQueries A)) true =
      ∑' k, PMF.uniformOfFintype K₁ k *
        (ProbOracleComp.runWith (memoize fun _ : M => PMF.uniformOfFintype Z) A
          []).toOuterMeasure {x | RandomOracle.HasImageCollision (H k) x.2} := by
  simp only [UHF.multiQueryExperiment, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure, eval_idealQueries, PMF.bind_map, Function.comp_def]
  rw [PMF.bind_comm, PMF.bind_apply]
  refine tsum_congr fun k => congrArg (PMF.uniformOfFintype K₁ k * ·) ?_
  rw [Probability.PMF.bind_pure_decide_apply_true]
  refine congrArg
    (fun s => (ProbOracleComp.runWith (memoize fun _ : M => PMF.uniformOfFintype Z) A
      []).toOuterMeasure s)
    (Set.ext fun x => ?_)
  exact (RandomOracle.hasImageCollision_iff (H k) x.2).symm

/-- Equation (7.22) ([BonehShoup2023], Version 0.6, Section 7.3, p. 264), Games 1 and 2: against
a uniform function, hashing the queries first changes the adversary's output only when two
distinct queries collide under the hash key. -/
theorem advantage_idealExperiment_hashReduction_le [Fintype K₁] [Nonempty K₁] [Fintype M]
    [DecidableEq M] [Fintype Y] [DecidableEq Y] [Fintype Z] [Nonempty Z] (H : K₁ → M → Y)
    (A : Adversary M Z) :
    (Game.advantage (ProbComp.eval (idealExperiment (hashReduction H A)))
        (ProbComp.eval (idealExperiment A)) : ℝ≥0∞) ≤
      ProbComp.eval (UHF.multiQueryExperiment H (idealQueries A)) true := by
  rw [Game.advantage_comm, ← Game.closeTo_iff_coe_advantage_le,
    eval_idealExperiment_eq_runWith_memoize, eval_idealExperiment_hashReduction,
    eval_multiQueryExperiment_idealQueries_true]
  have hconst : (ProbOracleComp.runWith
      (memoize fun _ : M => PMF.uniformOfFintype Z) A []).map Prod.fst =
      (PMF.uniformOfFintype K₁).bind fun _ =>
        (ProbOracleComp.runWith
          (memoize fun _ : M => PMF.uniformOfFintype Z) A []).map Prod.fst :=
    (PMF.bind_const _ _).symm
  rw [hconst]
  exact Probability.CloseTo.bind_right_tsum (PMF.uniformOfFintype K₁) fun k _ =>
    RandomOracle.closeTo_runWith_memoize_simulate_query (H k) (PMF.uniformOfFintype Z) A

/-- Equation (7.20) ([BonehShoup2023], Version 0.6, Section 7.3, p. 263): for every `H`, `F`,
and adversary `A`, the distinguishing advantage against `hashThenPRF H F` is bounded by the
advantage of `hashReduction H A` against `F` plus the probability that `idealQueries A` wins
the multi-query UHF game against `H`. -/
theorem advantage_hashThenPRF_le_add_multiQuery [Fintype K₁] [Nonempty K₁] [Fintype K₂]
    [Nonempty K₂] [Fintype M] [DecidableEq M] [Fintype Y] [DecidableEq Y] [Fintype Z]
    [Nonempty Z] (H : K₁ → M → Y) (F : K₂ → Y → Z) (A : Adversary M Z) :
    (advantage (hashThenPRF H F) A : ℝ≥0∞) ≤
      advantage F (hashReduction H A) +
        ProbComp.eval (UHF.multiQueryExperiment H (idealQueries A)) true := by
  have htri : advantage (hashThenPRF H F) A ≤
      advantage F (hashReduction H A) +
        Game.advantage (ProbComp.eval (idealExperiment (hashReduction H A)))
          (ProbComp.eval (idealExperiment A)) := by
    rw [advantage, eval_realExperiment_hashThenPRF]
    exact Game.advantage_triangle _ (ProbComp.eval (idealExperiment (hashReduction H A))) _
  refine (ENNReal.coe_le_coe.mpr htri).trans ?_
  rw [ENNReal.coe_add]
  exact add_le_add le_rfl (advantage_idealExperiment_hashReduction_le H A)

/-- Theorem 7.7 ([BonehShoup2023], Version 0.6, Section 7.3, p. 263) for finite types and a
statistical `ε`-universal hash family, with a query-bounded adversary and no running-time
certificate: `advantage (hashThenPRF H F) A ≤ advantage F (hashReduction H A) + C(Q, 2) · ε`. -/
theorem advantage_hashThenPRF_le [Fintype K₁] [Nonempty K₁] [Fintype K₂] [Nonempty K₂]
    [Fintype M] [DecidableEq M] [Fintype Y] [DecidableEq Y] [Fintype Z] [Nonempty Z]
    {H : K₁ → M → Y} {ε : ℝ≥0∞} (hH : IsUniversalHash (PMF.uniformOfFintype K₁) H ε)
    (F : K₂ → Y → Z) {A : Adversary M Z} {Q : ℕ} (hQ : A.IsQueryBounded Q) :
    (advantage (hashThenPRF H F) A : ℝ≥0∞) ≤
      advantage F (hashReduction H A) + (Q.choose 2 : ℕ) * ε :=
  (advantage_hashThenPRF_le_add_multiQuery H F A).trans
    (add_le_add le_rfl
      (UHF.eval_multiQueryExperiment_le hH fun _ hms =>
        length_le_of_mem_support_idealQueries hQ hms))

/-- The two-query collision distinguisher of [BonehShoup2023] (Version 0.6, Section 7.3, p. 263):
query `m₀` and `m₁` and accept when their replies agree. -/
def collisionDistinguisher [DecidableEq Z] (m₀ m₁ : M) : ProbOracleComp (fun _ : M => Z) Bool := do
  let t₀ ← ProbOracleComp.query m₀
  let t₁ ← ProbOracleComp.query m₁
  return decide (t₀ = t₁)

/-- `collisionDistinguisher m₀ m₁` makes at most two external queries. -/
theorem isQueryBounded_collisionDistinguisher [DecidableEq Z] (m₀ m₁ : M) :
    (collisionDistinguisher (Z := Z) m₀ m₁).IsQueryBounded 2 := by
  rw [collisionDistinguisher]
  exact ((ProbOracleComp.IsQueryBounded.query m₀).bind fun _ =>
    (ProbOracleComp.IsQueryBounded.query m₁).bind fun _ =>
      OracleComp.IsCostBounded.pure _ 0).mono (by omega)

/-- Output distribution of `collisionDistinguisher m₀ m₁` in the real experiment against
`hashThenPRF H F`. -/
theorem eval_realExperiment_collisionDistinguisher [Fintype K₁] [Nonempty K₁] [Fintype K₂]
    [Nonempty K₂] [DecidableEq Z] (H : K₁ → M → Y) (F : K₂ → Y → Z) (m₀ m₁ : M) :
    ProbComp.eval (realExperiment (hashThenPRF H F) (collisionDistinguisher m₀ m₁)) =
      (PMF.uniformOfFintype (K₁ × K₂)).bind fun k =>
        PMF.pure (decide (F k.2 (H k.1 m₀) = F k.2 (H k.1 m₁))) := by
  rw [eval_realExperiment, collisionDistinguisher]
  simp only [interp_norm, pmf_norm, hashThenPRF]

/-- Output distribution of `collisionDistinguisher m₀ m₁` in the ideal PRF experiment. -/
theorem eval_idealExperiment_collisionDistinguisher [Fintype M] [DecidableEq M] [Fintype Z]
    [Nonempty Z] [DecidableEq Z] (m₀ m₁ : M) :
    ProbComp.eval (idealExperiment (collisionDistinguisher (Z := Z) m₀ m₁)) =
      (PMF.uniformOfFintype (M → Z)).bind fun f => PMF.pure (decide (f m₀ = f m₁)) := by
  rw [eval_idealExperiment, collisionDistinguisher]
  simp only [interp_norm, pmf_norm]

/-- If `m₀ ≠ m₁` collide under `H` with probability `δ` over the uniform hash key, the two-query
distinguisher `collisionDistinguisher m₀ m₁` achieves advantage at least `δ - 1 / |Z|` against
`hashThenPRF H F`, for every `F` ([BonehShoup2023], Version 0.6, Section 7.3, p. 263). -/
theorem toOuterMeasure_collision_le_advantage_collisionDistinguisher [Fintype K₁] [Nonempty K₁]
    [Fintype K₂] [Nonempty K₂] [Fintype M] [DecidableEq M] [Fintype Z] [Nonempty Z]
    [DecidableEq Z] (H : K₁ → M → Y) (F : K₂ → Y → Z) {m₀ m₁ : M} (hm : m₀ ≠ m₁) :
    (PMF.uniformOfFintype K₁).toOuterMeasure {k | H k m₀ = H k m₁} ≤
      advantage (hashThenPRF H F) (collisionDistinguisher m₀ m₁) +
        (Fintype.card Z : ℝ≥0∞)⁻¹ := by
  have hideal :
      ProbComp.eval (idealExperiment (collisionDistinguisher (Z := Z) m₀ m₁)) true =
        (Fintype.card Z : ℝ≥0∞)⁻¹ := by
    rw [eval_idealExperiment_collisionDistinguisher]
    let e : Bool ↪ M :=
      ⟨fun b => bif b then m₀ else m₁,
        fun a b hab => by
          cases a <;> cases b <;> first | rfl | exact absurd hab hm | exact absurd hab hm.symm⟩
    have hmap : ((PMF.uniformOfFintype (M → Z)).bind fun f =>
        PMF.pure (decide (f m₀ = f m₁))) =
        ((PMF.uniformOfFintype (Bool → Z)).bind fun g =>
          PMF.pure (decide (g true = g false))) := by
      rw [← Probability.PMF.uniformOfFintype_pi_map_comp_embedding e, PMF.bind_map]
      rfl
    have hpair : ((PMF.uniformOfFintype (Bool → Z)).bind fun g =>
        PMF.pure (decide (g true = g false))) =
        (PMF.uniformOfFintype (Z × Z)).bind fun p => PMF.pure (decide (p.1 = p.2)) := by
      rw [← Probability.PMF.uniformOfFintype_map_equiv
        ((Equiv.boolArrowEquivProd Z).trans (Equiv.prodComm Z Z)), PMF.bind_map]
      rfl
    rw [hmap, hpair, ← Probability.PMF.uniformOfFintype_prod, PMF.bind_bind]
    refine Probability.PMF.bind_apply_of_forall _ fun z₀ => ?_
    simpa only [PMF.bind_map, Function.comp_def] using
      Probability.PMF.uniformOfFintype_bind_decide_eq_apply_true z₀
  have hreal : (PMF.uniformOfFintype K₁).toOuterMeasure {k | H k m₀ = H k m₁} ≤
      ProbComp.eval (realExperiment (hashThenPRF H F) (collisionDistinguisher m₀ m₁)) true := by
    rw [eval_realExperiment_collisionDistinguisher, Probability.PMF.bind_pure_decide_apply_true,
      ← Probability.PMF.uniformOfFintype_prod_map_fst (β := K₂), PMF.toOuterMeasure_map_apply]
    exact (PMF.uniformOfFintype (K₁ × K₂)).toOuterMeasure.mono fun k hk => congrArg (F k.2) hk
  have hclose := (Game.closeTo_iff_coe_advantage_le
    (game1 := ProbComp.eval (realExperiment (hashThenPRF H F) (collisionDistinguisher m₀ m₁)))
    (game2 := ProbComp.eval (idealExperiment (collisionDistinguisher (Z := Z) m₀ m₁)))).mpr
    le_rfl {true}
  simp only [PMF.toOuterMeasure_apply_singleton] at hclose
  rw [add_comm] at hclose
  exact hreal.trans (hclose.trans (by rw [hideal]))

end Cslib.Crypto.PRF
