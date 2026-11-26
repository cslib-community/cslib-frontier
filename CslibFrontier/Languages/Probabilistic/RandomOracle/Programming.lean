/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.RandomOracle
public import CslibFrontier.Languages.Probabilistic.UntilBad.Flag
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Union
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Tactic.SuppCases

/-!
# Random-oracle min-entropy programming and birthday collision bounds

Two quantitative patterns recur throughout random-oracle security proofs:

1. **Min-entropy programming (`toOuterMeasure_exists_mem_fst_eq_le`, `lazyProgramHandler`,
   `overwriteProgramHandler`)**: an oracle handler (such as a Fiat–Shamir signer or NIZK simulator)
   samples pre-challenge coins `ts` whose hash query `point req ts` has guessing probability at most
   `δ`, and programs `(point req ts) ↦ c` with a fresh `c ← dist` instead of querying the lazy
   random oracle `memoize (fun _ => dist)`. By `withBadFlag` and the two-cost triangular union bound
   `OracleComp.toOuterMeasure_bad_choose_two_cost_le`, an adaptive program making at most `q_S`
   programming calls and `q_H` direct random-oracle calls hits an already-cached point during
   programming with probability at most `(q_S * cache.length + q_S * q_H + q_S.choose 2) * δ` (hence
   `(q_S * q_H + q_S.choose 2) * δ ≤ q_S * (q_S + q_H) * δ` from an empty cache), bounding the
   `CloseTo` distance between lazy and programmed executions for both `OracleComp` and
   `ProbOracleComp.runWith`.
2. **Random-function output-collision birthday bound (`HasOutputCollision`,
   `toOuterMeasure_collision_memoize_uniform_le`,
   `toOuterMeasure_hasOutputCollision_memoize_uniform_le`)**: an adaptive `q`-query `OracleComp` or
   `ProbOracleComp` interacting with `memoize (fun _ => PMF.uniformOfFintype Digest)` from an empty
   cache observes two distinct queried keys with the same digest (`HasOutputCollision`, equivalent
   on duplicate-free key caches to `¬(cache.map Prod.snd).Nodup`) with probability at most
   `q.choose 2 / Fintype.card Digest`.

## Main definitions

* `Cslib.RandomOracle.lazyProgramHandler`, `Cslib.RandomOracle.overwriteProgramHandler`,
  `Cslib.RandomOracle.flaggedLazyProgramHandler`,
  `Cslib.RandomOracle.flaggedOverwriteProgramHandler`: two-channel lazy vs. fresh-overwrite
  random-oracle programming handlers and their monotone-flag collision wrappers.
* `Cslib.RandomOracle.HasOutputCollision`: existence of two cache entries with distinct keys and
  equal digests.

## Main results

* `Cslib.RandomOracle.toOuterMeasure_exists_mem_fst_eq_le`,
  `Cslib.RandomOracle.map_comp_apply_le_of_injective`: min-entropy list-key collision bound and
  injective key-embedding preservation.
* `Cslib.RandomOracle.flaggedLazyProgramHandler_apply_inl`,
  `Cslib.RandomOracle.flaggedLazyProgramHandler_apply_inr`,
  `Cslib.RandomOracle.identicalUntilBad_flaggedProgramHandlers`,
  `Cslib.RandomOracle.run_flaggedLazyProgramHandler_map_fst`,
  `Cslib.RandomOracle.run_flaggedOverwriteProgramHandler_map_fst`: flagged programming
  transition equations, `IdenticalUntilBad`, and marginal-projection laws.
* `Cslib.RandomOracle.toOuterMeasure_bad_flaggedLazyProgramHandler_choose_two_le`,
  `Cslib.RandomOracle.toOuterMeasure_bad_flaggedLazyProgramHandler_le`,
  `Cslib.RandomOracle.closeTo_run_lazyProgramHandler_overwriteProgramHandler_choose_two`,
  `Cslib.RandomOracle.closeTo_run_lazyProgramHandler_overwriteProgramHandler`,
  `Cslib.RandomOracle.closeTo_run_lazyProgramHandler_overwriteProgramHandler_of_isQueryBounded`,
  `Cslib.RandomOracle.closeTo_runWith_lazyProgramHandler_overwriteProgramHandler_choose_two`,
  `Cslib.RandomOracle.closeTo_runWith_lazyProgramHandler_overwriteProgramHandler`: adaptive
  random-oracle programming collision and `CloseTo` bounds for `OracleComp` and `ProbOracleComp`.
* `Cslib.RandomOracle.nodup_fst_of_mem_support_run_memoize`,
  `Cslib.RandomOracle.hasOutputCollision_iff_not_nodup_snd`,
  `Cslib.RandomOracle.toOuterMeasure_not_nodup_snd_memoize_le`,
  `Cslib.RandomOracle.toOuterMeasure_not_nodup_snd_runWith_memoize_le`,
  `Cslib.RandomOracle.toOuterMeasure_collision_memoize_uniform_le`,
  `Cslib.RandomOracle.toOuterMeasure_collision_runWith_memoize_uniform_le`,
  `Cslib.RandomOracle.toOuterMeasure_hasOutputCollision_memoize_uniform_le`,
  `Cslib.RandomOracle.toOuterMeasure_hasOutputCollision_runWith_memoize_uniform_le`: `q`-query
  random-oracle output-collision birthday bounds.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Theorem 4.7, Section 19.6.1, and Section 20.3.5.
-/

public section

namespace Cslib.RandomOracle

open Probability OracleComp
open scoped ENNReal

/-! ### Min-entropy cache-lookup bounds -/

section MinEntropyLookup

/-- **Min-entropy list-key collision bound**: if every value of `f` occurs under `μ` with
probability at most `δ` (`∀ q, (μ.map f) q ≤ δ`), then `f a` matches the key of some entry in
`cache` with probability at most `cache.length * δ`. -/
theorem toOuterMeasure_exists_mem_fst_eq_le {α Query Value : Type*}
    {μ : PMF α} {f : α → Query} {δ : ℝ≥0∞}
    (hμ : ∀ q, (μ.map f) q ≤ δ) (cache : List (Query × Value)) :
    μ.toOuterMeasure {a | ∃ e ∈ cache, e.1 = f a} ≤ cache.length * δ := by
  have hpoint (q : Query) : μ.toOuterMeasure {a | f a = q} ≤ δ := by
    rw [show {a : α | f a = q} = f ⁻¹' {q} from rfl, ← PMF.toOuterMeasure_map_apply,
      PMF.toOuterMeasure_apply_singleton]
    exact hμ q
  simpa only [Set.ofPred_mem_eq, List.mem_map, List.length_map] using
    (PMF.toOuterMeasure_mem_list_le μ f hpoint (cache.map Prod.fst))

private theorem toOuterMeasure_lookup_isSome_le_aux {α Query Value : Type*}
    [BEq Query] [LawfulBEq Query] {μ : PMF α} {f : α → Query} {δ : ℝ≥0∞}
    (hμ : ∀ q, (μ.map f) q ≤ δ) (cache : List (Query × Value)) :
    μ.toOuterMeasure {a | (cache.lookup (f a)).isSome} ≤ cache.length * δ := by
  refine (μ.toOuterMeasure.mono fun a ha => ?_).trans
    (toOuterMeasure_exists_mem_fst_eq_le hμ cache)
  obtain ⟨e, he, hbeq⟩ := List.lookup_isSome_iff.mp ha
  exact ⟨e, he, (eq_of_beq hbeq).symm⟩

/-- Composing `g : α → β` with an injective map `emb : β → Query` preserves any pointwise
probability upper bound `∀ b, (μ.map g) b ≤ δ`. -/
theorem map_comp_apply_le_of_injective {α β Query : Type*} {μ : PMF α}
    {g : α → β} {emb : β → Query} (hemb : Function.Injective emb) {δ : ℝ≥0∞}
    (hμ : ∀ b, (μ.map g) b ≤ δ) (q : Query) :
    (μ.map (emb ∘ g)) q ≤ δ := by
  rw [← PMF.map_comp, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  by_cases hq : ∃ b, emb b = q
  · obtain ⟨b, rfl⟩ := hq
    have hpre : emb ⁻¹' {emb b} = {b} := Set.ext fun _ => hemb.eq_iff
    simpa only [hpre, PMF.toOuterMeasure_apply_singleton] using hμ b
  · rw [show emb ⁻¹' {q} = ∅ from Set.eq_empty_iff_forall_notMem.mpr fun b hb => hq ⟨b, hb⟩]
    simp

end MinEntropyLookup

/-! ### Adaptive random-oracle programming hop -/

section Programming

variable {Req Query Digest Log α : Type} {Reply : Req → Type} {Coins : Req → Type}

/-- Two-channel handler on `List (Query × Digest) × Log` whose active `.inl req` calls sample
`ts ← samplePre req`, query the lazy random oracle `memoize (fun _ => dist)` at `point req ts` for
`c`, and return `finish req ts c`; `.inr q` calls query `memoize (fun _ => dist) q`. -/
@[expose] noncomputable def lazyProgramHandler [BEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log) :
    (q : Req ⊕ Query) → StateT (List (Query × Digest) × Log) PMF
      ((Reply ⊕ₒ fun _ : Query => Digest) q)
  | .inl req => fun (cache, log) =>
    if h : active req = true then do
      let ts ← samplePre req
      let (c, cache') ← memoize (fun _ => dist) (point req ts) cache
      let (reply, log') := finish req ts c log
      return (reply, (cache', log'))
    else
      (inactive req (Bool.eq_false_iff.mpr h) log).map fun (reply, log') =>
        (reply, (cache, log'))
  | .inr q => fun (cache, log) =>
    (memoize (fun _ => dist) q cache).map fun (c, cache') => (c, (cache', log))

/-- Two-channel programmable-ROM handler matching `lazyProgramHandler` except that active `.inl req`
calls draw a fresh `c ← dist` and overwrite `(point req ts, c)` at the front of `cache` without
checking for an existing entry. -/
@[expose] noncomputable def overwriteProgramHandler
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log)
    [BEq Query] :
    (q : Req ⊕ Query) → StateT (List (Query × Digest) × Log) PMF
      ((Reply ⊕ₒ fun _ : Query => Digest) q)
  | .inl req => fun (cache, log) =>
    if h : active req = true then do
      let ts ← samplePre req
      let c ← dist
      let (reply, log') := finish req ts c log
      return (reply, ((point req ts, c) :: cache, log'))
    else
      (inactive req (Bool.eq_false_iff.mpr h) log).map fun (reply, log') =>
        (reply, (cache, log'))
  | .inr q => fun (cache, log) =>
    (memoize (fun _ => dist) q cache).map fun (c, cache') => (c, (cache', log))

private noncomputable def lazyProgramStep [BEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log) :
    (q : Req ⊕ Query) → List (Query × Digest) × Log →
      PMF (((Reply ⊕ₒ fun _ : Query => Digest) q) × ((List (Query × Digest) × Log) × Bool))
  | .inl req => fun (cache, log) =>
    if h : active req = true then
      (samplePre req).bind fun ts =>
        (memoize (fun _ => dist) (point req ts) cache).map fun res =>
          ((finish req ts res.1 log).1, ((res.2, (finish req ts res.1 log).2),
            (cache.lookup (point req ts)).isSome))
    else
      (inactive req (Bool.eq_false_iff.mpr h) log).map fun res =>
        (res.1, ((cache, res.2), false))
  | .inr q => fun (cache, log) =>
    (memoize (fun _ => dist) q cache).map fun res => (res.1, ((res.2, log), false))

private noncomputable def overwriteProgramStep [BEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log) :
    (q : Req ⊕ Query) → List (Query × Digest) × Log →
      PMF (((Reply ⊕ₒ fun _ : Query => Digest) q) × ((List (Query × Digest) × Log) × Bool))
  | .inl req => fun (cache, log) =>
    if h : active req = true then
      (samplePre req).bind fun ts =>
        dist.map fun c =>
          ((finish req ts c log).1, (((point req ts, c) :: cache, (finish req ts c log).2),
            (cache.lookup (point req ts)).isSome))
    else
      (inactive req (Bool.eq_false_iff.mpr h) log).map fun res =>
        (res.1, ((cache, res.2), false))
  | .inr q => fun (cache, log) =>
    (memoize (fun _ => dist) q cache).map fun res => (res.1, ((res.2, log), false))

/-- Flagged version of `lazyProgramHandler` latching `FlagBad` whenever an active `.inl req` call
samples a point `point req ts` already present in `cache`. -/
noncomputable def flaggedLazyProgramHandler [BEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log) :
    (q : Req ⊕ Query) → StateT ((List (Query × Digest) × Log) × Bool) PMF
      ((Reply ⊕ₒ fun _ : Query => Digest) q) :=
  withBadFlag (lazyProgramStep dist active inactive samplePre point finish)

/-- Flagged version of `overwriteProgramHandler` latching `FlagBad` whenever an active `.inl req`
call overwrites a point `point req ts` already present in `cache`. -/
noncomputable def flaggedOverwriteProgramHandler [BEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log) :
    (q : Req ⊕ Query) → StateT ((List (Query × Digest) × Log) × Bool) PMF
      ((Reply ⊕ₒ fun _ : Query => Digest) q) :=
  withBadFlag (overwriteProgramStep dist active inactive samplePre point finish)

/-- Explicit `.inl` transition equation for `flaggedLazyProgramHandler`. -/
theorem flaggedLazyProgramHandler_apply_inl [BEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log)
    (req : Req) (cache : List (Query × Digest)) (log : Log) (b : Bool) :
    flaggedLazyProgramHandler dist active inactive samplePre point finish (.inl req)
        ((cache, log), b) =
      if h : active req = true then
        (samplePre req).bind fun ts =>
          (memoize (fun _ => dist) (point req ts) cache).map fun res =>
            ((finish req ts res.1 log).1, ((res.2, (finish req ts res.1 log).2),
              b || (cache.lookup (point req ts)).isSome))
      else
        (inactive req (Bool.eq_false_iff.mpr h) log).map fun res =>
          (res.1, ((cache, res.2), b)) := by
  dsimp only [flaggedLazyProgramHandler, withBadFlag, lazyProgramStep]
  split_ifs with h <;>
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Prod.map, id_eq, Bool.or_false]

/-- Explicit `.inr` transition equation for `flaggedLazyProgramHandler`. -/
theorem flaggedLazyProgramHandler_apply_inr [BEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log)
    (q : Query) (cache : List (Query × Digest)) (log : Log) (b : Bool) :
    flaggedLazyProgramHandler dist active inactive samplePre point finish (.inr q)
        ((cache, log), b) =
      (memoize (fun _ => dist) q cache).map fun res => (res.1, ((res.2, log), b)) := by
  simp only [flaggedLazyProgramHandler, withBadFlag, lazyProgramStep, PMF.map_comp,
    Function.comp_def, Prod.map, id_eq, Bool.or_false]

private theorem lazyProgramStep_map_fst [BEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log)
    (q : Req ⊕ Query) (st : List (Query × Digest) × Log) :
    (lazyProgramStep dist active inactive samplePre point finish q st).map
        (Prod.map id Prod.fst) =
      lazyProgramHandler dist active inactive samplePre point finish q st := by
  obtain ⟨cache, log⟩ := st
  cases q with
  | inl req =>
    dsimp only [lazyProgramStep, lazyProgramHandler]
    split_ifs with h
    · simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind, PMF.map_comp]
      exact congrArg (PMF.bind _) (funext fun ts => (PMF.bind_pure_comp _ _).symm)
    · exact PMF.map_comp _ _ _
  | inr q => exact PMF.map_comp _ _ _

private theorem overwriteProgramStep_map_fst [BEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log)
    (q : Req ⊕ Query) (st : List (Query × Digest) × Log) :
    (overwriteProgramStep dist active inactive samplePre point finish q st).map
        (Prod.map id Prod.fst) =
      overwriteProgramHandler dist active inactive samplePre point finish q st := by
  obtain ⟨cache, log⟩ := st
  cases q with
  | inl req =>
    dsimp only [overwriteProgramStep, overwriteProgramHandler]
    split_ifs with h
    · simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind, PMF.map_comp]
      exact congrArg (PMF.bind _) (funext fun ts => (PMF.bind_pure_comp _ _).symm)
    · exact PMF.map_comp _ _ _
  | inr q => exact PMF.map_comp _ _ _

private theorem lazyProgramStep_agree_overwriteProgramStep [BEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log)
    (q : Req ⊕ Query) (st : List (Query × Digest) × Log)
    (a : (Reply ⊕ₒ fun _ : Query => Digest) q) (st' : List (Query × Digest) × Log) :
    lazyProgramStep dist active inactive samplePre point finish q st (a, (st', false)) =
      overwriteProgramStep dist active inactive samplePre point finish q st (a, (st', false)) := by
  obtain ⟨cache, log⟩ := st
  cases q with
  | inr q => rfl
  | inl req =>
    dsimp only [lazyProgramStep, overwriteProgramStep]
    split_ifs with h
    · simp only [PMF.bind_apply]
      refine tsum_congr fun ts => congrArg (_ * ·) ?_
      cases hlookup : cache.lookup (point req ts) with
      | some c₀ =>
        refine ((PMF.apply_eq_zero_iff _ _).mpr fun hx => ?_).trans
          ((PMF.apply_eq_zero_iff _ _).mpr fun hx => ?_).symm <;>
        · obtain ⟨_, -, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
          exact absurd (congrArg (·.2.2) heq) (by simp)
      | none =>
        rw [memoize_of_none _ _ _ hlookup]
        simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map]
        exact DFunLike.congr_fun (PMF.bind_pure_comp _ dist) _
    · rfl

/-- `flaggedLazyProgramHandler` and `flaggedOverwriteProgramHandler` agree until `FlagBad`. -/
theorem identicalUntilBad_flaggedProgramHandlers [BEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log) :
    IdenticalUntilBad
      (flaggedLazyProgramHandler dist active inactive samplePre point finish)
      (flaggedOverwriteProgramHandler dist active inactive samplePre point finish)
      FlagBad :=
  OracleComp.identicalUntilBad_withBadFlag
    (lazyProgramStep dist active inactive samplePre point finish)
    (overwriteProgramStep dist active inactive samplePre point finish)
    (lazyProgramStep_agree_overwriteProgramStep dist active inactive samplePre point finish)

/-- Dropping `FlagBad` on `flaggedLazyProgramHandler` recovers `lazyProgramHandler`. -/
theorem run_flaggedLazyProgramHandler_map_fst [BEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log)
    (program : OracleComp (Reply ⊕ₒ fun _ : Query => Digest) α)
    (st : List (Query × Digest) × Log) (b : Bool) :
    ((interpret (flaggedLazyProgramHandler dist active inactive samplePre point finish)
      program).run (st, b)).map (Prod.map id Prod.fst) =
      (interpret (lazyProgramHandler dist active inactive samplePre point finish) program).run st :=
  run_interpret_withBadFlag_map_fst
    (lazyProgramStep dist active inactive samplePre point finish)
    (lazyProgramHandler dist active inactive samplePre point finish)
    (lazyProgramStep_map_fst dist active inactive samplePre point finish)
    program st b

/-- Dropping `FlagBad` on `flaggedOverwriteProgramHandler` recovers `overwriteProgramHandler`. -/
theorem run_flaggedOverwriteProgramHandler_map_fst [BEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log)
    (program : OracleComp (Reply ⊕ₒ fun _ : Query => Digest) α)
    (st : List (Query × Digest) × Log) (b : Bool) :
    ((interpret (flaggedOverwriteProgramHandler dist active inactive samplePre point finish)
      program).run (st, b)).map (Prod.map id Prod.fst) =
      (interpret (overwriteProgramHandler dist active inactive samplePre point finish)
        program).run st :=
  run_interpret_withBadFlag_map_fst
    (overwriteProgramStep dist active inactive samplePre point finish)
    (overwriteProgramHandler dist active inactive samplePre point finish)
    (overwriteProgramStep_map_fst dist active inactive samplePre point finish)
    program st b

private theorem grow_length_memoize {Query Digest : Type} [BEq Query]
    (dist : PMF Digest) (key : Query) (cache : List (Query × Digest))
    (x : Digest × List (Query × Digest))
    (hx : x ∈ (memoize (fun _ => dist) key cache).support) :
    x.2.length ≤ cache.length + 1 := by
  rcases (mem_support_memoize_iff _ _ _ _).mp hx with ⟨-, h⟩ | ⟨-, -, h⟩ <;> simp [h]

private theorem step_bad_flaggedLazyProgramHandler_le [BEq Query] [LawfulBEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log)
    {δ : ℝ≥0∞} (hminEnt : ∀ req, active req = true → ∀ q, ((samplePre req).map (point req)) q ≤ δ)
    (q : Req ⊕ Query) (st : (List (Query × Digest) × Log) × Bool) (hst : ¬FlagBad st) :
    (flaggedLazyProgramHandler dist active inactive samplePre point finish q st).toOuterMeasure
      {x | FlagBad x.2} ≤
      (Sum.elim (fun _ : Req => 1) (fun _ : Query => 0) q * st.1.1.length : ℕ) * δ := by
  obtain ⟨⟨cache, log⟩, b⟩ := st
  obtain rfl := Bool.eq_false_iff.mpr hst
  simp only [flaggedLazyProgramHandler, withBadFlag_false]
  cases q with
  | inl req =>
    simp only [Sum.elim_inl, one_mul, lazyProgramStep]
    split_ifs with h
    · let inner (ts : Coins req) := (memoize (fun _ => dist) (point req ts) cache).map fun res =>
        ((finish req ts res.1 log).1, ((res.2, (finish req ts res.1 log).2),
          (cache.lookup (point req ts)).isSome))
      let hit : Set (Coins req) := {ts | (cache.lookup (point req ts)).isSome}
      change ((samplePre req).bind inner).toOuterMeasure {x | FlagBad x.2} ≤ _
      rw [PMF.toOuterMeasure_bind_apply]
      calc ∑' ts, (samplePre req) ts * (inner ts).toOuterMeasure {x | FlagBad x.2}
          ≤ ∑' ts, (samplePre req) ts * hit.indicator 1 ts := by
            refine tsum_le_tsum fun ts => mul_le_mul_of_nonneg_left ?_ zero_le
            by_cases hts : (cache.lookup (point req ts)).isSome = true
            · rw [Set.indicator_of_mem (s := hit) hts, Pi.one_apply]
              exact PMF.toOuterMeasure_le_one _ _
            · rw [Set.indicator_of_notMem (s := hit) hts]
              simp [inner, PMF.toOuterMeasure_map_apply, FlagBad, hts]
        _ = (samplePre req).toOuterMeasure hit :=
            (PMF.toOuterMeasure_eq_tsum_mul_indicator _ _).symm
        _ ≤ cache.length * δ := toOuterMeasure_lookup_isSome_le_aux (hminEnt req h) cache
    · simp [PMF.toOuterMeasure_map_apply, FlagBad]
  | inr q => simp [lazyProgramStep, PMF.toOuterMeasure_map_apply, FlagBad]

private theorem length_cache_flaggedLazyProgramHandler_le [BEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log)
    (q : Req ⊕ Query) (st : (List (Query × Digest) × Log) × Bool)
    (x : ((Reply ⊕ₒ fun _ : Query => Digest) q) × ((List (Query × Digest) × Log) × Bool))
    (hx : x ∈
      (flaggedLazyProgramHandler dist active inactive samplePre point finish q st).support) :
    x.2.1.1.length ≤ st.1.1.length + 1 := by
  obtain ⟨⟨cache, log⟩, b⟩ := st
  supp_cases hx [flaggedLazyProgramHandler, withBadFlag] with ⟨⟨ans, ⟨cache', log'⟩, b'⟩, hmem, rfl⟩
  dsimp only [Prod.map, id_eq]
  cases q with
  | inl req =>
    supp_cases hmem [lazyProgramStep] with
      ⟨_, ts, -, res, hm, -, ⟨rfl, -⟩, -⟩ | ⟨_, res, -, -, ⟨rfl, -⟩, -⟩
    · exact grow_length_memoize dist _ cache res hm
    · exact Nat.le_succ _
  | inr q =>
    supp_cases hmem [lazyProgramStep] with ⟨res, hm, -, ⟨rfl, -⟩, -⟩
    exact grow_length_memoize dist q cache res hm

/-- **Sharpened adaptive RO programming collision bound (`OracleComp`)**: for a program making at
most `q_S` `.inl` calls and `q_H` `.inr` random-oracle calls from `(cache, log)`, the probability
that an active `.inl` call hits an already-cached point is at most
`(q_S * cache.length + q_S * q_H + q_S.choose 2) * δ`. -/
theorem toOuterMeasure_bad_flaggedLazyProgramHandler_choose_two_le
    [BEq Query] [LawfulBEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log)
    {δ : ℝ≥0∞} (hminEnt : ∀ req, active req = true → ∀ q, ((samplePre req).map (point req)) q ≤ δ)
    {program : OracleComp (Reply ⊕ₒ fun _ : Query => Digest) α} {q_S q_H : ℕ}
    (hqS : IsCostBounded (Sum.elim (fun _ => 1) (fun _ => 0)) program q_S)
    (hqH : IsCostBounded (Sum.elim (fun _ => 0) (fun _ => 1)) program q_H)
    (cache : List (Query × Digest)) (log : Log) :
    ((interpret (flaggedLazyProgramHandler dist active inactive samplePre point finish)
      program).run ((cache, log), false)).toOuterMeasure {x | FlagBad x.2} ≤
      (q_S * cache.length + q_S * q_H + q_S.choose 2 : ℕ) * δ :=
  OracleComp.toOuterMeasure_bad_choose_two_cost_le
    (Sum.elim (fun _ => 1) (fun _ => 0)) (Sum.elim (fun _ => 0) (fun _ => 1))
    (fun st : (List (Query × Digest) × Log) × Bool => st.1.1.length) δ
    (fun q st hst => (step_bad_flaggedLazyProgramHandler_le dist active inactive samplePre point
      finish hminEnt q st hst).trans (by gcongr; exact Nat.le_add_right _ _))
    (fun q st _ x hx _ => by
      have hlen := length_cache_flaggedLazyProgramHandler_le dist active inactive samplePre point
        finish q st x hx
      cases q <;> simpa using hlen)
    hqS hqH Bool.false_ne_true

private theorem choose_two_bound_le_mul (q_S len q_H : ℕ) (δ : ℝ≥0∞) :
    ((q_S * len + q_S * q_H + q_S.choose 2 : ℕ) : ℝ≥0∞) * δ ≤
      (q_S * (len + q_S + q_H) : ℕ) * δ := by
  have hchoose : q_S.choose 2 ≤ q_S * q_S := by
    rw [Nat.choose_two_right]
    exact Nat.div_le_of_le_mul (by nlinarith [Nat.sub_le q_S 1])
  gcongr
  nlinarith

/-- **Rectangular adaptive RO programming collision bound (`OracleComp`)**: corollary of
`toOuterMeasure_bad_flaggedLazyProgramHandler_choose_two_le` bounding the collision probability from
`(cache, log)` by `(q_S * (cache.length + q_S + q_H)) * δ`. -/
theorem toOuterMeasure_bad_flaggedLazyProgramHandler_le
    [BEq Query] [LawfulBEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log)
    {δ : ℝ≥0∞} (hminEnt : ∀ req, active req = true → ∀ q, ((samplePre req).map (point req)) q ≤ δ)
    {program : OracleComp (Reply ⊕ₒ fun _ : Query => Digest) α} {q_S q_H : ℕ}
    (hqS : IsCostBounded (Sum.elim (fun _ => 1) (fun _ => 0)) program q_S)
    (hqH : IsCostBounded (Sum.elim (fun _ => 0) (fun _ => 1)) program q_H)
    (cache : List (Query × Digest)) (log : Log) :
    ((interpret (flaggedLazyProgramHandler dist active inactive samplePre point finish)
      program).run ((cache, log), false)).toOuterMeasure {x | FlagBad x.2} ≤
      (q_S * (cache.length + q_S + q_H) : ℕ) * δ :=
  (toOuterMeasure_bad_flaggedLazyProgramHandler_choose_two_le dist active inactive samplePre
    point finish hminEnt hqS hqH cache log).trans (choose_two_bound_le_mul q_S cache.length q_H δ)

private theorem closeTo_run_lazyProgramHandler_overwriteProgramHandler_raw
    [BEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log)
    (program : OracleComp (Reply ⊕ₒ fun _ : Query => Digest) α)
    (cache : List (Query × Digest)) (log : Log) :
    CloseTo
      ((interpret (lazyProgramHandler dist active inactive samplePre point finish)
        program).run (cache, log))
      ((interpret (overwriteProgramHandler dist active inactive samplePre point finish)
        program).run (cache, log))
      (((interpret (flaggedLazyProgramHandler dist active inactive samplePre point finish)
        program).run ((cache, log), false)).toOuterMeasure {x | FlagBad x.2}) := by
  rw [← run_flaggedLazyProgramHandler_map_fst (b := false),
    ← run_flaggedOverwriteProgramHandler_map_fst (b := false)]
  exact ((identicalUntilBad_flaggedProgramHandlers dist active inactive samplePre point
    finish).closeTo_run program ((cache, log), false)).map (Prod.map id Prod.fst)

/-- **Sharpened adaptive RO programming `CloseTo` hop (`OracleComp`)**: replacing lazy oracle reads
at `point req ts` with fresh overwrites changes the joint `(α × (List (Query × Digest) × Log))`
distribution by at most `(q_S * cache.length + q_S * q_H + q_S.choose 2) * δ`. -/
theorem closeTo_run_lazyProgramHandler_overwriteProgramHandler_choose_two
    [BEq Query] [LawfulBEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log)
    {δ : ℝ≥0∞} (hminEnt : ∀ req, active req = true → ∀ q, ((samplePre req).map (point req)) q ≤ δ)
    {program : OracleComp (Reply ⊕ₒ fun _ : Query => Digest) α} {q_S q_H : ℕ}
    (hqS : IsCostBounded (Sum.elim (fun _ => 1) (fun _ => 0)) program q_S)
    (hqH : IsCostBounded (Sum.elim (fun _ => 0) (fun _ => 1)) program q_H)
    (cache : List (Query × Digest)) (log : Log) :
    CloseTo
      ((interpret (lazyProgramHandler dist active inactive samplePre point finish)
        program).run (cache, log))
      ((interpret (overwriteProgramHandler dist active inactive samplePre point finish)
        program).run (cache, log))
      ((q_S * cache.length + q_S * q_H + q_S.choose 2 : ℕ) * δ) :=
  (closeTo_run_lazyProgramHandler_overwriteProgramHandler_raw dist active inactive samplePre point
    finish program cache log).mono
    (toOuterMeasure_bad_flaggedLazyProgramHandler_choose_two_le dist active inactive samplePre
      point finish hminEnt hqS hqH cache log)

/-- **Rectangular adaptive RO programming `CloseTo` hop (`OracleComp`)**: replacing lazy oracle
reads with fresh overwrites from `(cache, log)` changes the joint result-and-state distribution by
at most `(q_S * (cache.length + q_S + q_H)) * δ`. -/
theorem closeTo_run_lazyProgramHandler_overwriteProgramHandler
    [BEq Query] [LawfulBEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log)
    {δ : ℝ≥0∞} (hminEnt : ∀ req, active req = true → ∀ q, ((samplePre req).map (point req)) q ≤ δ)
    {program : OracleComp (Reply ⊕ₒ fun _ : Query => Digest) α} {q_S q_H : ℕ}
    (hqS : IsCostBounded (Sum.elim (fun _ => 1) (fun _ => 0)) program q_S)
    (hqH : IsCostBounded (Sum.elim (fun _ => 0) (fun _ => 1)) program q_H)
    (cache : List (Query × Digest)) (log : Log) :
    CloseTo
      ((interpret (lazyProgramHandler dist active inactive samplePre point finish)
        program).run (cache, log))
      ((interpret (overwriteProgramHandler dist active inactive samplePre point finish)
        program).run (cache, log))
      ((q_S * (cache.length + q_S + q_H) : ℕ) * δ) :=
  (closeTo_run_lazyProgramHandler_overwriteProgramHandler_raw dist active inactive samplePre point
    finish program cache log).mono
    (toOuterMeasure_bad_flaggedLazyProgramHandler_le dist active inactive samplePre point finish
      hminEnt hqS hqH cache log)

/-- **Total-query adaptive RO programming `CloseTo` hop (`OracleComp`)**: when a program makes at
most `q_S` `.inl` calls and `Q` calls in total (`IsQueryBounded program Q`), lazy and
fresh-overwrite executions from `(cache, log)` are within `(q_S * (cache.length + Q)) * δ`. -/
theorem closeTo_run_lazyProgramHandler_overwriteProgramHandler_of_isQueryBounded
    [BEq Query] [LawfulBEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log)
    {δ : ℝ≥0∞} (hminEnt : ∀ req, active req = true → ∀ q, ((samplePre req).map (point req)) q ≤ δ)
    {program : OracleComp (Reply ⊕ₒ fun _ : Query => Digest) α} {q_S Q : ℕ}
    (hqS : IsCostBounded (Sum.elim (fun _ => 1) (fun _ => 0)) program q_S)
    (hQ : IsQueryBounded program Q)
    (cache : List (Query × Digest)) (log : Log) :
    CloseTo
      ((interpret (lazyProgramHandler dist active inactive samplePre point finish)
        program).run (cache, log))
      ((interpret (overwriteProgramHandler dist active inactive samplePre point finish)
        program).run (cache, log))
      ((q_S * (cache.length + Q) : ℕ) * δ) := by
  refine (closeTo_run_lazyProgramHandler_overwriteProgramHandler_raw dist active inactive samplePre
    point finish program cache log).mono ?_
  have hbad := OracleComp.toOuterMeasure_bad_le
    (handler := flaggedLazyProgramHandler dist active inactive samplePre point finish)
    (bad := FlagBad) (Sum.elim (fun _ => 1) (fun _ => 0))
    (fun st : (List (Query × Digest) × Log) × Bool => (st.1.1.length : ℝ≥0∞) * δ) δ
    (fun q st hst => by
      have h := step_bad_flaggedLazyProgramHandler_le dist active inactive samplePre point finish
        hminEnt q st hst
      simpa only [Nat.cast_mul, mul_assoc] using h)
    (fun q st _ x hx _ => by
      have hlen := length_cache_flaggedLazyProgramHandler_le dist active inactive samplePre point
        finish q st x hx
      calc (x.2.1.1.length : ℝ≥0∞) * δ
          ≤ (st.1.1.length + 1 : ℕ) * δ := by gcongr
        _ = (st.1.1.length : ℝ≥0∞) * δ + δ := by
            rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul])
    hQ hqS (s := ((cache, log), false)) Bool.false_ne_true
  refine hbad.trans_eq ?_
  simp only [Nat.cast_mul, Nat.cast_add]
  ring

/-- **Sharpened adaptive RO programming `CloseTo` hop (`ProbOracleComp.runWith`)**: lifts
`closeTo_run_lazyProgramHandler_overwriteProgramHandler_choose_two` to adversaries with private
randomness. -/
theorem closeTo_runWith_lazyProgramHandler_overwriteProgramHandler_choose_two
    [BEq Query] [LawfulBEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log)
    {δ : ℝ≥0∞} (hminEnt : ∀ req, active req = true → ∀ q, ((samplePre req).map (point req)) q ≤ δ)
    {program : ProbOracleComp (Reply ⊕ₒ fun _ : Query => Digest) α} {q_S q_H : ℕ}
    (hqS : IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0))) program q_S)
    (hqH : IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun _ => 1))) program q_H)
    (cache : List (Query × Digest)) (log : Log) :
    CloseTo
      (ProbOracleComp.runWith
        (lazyProgramHandler dist active inactive samplePre point finish) program (cache, log))
      (ProbOracleComp.runWith
        (overwriteProgramHandler dist active inactive samplePre point finish) program (cache, log))
      ((q_S * cache.length + q_S * q_H + q_S.choose 2 : ℕ) * δ) := by
  have hiub := ProbOracleComp.identicalUntilBad_withBadFlag
    (lazyProgramStep dist active inactive samplePre point finish)
    (overwriteProgramStep dist active inactive samplePre point finish)
    (lazyProgramStep_agree_overwriteProgramStep dist active inactive samplePre point finish)
  have hl := ProbOracleComp.runWith_withBadFlag_map_fst
    (lazyProgramStep dist active inactive samplePre point finish)
    (lazyProgramHandler dist active inactive samplePre point finish)
    (lazyProgramStep_map_fst dist active inactive samplePre point finish)
    program (cache, log) false
  have hr := ProbOracleComp.runWith_withBadFlag_map_fst
    (overwriteProgramStep dist active inactive samplePre point finish)
    (overwriteProgramHandler dist active inactive samplePre point finish)
    (overwriteProgramStep_map_fst dist active inactive samplePre point finish)
    program (cache, log) false
  rw [← hl, ← hr]
  refine ((hiub.closeTo_run program ((cache, log), false)).map (Prod.map id Prod.fst)).mono ?_
  exact ProbOracleComp.toOuterMeasure_bad_choose_two_cost_le
    (Sum.elim (fun _ => 1) (fun _ => 0)) (Sum.elim (fun _ => 0) (fun _ => 1))
    (fun st : (List (Query × Digest) × Log) × Bool => st.1.1.length) δ
    (fun q st hst => (step_bad_flaggedLazyProgramHandler_le dist active inactive samplePre point
      finish hminEnt q st hst).trans (by gcongr; exact Nat.le_add_right _ _))
    (fun q st _ x hx _ => by
      have hlen := length_cache_flaggedLazyProgramHandler_le dist active inactive samplePre point
        finish q st x hx
      cases q <;> simpa using hlen)
    hqS hqH Bool.false_ne_true

/-- **Rectangular adaptive RO programming `CloseTo` hop (`ProbOracleComp.runWith`)**: corollary
giving the `(q_S * (cache.length + q_S + q_H)) * δ` bound. -/
theorem closeTo_runWith_lazyProgramHandler_overwriteProgramHandler
    [BEq Query] [LawfulBEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log)
    {δ : ℝ≥0∞} (hminEnt : ∀ req, active req = true → ∀ q, ((samplePre req).map (point req)) q ≤ δ)
    {program : ProbOracleComp (Reply ⊕ₒ fun _ : Query => Digest) α} {q_S q_H : ℕ}
    (hqS : IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0))) program q_S)
    (hqH : IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun _ => 1))) program q_H)
    (cache : List (Query × Digest)) (log : Log) :
    CloseTo
      (ProbOracleComp.runWith
        (lazyProgramHandler dist active inactive samplePre point finish) program (cache, log))
      (ProbOracleComp.runWith
        (overwriteProgramHandler dist active inactive samplePre point finish) program (cache, log))
      ((q_S * (cache.length + q_S + q_H) : ℕ) * δ) :=
  (closeTo_runWith_lazyProgramHandler_overwriteProgramHandler_choose_two dist active
    inactive samplePre point finish hminEnt hqS hqH cache log).mono
    (choose_two_bound_le_mul q_S cache.length q_H δ)

end Programming

/-! ### Random-function output-collision birthday bounds -/

section Birthday

/-- A random-oracle association-list cache contains an *output collision* when two entries with
distinct keys map to the same digest. -/
@[expose] def HasOutputCollision {Query Digest : Type*} (cache : List (Query × Digest)) : Prop :=
  ∃ e₁ ∈ cache, ∃ e₂ ∈ cache, e₁.1 ≠ e₂.1 ∧ e₁.2 = e₂.2

private theorem nodup_fst_step_memoize {Query Digest : Type} [BEq Query] [LawfulBEq Query]
    (distribution : Query → PMF Digest) (key : Query) (c : List (Query × Digest))
    (hc : (c.map Prod.fst).Nodup) (ans : Digest) (c' : List (Query × Digest))
    (hstep : (ans, c') ∈ (memoize distribution key c).support) :
    (c'.map Prod.fst).Nodup := by
  rcases (mem_support_memoize_iff _ _ _ (ans, c')).mp hstep with ⟨-, hnext⟩ | ⟨hlookup, -, hnext⟩
  · obtain rfl : c' = c := hnext
    exact hc
  · obtain rfl : c' = (key, ans) :: c := hnext
    refine List.nodup_cons.mpr ⟨fun hkey => ?_, hc⟩
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hkey
    exact absurd (List.lookup_isSome_iff.mpr ⟨e, he, beq_iff_eq.mpr heq.symm⟩) (by simp [hlookup])

/-- `memoize` preserves key distinctness `(cache.map Prod.fst).Nodup` across every adaptive
execution, because cache hits reuse existing entries without prepending a duplicate key. -/
theorem nodup_fst_of_mem_support_run_memoize {Query Digest α : Type}
    [BEq Query] [LawfulBEq Query] (distribution : Query → PMF Digest)
    (program : OracleComp (fun _ : Query => Digest) α)
    {cache cache' : List (Query × Digest)} (hcache : (cache.map Prod.fst).Nodup)
    {result : α}
    (hmem : (result, cache') ∈ ((interpret (memoize distribution) program).run cache).support) :
    (cache'.map Prod.fst).Nodup :=
  run_interpret_invariant (memoize distribution) (fun c => (c.map Prod.fst).Nodup)
    (nodup_fst_step_memoize distribution) program cache hcache result cache' hmem

/-- On any cache with distinct keys (`(cache.map Prod.fst).Nodup`), `HasOutputCollision cache` is
equivalent to `¬(cache.map Prod.snd).Nodup`. -/
theorem hasOutputCollision_iff_not_nodup_snd {Query Digest : Type*}
    {cache : List (Query × Digest)} (hfst : (cache.map Prod.fst).Nodup) :
    HasOutputCollision cache ↔ ¬(cache.map Prod.snd).Nodup := by
  rw [List.nodup_map_iff_inj_on (hfst.of_map Prod.fst)]
  have hinj := (List.nodup_map_iff_inj_on (hfst.of_map Prod.fst)).mp hfst
  refine ⟨fun ⟨e₁, he₁, e₂, he₂, hne, heq⟩ h => hne (congrArg Prod.fst (h e₁ he₁ e₂ he₂ heq)),
    fun h => ?_⟩
  push Not at h
  obtain ⟨e₁, he₁, e₂, he₂, heq, hne⟩ := h
  exact ⟨e₁, he₁, e₂, he₂, fun hk => hne (hinj e₁ he₁ e₂ he₂ hk), heq⟩

private theorem step_not_nodup_snd_memoize_le {Query Digest : Type} [BEq Query]
    (dist : PMF Digest) {δ : ℝ≥0∞} (hdist : ∀ y, dist y ≤ δ)
    (key : Query) (cache : List (Query × Digest)) (hgood : ¬¬(cache.map Prod.snd).Nodup) :
    (memoize (fun _ => dist) key cache).toOuterMeasure
      {x | ¬(x.2.map Prod.snd).Nodup} ≤ cache.length * δ := by
  have hnodup := not_not.mp hgood
  cases hlookup : cache.lookup key with
  | some v =>
    rw [memoize_of_some _ _ _ _ hlookup]
    simp [PMF.monad_pure_eq_pure, PMF.toOuterMeasure_pure_apply, hnodup]
  | none =>
    rw [memoize_of_none _ _ _ hlookup, show dist >>= (fun y => pure (y, (key, y) :: cache)) =
        dist.map (fun y => (y, (key, y) :: cache)) from PMF.bind_pure_comp _ dist,
      PMF.toOuterMeasure_map_apply]
    have hsub : (fun y => (y, (key, y) :: cache)) ⁻¹' {x | ¬(x.2.map Prod.snd).Nodup} ⊆
        {y | ∃ e' ∈ cache.map Prod.swap, e'.1 = id y} := fun y hy => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp
        (Classical.not_not.mp fun hnot => hy (List.nodup_cons.mpr ⟨hnot, hnodup⟩))
      exact ⟨e.swap, List.mem_map_of_mem he, rfl⟩
    refine (MeasureTheory.measure_mono hsub).trans ?_
    simpa only [List.length_map] using toOuterMeasure_exists_mem_fst_eq_le (f := id)
      (by simpa only [PMF.map_id] using hdist) (cache.map Prod.swap)

/-- **Min-entropy random-oracle output-collision bound (`OracleComp`)**: if `∀ y, dist y ≤ δ` and
`program` makes at most `q` queries starting from `cache` with `(cache.map Prod.snd).Nodup`, then
`¬(cache'.map Prod.snd).Nodup` occurs with probability at most
`(q * cache.length + q.choose 2) * δ`. -/
theorem toOuterMeasure_not_nodup_snd_memoize_le {Query Digest α : Type} [BEq Query]
    (dist : PMF Digest) {δ : ℝ≥0∞} (hdist : ∀ y, dist y ≤ δ)
    {program : OracleComp (fun _ : Query => Digest) α} {q : ℕ} (hq : IsQueryBounded program q)
    {cache : List (Query × Digest)} (hcache : (cache.map Prod.snd).Nodup) :
    ((interpret (memoize (fun _ => dist)) program).run cache).toOuterMeasure
      {x | ¬(x.2.map Prod.snd).Nodup} ≤ (q * cache.length + q.choose 2 : ℕ) * δ :=
  OracleComp.toOuterMeasure_bad_choose_two_le
    (bad := fun c : List (Query × Digest) => ¬(c.map Prod.snd).Nodup) List.length δ
    (step_not_nodup_snd_memoize_le dist hdist)
    (fun key c _ x hx _ => grow_length_memoize dist key c x hx)
    hq (not_not.mpr hcache)

/-- **Min-entropy random-oracle output-collision bound (`ProbOracleComp.runWith`)**: lifts
`toOuterMeasure_not_nodup_snd_memoize_le` to adversaries with private randomness. -/
theorem toOuterMeasure_not_nodup_snd_runWith_memoize_le {Query Digest α : Type} [BEq Query]
    (dist : PMF Digest) {δ : ℝ≥0∞} (hdist : ∀ y, dist y ≤ δ)
    {program : ProbOracleComp (fun _ : Query => Digest) α} {q : ℕ}
    (hq : program.IsQueryBounded q)
    {cache : List (Query × Digest)} (hcache : (cache.map Prod.snd).Nodup) :
    (ProbOracleComp.runWith (memoize (fun _ => dist)) program cache).toOuterMeasure
      {x | ¬(x.2.map Prod.snd).Nodup} ≤ (q * cache.length + q.choose 2 : ℕ) * δ :=
  ProbOracleComp.toOuterMeasure_bad_choose_two_le
    (bad := fun c : List (Query × Digest) => ¬(c.map Prod.snd).Nodup) List.length δ
    (step_not_nodup_snd_memoize_le dist hdist)
    (fun key c _ x hx _ => grow_length_memoize dist key c x hx)
    hq (not_not.mpr hcache)

/-- **Random-oracle birthday bound (`OracleComp`, `Nodup` form)**: a `q`-query adaptive program
against `memoize (fun _ => PMF.uniformOfFintype Digest)` starting from `[]` produces duplicate
stored digests with probability at most `q.choose 2 / Fintype.card Digest`. -/
theorem toOuterMeasure_collision_memoize_uniform_le {Query Digest α : Type} [BEq Query]
    [Fintype Digest] [Nonempty Digest]
    {program : OracleComp (fun _ : Query => Digest) α} {q : ℕ} (hq : IsQueryBounded program q) :
    ((interpret (memoize (fun _ : Query => PMF.uniformOfFintype Digest)) program).run
      []).toOuterMeasure {x | ¬(x.2.map Prod.snd).Nodup} ≤
      (q.choose 2 : ℝ≥0∞) / Fintype.card Digest := by
  have h := toOuterMeasure_not_nodup_snd_memoize_le (PMF.uniformOfFintype Digest)
    (fun y => le_of_eq (PMF.uniformOfFintype_apply y)) hq (cache := []) List.nodup_nil
  simpa only [List.length_nil, mul_zero, zero_add, div_eq_mul_inv] using h

/-- **Random-oracle birthday bound (`ProbOracleComp.runWith`, `Nodup` form)**: a `q`-query adaptive
randomized program against `memoize (fun _ => PMF.uniformOfFintype Digest)` starting from `[]`
produces duplicate stored digests with probability at most `q.choose 2 / Fintype.card Digest`. -/
theorem toOuterMeasure_collision_runWith_memoize_uniform_le {Query Digest α : Type} [BEq Query]
    [Fintype Digest] [Nonempty Digest]
    {program : ProbOracleComp (fun _ : Query => Digest) α} {q : ℕ}
    (hq : program.IsQueryBounded q) :
    (ProbOracleComp.runWith (memoize (fun _ : Query => PMF.uniformOfFintype Digest)) program
      []).toOuterMeasure {x | ¬(x.2.map Prod.snd).Nodup} ≤
      (q.choose 2 : ℝ≥0∞) / Fintype.card Digest := by
  have h := toOuterMeasure_not_nodup_snd_runWith_memoize_le (PMF.uniformOfFintype Digest)
    (fun y => le_of_eq (PMF.uniformOfFintype_apply y)) hq (cache := []) List.nodup_nil
  simpa only [List.length_nil, mul_zero, zero_add, div_eq_mul_inv] using h

private theorem toOuterMeasure_hasOutputCollision_eq_not_nodup_snd {Query Digest α : Type}
    (μ : PMF (α × List (Query × Digest)))
    (hnodup : ∀ res cache', (res, cache') ∈ μ.support → (cache'.map Prod.fst).Nodup) :
    μ.toOuterMeasure {x | HasOutputCollision x.2} =
      μ.toOuterMeasure {x | ¬(x.2.map Prod.snd).Nodup} := by
  classical
  simp only [PMF.toOuterMeasure_apply]
  refine tsum_congr fun ⟨res, cache'⟩ => ?_
  by_cases hmem : (res, cache') ∈ μ.support
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq,
      hasOutputCollision_iff_not_nodup_snd (hnodup res cache' hmem)]
  · simp only [Set.indicator_apply, (PMF.apply_eq_zero_iff _ _).mpr hmem, ite_self]

/-- **Random-oracle birthday bound (`OracleComp`, distinct-key `HasOutputCollision` form)**: a
`q`-query adaptive program against `memoize (fun _ => PMF.uniformOfFintype Digest)` from `[]`
observes two distinct queried keys with the same digest with probability at most
`q.choose 2 / Fintype.card Digest`. -/
theorem toOuterMeasure_hasOutputCollision_memoize_uniform_le {Query Digest α : Type}
    [BEq Query] [LawfulBEq Query] [Fintype Digest] [Nonempty Digest]
    {program : OracleComp (fun _ : Query => Digest) α} {q : ℕ} (hq : IsQueryBounded program q) :
    ((interpret (memoize (fun _ : Query => PMF.uniformOfFintype Digest)) program).run
      []).toOuterMeasure {x | HasOutputCollision x.2} ≤
      (q.choose 2 : ℝ≥0∞) / Fintype.card Digest := by
  rw [toOuterMeasure_hasOutputCollision_eq_not_nodup_snd _ fun _ _ hmem =>
    nodup_fst_of_mem_support_run_memoize _ program (cache := []) List.nodup_nil hmem]
  exact toOuterMeasure_collision_memoize_uniform_le hq

/-- **Random-oracle birthday bound (`ProbOracleComp.runWith`, distinct-key `HasOutputCollision`
form)**: a `q`-query adaptive randomized program against
`memoize (fun _ => PMF.uniformOfFintype Digest)` from `[]` observes two distinct queried keys with
the same digest with probability at most `q.choose 2 / Fintype.card Digest`. -/
theorem toOuterMeasure_hasOutputCollision_runWith_memoize_uniform_le {Query Digest α : Type}
    [BEq Query] [LawfulBEq Query] [Fintype Digest] [Nonempty Digest]
    {program : ProbOracleComp (fun _ : Query => Digest) α} {q : ℕ}
    (hq : program.IsQueryBounded q) :
    (ProbOracleComp.runWith (memoize (fun _ : Query => PMF.uniformOfFintype Digest)) program
      []).toOuterMeasure {x | HasOutputCollision x.2} ≤
      (q.choose 2 : ℝ≥0∞) / Fintype.card Digest := by
  rw [toOuterMeasure_hasOutputCollision_eq_not_nodup_snd _ fun res cache' hmem =>
    ProbOracleComp.runWith_invariant (memoize (fun _ => PMF.uniformOfFintype Digest))
      (fun c => (c.map Prod.fst).Nodup) (nodup_fst_step_memoize _) program [] List.nodup_nil res
      cache' hmem]
  exact toOuterMeasure_collision_runWith_memoize_uniform_le hq

end Birthday

end Cslib.RandomOracle
