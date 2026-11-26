/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.Forgery
public import CslibFrontier.Crypto.Primitives.PRF.Finite
public import CslibFrontier.Languages.Probabilistic.UniformNat.ModIndex
public import CslibFrontier.Languages.Probabilistic.UntilBad.PlantedQuery
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Lens
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.UniformNat.LowerBound
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.DensityBounds
import CslibFrontier.Probability.PMF.Event
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Forgery experiments with verification queries

In [BonehShoup2023], Section 6.2 (Attack Game 6.2, p. 221), an adversary against a message
authentication code interleaves signing queries `m` with verification queries `(m̂, t̂)` and wins as
soon as the challenger accepts a verification query not among the previously answered `(m_i, t_i)`
pairs. Unlike Attack Game 6.1 (`forgeExperiment`), the adversary produces no final candidate; a
traditional Attack Game 6.1 forger is the special case making one verification query at the end
(`forgerToVq`).

This module develops the finite query-bounded steps of Theorem 6.1 ([BonehShoup2023], pp. 221–223)
and Exercise 6.2 ([BonehShoup2023], p. 246), where adversaries carry structural query budgets
(`IsSigningQueryBounded`, `IsVerificationQueryBounded`) without machine running-time certificates.
The full computational theorems with `IsOraclePPT` reduction certificates on `MACScheme` live in
`CslibFrontier.Crypto.Computational.MAC.VerificationQueries`.

## Design notes

* **Total verification oracle on repeated pairs.** Attack Game 6.2 syntactically forbids submitting
  a previously signed pair `(m, σ) ∈ log` to the verification oracle. Here `vqOracle` is total on
  `M × Sig`: it answers every verification query `(m, σ)` with `verify pk sk m σ` and latches `won`
  only when `verify pk sk m σ && freshPair m σ log` holds. An adversary that never submits a pair
  from `log` sees the exact Attack Game 6.2 oracle, while an adversary that replays `(m, σ) ∈ log`
  receives `true` (when honest signatures verify) without winning.
* **Why `freshPair` works for randomized MACs without `sk`.** Suppose every signature produced by
  `signer` verifies (`hsign`). Before the first winning fresh verification query occurs, any
  verification query `(m, σ)` satisfies `(verify pk sk m σ && freshPair m σ log) = false`: if
  `(m, σ) ∈ log` then `verify pk sk m σ = true`, and if `(m, σ) ∉ log` then
  `verify pk sk m σ = false`. In both cases the challenger's answer equals `decide ((m, σ) ∈ log)`,
  which the reduction `vqToForgerOn` computes from its local signing log without knowing `sk`, even
  when `signer` is randomized and messages have multiple valid tags. (Under existential freshness
  `freshMessage`, a second valid tag `(m, σ')` on a previously signed `m` would not win yet would
  require answering `true`, which cannot be simulated without `sk`.)
* **Policy admissibility.** Under `ProbOracleComp.runLogWith`, a refused signing query
  (`signer sk log m = none`, as in `Signer.restrict` or `Signer.oneTime`) returns `default` without
  appending to `log`. `vqToForgerOn` takes a public predicate `admit : List (M × Sig) → M → Bool`
  characterizing `(signer sk log m).isSome` so its local log matches the challenger's log; for an
  unrestricted signer (`Signer.ofSign`), `vqToForger` fixes `admit := fun _ _ => true`.
* **PRF MAC without the `Q_v` factor on PRF advantage (Exercise 6.2).** For a deterministic keyed
  function `F : Key → D → R`, `vqMacToPrfAdversary` forwards signing queries and fresh verification
  queries directly to the function oracle (`≤ Q_s + Q_v` calls in total) without guessing an index.
  In the ideal random-function world, the finite Theorem 6.1 step bounds the `Q_v`-verification
  success probability by `Q_v` times the Attack Game 6.1 random-function forgery probability
  (`≤ 1 / |R|`), yielding `PRF.advantage F (vqMacToPrfAdversary A) + Q_v / |R|`.

## Main definitions

* `Cslib.Crypto.forgeVqSpec`: disjoint sum `(fun _ : M => Sig) ⊕ₒ (fun _ : M × Sig => Bool)` of the
  signing and verification oracle interfaces.
* `Cslib.Crypto.IsSigningQueryBounded`, `Cslib.Crypto.IsVerificationQueryBounded`: separate pathwise
  signing and verification query budgets.
* `Cslib.Crypto.vqOracle`, `Cslib.Crypto.vqForgeExperiment`: stateful challenger and experiment of
  Attack Game 6.2.
* `Cslib.Crypto.forgerToVq`: embeds an Attack Game 6.1 forger as a 1-verification-query adversary.
* `Cslib.Crypto.vqToForgerOn`, `Cslib.Crypto.vqToForger`: planted-query guessing reduction from
  `vqForgeExperiment` to `forgeExperiment` with `freshPair`.
* `Cslib.Crypto.vqMacToPrfAdversary`: direct reduction from `vqForgeExperiment` on a deterministic
  keyed function `F` to `PRF.Adversary`.

## Main results

* `Cslib.Crypto.eval_vqForgeExperiment_forgerToVq`: `forgerToVq A` has the exact law of
  `forgeExperiment ... freshPair A`.
* `Cslib.Crypto.succProbability_vqForgeExperiment_zero`: `0` verification queries give `0` winning
  probability.
* `Cslib.Crypto.eval_vqForgeExperiment_le_mul_add_of_index`: general index-sampler guessing step.
* `Cslib.Crypto.succProbability_vqForgeExperiment_le_mul`,
  `Cslib.Crypto.succProbability_vqForgeExperiment_ofSign_le_mul`: finite query-bounded step of
  Theorem 6.1 (`≤ Q_v * succProbability (forgeExperiment ...)`).
* `Cslib.Crypto.eval_vqForgeExperiment_le_mul_sampleModIndex_add`,
  `Cslib.Crypto.eval_vqForgeExperiment_le_mul_sampleModIndex_of_dvd`: fair-coin `sampleModIndex`
  forms of the finite Theorem 6.1 step (with `+ Q_v / 2 ^ width`, and exact when
  `Q_v = 0 ∨ Q_v ∣ 2 ^ width`).
* `Cslib.Crypto.succProbability_vqForgeExperiment_prf_le`: finite query-bounded step of Exercise 6.2
  (`≤ PRF.advantage F (vqMacToPrfAdversary A) + Q_v / Fintype.card R`).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 6.2 (Attack Game 6.2 and Theorem 6.1, pp. 220–223) and Section 6.14 (Exercise 6.2,
  p. 246).
-/

public section

namespace Cslib.Crypto

open Probability
open scoped ENNReal NNReal

/-! ### Oracle interface, budgets, and Attack Game 6.2 -/

/-- Combined signing and verification oracle interface for Attack Game 6.2: left queries `.inl m`
request a signature in `Sig`, and right queries `.inr (m, σ)` request a Boolean verification
verdict. -/
abbrev forgeVqSpec (M Sig : Type) : OracleSpec (M ⊕ (M × Sig)) :=
  (fun _ : M => Sig) ⊕ₒ (fun _ : M × Sig => Bool)

/-- Pathwise budget of at most `Q_s` signing queries (`.inl m`), leaving private coin flips and
verification queries unconstrained. -/
abbrev IsSigningQueryBounded {M Sig α : Type}
    (program : ProbOracleComp (forgeVqSpec M Sig) α) (Q_s : ℕ) : Prop :=
  OracleComp.IsCostBounded
    (Sum.elim (fun _ => 0) (fun q => if q.isLeft then 1 else 0)) program Q_s

/-- Pathwise budget of at most `Q_v` verification queries (`.inr (m, σ)`), leaving private coin
flips and signing queries unconstrained. -/
abbrev IsVerificationQueryBounded {M Sig α : Type}
    (program : ProbOracleComp (forgeVqSpec M Sig) α) (Q_v : ℕ) : Prop :=
  OracleComp.IsCostBounded
    (Sum.elim (fun _ => 0) (fun q => if q.isRight then 1 else 0)) program Q_v

/-- One signing query costs `1` signing query. -/
theorem IsSigningQueryBounded.query_sign {M Sig : Type} (m : M) :
    IsSigningQueryBounded (ProbOracleComp.query (spec := forgeVqSpec M Sig) (Sum.inl m)) 1 :=
  ProbOracleComp.isCostBounded_query _ (Sum.inl m)

/-- One verification query costs `0` signing queries. -/
theorem IsSigningQueryBounded.query_verify {M Sig : Type} (p : M × Sig) :
    IsSigningQueryBounded (ProbOracleComp.query (spec := forgeVqSpec M Sig) (Sum.inr p)) 0 :=
  ProbOracleComp.isCostBounded_query _ (Sum.inr p)

/-- One signing query costs `0` verification queries. -/
theorem IsVerificationQueryBounded.query_sign {M Sig : Type} (m : M) :
    IsVerificationQueryBounded (ProbOracleComp.query (spec := forgeVqSpec M Sig) (Sum.inl m)) 0 :=
  ProbOracleComp.isCostBounded_query _ (Sum.inl m)

/-- One verification query costs `1` verification query. -/
theorem IsVerificationQueryBounded.query_verify {M Sig : Type} (p : M × Sig) :
    IsVerificationQueryBounded (ProbOracleComp.query (spec := forgeVqSpec M Sig) (Sum.inr p)) 1 :=
  ProbOracleComp.isCostBounded_query _ (Sum.inr p)

/-- A total external query budget bounds the number of signing queries. -/
theorem IsSigningQueryBounded.of_isQueryBounded {M Sig α : Type}
    {program : ProbOracleComp (forgeVqSpec M Sig) α} {Q : ℕ}
    (h : program.IsQueryBounded Q) : IsSigningQueryBounded program Q :=
  h.of_le fun q => by cases q with
    | inl _ => simp
    | inr q => cases q <;> simp

/-- A total external query budget bounds the number of verification queries. -/
theorem IsVerificationQueryBounded.of_isQueryBounded {M Sig α : Type}
    {program : ProbOracleComp (forgeVqSpec M Sig) α} {Q : ℕ}
    (h : program.IsQueryBounded Q) : IsVerificationQueryBounded program Q :=
  h.of_le fun q => by cases q with
    | inl _ => simp
    | inr q => cases q <;> simp

/-- Separate signing and verification query budgets yield a total external query budget of
`Q_s + Q_v`. -/
theorem IsQueryBounded.of_signing_and_verification {M Sig α : Type}
    {program : ProbOracleComp (forgeVqSpec M Sig) α} {Q_s Q_v : ℕ}
    (hs : IsSigningQueryBounded program Q_s) (hv : IsVerificationQueryBounded program Q_v) :
    program.IsQueryBounded (Q_s + Q_v) :=
  (hs.add hv).of_le fun q => by cases q with
    | inl _ => simp
    | inr q => cases q <;> simp

/-- Challenger state for Attack Game 6.2: the chronological `log` of answered signing pairs and
whether some fresh verification query has already verified (`won`). -/
structure VqOracleState (M Sig : Type) where
  /-- Answered `(message, signature)` pairs in the order answered by `signer`. -/
  log : List (M × Sig)
  /-- Latches `true` as soon as a verification query `(m, σ)` verifies and satisfies `freshPair`. -/
  won : Bool
  deriving DecidableEq, Repr

/-- Stateful challenger oracle for Attack Game 6.2 ([BonehShoup2023], p. 221):
* `.inl m` runs `signer sk st.log m`; if accepted (`some reply`), appends `(m, σ)` to `st.log` and
  returns `σ`; if refused (`none`), returns `default` without modifying `st`.
* `.inr (m, σ)` evaluates `ok := verify pk sk m σ`, latches `st.won` when `ok && freshPair m σ
  st.log` holds, and returns `ok`. -/
@[expose] def vqOracle {PK SK M Sig : Type} [Inhabited Sig] [DecidableEq M] [DecidableEq Sig]
    (signer : Signer SK M Sig) (verify : PK → SK → M → Sig → Bool)
    (pk : PK) (sk : SK) (q : M ⊕ (M × Sig)) :
    StateT (VqOracleState M Sig) ProbComp (forgeVqSpec M Sig q) :=
  match q with
  | .inl m => fun st =>
    match signer sk st.log m with
    | some reply => (fun σ => (σ, ⟨st.log ++ [(m, σ)], st.won⟩)) <$> reply
    | none => pure (default, st)
  | .inr (m, σ) => fun st =>
    let ok := verify pk sk m σ
    pure (ok, ⟨st.log, st.won || (ok && freshPair m σ st.log)⟩)

/-- Forgery experiment with verification queries ([BonehShoup2023], Section 6.2, Attack Game 6.2,
p. 221): draw `(pk, sk)` from `keyGen`, run `A pk` against `vqOracle signer verify pk sk` from the
empty log with `won = false`, and accept iff `won` latched `true` on some fresh valid verification
query. -/
@[expose] def vqForgeExperiment {PK SK M Sig : Type} [Inhabited Sig] [DecidableEq M]
    [DecidableEq Sig] (keyGen : ProbComp (PK × SK)) (signer : Signer SK M Sig)
    (verify : PK → SK → M → Sig → Bool)
    (A : PK → ProbOracleComp (forgeVqSpec M Sig) Unit) : Experiment := do
  let (pk, sk) ← keyGen
  let (_, st) ← ((A pk).runState (vqOracle signer verify pk sk)).run ⟨[], false⟩
  return st.won

/-! ### Embedding Attack Game 6.1 into Attack Game 6.2 -/

/-- Embed a standard Attack Game 6.1 forger `A` into Attack Game 6.2 by forwarding all signing
queries to `.inl` and submitting `A`'s final output `(m, σ)` as a single `.inr (m, σ)` verification
query. -/
@[expose] def forgerToVq {PK M Sig : Type}
    (A : PK → ProbOracleComp (fun _ : M => Sig) (M × Sig)) (pk : PK) :
    ProbOracleComp (forgeVqSpec M Sig) Unit := do
  let cand ← OracleComp.interpret
    (OracleComp.sumHandler (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
      fun m => ProbOracleComp.query (spec := forgeVqSpec M Sig) (Sum.inl m))
    (A pk)
  let _ ← ProbOracleComp.query (spec := forgeVqSpec M Sig) (Sum.inr cand)
  return ()

private theorem runWith_vqOracle_liftSigning {PK SK M Sig α : Type} [Inhabited Sig]
    [DecidableEq M] [DecidableEq Sig]
    (signer : Signer SK M Sig) (verify : PK → SK → M → Sig → Bool) (pk : PK) (sk : SK)
    (prog : ProbOracleComp (fun _ : M => Sig) α) (log : List (M × Sig)) :
    ProbOracleComp.runWith (fun q st => ProbComp.eval (vqOracle signer verify pk sk q st))
      (OracleComp.interpret
        (OracleComp.sumHandler (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
          fun m => ProbOracleComp.query (spec := forgeVqSpec M Sig) (Sum.inl m))
        prog)
      ⟨log, false⟩ =
    (ProbOracleComp.runWith (fun m l => ProbComp.eval (ProbOracleComp.logOracle (signer sk) m l))
      prog log).map (fun x => (x.1, ⟨x.2, false⟩)) := by
  rw [ProbOracleComp.runWith_interpret_sumHandler]
  exact (ProbOracleComp.runWith_map_state
    (oracle := fun m l => ProbComp.eval (ProbOracleComp.logOracle (signer sk) m l))
    (oracle' := fun q st =>
      ProbOracleComp.runWith (fun q' st' => ProbComp.eval (vqOracle signer verify pk sk q' st'))
        (ProbOracleComp.query (spec := forgeVqSpec M Sig) (Sum.inl q)) st)
    (represent := fun l => (⟨l, false⟩ : VqOracleState M Sig))
    (step := fun m l => by
      rw [ProbOracleComp.runWith_query]
      dsimp only [vqOracle, ProbOracleComp.logOracle, StateT.run]
      cases signer sk l m <;> simp [ProbComp.eval_map, PMF.map_comp, Function.comp_def])
    prog log).symm

/-- `forgerToVq A` in `vqForgeExperiment` has the exact Boolean law of `A` in `forgeExperiment` with
strong freshness (`freshPair`). -/
theorem eval_vqForgeExperiment_forgerToVq {PK SK M Sig : Type} [Inhabited Sig] [DecidableEq M]
    [DecidableEq Sig] (keyGen : ProbComp (PK × SK)) (signer : Signer SK M Sig)
    (verify : PK → SK → M → Sig → Bool)
    (A : PK → ProbOracleComp (fun _ : M => Sig) (M × Sig)) :
    ProbComp.eval (vqForgeExperiment keyGen signer verify (forgerToVq A)) =
      ProbComp.eval (forgeExperiment keyGen signer verify freshPair A) := by
  simp only [vqForgeExperiment, forgeExperiment, ProbOracleComp.runLogWith,
    ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨pk, sk⟩ _ => ?_
  rw [ProbOracleComp.eval_runState, ProbOracleComp.eval_runState]
  dsimp only [forgerToVq]
  rw [ProbOracleComp.runWith_bind, runWith_vqOracle_liftSigning, PMF.bind_map, PMF.bind_bind]
  refine PMF.bind_congr_on_support _ _ _ fun x _ => ?_
  rcases x with ⟨⟨m, σ⟩, log⟩
  simp [ProbOracleComp.runWith_query, vqOracle]

/-- `forgerToVq A` preserves the signing query bound of `A`. -/
theorem isSigningQueryBounded_forgerToVq {PK M Sig : Type}
    {A : PK → ProbOracleComp (fun _ : M => Sig) (M × Sig)} {pk : PK} {Q_s : ℕ}
    (h : (A pk).IsQueryBounded Q_s) :
    IsSigningQueryBounded (forgerToVq A pk) Q_s := by
  unfold forgerToVq
  refine ((h.interpret ?_).bind fun cand =>
    (IsSigningQueryBounded.query_verify cand).bind fun _ => .pure () 0).mono (by simp)
  rintro (k | m)
  · exact ProbOracleComp.isCostBounded_sample _ (ProbComp.unifFin k)
  · exact IsSigningQueryBounded.query_sign m

/-- `forgerToVq A` makes at most `1` verification query. -/
theorem isVerificationQueryBounded_forgerToVq {PK M Sig : Type}
    (A : PK → ProbOracleComp (fun _ : M => Sig) (M × Sig)) (pk : PK) :
    IsVerificationQueryBounded (forgerToVq A pk) 1 := by
  unfold forgerToVq
  refine (((OracleComp.IsCostBounded.of_forall_cost_eq_zero (fun _ => rfl) (A pk)).interpret
    ?_).bind fun cand =>
    (IsVerificationQueryBounded.query_verify cand).bind fun _ => .pure () 0).mono (by simp)
  rintro (k | m)
  · exact ProbOracleComp.isCostBounded_sample _ (ProbComp.unifFin k)
  · exact IsVerificationQueryBounded.query_sign m

/-! ### Finite Theorem 6.1: planted-query guessing reduction to Attack Game 6.1 -/

private theorem eval_vqForgeExperiment_zero {PK SK M Sig : Type} [Inhabited Sig] [DecidableEq M]
    [DecidableEq Sig] (keyGen : ProbComp (PK × SK)) (signer : Signer SK M Sig)
    (verify : PK → SK → M → Sig → Bool)
    {A : PK → ProbOracleComp (forgeVqSpec M Sig) Unit}
    (hA : ∀ pk, IsVerificationQueryBounded (A pk) 0) :
    ProbComp.eval (vqForgeExperiment keyGen signer verify A) true = 0 := by
  simp only [vqForgeExperiment, ProbComp.eval_bind, ProbComp.eval_pure]
  refine nonpos_iff_eq_zero.mp (PMF.bind_apply_le_on_support _ fun ⟨pk, sk⟩ _ => ?_)
  refine PMF.bind_apply_le_on_support _ fun ⟨⟨⟩, st⟩ hmem => ?_
  have hle := ProbOracleComp.measure_runState_le (hA pk) (vqOracle signer verify pk sk)
    (fun s => if s.won then 1 else 0)
    (fun q s z hz => by
      cases q with
      | inl m =>
        dsimp only [vqOracle, StateT.run] at hz
        cases hsig : signer sk s.log m with
        | none => simp_all [ProbComp.eval_pure]
        | some reply =>
          rw [hsig, ProbComp.eval_map, PMF.mem_support_map_iff] at hz
          obtain ⟨_, -, rfl⟩ := hz
          simp
      | inr p =>
        cases z.2.won <;> simp)
    ⟨[], false⟩ ((), st) hmem
  cases hwon : st.won <;> simp_all

/-- An adversary with verification-query budget `0` has `succProbability = 0` in
`vqForgeExperiment`. -/
theorem succProbability_vqForgeExperiment_zero {PK SK M Sig : Type} [Inhabited Sig] [DecidableEq M]
    [DecidableEq Sig] (keyGen : ProbComp (PK × SK)) (signer : Signer SK M Sig)
    (verify : PK → SK → M → Sig → Bool)
    {A : PK → ProbOracleComp (forgeVqSpec M Sig) Unit}
    (hA : ∀ pk, IsVerificationQueryBounded (A pk) 0) :
    Experiment.succProbability (vqForgeExperiment keyGen signer verify A) = 0 := by
  simp [Experiment.succProbability, Game.succProbability,
    eval_vqForgeExperiment_zero keyGen signer verify hA]

/-- Stateful handler of the planted-query guessing reduction ([BonehShoup2023], Theorem 6.1,
pp. 221–223):
* once `st.planted.hasCaptured = true`, returns `(default, st)` on `.inl` and `(false, st)` on
  `.inr` without querying the external signing oracle;
* while `st.planted.hasCaptured = false`:
  - on `.inl m`, if `admit st.oracleState m` holds, queries `m` on the external signing oracle and
    appends `(m, σ)` to `st.oracleState`, and otherwise returns `(default, st)` locally;
  - on `.inr p`, captures `p` with reply `false` when `st.planted.rem == 0`, and otherwise answers
    `decide (p ∈ st.oracleState)` while decrementing `st.planted.rem`. -/
@[expose] def vqToForgerHandler {M Sig : Type} [Inhabited M] [Inhabited Sig] [DecidableEq M]
    [DecidableEq Sig] (admit : List (M × Sig) → M → Bool) (q : M ⊕ (M × Sig)) :
    StateT (ProbOracleComp.PlantedOracleState (M × Sig) (List (M × Sig)))
      (ProbOracleComp (fun _ : M => Sig)) (forgeVqSpec M Sig q) :=
  fun st =>
    if st.planted.hasCaptured then
      match q with
      | .inl _ => pure (default, st)
      | .inr _ => pure (false, st)
    else
      match q with
      | .inl m =>
        if admit st.oracleState m then
          (fun σ => (σ, ⟨st.planted, st.oracleState ++ [(m, σ)]⟩)) <$> ProbOracleComp.query m
        else
          pure (default, st)
      | .inr p =>
        if st.planted.rem == 0 then
          pure (false, ⟨⟨0, true, p⟩, st.oracleState⟩)
        else
          pure (decide (p ∈ st.oracleState),
            ⟨⟨st.planted.rem - 1, false, default⟩, st.oracleState⟩)

/-- Policy-aware planted-query reduction ([BonehShoup2023], Theorem 6.1, pp. 221–223): draw a
target verification-query index `j` from `index`, simulate `A pk` through `vqToForgerHandler admit`
starting at `PlantedOracleState.init j default []`, and output the captured candidate pair
`st.planted.candidate`. -/
@[expose] def vqToForgerOn {PK M Sig : Type} [Inhabited M] [Inhabited Sig] [DecidableEq M]
    [DecidableEq Sig] (admit : List (M × Sig) → M → Bool) (index : ProbComp ℕ)
    (A : PK → ProbOracleComp (forgeVqSpec M Sig) Unit) (pk : PK) :
    ProbOracleComp (fun _ : M => Sig) (M × Sig) := do
  let j ← ProbOracleComp.sample index
  let (_, st) ← (OracleComp.interpret
    (OracleComp.sumHandler
      (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
      (vqToForgerHandler admit))
    (A pk)).run (ProbOracleComp.PlantedOracleState.init j default [])
  return st.planted.candidate

/-- Planted-query reduction for unrestricted signing policies (`admit := fun _ _ => true`), as in
`Signer.ofSign`. -/
abbrev vqToForger {PK M Sig : Type} [Inhabited M] [Inhabited Sig] [DecidableEq M]
    [DecidableEq Sig] (index : ProbComp ℕ)
    (A : PK → ProbOracleComp (forgeVqSpec M Sig) Unit) :
    PK → ProbOracleComp (fun _ : M => Sig) (M × Sig) :=
  vqToForgerOn (fun _ _ => true) index A

/-- `vqToForgerOn` makes at most `Q_s` signing queries whenever `A pk` makes at most `Q_s` signing
queries. -/
theorem isQueryBounded_vqToForgerOn {PK M Sig : Type} [Inhabited M] [Inhabited Sig] [DecidableEq M]
    [DecidableEq Sig] (admit : List (M × Sig) → M → Bool) (index : ProbComp ℕ)
    {A : PK → ProbOracleComp (forgeVqSpec M Sig) Unit} {pk : PK} {Q_s : ℕ}
    (h : IsSigningQueryBounded (A pk) Q_s) :
    (vqToForgerOn admit index A pk).IsQueryBounded Q_s := by
  unfold vqToForgerOn
  refine ((ProbOracleComp.IsQueryBounded.sample index).bind fun j =>
    ((OracleComp.IsCostBounded.run_interpret ?_ h _).bind fun _ => .pure _ 0)).mono (by omega)
  rintro (k | (m | p)) s
  · exact (ProbOracleComp.IsQueryBounded.sample (ProbComp.unifFin k)).bind fun a => .pure (a, s) 0
  · dsimp only [OracleComp.sumHandler, vqToForgerHandler, StateT.run]
    split_ifs
    · exact .pure _ 1
    · exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (ProbOracleComp.IsQueryBounded.query m)
    · exact .pure _ 1
  · dsimp only [OracleComp.sumHandler, vqToForgerHandler, StateT.run]
    split_ifs <;> exact .pure _ 0

private abbrev ValidVqLog {PK SK M Sig : Type} (verify : PK → SK → M → Sig → Bool)
    (pk : PK) (sk : SK) :=
  {log : List (M × Sig) // ∀ p ∈ log, verify pk sk p.1 p.2 = true}

private def validVqLogPush {PK SK M Sig : Type} (verify : PK → SK → M → Sig → Bool)
    (pk : PK) (sk : SK) (s : ValidVqLog verify pk sk) (m : M) (σ : Sig) :
    ValidVqLog verify pk sk :=
  if h : verify pk sk m σ = true then
    ⟨s.val ++ [(m, σ)], fun p hp => by
      rcases List.mem_append.mp hp with hp | hp
      · exact s.property p hp
      · rw [List.mem_singleton.mp hp]
        exact h⟩
  else
    s

private noncomputable def vqPlantedSim {PK SK M Sig : Type} [Inhabited Sig] [DecidableEq M]
    [DecidableEq Sig] (signer : Signer SK M Sig) (verify : PK → SK → M → Sig → Bool)
    (pk : PK) (sk : SK) (q : M ⊕ (M × Sig)) :
    StateT (ValidVqLog verify pk sk) PMF (forgeVqSpec M Sig q) :=
  match q with
  | .inl m => fun s =>
    match signer sk s.val m with
    | none => PMF.pure (default, s)
    | some program =>
      (ProbComp.eval program).map fun σ => (σ, validVqLogPush verify pk sk s m σ)
  | .inr p => fun s => PMF.pure (decide (p ∈ s.val), s)

private def vqExtract {M Sig : Type} [Inhabited Sig] : M ⊕ (M × Sig) → M × Sig
  | .inl m => (m, default)
  | .inr p => p

private def vqDummyReply {M Sig : Type} [Inhabited Sig] : (q : M ⊕ (M × Sig)) → forgeVqSpec M Sig q
  | .inl _ => default
  | .inr _ => false

private theorem eval_vqOracle_good_eq_sim {PK SK M Sig : Type} [Inhabited Sig] [DecidableEq M]
    [DecidableEq Sig] (signer : Signer SK M Sig) (verify : PK → SK → M → Sig → Bool)
    (pk : PK) (sk : SK)
    (hsign : ∀ log m program, signer sk log m = some program →
      ∀ σ ∈ (ProbComp.eval program).support, verify pk sk m σ = true)
    (q : M ⊕ (M × Sig)) (s : ValidVqLog verify pk sk)
    (hgood : (q.isRight &&
      match q with
      | .inl _ => false
      | .inr (m, σ) => verify pk sk m σ && freshPair m σ s.val) = false) :
    ProbComp.eval (vqOracle signer verify pk sk q ⟨s.val, false⟩) =
      (vqPlantedSim signer verify pk sk q s).map (fun x => (x.1, ⟨x.2.val, false⟩)) := by
  cases q with
  | inl m =>
    dsimp only [vqOracle, vqPlantedSim, StateT.run]
    cases hprog : signer sk s.val m with
    | none =>
      simp [ProbComp.eval_pure]
    | some program =>
      rw [ProbComp.eval_map, PMF.map_comp]
      refine PMF.map_congr_on_support (ProbComp.eval program) _ _ fun σ hσ => ?_
      have hv := hsign s.val m program hprog σ hσ
      simp [validVqLogPush, hv]
  | inr p =>
    rcases p with ⟨m, σ⟩
    simp only [Sum.isRight_inr, Bool.true_and] at hgood
    simp only [vqOracle, vqPlantedSim, ProbComp.eval_pure, PMF.pure_map, hgood, Bool.false_or]
    by_cases hmem : (m, σ) ∈ s.val
    · simp [hmem, s.property (m, σ) hmem]
    · simp only [freshPair, hmem, not_false_eq_true, decide_true, Bool.and_true] at hgood
      simp [hmem, hgood]

private theorem run_vqToForgerHandler_eq_plantedHandler {PK SK M Sig : Type} [Inhabited M]
    [Inhabited Sig] [DecidableEq M] [DecidableEq Sig]
    (admit : List (M × Sig) → M → Bool)
    (signer : Signer SK M Sig) (verify : PK → SK → M → Sig → Bool)
    (pk : PK) (sk : SK)
    (hadmit : ∀ log m, (signer sk log m).isSome = admit log m)
    (hsign : ∀ log m program, signer sk log m = some program →
      ∀ σ ∈ (ProbComp.eval program).support, verify pk sk m σ = true)
    (prog : ProbOracleComp (forgeVqSpec M Sig) Unit) (j : ℕ) :
    ProbComp.eval
      (((OracleComp.interpret
          (OracleComp.sumHandler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (vqToForgerHandler admit))
          prog).run (ProbOracleComp.PlantedOracleState.init j default [])).runLogWith
        (signer sk)) =
      (ProbOracleComp.runWith
        (ProbOracleComp.plantedHandler
          (vqPlantedSim signer verify pk sk)
          Sum.isRight vqExtract default vqDummyReply)
        prog
        (ProbOracleComp.PlantedOracleState.init j default ⟨[], by simp⟩)).map
          (fun x =>
            ((x.1, ⟨x.2.planted, x.2.oracleState.val⟩), x.2.oracleState.val)) := by
  rw [ProbOracleComp.runLogWith, ProbOracleComp.eval_runState,
    ProbOracleComp.runWith_run_interpret]
  let represent :
      ProbOracleComp.PlantedOracleState (M × Sig) (ValidVqLog verify pk sk) →
        ProbOracleComp.PlantedOracleState (M × Sig) (List (M × Sig)) × List (M × Sig) :=
    fun st => (⟨st.planted, st.oracleState.val⟩, st.oracleState.val)
  have hinit :
      (ProbOracleComp.PlantedOracleState.init j (default : M × Sig) ([] : List (M × Sig)),
        ([] : List (M × Sig))) =
      represent (ProbOracleComp.PlantedOracleState.init j default ⟨[], by simp⟩) := rfl
  have hsim := ProbOracleComp.runWith_map_state
    (oracle := ProbOracleComp.plantedHandler
      (vqPlantedSim signer verify pk sk)
      Sum.isRight vqExtract default vqDummyReply)
    (oracle' := fun q state =>
      (ProbOracleComp.runWith (fun m l => ProbComp.eval (ProbOracleComp.logOracle (signer sk) m l))
        ((vqToForgerHandler admit q).run state.1) state.2).map
        (fun ⟨⟨a, b⟩, c⟩ => (a, b, c)))
    (represent := represent)
    (step := fun q st => by
      dsimp only [ProbOracleComp.plantedHandler, vqToForgerHandler, represent, StateT.run]
      cases hcap : st.planted.hasCaptured
      · cases q with
        | inl m =>
          simp only [Bool.false_eq_true, ↓reduceIte, Sum.isRight_inl, StateLens.zoom,
            ProbOracleComp.PlantedOracleState.oracleStateLens, vqPlantedSim, PMF.monad_map_eq_map,
            PMF.map_comp, Function.comp_def]
          cases hprog : signer sk st.oracleState.val m with
          | none => simp [← hadmit, hprog]
          | some program =>
            simp only [← hadmit, hprog, Option.isSome_some, ↓reduceIte,
              ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, ProbOracleComp.logOracle,
              ProbComp.eval_map, PMF.map_comp, Function.comp_def]
            refine PMF.map_congr_on_support (ProbComp.eval program) _ _ fun σ hσ => ?_
            simp [validVqLogPush, hsign st.oracleState.val m program hprog σ hσ]
        | inr p =>
          simp only [Bool.false_eq_true, ↓reduceIte, Sum.isRight_inr, vqExtract, vqDummyReply,
            vqPlantedSim]
          cases st.planted.rem == 0 <;> simp
      · cases q <;> simp [vqDummyReply])
    prog (ProbOracleComp.PlantedOracleState.init j default ⟨[], by simp⟩)
  rw [hinit, ← hsim, PMF.map_comp]
  rfl

private theorem le_mul_add_of_le_sum {Q : ℕ} {p B c ε : ℝ≥0∞} {idx W : ℕ → ℝ≥0∞}
    (hp1 : p ≤ 1)
    (hsum : p ≤ ∑ j ∈ Finset.range Q, W j)
    (hB : ∑ j ∈ Finset.range Q, idx j * W j ≤ B)
    (hidx : ∀ j < Q, 1 ≤ c * idx j + ε) :
    p ≤ c * B + ε := by
  by_cases hε1 : 1 ≤ ε
  · exact hp1.trans (hε1.trans le_add_self)
  have hε_le : ε ≤ 1 := (not_le.mp hε1).le
  have hpt (j : ℕ) (hj : j ∈ Finset.range Q) : (1 - ε) * W j ≤ c * (idx j * W j) := calc
    (1 - ε) * W j ≤ c * idx j * W j :=
      mul_le_mul_left (tsub_le_iff_right.mpr (hidx j (Finset.mem_range.mp hj))) _
    _ = c * (idx j * W j) := mul_assoc _ _ _
  have hmul : (1 - ε) * p ≤ c * B := calc
    (1 - ε) * p ≤ (1 - ε) * ∑ j ∈ Finset.range Q, W j := mul_le_mul_right hsum _
    _ = ∑ j ∈ Finset.range Q, (1 - ε) * W j := Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ Finset.range Q, c * (idx j * W j) := Finset.sum_le_sum hpt
    _ = c * ∑ j ∈ Finset.range Q, idx j * W j := (Finset.mul_sum _ _ _).symm
    _ ≤ c * B := mul_le_mul_right hB c
  calc
    p = (1 - ε + ε) * p := by rw [tsub_add_cancel_of_le hε_le, one_mul]
    _ = (1 - ε) * p + ε * p := add_mul _ _ _
    _ ≤ c * B + ε * 1 := add_le_add hmul (mul_le_mul_right hp1 ε)
    _ = c * B + ε := by rw [mul_one]

/-- Finite index-sampler guessing step toward [BonehShoup2023], Section 6.2, Theorem 6.1
(pp. 221–223), without machine running-time certificates (not the computational result; see
`Cslib.Crypto.MACScheme.succProbability_sufCmaVqGame_le_mul_add` and
`Cslib.Crypto.MACScheme.sufCmaVq_iff_sufCma`): suppose every signature produced by `signer` verifies
(`hsign`), `admit` characterizes when `signer` accepts (`hadmit`), `A pk` makes at most `Q_v`
verification queries (`hA`), and `index` hits every `j < Q_v` according to
`1 ≤ c * Pr[index = j] + ε` (`hindex`). Then `vqForgeExperiment` accepts with probability at most
`c` times that of `forgeExperiment` with `freshPair` on `vqToForgerOn admit index A`, plus `ε`. -/
theorem eval_vqForgeExperiment_le_mul_add_of_index {PK SK M Sig : Type} [Inhabited M]
    [Inhabited Sig] [DecidableEq M] [DecidableEq Sig]
    (keyGen : ProbComp (PK × SK)) (signer : Signer SK M Sig)
    (verify : PK → SK → M → Sig → Bool)
    (admit : List (M × Sig) → M → Bool)
    (hadmit : ∀ keys ∈ (ProbComp.eval keyGen).support, ∀ log m,
      (signer keys.2 log m).isSome = admit log m)
    (hsign : ∀ keys ∈ (ProbComp.eval keyGen).support, ∀ log m program,
      signer keys.2 log m = some program →
      ∀ σ ∈ (ProbComp.eval program).support, verify keys.1 keys.2 m σ = true)
    (Q_v : ℕ) (index : ProbComp ℕ) {c ε : ℝ≥0∞}
    (hindex : ∀ j < Q_v, 1 ≤ c * ProbComp.eval index j + ε)
    {A : PK → ProbOracleComp (forgeVqSpec M Sig) Unit}
    (hA : ∀ pk, IsVerificationQueryBounded (A pk) Q_v) :
    ProbComp.eval (vqForgeExperiment keyGen signer verify A) true ≤
      c * ProbComp.eval
          (forgeExperiment keyGen signer verify freshPair (vqToForgerOn admit index A)) true +
        ε := by
  simp only [vqForgeExperiment, forgeExperiment, ProbComp.eval_bind, ProbComp.eval_pure]
  have hkey : ∀ keys ∈ (ProbComp.eval keyGen).support,
      (((ProbComp.eval (((A keys.1).runState
          (vqOracle signer verify keys.1 keys.2)).run ⟨[], false⟩)).bind
          fun x => PMF.pure x.2.won) true) ≤
        c * (((ProbComp.eval ((vqToForgerOn admit index A keys.1).runLogWith
            (signer keys.2))).bind
            fun x => PMF.pure
              (verify keys.1 keys.2 x.1.1 x.1.2 && freshPair x.1.1 x.1.2 x.2)) true) + ε := by
    rintro ⟨pk, sk⟩ hkeys
    have hsign' := hsign (pk, sk) hkeys
    have hadmit' := hadmit (pk, sk) hkeys
    let W : ℕ → ℝ≥0∞ := fun j =>
      (ProbOracleComp.runWith
        (ProbOracleComp.plantedHandler
          (vqPlantedSim signer verify pk sk)
          Sum.isRight vqExtract default vqDummyReply)
        (A pk)
        (ProbOracleComp.PlantedOracleState.init j default ⟨[], by simp⟩)).bind
        (fun x => PMF.pure
          (verify pk sk x.2.planted.candidate.1 x.2.planted.candidate.2 &&
            freshPair x.2.planted.candidate.1 x.2.planted.candidate.2 x.2.oracleState.val))
        true
    have hlhs_eq :
        (((ProbComp.eval (((A pk).runState
            (vqOracle signer verify pk sk)).run ⟨[], false⟩)).bind
            fun x => PMF.pure x.2.won) true) =
          (ProbOracleComp.runWith
            (fun q st => ProbComp.eval (vqOracle signer verify pk sk q st))
            (A pk) ⟨[], false⟩).toOuterMeasure {x | x.2.won = true} := by
      rw [ProbOracleComp.eval_runState, PMF.bind_apply, PMF.toOuterMeasure_eq_tsum_mul_indicator]
      refine tsum_congr fun x => ?_
      cases hwon : x.2.won <;> simp [hwon]
    have hunion :
        (ProbOracleComp.runWith
          (fun q st => ProbComp.eval (vqOracle signer verify pk sk q st))
          (A pk) ⟨[], false⟩).toOuterMeasure {x | x.2.won = true} ≤
          ∑ j ∈ Finset.range Q_v, W j :=
      ProbOracleComp.toOuterMeasure_bad_le_sum_planted_candidate_of_cost
        (badHandler := fun q st => ProbComp.eval (vqOracle signer verify pk sk q st))
        (bad := fun st => st.won = true)
        (embed := fun s : ValidVqLog verify pk sk => ⟨s.val, false⟩)
        (fun _ => Bool.false_ne_true)
        (vqPlantedSim signer verify pk sk)
        Sum.isRight
        (fun q s => match q with
          | .inl _ => false
          | .inr (m, σ) => verify pk sk m σ && freshPair m σ s.val)
        vqExtract default vqDummyReply
        (fun cand s => verify pk sk cand.1 cand.2 && freshPair cand.1 cand.2 s.val)
        (eval_vqOracle_good_eq_sim signer verify pk sk hsign')
        (fun q s ht hb => by cases q with
          | inl _ => simp at ht
          | inr p => exact hb)
        (hA pk)
        ⟨[], by simp⟩
    have hrhs_ge :
        ∑ j ∈ Finset.range Q_v, ProbComp.eval index j * W j ≤
          ((ProbComp.eval ((vqToForgerOn admit index A pk).runLogWith (signer sk))).bind
            fun x => PMF.pure
              (verify pk sk x.1.1 x.1.2 && freshPair x.1.1 x.1.2 x.2)) true := by
      refine (Summable.sum_le_tsum (Finset.range Q_v) (fun _ _ => zero_le)
        CompleteLattice.summable).trans_eq ?_
      symm
      rw [ProbOracleComp.runLogWith, ProbOracleComp.eval_runState]
      dsimp only [vqToForgerOn]
      rw [ProbOracleComp.runWith_sample_bind, PMF.bind_bind, PMF.bind_apply]
      refine tsum_congr fun j => congrArg (ProbComp.eval index j * ·) ?_
      rw [ProbOracleComp.runWith_bind]
      have hstep := run_vqToForgerHandler_eq_plantedHandler admit signer verify pk sk
        hadmit' hsign' (A pk) j
      rw [ProbOracleComp.runLogWith, ProbOracleComp.eval_runState] at hstep
      rw [hstep, PMF.bind_map, PMF.bind_bind]
      change ((ProbOracleComp.runWith _ (A pk) _).bind fun x => _) true = W j
      dsimp only [W]
      congr 2 with x : 1
      simp [ProbOracleComp.runWith_pure]
    rw [hlhs_eq]
    exact le_mul_add_of_le_sum (PMF.toOuterMeasure_le_one _ _) hunion hrhs_ge hindex
  exact PMF.bind_apply_le_mul_bind_apply_add_on_support (ProbComp.eval keyGen) hkey

/-- Finite query-bounded step toward [BonehShoup2023], Section 6.2, Theorem 6.1 (pp. 221–223),
without machine running-time certificates (not the cited computational result; see
`Cslib.Crypto.MACScheme.succProbability_sufCmaVqGame_le_mul_add` and
`Cslib.Crypto.MACScheme.sufCmaVq_iff_sufCma`): when every signature produced by `signer` verifies
and `admit` characterizes when `signer` accepts, an adversary making at most `Q_v` verification
queries wins `vqForgeExperiment` with probability at most `Q_v` times the success probability of
`vqToForgerOn admit (Fin.val <$> ProbComp.unifFin (Q_v - 1)) A` in `forgeExperiment` with
`freshPair`. Holds for every `Q_v : ℕ`, including `Q_v = 0`. -/
theorem succProbability_vqForgeExperiment_le_mul {PK SK M Sig : Type} [Inhabited M]
    [Inhabited Sig] [DecidableEq M] [DecidableEq Sig]
    (keyGen : ProbComp (PK × SK)) (signer : Signer SK M Sig)
    (verify : PK → SK → M → Sig → Bool)
    (admit : List (M × Sig) → M → Bool)
    (hadmit : ∀ keys ∈ (ProbComp.eval keyGen).support, ∀ log m,
      (signer keys.2 log m).isSome = admit log m)
    (hsign : ∀ keys ∈ (ProbComp.eval keyGen).support, ∀ log m program,
      signer keys.2 log m = some program →
      ∀ σ ∈ (ProbComp.eval program).support, verify keys.1 keys.2 m σ = true)
    (Q_v : ℕ) {A : PK → ProbOracleComp (forgeVqSpec M Sig) Unit}
    (hA : ∀ pk, IsVerificationQueryBounded (A pk) Q_v) :
    Experiment.succProbability (vqForgeExperiment keyGen signer verify A) ≤
      Q_v * Experiment.succProbability
        (forgeExperiment keyGen signer verify freshPair
          (vqToForgerOn admit (Fin.val <$> ProbComp.unifFin (Q_v - 1)) A)) := by
  rcases Nat.eq_zero_or_pos Q_v with rfl | hQv
  · simp [succProbability_vqForgeExperiment_zero keyGen signer verify hA]
  obtain ⟨m, rfl⟩ : ∃ m, Q_v = m + 1 := ⟨Q_v - 1, (Nat.sub_add_cancel hQv).symm⟩
  rw [Nat.add_sub_cancel]
  have hle := eval_vqForgeExperiment_le_mul_add_of_index keyGen signer verify admit hadmit hsign
    (m + 1) (Fin.val <$> ProbComp.unifFin m) (c := ((m + 1 : ℕ) : ℝ≥0∞)) (ε := 0)
    (fun j hj => by
      have hj_val : ProbComp.eval (Fin.val <$> ProbComp.unifFin m) j =
          ((m + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
        rw [ProbComp.eval_map, ProbComp.eval_unifFin]
        simpa [PMF.uniformOfFintype_apply] using
          PMF.map_apply_of_injective (PMF.uniformOfFintype (Fin (m + 1))) Fin.val_injective ⟨j, hj⟩
      rw [add_zero, hj_val, ENNReal.mul_inv_cancel (by simp) (ENNReal.natCast_ne_top _)])
    hA
  rw [add_zero] at hle
  simp only [Experiment.succProbability, Game.succProbability]
  rw [← ENNReal.toNNReal_natCast, ← ENNReal.toNNReal_mul]
  exact ENNReal.toNNReal_mono
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (PMF.apply_ne_top _ _)) hle

/-- Finite query-bounded step toward [BonehShoup2023], Section 6.2, Theorem 6.1 (pp. 221–223) for
unrestricted signers (`Signer.ofSign`), without machine running-time certificates (not the cited
computational result; see `Cslib.Crypto.MACScheme.sufCmaVq_iff_sufCma`): when every signature in the
support of `sign sk m` verifies, `vqForgeExperiment` success probability for any
`Q_v`-verification-query adversary is at most `Q_v` times the `freshPair` `forgeExperiment` success
probability of `vqToForger (Fin.val <$> ProbComp.unifFin (Q_v - 1)) A`. -/
theorem succProbability_vqForgeExperiment_ofSign_le_mul {PK SK M Sig : Type} [Inhabited M]
    [Inhabited Sig] [DecidableEq M] [DecidableEq Sig]
    (keyGen : ProbComp (PK × SK)) (sign : SK → M → ProbComp Sig)
    (verify : PK → SK → M → Sig → Bool)
    (hsign : ∀ keys ∈ (ProbComp.eval keyGen).support, ∀ m σ,
      σ ∈ (ProbComp.eval (sign keys.2 m)).support → verify keys.1 keys.2 m σ = true)
    (Q_v : ℕ) {A : PK → ProbOracleComp (forgeVqSpec M Sig) Unit}
    (hA : ∀ pk, IsVerificationQueryBounded (A pk) Q_v) :
    Experiment.succProbability (vqForgeExperiment keyGen (Signer.ofSign sign) verify A) ≤
      Q_v * Experiment.succProbability
        (forgeExperiment keyGen (Signer.ofSign sign) verify freshPair
          (vqToForger (Fin.val <$> ProbComp.unifFin (Q_v - 1)) A)) :=
  succProbability_vqForgeExperiment_le_mul keyGen (Signer.ofSign sign) verify (fun _ _ => true)
    (fun _ _ _ _ => rfl)
    (fun keys hkeys _ m program hprog σ hσ => by
      simp only [Signer.ofSign_apply, Option.some.injEq] at hprog
      subst hprog
      exact hsign keys hkeys m σ hσ)
    Q_v hA

/-- Finite query-bounded fair-coin `sampleModIndex` step toward [BonehShoup2023], Section 6.2,
Theorem 6.1 (pp. 221–223), without machine running-time certificates (not the cited computational
result; see `Cslib.Crypto.MACScheme.succProbability_sufCmaVqGame_le_mul_add`): drawing the planted
verification-query index via `ProbComp.sampleModIndex width Q_v` from `width` fair coins gives the
factor `Q_v` plus the dyadic bias `Q_v / 2 ^ width`, for every `width` and `Q_v` (including
`Q_v = 0`). -/
theorem eval_vqForgeExperiment_le_mul_sampleModIndex_add {PK SK M Sig : Type} [Inhabited M]
    [Inhabited Sig] [DecidableEq M] [DecidableEq Sig]
    (keyGen : ProbComp (PK × SK)) (signer : Signer SK M Sig)
    (verify : PK → SK → M → Sig → Bool)
    (admit : List (M × Sig) → M → Bool)
    (hadmit : ∀ keys ∈ (ProbComp.eval keyGen).support, ∀ log m,
      (signer keys.2 log m).isSome = admit log m)
    (hsign : ∀ keys ∈ (ProbComp.eval keyGen).support, ∀ log m program,
      signer keys.2 log m = some program →
      ∀ σ ∈ (ProbComp.eval program).support, verify keys.1 keys.2 m σ = true)
    (width Q_v : ℕ) {A : PK → ProbOracleComp (forgeVqSpec M Sig) Unit}
    (hA : ∀ pk, IsVerificationQueryBounded (A pk) Q_v) :
    ProbComp.eval (vqForgeExperiment keyGen signer verify A) true ≤
      Q_v * ProbComp.eval
          (forgeExperiment keyGen signer verify freshPair
            (vqToForgerOn admit (ProbComp.sampleModIndex width Q_v) A)) true +
        Q_v / 2 ^ width := by
  refine eval_vqForgeExperiment_le_mul_add_of_index keyGen signer verify admit hadmit hsign Q_v
    (ProbComp.sampleModIndex width Q_v) (fun j hj => ?_) hA
  rw [ProbComp.sampleModIndex_eq_sampleModNat width ((Nat.zero_le j).trans_lt hj)]
  exact ProbComp.one_le_mul_eval_sampleModNat_add hj

/-- Finite query-bounded exact dyadic `sampleModIndex` step toward [BonehShoup2023], Section 6.2,
Theorem 6.1 (pp. 221–223), without machine running-time certificates (not the cited computational
result; see `Cslib.Crypto.MACScheme.succProbability_sufCmaVqGame_le_mul`): proves the exact
factor-`Q_v` bound with no additive error term when `Q_v = 0` (where `vqForgeExperiment` accepts
with probability `0` via `eval_vqForgeExperiment_zero`) or when `Q_v` divides `2 ^ width` (where
`0 < Q_v` and `ProbComp.sampleModIndex width Q_v` is uniform below `Q_v`). -/
theorem eval_vqForgeExperiment_le_mul_sampleModIndex_of_dvd {PK SK M Sig : Type} [Inhabited M]
    [Inhabited Sig] [DecidableEq M] [DecidableEq Sig]
    (keyGen : ProbComp (PK × SK)) (signer : Signer SK M Sig)
    (verify : PK → SK → M → Sig → Bool)
    (admit : List (M × Sig) → M → Bool)
    (hadmit : ∀ keys ∈ (ProbComp.eval keyGen).support, ∀ log m,
      (signer keys.2 log m).isSome = admit log m)
    (hsign : ∀ keys ∈ (ProbComp.eval keyGen).support, ∀ log m program,
      signer keys.2 log m = some program →
      ∀ σ ∈ (ProbComp.eval program).support, verify keys.1 keys.2 m σ = true)
    (width Q_v : ℕ) (hdvd : Q_v = 0 ∨ Q_v ∣ 2 ^ width)
    {A : PK → ProbOracleComp (forgeVqSpec M Sig) Unit}
    (hA : ∀ pk, IsVerificationQueryBounded (A pk) Q_v) :
    ProbComp.eval (vqForgeExperiment keyGen signer verify A) true ≤
      Q_v * ProbComp.eval
        (forgeExperiment keyGen signer verify freshPair
          (vqToForgerOn admit (ProbComp.sampleModIndex width Q_v) A)) true := by
  rcases hdvd with rfl | hdvd
  · simp [eval_vqForgeExperiment_zero keyGen signer verify hA]
  simpa using eval_vqForgeExperiment_le_mul_add_of_index keyGen signer verify admit hadmit hsign
    Q_v (ProbComp.sampleModIndex width Q_v) (c := (Q_v : ℝ≥0∞)) (ε := 0)
    (fun j hj => by
      rw [add_zero, ProbComp.sampleModIndex_eq_sampleModNat width ((Nat.zero_le j).trans_lt hj)]
      exact ProbComp.one_le_mul_eval_sampleModNat_of_dvd hj hdvd)
    hA

/-! ### Finite Exercise 6.2: PRF-based MAC with verification queries -/

/-- Stateful handler for `vqMacToPrfAdversary`:
* `.inl m` queries `m` on the external function oracle, appends `(m, σ)` to `st.log`, and returns
  `σ`;
* `.inr (m, σ)` returns `true` locally when `(m, σ) ∈ st.log` (avoiding a redundant oracle call),
  and otherwise queries `m` on the external function oracle, sets `ok := decide (τ = σ)`, latches
  `st.won || ok`, and returns `ok`. -/
@[expose] def vqMacToPrfHandler {D R : Type} [DecidableEq D] [DecidableEq R]
    (q : D ⊕ (D × R)) :
    StateT (VqOracleState D R) (ProbOracleComp (fun _ : D => R)) (forgeVqSpec D R q) :=
  match q with
  | .inl m => fun st =>
    (fun σ => (σ, ⟨st.log ++ [(m, σ)], st.won⟩)) <$> ProbOracleComp.query m
  | .inr (m, σ) => fun st =>
    if (m, σ) ∈ st.log then
      pure (true, st)
    else
      (fun τ =>
        let ok := decide (τ = σ)
        (ok, ⟨st.log, st.won || ok⟩)) <$> ProbOracleComp.query m

/-- Direct reduction from `vqForgeExperiment` on a deterministic keyed function `F : Key → D → R`
to `PRF.Adversary D R` ([BonehShoup2023], Exercise 6.2, p. 246): simulate `A ()` via
`vqMacToPrfHandler` and output `st.won`. Unlike `vqToForger`, this reduction guesses no index and
forwards both signing and fresh verification queries directly to the PRF oracle. -/
@[expose] def vqMacToPrfAdversary {D R : Type} [DecidableEq D] [DecidableEq R]
    (A : Unit → ProbOracleComp (forgeVqSpec D R) Unit) : PRF.Adversary D R :=
  show ProbOracleComp (fun _ : D => R) Bool from do
    let (_, st) ← (OracleComp.interpret
      (OracleComp.sumHandler
        (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        vqMacToPrfHandler)
      (A ())).run ⟨[], false⟩
    return st.won

/-- `vqMacToPrfAdversary A` makes at most `Q_s + Q_v` function queries when `A ()` makes at most
`Q_s` signing queries and at most `Q_v` verification queries. -/
theorem isQueryBounded_vqMacToPrfAdversary {D R : Type} [DecidableEq D] [DecidableEq R]
    {A : Unit → ProbOracleComp (forgeVqSpec D R) Unit} {Q_s Q_v : ℕ}
    (hs : IsSigningQueryBounded (A ()) Q_s) (hv : IsVerificationQueryBounded (A ()) Q_v) :
    (vqMacToPrfAdversary A).IsQueryBounded (Q_s + Q_v) := by
  unfold vqMacToPrfAdversary
  refine ((OracleComp.IsCostBounded.run_interpret ?_
    (IsQueryBounded.of_signing_and_verification hs hv) _).bind
    fun _ => .pure _ 0).mono (by omega)
  rintro (k | (m | ⟨m, σ⟩)) s
  · exact (ProbOracleComp.IsQueryBounded.sample (ProbComp.unifFin k)).bind fun a => .pure (a, s) 0
  · exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (ProbOracleComp.IsQueryBounded.query m)
  · dsimp only [OracleComp.sumHandler, vqMacToPrfHandler, StateT.run]
    split_ifs
    · exact .pure _ 1
    · exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (ProbOracleComp.IsQueryBounded.query m)

private abbrev ValidPrfVqState {D R : Type} (f : D → R) :=
  {st : VqOracleState D R // ∀ p ∈ st.log, f p.1 = p.2}

private noncomputable def validPrfVqStep {D R : Type} [DecidableEq D] [DecidableEq R]
    (f : D → R) (q : D ⊕ (D × R)) :
    StateT (ValidPrfVqState f) PMF (forgeVqSpec D R q) :=
  match q with
  | .inl m => fun s =>
    PMF.pure (f m, ⟨⟨s.val.log ++ [(m, f m)], s.val.won⟩, fun p hp => by
      rcases List.mem_append.mp hp with hp | hp
      · exact s.property p hp
      · rw [List.mem_singleton.mp hp]⟩)
  | .inr (m, σ) => fun s =>
    let ok := decide (f m = σ)
    PMF.pure (ok, ⟨⟨s.val.log, s.val.won || (ok && freshPair m σ s.val.log)⟩, s.property⟩)

private theorem eval_interpret_pure_run_interpret {D R S α β : Type} {spec : OracleSpec β}
    (f : D → R) (h : (q : β) → StateT S (ProbOracleComp (fun _ : D => R)) (spec q))
    (prog : ProbOracleComp spec α) (init : S) :
    ProbComp.eval (OracleComp.interpret
      (OracleComp.sumHandler ProbComp.unifFin fun x => pure (f x))
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k))) h)
        prog).run init)) =
      (ProbOracleComp.runWith
        (fun q state =>
          (ProbOracleComp.runWith (fun x (u : Unit) => (PMF.pure (f x)).map (·, u))
            ((h q).run state.1) state.2).map (fun ⟨⟨a, b⟩, c⟩ => (a, b, c)))
        prog (init, ())).map (fun ⟨a, s, _⟩ => (a, s)) := by
  have hfst := congrArg (PMF.map Prod.fst) (ProbOracleComp.runWith_readOnly
    (fun x (_ : Unit) => PMF.pure (f x))
    ((OracleComp.interpret
      (OracleComp.sumHandler
        (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k))) h)
      prog).run init) ())
  simp only [PMF.map_comp, Function.comp_def, show (fun x : α × S => x) = id from rfl,
    PMF.map_id] at hfst
  rw [ProbOracleComp.eval_interpret]
  simp only [ProbComp.eval_pure]
  rw [← OracleComp.evalWith_eq_interpret, ← hfst, ProbOracleComp.runWith_run_interpret,
    PMF.map_comp]
  rfl

private theorem eval_run_vqMacToPrfAdversary_pure {D R : Type} [Inhabited R] [DecidableEq D]
    [DecidableEq R] (A : Unit → ProbOracleComp (forgeVqSpec D R) Unit) (f : D → R) :
    ProbComp.eval ((vqMacToPrfAdversary A).run fun x => pure (f x)) =
      (ProbComp.eval (((A ()).runState
        (vqOracle (Signer.ofSign fun g : D → R => fun m => pure (g m))
          (fun (_ : Unit) (g : D → R) m σ => decide (g m = σ)) () f)).run ⟨[], false⟩)).bind
        fun x => PMF.pure x.2.won := by
  have hlhs :
      ProbComp.eval (OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifFin fun x => pure (f x))
        ((OracleComp.interpret
          (OracleComp.sumHandler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            vqMacToPrfHandler)
          (A ())).run ⟨[], false⟩)) =
      (ProbOracleComp.runWith (validPrfVqStep f) (A ()) ⟨⟨[], false⟩, by simp⟩).map
        (fun x => (x.1, x.2.val)) := by
    rw [eval_interpret_pure_run_interpret]
    have hsim := ProbOracleComp.runWith_map_state
      (oracle := validPrfVqStep f)
      (oracle' := fun q state =>
        (ProbOracleComp.runWith (fun x (u : Unit) => (PMF.pure (f x)).map (·, u))
          ((vqMacToPrfHandler q).run state.1) state.2).map (fun ⟨⟨a, b⟩, c⟩ => (a, b, c)))
      (represent := fun s : ValidPrfVqState f => (s.val, ()))
      (step := fun q s => by
        cases q with
        | inl m =>
          dsimp only [validPrfVqStep, vqMacToPrfHandler, StateT.run]
          simp [ProbOracleComp.runWith_map, ProbOracleComp.runWith_query]
        | inr p =>
          rcases p with ⟨m, σ⟩
          dsimp only [validPrfVqStep, vqMacToPrfHandler, StateT.run]
          by_cases hmem : (m, σ) ∈ s.val.log
          · simp [hmem, s.property (m, σ) hmem, freshPair]
          · simp [hmem, freshPair, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query])
      (A ()) ⟨⟨[], false⟩, by simp⟩
    rw [← hsim, PMF.map_comp]; rfl
  have hrhs :
      ProbComp.eval (((A ()).runState
        (vqOracle (Signer.ofSign fun g : D → R => fun m => pure (g m))
          (fun (_ : Unit) (g : D → R) m σ => decide (g m = σ)) () f)).run ⟨[], false⟩) =
      (ProbOracleComp.runWith (validPrfVqStep f) (A ()) ⟨⟨[], false⟩, by simp⟩).map
        (fun x => (x.1, x.2.val)) := by
    rw [ProbOracleComp.eval_runState]
    exact (ProbOracleComp.runWith_map_state
      (oracle := validPrfVqStep f)
      (oracle' := fun q st => ProbComp.eval
        (vqOracle (Signer.ofSign fun g : D → R => fun m => pure (g m))
          (fun (_ : Unit) (g : D → R) m σ => decide (g m = σ)) () f q st))
      (represent := Subtype.val)
      (step := fun q s => by cases q <;> simp [validPrfVqStep, vqOracle, Signer.ofSign])
      (A ()) ⟨⟨[], false⟩, by simp⟩).symm
  unfold vqMacToPrfAdversary
  simp only [ProbOracleComp.run, OracleComp.interpret_bind, OracleComp.interpret_pure,
    ProbComp.eval_bind, ProbComp.eval_pure]
  rw [hlhs, hrhs]

/-- Running `vqMacToPrfAdversary A` in `PRF.realExperiment F` has the exact Boolean law of
`vqForgeExperiment` against the deterministic MAC `(k, m) ↦ F k m`. -/
theorem eval_realExperiment_vqMacToPrfAdversary {Key D R : Type} [Fintype Key] [Nonempty Key]
    [Inhabited R] [DecidableEq D] [DecidableEq R] (F : Key → D → R)
    (A : Unit → ProbOracleComp (forgeVqSpec D R) Unit) :
    ProbComp.eval (PRF.realExperiment F (vqMacToPrfAdversary A)) =
      ProbComp.eval
        (vqForgeExperiment (((), ·) <$> ProbComp.uniform Key)
          (Signer.ofSign fun k m => pure (F k m))
          (fun _ k m σ => decide (F k m = σ)) A) := by
  simp only [PRF.realExperiment, vqForgeExperiment, pmf_norm]
  refine PMF.bind_congr_on_support _ _ _ fun key _ => ?_
  rw [eval_run_vqMacToPrfAdversary_pure, ProbOracleComp.eval_runState, ProbOracleComp.eval_runState]
  congr 2

private def recordQueriesHandler {D R : Type} (q : D) :
    StateT (List D) (ProbOracleComp (fun _ : D => R)) R :=
  fun l => (fun r => (r, q :: l)) <$> ProbOracleComp.query q

private theorem succProbability_forgeExperiment_uniformFunction_le {D R : Type} [Fintype D]
    [DecidableEq D] [Fintype R] [DecidableEq R] [Inhabited R]
    (B : Unit → ProbOracleComp (fun _ : D => R) (D × R)) :
    Experiment.succProbability
        (forgeExperiment (((), ·) <$> ProbComp.uniform (D → R))
          (Signer.ofSign fun f m => pure (f m))
          (fun _ f m σ => decide (f m = σ)) freshPair B) ≤
      (Fintype.card R : ℝ≥0)⁻¹ := by
  have heq := forgeExperiment_freshPair_eq_freshMessage
    (keyGen := ((), ·) <$> ProbComp.uniform (D → R))
    (signer := Signer.ofSign fun f : D → R => fun m => pure (f m))
    (verify := fun (_ : Unit) (f : D → R) m σ => decide (f m = σ))
    (fun ⟨⟨⟩, f⟩ _ _ m program hprog σ hσ => by
      simp only [Signer.ofSign_apply, Option.some.injEq] at hprog
      subst hprog
      simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hσ
      simp [hσ])
    (fun ⟨⟨⟩, f⟩ _ m σ σ' h1 h2 => by
      simp only [decide_eq_true_eq] at h1 h2
      exact h1.symm.trans h2)
    B
  let test : ProbOracleComp (fun _ : D => R) Bool := do
    let ((m, σ), queried) ← (OracleComp.interpret
      (OracleComp.sumHandler
        (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        recordQueriesHandler)
      (B ())).run []
    if decide (m ∉ queried) then
      (fun r => decide (r = σ)) <$> ProbOracleComp.query m
    else
      pure false
  have htest_eq :
      ProbComp.eval
        (forgeExperiment (((), ·) <$> ProbComp.uniform (D → R))
          (Signer.ofSign fun f m => pure (f m))
          (fun _ f m σ => decide (f m = σ)) freshMessage B) =
      ProbComp.eval (PRF.idealExperiment test) := by
    simp only [forgeExperiment, PRF.idealExperiment, pmf_norm]
    refine PMF.bind_congr_on_support _ _ _ fun f _ => ?_
    have hlog :
        ProbComp.eval (OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifFin fun x => pure (f x))
          ((OracleComp.interpret
            (OracleComp.sumHandler
              (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
              recordQueriesHandler)
            (B ())).run [])) =
        (ProbComp.eval
          ((B ()).runLogWith (Signer.ofSign (fun g : D → R => fun m => pure (g m)) f))).map
          (fun x => (x.1, (x.2.map Prod.fst).reverse)) := by
      rw [eval_interpret_pure_run_interpret, ProbOracleComp.runLogWith,
        ProbOracleComp.eval_runState]
      have hsim := ProbOracleComp.runWith_map_state
        (oracle := fun m log =>
          ProbComp.eval (ProbOracleComp.logOracle
            (Signer.ofSign (fun g : D → R => fun q => pure (g q)) f) m log))
        (oracle' := fun q state =>
          (ProbOracleComp.runWith (fun x (u : Unit) => (PMF.pure (f x)).map (·, u))
            ((recordQueriesHandler q).run state.1) state.2).map (fun ⟨⟨a, b⟩, c⟩ => (a, b, c)))
        (represent := fun log : List (D × R) => ((log.map Prod.fst).reverse, ()))
        (step := fun m log => by
          dsimp only [recordQueriesHandler, StateT.run]
          simp [ProbOracleComp.logOracle, Signer.ofSign, ProbOracleComp.runWith_map,
            ProbOracleComp.runWith_query])
        (B ()) []
      simp only [List.map_nil, List.reverse_nil] at hsim
      rw [← hsim, PMF.map_comp]; rfl
    dsimp only [test, ProbOracleComp.run]
    simp only [OracleComp.interpret_bind, ProbComp.eval_bind]
    rw [hlog, PMF.bind_map]
    refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨m, σ⟩, log⟩ _ => ?_
    dsimp only [Function.comp_def]
    by_cases hmem : m ∈ log.map Prod.fst <;> simp [hmem, freshMessage]
  have hbound : ProbComp.eval (PRF.idealExperiment test) true ≤ (Fintype.card R : ℝ≥0∞)⁻¹ := by
    rw [PRF.eval_idealExperiment_eq_runWith_memoize]
    dsimp only [test]
    rw [ProbOracleComp.runWith_bind, PMF.map_bind, ProbOracleComp.runWith_run_interpret,
      PMF.bind_map]
    refine PMF.bind_apply_le_on_support _ fun ⟨⟨m, σ⟩, queried, cache⟩ hsupp => ?_
    have hinv : ∀ x, cache.lookup x ≠ none → x ∈ queried := by
      refine ProbOracleComp.runWith_invariant
        (fun q state =>
          (ProbOracleComp.runWith (memoize fun _ : D => PMF.uniformOfFintype R)
            ((recordQueriesHandler q).run state.1) state.2).map
            (fun ⟨⟨a, b⟩, c⟩ => (a, b, c)))
        (fun s : List D × List (D × R) => ∀ x, s.2.lookup x ≠ none → x ∈ s.1)
        (fun q ⟨ql, c⟩ hs a ⟨ql', c'⟩ hstep x hx => ?_)
        (B ()) ([], []) (by simp) (m, σ) (queried, cache) hsupp
      dsimp only [recordQueriesHandler, StateT.run] at hstep
      simp only [ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, PMF.map_comp,
        Function.comp_def, PMF.mem_support_map_iff] at hstep
      obtain ⟨⟨r, nextCache⟩, hmem_step, hpair⟩ := hstep
      rcases Prod.mk.inj hpair with ⟨-, rfl, rfl⟩
      cases hlook : c.lookup q with
      | some v =>
        rw [memoize_of_some _ _ _ _ hlook] at hmem_step
        simp only [PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem_step
        rcases hmem_step with ⟨_, rfl⟩
        exact List.mem_cons_of_mem _ (hs x hx)
      | none =>
        rw [memoize_of_none _ _ _ hlook] at hmem_step
        simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
          PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem_step
        obtain ⟨v, -, -, rfl⟩ := hmem_step
        by_cases hxq : x = q
        · exact List.mem_cons.mpr (.inl hxq)
        · dsimp only [Prod.map, id] at hx
          simp only [List.lookup_cons, beq_eq_false_iff_ne.mpr hxq] at hx
          exact List.mem_cons_of_mem _ (hs x hx)
    dsimp only [Function.comp_def]
    by_cases hfresh : m ∉ queried
    · have hnone : cache.lookup m = none := by
        by_contra hsome
        exact hfresh (hinv m hsome)
      simp only [decide_eq_true hfresh, ↓reduceIte, ProbOracleComp.runWith_map,
        ProbOracleComp.runWith_query, memoize_of_none _ _ _ hnone, Prod.map_fst, pmf_norm]
      rw [PMF.bind_apply, tsum_eq_single σ fun r hr => by simp [hr]]
      simp [PMF.uniformOfFintype_apply]
    · simp [hfresh]
  simp only [Experiment.succProbability, Game.succProbability]
  rw [heq, htest_eq]
  exact (ENNReal.toNNReal_mono (ENNReal.inv_ne_top.mpr (by simp [Fintype.card_ne_zero]))
    hbound).trans_eq (by rw [ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast])

/-- Finite query-bounded step toward [BonehShoup2023], Section 6.14, Exercise 6.2 (p. 246),
without machine running-time certificates (not the cited computational result; see
`Cslib.Crypto.succProbability_sufCmaVqGame_prfMAC_le` and
`Cslib.Crypto.PseudorandomFunction.sufCmaVq_prfMAC`): for any finite keyed function
`F : Key → D → R` and any adversary `A` making at most `Q_v` verification queries, the success
probability of `A` in `vqForgeExperiment` against the deterministic MAC `(k, m) ↦ F k m` is at most
`PRF.advantage F (vqMacToPrfAdversary A) + Q_v / Fintype.card R` (without a `Q_v` factor on the PRF
advantage). When `A ()` also makes at most `Q_s` signing queries, `vqMacToPrfAdversary A` makes at
most `Q_s + Q_v` PRF queries (`isQueryBounded_vqMacToPrfAdversary`). -/
theorem succProbability_vqForgeExperiment_prf_le {Key D R : Type} [Fintype Key] [Nonempty Key]
    [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R] [Nonempty R]
    (F : Key → D → R) (Q_v : ℕ)
    {A : Unit → ProbOracleComp (forgeVqSpec D R) Unit}
    (hA : IsVerificationQueryBounded (A ()) Q_v) :
    have : Inhabited R := Classical.inhabited_of_nonempty ‹Nonempty R›
    Experiment.succProbability
        (vqForgeExperiment (((), ·) <$> ProbComp.uniform Key)
          (Signer.ofSign fun k m => pure (F k m))
          (fun _ k m σ => decide (F k m = σ)) A) ≤
      PRF.advantage F (vqMacToPrfAdversary A) + Q_v / Fintype.card R := by
  let _ : Inhabited R := Classical.inhabited_of_nonempty ‹Nonempty R›
  have hreal := eval_realExperiment_vqMacToPrfAdversary F A
  have hideal :
      ProbComp.eval (PRF.idealExperiment (vqMacToPrfAdversary A)) =
        ProbComp.eval
          (vqForgeExperiment (((), ·) <$> ProbComp.uniform (D → R))
            (Signer.ofSign fun f m => pure (f m))
            (fun _ f m σ => decide (f m = σ)) A) :=
    eval_realExperiment_vqMacToPrfAdversary (id : (D → R) → D → R) A
  have hideal_le :
      Experiment.succProbability (PRF.idealExperiment (vqMacToPrfAdversary A)) ≤
        Q_v / Fintype.card R := by
    rw [Experiment.succProbability, hideal, ← Experiment.succProbability]
    by_cases hD : Nonempty D
    · let _ : Inhabited D := Classical.inhabited_of_nonempty hD
      calc Experiment.succProbability
            (vqForgeExperiment (((), ·) <$> ProbComp.uniform (D → R))
              (Signer.ofSign fun f m => pure (f m))
              (fun _ f m σ => decide (f m = σ)) A)
          ≤ Q_v * Experiment.succProbability
              (forgeExperiment (((), ·) <$> ProbComp.uniform (D → R))
                (Signer.ofSign fun f m => pure (f m))
                (fun _ f m σ => decide (f m = σ)) freshPair
                (vqToForger (Fin.val <$> ProbComp.unifFin (Q_v - 1)) A)) :=
            succProbability_vqForgeExperiment_ofSign_le_mul _ _ _
              (fun keys _ m σ hσ => by
                simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hσ
                simp [hσ])
              Q_v (fun _ => hA)
        _ ≤ Q_v * (Fintype.card R : ℝ≥0)⁻¹ :=
            mul_le_mul_of_nonneg_left (succProbability_forgeExperiment_uniformFunction_le _)
              zero_le
        _ = Q_v / Fintype.card R := div_eq_mul_inv _ _
    · have _ : IsEmpty D := not_nonempty_iff.mp hD
      have hzero : IsVerificationQueryBounded (A ()) 0 :=
        OracleComp.IsCostBounded.of_forall_cost_eq_zero (fun q => by
          rcases q with _ | (m | p)
          · rfl
          · exact IsEmpty.elim ‹_› m
          · exact IsEmpty.elim ‹_› p.1) (A ())
      rw [succProbability_vqForgeExperiment_zero _ _ _ fun _ => hzero]
      exact zero_le
  change Game.succProbability (ProbComp.eval (vqForgeExperiment _ _ _ A)) ≤ _
  rw [← hreal]
  calc Game.succProbability (ProbComp.eval (PRF.realExperiment F (vqMacToPrfAdversary A)))
      = Game.advantage (ProbComp.eval (PRF.realExperiment F (vqMacToPrfAdversary A)))
          (PMF.pure false) := (Game.advantage_pure_false _).symm
    _ ≤ PRF.advantage F (vqMacToPrfAdversary A) +
          Game.advantage (ProbComp.eval (PRF.idealExperiment (vqMacToPrfAdversary A)))
            (PMF.pure false) := Game.advantage_triangle _ _ _
    _ = PRF.advantage F (vqMacToPrfAdversary A) +
          Experiment.succProbability (PRF.idealExperiment (vqMacToPrfAdversary A)) := by
        rw [Game.advantage_pure_false]
    _ ≤ PRF.advantage F (vqMacToPrfAdversary A) + Q_v / Fintype.card R :=
        add_le_add le_rfl hideal_le

end Cslib.Crypto
