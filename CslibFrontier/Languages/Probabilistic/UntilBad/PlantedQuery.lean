/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.Lens
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event

/-!
# Adaptive planted-query union bounds for `ProbOracleComp`

In a multi-query reduction (such as chosen-ciphertext decryption-rejection hops or adaptive
search-to-decision reductions), an adversary interacts with an oracle that latches a bad event on
the first target query satisfying `isBad q s`, while a reduction guesses the zero-based target-query
index `j < Q` uniformly, simulates the `< j` target queries faithfully with `sim`, captures
`extract q` on target query `j`, and answers query `j` and all subsequent queries with `dummyReply`
without further state changes.

`plantedHandler` packages that countdown-and-capture state machine over the named composite record
`PlantedOracleState Cand State`, using `StateLens.zoom` on passive (`isTarget q = false`) calls.
`toOuterMeasure_bad_le_sum_planted_of_cost` proves the adaptive union bound once by induction on
the structural target-query budget `IsCostBounded`: the probability of reaching `bad` from
`embed s` is at most the sum over `j ∈ Finset.range Q` of the probability that the `j`-th planted
execution captures a winning candidate (`hasCaptured ∧ win candidate oracleState`).
`toOuterMeasure_bad_le_sum_planted` specializes `isTarget` to `fun _ => true` for total external
query budgets `ProbOracleComp.IsQueryBounded program Q`.

## Main definitions

* `Cslib.ProbOracleComp.PlantedState`: countdown `rem`, capture flag `hasCaptured`, and captured
  `candidate`.
* `Cslib.ProbOracleComp.PlantedOracleState`: composite state pairing `PlantedState Cand` with the
  underlying oracle state `State`, equipped with `plantedLens` and `oracleStateLens`.
* `Cslib.ProbOracleComp.plantedHandler`: stateful planted-index countdown handler.

## Main results

* `Cslib.ProbOracleComp.runWith_plantedHandler_captured_bind_eq_one`: once `hasCaptured = true`,
  `plantedHandler` freezes `PlantedOracleState` across any adaptive continuation.
* `Cslib.ProbOracleComp.toOuterMeasure_bad_le_sum_planted_of_cost`,
  `Cslib.ProbOracleComp.toOuterMeasure_bad_le_sum_planted_candidate_of_cost`: cost-filtered
  adaptive planted-query union bounds over `j ∈ Finset.range Q`.
* `Cslib.ProbOracleComp.toOuterMeasure_bad_le_sum_planted`: unit-cost `IsQueryBounded`
  planted-query union bound over `j ∈ Finset.range Q`.
-/

public section

namespace Cslib.ProbOracleComp

open Probability
open scoped ENNReal

/-- Countdown and capture state for a planted-query reduction: skips `rem` target queries, captures
a `Cand` value on the next target query (`hasCaptured = true`), and freezes thereafter. -/
structure PlantedState (Cand : Type*) where
  /-- Number of target queries still to skip before capturing. -/
  rem : ℕ
  /-- Whether the target query at the planted index has already been captured. -/
  hasCaptured : Bool
  /-- Captured candidate value (initialized to a default value while `hasCaptured = false`). -/
  candidate : Cand
  deriving DecidableEq, Repr

/-- Initial `PlantedState` targeting zero-based query index `j` with fallback `defaultCand`. -/
@[expose] def PlantedState.init {Cand : Type*} (j : ℕ) (defaultCand : Cand) : PlantedState Cand :=
  ⟨j, false, defaultCand⟩

/-- Composite state pairing a `PlantedState Cand` countdown with an underlying oracle state
`State`. -/
structure PlantedOracleState (Cand State : Type*) where
  /-- Countdown and capture state of the planted-query reduction. -/
  planted : PlantedState Cand
  /-- Underlying state of the simulated external oracle. -/
  oracleState : State
  deriving DecidableEq, Repr

namespace PlantedOracleState

/-- Initial `PlantedOracleState` at target index `j`, fallback `defaultCand`, and oracle state
`s`. -/
@[expose] def init {Cand State : Type*} (j : ℕ) (defaultCand : Cand) (s : State) :
    PlantedOracleState Cand State :=
  ⟨PlantedState.init j defaultCand, s⟩

/-- Lawful lens focusing on the `planted` field of `PlantedOracleState`. -/
@[expose] def plantedLens {Cand State : Type*} :
    StateLens (PlantedOracleState Cand State) (PlantedState Cand) where
  get st := st.planted
  set st p := { st with planted := p }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lawful lens focusing on the `oracleState` field of `PlantedOracleState`. -/
@[expose] def oracleStateLens {Cand State : Type*} :
    StateLens (PlantedOracleState Cand State) State where
  get st := st.oracleState
  set st s := { st with oracleState := s }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

end PlantedOracleState

/-- Adaptive planted-query countdown handler on `PlantedOracleState Cand State`:
* once `st.planted.hasCaptured = true`, every query returns `dummyReply q` and leaves `st` frozen;
* while `st.planted.hasCaptured = false`:
  - on a target query (`isTarget q = true`), captures `extract q` with `dummyReply q` and freezes
    `st.oracleState` if `st.planted.rem == 0`, and otherwise steps `sim q` while decrementing
    `st.planted.rem`;
  - on a non-target query (`isTarget q = false`), steps `sim q` zoomed onto `oracleState` while
    leaving the countdown untouched. -/
@[expose] noncomputable def plantedHandler {Query Cand State : Type} {spec : Query → Type}
    (sim : (q : Query) → StateT State PMF (spec q))
    (isTarget : Query → Bool) (extract : Query → Cand) (defaultCand : Cand)
    (dummyReply : (q : Query) → spec q)
    (q : Query) : StateT (PlantedOracleState Cand State) PMF (spec q) :=
  fun st =>
    if st.planted.hasCaptured then
      PMF.pure (dummyReply q, st)
    else if isTarget q then
      if st.planted.rem == 0 then
        PMF.pure (dummyReply q, ⟨⟨0, true, extract q⟩, st.oracleState⟩)
      else
        (sim q st.oracleState).map fun x =>
          (x.1, ⟨⟨st.planted.rem - 1, false, defaultCand⟩, x.2⟩)
    else
      PlantedOracleState.oracleStateLens.zoom (sim q) st

/-- Once `st.planted.hasCaptured = true`, `plantedHandler` freezes the entire `PlantedOracleState`
across any subsequent `ProbOracleComp` execution, so any boolean state predicate `test` holding at
`st` holds at termination with probability `1`. -/
theorem runWith_plantedHandler_captured_bind_eq_one {Query Cand State α : Type}
    {spec : Query → Type}
    (sim : (q : Query) → StateT State PMF (spec q))
    (isTarget : Query → Bool) (extract : Query → Cand) (defaultCand : Cand)
    (dummyReply : (q : Query) → spec q)
    (test : PlantedOracleState Cand State → Bool)
    (program : ProbOracleComp spec α)
    {st : PlantedOracleState Cand State}
    (hcap : st.planted.hasCaptured = true) (htest : test st = true) :
    (runWith (plantedHandler sim isTarget extract defaultCand dummyReply) program st).bind
      (fun x => PMF.pure (test x.2)) true = 1 := by
  refine le_antisymm (PMF.coe_le_one _ _) (PMF.le_bind_apply_on_support _ fun x hx => ?_)
  have heq : x.2 = st := runWith_invariant
    (plantedHandler sim isTarget extract defaultCand dummyReply)
    (· = st)
    (fun q s hs a s' hs' => by
      subst hs
      simp only [plantedHandler, hcap, ↓reduceIte, PMF.mem_support_pure_iff] at hs'
      exact (Prod.mk.inj hs').2)
    program st rfl x.1 x.2 hx
  rw [heq, htest, PMF.pure_apply_self]

private theorem tsum_mul_le_sum_tsum_mul {β ι : Type*} (μ : β → ℝ≥0∞) (s : Finset ι)
    {bad : β → ℝ≥0∞} {win : ι → β → ℝ≥0∞} (h : ∀ a, bad a ≤ ∑ j ∈ s, win j a) :
    ∑' a, μ a * bad a ≤ ∑ j ∈ s, ∑' a, μ a * win j a := by
  calc ∑' a, μ a * bad a ≤ ∑' a, μ a * ∑ j ∈ s, win j a :=
        tsum_le_tsum fun a => mul_le_mul_of_nonneg_left (h a) zero_le
    _ = ∑ j ∈ s, ∑' a, μ a * win j a := by
        simp only [Finset.mul_sum]
        exact Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable

/-- **Cost-filtered adaptive planted-query union bound.** Suppose `program : ProbOracleComp spec α`
makes at most `Q` target queries (`isTarget q = true`), `badHandler` agrees with `sim` along
`embed : State → BadS` whenever `(isTarget q && isBad q s) = false`, and every bad target query
yields a winning extracted candidate (`win (extract q) s = true`). Then the probability that
`runWith badHandler program (embed s)` ends in `bad` is bounded by the sum over `j ∈ Finset.range Q`
of the probability that `plantedHandler` started at `PlantedOracleState.init j defaultCand s`
captures a winning candidate. -/
theorem toOuterMeasure_bad_le_sum_planted_of_cost
    {Query Cand State BadS α : Type} {spec : Query → Type}
    {badHandler : (q : Query) → StateT BadS PMF (spec q)} {bad : BadS → Prop}
    (embed : State → BadS) (hembed : ∀ s, ¬bad (embed s))
    (sim : (q : Query) → StateT State PMF (spec q))
    (isTarget : Query → Bool) (isBad : Query → State → Bool)
    (extract : Query → Cand) (defaultCand : Cand) (dummyReply : (q : Query) → spec q)
    (win : Cand → State → Bool)
    (hgood : ∀ q s, (isTarget q && isBad q s) = false →
      badHandler q (embed s) = (sim q s).map (fun x => (x.1, embed x.2)))
    (hwin : ∀ q s, isTarget q = true → isBad q s = true → win (extract q) s = true)
    {program : ProbOracleComp spec α} {Q : ℕ}
    (hq : OracleComp.IsCostBounded
      (Sum.elim (fun _ => 0) (fun q => if isTarget q then 1 else 0)) program Q)
    (s : State) :
    (runWith badHandler program (embed s)).toOuterMeasure {x | bad x.2} ≤
      ∑ j ∈ Finset.range Q,
        (runWith (plantedHandler sim isTarget extract defaultCand dummyReply)
            program (PlantedOracleState.init j defaultCand s)).bind
          (fun x => PMF.pure
            (x.2.planted.hasCaptured && win x.2.planted.candidate x.2.oracleState))
          true := by
  simp only [runWith_eq_run_interpret]
  induction hq generalizing s with
  | pure a Q =>
    have hnot : (a, embed s) ∉ {x : α × BadS | bad x.2} := hembed s
    simp only [OracleComp.run_interpret_pure, PMF.monad_pure_eq_pure,
      PMF.toOuterMeasure_pure_apply, ite_eq_right hnot, zero_le]
  | liftBind q cont Q _ ih =>
    cases q with
    | inl m =>
      simp only [Sum.elim_inl, Nat.add_zero, OracleComp.run_interpret_bind,
        OracleComp.run_interpret_query, OracleComp.sumHandler, StateT.lift,
        PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
        PMF.bind_bind, PMF.pure_bind, PMF.toOuterMeasure_bind_apply, PMF.bind_apply]
      exact (tsum_mul_le_sum_tsum_mul _ _ fun a => ih a s).trans_eq
        (Finset.sum_congr rfl fun j _ => by simp only [PMF.bind_apply])
    | inr q =>
      simp only [Sum.elim_inr, OracleComp.run_interpret_bind, OracleComp.run_interpret_query,
        OracleComp.sumHandler]
      cases ht : isTarget q
      · -- Passive (`isTarget q = false`) query: budget stays `Q` and `sim q` steps both sides.
        have hgd : (isTarget q && isBad q s) = false := by simp [ht]
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, hgood q s hgd,
          plantedHandler, PlantedOracleState.init, PlantedState.init, ht, StateLens.zoom,
          PlantedOracleState.oracleStateLens, PMF.monad_map_eq_map, PMF.monad_bind_eq_bind,
          PMF.bind_map, PMF.bind_bind, PMF.toOuterMeasure_bind_apply, PMF.bind_apply,
          Function.comp_def]
        exact tsum_mul_le_sum_tsum_mul _ _ fun x : spec q × State => ih x.1 x.2
      · -- Target (`isTarget q = true`) query: budget is `Q + 1`; index `0` captures `q`.
        simp only [↓reduceIte]
        rw [Finset.sum_range_succ']
        cases hb : isBad q s
        · -- Not bad: `badHandler` steps `sim q`, matching `j + 1` in `plantedHandler`.
          have hgd : (isTarget q && isBad q s) = false := by simp [ht, hb]
          simp only [hgood q s hgd, plantedHandler, PlantedOracleState.init,
            PlantedState.init, Bool.false_eq_true, ↓reduceIte, ht,
            beq_eq_false_iff_ne.mpr (Nat.add_one_ne_zero _), Nat.add_sub_cancel,
            PMF.monad_bind_eq_bind, PMF.bind_map, PMF.bind_bind,
            PMF.toOuterMeasure_bind_apply, PMF.bind_apply, Function.comp_def]
          exact (tsum_mul_le_sum_tsum_mul _ _ fun x : spec q × State => ih x.1 x.2).trans
            le_self_add
        · -- Bad target query: the `j = 0` term captures `extract q` and wins with probability `1`.
          refine (PMF.toOuterMeasure_le_one _ _).trans
            (le_trans (le_of_eq (Eq.symm ?_)) le_add_self)
          simp only [plantedHandler, PlantedOracleState.init, PlantedState.init,
            Bool.false_eq_true, ↓reduceIte, ht, beq_self_eq_true, PMF.monad_bind_eq_bind,
            PMF.pure_bind, ← runWith_eq_run_interpret]
          exact runWith_plantedHandler_captured_bind_eq_one sim isTarget extract defaultCand
            dummyReply
            (fun st => st.planted.hasCaptured && win st.planted.candidate st.oracleState)
            (cont (dummyReply q)) (st := ⟨⟨0, true, extract q⟩, s⟩) rfl (by simp [hwin q s ht hb])

/-- **Adaptive `Q`-query planted-index union bound (`IsQueryBounded`).** When `program` makes at
most `Q` external queries (`program.IsQueryBounded Q`), `badHandler` agrees with `sim` along `embed`
whenever `isBad q s = false`, and every bad query yields `win (extract q) s = true`, the probability
of reaching `bad` from `embed s` is at most the sum over `j ∈ Finset.range Q` of the probability
that the `j`-th planted execution captures a winning candidate. -/
theorem toOuterMeasure_bad_le_sum_planted
    {Query Cand State BadS α : Type} {spec : Query → Type}
    {badHandler : (q : Query) → StateT BadS PMF (spec q)} {bad : BadS → Prop}
    (embed : State → BadS) (hembed : ∀ s, ¬bad (embed s))
    (sim : (q : Query) → StateT State PMF (spec q))
    (isBad : Query → State → Bool)
    (extract : Query → Cand) (defaultCand : Cand) (dummyReply : (q : Query) → spec q)
    (win : Cand → State → Bool)
    (hgood : ∀ q s, isBad q s = false →
      badHandler q (embed s) = (sim q s).map (fun x => (x.1, embed x.2)))
    (hwin : ∀ q s, isBad q s = true → win (extract q) s = true)
    {program : ProbOracleComp spec α} {Q : ℕ}
    (hq : program.IsQueryBounded Q) (s : State) :
    (runWith badHandler program (embed s)).toOuterMeasure {x | bad x.2} ≤
      ∑ j ∈ Finset.range Q,
        (runWith (plantedHandler sim (fun _ => true) extract defaultCand dummyReply)
            program (PlantedOracleState.init j defaultCand s)).bind
          (fun x => PMF.pure
            (x.2.planted.hasCaptured && win x.2.planted.candidate x.2.oracleState))
          true :=
  toOuterMeasure_bad_le_sum_planted_of_cost embed hembed sim (fun _ => true) isBad extract
    defaultCand dummyReply win (fun q s h => hgood q s (by simpa using h))
    (fun q s _ h => hwin q s h) (by simpa using hq) s

/-- Variant of `toOuterMeasure_bad_le_sum_planted_of_cost` for reductions that output
`x.2.planted.candidate` unconditionally (returning `defaultCand` when fewer than `j + 1` target
queries occur), dropping `hasCaptured &&` in the winning event. -/
theorem toOuterMeasure_bad_le_sum_planted_candidate_of_cost
    {Query Cand State BadS α : Type} {spec : Query → Type}
    {badHandler : (q : Query) → StateT BadS PMF (spec q)} {bad : BadS → Prop}
    (embed : State → BadS) (hembed : ∀ s, ¬bad (embed s))
    (sim : (q : Query) → StateT State PMF (spec q))
    (isTarget : Query → Bool) (isBad : Query → State → Bool)
    (extract : Query → Cand) (defaultCand : Cand) (dummyReply : (q : Query) → spec q)
    (win : Cand → State → Bool)
    (hgood : ∀ q s, (isTarget q && isBad q s) = false →
      badHandler q (embed s) = (sim q s).map (fun x => (x.1, embed x.2)))
    (hwin : ∀ q s, isTarget q = true → isBad q s = true → win (extract q) s = true)
    {program : ProbOracleComp spec α} {Q : ℕ}
    (hq : OracleComp.IsCostBounded
      (Sum.elim (fun _ => 0) (fun q => if isTarget q then 1 else 0)) program Q)
    (s : State) :
    (runWith badHandler program (embed s)).toOuterMeasure {x | bad x.2} ≤
      ∑ j ∈ Finset.range Q,
        (runWith (plantedHandler sim isTarget extract defaultCand dummyReply)
            program (PlantedOracleState.init j defaultCand s)).bind
          (fun x => PMF.pure (win x.2.planted.candidate x.2.oracleState))
          true := by
  refine (toOuterMeasure_bad_le_sum_planted_of_cost embed hembed sim isTarget isBad extract
    defaultCand dummyReply win hgood hwin hq s).trans (Finset.sum_le_sum fun j _ => ?_)
  simp only [PMF.bind_apply]
  refine tsum_le_tsum fun x => mul_le_mul_of_nonneg_left ?_ zero_le
  cases x.2.planted.hasCaptured <;> simp

end Cslib.ProbOracleComp
