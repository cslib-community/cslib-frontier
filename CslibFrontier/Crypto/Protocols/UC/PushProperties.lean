/-
Copyright (c) 2026 Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.PushExecution
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
import CslibFrontier.Languages.Probabilistic.Iteration.Add
import CslibFrontier.Probability.PMF.Bind

/-!
# Fuel Monotonicity, Truncation Bounds, and Pull-to-Push Bridge for UC Execution

This module proves fuel-monotonicity, truncation-error, and halting-stability properties for the
single-token push runtime in `CslibFrontier/Crypto/Protocols/UC/PushExecution.lean`, together with
a 3-node pull-to-push execution bridge from `Cslib.Crypto.Protocols.UC.exec` to `PushSystem`
(call-bounded, fixed 3-node set, non-PPT scheduler step; `#6043` remains open).

## Main definitions

* `Cslib.Crypto.Protocols.UC.Push.UCMsg`: messages exchanged between environment, adversary, and
  corruption-routed protocol in the 3-node push embedding of `UC.exec`.
* `Cslib.Crypto.Protocols.UC.Push.ucPushSystem`: explicit 3-node `PushSystem` (`0` = environment,
  `1` = adversary, `2` = `corruptRouter C (π κ C)`) realizing sequential `UC.exec`.

## Main results

* `Cslib.Crypto.Protocols.UC.Push.eval_pushRun_some_mono`,
  `Cslib.Crypto.Protocols.UC.Push.support_pushRun_some_mono`,
  `Cslib.Crypto.Protocols.UC.Push.eval_pushRun_none_antitone`: fuel monotonicity of halted output
  probabilities and supports, and antitonicity of the timeout probability `none`.
* `Cslib.Crypto.Protocols.UC.Push.eval_pushRun_some_le_add_none`,
  `Cslib.Crypto.Protocols.UC.Push.abs_toReal_pushExec_sub_le`: two-fuel truncation error bound
  relating the `pushExec` difference to the earlier timeout probability `Pr[pushRun = none]`.
* `Cslib.Crypto.Protocols.UC.Push.eval_pushRun_eq_of_none_eq_zero`,
  `Cslib.Crypto.Protocols.UC.Push.eval_pushExec_eq_of_none_eq_zero`: halting stability once all
  reachable traces terminate within `fuel₀` steps.
* `Cslib.Crypto.Protocols.UC.Push.eval_pushRun_ucPushSystem`,
  `Cslib.Crypto.Protocols.UC.Push.eval_pushExec_ucPushSystem`,
  `Cslib.Crypto.Protocols.UC.Push.eval_pushExec_ucPushSystem_of_polyBounded`: exact output
  distribution equality between `ucPushSystem` and `UC.exec` when `fuel` exceeds the query bound.
-/

public section

namespace Cslib.Crypto.Protocols.UC.Push

open Cslib.Probability
open scoped ENNReal

/-! ### Fuel Monotonicity, Truncation Bounds, and Halting Stability -/

section FuelProperties

variable {m : ℕ} {Msg : Type}

private def jointRun (S : PushSystem m Msg) (κ : ℕ) (z : List Bool) (fuel : ℕ) :
    ProbComp (TokenState m Msg × (SSP.parFin (S.node κ)).State) :=
  Machine.closeProgram
    (ProbOracleComp.sample (SSP.parFin (S.node κ)).init >>= fun s =>
      (SSP.parFin (S.node κ)).runFrom
        (OracleComp.iterate fuel (step S) (TokenState.initialFor S.initial z)) s)

private theorem pushRun_eq_map_jointRun (S : PushSystem m Msg) (κ : ℕ) (z : List Bool)
    (fuel : ℕ) :
    pushRun S κ z fuel = (TokenState.output ∘ Prod.fst) <$> jointRun S κ z fuel := by
  simp only [pushRun, jointRun, Machine.run, Machine.link, Machine.closeProgram_bind,
    Machine.closeProgram_sample, Machine.closeProgram_map, map_bind, Functor.map_map,
    Function.comp_def]

private theorem jointRun_add (S : PushSystem m Msg) (κ : ℕ) (z : List Bool) (fuel k : ℕ) :
    jointRun S κ z (fuel + k) =
      jointRun S κ z fuel >>= fun x =>
        Machine.closeProgram
          ((SSP.parFin (S.node κ)).runFrom (OracleComp.iterate k (step S) x.1) x.2) := by
  simp only [jointRun, OracleComp.iterate_add, Machine.runFrom_bind, bind_assoc,
    Machine.closeProgram_bind]

private noncomputable def stepTail (S : PushSystem m Msg) (κ k : ℕ)
    (x : TokenState m Msg × (SSP.parFin (S.node κ)).State) : PMF (Option Bool) :=
  ((TokenState.output ∘ Prod.fst) <$>
    Machine.closeProgram
      ((SSP.parFin (S.node κ)).runFrom (OracleComp.iterate k (step S) x.1) x.2)).eval

private theorem eval_pushRun_add (S : PushSystem m Msg) (κ : ℕ) (z : List Bool) (fuel k : ℕ) :
    (pushRun S κ z (fuel + k)).eval =
      (jointRun S κ z fuel).eval.bind (stepTail S κ k) := by
  rw [pushRun_eq_map_jointRun, jointRun_add, ProbComp.eval_map, ProbComp.eval_bind,
    PMF.map_bind]
  refine congrArg _ (funext fun x => ?_)
  simp only [stepTail, ProbComp.eval_map]

private theorem stepTail_of_output_eq_some (S : PushSystem m Msg) (κ k : ℕ)
    (x : TokenState m Msg × (SSP.parFin (S.node κ)).State) {b : Bool}
    (hx : x.1.output = some b) :
    stepTail S κ k x = PMF.pure (some b) := by
  rw [stepTail, runFrom_iterate_step_of_output_isSome S κ k (by simp [hx])]
  simp only [Machine.closeProgram_pure, map_pure, Function.comp_apply, hx, ProbComp.eval_pure]

private theorem eval_pushRun_some_mono_add (S : PushSystem m Msg) (κ : ℕ) (z : List Bool)
    (fuel k : ℕ) (b : Bool) :
    (pushRun S κ z fuel).eval (some b) ≤ (pushRun S κ z (fuel + k)).eval (some b) := by
  rw [pushRun_eq_map_jointRun, ProbComp.eval_map, ← PMF.bind_pure_comp, eval_pushRun_add]
  refine PMF.bind_apply_mono_on_support _ (some b) fun x _ => ?_
  dsimp only [Function.comp_apply]
  cases h : x.1.output with
  | none =>
    simp only [PMF.pure_apply, reduceCtorEq, ↓reduceIte]
    exact zero_le
  | some b' => rw [stepTail_of_output_eq_some S κ k x h]

/-- Fuel monotonicity for `pushRun`: once the initial node can halt with `some b`, increasing the
step budget never decreases the probability of `some b`. -/
theorem eval_pushRun_some_mono (S : PushSystem m Msg) (κ : ℕ) (z : List Bool)
    {fuel₁ fuel₂ : ℕ} (h : fuel₁ ≤ fuel₂) (b : Bool) :
    (pushRun S κ z fuel₁).eval (some b) ≤ (pushRun S κ z fuel₂).eval (some b) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact eval_pushRun_some_mono_add S κ z fuel₁ k b

/-- Support monotonicity for `pushRun`: any concrete outcome `some b` in the support at `fuel₁`
remains in the support at every `fuel₂ ≥ fuel₁`. -/
theorem support_pushRun_some_mono (S : PushSystem m Msg) (κ : ℕ) (z : List Bool)
    {fuel₁ fuel₂ : ℕ} (h : fuel₁ ≤ fuel₂) {b : Bool}
    (hb : some b ∈ (pushRun S κ z fuel₁).eval.support) :
    some b ∈ (pushRun S κ z fuel₂).eval.support := by
  rw [PMF.mem_support_iff] at hb ⊢
  intro hzero
  apply hb
  exact le_antisymm ((eval_pushRun_some_mono S κ z h b).trans_eq hzero) zero_le

/-- Antitonicity of timeout probability: the probability that `pushRun` returns `none` never
increases when additional fuel is supplied. -/
theorem eval_pushRun_none_antitone (S : PushSystem m Msg) (κ : ℕ) (z : List Bool)
    {fuel₁ fuel₂ : ℕ} (h : fuel₁ ≤ fuel₂) :
    (pushRun S κ z fuel₂).eval none ≤ (pushRun S κ z fuel₁).eval none := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [eval_pushRun_add, pushRun_eq_map_jointRun, ProbComp.eval_map, ← PMF.bind_pure_comp]
  refine PMF.bind_apply_mono_on_support _ none fun x _ => ?_
  dsimp only [Function.comp_apply]
  cases hx : x.1.output with
  | none =>
    simp only [PMF.pure_apply, ↓reduceIte]
    exact PMF.coe_le_one _ _
  | some b' => rw [stepTail_of_output_eq_some S κ k x hx]

/-- Two-fuel upper bound on `some b`: extra fuel can shift at most the earlier timeout mass
`eval (pushRun S κ z fuel₁) none` into `some b`. -/
theorem eval_pushRun_some_le_add_none (S : PushSystem m Msg) (κ : ℕ) (z : List Bool)
    {fuel₁ fuel₂ : ℕ} (h : fuel₁ ≤ fuel₂) (b : Bool) :
    (pushRun S κ z fuel₂).eval (some b) ≤
      (pushRun S κ z fuel₁).eval (some b) + (pushRun S κ z fuel₁).eval none := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [eval_pushRun_add, pushRun_eq_map_jointRun, ProbComp.eval_map, PMF.bind_apply]
  have hpoint (x : TokenState m Msg × (SSP.parFin (S.node κ)).State) :
      (jointRun S κ z fuel₁).eval x * stepTail S κ k x (some b) ≤
        (if some b = (TokenState.output ∘ Prod.fst) x then (jointRun S κ z fuel₁).eval x else 0) +
          (if none = (TokenState.output ∘ Prod.fst) x
            then (jointRun S κ z fuel₁).eval x else 0) := by
    dsimp only [Function.comp_apply]
    by_cases hnone : x.1.output = none
    · simp only [hnone, reduceCtorEq, ↓reduceIte, zero_add]
      exact mul_le_of_le_one_right zero_le (PMF.coe_le_one _ _)
    · obtain ⟨b', hx⟩ := Option.ne_none_iff_exists'.mp hnone
      simp only [hx, stepTail_of_output_eq_some S κ k x hx]
      by_cases hb : b' = b
      · subst hb; simp [PMF.pure_apply]
      · simp [PMF.pure_apply, Ne.symm hb]
  calc ∑' x, (jointRun S κ z fuel₁).eval x * stepTail S κ k x (some b)
      ≤ ∑' x, ((if some b = (TokenState.output ∘ Prod.fst) x
            then (jointRun S κ z fuel₁).eval x else 0) +
          (if none = (TokenState.output ∘ Prod.fst) x
            then (jointRun S κ z fuel₁).eval x else 0)) :=
        tsum_le_tsum hpoint
    _ = (∑' x, if some b = (TokenState.output ∘ Prod.fst) x
            then (jointRun S κ z fuel₁).eval x else 0) +
          (∑' x, if none = (TokenState.output ∘ Prod.fst) x
            then (jointRun S κ z fuel₁).eval x else 0) :=
        Summable.tsum_add CompleteLattice.summable CompleteLattice.summable
    _ = ((jointRun S κ z fuel₁).eval.map (TokenState.output ∘ Prod.fst) (some b)) +
          ((jointRun S κ z fuel₁).eval.map (TokenState.output ∘ Prod.fst) none) := by
        rw [PMF.map_apply, PMF.map_apply]
        congr 1 <;> refine tsum_congr fun _ => by split_ifs <;> rfl

/-- `pushExec` outputs `true` exactly when `pushRun` outputs `some true`. -/
@[simp] theorem eval_pushExec_true_eq (S : PushSystem m Msg) (κ : ℕ) (z : List Bool) (fuel : ℕ) :
    (pushExec S κ z fuel).eval true = (pushRun S κ z fuel).eval (some true) := by
  rw [pushExec, ProbComp.eval_map, PMF.map_apply, tsum_eq_single (some true)]
  · simp
  · intro r hr
    cases r with
    | none => simp
    | some b => cases b <;> simp_all

/-- Two-fuel truncation error bound for `pushExec`: when `fuel₁ ≤ fuel₂`, the difference in
acceptance probability is at most the probability that `pushRun` has not halted at `fuel₁`
steps. (By `Game.coe_advantage`, the left-hand side equals `(Game.advantage _ _ : ℝ)`.) -/
theorem abs_toReal_pushExec_sub_le (S : PushSystem m Msg) (κ : ℕ) (z : List Bool)
    {fuel₁ fuel₂ : ℕ} (h : fuel₁ ≤ fuel₂) :
    |((pushExec S κ z fuel₁).eval true).toReal - ((pushExec S κ z fuel₂).eval true).toReal| ≤
      ((pushRun S κ z fuel₁).eval none).toReal := by
  have h1 : (pushExec S κ z fuel₁).eval true ≤
      (pushExec S κ z fuel₂).eval true + (pushRun S κ z fuel₁).eval none := by
    rw [eval_pushExec_true_eq, eval_pushExec_true_eq]
    exact (eval_pushRun_some_mono S κ z h true).trans le_self_add
  have h2 : (pushExec S κ z fuel₂).eval true ≤
      (pushExec S κ z fuel₁).eval true + (pushRun S κ z fuel₁).eval none := by
    rw [eval_pushExec_true_eq, eval_pushExec_true_eq]
    exact eval_pushRun_some_le_add_none S κ z h true
  have hadv := Game.advantage_le_of_apply_le (PMF.apply_ne_top _ none) h1 h2
  rwa [Game.coe_advantage, Game.coe_succProbability, Game.coe_succProbability] at hadv

/-- Halting stability for `pushRun`: if the timeout probability at `fuel₀` is zero, then the
entire output distribution is invariant for all `fuel ≥ fuel₀`. -/
theorem eval_pushRun_eq_of_none_eq_zero (S : PushSystem m Msg) (κ : ℕ) (z : List Bool)
    {fuel₀ fuel : ℕ} (hzero : (pushRun S κ z fuel₀).eval none = 0) (hle : fuel₀ ≤ fuel) :
    (pushRun S κ z fuel).eval = (pushRun S κ z fuel₀).eval := by
  ext r
  cases r with
  | none =>
    have hle0 : (pushRun S κ z fuel).eval none ≤ 0 :=
      (eval_pushRun_none_antitone S κ z hle).trans_eq hzero
    rw [hzero]
    exact le_antisymm hle0 bot_le
  | some b =>
    refine le_antisymm ?_ (eval_pushRun_some_mono S κ z hle b)
    simpa only [hzero, add_zero] using eval_pushRun_some_le_add_none S κ z hle b

/-- Halting stability for `pushExec`: if the timeout probability at `fuel₀` is zero, then the
output distribution of `pushExec` is invariant for all `fuel ≥ fuel₀`. -/
theorem eval_pushExec_eq_of_none_eq_zero (S : PushSystem m Msg) (κ : ℕ) (z : List Bool)
    {fuel₀ fuel : ℕ} (hzero : (pushRun S κ z fuel₀).eval none = 0) (hle : fuel₀ ≤ fuel) :
    (pushExec S κ z fuel).eval = (pushExec S κ z fuel₀).eval := by
  simp only [pushExec, ProbComp.eval_map, eval_pushRun_eq_of_none_eq_zero S κ z hzero hle]

end FuelProperties

/-! ### Pull-to-Push Bridge for `UC.exec` -/

section PullToPush

/-- Messages exchanged in the 3-node push simulation of `UC.exec`:
- `0` (environment `Z`) sends `partyQuery` to `2` (`corruptRouter C π`) and `advQuery` to `1`
  (`A`);
- `1` (adversary `A`) sends `netQuery` to `2` and `advReply` back to `0`;
- `2` (routed protocol `corruptRouter C π`) sends `partyReply` back to `0` and `netReply` back to
  `1`. -/
inductive UCMsg (n : ℕ) (In Out NetQ NetR AdvQ AdvR : Type) : Type
  | partyQuery (i : Fin n) (x : In)
  | partyReply (o : Option Out)
  | advQuery (q : AdvQ)
  | advReply (r : AdvR)
  | netQuery (q : RoutedNetQ n In NetQ)
  | netReply (r : RoutedNetR Out NetR)

private inductive CompStep {ι : Type} (spec : ι → Type) (α : Type) : Type
  | done (a : α)
  | wait (q : ι) (cont : spec q → ProbOracleComp spec α)

private def advance {ι : Type} {spec : ι → Type} {α : Type} :
    ProbOracleComp spec α → ProbOracleComp OracleSpec.empty (CompStep spec α)
  | .pure a => pure (.done a)
  | .liftBind (.inl k) cont => do
    let a ← ProbOracleComp.sample (ProbComp.unifFin k)
    advance (cont a)
  | .liftBind (.inr q) cont => pure (.wait q cont)

private theorem advance_pure {ι : Type} {spec : ι → Type} {α : Type} (a : α) :
    advance (spec := spec) (pure a) = pure (.done a) := rfl

private theorem advance_sample {ι : Type} {spec : ι → Type} {α : Type} (k : ℕ)
    (cont : Fin (k + 1) → ProbOracleComp spec α) :
    advance (PFunctor.FreeM.bind (OracleComp.query (Sum.inl k)) cont) =
      (ProbOracleComp.sample (ProbComp.unifFin k) >>= fun a => advance (cont a)) := rfl

private theorem advance_query {ι : Type} {spec : ι → Type} {α : Type} (q : ι)
    (cont : spec q → ProbOracleComp spec α) :
    advance (PFunctor.FreeM.bind (OracleComp.query (Sum.inr q)) cont) =
      pure (.wait q cont) := rfl

private abbrev EnvCont (n : ℕ) (In Out AdvQ AdvR : Type) : Type :=
  (q : (Fin n × In) ⊕ AdvQ) ×
    (execSpec n In Out AdvQ AdvR q → ProbOracleComp (execSpec n In Out AdvQ AdvR) Bool)

private abbrev AdvCont (n : ℕ) (In Out NetQ NetR AdvR StateA : Type) : Type :=
  RoutedNetR Out NetR →
    ProbOracleComp (netSpec (RoutedNetQ n In NetQ) (RoutedNetR Out NetR)) (AdvR × StateA)

private inductive AdvState (n : ℕ) (In Out NetQ NetR AdvR StateA : Type) : Type
  | idle (sA : StateA)
  | waiting (cont : AdvCont n In Out NetQ NetR AdvR StateA)

private def envAction {n : ℕ} {In Out NetQ NetR AdvQ AdvR : Type} :
    CompStep (execSpec n In Out AdvQ AdvR) Bool →
      Outcome 3 (UCMsg n In Out NetQ NetR AdvQ AdvR) ×
        Option (EnvCont n In Out AdvQ AdvR)
  | .done b => (.halt b, none)
  | .wait (.inl (i, x)) cont =>
    (.write 2 .input (.partyQuery i x), some ⟨.inl (i, x), cont⟩)
  | .wait (.inr q) cont =>
    (.write 1 .backdoor (.advQuery q), some ⟨.inr q, cont⟩)

private def advAction {n : ℕ} {In Out NetQ NetR AdvQ AdvR StateA : Type} :
    CompStep (netSpec (RoutedNetQ n In NetQ) (RoutedNetR Out NetR)) (AdvR × StateA) →
      Outcome 3 (UCMsg n In Out NetQ NetR AdvQ AdvR) ×
        AdvState n In Out NetQ NetR AdvR StateA
  | .done (r, sA') => (.write 0 .subroutineOutput (.advReply r), .idle sA')
  | .wait rq cont => (.write 2 .backdoor (.netQuery rq), .waiting cont)

private def envNode {n : ℕ} {In Out NetQ NetR AdvQ AdvR : Type}
    (Z : Environment n In Out AdvQ AdvR) (κ : ℕ) :
    ReactiveNode 3 (UCMsg n In Out NetQ NetR AdvQ AdvR) where
  State := Option (EnvCont n In Out AdvQ AdvR)
  init := pure none
  handle d state := match d, state with
    | .start z, _ => envAction <$> advance (Z κ z)
    | .deliver e, some ⟨.inl _, cont⟩ =>
      match e.payload with
      | .partyReply o => envAction <$> advance (cont o)
      | _ => pure (.yield, state)
    | .deliver e, some ⟨.inr _, cont⟩ =>
      match e.payload with
      | .advReply r => envAction <$> advance (cont r)
      | _ => pure (.yield, state)
    | _, _ => pure (.halt false, state)

private def advNode {n : ℕ} {In Out NetQ NetR AdvQ AdvR : Type}
    (A : ExecAdversary n In Out NetQ NetR AdvQ AdvR) (κ : ℕ) (C : Finset (Fin n)) :
    ReactiveNode 3 (UCMsg n In Out NetQ NetR AdvQ AdvR) where
  State := AdvState n In Out NetQ NetR AdvR (A κ C).State
  init := AdvState.idle <$> (A κ C).init
  handle d state := match d, state with
    | .deliver e, .idle sA =>
      match e.payload with
      | .advQuery q => advAction <$> advance (((A κ C).handle q).run sA)
      | _ => pure (.yield, state)
    | .deliver e, .waiting cont =>
      match e.payload with
      | .netReply rr => advAction <$> advance (cont rr)
      | _ => pure (.yield, state)
    | _, _ => pure (.yield, state)

private def protoNode {n : ℕ} {In Out NetQ NetR AdvQ AdvR : Type}
    (π : Protocol n In Out NetQ NetR) (κ : ℕ) (C : Finset (Fin n)) :
    ReactiveNode 3 (UCMsg n In Out NetQ NetR AdvQ AdvR) where
  State := (π κ C).State
  init := (π κ C).init
  handle d sP := match d with
    | .deliver e =>
      match e.payload with
      | .partyQuery i x => do
        let (o, sP') ← ((corruptRouter C (π κ C)).handle (.inl (i, x))).run sP
        return (.write 0 .subroutineOutput (.partyReply o), sP')
      | .netQuery rq => do
        let (rr, sP') ← ((corruptRouter C (π κ C)).handle (.inr rq)).run sP
        return (.write 1 .backdoor (.netReply rr), sP')
      | _ => pure (.yield, sP)
    | _ => pure (.yield, sP)

/-- Library construction (no cited definition): explicit 3-node `PushSystem` embedding a
sequential `UC.exec` execution (`0` = environment `Z`, `1` = adversary `A`, `2` = routed protocol
`corruptRouter C (π κ C)`), with all writes allowed. Call-bounded, fixed 3-node set, non-PPT
scheduler step (`#6043` remains open). -/
def ucPushSystem {n : ℕ} {In Out NetQ NetR AdvQ AdvR : Type}
    (π : Protocol n In Out NetQ NetR) (A : ExecAdversary n In Out NetQ NetR AdvQ AdvR)
    (C : Finset (Fin n)) (Z : Environment n In Out AdvQ AdvR) :
    PushSystem 3 (UCMsg n In Out NetQ NetR AdvQ AdvR) where
  node κ
    | 0 => envNode Z κ
    | 1 => advNode A κ C
    | 2 => protoNode π κ C
  initial := 0
  control := fun _ _ => true

section BridgeProof

variable {n : ℕ} {In Out NetQ NetR AdvQ AdvR : Type}
  (π : Protocol n In Out NetQ NetR) (A : ExecAdversary n In Out NetQ NetR AdvQ AdvR)
  (C : Finset (Fin n)) (Z : Environment n In Out AdvQ AdvR) (κ : ℕ)

private def ucState3 (s₀ : Option (EnvCont n In Out AdvQ AdvR))
    (s₁ : AdvState n In Out NetQ NetR AdvR (A κ C).State) (s₂ : (π κ C).State) :
    (SSP.parFin ((ucPushSystem π A C Z).node κ)).State
  | 0 => s₀
  | 1 => s₁
  | 2 => s₂

private theorem ucState3_2 (s₀ : Option (EnvCont n In Out AdvQ AdvR))
    (s₁ : AdvState n In Out NetQ NetR AdvR (A κ C).State) (s₂ : (π κ C).State) :
    ucState3 π A C Z κ s₀ s₁ s₂ 2 = s₂ := rfl

private theorem update_ucState3_0 (s₀ s₀' : Option (EnvCont n In Out AdvQ AdvR))
    (s₁ : AdvState n In Out NetQ NetR AdvR (A κ C).State) (s₂ : (π κ C).State) :
    (Function.update (ucState3 π A C Z κ s₀ s₁ s₂) 0 s₀' :
      (SSP.parFin ((ucPushSystem π A C Z).node κ)).State) =
      ucState3 π A C Z κ s₀' s₁ s₂ := by
  funext j; fin_cases j <;> rfl

private theorem update_ucState3_1 (s₀ : Option (EnvCont n In Out AdvQ AdvR))
    (s₁ s₁' : AdvState n In Out NetQ NetR AdvR (A κ C).State) (s₂ : (π κ C).State) :
    (Function.update (ucState3 π A C Z κ s₀ s₁ s₂) 1 s₁' :
      (SSP.parFin ((ucPushSystem π A C Z).node κ)).State) =
      ucState3 π A C Z κ s₀ s₁' s₂ := by
  funext j; fin_cases j <;> rfl

private theorem update_ucState3_2 (s₀ : Option (EnvCont n In Out AdvQ AdvR))
    (s₁ : AdvState n In Out NetQ NetR AdvR (A κ C).State) (s₂ s₂' : (π κ C).State) :
    (Function.update (ucState3 π A C Z κ s₀ s₁ s₂) 2 s₂' :
      (SSP.parFin ((ucPushSystem π A C Z).node κ)).State) =
      ucState3 π A C Z κ s₀ s₁ s₂' := by
  funext j; fin_cases j <;> rfl

private theorem ucPushSystem_control (l : List (Envelope 3 (UCMsg n In Out NetQ NetR AdvQ AdvR)))
    (e : Envelope 3 (UCMsg n In Out NetQ NetR AdvQ AdvR)) :
    (ucPushSystem π A C Z).control l e = true := rfl

private theorem ucPushSystem_initial :
    (ucPushSystem π A C Z).initial = 0 := rfl

private theorem ucPushSystem_node_2 :
    (ucPushSystem π A C Z).node κ 2 = protoNode π κ C := rfl

private def runEnvStep (f : ℕ)
    (ts : TokenState 3 (UCMsg n In Out NetQ NetR AdvQ AdvR))
    (s : (SSP.parFin ((ucPushSystem π A C Z).node κ)).State)
    (prog : ProbOracleComp (execSpec n In Out AdvQ AdvR) Bool) :
    ProbOracleComp OracleSpec.empty (Option Bool) :=
  (TokenState.output ∘ Prod.fst) <$>
    ((envAction <$> advance prog) >>= fun x =>
      (SSP.parFin ((ucPushSystem π A C Z).node κ)).runFrom
        (OracleComp.iterate f (step (ucPushSystem π A C Z)) (ts.next (ucPushSystem π A C Z) x.1))
        (Function.update s 0 x.2))

private def runAdvStep (f : ℕ)
    (ts : TokenState 3 (UCMsg n In Out NetQ NetR AdvQ AdvR))
    (s : (SSP.parFin ((ucPushSystem π A C Z).node κ)).State)
    (sub : ProbOracleComp (netSpec (RoutedNetQ n In NetQ) (RoutedNetR Out NetR))
      (AdvR × (A κ C).State)) :
    ProbOracleComp OracleSpec.empty (Option Bool) :=
  (TokenState.output ∘ Prod.fst) <$>
    ((advAction <$> advance sub) >>= fun x =>
      (SSP.parFin ((ucPushSystem π A C Z).node κ)).runFrom
        (OracleComp.iterate f (step (ucPushSystem π A C Z)) (ts.next (ucPushSystem π A C Z) x.1))
        (Function.update s 1 x.2))

private theorem runEnvStep_sample (f : ℕ)
    (ts : TokenState 3 (UCMsg n In Out NetQ NetR AdvQ AdvR))
    (s : (SSP.parFin ((ucPushSystem π A C Z).node κ)).State) (k : ℕ)
    (cont : Fin (k + 1) → ProbOracleComp (execSpec n In Out AdvQ AdvR) Bool) :
    runEnvStep π A C Z κ f ts s (PFunctor.FreeM.bind (OracleComp.query (Sum.inl k)) cont) =
      ProbOracleComp.sample (ProbComp.unifFin k) >>= fun a =>
        runEnvStep π A C Z κ f ts s (cont a) := by
  simp only [runEnvStep, map_bind]
  rfl

private theorem runAdvStep_sample (f : ℕ)
    (ts : TokenState 3 (UCMsg n In Out NetQ NetR AdvQ AdvR))
    (s : (SSP.parFin ((ucPushSystem π A C Z).node κ)).State) (k : ℕ)
    (cont : Fin (k + 1) →
      ProbOracleComp (netSpec (RoutedNetQ n In NetQ) (RoutedNetR Out NetR))
        (AdvR × (A κ C).State)) :
    runAdvStep π A C Z κ f ts s (PFunctor.FreeM.bind (OracleComp.query (Sum.inl k)) cont) =
      ProbOracleComp.sample (ProbComp.unifFin k) >>= fun a =>
        runAdvStep π A C Z κ f ts s (cont a) := by
  simp only [runAdvStep, map_bind]
  rfl

private theorem execMachine_runFrom_pure (b : Bool) (sA : (A κ C).State) (sP : (π κ C).State) :
    (some ∘ Prod.fst) <$>
        ((execMachine π A κ C).runFrom (pure b : ProbOracleComp (execSpec n In Out AdvQ AdvR) Bool)
          (sA, sP)) =
      pure (some b) := rfl

private theorem execMachine_runFrom_sample (k : ℕ)
    (cont : Fin (k + 1) → ProbOracleComp (execSpec n In Out AdvQ AdvR) Bool)
    (sA : (A κ C).State) (sP : (π κ C).State) :
    (some ∘ Prod.fst) <$>
        ((execMachine π A κ C).runFrom
          (PFunctor.FreeM.bind (OracleComp.query (Sum.inl k)) cont) (sA, sP)) =
      ProbOracleComp.sample (ProbComp.unifFin k) >>= fun a =>
        (some ∘ Prod.fst) <$> ((execMachine π A κ C).runFrom (cont a) (sA, sP)) := by
  rw [PFunctor.FreeM.bind_eq_bind]
  erw [Machine.runFrom_bind]
  have hq : (execMachine π A κ C).runFrom
      (OracleComp.query (spec := probOracleSpec (execSpec n In Out AdvQ AdvR)) (Sum.inl k))
      (sA, sP) =
      (fun a => (a, (sA, sP))) <$> ProbOracleComp.sample (ProbComp.unifFin k) :=
    (execMachine π A κ C).runFrom_sample (ProbComp.unifFin k) (sA, sP)
  rw [hq]
  erw [bind_map_left, map_bind]
  rfl

private theorem execMachine_runFrom_party (i : Fin n) (x : In)
    (cont : Option Out → ProbOracleComp (execSpec n In Out AdvQ AdvR) Bool)
    (sA : (A κ C).State) (sP : (π κ C).State) :
    (some ∘ Prod.fst) <$>
        ((execMachine π A κ C).runFrom
          (PFunctor.FreeM.bind (OracleComp.query (Sum.inr (Sum.inl (i, x)))) cont) (sA, sP)) =
      ((corruptRouter C (π κ C)).handle (Sum.inl (i, x))).run sP >>= fun y =>
        (some ∘ Prod.fst) <$> ((execMachine π A κ C).runFrom (cont y.1) (sA, y.2)) := by
  rw [PFunctor.FreeM.bind_eq_bind]
  erw [Machine.runFrom_bind,
    show OracleComp.query (spec := probOracleSpec (execSpec n In Out AdvQ AdvR))
      (Sum.inr (Sum.inl (i, x))) = ProbOracleComp.query (Sum.inl (i, x)) from rfl,
    Machine.runFrom_query]
  change (some ∘ Prod.fst) <$>
      ((Equiv.prodAssoc _ _ _ <$>
        (corruptRouter C (π κ C)).runFrom
          ((Machine.liftRight (partySpec n In Out) (A κ C)).handle (Sum.inl (i, x)) sA) sP) >>=
        fun z => (execMachine π A κ C).runFrom (cont z.1) z.2) = _
  simp only [Machine.liftRight, StateT.lift, StateT.run, bind_pure_comp]
  erw [Machine.runFrom_map,
    show ProbOracleComp.query (Sum.inl (i, x)) =
      OracleComp.query (Sum.inr (Sum.inl (i, x))) from rfl,
    Machine.runFrom_query]
  simp only [bind_map_left, map_bind]
  rfl

private theorem execMachine_runFrom_adv_split (q : AdvQ)
    (cont : AdvR → ProbOracleComp (execSpec n In Out AdvQ AdvR) Bool)
    (sA : (A κ C).State) (sP : (π κ C).State) :
    (some ∘ Prod.fst) <$>
        ((execMachine π A κ C).runFrom
          (PFunctor.FreeM.bind (OracleComp.query (Sum.inr (Sum.inr q))) cont) (sA, sP)) =
      (corruptRouter C (π κ C)).runFrom
          (Machine.liftRightProgram (partySpec n In Out) (((A κ C).handle q).run sA)) sP >>=
        fun z => (some ∘ Prod.fst) <$>
          ((execMachine π A κ C).runFrom (cont z.1.1) (z.1.2, z.2)) := by
  rw [PFunctor.FreeM.bind_eq_bind]
  erw [Machine.runFrom_bind,
    show OracleComp.query (spec := probOracleSpec (execSpec n In Out AdvQ AdvR))
      (Sum.inr (Sum.inr q)) = ProbOracleComp.query (Sum.inr q) from rfl,
    Machine.runFrom_query]
  change (some ∘ Prod.fst) <$>
      ((Equiv.prodAssoc _ _ _ <$>
        (corruptRouter C (π κ C)).runFrom
          (Machine.liftRightProgram (partySpec n In Out) (((A κ C).handle q).run sA)) sP) >>=
        fun z => (execMachine π A κ C).runFrom (cont z.1) z.2) = _
  simp only [map_bind, bind_map_left]
  rfl

private theorem corruptRouter_runFrom_liftRight_sample (k : ℕ)
    (cont : Fin (k + 1) →
      ProbOracleComp (netSpec (RoutedNetQ n In NetQ) (RoutedNetR Out NetR))
        (AdvR × (A κ C).State))
    (sP : (π κ C).State) :
    (corruptRouter C (π κ C)).runFrom
        (Machine.liftRightProgram (partySpec n In Out)
          (PFunctor.FreeM.bind (OracleComp.query (Sum.inl k)) cont)) sP =
      ProbOracleComp.sample (ProbComp.unifFin k) >>= fun a =>
        (corruptRouter C (π κ C)).runFrom
          (Machine.liftRightProgram (partySpec n In Out) (cont a)) sP := by
  rw [PFunctor.FreeM.bind_eq_bind, Machine.liftRightProgram_bind,
    show Machine.liftRightProgram (partySpec n In Out)
      (OracleComp.query (spec := probOracleSpec _) (Sum.inl k)) =
      ProbOracleComp.sample (ProbComp.unifFin k) from rfl]
  erw [Machine.runFrom_bind, Machine.runFrom_sample, bind_map_left]

private theorem corruptRouter_runFrom_liftRight_query (rq : RoutedNetQ n In NetQ)
    (cont : RoutedNetR Out NetR →
      ProbOracleComp (netSpec (RoutedNetQ n In NetQ) (RoutedNetR Out NetR))
        (AdvR × (A κ C).State))
    (sP : (π κ C).State) :
    (corruptRouter C (π κ C)).runFrom
        (Machine.liftRightProgram (partySpec n In Out)
          (PFunctor.FreeM.bind (OracleComp.query (Sum.inr rq)) cont)) sP =
      ((corruptRouter C (π κ C)).handle (Sum.inr rq)).run sP >>= fun y =>
        (corruptRouter C (π κ C)).runFrom
          (Machine.liftRightProgram (partySpec n In Out) (cont y.1)) y.2 := by
  rw [PFunctor.FreeM.bind_eq_bind, Machine.liftRightProgram_bind,
    show Machine.liftRightProgram (partySpec n In Out)
      (OracleComp.query (spec := probOracleSpec _) (Sum.inr rq)) =
      ProbOracleComp.query (Sum.inr rq) from rfl]
  erw [Machine.runFrom_bind, Machine.runFrom_query]

private theorem runAdvStep_eq_runFrom
    (sub : ProbOracleComp (netSpec (RoutedNetQ n In NetQ) (RoutedNetR Out NetR))
      (AdvR × (A κ C).State))
    {bA bZ_rem tA : ℕ} (hsub : ProbOracleComp.IsQueryBounded sub bA)
    (cont : AdvR → ProbOracleComp (execSpec n In Out AdvQ AdvR) Bool)
    (houter : ∀ (r : AdvR) (f : ℕ) (ts : TokenState 3 (UCMsg n In Out NetQ NetR AdvQ AdvR))
      (s₀ : Option (EnvCont n In Out AdvQ AdvR)) (sA : (A κ C).State) (sP : (π κ C).State),
      ts.target = 0 → ts.output = none → ts.halted = ∅ → 2 * bZ_rem * (tA + 1) ≤ f →
      runEnvStep π A C Z κ f ts (ucState3 π A C Z κ s₀ (.idle sA) sP) (cont r) =
        (some ∘ Prod.fst) <$> ((execMachine π A κ C).runFrom (cont r) (sA, sP)))
    {q : AdvQ} {f : ℕ} {ts : TokenState 3 (UCMsg n In Out NetQ NetR AdvQ AdvR)}
    {s₁ : AdvState n In Out NetQ NetR AdvR (A κ C).State} {sP : (π κ C).State}
    (htarg : ts.target = 1) (ho : ts.output = none) (hh : ts.halted = ∅)
    (hf : 2 * bA + 1 + 2 * bZ_rem * (tA + 1) ≤ f) :
    runAdvStep π A C Z κ f ts (ucState3 π A C Z κ (some ⟨.inr q, cont⟩) s₁ sP) sub =
      (some ∘ Prod.fst) <$>
        ((corruptRouter C (π κ C)).runFrom
            (Machine.liftRightProgram (partySpec n In Out) sub) sP >>= fun z =>
          (execMachine π A κ C).runFrom (cont z.1.1) (z.1.2, z.2)) := by
  induction sub using OracleComp.induction generalizing bA f ts s₁ sP with
  | pure res =>
    rcases res with ⟨r, sA'⟩
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rw [runAdvStep, advance_pure, map_pure, pure_bind]
    simp only [advAction, TokenState.next_write_of_control_eq_true _ _ _ _ _
      (ucPushSystem_control π A C Z _ _), update_ucState3_1]
    conv_lhs =>
      rw [runFrom_iterate_step_succ_of_not_mem_halted (ucPushSystem π A C Z) κ f'
        (by dsimp; exact ho) (by simp [hh])]
    trans runEnvStep π A C Z κ f' { ts with
      target := 0
      delivery := .deliver ⟨ts.target, 0, .subroutineOutput, .advReply r⟩
      log := ts.log ++ [⟨ts.target, 0, .subroutineOutput, .advReply r⟩] }
      (ucState3 π A C Z κ (some ⟨.inr q, cont⟩) (.idle sA') sP) (cont r)
    · rfl
    · rw [houter r f' { ts with
        target := 0
        delivery := .deliver ⟨ts.target, 0, .subroutineOutput, .advReply r⟩
        log := ts.log ++ [⟨ts.target, 0, .subroutineOutput, .advReply r⟩] }
        (some ⟨.inr q, cont⟩) sA' sP rfl ho hh (by omega)]
      rfl
  | query_bind u kA ih =>
    rcases u with k | rq
    · have hkA : ∀ a, ProbOracleComp.IsQueryBounded (kA a) bA :=
        (OracleComp.IsCostBounded.liftBind_iff.mp hsub).2
      rw [runAdvStep_sample]
      erw [corruptRouter_runFrom_liftRight_sample]
      rw [bind_assoc, map_bind]
      exact bind_congr fun a => ih a (hkA a) htarg ho hh hf
    · obtain ⟨hle, hkA⟩ := OracleComp.IsCostBounded.liftBind_iff.mp hsub
      simp only [Sum.elim_inr] at hle hkA
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by omega⟩
      rw [runAdvStep, advance_query, map_pure, pure_bind]
      simp only [advAction, TokenState.next_write_of_control_eq_true _ _ _ _ _
        (ucPushSystem_control π A C Z _ _), update_ucState3_1]
      conv_lhs =>
        erw [runFrom_iterate_step_succ_of_not_mem_halted (ucPushSystem π A C Z) κ (f' + 1)
          (by dsimp; exact ho) (by simp [hh])]
      dsimp only
      simp only [ucPushSystem_node_2, protoNode, StateT.run, ucState3_2, bind_assoc, pure_bind,
        update_ucState3_2,
        TokenState.next_write_of_control_eq_true _ _ _ _ _ (ucPushSystem_control π A C Z _ _)]
      erw [corruptRouter_runFrom_liftRight_query]
      simp only [bind_assoc, map_bind]
      conv_lhs =>
        erw [show (corruptRouter C (π κ C)).handle (Sum.inr rq) sP =
          ((corruptRouter C (π κ C)).handle (Sum.inr rq)).run sP from rfl]
      refine bind_congr fun y => ?_
      conv_lhs =>
        rw [runFrom_iterate_step_succ_of_not_mem_halted (ucPushSystem π A C Z) κ f'
          (by dsimp; exact ho) (by simp [hh])]
      trans runAdvStep π A C Z κ f' {
        target := 1
        delivery := .deliver ⟨2, 1, .backdoor, .netReply y.1⟩
        log := ts.log ++ [⟨ts.target, 2, .backdoor, .netQuery rq⟩] ++
          [⟨2, 1, .backdoor, .netReply y.1⟩]
        halted := ts.halted
        output := ts.output }
        (ucState3 π A C Z κ (some ⟨.inr q, cont⟩) (.waiting kA) y.2) (kA y.1)
      · conv_rhs => rw [runAdvStep]
        rfl
      · rw [← map_bind]
        refine ih y.1 (bA := bA - 1) (hkA y.1) (f := f') ?_ ?_ ?_ ?_
        · rfl
        · exact ho
        · exact hh
        · omega

private theorem runEnvStep_eq_runFrom
    (prog : ProbOracleComp (execSpec n In Out AdvQ AdvR) Bool)
    {bZ tA : ℕ} (hprog : ProbOracleComp.IsQueryBounded prog bZ)
    (hA : (A κ C).IsBounded tA)
    {f : ℕ} {ts : TokenState 3 (UCMsg n In Out NetQ NetR AdvQ AdvR)}
    {s₀ : Option (EnvCont n In Out AdvQ AdvR)} {sA : (A κ C).State} {sP : (π κ C).State}
    (htarg : ts.target = 0) (ho : ts.output = none) (hh : ts.halted = ∅)
    (hf : 2 * bZ * (tA + 1) ≤ f) :
    runEnvStep π A C Z κ f ts (ucState3 π A C Z κ s₀ (.idle sA) sP) prog =
      (some ∘ Prod.fst) <$> ((execMachine π A κ C).runFrom prog (sA, sP)) := by
  induction prog using OracleComp.induction generalizing bZ f ts s₀ sA sP with
  | pure b =>
    rw [runEnvStep, advance_pure, map_pure, pure_bind]
    simp only [envAction, TokenState.next_halt_of_target_eq _ _ _
      (htarg.trans (ucPushSystem_initial π A C Z).symm), update_ucState3_0]
    conv_lhs =>
      rw [runFrom_iterate_step_of_output_isSome (ucPushSystem π A C Z) κ f (by simp)]
    simp only [map_pure, Function.comp_apply]
    rfl
  | query_bind u cont ih =>
    rcases u with k | q
    · have hcont : ∀ a, ProbOracleComp.IsQueryBounded (cont a) bZ :=
        (OracleComp.IsCostBounded.liftBind_iff.mp hprog).2
      rw [runEnvStep_sample]
      erw [execMachine_runFrom_sample]
      exact bind_congr fun a => ih a (hcont a) htarg ho hh hf
    · obtain ⟨hle, hcont⟩ := OracleComp.IsCostBounded.liftBind_iff.mp hprog
      simp only [Sum.elim_inr] at hle hcont
      rcases q with ⟨i, x⟩ | q
      · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := by
          have hb : 1 ≤ bZ := hle
          have h2 : 2 ≤ 2 * bZ * (tA + 1) := by nlinarith
          exact ⟨f - 2, by omega⟩
        rw [runEnvStep, advance_query, map_pure, pure_bind]
        simp only [envAction, TokenState.next_write_of_control_eq_true _ _ _ _ _
          (ucPushSystem_control π A C Z _ _), update_ucState3_0]
        conv_lhs =>
          erw [runFrom_iterate_step_succ_of_not_mem_halted (ucPushSystem π A C Z) κ (f' + 1)
            (by dsimp; exact ho) (by simp [hh])]
        dsimp only
        simp only [ucPushSystem_node_2, protoNode, StateT.run, ucState3_2, bind_assoc, pure_bind,
          update_ucState3_2,
          TokenState.next_write_of_control_eq_true _ _ _ _ _ (ucPushSystem_control π A C Z _ _)]
        erw [execMachine_runFrom_party]
        rw [map_bind]
        conv_lhs =>
          erw [show (corruptRouter C (π κ C)).handle (Sum.inl (i, x)) sP =
            ((corruptRouter C (π κ C)).handle (Sum.inl (i, x))).run sP from rfl]
        refine bind_congr fun y => ?_
        conv_lhs =>
          rw [runFrom_iterate_step_succ_of_not_mem_halted (ucPushSystem π A C Z) κ f'
            (by dsimp; exact ho) (by simp [hh])]
        exact ih y.1 (hcont y.1) rfl ho hh (by
          have : 2 * (bZ - 1) * (tA + 1) + 2 ≤ 2 * bZ * (tA + 1) := by
            obtain ⟨b', rfl⟩ : ∃ b', bZ = b' + 1 := ⟨bZ - 1, by omega⟩
            have hmul : 2 * b' * (tA + 1) + 2 * (tA + 1) = 2 * (b' + 1) * (tA + 1) := by ring
            simp only [Nat.add_sub_cancel] at *
            omega
          omega)
      · have hsubB : ProbOracleComp.IsQueryBounded (((A κ C).handle q).run sA) tA :=
          (hA.2 q sA).of_le fun q' => by cases q' <;> simp
        obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := by
          have hb : 1 ≤ bZ := hle
          have h1 : 1 ≤ 2 * bZ * (tA + 1) := by nlinarith
          exact ⟨f - 1, by omega⟩
        rw [runEnvStep, advance_query, map_pure, pure_bind]
        simp only [envAction, TokenState.next_write_of_control_eq_true _ _ _ _ _
          (ucPushSystem_control π A C Z _ _), update_ucState3_0]
        conv_lhs =>
          rw [runFrom_iterate_step_succ_of_not_mem_halted (ucPushSystem π A C Z) κ f'
            (by dsimp; exact ho) (by simp [hh])]
        erw [execMachine_runFrom_adv_split]
        rw [map_bind]
        trans runAdvStep π A C Z κ f' { ts with
          target := 1
          delivery := .deliver ⟨ts.target, 1, .backdoor, .advQuery q⟩
          log := ts.log ++ [⟨ts.target, 1, .backdoor, .advQuery q⟩] }
          (ucState3 π A C Z κ (some ⟨.inr q, cont⟩) (.idle sA) sP) (((A κ C).handle q).run sA)
        · rw [runAdvStep, map_bind]
          rfl
        · rw [← map_bind]
          refine runAdvStep_eq_runFrom π A C Z κ (((A κ C).handle q).run sA) (bZ_rem := bZ - 1)
            hsubB cont
            (fun r f'' ts'' s₀'' sA'' sP'' ht' ho' hh' hf'' =>
              ih r (hcont r) ht' ho' hh' hf'')
            (q := q) (f := f') (s₁ := .idle sA) (sP := sP) ?_ ?_ ?_ ?_
          · rfl
          · exact ho
          · exact hh
          obtain ⟨b', rfl⟩ : ∃ b', bZ = b' + 1 := ⟨bZ - 1, by omega⟩
          have hmul : 2 * b' * (tA + 1) + 2 * (tA + 1) = 2 * (b' + 1) * (tA + 1) := by ring
          simp only [Nat.add_sub_cancel]
          omega

private theorem runFrom_ucPushSystem_eq_runFrom
    (z : List Bool) {bZ tA fuel : ℕ}
    (hZ : ProbOracleComp.IsQueryBounded (Z κ z) bZ)
    (hA : (A κ C).IsBounded tA) (hfuel : 2 * bZ * (tA + 1) + 1 ≤ fuel)
    (sA : (A κ C).State) (sP : (π κ C).State) :
    (TokenState.output ∘ Prod.fst) <$>
        ((SSP.parFin ((ucPushSystem π A C Z).node κ)).runFrom
          (OracleComp.iterate fuel (step (ucPushSystem π A C Z))
            (TokenState.initialFor (ucPushSystem π A C Z).initial z))
          (ucState3 π A C Z κ none (.idle sA) sP)) =
      (some ∘ Prod.fst) <$> ((execMachine π A κ C).runFrom (Z κ z) (sA, sP)) := by
  obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by omega⟩
  rw [runFrom_iterate_step_succ_of_not_mem_halted (ucPushSystem π A C Z) κ f' rfl
    (by simp [TokenState.initialFor])]
  exact runEnvStep_eq_runFrom π A C Z κ (Z κ z) (bZ := bZ) (tA := tA) hZ hA
    (ucPushSystem_initial π A C Z) rfl rfl (by omega)

private theorem eval_pi3 {α : Fin 3 → Type} (p : (j : Fin 3) → ProbComp (α j)) :
    ProbComp.eval (OracleComp.pi p) =
      (p 0).eval.bind fun x₀ => (p 1).eval.bind fun x₁ => (p 2).eval.map fun x₂ =>
        Fin.cons x₀ (Fin.cons x₁ (Fin.cons x₂ (fun (i : Fin 0) => i.elim0))) := by
  rw [OracleComp.pi_succ]
  simp only [ProbComp.eval_bind, ProbComp.eval_map]
  refine congrArg ((p 0).eval.bind) (funext fun x₀ => ?_)
  rw [OracleComp.pi_succ]
  simp only [ProbComp.eval_bind, ProbComp.eval_map, PMF.map_bind]
  refine congrArg ((p 1).eval.bind) (funext fun x₁ => ?_)
  rw [OracleComp.pi_succ, OracleComp.pi_zero]
  simp only [ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, PMF.map_bind,
    PMF.map_comp]
  change (p 2).eval.bind (fun a => (PMF.pure fun i : Fin 0 => i.elim0).bind
      (PMF.pure ∘ (Fin.cons x₀ ∘ Fin.cons x₁ ∘ Fin.cons a))) =
    (p 2).eval.bind (fun x₂ => PMF.pure (Fin.cons x₀ (Fin.cons x₁ (Fin.cons x₂ fun i => i.elim0))))
  simp only [PMF.pure_bind]
  rfl

end BridgeProof

/-- Pull-to-push bridge for `pushRun`: when `Z κ z` makes at most `bZ` external queries,
each activation of `A κ C` makes at most `tA` calls, and `fuel ≥ 2 * bZ * (tA + 1) + 1`, the
3-node push execution `ucPushSystem` has the exact same output distribution as `UC.exec`
(wrapped in `some`). Call-bounded, fixed 3-node set, non-PPT scheduler step (`#6043` remains
open). -/
theorem eval_pushRun_ucPushSystem {n : ℕ} {In Out NetQ NetR AdvQ AdvR : Type}
    (π : Protocol n In Out NetQ NetR) (A : ExecAdversary n In Out NetQ NetR AdvQ AdvR)
    (C : Finset (Fin n)) (Z : Environment n In Out AdvQ AdvR)
    (κ : ℕ) (z : List Bool) {bZ tA fuel : ℕ}
    (hZ : ProbOracleComp.IsQueryBounded (Z κ z) bZ)
    (hA : (A κ C).IsBounded tA) (hfuel : 2 * bZ * (tA + 1) + 1 ≤ fuel) :
    (pushRun (ucPushSystem π A C Z) κ z fuel).eval =
      (exec π A C Z κ z).eval.map some := by
  rw [eval_pushRun]
  have hinit : ((SSP.parFin ((ucPushSystem π A C Z).node κ)).init).eval =
      ((A κ C).init.eval).bind fun sA =>
        ((π κ C).init.eval).map fun sP => ucState3 π A C Z κ none (.idle sA) sP := by
    change ProbComp.eval
        (OracleComp.pi fun j : Fin 3 => ((ucPushSystem π A C Z).node κ j).init) = _
    rw [eval_pi3]
    erw [PMF.pure_bind]
    simp only [ucPushSystem, advNode, protoNode, ProbComp.eval_map, PMF.bind_map]
    refine congrArg ((A κ C).init.eval.bind) (funext fun sA => ?_)
    refine congrArg ((π κ C).init.eval.map) (funext fun sP => ?_)
    funext j
    fin_cases j <;> rfl
  rw [hinit, PMF.bind_bind]
  have hcomm : (exec π A C Z κ z).eval =
      ((A κ C).init.eval).bind fun sA =>
        ((π κ C).init.eval).bind fun sP =>
          (Prod.fst <$> Machine.closeProgram
            ((execMachine π A κ C).runFrom (Z κ z) (sA, sP))).eval := by
    have hinit_exec : (execMachine π A κ C).init.eval =
        ((A κ C).init.eval).bind fun sA =>
          ((π κ C).init.eval).map fun sP => (sA, sP) := by
      change (do let sP ← (π κ C).init; let sA ← (A κ C).init; return (sA, sP)).eval = _
      simp only [ProbComp.eval_bind, ProbComp.eval_pure]
      rw [PMF.bind_comm]
      rfl
    change (Machine.closeProgram
        (ProbOracleComp.sample (execMachine π A κ C).init >>= fun x =>
          Prod.fst <$> (execMachine π A κ C).runFrom (Z κ z) x)).eval = _
    simp only [Machine.closeProgram_bind, Machine.closeProgram_sample, ProbComp.eval_bind]
    erw [hinit_exec, PMF.bind_bind]
    refine congrArg ((A κ C).init.eval.bind) (funext fun sA => ?_)
    erw [PMF.bind_map]
    simp only [Machine.closeProgram_map]
    rfl
  rw [hcomm, PMF.map_bind]
  refine congrArg ((A κ C).init.eval.bind) (funext fun sA => ?_)
  rw [PMF.bind_map, PMF.map_bind]
  refine congrArg ((π κ C).init.eval.bind) (funext fun sP => ?_)
  have hrun := congrArg (fun p => (Machine.closeProgram p).eval)
    (runFrom_ucPushSystem_eq_runFrom π A C Z κ z hZ hA hfuel sA sP)
  simpa only [Machine.closeProgram_map, ProbComp.eval_map, PMF.map_comp, Function.comp_def] using
    hrun

/-- Pull-to-push bridge for `pushExec`: under the same query bounds and fuel threshold
`2 * bZ * (tA + 1) + 1 ≤ fuel`, `pushExec (ucPushSystem π A C Z)` has the exact same Boolean
output distribution as `UC.exec`. -/
theorem eval_pushExec_ucPushSystem {n : ℕ} {In Out NetQ NetR AdvQ AdvR : Type}
    (π : Protocol n In Out NetQ NetR) (A : ExecAdversary n In Out NetQ NetR AdvQ AdvR)
    (C : Finset (Fin n)) (Z : Environment n In Out AdvQ AdvR)
    (κ : ℕ) (z : List Bool) {bZ tA fuel : ℕ}
    (hZ : ProbOracleComp.IsQueryBounded (Z κ z) bZ)
    (hA : (A κ C).IsBounded tA) (hfuel : 2 * bZ * (tA + 1) + 1 ≤ fuel) :
    (pushExec (ucPushSystem π A C Z) κ z fuel).eval = (exec π A C Z κ z).eval := by
  rw [pushExec, ProbComp.eval_map, eval_pushRun_ucPushSystem π A C Z κ z hZ hA hfuel, PMF.map_comp]
  exact PMF.map_id _

/-- Pull-to-push bridge specialized to `Environment.PolyBounded` and `Adversary.PolyBounded`:
for any `fuel ≥ 2 * (pZ.eval κ) * (pA.eval κ + 1) + 1`, `pushExec (ucPushSystem π A C Z)`
matches `UC.exec`. -/
theorem eval_pushExec_ucPushSystem_of_polyBounded {n : ℕ} {In Out NetQ NetR AdvQ AdvR : Type}
    (π : Protocol n In Out NetQ NetR) (A : ExecAdversary n In Out NetQ NetR AdvQ AdvR)
    (C : Finset (Fin n)) (Z : Environment n In Out AdvQ AdvR)
    {pZ pA : Polynomial ℕ} (hZ : Z.PolyBounded pZ) (hA : A.PolyBounded pA)
    (κ : ℕ) (z : List Bool) {fuel : ℕ}
    (hfuel : 2 * pZ.eval κ * (pA.eval κ + 1) + 1 ≤ fuel) :
    (pushExec (ucPushSystem π A C Z) κ z fuel).eval = (exec π A C Z κ z).eval :=
  eval_pushExec_ucPushSystem π A C Z κ z
    ((hZ κ z).of_le fun q => by cases q <;> simp) (hA κ C) hfuel

end PullToPush

end Cslib.Crypto.Protocols.UC.Push
