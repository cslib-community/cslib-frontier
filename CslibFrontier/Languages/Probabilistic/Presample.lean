/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Repeat
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm
import CslibFrontier.Tactic.PMFSwap

/-!
# Saved samples in adaptive oracle interactions

An external handler can consume one saved sample per call while the client continues drawing
independent private randomness. For a program making at most `n` external queries, `n`
independent samples drawn in advance give exactly the online joint law of the result and the
handler's state (`ProbOracleComp.IsQueryBounded.run_interpret_presample`). Unused samples are
discarded in this equality; they need not be independent of the final state or the client's
stopping time. The handler's fallback value is never used, so a run on a sufficient list of
samples is a function of those samples.

The general theorem `OracleComp.IsCostBounded.run_interpret_presample_when` also allows
uncharged calls to change state, as when a quantum device acts between classical signing calls.
A program without private coins is the special case
`OracleComp.IsQueryBounded.run_interpret_presample`, and closed `ProbComp` handlers the special
case `ProbOracleComp.IsQueryBounded.eval_presample`.

## Main definitions

* `Cslib.OracleComp.withSampleList`: supply a list's head to a handler and retain its tail.

## Main results

* `Cslib.ProbOracleComp.IsQueryBounded.run_interpret_presample`: presampling preserves the joint
  law of result and state.
* `Cslib.ProbOracleComp.IsQueryBounded.eval_presample`: the same for closed probabilistic handlers.
* `Cslib.OracleComp.IsQueryBounded.run_interpret_presample`: the same without private coins.

## References

Adapted from Languages/Probabilistic/Presample.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the typed sum of private and external calls.
-/

@[expose] public section

namespace Cslib

namespace OracleComp

universe u v w

/-- Supply the next saved sample to a stateful handler. The fallback makes short lists total;
the ordinary state and unused suffix are retained. -/
def withSampleList {Query : Type u} {spec : Query → Type v} {State Value : Type v}
    {m : Type v → Type w} [Functor m] (fallback : Value)
    (oracle : Value → (q : Query) → StateT State m (spec q))
    (q : Query) : StateT (State × List Value) m (spec q) := fun (state, values) =>
  (fun (answer, next) => (answer, next, values.tail)) <$> oracle (values.headD fallback) q state

/-- Consume a saved value on the selected calls. Other calls run the handler at its default
value and retain the whole tape, including when those calls modify the ordinary state. -/
noncomputable def withSampleListWhen {Query State Value : Type} {spec : Query → Type}
    (selected : Query → Bool) (fallback : Value)
    (oracle : Value → (q : Query) → StateT State PMF (spec q)) (q : Query) :
    StateT (State × List Value) PMF (spec q) :=
  if selected q then withSampleList fallback oracle q else fun (s, tape) =>
    (oracle fallback q s).map fun (reply, next) => (reply, next, tape)

/-- Two sufficiently long tapes give the same law of the result and retained state if
corresponding entries implement the same selected calls and the other calls agree. -/
theorem IsCostBounded.run_interpret_sampleListWhen_congr {Q S V W α : Type} {spec : Q → Type}
    {program : OracleComp spec α} {n : ℕ} (selected : Q → Bool)
    (h : IsCostBounded (fun q => (selected q).toNat) program n)
    (v₀ : V) (w₀ : W) (f : V → (q : Q) → StateT S PMF (spec q))
    (g : W → (q : Q) → StateT S PMF (spec q))
    (off : ∀ q, selected q = false → f v₀ q = g w₀ q)
    (vs : List V) (ws : List W) (len : n ≤ vs.length)
    (on : List.Forall₂ (fun v w => ∀ q, selected q = true → f v q = g w q) vs ws) (s : S) :
    ((OracleComp.interpret (withSampleListWhen selected v₀ f) program).run (s, vs)).map
      (fun (a, s', _) => (a, s')) =
    ((OracleComp.interpret (withSampleListWhen selected w₀ g) program).run (s, ws)).map
      (fun (a, s', _) => (a, s')) := by
  induction h generalizing vs ws s with
  | pure a n => simp only [interp_norm, pmf_norm]
  | liftBind q cont n _ ih =>
    cases hq : selected q with
    | false =>
      simp only [run_interpret_bind, run_interpret_query, withSampleListWhen, hq, ↓reduceIte,
        Bool.false_eq_true, Probability.PMF.monad_bind_eq_bind, PMF.map_bind, PMF.bind_map,
        Function.comp_def, off q hq]
      exact congrArg (fun k => (g w₀ q s).bind k)
        (funext fun v => ih v.1 vs ws (by simpa [hq] using len) on v.2)
    | true =>
      cases on with
      | nil => simp [hq] at len
      | cons equal tail =>
        simp only [run_interpret_bind, run_interpret_query, withSampleListWhen, hq, ↓reduceIte,
          withSampleList, List.headD_cons, List.tail_cons, Probability.PMF.monad_bind_eq_bind,
          PMF.monad_map_eq_map, PMF.map_bind, PMF.bind_map, Function.comp_def, equal q hq]
        exact congrArg (fun k => (g _ q s).bind k)
          (funext fun v => ih v.1 _ _ (by simpa [hq] using len) tail v.2)

/-- Presampling the selected calls of an adaptive program preserves the joint law of its
result and final state. An uncharged call can read or change that state arbitrarily. -/
theorem IsCostBounded.run_interpret_presample_when {Query State Value α : Type}
    {spec : Query → Type} {program : OracleComp spec α} {n : ℕ} (selected : Query → Bool)
    (h : IsCostBounded (fun q => (selected q).toNat) program n)
    (source : PMF Value) (fallback : Value)
    (oracle : Value → (q : Query) → StateT State PMF (spec q)) (s : State) :
    ((Probability.PMF.iid source n).map List.ofFn).bind (fun tape =>
      ((OracleComp.interpret (withSampleListWhen selected fallback oracle) program).run
        (s, tape)).map
        fun (result, next, _) => (result, next)) =
      (OracleComp.interpret (m := StateT State PMF) (fun q state =>
        if selected q then source.bind fun value => oracle value q state
        else oracle fallback q state) program).run s := by
  induction h generalizing s with
  | pure a n => simp only [interp_norm, pmf_norm, PMF.bind_const]
  | liftBind q cont n _ ih =>
    cases hq : selected q with
    | false =>
      simp only [run_interpret_bind, run_interpret_query, withSampleListWhen, hq, Bool.toNat_false,
        Nat.add_zero, Bool.false_eq_true, ↓reduceIte, Probability.PMF.monad_bind_eq_bind,
        PMF.map_bind, PMF.bind_map, Function.comp_def]
      pmf_swap with result
      rw [← ih result.1 result.2, PMF.bind_map]; rfl
    | true =>
      simp only [run_interpret_bind, run_interpret_query, withSampleListWhen, hq, Bool.toNat_true,
        ↓reduceIte, Probability.PMF.iid, withSampleList, Probability.PMF.monad_bind_eq_bind,
        PMF.monad_map_eq_map, PMF.map_bind, PMF.bind_bind, PMF.bind_map, PMF.map_comp,
        Function.comp_def, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.headD_cons,
        List.tail_cons]
      refine congrArg (source.bind ·) (funext fun value => ?_)
      pmf_swap with result
      rw [← ih result.1 result.2, PMF.bind_map]; rfl

end OracleComp

namespace ProbOracleComp

open OracleComp Probability

variable {Query α State Value : Type} {spec : Query → Type}

/-- **Presampling.** A program makes at most `n` external queries, and a handler draws one sample
from `source` per external query. Answering from `n` independent samples drawn in advance instead
gives the same joint law of the result and the handler's state. Private samples are drawn online
in both runs. The statement is exact and independent of the efficiency of the program, the
handler and the source. -/
theorem IsQueryBounded.run_interpret_presample {program : ProbOracleComp spec α} {n : ℕ}
    (h : program.IsQueryBounded n) (source : PMF Value) (fallback : Value)
    (oracle : Value → (q : Query) → StateT State PMF (spec q)) (s : State) :
    ((PMF.iid source n).map List.ofFn).bind (fun values =>
      ((interpret (sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (withSampleList fallback oracle)) program).run (s, values)).map
          fun (result, next, _) => (result, next)) =
      (interpret (sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (fun q state => source.bind fun value => oracle value q state)) program).run s := by
  let selected : ℕ ⊕ Query → Bool := Sum.elim (fun _ => false) (fun _ => true)
  let handler (v : Value) := sumHandler (m := StateT State PMF)
    (fun k => StateT.lift (ProbComp.unifOracle k)) (oracle v)
  have cost : (fun q => (selected q).toNat) = Sum.elim (fun _ => 0) (fun _ => 1) :=
    funext fun q => by cases q <;> rfl
  have saved : withSampleListWhen selected fallback handler =
      sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (withSampleList fallback oracle) := by
    funext q st
    rcases q with k | q
    · simp [withSampleListWhen, selected, handler, sumHandler, StateT.lift,
        PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind]
    · rfl
  have online : (fun q state => if selected q then source.bind fun v => handler v q state
      else handler fallback q state) = sumHandler (m := StateT State PMF)
        (fun k => StateT.lift (ProbComp.unifOracle k))
        (fun q state => source.bind fun v => oracle v q state) := by
    funext q state
    cases q <;> rfl
  simpa only [saved, online] using OracleComp.IsCostBounded.run_interpret_presample_when
    selected (cost ▸ h) source fallback handler s

/-- **Presampling with closed probabilistic handlers.** The `ProbComp` form of
`IsQueryBounded.run_interpret_presample`: `n` saved samples from `source` give the online joint law
of the result and the handler's state. -/
theorem IsQueryBounded.eval_presample {program : ProbOracleComp spec α} {count : ℕ}
    (h : program.IsQueryBounded count) (source : ProbComp Value) (fallback : Value)
    (oracle : Value → (q : Query) → StateT State ProbComp (spec q)) (s : State) :
    ProbComp.eval (do
      let values ← replicate count source
      (fun (result, next, _) => (result, next)) <$> (interpret
        (sumHandler (fun n => StateT.lift (ProbComp.unifFin n))
          (withSampleList fallback oracle)) program).run (s, values)) =
      ProbComp.eval ((interpret (sumHandler (fun n => StateT.lift (ProbComp.unifFin n))
        (fun q s => do
          let value ← source
          oracle value q s)) program).run s) := by
  have hstep (q : Query) (state : State × List Value) :
      ProbComp.eval (withSampleList fallback oracle q state) =
        withSampleList fallback (fun value q s => ProbComp.eval (oracle value q s)) q state := by
    simp [withSampleList, PMF.monad_map_eq_map]
  simpa only [ProbComp.eval_bind, ProbComp.eval_map, eval_run_interpret, hstep,
    ProbComp.eval_replicate_iid] using h.run_interpret_presample (ProbComp.eval source) fallback
      (fun value q s => ProbComp.eval (oracle value q s)) s

end ProbOracleComp

/-- **Presampling without private coins.** A program makes at most `n` calls, and a handler draws
one sample from `source` per call. Answering from `n` independent samples drawn in advance gives
the same joint law of the result and the handler's state. -/
theorem OracleComp.IsQueryBounded.run_interpret_presample {Query State Value γ : Type}
    {spec : Query → Type} {program : OracleComp spec γ} {n : ℕ} (h : program.IsQueryBounded n)
    (source : PMF Value) (fallback : Value)
    (oracle : Value → (q : Query) → StateT State PMF (spec q)) (s : State) :
    ((Probability.PMF.iid source n).map List.ofFn).bind (fun values =>
      ((interpret (withSampleList fallback oracle) program).run (s, values)).map
        fun (result, next, _) => (result, next)) =
      (interpret (m := StateT State PMF)
        (fun q state => source.bind fun value => oracle value q state) program).run s := by
  simpa only [interpret_interpret, ProbOracleComp.interpret_query] using
    h.probOracleComp.run_interpret_presample source fallback oracle s

end Cslib
