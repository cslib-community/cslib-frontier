/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Languages.Probabilistic.Oracle.Run
import CslibFrontier.Languages.Probabilistic.Oracle.QueryBoundedSimulation
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import CslibFrontier.Languages.Probabilistic.QueryCount.Congr
import CslibFrontier.Languages.Probabilistic.Simulation
import CslibFrontier.Languages.Probabilistic.Sum.Lift
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation

/-!
# Stateful oracle substitution with bounded state growth

Library infrastructure (no cited result): extends
`Cslib.Probability.IsOraclePPTOn.run_interpret_preprocess_open_of_polyBounded` to handlers whose
reply length may depend on the current encoded state as well as the caller and request, requiring
only that each call adds at most an encoded-state increment polynomially bounded in the caller and
request alone.

Because `IsOraclePPTOn` on the outer program gives one polynomial `Q` bounding both the number of
external queries and the length of every external request (`IsOraclePPTOn.query_bounds`), the
handler's encoded state stays bounded by `|initial| + k * G` after `k ≤ Q` calls. Combined with
`IsOraclePPTOn.length_le`, `ProbOracleComp.mem_support_iff_exists`, and `finite_operations` on
the handler certificate, every supported reply along a real execution stays polynomially bounded in
the caller's input. Adding an explicit call counter and capping both the call count and the request
length at `Q` reduces the certificate to
`IsOraclePPTOn.run_interpret_preprocess_open_of_polyBounded`, while query-bounded simulation shows
that the cap never triggers along executions of the program.

Specializations cover closed `ProbComp` handlers, handlers whose encoded state is uniformly bounded
in the caller (`of_state_le`, requiring no invariant or support case split), memoryless
`ProbOracleComp.run` oracles (including the empty-reply oracle), and parameterized `IsOraclePPT`
programs.

## Main results

* `Cslib.Probability.IsOraclePPTOn.run_interpret_preprocess_open_of_bounded_growth`,
  `Cslib.Probability.IsOraclePPTOn.run_interpret_preprocess_of_bounded_growth`: open and closed
  stateful substitution under polynomially bounded additive state growth, without a user-supplied
  reply-length bound.
* `Cslib.Probability.IsOraclePPTOn.run_interpret_preprocess_open_of_state_le`,
  `Cslib.Probability.IsOraclePPTOn.run_interpret_preprocess_of_state_le`: open and closed stateful
  substitution when all encoded states are bounded by a polynomial in the caller.
* `Cslib.Probability.IsOraclePPTOn.isPPTOn_run`,
  `Cslib.Probability.IsOraclePPTOn.isPPTOn_runEmptyOracle`: running an oracle-PPT program against an
  efficient memoryless `ProbComp` oracle (or the empty-reply oracle).
* `Cslib.Probability.IsOraclePPT.run_interpret_preprocess_open_of_bounded_growth`,
  `Cslib.Probability.IsOraclePPT.run_interpret_preprocess_of_bounded_growth`,
  `Cslib.Probability.IsOraclePPT.run_interpret_preprocess_open_of_state_le`,
  `Cslib.Probability.IsOraclePPT.run_interpret_preprocess_of_state_le`,
  `Cslib.Probability.IsOraclePPT.isPPTOn_run`: parameterized counterparts for `IsOraclePPT`.
-/

public section

namespace Cslib.Probability

open Turing.MultiTapeTM

section Helpers

variable {Operation External Caller State : Type}

/-- Counter- and request-capped wrapper around a stateful handler: while fewer than `cap a`
calls have occurred and the request fits in `cap a` bits, forward to `handler` and increment the
call counter; otherwise return the empty word and leave `(state, count)` unchanged. -/
private noncomputable def cappedHandler
    (handler : Caller → Operation × List Bool → State →
      WordOracleComp External (List Bool × State))
    (cap : Caller → ℕ) (a : Caller) (request : Operation × List Bool) (sk : State × ℕ) :
    WordOracleComp External (List Bool × (State × ℕ)) :=
  if sk.2 < cap a ∧ request.2.length ≤ cap a then
    (fun result => (result.1, (result.2, sk.2 + 1))) <$> handler a request sk.1
  else
    pure ([], sk)

/-- Counter-only capped wrapper around a stateful handler, agreeing with `cappedHandler` on all
requests whose payload has length at most `cap a`. -/
private noncomputable def budgetHandler
    (handler : Caller → Operation × List Bool → State →
      WordOracleComp External (List Bool × State))
    (cap : Caller → ℕ) (a : Caller) (request : Operation × List Bool) (sk : State × ℕ) :
    WordOracleComp External (List Bool × (State × ℕ)) :=
  if sk.2 < cap a then
    (fun result => (result.1, (result.2, sk.2 + 1))) <$> handler a request sk.1
  else
    pure ([], sk)

private theorem cappedHandler_eq_budgetHandler
    (handler : Caller → Operation × List Bool → State →
      WordOracleComp External (List Bool × State))
    (cap : Caller → ℕ) (a : Caller) {request : Operation × List Bool}
    (hreq : request.2.length ≤ cap a) :
    cappedHandler handler cap a request = budgetHandler handler cap a request := by
  funext ⟨state, k⟩
  simp only [cappedHandler, budgetHandler, hreq, and_true]

/-- Certify `cappedHandler` from a certificate of `handler` and a polynomial-time cap `cap`. -/
private theorem isOraclePPTOn_cappedHandler [DecidableEq External]
    {input : Caller ↪ List Bool} {operationEncoding : Operation ↪ List Bool}
    {stateEncoding : State ↪ List Bool}
    {handler : Caller → Operation × List Bool → State →
      WordOracleComp External (List Bool × State)}
    {cap : Caller → ℕ}
    (hhandler : IsOraclePPTOn (encHandlerCall input operationEncoding stateEncoding)
      (encPair encBits stateEncoding)
      (fun ⟨caller, request, state⟩ => handler caller request state))
    (hcap : ComputableInPolyTime cap input encUnary) :
    IsOraclePPTOn (encHandlerCall input operationEncoding (encPair stateEncoding encUnary))
      (encPair encBits (encPair stateEncoding encUnary))
      (fun ⟨caller, request, sk⟩ => cappedHandler handler cap caller request sk) := by
  have : Finite External := hhandler.finite_operations
  let EIn := encHandlerCall input operationEncoding (encPair stateEncoding encUnary)
  let EOut := encPair encBits (encPair stateEncoding encUnary)
  refine IsOraclePPTOn.ite
    (by dsimp only [EIn, encHandlerCall]; fun_prop)
    ((hhandler.preprocess (input := EIn)
      (prepare := fun p : Caller × (Operation × List Bool) × (State × ℕ) =>
        (p.1, p.2.1, p.2.2.1))
      (by dsimp only [EIn, encHandlerCall]; fun_prop)).map_with
      (f := fun p result => (result.1, (result.2, p.2.2.2 + 1)))
      (by dsimp only [EIn, EOut, encHandlerCall]; fun_prop))
    ((show ComputableInPolyTime (fun p : Caller × (Operation × List Bool) × (State × ℕ) =>
        ([], p.2.2)) EIn EOut by dsimp only [EIn, EOut, encHandlerCall]; fun_prop).isOraclePPTOn)

/-- Along every run of a program whose external queries are bounded in count and length by `cap`,
the capped handler with counter has the same joint law (with the counter forgotten) as the
uncapped handler. -/
private theorem runWith_cappedHandler_eq {β : Type}
    {handler : Caller → Operation × List Bool → State →
      WordOracleComp External (List Bool × State)}
    {cap : Caller → ℕ} (a : Caller)
    {program : WordOracleComp Operation β}
    (hq : program.IsQueryBounded (cap a))
    (hsat : program.QueriesSatisfy fun request => request.2.length ≤ cap a)
    {init : State} {ExtState : Type}
    (oracle : External × List Bool → StateT ExtState PMF (List Bool)) (ext : ExtState) :
    ProbOracleComp.runWith oracle
      ((fun ⟨res, sk⟩ => (res, sk.1)) <$>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
            (cappedHandler handler cap a))
          program).run (init, 0)) ext =
      ProbOracleComp.runWith oracle
        ((OracleComp.interpret
          (OracleComp.sumHandler
            (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
            (handler a))
          program).run init) ext := by
  have hinterp :
      OracleComp.interpret
        (OracleComp.sumHandler
          (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
          (cappedHandler handler cap a)) program =
        OracleComp.interpret
          (OracleComp.sumHandler
            (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
            (budgetHandler handler cap a)) program := by
    exact OracleComp.QueriesSatisfy.interpret_congr hsat fun
      | .inl _, _ => rfl
      | .inr _, hq => cappedHandler_eq_budgetHandler handler cap a hq
  rw [ProbOracleComp.runWith_map, hinterp, ProbOracleComp.runWith_run_interpret,
    ProbOracleComp.runWith_run_interpret, ProbOracleComp.runWith_eq_run_interpret,
    ProbOracleComp.runWith_eq_run_interpret]
  let h₁ : Operation × List Bool → StateT ((State × ℕ) × ExtState) PMF (List Bool) :=
    fun q st => (ProbOracleComp.runWith oracle (budgetHandler handler cap a q st.1) st.2).map
      fun ⟨⟨r, sk'⟩, ext'⟩ => (r, (sk', ext'))
  let h₂ : Unit → Operation × List Bool → StateT (State × ExtState) PMF (List Bool) :=
    fun _ q st => (ProbOracleComp.runWith oracle (handler a q st.1) st.2).map
      fun ⟨⟨r, s'⟩, ext'⟩ => (r, (s', ext'))
  let rep : (State × ℕ) × ExtState → State × ExtState := fun st => (st.1.1, st.2)
  let inv : ℕ → (State × ℕ) × ExtState → Prop := fun rem st => st.1.2 + rem ≤ cap a
  have hsim := (ProbOracleComp.IsQueryBounded.run_interpret_bind_comm_of_invariant
    h₁ h₂ (fun _ => PMF.pure ()) rep inv (fun r st h => by dsimp [inv] at h ⊢; omega)
    (fun rem q st hinv => by
      obtain ⟨⟨s, k⟩, ext'⟩ := st
      have hk : k < cap a := by dsimp [inv] at hinv; omega
      have hbud : budgetHandler handler cap a q (s, k) =
          (fun result => (result.1, (result.2, k + 1))) <$> handler a q s := by
        simp [budgetHandler, hk]
      refine ⟨?_, fun ans st' hmem => ?_⟩
      · simp only [h₁, h₂, hbud, ProbOracleComp.runWith_map, PMF.map_comp, PMF.pure_bind,
          PMF.bind_map, PMF.pure_map, Prod.map, Function.comp_def, rep]
        exact PMF.bind_pure_comp _ _
      · simp only [h₁, hbud, ProbOracleComp.runWith_map, PMF.map_comp, Function.comp_def,
          Prod.map, PMF.mem_support_map_iff] at hmem
        obtain ⟨⟨⟨r, s''⟩, ext''⟩, -, heq⟩ := hmem
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        dsimp only [inv] at hinv ⊢
        omega)
    hq (s := ((init, 0), ext)) (by dsimp [inv]; omega)).1
  simp only [PMF.pure_bind, rep] at hsim
  have hmap := congrArg (PMF.map fun ⟨_, res, s', ext'⟩ => ((res, s'), ext')) hsim
  simp only [PMF.map_bind, PMF.pure_map, PMF.map_comp, Function.comp_def, h₁, h₂] at hmap
  have hcomp : (fun x : β × (State × ℕ) × ExtState => PMF.pure ((x.1, x.2.1.1), x.2.2)) =
      PMF.pure ∘ fun x : β × (State × ℕ) × ExtState => ((x.1, x.2.1.1), x.2.2) := rfl
  rw [hcomp, PMF.bind_pure_comp] at hmap
  simp only [PMF.map_comp, Function.comp_def, Prod.map, id_eq]
  exact hmap

end Helpers

/-- Library infrastructure (no cited result): open stateful substitution when each call adds encoded
state polynomially bounded in the caller and request alone. Because the outer program's query
bound caps both the number of calls and every request length, the handler's encoded state stays
polynomially bounded in the caller's input along every execution, and `IsOraclePPTOn.length_le`
together with `ProbOracleComp.mem_support_iff_exists` gives a uniform polynomial bound on all
replies, reducing the certificate to
`Cslib.Probability.IsOraclePPTOn.run_interpret_preprocess_open_of_polyBounded`. -/
theorem IsOraclePPTOn.run_interpret_preprocess_open_of_bounded_growth
    {Operation External α β Caller State : Type} [DecidableEq Operation] [DecidableEq External]
    {source : α ↪ List Bool} {input : Caller ↪ List Bool} {output : β ↪ List Bool}
    {operationEncoding : Operation ↪ List Bool} {stateEncoding : State ↪ List Bool}
    {program : α → WordOracleComp Operation β}
    {handler : Caller → Operation × List Bool → State →
      WordOracleComp External (List Bool × State)}
    {prepare : Caller → α} {initial : Caller → State}
    {growth : Caller → List Bool → ℕ}
    (hprogram : IsOraclePPTOn source output program)
    (hprepare : ComputableInPolyTime prepare input source)
    (hhandler : IsOraclePPTOn (encHandlerCall input operationEncoding stateEncoding)
      (encPair encBits stateEncoding)
      (fun ⟨caller, request, state⟩ => handler caller request state))
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (invariant : Caller → State → Prop) (hinit : ∀ a, invariant a (initial a))
    (hgrowth : PolyBounded (fun pair : Caller × List Bool => (encPair input encBits pair).length)
      (fun ⟨a, w⟩ => growth a w))
    (hpreserve : ∀ a request state, invariant a state →
      ∀ result ∈ OracleComp.support (handler a request state),
        invariant a result.2 ∧
        (stateEncoding result.2).length ≤ (stateEncoding state).length + growth a request.2) :
    IsOraclePPTOn input (encPair output stateEncoding) (fun a =>
      (OracleComp.interpret
        (OracleComp.sumHandler
          (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n))) (handler a))
        (program (prepare a))).run (initial a)) := by
  obtain ⟨qC, qD, hqb⟩ := hprogram.query_bounds
  let Q (a : Caller) : ℕ := qC * ((source (prepare a)).length + 1) ^ qD
  have hword : ComputableInPolyTime (fun a => source (prepare a)) input encBits :=
    hprepare.of_enc_eq (fun _ => rfl)
  have hQ : ComputableInPolyTime Q input encUnary := by
    dsimp only [Q]
    fun_prop
  obtain ⟨gC, gD, hg_bound⟩ := hgrowth.exists_le
  let G (a : Caller) : ℕ := gC * (2 * (input a).length + Q a + 2) ^ gD
  have hG_le (a : Caller) {w : List Bool} (hw : w.length ≤ Q a) : growth a w ≤ G a := by
    refine (hg_bound (a, w)).trans (Nat.mul_le_mul_left gC (Nat.pow_le_pow_left ?_ gD))
    simp only [length_encPair, encBits_apply]
    omega
  have : Finite Operation := hprogram.finite_operations
  let _ : Fintype Operation := Fintype.ofFinite Operation
  let opMax : ℕ := Finset.univ.sup fun op : Operation => (operationEncoding op).length
  have hopMax (op : Operation) : (operationEncoding op).length ≤ opMax :=
    Finset.le_sup (f := fun op : Operation => (operationEncoding op).length) (Finset.mem_univ op)
  obtain ⟨rC, rD, hr_bound⟩ := hhandler.length_le
  let maxState (a : Caller) : ℕ := (stateEncoding (initial a)).length + Q a * G a
  let R (a : Caller) : ℕ :=
    rC * (2 * (input a).length + 4 * opMax + 2 * Q a + maxState a + 9) ^ rD
  let resources' (a : Caller) (_ : List Bool) : ℕ := R a + (2 * G a + 1)
  have hres'_poly : PolyBounded (fun pair : Caller × List Bool =>
      (encPair input encBits pair).length) (fun pair => resources' pair.1 pair.2) := by
    growth_poly
  let inv' (a : Caller) (sk : State × ℕ) : Prop :=
    invariant a sk.1 ∧ sk.2 ≤ Q a ∧
      (stateEncoding sk.1).length ≤ (stateEncoding (initial a)).length + sk.2 * G a
  have hcapped := isOraclePPTOn_cappedHandler hhandler hQ
  have hsub := hprogram.run_interpret_preprocess_open_of_polyBounded hprepare hcapped
    (hinitial.prod (.const 0)) inv'
    (fun a => ⟨hinit a, Nat.zero_le _, by simp⟩)
    hres'_poly
    (fun a request ⟨s, k⟩ ⟨hinv, hkQ, hlen⟩ result hresult => by
      by_cases hguard : k < Q a ∧ request.2.length ≤ Q a
      · rw [cappedHandler, ite_eq_left hguard, OracleComp.mem_supportWith_map_iff] at hresult
        obtain ⟨res, hres, rfl⟩ := hresult
        obtain ⟨hinv', hgro⟩ := hpreserve a request s hinv res hres
        have hG := hG_le a hguard.2
        have hstepLen : (stateEncoding res.2).length ≤
            (stateEncoding (initial a)).length + (k + 1) * G a := by
          simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using
            (hgro.trans (Nat.add_le_add_left hG _)).trans (Nat.add_le_add_right hlen _)
        have hsBound : (stateEncoding s).length ≤ maxState a :=
          hlen.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hkQ) _)
        obtain ⟨ExtState, oracle, ext, ext', hmem⟩ := ProbOracleComp.mem_support_iff_exists.mp hres
        rw [← ProbOracleComp.runWith_eq_run_interpret] at hmem
        have hresLen := hr_bound (a, request, s) ExtState oracle ext ext' res hmem
        have hop := hopMax request.1
        have hrepBound : res.1.length ≤ R a := by
          refine le_trans ?_ (hresLen.trans (Nat.mul_le_mul_left rC (Nat.pow_le_pow_left ?_ rD)))
          all_goals simp only [encHandlerCall, length_encPair, encBits_apply]
          all_goals omega
        have hstateEnc :
            (encPair stateEncoding encUnary (res.2, k + 1)).length ≤
              (encPair stateEncoding encUnary (s, k)).length + resources' a request.2 := by
          simp only [length_encPair, encUnary_apply, List.length_replicate, resources']
          omega
        exact ⟨⟨hinv', hguard.1, hstepLen⟩, hrepBound.trans (Nat.le_add_right _ _), hstateEnc⟩
      · rw [cappedHandler, ite_eq_right hguard] at hresult
        obtain rfl := OracleComp.eq_of_mem_supportWith_pure hresult
        exact ⟨⟨hinv, hkQ, hlen⟩, Nat.zero_le _, Nat.le_add_right _ _⟩)
  exact (hsub.map (f := fun ⟨res, sk⟩ => (res, sk.1)) (by fun_prop)).congr
    fun a ExtState oracle ext =>
      runWith_cappedHandler_eq a (hqb (prepare a)).1 (hqb (prepare a)).2 oracle ext

section Wrappers

variable {Operation External α β Caller State : Type} [DecidableEq Operation] [DecidableEq External]
  {source : α ↪ List Bool} {input : Caller ↪ List Bool} {output : β ↪ List Bool}
  {operationEncoding : Operation ↪ List Bool} {stateEncoding : State ↪ List Bool}

/-- Closed `ProbComp` stateful substitution under polynomially bounded additive state growth,
without a user-supplied reply-length bound. -/
theorem IsOraclePPTOn.run_interpret_preprocess_of_bounded_growth
    {program : α → WordOracleComp Operation β}
    {handler : Caller → Operation × List Bool → State → ProbComp (List Bool × State)}
    {prepare : Caller → α} {initial : Caller → State} {growth : Caller → List Bool → ℕ}
    (hprogram : IsOraclePPTOn source output program)
    (hprepare : ComputableInPolyTime prepare input source)
    (hhandler : IsPPTOn (encHandlerCall input operationEncoding stateEncoding)
      (encPair encBits stateEncoding) fun ⟨caller, req, state⟩ => handler caller req state)
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (invariant : Caller → State → Prop) (hinit : ∀ a, invariant a (initial a))
    (hgrowth : PolyBounded (fun pair : Caller × List Bool => (encPair input encBits pair).length)
      fun ⟨a, w⟩ => growth a w)
    (hpreserve : ∀ a req state, invariant a state →
      ∀ result ∈ (ProbComp.eval (handler a req state)).support,
        invariant a result.2 ∧
          (stateEncoding result.2).length ≤ (stateEncoding state).length + growth a req.2) :
    IsPPTOn input (encPair output stateEncoding) (fun a =>
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifFin n)) (handler a))
        (program (prepare a))).run (initial a)) := by
  refine ((hprogram.run_interpret_preprocess_open_of_bounded_growth (External := Empty)
    (handler := fun a req state => ProbOracleComp.sample (handler a req state))
    hprepare hhandler.isOraclePPTOn hinitial invariant hinit hgrowth
    fun a req state hstate result hresult => hpreserve a req state hstate result
      ((ProbOracleComp.support_sample _).subset hresult)).congr fun a _ _ _ => ?_).isPPTOn
  rw [ProbOracleComp.sample_run_interpret]

/-- Open stateful substitution when every encoded state is bounded by a polynomial `bound` in the
caller alone, requiring no invariant, growth allowance, or support case split. -/
theorem IsOraclePPTOn.run_interpret_preprocess_open_of_state_le
    {program : α → WordOracleComp Operation β}
    {handler : Caller → Operation × List Bool → State → WordOracleComp External (List Bool × State)}
    {prepare : Caller → α} {initial : Caller → State} {bound : Caller → ℕ}
    (hprogram : IsOraclePPTOn source output program)
    (hprepare : ComputableInPolyTime prepare input source)
    (hhandler : IsOraclePPTOn (encHandlerCall input operationEncoding stateEncoding)
      (encPair encBits stateEncoding) fun ⟨caller, req, state⟩ => handler caller req state)
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (hbound : PolyBounded (fun a => (input a).length) bound)
    (hstate : ∀ a state, (stateEncoding state).length ≤ bound a) :
    IsOraclePPTOn input (encPair output stateEncoding) (fun a =>
      (OracleComp.interpret
        (OracleComp.sumHandler
          (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n))) (handler a))
        (program (prepare a))).run (initial a)) :=
  hprogram.run_interpret_preprocess_open_of_bounded_growth hprepare hhandler hinitial
    (fun _ _ => True) (fun _ => trivial) (growth := fun a _ => bound a) (by growth_poly)
    fun a _ _ _ result _ => ⟨trivial, (hstate a result.2).trans (Nat.le_add_left _ _)⟩

/-- Closed `ProbComp` stateful substitution when every encoded state is bounded by a polynomial
`bound` in the caller alone, requiring no invariant, growth allowance, or support case split. -/
theorem IsOraclePPTOn.run_interpret_preprocess_of_state_le
    {program : α → WordOracleComp Operation β}
    {handler : Caller → Operation × List Bool → State → ProbComp (List Bool × State)}
    {prepare : Caller → α} {initial : Caller → State} {bound : Caller → ℕ}
    (hprogram : IsOraclePPTOn source output program)
    (hprepare : ComputableInPolyTime prepare input source)
    (hhandler : IsPPTOn (encHandlerCall input operationEncoding stateEncoding)
      (encPair encBits stateEncoding) fun ⟨caller, req, state⟩ => handler caller req state)
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (hbound : PolyBounded (fun a => (input a).length) bound)
    (hstate : ∀ a state, (stateEncoding state).length ≤ bound a) :
    IsPPTOn input (encPair output stateEncoding) (fun a =>
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifFin n)) (handler a))
        (program (prepare a))).run (initial a)) :=
  hprogram.run_interpret_preprocess_of_bounded_growth hprepare hhandler hinitial
    (fun _ _ => True) (fun _ => trivial) (growth := fun a _ => bound a) (by growth_poly)
    fun a _ _ _ result _ => ⟨trivial, (hstate a result.2).trans (Nat.le_add_left _ _)⟩

/-- Running an oracle-PPT program via `ProbOracleComp.run` against an efficient memoryless
`ProbComp` oracle is closed PPT, without a user-supplied reply-length bound. -/
theorem IsOraclePPTOn.isPPTOn_run {program : α → WordOracleComp Operation β}
    {oracle : Caller → Operation × List Bool → ProbComp (List Bool)} {prepare : Caller → α}
    (hprogram : IsOraclePPTOn source output program)
    (hprepare : ComputableInPolyTime prepare input source)
    (horacle : IsPPTOn (encPair input (encPair operationEncoding encBits)) encBits
      fun ⟨caller, req⟩ => oracle caller req) :
    IsPPTOn input output (fun a => (program (prepare a)).run (oracle a)) := by
  let EIn := encHandlerCall input operationEncoding (encFinEnum Unit)
  have hlift : IsPPTOn EIn (encPair encBits (encFinEnum Unit))
      (fun ⟨caller, req, state⟩ => (·, state) <$> oracle caller req) :=
    (horacle.preprocess (input := EIn) (prepare := fun p => (p.1, p.2.1))
      (by dsimp only [EIn, encHandlerCall]; fun_prop)).map_with
      (f := fun p reply => (reply, p.2.2)) (by dsimp only [EIn, encHandlerCall]; fun_prop)
  refine ((hprogram.run_interpret_preprocess_of_state_le
    (handler := fun a req (state : Unit) => (·, state) <$> oracle a req)
    hprepare hlift (.const ()) (.const (encFinEnum Unit ()).length)
    fun _ s => by cases s; exact le_rfl).map (.fst output (encFinEnum Unit))).congr fun a => ?_
  rw [ProbOracleComp.run, OracleComp.run_interpret_sumHandler_readOnly]; simp

/-- Running any `IsOraclePPTOn` program against `fun _ => pure []` is closed PPT. -/
theorem IsOraclePPTOn.isPPTOn_runEmptyOracle {program : α → WordOracleComp Operation β}
    (hprogram : IsOraclePPTOn source output program) :
    IsPPTOn source output (fun a => (program a).run (fun _ => pure [])) := by
  have := hprogram.finite_operations
  exact hprogram.isPPTOn_run (operationEncoding := encFinite Operation) .id'
    (ComputableInPolyTime.const []).isPPTOn

/-- Parameterized `IsOraclePPTOn.run_interpret_preprocess_open_of_bounded_growth`. -/
theorem IsOraclePPT.run_interpret_preprocess_open_of_bounded_growth
    {program : ℕ → List Bool → WordOracleComp Operation β}
    {handler : Caller → Operation × List Bool → State → WordOracleComp External (List Bool × State)}
    {prepare : Caller → ℕ × List Bool} {initial : Caller → State} {growth : Caller → List Bool → ℕ}
    (hprogram : IsOraclePPT output program)
    (hprepare : ComputableInPolyTime prepare input (encPair encUnary encBits))
    (hhandler : IsOraclePPTOn (encHandlerCall input operationEncoding stateEncoding)
      (encPair encBits stateEncoding) fun ⟨caller, req, state⟩ => handler caller req state)
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (invariant : Caller → State → Prop) (hinit : ∀ a, invariant a (initial a))
    (hgrowth : PolyBounded (fun pair : Caller × List Bool => (encPair input encBits pair).length)
      fun ⟨a, w⟩ => growth a w)
    (hpreserve : ∀ a req state, invariant a state →
      ∀ result ∈ OracleComp.support (handler a req state),
        invariant a result.2 ∧
          (stateEncoding result.2).length ≤ (stateEncoding state).length + growth a req.2) :
    IsOraclePPTOn input (encPair output stateEncoding) (fun a =>
      (OracleComp.interpret
        (OracleComp.sumHandler
          (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n))) (handler a))
        (program (prepare a).1 (prepare a).2)).run (initial a)) :=
  hprogram.on.run_interpret_preprocess_open_of_bounded_growth hprepare hhandler hinitial invariant
    hinit hgrowth hpreserve

/-- Parameterized `IsOraclePPTOn.run_interpret_preprocess_of_bounded_growth`. -/
theorem IsOraclePPT.run_interpret_preprocess_of_bounded_growth
    {program : ℕ → List Bool → WordOracleComp Operation β}
    {handler : Caller → Operation × List Bool → State → ProbComp (List Bool × State)}
    {prepare : Caller → ℕ × List Bool} {initial : Caller → State} {growth : Caller → List Bool → ℕ}
    (hprogram : IsOraclePPT output program)
    (hprepare : ComputableInPolyTime prepare input (encPair encUnary encBits))
    (hhandler : IsPPTOn (encHandlerCall input operationEncoding stateEncoding)
      (encPair encBits stateEncoding) fun ⟨caller, req, state⟩ => handler caller req state)
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (invariant : Caller → State → Prop) (hinit : ∀ a, invariant a (initial a))
    (hgrowth : PolyBounded (fun pair : Caller × List Bool => (encPair input encBits pair).length)
      fun ⟨a, w⟩ => growth a w)
    (hpreserve : ∀ a req state, invariant a state →
      ∀ result ∈ (ProbComp.eval (handler a req state)).support,
        invariant a result.2 ∧
          (stateEncoding result.2).length ≤ (stateEncoding state).length + growth a req.2) :
    IsPPTOn input (encPair output stateEncoding) (fun a =>
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifFin n)) (handler a))
        (program (prepare a).1 (prepare a).2)).run (initial a)) :=
  hprogram.on.run_interpret_preprocess_of_bounded_growth hprepare hhandler hinitial invariant hinit
    hgrowth hpreserve

/-- Parameterized `IsOraclePPTOn.run_interpret_preprocess_open_of_state_le`. -/
theorem IsOraclePPT.run_interpret_preprocess_open_of_state_le
    {program : ℕ → List Bool → WordOracleComp Operation β}
    {handler : Caller → Operation × List Bool → State → WordOracleComp External (List Bool × State)}
    {prepare : Caller → ℕ × List Bool} {initial : Caller → State} {bound : Caller → ℕ}
    (hprogram : IsOraclePPT output program)
    (hprepare : ComputableInPolyTime prepare input (encPair encUnary encBits))
    (hhandler : IsOraclePPTOn (encHandlerCall input operationEncoding stateEncoding)
      (encPair encBits stateEncoding) fun ⟨caller, req, state⟩ => handler caller req state)
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (hbound : PolyBounded (fun a => (input a).length) bound)
    (hstate : ∀ a state, (stateEncoding state).length ≤ bound a) :
    IsOraclePPTOn input (encPair output stateEncoding) (fun a =>
      (OracleComp.interpret
        (OracleComp.sumHandler
          (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n))) (handler a))
        (program (prepare a).1 (prepare a).2)).run (initial a)) :=
  hprogram.on.run_interpret_preprocess_open_of_state_le hprepare hhandler hinitial hbound hstate

/-- Parameterized `IsOraclePPTOn.run_interpret_preprocess_of_state_le`. -/
theorem IsOraclePPT.run_interpret_preprocess_of_state_le
    {program : ℕ → List Bool → WordOracleComp Operation β}
    {handler : Caller → Operation × List Bool → State → ProbComp (List Bool × State)}
    {prepare : Caller → ℕ × List Bool} {initial : Caller → State} {bound : Caller → ℕ}
    (hprogram : IsOraclePPT output program)
    (hprepare : ComputableInPolyTime prepare input (encPair encUnary encBits))
    (hhandler : IsPPTOn (encHandlerCall input operationEncoding stateEncoding)
      (encPair encBits stateEncoding) fun ⟨caller, req, state⟩ => handler caller req state)
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (hbound : PolyBounded (fun a => (input a).length) bound)
    (hstate : ∀ a state, (stateEncoding state).length ≤ bound a) :
    IsPPTOn input (encPair output stateEncoding) (fun a =>
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifFin n)) (handler a))
        (program (prepare a).1 (prepare a).2)).run (initial a)) :=
  hprogram.on.run_interpret_preprocess_of_state_le hprepare hhandler hinitial hbound hstate

/-- Parameterized `IsOraclePPTOn.isPPTOn_run`. -/
theorem IsOraclePPT.isPPTOn_run {program : ℕ → List Bool → WordOracleComp Operation β}
    {oracle : Caller → Operation × List Bool → ProbComp (List Bool)}
    {prepare : Caller → ℕ × List Bool}
    (hprogram : IsOraclePPT output program)
    (hprepare : ComputableInPolyTime prepare input (encPair encUnary encBits))
    (horacle : IsPPTOn (encPair input (encPair operationEncoding encBits)) encBits
      fun ⟨caller, req⟩ => oracle caller req) :
    IsPPTOn input output (fun a => (program (prepare a).1 (prepare a).2).run (oracle a)) :=
  hprogram.on.isPPTOn_run hprepare horacle

end Wrappers

end Cslib.Probability
