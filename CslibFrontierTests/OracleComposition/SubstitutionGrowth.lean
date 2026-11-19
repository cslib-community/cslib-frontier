/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Computability.Probabilistic.Oracle.SubstitutionGrowth
import CslibFrontier.Computability.Probabilistic.Oracle.RunState
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Tests for open stateful oracle substitution with state-dependent replies

Non-degenerate witnesses for
`Cslib.Probability.IsOraclePPTOn.run_interpret_preprocess_open_of_growth`:

* an echo handler that flips a private coin, forwards the request to an external stateful oracle,
  appends the coin and bounded external reply to its state, and echoes its entire prior state as the
  reply;
* a fixed-request multi-call client (`echoRun`) certified with non-identity `prepare`, non-constant
  initial state, and a non-trivial invariant, together with an explicit calculation of its joint law
  against a stateful external counter oracle;
* a variable-request multi-call client (`varEchoRun`) whose per-call state growth depends on the
  request length (`|w| + 1`);
* a multi-field caller `(n, tag)` whose handler replies with twice its prior state (`2 * |state|`),
  exercising a non-identity polynomial `reply` bound, non-trivial `prepare`, and `tag`-dependent
  initial state;
* a separation example showing that under the natural state invariant `n ≤ |state|`, no
  state-independent allowance satisfies the `hpreserve` hypothesis of
  `IsOraclePPTOn.run_interpret_preprocess_open_of_polyBounded`.
-/

namespace CslibFrontierTests.OracleSubstitutionGrowth

open Cslib Cslib.Probability Turing Turing.MultiTapeTM

/-! ### Echo handler with private coins and open external calls -/

/-- An open stateful handler with private randomness and an external oracle call: on each call it
samples a private coin `b`, queries the external oracle on `request.2` (reading at most
`request.2.length` bits), appends `b :: ext` to its private state, and echoes the entire prior state
as its reply. -/
private noncomputable def echoHandler (_ : ℕ) (request : Unit × List Bool) (state : List Bool) :
    WordOracleComp Unit (List Bool × List Bool) := do
  let b ← ProbOracleComp.sample (ProbComp.uniform Bool)
  let ext ← List.take request.2.length <$> ProbOracleComp.query ((), request.2)
  return (state, state ++ (b :: ext))

private theorem echoHandler_isOraclePPTOn :
    IsOraclePPTOn
      (encHandlerCall encUnary (encFinEnum Unit) encBits)
      (encPair encBits encBits)
      (fun ⟨n, request, state⟩ => echoHandler n request state) := by
  unfold echoHandler
  let EIn := encHandlerCall encUnary (encFinEnum Unit) encBits
  apply (isPPTOn_uniform_bool EIn).isOraclePPTOn.bind_with
  apply IsOraclePPTOn.bind_with (middle := encBits)
  · have hcall : ComputableInPolyTime
        (fun p : (ℕ × (Unit × List Bool) × List Bool) × Bool => p.1.2)
        (encPair EIn encBool) (encPair (encPair (encFinEnum Unit) encBits) encBits) := by
      dsimp only [EIn, encHandlerCall]
      exact (ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _)
    let reqFn : (ℕ × (Unit × List Bool) × List Bool) × Bool → List Bool :=
      fun ⟨⟨_, ⟨_, word⟩, _⟩, _⟩ => word
    have hreq : ComputableInPolyTime reqFn (encPair EIn encBool) encBits :=
      (ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.fst _ _).comp hcall)
    have hlim : ComputableInPolyTime (fun p => (reqFn p).length) (encPair EIn encBool)
        encUnary :=
      ComputableInPolyTime.length_bits.comp hreq
    exact IsOraclePPTOn.query_take () hreq hlim
  · let EStep := encPair (encPair EIn encBool) encBits
    have hcall : ComputableInPolyTime
        (fun q : ((ℕ × (Unit × List Bool) × List Bool) × Bool) × List Bool => q.1.1.2)
        EStep (encPair (encPair (encFinEnum Unit) encBits) encBits) := by
      dsimp only [EStep, EIn, encHandlerCall]
      exact (ComputableInPolyTime.snd _ _).comp
        ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _))
    let stFn : ((ℕ × (Unit × List Bool) × List Bool) × Bool) × List Bool → List Bool :=
      fun ⟨⟨⟨_, _, state⟩, _⟩, _⟩ => state
    let coinFn : ((ℕ × (Unit × List Bool) × List Bool) × Bool) × List Bool → Bool :=
      fun ⟨⟨_, coin⟩, _⟩ => coin
    let extFn : ((ℕ × (Unit × List Bool) × List Bool) × Bool) × List Bool → List Bool :=
      fun ⟨_, ext⟩ => ext
    have hst : ComputableInPolyTime stFn EStep encBits :=
      (ComputableInPolyTime.snd _ _).comp hcall
    have hcoinq : ComputableInPolyTime coinFn EStep encBool :=
      (ComputableInPolyTime.snd EIn encBool).comp (ComputableInPolyTime.fst _ _)
    have hextq : ComputableInPolyTime extFn EStep encBits :=
      ComputableInPolyTime.snd _ _
    have hpost : ComputableInPolyTime
        (fun q => (stFn q, stFn q ++ (coinFn q :: extFn q))) EStep (encPair encBits encBits) := by
      fun_prop
    exact hpost.isOraclePPTOn

private theorem echoHandler_preserve {k n : ℕ} (request : Unit × List Bool) (state : List Bool)
    (hstate : k ≤ state.length) (result : List Bool × List Bool)
    (hresult : result ∈ OracleComp.support (echoHandler n request state)) :
    k ≤ result.2.length ∧
      result.1.length ≤ state.length ∧
      result.2.length ≤ state.length + (request.2.length + 1) := by
  simp only [echoHandler, OracleComp.mem_supportWith_bind_iff,
    OracleComp.mem_supportWith_map_iff] at hresult
  obtain ⟨b, -, ext, hex, rfl⟩ := hresult
  obtain ⟨reply, -, rfl⟩ := hex
  simp only [List.length_append, List.length_cons]
  have htake := List.length_take_le request.2.length reply
  exact ⟨by omega, le_rfl, by omega⟩

/-! ### Multi-call client with non-identity preparation and growing initial state -/

/-- Run `m` sequential queries on `[true]`, keeping one bit of each reply as the loop state. -/
private noncomputable def echoClient (m : ℕ) : WordOracleComp Unit (List Bool) :=
  OracleComp.iterate m (fun _ => List.take 1 <$> ProbOracleComp.query ((), [true])) []

private theorem echoClient_isOraclePPTOn : IsOraclePPTOn encUnary encBits echoClient := by
  refine IsOraclePPTOn.iterate_of_bounded_growth (count := id) (initial := fun _ => [])
    ComputableInPolyTime.id' (.const []) (by fun_prop) (growth := 1) ?_
  intro _ next hnext
  obtain ⟨reply, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
  simp only [encBits_apply]
  exact (List.length_take_le _ _).trans (Nat.le_add_left _ _)

/-- Run `echoClient (n + 1)` against `echoHandler n` starting from `List.replicate n false`. -/
private noncomputable def echoRun (n : ℕ) : WordOracleComp Unit (List Bool × List Bool) :=
  (OracleComp.interpret
    (OracleComp.sumHandler
      (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
      (echoHandler n))
    (echoClient (n + 1))).run (List.replicate n false)

/-- `echoRun` is strict oracle PPT by `run_interpret_preprocess_open_of_growth`. -/
example : IsOraclePPTOn encUnary (encPair encBits encBits) echoRun := by
  unfold echoRun
  refine echoClient_isOraclePPTOn.run_interpret_preprocess_open_of_growth
    (operationEncoding := encFinEnum Unit)
    (prepare := fun n => n + 1)
    (initial := fun n => List.replicate n false)
    (reply := fun _ _ k => k)
    (growth := fun _ w => w.length + 1)
    (by fun_prop) echoHandler_isOraclePPTOn (ComputableInPolyTime.bitsReplicate false)
    (fun n state => n ≤ state.length) (fun n => by simp)
    (PolyBounded.self.mono fun ⟨_, _, k⟩ => by simp)
    (PolyBounded.self.mono fun ⟨_, w⟩ => by simp only [length_encPair, encBits_apply]; omega)
    (fun n request state hstate result hresult => by
      simpa only [encBits_apply] using
        echoHandler_preserve (k := n) (n := n) request state hstate result hresult)

/-! ### Explicit joint law with an external stateful counter oracle -/

/-- External stateful oracle returning `[decide (c % 2 = 0)]` and incrementing the counter `c`. -/
private noncomputable def parityOracle (_ : Unit × List Bool) : StateT ℕ PMF (List Bool) :=
  fun c => PMF.pure ([decide (c % 2 = 0)], c + 1)

private theorem run_echoHandler_one (c : ℕ) (state : List Bool) :
    ProbOracleComp.runWith parityOracle (StateT.run (echoHandler 1 ((), [true])) state) c =
      (PMF.uniformOfFintype Bool).map fun coin =>
        ((state, state ++ [coin, decide (c % 2 = 0)]), c + 1) := by
  simp only [StateT.run, echoHandler, parityOracle, runWith_norm, pmf_norm,
    ProbComp.eval_uniform, List.length_singleton, List.take_succ_cons, List.take_zero]
  rfl

-- On `n = 1` (`2` calls starting from `[false]` and external counter `0`), the first call extends
-- `[false]` to `[false, b₀, true]`, the second call echoes `[false, b₀, true]` so `echoClient`
-- returns `[false]`, the final handler state is `[false, b₀, true, b₁, false]`, and the external
-- counter reaches `2`.
example :
    ProbOracleComp.runWith parityOracle (echoRun 1) 0 =
      (PMF.uniformOfFintype (Bool × Bool)).map fun ⟨b₀, b₁⟩ =>
        (([false], [false, b₀, true, b₁, false]), 2) := by
  rw [echoRun, echoClient, OracleComp.iterate_succ, OracleComp.iterate_succ,
    OracleComp.iterate_zero]
  simp only [runWith_norm, pmf_norm, run_echoHandler_one]
  rw [← PMF.uniformOfFintype_prod Bool Bool]
  simp [pmf_norm]

/-! ### Variable-length request growth -/

/-- Run `n` sequential queries, each passing an `n`-bit word so the handler's growth is `n + 1`. -/
private noncomputable def varEchoClient (n : ℕ) : WordOracleComp Unit (List Bool) :=
  OracleComp.iterate n (fun _ => List.take 1 <$> ProbOracleComp.query ((), List.replicate n true))
    []

private theorem varEchoClient_isOraclePPTOn :
    IsOraclePPTOn encUnary encBits varEchoClient := by
  refine IsOraclePPTOn.iterateWith_of_bounded_growth (count := id) (initial := fun _ => [])
    ComputableInPolyTime.id' (.const []) ?_ (growth := fun _ => 1) (.const 1) ?_
  · have hreq : ComputableInPolyTime (fun p : ℕ × List Bool => List.replicate p.1 true)
        (encPair encUnary encBits) encBits :=
      (ComputableInPolyTime.bitsReplicate true).comp (ComputableInPolyTime.fst _ _)
    exact IsOraclePPTOn.query_take () hreq (ComputableInPolyTime.const 1)
  · intro _ _ next hnext
    obtain ⟨reply, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
    simp only [encBits_apply]
    exact (List.length_take_le _ _).trans (Nat.le_add_left _ _)

/-- Run `varEchoClient n` against `echoHandler n` starting from `[]`. -/
private noncomputable def varEchoRun (n : ℕ) : WordOracleComp Unit (List Bool × List Bool) :=
  (OracleComp.interpret
    (OracleComp.sumHandler
      (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
      (echoHandler n))
    (varEchoClient n)).run []

/-- `varEchoRun` is strict oracle PPT even with `O(n²)` accumulated state and echoed replies. -/
example : IsOraclePPTOn encUnary (encPair encBits encBits) varEchoRun := by
  unfold varEchoRun
  refine varEchoClient_isOraclePPTOn.run_interpret_preprocess_open_of_growth
    (operationEncoding := encFinEnum Unit)
    (prepare := id) (initial := fun _ => [])
    (reply := fun _ _ k => k) (growth := fun _ w => w.length + 1)
    ComputableInPolyTime.id' echoHandler_isOraclePPTOn (.const [])
    (fun _ state => 0 ≤ state.length) (fun _ => Nat.zero_le _)
    (PolyBounded.self.mono fun ⟨_, _, k⟩ => by simp)
    (PolyBounded.self.mono fun ⟨_, w⟩ => by simp only [length_encPair, encBits_apply]; omega)
    (fun n request state _ result hresult => by
      simpa only [encBits_apply] using
        echoHandler_preserve (k := 0) (n := n) request state (Nat.zero_le _) result hresult)

/-! ### Multi-field caller with doubled-state replies -/

/-- A tagged stateful handler that appends a private fair coin and a bounded external answer to its
state while replying with twice the prior state (`state ++ state`), exercising a non-identity
polynomial `reply` bound (`2 * k`). -/
private noncomputable def twiceEchoHandler (_ : ℕ × List Bool) (request : Unit × List Bool)
    (state : List Bool) : WordOracleComp Unit (List Bool × List Bool) := do
  let b ← ProbOracleComp.sample (ProbComp.uniform Bool)
  let ext ← List.take request.2.length <$> ProbOracleComp.query ((), request.2)
  return (state ++ state, state ++ (b :: ext))

private theorem twiceEchoHandler_isOraclePPTOn :
    IsOraclePPTOn
      (encHandlerCall (encPair encUnary encBits) (encFinEnum Unit) encBits)
      (encPair encBits encBits)
      (fun ⟨caller, request, state⟩ => twiceEchoHandler caller request state) := by
  unfold twiceEchoHandler
  let EIn := encHandlerCall (encPair encUnary encBits) (encFinEnum Unit) encBits
  apply (isPPTOn_uniform_bool EIn).isOraclePPTOn.bind_with
  apply IsOraclePPTOn.bind_with (middle := encBits)
  · have hcall : ComputableInPolyTime
        (fun p : ((ℕ × List Bool) × (Unit × List Bool) × List Bool) × Bool => p.1.2)
        (encPair EIn encBool) (encPair (encPair (encFinEnum Unit) encBits) encBits) := by
      dsimp only [EIn, encHandlerCall]
      exact (ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _)
    let reqFn : ((ℕ × List Bool) × (Unit × List Bool) × List Bool) × Bool → List Bool :=
      fun ⟨⟨_, ⟨_, word⟩, _⟩, _⟩ => word
    have hreq : ComputableInPolyTime reqFn (encPair EIn encBool) encBits :=
      (ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.fst _ _).comp hcall)
    have hlim : ComputableInPolyTime (fun p => (reqFn p).length) (encPair EIn encBool)
        encUnary :=
      ComputableInPolyTime.length_bits.comp hreq
    exact IsOraclePPTOn.query_take () hreq hlim
  · let EStep := encPair (encPair EIn encBool) encBits
    have hcall : ComputableInPolyTime
        (fun q : (((ℕ × List Bool) × (Unit × List Bool) × List Bool) × Bool) × List Bool =>
          q.1.1.2)
        EStep (encPair (encPair (encFinEnum Unit) encBits) encBits) := by
      dsimp only [EStep, EIn, encHandlerCall]
      exact (ComputableInPolyTime.snd _ _).comp
        ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _))
    let stFn : (((ℕ × List Bool) × (Unit × List Bool) × List Bool) × Bool) × List Bool →
        List Bool :=
      fun ⟨⟨⟨_, _, state⟩, _⟩, _⟩ => state
    let coinFn : (((ℕ × List Bool) × (Unit × List Bool) × List Bool) × Bool) × List Bool →
        Bool :=
      fun ⟨⟨_, coin⟩, _⟩ => coin
    let extFn : (((ℕ × List Bool) × (Unit × List Bool) × List Bool) × Bool) × List Bool →
        List Bool :=
      fun ⟨_, ext⟩ => ext
    have hst : ComputableInPolyTime stFn EStep encBits :=
      (ComputableInPolyTime.snd _ _).comp hcall
    have hcoinq : ComputableInPolyTime coinFn EStep encBool :=
      (ComputableInPolyTime.snd EIn encBool).comp (ComputableInPolyTime.fst _ _)
    have hextq : ComputableInPolyTime extFn EStep encBits :=
      ComputableInPolyTime.snd _ _
    have hpost : ComputableInPolyTime
        (fun q => (stFn q ++ stFn q, stFn q ++ (coinFn q :: extFn q)))
        EStep (encPair encBits encBits) := by
      fun_prop
    exact hpost.isOraclePPTOn

/-- Run `echoClient (p.1 + p.2.length)` against `twiceEchoHandler p` initialized with `p.2`. -/
private noncomputable def twiceEchoRun (p : ℕ × List Bool) :
    WordOracleComp Unit (List Bool × List Bool) :=
  (OracleComp.interpret
    (OracleComp.sumHandler
      (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
      (twiceEchoHandler p))
    (echoClient (p.1 + p.2.length))).run p.2

/-- `twiceEchoRun` certifies a compound caller, non-trivial `prepare`, `tag`-dependent initial
state, invariant `tag.length ≤ state.length`, and reply length `2 * |state|`. -/
example : IsOraclePPTOn (encPair encUnary encBits) (encPair encBits encBits) twiceEchoRun := by
  unfold twiceEchoRun
  refine echoClient_isOraclePPTOn.run_interpret_preprocess_open_of_growth
    (operationEncoding := encFinEnum Unit)
    (prepare := fun p : ℕ × List Bool => p.1 + p.2.length)
    (initial := fun p : ℕ × List Bool => p.2)
    (reply := fun _ _ k => 2 * k)
    (growth := fun _ w => w.length + 1)
    (by fun_prop) twiceEchoHandler_isOraclePPTOn (ComputableInPolyTime.snd _ _)
    (fun p state => p.2.length ≤ state.length) (fun _ => le_rfl)
    ((PolyBounded.const 2).mul PolyBounded.self |>.mono fun ⟨⟨_, _⟩, _, k⟩ => by
      dsimp only; omega)
    (PolyBounded.self.mono fun ⟨_, w⟩ => by simp only [length_encPair, encBits_apply]; omega)
    (fun p request state hstate result hresult => by
      simp only [twiceEchoHandler, OracleComp.mem_supportWith_bind_iff,
        OracleComp.mem_supportWith_map_iff] at hresult
      obtain ⟨b, -, ext, hex, rfl⟩ := hresult
      obtain ⟨reply, -, rfl⟩ := hex
      simp only [encBits_apply, List.length_append, List.length_cons]
      have htake := List.length_take_le request.2.length reply
      exact ⟨by omega, by omega, by omega⟩)

/-! ### Separation from state-independent allowances -/

-- Under the local state invariant `n ≤ state.length`, no state-independent allowance
-- `resources : ℕ → List Bool → ℕ` can satisfy the reply inequality of
-- `IsOraclePPTOn.run_interpret_preprocess_open_of_polyBounded` for `echoHandler`.
example (resources : ℕ → List Bool → ℕ) :
    ¬ (∀ (n : ℕ) (request : Unit × List Bool) (state : List Bool),
        n ≤ state.length →
        ∀ result ∈ OracleComp.support (echoHandler n request state),
          result.1.length ≤ resources n request.2) := by
  intro h
  let state := List.replicate (resources 0 [] + 1) false
  have hmem : (state, state ++ [true]) ∈ OracleComp.support (echoHandler 0 ((), []) state) := by
    simp only [echoHandler, OracleComp.mem_supportWith_bind_iff,
      OracleComp.mem_supportWith_map_iff]
    refine ⟨true, by simp, [], ⟨[], by simp, rfl⟩, rfl⟩
  have hle := h 0 ((), []) state (Nat.zero_le _) (state, state ++ [true]) hmem
  simp only [state, List.length_replicate] at hle
  omega

end CslibFrontierTests.OracleSubstitutionGrowth
