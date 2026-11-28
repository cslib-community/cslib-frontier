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
`Cslib.Probability.IsOraclePPTOn.run_interpret_preprocess_open_of_bounded_growth`:

* an echo handler that flips a private coin, forwards the request to an external stateful oracle,
  appends the coin and bounded external reply to its state, and replies with twice its prior
  state (`state ++ state`), without any user-supplied reply-length bound;
* a fixed-request multi-call client (`echoRun`) certified with non-identity `prepare`, non-constant
  initial state, and a non-trivial invariant, together with an explicit calculation of its joint law
  against a stateful external counter oracle;
* a variable-request multi-call client (`varEchoRun`) whose per-call state growth depends on the
  request length (`|w| + 1`);
* a separation example showing that for every invariant containing `initial` and preserved by
  `echoHandler`, no state-independent allowance satisfies the `hpreserve` hypothesis of
  `IsOraclePPTOn.run_interpret_preprocess_open_of_polyBounded`.
-/

namespace CslibFrontierTests.OracleSubstitutionGrowth

open Cslib Cslib.Probability Turing Turing.MultiTapeTM

/-! ### Echo handler with private coins and open external calls -/

/-- An open stateful handler with private randomness and an external oracle call: on each call it
samples a private coin `b`, queries the external oracle on `request.2` (reading at most
`request.2.length` bits), appends `b :: ext` to its private state, and replies with twice its prior
state (`state ++ state`). -/
private noncomputable def echoHandler (_ : ℕ) (request : Unit × List Bool) (state : List Bool) :
    WordOracleComp Unit (List Bool × List Bool) := do
  let b ← ProbOracleComp.sample (ProbComp.uniform Bool)
  let ext ← List.take request.2.length <$> ProbOracleComp.query ((), request.2)
  return (state ++ state, state ++ (b :: ext))

/-- Certify `echoHandler` as strict oracle PPT using the uniform-coin primitive, external call,
and polynomial-time postprocessing. -/
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
        (fun q => (stFn q ++ stFn q, stFn q ++ (coinFn q :: extFn q)))
        EStep (encPair encBits encBits) :=
      (hst.bitsAppend hst).prod (hst.bitsAppend (hcoinq.bitsCons hextq))
    exact hpost.isOraclePPTOn

/-- Preservation and additive state growth for `echoHandler`. -/
private theorem echoHandler_preserve {k n : ℕ} (request : Unit × List Bool) (state : List Bool)
    (hstate : k ≤ state.length) (result : List Bool × List Bool)
    (hresult : result ∈ OracleComp.support (echoHandler n request state)) :
    k ≤ result.2.length ∧
      result.2.length ≤ state.length + (request.2.length + 1) := by
  simp only [echoHandler, OracleComp.mem_supportWith_bind_iff,
    OracleComp.mem_supportWith_map_iff] at hresult
  obtain ⟨b, -, ext, hex, rfl⟩ := hresult
  obtain ⟨reply, -, rfl⟩ := hex
  simp only [List.length_append, List.length_cons]
  have htake := List.length_take_le request.2.length reply
  exact ⟨by omega, by omega⟩

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

/-- `echoRun` is strict oracle PPT by `run_interpret_preprocess_open_of_bounded_growth`. -/
example : IsOraclePPTOn encUnary (encPair encBits encBits) echoRun := by
  unfold echoRun
  refine echoClient_isOraclePPTOn.run_interpret_preprocess_open_of_bounded_growth
    (operationEncoding := encFinEnum Unit)
    (prepare := fun n => n + 1)
    (initial := fun n => List.replicate n false)
    (growth := fun _ w => w.length + 1)
    (by fun_prop) echoHandler_isOraclePPTOn (ComputableInPolyTime.bitsReplicate false)
    (fun n state => n ≤ state.length) (fun n => by simp)
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
        ((state ++ state, state ++ [coin, decide (c % 2 = 0)]), c + 1) := by
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
  refine varEchoClient_isOraclePPTOn.run_interpret_preprocess_open_of_bounded_growth
    (operationEncoding := encFinEnum Unit)
    (prepare := id) (initial := fun _ => [])
    (growth := fun _ w => w.length + 1)
    ComputableInPolyTime.id' echoHandler_isOraclePPTOn (.const [])
    (fun _ state => 0 ≤ state.length) (fun _ => Nat.zero_le _)
    (PolyBounded.self.mono fun ⟨_, w⟩ => by simp only [length_encPair, encBits_apply]; omega)
    (fun n request state _ result hresult => by
      simpa only [encBits_apply] using
        echoHandler_preserve (k := 0) (n := n) request state (Nat.zero_le _) result hresult)

/-! ### Separation from state-independent allowances -/

/-- One empty-request step on `echoHandler 0` appends `[true]` to `state` and replies with
`state ++ state`. -/
private theorem echoHandler_step_mem_support (state : List Bool) :
    (state ++ state, state ++ [true]) ∈ OracleComp.support (echoHandler 0 ((), []) state) := by
  simp only [echoHandler, OracleComp.mem_supportWith_bind_iff,
    OracleComp.mem_supportWith_map_iff]
  refine ⟨true, by simp, [], ⟨[], by simp, rfl⟩, rfl⟩

-- No preserved invariant containing `initial` admits a state-independent allowance
-- `resources : ℕ → List Bool → ℕ` satisfying the reply inequality of
-- `IsOraclePPTOn.run_interpret_preprocess_open_of_polyBounded` for `echoHandler`, because each call
-- strictly lengthens the handler state and doubles it in the reply.
example (invariant : ℕ → List Bool → Prop)
    (hinit : ∀ n, invariant n (List.replicate n false))
    (hpres : ∀ n request state, invariant n state →
      ∀ result ∈ OracleComp.support (echoHandler n request state), invariant n result.2)
    (resources : ℕ → List Bool → ℕ) :
    ¬ (∀ (n : ℕ) (request : Unit × List Bool) (state : List Bool),
        invariant n state →
        ∀ result ∈ OracleComp.support (echoHandler n request state),
          result.1.length ≤ resources n request.2) := by
  intro h
  have hreach : ∀ k : ℕ, ∃ state : List Bool, invariant 0 state ∧ k ≤ state.length := by
    intro k
    induction k with
    | zero => exact ⟨[], hinit 0, Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨state, hinv, hk⟩ := ih
      refine ⟨state ++ [true],
        hpres 0 ((), []) state hinv _ (echoHandler_step_mem_support state), ?_⟩
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  obtain ⟨state, hinv, hk⟩ := hreach (resources 0 [] + 1)
  have hle := h 0 ((), []) state hinv _ (echoHandler_step_mem_support state)
  simp only [List.length_append] at hle
  omega

end CslibFrontierTests.OracleSubstitutionGrowth
