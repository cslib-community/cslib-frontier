/-
Copyright (c) 2026 Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

import CslibFrontier.Crypto.Protocols.UC.SFE

/-!
# Tests for Ideal UC Oblivious Transfer and Secure Function Evaluation

Checked witnesses for `CslibFrontier/Crypto/Protocols/UC/ObliviousTransfer.lean` and
`CslibFrontier/Crypto/Protocols/UC/SFE.lean`:
1. `fot` positive delivery, pre-delivery polling (`none`), abort, post-abort `deliver` rejection,
   and repeated-write rejection for both sender `0` and receiver `1`.
2. Sender-hiding (`C = {1}`) and receiver-hiding (`C = {0}`) witnesses, paired with boundary checks
   showing distinguishability when `receiverChoice` is unset (`C = {1}`) or when honest receiver
   `1` is polled post-delivery (`C = {0}`).
3. Self-realization (`Realizes`), lazy multi-session budget and session isolation, and a concrete
   one-message plain-model OT scheme (`trivialPlainOT`) failing `Realizes _ (fot Bool)`.
4. Concrete 2-party (`otSFE`) and 3-party (`xor3SFE`) `fsfe` examples checking honest evaluation,
   abort, repeated-write rejection, early delivery rejection, selective abort, and pre- and
   post-output honest-input privacy.
-/

namespace CslibFrontierTests.Crypto.UCFunctionalities

open Polynomial
open Cslib Cslib.Crypto Cslib.Crypto.Protocols.UC
open scoped NNReal ENNReal

private theorem stateT_map_apply {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (f : α → β) (x : StateT σ m α) (s : σ) :
    (f <$> x) s = (fun p => (f p.1, p.2)) <$> x s :=
  StateT.run_map f x s

/-! ### `fot` delivery, abort, and repeated-write rejection -/

/-- Positive delivery on `fot (Fin 4)`: polling before delivery returns `none`, and polling after
delivery returns `some (.delivered 3)` when `b = true`. -/
example :
    (((fot (Fin 4)).toProtocol 0 ∅).run do
      let _ ← ProbOracleComp.query (Sum.inl ((0 : Fin 2), OTInput.send ⟨1, 3⟩))
      let _ ← ProbOracleComp.query (Sum.inl ((1 : Fin 2), OTInput.choose true))
      let pre ← ProbOracleComp.query (Sum.inl ((1 : Fin 2), OTInput.query))
      let st ← ProbOracleComp.query (Sum.inr OTBackdoor.query)
      let _ ← ProbOracleComp.query (Sum.inr OTBackdoor.deliver)
      let post ← ProbOracleComp.query (Sum.inl ((1 : Fin 2), OTInput.query))
      return (pre, st, post)).eval =
      PMF.pure (none, OTBackdoorReply.status ⟨true, true, false, false⟩,
        some (OTOutput.delivered (3 : Fin 4))) := by
  simp [Machine.run, Machine.link, fot, IdealFunctionality.toProtocol, OTState.status,
    OTState.receiverOutput, OTMessages.select, StateT.run, ProbOracleComp.sample_pure]

/-- Honest execution environment `honestOTEnv` succeeds with probability `1`. -/
example (κ : ℕ) (z : List Bool) :
    (exec (fot (Fin 4)).toProtocol (dummyAdversary 2 _ _) ∅
      (honestOTEnv ⟨(1 : Fin 4), 3⟩ false) κ z).eval = PMF.pure true :=
  eval_exec_honestOTEnv ⟨(1 : Fin 4), 3⟩ false κ z

/-- Abort on `fot`: once `.abort` occurs before delivery, receiver `1` sees `some .aborted`, a
subsequent `.deliver` is ignored, and sender `0` polling `.query` still sees `none`. -/
example :
    (((fot (Fin 4)).toProtocol 0 ∅).run do
      let _ ← ProbOracleComp.query (Sum.inl ((0 : Fin 2), OTInput.send ⟨1, 3⟩))
      let _ ← ProbOracleComp.query (Sum.inl ((1 : Fin 2), OTInput.choose true))
      let _ ← ProbOracleComp.query (Sum.inr OTBackdoor.abort)
      let _ ← ProbOracleComp.query (Sum.inr OTBackdoor.deliver)
      let r₁ ← ProbOracleComp.query (Sum.inl ((1 : Fin 2), OTInput.query))
      let r₀ ← ProbOracleComp.query (Sum.inl ((0 : Fin 2), OTInput.query))
      return (r₁, r₀)).eval =
      PMF.pure (some (OTOutput.aborted : OTOutput (Fin 4)),
        (none : Option (OTOutput (Fin 4)))) := by
  simp [Machine.run, Machine.link, fot, IdealFunctionality.toProtocol, OTState.receiverOutput,
    StateT.run, ProbOracleComp.sample_pure]

/-- Abort execution environment `abortOTEnv` succeeds with probability `1`. -/
example (κ : ℕ) (z : List Bool) :
    (exec (fot (Fin 4)).toProtocol (dummyAdversary 2 _ _) ∅
      (abortOTEnv ⟨(1 : Fin 4), 3⟩ true) κ z).eval = PMF.pure true :=
  eval_exec_abortOTEnv ⟨(1 : Fin 4), 3⟩ true κ z

/-- Repeated-write rejection on `fot`: a second `.send` by sender `0` and a second `.choose` by
receiver `1` are both ignored, so the first inputs prevail. -/
example :
    (((fot (Fin 4)).toProtocol 0 ∅).run do
      let _ ← ProbOracleComp.query (Sum.inl ((0 : Fin 2), OTInput.send ⟨0, 1⟩))
      let _ ← ProbOracleComp.query (Sum.inl ((0 : Fin 2), OTInput.send ⟨2, 3⟩))
      let _ ← ProbOracleComp.query (Sum.inl ((1 : Fin 2), OTInput.choose false))
      let _ ← ProbOracleComp.query (Sum.inl ((1 : Fin 2), OTInput.choose true))
      let _ ← ProbOracleComp.query (Sum.inr OTBackdoor.deliver)
      ProbOracleComp.query (Sum.inl ((1 : Fin 2), OTInput.query))).eval =
      PMF.pure (some (OTOutput.delivered (0 : Fin 4))) := by
  simp [Machine.run, Machine.link, fot, IdealFunctionality.toProtocol, OTState.receiverOutput,
    OTMessages.select, StateT.run, ProbOracleComp.sample_pure]

/-! ### Sender-hiding and receiver-hiding witnesses (plus boundary checks) -/

/-- Sender-hiding witness (`C = {1}`): with `b = false` fixed, changing `m₁` from `1` to `3` leaves
every corrupt-receiver + backdoor program identically distributed. -/
theorem sender_hiding_witness (κ : ℕ) :
    let prog : ProbOracleComp
        (protocolSpec 2 (OTInput (Fin 4)) (OTOutput (Fin 4))
          (RoutedNetQ 2 (OTInput (Fin 4)) OTBackdoor)
          (RoutedNetR (OTOutput (Fin 4)) OTBackdoorReply))
        (Option (OTOutput (Fin 4)) × OTBackdoorReply) := do
      let _ ← ProbOracleComp.query (Sum.inr (.inl ((1 : Fin 2), OTInput.choose true)))
      let _ ← ProbOracleComp.query (Sum.inr (.inr OTBackdoor.deliver))
      let st ← ProbOracleComp.query (Sum.inr (.inr OTBackdoor.query))
      let out ← ProbOracleComp.query (Sum.inr (.inl ((1 : Fin 2), OTInput.query)))
      return (match out with | .inl r => r | .inr _ => none,
              match st with | .inr r => r | .inl _ => .ack)
    (Prod.fst <$> Machine.closeProgram
      ((corruptRouter ({1} : Finset (Fin 2)) ((fot (Fin 4)).toProtocol κ {1})).runFrom prog
        { senderMsgs := some ⟨0, 1⟩, receiverChoice := some false })).eval =
      (Prod.fst <$> Machine.closeProgram
        ((corruptRouter ({1} : Finset (Fin 2)) ((fot (Fin 4)).toProtocol κ {1})).runFrom prog
          { senderMsgs := some ⟨0, 3⟩, receiverChoice := some false })).eval :=
  eval_runFrom_fot_corruptReceiver_eq_of_select_eq κ rfl _ false false

/-- Boundary check for sender hiding: when `receiverChoice` is NOT yet fixed (`none`), corrupt
receiver `1` can choose `true` and distinguish `m₁ = 1` from `m₁ = 3`. -/
example :
    let prog : ProbOracleComp
        (protocolSpec 2 (OTInput (Fin 4)) (OTOutput (Fin 4))
          (RoutedNetQ 2 (OTInput (Fin 4)) OTBackdoor)
          (RoutedNetR (OTOutput (Fin 4)) OTBackdoorReply))
        (RoutedNetR (OTOutput (Fin 4)) OTBackdoorReply) := do
      let _ ← ProbOracleComp.query (Sum.inr (.inl ((1 : Fin 2), OTInput.choose true)))
      let _ ← ProbOracleComp.query (Sum.inr (.inr OTBackdoor.deliver))
      ProbOracleComp.query (Sum.inr (.inl ((1 : Fin 2), OTInput.query)))
    (Prod.fst <$> Machine.closeProgram
      ((corruptRouter ({1} : Finset (Fin 2)) ((fot (Fin 4)).toProtocol 0 {1})).runFrom prog
        { senderMsgs := some ⟨0, 1⟩, receiverChoice := none })).eval ≠
      (Prod.fst <$> Machine.closeProgram
        ((corruptRouter ({1} : Finset (Fin 2)) ((fot (Fin 4)).toProtocol 0 {1})).runFrom prog
          { senderMsgs := some ⟨0, 3⟩, receiverChoice := none })).eval := by
  intro prog h
  have h1 : (Prod.fst <$> Machine.closeProgram
      ((corruptRouter ({1} : Finset (Fin 2)) ((fot (Fin 4)).toProtocol 0 {1})).runFrom prog
        { senderMsgs := some ⟨0, 1⟩, receiverChoice := none })).eval =
      PMF.pure (Sum.inl (some (OTOutput.delivered (1 : Fin 4)))) := by
    simp [prog, corruptRouter, IdealFunctionality.toProtocol, fot, OTState.receiverOutput,
      OTMessages.select, StateT.run, stateT_map_apply, ProbOracleComp.sample_pure]
  have h3 : (Prod.fst <$> Machine.closeProgram
      ((corruptRouter ({1} : Finset (Fin 2)) ((fot (Fin 4)).toProtocol 0 {1})).runFrom prog
        { senderMsgs := some ⟨0, 3⟩, receiverChoice := none })).eval =
      PMF.pure (Sum.inl (some (OTOutput.delivered (3 : Fin 4)))) := by
    simp [prog, corruptRouter, IdealFunctionality.toProtocol, fot, OTState.receiverOutput,
      OTMessages.select, StateT.run, stateT_map_apply, ProbOracleComp.sample_pure]
  rw [h1, h3] at h
  have hEq : (Sum.inl (some (OTOutput.delivered (1 : Fin 4))) :
      RoutedNetR (OTOutput (Fin 4)) OTBackdoorReply) =
      Sum.inl (some (OTOutput.delivered (3 : Fin 4))) := by
    have := congrArg (· (Sum.inl (some (OTOutput.delivered (1 : Fin 4))))) h
    simp [PMF.pure_apply] at this
  cases hEq

/-- Receiver-hiding witness (`C = {0}`): across party-`0` and backdoor queries, receiver `1`'s
choice bit `false` vs. `true` induces identical distributions. -/
theorem receiver_hiding_witness (κ : ℕ) :
    let netProg : ProbOracleComp
        (netSpec (RoutedNetQ 2 (OTInput (Fin 4)) OTBackdoor)
          (RoutedNetR (OTOutput (Fin 4)) OTBackdoorReply))
        (OTBackdoorReply × OTBackdoorReply) := do
      let st₀ ← ProbOracleComp.query (Sum.inr OTBackdoor.query)
      let _ ← ProbOracleComp.query (Sum.inl ((0 : Fin 2), OTInput.send ⟨0, 1⟩))
      let _ ← ProbOracleComp.query (Sum.inr OTBackdoor.deliver)
      let st₁ ← ProbOracleComp.query (Sum.inr OTBackdoor.query)
      return (match st₀ with | .inr r => r | .inl _ => .ack,
              match st₁ with | .inr r => r | .inl _ => .ack)
    (Prod.fst <$> Machine.closeProgram
      ((corruptRouter ({0} : Finset (Fin 2)) ((fot (Fin 4)).toProtocol κ {0})).runFrom
        (liftNet netProg) { receiverChoice := some false })).eval =
      (Prod.fst <$> Machine.closeProgram
        ((corruptRouter ({0} : Finset (Fin 2)) ((fot (Fin 4)).toProtocol κ {0})).runFrom
          (liftNet netProg) { receiverChoice := some true })).eval :=
  eval_runFrom_fot_corruptSender_flip κ false _
    { senderMsgs := none, delivered := false, aborted := false }

/-- Boundary check for receiver hiding: if honest receiver `1` is queried on the party port after
delivery (`Sum.inl (1, .query)`), then `b = false` and `b = true` produce distinct outputs when
`m₀ ≠ m₁`. -/
example :
    let prog : ProbOracleComp
        (protocolSpec 2 (OTInput (Fin 4)) (OTOutput (Fin 4))
          (RoutedNetQ 2 (OTInput (Fin 4)) OTBackdoor)
          (RoutedNetR (OTOutput (Fin 4)) OTBackdoorReply))
        (Option (OTOutput (Fin 4))) := do
      let _ ← ProbOracleComp.query (Sum.inr (.inl ((0 : Fin 2), OTInput.send ⟨0, 1⟩)))
      let _ ← ProbOracleComp.query (Sum.inr (.inr OTBackdoor.deliver))
      ProbOracleComp.query (Sum.inl ((1 : Fin 2), OTInput.query))
    (Prod.fst <$> Machine.closeProgram
      ((corruptRouter ({0} : Finset (Fin 2)) ((fot (Fin 4)).toProtocol 0 {0})).runFrom prog
        { receiverChoice := some false })).eval ≠
      (Prod.fst <$> Machine.closeProgram
        ((corruptRouter ({0} : Finset (Fin 2)) ((fot (Fin 4)).toProtocol 0 {0})).runFrom prog
          { receiverChoice := some true })).eval := by
  intro prog h
  have h0 : (Prod.fst <$> Machine.closeProgram
      ((corruptRouter ({0} : Finset (Fin 2)) ((fot (Fin 4)).toProtocol 0 {0})).runFrom prog
        { receiverChoice := some false })).eval =
      PMF.pure (some (OTOutput.delivered (0 : Fin 4))) := by
    simp [prog, corruptRouter, IdealFunctionality.toProtocol, fot, OTState.receiverOutput,
      OTMessages.select, StateT.run, stateT_map_apply, ProbOracleComp.sample_pure]
  have h1 : (Prod.fst <$> Machine.closeProgram
      ((corruptRouter ({0} : Finset (Fin 2)) ((fot (Fin 4)).toProtocol 0 {0})).runFrom prog
        { receiverChoice := some true })).eval =
      PMF.pure (some (OTOutput.delivered (1 : Fin 4))) := by
    simp [prog, corruptRouter, IdealFunctionality.toProtocol, fot, OTState.receiverOutput,
      OTMessages.select, StateT.run, stateT_map_apply, ProbOracleComp.sample_pure]
  rw [h0, h1] at h
  have hEq : (some (OTOutput.delivered (0 : Fin 4)) : Option (OTOutput (Fin 4))) =
      some (OTOutput.delivered (1 : Fin 4)) := by
    have := congrArg (· (some (OTOutput.delivered (0 : Fin 4)))) h
    simp [PMF.pure_apply] at this
  cases hEq

/-! ### Self-realization, multi-session isolation, and plain-model impossibility -/

example : Realizes (fot (Fin 4)).toProtocol (fot (Fin 4)) := Emulates.refl _

/-- Monotonicity check for `fot`: starting with `senderMsgs := some ⟨0, 1⟩`, any reachable
post-execution state locks `senderMsgs` to `some ⟨0, 1⟩`. -/
example (prog : ProbOracleComp
      (protocolSpec 2 (OTInput (Fin 4)) (OTOutput (Fin 4))
        (RoutedNetQ 2 (OTInput (Fin 4)) OTBackdoor)
        (RoutedNetR (OTOutput (Fin 4)) OTBackdoorReply)) Unit)
    {x : Unit × OTState (Fin 4)}
    (hx : x ∈ (Machine.closeEval
      ((corruptRouter ∅ ((fot (Fin 4)).toProtocol 0 ∅)).runFrom prog
        { senderMsgs := some ⟨0, 1⟩ })).support) :
    x.2.senderMsgs = some ⟨0, 1⟩ :=
  (OTState.monotone_of_mem_support_runFrom 0 ∅ prog { senderMsgs := some ⟨0, 1⟩ }
    hx).senderMsgs_lock ⟨0, 1⟩ rfl

example : ((fot Bool).multiSession (Fin 2)).toProtocol.PolyBounded 0 :=
  fot_multiSession_polyBounded Bool (Fin 2)

/-- Lazy multi-session `fot`: delivering session `0` leaves session `1` independent and idle. -/
example :
    ((((fot Bool).multiSession (Fin 2)).toProtocol 0 ∅).run do
      let _ ← ProbOracleComp.query (Sum.inl ((0 : Fin 2), ⟨0, OTInput.send ⟨false, true⟩⟩))
      let _ ← ProbOracleComp.query (Sum.inl ((1 : Fin 2), ⟨0, OTInput.choose true⟩))
      let _ ← ProbOracleComp.query (Sum.inr ⟨0, OTBackdoor.deliver⟩)
      let s₀ ← ProbOracleComp.query (Sum.inl ((1 : Fin 2), ⟨0, OTInput.query⟩))
      let s₁ ← ProbOracleComp.query (Sum.inl ((1 : Fin 2), ⟨1, OTInput.query⟩))
      return (s₀, s₁)).eval =
      PMF.pure (some (OTOutput.delivered true), (none : Option (OTOutput Bool))) := by
  simp [Machine.run, Machine.link, IdealFunctionality.multiSession, IdealFunctionality.toProtocol,
    fot, OTState.receiverOutput, OTMessages.select, StateT.run, ProbOracleComp.sample_pure,
    Function.update_self, Function.update_of_ne]

/-- Trivial one-message plain-model OT scheme sending `(m₀, m₁)` in the clear. -/
def trivialPlainOT : PlainSenderOT (Bool × Bool) where
  send _ m₀ m₁ := pure (m₀, m₁)
  recv _ c b := pure (if b then c.2 else c.1)

theorem trivialPlainOT_isPolyBounded : trivialPlainOT.IsPolyBounded 0 0 where
  send κ m₀ m₁ := by
    rw [Polynomial.eval_zero]
    exact OracleComp.IsCostBounded.pure _ 0
  recv κ c b := by
    rw [Polynomial.eval_zero]
    exact OracleComp.IsCostBounded.pure _ 0

theorem trivialPlainOT_acceptProb (κ : ℕ) (b : Bool) :
    trivialPlainOT.acceptProb κ b = 1 := by
  have h : (2 : ℝ≥0∞).toNNReal * (2 : ℝ≥0∞).toNNReal⁻¹ = 1 := by
    rw [mul_inv_cancel₀]
    simp [ENNReal.toNNReal_eq_zero_iff]
  cases b <;>
    simp [PlainSenderOT.acceptProb, PlainSenderOT.acceptGame, trivialPlainOT,
      Game.succProbability, ProbComp.eval_bind, PMF.bind_const, h]

/-- `trivialPlainOT` is perfectly complete, yet cannot UC-realize `fot Bool`. -/
theorem not_realizes_trivialPlainOT : ¬ Realizes trivialPlainOT.toProtocol (fot Bool) := by
  refine not_realizes_fot_of_plainSenderOT (pR := 0) trivialPlainOT_isPolyBounded.2
    (c := (1 / 2 : ℝ≥0)) (by norm_num) (Filter.Eventually.of_forall fun κ => ?_)
  rw [trivialPlainOT_acceptProb, trivialPlainOT_acceptProb]
  norm_num

/-! ### `fsfe`: 2-party `otSFE` and 3-party `xor3SFE` examples -/

/-- Honest 2-party OT via `otInSFEHybrid` over `otSFE (Fin 4)` succeeds with probability `1`. -/
example (κ : ℕ) (z : List Bool) :
    (exec (compose (otInSFEHybrid (Fin 4)) (otSFE (Fin 4)).toProtocol)
      (dummyAdversary 2 _ _) ∅ (honestOTInSFEEnv ⟨(1 : Fin 4), 3⟩ true) κ z).eval =
      PMF.pure true :=
  eval_exec_otInSFE_honestOT ⟨(1 : Fin 4), 3⟩ true κ z

/-- Abort in 2-party OT via `otInSFEHybrid` over `otSFE (Fin 4)` succeeds with probability `1`. -/
example (κ : ℕ) (z : List Bool) :
    (exec (compose (otInSFEHybrid (Fin 4)) (otSFE (Fin 4)).toProtocol)
      (dummyAdversary 2 _ _) ∅ (abortOTInSFEEnv ⟨(1 : Fin 4), 3⟩ false) κ z).eval =
      PMF.pure true :=
  eval_exec_otInSFE_abortOT ⟨(1 : Fin 4), 3⟩ false κ z

/-- Semantic difference witness: selective `.deliver 0` followed by `.abort` in `otSFE`. -/
example :
    (((otSFE (Fin 4)).toProtocol 0 ∅).run do
      let _ ← ProbOracleComp.query (Sum.inl ((0 : Fin 2), .input (.inl ⟨1, 3⟩)))
      let _ ← ProbOracleComp.query (Sum.inl ((1 : Fin 2), .input (.inr true)))
      let _ ← ProbOracleComp.query (Sum.inr (SFEBackdoor.deliver 0))
      let r₁Before ← ProbOracleComp.query (Sum.inl ((1 : Fin 2), .query))
      let _ ← ProbOracleComp.query (Sum.inr SFEBackdoor.abort)
      let r₀After ← ProbOracleComp.query (Sum.inl ((0 : Fin 2), .query))
      let r₁After ← ProbOracleComp.query (Sum.inl ((1 : Fin 2), .query))
      return (r₁Before, r₀After, r₁After)).eval =
      PMF.pure (none, some (.output (.inl ())), some .aborted) :=
  otSFE_selective_deliver_zero ⟨(1 : Fin 4), 3⟩ true 0

/-- 3-party Boolean XOR function `x ↦ (x₀ ⊕ x₁ ⊕ x₂)` given to every party. -/
def xor3Fn (x : Fin 3 → Bool) : Fin 3 → Bool := fun _ => x 0 ^^ x 1 ^^ x 2

/-- 3-party SFE for `xor3Fn`: honest evaluation delivers `x 0 ^^ x 1 ^^ x 2` to party `2`. -/
example (x : Fin 3 → Bool) (κ : ℕ) (z : List Bool) :
    (exec (fsfe xor3Fn).toProtocol (dummyAdversary 3 _ _) ∅
      (honestSFEEnv xor3Fn x 2) κ z).eval = PMF.pure true :=
  eval_exec_honestSFEEnv xor3Fn x 2 κ z

/-- 3-party SFE for `xor3Fn`: abort delivers `some .aborted` to party `1`. -/
example (x : Fin 3 → Bool) (κ : ℕ) (z : List Bool) :
    (exec (fsfe xor3Fn).toProtocol (dummyAdversary 3 _ _) ∅
      (abortSFEEnv x 1) κ z).eval = PMF.pure true :=
  eval_exec_abortSFEEnv xor3Fn x 1 κ z

/-- 3-party `fsfe`: early `.deliver 0` before all 3 submit is ignored, and repeated `.input` by
party `1` is rejected (`x = ![true, false, false]`, not `![true, true, false]`). -/
example :
    (((fsfe xor3Fn).toProtocol 0 ∅).run do
      let _ ← ProbOracleComp.query (Sum.inl ((0 : Fin 3), SFEInput.input true))
      let _ ← ProbOracleComp.query (Sum.inl ((1 : Fin 3), SFEInput.input false))
      let _ ← ProbOracleComp.query (Sum.inl ((1 : Fin 3), SFEInput.input true))
      let _ ← ProbOracleComp.query (Sum.inr (SFEBackdoor.deliver 0))
      let early ← ProbOracleComp.query (Sum.inl ((0 : Fin 3), SFEInput.query))
      let _ ← ProbOracleComp.query (Sum.inl ((2 : Fin 3), SFEInput.input false))
      let _ ← ProbOracleComp.query (Sum.inr (SFEBackdoor.deliver 0))
      let final ← ProbOracleComp.query (Sum.inl ((0 : Fin 3), SFEInput.query))
      return (early, final)).eval =
      PMF.pure (none, some (SFEOutput.output true)) := by
  simp [Machine.run, Machine.link, fsfe, IdealFunctionality.toProtocol, SFEState.allSubmitted,
    SFEState.partyOutput, SFEState.eval?, xor3Fn, StateT.run, ProbOracleComp.sample_pure,
    Fin.forall_fin_succ, Function.update_self, Function.update_of_ne]

/-- 3-party honest-input privacy witness (`C = {0}`): two input vectors `![false, false, true]` and
`![false, true, false]` agreeing on `C = {0}` and having the same XOR `true` produce identical
corrupt-party and backdoor behavior even after `.deliver 0`. -/
theorem xor3_post_output_privacy_witness (κ : ℕ) :
    let x₁ : Fin 3 → Bool := ![false, false, true]
    let x₂ : Fin 3 → Bool := ![false, true, false]
    let netProg : ProbOracleComp
        (netSpec (RoutedNetQ 3 (SFEInput Bool) (SFEBackdoor 3))
          (RoutedNetR (SFEOutput Bool) (SFEBackdoorReply 3)))
        (Option (SFEOutput Bool)) := do
      let _ ← ProbOracleComp.query (Sum.inr (SFEBackdoor.deliver 0))
      let out ← ProbOracleComp.query (Sum.inl ((0 : Fin 3), SFEInput.query))
      return match out with | .inl r => r | .inr _ => none
    (Prod.fst <$> Machine.closeProgram
      ((corruptRouter ({0} : Finset (Fin 3)) ((fsfe xor3Fn).toProtocol κ {0})).runFrom
        (liftNet netProg) { inputs := fun i => some (x₁ i) })).eval =
      (Prod.fst <$> Machine.closeProgram
        ((corruptRouter ({0} : Finset (Fin 3)) ((fsfe xor3Fn).toProtocol κ {0})).runFrom
          (liftNet netProg) { inputs := fun i => some (x₂ i) })).eval := by
  refine eval_runFrom_fsfe_corrupt_inputs_eq ({0} : Finset (Fin 3)) xor3Fn κ
    (fun i hi => by simp only [Finset.mem_singleton] at hi; subst hi; rfl)
    (fun i hi => by simp only [Finset.mem_singleton] at hi; subst hi; rfl)
    (fun _ => false) false _

/-- 3-party pre-output privacy witness (`C = {0}`): when party `2` has not yet submitted,
honest party `1`'s input (`false` vs. `true`) is completely hidden from `C = {0}` and the
backdoor, even if the adversary attempts `.deliver 0`. -/
theorem xor3_pre_allSubmitted_privacy_witness (κ : ℕ) :
    let s₁ : SFEState 3 Bool := { inputs := ![some false, some false, none] }
    let s₂ : SFEState 3 Bool := { inputs := ![some false, some true, none] }
    let netProg : ProbOracleComp
        (netSpec (RoutedNetQ 3 (SFEInput Bool) (SFEBackdoor 3))
          (RoutedNetR (SFEOutput Bool) (SFEBackdoorReply 3)))
        (Option (SFEOutput Bool)) := do
      let _ ← ProbOracleComp.query (Sum.inr (SFEBackdoor.deliver 0))
      let out ← ProbOracleComp.query (Sum.inl ((0 : Fin 3), SFEInput.query))
      return match out with | .inl r => r | .inr _ => none
    (Prod.fst <$> Machine.closeProgram
      ((corruptRouter ({0} : Finset (Fin 3)) ((fsfe xor3Fn).toProtocol κ {0})).runFrom
        (liftNet netProg) s₁)).eval =
      (Prod.fst <$> Machine.closeProgram
        ((corruptRouter ({0} : Finset (Fin 3)) ((fsfe xor3Fn).toProtocol κ {0})).runFrom
          (liftNet netProg) s₂)).eval := by
  refine eval_runFrom_fsfe_corrupt_preAllSubmitted_eq ({0} : Finset (Fin 3)) xor3Fn κ
    ⟨fun i hi => by simp only [Finset.mem_singleton] at hi; subst hi; rfl,
     fun i => by fin_cases i <;> rfl,
     fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl⟩
    ⟨2, by decide, rfl⟩ _

/-- Monotonicity check for `fsfe`: once party `0` submits `true`, any reachable post-execution state
preserves `inputs 0 = some true`. -/
example (prog : ProbOracleComp
      (protocolSpec 3 (SFEInput Bool) (SFEOutput Bool)
        (RoutedNetQ 3 (SFEInput Bool) (SFEBackdoor 3))
        (RoutedNetR (SFEOutput Bool) (SFEBackdoorReply 3))) Unit)
    {x : Unit × SFEState 3 Bool}
    (hx : x ∈ (Machine.closeEval
      ((corruptRouter ∅ ((fsfe xor3Fn).toProtocol 0 ∅)).runFrom prog
        { inputs := ![some true, none, none] })).support) :
    x.2.inputs 0 = some true :=
  (SFEState.monotone_of_mem_support_runFrom xor3Fn 0 ∅ prog
    { inputs := ![some true, none, none] } hx).inputs_lock 0 true rfl

end CslibFrontierTests.Crypto.UCFunctionalities
