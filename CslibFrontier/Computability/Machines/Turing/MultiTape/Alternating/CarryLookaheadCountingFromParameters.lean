/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCountingPrepare
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.Prepend

/-!
# Native count bits from raw parameters

One fixed finite alternating machine constructs every derived count and finishing-adder field
from a raw parameter word before running the ordinary-count evaluator. Its separate context word
is preserved by initialization. The clock includes the actual deterministic prefix and the full
alternating continuation; supplying or constructing the context remains an explicit boundary.
-/

public section

namespace Turing.MultiTapeATM.CarryLookaheadCountingFromParameters

open MultiTapeTM Cslib.Circuits.Boolean.CarryLookahead.Query

/-- The exact initialization charge added to any certified evaluator clock. -/
@[expose] def clockOfEvaluator (cInit dInit : ℕ) (a : CountingInput.Input)
    (evaluationTime : ℕ) : ℕ :=
  cInit * ((CountingInput.encInput a).length + 1) ^ dInit + evaluationTime

/-- Preparation of the short parameter record followed by the complete native count evaluator. -/
@[expose] def clock (cInit dInit c d cRoot dRoot : ℕ) (context : List Bool)
    (a : CountingInput.Input) : ℕ :=
  clockOfEvaluator cInit dInit a
    (CarryLookaheadCounting.clock c d cRoot dRoot context a.count a.query.width)

/-- Install the native counting layout for an arbitrary alternating continuation. Its semantics
and branch clock are preserved, so the same initializer serves sums and reduced products. -/
theorem exists_prepend {k r q : ℕ} {S : Type} [Finite S]
    (evaluator : MultiTapeATM (CarryLookaheadCountingLayout.size k r q) Bool S) :
    ∃ (scratch : ℕ) (Q : Type) (_ : Finite Q)
      (atm : MultiTapeATM (CarryLookaheadCountingPrepare.size scratch k r q) Bool Q)
      (cInit dInit : ℕ),
      ∀ (input context : List Bool) (a : CountingInput.Input) (evaluationTime : ℕ),
        let cfg := (CarryLookaheadCounting.initial k r q input context a.count a.query.width
          a.query.bit a.query.claim).withState (some evaluator.toPTM.initial)
        let start := (CarryLookaheadCountingPrepare.initial scratch k r q input context a).withState
          (some atm.toPTM.initial)
        evaluator.HaltsWithin evaluationTime cfg →
          atm.HaltsWithin (clockOfEvaluator cInit dInit a evaluationTime) start ∧
          (atm.AcceptsWithin (clockOfEvaluator cInit dInit a evaluationTime) start ↔
            evaluator.AcceptsWithin evaluationTime cfg) := by
  obtain ⟨scratch, P, hP, prepare, cInit, dInit, hprepare⟩ :=
    CarryLookaheadCountingPrepare.exists_prepare k r q
  let : Finite P := hP
  let e := CarryLookaheadCountingPrepare.evaluatorTapes scratch k r q
  let leaf := evaluator.extendTapes e
  let atm := prependTM prepare leaf
  refine ⟨scratch, _, inferInstance, atm, cInit, dInit, ?_⟩
  intro input context a evaluationTime cfg start hh
  let storage := CarryLookaheadCountingPrepare.initial scratch k r q input context a
  let finish := CarryLookaheadCountingPrepare.config scratch k r q input context a
    (CarryLookaheadCountingInitialLayout.canonical a)
  have hv : viewCfg e (finish.withState (some leaf.toPTM.toNTM.q₀)) =
      cfg := by
    change (viewCfg e finish).withState (some evaluator.toPTM.initial) = _
    rw [CarryLookaheadCountingPrepare.view_prepared]
  have hl : leaf.HaltsWithin evaluationTime
      (finish.withState (some leaf.toPTM.toNTM.q₀)) := by
    rw [haltsWithin_extendTapes_iff, hv]
    exact hh
  have hspec := prependTM_spec prepare leaf storage finish
    (cInit * ((CountingInput.encInput a).length + 1) ^ dInit)
    evaluationTime
    (hprepare input context a) hl
  refine ⟨hspec.1, hspec.2.trans ?_⟩
  rw [acceptsWithin_extendTapes_iff, hv]

/-- One finite native ATM answers ordinary count bits from only context and raw parameters.
No binary height, unary frontier, routing metadata, control header, or status is supplied. -/
theorem exists_evaluator (predicate : List Bool × ℕ → Bool)
    (hp : ComputableInPolyTime predicate (encPair encBits encNat) encBool) :
    ∃ (scratch k r q : ℕ) (S : Type) (_ : Finite S)
      (atm : MultiTapeATM (CarryLookaheadCountingPrepare.size scratch k r q) Bool S)
      (cInit dInit c d cRoot dRoot : ℕ),
      ∀ (input context : List Bool) (n w : ℕ) (bit : Fin w) (claim : Bool),
        let a : CountingInput.Input := ⟨n, ⟨w, bit.val, claim⟩⟩
        let start := (CarryLookaheadCountingPrepare.initial scratch k r q input context a).withState
          (some atm.toPTM.initial)
        atm.HaltsWithin (clock cInit dInit c d cRoot dRoot context a) start ∧
          (atm.AcceptsWithin (clock cInit dInit c d cRoot dRoot context a) start ↔
            Cslib.Circuits.Boolean.CarrySaveQuery.Counting.count n w
              (fun j => predicate (context, j)) bit = claim) := by
  obtain ⟨k, r, q, S, hS, evaluator, c, d, cRoot, dRoot, hevaluator⟩ :=
    CarryLookaheadCounting.exists_evaluator predicate hp
  let : Finite S := hS
  obtain ⟨scratch, Q, hQ, atm, cInit, dInit, h⟩ :=
    exists_prepend evaluator
  refine ⟨scratch, k, r, q, Q, hQ, atm, cInit, dInit, c, d, cRoot, dRoot, ?_⟩
  intro input context n w bit claim
  obtain ⟨hh, ha⟩ := hevaluator input context n w bit claim
  obtain ⟨hh', ha'⟩ := h input context ⟨n, ⟨w, bit.val, claim⟩⟩
    (CarryLookaheadCounting.clock c d cRoot dRoot context n w) hh
  exact ⟨hh', ha'.trans ha⟩

end Turing.MultiTapeATM.CarryLookaheadCountingFromParameters
