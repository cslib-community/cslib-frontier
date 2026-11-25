/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.TreeEval.Ary.Packed.QueryGateSpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatPow

/-!
# Charged initialization of the same-input interpolation loop

The alphabet size and coordinate count determine the assignment limit. This initialization
computes that power in native space, charging its possible binary output length in addition to
the supplied context, interpolation point and parameters. The limit is not a free input oracle.

## Main definitions

* `Cslib.TreeEval.Ary.Packed.QueryGate.Input`,
  `Cslib.TreeEval.Ary.Packed.QueryGate.encInput`: uninitialized interpolation inputs and their
  binary encoding.
* `Cslib.TreeEval.Ary.Packed.QueryGate.Input.gridParams`,
  `Cslib.TreeEval.Ary.Packed.QueryGate.Input.alphabet`,
  `Cslib.TreeEval.Ary.Packed.QueryGate.Input.coords`,
  `Cslib.TreeEval.Ary.Packed.QueryGate.Input.point`: named components of `Input`.
* `Cslib.TreeEval.Ary.Packed.QueryGate.prepare`,
  `Cslib.TreeEval.Ary.Packed.QueryGate.initializationSpace`: grid-limit preparation and its native
  space budget.

## Main results

* `Cslib.TreeEval.Ary.Packed.QueryGate.prepare_inSpace`,
  `Cslib.TreeEval.Ary.Packed.QueryGate.initial_prepare_inSpace`: native space certificates for
  computing the grid limit and initializing fresh loop counters.
-/

public section

namespace Cslib.TreeEval.Ary.Packed.QueryGate

open Turing MultiTapeTM ComputableInSpace Reader

/-- Supplier context, modulus/alphabet/coordinate parameters, and the interpolation point. -/
abbrev Input (γ : Type) := γ × (ℕ × ℕ × ℕ) × List ℕ

/-- The original parameters without a precomputed assignment limit. -/
abbrev encInput {γ : Type} (encG : γ ↪ List Bool) : Input γ ↪ List Bool :=
  encPair encG (encPair encNat3 (encList encNat))

/-- The `(p, s, n)` modulus, alphabet-size, and coordinate-count triple of `Input`. -/
abbrev Input.gridParams {γ : Type} (q : Input γ) : ℕ × ℕ × ℕ := q.2.1

/-- The alphabet size `s` of `Input`. -/
abbrev Input.alphabet {γ : Type} (q : Input γ) : ℕ := q.2.1.2.1

/-- The coordinate count `n` of `Input`. -/
abbrev Input.coords {γ : Type} (q : Input γ) : ℕ := q.2.1.2.2

/-- The interpolation point of `Input`. -/
abbrev Input.point {γ : Type} (q : Input γ) : List ℕ := q.2.2

/-- Compute the full grid limit, retaining the supplied parameters. -/
@[expose] def prepare {γ : Type} (q : Input γ) : Params γ :=
  (q.1, Input.gridParams q, Input.point q, Input.alphabet q ^ Input.coords q)

/-- Input storage and the possible binary size of the assignment limit. -/
@[expose] def initializationSpace {γ : Type} (encG : γ ↪ List Bool) (q : Input γ) : ℕ :=
  (encInput encG q).length + (Input.coords q + 1) * (encNat (Input.alphabet q)).length +
    (encNat (Input.coords q)).length + 1

/-- The actual grid limit can be computed without a unary space charge for the alphabet size. -/
theorem prepare_inSpace {γ : Type} (encG : γ ↪ List Bool) :
    ComputableInSpace prepare (encInput encG) (encParams encG)
      (initializationSpace encG) := by
  have hin : (fun q : Input γ => (encInput encG q).length) ≼ initializationSpace encG :=
    .of_le fun q => by simp only [initializationSpace]; omega
  have hctx := (fst encG (encPair encNat3 (encList encNat))).weaken hin
  have hrest := (snd encG (encPair encNat3 (encList encNat))).weaken hin
  have hpsn := fst' hrest
  have hpoint := snd' hrest
  have hs := fst' (snd' hpsn)
  have hn := snd' (snd' hpsn)
  have hlimit := budget_natPow_variable hs hn
    (show (fun q : Input γ => (Input.coords q + 1) * (encNat (Input.alphabet q)).length +
      (encNat (Input.coords q)).length + 1) ≼ initializationSpace encG from
      .of_le fun q => by simp only [initializationSpace]; omega)
  exact (budget_prod hctx (budget_prod hpsn (budget_prod hpoint hlimit))).of_enc_eq
    fun _ => rfl

/-- Fresh counters are initialized after the charged power computation. -/
theorem initial_prepare_inSpace {γ : Type} (encG : γ ↪ List Bool) :
    ComputableInSpace (fun q : Input γ => initial (prepare q)) (encInput encG)
      (encState encG) (initializationSpace encG) := by
  have hin : (fun q : Input γ => (encInput encG q).length) ≼ initializationSpace encG :=
    .of_le fun q => by simp only [initializationSpace]; omega
  exact budget_prod (prepare_inSpace encG)
    (budget_prod (budget_const 0) (budget_const 0))

/-- Preparing parameters sets the assignment limit to `s ^ n`. -/
@[simp] theorem prepare_limit {γ : Type} (q : Input γ) :
    Params.limit (prepare q) = Params.alphabet (prepare q) ^ Params.coords (prepare q) := rfl

end Cslib.TreeEval.Ary.Packed.QueryGate
