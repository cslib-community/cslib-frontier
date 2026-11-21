/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveStream

/-! # Native fixed-arity gates between a carry-save traversal and its leaf continuations -/

public section
namespace Turing.MultiTapeATM.CarrySaveGate

open MultiTapeTM Cslib Cslib.BitString Cslib.Circuits.Boolean.CarrySaveQuery

variable {k w : ℕ} {S : Type} (gate : (Fin 7 → Bool) → Bool)
  (child : Fin 7 → Bool → Bool → MultiTapeATM (k + 6) Bool S)

/-- The selected port receives the carry flag and one claimed bit. -/
@[expose] noncomputable def machine (carry claim : Bool) :=
  TruthTable.machine gate claim (fun j b => child j carry b)

/-- The truth-table check adds ten steps and calls one continuation per path. -/
theorem bound {time budget : ℕ} {input : List Bool} {scratch : CarrySaveStream.Scratch k}
    (h : ∀ j, CarrySaveStream.LeafBound (child j) time budget input scratch) :
    CarrySaveStream.LeafBound (machine gate child) (time + 10) budget input scratch := by
  intro ht bits path unary front status carry claim hf hb
  let cfg := (CarrySaveStream.config (input := input) (scratch := scratch)
    ht bits path unary front status).withState (none : Option S)
  exact TruthTable.haltsWithin gate claim (fun j b => child j carry b) time cfg
    fun j b => h j ht bits path unary front status carry b hf hb

/-- Real physical operand leaves suffice for the desired gate value on arbitrary configurations
of the persistent traversal, including padded paths. -/
theorem correct (parts : Fin 7 → List Bool → BitString (w + w))
    (target : List Bool → BitString (w + w))
    (op : ∀ (path : List Bool) (carry : Bool) (i : Fin w),
      value target ⟨path, 0, carry, i.val⟩ =
        gate (fun j => value (parts j) ⟨path, 0, carry, i.val⟩))
    {time budget : ℕ} {input : List Bool} {scratch : CarrySaveStream.Scratch k}
    (h : ∀ j, CarrySaveStream.LeafCorrect (parts j) (child j) time budget input scratch) :
    CarrySaveStream.LeafCorrect target (machine gate child) (time + 10) budget input scratch := by
  intro ht bits path unary front status carry claim hf hb hi
  let cfg := (CarrySaveStream.config (input := input) (scratch := scratch)
    ht bits path unary front status).withState (none : Option S)
  let val (j : Fin 7) := value (parts j) ⟨path, 0, carry, lsbValue bits⟩
  have hh := TruthTable.acceptsWithin_eval gate claim (fun j b => child j carry b)
    time cfg (by simp [cfg]) val (fun j b => h j ht bits path unary front status carry b hf hb hi)
  rw [op path carry ⟨_, hi⟩]
  exact hh

end Turing.MultiTapeATM.CarrySaveGate
