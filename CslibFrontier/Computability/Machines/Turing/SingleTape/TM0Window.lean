/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.SingleTape.TM0Restrict

/-!
# Finite tape windows for Mathlib Post–Turing machines

A window records the finite tape cells on both sides of the head. Moving past its ends has no
successor. Interior moves and writes use the original `TM0.Machine`, and keep the window length.

## Main definitions

* `Turing.TM0Window.Cfg`: finite control, scanned cell and two nearest-first tape lists.
* `Turing.TM0Window.step`: the original transition stopped at the window boundary.

## Main results

* `Turing.TM0Window.step_size`: every window transition preserves its number of cells.
* `Turing.TM0Window.step_native`: every window transition is a transition of the original machine.
-/

public section

namespace Turing.TM0Window

open Turing

/-- A finite tape window, with the nearest left cell first. -/
structure Cfg (Γ Q : Type*) where
  /-- Finite-control state. -/
  state : Q
  /-- Symbol currently scanned. -/
  scanned : Γ
  /-- Cells to the left, nearest first. -/
  left : List Γ
  /-- Cells to the right, nearest first. -/
  right : List Γ
  deriving DecidableEq

variable {Γ Q : Type*}

/-- The number of represented cells, including the scanned cell. -/
@[expose] def Cfg.size (c : Cfg Γ Q) : ℕ := c.left.length + c.right.length + 1

variable [Inhabited Q]

/-- The original machine step, stopped at the two ends of the supplied window. -/
@[expose] def step (M : TM0.Machine Γ Q) (c : Cfg Γ Q) : Option (Cfg Γ Q) :=
  match M c.state c.scanned with
  | none => none
  | some (q, .write b) => some ⟨q, b, c.left, c.right⟩
  | some (q, .move .left) =>
      match c.left with
      | [] => none
      | b :: L => some ⟨q, b, L, c.scanned :: c.right⟩
  | some (q, .move .right) =>
      match c.right with
      | [] => none
      | b :: R => some ⟨q, b, c.scanned :: c.left, R⟩

/-- Writing or moving within the window retains exactly its original number of cells. -/
theorem step_size {M : TM0.Machine Γ Q} {c d : Cfg Γ Q} (h : step M c = some d) :
    d.size = c.size := by
  rcases c with ⟨q, a, L, R⟩
  unfold step at h
  rcases hM : M q a with _ | ⟨q', (_ | _) | b⟩ <;> simp only [hM, reduceCtorEq] at h
  · cases L with
    | nil => contradiction
    | cons b L =>
      cases h
      simp only [Cfg.size, List.length_cons]
      omega
  · cases R with
    | nil => contradiction
    | cons b R =>
      cases h
      simp only [Cfg.size, List.length_cons]
      omega
  · cases h
    rfl

/-- The window size is invariant on the entire computation. -/
theorem reaches_size {M : TM0.Machine Γ Q} {c d : Cfg Γ Q}
    (hr : StateTransition.Reaches (step M) c d) : d.size = c.size := by
  induction hr with
  | refl => rfl
  | tail _ hm ih => exact (step_size hm).trans ih

variable [Inhabited Γ]

/-- Regard the finite lists as a standard two-way tape, with blank cells beyond the window. -/
@[expose] def Cfg.toNative (c : Cfg Γ Q) : TM0.Cfg Γ Q :=
  TM0.cfgOf c.state c.scanned c.left c.right

/-- Every window transition executes the same instruction on Mathlib's tape. -/
theorem step_native {M : TM0.Machine Γ Q} {c d : Cfg Γ Q} (h : step M c = some d) :
    TM0.step M c.toNative = some d.toNative := by
  rcases c with ⟨q, a, L, R⟩
  unfold step at h
  rcases hM : M q a with _ | ⟨q', (_ | _) | b⟩ <;> simp only [hM, reduceCtorEq] at h
  · cases L with
    | nil => contradiction
    | cons b L =>
      cases h
      exact TM0.step_of_eq_left hM (b :: L) R
  · cases R with
    | nil => contradiction
    | cons b R =>
      cases h
      exact TM0.step_of_eq_right hM L (b :: R)
  · cases h
    exact TM0.step_of_eq_write hM L R

/-- A finite-window computation is also a genuine computation of the original machine. -/
theorem reaches_native {M : TM0.Machine Γ Q} {c d : Cfg Γ Q}
    (hr : StateTransition.Reaches (step M) c d) : TM0.Reaches M c.toNative d.toNative :=
  hr.lift Cfg.toNative fun _ _ h => step_native h

end Turing.TM0Window
