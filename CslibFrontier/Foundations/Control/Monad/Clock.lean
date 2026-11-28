/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# Clock bounds for stateful computations

`Cslib.bind_stateM_clock` adds the bounds for two consecutive stateful computations.
`Cslib.bind_optionT_clock` handles the rejecting bind.
`Cslib.foldlM_optionT_clock` applies this to each iteration of a finite fold in
`OptionT (StateM σ)`. Rejection stops the fold but preserves the final state, so the bound
also charges the iteration that rejects. This is a bound on a caller-selected state clock,
not on the physical evaluation time of a callback.
-/

public section
namespace Cslib

/-- Bound the clock of a stateful bind by the sum of its component bounds. -/
theorem bind_stateM_clock {σ α β : Type} (clock : σ → ℕ) (A B : ℕ)
    (x : StateM σ α) (f : α → StateM σ β)
    (hx : ∀ s, clock (x s).2 ≤ clock s + A)
    (hf : ∀ a s, clock (f a s).2 ≤ clock s + B) (s : σ) :
    clock ((x >>= f) s).2 ≤ clock s + (A + B) := by
  change clock (f (x s).1 (x s).2).2 ≤ _
  exact (hf (x s).1 (x s).2).trans (by rw [← Nat.add_assoc]; exact Nat.add_le_add_right (hx s) B)

/-- Bound the clock of a rejecting bind by the sum of the component bounds.
If the first computation rejects, its final state supplies the clock. -/
theorem bind_optionT_clock {σ α β : Type} (clock : σ → ℕ) (A B : ℕ)
    (x : OptionT (StateM σ) α) (f : α → OptionT (StateM σ) β)
    (hx : ∀ s, clock (x.run s).2 ≤ clock s + A)
    (hf : ∀ a s, clock ((f a).run s).2 ≤ clock s + B) (s : σ) :
    clock ((x >>= f).run s).2 ≤ clock s + (A + B) := by
  simp only [bind, OptionT.bind, OptionT.mk, OptionT.run]
  apply bind_stateM_clock clock A B _ _ hx
  intro result t
  cases result with
  | none => exact Nat.le_add_right (clock t) B
  | some a => exact hf a t

/-- A finite fold spends at most its number of indices times the per-iteration budget,
including the last, possibly rejecting, iteration. -/
theorem foldlM_optionT_clock {σ R : Type} {n : ℕ} (clock : σ → ℕ) (cost : ℕ)
    (f : R → Fin n → OptionT (StateM σ) R)
    (h : ∀ a v s, clock ((f a v).run s).2 ≤ clock s + cost) (a : R) (s : σ) :
    clock ((Fin.foldlM n f a).run s).2 ≤ clock s + n * cost := by
  induction n generalizing a s with
  | zero => simp [Fin.foldlM_zero, pure, OptionT.pure, OptionT.run, OptionT.mk, StateT.pure]
  | succ n ih =>
    rw [Fin.foldlM_succ, Nat.succ_mul, Nat.add_comm (n * cost) cost]
    exact bind_optionT_clock clock cost (n * cost) (f a 0)
      (fun b => Fin.foldlM n (fun c v => f c v.succ) b) (h a 0)
      (ih _ fun b v t => h b v.succ t) s

end Cslib
