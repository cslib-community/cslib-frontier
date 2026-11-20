/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# Clock bounds for rejecting finite folds

`Cslib.foldlM_optionT_clock` adds a uniform per-iteration bound over a finite fold in
`OptionT (StateM σ)`. Rejection stops the fold but preserves the final state, so the bound
also charges the iteration that rejects. This is a bound on a caller-selected state clock,
not on the physical evaluation time of a callback.
-/

public section
namespace Cslib

/-- A finite fold spends at most its number of indices times the per-iteration budget,
including the last, possibly rejecting, iteration. -/
theorem foldlM_optionT_clock {σ R : Type} {n : ℕ} (clock : σ → ℕ) (cost : ℕ)
    (f : R → Fin n → OptionT (StateM σ) R)
    (h : ∀ a v s, clock ((f a v).run s).2 ≤ clock s + cost) (a : R) (s : σ) :
    clock ((Fin.foldlM n f a).run s).2 ≤ clock s + n * cost := by
  induction n generalizing a s with
  | zero => simp [Fin.foldlM_zero, pure, OptionT.pure, OptionT.run, OptionT.mk, StateT.pure]
  | succ n ih =>
    simp only [Fin.foldlM_succ, bind, OptionT.bind, OptionT.mk, OptionT.run, StateT.bind]
    have hfirst := h a 0 s
    change clock (f a 0 s).2 ≤ clock s + cost at hfirst
    cases hf : f a 0 s with
    | mk r t =>
      rw [hf] at hfirst
      change clock t ≤ clock s + cost at hfirst
      cases r with
      | none =>
        change clock t ≤ _
        rw [Nat.succ_mul]
        omega
      | some a' =>
        change clock ((Fin.foldlM n (fun b v => f b v.succ) a').run t).2 ≤ _
        have hrest := ih _ (fun b v t => h b v.succ t) a' t
        rw [Nat.succ_mul]
        omega

end Cslib
