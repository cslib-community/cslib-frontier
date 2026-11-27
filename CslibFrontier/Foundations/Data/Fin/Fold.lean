/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Lean, Init.Data.Fin.Fold)

public import CslibFrontier.Init

/-!
# Resuming a monadic fold over finite indices

`Fin.foldlMFrom` runs the suffix of a finite-index fold from a natural-number cursor.
Its equations specify initialization, one live step, and completion.
-/

public section

namespace Fin

/-- Run the suffix of a monadic fold over the indices from `i` to `n - 1`. -/
def foldlMFrom {m : Type → Type} [Monad m] {α : Type} {n : ℕ}
    (f : α → Fin n → m α) (a : α) (i : ℕ) : m α :=
  Fin.foldlM (n - i) (fun x u => f x ⟨i + u.val, by have := u.isLt; omega⟩) a

/-- Running from zero performs the original fold. -/
@[simp] theorem foldlMFrom_zero {m : Type → Type} [Monad m] {α : Type} {n : ℕ}
    (f : α → Fin n → m α) (a : α) : foldlMFrom f a 0 = Fin.foldlM n f a := by
  simp only [foldlMFrom, Nat.sub_zero, Nat.zero_add]

/-- Once the cursor reaches the bound, the current accumulator is final. -/
theorem foldlMFrom_of_le {m : Type → Type} [Monad m] {α : Type} {n : ℕ}
    (f : α → Fin n → m α) (a : α) {i : ℕ} (hi : n ≤ i) : foldlMFrom f a i = pure a := by
  simp only [foldlMFrom, Nat.sub_eq_zero_of_le hi, Fin.foldlM_zero]

/-- A live cursor consumes one index and continues at its successor. -/
theorem foldlMFrom_step {m : Type → Type} [Monad m] {α : Type} {n : ℕ}
    (f : α → Fin n → m α) (a : α) {i : ℕ} (hi : i < n) :
    foldlMFrom f a i = (f a ⟨i, hi⟩ >>= fun a' => foldlMFrom f a' (i + 1)) := by
  unfold foldlMFrom
  have hn : n - i = (n - (i + 1)) + 1 := by omega
  conv_lhs => simp only [hn, Fin.foldlM_succ]
  congr 1
  funext a'
  congr 1
  funext x u
  congr 1
  apply Fin.ext
  simp only [Fin.val_cast, Fin.val_succ]
  omega

end Fin
