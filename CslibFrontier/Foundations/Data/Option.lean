/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# Option lemmas

Lemmas about `Option` operations such as `Option.getD`.

## Main results

* `Option.getD_self_eq_iff`: `o.getD b = b ↔ ∀ b', o = some b' → b = b'`.
* `Option.getD_beq_self_eq_true_iff`: `(o.getD b == b) = true ↔ ∀ b', o = some b' → b = b'`.
-/

public section

namespace Option

/-- An optional Boolean value `o` agrees with `b` on the defined part (that is,
`b = b'` whenever `o = some b'`) if and only if `o.getD b = b` holds. -/
@[simp]
theorem getD_self_eq_iff {o : Option Bool} {b : Bool} :
    o.getD b = b ↔ ∀ b', o = some b' → b = b' := by
  cases o with
  | none => simp
  | some b' =>
    simp only [Option.getD_some, Option.some.injEq, forall_eq']
    exact eq_comm

/-- An optional Boolean value `o` agrees with `b` on the defined part (that is,
`b = b'` whenever `o = some b'`) if and only if `o.getD b == b` holds. -/
theorem getD_beq_self_eq_true_iff {o : Option Bool} {b : Bool} :
    (o.getD b == b) = true ↔ ∀ b', o = some b' → b = b' := by
  rw [beq_iff_eq, getD_self_eq_iff]

end Option

/-- Replacing every accepted entry in an optional vector with a prescribed value retains
failure and returns precisely the vector of prescribed values on success. -/
theorem Vector.ofFnM_option_replace {α β : Type*} {n : ℕ} (f : Fin n → Option α) (v : Fin n → β) :
    Vector.ofFnM (fun i => (f i).map fun _ => v i) =
      (Vector.ofFnM f).map fun _ => Vector.ofFn v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Vector.ofFnM_succ, Vector.ofFnM_succ, ih (fun i => f i.castSucc) (fun i => v i.castSucc)]
    cases Vector.ofFnM (fun i : Fin n => f i.castSucc) <;>
      cases f (Fin.last n) <;> simp [Vector.ofFn_succ, Fin.last]

end
