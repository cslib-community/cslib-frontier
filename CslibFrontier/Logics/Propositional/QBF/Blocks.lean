/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.QBF.Assignment

/-!
# Blocks of quantifiers in Boolean formulas

`QBF.blocks q bs φ` prefixes `φ` with the lists of variables in `bs`, alternating
existential and universal blocks, existential first when `q = true`. Empty blocks are
allowed. The matrix and the resulting formula use the existing `QBF` syntax.

The word-quantifier interpretation is proved in
`CslibFrontier.Computability.Complexity.Classes.PH.QBF`.
-/

public section

namespace Cslib.Logic.PL.QBF

variable {V : Type*} [DecidableEq V]

/-- Prefix a formula by alternating blocks of quantifiers, starting existentially for `true`.
An empty block is allowed and still changes the polarity of the next block. -/
@[expose] def blocks : Bool → List (List V) → QBF V → QBF V
  | _, [], φ => φ
  | true, vs :: bs, φ => exs vs (blocks false bs φ)
  | false, vs :: bs, φ => alls vs (blocks true bs φ)

/-- Updating a concatenated list of variables by a concatenated list of values is sequential
updating, when the first lists have the same length. -/
theorem updates_append {vs : List V} {u : List Bool} (hu : u.length = vs.length)
    (σ : V → Bool) (ws : List V) (w : List Bool) :
    updates σ (vs ++ ws) (u ++ w) = updates (updates σ vs u) ws w := by
  induction vs generalizing σ u with
  | nil => obtain rfl := List.length_eq_zero_iff.mp hu; rfl
  | cons v vs ih =>
    cases u with
    | nil => simp at hu
    | cons b u => exact ih (by simpa using hu) _

/-- An existential block quantifies over all words assigning its variables in order, even if
some variable names repeat. -/
theorem eval_exs_iff_word (vs : List V) (φ : QBF V) (σ : V → Bool) :
    (exs vs φ).eval σ = true ↔
      ∃ w : List Bool, w.length = vs.length ∧ φ.eval (updates σ vs w) = true := by
  induction vs generalizing σ with
  | nil => simp [exs, updates]
  | cons v vs ih =>
    change (ex v (exs vs φ)).eval σ = true ↔ _
    simp only [eval_ex_eq_true_iff, ih]
    constructor
    · rintro ⟨b, w, hw, h⟩
      exact ⟨b :: w, congrArg (· + 1) hw, h⟩
    · rintro ⟨_ | ⟨b, w⟩, hw, h⟩
      · simp at hw
      · exact ⟨b, w, Nat.succ.inj hw, h⟩

/-- A universal block quantifies over all words assigning its variables in order. -/
theorem eval_alls_iff_word (vs : List V) (φ : QBF V) (σ : V → Bool) :
    (alls vs φ).eval σ = true ↔
      ∀ w : List Bool, w.length = vs.length → φ.eval (updates σ vs w) = true := by
  induction vs generalizing σ with
  | nil => simp [alls, updates]
  | cons v vs ih =>
    change (all v (alls vs φ)).eval σ = true ↔ _
    simp only [eval_all_eq_true_iff, ih]
    constructor
    · rintro h (_ | ⟨b, w⟩) hw
      · simp at hw
      · exact h b w (Nat.succ.inj hw)
    · intro h b w hw
      exact h (b :: w) (congrArg (· + 1) hw)

/-- The free variables of alternating blocks are the free variables of the matrix with all
variables of the prefix removed. -/
theorem freeVars_blocks (q : Bool) (bs : List (List V)) (φ : QBF V) :
    (blocks q bs φ).freeVars = φ.freeVars \ bs.flatten.toFinset := by
  induction bs generalizing q with
  | nil => simp [blocks]
  | cons vs bs ih =>
    cases q <;> simp only [blocks, freeVars_exs, freeVars_alls, ih, List.flatten_cons,
      List.toFinset_append] <;> ext v <;> simp <;> tauto

/-- Append variables to the last block, leaving earlier blocks unchanged. -/
@[expose] def appendLast (bs : List (List V)) (vs : List V) : List (List V) :=
  match bs with
  | [] => [vs]
  | [b] => [b ++ vs]
  | b :: c :: bs => b :: appendLast (c :: bs) vs

omit [DecidableEq V] in
/-- Appending variables to a nonempty prefix preserves its number of blocks. -/
theorem length_appendLast {bs : List (List V)} (h : bs ≠ []) (vs : List V) :
    (appendLast bs vs).length = bs.length := by
  fun_induction appendLast bs vs with
  | case1 => contradiction -- []
  | case2 => rfl -- [b]
  | case3 b c bs ih => simp only [List.length_cons, ih (List.cons_ne_nil _ _)] -- b :: c :: bs

omit [DecidableEq V] in
/-- Appending variables to the final block appends them to the flattened prefix. -/
theorem flatten_appendLast (bs : List (List V)) (vs : List V) :
    (appendLast bs vs).flatten = bs.flatten ++ vs := by
  fun_induction appendLast bs vs with
  | case3 b c bs ih => -- b :: c :: bs
    simpa only [List.flatten_cons, List.append_assoc] using congrArg (b ++ ·) ih
  | _ => simp -- [] or [b]

omit [DecidableEq V] in
/-- Appending to the final block can be computed by reversing the prefix. -/
theorem appendLast_eq_reverse (bs : List (List V)) (vs : List V) :
    appendLast bs vs = ((bs.reverse.headD [] ++ vs) :: bs.reverse.tail).reverse := by
  fun_induction appendLast bs vs with
  | case3 b c bs ih => -- b :: c :: bs
    rcases hrev : (c :: bs).reverse with _ | ⟨v, rest⟩
    · simp at hrev
    · simp only [hrev, List.headD_cons, List.tail_cons] at ih
      simpa [List.reverse_cons, hrev] using congrArg (b :: ·) ih
  | _ => simp -- [] or [b]

omit [DecidableEq V] in
/-- Appending variables to the last block merges a quantifier of the same polarity into it.
The hypothesis identifies that last polarity without an arithmetic parity convention. -/
theorem blocks_appendLast (q r : Bool) {bs : List (List V)} (hbs : bs ≠ [])
    (hr : (Bool.not)^[bs.length] q = !r) (vs : List V) (φ : QBF V) :
    blocks q (appendLast bs vs) φ =
      blocks q bs (if r then exs vs φ else alls vs φ) := by
  fun_induction appendLast bs vs generalizing q with
  | case1 => contradiction -- []
  | case2 => -- [b]
    obtain rfl : q = r := by simpa using congrArg Bool.not hr
    cases q <;> simp [blocks, exs_append, alls_append]
  | case3 b c bs ih => -- b :: c :: bs
    rw [List.length_cons, Function.iterate_succ_apply] at hr
    cases q <;> exact congrArg _ (ih _ (List.cons_ne_nil _ _) hr)

end Cslib.Logic.PL.QBF
