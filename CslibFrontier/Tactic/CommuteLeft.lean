/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Group.Commute.Basic
public meta import Lean.Elab.Tactic.Simp

/-!
# Moving commuting factors to the left

Rigidity arguments move an operator of one player past operators of the other, which it commutes
with, many times in each chain of approximations: `X a * Z c * Z' d = Z' d * (X a * Z c)` when
`Z' d` commutes with `X a` and `Z c`. `commute_left [h₁, …, hₖ]` proves such equalities. Each
`hᵢ` states `Commute x y`, possibly quantified (`hXZ : ∀ a b, Commute (X a) (Z' b)`), and lets the
factors `y` move to the left of the factors `x`. The tactic calls `simp only` with associativity
and the instances of `Commute.left_comm` and `Commute.eq`. It supplies one placeholder per explicit
binder and leaves implicit and instance arguments to elaboration, so hypotheses such as
`∀ (a : ι) {b : ι}, Commute (X a) (Z b)` work.

In rigidity proofs the two players' operators form disjoint families. When the commutations
cover all cross-family pairs and orient them consistently, each swap reduces the number of
out-of-order pairs. The right-associated normal form has the second player's factors before the
first player's, preserving the order within each family. With overlapping families,
different normal forms can still be equal: under `Commute u v` and `Commute v w`, both
`v * u * w` and `u * w * v` are irreducible. The tactic reports any goal left open by
simplification.

## Main definitions

* `commute_left [h₁, …]`: prove an equation of products up to the given commutations.
-/

public meta section

namespace Cslib.Tactic.CommuteLeft

open Lean Meta Elab Tactic

/-- `commute_left [h₁, …, hₖ]` proves an equation of products in a monoid up to associativity and
the commutations `hᵢ : ∀ …, Commute x y`, by moving each `y` to the left of each `x`. -/
syntax (name := commuteLeft) "commute_left " "[" term,* "]" : tactic

/-- Elaborates `commute_left`. -/
@[tactic commuteLeft]
def evalCommuteLeft : Tactic := fun stx => do
  let hs : Syntax.TSepArray `term "," := ⟨stx[2].getArgs⟩
  let mut lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  for h in hs.getElems do
    let e ← elabTerm h none
    -- one placeholder per explicit binder; implicit arguments are inserted by elaboration
    let n ← forallTelescopeReducing (← inferType e) fun xs _ =>
      xs.foldlM (init := 0) fun k x => do
        return if (← x.fvarId!.getBinderInfo).isExplicit then k + 1 else k
    let holes : Array (TSyntax `term) ← (List.replicate n ()).toArray.mapM fun _ => `(_)
    let app ← if n = 0 then pure h else `($h $holes*)
    lemmas := lemmas.push (← `(Lean.Parser.Tactic.simpLemma| ($app).left_comm))
    lemmas := lemmas.push (← `(Lean.Parser.Tactic.simpLemma| ($app).eq))
  try
    evalTactic (← `(tactic| focus (simp only [mul_assoc, $lemmas,*]; done)))
  catch e =>
    throwError "commute_left: the given commutations do not close the goal; both sides must reach \
      the same normal form when each `y` with `Commute x y` moves left of `x`.\n{e.toMessageData}"

end Cslib.Tactic.CommuteLeft
