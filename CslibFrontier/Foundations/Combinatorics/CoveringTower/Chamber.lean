/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.CoveringTower.Defs
public import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic

/-!
# Chambers of a tower by their vertex and place

A chamber of a `Cslib.CoveringTower.Tower` is determined by its vertex of a type and its place at
that vertex, and the vertex of a chamber has a host in the next level.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Tow.Net`.

## Main definitions

* `Cslib.CoveringTower.Tower.hostOf`: the host of the vertex of a chamber.
* `Cslib.CoveringTower.Tower.chamberEquiv`: a chamber is a vertex and a place at it.

## Main results

* `Cslib.CoveringTower.Tower.π_ne`: the covering map separates the two ends of an edge.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Appendix H.3; module `Nc.Tow.Net`
-/

public section

namespace Cslib.CoveringTower.Tower

variable {h b D J r : ℕ} (T : Tower h b D J r) {j : ℕ}

/-- The host of the vertex of type `i` of a chamber. -/
abbrev hostOf (i : Fin h) (c : T.X j) : T.X (j + 1) := T.host i (T.vx i c)

variable {T}

/-- The covering map separates the two ends of an edge. -/
theorem π_ne (hj : j < J) (e : T.Ed j) : T.π (T.e0 e) ≠ T.π (T.e1 e) := fun heq => by
  have h1 := T.π_ends hj e
  rw [heq, Sym2.eq_iff] at h1
  exact T.e_ne (T.πE e) (h1.elim (fun h => h.1.trans h.2.symm) fun h => h.1.trans h.2.symm)

variable (T) in
/-- A chamber is its vertex of type `i` and its place at that vertex. -/
noncomputable def chamberEquiv (hj : j ≤ J) (i : Fin h) : T.X j ≃ T.V j i × T.Fl :=
  Equiv.ofBijective _ (T.vx_co hj i)

@[simp]
theorem chamberEquiv_apply (hj : j ≤ J) (i : Fin h) (c : T.X j) :
    T.chamberEquiv hj i c = (T.vx i c, T.co i c) := by rfl

@[simp]
theorem chamberEquiv_symm_vx_co (hj : j ≤ J) (i : Fin h) (c : T.X j) :
    (T.chamberEquiv hj i).symm (T.vx i c, T.co i c) = c :=
  (T.chamberEquiv hj i).symm_apply_apply c

@[simp]
theorem vx_chamberEquiv_symm (hj : j ≤ J) (i : Fin h) (p : T.V j i × T.Fl) :
    T.vx i ((T.chamberEquiv hj i).symm p) = p.1 :=
  congrArg Prod.fst ((T.chamberEquiv hj i).apply_symm_apply p)

@[simp]
theorem co_chamberEquiv_symm (hj : j ≤ J) (i : Fin h) (p : T.V j i × T.Fl) :
    T.co i ((T.chamberEquiv hj i).symm p) = p.2 :=
  congrArg Prod.snd ((T.chamberEquiv hj i).apply_symm_apply p)

end Cslib.CoveringTower.Tower
