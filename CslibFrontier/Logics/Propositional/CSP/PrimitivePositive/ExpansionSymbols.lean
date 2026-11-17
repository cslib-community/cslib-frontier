/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.Composition

/-!
# Interpreted symbol maps for primitive-positive gadgets

A map of relation symbols preserving declared arities and interpretations preserves an
actual gadget, including its ordered scopes and its exact auxiliary count. The symbol map
need not be injective. In particular, this permits a structural probe tag without changing
the underlying original-language gadget.

## Main definitions

* `Cslib.Logic.PL.CSP.PPGadget.mapRelation`: interpreted symbol maps on exact gadget bodies.
* `Cslib.Logic.PL.CSP.PPGadget.withProbe`: adjoin a tautological atom to a replacement family.
-/

public section

namespace Cslib.Logic.PL.CSP.PPGadget

variable {Rel Other : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {otherArity : Other → ℕ} {otherSem : Other → List Bool → Bool}
  {n : ℕ} {R : Set (Fin n → Bool)}

/-- Map interpreted relation symbols, retaining every constraint occurrence, ordered scope,
free label and auxiliary label. No injectivity or finiteness of the alphabets is required. -/
@[expose] def mapRelation (g : PPGadget arity sem R) (f : Rel → Other)
    (ha : ∀ r, otherArity (f r) = arity r)
    (hs : ∀ r xs, otherSem (f r) xs = sem r xs) :
    PPGadget otherArity otherSem R where
  numAux := g.numAux
  body := g.body.map fun c => ⟨f c.rel, c.scope⟩
  wellFormed := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    rw [ha]
    exact g.wellFormed d hd
  correct a := by
    rw [g.correct]
    simp only [eval, List.all_map, Function.comp_def, Constraint.eval, hs]
    rfl

/-- Extend a replacement family by a structural symbol with n ordered ports and constant
true interpretation. Original symbols use the interpreted symbol map; the added symbol
uses the actual atom with no auxiliaries. This permits expansion to retain a boundary probe. -/
@[expose] def withProbe {Src : Type} {srcArity : Src → ℕ}
    {srcSem : Src → List Bool → Bool}
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r)) (n : ℕ) :
    ∀ r : Option Src, PPGadget (Option.elim' n arity) (Option.elim' (fun _ => true) sem)
      (booleanRelation (Option.elim' n srcArity) (Option.elim' (fun _ => true) srcSem) r)
  | some r => (gadgets r).mapRelation some (fun _ => rfl) (fun _ _ => rfl)
  | none => PPGadget.atom none

end Cslib.Logic.PL.CSP.PPGadget
