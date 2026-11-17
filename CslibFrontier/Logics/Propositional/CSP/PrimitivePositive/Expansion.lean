/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.Composition
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Static expansion of primitive-positive gadgets

A finite macro body is interpreted using actual original-language gadgets. Each constraint
occurrence receives a fresh auxiliary block, even when its symbol and scope repeat. Blocks
have their actual lengths; no uniform bound or finite relation alphabet is required. The
macro's old auxiliaries precede the concatenation of replacement auxiliaries. Free ports
retain their index order. This module proves semantics only; ordered numerical witnesses
are constructed separately in the planar expansion bridge.

## Main definitions

* `Cslib.Logic.PL.CSP.PPGadget.expandList`: expansion on finite named ports.
* `Cslib.Logic.PL.CSP.PPGadget.expand`: expansion with the macro's original existential ports.
-/

public section

namespace Cslib.Logic.PL.CSP.PPGadget

variable {Src Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool}

/-- Expand a finite conjunction on named finite ports by the existing conjunction and
free-port substitution constructors. Its auxiliary layout is the ordered ragged sum of the
actual replacement sizes. Nullary constraints and empty bodies are retained. -/
@[expose] def expandList
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    {k : ℕ} (F : CSP Src (Fin k)) (hF : WellFormed srcArity F) :
    PPGadget arity sem {a | F.eval srcSem a = true} :=
  match F with
  | [] => {
      numAux := 0
      body := []
      wellFormed := by simp [WellFormed]
      correct := fun _ => by simp [eval] }
  | c :: cs =>
    let hc := hF c List.mem_cons_self
    let head := (gadgets c.rel).relabelFree (fun i => c.scope[i.val]'(by omega))
    let ht : WellFormed srcArity cs := fun d hd => hF d (List.mem_cons_of_mem c hd)
    let tail := expandList gadgets cs ht
    (head.conj tail).retarget fun a => by
      have hscope : List.ofFn (fun i : Fin (srcArity c.rel) =>
          a (c.scope[i.val]'(by omega))) = c.scope.map a := by
        apply List.ext_getElem
        · simp [hc]
        · intro i hi hj
          simp
      simp only [Set.mem_ofPred_eq, eval, List.all_cons, Bool.and_eq_true,
        Set.mem_inter_iff, booleanRelation, Function.comp_def]
      rw [hscope]
      rfl

/-- Exact auxiliary count: every source occurrence contributes its own replacement size. -/
@[simp] theorem numAux_expandList
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    {k : ℕ} (F : CSP Src (Fin k)) (hF : WellFormed srcArity F) :
    (expandList gadgets F hF).numAux = (F.map fun c => (gadgets c.rel).numAux).sum := by
  induction F with
  | nil => rfl
  | cons c cs ih =>
    change (gadgets c.rel).numAux + (expandList gadgets cs _).numAux =
      (gadgets c.rel).numAux + (cs.map fun d => (gadgets d.rel).numAux).sum
    exact congrArg ((gadgets c.rel).numAux + ·)
      (ih (fun d hd => hF d (List.mem_cons_of_mem c hd)))

/-- Expand a checked semantic macro into the original language. The macro's existential
ports are hidden using the existing substitution operation, before the fresh ragged blocks.
This is finite static preprocessing and makes no native running-time assertion. -/
@[expose] def expand
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    {n : ℕ} {R : Set (Fin n → Bool)} (g : PPGadget srcArity srcSem R) :
    PPGadget arity sem R :=
  ((expandList gadgets (g.body.relabel finSumFinEquiv)
    (g.wellFormed.relabel _)).substitute finSumFinEquiv.symm).retarget fun a => by
      rw [g.correct]
      apply exists_congr
      intro b
      simp only [Set.mem_ofPred_eq, eval_relabel, Function.comp_def,
        Equiv.symm_apply_apply]

/-- Old macro auxiliaries precede the actual per-occurrence replacement blocks. -/
@[simp] theorem numAux_expand
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    {n : ℕ} {R : Set (Fin n → Bool)} (g : PPGadget srcArity srcSem R) :
    (g.expand gadgets).numAux = g.numAux +
      (g.body.map fun c => (gadgets c.rel).numAux).sum := by
  change g.numAux + (expandList gadgets (g.body.relabel finSumFinEquiv) _).numAux = _
  rw [numAux_expandList]
  simp only [CSP.relabel, List.map_map, Constraint.relabel, Function.comp_def]

end Cslib.Logic.PL.CSP.PPGadget
