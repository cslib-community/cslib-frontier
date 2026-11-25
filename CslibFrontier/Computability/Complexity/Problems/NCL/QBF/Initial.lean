/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Source
public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Network.Evaluation
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Realization

/-!
# Initial configurations of quantifier circuits

Construct an explicit legal inactive configuration of every quantifier chain and CNF body.
The satisfied wires point down, the try and literal wires point up, and the matrix network has
every edge pointing up. Fixed local orientations of the two quantifiers suffice; the whole
configuration is assembled recursively, without evaluating the source formula.

These configurations support the soundness direction for the open circuit body of
[HearnDemaine2005, Section 3.1]. They also cover empty prefixes, empty matrices and empty clauses.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Initial.chain`: an inactive legal quantifier chain.
* `Cslib.Complexity.NCL.QBF.Initial.terminal`: its inactive CNF terminal.
* `Cslib.Complexity.NCL.QBF.Initial.body`: their explicit legal composite.

## Main results

* `Cslib.Complexity.NCL.QBF.Initial.eval_of_canReverse`: reversing the outer satisfied wire
  from this initial configuration implies truth of the closed upstream source formula.
* `Cslib.Complexity.NCL.QBF.Initial.chain_memories`: every variable latch initially holds false.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Initial

open Diagram Gate Network Cslib.Logic.PL Cslib.Logic.PL.QBF

local notation "R" => Color.red
local notation "B" => Color.blue

/-- Inactive controls, followed by inactive tail wires. The satisfied wire points down. -/
@[expose]
def controls (r : List Color) : List Bool := true :: false :: List.replicate r.length false

/-- The inactive directions at the bottom of a chain, with each new literal pair prepended. -/
@[expose] def boundary (r : List Color) : List Quantifier → List Bool
  | [] => controls r
  | _ :: qs => boundary ([R, R] ++ r) qs

attribute [local instance] Diagram.decidableLegal

/-- The existential gadget with its variable latch false and both literals inactive. -/
@[expose] def existsInitial : Realization Gate.interp existsGadget
    [true, false] [true, false, false, false] where
  orient := fun e => [0, 6].contains (existsGadget.num e)
  legal := by decide +kernel
  top_eq := by decide +kernel
  bot_eq := by decide +kernel

/-- The universal gadget with its variable latch false and its record clear. -/
@[expose] def forallInitial : Realization Gate.interp forallGadget
    [true, false] [true, false, false, false] where
  orient := fun e => [0, 2, 4, 7, 11, 26, 30, 31].contains (forallGadget.num e)
  legal := by decide +kernel
  top_eq := by decide +kernel
  bot_eq := by decide +kernel

/-- The inactive local configuration of either quantifier. -/
@[expose] def quantifier : (q : Quantifier) → Realization Gate.interp q.gadget
    [true, false] [true, false, false, false]
  | .ex => existsInitial
  | .all => forallInitial

/-- An explicit inactive legal configuration of an arbitrary quantifier chain.
All literal wires, including the incoming tail, point up. -/
@[expose] def chain (r : List Color) : (qs : List Quantifier) →
    Realization Gate.interp (Chain.diagram r qs) (controls r) (boundary r qs)
  | [] => .id _ _ (by simp [controls])
  | q :: qs => by
    have h := (quantifier q).tensor
      (Realization.id (I := Gate.interp) r (List.replicate r.length false) (by simp))
    exact (show Realization Gate.interp (q.gadget.tensor (.id r))
      (controls r) (controls ([R, R] ++ r)) from h).comp (chain ([R, R] ++ r) qs)

/-- Every variable latch in the initial chain holds false, in binding order. -/
theorem chain_memories (r : List Color) (qs : List Quantifier) :
    Chain.memories r qs (chain r qs).orient = List.replicate qs.length false := by
  induction qs generalizing r with
  | nil => rfl
  | cons q qs ih =>
    have hmem : (quantifier q).orient q.mem = false := by cases q <;> decide +kernel
    let h : Realization Gate.interp (q.gadget.tensor (.id r))
        (controls r) (controls ([R, R] ++ r)) := (quantifier q).tensor (.id r _ (by simp))
    have hh : (chain r (q :: qs)).orient ∘ (Chain.headOcc r q qs).emb = (quantifier q).orient :=
      (congrArg (· ∘ tensorLeft q.gadget (.id r))
        (Realization.comp_orient_compLeft h (chain ([R, R] ++ r) qs))).trans
        (Realization.tensor_orient_tensorLeft _ _)
    have ht : (chain r (q :: qs)).orient ∘ (Chain.tailOcc r q qs).emb =
        (chain ([R, R] ++ r) qs).orient := Realization.comp_orient_compRight _ _
    change ((chain r (q :: qs)).orient ∘ (Chain.headOcc r q qs).emb) q.mem ::
      Chain.memories ([R, R] ++ r) qs ((chain r (q :: qs)).orient ∘ (Chain.tailOcc r q qs).emb) = _
    rw [hh, ht, hmem, ih]; rfl

/-- The inactive orientation is legal when moving a wire left across a bundle. -/
theorem legal_moveLeft_zero (l : List Color) (x : Color) (r : List Color) :
    ((moveLeft l x r : Diagram Gate _ _).graph Gate.interp).Legal (fun _ => false) := by
  induction l with
  | nil => exact fun v => v.elim
  | cons y l ih =>
    exact (legal_comp_iff _ _ _).2 ⟨
      (legal_tensor_iff _ _ _).2 ⟨fun v => v.elim, ih⟩,
      (legal_tensor_iff _ _ _).2 ⟨fun v => v.elim, fun v => v.elim⟩⟩

/-- The return gate with inactive satisfied, try and matrix-value wires. -/
@[expose] def returnInitial : Realization Gate.interp Matrix.returnGate
    [true, false, false] [] where
  orient := fun e => Matrix.returnGate.num e == 0
  legal := by decide +kernel
  top_eq := by decide +kernel
  bot_eq := by decide +kernel

/-- Literal-pair caps admit the constant inactive orientation. -/
theorem legal_caps_zero (r : List Color) : ∀ (p : ℕ),
    ((Matrix.caps r p).graph Gate.interp).Legal (fun _ => false)
  | 0 => fun v => v.elim
  | p + 1 => (legal_tensor_iff _ _ _).2 ⟨by
      change ((gen cap).graph Gate.interp).Legal (fun _ => false)
      decide +kernel, legal_caps_zero r p⟩

/-- An inactive matrix network, return gate and terminated literal bundle. -/
@[expose] def terminalBase (p : ℕ) (ms : List (List Bool)) :
    Realization Gate.interp (Matrix.terminalBase p ms) (controls (bundle (2 * p) ++ [])) [] := by
  have hn := Realization.zeros (I := Gate.interp) (network [] (2 * p) ms)
    (by exact legal_network_zero [] (2 * p) ms)
  have hm := Realization.zeros (I := Gate.interp) (moveLeft (bundle (2 * p)) B [])
    (by exact legal_moveLeft_zero (bundle (2 * p)) B [])
  have hfirst := (Realization.id (I := Gate.interp) [B, B] [true, false] rfl).tensor hn
  have hmove := (Realization.id (I := Gate.interp) [B, B] [true, false] rfl).tensor hm
  have hlast := returnInitial.tensor
    (Realization.zeros (I := Gate.interp) (Matrix.caps [] p) (by exact legal_caps_zero [] p))
  exact (hfirst.comp hmove).comp hlast

/-- Every wire created inside the initial terminal points up. -/
theorem terminalBase_off (p : ℕ) (ms : List (List Bool)) :
    (Matrix.terminalBase p ms).off (terminalBase p ms).orient = (terminalBase p ms).orient := by
  have hr : Matrix.returnGate.off returnInitial.orient = returnInitial.orient := by decide +kernel
  dsimp only [terminalBase, Realization.comp, Realization.tensor, Realization.zeros]
  simp only [Matrix.terminalBase, off_glueComp, off_glueTensor, off_id, off_false, hr,
    off_false (moveLeft (bundle (2 * p)) B [] : Diagram Gate _ _), off_false (Matrix.caps [] p)]

/-- The CNF terminal in its inactive configuration. Its entire network points up. -/
@[expose] def terminal (p : ℕ) : (qs : List Quantifier) → (ms : List (List Bool)) →
    Realization Gate.interp (Matrix.terminal p qs ms) (boundary (bundle (2 * p) ++ []) qs) []
  | [], ms => terminalBase p ms
  | _ :: qs, ms => terminal (p + 1) qs ms

/-- The initial configuration of an arbitrary CNF body. Its satisfied wire points down and
its try wire points up; the construction is independent of the formula's truth. -/
@[expose] def body (qs : List Quantifier) (ms : List (List Bool)) :
    Realization Gate.interp (Matrix.body qs ms) [true, false] [] :=
  (chain [] qs).comp (terminal 0 qs ms)

/-- Every variable latch in the initial circuit body holds false. -/
theorem body_memories (qs : List Quantifier) (ms : List (List Bool)) :
    Chain.memories [] qs ((body qs ms).orient ∘ (Matrix.chainOcc qs ms).emb) =
      List.replicate qs.length false := by
  rw [show (body qs ms).orient ∘ (Matrix.chainOcc qs ms).emb = (chain [] qs).orient from
    Realization.comp_orient_compLeft _ _, chain_memories]

/-- Reversing the body's satisfied wire from the explicit initial configuration implies truth
of the closed source formula, for every valuation of its free-variable interface. -/
theorem eval_of_canReverse {V : Type*} [DecidableEq V] (ps : List (V × V))
    (φ : CNF V)
    (hclosed : (rounds ps (ofCNF φ)).Closed)
    (h : ((Matrix.body (Source.quantifiers ps) (Source.masks ps φ)).graph Gate.interp).CanReverse
      (body (Source.quantifiers ps) (Source.masks ps φ)).orient (.inl 0)) (σ : V → Bool) :
    (rounds ps (ofCNF φ)).eval σ = true := by
  let s := body (Source.quantifiers ps) (Source.masks ps φ)
  obtain ⟨t, ht, he⟩ := h
  exact Source.eval_of_reachable ps φ hclosed .refl s.legal (congrArg (·[1]!) s.top_eq) ht
    (Bool.eq_false_of_not_eq_true fun heq => he (heq.trans (congrArg (·[0]!) s.top_eq).symm)) σ

end Cslib.Complexity.NCL.QBF.Initial
