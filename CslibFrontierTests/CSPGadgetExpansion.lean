/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: candidate

import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Expansion

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Complexity.CSP.OrderedBoundary

namespace CSPGadgetExpansionTest

inductive Symbol where
  | bit
  | closed
  deriving DecidableEq

abbrev arity : Symbol → ℕ
  | .bit => 1
  | .closed => 0

def sem : Symbol → List Bool → Bool
  | .bit, [b] => b
  | .closed, [] => true
  | _, _ => false

-- Each bit replacement includes a genuinely used private auxiliary, a closed component,
-- and an isolated nullary constraint. No free port is identified with the private port.
def bitReplacement : PPGadget arity sem (booleanRelation arity sem .bit) where
  numAux := 1
  body := [⟨.bit, [.inl 0]⟩, ⟨.bit, [.inr 0]⟩, ⟨.closed, []⟩]
  wellFormed := by decide +kernel
  correct a := by
    simp only [booleanRelation, Set.mem_ofPred_eq]
    revert a
    decide +kernel

def bitWitness : GadgetWitness bitReplacement where
  certificate := ⟨[4, 1, 2, 3, 0, 5]⟩
  accepted := by decide +kernel

def replacements : ∀ r, PPGadget arity sem (booleanRelation arity sem r)
  | .bit => bitReplacement
  | .closed => PPGadget.atom (arity := arity) (sem := sem) .closed

def replacementWitnesses : ∀ r, GadgetWitness (replacements r)
  | .bit => bitWitness
  | .closed => Witness.atom arity sem .closed

-- Two separate occurrences have the same source symbol, scope and free label.
def repeated : PPGadget arity sem (booleanRelation arity sem .bit) where
  numAux := 0
  body := [⟨.bit, [.inl 0]⟩, ⟨.bit, [.inl 0]⟩]
  wellFormed := by decide +kernel
  correct a := by
    simp only [booleanRelation, Set.mem_ofPred_eq]
    revert a
    decide +kernel

def repeatedWitness : GadgetWitness repeated where
  certificate := ⟨[2, 1, 4, 3, 0, 5]⟩
  accepted := by decide +kernel

def expanded := repeated.expand replacements

example : expanded.numAux = 2 := rfl

-- Actual per-occurrence auxiliary indices differ, while both source scopes still share x.
example : expanded.body =
    ([⟨.bit, [.inl 0]⟩, ⟨.bit, [.inr 0]⟩, ⟨.closed, []⟩,
     ⟨.bit, [.inl 0]⟩, ⟨.bit, [.inr 1]⟩, ⟨.closed, []⟩] : CSP Symbol (Fin 1 ⊕ Fin 2)) := rfl

def expandedWitness : GadgetWitness expanded :=
  repeatedWitness.expand replacements replacementWitnesses 1 (by intro r; cases r <;> decide)

-- An explicit target table executes both full checkers on the literal expanded body.
example : verify expanded.body (List.ofFn Sum.inl)
    ⟨[4, 1, 2, 3, 8, 5, 6, 7, 0, 9]⟩ = true := by decide +kernel

-- The generic bridge itself computes that exact table from the checked input tables.
example : expandedWitness.certificate.successor =
    [4, 1, 2, 3, 8, 5, 6, 7, 0, 9] := by decide +kernel

example : verify expanded.body (List.ofFn Sum.inl) expandedWitness.certificate = true := by
  decide +kernel

-- SAT and UNSAT rows execute the literal expanded body, including the closed components.
example : ∃ b : Fin expanded.numAux → Bool,
    expanded.body.eval sem (Sum.elim (fun _ => true) b) = true := by decide +kernel

example : ¬∃ b : Fin expanded.numAux → Bool,
    expanded.body.eval sem (Sum.elim (fun _ => false) b) = true := by decide +kernel

-- A nullary macro remains a real nullary constraint after expansion; no fake port is added.
def nullaryExpanded := (PPGadget.atom (arity := arity) (sem := sem) .closed).expand replacements

example : nullaryExpanded.numAux = 0 ∧ nullaryExpanded.body = [⟨.closed, []⟩] := by
  decide +kernel

example : Nonempty (GadgetWitness nullaryExpanded) :=
  ⟨(Witness.atom arity sem .closed).expand replacements replacementWitnesses 1
    (by intro r; cases r <;> decide)⟩

-- The old hidden variable stays in block 0; replacement copies use blocks 1 and 2.
def hidden : PPGadget arity sem (booleanRelation arity sem .bit) where
  numAux := 1
  body := [⟨.bit, [.inl 0]⟩, ⟨.bit, [.inr 0]⟩]
  wellFormed := by decide +kernel
  correct a := by
    simp only [booleanRelation, Set.mem_ofPred_eq]
    revert a
    decide +kernel

def hiddenWitness : GadgetWitness hidden where
  certificate := ⟨[4, 1, 2, 3, 0, 5]⟩
  accepted := by decide +kernel

def hiddenExpanded := hidden.expand replacements

example : hiddenExpanded.numAux = 3 ∧ hiddenExpanded.body =
    ([⟨.bit, [.inl 0]⟩, ⟨.bit, [.inr 1]⟩, ⟨.closed, []⟩,
     ⟨.bit, [.inr 0]⟩, ⟨.bit, [.inr 2]⟩, ⟨.closed, []⟩] : CSP Symbol (Fin 1 ⊕ Fin 3)) := ⟨rfl, rfl⟩

example : verify hiddenExpanded.body (List.ofFn Sum.inl)
    ⟨[8, 1, 2, 3, 4, 5, 6, 7, 0, 9]⟩ = true := by decide +kernel

example : Nonempty (GadgetWitness hiddenExpanded) :=
  ⟨hiddenWitness.expand replacements replacementWitnesses 1
    (by intro r; cases r <;> decide)⟩

-- Both free ports are unused. The nonempty probe is still checked and kept in index order.
def empty : PPGadget arity sem (Set.univ : Set (Fin 2 → Bool)) where
  numAux := 0
  body := []
  wellFormed := by decide +kernel
  correct a := by revert a; decide +kernel

def emptyWitness : GadgetWitness empty where
  certificate := ⟨[0, 3, 2, 1]⟩
  accepted := by decide +kernel

example : (empty.expand replacements).body = [] ∧
    (empty.expand replacements).numAux = 0 := by decide +kernel

example : Nonempty (GadgetWitness (empty.expand replacements)) :=
  ⟨emptyWitness.expand replacements replacementWitnesses 1
    (by intro r; cases r <;> decide)⟩

-- An empty boundary with a genuine closed existential component exercises n = 0 hiding.
def closed : PPGadget arity sem (Set.univ : Set (Fin 0 → Bool)) where
  numAux := 1
  body := [⟨.bit, [.inr 0]⟩]
  wellFormed := by decide +kernel
  correct a := by revert a; decide +kernel

def closedWitness : GadgetWitness closed where
  certificate := ⟨[0, 1]⟩
  accepted := by decide +kernel

def closedExpanded := closed.expand replacements

example : closedExpanded.numAux = 2 ∧ closedExpanded.body =
    ([⟨.bit, [.inr 0]⟩, ⟨.bit, [.inr 1]⟩, ⟨.closed, []⟩] : CSP Symbol (Fin 0 ⊕ Fin 2)) := ⟨rfl, rfl⟩

example : verify closedExpanded.body (List.ofFn Sum.inl) ⟨[0, 1, 2, 3]⟩ = true := by
  decide +kernel

example : Nonempty (GadgetWitness closedExpanded) :=
  ⟨closedWitness.expand replacements replacementWitnesses 1
    (by intro r; cases r <;> decide)⟩

end CSPGadgetExpansionTest
