/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Relation

/-!
# Simulations between transition systems

Every reduction around constraint logic compares two transition systems: QBF evaluation with a
constraint graph, a constraint graph with its planarization, a constraint graph with a puzzle
[HearnDemaine2005]. A transition system here is just a step relation `r : α → α → Prop`, and
reachability is `Relation.ReflTransGen r`.

A simulation of `r` by `r'` (`Cslib.Complexity.NCL.Simulation`) consists of

* an abstraction `abs : β → α`, which maps every step of `r'` to a step of `r` or to no step
  (`Relation.ReflGen r`), and
* an encoding `enc : α → β`, a section of `abs`, which maps every step of `r` to a sequence of
  steps of `r'`.

The abstraction is a function, not a relation: a simulating system may pass through states that
correspond to no state of `r` exactly, and `abs` decides what they stand for. Then `r'` reaches
`enc a'` from `enc a` exactly when `r` reaches `a'` from `a`
(`Cslib.Complexity.NCL.Simulation.reachable_enc_iff`), and from `enc a` it reaches a goal that
`abs` respects exactly when `r` reaches the abstract goal from `a`
(`Cslib.Complexity.NCL.Simulation.exists_reachable_enc_iff`). Simulations compose
(`Cslib.Complexity.NCL.Simulation.trans`).

## Dead states and invariants

## Main definitions

* `Cslib.Complexity.NCL.Simulation`: a simulation of one step relation by another.
* `Cslib.Complexity.NCL.Simulation.refl`, `Cslib.Complexity.NCL.Simulation.trans`,
  `Cslib.Complexity.NCL.Simulation.ofEquiv`: identity, composition, and a bijection of states
  that preserves and reflects steps.
## Main results

* `Cslib.Complexity.NCL.Simulation.reachable_enc_iff`: reachability between encodings.
* `Cslib.Complexity.NCL.Simulation.exists_reachable_enc_iff`: reachability of goals.
## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL

open Relation

variable {α β γ : Type*} {r : α → α → Prop} {r' : β → β → Prop} {r'' : γ → γ → Prop}

/-- A simulation of the step relation `r` by `r'`: an abstraction of states of `r'` to states of
`r` that maps every step to a step or to no step, and an encoding back, a section of the
abstraction, that maps every step to a sequence of steps. -/
structure Simulation (r : α → α → Prop) (r' : β → β → Prop) where
  /-- The state of `r` that a state of `r'` stands for. -/
  abs : β → α
  /-- The state of `r'` that encodes a state of `r`. -/
  enc : α → β
  /-- An encoding stands for the state it encodes. -/
  abs_enc (a : α) : abs (enc a) = a
  /-- A step of `r'` stands for a step of `r`, or for none. -/
  step_abs {b b' : β} : r' b b' → ReflGen r (abs b) (abs b')
  /-- A step of `r` is realized by a sequence of steps between the encodings. -/
  step_enc {a a' : α} : r a a' → ReflTransGen r' (enc a) (enc a')

/-- At most one step of `r`, mapped along `f` to at most one step of `p`. -/
private theorem reflGen_map {p : β → β → Prop} (f : α → β)
    (hf : ∀ ⦃a a'⦄, r a a' → ReflGen p (f a) (f a')) {a a' : α} :
    ReflGen r a a' → ReflGen p (f a) (f a')
  | .refl => .refl
  | .single h => hf h

namespace Simulation

/-- Reachability in `r'` is abstracted to reachability in `r`. -/
theorem reachable_abs (S : Simulation r r') {b b' : β} (h : ReflTransGen r' b b') :
    ReflTransGen r (S.abs b) (S.abs b') :=
  ReflTransGen.lift' S.abs (fun _ _ h => (S.step_abs h).to_reflTransGen) _ _ h

/-- Reachability in `r` is realized between the encodings. -/
theorem reachable_enc (S : Simulation r r') {a a' : α} (h : ReflTransGen r a a') :
    ReflTransGen r' (S.enc a) (S.enc a') :=
  ReflTransGen.lift' S.enc (fun _ _ => S.step_enc) _ _ h

/-- **Reachability between encodings is preserved and reflected.** -/
theorem reachable_enc_iff (S : Simulation r r') {a a' : α} :
    ReflTransGen r' (S.enc a) (S.enc a') ↔ ReflTransGen r a a' :=
  ⟨fun h => S.abs_enc a ▸ S.abs_enc a' ▸ S.reachable_abs h, S.reachable_enc⟩

/-- **Reachability of goals is preserved and reflected**, for a goal `P'` of `r'` that holds,
among the states reachable from `enc a`, exactly at those standing for a state of the goal `P`
of `r`. -/
theorem exists_reachable_enc_iff_of_reachable (S : Simulation r r') {P : α → Prop}
    {P' : β → Prop} (a : α) (hP : ∀ b, ReflTransGen r' (S.enc a) b → (P' b ↔ P (S.abs b))) :
    (∃ b, ReflTransGen r' (S.enc a) b ∧ P' b) ↔ ∃ a', ReflTransGen r a a' ∧ P a' := by
  constructor
  · rintro ⟨b, hb, hPb⟩
    exact ⟨S.abs b, S.abs_enc a ▸ S.reachable_abs hb, (hP b hb).1 hPb⟩
  · rintro ⟨a', ha', hPa'⟩
    have hr := S.reachable_enc ha'
    exact ⟨S.enc a', hr, (hP _ hr).2 ((S.abs_enc a').symm ▸ hPa')⟩

/-- **Reachability of goals is preserved and reflected**, for a goal `P'` of `r'` that holds
exactly at the states standing for a state of the goal `P` of `r`. -/
theorem exists_reachable_enc_iff (S : Simulation r r') {P : α → Prop} {P' : β → Prop}
    (hP : ∀ b, P' b ↔ P (S.abs b)) (a : α) :
    (∃ b, ReflTransGen r' (S.enc a) b ∧ P' b) ↔ ∃ a', ReflTransGen r a a' ∧ P a' :=
  S.exists_reachable_enc_iff_of_reachable a fun b _ => hP b

/-- The identity simulation. -/
@[expose] def refl (r : α → α → Prop) : Simulation r r where
  abs := id
  enc := id
  abs_enc _ := rfl
  step_abs h := .single h
  step_enc h := .single h

/-- The composition of simulations: `r'` simulates `r`, and `r''` simulates `r'`. -/
@[expose] def trans (S : Simulation r r') (T : Simulation r' r'') : Simulation r r'' where
  abs := S.abs ∘ T.abs
  enc := T.enc ∘ S.enc
  abs_enc a := (congrArg S.abs (T.abs_enc (S.enc a))).trans (S.abs_enc a)
  step_abs h := by
    exact reflGen_map S.abs (fun _ _ => S.step_abs) (T.step_abs h)
  step_enc h := T.reachable_enc (S.step_enc h)

/-- A bijection of states that preserves and reflects steps is a simulation. -/
@[expose] def ofEquiv (e : α ≃ β) (h : ∀ a a', r' (e a) (e a') ↔ r a a') : Simulation r r' where
  abs := e.symm
  enc := e
  abs_enc := e.symm_apply_apply
  step_abs hb := .single ((h _ _).1 (by simpa only [Equiv.apply_symm_apply] using hb))
  step_enc ha := .single ((h _ _).2 ha)

end Simulation

/-- Restrict steps to those whose starting state satisfies `I`. -/
@[expose] def Within (r' : β → β → Prop) (I : β → Prop) (b b' : β) : Prop := I b ∧ r' b b'

end Cslib.Complexity.NCL
