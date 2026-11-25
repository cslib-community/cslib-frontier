/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.TM0Syntax

/-!
# Symmetric fixed-length rewriting of space-bounded computations

The symmetric rewrite graph preserves the partial evaluation of the deterministic phase
machine. Reachability of a halted word therefore agrees with the original forward computation.

## Main results

* `TM0Window.Rules.symmetric_reaches_halted_iff`: exact simulation by a fixed symmetric
  family of length-two, single-letter rules.
-/

public section

namespace Cslib.Complexity.NCL.TM0Window.Rules
open Turing.TM0Window
open Cslib.PostCorrespondence StateTransition
variable {Γ Q : Type*} [Inhabited Q]

/-- The machine rules in both directions. -/
@[expose] def SymmetricRule (M : Turing.TM0.Machine Γ Q) (d : Domino (Symbol Γ Q)) : Prop :=
  Rule M d ∨ Rule M ⟨d.bottom, d.top⟩

private theorem symmetric_rewrites {M : Turing.TM0.Machine Γ Q}
    {u v : List (Symbol Γ Q)} :
    Rewrites (SymmetricRule M) u v ↔ Rewrites (Rule M) u v ∨ Rewrites (Rule M) v u := by
  constructor
  · rintro ⟨p, d, s, hd, hu, hv⟩
    rcases hd with hd | hd
    · exact Or.inl ⟨p, d, s, hd, hu, hv⟩
    · exact Or.inr ⟨p, ⟨d.bottom, d.top⟩, s, hd, hv, hu⟩
  · rintro (⟨p, d, s, hd, hu, hv⟩ | ⟨p, d, s, hd, hv, hu⟩)
    · exact ⟨p, d, s, Or.inl hd, hu, hv⟩
    · exact ⟨p, ⟨d.bottom, d.top⟩, s, Or.inr hd, hu, hv⟩

private theorem eval_eq_of_symmetric_rewrites {M : Turing.TM0.Machine Γ Q}
    {c : MicroCfg Γ Q} {w : List (Symbol Γ Q)}
    (h : Rewrites (SymmetricRule M) (word c) w) :
    ∃ d, word d = w ∧ eval (Phases.step M) c = eval (Phases.step M) d := by
  rcases symmetric_rewrites.mp h with h | h
  · obtain ⟨d, hs, hd⟩ := rewrites_word_iff.mp h
    exact ⟨d, hd, reaches_eval (.single hs)⟩
  · obtain ⟨d, hs, hd⟩ := rewrites_to_word_iff.mp h
    exact ⟨d, hd, (reaches_eval (.single hs)).symm⟩

private theorem eval_eq_of_symmetric_reaches {M : Turing.TM0.Machine Γ Q}
    {c : MicroCfg Γ Q} {w : List (Symbol Γ Q)}
    (h : Relation.ReflTransGen (Rewrites (SymmetricRule M)) (word c) w) :
    ∃ d, word d = w ∧ eval (Phases.step M) c = eval (Phases.step M) d := by
  induction h with
  | refl => exact ⟨c, rfl, rfl⟩
  | tail _ hs ih =>
    obtain ⟨d, rfl, hd⟩ := ih
    obtain ⟨e, he, hde⟩ := eval_eq_of_symmetric_rewrites hs
    exact ⟨e, he, hd.trans hde⟩

/-- Symmetric rewriting reaches a halted word exactly when the original window machine does. -/
theorem symmetric_reaches_halted_iff (M : Turing.TM0.Machine Γ Q) (c d : Cfg Γ Q)
    (hd : Turing.TM0Window.step M d = none) :
    Relation.ReflTransGen (Rewrites (SymmetricRule M)) (word (.stable c)) (word (.stable d)) ↔
      Reaches (Turing.TM0Window.step M) c d := by
  refine ⟨fun hr => ?_, fun hr =>
    Relation.ReflTransGen.mono (fun _ _ h => symmetric_rewrites.mpr (.inl h)) _ _
      (window_reaches_word hr)⟩
  obtain ⟨e, he, hev⟩ := eval_eq_of_symmetric_reaches hr
  obtain rfl := word_injective he
  refine (Phases.reaches_halted_iff M c d hd).mp
    (mem_eval.mp (hev.symm ▸ mem_eval.mpr ⟨.refl, ?_⟩)).1
  simp only [Phases.step, hd, Option.map_none]

end Cslib.Complexity.NCL.TM0Window.Rules
