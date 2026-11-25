/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.TM0Phases
public import CslibFrontier.Computability.PostCorrespondence.OfTM0
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Set.Finite.List
import Mathlib.Basic.Finite.Prod

/-!
# Single-letter rules for finite-window tape computations

The standard configuration alphabet carries the four-phase head-transfer control. Each rule
replaces two letters by two letters, preserving at least one of them.

## Main results

* `TM0Window.Rules.rule_shape`: single-letter, length-two rules.
* `TM0Window.Rules.step_word`: a phase transition is a standard semi-Thue step.
* `TM0Window.Rules.window_reaches_word`: window computations have fixed-rule rewrite paths.
-/

public section

namespace Cslib.Complexity.NCL.TM0Window
open Turing.TM0Window
open Turing Cslib.PostCorrespondence

/-- Active control and the held-cell tags of each transfer direction. -/
inductive Control (Q : Type*)
  | running (state : Q)
  | rightFirst (state : Q)
  | rightSecond (state : Q)
  | leftFirst (state : Q)
  | leftSecond (state : Q)
  deriving DecidableEq, Fintype

instance {Q : Type*} [Finite Q] : Finite (Control Q) := by
  let := Fintype.ofFinite Q
  infer_instance

/-- Standard configuration letters, with a side bit on tape symbols and phase-tagged control. -/
abbrev Symbol (Γ Q : Type*) := OfTM0.Letter (Γ × Bool) (Control Q)

namespace Rules
variable {Γ Q : Type*}
open OfTM0.Letter

local notation "head" => fun q a => (cell (Control.running q) (a, false) : Symbol Γ Q)
local notation "rL" => fun q a => (cell (Control.rightFirst q) (a, false) : Symbol Γ Q)
local notation "rR" => fun q a => (cell (Control.rightSecond q) (a, false) : Symbol Γ Q)
local notation "lL" => fun q a => (cell (Control.leftFirst q) (a, false) : Symbol Γ Q)
local notation "lR" => fun q a => (cell (Control.leftSecond q) (a, false) : Symbol Γ Q)
local notation "leftSym" => fun a => (sym (a, false) : Symbol Γ Q)
local notation "rightSym" => fun a => (sym (a, true) : Symbol Γ Q)

/-- Place the active fragment between its left- and right-tagged tape cells. -/
@[expose] def frame (L : List Γ) (middle : List (Symbol Γ Q)) (R : List Γ) :
    List (Symbol Γ Q) := lb :: (L.reverse.map leftSym ++ middle ++ R.map rightSym ++ [rb])

/-- The complete word, including its two fixed boundary markers. -/
@[expose] def word : MicroCfg Γ Q → List (Symbol Γ Q)
  | .stable c => frame c.left [head c.state c.scanned] c.right
  | .moving .rightStart c => frame c.left [rL c.state c.first, rightSym c.second] c.right
  | .moving .rightBoth c => frame c.left [rL c.state c.first, rR c.state c.second] c.right
  | .moving .rightEnd c => frame c.left [leftSym c.first, rR c.state c.second] c.right
  | .moving .leftStart c => frame c.left [leftSym c.first, lR c.state c.second] c.right
  | .moving .leftBoth c => frame c.left [lL c.state c.first, lR c.state c.second] c.right
  | .moving .leftEnd c => frame c.left [lL c.state c.first, rightSym c.second] c.right

variable [Inhabited Q]

/-- The fixed local rule family determined by the original machine. -/
inductive Rule (M : TM0.Machine Γ Q) : Domino (Symbol Γ Q) → Prop
  | write {q a q' b} (c : Γ) (transition : M q a = some (q', .write b)) :
      Rule M ⟨[head q a, rightSym c], [head q' b, rightSym c]⟩
  | writeEnd {q a q' b} (transition : M q a = some (q', .write b)) :
      Rule M ⟨[head q a, rb], [head q' b, rb]⟩
  | rightBegin {q a q'} (b : Γ) (transition : M q a = some (q', .move .right)) :
      Rule M ⟨[head q a, rightSym b], [rL q' a, rightSym b]⟩
  | rightMark (q : Q) (a b : Γ) : Rule M ⟨[rL q a, rightSym b], [rL q a, rR q b]⟩
  | rightRelease (q : Q) (a b : Γ) : Rule M ⟨[rL q a, rR q b], [leftSym a, rR q b]⟩
  | rightActivate (q : Q) (a b : Γ) : Rule M ⟨[leftSym a, rR q b], [leftSym a, head q b]⟩
  | leftBegin {q a q'} (b : Γ) (transition : M q a = some (q', .move .left)) :
      Rule M ⟨[leftSym b, head q a], [leftSym b, lR q' a]⟩
  | leftMark (q : Q) (a b : Γ) : Rule M ⟨[leftSym a, lR q b], [lL q a, lR q b]⟩
  | leftRelease (q : Q) (a b : Γ) : Rule M ⟨[lL q a, lR q b], [lL q a, rightSym b]⟩
  | leftActivate (q : Q) (a b : Γ) : Rule M ⟨[lL q a, rightSym b], [head q a, rightSym b]⟩

/-- Every rule has length two and changes at most one letter. -/
theorem rule_shape {M : TM0.Machine Γ Q} {d : Domino (Symbol Γ Q)} (hd : Rule M d) :
    ∃ a b c e, d.top = [a, b] ∧ d.bottom = [c, e] ∧ (a = c ∨ b = e) := by
  cases hd <;> refine ⟨_, _, _, _, rfl, rfl, ?_⟩ <;>
    first | exact Or.inl rfl | exact Or.inr rfl

/-- The rule family is finite and independent of the window length. -/
theorem finite_rule [Finite Γ] [Finite Q] (M : TM0.Machine Γ Q) :
    {d | Rule M d}.Finite := by
  have hf : {w : List (Symbol Γ Q) | w.length ≤ 2}.Finite := List.finite_length_le _ _
  refine ((hf.prod hf).image fun p => (⟨p.1, p.2⟩ : Domino (Symbol Γ Q))).subset fun d hd => ?_
  exact ⟨(d.top, d.bottom), by cases hd <;> simp, rfl⟩

private theorem frame_rewrites {M : TM0.Machine Γ Q} (L R : List Γ)
    {a b c d : Symbol Γ Q} (hr : Rule M ⟨[a, b], [c, d]⟩) :
    Rewrites (Rule M) (frame L [a, b] R) (frame L [c, d] R) :=
  ⟨lb :: L.reverse.map leftSym, ⟨[a, b], [c, d]⟩, R.map rightSym ++ [rb], hr,
    by simp only [frame, List.cons_append, List.append_assoc],
    by simp only [frame, List.cons_append, List.append_assoc]⟩

private theorem stable_step_word {M : TM0.Machine Γ Q} {c : Cfg Γ Q} {d : MicroCfg Γ Q}
    (h : Phases.step M (.stable c) = some d) :
    Rewrites (Rule M) (word (.stable c)) (word d) := by
  rcases c with ⟨q, a, L, R⟩
  cases hM : M q a with
  | none => simp [Phases.step, step, hM] at h
  | some result =>
    rcases result with ⟨q', action⟩
    cases action with
    | write b =>
      simp only [Phases.step, step, hM, Option.map_some, Option.some.injEq] at h
      subst h
      rcases R with _ | ⟨c, R⟩
      · exact ⟨lb :: L.reverse.map leftSym, ⟨[head q a, rb], [head q' b, rb]⟩, [],
          Rule.writeEnd hM, by simp [word, frame], by simp [word, frame]⟩
      · simpa only [word, frame, List.map_cons, List.cons_append, List.nil_append,
          List.append_assoc] using frame_rewrites L R (Rule.write c hM)
    | move direction =>
      cases direction with
      | left =>
        rcases L with _ | ⟨b, L⟩
        · simp [Phases.step, step, hM] at h
        · simp only [Phases.step, step, hM, Option.map_some, Option.some.injEq] at h
          subst h
          simpa only [word, frame, List.reverse_cons, List.map_append, List.map_cons,
            List.map_nil, List.cons_append, List.nil_append, List.append_assoc] using
            frame_rewrites L R (Rule.leftBegin b hM)
      | right =>
        rcases R with _ | ⟨b, R⟩
        · simp [Phases.step, step, hM] at h
        · simp only [Phases.step, step, hM, Option.map_some, Option.some.injEq] at h
          subst h
          simpa only [word, frame, List.map_cons, List.cons_append, List.nil_append,
            List.append_assoc] using frame_rewrites L R (Rule.rightBegin b hM)

/-- Every phase transition executes one actual local rule. -/
theorem step_word {M : TM0.Machine Γ Q} {c d : MicroCfg Γ Q}
    (h : Phases.step M c = some d) : Rewrites (Rule M) (word c) (word d) := by
  rcases c with c | ⟨phase, q, a, b, L, R⟩
  · exact stable_step_word h
  · cases phase <;> simp only [Phases.step, Option.some.injEq] at h <;> subst h
    · exact frame_rewrites L R (Rule.rightMark q a b)
    · exact frame_rewrites L R (Rule.rightRelease q a b)
    · simpa only [word, frame, List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil, List.cons_append, List.nil_append, List.append_assoc] using
        frame_rewrites L R (Rule.rightActivate q a b)
    · exact frame_rewrites L R (Rule.leftMark q a b)
    · exact frame_rewrites L R (Rule.leftRelease q a b)
    · simpa only [word, frame, List.map_cons, List.cons_append, List.nil_append,
        List.append_assoc] using frame_rewrites L R (Rule.leftActivate q a b)

/-- Complete phase computations give standard semi-Thue paths. -/
private theorem reaches_word {M : TM0.Machine Γ Q} {c d : MicroCfg Γ Q}
    (hr : StateTransition.Reaches (Phases.step M) c d) :
    Relation.ReflTransGen (Rewrites (Rule M)) (word c) (word d) :=
  hr.lift word fun _ _ h => step_word h

/-- Window computations use the same fixed single-letter rule family. -/
theorem window_reaches_word {M : TM0.Machine Γ Q} {c d : Cfg Γ Q}
    (hr : StateTransition.Reaches (step M) c d) :
    Relation.ReflTransGen (Rewrites (Rule M)) (word (.stable c)) (word (.stable d)) := by
  obtain ⟨e, he, hre⟩ := StateTransition.tr_reaches (Phases.respects M) rfl hr
  exact he ▸ reaches_word hre

end Rules
end Cslib.Complexity.NCL.TM0Window
