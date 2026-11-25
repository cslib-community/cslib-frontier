/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.TM0Decode
import Mathlib.Data.List.Chain

/-!
# Local syntax of phased tape words

The side tags force every rewriting window to lie between a left-symbol prefix and a
right-symbol suffix. This recovers a machine transition from an arbitrary rule occurrence.

## Main results

* `TM0Window.Rules.rewrites_word_iff`: local rule occurrences are exactly machine phases.
* `TM0Window.Rules.rewrites_to_word_iff`: reverse occurrences also recover a machine phase.
-/

public section

namespace Cslib.Complexity.NCL.TM0Window.Rules
open Turing.TM0Window
open Cslib.PostCorrespondence.OfTM0.Letter
variable {Γ Q : Type*}

private def Entry : Symbol Γ Q → Prop
  | sym (_, false) | cell (.running _) (_, false) | cell (.rightFirst _) (_, false)
    | cell (.leftFirst _) (_, false) => True
  | _ => False

private def Exit : Symbol Γ Q → Prop
  | sym (_, true) | cell (.running _) (_, false) | cell (.rightSecond _) (_, false)
    | cell (.leftSecond _) (_, false) => True
  | _ => False

private def Compatible : Symbol Γ Q → Symbol Γ Q → Prop
  | lb, x => Entry x
  | sym (_, false), sym (_, false) => True
  | sym (_, false), cell _ (_, false) => True
  | cell _ (_, false), sym (_, true) => True
  | cell (.rightFirst q) (_, false), cell (.rightSecond q') (_, false) => q = q'
  | cell (.leftFirst q) (_, false), cell (.leftSecond q') (_, false) => q = q'
  | cell (.running _) (_, false), rb | cell (.rightSecond _) (_, false), rb
    | cell (.leftSecond _) (_, false), rb => True
  | sym (_, true), sym (_, true) | sym (_, true), rb => True
  | _, _ => False

private theorem incoming_entry {x a : Symbol Γ Q} (ha : Entry a) (h : Compatible x a) :
    x = lb ∨ ∃ b, x = sym (b, false) := by
  rcases a with ⟨a, _ | _⟩ | ⟨q, a, _ | _⟩ | _ | _ | _ <;> try exact ha.elim
  all_goals ((try cases q) <;> try exact ha.elim)
  all_goals rcases x with ⟨b, _ | _⟩ | ⟨q', b, _ | _⟩ | _ | _ | _ <;>
    (try cases q') <;> simp_all [Compatible, Entry]

private theorem outgoing_exit {a x : Symbol Γ Q} (ha : Exit a) (h : Compatible a x) :
    x = rb ∨ ∃ b, x = sym (b, true) := by
  rcases a with ⟨a, _ | _⟩ | ⟨q, a, _ | _⟩ | _ | _ | _ <;> try exact ha.elim
  all_goals ((try cases q) <;> try exact ha.elim)
  all_goals rcases x with ⟨b, _ | _⟩ | ⟨q', b, _ | _⟩ | _ | _ | _ <;>
    (try cases q') <;> simp_all [Compatible, Exit]

private theorem not_into_lb (x : Symbol Γ Q) : ¬Compatible x lb := by
  cases x <;> simp [Compatible, Entry]

private theorem chain_to_lb (p : List (Symbol Γ Q))
    (h : (p ++ [lb]).IsChain Compatible) : p = [] := by
  cases p using List.reverseRecOn with
  | nil => rfl
  | append_singleton p x =>
    have h' : (p ++ [x]).IsChain Compatible ∧ Compatible x lb := by
      simpa only [List.append_assoc, List.singleton_append, List.isChain_append_cons_cons,
        List.isChain_singleton, and_true] using h
    exact (not_into_lb x h'.2).elim

private theorem left_context {a : Symbol Γ Q} (p : List (Symbol Γ Q))
    (hc : (p ++ [a]).IsChain Compatible) (hh : (p ++ [a]).head? = some lb) (ha : Entry a) :
    ∃ L : List Γ, p = lb :: L.reverse.map (fun b => sym (b, false)) := by
  induction p using List.reverseRecOn generalizing a with
  | nil =>
    simp only [List.nil_append, List.head?_cons, Option.some.injEq] at hh
    subst a; contradiction
  | append_singleton p x ih =>
    have hs : (p ++ [x]).IsChain Compatible ∧ Compatible x a := by
      simpa only [List.append_assoc, List.singleton_append, List.isChain_append_cons_cons,
        List.isChain_singleton, and_true] using hc
    rcases incoming_entry ha hs.2 with rfl | ⟨b, rfl⟩
    · exact ⟨[], by rw [chain_to_lb p hs.1]; rfl⟩
    · obtain ⟨L, hL⟩ := ih hs.1
        (by cases p <;> simpa only [List.nil_append, List.cons_append, List.head?_cons] using hh)
        trivial
      exact ⟨b :: L, by simp [hL, List.reverse_cons]⟩

private theorem not_from_rb (x : Symbol Γ Q) : ¬Compatible rb x := by
  cases x <;> simp [Compatible]

private theorem chain_from_rb (s : List (Symbol Γ Q))
    (h : (rb :: s).IsChain Compatible) : s = [] := by
  cases s with
  | nil => rfl
  | cons x _ => exact (not_from_rb x h.rel).elim

private theorem right_context {b : Symbol Γ Q} (s : List (Symbol Γ Q))
    (hc : (b :: s).IsChain Compatible) (hh : (b :: s).getLast? = some rb) (hb : Exit b) :
    ∃ R : List Γ, s = R.map (fun a => sym (a, true)) ++ [rb] := by
  induction s generalizing b with
  | nil =>
    simp only [List.getLast?_singleton, Option.some.injEq] at hh
    subst b; contradiction
  | cons x s ih =>
    rcases outgoing_exit hb hc.rel with rfl | ⟨a, rfl⟩
    · exact ⟨[], by rw [chain_from_rb s hc.tail]; rfl⟩
    · obtain ⟨R, rfl⟩ := ih hc.tail (by simpa only [List.getLast?_cons_cons] using hh) trivial
      exact ⟨a :: R, rfl⟩

private theorem entry_compatible_left (a : Γ) {x : Symbol Γ Q} (hx : Entry x) :
    Compatible (sym (a, false)) x := by
  rcases x with ⟨b, _ | _⟩ | ⟨q, b, _ | _⟩ | _ | _ | _ <;>
    (try cases q) <;> simp_all [Entry, Compatible]

private theorem exit_compatible_right {x : Symbol Γ Q} (hx : Exit x) (a : Γ) :
    Compatible x (sym (a, true)) := by
  rcases x with ⟨b, _ | _⟩ | ⟨q, b, _ | _⟩ | _ | _ | _ <;>
    (try cases q) <;> simp_all [Exit, Compatible]

private theorem exit_compatible_rb {x : Symbol Γ Q} (hx : Exit x) : Compatible x rb := by
  rcases x with ⟨b, _ | _⟩ | ⟨q, b, _ | _⟩ | _ | _ | _ <;>
    (try cases q) <;> simp_all [Exit, Compatible]

private theorem chain_right {x : Symbol Γ Q} (hx : Exit x) (R : List Γ) :
    (x :: (R.map (fun a => sym (a, true)) ++ [rb])).IsChain Compatible := by
  induction R generalizing x with
  | nil => exact .cons_cons (exit_compatible_rb hx) (.singleton _)
  | cons a R ih => exact .cons_cons (exit_compatible_right hx a) (ih trivial)

private theorem chain_left {x : Symbol Γ Q} {s : List (Symbol Γ Q)}
    (hx : Entry x) (hc : (x :: s).IsChain Compatible) (L : List Γ) :
    (lb :: (L.map (fun a => sym (a, false)) ++ x :: s)).IsChain Compatible := by
  induction L with
  | nil => exact .cons_cons hx hc
  | cons a L ih =>
    apply List.IsChain.cons_cons (show Compatible lb (sym (a, false)) from trivial)
    cases L with
    | nil => exact .cons_cons (entry_compatible_left a hx) hc
    | cons b L => exact .cons_cons trivial ih.tail

private theorem frame_chain {x y : Symbol Γ Q} (L R : List Γ) (hx : Entry x) (hy : Exit y)
    (hxy : Compatible x y) : (frame L [x, y] R).IsChain Compatible := by
  simpa only [frame, List.append_assoc, List.cons_append, List.nil_append] using
    chain_left hx (.cons_cons hxy (chain_right hy R)) L.reverse

private theorem word_isChain (c : MicroCfg Γ Q) : (word c).IsChain Compatible := by
  cases c with
  | stable c =>
    simpa only [word, frame, List.append_assoc, List.cons_append, List.nil_append] using
      chain_left (x := cell (.running c.state) (c.scanned, false)) trivial
        (chain_right (x := cell (.running c.state) (c.scanned, false)) trivial c.right)
        c.left.reverse
  | moving phase c =>
    cases phase <;> exact frame_chain c.left c.right trivial trivial (by simp [Compatible])

private theorem word_head (c : MicroCfg Γ Q) : (word c).head? = some lb := by
  cases c with
  | stable c => rfl
  | moving phase c => cases phase <;> rfl

private theorem word_last (c : MicroCfg Γ Q) : (word c).getLast? = some rb := by
  cases c with
  | stable c => simp only [word, frame, ← List.cons_append, List.getLast?_append]; rfl
  | moving phase c =>
    cases phase <;> simp only [word, frame, ← List.cons_append, List.getLast?_append] <;> rfl

private theorem prefix_context {c : MicroCfg Γ Q} {a b : Symbol Γ Q}
    {p s : List (Symbol Γ Q)} (hw : p ++ [a, b] ++ s = word c) (ha : Entry a) :
    ∃ L : List Γ, p = lb :: L.reverse.map (fun b => sym (b, false)) := by
  have hc := hw ▸ word_isChain c
  have hh := hw ▸ word_head c
  simp only [List.append_assoc, List.cons_append, List.nil_append,
    List.isChain_append_cons_cons] at hc
  exact left_context p hc.1
    (by cases p <;> simpa only [List.nil_append, List.cons_append, List.head?_cons] using hh) ha

private theorem suffix_context {c : MicroCfg Γ Q} {a b : Symbol Γ Q}
    {p s : List (Symbol Γ Q)} (hw : p ++ [a, b] ++ s = word c) (hb : Exit b) :
    ∃ R : List Γ, s = R.map (fun b => sym (b, true)) ++ [rb] := by
  have hc := hw ▸ word_isChain c
  have hh := hw ▸ word_last c
  simp only [List.append_assoc, List.cons_append, List.nil_append,
    List.isChain_append_cons_cons] at hc
  exact right_context s hc.2.2 (by simpa only [List.append_assoc, List.cons_append,
    List.nil_append, List.getLast?_append_cons, List.getLast?_cons_cons] using hh) hb

private theorem end_context {c : MicroCfg Γ Q} {a : Symbol Γ Q}
    {p s : List (Symbol Γ Q)} (hw : p ++ [a, rb] ++ s = word c) : s = [] := by
  have hc := hw ▸ word_isChain c
  simp only [List.append_assoc, List.cons_append, List.nil_append,
    List.isChain_append_cons_cons] at hc
  exact chain_from_rb s hc.2.2

private theorem pair_context_either {c : MicroCfg Γ Q} {a b a' b' : Symbol Γ Q}
    {p s : List (Symbol Γ Q)}
    (hw : p ++ [a, b] ++ s = word c ∨ p ++ [a', b'] ++ s = word c)
    (ha : Entry a) (hb : Exit b) (ha' : Entry a') (hb' : Exit b') :
    ∃ L R : List Γ, p = lb :: L.reverse.map (fun b => sym (b, false)) ∧
      s = R.map (fun b => sym (b, true)) ++ [rb] := by
  rcases hw with hw | hw
  · exact let ⟨L, hL⟩ := prefix_context hw ha; let ⟨R, hR⟩ := suffix_context hw hb
      ⟨L, R, hL, hR⟩
  · exact let ⟨L, hL⟩ := prefix_context hw ha'; let ⟨R, hR⟩ := suffix_context hw hb'
      ⟨L, R, hL, hR⟩

private theorem end_context_either {c : MicroCfg Γ Q} {a a' : Symbol Γ Q}
    {p s : List (Symbol Γ Q)}
    (hw : p ++ [a, rb] ++ s = word c ∨ p ++ [a', rb] ++ s = word c)
    (ha : Entry a) (ha' : Entry a') :
    ∃ L : List Γ, p = lb :: L.reverse.map (fun b => sym (b, false)) ∧ s = [] := by
  rcases hw with hw | hw
  · exact let ⟨L, hL⟩ := prefix_context hw ha; ⟨L, hL, end_context hw⟩
  · exact let ⟨L, hL⟩ := prefix_context hw ha'; ⟨L, hL, end_context hw⟩

variable [Inhabited Q]
open Cslib.PostCorrespondence

private abbrev Occurrence (M : Turing.TM0.Machine Γ Q)
    (p s : List (Symbol Γ Q)) (d : Domino (Symbol Γ Q)) : Prop :=
  ∃ a b : MicroCfg Γ Q, word a = p ++ d.top ++ s ∧ word b = p ++ d.bottom ++ s ∧
    Phases.step M a = some b

private theorem write_occurrence {M : Turing.TM0.Machine Γ Q} {q q' : Q} {a b : Γ}
    {p s : List (Symbol Γ Q)} {c : MicroCfg Γ Q} (t : Γ)
    (hM : M q a = some (q', .write b))
    (hw : p ++ [cell (.running q) (a, false), sym (t, true)] ++ s = word c ∨
      p ++ [cell (.running q') (b, false), sym (t, true)] ++ s = word c) :
    Occurrence M p s ⟨[cell (.running q) (a, false), sym (t, true)],
      [cell (.running q') (b, false), sym (t, true)]⟩ := by
  obtain ⟨L, R, rfl, rfl⟩ := pair_context_either hw trivial trivial trivial trivial
  refine ⟨.stable ⟨q, a, L, t :: R⟩, .stable ⟨q', b, L, t :: R⟩, ?_, ?_,
    by simp [Phases.step, step, hM]⟩ <;> simp [word, frame]

private theorem writeEnd_occurrence {M : Turing.TM0.Machine Γ Q} {q q' : Q} {a b : Γ}
    {p s : List (Symbol Γ Q)} {c : MicroCfg Γ Q}
    (hM : M q a = some (q', .write b))
    (hw : p ++ [cell (.running q) (a, false), rb] ++ s = word c ∨
      p ++ [cell (.running q') (b, false), rb] ++ s = word c) :
    Occurrence M p s ⟨[cell (.running q) (a, false), rb],
      [cell (.running q') (b, false), rb]⟩ := by
  obtain ⟨L, rfl, rfl⟩ := end_context_either hw trivial trivial
  refine ⟨.stable ⟨q, a, L, []⟩, .stable ⟨q', b, L, []⟩, ?_, ?_,
    by simp [Phases.step, step, hM]⟩ <;> simp [word, frame]

private theorem rule_occurrence {M : Turing.TM0.Machine Γ Q} {d : Domino (Symbol Γ Q)}
    {p s : List (Symbol Γ Q)} {c : MicroCfg Γ Q} (hd : Rule M d)
    (hw : p ++ d.top ++ s = word c ∨ p ++ d.bottom ++ s = word c) :
    Occurrence M p s d := by
  cases hd with
  | write t hM => exact write_occurrence t hM hw
  | writeEnd hM => exact writeEnd_occurrence hM hw
  | @rightBegin q a q' b hM =>
    obtain ⟨L, R, rfl, rfl⟩ := pair_context_either hw trivial trivial trivial trivial
    refine ⟨.stable ⟨q, a, L, b :: R⟩, .moving .rightStart ⟨q', a, b, L, R⟩, ?_, ?_,
      by simp [Phases.step, step, hM]⟩ <;> simp [word, frame]
  | rightMark q a b =>
    obtain ⟨L, R, rfl, rfl⟩ := pair_context_either hw trivial trivial trivial trivial
    refine ⟨.moving .rightStart ⟨q, a, b, L, R⟩, .moving .rightBoth ⟨q, a, b, L, R⟩, ?_, ?_, rfl⟩
      <;> simp [word, frame]
  | rightRelease q a b =>
    obtain ⟨L, R, rfl, rfl⟩ := pair_context_either hw trivial trivial trivial trivial
    refine ⟨.moving .rightBoth ⟨q, a, b, L, R⟩, .moving .rightEnd ⟨q, a, b, L, R⟩, ?_, ?_, rfl⟩
      <;> simp [word, frame]
  | rightActivate q a b =>
    obtain ⟨L, R, rfl, rfl⟩ := pair_context_either hw trivial trivial trivial trivial
    refine ⟨.moving .rightEnd ⟨q, a, b, L, R⟩, .stable ⟨q, b, a :: L, R⟩, ?_, ?_, rfl⟩ <;>
      simp [word, frame, List.reverse_cons]
  | @leftBegin q a q' b hM =>
    obtain ⟨L, R, rfl, rfl⟩ := pair_context_either hw trivial trivial trivial trivial
    refine ⟨.stable ⟨q, a, b :: L, R⟩, .moving .leftStart ⟨q', b, a, L, R⟩, ?_, ?_,
      by simp [Phases.step, step, hM]⟩ <;> simp [word, frame, List.reverse_cons]
  | leftMark q a b =>
    obtain ⟨L, R, rfl, rfl⟩ := pair_context_either hw trivial trivial trivial trivial
    refine ⟨.moving .leftStart ⟨q, a, b, L, R⟩, .moving .leftBoth ⟨q, a, b, L, R⟩, ?_, ?_, rfl⟩
      <;> simp [word, frame]
  | leftRelease q a b =>
    obtain ⟨L, R, rfl, rfl⟩ := pair_context_either hw trivial trivial trivial trivial
    refine ⟨.moving .leftBoth ⟨q, a, b, L, R⟩, .moving .leftEnd ⟨q, a, b, L, R⟩, ?_, ?_, rfl⟩
      <;> simp [word, frame]
  | leftActivate q a b =>
    obtain ⟨L, R, rfl, rfl⟩ := pair_context_either hw trivial trivial trivial trivial
    refine ⟨.moving .leftEnd ⟨q, a, b, L, R⟩, .stable ⟨q, a, L, b :: R⟩, ?_, ?_, rfl⟩
      <;> simp [word, frame]

/-- Every forward rewrite from a phased word is its actual deterministic transition. -/
theorem rewrites_word_iff {M : Turing.TM0.Machine Γ Q} {c : MicroCfg Γ Q}
    {w : List (Symbol Γ Q)} :
    Rewrites (Rule M) (word c) w ↔ ∃ d, Phases.step M c = some d ∧ word d = w := by
  classical
  refine ⟨?_, fun ⟨d, hs, h⟩ => h ▸ step_word hs⟩
  rintro ⟨p, d, s, hd, hc, rfl⟩
  obtain ⟨a, b, ha, hb, hs⟩ := rule_occurrence hd (Or.inl hc.symm)
  exact ⟨b, word_injective (ha.trans hc.symm) ▸ hs, hb⟩

/-- Every reverse rewrite into a phased word recovers an actual predecessor. -/
theorem rewrites_to_word_iff {M : Turing.TM0.Machine Γ Q} {c : MicroCfg Γ Q}
    {w : List (Symbol Γ Q)} :
    Rewrites (Rule M) w (word c) ↔ ∃ d, Phases.step M d = some c ∧ word d = w := by
  classical
  refine ⟨?_, fun ⟨d, hs, h⟩ => h ▸ step_word hs⟩
  rintro ⟨p, d, s, hd, rfl, hc⟩
  obtain ⟨a, b, ha, hb, hs⟩ := rule_occurrence hd (Or.inr hc.symm)
  exact ⟨a, word_injective (hb.trans hc.symm) ▸ hs, ha⟩

end Cslib.Complexity.NCL.TM0Window.Rules
