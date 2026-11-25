/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Window
public import CslibFrontier.Computability.PostCorrespondence.Rewrite
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Local word-reconfiguration gadgets for two-letter rewrite rules

A fixed family of two-letter rewrite rules determines a finite compatibility digraph.
Overlapping pairs encode the source letters; one special symbol per rule temporarily replaces
the pair on which the rule acts.

## Main definitions

* `HWord.RewriteGadget.Rule`: a two-letter rule changing at most one letter.
* `HWord.RewriteGadget.compatibility`: the finite digraph of pairs and rule markers.

## Main results

* `HWord.RewriteGadget.rule_in_window`: every rule has a three-move realization inside an
  arbitrary legal ambient word, preserving all positions outside its window.
* `HWord.RewriteGadget.marker_left_rewrites`, `HWord.RewriteGadget.marker_right_rewrites`:
  changed letters next to a rule marker yield an actual semi-Thue rewriting step.

## References

* [M. Wrochna, *Reconfiguration in bounded bandwidth and treedepth*][Wrochna2014],
  arXiv:1405.0847v1, Section 3, proof of Theorem 3.
-/

public section

namespace Cslib.Complexity.NCL.HWord.RewriteGadget

open Cslib.PostCorrespondence

/-- A two-letter rewriting rule that changes at most one of its positions. -/
structure Rule (q : ℕ) where
  /-- First source letter. -/
  first : Fin q
  /-- Second source letter. -/
  second : Fin q
  /-- First target letter. -/
  first' : Fin q
  /-- Second target letter. -/
  second' : Fin q
  /-- At least one context letter is preserved. -/
  oneChange : first = first' ∨ second = second'

/-- The source domino, using the standard semi-Thue representation. -/
@[expose] def Rule.domino {q : ℕ} (rule : Rule q) : Domino (Fin q) :=
  ⟨[rule.first, rule.second], [rule.first', rule.second']⟩

/-- The same local rule in the reverse direction. -/
@[expose] def Rule.reverse {q : ℕ} (rule : Rule q) : Rule q where
  first := rule.first'
  second := rule.second'
  first' := rule.first
  second' := rule.second
  oneChange := rule.oneChange.elim (Or.inl ∘ Eq.symm) (Or.inr ∘ Eq.symm)

/-- Pair symbols, end markers, and one temporary symbol for each fixed rule. -/
inductive Symbol (q r : ℕ)
  /-- Left end marker. -/
  | start
  /-- Right end marker. -/
  | finish
  /-- Temporary symbol authorizing one rule. -/
  | marker (rule : Fin r)
  /-- Overlapping source letters; `none` is an exterior blank. -/
  | pair (left right : Option (Fin q))
  deriving DecidableEq, Fintype

variable {q r : ℕ} (rules : Fin r → Rule q)

/-- The fixed symmetric family of standard two-letter semi-Thue dominoes. -/
@[expose] def RuleSet (d : Domino (Fin q)) : Prop :=
  ∃ i, d = (rules i).domino ∨ d = (rules i).reverse.domino

/-- Directed compatibility for overlapping pairs and rule markers. Shared coordinates and
coordinates facing rule markers are source letters; end markers require exterior blanks. -/
@[expose] def Compatible : Symbol q r → Symbol q r → Prop
  | .pair _ b, .pair c _ => ∃ a : Fin q, b = some a ∧ c = some a
  | .start, .pair a b => a = none ∧ ∃ c : Fin q, b = some c
  | .pair a b, .finish => b = none ∧ ∃ c : Fin q, a = some c
  | .pair _ b, .marker i => b = some (rules i).first ∨ b = some (rules i).first'
  | .marker i, .pair a _ => a = some (rules i).second ∨ a = some (rules i).second'
  | _, _ => False

instance : DecidableRel (Compatible rules) := fun a b => by
  cases a <;> cases b <;> unfold Compatible <;> infer_instance

/-- A fixed enumeration of the compiled finite alphabet. -/
noncomputable def code : Symbol q r ≃ Fin (Fintype.card (Symbol q r)) :=
  Fintype.equivFin _

/-- The compiled compatibility digraph, over a fixed finite alphabet. -/
noncomputable def compatibility : Digraph (Fin (Fintype.card (Symbol q r))) where
  Adj a b := Compatible rules (code.symm a) (code.symm b)

noncomputable instance : DecidableRel (compatibility rules).Adj :=
  fun a b => inferInstanceAs (Decidable (Compatible rules (code.symm a) (code.symm b)))

/-- Coding the finite alphabet preserves exactly the specified directed edges. -/
theorem compatibility_adj (a b : Symbol q r) :
    (compatibility rules).Adj (code a) (code b) ↔ Compatible rules a b := by
  change Compatible rules (code.symm (code a)) (code.symm (code b)) ↔ _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

private theorem incoming_pair (v : Symbol q r) (a : Option (Fin q)) (b c : Fin q) :
    Compatible rules v (.pair a (some b)) ↔ Compatible rules v (.pair a (some c)) := by
  cases v <;> simp [Compatible]

private theorem outgoing_pair (a : Option (Fin q)) (b c : Fin q) (v : Symbol q r) :
    Compatible rules (.pair (some b) a) v ↔ Compatible rules (.pair (some c) a) v := by
  cases v <;> simp [Compatible]

/-- A three-symbol rewriting window framed by its two immediate outside neighbors. -/
@[expose] noncomputable def segment (a b c d e : Symbol q r) :
    Fin 5 → Fin (Fintype.card (Symbol q r)) :=
  code ∘ ![a, b, c, d, e]

private theorem legal_row {a b c d e : Symbol q r}
    (hab : Compatible rules a b) (hbc : Compatible rules b c)
    (hcd : Compatible rules c d) (hde : Compatible rules d e) :
    HWord.Legal (compatibility rules) (segment a b c d e) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals
    apply (compatibility_adj rules _ _).mpr
    assumption

private theorem framed_change {v a b c w a' b' c' : Symbol q r}
    (hs : HWord.Legal (compatibility rules) (segment v a b c w))
    (ht : HWord.Legal (compatibility rules) (segment v a' b' c' w))
    (i : Fin 5) (he : ∀ j, j ≠ i → segment v a b c w j = segment v a' b' c' w j) :
    Relation.ReflTransGen (Window.FramedStep (compatibility rules) (by decide) (code v) (code w))
      (segment v a b c w) (segment v a' b' c' w) := by
  by_cases hi : segment v a b c w i = segment v a' b' c' w i
  · have heq : segment v a b c w = segment v a' b' c' w :=
      funext fun j => if hj : j = i then hj ▸ hi else he j hj
    exact heq ▸ Relation.ReflTransGen.refl
  · exact .single ⟨⟨hs, ht, i, hi, he⟩, rfl, rfl, rfl, rfl⟩

private theorem framed_middle {v a b c w b' : Symbol q r}
    (hs : HWord.Legal (compatibility rules) (segment v a b c w))
    (ht : HWord.Legal (compatibility rules) (segment v a b' c w)) :
    Relation.ReflTransGen (Window.FramedStep (compatibility rules) (by decide) (code v) (code w))
      (segment v a b c w) (segment v a b' c w) := by
  apply framed_change rules hs ht 2
  intro j hj
  fin_cases j <;> simp_all [segment]

private theorem rule_reachable_framed (i : Fin r) (left right : Option (Fin q)) (v w : Symbol q r)
    (hv : Compatible rules v (.pair left (some (rules i).first)))
    (hw : Compatible rules (.pair (some (rules i).second) right) w) :
    Relation.ReflTransGen (Window.FramedStep (compatibility rules) (by decide) (code v) (code w))
      (segment v (.pair left (some (rules i).first))
        (.pair (some (rules i).first) (some (rules i).second))
        (.pair (some (rules i).second) right) w)
      (segment v (.pair left (some (rules i).first'))
        (.pair (some (rules i).first') (some (rules i).second'))
        (.pair (some (rules i).second') right) w) := by
  have hleft : Compatible rules v (.pair left (some (rules i).first')) :=
    (incoming_pair rules v left _ _).mp hv
  have hright : Compatible rules (.pair (some (rules i).second') right) w :=
    (outgoing_pair rules right _ _ w).mp hw
  have hs := legal_row rules (c := .pair (some (rules i).first) (some (rules i).second))
    hv (by simp [Compatible]) (by simp [Compatible]) hw
  have ht := legal_row rules (c := .pair (some (rules i).first') (some (rules i).second'))
    hleft (by simp [Compatible]) (by simp [Compatible]) hright
  have hmarker := legal_row rules (c := .marker i)
    hv (by simp [Compatible]) (by simp [Compatible]) hw
  have hmarker' := legal_row rules (c := .marker i)
    hleft (by simp [Compatible]) (by simp [Compatible]) hright
  have hstart := framed_middle rules hs hmarker
  have hend := framed_middle rules hmarker' ht
  apply hstart.trans
  apply Relation.ReflTransGen.trans ?_ hend
  rcases (rules i).oneChange with h | h
  · apply framed_change rules hmarker hmarker' 3
    intro j hj
    fin_cases j <;> simp_all [segment]
  · apply framed_change rules hmarker hmarker' 1
    intro j hj
    fin_cases j <;> simp_all [segment]

/-- Every source rule is realized inside an arbitrary-length legal H-word. The framing
condition identifies its original pair encoding, and the two outside neighbors stay fixed. -/
theorem rule_in_window {n : ℕ} (window : Window n 5)
    (base : Fin n → Fin (Fintype.card (Symbol q r)))
    (hb : HWord.Legal (compatibility rules) base)
    (i : Fin r) (left right : Option (Fin q)) (v w : Symbol q r)
    (hv : Compatible rules v (.pair left (some (rules i).first)))
    (hw : Compatible rules (.pair (some (rules i).second) right) w)
    (he : ∀ j, segment v (.pair left (some (rules i).first))
      (.pair (some (rules i).first) (some (rules i).second))
      (.pair (some (rules i).second) right) w j = base (window.get j)) :
    HWord.Reachable (compatibility rules) base
      (window.patch base (segment v (.pair left (some (rules i).first'))
        (.pair (some (rules i).first') (some (rules i).second'))
        (.pair (some (rules i).second') right) w)) := by
  have hr := rule_reachable_framed rules i left right v w hv hw
  have hfirst : code v = base (window.get 0) := by simpa [segment] using he 0
  have hlast : code w = base (window.get 4) := by simpa [segment] using he 4
  rw [hfirst, hlast] at hr
  have hpath := window.reachable_patch (by decide) hb hr
  rw [window.patch_eq he] at hpath
  exact hpath

private theorem choice_pair {a a' x y : Fin q}
    (hx : x = a ∨ x = a') (hy : y = a ∨ y = a') (hne : x ≠ y) :
    (x = a ∧ y = a') ∨ (x = a' ∧ y = a) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hne
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩
  · exact absurd rfl hne

private theorem rule_domino_rewrites (i : Fin r) {a b a' b' : Fin q}
    (h : (a = (rules i).first ∧ b = (rules i).second ∧
          a' = (rules i).first' ∧ b' = (rules i).second') ∨
      (a = (rules i).first' ∧ b = (rules i).second' ∧
          a' = (rules i).first ∧ b' = (rules i).second)) :
    Rewrites (RuleSet rules) [a, b] [a', b'] := by
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨[], (rules i).domino, [], ⟨i, .inl rfl⟩, rfl, rfl⟩
  · exact ⟨[], (rules i).reverse.domino, [], ⟨i, .inr rfl⟩, rfl, rfl⟩

/-- A change immediately after a rule marker is an actual source rewrite on its two letters. -/
theorem marker_right_rewrites (i : Fin r) (c x y : Fin q)
    (left right right' : Option (Fin q))
    (hc : Compatible rules (.pair left (some c)) (.marker i))
    (hx : Compatible rules (.marker i) (.pair (some x) right))
    (hy : Compatible rules (.marker i) (.pair (some y) right')) (hne : x ≠ y) :
    Rewrites (RuleSet rules) [c, x] [c, y] := by
  simp only [Compatible, Option.some.injEq] at hc hx hy
  rcases (rules i).oneChange with hf | hs
  · have hc' : c = (rules i).first := hc.elim id (·.trans hf.symm)
    exact rule_domino_rewrites rules i
      ((choice_pair hx hy hne).imp (fun ⟨h1, h2⟩ => ⟨hc', h1, hc'.trans hf, h2⟩)
        fun ⟨h1, h2⟩ => ⟨hc'.trans hf, h1, hc', h2⟩)
  · exact (choice_pair hx hy hne).elim (fun ⟨h1, h2⟩ => absurd (h1.trans (hs.trans h2.symm)) hne)
      fun ⟨h1, h2⟩ => absurd (h1.trans (hs.symm.trans h2.symm)) hne

/-- A change immediately before a rule marker is an actual source rewrite on its two letters. -/
theorem marker_left_rewrites (i : Fin r) (c x y : Fin q)
    (left left' right : Option (Fin q))
    (hc : Compatible rules (.marker i) (.pair (some c) right))
    (hx : Compatible rules (.pair left (some x)) (.marker i))
    (hy : Compatible rules (.pair left' (some y)) (.marker i)) (hne : x ≠ y) :
    Rewrites (RuleSet rules) [x, c] [y, c] := by
  simp only [Compatible, Option.some.injEq] at hc hx hy
  rcases (rules i).oneChange with hf | hs
  · exact (choice_pair hx hy hne).elim (fun ⟨h1, h2⟩ => absurd (h1.trans (hf.trans h2.symm)) hne)
      fun ⟨h1, h2⟩ => absurd (h1.trans (hf.symm.trans h2.symm)) hne
  · have hc' : c = (rules i).second := hc.elim id (·.trans hs.symm)
    exact rule_domino_rewrites rules i
      ((choice_pair hx hy hne).imp (fun ⟨h1, h2⟩ => ⟨h1, hc', h2, hc'.trans hs⟩)
        fun ⟨h1, h2⟩ => ⟨h1, hc'.trans hs, h2, hc'⟩)

end Cslib.Complexity.NCL.HWord.RewriteGadget
