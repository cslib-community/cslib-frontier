/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Computability.WordRewrite
public import Mathlib.Computability.Language

/-!
# Growing context-sensitive grammars

Each rule rewrites a substring containing a nonterminal. Rules strictly increase length
except for rules whose entire left-hand side is the start symbol. The start symbol never
appears on a right-hand side, so the exception is confined to the first rewrite. The induced
language consists of the terminal words derivable from the start symbol.

This is the growing-grammar model of [Dahlhaus and Warmuth][DahlhausWarmuth1986], with the
start-rule convention of [Buntrock and Otto][BuntrockOtto1998].

The [checked examples]
(https://github.com/cslib-community/cslib-frontier/blob/76f5dc9d64/CslibFrontierTests/GrowingGrammar.lean)
exercise the start-rule exception and a derivation with a strictly growing non-start rule.
-/

public section

namespace Cslib

open PostCorrespondence

/-- A strictly length-increasing grammar with a start-rule exception. -/
structure GrowingGrammar (T : Type*) where
  /-- The nonterminal alphabet. -/
  NT : Type
  /-- The nonterminal alphabet is finite. -/
  finiteNT : Finite NT
  /-- The start nonterminal. -/
  initial : NT
  /-- The finitely many string-rewriting rules. -/
  rules : List (Domino (Symbol T NT))
  /-- Each left-hand side contains a nonterminal. -/
  hasNonterminal : ∀ d ∈ rules, ∃ n : NT, Symbol.nonterminal n ∈ d.top
  /-- The start symbol is absent from every right-hand side. -/
  initial_notMem : ∀ d ∈ rules, Symbol.nonterminal initial ∉ d.bottom
  /-- Every rule increases length, except a rewrite of the isolated start symbol. -/
  grows : ∀ d ∈ rules, d.top ≠ [Symbol.nonterminal initial] → d.top.length < d.bottom.length

namespace GrowingGrammar

variable {T : Type*} (G : GrowingGrammar T)

/-- Apply one of the grammar's rules in a word. -/
@[expose] def Produces : List (Symbol T G.NT) → List (Symbol T G.NT) → Prop :=
  Rewrites (· ∈ G.rules)

/-- The language generated from the start symbol. -/
@[expose] def language : Language T :=
  {w | Relation.ReflTransGen G.Produces [Symbol.nonterminal G.initial] (w.map Symbol.terminal)}

/-- Rewriting the isolated start symbol yields a word with no start symbol. -/
theorem initial_notMem_of_first_produces {v : List (Symbol T G.NT)}
    (h : G.Produces [Symbol.nonterminal G.initial] v) : Symbol.nonterminal G.initial ∉ v := by
  obtain ⟨p, d, s, hd, heq, rfl⟩ := h
  obtain ⟨n, hn⟩ := G.hasNonterminal d hd
  have hpos := List.length_pos_of_mem hn
  have hlen := congrArg List.length heq
  simp only [List.length_append, List.length_singleton] at hlen
  have hp : p = [] := List.length_eq_zero_iff.mp (by omega)
  have hs : s = [] := List.length_eq_zero_iff.mp (by omega)
  simpa only [hp, hs, List.nil_append, List.append_nil] using G.initial_notMem d hd

/-- Rewrites preserve the absence of the start symbol. -/
theorem initial_notMem_of_produces {u v : List (Symbol T G.NT)}
    (h : G.Produces u v) (hu : Symbol.nonterminal G.initial ∉ u) :
    Symbol.nonterminal G.initial ∉ v := by
  obtain ⟨p, d, s, hd, rfl, rfl⟩ := h
  simp only [List.mem_append, not_or] at hu ⊢
  exact ⟨⟨hu.1.1, G.initial_notMem d hd⟩, hu.2⟩

/-- Every rewrite of a word without the start symbol strictly increases its length. -/
theorem length_lt_of_produces {u v : List (Symbol T G.NT)}
    (h : G.Produces u v) (hu : Symbol.nonterminal G.initial ∉ u) : u.length < v.length := by
  obtain ⟨p, d, s, hd, rfl, rfl⟩ := h
  have hne : d.top ≠ [Symbol.nonterminal G.initial] := by
    intro htop
    exact hu (by simp [htop])
  have hg := G.grows d hd hne
  simp only [List.length_append]
  omega

end GrowingGrammar

/-- The growing context-sensitive languages over the alphabet `T`. -/
@[expose] def GCSL (T : Type*) : Set (Language T) := {L | ∃ G : GrowingGrammar T, G.language = L}

end Cslib
