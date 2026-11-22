/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import CslibFrontier.Foundations.Computability.GrowingGrammar

open Cslib

private def emptyGrammar : GrowingGrammar Bool where
  NT := Unit
  finiteNT := inferInstance
  initial := ()
  rules := [⟨[Symbol.nonterminal ()], []⟩]
  hasNonterminal := by
    intro d hd
    obtain rfl := List.mem_singleton.mp hd
    exact ⟨(), List.mem_cons_self⟩
  initial_notMem := by
    intro d hd
    obtain rfl := List.mem_singleton.mp hd
    exact List.not_mem_nil
  grows := by
    intro d hd hne
    obtain rfl := List.mem_singleton.mp hd
    exact (hne rfl).elim

/-- The rule from the start symbol to the empty word is permitted. -/
public theorem gcsl_contains_emptyWordLanguage : ∃ L ∈ GCSL Bool, [] ∈ L := by
  refine ⟨emptyGrammar.language, ⟨emptyGrammar, rfl⟩, ?_⟩
  exact Relation.ReflTransGen.single ⟨[], _, [], List.mem_cons_self, rfl, rfl⟩

private def growGrammar : GrowingGrammar Bool where
  NT := Bool
  finiteNT := inferInstance
  initial := false
  rules := [⟨[Symbol.nonterminal false], [Symbol.nonterminal true]⟩,
    ⟨[Symbol.nonterminal true], [Symbol.terminal false, Symbol.terminal true]⟩]
  hasNonterminal := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl)
    · exact ⟨false, List.mem_cons_self⟩
    · exact ⟨true, List.mem_cons_self⟩
  initial_notMem := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl) <;> decide
  grows := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl) h
    · exact (h rfl).elim
    · decide

/-- A start rewrite followed by a strictly growing non-start rewrite gives a two-letter word. -/
example :
    [false, true] ∈ growGrammar.language ∧
    Symbol.nonterminal false ∉
      ([Symbol.terminal false, Symbol.terminal true] : List (Symbol Bool Bool)) ∧
    ([Symbol.nonterminal true] : List (Symbol Bool Bool)).length <
      ([Symbol.terminal false, Symbol.terminal true] : List (Symbol Bool Bool)).length := by
  have first : growGrammar.Produces [Symbol.nonterminal false] [Symbol.nonterminal true] :=
    ⟨[], _, [], List.mem_cons_self, rfl, rfl⟩
  have next : growGrammar.Produces [Symbol.nonterminal true]
      [Symbol.terminal false, Symbol.terminal true] :=
    ⟨[], _, [], List.mem_cons_of_mem _ List.mem_cons_self, rfl, rfl⟩
  have noStart := growGrammar.initial_notMem_of_first_produces first
  exact ⟨(Relation.ReflTransGen.single first).tail next,
    growGrammar.initial_notMem_of_produces next noStart,
    growGrammar.length_lt_of_produces next noStart⟩

/-- A same-length non-start rule violates the growth requirement. -/
example :
    let rule : PostCorrespondence.Domino (Symbol Bool Bool) :=
      ⟨[Symbol.nonterminal true], [Symbol.terminal true]⟩
    ¬ (rule.top ≠ [Symbol.nonterminal false] → rule.top.length < rule.bottom.length) := by
  intro _ grows
  exact (Nat.lt_irrefl 1) (grows (by decide))
