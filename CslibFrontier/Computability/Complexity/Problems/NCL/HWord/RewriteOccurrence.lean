/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.RewriteEncoding
import Mathlib.Data.List.OfFn

/-!
# Recovering indexed occurrences from semi-Thue rewriting

The standard context-and-domino semantics supplies an indexed occurrence of a two-letter
rule. This connects arbitrary source rewriting steps to the complete canonical-word macros.

## Main results

* `HWord.RewriteGadget.application_of_rewrites`: extract an occurrence in either rule direction.
* `HWord.RewriteGadget.word_reachable_of_rewrites`: every source rewrite reconfigures the
  complete canonical word.
-/

public section

namespace Cslib.Complexity.NCL.HWord.RewriteGadget

open Cslib.PostCorrespondence

variable {n q r : ℕ}

instance (rules : Fin r → Rule q) : Std.Symm (Rewrites (RuleSet rules)) where
  symm s t h := by
    obtain ⟨before, domino, after, ⟨i, hd | hd⟩, hs, ht⟩ := h
    · subst domino
      exact ⟨before, (rules i).reverse.domino, after, ⟨i, Or.inr rfl⟩, ht, hs⟩
    · subst domino
      exact ⟨before, (rules i).domino, after, ⟨i, Or.inl rfl⟩, ht, hs⟩

private theorem pair_lookup {α : Type} (before after : List α) (a b : α) :
    (before ++ [a, b] ++ after)[before.length]? = some a ∧
      (before ++ [a, b] ++ after)[before.length + 1]? = some b := by
  constructor
  · rw [List.append_assoc, List.getElem?_append_right (by omega)]
    simp
  · rw [List.append_assoc, List.getElem?_append_right (by omega)]
    simp

private theorem application_of_context (rule : Rule q) {s t : Fin n → Fin q}
    (before after : List (Fin q))
    (hs : List.ofFn s = before ++ rule.domino.top ++ after)
    (ht : List.ofFn t = before ++ rule.domino.bottom ++ after) :
    Nonempty (Application rule s t) := by
  have hlen := congrArg List.length hs
  simp only [List.length_ofFn, List.length_append, Rule.domino, List.length_cons,
    List.length_nil] at hlen
  let first : Fin n := ⟨before.length, by omega⟩
  let second : Fin n := ⟨before.length + 1, by omega⟩
  have hget (j : Fin n) :
      some (s j) = (before ++ [rule.first, rule.second] ++ after)[j.val]? ∧
      some (t j) = (before ++ [rule.first', rule.second'] ++ after)[j.val]? := by
    constructor
    · simpa [Rule.domino] using congrArg (fun word => word[j.val]?) hs
    · simpa [Rule.domino] using congrArg (fun word => word[j.val]?) ht
  have hs1 := (hget first).1
  have hs2 := (hget second).1
  have ht1 := (hget first).2
  have ht2 := (hget second).2
  rw [(pair_lookup before after rule.first rule.second).1] at hs1
  rw [(pair_lookup before after rule.first rule.second).2] at hs2
  rw [(pair_lookup before after rule.first' rule.second').1] at ht1
  rw [(pair_lookup before after rule.first' rule.second').2] at ht2
  refine ⟨⟨first, second, rfl, Option.some.inj hs1, Option.some.inj hs2,
    Option.some.inj ht1, Option.some.inj ht2, ?_⟩⟩
  intro j hj1 hj2
  have hfirst : j.val ≠ before.length := fun he => hj1 (Fin.ext he)
  have hsecond : j.val ≠ before.length + 1 := fun he => hj2 (Fin.ext he)
  obtain ⟨hsj, htj⟩ := hget j
  by_cases hp : j.val < before.length
  · rw [List.append_assoc, List.getElem?_append_left hp] at hsj htj
    exact Option.some.inj (hsj.trans htj.symm)
  · have hk : before.length + 2 ≤ j.val := by omega
    rw [List.append_assoc, List.getElem?_append_right (by omega),
      List.getElem?_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
      at hsj htj
    exact Option.some.inj (hsj.trans htj.symm)

/-- Every standard rewriting step has an indexed occurrence in one of the two rule directions. -/
theorem application_of_rewrites (rules : Fin r → Rule q) {s t : Fin n → Fin q}
    (h : Rewrites (RuleSet rules) (List.ofFn s) (List.ofFn t)) :
    ∃ i, Nonempty (Application (rules i) s t) ∨ Nonempty (Application (rules i) t s) := by
  obtain ⟨before, domino, after, ⟨i, hd | hd⟩, hs, ht⟩ := h
  · subst domino
    exact ⟨i, Or.inl (application_of_context (rules i) before after hs ht)⟩
  · subst domino
    exact ⟨i, Or.inr (application_of_context (rules i) before after ht hs)⟩

/-- A source semi-Thue rewrite in either direction reconfigures its complete encoded word. -/
theorem word_reachable_of_rewrites (rules : Fin r → Rule q) {s t : Fin n → Fin q}
    (h : Rewrites (RuleSet rules) (List.ofFn s) (List.ofFn t)) :
    HWord.Reachable (compatibility rules) (word s) (word t) := by
  obtain ⟨i, ha | ha⟩ := application_of_rewrites rules h
  · obtain ⟨app⟩ := ha
    exact rule_word_reachable rules i app
  · obtain ⟨app⟩ := ha
    exact symm (rule_word_reachable rules i app)

private def extend_application (rule : Rule q) {s t : Fin n → Fin q}
    (i j : Fin n) (hij : i.val + 1 = j.val)
    (he : ∀ k, k ≠ i → k ≠ j → s k = t k)
    (app : Application rule ![s i, s j] ![t i, t j]) : Application rule s t := by
  have hfirst : app.first = 0 := by
    apply Fin.ext
    have h := app.adjacent
    have hb := app.second.isLt
    change app.first.val = 0
    omega
  have hsecond : app.second = 1 := by
    apply Fin.ext
    have h := app.adjacent
    simp only [hfirst, Fin.val_zero] at h
    change app.second.val = 1
    omega
  exact ⟨i, j, hij, by simpa [hfirst] using app.source_first,
    by simpa [hsecond] using app.source_second,
    by simpa [hfirst] using app.target_first,
    by simpa [hsecond] using app.target_second, he⟩

/-- A rewriting of two adjacent source letters extends to a word retaining every other letter. -/
theorem rewrites_of_pair (rules : Fin r → Rule q) {s t : Fin n → Fin q}
    (i j : Fin n) (hij : i.val + 1 = j.val)
    (he : ∀ k, k ≠ i → k ≠ j → s k = t k)
    (hpair : Rewrites (RuleSet rules) [s i, s j] [t i, t j]) :
    Rewrites (RuleSet rules) (List.ofFn s) (List.ofFn t) := by
  have hlocal : Rewrites (RuleSet rules) (List.ofFn ![s i, s j]) (List.ofFn ![t i, t j]) := by
    simpa [List.ofFn_succ] using hpair
  obtain ⟨a, ha | ha⟩ := application_of_rewrites rules hlocal
  · obtain ⟨app⟩ := ha
    exact (extend_application (rules a) i j hij he app).rewrites rules a
  · obtain ⟨app⟩ := ha
    exact symm ((extend_application (rules a) i j hij (fun k hi hj => (he k hi hj).symm)
      app).rewrites rules a)

end Cslib.Complexity.NCL.HWord.RewriteGadget
