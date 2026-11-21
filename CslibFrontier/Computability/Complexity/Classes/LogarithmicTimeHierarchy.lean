/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Logics.FirstOrder.Ordered.Query
public import CslibFrontier.Logics.SecondOrder.WordMSO.FirstOrder

/-!
# The logarithmic-time hierarchy

We use the descriptive characterization of LH from [Immerman1999, Theorem 5.30]:
bounded-alternation logarithmic time with random access captures first-order logic on
canonically ordered inputs with BIT. On a binary word, the input relation tests the letter
at a position. We reuse the word vocabulary, in which the two letter predicates are
complements and strict order is recoverable from the canonical weak order. The canonical
numeric constants are definable from the order.

The convention that the universe has distinct zero and one leaves words of length zero
and one outside the formula test. Their membership is unrestricted because they form
a finite set and can be decided by finite control. The machine characterization is cited
here; the definitions and proofs use ordered first-order semantics.

## Main definitions

* `Cslib.Logic.FO.Ordered.ofWord`: the canonical ordered structure of a word of length at least two.
* `Cslib.Complexity.LH`: the logarithmic-time hierarchy of languages on binary encodings.

## Main results

* `Cslib.Complexity.compl_mem_LH`: LH is closed under complement.
-/

public section

namespace Cslib.Logic.FO.Ordered

open Cslib.Logic.WordMSO

/-- Interpret the word vocabulary on positions, with the canonical numeric vocabulary
provided by the ordered structure. -/
@[expose] def ofWord {α : Type} (w : List α) (hw : 2 ≤ w.length) :
    Structure (wordLanguage α) :=
  ⟨w.length, hw, wordStructure w⟩

end Cslib.Logic.FO.Ordered

namespace Cslib.Complexity

open FirstOrder.Language
open Cslib.Logic.WordMSO (wordLanguage)
open Cslib.Logic.FO.Ordered (language ofWord)

/-- A language is in LH if one ordered first-order sentence decides it on all encoded
words of length at least two. -/
@[expose] def LH {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ φ : (language (wordLanguage Bool)).Sentence,
    ∀ a (ha : 2 ≤ (enc a).length), a ∈ A ↔ φ.Realize (ofWord (enc a) ha)}

/-- Negating the defining ordered sentence decides the complement. -/
theorem compl_mem_LH {α : Type} {enc : α ↪ List Bool} {A : Set α} (hA : A ∈ LH enc) :
    Aᶜ ∈ LH enc := by
  obtain ⟨φ, hφ⟩ := hA
  refine ⟨φ.not, fun a ha => (not_congr (hφ a ha)).trans ?_⟩
  exact (Sentence.realize_not (ofWord (enc a) ha)).symm

end Cslib.Complexity
