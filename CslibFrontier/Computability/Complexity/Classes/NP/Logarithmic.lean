/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Logics.FirstOrder.Ordered.Query
public import Mathlib.ModelTheory.Complexity

/-!
# Logarithmically restricted NP

A `LOGNP0` query chooses an increasing tuple of logarithmically many universe elements.
For every fixed-length tuple of challenges, there must be a fixed-length tuple of responses
for which a quantifier-free first-order formula holds at every chosen element and its rank.
The logarithmic bound uses the size of the universe, independent of the length of its
encoded relation table. `LOGNP` is the polynomial-time many-one reduction closure of
single-relation `LOGNP0` queries on finite structures.

The quantifier pattern and the closure follow [Cai–Chen, §5, pp. 745–746]
(https://doi.org/10.1137/S0097539793258295), following [Papadimitriou–Yannakakis]
(https://doi.org/10.1006/jcss.1996.0058). The universe and rank use zero-based indices.
We use explicit relation tables and the library's ordered structures of size at least two.
-/

public section

namespace Cslib.Complexity

open FirstOrder Cslib.Logic Cslib.Logic.FO Turing.MultiTapeTM

/-- The local LOGNP pattern. The first two formula variables are the selected element
and its rank. The other variables hold the challenge and response tuples. -/
@[expose] def LOGNP0 {L : Language.{0, 0}} (K : Ordered.Query L) : Prop :=
  ∃ (p q : ℕ) (φ : L.Formula (Fin 2 ⊕ (Fin p ⊕ Fin q))), φ.IsQF ∧
    ∀ M : Ordered.Structure L, M ∈ K ↔
      ∃ chosen : Fin (Nat.log2 M.size) → Fin M.size, StrictMono chosen ∧
        ∀ challenge : Fin p → Fin M.size, ∃ response : Fin q → Fin M.size,
          ∀ rank : Fin (Nat.log2 M.size),
            φ.Realize (Sum.elim
              ![chosen rank, Fin.castLE (Nat.log2_le_self M.size) rank]
              (Sum.elim challenge response))

/-- The languages polynomial-time many-one reducible to the encoded language of a
single-relation `LOGNP0` query. -/
@[expose] def LOGNP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (L : Language.{0, 0}) (_ : L.IsRelational) (v : Vocabulary L) (K : Ordered.Query L),
     v.count = 1 ∧ LOGNP0 K ∧ PolyTimeReducible enc encStructure A (K.encodedLanguage v)}

/-- The defining polynomial-time many-one reduction closure of LOGNP. -/
theorem LOGNP.of_reduces {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {A : Set α} {B : Set β} (hB : B ∈ LOGNP encB) (hAB : PolyTimeReducible encA encB A B) :
    A ∈ LOGNP encA := by
  obtain ⟨L, hL, v, K, hc, hK, hB⟩ := hB
  exact ⟨L, hL, v, K, hc, hK, hAB.trans hB⟩

end Cslib.Complexity
