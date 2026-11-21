/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Fields

open Turing Turing.MultiTapeATM QuantifiedWord

-- The second player can match an observed universal bit. A first existential guess cannot
-- anticipate a later universal bit. Both games end with exactly two bits on the choice tape.
example : plays (fun w => w[0]? = w[1]?) [] [true, false] := by
  change ∀ e : Bool, ∃ g : Bool, some e = some g
  exact fun e => ⟨e, rfl⟩

example : ¬ plays (fun w => w[0]? = w[1]?) [] [false, true] := by
  change ¬ ∃ e : Bool, ∀ g : Bool, some e = some g
  rintro ⟨e, h⟩
  exact Bool.noConfusion (Option.some.inj ((h false).symm.trans (h true)))

-- The empty prefix still pays its one transition into the leaf.
example {k : ℕ} {S : Type} {input : List Bool} (leaf : MultiTapeATM k Bool S) (tape : Fin k)
    (storage : Cfg k Bool Unit input) (t : ℕ)
    (h : leaf.HaltsWithin t (WordGameLeaf.config tape (some leaf.toPTM.initial) [] 0 storage)) :
    (machine leaf tape).HaltsWithin (t + 1)
      (WordGameLeaf.config tape (some .dispatch) [] 0 storage) := by
  have hs := spec leaf tape t storage (fun word => leaf.AcceptsWithin t
    (WordGameLeaf.config tape (some leaf.toPTM.initial) word word.length storage)) [] [] (by
      intro suffix hlen
      have : suffix = [] := List.eq_nil_of_length_eq_zero hlen
      subst suffix
      exact ⟨h, Iff.rfl⟩)
  exact hs.1
