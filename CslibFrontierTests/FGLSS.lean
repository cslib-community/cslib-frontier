/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.Approximation.FGLSS

/-! Checked client of Goldreich Exercise 9.18, items 2–4: for a PCP verifier of a problem `A`,
the FGLSS graph of a member has independence number `2 ^ r`, and that of a non-member has
independence number at most `2 ^ (r - 1)`, so the two cases differ by a factor of `2`.

A verifier with no coins that queries position `0` twice and accepts exactly when the two answers
differ has only impossible accepting views, so its FGLSS graph has no vertices. -/

set_option linter.privateModule false

namespace CslibFrontierTests.FGLSS

open Cslib.Complexity

example {α : Type} {enc : α ↪ List Bool} {r q : ℕ → ℕ} {V : PCPVerifier α} {A : Set α}
    (hV : IsPCPVerifier enc r q V A) {a b : α} (ha : a ∈ A) (hb : b ∉ A)
    (hcoins : V.coins a = V.coins b) :
    2 * (V.fglssGraph b).indepNum ≤ (V.fglssGraph a).indepNum := by
  rw [hV.indepNum_fglssGraph_eq_of_mem ha, hcoins]
  exact hV.two_mul_indepNum_fglssGraph_le_of_not_mem hb

example {α : Type} (V : PCPVerifier α) (a : α) :
    ∃ π : List Bool, ∀ π' : List Bool,
      acceptCount (fun x => V.accepts x.1 π' x.2) a (V.coins a) ≤
        acceptCount (fun x => V.accepts x.1 π x.2) a (V.coins a) := by
  obtain ⟨π, hπ⟩ := V.exists_acceptCount_eq_indepNum_fglssGraph a
  exact ⟨π, fun π' => hπ ▸ PCPVerifier.acceptCount_le_indepNum_fglssGraph π'⟩

/-- No coins, two queries of position `0`, accept when the answers differ. -/
def conflicting : PCPVerifier Unit where
  coins _ := 0
  queries _ := [0, 0]
  verdict x := x.2.getD 0 false != x.2.getD 1 false

instance : IsEmpty {v : conflicting.View () // conflicting.IsFGLSSVertex () v} :=
  ⟨fun ⟨v, hv⟩ => by
    have h := hv.consistent.eq (i := ⟨0, by simp [conflicting]⟩)
      (j := ⟨1, by simp [conflicting]⟩) rfl
    exact absurd h (by simpa [conflicting, List.ofFn_succ] using hv.accepts)⟩

example : (conflicting.fglssGraph ()).indepNum = 0 := by
  obtain ⟨S, hS⟩ := (conflicting.fglssGraph ()).exists_isNIndepSet_indepNum
  rw [← hS.card_eq, Finset.eq_empty_of_isEmpty S, Finset.card_empty]

end CslibFrontierTests.FGLSS
