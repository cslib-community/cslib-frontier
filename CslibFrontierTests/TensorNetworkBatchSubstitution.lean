/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.BatchSubstitution
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.BigOperators

/-! Two calls on opposite ends of one edge occupy two slots of a three-slot verifier. A true
bit has weight two and a false bit has weight one, so their contraction is `1² + 2² = 5`. -/

open Cslib.Circuits.Frontier

example : ∃ (V E : Type) (_ : Fintype V) (_ : Fintype E) (_ : DecidableEq E)
    (M : OpenBitNetwork ℕ Empty V E), M.Trivalent ∧ M.volume = 4 ∧
      M.contraction Empty.elim = 5 := by
  let weight (b : Bool) : ℕ := if b then 2 else 1
  let N : OpenBitNetwork ℕ Empty (Empty ⊕ Bool) Unit :=
    { src _ := .inr false, tgt _ := .inr true, site := Empty.elim, tensor _ α _ := weight (α ()),
      tensor_congr := by
        rintro (o | b) α β h
        · exact o.elim
        · cases b
          · rw [h () (.inl rfl)]
          · rw [h () (.inr rfl)]
      exterior_congr _ _ _ _ _ := rfl }
  let D : OpenBitNetwork ℕ (Fin 3 × Unit) (Fin 3) Empty :=
    { src := Empty.elim, tgt := Empty.elim, site := Prod.fst,
      tensor t _ x := weight (x (t, ())), tensor_congr _ _ _ _ := rfl,
      exterior_congr t _ _ _ h := congrArg weight (h (t, ()) rfl) }
  let ports (c : Bool) : N.Port (.inr c) ≃ Unit :=
    { toFun _ := ()
      invFun _ := if hc : c = true then ⟨.inl (.inr ()), by simp [N, hc]⟩
        else ⟨.inl (.inl ()), by cases c <;> simp_all [N]⟩
      left_inv := by
        rintro ⟨(u | u) | i, h⟩
        · change Sum.inr false = Sum.inr c at h
          cases Sum.inr.inj h
          rfl
        · change Sum.inr true = Sum.inr c at h
          cases Sum.inr.inj h
          rfl
        · exact i.elim
      right_inv _ := rfl }
  have hd : D.Trivalent := by
    intro t
    change Nat.card {e : Empty // _} + Nat.card {e : Empty // _} +
      Nat.card {p : Fin 3 × Unit // p.1 = t} ≤ 3
    simp only [Nat.card_of_isEmpty, add_zero, zero_add]
    exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
      (by simp [Nat.card_eq_fintype_card])
  let slots : {c : Bool // () = ()} ↪ Fin 3 :=
    ⟨fun c => (finTwoEquiv.symm c.val).castLE (by decide), fun _ _ h =>
      Subtype.ext (finTwoEquiv.symm.injective (Fin.castLE_injective _ h))⟩
  obtain ⟨V, E, hV, hE, dE, M, ht, hsize, heval⟩ := OpenBitNetwork.exists_replace_call_batches
    N D (fun _ => ()) (fun | () => slots) ports (fun x => weight (x ())) (fun _ => false) rfl
    (fun o => o.elim) hd (fun x => by simp [TensorNetwork.contraction, D]) (by
      rintro (⟨⟩ | ⟨⟩) α x <;> simp [N, ports])
  refine ⟨V, E, hV, hE, dE, M, ht, ?_, ?_⟩
  · simpa [Nat.card_eq_fintype_card] using hsize
  · rw [heval]
    change (∑ α : Unit → Bool, ∏ v : Empty ⊕ Bool, weight (α ())) = 5
    rw [← (Equiv.funUnique Unit Bool).symm.sum_comp, Fintype.sum_bool]
    decide
