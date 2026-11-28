/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.Substitution
import Mathlib.Data.Fintype.BigOperators

/-! A single call has a self-loop joining its two ports. Substitution takes the trace of the
binary equality table. The two possible diagonal assignments each contribute one. -/

open Cslib.Circuits.Frontier

example : ∃ (V E : Type) (_ : Fintype V) (_ : Fintype E) (_ : DecidableEq E)
    (M : OpenBitNetwork ℕ Empty V E), M.Trivalent ∧ M.volume = 2 ∧
      M.contraction Empty.elim = 2 := by
  let N : OpenBitNetwork ℕ Empty (Empty ⊕ Unit) Unit :=
    { src _ := .inr (), tgt _ := .inr (), site := Empty.elim, tensor _ _ _ := 1,
      tensor_congr _ _ _ _ := rfl, exterior_congr _ _ _ _ _ := rfl }
  let D : OpenBitNetwork ℕ Bool Unit Empty :=
    { src := Empty.elim, tgt := Empty.elim, site _ := (),
      tensor _ _ x := if x false = x true then 1 else 0,
      tensor_congr _ _ _ _ := rfl,
      exterior_congr _ _ _ _ h := by rw [h false rfl, h true rfl] }
  let ports : N.Port (.inr ()) ≃ Bool :=
    { toFun p := Sum.elim (Sum.elim (fun _ => false) (fun _ => true)) Empty.elim p.val
      invFun b := if b then ⟨.inl (.inr ()), rfl⟩ else ⟨.inl (.inl ()), rfl⟩
      left_inv := by
        rintro ⟨(u | u) | i, _⟩
        · cases u; rfl
        · cases u; rfl
        · exact i.elim
      right_inv := by rintro (⟨⟩ | ⟨⟩) <;> rfl }
  have hd : D.Trivalent := by
    rintro ⟨⟩
    change Nat.card {e : Empty // _} + Nat.card {e : Empty // _} +
      Nat.card {i : Bool // () = ()} ≤ 3
    simp [Nat.card_eq_fintype_card]
  obtain ⟨V, E, hV, hE, dE, M, ht, hsize, hval⟩ :=
    OpenBitNetwork.exists_replace_calls N D (fun _ => ports) (fun o => o.elim) hd (by
      rintro ⟨⟩ α x
      simp [TensorNetwork.contraction, D, ports, N])
  refine ⟨V, E, hV, hE, dE, M, ht, ?_, ?_⟩
  · simpa [Nat.card_eq_fintype_card] using hsize
  · rw [hval]
    simp [TensorNetwork.contraction, N]
