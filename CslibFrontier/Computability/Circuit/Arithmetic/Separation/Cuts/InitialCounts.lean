/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Initial
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The units of a base party at the beginning

In the table of a base party at the beginning (`Cut.initialTable`), a term with a nonzero weight
(`Cut.partyWeight`) writes and reads at most `T` letters, and its condition `Cut.InitialOk` makes
the numbers of units of the strings to and from the other base parties those of these letters. So
a base party whose table at the beginning is not zero holds at most
`2 * ((T + (K + K) * (|S| + 1)) * c / ub + (K + K))` units
(`Cut.sum_count_le_of_initialTable_ne_zero`). This is the last bound of Lemma I.2 of
[AnthropicVPVNP2026], whose identity is `Cut.runVal_eq_sum_value_initial`, and the dealing program
of that paper checks it before it deals the units.

## Main results

* `Cut.sum_count_le_of_initialTable_ne_zero`: the units of a base party at the beginning.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Lemma I.2 (p. 51: a node whose node tensor is not `0` has at most
  `2((T + 2K(|S| + 1))c/ℓ + 2K)` packets), Proposition J.2 (p. 52) and its proof (p. 53: `N`, a
  bound for the packets at a node), and the program `G` in the proof of Theorem J.3 (p. 54: the
  numbers give every node at most `N` packets); modules `Nc.Dl.Facts` and `Paper.Runnet`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Cut

open Finset List.StairRefinement Tape

variable {F Γ S Q N : Type*} [CommSemiring F] [Fintype Γ] [DecidableEq Γ] [Fintype S]
  [DecidableEq S] [Fintype Q] [DecidableEq Q] {mu : Letter S Unit Γ → Matrix Q Q F}
  {K U0 U1 T ub c : ℕ} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}

/-- A party reads at most `T` letters on all tapes together. -/
private theorem sum_length_read_le_of_partyWeight_ne_zero {p : Fin (K + K)}
    {R C : Option S → Fin (K + K) → List Γ} (h : partyWeight mu T q x p R C ≠ 0) :
    ∑ s, (cat (C s)).length ≤ T := by
  induction p using Fin.addCases with
  | left κ =>
    rw [partyWeight_block] at h
    refine le_trans ?_ (sum_length_le_of_blockWeight_ne_zero (ite_ne_right_iff.1 h).2)
    let f : Option S ↪ Ch S Unit := ⟨fun s => s.elim (.inp ()) fun s => .tp s true, by
      rintro (_ | s) (_ | s') e <;> simp_all⟩
    calc ∑ s, (cat (C s)).length = ∑ s, (blockEmission R C (f s)).length :=
          sum_congr rfl fun s _ => by cases s <;> rfl
      _ ≤ _ := (sum_map univ f fun z => (blockEmission R C z).length).symm.trans_le
          (sum_le_sum_of_subset (subset_univ _))
  | right κ =>
    rw [partyWeight_input] at h
    obtain ⟨⟨-, hC, -⟩, -⟩ := ite_ne_right_iff.1 h
    simp [fun s => cat_eq_nil.2 (hC s)]

/-- **The units of a base party at the beginning** (Lemma I.2, its last bound). If the inputs of
the input parties have at most `T` letters each and the table at the beginning of the base party
`p` is not zero, then the strings from `p` to the base parties and from them to `p` have at most
`2 * ((T + (K + K) * (|S| + 1)) * c / ub + (K + K))` units in all. -/
theorem sum_count_le_of_initialTable_ne_zero (hx : ∀ κ, (x κ).length ≤ T)
    {cb : Option Γ → BitString c} {ρ : Option S → RowData (K + K)}
    {n : Fin (K + K) → Fin (K + K) → ℕ} {p : Fin (K + K)}
    {y : UnitId (K + K) U0 N U1 → UnitContent ub} (h : initialTable mu T cb q x ρ n p y ≠ 0) :
    ∑ b, (n p b + n b p) ≤ 2 * ((T + (K + K) * (Fintype.card S + 1)) * c / ub + (K + K)) := by
  obtain ⟨R, -, h⟩ := exists_ne_zero_of_sum_ne_zero h
  obtain ⟨C, -, h⟩ := exists_ne_zero_of_sum_ne_zero h
  obtain ⟨⟨-, hR, hC⟩, hW⟩ := ite_ne_right_iff.1 h
  have h1 := sum_unitCount_le (ub := ub) (cb := cb) (sum_length_le_of_partyWeight_ne_zero hx hW)
  have h2 := sum_unitCount_le (ub := ub) (cb := cb) (sum_length_read_le_of_partyWeight_ne_zero hW)
  simp only [fun b => (hR b).1, fun b => (hC b).1, Fintype.card_option] at h1 h2
  rw [sum_add_distrib]
  omega

end Cslib.Circuits.Arithmetic.Separation.Cut
