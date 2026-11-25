/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Units
public import Mathlib.Algebra.BigOperators.Fin
import CslibFrontier.Foundations.Data.List.SelfDelimiting
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Strings on the sides of a move, and their code words

After a law move of [AnthropicVPVNP2026] (Section H.2; modules `Nc.Cut.Defs` and
`Nc.Cut.Codes`), a channel of the law, here a *side*, holds a string of `B` blocks. The block `k`
has an index `i k` of the law, which has a label (its code) of `lam` bits, and a string `g k`
whose length `len (i k)` depends on the index. The *string on the side* (`Cut.sideString`)
consists of the labels and the strings of all blocks, and it determines the indices and the
strings: the label of a block says how long its string is. The string is written on units
(`Cut.unitsOf`, the packets of the paper), and its first `U` units are its *code word*
(`Cut.codeWord`), which still determines the indices and the strings if no string on a side has
more than `U` units.

## Main definitions

* `Cut.UnitContent.bits`: the bits of a unit, the empty list if the unit is absent.
* `Cut.sideString`: the string on a side, the labels and the strings of its blocks.
* `Cut.codeWord`: the first `U` units of the string on a side.

## Main results

* `Cut.sideString_injective`: the string on a side determines the indices and the strings of
  the blocks.
* `Cut.codeWord_injective`: so does its code word, if `U` is large enough.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Section H.2 (law moves) and the convention after Definition G.1, which Appendix J applies;
  modules `Nc.Cut.Defs`, `Nc.Cut.Codes`, `Nc.Plus.UnitBits`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Cut

/-- The bits of a unit: its `ub` bits, and the empty list if the unit is absent. -/
@[expose] def UnitContent.bits {ub : ℕ} : UnitContent ub → List Bool
  | none => []
  | some w => List.ofFn w

variable {I : Type*} {lam B : ℕ} {lab : I → BitString lam}

/-- The string on a side: for every block `k`, the label of its index `i k` and then its string
`g k`. -/
@[expose] def sideString (lab : I → BitString lam) (len : I → ℕ) (i : Fin B → I)
    (g : ∀ k, BitString (len (i k))) : List Bool :=
  (List.ofFn fun k => List.ofFn (lab (i k)) ++ List.ofFn (g k)).flatten

theorem length_sideString (lab : I → BitString lam) (len : I → ℕ) (i : Fin B → I)
    (g : ∀ k, BitString (len (i k))) :
    (sideString lab len i g).length = ∑ k, (lam + len (i k)) := by
  simp [sideString, List.length_flatten, List.sum_ofFn, Function.comp_def]

/-- The string on a side determines the indices and the strings of the blocks, if the labels of
the indices are distinct. -/
theorem sideString_injective (hlab : Function.Injective lab) (len : I → ℕ) :
    Function.Injective fun p : Σ i : Fin B → I, ∀ k, BitString (len (i k)) =>
      sideString lab len p.1 p.2 := by
  rintro ⟨i, g⟩ ⟨i', g'⟩ h
  have key : (fun k => (⟨i k, g k⟩ : Σ a, BitString (len a))) = fun k => ⟨i' k, g' k⟩ := by
    refine List.ofFn_injective (List.flatMap_inj_of_length_eq
      (c := fun p : Σ a, BitString (len a) => List.ofFn (lab p.1) ++ List.ofFn p.2) ?_ (by simp)
      (by simpa [sideString, List.flatMap_def, Function.comp_def] using h))
    rintro ⟨a, f⟩ ⟨a', f'⟩ r r' hr
    obtain ⟨h1, h2⟩ := List.append_inj (by simpa using hr) (by simp)
    obtain rfl := hlab (List.ofFn_injective h1)
    obtain ⟨h3, rfl⟩ := List.append_inj h2 (by simp)
    exact ⟨by rw [List.ofFn_injective h3], rfl⟩
  obtain rfl : i = i' := funext fun k => congrArg Sigma.fst (congrFun key k)
  exact congrArg _ (funext fun k => eq_of_heq (Sigma.mk.inj (congrFun key k)).2)

/-- The number of units of the string on a side, if the strings of the blocks have at most `m`
bits. -/
theorem unitCount_sideString_le {m U ub : ℕ} {len : I → ℕ} (hlen : ∀ i, len i ≤ m)
    (hB : B * (m + lam) / ub + 1 ≤ U) (i : Fin B → I) (g : ∀ k, BitString (len (i k))) :
    unitCount ub (sideString lab len i g) ≤ U := by
  refine le_trans ?_ hB
  rw [unitCount, length_sideString]
  refine Nat.add_le_add_right (Nat.div_le_div_right ?_) _
  calc ∑ k, (lam + len (i k)) ≤ ∑ _k : Fin B, (m + lam) :=
        Finset.sum_le_sum fun k _ => by have := hlen (i k); omega
    _ = B * (m + lam) := by simp

/-- The code word of the string on a side: its first `U` units. -/
@[expose] def codeWord (lab : I → BitString lam) (len : I → ℕ) (ub U : ℕ) (i : Fin B → I)
    (g : ∀ k, BitString (len (i k))) : Fin U → UnitContent ub :=
  fun k => unitsOf ub (sideString lab len i g) k

/-- The code word of the string on a side determines the indices and the strings of the blocks,
if the labels of the indices are distinct and the string has at most `U` units. -/
theorem codeWord_injective (hlab : Function.Injective lab) {m U ub : ℕ} (hub : 0 < ub)
    {len : I → ℕ} (hlen : ∀ i, len i ≤ m) (hB : B * (m + lam) / ub + 1 ≤ U) :
    Function.Injective fun p : Σ i : Fin B → I, ∀ k, BitString (len (i k)) =>
      codeWord lab len ub U p.1 p.2 := by
  intro p p' h
  refine sideString_injective hlab len (unitsOf_injective hub (funext fun k => ?_))
  by_cases hk : k < U
  · exact congrFun h ⟨k, hk⟩
  · rw [unitsOf_eq_none.2, unitsOf_eq_none.2] <;>
      exact (unitCount_sideString_le hlen hB _ _).trans (not_lt.1 hk)

end Cslib.Circuits.Arithmetic.Separation.Cut
