/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Products of lists of binary naturals

The product of a framed list of binary naturals is computable in binary in polynomial time, by a
left fold of binary multiplications from `1`. Multiplying by an element adds at most its binary
length to the running product (`Nat.size_mul_le`), and no element is longer than the encoded list,
so each partial product has binary length at most one more than the number of elements times the
length of the encoded list. The fold rule
`Turing.MultiTapeTM.ComputableInPolyTime.foldlWith_of_bounded_growth` takes exactly this additive
growth bound. This is the product counterpart of
`Turing.MultiTapeTM.ComputableInPolyTime.binary_sum` and the natural-number counterpart of
`Turing.MultiTapeTM.ComputableInPolyTime.intBin_prod`.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.binary_prod`: the product of a list of binary naturals.
* `Turing.MultiTapeTM.ComputableInPolyTime.binary_prod_map`: the product of the values of a
  polynomial-time function with binary values over a list.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- The product of a list of binary naturals, by a left fold of binary multiplications. -/
@[fun_prop]
theorem binary_prod : ComputableInPolyTime List.prod (encList encNat) encNat := by
  have hq := fst (encPair (encList encNat) encNat) encNat
  have h := foldlWith_of_bounded_growth (encA := encNat) (encL := encList encNat)
    (encB := encNat) (par := fun l : List ℕ => l) (list := fun l => l)
    (step := fun _ s a => s * a) id' id' (const 1) (binary_mul' hq.snd' (snd _ _))
    (growth := fun l => (encList encNat l).length) .self
    (fun l s a ha => by
      have := length_le_encList_of_mem encNat ha
      simp only [encNat_apply, Nat.size_eq_bits_len] at this ⊢
      have := Nat.size_mul_le s a
      lia)
  simpa only [← List.prod_eq_foldl] using h

/-- The product `(l.map H).prod` of the values of `H` over a list, for `H` polynomial-time with
binary values. `fun_prop` also finds this composition of `binary_prod` with
`Turing.MultiTapeTM.ComputableInPolyTime.map`; the name serves term-mode clients. -/
theorem binary_prod_map {α : Type} {enc : α ↪ List Bool} {H : α → ℕ}
    (hH : ComputableInPolyTime H enc encNat) :
    ComputableInPolyTime (fun l : List α => (l.map H).prod) (encList enc) encNat :=
  binary_prod.comp (map hH)

end Turing.MultiTapeTM.ComputableInPolyTime
