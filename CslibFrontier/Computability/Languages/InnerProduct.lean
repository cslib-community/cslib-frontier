/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Basic
public import Mathlib.Computability.Language
public import Mathlib.Data.Matrix.Mul
import CslibFrontier.Foundations.Data.BitString.List.Operations

/-!
# The binary inner-product language

An even-length word belongs to `Cslib.Language.innerProduct` exactly when the inner product
modulo two of its first and second halves is one. The alphabet is binary and there is no
delimiter. The empty word and every odd-length word are rejected.

The fixed-width interface `ofFn_append_mem_innerProduct_iff` recovers the existing bit-string
inner product from the language parser. Splitting each half into two blocks decomposes its value
as the XOR of the corresponding block inner products. This interface includes zero-width
blocks and zero padding as special cases.

## Main definitions

* `Cslib.Language.innerProduct`: the unmarked binary inner-product language.

## Main results

* `Cslib.Language.ofFn_blocks_mem_innerProduct_iff`: the two block pairs contribute by XOR.
-/

public section

open Matrix

namespace Cslib.Language

/-- Even-length binary words whose two halves have inner product one modulo two. No separator
is present; the empty word and all odd-length words are outside the language. -/
@[expose] def innerProduct : _root_.Language Bool :=
  {w | w.length % 2 = 0 ∧
    (List.zipWith Bool.and (w.take (w.length / 2)) (w.drop (w.length / 2))).foldl
      Bool.xor false = true}

instance : DecidablePred (· ∈ innerProduct) := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- On two equal-width bit strings, the language parser agrees with their inner product. -/
theorem ofFn_append_mem_innerProduct_iff {n : ℕ} (x y : BitString n) :
    List.ofFn x ++ List.ofFn y ∈ innerProduct ↔ x ⬝ᵥ y = true := by
  change ((List.ofFn x ++ List.ofFn y).length % 2 = 0 ∧ _) ↔ _
  simp only [List.length_append, List.length_ofFn]
  rw [show (n + n) % 2 = 0 by omega, show (n + n) / 2 = n by omega]
  simp [List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn,
    ← BitString.dotProduct_eq_foldl]

/-- Splitting both halves at the same position decomposes membership into the XOR of the two
corresponding block inner products. This includes zero-width blocks. -/
theorem ofFn_blocks_mem_innerProduct_iff {m r : ℕ}
    (x : BitString m) (a : BitString r) (y : BitString m) (b : BitString r) :
    List.ofFn x ++ List.ofFn a ++ (List.ofFn y ++ List.ofFn b) ∈ innerProduct ↔
      ((x ⬝ᵥ y) ^^ (a ⬝ᵥ b)) = true := by
  have h := ofFn_append_mem_innerProduct_iff (Fin.append x a) (Fin.append y b)
  simpa [dotProduct, Fin.sum_univ_add, Bool.add_eq_xor] using h

end Cslib.Language
