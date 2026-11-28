/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SharpP
public import CslibFrontier.Computability.Complexity.Problems.Permanent.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Computability.Complexity.Classes.SharpP.Closure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.Matrix.Permanent.ZeroOne
import Mathlib.Data.List.GetD
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The 0/1 permanent is in #P

A certificate for a Boolean table `A` with `n` rows is an `n × n` Boolean matrix, written row by
row in `n * n` bits: bit `j + n * i` is entry `(i, j)`. The verifier
`Cslib.Complexity.ZeroOnePermanent.verifier` accepts it when it is the matrix of a permutation
`σ` (every row has a `true` entry, and no row or column has two) whose entries all lie on `true`
entries of `A`. Such certificates correspond exactly to the permutations counted by
`zeroOnePermanent_eq_card`, so the accepting count at length `n * n` is the 0/1 permanent
(`ZeroOnePermanent.acceptCount_verifier`). The verifier is polynomial-time on
`encPair encBoolTable encBits`, and padding to a polynomial length in the encoded table
(`mem_SharpP_of_polyTime_length`) puts `ZeroOnePermanent` in #P, the membership half of Valiant's
theorem [Valiant][Valiant1979], [Arora and Barak, Section 9.2][AroraBarak07],
[Goldreich, Section 6.2.1][Goldreich2007Draft].

## Main definitions

* `Cslib.Complexity.ZeroOnePermanent.verifier`: the permutation-matrix verifier.

## Main results

* `Cslib.Complexity.ZeroOnePermanent.acceptCount_verifier`: the verifier counts the permanent.
* `Cslib.Complexity.ZeroOnePermanent.mem_SharpP`: `ZeroOnePermanent ∈ SharpP encBoolTable`.

## References

* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, 2007 draft][AroraBarak07]
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, 2007 draft]
  [Goldreich2007Draft]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

namespace ZeroOnePermanent

/-- Entry `(i, j)` of an `n × n` Boolean matrix written row by row in the bit string `w`. -/
@[expose]
def bit (w : List Bool) (n i j : ℕ) : Bool := w.getD (j + n * i) false

/-- Reading an entry of a computed certificate at computed unary coordinates is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_bit {γ : Type} {input : γ ↪ List Bool} {w : γ → List Bool}
    {n i j : γ → ℕ} (hw : ComputableInPolyTime w input encBits)
    (hn : ComputableInPolyTime n input encUnary) (hi : ComputableInPolyTime i input encUnary)
    (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime (fun x => bit (w x) (n x) (i x) (j x)) input encBool :=
  bitsGetDWithInput hw (unary_add' hj (unary_mul' hn hi)) false

/-- Accept a certificate `w` for the table `A` with `n` rows when, read as an `n × n` matrix by
`bit`, every row has a `true` entry, no row or column has two, and every `true` entry is a `true`
entry of `A`. -/
@[expose]
def verifier (x : List (List Bool) × List Bool) : Bool :=
  (List.range x.1.length).all fun i =>
    ((List.range x.1.length).any fun j => bit x.2 x.1.length i j) &&
      (List.range x.1.length).all fun j =>
        (!bit x.2 x.1.length i j || (x.1.getD i []).getD j false) &&
          (List.range x.1.length).all fun k =>
            (!(bit x.2 x.1.length i j && bit x.2 x.1.length i k) || j == k) &&
              (!(bit x.2 x.1.length i j && bit x.2 x.1.length k j) || i == k)

/-- The verifier is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encBoolTable encBits) encBool := by
  unfold verifier encBoolTable
  fun_prop

/-- The verifier's condition, on a certificate of length `n * n`, read as a Boolean matrix. -/
theorem verifier_ofFn (A : List (List Bool)) (w : Fin (A.length * A.length) → Bool) :
    verifier (A, List.ofFn w) = true ↔
      (∀ i, ∃ j, w (finProdFinEquiv (i, j)) = true) ∧
        (∀ i j k, w (finProdFinEquiv (i, j)) = true → w (finProdFinEquiv (i, k)) = true →
          j = k) ∧
        (∀ i k j, w (finProdFinEquiv (i, j)) = true → w (finProdFinEquiv (k, j)) = true →
          i = k) ∧
        ∀ i j : Fin A.length, w (finProdFinEquiv (i, j)) = true → A[i].getD j false = true := by
  have hall (p : ℕ → Bool) :
      (List.range A.length).all p = true ↔ ∀ i : Fin A.length, p i = true :=
    List.all_eq_true.trans ⟨fun h i => h i (List.mem_range.2 i.isLt),
      fun h i hi => h ⟨i, List.mem_range.1 hi⟩⟩
  have hany (p : ℕ → Bool) :
      (List.range A.length).any p = true ↔ ∃ i : Fin A.length, p i = true :=
    List.any_eq_true.trans ⟨fun ⟨i, hi, hp⟩ => ⟨⟨i, List.mem_range.1 hi⟩, hp⟩,
      fun ⟨i, hp⟩ => ⟨i, List.mem_range.2 i.isLt, hp⟩⟩
  have hbit (i j : Fin A.length) :
      bit (List.ofFn w) A.length i j = w (finProdFinEquiv (i, j)) :=
    List.getD_ofFn_of_lt w (finProdFinEquiv (i, j)).isLt false
  have hget (i : Fin A.length) : A.getD (i : ℕ) [] = A[i] := List.getD_eq_getElem _ _ i.isLt
  have hnot_or (a b : Bool) : (!a || b) = true ↔ (a = true → b = true) := by
    cases a <;> cases b <;> decide
  simp only [verifier, hall, hany, Bool.and_eq_true, hnot_or, beq_iff_eq, hbit, hget, Fin.val_inj]
  exact ⟨fun h => ⟨fun i => (h i).1, fun i j k hj hk => (((h i).2 j).2 k).1 ⟨hj, hk⟩,
      fun i k j hi hk => (((h i).2 j).2 k).2 ⟨hi, hk⟩, fun i j hij => ((h i).2 j).1 hij⟩,
    fun ⟨h1, h2, h3, h4⟩ i => ⟨h1 i, fun j => ⟨h4 i j, fun k =>
      ⟨fun ⟨hj, hk⟩ => h2 i j k hj hk, fun ⟨hi, hk⟩ => h3 i k j hi hk⟩⟩⟩⟩

/-- **The verifier counts the 0/1 permanent**: at certificate length `n * n` it accepts exactly
the row-by-row permutation matrices supported on `true` entries. -/
theorem acceptCount_verifier (A : List (List Bool)) :
    acceptCount verifier A (A.length * A.length) = ZeroOnePermanent A := by
  classical
  rw [zeroOnePermanent_eq_card,
    ← Matrix.card_filter_isPermMatrix fun i j : Fin A.length => A[i].getD j false = true,
    acceptCount]
  let e : (Fin (A.length * A.length) → Bool) ≃ (Fin A.length → Fin A.length → Bool) :=
    (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)
  refine Finset.card_equiv e fun w => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, verifier_ofFn]
  exact Iff.rfl

/-- **The 0/1 permanent is in #P** [Valiant][Valiant1979]. -/
theorem mem_SharpP : ZeroOnePermanent ∈ SharpP encBoolTable := by
  have h := mem_SharpP_of_polyTime_length (enc := encBoolTable) computableInPolyTime_verifier
    (r := fun A => A.length * A.length) (by fun_prop)
  simpa only [acceptCount_verifier] using h

end ZeroOnePermanent

end Cslib.Complexity
