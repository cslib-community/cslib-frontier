/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Logspace function computation by bit queries

The bit graph for `FNL` records both the output bits and the end of the output. `FNLPoly`
supplies length-dependent advice to this bit-graph computation.

## References

* [E. Allender and M. Ogihara, *Relationships Among PL, #L, and the Determinant*, §3]
  (https://www.cs.rutgers.edu/~allender/papers/pl3.pdf)
* [K. Reinhardt and E. Allender, *Making Nondeterminism Unambiguous*]
  (https://doi.org/10.1137/S0097539798339041)
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type}

/-- A query about the output bit or end marker at a specified index. -/
structure FNLQuery (α : Type) where
  /-- The input instance. -/
  instanceData : α
  /-- Zero-based index into the output. -/
  index : ℕ
  /-- The proposed bit, or `none` for an index at or beyond the end of the output. -/
  symbol : Option Bool

/-- Frame the instance and binary index, then append the tagged output symbol. -/
enc_structure encFNLQuery (enc : α ↪ List Bool) : FNLQuery α where
  instanceData : enc,
  index : encNat,
  symbol : (encOption encBool)

/-- Polynomial-length string functions whose bit graph, including the end marker, is in `NL`. -/
def FNL (enc : α ↪ List Bool) : Set (α → List Bool) :=
  {f | (∃ p : Polynomial ℕ, ∀ a, (f a).length ≤ p.eval (enc a).length) ∧
    {q : FNLQuery α | (f q.instanceData)[q.index]? = q.symbol} ∈ NL (encFNLQuery enc)}

/-- Nonuniform `FNL`: exactly `p(n)` arbitrary bits of advice are used at input length `n`. -/
def FNLPoly : Set (List Bool → List Bool) :=
  {f | ∃ (p : Polynomial ℕ) (advice : ℕ → List Bool),
    (∀ n, (advice n).length = p.eval n) ∧
    ∃ F ∈ FNL (encPair encBits encBits), ∀ x, f x = F (advice x.length, x)}

end Cslib.Complexity
