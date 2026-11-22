/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs

/-!
# The `q`-ary kernel lattice

For a matrix `A ∈ ℤ_q ^ {ρ × κ}`, the `q`-ary kernel lattice is
`Λ^⊥(A) = { z ∈ ℤ ^ κ : A z ≡ 0 (mod q) }`. Its membership condition is shared by the
coordinatewise and Euclidean short-integer-solution predicates and by the gadget-trapdoor
kernel bases.

## Main definitions

* `Cslib.Crypto.InKernelLattice`: membership of an integer vector in `Λ^⊥(A)`.

## References

* [D. Micciancio and C. Peikert, *Trapdoors for Lattices: Simpler, Tighter, Faster,
  Smaller*][MicciancioPeikert2012]
* [D. Micciancio and O. Regev, *Worst-Case to Average-Case Reductions Based on Gaussian
  Measures*][MicciancioRegev2007]
-/

@[expose] public section

namespace Cslib.Crypto

open scoped Matrix

/-- Membership in the `q`-ary kernel lattice `Λ^⊥(A) = { z ∈ ℤ ^ κ : A z ≡ 0 (mod q) }`
([MicciancioPeikert2012], Section 2.2; the kernel condition of [MicciancioRegev2007],
Definition 5.1). -/
abbrev InKernelLattice {q : ℕ} {ρ κ : Type*} [Fintype κ] (A : Matrix ρ κ (ZMod q))
    (z : κ → ℤ) : Prop :=
  A *ᵥ (Int.cast ∘ z) = 0

end Cslib.Crypto
