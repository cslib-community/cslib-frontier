/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Midpoint
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Savitch's midpoint recursion in polynomial space

The midpoint recursion `Cslib.Reachability.reach edge w d u v` runs in space
`O((d + 1) * (w + log₂ d + 1))` plus the space of one edge test
(`Turing.MultiTapeTM.ComputableInSpace.reach`). When the width and the depth are polynomial, which
holds when they are computed in unary within polynomial space, and the edge test runs in
polynomial space on two words of that width and the input, the recursion runs in polynomial space.

## Main results

* `Turing.MultiTapeTM.ComputableInPolySpace.reach`: the midpoint recursion in polynomial space.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.5][Sipser2013]
* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Section 4.2][AroraBarak09]
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolySpace

variable {α : Type} {encA : α ↪ List Bool}

/-- **Savitch's midpoint recursion in polynomial space**: with the width and the depth computed in
unary, the endpoints of that width and an edge test of two words and the input, all within
polynomial space, `Cslib.Reachability.reach` is computable within polynomial space. The input is
read in place by the edge test and never copied into the frames. -/
theorem reach {edge : α → List Bool → List Bool → Bool} {w d : α → ℕ} {u v : α → List Bool}
    (hw : ComputableInPolySpace w encA encUnary) (hd : ComputableInPolySpace d encA encUnary)
    (hu : ComputableInPolySpace u encA encBits) (hv : ComputableInPolySpace v encA encBits)
    (hedge : ComputableInPolySpace (fun q : (List Bool × List Bool) × α => edge q.2 q.1.1 q.1.2)
      (encPair (encPair encBits encBits) encA) encBool)
    (hlen : ∀ a, (u a).length = w a ∧ (v a).length = w a) :
    ComputableInPolySpace (fun a => Cslib.Reachability.reach (edge a) (w a) (d a) (u a) (v a))
      encA encBool := by
  have hdn : ComputableInPolySpace d encA encNat :=
    comp (f := fun n : ℕ => n) (g := d) (of_polyTime ComputableInPolyTime.unary_to_binary) hd
  obtain ⟨Sw, hSw, hw'⟩ := hw.exists_inSpace
  obtain ⟨Sd, hSd, hd'⟩ := hdn.exists_inSpace
  obtain ⟨Su, hSu, hu'⟩ := hu.exists_inSpace
  obtain ⟨Sv, hSv, hv'⟩ := hv.exists_inSpace
  obtain ⟨T, hT, hedge'⟩ := hedge.exists_inSpace
  obtain ⟨cT, dT, hcT⟩ := hT.exists_le
  set S := fun a => Sw a + Sd a + Su a + Sv a
  -- the cost of the edge test on two words of width `w a`
  set E := fun a => cT * (8 * w a + 2 * (encA a).length + 8) ^ dT
  have hTE (a : α) (x y : List Bool) (hx : x.length = w a) (hy : y.length = w a) :
      T ((x, y), a) ≤ E a := by
    refine (hcT _).trans (Nat.mul_le_mul_left cT (Nat.pow_le_pow_left ?_ dT))
    simp only [length_encPair, encBits_apply, hx, hy]
    omega
  have h := ComputableInSpace.reach (S := S) (E := E)
    (hw'.mono_le fun a => by dsimp only [S]; omega) (hd'.mono_le fun a => by dsimp only [S]; omega)
    (hu'.mono_le fun a => by dsimp only [S]; omega) (hv'.mono_le fun a => by dsimp only [S]; omega)
    hedge' hTE hlen
  refine of_inSpace ?_ h
  -- the width and the depth are bounded by the lengths of their unary codes
  have hwl : PolyBounded (fun a => (encA a).length) w :=
    hw.polyBounded_length.mono fun a => by simp
  have hdl : PolyBounded (fun a => (encA a).length) d :=
    hd.polyBounded_length.mono fun a => by simp
  have hE : PolyBounded (fun a => (encA a).length) E :=
    (PolyBounded.const cT).mul
      ((((PolyBounded.const 8).mul hwl).add ((PolyBounded.const 2).mul .self)).add (.const 8)
        |>.pow dT)
  refine (((((hSw.add hSd).add hSu).add hSv).add
    ((hdl.add (.const 1)).mul ((hwl.add hdl).add (.const 1)))).add (hE.add .self)).mono
    fun a => ?_
  have h₁ := Nat.log2_le_self (d a)
  have h₂ := Nat.log2_le_self (encA a).length
  have h₃ := Nat.mul_le_mul_left (d a + 1)
    (show w a + Nat.log2 (d a) + 1 ≤ w a + d a + 1 by omega)
  dsimp only [S, E] at h₃ ⊢
  omega

end Turing.MultiTapeTM.ComputableInPolySpace
