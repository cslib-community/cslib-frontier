/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Complexity.Classes.Space.Quantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.BitWord
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Context
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Midpoint
import CslibFrontier.Tactic.Space

/-!
# Reachability in a graph given by its adjacency matrix, in the space of Savitch's recursion

The input is a width `W` in unary and a word `m`, the adjacency matrix of a directed graph on the
words of `W` bits: there is an edge from `x` to `y` when `m` has a one at the position whose
binary digits are `y` followed by `x`. Whether the word of ones is reachable from the word of
zeros is decided by the midpoint recursion `Cslib.Reachability.reach` at depth `W`, within space
`O((W + 1) ^ 2 + log |m|)`: the matrix is never copied, and an edge test reads one bit of it.

The file declares the edge test and certifies it with `space`; the frames, the stack and the
recursion are those of `Turing.MultiTapeTM.ComputableInSpace.reach`.
-/

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace Cslib.Reachability

namespace SpaceMidpointTest

/-- The edges of the graph with adjacency matrix `m`: the bit at the position `y ++ x`. -/
def edge (m : List Bool) (x y : List Bool) : Bool := m[ofBits (y ++ x)]?.getD false

/-- Whether the word of ones is reachable from the word of zeros. -/
def connected (a : ℕ × List Bool) : Bool :=
  reach (edge a.2) a.1 a.1 (List.replicate a.1 false) (List.replicate a.1 true)

-- On two vertices, `[false]` and `[true]`: the matrix `0100` has the edge from `[false]` to
-- `[true]` only, and `0010` the reverse edge only.
example : edge [false, true, false, false] [false] [true] = true := by decide
example : connected (1, [false, true, false, false]) = true := by decide
example : connected (1, [false, false, true, false]) = false := by decide
example : connected (0, []) = true := by decide

/-- The edge test, from two stored words, the stored width and the matrix: within the stored
words and the logarithm of the length of the matrix. -/
theorem edge_inSpace : ComputableInSpace
    (fun q : ((List Bool × List Bool) × ℕ) × List Bool => edge q.2 q.1.1.1 q.1.1.2)
    (encPair (encPair (encPair encBits encBits) encUnary) encBits) encBool
    fun q => (encPair (encPair encBits encBits) encUnary q.1).length +
      Nat.log2 (encBits q.2).length := by
  have hreg := budget_registers (encR := encPair (encPair encBits encBits) encUnary)
    (encA := encBits) (.refl _)
  have hbit : ComputableInSpace
      (fun q : ((List Bool × List Bool) × ℕ) × List Bool => q.2[ofBits (q.1.1.2 ++ q.1.1.1)]?)
      (encPair (encPair (encPair encBits encBits) encUnary) encBits) (encOption encBool)
      fun q => (encPair (encPair encBits encBits) encUnary q.1).length +
        Nat.log2 (encBits q.2).length :=
    budget_inputBit (budget_ofBits (budget_bitsAppend hreg.fst'.snd' hreg.fst'.fst')) (.refl _)
  space [edge]

/-- **Reachability in a graph given by its adjacency matrix**, within the space of the frames of
the midpoint recursion and the logarithm of the length of the matrix. -/
theorem connected_inSpace : ComputableInSpace connected (encPair encUnary encBits) encBool
    fun a => (a.1 + 1) ^ 2 + Nat.log2 a.2.length := by
  have hW := budget_registers (encR := encUnary) (encA := encBits)
    (Bs := fun a => (encUnary a.1).length + Nat.log2 (encBits a.2).length) (.refl _)
  have hreach := reach (encA := encPair encUnary encBits) (edge := fun a => edge a.2)
    (S := fun a => (encUnary a.1).length + Nat.log2 (encBits a.2).length)
    (E := fun a => 13 * a.1 + 2 * Nat.log2 a.2.length + 12)
    hW (budget_unaryToNat hW) (budget_replicateFalse hW) (budget_replicateTrue hW)
    (assoc_context edge_inSpace)
    (fun a x y hx hy => by
      simp only [length_encPair, encBits_apply, encUnary_apply, List.length_replicate, hx, hy]
      omega)
    fun a => ⟨List.length_replicate, List.length_replicate⟩
  refine (hreach.of_enc_eq fun _ => rfl).weaken ⟨16, fun a => ?_⟩
  have h₁ := Nat.log2_le_self a.1
  have h₂ := log2_length_encPair_le encUnary encBits a
  simp only [encUnary_apply, List.length_replicate, encBits_apply] at h₂ ⊢
  nlinarith

end SpaceMidpointTest
