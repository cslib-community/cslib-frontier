/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Sigma
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sigma
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Circuit.Boolean.Encoding.PolyTime

/-! Dependent pairs under an index-dependent family, and `fun_prop` reading their index. -/

set_option linter.privateModule false

namespace CslibFrontierTests.EncSigma

open Turing.MultiTapeTM

/-- An index `n` with an element of `Fin (n + 1)`, encoded in unary by a family that depends on
the index. -/
abbrev encFinPair : (Σ n, Fin (n + 1)) ↪ List Bool :=
  encSigma encUnary fun n => encFinEnum (Fin (n + 1))

-- The index is framed; the second component is encoded under the family the index selects.
example : encFinPair ⟨1, 1⟩ = frame (encUnary 1) ++ encFinEnum (Fin 2) 1 := rfl
example (x : Σ n, Fin (n + 1)) :
    (encFinPair x).length = 2 * x.1 + 1 + (encFinEnum (Fin (x.1 + 1)) x.2).length := by
  simp

example {x y : Σ n, Fin (n + 1)} (h : encFinPair x = encFinPair y) : x = y :=
  encFinPair.injective h

-- `fun_prop` reads the index, bare or after a computable map, in degree and in polynomial time.
example : ComputableInDegree (fun x : Σ n, Fin (n + 1) => x.1) encFinPair encUnary 1 1 := by
  fun_prop
example : ComputableInPolyTime (fun x : Σ n, Fin (n + 1) => x.1) encFinPair encUnary := by
  fun_prop
example {α : Type} {encA : α ↪ List Bool} {f : α → Σ n, Fin (n + 1)}
    (hf : ComputableInPolyTime f encA encFinPair) :
    ComputableInPolyTime (fun a => (f a).1) encA encUnary := by
  fun_prop

-- The number of inputs of an encoded circuit.
example : ComputableInPolyTime (fun c : Σ n, Cslib.Circuits.Circuit
    Cslib.Circuits.Boolean.signature n 1 => c.1) (Cslib.Circuits.Boolean.encCircuit 1)
    encUnary := by
  fun_prop

end CslibFrontierTests.EncSigma
