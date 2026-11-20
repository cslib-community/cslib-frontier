/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Complexity.Classes.Advice.Classical
import CslibFrontier.Computability.Complexity.Classes.Advice.Randomized
import CslibFrontier.Computability.Complexity.Classes.EXP.Bounds
import CslibFrontier.Computability.Complexity.Classes.EXP.Counting
import CslibFrontier.Computability.Complexity.Classes.EXP.Hierarchy

open Cslib.Complexity Turing.MultiTapeTM

-- The exact-length advice API is still applicable to a polynomial-time language.
example {A : Set (List Bool)} (h : A ∈ P encBits) : A ∈ PLog :=
  Set.mem_iUnion.mpr ⟨0, P_subset_PWithAdvice _ h⟩

-- An advised BPP language requires a semantic decider on the entire pair domain.
example {A : Set (List Bool)} {B : Set (List Bool × List Bool)} (c : ℕ)
    (hB : B ∈ BPP (encPair encBits encBits)) (advice : ℕ → List Bool)
    (hlen : ∀ n, (advice n).length = c * (Nat.log2 n + 1))
    (hA : ∀ x, x ∈ A ↔ (advice x.length, x) ∈ B) : A ∈ BPPLog :=
  Set.mem_iUnion.mpr ⟨c, advice, hlen, B, hB, hA⟩

-- Linear and polynomial bottom exponents yield different families of clocks.
example {A : Set (List Bool)} (h : A ∈ DTIME encBits (fun n => 2 ^ 2 ^ (3 * n))) :
    A ∈ EE encBits :=
  Set.mem_iUnion.mpr ⟨3, h⟩

example {A : Set (List Bool)} (h : A ∈ NTIME encBits (fun n => 2 ^ 2 ^ n ^ 3)) :
    A ∈ NEEXP encBits :=
  Set.mem_iUnion.mpr ⟨3, h⟩
