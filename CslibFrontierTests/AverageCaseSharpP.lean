/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.AverageCase.SharpP
public import CslibFrontier.Computability.Complexity.Classes.Counting.OracleSpace
import CslibFrontier.Foundations.Data.BitString.List.BinaryOrder

/-! Clients for samplable ensembles that are not computable unless `#P` is easy: the order
convention the construction relies on, both textbook forms, the contrapositive a caller uses, and
the collapse of `P^#P` to `P` from `#P ⊆ FP` at word and structured instance encodings. -/

public section

open Cslib.Complexity Turing.MultiTapeTM

namespace AverageCaseSharpPTests

/-! The sampled word `x ++ [true]` immediately follows `x ++ [false]` among the words of its
length: the numeric order of `binaryValue` reads the first bit as the most significant one. With
the verdict bit placed first instead, the two words would be `2 ^ |x|` apart. -/

example : Cslib.BitString.binaryValue ([true, false, true] ++ [true]) =
    Cslib.BitString.binaryValue ([true, false, true] ++ [false]) + 1 := by decide

example : Cslib.BitString.binaryValue ([true] ++ [true, false, true]) =
    Cslib.BitString.binaryValue ([false] ++ [true, false, true]) + 2 ^ 3 := by decide

/-- Goldreich's Exercise 10.26 at the word level. -/
example (h : ¬ SharpP encBits ⊆ {f | ComputableInPolyTime f encBits encNat}) :
    ∃ D : Ensemble, D.PSamp ∧ ¬ D.PComp :=
  Ensemble.exists_pSamp_not_pComp_of_not_SharpP_subset h

/-- The contrapositive: if every polynomial-time samplable ensemble is polynomial-time computable,
every function in `#P` is computable in polynomial time. -/
example (h : ∀ D : Ensemble, D.PSamp → D.PComp) :
    SharpP encBits ⊆ {f | ComputableInPolyTime f encBits encNat} := by
  by_contra hsub
  obtain ⟨D, hs, hc⟩ := Ensemble.exists_pSamp_not_pComp_of_not_SharpP_subset hsub
  exact hc (h D hs)

/-- Arora–Barak's Chapter 15 Exercise 4, for languages of words. -/
example (h : P encBits ≠ PWithSharpPOracle encBits) : ∃ D : Ensemble, D.PSamp ∧ ¬ D.PComp :=
  Ensemble.exists_pSamp_not_pComp_of_P_ne_PWithSharpPOracle h

/-- The same at a structured instance encoding. -/
example (h : P (encPair encBits encNat) ≠ PWithSharpPOracle (encPair encBits encNat)) :
    ∃ D : Ensemble, D.PSamp ∧ ¬ D.PComp :=
  Ensemble.exists_pSamp_not_pComp_of_P_ne_PWithSharpPOracle h

/-- `#P ⊆ FP` makes `P^#P` equal to `P`. -/
example (h : SharpP encBits ⊆ {f | ComputableInPolyTime f encBits encNat}) :
    PWithSharpPOracle (encPair encBits encNat) = P (encPair encBits encNat) :=
  (PWithSharpPOracle_subset_P_of_SharpP_subset h).antisymm P_subset_PWithSharpPOracle

end AverageCaseSharpPTests
