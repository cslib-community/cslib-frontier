/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Kolmogorov.MultiTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Complexity

/-!
# Kolmogorov complexity relative to a universal machine

A *universal machine* takes a description of a machine `M` and an input `x`, and returns `M(x)`
if `M` halts on `x` and does not halt otherwise [Goldreich, Definition 1.8][Goldreich2006DraftR1].
Here the machines are the library's deterministic multi-tape machines over the binary alphabet with
finitely many states. The description of `M` is the word `eDesc (desc eS eBit M)`, for a numbering
`eS` of its states, and the pair `(⟨M⟩, x)` is the word `encPair encBits encBits (⟨M⟩, x)`: every
bit `b` of `⟨M⟩` written as `1 b`, then `0`, then `x` (`Turing.MultiTapeTM.encPair`,
`Turing.MultiTapeTM.frame`). Goldreich's proof of Theorem 1.10 asks for an adequate encoding of
pairs and gives as an example `σ₁σ₁ ⋯ σₖσₖ 01 τ₁ ⋯ τₗ`; the encoding used here is of the same kind,
with the first component self-delimiting and the second written as is, and it costs `2 |⟨M⟩| + 1`
bits beyond `|x|`.

The complexity of `s` with respect to a machine `M`, `K_M(s)`, is the length of a shortest input
on which `M` halts with output `s` (`Cslib.Kolmogorov.DescriptionMethod.ecomplexity` of
`Cslib.Kolmogorov.DescriptionMethod.ofMultiTapeTM M`), and `⊤` if there is none. If `x` describes
`s` with respect to `M`, then `(⟨M⟩, x)` describes `s` with respect to a universal `U`, so
`K_U(s) ≤ K_M(s) + 2 |⟨M⟩| + 1` for every `s`
(`Turing.MultiTapeTM.IsUniversal.exists_ecomplexity_le`, Goldreich's Theorem 1.10).

`IsUniversal` is a hypothesis on a given machine; this module does not construct one. The
library's universal function `Turing.MultiTapeTM.Universal.universal` is clocked: it takes the
number of steps as part of its input. An unclocked native universal machine, Goldreich's
Theorem 1.9, is not yet formalized.

## Main definitions

* `Turing.MultiTapeTM.IsUniversal`: a universal machine.

## Main results

* `Turing.MultiTapeTM.IsUniversal.exists_ecomplexity_le`: **complexity with respect to a universal
  machine**: `K_U(s) ≤ K_M(s) + c` for every machine `M` and a constant `c` depending only on `M`.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft of December 2006,
  Definition 1.8 and Theorem 1.10][Goldreich2006DraftR1]
-/

@[expose] public section

namespace Turing.MultiTapeTM

open Universal Cslib.Kolmogorov DescriptionMethod

/-- **Universal machines** [Goldreich, Definition 1.8][Goldreich2006DraftR1]: on the pair of the
description of a machine `M` and an input `x`, the machine `U` halts with output `o` exactly when
`M` halts on `x` with output `o`. So it returns `M(x)` if `M` halts on `x`, and does not halt
otherwise (`Turing.MultiTapeTM.halts_iff_exists_computes`). Machines range over the deterministic
multi-tape machines over the binary alphabet with finitely many states, described by
`eDesc (desc eS eBit M)` for any numbering `eS` of their states; pairs are encoded by
`encPair encBits encBits`. Nothing is required of `U` on other inputs. -/
def IsUniversal {k : ℕ} {S : Type*} (U : MultiTapeTM k Bool S) : Prop :=
  ∀ ⦃k' : ℕ⦄ ⦃State : Type⦄ [Fintype State] (eS : State ↪ ℕ) (M : MultiTapeTM k' Bool State)
    (x o : List Bool),
    U.Computes (encPair encBits encBits (eDesc (desc eS eBit M), x)) o ↔ M.Computes x o

namespace IsUniversal

variable {k : ℕ} {S : Type*} {U : MultiTapeTM k Bool S}

/-- **Complexity with respect to a universal machine**
[Goldreich, Theorem 1.10][Goldreich2006DraftR1]. For every machine `M` there is a constant `c`
with `K_U(s) ≤ K_M(s) + c` for every string `s`. The constant is `2 |⟨M⟩| + 1` for the description
`⟨M⟩ = eDesc (desc eS eBit M)` under any numbering `eS` of the states of `M`. -/
theorem exists_ecomplexity_le (hU : U.IsUniversal) {k' : ℕ} {State : Type} [Finite State]
    (M : MultiTapeTM k' Bool State) :
    ∃ c : ℕ, ∀ s : List Bool,
      (ofMultiTapeTM U).ecomplexity s ≤ (ofMultiTapeTM M).ecomplexity s + c := by
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  let w := eDesc (desc eS eBit M)
  obtain ⟨τ, ⟨S⟩⟩ := exists_simulation_of_produces (M := ofMultiTapeTM M)
    (N := ofMultiTapeTM U) (c := 2 * w.length + 1)
    (fun p => encPair encBits encBits (w, p))
    (fun p => by rw [length_encPair]; simp [encBits]; omega)
    fun {p x} h => ofMultiTapeTM_produces_iff.mpr
      ((hU eS M _ _).mpr (ofMultiTapeTM_produces_iff.mp h))
  exact ⟨_, S.ecomplexity_le⟩

end IsUniversal

end Turing.MultiTapeTM
