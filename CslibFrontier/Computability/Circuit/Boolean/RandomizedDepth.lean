/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.DepthClasses
public import CslibFrontier.Computability.Circuit.Boolean.Encoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace

/-!
# Randomized polylogarithmic-depth circuits

The `RNC` circuits at input length `n` receive the input bits followed by independent fair
random bits. Members are accepted on at least half of the random strings and nonmembers
are rejected on every random string. Uniformity means that a deterministic logspace
transducer takes unary `n` and outputs the complete encoded circuit. These are the
one-sided error convention of the [Complexity Zoo](https://complexityzoo.net/Complexity_Zoo:R#rnc)
and the logspace circuit generator convention in [Cook, §2]
(https://www.cs.utoronto.ca/~sacook/homepage/taxonomy.pdf).

The logarithmic-depth specialization explicitly uses logspace uniformity. Cook's
extended-connection uniformity at level one requires a separate definition.
The `NonuniformRNC` levels drop the generator constraint altogether.

## Main definitions

* `RNC`: logspace-uniform one-sided randomized polynomial-size polylogarithmic-depth circuits.
* `LogSpaceUniformRNC1`: the logspace-uniform logarithmic-depth specialization.
* `NonuniformRNCLevel`: one-sided error at fixed polylogarithmic depth.
* `NonuniformRNC`: the union of the nonuniform levels.
* `NonuniformRNC1`: the nonuniform logarithmic-depth level.
-/

public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM

/-- At length `n`, the circuit rejects all nonmembers and accepts each member on
at least half of the strings on its `r` random inputs. -/
@[expose] def HasOneSidedError {n r : ℕ} (C : Circuit signature (n + r) 1)
    (L : Language Bool) : Prop :=
  ∀ x : Fin n → Bool,
    let accepts (coins : Fin r → Bool) := C.eval interpretation (Fin.append x coins) 0
    (L.slice n x = true → 2 ^ r ≤ 2 * (Finset.univ.filter fun coins => accepts coins = true).card) ∧
    (L.slice n x = false → ∀ coins, accepts coins = false)

/-- Languages decided by logspace-uniform one-sided randomized circuits of polynomial size
and depth `O((log n) ^ i)`. The generator outputs the total input count and the circuit. -/
@[expose] def LogSpaceUniformRNCLevel (i : ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (s r : ℕ → ℕ), PolynomiallyBounded s ∧ PolynomiallyBounded r ∧
    ∃ C : ∀ n, Circuit signature (n + r n) 1,
      ComputableInLogSpace (fun n => ⟨n + r n, C n⟩) encUnary (encCircuit 1) ∧
      ∀ n, (C n).depth ≤ c * (Nat.log 2 n + 1) ^ i ∧ (C n).size ≤ s n ∧
        HasOneSidedError (C n) L}

/-- The union of the logspace-uniform one-sided randomized depth levels. -/
@[expose] def RNC : Set (Language Bool) := ⋃ i, LogSpaceUniformRNCLevel i

/-- One-sided randomized logarithmic depth with a logspace circuit generator. -/
abbrev LogSpaceUniformRNC1 : Set (Language Bool) := LogSpaceUniformRNCLevel 1

/-- Languages decided by a nonuniform family of polynomial-size, bounded-fan-in circuits
of depth `O((log n) ^ i)`. Members are accepted on at least half of the random strings.
Nonmembers are rejected on every random string. -/
def NonuniformRNCLevel (i : ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (s r : ℕ → ℕ), PolynomiallyBounded s ∧ PolynomiallyBounded r ∧
    ∀ n, ∃ C : Circuit signature (n + r n) 1,
      C.depth ≤ c * (Nat.log 2 n + 1) ^ i ∧ C.size ≤ s n ∧ HasOneSidedError C L}

/-- Forgetting the circuit generator preserves the size, depth and error bounds. -/
theorem logSpaceUniformRNCLevel_subset_nonuniformRNCLevel (i : ℕ) :
    LogSpaceUniformRNCLevel i ⊆ NonuniformRNCLevel i := by
  rintro L ⟨c, s, r, hs, hr, C, _, hC⟩
  exact ⟨c, s, r, hs, hr, fun n => ⟨C n, hC n⟩⟩

/-- The languages in some randomized polylogarithmic-depth level. -/
def NonuniformRNC : Set (Language Bool) := ⋃ i, NonuniformRNCLevel i

/-- The first randomized NC level, with logarithmic depth. -/
def NonuniformRNC1 : Set (Language Bool) := NonuniformRNCLevel 1

end Cslib.Circuits.Boolean
