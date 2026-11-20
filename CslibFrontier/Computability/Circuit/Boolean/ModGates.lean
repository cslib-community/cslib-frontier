/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AC0

/-!
# Constant-depth modular circuits

The basis of AC⁰ together with `MOD_q` gates of unbounded fan-in, which output `true` exactly when
the number of their true inputs is not divisible by `q` (`modGate`), and the class **AC⁰[q]** of
languages decided by such circuits of polynomial size and constant depth
[Arora and Barak, Section 14.2][AroraBarak09]: the unbounded fan-in basis extended by `MOD_q`
(`Unbounded.extInterpretation (modGate q)`).

## Main definitions

* `Cslib.Circuits.Boolean.modGate`: the `MOD_q` gate.
* `Cslib.Circuits.Boolean.AC0Mod`: the class AC⁰[q].
* `Cslib.Circuits.Boolean.CC0Mod`, `Cslib.Circuits.Boolean.CC0`: the classes with a purely modular
  basis, with one modulus fixed for the family [Chapman and Williams][ChapmanWilliams2022].

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

/-- The `MOD_q` gate: whether the number of true bits of `x` is not divisible by `q`. -/
def modGate (q m : ℕ) (x : Fin m → Bool) : Bool :=
  decide ((Finset.univ.filter fun i => x i = true).card % q ≠ 0)

/-- For `q = 2`, `modGate 2 m` is the `m`-bit parity function `parity m`. -/
theorem modGate_two_eq_parity (m : ℕ) : modGate 2 m = parity m := by
  funext x
  simp only [modGate, parity, parityOn, ne_eq, Nat.mod_two_ne_zero]

/-- **AC⁰[q]**: the languages over `Bool` decided, at every input length, by circuits with `MOD_q`
gates of polynomially bounded size and constant depth. -/
def AC0Mod (q : ℕ) : Set (Language Bool) :=
  ConstDepth (Unbounded.extInterpretation (modGate q))

/-- **AC⁰ ⊆ AC⁰[q]**: every AC⁰ circuit is a circuit with `MOD_q` gates. -/
theorem AC0_subset_AC0Mod (q : ℕ) : AC0 ⊆ AC0Mod q :=
  ConstDepth.mono Unbounded.toExt

namespace Modular

/-- A modular basis with two constant inputs and a modular gate of each finite arity. -/
abbrev signature : Signature :=
  ⟨Bool ⊕ ℕ, Sum.elim (fun _ => 0) id⟩

/-- Interpret the modular gates with one common modulus `q`. -/
def interpretation (q : ℕ) : Interpretation signature Bool
  | .inl b, _ => b
  | .inr m, x => modGate q m x

end Modular

/-- **CC⁰[q]**: polynomial size and constant depth using only `MOD_q` gates and Boolean
constants. -/
def CC0Mod (q : ℕ) : Set (Language Bool) := ConstDepth (Modular.interpretation q)

/-- **CC⁰**: constant-depth modular circuits with one fixed modulus at least two for all input
lengths [Chapman and Williams][ChapmanWilliams2022]. -/
def CC0 : Set (Language Bool) := {L | ∃ q ≥ 2, L ∈ CC0Mod q}

end Cslib.Circuits.Boolean
