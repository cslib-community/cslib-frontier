/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.Classes.NP.Nondeterministic
public import CslibFrontier.Computability.Complexity.Classes.Time.Verifier
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Complexity.Problems.NEXPBoundedAcceptance
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.SuccPow

/-!
# Verifiers with exponentially long witnesses: membership in `NE`

A verifier for a language in `NE = ⋃ₖ NTIME (2 ^ (k n))`
(`Cslib.Complexity.EasyWitness.NEVerifier`) is a function `verify` of an instance `x` and a
witness of length exactly `witnessLen x`, where the length is computable in polynomial time in
binary and is at most `2 ^ O(|x|)`, and `verify` runs in time `2 ^ O(|x|)` on witnesses of the right
length. The instances with an accepted witness form a language in `NE`
(`Cslib.Complexity.EasyWitness.NEVerifier.language_mem_NE`). This is the shape of
`Cslib.Complexity.NEXPBoundedAcceptance.mem_NE`, with the bounds as fields instead of being read
off an instance.

## Main definitions

* `Cslib.Complexity.EasyWitness.NEVerifier`: a verifier with its bounds.
* `Cslib.Complexity.EasyWitness.NEVerifier.language`: its language.

## Main results

* `Cslib.Complexity.EasyWitness.NEVerifier.language_mem_NE`: the language is in `NE`.
-/

open Turing Turing.MultiTapeTM

public section

namespace Cslib.Complexity.EasyWitness

/-- **A verifier for a language in `NE`.** The witnesses of an instance `x` have `witnessLen x`
bits, a number computable in polynomial time into binary with `witnessLen x < 2 ^ (B (|x| + 1))`
for some `B`; the verifier `verify` is computable on multi-tape machines within time `time` and
space `space`, with `time (x, y) ≤ C 2 ^ (k |x|)` on the witnesses `y` of length `witnessLen x`,
for some `C` and `k`. -/
structure NEVerifier where
  /-- The length of the witnesses of an instance. -/
  witnessLen : List Bool → ℕ
  /-- The verifier, on an instance and a witness. -/
  verify : List Bool × List Bool → Bool
  /-- The running time of the verifier. -/
  time : List Bool × List Bool → ℕ
  /-- The space of the verifier. -/
  space : List Bool × List Bool → ℕ
  /-- The witness length is computable in polynomial time, in binary. -/
  witnessLen_polyTime : ComputableInPolyTime witnessLen encBits encNat
  /-- The verifier is computable within time `time` and space `space`. -/
  verify_computableInO : ComputableInO verify (encPair encBits encBits) encBool time space
  /-- The witnesses are exponentially long. -/
  witnessLen_lt : ∃ B, ∀ x, witnessLen x + 1 ≤ 2 ^ (B * (x.length + 1))
  /-- The verifier runs in exponential time on witnesses of the right length. -/
  time_le : ∃ C k, ∀ x y, y.length = witnessLen x → time (x, y) ≤ C * 2 ^ (k * x.length)

namespace NEVerifier

variable (V : NEVerifier)

/-- The language of a verifier: the instances with an accepted witness of the right length. -/
def language : Set (List Bool) :=
  {x | ∃ y : List Bool, y.length = V.witnessLen x ∧ V.verify (x, y) = true}

/-- An instance is in the language of a verifier when it has an accepted witness. -/
theorem mem_language_iff (x : List Bool) :
    x ∈ V.language ↔ ∃ y : List Bool, y.length = V.witnessLen x ∧ V.verify (x, y) = true :=
  Iff.rfl

/-- **Guess and verify in time `2 ^ O(n)`**: the language of a verifier is in `NE`. -/
theorem language_mem_NE : V.language ∈ NE encBits := by
  obtain ⟨B, hB⟩ := V.witnessLen_lt
  obtain ⟨C₂, k₂, hT⟩ := V.time_le
  obtain ⟨dC, _, hcert_deg⟩ := V.witnessLen_polyTime.exists_degree
  have hℓU := ComputableInO.comp ComputableInO.natToUnary hcert_deg.inO
  rw [NE, Set.mem_iUnion]
  refine ⟨dC + B + k₂ + 1, ?_⟩
  refine setOf_exists_mem_NTIME (t := fun n => 2 ^ ((dC + B + k₂ + 1) * n)) hℓU
    V.verify_computableInO (C := 3 + 2 ^ B + C₂) fun w c hc => ?_
  set n := w.length with hn
  set P := 2 ^ ((dC + B + k₂ + 1) * n) with hP
  have hk : ∀ e, e ≤ dC + B + k₂ + 1 → 2 ^ (e * n) ≤ P := fun e he =>
    Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right n he)
  have hn1 : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have e1 : n + 1 ≤ P := hn1.trans (by simpa using hk 1 (by omega))
  have e2 : (n + 1) ^ dC ≤ P := (Nat.succ_pow_le_two_pow_mul n dC).trans (hk dC (by omega))
  have e3 : V.witnessLen w ≤ 2 ^ B * P :=
    calc V.witnessLen w ≤ 2 ^ (B * (n + 1)) := by
          have hBw : V.witnessLen w + 1 ≤ 2 ^ (B * (n + 1)) := hB w
          omega
      _ = 2 ^ B * 2 ^ (B * n) := by rw [mul_add, mul_one, pow_add, mul_comm]
      _ ≤ 2 ^ B * P := Nat.mul_le_mul_left _ (hk B (by omega))
  have e4 : V.time (w, c) ≤ C₂ * P :=
    (hT w c hc).trans (Nat.mul_le_mul_left _ (hk k₂ (by omega)))
  change n + ((n + 1) ^ dC + V.witnessLen w) + V.time (w, c) ≤
    (3 + 2 ^ B + C₂) * P + (3 + 2 ^ B + C₂)
  nlinarith

end NEVerifier

end Cslib.Complexity.EasyWitness
