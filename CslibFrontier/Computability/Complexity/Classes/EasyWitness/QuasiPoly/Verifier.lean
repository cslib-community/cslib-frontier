/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NQuasiP
public import CslibFrontier.Computability.Complexity.Classes.NP.Nondeterministic
public import CslibFrontier.Computability.Complexity.Classes.Time.Verifier
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Verifiers with quasi-polynomially long witnesses: membership in `NQuasiP`

A verifier for a language in `NQuasiP = ⋃ₖ NTIME (2 ^ (log₂ n + 1) ^ k)`
(`Cslib.Complexity.EasyWitness.QuasiPolyVerifier`) is a function `verify` of an instance
`x` and a witness of length exactly `witnessLen x`, where the length is computable in polynomial
time in binary and is at most `2 ^ O((log |x|) ^ k)`, and `verify` runs in time
`2 ^ O((log |x|) ^ k)` on witnesses of the right length. The instances with an accepted witness
form a language in `NQuasiP`
(`Cslib.Complexity.EasyWitness.QuasiPolyVerifier.language_mem_NQuasiP`). This is the
quasi-polynomial analogue of `Cslib.Complexity.EasyWitness.NEVerifier` [MurrayWilliams2018].

## Main definitions

* `Cslib.Complexity.EasyWitness.QuasiPolyVerifier`: a verifier with its bounds.
* `Cslib.Complexity.EasyWitness.QuasiPolyVerifier.language`: its language.

## Main results

* `Cslib.Complexity.EasyWitness.QuasiPolyVerifier.language_mem_NQuasiP`: the language
  is in `NQuasiP`.

## References

* [C. D. Murray, R. R. Williams, *Circuit lower bounds for nondeterministic quasi-polytime: an
  easy witness lemma for NP and NQP*][MurrayWilliams2018]
-/

open Turing Turing.MultiTapeTM

public section

namespace Cslib.Complexity.EasyWitness

/-- **A verifier for a language in `NQuasiP`.** The witnesses of an instance `x` have
`witnessLen x` bits, a number computable in polynomial time into binary with
`witnessLen x < 2 ^ (log₂ |x| + 1) ^ B` for some `B`; the verifier `verify` is computable on
multi-tape machines within time `time` and space `space`, with
`time (x, y) ≤ C 2 ^ (log₂ |x| + 1) ^ k` on the witnesses `y` of length `witnessLen x`, for some `C`
and `k`. -/
structure QuasiPolyVerifier where
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
  /-- The witnesses are quasi-polynomially long. -/
  witnessLen_lt : ∃ B, ∀ x, witnessLen x + 1 ≤ 2 ^ (Nat.log 2 x.length + 1) ^ B
  /-- The verifier runs in quasi-polynomial time on witnesses of the right length. -/
  time_le : ∃ C k, ∀ x y, y.length = witnessLen x →
    time (x, y) ≤ C * 2 ^ (Nat.log 2 x.length + 1) ^ k

namespace QuasiPolyVerifier

variable (V : QuasiPolyVerifier)

/-- The language of a verifier: the instances with an accepted witness of the right length. -/
def language : Set (List Bool) :=
  {x | ∃ y : List Bool, y.length = V.witnessLen x ∧ V.verify (x, y) = true}

/-- An instance is in the language of a verifier when it has an accepted witness. -/
theorem mem_language_iff (x : List Bool) :
    x ∈ V.language ↔ ∃ y : List Bool, y.length = V.witnessLen x ∧ V.verify (x, y) = true :=
  Iff.rfl

/-- **Guess and verify in time `2 ^ O((log n) ^ k)`**: the language of a verifier is in
`NQuasiP`. -/
theorem language_mem_NQuasiP : V.language ∈ NQuasiP encBits := by
  obtain ⟨B, hB⟩ := V.witnessLen_lt
  obtain ⟨C₂, k₂, hT⟩ := V.time_le
  obtain ⟨dC, _, hcert_deg⟩ := V.witnessLen_polyTime.exists_degree
  have hℓU := ComputableInO.comp ComputableInO.natToUnary hcert_deg.inO
  refine mem_NQuasiP_iff.mpr ⟨dC + B + k₂ + 1, ?_⟩
  refine setOf_exists_mem_NTIME
    (t := fun n => 2 ^ (Nat.log 2 n + 1) ^ (dC + B + k₂ + 1)) hℓU V.verify_computableInO
    (C := 2 + 2 ^ dC + C₂) fun w c hc => ?_
  set n := w.length with hn
  set L := Nat.log 2 n + 1 with hL
  set P := 2 ^ L ^ (dC + B + k₂ + 1) with hP
  have hL1 : 0 < L := Nat.succ_pos _
  have hk : ∀ e, e ≤ dC + B + k₂ + 1 → 2 ^ L ^ e ≤ P := fun e he =>
    Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right hL1 he)
  have e1 : n ≤ P :=
    calc n ≤ 2 ^ L := (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le
      _ = 2 ^ L ^ 1 := by rw [pow_one]
      _ ≤ P := hk 1 (by omega)
  have e2 : (n + 1) ^ dC ≤ 2 ^ dC * P :=
    (pow_succ_le_mul_two_pow_log dC n).trans
      (Nat.mul_le_mul_left _ (hk (dC + 1) (by omega)))
  have e3 : V.witnessLen w ≤ P := by
    have hBw : V.witnessLen w + 1 ≤ 2 ^ L ^ B := hB w
    have := hk B (by omega)
    omega
  have e4 : V.time (w, c) ≤ C₂ * P :=
    (hT w c hc).trans (Nat.mul_le_mul_left _ (hk k₂ (by omega)))
  change n + ((n + 1) ^ dC + V.witnessLen w) + V.time (w, c) ≤
    (2 + 2 ^ dC + C₂) * P + (2 + 2 ^ dC + C₂)
  clear_value P
  calc n + ((n + 1) ^ dC + V.witnessLen w) + V.time (w, c)
      ≤ P + (2 ^ dC * P + P) + C₂ * P := by omega
    _ = (2 + 2 ^ dC + C₂) * P := by ring
    _ ≤ _ := Nat.le_add_right _ _

end QuasiPolyVerifier

end Cslib.Complexity.EasyWitness
