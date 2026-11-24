/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.SLHDSA.HashCalls
public import CslibFrontier.Crypto.Primitives.SLHDSA.WOTS.Digits

/-!
# FIPS 205 WOTS+ hash chains

This module implements the WOTS+ chaining function from FIPS 205, Section 5, Algorithm 5.
Starting from a value `X` at chain index `i`, `chain` iterates the addressed function `F` (`f`)
over the steps `j = i, ..., i + s - 1`, writing `j` to the hash-address word before step `j`. The
source condition `i + s < w` is a proof argument, not a runtime failure; it bounds every
hash-address word that is written.

Algorithm 5 is called with an address of type `WOTS_HASH`. As for the addressed calls it is built
from, `chain` accepts every `Address`, and setting the address type is the caller's
responsibility.

This is an executable fixed-parameter construction. It does not implement WOTS+ key generation,
signing, public-key reconstruction, correctness or security, and it does not supply hash-call
counts or machine, program-size, gate, qubit or query costs.

## Main definitions

* `Cslib.Crypto.SLHDSA.WOTS.chain`: FIPS 205 Algorithm 5.

## Main results

* `Cslib.Crypto.SLHDSA.WOTS.chain_add`: adjacent chain segments compose.

## References

* [NIST, *Stateless Hash-Based Digital Signature Standard*, Section 5,
  Algorithm 5][NISTFIPS205]
-/

public section

namespace Cslib.Crypto.SLHDSA.WOTS

open Cslib.Crypto.SLHDSA

/-- FIPS 205 Algorithm 5 (`chain`): starting from `X`, step `j = i, ..., i + s - 1` writes `j` to
the hash-address word and applies the addressed function `F`. The proof argument is the source's
range condition `i + s < w`. -/
def chain (family : HashFamily) {p : SecurityBytes} (X : NBytes p) (i s : ℕ)
    (publicSeed : NBytes p) (address : Address) (hrange : i + s < w) : NBytes p :=
  match s with
  | 0 => X
  | s + 1 =>
      f family publicSeed
        (address.setHashAddress ⟨i + s, (show i + s < w by omega).trans (by decide)⟩)
        (chain family X i s publicSeed address (by omega))

/-- A zero-step chain is the identity, including at a nonzero valid start index. -/
@[simp] theorem chain_zero (family : HashFamily) {p : SecurityBytes} (X : NBytes p) (i : ℕ)
    (publicSeed : NBytes p) (address : Address) (hrange : i + 0 < w) :
    chain family X i 0 publicSeed address hrange = X :=
  (rfl)

/-- The last step of a nonempty chain writes hash address `i + s` and applies `F` to the value
reached by the first `s` steps. -/
theorem chain_succ (family : HashFamily) {p : SecurityBytes} (X : NBytes p) (i s : ℕ)
    (publicSeed : NBytes p) (address : Address) (hrange : i + (s + 1) < w) :
    chain family X i (s + 1) publicSeed address hrange =
      f family publicSeed
        (address.setHashAddress ⟨i + s, (show i + s < w by omega).trans (by decide)⟩)
        (chain family X i s publicSeed address (by omega)) :=
  (rfl)

/-- Running `s` steps and then `t` adjacent steps is the same as running `s + t` steps. -/
theorem chain_add (family : HashFamily) {p : SecurityBytes} (X : NBytes p) (i s t : ℕ)
    (publicSeed : NBytes p) (address : Address) (hrange : i + (s + t) < w) :
    chain family (chain family X i s publicSeed address (by omega)) (i + s) t publicSeed address
        (by omega) =
      chain family X i (s + t) publicSeed address hrange := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [chain_succ, ih (by omega)]
      refine Eq.trans ?_ (chain_succ family X i (s + t) publicSeed address hrange).symm
      simp only [Nat.add_assoc]

end Cslib.Crypto.SLHDSA.WOTS
