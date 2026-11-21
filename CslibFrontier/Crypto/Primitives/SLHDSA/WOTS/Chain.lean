/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.SLHDSA.HashCalls
public import CslibFrontier.Crypto.Primitives.SLHDSA.WOTS.Digits
import Mathlib.Tactic

/-!
# FIPS 205 WOTS+ hash chains

This module implements the WOTS+ chaining function from FIPS 205, Section 5, Algorithm 5.
Starting at chain index `i`, `chain` applies the concrete addressed function `F` exactly `s`
times. Before step `j`, it writes `j` to the hash-address word. The source conditions that the
address has type `WOTS_HASH` and that `i + s < w` are erased proof arguments, not new runtime
failures.

This is an executable fixed-parameter construction. It does not implement WOTS+ key generation,
signing, public-key reconstruction, correctness or security, and it does not supply machine,
program-size, gate, qubit or query costs.

## Main definitions

* `Cslib.Crypto.SLHDSA.WOTS.ValidHashAddress`: the Algorithm 5 address-type precondition.
* `Cslib.Crypto.SLHDSA.WOTS.ValidChainRange`: the source condition `i + s < w`.
* `Cslib.Crypto.SLHDSA.WOTS.chainWithCalls`: Algorithm 5 with its source-call ledger.
* `Cslib.Crypto.SLHDSA.WOTS.chain`: FIPS 205 Algorithm 5.
* `Cslib.Crypto.SLHDSA.WOTS.ChainCalls`: the exact source-level call and address-write counts.

## Main results

* `Cslib.Crypto.SLHDSA.WOTS.chainWithCalls_calls`: the instrumented ledger is exactly
  `chainCalls s`.
* `Cslib.Crypto.SLHDSA.WOTS.chain_zero`: a zero-step chain returns its input.
* `Cslib.Crypto.SLHDSA.WOTS.chain_add`: adjacent chain segments compose.

## References

* [NIST, *Stateless Hash-Based Digital Signature Standard*, Section 5,
  Algorithm 5][NISTFIPS205]
-/

public section

namespace Cslib.Crypto.SLHDSA.WOTS

open Cslib.Crypto.SLHDSA

/-- Algorithm 5 requires an address whose type has already been set to `WOTS_HASH`. -/
@[expose] def ValidHashAddress (address : Address) : Prop :=
  address.addressType = .wotsHash

instance (address : Address) : Decidable (ValidHashAddress address) := by
  unfold ValidHashAddress
  infer_instance

/-- The source range condition for Algorithm 5. -/
@[expose] def ValidChainRange (i s : ℕ) : Prop :=
  i + s < w

instance (i s : ℕ) : Decidable (ValidChainRange i s) := by
  unfold ValidChainRange
  infer_instance

/-- Exact source-level counts for one Algorithm 5 invocation. -/
structure ChainCalls where
  /-- Calls to the concrete addressed function `F`. -/
  fCalls : ℕ
  /-- Writes to the hash-address word. -/
  hashAddressWrites : ℕ
  deriving DecidableEq, Repr

/-- Algorithm 5 performs one `F` call and one hash-address write per requested step. -/
@[expose] def chainCalls (s : ℕ) : ChainCalls :=
  ⟨s, s⟩

/-- The result and source-call ledger of an instrumented Algorithm 5 invocation. -/
structure ChainRun (p : SecurityBytes) where
  /-- The final `n`-byte chain value. -/
  output : NBytes p
  /-- The `F` calls and hash-address writes made by the recursion. -/
  calls : ChainCalls

/-- Instrumented FIPS 205 Algorithm 5. Its recursion constructs both the chain output and the
ledger, so the counts are tied to the executable control flow. -/
def chainWithCalls (family : HashFamily) {p : SecurityBytes} (X : NBytes p) (i s : ℕ)
    (publicSeed : NBytes p) (address : Address) (_haddress : ValidHashAddress address)
    (hrange : ValidChainRange i s) : ChainRun p :=
  match s with
  | 0 => ⟨X, chainCalls 0⟩
  | s + 1 =>
      let previous := chainWithCalls family X i s publicSeed address _haddress (by
        unfold ValidChainRange at hrange ⊢
        omega)
      { output := f family publicSeed
          (address.setHashAddress ⟨i + s, (by
            unfold ValidChainRange at hrange
            have his : i + s < w := by omega
            exact his.trans (by decide))⟩)
          previous.output
        calls :=
          { fCalls := previous.calls.fCalls + 1
            hashAddressWrites := previous.calls.hashAddressWrites + 1 } }
termination_by s

/-- The instrumented Algorithm 5 recursion accumulates exactly one call and write per step. -/
@[simp] theorem chainWithCalls_calls (family : HashFamily) {p : SecurityBytes} (X : NBytes p)
    (i s : ℕ) (publicSeed : NBytes p) (address : Address)
    (haddress : ValidHashAddress address) (hrange : ValidChainRange i s) :
    (chainWithCalls family X i s publicSeed address haddress hrange).calls = chainCalls s := by
  induction s with
  | zero => simp only [chainWithCalls]
  | succ s ih =>
      simp only [chainWithCalls]
      rw [ih]
      rfl

/-- FIPS 205 Algorithm 5. The proof arguments enforce the source's address-type and range
conditions without adding a runtime branch. -/
def chain (family : HashFamily) {p : SecurityBytes} (X : NBytes p) (i s : ℕ)
    (publicSeed : NBytes p) (address : Address) (haddress : ValidHashAddress address)
    (hrange : ValidChainRange i s) : NBytes p :=
  (chainWithCalls family X i s publicSeed address haddress hrange).output

/-- `chain` is the output projection of the instrumented Algorithm 5 evaluator. -/
theorem chainWithCalls_output (family : HashFamily) {p : SecurityBytes} (X : NBytes p)
    (i s : ℕ) (publicSeed : NBytes p) (address : Address)
    (haddress : ValidHashAddress address) (hrange : ValidChainRange i s) :
    (chainWithCalls family X i s publicSeed address haddress hrange).output =
      chain family X i s publicSeed address haddress hrange :=
  (rfl)

/-- A zero-step chain is the identity, including at a nonzero valid start index. -/
@[simp] theorem chain_zero (family : HashFamily) {p : SecurityBytes} (X : NBytes p) (i : ℕ)
    (publicSeed : NBytes p) (address : Address) (haddress : ValidHashAddress address)
    (hrange : ValidChainRange i 0) :
    chain family X i 0 publicSeed address haddress hrange = X := by
  simp only [chain, chainWithCalls]

/-- The last step of a nonempty chain writes hash address `i + s` and makes one call to `F`. -/
theorem chain_succ (family : HashFamily) {p : SecurityBytes} (X : NBytes p) (i s : ℕ)
    (publicSeed : NBytes p) (address : Address) (haddress : ValidHashAddress address)
    (hrange : ValidChainRange i (s + 1)) :
    chain family X i (s + 1) publicSeed address haddress hrange =
      f family publicSeed
        (address.setHashAddress ⟨i + s, (by
          unfold ValidChainRange at hrange
          have his : i + s < w := by omega
          exact his.trans (by decide))⟩)
        (chain family X i s publicSeed address haddress (by
          unfold ValidChainRange at hrange ⊢
          omega)) :=
  by simp only [chain, chainWithCalls]

/-- Running `s` steps and then `t` adjacent steps is the same as running `s + t` steps. -/
theorem chain_add (family : HashFamily) {p : SecurityBytes} (X : NBytes p) (i s t : ℕ)
    (publicSeed : NBytes p) (address : Address) (haddress : ValidHashAddress address)
    (hrange : ValidChainRange i (s + t)) :
    chain family
        (chain family X i s publicSeed address haddress (by
          unfold ValidChainRange at hrange ⊢
          omega))
        (i + s) t publicSeed address haddress (by
          unfold ValidChainRange at hrange ⊢
          omega) =
      chain family X i (s + t) publicSeed address haddress hrange := by
  induction t generalizing X with
  | zero => simp only [Nat.add_zero, chain_zero]
  | succ t ih =>
      rw [chain_succ]
      rw [ih X (by
        unfold ValidChainRange at hrange ⊢
        omega)]
      symm
      convert chain_succ family X i (s + t) publicSeed address haddress (by
        unfold ValidChainRange at hrange ⊢
        omega) using 1
      congr 3
      omega

@[simp] theorem chainCalls_fCalls (s : ℕ) : (chainCalls s).fCalls = s :=
  rfl

@[simp] theorem chainCalls_hashAddressWrites (s : ℕ) :
    (chainCalls s).hashAddressWrites = s :=
  rfl

end Cslib.Crypto.SLHDSA.WOTS
