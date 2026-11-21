/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.SLHDSA.WOTS.Chain
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# FIPS 205 WOTS+ public-key reconstruction

This module implements FIPS 205, Section 5.3, Algorithm 8. It reconstructs the WOTS+ public-key
value associated with a message and signature: the common message/checksum digits select the
start of each remaining hash-chain suffix, the chain end nodes are concatenated in canonical
order, and one concrete `T_len` call compresses them under a `WOTS_PK` address.

The input address has the source precondition that its type is `WOTS_HASH`. The transition to
`WOTS_PK` clears all type-dependent words before restoring only the key-pair word, exactly as in
Algorithm 8. The executable source exposes exact hash-call, address-write and block-shape counts.
Lower-level permutation/compression costs and machine, program-size, gate, qubit and query costs
remain open.

This module does not implement WOTS+ key generation or signing, prove that a generated signature
reconstructs its generated public key, or establish one-time, classical or quantum security.

## Main definitions

* `Cslib.Crypto.SLHDSA.WOTS.Signature`: exactly `len` consecutive `n`-byte blocks.
* `Cslib.Crypto.SLHDSA.WOTS.chainEndRuns`: the instrumented Algorithm 5 calls for every block.
* `Cslib.Crypto.SLHDSA.WOTS.chainEndNodes`: the Algorithm 8 chain-end array.
* `Cslib.Crypto.SLHDSA.WOTS.publicKeyInput`: the canonical `len * n` byte compression input.
* `Cslib.Crypto.SLHDSA.WOTS.wotsPkFromSigWithCalls`: Algorithm 8 with its source-call ledger.
* `Cslib.Crypto.SLHDSA.WOTS.wotsPkFromSig`: FIPS 205 Algorithm 8.
* `Cslib.Crypto.SLHDSA.WOTS.PublicKeyFromSigCalls`: exact source-level calls and data shapes.

## Main results

* `Cslib.Crypto.SLHDSA.WOTS.publicKeyInput_apply`: the compression input preserves block order.
* `Cslib.Crypto.SLHDSA.WOTS.wotsPkFromSigWithCalls_calls`: the instrumented ledger is exactly
  `publicKeyFromSigCalls M`.
* `Cslib.Crypto.SLHDSA.WOTS.totalChainSteps_le`: at most `len * (w - 1)` calls to `F`.

## References

* [NIST, *Stateless Hash-Based Digital Signature Standard*, Sections 5 and 5.3,
  Algorithms 5 and 8][NISTFIPS205]
-/

public section

namespace Cslib.Crypto.SLHDSA.WOTS

open Cslib.BitString Cslib.Crypto Cslib.Crypto.SLHDSA
open scoped BigOperators

/-- A WOTS+ signature is exactly `len` consecutive `n`-byte strings. -/
abbrev Signature (p : SecurityBytes) := Fin (len p) → NBytes p

/-- The exact number of remaining chain steps, hence of `F` calls, in Algorithm 8. -/
@[expose] def totalChainSteps {p : SecurityBytes} (M : Message p) : ℕ :=
  Finset.univ.sum fun i : Fin (len p) => w - 1 - (digits M i).val

/-- Every Algorithm 8 chain suffix has at most `w - 1` steps. -/
theorem totalChainSteps_le {p : SecurityBytes} (M : Message p) :
    totalChainSteps M ≤ len p * (w - 1) := by
  unfold totalChainSteps
  calc
    Finset.univ.sum (fun i : Fin (len p) => w - 1 - (digits M i).val) ≤
        Finset.univ.sum (fun _i : Fin (len p) => w - 1) :=
      Finset.sum_le_sum fun _i _hi => Nat.sub_le _ _
    _ = len p * (w - 1) := by simp

/-- Exact source-level calls, address writes and byte shapes for Algorithm 8.

The fields count the executable specification. They are not a machine trace or a compiled-program
cost: in particular they do not charge hash permutations/compressions, controllers, layouts,
copies, interpreter work, handlers, advice or static tables. -/
@[ext] structure PublicKeyFromSigCalls where
  /-- Number of WOTS+ chain suffixes. -/
  chainTraversals : ℕ
  /-- Writes to the chain-address word. -/
  chainAddressWrites : ℕ
  /-- Calls to the concrete addressed function `F`. -/
  fCalls : ℕ
  /-- Writes to the hash-address word. -/
  hashAddressWrites : ℕ
  /-- Calls to `setTypeAndClear WOTS_PK`. -/
  typeAndClearCalls : ℕ
  /-- Writes restoring the key-pair word. -/
  keyPairAddressWrites : ℕ
  /-- Calls to the concrete `T_len` function. -/
  tLCalls : ℕ
  /-- Number of `n`-byte blocks in the compression input. -/
  compressionBlocks : ℕ
  /-- Number of bytes in the compression input. -/
  compressionInputBytes : ℕ
  /-- Number of output bytes. -/
  outputBytes : ℕ
  deriving DecidableEq, Repr

/-- The closed form for the exact Algorithm 8 source ledger on message `M`. -/
@[expose] def publicKeyFromSigCalls {p : SecurityBytes} (M : Message p) :
    PublicKeyFromSigCalls :=
  { chainTraversals := len p
    chainAddressWrites := len p
    fCalls := totalChainSteps M
    hashAddressWrites := totalChainSteps M
    typeAndClearCalls := 1
    keyPairAddressWrites := 1
    tLCalls := 1
    compressionBlocks := len p
    compressionInputBytes := len p * p.count
    outputBytes := p.count }

private def chainIndexAddressWord {p : SecurityBytes} (i : Fin (len p)) : AddressWord :=
  ⟨i, i.isLt.trans_le ((len_le_67 p).trans (by decide))⟩

/-- Algorithm 8 lines 12--14: clear the payload while changing to `WOTS_PK`, then restore the
key-pair word from the WOTS hash address. -/
@[expose] def publicKeyAddress (address : Address) : Address :=
  (address.setTypeAndClear .wotsPK).setKeyPairAddress address.word5

@[simp] theorem publicKeyAddress_type (address : Address) :
    (publicKeyAddress address).addressType = .wotsPK :=
  rfl

@[simp] theorem publicKeyAddress_keyPair (address : Address) :
    (publicKeyAddress address).word5 = address.word5 :=
  rfl

@[simp] theorem publicKeyAddress_padding (address : Address) :
    (publicKeyAddress address).word6 = 0 ∧ (publicKeyAddress address).word7 = 0 :=
  ⟨rfl, rfl⟩

/-- Algorithm 8 lines 8--11, instrumented: finish every chain from the signature-selected node
and retain its Algorithm 5 ledger. -/
def chainEndRuns (family : HashFamily) {p : SecurityBytes} (sig : Signature p) (M : Message p)
    (publicSeed : NBytes p) (address : Address) (haddress : ValidHashAddress address) :
    Fin (len p) → ChainRun p := fun i =>
  chainWithCalls family (sig i) (digits M i).val (w - 1 - (digits M i).val) publicSeed
    (address.setChainAddress (chainIndexAddressWord i)) (by
      simpa only [ValidHashAddress, Address.setChainAddress] using haddress) (by
      unfold ValidChainRange
      have hi := (digits M i).isLt
      omega)

/-- The per-chain instrumented ledger has exactly the message-selected suffix length. -/
@[simp] theorem chainEndRuns_calls (family : HashFamily) {p : SecurityBytes} (sig : Signature p)
    (M : Message p) (publicSeed : NBytes p) (address : Address)
    (haddress : ValidHashAddress address) (i : Fin (len p)) :
    (chainEndRuns family sig M publicSeed address haddress i).calls =
      chainCalls (w - 1 - (digits M i).val) :=
  chainWithCalls_calls family (sig i) (digits M i).val (w - 1 - (digits M i).val)
    publicSeed (address.setChainAddress (chainIndexAddressWord i)) (by
      simpa only [ValidHashAddress, Address.setChainAddress] using haddress) (by
      unfold ValidChainRange
      have hi := (digits M i).isLt
      omega)

/-- Algorithm 8 lines 8--11: the output projection of every instrumented chain suffix. -/
def chainEndNodes (family : HashFamily) {p : SecurityBytes} (sig : Signature p) (M : Message p)
    (publicSeed : NBytes p) (address : Address) (haddress : ValidHashAddress address) :
    Fin (len p) → NBytes p := fun i =>
  (chainEndRuns family sig M publicSeed address haddress i).output

/-- Pointwise Algorithm 8 equation: chain end `i` starts at digit `msg[i]` and performs exactly
`w - 1 - msg[i]` remaining steps under chain address `i`. -/
theorem chainEndNodes_eq_chain (family : HashFamily) {p : SecurityBytes} (sig : Signature p)
    (M : Message p) (publicSeed : NBytes p) (address : Address)
    (haddress : ValidHashAddress address) (i : Fin (len p)) :
    chainEndNodes family sig M publicSeed address haddress i =
      chain family (sig i) (digits M i).val (w - 1 - (digits M i).val) publicSeed
        (address.setChainAddress ⟨i, i.isLt.trans_le ((len_le_67 p).trans (by decide))⟩) (by
          simpa only [ValidHashAddress, Address.setChainAddress] using haddress) (by
          unfold ValidChainRange
          have hi := (digits M i).isLt
          omega) :=
  chainWithCalls_output family (sig i) (digits M i).val (w - 1 - (digits M i).val)
    publicSeed (address.setChainAddress
      ⟨i, i.isLt.trans_le ((len_le_67 p).trans (by decide))⟩) (by
        simpa only [ValidHashAddress, Address.setChainAddress] using haddress) (by
        unfold ValidChainRange
        have hi := (digits M i).isLt
        omega)

/-- The `len` chain ends concatenated as the exact `len * n` byte input to `T_len`. -/
def publicKeyInput (family : HashFamily) {p : SecurityBytes} (sig : Signature p) (M : Message p)
    (publicSeed : NBytes p) (address : Address) (haddress : ValidHashAddress address) :
    LBlocksBytes p (len p) :=
  blocksEquiv.symm (chainEndNodes family sig M publicSeed address haddress)

/-- Canonical block order: byte `j` of compression block `i` is byte `j` of chain end `i`. -/
@[simp] theorem publicKeyInput_apply (family : HashFamily) {p : SecurityBytes}
    (sig : Signature p) (M : Message p) (publicSeed : NBytes p) (address : Address)
    (haddress : ValidHashAddress address) (i : Fin (len p)) (j : Fin p.count) :
    publicKeyInput family sig M publicSeed address haddress (finProdFinEquiv (i, j)) =
      chainEndNodes family sig M publicSeed address haddress i j := by
  simp only [publicKeyInput, blocksEquiv_symm_apply, Equiv.symm_apply_apply]

/-- The complete compression input is the canonical concatenation of the directly specified
digit-selected chain suffixes. -/
theorem publicKeyInput_eq_direct (family : HashFamily) {p : SecurityBytes} (sig : Signature p)
    (M : Message p) (publicSeed : NBytes p) (address : Address)
    (haddress : ValidHashAddress address) :
    publicKeyInput family sig M publicSeed address haddress =
      blocksEquiv.symm fun i =>
        chain family (sig i) (digits M i).val (w - 1 - (digits M i).val) publicSeed
          (address.setChainAddress
            ⟨i, i.isLt.trans_le ((len_le_67 p).trans (by decide))⟩) (by
              simpa only [ValidHashAddress, Address.setChainAddress] using haddress) (by
              unfold ValidChainRange
              have hi := (digits M i).isLt
              omega) := by
  unfold publicKeyInput
  apply congrArg blocksEquiv.symm
  funext i
  exact chainEndNodes_eq_chain family sig M publicSeed address haddress i

/-- The result and source-call ledger of an instrumented Algorithm 8 invocation. -/
structure PublicKeyFromSigRun (p : SecurityBytes) where
  /-- The reconstructed `n`-byte WOTS+ public key. -/
  output : NBytes p
  /-- The calls, writes and byte shapes made by the executable construction. -/
  calls : PublicKeyFromSigCalls

/-- Instrumented FIPS 205 Algorithm 8. The variable call counts are summed from the instrumented
Algorithm 5 runs used to construct the actual compression input. -/
def wotsPkFromSigWithCalls (family : HashFamily) {p : SecurityBytes} (sig : Signature p)
    (M : Message p) (publicSeed : NBytes p) (address : Address)
    (haddress : ValidHashAddress address) : PublicKeyFromSigRun p :=
  { output := tL family (len p) publicSeed (publicKeyAddress address)
      (publicKeyInput family sig M publicSeed address haddress)
    calls :=
      { chainTraversals := len p
        chainAddressWrites := len p
        fCalls := ∑ i, (chainEndRuns family sig M publicSeed address haddress i).calls.fCalls
        hashAddressWrites :=
          ∑ i, (chainEndRuns family sig M publicSeed address haddress i).calls.hashAddressWrites
        typeAndClearCalls := 1
        keyPairAddressWrites := 1
        tLCalls := 1
        compressionBlocks := len p
        compressionInputBytes := len p * p.count
        outputBytes := p.count } }

/-- The instrumented Algorithm 8 ledger agrees with its closed source-count formula. -/
@[simp] theorem wotsPkFromSigWithCalls_calls (family : HashFamily) {p : SecurityBytes}
    (sig : Signature p) (M : Message p) (publicSeed : NBytes p) (address : Address)
    (haddress : ValidHashAddress address) :
    (wotsPkFromSigWithCalls family sig M publicSeed address haddress).calls =
      publicKeyFromSigCalls M := by
  ext <;>
    simp only [wotsPkFromSigWithCalls, publicKeyFromSigCalls, totalChainSteps,
      chainEndRuns_calls, chainCalls_fCalls, chainCalls_hashAddressWrites]

/-- FIPS 205 Algorithm 8 (`wots_pkFromSig`) as the output projection of the instrumented run. -/
def wotsPkFromSig (family : HashFamily) {p : SecurityBytes} (sig : Signature p) (M : Message p)
    (publicSeed : NBytes p) (address : Address) (haddress : ValidHashAddress address) : NBytes p :=
  (wotsPkFromSigWithCalls family sig M publicSeed address haddress).output

/-- `wotsPkFromSig` is the output projection of the instrumented Algorithm 8 evaluator. -/
theorem wotsPkFromSigWithCalls_output (family : HashFamily) {p : SecurityBytes}
    (sig : Signature p) (M : Message p) (publicSeed : NBytes p) (address : Address)
    (haddress : ValidHashAddress address) :
    (wotsPkFromSigWithCalls family sig M publicSeed address haddress).output =
      wotsPkFromSig family sig M publicSeed address haddress :=
  (rfl)

/-- Algorithm 8 is visibly one `T_len` call over the canonical array of chain ends. -/
theorem wotsPkFromSig_eq (family : HashFamily) {p : SecurityBytes} (sig : Signature p)
    (M : Message p) (publicSeed : NBytes p) (address : Address)
    (haddress : ValidHashAddress address) :
    wotsPkFromSig family sig M publicSeed address haddress =
      tL family (len p) publicSeed (publicKeyAddress address)
        (publicKeyInput family sig M publicSeed address haddress) :=
  (rfl)

/-- Algorithm 8 expanded directly into its digit-selected chains, canonical block concatenation,
address transition and final `T_len` call. This equation is the downstream unfolding interface;
the evaluators themselves remain opaque. -/
theorem wotsPkFromSig_eq_direct (family : HashFamily) {p : SecurityBytes} (sig : Signature p)
    (M : Message p) (publicSeed : NBytes p) (address : Address)
    (haddress : ValidHashAddress address) :
    wotsPkFromSig family sig M publicSeed address haddress =
      tL family (len p) publicSeed (publicKeyAddress address)
        (blocksEquiv.symm fun i =>
          chain family (sig i) (digits M i).val (w - 1 - (digits M i).val) publicSeed
            (address.setChainAddress
              ⟨i, i.isLt.trans_le ((len_le_67 p).trans (by decide))⟩) (by
                simpa only [ValidHashAddress, Address.setChainAddress] using haddress) (by
                unfold ValidChainRange
                have hi := (digits M i).isLt
                omega)) :=
  by rw [wotsPkFromSig_eq, publicKeyInput_eq_direct]

@[simp] theorem publicKeyFromSigCalls_fCalls {p : SecurityBytes} (M : Message p) :
    (publicKeyFromSigCalls M).fCalls = totalChainSteps M :=
  rfl

@[simp] theorem publicKeyFromSigCalls_hashAddressWrites {p : SecurityBytes} (M : Message p) :
    (publicKeyFromSigCalls M).hashAddressWrites = totalChainSteps M :=
  rfl

end Cslib.Crypto.SLHDSA.WOTS
