/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.SLHDSA.WOTS.Chain

/-!
# FIPS 205 WOTS+ public-key reconstruction

This module implements FIPS 205, Section 5.3, Algorithm 8. It reconstructs the WOTS+ public-key
value associated with a message and signature: the common message/checksum digits select the
start of each remaining hash-chain suffix, the chain end nodes are concatenated in canonical
order, and one `T_len` call (`tL`) compresses them under a `WOTS_PK` address.

Algorithm 8 is called with an address of type `WOTS_HASH`. As for the addressed calls,
`wotsPkFromSig` accepts every `Address`, and setting the address type is the caller's
responsibility. The transition to `WOTS_PK` clears all type-dependent words before restoring only
the key-pair word, exactly as in Algorithm 8.

This module is definitions only: its theorems are the equations that specify its definitions. It
does not implement WOTS+ key generation or signing, and it does not prove that a generated
signature reconstructs its generated public key, which is the first real property of Algorithm 8
and needs Algorithms 6 and 7 (#4987). It establishes no one-time, classical or quantum security
and supplies no hash-call counts or machine, program-size, gate, qubit or query costs.

## Main definitions

* `Cslib.Crypto.SLHDSA.WOTS.Signature`: exactly `len` consecutive `n`-byte blocks.
* `Cslib.Crypto.SLHDSA.WOTS.publicKeyAddress`: the `WOTS_PK` address of Algorithm 8.
* `Cslib.Crypto.SLHDSA.WOTS.chainEndNodes`: the Algorithm 8 chain-end array.
* `Cslib.Crypto.SLHDSA.WOTS.publicKeyInput`: the canonical `len * n` byte compression input.
* `Cslib.Crypto.SLHDSA.WOTS.wotsPkFromSig`: FIPS 205 Algorithm 8.

## References

* [NIST, *Stateless Hash-Based Digital Signature Standard*, Sections 5 and 5.3,
  Algorithms 5 and 8][NISTFIPS205]
-/

public section

namespace Cslib.Crypto.SLHDSA.WOTS

open Cslib.BitString Cslib.Crypto Cslib.Crypto.SLHDSA

/-- A WOTS+ signature is exactly `len` consecutive `n`-byte strings. -/
abbrev Signature (p : SecurityBytes) := Fin (len p) → NBytes p

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

/-- Algorithm 8 lines 8--11: finish every chain from the signature-selected node. -/
def chainEndNodes (family : HashFamily) {p : SecurityBytes} (sig : Signature p) (M : Message p)
    (publicSeed : NBytes p) (address : Address) : Fin (len p) → NBytes p := fun i =>
  chain family (sig i) (digits M i).val (w - 1 - (digits M i).val) publicSeed
    (address.setChainAddress ⟨i, i.isLt.trans_le ((len_le_67 p).trans (by decide))⟩) (by
      have hi := (digits M i).isLt
      omega)

/-- Pointwise Algorithm 8 equation: chain end `i` starts at digit `msg[i]` and runs the
`w - 1 - msg[i]` remaining steps under chain address `i`. -/
theorem chainEndNodes_eq_chain (family : HashFamily) {p : SecurityBytes} (sig : Signature p)
    (M : Message p) (publicSeed : NBytes p) (address : Address) (i : Fin (len p)) :
    chainEndNodes family sig M publicSeed address i =
      chain family (sig i) (digits M i).val (w - 1 - (digits M i).val) publicSeed
        (address.setChainAddress ⟨i, i.isLt.trans_le ((len_le_67 p).trans (by decide))⟩) (by
          have hi := (digits M i).isLt
          omega) :=
  (rfl)

/-- The `len` chain ends concatenated as the exact `len * n` byte input to `T_len`. -/
def publicKeyInput (family : HashFamily) {p : SecurityBytes} (sig : Signature p) (M : Message p)
    (publicSeed : NBytes p) (address : Address) : LBlocksBytes p (len p) :=
  blocksEquiv.symm (chainEndNodes family sig M publicSeed address)

/-- Canonical block order: byte `j` of compression block `i` is byte `j` of chain end `i`. -/
@[simp] theorem publicKeyInput_apply (family : HashFamily) {p : SecurityBytes}
    (sig : Signature p) (M : Message p) (publicSeed : NBytes p) (address : Address)
    (i : Fin (len p)) (j : Fin p.count) :
    publicKeyInput family sig M publicSeed address (finProdFinEquiv (i, j)) =
      chainEndNodes family sig M publicSeed address i j := by
  simp only [publicKeyInput, blocksEquiv_symm_apply, Equiv.symm_apply_apply]

/-- FIPS 205 Algorithm 8 (`wots_pkFromSig`): one `T_len` call over the chain ends, under the
`WOTS_PK` address. -/
def wotsPkFromSig (family : HashFamily) {p : SecurityBytes} (sig : Signature p) (M : Message p)
    (publicSeed : NBytes p) (address : Address) : NBytes p :=
  tL family (len p) publicSeed (publicKeyAddress address)
    (publicKeyInput family sig M publicSeed address)

/-- Algorithm 8 is one `T_len` call over the canonical array of chain ends. -/
theorem wotsPkFromSig_eq (family : HashFamily) {p : SecurityBytes} (sig : Signature p)
    (M : Message p) (publicSeed : NBytes p) (address : Address) :
    wotsPkFromSig family sig M publicSeed address =
      tL family (len p) publicSeed (publicKeyAddress address)
        (publicKeyInput family sig M publicSeed address) :=
  (rfl)

end Cslib.Crypto.SLHDSA.WOTS
