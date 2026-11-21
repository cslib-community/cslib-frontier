/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Crypto.Primitives.SLHDSA.WOTS.PublicKeyFromSignature

set_option linter.privateModule false

/-!
# Checked clients for FIPS 205 WOTS+ chaining and public-key reconstruction

These clients cover Algorithm 5's edge step counts and composition, Algorithm 8's address
transition and canonical block order, all six concrete hash-family/security-byte branches, and the
exact source call ledger. They do not claim generated-signature correctness or security.
-/

public section

namespace SLHDSAWOTSPublicKeyTests

open Cslib.BitString Cslib.Crypto Cslib.Crypto.SLHDSA Cslib.Crypto.SLHDSA.WOTS

private def zeroBytes (p : SecurityBytes) : NBytes p := fun _ => 0
private def zeroMessage (p : SecurityBytes) : Message p := fun _ => 0
private def maxMessage (p : SecurityBytes) : Message p := fun _ => 255
private def zeroSignature (p : SecurityBytes) : Signature p := fun _ _ => 0

private def hashAddress : Address :=
  Address.wotsHash 3 0x0102030405060708 0x11223344 0 0

private theorem hashAddress_valid : ValidHashAddress hashAddress := by decide

/-! ### Algorithm 5 -/

example (family : HashFamily) (p : SecurityBytes) :
    chain family (zeroBytes p) 7 0 (zeroBytes p) hashAddress hashAddress_valid (by decide) =
      zeroBytes p :=
  chain_zero family (zeroBytes p) 7 (zeroBytes p) hashAddress hashAddress_valid (by decide)

example (family : HashFamily) (p : SecurityBytes) :
    chain family (zeroBytes p) 4 1 (zeroBytes p) hashAddress hashAddress_valid (by decide) =
      f family (zeroBytes p) (hashAddress.setHashAddress 4) (zeroBytes p) :=
  by
    convert chain_succ family (zeroBytes p) 4 0 (zeroBytes p) hashAddress hashAddress_valid
      (by decide) using 1
    congr 3
    simp only [chain_zero]

example (family : HashFamily) (p : SecurityBytes) :
    chain family
        (chain family (zeroBytes p) 0 6 (zeroBytes p) hashAddress hashAddress_valid (by decide))
        6 9 (zeroBytes p) hashAddress hashAddress_valid (by decide) =
      chain family (zeroBytes p) 0 15 (zeroBytes p) hashAddress hashAddress_valid (by decide) :=
  chain_add family (zeroBytes p) 0 6 9 (zeroBytes p) hashAddress hashAddress_valid (by decide)

example : chainCalls 0 = ⟨0, 0⟩ := rfl
example : chainCalls 1 = ⟨1, 1⟩ := rfl
example : chainCalls 15 = ⟨15, 15⟩ := rfl

example (family : HashFamily) (p : SecurityBytes) :
    (chainWithCalls family (zeroBytes p) 0 15 (zeroBytes p) hashAddress hashAddress_valid
      (by decide)).output =
      chain family (zeroBytes p) 0 15 (zeroBytes p) hashAddress hashAddress_valid (by decide) :=
  chainWithCalls_output family (zeroBytes p) 0 15 (zeroBytes p) hashAddress hashAddress_valid
    (by decide)

example (family : HashFamily) (p : SecurityBytes) :
    (chainWithCalls family (zeroBytes p) 0 15 (zeroBytes p) hashAddress hashAddress_valid
      (by decide)).calls = chainCalls 15 :=
  chainWithCalls_calls family (zeroBytes p) 0 15 (zeroBytes p) hashAddress hashAddress_valid
    (by decide)

/-! ### Algorithm 8 address and layout -/

example : (publicKeyAddress hashAddress).addressType = .wotsPK := rfl
example : (publicKeyAddress hashAddress).word5 = hashAddress.word5 := rfl
example : (publicKeyAddress hashAddress).word6 = 0 ∧
    (publicKeyAddress hashAddress).word7 = 0 :=
  ⟨rfl, rfl⟩

example (family : HashFamily) (p : SecurityBytes) (i : Fin (len p)) (j : Fin p.count) :
    publicKeyInput family (zeroSignature p) (zeroMessage p) (zeroBytes p) hashAddress
        hashAddress_valid (finProdFinEquiv (i, j)) =
      chainEndNodes family (zeroSignature p) (zeroMessage p) (zeroBytes p) hashAddress
        hashAddress_valid i j :=
  publicKeyInput_apply family (zeroSignature p) (zeroMessage p) (zeroBytes p) hashAddress
    hashAddress_valid i j

-- The actual Algorithm 8 compression input lies in the standard's source domain independently of
-- the total `tL` evaluator.
example (family : HashFamily) {p : SecurityBytes} (sig : Signature p) (M : Message p)
    (publicSeed : NBytes p) (address : Address) (haddress : ValidHashAddress address) :
    ValidTInput family publicSeed (publicKeyAddress address)
      (publicKeyInput family sig M publicSeed address haddress) :=
  validTInput_of_blocks_le_67 family publicSeed (publicKeyAddress address)
    (publicKeyInput family sig M publicSeed address haddress) (len_le_67 p)

private def recompute (family : HashFamily) (p : SecurityBytes) : NBytes p :=
  tL family (len p) (zeroBytes p) (publicKeyAddress hashAddress)
    (blocksEquiv.symm fun i =>
      chain family (zeroSignature p i) (digits (zeroMessage p) i).val
        (w - 1 - (digits (zeroMessage p) i).val) (zeroBytes p)
        (hashAddress.setChainAddress ⟨i, i.isLt.trans_le ((len_le_67 p).trans (by decide))⟩)
        (by simpa only [ValidHashAddress, Address.setChainAddress] using hashAddress_valid) (by
          unfold ValidChainRange
          have hi := (digits (zeroMessage p) i).isLt
          omega))

example (family : HashFamily) (p : SecurityBytes) :
    wotsPkFromSig family (zeroSignature p) (zeroMessage p) (zeroBytes p) hashAddress
        hashAddress_valid = recompute family p :=
  wotsPkFromSig_eq_direct family (zeroSignature p) (zeroMessage p) (zeroBytes p) hashAddress
    hashAddress_valid

example (family : HashFamily) (p : SecurityBytes) :
    (wotsPkFromSigWithCalls family (zeroSignature p) (zeroMessage p) (zeroBytes p) hashAddress
      hashAddress_valid).output =
      wotsPkFromSig family (zeroSignature p) (zeroMessage p) (zeroBytes p) hashAddress
        hashAddress_valid :=
  wotsPkFromSigWithCalls_output family (zeroSignature p) (zeroMessage p) (zeroBytes p) hashAddress
    hashAddress_valid

example (family : HashFamily) (p : SecurityBytes) :
    (wotsPkFromSigWithCalls family (zeroSignature p) (zeroMessage p) (zeroBytes p) hashAddress
      hashAddress_valid).calls = publicKeyFromSigCalls (zeroMessage p) :=
  wotsPkFromSigWithCalls_calls family (zeroSignature p) (zeroMessage p) (zeroBytes p) hashAddress
    hashAddress_valid

-- Ordinary-import terms cover every concrete hash-family/security-byte branch without turning
-- these comparatively large executable specifications into a machine-cost or timing claim.
example : NBytes .bytes16 :=
  wotsPkFromSig .shake (zeroSignature .bytes16) (zeroMessage .bytes16) (zeroBytes .bytes16)
    hashAddress hashAddress_valid
example : NBytes .bytes24 :=
  wotsPkFromSig .shake (zeroSignature .bytes24) (zeroMessage .bytes24) (zeroBytes .bytes24)
    hashAddress hashAddress_valid
example : NBytes .bytes32 :=
  wotsPkFromSig .shake (zeroSignature .bytes32) (zeroMessage .bytes32) (zeroBytes .bytes32)
    hashAddress hashAddress_valid
example : NBytes .bytes16 :=
  wotsPkFromSig .sha2 (zeroSignature .bytes16) (zeroMessage .bytes16) (zeroBytes .bytes16)
    hashAddress hashAddress_valid
example : NBytes .bytes24 :=
  wotsPkFromSig .sha2 (zeroSignature .bytes24) (zeroMessage .bytes24) (zeroBytes .bytes24)
    hashAddress hashAddress_valid
example : NBytes .bytes32 :=
  wotsPkFromSig .sha2 (zeroSignature .bytes32) (zeroMessage .bytes32) (zeroBytes .bytes32)
    hashAddress hashAddress_valid

/-! ### Exact source ledger -/

-- Sixteen zero bytes produce 510 remaining chain steps; sixteen 0xff bytes produce 45.
example : totalChainSteps (zeroMessage .bytes16) = 510 := by decide +kernel
example : totalChainSteps (maxMessage .bytes16) = 45 := by decide +kernel
example : (publicKeyFromSigCalls (zeroMessage .bytes16)).chainAddressWrites = 35 := rfl
example : (publicKeyFromSigCalls (zeroMessage .bytes16)).fCalls = 510 := by decide +kernel
example : (publicKeyFromSigCalls (zeroMessage .bytes16)).hashAddressWrites = 510 := by
  decide +kernel
example : (publicKeyFromSigCalls (zeroMessage .bytes32)).compressionBlocks = 67 := rfl
example : (publicKeyFromSigCalls (zeroMessage .bytes32)).compressionInputBytes = 2144 := rfl
example : (publicKeyFromSigCalls (zeroMessage .bytes32)).outputBytes = 32 := rfl
example (p : SecurityBytes) : totalChainSteps (zeroMessage p) ≤ len p * (w - 1) :=
  totalChainSteps_le (zeroMessage p)

end SLHDSAWOTSPublicKeyTests
