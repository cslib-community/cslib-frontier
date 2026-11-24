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

These clients use only the public equations. They cover Algorithm 5's zero-step and one-step
cases, the largest start index and step total that the range condition admits, and composition;
and Algorithm 8's address transition, canonical block order and expansion into digit-selected
chains. They evaluate no hash and do not claim generated-signature correctness or security.
-/

public section

namespace SLHDSAWOTSPublicKeyTests

open Cslib.BitString Cslib.Crypto Cslib.Crypto.SLHDSA Cslib.Crypto.SLHDSA.WOTS

private def zeroBytes (p : SecurityBytes) : NBytes p := fun _ => 0
private def zeroMessage (p : SecurityBytes) : Message p := fun _ => 0
private def zeroSignature (p : SecurityBytes) : Signature p := fun _ _ => 0

private def hashAddress : Address :=
  Address.wotsHash 3 0x0102030405060708 0x11223344 0 0

/-! ### Algorithm 5 -/

example (family : HashFamily) (p : SecurityBytes) :
    chain family (zeroBytes p) 7 0 (zeroBytes p) hashAddress (by decide) = zeroBytes p :=
  chain_zero family (zeroBytes p) 7 (zeroBytes p) hashAddress (by decide)

-- A digit `w - 1` starts a zero-step chain at index 15, the largest start with `i + s < w`.
example (family : HashFamily) (p : SecurityBytes) :
    chain family (zeroBytes p) 15 0 (zeroBytes p) hashAddress (by decide) = zeroBytes p :=
  chain_zero family (zeroBytes p) 15 (zeroBytes p) hashAddress (by decide)

example (family : HashFamily) (p : SecurityBytes) :
    chain family (zeroBytes p) 4 1 (zeroBytes p) hashAddress (by decide) =
      f family (zeroBytes p) (hashAddress.setHashAddress 4) (zeroBytes p) := by
  rw [chain_succ, chain_zero]
  rfl

-- Fifteen steps from index 0 is the largest total with `i + s < w`.
example (family : HashFamily) (p : SecurityBytes) :
    chain family
        (chain family (zeroBytes p) 0 6 (zeroBytes p) hashAddress (by decide))
        6 9 (zeroBytes p) hashAddress (by decide) =
      chain family (zeroBytes p) 0 15 (zeroBytes p) hashAddress (by decide) :=
  chain_add family (zeroBytes p) 0 6 9 (zeroBytes p) hashAddress (by decide)

/-! ### Algorithm 8 address and layout -/

example : (publicKeyAddress hashAddress).addressType = .wotsPK := rfl
example : (publicKeyAddress hashAddress).word5 = hashAddress.word5 := rfl
example : (publicKeyAddress hashAddress).word6 = 0 ∧
    (publicKeyAddress hashAddress).word7 = 0 :=
  ⟨rfl, rfl⟩

example (family : HashFamily) (p : SecurityBytes) (i : Fin (len p)) (j : Fin p.count) :
    publicKeyInput family (zeroSignature p) (zeroMessage p) (zeroBytes p) hashAddress
        (finProdFinEquiv (i, j)) =
      chainEndNodes family (zeroSignature p) (zeroMessage p) (zeroBytes p) hashAddress i j :=
  publicKeyInput_apply family (zeroSignature p) (zeroMessage p) (zeroBytes p) hashAddress i j

-- The actual Algorithm 8 compression input lies in the standard's source domain independently of
-- the total `tL` evaluator.
example (family : HashFamily) {p : SecurityBytes} (sig : Signature p) (M : Message p)
    (publicSeed : NBytes p) (address : Address) :
    ValidTInput family publicSeed (publicKeyAddress address)
      (publicKeyInput family sig M publicSeed address) :=
  validTInput_of_blocks_le_67 family publicSeed (publicKeyAddress address)
    (publicKeyInput family sig M publicSeed address) (len_le_67 p)

private def recompute (family : HashFamily) (p : SecurityBytes) : NBytes p :=
  tL family (len p) (zeroBytes p) (publicKeyAddress hashAddress)
    (blocksEquiv.symm fun i =>
      chain family (zeroSignature p i) (digits (zeroMessage p) i).val
        (w - 1 - (digits (zeroMessage p) i).val) (zeroBytes p)
        (hashAddress.setChainAddress ⟨i, i.isLt.trans_le ((len_le_67 p).trans (by decide))⟩) (by
          have hi := (digits (zeroMessage p) i).isLt
          omega))

-- The public equations of `wotsPkFromSig`, `publicKeyInput` and `chainEndNodes` expand
-- Algorithm 8 into its digit-selected chains, canonical block concatenation, address transition
-- and final `T_len` call.
example (family : HashFamily) (p : SecurityBytes) :
    wotsPkFromSig family (zeroSignature p) (zeroMessage p) (zeroBytes p) hashAddress =
      recompute family p := by
  rw [wotsPkFromSig_eq, recompute]
  congr 1
  rw [Equiv.eq_symm_apply]
  funext i j
  rw [blocksEquiv_apply, block_apply, publicKeyInput_apply, chainEndNodes_eq_chain]

end SLHDSAWOTSPublicKeyTests
