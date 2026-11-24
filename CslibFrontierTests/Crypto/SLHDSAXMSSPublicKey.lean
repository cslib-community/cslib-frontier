/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Crypto.Primitives.SLHDSA.XMSS.PublicKeyFromSignature

set_option linter.privateModule false

/-!
# Checked clients for FIPS 205 XMSS public-key reconstruction

These checks use only the public interface of the Algorithm 11 module. They fix leaf index
`5 = 0b101` in a tree of height `h' = 3`, whose three loop iterations take the odd, the even and
the odd branch, and an input address whose type-specific words are all nonzero. The last check
unrolls Algorithm 11 completely for that leaf: it names the address and the block order of every
`H` call and the address of the WOTS+ call. A definition with the two branches exchanged, another
tree height or tree index, or a missing `setTypeAndClear` could not pass it.

The checks do not evaluate a hash function, and they say nothing about generated signatures,
verification or security.
-/

public section

namespace SLHDSAXMSSPublicKeyTests

open Cslib.Crypto Cslib.Crypto.SLHDSA Cslib.Crypto.SLHDSA.XMSS

/-! ### The address after each iteration -/

/-- An input address in layer 3 whose type and three type-specific words Algorithm 11 must
overwrite. -/
private def inputAddress : Address :=
  Address.forsTree 0x0102030405060708 7 11 13 |>.setLayerAddress 3

private def indexFive : LeafIndex .bytes16 .fast := ⟨5, by decide⟩

/-- The `TREE` address (FIPS 205, Figure 5) in the layer and tree of `inputAddress`. -/
private def treeAddress (height index : AddressWord) : Address :=
  Address.tree 3 0x0102030405060708 height index

/-- Leaf index `5` climbs through tree indices `5`, `2`, `1` and `0`. -/
example : authenticationAddress inputAddress indexFive 0 (by decide) = treeAddress 0 5 :=
  authenticationAddress_eq_tree inputAddress indexFive 0 (by decide)
example : authenticationAddress inputAddress indexFive 1 (by decide) = treeAddress 1 2 :=
  authenticationAddress_eq_tree inputAddress indexFive 1 (by decide)
example : authenticationAddress inputAddress indexFive 2 (by decide) = treeAddress 2 1 :=
  authenticationAddress_eq_tree inputAddress indexFive 2 (by decide)
example : authenticationAddress inputAddress indexFive 3 (by decide) = treeAddress 3 0 :=
  authenticationAddress_eq_tree inputAddress indexFive 3 (by decide)

/-! ### Algorithm 11 unrolled -/

/-- Algorithm 11 for leaf `5` and `h' = 3`. The WOTS+ public key is computed under the `WOTS_HASH`
address with key pair `5`. Iteration 0 (`5` is odd) hashes `AUTH[0] ∥ node`, iteration 1 (`2` is
even) hashes `node ∥ AUTH[1]`, and iteration 2 (`1` is odd) hashes `AUTH[2] ∥ node`, under the
`TREE` addresses with (height, index) equal to `(1, 2)`, `(2, 1)` and `(3, 0)`. -/
example (family : HashFamily) (sig : Signature .bytes16 .fast) (M : WOTS.Message .bytes16)
    (publicSeed : NBytes .bytes16) :
    xmssPkFromSig family indexFive sig M publicSeed inputAddress =
      h family publicSeed (treeAddress 3 0)
        (FixedBytes.pairBlocks (sig.authentication ⟨2, by decide⟩)
          (h family publicSeed (treeAddress 2 1)
            (FixedBytes.pairBlocks
              (h family publicSeed (treeAddress 1 2)
                (FixedBytes.pairBlocks (sig.authentication ⟨0, by decide⟩)
                  (WOTS.wotsPkFromSig family sig.wots M publicSeed
                    (Address.wotsHash 3 0x0102030405060708 5 0 0))))
              (sig.authentication ⟨1, by decide⟩)))) := by
  rw [xmssPkFromSig_eq]
  change authenticationNode family indexFive sig.authentication publicSeed inputAddress _ 3
    (by decide) = _
  rw [authenticationNode_succ, authenticationNode_succ, authenticationNode_succ,
    authenticationNode_zero, authenticationAddress_eq_tree, authenticationAddress_eq_tree,
    authenticationAddress_eq_tree]
  rfl

end SLHDSAXMSSPublicKeyTests
