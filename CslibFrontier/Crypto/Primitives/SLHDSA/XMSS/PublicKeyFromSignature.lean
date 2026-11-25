/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.SLHDSA.WOTS.PublicKeyFromSignature

/-!
# FIPS 205 XMSS public-key reconstruction

This module implements FIPS 205, Section 6.3, Algorithm 11 (`xmss_pkFromSig`). Lines 1--5
reconstruct the WOTS+ public key of leaf `idx` with Algorithm 8. Lines 6--18 combine that leaf with
the authentication path: iteration `k` writes tree height `k + 1`, halves the tree index, and
calls the addressed function `H` on the current node and `AUTH[k]`, with the current node first
exactly when `⌊idx / 2^k⌋` is even.

The source's loop over a mutable address and a mutable node is written as two functions of the
number of completed iterations: `authenticationAddress` is the address and `authenticationNode` is
`node[0]`. The address does not depend on the node, so the two are not threaded as a pair.
`authenticationAddress` performs the source's index updates literally, `i / 2` on the even branch
and `(i - 1) / 2` on the odd branch, and `authenticationAddress_eq_tree` proves that after `k`
iterations the result is the `TREE` address with tree height `k` and tree index `⌊idx / 2^k⌋`. One
step is moved: line 6 is applied to the input address instead of the address left by lines 1--5.
The result is the same, because `setTypeAndClear` overwrites the address type and the three
type-specific words, the only words that those lines can change.

Algorithm 11 is called with the layer and tree address of the XMSS tree. As for the addressed
calls it is built from, `xmssPkFromSig` accepts every `Address`.

This module does not prove that a signature produced by FIPS 205 Algorithms 9 and 10 reconstructs
the root of its tree. That is the first real property of Algorithm 11; it needs those two
algorithms, which are not formalized (#4987). The module does not define a generic Merkle tree,
perform SLH-DSA verification, or establish classical or quantum security, and it supplies no
hash-call counts or machine, program-size, gate, qubit or query costs.

## Main definitions

* `Cslib.Crypto.SLHDSA.XMSS.Signature`: a WOTS+ signature and an `h'`-node authentication path.
* `Cslib.Crypto.SLHDSA.XMSS.authenticationAddress`: the Algorithm 11 address after a number of
  loop iterations.
* `Cslib.Crypto.SLHDSA.XMSS.authenticationNode`: the Algorithm 11 node after a number of loop
  iterations.
* `Cslib.Crypto.SLHDSA.XMSS.xmssPkFromSig`: FIPS 205 Algorithm 11.

## Main results

* `Cslib.Crypto.SLHDSA.XMSS.authenticationAddress_eq_tree`: after `k` iterations the address is
  the `TREE` address of the input layer and tree with tree height `k` and tree index
  `⌊idx / 2^k⌋`.

## References

* [NIST, *Stateless Hash-Based Digital Signature Standard*, Table 2, Section 6 and
  Section 6.3, Algorithm 11][NISTFIPS205]
-/

public section

namespace Cslib.Crypto.SLHDSA.XMSS

open Cslib.Crypto Cslib.Crypto.SLHDSA

/-- An XMSS signature (FIPS 205, Section 6, Figure 11): a WOTS+ signature followed by `h'`
authentication nodes, the two parts that Algorithm 11 reads in lines 3--4. -/
structure Signature (p : SecurityBytes) (shape : ParameterShape) where
  /-- The WOTS+ signature, the first `len` `n`-byte blocks. -/
  wots : WOTS.Signature p
  /-- The authentication path, the following `h'` `n`-byte blocks, from the leaf level upward. -/
  authentication : Fin (ParameterShape.xmssHeight p shape) → NBytes p

/-- The index of one of the `2^h'` leaves of an XMSS tree. -/
abbrev LeafIndex (p : SecurityBytes) (shape : ParameterShape) :=
  Fin (2 ^ ParameterShape.xmssHeight p shape)

/-- One iteration of the Algorithm 11 address updates: `setTreeHeight` (line 9), then
`setTreeIndex` with the current index `i` replaced by `i / 2` when `even` holds (line 11) and by
`(i - 1) / 2` otherwise (line 14). -/
private def stepAddress (current : Address) (height : AddressWord) (even : Prop)
    [Decidable even] : Address :=
  (current.setTreeHeight height).setTreeIndex
    (if even then
      ⟨current.word7.val / 2, Nat.lt_of_le_of_lt (Nat.div_le_self _ 2) current.word7.isLt⟩
    else
      ⟨(current.word7.val - 1) / 2,
        Nat.lt_of_le_of_lt ((Nat.div_le_self _ 2).trans (Nat.sub_le _ 1)) current.word7.isLt⟩)

/-- The address of FIPS 205 Algorithm 11 after `levels` iterations of its loop.

Lines 6--7 give the address before the loop: `setTypeAndClear(TREE)`, then `setTreeIndex(idx)`.
Iteration `k` performs `setTreeHeight(k + 1)` (line 9) and then `setTreeIndex`, replacing the
current tree index `i` by `i / 2` when `⌊idx / 2^k⌋` is even (line 11) and by `(i - 1) / 2`
otherwise (line 14). `authenticationAddress_eq_tree` gives the result as a `TREE` address.

Line 6 is applied to the input address instead of the address left by lines 1--5. The two agree
after line 6, because `setTypeAndClear` overwrites the address type and the three type-specific
words, the only words that lines 1--5 can change. -/
def authenticationAddress {p : SecurityBytes} {shape : ParameterShape} (address : Address)
    (idx : LeafIndex p shape) :
    (levels : ℕ) → levels ≤ ParameterShape.xmssHeight p shape → Address
  | 0, _ =>
      (address.setTypeAndClear .tree).setTreeIndex
        (idx.castLE (ParameterShape.two_pow_xmssHeight_le p shape))
  | levels + 1, hlevels =>
      stepAddress (authenticationAddress address idx levels (Nat.le_of_succ_le hlevels))
        ⟨levels + 1, hlevels.trans_lt
          (Nat.lt_two_pow_self.trans_le (ParameterShape.two_pow_xmssHeight_le p shape))⟩
        (idx.val / 2 ^ levels % 2 = 0)

/-- After `levels` iterations the Algorithm 11 address is the `TREE` address (FIPS 205, Figure 5)
of the input's layer and tree with tree height `levels` and tree index `⌊idx / 2^levels⌋`. In
particular the source's two index updates, `i / 2` and `(i - 1) / 2`, both halve the index. -/
theorem authenticationAddress_eq_tree {p : SecurityBytes} {shape : ParameterShape}
    (address : Address) (idx : LeafIndex p shape) (levels : ℕ)
    (hlevels : levels ≤ ParameterShape.xmssHeight p shape) :
    authenticationAddress address idx levels hlevels =
      Address.tree address.layerAddress address.treeAddress
        ⟨levels, hlevels.trans_lt
          (Nat.lt_two_pow_self.trans_le (ParameterShape.two_pow_xmssHeight_le p shape))⟩
        ⟨idx.val / 2 ^ levels, (Nat.div_le_self _ _).trans_lt
          (idx.isLt.trans_le (ParameterShape.two_pow_xmssHeight_le p shape))⟩ := by
  induction levels with
  | zero =>
      exact Address.ext rfl rfl rfl rfl rfl (Fin.ext (Nat.div_one idx.val).symm)
  | succ levels ih =>
      have hhalf : idx.val / 2 ^ (levels + 1) = idx.val / 2 ^ levels / 2 := by
        rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
      change stepAddress (authenticationAddress address idx levels _) _ _ = _
      rw [ih (Nat.le_of_succ_le hlevels)]
      refine Address.ext rfl rfl rfl rfl rfl (Fin.ext ?_)
      by_cases heven : idx.val / 2 ^ levels % 2 = 0
      · exact (congrArg Fin.val (ite_eq_left heven)).trans hhalf.symm
      · refine (congrArg Fin.val (ite_eq_right heven)).trans ?_
        change (idx.val / 2 ^ levels - 1) / 2 = idx.val / 2 ^ (levels + 1)
        rw [hhalf]
        generalize idx.val / 2 ^ levels = i at heven ⊢
        omega

/-- The node `node[0]` of FIPS 205 Algorithm 11 after `levels` iterations of its loop, starting
from `leaf` (line 5).

Iteration `k` (lines 9--17) calls `H` under the address after `k + 1` iterations, on the current
node followed by `AUTH[k]` when `⌊idx / 2^k⌋` is even (line 12) and on `AUTH[k]` followed by the
current node otherwise (line 15). -/
def authenticationNode (family : HashFamily) {p : SecurityBytes} {shape : ParameterShape}
    (idx : LeafIndex p shape)
    (authentication : Fin (ParameterShape.xmssHeight p shape) → NBytes p)
    (publicSeed : NBytes p) (address : Address) (leaf : NBytes p) :
    (levels : ℕ) → levels ≤ ParameterShape.xmssHeight p shape → NBytes p
  | 0, _ => leaf
  | levels + 1, hlevels =>
      h family publicSeed (authenticationAddress address idx (levels + 1) hlevels)
        (if idx.val / 2 ^ levels % 2 = 0 then
          FixedBytes.pairBlocks
            (authenticationNode family idx authentication publicSeed address leaf levels
              (Nat.le_of_succ_le hlevels))
            (authentication ⟨levels, hlevels⟩)
        else
          FixedBytes.pairBlocks (authentication ⟨levels, hlevels⟩)
            (authenticationNode family idx authentication publicSeed address leaf levels
              (Nat.le_of_succ_le hlevels)))

/-- Before the loop the node is the leaf. -/
@[simp] theorem authenticationNode_zero (family : HashFamily) {p : SecurityBytes}
    {shape : ParameterShape} (idx : LeafIndex p shape)
    (authentication : Fin (ParameterShape.xmssHeight p shape) → NBytes p)
    (publicSeed : NBytes p) (address : Address) (leaf : NBytes p)
    (hlevels : 0 ≤ ParameterShape.xmssHeight p shape) :
    authenticationNode family idx authentication publicSeed address leaf 0 hlevels = leaf :=
  (rfl)

/-- Iteration `levels` of the loop: one `H` call under the next address, with the current node
first exactly when `⌊idx / 2^levels⌋` is even. -/
theorem authenticationNode_succ (family : HashFamily) {p : SecurityBytes}
    {shape : ParameterShape} (idx : LeafIndex p shape)
    (authentication : Fin (ParameterShape.xmssHeight p shape) → NBytes p)
    (publicSeed : NBytes p) (address : Address) (leaf : NBytes p) (levels : ℕ)
    (hlevels : levels + 1 ≤ ParameterShape.xmssHeight p shape) :
    authenticationNode family idx authentication publicSeed address leaf (levels + 1) hlevels =
      h family publicSeed (authenticationAddress address idx (levels + 1) hlevels)
        (if idx.val / 2 ^ levels % 2 = 0 then
          FixedBytes.pairBlocks
            (authenticationNode family idx authentication publicSeed address leaf levels
              (Nat.le_of_succ_le hlevels))
            (authentication ⟨levels, hlevels⟩)
        else
          FixedBytes.pairBlocks (authentication ⟨levels, hlevels⟩)
            (authenticationNode family idx authentication publicSeed address leaf levels
              (Nat.le_of_succ_le hlevels))) :=
  (rfl)

/-- FIPS 205 Algorithm 11 (`xmss_pkFromSig`): the WOTS+ public key reconstructed under the
`WOTS_HASH` address with key-pair address `idx` (lines 1--5), followed by all `h'` iterations of
the authentication loop (lines 6--19). -/
def xmssPkFromSig (family : HashFamily) {p : SecurityBytes} {shape : ParameterShape}
    (idx : LeafIndex p shape) (sig : Signature p shape) (M : WOTS.Message p)
    (publicSeed : NBytes p) (address : Address) : NBytes p :=
  authenticationNode family idx sig.authentication publicSeed address
    (WOTS.wotsPkFromSig family sig.wots M publicSeed
      ((address.setTypeAndClear .wotsHash).setKeyPairAddress
        (idx.castLE (ParameterShape.two_pow_xmssHeight_le p shape))))
    (ParameterShape.xmssHeight p shape) (Nat.le_refl _)

/-- Algorithm 11 is the full authentication loop started from the Algorithm 8 public key of leaf
`idx`. -/
theorem xmssPkFromSig_eq (family : HashFamily) {p : SecurityBytes} {shape : ParameterShape}
    (idx : LeafIndex p shape) (sig : Signature p shape) (M : WOTS.Message p)
    (publicSeed : NBytes p) (address : Address) :
    xmssPkFromSig family idx sig M publicSeed address =
      authenticationNode family idx sig.authentication publicSeed address
        (WOTS.wotsPkFromSig family sig.wots M publicSeed
          ((address.setTypeAndClear .wotsHash).setKeyPairAddress
            (idx.castLE (ParameterShape.two_pow_xmssHeight_le p shape))))
        (ParameterShape.xmssHeight p shape) (Nat.le_refl _) :=
  (rfl)

end Cslib.Crypto.SLHDSA.XMSS
