/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.MerkleDamgard
import CslibFrontier.Crypto.Computational.MerkleTree.Binding

/-!
# Merkle position binding from a `module` client

[BonehShoup2023], Theorem 8.8 (`CollisionResistantOn.merklePositionBinding`), used from a `module`
file: a hash that is collision resistant on the domain of a tree with one-bit leaves gives position
binding with one-bit leaves, and a compression family gives position binding for every leaf space
through Merkle–Damgård. At parameter `2` the domain contains the one-bit leaves and the pairs of
two-bit digests, and no other words of these shapes.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.MerkleBindingModule

open Cslib Cslib.Crypto Turing.MultiTapeTM

/-- The leaf space of one-bit words. -/
abbrev oneBitLeaves (_ : ℕ) (x : List Bool) : Bool := x.length == 1

-- Theorem 8.8 with one-bit leaves.
example {H : List Bool → List Bool → List Bool}
    (hCR : CollisionResistantOn H (merkleHashDomain oneBitLeaves))
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length) :
    MerklePositionBinding H oneBitLeaves :=
  hCR.merklePositionBinding hH hlen

-- A compression family gives position binding for every leaf space: Merkle–Damgård is collision
-- resistant on all words, hence on the domain of the tree's hash.
example {h : List Bool → List Bool → List Bool} (hh : CompressionFamily h)
    (leafSpace : ℕ → List Bool → Bool) : MerklePositionBinding (merkleDamgard h) leafSpace :=
  (CollisionResistantOn.mono hh.hashFamily_merkleDamgard.collisionResistant
    (.of_forall fun _ _ _ => rfl)).merklePositionBinding hh.hashFamily_merkleDamgard.polyTime
      hh.hashFamily_merkleDamgard.length_eq

-- The domain at parameter `2`: one-bit leaves and pairs of two-bit digests.
example : merkleHashDomain oneBitLeaves 2 [true] = true := by decide

example :
    merkleHashDomain oneBitLeaves 2 (encPair encBits encBits ([true, false], [false, false])) =
      true := by decide

-- A two-bit leaf, and a pair whose left part is not a two-bit digest, lie outside it.
example : merkleHashDomain oneBitLeaves 2 [true, false] = false := by decide

example : merkleHashDomain oneBitLeaves 2 (encPair encBits encBits ([true], [false, false])) =
    false := by decide

end CslibFrontierTests.Crypto.MerkleBindingModule
