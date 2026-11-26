/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.KeyChain.Reduction.Game
public import CslibFrontier.Crypto.Computational.Homomorphic.KeyChain.Reduction.PolyTime
public import CslibFrontier.Crypto.Computational.Encryption.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.Negligible

/-!
# Security of an acyclic encrypted-key chain

Base IND-CPA security hides every secret-key bit encrypted in the public acyclic chain. The
reduction replaces links from the end of the chain and bits from the beginning of each secret.
Its two coordinates are sampled uniformly from polynomially bounded dyadic ranges.

The secret-width function need not be computable. A native key-generation certificate supplies
an executable polynomial cap, while equality of supported secret lengths justifies the unknown
target-secret substitution. The reduction contains no parameter-dependent advice and requires
no decryption correctness or bootstrappability assumption.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.negligible_publicKeyChainHybrid`: every native uniform test
  has negligible advantage between the actual public chain and its all-zero-link hybrid.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2][Gentry2009]
-/

public section

namespace Cslib.Crypto.Homomorphic.Scheme

open Probability Turing.MultiTapeTM
open scoped NNReal

/-- Encrypting an acyclic chain of fixed-length secrets is indistinguishable from encrypting
zero words. The complete public keys and every encrypted link are given to the native test. -/
theorem negligible_publicKeyChainHybrid {E : Scheme}
    (hsecure : Encryption.INDCPA E.keyGen E.encrypt)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun (n, pk, bit) => E.encrypt n pk bit))
    {width depth : ℕ → ℕ}
    (hwidth : ∀ n keys, keys ∈ (ProbComp.eval (E.keyGen n)).support →
      keys.2.length = width n)
    (hdepth : ComputableInPolyTime depth encUnary encUnary)
    {test : ℕ → (List (List Bool) × List (List (List Bool))) → ProbComp Bool}
    (htest : IsPPTOn
      (encPair encUnary (encPair (encList encBits) (encList (encList encBits)))) encBool
      (fun p => test p.1 p.2)) :
    Negligible (fun n => Game.advantage
      (ProbComp.eval (E.publicKeyChainHybrid n (depth n) (depth n) >>= test n))
      (ProbComp.eval (E.publicKeyChainHybrid n (depth n) 0 >>= test n))) := by
  obtain ⟨c, d, hcapacity, hbound⟩ := Encryption.exists_keyLength_bound hkeyGen
  have hwidth_le (n : ℕ) : width n ≤ c * (n + 1) ^ d := by
    obtain ⟨keys, hkeys⟩ := (ProbComp.eval (E.keyGen n)).support_nonempty
    exact (Nat.le_add_left _ _).trans (hwidth n keys hkeys ▸ hbound n keys hkeys)
  have hneg := hsecure _ (isPPT_linkAdversary hkeyGen hencrypt htest hdepth hcapacity)
  negligible using fun n => (E.publicKeyChainHybrid_advantage_linkAdversary depth
    (fun n => c * (n + 1) ^ d) test n (width n) (hwidth n) (hwidth_le n)).le

end Cslib.Crypto.Homomorphic.Scheme
