/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.RSATrapdoor
public import CslibFrontier.Crypto.Computational.Signature.Scheme

/-!
# RSA signatures on a digest

[BonehShoup2023], Section 13.3.1, signs a message `m` with the RSA key `(n, d)` as
`σ := H(m) ^ d ∈ ℤ_n` and accepts `σ` on `m` when `σ ^ e = H(m)`. `rsaSignature desc H` is this
`Signature.Scheme` for the key `desc` and any digest function `H : M → ℕ`, and
`unhashedRSASignature desc` is the unhashed RSA system of p. 537, which signs a residue
`m : Fin N` directly.

The scheme is the scheme of one key: key generation returns `desc`, where the book's key
generator runs `RSAGen(ℓ, e)`. Every statement about it holds for every key, so it holds for a
key drawn from any law first, as `rsaInversionGame` draws its key. Signatures are natural numbers,
and `verify` accepts `σ` on `m` when `σ < N` and `σ ^ e % N = H m % N`; the book takes `σ ∈ ℤ_n`
and compares `σ ^ e` with `H(m)`, whose range it describes as "embedded in `ℤ_n`".

## Main definitions

* `Cslib.Crypto.rsaSignature`: RSA signatures on the digest `H m`, for a fixed key.
* `Cslib.Crypto.unhashedRSASignature`: RSA signatures on residues modulo `N`, without a hash.

## Main results

* `Cslib.Crypto.rsaSignature_correct`: every signature verifies.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section
  13.3.1, pp. 536–537.
-/

public section

namespace Cslib.Crypto

open Probability

variable {M : Type}

/-- RSA signatures on a digest, for the key `desc` and the digest function `H`
([BonehShoup2023], Section 13.3.1): the signature on `m` is `H m ^ d % N`, and `σ` is accepted
on `m` when `σ < N` and `σ ^ e % N = H m % N`. Key generation returns the fixed key. -/
@[expose]
def rsaSignature (desc : RSADesc) (H : M → ℕ) : Signature.Scheme RSAPublicKey RSADesc M ℕ where
  keyGen := pure (desc.publicKey, desc)
  sign sk m := pure (rsaInvert sk.modulus sk.d (H m))
  verify pk m σ := decide (σ < pk.N ∧ rsaEval pk.N pk.e σ = H m % pk.N)

/-- The unhashed RSA system ([BonehShoup2023], p. 537): the messages are the residues modulo `N`
and the signature on `m` is `m ^ d % N`. -/
abbrev unhashedRSASignature (desc : RSADesc) :
    Signature.Scheme RSAPublicKey RSADesc (Fin desc.modulus) ℕ :=
  rsaSignature desc Fin.val

/-- The verification test of `rsaSignature`: `σ < N` and `σ ^ e % N = H m % N`. -/
@[simp] theorem rsaSignature_verify_iff (desc : RSADesc) (H : M → ℕ) (pk : RSAPublicKey) (m : M)
    (σ : ℕ) :
    (rsaSignature desc H).verify pk m σ = true ↔
      σ < pk.N ∧ rsaEval pk.N pk.e σ = H m % pk.N := by
  simp [rsaSignature]

/-- Every signature of `rsaSignature` verifies. -/
theorem rsaSignature_correct (desc : RSADesc) (H : M → ℕ) : (rsaSignature desc H).Correct := by
  intro keys hkeys m σ hσ
  simp only [rsaSignature, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hkeys hσ
  subst hkeys hσ
  rw [rsaSignature_verify_iff]
  exact ⟨Nat.mod_lt _ desc.modulus_pos, rsaEval_rsaInvert_mod desc (H m)⟩

end Cslib.Crypto
