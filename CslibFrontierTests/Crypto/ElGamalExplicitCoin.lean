/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.DiffieHellman.Static
public import CslibFrontier.Crypto.Computational.ElGamal
public import CslibFrontier.Crypto.Computational.ElGamal.ExplicitCoin

/-!
# Tests for multiplicative ElGamal over a fixed group

Checks of `CslibFrontier/Crypto/Computational/ElGamal/ExplicitCoin.lean` as an ordinary `module`
client: one encryption and its decryption in `ZMod 5`; correctness applied to a key pair and a
ciphertext; at a member of a group family the scheme's encryption and decryption are the library's
`elGamalEncrypt` and `elGamalDecrypt`; and decryption is the decryption oracle of the static
Diffie–Hellman module.
-/

public section

namespace CslibFrontierTests.Crypto.ElGamalExplicitCoin

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Protocols

/-- In `ZMod 5` with `g = 1`, the public key of the secret key `2` is `2`; the message `3` is
encrypted with coins `4` as `(4 • 1, 4 • 2 + 3) = (4, 1)`, which decrypts to `1 - 2 • 4 = 3`. -/
example : (elGamalExplicitCoinPKE 5 (1 : ZMod 5)).encDet 2 3 4 = (4, 1) ∧
    (elGamalExplicitCoinPKE 5 (1 : ZMod 5)).dec 2 (4, 1) = some 3 := by
  decide

/-- Correctness at one key pair and one ciphertext: `(β • g, β • (α • g) + x)` decrypts to `x`
under the secret key `α`. -/
example {G : Type} [AddCommGroup G] (q : ℕ) [NeZero q] [Module (ZMod q) G] (g : G)
    (α β : ZMod q) (x : G) :
    (elGamalExplicitCoinPKE q g).dec α (β • g, β • α • g + x) = some x :=
  elGamalExplicitCoinPKEWith_correct q g ($ᵗ ZMod q) (α • g, α)
    (by simp [ExplicitCoinPKE.toPKE, elGamalExplicitCoinPKEWith]) x _
    (by simpa [ExplicitCoinPKE.toPKE, ExplicitCoinPKE.encrypt, elGamalExplicitCoinPKEWith]
      using ⟨β, rfl, rfl⟩)

/-- At a member of a group family, encryption is the library's `elGamalEncrypt`. -/
example (F : PrimeOrderGroupFamily) (d : F.Desc) (u x : F.Carrier d) (β : ZMod (F.order d)) :
    (elGamalExplicitCoinPKE (F.order d) (F.generator d)).encDet u x β =
      F.elGamalEncrypt d u x β := rfl

/-- At a member of a group family, decryption is the library's `elGamalDecrypt`. -/
example (F : PrimeOrderGroupFamily) (d : F.Desc) (α : ZMod (F.order d))
    (ct : F.Carrier d × F.Carrier d) :
    (elGamalExplicitCoinPKE (F.order d) (F.generator d)).dec α ct =
      some (F.elGamalDecrypt d α ct) := rfl

/-- Decryption is the decryption oracle of the static Diffie–Hellman module. -/
example {G : Type} [AddCommGroup G] [DecidableEq G] (q : ℕ) [NeZero q] [Module (ZMod q) G] (g : G)
    (α : ZMod q) (ct : G × G) :
    pure ((elGamalExplicitCoinPKE q g).dec α ct) =
      (some <$> elGamalDecryptOracle q α ct : ProbComp (Option G)) := by
  simp [elGamalExplicitCoinPKEWith, elGamalDecryptOracle]

end CslibFrontierTests.Crypto.ElGamalExplicitCoin
