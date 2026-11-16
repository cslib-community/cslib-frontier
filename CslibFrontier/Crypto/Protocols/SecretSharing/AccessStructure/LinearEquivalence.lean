/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.SpanProgram.ChangeOfBasis
public import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Linear
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Equivalent monotone span programs

Two monotone span programs are *equivalent* when, for every secret, the linear secret sharing
schemes derived from them give the same distribution of shares
[Boneh and Shoup, Definition 22.23, p. 981][BonehShoup2023]. Here that is the equation
`(linearUniformAccessScheme P').shareDist (uniformOfFintype (LinearKey P')) secret =
(linearUniformAccessScheme P).shareDist (uniformOfFintype (LinearKey P)) secret` for every
`secret`, over a finite field, with no separate predicate: the two sides have the same type only
when the programs have the same row dimensions. Their numbers of columns may differ.

Lemma 22.15 of [BonehShoup2023] says that multiplying every matrix on the right by an invertible
matrix `R` whose top row is `e₁` gives an equivalent program. For a key `k`, the program
`(M_i * R)_i` gives the shares that `P` gives for the key `tail (R * (secret, k))`, and that map
of keys is a bijection, so a uniform key goes to a uniform key.

## Main results

* `Cslib.Crypto.Protocols.SecretSharing.shareDist_linearUniformAccessScheme_mulRight`:
  Lemma 22.15.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Definition 22.23 and Lemma 22.15, pp. 981–982.
-/

public section

open scoped Matrix

namespace Cslib.Crypto.Protocols.SecretSharing

open Cslib.Circuits Cslib.Probability Cslib.Probability.PMF

variable {F Party : Type*} [Field F] [Fintype F]

/-- **Lemma 22.15** ([BonehShoup2023], p. 982): for an invertible matrix `R` whose top row is
`e₁`, the programs `P` and `(M_i * R)_i` give the same distribution of shares under a uniform
key. Holding for every `secret`, this is the equivalence of the two programs in the sense of
Definition 22.23 (p. 981). -/
theorem shareDist_linearUniformAccessScheme_mulRight (P : MonotoneSpanProgram F Party)
    {R : Matrix (Fin (P.tailDim + 1)) (Fin (P.tailDim + 1)) F} (hR : IsUnit R.det)
    (htop : R 0 = Pi.single 0 1) (secret : F) :
    (linearUniformAccessScheme (P.mulRight R)).shareDist
        (uniformOfFintype (LinearKey (P.mulRight R))) secret =
      (linearUniformAccessScheme P).shareDist (uniformOfFintype (LinearKey P)) secret := by
  have hhead : ∀ x : Fin (P.tailDim + 1) → F, (R *ᵥ x) 0 = x 0 := by
    intro x
    rw [Matrix.mulVec, htop, single_one_dotProduct]
  let T : LinearKey P → LinearKey P := fun k => Fin.tail (R *ᵥ Fin.cons secret k)
  have hcons : ∀ k : LinearKey P, R *ᵥ Fin.cons secret k = Fin.cons secret (T k) := by
    intro k
    have h0 : (R *ᵥ Fin.cons secret k) 0 = secret := by rw [hhead, Fin.cons_zero]
    calc R *ᵥ Fin.cons secret k
        = Fin.cons ((R *ᵥ Fin.cons secret k) 0) (Fin.tail (R *ᵥ Fin.cons secret k)) :=
          (Fin.cons_self_tail _).symm
      _ = Fin.cons secret (T k) := by rw [h0]
  have hT : Function.Injective T := by
    intro k₁ k₂ h
    have hmul : R *ᵥ Fin.cons secret k₁ = R *ᵥ Fin.cons secret k₂ := by rw [hcons, hcons, h]
    have := Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det R).2 hR) hmul
    exact (Fin.cons_right_injective (α := fun _ => F) secret) this
  have hshare : (fun k : LinearKey P => linearShare (P.mulRight R) k secret) =
      (fun k => linearShare P k secret) ∘ T := by
    funext k i
    change (P.matrix i * R) *ᵥ Fin.cons secret k = P.matrix i *ᵥ Fin.cons secret (T k)
    rw [← Matrix.mulVec_mulVec, hcons]
  have h₁ : (linearUniformAccessScheme (P.mulRight R)).shareDist
      (uniformOfFintype (LinearKey P)) secret =
        (uniformOfFintype (LinearKey P)).map ((fun k => linearShare P k secret) ∘ T) :=
    congrArg (fun f => (uniformOfFintype (LinearKey P)).map f) hshare
  have h₂ : (uniformOfFintype (LinearKey P)).map ((fun k => linearShare P k secret) ∘ T) =
      (linearUniformAccessScheme P).shareDist (uniformOfFintype (LinearKey P)) secret := by
    rw [← PMF.map_comp, show (uniformOfFintype (LinearKey P)).map T =
      uniformOfFintype (LinearKey P) from
        uniformOfFintype_map_equiv (Equiv.ofBijective T (Finite.injective_iff_bijective.1 hT))]
    rfl
  exact h₁.trans h₂

end Cslib.Crypto.Protocols.SecretSharing
