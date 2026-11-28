/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.SpanProgram.Elimination
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

For parties `Fin N` and a field with decidable equality, where elimination runs, this module also
proves the identities of the two parts of Theorem 22.14 of [BonehShoup2023] (p. 981). They are
steps toward that theorem, not the theorem. Part (a): for an accepted coalition, the vectors of
the algorithm `Lin` (`MonotoneSpanProgram.recombination`) recombine the members' shares to the
secret, for every key. Part (b)(i): for a coalition that is not accepted, the program `P_L`
(`MonotoneSpanProgram.normalForm`) is equivalent to `P`, by Lemma 22.15. Theorem 22.14 also says
that `Lin` is an efficient deterministic algorithm and that `P_L` is efficiently computable. The
only bounds are those of `CslibFrontier.Computability.Circuit.SpanProgram.EliminationSynthesis`,
one field-gate circuit for each shape of program; a uniform bound in bit operations is open
(#5293).

## Main results

* `Cslib.Crypto.Protocols.SecretSharing.shareDist_linearUniformAccessScheme_mulRight`:
  Lemma 22.15.
* `Cslib.Crypto.Protocols.SecretSharing.sum_recombination_dotProduct_linearShare`: the
  recombination identity of Theorem 22.14(a), a step toward that theorem.
* `Cslib.Crypto.Protocols.SecretSharing.shareDist_linearUniformAccessScheme_normalForm`: the
  equivalence of Theorem 22.14(b)(i), a step toward that theorem.
* `Cslib.Crypto.Protocols.SecretSharing.linearShare_eq_of_col_zero`: a share whose matrix has
  first column zero does not depend on the secret.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Definition 22.23, Theorem 22.14 and Lemma 22.15, pp. 981–982.
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
    rw [Matrix.mulVec_apply, Matrix.row_apply', htop, single_one_dotProduct]
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

omit [Fintype F] in
/-- A share whose matrix has left-most column zero does not depend on the secret
([BonehShoup2023], discussion after Theorem 22.14, p. 981). -/
theorem linearShare_eq_of_col_zero (P : MonotoneSpanProgram F Party) {i : Party}
    (h : ∀ row, P.matrix i row 0 = 0) (k : LinearKey P) (secret₀ secret₁ : F) :
    linearShare P k secret₀ i = linearShare P k secret₁ i := by
  funext row
  simp [linearShare, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h]

variable [DecidableEq F] {N : ℕ}

omit [Fintype F] in
/-- The recombination identity of Theorem 22.14(a), a step toward [BonehShoup2023],
Theorem 22.14 (p. 981), not that theorem: for an accepted coalition `s`, the vectors
`P.recombination s` that elimination computes for the algorithm `Lin` recombine the shares of the
members of `s` to the secret, for every key. Theorem 22.14(a) also says that `Lin` is an efficient
deterministic algorithm. The only bound is `Cslib.Circuits.Synthesis.full_recombination`, one
field-gate circuit for each shape of program; a uniform bound in bit operations is open
(#5293). -/
theorem sum_recombination_dotProduct_linearShare (P : MonotoneSpanProgram F (Fin N))
    {s : Finset (Fin N)} (hs : P.Accepts s) (k : LinearKey P) (secret : F) :
    ∑ i : s, P.recombination s i.val ⬝ᵥ linearShare P k secret i.val = secret :=
  sum_dotProduct_linearShare_eq_secret P k secret (fun i => P.recombination s i.val)
    (P.sum_vecMul_recombination hs)

/-- The equivalence of Theorem 22.14(b)(i), a step toward [BonehShoup2023], Theorem 22.14
(p. 981), not that theorem: for a coalition `s` that is not accepted, the program
`P_L = P.normalForm s` is equivalent to `P`, giving the same distribution of shares under a
uniform key. The zero column of part (ii) is `MonotoneSpanProgram.normalForm_matrix_zero`, and
with `linearShare_eq_of_col_zero` it says that the shares of the members of `s` do not depend on
the secret. Theorem 22.14(b) also says that `P_L` is efficiently computable. The only bound is
`Cslib.Circuits.Synthesis.full_normalForm`, one field-gate circuit for each shape of program; a
uniform bound in bit operations is open (#5293). -/
theorem shareDist_linearUniformAccessScheme_normalForm (P : MonotoneSpanProgram F (Fin N))
    {s : Finset (Fin N)} (hs : ¬ P.Accepts s) (secret : F) :
    (linearUniformAccessScheme (P.normalForm s)).shareDist
        (uniformOfFintype (LinearKey (P.normalForm s))) secret =
      (linearUniformAccessScheme P).shareDist (uniformOfFintype (LinearKey P)) secret :=
  shareDist_linearUniformAccessScheme_mulRight P (P.shearMatrix_nullVector_of_not_accepts hs).1
    (P.shearMatrix_nullVector_of_not_accepts hs).2 secret

end Cslib.Crypto.Protocols.SecretSharing
