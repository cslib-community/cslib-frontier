/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game
public import CslibFrontier.Foundations.Data.BitString.Basic
public import CslibFrontier.Languages.Probabilistic.Oracle.CoinFixing
public import CslibFrontier.Languages.Probabilistic.QueryCount
public import CslibFrontier.Languages.Probabilistic.RandomPermutation
public import CslibFrontier.Languages.Probabilistic.Sum
public import Mathlib.Data.Fintype.Perm
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm
import CslibFrontier.Languages.Probabilistic.Simulation
import CslibFrontier.Probability.BitString
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Probability.Uniform
import CslibFrontier.Tactic.ENNRealToReal
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.SuppCases
import CslibFrontier.Tactic.UniformRelabel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Even–Mansour cipher in the ideal-permutation model

The Even–Mansour construction ([BonehShoup2023], Section 4.7; [EvenMansour1997]) builds a block
cipher from a single public permutation `π : Equiv.Perm G` on a finite group `G` by XORing (or
adding in `G`) independent pre-whitening and post-whitening keys `(k₀, k₁) ∈ G × G`:
$$E((k_0, k_1), x) = \pi(x + k_0) + k_1, \qquad D((k_0, k_1), y) = \pi^{-1}(y - k_1) - k_0.$$
In the single-key variant ([DunkelmanKellerShamir2012]), `k₀ = k₁ = k`.

We formalize four aspects of the Even–Mansour construction:

1. **Algebraic structure and one-query secrecy**: `evenMansourEquiv π k₀ k₁ : Equiv.Perm G`
   bundles encryption and decryption as a permutation of `G`, satisfies the inverse-cipher
   conjugation law `(evenMansourEquiv π k₀ k₁).symm = evenMansourEquiv π.symm (-k₁) (-k₀)` (which
   swaps `k₀` and `k₁` over any group of exponent two such as `BitString n`), acts as a bijection
   on `Equiv.Perm G` for every fixed key pair (`evenMansourPermEquiv`), and achieves perfect
   one-query secrecy for any fixed `π` (`map_prod_evenMansourEncrypt_uniformOfFintype`).
2. **Necessity of both whitening keys ([BonehShoup2023], Section 4.7.3 and Exercise 4.20)**:
   omitting post-whitening (`preWhitenEquiv π k₀ x = π (x + k₀)`) or pre-whitening
   (`postWhitenEquiv π k₁ x = π x + k₁`) allows an explicit 2-query adversary (making `1` cipher
   query and `1` primitive permutation query, `IsCallBounded _ 1 1`) to recover the secret key with
   probability `1` and achieve key-recovery game advantage `1 - |G|⁻¹` against an independent
   uniform permutation and uniform target key (`advantage_preWhitenKeyRecoveryGame_eq`,
   `advantage_postWhitenKeyRecoveryGame_eq`).
3. **One-sided query security and lazy ideal-permutation equivalence**: because
   `evenMansourPermEquiv k₀ k₁` is a bijection on `Equiv.Perm G`, any adversary that queries only
   the cipher oracle (`liftLeft`) or only the primitive permutation oracle (`liftRight`) has zero
   distinguishing advantage between the real Even–Mansour game and two independent uniform
   permutations (`advantage_evenMansourRealGame_liftLeft_eq_zero`,
   `advantage_evenMansourRealGame_liftRight_eq_zero`). Moreover, `evenMansourIdealGame` is
   identically distributed to running two independent lazy bidirectional permutation samplers
   (`idealLazyHandler`) from empty caches (`evenMansourIdealGame_eq_lazy`).
4. **Bad-key transcript intersection bound ([BonehShoup2023], Theorem 4.14)**: given a cipher
   transcript `T_e : List (G × G)` and a primitive permutation transcript `T_π : List (G × G)`, a
   key `(k₀, k₁)` is bad (`isBadEvenMansourKey T_e T_π k`) when some `(x, y) ∈ T_e` and
   `(u, v) ∈ T_π` collide on the internal permutation input (`x + k₀ = u`) or output
   (`y - k₁ = v`). Outside this bad set, the internal permutation queries made through the cipher
   are disjoint in both domain and range from the direct queries to `π`
   (`disjoint_of_isBadEvenMansourKey_eq_false`), and when `T_e` and `T_π` are consistent with
   `evenMansourEquiv π k₀ k₁` and `π`, output collisions reduce to input collisions
   (`isBadKeyPair_eq_decide_of_evenMansourEquiv`). Under a uniform two-key `(k₀, k₁)` or single
   key `k`, the bad-key probability is at most `2 * |T_e| * |T_π| / |G|`
    (`toOuterMeasure_isBadEvenMansourKey_toReal_le`,
    `toOuterMeasure_isBadSingleKeyEvenMansour_toReal_le`). For any deterministic (coin-free)
    adaptive distinguisher satisfying `IsCallBounded program Q_e Q_π`,
    `OracleComp.IsCostBounded.transcript_cost_le` bounds every supported transcript by
    `|T_e| ≤ Q_e` and `|T_π| ≤ Q_π`, yielding the `2 * Q_e * Q_π / |G|` bad-key bound on every
    supported execution path (`IsCallBounded.badEvenMansourKey_toReal_le`,
    `IsCallBounded.badSingleKeyEvenMansour_toReal_le`). Coupling `idealLazyHandler` to a single
    key-shifted lazy permutation cache bounds the distinguishing advantage of any deterministic
    (`Q_e`, `Q_π`)-query adversary against both two-key and single-key Even–Mansour by
    `2 * Q_e * Q_π / |G|` (`advantage_evenMansourRealGame_evenMansourIdealGame_le`,
    `advantage_singleKeyEvenMansourRealGame_evenMansourIdealGame_le`).
5. **Randomized (`ProbOracleComp`) distinguishers via coin fixing**: fixing private coins
   (`ProbOracleComp.coinLaw`) lifts the deterministic two-key and single-key games and their
   `2 * Q_e * Q_π / |G|` bounds to arbitrary randomized adaptive distinguishers
   `ProbOracleComp (EvenMansourSpec G) Bool` with separate cipher and primitive query budgets
   `IsProbCallBounded program Q_e Q_π`
   (`advantage_evenMansourProbRealGame_evenMansourProbIdealGame_le`,
   `advantage_singleKeyEvenMansourProbRealGame_evenMansourProbIdealGame_le`, and the `BitString n`
   specializations `advantage_evenMansourProbRealGame_bitString_le`,
   `advantage_singleKeyEvenMansourProbRealGame_bitString_le`).

## Main definitions

* `Cslib.Crypto.EvenMansour.evenMansourEncrypt`, `evenMansourDecrypt`, `evenMansourEquiv`,
  `singleKeyEvenMansourEquiv`: Even–Mansour encryption, decryption, and bundled permutations.
* `Cslib.Crypto.EvenMansour.preWhitenEquiv`, `postWhitenEquiv`, `preWhitenKeyRecoveryAttack`,
  `postWhitenKeyRecoveryAttack`: single-whitening variants and 2-query key-recovery attacks.
* `Cslib.Crypto.EvenMansour.EvenMansourSpec`, `IsCallBounded`, `IsProbCallBounded`:
  bidirectional cipher and primitive permutation oracle interface and separate query budgets for
  coin-free and randomized distinguishers.
* `Cslib.Crypto.EvenMansour.evenMansourRealGame`, `singleKeyEvenMansourRealGame`,
  `evenMansourIdealGame`, `evenMansourProbRealGame`, `singleKeyEvenMansourProbRealGame`,
  `evenMansourProbIdealGame`, `idealLazyHandler`, `realLazyHandler`: deterministic and randomized
  real and ideal bidirectional permutation games and lazy two-cache and single-cache handlers.
* `Cslib.Crypto.EvenMansour.isBadKeyPair`, `isBadEvenMansourKey`, `isBadSingleKeyEvenMansour`,
  `transcriptCipher`, `transcriptPerm`: bad-key collision predicates and transcript projections.

## Main results

* `Cslib.Crypto.EvenMansour.map_prod_evenMansourEncrypt_uniformOfFintype`: one-query perfect
  secrecy and independence from the pre-whitening key `k₀`.
* `Cslib.Crypto.EvenMansour.advantage_preWhitenKeyRecoveryGame_eq`,
  `Cslib.Crypto.EvenMansour.advantage_postWhitenKeyRecoveryGame_eq`: 2-query attacks achieve
  key-recovery game advantage `1 - |G|⁻¹` when either whitening key is omitted.
* `Cslib.Crypto.EvenMansour.evenMansourIdealGame_eq_lazy`,
  `Cslib.Crypto.EvenMansour.run_idealLazyHandler_good_le_realLazyHandler`,
  `Cslib.Crypto.EvenMansour.advantage_evenMansourRealGame_liftLeft_eq_zero`,
  `Cslib.Crypto.EvenMansour.advantage_evenMansourRealGame_liftRight_eq_zero`: lazy two-permutation
  equivalence for `evenMansourIdealGame`, lazy coupling inequality, and zero advantage when
  queries are restricted to one oracle.
* `Cslib.Crypto.EvenMansour.toOuterMeasure_isBadEvenMansourKey_toReal_le`,
  `Cslib.Crypto.EvenMansour.toOuterMeasure_isBadSingleKeyEvenMansour_toReal_le`,
  `Cslib.Crypto.EvenMansour.IsCallBounded.badEvenMansourKey_toReal_le`,
  `Cslib.Crypto.EvenMansour.IsCallBounded.badSingleKeyEvenMansour_toReal_le`:
  Boneh–Shoup Theorem 4.14 bad-key probability bound `2 * Q_e * Q_π / |G|`.
* `Cslib.Crypto.EvenMansour.advantage_evenMansourRealGame_evenMansourIdealGame_le`,
  `Cslib.Crypto.EvenMansour.advantage_singleKeyEvenMansourRealGame_evenMansourIdealGame_le`,
  `Cslib.Crypto.EvenMansour.advantage_evenMansourProbRealGame_evenMansourProbIdealGame_le`,
  `Cslib.Crypto.EvenMansour.advantage_singleKeyEvenMansourProbRealGame_evenMansourProbIdealGame_le`:
  end-to-end PRP security bounds `2 * Q_e * Q_π / |G|` in the ideal-permutation model for
  deterministic and randomized distinguishers.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 4.7 (Theorem 4.14 in Section 4.7.4, p. 159; Even–Mansour
  is its single-key case `|K| = 1`, and Exercise 4.20 covers the single-whitening variants).
* [S. Even, Y. Mansour, *A Construction of a Cipher from a Single Pseudorandom
  Permutation*][EvenMansour1997].
* [O. Dunkelman, N. Keller, A. Shamir, *Minimalism in Cryptography: The Even–Mansour Scheme
  Revisited*][DunkelmanKellerShamir2012].
-/

@[expose] public section

namespace Cslib.Crypto.EvenMansour

open Probability OracleComp RandomPermutation
open scoped ENNReal NNReal BigOperators

/-! ### Algebraic Even–Mansour cipher over an additive group -/

section Algebraic

variable {G : Type*} [AddGroup G]

/-- Even–Mansour encryption ([BonehShoup2023], Section 4.7; [EvenMansour1997]): pre-whiten by adding
`k₀`, apply the public permutation `π`, and post-whiten by adding `k₁`. -/
def evenMansourEncrypt (π : G → G) (k₀ k₁ x : G) : G :=
  π (x + k₀) + k₁

/-- Even–Mansour decryption: remove post-whitening key `k₁`, apply the inverse permutation `π_inv`,
and remove pre-whitening key `k₀`. -/
def evenMansourDecrypt (π_inv : G → G) (k₀ k₁ y : G) : G :=
  π_inv (y - k₁) - k₀

/-- Decryption inverts encryption whenever `π_inv` is a left inverse of `π`. -/
@[simp] theorem evenMansourDecrypt_evenMansourEncrypt {π π_inv : G → G}
    (h : Function.LeftInverse π_inv π) (k₀ k₁ x : G) :
    evenMansourDecrypt π_inv k₀ k₁ (evenMansourEncrypt π k₀ k₁ x) = x := by
  simp [evenMansourEncrypt, evenMansourDecrypt, h (x + k₀)]

/-- Encryption inverts decryption whenever `π_inv` is a right inverse of `π`. -/
@[simp] theorem evenMansourEncrypt_evenMansourDecrypt {π π_inv : G → G}
    (h : Function.RightInverse π_inv π) (k₀ k₁ y : G) :
    evenMansourEncrypt π k₀ k₁ (evenMansourDecrypt π_inv k₀ k₁ y) = y := by
  simp [evenMansourEncrypt, evenMansourDecrypt, h (y - k₁)]

/-- The Even–Mansour cipher bundled as a permutation `Equiv.Perm G`. -/
def evenMansourEquiv (π : Equiv.Perm G) (k₀ k₁ : G) : Equiv.Perm G where
  toFun := evenMansourEncrypt π k₀ k₁
  invFun := evenMansourDecrypt π.symm k₀ k₁
  left_inv := evenMansourDecrypt_evenMansourEncrypt π.left_inv k₀ k₁
  right_inv := evenMansourEncrypt_evenMansourDecrypt π.right_inv k₀ k₁

@[simp] theorem evenMansourEquiv_apply (π : Equiv.Perm G) (k₀ k₁ x : G) :
    evenMansourEquiv π k₀ k₁ x = π (x + k₀) + k₁ := rfl

@[simp] theorem evenMansourEquiv_symm_apply (π : Equiv.Perm G) (k₀ k₁ y : G) :
    (evenMansourEquiv π k₀ k₁).symm y = π.symm (y - k₁) - k₀ := rfl

/-- With zero whitening keys, the Even–Mansour cipher is the underlying permutation `π`. -/
@[simp] theorem evenMansourEquiv_zero (π : Equiv.Perm G) :
    evenMansourEquiv π 0 0 = π := by
  ext x
  simp

/-- Composing two Even–Mansour wrappers with the same permutation adds the whitening keys. -/
theorem evenMansourEquiv_evenMansourEquiv (π : Equiv.Perm G) (k₀ k₁ k₀' k₁' : G) :
    evenMansourEquiv (evenMansourEquiv π k₀ k₁) k₀' k₁' =
      evenMansourEquiv π (k₀' + k₀) (k₁ + k₁') := by
  ext x
  simp [add_assoc]

/-- The inverse of an Even–Mansour cipher with keys `(k₀, k₁)` and permutation `π` is an
Even–Mansour cipher with keys `(-k₁, -k₀)` and inverse permutation `π.symm`. -/
theorem evenMansourEquiv_symm (π : Equiv.Perm G) (k₀ k₁ : G) :
    (evenMansourEquiv π k₀ k₁).symm = evenMansourEquiv π.symm (-k₁) (-k₀) := by
  ext y
  simp [sub_eq_add_neg]

/-- Single-key Even–Mansour cipher (`k₀ = k₁ = k`, [DunkelmanKellerShamir2012]). -/
abbrev singleKeyEvenMansourEquiv (π : Equiv.Perm G) (k : G) : Equiv.Perm G :=
  evenMansourEquiv π k k

/-- Over a group of exponent two (`∀ x : G, -x = x`), Even–Mansour decryption is encryption under
the inverse permutation with the two keys swapped. -/
theorem evenMansourDecrypt_eq_of_neg_eq_self (hneg : ∀ x : G, -x = x) (π_inv : G → G)
    (k₀ k₁ y : G) :
    evenMansourDecrypt π_inv k₀ k₁ y = evenMansourEncrypt π_inv k₁ k₀ y := by
  simp [evenMansourDecrypt, evenMansourEncrypt, sub_eq_add_neg, hneg]

/-- Over a group of exponent two (`∀ x : G, -x = x`), inverting the Even–Mansour permutation swaps
the pre-whitening and post-whitening keys. -/
theorem evenMansourEquiv_symm_eq_of_neg_eq_self (hneg : ∀ x : G, -x = x) (π : Equiv.Perm G)
    (k₀ k₁ : G) :
    (evenMansourEquiv π k₀ k₁).symm = evenMansourEquiv π.symm k₁ k₀ := by
  rw [evenMansourEquiv_symm, hneg, hneg]

/-- Over `BitString n`, inverting the Even–Mansour permutation swaps `k₀` and `k₁`. -/
theorem evenMansourEquiv_symm_bitString {n : ℕ} (π : Equiv.Perm (BitString n))
    (k₀ k₁ : BitString n) :
    (evenMansourEquiv π k₀ k₁).symm = evenMansourEquiv π.symm k₁ k₀ :=
  evenMansourEquiv_symm_eq_of_neg_eq_self
    (fun x => neg_eq_iff_add_eq_zero.mpr (BitString.add_self x)) π k₀ k₁

/-- For any fixed keys `(k₀, k₁)`, wrapping a permutation `π` in Even–Mansour is a bijection on
`Equiv.Perm G`. -/
def evenMansourPermEquiv (k₀ k₁ : G) : Equiv.Perm (Equiv.Perm G) where
  toFun π := evenMansourEquiv π k₀ k₁
  invFun π := evenMansourEquiv π (-k₀) (-k₁)
  left_inv π := by
    dsimp
    rw [evenMansourEquiv_evenMansourEquiv, neg_add_cancel, add_neg_cancel, evenMansourEquiv_zero]
  right_inv π := by
    dsimp
    rw [evenMansourEquiv_evenMansourEquiv, add_neg_cancel, neg_add_cancel, evenMansourEquiv_zero]

@[simp] theorem evenMansourPermEquiv_apply (k₀ k₁ : G) (π : Equiv.Perm G) :
    evenMansourPermEquiv k₀ k₁ π = evenMansourEquiv π k₀ k₁ := rfl

/-! ### One-query perfect secrecy -/

/-- For any fixed function `π : G → G` and input `x : G`, the map `(k₀, k₁) ↦ (k₀, π(x + k₀) + k₁)`
is a bijection on `G × G`. -/
def oneQueryKeyEquiv (π : G → G) (x : G) : Equiv.Perm (G × G) where
  toFun k := (k.1, evenMansourEncrypt π k.1 k.2 x)
  invFun p := (p.1, -π (x + p.1) + p.2)
  left_inv k := by
    ext <;> simp [evenMansourEncrypt]
  right_inv p := by
    ext <;> simp [evenMansourEncrypt]

/-- **One-query perfect secrecy**: for any fixed `π : G → G` and plaintext `x : G`, under uniform
independent keys `(k₀, k₁)`, the pre-whitening key `k₀` and the ciphertext
`evenMansourEncrypt π k₀ k₁ x` are independent and uniformly distributed on `G × G`. -/
theorem map_prod_evenMansourEncrypt_uniformOfFintype [Fintype G]
    (π : G → G) (x : G) :
    (PMF.uniformOfFintype (G × G)).map (fun k => (k.1, evenMansourEncrypt π k.1 k.2 x)) =
      PMF.uniformOfFintype (G × G) :=
  PMF.uniformOfFintype_map_equiv (oneQueryKeyEquiv π x)

/-- Under uniform independent keys `(k₀, k₁)`, a single Even–Mansour encryption of `x` is uniformly
distributed on `G` for every fixed `π : G → G`. -/
theorem map_evenMansourEncrypt_uniformOfFintype [Fintype G]
    (π : G → G) (x : G) :
    (PMF.uniformOfFintype (G × G)).map (fun k => evenMansourEncrypt π k.1 k.2 x) =
      PMF.uniformOfFintype G := by
  simpa [PMF.map_comp, Function.comp_def, PMF.uniformOfFintype_prod_map_snd] using
    congrArg (PMF.map Prod.snd) (map_prod_evenMansourEncrypt_uniformOfFintype π x)

/-! ### Necessity of both whitening keys (algebraic recovery) -/

/-- Even–Mansour with pre-whitening only (`k₁ = 0`): `E(k₀, x) = π(x + k₀)`
([BonehShoup2023], Section 4.7). -/
abbrev preWhitenEquiv (π : Equiv.Perm G) (k₀ : G) : Equiv.Perm G :=
  evenMansourEquiv π k₀ 0

/-- Even–Mansour with post-whitening only (`k₀ = 0`): `E(k₁, x) = π(x) + k₁`
([BonehShoup2023], Section 4.7). -/
abbrev postWhitenEquiv (π : Equiv.Perm G) (k₁ : G) : Equiv.Perm G :=
  evenMansourEquiv π 0 k₁

/-- Key recovery for `preWhitenEquiv`: given `y = E(k₀, x)` and `u = π⁻¹(y)`, recover
`k₀ = -x + u`. -/
def preWhitenKeyRecovery (pi_inv_enc_x x : G) : G :=
  -x + pi_inv_enc_x

/-- A single encryption query `y = preWhitenEquiv π k₀ x` and inverse permutation query `π.symm y`
recover `k₀` deterministically. -/
theorem preWhitenKeyRecovery_spec (π : Equiv.Perm G) (k₀ x : G) :
    preWhitenKeyRecovery (π.symm (preWhitenEquiv π k₀ x)) x = k₀ := by
  simp [preWhitenKeyRecovery, preWhitenEquiv]

/-- Key recovery for `postWhitenEquiv`: given `y = E(k₁, x)` and `v = π(x)`, recover
`k₁ = -v + y`. -/
def postWhitenKeyRecovery (enc_x pi_x : G) : G :=
  -pi_x + enc_x

/-- A single encryption query `y = postWhitenEquiv π k₁ x` and forward permutation query `π x`
recover `k₁` deterministically. -/
theorem postWhitenKeyRecovery_spec (π : Equiv.Perm G) (k₁ x : G) :
    postWhitenKeyRecovery (postWhitenEquiv π k₁ x) (π x) = k₁ := by
  simp [postWhitenKeyRecovery, postWhitenEquiv]

end Algebraic

/-! ### Bidirectional ideal-permutation oracle interface and games -/

/-- The combined oracle interface in the Even–Mansour security experiment ([BonehShoup2023],
Section 4.7): left queries (`.inl`) call the cipher permutation `E` and right queries (`.inr`)
call the public primitive permutation `π`. -/
abbrev EvenMansourSpec (G : Type) : OracleSpec (PermQuery G ⊕ PermQuery G) :=
  PermOracleSpec G ⊕ₒ PermOracleSpec G

/-- Cost function counting cipher oracle calls (`1` for `.inl`, `0` for `.inr`). -/
def cipherCost {G : Type} : PermQuery G ⊕ PermQuery G → ℕ
  | .inl _ => 1
  | .inr _ => 0

/-- Cost function counting primitive permutation oracle calls (`0` for `.inl`, `1` for `.inr`). -/
def permCost {G : Type} : PermQuery G ⊕ PermQuery G → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- An adversary `program` makes at most `Q_e` cipher queries and at most `Q_π` primitive
permutation queries on every execution path. -/
def IsCallBounded {G α : Type} (program : OracleComp (EvenMansourSpec G) α) (Q_e Q_π : ℕ) :
    Prop :=
  IsCostBounded cipherCost program Q_e ∧ IsCostBounded permCost program Q_π

/-- A program making at most `Q_e` cipher queries and `Q_π` primitive queries makes at most
`Q_e + Q_π` total queries. -/
theorem IsCallBounded.isQueryBounded {G α : Type} {program : OracleComp (EvenMansourSpec G) α}
    {Q_e Q_π : ℕ} (h : IsCallBounded program Q_e Q_π) :
    IsQueryBounded program (Q_e + Q_π) :=
  (h.1.add h.2).of_le fun q => by cases q <;> simp [cipherCost, permCost]

/-- Query the cipher permutation in the forward direction (`x ↦ E(x)`). -/
def queryCipherForward {G : Type} (x : G) : OracleComp (EvenMansourSpec G) G :=
  liftLeft (query (spec := PermOracleSpec G) (.forward x))

/-- Query the cipher permutation in the inverse direction (`y ↦ E⁻¹(y)`). -/
def queryCipherInverse {G : Type} (y : G) : OracleComp (EvenMansourSpec G) G :=
  liftLeft (query (spec := PermOracleSpec G) (.inverse y))

/-- Query the public primitive permutation in the forward direction (`u ↦ π(u)`). -/
def queryPermForward {G : Type} (u : G) : OracleComp (EvenMansourSpec G) G :=
  liftRight (query (spec := PermOracleSpec G) (.forward u))

/-- Query the public primitive permutation in the inverse direction (`v ↦ π⁻¹(v)`). -/
def queryPermInverse {G : Type} (v : G) : OracleComp (EvenMansourSpec G) G :=
  liftRight (query (spec := PermOracleSpec G) (.inverse v))

theorem isCallBounded_queryCipherForward {G : Type} (x : G) :
    IsCallBounded (queryCipherForward x) 1 0 :=
  ⟨IsCostBounded.query (spec := EvenMansourSpec G) (Sum.inl (.forward x)),
    IsCostBounded.query (spec := EvenMansourSpec G) (Sum.inl (.forward x))⟩

theorem isCallBounded_queryCipherInverse {G : Type} (y : G) :
    IsCallBounded (queryCipherInverse y) 1 0 :=
  ⟨IsCostBounded.query (spec := EvenMansourSpec G) (Sum.inl (.inverse y)),
    IsCostBounded.query (spec := EvenMansourSpec G) (Sum.inl (.inverse y))⟩

theorem isCallBounded_queryPermForward {G : Type} (u : G) :
    IsCallBounded (queryPermForward u) 0 1 :=
  ⟨IsCostBounded.query (spec := EvenMansourSpec G) (Sum.inr (.forward u)),
    IsCostBounded.query (spec := EvenMansourSpec G) (Sum.inr (.forward u))⟩

theorem isCallBounded_queryPermInverse {G : Type} (v : G) :
    IsCallBounded (queryPermInverse v) 0 1 :=
  ⟨IsCostBounded.query (spec := EvenMansourSpec G) (Sum.inr (.inverse v)),
    IsCostBounded.query (spec := EvenMansourSpec G) (Sum.inr (.inverse v))⟩

/-- Deterministically evaluate a program against cipher permutation `E` and primitive permutation
`π`. -/
def evalTwoPerms {G α : Type} (E π : Equiv.Perm G)
    (program : OracleComp (EvenMansourSpec G) α) : α :=
  (interpret (sumHandler (fun q => (evalPerm E q : Id G)) (fun q => (evalPerm π q : Id G)))
    program).run

@[simp] theorem evalTwoPerms_pure {G α : Type} (E π : Equiv.Perm G) (a : α) :
    evalTwoPerms E π (pure a) = a := rfl

@[simp] theorem evalTwoPerms_map {G α β : Type} (E π : Equiv.Perm G)
    (f : α → β) (program : OracleComp (EvenMansourSpec G) α) :
    evalTwoPerms E π (f <$> program) = f (evalTwoPerms E π program) := by
  simp [evalTwoPerms]

@[simp] theorem evalTwoPerms_bind {G α β : Type} (E π : Equiv.Perm G)
    (program : OracleComp (EvenMansourSpec G) α)
    (next : α → OracleComp (EvenMansourSpec G) β) :
    evalTwoPerms E π (program >>= next) =
      evalTwoPerms E π (next (evalTwoPerms E π program)) := by
  simp [evalTwoPerms]

@[simp] theorem evalTwoPerms_queryCipherForward {G : Type} (E π : Equiv.Perm G) (x : G) :
    evalTwoPerms E π (queryCipherForward x) = E x := rfl

@[simp] theorem evalTwoPerms_queryCipherInverse {G : Type} (E π : Equiv.Perm G) (y : G) :
    evalTwoPerms E π (queryCipherInverse y) = E.symm y := rfl

@[simp] theorem evalTwoPerms_queryPermForward {G : Type} (E π : Equiv.Perm G) (u : G) :
    evalTwoPerms E π (queryPermForward u) = π u := rfl

@[simp] theorem evalTwoPerms_queryPermInverse {G : Type} (E π : Equiv.Perm G) (v : G) :
    evalTwoPerms E π (queryPermInverse v) = π.symm v := rfl

theorem evalTwoPerms_liftLeft {G α : Type} (E π π' : Equiv.Perm G)
    (program : OracleComp (PermOracleSpec G) α) :
    evalTwoPerms E π (liftLeft program) = evalTwoPerms E π' (liftLeft program) := by
  simp [evalTwoPerms]

theorem evalTwoPerms_liftRight {G α : Type} (E E' π : Equiv.Perm G)
    (program : OracleComp (PermOracleSpec G) α) :
    evalTwoPerms E π (liftRight program) = evalTwoPerms E' π (liftRight program) := by
  simp [evalTwoPerms]

/-- Deterministically evaluate a program in the real Even–Mansour world with public permutation `π`
and keys `(k₀, k₁)`. -/
def evalEvenMansour {G α : Type} [AddGroup G] (π : Equiv.Perm G) (k₀ k₁ : G)
    (program : OracleComp (EvenMansourSpec G) α) : α :=
  evalTwoPerms (evenMansourEquiv π k₀ k₁) π program

section Attacks

variable {G : Type} [AddGroup G]

omit [AddGroup G] in
private theorem isCallBounded_twoStepAttack {q₁ : OracleComp (EvenMansourSpec G) G}
    {q₂ : G → OracleComp (EvenMansourSpec G) G} (f : G → G → G)
    (hq₁ : IsCallBounded q₁ 1 0) (hq₂ : ∀ y, IsCallBounded (q₂ y) 0 1) :
    IsCallBounded (do let y ← q₁; let u ← q₂ y; return f y u) 1 1 :=
  ⟨by simpa using hq₁.1.bind fun y => (hq₂ y).1.bind fun _ => IsCostBounded.pure _ 0,
   by simpa using hq₁.2.bind fun y => (hq₂ y).2.bind fun _ => IsCostBounded.pure _ 0⟩

/-- Oracle attack recovering `k₀` from `preWhitenEquiv π k₀` in `1` cipher query and `1` primitive
query: query `y ← E(x)` and `u ← π⁻¹(y)`, then return `-x + u`. -/
def preWhitenKeyRecoveryAttack (x : G) : OracleComp (EvenMansourSpec G) G := do
  let y ← queryCipherForward x
  let u ← queryPermInverse y
  return preWhitenKeyRecovery u x

/-- `preWhitenKeyRecoveryAttack x` makes at most `1` cipher query and `1` primitive query. -/
theorem isCallBounded_preWhitenKeyRecoveryAttack (x : G) :
    IsCallBounded (preWhitenKeyRecoveryAttack x) 1 1 :=
  isCallBounded_twoStepAttack (fun _ u => preWhitenKeyRecovery u x)
    (isCallBounded_queryCipherForward x) isCallBounded_queryPermInverse

/-- Against `preWhitenEquiv π k₀` and `π`, `preWhitenKeyRecoveryAttack x` deterministically returns
`k₀`. -/
@[simp] theorem evalTwoPerms_preWhitenKeyRecoveryAttack (π : Equiv.Perm G) (k₀ x : G) :
    evalTwoPerms (preWhitenEquiv π k₀) π (preWhitenKeyRecoveryAttack x) = k₀ := by
  simp [preWhitenKeyRecoveryAttack, preWhitenKeyRecovery]

/-- Oracle attack recovering `k₁` from `postWhitenEquiv π k₁` in `1` cipher query and `1` primitive
query: query `y ← E(x)` and `v ← π(x)`, then return `-v + y`. -/
def postWhitenKeyRecoveryAttack (x : G) : OracleComp (EvenMansourSpec G) G := do
  let y ← queryCipherForward x
  let v ← queryPermForward x
  return postWhitenKeyRecovery y v

/-- `postWhitenKeyRecoveryAttack x` makes at most `1` cipher query and `1` primitive query. -/
theorem isCallBounded_postWhitenKeyRecoveryAttack (x : G) :
    IsCallBounded (postWhitenKeyRecoveryAttack x) 1 1 :=
  isCallBounded_twoStepAttack postWhitenKeyRecovery
    (isCallBounded_queryCipherForward x) (fun _ => isCallBounded_queryPermForward x)

/-- Against `postWhitenEquiv π k₁` and `π`, `postWhitenKeyRecoveryAttack x` deterministically
returns `k₁`. -/
@[simp] theorem evalTwoPerms_postWhitenKeyRecoveryAttack (π : Equiv.Perm G) (k₁ x : G) :
    evalTwoPerms (postWhitenEquiv π k₁) π (postWhitenKeyRecoveryAttack x) = k₁ := by
  simp [postWhitenKeyRecoveryAttack, postWhitenKeyRecovery]

end Attacks

section Games

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]

/-- The real Even–Mansour security experiment ([BonehShoup2023], Section 4.7) for a deterministic
(coin-free) distinguisher `program : OracleComp (EvenMansourSpec G) Bool` (see
`evenMansourProbRealGame` for randomized distinguishers): sample a uniform permutation
`π ← Equiv.Perm G` and uniform independent keys `(k₀, k₁) ← G × G`, and run `program` against
`evenMansourEquiv π k₀ k₁` and `π`. -/
noncomputable def evenMansourRealGame (program : OracleComp (EvenMansourSpec G) Bool) : Game := do
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  let k ← PMF.uniformOfFintype (G × G)
  return evalEvenMansour π k.1 k.2 program

/-- The single-key Even–Mansour security experiment ([DunkelmanKellerShamir2012]) for a
deterministic (coin-free) distinguisher `program : OracleComp (EvenMansourSpec G) Bool` (see
`singleKeyEvenMansourProbRealGame` for randomized distinguishers): sample a uniform permutation
`π ← Equiv.Perm G` and a single uniform key `k ← G`, and run `program` against
`singleKeyEvenMansourEquiv π k` and `π`. -/
noncomputable def singleKeyEvenMansourRealGame
    (program : OracleComp (EvenMansourSpec G) Bool) : Game := do
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  let k ← PMF.uniformOfFintype G
  return evalEvenMansour π k k program

/-- The ideal Even–Mansour security experiment for a deterministic (coin-free) distinguisher
`program : OracleComp (EvenMansourSpec G) Bool` (see `evenMansourProbIdealGame` for randomized
distinguishers): sample two independent uniform permutations `E, π ← Equiv.Perm G` and run
`program` against `E` and `π`. -/
noncomputable def evenMansourIdealGame (program : OracleComp (EvenMansourSpec G) Bool) : Game := do
  let E ← PMF.uniformOfFintype (Equiv.Perm G)
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  return evalTwoPerms E π program

/-- Lazy bidirectional two-permutation handler for `evenMansourIdealGame`: left (cipher) queries
are answered lazily from `cache_e` and right (primitive permutation) queries are answered lazily
from `cache_π` via `RandomPermutation.answer`. -/
noncomputable def idealLazyHandler (q : PermQuery G ⊕ PermQuery G) :
    StateT (RandomPermutation.Cache G × RandomPermutation.Cache G) PMF (EvenMansourSpec G q) :=
  fun (cache_e, cache_π) =>
    match q with
    | .inl qe =>
      (RandomPermutation.answer qe cache_e).map fun (y, cache_e') => (y, (cache_e', cache_π))
    | .inr qπ =>
      (RandomPermutation.answer qπ cache_π).map fun (v, cache_π') => (v, (cache_e, cache_π'))

omit [AddGroup G] in
private theorem mem_support_idealLazyHandler_inl {qe : PermQuery G}
    {c_e c_π c_e' c_π' : RandomPermutation.Cache G} {a : G} :
    (a, c_e', c_π') ∈ (idealLazyHandler (.inl qe) (c_e, c_π)).support ↔
      (a, c_e') ∈ (RandomPermutation.answer qe c_e).support ∧ c_π' = c_π := by
  simp only [idealLazyHandler, PMF.mem_support_map_iff, Prod.mk.injEq, Prod.exists]
  exact ⟨fun ⟨a', c', hmem, h1, h2, h3⟩ => h1 ▸ h2 ▸ h3 ▸ ⟨hmem, rfl⟩,
    fun ⟨hmem, hπ⟩ => ⟨a, c_e', hmem, rfl, rfl, hπ.symm⟩⟩

omit [AddGroup G] in
private theorem mem_support_idealLazyHandler_inr {qπ : PermQuery G}
    {c_e c_π c_e' c_π' : RandomPermutation.Cache G} {a : G} :
    (a, c_e', c_π') ∈ (idealLazyHandler (.inr qπ) (c_e, c_π)).support ↔
      (a, c_π') ∈ (RandomPermutation.answer qπ c_π).support ∧ c_e' = c_e := by
  simp only [idealLazyHandler, PMF.mem_support_map_iff, Prod.mk.injEq, Prod.exists]
  exact ⟨fun ⟨a', c', hmem, h1, h2, h3⟩ => h1 ▸ h2 ▸ h3 ▸ ⟨hmem, rfl⟩,
    fun ⟨hmem, he⟩ => ⟨a, c_π', hmem, rfl, he.symm, rfl⟩⟩

omit [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] in
/-- Lifting deterministic `evalTwoPerms E π program` into `PMF.pure` equals interpreting `program`
against deterministic `PMF.pure ∘ evalPerm` handlers. -/
theorem pure_evalTwoPerms {α : Type} (E π : Equiv.Perm G)
    (program : OracleComp (EvenMansourSpec G) α) :
    (PMF.pure (evalTwoPerms E π program) : PMF α) =
      OracleComp.interpret
        (sumHandler (fun q => PMF.pure (evalPerm E q)) (fun q => PMF.pure (evalPerm π q)))
        program := by
  induction program with
  | pure a => rfl
  | liftBind q cont ih =>
    change PMF.pure (evalTwoPerms E π (OracleComp.query q >>= cont)) =
      OracleComp.interpret
        (sumHandler (fun q => PMF.pure (evalPerm E q)) (fun q => PMF.pure (evalPerm π q)))
        (OracleComp.query q >>= cont)
    cases q <;>
      · simp only [evalTwoPerms, interp_norm, pmf_norm, Id.run_bind]
        exact ih _

omit [AddGroup G] in
/-- **Ideal Even–Mansour game equals lazy bidirectional two-permutation sampling**: sampling two
independent uniform permutations `E, π ← PMF.uniformOfFintype (Equiv.Perm G)` has the exact same
output distribution as running `idealLazyHandler` from `([], [])`. -/
theorem evenMansourIdealGame_eq_lazy (program : OracleComp (EvenMansourSpec G) Bool) :
    evenMansourIdealGame program =
      (((OracleComp.interpret idealLazyHandler program).run ([], [])).map Prod.fst) := by
  let sim (st : RandomPermutation.Cache G × RandomPermutation.Cache G) :
      PMF (Equiv.Perm G × Equiv.Perm G) :=
    (RandomPermutation.complete st.1).bind fun E => (RandomPermutation.complete st.2).map (E, ·)
  let inv (st : RandomPermutation.Cache G × RandomPermutation.Cache G) : Prop :=
    RandomPermutation.IsPartialBijection st.1 ∧ RandomPermutation.IsPartialBijection st.2
  let readH (q : PermQuery G ⊕ PermQuery G) (p : Equiv.Perm G × Equiv.Perm G) :
      PMF (EvenMansourSpec G q) :=
    sumHandler (fun q => PMF.pure (evalPerm p.1 q)) (fun q => PMF.pure (evalPerm p.2 q)) q
  have hpres : ∀ q st, inv st →
      ∀ a st', (a, st') ∈ (idealLazyHandler q st).support → inv st' := by
    rintro (qe | qπ) ⟨c_e, c_π⟩ ⟨he, hπ⟩ a ⟨c_e', c_π'⟩ hmem
    · obtain ⟨hmem₀, rfl⟩ := mem_support_idealLazyHandler_inl.mp hmem
      exact ⟨RandomPermutation.answer_preserve_isPartialBijection qe c_e he a c_e' hmem₀, hπ⟩
    · obtain ⟨hmem₀, rfl⟩ := mem_support_idealLazyHandler_inr.mp hmem
      exact ⟨he, RandomPermutation.answer_preserve_isPartialBijection qπ c_π hπ a c_π' hmem₀⟩
  have hstep : ∀ q st, inv st →
      (do let (a, st') ← idealLazyHandler q st; (a, ·) <$> sim st') =
      (do let p ← sim st; let y ← (·, p) <$> readH q p; pure y) := by
    rintro (qe | qπ) ⟨c_e, c_π⟩ ⟨he, hπ⟩
    · have h1 := congrArg
        (fun m : PMF (G × Equiv.Perm G) =>
          m.bind fun (y, E) => (RandomPermutation.complete c_π).map fun π => (y, (E, π)))
        (RandomPermutation.answer_complete qe c_e he)
      simpa only [pmf_norm, idealLazyHandler, sim, readH, sumHandler, PMF.map] using h1
    · have h2 := congrArg
        (fun m : PMF (G × Equiv.Perm G) =>
          (RandomPermutation.complete c_e).bind fun E =>
            m.map fun (v, π) => (v, (E, π)))
        (RandomPermutation.answer_complete qπ c_π hπ)
      simp only [pmf_norm, idealLazyHandler, sim, readH, sumHandler, PMF.map] at h2 ⊢
      rw [← h2]
      pmf_swap
  have hsim := OracleComp.run_interpret_simulation_of_invariant idealLazyHandler
    (fun q p => (·, p) <$> readH q p) sim inv hpres hstep program ([], [])
    ⟨RandomPermutation.isPartialBijection_nil, RandomPermutation.isPartialBijection_nil⟩
  have hsim' := congrArg (PMF.map Prod.fst) hsim
  simp only [pmf_norm, sim, RandomPermutation.complete_nil, PMF.map, PMF.bind_const] at hsim'
  refine Eq.trans ?_ hsim'.symm
  simp only [evenMansourIdealGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  refine congrArg ((PMF.uniformOfFintype (Equiv.Perm G)).bind) (funext fun E => ?_)
  refine congrArg ((PMF.uniformOfFintype (Equiv.Perm G)).bind) (funext fun π => ?_)
  rw [pure_evalTwoPerms]
  simpa only [pmf_norm, readH, PMF.map] using
    (congrArg (PMF.map Prod.fst) (OracleComp.run_interpret_readOnly readH program (E, π))).symm

/-- For any adversary `program` that queries only the cipher oracle (`liftLeft program`), the real
Even–Mansour game is identically distributed to the ideal game. -/
theorem evenMansourRealGame_liftLeft_eq_ideal (program : OracleComp (PermOracleSpec G) Bool) :
    evenMansourRealGame (liftLeft program) = evenMansourIdealGame (liftLeft program) := by
  simp only [evenMansourRealGame, evenMansourIdealGame, evalEvenMansour, pmf_norm]
  simp_rw [evalTwoPerms_liftLeft _ _ (1 : Equiv.Perm G) program]
  pmf_hoist (PMF.uniformOfFintype (G × G))
  drop_uniform with k
  relabel_uniform (evenMansourPermEquiv k.1 k.2)

/-- Any adversary that queries only the cipher oracle (`liftLeft`) has zero advantage between the
real Even–Mansour game and the ideal game. -/
@[simp] theorem advantage_evenMansourRealGame_liftLeft_eq_zero
    (program : OracleComp (PermOracleSpec G) Bool) :
    Game.advantage (evenMansourRealGame (liftLeft program))
      (evenMansourIdealGame (liftLeft program)) = 0 := by
  rw [evenMansourRealGame_liftLeft_eq_ideal, Game.advantage_self]

/-- For any adversary `program` that queries only the primitive permutation oracle
(`liftRight program`), the real Even–Mansour game is identically distributed to the ideal game. -/
theorem evenMansourRealGame_liftRight_eq_ideal (program : OracleComp (PermOracleSpec G) Bool) :
    evenMansourRealGame (liftRight program) = evenMansourIdealGame (liftRight program) := by
  simp only [evenMansourRealGame, evenMansourIdealGame, evalEvenMansour, pmf_norm]
  simp_rw [evalTwoPerms_liftRight _ (1 : Equiv.Perm G) _ program, PMF.bind_const]

/-- Any adversary that queries only the primitive permutation oracle (`liftRight`) has zero
advantage between the real Even–Mansour game and the ideal game. -/
@[simp] theorem advantage_evenMansourRealGame_liftRight_eq_zero
    (program : OracleComp (PermOracleSpec G) Bool) :
    Game.advantage (evenMansourRealGame (liftRight program))
      (evenMansourIdealGame (liftRight program)) = 0 := by
  rw [evenMansourRealGame_liftRight_eq_ideal, Game.advantage_self]

/-! ### 2-query oracle attacks when either whitening key is omitted -/

/-- Key-recovery game for pre-whitening-only Even–Mansour: draw `π ← Equiv.Perm G` and
`k₀ ← G`, run `preWhitenKeyRecoveryAttack x` against `preWhitenEquiv π k₀` and `π`, and test
whether it outputs `k₀`. -/
noncomputable def preWhitenKeyRecoveryRealGame (x : G) : Game := do
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  let k₀ ← PMF.uniformOfFintype G
  return decide (evalTwoPerms (preWhitenEquiv π k₀) π (preWhitenKeyRecoveryAttack x) = k₀)

/-- Ideal comparison game for `preWhitenKeyRecoveryAttack`: draw independent uniform permutations
`E, π ← Equiv.Perm G` and a uniform target key `k₀ ← G`, and test whether
`preWhitenKeyRecoveryAttack x` outputs `k₀`. -/
noncomputable def preWhitenKeyRecoveryIdealGame (x : G) : Game := do
  let E ← PMF.uniformOfFintype (Equiv.Perm G)
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  let k₀ ← PMF.uniformOfFintype G
  return decide (evalTwoPerms E π (preWhitenKeyRecoveryAttack x) = k₀)

/-- In the real pre-whitened game, `preWhitenKeyRecoveryAttack x` succeeds with probability `1`. -/
@[simp] theorem preWhitenKeyRecoveryRealGame_eq_pure_true (x : G) :
    preWhitenKeyRecoveryRealGame x = PMF.pure true := by
  simp [preWhitenKeyRecoveryRealGame, PMF.bind_const]

/-- In the ideal game, `preWhitenKeyRecoveryAttack x` outputs the uniform target `k₀` with
probability `|G|⁻¹`. -/
theorem preWhitenKeyRecoveryIdealGame_true_toReal (x : G) :
    (preWhitenKeyRecoveryIdealGame x true).toReal = (Fintype.card G : ℝ)⁻¹ := by
  simp only [preWhitenKeyRecoveryIdealGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rw [PMF.bind_apply_of_forall _ fun E => PMF.bind_apply_of_forall _ fun π =>
      PMF.uniformOfFintype_bind_decide_eq_apply_true _,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- **2-query break of pre-whitening-only Even–Mansour** ([BonehShoup2023], Section 4.7):
omitting post-whitening (`k₁ = 0`) allows a 2-query attack (`1` cipher query + `1` primitive query)
to achieve key-recovery game advantage `1 - |G|⁻¹`. -/
theorem advantage_preWhitenKeyRecoveryGame_eq (x : G) :
    (Game.advantage (preWhitenKeyRecoveryRealGame x) (preWhitenKeyRecoveryIdealGame x) : ℝ) =
      1 - (Fintype.card G : ℝ)⁻¹ := by
  rw [preWhitenKeyRecoveryRealGame_eq_pure_true, Game.coe_advantage_pure_true_left,
    preWhitenKeyRecoveryIdealGame_true_toReal]

/-- Key-recovery game for post-whitening-only Even–Mansour: draw `π ← Equiv.Perm G` and
`k₁ ← G`, run `postWhitenKeyRecoveryAttack x` against `postWhitenEquiv π k₁` and `π`, and test
whether it outputs `k₁`. -/
noncomputable def postWhitenKeyRecoveryRealGame (x : G) : Game := do
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  let k₁ ← PMF.uniformOfFintype G
  return decide (evalTwoPerms (postWhitenEquiv π k₁) π (postWhitenKeyRecoveryAttack x) = k₁)

/-- Ideal comparison game for `postWhitenKeyRecoveryAttack`: draw independent uniform permutations
`E, π ← Equiv.Perm G` and a uniform target key `k₁ ← G`, and test whether
`postWhitenKeyRecoveryAttack x` outputs `k₁`. -/
noncomputable def postWhitenKeyRecoveryIdealGame (x : G) : Game := do
  let E ← PMF.uniformOfFintype (Equiv.Perm G)
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  let k₁ ← PMF.uniformOfFintype G
  return decide (evalTwoPerms E π (postWhitenKeyRecoveryAttack x) = k₁)

/-- In the real post-whitened game, `postWhitenKeyRecoveryAttack x` succeeds with probability
`1`. -/
@[simp] theorem postWhitenKeyRecoveryRealGame_eq_pure_true (x : G) :
    postWhitenKeyRecoveryRealGame x = PMF.pure true := by
  simp [postWhitenKeyRecoveryRealGame, PMF.bind_const]

/-- In the ideal game, `postWhitenKeyRecoveryAttack x` outputs the uniform target `k₁` with
probability `|G|⁻¹`. -/
theorem postWhitenKeyRecoveryIdealGame_true_toReal (x : G) :
    (postWhitenKeyRecoveryIdealGame x true).toReal = (Fintype.card G : ℝ)⁻¹ := by
  simp only [postWhitenKeyRecoveryIdealGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rw [PMF.bind_apply_of_forall _ fun E => PMF.bind_apply_of_forall _ fun π =>
      PMF.uniformOfFintype_bind_decide_eq_apply_true _,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- **2-query break of post-whitening-only Even–Mansour** ([BonehShoup2023], Section 4.7):
omitting pre-whitening (`k₀ = 0`) allows a 2-query attack (`1` cipher query + `1` primitive query)
to achieve key-recovery game advantage `1 - |G|⁻¹`. -/
theorem advantage_postWhitenKeyRecoveryGame_eq (x : G) :
    (Game.advantage (postWhitenKeyRecoveryRealGame x) (postWhitenKeyRecoveryIdealGame x) : ℝ) =
      1 - (Fintype.card G : ℝ)⁻¹ := by
  rw [postWhitenKeyRecoveryRealGame_eq_pure_true, Game.coe_advantage_pure_true_left,
    postWhitenKeyRecoveryIdealGame_true_toReal]

end Games

/-! ### Bad-key transcript intersection analysis (Boneh–Shoup Theorem 4.14) -/

section BadKeys

variable {G : Type} [AddGroup G] [DecidableEq G]

/-- A key pair `k = (k₀, k₁)` is bad for a cipher input-output pair `e = (x, y)` and a primitive
permutation input-output pair `p = (u, v)` if the internal permutation input `x + k₀` collides with
`u` or the internal permutation output `y - k₁` collides with `v`
([BonehShoup2023], Section 4.7, Theorem 4.14). -/
def isBadKeyPair (e p : G × G) (k : G × G) : Bool :=
  decide (e.1 + k.1 = p.1) || decide (e.2 - k.2 = p.2)

/-- A key pair `k = (k₀, k₁)` is bad for a cipher transcript `T_e : List (G × G)` and a primitive
permutation transcript `T_π : List (G × G)` if some `e ∈ T_e` and `p ∈ T_π` collide on the
internal permutation input or output ([BonehShoup2023], Section 4.7, Theorem 4.14). -/
def isBadEvenMansourKey (T_e T_π : List (G × G)) (k : G × G) : Bool :=
  T_e.any fun e => T_π.any fun p => isBadKeyPair e p k

/-- Single-key specialization (`k₀ = k₁ = k`, [DunkelmanKellerShamir2012]) of the Even–Mansour
bad-key predicate. -/
def isBadSingleKeyEvenMansour (T_e T_π : List (G × G)) (k : G) : Bool :=
  isBadEvenMansourKey T_e T_π (k, k)

/-- Input-only bad-key predicate (`x + k₀ = u` for some `(x, y) ∈ T_e` and `(u, v) ∈ T_π`), which
captures all collisions in the real Even–Mansour world where `y = π(x + k₀) + k₁` and
`v = π(u)`. -/
def isBadInputKey (T_e T_π : List (G × G)) (k₀ : G) : Bool :=
  T_e.any fun e => T_π.any fun p => decide (e.1 + k₀ = p.1)

@[simp] theorem isBadKeyPair_eq_true_iff (e p k : G × G) :
    isBadKeyPair e p k = true ↔ e.1 + k.1 = p.1 ∨ e.2 - k.2 = p.2 := by
  simp [isBadKeyPair]

@[simp] theorem isBadEvenMansourKey_eq_true_iff (T_e T_π : List (G × G)) (k : G × G) :
    isBadEvenMansourKey T_e T_π k = true ↔
      ∃ e ∈ T_e, ∃ p ∈ T_π, e.1 + k.1 = p.1 ∨ e.2 - k.2 = p.2 := by
  simp [isBadEvenMansourKey]

/-- **Domain and range disjointness outside bad keys**: when
`isBadEvenMansourKey T_e T_π k = false`, every cipher pair `(x, y) ∈ T_e` has internal permutation
input `x + k₀` distinct from every primitive query input `u` in `T_π`, and internal permutation
output `y - k₁` distinct from every primitive query output `v` in `T_π`. -/
theorem disjoint_of_isBadEvenMansourKey_eq_false {T_e T_π : List (G × G)} {k : G × G}
    (hgood : isBadEvenMansourKey T_e T_π k = false) {e p : G × G}
    (he : e ∈ T_e) (hp : p ∈ T_π) :
    e.1 + k.1 ≠ p.1 ∧ e.2 - k.2 ≠ p.2 := by
  have hnot : ¬isBadEvenMansourKey T_e T_π k = true := by simp [hgood]
  rw [isBadEvenMansourKey_eq_true_iff] at hnot
  push Not at hnot
  exact hnot e he p hp

omit [DecidableEq G] in
/-- When `e = (x, y)` is consistent with `evenMansourEquiv π k₀ k₁` (`π (x + k₀) + k₁ = y`) and
`p = (u, v)` is consistent with `π` (`π u = v`), an output collision `y - k₁ = v` is equivalent to
an input collision `x + k₀ = u`. -/
theorem input_collision_iff_output_collision (π : Equiv.Perm G) (k : G × G) {e p : G × G}
    (he : evenMansourEquiv π k.1 k.2 e.1 = e.2) (hp : π p.1 = p.2) :
    e.1 + k.1 = p.1 ↔ e.2 - k.2 = p.2 := by
  have he' : e.2 - k.2 = π (e.1 + k.1) := by
    rw [← he, evenMansourEquiv_apply, add_sub_cancel_right]
  rw [he', ← hp, π.injective.eq_iff]

/-- On a pair `(e, p)` consistent with `evenMansourEquiv π k.1 k.2` and `π`, `isBadKeyPair e p k`
reduces to the input collision `decide (e.1 + k.1 = p.1)`. -/
theorem isBadKeyPair_eq_decide_of_evenMansourEquiv (π : Equiv.Perm G) (k : G × G) {e p : G × G}
    (he : evenMansourEquiv π k.1 k.2 e.1 = e.2) (hp : π p.1 = p.2) :
    isBadKeyPair e p k = decide (e.1 + k.1 = p.1) := by
  rw [Bool.eq_iff_iff, isBadKeyPair_eq_true_iff, decide_eq_true_eq,
    ← input_collision_iff_output_collision π k he hp, or_self]

/-- On transcripts `T_e` and `T_π` consistent with `evenMansourEquiv π k.1 k.2` and `π`,
`isBadEvenMansourKey T_e T_π k` equals `isBadInputKey T_e T_π k.1`. -/
theorem isBadEvenMansourKey_eq_isBadInputKey_of_evenMansourEquiv (π : Equiv.Perm G) (k : G × G)
    {T_e T_π : List (G × G)} (hT_e : ∀ e ∈ T_e, evenMansourEquiv π k.1 k.2 e.1 = e.2)
    (hT_π : ∀ p ∈ T_π, π p.1 = p.2) :
    isBadEvenMansourKey T_e T_π k = isBadInputKey T_e T_π k.1 := by
  rw [Bool.eq_iff_iff]
  simp only [isBadEvenMansourKey, isBadInputKey, List.any_eq_true]
  refine exists_congr fun e => and_congr_right fun he => ?_
  refine exists_congr fun p => and_congr_right fun hp => ?_
  rw [isBadKeyPair_eq_decide_of_evenMansourEquiv π k (hT_e e he) (hT_π p hp)]

/-! ### Exact single-pair collision probabilities and multi-query union bounds -/

variable [Fintype G]

omit [DecidableEq G] in
private theorem toOuterMeasure_uniformOfFintype_singleton_pred {p : G → Prop} [DecidablePred p]
    (target : G) (htarget : ∀ k, p k ↔ k = target) :
    (PMF.uniformOfFintype G).toOuterMeasure {k : G | decide (p k) = true} =
      (Fintype.card G : ℝ≥0∞)⁻¹ := by
  rw [show {k : G | decide (p k) = true} = {target} by ext k; simp [htarget k],
    PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply]

/-- Under a uniform key `k₀ ← G`, the probability of an input collision `x + k₀ = u` is exactly
`|G|⁻¹`. -/
private theorem toOuterMeasure_input_collision (x u : G) :
    (PMF.uniformOfFintype G).toOuterMeasure {k₀ : G | decide (x + k₀ = u) = true} =
      (Fintype.card G : ℝ≥0∞)⁻¹ :=
  toOuterMeasure_uniformOfFintype_singleton_pred (-x + u) fun _ =>
    ⟨fun h => by rw [← h, neg_add_cancel_left], fun h => by rw [h, add_neg_cancel_left]⟩

/-- Under a uniform key `k₁ ← G`, the probability of an output collision `y - k₁ = v` is exactly
`|G|⁻¹`. -/
private theorem toOuterMeasure_output_collision (y v : G) :
    (PMF.uniformOfFintype G).toOuterMeasure {k₁ : G | decide (y - k₁ = v) = true} =
      (Fintype.card G : ℝ≥0∞)⁻¹ :=
  toOuterMeasure_uniformOfFintype_singleton_pred (-v + y) fun _ => by
    rw [← neg_inj, neg_sub, sub_eq_iff_eq_add]

/-- Under uniform independent keys `(k₀, k₁) ← G × G`, the probability of an input collision
`e.1 + k.1 = p.1` is `|G|⁻¹`. -/
private theorem toOuterMeasure_prod_input_collision (e p : G × G) :
    (PMF.uniformOfFintype (G × G)).toOuterMeasure {k : G × G | decide (e.1 + k.1 = p.1) = true} =
      (Fintype.card G : ℝ≥0∞)⁻¹ := by
  have hpre : {k : G × G | decide (e.1 + k.1 = p.1) = true} =
      Prod.fst ⁻¹' {k₀ : G | decide (e.1 + k₀ = p.1) = true} := rfl
  rw [hpre, ← PMF.toOuterMeasure_map_apply, PMF.uniformOfFintype_prod_map_fst,
    toOuterMeasure_input_collision]

/-- Under uniform independent keys `(k₀, k₁) ← G × G`, the probability of an output collision
`e.2 - k.2 = p.2` is `|G|⁻¹`. -/
private theorem toOuterMeasure_prod_output_collision (e p : G × G) :
    (PMF.uniformOfFintype (G × G)).toOuterMeasure {k : G × G | decide (e.2 - k.2 = p.2) = true} =
      (Fintype.card G : ℝ≥0∞)⁻¹ := by
  have hpre : {k : G × G | decide (e.2 - k.2 = p.2) = true} =
      Prod.snd ⁻¹' {k₁ : G | decide (e.2 - k₁ = p.2) = true} := rfl
  rw [hpre, ← PMF.toOuterMeasure_map_apply, PMF.uniformOfFintype_prod_map_snd,
    toOuterMeasure_output_collision]

private theorem toOuterMeasure_isBadKeyPair_union_le {K : Type*} (μ : PMF K) (f₁ f₂ : K → G)
    (e p : G × G)
    (h₁ : μ.toOuterMeasure {k | decide (e.1 + f₁ k = p.1) = true} = (Fintype.card G : ℝ≥0∞)⁻¹)
    (h₂ : μ.toOuterMeasure {k | decide (e.2 - f₂ k = p.2) = true} = (Fintype.card G : ℝ≥0∞)⁻¹) :
    μ.toOuterMeasure {k | isBadKeyPair e p (f₁ k, f₂ k) = true} ≤
      2 * (Fintype.card G : ℝ≥0∞)⁻¹ := by
  rw [show {k | isBadKeyPair e p (f₁ k, f₂ k) = true} =
      {k | decide (e.1 + f₁ k = p.1) = true} ∪ {k | decide (e.2 - f₂ k = p.2) = true} by
    ext k; simp only [isBadKeyPair, Bool.or_eq_true, Set.mem_ofPred_eq, Set.mem_union]]
  exact (MeasureTheory.measure_union_le _ _).trans_eq (by rw [h₁, h₂, two_mul])

/-- For a single pair `(e, p)`, a uniform key pair `k ← G × G` satisfies `isBadKeyPair e p k` with
probability at most `2 * |G|⁻¹`. -/
theorem toOuterMeasure_isBadKeyPair_le (e p : G × G) :
    (PMF.uniformOfFintype (G × G)).toOuterMeasure {k | isBadKeyPair e p k = true} ≤
      2 * (Fintype.card G : ℝ≥0∞)⁻¹ :=
  toOuterMeasure_isBadKeyPair_union_le (PMF.uniformOfFintype (G × G)) Prod.fst Prod.snd e p
    (toOuterMeasure_prod_input_collision e p) (toOuterMeasure_prod_output_collision e p)

/-- For a single pair `(e, p)`, a single uniform key `k ← G` satisfies `isBadKeyPair e p (k, k)`
with probability at most `2 * |G|⁻¹`. -/
theorem toOuterMeasure_isBadKeyPair_singleKey_le (e p : G × G) :
    (PMF.uniformOfFintype G).toOuterMeasure {k | isBadKeyPair e p (k, k) = true} ≤
      2 * (Fintype.card G : ℝ≥0∞)⁻¹ :=
  toOuterMeasure_isBadKeyPair_union_le (PMF.uniformOfFintype G) id id e p
    (toOuterMeasure_input_collision e.1 p.1) (toOuterMeasure_output_collision e.2 p.2)

omit [AddGroup G] [DecidableEq G] in
private theorem toOuterMeasure_any_any_le {K : Type*} (μ : PMF K)
    (badPair : G × G → G × G → K → Bool) (c : ℕ)
    (hpair : ∀ e p, μ.toOuterMeasure {k | badPair e p k = true} ≤
      (c : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹)
    (T_e T_π : List (G × G)) :
    μ.toOuterMeasure {k | (T_e.any fun e => T_π.any fun p => badPair e p k) = true} ≤
      (c : ℝ≥0∞) * T_e.length * T_π.length * (Fintype.card G : ℝ≥0∞)⁻¹ := by
  classical
  rw [show {k | (T_e.any fun e => T_π.any fun p => badPair e p k) = true} =
      ⋃ x ∈ T_e.toFinset ×ˢ T_π.toFinset, {k | badPair x.1 x.2 k = true} by
    ext k
    simp only [Set.mem_ofPred_eq, List.any_eq_true, Set.mem_iUnion, Finset.mem_product,
      List.mem_toFinset, Prod.exists, exists_prop]
    exact ⟨fun ⟨a, b, hab, c', d, hcd, h⟩ => ⟨a, b, c', d, ⟨hab, hcd⟩, h⟩,
      fun ⟨a, b, c', d, ⟨hab, hcd⟩, h⟩ => ⟨a, b, hab, c', d, hcd, h⟩⟩]
  calc μ.toOuterMeasure
        (⋃ x ∈ T_e.toFinset ×ˢ T_π.toFinset, {k | badPair x.1 x.2 k = true})
      ≤ ∑ x ∈ T_e.toFinset ×ˢ T_π.toFinset, μ.toOuterMeasure {k | badPair x.1 x.2 k = true} :=
        MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ (T_e.toFinset ×ˢ T_π.toFinset).card • ((c : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹) :=
        Finset.sum_le_card_nsmul _ _ _ fun x _ => hpair x.1 x.2
    _ ≤ (T_e.length : ℝ≥0∞) * T_π.length * ((c : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹) := by
        rw [Finset.card_product, nsmul_eq_mul, Nat.cast_mul]
        gcongr <;> exact List.toFinset_card_le _
    _ = (c : ℝ≥0∞) * T_e.length * T_π.length * (Fintype.card G : ℝ≥0∞)⁻¹ := by ring

omit [DecidableEq G] in
private theorem toOuterMeasure_any_any_toReal_le {K : Type*} (μ : PMF K)
    (badPair : G × G → G × G → K → Bool) (c : ℕ)
    (hpair : ∀ e p, μ.toOuterMeasure {k | badPair e p k = true} ≤
      (c : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹)
    (T_e T_π : List (G × G)) :
    (μ.toOuterMeasure {k | (T_e.any fun e => T_π.any fun p => badPair e p k) = true}).toReal ≤
      (c : ℝ) * (T_e.length : ℝ) * (T_π.length : ℝ) / (Fintype.card G : ℝ) := by
  rw [div_eq_mul_inv]
  ennreal_to_real using toOuterMeasure_any_any_le μ badPair c hpair T_e T_π

/-- **Boneh–Shoup Theorem 4.14 bad-key union bound (`ℝ≥0∞`)**: for any cipher transcript `T_e` and
primitive permutation transcript `T_π`, a uniform key pair `(k₀, k₁) ← G × G` is bad with
probability at most `2 * |T_e| * |T_π| * |G|⁻¹`. -/
theorem toOuterMeasure_isBadEvenMansourKey_le (T_e T_π : List (G × G)) :
    (PMF.uniformOfFintype (G × G)).toOuterMeasure {k | isBadEvenMansourKey T_e T_π k = true} ≤
      2 * T_e.length * T_π.length * (Fintype.card G : ℝ≥0∞)⁻¹ :=
  toOuterMeasure_any_any_le _ isBadKeyPair 2 toOuterMeasure_isBadKeyPair_le T_e T_π

/-- **Boneh–Shoup Theorem 4.14 bad-key union bound (`ℝ`)**: for any cipher transcript `T_e` and
primitive permutation transcript `T_π`, a uniform key pair `(k₀, k₁) ← G × G` is bad with real
probability at most `2 * |T_e| * |T_π| / |G|`. -/
theorem toOuterMeasure_isBadEvenMansourKey_toReal_le (T_e T_π : List (G × G)) :
    ((PMF.uniformOfFintype (G × G)).toOuterMeasure
      {k | isBadEvenMansourKey T_e T_π k = true}).toReal ≤
      2 * (T_e.length : ℝ) * (T_π.length : ℝ) / (Fintype.card G : ℝ) :=
  toOuterMeasure_any_any_toReal_le _ isBadKeyPair 2 toOuterMeasure_isBadKeyPair_le T_e T_π

/-- **Single-key Even–Mansour bad-key union bound (`ℝ≥0∞`, [DunkelmanKellerShamir2012])**: for any
cipher transcript `T_e` and primitive permutation transcript `T_π`, a single uniform key `k ← G` is
bad with probability at most `2 * |T_e| * |T_π| * |G|⁻¹`. -/
theorem toOuterMeasure_isBadSingleKeyEvenMansour_le (T_e T_π : List (G × G)) :
    (PMF.uniformOfFintype G).toOuterMeasure {k | isBadSingleKeyEvenMansour T_e T_π k = true} ≤
      2 * T_e.length * T_π.length * (Fintype.card G : ℝ≥0∞)⁻¹ :=
  toOuterMeasure_any_any_le _ (fun e p k => isBadKeyPair e p (k, k)) 2
    toOuterMeasure_isBadKeyPair_singleKey_le T_e T_π

/-- **Single-key Even–Mansour bad-key union bound (`ℝ`, [DunkelmanKellerShamir2012])**: for any
cipher transcript `T_e` and primitive permutation transcript `T_π`, a single uniform key `k ← G` is
bad with real probability at most `2 * |T_e| * |T_π| / |G|`. -/
theorem toOuterMeasure_isBadSingleKeyEvenMansour_toReal_le (T_e T_π : List (G × G)) :
    ((PMF.uniformOfFintype G).toOuterMeasure
      {k | isBadSingleKeyEvenMansour T_e T_π k = true}).toReal ≤
      2 * (T_e.length : ℝ) * (T_π.length : ℝ) / (Fintype.card G : ℝ) :=
  toOuterMeasure_any_any_toReal_le _ (fun e p k => isBadKeyPair e p (k, k)) 2
    toOuterMeasure_isBadKeyPair_singleKey_le T_e T_π

/-- **Input-collision union bound (`ℝ`)**: for any cipher transcript `T_e` and primitive transcript
`T_π`, a uniform pre-whitening key `k₀ ← G` triggers an input collision `isBadInputKey T_e T_π k₀`
with real probability at most `|T_e| * |T_π| / |G|`. -/
theorem toOuterMeasure_isBadInputKey_toReal_le (T_e T_π : List (G × G)) :
    ((PMF.uniformOfFintype G).toOuterMeasure {k₀ | isBadInputKey T_e T_π k₀ = true}).toReal ≤
      (T_e.length : ℝ) * (T_π.length : ℝ) / (Fintype.card G : ℝ) := by
  simpa only [isBadInputKey, Nat.cast_one, one_mul] using
    toOuterMeasure_any_any_toReal_le _ (fun e p k₀ => decide (e.1 + k₀ = p.1)) 1
      (fun e p => by simpa only [Nat.cast_one, one_mul] using
        (toOuterMeasure_input_collision e.1 p.1).le)
      T_e T_π

end BadKeys

/-! ### Adaptive distinguisher transcript bounds via `IsCallBounded` -/

section TranscriptBounds

/-- Project a logged `EvenMansourSpec G` query-response entry onto its cipher input-output pair
`(x, y)` (turning `.inverse y` with answer `x` into `(x, y)`), or `none` for primitive queries. -/
def transcriptCipherEntry {G : Type}
    (entry : (q : PermQuery G ⊕ PermQuery G) × EvenMansourSpec G q) : Option (G × G) :=
  match entry.1, entry.2 with
  | .inl (.forward x), y => some (x, y)
  | .inl (.inverse y), x => some (x, y)
  | .inr _, _ => none

/-- Project a logged `EvenMansourSpec G` query-response entry onto its primitive permutation
input-output pair `(u, v)` (turning `.inverse v` with answer `u` into `(u, v)`), or `none` for
cipher queries. -/
def transcriptPermEntry {G : Type}
    (entry : (q : PermQuery G ⊕ PermQuery G) × EvenMansourSpec G q) : Option (G × G) :=
  match entry.1, entry.2 with
  | .inl _, _ => none
  | .inr (.forward u), v => some (u, v)
  | .inr (.inverse v), u => some (u, v)

/-- The list of cipher input-output pairs recorded in a bidirectional interaction transcript. -/
def transcriptCipher {G : Type} (T : Transcript (EvenMansourSpec G)) : List (G × G) :=
  T.filterMap transcriptCipherEntry

/-- The list of primitive permutation input-output pairs recorded in a bidirectional interaction
transcript. -/
def transcriptPerm {G : Type} (T : Transcript (EvenMansourSpec G)) : List (G × G) :=
  T.filterMap transcriptPermEntry

private theorem length_filterMap_eq_sum_cost {G : Type}
    (proj : ((q : PermQuery G ⊕ PermQuery G) × EvenMansourSpec G q) → Option (G × G))
    (cost : PermQuery G ⊕ PermQuery G → ℕ)
    (hstep : ∀ entry, (if (proj entry).isSome then 1 else 0) = cost entry.1)
    (T : Transcript (EvenMansourSpec G)) :
    (T.filterMap proj).length = (T.map fun entry => cost entry.1).sum := by
  induction T with
  | nil => rfl
  | cons entry rest ih =>
    rw [List.filterMap_cons, List.map_cons, List.sum_cons, ← hstep entry]
    cases proj entry <;> simpa [Nat.add_comm] using ih

/-- The length of `transcriptCipher T` equals the total `cipherCost` of `T`. -/
@[simp] theorem length_transcriptCipher_eq_sum_cipherCost {G : Type}
    (T : Transcript (EvenMansourSpec G)) :
    (transcriptCipher T).length = (T.map fun entry => cipherCost entry.1).sum :=
  length_filterMap_eq_sum_cost transcriptCipherEntry cipherCost
    (fun ⟨q, _⟩ => by rcases q with (x | y) | (u | v) <;> rfl) T

/-- The length of `transcriptPerm T` equals the total `permCost` of `T`. -/
@[simp] theorem length_transcriptPerm_eq_sum_permCost {G : Type}
    (T : Transcript (EvenMansourSpec G)) :
    (transcriptPerm T).length = (T.map fun entry => permCost entry.1).sum :=
  length_filterMap_eq_sum_cost transcriptPermEntry permCost
    (fun ⟨q, _⟩ => by rcases q with (x | y) | (u | v) <;> rfl) T

/-- Against any stateful bidirectional oracle, a supported run of `program` with
`IsCallBounded program Q_e Q_π` records at most `Q_e` cipher pairs. -/
theorem IsCallBounded.length_transcriptCipher_le {G State γ : Type}
    {program : OracleComp (EvenMansourSpec G) γ} {Q_e Q_π : ℕ}
    (h : IsCallBounded program Q_e Q_π)
    (oracle : (q : PermQuery G ⊕ PermQuery G) → StateT State PMF (EvenMansourSpec G q))
    {s s' : State} {result : γ} {T : Transcript (EvenMansourSpec G)}
    (hmem : (result, s', T) ∈
      ((OracleComp.interpret (withTranscript oracle) program).run (s, [])).support) :
    (transcriptCipher T).length ≤ Q_e := by
  rw [length_transcriptCipher_eq_sum_cipherCost]
  exact h.1.transcript_cost_le oracle hmem

/-- Against any stateful bidirectional oracle, a supported run of `program` with
`IsCallBounded program Q_e Q_π` records at most `Q_π` primitive permutation pairs. -/
theorem IsCallBounded.length_transcriptPerm_le {G State γ : Type}
    {program : OracleComp (EvenMansourSpec G) γ} {Q_e Q_π : ℕ}
    (h : IsCallBounded program Q_e Q_π)
    (oracle : (q : PermQuery G ⊕ PermQuery G) → StateT State PMF (EvenMansourSpec G q))
    {s s' : State} {result : γ} {T : Transcript (EvenMansourSpec G)}
    (hmem : (result, s', T) ∈
      ((OracleComp.interpret (withTranscript oracle) program).run (s, [])).support) :
    (transcriptPerm T).length ≤ Q_π := by
  rw [length_transcriptPerm_eq_sum_permCost]
  exact h.2.transcript_cost_le oracle hmem

variable {G : Type} [AddGroup G] [DecidableEq G] [Fintype G]

omit [AddGroup G] [DecidableEq G] in
private theorem IsCallBounded.badKey_toReal_le {State γ K : Type}
    {program : OracleComp (EvenMansourSpec G) γ} {Q_e Q_π : ℕ}
    (h : IsCallBounded program Q_e Q_π)
    (oracle : (q : PermQuery G ⊕ PermQuery G) → StateT State PMF (EvenMansourSpec G q))
    {s s' : State} {result : γ} {T : Transcript (EvenMansourSpec G)}
    (hmem : (result, s', T) ∈
      ((OracleComp.interpret (withTranscript oracle) program).run (s, [])).support)
    (μ : PMF K) (bad : List (G × G) → List (G × G) → K → Bool)
    (hbad : ∀ T_e T_π,
      (μ.toOuterMeasure {k | bad T_e T_π k = true}).toReal ≤
        2 * (T_e.length : ℝ) * (T_π.length : ℝ) / (Fintype.card G : ℝ)) :
    (μ.toOuterMeasure {k | bad (transcriptCipher T) (transcriptPerm T) k = true}).toReal ≤
      2 * (Q_e : ℝ) * (Q_π : ℝ) / (Fintype.card G : ℝ) := by
  have hlen_e : ((transcriptCipher T).length : ℝ) ≤ Q_e :=
    Nat.cast_le.mpr (h.length_transcriptCipher_le oracle hmem)
  have hlen_π : ((transcriptPerm T).length : ℝ) ≤ Q_π :=
    Nat.cast_le.mpr (h.length_transcriptPerm_le oracle hmem)
  refine (hbad (transcriptCipher T) (transcriptPerm T)).trans ?_
  gcongr

/-- **Boneh–Shoup Theorem 4.14 bad-key union bound on call-bounded transcripts (two-key)**:
against any stateful bidirectional oracle, on any supported transcript `T` of a distinguisher
satisfying `IsCallBounded program Q_e Q_π`, a fresh uniform key pair `(k₀, k₁) ← G × G`, sampled
independently of `T`, is bad for `transcriptCipher T` and `transcriptPerm T` with real
probability at most `2 * Q_e * Q_π / |G|`. -/
theorem IsCallBounded.badEvenMansourKey_toReal_le {State γ : Type}
    {program : OracleComp (EvenMansourSpec G) γ} {Q_e Q_π : ℕ}
    (h : IsCallBounded program Q_e Q_π)
    (oracle : (q : PermQuery G ⊕ PermQuery G) → StateT State PMF (EvenMansourSpec G q))
    {s s' : State} {result : γ} {T : Transcript (EvenMansourSpec G)}
    (hmem : (result, s', T) ∈
      ((OracleComp.interpret (withTranscript oracle) program).run (s, [])).support) :
    ((PMF.uniformOfFintype (G × G)).toOuterMeasure
      {k | isBadEvenMansourKey (transcriptCipher T) (transcriptPerm T) k = true}).toReal ≤
      2 * (Q_e : ℝ) * (Q_π : ℝ) / (Fintype.card G : ℝ) :=
  h.badKey_toReal_le oracle hmem _ isBadEvenMansourKey toOuterMeasure_isBadEvenMansourKey_toReal_le

/-- **Boneh–Shoup Theorem 4.14 bad-key union bound on call-bounded transcripts (single-key)**:
against any stateful bidirectional oracle, on any supported transcript `T` of a distinguisher
satisfying `IsCallBounded program Q_e Q_π`, a single fresh uniform key `k ← G`, sampled
independently of `T`, is bad for `transcriptCipher T` and `transcriptPerm T` with real
probability at most `2 * Q_e * Q_π / |G|`. -/
theorem IsCallBounded.badSingleKeyEvenMansour_toReal_le {State γ : Type}
    {program : OracleComp (EvenMansourSpec G) γ} {Q_e Q_π : ℕ}
    (h : IsCallBounded program Q_e Q_π)
    (oracle : (q : PermQuery G ⊕ PermQuery G) → StateT State PMF (EvenMansourSpec G q))
    {s s' : State} {result : γ} {T : Transcript (EvenMansourSpec G)}
    (hmem : (result, s', T) ∈
      ((OracleComp.interpret (withTranscript oracle) program).run (s, [])).support) :
    ((PMF.uniformOfFintype G).toOuterMeasure
      {k | isBadSingleKeyEvenMansour (transcriptCipher T) (transcriptPerm T) k = true}).toReal ≤
      2 * (Q_e : ℝ) * (Q_π : ℝ) / (Fintype.card G : ℝ) :=
  h.badKey_toReal_le oracle hmem _ isBadSingleKeyEvenMansour
    toOuterMeasure_isBadSingleKeyEvenMansour_toReal_le

end TranscriptBounds

/-! ### Key-shifted lazy permutation coupling and end-to-end advantage bound -/

section Coupling

variable {G : Type} [AddGroup G] [DecidableEq G] [Fintype G] [Nonempty G]

/-- Translate an `EvenMansourSpec G` query under key `k = (k₀, k₁)` into the underlying query on the
primitive permutation `π`. -/
def toPermQuery (k : G × G) : PermQuery G ⊕ PermQuery G → PermQuery G
  | .inl (.forward x) => .forward (x + k.1)
  | .inl (.inverse y) => .inverse (y - k.2)
  | .inr qπ => qπ

/-- Post-process the primitive permutation's answer to recover the Even–Mansour oracle answer under
key `k = (k₀, k₁)`. -/
def fromPermAnswer (k : G × G) : (q : PermQuery G ⊕ PermQuery G) → G → EvenMansourSpec G q
  | .inl (.forward _) => (· + k.2)
  | .inl (.inverse _) => (· - k.1)
  | .inr _ => id

/-- Translate an `EvenMansourSpec G` program under key `k = (k₀, k₁)` into a single-permutation
`PermOracleSpec G` program on `π`. -/
def toPermProgram (k : G × G) {α : Type} (program : OracleComp (EvenMansourSpec G) α) :
    OracleComp (PermOracleSpec G) α :=
  OracleComp.interpret
    (fun q => fromPermAnswer k q <$> OracleComp.query (spec := PermOracleSpec G) (toPermQuery k q))
    program

/-- Lazy single-cache handler for the real Even–Mansour world with fixed key `k = (k₀, k₁)`:
translate each query via `toPermQuery k`, answer lazily against a single
`RandomPermutation.Cache G`, and post-process the answer via `fromPermAnswer k`. -/
noncomputable def realLazyHandler (k : G × G) (q : PermQuery G ⊕ PermQuery G) :
    StateT (RandomPermutation.Cache G) PMF (EvenMansourSpec G q) := fun cache =>
  (RandomPermutation.answer (toPermQuery k q) cache).map fun (ans, cache') =>
    (fromPermAnswer k q ans, cache')

omit [DecidableEq G] [Fintype G] [Nonempty G] in
private theorem interpret_evalPerm_toPermProgram {α : Type} (π : Equiv.Perm G) (k : G × G)
    (program : OracleComp (EvenMansourSpec G) α) :
    OracleComp.interpret (fun q => PMF.pure (evalPerm π q)) (toPermProgram k program) =
      PMF.pure (evalEvenMansour π k.1 k.2 program) := by
  rw [toPermProgram, OracleComp.interpret_interpret, evalEvenMansour, pure_evalTwoPerms]
  congr 1
  funext q
  rcases q with (x | y) | (u | v) <;>
    simp [toPermQuery, fromPermAnswer, sumHandler, PMF.monad_map_eq_map]

private theorem run_interpret_answer_toPermProgram {α : Type} (k : G × G)
    (program : OracleComp (EvenMansourSpec G) α) (cache : RandomPermutation.Cache G) :
    (OracleComp.interpret RandomPermutation.answer (toPermProgram k program)).run cache =
      (OracleComp.interpret (realLazyHandler k) program).run cache := by
  rw [toPermProgram, OracleComp.interpret_interpret]
  congr 2

/-- For a fixed key pair `k = (k₀, k₁)`, sampling a uniform permutation `π` and evaluating
`evalEvenMansour π k.1 k.2 program` has the exact same distribution as running `realLazyHandler k`
from the empty cache `[]`. -/
theorem realGameForKey_eq_lazy (k : G × G) (program : OracleComp (EvenMansourSpec G) Bool) :
    ((PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
      PMF.pure (evalEvenMansour π k.1 k.2 program)) =
    (((OracleComp.interpret (realLazyHandler k) program).run []).map Prod.fst) := by
  simpa only [PMF.monad_bind_eq_bind, interpret_evalPerm_toPermProgram,
    run_interpret_answer_toPermProgram] using
    RandomPermutation.uniform_interpret_eq_lazy (toPermProgram k program)

/-- Map a primitive permutation pair `(u, v)` to the corresponding cipher pair `(u - k₀, v + k₁)`
under key `k = (k₀, k₁)`. -/
def unshiftPair (k : G × G) (p : G × G) : G × G :=
  (p.1 - k.1, p.2 + k.2)

/-- Shift a cipher pair `(x, y)` to its internal permutation pair `(x + k₀, y - k₁)` under key
`k = (k₀, k₁)`. -/
def shiftPair (k : G × G) (e : G × G) : G × G :=
  (e.1 + k.1, e.2 - k.2)

omit [DecidableEq G] [Fintype G] [Nonempty G] in
@[simp] theorem unshiftPair_shiftPair (k e : G × G) : unshiftPair k (shiftPair k e) = e := by
  rcases e with ⟨x, y⟩
  simp [unshiftPair, shiftPair]

omit [DecidableEq G] [Fintype G] [Nonempty G] in
@[simp] theorem shiftPair_unshiftPair (k p : G × G) : shiftPair k (unshiftPair k p) = p := by
  rcases p with ⟨u, v⟩
  simp [unshiftPair, shiftPair]

omit [AddGroup G] [Fintype G] [Nonempty G] in
private theorem lookup_eq_some_iff_mem {cache : Cache G} (hc : IsPartialBijection cache)
    {x y : G} :
    cache.lookup x = some y ↔ (x, y) ∈ cache := by
  refine ⟨mem_of_lookup_eq_some, fun hmem => ?_⟩
  obtain ⟨π, hπ⟩ := hc
  cases h : cache.lookup x with
  | none => exact False.elim (lookup_eq_none_iff.mp h (x, y) hmem rfl)
  | some y' =>
    have hy' : π x = y' := hπ.apply_of_lookup_eq_some h
    have hy : π x = y := hπ (x, y) hmem
    exact congrArg some (hy'.symm.trans hy)

omit [AddGroup G] [Fintype G] [Nonempty G] in
private theorem invLookup_eq_some_iff_mem {cache : Cache G} (hc : IsPartialBijection cache)
    {y x : G} :
    invLookup cache y = some x ↔ (x, y) ∈ cache := by
  refine ⟨mem_of_invLookup_eq_some, fun hmem => ?_⟩
  obtain ⟨π, hπ⟩ := hc
  cases h : invLookup cache y with
  | none => exact False.elim (invLookup_eq_none_iff.mp h (x, y) hmem rfl)
  | some x' =>
    have hx' : π.symm y = x' := hπ.symm_apply_of_invLookup_eq_some h
    have hx : π.symm y = x := π.symm_apply_eq.mpr (hπ (x, y) hmem).symm
    exact congrArg some (hx'.symm.trans hx)

omit [AddGroup G] [Fintype G] [Nonempty G] in
private theorem lookup_eq_none_iff_forall {cache : Cache G} {x : G} :
    cache.lookup x = none ↔ ∀ y, (x, y) ∉ cache := by
  rw [lookup_eq_none_iff]
  exact ⟨fun h y hy => h (x, y) hy rfl, fun h ⟨a, b⟩ hab heq => h b (heq ▸ hab)⟩

omit [AddGroup G] [Fintype G] [Nonempty G] in
private theorem invLookup_eq_none_iff_forall {cache : Cache G} {y : G} :
    invLookup cache y = none ↔ ∀ x, (x, y) ∉ cache := by
  rw [invLookup_eq_none_iff]
  exact ⟨fun h x hx => h (x, y) hx rfl, fun h ⟨a, b⟩ hab heq => h a (heq ▸ hab)⟩

/-- Coupling invariant between the ideal caches `(c_e, c_π)` and the single real permutation cache
`c` under key `k = (k₀, k₁)`: all three caches are partial bijections, `(c_e, c_π)` has not
triggered `isBadEvenMansourKey`, and `c` contains exactly the key-shifted pairs of `c_e` together
with the pairs of `c_π`. -/
structure CacheRel (k : G × G) (c_e c_π c : Cache G) : Prop where
  partial_e : IsPartialBijection c_e
  partial_π : IsPartialBijection c_π
  partial_c : IsPartialBijection c
  good : isBadEvenMansourKey c_e c_π k = false
  mem_iff : ∀ p : G × G, p ∈ c ↔ unshiftPair k p ∈ c_e ∨ p ∈ c_π

omit [Fintype G] [Nonempty G] in
private theorem cacheRel_nil (k : G × G) : CacheRel k [] [] [] where
  partial_e := isPartialBijection_nil
  partial_π := isPartialBijection_nil
  partial_c := isPartialBijection_nil
  good := rfl
  mem_iff _ := by simp

omit [Nonempty G] in
private theorem CacheRel.map_unusedRange_subset_e {k : G × G} {c_e c_π c : Cache G}
    (hrel : CacheRel k c_e c_π c) :
    (unusedRange c).map (Equiv.addRight k.2).toEmbedding ⊆ unusedRange c_e := by
  intro y hy
  rw [Finset.mem_map] at hy
  obtain ⟨v, hv, rfl⟩ := hy
  rw [mem_unusedRange_iff, invLookup_eq_none_iff_forall] at hv ⊢
  intro x hx
  have hmem : (x + k.1, v) ∈ c := (hrel.mem_iff (x + k.1, v)).mpr
    (Or.inl (by simpa [unshiftPair] using hx))
  exact hv (x + k.1) hmem

omit [Nonempty G] in
private theorem CacheRel.map_unusedDomain_subset_e {k : G × G} {c_e c_π c : Cache G}
    (hrel : CacheRel k c_e c_π c) :
    (unusedDomain c).map (Equiv.subRight k.1).toEmbedding ⊆ unusedDomain c_e := by
  intro x hx
  rw [Finset.mem_map] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  rw [mem_unusedDomain_iff, lookup_eq_none_iff_forall] at hu ⊢
  intro y hy
  have hmem : (u, y - k.2) ∈ c := (hrel.mem_iff (u, y - k.2)).mpr
    (Or.inl (by simpa [unshiftPair] using hy))
  exact hu (y - k.2) hmem

omit [Nonempty G] in
private theorem CacheRel.unusedRange_subset_π {k : G × G} {c_e c_π c : Cache G}
    (hrel : CacheRel k c_e c_π c) :
    unusedRange c ⊆ unusedRange c_π := by
  intro v hv
  rw [mem_unusedRange_iff, invLookup_eq_none_iff_forall] at hv ⊢
  exact fun u hu => hv u ((hrel.mem_iff (u, v)).mpr (Or.inr hu))

omit [Nonempty G] in
private theorem CacheRel.unusedDomain_subset_π {k : G × G} {c_e c_π c : Cache G}
    (hrel : CacheRel k c_e c_π c) :
    unusedDomain c ⊆ unusedDomain c_π := by
  intro u hu
  rw [mem_unusedDomain_iff, lookup_eq_none_iff_forall] at hu ⊢
  exact fun v hv => hu v ((hrel.mem_iff (u, v)).mpr (Or.inr hv))

omit [Fintype G] [Nonempty G] in
private theorem CacheRel.lookup_c_of_lookup_e {k : G × G} {c_e c_π c : Cache G}
    (hrel : CacheRel k c_e c_π c) {x y : G} (h : c_e.lookup x = some y) :
    c.lookup (x + k.1) = some (y - k.2) := by
  rw [lookup_eq_some_iff_mem hrel.partial_c, hrel.mem_iff]
  exact Or.inl (by simpa [unshiftPair] using mem_of_lookup_eq_some h)

omit [Fintype G] [Nonempty G] in
private theorem CacheRel.invLookup_c_of_invLookup_e {k : G × G} {c_e c_π c : Cache G}
    (hrel : CacheRel k c_e c_π c) {y x : G} (h : invLookup c_e y = some x) :
    invLookup c (y - k.2) = some (x + k.1) := by
  rw [invLookup_eq_some_iff_mem hrel.partial_c, hrel.mem_iff]
  exact Or.inl (by simpa [unshiftPair] using mem_of_invLookup_eq_some h)

omit [Fintype G] [Nonempty G] in
private theorem CacheRel.lookup_c_of_lookup_π {k : G × G} {c_e c_π c : Cache G}
    (hrel : CacheRel k c_e c_π c) {u v : G} (h : c_π.lookup u = some v) :
    c.lookup u = some v := by
  rw [lookup_eq_some_iff_mem hrel.partial_c, hrel.mem_iff]
  exact Or.inr (mem_of_lookup_eq_some h)

omit [Fintype G] [Nonempty G] in
private theorem CacheRel.invLookup_c_of_invLookup_π {k : G × G} {c_e c_π c : Cache G}
    (hrel : CacheRel k c_e c_π c) {v u : G} (h : invLookup c_π v = some u) :
    invLookup c v = some u := by
  rw [invLookup_eq_some_iff_mem hrel.partial_c, hrel.mem_iff]
  exact Or.inr (mem_of_invLookup_eq_some h)

omit [Fintype G] [Nonempty G] in
private theorem CacheRel.cons_cipher {k : G × G} {c_e c_π c : Cache G}
    (hrel : CacheRel k c_e c_π c) {x y : G} (hx : c_e.lookup x = none)
    (hy : invLookup c_e y = none) (hgood' : isBadEvenMansourKey ((x, y) :: c_e) c_π k = false) :
    c.lookup (x + k.1) = none ∧ invLookup c (y - k.2) = none ∧
      CacheRel k ((x, y) :: c_e) c_π ((x + k.1, y - k.2) :: c) := by
  have hxc : c.lookup (x + k.1) = none := by
    refine lookup_eq_none_iff_forall.mpr fun v hv => ?_
    rcases (hrel.mem_iff (x + k.1, v)).mp hv with he | hπ
    · simp only [unshiftPair, add_sub_cancel_right] at he
      exact lookup_eq_none_iff_forall.mp hx (v + k.2) he
    · exact (disjoint_of_isBadEvenMansourKey_eq_false hgood' List.mem_cons_self hπ).1 rfl
  have hyc : invLookup c (y - k.2) = none := by
    refine invLookup_eq_none_iff_forall.mpr fun u hu => ?_
    rcases (hrel.mem_iff (u, y - k.2)).mp hu with he | hπ
    · simp only [unshiftPair, sub_add_cancel] at he
      exact invLookup_eq_none_iff_forall.mp hy (u - k.1) he
    · exact (disjoint_of_isBadEvenMansourKey_eq_false hgood' List.mem_cons_self hπ).2 rfl
  refine ⟨hxc, hyc,
    { partial_e := hrel.partial_e.cons_of_lookup_eq_none hx hy
      partial_π := hrel.partial_π
      partial_c := hrel.partial_c.cons_of_lookup_eq_none hxc hyc
      good := hgood'
      mem_iff := fun p => ?_ }⟩
  have hhead : p = (x + k.1, y - k.2) ↔ unshiftPair k p = (x, y) := by
    rcases p with ⟨u, v⟩
    simp only [unshiftPair, Prod.mk.injEq, eq_sub_iff_add_eq, sub_eq_iff_eq_add]
  rw [List.mem_cons, List.mem_cons, hrel.mem_iff, hhead, or_assoc]

omit [Fintype G] [Nonempty G] in
private theorem CacheRel.cons_perm {k : G × G} {c_e c_π c : Cache G}
    (hrel : CacheRel k c_e c_π c) {u v : G} (hu : c_π.lookup u = none)
    (hv : invLookup c_π v = none) (hgood' : isBadEvenMansourKey c_e ((u, v) :: c_π) k = false) :
    c.lookup u = none ∧ invLookup c v = none ∧
      CacheRel k c_e ((u, v) :: c_π) ((u, v) :: c) := by
  have huc : c.lookup u = none := by
    refine lookup_eq_none_iff_forall.mpr fun v' hv' => ?_
    rcases (hrel.mem_iff (u, v')).mp hv' with he | hπ
    · exact (disjoint_of_isBadEvenMansourKey_eq_false hgood' he List.mem_cons_self).1
        (sub_add_cancel u k.1)
    · exact lookup_eq_none_iff_forall.mp hu v' hπ
  have hvc : invLookup c v = none := by
    refine invLookup_eq_none_iff_forall.mpr fun u' hu' => ?_
    rcases (hrel.mem_iff (u', v)).mp hu' with he | hπ
    · exact (disjoint_of_isBadEvenMansourKey_eq_false hgood' he List.mem_cons_self).2
        (add_sub_cancel_right v k.2)
    · exact invLookup_eq_none_iff_forall.mp hv u' hπ
  exact ⟨huc, hvc,
    { partial_e := hrel.partial_e
      partial_π := hrel.partial_π.cons_of_lookup_eq_none hu hv
      partial_c := hrel.partial_c.cons_of_lookup_eq_none huc hvc
      good := hgood'
      mem_iff := fun p => by simp only [List.mem_cons, hrel.mem_iff, or_left_comm] }⟩

omit [AddGroup G] in
/-- One lazy permutation answer leaves the cache unchanged or prepends one entry. -/
private theorem eq_or_exists_cons_of_mem_answer_support {q : PermQuery G} {cache cache' : Cache G}
    {a : G} (hmem : (a, cache') ∈ (RandomPermutation.answer q cache).support) :
    cache' = cache ∨ ∃ e, cache' = e :: cache := by
  cases hq : cachedAnswer cache q with
  | some b =>
    rw [RandomPermutation.answer_of_cachedAnswer_eq_some hq] at hmem
    supp_cases hmem
    exact .inl rfl
  | none =>
    by_cases hne : (freshAnswers cache q).Nonempty
    · rw [RandomPermutation.answer_of_cachedAnswer_eq_none hq hne] at hmem
      supp_cases hmem
      exact .inr ⟨_, rfl⟩
    · cases q <;>
        (simp only [RandomPermutation.cachedAnswer, RandomPermutation.freshAnswers] at hq hne
         supp_cases hmem [RandomPermutation.answer, hq, dite_eq_right hne]
         exact .inr ⟨_, rfl⟩)

omit [AddGroup G] in
private theorem mem_of_mem_answer_support {q : PermQuery G} {cache cache' : Cache G} {a : G}
    (hmem : (a, cache') ∈ (RandomPermutation.answer q cache).support) :
    ∀ e ∈ cache, e ∈ cache' := by
  rcases eq_or_exists_cons_of_mem_answer_support hmem with rfl | ⟨_, rfl⟩
  · exact fun _ h => h
  · exact fun _ h => List.mem_cons_of_mem _ h

omit [AddGroup G] in
private theorem length_le_of_mem_answer_support {q : PermQuery G} {cache cache' : Cache G} {a : G}
    (hmem : (a, cache') ∈ (RandomPermutation.answer q cache).support) :
    cache'.length ≤ cache.length + 1 := by
  rcases eq_or_exists_cons_of_mem_answer_support hmem with rfl | ⟨_, rfl⟩ <;> simp

omit [Fintype G] [Nonempty G] in
private theorem isBadEvenMansourKey_mono {c_e c_e' c_π c_π' : Cache G} {k : G × G}
    (he : ∀ e ∈ c_e, e ∈ c_e') (hπ : ∀ p ∈ c_π, p ∈ c_π')
    (hbad : isBadEvenMansourKey c_e c_π k = true) :
    isBadEvenMansourKey c_e' c_π' k = true := by
  rw [isBadEvenMansourKey_eq_true_iff] at hbad ⊢
  obtain ⟨e, he_mem, p, hp_mem, hcol⟩ := hbad
  exact ⟨e, he e he_mem, p, hπ p hp_mem, hcol⟩

private theorem isBadEvenMansourKey_of_run_idealLazyHandler {α : Type}
    (program : OracleComp (EvenMansourSpec G) α) {c_e c_π : Cache G} {k : G × G}
    (hbad : isBadEvenMansourKey c_e c_π k = true) {res : α × (Cache G × Cache G)}
    (hmem : res ∈ ((OracleComp.interpret idealLazyHandler program).run (c_e, c_π)).support) :
    isBadEvenMansourKey res.2.1 res.2.2 k = true := by
  refine OracleComp.run_interpret_invariant idealLazyHandler
    (fun st => isBadEvenMansourKey st.1 st.2 k = true) ?_ program (c_e, c_π) hbad res.1 res.2 hmem
  rintro (qe | qπ) ⟨ce, cπ⟩ hb ans ⟨ce', cπ'⟩ hstep
  · obtain ⟨hmem₀, rfl⟩ := mem_support_idealLazyHandler_inl.mp hstep
    exact isBadEvenMansourKey_mono (mem_of_mem_answer_support hmem₀) (fun _ h => h) hb
  · obtain ⟨hmem₀, rfl⟩ := mem_support_idealLazyHandler_inr.mp hstep
    exact isBadEvenMansourKey_mono (fun _ h => h) (mem_of_mem_answer_support hmem₀) hb

private theorem toOuterMeasure_run_idealLazyHandler_eq_zero_of_bad {α : Type}
    (program : OracleComp (EvenMansourSpec G) α) (P : α → Prop) {c_e c_π : Cache G} {k : G × G}
    (hbad : isBadEvenMansourKey c_e c_π k = true) :
    ((OracleComp.interpret idealLazyHandler program).run (c_e, c_π)).toOuterMeasure
      {res | P res.1 ∧ isBadEvenMansourKey res.2.1 res.2.2 k = false} = 0 := by
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  exact fun res hmem hS => Bool.false_ne_true
    (hS.2.symm.trans (isBadEvenMansourKey_of_run_idealLazyHandler program hbad hmem))

omit [AddGroup G] [DecidableEq G] [Fintype G] [Nonempty G] in
private theorem toOuterMeasure_uniformOfFinset_bind {U : Finset G} (hU : U.Nonempty)
    {β : Type} (H : G → PMF β) (S : Set β) :
    ((PMF.uniformOfFinset U hU).bind H).toOuterMeasure S =
      ∑ z ∈ U, (U.card : ℝ≥0∞)⁻¹ * (H z).toOuterMeasure S := by
  classical
  rw [PMF.toOuterMeasure_bind_apply,
    tsum_eq_sum (s := U) fun z hz => by simp [PMF.uniformOfFinset_apply, hz]]
  exact Finset.sum_congr rfl fun z hz => by simp [PMF.uniformOfFinset_apply, hz]

omit [AddGroup G] [DecidableEq G] [Fintype G] [Nonempty G] in
/-- Compare the uniform continuation sums after discarding bad samples and relabeling the
remaining samples by an equivalence. -/
private theorem sum_uniform_le_of_good (U V : Finset G) (e : G ≃ G) (bad : G → Bool)
    (f g : G → ℝ≥0∞) (hsub : V.map e.toEmbedding ⊆ U)
    (hzero : ∀ x, bad x = true → f x = 0)
    (hgood : ∀ x ∈ U, bad x = false → e.symm x ∈ V ∧ f x ≤ g (e.symm x)) :
    ∑ x ∈ U, (U.card : ℝ≥0∞)⁻¹ * f x ≤ ∑ y ∈ V, (V.card : ℝ≥0∞)⁻¹ * g y := by
  have hcard : (U.card : ℝ≥0∞)⁻¹ ≤ (V.card : ℝ≥0∞)⁻¹ :=
    ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (by simpa using Finset.card_le_card hsub))
  have hout : ∀ x ∈ U, x ∉ V.map e.toEmbedding → (U.card : ℝ≥0∞)⁻¹ * f x = 0 := by
    intro x hx hnot
    by_cases hb : bad x = true
    · rw [hzero x hb, mul_zero]
    · exact False.elim (hnot (Finset.mem_map.mpr
        ⟨e.symm x, (hgood x hx (Bool.eq_false_iff.mpr hb)).1, e.apply_symm_apply x⟩))
  rw [← Finset.sum_subset hsub hout, Finset.sum_map]
  refine Finset.sum_le_sum fun y hy => ?_
  simp only [Equiv.toEmbedding_apply]
  by_cases hb : bad (e y) = true
  · simp only [hzero (e y) hb, mul_zero, zero_le]
  · simpa only [Equiv.symm_apply_apply] using mul_le_mul' hcard
      (hgood (e y) (hsub (Finset.mem_map_of_mem _ hy)) (Bool.eq_false_iff.mpr hb)).2

/-- Shared one-query lazy-permutation coupling step across forward/inverse cipher and primitive
queries. -/
private theorem answer_step_good_le {α : Type}
    (cont : G → OracleComp (EvenMansourSpec G) α) (P : α → Prop) (k : G × G)
    {c_e c_π c : Cache G} (hrel : CacheRel k c_e c_π c)
    (ih : ∀ ans {c_e' c_π' c' : Cache G}, CacheRel k c_e' c_π' c' →
      ((OracleComp.interpret idealLazyHandler (cont ans)).run (c_e', c_π')).toOuterMeasure
        {res | P res.1 ∧ isBadEvenMansourKey res.2.1 res.2.2 k = false} ≤
      ((OracleComp.interpret (realLazyHandler k) (cont ans)).run c').toOuterMeasure
        {res | P res.1})
    (q_i q_r : PermQuery G) (c_i : Cache G) (hc_i : IsPartialBijection c_i)
    (mkSt : Cache G → Cache G × Cache G) (hmk_self : mkSt c_i = (c_e, c_π))
    (e : G ≃ G)
    (hhit : ∀ a, cachedAnswer c_i q_i = some a → cachedAnswer c q_r = some (e.symm a))
    (hsub : (freshAnswers c q_r).map e.toEmbedding ⊆ freshAnswers c_i q_i)
    (hcons : cachedAnswer c_i q_i = none → ∀ a ∈ freshAnswers c_i q_i,
      isBadEvenMansourKey (mkSt (PermQuery.toCacheEntry ⟨q_i, a⟩ :: c_i)).1
        (mkSt (PermQuery.toCacheEntry ⟨q_i, a⟩ :: c_i)).2 k = false →
      cachedAnswer c q_r = none ∧ e.symm a ∈ freshAnswers c q_r ∧
        CacheRel k (mkSt (PermQuery.toCacheEntry ⟨q_i, a⟩ :: c_i)).1
          (mkSt (PermQuery.toCacheEntry ⟨q_i, a⟩ :: c_i)).2
          (PermQuery.toCacheEntry ⟨q_r, e.symm a⟩ :: c)) :
    (((RandomPermutation.answer q_i c_i).map fun (a, ci') => (a, mkSt ci')).bind fun p =>
      (OracleComp.interpret idealLazyHandler (cont p.1)).run p.2).toOuterMeasure
        {res | P res.1 ∧ isBadEvenMansourKey res.2.1 res.2.2 k = false} ≤
    (((RandomPermutation.answer q_r c).map fun (ans, c') => (e ans, c')).bind fun p =>
      (OracleComp.interpret (realLazyHandler k) (cont p.1)).run p.2).toOuterMeasure
        {res | P res.1} := by
  cases hq_i : cachedAnswer c_i q_i with
  | some a =>
    rw [RandomPermutation.answer_of_cachedAnswer_eq_some hq_i,
      RandomPermutation.answer_of_cachedAnswer_eq_some (hhit a hq_i)]
    simp only [PMF.pure_map, PMF.pure_bind, hmk_self, Equiv.apply_symm_apply]
    exact ih a hrel
  | none =>
    have hne_i := hc_i.freshAnswers_nonempty hq_i
    rw [RandomPermutation.answer_of_cachedAnswer_eq_none hq_i hne_i]
    simp only [PMF.map_comp, PMF.bind_map, Function.comp_def, toOuterMeasure_uniformOfFinset_bind]
    by_cases hq_r : cachedAnswer c q_r = none
    · have hne_r := hrel.partial_c.freshAnswers_nonempty hq_r
      rw [RandomPermutation.answer_of_cachedAnswer_eq_none hq_r hne_r]
      simp only [PMF.bind_map, Function.comp_def, toOuterMeasure_uniformOfFinset_bind]
      refine sum_uniform_le_of_good _ _ e
        (fun a => isBadEvenMansourKey (mkSt (PermQuery.toCacheEntry ⟨q_i, a⟩ :: c_i)).1
          (mkSt (PermQuery.toCacheEntry ⟨q_i, a⟩ :: c_i)).2 k) _ _ hsub
        (fun a hbad => toOuterMeasure_run_idealLazyHandler_eq_zero_of_bad (cont a) P hbad)
        fun a ha hgood => ?_
      obtain ⟨-, ha_r, hrel'⟩ := hcons hq_i a ha hgood
      exact ⟨ha_r, by simpa only [Equiv.apply_symm_apply] using ih a hrel'⟩
    · refine (le_of_eq (Finset.sum_eq_zero fun a ha => ?_)).trans zero_le
      have hbad := Bool.eq_true_of_not_eq_false fun hgood => hq_r (hcons hq_i a ha hgood).1
      rw [toOuterMeasure_run_idealLazyHandler_eq_zero_of_bad (cont a) P hbad, mul_zero]

/-- **Lazy coupling inequality**: starting from any cache triple `(c_e, c_π, c)` satisfying
`CacheRel k c_e c_π c`, the probability that `idealLazyHandler` produces an output satisfying `P`
without triggering `isBadEvenMansourKey` is at most the probability that `realLazyHandler k`
produces an output satisfying `P`. -/
theorem run_idealLazyHandler_good_le_realLazyHandler {α : Type}
    (program : OracleComp (EvenMansourSpec G) α) (P : α → Prop) (k : G × G)
    {c_e c_π c : Cache G} (hrel : CacheRel k c_e c_π c) :
    ((OracleComp.interpret idealLazyHandler program).run (c_e, c_π)).toOuterMeasure
      {(r, c_e', c_π') : α × Cache G × Cache G |
        P r ∧ isBadEvenMansourKey c_e' c_π' k = false} ≤
    ((OracleComp.interpret (realLazyHandler k) program).run c).toOuterMeasure
      {res | P res.1} := by
  rw [show {(r, c_e', c_π') : α × Cache G × Cache G |
      P r ∧ isBadEvenMansourKey c_e' c_π' k = false} =
      {res | P res.1 ∧ isBadEvenMansourKey res.2.1 res.2.2 k = false} by ext ⟨_, _, _⟩; rfl]
  induction program generalizing c_e c_π c with
  | pure a =>
    change (PMF.pure (a, (c_e, c_π))).toOuterMeasure
        {res | P res.1 ∧ isBadEvenMansourKey res.2.1 res.2.2 k = false} ≤
      (PMF.pure (a, c)).toOuterMeasure {res | P res.1}
    by_cases hP : P a <;> simp only [PMF.toOuterMeasure_pure_apply, hP, hrel.good,
      Set.mem_ofPred_eq, and_self, false_and, ↓reduceIte, le_refl]
  | liftBind q cont ih =>
    change ((idealLazyHandler q (c_e, c_π)).bind fun p =>
        (OracleComp.interpret idealLazyHandler (cont p.1)).run p.2).toOuterMeasure _ ≤
      ((realLazyHandler k q c).bind fun p =>
        (OracleComp.interpret (realLazyHandler k) (cont p.1)).run p.2).toOuterMeasure _
    rcases q with (x | y) | (u | v)
    · exact answer_step_good_le cont P k hrel ih (.forward x) (.forward (x + k.1)) c_e
        hrel.partial_e (·, c_π) rfl (Equiv.subRight k.2).symm
        (fun _ => hrel.lookup_c_of_lookup_e) hrel.map_unusedRange_subset_e
        fun hx y hy hgood =>
          let ⟨hxc, hyc, hrel'⟩ := hrel.cons_cipher hx (mem_unusedRange_iff.mp hy) hgood
          ⟨hxc, mem_unusedRange_iff.mpr hyc, hrel'⟩
    · exact answer_step_good_le cont P k hrel ih (.inverse y) (.inverse (y - k.2)) c_e
        hrel.partial_e (·, c_π) rfl (Equiv.subRight k.1)
        (fun _ => hrel.invLookup_c_of_invLookup_e) hrel.map_unusedDomain_subset_e
        fun hy x hx hgood =>
          let ⟨hxc, hyc, hrel'⟩ := hrel.cons_cipher (mem_unusedDomain_iff.mp hx) hy hgood
          ⟨hyc, mem_unusedDomain_iff.mpr hxc, hrel'⟩
    · exact answer_step_good_le cont P k hrel ih (.forward u) (.forward u) c_π
        hrel.partial_π (c_e, ·) rfl (Equiv.refl G)
        (fun _ => hrel.lookup_c_of_lookup_π)
        (Finset.map_refl.trans_subset hrel.unusedRange_subset_π)
        fun hu v hv hgood =>
          let ⟨huc, hvc, hrel'⟩ := hrel.cons_perm hu (mem_unusedRange_iff.mp hv) hgood
          ⟨huc, mem_unusedRange_iff.mpr hvc, hrel'⟩
    · exact answer_step_good_le cont P k hrel ih (.inverse v) (.inverse v) c_π
        hrel.partial_π (c_e, ·) rfl (Equiv.refl G)
        (fun _ => hrel.invLookup_c_of_invLookup_π)
        (Finset.map_refl.trans_subset hrel.unusedDomain_subset_π)
        fun hv u hu hgood =>
          let ⟨huc, hvc, hrel'⟩ := hrel.cons_perm (mem_unusedDomain_iff.mp hu) hv hgood
          ⟨hvc, mem_unusedDomain_iff.mpr huc, hrel'⟩

omit [AddGroup G] in
private theorem length_proj_idealLazyHandler_le {α : Type}
    (proj : Cache G × Cache G → Cache G) (cost : PermQuery G ⊕ PermQuery G → ℕ)
    (hstep_le : ∀ q st ans st', (ans, st') ∈ (idealLazyHandler q st).support →
      (proj st').length ≤ (proj st).length + cost q)
    {program : OracleComp (EvenMansourSpec G) α} {Q : ℕ}
    (h : IsCostBounded cost program Q) {st : Cache G × Cache G}
    {res : α × (Cache G × Cache G)}
    (hmem : res ∈ ((OracleComp.interpret idealLazyHandler program).run st).support) :
    (proj res.2).length ≤ (proj st).length + Q := by
  induction h generalizing st with
  | pure a n =>
    change res ∈ (PMF.pure (a, st)).support at hmem
    supp_cases hmem
    exact Nat.le_add_right _ _
  | liftBind q cont n hcost ih =>
    change res ∈ ((idealLazyHandler q st).bind fun p =>
      (OracleComp.interpret idealLazyHandler (cont p.1)).run p.2).support at hmem
    supp_cases hmem with ⟨⟨ans, st₁⟩, hstep, hcont⟩
    dsimp only at hcont
    have h1 := hstep_le q st ans st₁ hstep
    have h2 := ih ans hcont
    omega

omit [AddGroup G] in
private theorem length_fst_idealLazyHandler_le {α : Type}
    {program : OracleComp (EvenMansourSpec G) α} {Q_e : ℕ}
    (h : IsCostBounded cipherCost program Q_e) {c_e c_π : Cache G}
    {res : α × (Cache G × Cache G)}
    (hmem : res ∈ ((OracleComp.interpret idealLazyHandler program).run (c_e, c_π)).support) :
    res.2.1.length ≤ c_e.length + Q_e :=
  length_proj_idealLazyHandler_le Prod.fst cipherCost
    (fun
      | .inl _, ⟨_, _⟩, _, ⟨_, _⟩, hstep =>
        length_le_of_mem_answer_support (mem_support_idealLazyHandler_inl.mp hstep).1
      | .inr _, ⟨_, _⟩, _, ⟨_, _⟩, hstep =>
        (mem_support_idealLazyHandler_inr.mp hstep).2 ▸ le_rfl)
    h hmem

omit [AddGroup G] in
private theorem length_snd_idealLazyHandler_le {α : Type}
    {program : OracleComp (EvenMansourSpec G) α} {Q_π : ℕ}
    (h : IsCostBounded permCost program Q_π) {c_e c_π : Cache G}
    {res : α × (Cache G × Cache G)}
    (hmem : res ∈ ((OracleComp.interpret idealLazyHandler program).run (c_e, c_π)).support) :
    res.2.2.length ≤ c_π.length + Q_π :=
  length_proj_idealLazyHandler_le Prod.snd permCost
    (fun
      | .inl _, ⟨_, _⟩, _, ⟨_, _⟩, hstep =>
        (mem_support_idealLazyHandler_inl.mp hstep).2 ▸ le_rfl
      | .inr _, ⟨_, _⟩, _, ⟨_, _⟩, hstep =>
        length_le_of_mem_answer_support (mem_support_idealLazyHandler_inr.mp hstep).1)
    h hmem

omit [AddGroup G] [DecidableEq G] [Fintype G] [Nonempty G] in
private theorem preimage_beq_bool_singleton {α : Type*} (p : α → Bool) (b : Bool) :
    (fun x => p x == b) ⁻¹' {b} = {x | p x = true} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  cases b <;> cases p x <;> decide

private theorem evenMansourIdealGame_le_realLazy_add_bad
    (program : OracleComp (EvenMansourSpec G) Bool) (b : Bool) (k : G × G) :
    evenMansourIdealGame program b ≤
      (((OracleComp.interpret (realLazyHandler k) program).run []).map Prod.fst) b +
        (((OracleComp.interpret idealLazyHandler program).run ([], [])).map fun res =>
          isBadEvenMansourKey res.2.1 res.2.2 k == b) b := by
  let M_ideal := (OracleComp.interpret idealLazyHandler program).run ([], [])
  rw [evenMansourIdealGame_eq_lazy, ← PMF.toOuterMeasure_apply_singleton,
    ← PMF.toOuterMeasure_apply_singleton, ← PMF.toOuterMeasure_apply_singleton,
    PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply,
    preimage_beq_bool_singleton]
  have hsub : Prod.fst ⁻¹' ({b} : Set Bool) ⊆
      {(r, c_e', c_π') : Bool × Cache G × Cache G |
        r = b ∧ isBadEvenMansourKey c_e' c_π' k = false} ∪
      {res : Bool × (Cache G × Cache G) | isBadEvenMansourKey res.2.1 res.2.2 k = true} := by
    rintro ⟨r, c_e', c_π'⟩ hr
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hr
    cases hbad : isBadEvenMansourKey c_e' c_π' k
    · exact Or.inl ⟨hr, hbad⟩
    · exact Or.inr hbad
  exact ((MeasureTheory.measure_mono hsub).trans (MeasureTheory.measure_union_le _ _)).trans
    (add_le_add (run_idealLazyHandler_good_le_realLazyHandler program (· = b) k (cacheRel_nil k))
      le_rfl)

private theorem idealGame_apply_le_realGame_add_of_keyDist (keyDist : PMF (G × G))
    {program : OracleComp (EvenMansourSpec G) Bool} {Q_e Q_π : ℕ}
    (hcall : IsCallBounded program Q_e Q_π) {ε : ℝ≥0∞}
    (hbad_le : ∀ c_e c_π : Cache G, c_e.length ≤ Q_e → c_π.length ≤ Q_π →
      keyDist.toOuterMeasure {k | isBadEvenMansourKey c_e c_π k = true} ≤ ε)
    (b : Bool) :
    evenMansourIdealGame program b ≤
      ((PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
        keyDist.bind fun k => PMF.pure (evalEvenMansour π k.1 k.2 program)) b + ε := by
  let M_ideal := (OracleComp.interpret idealLazyHandler program).run ([], [])
  have hreal : (keyDist.bind fun k =>
      ((OracleComp.interpret (realLazyHandler k) program).run []).map Prod.fst) =
      ((PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
        keyDist.bind fun k => PMF.pure (evalEvenMansour π k.1 k.2 program)) := by
    pmf_hoist keyDist
    simp_rw [← realGameForKey_eq_lazy]
  have hbad : (keyDist.bind fun k =>
      M_ideal.map fun res => isBadEvenMansourKey res.2.1 res.2.2 k == b) b ≤ ε := by
    have hcomm : (keyDist.bind fun k =>
        M_ideal.map fun res => isBadEvenMansourKey res.2.1 res.2.2 k == b) =
      (M_ideal.bind fun res =>
        keyDist.map fun k => isBadEvenMansourKey res.2.1 res.2.2 k == b) := by
      simp only [PMF.map]
      pmf_swap
    rw [hcomm]
    refine Probability.PMF.bind_apply_le_on_support M_ideal fun res hmem => ?_
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      preimage_beq_bool_singleton]
    exact hbad_le res.2.1 res.2.2
      ((length_fst_idealLazyHandler_le hcall.1 hmem).trans (Nat.zero_add Q_e).le)
      ((length_snd_idealLazyHandler_le hcall.2 hmem).trans (Nat.zero_add Q_π).le)
  have hbind := Probability.PMF.bind_apply_le_add_on_support keyDist b fun k _ =>
    evenMansourIdealGame_le_realLazy_add_bad program b k
  rw [PMF.bind_const, hreal] at hbind
  exact hbind.trans (add_le_add le_rfl hbad)

private theorem advantage_le_of_forall_bool_le {g₁ g₂ : Game} {ε : ℝ≥0∞} (hε : ε ≠ ⊤)
    (hle : ∀ b : Bool, g₂ b ≤ g₁ b + ε) :
    (Game.advantage g₁ g₂ : ℝ) ≤ ε.toReal := by
  have htoReal (b : Bool) : (g₂ b).toReal ≤ (g₁ b).toReal + ε.toReal := by
    ennreal_to_real using hle b
  have h1 := PMF.sum_toReal g₁
  have h2 := PMF.sum_toReal g₂
  rw [Fintype.sum_bool] at h1 h2
  have ht := htoReal true
  have hf := htoReal false
  rw [Game.coe_advantage, Game.coe_succProbability, Game.coe_succProbability]
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

private theorem advantage_keyDist_evenMansourIdealGame_le (keyDist : PMF (G × G))
    {program : OracleComp (EvenMansourSpec G) Bool} {Q_e Q_π : ℕ}
    (hcall : IsCallBounded program Q_e Q_π)
    (hbad : ∀ c_e c_π : Cache G,
      keyDist.toOuterMeasure {k | isBadEvenMansourKey c_e c_π k = true} ≤
        2 * c_e.length * c_π.length * (Fintype.card G : ℝ≥0∞)⁻¹) :
    (Game.advantage
      ((PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
        keyDist.bind fun k => PMF.pure (evalEvenMansour π k.1 k.2 program))
      (evenMansourIdealGame program) : ℝ) ≤
      2 * (Q_e : ℝ) * (Q_π : ℝ) / (Fintype.card G : ℝ) := by
  let ε : ℝ≥0∞ := 2 * Q_e * Q_π * (Fintype.card G : ℝ≥0∞)⁻¹
  have hε : ε ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.natCast_ne_top _)) (ENNReal.natCast_ne_top _)) ?_
    simp [Fintype.card_ne_zero]
  have hle (b : Bool) := idealGame_apply_le_realGame_add_of_keyDist keyDist hcall
    (fun c_e c_π he hπ => (hbad c_e c_π).trans
      (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl (Nat.cast_le.mpr he))
        (Nat.cast_le.mpr hπ)) le_rfl)) b
  simpa [ε, ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv] using
    advantage_le_of_forall_bool_le hε hle

/-- **Deterministic Even–Mansour PRP security in the ideal-permutation model** ([BonehShoup2023],
Section 4.7, Theorem 4.14; [EvenMansour1997]): for any deterministic (coin-free) adaptive
distinguisher `program : OracleComp (EvenMansourSpec G) Bool` making at most `Q_e` cipher queries
and at most `Q_π` primitive permutation queries (`IsCallBounded program Q_e Q_π`), the
distinguishing advantage between `evenMansourRealGame program` and `evenMansourIdealGame program` is
at most `2 * Q_e * Q_π / |G|`. For randomized distinguishers (`ProbOracleComp`), see
`advantage_evenMansourProbRealGame_evenMansourProbIdealGame_le`. -/
theorem advantage_evenMansourRealGame_evenMansourIdealGame_le
    {program : OracleComp (EvenMansourSpec G) Bool} {Q_e Q_π : ℕ}
    (hcall : IsCallBounded program Q_e Q_π) :
    (Game.advantage (evenMansourRealGame program) (evenMansourIdealGame program) : ℝ) ≤
      2 * (Q_e : ℝ) * (Q_π : ℝ) / (Fintype.card G : ℝ) :=
  advantage_keyDist_evenMansourIdealGame_le (PMF.uniformOfFintype (G × G)) hcall
    toOuterMeasure_isBadEvenMansourKey_le

/-- **Deterministic single-key Even–Mansour PRP security in the ideal-permutation model**
([DunkelmanKellerShamir2012]): for any deterministic (coin-free) adaptive distinguisher
`program : OracleComp (EvenMansourSpec G) Bool` making at most `Q_e` cipher queries and at most
`Q_π` primitive permutation queries (`IsCallBounded program Q_e Q_π`), the distinguishing advantage
between `singleKeyEvenMansourRealGame program` and `evenMansourIdealGame program` is at most
`2 * Q_e * Q_π / |G|`. For randomized distinguishers (`ProbOracleComp`), see
`advantage_singleKeyEvenMansourProbRealGame_evenMansourProbIdealGame_le`. -/
theorem advantage_singleKeyEvenMansourRealGame_evenMansourIdealGame_le
    {program : OracleComp (EvenMansourSpec G) Bool} {Q_e Q_π : ℕ}
    (hcall : IsCallBounded program Q_e Q_π) :
    (Game.advantage (singleKeyEvenMansourRealGame program) (evenMansourIdealGame program) : ℝ) ≤
      2 * (Q_e : ℝ) * (Q_π : ℝ) / (Fintype.card G : ℝ) := by
  let keyDist : PMF (G × G) := (PMF.uniformOfFintype G).map fun k => (k, k)
  have hgame : ((PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
      keyDist.bind fun k => PMF.pure (evalEvenMansour π k.1 k.2 program)) =
      singleKeyEvenMansourRealGame program := by
    simp only [pmf_norm, keyDist, singleKeyEvenMansourRealGame]
  rw [← hgame]
  exact advantage_keyDist_evenMansourIdealGame_le keyDist hcall fun c_e c_π => by
    rw [PMF.toOuterMeasure_map_apply]
    exact toOuterMeasure_isBadSingleKeyEvenMansour_le c_e c_π

end Coupling

/-! ### Randomized (`ProbOracleComp`) ideal-permutation security via coin fixing -/

section ProbOracleSecurity

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]

omit [AddGroup G] [DecidableEq G] in
instance instFintypeEvenMansourSpec (q : PermQuery G ⊕ PermQuery G) :
    Fintype (EvenMansourSpec G q) := by
  cases q <;> exact inferInstanceAs (Fintype G)

/-- Answer a single `EvenMansourSpec G` query against cipher permutation `E` and primitive
permutation `π`. -/
def evalTwoPermsQuery (E π : Equiv.Perm G) (q : PermQuery G ⊕ PermQuery G) :
    EvenMansourSpec G q :=
  match q with
  | .inl qe => evalPerm E qe
  | .inr qπ => evalPerm π qπ

/-- Evaluate a randomized oracle program `ProbOracleComp (EvenMansourSpec G) α` against cipher
permutation `E` and primitive permutation `π`. -/
noncomputable def evalProbTwoPerms {α : Type} (E π : Equiv.Perm G)
    (program : ProbOracleComp (EvenMansourSpec G) α) : PMF α :=
  OracleComp.interpret
    (OracleComp.sumHandler ProbComp.unifOracle (fun q => PMF.pure (evalTwoPermsQuery E π q)))
    program

/-- A randomized adversary `program : ProbOracleComp (EvenMansourSpec G) α` makes at most `Q_e`
cipher queries and at most `Q_π` primitive permutation queries on every execution path, regardless
of its private coin choices. -/
def IsProbCallBounded {α : Type} (program : ProbOracleComp (EvenMansourSpec G) α) (Q_e Q_π : ℕ) :
    Prop :=
  OracleComp.IsCostBounded (Sum.elim (fun _ => 0) cipherCost) program Q_e ∧
    OracleComp.IsCostBounded (Sum.elim (fun _ => 0) permCost) program Q_π

omit [AddGroup G] [Fintype G] [DecidableEq G] in
/-- Fixing the private coins `ω` of a randomized `(Q_e, Q_π)`-call-bounded distinguisher yields a
deterministic distinguisher satisfying `IsCallBounded _ Q_e Q_π`. -/
theorem IsProbCallBounded.fixCoins {α : Type}
    {program : ProbOracleComp (EvenMansourSpec G) α} {Q_e Q_π : ℕ}
    (h : IsProbCallBounded program Q_e Q_π) (ω : ProbOracleComp.Coins program) :
    IsCallBounded (ProbOracleComp.fixCoins program ω) Q_e Q_π :=
  ⟨ProbOracleComp.isCostBounded_fixCoins h.1 ω, ProbOracleComp.isCostBounded_fixCoins h.2 ω⟩

omit [AddGroup G] [Fintype G] [DecidableEq G] in
/-- A closed probabilistic sample makes `0` cipher queries and `0` primitive queries. -/
theorem isProbCallBounded_sample {α : Type} (p : ProbComp α) :
    IsProbCallBounded (ProbOracleComp.sample (spec := EvenMansourSpec G) p) 0 0 :=
  ⟨ProbOracleComp.isCostBounded_sample cipherCost p,
   ProbOracleComp.isCostBounded_sample permCost p⟩

omit [AddGroup G] [Fintype G] [DecidableEq G] in
/-- Lifting a deterministic `IsCallBounded` program to `ProbOracleComp` preserves its `(Q_e, Q_π)`
query budgets. -/
theorem IsProbCallBounded.of_isCallBounded {α : Type}
    {program : OracleComp (EvenMansourSpec G) α} {Q_e Q_π : ℕ}
    (h : IsCallBounded program Q_e Q_π) :
    IsProbCallBounded (OracleComp.interpret (fun q => ProbOracleComp.query q) program) Q_e Q_π :=
  ⟨ProbOracleComp.isCostBounded_interpret_query h.1,
   ProbOracleComp.isCostBounded_interpret_query h.2⟩

omit [AddGroup G] [Fintype G] [DecidableEq G] in
/-- Any randomized program making at most `Q` total external queries satisfies
`IsProbCallBounded program Q Q`. -/
theorem IsProbCallBounded.of_isQueryBounded {α : Type}
    {program : ProbOracleComp (EvenMansourSpec G) α} {Q : ℕ}
    (hQ : program.IsQueryBounded Q) : IsProbCallBounded program Q Q :=
  ⟨hQ.of_le (by rintro (_ | (_ | _)) <;> simp [cipherCost]),
   hQ.of_le (by rintro (_ | (_ | _)) <;> simp [permCost])⟩

/-- The real two-key Even–Mansour game for a randomized distinguisher
`program : ProbOracleComp (EvenMansourSpec G) Bool`. -/
noncomputable def evenMansourProbRealGame
    (program : ProbOracleComp (EvenMansourSpec G) Bool) : Game := do
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  let k ← PMF.uniformOfFintype (G × G)
  evalProbTwoPerms (evenMansourEquiv π k.1 k.2) π program

/-- The real single-key Even–Mansour game for a randomized distinguisher
`program : ProbOracleComp (EvenMansourSpec G) Bool`. -/
noncomputable def singleKeyEvenMansourProbRealGame
    (program : ProbOracleComp (EvenMansourSpec G) Bool) : Game := do
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  let k ← PMF.uniformOfFintype G
  evalProbTwoPerms (singleKeyEvenMansourEquiv π k) π program

/-- The ideal Even–Mansour game for a randomized distinguisher
`program : ProbOracleComp (EvenMansourSpec G) Bool`: two independent uniform permutations
`E, π ← Equiv.Perm G`. -/
noncomputable def evenMansourProbIdealGame
    (program : ProbOracleComp (EvenMansourSpec G) Bool) : Game := do
  let E ← PMF.uniformOfFintype (Equiv.Perm G)
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  evalProbTwoPerms E π program

omit [AddGroup G] [Fintype G] [DecidableEq G] in
private theorem interpret_evalTwoPermsQuery_eq_pure_evalTwoPerms {α : Type} (E π : Equiv.Perm G)
    (program : OracleComp (EvenMansourSpec G) α) :
    OracleComp.interpret (fun q => PMF.pure (evalTwoPermsQuery E π q)) program =
      PMF.pure (evalTwoPerms E π program) := by
  rw [pure_evalTwoPerms]
  congr 1; funext q; cases q <;> rfl

omit [AddGroup G] [DecidableEq G] in
private theorem probGame_eq_coinLaw_bind {P : Type*} (μ : PMF P)
    (E π : P → Equiv.Perm G) (program : ProbOracleComp (EvenMansourSpec G) Bool) :
    (μ.bind fun p => evalProbTwoPerms (E p) (π p) program) =
      (ProbOracleComp.coinLaw program).bind fun ω =>
        μ.bind fun p =>
          PMF.pure (evalTwoPerms (E p) (π p) (ProbOracleComp.fixCoins program ω)) := by
  simpa only [evalProbTwoPerms, interpret_evalTwoPermsQuery_eq_pure_evalTwoPerms] using
    ProbOracleComp.table_bind_interpret_eq_coinLaw_bind μ
      (fun p => evalTwoPermsQuery (E p) (π p)) program

/-- Coin-fixing decomposition of `evenMansourProbRealGame`: sampling `(π, k)` independently of
`program`'s private coins equals averaging the deterministic `evenMansourRealGame` over
`ProbOracleComp.coinLaw program`. -/
theorem evenMansourProbRealGame_eq_coinLaw_bind
    (program : ProbOracleComp (EvenMansourSpec G) Bool) :
    evenMansourProbRealGame program =
      (ProbOracleComp.coinLaw program).bind fun ω =>
        evenMansourRealGame (ProbOracleComp.fixCoins program ω) := by
  simpa only [evenMansourProbRealGame, evenMansourRealGame, evalEvenMansour, pmf_norm] using
    probGame_eq_coinLaw_bind
      ((PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
        (PMF.uniformOfFintype (G × G)).map fun k => (π, k))
      (fun p => evenMansourEquiv p.1 p.2.1 p.2.2) Prod.fst program

/-- Coin-fixing decomposition of `singleKeyEvenMansourProbRealGame`: sampling `(π, k)`
independently of `program`'s private coins equals averaging the deterministic
`singleKeyEvenMansourRealGame` over `ProbOracleComp.coinLaw program`. -/
theorem singleKeyEvenMansourProbRealGame_eq_coinLaw_bind
    (program : ProbOracleComp (EvenMansourSpec G) Bool) :
    singleKeyEvenMansourProbRealGame program =
      (ProbOracleComp.coinLaw program).bind fun ω =>
        singleKeyEvenMansourRealGame (ProbOracleComp.fixCoins program ω) := by
  simpa only [singleKeyEvenMansourProbRealGame, singleKeyEvenMansourRealGame, evalEvenMansour,
    pmf_norm] using
    probGame_eq_coinLaw_bind
      ((PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
        (PMF.uniformOfFintype G).map fun k => (π, k))
      (fun p => singleKeyEvenMansourEquiv p.1 p.2) Prod.fst program

omit [AddGroup G] in
/-- Coin-fixing decomposition of `evenMansourProbIdealGame`: sampling `(E, π)` independently of
`program`'s private coins equals averaging the deterministic `evenMansourIdealGame` over
`ProbOracleComp.coinLaw program`. -/
theorem evenMansourProbIdealGame_eq_coinLaw_bind
    (program : ProbOracleComp (EvenMansourSpec G) Bool) :
    evenMansourProbIdealGame program =
      (ProbOracleComp.coinLaw program).bind fun ω =>
        evenMansourIdealGame (ProbOracleComp.fixCoins program ω) := by
  simpa only [evenMansourProbIdealGame, evenMansourIdealGame, pmf_norm] using
    probGame_eq_coinLaw_bind
      ((PMF.uniformOfFintype (Equiv.Perm G)).bind fun E =>
        (PMF.uniformOfFintype (Equiv.Perm G)).map fun π => (E, π))
      Prod.fst Prod.snd program

/-- **Even–Mansour PRP security in the ideal-permutation model** ([EvenMansour1997];
[BonehShoup2023], Section 4.7, Theorem 4.14; [KatzLindell2020]): for any randomized adaptive
distinguisher `program : ProbOracleComp (EvenMansourSpec G) Bool` making at most `Q_e` cipher
queries and at most `Q_π` primitive permutation queries (`IsProbCallBounded program Q_e Q_π`), the
distinguishing advantage between `evenMansourProbRealGame program` and
`evenMansourProbIdealGame program` is at most `2 * Q_e * Q_π / |G|`. -/
theorem advantage_evenMansourProbRealGame_evenMansourProbIdealGame_le
    {program : ProbOracleComp (EvenMansourSpec G) Bool} {Q_e Q_π : ℕ}
    (hcall : IsProbCallBounded program Q_e Q_π) :
    (Game.advantage (evenMansourProbRealGame program) (evenMansourProbIdealGame program) : ℝ) ≤
      2 * (Q_e : ℝ) * (Q_π : ℝ) / (Fintype.card G : ℝ) := by
  rw [evenMansourProbRealGame_eq_coinLaw_bind, evenMansourProbIdealGame_eq_coinLaw_bind]
  refine Game.advantage_bind_le _ _ _ fun ω => ?_
  exact advantage_evenMansourRealGame_evenMansourIdealGame_le (hcall.fixCoins ω)

/-- **Single-key Even–Mansour PRP security in the ideal-permutation model**
([DunkelmanKellerShamir2012]; [BonehShoup2023], Section 4.7): for any randomized adaptive
distinguisher `program : ProbOracleComp (EvenMansourSpec G) Bool` making at most `Q_e` cipher
queries and at most `Q_π` primitive permutation queries (`IsProbCallBounded program Q_e Q_π`), the
distinguishing advantage between `singleKeyEvenMansourProbRealGame program` and
`evenMansourProbIdealGame program` is at most `2 * Q_e * Q_π / |G|`. -/
theorem advantage_singleKeyEvenMansourProbRealGame_evenMansourProbIdealGame_le
    {program : ProbOracleComp (EvenMansourSpec G) Bool} {Q_e Q_π : ℕ}
    (hcall : IsProbCallBounded program Q_e Q_π) :
    (Game.advantage (singleKeyEvenMansourProbRealGame program)
      (evenMansourProbIdealGame program) : ℝ) ≤
      2 * (Q_e : ℝ) * (Q_π : ℝ) / (Fintype.card G : ℝ) := by
  rw [singleKeyEvenMansourProbRealGame_eq_coinLaw_bind, evenMansourProbIdealGame_eq_coinLaw_bind]
  refine Game.advantage_bind_le _ _ _ fun ω => ?_
  exact advantage_singleKeyEvenMansourRealGame_evenMansourIdealGame_le (hcall.fixCoins ω)

end ProbOracleSecurity

private theorem advantage_bitString_of_card_le {n Q_e Q_π : ℕ} {g₁ g₂ : Game}
    (h : (Game.advantage g₁ g₂ : ℝ) ≤
      2 * (Q_e : ℝ) * (Q_π : ℝ) / (Fintype.card (BitString n) : ℝ)) :
    (Game.advantage g₁ g₂ : ℝ) ≤ 2 * (Q_e : ℝ) * (Q_π : ℝ) / (2 : ℝ) ^ n := by
  simpa only [Fintype.card_pi, Fintype.card_fin, Fintype.card_bool, Finset.prod_const,
    Finset.card_univ, Nat.cast_pow, Nat.cast_ofNat] using h

/-- Specialization of `advantage_evenMansourProbRealGame_evenMansourProbIdealGame_le` to `n`-bit
strings `BitString n`: the distinguishing advantage is at most `2 * Q_e * Q_π / 2 ^ n`. -/
theorem advantage_evenMansourProbRealGame_bitString_le {n Q_e Q_π : ℕ}
    {program : ProbOracleComp (EvenMansourSpec (BitString n)) Bool}
    (hcall : IsProbCallBounded program Q_e Q_π) :
    (Game.advantage (evenMansourProbRealGame program) (evenMansourProbIdealGame program) : ℝ) ≤
      2 * (Q_e : ℝ) * (Q_π : ℝ) / (2 : ℝ) ^ n :=
  advantage_bitString_of_card_le
    (advantage_evenMansourProbRealGame_evenMansourProbIdealGame_le hcall)

/-- Specialization of `advantage_singleKeyEvenMansourProbRealGame_evenMansourProbIdealGame_le` to
`n`-bit strings `BitString n`: the distinguishing advantage is at most `2 * Q_e * Q_π / 2 ^ n`. -/
theorem advantage_singleKeyEvenMansourProbRealGame_bitString_le {n Q_e Q_π : ℕ}
    {program : ProbOracleComp (EvenMansourSpec (BitString n)) Bool}
    (hcall : IsProbCallBounded program Q_e Q_π) :
    (Game.advantage (singleKeyEvenMansourProbRealGame program)
      (evenMansourProbIdealGame program) : ℝ) ≤
      2 * (Q_e : ℝ) * (Q_π : ℝ) / (2 : ℝ) ^ n :=
  advantage_bitString_of_card_le
    (advantage_singleKeyEvenMansourProbRealGame_evenMansourProbIdealGame_le hcall)

end Cslib.Crypto.EvenMansour
