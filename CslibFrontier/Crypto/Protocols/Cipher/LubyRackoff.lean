/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game
public import CslibFrontier.Crypto.Primitives.PRF.MultiKey
public import CslibFrontier.Crypto.Primitives.PRP.Finite
public import CslibFrontier.Foundations.Data.BitString.Basic
public import CslibFrontier.Languages.Probabilistic.QueryCount
public import CslibFrontier.Probability.HashFamily
public import CslibFrontier.Probability.HashFamily.Uniform
public import Mathlib.Data.Fintype.Perm
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.CoinFixing
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.QueryCount
import CslibFrontier.Languages.Probabilistic.QueryCount.Scale
import CslibFrontier.Languages.Probabilistic.RandomOracle
import CslibFrontier.Languages.Probabilistic.RandomPermutation
import CslibFrontier.Languages.Probabilistic.Simulation
import CslibFrontier.Languages.Probabilistic.UntilBad
import CslibFrontier.Languages.Probabilistic.UntilBad.ChooseTwo
import CslibFrontier.Languages.Probabilistic.UntilBad.Flag
import CslibFrontier.Probability.BitString
import CslibFrontier.Probability.IID
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.SupportTsum
import CslibFrontier.Probability.PMF.Union
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Probability.Uniform
import CslibFrontier.Tactic.ENNRealToReal
import CslibFrontier.Tactic.GameHop
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.SuppCases
import CslibFrontier.Tactic.UniformRelabel
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Feistel networks and the Luby–Rackoff theorem

A Feistel round ([BonehShoup2023], Section 4.5; [LubyRackoff1988]) turns an arbitrary function
`f : G → G` on an additive group `G` into a bijection `feistelRoundEquiv f : G × G ≃ G × G` mapping
`(L, R)` to `(R, L + f R)` with explicit inverse `(L', R') ↦ (R' - f L', L')` requiring no
invertibility of `f`. Composing a list of round functions yields the multi-round Feistel cipher
`feistelNetwork`, specialized to the three-round (`feistel3`) and four-round (`feistel4`) networks.
Over any group of exponent two (`∀ x : G, -x = x`, including `BitString n`), swapping the two
halves (`Equiv.prodComm G G`) conjugates `feistelNetwork fs.reverse` to the inverse cipher
`(feistelNetwork fs).symm`.

We prove the **Luby–Rackoff theorem** ([BonehShoup2023], Section 4.5, Theorem 4.9;
[LubyRackoff1988]):

1. **Information-theoretic core with Δ-universal Round 1**: when the first round function is drawn
   from an `ε`-almost-Δ-universal family (`IsDeltaUniversalHash seed₁ h₁ ε`) and the second and
   third round functions are independent uniform random functions on `G`, any adaptive adversary
   `program : OracleComp (fun _ : G × G => G × G) Bool` making at most `Q` queries
   (`IsQueryBounded program Q`) distinguishes the three-round Feistel network from a uniform random
   function on `G × G` with advantage at most
   $$\binom{Q}{2} \cdot \varepsilon + \binom{Q}{2} \cdot \frac{1}{|G|}$$
   (`advantage_feistel3HashIdealGame_randomFunctionGame_le`).
2. **Classical three-round information-theoretic bound**: a uniform random function on `G` is
   `|G|⁻¹`-Δ-universal (`isDeltaUniversalHash_uniformOfFintype`), so three independent uniform
   random round functions have distinguishing advantage against a uniform random function on
   `G × G` at most
   $$\frac{2 \binom{Q}{2}}{|G|} = \frac{Q (Q - 1)}{|G|}$$
   (`advantage_feistel3RandomRoundsGame_randomFunctionGame_le`).
3. **PRP switching and the keyed three-round cipher**: the PRP/PRF switching bound on `G × G`
   (`advantage_idealPermGame_randomFunctionGame_le`) yields the pseudorandom-permutation bounds
   against `idealPermGame` (`advantage_feistel3HashIdealGame_idealPermGame_le`,
   `advantage_feistel3RandomRoundsGame_idealPermGame_le`). For the cipher `feistel3Cipher F`
   with three independent uniform keys of a finite round function `F : K → G → G`, and any
   `Q`-query adversary `A` with private coins in the finite PRF/PRP experiments of
   `Cslib.Crypto.PRF` and `Cslib.Crypto.PRP`,
   $$\mathrm{PRPadv}[A] \le \sum_{j < 3} \mathrm{PRFadv}[B_j] + \frac{2 \binom{Q}{2}}{|G|} +
   \frac{\binom{Q}{2}}{|G|^2}$$
   (`prpAdvantage_feistel3Cipher_le`, and `prfAdvantage_feistel3Cipher_le` against a random
   function). Here `B_j = feistel3Reduction F j A` is one explicit randomized PRF adversary:
   the `j`-th hybrid reduction of the multi-key PRF hybrid (`PRF.multiKeyReduction`) applied to
   the stateless adapter `feistel3MultiKeyAdversary A`. It samples its own keys for the rounds
   after round `j + 1`, forwards round `j + 1` to its PRF challenger, and lazily samples the
   rounds before it with a cache. This is the hybrid argument of [BonehShoup2023], Exercise 4.26,
   which the proof of Theorem 4.9 uses for the three round keys. It makes at most
   `3 * Q` queries (`isQueryBounded_feistel3Reduction`). Fixing the private coins of `A`
   transfers the random-round bounds to randomized adversaries
   (`advantage_feistel3RandomRounds_prfIdealExperiment_le`,
   `advantage_feistel3RandomRounds_prpIdealExperiment_le`).
4. **Three-round chosen-ciphertext separation ([BonehShoup2023], Section 4.1.3 and
   Exercise 4.15(b))**: with two forward
   encryption queries and one inverse decryption query, the explicit distinguisher
   `feistel3CCAAttack` accepts any three-round Feistel network with probability `1`
   (`eval_feistel3_feistel3CCAAttack`). When `l₀ = l₁`, the third query asks to invert the first
   ciphertext, so every bidirectional permutation (`feistelStrongOracle π`) and `idealStrongGame`
   also accept with probability `1` (`eval_feistelStrongOracle_feistel3CCAAttack_self`,
   `idealStrongGame_feistel3CCAAttack_self`, `advantage_feistel3CCAAttack_self`). Whenever
   `l₀ ≠ l₁`, coupling `idealStrongGame` with the forgetful bidirectional lazy sampler shows that
   `idealStrongGame` accepts `feistel3CCAAttack l₀ l₁ r₀` with probability at most
   `|G|⁻¹ + 4 * |G × G|⁻¹` (`idealStrongGame_feistel3CCAAttack_true_le`), giving the quantitative
   nonnegligible chosen-ciphertext advantage lower bound
   `1 - |G|⁻¹ - 4 * |G|⁻¹ ^ 2` against `idealStrongGame`
   (`le_advantage_feistel3CCAAttack_idealStrongGame_of_ne`). In addition, when `G` has three
   distinct elements `l₀, l₁, l₂` (`|G| ≥ 3`), the transposition
   `Equiv.swap (l₀, (l₁ - l₀) + r₀) (l₂, r₀)` is rejected deterministically
   (`eval_feistelStrongOracle_swap_feistel3CCAAttack_eq_false`,
   `le_advantage_feistel3CCAAttack_idealStrongGame`,
   `advantage_feistel3CCAAttack_idealStrongGame_pos`), and against the independent-table
   bidirectional benchmark `independentTableStrongGame`, `feistel3CCAAttack l₀ l₁ r₀` accepts with
   probability `|G|⁻¹` and has exact advantage `1 - |G|⁻¹`
   (`eval_independentTableStrongGame_feistel3CCAAttack`,
   `advantage_feistel3CCAAttack_independentTable`).
5. **Four-round strong PRP Luby–Rackoff theorem ([LubyRackoff1988]; see [BonehShoup2023],
   Section 4.1.3 for strongly secure block ciphers)**: when all four round functions
   `f₁, f₂, f₃, f₄ : G → G` are independent uniform random functions, coupling the inner rounds
   `f₂, f₃` to the forgetful bidirectional lazy sampler on `G × G` and bounding outer-round
   collisions for `f₁` (Round 1) and `-f₄` (Round 4 on the swapped cache) shows that any `Q`-query
   adaptive chosen-ciphertext distinguisher has advantage against `idealStrongGame` at most
   $$2 \binom{Q}{2} \cdot \frac{1}{|G|} + 2 \binom{Q}{2} \cdot \frac{1}{|G|^2}$$
   (with the concrete constant coming from this proof;
   `feistel4StrongRandomRoundsGame_apply_le`,
   `idealStrongGame_apply_le_feistel4StrongRandomRoundsGame`,
   `advantage_feistel4StrongRandomRoundsGame_idealStrongGame_le`,
   `advantage_feistel4StrongRandomRoundsGame_bitString_le`). For the cipher `feistel4Cipher F`
   with four independent uniform keys and any `Q`-query chosen-ciphertext adversary `A` with
   private coins, the strong PRP advantage is at most the sum of the PRF advantages of the four
   explicit hybrid reductions `feistel4StrongReduction F j A` plus this bound
   (`strongAdvantage_feistel4Cipher_le`). The bidirectional adapter
   `feistel4StrongMultiKeyAdversary` evaluates inverse queries with the round functions forwards,
   so each reduction again needs only forward PRF access.

## Main definitions

* `Cslib.Crypto.LubyRackoff.feistelRound`, `feistelInvRound`, `feistelRoundEquiv`: single Feistel
  round and its bundled equivalence over `[AddGroup G]`.
* `Cslib.Crypto.LubyRackoff.feistelNetwork`, `feistel3`, `feistel4`: multi-round, 3-round, and
  4-round Feistel permutations.
* `Cslib.Crypto.LubyRackoff.feistel3FixedGame`, `feistel3HashIdealGame`,
  `feistel3RandomRoundsGame`, `randomFunctionGame`, `idealPermGame`: 3-round Feistel, ideal
  random-function, and ideal random-permutation games for coin-free programs.
* `Cslib.Crypto.LubyRackoff.feistelStrongOracle`, `idealStrongGame`,
  `independentTableStrongGame`, `feistel4StrongRandomRoundsGame`, `feistel3CCAAttack`:
  bidirectional (forward + inverse) oracle games and the 3-query CCA attack on 3-round Feistel.
* `Cslib.Crypto.LubyRackoff.feistel3Cipher`, `feistel3ChannelQuery`, `feistel3MultiKeyAdversary`,
  `feistel3Reduction`: the keyed three-round cipher, its three-channel adapter, and its hybrid
  PRF reductions.
* `Cslib.Crypto.LubyRackoff.feistel4Cipher`, `feistel4StrongChannelQuery`,
  `feistel4StrongMultiKeyAdversary`, `feistel4StrongReduction`: the keyed four-round cipher, its
  bidirectional four-channel adapter, and its hybrid PRF reductions.

## Main results

* `Cslib.Crypto.LubyRackoff.prodComm_trans_feistelNetwork_reverse_trans_prodComm`: swap-reversal
  conjugation identity for Feistel decryption over groups of exponent two.
* `Cslib.Probability.isDeltaUniversalHash_uniformOfFintype`,
  `Cslib.Probability.isDeltaUniversalHash_neg_uniformOfFintype`: a uniform random function
  into `G` and its negation are `|G|⁻¹`-Δ-universal.
* `Cslib.Crypto.LubyRackoff.feistel3HashIdealGame_apply_le`,
  `Cslib.Crypto.LubyRackoff.randomFunctionGame_apply_le_feistel3HashIdealGame`: two-sided
  probability comparisons for 3-round Luby–Rackoff with Δ-universal Round 1.
* `Cslib.Crypto.LubyRackoff.advantage_feistel3HashIdealGame_randomFunctionGame_le`,
  `Cslib.Crypto.LubyRackoff.advantage_feistel3HashIdealGame_idealPermGame_le`: 3-round
  Luby–Rackoff bounds with Δ-universal Round 1 against `randomFunctionGame` and `idealPermGame`.
* `Cslib.Crypto.LubyRackoff.advantage_feistel3RandomRoundsGame_randomFunctionGame_le`,
  `Cslib.Crypto.LubyRackoff.advantage_feistel3RandomRoundsGame_idealPermGame_le`: 3-round
  Luby–Rackoff bounds with three uniform random round functions.
* `Cslib.Crypto.LubyRackoff.prfAdvantage_feistel3Cipher_le`,
  `Cslib.Crypto.LubyRackoff.prpAdvantage_feistel3Cipher_le`: Boneh–Shoup Theorem 4.9 for the
  keyed three-round cipher, with the PRF advantages of explicit hybrid reductions.
* `Cslib.Crypto.LubyRackoff.isQueryBounded_feistel3Reduction`,
  `Cslib.Crypto.LubyRackoff.isQueryBounded_feistel4StrongReduction`: the reductions make at most
  three (four) queries per query of the adversary.
* `Cslib.Crypto.LubyRackoff.advantage_feistel3RandomRounds_prfIdealExperiment_le`,
  `Cslib.Crypto.LubyRackoff.advantage_feistel3RandomRounds_prpIdealExperiment_le`,
  `Cslib.Crypto.LubyRackoff.advantage_feistel4StrongRandomRounds_strongIdealExperiment_le`:
  the random-round bounds for adversaries with private coins.
* `Cslib.Crypto.LubyRackoff.feistel4StrongRandomRoundsGame_apply_le`,
  `Cslib.Crypto.LubyRackoff.idealStrongGame_apply_le_feistel4StrongRandomRoundsGame`,
  `Cslib.Crypto.LubyRackoff.advantage_feistel4StrongRandomRoundsGame_idealStrongGame_le`,
  `Cslib.Crypto.LubyRackoff.advantage_feistel4StrongRandomRoundsGame_bitString_le`:
  information-theoretic 4-round random-round collision bound.
* `Cslib.Crypto.LubyRackoff.strongAdvantage_feistel4Cipher_le`: the 4-round strong
  Luby–Rackoff theorem for the keyed cipher, with the PRF advantages of explicit hybrid
  reductions.
* `Cslib.Crypto.LubyRackoff.eval_feistel3_feistel3CCAAttack`,
  `Cslib.Crypto.LubyRackoff.advantage_feistel3CCAAttack_self`,
  `Cslib.Crypto.LubyRackoff.idealStrongGame_feistel3CCAAttack_true_le`,
  `Cslib.Crypto.LubyRackoff.le_advantage_feistel3CCAAttack_idealStrongGame_of_ne`,
  `Cslib.Crypto.LubyRackoff.le_advantage_feistel3CCAAttack_idealStrongGame`,
  `Cslib.Crypto.LubyRackoff.advantage_feistel3CCAAttack_independentTable`: the 3-query CCA
  distinguisher against 3-round Feistel.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 4.1.3 and 4.5 (Theorem 4.9 and Exercise 4.15(b)), and
  Exercise 4.26 (parallel composition of PRFs).
* [M. Luby, C. Rackoff, *How to Construct Pseudorandom Permutations from Pseudorandom
  Functions*][LubyRackoff1988].
-/

@[expose] public section

namespace Cslib.Crypto.LubyRackoff

open Cslib.Probability
open scoped ENNReal NNReal

/-! ### Algebraic Feistel permutations -/

section Algebraic

variable {G : Type*} [AddGroup G]

/-- One Feistel round `(L, R) ↦ (R, L + f R)` over an additive group `G`. -/
def feistelRound (f : G → G) (p : G × G) : G × G :=
  (p.2, p.1 + f p.2)

/-- The inverse of one Feistel round `(L', R') ↦ (R' - f L', L')`, requiring no invertibility of
`f`. -/
def feistelInvRound (f : G → G) (p : G × G) : G × G :=
  (p.2 - f p.1, p.1)

@[simp]
theorem feistelRound_fst (f : G → G) (p : G × G) : (feistelRound f p).1 = p.2 := rfl

@[simp]
theorem feistelRound_snd (f : G → G) (p : G × G) : (feistelRound f p).2 = p.1 + f p.2 := rfl

@[simp]
theorem feistelInvRound_fst (f : G → G) (p : G × G) : (feistelInvRound f p).1 = p.2 - f p.1 :=
  rfl

@[simp]
theorem feistelInvRound_snd (f : G → G) (p : G × G) : (feistelInvRound f p).2 = p.1 := rfl

@[simp]
theorem feistelInvRound_feistelRound (f : G → G) (p : G × G) :
    feistelInvRound f (feistelRound f p) = p := by
  ext <;> simp [feistelRound, feistelInvRound]

@[simp]
theorem feistelRound_feistelInvRound (f : G → G) (p : G × G) :
    feistelRound f (feistelInvRound f p) = p := by
  ext <;> simp [feistelRound, feistelInvRound]

/-- A single Feistel round as a permutation of `G × G`. -/
def feistelRoundEquiv (f : G → G) : G × G ≃ G × G where
  toFun := feistelRound f
  invFun := feistelInvRound f
  left_inv := feistelInvRound_feistelRound f
  right_inv := feistelRound_feistelInvRound f

@[simp]
theorem feistelRoundEquiv_apply (f : G → G) (p : G × G) :
    feistelRoundEquiv f p = feistelRound f p := rfl

@[simp]
theorem feistelRoundEquiv_symm_apply (f : G → G) (p : G × G) :
    (feistelRoundEquiv f).symm p = feistelInvRound f p := rfl

/-- Multi-round Feistel network composing a list of round functions from left to right. -/
def feistelNetwork (fs : List (G → G)) : G × G ≃ G × G :=
  fs.foldl (fun e f => e.trans (feistelRoundEquiv f)) (Equiv.refl (G × G))

@[simp]
theorem feistelNetwork_nil : feistelNetwork ([] : List (G → G)) = Equiv.refl (G × G) := rfl

@[simp]
theorem feistelNetwork_singleton (f : G → G) :
    feistelNetwork [f] = feistelRoundEquiv f := rfl

private theorem foldl_feistelRoundEquiv (e : G × G ≃ G × G) (fs : List (G → G)) :
    fs.foldl (fun acc f => acc.trans (feistelRoundEquiv f)) e =
      e.trans (feistelNetwork fs) := by
  induction fs generalizing e with
  | nil => rfl
  | cons f rest ih =>
    simp only [List.foldl_cons, feistelNetwork, Equiv.refl_trans]
    rw [ih (e.trans (feistelRoundEquiv f)), ih (feistelRoundEquiv f)]
    rfl

@[simp]
theorem feistelNetwork_cons (f : G → G) (fs : List (G → G)) :
    feistelNetwork (f :: fs) = (feistelRoundEquiv f).trans (feistelNetwork fs) := by
  simp only [feistelNetwork, List.foldl_cons, Equiv.refl_trans]
  exact foldl_feistelRoundEquiv (feistelRoundEquiv f) fs

theorem feistelNetwork_append (fs₁ fs₂ : List (G → G)) :
    feistelNetwork (fs₁ ++ fs₂) = (feistelNetwork fs₁).trans (feistelNetwork fs₂) := by
  induction fs₁ with
  | nil => rfl
  | cons f rest ih =>
    simp only [List.cons_append, feistelNetwork_cons, ih]
    rfl

/-- Over any group of exponent two (`∀ x : G, -x = x`), swapping the two halves conjugates one
Feistel round to its inverse. -/
theorem prodComm_trans_feistelRoundEquiv_trans_prodComm
    (hneg : ∀ x : G, -x = x) (f : G → G) :
    (Equiv.prodComm G G).trans ((feistelRoundEquiv f).trans (Equiv.prodComm G G)) =
      (feistelRoundEquiv f).symm := by
  ext ⟨a, b⟩ <;> simp [feistelRound, feistelInvRound, sub_eq_add_neg, hneg]

/-- Over any group of exponent two (`∀ x : G, -x = x`), Feistel decryption is Feistel encryption
with the round functions in reverse order, conjugated by swapping the two halves. -/
theorem prodComm_trans_feistelNetwork_reverse_trans_prodComm
    (hneg : ∀ x : G, -x = x) (fs : List (G → G)) :
    (Equiv.prodComm G G).trans ((feistelNetwork fs.reverse).trans (Equiv.prodComm G G)) =
      (feistelNetwork fs).symm := by
  induction fs with
  | nil =>
    ext ⟨a, b⟩ <;> rfl
  | cons f rest ih =>
    rw [List.reverse_cons, feistelNetwork_append, feistelNetwork_singleton, feistelNetwork_cons]
    refine Equiv.ext fun p => ?_
    have hround := Equiv.congr_fun (prodComm_trans_feistelRoundEquiv_trans_prodComm hneg f)
      ((feistelNetwork rest).symm p)
    have hrest := Equiv.congr_fun ih p
    simp only [Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.prodComm_apply] at hround hrest ⊢
    rw [← hround, ← hrest, Prod.swap_swap]

/-- The three-round Feistel permutation `(feistelRoundEquiv f₁).trans ((feistelRoundEquiv f₂).trans
(feistelRoundEquiv f₃))`. -/
def feistel3 (f₁ f₂ f₃ : G → G) : G × G ≃ G × G :=
  (feistelRoundEquiv f₁).trans ((feistelRoundEquiv f₂).trans (feistelRoundEquiv f₃))

/-- The four-round Feistel permutation `(feistel3 f₁ f₂ f₃).trans (feistelRoundEquiv f₄)`. -/
def feistel4 (f₁ f₂ f₃ f₄ : G → G) : G × G ≃ G × G :=
  (feistel3 f₁ f₂ f₃).trans (feistelRoundEquiv f₄)

theorem feistelNetwork_three (f₁ f₂ f₃ : G → G) :
    feistelNetwork [f₁, f₂, f₃] = feistel3 f₁ f₂ f₃ := rfl

theorem feistelNetwork_four (f₁ f₂ f₃ f₄ : G → G) :
    feistelNetwork [f₁, f₂, f₃, f₄] = feistel4 f₁ f₂ f₃ f₄ := rfl

theorem feistel3_apply (f₁ f₂ f₃ : G → G) (p : G × G) :
    feistel3 f₁ f₂ f₃ p =
      (p.2 + f₂ (p.1 + f₁ p.2), (p.1 + f₁ p.2) + f₃ (p.2 + f₂ (p.1 + f₁ p.2))) := rfl

theorem feistel3_symm_apply (f₁ f₂ f₃ : G → G) (vw : G × G) :
    (feistel3 f₁ f₂ f₃).symm vw =
      ((vw.2 - f₃ vw.1) - f₁ (vw.1 - f₂ (vw.2 - f₃ vw.1)),
        vw.1 - f₂ (vw.2 - f₃ vw.1)) := rfl

theorem feistel4_apply (f₁ f₂ f₃ f₄ : G → G) (p : G × G) :
    feistel4 f₁ f₂ f₃ f₄ p = feistelRound f₄ (feistel3 f₁ f₂ f₃ p) := rfl

theorem feistel4_symm_apply (f₁ f₂ f₃ f₄ : G → G) (wz : G × G) :
    (feistel4 f₁ f₂ f₃ f₄).symm wz = (feistel3 f₁ f₂ f₃).symm (feistelInvRound f₄ wz) := rfl

end Algebraic

/-! ### Shared two-round coupling and collision infrastructure -/

section SharedCoupling

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]

private def splitBoolTable {X Y : Type*} : (Bool × X → Y) ≃ (X → Y) × (X → Y) where
  toFun table := (fun u => table (false, u), fun v => table (true, v))
  invFun fg := fun q => cond q.1 (fg.2 q.2) (fg.1 q.2)
  left_inv table := by funext ⟨b, x⟩; cases b <;> rfl
  right_inv _ := rfl

omit [AddGroup G] [Fintype G] [DecidableEq G] in
private theorem lookup_cons_tag_ne {X V : Type*} [BEq X] (b : Bool) (x z : X) (y : V)
    (cache : List ((Bool × X) × V)) :
    (((b, x), y) :: cache).lookup (!b, z) = cache.lookup (!b, z) := by
  have h : ((!b, z) == (b, x)) = false := by cases b <;> simp [BEq.beq]
  simp only [List.lookup_cons, h]

omit [AddGroup G] [Fintype G] [DecidableEq G] in
private theorem isSome_lookup_cons {α β : Type*} [DecidableEq α] (k k' : α) (v : β)
    (l : List (α × β)) :
    (((k, v) :: l).lookup k').isSome = (decide (k' = k) || (l.lookup k').isSome) := by
  by_cases h : k' = k
  · subst h; simp
  · simp [List.lookup_cons, beq_eq_false_iff_ne.mpr h, h]

omit [AddGroup G] [Fintype G] [DecidableEq G] in
private theorem tsum_mul_le_add {α : Type*} (μ : PMF α) {f g err : α → ℝ≥0∞}
    (h : ∀ a, f a ≤ g a + err a) :
    ∑' a, μ a * f a ≤ (∑' a, μ a * g a) + ∑' a, μ a * err a :=
  (tsum_le_tsum fun a => mul_le_mul_of_nonneg_left (h a) zero_le).trans_eq
    (by simp only [mul_add, tsum_add])

omit [AddGroup G] [Fintype G] [DecidableEq G] in
private theorem tsum_mul_const {α : Type*} (μ : PMF α) (c : ℝ≥0∞) :
    ∑' a, μ a * c = c := by
  rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

omit [AddGroup G] [Fintype G] [DecidableEq G] in
private theorem tsum_toOuterMeasure_of_pointwise_le {α β : Type} (μ : PMF α) (d : PMF β)
    (P : α → β → Prop) (M : ℝ≥0∞)
    (hM : ∀ y ∈ d.support, μ.toOuterMeasure {a | P a y} ≤ M) :
    (∑' a, μ a * d.toOuterMeasure {y | P a y}) ≤ M := by
  classical
  have hcomm :
      (∑' a, μ a * ∑' y, {y | P a y}.indicator d y) =
        ∑' y, d y * ∑' a, {a | P a y}.indicator μ a := by
    simp only [← ENNReal.tsum_mul_left]
    rw [tsum_comm]
    refine tsum_congr fun y => tsum_congr fun a => ?_
    by_cases h : P a y
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_comm]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero, mul_zero]
  simp only [PMF.toOuterMeasure_apply]
  rw [hcomm]
  exact Probability.PMF.tsum_mul_le_of_support d fun y hy => by
    rw [← PMF.toOuterMeasure_apply]
    exact hM y hy

omit [AddGroup G] [Fintype G] [DecidableEq G] in
private theorem toOuterMeasure_or_le {α : Type*} (μ : PMF α) (p q : α → Bool) :
    μ.toOuterMeasure {x | (p x || q x) = true} ≤
      μ.toOuterMeasure {x | p x = true} + μ.toOuterMeasure {x | q x = true} :=
  calc μ.toOuterMeasure {x | (p x || q x) = true}
      ≤ μ.toOuterMeasure ({x | p x = true} ∪ {x | q x = true}) :=
        μ.toOuterMeasure.mono fun _ hx => (Bool.or_eq_true _ _).mp hx
    _ ≤ _ := MeasureTheory.measure_union_le _ _

/-- Whether a list contains two entries with the same `key` value. -/
private def hasColl {α β : Type*} [DecidableEq β] (key : α → β) : List α → Bool
  | [] => false
  | a :: rest => hasColl key rest || rest.any (fun e => decide (key a = key e))

omit [AddGroup G] [Fintype G] [DecidableEq G] in
private theorem toOuterMeasure_any_le {α β : Type*} (μ : PMF α) (l : List β)
    (P : α → β → Prop) [∀ a b, Decidable (P a b)] {ε : ℝ≥0∞}
    (h : ∀ b ∈ l, μ.toOuterMeasure {a | P a b} ≤ ε) :
    μ.toOuterMeasure {a | l.any (fun b => decide (P a b)) = true} ≤ l.length * ε := by
  induction l with
  | nil => simp
  | cons b rest ih =>
    calc μ.toOuterMeasure {a | (b :: rest).any (fun e => decide (P a e)) = true}
        ≤ μ.toOuterMeasure {a | P a b} +
            μ.toOuterMeasure {a | rest.any (fun e => decide (P a e)) = true} := by
          simpa only [List.any_cons, decide_eq_true_eq] using
            toOuterMeasure_or_le μ (fun a => decide (P a b))
              (fun a => rest.any fun e => decide (P a e))
      _ ≤ ε + rest.length * ε :=
          add_le_add (h b List.mem_cons_self)
            (ih fun e he => h e (List.mem_cons_of_mem b he))
      _ = ((b :: rest).length : ℝ≥0∞) * ε := by
          rw [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

omit [Fintype G] in
/-- Over a list with pairwise distinct `proj` coordinates, a collision in `(proj e).1 + h k
(proj e).2` under an `ε`-almost-Δ-universal family `(seed, h)` occurs with probability at most
`qc.length.choose 2 * ε`. -/
private theorem toOuterMeasure_hasColl_delta_le {K₁ β : Type*} {seed : PMF K₁}
    {h : K₁ → G → G} {ε : ℝ≥0∞} (hh : IsDeltaUniversalHash seed h ε)
    (proj : β → G × G) {qc : List β} (hnodup : qc.Pairwise (fun a b => proj a ≠ proj b)) :
    seed.toOuterMeasure {k | hasColl (fun e => (proj e).1 + h k (proj e).2) qc = true} ≤
      qc.length.choose 2 * ε := by
  induction qc with
  | nil => simp [hasColl]
  | cons a rest ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hnodup
    have hstep :
        seed.toOuterMeasure
          {k | rest.any (fun e =>
            decide ((proj a).1 + h k (proj a).2 = (proj e).1 + h k (proj e).2)) = true} ≤
          rest.length * ε := by
      refine toOuterMeasure_any_le seed rest _ fun e he => ?_
      have hne := hhead e he
      by_cases hr : (proj a).2 = (proj e).2
      · have hemp : {k | (proj a).1 + h k (proj a).2 = (proj e).1 + h k (proj e).2} = ∅ :=
          Set.eq_empty_iff_forall_notMem.mpr fun k hk =>
            hne (Prod.ext (add_right_cancel (hr ▸ hk)) hr)
        simp [hemp]
      · have hiff :
            {k | (proj a).1 + h k (proj a).2 = (proj e).1 + h k (proj e).2} =
              {k | h k (proj a).2 - h k (proj e).2 = -(proj a).1 + (proj e).1} := by
          ext k
          simp only [Set.mem_ofPred_eq]
          rw [eq_comm, ← neg_add_eq_iff_eq_add, sub_eq_iff_eq_add, add_assoc, eq_comm]
        rw [hiff]
        exact hh (proj a).2 (proj e).2 hr (-(proj a).1 + (proj e).1)
    calc seed.toOuterMeasure {k | hasColl (fun e => (proj e).1 + h k (proj e).2) (a :: rest) = true}
        ≤ seed.toOuterMeasure {k | hasColl (fun e => (proj e).1 + h k (proj e).2) rest = true} +
            seed.toOuterMeasure {k | rest.any (fun e =>
              decide ((proj a).1 + h k (proj a).2 = (proj e).1 + h k (proj e).2)) = true} :=
          toOuterMeasure_or_le seed _ _
      _ ≤ rest.length.choose 2 * ε + rest.length * ε := add_le_add (ih htail) hstep
      _ = ((a :: rest).length.choose 2 : ℝ≥0∞) * ε := by
          rw [List.length_cons, Nat.choose_succ_succ' rest.length 1, Nat.choose_one_right,
            Nat.cast_add]
          ring

/-- Parameters for a single two-round (`f₂, f₃`) Feistel inner query (`3`-round forward, `4`-round
forward, or `4`-round inverse). -/
private structure TwoStepParams (G : Type) where
  tag : Bool
  key₁ : G
  inner₁ : G ≃ G
  inner₂ : G ≃ G
  outer : G × G ≃ G × G

private def TwoStepParams.query (p : TwoStepParams G) :
    OracleComp (fun _ : Bool × G => G) (G × G) := do
  let y₁ ← OracleComp.query (spec := fun _ : Bool × G => G) (p.tag, p.key₁)
  let y₂ ← OracleComp.query (spec := fun _ : Bool × G => G) (!p.tag, p.inner₁ y₁)
  return p.outer (p.inner₁ y₁, p.inner₂ y₂)

private noncomputable def TwoStepParams.realStep (p : TwoStepParams G)
    (cache : List ((Bool × G) × G)) : PMF ((G × G) × (List ((Bool × G) × G) × Bool)) := do
  let (y₁, c₁) ← memoize (fun _ : Bool × G => PMF.uniformOfFintype G) (p.tag, p.key₁) cache
  let k₂ := p.inner₁ y₁
  let (y₂, c₂) ← memoize (fun _ : Bool × G => PMF.uniformOfFintype G) (!p.tag, k₂) c₁
  let bad := (cache.lookup (p.tag, p.key₁)).isSome || (cache.lookup (!p.tag, k₂)).isSome
  return (p.outer (k₂, p.inner₂ y₂), (c₂, bad))

private noncomputable def TwoStepParams.idealStep (p : TwoStepParams G)
    (cache : List ((Bool × G) × G)) : PMF ((G × G) × (List ((Bool × G) × G) × Bool)) := do
  let ans ← PMF.uniformOfFintype (G × G)
  let x := p.outer.symm ans
  let c₂ := ((!p.tag, x.1), p.inner₂.symm x.2) :: ((p.tag, p.key₁), p.inner₁.symm x.1) :: cache
  let bad := (cache.lookup (p.tag, p.key₁)).isSome || (cache.lookup (!p.tag, x.1)).isSome
  return (ans, (c₂, bad))

private theorem TwoStepParams.realStep_map_fst (p : TwoStepParams G)
    (cache : List ((Bool × G) × G)) :
    (p.realStep cache).map (Prod.map id Prod.fst) =
      (OracleComp.interpret (memoize fun _ : Bool × G => PMF.uniformOfFintype G)
        p.query).run cache := by
  simp only [interp_norm, pmf_norm, TwoStepParams.realStep, TwoStepParams.query]
  rfl

private theorem TwoStepParams.realStep_agree_idealStep (p : TwoStepParams G)
    (cache cache' : List ((Bool × G) × G)) (ans : G × G) :
    p.realStep cache (ans, (cache', false)) = p.idealStep cache (ans, (cache', false)) := by
  have apply_false_eq_zero : ∀ {α : Type} (μ : PMF α) (f : α → G × G)
      (g : α → List ((Bool × G) × G)),
      (μ.bind fun a => PMF.pure (f a, (g a, true))) (ans, (cache', false)) = 0 := fun μ f g =>
    (PMF.apply_eq_zero_iff _ _).mpr fun hm => by supp_cases hm
  cases h₁ : cache.lookup (p.tag, p.key₁) with
  | some _ =>
    rw [(PMF.apply_eq_zero_iff _ _).mpr fun hm => by supp_cases hm [TwoStepParams.realStep, h₁],
      (PMF.apply_eq_zero_iff _ _).mpr fun hm => by supp_cases hm [TwoStepParams.idealStep, h₁]]
  | none =>
    have hreal : p.realStep cache =
        (PMF.uniformOfFintype G).bind fun k₂ =>
          (memoize (fun _ : Bool × G => PMF.uniformOfFintype G) (!p.tag, k₂)
            (((p.tag, p.key₁), p.inner₁.symm k₂) :: cache)).bind fun x =>
              PMF.pure (p.outer (k₂, p.inner₂ x.1), (x.2, (cache.lookup (!p.tag, k₂)).isSome)) := by
      simp only [pmf_norm, TwoStepParams.realStep, memoize_of_none _ _ _ h₁, h₁,
        Option.isSome_none, Bool.false_or]
      rw [← Probability.PMF.uniformOfFintype_bind_equiv p.inner₁.symm]
      simp only [Equiv.apply_symm_apply]
    have hideal : p.idealStep cache =
        (PMF.uniformOfFintype G).bind fun k₂ =>
          (PMF.uniformOfFintype G).bind fun y₂ =>
            PMF.pure (p.outer (k₂, p.inner₂ y₂),
              (((!p.tag, k₂), y₂) :: ((p.tag, p.key₁), p.inner₁.symm k₂) :: cache,
                (cache.lookup (!p.tag, k₂)).isSome)) := by
      simp only [pmf_norm, TwoStepParams.idealStep, h₁, Option.isSome_none, Bool.false_or]
      rw [← Probability.PMF.uniformOfFintype_bind_equiv p.outer,
        ← Probability.PMF.uniformOfFintype_prod]
      simp only [pmf_norm, Equiv.symm_apply_apply]
      congr 1 with k₂ : 1
      rw [← Probability.PMF.uniformOfFintype_bind_equiv p.inner₂]
      simp only [Equiv.symm_apply_apply]
    rw [hreal, hideal, PMF.bind_apply, PMF.bind_apply]
    refine tsum_congr fun k₂ => congrArg (_ * ·) ?_
    cases h₂ : cache.lookup (!p.tag, k₂) with
    | some _ =>
      simp only [Option.isSome_some, apply_false_eq_zero]
    | none =>
      have h₂' : (((p.tag, p.key₁), p.inner₁.symm k₂) :: cache).lookup (!p.tag, k₂) = none := by
        rw [lookup_cons_tag_ne, h₂]
      simp only [Option.isSome_none, memoize_of_none _ _ _ h₂', pmf_norm]

/-- Invariant linking a deduplication query cache `qc` with the internal lazy round-function cache
and bad flag `(cache, bad)` tracking collisions on `false`-key `keyF` and `true`-key `keyT`. -/
private structure RoundCacheInv (keyF keyT : (G × G) × (G × G) → G)
    (qc : List ((G × G) × (G × G))) (st : List ((Bool × G) × G) × Bool) : Prop where
  lookup_eq (b : Bool) (x : G) :
    (st.1.lookup (b, x)).isSome = qc.any (fun e => decide (x = cond b (keyT e) (keyF e)))
  bad_eq : st.2 = (hasColl keyF qc || hasColl keyT qc)

omit [AddGroup G] [Fintype G] in
private theorem roundCacheInv_nil (keyF keyT : (G × G) × (G × G) → G) :
    RoundCacheInv keyF keyT [] ([], false) where
  lookup_eq _ _ := rfl
  bad_eq := rfl

omit [AddGroup G] [Fintype G] in
private theorem RoundCacheInv.step {keyF keyT : (G × G) × (G × G) → G}
    {qc : List ((G × G) × (G × G))} {st : List ((Bool × G) × G) × Bool}
    (h : RoundCacheInv keyF keyT qc st) (b : Bool) (e : (G × G) × (G × G)) (y₁ y₂ : G) :
    let k₁ := cond b (keyT e) (keyF e)
    let k₂ := cond (!b) (keyT e) (keyF e)
    RoundCacheInv keyF keyT (e :: qc)
      (((!b, k₂), y₂) :: ((b, k₁), y₁) :: st.1,
        st.2 || ((st.1.lookup (b, k₁)).isSome || (st.1.lookup (!b, k₂)).isSome)) where
  lookup_eq c x := by
    rw [isSome_lookup_cons, isSome_lookup_cons, h.lookup_eq c x]
    cases b <;> cases c <;> simp [List.any_cons]
  bad_eq := by
    have hF := h.lookup_eq false (keyF e)
    have hT := h.lookup_eq true (keyT e)
    cases b <;>
      simp only [Bool.cond_false, Bool.cond_true, Bool.not_false, Bool.not_true,
        h.bad_eq, hF, hT, hasColl] <;>
      ac_rfl

/-- Rewrite a two-inner-round uniform Feistel game (`f₂, f₃ ← unif (G → G)`) as a flagged lazy
execution via `OracleComp.withBadFlag` over a deduplicated program. -/
private theorem bind_innerRounds_eq_realHandler {ι α : Type} {spec : ι → Type}
    (dedupProg : OracleComp spec (Bool × α))
    (query : (q : ι) → OracleComp (fun _ : Bool × G => G) (spec q))
    (step : (q : ι) → List ((Bool × G) × G) → PMF (spec q × (List ((Bool × G) × G) × Bool)))
    (hstep : ∀ q c, (step q c).map (Prod.map id Prod.fst) =
      (OracleComp.interpret (memoize fun _ : Bool × G => PMF.uniformOfFintype G) (query q)).run c)
    (target : (G → G) → (G → G) → Game)
    (heval : ∀ table : Bool × G → G,
      (OracleComp.interpret
        (fun q => OracleComp.interpret (fun x => PMF.pure (table x)) (query q)) dedupProg).map
          Prod.fst =
        target (fun u => table (false, u)) (fun v => table (true, v))) :
    ((PMF.uniformOfFintype (G → G)).bind fun f₂ =>
      (PMF.uniformOfFintype (G → G)).bind fun f₃ => target f₂ f₃) =
      (((OracleComp.interpret (OracleComp.withBadFlag step) dedupProg).run ([], false)).map
        fun x => x.1.1) := by
  have hdrop := congrArg (PMF.map fun x => x.1.1)
    (OracleComp.run_interpret_withBadFlag_map_fst step
      (fun q => OracleComp.interpret (memoize fun _ : Bool × G => PMF.uniformOfFintype G)
        (query q)) hstep dedupProg [] false)
  have hlazy := RandomOracle.interpret_eq_memoize (fun _ : Bool × G => PMF.uniformOfFintype G)
    (OracleComp.interpret query dedupProg)
  rw [Probability.PMF.pi_uniformOfFintype, OracleComp.interpret_interpret] at hlazy
  have hunif :
      (PMF.uniformOfFintype (Bool × G → G)).map splitBoolTable =
        (PMF.uniformOfFintype (G → G)).bind fun f₂ =>
          (PMF.uniformOfFintype (G → G)).map fun f₃ => (f₂, f₃) := by
    relabel_uniform splitBoolTable
  have hbind := congrArg (fun d : PMF ((G → G) × (G → G)) => d.bind fun fg => target fg.1 fg.2)
    hunif
  simp only [pmf_norm, splitBoolTable, Equiv.coe_fn_mk] at hbind
  rw [PMF.map_comp] at hdrop
  change ((OracleComp.interpret (OracleComp.withBadFlag step) dedupProg).run ([], false)).map
      (fun x => x.1.1) = _ at hdrop
  have hlazy' := congrArg (PMF.map Prod.fst) hlazy.symm
  simp only [pmf_norm] at hlazy'
  rw [← hbind, hdrop, hlazy']
  simp only [OracleComp.interpret_interpret, heval]

omit [AddGroup G] [Fintype G] [DecidableEq G] in
/-- Couple a stateful oracle handler `idealH` on a deduplicating transformer `dedupStep` with a
direct reference handler `refH` tracking the same cache `C` and collision indicator `coll`. -/
private theorem map_bad_run_ideal_dedup {ι α C St : Type} {spec : ι → Type}
    (Inv : C → St → Prop) (flag : St → Bool) (coll : C → Bool)
    (hflag : ∀ {c s}, Inv c s → flag s = coll c)
    (dedupStep : (q : ι) → StateT C (OracleComp spec) (spec q))
    (idealH : (q : ι) → StateT St PMF (spec q))
    (refH : (q : ι) → StateT C PMF (spec q))
    (program : OracleComp spec α) {c : C} {s : St} (hcs : Inv c s)
    (hstep : ∀ q c s (k₁ : spec q → C → St → PMF ((α × C) × Bool))
      (k₂ : spec q → C → PMF ((α × C) × Bool)),
      Inv c s → (∀ a c' s', Inv c' s' → k₁ a c' s' = k₂ a c') →
      ((OracleComp.interpret idealH (dedupStep q c)).run s).bind
        (fun x => k₁ x.1.1 x.1.2 x.2) =
      (refH q c).bind fun y => k₂ y.1 y.2) :
    (((OracleComp.interpret idealH ((OracleComp.interpret dedupStep program).run c)).run s).map
      fun x => (x.1, flag x.2)) =
      ((OracleComp.interpret refH program).run c).map fun x => (x, coll x.2) := by
  induction program using OracleComp.induction generalizing c s with
  | pure a => simp [PMF.pure_map, hflag hcs]
  | query_bind q cont ih =>
    simp only [PFunctor.FreeM.bind_eq_bind, interp_norm, PMF.map_bind,
      Probability.PMF.monad_bind_eq_bind]
    exact hstep q c s
      (fun a c' s' =>
        ((OracleComp.interpret idealH ((OracleComp.interpret dedupStep (cont a)).run c')).run
          s').map fun x => (x.1, flag x.2))
      (fun a c' =>
        ((OracleComp.interpret refH (cont a)).run c').map fun x => (x, coll x.2))
      hcs fun a _ _ hc' => ih a hc'

omit [AddGroup G] [Fintype G] [DecidableEq G] in
/-- Two-sided difference-lemma bounds combining an `IdenticalUntilBad` coupling on `St × Bool` with
a simulation equality into `refRun`. -/
private theorem apply_le_both_of_sim {ι C St : Type} {spec : ι → Type}
    {realH idealH : (q : ι) → StateT (St × Bool) PMF (spec q)}
    (hib : OracleComp.IdenticalUntilBad realH idealH OracleComp.FlagBad)
    {s₀ : St} (dedupProg : OracleComp spec (Bool × C)) (refRun : PMF (Bool × C))
    (coll : C → Bool)
    (hsim : ((OracleComp.interpret idealH dedupProg).run (s₀, false)).map
        (fun x => (x.1, x.2.2)) =
      refRun.map fun x => (x, coll x.2))
    {g : Game} (hg : g = ((OracleComp.interpret realH dedupProg).run (s₀, false)).map (·.1.1))
    (b : Bool) :
    g b ≤ (refRun.map Prod.fst) b + refRun.toOuterMeasure {x | coll x.2 = true} ∧
      (refRun.map Prod.fst) b ≤ g b + refRun.toOuterMeasure {x | coll x.2 = true} := by
  have hfst : ((OracleComp.interpret idealH dedupProg).run (s₀, false)).map (·.1.1) =
      refRun.map Prod.fst := by
    simpa only [PMF.map_comp, Function.comp_def] using congrArg (PMF.map fun x => x.1.1) hsim
  have hbad : ((OracleComp.interpret idealH dedupProg).run (s₀, false)).toOuterMeasure
      {x | OracleComp.FlagBad x.2} = refRun.toOuterMeasure {x | coll x.2 = true} := by
    have h := congrArg (fun d => d.toOuterMeasure {x | x.2 = true}) hsim
    rwa [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply] at h
  rw [hg, ← hfst, ← hbad]
  refine ⟨?_, ?_⟩
  · have h := hib.bind_apply_le dedupProg (s₀, false) (fun x => PMF.pure x.1.1) b
    rwa [hib.bad_eq] at h
  · exact hib.symm.bind_apply_le dedupProg (s₀, false) (fun x => PMF.pure x.1.1) b

/-- Combine inner-round lazy rewriting, `IdenticalUntilBad` coupling, and cache-invariant simulation
for a family of `TwoStepParams` (handling both 3-round and 4-round Feistel games). -/
private theorem apply_le_both_of_twoStep {ι : Type}
    (params : ι → TwoStepParams G)
    (keyF keyT : (G × G) × (G × G) → G)
    (dedupStep : (q : ι) → StateT (List ((G × G) × (G × G)))
      (OracleComp (fun _ : ι => G × G)) (G × G))
    (refH : (q : ι) → StateT (List ((G × G) × (G × G))) PMF (G × G))
    (program : OracleComp (fun _ : ι => G × G) Bool)
    (target : (G → G) → (G → G) → Game)
    (heval : ∀ table : Bool × G → G,
      (OracleComp.interpret
        (fun q => OracleComp.interpret (fun x => PMF.pure (table x)) (params q).query)
        ((OracleComp.interpret dedupStep program).run [])).map Prod.fst =
        target (fun u => table (false, u)) (fun v => table (true, v)))
    (hstep : ∀ q qc (k₁ : G × G → List ((G × G) × (G × G)) → List ((Bool × G) × G) × Bool →
        PMF ((Bool × List ((G × G) × (G × G))) × Bool))
      (k₂ : G × G → List ((G × G) × (G × G)) → PMF ((Bool × List ((G × G) × (G × G))) × Bool))
      (st : List ((Bool × G) × G) × Bool), RoundCacheInv keyF keyT qc st →
      (∀ a qc' st', RoundCacheInv keyF keyT qc' st' → k₁ a qc' st' = k₂ a qc') →
      ((OracleComp.interpret (OracleComp.withBadFlag (fun q => (params q).idealStep))
        (dedupStep q qc)).run st).bind (fun x => k₁ x.1.1 x.1.2 x.2) =
      (refH q qc).bind fun y => k₂ y.1 y.2)
    (b : Bool) :
    let g : Game := (PMF.uniformOfFintype (G → G)).bind fun f₂ =>
      (PMF.uniformOfFintype (G → G)).bind fun f₃ => target f₂ f₃
    let ref := (OracleComp.interpret refH program).run []
    g b ≤ (ref.map Prod.fst) b +
        ref.toOuterMeasure {x | (hasColl keyF x.2 || hasColl keyT x.2) = true} ∧
      (ref.map Prod.fst) b ≤ g b +
        ref.toOuterMeasure {x | (hasColl keyF x.2 || hasColl keyT x.2) = true} := by
  have hg := bind_innerRounds_eq_realHandler ((OracleComp.interpret dedupStep program).run [])
    (fun q => (params q).query) (fun q => (params q).realStep)
    (fun q c => (params q).realStep_map_fst c) target heval
  have hib := OracleComp.identicalUntilBad_withBadFlag
    (fun q => (params q).realStep) (fun q => (params q).idealStep)
    fun q cache ans cache' => (params q).realStep_agree_idealStep cache cache' ans
  have hsim := map_bad_run_ideal_dedup (RoundCacheInv keyF keyT) Prod.snd
    (fun qc => hasColl keyF qc || hasColl keyT qc) (fun h => h.bad_eq)
    dedupStep (OracleComp.withBadFlag (fun q => (params q).idealStep)) refH
    program (roundCacheInv_nil keyF keyT) fun q qc st k₁ k₂ hst hk => hstep q qc k₁ k₂ st hst hk
  exact apply_le_both_of_sim hib ((OracleComp.interpret dedupStep program).run [])
    ((OracleComp.interpret refH program).run []) (fun qc => hasColl keyF qc || hasColl keyT qc)
    hsim hg b

/-- Couple a miss step (`dedupStep q qc` reads a fresh query and pushes `mkEntry a :: qc`) to
`PMF.uniformOfFintype (G × G)` via `RoundCacheInv.step`. -/
private theorem twoStep_miss_bind {C : Type} {p : TwoStepParams G}
    {keyF keyT : (G × G) × (G × G) → G} {qc : List ((G × G) × (G × G))}
    {st : List ((Bool × G) × G) × Bool} (hst : RoundCacheInv keyF keyT qc st)
    (mkEntry : G × G → (G × G) × (G × G))
    (hk₁ : ∀ a, p.key₁ = cond p.tag (keyT (mkEntry a)) (keyF (mkEntry a)))
    (hk₂ : ∀ a, (p.outer.symm a).1 = cond (!p.tag) (keyT (mkEntry a)) (keyF (mkEntry a)))
    (k₁ : G × G → List ((G × G) × (G × G)) → List ((Bool × G) × G) × Bool → PMF C)
    (k₂ : G × G → List ((G × G) × (G × G)) → PMF C)
    (hk : ∀ a qc' st', RoundCacheInv keyF keyT qc' st' → k₁ a qc' st' = k₂ a qc') :
    ((OracleComp.withBadFlag (fun _ : Unit => p.idealStep) () st).bind
      fun x => k₁ x.1 (mkEntry x.1 :: qc) x.2) =
    (PMF.uniformOfFintype (G × G)).bind fun a => k₂ a (mkEntry a :: qc) := by
  rcases st with ⟨cache, bad⟩
  simp only [OracleComp.withBadFlag, TwoStepParams.idealStep, pmf_norm, Prod.map_apply, id_eq]
  refine congrArg (PMF.bind _) (funext fun a => ?_)
  have hnext := hst.step p.tag (mkEntry a) (p.inner₁.symm (p.outer.symm a).1)
    (p.inner₂.symm (p.outer.symm a).2)
  rw [← hk₁ a, ← hk₂ a] at hnext
  exact hk a (mkEntry a :: qc) _ hnext

end SharedCoupling

/-! ### The 3-round Luby–Rackoff theorem -/

section LubyRackoff3

variable {K K₁ G : Type} [AddGroup G] [Fintype G] [DecidableEq G]

/-- The 3-round Feistel game with a fixed first round function `f₁` and independent uniform random
second and third round functions `f₂, f₃ : G → G`. -/
noncomputable def feistel3FixedGame (f₁ : G → G)
    (program : OracleComp (fun _ : G × G => G × G) Bool) : Game := do
  let f₂ ← PMF.uniformOfFintype (G → G)
  let f₃ ← PMF.uniformOfFintype (G → G)
  OracleComp.interpret (fun p => PMF.pure (feistel3 f₁ f₂ f₃ p)) program

/-- The 3-round Feistel game where the first round function is drawn from a keyed hash family
`(seed₁, h₁)` and the second and third round functions are independent uniform random functions. -/
noncomputable def feistel3HashIdealGame (seed₁ : PMF K₁) (h₁ : K₁ → G → G)
    (program : OracleComp (fun _ : G × G => G × G) Bool) : Game := do
  let k₁ ← seed₁
  feistel3FixedGame (h₁ k₁) program

/-- The 3-round Feistel game with three independent uniform random round functions
`f₁, f₂, f₃ : G → G`. -/
noncomputable def feistel3RandomRoundsGame
    (program : OracleComp (fun _ : G × G => G × G) Bool) : Game := do
  let f₁ ← PMF.uniformOfFintype (G → G)
  feistel3FixedGame f₁ program

/-- The ideal random-function game on `G × G`: sample a uniform table `(G × G) → (G × G)` and
answer every query from it. -/
noncomputable def randomFunctionGame [Nonempty G]
    (program : OracleComp (fun _ : G × G => G × G) Bool) : Game := do
  let table ← PMF.uniformOfFintype (G × G → G × G)
  OracleComp.interpret (fun p => PMF.pure (table p)) program

/-- The ideal random-permutation game on `G × G`: sample a uniform permutation
`π ← PMF.uniformOfFintype (Equiv.Perm (G × G))` and answer every query via `π p`. -/
noncomputable def idealPermGame
    (program : OracleComp (fun _ : G × G => G × G) Bool) : Game := do
  let π ← PMF.uniformOfFintype (Equiv.Perm (G × G))
  OracleComp.interpret (fun p => PMF.pure (π p)) program

/-- Deduplicate queries of an adaptive program by caching the first answer to each query in an
association list. -/
private def dedup {α : Type} (program : OracleComp (fun _ : G × G => G × G) α) :
    OracleComp (fun _ : G × G => G × G) (α × List ((G × G) × (G × G))) :=
  (OracleComp.interpret (memoize OracleComp.query) program).run []

set_option linter.unusedFintypeInType false in
omit [AddGroup G] in
private theorem map_fst_interpret_dedup_pure {α : Type} (F : G × G → G × G)
    (program : OracleComp (fun _ : G × G => G × G) α) :
    (OracleComp.interpret (fun p => PMF.pure (F p)) (dedup program)).map Prod.fst =
      OracleComp.interpret (fun p => PMF.pure (F p)) program := by
  have hhom : IsMonadHom (OracleComp (fun _ : G × G => G × G)) PMF
      (OracleComp.interpret fun p => PMF.pure (F p)) :=
    PFunctor.FreeM.isMonadHom_liftM (P := ⟨G × G, fun _ => G × G⟩) _
  have hdedup :
      OracleComp.interpret (fun p => PMF.pure (F p)) (dedup program) =
        (OracleComp.interpret (memoize fun p => PMF.pure (F p)) program).run [] := by
    rw [dedup, OracleComp.map_run_interpret hhom]
    simp only [hhom.map_memoize, OracleComp.interpret_query]
  rw [hdedup, ← RandomOracle.interpret_eq_memoize (fun p => PMF.pure (F p)) program]
  have hpi : Probability.PMF.pi (fun p => PMF.pure (F p)) = PMF.pure F := by
    ext table
    simp only [Probability.PMF.pi_apply, PMF.pure_apply]
    by_cases h : table = F
    · subst h; simp
    · obtain ⟨p, hp⟩ := Function.ne_iff.mp h
      rw [ite_eq_right h]
      exact Finset.prod_eq_zero (Finset.mem_univ p) (ite_eq_right hp)
  simp [hpi]

private def hasUCollision (f₁ : G → G) (qc : List ((G × G) × (G × G))) : Bool :=
  hasColl (fun e => e.1.1 + f₁ e.1.2) qc

private def hasVCollision (qc : List ((G × G) × (G × G))) : Bool :=
  hasColl (fun e => e.2.1) qc

private theorem feistel3FixedGame_and_randomFunctionGame_le (f₁ : G → G)
    (program : OracleComp (fun _ : G × G => G × G) Bool) (b : Bool) :
    let ref := (OracleComp.interpret
      (memoize fun _ : G × G => PMF.uniformOfFintype (G × G)) program).run []
    feistel3FixedGame f₁ program b ≤
        randomFunctionGame program b +
          ref.toOuterMeasure {x | (hasUCollision f₁ x.2 || hasVCollision x.2) = true} ∧
      randomFunctionGame program b ≤
        feistel3FixedGame f₁ program b +
          ref.toOuterMeasure {x | (hasUCollision f₁ x.2 || hasVCollision x.2) = true} := by
  let params (p : G × G) : TwoStepParams G :=
    ⟨false, p.1 + f₁ p.2, Equiv.addLeft p.2, Equiv.addLeft (p.1 + f₁ p.2), Equiv.refl (G × G)⟩
  have hrand : randomFunctionGame program =
      ((OracleComp.interpret (memoize fun _ : G × G => PMF.uniformOfFintype (G × G))
        program).run []).map Prod.fst := by
    have hm := RandomOracle.interpret_eq_memoize
      (fun _ : G × G => PMF.uniformOfFintype (G × G)) program
    rwa [Probability.PMF.pi_uniformOfFintype] at hm
  rw [hrand]
  refine apply_le_both_of_twoStep params (fun e => e.1.1 + f₁ e.1.2) (fun e => e.2.1)
    (memoize OracleComp.query) (memoize fun _ : G × G => PMF.uniformOfFintype (G × G)) program
    (fun f₂ f₃ => OracleComp.interpret (fun p => PMF.pure (feistel3 f₁ f₂ f₃ p)) program)
    (fun table => ?_) (fun p qc k₁ k₂ st hst hk => ?_) b
  · have hstep :
        (fun p => OracleComp.interpret (fun x => PMF.pure (table x)) (params p).query) =
        (fun p => PMF.pure (feistel3 f₁ (fun u => table (false, u))
          (fun v => table (true, v)) p)) := by
      funext p; simp [params, TwoStepParams.query, feistel3_apply, add_assoc]
    exact hstep ▸ map_fst_interpret_dedup_pure _ program
  · cases h : qc.lookup p with
    | some r =>
      rw [memoize_of_some _ _ _ _ h, memoize_of_some _ _ _ _ h]
      simp only [interp_norm, pmf_norm]
      exact hk r qc st hst
    | none =>
      rw [memoize_of_none _ _ _ h, memoize_of_none _ _ _ h]
      simp only [interp_norm, pmf_norm]
      exact twoStep_miss_bind hst (fun vw => (p, vw)) (fun _ => rfl) (fun _ => rfl) k₁ k₂ hk

omit [AddGroup G] [Fintype G] in
/-- Every cache produced by `memoize` from `qc` on an `n`-query-bounded program has pairwise
distinct keys and length at most `qc.length + n`. -/
private theorem memoize_pairwise_and_length_le {α : Type}
    (distribution : G × G → PMF (G × G))
    {program : OracleComp (fun _ : G × G => G × G) α} {n : ℕ}
    (hn : OracleComp.IsQueryBounded program n)
    {qc : List ((G × G) × (G × G))} (hpair : qc.Pairwise (fun a b => a.1 ≠ b.1))
    {result : α} {qc' : List ((G × G) × (G × G))}
    (hmem : (result, qc') ∈
      ((OracleComp.interpret (memoize distribution) program).run qc).support) :
    qc'.Pairwise (fun a b => a.1 ≠ b.1) ∧ qc'.length ≤ qc.length + n := by
  induction hn generalizing qc with
  | pure a n =>
    simp only [interp_norm, pmf_norm, PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
    exact hmem.2.symm ▸ ⟨hpair, Nat.le_add_right _ _⟩
  | liftBind p cont n _ ih =>
    simp only [interp_norm, pmf_norm, PMF.mem_support_bind_iff] at hmem
    obtain ⟨⟨r, qc₁⟩, hstep, hcont⟩ := hmem
    have hmem' := (RandomOracle.mem_support_memoize_iff _ _ _ (r, qc₁)).mp hstep
    dsimp only at hmem' hcont
    rcases hmem' with ⟨_, rfl⟩ | ⟨hlookup, _, rfl⟩
    · obtain ⟨hp', hlen'⟩ := ih r hpair hcont
      exact ⟨hp', hlen'.trans (by omega)⟩
    · have hpair₁ : ((p, r) :: qc).Pairwise (fun a b => a.1 ≠ b.1) :=
        List.pairwise_cons.mpr
          ⟨fun e he => (RandomPermutation.lookup_eq_none_iff.mp hlookup e he).symm, hpair⟩
      obtain ⟨hp', hlen'⟩ := ih r hpair₁ hcont
      rw [List.length_cons] at hlen'
      exact ⟨hp', by omega⟩

omit [AddGroup G] in
/-- Over `n` queries from a cache `qc` with `hasVCollision qc = false`, the probability that
`memoize (fun _ => PMF.uniformOfFintype (G × G))` produces a `V`-collision is at most
`(n * qc.length + n.choose 2) * |G|⁻¹`. -/
private theorem toOuterMeasure_hasVCollision_le [Nonempty G] {α : Type}
    {program : OracleComp (fun _ : G × G => G × G) α} {n : ℕ}
    (hn : OracleComp.IsQueryBounded program n)
    {qc : List ((G × G) × (G × G))} (hqc : hasVCollision qc = false) :
    ((OracleComp.interpret (memoize (fun _ : G × G => PMF.uniformOfFintype (G × G)))
      program).run qc).toOuterMeasure {x | hasVCollision x.2 = true} ≤
      (n * qc.length + n.choose 2 : ℕ) * (Fintype.card G : ℝ≥0∞)⁻¹ := by
  refine OracleComp.toOuterMeasure_bad_choose_two_le
    (bad := fun s : List ((G × G) × (G × G)) => hasVCollision s = true)
    List.length (Fintype.card G : ℝ≥0∞)⁻¹
    (fun p s hs => ?_) (fun p s _ y hy _ => ?_) hn (Bool.eq_false_iff.mp hqc)
  · have hs' : hasVCollision s = false := Bool.eq_false_iff.mpr hs
    cases hlookup : s.lookup p with
    | some r =>
      rw [memoize_of_some _ _ _ _ hlookup]
      simp [PMF.toOuterMeasure_pure_apply, hs']
    | none =>
      have hpt (k : G) :
          (PMF.uniformOfFintype (G × G)).toOuterMeasure {vw : G × G | vw.1 = k} ≤
            (Fintype.card G : ℝ≥0∞)⁻¹ := by
        rw [show {vw : G × G | vw.1 = k} = Prod.fst ⁻¹' {k} from rfl,
          ← PMF.toOuterMeasure_map_apply, Probability.PMF.uniformOfFintype_prod_map_fst,
          PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply]
      rw [show memoize (fun _ : G × G => PMF.uniformOfFintype (G × G)) p s =
          (PMF.uniformOfFintype (G × G)).map (fun vw => (vw, (p, vw) :: s))
          from memoize_of_none _ _ _ hlookup, PMF.toOuterMeasure_map_apply]
      have hset : (fun vw : G × G => (vw, (p, vw) :: s)) ⁻¹' {x | hasVCollision x.2 = true} =
          {vw : G × G | vw.1 ∈ s.map fun e => e.2.1} := by
        ext ⟨v, w⟩
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, hasVCollision, hasColl, List.mem_map]
        rw [show hasColl (fun e => e.2.1) s = false from hs']
        simp only [Bool.false_or, List.any_eq_true, decide_eq_true_eq]
        exact exists_congr fun e => and_congr_right fun _ => eq_comm
      rw [hset]
      simpa only [List.length_map] using
        Probability.PMF.toOuterMeasure_mem_list_le (PMF.uniformOfFintype (G × G)) Prod.fst hpt
          (s.map fun e => e.2.1)
  · rcases (RandomOracle.mem_support_memoize_iff _ _ _ y).mp hy with ⟨_, heq⟩ | ⟨_, _, heq⟩
    · rw [heq]; exact Nat.le_succ _
    · rw [heq, List.length_cons]

/-- Bound on the expected bad-event probability averaged over `k₁ ← seed₁`. -/
private theorem tsum_seed_toOuterMeasure_hasCollision_le {seed₁ : PMF K₁} {h₁ : K₁ → G → G}
    {ε : ℝ≥0∞} (hh₁ : IsDeltaUniversalHash seed₁ h₁ ε)
    {program : OracleComp (fun _ : G × G => G × G) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) :
    (∑' k₁, seed₁ k₁ *
      ((OracleComp.interpret (memoize (fun _ : G × G => PMF.uniformOfFintype (G × G)))
        program).run []).toOuterMeasure
          {x | (hasUCollision (h₁ k₁) x.2 || hasVCollision x.2) = true}) ≤
      Q.choose 2 * ε + Q.choose 2 * (Fintype.card G : ℝ≥0∞)⁻¹ := by
  set idealRun :=
    (OracleComp.interpret (memoize (fun _ : G × G => PMF.uniformOfFintype (G × G)))
      program).run []
  refine (tsum_mul_le_add seed₁ fun k₁ =>
    toOuterMeasure_or_le idealRun (fun x => hasUCollision (h₁ k₁) x.2)
      (fun x => hasVCollision x.2)).trans (add_le_add ?_ ?_)
  · refine tsum_toOuterMeasure_of_pointwise_le seed₁ idealRun
      (fun k₁ x => hasUCollision (h₁ k₁) x.2 = true) _ fun x hx => ?_
    obtain ⟨hpair, hlen⟩ := memoize_pairwise_and_length_le _ hQ List.Pairwise.nil hx
    rw [List.length_nil, zero_add] at hlen
    exact (toOuterMeasure_hasColl_delta_le hh₁ Prod.fst hpair).trans
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.choose_le_choose 2 hlen)) zero_le)
  · rw [tsum_mul_const]
    simpa only [List.length_nil, mul_zero, zero_add] using
      toOuterMeasure_hasVCollision_le hQ (qc := []) rfl

/-- **3-round Luby–Rackoff theorem in `ℝ≥0∞` (with Δ-universal Round 1)**: for any adaptive
program making at most `Q` queries, `feistel3HashIdealGame` accepts with probability at most
`randomFunctionGame` plus `Q.choose 2 * ε + Q.choose 2 * |G|⁻¹`. -/
theorem feistel3HashIdealGame_apply_le {seed₁ : PMF K₁} {h₁ : K₁ → G → G} {ε : ℝ≥0∞}
    (hh₁ : IsDeltaUniversalHash seed₁ h₁ ε)
    {program : OracleComp (fun _ : G × G => G × G) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) (b : Bool) :
    feistel3HashIdealGame seed₁ h₁ program b ≤
      randomFunctionGame program b +
        (Q.choose 2 * ε + Q.choose 2 * (Fintype.card G : ℝ≥0∞)⁻¹) := by
  rw [feistel3HashIdealGame, Probability.PMF.monad_bind_eq_bind, PMF.bind_apply]
  refine (tsum_mul_le_add seed₁ fun k₁ =>
    (feistel3FixedGame_and_randomFunctionGame_le (h₁ k₁) program b).1).trans ?_
  rw [tsum_mul_const]
  exact add_le_add le_rfl (tsum_seed_toOuterMeasure_hasCollision_le hh₁ hQ)

/-- Reverse inequality for the 3-round Luby–Rackoff bound with Δ-universal Round 1:
`randomFunctionGame` accept probability is bounded by `feistel3HashIdealGame` plus the collision
term. -/
theorem randomFunctionGame_apply_le_feistel3HashIdealGame {seed₁ : PMF K₁} {h₁ : K₁ → G → G}
    {ε : ℝ≥0∞} (hh₁ : IsDeltaUniversalHash seed₁ h₁ ε)
    {program : OracleComp (fun _ : G × G => G × G) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) (b : Bool) :
    randomFunctionGame program b ≤
      feistel3HashIdealGame seed₁ h₁ program b +
        (Q.choose 2 * ε + Q.choose 2 * (Fintype.card G : ℝ≥0∞)⁻¹) := by
  rw [← tsum_mul_const seed₁ (randomFunctionGame program b),
    feistel3HashIdealGame, Probability.PMF.monad_bind_eq_bind, PMF.bind_apply]
  exact (tsum_mul_le_add seed₁ fun k₁ =>
    (feistel3FixedGame_and_randomFunctionGame_le (h₁ k₁) program b).2).trans
    (add_le_add le_rfl (tsum_seed_toOuterMeasure_hasCollision_le hh₁ hQ))

/-- **3-round Luby–Rackoff theorem with Δ-universal Round 1** ([BonehShoup2023], Section 4.5.1;
[LubyRackoff1988]): when Round 1 is drawn from an `ε`-almost-Δ-universal hash family and Rounds 2
and 3 are independent uniform random functions on `G`, any `Q`-query adaptive adversary has
distinguishing advantage against a uniform random function on `G × G` at most
`Q.choose 2 * ε.toReal + Q.choose 2 / |G|`. -/
theorem advantage_feistel3HashIdealGame_randomFunctionGame_le
    {seed₁ : PMF K₁} {h₁ : K₁ → G → G} {ε : ℝ≥0∞} (hh₁ : IsDeltaUniversalHash seed₁ h₁ ε)
    (hε : ε ≠ ⊤) {program : OracleComp (fun _ : G × G => G × G) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) :
    (Game.advantage (feistel3HashIdealGame seed₁ h₁ program)
      (randomFunctionGame program) : ℝ) ≤
      (Q.choose 2 : ℝ) * ε.toReal + (Q.choose 2 : ℝ) * (Fintype.card G : ℝ)⁻¹ := by
  ennreal_to_real using Game.advantage_le_of_apply_le (by finiteness)
    (feistel3HashIdealGame_apply_le hh₁ hQ true)
    (randomFunctionGame_apply_le_feistel3HashIdealGame hh₁ hQ true)

/-- **Classical 3-round Luby–Rackoff theorem** ([BonehShoup2023], Section 4.5, Theorem 4.9;
[LubyRackoff1988]):
three Feistel rounds with independent uniform random round functions on `G` are indistinguishable
from a uniform random function on `G × G` up to `2 * Q.choose 2 / |G| = Q * (Q - 1) / |G|` for any
`Q`-query adaptive adversary. -/
theorem advantage_feistel3RandomRoundsGame_randomFunctionGame_le
    {program : OracleComp (fun _ : G × G => G × G) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) :
    (Game.advantage (feistel3RandomRoundsGame program)
      (randomFunctionGame program) : ℝ) ≤
      2 * (Q.choose 2 : ℝ) * (Fintype.card G : ℝ)⁻¹ := by
  have hcard : (Fintype.card G : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hinv_top : (Fintype.card G : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hcard
  have h := advantage_feistel3HashIdealGame_randomFunctionGame_le
    (isDeltaUniversalHash_uniformOfFintype (X := G) (G := G)) hinv_top hQ
  simp only [feistel3HashIdealGame, id_eq, ENNReal.toReal_inv, ENNReal.toReal_natCast] at h
  change (Game.advantage (feistel3RandomRoundsGame program)
    (randomFunctionGame program) : ℝ) ≤ _ at h
  linarith [h]

omit [AddGroup G] in
/-- **PRP/PRF switching bound on `G × G`**: for any `Q`-query adaptive adversary, `idealPermGame`
and `randomFunctionGame` have distinguishing advantage at most `Q.choose 2 / |G| ^ 2`. -/
theorem advantage_idealPermGame_randomFunctionGame_le [Nonempty G]
    {program : OracleComp (fun _ : G × G => G × G) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) :
    (Game.advantage (idealPermGame program) (randomFunctionGame program) : ℝ) ≤
      (Q.choose 2 : ℝ) * ((Fintype.card G : ℝ)⁻¹) ^ 2 := by
  rw [Game.coe_advantage]
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, idealPermGame,
    randomFunctionGame, Probability.PMF.monad_bind_eq_bind]
  have h := RandomPermutation.abs_sub_uniformPerm_uniformFunc_le hQ PMF.pure true
  simp only [Probability.PMF.monad_bind_eq_bind, PMF.bind_pure] at h
  refine h.trans_eq ?_
  rw [Fintype.card_prod, Nat.cast_mul, mul_inv, sq]

/-- **3-round Luby–Rackoff PRP bound with Δ-universal Round 1**: against a uniform random
permutation on `G × G` (`idealPermGame`), the distinguishing advantage of a `Q`-query adversary is
at most `Q.choose 2 * ε.toReal + Q.choose 2 / |G| + Q.choose 2 / |G| ^ 2`. -/
theorem advantage_feistel3HashIdealGame_idealPermGame_le
    {seed₁ : PMF K₁} {h₁ : K₁ → G → G} {ε : ℝ≥0∞} (hh₁ : IsDeltaUniversalHash seed₁ h₁ ε)
    (hε : ε ≠ ⊤) {program : OracleComp (fun _ : G × G => G × G) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) :
    (Game.advantage (feistel3HashIdealGame seed₁ h₁ program)
      (idealPermGame program) : ℝ) ≤
      (Q.choose 2 : ℝ) * ε.toReal + (Q.choose 2 : ℝ) * (Fintype.card G : ℝ)⁻¹ +
        (Q.choose 2 : ℝ) * ((Fintype.card G : ℝ)⁻¹) ^ 2 := by
  game_trans [randomFunctionGame program] using
    [advantage_feistel3HashIdealGame_randomFunctionGame_le hh₁ hε hQ,
      advantage_idealPermGame_randomFunctionGame_le hQ]

/-- **Classical 3-round Luby–Rackoff PRP bound**: three Feistel rounds with independent uniform
random round functions on `G` are indistinguishable from a uniform random permutation on `G × G`
(`idealPermGame`) up to `2 * Q.choose 2 / |G| + Q.choose 2 / |G| ^ 2`. -/
theorem advantage_feistel3RandomRoundsGame_idealPermGame_le
    {program : OracleComp (fun _ : G × G => G × G) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) :
    (Game.advantage (feistel3RandomRoundsGame program)
      (idealPermGame program) : ℝ) ≤
      2 * (Q.choose 2 : ℝ) * (Fintype.card G : ℝ)⁻¹ +
        (Q.choose 2 : ℝ) * ((Fintype.card G : ℝ)⁻¹) ^ 2 := by
  game_trans [randomFunctionGame program] using
    [advantage_feistel3RandomRoundsGame_randomFunctionGame_le hQ,
      advantage_idealPermGame_randomFunctionGame_le hQ]

/-- Concrete instantiation of the 3-round Luby–Rackoff theorem on `BitString n` (block size `2n`):
the information-theoretic collision error is at most `2 * Q.choose 2 / 2 ^ n`. -/
theorem advantage_feistel3RandomRoundsGame_bitString_le (n : ℕ)
    {program : OracleComp (fun _ : BitString n × BitString n => BitString n × BitString n) Bool}
    {Q : ℕ} (hQ : OracleComp.IsQueryBounded program Q) :
    (Game.advantage (feistel3RandomRoundsGame program)
      (randomFunctionGame program) : ℝ) ≤
      2 * (Q.choose 2 : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by
  have h := advantage_feistel3RandomRoundsGame_randomFunctionGame_le hQ
  simpa only [Fintype.card_pi, Fintype.card_fin, Fintype.card_bool, Finset.prod_const,
    Finset.card_univ, Nat.cast_pow, Nat.cast_ofNat] using h

end LubyRackoff3

/-! ### Chosen-ciphertext separation for 3 rounds and the 4-round random-rounds game -/

section Strong4AndCCAAttack

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]

/-- Bidirectional permutation oracle on `G × G`: `(false, p)` evaluates forward encryption `π p`,
and `(true, q)` evaluates inverse decryption `π.symm q`. -/
noncomputable def feistelStrongOracle (π : G × G ≃ G × G) :
    (q : Bool × (G × G)) → PMF (G × G)
  | (false, p) => PMF.pure (π p)
  | (true, q) => PMF.pure (π.symm q)

/-- Ideal bidirectional random-permutation game on `G × G`: sample a uniform permutation
`π ← PMF.uniformOfFintype (Equiv.Perm (G × G))` and answer forward and inverse queries via
`feistelStrongOracle π`. -/
noncomputable def idealStrongGame
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) : Game := do
  let π ← PMF.uniformOfFintype (Equiv.Perm (G × G))
  OracleComp.interpret (feistelStrongOracle π) program

/-- Bidirectional independent-table game on `Bool × (G × G) → G × G`, where forward and inverse
queries are answered by two independent uniform random functions. -/
noncomputable def independentTableStrongGame [Nonempty G]
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) : Game := do
  let table ← PMF.uniformOfFintype (Bool × (G × G) → G × G)
  OracleComp.interpret (fun q => PMF.pure (table q)) program

/-- **The 3-query chosen-ciphertext distinguisher against 3-round Feistel** ([BonehShoup2023],
Exercise 4.15(b)):
1. Query encryption at `(l₀, r₀)` to obtain `(v₀, w₀)`.
2. Query encryption at `(l₁, r₀)` to obtain `(v₁, w₁)`.
3. Query decryption at `(v₀, (l₁ - l₀) + w₀)` to obtain `(l₂, r₂)`.
4. Accept iff `-v₀ + r₂ = -v₁ + r₀`. -/
def feistel3CCAAttack (l₀ l₁ r₀ : G) :
    OracleComp (fun _ : Bool × (G × G) => G × G) Bool := do
  let vw₀ ← OracleComp.query (spec := fun _ : Bool × (G × G) => G × G) (false, (l₀, r₀))
  let vw₁ ← OracleComp.query (spec := fun _ : Bool × (G × G) => G × G) (false, (l₁, r₀))
  let lr₂ ← OracleComp.query (spec := fun _ : Bool × (G × G) => G × G)
    (true, (vw₀.1, (l₁ - l₀) + vw₀.2))
  return decide (-vw₀.1 + lr₂.2 = -vw₁.1 + r₀)

omit [Fintype G] in
/-- `feistel3CCAAttack` makes at most 3 oracle queries. -/
theorem isQueryBounded_feistel3CCAAttack (l₀ l₁ r₀ : G) :
    OracleComp.IsQueryBounded (feistel3CCAAttack l₀ l₁ r₀) 3 := by
  refine ((OracleComp.IsCostBounded.query (false, (l₀, r₀))).bind fun vw₀ =>
    ((OracleComp.IsCostBounded.query (false, (l₁, r₀))).bind fun vw₁ =>
      (OracleComp.IsCostBounded.query (true, (vw₀.1, (l₁ - l₀) + vw₀.2))).bind fun lr₂ =>
        OracleComp.IsCostBounded.pure _ 0)).mono (by omega)

omit [Fintype G] in
/-- **Every 3-round Feistel network `feistel3 f₁ f₂ f₃` is accepted with probability `1` by
`feistel3CCAAttack`** ([BonehShoup2023], Exercise 4.15(b)), for any round functions `f₁, f₂, f₃`
and any `l₀, l₁, r₀ : G`. -/
theorem eval_feistel3_feistel3CCAAttack (f₁ f₂ f₃ : G → G) (l₀ l₁ r₀ : G) :
    OracleComp.interpret (feistelStrongOracle (feistel3 f₁ f₂ f₃))
      (feistel3CCAAttack l₀ l₁ r₀) = PMF.pure true := by
  simp only [interp_norm, pmf_norm, feistel3CCAAttack, feistelStrongOracle, feistel3_apply,
    feistel3_symm_apply]
  have h1 :
      (l₁ - l₀ + (l₀ + f₁ r₀ + f₃ (r₀ + f₂ (l₀ + f₁ r₀)))) - f₃ (r₀ + f₂ (l₀ + f₁ r₀)) =
        l₁ + f₁ r₀ := by
    rw [← add_assoc (l₁ - l₀), add_sub_cancel_right, ← add_assoc, sub_add_cancel]
  have h2 :
      -(r₀ + f₂ (l₀ + f₁ r₀)) +
        ((r₀ + f₂ (l₀ + f₁ r₀)) - f₂ (l₁ + f₁ r₀)) =
      -(r₀ + f₂ (l₁ + f₁ r₀)) + r₀ := by
    rw [sub_eq_add_neg, neg_add_cancel_left, neg_add_rev, neg_add_cancel_right]
  rw [h1, decide_eq_true h2]

omit [Fintype G] in
/-- When `l₀ = l₁`, the third query of `feistel3CCAAttack l₀ l₀ r₀` asks to invert the first
ciphertext, so *every* bidirectional permutation `π : G × G ≃ G × G` is accepted with probability
`1`. -/
theorem eval_feistelStrongOracle_feistel3CCAAttack_self (π : G × G ≃ G × G) (l₀ r₀ : G) :
    OracleComp.interpret (feistelStrongOracle π) (feistel3CCAAttack l₀ l₀ r₀) =
      PMF.pure true := by
  simp only [interp_norm, pmf_norm, feistel3CCAAttack, feistelStrongOracle, sub_self, zero_add,
    Prod.mk.eta, Equiv.symm_apply_apply, decide_true]

/-- At `l₀ = l₁`, the permutation-ideal game `idealStrongGame` accepts `feistel3CCAAttack l₀ l₀ r₀`
with probability `1`. -/
theorem idealStrongGame_feistel3CCAAttack_self (l₀ r₀ : G) :
    idealStrongGame (feistel3CCAAttack l₀ l₀ r₀) = PMF.pure true := by
  simp only [idealStrongGame, Probability.PMF.monad_bind_eq_bind,
    eval_feistelStrongOracle_feistel3CCAAttack_self, PMF.bind_const]

/-- At `l₀ = l₁`, `feistel3CCAAttack l₀ l₀ r₀` has zero advantage between any 3-round Feistel
network and the true bidirectional random-permutation game `idealStrongGame`. -/
theorem advantage_feistel3CCAAttack_self (f₁ f₂ f₃ : G → G) (l₀ r₀ : G) :
    Game.advantage
      (OracleComp.interpret (feistelStrongOracle (feistel3 f₁ f₂ f₃))
        (feistel3CCAAttack l₀ l₀ r₀))
      (idealStrongGame (feistel3CCAAttack l₀ l₀ r₀)) = 0 := by
  rw [eval_feistel3_feistel3CCAAttack, idealStrongGame_feistel3CCAAttack_self, Game.advantage_self]

omit [Fintype G] in
/-- When `l₀, l₁, l₂ : G` are pairwise distinct (`|G| ≥ 3`), the transposition
`Equiv.swap (l₀, (l₁ - l₀) + r₀) (l₂, r₀)` fixes `(l₀, r₀)` and `(l₁, r₀)` while mapping
`(l₀, (l₁ - l₀) + r₀)` to `(l₂, r₀)`, so `feistel3CCAAttack l₀ l₁ r₀` rejects it with probability
`1`. -/
theorem eval_feistelStrongOracle_swap_feistel3CCAAttack_eq_false {l₀ l₁ l₂ r₀ : G}
    (h01 : l₀ ≠ l₁) (h02 : l₀ ≠ l₂) (h12 : l₁ ≠ l₂) :
    OracleComp.interpret
      (feistelStrongOracle (Equiv.swap (l₀, (l₁ - l₀) + r₀) (l₂, r₀)))
      (feistel3CCAAttack l₀ l₁ r₀) = PMF.pure false := by
  have hA1 : (l₀, r₀) ≠ (l₀, (l₁ - l₀) + r₀) := fun h =>
    h01 (sub_eq_zero.mp (add_right_cancel ((zero_add r₀).trans (congrArg Prod.snd h))).symm).symm
  have hA2 : (l₀, r₀) ≠ (l₂, r₀) := fun h => h02 (congrArg Prod.fst h)
  have hB1 : (l₁, r₀) ≠ (l₀, (l₁ - l₀) + r₀) := fun h => h01 (congrArg Prod.fst h).symm
  have hB2 : (l₁, r₀) ≠ (l₂, r₀) := fun h => h12 (congrArg Prod.fst h)
  have hne : -l₀ + r₀ ≠ -l₁ + r₀ := fun h =>
    h01 (neg_inj.mp (add_right_cancel h))
  simp only [interp_norm, pmf_norm, feistel3CCAAttack, feistelStrongOracle, Equiv.symm_swap,
    Equiv.swap_apply_of_ne_of_ne hA1 hA2, Equiv.swap_apply_of_ne_of_ne hB1 hB2,
    Equiv.swap_apply_left, decide_eq_false hne]

/-- When `l₀, l₁, l₂ : G` are pairwise distinct, `idealStrongGame (feistel3CCAAttack l₀ l₁ r₀)`
rejects (`false`) with probability at least `|Equiv.Perm (G × G)|⁻¹`. -/
theorem le_idealStrongGame_feistel3CCAAttack_false {l₀ l₁ l₂ r₀ : G}
    (h01 : l₀ ≠ l₁) (h02 : l₀ ≠ l₂) (h12 : l₁ ≠ l₂) :
    (Fintype.card (Equiv.Perm (G × G)) : ℝ≥0∞)⁻¹ ≤
      idealStrongGame (feistel3CCAAttack l₀ l₁ r₀) false := by
  let π₀ : Equiv.Perm (G × G) := Equiv.swap (l₀, (l₁ - l₀) + r₀) (l₂, r₀)
  rw [idealStrongGame, Probability.PMF.monad_bind_eq_bind, PMF.bind_apply]
  calc (Fintype.card (Equiv.Perm (G × G)) : ℝ≥0∞)⁻¹
      = PMF.uniformOfFintype (Equiv.Perm (G × G)) π₀ *
          OracleComp.interpret (feistelStrongOracle π₀) (feistel3CCAAttack l₀ l₁ r₀) false := by
        rw [PMF.uniformOfFintype_apply,
          eval_feistelStrongOracle_swap_feistel3CCAAttack_eq_false h01 h02 h12,
          PMF.pure_apply_self, mul_one]
    _ ≤ ∑' π : Equiv.Perm (G × G),
          PMF.uniformOfFintype (Equiv.Perm (G × G)) π *
            OracleComp.interpret (feistelStrongOracle π) (feistel3CCAAttack l₀ l₁ r₀) false :=
        le_tsum (f := fun π : Equiv.Perm (G × G) =>
          PMF.uniformOfFintype (Equiv.Perm (G × G)) π *
            OracleComp.interpret (feistelStrongOracle π) (feistel3CCAAttack l₀ l₁ r₀) false) π₀

/-- When `l₀, l₁, l₂ : G` are pairwise distinct (`|G| ≥ 3`), `feistel3CCAAttack l₀ l₁ r₀`
distinguishes any 3-round Feistel network from the true bidirectional random-permutation game
`idealStrongGame` with advantage at least `|Equiv.Perm (G × G)|⁻¹`. -/
theorem le_advantage_feistel3CCAAttack_idealStrongGame (f₁ f₂ f₃ : G → G) {l₀ l₁ l₂ r₀ : G}
    (h01 : l₀ ≠ l₁) (h02 : l₀ ≠ l₂) (h12 : l₁ ≠ l₂) :
    (Fintype.card (Equiv.Perm (G × G)) : ℝ)⁻¹ ≤
      (Game.advantage
        (OracleComp.interpret (feistelStrongOracle (feistel3 f₁ f₂ f₃))
          (feistel3CCAAttack l₀ l₁ r₀))
        (idealStrongGame (feistel3CCAAttack l₀ l₁ r₀)) : ℝ) := by
  set g := idealStrongGame (feistel3CCAAttack l₀ l₁ r₀)
  have hfail := le_idealStrongGame_feistel3CCAAttack_false (r₀ := r₀) h01 h02 h12
  ennreal_to_real at hfail
  rwa [eval_feistel3_feistel3CCAAttack, Game.advantage_pure_true_left, Game.coe_failProbability]

/-- When `l₀, l₁, l₂ : G` are pairwise distinct (`|G| ≥ 3`), `feistel3CCAAttack l₀ l₁ r₀` has
strictly positive distinguishing advantage against the true bidirectional random-permutation game
`idealStrongGame`. -/
theorem advantage_feistel3CCAAttack_idealStrongGame_pos (f₁ f₂ f₃ : G → G) {l₀ l₁ l₂ r₀ : G}
    (h01 : l₀ ≠ l₁) (h02 : l₀ ≠ l₂) (h12 : l₁ ≠ l₂) :
    0 < (Game.advantage
      (OracleComp.interpret (feistelStrongOracle (feistel3 f₁ f₂ f₃))
        (feistel3CCAAttack l₀ l₁ r₀))
      (idealStrongGame (feistel3CCAAttack l₀ l₁ r₀)) : ℝ) := by
  have hpos : (0 : ℝ) < (Fintype.card (Equiv.Perm (G × G)) : ℝ)⁻¹ :=
    inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  exact hpos.trans_le (le_advantage_feistel3CCAAttack_idealStrongGame f₁ f₂ f₃ h01 h02 h12)

private theorem uniformOfFintype_prod_map_decide_add_snd_true (a t : G) :
    ((PMF.uniformOfFintype (G × G)).map (fun lr : G × G => decide (a + lr.2 = t))) true =
      (Fintype.card G : ℝ≥0∞)⁻¹ := by
  have hmap :
      (PMF.uniformOfFintype (G × G)).map (fun lr : G × G => decide (a + lr.2 = t)) =
        (PMF.uniformOfFintype G).map (fun y => decide (y = t)) := by
    rw [← Probability.PMF.uniformOfFintype_map_add_left a,
      ← Probability.PMF.uniformOfFintype_prod_map_snd (α := G) (β := G)]
    simp only [PMF.map_comp, Function.comp_def]
  rw [hmap, Probability.PMF.map_decide_eq_apply_true, PMF.uniformOfFintype_apply]

omit [AddGroup G] [Fintype G] [DecidableEq G] in
private theorem interpret_feistelStrongOracle_eq_liftBoolProd (π : Equiv.Perm (G × G))
    {α : Type} (program : OracleComp (fun _ : Bool × (G × G) => G × G) α) :
    OracleComp.interpret (feistelStrongOracle π) program =
      OracleComp.interpret (fun q => PMF.pure (RandomPermutation.evalPerm π q))
        (RandomPermutation.liftBoolProd program) := by
  rw [RandomPermutation.liftBoolProd, OracleComp.interpret_interpret]
  congr 1; funext ⟨b, p⟩; cases b <;> simp [feistelStrongOracle]

omit [AddGroup G] in
private theorem idealStrongGame_eq_bind_liftBoolProd
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) :
    idealStrongGame program =
      ((PMF.uniformOfFintype (Equiv.Perm (G × G))).bind fun π =>
        OracleComp.interpret (fun q => PMF.pure (RandomPermutation.evalPerm π q))
          (RandomPermutation.liftBoolProd program)) := by
  simp only [idealStrongGame, Probability.PMF.monad_bind_eq_bind,
    interpret_feistelStrongOracle_eq_liftBoolProd]

/-- Against the independent-table game `independentTableStrongGame`, `feistel3CCAAttack l₀ l₁ r₀`
accepts with probability `|G|⁻¹`. -/
theorem eval_independentTableStrongGame_feistel3CCAAttack (l₀ l₁ r₀ : G) :
    independentTableStrongGame (feistel3CCAAttack l₀ l₁ r₀) true =
      (Fintype.card G : ℝ≥0∞)⁻¹ := by
  have hprod : PMF.uniformOfFintype (Bool × (G × G) → G × G) =
      (PMF.uniformOfFintype (G × G → G × G)).bind fun encTable =>
        (PMF.uniformOfFintype (G × G → G × G)).map fun decTable =>
          splitBoolTable.symm (encTable, decTable) := by
    relabel_uniform splitBoolTable.symm
  rw [independentTableStrongGame, Probability.PMF.monad_bind_eq_bind, hprod]
  simp only [interp_norm, pmf_norm, feistel3CCAAttack, splitBoolTable, Equiv.coe_fn_symm_mk,
    Bool.cond_false, Bool.cond_true]
  refine Probability.PMF.bind_apply_of_forall _ fun encTable => ?_
  set vw₀ := encTable (l₀, r₀)
  set q₃ := (vw₀.1, (l₁ - l₀) + vw₀.2)
  have heval : (PMF.uniformOfFintype (G × G → G × G)).map (fun t => t q₃) =
      PMF.uniformOfFintype (G × G) := by
    rw [← Probability.PMF.pi_uniformOfFintype, Probability.PMF.pi_map_eval]
  have hmap := congrArg (fun d => (d.map fun lr : G × G =>
      decide (-vw₀.1 + lr.2 = -(encTable (l₁, r₀)).1 + r₀)) true) heval
  rw [PMF.map_comp] at hmap
  exact hmap.trans (uniformOfFintype_prod_map_decide_add_snd_true (-vw₀.1)
    (-(encTable (l₁, r₀)).1 + r₀))

/-- The 3-query CCA attack `feistel3CCAAttack` distinguishes any 3-round Feistel network from
the independent-table game `independentTableStrongGame` with exact advantage `1 - |G|⁻¹`. -/
theorem advantage_feistel3CCAAttack_independentTable (f₁ f₂ f₃ : G → G) (l₀ l₁ r₀ : G) :
    (Game.advantage
      (OracleComp.interpret (feistelStrongOracle (feistel3 f₁ f₂ f₃))
        (feistel3CCAAttack l₀ l₁ r₀))
      (independentTableStrongGame (feistel3CCAAttack l₀ l₁ r₀)) : ℝ) =
      1 - (Fintype.card G : ℝ)⁻¹ := by
  rw [eval_feistel3_feistel3CCAAttack, Game.coe_advantage_pure_true_left,
    eval_independentTableStrongGame_feistel3CCAAttack, ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- When `l₀ ≠ l₁`, the true bidirectional random-permutation game `idealStrongGame` accepts
`feistel3CCAAttack l₀ l₁ r₀` with probability at most `|G|⁻¹ + 4 * |G × G|⁻¹`. -/
theorem idealStrongGame_feistel3CCAAttack_true_le {l₀ l₁ : G} (r₀ : G) (h01 : l₀ ≠ l₁) :
    idealStrongGame (feistel3CCAAttack l₀ l₁ r₀) true ≤
      (Fintype.card G : ℝ≥0∞)⁻¹ + 4 * (Fintype.card (G × G) : ℝ≥0∞)⁻¹ := by
  have hswitch := RandomPermutation.uniformPerm_bind_apply_le_forgetful
    (RandomPermutation.isQueryBounded_liftBoolProd (isQueryBounded_feistel3CCAAttack l₀ l₁ r₀))
    PMF.pure true
  simp only [Probability.PMF.monad_bind_eq_bind, PMF.bind_pure,
    ← idealStrongGame_eq_bind_liftBoolProd] at hswitch
  have hp10 : (l₁, r₀) ≠ (l₀, r₀) := fun h => h01 (congrArg Prod.fst h).symm
  have hrun :
      ((OracleComp.interpret RandomPermutation.forgetfulAnswer
        (RandomPermutation.liftBoolProd (feistel3CCAAttack l₀ l₁ r₀))).run []).map Prod.fst =
        (PMF.uniformOfFintype (G × G)).bind fun vw₀ =>
          (PMF.uniformOfFintype (G × G)).bind fun vw₁ =>
            (RandomPermutation.forgetfulAnswer (.inverse (vw₀.1, (l₁ - l₀) + vw₀.2))
              [((l₁, r₀), vw₁), ((l₀, r₀), vw₀)]).map
              (fun x => decide (-vw₀.1 + x.1.2 = -vw₁.1 + r₀)) := by
    simp only [feistel3CCAAttack, RandomPermutation.liftBoolProd,
      RandomPermutation.PermQuery.ofBoolProd, interp_norm]
    dsimp only [StateT.run, RandomPermutation.forgetfulAnswer]
    simp only [pmf_norm, List.lookup, beq_eq_false_iff_ne.mpr hp10]
    rfl
  have hforget :
      (((OracleComp.interpret RandomPermutation.forgetfulAnswer
        (RandomPermutation.liftBoolProd (feistel3CCAAttack l₀ l₁ r₀))).run []).map Prod.fst)
          true ≤ (Fintype.card G : ℝ≥0∞)⁻¹ + (Fintype.card (G × G) : ℝ≥0∞)⁻¹ := by
    rw [hrun]
    refine Probability.PMF.bind_apply_le_on_support _ fun vw₀ _ => ?_
    set q₃ : G × G := (vw₀.1, (l₁ - l₀) + vw₀.2)
    have hvw₀_ne : vw₀ ≠ q₃ := fun h => h01
      (sub_eq_zero.mp (add_right_cancel ((zero_add vw₀.2).trans (congrArg Prod.snd h))).symm).symm
    rw [PMF.bind_apply, add_comm]
    refine (Probability.PMF.tsum_mul_le_card_mul_add (PMF.uniformOfFintype (G × G))
        (fun x => (PMF.uniformOfFintype_apply x).le) {q₃}
        (B := (Fintype.card G : ℝ≥0∞)⁻¹) fun vw₁ => ?_).trans_eq
      (by simp)
    by_cases h13 : vw₁ = q₃
    · simp only [Finset.mem_singleton, h13, ↓reduceIte]
      exact (PMF.coe_le_one _ true).trans le_self_add
    · simp only [Finset.mem_singleton, h13, ↓reduceIte, zero_add]
      have hinv : RandomPermutation.invLookup [((l₁, r₀), vw₁), ((l₀, r₀), vw₀)] q₃ = none := by
        simp [RandomPermutation.invLookup, Ne.symm h13, Ne.symm hvw₀_ne]
      dsimp only [RandomPermutation.forgetfulAnswer]
      rw [hinv, PMF.map_comp]
      exact (uniformOfFintype_prod_map_decide_add_snd_true (-vw₀.1) (-vw₁.1 + r₀)).le
  exact (hswitch.trans (add_le_add hforget le_rfl)).trans_eq (by
    simp only [show (Nat.choose 3 2 : ℝ≥0∞) = 3 from rfl]; ring)

/-- **Quantitative nonnegligible CCA advantage lower bound against `idealStrongGame`**
([BonehShoup2023], Section 4.1.3 and Exercise 4.15(b)): whenever `l₀ ≠ l₁`, the 3-query
chosen-ciphertext distinguisher `feistel3CCAAttack l₀ l₁ r₀` distinguishes any 3-round Feistel
network `feistel3 f₁ f₂ f₃` from a uniform random permutation on `G × G` (`idealStrongGame`) with
advantage at least `1 - |G|⁻¹ - 4 * |G|⁻¹ ^ 2`. -/
theorem le_advantage_feistel3CCAAttack_idealStrongGame_of_ne (f₁ f₂ f₃ : G → G) {l₀ l₁ r₀ : G}
    (h01 : l₀ ≠ l₁) :
    1 - (Fintype.card G : ℝ)⁻¹ - 4 * ((Fintype.card G : ℝ)⁻¹) ^ 2 ≤
      (Game.advantage
        (OracleComp.interpret (feistelStrongOracle (feistel3 f₁ f₂ f₃))
          (feistel3CCAAttack l₀ l₁ r₀))
        (idealStrongGame (feistel3CCAAttack l₀ l₁ r₀)) : ℝ) := by
  have htrue := idealStrongGame_feistel3CCAAttack_true_le r₀ h01
  ennreal_to_real at htrue
  rw [Fintype.card_prod, Nat.cast_mul, mul_inv, ← sq] at htrue
  rw [eval_feistel3_feistel3CCAAttack, Game.coe_advantage_pure_true_left]
  linarith

/-- 4-round Feistel strong (bidirectional) game with four independent uniform random round
functions `f₁, f₂, f₃, f₄ : G → G`. -/
noncomputable def feistel4StrongRandomRoundsGame
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) : Game := do
  let f₁ ← PMF.uniformOfFintype (G → G)
  let f₂ ← PMF.uniformOfFintype (G → G)
  let f₃ ← PMF.uniformOfFintype (G → G)
  let f₄ ← PMF.uniformOfFintype (G → G)
  OracleComp.interpret (feistelStrongOracle (feistel4 f₁ f₂ f₃ f₄)) program

/-! ### 4-round bidirectional random-round collision analysis and strong PRP Luby–Rackoff theorem -/

/-- 4-round strong Feistel game with fixed outer round functions `f₁, f₄ : G → G` and independent
uniform random inner round functions `f₂, f₃ : G → G`. -/
private noncomputable def feistel4StrongFixedGame (f₁ f₄ : G → G)
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) : Game := do
  let f₂ ← PMF.uniformOfFintype (G → G)
  let f₃ ← PMF.uniformOfFintype (G → G)
  OracleComp.interpret (feistelStrongOracle (feistel4 f₁ f₂ f₃ f₄)) program

private theorem feistel4StrongRandomRoundsGame_eq_bind_fixed
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) :
    feistel4StrongRandomRoundsGame program = (do
      let f₁ ← PMF.uniformOfFintype (G → G)
      let f₄ ← PMF.uniformOfFintype (G → G)
      feistel4StrongFixedGame f₁ f₄ program) := by
  simp only [feistel4StrongRandomRoundsGame, feistel4StrongFixedGame,
    Probability.PMF.monad_bind_eq_bind]
  pmf_swap

/-- Round-4 intermediate collision predicate `v = wz.2 - f₄ wz.1`. -/
private def hasVCollision4 (f₄ : G → G) (qc : List ((G × G) × (G × G))) : Bool :=
  hasColl (fun e => e.2.2 - f₄ e.2.1) qc

/-- Outer-round collision in `qc`: Round-1 `u` collision or Round-4 `v` collision. -/
private def hasCollision4 (f₁ f₄ : G → G) (qc : List ((G × G) × (G × G))) : Bool :=
  hasUCollision f₁ qc || hasVCollision4 f₄ qc

/-- Two-step inner-round coupling for `feistel4StrongFixedGame` against
`RandomPermutation.forgetfulAnswer`. -/
private theorem feistel4StrongFixedGame_and_forgetful_le (f₁ f₄ : G → G)
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) (b : Bool) :
    let prog := RandomPermutation.liftBoolProd program
    let ref := (OracleComp.interpret RandomPermutation.forgetfulAnswer prog).run []
    feistel4StrongFixedGame f₁ f₄ program b ≤
        (ref.map Prod.fst) b + ref.toOuterMeasure {x | hasCollision4 f₁ f₄ x.2 = true} ∧
      (ref.map Prod.fst) b ≤
        feistel4StrongFixedGame f₁ f₄ program b +
          ref.toOuterMeasure {x | hasCollision4 f₁ f₄ x.2 = true} := by
  let invOut : G × G ≃ G × G := (Equiv.prodComm G G).trans (feistelRoundEquiv f₁).symm
  let params : RandomPermutation.PermQuery (G × G) → TwoStepParams G
    | .forward p =>
      ⟨false, p.1 + f₁ p.2, Equiv.addLeft p.2, Equiv.addLeft (p.1 + f₁ p.2), feistelRoundEquiv f₄⟩
    | .inverse wz =>
      ⟨true, wz.2 - f₄ wz.1, Equiv.subLeft wz.1, Equiv.subLeft (wz.2 - f₄ wz.1), invOut⟩
  refine apply_le_both_of_twoStep params (fun e => e.1.1 + f₁ e.1.2) (fun e => e.2.2 - f₄ e.2.1)
    RandomPermutation.bidirDedupStep RandomPermutation.forgetfulAnswer
    (RandomPermutation.liftBoolProd program)
    (fun f₂ f₃ => OracleComp.interpret (feistelStrongOracle (feistel4 f₁ f₂ f₃ f₄)) program)
    (fun table => ?_) (fun q qc k₁ k₂ st hst hk => ?_) b
  · have hstep : (fun q => OracleComp.interpret (fun x => PMF.pure (table x)) (params q).query) =
        (fun q => PMF.pure (RandomPermutation.evalPerm
          (feistel4 f₁ (fun u => table (false, u)) (fun v => table (true, v)) f₄) q)) := by
      funext q; cases q <;>
        simp [params, TwoStepParams.query, invOut, feistel4_apply, feistel4_symm_apply,
          feistelRound, feistelInvRound, feistel3_apply, feistel3_symm_apply, add_assoc]
    rw [hstep]
    exact (RandomPermutation.map_fst_interpret_bidirDedup_evalPerm _ _).trans
      (interpret_feistelStrongOracle_eq_liftBoolProd _ _).symm
  · cases q with
    | forward p =>
      cases h : qc.lookup p with
      | some wz =>
        rw [RandomPermutation.bidirDedupStep_forward_of_some h,
          RandomPermutation.forgetfulAnswer_forward_of_some h]
        simp only [interp_norm, pmf_norm]; exact hk wz qc st hst
      | none =>
        rw [RandomPermutation.bidirDedupStep_forward_of_none h,
          RandomPermutation.forgetfulAnswer_forward_of_none h]
        simp only [interp_norm, pmf_norm]
        exact twoStep_miss_bind hst (fun wz => (p, wz)) (fun _ => rfl) (fun _ => rfl) k₁ k₂ hk
    | inverse wz =>
      cases h : RandomPermutation.invLookup qc wz with
      | some p =>
        rw [RandomPermutation.bidirDedupStep_inverse_of_some h,
          RandomPermutation.forgetfulAnswer_inverse_of_some h]
        simp only [interp_norm, pmf_norm]; exact hk p qc st hst
      | none =>
        rw [RandomPermutation.bidirDedupStep_inverse_of_none h,
          RandomPermutation.forgetfulAnswer_inverse_of_none h]
        simp only [interp_norm, pmf_norm]
        exact twoStep_miss_bind hst (fun p => (p, wz)) (fun _ => rfl) (fun _ => rfl) k₁ k₂ hk

/-- Local shorthand for a `Q`-bounded partial-bijection trace `c` with pairwise-distinct domain
and range entries. -/
private def IsGoodCache4 (Q : ℕ) (c : RandomPermutation.Cache (G × G)) : Prop :=
  c.Pairwise (fun x y => x.1 ≠ y.1) ∧ c.Pairwise (fun x y => x.2 ≠ y.2) ∧ c.length ≤ Q

omit [AddGroup G] in
/-- Averaged over a uniform `f : G → G`, a good `Q`-bounded cache hits `coll f` with probability
at most `Q.choose 2 * |G|⁻¹`. -/
private theorem tsum_uniform_goodCollision_le [Nonempty G] (Q : ℕ)
    (coll : (G → G) → RandomPermutation.Cache (G × G) → Bool)
    (hcoll : ∀ c, IsGoodCache4 Q c →
      (PMF.uniformOfFintype (G → G)).toOuterMeasure {f | coll f c = true} ≤
        c.length.choose 2 * (Fintype.card G : ℝ≥0∞)⁻¹)
    (d : PMF (Bool × RandomPermutation.Cache (G × G))) :
    (∑' f : G → G, PMF.uniformOfFintype (G → G) f *
      d.toOuterMeasure {x | IsGoodCache4 Q x.2 ∧ coll f x.2 = true}) ≤
      Q.choose 2 * (Fintype.card G : ℝ≥0∞)⁻¹ := by
  refine tsum_toOuterMeasure_of_pointwise_le (PMF.uniformOfFintype (G → G)) d
    (fun f x => IsGoodCache4 Q x.2 ∧ coll f x.2 = true) _ fun x _ => ?_
  by_cases hg : IsGoodCache4 Q x.2
  · exact (MeasureTheory.measure_mono
        (show {f : G → G | IsGoodCache4 Q x.2 ∧ coll f x.2 = true} ⊆ {f | coll f x.2 = true}
          from fun _ h => h.2)).trans ((hcoll x.2 hg).trans (mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (Nat.choose_le_choose 2 hg.2.2)) zero_le))
  · simp [show {f : G → G | IsGoodCache4 Q x.2 ∧ coll f x.2 = true} = ∅ by ext; simp [hg]]

private theorem tsum_uniform_toOuterMeasure_hasCollision4_le
    {prog : OracleComp (RandomPermutation.PermOracleSpec (G × G)) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded prog Q) :
    (∑' f₁ : G → G, PMF.uniformOfFintype (G → G) f₁ *
      ∑' f₄ : G → G, PMF.uniformOfFintype (G → G) f₄ *
        ((OracleComp.interpret RandomPermutation.forgetfulAnswer prog).run []).toOuterMeasure
          {x | hasCollision4 f₁ f₄ x.2 = true}) ≤
      2 * (Q.choose 2 : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹ +
        (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹ := by
  set d := (OracleComp.interpret RandomPermutation.forgetfulAnswer prog).run []
  set unif := PMF.uniformOfFintype (G → G)
  have hsplit (f₁ f₄ : G → G) :
      d.toOuterMeasure {x | hasCollision4 f₁ f₄ x.2 = true} ≤
        d.toOuterMeasure {x | IsGoodCache4 Q x.2 ∧ hasUCollision f₁ x.2 = true} +
        (d.toOuterMeasure {x | IsGoodCache4 Q x.2 ∧ hasVCollision4 f₄ x.2 = true} +
          (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹) := by
    have hgood := RandomPermutation.toOuterMeasure_forgetfulAnswer_le_pairwise_and_length_le_add hQ
      (fun c => hasCollision4 f₁ f₄ c = true)
    have hunion :
        d.toOuterMeasure {x | IsGoodCache4 Q x.2 ∧ hasCollision4 f₁ f₄ x.2 = true} ≤
          d.toOuterMeasure {x | IsGoodCache4 Q x.2 ∧ hasUCollision f₁ x.2 = true} +
            d.toOuterMeasure {x | IsGoodCache4 Q x.2 ∧ hasVCollision4 f₄ x.2 = true} :=
      calc d.toOuterMeasure {x | IsGoodCache4 Q x.2 ∧ hasCollision4 f₁ f₄ x.2 = true}
          ≤ d.toOuterMeasure ({x | IsGoodCache4 Q x.2 ∧ hasUCollision f₁ x.2 = true} ∪
              {x | IsGoodCache4 Q x.2 ∧ hasVCollision4 f₄ x.2 = true}) :=
            d.toOuterMeasure.mono fun _ hx =>
              ((Bool.or_eq_true _ _).mp hx.2).imp (⟨hx.1, ·⟩) (⟨hx.1, ·⟩)
        _ ≤ _ := MeasureTheory.measure_union_le _ _
    exact (hgood.trans (add_le_add hunion le_rfl)).trans_eq (add_assoc _ _ _)
  have hV := tsum_uniform_goodCollision_le Q hasVCollision4 (fun c hg => by
    simpa only [hasVCollision4, Prod.fst_swap, Prod.snd_swap, ← sub_eq_add_neg] using
      toOuterMeasure_hasColl_delta_le isDeltaUniversalHash_neg_uniformOfFintype
        (fun e : (G × G) × (G × G) => e.2.swap)
        (hg.2.1.imp fun h heq => h (Prod.swap_injective heq))) d
  have hU := tsum_uniform_goodCollision_le Q hasUCollision (fun _ hg =>
    toOuterMeasure_hasColl_delta_le isDeltaUniversalHash_uniformOfFintype Prod.fst hg.1) d
  have hinner (f₁ : G → G) :
      ∑' f₄, unif f₄ * d.toOuterMeasure {x | hasCollision4 f₁ f₄ x.2 = true} ≤
        d.toOuterMeasure {x | IsGoodCache4 Q x.2 ∧ hasUCollision f₁ x.2 = true} +
          (Q.choose 2 * (Fintype.card G : ℝ≥0∞)⁻¹ +
            (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹) := by
    refine (tsum_mul_le_add unif (hsplit f₁)).trans ?_
    rw [tsum_mul_const]
    refine add_le_add le_rfl ((tsum_mul_le_add unif fun _ => le_rfl).trans ?_)
    rw [tsum_mul_const]
    exact add_le_add hV le_rfl
  refine (tsum_le_tsum fun f₁ => mul_le_mul_of_nonneg_left (hinner f₁) zero_le).trans ?_
  simp only [mul_add, tsum_add, tsum_mul_const]
  exact (add_le_add hU le_rfl).trans_eq (by ring)

/-- **4-round strong Luby–Rackoff theorem in `ℝ≥0∞` (one-sided)**: for any adaptive
bidirectional program making at most `Q` forward or inverse queries,
`feistel4StrongRandomRoundsGame` accepts with probability at most `idealStrongGame` plus
`2 * Q.choose 2 * |G|⁻¹ + 2 * Q.choose 2 * |G × G|⁻¹`. -/
theorem feistel4StrongRandomRoundsGame_apply_le
    {program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) (b : Bool) :
    feistel4StrongRandomRoundsGame program b ≤
      idealStrongGame program b +
        (2 * (Q.choose 2 : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹ +
          2 * (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹) := by
  have hQ' := RandomPermutation.isQueryBounded_liftBoolProd hQ
  set unif := PMF.uniformOfFintype (G → G)
  have hstep : feistel4StrongRandomRoundsGame program b ≤
      (((OracleComp.interpret RandomPermutation.forgetfulAnswer
        (RandomPermutation.liftBoolProd program)).run []).map Prod.fst) b +
      (2 * (Q.choose 2 : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹ +
        (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹) := by
    rw [feistel4StrongRandomRoundsGame_eq_bind_fixed, Probability.PMF.monad_bind_eq_bind]
    simp only [PMF.bind_apply]
    refine (tsum_mul_le_add unif fun f₁ =>
      tsum_mul_le_add unif fun f₄ =>
        (feistel4StrongFixedGame_and_forgetful_le f₁ f₄ program b).1).trans ?_
    simp only [tsum_mul_const]
    exact add_le_add le_rfl (tsum_uniform_toOuterMeasure_hasCollision4_le hQ')
  have hperm := RandomPermutation.forgetfulAnswer_bind_apply_le_uniformPerm hQ' PMF.pure b
  simp only [Probability.PMF.monad_bind_eq_bind, PMF.bind_pure,
    ← idealStrongGame_eq_bind_liftBoolProd] at hperm
  exact (hstep.trans (add_le_add hperm le_rfl)).trans_eq (by ring)

/-- **Reverse 4-round strong Luby–Rackoff inequality in `ℝ≥0∞`**: for any adaptive bidirectional
program making at most `Q` forward or inverse queries, `idealStrongGame` accepts with probability
at most `feistel4StrongRandomRoundsGame` plus
`2 * Q.choose 2 * |G|⁻¹ + 2 * Q.choose 2 * |G × G|⁻¹`. -/
theorem idealStrongGame_apply_le_feistel4StrongRandomRoundsGame
    {program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) (b : Bool) :
    idealStrongGame program b ≤
      feistel4StrongRandomRoundsGame program b +
        (2 * (Q.choose 2 : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹ +
          2 * (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹) := by
  have hQ' := RandomPermutation.isQueryBounded_liftBoolProd hQ
  set unif := PMF.uniformOfFintype (G → G)
  set forgetVal := (((OracleComp.interpret RandomPermutation.forgetfulAnswer
      (RandomPermutation.liftBoolProd program)).run []).map Prod.fst) b
  have hstep :
      forgetVal ≤ feistel4StrongRandomRoundsGame program b +
        (2 * (Q.choose 2 : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹ +
          (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹) := by
    rw [feistel4StrongRandomRoundsGame_eq_bind_fixed, Probability.PMF.monad_bind_eq_bind]
    simp only [PMF.bind_apply]
    rw [← tsum_mul_const unif forgetVal]
    refine (tsum_mul_le_add unif fun f₁ => by
      rw [← tsum_mul_const unif forgetVal]
      exact tsum_mul_le_add unif fun f₄ =>
        (feistel4StrongFixedGame_and_forgetful_le f₁ f₄ program b).2).trans ?_
    exact add_le_add le_rfl (tsum_uniform_toOuterMeasure_hasCollision4_le hQ')
  have hperm := RandomPermutation.uniformPerm_bind_apply_le_forgetful hQ' PMF.pure b
  simp only [Probability.PMF.monad_bind_eq_bind, PMF.bind_pure,
    ← idealStrongGame_eq_bind_liftBoolProd] at hperm
  exact (hperm.trans (add_le_add hstep le_rfl)).trans_eq (by ring)

/-- **4-round strong Luby–Rackoff theorem with random round functions** ([LubyRackoff1988]; see
[BonehShoup2023], Section 4.1.3 for strongly secure block ciphers; the concrete constant comes
from this proof): when all four round functions `f₁, f₂, f₃, f₄ : G → G` are
independent uniform random functions, any `Q`-query adaptive chosen-ciphertext distinguisher has
distinguishing advantage against a uniform random permutation on `G × G` (`idealStrongGame`) at
most `2 * Q.choose 2 * |G|⁻¹ + 2 * Q.choose 2 * (|G|⁻¹) ^ 2`. -/
theorem advantage_feistel4StrongRandomRoundsGame_idealStrongGame_le
    {program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) :
    (Game.advantage (feistel4StrongRandomRoundsGame program)
      (idealStrongGame program) : ℝ) ≤
      2 * (Q.choose 2 : ℝ) * (Fintype.card G : ℝ)⁻¹ +
        2 * (Q.choose 2 : ℝ) * ((Fintype.card G : ℝ)⁻¹) ^ 2 := by
  have h := Game.advantage_le_of_apply_le (by finiteness)
    (feistel4StrongRandomRoundsGame_apply_le hQ true)
    (idealStrongGame_apply_le_feistel4StrongRandomRoundsGame hQ true)
  ennreal_to_real at h
  rw [Fintype.card_prod, Nat.cast_mul, mul_inv, ← sq] at h
  exact h

/-- Concrete instantiation of the 4-round strong Luby–Rackoff theorem on `BitString n`
(block size `2n`): the information-theoretic chosen-ciphertext collision error is at most
`2 * Q.choose 2 / 2 ^ n + 2 * Q.choose 2 / (2 ^ n) ^ 2`. -/
theorem advantage_feistel4StrongRandomRoundsGame_bitString_le (n : ℕ)
    {program :
      OracleComp (fun _ : Bool × (BitString n × BitString n) => BitString n × BitString n) Bool}
    {Q : ℕ} (hQ : OracleComp.IsQueryBounded program Q) :
    (Game.advantage (feistel4StrongRandomRoundsGame program)
      (idealStrongGame program) : ℝ) ≤
      2 * (Q.choose 2 : ℝ) * ((2 : ℝ) ^ n)⁻¹ +
        2 * (Q.choose 2 : ℝ) * (((2 : ℝ) ^ n)⁻¹) ^ 2 := by
  have h := advantage_feistel4StrongRandomRoundsGame_idealStrongGame_le hQ
  simpa only [Fintype.card_pi, Fintype.card_fin, Fintype.card_bool, Finset.prod_const,
    Finset.card_univ, Nat.cast_pow, Nat.cast_ofNat] using h

end Strong4AndCCAAttack

/-! ### Keyed ciphers from a pseudorandom function

The keyed ciphers use the finite PRF and PRP experiments of `Cslib.Crypto.PRF` and
`Cslib.Crypto.PRP`, whose adversaries have private coins. An adapter answers each block query of
the cipher by querying three (or four) PRF channels, one per round, and keeps no state. The
`j`-th hybrid reduction `PRF.multiKeyReduction F j` of the multi-key PRF hybrid then turns the
adapter into a single PRF adversary: it samples its own keys for the later rounds, forwards
round `j + 1` to its PRF challenger, and lazily samples the earlier rounds with a cache. This is
the hybrid argument of [BonehShoup2023], Exercise 4.26, which the proof of Theorem 4.9 uses for
the three round keys. -/

section Keyed3

variable {K G : Type} [AddGroup G]

/-- The three-round Luby–Rackoff cipher with three independent keys of a round function
`F : K → G → G`, one per round. -/
def feistel3Cipher (F : K → G → G) (keys : Fin 3 → K) : Equiv.Perm (G × G) :=
  feistel3 (F (keys 0)) (F (keys 1)) (F (keys 2))

/-- Answer one block query `(l, r)` of the three-round cipher through three PRF channels, channel
`i` providing round `i + 1`. -/
def feistel3ChannelQuery : G × G → ProbOracleComp (fun _ : Fin 3 × G => G) (G × G)
  | (l, r) => do
    let y₁ ← ProbOracleComp.query (spec := fun _ : Fin 3 × G => G) (0, r)
    let u := l + y₁
    let y₂ ← ProbOracleComp.query (spec := fun _ : Fin 3 × G => G) (1, u)
    let v := r + y₂
    let y₃ ← ProbOracleComp.query (spec := fun _ : Fin 3 × G => G) (2, v)
    return (v, u + y₃)

/-- Run a chosen-plaintext adversary of the three-round cipher against three PRF channels,
answering each block query with `feistel3ChannelQuery`. -/
def feistel3MultiKeyAdversary (A : PRF.Adversary (G × G) (G × G)) :
    PRF.MultiKeyAdversary 3 G G :=
  ProbOracleComp.simulate feistel3ChannelQuery A

/-- The adapter makes three channel queries per block query. -/
theorem isQueryBounded_feistel3MultiKeyAdversary {A : PRF.Adversary (G × G) (G × G)} {Q : ℕ}
    (hQ : A.IsQueryBounded Q) : (feistel3MultiKeyAdversary A).IsQueryBounded (3 * Q) := by
  have hquery (p : G × G) : (feistel3ChannelQuery p).IsQueryBounded 3 := by
    obtain ⟨l, r⟩ := p
    exact (ProbOracleComp.IsQueryBounded.query (spec := fun _ : Fin 3 × G => G) (0, r)).bind
      fun y₁ => (ProbOracleComp.IsQueryBounded.query (spec := fun _ : Fin 3 × G => G)
        (1, l + y₁)).bind fun y₂ => (ProbOracleComp.IsQueryBounded.query
          (spec := fun _ : Fin 3 × G => G) (2, r + y₂)).bind fun y₃ =>
            OracleComp.IsCostBounded.pure (r + y₂, (l + y₁) + y₃) 0
  rw [feistel3MultiKeyAdversary, mul_comm]
  exact ProbOracleComp.isCostBounded_simulate (cost := fun _ => 3) hquery
    (hQ.mul_of_le (c := 3) fun q => by rcases q with _ | _ <;> simp)

/-- The `j`-th hybrid PRF reduction for the three-round cipher: the multi-key reduction of the
adapter. It samples keys for rounds after `j + 1`, forwards round `j + 1` to its PRF challenger
and lazily samples the rounds before it. -/
noncomputable abbrev feistel3Reduction [Fintype K] [Nonempty K] [DecidableEq G] [Fintype G]
    (F : K → G → G) (j : ℕ) (A : PRF.Adversary (G × G) (G × G)) : PRF.Adversary G G :=
  PRF.multiKeyReduction F j (feistel3MultiKeyAdversary A)

/-- Each hybrid reduction makes at most three queries per query of the adversary. -/
theorem isQueryBounded_feistel3Reduction [Fintype K] [Nonempty K] [DecidableEq G] [Fintype G]
    (F : K → G → G) (j : ℕ) {A : PRF.Adversary (G × G) (G × G)} {Q : ℕ}
    (hQ : A.IsQueryBounded Q) : (feistel3Reduction F j A).IsQueryBounded (3 * Q) :=
  PRF.isQueryBounded_multiKeyReduction F j (isQueryBounded_feistel3MultiKeyAdversary hQ)

variable [Fintype K] [Nonempty K] [Fintype G] [DecidableEq G]

omit [Fintype K] [Nonempty K] [Fintype G] [DecidableEq G] in
/-- The adapter's channel queries compute the three-round network. -/
theorem run_feistel3ChannelQuery (f : Fin 3 → G → G) (p : G × G) :
    (feistel3ChannelQuery p).run (fun request => pure (f request.1 request.2)) =
      pure (feistel3 (f 0) (f 1) (f 2) p) := by
  obtain ⟨l, r⟩ := p
  simp [feistel3ChannelQuery, feistel3_apply]

omit [Fintype G] [DecidableEq G] in
/-- With keyed channels, the adapter plays the real chosen-plaintext experiment of the three-round
cipher. -/
theorem multiKeyRealExperiment_feistel3MultiKeyAdversary (F : K → G → G)
    (A : PRF.Adversary (G × G) (G × G)) :
    PRF.multiKeyRealExperiment F (feistel3MultiKeyAdversary A) =
      PRP.realExperiment (feistel3Cipher F) A := by
  simp only [PRF.multiKeyRealExperiment, feistel3MultiKeyAdversary, ProbOracleComp.run_simulate,
    PRP.realExperiment, PRF.realExperiment]
  rfl

/-- With random channels, the adapter runs the adversary against the three-round Feistel network
of three independent uniform random functions. -/
theorem eval_multiKeyIdealExperiment_feistel3MultiKeyAdversary
    (A : PRF.Adversary (G × G) (G × G)) :
    ProbComp.eval (PRF.multiKeyIdealExperiment (feistel3MultiKeyAdversary A)) =
      (PMF.uniformOfFintype (Fin 3 → G → G)).bind fun tables =>
        OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
          (fun p => PMF.pure (feistel3 (tables 0) (tables 1) (tables 2) p))) A := by
  simp only [PRF.multiKeyIdealExperiment, feistel3MultiKeyAdversary, ProbOracleComp.run_simulate,
    run_feistel3ChannelQuery, ProbComp.eval_bind, ProbComp.eval_uniform, ProbOracleComp.eval_run,
    ProbComp.eval_pure]

/-- **Three random rounds against a random function**, for adversaries with private coins
([BonehShoup2023], proof of Theorem 4.9): with independent uniform random round functions, a
`Q`-query adversary distinguishes the three-round Feistel network from a uniform function on
`G × G` with advantage at most `2 * Q.choose 2 / |G|`. -/
theorem advantage_feistel3RandomRounds_prfIdealExperiment_le
    {A : PRF.Adversary (G × G) (G × G)} {Q : ℕ} (hQ : A.IsQueryBounded Q) :
    (Game.advantage (ProbComp.eval (PRF.multiKeyIdealExperiment (feistel3MultiKeyAdversary A)))
      (ProbComp.eval (PRF.idealExperiment A)) : ℝ) ≤
      2 * (Q.choose 2 : ℝ) * (Fintype.card G : ℝ)⁻¹ := by
  rw [eval_multiKeyIdealExperiment_feistel3MultiKeyAdversary, PRF.eval_idealExperiment,
    ProbOracleComp.table_bind_interpret_eq_coinLaw_bind (PMF.uniformOfFintype (Fin 3 → G → G))
      (fun tables p => feistel3 (tables 0) (tables 1) (tables 2) p) A,
    ProbOracleComp.table_bind_interpret_eq_coinLaw_bind (PMF.uniformOfFintype (G × G → G × G))
      (fun f p => f p) A]
  refine Game.advantage_bind_le _ _ _ fun ω => ?_
  rw [PMF.bind_uniformOfFintype_fin_three (fun f₁ f₂ f₃ => OracleComp.interpret
    (fun p => PMF.pure (feistel3 f₁ f₂ f₃ p)) (ProbOracleComp.fixCoins A ω))]
  simpa only [feistel3RandomRoundsGame, feistel3FixedGame, randomFunctionGame,
    Probability.PMF.monad_bind_eq_bind] using
    advantage_feistel3RandomRoundsGame_randomFunctionGame_le
      (ProbOracleComp.isQueryBounded_fixCoins hQ ω)

/-- **Three random rounds against a random permutation**, for adversaries with private coins
([BonehShoup2023], proof of Theorem 4.9): with independent uniform random round functions, a
`Q`-query adversary distinguishes the three-round Feistel network from a uniform permutation of
`G × G` with advantage at most `2 * Q.choose 2 / |G| + Q.choose 2 / |G| ^ 2`. -/
theorem advantage_feistel3RandomRounds_prpIdealExperiment_le
    {A : PRF.Adversary (G × G) (G × G)} {Q : ℕ} (hQ : A.IsQueryBounded Q) :
    (Game.advantage (ProbComp.eval (PRF.multiKeyIdealExperiment (feistel3MultiKeyAdversary A)))
      (ProbComp.eval (PRP.idealExperiment A)) : ℝ) ≤
      2 * (Q.choose 2 : ℝ) * (Fintype.card G : ℝ)⁻¹ +
        (Q.choose 2 : ℝ) * ((Fintype.card G : ℝ)⁻¹) ^ 2 := by
  rw [eval_multiKeyIdealExperiment_feistel3MultiKeyAdversary, PRP.eval_idealExperiment,
    ProbOracleComp.table_bind_interpret_eq_coinLaw_bind (PMF.uniformOfFintype (Fin 3 → G → G))
      (fun tables p => feistel3 (tables 0) (tables 1) (tables 2) p) A,
    ProbOracleComp.table_bind_interpret_eq_coinLaw_bind
      (PMF.uniformOfFintype (Equiv.Perm (G × G))) (fun π p => π p) A]
  refine Game.advantage_bind_le _ _ _ fun ω => ?_
  rw [PMF.bind_uniformOfFintype_fin_three (fun f₁ f₂ f₃ => OracleComp.interpret
    (fun p => PMF.pure (feistel3 f₁ f₂ f₃ p)) (ProbOracleComp.fixCoins A ω))]
  simpa only [feistel3RandomRoundsGame, feistel3FixedGame, idealPermGame,
    Probability.PMF.monad_bind_eq_bind] using advantage_feistel3RandomRoundsGame_idealPermGame_le
      (ProbOracleComp.isQueryBounded_fixCoins hQ ω)

/-- The keyed half of the three-round theorem: the chosen-plaintext real experiment of the
three-round cipher is within the sum of the three hybrid reductions' PRF advantages of the
adapter's random-rounds experiment. -/
private theorem advantage_feistel3Cipher_randomRounds_le (F : K → G → G)
    (A : PRF.Adversary (G × G) (G × G)) :
    (Game.advantage (ProbComp.eval (PRP.realExperiment (feistel3Cipher F) A))
      (ProbComp.eval (PRF.multiKeyIdealExperiment (feistel3MultiKeyAdversary A))) : ℝ) ≤
      ∑ j ∈ Finset.range 3, (PRF.advantage F (feistel3Reduction F j A) : ℝ) := by
  rw [← multiKeyRealExperiment_feistel3MultiKeyAdversary, ← NNReal.coe_sum, NNReal.coe_le_coe]
  exact PRF.multiKeyAdvantage_le_sum F (feistel3MultiKeyAdversary A)

/-- **The Luby–Rackoff theorem, concrete PRF form** ([BonehShoup2023], Theorem 4.9;
[LubyRackoff1988]): against a `Q`-query adaptive chosen-plaintext adversary `A` with private
coins, the PRF advantage of the three-round cipher built from three independent uniform keys of
`F` is at most the PRF advantages of the three explicit hybrid reductions
`feistel3Reduction F j A` plus `2 * Q.choose 2 / |G|`. This is a concrete bound for one finite
instance in the standard model; running time is not modeled. The asymptotic theorem for
oracle-PPT adversaries is `Cslib.Crypto.PseudorandomFunction.prp_lubyRackoffCipher`. -/
theorem prfAdvantage_feistel3Cipher_le (F : K → G → G) {A : PRF.Adversary (G × G) (G × G)}
    {Q : ℕ} (hQ : A.IsQueryBounded Q) :
    (PRF.advantage (fun keys => ⇑(feistel3Cipher F keys)) A : ℝ) ≤
      ∑ j ∈ Finset.range 3, (PRF.advantage F (feistel3Reduction F j A) : ℝ) +
        2 * (Q.choose 2 : ℝ) * (Fintype.card G : ℝ)⁻¹ :=
  Game.coe_advantage_triangle_add _ _ _ (advantage_feistel3Cipher_randomRounds_le F A)
    (advantage_feistel3RandomRounds_prfIdealExperiment_le hQ)

/-- **The Luby–Rackoff theorem, concrete form** ([BonehShoup2023], Theorem 4.9; [LubyRackoff1988]):
against a `Q`-query adaptive chosen-plaintext adversary `A` with private coins, the PRP advantage
of the three-round cipher built from three independent uniform keys of `F` is at most the PRF
advantages of the three explicit hybrid reductions `feistel3Reduction F j A` plus
`2 * Q.choose 2 / |G| + Q.choose 2 / |G| ^ 2`. Each reduction makes at most `3 * Q` queries
(`isQueryBounded_feistel3Reduction`). The PRF part deviates from Theorem 4.9, which has `3`
times the advantage of one reduction that picks the hybrid at random: by the triangle inequality
the sum of the three hybrid advantages is at least that quantity, so this bound follows from the
book's form and may be weaker.
This is a concrete bound for one finite instance in the standard model; running time is not
modeled. The asymptotic theorem for oracle-PPT adversaries is
`Cslib.Crypto.PseudorandomFunction.prp_lubyRackoffCipher`. -/
theorem prpAdvantage_feistel3Cipher_le (F : K → G → G) {A : PRF.Adversary (G × G) (G × G)}
    {Q : ℕ} (hQ : A.IsQueryBounded Q) :
    (PRP.advantage (feistel3Cipher F) A : ℝ) ≤
      ∑ j ∈ Finset.range 3, (PRF.advantage F (feistel3Reduction F j A) : ℝ) +
        (2 * (Q.choose 2 : ℝ) * (Fintype.card G : ℝ)⁻¹ +
          (Q.choose 2 : ℝ) * ((Fintype.card G : ℝ)⁻¹) ^ 2) :=
  Game.coe_advantage_triangle_add _ _ _ (advantage_feistel3Cipher_randomRounds_le F A)
    (advantage_feistel3RandomRounds_prpIdealExperiment_le hQ)

end Keyed3

section Keyed4

open RandomPermutation (PermQuery PermOracleSpec evalPerm)

variable {K G : Type} [AddGroup G]

/-- The four-round Luby–Rackoff cipher with four independent keys of a round function
`F : K → G → G`, one per round. -/
def feistel4Cipher (F : K → G → G) (keys : Fin 4 → K) : Equiv.Perm (G × G) :=
  feistel4 (F (keys 0)) (F (keys 1)) (F (keys 2)) (F (keys 3))

/-- Answer one forward or inverse block query of the four-round cipher through four PRF channels,
channel `i` providing round `i + 1`. Inversion evaluates the round functions forwards, in reverse
order. -/
def feistel4StrongChannelQuery :
    PermQuery (G × G) → ProbOracleComp (fun _ : Fin 4 × G => G) (G × G)
  | .forward (l, r) => do
    let y₁ ← ProbOracleComp.query (spec := fun _ : Fin 4 × G => G) (0, r)
    let u := l + y₁
    let y₂ ← ProbOracleComp.query (spec := fun _ : Fin 4 × G => G) (1, u)
    let v := r + y₂
    let y₃ ← ProbOracleComp.query (spec := fun _ : Fin 4 × G => G) (2, v)
    let w := u + y₃
    let y₄ ← ProbOracleComp.query (spec := fun _ : Fin 4 × G => G) (3, w)
    return (w, v + y₄)
  | .inverse (w, z) => do
    let y₄ ← ProbOracleComp.query (spec := fun _ : Fin 4 × G => G) (3, w)
    let v := z - y₄
    let y₃ ← ProbOracleComp.query (spec := fun _ : Fin 4 × G => G) (2, v)
    let u := w - y₃
    let y₂ ← ProbOracleComp.query (spec := fun _ : Fin 4 × G => G) (1, u)
    let r := v - y₂
    let y₁ ← ProbOracleComp.query (spec := fun _ : Fin 4 × G => G) (0, r)
    return (u - y₁, r)

/-- Run a chosen-ciphertext adversary of the four-round cipher against four PRF channels,
answering each forward or inverse block query with `feistel4StrongChannelQuery`. -/
def feistel4StrongMultiKeyAdversary (A : PRP.StrongAdversary (G × G)) :
    PRF.MultiKeyAdversary 4 G G :=
  ProbOracleComp.simulate feistel4StrongChannelQuery A

/-- The adapter makes four channel queries per block query. -/
theorem isQueryBounded_feistel4StrongMultiKeyAdversary {A : PRP.StrongAdversary (G × G)} {Q : ℕ}
    (hQ : A.IsQueryBounded Q) : (feistel4StrongMultiKeyAdversary A).IsQueryBounded (4 * Q) := by
  have hq (i : Fin 4) (x : G) :=
    ProbOracleComp.IsQueryBounded.query (spec := fun _ : Fin 4 × G => G) (i, x)
  have hquery (q : PermQuery (G × G)) : (feistel4StrongChannelQuery q).IsQueryBounded 4 := by
    rcases q with ⟨l, r⟩ | ⟨w, z⟩
    · exact (hq 0 r).bind fun y₁ => (hq 1 (l + y₁)).bind fun y₂ =>
        (hq 2 (r + y₂)).bind fun y₃ => (hq 3 ((l + y₁) + y₃)).bind fun y₄ =>
          OracleComp.IsCostBounded.pure ((l + y₁) + y₃, (r + y₂) + y₄) 0
    · exact (hq 3 w).bind fun y₄ => (hq 2 (z - y₄)).bind fun y₃ =>
        (hq 1 (w - y₃)).bind fun y₂ => (hq 0 ((z - y₄) - y₂)).bind fun y₁ =>
          OracleComp.IsCostBounded.pure ((w - y₃) - y₁, (z - y₄) - y₂) 0
  rw [feistel4StrongMultiKeyAdversary, mul_comm]
  exact ProbOracleComp.isCostBounded_simulate (cost := fun _ => 4) hquery
    (hQ.mul_of_le (c := 4) fun q => by rcases q with _ | _ <;> simp)

/-- The `j`-th hybrid PRF reduction for the four-round cipher: the multi-key reduction of the
bidirectional adapter. -/
noncomputable abbrev feistel4StrongReduction [Fintype K] [Nonempty K] [DecidableEq G] [Fintype G]
    (F : K → G → G) (j : ℕ) (A : PRP.StrongAdversary (G × G)) : PRF.Adversary G G :=
  PRF.multiKeyReduction F j (feistel4StrongMultiKeyAdversary A)

/-- Each hybrid reduction makes at most four queries per query of the adversary. -/
theorem isQueryBounded_feistel4StrongReduction [Fintype K] [Nonempty K] [DecidableEq G]
    [Fintype G] (F : K → G → G) (j : ℕ) {A : PRP.StrongAdversary (G × G)} {Q : ℕ}
    (hQ : A.IsQueryBounded Q) : (feistel4StrongReduction F j A).IsQueryBounded (4 * Q) :=
  PRF.isQueryBounded_multiKeyReduction F j (isQueryBounded_feistel4StrongMultiKeyAdversary hQ)

variable [Fintype K] [Nonempty K] [Fintype G] [DecidableEq G]

omit [Fintype K] [Nonempty K] [Fintype G] [DecidableEq G] in
/-- The adapter's channel queries compute the four-round network in both directions. -/
theorem run_feistel4StrongChannelQuery (f : Fin 4 → G → G) (q : PermQuery (G × G)) :
    (feistel4StrongChannelQuery q).run (fun request => pure (f request.1 request.2)) =
      pure (evalPerm (feistel4 (f 0) (f 1) (f 2) (f 3)) q) := by
  rcases q with ⟨l, r⟩ | ⟨w, z⟩
  · simp [feistel4StrongChannelQuery, feistel4_apply, feistel3_apply, feistelRound]
  · simp [feistel4StrongChannelQuery, feistel4_symm_apply, feistel3_symm_apply, feistelInvRound]

omit [Fintype G] [DecidableEq G] in
/-- With keyed channels, the adapter plays the real chosen-ciphertext experiment of the four-round
cipher. -/
theorem multiKeyRealExperiment_feistel4StrongMultiKeyAdversary (F : K → G → G)
    (A : PRP.StrongAdversary (G × G)) :
    PRF.multiKeyRealExperiment F (feistel4StrongMultiKeyAdversary A) =
      PRP.strongRealExperiment (feistel4Cipher F) A := by
  simp only [PRF.multiKeyRealExperiment, feistel4StrongMultiKeyAdversary,
    ProbOracleComp.run_simulate, PRP.strongRealExperiment]
  congr 1 with keys : 1
  congr 1
  funext q
  exact run_feistel4StrongChannelQuery (fun i => F (keys i)) q

/-- With random channels, the adapter runs the adversary against the four-round Feistel network of
four independent uniform random functions, in both directions. -/
theorem eval_multiKeyIdealExperiment_feistel4StrongMultiKeyAdversary
    (A : PRP.StrongAdversary (G × G)) :
    ProbComp.eval (PRF.multiKeyIdealExperiment (feistel4StrongMultiKeyAdversary A)) =
      (PMF.uniformOfFintype (Fin 4 → G → G)).bind fun tables =>
        OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
          (fun q => PMF.pure
            (evalPerm (feistel4 (tables 0) (tables 1) (tables 2) (tables 3)) q))) A := by
  simp only [PRF.multiKeyIdealExperiment, feistel4StrongMultiKeyAdversary,
    ProbOracleComp.run_simulate, run_feistel4StrongChannelQuery, ProbComp.eval_bind,
    ProbComp.eval_uniform, ProbOracleComp.eval_run, ProbComp.eval_pure]

/-- Tag each query of a coin-free bidirectional program with a Boolean, as the random-rounds game
`feistel4StrongRandomRoundsGame` expects: `false` for forward and `true` for inverse. -/
private def tagQueries (program : OracleComp (PermOracleSpec (G × G)) Bool) :
    OracleComp (fun _ : Bool × (G × G) => G × G) Bool :=
  OracleComp.interpret (fun
    | .forward x => OracleComp.query (spec := fun _ : Bool × (G × G) => G × G) (false, x)
    | .inverse y => OracleComp.query (spec := fun _ : Bool × (G × G) => G × G) (true, y))
    program

omit [AddGroup G] [Fintype G] [DecidableEq G] in
private theorem interpret_feistelStrongOracle_tagQueries (π : Equiv.Perm (G × G))
    (program : OracleComp (PermOracleSpec (G × G)) Bool) :
    OracleComp.interpret (feistelStrongOracle π) (tagQueries program) =
      OracleComp.interpret (fun q => PMF.pure (evalPerm π q)) program := by
  rw [tagQueries, OracleComp.interpret_interpret]
  congr 1
  funext q
  cases q <;> simp [feistelStrongOracle]

omit [AddGroup G] [Fintype G] [DecidableEq G] in
private theorem isQueryBounded_tagQueries {program : OracleComp (PermOracleSpec (G × G)) Bool}
    {Q : ℕ} (hQ : OracleComp.IsQueryBounded program Q) :
    OracleComp.IsQueryBounded (tagQueries program) Q :=
  hQ.interpret fun q => by cases q <;> exact OracleComp.IsCostBounded.query _

/-- **Four random rounds against a random permutation, in both directions**, for adversaries with
private coins ([LubyRackoff1988]): with independent uniform random round functions, a `Q`-query
chosen-ciphertext adversary distinguishes the four-round Feistel network from a uniform
permutation of `G × G` with advantage at most `2 * Q.choose 2 / |G| + 2 * Q.choose 2 / |G| ^ 2`.
The constant comes from this proof. -/
theorem advantage_feistel4StrongRandomRounds_strongIdealExperiment_le
    {A : PRP.StrongAdversary (G × G)} {Q : ℕ} (hQ : A.IsQueryBounded Q) :
    (Game.advantage
      (ProbComp.eval (PRF.multiKeyIdealExperiment (feistel4StrongMultiKeyAdversary A)))
      (ProbComp.eval (PRP.strongIdealExperiment A)) : ℝ) ≤
      2 * (Q.choose 2 : ℝ) * (Fintype.card G : ℝ)⁻¹ +
        2 * (Q.choose 2 : ℝ) * ((Fintype.card G : ℝ)⁻¹) ^ 2 := by
  rw [eval_multiKeyIdealExperiment_feistel4StrongMultiKeyAdversary,
    PRP.strongIdealExperiment, ProbComp.eval_bind, ProbComp.eval_uniform]
  simp only [ProbOracleComp.eval_run, ProbComp.eval_pure]
  rw [ProbOracleComp.table_bind_interpret_eq_coinLaw_bind (PMF.uniformOfFintype (Fin 4 → G → G))
      (fun tables q => evalPerm (feistel4 (tables 0) (tables 1) (tables 2) (tables 3)) q) A,
    ProbOracleComp.table_bind_interpret_eq_coinLaw_bind
      (PMF.uniformOfFintype (Equiv.Perm (G × G))) (fun π q => evalPerm π q) A]
  refine Game.advantage_bind_le _ _ _ fun ω => ?_
  have h := advantage_feistel4StrongRandomRoundsGame_idealStrongGame_le
    (isQueryBounded_tagQueries (ProbOracleComp.isQueryBounded_fixCoins hQ ω))
  rw [PMF.bind_uniformOfFintype_fin_four (fun f₁ f₂ f₃ f₄ => OracleComp.interpret
    (fun q => PMF.pure (evalPerm (feistel4 f₁ f₂ f₃ f₄) q)) (ProbOracleComp.fixCoins A ω))]
  simpa only [feistel4StrongRandomRoundsGame, idealStrongGame,
    interpret_feistelStrongOracle_tagQueries, Probability.PMF.monad_bind_eq_bind] using h

/-- **Four-round strong Luby–Rackoff theorem, concrete form** ([LubyRackoff1988]; strongly secure
block ciphers as in [BonehShoup2023], Section 4.1.3): against a `Q`-query adaptive
chosen-ciphertext adversary `A` with private coins, the strong PRP advantage of the four-round
cipher built from four independent uniform keys of `F` is at most the PRF advantages of the four
explicit hybrid reductions `feistel4StrongReduction F j A` plus
`2 * Q.choose 2 / |G| + 2 * Q.choose 2 / |G| ^ 2`. Each reduction makes at most `4 * Q` queries
(`isQueryBounded_feistel4StrongReduction`). The constant comes from this proof. This is a
concrete bound for one finite instance in the standard model; running time is not modeled. The
asymptotic theorem for oracle-PPT adversaries is
`Cslib.Crypto.PseudorandomFunction.strongPRP_lubyRackoff4Cipher`. -/
theorem strongAdvantage_feistel4Cipher_le (F : K → G → G) {A : PRP.StrongAdversary (G × G)}
    {Q : ℕ} (hQ : A.IsQueryBounded Q) :
    (PRP.strongAdvantage (feistel4Cipher F) A : ℝ) ≤
      ∑ j ∈ Finset.range 4, (PRF.advantage F (feistel4StrongReduction F j A) : ℝ) +
        (2 * (Q.choose 2 : ℝ) * (Fintype.card G : ℝ)⁻¹ +
          2 * (Q.choose 2 : ℝ) * ((Fintype.card G : ℝ)⁻¹) ^ 2) := by
  refine Game.coe_advantage_triangle_add _ _ _ ?_
    (advantage_feistel4StrongRandomRounds_strongIdealExperiment_le hQ)
  rw [← multiKeyRealExperiment_feistel4StrongMultiKeyAdversary, ← NNReal.coe_sum,
    NNReal.coe_le_coe]
  exact PRF.multiKeyAdvantage_le_sum F (feistel4StrongMultiKeyAdversary A)

end Keyed4

end Cslib.Crypto.LubyRackoff
