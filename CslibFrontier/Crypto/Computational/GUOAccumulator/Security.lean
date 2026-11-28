/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.GUOAccumulator
public import CslibFrontier.Crypto.Computational.StrongRSA
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF.Bind

/-!
# The accumulator from a group of unknown order: security under strong RSA

The security of the accumulator of [BonehShoup2023], §10.9, p. 422, in `(ZMod N)ˣ` with a hash
`H` on words. An adversary breaks the accumulator when it outputs a commitment `c`, an element
`x`, a membership proof `a` and a non-membership proof `(b, γ)` such that both of Bob's checks
pass. The book derives `(b * a ^ γ) ^ H(x) = g` from the two checks, so that the root
`b * a ^ γ` with the exponent `H(x)` wins the strong RSA game, and concludes that the accumulator
is secure if the strong RSA assumption holds for `GGen`.

## Main definitions

* `Cslib.Crypto.GUOForgery`, `Cslib.Crypto.encGUOForgery`: an adversary's output
  `(c, x, a, (b, γ))` and its encoding.
* `Cslib.Crypto.GUOForger`, `Cslib.Crypto.GUOForger.IsPPT`: adversaries of the security game and
  their efficiency on encodings.
* `Cslib.Crypto.GUOForgery.isValid`: both of Bob's checks for one element.
* `Cslib.Crypto.guoAccumulatorGame`: the security game, won by a valid forgery.
* `Cslib.Crypto.guoToStrongRSA`: the reduction, which outputs `(b * a ^ γ mod N, H x)`.

## Main results

* `Cslib.Crypto.StrongRSA.negligible_guoAccumulatorGame`: **the security of the accumulator**
  (p. 422). If `StrongRSA setup` holds and `H` is computable in polynomial time with no value
  `1`, every PPT adversary wins `guoAccumulatorGame setup H` with negligible probability.
* `Cslib.Crypto.succProbability_guoAccumulatorGame_le`: if `H` never takes the value `1`, the
  success probability of every adversary `A` is at most that of `guoToStrongRSA H A` in the strong
  RSA game.
* `Cslib.Crypto.isPPT_guoToStrongRSA`: the reduction is PPT when `A` is and `H` is computable in
  polynomial time.

## Implementation notes

The statements differ from the book's as follows.

* The group is `(ZMod N)ˣ` for public parameters `(N, g)` from any law `setup`, the deviation of
  `StrongRSA`; `rsaGUOSetup` is the book's `GGen` from RSA keys (p. 421). Class groups (p. 423)
  are not covered.
* The elements are words (`List Bool`) and `H` is any function to `ℕ` that is computable in
  polynomial time and never takes the value `1`. The book's `H` takes values in the first `L`
  primes (p. 421); the reduction needs only `H x ≠ 1`, because the strong RSA game rejects the
  exponent `1`. The book's `H` is collision resistant; the security proof does not use this.
* The group elements `c`, `a` and `b` are natural numbers. Bob's non-membership check includes the
  check that `c` is a unit, the book's `c ∈ G` (see `GUOAccumulator.lean`).
* The book calls a *correct* accumulator secure when no efficient adversary breaks it. The
  statement here is the negligibility of the forgery game alone; correctness is in
  `GUOAccumulator.lean`, where Alice's proofs verify (`guoVerifyNonMem_guoCommit` and the
  membership lemmas).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  §10.9, p. 422.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- An adversary's output in the security game of the accumulator ([BonehShoup2023], §10.9,
p. 422): the book's 4-tuple `(c, x, π_x, π_¬x)` with `π_x = a` and `π_¬x = (b, γ)`. -/
structure GUOForgery where
  /-- The commitment `c`. -/
  commitment : ℕ
  /-- The element `x`, a word. -/
  element : List Bool
  /-- The membership proof `a`. -/
  member : ℕ
  /-- The group element `b` of the non-membership proof. -/
  nonMember : ℕ
  /-- The integer `γ` of the non-membership proof. -/
  coeff : ℤ

/-- The encoding of a forgery: `c`, `a` and `b` in binary, `x` as its bits and `γ` on
`encIntBin`, in the order of the fields (`encGUOForgery_apply`). -/
enc_structure encGUOForgery : GUOForgery where
  commitment : encNat, element : encBits, member : encNat, nonMember : encNat, coeff : encIntBin

/-- An adversary of the accumulator's security game: given the security parameter and the public
parameters `(N, g)`, it outputs a forgery. `GUOForger.IsPPT` states its efficiency on
encodings. -/
abbrev GUOForger : Type := ℕ → GUOParams → ProbComp GUOForgery

/-- An adversary of the accumulator is PPT when one uniform strict PPT machine reads the unary
security parameter followed by `encGUOParams`, and writes its forgery on `encGUOForgery`. -/
@[expose] def GUOForger.IsPPT (A : GUOForger) : Prop :=
  IsPPTOn (encPair encUnary encGUOParams) encGUOForgery fun p => A p.1 p.2

/-- A forgery is valid for the hash `H` and the public parameters `(N, g)` when its membership
proof `a` passes Bob's membership check `a ^ H x = c` and its non-membership proof `(b, γ)` passes
his non-membership check, including the check that `c` is a unit ([BonehShoup2023], §10.9,
pp. 421–422). -/
@[expose] def GUOForgery.isValid (H : List Bool → ℕ) (p : GUOParams) (f : GUOForgery) : Bool :=
  guoVerifySubset p.modulus f.commitment (H f.element) f.member &&
    guoVerifyNonMem p.modulus p.base f.commitment (H f.element) f.nonMember f.coeff

/-- The security game of the accumulator ([BonehShoup2023], §10.9, p. 422): draw `p ← setup n`,
run the adversary on `(n, p)`, and accept its forgery when it is valid for `H` and `p`. -/
@[expose] noncomputable def guoAccumulatorGame (setup : ℕ → PMF GUOParams) (H : List Bool → ℕ)
    (A : GUOForger) (n : ℕ) : Game :=
  Game.withSetup (setup n) fun p => do
    let f ← A n p
    return f.isValid H p

/-- The reduction of [BonehShoup2023], §10.9, p. 422, from the accumulator to strong RSA: run the
adversary and output the root `b * a ^ γ mod N` (`guoForgeryRoot`) with the exponent `H x`. The
book does not name it; `guoToStrongRSA` is this library's name. -/
def guoToStrongRSA (H : List Bool → ℕ) (A : GUOForger) : StrongRSAAdversary := fun n p =>
  (fun f => (guoForgeryRoot p.modulus f.member f.nonMember f.coeff, H f.element)) <$> A n p

/-- The reduction is PPT whenever the adversary is and `H` is computable in polynomial time from
the bits of the element to a binary number. -/
theorem isPPT_guoToStrongRSA {H : List Bool → ℕ} (hH : ComputableInPolyTime H encBits encNat)
    {A : GUOForger} (hA : A.IsPPT) : (guoToStrongRSA H A).IsPPT := by
  have hout : ComputableInPolyTime
      (fun q : (ℕ × GUOParams) × GUOForgery =>
        (guoForgeryRoot q.1.2.modulus q.2.member q.2.nonMember q.2.coeff, H q.2.element))
      (encPair (encPair encUnary encGUOParams) encGUOForgery) (encPair encNat encNat) :=
    (computableInPolyTime_guoForgeryRoot (by fun_prop) (by fun_prop) (by fun_prop)
      (by fun_prop)).prod (hH.comp (by fun_prop))
  exact IsPPTOn.map_with
    (f := fun p f => (guoForgeryRoot p.2.modulus f.member f.nonMember f.coeff, H f.element)) hA hout

/-- **The reduction of the accumulator's security to strong RSA** ([BonehShoup2023], §10.9,
p. 422), as a bound for every adversary: if `H` never takes the value `1`, the probability that
`A` wins `guoAccumulatorGame setup H` is at most the probability that `guoToStrongRSA H A` wins the
strong RSA game. A valid forgery gives an `H x`-th root of `g` (`powMod_guoForgeryRoot`). -/
theorem succProbability_guoAccumulatorGame_le (setup : ℕ → PMF GUOParams) {H : List Bool → ℕ}
    (hH : ∀ x, H x ≠ 1) (A : GUOForger) (n : ℕ) :
    Game.succProbability (guoAccumulatorGame setup H A n) ≤
      Game.succProbability (strongRSAGame setup (guoToStrongRSA H A) n) := by
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
  dsimp only [guoAccumulatorGame, strongRSAGame, Game.withSetup, guoToStrongRSA]
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_map, PMF.bind_map]
  refine PMF.bind_apply_mono_on_support (setup n) true fun p _ => ?_
  refine PMF.bind_apply_mono_on_support (ProbComp.eval (A n p)) true fun f _ => ?_
  by_cases hvalid : f.isValid H p = true
  · have hv := hvalid
    simp only [GUOForgery.isValid, Bool.and_eq_true] at hv
    simp [hvalid, isStrongRSASolution, powMod_guoForgeryRoot hv.1 hv.2, hH]
  · simp [Bool.eq_false_iff.mpr hvalid]

/-- **The accumulator is secure under strong RSA** ([BonehShoup2023], §10.9, p. 422). If the
strong RSA assumption holds for `setup` and the hash `H` on words is computable in polynomial time
and never takes the value `1`, then every PPT adversary wins `guoAccumulatorGame setup H` with
negligible probability. The book's `H` takes prime values, and its group comes from an efficient
`GGen`; here `setup` is any law on `GUOParams`, as in `StrongRSA`. -/
theorem StrongRSA.negligible_guoAccumulatorGame {setup : ℕ → PMF GUOParams}
    (h : StrongRSA setup) {H : List Bool → ℕ} (hH : ∀ x, H x ≠ 1)
    (hHc : ComputableInPolyTime H encBits encNat) {A : GUOForger} (hA : A.IsPPT) :
    Negligible fun n => Game.succProbability (guoAccumulatorGame setup H A n) :=
  negligible_of_le (h _ (isPPT_guoToStrongRSA hHc hA))
    fun n => succProbability_guoAccumulatorGame_le setup hH A n

end Cslib.Crypto
