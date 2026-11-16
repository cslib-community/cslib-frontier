/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MerkleDamgard
public import CslibFrontier.Crypto.Computational.MerkleDamgard.LengthPadding
import CslibFrontier.Foundations.Data.Nat.Subexponential
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PPT

/-!
# Length-strengthened Merkle–Damgård hash and Theorem 8.3

For a compression function `h`, `lengthStrengthenedMD h k msg` hashes `msg` by iterating
`merkleDamgardChain` over the padded blocks `mdLengthBlocks k.length msg` starting from the
all-zero `k.length`-bit initialization vector ([BonehShoup2023], Section 8.4, pp. 295–298).
Theorem 8.3 ([BonehShoup2023], p. 297; proof ending on p. 298) states that `H_MD` is collision
resistant when `h` is, with `CRadv[A, H_MD] = CRadv[B, h]` for a wrapper `B` around `A`.
`lengthStrengthenedWrapper` is that `B`: it succeeds with `adversary`'s exact probability whenever
every valid message satisfies `mdLengthBlockCount n m < 2 ^ (n / 2)`, the condition under which
the padding is suffix-free. Since every uniform strict PPT adversary only produces messages of
polynomially bounded length, every `CompressionFamily h` yields unrestricted
`CollisionResistant (lengthStrengthenedMD h)` and `HashFamily (lengthStrengthenedMD h)`.

## Main definitions

* `Cslib.Crypto.lengthStrengthenedMD`: length-strengthened Merkle–Damgård hash built from
  `merkleDamgardChain`, the all-zero IV, and `mdLengthBlocks`.
* `Cslib.Crypto.lengthStrengthenedWrapper`: explicit Theorem 8.3 reduction adversary mapping valid
  `lengthStrengthenedMD` collisions via `extractChainCollision` to `2n`-bit collisions for `h`,
  and returning `([], [])` otherwise.

## Main results

* `Cslib.Crypto.length_lengthStrengthenedMD`: length preservation of `lengthStrengthenedMD h`.
* `Cslib.Crypto.computableInPolyTime_lengthStrengthenedMD`: deterministic polynomial-time
  certificate for `lengthStrengthenedMD h`.
* `Cslib.Crypto.isPPT_lengthStrengthenedWrapper`: uniform strict PPT certificate for
  `lengthStrengthenedWrapper`.
* `Cslib.Crypto.succProbability_collisionGame_lengthStrengthenedMD_eq`: concrete advantage
  equality for `lengthStrengthenedWrapper` whenever every valid message satisfies
  `mdLengthBlockCount n m < 2 ^ (n / 2)`.
* `Cslib.Crypto.CompressionFamily.collisionResistant_lengthStrengthenedMD`: unrestricted
  collision resistance of `lengthStrengthenedMD h` for any `CompressionFamily h`.
* `Cslib.Crypto.CompressionFamily.hashFamily_lengthStrengthenedMD`: `HashFamily` instance for
  `lengthStrengthenedMD h` from any `CompressionFamily h`.

## Differences from Boneh–Shoup §8.4

* **(a) Parameterization (`ℓ = n`, `IV = 0^n`, single `2n`-bit compression input):**
  [BonehShoup2023], Section 8.4 (pp. 295–296) separates chaining length `n` from block length `ℓ`,
  uses an arbitrary fixed `IV ∈ {0, 1}^n`, and writes two-argument compression `h(tᵢ₋₁, mᵢ)`; here
  `ℓ = n = k.length`, `IV` is fixed to `List.replicate k.length false`, and `h k (t ‖ m)` takes a
  single `2n`-bit `List Bool` matching `CompressionFamily`.
* **(b) Domain bound as a predicate rather than `{0, 1}^{≤ L}`:**
  See `CslibFrontier/Crypto/Computational/MerkleDamgard/LengthPadding.lean` for the padding
  differences (`ℓ = n`, `(n / 2)`-bit block-count field, counting padded blocks, and truncation when
  `mdLengthBlockCount n msg ≥ 2 ^ (n / 2)`). Where Fig. 8.5 (pp. 296–297) restricts the message
  type to a bounded domain `{0, 1}^{≤ L}`, `succProbability_collisionGame_lengthStrengthenedMD_eq`
  takes the explicit hypothesis `∀ m, valid n m = true → mdLengthBlockCount n m < 2 ^ (n / 2)`,
  while `CollisionResistant` and `HashFamily` recover suffix-freeness asymptotically because strict
  PPT adversaries output messages of polynomially bounded length.
* **(c) Keyed uniform setting:** the hash and compression function are keyed by a uniform
  `k ← {0, 1}^n` at each security parameter `n`, matching `CollisionResistant` and
  `CompressionFamily` rather than a fixed/implicit key with finite message spaces.
* **(d) Checked wrapper giving exact `=`:** the book's `B` runs `A` "to obtain two distinct
  messages" that collide (p. 297), giving `CRadv[A, H_MD] = CRadv[B, h]`, without specifying what
  `B` returns otherwise. Here `lengthStrengthenedWrapper` checks
  `isCollision (lengthStrengthenedMD h) valid` and returns `([], [])` on failure, so it wins on
  the exact same event as `adversary` (whereas `succProbability_collisionGame_le_of_extract` gives
  `≤` for an unchecked extractor). Efficiency uses `ComputableInPolyTime` and strict uniform
  `IsPPT`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 8.4 (pp. 295–298).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

/-- Length-strengthened Merkle–Damgård hash: iterates `merkleDamgardChain` over the padded blocks
`mdLengthBlocks k.length msg` starting from the all-zero `k.length`-bit IV.

This instantiates [BonehShoup2023], Section 8.4 (pp. 295–297) with block length `k.length`, fixed
`IV = List.replicate k.length false`, and the `(k.length / 2)`-bit block-count encoding from
`mdLengthBlocks`. -/
@[expose] def lengthStrengthenedMD (h : List Bool → List Bool → List Bool)
    (k msg : List Bool) : List Bool :=
  merkleDamgardChain h k (List.replicate k.length false) (mdLengthBlocks k.length msg)

/-- When `h k` maps `2 * k.length`-bit inputs to `k.length`-bit digests,
`lengthStrengthenedMD h k msg` outputs a `k.length`-bit digest. -/
theorem length_lengthStrengthenedMD {h : List Bool → List Bool → List Bool}
    {k msg : List Bool}
    (hlen : ∀ x, x.length = 2 * k.length → (h k x).length = k.length) :
    (lengthStrengthenedMD h k msg).length = k.length :=
  length_merkleDamgardChain hlen List.length_replicate
    (fun _ hb => length_of_mem_mdLengthBlocks hb)

/-- Deterministic polynomial-time evaluation of `lengthStrengthenedMD h` from deterministic
polynomial-time evaluation and length preservation of `h`. -/
@[program_certificate]
theorem computableInPolyTime_lengthStrengthenedMD {h : List Bool → List Bool → List Bool}
    (hh : ComputableInPolyTime (fun p : List Bool × List Bool => h p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, x.length = 2 * k.length → (h k x).length = k.length) :
    ComputableInPolyTime (fun p : List Bool × List Bool => lengthStrengthenedMD h p.1 p.2)
      (encPair encBits encBits) encBits :=
  computableInPolyTime_merkleDamgardChain mdLengthBlocks hh hlen
    computableInPolyTime_mdLengthBlocks fun _ _ _ hb => length_of_mem_mdLengthBlocks hb

/-- Reduction adversary for [BonehShoup2023], Theorem 8.3 (p. 297): runs `adversary`, checks
whether the output pair `(m₁, m₂)` is a valid collision for `lengthStrengthenedMD h` under
`valid`, and if so runs `extractChainCollision` on `mdLengthBlocks k.length m₁` and
`mdLengthBlocks k.length m₂` to extract a `2n`-bit collision for `h`, returning `([], [])` when
the check fails. -/
@[expose] noncomputable def lengthStrengthenedWrapper
    (h : List Bool → List Bool → List Bool) (valid : ℕ → List Bool → Bool)
    (adversary : CollisionFinder) : CollisionFinder :=
  fun n k => do
    let pair ← adversary n k
    pure
      (if isCollision (lengthStrengthenedMD h) valid n k pair.1 pair.2 then
        extractChainCollision h k (List.replicate k.length false)
          (mdLengthBlocks k.length pair.1) (mdLengthBlocks k.length pair.2)
      else
        ([], []))

/-- Uniform strict PPT certificate for `lengthStrengthenedWrapper`. -/
@[program_certificate]
theorem isPPT_lengthStrengthenedWrapper {h : List Bool → List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} {adversary : CollisionFinder}
    (hh : ComputableInPolyTime (fun p : List Bool × List Bool => h p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, x.length = 2 * k.length → (h k x).length = k.length)
    (hvalid : ComputableInPolyTime (fun p : ℕ × List Bool => valid p.1 p.2)
      (encPair encUnary encBits) encBool)
    (ha : IsPPT (encPair encBits encBits) adversary) :
    IsPPT (encPair encBits encBits) (lengthStrengthenedWrapper h valid adversary) := by
  have hCol := (computableInPolyTime_isCollision
    (computableInPolyTime_lengthStrengthenedMD hh hlen) hvalid).tidy
  have hExt := (computableInPolyTime_extractChainCollision hh hlen).tidy
  have hBlk := computableInPolyTime_mdLengthBlocks.tidy
  unfold lengthStrengthenedWrapper
  ppt

private theorem eval_collisionGame_lengthStrengthenedMD_eq
    (h : List Bool → List Bool → List Bool) (valid : ℕ → List Bool → Bool)
    (adversary : CollisionFinder) (n : ℕ)
    (hlen : ∀ k x, k.length = n → x.length = 2 * n → (h k x).length = n)
    (hbound : ∀ m, valid n m = true → mdLengthBlockCount n m < 2 ^ (n / 2)) :
    ProbComp.eval (collisionGame (lengthStrengthenedMD h) valid adversary n) =
      ProbComp.eval (collisionGame h validCompressionInput
        (lengthStrengthenedWrapper h valid adversary) n) := by
  unfold collisionGame lengthStrengthenedWrapper
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun k hk => ?_
  rw [BitString.eval_sampleList] at hk
  have hklen : k.length = n := BitString.length_of_mem_support_uniformList hk
  subst hklen
  refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun pair _ => ?_
  congr 1
  by_cases hcol : isCollision (lengthStrengthenedMD h) valid k.length k pair.1 pair.2 = true
  · simp only [hcol, ↓reduceIte]
    rw [isCollision_eq_true_iff] at hcol
    rcases hcol with ⟨hv₁, hv₂, hne, hdigest⟩
    have hns₁ : ¬ mdLengthBlocks k.length pair.1 <:+ mdLengthBlocks k.length pair.2 :=
      (mdLengthBlocks_suffix_iff (hbound pair.2 hv₂)).not.mpr hne
    have hns₂ : ¬ mdLengthBlocks k.length pair.2 <:+ mdLengthBlocks k.length pair.1 :=
      (mdLengthBlocks_suffix_iff (hbound pair.1 hv₁)).not.mpr hne.symm
    exact (isCollision_extractChainCollision_of_not_suffix (fun x hx => hlen k x rfl hx)
      List.length_replicate
      (fun _ hb => length_of_mem_mdLengthBlocks hb)
      (fun _ hb => length_of_mem_mdLengthBlocks hb)
      hdigest hns₁ hns₂).symm
  · have hcolF : isCollision (lengthStrengthenedMD h) valid k.length k pair.1 pair.2 = false :=
      Bool.eq_false_iff.mpr hcol
    simp only [hcolF, Bool.false_eq_true, ↓reduceIte, isCollision_self]

/-- **Boneh–Shoup Theorem 8.3 (concrete equality):** when `h` preserves `n`-bit output lengths and
every `valid n`-accepted message satisfies `mdLengthBlockCount n m < 2 ^ (n / 2)`, `adversary`
succeeds against `lengthStrengthenedMD h` on `valid` with the exact same probability that
`lengthStrengthenedWrapper h valid adversary` succeeds against `h` on `validCompressionInput`. -/
theorem succProbability_collisionGame_lengthStrengthenedMD_eq
    (h : List Bool → List Bool → List Bool) (valid : ℕ → List Bool → Bool)
    (adversary : CollisionFinder) (n : ℕ)
    (hlen : ∀ k x, k.length = n → x.length = 2 * n → (h k x).length = n)
    (hbound : ∀ m, valid n m = true → mdLengthBlockCount n m < 2 ^ (n / 2)) :
    Game.succProbability
        (ProbComp.eval (collisionGame (lengthStrengthenedMD h) valid adversary n)) =
      Game.succProbability
        (ProbComp.eval
          (collisionGame h validCompressionInput
            (lengthStrengthenedWrapper h valid adversary) n)) :=
  congrArg Game.succProbability
    (eval_collisionGame_lengthStrengthenedMD_eq h valid adversary n hlen hbound)

/-- **Boneh–Shoup Theorem 8.3 (asymptotic):** any `2n → n` collision-resistant compression family
`h` yields an unrestricted collision-resistant hash `lengthStrengthenedMD h` on all bit strings. -/
theorem CompressionFamily.collisionResistant_lengthStrengthenedMD
    {h : List Bool → List Bool → List Bool} (hCF : CompressionFamily h) :
    CollisionResistant (lengthStrengthenedMD h) := by
  refine CollisionResistantOn.of_negligible fun adversary ha => ?_
  obtain ⟨c, d, hlen_out⟩ := ha.on.length_le
  let bound : ℕ → ℕ := fun n => c * (3 * n + 2) ^ d
  let validBound : ℕ → List Bool → Bool := fun n m => decide (m.length ≤ bound n)
  have hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool => validBound p.1 p.2) (encPair encUnary encBits) encBool := by
    unfold validBound bound
    fun_prop
  have hWrapPPT : IsPPT (encPair encBits encBits)
      (lengthStrengthenedWrapper h validBound adversary) :=
    isPPT_lengthStrengthenedWrapper hCF.polyTime hCF.length_eq hvalid ha
  have hNeg := hCF.collisionResistant.negligible _ hWrapPPT
  have hEvBound : ∀ᶠ n in Filter.atTop, bound n + n + 1 < 2 ^ (n / 2) := by
    have hpoly : PolynomiallyBounded (fun n => bound n + n + 2) := by
      unfold bound
      fun_prop
    filter_upwards [hpoly.subexponentiallyBounded.eventually_le_two_pow_div 2 (by decide)]
      with n hn
    omega
  refine negligible_of_eventually_le hNeg ?_
  filter_upwards [hEvBound] with n hn
  have hgame :
      ProbComp.eval (collisionGame (lengthStrengthenedMD h) (fun _ _ => true) adversary n) =
        ProbComp.eval (collisionGame (lengthStrengthenedMD h) validBound adversary n) := by
    simp only [collisionGame, ProbComp.eval_bind, ProbComp.eval_pure]
    refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun k hk => ?_
    rw [BitString.eval_sampleList] at hk
    have hklen : k.length = n := BitString.length_of_mem_support_uniformList hk
    refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun pair hp => ?_
    have hpair_in : ((encPair encUnary encBits) (n, k)).length + 1 = 3 * n + 2 := by
      simp only [length_encPair, encUnary_apply, encBits_apply, List.length_replicate, hklen]
      omega
    have henc := hlen_out (n, k) pair hp
    rw [hpair_in] at henc
    have hm₁ : pair.1.length ≤ bound n := by
      simpa only [encBits_apply] using (length_le_encPair_left encBits encBits pair).trans henc
    have hm₂ : pair.2.length ≤ bound n := by
      simpa only [encBits_apply] using (length_le_encPair_right encBits encBits pair).trans henc
    have hv₁ : validBound n pair.1 = true := decide_eq_true hm₁
    have hv₂ : validBound n pair.2 = true := decide_eq_true hm₂
    congr 1
    refine Bool.eq_iff_iff.mpr ?_
    simp only [isCollision_eq_true_iff, hv₁, hv₂, true_and]
  have hsuccEq :
      Game.succProbability
          (ProbComp.eval (collisionGame (lengthStrengthenedMD h) (fun _ _ => true) adversary n)) =
        Game.succProbability
          (ProbComp.eval
            (collisionGame h validCompressionInput
              (lengthStrengthenedWrapper h validBound adversary) n)) := by
    rw [hgame]
    refine succProbability_collisionGame_lengthStrengthenedMD_eq h validBound adversary n
      (fun k x hk hx => by
        have hlenx : x.length = 2 * k.length := by omega
        simpa only [hk] using hCF.length_eq k x hlenx)
      fun m hm => ?_
    have hmlen : m.length ≤ bound n := of_decide_eq_true (by simpa [validBound] using hm)
    have hcount : mdLengthBlockCount n m ≤ bound n + n + 1 := by
      unfold mdLengthBlockCount
      calc
        (m.length + n / 2) / n + 1 ≤ m.length + n / 2 + 1 := by
          exact Nat.add_le_add_right (Nat.div_le_self _ _) 1
        _ ≤ bound n + n + 1 := by omega
    exact lt_of_le_of_lt hcount hn
  rw [hsuccEq]

/-- Every `2n → n` collision-resistant compression family `h` induces a collision-resistant
hash family `HashFamily (lengthStrengthenedMD h)` on arbitrary bit strings. -/
theorem CompressionFamily.hashFamily_lengthStrengthenedMD
    {h : List Bool → List Bool → List Bool} (hCF : CompressionFamily h) :
    HashFamily (lengthStrengthenedMD h) where
  polyTime := computableInPolyTime_lengthStrengthenedMD hCF.polyTime hCF.length_eq
  length_eq k _ := length_lengthStrengthenedMD (hCF.length_eq k)
  collisionResistant := hCF.collisionResistant_lengthStrengthenedMD

end Cslib.Crypto
