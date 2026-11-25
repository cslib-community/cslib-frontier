/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.AffineHash
public import CslibFrontier.Crypto.Computational.InaccessibleEntropy.Basic
public import CslibFrontier.Crypto.Computational.OneWay
public import CslibFrontier.Foundations.Data.BitString.List.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Crypto.Computational.OneWay.Collision
import CslibFrontier.Crypto.Computational.OneWay.Normalize
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Foundations.Data.Nat.Log
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.UniformRelabel

/-!
# Inaccessible average max-entropy from any one-way function

Given any uniform `OneWay` function `f`, output-length normalization
(`OneWay.exists_fixedOutputLength`) produces a one-way function `g` sending `n`-bit inputs to
`m(n)`-bit outputs. Following `[HHRVW2020]`, Section 4.2, Theorem 4.5 (pp. 21–25), we combine `g`
with the constructible `3`-wise independent Boolean affine hash family `affineHash` on `m(n)`-bit
strings (`isThreeWiseIndependentHash_affineHash`) and a dyadic `(Nat.log 2 n + 1)`-bit prefix
index `r` truncated at `min r n`:
$$F_0(x, A, b, r) = \bigl(A, b, r, \mathrm{zeroPadPrefix}\;n\;r\;(A\,g(x) + b)\bigr).$$

Parameterizing the light-sibling set by a polynomial threshold exponent `c : ℕ`,
$$\widetilde{L}_c(y_0, r) =
  \{y_0\} \cup \{y \mid 4 (n + 1)^c |g^{-1}(y)| \le 2^{n - \min(r, n)}\},$$
establishes `[HHRVW2020]`, Theorem 4.5 against uniform strict-PPT adversaries (with an
adversary-independent accessible-set family for each `c`, stronger than Definition 3.9's
adversary-dependent quantifier):

1. **Claim 4.6** (`rompelBase_escape_le_mul_inversion`, pp. 21–22): sampling a prefix-colliding
   affine seed via `adjustAffineSeed` (`toReal_map_adjustAffineSeed_eq`) turns any adversary `A`
   into a uniform strict-PPT `g`-inverter (`rompelBaseInverter`) whose inversion success is at least
   `1 / (4 * (n + 1) ^ c)` of `A`'s escape probability outside `L_{0, c}`.
2. **Claim 4.8** (`rompelBase_heavy_sibling_prob_ge`, p. 23): for `gFin x ≠ gFin x*` with
   `|gFin⁻¹(gFin x)| ≤ |gFin⁻¹(gFin x*)| ≤ 2^(n - r)`, `3`-wise independence and Markov's
   inequality show that uniform resampling from `F₀⁻¹(F₀(x, s, r))` hits `(x*, s, r)` with
   probability at least `2^(-n) / 8`.
3. **Claim 4.7** (`rompelBase_accessible_le_conditionalEntropy_sub`, pp. 21, 23–25): Markov's
   inequality on `collisionProbability` bounds heavy fibers `|gFin⁻¹(gFin x*)| ≥ 2^(n - c⌊log₂ n⌋)`,
   and for every remaining distinct-image pair with `|gFin⁻¹(gFin x)| ≤ |gFin⁻¹(gFin x*)|`, all
   `c * Nat.log 2 n + 1` truncation lengths `r_j = n - (Nat.log 2 |gFin⁻¹(gFin x*)| + 1 + j)`
   simultaneously satisfy Claim 4.8 and exclude `gFin x*` from `rompelLightImages c`, yielding a
   gap of at least `(c * Nat.log 2 n + 1) / (64 * (n + 1))` (recovering `1 / (64 * (n + 1))` at
   `c = 0`).
4. **Theorem 4.5** (`OneWay.rompelBase_logGap`, p. 21): for a `OneWay` function `g` with fixed
   output length `m(n)`, the single uniform polynomial-time function family
   `rompelBaseEvalWord g outLen` achieves an eventual `d * Real.logb 2 n / n` entropy gap for every
   constant `d > 0`. `OneWay.rompelFamily` packages each threshold exponent `c` as an
   `InaccessibleEntropyFamily` with integer denominator
   `rompelGapDenom c n = 64 * (n + 1) / (c * Nat.log 2 n + 1) + 1`.
   `OneWay.exists_rompelBase_logGap` and `OneWay.exists_inaccessibleEntropyFamily` apply this to an
   arbitrary `OneWay` function, after normalizing its output length.

`F₀` differs from the source's $F(x, g, i) = (g(f(x))_{1, \dots, i}, g, i)$ on
$\{0,1\}^n \times G \times [n]$ in three ways:

* **The hash family.** `affineHash` from `m(n)` to `n` bits is one of the constructible `3`-wise
  independent families that Theorem 4.5 allows, but its seed has `n * m(n) + n` bits. The input
  width is `rompelBaseInLen n m = n + (n * m + n) + (Nat.log 2 n + 1)`, which is `Θ(n * m(n))` and
  so `Θ(n ^ 2)` even for length-preserving `g`. The source's `O(n)` width, which its Theorem 5.2
  (p. 26) uses, needs a `3`-wise independent family with `O(n)`-bit descriptions.
* **The prefix length.** It is `min r n` for a uniform `(Nat.log 2 n + 1)`-bit number `r`, so it
  ranges over `{0, …, n}` with extra mass at `n`, instead of being uniform on `[n]`.
* **The one-way function.** The source takes a length-preserving `f`. Here `g` has any fixed
  output length `m(n)`, and `OneWay.exists_fixedOutputLength` pads an arbitrary `OneWay` function to
  such a `g`.

## Main definitions

* `Cslib.Crypto.rompelTruncWidth`, `Cslib.Crypto.rompelSeedWidth`, `Cslib.Crypto.rompelBaseInLen`,
  `Cslib.Crypto.rompelBaseOutLen`, `Cslib.Crypto.rompelGapDenom`: bit-width and gap-denominator
  schedules of $F_0$.
* `Cslib.Crypto.RompelBaseInput`, `Cslib.Crypto.RompelBaseOutput`: structured finite views of
  $F_0$'s inputs and outputs, with bit-string equivalences `rompelBaseInputEquiv` and
  `rompelBaseOutputEquiv`.
* `Cslib.Crypto.rompelBaseHashFin`, `Cslib.Crypto.rompelBaseEvalWord`: finite and word-level
  evaluators of $F_0$.
* `Cslib.Crypto.rompelLightImages`, `Cslib.Crypto.rompelAccessibleInputSet`,
  `Cslib.Crypto.rompelAccessibleSet`: polynomial-threshold light-sibling sets and accessible
  preimage sets $L_{0, c}$.
* `Cslib.Crypto.rompelBaseInverter`: uniform strict-PPT OWF inverter reduction from $F_0$ escape.

## Main results

* `Cslib.Crypto.computableInPolyTime_rompelBaseEvalWord`: plain polynomial-time certificate for
  `rompelBaseEvalWord`.
* `Cslib.Crypto.isPPT_rompelBaseInverter`: plain uniform strict-PPT certificate for
  `rompelBaseInverter`.
* `Cslib.Crypto.rompelBase_escape_le_mul_inversion`: Claim 4.6 (`[HHRVW2020]`, pp. 21–22).
* `Cslib.Crypto.rompelBase_heavy_sibling_prob_ge`: Claim 4.8 (`[HHRVW2020]`, p. 23).
* `Cslib.Crypto.rompelBase_accessible_le_conditionalEntropy_sub`: Claim 4.7
  (`[HHRVW2020]`, pp. 21, 23–25).
* `Cslib.Crypto.OneWay.rompelBase_logGap`: Theorem 4.5 (`[HHRVW2020]`, p. 21) for `F₀`, with the
  deviations above: one fixed base family achieving eventual gap `d * Real.logb 2 n / n` for every
  `d > 0`.
* `Cslib.Crypto.OneWay.exists_rompelBase_logGap`,
  `Cslib.Crypto.OneWay.exists_inaccessibleEntropyFamily`: the same family from an arbitrary
  `OneWay` function, and an `InaccessibleEntropyFamily` from it.

## References

* [I. Haitner, T. Holenstein, O. Reingold, S. Vadhan, H. Wee, *Inaccessible Entropy II: IE
  Functions and Universal One-Way Hashing*, Section 4.2, Theorem 4.5 and Claims 4.6–4.8,
  pp. 21–25][HHRVW2020]
* [J. Rompel, *One-Way Functions are Necessary and Sufficient for Secure Signatures*, Section 3,
  pp. 388–391][Rompel1990]
-/

public section

namespace Cslib.Crypto

open Cslib.Probability Cslib.BitString.LinearHash Finset Turing.MultiTapeTM
open scoped BigOperators ENNReal NNReal

/-! ### Bit-width schedule and structured input/output views -/

/-- Bit width $\lfloor \log_2 n \rfloor + 1$ of the truncation-length field in $F_0$, large enough
to represent every $r \in \{0, \dots, n\}$ injectively (`n < 2 ^ rompelTruncWidth n`). -/
@[expose] def rompelTruncWidth (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- Affine seed bit width $n m + n$ for hashing $m$-bit images to $n$-bit digests. -/
@[expose] def rompelSeedWidth (n m : ℕ) : ℕ := n * m + n

/-- Total input bit width $n + (n m + n) + (\lfloor \log_2 n \rfloor + 1)$ of $F_0$. -/
@[expose] def rompelBaseInLen (n m : ℕ) : ℕ := n + rompelSeedWidth n m + rompelTruncWidth n

/-- Total output bit width $(n m + n) + (\lfloor \log_2 n \rfloor + 1) + n$ of $F_0$. -/
@[expose] def rompelBaseOutLen (n m : ℕ) : ℕ := rompelSeedWidth n m + rompelTruncWidth n + n

/-- Integer entropy-gap denominator
$\lfloor 64 (n + 1) / (c \lfloor \log_2 n \rfloor + 1) \rfloor + 1$ at polynomial light-image
threshold exponent `c`. -/
@[expose] def rompelGapDenom (c n : ℕ) : ℕ :=
  64 * (n + 1) / (c * Nat.log 2 n + 1) + 1

@[fun_prop]
theorem computableInPolyTime_rompelTruncWidth :
    ComputableInPolyTime rompelTruncWidth encUnary encUnary := by
  unfold rompelTruncWidth
  fun_prop

@[fun_prop]
theorem computableInPolyTime_rompelGapDenom (c : ℕ) :
    ComputableInPolyTime (rompelGapDenom c) encUnary encUnary := by
  unfold rompelGapDenom
  fun_prop

theorem rompelGapDenom_pos (c n : ℕ) : 1 ≤ rompelGapDenom c n :=
  Nat.succ_pos _

theorem lt_two_pow_rompelTruncWidth (n : ℕ) : n < 2 ^ rompelTruncWidth n := by
  simpa only [rompelTruncWidth] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) n

theorem two_pow_rompelTruncWidth_le (n : ℕ) : 2 ^ rompelTruncWidth n ≤ 2 * (n + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · decide
  · have hle := Nat.pow_log_le_self 2 hn.ne'
    rw [rompelTruncWidth, Nat.pow_succ]
    omega

/-- Structured input `(preimage, hashRows, hashShift, truncBits)` to `[HHRVW2020]`'s base function
$F_0$ (Section 4.2, Theorem 4.5, p. 21). -/
structure RompelBaseInput (n m : ℕ) where
  /-- Uniform `n`-bit input $x$ to the normalized one-way function $g$. -/
  preimage : BitString n
  /-- Matrix rows of the Boolean affine hash `BitString m → BitString n`. -/
  hashRows : Fin n → BitString m
  /-- Shift vector of the Boolean affine hash $h_{A, b}$. -/
  hashShift : BitString n
  /-- `(Nat.log 2 n + 1)`-bit word encoding the saturating prefix length $r \le n$. -/
  truncBits : BitString (rompelTruncWidth n)
  deriving DecidableEq, Fintype

instance (n m : ℕ) : Nonempty (RompelBaseInput n m) := ⟨⟨0, 0, 0, 0⟩⟩

/-- Saturating prefix length $r = \min(n, \mathrm{binaryValue}(\mathrm{truncBits})) \le n$. -/
@[expose] def RompelBaseInput.truncIndex {n m : ℕ} (z : RompelBaseInput n m) : ℕ :=
  BitString.boundedBinaryValue n (List.ofFn z.truncBits)

theorem RompelBaseInput.truncIndex_le {n m : ℕ} (z : RompelBaseInput n m) : z.truncIndex ≤ n :=
  BitString.boundedBinaryValue_le n (List.ofFn z.truncBits)

/-- Pack a `RompelBaseInput n m` into a word of length `rompelBaseInLen n m`. -/
@[expose] def RompelBaseInput.packWord {n m : ℕ} (z : RompelBaseInput n m) : List Bool :=
  List.ofFn z.preimage ++ packAffineSeed (z.hashRows, z.hashShift) ++ List.ofFn z.truncBits

@[simp] theorem RompelBaseInput.length_packWord {n m : ℕ} (z : RompelBaseInput n m) :
    z.packWord.length = rompelBaseInLen n m := by
  simp [RompelBaseInput.packWord, rompelBaseInLen, rompelSeedWidth]; omega

/-- Unpack a word into a `RompelBaseInput n m`. -/
@[expose] def RompelBaseInput.unpackWord (n m : ℕ) (w : List Bool) : RompelBaseInput n m :=
  let sLen := rompelSeedWidth n m
  let rest := w.drop n
  let seed := unpackAffineSeed n m (rest.take sLen)
  { preimage := BitString.ofList n (w.take n)
    hashRows := seed.1
    hashShift := seed.2
    truncBits := BitString.ofList (rompelTruncWidth n) (rest.drop sLen) }

@[simp] theorem RompelBaseInput.unpackWord_packWord {n m : ℕ} (z : RompelBaseInput n m) :
    RompelBaseInput.unpackWord n m z.packWord = z := by
  have hx : (List.ofFn z.preimage).length = n := List.length_ofFn
  have hs : (packAffineSeed (z.hashRows, z.hashShift)).length = rompelSeedWidth n m :=
    length_packAffineSeed _
  cases z with | mk pre rows shift tbits =>
  simp only [RompelBaseInput.packWord, RompelBaseInput.unpackWord, List.append_assoc,
    List.take_left' hx, List.drop_left' hx, List.take_left' hs, List.drop_left' hs,
    unpackAffineSeed_packAffineSeed, BitString.ofList_ofFn]

theorem RompelBaseInput.packWord_unpackWord {n m : ℕ} {w : List Bool}
    (hw : w.length = rompelBaseInLen n m) :
    (RompelBaseInput.unpackWord n m w).packWord = w := by
  have hx : (w.take n).length = n := by simp [hw, rompelBaseInLen]; omega
  have hs : ((w.drop n).take (rompelSeedWidth n m)).length = rompelSeedWidth n m := by
    simp [hw, rompelBaseInLen]; omega
  have ht : ((w.drop n).drop (rompelSeedWidth n m)).length = rompelTruncWidth n := by
    simp [hw, rompelBaseInLen]
  simp only [RompelBaseInput.unpackWord, RompelBaseInput.packWord, Prod.mk.eta,
    packAffineSeed_unpackAffineSeed hs, BitString.ofFn_ofList hx, BitString.ofFn_ofList ht,
    List.append_assoc, List.take_append_drop]

/-- Exact bit-string equivalence between `RompelBaseInput n m` and
`BitString (rompelBaseInLen n m)`. -/
@[expose] def rompelBaseInputEquiv (n m : ℕ) :
    RompelBaseInput n m ≃ BitString (rompelBaseInLen n m) where
  toFun z := BitString.ofList (rompelBaseInLen n m) z.packWord
  invFun b := RompelBaseInput.unpackWord n m (List.ofFn b)
  left_inv z := by
    dsimp only
    rw [BitString.ofFn_ofList z.length_packWord, RompelBaseInput.unpackWord_packWord]
  right_inv b := by
    dsimp only
    rw [RompelBaseInput.packWord_unpackWord List.length_ofFn, BitString.ofList_ofFn]

@[simp] theorem ofFn_rompelBaseInputEquiv {n m : ℕ} (z : RompelBaseInput n m) :
    List.ofFn (rompelBaseInputEquiv n m z) = z.packWord :=
  BitString.ofFn_ofList z.length_packWord

/-- Structured output `(hashRows, hashShift, truncBits, prefixDigest)` of `[HHRVW2020]`'s base
function $F_0$ (Section 4.2, Theorem 4.5, p. 21). -/
structure RompelBaseOutput (n m : ℕ) where
  /-- Matrix rows of the Boolean affine hash $h_{A, b}$. -/
  hashRows : Fin n → BitString m
  /-- Shift vector of the Boolean affine hash $h_{A, b}$. -/
  hashShift : BitString n
  /-- `(Nat.log 2 n + 1)`-bit word encoding the saturating prefix length $r$. -/
  truncBits : BitString (rompelTruncWidth n)
  /-- Zero-padded `r`-bit prefix of $h_{A, b}(g(x))$. -/
  prefixDigest : BitString n
  deriving DecidableEq, Fintype

/-- Pack a `RompelBaseOutput n m` into a word of length `rompelBaseOutLen n m`. -/
@[expose] def RompelBaseOutput.packWord {n m : ℕ} (y : RompelBaseOutput n m) : List Bool :=
  packAffineSeed (y.hashRows, y.hashShift) ++ List.ofFn y.truncBits ++ List.ofFn y.prefixDigest

@[simp] theorem RompelBaseOutput.length_packWord {n m : ℕ} (y : RompelBaseOutput n m) :
    y.packWord.length = rompelBaseOutLen n m := by
  simp [RompelBaseOutput.packWord, rompelBaseOutLen, rompelSeedWidth]; omega

/-- Unpack a word into a `RompelBaseOutput n m`. -/
@[expose] def RompelBaseOutput.unpackWord (n m : ℕ) (w : List Bool) : RompelBaseOutput n m :=
  let sLen := rompelSeedWidth n m
  let tLen := rompelTruncWidth n
  let seed := unpackAffineSeed n m (w.take sLen)
  let rest := w.drop sLen
  { hashRows := seed.1
    hashShift := seed.2
    truncBits := BitString.ofList tLen (rest.take tLen)
    prefixDigest := BitString.ofList n (rest.drop tLen) }

@[simp] theorem RompelBaseOutput.unpackWord_packWord {n m : ℕ} (y : RompelBaseOutput n m) :
    RompelBaseOutput.unpackWord n m y.packWord = y := by
  have hs : (packAffineSeed (y.hashRows, y.hashShift)).length = rompelSeedWidth n m :=
    length_packAffineSeed _
  have ht : (List.ofFn y.truncBits).length = rompelTruncWidth n := List.length_ofFn
  cases y with | mk rows shift tbits dig =>
  simp only [RompelBaseOutput.packWord, RompelBaseOutput.unpackWord, List.append_assoc,
    List.take_left' hs, List.drop_left' hs, List.take_left' ht, List.drop_left' ht,
    unpackAffineSeed_packAffineSeed, BitString.ofList_ofFn]

theorem RompelBaseOutput.packWord_unpackWord {n m : ℕ} {w : List Bool}
    (hw : w.length = rompelBaseOutLen n m) :
    (RompelBaseOutput.unpackWord n m w).packWord = w := by
  have hs : (w.take (rompelSeedWidth n m)).length = rompelSeedWidth n m := by
    simp [hw, rompelBaseOutLen]; omega
  have ht : ((w.drop (rompelSeedWidth n m)).take (rompelTruncWidth n)).length =
      rompelTruncWidth n := by
    simp [hw, rompelBaseOutLen]; omega
  have hd : ((w.drop (rompelSeedWidth n m)).drop (rompelTruncWidth n)).length = n := by
    simp [hw, rompelBaseOutLen]
  simp only [RompelBaseOutput.unpackWord, RompelBaseOutput.packWord, Prod.mk.eta,
    packAffineSeed_unpackAffineSeed hs, BitString.ofFn_ofList ht, BitString.ofFn_ofList hd,
    List.append_assoc, List.take_append_drop]

/-- Exact bit-string equivalence between `RompelBaseOutput n m` and
`BitString (rompelBaseOutLen n m)`. -/
@[expose] def rompelBaseOutputEquiv (n m : ℕ) :
    RompelBaseOutput n m ≃ BitString (rompelBaseOutLen n m) where
  toFun y := BitString.ofList (rompelBaseOutLen n m) y.packWord
  invFun b := RompelBaseOutput.unpackWord n m (List.ofFn b)
  left_inv y := by
    dsimp only
    rw [BitString.ofFn_ofList y.length_packWord, RompelBaseOutput.unpackWord_packWord]
  right_inv b := by
    dsimp only
    rw [RompelBaseOutput.packWord_unpackWord List.length_ofFn, BitString.ofList_ofFn]

/-! ### Finite and word-level evaluators of $F_0$ -/

/-- Finite evaluator $F_0(x, A, b, r) = (A, b, r, \mathrm{zeroPadPrefix}\;n\;r\;(A\,g(x) + b))$
(`[HHRVW2020]`, Section 4.2, Theorem 4.5, p. 21). -/
@[expose] def rompelBaseHashFin {n m : ℕ} (gFin : BitString n → BitString m)
    (z : RompelBaseInput n m) : RompelBaseOutput n m where
  hashRows := z.hashRows
  hashShift := z.hashShift
  truncBits := z.truncBits
  prefixDigest := zeroPadPrefix n z.truncIndex
    (Cslib.BitString.LinearHash.affineHash (z.hashRows, z.hashShift) (gFin z.preimage))

theorem rompelBaseHashFin_eq_iff {n m : ℕ} (gFin : BitString n → BitString m)
    (z' z : RompelBaseInput n m) :
    rompelBaseHashFin gFin z' = rompelBaseHashFin gFin z ↔
      z'.hashRows = z.hashRows ∧ z'.hashShift = z.hashShift ∧ z'.truncBits = z.truncBits ∧
        prefixProj n z.truncIndex
          (Cslib.BitString.LinearHash.affineHash (z.hashRows, z.hashShift) (gFin z'.preimage)) =
          prefixProj n z.truncIndex
            (Cslib.BitString.LinearHash.affineHash (z.hashRows, z.hashShift)
              (gFin z.preimage)) := by
  cases z'; cases z
  simp only [rompelBaseHashFin, RompelBaseOutput.mk.injEq, RompelBaseInput.truncIndex]
  exact ⟨fun ⟨rfl, rfl, rfl, h⟩ =>
      ⟨rfl, rfl, rfl, (zeroPadPrefix_eq_iff_prefixProj_eq _ _).mp h⟩,
    fun ⟨rfl, rfl, rfl, h⟩ =>
      ⟨rfl, rfl, rfl, (zeroPadPrefix_eq_iff_prefixProj_eq _ _).mpr h⟩⟩

/-- Word-level evaluator of `[HHRVW2020]`'s base function $F_0$
(Section 4.2, Theorem 4.5, p. 21). -/
@[expose] def rompelBaseEvalWord (g : List Bool → List Bool) (outLen : ℕ → ℕ)
    (n : ℕ) (zWord : List Bool) : List Bool :=
  let m := outLen n
  let sLen := rompelSeedWidth n m
  let tLen := rompelTruncWidth n
  let x := BitString.listRow n 0 (zWord.take n)
  let rest := zWord.drop n
  let seed := BitString.listRow sLen 0 (rest.take sLen)
  let rBits := BitString.listRow tLen 0 (rest.drop sLen)
  let r := BitString.boundedBinaryValue n rBits
  let gx := BitString.listRow m 0 (g x)
  let fullHash := wordAffineHash n seed gx
  seed ++ rBits ++ (fullHash.take r ++ List.replicate (n - r) false)

@[simp] theorem length_rompelBaseEvalWord (g : List Bool → List Bool) (outLen : ℕ → ℕ)
    (n : ℕ) (zWord : List Bool) :
    (rompelBaseEvalWord g outLen n zWord).length = rompelBaseOutLen n (outLen n) := by
  let r := BitString.boundedBinaryValue n
    (BitString.listRow (rompelTruncWidth n) 0 ((zWord.drop n).drop (rompelSeedWidth n (outLen n))))
  have hr : r ≤ n := BitString.boundedBinaryValue_le n _
  simp only [rompelBaseEvalWord, rompelBaseOutLen, List.length_append, BitString.length_listRow,
    List.length_take, length_wordAffineHash, List.length_replicate]
  change rompelSeedWidth n (outLen n) + rompelTruncWidth n + (min r n + (n - r)) = _
  omega

/-- On packed inputs, `rompelBaseEvalWord` computes `rompelBaseHashFin` exactly. -/
theorem rompelBaseEvalWord_packWord (g : List Bool → List Bool) (outLen : ℕ → ℕ) (n : ℕ)
    (z : RompelBaseInput n (outLen n)) :
    rompelBaseEvalWord g outLen n z.packWord =
      (rompelBaseHashFin (wordToFinMap n (outLen n) g) z).packWord := by
  have hx : (List.ofFn z.preimage).length = n := List.length_ofFn
  have hs : (packAffineSeed (z.hashRows, z.hashShift)).length = rompelSeedWidth n (outLen n) :=
    length_packAffineSeed _
  simp only [rompelBaseEvalWord, RompelBaseInput.packWord, RompelBaseOutput.packWord,
    rompelBaseHashFin, List.append_assoc, List.take_left' hx, List.drop_left' hx,
    List.take_left' hs, List.drop_left' hs, BitString.listRow_zero, BitString.ofList_ofFn,
    BitString.ofFn_ofList hs]
  rw [wordAffineHash_eq_ofFn, unpackAffineSeed_packAffineSeed, ofFn_zeroPadPrefix,
    Nat.min_eq_left z.truncIndex_le]
  rfl

theorem wordToFinMap_rompelBaseEvalWord (g : List Bool → List Bool) (outLen : ℕ → ℕ) (n : ℕ)
    (z : RompelBaseInput n (outLen n)) :
    wordToFinMap (rompelBaseInLen n (outLen n)) (rompelBaseOutLen n (outLen n))
        (rompelBaseEvalWord g outLen n) (rompelBaseInputEquiv n (outLen n) z) =
      rompelBaseOutputEquiv n (outLen n)
        (rompelBaseHashFin (wordToFinMap n (outLen n) g) z) := by
  rw [wordToFinMap, ofFn_rompelBaseInputEquiv, rompelBaseEvalWord_packWord, rompelBaseOutputEquiv]
  rfl

open ComputableInPolyTime in
/-- Plain polynomial-time certificate for `rompelBaseEvalWord`. -/
@[fun_prop]
theorem computableInPolyTime_rompelBaseEvalWord {g : List Bool → List Bool} {outLen : ℕ → ℕ}
    (hg : ComputableInPolyTime g encBits encBits)
    (houtLen : ComputableInPolyTime outLen encUnary encUnary) :
    ComputableInPolyTime (fun p : ℕ × List Bool => rompelBaseEvalWord g outLen p.1 p.2)
      (encPair encUnary encBits) encBits := by
  have hn := fst encUnary encBits
  have hz := snd encUnary encBits
  have hm := houtLen.comp hn
  have hs : ComputableInPolyTime (fun p : ℕ × List Bool => rompelSeedWidth p.1 (outLen p.1))
      (encPair encUnary encBits) encUnary :=
    unary_add' (unary_mul' hn hm) hn
  have hx := bitsRowWithInput hn (.const 0) (bitsTakeWithInput hz hn)
  have hrest := bitsDropWithInput hz hn
  have hseed := bitsRowWithInput hs (.const 0) (bitsTakeWithInput hrest hs)
  have ht : ComputableInPolyTime (fun p : ℕ × List Bool => rompelTruncWidth p.1)
      (encPair encUnary encBits) encUnary :=
    unary_add' (unary_log_two.comp hn) (.const 1)
  have hrBits := bitsRowWithInput ht (.const 0) (bitsDropWithInput hrest hs)
  have hr := bitsBoundedBinaryValueWithInput hn hrBits
  have hhash := computableInPolyTime_wordAffineHash hn hseed
    (bitsRowWithInput hm (.const 0) (hg.comp hx))
  exact bitsAppend (bitsAppend hseed hrBits)
    (bitsAppend (bitsTakeWithInput hhash hr)
      ((bitsReplicate false).comp (unary_sub' hn hr)))

/-! ### Accessible preimage sets $L_{0, c}$ and the OWF inverter reduction (Claim 4.6) -/

/-- Light sibling images
$\widetilde{L}_c(y_0, r) = \{y_0\} \cup \{y \mid 4 (n + 1)^c |g^{-1}(y)| \le 2^{n - \min(r, n)}\}$
with polynomial threshold exponent `c` (`[HHRVW2020]`, Section 4.2, Theorem 4.5, p. 21; setting
`c = 0` recovers the constant threshold $2^{n - \min(r, n)} / 4$). -/
@[expose] def rompelLightImages {n m : ℕ} (c : ℕ) (gFin : BitString n → BitString m)
    (y₀ : BitString m) (r : ℕ) : Finset (BitString m) :=
  insert y₀ (univ.filter fun y => 4 * (n + 1) ^ c * #(fiberSet gFin y) ≤ 2 ^ (n - min r n))

theorem self_mem_rompelLightImages {n m : ℕ} (c : ℕ) (gFin : BitString n → BitString m)
    (y₀ : BitString m) (r : ℕ) : y₀ ∈ rompelLightImages c gFin y₀ r :=
  mem_insert_self y₀ _

/-- Accessible preimage set
$L_{0, c}(z) = \{z' \in F_0^{-1}(F_0(z)) \mid g(x') \in \widetilde{L}_c(g(x), r)\}$ on
`RompelBaseInput n m` (`[HHRVW2020]`, Section 4.2, Theorem 4.5, p. 21). -/
@[expose] def rompelAccessibleInputSet {n m : ℕ} (c : ℕ) (gFin : BitString n → BitString m)
    (z : RompelBaseInput n m) : Finset (RompelBaseInput n m) :=
  (fiberSet (rompelBaseHashFin gFin) (rompelBaseHashFin gFin z)).filter fun z' =>
    gFin z'.preimage ∈ rompelLightImages c gFin (gFin z.preimage) z.truncIndex

theorem self_mem_rompelAccessibleInputSet {n m : ℕ} (c : ℕ) (gFin : BitString n → BitString m)
    (z : RompelBaseInput n m) : z ∈ rompelAccessibleInputSet c gFin z :=
  mem_filter.mpr ⟨self_mem_fiberSet _ z, self_mem_rompelLightImages c _ _ _⟩

theorem rompelAccessibleInputSet_subset_fiber {n m : ℕ} (c : ℕ) (gFin : BitString n → BitString m)
    (z : RompelBaseInput n m) :
    rompelAccessibleInputSet c gFin z ⊆
      fiberSet (rompelBaseHashFin gFin) (rompelBaseHashFin gFin z) :=
  filter_subset _ _

/-- Accessible preimage set $L_{0, c}$ transported to `BitString (rompelBaseInLen n (outLen n))`. -/
@[expose] def rompelAccessibleSet (c : ℕ) (g : List Bool → List Bool) (outLen : ℕ → ℕ) (n : ℕ)
    (b : BitString (rompelBaseInLen n (outLen n))) :
    Finset (BitString (rompelBaseInLen n (outLen n))) :=
  (rompelAccessibleInputSet c (wordToFinMap n (outLen n) g)
    ((rompelBaseInputEquiv n (outLen n)).symm b)).map
      (rompelBaseInputEquiv n (outLen n)).toEmbedding

theorem self_mem_rompelAccessibleSet (c : ℕ) (g : List Bool → List Bool) (outLen : ℕ → ℕ) (n : ℕ)
    (b : BitString (rompelBaseInLen n (outLen n))) :
    b ∈ rompelAccessibleSet c g outLen n b := by
  rw [rompelAccessibleSet, mem_map]
  exact ⟨(rompelBaseInputEquiv n (outLen n)).symm b,
    self_mem_rompelAccessibleInputSet c _ _,
    (rompelBaseInputEquiv n (outLen n)).apply_symm_apply b⟩

theorem rompelAccessibleSet_subset_fiber (c : ℕ) (g : List Bool → List Bool) (outLen : ℕ → ℕ)
    (n : ℕ) (b : BitString (rompelBaseInLen n (outLen n))) :
    rompelAccessibleSet c g outLen n b ⊆
      fiberSet (wordToFinMap (rompelBaseInLen n (outLen n)) (rompelBaseOutLen n (outLen n))
          (rompelBaseEvalWord g outLen n))
        (wordToFinMap (rompelBaseInLen n (outLen n)) (rompelBaseOutLen n (outLen n))
          (rompelBaseEvalWord g outLen n) b) := by
  intro b' hb'
  rw [rompelAccessibleSet, mem_map] at hb'
  obtain ⟨z', hz', rfl⟩ := hb'
  have hz'_fib := mem_fiberSet _ _ _ |>.mp (rompelAccessibleInputSet_subset_fiber c _ _ hz')
  rw [mem_fiberSet]
  simp only [Equiv.coe_toEmbedding]
  conv_rhs => rw [← (rompelBaseInputEquiv n (outLen n)).apply_symm_apply b]
  rw [wordToFinMap_rompelBaseEvalWord, wordToFinMap_rompelBaseEvalWord, hz'_fib]

/-- Uniform strict-PPT inverter reduction (`[HHRVW2020]`, Section 4.2, Claim 4.6, pp. 21–22):
on challenge image `y`, sample uniform `x` and `rBits`, sample a prefix-colliding affine seed via
`wordAdjustAffineSeed`, run `A` on `x ++ seed ++ rBits`, and output the `n`-bit prefix. -/
noncomputable def rompelBaseInverter (g : List Bool → List Bool) (outLen : ℕ → ℕ)
    (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ) (y : List Bool) :
    ProbComp (List Bool) := do
  let x ← Cslib.BitString.sampleList n
  let rBits ← Cslib.BitString.sampleList (rompelTruncWidth n)
  let rawSeed ← Cslib.BitString.sampleList (rompelSeedWidth n (outLen n))
  let seed := wordAdjustAffineSeed n (outLen n)
    (Cslib.BitString.boundedBinaryValue n rBits) y (g x) rawSeed
  let raw ← A n (x ++ seed ++ rBits)
  return raw.take n

open ComputableInPolyTime in
/-- Plain uniform strict-PPT certificate for `rompelBaseInverter`. -/
theorem isPPT_rompelBaseInverter {g : List Bool → List Bool} {outLen : ℕ → ℕ}
    {A : ℕ → List Bool → ProbComp (List Bool)}
    (hg : ComputableInPolyTime g encBits encBits)
    (houtLen : ComputableInPolyTime outLen encUnary encUnary)
    (hA : IsPPT encBits A) :
    IsPPT encBits (rompelBaseInverter g outLen A) := by
  apply IsPPTOn.isPPT
  refine (sampleList (by fun_prop)).bind_with ?_
  refine (sampleList (by fun_prop)).bind_with ?_
  refine (sampleList (by unfold rompelSeedWidth; fun_prop)).bind_with ?_
  have hp := id'
    (encIn := encPair (encPair (encPair (encPair encUnary encBits) encBits) encBits) encBits)
  have hparameter := hp.fst'.fst'.fst'.fst'
  have hx := hp.fst'.fst'.snd'
  have hrBits := hp.fst'.snd'
  have hadjust := computableInPolyTime_wordAdjustAffineSeed hparameter (houtLen.comp hparameter)
    (bitsBoundedBinaryValueWithInput hparameter hrBits)
    hp.fst'.fst'.fst'.snd' (hg.comp hx) hp.snd'
  have hprepare := bitsAppend (bitsAppend hx hadjust) hrBits
  have hresult := bitsTakeWithInput (snd _ encBits) (hparameter.comp (fst _ encBits))
  simpa only [bind_pure_comp, Function.comp_def] using
    (hA.preprocess hparameter hprepare).map_with hresult

private def rompelTupleEquiv (n m : ℕ) :
    (BitString n × ((Fin n → BitString m) × BitString n) × BitString (rompelTruncWidth n)) ≃
      RompelBaseInput n m where
  toFun t := ⟨t.1, t.2.1.1, t.2.1.2, t.2.2⟩
  invFun z := (z.preimage, (z.hashRows, z.hashShift), z.truncBits)
  left_inv t := by rcases t with ⟨x, ⟨rows, shift⟩, rBits⟩; rfl
  right_inv z := by cases z; rfl

private theorem uniformList_seed_eq_map (k n : ℕ) :
    Cslib.BitString.uniformList (k * n + k) =
      (PMF.uniformOfFintype ((Fin k → BitString n) × BitString k)).map packAffineSeed := by
  rw [Cslib.BitString.uniformList, ← PMF.uniformOfFintype_map_equiv (affineSeedEquiv k n).symm,
    PMF.map_comp]
  exact congrArg (PMF.uniformOfFintype _).map (funext ofFn_affineSeedEquiv_symm)

private theorem uniformList_rompelBaseInLen_eq (n m : ℕ) :
    Cslib.BitString.uniformList (rompelBaseInLen n m) =
      (PMF.uniformOfFintype (BitString n)).bind fun x =>
        (PMF.uniformOfFintype (BitString (rompelTruncWidth n))).bind fun rBits =>
          (PMF.uniformOfFintype ((Fin n → BitString m) × BitString n)).map fun s =>
            (RompelBaseInput.mk x s.1 s.2 rBits).packWord := by
  rw [Cslib.BitString.uniformList]
  relabel_uniform ((Equiv.prodCongr (Equiv.refl (BitString n)) (Equiv.prodComm _ _)).trans
    ((rompelTupleEquiv n m).trans (rompelBaseInputEquiv n m))) with t
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, ofFn_rompelBaseInputEquiv]
  rfl

private abbrev rompelEscPred (c : ℕ) (g : List Bool → List Bool) (outLen : ℕ → ℕ) (n : ℕ)
    (z : RompelBaseInput n (outLen n)) (raw : List Bool) : Prop :=
  raw.length = rompelBaseInLen n (outLen n) ∧
    rompelBaseEvalWord g outLen n raw = rompelBaseEvalWord g outLen n z.packWord ∧
    Cslib.BitString.ofList (rompelBaseInLen n (outLen n)) raw ∉
      rompelAccessibleSet c g outLen n (rompelBaseInputEquiv n (outLen n) z)

open Classical in
private theorem rompelBase_escape_succProbability_eq (c : ℕ) (g : List Bool → List Bool)
    (outLen : ℕ → ℕ) (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ) :
    (Game.succProbability (ProbComp.eval
      (accessibleEscapeGame (rompelBaseEvalWord g outLen)
        (fun k => rompelBaseInLen k (outLen k)) (rompelAccessibleSet c g outLen) A n)) : ℝ) =
    ∑ x : BitString n, ((PMF.uniformOfFintype (BitString n)) x).toReal *
      ∑ rBits : BitString (rompelTruncWidth n),
        ((PMF.uniformOfFintype (BitString (rompelTruncWidth n))) rBits).toReal *
        ∑ s : (Fin n → BitString (outLen n)) × BitString n,
          ((PMF.uniformOfFintype ((Fin n → BitString (outLen n)) × BitString n)) s).toReal *
            ((ProbComp.eval (A n (RompelBaseInput.mk x s.1 s.2 rBits).packWord) >>= fun raw =>
              PMF.pure (decide (rompelEscPred c g outLen n ⟨x, s.1, s.2, rBits⟩ raw)))
                true).toReal := by
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, accessibleEscapeGame,
    ProbComp.eval_bind, Cslib.BitString.eval_sampleList, ProbComp.eval_pure]
  rw [uniformList_rompelBaseInLen_eq n (outLen n)]
  simp only [PMF.bind_bind, PMF.bind_map, PMF.bind_apply_toReal]
  rfl

private theorem rompelBase_inversion_succProbability_eq (c : ℕ) (g : List Bool → List Bool)
    (outLen : ℕ → ℕ) (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ)
    (hlen : ∀ w : List Bool, w.length = n → (g w).length = outLen n) :
    let gFin := wordToFinMap n (outLen n) g
    (4 * (n + 1 : ℝ) ^ c) * (Game.succProbability (ProbComp.eval
      (inversionGame g (rompelBaseInverter g outLen A) n)) : ℝ) =
    ∑ x : BitString n, ((PMF.uniformOfFintype (BitString n)) x).toReal *
      ∑ rBits : BitString (rompelTruncWidth n),
        ((PMF.uniformOfFintype (BitString (rompelTruncWidth n))) rBits).toReal *
        ∑ y : BitString (outLen n),
          (4 * (n + 1 : ℝ) ^ c) * (((PMF.uniformOfFintype (BitString n)).map gFin) y).toReal *
          ∑ s : (Fin n → BitString (outLen n)) × BitString n,
            (((PMF.uniformOfFintype ((Fin n → BitString (outLen n)) × BitString n)).map
              (adjustAffineSeed (Cslib.BitString.boundedBinaryValue n (List.ofFn rBits))
                (y + gFin x))) s).toReal *
            ((ProbComp.eval (A n (RompelBaseInput.mk x s.1 s.2 rBits).packWord) >>= fun raw =>
              PMF.pure (g (raw.take n) == List.ofFn y)) true).toReal := by
  intro gFin
  have hg_ofFn (x : BitString n) : g (List.ofFn x) = List.ofFn (gFin x) :=
    (Cslib.BitString.ofFn_ofList (hlen (List.ofFn x) List.length_ofFn)).symm
  have heval :
      ProbComp.eval (inversionGame g (rompelBaseInverter g outLen A) n) =
      ((PMF.uniformOfFintype (BitString n)).map gFin).bind fun y =>
        (PMF.uniformOfFintype (BitString n)).bind fun x =>
          (PMF.uniformOfFintype (BitString (rompelTruncWidth n))).bind fun rBits =>
            ((PMF.uniformOfFintype ((Fin n → BitString (outLen n)) × BitString n)).map
              (adjustAffineSeed (Cslib.BitString.boundedBinaryValue n (List.ofFn rBits))
                (y + gFin x))).bind fun s =>
              ProbComp.eval (A n (RompelBaseInput.mk x s.1 s.2 rBits).packWord) >>=
                fun raw => PMF.pure (g (raw.take n) == List.ofFn y) := by
    simp only [inversionGame, inversionExperiment, rompelBaseInverter, ProbComp.eval_bind,
      Cslib.BitString.eval_sampleList, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind,
      PMF.monad_bind_eq_bind, rompelSeedWidth]
    rw [uniformList_seed_eq_map n (outLen n)]
    simp only [Cslib.BitString.uniformList, PMF.bind_map, Function.comp_def, hg_ofFn,
      wordAdjustAffineSeed_eq_packAffineSeed, Cslib.BitString.ofList_ofFn,
      unpackAffineSeed_packAffineSeed, RompelBaseInput.packWord, Prod.mk.eta]
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, heval, PMF.bind_apply_toReal,
    mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_comm]
  exact sum_congr rfl fun rBits _ => sum_congr rfl fun y _ => sum_congr rfl fun s _ => by ring

open Classical in
private theorem rompelBase_escape_seed_toReal_le (c : ℕ) (g : List Bool → List Bool)
    (outLen : ℕ → ℕ) (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ)
    (hlen : ∀ w : List Bool, w.length = n → (g w).length = outLen n)
    (x : BitString n) (rBits : BitString (rompelTruncWidth n))
    (s : (Fin n → BitString (outLen n)) × BitString n) :
    let gFin := wordToFinMap n (outLen n) g
    let r := Cslib.BitString.boundedBinaryValue n (List.ofFn rBits)
    ((ProbComp.eval (A n (RompelBaseInput.mk x s.1 s.2 rBits).packWord) >>= fun raw =>
        PMF.pure (decide (rompelEscPred c g outLen n ⟨x, s.1, s.2, rBits⟩ raw))) true).toReal ≤
      ∑ y ∈ (rompelLightImages c gFin (gFin x) r)ᶜ,
        if prefixProj n r (Cslib.BitString.LinearHash.affineHash s y) =
            prefixProj n r (Cslib.BitString.LinearHash.affineHash s (gFin x)) then
          ((ProbComp.eval (A n (RompelBaseInput.mk x s.1 s.2 rBits).packWord) >>= fun raw =>
            PMF.pure (g (raw.take n) == List.ofFn y)) true).toReal
        else 0 := by
  intro gFin r
  let m := outLen n
  let pA := ProbComp.eval (A n (RompelBaseInput.mk x s.1 s.2 rBits).packWord)
  let hitPref (y : BitString m) : Prop :=
    prefixProj n r (Cslib.BitString.LinearHash.affineHash s y) =
      prefixProj n r (Cslib.BitString.LinearHash.affineHash s (gFin x))
  have hg_ofFn (x' : BitString n) : g (List.ofFn x') = List.ofFn (gFin x') :=
    (Cslib.BitString.ofFn_ofList (hlen (List.ofFn x') List.length_ofFn)).symm
  have hkey (raw : List Bool) (hesc : rompelEscPred c g outLen n ⟨x, s.1, s.2, rBits⟩ raw) :
      let y := gFin (RompelBaseInput.unpackWord n m raw).preimage
      y ∈ (rompelLightImages c gFin (gFin x) r)ᶜ ∧ hitPref y ∧ g (raw.take n) = List.ofFn y := by
    rcases hesc with ⟨hlen_raw, heval_raw, hnot_acc⟩
    let z : RompelBaseInput n m := ⟨x, s.1, s.2, rBits⟩
    let z' := RompelBaseInput.unpackWord n m raw
    have hpack' : z'.packWord = raw := RompelBaseInput.packWord_unpackWord hlen_raw
    have hhash : rompelBaseHashFin gFin z' = rompelBaseHashFin gFin z := by
      apply (rompelBaseOutputEquiv n m).injective
      rw [← wordToFinMap_rompelBaseEvalWord, ← wordToFinMap_rompelBaseEvalWord,
        wordToFinMap, wordToFinMap, ofFn_rompelBaseInputEquiv, ofFn_rompelBaseInputEquiv,
        hpack', heval_raw]
    refine ⟨mem_compl.mpr fun hlight => hnot_acc ?_,
      ((rompelBaseHashFin_eq_iff gFin z' z).mp hhash).2.2.2, ?_⟩
    · rw [rompelAccessibleSet, mem_map]
      refine ⟨z', ?_, by simp [rompelBaseInputEquiv, hpack']⟩
      have hz' : z' ∈ rompelAccessibleInputSet c gFin z :=
        mem_filter.mpr ⟨(mem_fiberSet _ _ _).mpr hhash, hlight⟩
      dsimp only [gFin, m, z] at hz' ⊢
      simpa only [(rompelBaseInputEquiv n (outLen n)).symm_apply_apply] using hz'
    · have htake : raw.take n = List.ofFn z'.preimage := by
        rw [← hpack', RompelBaseInput.packWord, List.append_assoc,
          List.take_left' (List.length_ofFn (f := z'.preimage))]
      rw [htake, hg_ofFn]
  have hbind (b : List Bool → Bool) :
      (pA >>= fun raw => PMF.pure (b raw)) true = ∑' raw, if b raw then pA raw else 0 := by
    rw [show (pA >>= _) = pA.bind _ from rfl, PMF.bind_apply]
    exact tsum_congr fun raw => by cases b raw <;> simp
  have hterm (y : BitString m) :
      (if hitPref y then
          (pA >>= fun raw => PMF.pure (g (raw.take n) == List.ofFn y)) true else 0) =
        ∑' raw, if hitPref y ∧ g (raw.take n) = List.ofFn y then pA raw else 0 := by
    split_ifs with hp
    · rw [hbind]
      exact tsum_congr fun raw => by simp only [hp, true_and, beq_iff_eq]
    · simp [hp]
  have hne_top (y : BitString m) (_ : y ∈ (rompelLightImages c gFin (gFin x) r)ᶜ) :
      (if hitPref y then
        (pA >>= fun raw => PMF.pure (g (raw.take n) == List.ofFn y)) true else 0) ≠ ⊤ := by
    split_ifs
    · exact PMF.apply_ne_top _ _
    · exact ENNReal.zero_ne_top
  refine (ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr hne_top) ?_).trans_eq ?_
  · rw [hbind, sum_congr rfl fun y _ => hterm y,
      ← Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable]
    refine Summable.tsum_le_tsum (fun raw => ?_) CompleteLattice.summable CompleteLattice.summable
    split_ifs with hesc
    · obtain ⟨hy_mem, hpref, hg_eq⟩ := hkey raw (of_decide_eq_true hesc)
      simpa [hpref, hg_eq] using single_le_sum
        (f := fun y => if hitPref y ∧ g (raw.take n) = List.ofFn y then pA raw else 0)
        (fun _ _ => zero_le) hy_mem
    · exact zero_le
  · rw [ENNReal.toReal_sum hne_top]
    exact sum_congr rfl fun y _ => by split_ifs <;> rfl

private theorem rompelBase_heavy_image_mass_ge {n m r : ℕ} (c : ℕ) (hr_le : r ≤ n)
    (gFin : BitString n → BitString m) {y₀ y : BitString m}
    (hy_not : y ∉ rompelLightImages c gFin y₀ r) :
    (1 : ℝ) ≤
      (4 * (n + 1 : ℝ) ^ c) *
        (((PMF.uniformOfFintype (BitString n)).map gFin) y).toReal * (2 : ℝ) ^ r := by
  have hy_heavy : (2 : ℝ) ^ (n - r) ≤ 4 * (n + 1 : ℝ) ^ c * (#(fiberSet gFin y) : ℝ) := by
    refine mod_cast Nat.le_of_lt ?_
    by_contra! hle
    exact hy_not (mem_insert_of_mem (mem_filter.mpr ⟨mem_univ y, by rwa [Nat.min_eq_left hr_le]⟩))
  have hcard_sub : Nat.card {a : BitString n // gFin a = y} = #(fiberSet gFin y) :=
    Nat.card_eq_fintype_card.trans (card_fiberSet_eq_fintypeCard gFin y).symm
  have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - r) * (2 : ℝ) ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hr_le]
  rw [PMF.uniformOfFintype_map_apply, hcard_sub, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast, Cslib.BitString.card, Nat.cast_pow, Nat.cast_ofNat, hpow,
    mul_div_assoc', div_mul_eq_mul_div, one_le_div (by positivity)]
  exact mul_le_mul_of_nonneg_right hy_heavy (by positivity)

/-- **`[HHRVW2020]`, Section 4.2, Claim 4.6 (pp. 21–22)**: for any fixed-output-length function `g`
(`(g w).length = outLen n` on `n`-bit inputs), any polynomial light-image threshold exponent `c`,
and any adversary `A`, escaping `rompelAccessibleSet c` with a fixed-width colliding preimage occurs
with probability at most `4 * (n + 1) ^ c` times the inversion success of
`rompelBaseInverter g outLen A`. -/
theorem rompelBase_escape_le_mul_inversion (c : ℕ) (g : List Bool → List Bool) (outLen : ℕ → ℕ)
    (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ)
    (hlen : ∀ w : List Bool, w.length = n → (g w).length = outLen n) :
    (Game.succProbability (ProbComp.eval
      (accessibleEscapeGame (rompelBaseEvalWord g outLen)
        (fun k => rompelBaseInLen k (outLen k)) (rompelAccessibleSet c g outLen) A n)) : ℝ) ≤
      (4 * (n + 1 : ℝ) ^ c) * (Game.succProbability (ProbComp.eval
        (inversionGame g (rompelBaseInverter g outLen A) n)) : ℝ) := by
  classical
  let m := outLen n
  let gFin : BitString n → BitString m := wordToFinMap n m g
  rw [rompelBase_escape_succProbability_eq c g outLen A n,
    rompelBase_inversion_succProbability_eq c g outLen A n hlen]
  refine sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
    (sum_le_sum fun rBits _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg)
    ENNReal.toReal_nonneg
  let r := Cslib.BitString.boundedBinaryValue n (List.ofFn rBits)
  let S := (Fin n → BitString m) × BitString n
  let u := PMF.uniformOfFintype S
  let invProb (s : S) (y : BitString m) : ℝ :=
    ((ProbComp.eval (A n (RompelBaseInput.mk x s.1 s.2 rBits).packWord) >>= fun raw =>
      PMF.pure (g (raw.take n) == List.ofFn y)) true).toReal
  have hr_le : r ≤ n := Cslib.BitString.boundedBinaryValue_le n _
  calc
    _ ≤ ∑ s : S, (u s).toReal * ∑ y ∈ (rompelLightImages c gFin (gFin x) r)ᶜ,
          if prefixProj n r (Cslib.BitString.LinearHash.affineHash s y) =
              prefixProj n r (Cslib.BitString.LinearHash.affineHash s (gFin x))
            then invProb s y else 0 :=
      sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
        (rompelBase_escape_seed_toReal_le c g outLen A n hlen x rBits s) ENNReal.toReal_nonneg
    _ = ∑ y ∈ (rompelLightImages c gFin (gFin x) r)ᶜ, ∑ s : S, (u s).toReal *
          (if prefixProj n r (Cslib.BitString.LinearHash.affineHash s y) =
              prefixProj n r (Cslib.BitString.LinearHash.affineHash s (gFin x))
            then invProb s y else 0) := by simp only [mul_sum]; exact sum_comm
    _ ≤ _ := by
      refine le_trans (sum_le_sum fun y hy => ?_)
        (sum_le_univ_sum_of_nonneg fun y => mul_nonneg (by positivity)
          (sum_nonneg fun s _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg))
      have hy_not : y ∉ rompelLightImages c gFin (gFin x) r := mem_compl.mp hy
      have hy_ne : y ≠ gFin x := fun h => hy_not (h ▸ self_mem_rompelLightImages c _ _ _)
      have hmass := rompelBase_heavy_image_mass_ge c hr_le gFin hy_not
      rw [mul_sum]
      refine sum_le_sum fun s _ => ?_
      split_ifs with hpref
      · have hadj := toReal_map_adjustAffineSeed_eq r hy_ne hpref
        rw [Nat.min_eq_left hr_le] at hadj
        calc (u s).toReal * invProb s y
            = 1 * ((u s).toReal * invProb s y) := (one_mul _).symm
          _ ≤ _ * ((u s).toReal * invProb s y) :=
              mul_le_mul_of_nonneg_right hmass
                (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
          _ = _ := by rw [hadj]; ring
      · rw [mul_zero]; positivity

/-! ### Sibling isolation via 3-wise independence (Claim 4.8) and the entropy gap (Claim 4.7) -/

private theorem card_prefixProj_eq_of_restrict (n m r : ℕ) (hr : r ≤ n)
    (T : Finset (BitString m)) (hT : #T ≤ 3) (y₁ : BitString m) (hy₁ : y₁ ∈ T)
    (P : (Fin n → BitString m) × BitString n → Prop) [DecidablePred P]
    (hP : ∀ s, P s ↔ ∀ u ∈ T,
      prefixProj n r (Cslib.BitString.LinearHash.affineHash s u) =
        prefixProj n r (Cslib.BitString.LinearHash.affineHash s y₁)) :
    (#(univ.filter P) : ℝ) =
      (2 : ℝ) ^ r * ((Fintype.card ((Fin n → BitString m) × BitString n) : ℝ) *
        (((2 : ℝ) ^ r) ^ #T)⁻¹) := by
  let S := (Fin n → BitString m) × BitString n
  let H (s : S) (y : BitString m) := prefixProj n r (Cslib.BitString.LinearHash.affineHash s y)
  have hpart : univ.filter P = univ.biUnion fun w : BitString (min r n) =>
      univ.filter fun s : S => T.restrict (H s) = fun _ => w := by
    ext s
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, hP s]
    exact ⟨fun hs => ⟨H s y₁, funext fun ⟨u, hu⟩ => hs u hu⟩,
      fun ⟨w, hw⟩ u hu => (congrFun hw ⟨u, hu⟩).trans (congrFun hw ⟨y₁, hy₁⟩).symm⟩
  have hcard : #(univ.filter P) =
      ∑ w : BitString (min r n), #(univ.filter fun s : S => T.restrict (H s) = fun _ => w) := by
    rw [hpart, Finset.card_biUnion]
    intro w₁ _ w₂ _ hw₁₂
    exact disjoint_left.mpr fun s hs₁ hs₂ =>
      hw₁₂ ((congrFun (mem_filter.mp hs₁).2 ⟨y₁, hy₁⟩).symm.trans
        (congrFun (mem_filter.mp hs₂).2 ⟨y₁, hy₁⟩))
  have hterm (w : BitString (min r n)) :
      (#(univ.filter fun s : S => T.restrict (H s) = fun _ => w) : ℝ) =
        (Fintype.card S : ℝ) * (((2 : ℝ) ^ r) ^ #T)⁻¹ := by
    have hd := congrArg (fun q : ℚ≥0 => (q : ℝ))
      ((isThreeWiseIndependentHash_prefixProj_affineHash n m r).dens_filter_restrict_eq hT
        (fun _ => w))
    rw [Finset.dens_eq_card_div_card] at hd
    simp only [NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_inv, NNRat.cast_pow,
      Cslib.BitString.card, Nat.min_eq_left hr, Nat.cast_pow, Nat.cast_ofNat] at hd
    exact ((div_eq_iff (mod_cast Fintype.card_ne_zero)).mp hd).trans (mul_comm _ _)
  rw [hcard, Nat.cast_sum]
  simp only [hterm, sum_const, card_univ, Cslib.BitString.card, Nat.min_eq_left hr, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  rfl

private theorem card_prefixProj_pair_eq (n m r : ℕ) (hr : r ≤ n)
    {y₁ y₂ : BitString m} (h₁₂ : y₁ ≠ y₂) :
    (#(univ.filter fun s : (Fin n → BitString m) × BitString n =>
        prefixProj n r (Cslib.BitString.LinearHash.affineHash s y₂) =
          prefixProj n r (Cslib.BitString.LinearHash.affineHash s y₁)) : ℝ) =
      (Fintype.card ((Fin n → BitString m) × BitString n) : ℝ) / (2 : ℝ) ^ r := by
  have hcard : #({y₁, y₂} : Finset (BitString m)) = 2 := card_pair h₁₂
  rw [card_prefixProj_eq_of_restrict n m r hr {y₁, y₂} (by omega) y₁ (by simp) _
    (fun s => by simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq, true_and]),
    hcard]
  field_simp

private theorem card_prefixProj_triple_eq (n m r : ℕ) (hr : r ≤ n)
    {y₁ y₂ y₃ : BitString m} (h₁₂ : y₁ ≠ y₂) (h₁₃ : y₁ ≠ y₃) (h₂₃ : y₂ ≠ y₃) :
    (#(univ.filter fun s : (Fin n → BitString m) × BitString n =>
        prefixProj n r (Cslib.BitString.LinearHash.affineHash s y₂) =
          prefixProj n r (Cslib.BitString.LinearHash.affineHash s y₁) ∧
          prefixProj n r (Cslib.BitString.LinearHash.affineHash s y₃) =
            prefixProj n r (Cslib.BitString.LinearHash.affineHash s y₁)) : ℝ) =
      (Fintype.card ((Fin n → BitString m) × BitString n) : ℝ) / ((2 : ℝ) ^ r) ^ 2 := by
  have hcard : #({y₁, y₂, y₃} : Finset (BitString m)) = 3 := by
    rw [card_insert_of_notMem (by simp [h₁₂, h₁₃]), card_pair h₂₃]
  rw [card_prefixProj_eq_of_restrict n m r hr {y₁, y₂, y₃} (by omega) y₁ (by simp) _
    (fun s => by simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq, true_and]),
    hcard]
  field_simp

private theorem card_subset_rompelBaseHashFin_fiber_eq {n m : ℕ}
    (gFin : BitString n → BitString m) (x : BitString n)
    (s : (Fin n → BitString m) × BitString n) (rBits : BitString (rompelTruncWidth n))
    (A : Finset (RompelBaseInput n m))
    (hA : A ⊆ fiberSet (rompelBaseHashFin gFin)
      (rompelBaseHashFin gFin ⟨x, s.1, s.2, rBits⟩)) :
    #A = #(univ.filter fun x' : BitString n =>
      RompelBaseInput.mk x' s.1 s.2 rBits ∈ A) := by
  have hmk {z' : RompelBaseInput n m} (hz' : z' ∈ A) :
      RompelBaseInput.mk z'.preimage s.1 s.2 rBits = z' := by
    obtain ⟨h1, h2, h3, _⟩ := (rompelBaseHashFin_eq_iff gFin z' ⟨x, s.1, s.2, rBits⟩).mp
      ((mem_fiberSet _ _ _).mp (hA hz'))
    cases z'; simp only at h1 h2 h3; subst h1 h2 h3; rfl
  exact card_bij (fun z' _ => z'.preimage)
    (fun z' hz' => mem_filter.mpr ⟨mem_univ _, (hmk hz').symm ▸ hz'⟩)
    (fun z₁ hz₁ z₂ hz₂ hpre => by rw [← hmk hz₁, ← hmk hz₂, hpre])
    (fun x' hx' => ⟨⟨x', s.1, s.2, rBits⟩, (mem_filter.mp hx').2, rfl⟩)

private theorem rompelBase_sum_otherColl_le {n m r : ℕ} (hr : r ≤ n)
    (gFin : BitString n → BitString m) {x xStar : BitString n} (hne : gFin x ≠ gFin xStar) :
    (∑ s ∈ univ.filter (fun s : (Fin n → BitString m) × BitString n =>
        prefixProj n r (Cslib.BitString.LinearHash.affineHash s (gFin xStar)) =
          prefixProj n r (Cslib.BitString.LinearHash.affineHash s (gFin x))),
      (#((univ.filter fun x' : BitString n => gFin x' ≠ gFin x ∧ gFin x' ≠ gFin xStar).filter
        fun x' => prefixProj n r (Cslib.BitString.LinearHash.affineHash s (gFin x')) =
          prefixProj n r (Cslib.BitString.LinearHash.affineHash s (gFin x))) : ℝ)) ≤
      (2 : ℝ) ^ (n - r) *
        (#(univ.filter fun s : (Fin n → BitString m) × BitString n =>
          prefixProj n r (Cslib.BitString.LinearHash.affineHash s (gFin xStar)) =
            prefixProj n r (Cslib.BitString.LinearHash.affineHash s (gFin x))) : ℝ) := by
  let S := (Fin n → BitString m) × BitString n
  let H (s : S) (y : BitString m) := prefixProj n r (Cslib.BitString.LinearHash.affineHash s y)
  let otherDom : Finset (BitString n) :=
    univ.filter fun x' => gFin x' ≠ gFin x ∧ gFin x' ≠ gFin xStar
  have hexchange : (∑ s ∈ univ.filter (fun s : S => H s (gFin xStar) = H s (gFin x)),
        #(otherDom.filter fun x' => H s (gFin x') = H s (gFin x))) =
      ∑ x' ∈ otherDom, #(univ.filter fun s : S =>
        H s (gFin xStar) = H s (gFin x) ∧ H s (gFin x') = H s (gFin x)) := by
    simp only [card_eq_sum_ones, sum_filter]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => by simp only [ite_and]; split_ifs <;> simp
  rw [← Nat.cast_sum, hexchange, Nat.cast_sum]
  have htriple (x' : BitString n) (hx' : x' ∈ otherDom) :=
    let ⟨h₁₃, h₂₃⟩ := (mem_filter.mp hx').2
    card_prefixProj_triple_eq n m r hr hne h₁₃.symm h₂₃.symm
  rw [sum_congr rfl htriple, sum_const, nsmul_eq_mul, card_prefixProj_pair_eq n m r hr hne]
  have hdom : (#otherDom : ℝ) ≤ (2 : ℝ) ^ n := by
    simpa [Cslib.BitString.card] using (Nat.cast_le (α := ℝ)).mpr (card_le_univ otherDom)
  have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - r) * (2 : ℝ) ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hr]
  calc
    (#otherDom : ℝ) * ((Fintype.card S : ℝ) / ((2 : ℝ) ^ r) ^ 2)
      ≤ (2 : ℝ) ^ n * ((Fintype.card S : ℝ) / ((2 : ℝ) ^ r) ^ 2) := by gcongr
    _ = (2 : ℝ) ^ (n - r) * ((Fintype.card S : ℝ) / (2 : ℝ) ^ r) := by
        rw [hpow]; field_simp

/-- **`[HHRVW2020]`, Section 4.2, Claim 4.8 (p. 23)**: for distinct images `gFin x ≠ gFin xStar`
with `#(fiberSet gFin (gFin x)) ≤ #(fiberSet gFin (gFin xStar)) ≤ 2 ^ (n - r)` (`r ≤ n`),
uniformly sampling an affine seed `s` and then a uniform preimage from the `F₀`-fiber of
`(x, s, rBits)` (at truncation index `r`) yields `(xStar, s, rBits)` with probability at least
`((2 : ℝ) ^ n)⁻¹ / 8`. -/
theorem rompelBase_heavy_sibling_prob_ge {n m : ℕ} (gFin : BitString n → BitString m)
    {x xStar : BitString n} {rBits : BitString (rompelTruncWidth n)}
    (hne : gFin x ≠ gFin xStar)
    (hfib_le : #(fiberSet gFin (gFin x)) ≤ #(fiberSet gFin (gFin xStar)))
    (hstar_le : #(fiberSet gFin (gFin xStar)) ≤
      2 ^ (n - Cslib.BitString.boundedBinaryValue n (List.ofFn rBits))) :
    (((2 : ℝ) ^ n)⁻¹ / 8) ≤
      ∑ s : (Fin n → BitString m) × BitString n,
        ((PMF.uniformOfFintype ((Fin n → BitString m) × BitString n)) s).toReal *
          ((if RompelBaseInput.mk xStar s.1 s.2 rBits ∈
              fiberSet (rompelBaseHashFin gFin)
                (rompelBaseHashFin gFin ⟨x, s.1, s.2, rBits⟩) then (1 : ℝ) else 0) /
            #(fiberSet (rompelBaseHashFin gFin)
              (rompelBaseHashFin gFin ⟨x, s.1, s.2, rBits⟩))) := by
  let r := Cslib.BitString.boundedBinaryValue n (List.ofFn rBits)
  have hr : r ≤ n := Cslib.BitString.boundedBinaryValue_le n _
  let S := (Fin n → BitString m) × BitString n
  let H (s : S) (y : BitString m) := prefixProj n r (Cslib.BitString.LinearHash.affineHash s y)
  let collInputs (s : S) : Finset (BitString n) :=
    univ.filter fun x' => H s (gFin x') = H s (gFin x)
  have hmem_input (s : S) (x' : BitString n) :
      RompelBaseInput.mk x' s.1 s.2 rBits ∈
        fiberSet (rompelBaseHashFin gFin) (rompelBaseHashFin gFin ⟨x, s.1, s.2, rBits⟩) ↔
      H s (gFin x') = H s (gFin x) := by
    simp only [mem_fiberSet, rompelBaseHashFin_eq_iff, RompelBaseInput.truncIndex, true_and]
    rfl
  let E : Finset S := univ.filter fun s => H s (gFin xStar) = H s (gFin x)
  let otherColl (s : S) : Finset (BitString n) :=
    (univ.filter fun x' => gFin x' ≠ gFin x ∧ gFin x' ≠ gFin xStar).filter fun x' =>
      H s (gFin x') = H s (gFin x)
  let Egood : Finset S := E.filter fun s => #(otherColl s) ≤ 2 * 2 ^ (n - r)
  let Ebad : Finset S := E.filter fun s => ¬ (#(otherColl s) ≤ 2 * 2 ^ (n - r))
  -- Markov's inequality on `E`: at least half of `s ∈ E` have `#(otherColl s) ≤ 2 * 2 ^ (n - r)`.
  have hEgood_ge : (#E : ℝ) / 2 ≤ (#Egood : ℝ) := by
    have hsum : (∑ s ∈ E, (#(otherColl s) : ℝ)) ≤ (2 : ℝ) ^ (n - r) * (#E : ℝ) :=
      rompelBase_sum_otherColl_le hr gFin hne
    have hpart : (#Egood : ℝ) + (#Ebad : ℝ) = (#E : ℝ) := by
      exact_mod_cast card_filter_add_card_filter_not (s := E)
        (p := fun s => #(otherColl s) ≤ 2 * 2 ^ (n - r))
    have hbad : 2 * (2 : ℝ) ^ (n - r) * (#Ebad : ℝ) ≤ ∑ s ∈ E, (#(otherColl s) : ℝ) := by
      rw [mul_comm _ (#Ebad : ℝ), ← nsmul_eq_mul, ← sum_const]
      refine (sum_le_sum fun s hs => ?_).trans
        (sum_le_sum_of_subset_of_nonneg (filter_subset _ E) fun _ _ _ => Nat.cast_nonneg _)
      exact_mod_cast (Nat.lt_of_not_le (mem_filter.mp hs).2).le
    have hEbad_le : 2 * (#Ebad : ℝ) ≤ (#E : ℝ) := by
      refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (n - r))
      linarith [hbad.trans hsum]
    linarith
  have hcoll_le {s : S} (hs : s ∈ Egood) : #(collInputs s) ≤ 4 * 2 ^ (n - r) := by
    have hsub : collInputs s ⊆
        (fiberSet gFin (gFin x) ∪ fiberSet gFin (gFin xStar)) ∪ otherColl s := by
      intro x' hx'
      simp only [collInputs, otherColl, mem_union, mem_fiberSet, mem_filter, mem_univ,
        true_and] at hx' ⊢
      tauto
    have := (card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
    have := (mem_filter.mp hs).2
    have : #(fiberSet gFin (gFin xStar)) ≤ 2 ^ (n - r) := hstar_le
    omega
  have hS_pos : (0 : ℝ) < Fintype.card S := mod_cast Fintype.card_pos (α := S)
  have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - r) * (2 : ℝ) ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hr]
  calc
    (((2 : ℝ) ^ n)⁻¹ / 8)
      = (Fintype.card S : ℝ)⁻¹ * ((#E : ℝ) / 2) * (4 * (2 : ℝ) ^ (n - r))⁻¹ := by
        rw [card_prefixProj_pair_eq n m r hr hne, hpow]
        dsimp only [S]
        field_simp
        ring
    _ ≤ (Fintype.card S : ℝ)⁻¹ * (#Egood : ℝ) * (4 * (2 : ℝ) ^ (n - r))⁻¹ := by gcongr
    _ = ∑ _s ∈ Egood, ((Fintype.card S : ℝ)⁻¹ * (4 * (2 : ℝ) ^ (n - r))⁻¹) := by
        rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ s ∈ Egood, _ := by
        refine sum_le_sum fun s hs => ?_
        have hmem_s := (hmem_input s xStar).mpr (mem_filter.mp (mem_filter.mp hs).1).2
        have hfib_card : #(fiberSet (rompelBaseHashFin gFin)
            (rompelBaseHashFin gFin ⟨x, s.1, s.2, rBits⟩)) = #(collInputs s) := by
          rw [card_subset_rompelBaseHashFin_fiber_eq gFin x s rBits _ Subset.rfl]
          simp only [collInputs, hmem_input s]
        simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
          hmem_s, ↓reduceIte, hfib_card, one_div]
        have hpos : (0 : ℝ) < #(collInputs s) :=
          mod_cast card_pos.mpr ⟨x, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
        exact mul_le_mul_of_nonneg_left (inv_anti₀ hpos (mod_cast hcoll_le hs)) (by positivity)
    _ ≤ _ := sum_le_univ_sum_of_nonneg fun s =>
        mul_nonneg ENNReal.toReal_nonneg (div_nonneg (by split_ifs <;> positivity) (by positivity))

private noncomputable abbrev rompelSdiffWeight {n m : ℕ} (c : ℕ)
    (gFin : BitString n → BitString m) (x xStar : BitString n)
    (s : (Fin n → BitString m) × BitString n)
    (rBits : BitString (rompelTruncWidth n)) : ℝ :=
  (if RompelBaseInput.mk xStar s.1 s.2 rBits ∈
      fiberSet (rompelBaseHashFin gFin) (rompelBaseHashFin gFin ⟨x, s.1, s.2, rBits⟩) \
        rompelAccessibleInputSet c gFin ⟨x, s.1, s.2, rBits⟩ then (1 : ℝ) else 0) /
    #(fiberSet (rompelBaseHashFin gFin) (rompelBaseHashFin gFin ⟨x, s.1, s.2, rBits⟩))

private theorem two_pow_mul_log_le_succ_pow (c n : ℕ) :
    2 ^ (c * Nat.log 2 n) ≤ (n + 1) ^ c := by
  rw [Nat.mul_comm, pow_mul]
  refine Nat.pow_le_pow_left ?_ c
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · decide
  · exact (Nat.pow_log_le_self 2 hn.ne').trans (Nat.le_succ n)

private theorem rompelBase_goodLightPair_term_ge {n m : ℕ} (c : ℕ)
    (ht : c * Nat.log 2 n ≤ n) (gFin : BitString n → BitString m)
    {x xStar : BitString n} (hne : gFin x ≠ gFin xStar)
    (hfib_le : #(fiberSet gFin (gFin x)) ≤ #(fiberSet gFin (gFin xStar)))
    (hstar_lt : #(fiberSet gFin (gFin xStar)) < 2 ^ (n - c * Nat.log 2 n)) :
    (c * Nat.log 2 n + 1 : ℝ) *
        (((2 : ℝ) ^ n)⁻¹ / (8 * (2 ^ rompelTruncWidth n : ℝ))) ≤
      ∑ rBits : BitString (rompelTruncWidth n), ((2 ^ rompelTruncWidth n : ℝ)⁻¹) *
        ∑ s : (Fin n → BitString m) × BitString n,
          ((PMF.uniformOfFintype ((Fin n → BitString m) × BitString n)) s).toReal *
            rompelSdiffWeight c gFin x xStar s rBits := by
  let t := c * Nat.log 2 n
  let k := Nat.log 2 #(fiberSet gFin (gFin xStar))
  have hfib_pos : 1 ≤ #(fiberSet gFin (gFin xStar)) := card_fiberSet_pos gFin xStar
  have hk_lt : k < n - t :=
    (Nat.log_lt_iff_lt_pow (by decide : 1 < 2) (by omega)).mpr hstar_lt
  have hpow_k_le : 2 ^ k ≤ #(fiberSet gFin (gFin xStar)) := Nat.pow_log_le_self 2 (by omega)
  have hlt_pow_succ : #(fiberSet gFin (gFin xStar)) < 2 ^ (k + 1) :=
    Nat.lt_pow_succ_log_self (by decide : 1 < 2) _
  let rOf (j : ℕ) : ℕ := n - (k + 1 + j)
  let rBitsOf (j : ℕ) : BitString (rompelTruncWidth n) :=
    Cslib.BitString.ofList (rompelTruncWidth n)
      (Cslib.BitString.binaryWord (rompelTruncWidth n) (rOf j))
  let F (rBits : BitString (rompelTruncWidth n)) : ℝ :=
    (2 ^ rompelTruncWidth n : ℝ)⁻¹ *
      ∑ s : (Fin n → BitString m) × BitString n,
        ((PMF.uniformOfFintype ((Fin n → BitString m) × BitString n)) s).toReal *
          rompelSdiffWeight c gFin x xStar s rBits
  have hbv (j : ℕ) : Cslib.BitString.boundedBinaryValue n (List.ofFn (rBitsOf j)) = rOf j := by
    have hr_le : rOf j ≤ n := Nat.sub_le _ _
    have hr_lt := lt_of_le_of_lt hr_le (lt_two_pow_rompelTruncWidth n)
    rw [Cslib.BitString.ofFn_ofList (Cslib.BitString.length_binaryWord hr_lt),
      Cslib.BitString.boundedBinaryValue_eq, Cslib.BitString.binaryValue_binaryWord,
      Nat.min_eq_right hr_le]
  have hinj : Set.InjOn rBitsOf ↑(range (t + 1)) := fun j₁ hj₁ j₂ hj₂ heq => by
    have hr_eq : rOf j₁ = rOf j₂ := by rw [← hbv j₁, ← hbv j₂, heq]
    simp only [mem_coe, mem_range] at hj₁ hj₂
    dsimp only [rOf] at hr_eq; omega
  have hterm (j : ℕ) (hj : j ∈ range (t + 1)) :
      ((2 : ℝ) ^ n)⁻¹ / (8 * (2 ^ rompelTruncWidth n : ℝ)) ≤ F (rBitsOf j) := by
    have hj_lt := mem_range.mp hj
    have hstar_le : #(fiberSet gFin (gFin xStar)) ≤
        2 ^ (n - Cslib.BitString.boundedBinaryValue n (List.ofFn (rBitsOf j))) := by
      rw [hbv j, show n - rOf j = k + 1 + j by dsimp only [rOf]; omega]
      exact hlt_pow_succ.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
    have hnot_light : gFin xStar ∉ rompelLightImages c gFin (gFin x) (rOf j) := by
      intro hmem
      rcases mem_insert.mp hmem with heq | hfilt
      · exact hne heq.symm
      · have hle4 := (mem_filter.mp hfilt).2
        rw [Nat.min_eq_left (Nat.sub_le _ _), show n - rOf j = k + 1 + j by
          dsimp only [rOf]; omega] at hle4
        have hlow : 2 ^ (k + t + 2) ≤ 4 * (n + 1) ^ c * #(fiberSet gFin (gFin xStar)) := by
          rw [show 2 ^ (k + t + 2) = 4 * 2 ^ t * 2 ^ k by ring]
          exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 (two_pow_mul_log_le_succ_pow c n)) hpow_k_le
        have hhigh : 2 ^ (k + 1 + j) < 2 ^ (k + t + 2) :=
          Nat.pow_lt_pow_right (by decide) (by omega)
        omega
    have hclaim := rompelBase_heavy_sibling_prob_ge gFin (rBits := rBitsOf j) hne hfib_le hstar_le
    rw [show ((2 : ℝ) ^ n)⁻¹ / (8 * (2 ^ rompelTruncWidth n : ℝ)) =
      (2 ^ rompelTruncWidth n : ℝ)⁻¹ * (((2 : ℝ) ^ n)⁻¹ / 8) by ring]
    refine mul_le_mul_of_nonneg_left (hclaim.trans (sum_le_sum fun s _ =>
      mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg)) (by positivity)
    have hsdiff :
        RompelBaseInput.mk xStar s.1 s.2 (rBitsOf j) ∈
          fiberSet (rompelBaseHashFin gFin) (rompelBaseHashFin gFin ⟨x, s.1, s.2, rBitsOf j⟩) \
            rompelAccessibleInputSet c gFin ⟨x, s.1, s.2, rBitsOf j⟩ ↔
        RompelBaseInput.mk xStar s.1 s.2 (rBitsOf j) ∈
          fiberSet (rompelBaseHashFin gFin) (rompelBaseHashFin gFin ⟨x, s.1, s.2, rBitsOf j⟩) := by
      refine ⟨fun h => (mem_sdiff.mp h).1, fun h => mem_sdiff.mpr ⟨h, fun hacc => hnot_light ?_⟩⟩
      simpa only [RompelBaseInput.truncIndex, hbv j] using (mem_filter.mp hacc).2
    simp only [rompelSdiffWeight, hsdiff, le_rfl]
  calc
    (c * Nat.log 2 n + 1 : ℝ) * (((2 : ℝ) ^ n)⁻¹ / (8 * (2 ^ rompelTruncWidth n : ℝ)))
      = ∑ _j ∈ range (t + 1), (((2 : ℝ) ^ n)⁻¹ / (8 * (2 ^ rompelTruncWidth n : ℝ))) := by
        rw [sum_const, card_range, nsmul_eq_mul]; push_cast [t]; ring
    _ ≤ ∑ j ∈ range (t + 1), F (rBitsOf j) := sum_le_sum hterm
    _ = ∑ rBits ∈ (range (t + 1)).image rBitsOf, F rBits := (sum_image hinj).symm
    _ ≤ ∑ rBits, F rBits := sum_le_univ_sum_of_nonneg fun rBits =>
        mul_nonneg (by positivity) (sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg
          (div_nonneg (by split_ifs <;> positivity) (by positivity)))

private theorem rompelBase_escape_density_sum_eq {n m : ℕ} (c : ℕ)
    (gFin : BitString n → BitString m) :
    (∑ z : RompelBaseInput n m, ((PMF.uniformOfFintype (RompelBaseInput n m)) z).toReal *
      ((#(fiberSet (rompelBaseHashFin gFin) (rompelBaseHashFin gFin z) \
          rompelAccessibleInputSet c gFin z) : ℝ) /
        #(fiberSet (rompelBaseHashFin gFin) (rompelBaseHashFin gFin z)))) =
    ∑ p : BitString n × BitString n, ((2 ^ n : ℝ)⁻¹) *
      ∑ rBits : BitString (rompelTruncWidth n), ((2 ^ rompelTruncWidth n : ℝ)⁻¹) *
        ∑ s : (Fin n → BitString m) × BitString n,
          ((PMF.uniformOfFintype ((Fin n → BitString m) × BitString n)) s).toReal *
            rompelSdiffWeight c gFin p.1 p.2 s rBits := by
  let S := (Fin n → BitString m) × BitString n
  have hcard_Z : (Fintype.card (RompelBaseInput n m) : ℝ) =
      (2 ^ n : ℝ) * (2 ^ rompelTruncWidth n : ℝ) * (Fintype.card S : ℝ) := by
    rw [← Fintype.card_congr (rompelTupleEquiv n m)]
    have : Fintype.card (BitString n × S × BitString (rompelTruncWidth n)) =
        2 ^ n * Fintype.card S * 2 ^ rompelTruncWidth n := by
      simp only [Fintype.card_prod, Cslib.BitString.card, mul_assoc]
    rw [this]; push_cast; ring
  conv_lhs => rw [← (rompelTupleEquiv n m).sum_comp, Fintype.sum_prod_type]
  conv_rhs => rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  conv_lhs => rw [Fintype.sum_prod_type, sum_comm]
  have step (rBits : BitString (rompelTruncWidth n)) (s : S) :
      ((PMF.uniformOfFintype (RompelBaseInput n m))
          (rompelTupleEquiv n m (x, s, rBits))).toReal *
        ((#(fiberSet (rompelBaseHashFin gFin)
            (rompelBaseHashFin gFin (rompelTupleEquiv n m (x, s, rBits))) \
            rompelAccessibleInputSet c gFin (rompelTupleEquiv n m (x, s, rBits))) : ℝ) /
          #(fiberSet (rompelBaseHashFin gFin)
            (rompelBaseHashFin gFin (rompelTupleEquiv n m (x, s, rBits))))) =
      ∑ xStar : BitString n,
        ((2 ^ n : ℝ)⁻¹) * ((2 ^ rompelTruncWidth n : ℝ)⁻¹) *
          ((PMF.uniformOfFintype S) s).toReal * rompelSdiffWeight c gFin x xStar s rBits := by
    simp only [rompelTupleEquiv, Equiv.coe_fn_mk, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, hcard_Z, rompelSdiffWeight]
    rw [card_subset_rompelBaseHashFin_fiber_eq gFin x s rBits _ sdiff_subset,
      card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_filter, sum_div, mul_sum]
    exact sum_congr rfl fun _ _ => by ring
  simp_rw [step]
  rw [sum_congr rfl fun _ _ => sum_comm, sum_comm]
  exact sum_congr rfl fun _ _ => by
    simp only [mul_sum]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

private theorem rompelBase_goodLightPairs_frac_ge {n m : ℕ} (c : ℕ)
    (ht : c * Nat.log 2 n ≤ n) (gFin : BitString n → BitString m) :
    (1 - (4 * (2 : ℝ) ^ (c * Nat.log 2 n) - 3) *
        PMF.collisionProbability ((PMF.uniformOfFintype (BitString n)).map gFin)) / 2 ≤
      (#(univ.filter fun p : BitString n × BitString n => gFin p.1 ≠ gFin p.2 ∧
          #(fiberSet gFin (gFin p.1)) ≤ #(fiberSet gFin (gFin p.2)) ∧
          #(fiberSet gFin (gFin p.2)) < 2 ^ (n - c * Nat.log 2 n)) : ℝ) /
        ((2 ^ n : ℝ) * (2 ^ n : ℝ)) := by
  let t := c * Nat.log 2 n
  let lightDom : Finset (BitString n) :=
    univ.filter fun x => #(fiberSet gFin (gFin x)) < 2 ^ (n - t)
  let goodLightPairs : Finset (BitString n × BitString n) :=
    univ.filter fun p => gFin p.1 ≠ gFin p.2 ∧
      #(fiberSet gFin (gFin p.1)) ≤ #(fiberSet gFin (gFin p.2)) ∧
      #(fiberSet gFin (gFin p.2)) < 2 ^ (n - t)
  let eqPairs : Finset (BitString n × BitString n) := univ.filter fun p => gFin p.1 = gFin p.2
  let lightNeqPairs : Finset (BitString n × BitString n) :=
    univ.filter fun p => gFin p.1 ≠ gFin p.2 ∧ p.1 ∈ lightDom ∧ p.2 ∈ lightDom
  let badNeqPairs : Finset (BitString n × BitString n) :=
    univ.filter fun p => gFin p.1 ≠ gFin p.2 ∧ ¬ (p.1 ∈ lightDom ∧ p.2 ∈ lightDom)
  have hlightNeq_le : #lightNeqPairs ≤ 2 * #goodLightPairs := by
    let swapEmb := (Equiv.prodComm (BitString n) (BitString n)).toEmbedding
    have hsub : lightNeqPairs ⊆ goodLightPairs ∪ goodLightPairs.map swapEmb := by
      intro ⟨x₁, x₂⟩ hp
      obtain ⟨hne, hx₁, hx₂⟩ := (mem_filter.mp hp).2
      rcases le_total #(fiberSet gFin (gFin x₁)) #(fiberSet gFin (gFin x₂)) with hle | hge
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hne, hle, (mem_filter.mp hx₂).2⟩)
      · exact mem_union_right _ (mem_map.mpr
          ⟨(x₂, x₁), mem_filter.mpr ⟨mem_univ _, hne.symm, hge, (mem_filter.mp hx₁).2⟩, rfl⟩)
    have := (card_le_card hsub).trans (card_union_le _ _)
    rw [card_map] at this; omega
  have hcoll_eq : PMF.collisionProbability ((PMF.uniformOfFintype (BitString n)).map gFin) =
      (#eqPairs : ℝ) / ((2 ^ n : ℝ) * (2 ^ n : ℝ)) := by
    rw [PMF.collisionProbability_map]
    simp only [PMF.uniformOfFintype_apply, Cslib.BitString.card, ENNReal.toReal_inv,
      ENNReal.toReal_pow, ENNReal.toReal_ofNat, Nat.cast_pow, Nat.cast_ofNat]
    rw [← Fintype.sum_prod_type fun p : BitString n × BitString n =>
        if gFin p.1 = gFin p.2 then ((2 : ℝ) ^ n)⁻¹ * ((2 : ℝ) ^ n)⁻¹ else 0,
      ← sum_filter, sum_const, nsmul_eq_mul]
    change (#eqPairs : ℝ) * (((2 : ℝ) ^ n)⁻¹ * ((2 : ℝ) ^ n)⁻¹) = _
    ring
  have hcover : 2 ^ n * 2 ^ n ≤ #eqPairs + #badNeqPairs + #lightNeqPairs := by
    have huniv : (univ : Finset (BitString n × BitString n)) ⊆
        eqPairs ∪ badNeqPairs ∪ lightNeqPairs := fun p _ => by
      simp only [eqPairs, badNeqPairs, lightNeqPairs, mem_union, mem_filter, mem_univ, true_and]
      tauto
    have h1 := (card_le_card huniv).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
    simpa only [card_univ, Fintype.card_prod, Cslib.BitString.card] using h1
  have hbad_bound : (#eqPairs : ℝ) + (#badNeqPairs : ℝ) ≤
      (4 * (2 : ℝ) ^ t - 3) * (#eqPairs : ℝ) := by
    rcases Nat.eq_zero_or_pos t with ht0 | ht_pos
    · have hall_eq {x : BitString n} (hx : x ∉ lightDom) (y : BitString n) : gFin y = gFin x := by
        have hle : #(univ : Finset (BitString n)) ≤ #(fiberSet gFin (gFin x)) := by
          simpa [lightDom, ht0, Cslib.BitString.card] using hx
        exact (mem_fiberSet gFin _ y).mp
          ((eq_of_subset_of_card_le (subset_univ _) hle) ▸ mem_univ y)
      have hbad_empty : badNeqPairs = ∅ :=
        eq_empty_iff_forall_notMem.mpr fun ⟨x₁, x₂⟩ hp => by
          obtain ⟨hne, hnb⟩ := (mem_filter.mp hp).2
          by_cases hx₁ : x₁ ∈ lightDom
          · exact hne (hall_eq (fun hx₂ => hnb ⟨hx₁, hx₂⟩) x₁)
          · exact hne (hall_eq hx₁ x₂).symm
      simp only [hbad_empty, card_empty, CharP.cast_eq_zero, add_zero, ht0, pow_zero]
      linarith
    · have hcard_eq : #eqPairs = ∑ x : BitString n, #(fiberSet gFin (gFin x)) := by
        simp only [eqPairs, fiberSet, card_filter, Fintype.sum_prod_type]
        exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by simp only [eq_comm]
      have hmarkov : #lightDomᶜ * 2 ^ (n - t) ≤ #eqPairs := by
        rw [← smul_eq_mul, ← sum_const]
        exact (sum_le_sum fun x hx => by
            simpa only [lightDom, mem_compl, mem_filter, mem_univ, true_and, not_lt] using hx).trans
          ((sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _).trans hcard_eq.symm.le)
      have hsub : badNeqPairs ⊆ lightDomᶜ ×ˢ univ ∪ univ ×ˢ lightDomᶜ := fun p hp => by
        simp only [badNeqPairs, mem_filter, mem_univ, true_and] at hp
        simp only [mem_union, mem_product, mem_compl, mem_univ, true_and, and_true]
        tauto
      have hbad_nat : #badNeqPairs ≤ 2 * 2 ^ t * #eqPairs := by
        have h1 := (card_le_card hsub).trans (card_union_le _ _)
        simp only [card_product, card_univ, Cslib.BitString.card, Nat.mul_comm (2 ^ n)] at h1
        calc #badNeqPairs ≤ 2 * (#lightDomᶜ * 2 ^ n) := by omega
          _ = 2 * (#lightDomᶜ * 2 ^ (n - t) * 2 ^ t) := by
              rw [mul_assoc, ← pow_add, Nat.sub_add_cancel ht]
          _ ≤ 2 * (#eqPairs * 2 ^ t) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hmarkov)
          _ = 2 * 2 ^ t * #eqPairs := by ring
      have hbad_r : (#badNeqPairs : ℝ) ≤ 2 * (2 : ℝ) ^ t * (#eqPairs : ℝ) := mod_cast hbad_nat
      have hpow2 : (2 : ℝ) ≤ (2 : ℝ) ^ t := by
        exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < 2) ht_pos
      have hcoeff : (1 + 2 * (2 : ℝ) ^ t) * (#eqPairs : ℝ) ≤
          (4 * (2 : ℝ) ^ t - 3) * (#eqPairs : ℝ) := by gcongr; linarith
      linarith
  rw [hcoll_eq, div_le_div_iff₀ (by norm_num) (by positivity)]
  have hcover_r : (2 ^ n : ℝ) * (2 ^ n : ℝ) ≤
      (#eqPairs : ℝ) + (#badNeqPairs : ℝ) + (#lightNeqPairs : ℝ) := mod_cast hcover
  have hlight_r : (#lightNeqPairs : ℝ) ≤ 2 * (#goodLightPairs : ℝ) := mod_cast hlightNeq_le
  rw [sub_mul, one_mul, mul_assoc, div_mul_cancel₀ _ (by positivity)]
  dsimp only [t] at hbad_bound ⊢
  linarith

/-- **`[HHRVW2020]`, Section 4.2, Claim 4.7 (pp. 21, 23–25)**: unconditional finite-`n` lower bound
on the entropy gap between `PMF.conditionalEntropy` of `rompelBaseHashFin gFin` and
`accessibleSetExpectation (rompelAccessibleInputSet c gFin)`. -/
theorem rompelBase_accessibleInput_le_conditionalEntropy_sub {n m : ℕ} (c : ℕ)
    (ht : c * Nat.log 2 n ≤ n) (gFin : BitString n → BitString m) :
    accessibleSetExpectation (rompelAccessibleInputSet c gFin) ≤
      PMF.conditionalEntropy
        ((PMF.uniformOfFintype (RompelBaseInput n m)).map fun z =>
          (rompelBaseHashFin gFin z, z)) -
        (c * Nat.log 2 n + 1 : ℝ) *
          (1 - (4 * (2 : ℝ) ^ (c * Nat.log 2 n) - 3) *
            PMF.collisionProbability ((PMF.uniformOfFintype (BitString n)).map gFin)) /
          (16 * (2 ^ rompelTruncWidth n : ℝ)) := by
  have hbase := conditionalEntropy_sub_accessibleSetExpectation_ge
    (rompelBaseHashFin gFin) (rompelAccessibleInputSet c gFin)
    (self_mem_rompelAccessibleInputSet c gFin) (rompelAccessibleInputSet_subset_fiber c gFin)
  let good : Finset (BitString n × BitString n) :=
    univ.filter fun p => gFin p.1 ≠ gFin p.2 ∧
      #(fiberSet gFin (gFin p.1)) ≤ #(fiberSet gFin (gFin p.2)) ∧
      #(fiberSet gFin (gFin p.2)) < 2 ^ (n - c * Nat.log 2 n)
  have hprob :
      (c * Nat.log 2 n + 1 : ℝ) *
          (1 - (4 * (2 : ℝ) ^ (c * Nat.log 2 n) - 3) *
            PMF.collisionProbability ((PMF.uniformOfFintype (BitString n)).map gFin)) /
          (16 * (2 ^ rompelTruncWidth n : ℝ)) ≤
        ∑ z : RompelBaseInput n m, ((PMF.uniformOfFintype (RompelBaseInput n m)) z).toReal *
          ((#(fiberSet (rompelBaseHashFin gFin) (rompelBaseHashFin gFin z) \
              rompelAccessibleInputSet c gFin z) : ℝ) /
            #(fiberSet (rompelBaseHashFin gFin) (rompelBaseHashFin gFin z))) := by
    rw [rompelBase_escape_density_sum_eq c gFin]
    calc
      _ = ((1 - (4 * (2 : ℝ) ^ (c * Nat.log 2 n) - 3) *
            PMF.collisionProbability ((PMF.uniformOfFintype (BitString n)).map gFin)) / 2) *
            ((c * Nat.log 2 n + 1 : ℝ) / (8 * (2 ^ rompelTruncWidth n : ℝ))) := by ring
      _ ≤ ((#good : ℝ) / ((2 ^ n : ℝ) * (2 ^ n : ℝ))) *
            ((c * Nat.log 2 n + 1 : ℝ) / (8 * (2 ^ rompelTruncWidth n : ℝ))) :=
          mul_le_mul_of_nonneg_right (rompelBase_goodLightPairs_frac_ge c ht gFin) (by positivity)
      _ = ∑ _p ∈ good, ((2 ^ n : ℝ)⁻¹ * ((c * Nat.log 2 n + 1 : ℝ) *
            (((2 : ℝ) ^ n)⁻¹ / (8 * (2 ^ rompelTruncWidth n : ℝ))))) := by
          rw [sum_const, nsmul_eq_mul]; field_simp
      _ ≤ ∑ p ∈ good, _ := sum_le_sum fun p hp => mul_le_mul_of_nonneg_left
          (let ⟨hne, hfib, hstar⟩ := (mem_filter.mp hp).2
           rompelBase_goodLightPair_term_ge c ht gFin hne hfib hstar) (by positivity)
      _ ≤ _ := sum_le_univ_sum_of_nonneg fun _ => mul_nonneg (by positivity)
          (sum_nonneg fun _ _ => mul_nonneg (by positivity)
            (sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg
              (div_nonneg (by split_ifs <;> positivity) (by positivity))))
  linarith

/-- Bit-string transport of `rompelBase_accessibleInput_le_conditionalEntropy_sub` (`[HHRVW2020]`,
Section 4.2, Claim 4.7, pp. 21, 23–25): when `c * Nat.log 2 n ≤ n` and the weighted output collision
probability `(4 * 2 ^ (c * Nat.log 2 n) - 3) * collisionProbability` of `g` on `n`-bit inputs is at
most `1 / 2`, the entropy gap on `BitString (rompelBaseInLen n (outLen n))` is at least
`(c * Nat.log 2 n + 1) / (64 * (n + 1))`. -/
theorem rompelBase_accessible_le_conditionalEntropy_sub (c : ℕ) (g : List Bool → List Bool)
    (outLen : ℕ → ℕ) (n : ℕ) (ht : c * Nat.log 2 n ≤ n)
    (hlen : ∀ w : List Bool, w.length = n → (g w).length = outLen n)
    (hcoll : (4 * (2 : ℝ) ^ (c * Nat.log 2 n) - 3) *
      PMF.collisionProbability ((Cslib.BitString.uniformList n).map g) ≤ 1 / 2) :
    accessibleSetExpectation (rompelAccessibleSet c g outLen n) ≤
      PMF.conditionalEntropy
        ((PMF.uniformOfFintype (BitString (rompelBaseInLen n (outLen n)))).map fun b =>
          (wordToFinMap (rompelBaseInLen n (outLen n)) (rompelBaseOutLen n (outLen n))
            (rompelBaseEvalWord g outLen n) b, b)) -
        (c * Nat.log 2 n + 1 : ℝ) / (64 * (n + 1 : ℝ)) := by
  let m := outLen n
  let gFin : BitString n → BitString m := wordToFinMap n m g
  let eIn := rompelBaseInputEquiv n m
  let eOut := rompelBaseOutputEquiv n m
  have hacc : accessibleSetExpectation (rompelAccessibleSet c g outLen n) =
      accessibleSetExpectation (rompelAccessibleInputSet c gFin) := by
    rw [accessibleSetExpectation, accessibleSetExpectation, ← eIn.sum_comp]
    refine sum_congr rfl fun z _ => ?_
    simp [PMF.uniformOfFintype_apply, Fintype.card_congr eIn, rompelAccessibleSet, eIn, gFin, m]
  have hjoint :
      ((PMF.uniformOfFintype (BitString (rompelBaseInLen n m))).map fun b =>
        (wordToFinMap (rompelBaseInLen n m) (rompelBaseOutLen n m)
          (rompelBaseEvalWord g outLen n) b, b)) =
      ((PMF.uniformOfFintype (RompelBaseInput n m)).map fun z =>
        (rompelBaseHashFin gFin z, z)).map (Equiv.prodCongr eOut eIn) := by
    rw [← PMF.uniformOfFintype_map_equiv eIn, PMF.map_comp, PMF.map_comp]
    exact congrArg _ (funext fun z => by
      simp [eIn, eOut, gFin, m, wordToFinMap_rompelBaseEvalWord])
  have hcond :
      PMF.conditionalEntropy
        ((PMF.uniformOfFintype (BitString (rompelBaseInLen n m))).map fun b =>
          (wordToFinMap (rompelBaseInLen n m) (rompelBaseOutLen n m)
            (rompelBaseEvalWord g outLen n) b, b)) =
      PMF.conditionalEntropy
        ((PMF.uniformOfFintype (RompelBaseInput n m)).map fun z =>
          (rompelBaseHashFin gFin z, z)) := by
    rw [PMF.conditionalEntropy, PMF.conditionalEntropy, hjoint,
      PMF.entropy_map_of_injective _ (Equiv.prodCongr eOut eIn).injective,
      show (((PMF.uniformOfFintype _).map fun z => (rompelBaseHashFin gFin z, z)).map
          (Equiv.prodCongr eOut eIn)).map Prod.fst =
        (((PMF.uniformOfFintype _).map fun z => (rompelBaseHashFin gFin z, z)).map Prod.fst).map
          eOut by simp only [PMF.map_comp]; rfl,
      PMF.entropy_map_of_injective _ eOut.injective]
  have hcoll_fin : (4 * (2 : ℝ) ^ (c * Nat.log 2 n) - 3) *
      PMF.collisionProbability ((PMF.uniformOfFintype (BitString n)).map gFin) ≤ 1 / 2 := by
    have hmap : (Cslib.BitString.uniformList n).map g =
        ((PMF.uniformOfFintype (BitString n)).map gFin).map List.ofFn := by
      rw [Cslib.BitString.uniformList, PMF.map_comp, PMF.map_comp]
      exact congrArg (PMF.uniformOfFintype _).map (funext fun x =>
        (Cslib.BitString.ofFn_ofList (hlen (List.ofFn x) List.length_ofFn)).symm)
    rwa [hmap, PMF.collisionProbability_map_of_injective _ _ List.ofFn_injective] at hcoll
  have htrunc : (2 ^ rompelTruncWidth n : ℝ) ≤ 2 * (n + 1 : ℝ) :=
    mod_cast two_pow_rompelTruncWidth_le n
  have hfrac : (c * Nat.log 2 n + 1 : ℝ) / (64 * (n + 1 : ℝ)) ≤
      (c * Nat.log 2 n + 1 : ℝ) *
        (1 - (4 * (2 : ℝ) ^ (c * Nat.log 2 n) - 3) *
          PMF.collisionProbability ((PMF.uniformOfFintype (BitString n)).map gFin)) /
        (16 * (2 ^ rompelTruncWidth n : ℝ)) := by
    calc
      (c * Nat.log 2 n + 1 : ℝ) / (64 * (n + 1 : ℝ))
        = (c * Nat.log 2 n + 1 : ℝ) * (1 / 2) / (16 * (2 * (n + 1 : ℝ))) := by field_simp; ring
      _ ≤ (c * Nat.log 2 n + 1 : ℝ) * (1 / 2) / (16 * (2 ^ rompelTruncWidth n : ℝ)) := by gcongr
      _ ≤ _ := by gcongr; linarith
  have hgap := rompelBase_accessibleInput_le_conditionalEntropy_sub c ht gFin
  rw [hacc, hcond]
  linarith

/-! ### Theorem 4.5: logarithmic entropy gap from any one-way function -/

theorem inv_rompelGapDenom_le (c n : ℕ) :
    1 / (rompelGapDenom c n : ℝ) ≤ (c * Nat.log 2 n + 1 : ℝ) / (64 * (n + 1 : ℝ)) := by
  have hprod : (64 * (n + 1 : ℝ)) ≤ (rompelGapDenom c n : ℝ) * (c * Nat.log 2 n + 1 : ℝ) := by
    have h := (Nat.lt_mul_div_succ (64 * (n + 1)) (Nat.succ_pos (c * Nat.log 2 n))).le
    rw [Nat.mul_comm (c * Nat.log 2 n + 1)] at h
    exact_mod_cast h
  rw [div_le_div_iff₀ (mod_cast rompelGapDenom_pos c n) (by positivity)]
  linarith

theorem logGap_le_inv_rompelGapDenom {d : ℝ} (hd : 0 < d) {c n : ℕ}
    (hc : 256 * d ≤ c) (hn : 2 ≤ n) (ht : c * Nat.log 2 n ≤ n) :
    d * Real.logb 2 n / n ≤ 1 / (rompelGapDenom c n : ℝ) := by
  have hlog1 : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le Nat.one_lt_two (by simpa using hn)
  have hlogb : Real.logb 2 n ≤ 2 * (Nat.log 2 n : ℝ) := by
    have hpow_le : (n : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 n + 1) := by
      exact_mod_cast (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le
    have h1 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hpow_le
    rw [Real.logb_two_pow] at h1
    have : (Nat.log 2 n : ℝ) + 1 ≤ 2 * (Nat.log 2 n : ℝ) := by
      exact_mod_cast (show Nat.log 2 n + 1 ≤ 2 * Nat.log 2 n by omega)
    push_cast at h1; linarith
  have hprod_nat : rompelGapDenom c n * (c * Nat.log 2 n) ≤ 128 * n := by
    let b := c * Nat.log 2 n + 1
    calc
      rompelGapDenom c n * (c * Nat.log 2 n)
        ≤ rompelGapDenom c n * b := Nat.mul_le_mul_left _ (Nat.le_succ _)
      _ = 64 * (n + 1) / b * b + b := by dsimp only [rompelGapDenom, b]; ring
      _ ≤ 64 * (n + 1) + (n + 1) := Nat.add_le_add (Nat.div_mul_le_self _ _) (by omega)
      _ ≤ 128 * n := by omega
  have hprod : (rompelGapDenom c n : ℝ) * ((c : ℝ) * (Nat.log 2 n : ℝ)) ≤ 128 * n :=
    mod_cast hprod_nat
  have hdmul : 128 * (d * Real.logb 2 n) ≤ (c : ℝ) * (Nat.log 2 n : ℝ) :=
    calc
      128 * (d * Real.logb 2 n) ≤ 128 * (d * (2 * (Nat.log 2 n : ℝ))) := by gcongr
      _ = (256 * d) * (Nat.log 2 n : ℝ) := by ring
      _ ≤ (c : ℝ) * (Nat.log 2 n : ℝ) := by gcongr
  rw [div_le_div_iff₀ (by positivity) (mod_cast rompelGapDenom_pos c n)]
  have hmul := mul_le_mul_of_nonneg_left hdmul (Nat.cast_nonneg (rompelGapDenom c n))
  linarith

private theorem mul_log_le_self_of_four_mul_sq_le (c n : ℕ) (hn : 4 * c * c ≤ n) :
    c * Nat.log 2 n ≤ n := by
  have hsq := Nat.mul_log_le_add_sq Nat.one_lt_two (2 * c) n
  have hmul : (2 * c) * Nat.log 2 n = 2 * (c * Nat.log 2 n) := by ring
  have h4 : (2 * c) * (2 * c) = 4 * c * c := by ring
  omega

/-- Construct an `InaccessibleEntropyFamily` at polynomial light-image threshold exponent `c` from
any fixed-output-length `OneWay` function `g`. Note that `inLen`, `outLen`, and `evalWord` are
independent of `c`. -/
def OneWay.rompelFamily {g : List Bool → List Bool} {outLen : ℕ → ℕ}
    (c : ℕ) (hg : OneWay g) (hlen : ∀ w : List Bool, (g w).length = outLen w.length)
    (houtLen : ComputableInPolyTime outLen encUnary encUnary) :
    InaccessibleEntropyFamily where
  inLen := fun n => rompelBaseInLen n (outLen n)
  outLen := fun n => rompelBaseOutLen n (outLen n)
  denom := rompelGapDenom c
  evalWord := rompelBaseEvalWord g outLen
  accSet := rompelAccessibleSet c g outLen
  polyTime_inLen := by unfold rompelBaseInLen rompelSeedWidth; fun_prop
  polyTime_outLen := by unfold rompelBaseOutLen rompelSeedWidth; fun_prop
  polyTime_denom := computableInPolyTime_rompelGapDenom c
  denom_pos := rompelGapDenom_pos c
  polyTime_evalWord := computableInPolyTime_rompelBaseEvalWord hg.polyTime houtLen
  length_evalWord := fun n z _ => length_rompelBaseEvalWord g outLen n z
  self_mem_accSet := self_mem_rompelAccessibleSet c g outLen
  accSet_subset_fiber := rompelAccessibleSet_subset_fiber c g outLen
  eventually_entropy_gap := by
    have hcoll_ev := hg.output_collision_negligible.eventually_le_inv_polynomial
      (p := fun n => 8 * (n + 1) ^ c) (by fun_prop) (fun _ => by positivity)
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hcoll_ev
    refine ⟨max N₀ (4 * c * c), fun n hn => ?_⟩
    have ht : c * Nat.log 2 n ≤ n :=
      mul_log_le_self_of_four_mul_sq_le c n (le_trans (le_max_right _ _) hn)
    have hc_nn := hN₀ n (le_trans (le_max_left _ _) hn)
    have hnonneg := PMF.collisionProbability_nonneg ((Cslib.BitString.uniformList n).map g)
    rw [Real.coe_toNNReal _ hnonneg] at hc_nn
    have hpow_le : (2 : ℝ) ^ (c * Nat.log 2 n) ≤ (n + 1 : ℝ) ^ c :=
      mod_cast two_pow_mul_log_le_succ_pow c n
    have hc : (4 * (2 : ℝ) ^ (c * Nat.log 2 n) - 3) *
        PMF.collisionProbability ((Cslib.BitString.uniformList n).map g) ≤ 1 / 2 := by
      rcases le_or_gt (4 * (2 : ℝ) ^ (c * Nat.log 2 n) - 3) 0 with hneg | _
      · exact (mul_nonpos_of_nonpos_of_nonneg hneg hnonneg).trans (by norm_num)
      · calc
          _ ≤ (4 * (n + 1 : ℝ) ^ c) * (1 / (8 * (n + 1 : ℝ) ^ c)) :=
            mul_le_mul (by linarith) (by exact_mod_cast hc_nn) hnonneg (by positivity)
          _ = 1 / 2 := by field_simp; ring
    have hgap := rompelBase_accessible_le_conditionalEntropy_sub c g outLen n ht
      (fun w hw => hw ▸ hlen w) hc
    exact hgap.trans (sub_le_sub_left (inv_rompelGapDenom_le c n) _)
  escape_negligible := fun A hA => by
    have hinv_ppt := isPPT_rompelBaseInverter hg.polyTime houtLen hA
    have hinv_neg := (hg.inversion_negligible _ hinv_ppt).polynomiallyBounded_mul
      (p := fun n => 4 * (n + 1) ^ c) (by fun_prop)
    refine negligible_of_le hinv_neg fun n => ?_
    exact_mod_cast rompelBase_escape_le_mul_inversion c g outLen A n (fun w hw => hw ▸ hlen w)

/-- **`[HHRVW2020]`, Section 4.2, Theorem 4.5 (p. 21)** for the concrete family
`rompelBaseEvalWord g outLen`. Take a uniform `OneWay` function `g` with output length
`outLen n` on `n`-bit inputs, a constant `d > 0`, and the light-image threshold exponent
`c = Nat.ceil (256 * d) + 1`. The accessible-set family `rompelAccessibleSet c g outLen` then has
average max-entropy eventually at most `conditionalEntropy - d * Real.logb 2 n / n`, and every
uniform strict-PPT adversary escapes it with negligible probability.

The function differs from the source's $F(x, g, i) = (g(f(x))_{1, \dots, i}, g, i)$ in three
ways:
* The hash is the affine family `affineHash` with an `n * outLen n + n`-bit seed, so the input
  width is `rompelBaseInLen n (outLen n) = n + (n * outLen n + n) + (Nat.log 2 n + 1)`. The source
  instead gets an `O(n)` width, using a family with `O(n)`-bit descriptions (Theorem 5.2, p. 26).
* The prefix length is `min r n` for a uniform `(Nat.log 2 n + 1)`-bit `r`, instead of uniform
  `i ∈ [n]`.
* `g` has a fixed output length `outLen n` rather than being length-preserving. -/
theorem OneWay.rompelBase_logGap {g : List Bool → List Bool} {outLen : ℕ → ℕ}
    (hg : OneWay g) (hlen : ∀ w : List Bool, (g w).length = outLen w.length)
    (houtLen : ComputableInPolyTime outLen encUnary encUnary) {d : ℝ} (hd : 0 < d) :
    let c := Nat.ceil (256 * d) + 1
    (∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      accessibleSetExpectation (rompelAccessibleSet c g outLen n) ≤
        PMF.conditionalEntropy
          ((PMF.uniformOfFintype (BitString (rompelBaseInLen n (outLen n)))).map fun b =>
            (wordToFinMap (rompelBaseInLen n (outLen n)) (rompelBaseOutLen n (outLen n))
              (rompelBaseEvalWord g outLen n) b, b)) -
          d * Real.logb 2 n / n) ∧
    (∀ A : ℕ → List Bool → ProbComp (List Bool),
      Probability.IsPPT encBits A →
        Negligible (fun n =>
          Game.succProbability (ProbComp.eval
            (accessibleEscapeGame (rompelBaseEvalWord g outLen)
              (fun k => rompelBaseInLen k (outLen k))
              (rompelAccessibleSet c g outLen) A n)))) := by
  intro c
  let F := hg.rompelFamily c hlen houtLen
  obtain ⟨N₀, hN₀⟩ := F.eventually_entropy_gap
  have hc : 256 * d ≤ (c : ℝ) := (Nat.le_ceil _).trans (by push_cast [c]; linarith)
  refine ⟨⟨max N₀ (max 2 (4 * c * c)), fun n hn => ?_⟩, F.escape_negligible⟩
  have hn_r := le_trans (le_max_right _ _) hn
  have ht := mul_log_le_self_of_four_mul_sq_le c n (le_trans (le_max_right _ _) hn_r)
  exact (hN₀ n (le_trans (le_max_left _ _) hn)).trans
    (sub_le_sub_left (logGap_le_inv_rompelGapDenom hd hc (le_trans (le_max_left _ _) hn_r) ht) _)

/-- `OneWay.rompelBase_logGap` applied to an arbitrary uniform `OneWay` function `f`, after
`OneWay.exists_fixedOutputLength` normalizes its output length. The result is a single uniform
polynomial-time fixed-width function family `(inLen, outLen, evalWord)`. For every constant
`d > 0`, it has a family of fiber-contained accessible preimage sets with an eventual
`d * Real.logb 2 n / n` entropy gap against all uniform strict-PPT adversaries.

The conclusion does not bound the input width `inLen n`, so its gap, stated in the security
parameter `n`, is not the quantitative content of Theorem 4.5. That content is
`OneWay.rompelBase_logGap`, whose statement names the width
`n + (n * m(n) + n) + (Nat.log 2 n + 1)` for the normalized output length `m(n)`. That length is
internal to `OneWay.exists_fixedOutputLength`, so this statement cannot name the width. -/
theorem OneWay.exists_rompelBase_logGap {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ (inLen outLen : ℕ → ℕ) (evalWord : ℕ → List Bool → List Bool),
      ComputableInPolyTime inLen encUnary encUnary ∧
      ComputableInPolyTime outLen encUnary encUnary ∧
      ComputableInPolyTime (fun p : ℕ × List Bool => evalWord p.1 p.2)
        (encPair encUnary encBits) encBits ∧
      (∀ n z, z.length = inLen n → (evalWord n z).length = outLen n) ∧
      ∀ d : ℝ, 0 < d →
        ∃ accSet : (n : ℕ) → BitString (inLen n) → Finset (BitString (inLen n)),
          (∀ n z, z ∈ accSet n z) ∧
          (∀ n z, accSet n z ⊆
            fiberSet (wordToFinMap (inLen n) (outLen n) (evalWord n))
              (wordToFinMap (inLen n) (outLen n) (evalWord n) z)) ∧
          (∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
            accessibleSetExpectation (accSet n) ≤
              PMF.conditionalEntropy
                ((PMF.uniformOfFintype (BitString (inLen n))).map fun z =>
                  (wordToFinMap (inLen n) (outLen n) (evalWord n) z, z)) -
                d * Real.logb 2 n / n) ∧
          (∀ A : ℕ → List Bool → ProbComp (List Bool),
            Probability.IsPPT encBits A →
              Negligible (fun n =>
                Game.succProbability (ProbComp.eval
                  (accessibleEscapeGame evalWord inLen accSet A n)))) := by
  obtain ⟨g, outLen, hg, hlen, houtLen⟩ := hf.exists_fixedOutputLength
  let F₀ := hg.rompelFamily 0 hlen houtLen
  refine ⟨F₀.inLen, F₀.outLen, F₀.evalWord, F₀.polyTime_inLen, F₀.polyTime_outLen,
    F₀.polyTime_evalWord, F₀.length_evalWord, fun d hd => ?_⟩
  let c := Nat.ceil (256 * d) + 1
  obtain ⟨hgap, hesc⟩ := hg.rompelBase_logGap hlen houtLen hd
  exact ⟨rompelAccessibleSet c g outLen, self_mem_rompelAccessibleSet c g outLen,
    rompelAccessibleSet_subset_fiber c g outLen, hgap, hesc⟩

/-- Every uniform `OneWay` function yields a uniform polynomial-time `InaccessibleEntropyFamily`:
`OneWay.rompelFamily` for its fixed-output-length normalization. -/
theorem OneWay.exists_inaccessibleEntropyFamily {f : List Bool → List Bool} (hf : OneWay f) :
    Nonempty InaccessibleEntropyFamily :=
  let ⟨_, _, hg, hlen, houtLen⟩ := hf.exists_fixedOutputLength
  ⟨hg.rompelFamily 0 hlen houtLen⟩

end Cslib.Crypto
