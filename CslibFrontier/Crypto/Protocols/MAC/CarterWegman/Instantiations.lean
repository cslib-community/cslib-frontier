/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.LinearHash
public import CslibFrontier.Crypto.Protocols.MAC.CarterWegman.RandomNonce
public import CslibFrontier.Probability.BitString.LinearHash
public import CslibFrontier.Probability.BitString.SubsetSum
public import CslibFrontier.Probability.HashFamily.Polynomial
public import CslibFrontier.Probability.PairwiseIndependentHash.Universal
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Tactic.Negligible

/-!
# Concrete hash instantiations of Carter–Wegman MACs

This module instantiates the one-time, issued-counter, stateful nonce-based, and randomized-nonce
Carter–Wegman MAC theorems with four Δ-universal hash families:

1. **Polynomial hashing (`xpolyHash`)** over a finite field `F` on messages of length at most `ℓ`
   ([BonehShoup2023], Section 7.4.1), with difference-collision bound `(ℓ + 1) / |F|`.
2. **Boolean-matrix linear hashing (`BitString.LinearHash.hash` and executable
   `BitString.LinearHash.wordHash`)**, with bound `2⁻ᵐ` (`isDeltaUniversalHash_linearHashWordHash`).
   Because `BitString.LinearHash.wordHash` is a `2⁻ⁿ`-DUF (hence a statistical and computational
   DUF, [BonehShoup2023], Definition 7.5, p. 269), the concrete computational schemes
   `linearHashNonceMAC` (`NonceMACScheme`) and `linearHashRandomMAC` (`MACScheme`) satisfy
   `SUFCMA`, `EUFCMA`, `CounterSUFCMA`, and `OneTimeEUFCMA` under `PseudorandomFunction family`
   alone, realizing [BonehShoup2023], Theorems 7.10 and 7.9 for this hash family.
3. **Subset-sum hashing (`BitString.SubsetSum.hash`)** into a finite additive abelian group `G`,
   with bound `1 / |G|`.
4. **Pairwise independent hash families (`IsPairwiseIndependentHash`)**, with bound `1 / |Y|`.

## Main definitions

* `Cslib.Crypto.Protocols.CarterWegman.linearHashNonceMAC`: computational nonce-based Carter–Wegman
  `NonceMACScheme` from `BitString.LinearHash.wordHash` and a PRF family `family`.
* `Cslib.Crypto.Protocols.CarterWegman.linearHashRandomMAC`: computational randomized Carter–Wegman
  `MACScheme` from `BitString.LinearHash.wordHash` and a PRF family `family`.

## Main results

* `Cslib.Crypto.Protocols.CarterWegman.oneTimeGame_xpolyHash_le`,
  `Cslib.Crypto.Protocols.CarterWegman.counterGame_xpolyHash_le`,
  `Cslib.Crypto.Protocols.CarterWegman.counterStrongGame_xpolyHash_le`,
  `Cslib.Crypto.Protocols.CarterWegman.nonceStrongGame_xpolyHash_le`,
  `Cslib.Crypto.Protocols.CarterWegman.nonceGame_xpolyHash_le`,
  `Cslib.Crypto.Protocols.CarterWegman.randomNonceStrongGame_xpolyHash_le`: polynomial-hash
  Carter–Wegman bounds.
* `Cslib.Crypto.Protocols.CarterWegman.oneTimeGame_linearHash_le`,
  `Cslib.Crypto.Protocols.CarterWegman.counterGame_linearHash_le`,
  `Cslib.Crypto.Protocols.CarterWegman.counterStrongGame_linearHash_le`,
  `Cslib.Crypto.Protocols.CarterWegman.nonceStrongGame_linearHash_le`,
  `Cslib.Crypto.Protocols.CarterWegman.nonceGame_linearHash_le`,
  `Cslib.Crypto.Protocols.CarterWegman.randomNonceStrongGame_linearHash_le`: Boolean-matrix
  linear-hash Carter–Wegman bounds.
* `Cslib.Crypto.Protocols.CarterWegman.isPPTOn_linearHashSeed`,
  `Cslib.Crypto.Protocols.CarterWegman.computableInPolyTime_linearHashWordHash`,
  `Cslib.Crypto.Protocols.CarterWegman.isDeltaUniversalHash_linearHashWordHash`,
  `Cslib.Crypto.Protocols.CarterWegman.sufCmaGame_linearHashNonceMAC_toReal_le`,
  `Cslib.Crypto.PseudorandomFunction.sufCma_linearHashNonceMAC`,
  `Cslib.Crypto.PseudorandomFunction.eufCma_linearHashNonceMAC`,
  `Cslib.Crypto.PseudorandomFunction.counterSufCma_linearHashNonceMAC`,
  `Cslib.Crypto.Protocols.CarterWegman.sufCmaGame_linearHashRandomMAC_toReal_le`,
  `Cslib.Crypto.PseudorandomFunction.sufCma_linearHashRandomMAC`,
  `Cslib.Crypto.PseudorandomFunction.eufCma_linearHashRandomMAC`,
  `Cslib.Crypto.PseudorandomFunction.oneTimeEUFCMA_linearHashRandomMAC`: computational
  linear-hash Carter–Wegman certificates, quantitative bounds, and asymptotic security instances of
  Boneh–Shoup Theorems 7.10 and 7.9.
* `Cslib.Crypto.Protocols.CarterWegman.oneTimeGame_subsetSum_le`,
  `Cslib.Crypto.Protocols.CarterWegman.counterGame_subsetSum_le`,
  `Cslib.Crypto.Protocols.CarterWegman.nonceStrongGame_subsetSum_le`: subset-sum Carter–Wegman
  bounds.
* `Cslib.Crypto.Protocols.CarterWegman.oneTimeGame_of_isPairwiseIndependentHash_le`,
  `Cslib.Crypto.Protocols.CarterWegman.counterGame_of_isPairwiseIndependentHash_le`,
  `Cslib.Crypto.Protocols.CarterWegman.nonceStrongGame_of_isPairwiseIndependentHash_le`:
  pairwise-independent Carter–Wegman bounds.

## References

* [M. N. Wegman, J. L. Carter, *New Hash Functions and Their Use in Authentication and Set
  Equality*][WegmanCarter1981]
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 7.4–7.6.
-/

public section

namespace Cslib.Crypto.Protocols.CarterWegman

open Cslib.Probability Cslib.Probability.PMF Turing.MultiTapeTM
open scoped NNReal ENNReal

section Instantiations

/-- **Polynomial Carter–Wegman one-time MAC (`xpolyHash`)** ([BonehShoup2023], Section 7.4.1):
over a finite field `F`, authenticating messages of length at most `ℓ` via `xpolyHash` has
adaptive one-time EUF-CMA (and SUF-CMA) forgery probability at most `(ℓ + 1) / |F|`. -/
theorem oneTimeGame_xpolyHash_le {F : Type} [Field F] [Fintype F] [DecidableEq F] (ℓ : ℕ)
    (forger : OneTimeForger {m : List F // m.length ≤ ℓ} F) :
    oneTimeGame (PMF.uniformOfFintype F)
      (fun k (m : {m : List F // m.length ≤ ℓ}) => xpolyHash k m) forger true ≤
      (ℓ + 1) / Fintype.card F :=
  oneTimeGame_le (isDeltaUniversalHash_xpolyHash ℓ) forger

/-- **Polynomial Carter–Wegman multi-query issued-counter MAC (`xpolyHash`)**:
authenticating messages of length at most `ℓ` via `xpolyHash` with fresh pads per query has
adaptive multi-query issued-counter EUF-CMA forgery probability at most `(ℓ + 1) / |F|`. -/
theorem counterGame_xpolyHash_le {F : Type} [Field F] [Fintype F] [DecidableEq F] (ℓ : ℕ)
    (forger : CounterForger {m : List F // m.length ≤ ℓ} F) :
    counterGame (PMF.uniformOfFintype F)
      (fun k (m : {m : List F // m.length ≤ ℓ}) => xpolyHash k m) forger true ≤
      (ℓ + 1) / Fintype.card F :=
  counterGame_le (isDeltaUniversalHash_xpolyHash ℓ) forger

/-- **Polynomial Carter–Wegman multi-query issued-slot strong unforgeability (`xpolyHash`)**. -/
theorem counterStrongGame_xpolyHash_le {F : Type} [Field F] [Fintype F] [DecidableEq F] (ℓ : ℕ)
    (forger : CounterForger {m : List F // m.length ≤ ℓ} F) :
    counterStrongGame (PMF.uniformOfFintype F)
      (fun k (m : {m : List F // m.length ≤ ℓ}) => xpolyHash k m) forger true ≤
      (ℓ + 1) / Fintype.card F :=
  counterStrongGame_le (isDeltaUniversalHash_xpolyHash ℓ) forger

/-- **Boolean-matrix Carter–Wegman one-time MAC (`BitString.LinearHash.hash`)**:
hashing `n`-bit messages to `m`-bit tags with a uniform Boolean matrix has adaptive one-time
forgery probability at most `2⁻ᵐ`. -/
theorem oneTimeGame_linearHash_le (n m : ℕ)
    (forger : OneTimeForger (BitString n) (BitString m)) :
    oneTimeGame (PMF.uniformOfFintype (Fin m → BitString n))
      BitString.LinearHash.hash forger true ≤ ((2 : ℝ≥0∞) ^ m)⁻¹ := by
  simpa only [BitString.card, Nat.cast_pow, Nat.cast_ofNat] using
    oneTimeGame_le (BitString.LinearHash.isDeltaUniversalHash n m) forger

/-- **Boolean-matrix Carter–Wegman multi-query issued-counter MAC (`BitString.LinearHash.hash`)**:
adaptive multi-query issued-counter EUF-CMA forgery probability is at most `2⁻ᵐ`. -/
theorem counterGame_linearHash_le (n m : ℕ)
    (forger : CounterForger (BitString n) (BitString m)) :
    counterGame (PMF.uniformOfFintype (Fin m → BitString n))
      BitString.LinearHash.hash forger true ≤ ((2 : ℝ≥0∞) ^ m)⁻¹ := by
  simpa only [BitString.card, Nat.cast_pow, Nat.cast_ofNat] using
    counterGame_le (BitString.LinearHash.isDeltaUniversalHash n m) forger

/-- **Boolean-matrix Carter–Wegman multi-query issued-slot strong unforgeability
(`BitString.LinearHash.hash`)**. -/
theorem counterStrongGame_linearHash_le (n m : ℕ)
    (forger : CounterForger (BitString n) (BitString m)) :
    counterStrongGame (PMF.uniformOfFintype (Fin m → BitString n))
      BitString.LinearHash.hash forger true ≤ ((2 : ℝ≥0∞) ^ m)⁻¹ := by
  simpa only [BitString.card, Nat.cast_pow, Nat.cast_ofNat] using
    counterStrongGame_le (BitString.LinearHash.isDeltaUniversalHash n m) forger

/-- **Subset-sum Carter–Wegman one-time MAC (`BitString.SubsetSum.hash`)**:
hashing binary words `ι → Bool` into a finite additive abelian group `G` via uniform subset-sum
weights has adaptive one-time forgery probability at most `1 / |G|`. -/
theorem oneTimeGame_subsetSum_le {ι G : Type} [Fintype ι] [DecidableEq ι]
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (forger : OneTimeForger (ι → Bool) G) :
    oneTimeGame (PMF.uniformOfFintype (ι → G)) BitString.SubsetSum.hash forger true ≤
      (Fintype.card G : ℝ≥0∞)⁻¹ :=
  oneTimeGame_le BitString.SubsetSum.isDeltaUniversalHash forger

/-- **Subset-sum Carter–Wegman multi-query issued-counter MAC (`BitString.SubsetSum.hash`)**:
adaptive multi-query issued-counter EUF-CMA forgery probability is at most `1 / |G|`. -/
theorem counterGame_subsetSum_le {ι G : Type} [Fintype ι] [DecidableEq ι]
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (forger : CounterForger (ι → Bool) G) :
    counterGame (PMF.uniformOfFintype (ι → G)) BitString.SubsetSum.hash forger true ≤
      (Fintype.card G : ℝ≥0∞)⁻¹ :=
  counterGame_le BitString.SubsetSum.isDeltaUniversalHash forger

/-- **Pairwise-independent Carter–Wegman one-time MAC**: any pairwise independent hash family
`hash : K → M → Y` into a finite additive group `Y` has adaptive one-time forgery probability at
most `1 / |Y|`. -/
theorem oneTimeGame_of_isPairwiseIndependentHash_le {K M Y : Type} [Fintype K] [Nonempty K]
    [AddGroup Y] [Fintype Y] [Nonempty Y] [DecidableEq M] [DecidableEq Y] {hash : K → M → Y}
    (hh : IsPairwiseIndependentHash hash) (forger : OneTimeForger M Y) :
    oneTimeGame (PMF.uniformOfFintype K) hash forger true ≤ (Fintype.card Y : ℝ≥0∞)⁻¹ :=
  oneTimeGame_le hh.isDeltaUniversalHash forger

/-- **Pairwise-independent Carter–Wegman multi-query issued-counter MAC**: any pairwise independent
hash family `hash : K → M → Y` has adaptive multi-query issued-counter forgery probability at most
`1 / |Y|`. -/
theorem counterGame_of_isPairwiseIndependentHash_le {K M Y : Type} [Fintype K] [Nonempty K]
    [AddGroup Y] [Fintype Y] [Nonempty Y] [DecidableEq M] [DecidableEq Y] {hash : K → M → Y}
    (hh : IsPairwiseIndependentHash hash) (forger : CounterForger M Y) :
    counterGame (PMF.uniformOfFintype K) hash forger true ≤ (Fintype.card Y : ℝ≥0∞)⁻¹ :=
  counterGame_le hh.isDeltaUniversalHash forger

/-- **Polynomial Carter–Wegman nonce-based MAC (`xpolyHash`)** (after [BonehShoup2023],
Section 7.4.1 and Section 7.5.1, Theorem 7.10, p. 274, with a truly random function in place of the
PRF): over a finite field `F` and finite nonce space `N`, authenticating messages of length at most
`ℓ` via `xpolyHash` has adaptive nonce-based SUF-CMA forgery probability at most `(ℓ + 1) / |F|`
(since `1 / |F| ≤ (ℓ + 1) / |F|`). -/
theorem nonceStrongGame_xpolyHash_le {F N : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype N] [DecidableEq N] (ℓ : ℕ)
    (forger : NonceForger {m : List F // m.length ≤ ℓ} N F) :
    nonceStrongGame (PMF.uniformOfFintype F)
      (fun k (m : {m : List F // m.length ≤ ℓ}) => xpolyHash k m) forger true ≤
      (ℓ + 1) / Fintype.card F := by
  refine (nonceStrongGame_le_max (isDeltaUniversalHash_xpolyHash ℓ) forger).trans (max_le le_rfl ?_)
  rw [← one_div]
  gcongr
  exact le_add_self

/-- **Polynomial Carter–Wegman nonce-based EUF-CMA (message-freshness) security (`xpolyHash`)**. -/
theorem nonceGame_xpolyHash_le {F N : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype N] [DecidableEq N] (ℓ : ℕ)
    (forger : NonceForger {m : List F // m.length ≤ ℓ} N F) :
    nonceGame (PMF.uniformOfFintype F)
      (fun k (m : {m : List F // m.length ≤ ℓ}) => xpolyHash k m) forger true ≤
      (ℓ + 1) / Fintype.card F :=
  (nonceGame_le_nonceStrongGame _ _ forger).trans (nonceStrongGame_xpolyHash_le ℓ forger)

/-- **Polynomial Carter–Wegman randomized MAC (`xpolyHash`)** (after [BonehShoup2023],
Section 7.4, Theorem 7.9, p. 270, with a truly random function in place of the PRF): over a finite
field `F` and nonempty finite nonce space `N`, any `Q`-query-bounded `RandomNonceForger` wins
`randomNonceStrongGame` with probability at most
`(Q : ℝ≥0∞) ^ 2 / (2 * Fintype.card N) + (Fintype.card F : ℝ≥0∞)⁻¹ + (ℓ + 1) / Fintype.card F`. -/
theorem randomNonceStrongGame_xpolyHash_le {F N : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype N] [Nonempty N] [DecidableEq N] (ℓ : ℕ)
    {forger : RandomNonceForger {m : List F // m.length ≤ ℓ} N F} {Q : ℕ}
    (hforger : ∀ s, (forger.forge s).IsQueryBounded Q) :
    randomNonceStrongGame (PMF.uniformOfFintype F)
      (fun k (m : {m : List F // m.length ≤ ℓ}) => xpolyHash k m) forger true ≤
      (Q : ℝ≥0∞) ^ 2 / (2 * Fintype.card N) + (Fintype.card F : ℝ≥0∞)⁻¹ +
        (ℓ + 1) / Fintype.card F :=
  randomNonceStrongGame_le (isDeltaUniversalHash_xpolyHash ℓ) hforger

/-- **Boolean-matrix Carter–Wegman nonce-based MAC (`BitString.LinearHash.hash`)**:
hashing `n`-bit messages to `m`-bit tags with a uniform Boolean matrix has adaptive nonce-based
SUF-CMA forgery probability at most `2⁻ᵐ` (since `max (2⁻ᵐ) (2⁻ᵐ) = 2⁻ᵐ`). -/
theorem nonceStrongGame_linearHash_le {N : Type} [Fintype N] [DecidableEq N] (n m : ℕ)
    (forger : NonceForger (BitString n) N (BitString m)) :
    nonceStrongGame (PMF.uniformOfFintype (Fin m → BitString n))
      BitString.LinearHash.hash forger true ≤ ((2 : ℝ≥0∞) ^ m)⁻¹ := by
  simpa only [max_self, BitString.card, Nat.cast_pow, Nat.cast_ofNat] using
    nonceStrongGame_le_max (BitString.LinearHash.isDeltaUniversalHash n m) forger

/-- **Boolean-matrix Carter–Wegman nonce-based EUF-CMA (message-freshness) security
(`BitString.LinearHash.hash`)**. -/
theorem nonceGame_linearHash_le {N : Type} [Fintype N] [DecidableEq N] (n m : ℕ)
    (forger : NonceForger (BitString n) N (BitString m)) :
    nonceGame (PMF.uniformOfFintype (Fin m → BitString n))
      BitString.LinearHash.hash forger true ≤ ((2 : ℝ≥0∞) ^ m)⁻¹ :=
  (nonceGame_le_nonceStrongGame _ _ forger).trans (nonceStrongGame_linearHash_le n m forger)

/-- **Boolean-matrix Carter–Wegman randomized MAC (`BitString.LinearHash.hash`)**
(after [BonehShoup2023], Section 7.4, Theorem 7.9, p. 270, with a truly random function in place of
the PRF): any `Q`-query-bounded `RandomNonceForger` wins `randomNonceStrongGame` with probability
at most `(Q : ℝ≥0∞) ^ 2 / (2 * Fintype.card N) + ((2 : ℝ≥0∞) ^ m)⁻¹ + ((2 : ℝ≥0∞) ^ m)⁻¹`. -/
theorem randomNonceStrongGame_linearHash_le {N : Type} [Fintype N] [Nonempty N] [DecidableEq N]
    (n m : ℕ) {forger : RandomNonceForger (BitString n) N (BitString m)} {Q : ℕ}
    (hforger : ∀ s, (forger.forge s).IsQueryBounded Q) :
    randomNonceStrongGame (PMF.uniformOfFintype (Fin m → BitString n))
      BitString.LinearHash.hash forger true ≤
      (Q : ℝ≥0∞) ^ 2 / (2 * Fintype.card N) + ((2 : ℝ≥0∞) ^ m)⁻¹ + ((2 : ℝ≥0∞) ^ m)⁻¹ := by
  simpa only [BitString.card, Nat.cast_pow, Nat.cast_ofNat] using
    randomNonceStrongGame_le (BitString.LinearHash.isDeltaUniversalHash n m) hforger

/-- **Subset-sum Carter–Wegman nonce-based MAC (`BitString.SubsetSum.hash`)**:
adaptive nonce-based SUF-CMA forgery probability is at most `1 / |G|`. -/
theorem nonceStrongGame_subsetSum_le {ι N G : Type} [Fintype ι] [DecidableEq ι]
    [Fintype N] [DecidableEq N] [AddCommGroup G] [Fintype G] [DecidableEq G]
    (forger : NonceForger (ι → Bool) N G) :
    nonceStrongGame (PMF.uniformOfFintype (ι → G)) BitString.SubsetSum.hash forger true ≤
      (Fintype.card G : ℝ≥0∞)⁻¹ := by
  simpa only [max_self] using
    nonceStrongGame_le_max BitString.SubsetSum.isDeltaUniversalHash forger

/-- **Pairwise-independent Carter–Wegman nonce-based MAC**: any pairwise independent hash family
`hash : K → M → Y` has adaptive nonce-based SUF-CMA forgery probability at most `1 / |Y|`. -/
theorem nonceStrongGame_of_isPairwiseIndependentHash_le {K M N Y : Type} [Fintype K] [Nonempty K]
    [Fintype N] [DecidableEq N] [AddGroup Y] [Fintype Y] [Nonempty Y] [DecidableEq M]
    [DecidableEq Y] {hash : K → M → Y}
    (hh : IsPairwiseIndependentHash hash) (forger : NonceForger M N Y) :
    nonceStrongGame (PMF.uniformOfFintype K) hash forger true ≤ (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  simpa only [max_self] using nonceStrongGame_le_max hh.isDeltaUniversalHash forger

/-- Sampling an `(n * msgLen n)`-bit Boolean-matrix seed is uniformly strict PPT whenever `msgLen`
is computable in polynomial time. -/
theorem isPPTOn_linearHashSeed {msgLen : ℕ → ℕ}
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary) :
    IsPPTOn encUnary encBits (fun n => BitString.sampleList (n * msgLen n)) :=
  ComputableInPolyTime.sampleList (by fun_prop)

/-- Uncurried `BitString.LinearHash.wordHash` is computable in plain polynomial time. -/
theorem computableInPolyTime_linearHashWordHash :
    ComputableInPolyTime
      (fun ((n, k, m) : ℕ × List Bool × List Bool) => BitString.LinearHash.wordHash n k m)
      (encKeyedInput encBits) encBits := by
  fun_prop

/-- Under a uniform `(n * msgLen n)`-bit seed `BitString.sampleList (n * msgLen n)`, the executable
Boolean-matrix hash `BitString.LinearHash.wordHash n` on `BitString (msgLen n)` into `BitString n`
is `(2 ^ n)⁻¹`-almost-Δ-universal (`IsDeltaUniversalHash`). -/
theorem isDeltaUniversalHash_linearHashWordHash (msgLen : ℕ → ℕ) (n : ℕ) :
    IsDeltaUniversalHash (ProbComp.eval (BitString.sampleList (n * msgLen n)))
      (fun k (m : BitString (msgLen n)) =>
        BitString.ofList n (BitString.LinearHash.wordHash n k (List.ofFn m)))
      ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  let prepare (k : List Bool) : Fin n → BitString (msgLen n) :=
    BitString.block (BitString.ofList (n * msgLen n) k)
  have hfn :
      (fun k (m : BitString (msgLen n)) =>
        BitString.ofList n (BitString.LinearHash.wordHash n k (List.ofFn m))) =
      (fun k (m : BitString (msgLen n)) => BitString.LinearHash.hash (prepare k) m) := by
    funext k m
    rw [BitString.LinearHash.wordHash_eq_ofFn, BitString.ofList_ofFn]
  have hmap :
      (ProbComp.eval (BitString.sampleList (n * msgLen n))).map prepare =
        PMF.uniformOfFintype (Fin n → BitString (msgLen n)) := by
    rw [BitString.eval_sampleList, BitString.uniformList, PMF.map_comp]
    have hcomp :
        prepare ∘ List.ofFn =
          (BitString.blocksEquiv (m := n) (k := msgLen n) :
            BitString (n * msgLen n) ≃ (Fin n → BitString (msgLen n))) := by
      funext s
      simp [prepare, BitString.ofList_ofFn, BitString.blocksEquiv_apply]
    rw [hcomp, PMF.uniformOfFintype_map_equiv]
  rw [hfn]
  refine IsDeltaUniversalHash.precompose_seed
    (ProbComp.eval (BitString.sampleList (n * msgLen n))) prepare ?_
  rw [hmap]
  simpa only [BitString.card, Nat.cast_pow, Nat.cast_ofNat] using
    BitString.LinearHash.isDeltaUniversalHash (msgLen n) n

/-- **Concrete computational nonce-based Carter–Wegman MAC (`NonceMACScheme`) from Boolean-matrix
linear hashing (`BitString.LinearHash.wordHash`) and a PRF family `family`**
([BonehShoup2023], Section 7.5.1, Theorem 7.10, p. 274). -/
noncomputable def linearHashNonceMAC (msgLen : ℕ → ℕ)
    (family : List Bool → List Bool → List Bool)
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary)
    (hfamily : ComputableInPolyTime
      (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits) : NonceMACScheme :=
  carterWegmanNonceMAC msgLen (fun n => BitString.sampleList (n * msgLen n))
    BitString.LinearHash.wordHash family hmsgLen (isPPTOn_linearHashSeed hmsgLen)
    computableInPolyTime_linearHashWordHash hfamily

/-- Step instance of [BonehShoup2023], Theorem 7.10 (Section 7.5.1, p. 274), for the Boolean-matrix
linear hash, not the cited result, which holds for every DUF hash: the quantitative SUF-CMA bound
for `linearHashNonceMAC`. At security parameter `n`, the SUF-CMA forgery probability of any
`NonceMACForger` against `linearHashNonceMAC` is at most `2 * (2 ^ n)⁻¹` plus the PRF distinguishing
advantage of `prfNonceToPrfDistinguisher`. -/
theorem sufCmaGame_linearHashNonceMAC_toReal_le
    {msgLen : ℕ → ℕ} {family : List Bool → List Bool → List Bool}
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary)
    (hfamily : ComputableInPolyTime
      (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits)
    (n : ℕ) (adversary : NonceMACForger) :
    (ProbComp.eval
      ((linearHashNonceMAC msgLen family hmsgLen hfamily).sufCmaGame adversary n) true).toReal ≤
      ((2 : ℝ) ^ n)⁻¹ + ((2 : ℝ) ^ n)⁻¹ +
        (Game.advantage
          (ProbComp.eval
            (prfRealGame id family
               (prfNonceToPrfDistinguisher msgLen (fun k => BitString.sampleList (k * msgLen k))
                 BitString.LinearHash.wordHash adversary) n))
          (ProbComp.eval
            (prfIdealGame id id
              (prfNonceToPrfDistinguisher msgLen (fun k => BitString.sampleList (k * msgLen k))
                BitString.LinearHash.wordHash adversary) n)) : ℝ) := by
  have h := sufCmaGame_carterWegmanNonceMAC_toReal_le hmsgLen (isPPTOn_linearHashSeed hmsgLen)
    computableInPolyTime_linearHashWordHash hfamily
    (isDeltaUniversalHash_linearHashWordHash msgLen n) (by simp) adversary
  simpa only [linearHashNonceMAC, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat] using h

private theorem isDeltaUniversalHash_linearHashWordHash_nnreal (msgLen : ℕ → ℕ) (n : ℕ) :
    IsDeltaUniversalHash (ProbComp.eval (BitString.sampleList (n * msgLen n)))
      (fun k (m : BitString (msgLen n)) =>
        BitString.ofList n (BitString.LinearHash.wordHash n k (List.ofFn m)))
      (((2 : ℝ≥0) ^ n)⁻¹ : ℝ≥0) := by
  simpa only [ENNReal.coe_inv (pow_ne_zero n two_ne_zero), ENNReal.coe_pow, ENNReal.coe_ofNat] using
    isDeltaUniversalHash_linearHashWordHash msgLen n

/-- Step instance of [BonehShoup2023], Theorem 7.10 (Section 7.5.1, p. 274), for the Boolean-matrix
linear hash, not the cited result, which holds for every DUF hash: asymptotic
`NonceMACScheme.SUFCMA` security of `linearHashNonceMAC`. For any `PseudorandomFunction family` and
polynomial-time message-length schedule `msgLen`, `linearHashNonceMAC` satisfies
`NonceMACScheme.SUFCMA`. The Boolean-matrix linear hash is a `2⁻ⁿ`-DUF
(`isDeltaUniversalHash_linearHashWordHash`), hence a statistical and so a computational DUF
([BonehShoup2023], Definition 7.5, p. 269), so this is Theorem 7.10 for this hash; it is proved
through `PseudorandomFunction.sufCma_carterWegmanNonceMAC_of_statisticalDUF`. -/
theorem _root_.Cslib.Crypto.PseudorandomFunction.sufCma_linearHashNonceMAC
    {msgLen : ℕ → ℕ} {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family)
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary) :
    (linearHashNonceMAC msgLen family hmsgLen hprf.polyTime).SUFCMA :=
  hprf.sufCma_carterWegmanNonceMAC_of_statisticalDUF hmsgLen (isPPTOn_linearHashSeed hmsgLen)
    computableInPolyTime_linearHashWordHash (isDeltaUniversalHash_linearHashWordHash_nnreal msgLen)
    negligible_inv_two_pow

/-- Step instance of [BonehShoup2023], Theorem 7.10 (Section 7.5.1, p. 274), for the Boolean-matrix
linear hash, not the cited result, which holds for every DUF hash: asymptotic
`NonceMACScheme.EUFCMA` security of `linearHashNonceMAC`. -/
theorem _root_.Cslib.Crypto.PseudorandomFunction.eufCma_linearHashNonceMAC
    {msgLen : ℕ → ℕ} {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family)
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary) :
    (linearHashNonceMAC msgLen family hmsgLen hprf.polyTime).EUFCMA :=
  (hprf.sufCma_linearHashNonceMAC hmsgLen).eufCma

/-- Asymptotic counter SUF-CMA security of `linearHashNonceMAC`, after [BonehShoup2023], Section 7.5
and the remark after Theorem 7.10 (p. 274), a step and not a cited result: the Boolean-matrix
linear hash instance of `PseudorandomFunction.counterSufCma_carterWegmanNonceMAC_of_statisticalDUF`,
whose only assumption is that `family` is a `PseudorandomFunction`; the hash is a statistical DUF,
as `PseudorandomFunction.sufCma_linearHashNonceMAC` explains. -/
theorem _root_.Cslib.Crypto.PseudorandomFunction.counterSufCma_linearHashNonceMAC
    {msgLen : ℕ → ℕ} {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family)
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary) :
    (linearHashNonceMAC msgLen family hmsgLen hprf.polyTime).CounterSUFCMA :=
  (hprf.sufCma_linearHashNonceMAC hmsgLen).counterSufCma

/-- **Concrete computational randomized Carter–Wegman MAC (`MACScheme`) from Boolean-matrix linear
hashing (`BitString.LinearHash.wordHash`) and a PRF family `family`**
([BonehShoup2023], Section 7.4, Theorem 7.9, p. 270). -/
noncomputable def linearHashRandomMAC (msgLen : ℕ → ℕ)
    (family : List Bool → List Bool → List Bool)
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary)
    (hfamily : ComputableInPolyTime
      (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits) : MACScheme :=
  carterWegmanRandomMAC msgLen (fun n => BitString.sampleList (n * msgLen n))
    BitString.LinearHash.wordHash family hmsgLen (isPPTOn_linearHashSeed hmsgLen)
    computableInPolyTime_linearHashWordHash hfamily

/-- Step instance of [BonehShoup2023], Theorem 7.9 (Section 7.4, p. 270), for the Boolean-matrix
linear hash, not the cited result, which holds for every DUF hash: the quantitative SUF-CMA bound
for `linearHashRandomMAC`. At security parameter `n`, the SUF-CMA forgery probability of any
`Q`-query `Forger` against `linearHashRandomMAC` is at most
`(Q : ℝ) ^ 2 / (2 * (2 : ℝ) ^ n) + ((2 : ℝ) ^ n)⁻¹ + ((2 : ℝ) ^ n)⁻¹` plus the PRF distinguishing
advantage of `prfRandomNonceToPrfDistinguisher`. -/
theorem sufCmaGame_linearHashRandomMAC_toReal_le
    {msgLen : ℕ → ℕ} {family : List Bool → List Bool → List Bool}
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary)
    (hfamily : ComputableInPolyTime
      (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits)
    {n Q : ℕ} {adversary : Forger} (hq : (adversary n []).IsQueryBounded Q) :
    (ProbComp.eval
      ((linearHashRandomMAC msgLen family hmsgLen hfamily).sufCmaGame adversary n) true).toReal ≤
      (Q : ℝ) ^ 2 / (2 * (2 : ℝ) ^ n) + ((2 : ℝ) ^ n)⁻¹ + ((2 : ℝ) ^ n)⁻¹ +
        (Game.advantage
          (ProbComp.eval
            (prfRealGame id family
              (prfRandomNonceToPrfDistinguisher msgLen
                (fun k => BitString.sampleList (k * msgLen k))
                BitString.LinearHash.wordHash adversary) n))
          (ProbComp.eval
            (prfIdealGame id id
              (prfRandomNonceToPrfDistinguisher msgLen
                (fun k => BitString.sampleList (k * msgLen k))
                BitString.LinearHash.wordHash adversary) n)) : ℝ) := by
  dsimp only [linearHashRandomMAC]
  have h := sufCmaGame_carterWegmanRandomMAC_toReal_le hmsgLen (isPPTOn_linearHashSeed hmsgLen)
    computableInPolyTime_linearHashWordHash hfamily
    (isDeltaUniversalHash_linearHashWordHash msgLen n) (by simp) hq
  simpa only [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat] using h

/-- Step instance of [BonehShoup2023], Theorem 7.9 (Section 7.4, p. 270), for the Boolean-matrix
linear hash, not the cited result, which holds for every DUF hash: asymptotic `MACScheme.SUFCMA`
security of `linearHashRandomMAC`. For any `PseudorandomFunction family` and polynomial-time
message-length schedule `msgLen`, `linearHashRandomMAC` satisfies `MACScheme.SUFCMA`. The
Boolean-matrix linear hash is a `2⁻ⁿ`-DUF (`isDeltaUniversalHash_linearHashWordHash`), hence a
statistical and so a computational DUF ([BonehShoup2023], Definition 7.5, p. 269), so this is
Theorem 7.9 for this hash; it is proved through
`PseudorandomFunction.sufCma_carterWegmanRandomMAC_of_statisticalDUF`. -/
theorem _root_.Cslib.Crypto.PseudorandomFunction.sufCma_linearHashRandomMAC
    {msgLen : ℕ → ℕ} {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family)
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary) :
    (linearHashRandomMAC msgLen family hmsgLen hprf.polyTime).SUFCMA :=
  hprf.sufCma_carterWegmanRandomMAC_of_statisticalDUF hmsgLen (isPPTOn_linearHashSeed hmsgLen)
    computableInPolyTime_linearHashWordHash (isDeltaUniversalHash_linearHashWordHash_nnreal msgLen)
    negligible_inv_two_pow

/-- Step instance of [BonehShoup2023], Theorem 7.9 (Section 7.4, p. 270), for the Boolean-matrix
linear hash, not the cited result, which holds for every DUF hash: asymptotic `MACScheme.EUFCMA`
security of `linearHashRandomMAC`. -/
theorem _root_.Cslib.Crypto.PseudorandomFunction.eufCma_linearHashRandomMAC
    {msgLen : ℕ → ℕ} {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family)
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary) :
    (linearHashRandomMAC msgLen family hmsgLen hprf.polyTime).EUFCMA :=
  (hprf.sufCma_linearHashRandomMAC hmsgLen).eufCma

/-- Step instance of [BonehShoup2023], Theorem 7.9 (Section 7.4, p. 270), for the Boolean-matrix
linear hash, not the cited result, which holds for every DUF hash: asymptotic
`MACScheme.OneTimeEUFCMA` security of `linearHashRandomMAC`. -/
theorem _root_.Cslib.Crypto.PseudorandomFunction.oneTimeEUFCMA_linearHashRandomMAC
    {msgLen : ℕ → ℕ} {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family)
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary) :
    (linearHashRandomMAC msgLen family hmsgLen hprf.polyTime).OneTimeEUFCMA :=
  (hprf.sufCma_linearHashRandomMAC hmsgLen).oneTimeEUFCMA

end Instantiations

end Cslib.Crypto.Protocols.CarterWegman
