/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MAC
public import CslibFrontier.Crypto.Computational.PseudorandomFunction.PrefixFree
public import CslibFrontier.Crypto.Computational.PseudorandomFunction.RandomOracle
public import CslibFrontier.Crypto.Primitives.BlockCipher.LengthPrependedCBCMAC
public import CslibFrontier.Foundations.Data.BitString.List.Binary
public import CslibFrontier.Foundations.Data.BitString.List.Rows
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Probabilistic.Memoize
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Foundations.Data.BitString.List.LowBits
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.CoinFixing
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation.Handler
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.QueryCount
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Computational PRF and MAC Security for CBC-MAC and Length-Prepended CBC-MAC

This module lifts the finite uniform-random-function bounds of
`CslibFrontier.Crypto.Primitives.BlockCipher.CBCMAC` and
`CslibFrontier.Crypto.Primitives.BlockCipher.LengthPrependedCBCMAC` to uniform computational
pseudorandom-function (`PRF`) and adaptive chosen-message MAC (`SUFCMA`, `EUFCMA`) security over a
length-preserving keyed block-function family (`PseudorandomFunction`), completing #6046:

1. **Prefix-free CBC-MAC is a computational prefix-free PRF** ([BonehShoup2023], Section 6.4.1,
   Theorem 6.3, printed pp. 226–229): for any `PseudorandomFunction family` and unary
   polynomial-time block-count cap `ℓ : ℕ → ℕ`, basic zero-IV CBC-MAC (`cbcMacFamily family`) is
   indistinguishable from a uniform random function on nonempty whole-block messages of at most
   `ℓ n` blocks (`cbcBlockValid ℓ`) against every uniform strict oracle-PPT prefix-free
   distinguisher (`PseudorandomFunction.prefixFreePRF_cbcMac`), via the certified reduction
   `cbcMacToPrfDistinguisher` and concrete game-hop bound `advantage_cbcMac_le`. Specializing to
   fixed `ℓ n`-block messages (`0 < ℓ n`) gives standard `PseudorandomFunctionOver` security
   (`PseudorandomFunction.prfOver_cbcMac`) and `MACScheme` `SUFCMA` security
   (`PseudorandomFunction.sufCma_cbcFixedBlockMAC`, with `EUFCMA` via `MACScheme.SUFCMA.eufCma`).
   As a CBC-MAC step toward #5801's open cascade / extendable-PRF / extension-attack item (after
   [BonehShoup2023], Section 6.4.3, pp. 230–231; cascade `F*` and Definition 6.4 remain open), the
   1-query length-extension forger `cbcExtensionForger` breaks variable-length `MACSUFCMAOn` and
   `PseudorandomFunctionOn` for every length-preserving family (`not_macSufCmaOn_cbcMacFamily`,
   `not_prfOn_cbcMacFamily`).
2. **Length-prepended CBC-MAC is a variable-length PRF and adaptive MAC** ([BonehShoup2023],
   Section 6.4.1 Theorem 6.3, pp. 226–229, Section 6.6.1 Method 1 via Section 6.6 Theorem 6.8,
   pp. 235–236, and Section 6.3 Theorem 6.2, p. 224):
   prepending the `n`-bit little-endian binary block count `BitString.lowBits n (msg.length / n)`
   makes whole-block messages of `0` to `L n` blocks (empty message included) prefix-free whenever
   `L n < 2 ^ n`, which holds eventually for every unary polynomial-time schedule `L`. Under
   `PseudorandomFunction family` and `ComputableInPolyTime L encUnary encUnary` alone,
   `lengthPrependedCbcMacFamily family` is a full variable-length computational PRF on
   `lpBlockValid L` (`PseudorandomFunction.prfOn_lengthPrependedCbcMac`) and satisfies adaptive
   chosen-message unforgeability on `lpBlockValid L`
   (`PseudorandomFunction.macSufCmaOn_lengthPrependedCbcMac`, equivalent to `MACEUFCMAOn` via
   `macSufCmaOn_iff_macEufCmaOn`), as well as `MACScheme.SUFCMA` at any unary polynomial-time
   block-count schedule `k` including `k n = 0`
   (`PseudorandomFunction.sufCma_lengthPrependedBlockMAC`).

## Deviations from [BonehShoup2023] Theorems 6.2, 6.3, and 6.8

* **Concrete Method 1 specialization of Theorem 6.8.** [BonehShoup2023], Section 6.6, Theorem 6.8
  (printed p. 235) states PRF security for an arbitrary prefix-free PRF composed with an arbitrary
  prefix-free encoding (see `Cslib.Crypto.PRF.IsPrefixFreeEncoding` in
  `CslibFrontier.Crypto.Primitives.PRF.PrefixFreeEncoding`). Here `lengthPrependedCbcMacFamily`
  formalizes the concrete Section 6.6.1 Method 1 composition (`prependLengthWord` followed by basic
  CBC-MAC) over `{0,1}^n` whole-block messages of `0` to `L n` blocks (including the `0`-block
  empty message, so the prepended chain has `1` to `L n + 1` blocks).
* **Uniform strict oracle-PPT adversaries and flat bit-word messages.** Following the asymptotic
  reading of [BonehShoup2023], Sections 2.3 and 4.4.5, adversaries are uniform strict `IsOraclePPT`
  programs over `List Bool` with `n`-bit keys and blocks (`|X| = 2 ^ n`), and queries outside the
  declared whole-block domain (`cbcBlockValid ℓ` or `lpBlockValid L`) receive `[]` without invoking
  the keyed family or recording a MAC query, matching `prfRealGame` and `MACScheme.sufCmaGame`.
* **Execution-based prefix-freeness on valid queries.** [BonehShoup2023], Section 4.6.1,
  Definition 4.5 (printed p. 152) and Section 6.4 (p. 226) require all queries of a prefix-free PRF
  adversary to lie in `X_{>0}^{≤ ℓ}` with no query a proper prefix of another (repeated identical
  queries permitted). Because invalid word queries are answered with `[]` in both worlds without
  reaching CBC-MAC, `IsPrefixFreeOn valid outLen` imposes no-proper-prefix among valid queries along
  runs against deterministic oracles that map valid queries to `outLen`-bit words and invalid words
  to `[]`. On adversaries whose queries all lie in `cbcBlockValid ℓ n`, the two conditions coincide.
* **Little-endian block-count block.** `prependLengthWord` writes `v = msg.length / n` as
  `BitString.lowBits n v`, matching `List.ofFn (blockCountBlock h v)` where
  [BonehShoup2023], Section 6.6.1, Method 1 (p. 235) writes an `n`-bit binary representation of `v`.

## Main definitions

* `cbcMacWord`, `cbcMacFamily`, `prependLengthWord`, `lengthPrependedCbcMacWord`,
  `lengthPrependedCbcMacFamily`: polynomial-time word-level basic and length-prepended CBC-MAC.
* `cbcBlockValid`, `lpBlockValid`: the word-level query domains for both forms of CBC-MAC.
* `cbcInputCodec`, `lengthPrependedCodec`: `OracleCodec` bridges to `CBCOracleSpec` and
  `LengthPrependedSpec`.
* `cbcMacStep`, `cbcMacQueries`, `cbcMacQuery`, `cbcMacToPrfDistinguisher`, `lengthPrependedQuery`,
  `lengthPrependedToPrfDistinguisher`: certified word-oracle PRF reductions.
* `macSigningPairOracleOn`, `macSigningOracleOn`, `macSufCmaGameOn`, `macEufCmaGameOn`,
  `MACSUFCMAOn`, `MACEUFCMAOn`, `macToPrfOnDistinguisher`,
  `lengthPrependedMacToPrfDistinguisher`, `cbcExtensionForger`, `cbcFixedBlockMAC`,
  `cbcFixedBlockMacToPrfDistinguisher`, `lengthPrependedBlockMAC`: domain-restricted and
  `MACScheme` adaptive chosen-message security games, certified reductions, and extension forger.

## Main results

* `cbcMacWord_append_block`: one-step chaining on aligned words, which preserves equal tags
  under a common block extension.

* `computableInPolyTime_cbcMacFamily`, `computableInPolyTime_lengthPrependedCbcMacFamily`,
  `ofFn_blockCountBlock`: polynomial-time evaluation and exact bit-level agreement with
  `blockCountBlock`.
* `isOraclePPT_cbcMacToPrfDistinguisher`, `advantage_cbcMac_le`,
  `PseudorandomFunction.prefixFreePRF_cbcMac`, `PseudorandomFunction.prfOver_cbcMac`: certified
  reduction, concrete advantage bound, and asymptotic prefix-free / fixed-block PRF security for
  basic CBC-MAC ([BonehShoup2023], Theorem 6.3, pp. 226–229).
* `isOraclePPT_lengthPrependedToPrfDistinguisher`, `advantage_lengthPrependedCbcMac_le`,
  `PseudorandomFunction.prfOn_lengthPrependedCbcMac`,
  `PseudorandomFunction.prfOver_lengthPrependedCbcMac`: certified reduction, concrete advantage
  bound, and variable-length / fixed-block PRF security for length-prepended CBC-MAC
  ([BonehShoup2023], Theorems 6.3 and 6.8, pp. 226–229 and 235–236).
* `eval_macSufCmaGameOn_eq_macEufCmaGameOn`, `macSufCmaOn_iff_macEufCmaOn`,
  `isOraclePPT_macToPrfOnDistinguisher`, `succProbability_macSufCmaGameOn_le`,
  `PseudorandomFunctionOn.macSufCmaOn`, `isOraclePPT_lengthPrependedMacToPrfDistinguisher`,
  `succProbability_macSufCmaGameOn_lengthPrependedCbcMac_le`,
  `PseudorandomFunction.macSufCmaOn_lengthPrependedCbcMac`: certified forger-to-PRF reductions,
  concrete forgery bounds, and adaptive `MACSUFCMAOn` security on variable-length whole-block
  messages ([BonehShoup2023], Theorems 6.2, 6.3, and 6.8).
* `isOraclePPT_cbcExtensionForger`, `eval_macSufCmaGameOn_cbcMacFamily_cbcExtensionForger`,
  `not_macSufCmaOn_cbcMacFamily`, `not_prfOn_cbcMacFamily`: CBC-MAC length-extension step toward
  #5801 after [BonehShoup2023], Section 6.4.3 (pp. 230–231; cascade `F*` and Definition 6.4 remain
  open).
* `isOraclePPT_cbcFixedBlockMacToPrfDistinguisher`,
  `succProbability_sufCmaGame_cbcFixedBlockMAC_le`,
  `PseudorandomFunction.sufCma_cbcFixedBlockMAC`,
  `PseudorandomFunction.sufCma_lengthPrependedBlockMAC`: `MACScheme` `SUFCMA` corollaries.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 4.4.1 (Attack Game 4.2 and Definition 4.2, pp. 132–133),
  Section 4.6.1 (Definition 4.5, p. 152), Section 6.1 (Attack Game 6.1 and Definition 6.2,
  pp. 218–219), Section 6.3 (Theorem 6.2, p. 224), Section 6.4.1 (Figure 6.3a and Theorem 6.3,
  pp. 226–229), Section 6.4.3 (pp. 230–231), and Sections 6.6–6.6.1 (Theorem 6.8 and Method 1,
  pp. 235–236).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-! ### Section 1: Word-Level Basic and Length-Prepended CBC-MAC -/

/-- Word-level basic CBC-MAC ([BonehShoup2023], Section 6.4.1, Figure 6.3a, printed p. 226):
starting from the `n`-bit zero block `List.replicate n false`, XOR the chaining block with each
`n`-bit block of `msg` and apply `family key` truncated to `n` bits. Truncating step outputs keeps
the chaining state bounded on all inputs while leaving `n`-bit block evaluations unchanged. -/
@[expose]
def cbcMacWord (family : List Bool → List Bool → List Bool) (n : ℕ)
    (key msg : List Bool) : List Bool :=
  (BitString.listRows (msg.length / n) n msg).foldl
    (fun state block => (family key (List.zipWith xor state block)).take n)
    (List.replicate n false)

/-- Appending one full block to an aligned word advances the CBC-MAC state by one step.
In particular, equal tags stay equal after appending the same block, the CBC-MAC extension
property used in [BonehShoup2023], v0.6, §7.2.2, printed p. 258. -/
theorem cbcMacWord_append_block (family : List Bool → List Bool → List Bool) {n : ℕ}
    (hn : 0 < n) (key : List Bool) {msg block : List Bool} (hmsg : n ∣ msg.length)
    (hblock : block.length = n) :
    cbcMacWord family n key (msg ++ block) =
      (family key (List.zipWith xor (cbcMacWord family n key msg) block)).take n := by
  have hdvd : n ∣ block.length := by simpa only [hblock] using (dvd_rfl : n ∣ n)
  have hrow : BitString.listRows (block.length / n) n block = [block] := by
    simpa only [List.length_singleton, List.flatten_singleton, hblock, Nat.div_self hn] using
      BitString.listRows_flatten [block]
        (fun _ hm => (List.mem_singleton.mp hm) ▸ hblock)
  simp only [cbcMacWord, BitString.listRows_append_aligned hn hmsg hdvd, hrow,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Keyed-family presentation of basic CBC-MAC at block width `key.length`. -/
@[expose]
def cbcMacFamily (family : List Bool → List Bool → List Bool) (key msg : List Bool) : List Bool :=
  cbcMacWord family key.length key msg

/-- Prepend the `n`-bit little-endian binary block count `BitString.lowBits n (msg.length / n)` to
`msg` ([BonehShoup2023], Section 6.6.1, Method 1, printed p. 235). -/
@[expose]
def prependLengthWord (n : ℕ) (msg : List Bool) : List Bool :=
  BitString.lowBits n (msg.length / n) ++ msg

/-- Word-level length-prepended CBC-MAC ([BonehShoup2023], Section 6.6.1, Method 1,
printed p. 235): prepend the `n`-bit binary block count `msg.length / n` and evaluate
`cbcMacWord`. -/
@[expose]
def lengthPrependedCbcMacWord (family : List Bool → List Bool → List Bool) (n : ℕ)
    (key msg : List Bool) : List Bool :=
  cbcMacWord family n key (prependLengthWord n msg)

/-- Keyed-family presentation of length-prepended CBC-MAC at block width `key.length`. -/
@[expose]
def lengthPrependedCbcMacFamily (family : List Bool → List Bool → List Bool)
    (key msg : List Bool) : List Bool :=
  lengthPrependedCbcMacWord family key.length key msg

private theorem foldl_cbcStep_length {g : List Bool → List Bool} {n : ℕ}
    (hg : ∀ x : List Bool, x.length = n → (g x).length = n)
    {state : List Bool} (hstate : state.length = n) {ms : List (List Bool)}
    (hms : ∀ m ∈ ms, m.length = n) :
    (ms.foldl (fun s b => (g (List.zipWith xor s b)).take n) state).length = n := by
  induction ms generalizing state with
  | nil => exact hstate
  | cons m ms ih =>
    have hgLen := hg (List.zipWith xor state m) (by simp [hstate, hms m List.mem_cons_self])
    exact ih (by simp [hgLen]) fun b hb => hms b (List.mem_cons_of_mem _ hb)

/-- When `family key` maps `n`-bit blocks to `n`-bit blocks, `cbcMacWord` always outputs `n`
bits. -/
theorem length_cbcMacWord {family : List Bool → List Bool → List Bool} {n : ℕ} {key : List Bool}
    (hlen : ∀ x : List Bool, x.length = n → (family key x).length = n) (msg : List Bool) :
    (cbcMacWord family n key msg).length = n :=
  foldl_cbcStep_length hlen (List.length_replicate)
    (fun _ hm => BitString.length_of_mem_listRows hm)

/-- When `family` is length-preserving, `cbcMacFamily family key msg` has `key.length` bits. -/
theorem length_cbcMacFamily {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query : List Bool, query.length = key.length →
      (family key query).length = key.length)
    (key msg : List Bool) :
    (cbcMacFamily family key msg).length = key.length :=
  length_cbcMacWord (hlen key) msg

/-- When `family key` maps `n`-bit blocks to `n`-bit blocks, `lengthPrependedCbcMacWord` outputs `n`
bits. -/
theorem length_lengthPrependedCbcMacWord {family : List Bool → List Bool → List Bool} {n : ℕ}
    {key : List Bool} (hlen : ∀ x : List Bool, x.length = n → (family key x).length = n)
    (msg : List Bool) :
    (lengthPrependedCbcMacWord family n key msg).length = n :=
  length_cbcMacWord hlen (prependLengthWord n msg)

/-- When `family` is length-preserving, `lengthPrependedCbcMacFamily family key msg` has
`key.length` bits. -/
theorem length_lengthPrependedCbcMacFamily {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query : List Bool, query.length = key.length →
      (family key query).length = key.length)
    (key msg : List Bool) :
    (lengthPrependedCbcMacFamily family key msg).length = key.length :=
  length_lengthPrependedCbcMacWord (hlen key) msg

private theorem computableInPolyTime_cbcMacWord_with
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits)
    {α : Type} {input : α ↪ List Bool} {width : α → ℕ} {key msg : α → List Bool}
    (hwidth : ComputableInPolyTime width input encUnary)
    (hkey : ComputableInPolyTime key input encBits)
    (hmsg : ComputableInPolyTime msg input encBits) :
    ComputableInPolyTime (fun a => cbcMacWord family (width a) (key a) (msg a))
      input encBits := by
  let EPar := encPair encUnary encBits
  let EFold := encPair (encPair EPar encBits) encBits
  have hblocks : ComputableInPolyTime
      (fun a => BitString.listRows ((msg a).length / width a) (width a) (msg a))
      input (encList encBits) :=
    ComputableInPolyTime.bitsRowsWithInput
      (ComputableInPolyTime.unary_div' (ComputableInPolyTime.length_bits.comp hmsg) hwidth)
      hwidth hmsg
  have hstep : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × List Bool =>
        (family p.1.1.2 (List.zipWith xor p.1.2 p.2)).take p.1.1.1)
      EFold encBits := by
    dsimp only [EFold, EPar]
    refine ComputableInPolyTime.bitsTakeWithInput
      (hpoly.comp (ComputableInPolyTime.prod ?_
        (ComputableInPolyTime.bitsZipWithInput xor ?_ ?_))) ?_
    all_goals fun_prop
  exact ComputableInPolyTime.foldlWith_of_bounded_growth
    (encA := encBits) (encL := encList encBits) (encP := EPar) (encB := encBits)
    (par := fun a => (width a, key a))
    (list := fun a => BitString.listRows ((msg a).length / width a) (width a) (msg a))
    (init := fun a => List.replicate (width a) false)
    (step := fun wk state block => (family wk.2 (List.zipWith xor state block)).take wk.1)
    (hwidth.prod hkey) hblocks ((ComputableInPolyTime.bitsReplicate false).comp hwidth) hstep
    (growth := fun a => width a) hwidth.polyBounded
    (fun a state block _ => by
      simp only [encBits_apply]
      exact (List.length_take_le _ _).trans (Nat.le_add_left _ _))

/-- `cbcMacFamily family` is computable in deterministic polynomial time whenever `family` is. -/
theorem computableInPolyTime_cbcMacFamily
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun p : List Bool × List Bool => cbcMacFamily family p.1 p.2)
      (encPair encBits encBits) encBits :=
  computableInPolyTime_cbcMacWord_with hpoly
    (ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.fst encBits encBits))
    (ComputableInPolyTime.fst encBits encBits)
    (ComputableInPolyTime.snd encBits encBits)

private theorem computableInPolyTime_prependLengthWord_with
    {α : Type} {input : α ↪ List Bool} {width : α → ℕ} {msg : α → List Bool}
    (hwidth : ComputableInPolyTime width input encUnary)
    (hmsg : ComputableInPolyTime msg input encBits) :
    ComputableInPolyTime (fun a => prependLengthWord (width a) (msg a)) input encBits :=
  ComputableInPolyTime.bitsAppend (ComputableInPolyTime.bitsLow hwidth
    (ComputableInPolyTime.unary_to_binary.comp
      (ComputableInPolyTime.unary_div' (ComputableInPolyTime.length_bits.comp hmsg) hwidth))) hmsg

/-- `lengthPrependedCbcMacFamily family` is computable in deterministic polynomial time whenever
`family` is. -/
theorem computableInPolyTime_lengthPrependedCbcMacFamily
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime
      (fun p : List Bool × List Bool => lengthPrependedCbcMacFamily family p.1 p.2)
      (encPair encBits encBits) encBits :=
  computableInPolyTime_cbcMacWord_with hpoly
    (ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.fst encBits encBits))
    (ComputableInPolyTime.fst encBits encBits)
    (computableInPolyTime_prependLengthWord_with
      (ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.fst encBits encBits))
      (ComputableInPolyTime.snd encBits encBits))

private theorem val_equivFin_testBit :
    ∀ {n m : ℕ}, m < 2 ^ n →
      (BitString.equivFin n (fun i : Fin n => m.testBit i.val) : ℕ) = m
  | 0, m, hm => by simp [Nat.lt_one_iff.mp hm]
  | n + 1, m, hm => by
    have hcons : (fun i : Fin (n + 1) => m.testBit i.val) =
        Fin.cons (m.testBit 0) (fun j : Fin n => (m / 2).testBit j.val) := by
      refine funext (Fin.cases (by simp) fun _ => ?_)
      simp [Nat.testBit_succ]
    have hdiv : m / 2 < 2 ^ n := by
      rw [pow_succ] at hm
      omega
    rw [hcons, BitString.val_equivFin_cons, val_equivFin_testBit hdiv, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h] <;> omega

/-- The `n`-bit block `blockCountBlock h k` flattens to `BitString.lowBits n k.val`. -/
theorem ofFn_blockCountBlock {n L : ℕ} (h : L < 2 ^ n) (k : Fin (L + 1)) :
    List.ofFn (blockCountBlock h k) = BitString.lowBits n k.val := by
  have hk : k.val < 2 ^ n := k.isLt.trans_le h
  have hsymm : blockCountBlock h k = fun i : Fin n => k.val.testBit i.val := by
    apply (BitString.equivFin n).injective
    rw [blockCountBlock, Equiv.apply_symm_apply]
    exact Fin.ext (val_equivFin_testBit hk).symm
  rw [hsymm, BitString.lowBits_eq_ofFn]

private theorem foldl_cbcStep_map_ofFn {n : ℕ} {f : List Bool → List Bool}
    {g : BitString n → BitString n}
    (hfg : ∀ x : BitString n, (f (List.ofFn x)).take n = List.ofFn (g x))
    (iv : BitString n) (bs : List (BitString n)) :
    (bs.map List.ofFn).foldl (fun state block => (f (List.zipWith xor state block)).take n)
      (List.ofFn iv) = List.ofFn (cbcMacBlocks g iv bs) := by
  induction bs generalizing iv with
  | nil => rfl
  | cons b bs ih =>
    have hxor : List.zipWith xor (List.ofFn iv) (List.ofFn b) = List.ofFn (iv + b) :=
      (BitString.ofFn_add iv b).symm
    simp only [List.map_cons, List.foldl_cons, hxor, hfg, cbcMacBlocks_cons]
    exact ih (g (iv + b))

private theorem cbcMacWord_eq_ofFn_cbcMacBlocks {n : ℕ} {f : List Bool → List Bool}
    {g : BitString n → BitString n}
    (hfg : ∀ x : BitString n, (f (List.ofFn x)).take n = List.ofFn (g x))
    (msg : List Bool) :
    cbcMacWord (fun _ => f) n [] msg =
      List.ofFn (cbcMacBlocks g 0 (BitString.toBlocks n msg)) := by
  have hzero : List.replicate n false = List.ofFn (0 : BitString n) := by
    refine List.ext_getElem (by simp) fun i _ _ => ?_
    simp [OfNat.ofNat, Zero.zero]
  rw [cbcMacWord, BitString.listRows_eq_map_ofFn_toBlocks, hzero]
  exact foldl_cbcStep_map_ofFn hfg 0 _

/-! ### Section 2: CBC-MAC Query Domains -/

/-- Nonempty whole-block messages of at most `ℓ n` blocks (`X_{>0}^{≤ ℓ n}` in
[BonehShoup2023], Section 6.4, printed p. 226). At `n = 0`, `ℓ 0 * 0 = 0`, so every message is
rejected. -/
@[expose]
def cbcBlockValid (ℓ : ℕ → ℕ) (n : ℕ) (msg : List Bool) : Bool :=
  decide (0 < msg.length) && (msg.length % n == 0) && decide (msg.length ≤ ℓ n * n)

/-- Whole-block messages of at most `L n` blocks, including the empty message `[]` (`X^{≤ L n}` in
[BonehShoup2023], Section 6.6, printed p. 235). -/
@[expose]
def lpBlockValid (L : ℕ → ℕ) (n : ℕ) (msg : List Bool) : Bool :=
  (msg.length % n == 0) && decide (msg.length ≤ L n * n)

/-- `cbcBlockValid ℓ` is computable in polynomial time whenever `ℓ` is computable in polynomial time
in unary. -/
theorem computableInPolyTime_cbcBlockValid {ℓ : ℕ → ℕ}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) :
    ComputableInPolyTime (fun (n, msg) => cbcBlockValid ℓ n msg)
      (encPair encUnary encBits) encBool := by
  unfold cbcBlockValid
  polytime

/-- `lpBlockValid L` is computable in polynomial time whenever `L` is computable in polynomial time
in unary. -/
theorem computableInPolyTime_lpBlockValid {L : ℕ → ℕ}
    (hL : ComputableInPolyTime L encUnary encUnary) :
    ComputableInPolyTime (fun (n, msg) => lpBlockValid L n msg)
      (encPair encUnary encBits) encBool := by
  unfold lpBlockValid
  polytime

/-! ### Section 3: Typed Codec Bridges to `CBCOracleSpec` and `LengthPrependedSpec` -/

private def encodeBlockList {n : ℕ} (bs : List (BitString n)) : List Bool :=
  bs.flatMap List.ofFn

private theorem length_encodeBlockList {n : ℕ} (bs : List (BitString n)) :
    (encodeBlockList bs).length = bs.length * n := by
  simp [encodeBlockList, List.length_flatMap]

private theorem toBlocks_encodeBlockList {n : ℕ} (hn : 0 < n) (bs : List (BitString n)) :
    BitString.toBlocks n (encodeBlockList bs) = bs := by
  have h := BitString.listRows_flatten (width := n) (bs.map List.ofFn) (by simp)
  rw [List.length_map, ← List.flatMap_def, ← encodeBlockList, ← Nat.mul_div_cancel bs.length hn,
    ← length_encodeBlockList, BitString.listRows_eq_map_ofFn_toBlocks] at h
  exact List.map_injective_iff.mpr List.ofFn_injective h

private theorem cbcInputBlocks_injective {n ℓ : ℕ} :
    Function.Injective (cbcInputBlocks (n := n) (ℓ := ℓ)) := by
  rintro ⟨k, f⟩ ⟨k', f'⟩ h
  have hk : k = k' := Fin.ext (by
    have hlen := congrArg List.length h
    simpa only [length_cbcInputBlocks, Nat.add_right_cancel_iff] using hlen)
  subst hk
  exact congrArg (Sigma.mk k) (List.ofFn_injective h)

private def decodeCBCWord (n ℓ : ℕ) (w : List Bool) : Option (CBCInput n ℓ) :=
  let blocks := BitString.toBlocks n w
  if h : blocks.length - 1 < ℓ ∧ 0 < blocks.length ∧ w.length = blocks.length * n then
    some ⟨⟨blocks.length - 1, h.1⟩, fun i => blocks[i.val]'(i.isLt.trans_le (by
      have := h.2.1
      dsimp only
      omega))⟩
  else
    none

/-- Word-to-typed codec identifying `cbcBlockValid (fun _ => ℓ) n` word queries (`0 < n`) with
`CBCInput n ℓ` and `n`-bit replies. -/
def cbcInputCodec (n ℓ : ℕ) (hn : 0 < n) : OracleCodec Unit (CBCInput n ℓ) (CBCOracleSpec n ℓ) where
  encodeQuery q := ((), encodeBlockList (cbcInputBlocks q))
  decodeQuery req := decodeCBCWord n ℓ req.2
  decodeQuery_eq_some_iff := by
    rintro ⟨⟨⟩, w⟩ q
    constructor
    · intro hdec
      unfold decodeCBCWord at hdec
      dsimp only at hdec
      split_ifs at hdec with h
      obtain rfl := Option.some.inj hdec.symm
      refine Prod.ext rfl ?_
      have hblocks : cbcInputBlocks
          ⟨⟨(BitString.toBlocks n w).length - 1, h.1⟩,
            fun i => (BitString.toBlocks n w)[i.val]'(i.isLt.trans_le (by
              have := h.2.1; dsimp only; omega))⟩ =
          BitString.toBlocks n w := by
        refine List.ext_getElem ?_ fun i _ _ => by simp only [cbcInputBlocks, List.getElem_ofFn]
        rw [length_cbcInputBlocks]
        have := h.2.1
        dsimp only
        omega
      have hmod : n ∣ w.length := ⟨_, by rw [Nat.mul_comm]; exact h.2.2⟩
      rw [hblocks, encodeBlockList, BitString.flatMap_ofFn_toBlocks hmod]
    · intro henc
      rcases Prod.mk.inj henc with ⟨-, rfl⟩
      rcases q with ⟨k, f⟩
      let bs := cbcInputBlocks ⟨k, f⟩
      have hpad : BitString.toBlocks n (encodeBlockList bs) = bs :=
        toBlocks_encodeBlockList hn bs
      have hbsLen : bs.length = k.val + 1 := length_cbcInputBlocks ⟨k, f⟩
      have hcond :
          (BitString.toBlocks n (encodeBlockList bs)).length - 1 < ℓ ∧
          0 < (BitString.toBlocks n (encodeBlockList bs)).length ∧
          (encodeBlockList bs).length =
            (BitString.toBlocks n (encodeBlockList bs)).length * n := by
        rw [hpad, length_encodeBlockList, hbsLen]
        exact ⟨by omega, Nat.succ_pos k.val, rfl⟩
      change decodeCBCWord n ℓ (encodeBlockList bs) = some ⟨k, f⟩
      unfold decodeCBCWord
      dsimp only
      rw [dite_eq_left_of_eq_true (eq_true hcond), Option.some.injEq]
      apply cbcInputBlocks_injective
      refine Eq.trans ?_ hpad
      refine List.ext_getElem ?_ fun i _ _ => by simp only [cbcInputBlocks, List.getElem_ofFn]
      rw [length_cbcInputBlocks]
      have := hcond.2.1
      dsimp only
      omega
  encodeReply _ := ⟨List.ofFn, List.ofFn_injective⟩

private theorem cbcBlockValid_eq_isSome_cbcInputCodec {ℓ : ℕ → ℕ} {n : ℕ} (hn : 0 < n)
    (query : List Bool) :
    cbcBlockValid ℓ n query = ((cbcInputCodec n (ℓ n) hn).decodeQuery ((), query)).isSome := by
  have hiff : cbcBlockValid ℓ n query = true ↔ (BitString.toBlocks n query).length - 1 < ℓ n ∧
      0 < (BitString.toBlocks n query).length ∧
      query.length = (BitString.toBlocks n query).length * n := by
    simp only [cbcBlockValid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      BitString.length_toBlocks]
    constructor
    · rintro ⟨⟨hpos, hmod⟩, hle⟩
      have hdivPos := Nat.div_pos (Nat.le_of_dvd hpos (Nat.dvd_of_mod_eq_zero hmod)) hn
      have hdivLe : query.length / n ≤ ℓ n := Nat.div_le_of_le_mul (by rwa [Nat.mul_comm])
      exact ⟨by omega, hdivPos, (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)).symm⟩
    · rintro ⟨hlt, hpos, hmul⟩
      rw [hmul]
      exact ⟨⟨Nat.mul_pos hpos hn, Nat.mul_mod_left _ _⟩, Nat.mul_le_mul_right n (by omega)⟩
  rw [Bool.eq_iff_iff, hiff]
  dsimp only [cbcInputCodec, decodeCBCWord]
  split_ifs with h
  exacts [iff_of_true h rfl, iff_of_false h Bool.false_ne_true]

private def decodeLPWord (n L : ℕ) (w : List Bool) : Option (LengthPrependedInput n L) :=
  let blocks := BitString.toBlocks n w
  if h : blocks.length < L + 1 ∧ w.length = blocks.length * n then
    some ⟨⟨blocks.length, h.1⟩, fun i => blocks[i.val]'i.isLt⟩
  else
    none

/-- Word-to-typed codec identifying `lpBlockValid (fun _ => L) n` word queries (`L < 2 ^ n`) with
`LengthPrependedInput n L` and `n`-bit replies, including `[]` and `n = 0, L = 0`. -/
def lengthPrependedCodec (n L : ℕ) (hL : L < 2 ^ n) :
    OracleCodec Unit (LengthPrependedInput n L) (LengthPrependedSpec n L) where
  encodeQuery q := ((), encodeBlockList (lengthPrependedBlocks q))
  decodeQuery req := decodeLPWord n L req.2
  decodeQuery_eq_some_iff := by
    rintro ⟨⟨⟩, w⟩ q
    constructor
    · intro hdec
      unfold decodeLPWord at hdec
      dsimp only at hdec
      split_ifs at hdec with h
      obtain rfl := Option.some.inj hdec.symm
      refine Prod.ext rfl ?_
      have hblocks :
          lengthPrependedBlocks
            ⟨⟨(BitString.toBlocks n w).length, h.1⟩,
              fun i => (BitString.toBlocks n w)[i.val]'i.isLt⟩ =
          BitString.toBlocks n w := by
        refine List.ext_getElem ?_ fun i _ _ => by simp [lengthPrependedBlocks]
        rw [length_lengthPrependedBlocks]
      have hmod : n ∣ w.length := ⟨_, by rw [Nat.mul_comm]; exact h.2⟩
      rw [hblocks, encodeBlockList, BitString.flatMap_ofFn_toBlocks hmod]
    · intro henc
      rcases Prod.mk.inj henc with ⟨-, rfl⟩
      rcases q with ⟨k, f⟩
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have hL0 : L = 0 := by simpa using hL
        subst hL0
        have hk0 : k = ⟨0, Nat.zero_lt_one⟩ := Fin.ext (by omega)
        subst hk0
        have hnil : encodeBlockList (lengthPrependedBlocks ⟨⟨0, Nat.zero_lt_one⟩, f⟩) = [] := by
          simp [lengthPrependedBlocks, encodeBlockList]
        rw [hnil]
        have hcond0 : (BitString.toBlocks 0 ([] : List Bool)).length < 0 + 1 ∧
            ([] : List Bool).length =
              (BitString.toBlocks 0 ([] : List Bool)).length * 0 := by
          simp [BitString.length_toBlocks]
        unfold decodeLPWord
        dsimp only
        rw [dite_eq_left_of_eq_true (eq_true hcond0), Option.some.injEq]
        exact lengthPrependedBlocks_injective
          (by simp [lengthPrependedBlocks, BitString.length_toBlocks])
      · let bs := lengthPrependedBlocks ⟨k, f⟩
        have hpad : BitString.toBlocks n (encodeBlockList bs) = bs :=
          toBlocks_encodeBlockList hn bs
        have hbsLen : bs.length = k.val := length_lengthPrependedBlocks ⟨k, f⟩
        have hcond :
            (BitString.toBlocks n (encodeBlockList bs)).length <
              L + 1 ∧
            (encodeBlockList bs).length =
              (BitString.toBlocks n (encodeBlockList bs)).length * n := by
          rw [hpad, length_encodeBlockList, hbsLen]
          exact ⟨k.isLt, rfl⟩
        change decodeLPWord n L (encodeBlockList bs) = some ⟨k, f⟩
        unfold decodeLPWord
        dsimp only
        rw [dite_eq_left_of_eq_true (eq_true hcond), Option.some.injEq]
        apply lengthPrependedBlocks_injective
        refine Eq.trans ?_ hpad
        refine List.ext_getElem ?_ fun i _ _ => by
          simp only [lengthPrependedBlocks, List.getElem_ofFn]
        rw [length_lengthPrependedBlocks]
  encodeReply _ := ⟨List.ofFn, List.ofFn_injective⟩

private theorem lpBlockValid_eq_isSome_lengthPrependedCodec {L : ℕ → ℕ} {n : ℕ}
    (hL : L n < 2 ^ n) (query : List Bool) :
    lpBlockValid L n query =
      ((lengthPrependedCodec n (L n) hL).decodeQuery ((), query)).isSome := by
  have hiff : lpBlockValid L n query = true ↔ (BitString.toBlocks n query).length < L n + 1 ∧
      query.length = (BitString.toBlocks n query).length * n := by
    simp only [lpBlockValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      BitString.length_toBlocks]
    constructor
    · rintro ⟨hmod, hle⟩
      exact ⟨Nat.lt_succ_of_le (Nat.div_le_of_le_mul (by rwa [Nat.mul_comm])),
        (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)).symm⟩
    · rintro ⟨hlt, hmul⟩
      rw [hmul]
      exact ⟨Nat.mul_mod_left _ _, Nat.mul_le_mul_right n (Nat.lt_succ_iff.mp hlt)⟩
  rw [Bool.eq_iff_iff, hiff]
  dsimp only [lengthPrependedCodec, decodeLPWord]
  split_ifs with h
  exacts [iff_of_true h rfl, iff_of_false h Bool.false_ne_true]

private noncomputable def probCbcQueryRun {α : Type} {n ℓ : ℕ}
    (o : CBCInput n ℓ → BitString n) :
    ProbOracleComp (CBCOracleSpec n ℓ) α → PMF (α × List (CBCInput n ℓ))
  | .pure a => PMF.pure (a, [])
  | .liftBind (.inl k) cont =>
    (ProbComp.unifOracle k).bind fun c => probCbcQueryRun o (cont c)
  | .liftBind (.inr q) cont =>
    (probCbcQueryRun o (cont (o q))).map fun (a, qs) => (a, q :: qs)

private theorem cbcQueryRun_fixCoins_mem_support {α : Type} {n ℓ : ℕ}
    (o : CBCInput n ℓ → BitString n) :
    ∀ (P : ProbOracleComp (CBCOracleSpec n ℓ) α) (ω : ProbOracleComp.Coins P),
      ω ∈ (ProbOracleComp.coinLaw P).support →
      cbcQueryRun o (ProbOracleComp.fixCoins P ω) ∈ (probCbcQueryRun o P).support
  | .pure a, _, _ => by simp [ProbOracleComp.fixCoins, probCbcQueryRun]
  | .liftBind (.inl k) cont, ⟨c, ω'⟩, hω => by
    let p : Σ i : Fin (k + 1), ProbOracleComp.Coins (cont i) := ⟨c, ω'⟩
    have hmem : p ∈ ((ProbComp.unifOracle k).bind fun c =>
        (ProbOracleComp.coinLaw (cont c)).map fun ω => ⟨c, ω⟩).support := by
      rwa [← ProbOracleComp.coinLaw_liftBind_inl]
    obtain ⟨c', hc', hmap⟩ := (PMF.mem_support_bind_iff _ _ _).mp hmem
    obtain ⟨ω₀, hω₀, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hmap
    rcases Sigma.mk.inj_iff.mp heq.symm with ⟨rfl, heq'⟩
    cases eq_of_heq heq'.symm
    exact (PMF.mem_support_bind_iff _ _ _).mpr
      ⟨c, hc', cbcQueryRun_fixCoins_mem_support o (cont c) ω' hω₀⟩
  | .liftBind (.inr q) cont, f, hω => by
    let f' : (y : BitString n) → ProbOracleComp.Coins (cont y) := f
    have hne : (ProbOracleComp.coinLaw (.liftBind (.inr q) cont)) f' ≠ 0 :=
      (PMF.mem_support_iff _ _).mp hω
    rw [ProbOracleComp.coinLaw_liftBind_inr] at hne
    have hmem := (PMF.mem_support_pi_iff _ _).mp ((PMF.mem_support_iff _ _).mpr hne)
    exact (PMF.mem_support_map_iff _ _ _).mpr
      ⟨_, cbcQueryRun_fixCoins_mem_support o (cont (o q)) (f' (o q)) (hmem (o q)), rfl⟩

private def cbcOracleWord {n ℓ : ℕ} (hn : 0 < n) (o : CBCInput n ℓ → BitString n)
    (w : List Bool) : List Bool :=
  match (cbcInputCodec n ℓ hn).decodeQuery ((), w) with
  | some q => List.ofFn (o q)
  | none => []

private theorem exists_wordQueryRunDist_of_probCbcQueryRun {α : Type} {n ℓ : ℕ}
    (hn : 0 < n) (o : CBCInput n ℓ → BitString n) :
    ∀ (program : WordOracleComp Unit α) {out : α × List (CBCInput n ℓ)},
      out ∈ (probCbcQueryRun o ((cbcInputCodec n ℓ hn).adapt program)).support →
      ∃ result ∈ (wordQueryRunDist (cbcOracleWord hn o) program).support,
        ∀ q ∈ out.2, ((cbcInputCodec n ℓ hn).encodeQuery q).2 ∈ result.2
  | .pure a, _, hout => by
    obtain rfl := (PMF.mem_support_pure_iff _ _).mp hout
    exact ⟨(a, []), by simp [wordQueryRunDist], fun _ hq => by cases hq⟩
  | .liftBind (.inl k) cont, _, hout => by
    obtain ⟨c, hc, hcont⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    obtain ⟨res, hres, hsub⟩ :=
      exists_wordQueryRunDist_of_probCbcQueryRun hn o (cont c) hcont
    exact ⟨res, (PMF.mem_support_bind_iff _ _ _).mpr ⟨c, hc, hres⟩, hsub⟩
  | .liftBind (.inr ((), w)) cont, _, hout => by
    change _ ∈ (probCbcQueryRun o
      ((cbcInputCodec n ℓ hn).adapt (ProbOracleComp.query ((), w) >>= cont))).support at hout
    rw [OracleCodec.adapt_bind, OracleCodec.adapt_query] at hout
    cases hdec : (cbcInputCodec n ℓ hn).decodeQuery ((), w) with
    | none =>
      rw [OracleCodec.wordOracle_of_decodeQuery_eq_none _ _ hdec, pure_bind] at hout
      obtain ⟨⟨a, log⟩, hres, hsub⟩ :=
        exists_wordQueryRunDist_of_probCbcQueryRun hn o (cont []) hout
      refine ⟨(a, w :: log), ?_, fun q hq => List.mem_cons_of_mem w (hsub q hq)⟩
      simp only [wordQueryRunDist, cbcOracleWord, hdec, PMF.mem_support_map_iff]
      exact ⟨(a, log), hres, rfl⟩
    | some q₀ =>
      have henc : ((cbcInputCodec n ℓ hn).encodeQuery q₀).2 = w :=
        congrArg Prod.snd (((cbcInputCodec n ℓ hn).decodeQuery_eq_some_iff ((), w) q₀).mp hdec)
      have hadapt : ((cbcInputCodec n ℓ hn).wordOracle ProbOracleComp.query ((), w) >>= fun y =>
            (cbcInputCodec n ℓ hn).adapt (cont y)) =
          .liftBind (.inr q₀) (fun y => (cbcInputCodec n ℓ hn).adapt (cont (List.ofFn y))) := by
        rw [OracleCodec.wordOracle, hdec]
        simp only [cbcInputCodec, ProbOracleComp.query, OracleComp.query, map_eq_bind_pure_comp,
          Function.comp_def, Function.Embedding.coeFn_mk, bind_assoc, pure_bind]
        rfl
      rw [hadapt] at hout
      obtain ⟨⟨a', qs⟩, hcont, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
      obtain ⟨⟨a, log⟩, hres, hsub⟩ :=
        exists_wordQueryRunDist_of_probCbcQueryRun hn o (cont (List.ofFn (o q₀))) hcont
      refine ⟨(a, w :: log), ?_, fun q hq => ?_⟩
      · simp only [wordQueryRunDist, cbcOracleWord, hdec, PMF.mem_support_map_iff]
        exact ⟨(a, log), hres, rfl⟩
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact henc ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem w (hsub q hq)

private theorem cbcQueryRun_length_le_of_isQueryBounded {n ℓ q : ℕ}
    (o : CBCInput n ℓ → BitString n) {tree : OracleComp (CBCOracleSpec n ℓ) Bool}
    (hq : tree.IsQueryBounded q) :
    (cbcQueryRun o tree).2.length ≤ q := by
  unfold OracleComp.IsQueryBounded at hq
  induction hq with
  | pure a k => simp
  | liftBind x cont k _ ih =>
    rw [cbcQueryRun_query_bind, List.length_cons]
    have htail := ih (o x)
    omega

private theorem cbcAdmissible_fixCoins_adapt {ℓ : ℕ → ℕ} {n Q : ℕ} (hn : 0 < n)
    {program : WordOracleComp Unit Bool} (hQ : program.IsQueryBounded Q)
    (hpf : IsPrefixFreeOn (cbcBlockValid ℓ n) n program)
    {ω : ProbOracleComp.Coins ((cbcInputCodec n (ℓ n) hn).adapt program)}
    (hω : ω ∈ (ProbOracleComp.coinLaw ((cbcInputCodec n (ℓ n) hn).adapt program)).support) :
    CBCAdmissible Q (ProbOracleComp.fixCoins ((cbcInputCodec n (ℓ n) hn).adapt program) ω) := by
  intro o
  have htreeQ :
      (ProbOracleComp.fixCoins ((cbcInputCodec n (ℓ n) hn).adapt program) ω).IsQueryBounded Q :=
    ProbOracleComp.isQueryBounded_fixCoins
      (OracleCodec.isQueryBounded_adapt (cbcInputCodec n (ℓ n) hn) hQ) ω
  refine ⟨?_, cbcQueryRun_length_le_of_isQueryBounded o htreeQ⟩
  obtain ⟨res, hres, hsub⟩ := exists_wordQueryRunDist_of_probCbcQueryRun hn o program
    (cbcQueryRun_fixCoins_mem_support o _ ω hω)
  have horacle (w : List Bool) : (cbcBlockValid ℓ n w = false → cbcOracleWord hn o w = []) ∧
      (cbcBlockValid ℓ n w = true → (cbcOracleWord hn o w).length = n) := by
    rw [cbcBlockValid_eq_isSome_cbcInputCodec hn, cbcOracleWord]
    cases (cbcInputCodec n (ℓ n) hn).decodeQuery ((), w) <;> simp
  have hwordPf :=
    hpf (cbcOracleWord hn o) (fun w => (horacle w).1) (fun w => (horacle w).2) res hres
  have hvalid (z : CBCInput n (ℓ n)) :
      cbcBlockValid ℓ n ((cbcInputCodec n (ℓ n) hn).encodeQuery z).2 = true := by
    rw [cbcBlockValid_eq_isSome_cbcInputCodec hn,
      show ((), ((cbcInputCodec n (ℓ n) hn).encodeQuery z).2) =
        (cbcInputCodec n (ℓ n) hn).encodeQuery z from rfl,
      OracleCodec.decodeQuery_encodeQuery, Option.isSome_some]
  intro x hx y hy hxy hpre
  have hneWord : ((cbcInputCodec n (ℓ n) hn).encodeQuery x).2 ≠
      ((cbcInputCodec n (ℓ n) hn).encodeQuery y).2 := fun heq =>
    hxy ((cbcInputCodec n (ℓ n) hn).encodeQuery_injective (Prod.ext rfl heq))
  exact hwordPf _ (hsub x hx) (hvalid x) _ (hsub y hy) (hvalid y) hneWord
    (hpre.flatMap List.ofFn)

/-! ### Section 4: Certified PRF Reductions and Concrete & Asymptotic PRF Security -/

/-- One CBC-MAC oracle query step: XOR the `n`-bit chaining block `state` with the next message
block, query the external block-function oracle, and truncate the reply to `n` bits. -/
def cbcMacStep (n : ℕ) :
    List (List Bool) × List Bool → WordOracleComp Unit (List (List Bool) × List Bool)
  | (blocks, state) =>
    (fun tag => (blocks.tail, tag)) <$>
      (List.take n <$>
        ProbOracleComp.query ((), List.zipWith xor state (blocks.headD [])))

/-- Compute `cbcMacWord` of `msg` from a word oracle using one `n`-truncated oracle query per
`n`-bit block of `msg`, starting from `List.replicate n false`. -/
def cbcMacQueries (n : ℕ) (msg : List Bool) : WordOracleComp Unit (List Bool) :=
  let blocks := BitString.listRows (msg.length / n) n msg
  Prod.snd <$>
    OracleComp.iterate blocks.length (cbcMacStep n) (blocks, List.replicate n false)

/-- Against any deterministic oracle `g`, `cbcMacQueries n msg` computes `cbcMacWord` for `g`. -/
theorem run_cbcMacQueries {n : ℕ} (g : List Bool → List Bool) (msg : List Bool) :
    (cbcMacQueries n msg).run (fun request => pure (g request.2)) =
      pure (cbcMacWord (fun _ x => g x) n [] msg) := by
  have hloop (xs : List (List Bool)) (state : List Bool) :
      ProbOracleComp.run (OracleComp.iterate xs.length (cbcMacStep n) (xs, state))
        (fun request => pure (g request.2)) =
      pure ([], xs.foldl (fun s b => (g (List.zipWith xor s b)).take n) state) := by
    induction xs generalizing state with
    | nil => rfl
    | cons m xs ih =>
      rw [List.length_cons, OracleComp.iterate_succ_bind, ProbOracleComp.run_bind]
      simp only [cbcMacStep, List.headD_cons, List.tail_cons, ProbOracleComp.run_map,
        ProbOracleComp.run_query, map_pure, pure_bind, List.foldl_cons]
      exact ih _
  rw [cbcMacQueries, ProbOracleComp.run_map, hloop, map_pure, cbcMacWord]

private theorem isOraclePPTOn_cbcMacQueries :
    IsOraclePPTOn (Operation := Unit) (encPair encUnary encBits) encBits
      (fun (n, msg) => cbcMacQueries n msg) := by
  let EIn := encPair encUnary encBits
  let EState := encPair (encList encBits) encBits
  let EStep := encPair EIn EState
  have hn : ComputableInPolyTime (fun a : ℕ × List Bool => a.1) EIn encUnary := by
    dsimp only [EIn]; fun_prop
  have hblocks : ComputableInPolyTime
      (fun a : ℕ × List Bool => BitString.listRows (a.2.length / a.1) a.1 a.2)
      EIn (encList encBits) :=
    ComputableInPolyTime.bitsRowsWithInput
      (by dsimp only [EIn]; fun_prop) hn (by dsimp only [EIn]; fun_prop)
  have hcount : ComputableInPolyTime
      (fun a : ℕ × List Bool => (BitString.listRows (a.2.length / a.1) a.1 a.2).length)
      EIn encUnary :=
    (ComputableInPolyTime.length_list encBits).comp hblocks
  have hinit : ComputableInPolyTime
      (fun a : ℕ × List Bool =>
        (BitString.listRows (a.2.length / a.1) a.1 a.2, List.replicate a.1 false))
      EIn EState :=
    hblocks.prod ((ComputableInPolyTime.bitsReplicate false).comp hn)
  have hquery : IsOraclePPTOn (Operation := Unit) EStep encBits
      (fun p : (ℕ × List Bool) × (List (List Bool) × List Bool) =>
        List.take p.1.1 <$>
          ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
            ((), List.zipWith xor p.2.2 (p.2.1.headD []))) :=
    IsOraclePPTOn.query_take ()
      (ComputableInPolyTime.bitsZipWithInput xor
        (by dsimp only [EStep, EIn, EState]; fun_prop)
        (by dsimp only [EStep, EIn, EState]; fun_prop))
      (by dsimp only [EStep, EIn, EState]; fun_prop)
  have hstep : IsOraclePPTOn EStep EState
      (fun p : (ℕ × List Bool) × (List (List Bool) × List Bool) => cbcMacStep p.1.1 p.2) :=
    hquery.map_with (f := fun p tag => (p.2.1.tail, tag))
      (by
        have hp := ComputableInPolyTime.id' (encIn := encPair EStep encBits)
        exact ((ComputableInPolyTime.tail (encA := encBits) (encL := encList encBits)).comp
          hp.fst'.snd'.fst').prod hp.snd')
  have hloop := IsOraclePPTOn.iterateWith_of_bounded_growth
    (stateEncoding := EState)
    (initial := fun a : ℕ × List Bool =>
      (BitString.listRows (a.2.length / a.1) a.1 a.2, List.replicate a.1 false))
    (count := fun a => (BitString.listRows (a.2.length / a.1) a.1 a.2).length)
    (step := fun a state => cbcMacStep a.1 state)
    hcount hinit hstep (growth := fun a => a.1)
    hn.polyBounded
    (fun a (blocks, state) next hnext => by
      obtain ⟨tag, htag, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
      obtain ⟨raw, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp htag
      have htailLen : (encList encBits blocks.tail).length ≤ (encList encBits blocks).length :=
        ((List.tail_sublist blocks).flatMap (frame ∘ encBits)).length_le
      have htake := List.length_take_le a.1 raw
      simp only [EState, length_encPair, encBits_apply]
      omega)
  exact IsOraclePPTOn.map hloop (f := Prod.snd) (by dsimp only [EState]; fun_prop)

private theorem length_le_of_mem_support_cbcMacQueries (n : ℕ) (msg reply : List Bool)
    (hreply : reply ∈ OracleComp.support (cbcMacQueries n msg)) :
    reply.length ≤ n := by
  unfold cbcMacQueries at hreply
  dsimp only at hreply
  obtain ⟨⟨_, tag⟩, hstate, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
  exact OracleComp.iterate_invariant
    (invariant := fun _ (_, s) => s.length ≤ n)
    (by simp)
    (fun _ _ _ _ next hnext => by
      obtain ⟨c, hc, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
      obtain ⟨raw, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hc
      exact List.length_take_le n raw)
    _ hstate

/-- Answer a word request to basic CBC-MAC on `cbcBlockValid ℓ n`: valid nonempty bounded
whole-block messages are evaluated block-by-block via `cbcMacQueries n`, and invalid requests
receive `[]` without querying. -/
@[expose]
def cbcMacQuery (ℓ : ℕ → ℕ) (n : ℕ) (request : Unit × List Bool) :
    WordOracleComp Unit (List Bool) :=
  if cbcBlockValid ℓ n request.2 then cbcMacQueries n request.2 else pure []

/-- Certified PRF reduction for basic CBC-MAC ([BonehShoup2023], Section 6.4.1, proof of Theorem
6.3, adversary `B`, printed pp. 227–228): run `adversary n aux`, answering each `cbcBlockValid ℓ n`
message with `cbcMacQueries n`. -/
@[expose]
def cbcMacToPrfDistinguisher (ℓ : ℕ → ℕ) (adversary : OracleDistinguisher) :
    OracleDistinguisher := fun n aux =>
  OracleComp.interpret
    (OracleComp.sumHandler (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
      (cbcMacQuery ℓ n))
    (adversary n aux)

/-- Answer a word request to length-prepended CBC-MAC on `lpBlockValid L n`: valid whole-block
messages of at most `L n` blocks prepend `BitString.lowBits n (msg.length / n)` and run
`cbcMacQueries n`; invalid requests receive `[]` without querying. -/
@[expose]
def lengthPrependedQuery (L : ℕ → ℕ) (n : ℕ) (request : Unit × List Bool) :
    WordOracleComp Unit (List Bool) :=
  if lpBlockValid L n request.2 then
    cbcMacQueries n (prependLengthWord n request.2)
  else
    pure []

/-- Certified PRF reduction for length-prepended CBC-MAC ([BonehShoup2023], Sections 6.4.1 and
6.6.1, Theorems 6.3 and 6.8, printed pp. 226–229 and 235–236): run `adversary n aux`, answering
each `lpBlockValid L n` message with `cbcMacQueries n (prependLengthWord n msg)`. -/
@[expose]
def lengthPrependedToPrfDistinguisher (L : ℕ → ℕ) (adversary : OracleDistinguisher) :
    OracleDistinguisher := fun n aux =>
  OracleComp.interpret
    (OracleComp.sumHandler (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
      (lengthPrependedQuery L n))
    (adversary n aux)

private theorem isOraclePPT_interpret_wordGuard
    {valid : ℕ → List Bool → Bool}
    (hvalid : ComputableInPolyTime (fun a : ℕ × List Bool => valid a.1 a.2)
      (encPair encUnary encBits) encBool)
    {call : ℕ × List Bool → WordOracleComp Unit (List Bool)}
    (hcall : IsOraclePPTOn (encPair encUnary encBits) encBits call)
    (hlen : ∀ n msg reply, reply ∈ OracleComp.support (call (n, msg)) → reply.length ≤ n)
    {handler : ℕ → Unit × List Bool → WordOracleComp Unit (List Bool)}
    (hdef : ∀ n req, handler n req = if valid n req.2 then call (n, req.2) else pure [])
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (fun n aux =>
      OracleComp.interpret
        (OracleComp.sumHandler (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
          (handler n))
        (adversary n aux)) := by
  let ECall := encPair (encPair encUnary encBits) (encPair (encFinEnum Unit) encBits)
  have hpair : ComputableInPolyTime
      (fun c : (ℕ × List Bool) × (Unit × List Bool) => (c.1.1, c.2.2))
      ECall (encPair encUnary encBits) := by
    dsimp only [ECall]; fun_prop
  have hhandler : IsOraclePPTOn ECall encBits
      (fun c : (ℕ × List Bool) × (Unit × List Bool) => handler c.1.1 c.2) := by
    have heq : (fun c : (ℕ × List Bool) × (Unit × List Bool) => handler c.1.1 c.2) =
        (fun c => if valid c.1.1 c.2.2 then
            (call ∘ (fun c : (ℕ × List Bool) × (Unit × List Bool) => (c.1.1, c.2.2))) c
          else ProbOracleComp.sample (pure [])) := by
      funext c
      rw [hdef]
      cases valid c.1.1 c.2.2 <;> rfl
    rw [heq]
    exact IsOraclePPTOn.cond (hvalid.comp hpair) (hcall.preprocess hpair)
      ((ComputableInPolyTime.const []).isPPTOn.isOraclePPTOn)
  refine (hadversary.on.interpret_preprocess_open' (operationEncoding := encFinEnum Unit)
    (handler := fun c => handler c.1) (prepare := id) (resources := fun c _ => c.1)
    ComputableInPolyTime.id' hhandler
    (by polytime) fun caller request reply hreply => ?_).isOraclePPT
  rw [hdef] at hreply
  split_ifs at hreply
  · exact hlen caller.1 request.2 reply hreply
  · rw [OracleComp.eq_of_mem_supportWith_pure hreply]
    exact Nat.zero_le _

/-- `cbcMacToPrfDistinguisher ℓ adversary` is uniform strict oracle PPT whenever `ℓ` is unary
polynomial-time and `adversary` is uniform strict oracle PPT. -/
theorem isOraclePPT_cbcMacToPrfDistinguisher {ℓ : ℕ → ℕ}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (cbcMacToPrfDistinguisher ℓ adversary) :=
  isOraclePPT_interpret_wordGuard (computableInPolyTime_cbcBlockValid hℓ)
    isOraclePPTOn_cbcMacQueries length_le_of_mem_support_cbcMacQueries
    (fun _ _ => rfl) hadversary

private theorem isOraclePPTOn_cbcMacQueries_prependLengthWord :
    IsOraclePPTOn (Operation := Unit) (encPair encUnary encBits) encBits
      (fun a : ℕ × List Bool => cbcMacQueries a.1 (prependLengthWord a.1 a.2)) :=
  have hn : ComputableInPolyTime (fun a : ℕ × List Bool => a.1)
      (encPair encUnary encBits) encUnary := by fun_prop
  isOraclePPTOn_cbcMacQueries.preprocess
    (hn.prod (computableInPolyTime_prependLengthWord_with hn (by fun_prop)))

/-- `lengthPrependedToPrfDistinguisher L adversary` is uniform strict oracle PPT whenever `L` is
unary polynomial-time and `adversary` is uniform strict oracle PPT. -/
theorem isOraclePPT_lengthPrependedToPrfDistinguisher {L : ℕ → ℕ}
    (hL : ComputableInPolyTime L encUnary encUnary) {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (lengthPrependedToPrfDistinguisher L adversary) :=
  isOraclePPT_interpret_wordGuard (computableInPolyTime_lpBlockValid hL)
    isOraclePPTOn_cbcMacQueries_prependLengthWord
    (fun n msg reply h =>
      length_le_of_mem_support_cbcMacQueries n (prependLengthWord n msg) reply h)
    (fun _ _ => rfl) hadversary

private theorem cbcMacWord_prfOracle_eq {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query : List Bool, query.length = key.length →
      (family key query).length = key.length)
    {n : ℕ} {key : List Bool} (hkey : key.length = n) (msg : List Bool) :
    cbcMacWord (fun _ x => prfOracle family n key x) n [] msg = cbcMacFamily family key msg := by
  have hstep : ∀ (ms : List (List Bool)) (state : List Bool),
      state.length = n → (∀ m ∈ ms, m.length = n) →
      ms.foldl (fun s b => (prfOracle family n key (List.zipWith xor s b)).take n) state =
        ms.foldl (fun s b => (family key (List.zipWith xor s b)).take n) state := by
    intro ms
    induction ms with
    | nil => intros; rfl
    | cons m ms ih =>
      intro state hstate hms
      have hm : m.length = n := hms m List.mem_cons_self
      have hxor : (List.zipWith xor state m).length = n := by simp [hstate, hm]
      have hfamLen : (family key (List.zipWith xor state m)).length = n :=
        hkey ▸ hlen key _ (hxor.trans hkey.symm)
      simp only [List.foldl_cons, prfOracle, hxor, ↓reduceIte]
      exact ih _ (by simp [hfamLen]) fun b hb => hms b (List.mem_cons_of_mem _ hb)
  rw [cbcMacFamily, hkey, cbcMacWord, cbcMacWord]
  exact hstep _ _ List.length_replicate fun _ hm => BitString.length_of_mem_listRows hm

private theorem run_interpret_wordHandler {α : Type}
    (handler : Unit × List Bool → WordOracleComp Unit (List Bool))
    (oracle : Unit × List Bool → ProbComp (List Bool))
    (program : WordOracleComp Unit α) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun k => ProbOracleComp.sample (ProbComp.unifFin k)) handler)
      program).run oracle =
    program.run fun request => (handler request).run oracle := by
  rw [← OracleComp.substitute_eq_interpret, ← ProbOracleComp.simulate,
    ProbOracleComp.run_simulate]

private theorem eval_sampleKey_interpret_wordHandler {n : ℕ}
    (oracle₁ oracle₂ : List Bool → List Bool → List Bool)
    (handler : Unit × List Bool → WordOracleComp Unit (List Bool))
    (program : WordOracleComp Unit Bool)
    (hstep : ∀ key : List Bool, key.length = n → ∀ request : Unit × List Bool,
      (handler request).run (fun r => pure (oracle₁ key r.2)) = pure (oracle₂ key request.2)) :
    ProbComp.eval (do
      let key ← BitString.sampleList n
      (OracleComp.interpret
        (OracleComp.sumHandler (fun k => ProbOracleComp.sample (ProbComp.unifFin k)) handler)
        program).run fun r => pure (oracle₁ key r.2)) =
    ProbComp.eval (do
      let key ← BitString.sampleList n
      program.run fun r => pure (oracle₂ key r.2)) := by
  simp only [ProbComp.eval_bind, BitString.eval_sampleList, run_interpret_wordHandler]
  refine PMF.bind_congr_on_support _ _ _ fun key hkey => ?_
  have hkeyLen : key.length = n := BitString.length_of_mem_support_uniformList hkey
  exact congrArg (fun h => ProbComp.eval (program.run h)) (funext (hstep key hkeyLen))

/-- Against `prfRealGame id family`, `cbcMacToPrfDistinguisher ℓ adversary` has the exact output law
of `prfRealGameOn (cbcBlockValid ℓ) (cbcMacFamily family) adversary`. -/
theorem eval_prfRealGame_cbcMacToPrfDistinguisher
    {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query : List Bool, query.length = key.length →
      (family key query).length = key.length)
    (ℓ : ℕ → ℕ) (adversary : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (prfRealGame id family (cbcMacToPrfDistinguisher ℓ adversary) n) =
      ProbComp.eval (prfRealGameOn (cbcBlockValid ℓ) (cbcMacFamily family) adversary n) :=
  eval_sampleKey_interpret_wordHandler (prfOracle family n)
    (prfOracleOn (cbcBlockValid ℓ n) (cbcMacFamily family)) (cbcMacQuery ℓ n) (adversary n [])
    fun key hkey request => by
      unfold cbcMacQuery prfOracleOn
      by_cases hv : cbcBlockValid ℓ n request.2 = true <;>
        simp [hv, run_cbcMacQueries, cbcMacWord_prfOracle_eq hlen hkey]

/-- Against `prfRealGame id family`, `lengthPrependedToPrfDistinguisher L adversary` has the exact
output law of `prfRealGameOn (lpBlockValid L) (lengthPrependedCbcMacFamily family) adversary`. -/
theorem eval_prfRealGame_lengthPrependedToPrfDistinguisher
    {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query : List Bool, query.length = key.length →
      (family key query).length = key.length)
    (L : ℕ → ℕ) (adversary : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (prfRealGame id family (lengthPrependedToPrfDistinguisher L adversary) n) =
      ProbComp.eval
        (prfRealGameOn (lpBlockValid L) (lengthPrependedCbcMacFamily family) adversary n) :=
  eval_sampleKey_interpret_wordHandler (prfOracle family n)
    (prfOracleOn (lpBlockValid L n) (lengthPrependedCbcMacFamily family))
    (lengthPrependedQuery L n) (adversary n [])
    fun key hkey request => by
      unfold lengthPrependedQuery prfOracleOn lengthPrependedCbcMacFamily lengthPrependedCbcMacWord
      by_cases hv : lpBlockValid L n request.2 = true <;>
        simp [hv, hkey, run_cbcMacQueries, cbcMacWord_prfOracle_eq hlen hkey, cbcMacFamily]

private theorem interpret_pmf_pure_eq {Q α : Type} {spec : Q → Type} (f : (q : Q) → spec q) :
    ∀ tree : OracleComp spec α,
      OracleComp.interpret (fun q => PMF.pure (f q)) tree =
        PMF.pure (OracleComp.interpret (m := Id) f tree)
  | .pure _ => rfl
  | .liftBind q next => by
    change (OracleComp.interpret (fun q => PMF.pure (f q)) (OracleComp.query q >>= next)) = _
    rw [OracleComp.interpret_bind, OracleComp.interpret_query]
    simp only [PMF.monad_bind_eq_bind, PMF.pure_bind]
    exact interpret_pmf_pure_eq f (next (f q))

private theorem eval_table_run_eq_coinLaw_bind {Q : Type} {w : ℕ} {τ : Type*} (μ : PMF τ)
    (table : τ → Q → BitString w) (program : ProbOracleComp (fun _ : Q => BitString w) Bool) :
    (μ.bind fun t => ProbComp.eval (program.run fun q => pure (table t q))) =
      μ.bind fun t =>
        ((ProbOracleComp.coinLaw program).map (ProbOracleComp.fixCoins program)).bind fun tree =>
          PMF.pure (OracleComp.interpret (m := Id) (table t) tree) := by
  refine congrArg (μ.bind) (funext fun t => ?_)
  rw [ProbOracleComp.eval_run]
  simp only [ProbComp.eval_pure, PMF.bind_map, Function.comp_def,
    ← fun ω => interpret_pmf_pure_eq (table t) (ProbOracleComp.fixCoins program ω)]
  exact (ProbOracleComp.bind_interpret_fixCoins program (table t)).symm

private theorem take_randomFunctionOracle_ofFn {n : ℕ} (g : BitString n → BitString n)
    (x : BitString n) : (randomFunctionOracle n g (List.ofFn x)).take n = List.ofFn (g x) := by
  simp [randomFunctionOracle, List.take_of_length_le (List.length_ofFn (f := g x)).le]

private theorem advantage_le_of_abs_toReal_le (p q : Game) {δ : ℝ≥0}
    (h : |(p true).toReal - (q true).toReal| ≤ (δ : ℝ)) :
    Game.advantage p q ≤ δ := by
  rwa [← NNReal.coe_le_coe, Game.coe_advantage]

private def emptyWordCodec (w : ℕ) : OracleCodec Unit (Fin 0) (fun _ => BitString w) where
  encodeQuery := Fin.elim0
  decodeQuery _ := none
  decodeQuery_eq_some_iff _ q := q.elim0
  encodeReply := Fin.elim0

private theorem eval_prfIdealGameOn_false (outLen : ℕ → ℕ) (adversary : OracleDistinguisher)
    (n : ℕ) :
    ProbComp.eval (prfIdealGameOn (fun _ _ => false) outLen adversary n) =
      ProbComp.eval ((adversary n []).run fun _ => pure []) := by
  rw [prfIdealGameOn, eval_prfIdealGameOn_eq_eager_of_codec (valid := fun _ => false)
    (emptyWordCodec (outLen n)) (fun _ => rfl) (fun q => q.elim0)]
  refine (congrArg (PMF.bind _) (funext fun table => ?_)).trans (PMF.bind_const _ _)
  exact congrArg ProbComp.eval (OracleCodec.run_adapt _ _ _)

/-- **Concrete computational PRF bound for prefix-free CBC-MAC** ([BonehShoup2023], Section 6.4.1,
Theorem 6.3, printed pp. 226–229): for any length-preserving `family`, block-count bound `ℓ`, and
distinguisher `adversary` that at parameter `n` makes at most `Q` queries and is prefix-free on
`cbcBlockValid ℓ n`, the domain-restricted PRF advantage of `cbcMacFamily family` is at most the
length-preserving PRF advantage of `cbcMacToPrfDistinguisher ℓ adversary` plus
`Q ^ 2 * (ℓ n) ^ 2 / (2 * 2 ^ n)` (equation (6.7) with `|X| = 2 ^ n`). -/
theorem advantage_cbcMac_le {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query : List Bool, query.length = key.length →
      (family key query).length = key.length)
    (ℓ : ℕ → ℕ) (adversary : OracleDistinguisher) {n Q : ℕ}
    (hQ : (adversary n []).IsQueryBounded Q)
    (hpf : IsPrefixFreeOn (cbcBlockValid ℓ n) n (adversary n [])) :
    Game.advantage
        (ProbComp.eval (prfRealGameOn (cbcBlockValid ℓ) (cbcMacFamily family) adversary n))
        (ProbComp.eval (prfIdealGameOn (cbcBlockValid ℓ) id adversary n)) ≤
      Game.advantage
        (ProbComp.eval (prfRealGame id family (cbcMacToPrfDistinguisher ℓ adversary) n))
        (ProbComp.eval (prfIdealGame id id (cbcMacToPrfDistinguisher ℓ adversary) n)) +
      (Q : ℝ≥0) ^ 2 * (ℓ n : ℝ≥0) ^ 2 / (2 * 2 ^ n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hfalse : cbcBlockValid ℓ 0 = fun _ => false := by
      funext msg
      simp only [cbcBlockValid, Nat.mul_zero, Nat.le_zero, Bool.and_eq_false_iff,
        decide_eq_false_iff_not]
      omega
    have hreal0 :
        ProbComp.eval (prfRealGameOn (cbcBlockValid ℓ) (cbcMacFamily family) adversary 0) =
        ProbComp.eval ((adversary 0 []).run fun _ => pure []) := by
      simp [prfRealGameOn, prfOracleOn, hfalse, BitString.eval_sampleList]
    have hideal0 : prfIdealGameOn (cbcBlockValid ℓ) id adversary 0 =
        prfIdealGameOn (fun _ _ => false) id adversary 0 := by
      simp only [prfIdealGameOn, hfalse]
    rw [hreal0, hideal0, eval_prfIdealGameOn_false, Game.advantage_self]
    exact zero_le
  · rw [← eval_prfRealGame_cbcMacToPrfDistinguisher hlen ℓ adversary n]
    refine (Game.advantage_triangle _ _ _).trans
      (add_le_add le_rfl (advantage_le_of_abs_toReal_le _ _ ?_))
    let codec := cbcInputCodec n (ℓ n) hn
    let P := codec.adapt (adversary n [])
    let D : PMF (OracleComp (CBCOracleSpec n (ℓ n)) Bool) :=
      (ProbOracleComp.coinLaw P).map (ProbOracleComp.fixCoins P)
    have hurfEq : ProbComp.eval (prfIdealGame id id (cbcMacToPrfDistinguisher ℓ adversary) n) =
        (PMF.uniformOfFintype (BitString n → BitString n)).bind fun g =>
          D.bind fun tree => PMF.pure ((cbcQueryRun (cbcMacFinite g) tree).1) := by
      have hrunG (g : BitString n → BitString n) :
          ProbComp.eval ((cbcMacToPrfDistinguisher ℓ adversary n []).run
            fun req => pure (randomFunctionOracle n g req.2)) =
          ProbComp.eval (P.run fun q => pure (cbcMacFinite g q)) := by
        rw [cbcMacToPrfDistinguisher, run_interpret_wordHandler, OracleCodec.run_adapt]
        refine congrArg (fun h => ProbComp.eval ((adversary n []).run h)) (funext fun req => ?_)
        rcases req with ⟨⟨⟩, w⟩
        rw [cbcMacQuery, cbcBlockValid_eq_isSome_cbcInputCodec hn, OracleCodec.wordOracle]
        cases hdec : codec.decodeQuery ((), w) with
        | none => simp
        | some q =>
          have henc : w = encodeBlockList (cbcInputBlocks q) :=
            (congrArg Prod.snd ((codec.decodeQuery_eq_some_iff ((), w) q).mp hdec)).symm
          have hword : cbcMacWord (fun _ x => randomFunctionOracle n g x) n [] w =
              List.ofFn (cbcMacFinite g q) := by
            rw [cbcMacWord_eq_ofFn_cbcMacBlocks (take_randomFunctionOracle_ofFn g),
              henc, toBlocks_encodeBlockList hn, cbcMacFinite]
          simp [codec, cbcInputCodec, run_cbcMacQueries, hword]
      simp only [prfIdealGame, id_eq, ProbComp.eval_bind, ProbComp.eval_uniform, hrunG]
      rw [eval_table_run_eq_coinLaw_bind]
      simp only [D, cbcQueryRun_fst]
    have hidealEq : ProbComp.eval (prfIdealGameOn (cbcBlockValid ℓ) id adversary n) =
        (PMF.uniformOfFintype (CBCInput n (ℓ n) → BitString n)).bind fun f =>
          D.bind fun tree => PMF.pure ((cbcQueryRun f tree).1) := by
      rw [prfIdealGameOn, id_eq, eval_prfIdealGameOn_eq_eager_of_codec codec
        (cbcBlockValid_eq_isSome_cbcInputCodec hn) (fun _ => rfl),
        eval_table_run_eq_coinLaw_bind]
      simp only [P, D, cbcQueryRun_fst]
    rw [hurfEq, hidealEq]
    simpa only [cbcUniformFunctionSuccess, cbcIdealSuccess, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast,
      NNReal.coe_ofNat] using abs_cbcUniformFunctionSuccess_sub_cbcIdealSuccess_le n Q (ℓ n) D
        fun tree htree => by
          obtain ⟨ω, hω, rfl⟩ :=
            (PMF.mem_support_map_iff _ _ _).mp ((PMF.mem_support_iff _ _).mpr htree)
          exact cbcAdmissible_fixCoins_adapt hn hQ hpf hω

/-- **Concrete computational PRF bound for length-prepended CBC-MAC** ([BonehShoup2023], Section
6.4.1 Theorem 6.3 and Section 6.6.1 Method 1 via Section 6.6 Theorem 6.8, printed pp. 226–229 and
235–236): whenever `L n < 2 ^ n` and `adversary` makes at most `Q` queries at parameter
`n`, the variable-length PRF advantage of `lengthPrependedCbcMacFamily family` on `lpBlockValid L`
is at most the length-preserving PRF advantage of `lengthPrependedToPrfDistinguisher L adversary`
plus `Q ^ 2 * (L n + 1) ^ 2 / (2 * 2 ^ n)`. -/
theorem advantage_lengthPrependedCbcMac_le {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query : List Bool, query.length = key.length →
      (family key query).length = key.length)
    (L : ℕ → ℕ) (adversary : OracleDistinguisher) {n Q : ℕ}
    (hL : L n < 2 ^ n) (hQ : (adversary n []).IsQueryBounded Q) :
    Game.advantage
        (ProbComp.eval
          (prfRealGameOn (lpBlockValid L) (lengthPrependedCbcMacFamily family) adversary n))
        (ProbComp.eval (prfIdealGameOn (lpBlockValid L) id adversary n)) ≤
      Game.advantage
        (ProbComp.eval (prfRealGame id family (lengthPrependedToPrfDistinguisher L adversary) n))
        (ProbComp.eval (prfIdealGame id id (lengthPrependedToPrfDistinguisher L adversary) n)) +
      (Q : ℝ≥0) ^ 2 * ((L n : ℝ≥0) + 1) ^ 2 / (2 * 2 ^ n) := by
  rw [← eval_prfRealGame_lengthPrependedToPrfDistinguisher hlen L adversary n]
  refine (Game.advantage_triangle _ _ _).trans
    (add_le_add le_rfl (advantage_le_of_abs_toReal_le _ _ ?_))
  let codec := lengthPrependedCodec n (L n) hL
  let P := codec.adapt (adversary n [])
  let D : PMF (OracleComp (LengthPrependedSpec n (L n)) Bool) :=
    (ProbOracleComp.coinLaw P).map (ProbOracleComp.fixCoins P)
  have hurfEq :
      ProbComp.eval (prfIdealGame id id (lengthPrependedToPrfDistinguisher L adversary) n) =
      (PMF.uniformOfFintype (BitString n → BitString n)).bind fun g =>
        D.bind fun tree =>
          PMF.pure (OracleComp.interpret (m := Id)
            (lengthPrependedCbcMac g (blockCountBlock hL)) tree) := by
    have hrunG (g : BitString n → BitString n) :
        ProbComp.eval ((lengthPrependedToPrfDistinguisher L adversary n []).run
          fun req => pure (randomFunctionOracle n g req.2)) =
        ProbComp.eval (P.run fun q => pure (lengthPrependedCbcMac g (blockCountBlock hL) q)) := by
      rw [lengthPrependedToPrfDistinguisher, run_interpret_wordHandler, OracleCodec.run_adapt]
      refine congrArg (fun h => ProbComp.eval ((adversary n []).run h)) (funext fun req => ?_)
      rcases req with ⟨⟨⟩, w⟩
      rw [lengthPrependedQuery, lpBlockValid_eq_isSome_lengthPrependedCodec hL,
        OracleCodec.wordOracle]
      cases hdec : codec.decodeQuery ((), w) with
      | none => simp
      | some q =>
        have henc : w = encodeBlockList (lengthPrependedBlocks q) :=
          (congrArg Prod.snd ((codec.decodeQuery_eq_some_iff ((), w) q).mp hdec)).symm
        have hword : cbcMacWord (fun _ x => randomFunctionOracle n g x) n []
              (prependLengthWord n w) =
            List.ofFn (lengthPrependedCbcMac g (blockCountBlock hL) q) := by
          rcases Nat.eq_zero_or_pos n with rfl | hn
          · simp [cbcMacWord, BitString.listRows]
          · have hwDiv : w.length / n = q.1.val := by
              rw [henc, length_encodeBlockList, length_lengthPrependedBlocks,
                Nat.mul_div_cancel _ hn]
            have hprepEq : prependLengthWord n w =
                encodeBlockList (cbcInputBlocks (prependLength (blockCountBlock hL) q)) := by
              rw [prependLengthWord, hwDiv, ← ofFn_blockCountBlock hL q.1, henc]
              simp only [cbcInputBlocks_prependLength, encodeBlockList, List.flatMap_cons]
            rw [cbcMacWord_eq_ofFn_cbcMacBlocks (take_randomFunctionOracle_ofFn g),
              hprepEq, toBlocks_encodeBlockList hn, lengthPrependedCbcMac, cbcMacFinite]
        simp [codec, lengthPrependedCodec, run_cbcMacQueries, hword]
    simp only [prfIdealGame, id_eq, ProbComp.eval_bind, ProbComp.eval_uniform, hrunG]
    exact eval_table_run_eq_coinLaw_bind _ _ _
  have hidealEq : ProbComp.eval (prfIdealGameOn (lpBlockValid L) id adversary n) =
      (PMF.uniformOfFintype (LengthPrependedInput n (L n) → BitString n)).bind fun f =>
        D.bind fun tree => PMF.pure (OracleComp.interpret (m := Id) f tree) := by
    rw [prfIdealGameOn, id_eq, eval_prfIdealGameOn_eq_eager_of_codec codec
      (lpBlockValid_eq_isSome_lengthPrependedCodec hL) (fun _ => rfl),
      eval_table_run_eq_coinLaw_bind]
  rw [hurfEq, hidealEq]
  simpa only [lengthPrependedUniformFunctionSuccess, lengthPrependedIdealSuccess,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, NNReal.coe_div, NNReal.coe_mul,
    NNReal.coe_pow, NNReal.coe_add, NNReal.coe_one, NNReal.coe_natCast, NNReal.coe_ofNat]
    using abs_lengthPrependedUniformFunctionSuccess_sub_lengthPrependedIdealSuccess_le
      n Q (L n) (blockCountBlock_injective hL) D fun tree htree => by
        obtain ⟨ω, _, rfl⟩ :=
          (PMF.mem_support_map_iff _ _ _).mp ((PMF.mem_support_iff _ _).mpr htree)
        exact ProbOracleComp.isQueryBounded_fixCoins (OracleCodec.isQueryBounded_adapt codec hQ) ω

/-- **Prefix-free CBC-MAC is a prefix-free pseudorandom function** ([BonehShoup2023], Section
6.4.1, Theorem 6.3, printed pp. 226–229): for any `PseudorandomFunction family` and unary
polynomial-time block-count cap `ℓ : ℕ → ℕ`, basic CBC-MAC `cbcMacFamily family` is a
`PrefixFreePseudorandomFunctionOn (cbcBlockValid ℓ) id`. -/
theorem PseudorandomFunction.prefixFreePRF_cbcMac {family : List Bool → List Bool → List Bool}
    (hF : PseudorandomFunction family) {ℓ : ℕ → ℕ}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) :
    PrefixFreePseudorandomFunctionOn (cbcBlockValid ℓ) id (cbcMacFamily family) where
  polyTime := computableInPolyTime_cbcMacFamily hF.polyTime
  length_eq key query _ := length_cbcMacFamily hF.length_eq key query
  secure adversary hadv := by
    obtain ⟨hadversary, hpf⟩ := hadv
    obtain ⟨c, d, hbounds⟩ := hadversary.query_bounds
    let Q : ℕ → ℕ := fun n => c * (n + 2) ^ d
    have hQ (n : ℕ) : (adversary n []).IsQueryBounded (Q n) := by
      simpa only [Q, List.length_nil, Nat.add_zero] using (hbounds n []).1
    have hprf := hF.secure (cbcMacToPrfDistinguisher ℓ adversary)
      (isOraclePPT_cbcMacToPrfDistinguisher hℓ hadversary)
    negligible using fun n => advantage_cbcMac_le hF.length_eq ℓ adversary (hQ n) (hpf n)

/-- **Variable-length length-prepended CBC-MAC is a pseudorandom function** ([BonehShoup2023],
Section 6.4.1 Theorem 6.3, pp. 226–229, and Section 6.6.1 Method 1 via Section 6.6 Theorem 6.8,
pp. 235–236): for any `PseudorandomFunction family` and unary polynomial-time block-count cap
`L : ℕ → ℕ`, `lengthPrependedCbcMacFamily family` is a `PseudorandomFunctionOn (lpBlockValid L) id`
over whole-block messages of `0` to `L n` blocks (empty message included). -/
theorem PseudorandomFunction.prfOn_lengthPrependedCbcMac
    {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family)
    {L : ℕ → ℕ} (hL : ComputableInPolyTime L encUnary encUnary) :
    PseudorandomFunctionOn (lpBlockValid L) id (lengthPrependedCbcMacFamily family) where
  polyTime := computableInPolyTime_lengthPrependedCbcMacFamily hF.polyTime
  length_eq key query _ := length_lengthPrependedCbcMacFamily hF.length_eq key query
  secure adversary hadversary := by
    obtain ⟨c, d, hbounds⟩ := hadversary.query_bounds
    let Q : ℕ → ℕ := fun n => c * (n + 2) ^ d
    have hQ (n : ℕ) : (adversary n []).IsQueryBounded (Q n) := by
      simpa only [Q, List.length_nil, Nat.add_zero] using (hbounds n []).1
    have hprf := hF.secure (lengthPrependedToPrfDistinguisher L adversary)
      (isOraclePPT_lengthPrependedToPrfDistinguisher hL hadversary)
    negligible eventually hL.polynomiallyBounded.eventually_lt_two_pow.mono fun n hLn =>
      advantage_lengthPrependedCbcMac_le hF.length_eq L adversary hLn (hQ n)

private def restrictLengthQuery (inLen : ℕ → ℕ) (n : ℕ) (request : Unit × List Bool) :
    WordOracleComp Unit (List Bool) :=
  if request.2.length == inLen n then
    List.take n <$> ProbOracleComp.query request
  else
    pure []

private def restrictLengthDistinguisher (inLen : ℕ → ℕ) (adversary : OracleDistinguisher) :
    OracleDistinguisher := fun n aux =>
  OracleComp.interpret
    (OracleComp.sumHandler (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
      (restrictLengthQuery inLen n))
    (adversary n aux)

private theorem isOraclePPT_restrictLengthDistinguisher {inLen : ℕ → ℕ}
    (hinLen : ComputableInPolyTime inLen encUnary encUnary) {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (restrictLengthDistinguisher inLen adversary) :=
  isOraclePPT_interpret_wordGuard
    (valid := fun n msg => msg.length == inLen n)
    (call := fun a : ℕ × List Bool => List.take a.1 <$> ProbOracleComp.query ((), a.2))
    (handler := restrictLengthQuery inLen)
    (by
      have hin : ComputableInPolyTime (fun a : ℕ × List Bool => inLen a.1)
          (encPair encUnary encBits) encUnary := hinLen.comp (by fun_prop)
      polytime)
    (IsOraclePPTOn.query_take ()
      (request := fun a : ℕ × List Bool => a.2)
      (limit := fun a : ℕ × List Bool => a.1)
      (by fun_prop) (by fun_prop))
    (fun n _ _ hreply => by
      obtain ⟨raw, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
      exact List.length_take_le n raw)
    (fun _ _ => rfl) hadversary

private theorem mem_wordQueryRunDist_restrictLengthQuery {α : Type} {inLen : ℕ → ℕ} {n : ℕ}
    (oracle : List Bool → List Bool) :
    ∀ (program : WordOracleComp Unit α) {res : α × List (List Bool)},
      res ∈ (wordQueryRunDist oracle
        (ProbOracleComp.simulate (restrictLengthQuery inLen n) program)).support →
      ∀ w ∈ res.2, w.length = inLen n
  | .pure a, _, hmem, w, hw => by
    obtain rfl := (PMF.mem_support_pure_iff _ _).mp hmem
    cases hw
  | .liftBind (.inl k) cont, _, hmem, w, hw => by
    obtain ⟨c, _, hcont⟩ := (PMF.mem_support_bind_iff _ _ _).mp hmem
    exact mem_wordQueryRunDist_restrictLengthQuery oracle (cont c) hcont w hw
  | .liftBind (.inr ((), u)) cont, _, hmem, w, hw => by
    change _ ∈ (wordQueryRunDist oracle
      (ProbOracleComp.simulate (restrictLengthQuery inLen n)
        (ProbOracleComp.query ((), u) >>= cont))).support at hmem
    rw [ProbOracleComp.simulate_bind, ProbOracleComp.simulate_query, restrictLengthQuery] at hmem
    by_cases hu : (u.length == inLen n) = true
    · simp only [hu, ↓reduceIte] at hmem
      have hqStep : (List.take n <$> ProbOracleComp.query ((), u) >>= fun y =>
            ProbOracleComp.simulate (restrictLengthQuery inLen n) (cont y)) =
          .liftBind (.inr ((), u)) (fun raw =>
            ProbOracleComp.simulate (restrictLengthQuery inLen n) (cont (raw.take n))) := by
        simp only [ProbOracleComp.query, OracleComp.query, map_eq_bind_pure_comp,
          Function.comp_def, bind_assoc, pure_bind]
        rfl
      rw [hqStep] at hmem
      obtain ⟨⟨a, log⟩, hcont, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hmem
      rcases List.mem_cons.mp hw with rfl | hw
      · exact beq_iff_eq.mp hu
      · exact mem_wordQueryRunDist_restrictLengthQuery oracle (cont ((oracle u).take n)) hcont w hw
    · simp only [Bool.eq_false_iff.mpr hu, Bool.false_eq_true, ↓reduceIte, pure_bind] at hmem
      exact mem_wordQueryRunDist_restrictLengthQuery oracle (cont []) hmem w hw

private theorem restrictLengthDistinguisher_eq_simulate (inLen : ℕ → ℕ)
    (adversary : OracleDistinguisher) (n : ℕ) (aux : List Bool) :
    restrictLengthDistinguisher inLen adversary n aux =
      ProbOracleComp.simulate (restrictLengthQuery inLen n) (adversary n aux) := by
  rw [restrictLengthDistinguisher, ← OracleComp.substitute_eq_interpret, ← ProbOracleComp.simulate]

/-- Restricting to one input length makes every distinguisher prefix-free on valid queries. -/
private theorem isPrefixFreeOn_restrictLengthDistinguisher {valid : List Bool → Bool} {outLen : ℕ}
    (inLen : ℕ → ℕ) (adversary : OracleDistinguisher) (n : ℕ) :
    IsPrefixFreeOn valid outLen (restrictLengthDistinguisher inLen adversary n []) := by
  rw [restrictLengthDistinguisher_eq_simulate]
  intro oracle _ _ res hres x hx _ y hy _ hxy hpre
  exact hxy (hpre.eq_of_length
    ((mem_wordQueryRunDist_restrictLengthQuery oracle _ hres x hx).trans
      (mem_wordQueryRunDist_restrictLengthQuery oracle _ hres y hy).symm))

private theorem eval_prfRealGameOn_restrictLengthDistinguisher
    {valid : ℕ → List Bool → Bool} (inLen : ℕ → ℕ)
    {tagFamily : List Bool → List Bool → List Bool}
    (hlen : ∀ key query : List Bool, valid key.length query = true →
      (tagFamily key query).length = key.length)
    {n : ℕ} (hsub : ∀ w : List Bool, w.length = inLen n → valid n w = true)
    (adversary : OracleDistinguisher) :
    ProbComp.eval
      (prfRealGameOn valid tagFamily (restrictLengthDistinguisher inLen adversary) n) =
    ProbComp.eval (prfRealGame inLen tagFamily adversary n) :=
  eval_sampleKey_interpret_wordHandler (prfOracleOn (valid n) tagFamily)
    (prfOracle tagFamily (inLen n)) (restrictLengthQuery inLen n) (adversary n [])
    fun key hkey req => by
      unfold restrictLengthQuery prfOracleOn prfOracle
      by_cases hq : req.2.length = inLen n
      · have hv : valid n req.2 = true := hsub req.2 hq
        have htLen : (tagFamily key req.2).length = n :=
          hkey ▸ hlen key req.2 (hkey.symm ▸ hv)
        simp [hq, hv, ProbOracleComp.run_map, ProbOracleComp.run_query,
          List.take_of_length_le htLen.le]
      · simp [hq]

private theorem lookup_map_take {n : ℕ} (q : List Bool) :
    ∀ cache : List (List Bool × List Bool),
      (cache.map fun (k, v) => (k, v.take n)).lookup q = (cache.lookup q).map (List.take n)
  | [] => rfl
  | (k, v) :: rest => by
    simp only [List.map_cons, List.lookup_cons]
    cases q == k
    · exact lookup_map_take q rest
    · rfl

private theorem eval_prfIdealGameOn_restrictLengthDistinguisher
    {valid : ℕ → List Bool → Bool} (inLen : ℕ → ℕ) {n : ℕ}
    (hsub : ∀ w : List Bool, w.length = inLen n → valid n w = true)
    (adversary : OracleDistinguisher) :
    ProbComp.eval (prfIdealGameOn valid id (restrictLengthDistinguisher inLen adversary) n) =
      ProbComp.eval (prfIdealGame inLen id adversary n) := by
  rw [← eval_prfIdealGameOn_length_eq]
  simp only [prfIdealGameOn, id_eq, ProbComp.eval_map, restrictLengthDistinguisher_eq_simulate,
    ProbOracleComp.eval_run_interpret]
  rw [ProbOracleComp.interpret_simulate, ← ProbOracleComp.runWith_eq_run_interpret,
    ← ProbOracleComp.runWith_eq_run_interpret]
  let rep : List (List Bool × List Bool) → List (List Bool × List Bool) :=
    List.map fun (k, v) => (k, v.take n)
  have hsim := ProbOracleComp.runWith_map_state
    (oracle := fun req =>
      OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (fun r state => (cachedRandomFunctionOracle (valid n) n r.2 state).eval))
        (restrictLengthQuery inLen n req))
    (oracle' := fun req s =>
      (cachedRandomFunctionOracle (fun q => q.length == inLen n) n req.2 s).eval)
    (represent := rep)
    (step := fun req cache => by
      change (StateT.run (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
            (fun r state => (cachedRandomFunctionOracle (valid n) n r.2 state).eval))
          (restrictLengthQuery inLen n req)) cache).map _ = _
      rw [← ProbOracleComp.runWith_eq_run_interpret]
      unfold restrictLengthQuery cachedRandomFunctionOracle cachedSamplerOracle
      by_cases hq : req.2.length = inLen n
      · have hv : valid n req.2 = true := hsub req.2 hq
        simp only [hq, beq_self_eq_true, ↓reduceIte, hv, ProbOracleComp.runWith_map,
          ProbOracleComp.runWith_query, ProbComp.eval_memoize,
          BitString.eval_sampleList, PMF.map_comp]
        rw [memoize, memoize, lookup_map_take]
        cases cache.lookup req.2 with
        | some v => simp [rep, PMF.pure_map]
        | none =>
          simp only [← PMF.bind_pure_comp, pmf_norm]
          refine PMF.bind_congr_on_support _ _ _ fun v hvMem => ?_
          have hvLen : v.length = n := BitString.length_of_mem_support_uniformList hvMem
          simp [rep, List.take_of_length_le hvLen.le]
      · simp [hq, ProbOracleComp.runWith_pure, ProbComp.eval_pure])
    (adversary n []) []
  have hfst := congrArg (PMF.map Prod.fst) hsim
  simpa only [PMF.map_comp, Function.comp_def, rep, List.map_nil] using hfst

/-- **Fixed-block-count CBC-MAC is a pseudorandom function** ([BonehShoup2023], Section 6.4.1,
Theorem 6.3, printed pp. 226–229, specialized to fixed positive block count `ℓ n`): for any
`PseudorandomFunction family` and unary polynomial-time `ℓ` with `∀ n, 0 < ℓ n`, `cbcMacFamily
family` satisfies `PseudorandomFunctionOver (fun n => ℓ n * n) id`. -/
theorem PseudorandomFunction.prfOver_cbcMac {family : List Bool → List Bool → List Bool}
    (hF : PseudorandomFunction family) {ℓ : ℕ → ℕ}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) (hpos : ∀ n, 0 < ℓ n) :
    PseudorandomFunctionOver (fun n => ℓ n * n) id (cbcMacFamily family) where
  polyTime := computableInPolyTime_cbcMacFamily hF.polyTime
  length_eq key query _ := length_cbcMacFamily hF.length_eq key query
  secure adversary hadversary := by
    have hsec := (hF.prefixFreePRF_cbcMac hℓ).secure
      (restrictLengthDistinguisher (fun n => ℓ n * n) adversary)
      ⟨isOraclePPT_restrictLengthDistinguisher (by polytime) hadversary,
        fun n => isPrefixFreeOn_restrictLengthDistinguisher _ adversary n⟩
    refine negligible_of_eventually_le hsec ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hsub (w : List Bool) (hw : w.length = ℓ n * n) : cbcBlockValid ℓ n w = true := by
      simp [cbcBlockValid, hw, hpos n, Nat.pos_of_ne_zero (by omega : n ≠ 0), Nat.mul_mod_left]
    rw [← eval_prfRealGameOn_restrictLengthDistinguisher (fun m => ℓ m * m)
      (fun key _ _ => length_cbcMacFamily hF.length_eq key _) hsub adversary,
      ← eval_prfIdealGameOn_restrictLengthDistinguisher (fun m => ℓ m * m) hsub adversary]

/-- **Fixed-block-count length-prepended CBC-MAC is a pseudorandom function**: for any
`PseudorandomFunction family` and unary polynomial-time block-count schedule `k : ℕ → ℕ` (including
`k n = 0` empty messages), `lengthPrependedCbcMacFamily family` satisfies
`PseudorandomFunctionOver (fun n => k n * n) id`. -/
theorem PseudorandomFunction.prfOver_lengthPrependedCbcMac
    {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family)
    {k : ℕ → ℕ} (hk : ComputableInPolyTime k encUnary encUnary) :
    PseudorandomFunctionOver (fun n => k n * n) id (lengthPrependedCbcMacFamily family) where
  polyTime := computableInPolyTime_lengthPrependedCbcMacFamily hF.polyTime
  length_eq key query _ := length_lengthPrependedCbcMacFamily hF.length_eq key query
  secure adversary hadversary := by
    have hsec := (hF.prfOn_lengthPrependedCbcMac hk).secure
      (restrictLengthDistinguisher (fun n => k n * n) adversary)
      (isOraclePPT_restrictLengthDistinguisher (by polytime) hadversary)
    refine hsec.congr fun n => ?_
    dsimp only
    have hsub (w : List Bool) (hw : w.length = k n * n) : lpBlockValid k n w = true := by
      simp [lpBlockValid, hw, Nat.mul_mod_left]
    rw [eval_prfRealGameOn_restrictLengthDistinguisher (fun m => k m * m)
      (fun key _ _ => length_lengthPrependedCbcMacFamily hF.length_eq key _) hsub adversary,
      eval_prfIdealGameOn_restrictLengthDistinguisher (fun m => k m * m) hsub adversary]

/-! ### Section 5: Adaptive Chosen-Message MAC Security (`SUFCMA` and `EUFCMA`) -/

/-- Pair-logging tagging oracle for a deterministic keyed family `tagFamily` on message domain
`valid n` ([BonehShoup2023], Section 6.1, Attack Game 6.1, printed p. 218): valid messages return
`tagFamily sk msg` and record `(msg, tag)`; invalid requests receive `[]` without recording. -/
@[expose]
def macSigningPairOracleOn (valid : ℕ → List Bool → Bool)
    (tagFamily : List Bool → List Bool → List Bool) (n : ℕ) (sk : List Bool)
    (request : Unit × List Bool) :
    StateT (List (List Bool × List Bool)) ProbComp (List Bool) :=
  fun issued =>
    if valid n request.2 then
      let tag := tagFamily sk request.2
      pure (tag, (request.2, tag) :: issued)
    else
      pure ([], issued)

/-- Message-logging tagging oracle for a deterministic keyed family `tagFamily` on `valid n`: valid
messages return `tagFamily sk msg` and record `msg`, while invalid requests receive `[]` without
recording. -/
@[expose]
def macSigningOracleOn (valid : ℕ → List Bool → Bool)
    (tagFamily : List Bool → List Bool → List Bool) (n : ℕ) (sk : List Bool)
    (request : Unit × List Bool) :
    StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queried =>
    if valid n request.2 then
      pure (tagFamily sk request.2, request.2 :: queried)
    else
      pure ([], queried)

/-- Strong (fresh-pair) adaptive chosen-message experiment on message domain `valid`
([BonehShoup2023], Section 6.1, Attack Game 6.1 and Definition 6.2, printed pp. 218–219): sample
`sk ← BitString.sampleList n`, run `adversary n []` with `macSigningPairOracleOn`, and accept a
valid `(msg, tag)` pair never returned by the tagging oracle such that `tagFamily sk msg == tag`. -/
@[expose]
noncomputable def macSufCmaGameOn (valid : ℕ → List Bool → Bool)
    (tagFamily : List Bool → List Bool → List Bool) (adversary : Forger) (n : ℕ) :
    ProbComp Bool := do
  let sk ← BitString.sampleList n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (macSigningPairOracleOn valid tagFamily n sk))
    (adversary n [])).run []
  let ((msg, tag), issued) := out
  return valid n msg && !issued.contains (msg, tag) && (tagFamily sk msg == tag)

/-- Ordinary (fresh-message) adaptive chosen-message experiment on message domain `valid`: sample
`sk ← BitString.sampleList n`, run `adversary n []` with `macSigningOracleOn`, and accept a valid
message `msg` never queried to the tagging oracle together with `tag = tagFamily sk msg`. -/
@[expose]
noncomputable def macEufCmaGameOn (valid : ℕ → List Bool → Bool)
    (tagFamily : List Bool → List Bool → List Bool) (adversary : Forger) (n : ℕ) :
    ProbComp Bool := do
  let sk ← BitString.sampleList n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (macSigningOracleOn valid tagFamily n sk))
    (adversary n [])).run []
  let ((msg, tag), queried) := out
  return valid n msg && !queried.contains msg && (tagFamily sk msg == tag)

/-- Strong existential unforgeability under adaptive chosen-message attack on message domain `valid`
([BonehShoup2023], Attack Game 6.1 and Definition 6.2, printed pp. 218–219). -/
@[expose]
def MACSUFCMAOn (valid : ℕ → List Bool → Bool)
    (tagFamily : List Bool → List Bool → List Bool) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (macSufCmaGameOn valid tagFamily adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT (encPair encBits encBits))

/-- Ordinary (fresh-message) existential unforgeability under adaptive chosen-message attack on
message domain `valid` ([BonehShoup2023], Attack Game 6.1 and Definition 6.2, printed pp. 218–219,
fresh-message form). -/
@[expose]
def MACEUFCMAOn (valid : ℕ → List Bool → Bool)
    (tagFamily : List Bool → List Bool → List Bool) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (macEufCmaGameOn valid tagFamily adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT (encPair encBits encBits))

/-- Because `tagFamily` is deterministic with a unique valid tag `tagFamily sk msg` per `(sk, msg)`,
`macSufCmaGameOn` and `macEufCmaGameOn` have identical output distributions. -/
theorem eval_macSufCmaGameOn_eq_macEufCmaGameOn (valid : ℕ → List Bool → Bool)
    (tagFamily : List Bool → List Bool → List Bool) (adversary : Forger) (n : ℕ) :
    ProbComp.eval (macSufCmaGameOn valid tagFamily adversary n) =
      ProbComp.eval (macEufCmaGameOn valid tagFamily adversary n) := by
  simp only [macSufCmaGameOn, macEufCmaGameOn, ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_congr_on_support _ _ _ fun sk _ => ?_
  let rep : List (List Bool) → List (List Bool × List Bool) :=
    List.map fun m => (m, tagFamily sk m)
  have hsim := ProbOracleComp.runWith_map_state
    (oracle := fun req s => (macSigningOracleOn valid tagFamily n sk req s).eval)
    (oracle' := fun req s => (macSigningPairOracleOn valid tagFamily n sk req s).eval)
    (represent := rep)
    (step := fun req queried => by
      unfold macSigningOracleOn macSigningPairOracleOn
      by_cases hv : valid n req.2 = true <;>
        simp [hv, rep, ProbComp.eval_pure])
    (adversary n []) []
  simp only [rep, List.map_nil] at hsim
  rw [ProbOracleComp.eval_run_interpret_eq_runWith,
    ProbOracleComp.eval_run_interpret_eq_runWith, ← hsim, PMF.bind_map]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨(msg, tag), queried⟩ _ => ?_
  simp only [Function.comp_apply]
  congr 1
  by_cases htag : tagFamily sk msg = tag
  · subst htag
    simp
  · simp [beq_eq_false_iff_ne.mpr htag]

/-- Because `tagFamily` is deterministic with a unique valid tag per `(sk, msg)`, strong and
ordinary adaptive chosen-message unforgeability on `valid` coincide. -/
theorem macSufCmaOn_iff_macEufCmaOn (valid : ℕ → List Bool → Bool)
    (tagFamily : List Bool → List Bool → List Bool) :
    MACSUFCMAOn valid tagFamily ↔ MACEUFCMAOn valid tagFamily := by
  constructor <;> intro hsec adversary hadversary <;>
    refine (hsec adversary hadversary).congr fun n => ?_ <;> dsimp only
  · rw [eval_macSufCmaGameOn_eq_macEufCmaGameOn]
  · rw [← eval_macSufCmaGameOn_eq_macEufCmaGameOn]

/-- Certified reduction turning an adaptive MAC forger on `valid` into a domain-restricted PRF
distinguisher ([BonehShoup2023], Section 6.3, Theorem 6.2, printed p. 224). -/
def macToPrfOnDistinguisher (valid : ℕ → List Bool → Bool) (adversary : Forger) :
    OracleDistinguisher :=
  fun n _ => do
    let out ← (OracleComp.interpret
      (OracleComp.sumHandler
        (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        (macLogHandlerOn valid n))
      (adversary n [])).run []
    let ((msg, tag), queried) := out
    if valid n msg && !queried.contains msg then
      (· == tag) <$> (List.take n <$> ProbOracleComp.query ((), msg))
    else
      pure false

/-- `macToPrfOnDistinguisher valid adversary` is uniform strict oracle PPT whenever `valid` is
computable in polynomial time on `(1ⁿ, msg)` and `adversary` is uniform strict oracle PPT. -/
theorem isOraclePPT_macToPrfOnDistinguisher {valid : ℕ → List Bool → Bool}
    (hvalid : ComputableInPolyTime (fun (n, msg) => valid n msg)
      (encPair encUnary encBits) encBool)
    {adversary : Forger} (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsOraclePPT encBool (macToPrfOnDistinguisher valid adversary) := by
  have hrun := isOraclePPTOn_run_macLogHandlerOn hvalid hadversary
  ppt [macToPrfOnDistinguisher]

private theorem isQueryBounded_run_macLogHandlerOn {α : Type} (valid : ℕ → List Bool → Bool)
    (n : ℕ) {prog : WordOracleComp Unit α} {q : ℕ}
    (hq : prog.IsQueryBounded q) (queried : List (List Bool)) :
    ((OracleComp.interpret
      (OracleComp.sumHandler
        (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        (macLogHandlerOn valid n))
      prog).run queried).IsQueryBounded q := by
  refine OracleComp.IsCostBounded.run_interpret (fun op s => ?_) hq queried
  cases op with
  | inl k =>
    simp only [OracleComp.sumHandler, StateT.run_lift]
    simpa using (ProbOracleComp.isCostBounded_sample (fun _ => 1) (ProbComp.unifFin k)).bind
      fun a => OracleComp.IsCostBounded.pure (a, s) 0
  | inr req =>
    dsimp only [OracleComp.sumHandler, macLogHandlerOn, StateT.run, Sum.elim_inr]
    split_ifs
    · simp only [OracleComp.isCostBounded_map_iff]
      exact ProbOracleComp.isCostBounded_query _ _
    · exact OracleComp.IsCostBounded.pure ([], s) 1

/-- A forger making at most `Q` signing queries yields a PRF distinguisher making at most `Q + 1`
queries (`Q` signing queries plus one verification query). -/
theorem isQueryBounded_macToPrfOnDistinguisher (valid : ℕ → List Bool → Bool) (adversary : Forger)
    {n Q : ℕ} (hQ : (adversary n []).IsQueryBounded Q) :
    (macToPrfOnDistinguisher valid adversary n []).IsQueryBounded (Q + 1) := by
  unfold macToPrfOnDistinguisher
  refine (isQueryBounded_run_macLogHandlerOn valid n hQ []).bind fun out => ?_
  rcases out with ⟨⟨msg, tag⟩, queried⟩
  dsimp only
  split_ifs
  · rw [OracleComp.isCostBounded_map_iff, OracleComp.isCostBounded_map_iff]
    exact ProbOracleComp.isCostBounded_query _ _
  · exact OracleComp.IsCostBounded.pure false 1

private noncomputable def prfRealLogHandlerOn (valid : ℕ → List Bool → Bool)
    (tagFamily : List Bool → List Bool → List Bool) (n : ℕ) (sk : List Bool)
    (q : Unit × List Bool) : StateT (List (List Bool) × Unit) PMF (List Bool) :=
  fun s =>
    (ProbOracleComp.runWith
      (fun request (u : Unit) =>
        (PMF.pure (prfOracleOn (valid n) tagFamily sk request.2)).map (·, u))
      ((macLogHandlerOn valid n q).run s.1) s.2).map (fun r => (r.1.1, r.1.2, r.2))

private theorem run_macLogHandlerOn_eq_macSigningOracleOn
    {valid : ℕ → List Bool → Bool} {tagFamily : List Bool → List Bool → List Bool}
    (hlen : ∀ key query : List Bool, valid key.length query = true →
      (tagFamily key query).length = key.length)
    (n : ℕ) (sk : List Bool) (hsk : sk.length = n)
    (prog : WordOracleComp Unit (List Bool × List Bool)) :
    ProbComp.eval (OracleComp.interpret
      (OracleComp.sumHandler ProbComp.unifFin (fun request =>
        pure (prfOracleOn (valid n) tagFamily sk request.2)))
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          (macLogHandlerOn valid n))
        prog).run [])) =
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (macSigningOracleOn valid tagFamily n sk)) prog).run []) := by
  have hfst := congrArg (PMF.map Prod.fst) (ProbOracleComp.runWith_readOnly
    (fun request (_ : Unit) => PMF.pure (prfOracleOn (valid n) tagFamily sk request.2))
    ((OracleComp.interpret
      (OracleComp.sumHandler
        (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        (macLogHandlerOn valid n))
      prog).run []) ())
  simp only [PMF.map_comp, Function.comp_def,
    show (fun x : (List Bool × List Bool) × List (List Bool) => x) = id from rfl, PMF.map_id]
    at hfst
  simp only [ProbOracleComp.eval_interpret, ProbComp.eval_pure]
  rw [← OracleComp.evalWith_eq_interpret, ← hfst, ProbOracleComp.runWith_run_interpret,
    ProbOracleComp.eval_run_interpret_eq_runWith]
  have hsim := ProbOracleComp.runWith_map_state
    (oracle := prfRealLogHandlerOn valid tagFamily n sk)
    (oracle' := fun q s => ProbComp.eval (macSigningOracleOn valid tagFamily n sk q s))
    (represent := Prod.fst)
    (step := fun ⟨⟨⟩, msg⟩ ⟨queried, ⟨⟩⟩ => by
      dsimp only [prfRealLogHandlerOn]
      rw [ProbOracleComp.runWith_eq_run_interpret]
      unfold macLogHandlerOn macSigningOracleOn
      dsimp only [prfOracleOn, StateT.run]
      by_cases hv : valid n msg = true
      · have hlenEq : (tagFamily sk msg).length = n := hsk ▸ hlen sk msg (hsk.symm ▸ hv)
        simp only [hv, ↓reduceIte, Functor.map_map, OracleComp.interpret_map,
          ProbOracleComp.interpret_query, ProbComp.eval_pure]
        dsimp only [Functor.map, StateT.map]
        simp only [List.take_of_length_le hlenEq.le, pmf_norm]
      · simp only [Bool.eq_false_iff.mpr hv, Bool.false_eq_true, ↓reduceIte,
          OracleComp.interpret_pure, ProbComp.eval_pure]
        rw [show (pure ([], queried) : StateT Unit PMF _) PUnit.unit =
            PMF.pure (([], queried), PUnit.unit) from rfl]
        simp only [PMF.pure_map])
    prog ([], ())
  unfold prfRealLogHandlerOn at hsim
  simpa only [PMF.map_comp, Function.comp_def] using hsim

/-- Against `prfRealGameOn valid tagFamily`, `macToPrfOnDistinguisher valid adversary` has the exact
output law of `macEufCmaGameOn valid tagFamily adversary` (and `macSufCmaGameOn`). -/
theorem eval_prfRealGameOn_macToPrfOnDistinguisher {valid : ℕ → List Bool → Bool}
    {tagFamily : List Bool → List Bool → List Bool}
    (hlen : ∀ key query : List Bool, valid key.length query = true →
      (tagFamily key query).length = key.length)
    (adversary : Forger) (n : ℕ) :
    ProbComp.eval (prfRealGameOn valid tagFamily (macToPrfOnDistinguisher valid adversary) n) =
      ProbComp.eval (macEufCmaGameOn valid tagFamily adversary n) := by
  simp only [prfRealGameOn, ProbOracleComp.run, macEufCmaGameOn, macToPrfOnDistinguisher,
    OracleComp.interpret_bind, ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList]
  refine PMF.bind_congr_on_support _ _ _ fun sk hsk => ?_
  have hskLen : sk.length = n := BitString.length_of_mem_support_uniformList hsk
  rw [run_macLogHandlerOn_eq_macSigningOracleOn hlen n sk hskLen (adversary n [])]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨(msg, tag), queried⟩ _ => ?_
  dsimp only
  by_cases hcond : (valid n msg && !queried.contains msg) = true
  · obtain ⟨hv, hfresh⟩ := (Bool.and_eq_true _ _).mp hcond
    have htagLen : (tagFamily sk msg).length = n := hskLen ▸ hlen sk msg (hskLen.symm ▸ hv)
    simp only [hv, hfresh, Bool.true_and, ↓reduceIte, Functor.map_map, OracleComp.interpret_map,
      ProbOracleComp.interpret_query, ProbComp.eval_map, ProbComp.eval_pure, PMF.pure_map,
      prfOracleOn, List.take_of_length_le htagLen.le]
  · simp only [Bool.eq_false_iff.mpr hcond, Bool.false_eq_true, ↓reduceIte, Bool.false_and,
      OracleComp.interpret_pure, ProbComp.eval_pure]

private noncomputable def prfIdealLogOracleOn (valid : ℕ → List Bool → Bool) (n : ℕ)
    (q : Unit × List Bool) :
    StateT (List (List Bool) × List (List Bool × List Bool)) PMF (List Bool) :=
  fun state =>
    ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (fun request s => (cachedRandomFunctionOracle (valid n) n request.2 s).eval))
      ((macLogHandlerOn valid n q).run state.1)).run state.2).map
        (fun result => (result.1.1, result.1.2, result.2))

private theorem prfIdealLogOracleOn_inv (valid : ℕ → List Bool → Bool) (adversary : Forger)
    (n : ℕ) {result : List Bool × List Bool}
    {state : List (List Bool) × List (List Bool × List Bool)}
    (hmem : (result, state) ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (prfIdealLogOracleOn valid n))
      (adversary n [])).run ([], [])).support) :
    ∀ entry ∈ state.2, entry.1 ∈ state.1 := by
  rw [← ProbOracleComp.runWith_eq_run_interpret] at hmem
  refine ProbOracleComp.runWith_invariant (prfIdealLogOracleOn valid n)
    (fun s => ∀ entry ∈ s.2, entry.1 ∈ s.1)
    ?_ (adversary n []) ([], []) (by simp) result state hmem
  intro ⟨⟨⟩, msg⟩ ⟨queried, cache⟩ hstate _ ⟨queried', cache'⟩ hstep
  dsimp only [prfIdealLogOracleOn] at hstep
  unfold macLogHandlerOn at hstep
  dsimp only [StateT.run] at hstep
  by_cases hv : valid n msg = true
  · simp only [hv, ↓reduceIte, Functor.map_map, OracleComp.interpret_map,
      ProbOracleComp.interpret_query] at hstep
    dsimp only [Functor.map, StateT.map, StateT.run] at hstep
    simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_map_iff,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hstep
    obtain ⟨_, ⟨⟨v, nextCache⟩, hans, rfl⟩, hpair⟩ := hstep
    rcases Prod.mk.inj hpair with ⟨-, rfl, rfl⟩
    have htail : ∀ e ∈ cache, e.1 ∈ msg :: queried :=
      fun e he => List.mem_cons_of_mem _ (hstate e he)
    rcases cachedSamplerOracle_cache_of_mem_support hans with hnext | ⟨-, -, hnext⟩ <;>
      dsimp only at hnext ⊢ <;> rw [hnext]
    · exact htail
    · exact List.forall_mem_cons.mpr ⟨List.mem_cons_self, htail⟩
  · simp only [Bool.eq_false_iff.mpr hv, Bool.false_eq_true, ↓reduceIte,
      OracleComp.interpret_pure] at hstep
    rw [show (pure ([], queried) : StateT _ PMF _) cache =
        PMF.pure (([], queried), cache) from rfl] at hstep
    simp only [PMF.pure_map, PMF.mem_support_pure_iff, Prod.mk.injEq] at hstep
    rcases hstep with ⟨-, rfl, rfl⟩
    exact hstate

private theorem lookup_eq_none_of_forall_fst_not_mem {K V : Type} [BEq K] [LawfulBEq K]
    {k : K} :
    ∀ {cache : List (K × V)}, (∀ e ∈ cache, e.1 ≠ k) → cache.lookup k = none
  | [], _ => rfl
  | (k', v) :: rest, h => by
    have hne : (k == k') = false := beq_eq_false_iff_ne.mpr (h (k', v) List.mem_cons_self).symm
    simp only [List.lookup_cons, hne]
    exact lookup_eq_none_of_forall_fst_not_mem fun e he => h e (List.mem_cons_of_mem _ he)

/-- Helper step after [BonehShoup2023], Section 6.3, proof of Theorem 6.2 (printed p. 224), not the
standalone Theorem 6.2 endpoint (see `Cslib.Crypto.PseudorandomFunction.sufCma_prfMAC`): in
`prfIdealGameOn valid id`, `macToPrfOnDistinguisher valid adversary` succeeds with probability at
most `1 / 2 ^ n`. -/
theorem succProbability_prfIdealGameOn_macToPrfOnDistinguisher_le
    (valid : ℕ → List Bool → Bool) (adversary : Forger) (n : ℕ) :
    Game.succProbability
        (ProbComp.eval (prfIdealGameOn valid id (macToPrfOnDistinguisher valid adversary) n)) ≤
      (1 : ℝ≥0) / 2 ^ n := by
  let post : (List Bool × List Bool) × List (List Bool) × List (List Bool × List Bool) →
      PMF Bool := fun ⟨(msg, tag), queried, cache⟩ =>
    if valid n msg && !queried.contains msg then
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (fun request s => (cachedRandomFunctionOracle (valid n) n request.2 s).eval))
        ((· == tag) <$> (List.take n <$> ProbOracleComp.query ((), msg)))).run cache).map Prod.fst
    else
      PMF.pure false
  have heval : ProbComp.eval
        (prfIdealGameOn valid id (macToPrfOnDistinguisher valid adversary) n) =
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (prfIdealLogOracleOn valid n))
        (adversary n [])).run ([], [])).bind post := by
    rw [prfIdealGameOn, id_eq, ProbComp.eval_map, ProbOracleComp.eval_run_interpret]
    dsimp only [macToPrfOnDistinguisher, prfIdealLogOracleOn]
    simp only [OracleComp.interpret_bind, StateT.run_bind,
      ProbOracleComp.run_interpret_run_interpret, pmf_norm]
    refine PMF.bind_congr_on_support _ _ _ fun ⟨(msg, tag), queried, cache⟩ _ => ?_
    dsimp only [post]
    by_cases hcond : (valid n msg && !queried.contains msg) = true
    · simp only [hcond, ↓reduceIte]
    · simp only [Bool.eq_false_iff.mpr hcond, Bool.false_eq_true, ↓reduceIte,
        OracleComp.interpret_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.pure_map]
  have hpostLe : ∀ {out : List Bool × List Bool} {queried : List (List Bool)}
      {cache : List (List Bool × List Bool)},
      (∀ entry ∈ cache, entry.1 ∈ queried) →
      post (out, queried, cache) true ≤ (1 : ℝ≥0∞) / 2 ^ n := by
    rintro ⟨msg, tag⟩ queried cache hinv
    dsimp only [post]
    by_cases hcond : (valid n msg && !queried.contains msg) = true
    · simp only [hcond, ↓reduceIte]
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      have hmiss : cache.lookup msg = none := by
        refine lookup_eq_none_of_forall_fst_not_mem fun e he hEq => ?_
        have hmemQ : msg ∈ queried := hEq ▸ hinv e he
        exact Bool.false_ne_true (hcond.2.symm.trans (List.contains_iff_mem.mpr hmemQ))
      simp only [Functor.map_map, OracleComp.interpret_map, StateT.run_map,
        ProbOracleComp.interpret_query, PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def]
      unfold cachedRandomFunctionOracle cachedSamplerOracle
      simp only [hcond.1, ↓reduceIte, ProbComp.eval_memoize, BitString.eval_sampleList]
      dsimp only [StateT.run]
      rw [memoize, hmiss, BitString.uniformList]
      simp only [← PMF.bind_pure_comp, pmf_norm, List.length_ofFn, le_refl, List.take_of_length_le]
      refine (PMF.uniformOfFintype_bind_pure_apply_true_le (E := fun x => List.ofFn x == tag)
        fun a ha b hb => List.ofFn_injective
          ((beq_iff_eq.mp ha).trans (beq_iff_eq.mp hb).symm)).trans_eq ?_
      simp
    · simp only [Bool.eq_false_iff.mpr hcond, Bool.false_eq_true, ↓reduceIte, PMF.pure_apply,
        reduceCtorEq, zero_le]
  rw [heval, Game.succProbability]
  refine (ENNReal.toNNReal_mono (ENNReal.div_ne_top ENNReal.one_ne_top (by positivity))
    (PMF.bind_apply_le_on_support _ fun ⟨out, queried, cache⟩ hmem =>
      hpostLe (prfIdealLogOracleOn_inv valid adversary n hmem))).trans_eq ?_
  simp [ENNReal.toNNReal_ofNat]

/-- Helper step after [BonehShoup2023], Section 6.3, proof of Theorem 6.2 (printed p. 224), not the
standalone Theorem 6.2 endpoint (see `Cslib.Crypto.PseudorandomFunction.sufCma_prfMAC`): for every
adaptive MAC forger `adversary` on `valid`, the strong `SUFCMA` forgery probability against
`tagFamily` is at most the `prfRealGameOn`/`prfIdealGameOn` advantage of
`macToPrfOnDistinguisher valid adversary` plus `1 / 2 ^ n`. -/
theorem succProbability_macSufCmaGameOn_le {valid : ℕ → List Bool → Bool}
    {tagFamily : List Bool → List Bool → List Bool}
    (hlen : ∀ key query : List Bool, valid key.length query = true →
      (tagFamily key query).length = key.length)
    (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval (macSufCmaGameOn valid tagFamily adversary n)) ≤
      Game.advantage
        (ProbComp.eval
          (prfRealGameOn valid tagFamily (macToPrfOnDistinguisher valid adversary) n))
        (ProbComp.eval (prfIdealGameOn valid id (macToPrfOnDistinguisher valid adversary) n)) +
      (1 : ℝ≥0) / 2 ^ n := by
  rw [eval_macSufCmaGameOn_eq_macEufCmaGameOn,
    ← eval_prfRealGameOn_macToPrfOnDistinguisher hlen adversary n]
  have htri := Game.advantage_triangle
    (ProbComp.eval (prfRealGameOn valid tagFamily (macToPrfOnDistinguisher valid adversary) n))
    (ProbComp.eval (prfIdealGameOn valid id (macToPrfOnDistinguisher valid adversary) n))
    (PMF.pure false)
  simp only [Game.advantage_pure_false] at htri
  exact htri.trans (add_le_add le_rfl
    (succProbability_prfIdealGameOn_macToPrfOnDistinguisher_le valid adversary n))

/-- Helper step after [BonehShoup2023], Section 6.3, Theorem 6.2 (printed p. 224), not the
standalone Theorem 6.2 endpoint (see `Cslib.Crypto.PseudorandomFunction.sufCma_prfMAC`): any
`PseudorandomFunctionOn valid id` with polynomial-time domain predicate `valid` satisfies
`MACSUFCMAOn valid`. -/
theorem PseudorandomFunctionOn.macSufCmaOn {valid : ℕ → List Bool → Bool}
    (hvalid : ComputableInPolyTime (fun p : ℕ × List Bool => valid p.1 p.2)
      (encPair encUnary encBits) encBool)
    {tagFamily : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunctionOn valid id tagFamily) :
    MACSUFCMAOn valid tagFamily := by
  apply Game.Indistinguishable.of_negligible_succProbability
  intro adversary hadversary
  have hadv := hprf.secure (macToPrfOnDistinguisher valid adversary)
    (isOraclePPT_macToPrfOnDistinguisher hvalid hadversary)
  negligible using fun n => succProbability_macSufCmaGameOn_le hprf.length_eq adversary n

/-- Certified reduction from an adaptive variable-length MAC forger against length-prepended
CBC-MAC (`lpBlockValid L`) to a length-preserving PRF distinguisher ([BonehShoup2023], Theorems
6.2, 6.3, and 6.8): compose `macToPrfOnDistinguisher (lpBlockValid L)` with
`lengthPrependedToPrfDistinguisher L`. -/
def lengthPrependedMacToPrfDistinguisher (L : ℕ → ℕ) (adversary : Forger) :
    OracleDistinguisher :=
  lengthPrependedToPrfDistinguisher L (macToPrfOnDistinguisher (lpBlockValid L) adversary)

/-- `lengthPrependedMacToPrfDistinguisher L adversary` is uniform strict oracle PPT whenever `L` is
unary polynomial-time and `adversary` is uniform strict oracle PPT. -/
theorem isOraclePPT_lengthPrependedMacToPrfDistinguisher {L : ℕ → ℕ}
    (hL : ComputableInPolyTime L encUnary encUnary) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsOraclePPT encBool (lengthPrependedMacToPrfDistinguisher L adversary) :=
  isOraclePPT_lengthPrependedToPrfDistinguisher hL
    (isOraclePPT_macToPrfOnDistinguisher (computableInPolyTime_lpBlockValid hL) hadversary)

/-- **Concrete adaptive `SUFCMA` forgery bound for variable-length length-prepended CBC-MAC**
([BonehShoup2023], Section 6.3 Theorem 6.2, Section 6.4.1 Theorem 6.3, and Section 6.6.1 Method 1
via Section 6.6 Theorem 6.8, printed pp. 224, 226–229, and 235–236): whenever `L n < 2 ^ n` and
`adversary` makes at most `Q` signing queries at parameter `n`, its strong forgery probability on
`lpBlockValid L` is at most the PRF advantage of `lengthPrependedMacToPrfDistinguisher L adversary`
plus `(Q + 1) ^ 2 * (L n + 1) ^ 2 / (2 * 2 ^ n) + 1 / 2 ^ n`. -/
theorem succProbability_macSufCmaGameOn_lengthPrependedCbcMac_le
    {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query : List Bool, query.length = key.length →
      (family key query).length = key.length)
    (L : ℕ → ℕ) (adversary : Forger) {n Q : ℕ}
    (hL : L n < 2 ^ n) (hQ : (adversary n []).IsQueryBounded Q) :
    Game.succProbability
        (ProbComp.eval
          (macSufCmaGameOn (lpBlockValid L) (lengthPrependedCbcMacFamily family) adversary n)) ≤
      Game.advantage
        (ProbComp.eval
          (prfRealGame id family (lengthPrependedMacToPrfDistinguisher L adversary) n))
        (ProbComp.eval
          (prfIdealGame id id (lengthPrependedMacToPrfDistinguisher L adversary) n)) +
      ((Q : ℝ≥0) + 1) ^ 2 * ((L n : ℝ≥0) + 1) ^ 2 / (2 * 2 ^ n) +
      (1 : ℝ≥0) / 2 ^ n := by
  have hmac := succProbability_macSufCmaGameOn_le (valid := lpBlockValid L)
    (fun key query _ => length_lengthPrependedCbcMacFamily hlen key query) adversary n
  have hprf := advantage_lengthPrependedCbcMac_le hlen L
    (macToPrfOnDistinguisher (lpBlockValid L) adversary) hL
    (isQueryBounded_macToPrfOnDistinguisher (lpBlockValid L) adversary hQ)
  rw [Nat.cast_add, Nat.cast_one] at hprf
  exact hmac.trans (add_le_add hprf le_rfl)

/-- **Variable-length length-prepended CBC-MAC is strongly unforgeable (`MACSUFCMAOn`)**
([BonehShoup2023], Section 6.3 Theorem 6.2, Section 6.4.1 Theorem 6.3, and Section 6.6.1 Method 1
via Section 6.6 Theorem 6.8, printed pp. 224, 226–229, and 235–236): for any
`PseudorandomFunction family` and unary polynomial-time block-count cap `L : ℕ → ℕ`,
`lengthPrependedCbcMacFamily family` satisfies `MACSUFCMAOn (lpBlockValid L)` over whole-block
messages of `0` to `L n` blocks (empty message included). -/
theorem PseudorandomFunction.macSufCmaOn_lengthPrependedCbcMac
    {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family)
    {L : ℕ → ℕ} (hL : ComputableInPolyTime L encUnary encUnary) :
    MACSUFCMAOn (lpBlockValid L) (lengthPrependedCbcMacFamily family) :=
  (hF.prfOn_lengthPrependedCbcMac hL).macSufCmaOn (computableInPolyTime_lpBlockValid hL)

/-! ### Length-Extension Attack on Unmodified Zero-IV CBC-MAC -/

/-- Classic 1-query length-extension forger against unmodified zero-IV CBC-MAC ([BonehShoup2023],
Section 6.4.3, printed pp. 230–231): sign the 1-block zero message `0^n`, receive `t = F_k(0^n)`,
and output the fresh 2-block forgery `(0^n ++ t, t)`. -/
@[expose]
def cbcExtensionForger : Forger := fun n _ =>
  (fun tag => (List.replicate n false ++ tag, tag)) <$>
    (List.take n <$> ProbOracleComp.query ((), List.replicate n false))

/-- `cbcExtensionForger` is uniform strict oracle PPT. -/
theorem isOraclePPT_cbcExtensionForger :
    IsOraclePPT (encPair encBits encBits) cbcExtensionForger := by
  have hq : IsOraclePPTOn (encPair encUnary encBits) encBits
      (fun p : ℕ × List Bool =>
        List.take p.1 <$> ProbOracleComp.query ((), List.replicate p.1 false)) :=
    IsOraclePPTOn.query_take () (by polytime) (by fun_prop)
  unfold cbcExtensionForger
  exact (hq.map_with (by polytime)).isOraclePPT

private theorem zipWith_xor_self : ∀ l : List Bool,
    List.zipWith xor l l = List.replicate l.length false
  | [] => rfl
  | b :: bs => by
    simp only [List.zipWith_cons_cons, bne_self_eq_false, List.length_cons, List.replicate_succ,
      List.cons.injEq, true_and]
    exact zipWith_xor_self bs

private theorem cbcMacFamily_zero_append_tag {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query : List Bool, query.length = key.length →
      (family key query).length = key.length)
    {n : ℕ} (hn : 0 < n) {sk : List Bool} (hsk : sk.length = n) :
    let tag := cbcMacFamily family sk (List.replicate n false)
    cbcMacFamily family sk (List.replicate n false ++ tag) = tag := by
  intro tag
  have htagLen : tag.length = n := hsk ▸ length_cbcMacFamily hlen sk _
  have hrows1 : BitString.listRows (n / n) n (List.replicate n false) =
      [List.replicate n false] := by
    simpa [Nat.div_self hn] using BitString.listRows_flatten [List.replicate n false] (by simp)
  have hfamLen : (family sk (List.replicate n false)).length = n :=
    hsk ▸ hlen sk _ (by simp [hsk])
  have htag1 : tag = family sk (List.replicate n false) := by
    simp only [tag, cbcMacFamily, hsk, cbcMacWord, List.length_replicate, hrows1,
      List.foldl_cons, List.foldl_nil, zipWith_xor_self, List.take_of_length_le hfamLen.le]
  have htagWord : cbcMacWord family n sk (List.replicate n false) = tag := by
    rw [show tag = cbcMacFamily family sk (List.replicate n false) from rfl, cbcMacFamily, hsk]
  rw [cbcMacFamily, hsk, cbcMacWord_append_block family hn sk (by simp) htagLen, htagWord,
    zipWith_xor_self, htagLen, ← htag1, List.take_of_length_le htagLen.le]

/-- Helper step of [BonehShoup2023], Section 6.4.3 (printed pp. 230–231): at every `n ≥ 1`,
`cbcExtensionForger` wins `macSufCmaGameOn (lpBlockValid (fun _ => 2)) (cbcMacFamily family)` with
probability `1`. -/
theorem eval_macSufCmaGameOn_cbcMacFamily_cbcExtensionForger
    {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query : List Bool, query.length = key.length →
      (family key query).length = key.length)
    {n : ℕ} (hn : 0 < n) :
    ProbComp.eval
      (macSufCmaGameOn (lpBlockValid (fun _ => 2)) (cbcMacFamily family) cbcExtensionForger n) =
    PMF.pure true := by
  rw [eval_macSufCmaGameOn_eq_macEufCmaGameOn]
  have hval1 : lpBlockValid (fun _ => 2) n (List.replicate n false) = true := by
    simp only [lpBlockValid, List.length_replicate, Nat.mod_self, beq_self_eq_true, Bool.true_and,
      decide_eq_true_eq]
    omega
  simp only [macEufCmaGameOn, cbcExtensionForger, Functor.map_map, OracleComp.interpret_map,
    StateT.run_map, ProbOracleComp.interpret_query, BitString.eval_sampleList, pmf_norm]
  dsimp only [StateT.run, macSigningOracleOn]
  simp only [hval1, ↓reduceIte, ProbComp.eval_pure, PMF.pure_bind]
  trans PMF.bind (BitString.uniformList n) (fun _ => PMF.pure true)
  · refine PMF.bind_congr_on_support _ _ _ fun sk hsk => ?_
    have hskLen : sk.length = n := BitString.length_of_mem_support_uniformList hsk
    have htagLen : (cbcMacFamily family sk (List.replicate n false)).length = n := by
      rw [length_cbcMacFamily hlen, hskLen]
    have hlen2 : (List.replicate n false ++
        cbcMacFamily family sk (List.replicate n false)).length = 2 * n := by
      rw [List.length_append, List.length_replicate, htagLen, Nat.two_mul]
    have hval2 : lpBlockValid (fun _ => 2) n
        (List.replicate n false ++ cbcMacFamily family sk (List.replicate n false)) = true := by
      simp [lpBlockValid, hlen2, Nat.mul_mod_left]
    have hne : List.replicate n false ++ cbcMacFamily family sk (List.replicate n false) ≠
        List.replicate n false := fun hEq => by
      have hlenEq := congrArg List.length hEq
      rw [hlen2, List.length_replicate] at hlenEq
      omega
    rw [List.take_of_length_le htagLen.le]
    simp [hval2, hne, cbcMacFamily_zero_append_tag hlen hn hskLen]
  · exact PMF.bind_const _ _

/-- CBC-MAC step toward #5801 after [BonehShoup2023], Section 6.4.3 (printed pp. 230–231), not the
full Section 6.4.2–6.4.3 / Definition 6.4 cascade and extendable-PRF endpoint: for every
length-preserving `family` (including any `PseudorandomFunction`), unmodified `cbcMacFamily family`
fails `MACSUFCMAOn (lpBlockValid (fun _ => 2))` (and hence `MACEUFCMAOn` by
`macSufCmaOn_iff_macEufCmaOn`). -/
theorem not_macSufCmaOn_cbcMacFamily {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query : List Bool, query.length = key.length →
      (family key query).length = key.length) :
    ¬ MACSUFCMAOn (lpBlockValid (fun _ => 2)) (cbcMacFamily family) := by
  intro hsec
  refine not_negligible_const one_ne_zero (negligible_of_eventually_le
    (hsec cbcExtensionForger isOraclePPT_cbcExtensionForger) ?_)
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  rw [eval_macSufCmaGameOn_cbcMacFamily_cbcExtensionForger hlen hn, Game.advantage_pure_false,
    Game.succProbability]
  simp

/-- CBC-MAC step toward #5801 after [BonehShoup2023], Section 6.4.3 (printed p. 231), not the full
Section 6.4.2–6.4.3 / Definition 6.4 cascade and extendable-PRF endpoint: for every
length-preserving `family`, unmodified `cbcMacFamily family` fails
`PseudorandomFunctionOn (lpBlockValid (fun _ => 2)) id`. -/
theorem not_prfOn_cbcMacFamily {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query : List Bool, query.length = key.length →
      (family key query).length = key.length) :
    ¬ PseudorandomFunctionOn (lpBlockValid (fun _ => 2)) id (cbcMacFamily family) := fun hprf =>
  not_macSufCmaOn_cbcMacFamily hlen
    (hprf.macSufCmaOn (computableInPolyTime_lpBlockValid (ComputableInPolyTime.const 2)))

/-! ### `MACScheme` Instances for Fixed-Block-Count Schedules -/

private theorem detVerify_polyTime {tagFamily : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun p : List Bool × List Bool => tagFamily p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun p : List Bool × List Bool × List Bool => tagFamily p.1 p.2.1 == p.2.2)
      encBitsTriple encBool := by
  have hcall : ComputableInPolyTime
      (fun p : List Bool × List Bool × List Bool => tagFamily p.1 p.2.1)
      encBitsTriple encBits :=
    hpoly.comp (g := fun p : List Bool × List Bool × List Bool => (p.1, p.2.1))
      (by dsimp only [encBitsTriple]; fun_prop)
  dsimp only [encBitsTriple]
  fun_prop

private theorem detVerify_sign (tagFamily : List Bool → List Bool → List Bool)
    (sk msg tag : List Bool)
    (htag : tag ∈ (ProbComp.eval (pure (tagFamily sk msg) : ProbComp (List Bool))).support) :
    (tagFamily sk msg == tag) = true := by
  simp_all [ProbComp.eval_pure]

private theorem eval_sufCmaGame_det (scheme : MACScheme)
    (hkey : scheme.keyGen = BitString.sampleList)
    (tagFamily : List Bool → List Bool → List Bool)
    (hsign : scheme.sign = fun sk msg => pure (tagFamily sk msg))
    (hver : scheme.verify = fun sk msg tag => tagFamily sk msg == tag)
    (adversary : Forger) (n : ℕ) :
    ProbComp.eval (scheme.sufCmaGame adversary n) =
      ProbComp.eval
        (macSufCmaGameOn (fun m q => q.length == scheme.msgLen m) tagFamily adversary n) := by
  unfold MACScheme.sufCmaGame macSufCmaGameOn
  have horacle (sk : List Bool) :
      scheme.signingPairOracle n sk =
        macSigningPairOracleOn (fun m q => q.length == scheme.msgLen m) tagFamily n sk := by
    funext ⟨⟨⟩, msg⟩ issued
    unfold MACScheme.signingPairOracle MACScheme.signingPairOracleOn macSigningPairOracleOn
    dsimp only [StateT.run]
    rw [hsign]
    by_cases hm : (msg.length == scheme.msgLen n) = true <;> simp [hm]
  simp only [hkey, horacle, hver]

/-- Deterministic `MACScheme` authenticating `ℓ n * n`-bit (`ℓ n`-block) messages via basic zero-IV
CBC-MAC `cbcMacFamily family` ([BonehShoup2023], Section 6.3, p. 223, and Section 6.4.1, Figure
6.3a, printed p. 226). -/
noncomputable def cbcFixedBlockMAC (ℓ : ℕ → ℕ)
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary)
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits) : MACScheme where
  msgLen n := ℓ n * n
  msgLen_polyTime := by polytime
  keyGen := BitString.sampleList
  sign sk msg := pure (cbcMacFamily family sk msg)
  verify sk msg tag := cbcMacFamily family sk msg == tag
  keyGen_ppt := isPPTOn_sampleList
  sign_ppt := (computableInPolyTime_cbcMacFamily hpoly).isPPTOn
  verify_polyTime := detVerify_polyTime (computableInPolyTime_cbcMacFamily hpoly)
  verify_sign _ sk _ msg _ tag htag := detVerify_sign (cbcMacFamily family) sk msg tag htag

@[simp]
theorem cbcFixedBlockMAC_msgLen (ℓ : ℕ → ℕ) (hℓ : ComputableInPolyTime ℓ encUnary encUnary)
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits) (n : ℕ) :
    (cbcFixedBlockMAC ℓ hℓ family hpoly).msgLen n = ℓ n * n := by rfl

@[simp]
theorem cbcFixedBlockMAC_sign (ℓ : ℕ → ℕ) (hℓ : ComputableInPolyTime ℓ encUnary encUnary)
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits) (sk msg : List Bool) :
    (cbcFixedBlockMAC ℓ hℓ family hpoly).sign sk msg = pure (cbcMacFamily family sk msg) := by rfl

@[simp]
theorem cbcFixedBlockMAC_verify (ℓ : ℕ → ℕ) (hℓ : ComputableInPolyTime ℓ encUnary encUnary)
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits) (sk msg tag : List Bool) :
    (cbcFixedBlockMAC ℓ hℓ family hpoly).verify sk msg tag =
      (cbcMacFamily family sk msg == tag) := by rfl

/-- Certified reduction from an adaptive forger against `cbcFixedBlockMAC ℓ` to a length-preserving
PRF distinguisher ([BonehShoup2023], Section 6.3 Theorem 6.2 and Section 6.4.1 Theorem 6.3). -/
def cbcFixedBlockMacToPrfDistinguisher (ℓ : ℕ → ℕ) (adversary : Forger) : OracleDistinguisher :=
  cbcMacToPrfDistinguisher ℓ
    (restrictLengthDistinguisher (fun n => ℓ n * n)
      (macToPrfOnDistinguisher (fun n msg => msg.length == ℓ n * n) adversary))

/-- `cbcFixedBlockMacToPrfDistinguisher ℓ adversary` is uniform strict oracle PPT whenever `ℓ` is
unary polynomial-time and `adversary` is uniform strict oracle PPT. -/
theorem isOraclePPT_cbcFixedBlockMacToPrfDistinguisher {ℓ : ℕ → ℕ}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsOraclePPT encBool (cbcFixedBlockMacToPrfDistinguisher ℓ adversary) :=
  isOraclePPT_cbcMacToPrfDistinguisher hℓ
    (isOraclePPT_restrictLengthDistinguisher (by polytime)
      (isOraclePPT_macToPrfOnDistinguisher (by polytime) hadversary))

private theorem isQueryBounded_restrictLengthDistinguisher (inLen : ℕ → ℕ)
    (adversary : OracleDistinguisher) {n Q : ℕ} (hQ : (adversary n []).IsQueryBounded Q) :
    (restrictLengthDistinguisher inLen adversary n []).IsQueryBounded Q := by
  rw [restrictLengthDistinguisher_eq_simulate]
  refine ProbOracleComp.IsQueryBounded.simulate (fun req => ?_) hQ
  unfold restrictLengthQuery ProbOracleComp.IsQueryBounded
  split_ifs
  · rw [OracleComp.isCostBounded_map_iff]
    exact ProbOracleComp.isCostBounded_query _ _
  · exact OracleComp.IsCostBounded.pure [] 1

/-- **Concrete `SUFCMA` forgery bound for fixed-block-count basic CBC-MAC** ([BonehShoup2023],
Section 6.3 Theorem 6.2 and Section 6.4.1 Theorem 6.3, printed pp. 224 and 226–229): for `0 < ℓ n`,
`0 < n`, and a forger making at most `Q` signing queries, the `SUFCMA` forgery probability against
`cbcFixedBlockMAC ℓ hℓ family hpoly` is at most the PRF advantage of
`cbcFixedBlockMacToPrfDistinguisher ℓ adversary` plus
`(Q + 1) ^ 2 * (ℓ n) ^ 2 / (2 * 2 ^ n) + 1 / 2 ^ n`. -/
theorem succProbability_sufCmaGame_cbcFixedBlockMAC_le (ℓ : ℕ → ℕ)
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary)
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query : List Bool, query.length = key.length →
      (family key query).length = key.length)
    (adversary : Forger) {n Q : ℕ} (hn : 0 < n) (hpos : 0 < ℓ n)
    (hQ : (adversary n []).IsQueryBounded Q) :
    Game.succProbability
        (ProbComp.eval ((cbcFixedBlockMAC ℓ hℓ family hpoly).sufCmaGame adversary n)) ≤
      Game.advantage
        (ProbComp.eval (prfRealGame id family (cbcFixedBlockMacToPrfDistinguisher ℓ adversary) n))
        (ProbComp.eval (prfIdealGame id id (cbcFixedBlockMacToPrfDistinguisher ℓ adversary) n)) +
      ((Q : ℝ≥0) + 1) ^ 2 * (ℓ n : ℝ≥0) ^ 2 / (2 * 2 ^ n) +
      (1 : ℝ≥0) / 2 ^ n := by
  rw [eval_sufCmaGame_det (cbcFixedBlockMAC ℓ hℓ family hpoly) (by rfl) (cbcMacFamily family)
    (by rfl) (by rfl)]
  simp only [cbcFixedBlockMAC_msgLen]
  have hmac := succProbability_macSufCmaGameOn_le
    (valid := fun m q => q.length == ℓ m * m)
    (fun key query _ => length_cbcMacFamily hlen key query) adversary n
  have hsub (w : List Bool) (hw : w.length = ℓ n * n) : cbcBlockValid ℓ n w = true := by
    simp [cbcBlockValid, hw, hpos, hn, Nat.mul_mod_left]
  let M := macToPrfOnDistinguisher (fun m msg => msg.length == ℓ m * m) adversary
  rw [eval_prfRealGameOn_length_eq,
    ← eval_prfRealGameOn_restrictLengthDistinguisher (fun m => ℓ m * m)
      (fun key _ _ => length_cbcMacFamily hlen key _) hsub M,
    eval_prfIdealGameOn_length_eq,
    ← eval_prfIdealGameOn_restrictLengthDistinguisher (fun m => ℓ m * m) hsub M] at hmac
  have hMRestQ : (restrictLengthDistinguisher (fun m => ℓ m * m) M n []).IsQueryBounded (Q + 1) :=
    isQueryBounded_restrictLengthDistinguisher _ M
      (isQueryBounded_macToPrfOnDistinguisher _ adversary hQ)
  have hprf := advantage_cbcMac_le hlen ℓ
    (restrictLengthDistinguisher (fun m => ℓ m * m) M) hMRestQ
    (isPrefixFreeOn_restrictLengthDistinguisher _ M n)
  rw [Nat.cast_add, Nat.cast_one] at hprf
  exact hmac.trans (add_le_add hprf le_rfl)

/-- **Fixed-block-count basic CBC-MAC is `SUFCMA`-secure** ([BonehShoup2023], Section 6.3 Theorem
6.2 and Section 6.4.1 Theorem 6.3, printed pp. 224 and 226–229, specialized to fixed positive block
count `ℓ n`): for any `PseudorandomFunction family` and unary polynomial-time `ℓ` with
`∀ n, 0 < ℓ n`, `cbcFixedBlockMAC ℓ hℓ family hF.polyTime` satisfies `MACScheme.SUFCMA`. -/
theorem PseudorandomFunction.sufCma_cbcFixedBlockMAC
    {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family)
    {ℓ : ℕ → ℕ} (hℓ : ComputableInPolyTime ℓ encUnary encUnary) (hpos : ∀ n, 0 < ℓ n) :
    (cbcFixedBlockMAC ℓ hℓ family hF.polyTime).SUFCMA := by
  apply Game.Indistinguishable.of_negligible_succProbability
  intro adversary hadversary
  obtain ⟨c, d, hbounds⟩ := hadversary.query_bounds
  let Q : ℕ → ℕ := fun n => c * (n + 2) ^ d
  have hQ (n : ℕ) : (adversary n []).IsQueryBounded (Q n) := by
    simpa only [Q, List.length_nil, Nat.add_zero] using (hbounds n []).1
  have hprf := hF.secure (cbcFixedBlockMacToPrfDistinguisher ℓ adversary)
    (isOraclePPT_cbcFixedBlockMacToPrfDistinguisher hℓ hadversary)
  negligible eventually (Filter.eventually_ge_atTop 1).mono fun n hn =>
    succProbability_sufCmaGame_cbcFixedBlockMAC_le ℓ hℓ hF.polyTime hF.length_eq adversary
      hn (hpos n) (hQ n)

/-- Deterministic `MACScheme` authenticating `k n * n`-bit (`k n`-block, `k n = 0` permitted)
messages via length-prepended CBC-MAC `lengthPrependedCbcMacFamily family`. -/
noncomputable def lengthPrependedBlockMAC (k : ℕ → ℕ)
    (hk : ComputableInPolyTime k encUnary encUnary)
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits) : MACScheme where
  msgLen n := k n * n
  msgLen_polyTime := by polytime
  keyGen := BitString.sampleList
  sign sk msg := pure (lengthPrependedCbcMacFamily family sk msg)
  verify sk msg tag := lengthPrependedCbcMacFamily family sk msg == tag
  keyGen_ppt := isPPTOn_sampleList
  sign_ppt := (computableInPolyTime_lengthPrependedCbcMacFamily hpoly).isPPTOn
  verify_polyTime := detVerify_polyTime (computableInPolyTime_lengthPrependedCbcMacFamily hpoly)
  verify_sign _ sk _ msg _ tag htag :=
    detVerify_sign (lengthPrependedCbcMacFamily family) sk msg tag htag

@[simp]
theorem lengthPrependedBlockMAC_msgLen (k : ℕ → ℕ) (hk : ComputableInPolyTime k encUnary encUnary)
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits) (n : ℕ) :
    (lengthPrependedBlockMAC k hk family hpoly).msgLen n = k n * n := by rfl

@[simp]
theorem lengthPrependedBlockMAC_sign (k : ℕ → ℕ) (hk : ComputableInPolyTime k encUnary encUnary)
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits) (sk msg : List Bool) :
    (lengthPrependedBlockMAC k hk family hpoly).sign sk msg =
      pure (lengthPrependedCbcMacFamily family sk msg) := by rfl

@[simp]
theorem lengthPrependedBlockMAC_verify (k : ℕ → ℕ) (hk : ComputableInPolyTime k encUnary encUnary)
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits) (sk msg tag : List Bool) :
    (lengthPrependedBlockMAC k hk family hpoly).verify sk msg tag =
      (lengthPrependedCbcMacFamily family sk msg == tag) := by rfl

/-- **`lengthPrependedBlockMAC` is `SUFCMA`-secure** at every unary polynomial-time block-count
schedule `k` (including `k n = 0` empty messages). -/
theorem PseudorandomFunction.sufCma_lengthPrependedBlockMAC
    {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family)
    {k : ℕ → ℕ} (hk : ComputableInPolyTime k encUnary encUnary) :
    (lengthPrependedBlockMAC k hk family hF.polyTime).SUFCMA := by
  apply Game.Indistinguishable.of_negligible_succProbability
  intro adversary hadversary
  let M := macToPrfOnDistinguisher (fun m msg => msg.length == k m * m) adversary
  have hprf := (hF.prfOver_lengthPrependedCbcMac hk).secure M
    (isOraclePPT_macToPrfOnDistinguisher (by polytime) hadversary)
  simp only [← eval_prfRealGameOn_length_eq, ← eval_prfIdealGameOn_length_eq] at hprf
  have hdet (n : ℕ) :
      ProbComp.eval ((lengthPrependedBlockMAC k hk family hF.polyTime).sufCmaGame adversary n) =
      ProbComp.eval (macSufCmaGameOn (fun m q => q.length == k m * m)
        (lengthPrependedCbcMacFamily family) adversary n) := by
    simpa only [lengthPrependedBlockMAC_msgLen] using eval_sufCmaGame_det
      (lengthPrependedBlockMAC k hk family hF.polyTime) rfl
      (lengthPrependedCbcMacFamily family) rfl rfl adversary n
  negligible using fun n => (congrArg Game.succProbability (hdet n)).trans_le
    (succProbability_macSufCmaGameOn_le
      (fun key query _ => length_lengthPrependedCbcMacFamily hF.length_eq key query) adversary n)

end Cslib.Crypto
