/-
Copyright (c) 2026 Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.BatchOT
public import CslibFrontier.Crypto.Protocols.MPC.Beaver
public import CslibFrontier.Crypto.Protocols.MPC.SharedMul
public import Mathlib.Data.ZMod.Basic
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform
-- `import all` only to unfold unexposed `Beaver.beaverTripleFunctionality`.
import all CslibFrontier.Crypto.Protocols.MPC.Beaver

/-!
# Two-Party Multiplication over `ZMod q` and Beaver Triple Generation from Batched 1-out-of-2 OT

This module formalizes Gilboa-style two-party multiplication over `ZMod q` from batched 1-out-of-2
oblivious transfer (`batchOTSpec` / `batchOTWorld`) together with symmetric additive-share
multiplication and preprocessing of additive Beaver multiplication triples (`Beaver.TripleShare`):

1. **Binary Bit-Decomposition & Gilboa's Algebraic Identity (`bitVecValue`, `natToBits`,
   `zmodToBits`, `otMul2SenderPairs`, `otMul2Share0`, `otMul2Share1`, `otMul2_correct`):**
   for a `k`-bit vector `bits : Fin k → Bool` representing
   `bitVecValue bits = ∑ i : Fin k, (if bits i then 1 else 0) * 2 ^ (i : ℕ)` in any ring `R`, the
   sender (holding `a : R` and random masks `r : Fin k → R`) prepares the 1-out-of-2 OT pairs
   `m_{i, 0} = -r i` and `m_{i, 1} = a * 2^i - r i` while the receiver selects `bits i` and
   receives `t i = m_{i, bits i}`. For every mask vector `r`, the local additive shares
   `u₀ = ∑ i, r i` and `u₁ = ∑ i, t i` satisfy `u₀ + u₁ = a * bitVecValue bits`. Setting
   `k = Nat.clog 2 q` decomposes any `b : ZMod q` (`[NeZero q]`) into `zmodToBits b`.
2. **Ideal-OT Experiments & Perfect Semi-Honest Security (`otMul2BitsReal`,
   `otMul2BitsReceiverSim`, `otMul2BitsProtocol`, `otMul2Protocol`,
   `perfectSemiHonestPrivate_otMul2Bits`, `perfectSemiHonestPrivate_otMul2`):**
   in `batchOTWorld k (ZMod q)`, the sender's view consists solely of uniform random masks `r`
   independent of `bits`, and the receiver's view `(bits, t)` together with the sender's output
   `u₀` is identically distributed to sampling `t ← $ᵗ (Fin k → ZMod q)` and setting
   `u₀ = a * bitVecValue bits - ∑ i, t i`. When `1 < q` (`0 < Nat.clog 2 q`), `otMul2Protocol q`
   realizes `otMul2Functionality q` with `PerfectSemiHonestPrivate` against every static
   coalition `I : Finset (Fin 2)`.
3. **Symmetric Additive-Share Multiplication (`shareMulFromOTProtocol`,
   `perfectSemiHonestPrivate_shareMulFromOT`):**
   given additive shares `(a₀, b₀)` and `(a₁, b₁)` over `ZMod q`, two batched 1-out-of-2 OT
   invocations (for the cross-terms `a₀ * b₁` and `a₁ * b₀`) produce additive shares `c₀, c₁`
   satisfying `c₀ + c₁ = (a₀ + a₁) * (b₀ + b₁)` and realize `sharedMulFunctionality 2` in
   `batchOTWorld (otBitWidth q) (ZMod q)` with `PerfectSemiHonestPrivate` against every static
   coalition `I : Finset (Fin 2)`.
4. **Beaver Multiplication Triple Generation (`tripleSharesOfOTMul`, `tripleFromOTMulProtocol`,
   `perfectSemiHonestPrivate_tripleFromOTMul`):**
   sampling uniform local mask pairs `(a₀, b₀)` and `(a₁, b₁)` and running
   `shareMulFromOTProtocol q` yields valid `Beaver.TripleShare (ZMod q)` shares realizing
   `Beaver.beaverTripleFunctionality q 2` in `batchOTWorld (otBitWidth q) (ZMod q)` with
   `PerfectSemiHonestPrivate` against every static coalition `I : Finset (Fin 2)`.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.bitVecValue`, `Cslib.Crypto.Protocols.MPC.natToBits`,
  `Cslib.Crypto.Protocols.MPC.otBitWidth`, `Cslib.Crypto.Protocols.MPC.zmodToBits`:
  little-endian binary decomposition and evaluation over rings and `ZMod q`.
* `Cslib.Crypto.Protocols.MPC.otMul2SenderPairs`, `Cslib.Crypto.Protocols.MPC.otMul2Share0`,
  `Cslib.Crypto.Protocols.MPC.otMul2Share1`: Gilboa OT message pairs and local additive shares.
* `Cslib.Crypto.Protocols.MPC.otMul2BitsReal`, `Cslib.Crypto.Protocols.MPC.otMul2BitsReceiverSim`,
  `Cslib.Crypto.Protocols.MPC.otMul2BitsFunctionality`,
  `Cslib.Crypto.Protocols.MPC.otMul2BitsProtocol`, `Cslib.Crypto.Protocols.MPC.otMul2BitsSim`,
  `Cslib.Crypto.Protocols.MPC.otMul2Functionality`, `Cslib.Crypto.Protocols.MPC.otMul2Protocol`,
  `Cslib.Crypto.Protocols.MPC.otMul2Sim`: standalone experiments, functionalities, protocols, and
  coalition simulators for 2-party multiplication from batched 1-out-of-2 OT.
* `Cslib.Crypto.Protocols.MPC.shareMulFromOTOut0`,
  `Cslib.Crypto.Protocols.MPC.shareMulFromOTOut1`,
  `Cslib.Crypto.Protocols.MPC.shareMulFromOTProtocol`,
  `Cslib.Crypto.Protocols.MPC.shareMulFromOTSim`: symmetric 2-party shared multiplication in
  `batchOTWorld (otBitWidth q) (ZMod q)`.
* `Cslib.Crypto.Protocols.MPC.tripleSharesOfOTMul`,
  `Cslib.Crypto.Protocols.MPC.tripleFromOTMulProtocol`,
  `Cslib.Crypto.Protocols.MPC.tripleFromOTMulSim`: 2-party Beaver multiplication triple
  generation in `batchOTWorld (otBitWidth q) (ZMod q)`.

## Main results

* `Cslib.Crypto.Protocols.MPC.bitVecValue_natToBits`,
  `Cslib.Crypto.Protocols.MPC.bitVecValue_zmodToBits`: binary decomposition correctness.
* `Cslib.Crypto.Protocols.MPC.otMul2_correct`, `Cslib.Crypto.Protocols.MPC.otMul2ZMod_correct`:
  exact algebraic reconstruction `u₀ + u₁ = a * b` for every mask vector `r`.
* `Cslib.Crypto.Protocols.MPC.eval_otMul2BitsReal_senderView`,
  `Cslib.Crypto.Protocols.MPC.eval_otMul2BitsReal_receiverJoint`: standalone sender view
  uniformity and receiver `(bits, t, u₀)` simulation for any bit-width `k : ℕ`.
* `Cslib.Crypto.Protocols.MPC.perfectSemiHonestPrivate_otMul2Bits`,
  `Cslib.Crypto.Protocols.MPC.perfectSemiHonestPrivate_otMul2`: full-coalition perfect
  semi-honest privacy of `otMul2BitsProtocol` and `otMul2Protocol` in `batchOTWorld`.
* `Cslib.Crypto.Protocols.MPC.shareMulFromOT_correct`,
  `Cslib.Crypto.Protocols.MPC.perfectSemiHonestPrivate_shareMulFromOT`: algebraic correctness and
  full-coalition perfect semi-honest privacy of `shareMulFromOTProtocol` for
  `sharedMulFunctionality 2`.
* `Cslib.Crypto.Protocols.MPC.tripleSharesOfOTMul_correct`,
  `Cslib.Crypto.Protocols.MPC.mem_support_tripleFromOTMulProtocol`,
  `Cslib.Crypto.Protocols.MPC.perfectSemiHonestPrivate_tripleFromOTMul`,
  `Cslib.Crypto.Protocols.MPC.eval_restrict_output_tripleFromOTMul`: algebraic correctness,
  support membership, full-coalition perfect semi-honest privacy against
  `Beaver.beaverTripleFunctionality q 2`, and proper-coalition output uniformity of
  `tripleFromOTMulProtocol`.

## References

* N. Gilboa, *Two Party RSA Key Generation*, CRYPTO 1999 (binary-expansion 2-party
  multiplication via 1-out-of-2 OT; locator not verified from PDF).
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Chapter 23,
  Exercises 23.4–23.5 (motivation for OT-based multiplication and Beaver triple generation;
  unverified edition/page locators).
* [D. Beaver, *Efficient Multiparty Protocols Using Circuit Randomization*][Beaver1991].
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib.Probability Cslib.ProbComp
open scoped ENNReal

/-! ### 1. Little-endian binary decomposition and Gilboa's algebraic identity -/

/-- Value in a semiring `R` represented by a little-endian bit vector `bits : Fin k → Bool`:
`∑ i : Fin k, (if bits i then (1 : R) else 0) * (2 : R) ^ (i : ℕ)`. -/
@[expose] def bitVecValue {R : Type*} [Semiring R] {k : ℕ} (bits : Fin k → Bool) : R :=
  ∑ i : Fin k, (if bits i then (1 : R) else 0) * (2 : R) ^ (i : ℕ)

/-- Little-endian `k`-bit decomposition of a natural number `n`. -/
@[expose] def natToBits (k n : ℕ) : Fin k → Bool :=
  fun i => n.testBit i

/-- For `n < 2 ^ k`, evaluating `bitVecValue (natToBits k n)` in any semiring `R` yields
`(n : R)`. -/
theorem bitVecValue_natToBits {R : Type*} [Semiring R] {k n : ℕ} (hn : n < 2 ^ k) :
    bitVecValue (R := R) (natToBits k n) = (n : R) := by
  induction k generalizing n with
  | zero =>
    have hn0 : n = 0 := by
      simp only [pow_zero] at hn
      omega
    subst hn0
    simp [bitVecValue]
  | succ k ih =>
    dsimp only [bitVecValue, natToBits]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, Nat.testBit_succ]
    have hdiv : n / 2 < 2 ^ k := by
      rw [pow_succ'] at hn
      omega
    have hpow : ∀ i : Fin k,
        (if (n / 2).testBit i then (1 : R) else 0) * (2 : R) ^ ((i : ℕ) + 1) =
          ((if (n / 2).testBit i then (1 : R) else 0) * (2 : R) ^ (i : ℕ)) * 2 := by
      intro i
      rw [pow_succ, mul_assoc]
    simp_rw [hpow, ← Finset.sum_mul]
    have hih : (∑ i : Fin k, (if (n / 2).testBit i then (1 : R) else 0) * (2 : R) ^ (i : ℕ)) =
        ((n / 2 : ℕ) : R) := ih hdiv
    rw [hih]
    have htb := Nat.testBit_zero n
    rcases Nat.mod_two_eq_zero_or_one n with hm | hm <;> simp [htb, hm]
    · simpa [Nat.cast_mul] using congrArg (Nat.cast : ℕ → R) (by omega : n / 2 * 2 = n)
    · simpa [Nat.cast_add, Nat.cast_mul] using
        congrArg (Nat.cast : ℕ → R) (by omega : 1 + n / 2 * 2 = n)

/-- Canonical bit-width `⌈log₂ q⌉` sufficient to represent every element of `ZMod q`. -/
@[expose, reducible] def otBitWidth (q : ℕ) : ℕ :=
  Nat.clog 2 q

/-- Little-endian binary decomposition of `b : ZMod q` into `otBitWidth q` bits. -/
@[expose] def zmodToBits {q : ℕ} [NeZero q] (b : ZMod q) : Fin (otBitWidth q) → Bool :=
  natToBits (otBitWidth q) b.val

/-- Evaluating `bitVecValue (zmodToBits b)` in `ZMod q` recovers `b`. -/
theorem bitVecValue_zmodToBits {q : ℕ} [NeZero q] (b : ZMod q) :
    bitVecValue (zmodToBits b) = b := by
  have hlt : b.val < 2 ^ otBitWidth q :=
    lt_of_lt_of_le (ZMod.val_lt b) (Nat.le_pow_clog one_lt_two q)
  rw [zmodToBits, bitVecValue_natToBits hlt, ZMod.natCast_zmod_val]

/-- Sender's 1-out-of-2 OT message pairs for Gilboa-style multiplication of `a : R` by a
`k`-bit vector using random masks `r : Fin k → R`: for bit position `i`,
`m_{i, 0} = -r i` and `m_{i, 1} = a * 2^i - r i`. -/
@[expose] def otMul2SenderPairs {R : Type*} [Ring R] {k : ℕ} (a : R) (r : Fin k → R) :
    Fin k → Bool → R :=
  fun i bit => (if bit then a * (2 : R) ^ (i : ℕ) else 0) - r i

/-- Sender's local additive share `u₀ = ∑ i, r i` in Gilboa-style multiplication. -/
@[expose] def otMul2Share0 {R : Type*} [AddCommMonoid R] {k : ℕ} (r : Fin k → R) : R :=
  ∑ i : Fin k, r i

/-- Receiver's local additive share `u₁ = ∑ i, t i` in Gilboa-style multiplication. -/
@[expose] def otMul2Share1 {R : Type*} [AddCommMonoid R] {k : ℕ} (t : Fin k → R) : R :=
  ∑ i : Fin k, t i

/-- **Gilboa (1999) algebraic correctness:** for every `a : R`, `bits : Fin k → Bool`, and
mask vector `r : Fin k → R`, the local additive shares `u₀ = ∑ i, r i` and
`u₁ = ∑ i, otMul2SenderPairs a r i (bits i)` sum identically to `a * bitVecValue bits`. -/
theorem otMul2_correct {R : Type*} [Ring R] {k : ℕ} (a : R) (bits : Fin k → Bool)
    (r : Fin k → R) :
    otMul2Share0 r + otMul2Share1 (fun i => otMul2SenderPairs a r i (bits i)) =
      a * bitVecValue bits := by
  simp only [otMul2Share0, otMul2Share1, otMul2SenderPairs, bitVecValue, ← Finset.sum_add_distrib,
    add_sub_cancel, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases bits i <;> simp

/-- Corollary for `b : ZMod q`: decomposing `b` into `otBitWidth q` bits yields additive shares
summing identically to `a * b` for every mask vector `r`. -/
theorem otMul2ZMod_correct {q : ℕ} [NeZero q] (a b : ZMod q)
    (r : Fin (otBitWidth q) → ZMod q) :
    otMul2Share0 r + otMul2Share1 (fun i => otMul2SenderPairs a r i (zmodToBits b i)) =
      a * b := by
  rw [otMul2_correct, bitVecValue_zmodToBits]

/-! ### 2. Standalone ideal-OT view-and-output experiments and privacy -/

/-- Standalone ideal-OT execution of Gilboa multiplication on sender input `a : ZMod q` and
receiver bit-vector `bits : Fin k → Bool`, returning `(r, t, u₀, u₁)`. -/
@[expose] noncomputable def otMul2BitsReal (k q : ℕ) [NeZero q] (a : ZMod q) (bits : Fin k → Bool) :
    ProbComp ((Fin k → ZMod q) × (Fin k → ZMod q) × ZMod q × ZMod q) := do
  let r ← ProbComp.uniform (Fin k → ZMod q)
  let t : Fin k → ZMod q := fun i => otMul2SenderPairs a r i (bits i)
  return (r, t, otMul2Share0 r, otMul2Share1 t)

/-- **Perfect sender privacy (for arbitrary `k : ℕ`):** in `otMul2BitsReal`, the sender's view
`(a, r)` is uniformly distributed on `Fin k → ZMod q` and independent of the receiver's `bits`. -/
theorem eval_otMul2BitsReal_senderView (k q : ℕ) [NeZero q] (a : ZMod q) (bits : Fin k → Bool) :
    (ProbComp.eval (otMul2BitsReal k q a bits)).map (fun res => (a, res.1)) =
      (PMF.uniformOfFintype (Fin k → ZMod q)).map (fun r => (a, r)) := by
  simp [otMul2BitsReal, pmf_norm]

/-- Receiver view-and-honest-output simulator for `otMul2BitsReal`: samples a uniform vector
`t ← $ᵗ (Fin k → ZMod q)` and sets `u₀ = a * bitVecValue bits - otMul2Share1 t`. -/
@[expose] noncomputable def otMul2BitsReceiverSim (k q : ℕ) [NeZero q] (a : ZMod q)
    (bits : Fin k → Bool) :
    ProbComp ((Fin k → Bool) × (Fin k → ZMod q) × ZMod q) := do
  let t ← ProbComp.uniform (Fin k → ZMod q)
  return (bits, t, a * bitVecValue bits - otMul2Share1 t)

private def otMul2MaskEquiv {R : Type*} [Ring R] {k : ℕ} (a : R) (bits : Fin k → Bool) :
    (Fin k → R) ≃ (Fin k → R) where
  toFun r i := otMul2SenderPairs a r i (bits i)
  invFun t i := otMul2SenderPairs a t i (bits i)
  left_inv r := by
    ext i
    simp [otMul2SenderPairs]
  right_inv t := by
    ext i
    simp [otMul2SenderPairs]

private theorem otMul2Share0_maskEquiv {R : Type*} [Ring R] {k : ℕ} (a : R)
    (bits : Fin k → Bool) (t : Fin k → R) :
    otMul2Share0 (otMul2MaskEquiv a bits t) = a * bitVecValue bits - otMul2Share1 t := by
  have h := otMul2_correct a bits (otMul2MaskEquiv a bits t)
  have hinv : (fun i => otMul2SenderPairs a (otMul2MaskEquiv a bits t) i (bits i)) = t :=
    (otMul2MaskEquiv a bits).right_inv t
  rw [hinv] at h
  exact eq_sub_of_add_eq h

/-- **Perfect receiver privacy (for arbitrary `k : ℕ`):** the real joint distribution of
`(bits, t, u₀)` in `otMul2BitsReal` equals `otMul2BitsReceiverSim k q a bits`. -/
theorem eval_otMul2BitsReal_receiverJoint (k q : ℕ) [NeZero q]
    (a : ZMod q) (bits : Fin k → Bool) :
    (ProbComp.eval (otMul2BitsReal k q a bits)).map (fun (_, t, u₀, _) => (bits, t, u₀)) =
      ProbComp.eval (otMul2BitsReceiverSim k q a bits) := by
  simp only [otMul2BitsReal, otMul2BitsReceiverSim, bind_pure_comp, pmf_norm,
    ProbComp.eval_uniform]
  conv_lhs => rw [← PMF.uniformOfFintype_map_equiv (otMul2MaskEquiv a bits), PMF.map_comp]
  refine congrArg (PMF.map · (PMF.uniformOfFintype (Fin k → ZMod q))) (funext fun t => ?_)
  dsimp [Function.comp_def, otMul2MaskEquiv]
  rw [← otMul2Share0_maskEquiv a bits t]
  have hinv :
      (fun i => otMul2SenderPairs a (fun j => otMul2SenderPairs a t j (bits j)) i (bits i)) =
        t :=
    (otMul2MaskEquiv a bits).right_inv t
  rw [hinv]
  rfl

/-! ### 3. Sum-of-uniforms and `sampleAdditiveShares` equivalence -/

private theorem card_pi_fin_eq_mul_pred (k : ℕ) [NeZero k] (G : Type*) [Fintype G] :
    Fintype.card G * Fintype.card (Fin (k - 1) → G) = Fintype.card (Fin k → G) := by
  simp only [Fintype.card_fun, Fintype.card_fin]
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  calc
    Fintype.card G * Fintype.card G ^ (k - 1) = Fintype.card G ^ (k - 1 + 1) := by
      rw [pow_succ, mul_comm]
    _ = Fintype.card G ^ k := by
      rw [Nat.sub_add_cancel hk]

/-- For `[NeZero k]` and a finite commutative group `G`, sampling a uniform `k`-tuple
`r : Fin k → G` together with its sum `∑ i, r i` has the exact same joint distribution as
sampling a uniform sum `u : G` and then sampling `r ← sampleAdditiveShares k u`. -/
theorem eval_uniform_pi_sum_eq_bind_sampleAdditiveShares (k : ℕ) [NeZero k]
    {G : Type} [AddCommGroup G] [Fintype G] :
    (ProbComp.eval (ProbComp.uniform (Fin k → G))).map (fun r => (r, ∑ i : Fin k, r i)) =
      (ProbComp.eval (ProbComp.uniform G)).bind fun u =>
        (ProbComp.eval (ProbComp.sampleAdditiveShares k u)).map (fun r => (r, u)) := by
  classical
  ext ⟨r₀, u₀⟩
  simp only [ProbComp.sampleAdditiveShares, ProbComp.eval_map, PMF.map_comp, Function.comp_def,
    PMF.map_apply, PMF.bind_apply, ProbComp.eval_uniform, PMF.uniformOfFintype_apply]
  have hinner : ∀ u : G,
      (∑' init : Fin (k - 1) → G,
        if (r₀, u₀) = (ProbComp.completeShares k u init, u) then
          (Fintype.card (Fin (k - 1) → G) : ℝ≥0∞)⁻¹
        else 0) =
      if u₀ = ∑ i : Fin k, r₀ i ∧ u = u₀ then
        (Fintype.card (Fin (k - 1) → G) : ℝ≥0∞)⁻¹
      else 0 := by
    intro u
    by_cases hu : u = u₀
    · subst hu
      by_cases hsum : u = ∑ i : Fin k, r₀ i
      · simp only [Prod.mk.injEq, and_true, hsum, ↓reduceIte]
        rw [tsum_eq_single (ProbComp.initOfShares k r₀)]
        · have hc : ProbComp.completeShares k (∑ i : Fin k, r₀ i) (ProbComp.initOfShares k r₀) =
              r₀ :=
            ProbComp.completeShares_initOfShares k rfl
          simp [hc]
        · intro init hne
          have hc : r₀ ≠ ProbComp.completeShares k (∑ i : Fin k, r₀ i) init := by
            intro heq
            apply hne
            have := congrArg (ProbComp.initOfShares k) heq
            simpa using this.symm
          simp [hc]
      · simp only [Prod.mk.injEq, and_true, hsum, ↓reduceIte]
        have hc : ∀ init, r₀ ≠ ProbComp.completeShares k u init := by
          intro init heq
          apply hsum
          have := congrArg (fun f : Fin k → G => ∑ i : Fin k, f i) heq
          simpa using this.symm
        simp [hc]
    · have hleft : ∀ init : Fin (k - 1) → G,
          (if r₀ = ProbComp.completeShares k u init ∧ u₀ = u then
            (Fintype.card (Fin (k - 1) → G) : ℝ≥0∞)⁻¹
          else 0) = 0 := by
        intro init
        simp only [ite_eq_right_iff]
        intro h
        exact absurd h.2.symm hu
      have hright :
          (if u₀ = ∑ i : Fin k, r₀ i ∧ u = u₀ then
            (Fintype.card (Fin (k - 1) → G) : ℝ≥0∞)⁻¹
          else 0) = 0 := by
        simp only [ite_eq_right_iff]
        intro h
        exact absurd h.2 hu
      simp only [Prod.mk.injEq, hleft, hright, tsum_zero]
  simp_rw [hinner]
  simp only [Prod.mk.injEq]
  by_cases hsum : u₀ = ∑ i : Fin k, r₀ i
  · simp only [hsum, true_and]
    rw [tsum_eq_single (∑ i : Fin k, r₀ i), tsum_eq_single r₀]
    · simp only [and_self, ↓reduceIte]
      rw [← ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)), ← Nat.cast_mul,
        card_pi_fin_eq_mul_pred]
    · intro r hr
      simp [Ne.symm hr]
    · intro u hu
      simp [hu]
  · simp only [hsum, false_and, ↓reduceIte]
    have hnone : ∀ r : Fin k → G, ¬(r₀ = r ∧ u₀ = ∑ i : Fin k, r i) := by
      rintro r ⟨rfl, hu⟩
      exact hsum hu
    simp [hnone]

/-- Pushing a uniform distribution on `Fin k → G` (`[NeZero k]`) forward along `r ↦ ∑ i, r i`
gives the uniform distribution on `G`. -/
theorem eval_uniform_pi_map_sum (k : ℕ) [NeZero k]
    {G : Type} [AddCommGroup G] [Fintype G] :
    (ProbComp.eval (ProbComp.uniform (Fin k → G))).map (fun r => ∑ i : Fin k, r i) =
      PMF.uniformOfFintype G := by
  have h := congrArg (PMF.map Prod.snd)
    (eval_uniform_pi_sum_eq_bind_sampleAdditiveShares k (G := G))
  simp only [PMF.map_comp, Function.comp_def, PMF.map_bind] at h
  have hconst : ∀ a : G,
      (ProbComp.eval (ProbComp.sampleAdditiveShares k a)).map (fun _ => a) = PMF.pure a :=
    fun a => PMF.map_const _ a
  simp_rw [hconst] at h
  simp only [PMF.bind_pure, ProbComp.eval_uniform] at h
  rwa [ProbComp.eval_uniform]

/-! ### 4. `otMul2BitsProtocol` and `otMul2Protocol` in `batchOTWorld` -/

/-- Schedule for `otMul2BitsProtocol` and `otMul2Protocol`: a single joint 2-party invocation
of `batchOTSpec k (ZMod q)` with Party `0` as sender and Party `1` as receiver. -/
@[expose, reducible] def otMul2Schedule (k q : ℕ) : Schedule 2 (batchOTSpec k (ZMod q)) :=
  [.oracle () (Function.Embedding.refl (Fin 2))]

/-- Local coins for `otMul2BitsProtocol` and `otMul2Protocol`: Party `0` holds a mask vector
`Fin k → ZMod q`; Party `1` uses `()`. -/
@[expose, reducible] def OTMultCoins (k q : ℕ) (i : Fin 2) : Type :=
  Fin.cases (motive := fun _ => Type) (Fin k → ZMod q) (fun _ => Unit) i

/-- Input tuple type for `otMul2BitsProtocol`: Party `0` inputs `a : ZMod q` and Party `1`
inputs `bits : Fin k → Bool`. -/
@[expose, reducible] def OTMultBitsIn (k q : ℕ) (i : Fin 2) : Type :=
  Fin.cases (motive := fun _ => Type) (ZMod q) (fun _ => Fin k → Bool) i

/-- Ideal 2-party functionality for bit-vector multiplication over `ZMod q`: samples uniform
additive shares of `a * bitVecValue bits`. -/
@[expose] noncomputable def otMul2BitsFunctionality (k q : ℕ) [NeZero q] :
    Functionality 2 (OTMultBitsIn k q) (fun _ => ZMod q) :=
  fun x =>
    let a : ZMod q := x 0
    let bits : Fin k → Bool := x 1
    ProbComp.sampleAdditiveShares 2 (a * bitVecValue bits)

/-- Package Party `0`'s mask vector `r : Fin k → ZMod q` and Party `1`'s coin `()` into the
2-party coin tuple. -/
@[expose] def otMul2Coins {k q : ℕ} (r : Fin k → ZMod q) (i : Fin 2) : OTMultCoins k q i :=
  Fin.cases r (fun _ => ()) i

/-- Oracle query function for `otMul2BitsProtocol`. -/
@[expose] def otMul2BitsQuery {k q : ℕ} [NeZero q]
    (s : Fin ((batchOTSpec k (ZMod q)).arity ()))
    (st : OTMultBitsIn k q (Function.Embedding.refl (Fin 2) s) ×
      OTMultCoins k q (Function.Embedding.refl (Fin 2) s)) :
    (batchOTSpec k (ZMod q)).Query () s :=
  Fin.cases
    (motive := fun s =>
      OTMultBitsIn k q (Function.Embedding.refl (Fin 2) s) ×
        OTMultCoins k q (Function.Embedding.refl (Fin 2) s) →
        (batchOTSpec k (ZMod q)).Query () s)
    (fun st => otMul2SenderPairs st.1 st.2)
    (fun j => Fin.cases
      (motive := fun j =>
        OTMultBitsIn k q (Function.Embedding.refl (Fin 2) j.succ) ×
          OTMultCoins k q (Function.Embedding.refl (Fin 2) j.succ) →
          (batchOTSpec k (ZMod q)).Query () j.succ)
      (fun st => st.1) (fun l => l.elim0) j)
    s st

/-- Output extraction function for `otMul2BitsProtocol`. -/
@[expose] def otMul2BitsOutput {k q : ℕ} [NeZero q] (i : Fin 2)
    (st : (OTMultBitsIn k q i × OTMultCoins k q i) ×
      (Round.oracle (spec := batchOTSpec k (ZMod q)) ()
        (Function.Embedding.refl (Fin 2))).Received i) : ZMod q :=
  Fin.cases
    (motive := fun i => (OTMultBitsIn k q i × OTMultCoins k q i) ×
      (Round.oracle (spec := batchOTSpec k (ZMod q)) ()
        (Function.Embedding.refl (Fin 2))).Received i → ZMod q)
    (fun ((_, r), _) => otMul2Share0 r)
    (fun j => Fin.cases
      (motive := fun j => (OTMultBitsIn k q j.succ × OTMultCoins k q j.succ) ×
        (Round.oracle (spec := batchOTSpec k (ZMod q)) ()
          (Function.Embedding.refl (Fin 2))).Received j.succ → ZMod q)
      (fun st => otMul2Share1 (st.2 1 rfl)) (fun l => l.elim0) j)
    i st

/-- Gilboa-style 2-party bit-vector multiplication protocol in the `batchOTSpec k (ZMod q)`-hybrid
model. -/
@[expose] noncomputable def otMul2BitsProtocol (k q : ℕ) [NeZero q] :
    Protocol 2 (batchOTSpec k (ZMod q)) (otMul2Schedule k q)
      (OTMultBitsIn k q) (OTMultCoins k q) (fun _ => ZMod q) where
  sampleCoins i :=
    Fin.cases (motive := fun i => ProbComp (OTMultCoins k q i))
      (ProbComp.uniform (Fin k → ZMod q)) (fun _ => pure ()) i
  steps := .oracle otMul2BitsQuery (.done otMul2BitsOutput)

/-- Construct Party `i`'s `PartyView` in `otMul2BitsProtocol` from its input `xi`, Party `0`'s
coins `r`, and Party `1`'s received OT answer vector `t`. -/
@[expose] def otMul2BitsView {k q : ℕ} [NeZero q] (i : Fin 2) (xi : OTMultBitsIn k q i)
    (r t : Fin k → ZMod q) :
    PartyView (OTMultBitsIn k q) (OTMultCoins k q) (otMul2Schedule k q) i where
  input := xi
  coins := otMul2Coins r i
  received :=
    (fun s hs =>
      Fin.cases (motive := fun s => s = i → (batchOTSpec k (ZMod q)).Answer () s)
        (fun _ => ())
        (fun j => Fin.cases
          (motive := fun j => j.succ = i → (batchOTSpec k (ZMod q)).Answer () j.succ)
          (fun _ => t) (fun l => l.elim0) j)
        s hs, ())

/-- Coalition simulator for `otMul2BitsProtocol` against every static coalition
`I : Finset (Fin 2)`. -/
@[expose] noncomputable def otMul2BitsSim (k q : ℕ) [NeZero q] (I : Finset (Fin 2)) :
    CoalitionSimulator (otMul2Schedule k q) (OTMultBitsIn k q) (OTMultCoins k q)
      (fun _ => ZMod q) I :=
  fun xI yI =>
    if h0 : (0 : Fin 2) ∈ I then
      if h1 : (1 : Fin 2) ∈ I then do
        let r ← ProbComp.sampleAdditiveShares k (yI ⟨0, h0⟩)
        let t : Fin k → ZMod q := fun i => otMul2SenderPairs (xI ⟨0, h0⟩) r i (xI ⟨1, h1⟩ i)
        return fun i => otMul2BitsView i.1 (xI i) r t
      else do
        let r ← ProbComp.sampleAdditiveShares k (yI ⟨0, h0⟩)
        return fun i => otMul2BitsView i.1 (xI i) r (fun _ => 0)
    else
      if h1 : (1 : Fin 2) ∈ I then do
        let t ← ProbComp.sampleAdditiveShares k (yI ⟨1, h1⟩)
        return fun i => otMul2BitsView i.1 (xI i) (fun _ => 0) t
      else
        pure fun i => otMul2BitsView i.1 (xI i) (fun _ => 0) (fun _ => 0)

private instance instFintypeOTMultCoins (k q : ℕ) [NeZero q] (i : Fin 2) :
    Fintype (OTMultCoins k q i) :=
  Fin.cases (inferInstanceAs (Fintype (Fin k → ZMod q))) (fun _ => inferInstanceAs (Fintype Unit)) i

private theorem eval_pi_otMul2Coins (k q : ℕ) [NeZero q] :
    ProbComp.eval (OracleComp.pi (otMul2BitsProtocol k q).sampleCoins) =
      (PMF.uniformOfFintype (Fin k → ZMod q)).map otMul2Coins := by
  classical
  ext c
  rw [ProbComp.eval_pi, PMF.pi_apply, Fin.prod_univ_two, PMF.map_apply]
  have hc : c = otMul2Coins (c 0) := by
    ext i
    fin_cases i <;> rfl
  have h0 : ProbComp.eval ((otMul2BitsProtocol k q).sampleCoins 0) (c 0) =
      PMF.uniformOfFintype (Fin k → ZMod q) (c 0) :=
    congrFun (congrArg DFunLike.coe (ProbComp.eval_uniform (α := Fin k → ZMod q))) (c 0)
  have h1 : ProbComp.eval ((otMul2BitsProtocol k q).sampleCoins 1) (c 1) = 1 :=
    PMF.pure_apply_self ()
  rw [h0, h1, mul_one]
  symm
  let r₀ : Fin k → ZMod q := c 0
  rw [tsum_eq_single r₀]
  · simp only [r₀, ← hc, ↓reduceIte]
  · intro r hr
    have hne : c ≠ otMul2Coins r := fun h => hr (congrFun h 0).symm
    simp [hne]

private theorem evalWith_otMul2BitsProtocol (k q : ℕ) [NeZero q]
    (x : (i : Fin 2) → OTMultBitsIn k q i) :
    (otMul2BitsProtocol k q).evalWith (batchOTWorld k (ZMod q)) x =
      (PMF.uniformOfFintype (Fin k → ZMod q)).map fun r =>
        let t : Fin k → ZMod q := fun i => otMul2SenderPairs (x 0) r i (x 1 i)
        let y : Fin 2 → ZMod q := Fin.cases (otMul2Share0 r) (fun _ => otMul2Share1 t)
        (fun i => otMul2BitsView i (x i) r t, y) := by
  rw [Protocol.evalWith_eq, eval_pi_otMul2Coins]
  simp only [pmf_norm, Protocol.outputOfView, otMul2BitsProtocol, batchOTWorld,
    Steps.evalWith_oracle, Steps.evalWith_done, Steps.outputAt]
  refine congrArg (PMF.map · (PMF.uniformOfFintype (Fin k → ZMod q))) (funext fun r => ?_)
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · fin_cases i
    · refine PartyView.ext rfl rfl (Prod.ext ?_ rfl)
      refine Round.received_oracle_ext fun s hs => ?_
      fin_cases s
      · rfl
      · simp at hs
    · refine PartyView.ext rfl rfl (Prod.ext ?_ rfl)
      refine Round.received_oracle_ext fun s hs => ?_
      fin_cases s
      · simp at hs
      · rfl
  · fin_cases i <;> rfl

private theorem eval_sampleAdditiveShares_two {G : Type} [AddCommGroup G] [Fintype G]
    (target : G) :
    ProbComp.eval (ProbComp.sampleAdditiveShares 2 target) =
      (PMF.uniformOfFintype G).map fun u₀ => Fin.cases u₀ (fun _ => target - u₀) := by
  simp only [ProbComp.sampleAdditiveShares, ProbComp.eval_map, ProbComp.eval_uniform]
  rw [← PMF.uniformOfFintype_map_equiv (Equiv.funUnique (Fin 1) G).symm, PMF.map_comp]
  refine congrArg (PMF.map · (PMF.uniformOfFintype G)) (funext fun u₀ => ?_)
  ext i
  fin_cases i
  · exact ProbComp.completeShares_castLE 2 target (fun _ => u₀) 0
  · change ProbComp.completeShares 2 target (fun _ => u₀) (⊤ : Fin 2) = target - u₀
    simp

/-- **Perfect semi-honest security of `otMul2BitsProtocol`:** for every `[NeZero q]`, every
`[NeZero k]`, and every static coalition `I : Finset (Fin 2)`, `otMul2BitsProtocol k q` realizes
`otMul2BitsFunctionality k q` in `batchOTWorld k (ZMod q)`. -/
theorem perfectSemiHonestPrivate_otMul2Bits (k q : ℕ) [NeZero q] [NeZero k] :
    PerfectSemiHonestPrivate (otMul2BitsProtocol k q)
      (batchOTWorld k (ZMod q)) (otMul2BitsFunctionality k q) (otMul2BitsSim k q) := by
  intro I x
  let a : ZMod q := x 0
  let bits : Fin k → Bool := x 1
  let target : ZMod q := a * bitVecValue bits
  simp only [idealJoint, otMul2BitsFunctionality, eval_sampleAdditiveShares_two,
    Protocol.realJoint, evalWith_otMul2BitsProtocol, pmf_norm]
  have hres0 : ∀ (h0 : (0 : Fin 2) ∈ I) {α : Fin 2 → Type} (f : ∀ i, α i),
      I.restrict f ⟨0, h0⟩ = f 0 :=
    fun _ _ _ => rfl
  have hres1 : ∀ (h1 : (1 : Fin 2) ∈ I) {α : Fin 2 → Type} (f : ∀ i, α i),
      I.restrict f ⟨1, h1⟩ = f 1 :=
    fun _ _ _ => rfl
  have hfc1 : ∀ (a b : ZMod q), Fin.cases a (fun _ => b) (1 : Fin 2) = b :=
    fun _ _ => rfl
  by_cases h0 : (0 : Fin 2) ∈ I
  · by_cases h1 : (1 : Fin 2) ∈ I
    · simp only [otMul2BitsSim, h0, h1, ↓reduceDIte, pmf_norm, hres0, hres1,
        Fin.cases_zero, Prod.map_apply, id_eq]
      have hr := eval_uniform_pi_sum_eq_bind_sampleAdditiveShares k (G := ZMod q)
      have hmap := congrArg (PMF.map fun p : (Fin k → ZMod q) × ZMod q =>
        let r := p.1
        let t : Fin k → ZMod q := fun i => otMul2SenderPairs a r i (bits i)
        let y : Fin 2 → ZMod q := Fin.cases p.2 (fun _ => target - p.2)
        (fun i : I => otMul2BitsView i.1 (I.restrict x i) r t, y)) hr
      simp only [← PMF.bind_pure_comp, pmf_norm, ProbComp.eval_uniform] at hmap
      dsimp only [a, bits, target] at hmap
      rw [← hmap]
      refine congrArg (fun f => (PMF.uniformOfFintype (Fin k → ZMod q)).bind f) (funext fun r => ?_)
      have hsum : otMul2Share1 (fun i => otMul2SenderPairs a r i (bits i)) =
          target - otMul2Share0 r :=
        eq_sub_of_add_eq' (otMul2_correct a bits r)
      refine congrArg PMF.pure (Prod.ext rfl (funext fun i => ?_))
      fin_cases i
      · rfl
      · exact hsum.symm
    · simp only [otMul2BitsSim, h0, h1, ↓reduceDIte, pmf_norm, hres0,
        Fin.cases_zero, Prod.map_apply, id_eq]
      have hr := eval_uniform_pi_sum_eq_bind_sampleAdditiveShares k (G := ZMod q)
      have hmap := congrArg (PMF.map fun p : (Fin k → ZMod q) × ZMod q =>
        let y : Fin 2 → ZMod q := Fin.cases p.2 (fun _ => target - p.2)
        (fun i : I => otMul2BitsView i.1 (I.restrict x i) p.1 (fun _ => 0), y)) hr
      simp only [← PMF.bind_pure_comp, pmf_norm, ProbComp.eval_uniform] at hmap
      rw [← hmap]
      refine congrArg (fun f => (PMF.uniformOfFintype (Fin k → ZMod q)).bind f) (funext fun r => ?_)
      have hsum : otMul2Share1 (fun i => otMul2SenderPairs a r i (bits i)) =
          target - otMul2Share0 r :=
        eq_sub_of_add_eq' (otMul2_correct a bits r)
      refine congrArg PMF.pure (Prod.ext (funext fun ⟨i, hi⟩ => ?_) (funext fun i => ?_))
      · fin_cases i
        · refine PartyView.ext rfl rfl (Prod.ext ?_ rfl)
          refine Round.received_oracle_ext fun s hs => ?_
          fin_cases s
          · rfl
          · simp at hs
        · exact (h1 hi).elim
      · fin_cases i
        · rfl
        · exact hsum.symm
  · by_cases h1 : (1 : Fin 2) ∈ I
    · simp only [otMul2BitsSim, h0, h1, ↓reduceDIte, pmf_norm, hres1,
        hfc1, Prod.map_apply, id_eq]
      have ht := eval_uniform_pi_sum_eq_bind_sampleAdditiveShares k (G := ZMod q)
      have hmap := congrArg (PMF.map fun p : (Fin k → ZMod q) × ZMod q =>
        let y : Fin 2 → ZMod q := Fin.cases (target - p.2) (fun _ => p.2)
        (fun i : I => otMul2BitsView i.1 (I.restrict x i) (fun _ => 0) p.1, y)) ht
      simp only [PMF.map_comp, Function.comp_def, PMF.map_bind, ProbComp.eval_uniform] at hmap
      have hsub : (PMF.uniformOfFintype (ZMod q)).map (fun u₀ => target - u₀) =
          PMF.uniformOfFintype (ZMod q) :=
        PMF.uniformOfFintype_map_equiv (Equiv.subLeft target)
      rw [← hsub, PMF.bind_map] at hmap
      simp only [← PMF.bind_pure_comp, sub_sub_cancel, pmf_norm] at hmap
      rw [← hmap]
      conv_rhs => rw [← PMF.uniformOfFintype_map_equiv (otMul2MaskEquiv a bits)]
      simp only [← PMF.bind_pure_comp, pmf_norm]
      refine congrArg (fun f => (PMF.uniformOfFintype (Fin k → ZMod q)).bind f) (funext fun t => ?_)
      dsimp only [otMul2MaskEquiv, Equiv.coe_fn_mk]
      have hinv :
          (fun i => otMul2SenderPairs a (fun j => otMul2SenderPairs a t j (bits j)) i (bits i)) =
            t :=
        (otMul2MaskEquiv a bits).right_inv t
      have hsum : otMul2Share0 (fun j => otMul2SenderPairs a t j (bits j)) =
          target - otMul2Share1 t := by
        have := otMul2Share0_maskEquiv a bits t
        simpa [otMul2MaskEquiv, Equiv.coe_fn_mk, target] using this
      refine congrArg PMF.pure (Prod.ext (funext fun ⟨i, hi⟩ => ?_) (funext fun i => ?_))
      · fin_cases i
        · exact (h0 hi).elim
        · change otMul2BitsView 1 (x 1) (fun _ => 0) t =
            otMul2BitsView 1 (x 1) (fun i => otMul2SenderPairs a t i (bits i))
              (fun i => otMul2SenderPairs a (fun j => otMul2SenderPairs a t j (bits j)) i (bits i))
          rw [hinv]
          rfl
      · fin_cases i
        · exact hsum.symm
        · change otMul2Share1 t =
            otMul2Share1 (fun i =>
              otMul2SenderPairs a (fun j => otMul2SenderPairs a t j (bits j)) i (bits i))
          rw [hinv]
    · simp only [otMul2BitsSim, h0, h1, ↓reduceDIte, pmf_norm, Prod.map_apply, id_eq]
      have hsum := eval_uniform_pi_map_sum k (G := ZMod q)
      have hmap := congrArg (PMF.map fun u₀ : ZMod q =>
        let y : Fin 2 → ZMod q := Fin.cases u₀ (fun _ => target - u₀)
        (fun i : I => otMul2BitsView i.1 (I.restrict x i) (fun _ => 0) (fun _ => 0), y)) hsum
      simp only [← PMF.bind_pure_comp, pmf_norm, ProbComp.eval_uniform] at hmap
      rw [← hmap]
      refine congrArg (fun f => (PMF.uniformOfFintype (Fin k → ZMod q)).bind f) (funext fun r => ?_)
      have hsum1 : otMul2Share1 (fun i => otMul2SenderPairs a r i (bits i)) =
          target - otMul2Share0 r :=
        eq_sub_of_add_eq' (otMul2_correct a bits r)
      refine congrArg PMF.pure (Prod.ext (funext fun ⟨i, hi⟩ => ?_) (funext fun i => ?_))
      · fin_cases i
        · exact (h0 hi).elim
        · exact (h1 hi).elim
      · fin_cases i
        · rfl
        · exact hsum1.symm

/-! #### Specialization to `ZMod q × ZMod q` via `zmodToBits` -/

/-- Input tuple type for `otMul2Protocol`: both parties hold values in `ZMod q`. -/
@[expose, reducible] def OTMultIn (q : ℕ) (_ : Fin 2) : Type :=
  ZMod q

/-- Ideal 2-party multiplication functionality over `ZMod q`: given `(a, b) : ZMod q × ZMod q`,
samples uniform additive shares of `a * b`. -/
@[expose] noncomputable def otMul2Functionality (q : ℕ) [NeZero q] :
    Functionality 2 (OTMultIn q) (fun _ => ZMod q) :=
  fun x => ProbComp.sampleAdditiveShares 2 (x 0 * x 1)

/-- Embed `OTMultIn q` into `OTMultBitsIn (otBitWidth q) q` by decomposing Party `1`'s input
with `zmodToBits`. -/
@[expose] def otMul2EmbedIn {q : ℕ} [NeZero q] (i : Fin 2) (xi : OTMultIn q i) :
    OTMultBitsIn (otBitWidth q) q i :=
  Fin.cases (motive := fun i => OTMultIn q i → OTMultBitsIn (otBitWidth q) q i)
    (fun a => a)
    (fun j => Fin.cases
      (motive := fun j => OTMultIn q j.succ → OTMultBitsIn (otBitWidth q) q j.succ)
      zmodToBits (fun l => l.elim0) j)
    i xi

/-- Precompose `otMul2BitsProtocol` state with `otMul2EmbedIn`. -/
@[expose] def otMul2EmbedState {q : ℕ} [NeZero q] (i : Fin 2)
    (st : OTMultIn q i × OTMultCoins (otBitWidth q) q i) :
    OTMultBitsIn (otBitWidth q) q i × OTMultCoins (otBitWidth q) q i :=
  (otMul2EmbedIn i st.1, st.2)

/-- Gilboa-style 2-party multiplication protocol over `ZMod q` in
`batchOTWorld (otBitWidth q) (ZMod q)`: Party `1` decomposes its input `b : ZMod q` via
`zmodToBits b` and executes `otMul2BitsProtocol`. -/
@[expose] noncomputable def otMul2Protocol (q : ℕ) [NeZero q] :
    Protocol 2 (batchOTSpec (otBitWidth q) (ZMod q)) (otMul2Schedule (otBitWidth q) q)
      (OTMultIn q) (OTMultCoins (otBitWidth q) q) (fun _ => ZMod q) where
  sampleCoins := (otMul2BitsProtocol (otBitWidth q) q).sampleCoins
  steps := (otMul2BitsProtocol (otBitWidth q) q).steps.mapState otMul2EmbedState

/-- Coalition simulator for `otMul2Protocol`. -/
@[expose] noncomputable def otMul2Sim (q : ℕ) [NeZero q] (I : Finset (Fin 2)) :
    CoalitionSimulator (otMul2Schedule (otBitWidth q) q) (OTMultIn q) (OTMultCoins (otBitWidth q) q)
      (fun _ => ZMod q) I :=
  fun xI yI => do
    let vI ← otMul2BitsSim (otBitWidth q) q I (fun i => otMul2EmbedIn i.1 (xI i)) yI
    return fun i => ⟨xI i, (vI i).coins, (vI i).received⟩

/-- **Perfect semi-honest security of `otMul2Protocol`:** for every `q > 1` (`0 < otBitWidth q`)
and every static coalition `I : Finset (Fin 2)`, `otMul2Protocol q` realizes `otMul2Functionality q`
in `batchOTWorld (otBitWidth q) (ZMod q)`. -/
theorem perfectSemiHonestPrivate_otMul2 (q : ℕ) [NeZero q] (hq : 1 < q) :
    PerfectSemiHonestPrivate (otMul2Protocol q)
      (batchOTWorld (otBitWidth q) (ZMod q)) (otMul2Functionality q) (otMul2Sim q) := by
  have : NeZero (otBitWidth q) := ⟨Nat.ne_of_gt (Nat.clog_pos one_lt_two hq)⟩
  intro I x
  let xBits : (i : Fin 2) → OTMultBitsIn (otBitWidth q) q i := fun i => otMul2EmbedIn i (x i)
  have hfunc : otMul2Functionality q x = otMul2BitsFunctionality (otBitWidth q) q xBits := by
    have h0 : xBits 0 = x 0 := rfl
    have h1 : xBits 1 = zmodToBits (x 1) := rfl
    simp [otMul2Functionality, otMul2BitsFunctionality, h0, h1, bitVecValue_zmodToBits]
  have hreal : (otMul2Protocol q).realJoint (batchOTWorld (otBitWidth q) (ZMod q)) I x =
      ((otMul2BitsProtocol (otBitWidth q) q).realJoint
        (batchOTWorld (otBitWidth q) (ZMod q)) I xBits).map
        (Prod.map (fun vI i => ⟨x i, (vI i).coins, (vI i).received⟩) id) := by
    simp only [Protocol.realJoint, Protocol.evalWith_eq, otMul2Protocol, Steps.evalWith_mapState,
      Protocol.outputOfView, Steps.outputAt_mapState, PMF.map_comp, PMF.map_bind]
    rfl
  have hpriv := perfectSemiHonestPrivate_otMul2Bits (otBitWidth q) q I xBits
  have hmap := congrArg (PMF.map (Prod.map
    (fun (vI : (i : I) → PartyView (OTMultBitsIn (otBitWidth q) q)
      (OTMultCoins (otBitWidth q) q) (otMul2Schedule (otBitWidth q) q) i.1) (i : I) =>
        (⟨x i.1, (vI i).coins, (vI i).received⟩ : PartyView (OTMultIn q)
          (OTMultCoins (otBitWidth q) q) (otMul2Schedule (otBitWidth q) q) i.1)) id)) hpriv
  rw [hreal, ← hmap]
  simp only [idealJoint, otMul2Sim, hfunc, pmf_norm]
  refine congrArg (fun f => (ProbComp.eval (otMul2BitsFunctionality (otBitWidth q) q xBits)).bind f)
    (funext fun y => ?_)
  refine congrArg
    (fun g => (ProbComp.eval
      (otMul2BitsSim (otBitWidth q) q I (I.restrict xBits) (I.restrict y))).bind g)
    (funext fun vI => ?_)
  rfl

/-! ### 5. Symmetric additive-share multiplication (`shareMulFromOT`) -/

/-- Role-reversal embedding `Fin 2 ↪ Fin 2` swapping Party `0` and Party `1`. -/
@[expose, reducible] def otRoleReversal : Fin 2 ↪ Fin 2 :=
  ⟨Fin.rev, Fin.rev_injective⟩

/-- Party `0`'s output share in symmetric 2-party additive-share multiplication from two
instances of `otMul2`: `a₀ * b₀ + ∑ r₀ + ∑ t₀`. -/
@[expose] def shareMulFromOTOut0 {q : ℕ} [NeZero q] (xy₀ : ZMod q × ZMod q)
    (r₀ t₀ : Fin (otBitWidth q) → ZMod q) : ZMod q :=
  xy₀.1 * xy₀.2 + otMul2Share0 r₀ + otMul2Share1 t₀

/-- Party `1`'s output share in symmetric 2-party additive-share multiplication from two
instances of `otMul2`: `a₁ * b₁ + ∑ r₁ + ∑ t₁`. -/
@[expose] def shareMulFromOTOut1 {q : ℕ} [NeZero q] (xy₁ : ZMod q × ZMod q)
    (r₁ t₁ : Fin (otBitWidth q) → ZMod q) : ZMod q :=
  xy₁.1 * xy₁.2 + otMul2Share0 r₁ + otMul2Share1 t₁

/-- **Algebraic correctness of `shareMulFromOT`:** for all input shares `(a₀, b₀)`, `(a₁, b₁)`
and all mask vectors `r₀, r₁ : Fin (otBitWidth q) → ZMod q`, the output shares `c₀, c₁` sum
identically to `(a₀ + a₁) * (b₀ + b₁)`. -/
theorem shareMulFromOT_correct {q : ℕ} [NeZero q] (xy₀ xy₁ : ZMod q × ZMod q)
    (r₀ r₁ : Fin (otBitWidth q) → ZMod q) :
    let t₁ := fun i => otMul2SenderPairs xy₀.1 r₀ i (zmodToBits xy₁.2 i)
    let t₀ := fun i => otMul2SenderPairs xy₁.1 r₁ i (zmodToBits xy₀.2 i)
    shareMulFromOTOut0 xy₀ r₀ t₀ + shareMulFromOTOut1 xy₁ r₁ t₁ =
      (xy₀.1 + xy₁.1) * (xy₀.2 + xy₁.2) := by
  intro t₁ t₀
  dsimp only [shareMulFromOTOut0, shareMulFromOTOut1]
  have h01 := otMul2ZMod_correct xy₀.1 xy₁.2 r₀
  have h10 := otMul2ZMod_correct xy₁.1 xy₀.2 r₁
  calc
    xy₀.1 * xy₀.2 + otMul2Share0 r₀ + otMul2Share1 t₀ +
        (xy₁.1 * xy₁.2 + otMul2Share0 r₁ + otMul2Share1 t₁)
      = xy₀.1 * xy₀.2 + (otMul2Share0 r₀ + otMul2Share1 t₁) +
          (otMul2Share0 r₁ + otMul2Share1 t₀) + xy₁.1 * xy₁.2 := by ring
    _ = xy₀.1 * xy₀.2 + xy₀.1 * xy₁.2 + xy₁.1 * xy₀.2 + xy₁.1 * xy₁.2 := by
          rw [h01, h10]
    _ = (xy₀.1 + xy₁.1) * (xy₀.2 + xy₁.2) := by ring

/-- Schedule for `shareMulFromOTProtocol`: two sequential invocations of `batchOTSpec` with
roles `(0, 1)` and `(1, 0)`. -/
@[expose, reducible] def shareMulFromOTSchedule (q : ℕ) :
    Schedule 2 (batchOTSpec (otBitWidth q) (ZMod q)) :=
  [.oracle () (Function.Embedding.refl (Fin 2)), .oracle () otRoleReversal]

/-- Local coins for `shareMulFromOTProtocol`: each party holds a mask vector in
`Fin (otBitWidth q) → ZMod q`. -/
@[expose, reducible] def ShareMulFromOTCoins (q : ℕ) (_ : Fin 2) : Type :=
  Fin (otBitWidth q) → ZMod q

/-- Round-0 oracle query for `shareMulFromOTProtocol` (`a₀ * b₁`). -/
@[expose] def shareMulFromOTQuery0 {q : ℕ} [NeZero q]
    (s : Fin ((batchOTSpec (otBitWidth q) (ZMod q)).arity ()))
    (st : (ZMod q × ZMod q) × ShareMulFromOTCoins q (Function.Embedding.refl (Fin 2) s)) :
    (batchOTSpec (otBitWidth q) (ZMod q)).Query () s :=
  Fin.cases
    (motive := fun s =>
      (ZMod q × ZMod q) × ShareMulFromOTCoins q (Function.Embedding.refl (Fin 2) s) →
        (batchOTSpec (otBitWidth q) (ZMod q)).Query () s)
    (fun ((a, _), r) => otMul2SenderPairs a r)
    (fun j => Fin.cases
      (motive := fun j =>
        (ZMod q × ZMod q) × ShareMulFromOTCoins q (Function.Embedding.refl (Fin 2) j.succ) →
          (batchOTSpec (otBitWidth q) (ZMod q)).Query () j.succ)
      (fun ((_, b), _) => zmodToBits b) (fun l => l.elim0) j)
    s st

/-- Round-1 oracle query for `shareMulFromOTProtocol` (`a₁ * b₀`). -/
@[expose] def shareMulFromOTQuery1 {q : ℕ} [NeZero q]
    (s : Fin ((batchOTSpec (otBitWidth q) (ZMod q)).arity ()))
    (st : ((ZMod q × ZMod q) × ShareMulFromOTCoins q (otRoleReversal s)) ×
      (Round.oracle (spec := batchOTSpec (otBitWidth q) (ZMod q)) ()
        (Function.Embedding.refl (Fin 2))).Received (otRoleReversal s)) :
    (batchOTSpec (otBitWidth q) (ZMod q)).Query () s :=
  Fin.cases
    (motive := fun s =>
      ((ZMod q × ZMod q) × ShareMulFromOTCoins q (otRoleReversal s)) ×
        (Round.oracle (spec := batchOTSpec (otBitWidth q) (ZMod q)) ()
          (Function.Embedding.refl (Fin 2))).Received (otRoleReversal s) →
        (batchOTSpec (otBitWidth q) (ZMod q)).Query () s)
    (fun (((a, _), r), _) => otMul2SenderPairs a r)
    (fun j => Fin.cases
      (motive := fun j =>
        ((ZMod q × ZMod q) × ShareMulFromOTCoins q (otRoleReversal j.succ)) ×
          (Round.oracle (spec := batchOTSpec (otBitWidth q) (ZMod q)) ()
            (Function.Embedding.refl (Fin 2))).Received (otRoleReversal j.succ) →
          (batchOTSpec (otBitWidth q) (ZMod q)).Query () j.succ)
      (fun (((_, b), _), _) => zmodToBits b) (fun l => l.elim0) j)
    s st

/-- Output extraction for `shareMulFromOTProtocol`. -/
@[expose] def shareMulFromOTOutput {q : ℕ} [NeZero q] (i : Fin 2)
    (st : (((ZMod q × ZMod q) × ShareMulFromOTCoins q i) ×
      (Round.oracle (spec := batchOTSpec (otBitWidth q) (ZMod q)) ()
        (Function.Embedding.refl (Fin 2))).Received i) ×
      (Round.oracle (spec := batchOTSpec (otBitWidth q) (ZMod q)) ()
        otRoleReversal).Received i) : ZMod q :=
  Fin.cases
    (motive := fun i =>
      (((ZMod q × ZMod q) × ShareMulFromOTCoins q i) ×
        (Round.oracle (spec := batchOTSpec (otBitWidth q) (ZMod q)) ()
          (Function.Embedding.refl (Fin 2))).Received i) ×
        (Round.oracle (spec := batchOTSpec (otBitWidth q) (ZMod q)) ()
          otRoleReversal).Received i → ZMod q)
    (fun (((xy, r), _), rec1) => shareMulFromOTOut0 xy r (rec1 1 rfl))
    (fun j => Fin.cases
      (motive := fun j =>
        (((ZMod q × ZMod q) × ShareMulFromOTCoins q j.succ) ×
          (Round.oracle (spec := batchOTSpec (otBitWidth q) (ZMod q)) ()
            (Function.Embedding.refl (Fin 2))).Received j.succ) ×
          (Round.oracle (spec := batchOTSpec (otBitWidth q) (ZMod q)) ()
            otRoleReversal).Received j.succ → ZMod q)
      (fun (((xy, r), rec0), _) => shareMulFromOTOut1 xy r (rec0 1 rfl))
      (fun l => l.elim0) j)
    i st

/-- Symmetric 2-party shared multiplication protocol over `ZMod q` in
`batchOTWorld (otBitWidth q) (ZMod q)`, realizing `sharedMulFunctionality 2`. -/
@[expose] noncomputable def shareMulFromOTProtocol (q : ℕ) [NeZero q] :
    Protocol 2 (batchOTSpec (otBitWidth q) (ZMod q)) (shareMulFromOTSchedule q)
      (fun _ => ZMod q × ZMod q) (ShareMulFromOTCoins q) (fun _ => ZMod q) where
  sampleCoins _ := ProbComp.uniform (Fin (otBitWidth q) → ZMod q)
  steps := .oracle shareMulFromOTQuery0 (.oracle shareMulFromOTQuery1 (.done shareMulFromOTOutput))

/-- Construct Party `i`'s `PartyView` in `shareMulFromOTProtocol` from its input `xyi`, its own
coins `r_i`, and its received OT answer vector `t_i`. -/
@[expose] def shareMulFromOTView {q : ℕ} [NeZero q] (i : Fin 2) (xyi : ZMod q × ZMod q)
    (ri ti : Fin (otBitWidth q) → ZMod q) :
    PartyView (fun _ => ZMod q × ZMod q) (ShareMulFromOTCoins q) (shareMulFromOTSchedule q) i where
  input := xyi
  coins := ri
  received :=
    (fun s hs =>
      Fin.cases (motive := fun s => s = i → (batchOTSpec (otBitWidth q) (ZMod q)).Answer () s)
        (fun _ => ())
        (fun j => Fin.cases
          (motive := fun j => j.succ = i → (batchOTSpec (otBitWidth q) (ZMod q)).Answer () j.succ)
          (fun _ => ti) (fun l => l.elim0) j)
        s hs,
     (fun s hs =>
      Fin.cases (motive := fun s => otRoleReversal s = i →
          (batchOTSpec (otBitWidth q) (ZMod q)).Answer () s)
        (fun _ => ())
        (fun j => Fin.cases
          (motive := fun j => otRoleReversal j.succ = i →
            (batchOTSpec (otBitWidth q) (ZMod q)).Answer () j.succ)
          (fun _ => ti) (fun l => l.elim0) j)
        s hs, ()))

/-- Coalition simulator for `shareMulFromOTProtocol` against every static coalition
`I : Finset (Fin 2)`. -/
@[expose] noncomputable def shareMulFromOTSim (q : ℕ) [NeZero q] (I : Finset (Fin 2)) :
    CoalitionSimulator (shareMulFromOTSchedule q) (fun _ => ZMod q × ZMod q)
      (ShareMulFromOTCoins q) (fun _ => ZMod q) I :=
  fun xI yI =>
    if h0 : (0 : Fin 2) ∈ I then
      if h1 : (1 : Fin 2) ∈ I then do
        let r₁ ← ProbComp.uniform (Fin (otBitWidth q) → ZMod q)
        let t₀ : Fin (otBitWidth q) → ZMod q :=
          fun i => otMul2SenderPairs (xI ⟨1, h1⟩).1 r₁ i (zmodToBits (xI ⟨0, h0⟩).2 i)
        let r₀ ← ProbComp.sampleAdditiveShares (otBitWidth q)
          (yI ⟨0, h0⟩ - (xI ⟨0, h0⟩).1 * (xI ⟨0, h0⟩).2 - otMul2Share1 t₀)
        let t₁ : Fin (otBitWidth q) → ZMod q :=
          fun i => otMul2SenderPairs (xI ⟨0, h0⟩).1 r₀ i (zmodToBits (xI ⟨1, h1⟩).2 i)
        return fun i =>
          Fin.cases
            (motive := fun j => (hj : j ∈ I) →
              PartyView (fun _ => ZMod q × ZMod q) (ShareMulFromOTCoins q)
                (shareMulFromOTSchedule q) j)
            (fun _ => shareMulFromOTView 0 (xI ⟨0, h0⟩) r₀ t₀)
            (fun j => Fin.cases
              (motive := fun j => (hj : j.succ ∈ I) →
                PartyView (fun _ => ZMod q × ZMod q) (ShareMulFromOTCoins q)
                  (shareMulFromOTSchedule q) j.succ)
              (fun _ => shareMulFromOTView 1 (xI ⟨1, h1⟩) r₁ t₁)
              (fun l => l.elim0) j)
            i.1 i.2
      else do
        let r₀ ← ProbComp.uniform (Fin (otBitWidth q) → ZMod q)
        let t₀ ← ProbComp.sampleAdditiveShares (otBitWidth q)
          (yI ⟨0, h0⟩ - (xI ⟨0, h0⟩).1 * (xI ⟨0, h0⟩).2 - otMul2Share0 r₀)
        return fun i => shareMulFromOTView i.1 (xI i) r₀ t₀
    else
      if h1 : (1 : Fin 2) ∈ I then do
        let r₁ ← ProbComp.uniform (Fin (otBitWidth q) → ZMod q)
        let t₁ ← ProbComp.sampleAdditiveShares (otBitWidth q)
          (yI ⟨1, h1⟩ - (xI ⟨1, h1⟩).1 * (xI ⟨1, h1⟩).2 - otMul2Share0 r₁)
        return fun i => shareMulFromOTView i.1 (xI i) r₁ t₁
      else
        pure fun i => shareMulFromOTView i.1 (xI i) (fun _ => 0) (fun _ => 0)

private theorem eval_pi_shareMulFromOTCoins (q : ℕ) [NeZero q] :
    ProbComp.eval (OracleComp.pi (shareMulFromOTProtocol q).sampleCoins) =
      (PMF.uniformOfFintype ((Fin (otBitWidth q) → ZMod q) × (Fin (otBitWidth q) → ZMod q))).map
        (fun p i => Fin.cases p.1 (fun _ => p.2) i) := by
  classical
  ext c
  rw [ProbComp.eval_pi, PMF.pi_apply, Fin.prod_univ_two, PMF.map_apply]
  have hc : c = (fun i : Fin 2 => Fin.cases (c 0) (fun _ => c 1) i) := by
    ext i
    fin_cases i <;> rfl
  have h0 : ProbComp.eval ((shareMulFromOTProtocol q).sampleCoins 0) (c 0) =
      PMF.uniformOfFintype (Fin (otBitWidth q) → ZMod q) (c 0) :=
    congrFun (congrArg DFunLike.coe
      (ProbComp.eval_uniform (α := Fin (otBitWidth q) → ZMod q))) (c 0)
  have h1 : ProbComp.eval ((shareMulFromOTProtocol q).sampleCoins 1) (c 1) =
      PMF.uniformOfFintype (Fin (otBitWidth q) → ZMod q) (c 1) :=
    congrFun (congrArg DFunLike.coe
      (ProbComp.eval_uniform (α := Fin (otBitWidth q) → ZMod q))) (c 1)
  rw [h0, h1]
  symm
  let p₀ : (Fin (otBitWidth q) → ZMod q) × (Fin (otBitWidth q) → ZMod q) := (c 0, c 1)
  rw [tsum_eq_single p₀]
  · simp only [p₀, ← hc, ↓reduceIte, PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
    have hcard0 : (Fintype.card (Fin (otBitWidth q) → ZMod q) : ℝ≥0∞) ≠ 0 := by
      simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, ne_eq, Nat.cast_eq_zero,
        pow_eq_zero_iff', NeZero.ne q, false_and, not_false_eq_true]
    rw [ENNReal.mul_inv (Or.inl hcard0) (Or.inr hcard0)]
  · intro p hp
    have hne : c ≠ (fun i : Fin 2 => Fin.cases p.1 (fun _ => p.2) i) := by
      intro h
      apply hp
      exact Prod.ext (congrFun h 0).symm (congrFun h 1).symm
    simp [hne]

private theorem evalWith_shareMulFromOTProtocol (q : ℕ) [NeZero q]
    (x : Fin 2 → ZMod q × ZMod q) :
    (shareMulFromOTProtocol q).evalWith (batchOTWorld (otBitWidth q) (ZMod q)) x =
      (PMF.uniformOfFintype
        ((Fin (otBitWidth q) → ZMod q) × (Fin (otBitWidth q) → ZMod q))).map fun p =>
        let t₁ : Fin (otBitWidth q) → ZMod q :=
          fun i => otMul2SenderPairs (x 0).1 p.1 i (zmodToBits (x 1).2 i)
        let t₀ : Fin (otBitWidth q) → ZMod q :=
          fun i => otMul2SenderPairs (x 1).1 p.2 i (zmodToBits (x 0).2 i)
        let views : (i : Fin 2) → PartyView (fun _ => ZMod q × ZMod q)
            (ShareMulFromOTCoins q) (shareMulFromOTSchedule q) i :=
          fun i => shareMulFromOTView i (x i)
            (Fin.cases p.1 (fun _ => p.2) i)
            (Fin.cases t₀ (fun _ => t₁) i)
        let y : Fin 2 → ZMod q :=
          Fin.cases (shareMulFromOTOut0 (x 0) p.1 t₀)
            (fun _ => shareMulFromOTOut1 (x 1) p.2 t₁)
        (views, y) := by
  rw [Protocol.evalWith_eq, eval_pi_shareMulFromOTCoins]
  simp only [pmf_norm, Protocol.outputOfView, shareMulFromOTProtocol, batchOTWorld,
    Steps.evalWith_oracle, Steps.evalWith_done, Steps.outputAt]
  refine congrArg (PMF.map · _) (funext fun p => ?_)
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · fin_cases i
    · refine PartyView.ext rfl rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
      · refine Round.received_oracle_ext fun s hs => ?_
        fin_cases s
        · rfl
        · simp at hs
      · refine Round.received_oracle_ext fun s hs => ?_
        fin_cases s
        · simp at hs
        · rfl
    · refine PartyView.ext rfl rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
      · refine Round.received_oracle_ext fun s hs => ?_
        fin_cases s
        · simp at hs
        · rfl
      · refine Round.received_oracle_ext fun s hs => ?_
        fin_cases s
        · rfl
        · simp at hs
  · fin_cases i <;> rfl

private theorem uniformOfFintype_prod_map {α β γ : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] (f : α × β → γ) :
    (PMF.uniformOfFintype (α × β)).map f =
      (PMF.uniformOfFintype α).bind (fun a =>
        (PMF.uniformOfFintype β).map (fun b => f (a, b))) := by
  rw [← PMF.uniformOfFintype_prod, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]

private theorem uniformOfFintype_bind_map_comm {α β γ : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] (f : α → β → γ) :
    (PMF.uniformOfFintype α).bind (fun a => (PMF.uniformOfFintype β).map (fun b => f a b)) =
      (PMF.uniformOfFintype β).bind (fun b => (PMF.uniformOfFintype α).map (fun a => f a b)) :=
  PMF.bind_comm _ _ _

/-- **Perfect semi-honest security of `shareMulFromOTProtocol`:** for every `q > 1`
(`0 < otBitWidth q`) and every static coalition `I : Finset (Fin 2)`,
`shareMulFromOTProtocol q` realizes `sharedMulFunctionality 2` in
`batchOTWorld (otBitWidth q) (ZMod q)`. -/
theorem perfectSemiHonestPrivate_shareMulFromOT (q : ℕ) [NeZero q] (hq : 1 < q) :
    PerfectSemiHonestPrivate (shareMulFromOTProtocol q)
      (batchOTWorld (otBitWidth q) (ZMod q)) (sharedMulFunctionality 2)
      (shareMulFromOTSim q) := by
  have : NeZero (otBitWidth q) := ⟨Nat.ne_of_gt (Nat.clog_pos one_lt_two hq)⟩
  intro I x
  let target : ZMod q := (∑ i : Fin 2, (x i).1) * (∑ i : Fin 2, (x i).2)
  have htarget : target = ((x 0).1 + (x 1).1) * ((x 0).2 + (x 1).2) := by
    simp [target, Fin.sum_univ_two]
  simp only [idealJoint, sharedMulFunctionality, eval_sampleAdditiveShares_two,
    Protocol.realJoint, evalWith_shareMulFromOTProtocol, pmf_norm]
  have hres0 : ∀ (h0 : (0 : Fin 2) ∈ I) {β : Type} (f : Fin 2 → β),
      I.restrict f ⟨0, h0⟩ = f 0 :=
    fun _ _ _ => rfl
  have hres1 : ∀ (h1 : (1 : Fin 2) ∈ I) {β : Type} (f : Fin 2 → β),
      I.restrict f ⟨1, h1⟩ = f 1 :=
    fun _ _ _ => rfl
  have hfc1 : ∀ (a b : ZMod q), Fin.cases a (fun _ => b) (1 : Fin 2) = b :=
    fun _ _ => rfl
  by_cases h0 : (0 : Fin 2) ∈ I
  · by_cases h1 : (1 : Fin 2) ∈ I
    · simp only [shareMulFromOTSim, h0, h1, ↓reduceDIte, pmf_norm, ProbComp.eval_uniform,
        hres0, hres1, Fin.cases_zero, Prod.map_apply, id_eq]
      conv_lhs => rw [PMF.bind_comm]
      conv_rhs => rw [uniformOfFintype_prod_map, uniformOfFintype_bind_map_comm]; dsimp only
      symm
      refine congrArg (PMF.bind (PMF.uniformOfFintype (Fin (otBitWidth q) → ZMod q)))
        (funext fun r₁ => ?_)
      let t₀ : Fin (otBitWidth q) → ZMod q :=
        fun i => otMul2SenderPairs (x 1).1 r₁ i (zmodToBits (x 0).2 i)
      let shift₀ : ZMod q := (x 0).1 * (x 0).2 + otMul2Share1 t₀
      have hr₀ := eval_uniform_pi_sum_eq_bind_sampleAdditiveShares (otBitWidth q) (G := ZMod q)
      have hmap := congrArg (PMF.map fun p : (Fin (otBitWidth q) → ZMod q) × ZMod q =>
        let c₀ := shift₀ + p.2
        let t₁ : Fin (otBitWidth q) → ZMod q :=
          fun i => otMul2SenderPairs (x 0).1 p.1 i (zmodToBits (x 1).2 i)
        let views : (i : I) → PartyView (fun _ => ZMod q × ZMod q)
            (ShareMulFromOTCoins q) (shareMulFromOTSchedule q) i.1 :=
          fun i =>
            Fin.cases
              (motive := fun j => (hj : j ∈ I) →
                PartyView (fun _ => ZMod q × ZMod q) (ShareMulFromOTCoins q)
                  (shareMulFromOTSchedule q) j)
              (fun _ => shareMulFromOTView 0 (x 0) p.1 t₀)
              (fun j => Fin.cases
                (motive := fun j => (hj : j.succ ∈ I) →
                  PartyView (fun _ => ZMod q × ZMod q) (ShareMulFromOTCoins q)
                    (shareMulFromOTSchedule q) j.succ)
                (fun _ => shareMulFromOTView 1 (x 1) r₁ t₁)
                (fun l => l.elim0) j)
              i.1 i.2
        let y : Fin 2 → ZMod q := Fin.cases c₀ (fun _ => target - c₀)
        (views, y)) hr₀
      simp only [PMF.map_comp, Function.comp_def, PMF.map_bind, ProbComp.eval_uniform] at hmap
      have hshift : (PMF.uniformOfFintype (ZMod q)).map (fun c₀ => c₀ - shift₀) =
          PMF.uniformOfFintype (ZMod q) :=
        PMF.uniformOfFintype_map_equiv (Equiv.subRight shift₀)
      rw [← hshift, PMF.bind_map] at hmap
      simp only [Function.comp_def] at hmap
      have hsub : ∀ c₀ : ZMod q,
          c₀ - shift₀ = c₀ - (x 0).1 * (x 0).2 - otMul2Share1 t₀ := by
        intro c₀
        dsimp [shift₀]
        ring
      have hsub' : ∀ c₀ : ZMod q, shift₀ + (c₀ - shift₀) = c₀ :=
        fun c₀ => add_sub_cancel shift₀ c₀
      simp only [hsub'] at hmap
      simp only [hsub, ← PMF.bind_pure_comp, pmf_norm] at hmap
      dsimp only [target] at hmap
      rw [← hmap]
      refine congrArg (fun f => (PMF.uniformOfFintype (Fin (otBitWidth q) → ZMod q)).bind f)
        (funext fun r₀ => ?_)
      dsimp only [shift₀, shareMulFromOTOut0]
      have hc₀ : shareMulFromOTOut0 (x 0) r₀ t₀ =
          (x 0).1 * (x 0).2 + otMul2Share1 t₀ + otMul2Share0 r₀ := by
        dsimp [shareMulFromOTOut0]
        ring
      have hcorr := shareMulFromOT_correct (x 0) (x 1) r₀ r₁
      dsimp only at hcorr
      have hc₁ : shareMulFromOTOut1 (x 1) r₁
          (fun i => otMul2SenderPairs (x 0).1 r₀ i (zmodToBits (x 1).2 i)) =
          target - shareMulFromOTOut0 (x 0) r₀ t₀ := by
        rw [htarget]
        exact eq_sub_of_add_eq' hcorr
      refine congrArg PMF.pure (Prod.ext (funext fun ⟨i, hi⟩ => ?_) (funext fun i => ?_))
      · fin_cases i <;> rfl
      · fin_cases i
        · exact hc₀
        · dsimp only
          simp only [Fin.mk_one, hfc1]
          rw [hc₁, hc₀]
          dsimp only [target, otMul2Share0]
    · simp only [shareMulFromOTSim, h0, h1, ↓reduceDIte, pmf_norm, ProbComp.eval_uniform,
        hres0, Fin.cases_zero, Prod.map_apply, id_eq]
      conv_lhs => rw [PMF.bind_comm]
      conv_rhs => rw [uniformOfFintype_prod_map]; dsimp only
      symm
      refine congrArg (PMF.bind (PMF.uniformOfFintype (Fin (otBitWidth q) → ZMod q)))
        (funext fun r₀ => ?_)
      let shift₀ : ZMod q := (x 0).1 * (x 0).2 + otMul2Share0 r₀
      have ht₀ := eval_uniform_pi_sum_eq_bind_sampleAdditiveShares (otBitWidth q) (G := ZMod q)
      have hmap := congrArg (PMF.map fun p : (Fin (otBitWidth q) → ZMod q) × ZMod q =>
        let c₀ := shift₀ + p.2
        let y : Fin 2 → ZMod q := Fin.cases c₀ (fun _ => target - c₀)
        (fun i : I => shareMulFromOTView i.1 (I.restrict x i) r₀ p.1, y)) ht₀
      simp only [PMF.map_comp, Function.comp_def, PMF.map_bind, ProbComp.eval_uniform] at hmap
      have hshift : (PMF.uniformOfFintype (ZMod q)).map (fun c₀ => c₀ - shift₀) =
          PMF.uniformOfFintype (ZMod q) :=
        PMF.uniformOfFintype_map_equiv (Equiv.subRight shift₀)
      rw [← hshift, PMF.bind_map] at hmap
      simp only [Function.comp_def] at hmap
      have hsub : ∀ c₀ : ZMod q,
          c₀ - shift₀ = c₀ - (x 0).1 * (x 0).2 - otMul2Share0 r₀ := by
        intro c₀
        dsimp [shift₀]
        ring
      have hsub' : ∀ c₀ : ZMod q, shift₀ + (c₀ - shift₀) = c₀ :=
        fun c₀ => add_sub_cancel shift₀ c₀
      simp only [hsub'] at hmap
      simp only [hsub, ← PMF.bind_pure_comp, pmf_norm] at hmap
      dsimp only [target] at hmap
      rw [← hmap]
      conv_rhs =>
        rw [← PMF.uniformOfFintype_map_equiv (otMul2MaskEquiv (x 1).1 (zmodToBits (x 0).2))]
      simp only [← PMF.bind_pure_comp, pmf_norm]
      refine congrArg (fun f => (PMF.uniformOfFintype (Fin (otBitWidth q) → ZMod q)).bind f)
        (funext fun t₀ => ?_)
      dsimp only [otMul2MaskEquiv, Equiv.coe_fn_mk, shift₀]
      have hcorr := shareMulFromOT_correct (x 0) (x 1) r₀ t₀
      dsimp only at hcorr
      have hc₁ : shareMulFromOTOut1 (x 1) t₀
          (fun i => otMul2SenderPairs (x 0).1 r₀ i (zmodToBits (x 1).2 i)) =
          target - shareMulFromOTOut0 (x 0) r₀
            (fun i => otMul2SenderPairs (x 1).1 t₀ i (zmodToBits (x 0).2 i)) := by
        rw [htarget]
        exact eq_sub_of_add_eq' hcorr
      dsimp only [target, shareMulFromOTOut0, otMul2Share1] at hc₁
      refine congrArg PMF.pure (Prod.ext (funext fun ⟨i, hi⟩ => ?_) (funext fun i => ?_))
      · fin_cases i
        · rfl
        · exact (h1 hi).elim
      · fin_cases i
        · rfl
        · exact hc₁
  · by_cases h1 : (1 : Fin 2) ∈ I
    · simp only [shareMulFromOTSim, h0, h1, ↓reduceDIte, pmf_norm, ProbComp.eval_uniform,
        hres1, hfc1, Prod.map_apply, id_eq]
      conv_lhs => rw [PMF.bind_comm]
      conv_rhs => rw [uniformOfFintype_prod_map, uniformOfFintype_bind_map_comm]; dsimp only
      symm
      refine congrArg (PMF.bind (PMF.uniformOfFintype (Fin (otBitWidth q) → ZMod q)))
        (funext fun r₁ => ?_)
      let shift₁ : ZMod q := (x 1).1 * (x 1).2 + otMul2Share0 r₁
      have ht₁ := eval_uniform_pi_sum_eq_bind_sampleAdditiveShares (otBitWidth q) (G := ZMod q)
      have hmap := congrArg (PMF.map fun p : (Fin (otBitWidth q) → ZMod q) × ZMod q =>
        let c₁ := shift₁ + p.2
        let y : Fin 2 → ZMod q := Fin.cases (target - c₁) (fun _ => c₁)
        (fun i : I => shareMulFromOTView i.1 (I.restrict x i) r₁ p.1, y)) ht₁
      simp only [PMF.map_comp, Function.comp_def, PMF.map_bind, ProbComp.eval_uniform] at hmap
      have hshift : (PMF.uniformOfFintype (ZMod q)).map (fun u => shift₁ + u) =
          PMF.uniformOfFintype (ZMod q) :=
        PMF.uniformOfFintype_map_equiv (Equiv.addLeft shift₁)
      have hsub0 : (PMF.uniformOfFintype (ZMod q)).map (fun u => target - (shift₁ + u)) =
          PMF.uniformOfFintype (ZMod q) := by
        have hcomp : (PMF.uniformOfFintype (ZMod q)).map (fun u => target - (shift₁ + u)) =
            ((PMF.uniformOfFintype (ZMod q)).map (fun u => shift₁ + u)).map
              (fun v => target - v) := by
          rw [PMF.map_comp]
          rfl
        rw [hcomp, hshift]
        exact PMF.uniformOfFintype_map_equiv (Equiv.subLeft target)
      rw [← hsub0, PMF.bind_map] at hmap
      simp only [Function.comp_def] at hmap
      dsimp only [target] at hmap
      have hrhs2 : ∀ c₀ : ZMod q,
          shift₁ + ((∑ i : Fin 2, (x i).1) * (∑ i : Fin 2, (x i).2) - (shift₁ + c₀)) =
            (∑ i : Fin 2, (x i).1) * (∑ i : Fin 2, (x i).2) - c₀ := fun c₀ => by ring
      have hrhs3 : ∀ c₀ : ZMod q,
          (∑ i : Fin 2, (x i).1) * (∑ i : Fin 2, (x i).2) - (shift₁ + c₀) =
            (∑ i : Fin 2, (x i).1) * (∑ i : Fin 2, (x i).2) - c₀ - (x 1).1 * (x 1).2 -
              otMul2Share0 r₁ := fun c₀ => by
        dsimp [shift₁]
        ring
      simp only [hrhs2] at hmap
      simp only [hrhs3, sub_sub_cancel, ← PMF.bind_pure_comp, pmf_norm] at hmap
      rw [← hmap]
      conv_rhs =>
        rw [← PMF.uniformOfFintype_map_equiv (otMul2MaskEquiv (x 0).1 (zmodToBits (x 1).2))]
      simp only [← PMF.bind_pure_comp, pmf_norm]
      refine congrArg (fun f => (PMF.uniformOfFintype (Fin (otBitWidth q) → ZMod q)).bind f)
        (funext fun t₁ => ?_)
      dsimp only [otMul2MaskEquiv, Equiv.coe_fn_mk, shift₁]
      have hcorr := shareMulFromOT_correct (x 0) (x 1) t₁ r₁
      dsimp only at hcorr
      have hc₀ : shareMulFromOTOut0 (x 0) t₁
          (fun i => otMul2SenderPairs (x 1).1 r₁ i (zmodToBits (x 0).2 i)) =
          target - shareMulFromOTOut1 (x 1) r₁
            (fun i => otMul2SenderPairs (x 0).1 t₁ i (zmodToBits (x 1).2 i)) := by
        rw [htarget]
        exact eq_sub_of_add_eq hcorr
      dsimp only [target, shareMulFromOTOut1] at hc₀
      refine congrArg PMF.pure (Prod.ext (funext fun ⟨i, hi⟩ => ?_) (funext fun i => ?_))
      · fin_cases i
        · exact (h0 hi).elim
        · rfl
      · fin_cases i
        · dsimp only
          simp only [Fin.zero_eta, Fin.cases_zero]
          rw [hc₀]
          dsimp only [otMul2Share1]
          ring
        · rfl
    · simp only [shareMulFromOTSim, h0, h1, ↓reduceDIte, pmf_norm, Prod.map_apply, id_eq]
      have hbind :
          (PMF.uniformOfFintype (Fin (otBitWidth q) → ZMod q)).bind (fun r₁ =>
            (PMF.uniformOfFintype (Fin (otBitWidth q) → ZMod q)).map fun r₀ =>
              (I.restrict fun i => shareMulFromOTView i (x i)
                (Fin.cases r₀ (fun _ => r₁) i)
                (Fin.cases (fun i => otMul2SenderPairs (x 1).1 r₁ i (zmodToBits (x 0).2 i))
                  (fun _ i => otMul2SenderPairs (x 0).1 r₀ i (zmodToBits (x 1).2 i)) i),
                fun i => @Fin.cases 1 (fun _ => ZMod q)
                  (shareMulFromOTOut0 (x 0) r₀
                    (fun i => otMul2SenderPairs (x 1).1 r₁ i (zmodToBits (x 0).2 i)))
                  (fun _ => shareMulFromOTOut1 (x 1) r₁
                    (fun i => otMul2SenderPairs (x 0).1 r₀ i (zmodToBits (x 1).2 i))) i)) =
          (PMF.uniformOfFintype (Fin (otBitWidth q) → ZMod q)).bind (fun _ =>
            (PMF.uniformOfFintype (ZMod q)).map fun c₀ =>
              (fun i : I => shareMulFromOTView i.1 (I.restrict x i) (fun _ => 0) (fun _ => 0),
                fun i => @Fin.cases 1 (fun _ => ZMod q) c₀ (fun _ => target - c₀) i)) := by
        refine congrArg (PMF.bind (PMF.uniformOfFintype (Fin (otBitWidth q) → ZMod q)))
          (funext fun r₁ => ?_)
        let t₀ : Fin (otBitWidth q) → ZMod q :=
          fun i => otMul2SenderPairs (x 1).1 r₁ i (zmodToBits (x 0).2 i)
        let shift₀ : ZMod q := (x 0).1 * (x 0).2 + otMul2Share1 t₀
        have hsum := eval_uniform_pi_map_sum (otBitWidth q) (G := ZMod q)
        have hmap := congrArg (PMF.map fun u₀ : ZMod q =>
          let c₀ := shift₀ + u₀
          let y : Fin 2 → ZMod q := Fin.cases c₀ (fun _ => target - c₀)
          (fun i : I => shareMulFromOTView i.1 (I.restrict x i) (fun _ => 0) (fun _ => 0), y)) hsum
        simp only [PMF.map_comp, Function.comp_def, ProbComp.eval_uniform] at hmap
        dsimp only [target] at hmap
        have hshift : (PMF.uniformOfFintype (ZMod q)).map (fun u₀ => shift₀ + u₀) =
            PMF.uniformOfFintype (ZMod q) :=
          PMF.uniformOfFintype_map_equiv (Equiv.addLeft shift₀)
        have hcomp :
            (PMF.uniformOfFintype (ZMod q)).map (fun u₀ : ZMod q =>
              (fun i : I => shareMulFromOTView i.1 (I.restrict x i) (fun _ => 0) (fun _ => 0),
                fun i => @Fin.cases 1 (fun _ => ZMod q) (shift₀ + u₀)
                  (fun _ => (∑ i : Fin 2, (x i).1) * (∑ i : Fin 2, (x i).2) -
                    (shift₀ + u₀)) i)) =
              (PMF.uniformOfFintype (ZMod q)).map fun c₀ =>
                (fun i : I => shareMulFromOTView i.1 (I.restrict x i) (fun _ => 0) (fun _ => 0),
                  fun i => @Fin.cases 1 (fun _ => ZMod q) c₀
                    (fun _ => (∑ i : Fin 2, (x i).1) * (∑ i : Fin 2, (x i).2) - c₀) i) := by
          conv_rhs => rw [← hshift, PMF.map_comp]
          rfl
        rw [hcomp] at hmap
        dsimp only [target]
        rw [← hmap]
        refine congrArg (PMF.map · (PMF.uniformOfFintype (Fin (otBitWidth q) → ZMod q)))
          (funext fun r₀ => ?_)
        dsimp only [shift₀]
        have hc₀ : shareMulFromOTOut0 (x 0) r₀ t₀ =
            (x 0).1 * (x 0).2 + otMul2Share1 t₀ + otMul2Share0 r₀ := by
          dsimp [shareMulFromOTOut0]
          ring
        have hcorr := shareMulFromOT_correct (x 0) (x 1) r₀ r₁
        dsimp only at hcorr
        have hc₁ : shareMulFromOTOut1 (x 1) r₁
            (fun i => otMul2SenderPairs (x 0).1 r₀ i (zmodToBits (x 1).2 i)) =
            target - shareMulFromOTOut0 (x 0) r₀ t₀ := by
          rw [htarget]
          exact eq_sub_of_add_eq' hcorr
        dsimp only [target] at hc₁
        refine Prod.ext (funext fun ⟨i, hi⟩ => ?_) (funext fun i => ?_)
        · fin_cases i
          · exact (h0 hi).elim
          · exact (h1 hi).elim
        · fin_cases i
          · exact hc₀
          · rw [hc₁, hc₀]
            dsimp only [otMul2Share0]
      conv_rhs =>
        rw [uniformOfFintype_prod_map, uniformOfFintype_bind_map_comm]
        dsimp only
        rw [hbind, PMF.bind_const]
      dsimp only [target]
      rw [← PMF.bind_pure_comp]
      rfl

/-! ### 6. Beaver multiplication triple generation (`tripleFromOTMul`) -/

/-- Construct a pair of `Beaver.TripleShare (ZMod q)` shares from local random mask pairs
`ab₀, ab₁ : ZMod q × ZMod q` and OT mask vectors `r₀, r₁ : Fin (otBitWidth q) → ZMod q`. -/
@[expose] def tripleSharesOfOTMul {q : ℕ} [NeZero q] (ab₀ ab₁ : ZMod q × ZMod q)
    (r₀ r₁ : Fin (otBitWidth q) → ZMod q) : Fin 2 → Beaver.TripleShare (ZMod q) :=
  let t₁ := fun i => otMul2SenderPairs ab₀.1 r₀ i (zmodToBits ab₁.2 i)
  let t₀ := fun i => otMul2SenderPairs ab₁.1 r₁ i (zmodToBits ab₀.2 i)
  Fin.cases
    ⟨ab₀.1, ab₀.2, shareMulFromOTOut0 ab₀ r₀ t₀⟩
    (fun _ => ⟨ab₁.1, ab₁.2, shareMulFromOTOut1 ab₁ r₁ t₁⟩)

/-- **Beaver triple correctness:** for all mask shares `ab₀, ab₁` and OT mask vectors `r₀, r₁`,
`tripleSharesOfOTMul ab₀ ab₁ r₀ r₁` satisfies
`(t 0).c + (t 1).c = ((t 0).a + (t 1).a) * ((t 0).b + (t 1).b)`. -/
theorem tripleSharesOfOTMul_correct {q : ℕ} [NeZero q] (ab₀ ab₁ : ZMod q × ZMod q)
    (r₀ r₁ : Fin (otBitWidth q) → ZMod q) :
    let t := tripleSharesOfOTMul ab₀ ab₁ r₀ r₁
    (t 0).c + (t 1).c = ((t 0).a + (t 1).a) * ((t 0).b + (t 1).b) :=
  shareMulFromOT_correct ab₀ ab₁ r₀ r₁

/-- Local coins for `tripleFromOTMulProtocol`: each party samples its own additive triple
mask shares `(a_i, b_i) : ZMod q × ZMod q` and OT mask vector
`r_i : Fin (otBitWidth q) → ZMod q`. -/
@[expose, reducible] def TripleFromOTMulCoins (q : ℕ) (_ : Fin 2) : Type :=
  (ZMod q × ZMod q) × (Fin (otBitWidth q) → ZMod q)

/-- Extract the input `(a_i, b_i)` and OT coins `r_i` from `TripleFromOTMulCoins q i`. -/
@[expose] def tripleFromOTMulState {q : ℕ} (i : Fin 2)
    (st : Unit × TripleFromOTMulCoins q i) :
    (ZMod q × ZMod q) × ShareMulFromOTCoins q i :=
  st.2

private noncomputable def twoPartyBeaverTripleFunctionality (q : ℕ) [NeZero q] :
    Functionality 2 (fun _ => Unit) (fun _ => Beaver.TripleShare (ZMod q)) :=
  fun _ => do
    let ab ← ProbComp.uniform (Fin 2 → ZMod q × ZMod q)
    let c ← sharedMulFunctionality 2 ab
    return fun i => ⟨(ab i).1, (ab i).2, c i⟩

private theorem eval_beaverTripleFunctionality_two_eq (q : ℕ) [NeZero q] (u : Fin 2 → Unit) :
    ProbComp.eval (Beaver.beaverTripleFunctionality q 2 u) =
      ProbComp.eval (twoPartyBeaverTripleFunctionality q u) := by
  classical
  let e : ((Fin 2 → ZMod q) × (Fin 2 → ZMod q)) ≃ (Fin 2 → ZMod q × ZMod q) :=
    { toFun := fun ⟨a, b⟩ i => (a i, b i)
      invFun := fun ab => (fun i => (ab i).1, fun i => (ab i).2)
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun _ => rfl }
  simp only [Beaver.beaverTripleFunctionality, twoPartyBeaverTripleFunctionality,
    sharedMulFunctionality, pmf_norm, ProbComp.eval_uniform]
  rw [← PMF.uniformOfFintype_map_equiv e, ← PMF.uniformOfFintype_prod]
  simp only [pmf_norm, e]
  rfl

/-- 2-party Beaver multiplication triple generation protocol over `ZMod q` in
`batchOTWorld (otBitWidth q) (ZMod q)`: each party samples uniform `(a_i, b_i)` and OT mask
vector `r_i`, runs `shareMulFromOTProtocol q` to obtain `c_i`, and outputs `⟨a_i, b_i, c_i⟩`. -/
@[expose] noncomputable def tripleFromOTMulProtocol (q : ℕ) [NeZero q] :
    Protocol 2 (batchOTSpec (otBitWidth q) (ZMod q)) (shareMulFromOTSchedule q)
      (fun _ => Unit) (TripleFromOTMulCoins q) (fun _ => Beaver.TripleShare (ZMod q)) where
  sampleCoins _ := ProbComp.uniform ((ZMod q × ZMod q) × (Fin (otBitWidth q) → ZMod q))
  steps :=
    .oracle
      (fun s st => shareMulFromOTQuery0 s (tripleFromOTMulState _ st))
      (.oracle
        (fun s st => shareMulFromOTQuery1 s ((tripleFromOTMulState _ st.1, st.2)))
        (.done fun i (((_, (ab, r)), rec0), rec1) =>
          let c := shareMulFromOTOutput i (((ab, r), rec0), rec1)
          ⟨ab.1, ab.2, c⟩))

/-- Coalition simulator for `tripleFromOTMulProtocol` against every static coalition
`I : Finset (Fin 2)`. -/
@[expose] noncomputable def tripleFromOTMulSim (q : ℕ) [NeZero q] (I : Finset (Fin 2)) :
    CoalitionSimulator (shareMulFromOTSchedule q) (fun _ => Unit) (TripleFromOTMulCoins q)
      (fun _ => Beaver.TripleShare (ZMod q)) I :=
  fun _ tI =>
    let xI : (i : I) → ZMod q × ZMod q := fun i => ((tI i).a, (tI i).b)
    let yI : (i : I) → ZMod q := fun i => (tI i).c
    (shareMulFromOTSim q I xI yI).map fun vI i =>
      ⟨(), (xI i, (vI i).coins), (vI i).received⟩

private theorem evalWith_tripleFromOTMulProtocol (q : ℕ) [NeZero q] :
    (tripleFromOTMulProtocol q).evalWith (batchOTWorld (otBitWidth q) (ZMod q)) (fun _ => ()) =
      (PMF.uniformOfFintype (Fin 2 → ZMod q × ZMod q)).bind fun ab =>
        ((shareMulFromOTProtocol q).evalWith (batchOTWorld (otBitWidth q) (ZMod q)) ab).map
          fun res =>
            (fun i => ⟨(), (ab i, (res.1 i).coins), (res.1 i).received⟩,
             fun i => ⟨(ab i).1, (ab i).2, res.2 i⟩) := by
  classical
  let eCoins :
      (Fin 2 → (ZMod q × ZMod q) × (Fin (otBitWidth q) → ZMod q)) ≃
        ((Fin 2 → ZMod q × ZMod q) × ((i : Fin 2) → ShareMulFromOTCoins q i)) :=
    { toFun := fun c => (fun i => (c i).1, fun i => (c i).2)
      invFun := fun p i => (p.1 i, p.2 i)
      left_inv := fun c => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  have hcoins :
      ProbComp.eval (OracleComp.pi (tripleFromOTMulProtocol q).sampleCoins) =
        (PMF.uniformOfFintype (Fin 2 → ZMod q × ZMod q)).bind fun ab =>
          (ProbComp.eval (OracleComp.pi (shareMulFromOTProtocol q).sampleCoins)).map
            fun r i => (ab i, r i) := by
    have h1 : ProbComp.eval (OracleComp.pi (tripleFromOTMulProtocol q).sampleCoins) =
        PMF.uniformOfFintype (Fin 2 → (ZMod q × ZMod q) × (Fin (otBitWidth q) → ZMod q)) := by
      simp only [tripleFromOTMulProtocol, ProbComp.eval_pi, ProbComp.eval_uniform,
        PMF.pi_uniformOfFintype]
    have h2 : ProbComp.eval (OracleComp.pi (shareMulFromOTProtocol q).sampleCoins) =
        PMF.uniformOfFintype ((i : Fin 2) → ShareMulFromOTCoins q i) := by
      simp only [shareMulFromOTProtocol, ProbComp.eval_pi, ProbComp.eval_uniform]
      ext r
      rw [PMF.pi_apply, Fin.prod_univ_two]
      simp only [PMF.uniformOfFintype_apply]
      conv_rhs => rw [Fintype.card_pi, Fin.prod_univ_two]
      have hcard0 : (Fintype.card (ShareMulFromOTCoins q 0) : ℝ≥0∞) ≠ 0 := by
        simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, ne_eq, Nat.cast_eq_zero,
          pow_eq_zero_iff', NeZero.ne q, false_and, not_false_eq_true]
      have hcard1 : (Fintype.card (ShareMulFromOTCoins q 1) : ℝ≥0∞) ≠ 0 := by
        simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, ne_eq, Nat.cast_eq_zero,
          pow_eq_zero_iff', NeZero.ne q, false_and, not_false_eq_true]
      rw [Nat.cast_mul, ENNReal.mul_inv (Or.inl hcard0) (Or.inr hcard1)]
    rw [h1, h2, ← PMF.uniformOfFintype_map_equiv eCoins.symm, ← PMF.uniformOfFintype_prod,
      PMF.map_bind]
    simp only [PMF.map_comp]
    rfl
  rw [Protocol.evalWith_eq, hcoins]
  simp only [pmf_norm, Protocol.outputOfView, Protocol.evalWith_eq, tripleFromOTMulProtocol,
    shareMulFromOTProtocol, tripleFromOTMulState, Steps.evalWith_oracle, Steps.evalWith_done,
    Steps.outputAt]

/-- Every supported execution of `tripleFromOTMulProtocol q` outputs valid
`Beaver.TripleShare (ZMod q)` shares in the support of `Beaver.beaverTripleFunctionality q 2`. -/
theorem mem_support_tripleFromOTMulProtocol (q : ℕ) [NeZero q]
    {res : ((i : Fin 2) → PartyView (fun _ => Unit) (TripleFromOTMulCoins q)
      (shareMulFromOTSchedule q) i) × (Fin 2 → Beaver.TripleShare (ZMod q))}
    (hres : res ∈ ((tripleFromOTMulProtocol q).evalWith
      (batchOTWorld (otBitWidth q) (ZMod q)) (fun _ => ())).support) :
    res.2 ∈ (ProbComp.eval (Beaver.beaverTripleFunctionality q 2 (fun _ => ()))).support := by
  rw [evalWith_tripleFromOTMulProtocol, PMF.mem_support_bind_iff] at hres
  obtain ⟨ab, _, hres⟩ := hres
  rw [PMF.mem_support_map_iff] at hres
  obtain ⟨inner, hinner, rfl⟩ := hres
  rw [Beaver.mem_support_beaverTripleFunctionality_iff, Fin.sum_univ_two, Fin.sum_univ_two,
    Fin.sum_univ_two]
  rw [evalWith_shareMulFromOTProtocol, PMF.mem_support_map_iff] at hinner
  obtain ⟨p, _, rfl⟩ := hinner
  exact shareMulFromOT_correct (ab 0) (ab 1) p.1 p.2

/-- **Perfect semi-honest security of `tripleFromOTMulProtocol`:** for every `q > 1`
(`0 < otBitWidth q`) and every static coalition `I : Finset (Fin 2)`,
`tripleFromOTMulProtocol q` realizes `Beaver.beaverTripleFunctionality q 2` in
`batchOTWorld (otBitWidth q) (ZMod q)`. -/
theorem perfectSemiHonestPrivate_tripleFromOTMul (q : ℕ) [NeZero q] (hq : 1 < q) :
    PerfectSemiHonestPrivate (tripleFromOTMulProtocol q)
      (batchOTWorld (otBitWidth q) (ZMod q)) (Beaver.beaverTripleFunctionality q 2)
      (tripleFromOTMulSim q) := by
  intro I _
  have hideal :
      ProbComp.eval (idealJoint (Beaver.beaverTripleFunctionality q 2) I
        (tripleFromOTMulSim q I) (fun _ => ())) =
      ProbComp.eval (idealJoint (twoPartyBeaverTripleFunctionality q) I
        (tripleFromOTMulSim q I) (fun _ => ())) := by
    simp only [idealJoint, ProbComp.eval_bind, eval_beaverTripleFunctionality_two_eq]
  rw [hideal]
  simp only [idealJoint, twoPartyBeaverTripleFunctionality, Protocol.realJoint, pmf_norm,
    ProbComp.eval_uniform]
  rw [evalWith_tripleFromOTMulProtocol, PMF.map_bind]
  refine congrArg (PMF.bind (PMF.uniformOfFintype (Fin 2 → ZMod q × ZMod q))) (funext fun ab => ?_)
  have hpriv := perfectSemiHonestPrivate_shareMulFromOT q hq I ab
  simp only [idealJoint, Protocol.realJoint, pmf_norm] at hpriv
  have hmap := congrArg (PMF.map fun p :
      ((i : I) → PartyView (fun _ => ZMod q × ZMod q) (ShareMulFromOTCoins q)
        (shareMulFromOTSchedule q) i.1) × (Fin 2 → ZMod q) =>
      ((fun i : I => (⟨(), ((ab i.1, (p.1 i).coins)), (p.1 i).received⟩ :
          PartyView (fun _ => Unit) (TripleFromOTMulCoins q)
            (shareMulFromOTSchedule q) i.1)),
       fun i : Fin 2 => (⟨(ab i).1, (ab i).2, p.2 i⟩ : Beaver.TripleShare (ZMod q)))) hpriv
  simp only [pmf_norm] at hmap
  simpa only [tripleFromOTMulSim, ProbComp.eval, OracleComp.evalWith_freeMMap,
    Finset.restrict_def, Prod.map, id_eq, pmf_norm] using hmap

/-- For every proper coalition `I ≠ Finset.univ` (`q > 1`), the marginal distribution of `I`'s
generated `Beaver.TripleShare (ZMod q)` shares in `tripleFromOTMulProtocol q` is uniform on
`(i : I) → Beaver.TripleShare (ZMod q)`. -/
theorem eval_restrict_output_tripleFromOTMul (q : ℕ) [NeZero q] (hq : 1 < q)
    (I : Finset (Fin 2)) (hI : I ≠ Finset.univ) :
    ((tripleFromOTMulProtocol q).evalWith
      (batchOTWorld (otBitWidth q) (ZMod q)) (fun _ => ())).map
        (fun res => I.restrict res.2) =
      PMF.uniformOfFintype ((i : I) → Beaver.TripleShare (ZMod q)) := by
  have hpriv := perfectSemiHonestPrivate_tripleFromOTMul q hq I (fun _ => ())
  have hmarg := congrArg (PMF.map (fun p => I.restrict p.2)) hpriv
  simp only [idealJoint, Protocol.realJoint, pmf_norm, Prod.map, id_eq] at hmarg
  have hconst : ∀ y : Fin 2 → Beaver.TripleShare (ZMod q),
      ((ProbComp.eval (tripleFromOTMulSim q I (I.restrict fun _ => ()) (I.restrict y))).bind
        fun _ => PMF.pure (I.restrict y)) =
      PMF.pure (I.restrict y) := by
    intro y
    rw [PMF.bind_const]
  simp_rw [hconst] at hmarg
  rw [← hmarg]
  exact Beaver.eval_restrict_beaverTripleFunctionality I hI (fun _ => ())

end Cslib.Crypto.Protocols.MPC
