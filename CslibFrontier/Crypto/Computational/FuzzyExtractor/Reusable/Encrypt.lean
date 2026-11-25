/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Crypto.Computational.FuzzyExtractor.Reusable
public import CslibFrontier.Crypto.Computational.FuzzyExtractor.Reusable.Security
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.BitString
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Probability.Product
public import Mathlib.Data.ZMod.ValMinAbs
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.Oracle.RunState
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Matrix.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Probabilistic.Oracle.RunState
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.Sampling.BitString
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.Presample
import CslibFrontier.Languages.Probabilistic.UniformNat.Residue
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.PPT

/-!
# Encryption-based strongly reusable fuzzy extractor from LWE

This file formalizes the encryption-based fuzzy extractor from Learning With Errors of Apon, Cho,
Eldefrawy, and Katz ([AponChoEldefrawyKatz2017], Section 5, pp. 11–12), which the paper shows
strongly reusable in the standard model without random oracles. Section 5 has no numbered
theorem: it sketches a proof of strong reusability "based on hardness of the `LWE_{n,(t+2)m,q,χ}`
problem, where the adversary makes at most `t` oracle calls in the experiment of Definition 3"
(p. 12), assuming that the coordinates of the reading are independent draws from `χ` and that
the encryption error has the same law. We formalize the construction, a decoder-relative step for
its setup correctness (#6040), the reduction step as a concrete advantage inequality, and the
security claim against efficient adversaries (`stronglyReusable_lweEncryptFuzzyExtractor`).

## Construction (Section 5)

Given a public matrix `A : Matrix (Fin m) (Fin n) (ZMod q)`, an encryption error sampler
`E : ProbComp (Fin l → ZMod q)`, and a syndrome decoder
`decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
  ProbComp (Option (Fin n → ZMod q))`:
* **Symmetric-key encryption (`symEncrypt`)**: given secret `s : Fin n → ZMod q` and key
  `r : Fin l → Bool`, sample uniform `B : Matrix (Fin l) (Fin n) (ZMod q)` and error
  `e ← E`, and output `(B, B s + e + ⌊q / 2⌋ r)`.
* **Symmetric-key decryption (`symDecrypt`)**: given `s`, `B`, and `h`, compute `h - B s`
  and apply the `[3q / 8, 5q / 8]` threshold decoder coordinatewise.
* **Generation (`lweEncryptFuzzyExtractor.gen`)**: on reading `w : Fin m → ZMod q`, sample
  uniform `s : Fin n → ZMod q` and uniform key `r : Fin l → Bool`, encrypt
  `(B, h) ← symEncrypt E s r`, and output `(r, ⟨A s + w, B, h⟩)`.
* **Reproduction (`lweEncryptFuzzyExtractor.rep`)**: on close reading `w'` and helper
  `⟨c, B, h⟩`, decode `c - w'` with `decode A`; on `some s`, output `symDecrypt s B h`.

## Main definitions

* `Cslib.Crypto.FuzzyExtractor.encodeHalfBit`,
  `Cslib.Crypto.FuzzyExtractor.encodeHalfBits`,
  `Cslib.Crypto.FuzzyExtractor.decodeThresholdBit`,
  `Cslib.Crypto.FuzzyExtractor.decodeThresholdBits`: half-modulus bit encoding and
  `[3q / 8, 5q / 8]` threshold decoding over `ZMod q`.
* `Cslib.Crypto.FuzzyExtractor.symEncrypt`, `Cslib.Crypto.FuzzyExtractor.symDecrypt`: the
  LWE-based symmetric-key encryption scheme `(Enc, Dec)` of Section 5.
* `Cslib.Crypto.FuzzyExtractor.EncryptHelper`,
  `Cslib.Crypto.FuzzyExtractor.lweEncryptFuzzyExtractor`: helper structure `(c, B, h)` and
  the Section 5 encryption-based reusable fuzzy extractor.
* `Cslib.Crypto.FuzzyExtractor.encryptLWEErrorLaw`,
  `Cslib.Crypto.FuzzyExtractor.encryptShiftOracle`,
  `Cslib.Crypto.FuzzyExtractor.encryptSimRun`,
  `Cslib.Crypto.FuzzyExtractor.encryptRealReduction`,
  `Cslib.Crypto.FuzzyExtractor.encryptIdealReduction`: the combined `(m + (Q + 1) * l)`-row
  LWE error distribution, the simulated shift oracle that answers the `k`-th query from the `k`-th
  `l`-row LWE block, and the real/ideal LWE reductions.
* `Cslib.Crypto.FuzzyExtractor.encEncryptHelper`: the words of a helper at modulus `2 ^ w`.
* `Cslib.Crypto.FuzzyExtractor.LWEFamily.encryptRealReduction`,
  `Cslib.Crypto.FuzzyExtractor.LWEFamily.encryptIdealReduction`: the reductions at every security
  parameter, as LWE distinguishers, against the typed adversary that a word adversary plays.

## Main results

* `Cslib.Crypto.FuzzyExtractor.decodeThresholdBit_add_encodeHalfBit`,
  `Cslib.Crypto.FuzzyExtractor.decodeThresholdBits_add_encodeHalfBits`,
  `Cslib.Crypto.FuzzyExtractor.symDecrypt_symEncrypt_eq`: deterministic decryption
  correctness whenever every coordinate `e i` of the encryption error satisfies
  `8 * (e i).valMinAbs.natAbs + 4 ≤ q`.
* `Cslib.Crypto.FuzzyExtractor.setupCorrect_lweEncryptFuzzyExtractor_of_decoderCorrectWithError`:
  a step establishing `δ`-error setup correctness of `lweEncryptFuzzyExtractor` over a uniform
  matrix `A` relative to a caller-supplied decoder (`DecoderCorrectWithError decode t δ`, #6040),
  when every error vector in `(ProbComp.eval E).support` has centered coordinates bounded by
  `8 * (e i).valMinAbs.natAbs + 4 ≤ q`.
* `Cslib.Crypto.FuzzyExtractor.realGame_encryptRealReduction`,
  `Cslib.Crypto.FuzzyExtractor.realGame_encryptIdealReduction`,
  `Cslib.Crypto.FuzzyExtractor.randomGame_encryptRealReduction_eq_ideal`: exact game
  identities linking the real and random LWE games of `encryptRealReduction` and
  `encryptIdealReduction` to `strongReuseRealGame` and `strongReuseIdealGame`, for an adversary
  that makes at most `Q` shift queries. Answering the queries from `Q` blocks drawn in advance
  has the law of answering each from a fresh block, by the presampling theorem
  `ProbOracleComp.IsQueryBounded.eval_presample`.
* `Cslib.Crypto.FuzzyExtractor.encryptLWEErrorLaw_pi`: under assumptions (1) and (2) of Section 5
  the combined error law has independent coordinates drawn from `χ`.
* `Cslib.Crypto.FuzzyExtractor.strongReuseAdvantage_lweEncryptFuzzyExtractor_le`: the reduction
  step of the Section 5 argument. For every biometric source `W`, encryption error sampler `E`,
  error bound `t`, and strong-reusability adversary `adv` making at most `Q` shift queries,
  `strongReuseAdvantage ≤ LWE.advantage uniform errs (encryptRealReduction t Q adv) +
    LWE.advantage uniform errs (encryptIdealReduction t Q adv)`,
  where the combined LWE instance has `m + (Q + 1) * l` rows and error law
  `errs = encryptLWEErrorLaw W (ProbComp.eval E) Q`. When `W = χ^m`, `E = χ^l`, and `l = m`,
  this is the paper's `LWE_{n, (t + 2) m, q, χ}` ([AponChoEldefrawyKatz2017], Section 5).
  Here `Q` is the letter `t` of Section 5, the number of oracle calls the adversary makes. It is
  not the Hamming bound `t` of Definitions 1–3, which is the argument `t` of these lemmas.
* `Cslib.Crypto.FuzzyExtractor.LWEFamily.isPPT_encryptRealReduction`,
  `Cslib.Crypto.FuzzyExtractor.LWEFamily.isPPT_encryptIdealReduction`: the reductions are uniform
  strict PPT LWE distinguishers when the word adversary is uniform strict oracle PPT.
* `Cslib.Crypto.FuzzyExtractor.stronglyReusable_lweEncryptFuzzyExtractor`: the Section 5 claim,
  `StronglyReusable` from `DecisionLWE`, against adversaries that make at most `Q κ` shift queries.

## The reductions' word programs

At parameter `κ` a reduction reads the word of the LWE matrix `[b | M]` with `m + (Q + 1) * l`
rows. Its word program writes the adversary's view from rows `0, …, m + l - 1` and answers the
`k`-th well-formed shift request from rows `m + l + l k, …, m + l + l k + l - 1`, on fresh coins
for `s'` (as `w`-bit naturals) and for the key bits. Its state is the index of the next unused
block, which stands for the unused blocks that `encryptSimRun` keeps; past the last block the rows
read as zero, as `encryptSimRun`'s fallback block. The program has the law of the typed reduction,
so the certificate is proved for the program.

## Deviations

* The modulus is `2 ^ w κ`, the modulus of `DecisionLWE`; Definition 4 allows any integer `q ≥ 2`.
  The fixed-parameter results allow any modulus `q`.
* Adversaries are uniform strict oracle PPT programs on bit words (`WordReuseAdversary`) that make
  at most `Q κ` shift queries.
* A shift of Hamming weight above `t` is answered as the shift `0` (`clampShift`), where
  Definition 3 admits only shifts of weight at most `t`.
* The key length `l` may differ from `m`, which the source takes equal (p. 11).

## References

* [D. Apon, C. Cho, K. Eldefrawy, and J. Katz, *Efficient, Reusable Fuzzy Extractors from
  LWE*][AponChoEldefrawyKatz2017], Section 5.
* [B. Fuller, X. Meng, and L. Reyzin, *Computational Fuzzy Extractors*][FullerMengReyzin2020],
  Section 4 (Construction 4.9, Lemma 4.10).
-/

public section

namespace Cslib.Crypto.FuzzyExtractor

open Probability
open scoped _root_.Matrix ENNReal NNReal

variable {m n l q : ℕ} [NeZero q]

/-! ### Half-Modulus Encoding and `[3q / 8, 5q / 8]` Threshold Decoding -/

/-- Half-modulus bit encoding in `ZMod q` ([AponChoEldefrawyKatz2017], Section 5):
`false ↦ 0` and `true ↦ ⌊q / 2⌋`. -/
@[expose] def encodeHalfBit (q : ℕ) (b : Bool) : ZMod q :=
  if b then ((q / 2 : ℕ) : ZMod q) else 0

/-- Coordinatewise half-modulus encoding of an `l`-bit key `r : Fin l → Bool` in
`Fin l → ZMod q`. -/
@[expose] def encodeHalfBits (q : ℕ) {l : ℕ} (r : Fin l → Bool) : Fin l → ZMod q :=
  fun i => encodeHalfBit q (r i)

/-- Per-coordinate threshold decoder in `ZMod q` ([AponChoEldefrawyKatz2017], Section 5):
outputs `true` iff the canonical residue `x.val` lies in `[3q / 8, 5q / 8]`, i.e.,
`3 * q ≤ 8 * x.val ∧ 8 * x.val ≤ 5 * q`. -/
@[expose] def decodeThresholdBit (q : ℕ) (x : ZMod q) : Bool :=
  decide (3 * q ≤ 8 * x.val ∧ 8 * x.val ≤ 5 * q)

/-- Coordinatewise threshold decoding of a vector `v : Fin l → ZMod q` to `Fin l → Bool`. -/
@[expose] def decodeThresholdBits (q : ℕ) {l : ℕ} (v : Fin l → ZMod q) : Fin l → Bool :=
  fun i => decodeThresholdBit q (v i)

/-- If an integer error `z : ℤ` satisfies `8 * z.natAbs + 4 ≤ q`, then adding `(z : ZMod q)`
to `encodeHalfBit q b` decodes back to `b` under the `[3q / 8, 5q / 8]` threshold decoder. -/
theorem decodeThresholdBit_intCast_add_encodeHalfBit (b : Bool) (z : ℤ)
    (hz : 8 * z.natAbs + 4 ≤ q) :
    decodeThresholdBit q ((z : ZMod q) + encodeHalfBit q b) = b := by
  have hz' : -(z.natAbs : ℤ) ≤ z ∧ z ≤ (z.natAbs : ℤ) :=
    abs_le.mp (by rw [← Int.abs_eq_natAbs])
  have hmod (x : ℤ) (hx : 0 ≤ x) (hx' : x < q) : (((x : ZMod q).val : ℕ) : ℤ) = x := by
    rw [ZMod.val_intCast, Int.emod_eq_of_lt hx hx']
  cases b
  · simp only [encodeHalfBit, Bool.false_eq_true, ↓reduceIte, add_zero, decodeThresholdBit,
      decide_eq_false_iff_not, not_and_or, not_le]
    by_cases hnonneg : 0 ≤ z
    · exact Or.inl (by have := hmod z hnonneg (by omega); omega)
    · have hval := hmod (z + q) (by omega) (by omega)
      simp only [Int.cast_add, Int.cast_natCast, CharP.cast_eq_zero, add_zero] at hval
      exact Or.inr (by omega)
  · simp only [encodeHalfBit, ↓reduceIte, decodeThresholdBit, decide_eq_true_eq]
    have hcast : (z : ZMod q) + ((q / 2 : ℕ) : ZMod q) =
        ((z + ((q / 2 : ℕ) : ℤ) : ℤ) : ZMod q) := by
      rw [Int.cast_add, Int.cast_natCast]
    have hval := hmod (z + ((q / 2 : ℕ) : ℤ)) (by omega) (by omega)
    rw [hcast]
    omega

/-- If a residue `e : ZMod q` has centered representative `e.valMinAbs` satisfying
`8 * e.valMinAbs.natAbs + 4 ≤ q`, then `decodeThresholdBit q (e + encodeHalfBit q b) = b`. -/
theorem decodeThresholdBit_add_encodeHalfBit (b : Bool) (e : ZMod q)
    (he : 8 * e.valMinAbs.natAbs + 4 ≤ q) :
    decodeThresholdBit q (e + encodeHalfBit q b) = b := by
  simpa only [ZMod.coe_valMinAbs] using
    decodeThresholdBit_intCast_add_encodeHalfBit (q := q) b e.valMinAbs he

/-- Coordinatewise threshold decoding recovers `r : Fin l → Bool` from
`e + encodeHalfBits q r` whenever every coordinate `e i` satisfies
`8 * (e i).valMinAbs.natAbs + 4 ≤ q`. -/
theorem decodeThresholdBits_add_encodeHalfBits (r : Fin l → Bool) (e : Fin l → ZMod q)
    (he : ∀ i : Fin l, 8 * (e i).valMinAbs.natAbs + 4 ≤ q) :
    decodeThresholdBits q (e + encodeHalfBits q r) = r := by
  ext i
  exact decodeThresholdBit_add_encodeHalfBit (r i) (e i) (he i)

/-! ### Section 5 Symmetric Encryption and Fuzzy Extractor Construction -/

/-- Symmetric-key encryption `Enc_s(r)` of [AponChoEldefrawyKatz2017], Section 5:
sample uniform `B : Matrix (Fin l) (Fin n) (ZMod q)` and error `e ← E`, and output
`(B, B s + e + ⌊q / 2⌋ r)`. -/
@[expose] noncomputable def symEncrypt (E : ProbComp (Fin l → ZMod q))
    (s : Fin n → ZMod q) (r : Fin l → Bool) :
    ProbComp (Matrix (Fin l) (Fin n) (ZMod q) × (Fin l → ZMod q)) := do
  let B ← ProbComp.uniform (Matrix (Fin l) (Fin n) (ZMod q))
  let e ← E
  return (B, B.mulVec s + e + encodeHalfBits q r)

/-- Symmetric-key decryption `Dec_s(B, h)` of [AponChoEldefrawyKatz2017], Section 5:
compute `h - B s` and apply the `[3q / 8, 5q / 8]` threshold decoder coordinatewise. -/
@[expose] def symDecrypt (s : Fin n → ZMod q)
    (B : Matrix (Fin l) (Fin n) (ZMod q)) (h : Fin l → ZMod q) : Fin l → Bool :=
  decodeThresholdBits q (h - B.mulVec s)

/-- Deterministic decryption identity: `symDecrypt s B (B s + e + encodeHalfBits q r) = r`
whenever every coordinate of `e` satisfies `8 * (e i).valMinAbs.natAbs + 4 ≤ q`. -/
theorem symDecrypt_symEncrypt_eq (s : Fin n → ZMod q)
    (B : Matrix (Fin l) (Fin n) (ZMod q)) (e : Fin l → ZMod q) (r : Fin l → Bool)
    (he : ∀ i : Fin l, 8 * (e i).valMinAbs.natAbs + 4 ≤ q) :
    symDecrypt s B (B.mulVec s + e + encodeHalfBits q r) = r := by
  have hsub : B.mulVec s + e + encodeHalfBits q r - B.mulVec s = e + encodeHalfBits q r := by
    abel
  rw [symDecrypt, hsub, decodeThresholdBits_add_encodeHalfBits r e he]

/-- Helper data `P = (c, B, h)` for the Section 5 encryption-based reusable fuzzy extractor
([AponChoEldefrawyKatz2017], Section 5), consisting of:
* `codeOffset`: the code-offset vector `c = A s + w : Fin m → ZMod q`,
* `encMatrix`: the fresh encryption matrix `B : Matrix (Fin l) (Fin n) (ZMod q)`,
* `ciphertext`: the LWE ciphertext vector `h = B s + e + ⌊q / 2⌋ r : Fin l → ZMod q`. -/
structure EncryptHelper (m n l q : ℕ) where
  /-- Code-offset vector `c = A s + w`. -/
  codeOffset : Fin m → ZMod q
  /-- Fresh LWE matrix `B` for symmetric-key encryption. -/
  encMatrix : Matrix (Fin l) (Fin n) (ZMod q)
  /-- LWE ciphertext vector `h = B s + e + ⌊q / 2⌋ r`. -/
  ciphertext : Fin l → ZMod q
  deriving DecidableEq

instance : Inhabited (EncryptHelper m n l q) :=
  ⟨⟨0, 0, 0⟩⟩

/-- The Section 5 encryption-based reusable fuzzy extractor from LWE
([AponChoEldefrawyKatz2017], Section 5), parameterized by the public matrix
`A : Matrix (Fin m) (Fin n) (ZMod q)`, encryption error sampler `E : ProbComp (Fin l → ZMod q)`,
and syndrome decoder `decode`:
* `gen w`: sample uniform secret `s : Fin n → ZMod q` and uniform key `r : Fin l → Bool`,
  encrypt `(B, h) ← symEncrypt E s r`, and output `(r, ⟨A s + w, B, h⟩)`.
* `rep w' ⟨c, B, h⟩`: decode `c - w'` using `decode A`; on `some s`, output
  `symDecrypt s B h` (defaulting to `fun _ => false` on `none`). -/
@[expose] noncomputable def lweEncryptFuzzyExtractor (m n l q : ℕ) [NeZero q]
    (E : ProbComp (Fin l → ZMod q))
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (A : Matrix (Fin m) (Fin n) (ZMod q)) :
    FuzzyExtractor (Fin m → ZMod q) (Fin l → Bool) (EncryptHelper m n l q) where
  gen w := do
    let s ← ProbComp.uniform (Fin n → ZMod q)
    let r ← ProbComp.uniform (Fin l → Bool)
    let (B, h) ← symEncrypt E s r
    return (r, ⟨A.mulVec s + w, B, h⟩)
  rep w' helper := do
    let sOpt ← decode A (helper.codeOffset - w')
    match sOpt with
    | some s => return symDecrypt s helper.encMatrix helper.ciphertext
    | none => return fun _ => false

/-! ### Section 5 Correctness -/

/-- A step after [AponChoEldefrawyKatz2017] Section 5 (p. 12) establishing `δ`-error Hamming
setup correctness of `lweEncryptFuzzyExtractor m n l q E decode` over a uniform public matrix `A`
relative to a caller-supplied decoder (`hdec : DecoderCorrectWithError decode t δ`), not the
unconditional correctness claim of Section 5, because the concrete random-subset LWE decoder of
[FullerMengReyzin2020] Construction 4.9 / Lemma 4.10 (pp. 15–16) is not formalized (#6040).
When every encryption error vector `e` in the support of `E` satisfies
`8 * (e i).valMinAbs.natAbs + 4 ≤ q` for all `i : Fin l`, decryption is exact once decoding
succeeds, so the only reproduction failure is a decoding failure. -/
theorem setupCorrect_lweEncryptFuzzyExtractor_of_decoderCorrectWithError
    {E : ProbComp (Fin l → ZMod q)}
    {decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q))}
    {t : ℕ} {δ : ℝ≥0} (hdec : DecoderCorrectWithError decode t δ)
    (herr : ∀ e ∈ (ProbComp.eval E).support, ∀ i : Fin l, 8 * (e i).valMinAbs.natAbs + 4 ≤ q) :
    SetupCorrectHammingWithError (ProbComp.uniform (Matrix (Fin m) (Fin n) (ZMod q)))
      (lweEncryptFuzzyExtractor m n l q E decode) t δ := by
  intro w w' hdis
  rw [hammingDist_comm, hammingDist_eq_hammingNorm, neg_add_eq_sub] at hdis
  rw [← ENNReal.coe_le_coe]
  simp only [Game.failProbability, ENNReal.coe_toNNReal (PMF.apply_ne_top _ _), setupReproduceGame,
    FuzzyExtractor.reproduceGame, FuzzyExtractor.reproduceCheck, lweEncryptFuzzyExtractor,
    symEncrypt, ProbComp.eval_uniform, pmf_norm]
  pmf_hoist (PMF.uniformOfFintype (Fin n → ZMod q))
  pmf_hoist (PMF.uniformOfFintype (Fin l → Bool))
  pmf_hoist (PMF.uniformOfFintype (Matrix (Fin l) (Fin n) (ZMod q)))
  pmf_hoist (ProbComp.eval E)
  refine PMF.bind_apply_le_on_support _ fun e he => PMF.bind_apply_le_on_support _ fun B _ =>
    PMF.bind_apply_le_on_support _ fun r _ => PMF.bind_apply_le_on_support _ fun s _ => ?_
  simp only [add_sub_assoc]
  exact uniform_bind_decode_bind_apply_false_le_of_failProbability_le decode s (w - w') _
    (fun A => by simp [symDecrypt_symEncrypt_eq s B e r (herr e he)]) (hdec s (w - w') hdis)

/-! ### Row-Block Splitting for `(m + (Q + 1) * l)`-Row LWE Instances -/

/-- Index equivalence partitioning `Fin (m + (Q + 1) * l)` into:
* `Sum.inl i` (`i : Fin m`) for the `m` rows of the public matrix `A`,
* `Sum.inr (Sum.inl i)` (`i : Fin l`) for the `l` rows of the challenge encryption matrix `B`,
* `Sum.inr (Sum.inr (k, i))` (`k : Fin Q`, `i : Fin l`) for row `i` of the `k`-th shift-query
  encryption matrix `B_k`. -/
private def rowIndexEquiv (m l Q : ℕ) :
    Fin m ⊕ (Fin l ⊕ (Fin Q × Fin l)) ≃ Fin (m + (Q + 1) * l) :=
  (Equiv.sumCongr (Equiv.refl (Fin m))
    ((Equiv.sumCongr (Equiv.refl (Fin l)) finProdFinEquiv).trans
      (finSumFinEquiv.trans (finCongr (by ring))))).trans finSumFinEquiv

/-- Stack an `m`-row block, an `l`-row block, and `Q` blocks of `l` rows into a single
`(m + (Q + 1) * l)`-row family. -/
private def joinRows {m l Q : ℕ} {α : Type}
    (xA : Fin m → α) (xB : Fin l → α) (xQ : Fin Q → Fin l → α) :
    Fin (m + (Q + 1) * l) → α :=
  fun idx =>
    match (rowIndexEquiv m l Q).symm idx with
    | Sum.inl i => xA i
    | Sum.inr (Sum.inl i) => xB i
    | Sum.inr (Sum.inr (k, i)) => xQ k i

/-- Extract the top `m`-row block from a `(m + (Q + 1) * l)`-row family. -/
private def headRows {m l Q : ℕ} {α : Type} (f : Fin (m + (Q + 1) * l) → α) : Fin m → α :=
  fun i => f (rowIndexEquiv m l Q (Sum.inl i))

/-- Extract the challenge `l`-row block from a `(m + (Q + 1) * l)`-row family. -/
private def challengeRows {m l Q : ℕ} {α : Type} (f : Fin (m + (Q + 1) * l) → α) : Fin l → α :=
  fun i => f (rowIndexEquiv m l Q (Sum.inr (Sum.inl i)))

/-- Extract the `Q` query blocks of `l` rows each from a `(m + (Q + 1) * l)`-row family. -/
private def queryRows {m l Q : ℕ} {α : Type} (f : Fin (m + (Q + 1) * l) → α) : Fin Q → Fin l → α :=
  fun k i => f (rowIndexEquiv m l Q (Sum.inr (Sum.inr (k, i))))

/-- Extract the top `m × n` matrix block from an `(m + (Q + 1) * l) × n` matrix. -/
private def headMatrixRows {m n l Q : ℕ} {α : Type}
    (M : Matrix (Fin (m + (Q + 1) * l)) (Fin n) α) : Matrix (Fin m) (Fin n) α :=
  headRows M

/-- Extract the challenge `l × n` matrix block from an `(m + (Q + 1) * l) × n` matrix. -/
private def challengeMatrixRows {m n l Q : ℕ} {α : Type}
    (M : Matrix (Fin (m + (Q + 1) * l)) (Fin n) α) : Matrix (Fin l) (Fin n) α :=
  challengeRows M

/-- Extract the `Q` query matrix blocks of size `l × n` from an `(m + (Q + 1) * l) × n` matrix. -/
private def queryMatrixRows {m n l Q : ℕ} {α : Type}
    (M : Matrix (Fin (m + (Q + 1) * l)) (Fin n) α) : Fin Q → Matrix (Fin l) (Fin n) α :=
  queryRows M

private def joinMatrixRows {m n l Q : ℕ} {α : Type}
    (A : Matrix (Fin m) (Fin n) α) (B : Matrix (Fin l) (Fin n) α)
    (B_vec : Fin Q → Matrix (Fin l) (Fin n) α) :
    Matrix (Fin (m + (Q + 1) * l)) (Fin n) α :=
  joinRows A B B_vec

@[simp]
private theorem headRows_joinRows {m l Q : ℕ} {α : Type}
    (xA : Fin m → α) (xB : Fin l → α) (xQ : Fin Q → Fin l → α) :
    headRows (joinRows xA xB xQ) = xA := by
  ext i
  simp [headRows, joinRows]

@[simp]
private theorem challengeRows_joinRows {m l Q : ℕ} {α : Type}
    (xA : Fin m → α) (xB : Fin l → α) (xQ : Fin Q → Fin l → α) :
    challengeRows (joinRows xA xB xQ) = xB := by
  ext i
  simp [challengeRows, joinRows]

@[simp]
private theorem queryRows_joinRows {m l Q : ℕ} {α : Type}
    (xA : Fin m → α) (xB : Fin l → α) (xQ : Fin Q → Fin l → α) :
    queryRows (joinRows xA xB xQ) = xQ := by
  ext k i
  simp [queryRows, joinRows]

@[simp]
private theorem headMatrixRows_joinMatrixRows {m n l Q : ℕ} {α : Type}
    (A : Matrix (Fin m) (Fin n) α) (B : Matrix (Fin l) (Fin n) α)
    (B_vec : Fin Q → Matrix (Fin l) (Fin n) α) :
    headMatrixRows (joinMatrixRows A B B_vec) = A :=
  headRows_joinRows A B B_vec

@[simp]
private theorem challengeMatrixRows_joinMatrixRows {m n l Q : ℕ} {α : Type}
    (A : Matrix (Fin m) (Fin n) α) (B : Matrix (Fin l) (Fin n) α)
    (B_vec : Fin Q → Matrix (Fin l) (Fin n) α) :
    challengeMatrixRows (joinMatrixRows A B B_vec) = B :=
  challengeRows_joinRows A B B_vec

@[simp]
private theorem queryMatrixRows_joinMatrixRows {m n l Q : ℕ} {α : Type}
    (A : Matrix (Fin m) (Fin n) α) (B : Matrix (Fin l) (Fin n) α)
    (B_vec : Fin Q → Matrix (Fin l) (Fin n) α) :
    queryMatrixRows (joinMatrixRows A B B_vec) = B_vec :=
  queryRows_joinRows A B B_vec

@[simp]
private theorem joinRows_headRows_challengeRows_queryRows {m l Q : ℕ} {α : Type}
    (f : Fin (m + (Q + 1) * l) → α) :
    joinRows (headRows f) (challengeRows f) (queryRows f) = f := by
  ext idx
  simp only [joinRows, headRows, challengeRows, queryRows]
  rcases h : (rowIndexEquiv m l Q).symm idx with i | (i | ⟨k, i⟩) <;>
    simp [← h]

private def splitRowsEquiv (m l Q : ℕ) (α : Type) :
    (Fin m → α) × ((Fin l → α) × (Fin Q → Fin l → α)) ≃ (Fin (m + (Q + 1) * l) → α) where
  toFun p :=
    let (xA, rest) := p
    let (xB, xQ) := rest
    joinRows xA xB xQ
  invFun f := (headRows f, (challengeRows f, queryRows f))
  left_inv p := by
    obtain ⟨xA, xB, xQ⟩ := p
    simp
  right_inv f := by simp

@[simp]
private theorem headRows_mulVec_add {m n l Q q : ℕ}
    (M : Matrix (Fin (m + (Q + 1) * l)) (Fin n) (ZMod q))
    (s : Fin n → ZMod q) (err : Fin (m + (Q + 1) * l) → ZMod q) :
    headRows (M *ᵥ s + err) = (headMatrixRows M).mulVec s + headRows err := rfl

@[simp]
private theorem challengeRows_mulVec_add {m n l Q q : ℕ}
    (M : Matrix (Fin (m + (Q + 1) * l)) (Fin n) (ZMod q))
    (s : Fin n → ZMod q) (err : Fin (m + (Q + 1) * l) → ZMod q) :
    challengeRows (M *ᵥ s + err) = (challengeMatrixRows M).mulVec s + challengeRows err := rfl

@[simp]
private theorem queryRows_mulVec_add {m n l Q q : ℕ}
    (M : Matrix (Fin (m + (Q + 1) * l)) (Fin n) (ZMod q))
    (s : Fin n → ZMod q) (err : Fin (m + (Q + 1) * l) → ZMod q) :
    queryRows (M *ᵥ s + err) = fun k => (queryMatrixRows M k).mulVec s + queryRows err k := rfl

private theorem uniform_bind_splitRows {m l Q : ℕ} {α β : Type} [Fintype α] [Nonempty α]
    (k : (Fin (m + (Q + 1) * l) → α) → PMF β) :
    (PMF.uniformOfFintype (Fin (m + (Q + 1) * l) → α)).bind k =
      (PMF.uniformOfFintype (Fin m → α)).bind fun xA =>
        (PMF.uniformOfFintype (Fin l → α)).bind fun xB =>
          (PMF.uniformOfFintype (Fin Q → Fin l → α)).bind fun xQ =>
            k (joinRows xA xB xQ) := by
  rw [← Probability.PMF.uniformOfFintype_bind_bind_equiv (splitRowsEquiv m l Q α) k]
  congr 1 with xA : 1
  rw [← Probability.PMF.uniformOfFintype_bind_bind_equiv (Equiv.refl _)
    (fun b => k ((splitRowsEquiv m l Q α) (xA, b)))]
  rfl

private theorem uniform_bind_splitMatrixRows {m n l Q : ℕ} {α β : Type}
    [Fintype α] [Inhabited α]
    (k : Matrix (Fin (m + (Q + 1) * l)) (Fin n) α → PMF β) :
    (PMF.uniformOfFintype (Matrix (Fin (m + (Q + 1) * l)) (Fin n) α)).bind k =
      (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) α)).bind fun A =>
        (PMF.uniformOfFintype (Matrix (Fin l) (Fin n) α)).bind fun B =>
          (PMF.uniformOfFintype (Fin Q → Matrix (Fin l) (Fin n) α)).bind fun B_vec =>
            k (joinMatrixRows A B B_vec) :=
  uniform_bind_splitRows k

/-! ### Section 5 Strong Reusability Reduction to Decisional LWE -/

/-- The product error distribution on `Fin (m + (Q + 1) * l) → ZMod q` for the Section 5
strong-reusability LWE reduction ([AponChoEldefrawyKatz2017], Section 5):
* the first `m` coordinates are drawn from the biometric source `W`;
* the next `l` coordinates (challenge encryption error) are drawn from `E`;
* the remaining `Q` blocks of `l` coordinates (shift-query encryption errors) are drawn
  independently from `E`.
When `W = χ^m`, `E = χ^l`, and `l = m`, this is `χ^{(Q + 2) m}`, matching `LWE_{n, (t + 2) m, q, χ}`
in [AponChoEldefrawyKatz2017], Section 5, where `t` is the number of oracle calls (our `Q`), not the
Hamming bound. -/
noncomputable def encryptLWEErrorLaw {m l q : ℕ} [NeZero q]
    (W : PMF (Fin m → ZMod q)) (E : PMF (Fin l → ZMod q)) (Q : ℕ) :
    PMF (Fin (m + (Q + 1) * l) → ZMod q) :=
  W.bind fun w =>
    E.bind fun e₀ =>
      (Probability.PMF.pi (fun _ : Fin Q => E)).bind fun eQ =>
        PMF.pure (joinRows w e₀ eQ)

/-- Under assumptions (1) and (2) of [AponChoEldefrawyKatz2017], Section 5, p. 12, the combined
error law of `encryptLWEErrorLaw` is that of plain LWE: when every coordinate of the reading and
of each encryption error is drawn independently from one law `χ`, all `m + (Q + 1) * l`
coordinates are drawn independently from `χ`. -/
theorem encryptLWEErrorLaw_pi (χ : PMF (ZMod q)) (Q : ℕ) :
    encryptLWEErrorLaw (Probability.PMF.pi fun _ : Fin m => χ)
        (Probability.PMF.pi fun _ : Fin l => χ) Q =
      Probability.PMF.pi fun _ : Fin (m + (Q + 1) * l) => χ := by
  set E := Probability.PMF.pi fun _ : Fin l => χ
  have hlaw : encryptLWEErrorLaw (Probability.PMF.pi fun _ : Fin m => χ) E Q =
      ((Probability.PMF.pi fun _ : Fin m => χ).bind fun w =>
        (E.bind fun e₀ => (Probability.PMF.pi fun _ : Fin Q => E).map (e₀, ·)).map (w, ·)).map
          (splitRowsEquiv m l Q (ZMod q)) := by
    simp only [encryptLWEErrorLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]
    rfl
  rw [hlaw]
  ext f
  rw [Probability.PMF.map_equiv_apply, Probability.PMF.bind_map_prodMk_apply,
    Probability.PMF.bind_map_prodMk_apply]
  change (∏ i, χ (headRows f i)) * ((∏ i, χ (challengeRows f i)) *
      ∏ k, ∏ i, χ (queryRows f k i)) = ∏ r, χ (f r)
  rw [← Fintype.prod_equiv (rowIndexEquiv m l Q) (fun x => χ (f (rowIndexEquiv m l Q x)))
    (fun r => χ (f r)) fun _ => rfl, Fintype.prod_sum_type, Fintype.prod_sum_type,
    Fintype.prod_prod_type]
  rfl

/-- The shift oracle of the Section 5 reduction ([AponChoEldefrawyKatz2017], Section 5, step 2 of
the simulation on p. 12), answering a shift `δ` from one `l`-row LWE block `(B_k, b_k)`: sample a
fresh uniform `s' : Fin n → ZMod q` and key `r_i : Fin l → Bool`, and return
`(⟨c* + A s' + clampShift t δ, B_k, b_k + B_k s' + encodeHalfBits q r_i⟩, r_i)`. It never sees
`s`, `w*` or the LWE errors. -/
noncomputable def encryptShiftOracle (t : ℕ) (A : Matrix (Fin m) (Fin n) (ZMod q))
    (cStar : Fin m → ZMod q) (B : Matrix (Fin l) (Fin n) (ZMod q)) (b : Fin l → ZMod q)
    (δ : Fin m → ZMod q) : ProbComp (EncryptHelper m n l q × (Fin l → Bool)) := do
  let s' ← ProbComp.uniform (Fin n → ZMod q)
  let rᵢ ← ProbComp.uniform (Fin l → Bool)
  return (⟨cStar + A.mulVec s' + clampShift t δ, B, b + B.mulVec s' + encodeHalfBits q rᵢ⟩, rᵢ)

/-- Run the query stage of `adv` on public matrix `A` and challenge helper `pStar`, answering the
`k`-th shift query from the `k`-th block `(B_k, b_k)` of `blocks` with `encryptShiftOracle` and
returning the saved state. An exhausted list supplies the zero block. -/
noncomputable def encryptSimRun {σ : Type} (t : ℕ) (A : Matrix (Fin m) (Fin n) (ZMod q))
    (pStar : EncryptHelper m n l q)
    (adv : StrongReuseAdversary (Matrix (Fin m) (Fin n) (ZMod q)) m q
      (Fin l → Bool) (EncryptHelper m n l q) σ)
    (blocks : List (Matrix (Fin l) (Fin n) (ZMod q) × (Fin l → ZMod q))) : ProbComp σ := do
  let (st, _) ← (ProbOracleComp.runState (adv.query A pStar) (OracleComp.withSampleList (0, 0)
    fun (B, b) δ => StateT.lift (encryptShiftOracle t A pStar.codeOffset B b δ))).run ((), blocks)
  return st

/-- The real-key LWE reduction of [AponChoEldefrawyKatz2017], Section 5 (simulation on p. 12):
given an `(m + (Q + 1) * l)`-row LWE instance `(M, b)`, read
* `(A, c*) = (headMatrixRows M, headRows b)` for the public matrix and challenge code-offset vector,
* `(B, b₁) = (challengeMatrixRows M, challengeRows b)` for the challenge encryption,
* the `Q` blocks `(queryMatrixRows M k, queryRows b k)` for the shift queries;
sample a uniform challenge key `r* : Fin l → Bool`, give `adv` the helper
`⟨c*, B, b₁ + encodeHalfBits q r*⟩`, answer its `k`-th shift query from the `k`-th block
(`encryptSimRun`), and pass `r*` to `adv.guess`. The reduction never sees the secret `s`, reading
`w*`, or encryption errors. -/
noncomputable def encryptRealReduction {σ : Type} (t Q : ℕ)
    (adv : StrongReuseAdversary (Matrix (Fin m) (Fin n) (ZMod q)) m q
      (Fin l → Bool) (EncryptHelper m n l q) σ)
    (M : Matrix (Fin (m + (Q + 1) * l)) (Fin n) (ZMod q))
    (b : Fin (m + (Q + 1) * l) → ZMod q) : Experiment := do
  let rStar ← ProbComp.uniform (Fin l → Bool)
  let st ← encryptSimRun t (headMatrixRows M)
    ⟨headRows b, challengeMatrixRows M, challengeRows b + encodeHalfBits q rStar⟩ adv
    (List.ofFn fun k => (queryMatrixRows M k, queryRows b k))
  adv.guess st rStar

/-- The ideal-key LWE reduction of [AponChoEldefrawyKatz2017], Section 5 (simulation on p. 12):
as `encryptRealReduction`, except `adv.guess` receives an independent uniform key
`u ← ProbComp.uniform (Fin l → Bool)` in place of `r*`. -/
noncomputable def encryptIdealReduction {σ : Type} (t Q : ℕ)
    (adv : StrongReuseAdversary (Matrix (Fin m) (Fin n) (ZMod q)) m q
      (Fin l → Bool) (EncryptHelper m n l q) σ)
    (M : Matrix (Fin (m + (Q + 1) * l)) (Fin n) (ZMod q))
    (b : Fin (m + (Q + 1) * l) → ZMod q) : Experiment := do
  let rStar ← ProbComp.uniform (Fin l → Bool)
  let st ← encryptSimRun t (headMatrixRows M)
    ⟨headRows b, challengeMatrixRows M, challengeRows b + encodeHalfBits q rStar⟩ adv
    (List.ofFn fun k => (queryMatrixRows M k, queryRows b k))
  let u ← ProbComp.uniform (Fin l → Bool)
  adv.guess st u

/-! ### Reduction Equivalence Lemmas -/

/-- One shift query answered from a fresh LWE block `(B, B s + e)`, with `B` uniform and `e ← E`,
has the law of the honest strong-reusability oracle of `lweEncryptFuzzyExtractor` on reading `w`,
when the challenge code offset is `A s + w`: the secret `s + s'` of the simulated answer is
uniform. -/
private theorem eval_encryptShiftOracle_eq {m n l q : ℕ} [NeZero q]
    (E : ProbComp (Fin l → ZMod q))
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (t : ℕ) (A : Matrix (Fin m) (Fin n) (ZMod q))
    (s : Fin n → ZMod q) (w δ : Fin m → ZMod q) :
    ProbComp.eval (do
      let B ← ProbComp.uniform (Matrix (Fin l) (Fin n) (ZMod q))
      let e ← E
      encryptShiftOracle t A (A.mulVec s + w) B (B.mulVec s + e) δ) =
      ProbComp.eval (strongReuseOracle (lweEncryptFuzzyExtractor m n l q E decode) t A w δ) := by
  simp only [encryptShiftOracle, strongReuseOracle, lweEncryptFuzzyExtractor, symEncrypt,
    ProbComp.eval_uniform, pmf_norm]
  conv_rhs => rw [← Probability.PMF.uniformOfFintype_bind_equiv (Equiv.addLeft s)]
  pmf_swap
  simp only [Equiv.coe_addLeft, Matrix.mulVec_add]
  congr 3 <;> abel

/-- **The query stage of the Section 5 reduction.** If `adv` makes at most `Q` shift queries on
the challenge helper `pStar`, whose code offset is `A s + w`, then answering them from `Q`
independent blocks `(B_k, B_k s + e_k)`, with `B_k` uniform and `e_k ← E`, gives the saved state
the law it has against the honest strong-reusability oracle. This is the presampling theorem
`ProbOracleComp.IsQueryBounded.eval_presample` with `eval_encryptShiftOracle_eq` at each query. -/
private theorem eval_encryptSimRun_eq {m n l q : ℕ} [NeZero q] {σ : Type}
    (E : ProbComp (Fin l → ZMod q))
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (t : ℕ) (A : Matrix (Fin m) (Fin n) (ZMod q))
    (s : Fin n → ZMod q) (w : Fin m → ZMod q) (B : Matrix (Fin l) (Fin n) (ZMod q))
    (h : Fin l → ZMod q)
    (adv : StrongReuseAdversary (Matrix (Fin m) (Fin n) (ZMod q)) m q
      (Fin l → Bool) (EncryptHelper m n l q) σ) (Q : ℕ)
    (hQ : ProbOracleComp.IsQueryBounded (adv.query A ⟨A.mulVec s + w, B, h⟩) Q) :
    ((PMF.uniformOfFintype (Fin Q → Matrix (Fin l) (Fin n) (ZMod q))).bind fun B_vec =>
      (Probability.PMF.pi (fun _ : Fin Q => ProbComp.eval E)).bind fun e_vec =>
        ProbComp.eval (encryptSimRun t A ⟨A.mulVec s + w, B, h⟩ adv
          (List.ofFn fun k => (B_vec k, (B_vec k).mulVec s + e_vec k)))) =
      ProbComp.eval ((adv.query A ⟨A.mulVec s + w, B, h⟩).run
        (strongReuseOracle (lweEncryptFuzzyExtractor m n l q E decode) t A w)) := by
  let block : ProbComp (Matrix (Fin l) (Fin n) (ZMod q) × (Fin l → ZMod q)) := do
    let B' ← ProbComp.uniform (Matrix (Fin l) (Fin n) (ZMod q))
    let e ← E
    return (B', B'.mulVec s + e)
  let oracle : Matrix (Fin l) (Fin n) (ZMod q) × (Fin l → ZMod q) → (Fin m → ZMod q) →
      StateT Unit ProbComp (EncryptHelper m n l q × (Fin l → Bool)) :=
    fun (B', b) δ => StateT.lift (encryptShiftOracle t A (A.mulVec s + w) B' b δ)
  have hpresample := congrArg (PMF.map Prod.fst) (hQ.eval_presample block (0, 0) oracle ())
  have hhonest (δ : Fin m → ZMod q) : ProbComp.eval (block >>= fun value =>
      encryptShiftOracle t A (A.mulVec s + w) value.1 value.2 δ) =
      ProbComp.eval (strongReuseOracle (lweEncryptFuzzyExtractor m n l q E decode) t A w δ) := by
    rw [← eval_encryptShiftOracle_eq E decode t A s w δ]; simp only [block, bind_assoc, pure_bind]
  have hblock : ProbComp.eval block =
      (PMF.uniformOfFintype (Matrix (Fin l) (Fin n) (ZMod q))).bind fun B' =>
        (ProbComp.eval E).map fun e => (B', B'.mulVec s + e) := by
    simp only [block, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
    rfl
  have hblocks : ((PMF.uniformOfFintype (Fin Q → Matrix (Fin l) (Fin n) (ZMod q))).bind
      fun B_vec => (Probability.PMF.pi (fun _ : Fin Q => ProbComp.eval E)).bind fun e_vec =>
        ProbComp.eval (encryptSimRun t A ⟨A.mulVec s + w, B, h⟩ adv
          (List.ofFn fun k => (B_vec k, (B_vec k).mulVec s + e_vec k)))) =
      (ProbComp.eval (OracleComp.replicate Q block)).bind
        fun values => ProbComp.eval (encryptSimRun t A ⟨A.mulVec s + w, B, h⟩ adv values) := by
    rw [ProbComp.eval_replicate, hblock, Probability.PMF.pi_bind,
      ← Probability.PMF.pi_uniformOfFintype]
    simp only [Probability.PMF.pi_map, pmf_norm]
  have hfresh : (fun δ (u : Unit) => block >>= fun value => oracle value δ u) = fun δ =>
      StateT.lift (block >>= fun value =>
        encryptShiftOracle t A (A.mulVec s + w) value.1 value.2 δ) := by
    funext δ u
    simp only [oracle, StateT.lift, bind_assoc]
  rw [hblocks]
  simp only [pmf_norm] at hpresample
  simp only [encryptSimRun, ProbComp.eval_bind, ProbComp.eval_pure]
  refine hpresample.trans ?_
  change PMF.map Prod.fst (ProbComp.eval ((ProbOracleComp.runState _ fun δ (u : Unit) =>
    block >>= fun value => oracle value δ u).run ())) = _
  rw [hfresh, ProbOracleComp.runState_lift, ProbComp.eval_map, PMF.map_comp]
  simp only [Function.comp_def, ProbOracleComp.eval_run, hhonest]
  exact PMF.map_id _

private theorem realGame_encrypt_embed {St : Type}
    (E : ProbComp (Fin l → ZMod q))
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (W : PMF (Fin m → ZMod q)) (t Q : ℕ)
    (adv : StrongReuseAdversary (Matrix (Fin m) (Fin n) (ZMod q)) m q
      (Fin l → Bool) (EncryptHelper m n l q) St)
    (hQ : ∀ A pStar, ProbOracleComp.IsQueryBounded (adv.query A pStar) Q)
    (K : St → (Fin l → Bool) → PMF Bool) :
    ((PMF.uniformOfFintype (Fin n → ZMod q)).bind fun s =>
      W.bind fun w =>
        (ProbComp.eval E).bind fun e₀ =>
          (Probability.PMF.pi (fun _ : Fin Q => ProbComp.eval E)).bind fun eQ =>
            (PMF.uniformOfFintype (Matrix (Fin (m + (Q + 1) * l)) (Fin n) (ZMod q))).bind fun M =>
              (PMF.uniformOfFintype (Fin l → Bool)).bind fun rStar =>
                (ProbComp.eval (encryptSimRun t (headMatrixRows M)
                  ⟨headRows (M *ᵥ s + joinRows w e₀ eQ), challengeMatrixRows M,
                    challengeRows (M *ᵥ s + joinRows w e₀ eQ) + encodeHalfBits q rStar⟩ adv
                  (List.ofFn fun k =>
                    (queryMatrixRows M k, queryRows (M *ᵥ s + joinRows w e₀ eQ) k)))).bind
                  fun st => K st rStar) =
      (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))).bind fun A =>
        W.bind fun w =>
          (PMF.uniformOfFintype (Fin n → ZMod q)).bind fun s =>
            (PMF.uniformOfFintype (Fin l → Bool)).bind fun rStar =>
              (PMF.uniformOfFintype (Matrix (Fin l) (Fin n) (ZMod q))).bind fun B =>
                (ProbComp.eval E).bind fun e₀ =>
                  (ProbComp.eval ((adv.query A
                    ⟨A.mulVec s + w, B, B.mulVec s + e₀ + encodeHalfBits q rStar⟩).run
                      (strongReuseOracle (lweEncryptFuzzyExtractor m n l q E decode) t A w))).bind
                    fun st => K st rStar := by
  simp_rw [uniform_bind_splitMatrixRows]
  simp only [headRows_mulVec_add, challengeRows_mulVec_add, queryRows_mulVec_add,
    headRows_joinRows, challengeRows_joinRows, queryRows_joinRows,
    headMatrixRows_joinMatrixRows, challengeMatrixRows_joinMatrixRows,
    queryMatrixRows_joinMatrixRows]
  pmf_swap with A w s rStar B e₀
  rw [PMF.bind_comm (Probability.PMF.pi (fun _ : Fin Q => ProbComp.eval E))]
  have hloop := congrArg (fun p : PMF St => p.bind fun st => K st rStar)
    (eval_encryptSimRun_eq E decode t A s w B (B.mulVec s + e₀ + encodeHalfBits q rStar) adv Q
      (hQ _ _))
  simpa only [PMF.bind_bind] using hloop

/-- The real LWE game against `encryptRealReduction t Q adv` is identically distributed to
the strong-reusability real game `strongReuseRealGame` of `lweEncryptFuzzyExtractor`, for an
adversary that makes at most `Q` shift queries. -/
theorem realGame_encryptRealReduction {St : Type}
    (E : ProbComp (Fin l → ZMod q))
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (W : PMF (Fin m → ZMod q)) (t Q : ℕ)
    (adv : StrongReuseAdversary (Matrix (Fin m) (Fin n) (ZMod q)) m q
      (Fin l → Bool) (EncryptHelper m n l q) St)
    (hQ : ∀ A pStar, ProbOracleComp.IsQueryBounded (adv.query A pStar) Q) :
    LWE.realGame (PMF.uniformOfFintype (Fin n → ZMod q))
      (encryptLWEErrorLaw W (ProbComp.eval E) Q)
      (encryptRealReduction t Q adv) =
      strongReuseRealGame
        (ProbComp.uniform (Matrix (Fin m) (Fin n) (ZMod q)))
        (lweEncryptFuzzyExtractor m n l q E decode) W t adv := by
  simp only [LWE.realGame, LWE.eval_realExperiment, encryptLWEErrorLaw, encryptRealReduction,
    strongReuseRealGame, Game.withSetup, strongReuseRealExperiment, lweEncryptFuzzyExtractor,
    symEncrypt, ProbComp.eval_uniform, pmf_norm]
  exact realGame_encrypt_embed E decode W t Q adv hQ fun st rStar =>
    ProbComp.eval (adv.guess st rStar)

/-- The real LWE game against `encryptIdealReduction t Q adv` is identically distributed to
the strong-reusability ideal game `strongReuseIdealGame` of `lweEncryptFuzzyExtractor`, for an
adversary that makes at most `Q` shift queries. -/
theorem realGame_encryptIdealReduction {St : Type}
    (E : ProbComp (Fin l → ZMod q))
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (W : PMF (Fin m → ZMod q)) (t Q : ℕ)
    (adv : StrongReuseAdversary (Matrix (Fin m) (Fin n) (ZMod q)) m q
      (Fin l → Bool) (EncryptHelper m n l q) St)
    (hQ : ∀ A pStar, ProbOracleComp.IsQueryBounded (adv.query A pStar) Q) :
    LWE.realGame (PMF.uniformOfFintype (Fin n → ZMod q))
      (encryptLWEErrorLaw W (ProbComp.eval E) Q)
      (encryptIdealReduction t Q adv) =
      strongReuseIdealGame
        (ProbComp.uniform (Matrix (Fin m) (Fin n) (ZMod q)))
        (lweEncryptFuzzyExtractor m n l q E decode) W t adv := by
  simp only [LWE.realGame, LWE.eval_realExperiment, encryptLWEErrorLaw, encryptIdealReduction,
    strongReuseIdealGame, Game.withSetup, strongReuseIdealExperiment, lweEncryptFuzzyExtractor,
    symEncrypt, ProbComp.eval_uniform, pmf_norm]
  exact realGame_encrypt_embed E decode W t Q adv hQ fun st _ =>
    (PMF.uniformOfFintype (Fin l → Bool)).bind fun u => ProbComp.eval (adv.guess st u)

private theorem uniform_mask_encodeHalfBits_eq {l q : ℕ} [NeZero q] {St α : Type}
    (G : (Fin l → ZMod q) → PMF St) (H : St → (Fin l → Bool) → PMF α) :
    ((PMF.uniformOfFintype (Fin l → ZMod q)).bind fun b₁ =>
      (PMF.uniformOfFintype (Fin l → Bool)).bind fun rStar =>
        (G (b₁ + encodeHalfBits q rStar)).bind fun st => H st rStar) =
    ((PMF.uniformOfFintype (Fin l → ZMod q)).bind fun b₁ =>
      (PMF.uniformOfFintype (Fin l → Bool)).bind fun rStar =>
        (G (b₁ + encodeHalfBits q rStar)).bind fun st =>
          (PMF.uniformOfFintype (Fin l → Bool)).bind fun u => H st u) := by
  have hshift (K : St → PMF α) (rStar : Fin l → Bool) :
      ((PMF.uniformOfFintype (Fin l → ZMod q)).bind fun b₁ =>
        (G (b₁ + encodeHalfBits q rStar)).bind K) =
      (PMF.uniformOfFintype (Fin l → ZMod q)).bind fun hStar => (G hStar).bind K :=
    Probability.PMF.uniformOfFintype_bind_equiv (Equiv.addRight (encodeHalfBits q rStar))
      fun hStar => (G hStar).bind K
  pmf_hoist (PMF.uniformOfFintype (Fin l → Bool))
  simp_rw [hshift, PMF.bind_const]

/-- In the uniform-oracle LWE world (`LWE.randomGame`), `b₁` is uniform on `Fin l → ZMod q`
and independent of the rest of the challenge, so `h* = b₁ + encodeHalfBits q r*` information-
theoretically hides `r*`. Consequently, `encryptRealReduction` and `encryptIdealReduction`
induce the exact same random-world distribution ([AponChoEldefrawyKatz2017], Section 5,
p. 12). -/
theorem randomGame_encryptRealReduction_eq_ideal {St : Type}
    (t Q : ℕ)
    (adv : StrongReuseAdversary (Matrix (Fin m) (Fin n) (ZMod q)) m q
      (Fin l → Bool) (EncryptHelper m n l q) St) :
    LWE.randomGame (encryptRealReduction t Q adv) =
      LWE.randomGame (encryptIdealReduction t Q adv) := by
  simp only [LWE.randomGame, LWE.eval_randomExperiment, encryptRealReduction,
    encryptIdealReduction, ProbComp.eval_bind, ProbComp.eval_uniform]
  congr 1 with M : 1
  rw [uniform_bind_splitRows, uniform_bind_splitRows]
  congr 1 with cStar : 1
  simp only [headRows_joinRows, challengeRows_joinRows, queryRows_joinRows]
  pmf_hoist (PMF.uniformOfFintype (Fin Q → Fin l → ZMod q))
  congr 1 with b_vec : 1
  simpa only [PMF.bind_bind] using uniform_mask_encodeHalfBits_eq
    (fun hStar => ProbComp.eval (encryptSimRun t (headMatrixRows M)
      ⟨cStar, challengeMatrixRows M, hStar⟩ adv
      (List.ofFn fun k => (queryMatrixRows M k, b_vec k))))
    (fun st key => ProbComp.eval (adv.guess st key))

/-- A step of the strong-reusability argument of [AponChoEldefrawyKatz2017], Section 5, not the
security claim, which is `stronglyReusable_lweEncryptFuzzyExtractor`: for every biometric source
`W`, encryption error sampler `E`, error bound `t`, and strong-reusability adversary `adv` making
at most `Q` shift queries, the strong-reusability advantage against `lweEncryptFuzzyExtractor` is
bounded by the sum of the decisional LWE advantages of `encryptRealReduction t Q adv` and
`encryptIdealReduction t Q adv` against `(m + (Q + 1) * l)`-sample LWE with uniform secret on
`Fin n → ZMod q` and error distribution `encryptLWEErrorLaw W (ProbComp.eval E) Q`. When `W = χ^m`,
`E = χ^l`, and `l = m`, this corresponds to the paper's `LWE_{n, (t + 2) m, q, χ}`, whose `t` is
the number of oracle calls (our `Q`), not the Hamming bound `t` here. The bound holds for every
adversary with the query bound; the efficiency certificates of the reductions are
`LWEFamily.isPPT_encryptRealReduction` and `LWEFamily.isPPT_encryptIdealReduction`. -/
theorem strongReuseAdvantage_lweEncryptFuzzyExtractor_le {St : Type}
    (E : ProbComp (Fin l → ZMod q))
    (decode : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin n → ZMod q)))
    (W : PMF (Fin m → ZMod q)) (t Q : ℕ)
    (adv : StrongReuseAdversary (Matrix (Fin m) (Fin n) (ZMod q)) m q
      (Fin l → Bool) (EncryptHelper m n l q) St)
    (hQ : ∀ A pStar, ProbOracleComp.IsQueryBounded (adv.query A pStar) Q) :
    strongReuseAdvantage
      (ProbComp.uniform (Matrix (Fin m) (Fin n) (ZMod q)))
      (lweEncryptFuzzyExtractor m n l q E decode) W t adv ≤
      LWE.advantage (PMF.uniformOfFintype (Fin n → ZMod q))
        (encryptLWEErrorLaw W (ProbComp.eval E) Q) (encryptRealReduction t Q adv) +
      LWE.advantage (PMF.uniformOfFintype (Fin n → ZMod q))
        (encryptLWEErrorLaw W (ProbComp.eval E) Q) (encryptIdealReduction t Q adv) := by
  simp only [strongReuseAdvantage, LWE.advantage,
    ← realGame_encryptRealReduction E decode W t Q adv hQ,
    ← realGame_encryptIdealReduction E decode W t Q adv hQ,
    ← randomGame_encryptRealReduction_eq_ideal t Q adv]
  rw [Game.advantage_comm
    (LWE.realGame (PMF.uniformOfFintype (Fin n → ZMod q))
      (encryptLWEErrorLaw W (ProbComp.eval E) Q) (encryptIdealReduction t Q adv))]
  exact Game.advantage_triangle _ _ _

end Cslib.Crypto.FuzzyExtractor

/-! ### Strong reusability against efficient adversaries -/

namespace Cslib.Crypto.FuzzyExtractor

open Probability Turing.MultiTapeTM
open scoped _root_.Matrix

/-- The encoding of a Section 5 helper `⟨c, B, h⟩` at modulus `2 ^ w`: the word `keyWord c` of the
code offset, framed, then the row-major word of `B`, framed, then the word `keyWord h` of the
ciphertext, each residue in `w` binary digits, least significant first
(`encEncryptHelper_apply`). -/
enc_structure encEncryptHelper (m : ℕ) (n : ℕ) (l : ℕ) (w : ℕ) : EncryptHelper m n l (2 ^ w) where
  codeOffset : (LWEFamily.encVector m w), encMatrix : (Cslib.Matrix.encBinary l n w),
  ciphertext : (LWEFamily.encVector l w)

/-- The row of block `k`, entry `i`, of an `(m + (Q + 1) * l)`-row family is `m + l + l * k + i`. -/
private theorem val_rowIndexEquiv_query {m l Q : ℕ} (k : Fin Q) (i : Fin l) :
    (rowIndexEquiv m l Q (Sum.inr (Sum.inr (k, i)))).val = m + l + l * k.val + i.val := by
  simp [rowIndexEquiv, finSumFinEquiv_apply_right, finProdFinEquiv]
  omega

namespace LWEFamily

/-! ### The reductions at every parameter -/

/-- The typed adversary that a word adversary `A` plays at parameter `κ` against the Section 5
scheme: it reads the view `(A, p*)` as `encPair (Cslib.Matrix.encBinary …) (encEncryptHelper …)`,
each leakage `(p, r)` as `encPair (encEncryptHelper …) (encBitString …)` and keys as
`encBitString (l κ)`. -/
private abbrev typedAdversary (m n l w : ℕ → ℕ) (A : WordReuseAdversary) (κ : ℕ) :
    StrongReuseAdversary (_root_.Matrix (Fin (m κ)) (Fin (n κ)) (ZMod (2 ^ w κ))) (m κ)
      (2 ^ w κ) (Fin (l κ) → Bool) (EncryptHelper (m κ) (n κ) (l κ) (2 ^ w κ)) (List Bool) :=
  A.toReuseAdversary (m κ) (w κ)
    (encPair (Cslib.Matrix.encBinary (m κ) (n κ) (w κ)) (encEncryptHelper (m κ) (n κ) (l κ) (w κ)))
    (encPair (encEncryptHelper (m κ) (n κ) (l κ) (w κ)) (encBitString (l κ)))
    (encBitString (l κ)) κ

/-- `encryptRealReduction` at every security parameter: an LWE distinguisher with `n κ` secret
coordinates and `m κ + (Q κ + 1) * l κ` samples. At `κ` it runs the typed adversary that the word
adversary `A` plays, reading the view `(A, p*)` as `encPair (Cslib.Matrix.encBinary …)
(encEncryptHelper …)`, each leakage `(p, r)` as `encPair (encEncryptHelper …) (encBitString …)`
and keys as `encBitString (l κ)`. -/
noncomputable def encryptRealReduction {m n l w : ℕ → ℕ} (t Q : ℕ → ℕ) (A : WordReuseAdversary) :
    LWE.Distinguisher n (fun κ => m κ + (Q κ + 1) * l κ) w := fun κ =>
  FuzzyExtractor.encryptRealReduction (t κ) (Q κ) (typedAdversary m n l w A κ)

/-- `encryptIdealReduction` at every security parameter, with the encodings of
`LWEFamily.encryptRealReduction`. -/
noncomputable def encryptIdealReduction {m n l w : ℕ → ℕ} (t Q : ℕ → ℕ) (A : WordReuseAdversary) :
    LWE.Distinguisher n (fun κ => m κ + (Q κ + 1) * l κ) w := fun κ =>
  FuzzyExtractor.encryptIdealReduction (t κ) (Q κ) (typedAdversary m n l w A κ)

/-! ### The reductions' word programs -/

/-- The word of the matrix block in columns `1, …, n` of rows `offset, …, offset + rows - 1` of a
word of an augmented matrix `[b | M]` with `n + 1` columns, row by row, in `w` bits per entry. -/
private def matrixRowsWord (rows n w : ℕ) (word : List Bool) (offset : ℕ) : List Bool :=
  (List.range rows).flatMap fun i => (List.range n).flatMap fun j =>
    BitString.lowBits w (Cslib.Matrix.binaryEntry (n + 1) w word (offset + i) (j + 1))

/-- The half-modulus residue `⌊2 ^ w / 2⌋` of a key bit `true`, and `0` of `false`. -/
private def halfOf (w : ℕ) (b : Bool) : ℕ :=
  if b then 2 ^ w / 2 else 0

/-- The word of a ciphertext `b + M s' + ⌊2 ^ w / 2⌋ r`: entry `i` reads `b` and `M` from row
`offset + i` of a word of `[b | M]` with `n + 1` columns, `s'` from the coins and `r` from the key
bits, in `w` bits. Missing coins and key bits count as `0` and `false`. -/
private def cipherRowsWord (rows n w : ℕ) (word : List Bool) (offset : ℕ) (coins : List ℕ)
    (key : List Bool) : List Bool :=
  (List.range rows).flatMap fun i =>
    BitString.lowBits w (Cslib.Matrix.binaryEntry (n + 1) w word (offset + i) 0 +
      ((List.range n).map fun j =>
        Cslib.Matrix.binaryEntry (n + 1) w word (offset + i) (j + 1) * coins.getD j 0).sum +
      halfOf w (key.getD i false))

/-- The word of the view `(A, ⟨c*, B, b₁ + ⌊2 ^ w / 2⌋ r*⟩)` that the reductions give the
adversary, from the LWE word `[b | M]` and the key bits of `r*`: `A` and `c*` are rows
`0, …, m - 1` and `B` and `b₁` rows `m, …, m + l - 1`. -/
private def viewWordOf (m n l w : ℕ) (word key : List Bool) : List Bool :=
  encPair encBits (encPair encBits (encPair encBits encBits))
    (matrixRowsWord m n w word 0, cipherRowsWord m n w word 0 [] [], matrixRowsWord l n w word m,
      cipherRowsWord l n w word m [] key)

/-- The word of the leakage `(⟨c* + A s' + δ', B_k, b_k + B_k s' + ⌊2 ^ w / 2⌋ r⟩, r)` that
answers a shift request from block `k`, rows `m + l + l * k, …, m + l + l * k + l - 1` of the LWE
word, with the coins of `s'` and the key bits of `r`. -/
private def leakWordOf (m n l w t k : ℕ) (word : List Bool) (coins : List ℕ)
    (key request : List Bool) : List Bool :=
  encPair (encPair encBits (encPair encBits encBits)) encBits
    ((replyWordOf m n w t word coins request,
      matrixRowsWord l n w word (m + l + l * k),
        cipherRowsWord l n w word (m + l + l * k) coins key),
      key)

/-- The shift oracle of the word programs, whose state is the index `k` of the next unused block:
a request of `m * w` bits is answered by `leakWordOf` from block `k` on fresh coins and key bits,
and moves to block `k + 1`; any other request is answered `[]`. -/
private noncomputable def blockOracle (m n l w t : ℕ) (word : List Bool)
    (request : Unit × List Bool) : StateT ℕ ProbComp (List Bool) := fun k =>
  if request.2.length = m * w then do
    let coins ← OracleComp.replicate n (ProbComp.sampleBinaryNat w)
    let key ← encBitString l <$> ProbComp.uniform (BitString l)
    return (leakWordOf m n l w t k word coins key request.2, k + 1)
  else pure ([], k)

variable {m n l w : ℕ → ℕ}

/-- The query stage of the word programs on an LWE input and the key bits of `r*`. -/
private noncomputable def queryWords (t Q : ℕ → ℕ) (A : WordReuseAdversary)
    (x : LWE.Input n (fun κ => m κ + (Q κ + 1) * l κ) w) (key : List Bool) :
    ProbComp (List Bool) :=
  Prod.fst <$> ((A.query x.secParam (viewWordOf (m x.secParam) (n x.secParam) (l x.secParam)
    (w x.secParam) (Cslib.Matrix.toBinary (LWE.augmentedMatrix x.matrix x.target)) key)).runState
      (blockOracle (m x.secParam) (n x.secParam) (l x.secParam) (w x.secParam) (t x.secParam)
        (Cslib.Matrix.toBinary (LWE.augmentedMatrix x.matrix x.target)))).run 0

/-- The word program of `LWEFamily.encryptRealReduction`. -/
private noncomputable def realWords (t Q : ℕ → ℕ) (A : WordReuseAdversary)
    (x : LWE.Input n (fun κ => m κ + (Q κ + 1) * l κ) w) : Experiment := do
  let key ← encBitString (l x.secParam) <$> ProbComp.uniform (BitString (l x.secParam))
  let state ← queryWords t Q A x key
  A.guess x.secParam state key

/-- The word program of `LWEFamily.encryptIdealReduction`. -/
private noncomputable def idealWords (t Q : ℕ → ℕ) (A : WordReuseAdversary)
    (x : LWE.Input n (fun κ => m κ + (Q κ + 1) * l κ) w) : Experiment := do
  let key ← encBitString (l x.secParam) <$> ProbComp.uniform (BitString (l x.secParam))
  let state ← queryWords t Q A x key
  let u ← encBitString (l x.secParam) <$> ProbComp.uniform (BitString (l x.secParam))
  A.guess x.secParam state u

/-! ### The word programs have the reductions' laws -/

/-- `matrixRowsWord` is the word of the matrix whose entries it reads. -/
private theorem toBinary_eq_matrixRowsWord {rows n w : ℕ}
    (B : _root_.Matrix (Fin rows) (Fin n) (ZMod (2 ^ w))) (word : List Bool) (offset : ℕ)
    (hB : ∀ (i : Fin rows) (j : Fin n),
      (Cslib.Matrix.binaryEntry (n + 1) w word (offset + i.val) (j.val + 1) : ZMod (2 ^ w)) =
        B i j) :
    Cslib.Matrix.toBinary B = matrixRowsWord rows n w word offset := by
  simp only [matrixRowsWord, Cslib.Matrix.toBinary_eq, List.flatMap_def, List.map_range_eq_ofFn,
    BitString.lowBits_eq_ofFn_val, hB]

/-- `halfOf` is the half-modulus encoding `encodeHalfBit`. -/
private theorem natCast_halfOf (w : ℕ) (b : Bool) :
    (halfOf w b : ZMod (2 ^ w)) = encodeHalfBit (2 ^ w) b := by
  cases b <;> simp [halfOf, encodeHalfBit]

/-- `cipherRowsWord` is the word of the ciphertext `b + B x + ⌊2 ^ w / 2⌋ r` whose parts it
reads. -/
private theorem keyWord_eq_cipherRowsWord {rows n w : ℕ} (b : Fin rows → ZMod (2 ^ w))
    (B : _root_.Matrix (Fin rows) (Fin n) (ZMod (2 ^ w))) (x : Fin n → ZMod (2 ^ w))
    (r : Fin rows → Bool) (word : List Bool) (offset : ℕ) (coins : List ℕ) (key : List Bool)
    (hb : ∀ i : Fin rows,
      (Cslib.Matrix.binaryEntry (n + 1) w word (offset + i.val) 0 : ZMod (2 ^ w)) = b i)
    (hB : ∀ (i : Fin rows) (j : Fin n),
      (Cslib.Matrix.binaryEntry (n + 1) w word (offset + i.val) (j.val + 1) : ZMod (2 ^ w)) =
        B i j)
    (hx : ∀ j : Fin n, (coins.getD j.val 0 : ZMod (2 ^ w)) = x j)
    (hr : ∀ i : Fin rows, key.getD i.val false = r i) :
    keyWord (b + B *ᵥ x + encodeHalfBits (2 ^ w) r) =
      cipherRowsWord rows n w word offset coins key := by
  simp only [keyWord, cipherRowsWord, Cslib.Matrix.toBinary_eq, _root_.Matrix.of_apply,
    List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.flatMap_def, List.map_range_eq_ofFn, BitString.lowBits_eq_ofFn_val]
  congr 1
  apply congrArg List.ofFn
  funext i
  congr 2
  funext k
  congr 2
  simp only [Pi.add_apply, Nat.cast_add, Nat.cast_sum, List.sum_ofFn, Nat.cast_mul, hb, hB, hx,
    hr, natCast_halfOf, _root_.Matrix.mulVec, dotProduct, encodeHalfBits]

/-- Row `row` of the word of `[b | M]` reads `b r` in column `0` and `M r j` in column `j + 1`,
where `r` is the row with index `row`. -/
private theorem rowEntries {R n w : ℕ} (M : _root_.Matrix (Fin R) (Fin n) (ZMod (2 ^ w)))
    (b : Fin R → ZMod (2 ^ w)) (r : Fin R) {row : ℕ} (hrow : r.val = row) :
    (Cslib.Matrix.binaryEntry (n + 1) w (Cslib.Matrix.toBinary (LWE.augmentedMatrix M b)) row 0 :
        ZMod (2 ^ w)) = b r ∧
      ∀ j : Fin n, (Cslib.Matrix.binaryEntry (n + 1) w
        (Cslib.Matrix.toBinary (LWE.augmentedMatrix M b)) row (j.val + 1) : ZMod (2 ^ w)) =
          M r j := by
  subst hrow
  exact ⟨LWE.binaryEntry_toBinary_augmentedMatrix_zero M b r,
    LWE.binaryEntry_toBinary_augmentedMatrix_succ M b r⟩

/-- The view word of the reductions is the encoded view `(A, ⟨c*, B, b₁ + ⌊2 ^ w / 2⌋ r*⟩)`. -/
private theorem viewWordOf_eq {m n l Q w : ℕ}
    (M : _root_.Matrix (Fin (m + (Q + 1) * l)) (Fin n) (ZMod (2 ^ w)))
    (b : Fin (m + (Q + 1) * l) → ZMod (2 ^ w)) (r : Fin l → Bool) :
    viewWordOf m n l w (Cslib.Matrix.toBinary (LWE.augmentedMatrix M b)) (List.ofFn r) =
      encPair (Cslib.Matrix.encBinary m n w) (encEncryptHelper m n l w)
        (headMatrixRows M,
          ⟨headRows b, challengeMatrixRows M, challengeRows b + encodeHalfBits (2 ^ w) r⟩) := by
  have hhead (i : Fin m) := rowEntries M b (rowIndexEquiv m l Q (Sum.inl i)) (row := 0 + i.val)
    (by simp [rowIndexEquiv])
  have hchal (i : Fin l) := rowEntries M b (rowIndexEquiv m l Q (Sum.inr (Sum.inl i)))
    (row := m + i.val) (by simp [rowIndexEquiv, finSumFinEquiv_apply_right])
  have hzero : encodeHalfBits (2 ^ w) (fun _ : Fin m => false) = 0 := by
    funext i
    simp [encodeHalfBits, encodeHalfBit]
  have hc := keyWord_eq_cipherRowsWord (headRows b) (headMatrixRows M) 0 (fun _ => false) _ 0 []
    [] (fun i => (hhead i).1) (fun i j => (hhead i).2 j) (by simp) (by simp)
  rw [_root_.Matrix.mulVec_zero, add_zero, hzero, add_zero] at hc
  rw [viewWordOf, ← toBinary_eq_matrixRowsWord (headMatrixRows M) _ 0 fun i j => (hhead i).2 j,
    ← hc, ← toBinary_eq_matrixRowsWord (challengeMatrixRows M) _ m fun i j => (hchal i).2 j,
    ← keyWord_eq_cipherRowsWord (challengeRows b) (challengeMatrixRows M) 0 r _ m [] (List.ofFn r)
      (fun i => (hchal i).1) (fun i j => (hchal i).2 j) (by simp)
      (fun i => List.getD_ofFn r i false)]
  simp only [_root_.Matrix.mulVec_zero, add_zero]
  rfl

/-- The block that `withSampleList` supplies after `k` queries: block `k` of the query rows, or
the zero block once they are used up. -/
private noncomputable def blockAt {m n l Q w : ℕ}
    (M : _root_.Matrix (Fin (m + (Q + 1) * l)) (Fin n) (ZMod (2 ^ w)))
    (b : Fin (m + (Q + 1) * l) → ZMod (2 ^ w)) (k : ℕ) :
    _root_.Matrix (Fin l) (Fin n) (ZMod (2 ^ w)) × (Fin l → ZMod (2 ^ w)) :=
  ((List.ofFn fun k => (queryMatrixRows M k, queryRows b k)).drop k).headD (0, 0)

/-- Rows `m + l + l * k, …, m + l + l * k + l - 1` of the LWE word read `blockAt M b k`, including
the zero block past the end of the word. -/
private theorem blockAt_entries {m n l Q w : ℕ}
    (M : _root_.Matrix (Fin (m + (Q + 1) * l)) (Fin n) (ZMod (2 ^ w)))
    (b : Fin (m + (Q + 1) * l) → ZMod (2 ^ w)) (k : ℕ) :
    (∀ i : Fin l, (Cslib.Matrix.binaryEntry (n + 1) w
      (Cslib.Matrix.toBinary (LWE.augmentedMatrix M b)) (m + l + l * k + i.val) 0 :
        ZMod (2 ^ w)) = (blockAt M b k).2 i) ∧
    (∀ (i : Fin l) (j : Fin n), (Cslib.Matrix.binaryEntry (n + 1) w
      (Cslib.Matrix.toBinary (LWE.augmentedMatrix M b)) (m + l + l * k + i.val) (j.val + 1) :
        ZMod (2 ^ w)) = (blockAt M b k).1 i j) := by
  by_cases hk : k < Q
  · rw [show blockAt M b k = (queryMatrixRows M ⟨k, hk⟩, queryRows b ⟨k, hk⟩) by simp [blockAt, hk]]
    exact ⟨fun i => (rowEntries M b _ (val_rowIndexEquiv_query ⟨k, hk⟩ i)).1,
      fun i j => (rowEntries M b _ (val_rowIndexEquiv_query ⟨k, hk⟩ i)).2 j⟩
  · rw [show blockAt M b k = (0, 0) by simp [blockAt, hk]]
    have hzero (i : Fin l) (j : ℕ) : Cslib.Matrix.binaryEntry (n + 1) w
        (Cslib.Matrix.toBinary (LWE.augmentedMatrix M b)) (m + l + l * k + i.val) j = 0 := by
      apply Cslib.Matrix.binaryEntry_eq_zero_of_length_le
      rw [Cslib.Matrix.length_toBinary]
      have hrow : m + (Q + 1) * l ≤ m + l + l * k + i.val := by
        have := Nat.mul_le_mul_left l (not_lt.mp hk)
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm Q l]; omega
      exact Nat.mul_le_mul_right w
        ((Nat.mul_le_mul_right (n + 1) hrow).trans (Nat.le_add_right _ _))
    exact ⟨fun i => by simp [hzero], fun i j => by simp [hzero]⟩

/-- The leakage word from block `k` is the encoded leakage
`(⟨c* + A x + clampShift t δ, B_k, b_k + B_k x + ⌊2 ^ w / 2⌋ r⟩, r)`. -/
private theorem leakWordOf_eq {m n l Q w : ℕ} (t k : ℕ)
    (M : _root_.Matrix (Fin (m + (Q + 1) * l)) (Fin n) (ZMod (2 ^ w)))
    (b : Fin (m + (Q + 1) * l) → ZMod (2 ^ w)) (x : Fin n → ZMod (2 ^ w)) (r : Fin l → Bool)
    (request : List Bool) :
    leakWordOf m n l w t k (Cslib.Matrix.toBinary (LWE.augmentedMatrix M b))
        (List.ofFn fun j => (x j).val) (List.ofFn r) request =
      encPair (encEncryptHelper m n l w) (encBitString l)
        (⟨headRows b + headMatrixRows M *ᵥ x +
            clampShift t (fun j => Cslib.Matrix.ofBinary 1 m w request 0 j),
          (blockAt M b k).1, (blockAt M b k).2 + (blockAt M b k).1 *ᵥ x +
            encodeHalfBits (2 ^ w) r⟩, r) := by
  have hhead (i : Fin m) := rowEntries M b (rowIndexEquiv m l Q (Sum.inl i)) (row := i.val)
    (by simp [rowIndexEquiv])
  obtain ⟨hb, hB⟩ := blockAt_entries M b k
  rw [leakWordOf, ← keyWord_eq_replyWordOf (headMatrixRows M) (headRows b) t x request _
      (fun i => (hhead i).1) (fun i j => (hhead i).2 j),
    ← toBinary_eq_matrixRowsWord (blockAt M b k).1 _ _ hB,
    ← keyWord_eq_cipherRowsWord (blockAt M b k).2 (blockAt M b k).1 x r _ _ _ _ hb hB
      (fun j => by rw [List.getD_ofFn, ZMod.natCast_zmod_val]) (fun i => List.getD_ofFn r i false)]
  rfl

/-- The query stage of the word programs has the law of `encryptSimRun` on the typed view and the
query blocks of the LWE input. The block index of `blockOracle` stands for the unused suffix of
the blocks that `withSampleList` keeps. -/
private theorem eval_queryWords (t Q : ℕ → ℕ) (A : WordReuseAdversary)
    (x : LWE.Input n (fun κ => m κ + (Q κ + 1) * l κ) w) (r : Fin (l x.secParam) → Bool) :
    ProbComp.eval (queryWords t Q A x (List.ofFn r)) =
      ProbComp.eval (encryptSimRun (t x.secParam) (headMatrixRows x.matrix)
        ⟨headRows x.target, challengeMatrixRows x.matrix,
          challengeRows x.target + encodeHalfBits (2 ^ w x.secParam) r⟩
        (typedAdversary m n l w A x.secParam)
        (List.ofFn fun k => (queryMatrixRows x.matrix k, queryRows x.target k))) := by
  obtain ⟨κ, M, b⟩ := x
  simp only [queryWords, encryptSimRun, typedAdversary, WordReuseAdversary.toReuseAdversary]
  rw [viewWordOf_eq]
  generalize A.query κ _ = P
  set c := shiftCodec (m κ) (w κ)
    (encPair (encEncryptHelper (m κ) (n κ) (l κ) (w κ)) (encBitString (l κ)))
  set blocks := List.ofFn fun k => (queryMatrixRows M k, queryRows b k)
  set O := OracleComp.withSampleList (m := ProbComp) (0, 0) fun x δ =>
    StateT.lift (encryptShiftOracle (t κ) (headMatrixRows M) (headRows b) x.1 x.2 δ)
  have hadapt : (c.adapt P).runState O = P.runState (c.wordOracle O) := c.interpret_adapt _ _ _
  have hstep : ∀ q k,
      (ProbComp.eval ((blockOracle (m κ) (n κ) (l κ) (w κ) (t κ)
        (Cslib.Matrix.toBinary (LWE.augmentedMatrix M b)) q).run k)).map
          (fun (a, k') => (a, ((), blocks.drop k'))) =
        ProbComp.eval ((c.wordOracle O q).run ((), blocks.drop k)) := by
    rintro ⟨⟨⟩, word⟩ k
    by_cases hlen : word.length = m κ * w κ
    · simp only [OracleCodec.wordOracle, c, shiftCodec, hlen, ↓reduceIte, StateT.run_map]
      simp only [blockOracle, StateT.run, hlen, ↓reduceIte, O, OracleComp.withSampleList,
        StateT.lift, encryptShiftOracle, ProbComp.eval_replicate_sampleBinaryNat,
        ProbComp.eval_uniform, pmf_norm]
      congr 1 with x : 1; congr 1 with r' : 1
      rw [encBitString_apply, leakWordOf_eq, List.tail_drop]; rfl
    · simp only [blockOracle, StateT.run, hlen, ↓reduceIte, OracleCodec.wordOracle, c, shiftCodec,
        ProbComp.eval_pure, PMF.pure_map]
      exact (ProbComp.eval_pure _).symm
  have h := ProbOracleComp.runWith_map_state
    (fun q k => ProbComp.eval ((blockOracle (m κ) (n κ) (l κ) (w κ) (t κ)
      (Cslib.Matrix.toBinary (LWE.augmentedMatrix M b)) q).run k))
    (fun q s => ProbComp.eval ((c.wordOracle O q).run s)) (fun k => ((), blocks.drop k)) hstep P 0
  simp only [StateT.run, List.drop_zero] at h
  rw [hadapt]
  simp only [ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbOracleComp.eval_runState]
  rw [← h, PMF.bind_map]; rfl

/-- The word program of `LWEFamily.encryptRealReduction` has its law. -/
private theorem eval_realWords (t Q : ℕ → ℕ) (A : WordReuseAdversary)
    (x : LWE.Input n (fun κ => m κ + (Q κ + 1) * l κ) w) :
    ProbComp.eval (realWords t Q A x) =
      ProbComp.eval (encryptRealReduction t Q A x.secParam x.matrix x.target) := by
  simp only [realWords, encryptRealReduction, FuzzyExtractor.encryptRealReduction,
    ProbComp.eval_uniform, encBitString_apply, pmf_norm]
  congr 1 with r : 1
  rw [eval_queryWords]; rfl

/-- The word program of `LWEFamily.encryptIdealReduction` has its law. -/
private theorem eval_idealWords (t Q : ℕ → ℕ) (A : WordReuseAdversary)
    (x : LWE.Input n (fun κ => m κ + (Q κ + 1) * l κ) w) :
    ProbComp.eval (idealWords t Q A x) =
      ProbComp.eval (encryptIdealReduction t Q A x.secParam x.matrix x.target) := by
  simp only [idealWords, encryptIdealReduction, FuzzyExtractor.encryptIdealReduction,
    ProbComp.eval_uniform, encBitString_apply, pmf_norm]
  congr 1 with r : 1
  rw [eval_queryWords]; rfl

/-! ### Polynomial-time computation of the words -/

attribute [local fun_prop]
  ComputableInPolyTime.uniformBitString LWE.computableInPolyTime_secParam

section PolyTime

open ComputableInPolyTime

variable {α : Type} {input : α ↪ List Bool}

/-- `matrixRowsWord` is computed in polynomial time from polynomial-time inputs. -/
@[local fun_prop]
private theorem computableInPolyTime_matrixRowsWord {rows n w offset : α → ℕ}
    {word : α → List Bool} (hrows : ComputableInPolyTime rows input encUnary)
    (hn : ComputableInPolyTime n input encUnary) (hw : ComputableInPolyTime w input encUnary)
    (hword : ComputableInPolyTime word input encBits)
    (hoffset : ComputableInPolyTime offset input encUnary) :
    ComputableInPolyTime (fun a => matrixRowsWord (rows a) (n a) (w a) (word a) (offset a))
      input encBits := by
  unfold matrixRowsWord
  apply flatMapToBitsWithInput (by polytime)
  apply flatMapToBitsWithInput (by polytime)
  polytime

/-- `cipherRowsWord` is computed in polynomial time from polynomial-time inputs. -/
@[local fun_prop]
private theorem computableInPolyTime_cipherRowsWord {rows n w offset : α → ℕ}
    {word key : α → List Bool} {coins : α → List ℕ}
    (hrows : ComputableInPolyTime rows input encUnary)
    (hn : ComputableInPolyTime n input encUnary) (hw : ComputableInPolyTime w input encUnary)
    (hword : ComputableInPolyTime word input encBits)
    (hoffset : ComputableInPolyTime offset input encUnary)
    (hcoins : ComputableInPolyTime coins input (encList encNat))
    (hkey : ComputableInPolyTime key input encBits) :
    ComputableInPolyTime
      (fun a => cipherRowsWord (rows a) (n a) (w a) (word a) (offset a) (coins a) (key a))
      input encBits := by
  unfold cipherRowsWord halfOf
  apply flatMapToBitsWithInput (by polytime)
  apply bitsLow (by polytime)
  have hsum : ComputableInPolyTime
      (fun p : α × ℕ => ((List.range (n p.1)).map fun j =>
        Cslib.Matrix.binaryEntry (n p.1 + 1) (w p.1) (word p.1) (offset p.1 + p.2) (j + 1) *
          (coins p.1).getD j 0).sum)
      (encPair input encUnary) encNat :=
    (show ComputableInPolyTime List.sum (encList encNat) encNat by fun_prop).comp
      (mapWithInput (encA := encUnary) (by polytime) (by polytime))
  exact binary_add' (binary_add' (by polytime) hsum)
    (ite' (by polytime) (binary_div' (by polytime) (const 2)) (const 0))

/-- `viewWordOf` is computed in polynomial time from polynomial-time inputs. -/
private theorem computableInPolyTime_viewWordOf {m n l w : α → ℕ} {word key : α → List Bool}
    (hm : ComputableInPolyTime m input encUnary) (hn : ComputableInPolyTime n input encUnary)
    (hl : ComputableInPolyTime l input encUnary) (hw : ComputableInPolyTime w input encUnary)
    (hword : ComputableInPolyTime word input encBits)
    (hkey : ComputableInPolyTime key input encBits) :
    ComputableInPolyTime (fun a => viewWordOf (m a) (n a) (l a) (w a) (word a) (key a))
      input encBits := by
  polytime [viewWordOf]

/-- `blockOracle` is strict PPT in the security-parameter inputs and word. -/
private theorem isPPTOn_blockOracle {m n l w t : α → ℕ} {word : α → List Bool}
    (hm : ComputableInPolyTime m input encUnary) (hn : ComputableInPolyTime n input encUnary)
    (hl : ComputableInPolyTime l input encUnary) (hw : ComputableInPolyTime w input encUnary)
    (ht : ComputableInPolyTime t input encUnary)
    (hword : ComputableInPolyTime word input encBits) :
    IsPPTOn (encHandlerCall input (encFinEnum Unit) encUnary) (encPair encBits encUnary)
      fun call : α × (Unit × List Bool) × ℕ =>
        blockOracle (m call.1) (n call.1) (l call.1) (w call.1) (t call.1) (word call.1)
          call.2.1 call.2.2 := by
  unfold blockOracle
  refine (IsPPTOn.ite (by polytime) ?_ (by ppt)).congr fun _ => rfl
  let encKeyed :=
    encPair (encPair (encHandlerCall input (encFinEnum Unit) encUnary) (encList encNat)) encBits
  have hrep := computableInPolyTime_replyWordOf (input := encKeyed)
    (m := fun p => m p.1.1.1) (n := fun p => n p.1.1.1) (w := fun p => w p.1.1.1)
    (t := fun p => t p.1.1.1) (helper := fun p => word p.1.1.1) (coins := fun p => p.1.2)
    (request := fun p => p.1.1.2.1.2)
    (by polytime) (by polytime) (by polytime) (by polytime) (by polytime) (by polytime)
    (by polytime)
  ppt [leakWordOf]

end PolyTime

/-! ### The certificates -/

/-- Every leakage word has `4 m w + 4 l n w + 2 l w + l + 5` bits. -/
private theorem length_leakWordOf_le (m n l w t k : ℕ) (word : List Bool) (coins : List ℕ)
    (r : Fin l → Bool) (request : List Bool) :
    (leakWordOf m n l w t k word coins (List.ofFn r) request).length ≤
      4 * (m * w) + 4 * (l * (n * w)) + 2 * (l * w) + l + 5 := by
  simp only [leakWordOf, encPair_apply, List.length_append, length_frame, encBits_apply,
    replyWordOf, matrixRowsWord, cipherRowsWord, List.length_flatMap, BitString.length_lowBits,
    List.length_ofFn, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  exact le_of_eq (by ring)

/-- The query stage of the word programs is strict PPT in the LWE input and the key word, when
`m, n, l, w, t` are computable in polynomial time in unary and the adversary is uniform strict
oracle PPT. -/
@[local fun_prop]
private theorem isPPTOn_queryWords (hm : ComputableInPolyTime m encUnary encUnary)
    (hn : ComputableInPolyTime n encUnary encUnary)
    (hl : ComputableInPolyTime l encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary)
    {t : ℕ → ℕ} (ht : ComputableInPolyTime t encUnary encUnary) {Q : ℕ → ℕ}
    {A : WordReuseAdversary} (hA : A.IsPPT) :
    IsPPTOn (encPair (LWE.encInput n (fun κ => m κ + (Q κ + 1) * l κ) w) encBits) encBits
      fun p => queryWords t Q A p.1 p.2 := by
  let R : ℕ → ℕ := fun κ => m κ + (Q κ + 1) * l κ
  let encIn := LWE.encInput n R w
  let input := encPair encIn encBits
  let bound (κ : ℕ) := 4 * (m κ * w κ) + 4 * (l κ * (n κ * w κ)) + 2 * (l κ * w κ) + l κ + 5
  have hκ : ComputableInPolyTime (fun p : LWE.Input n R w × List Bool => p.1.secParam)
      input encUnary := by polytime
  have hword := LWE.computableInPolyTime_augmentedWord.comp (ComputableInPolyTime.fst encIn encBits)
  have hview := hκ.prod
    (computableInPolyTime_viewWordOf (hm.comp hκ) (hn.comp hκ) (hl.comp hκ) (hw.comp hκ)
      hword (ComputableInPolyTime.snd encIn encBits))
  have hrun := hA.query.isPPTOn_runState (input := input) (operationEncoding := encFinEnum Unit)
    (stateEncoding := encUnary)
    (oracle := fun p => blockOracle (m p.1.secParam) (n p.1.secParam) (l p.1.secParam)
      (w p.1.secParam) (t p.1.secParam)
      (Cslib.Matrix.toBinary (LWE.augmentedMatrix p.1.matrix p.1.target)))
    (initial := fun _ => 0) (resources := fun p _ => bound p.1.secParam)
    hview ((isPPTOn_blockOracle (hm.comp hκ) (hn.comp hκ) (hl.comp hκ) (hw.comp hκ)
      (ht.comp hκ) hword).congr fun ⟨_, _, _⟩ => rfl)
    (ComputableInPolyTime.const 0) (fun _ _ => True) (fun _ => trivial) (by polytime [bound])
    fun p request k _ result hresult => ⟨trivial, by
      simp only [blockOracle] at hresult
      split_ifs at hresult
      · simp only [ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, ProbComp.eval_uniform,
          PMF.support_bind, PMF.support_map, PMF.support_pure, Set.mem_iUnion, Set.mem_image,
          Set.mem_singleton_iff] at hresult
        obtain ⟨coins, _, key, ⟨r, _, rfl⟩, rfl⟩ := hresult
        have := length_leakWordOf_le (m p.1.secParam) (n p.1.secParam) (l p.1.secParam)
          (w p.1.secParam) (t p.1.secParam) k
          (Cslib.Matrix.toBinary (LWE.augmentedMatrix p.1.matrix p.1.target)) coins r request.2
        simp only [encBitString_apply, encUnary_apply, List.length_replicate, bound]; omega
      · simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hresult
        subst hresult; simp only [List.length_nil, encUnary_apply, List.length_replicate]; omega⟩
  exact (hrun.map (ComputableInPolyTime.fst encBits encUnary)).congr fun _ => rfl

/-- **`LWEFamily.encryptRealReduction` is PPT.** When `m, n, l, w, t` are computable in polynomial
time in unary, the real-key reduction of a uniform strict oracle PPT word adversary is a uniform
strict PPT LWE distinguisher. -/
theorem isPPT_encryptRealReduction (hm : ComputableInPolyTime m encUnary encUnary)
    (hn : ComputableInPolyTime n encUnary encUnary)
    (hl : ComputableInPolyTime l encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary)
    {t : ℕ → ℕ} (ht : ComputableInPolyTime t encUnary encUnary) {Q : ℕ → ℕ}
    {A : WordReuseAdversary} (hA : A.IsPPT) :
    (encryptRealReduction (m := m) (n := n) (l := l) (w := w) t Q A).IsPPT := by
  have hguess := hA.guess
  exact (by ppt [realWords] : IsPPTOn _ _ (realWords t Q A)).congr (eval_realWords t Q A)

/-- **`LWEFamily.encryptIdealReduction` is PPT.** When `m, n, l, w, t` are computable in
polynomial time in unary, the ideal-key reduction of a uniform strict oracle PPT word adversary is
a uniform strict PPT LWE distinguisher. -/
theorem isPPT_encryptIdealReduction (hm : ComputableInPolyTime m encUnary encUnary)
    (hn : ComputableInPolyTime n encUnary encUnary)
    (hl : ComputableInPolyTime l encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary)
    {t : ℕ → ℕ} (ht : ComputableInPolyTime t encUnary encUnary) {Q : ℕ → ℕ}
    {A : WordReuseAdversary} (hA : A.IsPPT) :
    (encryptIdealReduction (m := m) (n := n) (l := l) (w := w) t Q A).IsPPT := by
  have hguess := hA.guess
  exact (by ppt [idealWords] : IsPPTOn _ _ (idealWords t Q A)).congr (eval_idealWords t Q A)

end LWEFamily

/-! ### Strong reusability -/

/-- **Strong reusability of the Section 5 fuzzy extractor** ([AponChoEldefrawyKatz2017],
Section 5, pp. 11–12). Let `m, n, l, w, t` be computable in polynomial time in unary, let `χ κ` be
a law on `ZMod (2 ^ w κ)`, and let the scheme's encryption errors `E κ` have independent
coordinates drawn from `χ κ`. If decision LWE with `n κ` secret coordinates,
`m κ + (Q κ + 1) * l κ` samples, modulus `2 ^ w κ` and error law `χ κ` holds
(`DecisionLWE`), then the family `κ ↦ lweEncryptFuzzyExtractor (m κ) (n κ) (l κ) (2 ^ w κ) (E κ)
(decode κ)`, whose public parameter is a uniform matrix, is `StronglyReusable` for the source
`κ ↦ χ κ ^ m κ`, with shifts of Hamming weight at most `t κ`, against uniform strict oracle PPT
word adversaries that make at most `Q κ` shift queries.

Section 5 states no numbered theorem. It sketches a proof of strong reusability "based on
hardness of the `LWE_{n,(t+2)m,q,χ}` problem, where the adversary makes at most `t` oracle calls
in the experiment of Definition 3" (p. 12), assuming (1) that each coordinate of `w` is drawn
independently from `χ` and (2) that the encryption error has the same law. Here `Q κ` is that
number of calls and `l κ` the key length, which the source takes equal to `m` (p. 11), where the
sample count is `(Q + 2) m`. The premise is `DecisionLWE`, the source's Definition 4 (p. 7) at
modulus `q = 2 ^ w κ`, where Definition 4 allows any integer `q ≥ 2`; at `w κ = 0` the modulus is
`1`, where the real and random games coincide. The reductions are `LWEFamily.encryptRealReduction`
and `LWEFamily.encryptIdealReduction`, which are PPT by `LWEFamily.isPPT_encryptRealReduction` and
`LWEFamily.isPPT_encryptIdealReduction`; the bound is
`strongReuseAdvantage_lweEncryptFuzzyExtractor_le` with the error law `encryptLWEErrorLaw_pi`.

Further deviations: adversaries are uniform strict oracle PPT programs, a shift of Hamming weight
above `t κ` is answered as the shift `0` (`clampShift`), where Definition 3 admits only shifts of
weight at most `t`, and the advantage is the distance between the real and ideal games, twice the
source's `ε` in `1/2 + ε`. Definition 3 is stated for a fuzzy extractor, correctness included;
this theorem concludes only the security half. Section 5 calls correctness immediate "for the same
range of parameters as in the FMR scheme" (p. 12); averaged over the matrix and relative to a
caller-supplied decoder (`DecoderCorrectWithError`, #6040), that step is
`setupCorrect_lweEncryptFuzzyExtractor_of_decoderCorrectWithError`. -/
theorem stronglyReusable_lweEncryptFuzzyExtractor {m n l w : ℕ → ℕ}
    (hm : ComputableInPolyTime m encUnary encUnary)
    (hn : ComputableInPolyTime n encUnary encUnary)
    (hl : ComputableInPolyTime l encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary)
    {t : ℕ → ℕ} (ht : ComputableInPolyTime t encUnary encUnary) (Q : ℕ → ℕ)
    (χ : (κ : ℕ) → PMF (ZMod (2 ^ w κ)))
    (E : (κ : ℕ) → ProbComp (Fin (l κ) → ZMod (2 ^ w κ)))
    (hE : ∀ κ, ProbComp.eval (E κ) = PMF.pi fun _ => χ κ)
    (decode : (κ : ℕ) → _root_.Matrix (Fin (m κ)) (Fin (n κ)) (ZMod (2 ^ w κ)) →
      (Fin (m κ) → ZMod (2 ^ w κ)) → ProbComp (Option (Fin (n κ) → ZMod (2 ^ w κ))))
    (hLWE : DecisionLWE n (fun κ => m κ + (Q κ + 1) * l κ) w χ) :
    StronglyReusable
      (fun κ => ProbComp.uniform (_root_.Matrix (Fin (m κ)) (Fin (n κ)) (ZMod (2 ^ w κ))))
      (fun κ => lweEncryptFuzzyExtractor (m κ) (n κ) (l κ) (2 ^ w κ) (E κ) (decode κ)) t
      {fun κ => PMF.pi fun _ => χ κ}
      (fun κ => encPair (Cslib.Matrix.encBinary (m κ) (n κ) (w κ))
        (encEncryptHelper (m κ) (n κ) (l κ) (w κ)))
      (fun κ => encEncryptHelper (m κ) (n κ) (l κ) (w κ)) (fun κ => encBitString (l κ))
      (fun A => A.IsPPT ∧ ∀ κ view, (A.query κ view).IsQueryBounded (Q κ)) := by
  rintro _ rfl A ⟨hA, hQ⟩
  refine negligible_of_le
    ((hLWE _ (LWEFamily.isPPT_encryptRealReduction hm hn hl hw ht (Q := Q) hA)).add
      (hLWE _ (LWEFamily.isPPT_encryptIdealReduction hm hn hl hw ht (Q := Q) hA))) fun κ => ?_
  have h := strongReuseAdvantage_lweEncryptFuzzyExtractor_le (E κ) (decode κ)
    (PMF.pi fun _ => χ κ) (t κ) (Q κ) (LWEFamily.typedAdversary m n l w A κ)
    fun _ _ => OracleCodec.isQueryBounded_adapt _ (hQ κ _)
  rwa [hE, encryptLWEErrorLaw_pi] at h

end Cslib.Crypto.FuzzyExtractor
