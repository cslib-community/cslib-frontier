/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.Stages
public import CslibFrontier.Foundations.Data.Code.Hadamard
public import CslibFrontier.Foundations.Data.Code.Concatenation
public import CslibFrontier.Foundations.Data.Code.LowDegreeExtension
import CslibFrontier.Foundations.Data.BitString.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# From worst-case to average-case hardness by local list decoding

Let `f` be a Boolean function on `n = m * b` bits. Its *encoding*
(`Cslib.Circuits.Boolean.hardnessEncode`) [SudanTrevisanVadhan2001] is the concatenation of the
Reed–Muller code with the Hadamard code: read `f` as a function on `(BitString b) ^ m`, take its
low-degree extension `p` to `F ^ m` for a field `F` of `q = 2 ^ w` elements containing
`BitString b` (`Cslib.Code.lowDegreeExtension`), a polynomial of total degree at most
`d = m * (2 ^ b - 1)`, and output the parity `enc (p x) ⬝ r` of the `w` bits of `p x` selected by
`r`. The encoding is a Boolean function on `m * w + w` bits (`Cslib.Code.concat` of the extension
with the Hadamard code, `Cslib.Circuits.Boolean.hardnessEncode_append_eq_concat`). Informally,
given the truth table of `f` and the field arithmetic, it is evaluated with `2 ^ n` terms of the
extension, in time `2 ^ O(n)`; this module formalizes no running time.

**The reconstruction theorem** (`Cslib.Circuits.Boolean.complexity_le_of_agree_hardnessEncode`):
if a circuit of size `s` agrees with the encoding of `f` on a `1 / 2 + ε` fraction of its inputs,
then `f` has a circuit of size at most `reconstructionCost`, an explicit polynomial in `s`, `q`,
`2 ^ K`, `3 ^ L`, `2 ^ b` and the number of monomials `M ≤ (D + 1) ^ 2` used by Sudan decoding,
for parameters `K`, `L`, `D` satisfying explicit inequalities. The circuit for `f` is built in
four stages, each querying the previous one:

1. Goldreich–Levin decoding of the inner code, with fixed masks and guess, gives a function
   `G : F ^ m → F` that agrees with `p` on at least an `ε / 2 ^ (K + 2)` fraction of `F ^ m`
   (`Cslib.Circuits.Boolean.exists_glPredictor_agree`).
2. Local list decoding along lines with advice (`Cslib.Code.lineListDecode`) gives a function
   that computes `p` at all but a small fraction of the points
   (`Cslib.Code.exists_card_lineListDecode_ne_le`).
3. Self-correction by interpolation along lines and majority trees computes `p` at every point of
   the grid `h (BitString b) ^ m` (`Cslib.exists_forall_majTree_eq`).
4. Reading off `f` from the value of `p` on the grid.

The stages are bit-blasted De Morgan circuits whose costs are bounded by
`Cslib.Circuits.Boolean.bitSynthesis_glPredictor`,
`Cslib.Circuits.Boolean.BitSynthesis.lineListDecode` and
`Cslib.Circuits.Boolean.BitSynthesis.selfCorrect`. In the ranges forced by the hypotheses the
reconstruction cost is at most `2 ^ 11 * 3 ^ L * m * w ^ 2 * q ^ 9 * 4 ^ K * (s + 1)`
(`Cslib.Circuits.Boolean.reconstructionCost_le`,
`Cslib.Circuits.Boolean.complexity_le_pow_of_agree_hardnessEncode`). Informally (none of the
following asymptotics is formalized here), the smallest admissible parameters have
`2 ^ K = O(w / ε ^ 2)`, `3 ^ L = O((m * b) ^ (log₂ 3))`, `D = O(√(d * q))` and
`q = poly(d, w, 1 / ε)`, so for a block length `b = Θ(log (n / ε))` the reconstructed circuit has
size polynomial in `s`, `n` and `1 / ε`, and the encoding has `O(n + log (1 / ε))` input bits when
`m = n / b`.

The theorem is nonuniform: the masks and guess of the Goldreich–Levin stage, the advice point of
the line stage and the directions of the self-correction stage are fixed by counting arguments, and
the circuits are obtained from synthesis bounds rather than constructed by an algorithm. Membership
of the encoding in `E` for `f` in `E`, and the derandomization of `BPP` from worst-case hardness,
are separate steps.

## Main definitions

* `Cslib.Circuits.Boolean.truthTableExtension`: the low-degree extension of a truth table.
* `Cslib.Circuits.Boolean.hardnessEncode`: the encoding.
* `Cslib.Circuits.Boolean.reconstructionCost`: the size of the reconstructed circuit.

## Main results

* `Cslib.Circuits.Boolean.exists_glPredictor_agree`: the Goldreich–Levin stage.
* `Cslib.Circuits.Boolean.complexity_le_of_agree_hardnessEncode`: **the reconstruction theorem**.
* `Cslib.Circuits.Boolean.reconstructionCost_le`: the reconstruction cost is at most
  `2 ^ 11 * 3 ^ L * m * w ^ 2 * q ^ 9 * 4 ^ K * (s + 1)`.
* `Cslib.Circuits.Boolean.complexity_le_pow_of_agree_hardnessEncode`: the reconstruction theorem
  with this polynomial bound.

## References

* [M. Sudan, L. Trevisan, S. Vadhan, *Pseudorandom generators without the XOR lemma*]
  [SudanTrevisanVadhan2001]
* [R. Impagliazzo, A. Wigderson, *P = BPP if E requires exponential circuits: Derandomizing the
  XOR lemma*][ImpagliazzoWigderson1997]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 19
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Finset Cslib.Code

variable {F : Type*} {w m b : ℕ}

/-! ### The encoding -/

variable [Field F]

/-- The low-degree extension of the truth table of `f`, read as a function on `(BitString b) ^ m`
with values `0` and `1`: a codeword of the Reed–Muller code of degree `m * (2 ^ b - 1)`. -/
noncomputable def truthTableExtension (h : BitString b ↪ F) (f : BooleanFunction (m * b)) :
    (Fin m → F) → F :=
  lowDegreeExtension h fun u => if f (BitString.blocksEquiv.symm u) then 1 else 0

/-- The extension of a truth table on `(BitString b) ^ m` is a codeword of the Reed–Muller code of
degree `m * (2 ^ b - 1)`. -/
theorem truthTableExtension_mem_reedMuller (h : BitString b ↪ F) (f : BooleanFunction (m * b)) :
    truthTableExtension h f ∈ reedMuller F m (m * (2 ^ b - 1)) := by
  have := lowDegreeExtension_mem_reedMuller h fun u =>
    if f (BitString.blocksEquiv.symm u) then (1 : F) else 0
  rw [BitString.card] at this
  exact this

/-- On the grid, the extension of a truth table is the truth table: at the point whose coordinates
embed the blocks of `x`, it is `1` if `f x` and `0` otherwise. -/
theorem truthTableExtension_block (h : BitString b ↪ F) (f : BooleanFunction (m * b))
    (x : BitString (m * b)) :
    truthTableExtension h f (fun i => h (BitString.block x i)) = if f x then 1 else 0 := by
  rw [truthTableExtension, lowDegreeExtension_apply_embed, BitString.blocksEquiv_symm_block]

/-- **The worst-case-to-average-case encoding** [SudanTrevisanVadhan2001]. On an input of
`m * w + w` bits, read the first `m * w` bits as a point `x` of `F ^ m` and the last `w` bits as
`r`, and output the parity `enc (p x) ⬝ r` of the bits of `p x = truthTableExtension h f x`
selected by `r`. -/
noncomputable def hardnessEncode (enc : F ≃ BitString w) (h : BitString b ↪ F)
    (f : BooleanFunction (m * b)) : BooleanFunction (m * w + w) :=
  fun y => enc (truthTableExtension h f
    ((BitString.pointEquiv enc).symm fun i => y (Fin.castAdd w i))) ⬝ᵥ
    fun j => y (Fin.natAdd (m * w) j)

/-- The encoding at the input `(x, r)` is the parity of the bits of `p x` selected by `r`. -/
@[simp]
theorem hardnessEncode_append (enc : F ≃ BitString w) (h : BitString b ↪ F)
    (f : BooleanFunction (m * b)) (x : BitString (m * w)) (r : BitString w) :
    hardnessEncode enc h f (Fin.append x r) =
      enc (truthTableExtension h f ((BitString.pointEquiv enc).symm x)) ⬝ᵥ r := by
  simp only [hardnessEncode, Fin.append_left, Fin.append_right]

/-- **The encoding is a concatenated code** (`Cslib.Code.concat`): the outer word is the
extension of the truth table, read at the point with bits `x`, and the inner code is the Hadamard
code (`Cslib.BitString.hadamardCode`) of the bits of the field element. -/
theorem hardnessEncode_append_eq_concat (enc : F ≃ BitString w) (h : BitString b ↪ F)
    (f : BooleanFunction (m * b)) (x : BitString (m * w)) (r : BitString w) :
    hardnessEncode enc h f (Fin.append x r) =
      Code.concat (fun a => BitString.hadamardCode (enc a)) (truthTableExtension h f)
        ((BitString.pointEquiv enc).symm x, r) := by
  rw [hardnessEncode_append, Code.concat_apply, BitString.hadamardCode_apply]

/-! ### The Goldreich–Levin stage -/

/-- A fraction of agreement is at most one: agreement on a `1 / 2 + ε` fraction forces
`ε ≤ 1 / 2`. -/
private theorem le_half_of_agree {N : ℕ} {C E : BooleanFunction N} {ε : ℝ}
    (hagree : (1 / 2 + ε) * 2 ^ N ≤ #{y | C y = E y}) : ε ≤ 1 / 2 := by
  have hN : (#{y | C y = E y} : ℝ) ≤ 2 ^ N := by
    have := card_le_univ (univ.filter fun y : BitString N => C y = E y)
    rw [BitString.card] at this
    exact_mod_cast this
  have hpos : (0 : ℝ) < 2 ^ N := by positivity
  have h1 : (1 / 2 + ε) * 2 ^ N ≤ 1 * 2 ^ N := hagree.trans (by linarith only [hN])
  linarith only [le_of_mul_le_mul_right h1 hpos]

variable [Fintype F] [DecidableEq F]

/-- **The Goldreich–Levin stage.** If `C` agrees with the encoding of `f` on a `1 / 2 + ε`
fraction of the inputs and `w ≤ 2 * (ε / 2) ^ 2 * (2 ^ K - 1)` with `K ≥ 1`, then for some masks
and guess the Goldreich–Levin decoder agrees with the extension of `f` on at least
`ε * 2 ^ (m * w) / 2 ^ (K + 2)` points of `F ^ m`. -/
theorem exists_glPredictor_agree (enc : F ≃ BitString w) (h : BitString b ↪ F)
    (f : BooleanFunction (m * b)) (C : BooleanFunction (m * w + w)) {ε : ℝ} (hε : 0 < ε)
    (hagree : (1 / 2 + ε) * 2 ^ (m * w + w) ≤ #{y | C y = hardnessEncode enc h f y})
    {K : ℕ} (hK : 0 < K) (hsize : (w : ℝ) ≤ 2 * (ε / 2) ^ 2 * (2 ^ K - 1 : ℕ)) :
    ∃ (masks : Fin K → BitString w) (guess : BitString K),
      ε * 2 ^ (m * w) ≤
        2 ^ (K + 2) * #{x | glPredictor enc C masks guess x = truthTableExtension h f x} := by
  classical
  set p := truthTableExtension h f
  let pred : BitString (m * w) → BitString w → Bool := fun x r => C (Fin.append x r)
  let target : BitString (m * w) → BitString w :=
    fun x => enc (p ((BitString.pointEquiv enc).symm x))
  -- the agreement as a count of pairs
  have hpairs : #{y | C y = hardnessEncode enc h f y} =
      #{xr : BitString (m * w) × BitString w | pred xr.1 xr.2 = target xr.1 ⬝ᵥ xr.2} :=
    card_equiv (Fin.appendEquiv (m * w) w).symm fun y => by
      simp [pred, target, p, Fin.append_castAdd_natAdd, -hardnessEncode_append,
        ← hardnessEncode_append]
  have hcard : (Fintype.card (BitString (m * w)) : ℝ) = 2 ^ (m * w) := by
    rw [BitString.card, Nat.cast_pow, Nat.cast_ofNat]
  -- many points are good
  set good := (univ : Finset (BitString (m * w))).filter fun x =>
    1 / 2 + ε / 2 ≤ Crypto.GoldreichLevin.agreement (pred x) (target x)
  have hgood : ε / 2 * 2 ^ (m * w) ≤ #good := by
    have hcount := Crypto.GoldreichLevin.card_filter_agreement_ge pred target hε.le (by
      rw [← hpairs, hcard, ← mul_assoc, mul_assoc (1 / 2 + ε), ← pow_add]
      exact hagree)
    rwa [hcard] at hcount
  -- Goldreich–Levin with fixed masks and guess
  obtain ⟨masks, guess, hgl⟩ := Crypto.GoldreichLevin.exists_card_candidate_eq pred target
    (ε / 2) (by positivity) hK hsize good fun x hx => (mem_filter.1 hx).2
  refine ⟨masks, guess, ?_⟩
  have hcount : #{x | glPredictor enc C masks guess x = p x} =
      #{x | Crypto.GoldreichLevin.candidate (pred x) masks guess = target x} := by
    refine card_nbij' (BitString.pointBits enc) (BitString.pointEquiv enc).symm
      (fun x hx => ?_) (fun x hx => ?_)
      (fun x _ => BitString.pointEquiv_symm_pointBits enc x)
      (fun x _ => BitString.pointBits_pointEquiv_symm enc x)
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
      simp only [target, BitString.pointEquiv_symm_pointBits, ← hx, glPredictor,
        Equiv.apply_symm_apply]
      rfl
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
      simp only [glPredictor]
      rw [show (fun r => C (Fin.append (BitString.pointBits enc
          ((BitString.pointEquiv enc).symm x)) r)) = pred x by
        rw [BitString.pointBits_pointEquiv_symm]]
      rw [hx, Equiv.symm_apply_apply]
  rw [hcount]
  have : (#good : ℝ) ≤ 2 ^ (K + 1) *
      #{x | Crypto.GoldreichLevin.candidate (pred x) masks guess = target x} := by
    exact_mod_cast hgl
  calc ε * 2 ^ (m * w) = 2 * (ε / 2 * 2 ^ (m * w)) := by ring
    _ ≤ 2 * #good := by linarith
    _ ≤ 2 * (2 ^ (K + 1) *
        #{x | Crypto.GoldreichLevin.candidate (pred x) masks guess = target x}) := by linarith
    _ = _ := by ring

/-! ### The reconstruction theorem -/

/-- The size of the circuit reconstructed from a predictor of size `s` for the encoding, with
`K` masks, Sudan parameter `D` with `M` monomials, majority trees of depth `L` and a field of `q`
elements: reading the grid point from the input, the self-correction stage over the line stage
over the Goldreich–Levin stage, and reading off `f` from the value of the extension. -/
def reconstructionCost (w b m D K L s q M : ℕ) : ℕ :=
  m * w * (2 ^ b * (2 * b + 2) + 1) +
    selfCorrectCost w m (m * (2 ^ b - 1)) L
      (lineCost w q m M (D / (m * (2 ^ b - 1))) (m * (2 ^ b - 1)) (glCost w K s)) +
    (2 ^ w * (2 * w + 2) + 1)

/-- The agreement margin makes the mean agreement `q * a / Q` of a line at least `2 * D`. -/
private theorem two_mul_mul_le {q Q a ε D : ℝ} (hq : 0 ≤ q) (hQ : 0 ≤ Q) {K : ℕ}
    (hgl : ε * Q ≤ 2 ^ (K + 2) * a) (hmargin : 2 ^ (K + 3) * D ≤ q * ε) : 2 * D * Q ≤ q * a := by
  refine le_of_mul_le_mul_left (a := (2 : ℝ) ^ (K + 2)) ?_ (by positivity)
  calc 2 ^ (K + 2) * (2 * D * Q) = 2 ^ (K + 3) * D * Q := by ring
    _ ≤ q * ε * Q := mul_le_mul_of_nonneg_right hmargin hQ
    _ = q * (ε * Q) := by ring
    _ ≤ q * (2 ^ (K + 2) * a) := mul_le_mul_of_nonneg_left hgl hq
    _ = 2 ^ (K + 2) * (q * a) := by ring

/-- The number of errors left by the line stage, bounded in terms of the agreement margin. -/
private theorem lineErrors_le {q Q a ε D δ : ℝ} (hq : 1 < q) (hQ : 1 ≤ Q) (ha : 0 < a)
    (hε : 0 < ε) {K : ℕ} (hgl : ε * Q ≤ 2 ^ (K + 2) * a) (_hD : 0 ≤ D)
    (hmargin : 2 ^ (K + 3) * D ≤ q * ε) (hδ : 0 ≤ δ) (hδD : δ ≤ D) :
    1 + (q * a * (Q - 1) / (q * a / Q - D) ^ 2 + Q * (Q - 1) * δ / (q - 1)) / Q ≤
      Q * (1 / Q + 2 ^ (K + 4) / (q * ε) + D / (q - 1)) := by
  have hQpos : 0 < Q := by linarith
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q - 1 := by linarith
  set μ := q * a / Q
  have hμpos : 0 < μ := by positivity
  -- the mean is at least twice `D`
  have hμ : 2 * D ≤ μ := (le_div_iff₀ hQpos).2 (two_mul_mul_le hq0.le hQpos.le hgl hmargin)
  have hμD : μ / 2 ≤ μ - D := by linarith only [hμ]
  have hsq : μ ^ 2 / 4 ≤ (μ - D) ^ 2 := by
    simpa only [div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using
      pow_le_pow_left₀ (by positivity) hμD 2
  -- the first term
  have hterm1 : q * a * (Q - 1) / (μ - D) ^ 2 / Q ≤ Q * (2 ^ (K + 4) / (q * ε)) := by
    have hμD' : 0 < μ - D := by linarith only [hμpos, hμD]
    rw [div_div, div_le_iff₀ (by positivity)]
    have hμsq : μ ^ 2 * Q ^ 2 = (q * a) ^ 2 := by
      simp only [μ]
      field_simp
    have key : q * a * (Q - 1) ≤ q * a * Q :=
      mul_le_mul_of_nonneg_left (by linarith only [hQ]) (by positivity)
    have hstep : q * a * Q * 4 ≤ Q * (2 ^ (K + 4) / (q * ε)) * (μ ^ 2 * Q) := by
      rw [show Q * (2 ^ (K + 4) / (q * ε)) * (μ ^ 2 * Q) = 2 ^ (K + 4) * (μ ^ 2 * Q ^ 2) /
        (q * ε) by field_simp, hμsq, le_div_iff₀ (by positivity)]
      calc q * a * Q * 4 * (q * ε) = 4 * q * (q * a) * (ε * Q) := by ring
        _ ≤ 4 * q * (q * a) * (2 ^ (K + 2) * a) :=
            mul_le_mul_of_nonneg_left hgl (by positivity)
        _ = 2 ^ (K + 4) * (q * a) ^ 2 := by ring
    calc q * a * (Q - 1) ≤ q * a * Q := key
      _ = q * a * Q * 4 / 4 := by ring
      _ ≤ Q * (2 ^ (K + 4) / (q * ε)) * (μ ^ 2 * Q) / 4 := by gcongr
      _ = Q * (2 ^ (K + 4) / (q * ε)) * (μ ^ 2 / 4 * Q) := by ring
      _ ≤ Q * (2 ^ (K + 4) / (q * ε)) * ((μ - D) ^ 2 * Q) := by gcongr
  -- the second term
  have hterm2 : Q * (Q - 1) * δ / (q - 1) / Q ≤ Q * (D / (q - 1)) := by
    rw [div_div, div_le_iff₀ (by positivity)]
    have : Q * (Q - 1) * δ ≤ Q * Q * D :=
      by gcongr; linarith only [hQ]
    calc Q * (Q - 1) * δ ≤ Q * Q * D := this
      _ = Q * (D / (q - 1)) * ((q - 1) * Q) := by field_simp
  rw [add_div]
  calc 1 + (q * a * (Q - 1) / (μ - D) ^ 2 / Q + Q * (Q - 1) * δ / (q - 1) / Q)
      ≤ 1 + (Q * (2 ^ (K + 4) / (q * ε)) + Q * (D / (q - 1))) := by linarith only [hterm1, hterm2]
    _ = Q * (1 / Q + 2 ^ (K + 4) / (q * ε) + D / (q - 1)) := by
        field_simp
        ring

/-- The ranges of the parameters forced by the hypotheses of the reconstruction theorem: the
Sudan parameter `D` is positive and below `q`, and `d + 1 ≤ q - 1`, so there are `d + 1` distinct
nonzero interpolation nodes. -/
private theorem reconstruction_ranges {q d D K m : ℕ} {ε : ℝ} (hq2 : 2 ≤ q) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 2) (hn : q < #(Sudan.monomials d D))
    (hmargin : (2 : ℝ) ^ (K + 3) * D ≤ q * ε)
    (herr : 6 * ((d : ℝ) + 1) * (1 / (q : ℝ) ^ m + 2 ^ (K + 4) / (q * ε) + D / (q - 1)) ≤ 1) :
    1 ≤ D ∧ D < q ∧ d + 1 ≤ q - 1 := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq2
  have hD1 : 1 ≤ D := by
    by_contra! hD0
    have : #(Sudan.monomials d D) ≤ 1 := card_le_one.2 fun x hx y hy => by
      rw [Sudan.mem_monomials] at hx hy
      ext <;> omega
    omega
  have hDq : D < q := by
    have hqε : (q : ℝ) * ε ≤ q / 2 := by
      linarith only [mul_le_mul_of_nonneg_left hε1 (by linarith only [hq1] : (0 : ℝ) ≤ q)]
    have h8 : (8 : ℝ) ≤ 2 ^ (K + 3) := by
      calc (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (K + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h8D : 8 * (D : ℝ) ≤ q / 2 :=
      (mul_le_mul_of_nonneg_right h8 (Nat.cast_nonneg D)).trans (hmargin.trans hqε)
    have : (D : ℝ) < q := by linarith only [h8D, hq1]
    exact_mod_cast this
  refine ⟨hD1, hDq, ?_⟩
  have h6 : 6 * ((d : ℝ) + 1) * (D / (q - 1)) ≤ 1 := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity)) herr
    have h1 : (0 : ℝ) ≤ 1 / (q : ℝ) ^ m := by positivity
    have h2 : (0 : ℝ) ≤ 2 ^ (K + 4) / (q * ε) := by positivity
    linarith only [h1, h2]
  have h6' : 6 * ((d : ℝ) + 1) * D ≤ q - 1 := by
    rwa [mul_div_assoc', div_le_one (by linarith only [hq1])] at h6
  have hD1' : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hle : ((d : ℝ) + 1) ≤ q - 1 := by
    linarith only [h6', le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ 6 * ((d : ℝ) + 1)) hD1',
      hd0]
  have : ((d + 1 : ℕ) : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    exact hle
  exact_mod_cast this

omit [DecidableEq F] in
/-- **The reconstruction theorem** [SudanTrevisanVadhan2001]. Let `F` be a field of `q` elements
with an encoding `enc : F ≃ BitString w`, let `h : BitString b ↪ F`, let `f` be a Boolean
function on `m * b` bits, and let `d = m * (2 ^ b - 1) ≥ 1`. Suppose a Boolean function `C` with a
De Morgan circuit of size at most `s` agrees with the encoding `hardnessEncode enc h f` on a
`1 / 2 + ε` fraction of its `2 ^ (m * w + w)` inputs. Let the parameters `K ≥ 1`, `D` and `L`
satisfy
* `w ≤ 2 * (ε / 2) ^ 2 * (2 ^ K - 1)` (Goldreich–Levin decoding),
* `q < #(Sudan.monomials d D)` (more monomials of `(1, d)`-weighted degree at most `D` than
  points on a line; this holds when `2 * d * q < (D + 1) * (D + 2)`),
* `2 ^ (K + 3) * D ≤ q * ε` (lines have more than `D` agreements on average),
* `6 * (d + 1) * (1 / q ^ m + 2 ^ (K + 4) / (q * ε) + D / (q - 1)) ≤ 1` (few errors are left for
  self-correction), and
* `m * b ≤ 2 ^ L` (majority trees of depth `L` correct all `2 ^ (m * b)` grid points).

Then `f` has a De Morgan circuit with at most
`reconstructionCost w b m D K L s q (#(Sudan.monomials d D))` gates. -/
theorem complexity_le_of_agree_hardnessEncode (enc : F ≃ BitString w) (h : BitString b ↪ F)
    (f : BooleanFunction (m * b)) {C : BooleanFunction (m * w + w)} {s : ℕ}
    (hC : complexity interpretation (single C) ≤ s) {ε : ℝ} (hε : 0 < ε)
    (hagree : (1 / 2 + ε) * 2 ^ (m * w + w) ≤ #{y | C y = hardnessEncode enc h f y})
    {K D L : ℕ} (hK : 0 < K) (hsize : (w : ℝ) ≤ 2 * (ε / 2) ^ 2 * (2 ^ K - 1 : ℕ))
    (hd : 1 ≤ m * (2 ^ b - 1))
    (hn : Fintype.card F < #(Sudan.monomials (m * (2 ^ b - 1)) D))
    (hmargin : (2 : ℝ) ^ (K + 3) * D ≤ Fintype.card F * ε)
    (herr : 6 * ((m * (2 ^ b - 1) : ℕ) + 1 : ℝ) * (1 / (Fintype.card F : ℝ) ^ m +
      2 ^ (K + 4) / (Fintype.card F * ε) + D / (Fintype.card F - 1)) ≤ 1)
    (hL : m * b ≤ 2 ^ L) :
    complexity interpretation (single f) ≤
      reconstructionCost w b m D K L s (Fintype.card F)
        #(Sudan.monomials (m * (2 ^ b - 1)) D) := by
  classical
  set d := m * (2 ^ b - 1) with hd_def
  set q := Fintype.card F with hq_def
  set p := truthTableExtension h f
  have hp : p ∈ reedMuller F m d := truthTableExtension_mem_reedMuller h f
  have hqw : q = 2 ^ w := by
    rw [hq_def, Fintype.card_congr enc, BitString.card]
  have hQnat : Fintype.card (Fin m → F) = 2 ^ (m * w) := by
    rw [Fintype.card_fun, Fintype.card_fin, ← hq_def, hqw, ← pow_mul, mul_comm]
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq2
  -- the Goldreich–Levin stage
  obtain ⟨masks, guess, hgl⟩ := exists_glPredictor_agree enc h f C hε hagree hK hsize
  set G := glPredictor enc C masks guess
  -- the parameters
  have hε1 : ε ≤ 1 / 2 := le_half_of_agree hagree
  obtain ⟨hD1, hDq, hdq⟩ := reconstruction_ranges hq2 hε hε1 hn hmargin herr
  set Q : ℝ := (q : ℝ) ^ m with hQ_def
  have hQ : (Fintype.card (Fin m → F) : ℝ) = Q := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    rfl
  have hQ2 : (2 : ℝ) ^ (m * w) = Q := by
    rw [hQ_def, hqw]
    push_cast
    rw [← pow_mul, mul_comm]
  have hQ1 : (1 : ℝ) ≤ Q := one_le_pow₀ hq1.le
  set a := (#{x | G x = p x} : ℕ)
  have ha : ε * Q ≤ 2 ^ (K + 2) * a := by rw [← hQ2]; exact hgl
  have hapos : (0 : ℝ) < a :=
    pos_of_mul_pos_right ((by positivity : (0 : ℝ) < ε * Q).trans_le ha) (by positivity)
  -- the line stage
  have hμ : (D : ℝ) < q * #{y | G y = p y} / q ^ m := by
    rw [lt_div_iff₀ (by positivity)]
    have hD1' : (1 : ℝ) ≤ D := by exact_mod_cast hD1
    linarith only [two_mul_mul_le (Nat.cast_nonneg q) (by linarith only [hQ1]) ha hmargin,
      one_le_mul_of_one_le_of_one_le hD1' hQ1]
  obtain ⟨z, hz⟩ := exists_card_lineListDecode_ne_le hd hn hDq hp G hμ
  set C1 := lineListDecode G d D z (p z)
  have herrC1 : ((d : ℝ) + 1) * #{x | C1 x ≠ p x} ≤ Q / 6 := by
    have hbound := lineErrors_le (q := q) (Q := Q) (a := a) (ε := ε) (D := D)
      (δ := ((D - d : ℕ) : ℝ)) hq1 hQ1 hapos hε ha (by positivity) hmargin (by positivity)
      (by exact_mod_cast Nat.sub_le D d)
    calc ((d : ℝ) + 1) * #{x | C1 x ≠ p x} ≤
          ((d : ℝ) + 1) * (Q * (1 / Q + 2 ^ (K + 4) / (q * ε) + D / (q - 1))) := by
          gcongr; exact hz.trans hbound
      _ = Q / 6 * (6 * ((d : ℝ) + 1) * (1 / Q + 2 ^ (K + 4) / (q * ε) + D / (q - 1))) := by
          ring
      _ ≤ Q / 6 := mul_le_of_le_one_right (by positivity) herr
  -- the interpolation nodes
  have hdq' : d + 2 ≤ Fintype.card F := by
    have := Fintype.one_lt_card (α := F)
    omega
  let ν : Fin (d + 1) ↪ F := nonzeroNodes hdq'
  have hν : ∀ i, ν i ≠ 0 := nonzeroNodes_ne_zero hdq'
  -- the self-correction stage
  let grid : Finset (Fin m → F) :=
    univ.image fun x : BitString (m * b) => fun i => h (BitString.block x i)
  have hgrid : #grid ≤ 2 ^ (2 ^ L) := by
    calc #grid ≤ #(univ : Finset (BitString (m * b))) := card_image_le
      _ = 2 ^ (m * b) := by rw [card_univ, BitString.card]
      _ ≤ 2 ^ (2 ^ L) := Nat.pow_le_pow_right (by decide) hL
  obtain ⟨V, hV⟩ := exists_forall_majTree_eq (α := F) (Ω := Fin m → F) grid
    (fun x v => lagrangeDecode ν C1 x v) p (ρ := 1 / 6) (fun x _ => by
      have := card_lagrangeDecode_ne_le ν hν hp C1 x
      rw [hQ]
      calc (#{v | lagrangeDecode ν C1 x v ≠ p x} : ℝ) ≤ ((d + 1) * #{y | C1 y ≠ p y} : ℕ) := by
            exact_mod_cast this
        _ = ((d : ℝ) + 1) * #{y | C1 y ≠ p y} := by push_cast; ring
        _ ≤ Q / 6 := herrC1
        _ = 1 / 6 * Q := by ring) (by norm_num) hgrid
  -- the circuits
  have hU := ((bitSynthesis_glPredictor enc hC masks guess).lineListDecode d D z (p z)).selfCorrect
    ν V
  -- the grid point
  let gp : Fin m → (Fin (m * b) → Bool) → F := fun i x => h (BitString.block x i)
  have hemb : Synthesis interpretation (inputs (m * b))
      (Set.range fun ij : Fin m × Fin w => bitsOf enc (gp ij.1) ij.2)
      (m * w * (2 ^ b * (2 * b + 2) + 1)) := by
    have := Synthesis.family (I := interpretation) (s := inputs (m * b))
      (fun ij : Fin m × Fin w => bitsOf enc (gp ij.1) ij.2) (fun _ => 2 ^ b * (2 * b + 2) + 1)
      (fun ij => Synthesis.selected (fun l => finProdFinEquiv (ij.1, l))
        (fun y => enc (h y) ij.2))
    simpa only [Finset.sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul,
      mul_assoc] using this
  set T₁ := Set.range fun ij : Fin m × Fin w => bitsOf enc (gp ij.1) ij.2
  have hUs := hU (m * b) (inputs (m * b) ∪ T₁) gp fun i j =>
    Set.mem_union_right _ ⟨(i, j), rfl⟩
  set U : (Fin m → F) → F := fun x => majTree L fun τ => lagrangeDecode ν C1 x (V τ)
  set T₂ := Set.range fun j => bitsOf enc (fun v => U fun i => gp i v) j
  -- reading off `f`
  have hout : Synthesis interpretation ((inputs (m * b) ∪ T₁) ∪ T₂) {f}
      (2 ^ w * (2 * w + 2) + 1) := by
    obtain ⟨c, hc, hsize⟩ := (Synthesis.selected (n := w) id
      (fun y => decide (enc.symm y = 1))).exists_circuit
    have hcirc := Synthesis.circuit (I := interpretation) (s := (inputs (m * b) ∪ T₁) ∪ T₂) c
      (fun j => bitsOf enc (fun v => U fun i => gp i v) j) (fun j => Or.inr ⟨j, rfl⟩)
    refine hcirc.mono Set.Subset.rfl (Set.singleton_subset_iff.2 ⟨0, funext fun x => ?_⟩)
      hsize
    refine (congrFun (hc _) 0).trans ?_
    have hgx : (fun i => gp i x) ∈ grid := mem_image.2 ⟨x, mem_univ _, rfl⟩
    have hUx : U (fun i => gp i x) = if f x then 1 else 0 := by
      rw [show U (fun i => gp i x) = p (fun i => gp i x) from hV _ hgx]
      exact truthTableExtension_block h f x
    simp only [single_apply, Function.comp_id, bitsOf, Equiv.symm_apply_apply]
    rw [hUx]
    cases f x <;> simp
  have htotal := hemb.trans (hUs.trans hout)
  refine le_trans htotal.complexity_le ?_
  simp only [reconstructionCost, ← hd_def, ← hq_def]
  omega

/-! ### A polynomial bound on the reconstruction cost -/

section Bound

variable {w q M ℓ d K s : ℕ}

private theorem bitBlastCost_le (hq : q = 2 ^ w) (_hw : 1 ≤ w) :
    bitBlastCost w ≤ 7 * w ^ 2 * q ^ 2 := by
  have h2 : 2 ^ (2 * w) = q ^ 2 := by rw [hq, ← pow_mul, mul_comm]
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by rw [hq]; positivity)
  unfold bitBlastCost
  rw [h2]
  have hw2 : w ≤ w ^ 2 := Nat.le_self_pow (by decide : 2 ≠ 0) w
  have h1 : w * q ^ 2 ≤ w ^ 2 * q ^ 2 := Nat.mul_le_mul_right _ hw2
  have h3 : w ≤ w ^ 2 * q ^ 2 := hw2.trans (Nat.le_mul_of_pos_right _ hq1)
  rw [show w * (q ^ 2 * (4 * w + 2) + 1) = 4 * (w ^ 2 * q ^ 2) + 2 * (w * q ^ 2) + w by ring,
    show 7 * w ^ 2 * q ^ 2 = 7 * (w ^ 2 * q ^ 2) by ring]
  omega

private theorem kernelVecCost_le (hM : M ≤ q ^ 2) (hq : 1 ≤ q) :
    kernelVecCost q M ≤ 64 * q ^ 5 := by
  unfold kernelVecCost
  have hq0 : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q hq
  have h1 : q + 1 ≤ 2 * q := by omega
  have h2 : M + 1 ≤ 2 * q ^ 2 := by omega
  calc 8 * (q + 1) * (M + 1) ^ 2 ≤ 8 * (2 * q) * (2 * q ^ 2) ^ 2 := by gcongr
    _ = 64 * q ^ 5 := by ring

private theorem interpolantCost_le (hM : M ≤ q ^ 2) (hℓ : ℓ ≤ q) (hq : 1 ≤ q) :
    interpolantCost q M ℓ ≤ 150 * q ^ 6 := by
  have hk := kernelVecCost_le hM hq
  have hq0 : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q hq
  have hℓ1 : ℓ + 1 ≤ 2 * q := by omega
  have hM1 : M + 1 ≤ 2 * q ^ 2 := by omega
  unfold interpolantCost
  calc
    _ ≤ q * q ^ 2 + (2 * q) * (64 * q ^ 5) + (2 * q) * (2 * q ^ 2) +
        (2 * (2 * q) + 1) + q ^ 2 * (2 * (2 * q) + 1) := by gcongr
    _ = 128 * q ^ 6 + 9 * q ^ 3 + q ^ 2 + 4 * q + 1 := by ring
    _ ≤ 150 * q ^ 6 := by
      have hq6 : 1 ≤ q ^ 6 := Nat.one_le_pow 6 q hq
      have hq16 : q ≤ q ^ 6 := (pow_one q).symm.le.trans (Nat.pow_le_pow_right hq (by decide))
      have hq26 : q ^ 2 ≤ q ^ 6 := Nat.pow_le_pow_right hq (by decide)
      have hq36 : q ^ 3 ≤ q ^ 6 := Nat.pow_le_pow_right hq (by decide)
      omega

private theorem henselCost_le (hM : M ≤ q ^ 2) (hd : d ≤ q) (hq : 1 ≤ q) :
    henselCost q M d ≤ 25 * q ^ 4 := by
  unfold henselCost henselStepCost
  have hq2 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right hq (by norm_num)
  have hq1 : q ≤ q ^ 4 := by
    calc q = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ 4 := Nat.pow_le_pow_right hq (by norm_num)
  have hq3 : q ^ 3 ≤ q ^ 4 := Nat.pow_le_pow_right hq (by norm_num)
  have e1 : d * (q * (2 * d + 3 * M + 6) + 2) ≤ 13 * q ^ 4 := by
    calc d * (q * (2 * d + 3 * M + 6) + 2) ≤ q * (q * (2 * q + 3 * q ^ 2 + 6) + 2) := by
          gcongr
      _ = 2 * q ^ 3 + 3 * q ^ 4 + 6 * q ^ 2 + 2 * q := by ring
      _ ≤ 13 * q ^ 4 := by omega
  omega

private theorem glCost_le (hw : 1 ≤ w) : glCost w K s ≤ 7 * w * 4 ^ K * (s + 1) := by
  set X := 2 ^ K - 1
  have hpow : 2 ^ K = X + 1 := by grind
  have h4 : 4 ^ K = (X + 1) ^ 2 := by
    rw [← hpow, ← pow_mul, mul_comm, pow_mul]
    norm_num
  unfold glCost
  rw [h4]
  change 2 + w * (X * (s + 1) + (2 + X * (2 * (X + 2)))) ≤ _
  ring_nf
  omega

/-- **The reconstruction cost is polynomial**: with `q = 2 ^ w` and the parameters in the ranges
guaranteed by the hypotheses of `complexity_le_of_agree_hardnessEncode` (`D < q`, `d + 1 ≤ q`,
at most `q ^ 2` monomials, `2 ^ b ≤ q`), the reconstructed circuit has at most
`2 ^ 11 * 3 ^ L * m * w ^ 2 * q ^ 9 * 4 ^ K * (s + 1)` gates. -/
theorem reconstructionCost_le {w b m D K L s q M : ℕ} (hq : q = 2 ^ w) (hw : 1 ≤ w)
    (hm : 1 ≤ m) (hb : 2 ^ b ≤ q) (hD : D < q) (hM : M ≤ q ^ 2)
    (hdq : m * (2 ^ b - 1) + 1 ≤ q) :
    reconstructionCost w b m D K L s q M ≤
      2 ^ 11 * 3 ^ L * m * w ^ 2 * q ^ 9 * 4 ^ K * (s + 1) := by
  unfold reconstructionCost selfCorrectCost lineCost
  rw [← hq]
  set d := m * (2 ^ b - 1)
  have hq1 : 1 ≤ q := hq ▸ Nat.one_le_two_pow
  have hbw : b ≤ w := (Nat.pow_le_pow_iff_right (by norm_num)).1 (hq ▸ hb : 2 ^ b ≤ 2 ^ w)
  have hbb := bitBlastCost_le hq hw
  have hhint : hintDecodeCost q q M (D / d) d ≤ 175 * q ^ 6 := by
    have h1 := interpolantCost_le hM ((Nat.div_le_self D d).trans hD.le) hq1
    have h2 := henselCost_le hM (by omega : d ≤ q) hq1
    have : q ^ 4 ≤ q ^ 6 := Nat.pow_le_pow_right hq1 (by norm_num)
    unfold hintDecodeCost
    omega
  set P := 3 ^ L
  set E := 4 ^ K
  have hgl : glCost w K s ≤ 7 * w * E * (s + 1) := glCost_le hw
  set T := P * m * w ^ 2 * q ^ 9 * E * (s + 1) with hT_def
  have hT0 : 0 < T := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos
    (Nat.one_le_pow _ _ (by norm_num)) hm) (pow_pos hw 2)) (pow_pos hq1 9))
    (Nat.one_le_pow _ _ (by norm_num))) s.succ_pos
  -- each monomial of the expanded bound divides `T`
  have hT : ∀ X Y, X * Y = T → X ≤ T := fun X Y h => Nat.le_of_dvd hT0 ⟨Y, h.symm⟩
  calc _ ≤ m * w * (q * (2 * w + 2) + 1) +
        ((m * (P * q) + (P * (2 * q + 1) + 2 * P)) * (7 * w ^ 2 * q ^ 2) +
          P * q * (((q + 5) * m + 2 + (1 + 175 * q ^ 6)) * (7 * w ^ 2 * q ^ 2) +
            q * (7 * w * E * (s + 1)))) + (q * (2 * w + 2) + 1) := by
        gcongr
        exact Nat.sub_le _ _
    _ = 2 * (m * w ^ 2 * q) + 2 * (m * w * q) + m * w + 42 * (P * m * w ^ 2 * q ^ 3) +
          35 * (P * w ^ 2 * q ^ 3) + 21 * (P * w ^ 2 * q ^ 2) + 7 * (P * m * w ^ 2 * q ^ 4) +
          1225 * (P * w ^ 2 * q ^ 9) + 7 * (P * w * q ^ 2 * E * (s + 1)) + 2 * (w * q) + 2 * q +
          1 := by ring
    _ ≤ 2 * T + 2 * T + T + 42 * T + 35 * T + 21 * T + 7 * T + 1225 * T + 7 * T + 2 * T +
          2 * T + T := by
        gcongr
        · exact hT _ (P * q ^ 8 * E * (s + 1)) (by ring)
        · exact hT _ (P * w * q ^ 8 * E * (s + 1)) (by ring)
        · exact hT _ (P * w * q ^ 9 * E * (s + 1)) (by ring)
        · exact hT _ (q ^ 6 * E * (s + 1)) (by ring)
        · exact hT _ (m * q ^ 6 * E * (s + 1)) (by ring)
        · exact hT _ (m * q ^ 7 * E * (s + 1)) (by ring)
        · exact hT _ (q ^ 5 * E * (s + 1)) (by ring)
        · exact hT _ (m * E * (s + 1)) (by ring)
        · exact hT _ (m * w * q ^ 7) (by ring)
        · exact hT _ (P * m * w * q ^ 8 * E * (s + 1)) (by ring)
        · exact hT _ (P * m * w ^ 2 * q ^ 8 * E * (s + 1)) (by ring)
        · exact hT0
    _ ≤ 2 ^ 11 * T := by omega
    _ = _ := by rw [hT_def]; ring

end Bound

omit [DecidableEq F] in
/-- **The reconstruction theorem with a polynomial bound** [SudanTrevisanVadhan2001]. Under the
hypotheses of `complexity_le_of_agree_hardnessEncode`, with `q = |F| = 2 ^ w`, the function `f`
has a De Morgan circuit with at most `2 ^ 11 * 3 ^ L * m * w ^ 2 * q ^ 9 * 4 ^ K * (s + 1)`
gates. -/
theorem complexity_le_pow_of_agree_hardnessEncode (enc : F ≃ BitString w)
    (h : BitString b ↪ F) (f : BooleanFunction (m * b)) {C : BooleanFunction (m * w + w)} {s : ℕ}
    (hC : complexity interpretation (single C) ≤ s) {ε : ℝ} (hε : 0 < ε)
    (hagree : (1 / 2 + ε) * 2 ^ (m * w + w) ≤ #{y | C y = hardnessEncode enc h f y})
    {K D L : ℕ} (hK : 0 < K) (hsize : (w : ℝ) ≤ 2 * (ε / 2) ^ 2 * (2 ^ K - 1 : ℕ))
    (hd : 1 ≤ m * (2 ^ b - 1))
    (hn : Fintype.card F < #(Sudan.monomials (m * (2 ^ b - 1)) D))
    (hmargin : (2 : ℝ) ^ (K + 3) * D ≤ Fintype.card F * ε)
    (herr : 6 * ((m * (2 ^ b - 1) : ℕ) + 1 : ℝ) * (1 / (Fintype.card F : ℝ) ^ m +
      2 ^ (K + 4) / (Fintype.card F * ε) + D / (Fintype.card F - 1)) ≤ 1)
    (hL : m * b ≤ 2 ^ L) :
    complexity interpretation (single f) ≤
      2 ^ 11 * 3 ^ L * m * w ^ 2 * Fintype.card F ^ 9 * 4 ^ K * (s + 1) := by
  refine (complexity_le_of_agree_hardnessEncode enc h f hC hε hagree hK hsize hd hn hmargin herr
    hL).trans ?_
  have hqw : Fintype.card F = 2 ^ w := by
    rw [Fintype.card_congr enc, BitString.card]
  have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hε1 : ε ≤ 1 / 2 := le_half_of_agree hagree
  obtain ⟨-, hDq, hdq⟩ := reconstruction_ranges hq2 hε hε1 hn hmargin herr
  refine reconstructionCost_le hqw ?_ ?_ ?_ hDq ?_ (by omega)
  · by_contra hw
    rw [Nat.lt_one_iff.1 (not_le.1 hw), pow_zero] at hqw
    omega
  · by_contra hm
    rw [Nat.lt_one_iff.1 (not_le.1 hm), zero_mul] at hd
    omega
  · have := Fintype.card_le_of_embedding h
    simpa [BitString] using this
  · calc #(Sudan.monomials (m * (2 ^ b - 1)) D) ≤ #(range (D + 1) ×ˢ range (D + 1)) :=
          card_filter_le _ _
      _ = (D + 1) * (D + 1) := by rw [card_product, card_range]
      _ ≤ Fintype.card F * Fintype.card F := Nat.mul_le_mul hDq hDq
      _ = Fintype.card F ^ 2 := (sq _).symm

end Cslib.Circuits.Boolean
