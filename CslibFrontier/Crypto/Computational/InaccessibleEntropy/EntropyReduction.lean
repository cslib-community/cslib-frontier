/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.LinearHash
public import CslibFrontier.Crypto.Computational.InaccessibleEntropy.Basic
public import CslibFrontier.Probability.BitString.AffineHash.ThreeWise
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Probability.HashFamily.Collisions
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.Uniform
import CslibFrontier.Tactic.UniformRelabel

/-!
# Accessible-entropy reduction and 1-bit shrinking output hashing

Following `[HHRVW2020]`, Sections 5.1.2–5.1.3 (Lemmas 5.4 and 5.5, pp. 27–29), this module
transforms a function $F_1 : \{0, 1\}^{n_1} \to \{0, 1\}^{m_1}$ whose real sample entropy exceeds
$K_{\min}$ except on a small bad set, and whose accessible set $L_1(z)$ has $\log_2 |L_1(z)| <
A_{\max}$ except on a small bad set, into a **strictly $1$-bit shrinking** function
$F_3^{(j)} : \{0, 1\}^{N_3} \to \{0, 1\}^{N_3 - 1}$ ($1 \le n_1$) that is collision-resistant on
random inputs whenever $A_{\max} \ll j \ll K_{\min}$:

1. **Input-hash entropy reduction $F_2^{(j)}$** (`inputHashFin`, `inputHashEvalWord`, Lemma 5.4,
   pp. 27–28): using a fixed-width $n_1 \times n_1$ Boolean matrix `inRows` so that the input width
   `inputHashInLen n₁ = n₁ + n₁ * n₁` and output width `inputHashOutLen n₁ m₁ = m₁ + n₁ * n₁ + n₁`
   are independent of the truncation parameter $j$, define
   $$F_2^{(j)}(z, \mathrm{inRows}) =
     \bigl(F_1(z),\; \mathrm{inRows},\;
       \mathrm{zeroPadPrefix}\;n_1\;j\;(\mathrm{hash}\;\mathrm{inRows}\;z)\bigr).$$
   By `LinearHash.isTwoUniversal_prefix` and `IsTwoUniversal.collision_with_set_le`, any input $z$
   has probability at most $|L_1(z)| / 2^{\min(j, n_1)}$ over `inRows` of colliding under
   $F_2^{(j)}$ with a distinct $z' \in L_1(z)$ (`inputHashFin_accessible_collision_le`).
   Meanwhile, partitioning inputs around `{z | realSampleEntropy f₁ z ≤ K_min}` bounds the total
   image size $|F_2^{(j)}(\{0, 1\}^{n_2})|$ directly (`card_image_inputHashFin_le`, Equation (5.6),
   p. 29).
2. **Output-hash `s`-bit shrinkage $F_3^{(j)}$** (`shrunkHashFin`, `shrunkHashEvalWord`, Lemma 5.5,
   Equations (5.6)–(5.7), p. 29): hashing $F_2^{(j)}(w)$ to
   `outHashLen n₁ s = inputHashInLen n₁ - s` bits via a public Boolean matrix `outRows` yields
   `shrunkHashInLen n₁ m₁ s = shrunkHashOutLen n₁ m₁ s + s` whenever `s ≤ inputHashInLen n₁`
   (`shrunkHashOutLen_add_shrink`), while `LinearHash.isTwoUniversal` bounds false-positive
   output-hash collisions (`shrunkHashFin_false_positive_le`, Equation (5.7), p. 29).
3. **Random-input collision-to-escape reduction** (`randomCollisionGame`,
   `shrunkHashEscapeInverter`, `isPPT_shrunkHashEscapeInverter`, `shrunkHash_randomCollision_le`):
   padding a challenge $z$ with uniform `(inRows, outRows)` — via a uniform strict-PPT reduction
   independent of $j$ — reduces random-input collisions of $F_3^{(j)}$ to escaping $L_1$ plus the
   two concentration tails and two universal-hash error terms (with output-hash factor $2^{s(n)}$).

## Main definitions

* `Cslib.Crypto.inputHashInLen`, `Cslib.Crypto.inputHashOutLen`, `Cslib.Crypto.outHashLen`,
  `Cslib.Crypto.shrunkHashInLen`, `Cslib.Crypto.shrunkHashOutLen`: bit-width schedule of $F_2^{(j)}$
  and $F_3^{(j)}$.
* `Cslib.Crypto.InputHashedInput`, `Cslib.Crypto.InputHashedOutput`,
  `Cslib.Crypto.ShrunkHashInput`, `Cslib.Crypto.ShrunkHashOutput`: structured finite inputs/outputs
  with bit-string equivalences.
* `Cslib.Crypto.inputHashFin`, `Cslib.Crypto.inputHashEvalWord`: finite and word-level evaluators
  of $F_2^{(j)}$.
* `Cslib.Crypto.shrunkHashFin`, `Cslib.Crypto.shrunkHashEvalWord`: finite and word-level evaluators
  of $F_3^{(j)}$.
* `Cslib.Crypto.randomCollisionGame`: security experiment for collision resistance on random inputs.
* `Cslib.Crypto.shrunkHashEscapeInverter`: uniform strict-PPT reduction from $F_3^{(j)}$ collisions
  to $F_1$ accessible escape.

## Main results

* `Cslib.Crypto.inputHashFin_accessible_collision_le`: Lemma 5.4 accessible-collision bound.
* `Cslib.Crypto.card_image_inputHashFin_le`: Equation (5.6) image-cardinality bound for $F_2^{(j)}$.
* `Cslib.Crypto.shrunkHashOutLen_add_shrink`: exact `s`-bit shrinkage when `s ≤ inputHashInLen n₁`.
* `Cslib.Crypto.shrunkHashFin_false_positive_le`: Equation (5.7) false-positive bound for
  $F_3^{(j)}$.
* `Cslib.Crypto.computableInPolyTime_shrunkHashEvalWord`: plain polynomial-time certificate for
  `shrunkHashEvalWord`.
* `Cslib.Crypto.isPPT_shrunkHashEscapeInverter`: plain uniform strict-PPT certificate for
  `shrunkHashEscapeInverter`.
* `Cslib.Crypto.shrunkHash_randomCollision_le`: combined concrete random-input collision bound for
  Lemmas 5.4 and 5.5.

## References

* [I. Haitner, T. Holenstein, O. Reingold, S. Vadhan, H. Wee, *Inaccessible Entropy II: IE
  Functions and Universal One-Way Hashing*, Sections 5.1.2–5.1.3, Lemmas 5.4–5.5 and Equations
  (5.6)–(5.7), pp. 27–29][HHRVW2020]
-/

public section

namespace Cslib.Crypto

open Cslib.Probability Cslib.BitString.LinearHash Finset Turing.MultiTapeTM
open scoped BigOperators ENNReal NNReal

/-! ### Bit-width schedule and structured views for $F_2^{(j)}$ and $F_3^{(j)}$ -/

/-- Input bit width $n_2 = n_1 + n_1^2$ of $F_2^{(j)}$, independent of $j$. -/
@[expose] def inputHashInLen (n₁ : ℕ) : ℕ := n₁ + n₁ * n₁

/-- Output bit width $m_2 = m_1 + n_1^2 + n_1$ of $F_2^{(j)}$, independent of $j$. -/
@[expose] def inputHashOutLen (n₁ m₁ : ℕ) : ℕ := m₁ + n₁ * n₁ + n₁

/-- Digest bit width $n_2 - s$ of the output hash in $F_3^{(j)}$. -/
@[expose] def outHashLen (n₁ s : ℕ) : ℕ := inputHashInLen n₁ - s

/-- Input bit width $N_3 = n_2 + (n_2 - s) m_2$ of $F_3^{(j)}$. -/
@[expose] def shrunkHashInLen (n₁ m₁ s : ℕ) : ℕ :=
  inputHashInLen n₁ + outHashLen n₁ s * inputHashOutLen n₁ m₁

/-- Output bit width $M_3 = (n_2 - s) m_2 + (n_2 - s)$ of $F_3^{(j)}$. -/
@[expose] def shrunkHashOutLen (n₁ m₁ s : ℕ) : ℕ :=
  outHashLen n₁ s * inputHashOutLen n₁ m₁ + outHashLen n₁ s

/-- When `s ≤ inputHashInLen n₁`, $F_3^{(j)}$ shrinks its input by `s` bits. -/
theorem shrunkHashOutLen_add_shrink {n₁ s : ℕ} (hs : s ≤ inputHashInLen n₁) (m₁ : ℕ) :
    shrunkHashOutLen n₁ m₁ s + s = shrunkHashInLen n₁ m₁ s := by
  simp only [shrunkHashOutLen, shrunkHashInLen, outHashLen, inputHashInLen] at hs ⊢
  omega

/-- Structured input `(base, inRows)` to $F_2^{(j)}$ (`[HHRVW2020]`, Section 5.1.2, Lemma 5.4,
pp. 27–28). -/
structure InputHashedInput (n₁ : ℕ) where
  /-- Base $n_1$-bit input $z$ to $F_1$. -/
  base : BitString n₁
  /-- Public $n_1 \times n_1$ Boolean matrix rows of the two-universal input hash. -/
  inRows : Fin n₁ → BitString n₁

instance (n₁ : ℕ) : Nonempty (InputHashedInput n₁) := ⟨⟨0, 0⟩⟩

/-- Pack an `InputHashedInput n₁` into a word of length `inputHashInLen n₁`. -/
@[expose] def InputHashedInput.packWord {n₁ : ℕ} (w : InputHashedInput n₁) : List Bool :=
  List.ofFn w.base ++ List.ofFn (Cslib.BitString.blocksEquiv.symm w.inRows)

@[simp] theorem InputHashedInput.length_packWord {n₁ : ℕ} (w : InputHashedInput n₁) :
    w.packWord.length = inputHashInLen n₁ := by
  simp [InputHashedInput.packWord, inputHashInLen]

/-- Unpack a word into an `InputHashedInput n₁`. -/
@[expose] def InputHashedInput.unpackWord (n₁ : ℕ) (u : List Bool) : InputHashedInput n₁ where
  base := Cslib.BitString.ofList n₁ (u.take n₁)
  inRows := Cslib.BitString.blocksEquiv
    (Cslib.BitString.ofList (n₁ * n₁) ((u.drop n₁).take (n₁ * n₁)))

@[simp] theorem InputHashedInput.unpackWord_packWord {n₁ : ℕ} (w : InputHashedInput n₁) :
    InputHashedInput.unpackWord n₁ w.packWord = w := by
  cases w
  simp only [InputHashedInput.packWord, InputHashedInput.unpackWord,
    List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn,
    Cslib.BitString.ofList_take, Cslib.BitString.ofList_ofFn, Equiv.apply_symm_apply]

theorem InputHashedInput.packWord_unpackWord {n₁ : ℕ} {u : List Bool}
    (hu : u.length = inputHashInLen n₁) :
    (InputHashedInput.unpackWord n₁ u).packWord = u := by
  have hb : (u.take n₁).length = n₁ := by simp [hu, inputHashInLen]
  have hd : (u.drop n₁).length = n₁ * n₁ := by simp [hu, inputHashInLen]
  simp only [InputHashedInput.unpackWord, InputHashedInput.packWord, List.take_of_length_le hd.le,
    Equiv.symm_apply_apply, Cslib.BitString.ofFn_ofList hb, Cslib.BitString.ofFn_ofList hd,
    List.take_append_drop]

/-- Exact bit-string equivalence between `InputHashedInput n₁` and
`BitString (inputHashInLen n₁)`. -/
@[expose] def inputHashedInputEquiv (n₁ : ℕ) :
    InputHashedInput n₁ ≃ BitString (inputHashInLen n₁) where
  toFun w := Cslib.BitString.ofList (inputHashInLen n₁) w.packWord
  invFun b := InputHashedInput.unpackWord n₁ (List.ofFn b)
  left_inv w := by
    dsimp only
    rw [Cslib.BitString.ofFn_ofList w.length_packWord, InputHashedInput.unpackWord_packWord]
  right_inv b := by
    dsimp only
    rw [InputHashedInput.packWord_unpackWord List.length_ofFn, Cslib.BitString.ofList_ofFn]

instance (n₁ : ℕ) : Fintype (InputHashedInput n₁) :=
  Fintype.ofEquiv (BitString (inputHashInLen n₁)) (inputHashedInputEquiv n₁).symm

/-- Structured output `(baseOut, inRows, inDigest)` of $F_2^{(j)}$ (`[HHRVW2020]`, Section 5.1.2,
Lemma 5.4, pp. 27–28). -/
structure InputHashedOutput (n₁ m₁ : ℕ) where
  /-- Base output $F_1(z) \in \{0, 1\}^{m_1}$. -/
  baseOut : BitString m₁
  /-- Public $n_1 \times n_1$ Boolean matrix rows of the input hash. -/
  inRows : Fin n₁ → BitString n₁
  /-- Zero-padded $\min(j, n_1)$-bit prefix of $\mathrm{hash}\;\mathrm{inRows}\;z$. -/
  inDigest : BitString n₁

/-- Pack an `InputHashedOutput n₁ m₁` into a word of length `inputHashOutLen n₁ m₁`. -/
@[expose] def InputHashedOutput.packWord {n₁ m₁ : ℕ} (y : InputHashedOutput n₁ m₁) : List Bool :=
  List.ofFn y.baseOut ++ List.ofFn (Cslib.BitString.blocksEquiv.symm y.inRows) ++
    List.ofFn y.inDigest

@[simp] theorem InputHashedOutput.length_packWord {n₁ m₁ : ℕ} (y : InputHashedOutput n₁ m₁) :
    y.packWord.length = inputHashOutLen n₁ m₁ := by
  simp only [InputHashedOutput.packWord, inputHashOutLen, List.length_append, List.length_ofFn]

/-- Unpack a word into an `InputHashedOutput n₁ m₁`. -/
@[expose] def InputHashedOutput.unpackWord (n₁ m₁ : ℕ) (u : List Bool) :
    InputHashedOutput n₁ m₁ :=
  let rest := u.drop m₁
  { baseOut := Cslib.BitString.ofList m₁ (u.take m₁)
    inRows := Cslib.BitString.blocksEquiv
      (Cslib.BitString.ofList (n₁ * n₁) (rest.take (n₁ * n₁)))
    inDigest := Cslib.BitString.ofList n₁ (rest.drop (n₁ * n₁)) }

@[simp] theorem InputHashedOutput.unpackWord_packWord {n₁ m₁ : ℕ} (y : InputHashedOutput n₁ m₁) :
    InputHashedOutput.unpackWord n₁ m₁ y.packWord = y := by
  cases y
  simp only [InputHashedOutput.packWord, InputHashedOutput.unpackWord, List.append_assoc,
    List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn,
    Cslib.BitString.ofList_ofFn, Equiv.apply_symm_apply]

theorem InputHashedOutput.packWord_unpackWord {n₁ m₁ : ℕ} {u : List Bool}
    (hu : u.length = inputHashOutLen n₁ m₁) :
    (InputHashedOutput.unpackWord n₁ m₁ u).packWord = u := by
  have hb : (u.take m₁).length = m₁ := by simp [hu, inputHashOutLen]; omega
  have hr : ((u.drop m₁).take (n₁ * n₁)).length = n₁ * n₁ := by simp [hu, inputHashOutLen]; omega
  have hd : ((u.drop m₁).drop (n₁ * n₁)).length = n₁ := by simp [hu, inputHashOutLen]
  simp only [InputHashedOutput.unpackWord, InputHashedOutput.packWord, Equiv.symm_apply_apply,
    Cslib.BitString.ofFn_ofList hb, Cslib.BitString.ofFn_ofList hr, Cslib.BitString.ofFn_ofList hd,
    List.append_assoc, List.take_append_drop]

/-- Exact bit-string equivalence between `InputHashedOutput n₁ m₁` and
`BitString (inputHashOutLen n₁ m₁)`. -/
@[expose] def inputHashedOutputEquiv (n₁ m₁ : ℕ) :
    InputHashedOutput n₁ m₁ ≃ BitString (inputHashOutLen n₁ m₁) where
  toFun y := Cslib.BitString.ofList (inputHashOutLen n₁ m₁) y.packWord
  invFun b := InputHashedOutput.unpackWord n₁ m₁ (List.ofFn b)
  left_inv y := by
    dsimp only
    rw [Cslib.BitString.ofFn_ofList y.length_packWord, InputHashedOutput.unpackWord_packWord]
  right_inv b := by
    dsimp only
    rw [InputHashedOutput.packWord_unpackWord List.length_ofFn, Cslib.BitString.ofList_ofFn]

/-- Structured input `(inner, outRows)` to $F_3^{(j)}$ (`[HHRVW2020]`, Section 5.1.3, Lemma 5.5,
p. 29). -/
structure ShrunkHashInput (n₁ m₁ s : ℕ) where
  /-- Input $(z, \mathrm{inRows})$ to $F_2^{(j)}$. -/
  inner : InputHashedInput n₁
  /-- Public $(n_2 - s) \times m_2$ Boolean matrix rows of the output hash. -/
  outRows : Fin (outHashLen n₁ s) → BitString (inputHashOutLen n₁ m₁)

instance (n₁ m₁ s : ℕ) : Nonempty (ShrunkHashInput n₁ m₁ s) := ⟨⟨⟨0, 0⟩, 0⟩⟩

/-- Pack a `ShrunkHashInput n₁ m₁ s` into a word of length `shrunkHashInLen n₁ m₁ s`. -/
@[expose] def ShrunkHashInput.packWord {n₁ m₁ s : ℕ} (v : ShrunkHashInput n₁ m₁ s) : List Bool :=
  v.inner.packWord ++ List.ofFn (Cslib.BitString.blocksEquiv.symm v.outRows)

@[simp] theorem ShrunkHashInput.length_packWord {n₁ m₁ s : ℕ} (v : ShrunkHashInput n₁ m₁ s) :
    v.packWord.length = shrunkHashInLen n₁ m₁ s := by
  simp [ShrunkHashInput.packWord, shrunkHashInLen]

/-- Unpack a word into a `ShrunkHashInput n₁ m₁ s`. -/
@[expose] def ShrunkHashInput.unpackWord (n₁ m₁ s : ℕ) (raw : List Bool) :
    ShrunkHashInput n₁ m₁ s :=
  let inLen₂ := inputHashInLen n₁
  let outSeedLen := outHashLen n₁ s * inputHashOutLen n₁ m₁
  { inner := InputHashedInput.unpackWord n₁ (raw.take inLen₂)
    outRows := Cslib.BitString.blocksEquiv
      (Cslib.BitString.ofList outSeedLen ((raw.drop inLen₂).take outSeedLen)) }

@[simp] theorem ShrunkHashInput.unpackWord_packWord {n₁ m₁ s : ℕ} (v : ShrunkHashInput n₁ m₁ s) :
    ShrunkHashInput.unpackWord n₁ m₁ s v.packWord = v := by
  cases v with | mk inn _ =>
  simp only [ShrunkHashInput.packWord, ShrunkHashInput.unpackWord,
    List.take_left' inn.length_packWord, List.drop_left' inn.length_packWord,
    InputHashedInput.unpackWord_packWord, Cslib.BitString.ofList_take,
    Cslib.BitString.ofList_ofFn, Equiv.apply_symm_apply]

theorem ShrunkHashInput.packWord_unpackWord {n₁ m₁ s : ℕ} {raw : List Bool}
    (hraw : raw.length = shrunkHashInLen n₁ m₁ s) :
    (ShrunkHashInput.unpackWord n₁ m₁ s raw).packWord = raw := by
  have hi : (raw.take (inputHashInLen n₁)).length = inputHashInLen n₁ := by
    simp [hraw, shrunkHashInLen]
  have hd : (raw.drop (inputHashInLen n₁)).length = outHashLen n₁ s * inputHashOutLen n₁ m₁ := by
    simp [hraw, shrunkHashInLen]
  simp only [ShrunkHashInput.unpackWord, ShrunkHashInput.packWord,
    InputHashedInput.packWord_unpackWord hi, Cslib.BitString.ofList_take,
    Equiv.symm_apply_apply, Cslib.BitString.ofFn_ofList hd, List.take_append_drop]

/-- Structured output `(outRows, outDigest)` of $F_3^{(j)}$ (`[HHRVW2020]`, Section 5.1.3,
Lemma 5.5, p. 29). -/
structure ShrunkHashOutput (n₁ m₁ s : ℕ) where
  /-- Public $(n_2 - s) \times m_2$ Boolean matrix rows of the output hash. -/
  outRows : Fin (outHashLen n₁ s) → BitString (inputHashOutLen n₁ m₁)
  /-- $(n_2 - s)$-bit two-universal digest of $F_2^{(j)}(\mathrm{inner})$. -/
  outDigest : BitString (outHashLen n₁ s)

/-- Pack a `ShrunkHashOutput n₁ m₁ s` into a word of length `shrunkHashOutLen n₁ m₁ s`. -/
@[expose] def ShrunkHashOutput.packWord {n₁ m₁ s : ℕ} (y : ShrunkHashOutput n₁ m₁ s) : List Bool :=
  List.ofFn (Cslib.BitString.blocksEquiv.symm y.outRows) ++ List.ofFn y.outDigest

@[simp] theorem ShrunkHashOutput.length_packWord {n₁ m₁ s : ℕ} (y : ShrunkHashOutput n₁ m₁ s) :
    y.packWord.length = shrunkHashOutLen n₁ m₁ s := by
  simp [ShrunkHashOutput.packWord, shrunkHashOutLen]

/-- Unpack a word into a `ShrunkHashOutput n₁ m₁ s`. -/
@[expose] def ShrunkHashOutput.unpackWord (n₁ m₁ s : ℕ) (u : List Bool) :
    ShrunkHashOutput n₁ m₁ s :=
  let outSeedLen := outHashLen n₁ s * inputHashOutLen n₁ m₁
  { outRows := Cslib.BitString.blocksEquiv
      (Cslib.BitString.ofList outSeedLen (u.take outSeedLen))
    outDigest := Cslib.BitString.ofList (outHashLen n₁ s) (u.drop outSeedLen) }

@[simp] theorem ShrunkHashOutput.unpackWord_packWord {n₁ m₁ s : ℕ}
    (y : ShrunkHashOutput n₁ m₁ s) :
    ShrunkHashOutput.unpackWord n₁ m₁ s y.packWord = y := by
  cases y
  simp only [ShrunkHashOutput.packWord, ShrunkHashOutput.unpackWord,
    List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn,
    Cslib.BitString.ofList_ofFn, Equiv.apply_symm_apply]

/-! ### Step 2: Input-hash entropy reduction $F_2^{(j)}$ (Lemma 5.4 and Equation (5.6)) -/

/-- Finite evaluator $F_2^{(j)}(z, \mathrm{inRows}) = (F_1(z), \mathrm{inRows},
\mathrm{zeroPadPrefix}\;n_1\;j\;(\mathrm{hash}\;\mathrm{inRows}\;z))$ (`[HHRVW2020]`, Section 5.1.2,
Lemma 5.4, pp. 27–28). -/
@[expose] def inputHashFin {n₁ m₁ : ℕ} (f₁ : BitString n₁ → BitString m₁) (j : ℕ)
    (w : InputHashedInput n₁) : InputHashedOutput n₁ m₁ where
  baseOut := f₁ w.base
  inRows := w.inRows
  inDigest := zeroPadPrefix n₁ j (Cslib.BitString.LinearHash.hash w.inRows w.base)

open Classical in
/-- **`[HHRVW2020]`, Section 5.1.2, Lemma 5.4(ii) (p. 28)**: by two-universality of matrix prefixes
(`LinearHash.isTwoUniversal_prefix`), the probability over `inRows` that some distinct
$z' \in L$ collides with $z$ under `inputHashFin f₁ j` is at most $|L| / 2^{\min(j, n_1)}$. -/
theorem inputHashFin_accessible_collision_le {n₁ m₁ : ℕ} (f₁ : BitString n₁ → BitString m₁)
    (j : ℕ) (L : Finset (BitString n₁)) (z : BitString n₁) :
    (∑ rows : Fin n₁ → BitString n₁,
        if ∃ z' ∈ L, z' ≠ z ∧ inputHashFin f₁ j ⟨z', rows⟩ = inputHashFin f₁ j ⟨z, rows⟩ then
          ((PMF.uniformOfFintype (Fin n₁ → BitString n₁)) rows).toReal
        else 0) ≤
      (#L : ℝ) / (2 : ℝ) ^ (min j n₁) := by
  rw [show (2 : ℝ) ^ min j n₁ = Fintype.card (BitString (min j n₁)) by simp [BitString]]
  exact (Cslib.BitString.LinearHash.isTwoUniversal_prefix (Nat.min_le_right j n₁))
    |>.sum_ite_toReal_le_card_div_of_imp L z fun _ ⟨z', hz', hne, heq⟩ =>
      ⟨z', hz', hne, (zeroPadPrefix_eq_iff_prefixProj_eq _ _).mp
        (congrArg InputHashedOutput.inDigest heq)⟩

private def unpadPrefix (k r : ℕ) (p : BitString (min r k)) : BitString k :=
  fun i => if h : i.val < min r k then p ⟨i.val, h⟩ else false

private theorem zeroPadPrefix_eq_unpadPrefix (k r : ℕ) (v : BitString k) :
    zeroPadPrefix k r v = unpadPrefix k r (prefixProj k r v) := by
  funext i
  by_cases hi : i.val < r <;> simp [zeroPadPrefix, unpadPrefix, prefixProj, hi, i.isLt]

open Classical in
/-- **`[HHRVW2020]`, Section 5.1.3, Lemma 5.5, Equation (5.6) (p. 29)**: partitioning inputs around
`{z | realSampleEntropy f₁ z ≤ K}` bounds the image cardinality of `inputHashFin f₁ j` by
$(\Pr[H_z \le K] + 2^{\min(j, n_1) - K}) \cdot 2^{n_2}$. -/
theorem card_image_inputHashFin_le {n₁ m₁ : ℕ} (f₁ : BitString n₁ → BitString m₁)
    (j : ℕ) (K : ℝ) :
    (#(univ.image (inputHashFin f₁ j)) : ℝ) ≤
      (((PMF.uniformOfFintype (BitString n₁)).toOuterMeasure
          {z | realSampleEntropy f₁ z ≤ K}).toReal +
        (2 : ℝ) ^ ((min j n₁ : ℝ) - K)) * (2 : ℝ) ^ (inputHashInLen n₁) := by
  classical
  let badInputs : Finset (BitString n₁) := univ.filter fun z => realSampleEntropy f₁ z ≤ K
  let goodInputs : Finset (BitString n₁) := univ.filter fun z => ¬ realSampleEntropy f₁ z ≤ K
  let goodImages : Finset (BitString m₁) := goodInputs.image f₁
  have hsub : univ.image (inputHashFin f₁ j) ⊆
      (badInputs ×ˢ (univ : Finset (Fin n₁ → BitString n₁))).image
        (fun p => inputHashFin f₁ j ⟨p.1, p.2⟩) ∪
      (goodImages ×ˢ (univ : Finset (Fin n₁ → BitString n₁)) ×ˢ
        (univ : Finset (BitString (min j n₁)))).image
        (fun ⟨y, rows, p⟩ => ⟨y, rows, unpadPrefix n₁ j p⟩) := by
    intro out hout
    obtain ⟨⟨z, rows⟩, _, rfl⟩ := mem_image.mp hout
    by_cases hz : realSampleEntropy f₁ z ≤ K
    · exact mem_union_left _ (mem_image.mpr
        ⟨(z, rows), mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ z, hz⟩, mem_univ rows⟩, rfl⟩)
    · refine mem_union_right _ (mem_image.mpr
        ⟨(f₁ z, rows, prefixProj n₁ j (Cslib.BitString.LinearHash.hash rows z)),
          mem_product.mpr ⟨mem_image_of_mem f₁ (mem_filter.mpr ⟨mem_univ z, hz⟩),
            mem_product.mpr ⟨mem_univ rows, mem_univ _⟩⟩, ?_⟩)
      simp only [inputHashFin, zeroPadPrefix_eq_unpadPrefix]
  have htotal_nat : #(univ.image (inputHashFin f₁ j)) ≤
      #badInputs * 2 ^ (n₁ * n₁) + #goodImages * 2 ^ (n₁ * n₁) * 2 ^ min j n₁ := by
    refine (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add ?_ ?_))
    · exact card_image_le.trans (by simp [BitString, pow_mul])
    · exact card_image_le.trans (by simp [BitString, pow_mul, mul_assoc])
  have hgoodImages_card : (#goodImages : ℝ) ≤ (2 : ℝ) ^ n₁ * ((2 : ℝ) ^ K)⁻¹ := by
    refine (le_mul_inv_iff₀ (Real.rpow_pos_of_pos two_pos K)).mpr ?_
    calc
      (#goodImages : ℝ) * (2 : ℝ) ^ K = ∑ _y ∈ goodImages, (2 : ℝ) ^ K := by
        rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ y ∈ goodImages, (#(fiberSet f₁ y) : ℝ) := sum_le_sum fun y hy => by
        obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
        exact (Real.le_logb_iff_rpow_le one_lt_two
          (by exact_mod_cast card_fiberSet_pos f₁ z)).mp (not_le.mp (mem_filter.mp hz).2).le
      _ ≤ ∑ y ∈ univ.image f₁, (#(univ.filter fun z => f₁ z = y) : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (image_subset_image (subset_univ _))
          fun _ _ _ => Nat.cast_nonneg _
      _ = (2 : ℝ) ^ n₁ := by
        rw [← Nat.cast_sum, ← card_eq_sum_card_image]
        simp [BitString]
  have hbad_prob : (#badInputs : ℝ) / (2 : ℝ) ^ n₁ =
      ((PMF.uniformOfFintype (BitString n₁)).toOuterMeasure
        {z | realSampleEntropy f₁ z ≤ K}).toReal := by
    rw [PMF.toOuterMeasure_uniformOfFintype_toReal]
    simp [BitString, badInputs]
  calc
    (#(univ.image (inputHashFin f₁ j)) : ℝ)
      ≤ (#badInputs : ℝ) * (2 : ℝ) ^ (n₁ * n₁) +
          (#goodImages : ℝ) * (2 : ℝ) ^ (n₁ * n₁) * (2 : ℝ) ^ min j n₁ := by
        exact_mod_cast htotal_nat
    _ ≤ (#badInputs : ℝ) * (2 : ℝ) ^ (n₁ * n₁) +
          ((2 : ℝ) ^ n₁ * ((2 : ℝ) ^ K)⁻¹) * (2 : ℝ) ^ (n₁ * n₁) * (2 : ℝ) ^ min j n₁ := by
        gcongr
    _ = (((PMF.uniformOfFintype (BitString n₁)).toOuterMeasure
          {z | realSampleEntropy f₁ z ≤ K}).toReal +
        (2 : ℝ) ^ ((min j n₁ : ℝ) - K)) * (2 : ℝ) ^ inputHashInLen n₁ := by
        rw [← hbad_prob, inputHashInLen, pow_add, Real.rpow_sub two_pos, ← Nat.cast_min,
          Real.rpow_natCast]
        field_simp

/-! ### Step 3: Output-hash `s`-bit shrinkage $F_3^{(j)}$ (Lemma 5.5 and Equation (5.7)) -/

/-- Finite evaluator $F_3^{(j)}(w, \mathrm{outRows}) = (\mathrm{outRows},
\mathrm{hash}\;\mathrm{outRows}\;(\mathrm{enc}(F_2^{(j)}(w))))$ with `s`-bit shrinkage
(`outHashLen n₁ s = inputHashInLen n₁ - s`; `[HHRVW2020]`, Section 5.1.3, Lemma 5.5, p. 29). -/
@[expose] def shrunkHashFin {n₁ m₁ : ℕ} (f₁ : BitString n₁ → BitString m₁) (j s : ℕ)
    (v : ShrunkHashInput n₁ m₁ s) : ShrunkHashOutput n₁ m₁ s where
  outRows := v.outRows
  outDigest := Cslib.BitString.LinearHash.hash v.outRows
    (inputHashedOutputEquiv n₁ m₁ (inputHashFin f₁ j v.inner))

open Classical in
/-- **`[HHRVW2020]`, Section 5.1.3, Lemma 5.5, Equation (5.7) (p. 29)**: for every fixed input $w$,
the probability over `outRows` that some $w'$ with $F_2^{(j)}(w') \ne F_2^{(j)}(w)$ collides with
$w$ under `shrunkHashFin f₁ j s` is at most
$|F_2^{(j)}(\{0, 1\}^{n_2})| / 2^{\mathrm{outHashLen}\;n_1\;s}$. -/
theorem shrunkHashFin_false_positive_le {n₁ m₁ : ℕ} (f₁ : BitString n₁ → BitString m₁)
    (j s : ℕ) (w : InputHashedInput n₁) :
    (∑ outRows : Fin (outHashLen n₁ s) → BitString (inputHashOutLen n₁ m₁),
        if ∃ w' : InputHashedInput n₁,
            inputHashFin f₁ j w' ≠ inputHashFin f₁ j w ∧
            shrunkHashFin f₁ j s ⟨w', outRows⟩ = shrunkHashFin f₁ j s ⟨w, outRows⟩ then
          ((PMF.uniformOfFintype
            (Fin (outHashLen n₁ s) → BitString (inputHashOutLen n₁ m₁))) outRows).toReal
        else 0) ≤
      (#(univ.image (inputHashFin f₁ j)) : ℝ) / (2 : ℝ) ^ (outHashLen n₁ s) := by
  rw [show (2 : ℝ) ^ outHashLen n₁ s = Fintype.card (BitString (outHashLen n₁ s)) by
    simp [BitString]]
  exact IsTwoUniversal.sum_ite_toReal_le_card_div_of_imp
    ((Cslib.BitString.LinearHash.isTwoUniversal
      (inputHashOutLen n₁ m₁) (outHashLen n₁ s)).precompose
      (inputHashedOutputEquiv n₁ m₁).injective)
    (univ.image (inputHashFin f₁ j)) (inputHashFin f₁ j w) fun _ ⟨w', hne, heq⟩ =>
      ⟨inputHashFin f₁ j w', mem_image_of_mem _ (mem_univ w'), hne,
        congrArg ShrunkHashOutput.outDigest heq⟩

/-! ### Word-level evaluators and polynomial-time certificates -/

/-- Word-level evaluator of $F_2^{(j)}$ (`[HHRVW2020]`, Section 5.1.2, Lemma 5.4, pp. 27–28). -/
@[expose] def inputHashEvalWord (n₁ m₁ : ℕ) (evalWord₁ : List Bool → List Bool)
    (j : ℕ) (u : List Bool) : List Bool :=
  let zWord := Cslib.BitString.listRow n₁ 0 (u.take n₁)
  let inSeed := Cslib.BitString.listRow (n₁ * n₁) 0 ((u.drop n₁).take (n₁ * n₁))
  let baseBits := Cslib.BitString.listRow m₁ 0 (evalWord₁ zWord)
  let fullDigest := wordHash n₁ inSeed zWord
  let r := n₁ - (n₁ - j)
  baseBits ++ inSeed ++ (fullDigest.take r ++ List.replicate (n₁ - r) false)

/-- Word-level evaluator of $F_3^{(j)}$ with `s`-bit shrinkage (`[HHRVW2020]`, Section 5.1.3,
Lemma 5.5, p. 29). -/
@[expose] def shrunkHashEvalWord (n₁ m₁ : ℕ) (evalWord₁ : List Bool → List Bool)
    (j s : ℕ) (raw : List Bool) : List Bool :=
  let inLen₂ := inputHashInLen n₁
  let outLen₂ := inputHashOutLen n₁ m₁
  let outH := outHashLen n₁ s
  let innerWord := raw.take inLen₂
  let outSeed := Cslib.BitString.listRow (outH * outLen₂) 0
    ((raw.drop inLen₂).take (outH * outLen₂))
  let y₂ := inputHashEvalWord n₁ m₁ evalWord₁ j innerWord
  outSeed ++ wordHash outH outSeed y₂

@[simp] theorem length_inputHashEvalWord (n₁ m₁ : ℕ) (evalWord₁ : List Bool → List Bool)
    (j : ℕ) (u : List Bool) :
    (inputHashEvalWord n₁ m₁ evalWord₁ j u).length = inputHashOutLen n₁ m₁ := by
  have hr : n₁ - (n₁ - j) ≤ n₁ := Nat.sub_le _ _
  simp only [inputHashEvalWord, inputHashOutLen, List.length_append,
    Cslib.BitString.length_listRow, List.length_take, length_wordHash, List.length_replicate]
  omega

@[simp] theorem length_shrunkHashEvalWord (n₁ m₁ : ℕ) (evalWord₁ : List Bool → List Bool)
    (j s : ℕ) (raw : List Bool) :
    (shrunkHashEvalWord n₁ m₁ evalWord₁ j s raw).length = shrunkHashOutLen n₁ m₁ s := by
  simp only [shrunkHashEvalWord, shrunkHashOutLen, List.length_append,
    Cslib.BitString.length_listRow, length_wordHash]

/-- Plain polynomial-time certificate for `inputHashEvalWord`. -/
@[fun_prop]
theorem computableInPolyTime_inputHashEvalWord {α : Type} {encode : α ↪ List Bool}
    {n₁ m₁ n j : α → ℕ} {evalWord₁ : ℕ → List Bool → List Bool} {u : α → List Bool}
    (hn₁ : ComputableInPolyTime n₁ encode encUnary)
    (hm₁ : ComputableInPolyTime m₁ encode encUnary)
    (hn : ComputableInPolyTime n encode encUnary)
    (hj : ComputableInPolyTime j encode encUnary)
    (heval₁ : ComputableInPolyTime (fun p : ℕ × List Bool => evalWord₁ p.1 p.2)
      (encPair encUnary encBits) encBits)
    (hu : ComputableInPolyTime u encode encBits) :
    ComputableInPolyTime
      (fun a => inputHashEvalWord (n₁ a) (m₁ a) (evalWord₁ (n a)) (j a) (u a))
      encode encBits := by
  have hz := ComputableInPolyTime.bitsRowWithInput hn₁ (.const 0)
    (ComputableInPolyTime.bitsTakeWithInput hu hn₁)
  have hsize := ComputableInPolyTime.unary_mul' hn₁ hn₁
  have hseed := ComputableInPolyTime.bitsRowWithInput hsize (.const 0)
    (ComputableInPolyTime.bitsTakeWithInput
      (ComputableInPolyTime.bitsDropWithInput hu hn₁) hsize)
  have hbase := ComputableInPolyTime.bitsRowWithInput hm₁ (.const 0) (heval₁.comp (hn.prod hz))
  have hr := ComputableInPolyTime.unary_sub' hn₁ (ComputableInPolyTime.unary_sub' hn₁ hj)
  exact ComputableInPolyTime.bitsAppend (ComputableInPolyTime.bitsAppend hbase hseed)
    (ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.bitsTakeWithInput (computableInPolyTime_wordHash hn₁ hseed hz) hr)
      ((ComputableInPolyTime.bitsReplicate false).comp (ComputableInPolyTime.unary_sub' hn₁ hr)))

/-- Plain polynomial-time certificate for `shrunkHashEvalWord`. -/
@[fun_prop]
theorem computableInPolyTime_shrunkHashEvalWord {α : Type} {encode : α ↪ List Bool}
    {n₁ m₁ n j s : α → ℕ} {evalWord₁ : ℕ → List Bool → List Bool} {raw : α → List Bool}
    (hn₁ : ComputableInPolyTime n₁ encode encUnary)
    (hm₁ : ComputableInPolyTime m₁ encode encUnary)
    (hn : ComputableInPolyTime n encode encUnary)
    (hj : ComputableInPolyTime j encode encUnary)
    (hs : ComputableInPolyTime s encode encUnary)
    (heval₁ : ComputableInPolyTime (fun p : ℕ × List Bool => evalWord₁ p.1 p.2)
      (encPair encUnary encBits) encBits)
    (hraw : ComputableInPolyTime raw encode encBits) :
    ComputableInPolyTime
      (fun a => shrunkHashEvalWord (n₁ a) (m₁ a) (evalWord₁ (n a)) (j a) (s a) (raw a))
      encode encBits := by
  simp only [shrunkHashEvalWord, inputHashInLen, inputHashOutLen, outHashLen]
  have hin₂ := ComputableInPolyTime.unary_add' hn₁ (ComputableInPolyTime.unary_mul' hn₁ hn₁)
  have hout₂ := ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_add' hm₁ (ComputableInPolyTime.unary_mul' hn₁ hn₁)) hn₁
  have houtH := ComputableInPolyTime.unary_sub' hin₂ hs
  have hsize := ComputableInPolyTime.unary_mul' houtH hout₂
  have hseed := ComputableInPolyTime.bitsRowWithInput hsize (.const 0)
    (ComputableInPolyTime.bitsTakeWithInput
      (ComputableInPolyTime.bitsDropWithInput hraw hin₂) hsize)
  exact ComputableInPolyTime.bitsAppend hseed (computableInPolyTime_wordHash houtH hseed
    (computableInPolyTime_inputHashEvalWord hn₁ hm₁ hn hj heval₁
      (ComputableInPolyTime.bitsTakeWithInput hraw hin₂)))

@[simp] private theorem listRow_zero_ofFn {k : ℕ} (x : BitString k) :
    Cslib.BitString.listRow k 0 (List.ofFn x) = List.ofFn x := by
  rw [Cslib.BitString.listRow_zero, Cslib.BitString.ofList_ofFn]

@[simp] private theorem wordHash_blocksEquiv_symm {k m : ℕ} (rows : Fin k → BitString m)
    (x : BitString m) :
    wordHash k (List.ofFn (Cslib.BitString.blocksEquiv.symm rows)) (List.ofFn x) =
      List.ofFn (Cslib.BitString.LinearHash.hash rows x) := by
  rw [wordHash_eq_ofFn, Cslib.BitString.ofList_ofFn, ← Cslib.BitString.blocksEquiv_apply,
    Equiv.apply_symm_apply]

theorem inputHashEvalWord_packWord {n₁ m₁ : ℕ} (evalWord₁ : List Bool → List Bool)
    (j : ℕ) (w : InputHashedInput n₁) :
    inputHashEvalWord n₁ m₁ evalWord₁ j w.packWord =
      (inputHashFin (wordToFinMap n₁ m₁ evalWord₁) j w).packWord := by
  have hmin : n₁ - (n₁ - j) = min j n₁ := by omega
  simp only [inputHashEvalWord, InputHashedInput.packWord, List.take_left' List.length_ofFn,
    List.drop_left' List.length_ofFn, List.take_of_length_le List.length_ofFn.le, listRow_zero_ofFn,
    Cslib.BitString.listRow_zero m₁ (evalWord₁ _), wordToFinMap, wordHash_blocksEquiv_symm, hmin,
    inputHashFin, InputHashedOutput.packWord, List.append_assoc]
  rw [ofFn_zeroPadPrefix]

theorem shrunkHashEvalWord_packWord {n₁ m₁ s : ℕ} (evalWord₁ : List Bool → List Bool)
    (j : ℕ) (v : ShrunkHashInput n₁ m₁ s) :
    shrunkHashEvalWord n₁ m₁ evalWord₁ j s v.packWord =
      (shrunkHashFin (wordToFinMap n₁ m₁ evalWord₁) j s v).packWord := by
  simp only [shrunkHashEvalWord, ShrunkHashInput.packWord,
    List.take_left' v.inner.length_packWord, List.drop_left' v.inner.length_packWord,
    List.take_of_length_le List.length_ofFn.le, listRow_zero_ofFn,
    inputHashEvalWord_packWord evalWord₁ j v.inner, shrunkHashFin, ShrunkHashOutput.packWord]
  rw [← Cslib.BitString.ofFn_ofList (inputHashFin _ j v.inner).length_packWord,
    wordHash_blocksEquiv_symm]
  rfl

/-! ### Random-input collision game and combined reduction to $L_1$-escape -/

/-- Security experiment for collision resistance on random inputs (`[HHRVW2020]`, Section 3.1,
p. 13, and Section 5.1.3, Lemma 5.5, p. 29): draw a uniform `(inLen n)`-bit input `xWord`, run `A`,
and accept when `A` returns a distinct `(inLen n)`-bit input with the same `evalWord n` image. -/
@[expose] noncomputable def randomCollisionGame (evalWord : ℕ → List Bool → List Bool)
    (inLen : ℕ → ℕ) (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ) : ProbComp Bool := do
  let xWord ← Cslib.BitString.sampleList (inLen n)
  let xWord' ← A n xWord
  return decide (xWord'.length = inLen n ∧ xWord' ≠ xWord ∧ evalWord n xWord' = evalWord n xWord)

/-- Uniform strict-PPT reduction from random-input collisions of $F_3^{(j)}$ to $F_1$ accessible
escape (`[HHRVW2020]`, Lemmas 5.4(ii) and 5.5, pp. 28–29). Note that the reduction does **not**
depend on the grid truncation length $j$: it pads the $n_1$-bit challenge `zWord` with uniform
`(inSeed, outSeed)`, runs `A`, and extracts the $n_1$-bit prefix. -/
@[expose] noncomputable def shrunkHashEscapeInverter (n₁ m₁ s : ℕ → ℕ)
    (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ) (zWord : List Bool) :
    ProbComp (List Bool) := do
  let inSeed ← Cslib.BitString.sampleList (n₁ n * n₁ n)
  let outSeed ← Cslib.BitString.sampleList (outHashLen (n₁ n) (s n) * inputHashOutLen (n₁ n) (m₁ n))
  let zPad := Cslib.BitString.listRow (n₁ n) 0 zWord
  let raw ← A n (zPad ++ inSeed ++ outSeed)
  return raw.take (n₁ n)

/-- Plain uniform strict-PPT certificate for `shrunkHashEscapeInverter`. -/
theorem isPPT_shrunkHashEscapeInverter {n₁ m₁ s : ℕ → ℕ}
    {A : ℕ → List Bool → ProbComp (List Bool)}
    (hn₁ : ComputableInPolyTime n₁ encUnary encUnary)
    (hm₁ : ComputableInPolyTime m₁ encUnary encUnary)
    (hs : ComputableInPolyTime s encUnary encUnary)
    (hA : IsPPT encBits A) :
    IsPPT encBits (shrunkHashEscapeInverter n₁ m₁ s A) := by
  apply IsPPTOn.isPPT
  refine (ComputableInPolyTime.sampleList (by fun_prop)).bind_with ?_
  refine (ComputableInPolyTime.sampleList
    (by unfold outHashLen inputHashOutLen inputHashInLen; fun_prop)).bind_with ?_
  have hp := ComputableInPolyTime.id'
    (encIn := encPair (encPair (encPair encUnary encBits) encBits) encBits)
  have hparam := hp.fst'.fst'.fst'
  have hwidth := hn₁.comp hparam
  have hprep := ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.bitsRowWithInput hwidth (.const 0) hp.fst'.fst'.snd') hp.fst'.snd')
    hp.snd'
  simpa only [bind_pure_comp, Function.comp_def] using
    (hA.preprocess hparam hprep).map_with
      (ComputableInPolyTime.bitsTakeWithInput (ComputableInPolyTime.snd _ encBits)
        (hwidth.comp (ComputableInPolyTime.fst _ encBits)))

private theorem uniformList_shrunkHashInLen_eq (n₁ m₁ s : ℕ) :
    Cslib.BitString.uniformList (shrunkHashInLen n₁ m₁ s) =
      (PMF.uniformOfFintype (BitString n₁)).bind fun z =>
        (PMF.uniformOfFintype (Fin n₁ → BitString n₁)).bind fun iRows =>
          (PMF.uniformOfFintype
            (Fin (outHashLen n₁ s) → BitString (inputHashOutLen n₁ m₁))).map fun oRows =>
              (ShrunkHashInput.mk ⟨z, iRows⟩ oRows).packWord := by
  rw [Cslib.BitString.uniformList]
  relabel_uniform (fun t : BitString n₁ × (Fin n₁ → BitString n₁) ×
      (Fin (outHashLen n₁ s) → BitString (inputHashOutLen n₁ m₁)) =>
    Cslib.BitString.ofList (shrunkHashInLen n₁ m₁ s)
      (ShrunkHashInput.mk ⟨t.1, t.2.1⟩ t.2.2).packWord) with t
  · rintro ⟨z₁, i₁, o₁⟩ ⟨z₂, i₂, o₂⟩ h
    have hpk := congrArg (fun b => ShrunkHashInput.unpackWord n₁ m₁ s (List.ofFn b)) h
    simp only [Cslib.BitString.ofFn_ofList (ShrunkHashInput.mk _ _).length_packWord,
      ShrunkHashInput.unpackWord_packWord, ShrunkHashInput.mk.injEq,
      InputHashedInput.mk.injEq] at hpk
    exact Prod.ext hpk.1.1 (Prod.ext hpk.1.2 hpk.2)
  · simp only [Fintype.card_prod, Fintype.card_pi, Fintype.card_bool, Fintype.card_fin,
      Finset.prod_const, Finset.card_univ, shrunkHashInLen, inputHashInLen, Cslib.BitString,
      ← pow_mul, ← pow_add, Nat.mul_comm, add_assoc]
  · simp only [Cslib.BitString.ofFn_ofList (ShrunkHashInput.mk ⟨t.1, t.2.1⟩ t.2.2).length_packWord]

private theorem uniformList_mul_eq_map_blocks (k m : ℕ) :
    Cslib.BitString.uniformList (k * m) =
      (PMF.uniformOfFintype (Fin k → BitString m)).map
        (fun rows => List.ofFn (Cslib.BitString.blocksEquiv.symm rows)) := by
  rw [Cslib.BitString.uniformList]
  relabel_uniform (Cslib.BitString.blocksEquiv (m := k) (k := m)).symm

private abbrev shrunkBadIn {w₁ out₁ : ℕ} (f₁ : BitString w₁ → BitString out₁) (j₀ : ℕ)
    (L : BitString w₁ → Finset (BitString w₁)) (z : BitString w₁)
    (iRows : Fin w₁ → BitString w₁) : Prop :=
  ∃ z' ∈ L z, z' ≠ z ∧ inputHashFin f₁ j₀ ⟨z', iRows⟩ = inputHashFin f₁ j₀ ⟨z, iRows⟩

private abbrev shrunkBadOut {w₁ out₁ s : ℕ} (f₁ : BitString w₁ → BitString out₁) (j₀ : ℕ)
    (w : InputHashedInput w₁)
    (oRows : Fin (outHashLen w₁ s) → BitString (inputHashOutLen w₁ out₁)) : Prop :=
  ∃ w' : InputHashedInput w₁,
    inputHashFin f₁ j₀ w' ≠ inputHashFin f₁ j₀ w ∧
    shrunkHashFin f₁ j₀ s ⟨w', oRows⟩ = shrunkHashFin f₁ j₀ s ⟨w, oRows⟩

private abbrev shrunkCollPred (w₁ out₁ j₀ s : ℕ) (evalWord₁ : List Bool → List Bool)
    (v : ShrunkHashInput w₁ out₁ s) (raw : List Bool) : Prop :=
  raw.length = shrunkHashInLen w₁ out₁ s ∧ raw ≠ v.packWord ∧
    shrunkHashEvalWord w₁ out₁ evalWord₁ j₀ s raw =
      shrunkHashEvalWord w₁ out₁ evalWord₁ j₀ s v.packWord

private abbrev shrunkEscPred (w₁ : ℕ) (evalWord₁ : List Bool → List Bool)
    (L : BitString w₁ → Finset (BitString w₁)) (z : BitString w₁) (raw : List Bool) : Prop :=
  let xRaw := raw.take w₁
  xRaw.length = w₁ ∧ evalWord₁ xRaw = evalWord₁ (List.ofFn z) ∧
    Cslib.BitString.ofList w₁ xRaw ∉ L z

private theorem shrunkCollPred_imp_shrunkEscPred {w₁ out₁ j₀ s : ℕ}
    (evalWord₁ : List Bool → List Bool)
    (L : BitString w₁ → Finset (BitString w₁))
    (hlen₁ : ∀ u : List Bool, u.length = w₁ → (evalWord₁ u).length = out₁)
    (z : BitString w₁) (iRows : Fin w₁ → BitString w₁)
    (oRows : Fin (outHashLen w₁ s) → BitString (inputHashOutLen w₁ out₁))
    (hnot_in : ¬ shrunkBadIn (wordToFinMap w₁ out₁ evalWord₁) j₀ L z iRows)
    (hnot_out : ¬ shrunkBadOut (wordToFinMap w₁ out₁ evalWord₁) j₀ ⟨z, iRows⟩ oRows)
    (raw : List Bool) (hcoll : shrunkCollPred w₁ out₁ j₀ s evalWord₁ ⟨⟨z, iRows⟩, oRows⟩ raw) :
    shrunkEscPred w₁ evalWord₁ L z raw := by
  let f₁ := wordToFinMap w₁ out₁ evalWord₁
  rcases hcoll with ⟨hlen_raw, hne_raw, heval_raw⟩
  let v : ShrunkHashInput w₁ out₁ s := ⟨⟨z, iRows⟩, oRows⟩
  let v' := ShrunkHashInput.unpackWord w₁ out₁ s raw
  have hpack' : v'.packWord = raw := ShrunkHashInput.packWord_unpackWord hlen_raw
  have hf₃_eq : shrunkHashFin f₁ j₀ s v' = shrunkHashFin f₁ j₀ s v := by
    have hp : (shrunkHashFin f₁ j₀ s v').packWord = (shrunkHashFin f₁ j₀ s v).packWord := by
      rw [← shrunkHashEvalWord_packWord evalWord₁ j₀ v',
        ← shrunkHashEvalWord_packWord evalWord₁ j₀ v, hpack', heval_raw]
    simpa only [ShrunkHashOutput.unpackWord_packWord] using
      congrArg (ShrunkHashOutput.unpackWord w₁ out₁ s) hp
  have hoRows_eq : v'.outRows = oRows := congrArg ShrunkHashOutput.outRows hf₃_eq
  have hf₂_eq : inputHashFin f₁ j₀ v'.inner = inputHashFin f₁ j₀ ⟨z, iRows⟩ :=
    Classical.byContradiction fun hne₂ => hnot_out ⟨v'.inner, hne₂,
      by rwa [show (⟨v'.inner, oRows⟩ : ShrunkHashInput _ _ _) = v' by rw [← hoRows_eq]]⟩
  have hiRows_eq : v'.inner.inRows = iRows := congrArg InputHashedOutput.inRows hf₂_eq
  have hz_ne : v'.inner.base ≠ z := fun hz_eq => hne_raw <| by
    rw [← hpack']
    rcases v' with ⟨⟨_, _⟩, _⟩
    dsimp only at hz_eq hiRows_eq hoRows_eq
    subst hz_eq hiRows_eq hoRows_eq; rfl
  have htake_eq : raw.take w₁ = List.ofFn v'.inner.base := by
    rw [← hpack', ShrunkHashInput.packWord, InputHashedInput.packWord, List.append_assoc,
      List.take_left' List.length_ofFn]
  have heval₁_eq : evalWord₁ (List.ofFn v'.inner.base) = evalWord₁ (List.ofFn z) := by
    rw [← Cslib.BitString.ofFn_ofList (hlen₁ _ List.length_ofFn),
      ← Cslib.BitString.ofFn_ofList (hlen₁ (List.ofFn z) List.length_ofFn)]
    exact congrArg List.ofFn (congrArg InputHashedOutput.baseOut hf₂_eq)
  have hnot_L₁ : v'.inner.base ∉ L z := fun hmem =>
    hnot_in ⟨v'.inner.base, hmem, hz_ne,
      by rwa [show (⟨v'.inner.base, iRows⟩ : InputHashedInput _) = v'.inner by rw [← hiRows_eq]]⟩
  simpa only [shrunkEscPred, htake_eq, List.length_ofFn, heval₁_eq, Cslib.BitString.ofList_ofFn,
    true_and] using hnot_L₁

open Classical in
private theorem shrunkHash_pointwise_toReal_le {w₁ out₁ j₀ s : ℕ}
    (evalWord₁ : List Bool → List Bool)
    (L : BitString w₁ → Finset (BitString w₁))
    (hlen₁ : ∀ u : List Bool, u.length = w₁ → (evalWord₁ u).length = out₁)
    (pA : PMF (List Bool)) (z : BitString w₁) (iRows : Fin w₁ → BitString w₁)
    (oRows : Fin (outHashLen w₁ s) → BitString (inputHashOutLen w₁ out₁)) :
    ((pA >>= fun raw =>
        PMF.pure (decide (shrunkCollPred w₁ out₁ j₀ s evalWord₁ ⟨⟨z, iRows⟩, oRows⟩ raw)))
      true).toReal ≤
      ((pA >>= fun raw => PMF.pure (decide (shrunkEscPred w₁ evalWord₁ L z raw))) true).toReal +
      (if shrunkBadIn (wordToFinMap w₁ out₁ evalWord₁) j₀ L z iRows then 1 else 0) +
      (if shrunkBadOut (wordToFinMap w₁ out₁ evalWord₁) j₀ ⟨z, iRows⟩ oRows then 1 else 0) := by
  have h1 := PMF.toReal_apply_le_one (pA >>= fun raw =>
    PMF.pure (decide (shrunkCollPred w₁ out₁ j₀ s evalWord₁ ⟨⟨z, iRows⟩, oRows⟩ raw))) true
  have h0 := ENNReal.toReal_nonneg (a := (pA >>= fun raw =>
    PMF.pure (decide (shrunkEscPred w₁ evalWord₁ L z raw))) true)
  by_cases hin : shrunkBadIn (wordToFinMap w₁ out₁ evalWord₁) j₀ L z iRows
  · simp only [hin, ↓reduceIte]; split_ifs <;> linarith
  · by_cases hout : shrunkBadOut (wordToFinMap w₁ out₁ evalWord₁) j₀ ⟨z, iRows⟩ oRows
    · simp only [hin, hout, ↓reduceIte]; linarith
    · simp only [hin, hout, ↓reduceIte, add_zero, PMF.monad_bind_eq_bind]
      refine ENNReal.toReal_mono (PMF.apply_ne_top _ _)
        (PMF.bind_apply_mono_on_support pA true fun raw _ => ?_)
      by_cases hc : shrunkCollPred w₁ out₁ j₀ s evalWord₁ ⟨⟨z, iRows⟩, oRows⟩ raw
      · simp [hc, shrunkCollPred_imp_shrunkEscPred evalWord₁ L hlen₁ z iRows oRows hin hout raw hc]
      · simp [hc]

private noncomputable abbrev shrunkExpect (w₁ out₁ s : ℕ)
    (g : BitString w₁ → (Fin w₁ → BitString w₁) →
      (Fin (outHashLen w₁ s) → BitString (inputHashOutLen w₁ out₁)) → ℝ) : ℝ :=
  ∑ z : BitString w₁, ((PMF.uniformOfFintype (BitString w₁)) z).toReal *
    ∑ iRows : Fin w₁ → BitString w₁,
      ((PMF.uniformOfFintype (Fin w₁ → BitString w₁)) iRows).toReal *
      ∑ oRows : Fin (outHashLen w₁ s) → BitString (inputHashOutLen w₁ out₁),
        ((PMF.uniformOfFintype _) oRows).toReal * g z iRows oRows

open Classical in
private theorem shrunkHash_randomCollision_succProbability_eq (n₁ m₁ j s : ℕ → ℕ)
    (evalWord₁ : ℕ → List Bool → List Bool)
    (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ) :
    (Game.succProbability (ProbComp.eval
      (randomCollisionGame
        (fun k => shrunkHashEvalWord (n₁ k) (m₁ k) (evalWord₁ k) (j k) (s k))
        (fun k => shrunkHashInLen (n₁ k) (m₁ k) (s k)) A n)) : ℝ) =
      shrunkExpect (n₁ n) (m₁ n) (s n) fun z iRows oRows =>
        ((ProbComp.eval (A n (ShrunkHashInput.mk ⟨z, iRows⟩ oRows).packWord) >>= fun raw =>
          PMF.pure (decide (shrunkCollPred (n₁ n) (m₁ n) (j n) (s n) (evalWord₁ n)
            ⟨⟨z, iRows⟩, oRows⟩ raw))) true).toReal := by
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, randomCollisionGame,
    ProbComp.eval_bind, Cslib.BitString.eval_sampleList, ProbComp.eval_pure]
  rw [uniformList_shrunkHashInLen_eq (n₁ n) (m₁ n) (s n), PMF.bind_bind]
  simp only [PMF.bind_apply_toReal]
  refine sum_congr rfl fun z _ => congrArg (_ * ·) ?_
  rw [PMF.bind_bind]
  simp only [PMF.bind_apply_toReal]
  exact sum_congr rfl fun _ _ => congrArg (_ * ·) (by rw [PMF.bind_map, PMF.bind_apply_toReal]; rfl)

open Classical in
private theorem shrunkHash_escape_succProbability_eq (n₁ m₁ s : ℕ → ℕ)
    (evalWord₁ : ℕ → List Bool → List Bool)
    (L₁ : (n : ℕ) → BitString (n₁ n) → Finset (BitString (n₁ n)))
    (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ) :
    (Game.succProbability (ProbComp.eval
      (accessibleEscapeGame evalWord₁ n₁ L₁ (shrunkHashEscapeInverter n₁ m₁ s A) n)) : ℝ) =
      shrunkExpect (n₁ n) (m₁ n) (s n) fun z iRows oRows =>
        ((ProbComp.eval (A n (ShrunkHashInput.mk ⟨z, iRows⟩ oRows).packWord) >>= fun raw =>
          PMF.pure (decide
            (shrunkEscPred (n₁ n) (evalWord₁ n) (L₁ n) z raw))) true).toReal := by
  have heval :
      ProbComp.eval (accessibleEscapeGame evalWord₁ n₁ L₁
        (shrunkHashEscapeInverter n₁ m₁ s A) n) =
      (PMF.uniformOfFintype (BitString (n₁ n))).bind fun z =>
        (PMF.uniformOfFintype (Fin (n₁ n) → BitString (n₁ n))).bind fun iRows =>
          (PMF.uniformOfFintype
            (Fin (outHashLen (n₁ n) (s n)) → BitString (inputHashOutLen (n₁ n) (m₁ n)))).bind
              fun oRows =>
                ProbComp.eval (A n (ShrunkHashInput.mk ⟨z, iRows⟩ oRows).packWord) >>= fun raw =>
                  PMF.pure (decide (shrunkEscPred (n₁ n) (evalWord₁ n) (L₁ n) z raw)) := by
    simp only [accessibleEscapeGame, shrunkHashEscapeInverter, ProbComp.eval_bind,
      Cslib.BitString.eval_sampleList, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
      PMF.bind_bind]
    rw [Cslib.BitString.uniformList, PMF.bind_map]
    refine congrArg (PMF.uniformOfFintype (BitString (n₁ n))).bind (funext fun z => ?_)
    dsimp only [Function.comp_def]
    rw [uniformList_mul_eq_map_blocks, PMF.bind_map]
    refine congrArg (PMF.uniformOfFintype _).bind (funext fun iRows => ?_)
    dsimp only [Function.comp_def]
    rw [uniformList_mul_eq_map_blocks, PMF.bind_map]
    refine congrArg (PMF.uniformOfFintype _).bind (funext fun oRows => ?_)
    simp only [Function.comp_def, listRow_zero_ofFn, Cslib.BitString.ofList_ofFn, PMF.pure_bind,
      ShrunkHashInput.packWord, InputHashedInput.packWord, shrunkEscPred]
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, heval, PMF.bind_apply_toReal]

open Classical in
private theorem shrunkBadIn_sum_le {w₁ out₁ j₀ s : ℕ} (f₁ : BitString w₁ → BitString out₁)
    (L : BitString w₁ → Finset (BitString w₁)) (A_max : ℝ) :
    shrunkExpect w₁ out₁ s (fun z iRows _ => if shrunkBadIn f₁ j₀ L z iRows then 1 else 0) ≤
      ((PMF.uniformOfFintype (BitString w₁)).toOuterMeasure
        {z | A_max ≤ Real.logb 2 #(L z)}).toReal +
      (2 : ℝ) ^ (A_max - (min j₀ w₁ : ℝ)) := by
  have hinner_z (z : BitString w₁) :
      (∑ iRows : Fin w₁ → BitString w₁,
        if shrunkBadIn f₁ j₀ L z iRows then
          ((PMF.uniformOfFintype (Fin w₁ → BitString w₁)) iRows).toReal
        else 0) ≤
      (if A_max ≤ Real.logb 2 #(L z) then 1 else 0) +
        (2 : ℝ) ^ (A_max - (min j₀ w₁ : ℝ)) := by
    by_cases hA_ge : A_max ≤ Real.logb 2 #(L z)
    · simp only [hA_ge, ↓reduceIte]
      have hle1 := (sum_le_sum fun iRows (_ : iRows ∈ univ) => show
          (if shrunkBadIn f₁ j₀ L z iRows then
            ((PMF.uniformOfFintype (Fin w₁ → BitString w₁)) iRows).toReal else 0) ≤
            ((PMF.uniformOfFintype (Fin w₁ → BitString w₁)) iRows).toReal by
        split_ifs <;> simp).trans_eq (PMF.sum_toReal _)
      linarith [Real.rpow_nonneg two_pos.le (A_max - (min j₀ w₁ : ℝ))]
    · simp only [hA_ge, ↓reduceIte, zero_add]
      have hcard_le : (#(L z) : ℝ) ≤ (2 : ℝ) ^ A_max := by
        rcases Nat.eq_zero_or_pos #(L z) with h0 | hpos
        · simp [h0, Real.rpow_nonneg two_pos.le]
        · exact (Real.logb_le_iff_le_rpow one_lt_two (by exact_mod_cast hpos)).mp
            (not_le.mp hA_ge).le
      refine (inputHashFin_accessible_collision_le f₁ j₀ (L z) z).trans ?_
      rw [Real.rpow_sub two_pos, ← Nat.cast_min, Real.rpow_natCast]
      gcongr
  calc
    shrunkExpect w₁ out₁ s (fun z iRows _ => if shrunkBadIn f₁ j₀ L z iRows then 1 else 0)
      = ∑ z : BitString w₁, ((PMF.uniformOfFintype (BitString w₁)) z).toReal *
          ∑ iRows : Fin w₁ → BitString w₁,
            if shrunkBadIn f₁ j₀ L z iRows then
              ((PMF.uniformOfFintype (Fin w₁ → BitString w₁)) iRows).toReal
            else 0 := by
        simp only [shrunkExpect, ← sum_mul, PMF.sum_toReal, one_mul]
        simp only [mul_boole]
    _ ≤ ∑ z : BitString w₁, ((PMF.uniformOfFintype (BitString w₁)) z).toReal *
          ((if z ∈ {z : BitString w₁ | A_max ≤ Real.logb 2 #(L z)} then (1 : ℝ) else 0) +
            (2 : ℝ) ^ (A_max - (min j₀ w₁ : ℝ))) :=
        sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hinner_z z) ENNReal.toReal_nonneg
    _ = ((PMF.uniformOfFintype (BitString w₁)).toOuterMeasure
          {z | A_max ≤ Real.logb 2 #(L z)}).toReal +
        (2 : ℝ) ^ (A_max - (min j₀ w₁ : ℝ)) := by
        simp only [mul_add, sum_add_distrib, ← sum_mul, PMF.sum_toReal, one_mul,
          ← PMF.toOuterMeasure_toReal_eq_sum_ite]

open Classical in
private theorem shrunkBadOut_sum_le {w₁ out₁ j₀ s : ℕ} (hs : s ≤ inputHashInLen w₁)
    (f₁ : BitString w₁ → BitString out₁) (K_min : ℝ) :
    shrunkExpect w₁ out₁ s (fun z iRows oRows =>
        if shrunkBadOut f₁ j₀ ⟨z, iRows⟩ oRows then 1 else 0) ≤
      (2 : ℝ) ^ s * (((PMF.uniformOfFintype (BitString w₁)).toOuterMeasure
          {z | realSampleEntropy f₁ z ≤ K_min}).toReal +
        (2 : ℝ) ^ ((min j₀ w₁ : ℝ) - K_min)) := by
  have hpow_ratio :
      (2 : ℝ) ^ inputHashInLen w₁ / (2 : ℝ) ^ outHashLen w₁ s = (2 : ℝ) ^ s := by
    rw [← Nat.sub_add_cancel hs, pow_add]
    exact mul_div_cancel_left₀ _ (by positivity)
  let C := (2 : ℝ) ^ s * (((PMF.uniformOfFintype (BitString w₁)).toOuterMeasure
      {z | realSampleEntropy f₁ z ≤ K_min}).toReal + (2 : ℝ) ^ ((min j₀ w₁ : ℝ) - K_min))
  have hper_w (z : BitString w₁) (iRows : Fin w₁ → BitString w₁) :
      (∑ oRows : Fin (outHashLen w₁ s) → BitString (inputHashOutLen w₁ out₁),
        ((PMF.uniformOfFintype _) oRows).toReal *
          (if shrunkBadOut f₁ j₀ ⟨z, iRows⟩ oRows then 1 else 0)) ≤ C := by
    simp only [mul_boole]
    refine (shrunkHashFin_false_positive_le f₁ j₀ s ⟨z, iRows⟩).trans ?_
    calc
      (#(univ.image (inputHashFin f₁ j₀)) : ℝ) / (2 : ℝ) ^ outHashLen w₁ s
        ≤ ((((PMF.uniformOfFintype (BitString w₁)).toOuterMeasure
              {z | realSampleEntropy f₁ z ≤ K_min}).toReal +
            (2 : ℝ) ^ ((min j₀ w₁ : ℝ) - K_min)) * (2 : ℝ) ^ inputHashInLen w₁) /
            (2 : ℝ) ^ outHashLen w₁ s := by
          gcongr; exact card_image_inputHashFin_le f₁ j₀ K_min
      _ = C := by rw [mul_div_assoc, hpow_ratio, mul_comm]
  calc
    shrunkExpect w₁ out₁ s (fun z iRows oRows =>
        if shrunkBadOut f₁ j₀ ⟨z, iRows⟩ oRows then 1 else 0)
      ≤ ∑ z : BitString w₁, ((PMF.uniformOfFintype (BitString w₁)) z).toReal *
          ∑ iRows : Fin w₁ → BitString w₁,
            ((PMF.uniformOfFintype (Fin w₁ → BitString w₁)) iRows).toReal * C := by
        dsimp only [shrunkExpect]
        gcongr with z _ iRows _
        exact hper_w z iRows
    _ = C := by simp only [← sum_mul, PMF.sum_toReal, one_mul]

private theorem shrunkExpect_le_add3 {w₁ out₁ s : ℕ}
    {f g₁ g₂ g₃ : BitString w₁ → (Fin w₁ → BitString w₁) →
      (Fin (outHashLen w₁ s) → BitString (inputHashOutLen w₁ out₁)) → ℝ}
    (h : ∀ z iRows oRows,
      f z iRows oRows ≤ g₁ z iRows oRows + g₂ z iRows oRows + g₃ z iRows oRows) :
    shrunkExpect w₁ out₁ s f ≤
      shrunkExpect w₁ out₁ s g₁ + shrunkExpect w₁ out₁ s g₂ + shrunkExpect w₁ out₁ s g₃ := by
  calc
    shrunkExpect w₁ out₁ s f
      ≤ shrunkExpect w₁ out₁ s (fun z i o => g₁ z i o + g₂ z i o + g₃ z i o) := by
        dsimp only [shrunkExpect]; gcongr with z _ i _ o _; exact h z i o
    _ = _ := by simp only [shrunkExpect, mul_add, sum_add_distrib]

/-- **Combined concrete bound for `[HHRVW2020]`, Sections 5.1.2–5.1.3, Lemmas 5.4 and 5.5
(pp. 27–29)**: when `s n ≤ inputHashInLen (n₁ n)`, random-input collision success on
`shrunkHashEvalWord` at truncation parameter `j n` and shrinkage `s n` is bounded by the
$L_1$-escape probability of `shrunkHashEscapeInverter` plus the two concentration tails
(`A_max ≤ log₂ |L₁(z)|` and `realSampleEntropy f₁ z ≤ K_min`) and the two universal-hash error
terms `2 ^ (A_max - min (j n) (n₁ n))` and `2 ^ (s n) * 2 ^ (min (j n) (n₁ n) - K_min)`. -/
theorem shrunkHash_randomCollision_le (n₁ m₁ j s : ℕ → ℕ)
    (evalWord₁ : ℕ → List Bool → List Bool)
    (L₁ : (n : ℕ) → BitString (n₁ n) → Finset (BitString (n₁ n)))
    (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ)
    (hs : s n ≤ inputHashInLen (n₁ n))
    (hlen₁ : ∀ u : List Bool, u.length = n₁ n → (evalWord₁ n u).length = m₁ n)
    (A_max K_min : ℝ) :
    let f₁ := wordToFinMap (n₁ n) (m₁ n) (evalWord₁ n)
    (Game.succProbability (ProbComp.eval
      (randomCollisionGame
        (fun k => shrunkHashEvalWord (n₁ k) (m₁ k) (evalWord₁ k) (j k) (s k))
        (fun k => shrunkHashInLen (n₁ k) (m₁ k) (s k)) A n)) : ℝ) ≤
      (Game.succProbability (ProbComp.eval
        (accessibleEscapeGame evalWord₁ n₁ L₁ (shrunkHashEscapeInverter n₁ m₁ s A) n)) : ℝ) +
      ((PMF.uniformOfFintype (BitString (n₁ n))).toOuterMeasure
        {z | A_max ≤ Real.logb 2 #(L₁ n z)}).toReal +
      (2 : ℝ) ^ (A_max - (min (j n) (n₁ n) : ℝ)) +
      (2 : ℝ) ^ (s n) * (((PMF.uniformOfFintype (BitString (n₁ n))).toOuterMeasure
          {z | realSampleEntropy f₁ z ≤ K_min}).toReal +
        (2 : ℝ) ^ ((min (j n) (n₁ n) : ℝ) - K_min)) := by
  intro f₁
  classical
  rw [shrunkHash_randomCollision_succProbability_eq n₁ m₁ j s evalWord₁ A n,
    shrunkHash_escape_succProbability_eq n₁ m₁ s evalWord₁ L₁ A n]
  have hle := shrunkExpect_le_add3 fun z iRows oRows =>
    shrunkHash_pointwise_toReal_le (j₀ := j n) (s := s n) (evalWord₁ n) (L₁ n) hlen₁
      (ProbComp.eval (A n (ShrunkHashInput.mk ⟨z, iRows⟩ oRows).packWord)) z iRows oRows
  linarith [hle, shrunkBadIn_sum_le (j₀ := j n) (s := s n) f₁ (L₁ n) A_max,
    shrunkBadOut_sum_le (j₀ := j n) hs f₁ K_min]

end Cslib.Crypto
