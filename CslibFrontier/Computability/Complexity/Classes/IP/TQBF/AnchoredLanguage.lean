/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.IP.TQBF
public import CslibFrontier.Computability.Complexity.Classes.IP.TQBF.ValueInstance
public import Mathlib.Computability.Language

/-!
# The language of bits of values of subformulas of an arithmetization

The validity of a value instance (`Cslib.Complexity.QBFProtocol.ValueInstance.ValidFor`)
involves `e.maxRoundDegree ≤ D`, which is hard to decide in polynomial time from the tokens
alone. This file anchors every instance to its source formula `ψ`, so that validity is decidable in
polynomial time. The language is the base of the structured language that
[MurrayWilliams2018], Theorem 3.1, uses; the properties of [MurrayWilliams2018], Theorem 2.2, that
it needs (not `PSPACE` membership) are proved in the files that import this one.

An *anchored instance* (`Cslib.Complexity.QBFProtocol.AnchoredInstance`) is a closed quantified
Boolean formula `ψ`, a block of the tokens of the arithmetization `arithOf ψ`, a point and a bit
index. The block is given by its start and its length, so that the tokens of a subformula, which
are a block of the tokens of the whole formula in prefix order, need not be written out: a block
is valid when it begins where a subformula begins and has the length of that subformula
(`Cslib.Complexity.QBFProtocol.exists_isSub_drop_tokens`). A valid instance is then a valid
value instance for that subformula
(`Cslib.Complexity.QBFProtocol.AnchoredInstance.Valid.validFor`).

* **Encoding.** The start, the point values and the bit are written as words of fixed width, as
  many `true`s as the number followed by `false`s (`Cslib.Complexity.QBFProtocol.padUnary`), the
  length in unary. The length of the word of a valid instance depends only on `ψ` and the length
  of its block (`Cslib.Complexity.QBFProtocol.length_encAnchored`), so that the instance of a
  strictly smaller block, for any point and bit, has a strictly shorter word
  (`Cslib.Complexity.QBFProtocol.length_encAnchored_lt`).
* **Children.** The blocks of the arguments of a subformula are found from the block of the
  subformula (`Cslib.Complexity.QBFProtocol.AnchoredInstance.IsFor.not`, `.bin_left`,
  `.bin_right`, `.op`), and every instance whose block is that of a subformula is valid, whatever
  its point and bit (`Cslib.Complexity.QBFProtocol.AnchoredInstance.IsFor.valid`).
* **The languages.** `Cslib.Complexity.QBFProtocol.anchoredBase` holds the words of the valid
  instances whose value has the bit set, and `Cslib.Complexity.QBFProtocol.anchoredLanguage` is
  its padding by leading `true`s.

## Main definitions

* `Cslib.Complexity.QBFProtocol.AnchoredInstance`, `Cslib.Complexity.QBFProtocol.encAnchored`
* `Cslib.Complexity.QBFProtocol.AnchoredInstance.Valid`
* `Cslib.Complexity.QBFProtocol.AnchoredInstance.toValue`
* `Cslib.Complexity.QBFProtocol.anchoredBase`, `Cslib.Complexity.QBFProtocol.anchoredLanguage`
* `Cslib.Complexity.QBFProtocol.stripWord`: a word without its leading `true`s.

## Main results

* `Cslib.Complexity.QBFProtocol.length_encAnchored`,
  `Cslib.Complexity.QBFProtocol.length_encAnchored_lt`: the lengths of the words of instances.
* `Cslib.Complexity.QBFProtocol.AnchoredInstance.Valid.validFor`: a valid instance is a valid
  value instance.
* `Cslib.Complexity.QBFProtocol.AnchoredInstance.IsFor.length_lt`: the children of a valid
  instance are valid and have shorter words.
* `Cslib.Complexity.QBFProtocol.cons_false_mem_anchoredLanguage`,
  `Cslib.Complexity.QBFProtocol.encAnchored_mem_anchoredBase`: membership in the languages.

## References

* [C. D. Murray, R. R. Williams, *Circuit lower bounds for nondeterministic quasi-polytime: an
  easy witness lemma for NP and NQP*][MurrayWilliams2018], Theorem 2.2
* [R. Santhanam, *Circuit lower bounds for Merlin–Arthur classes*][Santhanam2009]
* [L. Trevisan, S. Vadhan, *Pseudorandomness and average-case complexity via uniform
  reductions*][TrevisanVadhan2007]
-/

public section

namespace Cslib.Complexity.QBFProtocol

open Cslib.Logic.PL Turing.MultiTapeTM Machine

/-! ### Anchored instances -/

/-- **An anchored instance**: a quantified Boolean formula `ψ`, the block of the tokens of its
arithmetization `(loopInput ψ).tokens` that starts at `start` and has length `len`, the values of
the point on the variables of `(loopInput ψ).xs` in order, and the index of the bit asked for. -/
structure AnchoredInstance where
  /-- The quantified Boolean formula that the instance is anchored to. -/
  formula : QBF ℕ
  /-- The position in the tokens of the arithmetization where the block starts. -/
  start : ℕ
  /-- The number of tokens of the block. -/
  len : ℕ
  /-- The values of the point, one for every variable of `(loopInput formula).xs`. -/
  point : List ℕ
  /-- The index of the bit of the value that the instance asks for. -/
  bit : ℕ

namespace AnchoredInstance

/-- The tokens of the block of an instance. -/
@[expose] def tokens (I : AnchoredInstance) : List (ArithQBF.Kind × ℕ) :=
  ((loopInput I.formula).tokens.drop I.start).take I.len

/-- The block of an instance is that of the formula `e`: the tokens from its start begin with those
of `e`, and its length is that of `e`. -/
@[expose] def IsFor (I : AnchoredInstance) (e : ArithQBF ℕ) : Prop :=
  ∃ rest, (loopInput I.formula).tokens.drop I.start = e.tokens ++ rest ∧
    I.len = e.tokens.length

/-- **Validity of an anchored instance**: the formula is closed, the block begins inside the tokens
and has the length of the formula that begins there, and the point and the bit are in range. -/
structure Valid (I : AnchoredInstance) : Prop where
  /-- The formula is closed. -/
  closed : I.formula.Closed
  /-- The block begins inside the tokens of the arithmetization. -/
  start_lt : I.start < (loopInput I.formula).tokens.length
  /-- The block has the length of the first formula of the tokens from its start. -/
  firstLen_eq : firstLen ((loopInput I.formula).tokens.drop I.start) = I.len
  /-- There is one value for every variable of `xs`. -/
  point_length : I.point.length = (loopInput I.formula).xs.length
  /-- Every value is below the modulus. -/
  point_lt : ∀ v ∈ I.point, v < modulus I.formula
  /-- The bit index is below the modulus. -/
  bit_lt : I.bit < modulus I.formula

/-- The instance of the value language that an anchored instance stands for: the parameters of
the machine on `ψ`, with the tokens of the block, the point and the bit. -/
@[expose] def toValue (I : AnchoredInstance) : ValueInstance :=
  ⟨{ loopInput I.formula with tokens := I.tokens }, I.point, I.bit⟩

variable {I : AnchoredInstance} {e e' : ArithQBF ℕ}

/-- The block of an instance for `e` consists of the tokens of `e`. -/
theorem IsFor.tokens_eq (h : I.IsFor e) : I.tokens = e.tokens := by
  obtain ⟨rest, hd, hl⟩ := h
  unfold AnchoredInstance.tokens
  rw [hd, hl]
  simp

/-- The formula whose block an instance is, is unique. -/
theorem IsFor.unique (h : I.IsFor e) (h' : I.IsFor e') : e = e' := by
  obtain ⟨rest, hd, -⟩ := h
  obtain ⟨rest', hd', -⟩ := h'
  exact (ArithQBF.tokens_append_inj (hd.symm.trans hd')).1

/-- A valid instance is the block of a subformula of the arithmetization. -/
theorem Valid.exists_isFor (h : I.Valid) :
    ∃ e, IsSub e (arithOf I.formula) ∧ I.IsFor e := by
  have hlt : I.start < (arithOf I.formula).tokens.length := by
    rw [tokens_arithOf]
    exact h.start_lt
  obtain ⟨e, rest, hs, hd⟩ := exists_isSub_drop_tokens _ hlt
  rw [tokens_arithOf] at hd
  refine ⟨e, hs, rest, hd, ?_⟩
  have := h.firstLen_eq
  rw [hd, firstLen_tokens_append] at this
  exact this.symm

/-- **An instance whose block is that of a subformula is valid**, whatever its point and bit in
range. -/
theorem IsFor.valid (h : I.IsFor e) (hc : I.formula.Closed)
    (hlen : I.point.length = (loopInput I.formula).xs.length)
    (hlt : ∀ v ∈ I.point, v < modulus I.formula) (hbit : I.bit < modulus I.formula) :
    I.Valid := by
  obtain ⟨rest, hd, hl⟩ := h
  refine ⟨hc, ?_, ?_, hlen, hlt, hbit⟩
  · by_contra hge
    have := List.drop_eq_nil_of_le (not_lt.1 hge)
    rw [hd] at this
    exact ArithQBF.tokens_ne_nil e (List.append_eq_nil_iff.1 this).1
  · rw [hd, firstLen_tokens_append, hl]

/-- **The argument of a negation**: the instance of the block after the first token. -/
theorem IsFor.not (h : I.IsFor (ArithQBF.not e)) (pt : List ℕ) (b : ℕ) :
    ({ I with start := I.start + 1, len := I.len - 1, point := pt, bit := b } :
      AnchoredInstance).IsFor e := by
  obtain ⟨rest, hd, hl⟩ := h
  refine ⟨rest, ?_, ?_⟩
  · change (loopInput I.formula).tokens.drop (I.start + 1) = e.tokens ++ rest
    rw [← List.tail_drop, hd]
    simp [ArithQBF.tokens]
  · change I.len - 1 = e.tokens.length
    simp only [ArithQBF.tokens, List.length_cons] at hl
    omega

/-- **The first argument of a binary connective**: the instance of the block after the first
token, with the length of the first argument. -/
theorem IsFor.bin_left {o : ArithQBF.Connective} {e₁ e₂ : ArithQBF ℕ}
    (h : I.IsFor (ArithQBF.bin o e₁ e₂)) (pt : List ℕ) (b : ℕ) :
    ({ I with start := I.start + 1, len := e₁.tokens.length, point := pt, bit := b } :
      AnchoredInstance).IsFor e₁ := by
  obtain ⟨rest, hd, hl⟩ := h
  refine ⟨e₂.tokens ++ rest, ?_, rfl⟩
  change (loopInput I.formula).tokens.drop (I.start + 1) = e₁.tokens ++ (e₂.tokens ++ rest)
  rw [← List.tail_drop, hd]
  cases o <;> simp [ArithQBF.tokens]

/-- **The second argument of a binary connective**: the instance of the block after the first
argument, with the length of the second argument. -/
theorem IsFor.bin_right {o : ArithQBF.Connective} {e₁ e₂ : ArithQBF ℕ}
    (h : I.IsFor (ArithQBF.bin o e₁ e₂)) (pt : List ℕ) (b : ℕ) :
    ({ I with
        start := I.start + 1 + e₁.tokens.length
        len := e₂.tokens.length
        point := pt
        bit := b } : AnchoredInstance).IsFor e₂ := by
  obtain ⟨rest, hd, hl⟩ := h
  refine ⟨rest, ?_, rfl⟩
  change (loopInput I.formula).tokens.drop (I.start + 1 + e₁.tokens.length) = e₂.tokens ++ rest
  have h1 : (loopInput I.formula).tokens.drop (I.start + 1) = e₁.tokens ++ (e₂.tokens ++ rest) := by
    rw [← List.tail_drop, hd]
    cases o <;> simp [ArithQBF.tokens]
  rw [← List.drop_drop, h1, List.drop_left' rfl]

/-- **The body of an operator**: the instance of the block after the first token. -/
theorem IsFor.op {o : ArithQBF.Operator} {v : ℕ} (h : I.IsFor (ArithQBF.op o v e)) (pt : List ℕ)
    (b : ℕ) :
    ({ I with start := I.start + 1, len := I.len - 1, point := pt, bit := b } :
      AnchoredInstance).IsFor e := by
  obtain ⟨rest, hd, hl⟩ := h
  refine ⟨rest, ?_, ?_⟩
  · change (loopInput I.formula).tokens.drop (I.start + 1) = e.tokens ++ rest
    rw [← List.tail_drop, hd]
    cases o <;> simp [ArithQBF.tokens]
  · change I.len - 1 = e.tokens.length
    cases o <;> simp only [ArithQBF.tokens, List.length_cons] at hl <;> omega

/-- **A valid anchored instance is a valid instance of the value language** for every subformula
of the arithmetization whose block it is. -/
theorem Valid.validFor (hI : I.Valid) (hsub : IsSub e (arithOf I.formula)) (hf : I.IsFor e) :
    I.toValue.ValidFor e := by
  have hmod : (loopInput I.formula).modulus = modulus I.formula := modulus_loopInput _
  have hops : e.ops ≤ (I.formula.tokens.length + 1) * I.formula.tokens.length := by
    have h1 := QBF.ops_arithmetize_le (linVars I.formula) I.formula
    have h2 : (linVars I.formula).length = I.formula.tokens.length := by simp [linVars]
    rw [h2, ← QBF.length_tokens] at h1
    exact (IsSub.ops_le hsub).trans h1
  have hbound := lt_modulus I.formula
  set s := I.formula.tokens.length with hs
  refine ⟨hf.tokens_eq, ?_, ?_, ?_, ?_, ?_, hI.point_length, ?_, ?_⟩
  · change ((loopInput I.formula).modulus).Prime
    rw [hmod]
    exact (prime_modulus I.formula).1
  · change 6 * e.ops * (2 * s) + 1 ≤ (loopInput I.formula).modulus
    rw [hmod]
    have h2 : 6 * e.ops * (2 * s) ≤ 6 * (((s + 1) * s) * (2 * s)) := by
      rw [mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hops)
    have h3 : 6 * (((s + 1) * s) * (2 * s)) = primeBound I.formula := by
      unfold primeBound
      rw [← hs]
      ring
    omega
  · exact (IsSub.maxRoundDegree_le hsub).trans (maxRoundDegree_arithOf I.formula)
  · change 2 * s < (loopInput I.formula).modulus
    rw [hmod]
    have h2 : s ≤ s * s := Nat.le_mul_self s
    have h3 : primeBound I.formula = 12 * s ^ 2 * (s + 1) := by
      unfold primeBound
      rw [← hs]
    have h4 : 0 ≤ s ^ 3 := Nat.zero_le _
    nlinarith
  · exact fun w hw => vars_arithOf I.formula (IsSub.vars_subset hsub w hw)
  · change ∀ v ∈ I.point, v < (loopInput I.formula).modulus
    rw [hmod]
    exact hI.point_lt
  · change I.bit < (loopInput I.formula).modulus
    rw [hmod]
    exact hI.bit_lt

end AnchoredInstance

/-! ### The fields of the word of an instance -/

/-- The fields of an anchored instance as read from its word: the formula, the padded start, the
length, the padded point values and the padded bit. -/
abbrev RawInstance := QBF ℕ × List Bool × ℕ × List (List Bool) × List Bool

/-- The formula of the raw fields of an instance. -/
abbrev RawInstance.formula (r : RawInstance) : QBF ℕ := r.1

/-- The padded start of the raw fields of an instance. -/
abbrev RawInstance.start (r : RawInstance) : List Bool := r.2.1

/-- The length of the raw fields of an instance. -/
abbrev RawInstance.len (r : RawInstance) : ℕ := r.2.2.1

/-- The padded point values of the raw fields of an instance. -/
abbrev RawInstance.point (r : RawInstance) : List (List Bool) := r.2.2.2.1

/-- The padded bit of the raw fields of an instance. -/
abbrev RawInstance.bit (r : RawInstance) : List Bool := r.2.2.2.2

/-- The encoding of the raw fields of an anchored instance: the formula, the start padded to
`(loopInput formula).tokens.length` bits, the length in unary, the framed list of the point values
padded to `modulus formula` bits, and the bit padded likewise, each framed by `encPair`. -/
abbrev encRaw : RawInstance ↪ List Bool :=
  encPair encQBF (encPair encBits (encPair encUnary (encPair (encList encBits) encBits)))

/-- The fields of the word of an instance. -/
@[expose] def AnchoredInstance.rawOf (I : AnchoredInstance) : RawInstance :=
  (I.formula, padUnary (loopInput I.formula).tokens.length I.start, I.len,
    I.point.map (padUnary (modulus I.formula)), padUnary (modulus I.formula) I.bit)

/-- The instance with the given raw fields, counting the `true`s of the padded numbers. -/
@[expose] def RawInstance.toInstance (r : RawInstance) : AnchoredInstance :=
  ⟨r.formula, r.start.count true, r.len, r.point.map (List.count true), r.bit.count true⟩

/-- The number of `true`s of a padded number. -/
theorem count_padUnary (m v : ℕ) : (padUnary m v).count true = v := by
  simp [padUnary, List.count_append, List.count_replicate]

/-- Counting the `true`s inverts the padding of the fields. -/
theorem AnchoredInstance.rawOf_toInstance (I : AnchoredInstance) : I.rawOf.toInstance = I := by
  obtain ⟨ψ, s, l, pt, b⟩ := I
  simp [RawInstance.toInstance, AnchoredInstance.rawOf, RawInstance.formula, RawInstance.start,
    RawInstance.len, RawInstance.point, RawInstance.bit, count_padUnary, List.map_map,
    Function.comp_def]

namespace AnchoredInstance

/-! ### Encoding -/

/-- The word of an anchored instance: its raw fields (`rawOf`) under `encRaw`. -/
@[expose] def word (I : AnchoredInstance) : List Bool := encRaw I.rawOf

end AnchoredInstance

/-- **The encoding of anchored instances.** The start, every point value and the bit are written
in unary padded to a width determined by the formula (`padUnary`), so that the length depends
only on the formula and the length of the block when they are in range. -/
@[expose] def encAnchored : AnchoredInstance ↪ List Bool :=
  ⟨AnchoredInstance.word, fun a b h => by
    rw [← AnchoredInstance.rawOf_toInstance a, ← AnchoredInstance.rawOf_toInstance b,
      encRaw.injective h]⟩

/-- The length of the word of a valid anchored instance with formula `ψ` and a block of `len`
tokens. -/
@[expose] def anchoredLength (ψ : QBF ℕ) (len : ℕ) : ℕ :=
  2 * (encQBF ψ).length + 1 + (2 * (loopInput ψ).tokens.length + 1 + (2 * len + 1 +
    (2 * ((loopInput ψ).xs.length * (2 * modulus ψ + 1)) + 1 + modulus ψ)))

/-- **The length of an encoding depends on the formula and the block alone**: a valid instance has
an encoding of length `anchoredLength`. -/
theorem length_encAnchored {I : AnchoredInstance} (h : I.Valid) :
    (encAnchored I).length = anchoredLength I.formula I.len := by
  have hl : (encList encBits (I.point.map (padUnary (modulus I.formula)))).length =
      (loopInput I.formula).xs.length * (2 * modulus I.formula + 1) := by
    rw [length_encList_of_forall encBits _ (k := modulus I.formula), List.length_map,
      h.point_length]
    intro a ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 ha
    exact length_padUnary (h.point_lt v hv).le
  have hb := length_padUnary (m := modulus I.formula) (v := I.bit) h.bit_lt.le
  have hs := length_padUnary (m := (loopInput I.formula).tokens.length) (v := I.start)
    h.start_lt.le
  change (AnchoredInstance.word I).length = _
  simp only [AnchoredInstance.word, AnchoredInstance.rawOf, encRaw, length_encPair, hl,
    encBits_apply, hb, hs, encUnary_apply, List.length_replicate, anchoredLength]

/-- **Strictly shorter blocks give strictly shorter encodings**: for valid instances of the same
formula, any point and any bit. -/
theorem length_encAnchored_lt {I I' : AnchoredInstance} (hI : I.Valid) (hI' : I'.Valid)
    (hf : I'.formula = I.formula) (hl : I'.len < I.len) :
    (encAnchored I').length < (encAnchored I).length := by
  rw [length_encAnchored hI, length_encAnchored hI', hf]
  unfold anchoredLength
  omega

/-- **Children of valid instances have strictly shorter encodings.** An instance whose block is
that of a proper child of the subformula of a valid instance is valid for any point and bit in
range, and its encoding is strictly shorter. -/
theorem AnchoredInstance.IsFor.length_lt {I I' : AnchoredInstance} {e e' : ArithQBF ℕ}
    (hI : I.Valid) (hf : I.IsFor e) (hf' : I'.IsFor e') (hc : IsChild e' e)
    (hform : I'.formula = I.formula) (hpl : I'.point.length = (loopInput I'.formula).xs.length)
    (hpt : ∀ v ∈ I'.point, v < modulus I'.formula) (hbit : I'.bit < modulus I'.formula) :
    I'.Valid ∧ (encAnchored I').length < (encAnchored I).length := by
  have hv : I'.Valid := hf'.valid (hform ▸ hI.closed) hpl hpt hbit
  refine ⟨hv, length_encAnchored_lt hI hv hform ?_⟩
  obtain ⟨_, -, hl⟩ := hf
  obtain ⟨_, -, hl'⟩ := hf'
  rw [hl, hl']
  exact hc.tokens_sublist.2

/-! ### The languages -/

/-- **The bit of the value of an anchored instance**: the bit `bit` of the value, modulo the
modulus, of the subformula whose block the instance is, at the point of the instance. -/
@[expose] def AnchoredInstance.BitSet (I : AnchoredInstance) : Prop :=
  ∃ e, I.IsFor e ∧ (I.toValue.value e).val.testBit I.bit = true

/-- A word without its leading `true`s. -/
@[expose] def stripWord (y : List Bool) : List Bool := y.dropWhile (fun b => b = true)

/-- **The base language**: the words of the valid anchored instances whose value has the bit of the
instance set. -/
@[expose] def anchoredBase : Set (List Bool) :=
  {w | ∃ I : AnchoredInstance, I.Valid ∧ encAnchored I = w ∧ I.BitSet}

/-- **The anchored language**: the base language, padded by leading `true`s. A word is in it when
it consists of `true`s, or when after its leading `true`s comes a `false` and a word of the base
language. -/
@[expose] def anchoredLanguage : Language Bool :=
  {w | stripWord w = [] ∨ ∃ u ∈ anchoredBase, stripWord w = false :: u}

/-- The empty word is in the anchored language. -/
theorem nil_mem_anchoredLanguage : [] ∈ anchoredLanguage :=
  Or.inl rfl

/-- Prepending `true` does not change membership of the anchored language. -/
theorem cons_true_mem_anchoredLanguage (y : List Bool) :
    true :: y ∈ anchoredLanguage ↔ y ∈ anchoredLanguage := by
  unfold anchoredLanguage
  change (_ ∨ _) ↔ (_ ∨ _)
  simp only [stripWord, List.dropWhile_cons, decide_true, ↓reduceIte]

/-- Prepending any number of `true`s does not change membership of the anchored language. -/
theorem replicate_append_mem_anchoredLanguage (r : ℕ) (y : List Bool) :
    List.replicate r true ++ y ∈ anchoredLanguage ↔ y ∈ anchoredLanguage := by
  induction r with
  | zero => simp
  | succ r ih => rw [List.replicate_succ, List.cons_append, cons_true_mem_anchoredLanguage, ih]

/-- A word that begins with `false` is in the anchored language exactly when what follows is in
the base language. -/
theorem cons_false_mem_anchoredLanguage (u : List Bool) :
    false :: u ∈ anchoredLanguage ↔ u ∈ anchoredBase := by
  unfold anchoredLanguage
  change (_ ∨ _) ↔ _
  simp [stripWord]

/-- The word of a valid instance is in the base language exactly when the bit of its value is
set. -/
theorem encAnchored_mem_anchoredBase {I : AnchoredInstance} (hI : I.Valid) :
    encAnchored I ∈ anchoredBase ↔ I.BitSet := by
  constructor
  · rintro ⟨J, -, hJ, hb⟩
    obtain rfl := encAnchored.injective hJ
    exact hb
  · exact fun hb => ⟨I, hI, rfl, hb⟩

/-- The bit of the value of an instance whose block is that of `e`, in terms of `e`. -/
theorem AnchoredInstance.BitSet_iff {I : AnchoredInstance} {e : ArithQBF ℕ} (h : I.IsFor e) :
    I.BitSet ↔ (I.toValue.value e).val.testBit I.bit = true :=
  ⟨fun ⟨e', hf, hb⟩ => by obtain rfl := h.unique hf; exact hb, fun hb => ⟨e, h, hb⟩⟩

end Cslib.Complexity.QBFProtocol
