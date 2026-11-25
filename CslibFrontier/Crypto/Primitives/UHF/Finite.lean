/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Languages.Probabilistic.Basic
public import CslibFrontier.Probability.HashFamily
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Probabilistic.BoundedUniform
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Languages.Probabilistic.Semantics
import CslibFrontier.Probability.HashFamily.Collisions
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.SupportTsum
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.UniformPoint
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax

/-!
# Universal hash games with a finite key space

These experiments express the collision and difference-prediction advantages of
[BonehShoup2023], Attack Games 7.1–7.3, as probabilities of returning `true`. The challenger
keeps the uniform key private. An adversary is a closed probabilistic program with no key input.

## Main definitions

* `Cslib.Crypto.UHF.collisionExperiment`: the single-pair collision game (Attack Game 7.1).
* `Cslib.Crypto.UHF.multiQueryExperiment`: the multi-query collision game (Attack Game 7.2).
* `Cslib.Crypto.UHF.differenceExperiment`: the difference-prediction game (Attack Game 7.3).
* `Cslib.Crypto.UHF.collisionPairReduction`: turns a list of guesses into one pair.
* `Cslib.Crypto.UHF.bestCollisionGuess`: exhaustive search for a pair with maximal collision
  probability in an enumeration of the message space.

## Main results

* `Cslib.Crypto.UHF.isUniversalHash_iff_eval_collisionExperiment_le` and
  `Cslib.Crypto.UHF.isDeltaUniversalHash_iff_eval_differenceExperiment_le`: the pairwise
  predicates are equivalent to bounding the corresponding advantage for every adversary.
* `Cslib.Crypto.UHF.bestCollisionGuess_wins`: exhaustive search finds a guess that exceeds
  the proposed bound whenever a distinct pair does (Exercise 7.3).
* `Cslib.Crypto.UHF.eval_multiQueryExperiment_le_collisionPairReduction`: the finite-game
  advantage bound for the explicit wrapper, using bounded fair-bit sampling.
* `Cslib.Crypto.UHF.isPPTOn_collisionPairReduction`: the wrapper preserves strict PPT.
* `Cslib.Crypto.UHF.eval_multiQueryExperiment_le`: the statistical `C(Q, 2) * ε` bound
  for lists of length at most `Q`.

The results here concern one key distribution and one hash function at a time. The computational
collision games and asymptotic implication are in `Crypto.Primitives.UHF.Computational`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 7.1 and 7.4 and Exercise 7.3.
-/

public section

namespace Cslib.Crypto.UHF

open Cslib.Probability Turing.MultiTapeTM
open scoped ENNReal

variable {K M Y : Type}

/-- The two messages submitted to the collision game. -/
structure CollisionGuess (M : Type) where
  /-- The first message. -/
  first : M
  /-- The second message. -/
  second : M

/-- Frame the first collision message and then write the encoding of the second message. -/
enc_structure encCollisionGuess (encM : M ↪ List Bool) : CollisionGuess M where
  first : encM,
  second : encM

/-- The messages and the predicted difference of their hashes. -/
structure DifferenceGuess (M Y : Type) extends CollisionGuess M where
  /-- The predicted hash of the second message minus the hash of the first. -/
  difference : Y

/-- Attack Game 7.1 ([BonehShoup2023], v0.6, §7.1, p. 253). A guess wins when its two
distinct messages hash to the same value under an independently sampled uniform key.
The experiment rejects equal messages, which the source forbids submitting. -/
@[expose] noncomputable def collisionExperiment [Fintype K] [Nonempty K] [DecidableEq M]
    [DecidableEq Y] (H : K → M → Y) (A : ProbComp (CollisionGuess M)) : ProbComp Bool := do
  let guess ← A
  let k ← ProbComp.uniform K
  return decide (guess.first ≠ guess.second ∧ H k guess.first = H k guess.second)

/-- Attack Game 7.3 ([BonehShoup2023], v0.6, §7.4, p. 268). A guess wins when its prediction
equals the hash of the second message minus the hash of the first under a uniform key.
Equal messages are rejected. The digest space may be any additive group, encompassing
the source's cyclic group and the XOR example in Remark 7.3. -/
@[expose] noncomputable def differenceExperiment [Fintype K] [Nonempty K] [DecidableEq M]
    [AddGroup Y] [DecidableEq Y] (H : K → M → Y) (A : ProbComp (DifferenceGuess M Y)) :
    ProbComp Bool := do
  let guess ← A
  let k ← ProbComp.uniform K
  return decide (guess.first ≠ guess.second ∧
    H k guess.second - H k guess.first = guess.difference)

private theorem forall_eval_uniformGuess_le_iff {Guess : Type} [Fintype K] [Nonempty K]
    (legal : Guess → Prop) [DecidablePred legal] (wins : Guess → K → Prop)
    [∀ guess, DecidablePred (wins guess)] (ε : ℝ≥0∞) :
    (∀ A : ProbComp Guess, ((ProbComp.eval A).bind fun guess =>
      (PMF.uniformOfFintype K).bind fun k =>
        PMF.pure (decide (legal guess ∧ wins guess k))) true ≤ ε) ↔
      ∀ guess, legal guess → (PMF.uniformOfFintype K).toOuterMeasure {k | wins guess k} ≤ ε := by
  constructor
  · intro h guess hlegal
    simpa only [ProbComp.eval_pure, PMF.pure_bind, hlegal, true_and,
      Probability.PMF.bind_pure_decide_apply_true] using h (pure guess)
  · intro h A
    refine Probability.PMF.bind_apply_le_on_support _ fun guess _ => ?_
    rw [Probability.PMF.bind_pure_decide_apply_true]
    by_cases hlegal : legal guess
    · simpa only [hlegal, true_and] using h guess hlegal
    · simp [hlegal]

/-- The pairwise collision bound (7.1) is equivalent to the game bound of Definition 7.2
([BonehShoup2023], v0.6, p. 254), for one uniform-key instance and any `ε`. -/
theorem isUniversalHash_iff_eval_collisionExperiment_le [Fintype K] [Nonempty K]
    [DecidableEq M] [DecidableEq Y] (H : K → M → Y) (ε : ℝ≥0∞) :
    IsUniversalHash (PMF.uniformOfFintype K) H ε ↔
      ∀ A, ProbComp.eval (collisionExperiment H A) true ≤ ε := by
  simp only [collisionExperiment, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  rw [forall_eval_uniformGuess_le_iff]
  exact ⟨fun h guess hne => h guess.first guess.second hne, fun h m m' hne => h ⟨m, m'⟩ hne⟩

/-- The pairwise difference bound is equivalent to the game bound of Definition 7.5
([BonehShoup2023], v0.6, pp. 268–269), for one uniform-key instance and any `ε`. -/
theorem isDeltaUniversalHash_iff_eval_differenceExperiment_le [Fintype K] [Nonempty K]
    [DecidableEq M] [AddGroup Y] [DecidableEq Y] (H : K → M → Y) (ε : ℝ≥0∞) :
    IsDeltaUniversalHash (PMF.uniformOfFintype K) H ε ↔
      ∀ A, ProbComp.eval (differenceExperiment H A) true ≤ ε := by
  simp only [differenceExperiment, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  rw [forall_eval_uniformGuess_le_iff]
  exact ⟨fun h guess hne => h guess.second guess.first hne.symm guess.difference,
    fun h m m' hne d => h ⟨⟨m', m⟩, d⟩ hne.symm⟩

/-- Exhaustively score the distinct pairs from an enumerated message space by the number of
keys giving a collision. Choose the first maximizer, or return `none` if there is no pair. -/
@[expose] def bestCollisionGuess [Fintype K] [DecidableEq M] [DecidableEq Y]
    (H : K → M → Y) (messages : List M) : Option (CollisionGuess M) :=
  let candidates := (messages.product messages).filter fun p => decide (p.1 ≠ p.2)
  let score := fun p : M × M => (Finset.univ.filter fun k => H k p.1 = H k p.2).card
  (candidates.argmax score).map fun p => ⟨p.1, p.2⟩

private theorem eval_collisionExperiment_pure [Fintype K] [Nonempty K] [DecidableEq M]
    [DecidableEq Y] (H : K → M → Y) (guess : CollisionGuess M)
    (hne : guess.first ≠ guess.second) :
    ProbComp.eval (collisionExperiment H (pure guess)) true =
      (PMF.uniformOfFintype K).toOuterMeasure {k | H k guess.first = H k guess.second} := by
  simp only [collisionExperiment, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
    PMF.pure_bind, Probability.PMF.bind_pure_decide_apply_true]
  congr 1
  ext k
  simp [hne]

/-- **Exercise 7.3** ([BonehShoup2023], v0.6, p. 277). Given a complete enumeration of a finite
message space, exhaustive search produces a deterministic guess that exceeds `ε` whenever
some distinct pair does. The search takes only the hash and the enumeration as inputs.
The witness pair and the sampled challenge key are absent from its inputs. -/
theorem bestCollisionGuess_wins [Fintype K] [Nonempty K] [DecidableEq M] [DecidableEq Y]
    (H : K → M → Y) (messages : List M) (complete : ∀ m, m ∈ messages) {ε : ℝ≥0∞}
    {m m' : M} (hne : m ≠ m')
    (h : ε < (PMF.uniformOfFintype K).toOuterMeasure {k | H k m = H k m'}) :
    ∃ guess, bestCollisionGuess H messages = some guess ∧
      ε < ProbComp.eval (collisionExperiment H (pure guess)) true := by
  let candidates := (messages.product messages).filter fun p => decide (p.1 ≠ p.2)
  let score := fun p : M × M => (Finset.univ.filter fun k => H k p.1 = H k p.2).card
  have hmem : (m, m') ∈ candidates := by simp [candidates, complete, hne]
  cases hbest : candidates.argmax score with
  | none =>
    simp [List.argmax_eq_none.mp hbest] at hmem
  | some p =>
    have hp : p ∈ candidates.argmax score := by simp [hbest]
    have hne' : p.1 ≠ p.2 :=
      of_decide_eq_true (List.mem_filter.mp (List.argmax_mem hp)).2
    have hscore := List.le_of_mem_argmax hmem hp
    refine ⟨⟨p.1, p.2⟩, ?_, ?_⟩
    · change (candidates.argmax score).map (fun q => CollisionGuess.mk q.1 q.2) = _
      simp [hbest]
    · rw [Probability.PMF.toOuterMeasure_uniformOfFintype] at h
      rw [eval_collisionExperiment_pure H _ hne', Probability.PMF.toOuterMeasure_uniformOfFintype]
      exact h.trans_le (mul_le_mul' (by exact_mod_cast hscore) le_rfl)

/-- Attack Game 7.2 (multi-query UHF, [BonehShoup2023], Version 0.6, Section 7.1.1, p. 254): the
adversary `B` outputs a list of messages, the challenger samples a uniform hash key independently,
and `B` wins when two distinct messages of the list have the same digest (`MUHFadv[B, H]` is the
probability of `true`). The book asks `B` to output distinct messages; Lean accepts any `List M`
and rewards only pairs with `m ≠ m'` and `H k m = H k m'`, so duplicate messages earn nothing. -/
@[expose] noncomputable def multiQueryExperiment [Fintype K] [Nonempty K] [DecidableEq M]
    [DecidableEq Y] (H : K → M → Y) (B : ProbComp (List M)) : ProbComp Bool := do
  let ms ← B
  let k ← ProbComp.uniform K
  return decide (∃ m ∈ ms, ∃ m' ∈ ms, m ≠ m' ∧ H k m = H k m')

private def decodeCollisionPair (fallback : M) (ms : List M) (slot : ℕ) : CollisionGuess M :=
  let width := ms.length - 1
  let i := slot / width
  let j := slot % width
  ⟨ms.getD i fallback, ms.getD (if j < i then j else j + 1) fallback⟩

private noncomputable def sampleCollisionPair (fallback : M) (ms : List M) :
    ProbComp (CollisionGuess M) :=
  (fun slot => slot.elim ⟨fallback, fallback⟩ (decodeCollisionPair fallback ms)) <$>
    ProbComp.sampleUniformInterval (ms.length * (ms.length - 1)) ms.length

/-- Run the multi-query adversary and sample an ordered pair of distinct positions with bounded
fair-bit rejection sampling. A list of length `s` allows `s` attempts. If the attempts fail
or there are fewer than two positions, return a repeated dummy message. -/
noncomputable def collisionPairReduction (fallback : M) (A : ProbComp (List M)) :
    ProbComp (CollisionGuess M) := do
  let ms ← A
  sampleCollisionPair fallback ms

open ComputableInPolyTime in
/-- Bounded sampling and unary list access preserve strict PPT for a multi-query adversary.
The certificate charges the framed input list and uses at most its length in attempts. -/
theorem isPPTOn_collisionPairReduction {I : Type} {encI : I ↪ List Bool}
    {encM : M ↪ List Bool} {A : I → ProbComp (List M)}
    (hA : IsPPTOn encI (encList encM) A) (fallback : M) :
    IsPPTOn encI (encCollisionGuess encM) (fun x => collisionPairReduction fallback (A x)) := by
  let encL := encList encM
  let encO := encPair encL (encOption encUnary)
  have hlen := length_list encM
  have hbound := hlen.unary_mul' (hlen.unary_sub' (.const 1))
  have hdecode : ComputableInPolyTime (fun p : List M × ℕ => decodeCollisionPair fallback p.1 p.2)
      (encPair encL encUnary) (encCollisionGuess encM) := by
    let encQR := encPair encUnary encUnary
    have hinputList := fst encL encUnary
    have hdivMod := unary_divMod.comp
      ((snd encL encUnary).prod ((hlen.comp hinputList).unary_sub' (.const 1)))
    have hlist := fst encL encQR
    have hqr := snd encL encQR
    have hi := (fst encUnary encUnary).comp hqr
    have hj := (snd encUnary encUnary).comp hqr
    have hskip := (unary_lt' hj hi).ite hj (hj.unary_add' (.const 1))
    have hlookup := encCollisionGuess_mk_polyTime encM
      (listGetDWithInput hlist hi fallback) (listGetDWithInput hlist hskip fallback)
    refine (hlookup.comp (hinputList.prod hdivMod)).of_enc_eq fun p => ?_
    simp only [decodeCollisionPair, Function.comp_apply, decide_eq_true_eq]
  have hresult : ComputableInPolyTime
      (fun p : List M × Option ℕ =>
        p.2.elim ⟨fallback, fallback⟩ (decodeCollisionPair fallback p.1))
      encO (encCollisionGuess encM) :=
    optionElimWithInput (snd encL (encOption encUnary))
      (.const (CollisionGuess.mk fallback fallback))
      (hdecode.comp (((fst encL (encOption encUnary)).comp (fst encO encUnary)).prod
        (snd encO encUnary)))
  exact hA.bind ((isPPTOn_sampleUniformInterval hbound hlen).map_with hresult)

private def pairSlot (s i j : ℕ) : ℕ :=
  i * (s - 1) + if j < i then j else j - 1

private theorem pairSlot_spec {s i j : ℕ} (hi : i < s) (hj : j < s) (hne : i ≠ j) :
    pairSlot s i j < s * (s - 1) ∧
      pairSlot s i j / (s - 1) = i ∧
      (if pairSlot s i j % (s - 1) < i then pairSlot s i j % (s - 1)
        else pairSlot s i j % (s - 1) + 1) = j := by
  let offset := if j < i then j else j - 1
  have hoff : offset < s - 1 := by
    dsimp only [offset]
    split <;> omega
  have hwidth : 0 < s - 1 := Nat.zero_lt_of_lt hoff
  have hquot : pairSlot s i j / (s - 1) = i := by
    change (i * (s - 1) + offset) / (s - 1) = i
    rw [Nat.mul_comm i (s - 1), Nat.mul_add_div hwidth, Nat.div_eq_of_lt hoff, Nat.add_zero]
  have hrem : pairSlot s i j % (s - 1) = offset := by
    change (i * (s - 1) + offset) % (s - 1) = offset
    rw [Nat.mul_comm i (s - 1), Nat.mul_add_mod, Nat.mod_eq_of_lt hoff]
  change i * (s - 1) + offset < s * (s - 1) ∧ _ ∧ _
  refine ⟨?_, hquot, ?_⟩
  · calc
      _ < (i + 1) * (s - 1) := by rw [Nat.add_mul, Nat.one_mul]; omega
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  · rw [hrem]
    dsimp only [offset]
    split_ifs <;> omega

private theorem inv_sq_le_sampleUniformInterval_pair {s slot : ℕ} (hs : 2 ≤ s)
    (hslot : slot < s * (s - 1)) :
    ((s : ℝ≥0∞) ^ 2)⁻¹ ≤ ProbComp.eval (ProbComp.sampleUniformInterval (s * (s - 1)) s)
      (some slot) := by
  have hs' : 0 < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
  have hs1 : 1 < (s : ℝ) := by exact_mod_cast (by omega : 1 < s)
  have hpos : 0 < s * (s - 1) := Nat.mul_pos (by omega) (by omega)
  have hsmall : (1 / 2 : ℝ) ^ s ≤ 1 / (s : ℝ) := by
    rw [div_pow, one_pow]
    exact one_div_le_one_div_of_le hs' (by exact_mod_cast (Nat.lt_two_pow_self (n := s)).le)
  refine le_trans ?_ (ProbComp.le_eval_sampleUniformInterval_some hpos s hslot)
  rw [← ENNReal.ofReal_toReal (ENNReal.inv_ne_top.mpr
    (pow_ne_zero _ (by exact_mod_cast (by omega : s ≠ 0))))]
  apply ENNReal.ofReal_le_ofReal
  simp only [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one]
  rw [← one_div]
  calc
    _ = (1 - 1 / (s : ℝ)) / ((s : ℝ) * (s - 1)) := by
      field_simp [hs'.ne', (sub_pos.mpr hs1).ne']
    _ ≤ _ := div_le_div_of_nonneg_right (sub_le_sub_left hsmall 1)
      (mul_nonneg hs'.le (sub_nonneg.mpr hs1.le))

private theorem two_inv_sq_le_sampleCollisionPair [DecidableEq M] [DecidableEq Y]
    (H : K → M → Y) (k : K) (fallback : M) (ms : List M)
    (h : ∃ m ∈ ms, ∃ m' ∈ ms, m ≠ m' ∧ H k m = H k m') :
    2 * ((ms.length : ℝ≥0∞) ^ 2)⁻¹ ≤ ((ProbComp.eval (sampleCollisionPair fallback ms)).bind
      fun g => PMF.pure (decide (g.first ≠ g.second ∧ H k g.first = H k g.second))) true := by
  obtain ⟨m, hm, m', hm', hne, hd⟩ := h
  obtain ⟨i, hi, hi'⟩ := List.mem_iff_getElem.mp hm
  obtain ⟨j, hj, hj'⟩ := List.mem_iff_getElem.mp hm'
  have hij : i ≠ j := by
    rintro rfl
    exact hne (hi'.symm.trans hj')
  have hlen : 2 ≤ ms.length := by omega
  obtain ⟨ha, ha₁, ha₂⟩ := pairSlot_spec hi hj hij
  obtain ⟨hb, hb₁, hb₂⟩ := pairSlot_spec hj hi hij.symm
  let a := pairSlot ms.length i j
  let b := pairSlot ms.length j i
  have hab : a ≠ b := fun he => hij (ha₁.symm.trans
    ((congrArg (fun x => x / (ms.length - 1)) he).trans hb₁))
  have hdecode {slot first second : ℕ} (hfirst : first < ms.length)
      (hsecond : second < ms.length) (hquot : slot / (ms.length - 1) = first)
      (hrem : (if slot % (ms.length - 1) < first then slot % (ms.length - 1)
        else slot % (ms.length - 1) + 1) = second) :
      decodeCollisionPair fallback ms slot = ⟨ms[first], ms[second]⟩ := by
    simp only [decodeCollisionPair, hquot, hrem,
      List.getD_eq_getElem _ _ hfirst, List.getD_eq_getElem _ _ hsecond]
  have hga : decodeCollisionPair fallback ms a = ⟨m, m'⟩ := by
    simpa only [hi', hj'] using hdecode (slot := a) hi hj ha₁ ha₂
  have hgb : decodeCollisionPair fallback ms b = ⟨m', m⟩ := by
    simpa only [hi', hj'] using hdecode (slot := b) hj hi hb₁ hb₂
  simp only [sampleCollisionPair, ProbComp.eval_map, PMF.bind_map, Function.comp_def,
    Probability.PMF.bind_pure_decide_apply_true]
  let p := ProbComp.eval (ProbComp.sampleUniformInterval (ms.length * (ms.length - 1)) ms.length)
  let pair : Finset (Option ℕ) := {some a, some b}
  have hsum : 2 * ((ms.length : ℝ≥0∞) ^ 2)⁻¹ ≤ p.toOuterMeasure pair := by
    have hab' : some a ∉ ({some b} : Finset (Option ℕ)) := by simpa using hab
    rw [PMF.toOuterMeasure_apply_finset]
    simp only [pair, Finset.sum_insert hab', Finset.sum_singleton, two_mul]
    exact add_le_add (inv_sq_le_sampleUniformInterval_pair hlen ha)
      (inv_sq_le_sampleUniformInterval_pair hlen hb)
  refine hsum.trans (p.toOuterMeasure.mono fun slot hslot => ?_)
  simp only [pair, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hslot
  rcases hslot with rfl | rfl
  · simp [hga, hne, hd]
  · simp [hgb, hne.symm, hd.symm]

private theorem collision_indicator_le_samplePair [DecidableEq M] [DecidableEq Y]
    (H : K → M → Y) (k : K) (fallback : M) (ms : List M) {Q : ℕ} (hlen : ms.length ≤ Q) :
    PMF.pure (decide (∃ m ∈ ms, ∃ m' ∈ ms, m ≠ m' ∧ H k m = H k m')) true ≤
      ((Q : ℝ≥0∞) ^ 2 / 2) * ((ProbComp.eval (sampleCollisionPair fallback ms)).bind
        fun g => PMF.pure (decide (g.first ≠ g.second ∧ H k g.first = H k g.second))) true := by
  by_cases h : ∃ m ∈ ms, ∃ m' ∈ ms, m ≠ m' ∧ H k m = H k m'
  · have hpos : (ms.length : ℝ≥0∞) ^ 2 ≠ 0 := by
      obtain ⟨m, hm, -⟩ := h
      simpa using List.ne_nil_of_mem hm
    simp only [h, decide_true, PMF.pure_apply_self]
    calc
      1 = (((ms.length : ℝ≥0∞) ^ 2) / 2) * (2 * ((ms.length : ℝ≥0∞) ^ 2)⁻¹) := by
        rw [div_eq_mul_inv, mul_comm 2, mul_mul_mul_comm, ENNReal.mul_inv_cancel hpos (by simp),
          ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
      _ ≤ _ := by
        gcongr
        exact two_inv_sq_le_sampleCollisionPair H k fallback ms h
  · simp [h]

/-- A finite-game step toward Lemma 7.1 ([BonehShoup2023], v0.6, printed pp. 254–255).
If the multi-query adversary outputs at most `Q` messages, its collision probability is at most
`Q ^ 2 / 2` times that of the explicit single-pair wrapper. Whenever the list contains a
collision, both orders of a colliding pair have enough sampling mass to give the bound. The
wrapper has a strict PPT certificate. `Crypto.Primitives.UHF.Computational` lifts this bound to
public setup and proves the asymptotic implication. -/
theorem eval_multiQueryExperiment_le_collisionPairReduction [Fintype K] [Nonempty K]
    [DecidableEq M] [DecidableEq Y] (H : K → M → Y) (fallback : M)
    (A : ProbComp (List M)) {Q : ℕ} (hA : ∀ ms ∈ (ProbComp.eval A).support, ms.length ≤ Q) :
    ProbComp.eval (multiQueryExperiment H A) true ≤ ((Q : ℝ≥0∞) ^ 2 / 2) *
      ProbComp.eval (collisionExperiment H (collisionPairReduction fallback A)) true := by
  simp only [multiQueryExperiment, collisionExperiment, collisionPairReduction,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, PMF.bind_bind]
  rw [PMF.bind_apply, PMF.bind_apply, ← ENNReal.tsum_mul_left]
  simp_rw [mul_left_comm ((Q : ℝ≥0∞) ^ 2 / 2)]
  refine Probability.PMF.tsum_mul_mono_support _ fun ms hms => ?_
  rw [PMF.bind_comm (ProbComp.eval (sampleCollisionPair fallback ms)), PMF.bind_apply,
    PMF.bind_apply, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun k => ?_
  rw [mul_left_comm]
  gcongr
  exact collision_indicator_le_samplePair H k fallback ms (hA ms hms)

/-- The `ε`-bounded case of [BonehShoup2023], Lemma 7.1, a step toward the lemma, not the cited
result: against an `ε`-bounded UHF (`IsUniversalHash` for the uniform key, the `ε`-UHF of
Definition 7.2), an adversary whose supported output lists have length at most `Q` wins Attack
Game 7.2 with probability at most `Q.choose 2 * ε`. Only the key type has to be finite. Lemma 7.1
assumes only a computational UHF and bounds the multi-query advantage by `Q ^ 2 / 2` times the
advantage of an efficient wrapper in Attack Game 7.1; here the hash is `ε`-bounded against every
adversary, efficient or not, for one fixed instance, with any `ε` (Definition 7.2 calls it
statistical only when `ε` is negligible), and the proof uses a union bound (#5790). -/
theorem eval_multiQueryExperiment_le [Fintype K] [Nonempty K] [DecidableEq M] [DecidableEq Y]
    {H : K → M → Y} {ε : ℝ≥0∞} (hH : IsUniversalHash (PMF.uniformOfFintype K) H ε)
    {B : ProbComp (List M)} {Q : ℕ} (hB : ∀ ms ∈ (ProbComp.eval B).support, ms.length ≤ Q) :
    ProbComp.eval (multiQueryExperiment H B) true ≤ (Q.choose 2 : ℕ) * ε := by
  simp only [multiQueryExperiment, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  refine Probability.PMF.bind_apply_le_on_support _ fun ms hms => ?_
  rw [Probability.PMF.bind_pure_decide_apply_true]
  refine ((PMF.uniformOfFintype K).toOuterMeasure.mono fun k hk => ?_).trans
    ((hH.toOuterMeasure_not_injOn_le ms.toFinset).trans ?_)
  · rcases hk with ⟨m, hm, m', hm', hne, heq⟩
    intro hinj
    exact hne (hinj (List.mem_toFinset.mpr hm) (List.mem_toFinset.mpr hm') heq)
  · gcongr
    exact ms.toFinset_card_le.trans (hB ms hms)

end Cslib.Crypto.UHF
