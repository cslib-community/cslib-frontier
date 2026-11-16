/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import Cslib.Crypto.Primitives.PRG.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Search

/-!
# Linear congruential generator distinguisher and seed search

The linear congruential generator `G_lcg(s) = (⌊s / w⌋, a * s + b mod q)` with state space
`S_q = {0, …, q - 1}` and output space `R = {0, …, ⌊(q - 1) / w⌋}`
([BonehShoup2023], Section 3.7.1, pp. 70–71).

Given `(r, s')`, `LinearCongruential.test` recovers `s` from `s'` using `BinaryGcd.modInv` and
checks `⌊s / w⌋ = r`. On `LinearCongruential.generator : Generator (Fin q) (Fin |R| × Fin q)`,
when `a` is coprime to `q`, `generator` is injective (`generator_injective`) and `test` computes
cslib's range test `Generator.rangeTest` (`rangeTest_generator`), so
`advantage_generator_test` gives exact distinguishing advantage `1 - 1 / |R|`. Note the boundary:
Boneh–Shoup call `G_lcg` "clearly insecure" for every positive `w ≤ q`. That holds when `0 < w < q`
(advantage at least `1 / 2`) and fails at `w = q`: then `|R| = 1` and the advantage is `0`, as it
is for the values `w = 0` and `w > q` that the book excludes. The advantage theorem targets the
finite typed game (which has no adversary cost model); `computableInPolyTime_test` separately
certifies `test` on encoded natural numbers in binary.

For the multi-iteration generator outputting consecutive `⌊s_i / w⌋` values,
`LinearCongruential.seedSearch` checks all `w` candidates `r₁ * w + e` with `e < w` below `q` whose
second and third outputs match `r₂` and `r₃`, returning the greatest passing candidate or `r₁ * w`
if none passes (Boneh–Shoup do not specify a tie-breaking or fallback value). `seedSearch_eq` proves
that the search returns the seed `s < q` when `0 < w` and the condition `hshort` holds: no nonzero
`d` with `|d| < w` has `a * d` within less than `w` of a multiple of `q`. Under `0 < w` and
`hshort` two outputs already determine the state (`eq_of_div_eq_of_next_div_eq`). `hshort` is not
in the book, which describes the search for the Java 8 parameters only. It is sufficient and not
necessary, and some condition is needed: with `a = b = 1`, `q = 16`, `w = 4`, which meet the book's
conditions on the parameters, the seeds `0` and `1` have the same three outputs.
`computableInPolyTime_seedSearch` certifies `seedSearch` in time polynomial in `w` (given in unary
via `encUnary`, so exponential in the bit length of `w`) and the binary lengths of the other
inputs. `java8` records Boneh–Shoup's parameters for Java 8 `Math.random`, and `seedSearch_java8`
discharges `hshort` for every seed `s < 2 ^ 48`.

Differences from [BonehShoup2023]: `LinearCongruential` omits `a, b < q` and `0 < w ≤ q`, taking
only the hypothesis each result uses; `G_lcg^(n)` as a generator and Lemma 3.7 are omitted.

## Main definitions

* `Cslib.Crypto.PRG.LinearCongruential`: parameters `(q, a, b, w)` and binary encoding
  `encLinearCongruential`.
* `Cslib.Crypto.PRG.LinearCongruential.next`, `Cslib.Crypto.PRG.LinearCongruential.prev`: modular
  state update and inverse via `BinaryGcd.modInv`.
* `Cslib.Crypto.PRG.LinearCongruential.test`: the distinguishing test
  `(r, s') ↦ (prev s' / w == r)`.
* `Cslib.Crypto.PRG.LinearCongruential.generator`: the single-step `Generator` `G_lcg`.
* `Cslib.Crypto.PRG.LinearCongruential.seedSearch`: exhaustive search over `e < w` matching three
  outputs.
* `Cslib.Crypto.PRG.LinearCongruential.java8`: Boneh–Shoup's parameters for `Math.random`.

## Main results

* `Cslib.Crypto.PRG.LinearCongruential.prev_next`: `prev` inverts `next` when `a.Coprime q`.
* `Cslib.Crypto.PRG.LinearCongruential.computableInPolyTime_test`: `test` is computable in
  polynomial time in binary.
* `Cslib.Crypto.PRG.LinearCongruential.generator_injective`: `generator` is injective when
  `a.Coprime q`.
* `Cslib.Crypto.PRG.LinearCongruential.rangeTest_generator`: `generator.rangeTest` agrees with
  `test`.
* `Cslib.Crypto.PRG.LinearCongruential.advantage_generator_test`: `generator.advantage` against
  `test` is `1 - 1 / (⌊(q - 1) / w⌋ + 1)`.
* `Cslib.Crypto.PRG.LinearCongruential.eq_of_div_eq_of_next_div_eq`: state uniqueness from two
  outputs under `hshort`.
* `Cslib.Crypto.PRG.LinearCongruential.seedSearch_eq`: `seedSearch` recovers `s < q` under `0 < w`
  and `hshort`.
* `Cslib.Crypto.PRG.LinearCongruential.computableInPolyTime_seedSearch`: `seedSearch` runs in
  polynomial time in `w` (unary) and the binary lengths of `P, r₁, r₂, r₃`.
* `Cslib.Crypto.PRG.LinearCongruential.seedSearch_java8`: `seedSearch` recovers every seed
  `s < 2 ^ 48` of `java8`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 3.7.1, pp. 70–71.
-/

public section

open Turing.MultiTapeTM

namespace Cslib.Crypto.PRG

/-- The public system parameters of a linear congruential generator
([BonehShoup2023], Section 3.7.1, p. 70). -/
structure LinearCongruential where
  /-- The modulus `q`: the states are the numbers below `q`. -/
  q : ℕ
  /-- The multiplier `a`. -/
  a : ℕ
  /-- The increment `b`. -/
  b : ℕ
  /-- The divisor `w`: an iteration in state `s` outputs `s / w`. -/
  w : ℕ

/-- The encoding of the parameters of a linear congruential generator: `q`, `a`, `b` and `w` in
binary, each framed except the last (`encLinearCongruential_apply`). -/
enc_structure encLinearCongruential : LinearCongruential where
  q : encNat, a : encNat, b : encNat, w : encNat

namespace LinearCongruential

/-- The state update `s ↦ a * s + b mod q`. -/
@[expose] def next (P : LinearCongruential) (s : ℕ) : ℕ :=
  (P.a * s + P.b) % P.q

/-- The state before `s'`: `a⁻¹ * (s' - b) mod q`, with `a⁻¹` computed by the extended Euclidean
algorithm. It inverts `next` on states when `a` is coprime to `q` (`prev_next`). -/
@[expose] def prev (P : LinearCongruential) (s' : ℕ) : ℕ :=
  BinaryGcd.modInv P.a P.q * (s' + P.q - P.b % P.q) % P.q

/-- The state update can be undone: `prev` recovers the state `s` from `a * s + b mod q`. -/
theorem prev_next (P : LinearCongruential) (ha : P.a.Coprime P.q) {s : ℕ} (hs : s < P.q) :
    P.prev (P.next s) = s := by
  have hq : 0 < P.q := by lia
  have hb : P.b % P.q < P.q := Nat.mod_lt _ hq
  have h₁ : P.next s + P.q - P.b % P.q ≡ P.a * s [MOD P.q] := by
    have h : P.next s + P.q - P.b % P.q + P.b ≡ P.a * s + P.b [MOD P.q] := by
      have e : P.next s + P.q - P.b % P.q + P.b = P.next s + P.b / P.q * P.q + P.q := by
        have := Nat.div_add_mod' P.b P.q
        lia
      rw [e]
      calc P.next s + P.b / P.q * P.q + P.q ≡ P.next s + 0 + 0 [MOD P.q] :=
            ((Nat.ModEq.refl _).add (Nat.modEq_zero_iff_dvd.mpr (Nat.dvd_mul_left ..))).add
              (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)
        _ ≡ P.a * s + P.b [MOD P.q] := by simpa [next] using Nat.mod_modEq _ _
    exact Nat.ModEq.add_right_cancel' _ h
  have h₂ : P.prev (P.next s) ≡ s [MOD P.q] := by
    calc P.prev (P.next s) ≡ BinaryGcd.modInv P.a P.q * (P.next s + P.q - P.b % P.q) [MOD P.q] :=
          Nat.mod_modEq _ _
      _ ≡ BinaryGcd.modInv P.a P.q * (P.a * s) [MOD P.q] := h₁.mul_left _
      _ = P.a * BinaryGcd.modInv P.a P.q * s := by ring
      _ ≡ 1 * s [MOD P.q] := (BinaryGcd.mul_modInv_modEq_one hq ha).mul_right _
      _ = s := one_mul s
  exact Nat.ModEq.eq_of_lt_of_lt h₂ (Nat.mod_lt _ hq) hs

/-- The test of [BonehShoup2023], p. 70, on numbers: given `(r, s')`, recover the state `s` before
`s'` and accept when `s / w = r`. -/
@[expose] def test (P : LinearCongruential) (r s' : ℕ) : Bool :=
  decide (P.prev s' / P.w = r)

/-- The test runs in time polynomial in the length of the parameters and the challenge, all in
binary. -/
theorem computableInPolyTime_test {α : Type} {enc : α ↪ List Bool} {P : α → LinearCongruential}
    {r s' : α → ℕ} (hP : ComputableInPolyTime P enc encLinearCongruential)
    (hr : ComputableInPolyTime r enc encNat) (hs' : ComputableInPolyTime s' enc encNat) :
    ComputableInPolyTime (fun x => (P x).test (r x) (s' x)) enc encBool := by
  have hq := encLinearCongruential_q_polyTime hP
  have ha := encLinearCongruential_a_polyTime hP
  have hb := encLinearCongruential_b_polyTime hP
  have hw := encLinearCongruential_w_polyTime hP
  have hprev : ComputableInPolyTime (fun x => (P x).prev (s' x)) enc encNat :=
    ComputableInPolyTime.binary_mod'
      (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.binary_modInv' ha hq)
        (ComputableInPolyTime.binary_sub' (ComputableInPolyTime.binary_add' hs' hq)
          (ComputableInPolyTime.binary_mod' hb hq))) hq
  exact ComputableInPolyTime.decide_eq' (ComputableInPolyTime.binary_div' hprev hw) hr

/-- The generator `G_lcg : S_q → R × S_q` of [BonehShoup2023], p. 70:
`s ↦ (⌊s / w⌋, a * s + b mod q)`, where `R` has the `⌊(q - 1) / w⌋ + 1` elements
`0, …, ⌊(q - 1) / w⌋`. -/
@[expose] def generator (P : LinearCongruential) :
    Generator (Fin P.q) (Fin ((P.q - 1) / P.w + 1) × Fin P.q) :=
  ⟨fun s => (⟨s / P.w, Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_sub_one_of_lt s.isLt))⟩,
    ⟨P.next s, Nat.mod_lt _ s.pos⟩)⟩

private theorem eq_of_next_eq (P : LinearCongruential) (ha : P.a.Coprime P.q)
    {s t : ℕ} (hs : s < P.q) (ht : t < P.q) (h : P.next s = P.next t) : s = t := by
  have := congrArg P.prev h
  simpa [P.prev_next ha hs, P.prev_next ha ht] using this

/-- `G_lcg` is injective when `a` is coprime to `q`. -/
theorem generator_injective (P : LinearCongruential) (ha : P.a.Coprime P.q) :
    Function.Injective P.generator := fun s t h =>
  Fin.ext (P.eq_of_next_eq ha s.isLt t.isLt (congrArg (Fin.val ∘ Prod.snd) h))

/-- The book's test is the range test of `G_lcg`. -/
theorem rangeTest_generator (P : LinearCongruential) (ha : P.a.Coprime P.q)
    (y : Fin ((P.q - 1) / P.w + 1) × Fin P.q) :
    P.generator.rangeTest y = P.test y.1 y.2 := by
  have hinj : Function.Injective fun s : Fin P.q => (P.generator s).2 := fun s t h =>
    Fin.ext (P.eq_of_next_eq ha s.isLt t.isLt (congrArg Fin.val h))
  obtain ⟨t, ht⟩ := Finite.surjective_of_injective hinj y.2
  have hprev : P.prev y.2 = t := by
    rw [← ht]
    exact P.prev_next ha t.isLt
  rw [Generator.rangeTest, test, hprev]
  refine decide_eq_decide.mpr ⟨?_, fun h => ⟨t, Prod.ext (Fin.ext h) ht⟩⟩
  rintro ⟨s, rfl⟩
  obtain rfl := hinj ht
  rfl

/-- **`G_lcg` is insecure** ([BonehShoup2023], Section 3.7.1, p. 70): the test that recovers the
state `s` from `a * s + b mod q` and compares `⌊s / w⌋`, run on a challenge in `R × S_q`, has
advantage exactly `1 - 1 / |R|`, where `|R| = ⌊(q - 1) / w⌋ + 1`. The advantage is at least `1 / 2`
when `0 < w < q`; otherwise `R` has one element and the advantage is `0`. -/
theorem advantage_generator_test (P : LinearCongruential) [NeZero P.q] (ha : P.a.Coprime P.q) :
    P.generator.advantage (fun y => PMF.pure (P.test y.1 y.2)) =
      1 - 1 / (((P.q - 1) / P.w + 1 : ℕ) : ℝ) := by
  have h : (fun y : Fin ((P.q - 1) / P.w + 1) × Fin P.q => PMF.pure (P.test y.1 y.2)) =
      P.generator.rangeAdversary :=
    funext fun y => congrArg PMF.pure (P.rangeTest_generator ha y).symm
  have hq : (P.q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne P.q)
  rw [h, Generator.advantage_rangeAdversary,
    Nat.card_range_of_injective (P.generator_injective ha)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin]
  push_cast
  field_simp

/-- Under `hshort`, a state is determined by its output and the output of its successor. -/
theorem eq_of_div_eq_of_next_div_eq (P : LinearCongruential) (hw : 0 < P.w)
    (hshort : ∀ d d' : ℤ, |d| < P.w → |d'| < P.w → (P.q : ℤ) ∣ P.a * d - d' → d = 0)
    {s t : ℕ} (h₁ : s / P.w = t / P.w) (h₂ : P.next s / P.w = P.next t / P.w) :
    s = t := by
  have hs := Nat.div_add_mod s P.w
  have ht := Nat.div_add_mod t P.w
  have hsl := Nat.mod_lt s hw
  have htl := Nat.mod_lt t hw
  have hn := Nat.div_add_mod (P.next s) P.w
  have hn' := Nat.div_add_mod (P.next t) P.w
  have hlt := Nat.mod_lt (P.next s) hw
  have hlt' := Nat.mod_lt (P.next t) hw
  have hk := Nat.div_add_mod (P.a * s + P.b) P.q
  have hk' := Nat.div_add_mod (P.a * t + P.b) P.q
  have hd : (s : ℤ) - t = 0 := by
    refine hshort _ ((P.next s : ℤ) - P.next t) ?_ ?_ ?_
    · rw [h₁] at hs
      rw [abs_lt]
      lia
    · rw [h₂] at hn
      rw [abs_lt]
      lia
    · refine ⟨((P.a * s + P.b) / P.q : ℕ) - ((P.a * t + P.b) / P.q : ℕ), ?_⟩
      unfold next
      zify at hk hk'
      push_cast
      linear_combination hk' - hk
  lia

/-- The exhaustive search of [BonehShoup2023], p. 71, for a seed with first outputs `r₁`, `r₂`,
`r₃`. The candidates are the `w` numbers `r₁ * w + e` with `e < w`, the numbers whose first output
is `r₁`. The result is the greatest candidate below `q` whose second and third outputs are `r₂`
and `r₃`, and `r₁ * w` if there is none. -/
@[expose] def seedSearch (P : LinearCongruential) (r₁ r₂ r₃ : ℕ) : ℕ :=
  r₁ * P.w + Nat.findGreatest (fun e => r₁ * P.w + e < P.q ∧
    P.next (r₁ * P.w + e) / P.w = r₂ ∧ P.next (P.next (r₁ * P.w + e)) / P.w = r₃) (P.w - 1)

/-- The search recovers the seed from its first three outputs under `hshort`: no nonzero `d` with
`|d| < w` has `a * d` within `w` of a multiple of `q`. Then no two states have the same first two
outputs. The condition is sufficient and not necessary. -/
theorem seedSearch_eq (P : LinearCongruential) (hw : 0 < P.w)
    (hshort : ∀ d d' : ℤ, |d| < P.w → |d'| < P.w → (P.q : ℤ) ∣ P.a * d - d' → d = 0)
    {s : ℕ} (hs : s < P.q) :
    P.seedSearch (s / P.w) (P.next s / P.w) (P.next (P.next s) / P.w) = s := by
  have hdm : s / P.w * P.w + s % P.w = s := Nat.div_add_mod' s P.w
  have hmod : s % P.w ≤ P.w - 1 := Nat.le_sub_one_of_lt (Nat.mod_lt _ hw)
  have hspec := Nat.findGreatest_spec (P := fun e => s / P.w * P.w + e < P.q ∧
      P.next (s / P.w * P.w + e) / P.w = P.next s / P.w ∧
      P.next (P.next (s / P.w * P.w + e)) / P.w = P.next (P.next s) / P.w) hmod
      ⟨by rw [hdm]; exact hs, by rw [hdm], by rw [hdm]⟩
  refine P.eq_of_div_eq_of_next_div_eq hw hshort ?_ hspec.2.1
  have hle := Nat.findGreatest_le (P := fun e => s / P.w * P.w + e < P.q ∧
      P.next (s / P.w * P.w + e) / P.w = P.next s / P.w ∧
      P.next (P.next (s / P.w * P.w + e)) / P.w = P.next (P.next s) / P.w) (P.w - 1)
  rw [seedSearch, Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt (by lia),
    Nat.zero_add]

/-- The search runs in time polynomial in `w` and in the length of the other inputs in binary: the
caller supplies `w` in unary (so time is exponential in the bit length of `w`). -/
theorem computableInPolyTime_seedSearch {α : Type} {enc : α ↪ List Bool}
    {P : α → LinearCongruential} {r₁ r₂ r₃ : α → ℕ}
    (hP : ComputableInPolyTime P enc encLinearCongruential)
    (hw : ComputableInPolyTime (fun x => (P x).w) enc encUnary)
    (h₁ : ComputableInPolyTime r₁ enc encNat) (h₂ : ComputableInPolyTime r₂ enc encNat)
    (h₃ : ComputableInPolyTime r₃ enc encNat) :
    ComputableInPolyTime (fun x => (P x).seedSearch (r₁ x) (r₂ x) (r₃ x)) enc encNat := by
  have hfst := ComputableInPolyTime.fst enc encUnary
  have hq := (encLinearCongruential_q_polyTime hP).comp hfst
  have ha := (encLinearCongruential_a_polyTime hP).comp hfst
  have hb := (encLinearCongruential_b_polyTime hP).comp hfst
  have hwb := (encLinearCongruential_w_polyTime hP).comp hfst
  have hnext : ∀ {s : α × ℕ → ℕ}, ComputableInPolyTime s (encPair enc encUnary) encNat →
      ComputableInPolyTime (fun p => (P p.1).next (s p)) (encPair enc encUnary) encNat := fun hs =>
    ComputableInPolyTime.binary_mod'
      (ComputableInPolyTime.binary_add' (ComputableInPolyTime.binary_mul' ha hs) hb) hq
  have hcand : ComputableInPolyTime (fun p : α × ℕ => r₁ p.1 * (P p.1).w + p.2)
      (encPair enc encUnary) encNat :=
    ComputableInPolyTime.binary_add' (ComputableInPolyTime.binary_mul' (h₁.comp hfst) hwb)
      (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd enc encUnary))
  have hpred : ComputableInPolyTime (fun p : α × ℕ => decide (r₁ p.1 * (P p.1).w + p.2 < (P p.1).q ∧
      (P p.1).next (r₁ p.1 * (P p.1).w + p.2) / (P p.1).w = r₂ p.1 ∧
      (P p.1).next ((P p.1).next (r₁ p.1 * (P p.1).w + p.2)) / (P p.1).w = r₃ p.1))
      (encPair enc encUnary) encBool :=
    ComputableInPolyTime.decide_and (ComputableInPolyTime.binary_lt' hcand hq)
      (ComputableInPolyTime.decide_and
        (ComputableInPolyTime.decide_eq' (ComputableInPolyTime.binary_div' (hnext hcand) hwb)
          (h₂.comp hfst))
        (ComputableInPolyTime.decide_eq'
          (ComputableInPolyTime.binary_div' (hnext (hnext hcand)) hwb) (h₃.comp hfst)))
  have hfind := ComputableInPolyTime.findGreatest
    (predicate := fun x e => r₁ x * (P x).w + e < (P x).q ∧
      (P x).next (r₁ x * (P x).w + e) / (P x).w = r₂ x ∧
      (P x).next ((P x).next (r₁ x * (P x).w + e)) / (P x).w = r₃ x)
    (ComputableInPolyTime.unary_sub' hw (ComputableInPolyTime.const 1)) hpred
  exact ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_mul' h₁ (encLinearCongruential_w_polyTime hP))
    (ComputableInPolyTime.unary_to_binary.comp hfind)

/-- The parameters of `Math.random` in the Java 8 Development Kit as stated by
[BonehShoup2023], pp. 70–71: `q = 2 ^ 48`, `a = 0x5DEECE66D`, `b = 0x0B` and `w = 2 ^ 22`. -/
@[expose] def java8 : LinearCongruential :=
  ⟨2 ^ 48, 0x5DEECE66D, 0x0B, 2 ^ 22⟩

/-- **Seed recovery for Java 8 `Math.random`** ([BonehShoup2023], p. 71): the search over the
`2 ^ 22` candidates returns the seed, for every seed. The proof uses the first two outputs only. -/
theorem seedSearch_java8 {s : ℕ} (hs : s < java8.q) :
    java8.seedSearch (s / java8.w) (java8.next s / java8.w)
      (java8.next (java8.next s) / java8.w) = s := by
  refine java8.seedSearch_eq (by decide) (fun d d' hd hd' h => ?_) hs
  have hd₁ : |d| < 2 ^ 22 := by simpa [java8] using hd
  have hd₂ : |d'| < 2 ^ 22 := by simpa [java8] using hd'
  have h' : (2 ^ 48 : ℤ) ∣ 0x5DEECE66D * d - d' := by simpa [java8] using h
  obtain ⟨t, ht⟩ := h'
  rw [abs_lt] at hd₁ hd₂
  have e₁ : 4824621 * d - 7847617 * d' = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd (m := 2 ^ 48) ⟨7847617 * t - 703 * d, ?_⟩ ?_
    · linear_combination 7847617 * ht
    · rw [abs_lt]
      lia
  have e₂ : 24667315 * d + 18218081 * d' = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd (m := 2 ^ 48) ⟨1632 * d - 18218081 * t, ?_⟩ ?_
    · linear_combination (-18218081) * ht
    · rw [abs_lt]
      lia
  lia

end LinearCongruential

end Cslib.Crypto.PRG
