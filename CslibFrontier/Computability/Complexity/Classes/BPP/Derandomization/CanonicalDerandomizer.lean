/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BPP.Derandomization.CircuitPRG
import CslibFrontier.Computability.Circuit.Boolean.Synthesis
import CslibFrontier.Computability.Complexity.Classes.BPP.Derandomization.Generator
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Log

/-!
# Generators running in time exponential in the seed

The generators used for derandomization may run longer than the tests they fool. Goldreich's
*canonical derandomizers* [Goldreich, Definition 8.14][Goldreich2007DraftR4] (draft r4, printed
page 338, PDF page 74) run in time `poly(2 ^ k ℓ(k))` on seeds of `k` bits and fool circuits of
size `ℓ(k) ^ 2` within `1 / 6`. Arora and Barak's `S(ℓ)`-pseudorandom generators
[Arora and Barak, Definition 16.2][AroraBarak07] (draft of 2007-01-08, printed pages 283–284,
PDF pages 299–300) run in time `2 ^ (c ℓ)` and fool circuits of size `S(ℓ) ^ 3` within `1 / 10`.
Enumerating the seeds still takes time polynomial in `2 ^ k` and the instance, as for
polynomial-time generators (`Cslib.Complexity.seedDecider`).

* *The stretch is at most exponential* [Goldreich, Exercise 8.18][Goldreich2007DraftR4] (printed
  page 374): for every generator `G : {0,1} ^ k → {0,1} ^ L`, the test for membership in the range
  of `G` has circuits with `2 ^ k (2 L + 2) + 1` gates and distinguishes `G` with gap at least
  `1 - 2 ^ (k - L)` (`Cslib.Crypto.PRG.Generator.exists_complexity_le_advantage_ge`). So a
  canonical derandomizer has `ℓ(k) ≤ 2 ^ (k + 1) + 1`
  (`Cslib.Complexity.CanonicalDerandomizer.le_two_pow`), and its running time `poly(2 ^ k ℓ(k))`
  is `poly(2 ^ k)`, as Goldreich notes in Footnote 23.
* *Full derandomization* [Goldreich, Theorem 8.16][Goldreich2007DraftR4] (printed page 339): a
  canonical derandomizer of stretch `2 ^ Ω(k)` gives `P = BPP`
  (`Cslib.Complexity.P_eq_BPP_of_canonicalDerandomizer`). Seeds of `O(log n)` bits are stretched
  past the size of the verifier's circuit with its instance hardwired, and the seed decider runs
  the generator on seeds of `O(log n)` bits in time polynomial in `n`.
* An `S(ℓ)`-pseudorandom generator of Arora and Barak is a canonical derandomizer of stretch `S`
  (`Cslib.Complexity.ExponentialTimePRG.canonicalDerandomizer`), so a `2 ^ (ε ℓ)`-pseudorandom
  generator gives `P = BPP` [Arora and Barak, Corollary 16.6 (1)][AroraBarak07]
  (`Cslib.Complexity.P_eq_BPP_of_exponentialTimePRG`).

Goldreich's Proposition 8.15 and Arora and Barak's Lemma 16.4, for `BPTIME(t)` with general `t`,
are not proved: under this library's constant-factor conventions their printed proofs leave a
gap. Conditional forms under a growth hypothesis are in
`CslibFrontier.Computability.Complexity.Classes.BPP.Derandomization.GeneralTime`. In the
polynomial regime of Theorem 8.16, the constant factors are absorbed by a longer seed of
`O(log n)` bits.

## Main definitions

* `Cslib.Complexity.CanonicalDerandomizer`: Goldreich's Definition 8.14.
* `Cslib.Complexity.ExponentialTimePRG`: Arora and Barak's Definition 16.2.

## Main results

* `Cslib.Crypto.PRG.Generator.exists_complexity_le_advantage_ge`: Goldreich's Exercise 8.18.
* `Cslib.Complexity.CanonicalDerandomizer.le_two_pow`: the stretch of a canonical derandomizer is
  `O(2 ^ k)`.
* `Cslib.Complexity.P_eq_BPP_of_canonicalDerandomizer`: Goldreich's Theorem 8.16.
* `Cslib.Complexity.ExponentialTimePRG.canonicalDerandomizer`: Definition 16.2 gives
  Definition 8.14.
* `Cslib.Complexity.P_eq_BPP_of_exponentialTimePRG`: Arora and Barak's Corollary 16.6 (1).

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft
  r4][Goldreich2007DraftR4], Section 8.3.1
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, draft][AroraBarak07],
  Section 16.1
-/

@[expose] public section

open Turing Turing.MultiTapeTM Filter Finset

namespace Cslib.Crypto.PRG

open Cslib.Circuits Cslib.Circuits.Boolean

/-- **Goldreich, Exercise 8.18: a range test distinguishes every generator**
[Goldreich, Exercise 8.18][Goldreich2007DraftR4] (draft r4, printed page 374). For every
generator `G : {0,1} ^ k → {0,1} ^ L`, the test for membership in the range of `G` has De Morgan
circuits with at most `2 ^ k (2 L + 2) + 1 = O(2 ^ k L)` gates (a disjunction over the seeds of
the conjunction of the `L` output bits), accepts every output of `G`, and accepts at most `2 ^ k`
of the `2 ^ L` strings. So it distinguishes `G` with advantage at least `1 - 2 ^ k / 2 ^ L`, which
is at least `1 / 2` when `L > k`. -/
theorem Generator.exists_complexity_le_advantage_ge {k L : ℕ}
    (Gk : Generator (BitString k) (BitString L)) :
    ∃ test : BooleanFunction L,
      complexity interpretation (single test) ≤ 2 ^ k * (2 * L + 2) + 1 ∧
      1 - (2 : ℝ) ^ k / 2 ^ L ≤ Gk.advantage fun y => PMF.pure (test y) := by
  classical
  refine ⟨fun y => decide (∃ z, Gk z = y), ?_, ?_⟩
  · -- a disjunction over the seeds of the conjunction of the output bits
    set D : List (List (BooleanFunction L × Bool)) := (BitString.enum k).map fun z =>
      (List.finRange L).map fun i => ((fun x : BitString L => x i), Gk z i)
    have hw : ∀ c ∈ D, c.length ≤ L := by
      intro c hc
      obtain ⟨z, -, rfl⟩ := List.mem_map.1 hc
      simp
    have hD : ∀ c ∈ D, ∀ l ∈ c, l.1 ∈ inputs L := by
      intro c hc l hl
      obtain ⟨z, -, rfl⟩ := List.mem_map.1 hc
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hl
      exact ⟨i, rfl⟩
    have hsyn := Synthesis.any_all_literal hw hD
    have hlen : D.length = 2 ^ k := by simp [D]
    rw [hlen] at hsyn
    refine Synthesis.complexity_le (Synthesis.congr_iff hsyn fun x => ?_)
    simp only [D, List.any_map, List.any_eq_true, Function.comp_apply, List.all_map,
      List.all_eq_true, List.mem_finRange, decide_eq_true_eq, true_implies, BitString.mem_enum,
      true_and]
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, funext fun i => (hz i).symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, fun i => rfl⟩
  · rw [Generator.advantage_pure_eq]
    have hseeds : #{z : BitString k | decide (∃ z', Gk z' = Gk z) = true} = 2 ^ k := by
      rw [filter_true_of_mem fun z _ => decide_eq_true ⟨z, rfl⟩, card_univ, BitString.card]
    have hrange : #{y : BitString L | decide (∃ z, Gk z = y) = true} ≤ 2 ^ k := by
      calc #{y : BitString L | decide (∃ z, Gk z = y) = true}
          ≤ (univ.image Gk).card := card_le_card fun y hy => by
            obtain ⟨z, rfl⟩ := of_decide_eq_true (mem_filter.1 hy).2
            exact mem_image_of_mem Gk (mem_univ z)
        _ ≤ (univ : Finset (BitString k)).card := card_image_le
        _ = 2 ^ k := by rw [card_univ, BitString.card]
    rw [hseeds]
    have hrange' : (#{y : BitString L | decide (∃ z, Gk z = y) = true} : ℝ) ≤ 2 ^ k := by
      exact_mod_cast hrange
    have hpos : (0 : ℝ) < 2 ^ L := by positivity
    have hk : ((2 ^ k : ℕ) : ℝ) / 2 ^ k = 1 := by push_cast; exact div_self (by positivity)
    rw [hk]
    refine le_trans ?_ (le_abs_self _)
    have := div_le_div_of_nonneg_right hrange' hpos.le
    linarith

end Cslib.Crypto.PRG

namespace Cslib.Complexity

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Crypto.PRG

/-- **Canonical derandomizers** [Goldreich, Definition 8.14][Goldreich2007DraftR4] (draft r4,
printed page 338, PDF page 74). A canonical derandomizer of stretch `ℓ` is a deterministic
algorithm `G`, computable within time `poly(2 ^ k ℓ(k))` on seeds of `k` bits, with outputs of
`ℓ(k)` bits, such that every De Morgan circuit with at most `ℓ(k) ^ 2` gates distinguishes `G` on a
uniform seed of `k` bits from a uniform string of `ℓ(k)` bits with advantage below `1 / 6`
(Eq. 8.11).

Deviations, each of which only admits more generators: the stretch `ℓ` is non-decreasing
(the source says "monotonically increasing"); the time bound is `(2 ^ k (ℓ(k) + 1)) ^ D` up to a
constant factor, which is `poly(2 ^ k ℓ(k))` whenever `ℓ(k) ≥ 1`; and the space is bounded by the
same function, as `Turing.MultiTapeTM.ComputableInO` requires (a machine visits at most one new
cell per step). Circuit size is the number of gates (`Cslib.Crypto.PRG.IsCircuitTest`). No
canonical derandomizer of super-polynomial stretch is known to exist unconditionally; the record
is a hypothesis. -/
structure CanonicalDerandomizer (G : List Bool → List Bool) (ℓ : ℕ → ℕ) : Prop where
  /-- The stretch is non-decreasing. -/
  monotone : Monotone ℓ
  /-- The output length depends only on the seed length. -/
  length_eq : ∀ z, (G z).length = ℓ z.length
  /-- The generator runs in time polynomial in `2 ^ k` and the output length. -/
  time : ∃ D : ℕ, ComputableInO G encBits encBits (fun z => (2 ^ z.length * (ℓ z.length + 1)) ^ D)
    fun z => (2 ^ z.length * (ℓ z.length + 1)) ^ D
  /-- Every circuit with at most `ℓ(k) ^ 2` gates has advantage below `1 / 6` (Eq. 8.11). -/
  fools : ∀ k adversary, IsCircuitTest (ℓ k ^ 2) adversary →
    (wordFamily G ℓ k).advantage adversary < 1 / 6

namespace CanonicalDerandomizer

variable {G : List Bool → List Bool} {ℓ : ℕ → ℕ}

/-- **The stretch of a canonical derandomizer is `O(2 ^ k)`** [Goldreich, Section 8.3.1, Footnote
23 and Exercise 8.18][Goldreich2007DraftR4]. If `ℓ(k) > 2 ^ (k + 1) + 1`, the range test of
`Cslib.Crypto.PRG.Generator.exists_complexity_le_advantage_ge` has at most `ℓ(k) ^ 2` gates and
advantage at least `1 / 2`, contradicting Eq. 8.11. -/
theorem le_two_pow (hG : CanonicalDerandomizer G ℓ) (k : ℕ) : ℓ k ≤ 2 ^ (k + 1) + 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨test, hsize, hadv⟩ := (wordFamily G ℓ k).exists_complexity_le_advantage_ge
  have hP : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have hcirc : IsCircuitTest (ℓ k ^ 2) fun y => PMF.pure (test y) := by
    refine ⟨test, hsize.trans ?_, rfl⟩
    have hL : 2 * 2 ^ k + 2 ≤ ℓ k := by omega
    have := Nat.mul_le_mul_left (ℓ k) hL
    rw [sq]
    nlinarith
  have hfool := hG.fools k _ hcirc
  have hkℓ : k + 1 ≤ ℓ k := by have := Nat.lt_two_pow_self (n := k + 1); omega
  have h2 : (2 : ℝ) ^ k / 2 ^ ℓ k ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : (2 : ℝ) ^ (k + 1) ≤ 2 ^ ℓ k := pow_le_pow_right₀ (by norm_num) hkℓ
    rw [pow_succ] at this
    linarith
  linarith

end CanonicalDerandomizer

/-- A stretch of `2 ^ Ω(k)`, for a real `ε > 0`, is at least `2 ^ ⌊k / e⌋` from some point on,
for a natural `e > 0`. -/
private theorem exists_two_pow_div_le {ℓ : ℕ → ℕ}
    (h : ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k : ℕ in atTop, (2 : ℝ) ^ (ε * k) ≤ ℓ k) :
    ∃ e K : ℕ, 0 < e ∧ ∀ k, K ≤ k → 2 ^ (k / e) ≤ ℓ k := by
  obtain ⟨ε, hε, hev⟩ := h
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  obtain ⟨e, he, hεe⟩ := Real.exists_nat_pos_inv_lt hε
  have hεe : 1 / (e : ℝ) ≤ ε := by simpa only [one_div] using hεe.le
  refine ⟨e, K, he, fun k hk => ?_⟩
  have hdiv : ((k / e : ℕ) : ℝ) ≤ ε * k := by
    calc ((k / e : ℕ) : ℝ) ≤ (k : ℝ) / e := Nat.cast_div_le
      _ = k * (1 / (e : ℝ)) := by ring
      _ ≤ k * ε := mul_le_mul_of_nonneg_left hεe (by positivity)
      _ = ε * k := mul_comm _ _
  have : (2 : ℝ) ^ ((k / e : ℕ) : ℝ) ≤ ℓ k :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hdiv).trans (hK k hk)
  rw [Real.rpow_natCast] at this
  exact_mod_cast this

/-- **Goldreich, Theorem 8.16** [Goldreich, Theorem 8.16][Goldreich2007DraftR4] (draft r4, printed
page 339, PDF page 75): *if there exists a canonical derandomizer of stretch `ℓ(k) = 2 ^ Ω(k)`,
then `BPP = P`*, for every encoding `enc` of instances. Stretch `2 ^ Ω(k)` means that for some
`ε > 0`, `ℓ(k) ≥ 2 ^ (ε k)` for all large `k`.

For a verifier reading `p(n)` random bits whose circuit with the instance hardwired has
`O(n ^ a)` gates, seeds of `k = O(log n)` bits have `ℓ(k) ≥ n ^ a`. The generator then fools that
circuit within `1 / 6`, so the majority over the seeds is correct
(`Cslib.Complexity.seedDecider_eq_true_iff_of_advantage_lt`). The decider runs the generator in
time `poly(2 ^ k ℓ(k)) = poly(2 ^ k)` by the bound `ℓ(k) = O(2 ^ k)` of Exercise 8.18
(`Cslib.Complexity.CanonicalDerandomizer.le_two_pow`), polynomial in `n`. -/
theorem P_eq_BPP_of_canonicalDerandomizer {G : List Bool → List Bool} {ℓ : ℕ → ℕ}
    (hG : CanonicalDerandomizer G ℓ)
    (hstretch : ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k : ℕ in atTop, (2 : ℝ) ^ (ε * k) ≤ ℓ k)
    {α : Type} (enc : α ↪ List Bool) : P enc = BPP enc := by
  refine P_subset_BPP.antisymm ?_
  rintro A ⟨p, V, hV, hA⟩
  obtain ⟨e, K, he, hK⟩ := exists_two_pow_div_le hstretch
  -- the verifier with its instance hardwired is a circuit of polynomial size
  obtain ⟨c₁, a₁, hB⟩ := exists_complexity_verifierTest_le p hV
  have hBpoly : PolynomiallyBounded fun N => c₁ * (N + 1) ^ a₁ := by fun_prop
  obtain ⟨e₁, he₁⟩ := hBpoly.exists_clog_le_mul_log
  -- seeds of `e e₁ (⌊log₂ n⌋ + 1) + K` bits
  set seed : α → ℕ := fun x => e * (e₁ * (Nat.log 2 (enc x).length + 1)) + K with hseed_def
  set gen : α → List Bool → List Bool := fun x z =>
    (G (z.take (seed x))).take (p.eval (enc x).length)
  refine ⟨seedDecider V gen seed, ?_, fun x => ?_⟩
  · -- the running time
    obtain ⟨D, hGO⟩ := hG.time
    have hlog2 : ComputableInPolyTime (fun x => Nat.log 2 (enc x).length) enc encUnary :=
      ComputableInPolyTime.binary_log_two.comp
        (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.encoding_length enc))
    have hseed : ComputableInPolyTime seed enc encUnary := by
      simp only [hseed_def]; fun_prop
    have hT : Monotone fun k => (2 ^ k * (ℓ k + 1)) ^ D := fun a b h =>
      Nat.pow_le_pow_left (Nat.mul_le_mul (Nat.pow_le_pow_right two_pos h)
        (Nat.add_le_add_right (hG.monotone h) 1)) D
    have hGbound : PolyBounded (fun x => (enc x).length) fun x =>
        (2 ^ seed x * (ℓ (seed x) + 1)) ^ D := by
      growth_poly [hG.le_two_pow]
    have hGq : ComputableInPolyTime (fun q : α × List Bool => G (q.2.take (seed q.1)))
        (encPair enc encBits) encBits :=
      ComputableInO.computableInPolyTime_take hT hGO hseed hGbound
    have hm : ComputableInPolyTime (fun q : α × List Bool => p.eval (enc q.1).length)
        (encPair enc encBits) encUnary :=
      (ComputableInPolyTime.unary_eval p).comp
        ((ComputableInPolyTime.encoding_length enc).comp (ComputableInPolyTime.fst enc encBits))
    have hgen : ComputableInPolyTime (fun q : α × List Bool => gen q.1 q.2)
        (encPair enc encBits) encBits :=
      ComputableInPolyTime.bitsTakeWithInput hGq hm
    exact computableInPolyTime_seedDecider hV hgen hseed (by growth_poly)
  · -- correctness on every instance
    obtain ⟨hpB, hcB⟩ := hB x
    have hBℓ : c₁ * ((enc x).length + 1) ^ a₁ ≤ ℓ (seed x) := by
      have hdiv : e₁ * (Nat.log 2 (enc x).length + 1) ≤ seed x / e :=
        (Nat.le_div_iff_mul_le he).2 (by simp only [hseed_def]; nlinarith)
      calc c₁ * ((enc x).length + 1) ^ a₁
          ≤ 2 ^ Nat.clog 2 (c₁ * ((enc x).length + 1) ^ a₁) := Nat.le_pow_clog one_lt_two _
        _ ≤ 2 ^ (e₁ * (Nat.log 2 (enc x).length + 1)) :=
          Nat.pow_le_pow_right two_pos (he₁ (enc x).length)
        _ ≤ 2 ^ (seed x / e) := Nat.pow_le_pow_right two_pos hdiv
        _ ≤ ℓ (seed x) := hK _ (by simp only [hseed_def]; omega)
    have hmℓ : p.eval (enc x).length ≤ ℓ (seed x) := hpB.trans hBℓ
    have hcirc : IsCircuitTest (ℓ (seed x) ^ 2) fun y : BitString (ℓ (seed x)) =>
        PMF.pure (V (x, (List.ofFn y).take (p.eval (enc x).length))) :=
      ⟨_, (hcB _ hmℓ).trans (hBℓ.trans (Nat.le_self_pow two_ne_zero _)), rfl⟩
    refine (seedDecider_eq_true_iff_of_advantage_lt (hA x).1
      (fun hx => boundedErrorAt_false_iff.1 ((hA x).2 hx)) hG.length_eq gen seed (fun z => ?_) hmℓ
      (hG.fools _ _ hcirc)).symm
    simp only [gen, List.take_of_length_le (le_of_eq (List.length_ofFn (f := z)))]

/-! ### Arora and Barak's pseudorandom generators -/

/-- **`S(ℓ)`-pseudorandom generators** [Arora and Barak, Definition 16.2][AroraBarak07] (draft of
2007-01-08, printed pages 283–284, PDF pages 299–300). For a non-decreasing `S`, the generator `G`
has outputs of `S(ℓ)` bits on seeds of `ℓ` bits, is computable within time `2 ^ (c ℓ)` for some
constant `c`, and for every `ℓ`, every De Morgan circuit with at most `S(ℓ) ^ 3` gates distinguishes
`G` on a uniform seed of `ℓ` bits from a uniform string of `S(ℓ)` bits with advantage below
`1 / 10`.

Deviations, each of which only admits more generators: the definition also requires `S` to be
polynomial-time computable, which no result here uses, so the record omits it; the time bound is
up to a constant factor and also bounds the space, as `Turing.MultiTapeTM.ComputableInO` requires.
No such generator with `S` super-polynomial is known to exist unconditionally; the record is a
hypothesis. -/
structure ExponentialTimePRG (G : List Bool → List Bool) (S : ℕ → ℕ) : Prop where
  /-- The output length is non-decreasing in the seed length. -/
  monotone : Monotone S
  /-- The output length depends only on the seed length. -/
  length_eq : ∀ z, (G z).length = S z.length
  /-- The generator runs in time `2 ^ (c ℓ)` on seeds of `ℓ` bits. -/
  time : ∃ c : ℕ, ComputableInO G encBits encBits (fun z => 2 ^ (c * z.length))
    fun z => 2 ^ (c * z.length)
  /-- Every circuit with at most `S(ℓ) ^ 3` gates has advantage below `1 / 10`. -/
  pseudorandom : ∀ ℓ adversary, IsCircuitTest (S ℓ ^ 3) adversary →
    (wordFamily G S ℓ).advantage adversary < 1 / 10

/-- **An `S(ℓ)`-pseudorandom generator is a canonical derandomizer of stretch `S`.** Its time
`2 ^ (c ℓ)` is at most `(2 ^ ℓ (S(ℓ) + 1)) ^ c`, circuits with `S(ℓ) ^ 2` gates have at most
`S(ℓ) ^ 3` gates, and `1 / 10 < 1 / 6` [Arora and Barak, Definition 16.2][AroraBarak07],
[Goldreich, Definition 8.14][Goldreich2007DraftR4]. -/
theorem ExponentialTimePRG.canonicalDerandomizer {G : List Bool → List Bool} {S : ℕ → ℕ}
    (hG : ExponentialTimePRG G S) : CanonicalDerandomizer G S := by
  obtain ⟨c, hc⟩ := hG.time
  have hle (z : List Bool) : 2 ^ (c * z.length) ≤ (2 ^ z.length * (S z.length + 1)) ^ c := by
    rw [mul_comm c, pow_mul]
    exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)) c
  refine ⟨hG.monotone, hG.length_eq, ⟨c, hc.mono_le hle hle⟩, fun k adversary hadv => ?_⟩
  have hsize : S k ^ 2 ≤ S k ^ 3 := by
    rcases Nat.eq_zero_or_pos (S k) with h | h
    · simp [h]
    · exact Nat.pow_le_pow_right h (by norm_num)
  obtain ⟨test, htest, rfl⟩ := hadv
  have := hG.pseudorandom k _ ⟨test, htest.trans hsize, rfl⟩
  linarith

/-- **Arora and Barak, Corollary 16.6 (1)** [Arora and Barak, Corollary 16.6][AroraBarak07] (draft
of 2007-01-08, printed page 285, PDF page 301): *if there exists a `2 ^ (ε ℓ)`-pseudorandom
generator for some constant `ε > 0`, then `BPP = P`*, for every encoding `enc` of instances. The
output length `S(ℓ)` need only be at least `2 ^ (ε ℓ)` for all large `ℓ`, which covers any rounding
of `2 ^ (ε ℓ)` to a natural number. The corollary follows from Goldreich's Theorem 8.16
(`Cslib.Complexity.P_eq_BPP_of_canonicalDerandomizer`) through
`Cslib.Complexity.ExponentialTimePRG.canonicalDerandomizer`; the draft derives it from its
Lemma 16.4 (Exercise 16.1). -/
theorem P_eq_BPP_of_exponentialTimePRG {G : List Bool → List Bool} {S : ℕ → ℕ}
    (hG : ExponentialTimePRG G S)
    (hS : ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ ℓ : ℕ in atTop, (2 : ℝ) ^ (ε * ℓ) ≤ S ℓ)
    {α : Type} (enc : α ↪ List Bool) : P enc = BPP enc :=
  P_eq_BPP_of_canonicalDerandomizer hG.canonicalDerandomizer hS enc

end Cslib.Complexity
