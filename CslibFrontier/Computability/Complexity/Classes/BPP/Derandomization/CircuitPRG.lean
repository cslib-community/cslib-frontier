/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BPP.Derandomization.SeedEnumeration
public import CslibFrontier.Computability.Complexity.Classes.Time
public import CslibFrontier.Crypto.Primitives.PRG.Circuit
public import CslibFrontier.Crypto.Primitives.PRG.Deterministic
public import CslibFrontier.Crypto.Computational.PseudorandomGenerator
public import CslibFrontier.Crypto.Computational.Nonuniform.Basic
import CslibFrontier.Computability.Circuit.Boolean.PolynomialTime
import CslibFrontier.Computability.Circuit.Boolean.Encoding.Certificate
import CslibFrontier.Computability.Circuit.Boolean.EvaluationTime
import CslibFrontier.Crypto.Computational.Stretch
import CslibFrontier.Crypto.Primitives.PRG.Game
import CslibFrontier.Computability.Circuit.Boolean.Substitution
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Search
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Foundations.Data.BitString.WordCount
import CslibFrontier.Foundations.Data.List.OfFnGetD

/-!
# Pseudorandom generators against circuits derandomize `BPP`

Arora and Barak [Arora and Barak, Theorem 10.17][AroraBarak07] (draft of 2007-01-08, printed page
201, PDF page 217): *if for every `c > 1` there is a pseudorandom generator that is secure against
circuits of size `n ^ c`, then `BPP ⊆ ⋂_{ε > 0} DTIME (2 ^ (n ^ ε))`.* Goldreich
[Goldreich, Theorem 8.13][Goldreich2007DraftR4] (draft r4, printed page 334): *if there exist
non-uniformly strong pseudorandom generators, then `BPP ⊆ ⋂_{ε > 0} DTIME (2 ^ (n ^ ε))`.*

This file proves the conclusion first under a polynomial-stretch hypothesis: for every `c > 1`, a
generator fooling circuits of size `k ^ c` with output length at least `k ^ c`
(`Cslib.Complexity.BPP_subset_DTIME_two_pow_rpow_of_polyStretch_circuitSecurePRG`). Goldreich's
Theorem 8.13 follows (`Cslib.Complexity.BPP_subset_DTIME_two_pow_rpow_of_nonuniformPRG`): a
non-uniformly strong generator (`Cslib.Crypto.NonuniformPRG`) of any stretch is amplified to every
polynomial stretch by the library's `Cslib.Crypto.NonuniformPRG.amplify`, and every such generator
fools circuits of every polynomial size (`Cslib.Crypto.NonuniformPRG.circuitSecurePRG`).

Arora and Barak's Theorem 10.17 itself is not proved. Its `c`-th generator need only have output
length `m(n) > n` and fool circuits of the fixed size `n ^ c`. Amplifying the stretch by the hybrid
argument produces distinguishers that also evaluate the generator, and the generator's circuits
need not have size at most `n ^ c`. So the available fixed-size premise does not justify the
amplification. `NonuniformPRG.amplify` applies only to generators secure against every polynomial
size.

Their pseudorandom generators are those of [Arora and Barak, Definition 10.11][AroraBarak07]
(printed pages 193–194): a polynomial-time computable family `g_n : {0,1}^n → {0,1}^{m(n)}` with
`m(n) > n` such that, for every `c'`, for all large `n` no test of the admitted class distinguishes
`g_n(U_n)` from `U_{m(n)}` with advantage more than `1 / n ^ c'`. Definition 10.11 admits uniform
probabilistic algorithms running in time `s(n)`; Theorem 10.17 asks for security against circuits
of size `n ^ c` instead, which this file reads as security against every nonuniform family of De
Morgan circuits with at most `s(n)` gates. That is `Cslib.Complexity.CircuitSecurePRG G ℓ s`: the
generator is a polynomial-time map on words with output length `ℓ k` on seeds of `k` bits, and its
restriction to seeds of `k` bits (`Cslib.Crypto.PRG.wordFamily`) is secure in the sense
of `Cslib.Crypto.PRG.Generator.Secure` against the tests computed by De Morgan circuits with at
most `s k` gates (`Cslib.Crypto.PRG.IsCircuitTest`).

The proof enumerates seeds (`Cslib.Complexity.seedDecider`). For a verifier `V` reading `p(n)`
random bits on instances of length `n`, seeds of `k ≈ n ^ (1 / d)` bits are stretched to at least
`k ^ c ≥ p(n)` bits, and `V` runs on the instance and the first `p(n)` of them. The verifier with
its instance hardwired is a circuit of polynomial size in `n`
(`Cslib.Circuits.Boolean.PPoly.exists_of_polyTime`,
`Cslib.Circuits.Boolean.complexity_le_of_append_take`), hence of size at most `k ^ c` for a
suitable `c`, and the generator for that `c` fools it within `1 / k < 1 / 6`. The majority over the
`2 ^ k` seeds is then correct (`Cslib.Complexity.seedDecider_eq_true_iff`), and it runs within
time `2 ^ O(k)` times a polynomial (`Cslib.Complexity.exists_computableInO_seedDecider`), which is
eventually below `2 ^ (n ^ ε)`. Seeds of `k = ⌊n ^ (1 / d)⌋ + K` bits, for a constant `K` beyond
the point where security holds, make the security hypothesis apply on every instance, so no
finitely many instances need to be patched.

## Main definitions

* `Cslib.Complexity.CircuitSecurePRG`: Arora and Barak's pseudorandom generators, with circuits
  of a given size as the tests.

## Main results

* `Cslib.Complexity.BPP_subset_DTIME_two_pow_rpow_of_polyStretch_circuitSecurePRG`: the
  conclusion of Theorem 10.17 of Arora and Barak, from generators of polynomial stretch; not
  Theorem 10.17 itself.
* `Cslib.Crypto.NonuniformPRG.circuitSecurePRG`: non-uniformly strong generators fool circuits of
  every polynomial size.
* `Cslib.Complexity.BPP_subset_DTIME_two_pow_rpow_of_nonuniformPRG`: Theorem 8.13 of Goldreich.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, draft][AroraBarak07],
  Section 10.2
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft
  r4][Goldreich2007DraftR4], Section 8.2.6
-/

@[expose] public section

open Turing Turing.MultiTapeTM Filter Finset
open scoped NNReal

namespace Cslib.Complexity

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Crypto.PRG

/-- **Pseudorandom generators secure against circuits of size `s`**, after
[Arora and Barak, Definition 10.11][AroraBarak07] (printed pages 193–194) with De Morgan circuits
of at most `s k` gates as the tests. `G` is a polynomial-time map on words whose outputs on seeds
of `k` bits have `ℓ k > k` bits, and for every `c`, for all large `k`, no circuit with at most
`s k` gates distinguishes `G` on a uniform seed of `k` bits from a uniform string of `ℓ k` bits
with advantage more than `1 / k ^ c`.

The tests are nonuniform: the threshold `k₀` past which every circuit with at most `s k` gates
has advantage at most `1 / k ^ c` is uniform over all circuits of each size. This is security
against every nonuniform family of circuits of size `s`, quantified "for every family, for all
large `k`": a family choosing a circuit of largest advantage at each length is one such family, so
the two orders of quantifiers agree. It is not Definition 10.11's security against uniform
probabilistic algorithms, for which this exchange of quantifiers is not available. No generator
satisfying this record is known to exist unconditionally; the record is a hypothesis. -/
structure CircuitSecurePRG (G : List Bool → List Bool) (ℓ s : ℕ → ℕ) : Prop where
  /-- One deterministic polynomial-time machine evaluates the generator. -/
  polyTime : ComputableInPolyTime G encBits encBits
  /-- The output length depends only on the seed length. -/
  length_eq : ∀ z, (G z).length = ℓ z.length
  /-- Every seed length is strictly expanded. -/
  stretch : ∀ k, k < ℓ k
  /-- For every `c`, eventually every circuit with at most `s k` gates has advantage at most
  `1 / k ^ c`. -/
  secure : ∀ c : ℕ, ∀ᶠ k in atTop,
    (wordFamily G ℓ k).Secure (IsCircuitTest (s k)) ((k : ℝ≥0) ^ c)⁻¹

section Arithmetic

/-- With `r ^ (2 e) ≤ n` and `1 / e ≤ ε`, `r ^ 2 ≤ n ^ ε`. -/
private theorem sq_le_rpow {r n e : ℕ} (he : 0 < e) (hr : r ^ (2 * e) ≤ n) {ε : ℝ}
    (hε : 1 / (e : ℝ) ≤ ε) : ((r ^ 2 : ℕ) : ℝ) ≤ (n : ℝ) ^ ε := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : r = 0 := by
      by_contra h
      have := pow_pos (Nat.pos_of_ne_zero h) (2 * e)
      omega
    subst this
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, CharP.cast_eq_zero]
    exact Real.rpow_nonneg le_rfl ε
  have hr' : (((r ^ 2) ^ e : ℕ) : ℝ) ≤ n := by
    rw [← pow_mul]; exact_mod_cast hr
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc ((r ^ 2 : ℕ) : ℝ) = ((((r ^ 2 : ℕ) : ℝ)) ^ e) ^ ((e : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (by positivity) he.ne').symm
    _ ≤ (n : ℝ) ^ ((e : ℝ)⁻¹) := by
        refine Real.rpow_le_rpow (by positivity) (by exact_mod_cast hr') (by positivity)
    _ ≤ (n : ℝ) ^ ε := Real.rpow_le_rpow_of_exponent_le hn1 (by simpa using hε)

/-- The integer `d`-th root `⌊n ^ (1 / d)⌋`, the greatest `j ≤ n` with `j ^ d ≤ n`. -/
private def rootFloor (d n : ℕ) : ℕ := Nat.findGreatest (fun j => j ^ d ≤ n) n

private theorem findGreatest_root_spec {d : ℕ} (hd : 1 ≤ d) (n : ℕ) :
    rootFloor d n ^ d ≤ n ∧ n + 1 ≤ (rootFloor d n + 1) ^ d := by
  set r := rootFloor d n
  refine ⟨Nat.findGreatest_spec (P := fun j => j ^ d ≤ n) (Nat.zero_le n)
    (by simp [Nat.zero_pow (by omega : 0 < d)]), ?_⟩
  by_contra h
  have hle : (r + 1) ^ d ≤ n := by omega
  have hr1 : r + 1 ≤ n := (Nat.le_self_pow (by omega) _).trans hle
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self r) hr1 hle

/-- `⌊n ^ (1 / d)⌋` grows: it is at least `R` once `n ≥ R ^ d`. -/
private theorem le_findGreatest_root {d R n : ℕ} (hd : 1 ≤ d) (hn : R ^ d ≤ n) :
    R ≤ rootFloor d n := by
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · exact Nat.zero_le _
  exact Nat.le_findGreatest ((Nat.le_self_pow (by omega) _).trans hn) hn

end Arithmetic

/-! ### Seed enumeration with a generator fooling the verifier -/

section SeedEnumeration

variable {α : Type} {enc : α ↪ List Bool}

/-- **A polynomial-time verifier with its instance hardwired is a small circuit.** For a
polynomial-time verifier `V` and a polynomial `p`, there are constants `c` and `a` such that, on
every instance `x` with `n = |enc x|`, both `p(n)` and the circuit complexity of the test
`y ↦ V (x, (first p(n) bits of y))` on strings of any length `L ≥ p(n)` are at most
`c (n + 1) ^ a` (`Cslib.Circuits.Boolean.PPoly.exists_of_polyTime`,
`Cslib.Circuits.Boolean.complexity_le_of_append_take`). -/
theorem exists_complexity_verifierTest_le (p : Polynomial ℕ) {V : α × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) :
    ∃ c a : ℕ, ∀ x : α, p.eval (enc x).length ≤ c * ((enc x).length + 1) ^ a ∧
      ∀ L, p.eval (enc x).length ≤ L →
        complexity interpretation (single fun y : BitString L =>
          V (x, (List.ofFn y).take (p.eval (enc x).length))) ≤ c * ((enc x).length + 1) ^ a := by
  obtain ⟨L', hL', hVL'⟩ := PPoly.exists_of_polyTime hV
  set Tc : ℕ → ℕ := fun N =>
    complexity interpretation (single (L'.slice (2 * N + 1 + p.eval N)))
  have hTcpoly : PolynomiallyBounded Tc :=
    (mem_PPoly.1 hL').comp (g := fun N => 2 * N + 1 + p.eval N) (by fun_prop)
  have hBpoly : PolynomiallyBounded fun N => p.eval N + Tc N + 2 := by fun_prop
  obtain ⟨c, a, hB⟩ := polynomiallyBounded_iff_le.1 hBpoly
  refine ⟨c, a, fun x => ⟨by have := hB (enc x).length; omega, fun L hL => ?_⟩⟩
  have h := complexity_le_of_append_take L' (frame (enc x)) hL
    (f := fun y : BitString L => V (x, (List.ofFn y).take (p.eval (enc x).length))) fun y => by
      rw [hVL', encPair_apply, encBits_apply]
  rw [length_frame] at h
  have := hB (enc x).length
  simp only [Tc] at this
  omega

/-- **Seed enumeration is correct for a generator that fools the verifier.** Let `V` decide `A`
with bounded error, reading `m = p(|x|)` random bits, and let the generator `G` have output
length `ℓ k` on seeds of `k` bits, with `m ≤ ℓ (seed x)`. If `G` on seeds of `seed x` bits fools
the test `y ↦ V (x, (first m bits of y))` with advantage below `1 / 6`, then the seed decider that
runs `V` on the first `m` bits of the generated strings answers correctly on `x`. -/
theorem seedDecider_eq_true_iff_of_advantage_lt {A : Set α} {p : Polynomial ℕ}
    {V : α × List Bool → Bool} (hA : DecidesWithBoundedError enc p V A)
    {G : List Bool → List Bool} {ℓ : ℕ → ℕ} (hlen : ∀ z, (G z).length = ℓ z.length)
    (gen : α → List Bool → List Bool) (seed : α → ℕ) {x : α}
    (hgen : ∀ z : Fin (seed x) → Bool,
      gen x (List.ofFn z) = (G (List.ofFn z)).take (p.eval (enc x).length))
    (hm : p.eval (enc x).length ≤ ℓ (seed x))
    (hadv : (wordFamily G ℓ (seed x)).advantage
      (fun y => PMF.pure (V (x, (List.ofFn y).take (p.eval (enc x).length)))) < 1 / 6) :
    seedDecider V gen seed x = true ↔ x ∈ A := by
  set k := seed x
  set m := p.eval (enc x).length
  set test : BooleanFunction (ℓ k) := fun y => V (x, (List.ofFn y).take m) with htest_def
  rw [Generator.advantage_pure_eq] at hadv
  have hseeds : #{z : BitString k | test (wordFamily G ℓ k z) = true} =
      #{z : Fin k → Bool | V (x, gen x (List.ofFn z)) = true} := by
    refine congrArg _ (filter_congr fun z _ => ?_)
    simp only [test, hgen]
    rw [show wordFamily G ℓ k z = fun i : Fin (ℓ k) => (G (List.ofFn z)).getD i false from rfl,
      List.ofFn_getD_eq_of_length false (by rw [hlen, List.length_ofFn])]
  have hstrings : (#{y : BitString (ℓ k) | test y = true} : ℝ) / 2 ^ ℓ k =
      #{r : Fin m → Bool | V (x, List.ofFn r) = true} / 2 ^ m := by
    have hcount := BitString.card_filter_take hm fun w => V (x, w) = true
    simp only [test]
    rw [hcount, ← pow_sub_mul_pow 2 hm]
    push_cast
    field_simp
  rw [hseeds, hstrings] at hadv
  exact seedDecider_eq_true_iff hA gen seed hadv

end SeedEnumeration

/-- **Not Arora–Barak Theorem 10.17: its conclusion under an extra stretch hypothesis.** If for
every `c > 1` there is a pseudorandom generator secure against circuits of size `k ^ c` on seeds of
`k` bits (`Cslib.Complexity.CircuitSecurePRG`) *and with output length at least `k ^ c` for all
large `k`*, then for every `ε > 0` every problem in `BPP enc` is in `DTIME enc (2 ^ ⌈n ^ ε⌉)`, for
every encoding `enc` of instances.

[Arora and Barak, Theorem 10.17][AroraBarak07] (draft of 2007-01-08, printed page 201) assumes only
the output length `m(n) > n` of Definition 10.11; its proof stretches seeds of `n ^ ε` bits to
`n ^ k` bits, which needs stretch amplification. The library's `Cslib.Crypto.NonuniformPRG.amplify`
needs security against every polynomial size, while the `c`-th generator here fools only circuits
of size `k ^ c`, and the hybrid distinguishers also evaluate the generator. Goldreich's Theorem
8.13, with that stronger security, is `BPP_subset_DTIME_two_pow_rpow_of_nonuniformPRG`. The bound
`2 ^ ⌈n ^ ε⌉` is the draft's `2 ^ (n ^ ε)`, rounded up to a natural exponent. -/
theorem BPP_subset_DTIME_two_pow_rpow_of_polyStretch_circuitSecurePRG
    (h : ∀ c : ℕ, 1 < c → ∃ (G : List Bool → List Bool) (ℓ : ℕ → ℕ),
      (∀ᶠ k in atTop, k ^ c ≤ ℓ k) ∧ CircuitSecurePRG G ℓ (· ^ c))
    {α : Type} (enc : α ↪ List Bool) :
    BPP enc ⊆ ⋂ (ε : ℝ) (_ : 0 < ε), DTIME enc fun n => 2 ^ ⌈(n : ℝ) ^ ε⌉₊ := by
  rintro A ⟨p, V, hV, hA⟩
  simp only [Set.mem_iInter]
  intro ε hε
  -- the verifier with its instance hardwired is a circuit of polynomial size
  obtain ⟨c₁, a₁, hB⟩ := exists_complexity_verifierTest_le p hV
  -- seeds of `⌊n ^ (1 / d)⌋ + K` bits, with `1 / e ≤ ε` and `d = 2 e`
  obtain ⟨e, he, hεe⟩ := Real.exists_nat_pos_inv_lt hε
  have hεe : 1 / (e : ℝ) ≤ ε := by simpa only [one_div] using hεe.le
  set d := 2 * e with hd_def
  have hd : 1 ≤ d := by omega
  -- the generator for circuits of size `k ^ c`
  set c := d * a₁ + 2
  obtain ⟨G, ℓ, hℓ, hG⟩ := h c (by omega)
  obtain ⟨K, hK⟩ := eventually_atTop.1 (((hG.secure 1).and hℓ).and
    (eventually_ge_atTop (c₁ + 7)))
  set seed : α → ℕ := fun x => rootFloor d (enc x).length + (K + 1)
  set gen : α → List Bool → List Bool := fun x z => (G z).take (p.eval (enc x).length)
  -- the running time
  have hgen : ComputableInPolyTime (fun q : α × List Bool => gen q.1 q.2) (encPair enc encBits)
      encBits := by
    have h₁ : ComputableInPolyTime (fun q : α × List Bool => G q.2) (encPair enc encBits)
        encBits := hG.polyTime.comp (ComputableInPolyTime.snd enc encBits)
    have h₂ : ComputableInPolyTime (fun q : α × List Bool => p.eval (enc q.1).length)
        (encPair enc encBits) encUnary :=
      (ComputableInPolyTime.unary_eval p).comp
        ((ComputableInPolyTime.encoding_length enc).comp (ComputableInPolyTime.fst enc encBits))
    exact .of_tidy (ComputableTidilyInPolyTime.bitsTakeWithInput h₁.tidy h₂.tidy)
  have hseed : ComputableInPolyTime seed enc encUnary := by
    have hlen := ComputableInPolyTime.encoding_length enc
    simp only [seed, rootFloor]
    fun_prop
  obtain ⟨C, D, hO⟩ := exists_computableInO_seedDecider hV hgen hseed
  have hmem := setOf_mem_DTIME_of_computableInO hO
    (t := fun n => C * 2 ^ (D * (rootFloor d n + (K + 1))) * (n + 1) ^ D) fun x => le_rfl
  -- correctness on every instance
  have hAeq : A = {x | seedDecider V gen seed x = true} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    set k := seed x with hk
    have hKk : K ≤ k := by simp only [hk, seed]; omega
    obtain ⟨⟨hsec, hℓk⟩, hk7⟩ := hK k hKk
    obtain ⟨-, hroot⟩ := findGreatest_root_spec hd (enc x).length
    -- the sizes are at most `k ^ c`
    have hk1 : 1 ≤ k := by omega
    have hnk : (enc x).length + 1 ≤ k ^ d :=
      hroot.trans (Nat.pow_le_pow_left (by simp only [hk, seed]; omega) d)
    have hsize : c₁ * ((enc x).length + 1) ^ a₁ ≤ k ^ c := by
      calc c₁ * ((enc x).length + 1) ^ a₁
          ≤ k * (k ^ d) ^ a₁ := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hnk a₁)
        _ = k ^ (d * a₁ + 1) := by rw [← pow_mul, pow_succ, mul_comm]
        _ ≤ k ^ c := Nat.pow_le_pow_right hk1 (by omega)
    obtain ⟨hpB, hcB⟩ := hB x
    have hmℓ : p.eval (enc x).length ≤ ℓ k := by omega
    -- the test: the verifier on the instance and the first `p(|x|)` bits
    have htest : IsCircuitTest (k ^ c) fun y : BitString (ℓ k) =>
        PMF.pure (V (x, (List.ofFn y).take (p.eval (enc x).length))) :=
      ⟨_, (hcB _ hmℓ).trans hsize, rfl⟩
    have hadv := hsec _ htest
    have h7 : (((k : ℝ≥0) ^ 1)⁻¹ : ℝ≥0) ≤ 7⁻¹ := by
      rw [pow_one]
      exact inv_anti₀ (by norm_num) (by exact_mod_cast (show 7 ≤ k by omega))
    have h7' : ((((k : ℝ≥0) ^ 1)⁻¹ : ℝ≥0) : ℝ) ≤ 1 / 7 := by
      have := NNReal.coe_le_coe.2 h7
      simpa using this
    exact (seedDecider_eq_true_iff_of_advantage_lt hA hG.length_eq gen seed (fun _ => rfl) hmℓ
      (by linarith)).symm
  rw [hAeq]
  -- the time bound is eventually below `2 ^ ⌈n ^ ε⌉`
  have hev : ∀ᶠ n in atTop, C * 2 ^ (D * (rootFloor d n + (K + 1))) * (n + 1) ^ D ≤
      C * 2 ^ (D * (K + 1)) * 2 ^ ⌈(n : ℝ) ^ ε⌉₊ := by
    filter_upwards [eventually_ge_atTop ((D * (d + 1)) ^ d)] with n hn
    obtain ⟨hρd, hroot⟩ := findGreatest_root_spec hd n
    have hR := le_findGreatest_root hd hn
    set ρ := rootFloor d n
    have hsq : ρ * ρ ≤ ⌈(n : ℝ) ^ ε⌉₊ := by
      have h₁ := sq_le_rpow he (r := ρ) (n := n) (by rw [← hd_def]; exact hρd) hεe
      have h₂ := h₁.trans (Nat.le_ceil _)
      rw [← sq]
      exact_mod_cast h₂
    have hpow : (n + 1) ^ D ≤ 2 ^ (ρ * d * D) :=
      calc (n + 1) ^ D ≤ ((ρ + 1) ^ d) ^ D := Nat.pow_le_pow_left hroot D
        _ ≤ ((2 ^ ρ) ^ d) ^ D :=
          Nat.pow_le_pow_left (Nat.pow_le_pow_left Nat.lt_two_pow_self d) D
        _ = 2 ^ (ρ * d * D) := by rw [← pow_mul, ← pow_mul, ← Nat.mul_assoc]
    have hexp : D * ρ + ρ * d * D ≤ ρ * ρ := by
      have := Nat.mul_le_mul_right ρ hR
      nlinarith
    calc C * 2 ^ (D * (ρ + (K + 1))) * (n + 1) ^ D
        ≤ C * 2 ^ (D * (ρ + (K + 1))) * 2 ^ (ρ * d * D) :=
          Nat.mul_le_mul_left _ hpow
      _ = C * 2 ^ (D * (K + 1)) * 2 ^ (D * ρ + ρ * d * D) := by
          rw [mul_assoc, ← pow_add, mul_assoc C (2 ^ (D * (K + 1))), ← pow_add]
          ring_nf
      _ ≤ C * 2 ^ (D * (K + 1)) * 2 ^ ⌈(n : ℝ) ^ ε⌉₊ :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right two_pos (hexp.trans hsq))
  exact DTIME_mono_of_le_mul_add (C := C * 2 ^ (D * (K + 1))) (fun n => Nat.le_add_right _ _)
    (DTIME_mono_of_eventually_le hev hmem)

/-! ### Nonuniform pseudorandom generators fool circuits -/

section Nonuniform

open Cslib.Crypto Cslib.Probability

/-- **Nonuniform pseudorandom generators are circuit-secure.** A generator secure against
polynomial-time tests with polynomially bounded advice (`Cslib.Crypto.NonuniformPRG`) is secure,
for every `c`, against De Morgan circuits with `k ^ c` gates in the sense of
`Cslib.Complexity.CircuitSecurePRG`. Suppose circuits with `k ^ c` gates had advantage above
`1 / k ^ c'` for infinitely many `k`. At each such `k`, choose one violating circuit and give its
certificate (`Cslib.Circuits.Boolean.certificate`) as advice. The advised test reads the
certificate back (`Cslib.Circuits.Boolean.readCertificate`) and evaluates it on the challenge
(`Cslib.Circuits.Boolean.evalOutput`) in polynomial time, so it has the circuit's advantage at
those `k`, which contradicts negligibility. -/
theorem _root_.Cslib.Crypto.NonuniformPRG.circuitSecurePRG {G : List Bool → List Bool}
    {ℓ : ℕ → ℕ} (hG : Crypto.NonuniformPRG G ℓ) (c : ℕ) : CircuitSecurePRG G ℓ (· ^ c) := by
  refine ⟨hG.polyTime, hG.length_eq, hG.stretch, fun c' => ?_⟩
  by_contra hbad
  rw [Filter.not_eventually] at hbad
  -- at each seed length, a circuit with `k ^ c` gates, violating security if security fails
  have hex (k : ℕ) : ∃ C : Circuit signature (ℓ k) 1, C.size ≤ k ^ c ∧
      (¬ (wordFamily G ℓ k).Secure (IsCircuitTest (k ^ c)) ((k : ℝ≥0) ^ c')⁻¹ →
        (((k : ℝ≥0) ^ c')⁻¹ : ℝ) < (wordFamily G ℓ k).advantage
          fun y => PMF.pure (C.eval interpretation y 0)) := by
    have hcirc (f : BooleanFunction (ℓ k)) : ∃ C : Circuit signature (ℓ k) 1,
        C.size = complexity interpretation (single f) ∧ ∀ y, C.eval interpretation y 0 = f y := by
      obtain ⟨C, hC, hsize⟩ := exists_computes_size_eq_complexity (I := interpretation)
        (f := single f)
      exact ⟨C, hsize, Circuit.computes_single_iff.1 hC⟩
    by_cases hk : (wordFamily G ℓ k).Secure (IsCircuitTest (k ^ c)) ((k : ℝ≥0) ^ c')⁻¹
    · obtain ⟨C, hC, -⟩ := hcirc fun y => y ⟨0, by have := hG.stretch k; omega⟩
      exact ⟨C, by simp [hC], fun h => absurd hk h⟩
    · simp only [Generator.Secure, not_forall, not_le] at hk
      obtain ⟨adv, ⟨f, hf, rfl⟩, hlt⟩ := hk
      obtain ⟨C, hC, hCf⟩ := hcirc f
      refine ⟨C, hC ▸ hf, fun _ => ?_⟩
      rw [show (fun y => PMF.pure (C.eval interpretation y 0)) = fun y => PMF.pure (f y) from
        funext fun y => by rw [hCf]]
      exact hlt
  choose C hCsize hbreak using hex
  set advice : ℕ → List Bool := fun k =>
    certificate (ℓ k) (k ^ c) (C k).code.1 ((C k).outputs 0).toNat
  -- the output length is polynomial-time and polynomially bounded
  have hℓ : ComputableInPolyTime ℓ encUnary encUnary := by
    have h : ℓ = fun k => (G (List.replicate k false)).length :=
      funext fun k => by rw [hG.length_eq, List.length_replicate]
    rw [h]
    exact ComputableInPolyTime.length_bits.comp
      (hG.polyTime.comp (ComputableInPolyTime.bitsReplicate false))
  have hℓpoly : PolynomiallyBounded ℓ := ComputableTidilyInPolyTime.polynomiallyBounded hℓ.tidy
  have hadvice : PolynomiallyBounded fun k => (advice k).length := by
    have hlen : (fun k => (advice k).length) = fun k => certLength (ℓ k) (k ^ c) :=
      funext fun k => length_certificate_code (C k) (hCsize k)
    rw [hlen]
    simp only [certLength]
    fun_prop
  -- the advised test reads the certificate and evaluates its circuit on the challenge
  set test : (ℕ × List Bool) × List Bool → ProbComp Bool := fun q =>
    pure (evalOutput q.2 (readCertificate q.2.length (q.1.1 ^ c) q.1.2).1
      (readCertificate q.2.length (q.1.1 ^ c) q.1.2).2)
  have htest : IsPPTOn encAdvisedInput encBool test := by
    have hk : ComputableInPolyTime (fun q : (ℕ × List Bool) × List Bool => q.1.1)
        encAdvisedInput encUnary :=
      (ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)
    have hw : ComputableInPolyTime (fun q : (ℕ × List Bool) × List Bool => q.1.2)
        encAdvisedInput encBits :=
      (ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _)
    have hx : ComputableInPolyTime (fun q : (ℕ × List Bool) × List Bool => q.2)
        encAdvisedInput encBits := ComputableInPolyTime.snd _ _
    have hread := computableInPolyTime_readCertificate (ComputableInPolyTime.length_bits.comp hx)
      (by fun_prop : ComputableInPolyTime (fun q : (ℕ × List Bool) × List Bool => q.1.1 ^ c)
        encAdvisedInput encUnary) hw
    exact (computableInPolyTime_evalOutput hx ((ComputableInPolyTime.fst _ _).comp hread)
      ((ComputableInPolyTime.snd _ _).comp hread)).isPPTOn
  have hneg := hG.secure advice hadvice test htest
  -- its advantage at seed length `k` is that of the chosen circuit
  have hadv (k : ℕ) : (Game.advantage
      (distinguishingGame (generatorEnsemble G k) fun w => test ((k, advice k), w))
      (distinguishingGame (BitString.uniformList (ℓ k)) fun w => test ((k, advice k), w)) : ℝ) =
        (wordFamily G ℓ k).advantage fun y => PMF.pure ((C k).eval interpretation y 0) := by
    rw [← PRG.wordFamily_realExperiment hG.length_eq (fun n w => test ((n, advice n), w)),
      ← PRG.wordFamily_idealExperiment ℓ (fun n w => test ((n, advice n), w)),
      ← Generator.advantage_eq_game]
    congr 1
    funext bits
    simp only [test, advice, List.length_ofFn]
    rw [ProbComp.eval_pure, ← List.append_nil (certificate _ _ _ _),
      readCertificate_certificate_code_append (C k) (hCsize k), ← Circuit.eval_eq_evalOutput]
  -- negligible advantage contradicts the frequent breaks
  obtain ⟨m, hm⟩ := (Crypto.negligible_iff _).1 hneg c' 1 one_pos
  obtain ⟨k, hk, hkm⟩ := (hbad.and_eventually (eventually_ge_atTop (m + 1))).exists
  have hlt := hbreak k hk
  rw [← hadv k] at hlt
  have hmk := hm k (by omega)
  have hmk' : (k : ℝ) ^ c' * (Game.advantage
      (distinguishingGame (generatorEnsemble G k) fun w => test ((k, advice k), w))
      (distinguishingGame (BitString.uniformList (ℓ k)) fun w => test ((k, advice k), w)) : ℝ) <
        1 := by
    exact_mod_cast hmk
  have hpos : (0 : ℝ) < (k : ℝ) ^ c' := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    positivity
  rw [NNReal.coe_natCast, inv_lt_iff_one_lt_mul₀ hpos] at hlt
  linarith

/-- **Goldreich, Theorem 8.13** [Goldreich, Theorem 8.13][Goldreich2007DraftR4] (draft r4, printed
page 334, PDF page 70): *if there exist non-uniformly strong pseudorandom generators, then
`BPP ⊆ ⋂_{ε > 0} DTIME (2 ^ (n ^ ε))`*, for every encoding `enc` of instances.

The non-uniformly strong generators of Definition 8.12 are `Cslib.Crypto.NonuniformPRG`, whose
tests are polynomial-time machines with polynomially bounded advice in place of polynomial-size
circuit families (the model of that record; compare `Cslib.Circuits.Boolean.PPoly_eq_PAdvice`).
Any stretch `ℓ k > k` suffices: truncating to one bit of stretch (`NonuniformPRG.truncate`) and
amplifying (`NonuniformPRG.amplify`) gives, for every `c`, a generator of stretch `k ^ c + k + 1`,
which fools circuits of size `k ^ c` (`Cslib.Crypto.NonuniformPRG.circuitSecurePRG`), and
`Cslib.Complexity.BPP_subset_DTIME_two_pow_rpow_of_polyStretch_circuitSecurePRG` concludes. The
bound `2 ^ ⌈n ^ ε⌉` is the source's `2 ^ (n ^ ε)`, rounded up to a natural exponent. -/
theorem BPP_subset_DTIME_two_pow_rpow_of_nonuniformPRG {G : List Bool → List Bool}
    {ℓ : ℕ → ℕ} (hG : Crypto.NonuniformPRG G ℓ) {α : Type} (enc : α ↪ List Bool) :
    BPP enc ⊆ ⋂ (ε : ℝ) (_ : 0 < ε), DTIME enc fun n => 2 ^ ⌈(n : ℝ) ^ ε⌉₊ := by
  refine BPP_subset_DTIME_two_pow_rpow_of_polyStretch_circuitSecurePRG (fun c _ => ?_) enc
  have h₁ := hG.truncate (fun n => n + 1) (by fun_prop) (fun n => hG.stretch n)
    fun n => Nat.lt_succ_self n
  have h₂ := Crypto.NonuniformPRG.amplify h₁ (fun n => n ^ c + n + 1) (by fun_prop)
    fun n => by omega
  exact ⟨_, _, Eventually.of_forall fun k => by omega, h₂.circuitSecurePRG c⟩

end Nonuniform

end Cslib.Complexity
