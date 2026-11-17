/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BPP
public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification
public import CslibFrontier.Computability.Languages.Slice
import CslibFrontier.Computability.Circuit.Boolean.PolynomialTime
import CslibFrontier.Computability.Circuit.Boolean.Substitution
import CslibFrontier.Computability.Complexity.Classes.BPP.Derandomization.Generator
import CslibFrontier.Computability.Complexity.Classes.BPP.Derandomization.SeedEnumeration
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log

/-!
# Derandomizing BPP from average-case hardness

**Hardness versus randomness** [NisanWigderson1994]: if some problem in `E`, decidable in time
`2 ^ O(n)`, is average-case hard for circuits of size `2 ^ (n / c)`, then `BPP = P`
[Arora and Barak, Chapter 20][AroraBarak09]. Here the hardness is
`Cslib.Circuits.Boolean.IsAverageCaseHard` for nonuniform De Morgan circuits, with the non-strict
bound produced by Yao's XOR lemma, and the conclusion is uniform: every problem in `BPP enc` is in
`P enc`, for every encoding `enc` of instances (`BPP_subset_P_of_isAverageCaseHard`), so
`P enc = BPP enc` (`P_eq_BPP_of_isAverageCaseHard`). A hardness `2 ^ (ε n)` for a real `ε > 0`
gives the hypothesis for every natural `c ≥ 1 / ε`, by
`Cslib.Circuits.Boolean.IsAverageCaseHard.mono`.

The deterministic algorithm is the seed-enumeration decider `Cslib.Complexity.seedDecider` over
the Nisan–Wigderson generator. On an instance of length `N` it sets
`t = t₀ + e (⌊log₂ N⌋ + 1)` for constants `t₀` and `e`, and runs the verifier on the output of the
Nisan–Wigderson generator for all `2 ^ ℓ` seeds of `ℓ = (2 ^ (8 c + 1) + 1) t` bits, taking the
majority. The generator uses the greedy design (`Cslib.Crypto.PRG.NisanWigderson.Design.greedy`)
with blocks of `n = 4 c t` positions sharing at most `t - 1` of them, and the hard function on `n`
bits, evaluated in time `2 ^ O(n)`. Both `2 ^ ℓ` and `2 ^ O(n)` are polynomial in `N`, so the
algorithm runs in polynomial time (`Cslib.Complexity.computableInPolyTime_seedDecider`,
`Cslib.Complexity.computableInPolyTime_listGenerator_greedyMasks`).

For correctness, the verifier with the instance fixed is a circuit of polynomial size in its
random string (`Cslib.Circuits.Boolean.PPoly.exists_of_polyTime`), and `t` is chosen so that
`2 ^ t` is at least eight times the size of this circuit and the number `m` of random bits. The
greedy design then has at least `m` blocks (`Cslib.Crypto.PRG.NisanWigderson.le_length_greedyMasks`)
and the hardness `2 ^ (n / c) = 2 ^ (4 t)` exceeds the size of the reconstructed circuits and `6 m`.
By `Cslib.Crypto.PRG.NisanWigderson.abs_card_div_sub_card_div_lt`, the fraction of seeds on which
the verifier accepts is within `1 / 6` of the fraction of random strings on which it accepts, which
is at least `2 / 3` on members and at most `1 / 3` on other instances, so the majority is correct
(`Cslib.Complexity.seedDecider_eq_true_iff`).

## Main results

* `Cslib.Complexity.PromiseBPP_subset_PromiseP_of_isAverageCaseHard`: if a problem in `E` has
  slices average-case hard for size `2 ^ (n / c)` for all large `n`, then
  `PromiseBPP enc ⊆ PromiseP enc`.
* `Cslib.Complexity.BPP_subset_P_of_isAverageCaseHard`: the same for `BPP enc ⊆ P enc`.
* `Cslib.Complexity.P_eq_BPP_of_isAverageCaseHard`: under the same hypothesis, `P enc = BPP enc`.

The worst-case to average-case amplification, giving the same conclusion from a problem in `E`
outside `SIZE (2 ^ (ε n))` [ImpagliazzoWigderson1997], and the endpoint of Babai, Fortnow, Nisan
and Wigderson from `EXP ⊄ P/poly` [BabaiFortnowNisanWigderson1993] are not formalized here.

## References

* [N. Nisan, A. Wigderson, *Hardness vs randomness*][NisanWigderson1994]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 20
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Crypto.PRG.NisanWigderson Turing.MultiTapeTM
  Finset Filter

/-! ### The main theorem -/

/-- The seed map of the Nisan–Wigderson derandomization: on an instance `x` and a seed, the
generator of the hard function `g` with blocks of `block x` positions and the first `out x` masks
of the greedy design with seeds of `seed x` bits and overlaps at most `overlap x`. -/
private abbrev nwGen {α : Type} (g : List Bool → Bool) (seed block overlap out : α → ℕ) (x : α) :
    List Bool → List Bool :=
  listGenerator g (block x) ((greedyMasks (seed x) (block x) (overlap x)).take (out x))

private theorem computableInPolyTime_seedDecider_nwGen {α : Type} (enc : α ↪ List Bool)
    {V : α × List Bool → Bool} (hV : ComputableInPolyTime V (encPair enc encBits) encBool)
    {g : List Bool → Bool} {k : ℕ}
    (hg : ComputableInO g encBits encBool (fun y => 2 ^ (k * y.length))
      fun y => 2 ^ (k * y.length))
    (n₀ e c : ℕ) (p : Polynomial ℕ) :
    let t := fun N => n₀ + 3 + e * (Nat.log 2 N + 1)
    let b := 2 ^ (8 * c + 1)
    ComputableInPolyTime
      (seedDecider V (nwGen g (fun x => (b + 1) * t (enc x).length)
        (fun x => c * (4 * t (enc x).length)) (fun x => t (enc x).length - 1)
        (fun x => p.eval (enc x).length)) fun x => (b + 1) * t (enc x).length)
      enc encBool := by
  intro t b
  have hlog2 : ComputableInPolyTime (fun x => Nat.log 2 (enc x).length) enc encUnary :=
    ComputableInPolyTime.binary_log_two.comp
      (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.encoding_length enc))
  have hlog : ComputableInPolyTime (fun x => t (enc x).length) enc encUnary := by
    dsimp only [t]; fun_prop
  have hbudget (d : ℕ) : PolyBounded (fun x => (enc x).length) fun x =>
      2 ^ (d * t (enc x).length) := by
    refine PolyBounded.of_polynomiallyBounded (fun x => (enc x).length)
      (bound := fun N => 2 ^ (d * (n₀ + 3)) * 2 ^ (d * e * (Nat.log 2 N + 1)))
      ((PolynomiallyBounded.const _).mul (polynomiallyBounded_two_pow_mul_log _)) |>.mono
      fun x => le_of_eq ?_
    rw [← pow_add]; dsimp [t]; ring_nf
  have hseedO : ComputableInPolyTime (fun x => (b + 1) * t (enc x).length) enc encUnary := by
    fun_prop
  have hblockO : ComputableInPolyTime (fun x => c * (4 * t (enc x).length)) enc encUnary := by
    fun_prop
  have hoverlapO : ComputableInPolyTime (fun x => t (enc x).length - 1) enc encUnary := by
    fun_prop
  have houtO : ComputableInPolyTime (fun x => p.eval (enc x).length) enc encUnary := by
    fun_prop
  refine computableInPolyTime_seedDecider hV (computableInPolyTime_listGenerator_greedyMasks
    (fun _ _ h => Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_left k h)) hg hseedO
    hblockO hoverlapO houtO
    (hbudget (b + 1)) ((hbudget (k * (c * 4))).mono fun x => le_of_eq ?_)) hseedO (hbudget (b + 1))
  ring_nf

private theorem nw_design_and_size_bounds {c m Tc τ : ℕ} (hc : 0 < c) (hτ3 : 3 ≤ τ)
    (hBτ : 8 * (m + Tc + 5) ≤ 2 ^ τ) :
    m ≤ (greedyMasks ((2 ^ (8 * c + 1) + 1) * τ) (c * (4 * τ)) (τ - 1)).length ∧
    Tc + 2 + 1 + m * (2 ^ (τ - 1) * (2 * (τ - 1) + 3) + 1) + 1 ≤ 2 ^ (4 * τ) ∧
    (m : ℝ) < 1 / 6 * ((2 ^ (4 * τ) : ℕ) : ℝ) := by
  set b := 2 ^ (8 * c + 1) with hb
  set P := 2 ^ τ with hP
  have hP8 : 8 ≤ P := (Nat.pow_le_pow_right two_pos hτ3).trans_eq' rfl
  have hc4 : c * 4 ≤ b + 1 := by
    have h₁ : c < 2 ^ c := Nat.lt_two_pow_self
    have h₂ : 2 ^ c * 4 ≤ b := by
      rw [hb, show 2 ^ c * 4 = 2 ^ (c + 2) by rw [pow_add]; rfl]
      exact Nat.pow_le_pow_right two_pos (by omega)
    omega
  have hlen : m ≤ (greedyMasks ((b + 1) * τ) (c * (4 * τ)) (τ - 1)).length := by
    refine le_length_greedyMasks (by omega) (by nlinarith) (by nlinarith) ?_
    calc 4 ^ (c * (4 * τ)) * m ≤ 4 ^ (c * (4 * τ)) * P := Nat.mul_le_mul_left _ (by omega)
      _ = b ^ τ := by
        rw [hb, hP, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul, ← pow_add]; ring_nf
  have hY : 2 ^ (τ - 1) * (2 * (τ - 1) + 3) + 1 ≤ P ^ 2 := by
    have hQ : 2 ^ (τ - 1) * 2 = P := by rw [hP, ← pow_succ, Nat.sub_add_cancel (by omega)]
    have := Nat.lt_two_pow_self (n := τ - 1); have := @Nat.one_le_two_pow (τ - 1)
    rw [← hQ]; nlinarith
  have h₂ : 8 * (m * P ^ 2) ≤ P ^ 3 :=
    calc 8 * (m * P ^ 2) = 8 * m * P ^ 2 := by ring
      _ ≤ P * P ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = P ^ 3 := by ring
  have h₃ : 8 * P ^ 3 ≤ P ^ 4 := by
    rw [pow_succ P 3, mul_comm (P ^ 3)]; exact Nat.mul_le_mul_right _ hP8
  have h₄ : P ≤ P ^ 4 := Nat.le_self_pow (by norm_num) P
  have h₁ := Nat.mul_le_mul_left m hY
  have h6m : 6 * m < 2 ^ (4 * τ) := by rw [mul_comm 4 τ, pow_mul, ← hP]; omega
  refine ⟨hlen, by rw [mul_comm 4 τ, pow_mul, ← hP]; omega, ?_⟩
  have h6m' : (6 * m : ℝ) < ((2 ^ (4 * τ) : ℕ) : ℝ) := by exact_mod_cast h6m
  linarith

/-- **Hardness versus randomness for promise problems: average-case hardness in `E` derandomizes
`PromiseBPP`** [NisanWigderson1994], [Arora and Barak, Chapter 20][AroraBarak09]. Let `L` be a
problem on words in `E`, decidable in time `O(2 ^ (k n))` for some `k`, and let `c > 0`. If for all
large `n` the slice of `L` at `n` is average-case hard for size `2 ^ (n / c)`, that is, every
Boolean function of De Morgan circuit complexity at most `2 ^ (n / c)` agrees with it on at most a
`1 / 2 + 2 ^ (-(n / c))` fraction of the words of length `n`, then every promise problem in
`PromiseBPP enc` is in `PromiseP enc`, for every encoding `enc` of instances.

The hardness is nonuniform and non-strict (`Cslib.Circuits.Boolean.IsAverageCaseHard`); the
conclusion is uniform, with the deterministic decider `Cslib.Complexity.seedDecider` over the
Nisan–Wigderson generator. The decider is correct on every instance where the verifier has bounded
error, which is what the promise asks. -/
theorem PromiseBPP_subset_PromiseP_of_isAverageCaseHard {L : Language Bool} {c : ℕ}
    (hL : (L : Set (List Bool)) ∈ E encBits) (hc : 0 < c)
    (hard : ∀ᶠ n in atTop, IsAverageCaseHard (L.slice n) (2 ^ (n / c)))
    {α : Type} (enc : α ↪ List Bool) : PromiseBPP enc ⊆ PromiseP enc := by
  rintro Q ⟨p, V, hV, hdec⟩
  obtain ⟨k, hL⟩ := mem_E_iff.1 hL
  obtain ⟨g, hgL, hg⟩ := exists_computableInO_of_mem_DTIME hL
  have hslice (n : ℕ) : (fun y : Fin n → Bool => g (List.ofFn y)) = L.slice n := by
    funext y; rw [Bool.eq_iff_iff, Language.slice_eq_true_iff, ← hgL]; rfl
  obtain ⟨L', hL', hVL'⟩ := PPoly.exists_of_polyTime hV
  set Tc : ℕ → ℕ := fun N =>
    complexity interpretation (single (L'.slice (2 * N + 1 + p.eval N)))
  have hTcpoly : PolynomiallyBounded Tc :=
    (mem_PPoly.1 hL').comp (g := fun N => 2 * N + 1 + p.eval N) (by fun_prop)
  set B : ℕ → ℕ := fun N => p.eval N + Tc N + 5 with hB
  have hBpoly : PolynomiallyBounded B := by simp only [hB]; fun_prop
  obtain ⟨e, he⟩ := hBpoly.exists_clog_le_mul_log
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hard
  set t : ℕ → ℕ := fun N => n₀ + 3 + e * (Nat.log 2 N + 1) with ht
  set b := 2 ^ (8 * c + 1)
  -- the decider gives the expected answer on every instance where `V` has bounded error
  suffices key : ∀ x (ans : Bool), BoundedErrorAt enc p V x ans →
      seedDecider V (nwGen g (fun x => (b + 1) * t (enc x).length)
        (fun x => c * (4 * t (enc x).length)) (fun x => t (enc x).length - 1)
        (fun x => p.eval (enc x).length)) (fun x => (b + 1) * t (enc x).length) x = ans by
    exact mem_PromiseP_iff.2 ⟨_, computableInPolyTime_seedDecider_nwGen enc hV hg n₀ e c p,
      fun x hx => key x true ((hdec x).1 hx), fun x hx => key x false ((hdec x).2 hx)⟩
  intro x ans hans
  set N := (enc x).length
  set τ := t N with hτ
  set m := p.eval N
  have hτ3 : n₀ + 3 ≤ τ := by simp only [hτ, ht]; omega
  have hBτ : 8 * B N ≤ 2 ^ τ := by
    rw [hτ, ht, pow_add]
    exact Nat.mul_le_mul (by rw [pow_add]; exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
      ((Nat.le_pow_clog one_lt_two _).trans (Nat.pow_le_pow_right two_pos (he N)))
  obtain ⟨hlen, hs, hεs⟩ := nw_design_and_size_bounds hc (by omega) hBτ
  have hhard : IsAverageCaseHard (L.slice (c * (4 * τ))) (2 ^ (4 * τ)) := by
    have h := hn₀ (c * (4 * τ)) (by nlinarith)
    rwa [Nat.mul_div_cancel_left _ hc] at h
  set test : BooleanFunction m := fun r => V (x, List.ofFn r) with htest_def
  have htest : complexity interpretation (single test) ≤ Tc N + 2 := by
    have h := complexity_le_of_append_take L' (frame (enc x)) le_rfl (f := test) fun r => by
      rw [htest_def, List.take_of_length_le (by simp), hVL', encPair_apply, encBits_apply]
    rwa [length_frame] at h
  have hgap := abs_card_div_sub_card_div_lt (Design.greedy _ _ _ _ hlen) hhard hs hεs test htest
  refine seedDecider_eq_of_boundedError (fun h => boundedErrorAt_true_iff.1 (h ▸ hans))
    (fun h => boundedErrorAt_false_iff.1 (h ▸ hans)) _ _ ?_
  have hseeds : #{z : Fin ((b + 1) * τ) → Bool |
      V (x, nwGen g (fun x => (b + 1) * t (enc x).length) (fun x => c * (4 * t (enc x).length))
        (fun x => t (enc x).length - 1) (fun x => p.eval (enc x).length) x (List.ofFn z)) =
          true} =
      #{z | test (generator (Design.greedy ((b + 1) * τ) (c * (4 * τ)) (τ - 1) m hlen)
        (L.slice (c * (4 * τ))) z) = true} := by
    refine congrArg _ (filter_congr fun z _ => ?_)
    rw [htest_def, nwGen, listGenerator_take_greedyMasks hlen, hslice]
  rw [hseeds]
  exact hgap

/-- **Hardness versus randomness: average-case hardness in `E` derandomizes `BPP`**
[NisanWigderson1994], [Arora and Barak, Chapter 20][AroraBarak09]: under the hypothesis of
`PromiseBPP_subset_PromiseP_of_isAverageCaseHard`, every problem in `BPP enc` is in `P enc`, for
every encoding `enc` of instances. This is the promise result for promise problems without
promise. -/
theorem BPP_subset_P_of_isAverageCaseHard {L : Language Bool} {c : ℕ}
    (hL : (L : Set (List Bool)) ∈ E encBits) (hc : 0 < c)
    (hard : ∀ᶠ n in atTop, IsAverageCaseHard (L.slice n) (2 ^ (n / c)))
    {α : Type} (enc : α ↪ List Bool) : BPP enc ⊆ P enc := fun _ hA =>
  ofSet_mem_PromiseP.1
    (PromiseBPP_subset_PromiseP_of_isAverageCaseHard hL hc hard enc (ofSet_mem_PromiseBPP.2 hA))

/-- **Hardness versus randomness: `P = BPP` from average-case hardness in `E`**
[NisanWigderson1994], [Arora and Barak, Chapter 20][AroraBarak09]. If some problem in `E` has
slices that are average-case hard for size `2 ^ (n / c)` for all large `n`, for some `c > 0`, then
`P enc = BPP enc` for every encoding `enc` of instances. -/
theorem P_eq_BPP_of_isAverageCaseHard {L : Language Bool} {c : ℕ}
    (hL : (L : Set (List Bool)) ∈ E encBits) (hc : 0 < c)
    (hard : ∀ᶠ n in atTop, IsAverageCaseHard (L.slice n) (2 ^ (n / c)))
    {α : Type} (enc : α ↪ List Bool) : P enc = BPP enc :=
  P_subset_BPP.antisymm (BPP_subset_P_of_isAverageCaseHard hL hc hard enc)

end Cslib.Complexity
