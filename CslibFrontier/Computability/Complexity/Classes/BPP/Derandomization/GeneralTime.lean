/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BPP.Derandomization.CanonicalDerandomizer
import CslibFrontier.Computability.Circuit.Boolean.PolynomialTime
import CslibFrontier.Computability.Circuit.Boolean.Substitution
import CslibFrontier.Computability.Complexity.Classes.BPP.Derandomization.Generator
import CslibFrontier.Computability.Complexity.Classes.Promise.Time
import CslibFrontier.Computability.Complexity.Classes.Promise.Time.Verifier
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation

/-!
# Derandomizing `BPTIME(t)` with generators running in time exponential in the seed

Arora and Barak's Lemma 16.4 [Arora and Barak, Lemma 16.4][AroraBarak07] (draft of 2007-01-08,
printed page 284, PDF page 300) and Goldreich's Proposition 8.15
[Goldreich, Proposition 8.15][Goldreich2007DraftR4] (draft r4, printed page 339, PDF page 75)
derandomize `BPTIME(t)` for general `t` by enumerating the seeds of a generator. Under this
library's conventions their printed proofs leave a constant-factor gap. A machine in
`Cslib.Complexity.BPTIME`, which is up to constant factors, may toss `c t(n)` coins for a constant
`c` of its own, while the proofs stretch the seeds to exactly `t(n)` bits. The circuit with the
instance hardwired has `O((n + t(n)) ^ 2)` gates with a machine-dependent constant, while the
proofs take it to have at most `t(n) ^ 2` (Goldreich) or `O(t(n)) ^ 2` (Arora and Barak) gates.
This does not show the cited results false: under the sources' own conventions (exact time bounds,
an explicit coin budget) the gap may not arise, and that question is open. Neither cited result is
proved here.

This file proves the general step and conditional results. Seeds longer by a constant factor close
the gap when the stretch grows by at least any constant factor on seeds longer by a constant
factor (true for polynomial, `2 ^ (ℓ ^ ε)` and `2 ^ (ε ℓ)` stretch) and the time bound is at least
the input length.

* *The seed-length step.* For a canonical derandomizer `G` of stretch `ℓ` and a problem in
  `BPTIME(t)`, there is a constant `c` such that seeds of `k(n)` bits suffice whenever
  `ℓ(k(n)) ≥ c (t(n) + n + 1)` and `k` is computable in polynomial time: the problem is then in
  `DTIME(2 ^ O(k(n)) poly(n))`
  (`Cslib.Complexity.CanonicalDerandomizer.exists_mem_DTIME_of_mem_BPTIME`). The decider runs the
  verifier that replays the machine's coins on the first `⌊ℓ(k) / E⌋` bits of each generated
  string, for a constant `E` making that verifier's circuit, with `O((n + ℓ(k) / E) ^ 2)` gates,
  smaller than `ℓ(k) ^ 2` (`Cslib.Circuits.Boolean.exists_complexity_slice_le_of_computableInTime`).
* *Conditional forms of Goldreich's Proposition 8.15 and Arora and Barak's Lemma 16.4*, under the
  growth hypothesis and a polynomial-time seed schedule
  (`Cslib.Complexity.BPTIME_subset_DTIME_of_canonicalDerandomizer_of_growth`,
  `Cslib.Complexity.BPTIME_subset_DTIME_of_exponentialTimePRG_of_growth`). These are not the
  cited results.
* *Arora and Barak's Corollary 16.6 (2) and (3)*
  (`Cslib.Complexity.BPP_subset_quasiPoly_of_exponentialTimePRG`,
  `Cslib.Complexity.BPP_subset_DTIME_two_pow_rpow_of_exponentialTimePRG`). For `BPP` the time bound
  is polynomial, and the corollaries choose seeds with polynomial slack, so they follow from the
  seed-length step without a growth condition on the stretch. Part (1) is
  `Cslib.Complexity.P_eq_BPP_of_exponentialTimePRG`.

## Main results

* `Cslib.Complexity.CanonicalDerandomizer.exists_mem_DTIME_of_mem_BPTIME`: the seed-length step.
* `Cslib.Complexity.BPTIME_subset_DTIME_of_canonicalDerandomizer_of_growth`: not Goldreich's
  Proposition 8.15; its conclusion under a growth hypothesis and a polynomial-time seed schedule.
* `Cslib.Complexity.BPTIME_subset_DTIME_of_exponentialTimePRG_of_growth`: not Arora and Barak's
  Lemma 16.4; its conclusion under a growth hypothesis.
* `Cslib.Complexity.BPP_subset_quasiPoly_of_exponentialTimePRG`: Arora and Barak's
  Corollary 16.6 (2).
* `Cslib.Complexity.BPP_subset_DTIME_two_pow_rpow_of_exponentialTimePRG`: Arora and Barak's
  Corollary 16.6 (3).

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, draft][AroraBarak07],
  Section 16.1
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft
  r4][Goldreich2007DraftR4], Section 8.3.1
-/

public section

open Turing Turing.MultiTapeTM Filter

namespace Cslib.Complexity

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Crypto.PRG

variable {α : Type} {enc : α ↪ List Bool}

/-- A linear-time verifier with its instance hardwired, reading the first `m` bits of its random
string, has circuits with `O((n + m) ^ 2)` gates on instances whose encoding has length `n`. -/
private theorem exists_complexity_test_le {V : α × List Bool → Bool}
    (hV : ComputableInO V (encPair enc encBits) encBool (fun p => (encPair enc encBits p).length)
      fun p => (encPair enc encBits p).length) :
    ∃ B : ℕ, ∀ (x : α) (m L : ℕ), m ≤ L →
      complexity interpretation (single fun y : BitString L => V (x, (List.ofFn y).take m)) ≤
        B * ((enc x).length + m + 1) ^ 2 := by
  obtain ⟨c, hc, -⟩ := hV
  obtain ⟨L', C, hL', hC⟩ := exists_complexity_slice_le_of_computableInTime
    (t := fun N => c * (N + 1)) (s := fun N => c * (N + 1)) hc
  refine ⟨4 * C * (c + 1) ^ 2 + 2, fun x m L hmL => ?_⟩
  have h := complexity_le_of_append_take L' (frame (enc x)) hmL
    (f := fun y : BitString L => V (x, (List.ofFn y).take m)) fun y => by
      rw [hL', encPair_apply, encBits_apply]
  rw [length_frame] at h
  set n := (enc x).length
  have hle : 2 * n + 1 + m + c * (2 * n + 1 + m + 1) + 1 ≤ (c + 1) * (2 * (n + m + 1)) := by
    nlinarith
  have h1 : 1 ≤ (n + m + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  calc complexity interpretation (single fun y : BitString L => V (x, (List.ofFn y).take m))
      ≤ C * (2 * n + 1 + m + c * (2 * n + 1 + m + 1) + 1) ^ 2 + 2 :=
        h.trans (Nat.add_le_add_right (hC _) 2)
    _ ≤ C * ((c + 1) * (2 * (n + m + 1))) ^ 2 + 2 * (n + m + 1) ^ 2 :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hle 2)) (by omega)
    _ = (4 * C * (c + 1) ^ 2 + 2) * (n + m + 1) ^ 2 := by ring

/-- **Seeds of `k(n)` bits derandomize `BPTIME(t)` once `ℓ(k(n)) ≥ c (t(n) + n + 1)`.** This is
the step of [Goldreich, Proposition 8.15][Goldreich2007DraftR4] and
[Arora and Barak, Lemma 16.4][AroraBarak07] with the constant factors made explicit; it is not
either cited result, which use seeds with `ℓ(k(n)) ≥ t(n)`. For a canonical derandomizer `G` of
stretch `ℓ` and a problem `A ∈ BPTIME(t)`, there is a constant `c` such that for every seed length
`k`, computable from `n` in unary in polynomial time, with `c (t(n) + n + 1) ≤ ℓ(k(n))`, the problem
is in `DTIME(2 ^ (D k(n)) (n + 1) ^ D)` for some `D`.

The decider enumerates the seeds of `k(n)` bits and runs the verifier replaying the machine's
coins on the first `⌊ℓ(k(n)) / E⌋` bits of each generated string, for a constant `E`. These are at
least the `O(t(n))` coins the machine tosses, and the verifier with the instance hardwired has
`O((n + ℓ(k) / E) ^ 2) ≤ ℓ(k) ^ 2` gates, so the generator fools it within `1 / 6`
(Eq. 8.11). The generator's time `poly(2 ^ k ℓ(k))` is `2 ^ O(k)` by
`Cslib.Complexity.CanonicalDerandomizer.le_two_pow`. -/
theorem CanonicalDerandomizer.exists_mem_DTIME_of_mem_BPTIME {G : List Bool → List Bool}
    {ℓ : ℕ → ℕ} (hG : CanonicalDerandomizer G ℓ) {t : ℕ → ℕ} {A : Set α}
    (hA : A ∈ BPTIME enc t) :
    ∃ c : ℕ, ∀ k : ℕ → ℕ, ComputableInPolyTime k encUnary encUnary →
      (∀ n, c * (t n + n + 1) ≤ ℓ (k n)) →
      ∃ D : ℕ, A ∈ DTIME enc fun n => 2 ^ (D * k n) * (n + 1) ^ D := by
  obtain ⟨V, c₀, hVO, hcount⟩ :=
    exists_verifier_of_mem_PromiseBPTIME (ofSet_mem_PromiseBPTIME.2 hA)
  obtain ⟨B, hB⟩ := exists_complexity_test_le hVO
  set E := 2 * B + 1 with hE
  have hE0 : 0 < E := by omega
  refine ⟨E * (c₀ + 2), fun k hk hkℓ => ?_⟩
  set seed : α → ℕ := fun x => k (enc x).length with hseed_def
  set gen : α → List Bool → List Bool := fun _ z => (G z).take ((G z).length / E)
  -- correctness on every instance
  have hAeq : A = {x | seedDecider V gen seed x = true} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    set n := (enc x).length
    set L := ℓ (seed x)
    have hL : E * (c₀ + 2) * (t n + n + 1) ≤ L := hkℓ n
    have hmt : c₀ * t n + c₀ ≤ L / E := (Nat.le_div_iff_mul_le hE0).2 (le_trans (by
      rw [show (c₀ * t n + c₀) * E = E * c₀ * (t n + 1) by ring]
      exact Nat.mul_le_mul (Nat.mul_le_mul_left E (by omega)) (by omega)) hL)
    have hn1 : n + 1 ≤ L / E := (Nat.le_div_iff_mul_le hE0).2 (le_trans (by
      rw [show (n + 1) * E = E * 1 * (n + 1) by ring]
      exact Nat.mul_le_mul (Nat.mul_le_mul_left E (by omega)) (by omega)) hL)
    have hmL : L / E ≤ L := Nat.div_le_self _ _
    obtain ⟨hyes, hno⟩ := hcount x (L / E) hmt
    have hcirc : IsCircuitTest (L ^ 2) fun y : BitString L =>
        PMF.pure (V (x, (List.ofFn y).take (L / E))) := by
      refine ⟨_, (hB x (L / E) L hmL).trans ?_, rfl⟩
      calc B * (n + L / E + 1) ^ 2 ≤ B * (2 * (L / E)) ^ 2 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
        _ ≤ (E * (L / E)) ^ 2 := by rw [hE]; nlinarith
        _ ≤ L ^ 2 := Nat.pow_le_pow_left (Nat.mul_div_le L E) 2
    refine (seedDecider_eq_true_iff_of_advantage_lt hyes (fun hx => ?_) hG.length_eq gen seed
      (fun z => ?_) hmL (hG.fools _ _ hcirc)).symm
    · have h := hno hx
      have hsum := acceptCount_add_acceptCount_not V x (L / E)
      omega
    · simp only [gen, hG.length_eq, List.length_ofFn]
      rfl
  -- the running time: the decider is polynomial-time on instances padded to `2 ^ seed x`
  obtain ⟨D₀, hGO⟩ := hG.time
  set encP := encPair enc encUnary
  have hlog : ComputableInPolyTime (fun q : α × ℕ => Nat.log 2 q.2) encP encUnary :=
    ComputableInPolyTime.binary_log_two.comp
      (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd enc encUnary))
  have hT : Monotone fun j => (2 ^ j * (ℓ j + 1)) ^ D₀ := fun a b h =>
    Nat.pow_le_pow_left (Nat.mul_le_mul (Nat.pow_le_pow_right two_pos h)
      (Nat.add_le_add_right (hG.monotone h) 1)) D₀
  have hbound : PolyBounded (fun q : α × ℕ => (encP q).length)
      fun q => (2 ^ Nat.log 2 q.2 * (ℓ (Nat.log 2 q.2) + 1)) ^ D₀ := by
    growth_poly [hG.le_two_pow]
  have hGq : ComputableInPolyTime (fun q : (α × ℕ) × List Bool => G (q.2.take (Nat.log 2 q.1.2)))
      (encPair encP encBits) encBits :=
    ComputableInO.computableInPolyTime_take hT hGO hlog hbound
  have hgen : ComputableInPolyTime (fun q : (α × ℕ) × List Bool =>
      (G (q.2.take (Nat.log 2 q.1.2))).take ((G (q.2.take (Nat.log 2 q.1.2))).length / E))
      (encPair encP encBits) encBits :=
    ComputableInPolyTime.bitsTakeWithInput hGq
      ((ComputableInPolyTime.unary_div_const E).comp (ComputableInPolyTime.length_bits.comp hGq))
  have hV : ComputableInPolyTime V (encPair enc encBits) encBool :=
    hVO.computableInPolyTime PolyBounded.self PolyBounded.self
  have hseed : ComputableInPolyTime seed enc encUnary :=
    hk.comp (ComputableInPolyTime.encoding_length enc)
  obtain ⟨C, D, hO⟩ := exists_computableInO_seedDecider (gen := gen)
    (fun q z => (G (z.take (Nat.log 2 q.2))).take ((G (z.take (Nat.log 2 q.2))).length / E)) hV
    hgen (fun x z hz => by simp only [gen, Nat.log_pow Nat.one_lt_two, ← hz, List.take_length])
    hseed
  have hmem := setOf_mem_DTIME_of_computableInO hO
    (t := fun n => C * 2 ^ (D * k n) * (n + 1) ^ D) fun x => le_rfl
  refine ⟨D, ?_⟩
  rw [hAeq]
  exact DTIME_mono_of_le_mul_add (C := C) (fun n => by rw [mul_assoc]; omega) hmem

/-- **Not Goldreich's Proposition 8.15: a conditional result under a growth hypothesis and a
polynomial-time seed schedule.** [Goldreich, Proposition 8.15][Goldreich2007DraftR4] (draft r4,
printed page 339, PDF page 75) states: *let `G` be a canonical derandomizer of stretch `ℓ`; then
for every time-constructible `t`, `BPtime(t) ⊆ Dtime(T)` with `T(n) = poly(2 ^ ℓ⁻¹(t(n)) t(n))`*,
where `ℓ⁻¹(t(n))` is the least `k` with `ℓ(k) ≥ t(n)`. This theorem proves
`BPTIME(t) ⊆ ⋃ D, DTIME((2 ^ k(n) (t(n) + 1)) ^ D)` for every seed length `k` with
`t(n) ≤ ℓ(k(n))`, in particular `ℓ⁻¹ ∘ t`, under three hypotheses the source does not make:
* *growth*: for every `c` there is `d` with `c ℓ(j) ≤ ℓ(d (j + 1))` for all `j`, so that
  `ℓ⁻¹(c t) ≤ d (ℓ⁻¹(t) + 1)`; it holds for polynomial and `2 ^ (ε k)` stretch;
* `n ≤ t(n)`;
* the seed length `k` is computable from `n` in unary in polynomial time, in place of `t` being
  time-constructible.

They let longer seeds absorb the constant factors of `Cslib.Complexity.BPTIME`, which the printed
proof sketch fixes at one (`|C_x| ≤ |r| ^ 2`). Whether the proposition holds as printed under the
source's own conventions is open; the cited objective is tracked on #5452. -/
theorem BPTIME_subset_DTIME_of_canonicalDerandomizer_of_growth {G : List Bool → List Bool}
    {ℓ : ℕ → ℕ}
    (hG : CanonicalDerandomizer G ℓ) (hgrowth : ∀ c : ℕ, ∃ d : ℕ, ∀ j, c * ℓ j ≤ ℓ (d * (j + 1)))
    {t k : ℕ → ℕ} (ht : ∀ n, n ≤ t n) (hk : ComputableInPolyTime k encUnary encUnary)
    (hkt : ∀ n, t n ≤ ℓ (k n)) {α : Type} (enc : α ↪ List Bool) :
    BPTIME enc t ⊆ ⋃ D : ℕ, DTIME enc fun n => (2 ^ k n * (t n + 1)) ^ D := by
  intro A hA
  obtain ⟨c, hc⟩ := hG.exists_mem_DTIME_of_mem_BPTIME hA
  obtain ⟨d, hd⟩ := hgrowth (3 * c)
  -- a seed length `e` with `c ≤ ℓ e`, for the instances of length `0`
  have he : c ≤ ℓ (k c) := (ht c).trans (hkt c)
  set e := k c
  obtain ⟨D, hD⟩ := hc (fun n => d * (k n + 1) + e) (by fun_prop) fun n => by
    have h1 : 3 * c * ℓ (k n) ≤ ℓ (d * (k n + 1) + e) :=
      (hd (k n)).trans (hG.monotone (Nat.le_add_right _ _))
    have h2 : ℓ e ≤ ℓ (d * (k n + 1) + e) := hG.monotone (Nat.le_add_left _ _)
    have h3 := hkt n
    have h4 := ht n
    rcases Nat.eq_zero_or_pos (t n) with h0 | h0
    · have hn0 : n = 0 := by omega
      subst hn0
      rw [h0]
      omega
    · nlinarith [Nat.mul_le_mul_left c h3, Nat.mul_le_mul_left c h4, Nat.mul_le_mul_left c h0]
  refine Set.mem_iUnion.2 ⟨D * d + D,
    DTIME_mono_of_le_mul_add (C := 2 ^ (D * d + D * e)) (fun n => ?_) hD⟩
  set P := 2 ^ k n * (t n + 1)
  have hP1 : 2 ^ k n ≤ P := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hP2 : n + 1 ≤ P :=
    (Nat.succ_le_succ (ht n)).trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
  calc 2 ^ (D * (d * (k n + 1) + e)) * (n + 1) ^ D
      = 2 ^ (D * d + D * e) * ((2 ^ k n) ^ (D * d) * (n + 1) ^ D) := by
        rw [← pow_mul, mul_left_comm, ← mul_assoc, ← pow_add]
        ring_nf
    _ ≤ 2 ^ (D * d + D * e) * (P ^ (D * d) * P ^ D) :=
        by gcongr
    _ = 2 ^ (D * d + D * e) * P ^ (D * d + D) := by rw [pow_add P]
    _ ≤ _ := Nat.le_add_right _ _

/-- **Not Arora and Barak's Lemma 16.4: a conditional result under a growth hypothesis.**
[Arora and Barak, Lemma 16.4][AroraBarak07] (draft of 2007-01-08, printed page 284, PDF page 300)
states: *if there exists an `S(ℓ)`-pseudorandom generator, then for every polynomial-time
computable `ℓ : ℕ → ℕ`, `BPTIME(S(ℓ(n))) ⊆ DTIME(2 ^ (c ℓ(n)))` for some constant `c`*. This
theorem proves `BPTIME(S(ℓ(n))) ⊆ ⋃ c, DTIME(2 ^ (c ℓ(n)))`, for every encoding of instances,
under two hypotheses the source does not make:
* *growth*, `S(O(ℓ)) ≥ c S(ℓ)`: for every `c` there is `d` with `c S(m) ≤ S(d (m + 1))` for all
  `m`; it holds for polynomial, `2 ^ (ℓ ^ ε)` and `2 ^ (ε ℓ)` stretch, and is implied by
  `S(ℓ + O(1)) ≥ c S(ℓ)`, which fails for polynomial `S`;
* `n ≤ S(ℓ(n))`.

They let longer seeds absorb the constant factors of `Cslib.Complexity.BPTIME`: a machine of time
`c' S(ℓ(n))` may toss more coins than the generator outputs, which the printed proof does not
allow for. The constant `c` depends on the problem. The seed schedule `ℓ` is computed from `n` in
unary to unary, so `ℓ(n) ≤ poly(n)`. Whether the lemma holds as printed under the source's own
conventions is open; the cited objective is tracked on #5452. -/
theorem BPTIME_subset_DTIME_of_exponentialTimePRG_of_growth {G : List Bool → List Bool} {S : ℕ → ℕ}
    (hG : ExponentialTimePRG G S) (hgrowth : ∀ c : ℕ, ∃ d : ℕ, ∀ m, c * S m ≤ S (d * (m + 1)))
    {ℓ : ℕ → ℕ} (hℓ : ComputableInPolyTime ℓ encUnary encUnary) (hS : ∀ n, n ≤ S (ℓ n))
    {α : Type} (enc : α ↪ List Bool) :
    BPTIME enc (fun n => S (ℓ n)) ⊆ ⋃ c : ℕ, DTIME enc fun n => 2 ^ (c * ℓ n) := by
  have hC := hG.canonicalDerandomizer
  refine (BPTIME_subset_DTIME_of_canonicalDerandomizer_of_growth hC hgrowth hS hℓ (fun _ => le_rfl)
    enc).trans (Set.iUnion_subset fun D => ?_)
  refine Set.subset_iUnion_of_subset (2 * D) (DTIME_mono_of_le_mul_add (C := 4 ^ D) fun n => ?_)
  have hS2 := hC.le_two_pow (ℓ n)
  have h2 : 2 ≤ 2 ^ (ℓ n + 1) := Nat.le_self_pow (Nat.succ_ne_zero _) 2
  have h4 : 2 ^ (ℓ n + 2) = 2 * 2 ^ (ℓ n + 1) := by ring
  calc (2 ^ ℓ n * (S (ℓ n) + 1)) ^ D ≤ (2 ^ ℓ n * 2 ^ (ℓ n + 2)) ^ D :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (by omega)) D
    _ = 4 ^ D * 2 ^ (2 * D * ℓ n) := by ring
    _ ≤ _ := Nat.le_add_right _ _

/-! ### Arora and Barak's Corollary 16.6 -/

/-- The polynomial `n ^ a + n + 1` is at most `3 (n + 1) ^ (a + 1)`. -/
private theorem pow_add_add_one_le (n a : ℕ) : n ^ a + n + 1 ≤ 3 * (n + 1) ^ (a + 1) := by
  have h1 : n ^ a ≤ (n + 1) ^ (a + 1) :=
    (Nat.pow_le_pow_left (Nat.le_succ n) a).trans (Nat.pow_le_pow_right (Nat.succ_pos n) (by omega))
  have h2 : n + 1 ≤ (n + 1) ^ (a + 1) := Nat.le_self_pow (Nat.succ_ne_zero a) _
  omega

/-- An output length of at least `2 ^ (ℓ ^ ε)` for all large `ℓ`, for a real `ε > 0`, is at least
`2 ^ X` on seeds of `X ^ e + M` bits, for naturals `e ≥ 1` and `M`. -/
private theorem exists_two_pow_le_of_rpow {S : ℕ → ℕ}
    (h : ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ m : ℕ in atTop, (2 : ℝ) ^ ((m : ℝ) ^ ε) ≤ S m) :
    ∃ e M : ℕ, 1 ≤ e ∧ ∀ X : ℕ, 2 ^ X ≤ S (X ^ e + M) := by
  obtain ⟨ε, hε, hev⟩ := h
  obtain ⟨M, hM⟩ := eventually_atTop.1 hev
  obtain ⟨e, he, heε⟩ := Real.exists_nat_pos_inv_lt hε
  have heε : 1 ≤ (e : ℝ) * ε := by
    rw [inv_lt_iff_one_lt_mul₀' (by exact_mod_cast he)] at heε
    exact heε.le
  refine ⟨e, M, he, fun X => ?_⟩
  set m := X ^ e + M
  have hm := hM m (Nat.le_add_left _ _)
  have hXm : (X : ℝ) ≤ (m : ℝ) ^ ε := by
    rcases Nat.eq_zero_or_pos X with rfl | hX
    · simpa using Real.rpow_nonneg (Nat.cast_nonneg m) ε
    have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
    calc (X : ℝ) = (X : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (X : ℝ) ^ ((e : ℝ) * ε) := Real.rpow_le_rpow_of_exponent_le hX1 heε
      _ = ((X : ℝ) ^ e) ^ ε := Real.rpow_natCast_mul (by positivity) e ε
      _ ≤ (m : ℝ) ^ ε := Real.rpow_le_rpow (by positivity)
          (by simp only [m]; push_cast; linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]) hε.le
  have : (2 : ℝ) ^ X ≤ S m := by
    calc (2 : ℝ) ^ X = (2 : ℝ) ^ (X : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (2 : ℝ) ^ ((m : ℝ) ^ ε) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hXm
      _ ≤ S m := hm
  exact_mod_cast this

/-- Eventually `Q (log₂ n + 1) ^ e ≤ (log₂ n) ^ (e + 1)`. -/
private theorem eventually_mul_log_succ_pow_le (Q e : ℕ) :
    ∀ᶠ n : ℕ in atTop, Q * (Nat.log 2 n + 1) ^ e ≤ Nat.log 2 n ^ (e + 1) := by
  filter_upwards [eventually_ge_atTop (2 ^ (Q * 2 ^ e + 1))] with n hn
  have hl : Q * 2 ^ e + 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le Nat.one_lt_two hn
  set l := Nat.log 2 n
  calc Q * (l + 1) ^ e ≤ Q * (2 * l) ^ e :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) e)
    _ = Q * 2 ^ e * l ^ e := by ring
    _ ≤ l * l ^ e := Nat.mul_le_mul_right _ (by omega)
    _ = l ^ (e + 1) := by ring

/-- **Arora and Barak, Corollary 16.6 (2)** [Arora and Barak, Corollary 16.6][AroraBarak07] (draft
of 2007-01-08, printed page 285, PDF page 301): *if there exists a `2 ^ (ℓ ^ ε)`-pseudorandom
generator for some constant `ε > 0`, then `BPP ⊆ QuasiP = DTIME(2 ^ polylog(n))`*, for every
encoding `enc` of instances. `QuasiP` is written as `⋃ c, DTIME(2 ^ (log₂ n) ^ c)`. The output
length `S(ℓ)` need only be at least `2 ^ (ℓ ^ ε)` for all large `ℓ`, which covers any rounding.

The draft derives the corollary from its Lemma 16.4 (Exercise 16.1). Here it follows from the
seed-length step `Cslib.Complexity.CanonicalDerandomizer.exists_mem_DTIME_of_mem_BPTIME`, with
seeds of polylogarithmic length `(b * (log₂ n + 1)) ^ e + M`, for an integer `e` with
`1 / e < ε`, which needs no growth condition on `S`: the time bound of a
`BPP` problem is a polynomial `n ^ a`, and the seeds are chosen with polynomial slack. -/
theorem BPP_subset_quasiPoly_of_exponentialTimePRG {G : List Bool → List Bool} {S : ℕ → ℕ}
    (hG : ExponentialTimePRG G S)
    (hS : ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ m : ℕ in atTop, (2 : ℝ) ^ ((m : ℝ) ^ ε) ≤ S m)
    {α : Type} (enc : α ↪ List Bool) :
    BPP enc ⊆ ⋃ c : ℕ, DTIME enc fun n => 2 ^ Nat.log 2 n ^ c := by
  intro A hA
  obtain ⟨a, hA⟩ := mem_BPP_iff_exists_mem_BPTIME.1 hA
  obtain ⟨c, hc⟩ := hG.canonicalDerandomizer.exists_mem_DTIME_of_mem_BPTIME hA
  obtain ⟨e, M, he, hM⟩ := exists_two_pow_le_of_rpow hS
  set b := a + 1 + 3 * c
  have hlog : ComputableInPolyTime (fun n => Nat.log 2 n) encUnary encUnary :=
    ComputableInPolyTime.binary_log_two.comp ComputableInPolyTime.unary_to_binary
  obtain ⟨D, hD⟩ := hc (fun n => (b * (Nat.log 2 n + 1)) ^ e + M) (by fun_prop) fun n => by
    -- `2 ^ (b (log₂ n + 1)) ≥ 2 ^ (3 c) (n + 1) ^ (a + 1) ≥ c (n ^ a + n + 1)`
    set L := Nat.log 2 n + 1
    have hn1 : n + 1 ≤ 2 ^ L := Nat.lt_pow_succ_log_self Nat.one_lt_two n
    have hpow : (n + 1) ^ (a + 1) ≤ 2 ^ (L * (a + 1)) := by
      rw [pow_mul]; exact Nat.pow_le_pow_left hn1 _
    have h3c : 3 * c ≤ 2 ^ (3 * c * L) :=
      Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right two_pos (Nat.le_mul_of_pos_right _
        (Nat.succ_pos _)))
    calc c * (n ^ a + n + 1) ≤ c * (3 * (n + 1) ^ (a + 1)) :=
          Nat.mul_le_mul_left _ (pow_add_add_one_le n a)
      _ = 3 * c * (n + 1) ^ (a + 1) := by ring
      _ ≤ 2 ^ (3 * c * L) * 2 ^ (L * (a + 1)) := Nat.mul_le_mul h3c hpow
      _ = 2 ^ (b * L) := by rw [← pow_add]; congr 1; simp only [b]; ring
      _ ≤ S ((b * L) ^ e + M) := hM _
  refine Set.mem_iUnion.2 ⟨e + 1, ?_⟩
  -- the time bound is eventually below `2 ^ (D M) 2 ^ (log₂ n) ^ (e + 1)`
  have hev : ∀ᶠ n in atTop, 2 ^ (D * ((b * (Nat.log 2 n + 1)) ^ e + M)) * (n + 1) ^ D ≤
      2 ^ (D * M) * 2 ^ Nat.log 2 n ^ (e + 1) := by
    filter_upwards [eventually_mul_log_succ_pow_le (D * b ^ e + D) e] with n hn
    set L := Nat.log 2 n + 1
    have hn1 : n + 1 ≤ 2 ^ L := Nat.lt_pow_succ_log_self Nat.one_lt_two n
    have hL : L ≤ L ^ e := Nat.le_self_pow (by omega) L
    calc 2 ^ (D * ((b * L) ^ e + M)) * (n + 1) ^ D
        ≤ 2 ^ (D * ((b * L) ^ e + M)) * 2 ^ (L * D) :=
          Nat.mul_le_mul_left _ (by rw [pow_mul]; exact Nat.pow_le_pow_left hn1 D)
      _ = 2 ^ (D * M) * 2 ^ (D * b ^ e * L ^ e + D * L) := by
          rw [← pow_add, ← pow_add, mul_pow]; ring_nf
      _ ≤ 2 ^ (D * M) * 2 ^ ((D * b ^ e + D) * L ^ e) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right two_pos (by nlinarith))
      _ ≤ 2 ^ (D * M) * 2 ^ Nat.log 2 n ^ (e + 1) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right two_pos hn)
  exact ((DTIME_mono_of_eventually_le hev).trans
    (DTIME_mono_of_le_mul_add (C := 2 ^ (D * M)) fun n => Nat.le_add_right _ _)) hD

/-- **Arora and Barak, Corollary 16.6 (3)** [Arora and Barak, Corollary 16.6][AroraBarak07] (draft
of 2007-01-08, printed page 285, PDF page 301): *if there exists an `S(ℓ)`-pseudorandom generator
for some super-polynomial `S` (`S(ℓ) = ℓ ^ ω(1)`), then
`BPP ⊆ SUBEXP = ⋂ ε > 0, DTIME(2 ^ (n ^ ε))`*, for every encoding `enc` of instances.
Super-polynomial means that for every `a`, `ℓ ^ a ≤ S(ℓ)` for all large `ℓ`; the bound
`2 ^ ⌈n ^ ε⌉` is `2 ^ (n ^ ε)` rounded up to a natural exponent.

The draft derives the corollary from its Lemma 16.4 (Exercise 16.1). Here it follows from the
seed-length step `Cslib.Complexity.CanonicalDerandomizer.exists_mem_DTIME_of_mem_BPTIME`, with
seeds of `⌊n ^ (1 / d)⌋ + K` bits, which needs no growth condition on `S`: the time bound of a
`BPP` problem is a polynomial, and the seeds are chosen with polynomial slack. -/
theorem BPP_subset_DTIME_two_pow_rpow_of_exponentialTimePRG {G : List Bool → List Bool}
    {S : ℕ → ℕ} (hG : ExponentialTimePRG G S) (hS : ∀ a : ℕ, ∀ᶠ m in atTop, m ^ a ≤ S m)
    {α : Type} (enc : α ↪ List Bool) :
    BPP enc ⊆ ⋂ (ε : ℝ) (_ : 0 < ε), DTIME enc fun n => 2 ^ ⌈(n : ℝ) ^ ε⌉₊ := by
  intro A hA
  obtain ⟨a, hA⟩ := mem_BPP_iff_exists_mem_BPTIME.1 hA
  obtain ⟨c, hc⟩ := hG.canonicalDerandomizer.exists_mem_DTIME_of_mem_BPTIME hA
  simp only [Set.mem_iInter]
  intro ε hε
  obtain ⟨d, r, hd, hr, hroot, hsub⟩ := exists_rootSeed_DTIME_subset hε
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 (hS (d * (a + 1) + 1))
  set K := K₀ + 3 * c + 1
  obtain ⟨D, hD⟩ := hc (fun n => r n + K) (by fun_prop) fun n => by
    -- `c (n ^ a + n + 1) ≤ k ^ (d (a + 1) + 1) ≤ S k` for the seed length `k`
    have hk := hK₀ (r n + K) (by omega)
    have h1 : n + 1 ≤ (r n + K) ^ d := (hroot n).trans (Nat.pow_le_pow_left (by omega) d)
    calc c * (n ^ a + n + 1) ≤ c * (3 * (n + 1) ^ (a + 1)) :=
          Nat.mul_le_mul_left _ (pow_add_add_one_le n a)
      _ = 3 * c * (n + 1) ^ (a + 1) := by ring
      _ ≤ (r n + K) * ((r n + K) ^ d) ^ (a + 1) :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left h1 _)
      _ = (r n + K) ^ (d * (a + 1) + 1) := by rw [← pow_mul, pow_succ, mul_comm]
      _ ≤ S (r n + K) := hk
  exact hsub enc 1 D K (DTIME_mono (fun n => by rw [one_mul]) hD)

end Cslib.Complexity
