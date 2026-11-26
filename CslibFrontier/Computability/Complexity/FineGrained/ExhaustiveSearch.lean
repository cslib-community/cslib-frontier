/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.PowerTime
import CslibFrontier.Computability.Complexity.FineGrained.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import Mathlib.Data.Nat.Size
import CslibFrontier.Tactic.EncLen

/-!
# Exhaustive-search reductions

Exponential, subexponential, and fixed-power time bounds transfer along reductions that branch over
$2^{\nu(a)}$ polynomial-time subinstances $f(a, r)$ (`r < 2 ^ ν a`), implemented by iterating a
polynomial-time step with a binary counter (`Turing.MultiTapeTM.ComputableInO.iterate`):
* `Cslib.Complexity.DecidableInExpTime.of_computableInPolyTime`: a set decided in polynomial time is
  decidable within exponential time with exponent `0`.
* `Cslib.Complexity.DecidableInExpTime.of_exhaustiveSearch`: if
  $a \in A \iff \exists r < 2^{\nu(a)}, f(a, r) \in B$, $\mu_B(f(a, r)) \le c \cdot \mu_A(a) + c$,
  and $\nu(a) \le \mu_A(a) / M + K$, then a decider for $B$ within time
  $2^{\delta \mu_B(b)} \cdot \mathrm{poly}(|b|)$ gives a decider for $A$ within time
  $2^{(1 / M + c \delta) \mu_A(a)} \cdot \mathrm{poly}(|a|)$.
* `Cslib.Complexity.DecidableInSubexpTime.of_exhaustiveSearch`: when $\nu(a) \le \mu_A(a) / M + K_M$
  for every $M \ge 1$, subexponential time for $B$ in $\mu_B$ gives subexponential time for $A$ in
  $\mu_A$.

## Main results

* `Cslib.Complexity.DecidableInExpTime.of_computableInPolyTime`: polynomial-time predicates have
  exponential-time exponent `0`.
* `Cslib.Complexity.DecidableInExpTime.of_exhaustiveSearch`,
  `Cslib.Complexity.DecidableInSubexpTime.of_exhaustiveSearch`: exponential and subexponential time
  transfer along exhaustive-search reductions.
* `Cslib.Complexity.DecidableInPowerExpTime.of_exhaustiveSearch`: combines the branch exponent
  power and the query power after parameter blowup.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 2.3][AroraBarak09]
* [R. Impagliazzo, R. Paturi, *On the complexity of k-SAT*][ImpagliazzoPaturi2001]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
  {A : Set α} {B : Set β} {μA : α → ℕ} {μB : β → ℕ}

/-- A set decided by a polynomial-time predicate is decidable within exponential time with exponent
`0` for any parameter `μ`. -/
theorem DecidableInExpTime.of_computableInPolyTime {μ : α → ℕ} {p : α → Bool}
    (hp : ComputableInPolyTime p encA encBool) (hA : ∀ a, a ∈ A ↔ p a = true) :
    DecidableInExpTime A encA μ 0 := by
  obtain ⟨d, _, hp'⟩ := hp.exists_degree
  exact DecidableInExpTime.of_computableInO hp'.inO hA 1 d fun _ => by simp

namespace ExhaustiveSearch

private abbrev State (α : Type) : Type := (α × ℕ) × Bool

private def encState (encA : α ↪ List Bool) : State α ↪ List Bool :=
  encPair (encPair encA encNat) encBool

private def init (a : α) : State α := ((a, 0), false)

private def step (f : α × ℕ → β) (g : β → Bool) (s : State α) : State α :=
  ((s.1.1, s.1.2 + 1), s.2 || g (f s.1))

private def rounds (ν : α → ℕ) (a : α) : ℕ := 2 ^ ν a

private def search (f : α × ℕ → β) (ν : α → ℕ) (g : β → Bool) (a : α) : Bool :=
  ((step f g)^[rounds ν a] (init a)).2

private theorem iterate_step_init (f : α × ℕ → β) (g : β → Bool) (a : α) (k : ℕ) :
    (step f g)^[k] (init a) =
      ((a, k), (List.range k).any fun r => g (f (a, r))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, step, List.range_succ, List.any_append,
      List.any_cons, List.any_nil, Bool.or_false]

private theorem search_eq_true_iff {f : α × ℕ → β} {ν : α → ℕ} {g : β → Bool}
    (hfA : ∀ a, a ∈ A ↔ ∃ r < 2 ^ ν a, f (a, r) ∈ B)
    (hg : ∀ b, g b = true ↔ b ∈ B) (a : α) :
    search f ν g a = true ↔ a ∈ A := by
  rw [search, iterate_step_init, List.any_eq_true, hfA]
  simp only [List.mem_range, hg, rounds]

open ComputableInPolyTime in
private theorem computableInPolyTime_init :
    ComputableInPolyTime init encA (encState encA) := by
  unfold init encState
  fun_prop

open ComputableInPolyTime in
private theorem computableInPolyTime_rounds {ν : α → ℕ}
    (hν : ComputableInPolyTime ν encA encUnary) :
    ComputableInPolyTime (rounds ν) encA encNat :=
  binary_two_pow.comp hν

open ComputableInPolyTime in
private theorem exists_computableInO_step {f : α × ℕ → β}
    (hf : ComputableInPolyTime f (encPair encA encNat) encB)
    {g : β → Bool} {t : β → ℕ}
    (hg : ComputableInO g encB encBool t t) :
    ∃ d, ComputableInO (step f g) (encState encA) (encState encA)
      (fun s => ((encState encA s).length + 1) ^ d + t (f s.1))
      (fun s => ((encState encA s).length + 1) ^ d + t (f s.1)) := by
  obtain ⟨dN, eN, hN⟩ := (show ComputableInPolyTime (fun s : State α => (s.1.1, s.1.2 + 1))
    (encState encA) (encPair encA encNat) by unfold encState; fun_prop).exists_degree
  obtain ⟨dB, eB, hB⟩ := (show ComputableInPolyTime (fun s : State α => s.2)
    (encState encA) encBool by unfold encState; fun_prop).exists_degree
  obtain ⟨dR, eR, hR⟩ := (hf.comp (show ComputableInPolyTime (fun s : State α => s.1)
    (encState encA) (encPair encA encNat) by unfold encState; fun_prop)).exists_degree
  obtain ⟨dO, eO, hO⟩ := bool_or.exists_degree
  set D := dN + dB + dR
  have h := (hN.mono (d' := D) (e' := eN) (by omega) le_rfl).inO.prod
    (hO.inO.comp ((hB.mono (d' := D) (e' := eB) (by omega) le_rfl).inO.prod
      (hg.comp (hR.mono (d' := D) (e' := eR) (by omega) le_rfl).inO)))
  refine ⟨D, (h.mono (5 ^ dO + 4) (fun s => ?_) (fun s => ?_)).of_enc_eq fun _ => rfl⟩ <;>
  · simp only [Function.comp_apply,
      show ∀ p : Bool × Bool, (encPair encBool encBool p).length = 4 from fun _ => by simp]
    have hF : 1 ≤ (4 + 1) ^ dO := Nat.one_le_pow _ _ (by norm_num)
    generalize ((encState encA s).length + 1) ^ D = P, t (f s.1) = T, (4 + 1) ^ dO = F at hF ⊢
    nlinarith

/-- **Length bounds for the search.** The states visited by the search and the binary round counter
have length at most `st a`, and every subinstance `f (a, k)` it queries has length at most `nd a`;
both bounds are polynomial in the length of the encoded instance. -/
private theorem exists_search_length_bounds {f : α × ℕ → β} {ν : α → ℕ}
    (hf : ComputableInPolyTime f (encPair encA encNat) encB)
    (hν : ComputableInPolyTime ν encA encUnary) :
    ∃ st nd : α → ℕ,
      PolyBounded (fun a => (encA a).length) st ∧ PolyBounded (fun a => (encA a).length) nd ∧
      (∀ (g : β → Bool) (a : α) (k : ℕ), k ≤ rounds ν a →
        (encState encA ((step f g)^[k] (init a))).length ≤ st a) ∧
      (∀ a, (encNat (rounds ν a)).length ≤ st a) ∧
      (∀ a k, k ≤ rounds ν a → (encB (f (a, k))).length ≤ nd a) := by
  -- `rounds ν a = 2 ^ ν a` has `ν a + 1` binary digits, which bounds every round counter.
  have hpair (a : α) {k : ℕ} (hk : k ≤ rounds ν a) :
      (encPair encA encNat (a, k)).length ≤ 2 * (encA a).length + ν a + 2 := by
    have : (encNat k).length ≤ ν a + 1 :=
      (length_encNat_mono hk).trans_eq (length_encNat_two_pow (ν a))
    enc_len
  obtain ⟨cf, df, hf_len⟩ := hf.polyBounded_length.exists_le
  refine ⟨fun a => 2 * (2 * (encA a).length + ν a + 2) + 2,
    fun a => cf * (2 * (encA a).length + ν a + 2 + 1) ^ df, by growth_poly, by growth_poly,
    fun g a k hk => ?_, fun a => by simp only [rounds, length_encNat_two_pow]; omega,
    fun a k hk => (hf_len (a, k)).trans
      (Nat.mul_le_mul_left cf (Nat.pow_le_pow_left (by have := hpair a hk; omega) df))⟩
  have := hpair a hk
  rw [iterate_step_init, encState, length_encPair]
  simp only [encBool_apply, List.length_singleton]; omega

/-- Time bound for a leaf, with a common query exponent and length bound for each search input. -/
private noncomputable def leafTime (nd : α → ℕ) (queryExponent : α → ℝ) (k e : ℕ)
    (a : α) : ℕ :=
  ⌈(k : ℝ) * (2 ^ queryExponent a * ((nd a : ℝ) + 1) ^ e) + k⌉₊

private theorem le_leafTime {nd : α → ℕ} {queryExponent : α → ℝ} {k e : ℕ}
    {t : β → ℕ} {rate : β → ℝ} {a : α} {b : β}
    (ht : (t b : ℝ) ≤ k * (2 ^ rate b * ((encB b).length + 1) ^ e) + k)
    (hRate : rate b ≤ queryExponent a) (hlen : (encB b).length ≤ nd a) :
    t b ≤ leafTime nd queryExponent k e a := by
  have h₁ : (2 : ℝ) ^ rate b ≤ 2 ^ queryExponent a :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hRate
  have h₂ : (((encB b).length : ℝ) + 1) ^ e ≤ ((nd a : ℝ) + 1) ^ e := by gcongr
  exact Nat.cast_le.mp (ht.trans ((by gcongr : _ ≤ _).trans (Nat.le_ceil _)))

/-- **Absorbing the overheads.** A running time `A + R * (B + ℓ)`, with polynomial overheads
`A, B ≤ a * P`, `R ≤ r * X` rounds and leaves within `ℓ ≤ b * Y * P + b'`, is within a constant
times `X * Y * P` when `X, Y, P ≥ 1`. -/
private theorem add_mul_add_le {A B R ℓ X Y P a r b b' : ℝ} (hA : A ≤ a * P) (hB : B ≤ a * P)
    (hR : R ≤ r * X) (hℓ : ℓ ≤ b * Y * P + b') (hR₀ : 0 ≤ R) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hb' : 0 ≤ b') (hX : 1 ≤ X) (hY : 1 ≤ Y) (hP : 1 ≤ P) :
    A + R * (B + ℓ) ≤ (a + r * (a + b + b')) * (X * Y * P) := by
  have hP₀ : 0 ≤ P := zero_le_one.trans hP
  -- Each round costs at most `(a + b + b') * (Y * P)`.
  have hBℓ : B + ℓ ≤ (a + b + b') * (Y * P) := by
    have := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hP₀ hY) ha
    have := le_mul_of_one_le_right hb' (one_le_mul_of_one_le_of_one_le hY hP)
    linarith
  have := (mul_le_mul_of_nonneg_left hBℓ hR₀).trans (mul_le_mul_of_nonneg_right hR (by positivity))
  have := mul_le_mul_of_nonneg_left
    (le_mul_of_one_le_left hP₀ (one_le_mul_of_one_le_of_one_le hX hY)) ha
  linarith

/-- Certify the search once for arbitrary bounds on the branch and leaf exponents. -/
private theorem exists_decidableInTimeO {f : α × ℕ → β} {ν : α → ℕ}
    (hf : ComputableInPolyTime f (encPair encA encNat) encB)
    (hν : ComputableInPolyTime ν encA encUnary)
    (hfA : ∀ a, a ∈ A ↔ ∃ r < 2 ^ ν a, f (a, r) ∈ B)
    {rate : β → ℝ} {branchExponent queryExponent : α → ℝ} {e : ℕ}
    (hbranch : ∀ a, (ν a : ℝ) ≤ branchExponent a)
    (hquery : ∀ a r, rate (f (a, r)) ≤ queryExponent a)
    (hquery₀ : ∀ a, 0 ≤ queryExponent a)
    (h : DecidableInTimeO B encB
      fun b => (2 : ℝ) ^ rate b * ((encB b).length + 1) ^ e) :
    ∃ E : ℕ, DecidableInTimeO A encA
      fun a => (2 : ℝ) ^ (branchExponent a + queryExponent a) * ((encA a).length + 1) ^ E := by
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨0, DecidableInTimeO.of_computableInO (.const false)
      (fun a => hα.elim a) (fun a => hα.elim a)⟩
  have := Classical.inhabited_of_nonempty hα
  -- The machine counts `rounds ν a = 2 ^ ν a` rounds in binary; round `r` queries the decider `g`
  -- for `B` on `f (a, r)`, and the accumulated answer is read off at the end.
  obtain ⟨g, t, k, hg, hgB, ht⟩ := h.exists_computableInO
  obtain ⟨d, hstep⟩ := exists_computableInO_step hf hg
  obtain ⟨dn, _, hn⟩ := (computableInPolyTime_rounds hν).exists_degree
  obtain ⟨di, _, hi⟩ := (computableInPolyTime_init (encA := encA)).exists_degree
  obtain ⟨da, _, ha⟩ := (show ComputableInPolyTime (fun s : State α => s.2)
    (encState encA) encBool by unfold encState; fun_prop).exists_degree
  obtain ⟨st, nd, hst, hnd, hstate, hrounds_len, hnd_bound⟩ := exists_search_length_bounds hf hν
  have hround (a : α) (j : ℕ) (hj : j ≤ rounds ν a) :
      ((encState encA ((step f g)^[j] (init a))).length + 1) ^ d +
        t (f ((step f g)^[j] (init a)).1) ≤ (st a + 1) ^ d + leafTime nd queryExponent k e a :=
    Nat.add_le_add (Nat.pow_le_pow_left (Nat.add_le_add_right (hstate g a j hj) 1) d) (by
      rw [iterate_step_init]
      exact le_leafTime (rate := rate) (ht _) (hquery a j) (hnd_bound a j hj))
  have hsearch := ha.inO.comp
    (ComputableInO.iterate hn.inO hi.inO hstep hround hround (hstate g))
  -- Apart from the number of rounds and the leaves, the running time is polynomial.
  have hpoly : PolyBounded (fun a => (encA a).length) fun a =>
      ((encA a).length + 1) ^ dn + ((encA a).length + 1) ^ di + (st a + 1) ^ da +
        ((st a + 1) ^ d + st a + (st a + 1) ^ 2) + (nd a + 1) ^ e := by
    growth_poly
  obtain ⟨Cp, E, hCp⟩ := hpoly.exists_le
  let C : ℕ := ⌈(Cp + 2 * (Cp + k * Cp + (k + 1)) : ℝ)⌉₊
  refine ⟨E, (DecidableInTimeO.of_computableInO hsearch
    (fun a => (search_eq_true_iff hfA (fun b => (hgB b).symm) a).symm)
    (T := fun a => (C : ℝ) *
      (2 ^ (branchExponent a + queryExponent a) * ((encA a).length + 1) ^ E))
    fun a => ?_).mono C (fun _ => le_add_of_nonneg_right (Nat.cast_nonneg C))
      (fun _ => by positivity)⟩
  -- The polynomial overheads, the number of rounds and the leaves, bounded separately.
  have hP := hCp a
  have hbr₁ : (1 : ℝ) ≤ 2 ^ branchExponent a :=
    Real.one_le_rpow (by norm_num) ((Nat.cast_nonneg _).trans (hbranch a))
  have hA : (((encA a).length : ℝ) + 1) ^ dn + ((encA a).length + 1) ^ di +
      ((encState encA ((step f g)^[rounds ν a] (init a))).length + 1) ^ da ≤
      Cp * ((encA a).length + 1) ^ E := by
    have := Nat.pow_le_pow_left (Nat.add_le_add_right (hstate g a (rounds ν a) le_rfl) 1) da
    norm_cast; omega
  have hB : ((st a : ℝ) + 1) ^ d + st a + ((encNat (rounds ν a)).length + 1) ^ 2 ≤
      Cp * ((encA a).length + 1) ^ E := by
    have := Nat.pow_le_pow_left (Nat.add_le_add_right (hrounds_len a) 1) 2
    norm_cast; omega
  have hR : (rounds ν a : ℝ) + 1 ≤ 2 * (2 : ℝ) ^ branchExponent a := by
    have h₁ : (rounds ν a : ℝ) ≤ 2 ^ branchExponent a := by
      rw [rounds, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (hbranch a)
    linarith
  have hleaf : (leafTime nd queryExponent k e a : ℝ) ≤
      k * Cp * 2 ^ queryExponent a * ((encA a).length + 1) ^ E + (k + 1) := by
    have hnd : ((nd a : ℝ) + 1) ^ e ≤ Cp * ((encA a).length + 1) ^ E := by norm_cast; omega
    have hceil := Nat.ceil_lt_add_one (show (0 : ℝ) ≤
      k * (2 ^ queryExponent a * ((nd a : ℝ) + 1) ^ e) + k by positivity)
    have := mul_le_mul_of_nonneg_left hnd
      (by positivity : (0 : ℝ) ≤ k * 2 ^ queryExponent a)
    unfold leafTime
    linarith
  have key := add_mul_add_le hA hB hR hleaf (by positivity) (by positivity) (by positivity)
    (by positivity) hbr₁ (Real.one_le_rpow (by norm_num) (hquery₀ a))
    (one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg _)))
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  push_cast
  refine (?_ : _ ≤ _).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity))
  linarith

end ExhaustiveSearch

/-- **Exponential-time transfer along an exhaustive search.** If
$f : \alpha \times \mathbb{N} \to \beta$ and $\nu : \alpha \to \mathbb{N}$ are computable in
polynomial time (with $\nu$ in unary), $a \in A \iff \exists r < 2^{\nu(a)},\, f(a, r) \in B$,
$\mu_B(f(a, r)) \le c \cdot \mu_A(a) + c$, and $\nu(a) \le \mu_A(a) / M + K$, then a decider for $B$
within time $2^{\delta \mu_B(b)} \cdot \mathrm{poly}(|b|)$ yields a decider for $A$ within time
$2^{(1 / M + c \delta) \mu_A(a)} \cdot \mathrm{poly}(|a|)$. -/
theorem DecidableInExpTime.of_exhaustiveSearch {f : α × ℕ → β} {ν : α → ℕ}
    (hf : ComputableInPolyTime f (encPair encA encNat) encB)
    (hν : ComputableInPolyTime ν encA encUnary)
    (hfA : ∀ a, a ∈ A ↔ ∃ r < 2 ^ ν a, f (a, r) ∈ B) {c : ℕ}
    (hμ : ∀ a r, μB (f (a, r)) ≤ c * μA a + c) {M K : ℕ}
    (hνM : ∀ a, ν a ≤ μA a / M + K) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : DecidableInExpTime B encB μB δ) :
    DecidableInExpTime A encA μA (1 / M + c * δ) := by
  obtain ⟨e, h⟩ := h
  have hbranch (a : α) : (ν a : ℝ) ≤ (1 / M : ℝ) * μA a + K := by
    rw [one_div_mul_eq_div]
    exact (mod_cast hνM a : (ν a : ℝ) ≤ ↑(μA a / M) + K).trans (add_le_add Nat.cast_div_le le_rfl)
  have hquery (a : α) (r : ℕ) : δ * μB (f (a, r)) ≤ c * δ * μA a + c * δ := by
    have hbound : (μB (f (a, r)) : ℝ) ≤ c * μA a + c := by exact_mod_cast hμ a r
    calc
      δ * μB (f (a, r)) ≤ δ * (c * μA a + c) :=
        mul_le_mul_of_nonneg_left hbound hδ
      _ = c * δ * μA a + c * δ := by ring
  obtain ⟨E, hsearch⟩ := ExhaustiveSearch.exists_decidableInTimeO hf hν hfA hbranch hquery
    (fun a => add_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg c) hδ)
      (Nat.cast_nonneg (μA a))) (mul_nonneg (Nat.cast_nonneg c) hδ)) h
  refine ⟨E, hsearch.mono ⌈(2 : ℝ) ^ (K + c * δ)⌉₊ (fun a => ?_) (fun _ => by positivity)⟩
  have hsum : (1 / M : ℝ) * μA a + K + (c * δ * μA a + c * δ) =
      (1 / M + c * δ) * μA a + (K + c * δ) := by ring
  rw [hsum, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    mul_comm ((2 : ℝ) ^ ((1 / M + c * δ) * μA a)), mul_assoc]
  exact (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)).trans
    (le_add_of_nonneg_right (by positivity))

/-- Exhaustive search with a branch exponent of power `q` and query parameter blowup of power
`b` transfers a power-`p` decider to a power-`max q (b * p)` decider. Query generation and
computing the number of branch bits take polynomial time. The binary search counters and all
encoded queries have length polynomial in the encoded input length. -/
theorem DecidableInPowerExpTime.of_exhaustiveSearch {f : α × ℕ → β} {ν : α → ℕ}
    (hf : ComputableInPolyTime f (encPair encA encNat) encB)
    (hν : ComputableInPolyTime ν encA encUnary)
    (hfA : ∀ a, a ∈ A ↔ ∃ r < 2 ^ ν a, f (a, r) ∈ B) {C K : ℕ} {q b p : ℝ}
    (hbranch : ∀ a, (ν a : ℝ) ≤ C * (μA a + 1 : ℝ) ^ q)
    (hsize : ∀ a r, (μB (f (a, r)) + 1 : ℝ) ≤ (K + 1 : ℝ) * (μA a + 1 : ℝ) ^ b)
    (hp : 0 ≤ p) (h : DecidableInPowerExpTime B encB μB p) :
    DecidableInPowerExpTime A encA μA (max q (b * p)) := by
  obtain ⟨D, e, h⟩ := h
  let R : ℝ := D * (K + 1 : ℝ) ^ p
  have hquery (a : α) (r : ℕ) : D * (μB (f (a, r)) + 1 : ℝ) ^ p ≤
      R * (μA a + 1 : ℝ) ^ (b * p) := by
    have h := Real.rpow_le_rpow (by positivity) (hsize a r) hp
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity)] at h
    simpa only [R, mul_assoc] using mul_le_mul_of_nonneg_left h (Nat.cast_nonneg D)
  have hR : 0 ≤ R := by unfold R; positivity
  obtain ⟨E, hsearch⟩ := ExhaustiveSearch.exists_decidableInTimeO hf hν hfA hbranch hquery
    (fun _ => mul_nonneg hR (by positivity)) h
  refine ⟨C + ⌈R⌉₊, E, hsearch.mono 1 (fun a => ?_) (fun _ => by positivity)⟩
  have hx : 1 ≤ (μA a + 1 : ℝ) := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hq := Real.rpow_le_rpow_of_exponent_le hx (le_max_left q (b * p))
  have hp' := Real.rpow_le_rpow_of_exponent_le hx (le_max_right q (b * p))
  have hexponent : C * (μA a + 1 : ℝ) ^ q + R * (μA a + 1 : ℝ) ^ (b * p) ≤
      ((C + ⌈R⌉₊ : ℕ) : ℝ) * (μA a + 1 : ℝ) ^ max q (b * p) := by
    push_cast
    calc
      _ ≤ (C : ℝ) * (μA a + 1 : ℝ) ^ max q (b * p) +
          R * (μA a + 1 : ℝ) ^ max q (b * p) :=
        add_le_add (mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg C))
          (mul_le_mul_of_nonneg_left hp' hR)
      _ ≤ _ := by
        rw [← add_mul]
        exact mul_le_mul_of_nonneg_right (add_le_add le_rfl (Nat.le_ceil R)) (by positivity)
  have hbound := mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexponent)
    (show 0 ≤ ((encA a).length + 1 : ℝ) ^ E by positivity)
  simp only [Nat.cast_one, one_mul]
  exact hbound.trans (le_add_of_nonneg_right zero_le_one)

/-- **Subexponential-time transfer along an exhaustive search with sublinear branch exponent.** If
$f : \alpha \times \mathbb{N} \to \beta$ and $\nu : \alpha \to \mathbb{N}$ are computable in
polynomial time (with $\nu$ in unary), $a \in A \iff \exists r < 2^{\nu(a)},\, f(a, r) \in B$,
$\mu_B(f(a, r)) \le c \cdot \mu_A(a) + c$, and for every $M \ge 1$ there is a constant $K$ with
$\nu(a) \le \mu_A(a) / M + K$, then subexponential time for $B$ in $\mu_B$ gives subexponential time
for $A$ in $\mu_A$. -/
theorem DecidableInSubexpTime.of_exhaustiveSearch {f : α × ℕ → β} {ν : α → ℕ}
    (hf : ComputableInPolyTime f (encPair encA encNat) encB)
    (hν : ComputableInPolyTime ν encA encUnary)
    (hfA : ∀ a, a ∈ A ↔ ∃ r < 2 ^ ν a, f (a, r) ∈ B) {c : ℕ}
    (hμ : ∀ a r, μB (f (a, r)) ≤ c * μA a + c)
    (hνM : ∀ M > 0, ∃ K, ∀ a, ν a ≤ μA a / M + K)
    (h : DecidableInSubexpTime B encB μB) :
    DecidableInSubexpTime A encA μA := by
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / ε)
  have hMpos : (0 : ℝ) < M := lt_trans (by positivity) hM
  obtain ⟨K, hK⟩ := hνM M (Nat.cast_pos.mp hMpos)
  have hMε : 1 / (M : ℝ) < ε / 2 :=
    (one_div_lt hMpos (half_pos hε)).mpr (by simpa only [one_div_div] using hM)
  set δ : ℝ := ε / (2 * (c + 1))
  have hδ : 0 < δ := by positivity
  refine ((h δ hδ).of_exhaustiveSearch hf hν hfA hμ hK hδ.le).mono ?_
  have : (c : ℝ) * δ ≤ ε / 2 := by
    simpa only [δ, div_div] using natCast_mul_div_add_one_le (half_pos hε).le c
  linarith

end Cslib.Complexity
