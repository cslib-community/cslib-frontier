/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Price.Basic
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.Identity
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.Estimates
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Prices.Cross
import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Hubs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The crossing inequality

Proposition B.3 of *VP ≠ VNP over every field* [AnthropicVPVNP2026]. Let
`x, v, y, u, o, o', w, w'` be points of a price `d` and `p, q ≥ 0`. There are `r, l ≥ 0` with
`r² + l² ≤ 2 (p² + q²)` such that `p d(x, v) + q d(y, u)` is at most each of
`p d(x, o) + q d(y, o) + p d(v, o') + q d(u, o') + r d(o, o')` and
`p d(x, w) + q d(u, w) + q d(y, w') + p d(v, w') + l d(w, w')` (`isPrice_crossing`). Adding the two
gives display (B.2) of the paper, the inequality (Q) of `CrossingLength`, for every `τ > 0`
(`isPrice_crossing_two_mul_le`).

The proof follows the paper. For a spectral point, the product of the two crossing wires is covered
by the tensors `Ψ_N` of Proposition B.2 (`exists_crossing_identity`); routing `Ψ_N` through two
hubs (Lemma A.3, `push_le_prod_wire_hubs`) bounds it in two ways, and the classes of states of
Lemma B.1 (`exists_log_stateCount_asymptotic`) give the sizes. A price is a limit of multiples of
wire exponents, and the pairs `(r, l)` lie in a compact set (`Separation.Prices.exists_quarter`).

## Main results

* `isPrice_crossing`, `isPrice_crossing_two_mul_le`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition B.3 and display (B.2) of the paper (§B.4); module `Paper.Crossing` (`prop_crossing`,
  `eq_Q`)
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Curvature

open Finset Filter Cslib.PartyTensor Cslib.Circuits.Arithmetic.Separation.Prices

variable {K : Type} [Field K]

section Hubs

variable {I : Type} [Fintype I] [DecidableEq I] (F : SpectralPoint K I)

/-- Lemma A.3, read for a spectral point `F`: a tensor that is a sum of `r` products of a tensor on
the legs in `S` and one on the other legs has value at most the product of the values of the wires
to the hubs `o₁, o₂` and of the wire of dimension `r` between them. -/
private theorem prop_crossing_cut {A : Type} [Fintype A] [DecidableEq A] (π : A → I)
    (t : PartyTensor K A)
    (S : A → Prop)
    [DecidablePred S] {r : ℕ} (g h : Fin r → (∀ a, t.Index a) → K)
    (hg : ∀ j x x', (∀ a, S a → x a = x' a) → g j x = g j x')
    (hh : ∀ j x x', (∀ a, ¬ S a → x a = x' a) → h j x = h j x')
    (hs : ∀ x, t.entry x = ∑ j, g j x * h j x) (o₁ o₂ : I) :
    F (push π t) ≤
        (∏ a, (Fintype.card (t.Index a) : ℝ) ^ F.wireExponent (π a) (if S a then o₁ else o₂)) *
      (r : ℝ) ^ F.wireExponent o₁ o₂ := by
  refine (F.monotone (push_le_prod_wire_hubs π t S g h hg hh hs o₁ o₂)).trans ?_
  rw [F.map_mul, F.map_prod]
  exact mul_le_mul (Finset.prod_le_prod₀ (fun _ _ => F.nonneg _) fun a _ => F.apply_wire_le _ _ _)
      (F.apply_wire_le _ _ _)
    (F.nonneg _) (Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

variable {α β : Type} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype β] [DecidableEq β]
  [Nonempty β]

/-- Proof of Proposition B.3: Lemma A.3 with the hubs `o, o'` for part (c) of Proposition B.2 bounds
`F(Ψ_N)`. The four legs are at `x, y, v, u`, and `f` is a sum of `R` products of a function of the
indices at `x, y` and one of those at `v, u`. -/
private theorem prop_crossing_hubs_c {f : α → β → α → β → K} {R : ℕ} (h : SplitAB f R)
    (x y v u o o' : I) :
    F (push ![x, y, v, u] (four f)) ≤
      (Fintype.card α : ℝ) ^ (F.wireExponent x o + F.wireExponent v o') * (Fintype.card β : ℝ) ^
          (F.wireExponent y o + F.wireExponent u o') *
        (R : ℝ) ^ F.wireExponent o o' := by
  obtain ⟨g, w, hf⟩ := h
  refine (prop_crossing_cut F ![x, y, v, u] (four f) (fun a => a = 0 ∨ a = 1)
    (fun t z => g t (z 0, z 1)) (fun t z => w t (z 2, z 3))
    (fun _ _ _ hz => by simp only [hz 0 (Or.inl rfl), hz 1 (Or.inr rfl)])
    (fun _ _ _ hz => by simp only [hz 2 (by decide), hz 3 (by decide)])
    (fun z => hf (z 0) (z 1) (z 2) (z 3)) o o').trans
    (mul_le_mul_of_nonneg_right (le_of_eq ?_) (by positivity))
  rw [Fin.prod_univ_four, Real.rpow_add (Nat.cast_pos.2 Fintype.card_pos),
    Real.rpow_add (Nat.cast_pos.2 Fintype.card_pos)]
  change (Fintype.card α : ℝ) ^ F.wireExponent x o * (Fintype.card β : ℝ) ^ F.wireExponent y o *
    (Fintype.card α : ℝ) ^ F.wireExponent v o' * (Fintype.card β : ℝ) ^ F.wireExponent u o' = _
  ring

/-- Proof of Proposition B.3: Lemma A.3 with the hubs `w, w'` for part (b) of Proposition B.2 bounds
`F(Ψ_N)`. Here `f` is a sum of `L` products of a function of the indices at `x, u` and one of those
at `y, v`. -/
private theorem prop_crossing_hubs_b {f : α → β → α → β → K} {L : ℕ} (h : SplitAD f L)
    (x y v u w w' : I) :
    F (push ![x, y, v, u] (four f)) ≤
      (Fintype.card α : ℝ) ^ (F.wireExponent x w + F.wireExponent v w') * (Fintype.card β : ℝ) ^
          (F.wireExponent u w + F.wireExponent y w') *
        (L : ℝ) ^ F.wireExponent w w' := by
  obtain ⟨g, m, hf⟩ := h
  refine (prop_crossing_cut F ![x, y, v, u] (four f) (fun a => a = 0 ∨ a = 3)
    (fun t z => g t (z 0, z 3)) (fun t z => m t (z 1, z 2))
    (fun _ _ _ hz => by simp only [hz 0 (Or.inl rfl), hz 3 (Or.inr rfl)])
    (fun _ _ _ hz => by simp only [hz 1 (by decide), hz 2 (by decide)])
    (fun z => hf (z 0) (z 1) (z 2) (z 3)) w w').trans
    (mul_le_mul_of_nonneg_right (le_of_eq ?_) (by positivity))
  rw [Fin.prod_univ_four, Real.rpow_add (Nat.cast_pos.2 Fintype.card_pos),
    Real.rpow_add (Nat.cast_pos.2 Fintype.card_pos)]
  change (Fintype.card α : ℝ) ^ F.wireExponent x w * (Fintype.card β : ℝ) ^ F.wireExponent y w' *
    (Fintype.card α : ℝ) ^ F.wireExponent v w' * (Fintype.card β : ℝ) ^ F.wireExponent u w = _
  ring

/-- Proof of Proposition B.3: the product of the two wires is covered by the `Θ + 1` tensors `Ψ_N`
of Proposition B.2 (a), and `F` is subadditive. The left side is the value of `F` at the two wires,
of dimensions `|α|` and `|β|`. -/
private theorem prop_crossing_cover {J : Type} [Fintype J] (Ψ : J → α → β → α → β → K)
    (hΨ : ∀ a b c d, ∑ j, Ψ j a b c d = if a = c ∧ b = d then 1 else 0) (x y v u : I) :
    (Fintype.card α : ℝ) ^ F.wireExponent x v * (Fintype.card β : ℝ) ^ F.wireExponent y u ≤
      ∑ j, F (push ![x, y, v, u] (four (Ψ j))) :=
  (rpow_mul_rpow_le_apply_four (K := K) (α := α) (β := β) F x y v u).trans <|
    F.le_sum _ _ <| (CoveredBy.withEntry
      (four fun (a : α) (b : β) c d => if a = c ∧ b = d then (1 : K) else 0)
      (fun j z => Ψ j (z 0) (z 1) (z 2) (z 3)) fun z => (hΨ (z 0) (z 1) (z 2) (z 3)).symm).push
      ![x, y, v, u]

/-- Proof of Proposition B.3: some `F(Ψ_N)` is at least the value of the two wires divided by the
number `Θ + 1` of the tensors (before logarithms, the paper's `ln F(Ψ_N) ≥ (p|xv| + q|yu| - o(1))
κ √n₀`). -/
private theorem prop_crossing_some {J : Type} [Fintype J] (Ψ : J → α → β → α → β → K)
    (hΨ : ∀ a b c d, ∑ j, Ψ j a b c d = if a = c ∧ b = d then 1 else 0) (x y v u : I) :
    ∃ j, (Fintype.card α : ℝ) ^ F.wireExponent x v * (Fintype.card β : ℝ) ^ F.wireExponent y u ≤
      Fintype.card J * F (push ![x, y, v, u] (four (Ψ j))) := by
  have h1 := prop_crossing_cover F Ψ hΨ x y v u
  have hne : (Finset.univ : Finset J).Nonempty := Finset.nonempty_of_ne_empty fun h => by
    simp only [h, Finset.sum_empty] at h1
    exact h1.not_gt (by positivity)
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ
    (fun j => F (push ![x, y, v, u] (four (Ψ j)))) hne
  exact ⟨j, h1.trans ((Finset.sum_le_sum hj).trans_eq (by simp [nsmul_eq_mul]))⟩

/-- Proof of Proposition B.3: Lemma A.3, with the hubs `o, o'` for (c) and `w, w'` for (b), bounds
`F(Ψ_N)` in both ways. So for the `N` of the step before, in logarithms,
`ln |α| · |xv| + ln |β| · |yu|` is at most `ln (Θ + 1)` plus each of the two bounds through the
hubs, where `Ψ_N` is a sum of `R_N` products as in (c) and of `L_N` products as in (b). -/
private theorem prop_crossing_term {J : Type} [Fintype J] (Ψ : J → α → β → α → β → K) (R L : J → ℕ)
    (hR : ∀ j, SplitAB (Ψ j) (R j))
    (hL : ∀ j, SplitAD (Ψ j) (L j))
    (hΨ : ∀ a b c d, ∑ j, Ψ j a b c d = if a = c ∧ b = d then 1 else 0)
    (x y v u o o' w w' : I) :
    ∃ j, Real.log (Fintype.card α) * F.wireExponent x v + Real.log (Fintype.card β) *
        F.wireExponent y u ≤
      Real.log (Fintype.card J) +
      min (Real.log (Fintype.card α) * (F.wireExponent x o + F.wireExponent v o') +
          Real.log (Fintype.card β) * (F.wireExponent y o + F.wireExponent u o') + Real.log (R j) *
              F.wireExponent o o')
        (Real.log (Fintype.card α) * (F.wireExponent x w + F.wireExponent v w') +
          Real.log (Fintype.card β) * (F.wireExponent u w + F.wireExponent y w') + Real.log (L j) *
              F.wireExponent w w') := by
  have hα : (0 : ℝ) < Fintype.card α := Nat.cast_pos.2 Fintype.card_pos
  have hβ : (0 : ℝ) < Fintype.card β := Nat.cast_pos.2 Fintype.card_pos
  obtain ⟨j, hj⟩ := prop_crossing_some F Ψ hΨ x y v u
  have hJ0 : (0 : ℝ) < Fintype.card J := Nat.cast_pos.2 (@Fintype.card_pos _ _ ⟨j⟩)
  refine ⟨j, ?_⟩
  have hexp (s s' : ℝ) (n : ℕ) (e : ℝ) :
      (Fintype.card α : ℝ) ^ s * (Fintype.card β : ℝ) ^ s' * (n : ℝ) ^ e ≤
        Real.exp (Real.log (Fintype.card α) * s + Real.log (Fintype.card β) * s' +
          Real.log n * e) := by
    rw [Real.rpow_def_of_pos hα, Real.rpow_def_of_pos hβ, Real.exp_add, Real.exp_add]
    exact mul_le_mul_of_nonneg_left (rpow_le_exp n e) (by positivity)
  have hm := le_min ((prop_crossing_hubs_c F (hR j) x y v u o o').trans (hexp _ _ _ _))
    ((prop_crossing_hubs_b F (hL j) x y v u w w').trans (hexp _ _ _ _))
  rw [← Real.exp_monotone.map_min] at hm
  have h2 := hj.trans (mul_le_mul_of_nonneg_left hm hJ0.le)
  rw [Real.rpow_def_of_pos hα, Real.rpow_def_of_pos hβ, ← Real.exp_add] at h2
  nth_rewrite 1 [← Real.exp_log hJ0] at h2
  rwa [← Real.exp_add, Real.exp_le_exp] at h2

end Hubs

/-- Proof of Proposition B.3: by pigeonhole, some class of states of energy `e ≤ E` contains at
least a fraction `(E + 1)⁻²` of the states of energy at most `E`. -/
private theorem prop_crossing_classes (E : ℕ) : ∃ μ e,
    e ≤ E ∧ stateCount E ≤ (E + 1) ^ 2 * (states μ e).card ∧
    (states μ e).card ≤ stateCount E := by
  classical
  set S := range (E + 1) ×ˢ range (E + 1) with hS
  have hmaps : ∀ s ∈ lowStates E, (s.1.card, energy s.1 + energy s.2) ∈ S := fun s hs => by
    obtain ⟨h1, h2⟩ := mem_lowStates.1 hs
    have h3 : s.1.card ≤ energy s.1 := by
      simpa only [energy, Finset.card_eq_sum_ones] using Finset.sum_le_sum fun _ _ => by omega
    simp only [hS, mem_product, mem_range]; omega
  obtain ⟨z, hz, hmax⟩ :=
    Finset.exists_max_image S (fun z => (states z.1 z.2).card) ⟨(0, 0), by simp [hS]⟩
  have hzE : z.2 ≤ E := Nat.lt_succ_iff.1 (mem_range.1 (mem_product.1 hz).2)
  refine ⟨z.1, z.2, hzE, ?_, card_le_card fun s hs => lowStates_mono hzE (mem_states.1 hs).1⟩
  rw [stateCount, Finset.card_eq_sum_card_fiberwise hmaps]
  calc ∑ b ∈ S, ((lowStates E).filter fun s => (s.1.card, energy s.1 + energy s.2) = b).card
      ≤ ∑ b ∈ S, (states b.1 b.2).card :=
        Finset.sum_le_sum fun b _ => Finset.card_le_card fun s hs => by
          obtain ⟨h1, rfl⟩ := mem_filter.1 hs
          exact mem_states.2 ⟨mem_lowStates.2 ⟨(mem_lowStates.1 h1).1, le_rfl⟩, rfl,
            (mem_lowStates.1 h1).1.symm, rfl⟩
    _ ≤ ∑ _b ∈ S, (states z.1 z.2).card := Finset.sum_le_sum hmax
    _ = (E + 1) ^ 2 * (states z.1 z.2).card := by
        rw [Finset.sum_const, smul_eq_mul, hS, card_product, card_range, pow_two]

/-- Proof of Proposition B.3: in units of `κ √n`, the logarithms of the sizes of the two classes are
`p + o(1)` and `q + o(1)` by Lemma B.1. Here `κ` has the two properties of Lemma B.1, `n` is the
paper's `n₀`, and the class of size `μ` and energy `e ≤ E = ⌊p² n⌋` is the one found by
pigeonhole. -/
private theorem prop_crossing_class_size {κ : ℝ} (hκ : 0 < κ)
    (hup : ∀ E : ℕ, Real.log (stateCount E) ≤ κ * √E)
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ E : ℕ in atTop, (κ - ε) * √E ≤ Real.log (stateCount E))
        {p : ℝ} (hp : 0 ≤ p)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∃ μ e, e ≤ ⌊p ^ 2 * n⌋₊ ∧ 0 < (states μ e).card ∧
      |Real.log (states μ e).card - p * (κ * √n)| ≤ δ * (κ * √n) := by
  filter_upwards [eventually_le_logLowStates_floor hκ
    (fun ε hε => eventually_atTop.1 (hlow ε hε)) hp (η := δ * κ) (by positivity)] with n hn
  obtain ⟨μ, e, he, hcard, hle⟩ := prop_crossing_classes ⌊p ^ 2 * n⌋₊
  set E := ⌊p ^ 2 * n⌋₊
  have hpos : 0 < (states μ e).card := Nat.pos_of_ne_zero fun h0 => by
    simpa [stateCount, h0] using (lowStates_card_pos E).trans_le hcard
  have h0 : (0 : ℝ) < (states μ e).card := Nat.cast_pos.2 hpos
  have h2 := Real.log_le_log (Nat.cast_pos.2 (lowStates_card_pos E))
    (show ((lowStates E).card : ℝ) ≤ ((E : ℝ) + 1) ^ 2 * (states μ e).card by exact_mod_cast hcard)
  rw [Real.log_mul (by positivity) h0.ne', Real.log_pow] at h2
  push_cast at h2
  have hupper := (Real.log_le_log h0 (by exact_mod_cast hle)).trans (hup E)
  have hv := mul_le_mul_of_nonneg_left (sqrt_floor_le hp n) hκ.le
  have hd : 0 ≤ δ * (κ * √(n : ℝ)) := by positivity
  refine ⟨μ, e, he, hpos, abs_le.2 ⟨?_, ?_⟩⟩ <;>
    linarith [show logLowStates E = Real.log (lowStates E).card from rfl]

/-- Proof of Proposition B.3: in the same units, the logarithm of the number of products in (b) is
at most `l + o(1)` and that in (c) at most `r + o(1)`, with `l² = N/n₀` and `r² = (Θ - N)/n₀`. Here
`M` stands for `N` and for `Θ - N`, which are at most `Θ ≤ A n`, and `(M + 1) P(M)` is the number
of products. -/
private theorem prop_crossing_products {κ : ℝ} (hκ : 0 < κ)
    (hup : ∀ E : ℕ, Real.log (stateCount E) ≤ κ * √E) {A : ℝ}
    (hA : 0 ≤ A) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ M : ℕ, (M : ℝ) ≤ A * n →
      Real.log (((M + 1) * stateCount M : ℕ) : ℝ) ≤ (√(M : ℝ) / √(n : ℝ) + δ) * (κ * √n) := by
  filter_upwards [eventually_log_le_mul_sqrt hA (η := δ * κ) (by positivity),
    eventually_ge_atTop 1] with n hlog hn M hM
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hn)
  have h2 : Real.log ((M : ℝ) + 1) ≤ δ * κ * √(n : ℝ) :=
    (Real.log_le_log (by positivity) (by linarith)).trans hlog
  have hsc : (stateCount M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (lowStates_card_pos M).ne'
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Real.log_mul (by positivity) hsc, add_mul,
    mul_left_comm (√(M : ℝ) / √(n : ℝ)) κ, div_mul_cancel₀ _ hsn.ne']
  linarith [hup M]

/-- Proof of Proposition B.3, the tensors: for every `δ > 0` there are `s > 0` and finite sets
`α, β` (the paper's `κ √n₀` and the classes of states) with `ln |α| = (p ± δ) s` and
`ln |β| = (q ± δ) s`, and at most `e^(δ s)` tensors `Ψ_N` with sum the two wires (Proposition
B.2 (a)), where `Ψ_N` is a sum of at most `e^((r + δ) s)` products as in (c) and of at most
`e^((l + δ) s)` products as in (b), with `r² + l² ≤ 2 (p² + q²)`. -/
private theorem prop_crossing_tensors (K : Type) [Field K] {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (α β J : Type) (_ : Fintype α) (_ : DecidableEq α) (_ : Nonempty α)
      (_ : Fintype β) (_ : DecidableEq β) (_ : Nonempty β) (_ : Fintype J)
      (Ψ : J → α → β → α → β → K) (R L : J → ℕ) (s : ℝ), 0 < s ∧
      (∀ j, SplitAB (Ψ j) (R j)) ∧ (∀ j, SplitAD (Ψ j) (L j)) ∧
      (∀ a b c d, ∑ j, Ψ j a b c d = if a = c ∧ b = d then 1 else 0) ∧
      Real.log (Fintype.card J) ≤ δ * s ∧ |Real.log (Fintype.card α) - p * s| ≤ δ * s ∧
      |Real.log (Fintype.card β) - q * s| ≤ δ * s ∧
      ∀ j, ∃ r l : ℝ, 0 ≤ r ∧ 0 ≤ l ∧ r ^ 2 + l ^ 2 ≤ 2 * (p ^ 2 + q ^ 2) ∧
        Real.log (R j) ≤ (r + δ) * s ∧ Real.log (L j) ≤ (l + δ) * s := by
  obtain ⟨c, hc, hup, hlow⟩ := exists_log_stateCount_asymptotic
  set A : ℝ := 2 * (p ^ 2 + q ^ 2) with hA
  have hA0 : 0 ≤ A := by positivity
  obtain ⟨n, ⟨⟨μ, e₁, he₁, hpos₁, hsize₁⟩, ⟨ν, e₂, he₂, hpos₂, hsize₂⟩⟩, hnum, hlog, hn⟩ :=
    (((prop_crossing_class_size hc hup hlow hp hδ).and
        (prop_crossing_class_size hc hup hlow hq hδ)).and
      ((prop_crossing_products hc hup hA0 hδ).and
        ((eventually_log_le_mul_sqrt hA0 (η := δ * c) (by positivity)).and
            (eventually_ge_atTop 1)))).exists
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
  obtain ⟨Ψ, hΨ, hL, hR⟩ := exists_crossing_identity μ ν e₁ e₂
  have hH : ((2 * (e₁ + e₂) : ℕ) : ℝ) ≤ A * n := by
    have h1 : (e₁ : ℝ) ≤ p ^ 2 * n := (Nat.cast_le.2 he₁).trans (Nat.floor_le (by positivity))
    have h2 : (e₂ : ℝ) ≤ q ^ 2 * n := (Nat.cast_le.2 he₂).trans (Nat.floor_le (by positivity))
    push_cast; linarith [hA]
  refine ⟨↥(states μ e₁), ↥(states ν e₂), Fin (2 * (e₁ + e₂) + 1), inferInstance, inferInstance,
    (Finset.card_pos.1 hpos₁).to_subtype, inferInstance, inferInstance,
    (Finset.card_pos.1 hpos₂).to_subtype, inferInstance, fun N a b c d => ((Ψ N a b c d : ℤ) : K),
    fun N => (2 * (e₁ + e₂) - N + 1) * stateCount (2 * (e₁ + e₂) - N),
    fun N => (N + 1) * stateCount N, c * Real.sqrt n, by positivity,
    fun N => ?_, fun N => ?_, fun a b c d => ?_, ?_, by rwa [Fintype.card_coe],
    by rwa [Fintype.card_coe], fun N => ?_⟩
  · obtain ⟨g, h, hgh⟩ := hR N _ rfl
    exact ⟨fun k z => (g k z : K), fun k z => (h k z : K), fun a b c d => by simp [hgh]⟩
  · obtain ⟨g, h, hgh⟩ := hL N
    exact ⟨fun k z => (g k z : K), fun k z => (h k z : K), fun a b c d => by simp [hgh]⟩
  · rw [← Int.cast_sum, hΨ, ite_and]
    split_ifs <;> simp
  · simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, mul_assoc] using
      (Real.log_le_log (by positivity) (add_le_add_left hH 1)).trans hlog
  · have hN : (N : ℕ) ≤ 2 * (e₁ + e₂) := by omega
    refine ⟨Real.sqrt ((2 * (e₁ + e₂) - N : ℕ) : ℝ) / Real.sqrt n,
      Real.sqrt ((N : ℕ) : ℝ) / Real.sqrt n, by positivity, by positivity, ?_,
      hnum _ ((Nat.cast_le.2 (Nat.sub_le _ _)).trans hH),
      hnum _ ((Nat.cast_le.2 hN).trans hH)⟩
    rwa [div_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg (2 * (e₁ + e₂) - N)),
      Real.sq_sqrt (Nat.cast_nonneg (N : ℕ)), Real.sq_sqrt hn0.le, ← add_div, div_le_iff₀ hn0,
      Nat.cast_sub hN, sub_add_cancel]

/-- Proof of Proposition B.3 for the wire exponents of a spectral point; a limit of `(r, l)` along a
subsequence gives the first statement. -/
private theorem prop_crossing_spectral {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) {I : Type} [Fintype I]
    [DecidableEq I] (F : SpectralPoint K I) (x y v u o o' w w' : I) :
    ∃ z ∈ quarter (2 * (p ^ 2 + q ^ 2)), p * F.wireExponent x v + q * F.wireExponent y u ≤
      min (p * F.wireExponent x o + q * F.wireExponent y o + p * F.wireExponent v o' + q *
          F.wireExponent u o' + z.1 * F.wireExponent o o')
        (p * F.wireExponent x w + q * F.wireExponent u w + q * F.wireExponent y w' + p *
            F.wireExponent v w' + z.2 * F.wireExponent w w') := by
  refine exists_quarter (by positivity) fun δ hδ => ?_
  obtain ⟨α, β, J, _, _, _, _, _, _, _, Ψ, R, L, s, hs, hR, hL, hΨ, hJ, hα, hβ, hrl⟩ :=
    prop_crossing_tensors K hp hq (δ := δ / 8) (by positivity)
  obtain ⟨j, hj⟩ := prop_crossing_term F Ψ R L hR hL hΨ x y v u o o' w w'
  obtain ⟨r, l, hr, hl, hrl, h1, h2⟩ := hrl j
  refine ⟨(r, l), ⟨hr, hl, hrl⟩, ?_⟩
  set A := Real.log (Fintype.card α)
  set B := Real.log (Fintype.card β)
  obtain ⟨hα1, hα2⟩ := abs_le.1 hα
  obtain ⟨hβ1, hβ2⟩ := abs_le.1 hβ
  have hi (a b : I) {Z c : ℝ} (h : Z ≤ c * s + δ / 8 * s) :
      Z * F.wireExponent a b ≤ (c * F.wireExponent a b + δ / 8) * s := by
    nlinarith [mul_le_mul_of_nonneg_right h (F.wireExponent_nonneg a b),
      mul_le_of_le_one_right (by positivity : 0 ≤ δ / 8 * s) (F.wireExponent_le_one a b)]
  have lo (a b : I) {Z c : ℝ} (h : c * s - δ / 8 * s ≤ Z) :
      (c * F.wireExponent a b - δ / 8) * s ≤ Z * F.wireExponent a b := by
    nlinarith [mul_le_mul_of_nonneg_right h (F.wireExponent_nonneg a b),
      mul_le_of_le_one_right (by positivity : 0 ≤ δ / 8 * s) (F.wireExponent_le_one a b)]
  have b1 := lo x v (Z := A) (c := p) (by linarith)
  have b2 := lo y u (Z := B) (c := q) (by linarith)
  rw [← min_add_add_right]
  refine le_min (le_of_mul_le_mul_right ?_ hs) (le_of_mul_le_mul_right ?_ hs)
  · nlinarith [hj.trans (add_le_add le_rfl (min_le_left _ _)),
      hi x o (Z := A) (c := p) (by linarith), hi y o (Z := B) (c := q) (by linarith),
      hi v o' (Z := A) (c := p) (by linarith), hi u o' (Z := B) (c := q) (by linarith),
      hi o o' (Z := Real.log (R j)) (c := r) (by linarith)]
  · nlinarith [hj.trans (add_le_add le_rfl (min_le_right _ _)),
      hi x w (Z := A) (c := p) (by linarith), hi u w (Z := B) (c := q) (by linarith),
      hi v w' (Z := A) (c := p) (by linarith), hi y w' (Z := B) (c := q) (by linarith),
      hi w w' (Z := Real.log (L j)) (c := l) (by linarith)]

/-- **Paper: Proposition B.3.** Let `x, v, y, u, o, o', w, w'` be points of a price
`d` and `p, q ≥ 0`. There are `r, l ≥ 0` with `r² + l² ≤ 2 (p² + q²)` such that
`p d(x, v) + q d(y, u)` is at most each of
`p d(x, o) + q d(y, o) + p d(v, o') + q d(u, o') + r d(o, o')` and
`p d(x, w) + q d(u, w) + q d(y, w') + p d(v, w') + l d(w, w')`.

The points need not be distinct: the proof pulls the price back to eight distinct points. Both
inequalities are homogeneous in the distances, and the pairs `(r, l)` lie in a compact set, so
they pass to limits. -/
theorem isPrice_crossing {Y : Type} {d : Y → Y → ℝ} (hd : IsPrice K d)
    (x v y u o o' w w' : Y)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ∃ r l : ℝ, 0 ≤ r ∧ 0 ≤ l ∧ r ^ 2 + l ^ 2 ≤ 2 * (p ^ 2 + q ^ 2) ∧
      p * d x v + q * d y u ≤ p * d x o + q * d y o + p * d v o' + q * d u o' + r * d o o' ∧
      p * d x v + q * d y u ≤ p * d x w + q * d u w + q * d y w' + p * d v w' + l * d w w' := by
  set ρ := 2 * (p ^ 2 + q ^ 2) with hρ
  obtain ⟨z, ⟨h1, h2, h3⟩, h⟩ : ∃ z ∈ quarter ρ, p * d x v + q * d y u ≤
      min (p * d x o + q * d y o + p * d v o' + q * d u o' + z.1 * d o o')
        (p * d x w + q * d u w + q * d y w' + p * d v w' + z.2 * d w w') := by
    refine exists_quarter (by positivity) fun δ hδ => ?_
    set T := 3 * (p + q) + ρ + 1 with hT
    have hT0 : 0 < T := by positivity
    set η := δ / T with hη
    have hη0 : 0 < η := by positivity
    obtain ⟨F, c, hc, hF⟩ := hd.exists_spectralPoint ![x, y, v, u, o, o', w, w'] hη0
    obtain ⟨z, ⟨hz1, hz2, hz3⟩, h⟩ := prop_crossing_spectral hp hq F 0 1 2 3 4 5 6 7
    refine ⟨z, ⟨hz1, hz2, hz3⟩, ?_⟩
    have q1 : z.1 ≤ ρ + 1 := by nlinarith [sq_nonneg (z.1 - 1)]
    have q2 : z.2 ≤ ρ + 1 := by nlinarith [sq_nonneg (z.2 - 1)]
    have lo (i j : Fin 8) {t : ℝ} (ht : 0 ≤ t) :
        t * (c * F.wireExponent i j) ≤
          t * d (![x, y, v, u, o, o', w, w'] i) (![x, y, v, u, o, o', w, w'] j) + t * η :=
      mul_add t _ η ▸ mul_le_mul_of_nonneg_left (by linarith [(abs_lt.1 (hF i j)).1]) ht
    have hi (i j : Fin 8) {t : ℝ} (ht : 0 ≤ t) :
        t * d (![x, y, v, u, o, o', w, w'] i) (![x, y, v, u, o, o', w, w'] j) ≤
          t * (c * F.wireExponent i j) + t * η :=
      mul_add t _ η ▸ mul_le_mul_of_nonneg_left (by linarith [(abs_lt.1 (hF i j)).2]) ht
    have hsum : 3 * (p * η) + 3 * (q * η) + (ρ + 1) * η = δ :=
      (by ring : _ = η * T).trans (div_mul_cancel₀ δ hT0.ne')
    obtain ⟨a1, a2⟩ : _ ∧ _ := ⟨hi 0 2 hp, hi 1 3 hq⟩
    dsimp at a1 a2
    rw [← min_add_add_right]
    refine le_min ?_ ?_
    · obtain ⟨a3, a4, a5, a6, a7⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ :=
        ⟨lo 0 4 hp, lo 1 4 hq, lo 2 5 hp, lo 3 5 hq, lo 4 5 hz1⟩
      dsimp at a3 a4 a5 a6 a7
      linarith [mul_le_mul_of_nonneg_left (h.trans (min_le_left _ _)) hc,
        mul_le_mul_of_nonneg_right q1 hη0.le]
    · obtain ⟨a3, a4, a5, a6, a7⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ :=
        ⟨lo 0 6 hp, lo 3 6 hq, lo 1 7 hq, lo 2 7 hp, lo 6 7 hz2⟩
      dsimp at a3 a4 a5 a6 a7
      linarith [mul_le_mul_of_nonneg_left (h.trans (min_le_right _ _)) hc,
        mul_le_mul_of_nonneg_right q2 hη0.le]
  exact ⟨z.1, z.2, h1, h2, h3, le_min_iff.1 h⟩

/-- **Paper: display (B.2) of Proposition B.3**, the inequality (Q) of `CrossingLength`. Adding the
two inequalities of `isPrice_crossing` and using `r λ ≤ (τ/2) r² + λ²/(2τ)` gives, for every
`τ > 0`,
`2 (p d(x, v) + q d(y, u)) ≤ p (d(x, o) + d(v, o') + d(x, w) + d(v, w')) +
q (d(y, o) + d(u, o') + d(u, w) + d(y, w')) + τ (p² + q²) + (d(o, o')² + d(w, w')²)/(2τ)`. -/
theorem isPrice_crossing_two_mul_le {Y : Type} {d : Y → Y → ℝ} (hd : IsPrice K d)
    (x v y u o o' w w' : Y)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (τ : ℝ) (hτ : 0 < τ) :
    2 * (p * d x v + q * d y u) ≤
      p * (d x o + d v o' + d x w + d v w') + q * (d y o + d u o' + d u w + d y w') +
        τ * (p ^ 2 + q ^ 2) + (d o o' ^ 2 + d w w' ^ 2) / (2 * τ) := by
  obtain ⟨r, l, hr, hl, hrl, h1, h2⟩ := isPrice_crossing hd x v y u o o' w w' hp hq
  have am (a b : ℝ) : a * b ≤ τ / 2 * a ^ 2 + b ^ 2 / (2 * τ) := by
    have e : τ / 2 * a ^ 2 + b ^ 2 / (2 * τ) - a * b = (τ * a - b) ^ 2 / (2 * τ) := by
      field_simp; ring
    linarith [div_nonneg (sq_nonneg (τ * a - b)) (mul_nonneg zero_le_two hτ.le)]
  rw [add_div]
  linarith [am r (d o o'), am l (d w w'),
    mul_le_mul_of_nonneg_left hrl (div_nonneg hτ.le zero_le_two)]

end Cslib.Circuits.Arithmetic.Separation.Curvature
