/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Compose
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.BaseChange
import Mathlib.Tactic.Ring

/-!
# From one cut to the cut at a scale

The hypothesis `Cut.OneCutAt` gives, at a scale `v`, one cut by any factor `2 ≤ k ≤ v ^ 64`:
the number of steps goes down by `k`, up to a loss `Λ`. Cutting by `v ^ 63` as long as the steps
are many, and once more at the end, brings the number of steps down to `v ^ H`
(`Cut.OneCutAt.exists_isCut_iterate`); every cut multiplies the bounds for the pieces, the
sizes and the time by a loss `X ≥ 8 Λ ^ 2`. When the total loss is at most `v`, the result is the
cut of the cut hypothesis (`Cut.OneCutAt.exists_isCut`).

`Cut.OneCutAt` is a hypothesis here, with the loss `Λ` as a parameter and for all numbers of
steps `τ ≤ v ^ α`. [AnthropicVPVNP2026], Theorem J.3 (one cut) gives the bounds of `Cut.OneCutAt`
with `Λ = (lg v) ^ C` and only for `τ` with `4 * lg τ ≤ (lg v) ^ 2`; the user of this file must
check that this logarithmic bound holds for all `τ ≤ v ^ α`. The results are the conditional
step of the proof of Theorem J.4 (cuts at all scales): the induction on the numbers of steps,
sizes and pieces, given one cut (module `NS1.OneCut`).

## Main definitions

* `Cut.OneCutAt`: one cut by any factor at a scale.

## Main results

* `Cut.OneCutAt.exists_isCut_iterate`: the iterated cuts, with their losses.
* `Cut.OneCutAt.exists_isCut`: the cut to `v ^ H` steps when the total loss is at most
  `v`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem J.3 (one cut), whose bounds are the hypothesis `Cut.OneCutAt` in the range where its
  logarithmic condition holds, and the proof of Theorem J.4 (cuts at all scales) for the
  iteration; module `NS1.OneCut`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Cut

open Interpreter Interpreter.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {v a₀ α H Λ : ℕ}

/-- One cut at the scale `v`: plain sums of `v ^ a₀ ≤ τ ≤ v ^ α` steps can be cut by any factor
`2 ≤ k ≤ v ^ 64`, with the loss `Λ`, by a program of size at most `v ^ a₀`. These are the bounds
of [AnthropicVPVNP2026], Theorem J.3, which proves them for `Λ = (lg v) ^ C` and for `τ` with
`4 * lg τ ≤ (lg v) ^ 2`; here they are assumed for all `τ` in the range and for a given `Λ`. -/
@[expose] def OneCutAt (θ : List Bool → A) (v a₀ α Λ : ℕ) : Prop :=
  ∀ τ s k, v ^ a₀ ≤ τ → τ ≤ v ^ α → s ≤ τ → 2 ≤ k → k ≤ v ^ 64 →
    ∃ G : Tree, G.size ≤ v ^ a₀ ∧ IsCut θ τ s (τ * Λ / k)
      ((s / k + τ / v ^ 256) * Λ) (k * Λ) ((s + τ * k / v ^ 256) * Λ) G

namespace OneCutAt

theorem mono {Λ' : ℕ} (h : OneCutAt θ v a₀ α Λ) (hΛ : Λ ≤ Λ') : OneCutAt θ v a₀ α Λ' :=
  fun τ s k h1 h2 h3 h4 h5 =>
    let ⟨G, hG, hcut⟩ := h τ s k h1 h2 h3 h4 h5
    ⟨G, hG, hcut.mono (Nat.div_le_div_right (Nat.mul_le_mul_left _ hΛ))
      (Nat.mul_le_mul_left _ hΛ) (Nat.mul_le_mul_left _ hΛ) (Nat.mul_le_mul_left _ hΛ)⟩

/-- One cut by `k`, with the bounds for the sizes and the time multiplied out. -/
private theorem exists_isCut_factor (hc : OneCutAt θ v a₀ α Λ) (hv : 1 ≤ v) {τ s k c : ℕ}
    (hτ : v ^ a₀ ≤ τ) (hτα : τ ≤ v ^ α) (hk : 2 ≤ k) (hkv : k ≤ v ^ 64)
    (hs : s * v ^ 48 ≤ c * τ) (hc1 : 1 ≤ c) (hcv : c ≤ v) :
    ∃ (G : Tree) (s' t : ℕ), G.size ≤ v ^ a₀ ∧ IsCut θ τ s (τ * Λ / k) s' (k * Λ) t G ∧
      s' * k * v ^ 48 ≤ 2 * c * τ * Λ ∧ t * v ^ 48 ≤ 2 * c * τ * Λ := by
  have ppos : ∀ a, 0 < v ^ a := fun a => Nat.pow_pos hv
  have pmono : ∀ {a b}, a ≤ b → v ^ a ≤ v ^ b := fun h => Nat.pow_le_pow_right hv h
  have hsτ : s ≤ τ := Nat.le_of_mul_le_mul_right (hs.trans <| (Nat.mul_le_mul_right _
    (hcv.trans (Nat.le_self_pow (by norm_num) v))).trans (Nat.mul_comm _ _).le) (ppos 48)
  have hcτ : τ ≤ c * τ := Nat.le_mul_of_pos_left _ hc1
  obtain ⟨G, hG, hcut⟩ := hc τ s k hτ hτα hsτ hk hkv
  have hA : τ / v ^ 256 * (k * v ^ 48) ≤ τ :=
    calc τ / v ^ 256 * (k * v ^ 48) ≤ τ / v ^ 256 * (v ^ 64 * v ^ 48) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hkv)
      _ ≤ τ / v ^ 256 * v ^ 256 :=
        Nat.mul_le_mul_left _ ((pow_add v 64 48).symm.le.trans (pmono (by norm_num)))
      _ ≤ τ := Nat.div_mul_le_self _ _
  have hB : τ * k / v ^ 256 * v ^ 48 ≤ τ := by
    have h1 : τ * k / v ^ 256 ≤ τ / v ^ 192 := by
      rw [show v ^ 256 = v ^ 64 * v ^ 192 by rw [← pow_add], ← Nat.div_div_eq_div_mul]
      exact Nat.div_le_div_right (Nat.div_le_of_le_mul (by
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul_right _ hkv))
    exact (Nat.mul_le_mul h1 (pmono (by norm_num))).trans (Nat.div_mul_le_self _ _)
  refine ⟨G, _, _, hG, hcut, ?_, ?_⟩
  · calc (s / k + τ / v ^ 256) * Λ * k * v ^ 48
        = (s / k * k * v ^ 48 + τ / v ^ 256 * (k * v ^ 48)) * Λ := by ring
      _ ≤ (c * τ + c * τ) * Λ := Nat.mul_le_mul_right _ (Nat.add_le_add
          ((Nat.mul_le_mul_right _ (Nat.div_mul_le_self s k)).trans hs) (hA.trans hcτ))
      _ = 2 * c * τ * Λ := by ring
  · calc (s + τ * k / v ^ 256) * Λ * v ^ 48
        = (s * v ^ 48 + τ * k / v ^ 256 * v ^ 48) * Λ := by ring
      _ ≤ (c * τ + c * τ) * Λ := Nat.mul_le_mul_right _ (Nat.add_le_add hs (hB.trans hcτ))
      _ = 2 * c * τ * Λ := by ring

/-- The last cut: fewer than `v ^ H * v ^ 64 / Λ` steps are cut to `v ^ H` steps at once. -/
private theorem exists_isCut_last (hc : OneCutAt θ v a₀ α Λ) (hv : 1 ≤ v) (hΛ : 2 ≤ Λ)
    (hH : a₀ ≤ H) {τ s c : ℕ} (hτ : v ^ H ≤ τ) (hτα : τ ≤ v ^ α)
    (hτΛ : τ * Λ < v ^ H * v ^ 64) (hs : s * v ^ 48 ≤ c * τ) (hc1 : 1 ≤ c) (hcv : c ≤ v) :
    ∃ (G : Tree) (P t s' : ℕ), IsCut θ τ s (v ^ H) s' P t G ∧ P * v ^ H ≤ τ * (2 * Λ ^ 2) ∧
      t * v ^ 48 ≤ c * τ * (2 * Λ) ∧ s' * v ^ 48 ≤ c * v ^ H * 2 ∧ G.size ≤ v ^ a₀ := by
  have hV : 0 < v ^ H := Nat.pow_pos hv
  set k := τ * Λ / v ^ H + 1
  have hk1 : τ * Λ < k * v ^ H :=
    Nat.mul_comm (v ^ H) k ▸ Nat.lt_mul_div_succ (τ * Λ) hV
  have hk2 : k * v ^ H ≤ τ * Λ + v ^ H := by
    simpa only [k, Nat.add_mul, Nat.one_mul] using
      Nat.add_le_add_right (Nat.div_mul_le_self (τ * Λ) (v ^ H)) (v ^ H)
  have hk0 : 2 ≤ k := Nat.succ_le_succ ((Nat.le_div_iff_mul_le hV).2
    (by simpa using hτ.trans (Nat.le_mul_of_pos_right _ (by omega))))
  have hkv : k ≤ v ^ 64 := Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul hV).2
    (hτΛ.trans_eq (Nat.mul_comm _ _)))
  obtain ⟨G, s', t, hG, hcut, hs', ht⟩ := hc.exists_isCut_factor hv
    ((Nat.pow_le_pow_right hv hH).trans hτ) hτα hk0 hkv hs hc1 hcv
  refine ⟨G, k * Λ, t, s', hcut.mono (Nat.div_le_of_le_mul hk1.le) le_rfl le_rfl le_rfl, ?_,
    ht.trans_eq (by ring), Nat.le_of_mul_le_mul_right (c := k) ?_ (by omega), hG⟩
  · calc k * Λ * v ^ H = k * v ^ H * Λ := by ring
      _ ≤ (τ * Λ + τ * Λ) * Λ := Nat.mul_le_mul_right _ (hk2.trans (Nat.add_le_add_left
          (hτ.trans (Nat.le_mul_of_pos_right _ (by omega))) _))
      _ = τ * (2 * Λ ^ 2) := by ring
  · calc s' * v ^ 48 * k = s' * k * v ^ 48 := by ring
      _ ≤ 2 * c * (τ * Λ) := hs'.trans_eq (by ring)
      _ ≤ 2 * c * (k * v ^ H) := Nat.mul_le_mul_left _ hk1.le
      _ = c * v ^ H * 2 * k := by ring

/-- **Iterated cuts** ([AnthropicVPVNP2026], proof of Theorem J.4): cut by `v ^ 63` as long as the
steps are many, and at the end once to `v ^ H` steps. After at most `r + 1` cuts, the pieces, the
time and the sizes have lost at most `X ^ (r + 1)`, for any `X ≥ 8 Λ ^ 2`. -/
theorem exists_isCut_iterate (hc : OneCutAt θ v a₀ α Λ) (hv : 110 ≤ v) (hΛ : 2 ≤ Λ)
    (hΛv : Λ ≤ v) (hH : a₀ ≤ H) (hH' : 200 ≤ H) {X : ℕ} (hX : 8 * Λ ^ 2 ≤ X) :
    ∀ r τ s c, v ^ H ≤ τ → τ ≤ v ^ α → τ * Λ < v ^ H * v ^ (64 + 62 * r) →
      s * v ^ 48 ≤ c * τ → 1 ≤ c → c * 4 ^ (r + 1) ≤ v →
      ∃ (G : Tree) (P t s' : ℕ), IsCut θ τ s (v ^ H) s' P t G ∧
        P * v ^ H ≤ τ * X ^ (r + 1) ∧ t * v ^ 48 ≤ c * τ * X ^ (r + 1) ∧
        s' * v ^ 48 ≤ c * v ^ H * X ^ (r + 1) ∧ G.size ≤ 4 ^ r * (v ^ a₀ + 3000) := by
  have hv1 : 1 ≤ v := by omega
  have ppos : ∀ a, 0 < v ^ a := fun a => Nat.pow_pos hv1
  have pmono : ∀ {a b}, a ≤ b → v ^ a ≤ v ^ b := fun h => Nat.pow_le_pow_right hv1 h
  have hΛsq : Λ ≤ Λ ^ 2 := Nat.le_self_pow (by norm_num) Λ
  -- the last cut, with the losses of `r + 1` cuts
  have last : ∀ r τ s c, v ^ H ≤ τ → τ ≤ v ^ α → τ * Λ < v ^ H * v ^ 64 → s * v ^ 48 ≤ c * τ →
      1 ≤ c → c ≤ v → ∃ (G : Tree) (P t s' : ℕ), IsCut θ τ s (v ^ H) s' P t G ∧
        P * v ^ H ≤ τ * X ^ (r + 1) ∧ t * v ^ 48 ≤ c * τ * X ^ (r + 1) ∧
        s' * v ^ 48 ≤ c * v ^ H * X ^ (r + 1) ∧ G.size ≤ 4 ^ r * (v ^ a₀ + 3000) := by
    intro r τ s c hτ hτα hτΛ hs hc1 hcv
    obtain ⟨G, P, t, s', h1, h2, h3, h4, h5⟩ :=
      hc.exists_isCut_last hv1 hΛ hH hτ hτα hτΛ hs hc1 hcv
    have hXr : X ≤ X ^ (r + 1) := Nat.le_self_pow (Nat.succ_ne_zero r) X
    exact ⟨G, P, t, s', h1, h2.trans (Nat.mul_le_mul_left _ (le_trans (by omega) hXr)),
      h3.trans (Nat.mul_le_mul_left _ (le_trans (by omega) hXr)),
      h4.trans (Nat.mul_le_mul_left _ (le_trans (by omega) hXr)),
      h5.trans ((Nat.le_add_right _ _).trans
        (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by norm_num))))⟩
  intro r
  induction r with
  | zero =>
    intro τ s c hτ hτα hτΛ hs hc1 hcv
    exact last 0 τ s c hτ hτα (by simpa using hτΛ) hs hc1 (by omega)
  | succ r ih =>
    intro τ s c hτ hτα hτΛ hs hc1 hcv
    have h4r : 1 ≤ 4 ^ (r + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hcv' : 4 * c * 4 ^ (r + 1) ≤ v := hcv.trans_eq' (by rw [pow_succ 4 (r + 1)]; ring)
    have hcv1 : 4 * c ≤ v := (Nat.le_mul_of_pos_right _ h4r).trans hcv'
    rcases Nat.lt_or_ge (τ * Λ) (v ^ H * v ^ 64) with hlast | hmany
    · exact last (r + 1) τ s c hτ hτα hlast hs hc1 (by omega)
    -- one cut by `v ^ 63`, then the rest
    obtain ⟨G₁, s₁, t₁, hG₁, hcut₁, hs₁, ht₁⟩ := hc.exists_isCut_factor hv1 (k := v ^ 63)
      ((pmono hH).trans hτ) hτα ((by omega : 2 ≤ v).trans (Nat.le_self_pow (by norm_num) v))
      (pmono (by norm_num)) hs hc1 (by omega)
    set τ₁ := τ * Λ / v ^ 63 with hτ₁
    have hτ₁le : τ₁ * v ^ 63 ≤ τ * Λ := Nat.div_mul_le_self _ _
    have hτ₁V : v ^ H ≤ τ₁ := (Nat.le_div_iff_mul_le (ppos 63)).2
      ((Nat.mul_le_mul_left _ (pmono (by norm_num))).trans hmany)
    have hτ₁half : τ * Λ ≤ 2 * (τ₁ * v ^ 63) := by
      have h1 := Nat.lt_mul_div_succ (τ * Λ) (ppos 63)
      have h2 : v ^ 63 ≤ τ₁ * v ^ 63 := Nat.le_mul_of_pos_left _ ((ppos H).trans_le hτ₁V)
      rw [← hτ₁, Nat.mul_add, Nat.mul_one, Nat.mul_comm (v ^ 63)] at h1
      omega
    have hτ₁τ : τ₁ ≤ τ := Nat.le_of_mul_le_mul_right (hτ₁le.trans (Nat.mul_le_mul_left _
      (hΛv.trans (Nat.le_self_pow (by norm_num) v)))) (ppos 63)
    have hτ₁Λ : τ₁ * Λ < v ^ H * v ^ (64 + 62 * r) := by
      have h1 : τ₁ < v ^ H * v ^ (63 + 62 * r) := by
        refine lt_of_mul_lt_mul_right (a := v ^ 63) (hτ₁le.trans_lt (hτΛ.trans_eq ?_))
          (Nat.zero_le _)
        rw [Nat.mul_assoc, ← pow_add]
        ring_nf
      calc τ₁ * Λ ≤ τ₁ * v := Nat.mul_le_mul_left _ hΛv
        _ < v ^ H * v ^ (63 + 62 * r) * v := Nat.mul_lt_mul_of_pos_right h1 (by omega)
        _ = v ^ H * v ^ (64 + 62 * r) := by
          rw [Nat.mul_assoc, ← pow_succ]
          congr 2
          ring
    have hs₁c : s₁ * v ^ 48 ≤ 4 * c * τ₁ := Nat.le_of_mul_le_mul_right (c := v ^ 63)
      (calc s₁ * v ^ 48 * v ^ 63 = s₁ * v ^ 63 * v ^ 48 := by ring
        _ ≤ 2 * c * (τ * Λ) := hs₁.trans_eq (by ring)
        _ ≤ 2 * c * (2 * (τ₁ * v ^ 63)) := Nat.mul_le_mul_left _ hτ₁half
        _ = 4 * c * τ₁ * v ^ 63 := by ring) (ppos 63)
    obtain ⟨G₂, P₂, t₂, s₂, hcut₂, hP₂, ht₂, hs₂, hG₂⟩ :=
      ih τ₁ s₁ (4 * c) hτ₁V (hτ₁τ.trans hτα) hτ₁Λ hs₁c (by omega) hcv'
    rw [pow_succ X (r + 1)]
    set Y := X ^ (r + 1)
    have hΛY : Λ ^ 2 ≤ Λ ^ 2 * Y := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by omega))
    have hXY : 8 * (Λ ^ 2 * Y) ≤ Y * X :=
      (Nat.mul_assoc 8 (Λ ^ 2) Y).symm.trans_le (Nat.mul_comm X Y ▸ Nat.mul_le_mul_right Y hX)
    have hP : v ^ 63 * Λ * P₂ * v ^ H ≤ τ * (Λ ^ 2 * Y) :=
      calc v ^ 63 * Λ * P₂ * v ^ H = v ^ 63 * Λ * (P₂ * v ^ H) := by ring
        _ ≤ v ^ 63 * Λ * (τ₁ * Y) := Nat.mul_le_mul_left _ hP₂
        _ = τ₁ * v ^ 63 * (Λ * Y) := by ring
        _ ≤ τ * Λ * (Λ * Y) := Nat.mul_le_mul_right _ hτ₁le
        _ = τ * (Λ ^ 2 * Y) := by ring
    refine ⟨_, _, _, _, hcut₁.comp hcut₂, hP.trans (Nat.mul_le_mul_left _ (by omega)), ?_,
      hs₂.trans ?_, ?_⟩
    · -- the time
      have b2 : v ^ 63 * Λ * t₂ * v ^ 48 ≤ c * τ * (4 * (Λ ^ 2 * Y)) :=
        calc v ^ 63 * Λ * t₂ * v ^ 48 = v ^ 63 * Λ * (t₂ * v ^ 48) := by ring
          _ ≤ v ^ 63 * Λ * (4 * c * τ₁ * Y) := Nat.mul_le_mul_left _ ht₂
          _ = τ₁ * v ^ 63 * (4 * c * Λ * Y) := by ring
          _ ≤ τ * Λ * (4 * c * Λ * Y) := Nat.mul_le_mul_right _ hτ₁le
          _ = c * τ * (4 * (Λ ^ 2 * Y)) := by ring
      have b3 : v ^ 63 * Λ * (62 * P₂) * v ^ 48 ≤ c * τ * (Λ ^ 2 * Y) :=
        calc v ^ 63 * Λ * (62 * P₂) * v ^ 48 = v ^ 63 * Λ * P₂ * (62 * v ^ 48) := by ring
          _ ≤ v ^ 63 * Λ * P₂ * v ^ H := Nat.mul_le_mul_left _
              ((Nat.mul_le_mul_right _ (by omega : 62 ≤ v)).trans
                ((pow_succ' v 48).symm.le.trans (pmono (by omega))))
          _ ≤ c * (τ * (Λ ^ 2 * Y)) := hP.trans (Nat.le_mul_of_pos_left _ hc1)
          _ = c * τ * (Λ ^ 2 * Y) := by ring
      have b4 : v ^ 63 * Λ * 110 * v ^ 48 + 100 * v ^ 48 ≤ c * τ * 2 := by
        have h1 : v ^ 63 * Λ * 110 * v ^ 48 ≤ τ :=
          calc v ^ 63 * Λ * 110 * v ^ 48 ≤ v ^ 63 * v * v * v ^ 48 := Nat.mul_le_mul_right _
                (Nat.mul_le_mul (Nat.mul_le_mul_left _ hΛv) hv)
            _ = v ^ 113 := by ring
            _ ≤ τ := (pmono (by omega)).trans hτ
        have h2 : 100 * v ^ 48 ≤ τ :=
          calc 100 * v ^ 48 ≤ v * v ^ 48 := Nat.mul_le_mul_right _ (by omega)
            _ = v ^ 49 := (pow_succ' v 48).symm
            _ ≤ τ := (pmono (by omega)).trans hτ
        have h3 : τ ≤ c * τ := Nat.le_mul_of_pos_left _ hc1
        omega
      calc (t₁ + v ^ 63 * Λ * (t₂ + 62 * P₂ + 110) + 100) * v ^ 48
          = t₁ * v ^ 48 + v ^ 63 * Λ * t₂ * v ^ 48 + v ^ 63 * Λ * (62 * P₂) * v ^ 48 +
            (v ^ 63 * Λ * 110 * v ^ 48 + 100 * v ^ 48) := by ring
        _ ≤ 2 * c * τ * Λ + c * τ * (4 * (Λ ^ 2 * Y)) + c * τ * (Λ ^ 2 * Y) + c * τ * 2 :=
          Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ht₁ b2) b3) b4
        _ = c * τ * (2 * Λ + 5 * (Λ ^ 2 * Y) + 2) := by ring
        _ ≤ c * τ * (Y * X) := Nat.mul_le_mul_left _ (by omega)
    · -- the sizes
      calc 4 * c * v ^ H * Y = c * v ^ H * (4 * Y) := by ring
        _ ≤ c * v ^ H * (Y * X) := Nat.mul_le_mul_left _
            (Nat.mul_comm 4 Y ▸ Nat.mul_le_mul_left Y (by omega))
    · -- the size of the program
      rw [pow_succ' 4 r, Nat.mul_assoc]
      have h1 := size_cutComp G₁ G₂
      have h2 : v ^ a₀ + 3000 ≤ 4 ^ r * (v ^ a₀ + 3000) :=
        Nat.le_mul_of_pos_left _ (Nat.pow_pos (by norm_num))
      omega

/-- **The cut at a scale, given one cut** (the conditional step of the proof of
[AnthropicVPVNP2026], Theorem J.4): when `α + 1` cuts lose at most `v`, plain sums of
`v ^ H ≤ τ ≤ v ^ α` steps on instances of size `s ≤ τ / v ^ 48` are cut into at most
`τ * v ^ 2 / v ^ H` pieces of `v ^ H` steps and size `v ^ (H - 32)`, in `τ / v ^ 24` steps, by a
program of size at most `v ^ H`. -/
theorem exists_isCut (hc : OneCutAt θ v a₀ α Λ) (hv : 110 ≤ v) (hΛ : 2 ≤ Λ)
    (hloss : (8 * Λ ^ 2) ^ (α + 1) ≤ v) (hH : a₀ + 4 ≤ H) (hH' : 200 ≤ H) {τ s : ℕ}
    (hτ : v ^ H ≤ τ) (hτα : τ ≤ v ^ α) (hs : s * v ^ 48 ≤ τ) :
    ∃ G : Tree, G.size ≤ v ^ H ∧
      IsCut θ τ s (v ^ H) (v ^ (H - 32)) (τ * v ^ 2 / v ^ H) (τ / v ^ 24) G := by
  have hv1 : 1 ≤ v := by omega
  have ppos : ∀ a, 0 < v ^ a := fun a => Nat.pow_pos hv1
  have pmono : ∀ {a b}, a ≤ b → v ^ a ≤ v ^ b := fun h => Nat.pow_le_pow_right hv1 h
  have hΛsq : Λ ≤ Λ ^ 2 := Nat.le_self_pow (by norm_num) Λ
  have hXv : 8 * Λ ^ 2 ≤ v := (Nat.le_self_pow (Nat.succ_ne_zero α) _).trans hloss
  have h4 : 4 ^ (α + 1) ≤ v := (Nat.pow_le_pow_left (by omega) _).trans hloss
  obtain ⟨G, P, t, s', hcut, hP, ht, hs', hG⟩ := hc.exists_isCut_iterate hv hΛ (by omega)
    (by omega) hH' le_rfl α τ s 1 hτ hτα
    (calc τ * Λ < τ * v := Nat.mul_lt_mul_of_pos_left (by omega) ((ppos H).trans_le hτ)
      _ ≤ v ^ α * v := Nat.mul_le_mul_right _ hτα
      _ = v ^ (α + 1) := (pow_succ v α).symm
      _ ≤ v ^ (H + (64 + 62 * α)) := pmono (by omega)
      _ = v ^ H * v ^ (64 + 62 * α) := pow_add _ _ _)
    (by simpa using hs) le_rfl (by simpa using h4)
  rw [Nat.one_mul] at ht hs'
  refine ⟨G, ?_, hcut.mono le_rfl (Nat.le_of_mul_le_mul_right ?_ (ppos 48))
    ((Nat.le_div_iff_mul_le (ppos H)).2 ?_) ((Nat.le_div_iff_mul_le (ppos 24)).2
      (Nat.le_of_mul_le_mul_right ?_ (ppos 24)))⟩
  · have h4α : 4 ^ α ≤ v := (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ α)).trans h4
    calc G.size ≤ 4 ^ α * (v ^ a₀ + 3000) := hG
      _ ≤ v * (v ^ (a₀ + 2) + v ^ (a₀ + 2)) := Nat.mul_le_mul h4α (Nat.add_le_add
          (pmono (by omega)) ((by norm_num : 3000 ≤ 110 ^ 2).trans
            ((Nat.pow_le_pow_left hv 2).trans (pmono (Nat.le_add_left 2 a₀)))))
      _ = 2 * v ^ (a₀ + 3) := by ring
      _ ≤ v * v ^ (a₀ + 3) := Nat.mul_le_mul_right _ (by omega)
      _ = v ^ (a₀ + 4) := (pow_succ' v (a₀ + 3)).symm
      _ ≤ v ^ H := pmono hH
  · calc s' * v ^ 48 ≤ v ^ H * v := hs'.trans (Nat.mul_le_mul_left _ hloss)
      _ = v ^ (H + 1) := (pow_succ v H).symm
      _ ≤ v ^ (H - 32 + 48) := pmono (by omega)
      _ = v ^ (H - 32) * v ^ 48 := pow_add _ _ _
  · exact hP.trans (Nat.mul_le_mul_left _ (hloss.trans (Nat.le_self_pow (by norm_num) v)))
  · calc t * v ^ 24 * v ^ 24 = t * v ^ 48 := by rw [Nat.mul_assoc, ← pow_add]
      _ ≤ τ * v ^ 24 := ht.trans (Nat.mul_le_mul_left _
          (hloss.trans (Nat.le_self_pow (by norm_num) v)))

end OneCutAt

end Cslib.Circuits.Arithmetic.Separation.Cut

/-! ### Powers of the logarithm -/

namespace Cslib.Circuits.Arithmetic.Separation.Interpreter

/-- Powers of the logarithm that are at most `v` bound the exponent by the logarithm. -/
theorem le_lg_of_lg_pow_le {v k : ℕ} (hv : 4 ≤ v) (hk : lg v ^ k ≤ v) : k ≤ lg v :=
  ((Nat.pow_lt_pow_iff_right (by norm_num)).1 (lt_of_le_of_lt
    ((Nat.pow_le_pow_left (lg_ge_two hv) k).trans hk) (lt_two_pow_lg v))).le

/-- The iterated cuts with the loss `(lg v) ^ (C + 1)` lose at most `v`, if
`(lg v) ^ (C₀ * α) ≤ v` for the constant `C₀ = (3 * C + 4) * (32 * h + 2)`. -/
theorem polylog_loss_le {h C v α : ℕ} (hl : 100 ≤ lg v) (hα : 1 ≤ α)
    (hlog : lg v ^ ((3 * C + 4) * (32 * h + 2) * α) ≤ v) :
    (100 * (lg v ^ (C + 1)) ^ 3) ^ (16 * h * α + 1) ≤ v :=
  calc (100 * (lg v ^ (C + 1)) ^ 3) ^ (16 * h * α + 1)
      ≤ (lg v * (lg v ^ (C + 1)) ^ 3) ^ (16 * h * α + 1) :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hl) _
    _ = lg v ^ ((3 * C + 4) * (16 * h * α + 1)) := by
        rw [← pow_mul (lg v) (C + 1) 3, ← pow_succ', ← pow_mul]
        congr 1
        ring
    _ ≤ lg v ^ ((3 * C + 4) * (32 * h + 2) * α) := Nat.pow_le_pow_right (by omega) (by
        rw [Nat.mul_assoc (3 * C + 4) (32 * h + 2)]
        refine Nat.mul_le_mul_left _ ?_
        have : (32 * h + 2) * α = 16 * h * α + 16 * h * α + 2 * α := by ring
        omega)
    _ ≤ v := hlog

end Cslib.Circuits.Arithmetic.Separation.Interpreter
