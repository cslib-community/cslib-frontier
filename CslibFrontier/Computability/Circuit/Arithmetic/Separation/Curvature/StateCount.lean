/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.Terms
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The number of states

For Lemma B.1 (lem:count) of *VP ≠ VNP over every field* [AnthropicVPVNP2026]: interleaving `k` sets
along the residues modulo `k` (`interleave`), the sets of bounded energy (`lowSets`), and the
logarithm of the number of states of bounded energy (`logLowStates`).

## Main definitions

* `interleave`, `lowSets`, `logLowStates`.

## Main results

* `interleave_injective`, `sum_interleave`, `card_interleave`, `energy_interleave`,
  `card_lowStates_le`, `logLowStates_zero`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Lemma B.1 of the paper; module `Nc.Cross.Count`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Curvature

open Finset

/-- Glue `k` sets along the residues modulo `k`. -/
def interleave (k : ℕ) (I : Fin k → Finset ℕ) : Finset ℕ :=
  univ.biUnion fun r => (I r).image fun i => k * i + r

theorem mem_interleave {k : ℕ} (I : Fin k → Finset ℕ) (r : Fin k) (i : ℕ) :
    k * i + r ∈ interleave k I ↔ i ∈ I r := by
  have hk : 0 < k := r.pos
  unfold interleave
  simp only [mem_biUnion, mem_univ, true_and, mem_image]
  refine ⟨?_, fun h => ⟨r, i, h, rfl⟩⟩
  rintro ⟨r', i', hi', h⟩
  have h1 : (r' : ℕ) = r := by
    have := congrArg (· % k) h
    simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt r.2, Nat.mod_eq_of_lt r'.2] using this
  have h2 : r' = r := Fin.ext h1
  subst h2
  have h3 : i' = i := Nat.eq_of_mul_eq_mul_left hk (by omega)
  exact h3 ▸ hi'

theorem interleave_injective {k : ℕ} : Function.Injective (interleave k) := by
  intro I I' h
  funext r
  ext i
  rw [← mem_interleave I r i, h, mem_interleave]

theorem sum_interleave {k : ℕ} (I : Fin k → Finset ℕ) (f : ℕ → ℕ) :
    ∑ n ∈ interleave k I, f n = ∑ r, ∑ i ∈ I r, f (k * i + r) := by
  unfold interleave
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_image]
    intro i _ j _ hij
    exact Nat.eq_of_mul_eq_mul_left r.pos (by simpa using hij)
  · intro r _ r' _ hrr'
    rw [Function.onFun, Finset.disjoint_left]
    intro n hn hn'
    obtain ⟨i, -, rfl⟩ := mem_image.1 hn
    obtain ⟨i', -, h⟩ := mem_image.1 hn'
    apply hrr'
    have := congrArg (· % k) h
    refine Fin.ext ?_
    simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt r.2, Nat.mod_eq_of_lt r'.2] using this.symm

theorem card_interleave {k : ℕ} (I : Fin k → Finset ℕ) : (interleave k I).card = ∑ r,
    (I r).card := by
  have := sum_interleave I fun _ => 1
  simpa using this

theorem energy_interleave {k : ℕ} (s : Fin k → Finset ℕ × Finset ℕ)
    (h : ∀ r, (s r).1.card = (s r).2.card) :
    energy (interleave k fun r => (s r).1) + energy (interleave k fun r => (s r.rev).2) =
      k * ∑ r, (energy (s r).1 + energy (s r).2) := by
  have e1 : energy (interleave k fun r => (s r.rev).2) = ∑ r : Fin k, ∑ i ∈ (s r).2,
      (2 * (k * i + (r.rev : Fin k)) + 1) := by
    rw [energy, sum_interleave]
    refine Fintype.sum_equiv Fin.revPerm _ _ fun r => ?_
    simp
  rw [e1, energy, sum_interleave, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hr : ((r.rev : Fin k) : ℕ) + r + 1 = k := by
    rw [Fin.val_rev]
    omega
  have a1 : ∑ i ∈ (s r).1, (2 * (k * i + r) + 1) = k * ∑ i ∈ (s r).1,
      2 * i + (s r).1.card * (2 * r + 1) := by
    rw [Finset.mul_sum, Finset.card_eq_sum_ones, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have a2 : ∑ i ∈ (s r).2, (2 * (k * i + (r.rev : Fin k)) + 1) =
      k * ∑ i ∈ (s r).2, 2 * i + (s r).2.card * (2 * (r.rev : Fin k) + 1) := by
    rw [Finset.mul_sum, Finset.card_eq_sum_ones, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have a3 : ∀ S : Finset ℕ, energy S = ∑ i ∈ S, 2 * i + S.card := by
    intro S
    rw [energy, Finset.sum_add_distrib, Finset.card_eq_sum_ones]
  rw [a1, a2, a3, a3, ← h r]
  have : (2 * (r : ℕ) + 1) + (2 * ((r.rev : Fin k) : ℕ) + 1) = 2 * k := by omega
  calc k * ∑ i ∈ (s r).1, 2 * i + (s r).1.card * (2 * ↑r + 1) +
        (k * ∑ i ∈ (s r).2, 2 * i + (s r).1.card * (2 * ((r.rev : Fin k) : ℕ) + 1))
      = k * ∑ i ∈ (s r).1, 2 * i + k * ∑ i ∈ (s r).2, 2 * i +
        (s r).1.card * ((2 * ↑r + 1) + (2 * ((r.rev : Fin k) : ℕ) + 1)) := by ring
    _ = _ := by rw [this]; ring

theorem lowStates_mono {E E' : ℕ} (h : E ≤ E') : lowStates E ⊆ lowStates E' := fun s hs => by
  rw [mem_lowStates] at hs ⊢
  exact ⟨hs.1, hs.2.trans h⟩

theorem lowStates_card_pos (E : ℕ) : 0 < (lowStates E).card :=
  Finset.card_pos.2 ⟨(∅, ∅), mem_lowStates.2 ⟨rfl, by simp [energy]⟩⟩

theorem two_le_card_lowStates : 2 ≤ (lowStates 2).card := by
  have : ({(∅, ∅), ({0}, {0})} : Finset (Finset ℕ × Finset ℕ)) ⊆ lowStates 2 := by
    intro s hs
    rw [mem_insert, mem_singleton] at hs
    rw [mem_lowStates]
    rcases hs with rfl | rfl <;> simp [energy]
  refine le_trans ?_ (card_le_card this)
  rw [card_insert_of_notMem, card_singleton]
  simp

/-- The sets of energy at most `E`. -/
@[expose] def lowSets (E : ℕ) : Finset (Finset ℕ) := (range E).powerset.filter fun S => energy S ≤ E

/-- The states of energy at most `E` are pairs of sets of energy at most `E`. -/
theorem card_lowStates_le (E : ℕ) : (lowStates E).card ≤ (lowSets E).card * (lowSets E).card := by
  rw [← card_product]
  refine card_le_card fun s hs => ?_
  unfold lowStates at hs
  rw [mem_filter, mem_product] at hs
  rw [mem_product, lowSets, mem_filter, mem_filter]
  exact ⟨⟨hs.1.1, by omega⟩, hs.1.2, by omega⟩

/-- The logarithm of the number of states. -/
@[expose] noncomputable def logLowStates (E : ℕ) : ℝ := Real.log (lowStates E).card

theorem logLowStates_nonneg (E : ℕ) : 0 ≤ logLowStates E := Real.log_natCast_nonneg _

theorem logLowStates_zero : logLowStates 0 = 0 := by
  have : lowStates 0 = {(∅, ∅)} := by
    ext s
    rw [mem_lowStates, mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      have h1 : s.1 = ∅ := by
        by_contra hne
        obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hne
        exact absurd (lt_of_mem_of_energy_le (E := 0) (by omega) hi) (by omega)
      have h2 : s.2 = ∅ := by
        by_contra hne
        obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hne
        exact absurd (lt_of_mem_of_energy_le (E := 0) (by omega) hi) (by omega)
      exact Prod.ext h1 h2
    · rintro rfl
      simp [energy]
  rw [logLowStates, this]
  simp

theorem logLowStates_mono {E E' : ℕ} (h : E ≤ E') : logLowStates E ≤ logLowStates E' :=
  Real.log_le_log (by exact_mod_cast lowStates_card_pos E)
      (by exact_mod_cast card_le_card (lowStates_mono h))

end Cslib.Circuits.Arithmetic.Separation.Curvature
