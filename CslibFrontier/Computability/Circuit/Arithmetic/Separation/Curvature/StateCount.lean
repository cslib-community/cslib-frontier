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
  simp only [interleave, mem_biUnion, mem_univ, true_and, mem_image]
  refine ⟨fun ⟨r', i', hi', h⟩ => ?_, fun h => ⟨r, i, h, rfl⟩⟩
  have hr' : r = r' := Fin.ext <| by
    simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt r.2, Nat.mod_eq_of_lt r'.2] using
      (congrArg (· % k) h).symm
  subst hr'
  exact Nat.eq_of_mul_eq_mul_left r.pos (Nat.add_right_cancel h) ▸ hi'

theorem interleave_injective {k : ℕ} : Function.Injective (interleave k) := fun I I' h => by
  funext r
  ext i
  rw [← mem_interleave I r i, h, mem_interleave]

theorem sum_interleave {k : ℕ} (I : Fin k → Finset ℕ) (f : ℕ → ℕ) :
    ∑ n ∈ interleave k I, f n = ∑ r, ∑ i ∈ I r, f (k * i + r) := by
  rw [interleave, Finset.sum_biUnion]
  · exact Finset.sum_congr rfl fun r _ => Finset.sum_image fun i _ j _ hij =>
      Nat.eq_of_mul_eq_mul_left r.pos (by simpa using hij)
  · intro r _ r' _ hrr'
    rw [Function.onFun, Finset.disjoint_left]
    rintro _ hr hr'
    obtain ⟨i, -, rfl⟩ := mem_image.1 hr
    obtain ⟨i', -, h⟩ := mem_image.1 hr'
    exact hrr' <| Fin.ext <| by
      simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt r.2, Nat.mod_eq_of_lt r'.2] using
        (congrArg (· % k) h).symm

theorem card_interleave {k : ℕ} (I : Fin k → Finset ℕ) : (interleave k I).card = ∑ r,
    (I r).card := by
  simpa using sum_interleave I fun _ => 1

theorem energy_interleave {k : ℕ} (s : Fin k → Finset ℕ × Finset ℕ)
    (h : ∀ r, (s r).1.card = (s r).2.card) :
    energy (interleave k fun r => (s r).1) + energy (interleave k fun r => (s r.rev).2) =
      k * ∑ r, (energy (s r).1 + energy (s r).2) := by
  have e1 : energy (interleave k fun r => (s r.rev).2) = ∑ r : Fin k, ∑ i ∈ (s r).2,
      (2 * (k * i + (r.rev : Fin k)) + 1) := by
    rw [energy, sum_interleave]
    exact Fintype.sum_equiv Fin.revPerm _ _ fun _ => by simp
  have ha (S : Finset ℕ) (m : ℕ) :
      ∑ i ∈ S, (2 * (k * i + m) + 1) = k * ∑ i ∈ S, 2 * i + S.card * (2 * m + 1) := by
    rw [Finset.mul_sum, Finset.card_eq_sum_ones, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e1, energy, sum_interleave, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hr : (2 * (r : ℕ) + 1) + (2 * ((r.rev : Fin k) : ℕ) + 1) = 2 * k := by
    rw [Fin.val_rev]; omega
  rw [ha, ha, energy, energy, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.sum_const, smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← h r]
  calc k * ∑ i ∈ (s r).1, 2 * i + (s r).1.card * (2 * ↑r + 1) +
        (k * ∑ i ∈ (s r).2, 2 * i + (s r).1.card * (2 * ((r.rev : Fin k) : ℕ) + 1))
      = k * ∑ i ∈ (s r).1, 2 * i + k * ∑ i ∈ (s r).2, 2 * i +
        (s r).1.card * ((2 * ↑r + 1) + (2 * ((r.rev : Fin k) : ℕ) + 1)) := by ring
    _ = _ := by rw [hr]; ring

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
  simp only [lowStates, lowSets, mem_filter, mem_product] at hs ⊢
  exact ⟨⟨hs.1.1, by omega⟩, hs.1.2, by omega⟩

/-- The logarithm of the number of states. -/
@[expose] noncomputable def logLowStates (E : ℕ) : ℝ := Real.log (lowStates E).card

theorem logLowStates_nonneg (E : ℕ) : 0 ≤ logLowStates E := Real.log_natCast_nonneg _

theorem logLowStates_zero : logLowStates 0 = 0 := by
  have hempty {S : Finset ℕ} (h : energy S ≤ 0) : S = ∅ :=
    Finset.eq_empty_iff_forall_notMem.2 fun i hi =>
      absurd (lt_of_mem_of_energy_le (by omega) hi) (by omega)
  suffices lowStates 0 = {(∅, ∅)} by simp [logLowStates, this]
  ext ⟨s₁, s₂⟩
  simp only [mem_lowStates, mem_singleton, Prod.mk.injEq]
  refine ⟨fun ⟨_, h⟩ => ⟨hempty (by omega), hempty (by omega)⟩, ?_⟩
  rintro ⟨rfl, rfl⟩
  simp [energy]

theorem logLowStates_mono {E E' : ℕ} (h : E ≤ E') : logLowStates E ≤ logLowStates E' :=
  Real.log_le_log (by exact_mod_cast lowStates_card_pos E)
      (by exact_mod_cast card_le_card (lowStates_mono h))

end Cslib.Circuits.Arithmetic.Separation.Curvature
