/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.Inversion
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.StateCount

/-!
# The states of given size and energy, as words

The index sets of Proposition B.2 (prop:identity) of *VP ≠ VNP over every field*
[AnthropicVPVNP2026]: the states of size `μ` and energy `e` (`states`), and the word of a state
(`word`), which is injective and keeps the energy.

## Main definitions

* `states`, `word`.

## Main results

* `word_injective`, `wordEnergy_word`, `wordEnergy_swap`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition B.2 of the paper; module `Nc.Cross.Ident`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Curvature

open Finset

/-- The states of size `μ` and energy `e`. -/
def states (μ e : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  (lowStates e).filter fun s => s.1.card = μ ∧ s.2.card = μ ∧ energy s.1 + energy s.2 = e

@[simp] theorem mem_states {μ e : ℕ} {s : Finset ℕ × Finset ℕ} :
    s ∈ states μ e ↔
      s ∈ lowStates e ∧ s.1.card = μ ∧ s.2.card = μ ∧ energy s.1 + energy s.2 = e :=
  mem_filter

section word

variable {μ e : ℕ}

theorem states_prop (s : ↥(states μ e)) :
    s.val.1.card = μ ∧ s.val.2.card = μ ∧ energy s.val.1 + energy s.val.2 = e :=
        (mem_filter.1 s.property).2

theorem card_fst_of_mem_states (s : ↥(states μ e)) : s.val.1.card = μ := (states_prop s).1

theorem card_snd_of_mem_states (s : ↥(states μ e)) : s.val.2.card = μ := (states_prop s).2.1

/-- The word of a state. -/
def word (s : ↥(states μ e)) : Word μ :=
  ⟨s.val.1.orderEmbOfFin (card_fst_of_mem_states s),
    s.val.2.orderEmbOfFin (card_snd_of_mem_states s)⟩

theorem word_strictMono (s : ↥(states μ e)) : StrictMono (word s).row ∧ StrictMono (word s).col :=
  ⟨(s.val.1.orderEmbOfFin (states_prop s).1).strictMono,
      (s.val.2.orderEmbOfFin (states_prop s).2.1).strictMono⟩

theorem word_injective : Function.Injective (word : ↥(states μ e) → Word μ) := by
  intro s s' h
  have h1 : ((s.val.1 : Finset ℕ) : Set ℕ) = s'.val.1 := by
    rw [← Finset.range_orderEmbOfFin _ (states_prop s).1,
        ← Finset.range_orderEmbOfFin _ (states_prop s').1]
    exact congrArg Set.range (congrArg Word.row h)
  have h2 : ((s.val.2 : Finset ℕ) : Set ℕ) = s'.val.2 := by
    rw [← Finset.range_orderEmbOfFin _ (states_prop s).2.1,
        ← Finset.range_orderEmbOfFin _ (states_prop s').2.1]
    exact congrArg Set.range (congrArg Word.col h)
  exact Subtype.ext (Prod.ext (Finset.coe_injective h1) (Finset.coe_injective h2))

private theorem sum_orderEmb (S : Finset ℕ) {k : ℕ} (h : S.card = k) :
    ∑ i, (2 * S.orderEmbOfFin h i + 1) = energy S := by
  conv_rhs => rw [energy, ← Finset.map_orderEmbOfFin_univ S h, Finset.sum_map]
  rfl

theorem wordEnergy_word (s : ↥(states μ e)) : wordEnergy (word s) = e := by
  rw [wordEnergy, word, sum_orderEmb, sum_orderEmb]
  exact (states_prop s).2.2

theorem wordEnergy_swap (w : Word μ) : wordEnergy w.swap = wordEnergy w := by
  rw [wordEnergy, wordEnergy, add_comm]
  rfl

end word

end Cslib.Circuits.Arithmetic.Separation.Curvature
