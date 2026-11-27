/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BQP.Time
public import CslibFrontier.Computability.Complexity.Classes.PP
import CslibFrontier.Computability.Circuit.Quantum.RandomTag
import CslibFrontier.Computability.Complexity.Classes.BQP.Nondeterministic
import CslibFrontier.Computability.Complexity.Classes.PP.SignWeights
import CslibFrontier.Computability.Complexity.Classes.BQP.Counting
import CslibFrontier.Computability.Complexity.Classes.PP.Characterization

/-!
# Postselected quantum polynomial time

`PostBQP` is the polynomial-time union of the native postselected circuit classes, over Hadamard,
NOT, CNOT and Toffoli. The postselection bit is required to be one with positive probability on
every encoded instance. Conditional on this outcome, the decision bit has completeness `2/3` and
soundness `1/3`. These are [Aaronson][Aaronson2005Postselection], Definition 1, with the decision
bit on wire zero and the postselection bit on wire one.

The upper bound `PostBQP_subset_PP` is the inclusion proved in Aaronson's Proposition 2. Both
probabilities in the conditional decision have the same dyadic denominator. Twice the numerator
of the joint event minus that of the postselection event is a GapP function, positive on exactly
the yes-instances.

The reverse inclusion uses two GapP weights obtained from Newman's polynomial. On a uniformly
chosen tag bit the circuit accepts with probability proportional to the square of the corresponding
weight. The weight on the correct tag is at least twice the magnitude of the other. Squaring
gives the required conditional decision bounds and proves Theorem 4 for the native gate set.

## Main definitions

* `PostBQP` consists of languages decided in postselected quantum polynomial time.

## Main results

* `PostBQP_eq_PP` identifies bounded-error postselected quantum computation with strict majority.

## References

* [S. Aaronson, *Quantum Computing, Postselection, and Probabilistic Polynomial-Time*]
  [Aaronson2005Postselection]
-/

@[expose] public section

namespace Cslib.Complexity

open Quantum Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- Bounded-error postselected uniform quantum polynomial time on inputs encoded by `enc`.
Qubit one must have positive probability of reading one on every instance. -/
def PostBQP (enc : α ↪ List Bool) : Set (Set α) :=
  ⋃ k : ℕ, PostBQTIME enc (· ^ k)

/-- **PostBQP ⊆ PP** [Aaronson][Aaronson2005Postselection], Proposition 2, for the native uniform
gate set. The positivity of the postselection probability makes the comparison of projected gaps
strict on yes-instances. -/
theorem PostBQP_subset_PP : PostBQP enc ⊆ PP enc := by
  intro A hA
  obtain ⟨k, F, _, _, _, hF⟩ := Set.mem_iUnion.mp hA
  let gap (S : List ℕ) (a : α) := onesGap S (F.gates (enc a).length)
    (List.ofFn (inputState (F.width (enc a).length) (enc a)))
  have hg (S : List ℕ) : gap S ∈ GapP enc := onesGap_mem_GapP F S
  refine mem_PP_iff_exists_GapP.mpr ⟨_, GapP.sub_mem' (GapP.add_mem (hg [0, 1]) (hg [0, 1]))
    (hg [1]), fun a => ?_⟩
  change a ∈ A ↔ 0 < gap [0, 1] a + gap [0, 1] a - gap [1] a
  let d : ℝ := 2 ^ hadamardCount (F.gates (enc a).length)
  have hd : 0 < d := by dsimp [d]; positivity
  have heq (S : List ℕ) : F.onesProb S (enc a) = (gap S a : ℝ) / d :=
    onesProb_eq_onesGap _ (F.wellFormed _) S _
  obtain ⟨hpos, hyes, hno⟩ := hF a
  rw [heq] at hpos
  have hden := (div_pos_iff_of_pos_right hd).mp hpos
  have hp : F.postselectedAcceptProb (enc a) = (gap [0, 1] a : ℝ) / gap [1] a := by
    rw [UniformCircuitFamily.postselectedAcceptProb, heq, heq, div_div_div_cancel_right₀ hd.ne']
  constructor
  · intro ha
    have := (le_div_iff₀ hden).mp (hp ▸ hyes ha)
    exact_mod_cast (by linarith : (0 : ℝ) < gap [0, 1] a + gap [0, 1] a - gap [1] a)
  · contrapose!
    intro ha
    have := (div_le_iff₀ hden).mp (hp ▸ hno ha)
    exact_mod_cast (by linarith : (gap [0, 1] a : ℝ) + gap [0, 1] a - gap [1] a ≤ 0)

private theorem two_mul_sq_le {a b : ℤ} (h : 2 * |a| ≤ b) : 2 * (a : ℝ) ^ 2 ≤ (b : ℝ) ^ 2 := by
  have hab : (2 : ℝ) * |(a : ℝ)| ≤ (b : ℝ) := by exact_mod_cast h
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * |(a : ℝ)|) hab 2
  rw [mul_pow, sq_abs] at hs
  nlinarith [sq_nonneg (a : ℝ)]

/-- **PostBQP = PP** [Aaronson][Aaronson2005Postselection], Theorem 4. The classes use native
polynomial-time uniform circuits with Hadamard and classical reversible gates, and strict
majority for PP. -/
theorem PostBQP_eq_PP : PostBQP enc = PP enc := by
  apply Set.Subset.antisymm PostBQP_subset_PP
  intro A hA
  obtain ⟨g, hg, hsep⟩ := exists_gapP_separation_of_mem_PP hA
  obtain ⟨F, p, hF⟩ := exists_uniformCircuitFamily_acceptProb_sq_of_mem_GapP hg
  obtain ⟨k, c₁, c₂, hsize⟩ := F.randomTag.exists_polynomial_gate_bound
  refine Set.mem_iUnion.mpr ⟨k, F.randomTag, c₁, c₂, hsize, fun a => ?_⟩
  let y : ℝ := (g (.inr a) : ℝ) ^ 2
  let n : ℝ := (g (.inl a) : ℝ) ^ 2
  let d : ℝ := (2 ^ p.eval ((enc a).length + 1)) ^ 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hyes : F.acceptProb (true :: enc a) = y / d := by
    simpa [y, d, div_pow] using hF (.inr a)
  have hno : F.acceptProb (false :: enc a) = n / d := by
    simpa [n, d, div_pow] using hF (.inl a)
  have hp : F.randomTag.onesProb [1] (enc a) = (y + n) / d / 2 := by
    rw [UniformCircuitFamily.onesProb_randomTag, hyes, hno, ← add_div]
  have ht : 0 < y + n := by
    rcases em (a ∈ A) with ha | ha
    · have hy : 0 < (g (.inr a) : ℝ) := by exact_mod_cast ((hsep a).1 ha).1
      dsimp [y, n]
      positivity
    · have hn : 0 < (g (.inl a) : ℝ) := by exact_mod_cast ((hsep a).2 ha).1
      dsimp [y, n]
      positivity
  have hcond : F.randomTag.postselectedAcceptProb (enc a) = y / (y + n) := by
    rw [UniformCircuitFamily.postselectedAcceptProb, UniformCircuitFamily.jointProb_randomTag,
      hyes, hp, div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0),
      div_div_div_cancel_right₀ hd.ne']
  rw [hp, hcond]
  refine ⟨by positivity, fun ha => (le_div_iff₀ ht).mpr ?_, fun ha => (div_le_iff₀ ht).mpr ?_⟩
  · have h : 2 * n ≤ y := two_mul_sq_le ((hsep a).1 ha).2
    linarith
  · have h : 2 * y ≤ n := two_mul_sq_le ((hsep a).2 ha).2
    linarith

end Cslib.Complexity
