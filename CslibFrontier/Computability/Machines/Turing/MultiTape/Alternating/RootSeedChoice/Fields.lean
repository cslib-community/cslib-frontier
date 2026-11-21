/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.SeedChoice
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Fields

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Existential moves for one valid, shared trinomial seed

The four coefficient fields precede every later player move. Thus the continuation's edge and
rank challenges all see the same seed. The field width is selected uniformly from the universe
and the requested label length.
-/

public section

namespace Turing.MultiTapeATM.RootSeedChoice

open Cslib QuantifiedWord MultiTapeTM MultiTapeTM.ComputableInPolyTime

/-- Four existential coefficient choices, each at the degree of the selected field. -/
@[expose] def seedFlags (U a : ℕ) : List Bool :=
  List.replicate (4 * Probability.trinomialDeg U (6 * a)) false

/-- The physical quantifier prefix can select every genuine seed and no other four coefficients.
The continuation may contain arbitrary further alternation. -/
theorem plays_seedFlags (value : List Bool → Prop) (pre rest : List Bool) (U a : ℕ) :
    plays value pre (seedFlags U a ++ rest) ↔
      ∃ seed : BalancedSchedules.SeededLabels.Seed U (6 * a),
        plays value (pre ++ SeedChoice.word seed) rest := by
  let d := Probability.trinomialDeg U (6 * a)
  let f := List.replicate d false
  have hf : seedFlags U a ++ rest = f ++ (f ++ (f ++ (f ++ rest))) := by
    simp only [seedFlags, f, ← List.append_assoc, ← List.replicate_add]
    congr 2
    omega
  rw [hf]
  simp only [f, plays_exists_field, List.append_assoc]
  constructor
  · rintro ⟨x₀, x₁, x₂, x₃, hx⟩
    exact ⟨![x₀, x₁, x₂, x₃], by simpa [SeedChoice.word, List.append_assoc] using hx⟩
  · rintro ⟨seed, h⟩
    exact ⟨seed 0, seed 1, seed 2, seed 3, by simpa [SeedChoice.word, List.append_assoc] using h⟩

/-- A native machine prepares the coefficient-player flags from the short public hash parameters. -/
theorem computableInPolyTime_seedFlags :
    ComputableInPolyTime
      (fun c : SeededPredecessor.Context => seedFlags c.universeSize c.labelLength)
      SeededPredecessor.encContext encBits :=
  (bitsReplicate false).comp (unary_mul' (const 4) (SeedChoice.computableInPolyTime_width .id'))

end Turing.MultiTapeATM.RootSeedChoice
