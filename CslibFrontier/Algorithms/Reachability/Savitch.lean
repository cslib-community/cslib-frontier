/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Enumeration
public import CslibFrontier.Foundations.Relation.RelatesWithinSteps

/-!
# Savitch's midpoint reachability

Savitch's theorem rests on the midpoint recursion: `v` is reachable from `u` within `2 ^ (i + 1)`
steps exactly when some midpoint is reachable from `u` and reaches `v` within `2 ^ i` steps each
(`Relation.RelatesWithinSteps.two_pow_succ_iff`). On the words of a fixed width `w`,
`Cslib.Reachability.reach` is this recursion, with the midpoints enumerated by
`Cslib.BitString.enumList`, and it decides walks of at most `2 ^ i` steps along the edges of an
edge test (`Cslib.Reachability.reach_iff`).

Its space on multi-tape machines, `O((d + 1) * (w + log₂ d + 1))` plus one edge test, is
`Turing.MultiTapeTM.ComputableInSpace.reach`, and in polynomial space
`Turing.MultiTapeTM.ComputableInPolySpace.reach`.

## Main definitions

* `Cslib.Reachability.reach`: the midpoint recursion.

## Main results

* `Cslib.Reachability.reach_iff`: the recursion decides walks of at most `2 ^ i` steps.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.5][Sipser2013]
* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Section 4.2][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Reachability

open Cslib.BitString (enumList mem_enumList)

/-! ### Reachability by midpoints -/

/-- **Reachability within `2 ^ i` steps, by midpoints.** At level `0`, `v` is `u` or one edge
away; at level `i + 1`, some word `m` of width `w` is reachable from `u` and reaches `v` at level
`i`. This is the recursion of Savitch's theorem [Sipser, Theorem 8.5][Sipser2013]. -/
def reach (edge : List Bool → List Bool → Bool) (w : ℕ) : ℕ → List Bool → List Bool → Bool
  | 0, u, v => decide (u = v) || edge u v
  | i + 1, u, v => (enumList w).any fun m => reach edge w i u m && reach edge w i m v

/-- A walk along edges between words of width `w` stays among the words of width `w`. -/
private theorem length_eq_of_relatesWithinSteps {edge : List Bool → List Bool → Bool} {w n : ℕ}
    {u v : List Bool} (hu : u.length = w)
    (h : Relation.RelatesWithinSteps (fun a b => a.length = w ∧ b.length = w ∧ edge a b = true)
      u v n) : v.length = w := by
  induction h.reflTransGen with
  | refl => exact hu
  | tail _ hstep _ => exact hstep.2.1

/-- **The midpoint recursion decides walks of at most `2 ^ i` steps** between words of width `w`,
along the edges given by `edge` [Sipser, Theorem 8.5][Sipser2013]. -/
theorem reach_iff {edge : List Bool → List Bool → Bool} {w i : ℕ} {u v : List Bool}
    (hu : u.length = w) (hv : v.length = w) :
    reach edge w i u v = true ↔
      Relation.RelatesWithinSteps (fun a b => a.length = w ∧ b.length = w ∧ edge a b = true)
        u v (2 ^ i) := by
  induction i generalizing u v with
  | zero =>
    rw [pow_zero, Relation.RelatesWithinSteps.one_iff, Relation.reflGen_iff]
    simp only [reach, Bool.or_eq_true, decide_eq_true_eq, hu, hv, true_and]
    exact or_congr eq_comm Iff.rfl
  | succ i ih =>
    rw [Relation.RelatesWithinSteps.two_pow_succ_iff]
    simp only [reach, List.any_eq_true, Bool.and_eq_true, mem_enumList]
    constructor
    · rintro ⟨m, hm, h₁, h₂⟩
      exact ⟨m, (ih hu hm).mp h₁, (ih hm hv).mp h₂⟩
    · rintro ⟨m, h₁, h₂⟩
      have hm := length_eq_of_relatesWithinSteps hu h₁
      exact ⟨m, hm, (ih hu hm).mpr h₁, (ih hm hv).mpr h₂⟩

end Cslib.Reachability
