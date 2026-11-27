/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Metric
import CslibFrontier.Foundations.Data.BitString.Hamming

/-!
# Hamming-far functions that share their computation

Two distinct coordinate projections `x_i` and `x_j` differ on half of the inputs, and so do their
shifts `g_i = f + x_i` and `g_j = f + x_j` by any common Boolean function `f`
(`Cslib.BitString.two_mul_hammingDist_add_proj`). Statistically the shifts are as far apart as
two independent random functions, yet they share almost all of their computation. In the De
Morgan basis, where an exclusive or costs four gates:

* each shift costs at most four gates more than `f`
  (`Cslib.Circuits.Boolean.complexity_add_proj_le`);
* all `m` shifts `x ↦ f x + x_{i o}` together cost at most `C(f) + 4 m`: compute `f` once, then
  one exclusive or per output (`Cslib.Circuits.Boolean.complexity_add_projs_le`);
* the computational Hamming distance of two shifts is that of the two projections
  (`Cslib.Circuits.Boolean.circuitDist_add_proj`), which lies between five and eight for distinct
  projections (`Cslib.Circuits.Boolean.five_le_circuitDist_proj`,
  `Cslib.Circuits.Boolean.circuitDist_proj_le`).

Statistical disagreement therefore does not certify computational independence, while the
computational distance `Cslib.Circuits.Boolean.circuitDist` sees the shared part. Pairwise
computational distance alone still says nothing about direct sums.

## Main results

* `Cslib.Circuits.Boolean.complexity_add_proj_le`: one shift costs at most four more gates.
* `Cslib.Circuits.Boolean.complexity_add_projs_le`: `m` shifts cost at most `C(f) + 4 m`.
* `Cslib.Circuits.Boolean.circuitDist_add_proj`, `Cslib.Circuits.Boolean.circuitDist_proj_le`,
  `Cslib.Circuits.Boolean.five_le_circuitDist_proj`: shifts are at computational distance between
  five and eight.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

public section

namespace Cslib.Circuits.Boolean

variable {n : ℕ}

/-- Adding a coordinate to `f` costs at most four gates more than `f`. -/
theorem complexity_add_proj_le (f : BooleanFunction n) (i : Fin n) :
    complexity interpretation (single (f + fun x => x i)) ≤
      complexity interpretation (single f) + 4 := by
  have h := complexity_xor_le f fun x => x i
  rwa [complexity_single_proj] at h

/-- **Joint complexity of shifts.** The `m` functions `x ↦ f x + x_{i o}` together cost at most
four gates each more than `f`: compute `f` once beside the inputs, then one exclusive or per
output. -/
theorem complexity_add_projs_le {m : ℕ} (f : BooleanFunction n) (i : Fin m → Fin n) :
    complexity interpretation (fun x o => f x + x (i o)) ≤
      complexity interpretation (single f) + 4 * m := by
  -- `F` computes `f` beside the inputs, `G` adds the value of `f` to the selected inputs
  let F : BitString n → Fin (1 + n) → Bool := fun x => Fin.append (single f x) x
  have hF : complexity interpretation F ≤ complexity interpretation (single f) := by
    have h := complexity_append_le (I := interpretation) (single f) fun x : BitString n => x
    have hid : complexity interpretation (fun x : BitString n => x) = 0 := complexity_wiring id
    rwa [hid, add_zero] at h
  let G : (Fin (1 + n) → Bool) → Fin m → Bool :=
    fun y o => y (Fin.castAdd n 0) ^^ y (Fin.natAdd 1 (i o))
  have hG : complexity interpretation G ≤ 4 * m := by
    have hsyn : Synthesis interpretation (inputs (1 + n)) (Set.range fun o y => G y o)
        (∑ _ : Fin m, (0 + 0 + 4)) :=
      Synthesis.family _ _ fun o =>
        (Synthesis.of_mem (s := inputs (1 + n)) (f := fun y => y (Fin.castAdd n 0))
          ⟨Fin.castAdd n 0, rfl⟩).xor
        (Synthesis.of_mem (s := inputs (1 + n)) (f := fun y => y (Fin.natAdd 1 (i o)))
          ⟨Fin.natAdd 1 (i o), rfl⟩)
    obtain ⟨c, hc, hsize⟩ := hsyn.exists_circuit_outputs
    exact (complexity_le_of_computes c hc).trans (hsize.trans (by simp [mul_comm]))
  have heq : (fun x o => f x + x (i o)) = G ∘ F :=
    funext₂ fun _ _ => by simp [F, G, Bool.add_eq_xor]
  rw [heq]
  exact (complexity_comp_le (I := interpretation) F G).trans (Nat.add_le_add hF hG)

/-- Shifting two projections by the same `f` keeps their computational Hamming distance. -/
theorem circuitDist_add_proj (f : BooleanFunction n) (i j : Fin n) :
    circuitDist (f + fun x => x i) (f + fun x => x j) =
      circuitDist (fun x : BitString n => x i) fun x => x j :=
  circuitDist_add_left f _ _

/-- Two coordinate projections are at computational Hamming distance at most eight. -/
theorem circuitDist_proj_le (i j : Fin n) :
    circuitDist (fun x : BitString n => x i) (fun x => x j) ≤ 8 := by
  by_cases hij : (fun x : BitString n => x i) = fun x => x j
  · simp [hij]
  rw [circuitDist_of_ne hij]
  have h := complexity_xor_le (fun x : BitString n => x i) fun x => x j
  rw [complexity_single_proj, complexity_single_proj] at h; omega

/-- Two distinct coordinate projections are at computational Hamming distance at least five:
their exclusive or is not a projection. -/
theorem five_le_circuitDist_proj {i j : Fin n} (hij : i ≠ j) :
    5 ≤ circuitDist (fun x : BitString n => x i) (fun x => x j) := by
  rw [circuitDist_of_ne fun h => by
    simpa [Function.update_of_ne hij.symm] using
      congrFun h (Function.update (fun _ => false) i true)]
  have := one_le_complexity_single (I := interpretation) (f := fun x => x i ^^ x j) fun _ h => by
    simpa using congrFun h fun _ => true
  omega

end Cslib.Circuits.Boolean
