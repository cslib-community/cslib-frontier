/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser.Step
public import CslibFrontier.Computability.Circuit.Boolean.SemiCircuit.OfCircuit

/-!
# A `3.5 n - 7 d` lower bound for affine dispersers

**Theorem 4.1** of [Mishra and Santhanam][MishraSanthanam2026]: every circuit over the full
binary basis `B₂` computing an affine disperser for dimension `d` on `n` bits requires at least
`3.5 n - 7 d` genuinely binary `B₂` gates
(`Cslib.Circuits.Boolean.AffineDisperser.seven_mul_le_two_mul_cost_add`), and hence at least
`3.5 n - 7 d` total gates
(`Cslib.Circuits.Boolean.AffineDisperser.seven_mul_le_two_mul_size_add`).
This improves the `3.1 n - o(n)` lower bound of [Li and Yang][LiYang2022], itself improving the
`(3 + 1/86) n - o(n)` bound of [Find, Golovnev, Hirsch and Kulikov][FindGolovnevHirschKulikov2016],
whose fair semi-circuits (`Cslib.Circuits.Boolean.SemiCircuit`) carry the gate elimination.

The proof starts gate elimination from `SemiCircuit.ofCircuitBinary C` (`initialState`), folding
constants and unary projections/negations into literals at zero cost (`binaryB2Cost`): its inputs
are the parameters, its binary gates form the acyclic part, the affine system is empty and the
parameter map is the identity, so `a = n` and `W ≤ 2 · cost(C) + 7 n`. Every valid state satisfies
`14 a ≤ W + 14 d` (`State.Valid.fourteen_mul_a_le`), by induction on `m + s` along the steps of
Lemma 4.2 (`State.Valid.exists_step`), so `14 n ≤ 2 · cost(C) + 7 n + 14 d`.

The development is organised as follows.

* `AffineDisperser.State`: the states of gate elimination, their potential, Proposition 2.2 and
  Lemma 2.3 of the source.
* `AffineDisperser.Operations`, `AffineDisperser.Reparameterisation`: the operations on states
  (restrictions, exchanging a parameter with an auxiliary variable, and the quadratic
  substitution), with validity.
* `AffineDisperser.Reduction`: reductions, which restrict parameters and delete constraints, and
  their accounting, done once for all reductions.
* `AffineDisperser.Deletion`, `AffineDisperser.Normal`: the preliminary reductions of
  Section 4.1.
* `AffineDisperser.MinimalAnd`: restructuring the minimal AND, Section 4.2.
* `AffineDisperser.Elimination`: eliminating the minimal AND, Section 4.3.
* `AffineDisperser.Step`: Lemma 4.2, one step of gate elimination.

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser.initialState`: the initial state of gate elimination.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.fourteen_mul_a_le`: the potential bound.
* `Cslib.Circuits.Boolean.AffineDisperser.seven_mul_le_two_mul_cost_add`,
  `Cslib.Circuits.Boolean.AffineDisperser.seven_mul_le_two_mul_size_add`: Theorem 4.1.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
* [J. Li and T. Yang, *3.1n − o(n) Circuit Lower Bounds for Explicit Functions*][LiYang2022]
* [M. G. Find, A. Golovnev, E. A. Hirsch and A. S. Kulikov, *A better-than-3n lower bound for the
  circuit complexity of an explicit function*][FindGolovnevHirschKulikov2016]
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser

open Cslib.Circuits Cslib.BitString SemiCircuit AffineDisperserCore

variable {n : ℕ} {f : BooleanFunction n}

/-! ### The potential bound -/

/-- Every valid state for an affine disperser for dimension `d` satisfies `14 a ≤ W + 14 d`:
apply Lemma 4.2 until `a ≤ d`, adding up `ΔW ≤ 14 Δa`. -/
theorem State.Valid.fourteen_mul_a_le {d : ℕ} (hf : IsAffineDisperser f d) :
    ∀ S : State n, S.Valid f → 14 * S.a ≤ S.W + 14 * d := by
  intro S
  induction S using (_root_.measure (fun S : State n => S.m + S.s)).wf.induction with
  | h S ih =>
    intro hS
    by_cases ha : S.a ≤ d
    · omega
    · obtain ⟨S', hstep⟩ := State.Valid.exists_step hS hf (lt_of_not_ge ha)
      have := ih S' hstep.lt hstep.valid
      have := hstep.potential
      rw [config_ca] at this
      omega

/-! ### The initial state of a circuit -/

/-- The initial state of gate elimination for a circuit: its binary-gate semi-circuit
(`SemiCircuit.ofCircuitBinary`), whose parameters are the inputs, with no pairs and the parameter
map reading the inputs. -/
def initialState (C : Circuit (fullSignature 2 Bool) n 1) : State n where
  toSemiCircuit := SemiCircuit.ofCircuitBinary C
  pairs := ∅
  phi val := fun i => val i

/-- The initial state of a circuit computing `f` is valid. -/
theorem initialState_valid {C : Circuit (fullSignature 2 Bool) n 1}
    (hC : C.Computes fullInterpretation (single f)) : (initialState C).Valid f where
  wf := wellFormed_ofCircuitBinary C
  pair_mem := fun _ hpr => absurd hpr (Finset.notMem_empty _)
  pairs_disjoint := fun _ hpr => absurd hpr (Finset.notMem_empty _)
  phi_congr := fun val val' h => funext fun i => h i (by
    change ↑i ∈ (ofCircuitBinary C).params
    rw [ofCircuitBinary_params]
    exact Finset.mem_range.2 i.isLt)
  phi_affine := fun _ _ hσ _ u v w => funext fun i => congrFun (hσ u v w) i
  phi_injective := fun val val' h j hj => by
    change j ∈ (ofCircuitBinary C).params at hj
    rw [ofCircuitBinary_params, Finset.mem_range] at hj
    exact congrFun h ⟨j, hj⟩
  computes := fun val hval _ => by
    change (ofCircuitBinary C).out.eval val = f (fun i => val i)
    rw [out_eval_ofCircuitBinary C hval]
    exact congrFun (hC fun i => val i) 0

/-- The initial state of an `n`-input circuit has affine dimension `n`. -/
theorem initialState_a (C : Circuit (fullSignature 2 Bool) n 1) : (initialState C).a = n := by
  change (ofCircuitBinary C).params.card - (∅ : Finset config.Pair).card = n
  rw [ofCircuitBinary_params, Finset.card_range, Finset.card_empty, Nat.sub_zero]

private theorem initialState_W_le (C : Circuit (fullSignature 2 Bool) n 1) :
    (initialState C).W ≤ 2 * C.program.cost binaryB2Cost + 7 * n := by
  have hs : (initialState C).s = C.program.cost binaryB2Cost := size_ofCircuitBinary C
  have hq : (initialState C).q = 0 := Finset.card_empty
  unfold AffineDisperserCore.State.W
  rw [hs, hq, config_cs, config_cq, config_weight]
  have : ∑ x ∈ (initialState C).unpaired, weight ((initialState C).deg x) ≤ 7 * n := by
    calc ∑ x ∈ (initialState C).unpaired, weight ((initialState C).deg x)
        ≤ ∑ _x ∈ (initialState C).unpaired, 7 := Finset.sum_le_sum fun _ _ => weight_le_seven _
      _ = 7 * (initialState C).unpaired.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ 7 * n := by
        have : (initialState C).unpaired.card ≤ n :=
          (Finset.card_filter_le _ _).trans (by
            change (ofCircuitBinary C).params.card ≤ n
            rw [ofCircuitBinary_params, Finset.card_range])
        omega
  omega

/-! ### Theorem 4.1 -/

/-- **Theorem 4.1** of [Mishra and Santhanam][MishraSanthanam2026] on binary `B₂` gate cost: every
circuit over `fullSignature 2 Bool` computing an affine disperser for dimension `d` on `n` bits
satisfies `7 * n ≤ 2 * C.program.cost binaryB2Cost + 14 * d` (constants and negations free). -/
theorem seven_mul_le_two_mul_cost_add {d : ℕ} (hf : IsAffineDisperser f d)
    (C : Circuit (fullSignature 2 Bool) n 1) (hC : C.Computes fullInterpretation (single f)) :
    7 * n ≤ 2 * C.program.cost binaryB2Cost + 14 * d := by
  have h := State.Valid.fourteen_mul_a_le hf _ (initialState_valid hC)
  rw [initialState_a] at h
  have := initialState_W_le C
  omega

/-- **Theorem 4.1** of [Mishra and Santhanam][MishraSanthanam2026]: every circuit over the full
binary basis computing an affine disperser for dimension `d` on `n` bits has at least
`3.5 n - 7 d` gates, stated without subtraction as `7 n ≤ 2 |C| + 14 d`. -/
theorem seven_mul_le_two_mul_size_add {d : ℕ} (hf : IsAffineDisperser f d)
    (C : Circuit (fullSignature 2 Bool) n 1) (hC : C.Computes fullInterpretation (single f)) :
    7 * n ≤ 2 * C.size + 14 * d :=
  (seven_mul_le_two_mul_cost_add hf C hC).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (cost_binaryB2Cost_le_size C)) _)

end Cslib.Circuits.Boolean.AffineDisperser
