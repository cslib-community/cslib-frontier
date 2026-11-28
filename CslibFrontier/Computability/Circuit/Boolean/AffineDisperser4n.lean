/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Step
public import CslibFrontier.Computability.Circuit.Boolean.SemiCircuit.OfCircuit

/-!
# The `4n - 9d` circuit lower bound for affine dispersers

This module proves a tightened `4n - 9d` binary-gate lower bound extending the `4n - 10d`
zero-locus gate-elimination framework of [Mishra and Santhanam][MishraSanthanam2026Revision1],
ECCC TR26-260 revision 1, Theorem 4.1 (p. 21), also recorded in issue `#4322`: any
general Boolean circuit (`fullSignature 2 Bool`) computing a `d`-affine disperser `f` on `n` bits
satisfies `4 * n ≤ C.program.cost binaryB2Cost + 9 * d`
(`Cslib.Circuits.Boolean.AffineDisperser4n.four_mul_le_cost_add`), and hence
`4 * n ≤ C.size + 9 * d` (`Cslib.Circuits.Boolean.AffineDisperser4n.four_mul_le_size_add`).

Two original improvements over `#4322` are combined here:
* `initialState` builds on `SemiCircuit.ofCircuitBinary`, folding all constant and unary
  projections / negations of `fullSignature 2 Bool` into literals at zero gate cost
  (`binaryB2Cost`);
* in the opposite-bias paired subcase of Case 5a (`State.andOnPairStep`), deleting the consumer
  gate `K` reading `G` alongside `G` and `H_*` removes three distinct constraints instead of two,
  tightening the LP weights from `(α, β, ca) = (6, 4, 10)` to `(5, 3, 9)`.

The potential of a state (`State.W`) is `s + 3 q + 5 · #{used unpaired parameters}`. Starting from
`initialState C` with `a = n`, `s = C.program.cost binaryB2Cost`, `q = 0`, and
`W ≤ C.program.cost binaryB2Cost + 5 * n`, iterating `State.Valid.exists_step` establishes
`9 * S.a ≤ S.W + 9 * d` for every valid state (`State.Valid.nine_mul_a_le`), yielding
`9 * n ≤ C.program.cost binaryB2Cost + 5 * n + 9 * d`, hence
`4 * n ≤ C.program.cost binaryB2Cost + 9 * d`. The deterministic refuter is in
`CslibFrontier/Computability/Circuit/Boolean/AffineDisperser4n/Refuter.lean` (`refute_correct` in
`CslibFrontier/Computability/Circuit/Boolean/AffineDisperser4n/RefuterProofs.lean`; runtime open).

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser4n.initialState`: the initial zero-locus state of a
  circuit (with constants and unary gates folded via `ofCircuitBinary`).

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.nine_mul_a_le`: `9 * S.a ≤ S.W + 9 * d`
  for every valid state of a `d`-affine disperser.
* `Cslib.Circuits.Boolean.AffineDisperser4n.four_mul_le_cost_add`: the `4n - 9d` binary-gate lower
  bound `4 * n ≤ C.program.cost binaryB2Cost + 9 * d`.
* `Cslib.Circuits.Boolean.AffineDisperser4n.four_mul_le_size_add`: the `4n - 9d` total-size lower
  bound `4 * n ≤ C.size + 9 * d`.
* `Cslib.Circuits.Boolean.AffineDisperser4n.exists_affine_subspace_const_of_cost_lt`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.exists_affine_subspace_const_of_size_lt`: any circuit
  below `4 * n - 9 * d` in `binaryB2Cost` (or `size`) is constant on some `d`-dimensional affine
  subspace.
* `Cslib.Circuits.Boolean.AffineDisperser4n.exists_disagreeing_input_of_cost_lt`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.exists_disagreeing_input_of_size_lt`: non-constructive
  disagreement witness against any `d`-affine disperser.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 4n - O(log n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026Revision1], ECCC TR26-260 revision 1, Theorem 4.1
  (p. 21) and Remark 4.3 (p. 26): `4n - 10d` with weights `(6, 4, 10)`; `(5, 3, 9)` and
  `binaryB2Cost` are refinements of this formalization.
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser4n

open Finset Cslib.Circuits Cslib.BitString SemiCircuit AffineDisperserCore

namespace State
open AffineDisperserCore.State
private theorem Valid.nine_mul_a_le_aux {n : ℕ} {f : BooleanFunction n} {d : ℕ}
    (hf : IsAffineDisperser f d) :
    ∀ k (S : State n), S.Valid f → S.m + S.s ≤ k → 9 * S.a ≤ S.W + 9 * d := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro S hS hk
    by_cases ha : d < S.a
    · obtain ⟨S', hstep⟩ := Valid.exists_step hS hf ha
      have hih := ih (S'.m + S'.s) (Nat.lt_of_lt_of_le hstep.lt hk) S' hstep.valid le_rfl
      have hp := hstep.potential
      rw [config_ca] at hp; omega
    · omega

/-- Every valid state of a `d`-affine disperser satisfies `9 * S.a ≤ S.W + 9 * d`. -/
theorem Valid.nine_mul_a_le {n : ℕ} {f : BooleanFunction n} {d : ℕ} {S : State n}
    (hS : S.Valid f) (hf : IsAffineDisperser f d) : 9 * S.a ≤ S.W + 9 * d :=
  Valid.nine_mul_a_le_aux hf (S.m + S.s) S hS le_rfl

end State

/-- The initial gate-elimination state of a general Boolean circuit `C`, folding constant and unary
lines via `ofCircuitBinary`. -/
@[expose] def initialState {n : ℕ} (C : Circuit (fullSignature 2 Bool) n 1) : State n where
  toSemiCircuit := ofCircuitBinary C
  pairs := ∅
  phi val i := val i

/-- The initial state of a circuit computing `f` is valid. -/
theorem initialState_valid {n : ℕ} {f : BooleanFunction n}
    {C : Circuit (fullSignature 2 Bool) n 1}
    (hC : C.Computes fullInterpretation (single f)) : (initialState C).Valid f where
  wf := wellFormed_ofCircuitBinary C
  pair_mem _ h := absurd h (Finset.notMem_empty _)
  pairs_disjoint _ h := absurd h (Finset.notMem_empty _)
  phi_congr val val' hv := funext fun i => hv i (by
    change ↑i ∈ (ofCircuitBinary C).params
    rw [ofCircuitBinary_params]
    exact Finset.mem_range.2 i.isLt)
  phi_affine _ _ _ := rfl
  phi_injective val val' hv j hj := by
    change j ∈ (ofCircuitBinary C).params at hj
    exact congrFun hv ⟨j, Finset.mem_range.1 (ofCircuitBinary_params C ▸ hj)⟩
  computes val hval _ := by
    exact (out_eval_ofCircuitBinary C hval).trans (congrFun (hC fun i => val i) 0)

/-- The initial state has effective affine dimension `n`. -/
theorem initialState_a {n : ℕ} (C : Circuit (fullSignature 2 Bool) n 1) :
    (initialState C).a = n := by
  change (ofCircuitBinary C).params.card - (∅ : Finset ZeroPair).card = n
  rw [ofCircuitBinary_params, Finset.card_range, Finset.card_empty, Nat.sub_zero]

/-- The initial state has potential at most `C.program.cost binaryB2Cost + 5 * n`. -/
theorem initialState_W_le {n : ℕ} (C : Circuit (fullSignature 2 Bool) n 1) :
    (initialState C).W ≤ C.program.cost binaryB2Cost + 5 * n := by
  have hs : (initialState C).s = C.program.cost binaryB2Cost := size_ofCircuitBinary C
  have hq : (initialState C).q = 0 := Finset.card_empty
  have hwt : ∑ x ∈ (initialState C).unpaired, weight ((initialState C).deg x) ≤ 5 * n := by
    calc
      ∑ x ∈ (initialState C).unpaired, weight ((initialState C).deg x)
        ≤ ∑ _ ∈ (initialState C).unpaired, 5 :=
          Finset.sum_le_sum fun _ _ => weight_le_five _
      _ = (initialState C).unpaired.card * 5 := Finset.sum_const_nat fun _ _ => rfl
      _ ≤ (initialState C).params.card * 5 :=
          Nat.mul_le_mul_right 5 (Finset.card_le_card (Finset.filter_subset _ _))
      _ = 5 * n := by
          change (ofCircuitBinary C).params.card * 5 = 5 * n
          rw [ofCircuitBinary_params, Finset.card_range, mul_comm]
  unfold AffineDisperserCore.State.W
  rw [config_cs, config_cq, config_weight]
  omega

/-- Binary-gate lower bound `4 * n ≤ C.program.cost binaryB2Cost + 9 * d` for any
`fullSignature 2 Bool` circuit computing a `d`-affine disperser on `n` bits (charging `0` for
constants and unary gates and `1` for genuinely two-variable `B₂` gates). -/
theorem four_mul_le_cost_add {n : ℕ} {f : BooleanFunction n} {d : ℕ}
    (hf : IsAffineDisperser f d) (C : Circuit (fullSignature 2 Bool) n 1)
    (hC : C.Computes fullInterpretation (single f)) :
    4 * n ≤ C.program.cost binaryB2Cost + 9 * d := by
  have := State.Valid.nine_mul_a_le (initialState_valid hC) hf
  have := initialState_a C
  have := initialState_W_le C
  omega

/-- Size lower bound `4 * n ≤ C.size + 9 * d` for any `fullSignature 2 Bool` circuit computing a
`d`-affine disperser on `n` bits (tightening the `4 * n ≤ C.size + 10 * d` comparison bound in
[MishraSanthanam2026Revision1], Theorem 4.1, p. 21). -/
theorem four_mul_le_size_add {n : ℕ} {f : BooleanFunction n} {d : ℕ}
    (hf : IsAffineDisperser f d) (C : Circuit (fullSignature 2 Bool) n 1)
    (hC : C.Computes fullInterpretation (single f)) :
    4 * n ≤ C.size + 9 * d :=
  (four_mul_le_cost_add hf C hC).trans (Nat.add_le_add_right (cost_binaryB2Cost_le_size C) _)

/-- Any circuit with `C.program.cost binaryB2Cost + 9 * d < 4 * n` is constant on some
`d`-dimensional injective affine subspace. -/
theorem exists_affine_subspace_const_of_cost_lt {n d : ℕ}
    (C : Circuit (fullSignature 2 Bool) n 1) (hC : C.program.cost binaryB2Cost + 9 * d < 4 * n) :
    ∃ g : BitString d → BitString n, IsAffine g ∧ Function.Injective g ∧
      ∃ b : Bool, ∀ u, C.eval fullInterpretation (g u) 0 = b := by
  by_contra! hno
  let fC : BooleanFunction n := fun x => C.eval fullInterpretation x 0
  have hfC : IsAffineDisperser fC d := fun g hg hinj => by
    obtain ⟨u, hu⟩ := hno g hg hinj (fC (g 0))
    exact ⟨u, 0, hu⟩
  have hlb := four_mul_le_cost_add hfC C fun x => funext fun i => by rw [Fin.eq_zero i]; rfl
  omega

/-- Any circuit of size strictly below `4 * n - 9 * d` is constant on some `d`-dimensional
injective affine subspace. -/
theorem exists_affine_subspace_const_of_size_lt {n d : ℕ}
    (C : Circuit (fullSignature 2 Bool) n 1) (hC : C.size + 9 * d < 4 * n) :
    ∃ g : BitString d → BitString n, IsAffine g ∧ Function.Injective g ∧
      ∃ b : Bool, ∀ u, C.eval fullInterpretation (g u) 0 = b :=
  exists_affine_subspace_const_of_cost_lt C
    ((Nat.add_le_add_right (cost_binaryB2Cost_le_size C) _).trans_lt hC)

/-- Every circuit with `C.program.cost binaryB2Cost + 9 * d < 4 * n` disagrees with any `d`-affine
disperser on some input. -/
theorem exists_disagreeing_input_of_cost_lt {n d : ℕ} {f : BooleanFunction n}
    (hf : IsAffineDisperser f d) (C : Circuit (fullSignature 2 Bool) n 1)
    (hC : C.program.cost binaryB2Cost + 9 * d < 4 * n) :
    ∃ x : BitString n, C.eval fullInterpretation x 0 ≠ f x := by
  obtain ⟨g, hg, hinj, b, hb⟩ := exists_affine_subspace_const_of_cost_lt C hC
  obtain ⟨u, v, huv⟩ := hf g hg hinj
  by_cases hu : C.eval fullInterpretation (g u) 0 = f (g u)
  · refine ⟨g v, ?_⟩
    rw [hb v, ← hb u, hu]
    exact huv
  · exact ⟨g u, hu⟩

/-- Every circuit of size strictly below `4 * n - 9 * d` disagrees with any `d`-affine disperser on
some input. -/
theorem exists_disagreeing_input_of_size_lt {n d : ℕ} {f : BooleanFunction n}
    (hf : IsAffineDisperser f d) (C : Circuit (fullSignature 2 Bool) n 1)
    (hC : C.size + 9 * d < 4 * n) :
    ∃ x : BitString n, C.eval fullInterpretation x 0 ≠ f x :=
  exists_disagreeing_input_of_cost_lt hf C
    ((Nat.add_le_add_right (cost_binaryB2Cost_le_size C) _).trans_lt hC)

end Cslib.Circuits.Boolean.AffineDisperser4n
