/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Boolean.Complexity
public import Cslib.Computability.Circuit.Simulation
public import CslibFrontier.Computability.Circuit.SourceComplexity
public import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.Basis
import CslibFrontier.Computability.Circuit.Simulation
import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.Synthesis
import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.Decomposition

/-!
# Functional completeness and multiplicative complexity over `{⊕, ∧, 1}`

Proves that the Zhegalkin basis `{⊕, ∧, 1}` simulates the De Morgan basis and defines
`multiplicativeComplexity` (`L_∧(f)`) along with its basic circuit characterizations.

## Main definitions

* `Cslib.Circuits.Boolean.Zhegalkin.multiplicativeComplexity`: minimum conjunction-gate count
  `L_∧(f)`.

## Main results

* `Cslib.Circuits.Boolean.Zhegalkin.simulates_deMorgan`: `{⊕, ∧, 1}` simulates De Morgan circuits.
* `Cslib.Circuits.Boolean.Zhegalkin.natCast_multiplicativeComplexity`,
  `multiplicativeComplexity_le_of_computes`, `multiplicativeComplexity_le_iff`,
  `exists_computes_cost_eq_multiplicativeComplexity`, `multiplicativeComplexity_le_complexity`:
  exact characterizations and complexity comparison for `multiplicativeComplexity`.

## References

* [I. S. Sergeev, *A relation between additive and multiplicative complexity of Boolean
  functions*][Sergeev2013AdditiveMultiplicative]
-/

public section

namespace Cslib.Circuits.Boolean.Zhegalkin

/-- The Zhegalkin basis `{⊕, ∧, 1}` simulates the De Morgan basis `{0, 1, ¬, ∧, ∨}`. -/
theorem simulates_deMorgan : interpretation.Simulates Boolean.interpretation := by
  rw [Interpretation.simulates_iff]
  intro op
  cases op with
  | const b =>
    cases b
    · obtain ⟨c, hc, -, -⟩ := ((synth_consts 0).mono Set.Subset.rfl
        (Set.singleton_subset_iff.mpr (Or.inl rfl)) le_rfl le_rfl).exists_circuit
      exact ⟨c, hc⟩
    · obtain ⟨c, hc, -, -⟩ := ((synth_consts 0).mono Set.Subset.rfl
        (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl le_rfl).exists_circuit
      exact ⟨c, hc⟩
  | not =>
    have h1 := synth_consts 1
    have hnot : CostSynthesis interpretation andCost
        (inputs 1 ∪ {constZero 1, constOne 1}) {Boolean.interpretation .not} 1 0 := by
      have hx0 : (fun x : Fin 1 → Bool => x 0) ∈ inputs 1 ∪ {constZero 1, constOne 1} :=
        Or.inl ⟨0, rfl⟩
      have hc1 : constOne 1 ∈ inputs 1 ∪ {constZero 1, constOne 1} := Or.inr (Or.inr rfl)
      have h := add_two_of_mem (G := Bool) (I := interpretation) (w := andCost) (addOp := Op.xor)
        rfl (fun _ => rfl) rfl hx0 hc1
      refine h.mono Set.Subset.rfl ?_ le_rfl le_rfl
      rintro _ rfl
      funext x
      change (!x 0) = (x 0 ^^ true)
      cases x 0 <;> rfl
    obtain ⟨c, hc, -, -⟩ := (h1.trans hnot).exists_circuit
    exact ⟨c, hc⟩
  | and =>
    let args : Fin 2 → BooleanFunction 2 := fun i x => x i
    have hand_raw := CostSynthesis.gate (I := interpretation) (w := andCost) (s := inputs 2)
      Op.and args fun i => ⟨i, rfl⟩
    have hand : CostSynthesis interpretation andCost (inputs 2)
        {Boolean.interpretation .and} 1 1 :=
      hand_raw.mono Set.Subset.rfl (by rintro _ rfl; rfl) le_rfl le_rfl
    obtain ⟨c, hc, -, -⟩ := hand.exists_circuit
    exact ⟨c, hc⟩
  | or =>
    let args : Fin 2 → BooleanFunction 2 := fun i x => x i
    have hand : CostSynthesis interpretation andCost (inputs 2)
        {fun x : Fin 2 → Bool => x 0 && x 1} 1 1 :=
      (CostSynthesis.gate (I := interpretation) (w := andCost) (s := inputs 2)
        Op.and args fun i => ⟨i, rfl⟩).mono Set.Subset.rfl (by rintro _ rfl; rfl) le_rfl le_rfl
    have hxor : CostSynthesis interpretation andCost (inputs 2)
        {fun x : Fin 2 → Bool => x 0 ^^ x 1} 1 0 :=
      (CostSynthesis.gate (I := interpretation) (w := andCost) (s := inputs 2)
        Op.xor args fun i => ⟨i, rfl⟩).mono Set.Subset.rfl (by rintro _ rfl; rfl) le_rfl le_rfl
    have hor : CostSynthesis interpretation andCost
        (inputs 2 ∪ ({fun x : Fin 2 → Bool => x 0 && x 1} ∪
          {fun x : Fin 2 → Bool => x 0 ^^ x 1}))
        {Boolean.interpretation .or} 1 0 := by
      have ha : (fun x : Fin 2 → Bool => x 0 && x 1) ∈
          inputs 2 ∪ ({fun x => x 0 && x 1} ∪ {fun x => x 0 ^^ x 1}) :=
        Or.inr (Or.inl rfl)
      have hx : (fun x : Fin 2 → Bool => x 0 ^^ x 1) ∈
          inputs 2 ∪ ({fun x => x 0 && x 1} ∪ {fun x => x 0 ^^ x 1}) :=
        Or.inr (Or.inr rfl)
      have h := add_two_of_mem (G := Bool) (I := interpretation) (w := andCost) (addOp := Op.xor)
        rfl (fun _ => rfl) rfl hx ha
      refine h.mono Set.Subset.rfl ?_ le_rfl le_rfl
      rintro _ rfl
      funext x
      change (x 0 || x 1) = ((x 0 ^^ x 1) ^^ (x 0 && x 1))
      cases x 0 <;> cases x 1 <;> rfl
    obtain ⟨c, hc, -, -⟩ := ((hand.union hxor).trans hor).exists_circuit
    exact ⟨c, hc⟩

/-- The Zhegalkin basis `{⊕, ∧, 1}` is functionally complete. -/
instance : interpretation.IsComplete :=
  simulates_deMorgan.isComplete

/-- The *multiplicative complexity* `L_∧(f)` of a Boolean operator `f` over `{⊕, ∧, 1}`
([Sergeev, p. 1][Sergeev2013AdditiveMultiplicative]): the least number of conjunction (`∧`) gates
in a `{⊕, ∧, 1}`-circuit computing `f`, with `.xor` and `.one` gates free. -/
noncomputable def multiplicativeComplexity {n m : ℕ} (f : (Fin n → Bool) → Fin m → Bool) : ℕ :=
  (ecomplexityFrom interpretation andCost f id).untop <|
    ecomplexityFrom_ne_top_iff.mpr (Interpretation.IsComplete.exists_computes f)

@[simp] theorem natCast_multiplicativeComplexity {n m : ℕ} (f : (Fin n → Bool) → Fin m → Bool) :
    (multiplicativeComplexity f : ℕ∞) = ecomplexityFrom interpretation andCost f id :=
  WithTop.coe_untop _ _

/-- Every `{⊕, ∧, 1}`-circuit computing `f` bounds `multiplicativeComplexity f` by its `andCost`. -/
theorem multiplicativeComplexity_le_of_computes {n m : ℕ} {f : (Fin n → Bool) → Fin m → Bool}
    (c : Circuit signature n m) (hc : c.Computes interpretation f) :
    multiplicativeComplexity f ≤ c.program.cost andCost := by
  have h := ecomplexityFrom_le_of_computesFrom (cost := andCost) (sources := id) c hc
  rw [← natCast_multiplicativeComplexity] at h
  exact_mod_cast h

/-- `multiplicativeComplexity f ≤ M` holds iff some `{⊕, ∧, 1}`-circuit computes `f` using at most
`M` conjunction gates. -/
theorem multiplicativeComplexity_le_iff {n m M : ℕ} {f : (Fin n → Bool) → Fin m → Bool} :
    multiplicativeComplexity f ≤ M ↔
      ∃ c : Circuit signature n m, c.Computes interpretation f ∧ c.program.cost andCost ≤ M := by
  have h := ecomplexityFrom_le_iff (I := interpretation) (cost := andCost) (target := f)
    (sources := id) (k := M)
  rw [← natCast_multiplicativeComplexity] at h
  exact (Nat.cast_le (α := ℕ∞)).symm.trans h

/-- Some `{⊕, ∧, 1}`-circuit computing `f` attains `multiplicativeComplexity f`. -/
theorem exists_computes_cost_eq_multiplicativeComplexity {n m : ℕ}
    (f : (Fin n → Bool) → Fin m → Bool) :
    ∃ c : Circuit signature n m,
      c.Computes interpretation f ∧ c.program.cost andCost = multiplicativeComplexity f := by
  obtain ⟨c, hc, hcost⟩ := exists_computesFrom_cost_eq_ecomplexityFrom (I := interpretation)
    (cost := andCost) (target := f) (sources := id) (Interpretation.IsComplete.exists_computes f)
  rw [← natCast_multiplicativeComplexity] at hcost
  exact ⟨c, hc, by exact_mod_cast hcost⟩

/-- Multiplicative complexity never exceeds total `{⊕, ∧, 1}` circuit complexity. -/
theorem multiplicativeComplexity_le_complexity {n m : ℕ} (f : (Fin n → Bool) → Fin m → Bool) :
    multiplicativeComplexity f ≤ complexity interpretation f := by
  obtain ⟨c, hc, hsize⟩ := exists_computes_size_eq_complexity (I := interpretation) (f := f)
  exact (multiplicativeComplexity_le_of_computes c hc).trans (c.program.cost_le_mul (b := 1)
    (fun op => by cases op <;> decide) |>.trans_eq (by simp [hsize]))


end Cslib.Circuits.Boolean.Zhegalkin
