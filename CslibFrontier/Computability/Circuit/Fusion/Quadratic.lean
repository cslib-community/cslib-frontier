/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Fusion.Cyclic.Compiler
public import CslibFrontier.Computability.Circuit.Iteration
import Mathlib.Data.Finset.Card
import CslibFrontier.Computability.Circuit.Simps

/-!
# Quadratic completeness of semifilter covers

A cover of length `t` yields an acyclic set circuit with exactly `t²` charged AND gates.
Unions and constants are free. The construction works on arbitrary carriers: at each point,
only the `t` pair coordinates can become true, so `t` synchronous rounds suffice.

Counting every gate instead, unions and constants included, the circuit over `n` supplied sets
has at most `4 (t + 1)² (n + t + 1)` gates: each round reads at most `n + t` seeds per argument
through a union tree.

## Main definitions

* `Cslib.Circuits.Fusion.PairClosureCompiler.step`,
  `Cslib.Circuits.Fusion.PairClosureCompiler.stages`: one synchronous pair-propagation step and
  iterated synchronous pair propagation.
* `Cslib.Circuits.Fusion.PairClosureCompiler.roundCircuit`,
  `Cslib.Circuits.Fusion.PairClosureCompiler.initialCircuit`,
  `Cslib.Circuits.Fusion.PairClosureCompiler.stageCircuit`: the single-round update circuit,
  initial state circuit, and unrolled stage circuit.
* `Cslib.Circuits.Fusion.PairCover.toCircuit`: an acyclic circuit realizing an unrestricted cover.

## Main results

* `Cslib.Circuits.Fusion.PairClosureCompiler.stages_stable`: point pair state stabilizes within
  the listed pair count.
* `Cslib.Circuits.Fusion.PairClosureCompiler.readState_stages`: `t` rounds recover the closure.
* `Cslib.Circuits.Fusion.PairCover.cost_toCircuit`: exactly `t²` AND gates.
* `Cslib.Circuits.Fusion.PairCover.size_toCircuit_le`: at most `4 (t + 1)² (n + t + 1)` gates.
* `Cslib.Circuits.Fusion.PairCover.eval_toCircuit`: evaluation gives the target.
* `Cslib.Circuits.Fusion.ecomplexityFrom_le_pairCoverComplexity_sq`: the minimum AND cost is at
  most the square of unrestricted cover complexity.

## References

* [B. P. Cavalar and I. C. Oliveira, *Boolean Circuit Complexity and Two-Dimensional Cover
  Problems*, Theorem 24][CavalarOliveira2025]. This formalization uses the native monotone
  basis with free bottom and top constants, and includes empty inputs and trivial targets.
-/

@[expose] public section

namespace Cslib.Circuits.Fusion.PairClosureCompiler

universe u

variable {U : Type u} {n : ℕ}
variable (target : Set U) (input : Fin n → Set U)
  (pairs : List (Set ↥(targetᶜ) × Set ↥(targetᶜ)))

/-- Apply every listed intersection rule to the reconstructed state. -/
def step (state : Fin pairs.length → Set U) : Fin pairs.length → Set U :=
  fun j => readState target input pairs state (pairs.get j).1 ∩
    readState target input pairs state (pairs.get j).2

/-- Pair values after `k` synchronous rounds, starting with all pair values empty. -/
def stages : ℕ → Fin pairs.length → Set U
  | 0 => ⊥
  | k + 1 => step target input pairs (stages k)

/-- Reconstruction is monotone in the supplied pair values. -/
theorem readState_mono {s t : Fin pairs.length → Set U} (h : s ≤ t) :
    readState target input pairs s ≤ readState target input pairs t :=
  fun _ _ hp => hp.imp_right <| Or.imp_right <| Exists.imp fun j => And.imp_right (h j ·)

/-- Pair propagation is monotone. -/
theorem step_mono : Monotone (step target input pairs) :=
  fun _ _ h _ => Set.inter_subset_inter (readState_mono target input pairs h _)
    (readState_mono target input pairs h _)

/-- Pair values only grow as rounds proceed. -/
theorem stages_mono : Monotone (stages target input pairs) := by
  refine monotone_nat_of_le_succ fun k => ?_
  induction k with | zero => exact bot_le | succ _ ih => exact step_mono target input pairs ih

private theorem readState_congr_point {s t : Fin pairs.length → Set U} {point : U}
    (h : ∀ j, point ∈ s j ↔ point ∈ t j) (a : Set ↥(targetᶜ)) :
    point ∈ readState target input pairs s a ↔ point ∈ readState target input pairs t a := by
  change (_ ∨ _ ∨ ∃ j, _ ∧ point ∈ s j) ↔ (_ ∨ _ ∨ ∃ j, _ ∧ point ∈ t j)
  simp only [h]

private theorem finite_chain_stable {m : ℕ} (a : ℕ → Finset (Fin m)) (ha : Monotone a)
    (hstep : ∀ k, a k = a (k + 1) → a (k + 1) = a (k + 2)) : a m = a (m + 1) := by
  have hanti : Antitone fun k => m - (a k).card :=
    fun _ _ hkl => Nat.sub_le_sub_left (Finset.card_le_card (ha hkl)) m
  have heq (k : ℕ) (h : m - (a k).card = m - (a (k + 1)).card) : a k = a (k + 1) := by
    refine Finset.eq_of_subset_of_card_le (ha (Nat.le_succ k)) ?_
    have := Finset.card_le_univ (a k); have := Finset.card_le_univ (a (k + 1))
    simp only [Fintype.card_fin] at *; lia
  obtain ⟨k, hk, hstable⟩ := Nat.stabilises_of_antitone hanti fun k h => by rw [hstep k (heq k h)]
  exact heq m ((hstable m (by lia)).trans (hstable (m + 1) (by lia)).symm)

/-- Every point's pair state stabilizes within the number of listed pairs, independently of
how many points the carrier contains. -/
theorem stages_stable :
    stages target input pairs pairs.length = stages target input pairs (pairs.length + 1) := by
  classical
  funext j; ext point
  let a (k : ℕ) : Finset (Fin pairs.length) :=
    Finset.univ.filter fun i => point ∈ stages target input pairs k i
  have ha : Monotone a := fun _ _ hkl _ hi => by
    simpa only [a, Finset.mem_filter, Finset.mem_univ, true_and] using
      stages_mono target input pairs hkl _ (Finset.mem_filter.mp hi).2
  have hstep (k : ℕ) (h : a k = a (k + 1)) : a (k + 1) = a (k + 2) := by
    have hpt (i) : point ∈ stages target input pairs k i ↔
        point ∈ stages target input pairs (k + 1) i := by
      simpa only [a, Finset.mem_filter, Finset.mem_univ, true_and] using Finset.ext_iff.mp h i
    ext i
    simp only [a, Finset.mem_filter, Finset.mem_univ, true_and, stages, step, Set.mem_inter_iff]
    exact and_congr (readState_congr_point target input pairs hpt _)
      (readState_congr_point target input pairs hpt _)
  simpa only [a, Finset.mem_filter, Finset.mem_univ, true_and] using
    Finset.ext_iff.mp (finite_chain_stable a ha hstep) j

/-- All finite propagation stages are contained in the generated pair values. -/
private theorem stages_le_pairValues (k : ℕ) :
    stages target input pairs k ≤ pairValues target input pairs := by
  induction k with
  | zero => exact bot_le
  | succ k ih =>
    intro j
    have hj : _ ⊆ readState target input pairs (pairValues target input pairs) _ ∩
        readState target input pairs (pairValues target input pairs) _ :=
      step_mono target input pairs ih j
    simpa only [readState_pairValues, stages, pairValues] using hj

/-- After one round per pair, reconstruction is exactly the generated semifilter closure. -/
theorem readState_stages :
    readState target input pairs (stages target input pairs pairs.length) =
      pairClosure target input pairs := by
  refine le_antisymm
    ((readState_mono target input pairs (stages_le_pairValues target input pairs _)).trans_eq
      (readState_pairValues target input pairs)) ?_
  apply pairClosure_le_readState; intro j
  change stages target input pairs (pairs.length + 1) j ⊆ _; rw [← stages_stable]

/-- Preserve the external inputs while performing one native circuit update. -/
noncomputable def roundCircuit : Circuit Monotone.signature
    (n + (pairs.length + 1)) (n + (pairs.length + 1)) :=
  (Circuit.wiring Monotone.signature (Fin.castAdd (pairs.length + 1))).append
    (updateCircuit target input pairs)

/-- The initial state has the supplied inputs and empty pair coordinates. -/
def initialCircuit : Circuit Monotone.signature n (n + (pairs.length + 1)) :=
  (Circuit.id Monotone.signature n).append
    (Circuit.pi (fun _ : Fin (pairs.length + 1) =>
      (Monotone.const false : Formula Monotone.signature n).toCircuit))

/-- Unroll the finite update program, retaining the input wires at every round. -/
noncomputable def stageCircuit (k : ℕ) :
    Circuit Monotone.signature n (n + (pairs.length + 1)) :=
  ((roundCircuit target input pairs).iterate k).comp (initialCircuit target pairs)

/-- Each propagation round charges one conjunction per listed pair. -/
private theorem cost_stageCircuit (k : ℕ) :
    (stageCircuit target input pairs k).program.cost Monotone.andCost = k * pairs.length := by
  simp only [circuit_simps, stageCircuit, roundCircuit, cost_updateCircuit, initialCircuit,
    Monotone.const, Monotone.andCost, add_zero, zero_add, mul_zero]

/-- The unrolled program carries the intended pair values; the extra output is a free read
from the preceding round and is ignored by all subsequent pair updates. -/
theorem eval_stageCircuit (k : ℕ) :
    ∃ output, (stageCircuit target input pairs k).eval (Monotone.setInterpretation U) input =
      Fin.append input (Fin.lastCases output (stages target input pairs k)) := by
  induction k with
  | zero =>
    refine ⟨∅, ?_⟩
    simp only [circuit_simps, stageCircuit, Circuit.iterate, Function.comp_id, initialCircuit]
    congr 1 with j : 1; induction j using Fin.lastCases <;> simp [Monotone.const, stages]
  | succ k ih =>
    obtain ⟨output, houtput⟩ := ih
    refine ⟨readState target input pairs (stages target input pairs k) ∅, ?_⟩
    simp only [stageCircuit, Circuit.iterate, Circuit.eval_comp] at houtput ⊢
    rw [houtput]
    simp only [circuit_simps, roundCircuit, Fin.append_comp_castAdd, eval_updateCircuit,
      show Fin.lastCases output (stages target input pairs k) ∘ Fin.castSucc =
        stages target input pairs k from funext fun _ => by simp]
    rfl

/-- A union tree has one disjunction per argument and its seed constant. -/
theorem size_joinFormula {r : ℕ} (seed : Bool) (fs : List (Formula Monotone.signature r)) :
    (joinFormula seed fs).size = (fs.map (·.size)).sum + fs.length + 1 := by
  induction fs with
  | nil => simp [joinFormula, Monotone.const]
  | cons f fs ih =>
    simp only [circuit_simps, joinFormula, Monotone.or, ih, List.map_cons, List.sum_cons,
      List.length_cons]
    lia

/-- Reading a closure coordinate uses at most two gates per input seed and pair value. -/
@[circuit_bound]
theorem size_readFormula_le (s : Set ↥(targetᶜ)) :
    (readFormula target input pairs s).size ≤ 2 * (n + pairs.length) + 1 := by
  classical
  circuit_bound [readFormula, size_joinFormula, Monotone.const]

/-- The update circuit has at most `(t + 1) (4 (n + t) + 3)` gates for `t` pairs. -/
@[circuit_bound]
theorem size_updateCircuit_le :
    (updateCircuit target input pairs).size ≤
      (pairs.length + 1) * (4 * (n + pairs.length) + 3) := by
  have : ∀ j : Fin (pairs.length + 1),
      (updateFormula target input pairs j).size ≤ 4 * (n + pairs.length) + 3 := fun j => by
    induction j using Fin.lastCases with
    | last => circuit_bound [updateFormula, Fin.lastCases_last]
    | cast j => circuit_bound [updateFormula, Fin.lastCases_castSucc, Monotone.and]
  circuit_bound [updateCircuit]

/-- Each propagation round charges the gates of one update circuit. -/
theorem size_stageCircuit (k : ℕ) :
    (stageCircuit target input pairs k).size =
      (pairs.length + 1) + k * (updateCircuit target input pairs).size := by
  simp [stageCircuit, roundCircuit, initialCircuit, Circuit.id, Formula.size_toCircuit,
    Monotone.const]

end Cslib.Circuits.Fusion.PairClosureCompiler

namespace Cslib.Circuits.Fusion

universe u

variable {U : Type u} {n : ℕ} {target : Set U} {input : Fin n → Set U}

/-- Compile an unrestricted pair cover to an ordinary acyclic set circuit, using one
propagation round per pair. Constants and binary unions are free. -/
noncomputable def PairCover.toCircuit (c : PairCover target input) :
    Circuit Monotone.signature n 1 :=
  (PairClosureCompiler.readFormula target input c.pairs ∅).toCircuit.comp
    (PairClosureCompiler.stageCircuit target input c.pairs c.pairs.length)

/-- The unrolled cover compiler uses exactly the square of the pair count in AND gates. -/
@[simp] theorem PairCover.cost_toCircuit (c : PairCover target input) :
    c.toCircuit.program.cost Monotone.andCost = c.pairs.length ^ 2 := by
  rw [PairCover.toCircuit, Circuit.cost_program_comp, Formula.cost_toCircuit,
    PairClosureCompiler.cost_readFormula, PairClosureCompiler.cost_stageCircuit,
    Nat.add_zero, pow_two]

/-- The acyclic circuit compiled from an unrestricted cover computes its target set. -/
@[simp] theorem PairCover.eval_toCircuit (c : PairCover target input) :
    c.toCircuit.eval (Monotone.setInterpretation U) input = fun _ => target := by
  obtain ⟨output, houtput⟩ := PairClosureCompiler.eval_stageCircuit target input c.pairs
    c.pairs.length
  funext i
  rw [PairCover.toCircuit, Circuit.eval_comp, houtput, Formula.eval_toCircuit,
    PairClosureCompiler.eval_readFormula,
    show Fin.lastCases output (PairClosureCompiler.stages target input c.pairs c.pairs.length) ∘
      Fin.castSucc = PairClosureCompiler.stages target input c.pairs c.pairs.length from
      funext fun _ => by simp,
    PairClosureCompiler.readState_stages, c.pairClosure_empty]

/-- The compiled circuit of a `t`-pair cover over `n` inputs has at most `4 (t + 1)² (n + t + 1)`
gates in total, counting unions and constants. -/
theorem PairCover.size_toCircuit_le (c : PairCover target input) :
    c.toCircuit.size ≤ 4 * (c.pairs.length + 1) ^ 2 * (n + c.pairs.length + 1) := by
  circuit_bound [PairCover.toCircuit, PairClosureCompiler.size_stageCircuit]

/-- Every unrestricted pair cover yields a quadratic upper bound for native AND complexity. -/
theorem PairCover.ecomplexityFrom_le_sq (c : PairCover target input) :
    ecomplexityFrom (Monotone.setInterpretation U) Monotone.andCost
      (fun _ : Unit => fun _ : Fin 1 => target) (fun _ => input) ≤
        (c.pairs.length : ℕ∞) ^ 2 := by
  have h := ecomplexityFrom_le_of_computesFrom (cost := Monotone.andCost)
    c.toCircuit (fun _ : Unit => c.eval_toCircuit)
  simpa only [PairCover.cost_toCircuit, Nat.cast_pow] using h

/-- **Quadratic completeness of Fusion**, in the native basis with free constants and unions.
No assumption on the carrier, target, or input-family size is needed with this convention. -/
theorem ecomplexityFrom_le_pairCoverComplexity_sq (target : Set U) (input : Fin n → Set U) :
    ecomplexityFrom (Monotone.setInterpretation U) Monotone.andCost
      (fun _ : Unit => fun _ : Fin 1 => target) (fun _ => input) ≤
        pairCoverComplexity target input ^ 2 := by
  by_cases htop : pairCoverComplexity target input = ⊤
  · simp [htop]
  have : Nonempty (PairCover target input) := ENat.iInf_natCast_ne_top.mp htop
  obtain ⟨c, hc⟩ := ENat.exists_eq_iInf (fun c : PairCover target input =>
    (c.pairs.length : ℕ∞))
  exact c.ecomplexityFrom_le_sq.trans_eq (congrArg (fun x => x ^ 2) hc)

end Cslib.Circuits.Fusion
