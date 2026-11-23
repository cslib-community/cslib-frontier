/-
Copyright (c) 2026 Bas Spitters, Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters, Devon Tuma
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.QueryCount
import CslibFrontier.Languages.Probabilistic.QueryCount.Scale
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Query budgets through a handler with several kinds of calls

A program can have separate budgets for signing calls and direct hash queries, for example.
If implementing a source call uses at most its weighted sum of source charges on target
channel `j`, then the same weighted sum of program budgets bounds the entire implementation
on `j`. Successive handlers act on the resulting budgets in turn.

These laws specialize vector charges to the pathwise natural-number bounds of
`Cslib.OracleComp.IsCostBounded`.

## Main results

* `Cslib.OracleComp.IsCostBounded.sum_mul` combines a finite set of weighted bounds.
* `Cslib.OracleComp.IsCostBounded.interpret_demand` transfers channel budgets across one handler.
* `Cslib.OracleComp.IsCostBounded.interpret_interpret_demand` composes two handlers' demand
  matrices in execution order.

## References

Bas Spitters's [vector-charge demand laws in PolyFun](https://github.com/Verified-zkEVM/PolyFun/blob/ae1b2a3b9cb5f28f43c4b41138481f68b901838d/PolyFun/PFunctor/Handler/CertifiedVec.lean).
-/

public section

open scoped BigOperators

namespace Cslib.OracleComp.IsCostBounded

universe u v w

variable {Q : Type u} {spec : OracleSpec.{u, v} Q} {α : Type v}

/-- A finite weighted sum of budgets bounds the corresponding weighted sum of charges. -/
theorem sum_mul {I : Type*} (indices : Finset I) (weight : I → ℕ)
    {cost : I → Q → ℕ} {budget : I → ℕ} {p : OracleComp spec α}
    (h : ∀ i ∈ indices, IsCostBounded (cost i) p (budget i)) :
    IsCostBounded (fun q => ∑ i ∈ indices, cost i q * weight i) p
      (∑ i ∈ indices, budget i * weight i) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa using of_forall_cost_eq_zero (cost := fun _ : Q => 0) (fun _ => rfl) p
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact ((h i (Finset.mem_insert_self i s)).mul_of_le (c := weight i)
      (fun _ => le_rfl)).add (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))

/-- Substitution transfers a family of source budgets to each target channel according to
the per-call demand. Only the family of source charges needs to be finite. -/
theorem interpret_demand {I J : Type*} [Fintype I] {R : Type w} {target : OracleSpec.{w, v} R}
    (sourceCost : I → Q → ℕ) (targetCost : J → R → ℕ) (demand : I → J → ℕ)
    {budget : I → ℕ} (handler : (q : Q) → OracleComp target (spec q))
    (step : ∀ q j, IsCostBounded (targetCost j) (handler q) (∑ i, sourceCost i q * demand i j))
    {p : OracleComp spec α} (bound : ∀ i, IsCostBounded (sourceCost i) p (budget i)) (j : J) :
    IsCostBounded (targetCost j) (OracleComp.interpret handler p) (∑ i, budget i * demand i j) :=
  (sum_mul Finset.univ (fun i => demand i j) (fun i _ => bound i)).interpret (fun q => step q j)

/-- With two handlers, demands compose by matrix multiplication. The inner sum ranges over
the intermediate channels and the outer sum weights each source budget exactly once. -/
theorem interpret_interpret_demand {I J K : Type*} [Fintype I] [Fintype J]
    {R T : Type*} {mid : OracleSpec.{_, v} R} {target : OracleSpec.{_, v} T}
    (sourceCost : I → Q → ℕ) (midCost : J → R → ℕ) (targetCost : K → T → ℕ)
    (d : I → J → ℕ) (e : J → K → ℕ)
    (f : (q : Q) → OracleComp mid (spec q)) (g : (r : R) → OracleComp target (mid r))
    (hf : ∀ q j, IsCostBounded (midCost j) (f q) (∑ i, sourceCost i q * d i j))
    (hg : ∀ r k, IsCostBounded (targetCost k) (g r) (∑ j, midCost j r * e j k))
    {budget : I → ℕ} {p : OracleComp spec α} (hp : ∀ i, IsCostBounded (sourceCost i) p (budget i))
    (k : K) : IsCostBounded (targetCost k) (OracleComp.interpret g (OracleComp.interpret f p))
      (∑ i, budget i * ∑ j, d i j * e j k) := by
  have h := interpret_demand midCost targetCost e g hg
    (interpret_demand sourceCost midCost d f hf hp) k
  simpa only [Finset.sum_mul, Finset.mul_sum, Nat.mul_assoc, Finset.sum_comm (γ := I)] using h

end Cslib.OracleComp.IsCostBounded
