/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Algorithms.Lean.Query.FreeM
public import Mathlib.Algebra.Group.Hom.Defs

/-!
# Changing the cost monoid of a query program

`FreeM.cost oracle weight p` adds up the weights of the queries along the path of `p` under
`oracle`. An additive monoid homomorphism `f : T →+ T'` commutes with this sum: `f` of the cost
with weights `weight` is the cost with weights `f ∘ weight`. For example, with
`f = Nat.castAddMonoidHom ℝ`, an exact natural-number cost transfers to a real-valued cost bound.

## Main results

* `Cslib.FreeM.map_cost`: `f (p.cost oracle weight) = p.cost oracle (f ∘ weight)`.
* `Cslib.FreeM.cost_zero`: with zero weights, the cost is zero.
* `Cslib.FreeM.cost_le_mul_countQueries`: with weights at most `c`, the cost is at most `c` times
  the number of queries.
-/

public section

namespace Cslib.FreeM

universe u v t w x

variable {F : Type u → Type v} {α : Type u}

/-- An additive monoid homomorphism commutes with the weighted query cost. -/
theorem map_cost {T : Type t} {T' : Type w} {G : Type x} [AddMonoid T] [AddMonoid T']
    [FunLike G T T'] [AddMonoidHomClass G T T'] (f : G) (oracle : {ι : Type u} → F ι → ι)
    (weight : {ι : Type u} → F ι → T) (p : FreeM F α) :
    f (p.cost oracle weight) = p.cost oracle (fun q => f (weight q)) := by
  induction p with
  | pure a => rw [cost_pure, cost_pure, map_zero]
  | lift_bind op cont ih =>
    change f ((FreeM.lift op >>= cont).cost oracle weight) =
      (FreeM.lift op >>= cont).cost oracle (fun q => f (weight q))
    rw [cost_liftBind, cost_liftBind, map_add, ih]

/-- With every query weighted zero, the cost is zero: `map_cost` for the zero homomorphism. -/
@[simp] theorem cost_zero {T : Type t} [AddMonoid T] (oracle : {ι : Type u} → F ι → ι)
    (p : FreeM F α) : p.cost oracle (fun _ => (0 : T)) = 0 := by
  simpa using (map_cost (0 : T →+ T) oracle (fun _ => (0 : T)) p).symm

/-- With every query weighted at most `c`, the cost is at most `c` times the number of queries.
For example, a program whose queries are each simulated by at most `c` queries of another kind
(`Cslib.FreeM.liftM`, `Cslib.FreeM.cost_liftM`) makes at most `c` times as many. -/
theorem cost_le_mul_countQueries (oracle : {ι : Type u} → F ι → ι)
    (weight : {ι : Type u} → F ι → ℕ) {c : ℕ} (hc : ∀ {ι : Type u} (q : F ι), weight q ≤ c)
    (p : FreeM F α) : p.cost oracle weight ≤ c * p.countQueries oracle := by
  induction p with
  | pure a => simp
  | lift_bind op cont ih =>
    change (FreeM.lift op >>= cont).cost oracle weight ≤
      c * (FreeM.lift op >>= cont).countQueries oracle
    rw [cost_liftBind, countQueries_liftBind, Nat.mul_add, Nat.mul_one]
    have := ih (oracle op)
    have := hc op
    omega

end Cslib.FreeM
