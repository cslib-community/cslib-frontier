/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module

import CslibFrontier.Logics.Propositional.CuttingPlanes.Reification
import CslibFrontier.Logics.Propositional.PseudoBoolean.Reification

/-! A client of the two reification modules through ordinary imports, without `import all`:

* two reifications in a row, `x3 ⇔ x1 + x2 ≥ 2` and then `x4 ⇔ x3 ≥ 1`, by `runTop_reify`, reading
  the freshness of `x4`, the next number and the stored constraints from the resulting states;
* wrapping `x3 ⇒ x1 + x2 ≥ 2` by the stored clause `x4 ⇒ x3` into `x4 ⇒ x1 + x2 ≥ 2`, and
  unwrapping, by `runStep_resolveGuard_wrap` and `runStep_resolveGuard_unwrap`;
* the guard lifting of `CslibFrontier.Logics.Propositional.CuttingPlanes.Reification` at an
  assignment that makes the guard false: the counterexample `10 x̄₂ + x̄₁ ≥ 15` under `x1 ↦ 1`,
  whose restriction has degree `15`, so that the coefficient `2` gives a false line while the
  implication holds, and a coefficient at least the degree gives the implication; and the meaning
  of a wrapped derivation. -/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.VeriPBReify

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB PBConstr

/-! ### Two reifications and a wrap -/

/-- `x1 ≥ 1`, `x2 ≥ 1`, `~x1 + ~x2 ≥ 1`, numbered `1` to `3`. -/
def F : List PBConstr :=
  [⟨[(1, (0, true))], 1⟩, ⟨[(1, (1, true))], 1⟩, ⟨[(1, (0, false)), (1, (1, false))], 1⟩]

/-- `x1 + x2 ≥ 2`. -/
def C₁ : PBConstr := ⟨[(1, (0, true)), (1, (1, true))], 2⟩

/-- `x3 ≥ 1`. -/
def C₂ : PBConstr := ⟨[(1, (2, true))], 1⟩

def s₀ : State := State.init F none none

/-- After `x3 ⇔ C₁`: `x3 ⇒ C₁` at `5` and `C₁ ⇒ x3` at `7`. -/
def s₁ : State :=
  (s₀.addStrengthened 5 (impl [(2, true)] C₁)).addStrengthened 7 (impl [(2, false)] C₁.negate)

/-- After `x4 ⇔ C₂`: `x4 ⇒ x3` at `9` and `x3 ⇒ x4` at `11`. -/
def s₂ : State :=
  (s₁.addStrengthened 9 (impl [(3, true)] C₂)).addStrengthened 11 (impl [(3, false)] C₂.negate)

example : runTop F none s₀ (reify 2 C₁) = some s₁ :=
  runTop_reify (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : s₁.next = 8 := rfl

example : s₁.fresh 3 = true := by decide +kernel

/-- `x3` is not fresh after its own reification. -/
example : s₁.fresh 2 = false := by decide +kernel

example : runTop F none s₁ (reify 3 C₂) = some s₂ :=
  runTop_reify (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : s₂.next = 12 := rfl

/-- The stored `x4 ⇒ x3` is the clause `~x4 ∨ x3`. -/
example : lookup s₂.db 9 = some (Clause.toPB [(3, false), (2, true)]).normalize := by
  decide +kernel

/-- **Wrapping**: `x3 ⇒ C₁` (`5`) plus twice `x4 ⇒ x3` (`9`) is a constraint meaning
`x4 ⇒ C₁`. -/
example : ∃ d, runStep s₂.db s₂.next (resolveGuard 5 9 C₁.degree) =
      some ((s₂.next, d) :: s₂.db, s₂.next + 1) ∧
    ∀ σ, d.Holds σ ↔ (σ 3 = true → C₁.Holds σ) := by
  obtain ⟨d, hrun, -, hd⟩ := runStep_resolveGuard_wrap (s := (3, true)) (z := 2)
    (a := 5) (b := 9) (db := s₂.db) (n := s₂.next) (c := C₁) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  refine ⟨d, hrun, fun σ => ?_⟩
  rw [hd, holds_impl]
  simp

/-- **Unwrapping**: `x3 ⇒ C₁` plus twice the unit clause `x3` is a constraint meaning `C₁`. -/
example : ∃ d, runStep [(2, C₂.normalize), (1, (impl [(2, true)] C₁).normalize)] 3
      (resolveGuard 1 2 C₁.degree) =
      some ((3, d) :: [(2, C₂.normalize), (1, (impl [(2, true)] C₁).normalize)], 4) ∧
    ∀ σ, d.Holds σ ↔ C₁.Holds σ := by
  obtain ⟨d, hrun, -, hd⟩ := runStep_resolveGuard_unwrap (z := 2) (c := C₁) (a := 1) (b := 2)
    (db := [(2, C₂.normalize), (1, (impl [(2, true)] C₁).normalize)]) (n := 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact ⟨d, hrun, hd⟩

/-! ### Guard lifting at a false guard -/

open Ineq

/-- `10 x̄₂ + x̄₁ ≥ 15`, written `-10 x₂ - x₁ ≥ 4` (variables `1` and `0`). -/
noncomputable def I₀ : Ineq ℕ := ⟨Finsupp.single 1 (-10) + Finsupp.single 0 (-1), 4⟩

/-- The partial assignment `x1 ↦ 1`. -/
def τ₀ : ℕ → Bool := fun _ => true

/-- `x1 ↦ 0`, `x2 ↦ 1`: it falsifies the guard. -/
def σ₀ : ℕ → Bool := fun v => v == 1

theorem restrict_I₀ : I₀.restrict {0} τ₀ = ⟨Finsupp.single 1 (-10), 5⟩ := by
  ext w
  · rw [coeff_restrict]
    by_cases h : w = 0 <;> simp [I₀, h, Finsupp.single_apply, eq_comm]
  · simp [I₀, τ₀]

theorem guard_τ₀ : guard {0} τ₀ = ⟨Finsupp.single 0 (-1), -1⟩ := by
  ext w
  · rw [coeff_guard]
    by_cases h : w = 0 <;> simp [τ₀, h]
  · simp [bound_guard, τ₀]

/-- The restriction `10 x̄₂ ≥ 15` has degree `15`. -/
theorem degree_restrict_I₀ : (I₀.restrict {0} τ₀).degree = 15 := by
  refine le_antisymm (degree_le_iff.2 fun σ => ?_) ?_
  · rw [restrict_I₀, lhs_mk_single]; cases σ 1 <;> simp
  · have := bound_sub_lhs_le_degree σ₀ ⟨Finsupp.single 1 (-10), 5⟩
    rw [lhs_mk_single, show (σ₀ 1).toInt = 1 from rfl] at this
    rw [restrict_I₀]
    dsimp only at this
    omega

/-- A false guard, so the implication `x1 ⇒ I₀` holds at `σ₀`. -/
example : (∀ v ∈ ({0} : Finset ℕ), σ₀ v = τ₀ v) → I₀.Holds σ₀ := fun h =>
  absurd (h 0 (Finset.mem_singleton_self 0)) (by decide)

/-- With the coefficient `2`, below the degree, the lifted line fails at `σ₀`: `-10 ≥ 3`. -/
example : ¬ (I₀.restrict {0} τ₀ + 2 • guard {0} τ₀).Holds σ₀ := by
  rw [restrict_I₀, guard_τ₀]
  unfold Ineq.Holds
  rw [lhs_add, lhs_nsmul, lhs_mk_single, lhs_mk_single, bound_add, bound_nsmul]
  simp [σ₀]

/-- With a coefficient at least the degree, the lifted line holds at `σ₀`, as the implication
does. -/
example : (I₀.restrict {0} τ₀ + 15 • guard {0} τ₀).Holds σ₀ :=
  (holds_restrict_add_guard degree_restrict_I₀.le).2 fun h =>
    absurd (h 0 (Finset.mem_singleton_self 0)) (by decide)

/-- `guardLiftBound` covers the degree. -/
example : 15 ≤ guardLiftBound {0} τ₀ I₀ :=
  degree_restrict_I₀ ▸ degree_restrict_le_guardLiftBound I₀

/-- **A wrapped derivation means the implication**: if `D` follows from `C` and `z` is in
neither, every assignment satisfying `z ⇒ C`, with a coefficient `K₀` at least the degree of `C`,
satisfies `z ⇒ D`. -/
example {C D : Ineq ℕ} {z s : ℕ} (hC : C.coeff z = 0) (hD : D.coeff z = 0) (K₀ : ℕ)
    (hK₀ : C.degree ≤ K₀) (h : CuttingPlanes.DerivableInSize {C} D s) (σ : ℕ → Bool)
    (hσ : σ z = true → C.Holds σ) : σ z = true → D.Holds σ := by
  have hCr : C.restrict {z} (fun _ => true) = C := restrict_of_coeff_eq_zero (by simpa using hC)
  have hDr : D.restrict {z} (fun _ => true) = D := restrict_of_coeff_eq_zero (by simpa using hD)
  obtain ⟨K, hK, hd⟩ := h.wrap hC hD K₀
  have hlift := hd.holds (σ := σ) fun J hJ => by
    rw [Set.mem_singleton_iff.1 hJ, ← hCr]
    exact (holds_restrict_add_guard (by rwa [hCr])).2 (by simpa using hσ)
  rw [← hDr] at hlift
  simpa using (holds_restrict_add_guard (by rwa [hDr])).1 hlift

end CslibFrontierTests.Logics.Propositional.VeriPBReify
