/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module

public import CslibFrontier.Foundations.Computability.RecursiveInStream

/-! Clients of type-2 computability on Baire space, under module encapsulation. The shift
`x ↦ (n ↦ x (n + 1))` is computable, by reading the input at `n + 1`, and so is its composite
with itself; it therefore has a computable associate. The indicator of `x = 0` is not computable
relative to any total oracle, being discontinuous, while its restriction to the single input `0`
is computable, since nothing is required outside the domain. -/

public section

namespace CslibFrontierTests.RecursiveInStream

open Nat.RecursiveIn Nat.RecursiveIn.Code
open scoped Partrec

/-- The shift on Baire space. -/
def shift (x : ℕ → ℕ) : ℕ → ℕ := fun n => x (n + 1)

/-- The shift is computed, relative to every oracle, by reading the input at `n + 1`. -/
theorem computesStream_shift (p : ℕ →. ℕ) :
    ComputesStream p (comp joinRight Code.succ) shift := by
  refine computesStream_coe_iff.2 fun x n => ?_
  change (Nat.succ : ℕ →. ℕ) n >>= eval _ joinRight = _
  rw [eval_joinRight]
  exact Part.bind_some _ _

/-- The shift is computable. -/
theorem streamComputable_shift : StreamComputable shift :=
  ⟨_, computesStream_shift _⟩

/-- The composite of the shift with itself is computable, by closure under composition. -/
example : StreamComputable (fun x n => x (n + 2) : (ℕ → ℕ) → ℕ → ℕ) := by
  have h := streamComputable_shift.comp streamComputable_shift
  rwa [← PFun.coe_comp] at h

/-- The code of the composite is `streamComp` of the two codes. -/
example (p : ℕ →. ℕ) :
    ComputesStream p (streamComp (comp joinRight Code.succ) (comp joinRight Code.succ))
      ((shift : (ℕ → ℕ) →. (ℕ → ℕ)).comp shift) :=
  (computesStream_shift p).comp (computesStream_shift p)

/-- The shift has a computable associate, by the effective continuity theorem. -/
example : ∃ α : ℕ → ℕ, Computable α ∧ IsAssociate α shift :=
  streamComputable_iff_exists_isAssociate.1 streamComputable_shift

open Classical in
/-- The indicator of `x = 0` is not computable relative to any total oracle, in particular not
computable. -/
theorem not_streamComputableIn_indicator : ¬ ∃ p : ℕ → ℕ,
    StreamComputableIn p (fun x _ => if x = 0 then 1 else 0 : (ℕ → ℕ) → ℕ → ℕ) := by
  rw [← continuous_iff_streamComputableIn, continuous_iff_forall_exists_cylinder]
  intro h
  obtain ⟨k, hk⟩ := h 0 0
  have := hk (Function.update 0 k 1) (PiNat.update_mem_cylinder _ _ _)
  simp at this

open Classical in
example : ¬ StreamComputable (fun x _ => if x = 0 then 1 else 0 : (ℕ → ℕ) → ℕ → ℕ) :=
  fun h => not_streamComputableIn_indicator ⟨_, h⟩

/-- The indicator of `x = 0` restricted to the single input `0`: the partial map defined only at
`0`, with constant output `1`. -/
def indicatorAtZero : (ℕ → ℕ) →. (ℕ → ℕ) := fun x => ⟨x = 0, fun _ _ => 1⟩

/-- The restriction is computed, relative to every oracle, by the code with constant output `1`,
because nothing is required outside its domain. -/
theorem computesStream_indicatorAtZero (p : ℕ →. ℕ) :
    ComputesStream p (comp Code.succ Code.zero) indicatorAtZero := fun x y ⟨_, hy⟩ => by
  subst hy
  funext n
  change Code.eval _ Code.zero n >>= (Nat.succ : ℕ →. ℕ) = _
  exact Part.bind_some _ _

example : StreamComputable indicatorAtZero :=
  ⟨_, computesStream_indicatorAtZero _⟩

/-- A computable partial map is continuous on its domain. -/
example : Continuous fun x : indicatorAtZero.Dom => (indicatorAtZero x).get x.2 :=
  StreamComputableIn.continuous_get (p := fun _ => 0) ⟨_, computesStream_indicatorAtZero _⟩

end CslibFrontierTests.RecursiveInStream
