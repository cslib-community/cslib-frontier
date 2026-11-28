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
is computable, since nothing is required outside the domain. Finally, `nextNonzeroPos` is a
partial map defined exactly on the non-open set of sequences with infinitely many nonzero entries,
continuous on its domain and therefore computable relative to an oracle with a Gδ extension. -/

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
example : Continuous fun x : indicatorAtZero.Dom => (indicatorAtZero x).get x.property :=
  StreamComputableIn.continuous_get (p := fun _ => 0) ⟨_, computesStream_indicatorAtZero _⟩

/-- The partial map defined on sequences with infinitely many nonzero entries, sending `x` to the
sequence `n ↦ min {m ≥ n | x m ≠ 0}`. -/
def nextNonzeroPos : (ℕ → ℕ) →. (ℕ → ℕ) :=
  fun x => ⟨∀ k, ∃ m ≥ k, x m ≠ 0, fun hx n => Nat.find (hx n)⟩

/-- The domain of `nextNonzeroPos` is not open in Baire space. -/
theorem not_isOpen_dom_nextNonzeroPos : ¬ IsOpen nextNonzeroPos.Dom := by
  intro hopen
  have hone : (fun _ => 1 : ℕ → ℕ) ∈ nextNonzeroPos.Dom := fun k => ⟨k, le_rfl, one_ne_zero⟩
  obtain ⟨_, ⟨z, k, rfl⟩, hz, hsub⟩ := (PiNat.isTopologicalBasis_cylinders fun _ : ℕ => ℕ)
    |>.exists_subset_of_mem_open hone hopen
  have hzero : (fun i => if i < k then 1 else 0 : ℕ → ℕ) ∈ nextNonzeroPos.Dom := by
    refine hsub ?_
    rw [← PiNat.mem_cylinder_iff_eq.1 hz]
    intro i hi
    simp [hi]
  obtain ⟨m, hm, hne⟩ := hzero k
  exact hne (by simp [Nat.not_lt.2 hm])

/-- `nextNonzeroPos` is continuous on its domain. -/
theorem continuous_get_nextNonzeroPos :
    Continuous fun x : nextNonzeroPos.Dom => (nextNonzeroPos x).get x.property := by
  refine continuous_get_iff_forall_exists_cylinder.2 fun x y hy n => ?_
  obtain ⟨hx, rfl⟩ := hy
  refine ⟨Nat.find (hx n) + 1, fun x' hcyl y' hy' => ?_⟩
  obtain ⟨hx', rfl⟩ := hy'
  change Nat.find (hx' n) = Nat.find (hx n)
  have hspec := Nat.find_spec (hx n)
  refine (Nat.find_eq_iff (hx' n)).2 ⟨⟨hspec.1, ?_⟩, fun m hm => ?_⟩
  · rw [PiNat.mem_cylinder_iff.1 hcyl _ (Nat.lt_succ_self _)]
    exact hspec.2
  · rw [PiNat.mem_cylinder_iff.1 hcyl _ (Nat.lt_succ_of_lt hm)]
    exact Nat.find_min (hx n) hm

/-- `nextNonzeroPos` is computable relative to a total oracle. -/
example : ∃ p : ℕ → ℕ, StreamComputableIn p nextNonzeroPos :=
  continuous_get_iff_streamComputableIn.1 continuous_get_nextNonzeroPos

/-- `nextNonzeroPos` extends to a computable continuous partial map on a Gδ domain. -/
example :
    ∃ (p : ℕ → ℕ) (F' : (ℕ → ℕ) →. (ℕ → ℕ)),
      IsGδ F'.Dom ∧
      (∀ x, ∀ y ∈ nextNonzeroPos x, y ∈ F' x) ∧
      StreamComputableIn p F' ∧
      Continuous fun x : F'.Dom => (F' x).get x.property :=
  exists_gδ_extension_of_continuous_get continuous_get_nextNonzeroPos

example : (fun _ => 0 : ℕ → ℕ) ∉ nextNonzeroPos.Dom := by
  intro h
  obtain ⟨_, _, hne⟩ := h 0
  exact hne rfl

example :
    ∃ y ∈ nextNonzeroPos (fun i => if i % 2 = 1 then 1 else 0), y 0 = 1 ∧ y 2 = 3 := by
  have hdom : (fun i => if i % 2 = 1 then 1 else 0 : ℕ → ℕ) ∈ nextNonzeroPos.Dom :=
    fun k => ⟨2 * k + 1, by omega, by simp⟩
  refine ⟨_, Part.get_mem hdom, ?_, ?_⟩
  · exact (Nat.find_eq_iff (hdom 0)).2 ⟨by simp, fun m hm => by simp [Nat.lt_one_iff.1 hm]⟩
  · exact (Nat.find_eq_iff (hdom 2)).2 ⟨by simp, fun m hm => by
      intro ⟨hge, hne⟩
      have : m = 2 := by omega
      subst this
      simp at hne⟩

end CslibFrontierTests.RecursiveInStream
