/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Basic
public import CslibFrontier.Probability.Fooling.DecisionTree.Separation
public import CslibFrontier.Probability.KWiseIndependent
public import CslibFrontier.Probability.StatisticalDistance
import CslibFrontier.Probability.Fooling
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.StatisticalDistance.Event

/-!
# Adaptive tests of `t`-wise independence

A test that inspects bits of its input adaptively is a decision tree
(`Cslib.DecisionTree`), and the bits it inspects on an input `z` are `t.queries z`. The input
reaches the leaf it reaches exactly on the subcube of inputs that agree with `z` on those bits
(`DecisionTree.eval_eq_of_forall_mem_queries`). Summing over the leaves therefore turns a bound
on subcubes into a bound on trees: if a signed weight `d` on the cube has total weight at most
`ε` in absolute value on every subcube spanned by an *admissible* set of coordinates, and every
query set of the tree is admissible, then `|∑ z, d z * g (t.eval z)| ≤ 2 ^ k * C * ε`, where every
input makes at most `k` queries and `|g| ≤ C` at the outputs
(`Cslib.DecisionTree.abs_sum_mul_eval_le`). The proof is an induction over the tree that keeps the
partial assignment fixed by the queries so far; a query whose answer is already fixed follows a
single branch, so repeated queries cost nothing.

With `d` the difference of a distribution and the uniform distribution, this gives the bounds
in Exercises 8.29 and 8.32(2) of the March 2007 draft [Goldreich2007DraftR4]:

* **Exercise 8.29**: a `t`-wise independent generator with blocks of `κ → Bool`, as in
  `Cslib.Probability.IsKWiseIndependentHash`, is perfectly indistinguishable from uniform by any
  randomized test that examines `t` blocks adaptively
  (`Cslib.Probability.IsKWiseIndependentHash.bind_map_eval_eq`). Here every admissible set meets
  at most `t` blocks, on which the generator is exactly uniform, so `ε = 0`.
* **Exercise 8.32(2)**: if every `t` positions of `X` are `ε`-close to uniform, then every
  randomized test that inspects `t` positions adaptively has distinguishing gap at most `2 ^ t ε`
  (`Cslib.DecisionTree.abs_bind_map_eval_apply_sub_le`).

The companion separation module proves that adaptive tests can detect distributions
whose fixed-coordinate marginals are close to uniform.

## Main results

* `Cslib.DecisionTree.abs_sum_mul_eval_le`: bounds on subcubes give bounds on decision trees.
* `Cslib.Probability.IsKWiseIndependentHash.map_eval_eq`,
  `Cslib.Probability.IsKWiseIndependentHash.bind_map_eval_eq`: Exercise 8.29.
* `Cslib.DecisionTree.abs_map_eval_apply_sub_le`,
  `Cslib.DecisionTree.abs_bind_map_eval_apply_sub_le`: Exercise 8.32(2).
* `Cslib.DecisionTree.exists_dist_map_restrict_le_and_map_eval_eq_printed_length`:
  separation at the printed length in Exercise 8.32(1).

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft r4]
  [Goldreich2007DraftR4]
-/

public section

open Finset
open scoped BigOperators Cslib.Probability.PMF

namespace Cslib.DecisionTree

open Probability

variable {ι β : Type*} [Fintype ι] [DecidableEq ι]

/-- The induction behind `abs_sum_mul_eval_le`, on the subcube of inputs agreeing with `a` on `P`.
-/
private theorem abs_sum_filter_mul_eval_le (A : Finset ι → Prop) (d : (ι → Bool) → ℝ) {ε C : ℝ}
    (hd : ∀ P, A P → ∀ a : ι → Bool, |∑ z with ∀ i ∈ P, z i = a i, d z| ≤ ε) (g : β → ℝ)
    (t : DecisionTree ι β) (P : Finset ι) (a : ι → Bool) (k : ℕ)
    (h : ∀ z, (∀ i ∈ P, z i = a i) →
      A (P ∪ t.queries z) ∧ #(t.queries z \ P) ≤ k ∧ |g (t.eval z)| ≤ C) :
    |∑ z with ∀ i ∈ P, z i = a i, d z * g (t.eval z)| ≤ 2 ^ k * (C * ε) := by
  induction t generalizing P a k with
  | leaf b =>
    obtain ⟨hA, -, hg⟩ := h a fun _ _ => rfl
    simp only [queries_leaf, union_empty, eval_leaf] at hA hg ⊢
    have hC := (abs_nonneg _).trans hg
    rw [← sum_mul, abs_mul, mul_comm]
    exact (mul_le_mul hg (hd P hA a) (abs_nonneg _) hC).trans (le_mul_of_one_le_left
      (mul_nonneg hC ((abs_nonneg _).trans (hd P hA a))) (one_le_pow₀ one_le_two))
  | node i t₀ t₁ ih₀ ih₁ =>
    by_cases hi : i ∈ P
    · -- the queried coordinate is fixed on the subcube, so the node follows one branch
      have hbranch : ∀ z, (∀ j ∈ P, z j = a j) →
          (node i t₀ t₁).eval z = (cond (a i) t₁ t₀).eval z ∧
            (node i t₀ t₁).queries z = insert i ((cond (a i) t₁ t₀).queries z) := by
        intro z hz
        simp only [eval_node, queries_node, hz i hi]
        cases a i <;> simp
      have hsum : ∑ z with ∀ j ∈ P, z j = a j, d z * g ((node i t₀ t₁).eval z) =
          ∑ z with ∀ j ∈ P, z j = a j, d z * g ((cond (a i) t₁ t₀).eval z) :=
        sum_congr rfl fun z hz => by rw [(hbranch z (mem_filter.1 hz).2).1]
      have hsub : ∀ z, (∀ j ∈ P, z j = a j) →
          A (P ∪ (cond (a i) t₁ t₀).queries z) ∧ #((cond (a i) t₁ t₀).queries z \ P) ≤ k ∧
            |g ((cond (a i) t₁ t₀).eval z)| ≤ C := by
        intro z hz
        obtain ⟨hA, hk, hg⟩ := h z hz
        rw [(hbranch z hz).2, union_insert, insert_eq_of_mem (mem_union_left _ hi)] at hA
        rw [(hbranch z hz).2, insert_sdiff_of_mem _ hi] at hk
        exact ⟨hA, hk, (hbranch z hz).1 ▸ hg⟩
      rw [hsum]
      cases ha : a i
      · simpa [ha] using ih₀ P a k (by simpa [ha] using hsub)
      · simpa [ha] using ih₁ P a k (by simpa [ha] using hsub)
    · -- split the subcube along the queried coordinate
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := by
        obtain ⟨-, hk, -⟩ := h a fun _ _ => rfl
        rw [queries_node] at hk
        have := card_pos.2 ⟨i, mem_sdiff.2 ⟨mem_insert_self i
          (cond (a i) (t₁.queries a) (t₀.queries a)), hi⟩⟩
        exact ⟨k - 1, by omega⟩
      have hcube (b : Bool) (z : ι → Bool) :
          ((∀ j ∈ P, z j = a j) ∧ z i = b) ↔
            ∀ j ∈ insert i P, z j = Function.update a i b j := by
        rw [forall_mem_insert, Function.update_self]
        refine ⟨fun ⟨hz, hzi⟩ => ⟨hzi, fun j hj => (hz j hj).trans ?_⟩,
          fun ⟨hzi, hz⟩ => ⟨fun j hj => (hz j hj).trans ?_, hzi⟩⟩ <;>
        simp only [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]
      have hpiece (b : Bool) :
          ∑ z with (∀ j ∈ P, z j = a j) ∧ z i = b, d z * g ((node i t₀ t₁).eval z) =
            ∑ z with ∀ j ∈ insert i P, z j = Function.update a i b j,
              d z * g ((cond b t₁ t₀).eval z) := by
        rw [filter_congr fun z _ => hcube b z]
        refine sum_congr rfl fun z hz => ?_
        simp only [eval_node, ((hcube b z).2 (mem_filter.1 hz).2).2]
        cases b <;> rfl
      have hsub (b : Bool) : ∀ z, (∀ j ∈ insert i P, z j = Function.update a i b j) →
          A (insert i P ∪ (cond b t₁ t₀).queries z) ∧
            #((cond b t₁ t₀).queries z \ insert i P) ≤ k ∧ |g ((cond b t₁ t₀).eval z)| ≤ C := by
        intro z hz
        have hz' := (hcube b z).2 hz
        obtain ⟨hA, hk, hg⟩ := h z hz'.1
        have hq : (node i t₀ t₁).queries z = insert i ((cond b t₁ t₀).queries z) ∧
            (node i t₀ t₁).eval z = (cond b t₁ t₀).eval z := by
          simp only [queries_node, eval_node, hz'.2]
          cases b <;> exact ⟨rfl, rfl⟩
        rw [hq.1, union_insert, ← insert_union] at hA
        refine ⟨hA, ?_, hq.2 ▸ hg⟩
        have hsd : insert i ((cond b t₁ t₀).queries z \ P) =
            insert i ((cond b t₁ t₀).queries z \ insert i P) :=
          Finset.ext fun j => by by_cases hj : j = i <;> simp [hj]
        rw [hq.1, insert_sdiff_of_notMem _ hi, hsd, card_insert_of_notMem (by simp)] at hk
        omega
      have hsplit := sum_filter_add_sum_filter_not
        (({z | ∀ j ∈ P, z j = a j} : Finset (ι → Bool))) (fun z => z i = true)
        (fun z => d z * g ((node i t₀ t₁).eval z))
      simp only [filter_filter, Bool.not_eq_true] at hsplit
      rw [← hsplit, hpiece true, hpiece false, pow_succ, mul_two, add_mul]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · exact ih₁ (insert i P) (Function.update a i true) k (hsub true)
      · exact ih₀ (insert i P) (Function.update a i false) k (hsub false)

/-- **Bounds on subcubes bound decision trees.** Let `d` be a signed weight on the cube whose total
on every subcube spanned by an admissible set `P` of coordinates, `{z | ∀ i ∈ P, z i = a i}`, is at
most `ε` in absolute value. If a decision tree `t` makes at most `k` queries on every input, its
query sets are all admissible, and `|g| ≤ C` on its outputs, then the `d`-weighted sum of
`g (t.eval z)` is at most `2 ^ k * (C * ε)` in absolute value. -/
theorem abs_sum_mul_eval_le (A : Finset ι → Prop) (d : (ι → Bool) → ℝ) {ε : ℝ}
    (hd : ∀ P, A P → ∀ a : ι → Bool, |∑ z with ∀ i ∈ P, z i = a i, d z| ≤ ε)
    (t : DecisionTree ι β) (hA : ∀ z, A (t.queries z)) {k : ℕ} (hk : ∀ z, #(t.queries z) ≤ k)
    (g : β → ℝ) {C : ℝ} (hg : ∀ z, |g (t.eval z)| ≤ C) :
    |∑ z, d z * g (t.eval z)| ≤ 2 ^ k * (C * ε) := by
  simpa using abs_sum_filter_mul_eval_le A d hd g t ∅ (fun _ => false) k
    fun z _ => by simpa using ⟨hA z, hk z, hg z⟩

/-- The output distributions of a decision tree on two input distributions differ, at each output,
by the weighted sum of `abs_sum_mul_eval_le` for the indicator of that output. -/
private theorem map_eval_apply_toReal_sub [DecidableEq β] (X Y : PMF (ι → Bool))
    (t : DecisionTree ι β) (b : β) :
    ((X.map t.eval) b).toReal - ((Y.map t.eval) b).toReal =
      ∑ z, ((X z).toReal - (Y z).toReal) * (fun c => if b = c then (1 : ℝ) else 0) (t.eval z) := by
  rw [Probability.PMF.map_apply_toReal, Probability.PMF.map_apply_toReal, ← sum_sub_distrib]
  refine sum_congr rfl fun z _ => ?_
  by_cases h : b = t.eval z <;> simp [h]

/-- If the marginal of `X` on every `t` coordinates is `ε`-close to uniform, then so is the
probability of every subcube spanned by at most `t` coordinates. -/
private theorem abs_sum_filter_sub_le_of_dist_map_restrict_le {X : PMF (ι → Bool)} {t : ℕ}
    {ε : ℝ} (ht : t ≤ Fintype.card ι)
    (hX : ∀ S : Finset ι, #S = t → dist (X.map S.restrict) (PMF.uniformOfFintype (S → Bool)) ≤ ε)
    (P : Finset ι) (hP : #P ≤ t) (a : ι → Bool) :
    |∑ z with ∀ i ∈ P, z i = a i,
      ((X z).toReal - ((PMF.uniformOfFintype (ι → Bool)) z).toReal)| ≤ ε := by
  classical
  obtain ⟨S, hPS, hS⟩ := Finset.exists_superset_card_eq hP ht
  let E : Set (S → Bool) := {y | ∀ i (hi : i ∈ P), y ⟨i, hPS hi⟩ = a i}
  have hpre : S.restrict ⁻¹' E = {z | ∀ i ∈ P, z i = a i} := by
    ext z
    simp [E, Finset.restrict]
  have hprob (Y : PMF (ι → Bool)) :
      ∑ z with ∀ i ∈ P, z i = a i, (Y z).toReal = ((Y.map S.restrict).toOuterMeasure E).toReal := by
    rw [PMF.toOuterMeasure_map_apply, hpre, Probability.PMF.toOuterMeasure_apply_toReal,
      sum_filter]
    refine sum_congr rfl fun z _ => ?_
    by_cases h : ∀ i ∈ P, z i = a i <;> simp [h]
  rw [sum_sub_distrib, hprob, hprob, Probability.PMF.uniformOfFintype_pi_map_restrict]
  exact (Probability.PMF.abs_toOuterMeasure_toReal_sub_le_dist _ _ E).trans (hX S hS)

/-- **Adaptive tests of almost `t`-wise independence, deterministic case.** If the marginal of `X`
on every `t` coordinates is `ε`-close to uniform, a decision tree that inspects at most `t`
coordinates on every input accepts `X` and the uniform distribution with probabilities that differ
by at most `2 ^ t ε`. The randomized form is `abs_bind_map_eval_apply_sub_le`
[Goldreich, Exercise 8.32(2)][Goldreich2007DraftR4]. -/
theorem abs_map_eval_apply_sub_le {X : PMF (ι → Bool)} {t : ℕ} {ε : ℝ}
    (ht : t ≤ Fintype.card ι)
    (hX : ∀ S : Finset ι, #S = t → dist (X.map S.restrict) (PMF.uniformOfFintype (S → Bool)) ≤ ε)
    (T : DecisionTree ι Bool) (hT : ∀ z, #(T.queries z) ≤ t) :
    |((X.map T.eval) true).toReal -
        (((PMF.uniformOfFintype (ι → Bool)).map T.eval) true).toReal| ≤ 2 ^ t * ε := by
  rw [map_eval_apply_toReal_sub]
  simpa using abs_sum_mul_eval_le (fun P => #P ≤ t) _
    (abs_sum_filter_sub_le_of_dist_map_restrict_le ht hX) T hT hT
    (fun c => if true = c then (1 : ℝ) else 0) (C := 1) fun z => by split_ifs <;> simp

/-- **Adaptive tests of almost `t`-wise independence** [Goldreich, Exercise 8.32(2)]
[Goldreich2007DraftR4]. If every `t` fixed positions of `X` are `ε`-close to uniform, then every
randomized test that inspects `t` positions adaptively distinguishes `X` from the uniform
distribution with gap at most `2 ^ t ε`. The test draws coins `r` from `ρ` on a finite type and
runs the decision tree `T r`, which inspects at most `t` positions on every input. Its gap is the
absolute difference of its acceptance probabilities. The source leaves the string length `n ≥ t`
implicit. It appears here as `t ≤ Fintype.card ι`. -/
theorem abs_bind_map_eval_apply_sub_le {R : Type*} [Finite R] {X : PMF (ι → Bool)} {t : ℕ}
    {ε : ℝ} (ht : t ≤ Fintype.card ι)
    (hX : ∀ S : Finset ι, #S = t → dist (X.map S.restrict) (PMF.uniformOfFintype (S → Bool)) ≤ ε)
    (ρ : PMF R) (T : R → DecisionTree ι Bool) (hT : ∀ r z, #((T r).queries z) ≤ t) :
    |((ρ.bind fun r => X.map (T r).eval) true).toReal -
        ((ρ.bind fun r => (PMF.uniformOfFintype (ι → Bool)).map (T r).eval) true).toReal| ≤
      2 ^ t * ε := by
  cases nonempty_fintype R
  rw [Probability.PMF.bind_apply_toReal, Probability.PMF.bind_apply_toReal, ← sum_sub_distrib]
  calc |∑ r, ((ρ r).toReal * ((X.map (T r).eval) true).toReal -
          (ρ r).toReal * (((PMF.uniformOfFintype (ι → Bool)).map (T r).eval) true).toReal)|
      ≤ ∑ r, (ρ r).toReal * (2 ^ t * ε) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun r _ => ?_)
        rw [← mul_sub, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
        exact mul_le_mul_of_nonneg_left (abs_map_eval_apply_sub_le ht hX (T r) (hT r))
          ENNReal.toReal_nonneg
    _ = 2 ^ t * ε := by rw [← sum_mul, Probability.PMF.sum_toReal, one_mul]

end Cslib.DecisionTree

namespace Cslib.Probability.IsKWiseIndependentHash

variable {Seed Pos κ β : Type*} [Fintype Seed] [Nonempty Seed] [Fintype Pos] [DecidableEq Pos]
  [Fintype κ] [DecidableEq κ] {t : ℕ} {G : Seed → Pos → κ → Bool}

/-- The subcube probability of `u` with a uniform seed, as an average over the seeds. -/
private theorem sum_filter_uniformOfFintype_map {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (u : Ω → Pos × κ → Bool) (P : Finset (Pos × κ)) (a : Pos × κ → Bool) :
    ∑ z with ∀ i ∈ P, z i = a i, (((PMF.uniformOfFintype Ω).map u) z).toReal =
      𝔼 s, if ∀ i ∈ P, u s i = a i then (1 : ℝ) else 0 := by
  classical
  rw [sum_filter, sum_congr rfl fun z _ => (mul_boole (∀ i ∈ P, z i = a i)
      (((PMF.uniformOfFintype Ω).map u) z).toReal).symm,
    Probability.PMF.sum_map_mul]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Fintype.expect_eq_sum_div_card, inv_mul_eq_div, sum_div]

/-- For a `t`-wise independent family, the probability of a subcube spanned by bits of at most `t`
blocks depends only on the subcube. -/
private theorem expect_cube_eq {Ω : Type*} [Fintype Ω] {f : Ω → Pos → κ → Bool}
    (hf : IsKWiseIndependentHash t f) (P : Finset (Pos × κ)) (hP : #(P.image Prod.fst) ≤ t)
    (a : Pos × κ → Bool) :
    (𝔼 s, if ∀ i ∈ P, Function.uncurry (f s) i = a i then (1 : ℝ) else 0) =
      𝔼 y : P.image Prod.fst → κ → Bool,
        if ∀ p (hp : p ∈ P), y ⟨p.1, mem_image_of_mem _ hp⟩ p.2 = a p then 1 else 0 := by
  classical
  rw [← hf.expect_restrict hP]
  simp [Finset.restrict]

/-- A `t`-wise independent generator gives every subcube spanned by bits of at most `t` blocks its
uniform probability. -/
private theorem sum_filter_eq (hG : IsKWiseIndependentHash t G) (P : Finset (Pos × κ))
    (hP : #(P.image Prod.fst) ≤ t) (a : Pos × κ → Bool) :
    ∑ z with ∀ i ∈ P, z i = a i,
        ((((PMF.uniformOfFintype Seed).map fun s => Function.uncurry (G s)) z).toReal -
          ((PMF.uniformOfFintype (Pos × κ → Bool)) z).toReal) = 0 := by
  rw [sum_sub_distrib, ← Probability.PMF.uniformOfFintype_map_equiv (Equiv.curry Pos κ Bool).symm,
    sum_filter_uniformOfFintype_map, sum_filter_uniformOfFintype_map]
  simp only [Equiv.curry_symm_apply]
  have hid : (𝔼 s, if ∀ i ∈ P, Function.uncurry s i = a i then (1 : ℝ) else 0) = _ :=
    expect_cube_eq (isKWiseIndependentHash_id t) P hP a
  rw [expect_cube_eq hG P hP, hid, sub_self]

/-- **`t`-wise independent generators fool adaptive block tests, deterministic case.** If `G` is a
`t`-wise independent family of block sequences, then a decision tree on the bits `(p, j)` of the
blocks that reads bits of at most `t` blocks on every input has the same output distribution on
`G` with a uniform seed as on uniform bits. The randomized form is `bind_map_eval_eq`
[Goldreich, Exercise 8.29][Goldreich2007DraftR4]. -/
theorem map_eval_eq (hG : IsKWiseIndependentHash t G) (T : DecisionTree (Pos × κ) β)
    (hT : ∀ z, #((T.queries z).image Prod.fst) ≤ t) :
    (PMF.uniformOfFintype Seed).map (fun s => T.eval (Function.uncurry (G s))) =
      (PMF.uniformOfFintype (Pos × κ → Bool)).map T.eval := by
  classical
  rw [← Function.comp_def T.eval, ← PMF.map_comp]
  ext b
  rw [← ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _),
    ← sub_eq_zero, DecisionTree.map_eval_apply_toReal_sub]
  exact abs_nonpos_iff.1 <| (DecisionTree.abs_sum_mul_eval_le (fun P => #(P.image Prod.fst) ≤ t) _
    (fun P hP a => by rw [sum_filter_eq hG P hP a, abs_zero]) T hT (fun _ => card_le_univ _)
    (fun c => if b = c then (1 : ℝ) else 0) (C := 1)
    fun _ => by split_ifs <;> simp).trans_eq (mul_eq_zero_of_right _ (mul_zero 1))

/-- **`t`-wise independent generators fool adaptive tests of `t` blocks**
[Goldreich, Exercise 8.29][Goldreich2007DraftR4]. Let `G` be a `t`-wise independent generator:
for a uniform seed `s`, the blocks `G s p : κ → Bool` at any `t` positions `p` are independent and
uniform (`IsKWiseIndependentHash t G`; Goldreich's blocks are `b(k)`-bit strings, `κ = Fin (b k)`).
A randomized test draws coins `r` from `ρ` and runs the decision tree `T r` on the output bits
`(p, j)`, reading bits of at most `t` blocks on every input. Its output distribution on `G` with a
uniform seed equals that on uniform bits, so the output of `G` is perfectly indistinguishable from
uniform by it. A test that reads whole blocks, choosing the next block from the contents of those
already read, is such a tree; trees may also read parts of blocks. -/
theorem bind_map_eval_eq (hG : IsKWiseIndependentHash t G) {R : Type*} (ρ : PMF R)
    (T : R → DecisionTree (Pos × κ) β) (hT : ∀ r z, #(((T r).queries z).image Prod.fst) ≤ t) :
    (ρ.bind fun r => (PMF.uniformOfFintype Seed).map fun s =>
        (T r).eval (Function.uncurry (G s))) =
      ρ.bind fun r => (PMF.uniformOfFintype (Pos × κ → Bool)).map (T r).eval := by
  simp only [hG.map_eval_eq _ (hT _)]

end Cslib.Probability.IsKWiseIndependentHash
