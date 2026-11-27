/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Finset.Piecewise
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Sums over contents, one step after the other

Cells `c : Ce` hold contents in `W`. A *step* (`WriteStep`) writes the cells of a finite set: it
chooses among finitely many choices, each with a weight, and writes contents, where the weight and
the contents are functions of the contents of all cells. Its *factor* at contents `y` of all cells
is the sum of the weights of the choices that write what `y` has at the cells of the step.

If every cell is written by at most one step of a list and every step depends only on the cells
that no step from it on writes (`WriteStep.Sequential`), then the sum, over all contents of the
written cells, of the product of the factors is the sum over all executions of the steps in
order, each from the contents that the steps before it have left
(`WriteStep.sum_prod_factor_mul_eq_exec`).

## Main definitions

* `WriteStep`: a step, with its `choices`, the cells `written`, the `weight` and the `contents`
  of a choice, and the cells `read`.
* `WriteStep.factor`: the factor of a step at given contents.
* `WriteStep.writtenCells`: the cells written by a list of steps.
* `WriteStep.exec`: the sum over all executions of a list of steps.
* `WriteStep.Sequential`: steps depend only on what has been written before, and write every
  cell once.

## Main results

* `WriteStep.sum_prod_factor_mul_eq_exec`: sums over contents are sums over executions.
* `WriteStep.Sequential.of_pairwise`: a criterion for `Sequential` by the cells `read`.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3 (the evaluator in the proof of
Theorem J.3 guesses the contents of the inner packets and then compares them); module
`Nc.Grp.Steps`.
-/

public section

open Finset

/-- A step that writes the cells of `written`: a choice `ω ∈ choices` has the weight
`weight ω y` and writes the contents `contents ω y c` at the cells `c ∈ written`, as functions of
the contents `y` of all cells. The field `read` names cells on which the weight and the contents
may depend; it does not enter `WriteStep.factor` or `WriteStep.exec`, and is the datum of the
criterion `WriteStep.Sequential.of_pairwise`. -/
structure WriteStep (F Ce W : Type*) where
  /-- The type of the choices. -/
  Choice : Type
  /-- The finitely many choices. -/
  choices : Finset Choice
  /-- The cells that are written. -/
  written : Finset Ce
  /-- The weight of a choice. -/
  weight : Choice → (Ce → W) → F
  /-- The contents that a choice writes. -/
  contents : Choice → (Ce → W) → Ce → W
  /-- The cells that are read. -/
  read : Finset Ce

namespace WriteStep

variable {F Ce W : Type*} [DecidableEq Ce]

/-- The factor of a step at the contents `y`: the sum of the weights of the choices that write the
contents that `y` has at the written cells. -/
@[expose] def factor [AddCommMonoid F] [DecidableEq W] (s : WriteStep F Ce W) (y : Ce → W) : F :=
  ∑ ω ∈ s.choices, if ∀ c ∈ s.written, y c = s.contents ω y c then s.weight ω y else 0

/-- The cells written by a list of steps. -/
@[expose] def writtenCells : List (WriteStep F Ce W) → Finset Ce
  | [] => ∅
  | s :: l => s.written ∪ writtenCells l

/-- The sum over all executions of a list of steps from the contents `σ`, of the product of the
weights times `G` at the final contents. -/
@[expose] def exec [NonUnitalNonAssocSemiring F] :
    List (WriteStep F Ce W) → ((Ce → W) → F) → (Ce → W) → F
  | [], G, σ => G σ
  | s :: l, G, σ =>
    ∑ ω ∈ s.choices, s.weight ω σ * exec l G (s.written.piecewise (s.contents ω σ) σ)

/-- Every step depends only on the cells that neither it nor a later step writes, and every cell
is written at most once. -/
@[expose] def Sequential : List (WriteStep F Ce W) → Prop
  | [] => True
  | s :: l => Disjoint s.written (writtenCells l) ∧
      (∀ ω ∈ s.choices, ∀ y y' : Ce → W, (∀ c ∉ s.written ∪ writtenCells l, y c = y' c) →
        s.weight ω y = s.weight ω y' ∧ ∀ c ∈ s.written, s.contents ω y c = s.contents ω y' c) ∧
      Sequential l

@[simp] theorem writtenCells_nil : writtenCells ([] : List (WriteStep F Ce W)) = ∅ := rfl

@[simp] theorem writtenCells_cons (s : WriteStep F Ce W) (l : List (WriteStep F Ce W)) :
    writtenCells (s :: l) = s.written ∪ writtenCells l := rfl

theorem mem_writtenCells {l : List (WriteStep F Ce W)} {c : Ce} :
    c ∈ writtenCells l ↔ ∃ s ∈ l, c ∈ s.written := by
  induction l with
  | nil => simp
  | cons s l ih => simp [ih]

@[simp] theorem exec_nil [NonUnitalNonAssocSemiring F] (G : (Ce → W) → F) (σ : Ce → W) :
    exec [] G σ = G σ := rfl

@[simp] theorem exec_cons [NonUnitalNonAssocSemiring F] (s : WriteStep F Ce W)
    (l : List (WriteStep F Ce W)) (G : (Ce → W) → F) (σ : Ce → W) :
    exec (s :: l) G σ =
      ∑ ω ∈ s.choices, s.weight ω σ * exec l G (s.written.piecewise (s.contents ω σ) σ) := rfl

/-- **Sums over contents are sums over executions.** For a sequential list of steps, the sum,
over the contents `y` of the written cells (the other cells keep the contents `σ`), of the product
of the factors of the steps times `G y` is the sum over the executions from `σ`. -/
theorem sum_prod_factor_mul_eq_exec [Semiring F] [Fintype Ce] [Fintype W] [DecidableEq W]
    {l : List (WriteStep F Ce W)} (hl : Sequential l) (G : (Ce → W) → F) (σ : Ce → W) :
    ∑ y with ∀ c ∉ writtenCells l, y c = σ c, (l.map fun s => s.factor y).prod * G y =
      exec l G σ := by
  induction l generalizing σ with
  | nil => simp [← funext_iff, Finset.filter_eq']
  | cons s l ih =>
    obtain ⟨hd, hr, hl⟩ := hl
    have h1 : ∀ y ∈ ({y | ∀ c ∉ writtenCells (s :: l), y c = σ c} : Finset (Ce → W)),
        ((s :: l).map fun s => s.factor y).prod * G y = ∑ ω ∈ s.choices,
          if ∀ c ∈ s.written, y c = s.contents ω σ c then
            s.weight ω σ * ((l.map fun s => s.factor y).prod * G y) else 0 := by
      intro y hy
      rw [List.map_cons, List.prod_cons, factor, mul_assoc, sum_mul]
      refine sum_congr rfl fun ω hω => ?_
      obtain ⟨e1, e2⟩ := hr ω hω y σ (mem_filter.1 hy).2
      have e3 : (∀ c ∈ s.written, y c = s.contents ω y c) ↔
          ∀ c ∈ s.written, y c = s.contents ω σ c := forall₂_congr fun c hc => by rw [e2 c hc]
      simp only [e3, e1, ite_mul, zero_mul]
    rw [sum_congr rfl h1, sum_comm, exec_cons]
    refine sum_congr rfl fun ω _ => ?_
    rw [← ih hl, mul_sum, ← sum_filter, filter_filter]
    refine sum_congr (filter_congr fun y _ => ?_) fun _ _ => rfl
    simp only [writtenCells_cons, mem_union, not_or, piecewise, disjoint_left] at hd ⊢
    grind

/-- A criterion for `Sequential`: the cells that a step reads are written neither by it nor by a
later step, different steps write different cells, and the weight and the written contents of a
step depend only on the cells that it reads. -/
theorem Sequential.of_pairwise {l : List (WriteStep F Ce W)}
    (h1 : l.Pairwise fun s s' => Disjoint s.written s'.written ∧ Disjoint s.read s'.written)
    (h2 : ∀ s ∈ l, Disjoint s.read s.written ∧ ∀ ω ∈ s.choices, ∀ y y' : Ce → W,
      (∀ c ∈ s.read, y c = y' c) →
        s.weight ω y = s.weight ω y' ∧ ∀ c ∈ s.written, s.contents ω y c = s.contents ω y' c) :
    Sequential l := by
  induction l with
  | nil => trivial
  | cons s l ih =>
    rw [List.pairwise_cons] at h1
    obtain ⟨h3, h4⟩ := h2 s List.mem_cons_self
    refine ⟨?_, fun ω hω y y' hy => h4 ω hω y y' fun c hc => hy c ?_,
      ih h1.2 fun s' hs' => h2 s' (List.mem_cons_of_mem _ hs')⟩
    · exact disjoint_left.2 fun c hc hc' =>
        have ⟨s', hs', hc''⟩ := mem_writtenCells.1 hc'
        disjoint_left.1 (h1.1 s' hs').1 hc hc''
    · rw [mem_union, not_or, mem_writtenCells]
      exact ⟨disjoint_left.1 h3 hc, fun ⟨s', hs', hc'⟩ => disjoint_left.1 (h1.1 s' hs').2 hc hc'⟩

end WriteStep
