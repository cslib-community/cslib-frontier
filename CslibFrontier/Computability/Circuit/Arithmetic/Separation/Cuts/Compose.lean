/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Accel
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Lists
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Guess
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.Ring

/-!
# Cuts, and one cut after another

A *cut* (`Cut.IsCut`) is a program that turns an instance of a plain sum into a weighted
list of lists of smaller instances, the *pieces*, such that the plain sum of the instance is the
weighted sum of the products of the plain sums of the pieces (`Cut.pvProd`). The numbers
of steps and the sizes before and after, the number of pieces and the running time are
parameters.

Running a second cut on every piece of a first one is a cut again (`Cut.IsCut.comp`): the
numbers of pieces multiply and the sum formulas compose. This is the composition step of the
proof of [AnthropicVPVNP2026], Theorem J.4 (module `NS1.Compose`).

## Main definitions

* `Cut.pvProd`: the product of the plain sums of a list of instances.
* `Cut.IsCut`: a program that cuts plain sums into pieces.
* `Cut.cutComp`: the program that runs a second cut on every piece of a first one.

## Main results

* `Cut.IsCut.comp`: the composition of two cuts is a cut.
* `Cut.IsCut.cutProg`: a cut to the scale `v ^ H` is a program for the cut hypothesis
  `Interpreter.CutProg`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem J.4 (cuts at all scales), the composition of cuts in its proof; module `NS1.Compose`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Cut

open Interpreter Interpreter.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- The product of the plain sums of a list of instances. -/
@[expose] noncomputable def pvProd (θ : List Bool → A) (o : Tree) : A :=
  (o.toList.map (pv θ)).prod

/-- The program `G` cuts plain sums into pieces. The parameters of `IsCut θ τ s τ' s' P t G`
are, in order: the number `τ` of steps and the size `s` of the instances that are cut; the number
`τ'` of steps and the size `s'` of the pieces; the bound `P` for the number of pieces; the running
time `t`; and the program `G`. The value of `G` is a weighted list of lists of pieces, and `P`
bounds the number of pieces in each of the returned lists, not the number of lists. -/
@[expose] def IsCut (θ : List Bool → A) (τ s τ' s' P t : ℕ) (G : Tree) : Prop :=
  ∀ z, z.size ≤ s → ∃ Q, Does θ (Fm.ofTree G) z Q t ∧
    (∀ q ∈ Q, q.2.toList.length ≤ P ∧ ∀ y ∈ q.2.toList, y.size ≤ s') ∧
    (Plain θ τ z → (∀ q ∈ Q, ∀ y ∈ q.2.toList, Plain θ τ' y) ∧ pv θ z = wsum Q (pvProd θ))

/-- A cut with weaker bounds on the pieces and the time. -/
theorem IsCut.mono {τ s τ' s' P t τ'' s'' P' t' : ℕ} {G : Tree} (h : IsCut θ τ s τ' s' P t G)
    (hτ : τ' ≤ τ'') (hs : s' ≤ s'') (hP : P ≤ P') (ht : t ≤ t') :
    IsCut θ τ s τ'' s'' P' t' G := fun z hz =>
  let ⟨Q, hD, hQ, hv⟩ := h z hz
  ⟨Q, hD.mono ht, fun q hq => ⟨(hQ q hq).1.trans hP, fun y hy => ((hQ q hq).2 y hy).trans hs⟩,
    fun hp => ⟨fun q hq y hy => ((hv hp).1 q hq y hy).of_le hτ, (hv hp).2⟩⟩

/-- A cut to `v ^ H` steps whose pieces, sizes and time are small enough is a program for the cut
hypothesis. -/
theorem IsCut.cutProg {H v τ s P t : ℕ} {G : Tree}
    (h : IsCut θ τ s (v ^ H) (v ^ (H - 32)) P t G) (hG : G.size ≤ v ^ H) (ht : t * v ^ 24 ≤ τ)
    (hP : P * v ^ H ≤ τ * v ^ 2) : CutProg θ H v τ s G := by
  refine ⟨hG, fun z hz => ?_, fun z hz hp => ?_⟩
  · obtain ⟨Q, hD, hQ, -⟩ := h z hz
    refine ⟨hD.hl, fun r hr => ?_⟩
    obtain ⟨h1, h2, q, hq, h3⟩ := hD.evl.1 r hr
    rw [← h3]
    exact ⟨h1, (Nat.mul_le_mul_right _ h2).trans ht,
      (Nat.mul_le_mul_right _ (hQ q hq).1).trans hP, (hQ q hq).2⟩
  · obtain ⟨Q, hD, hQ, hv⟩ := h z hz
    refine ⟨fun r hr y hy => ?_, (hv hp).2.trans (hD.evl.2 (pvProd θ)).symm⟩
    obtain ⟨-, -, q, hq, h3⟩ := hD.evl.1 r hr
    exact (hv hp).1 q hq y (h3 ▸ hy)

/-! ### The pieces of the pieces -/

/-- One step of the second cut, as a weighted list: the pieces `R x` of the instance `x` are put
in front of the pieces `σ` found so far. -/
private def cutStepW (R : Tree → List (A × Tree)) (x σ : Tree) : List (A × Tree) :=
  (R x).map fun q => (q.1, listT (q.2.toList ++ σ.toList))

/-- Every list in the fold of `cutStepW R` over `xs` consists of the pieces so far and of pieces
of the elements of `xs`, at most `P` for each element. -/
private theorem mem_foldW_cutStepW {R : Tree → List (A × Tree)} {P : ℕ} {xs : List Tree}
    (hP : ∀ x ∈ xs, ∀ q ∈ R x, q.2.toList.length ≤ P) {σ : Tree} {r : A × Tree}
    (hr : r ∈ foldW (cutStepW R) xs σ) :
    r.2.toList.length ≤ σ.toList.length + xs.length * P ∧
      ∀ y ∈ r.2.toList, y ∈ σ.toList ∨ ∃ x ∈ xs, ∃ q ∈ R x, y ∈ q.2.toList := by
  induction xs generalizing σ r with
  | nil =>
    obtain rfl := List.mem_singleton.1 hr
    exact ⟨by simp, fun y hy => .inl hy⟩
  | cons x xs ih =>
    obtain ⟨q', hq', r', hr', h1, -⟩ := mem_bindW hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hq'
    obtain ⟨h2, h3⟩ := ih (fun y hy => hP y (List.mem_cons_of_mem _ hy)) hr'
    simp only [toList_listT, List.length_append, List.mem_append] at h2 h3
    have := hP x List.mem_cons_self q hq
    rw [h1]
    refine ⟨by simp only [List.length_cons, add_mul, one_mul]; omega, fun y hy => ?_⟩
    rcases h3 y hy with (h | h) | ⟨x', hx', h⟩
    · exact .inr ⟨x, List.mem_cons_self, q, hq, h⟩
    · exact .inl h
    · exact .inr ⟨x', List.mem_cons_of_mem _ hx', h⟩

/-- The sum formulas compose: if the pieces `R x` of every `x` in `xs` have the plain sum of `x`,
the fold of `cutStepW R` over `xs` has the product of the plain sums of `xs`. -/
private theorem wsum_foldW_cutStepW {R : Tree → List (A × Tree)} {xs : List Tree}
    (hR : ∀ x ∈ xs, wsum (R x) (pvProd θ) = pv θ x) (σ : Tree) :
    wsum (foldW (cutStepW R) xs σ) (pvProd θ) = (xs.map (pv θ)).prod * pvProd θ σ := by
  induction xs generalizing σ with
  | nil => simp [foldW]
  | cons x xs ih =>
    rw [foldW, wsum_bindW, wsum_congr (φ' := fun o => (xs.map (pv θ)).prod * pvProd θ o)
      fun q _ => ih (fun y hy => hR y (List.mem_cons_of_mem _ hy)) q.2,
      List.map_cons, List.prod_cons, ← hR x List.mem_cons_self]
    simp only [wsum, cutStepW, List.map_map, Function.comp_def, pvProd, toList_listT,
      List.map_append, List.prod_append]
    rw [mul_assoc, ← List.sum_map_mul_right]
    exact congrArg List.sum (List.map_congr_left fun q _ => by ring)

/-! ### The program -/

/-- One more cut: at (element, list of pieces so far), the pieces of the element are put in front
of the list. -/
private def cutStep (G : Tree) : Fm :=
  lett (.cons (app G (.hd .id)) (.tl .id)) (appF (.hd .id) (.tl .id))

/-- First the cut `G`, then the cut `G'` on every piece. -/
def cutComp (G G' : Tree) : Fm :=
  lett (app G .id) (foldF (cutStep G') (.quote .nil) .id)

theorem size_cutComp (G G' : Tree) : (cutComp G G').code.size ≤ G.size + 3 * G'.size + 3000 := by
  simp only [cutComp, cutStep, appF, foldF, foldB, lett, app, Fm.code, Tree.size, size_num]
  omega

private theorem cutStep_does {G : Tree} {R : Tree → List (A × Tree)} {x : Tree} {t P : ℕ}
    (hD : Does θ (Fm.ofTree G) x (R x) t) (hP : ∀ q ∈ R x, q.2.toList.length ≤ P) (σ : Tree) :
    Does θ (cutStep G) (.cons x σ) (cutStepW R x σ) (t + 62 * P + 70) := by
  have e1 : Does θ (app G (.hd .id)) (.cons x σ) (R x) (2 + t + 2) := by
    simpa [bindW] using Does.app (p := G) (R := fun _ => R x)
      (Gives.id (θ := θ) (.cons x σ)).hd (d := t) (by simpa using hD)
  have e2 := Gives.after (G := appF (.hd .id) (.tl .id))
    (f := fun o => listT (o.hd.toList ++ o.tl.toList)) (d := 62 * P + 50)
    (e1.cons (Gives.id (θ := θ) (.cons x σ)).tl) (by
      intro q hq
      simp only [List.mem_flatMap, List.map_cons, List.map_nil, List.mem_singleton] at hq
      obtain ⟨q1, hq1, rfl⟩ := hq
      refine (appF_gives (ca := 2) (cb := 2) (xs := q1.2.toList)
        ((listT_toList _).symm ▸ (Gives.id _).hd)
        ((listT_toList _).symm ▸ (Gives.id _).tl)).mono ?_
      have := hP q1 hq1
      omega)
  refine (e2.congr ?_ fun φ => ?_).mono (by omega)
  · intro q hq
    simp only [List.mem_map, List.mem_flatMap, List.map_cons, List.map_nil,
      List.mem_singleton] at hq
    obtain ⟨q1, ⟨q2, hq2, rfl⟩, rfl⟩ := hq
    exact ⟨_, List.mem_map.2 ⟨q2, hq2, rfl⟩, rfl⟩
  · simp [cutStepW, wsum, Function.comp_def, ← List.map_eq_flatMap]

/-- **Composition of cuts** ([AnthropicVPVNP2026], proof of Theorem J.4): running a second cut on
every piece of a first one is a cut. The numbers of pieces multiply, and the second cut and the
concatenation of its pieces are paid once for every piece of the first. -/
theorem IsCut.comp {τ s τ₁ s₁ P₁ t₁ τ₂ s₂ P₂ t₂ : ℕ} {G₁ G₂ : Tree}
    (h₁ : IsCut θ τ s τ₁ s₁ P₁ t₁ G₁) (h₂ : IsCut θ τ₁ s₁ τ₂ s₂ P₂ t₂ G₂) :
    IsCut θ τ s τ₂ s₂ (P₁ * P₂) (t₁ + P₁ * (t₂ + 62 * P₂ + 110) + 100) (cutComp G₁ G₂).code := by
  intro z hz
  obtain ⟨Q₁, hD₁, hQ₁, hv₁⟩ := h₁ z hz
  choose! R hR using h₂
  have hs₁ : ∀ q ∈ Q₁, ∀ x ∈ q.2.toList, x.size ≤ s₁ := fun q hq => (hQ₁ q hq).2
  have hfold : ∀ q ∈ Q₁, Does θ (foldF (cutStep G₂) (.quote .nil) .id) q.2
      (foldW (cutStepW R) q.2.toList .nil) (P₁ * (t₂ + 62 * P₂ + 100) + 30) := by
    intro q hq
    have hl : Gives θ .id q.2 (listT q.2.toList) 1 := (listT_toList q.2).symm ▸ Gives.id _
    refine (foldF_does (Inv := fun _ _ => True) (d := fun _ => t₂ + 62 * P₂ + 70)
      (Gives.quote (θ := θ) .nil q.2) hl (fun x ys σ hx _ => ⟨?_, fun _ _ => trivial⟩)
      trivial).mono ?_
    · obtain ⟨hD, hP, -⟩ := hR x (hs₁ q hq x hx)
      exact cutStep_does hD (fun q' hq' => (hP q' hq').1) σ
    · rw [List.map_const', List.sum_replicate, smul_eq_mul,
        show t₂ + 62 * P₂ + 70 + 30 = t₂ + 62 * P₂ + 100 by omega]
      have := Nat.mul_le_mul_right (t₂ + 62 * P₂ + 100) (hQ₁ q hq).1
      omega
  have hDz : Does θ (app G₁ .id) z Q₁ (1 + t₁ + 2) := by
    simpa [bindW] using Does.app (p := G₁) (R := fun _ => Q₁) (Gives.id (θ := θ) z) (d := t₁)
      (by simpa using hD₁)
  -- every piece at the end is a piece, under the second cut, of a piece of the first
  have hmem : ∀ p ∈ bindW Q₁ fun o => foldW (cutStepW R) o.toList .nil, ∃ q ∈ Q₁,
      p.2.toList.length ≤ P₁ * P₂ ∧
        ∀ y ∈ p.2.toList, ∃ x ∈ q.2.toList, ∃ q' ∈ R x, y ∈ q'.2.toList := by
    intro p hp
    obtain ⟨q, hq, r, hr, h1, -⟩ := mem_bindW hp
    obtain ⟨h2, h3⟩ := mem_foldW_cutStepW (P := P₂)
      (fun x hx q' hq' => ((hR x (hs₁ q hq x hx)).2.1 q' hq').1) hr
    refine ⟨q, hq, h1 ▸ (Nat.mul_le_mul_right P₂ (hQ₁ q hq).1).trans'
      (by simpa [toList] using h2),
      fun y hy => (h3 y (h1 ▸ hy)).resolve_left (by simp [toList])⟩
  refine ⟨bindW Q₁ fun o => foldW (cutStepW R) o.toList .nil, ?_, fun p hp => ?_,
    fun hp => ⟨fun p hp' y hy => ?_, ?_⟩⟩
  · rw [Fm.ofTree_code]
    refine (hDz.lett (R := fun o => foldW (cutStepW R) o.toList .nil) hfold).mono ?_
    have : P₁ * (t₂ + 62 * P₂ + 100) ≤ P₁ * (t₂ + 62 * P₂ + 110) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  · obtain ⟨q, hq, h1, h2⟩ := hmem p hp
    exact ⟨h1, fun y hy => let ⟨x, hx, q', hq', hy'⟩ := h2 y hy
      ((hR x (hs₁ q hq x hx)).2.1 q' hq').2 y hy'⟩
  · obtain ⟨q, hq, -, h2⟩ := hmem p hp'
    exact let ⟨x, hx, q', hq', hy'⟩ := h2 y hy
      ((hR x (hs₁ q hq x hx)).2.2 ((hv₁ hp).1 q hq x hx)).1 q' hq' y hy'
  · rw [(hv₁ hp).2, wsum_bindW]
    refine wsum_congr fun q hq => ?_
    rw [wsum_foldW_cutStepW fun x hx =>
      ((hR x (hs₁ q hq x hx)).2.2 ((hv₁ hp).1 q hq x hx)).2.symm]
    simp [pvProd, toList]

end Cslib.Circuits.Arithmetic.Separation.Cut
