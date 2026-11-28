/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.EditDistance.HirschbergBase
public import CslibFrontier.Algorithms.Lean.EditDistance.HirschbergSplit

/-!
# Optimal alignments by Hirschberg's divide-and-conquer algorithm

Split the source in half and use the forward and reverse score rows to find the target column
where some optimal alignment crosses the split. Solve the two smaller alignment problems, then
join their scripts. The empty and singleton cases construct scripts directly. Hirschberg gives
Algorithm C for common subsequences on p. 342 and its minimum-trace-cost variant on p. 343
[Hirschberg1975].

`hirschbergAlign` places the shorter input across the score row. When it exchanges the inputs,
it transposes the costs and emits operations in the original direction. This works for arbitrary
natural insertion, deletion and substitution costs. Each leaf prepends its operations to the output
tail, so joining two subproblems takes no traversal of their scripts.
-/

public section

namespace Cslib.Algorithms.Lean.EditDistance

variable {α β : Type*}

open EditScript

/-- Costs of running an alignment in the opposite direction. -/
@[expose] def Costs.transpose (C : Costs α) : Costs α :=
  ⟨C.ins, C.del, fun a b => C.sub b a⟩

/-- Reverse the direction of a single edit operation. -/
@[expose] def EditOp.transpose : EditOp α → EditOp α
  | .del a => .ins a
  | .ins b => .del b
  | .sub a b => .sub b a

/-- Swapping the sides of each operation exchanges the words consumed and produced and
charges the transposed costs. Operations stay in their original order. -/
theorem EditScript.transpose_spec (C : Costs α) (s : EditScript α) :
    src (s.map EditOp.transpose) = s.tgt ∧ tgt (s.map EditOp.transpose) = s.src ∧
      cost C (s.map EditOp.transpose) = s.cost C.transpose := by
  induction s with
  | nil => simp
  | cons o s ih =>
    obtain ⟨hs, ht, hc⟩ := ih
    cases o <;> simp [EditOp.transpose, EditOp.src, EditOp.tgt, EditOp.cost,
      Costs.transpose, hs, ht, hc]

private theorem editDist_le_transpose (C : Costs α) (x y : List α) :
    editDist C x y ≤ editDist C.transpose y x := by
  let s := optScript C.transpose y x
  obtain ⟨hs, ht, hc⟩ := EditScript.transpose_spec C s
  simpa only [hs, ht, hc, s, src_optScript, tgt_optScript, cost_optScript] using
    editDist_le_cost C (s.map EditOp.transpose)

/-- Swapping the input words preserves edit distance when the costs are transposed as well. -/
theorem editDist_transpose (C : Costs α) (x y : List α) :
    editDist C.transpose y x = editDist C x y :=
  le_antisymm (editDist_le_transpose C.transpose y x) (editDist_le_transpose C x y)

/-- Recurse on Hirschberg's selected subproblems. The combining function receives the two source
halves, the unsplit target, the chosen column, and the results of its left and right children.
The same fold constructs the alignment and describes the work of its row computations. -/
@[expose] def hirschbergFold (C : Costs α) (emptyLeft emptyRight : List α → β)
    (singleton : α → List α → β) (combine : List α → List α → List α → ℕ → β → β → β) :
    List α → List α → β
  | [], y => emptyLeft y
  | a :: xs, [] => emptyRight (a :: xs)
  | [a], b :: ys => singleton a (b :: ys)
  | a :: b :: xs, c :: ys =>
    let x := a :: b :: xs
    let y := c :: ys
    let left := x.take (x.length / 2)
    let right := x.drop (x.length / 2)
    let k := bestSplit C left right y
    combine left right y k
      (hirschbergFold C emptyLeft emptyRight singleton combine left (y.take k))
      (hirschbergFold C emptyLeft emptyRight singleton combine right (y.drop k))
termination_by x _ => x.length
decreasing_by all_goals simp; omega

private def buildScript (C : Costs α) (emit : EditOp α → EditOp α) :
    List α → List α → EditScript α → EditScript α :=
  hirschbergFold C (fun y tail => y.foldr (fun b out => emit (.ins b) :: out) tail)
    (fun x tail => x.foldr (fun a out => emit (.del a) :: out) tail)
    (fun a y tail => (singletonAlign C a y).foldr (fun o out => emit o :: out) tail)
    (fun _ _ _ _ left right tail => left (right tail))

/-- Hirschberg alignment reconstructed with its shorter input across the score rows. -/
def hirschbergAlign (C : Costs α) (x y : List α) : EditScript α :=
  if y.length ≤ x.length then buildScript C id x y []
  else buildScript C.transpose EditOp.transpose y x []

private theorem buildScript_spec (C : Costs α) (x y : List α) :
    ∃ s : EditScript α, s.src = x ∧ s.tgt = y ∧ s.cost C = editDist C x y ∧
      ∀ emit tail, buildScript C emit x y tail = s.map emit ++ tail := by
  match x, y with
  | [], ys =>
    obtain ⟨hs, ht, hc⟩ := optScript_spec C [] ys
    refine ⟨optScript C [] ys, hs, ht, hc, ?_⟩
    intro emit tail
    simp [buildScript, hirschbergFold, optScript_nil, List.map_map]
  | a :: xs, [] =>
    have hdel (z : List α) : optScript C z [] = z.map EditOp.del := by
      induction z <;> simp [optScript_nil, optScript_cons_nil, *]
    obtain ⟨hs, ht, hc⟩ := optScript_spec C (a :: xs) []
    refine ⟨optScript C (a :: xs) [], hs, ht, hc, ?_⟩
    intro emit tail
    simp [buildScript, hirschbergFold, hdel, List.map_map]
  | [a], b :: ys =>
    obtain ⟨hs, ht, hc⟩ := singletonAlign_spec C a (b :: ys)
    refine ⟨singletonAlign C a (b :: ys), hs, ht, hc, ?_⟩
    intro emit tail
    simp [buildScript, hirschbergFold]
  | a :: b :: xs, c :: ys =>
    let x := a :: b :: xs
    let y := c :: ys
    let left := x.take (x.length / 2)
    let right := x.drop (x.length / 2)
    let k := bestSplit C left right y
    obtain ⟨s, hs, ht, hc, hbuild⟩ := buildScript_spec C left (y.take k)
    obtain ⟨t, hs', ht', hc', hbuild'⟩ := buildScript_spec C right (y.drop k)
    refine ⟨s ++ t, ?_, ?_, ?_, ?_⟩
    · rw [src_append, hs, hs', List.take_append_drop]
    · rw [tgt_append, ht, ht', List.take_append_drop]
    · rw [cost_append, hc, hc', bestSplit_spec, List.take_append_drop]
    · intro emit tail
      simp only [buildScript, hirschbergFold]
      change buildScript C emit left (y.take k) (buildScript C emit right (y.drop k) tail) = _
      rw [hbuild', hbuild, List.map_append, List.append_assoc]
termination_by x.length
decreasing_by all_goals simp [*]; omega

/-- Hirschberg reconstruction consumes the entire source, produces the entire target, and
attains the Wagner–Fischer minimum for arbitrary natural edit costs. -/
theorem hirschbergAlign_spec (C : Costs α) (x y : List α) :
    (hirschbergAlign C x y).src = x ∧ (hirschbergAlign C x y).tgt = y ∧
      (hirschbergAlign C x y).cost C = editDist C x y := by
  unfold hirschbergAlign
  split
  · obtain ⟨s, hs, ht, hc, h⟩ := buildScript_spec C x y
    rw [h, List.map_id, List.append_nil]
    exact ⟨hs, ht, hc⟩
  · obtain ⟨s, hs, ht, hc, h⟩ := buildScript_spec C.transpose y x
    obtain ⟨hst, htt, hct⟩ := EditScript.transpose_spec C s
    rw [h, List.append_nil]
    exact ⟨hst.trans ht, htt.trans hs, hct.trans (hc.trans (editDist_transpose C x y))⟩

end Cslib.Algorithms.Lean.EditDistance
