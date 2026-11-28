/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EditDistance.Basic

/-!
# Aligning one letter with a word

The singleton base case of Hirschberg reconstruction scans the target from right to left.
At each suffix it carries the cost and script both for inserting that suffix and for aligning the
source letter with it. Each extension compares replacing the source letter now against inserting
the new target letter before the best alignment already found. The empty target deletes the
source letter, so the scan also considers deleting it and inserting the entire target.
-/

public section

namespace Cslib.Algorithms.Lean.EditDistance

variable {α : Type*}

private structure SingletonColumn (α : Type*) where
  insertCost : ℕ
  insertions : EditScript α
  bestCost : ℕ
  alignment : EditScript α

private def singletonColumn (C : Costs α) (a : α) : List α → SingletonColumn α
  | [] => ⟨0, [], C.del a, [.del a]⟩
  | b :: y =>
    let s := singletonColumn C a y
    let i := C.ins b
    let replaceCost := C.sub a b + s.insertCost
    let skipCost := i + s.bestCost
    let inserts := EditOp.ins b :: s.insertions
    if replaceCost ≤ skipCost then
      ⟨i + s.insertCost, inserts, replaceCost, .sub a b :: s.insertions⟩
    else
      ⟨i + s.insertCost, inserts, skipCost, .ins b :: s.alignment⟩

/-- An optimal alignment from `[a]` to `y`, computed by one scan of the target. If replacing
and inserting the next target letter achieve equal costs, prefer the replacement. -/
def singletonAlign (C : Costs α) (a : α) (y : List α) : EditScript α :=
  (singletonColumn C a y).alignment

private theorem singletonColumn_spec (C : Costs α) (a : α) (y : List α) :
    let s := singletonColumn C a y
    s.insertCost = editDist C [] y ∧ s.insertions = optScript C [] y ∧
      s.bestCost = editDist C [a] y ∧ s.alignment.src = [a] ∧
      s.alignment.tgt = y ∧ s.alignment.cost C = s.bestCost := by
  induction y with
  | nil =>
    simp [singletonColumn, optScript_nil, editDist_cons_nil, EditOp.src, EditOp.tgt, EditOp.cost]
  | cons b y ih =>
    obtain ⟨hi, hs, hb, hsrc, htgt, hcost⟩ := ih
    -- Inserting b and then using the best remaining alignment costs no more than deleting a
    -- and inserting the whole target. The latter move need not be tested separately.
    have hd := editDist_cons_left_le C a [] y
    have hin := optScript_spec C [] y
    rw [optScript_nil] at hin hs
    simp +zetaHave only [singletonColumn]
    split <;> rename_i h
    all_goals
      simp only [hi, hs, hb] at h ⊢
      simp only [editDist_cons_cons, editDist_nil_cons, optScript_nil, List.map_cons,
        EditScript.src_cons, EditScript.tgt_cons, EditScript.cost_cons, EditOp.src, EditOp.tgt,
        EditOp.cost, List.singleton_append, List.nil_append, hsrc, htgt, hcost,
        hin.1, hin.2.1, hin.2.2, hb, true_and, and_true]
      omega

/-- The singleton scan consumes exactly the source letter, produces the target word, and
attains the Wagner–Fischer distance for arbitrary natural-valued letter costs. -/
theorem singletonAlign_spec (C : Costs α) (a : α) (y : List α) :
    (singletonAlign C a y).src = [a] ∧ (singletonAlign C a y).tgt = y ∧
      (singletonAlign C a y).cost C = editDist C [a] y := by
  obtain ⟨_, _, hd, hsrc, htgt, hc⟩ := singletonColumn_spec C a y
  exact ⟨hsrc, htgt, hc.trans hd⟩

end Cslib.Algorithms.Lean.EditDistance
