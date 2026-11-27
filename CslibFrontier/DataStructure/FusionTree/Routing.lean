/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.FusionTree.Tree
public import CslibFrontier.DataStructure.FusionTree.Correction

/-!
# Routing by child-minimum ranks

A constant-time node rank replaces the outer tree's semantic linear scan: a zero rank
stops the search, and a positive rank selects the preceding child pointer.

## Main results

* `Tree.selectChild_eq_rank`: inclusive rank selects the same child as the semantic search.

## References

See [FredmanWillard1993] for multiway fusion-tree descent.
-/

public section

namespace Cslib.DataStructure.FusionTree.Tree

private theorem selectChild_eq_cut (q : ℕ) (cs : List Tree) (t : ℕ) (ht : t ≤ cs.length)
    (hcut : ∀ i (hi : i < cs.length), cs[i].minimum ≤ q ↔ i < t) :
    selectChild q cs = if t = 0 then none else cs[t - 1]? := by
  induction cs generalizing t with
  | nil => simp [selectChild, Nat.eq_zero_of_le_zero ht]
  | cons c cs ih =>
    cases t with
    | zero =>
      have hc : ¬c.minimum ≤ q := mt (hcut 0 (Nat.zero_lt_succ _)).mp (Nat.not_lt_zero 0)
      have htail (i : ℕ) (hi : i < cs.length) : cs[i].minimum ≤ q ↔ i < 0 :=
        (hcut (i + 1) (Nat.succ_lt_succ hi)).trans
          (iff_of_false (Nat.not_lt_zero _) (Nat.not_lt_zero _))
      simp [selectChild, ih 0 (Nat.zero_le _) htail, hc]
    | succ t =>
      have hc : c.minimum ≤ q := (hcut 0 (Nat.zero_lt_succ _)).mpr (Nat.zero_lt_succ t)
      have htail (i : ℕ) (hi : i < cs.length) : cs[i].minimum ≤ q ↔ i < t :=
        (hcut (i + 1) (Nat.succ_lt_succ hi)).trans Nat.succ_lt_succ_iff
      rw [selectChild, ih t (Nat.le_of_succ_le_succ ht) htail]
      cases t with
      | zero => simp [hc]
      | succ t =>
        simp [List.getElem?_eq_getElem (Nat.lt_of_succ_le (Nat.le_of_succ_le_succ ht)), hc]

/-- For strictly increasing child minima, the inclusive full-key rank routes to exactly the
same child as the semantic linear scan. A positive cut uses child index `rank-1`. -/
theorem selectChild_eq_rank (q : ℕ) (cs : List Tree)
    (hsorted : StrictMono (fun i : Fin cs.length => cs[i.val].minimum)) :
    selectChild q cs =
      if upperRank (fun i : Fin cs.length => cs[i.val].minimum) q = 0 then none
      else cs[upperRank (fun i : Fin cs.length => cs[i.val].minimum) q - 1]? := by
  apply selectChild_eq_cut q cs _ (upperRank_le _ _)
  intro i hi
  exact (lt_upperRank_iff hsorted ⟨i, hi⟩).symm

end Cslib.DataStructure.FusionTree.Tree
