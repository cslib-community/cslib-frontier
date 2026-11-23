/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Composition
public import CslibFrontier.Languages.Probabilistic.QueryCount

/-!
# Substituting and budgeting Boolean query programs

Translating query substitution on decision trees into free programs gives oracle substitution.
A bound on weighted structural depth is precisely an oracle cost bound. Both bounds include
branches that answer a repeated variable inconsistently with previous replies. For trees returning
a value in a higher universe, postprocessing the result to `Unit` retains the query structure and
puts the result in the universe of the Boolean replies required by `OracleComp.IsCostBounded`.

## Main results

* `Cslib.DecisionTree.toFreeM_substitute` translates query substitution into oracle substitution.
* `Cslib.DecisionTree.weightedDepth_le_iff_isCostBounded_map_unit` characterizes the query
  budget after discarding the result, for every result universe.
* `Cslib.DecisionTree.weightedDepth_le_iff_isCostBounded` gives the budget directly for
  programs whose result is in the Boolean replies' universe.
-/

public section

namespace Cslib.DecisionTree

open PFunctor

variable {ι κ β : Type*}

/-- Substituting Boolean query subroutines agrees with free-program substitution. -/
theorem toFreeM_substitute (t : DecisionTree ι β) (s : ι → DecisionTree κ Bool) :
    (t.substitute s).toFreeM = OracleComp.substitute (fun i => (s i).toFreeM) t.toFreeM := by
  induction t with
  | leaf a => rfl
  | node i l r il ir =>
    rw [substitute_node, toFreeM_bind]
    change PFunctor.FreeM.bind (s i).toFreeM _ = PFunctor.FreeM.bind (s i).toFreeM _
    congr 1
    funext b
    cases b <;> assumption

/-- The weighted depth bounds precisely the calls of the free program, even when its result is in
a higher universe than its Boolean replies. Discarding the result preserves every query branch. -/
theorem weightedDepth_le_iff_isCostBounded_map_unit (t : DecisionTree ι β)
    (w : ι → ℕ) (n : ℕ) :
    t.weightedDepth w ≤ n ↔ OracleComp.IsCostBounded w (FreeM.map (fun _ => ()) t.toFreeM) n := by
  induction t generalizing n with
  | leaf a => exact ⟨fun _ => .pure () n, fun _ => Nat.zero_le _⟩
  | node i l r il ir =>
    change max (l.weightedDepth w) (r.weightedDepth w) + w i ≤ n ↔
      OracleComp.IsCostBounded w (FreeM.liftBind i fun b : Bool =>
        FreeM.map (fun _ => ()) (cond b r.toFreeM l.toFreeM)) n
    rw [OracleComp.IsCostBounded.liftBind_iff, Bool.forall_bool]
    simp only [Bool.cond_false, Bool.cond_true, ← il, ← ir]
    omega

/-- For a result in the Boolean replies' universe, weighted depth is the query budget of the
translated program itself. -/
theorem weightedDepth_le_iff_isCostBounded {γ : Type} (t : DecisionTree ι γ)
    (w : ι → ℕ) (n : ℕ) :
    t.weightedDepth w ≤ n ↔ OracleComp.IsCostBounded w t.toFreeM n := by
  simpa only [FreeM.map_eq_map, OracleComp.isCostBounded_map_iff] using
    t.weightedDepth_le_iff_isCostBounded_map_unit w n

end Cslib.DecisionTree
