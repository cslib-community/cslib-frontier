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
branches that answer a repeated variable inconsistently with previous replies.
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

/-- A weighted structural depth bound is precisely a free-program query budget. -/
theorem weightedDepth_le_iff_isCostBounded (t : DecisionTree ι β)
    (w : ι → ℕ) (n : ℕ) :
    t.weightedDepth w ≤ n ↔ OracleComp.IsCostBounded w t.toFreeM n := by
  induction t generalizing n with
  | leaf a => exact ⟨fun _ => .pure a n, fun _ => Nat.zero_le _⟩
  | node i l r il ir =>
    change max (l.weightedDepth w) (r.weightedDepth w) + w i ≤ n ↔
      OracleComp.IsCostBounded w
        (FreeM.liftBind i fun b : Bool => cond b r.toFreeM l.toFreeM) n
    rw [OracleComp.IsCostBounded.liftBind_iff, Bool.forall_bool]
    simp only [Bool.cond_false, Bool.cond_true, ← il, ← ir]
    omega

end Cslib.DecisionTree
