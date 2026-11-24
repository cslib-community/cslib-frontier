/-
Copyright (c) 2026 Samuel Schlesinger, Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Leaves
public import Cslib.MachineLearning.PACLearning.Defs

/-!
# The concept class of small decision trees

`UniformLearning.decisionTreeClass ι L` is the class of Boolean functions on `ι → Bool` computed by
some decision tree with at most `L` leaves. It is learned with membership queries by the
Kushilevitz–Mansour algorithm (`UniformLearning.kmLearner_learns_decisionTree`) and from uniform
random examples by the low-degree algorithm
(`UniformLearning.lowDegreeLearner_learns_decisionTreeClass`).

## Main definitions

* `Cslib.MachineLearning.UniformLearning.decisionTreeClass`: the functions computed by decision
  trees with at most `L` leaves.
-/

@[expose] public section

namespace Cslib.MachineLearning.UniformLearning

open PACLearning

variable (ι : Type*)

/-- The functions computed by decision trees with at most `L` leaves. -/
def decisionTreeClass (L : ℕ) : ConceptClass (ι → Bool) Bool :=
  {f | ∃ t : DecisionTree ι Bool, t.Computes f ∧ t.leafCount ≤ L}

end Cslib.MachineLearning.UniformLearning
