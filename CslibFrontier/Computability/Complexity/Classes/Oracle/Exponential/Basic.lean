/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.Classes.Oracle

/-!
# Exponential oracle-clock contract

`IsOracleExpTimeOn` records one finite-control machine whose exponentially bounded run
preserves the complete joint output and external-oracle state. The contract itself assumes
neither bounded external replies nor a clean-machine interface. The exponential-class facade
exports its compilation and class-containment results.
-/

@[expose] public section

namespace Cslib

namespace Probability

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM

/-- One finite machine and an exponential clock `c * 2 ^ (d * n)` in the input length `n` preserve
the full interaction with every shared stateful oracle: `Cslib.Probability.IsOraclePPTOn` with the
polynomial clock replaced by `2 ^ O(n)`. The oracle's computation is external; request
construction and reply access are ordinary machine work. -/
def IsOracleExpTimeOn {Operation α β : Type} [DecidableEq Operation]
    (input : α ↪ List Bool) (output : β ↪ List Bool)
    (program : α → WordOracleComp Operation β) : Prop :=
  Finite Operation ∧ ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
    (machine : Turing.MultiTapePTM k Bool Control Operation) (c d : ℕ),
    ∀ a (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool)) s,
      ProbOracleComp.runWith oracle (output <$> program a) s =
      ProbOracleComp.runWith oracle (machine.runOracle (c * 2 ^ (d * (input a).length)) (input a)) s

end Probability
end Cslib
