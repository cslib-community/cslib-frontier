/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.MIP.Defs
public import CslibFrontier.Computability.Complexity.Classes.IP.Repetition

/-!
# Sequential repetition against non-communicating provers

`Cslib.Complexity.sequentialRepeat` runs a verifier several times in sequence. Against a family of
non-communicating provers (`Cslib.Complexity.Prover.independent`), the provers after any history
are again an independent family, each restarted from its own state. A bound `ε` on the acceptance of one run
against every independent family bounds `k` runs by `ε ^ k`
(`Cslib.Complexity.acceptProb_sequentialRepeat_independent_le`), as for one prover in
`CslibFrontier/Computability/Complexity/Classes/IP/Repetition.lean`.

## Main results

* `Cslib.Complexity.acceptProb_sequentialRepeat_independent_le`: soundness error `ε ^ k`.
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Probability

/-- **Soundness amplification against non-communicating provers.** If every independent prover
family is accepted by one run with probability at most `ε`, every independent family is accepted
by `k` sequential runs with probability at most `ε ^ k`: after any history the provers are again
an independent family. -/
theorem acceptProb_sequentialRepeat_independent_le {ι : Type} [DecidableEq ι]
    {round : WordOracleComp ι Bool} {ε : ENNReal}
    (h : ∀ P : ι → Prover Unit, acceptProb round (Prover.independent P) ≤ ε) (k : ℕ)
    (P : ι → Prover Unit) :
    acceptProb (sequentialRepeat k round) (Prover.independent P) ≤ ε ^ k :=
  acceptProb_sequentialRepeat_le_of_forall_init _ (fun s =>
    h (fun i => { P i with init := s i })) k

end Cslib.Complexity
