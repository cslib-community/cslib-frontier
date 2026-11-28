/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.Simulation

/-!
# A simulating handler as one simple oracle

A reduction often answers its adversary's queries with a stateful handler that draws private coins
and calls an outer oracle. Run against that oracle, the handler is a single stateful oracle on the
joint state (`Cslib.ProbOracleComp.runWith_run_interpret`). When a simpler oracle, on a state that
represents both the handler's state and the outer oracle's, answers each query as one call of the
handler does, the whole run is the simple oracle's run with its final state represented.

## Main results

* `Cslib.ProbOracleComp.runWith_run_interpret_map`: a handler run against its outer oracle is a
  simple oracle's run, when they agree on each call.
-/

public section

namespace Cslib.ProbOracleComp

open OracleComp (sumHandler)

/-- A stateful handler that draws private coins and calls an outer oracle, run against that oracle,
is a run of a simple oracle whose state `s` represents the handler's state `rep₂ s` and the outer
oracle's state `repE s`, when each call of the simple oracle maps to one call of the handler. -/
theorem runWith_run_interpret_map {Query Query' S₁ S₂ E₁ α : Type} {spec : Query → Type}
    {spec' : Query' → Type}
    (inner : (q : Query) → StateT S₂ (ProbOracleComp spec') (spec q))
    (oOuter : (q : Query') → StateT E₁ PMF (spec' q))
    (oSimple : (q : Query) → StateT S₁ PMF (spec q))
    (rep₂ : S₁ → S₂) (repE : S₁ → E₁)
    (hstep : ∀ q s₁,
      (oSimple q s₁).map (fun p => (p.1, (rep₂ p.2, repE p.2))) =
        (runWith oOuter ((inner q).run (rep₂ s₁)) (repE s₁)).map
          (fun (((a, s₂), e) : (spec q × S₂) × E₁) => (a, s₂, e)))
    (prog : ProbOracleComp spec α) (s₁ : S₁) :
    runWith oOuter ((OracleComp.interpret
      (sumHandler (fun m => StateT.lift (sample (ProbComp.unifFin m))) inner) prog).run
        (rep₂ s₁)) (repE s₁) =
      (runWith oSimple prog s₁).map (fun (a, s') => ((a, rep₂ s'), repE s')) := by
  rw [runWith_run_interpret,
    ← runWith_map_state oSimple _ (fun s => (rep₂ s, repE s)) hstep prog s₁, PMF.map_comp]
  congr 1

end Cslib.ProbOracleComp
