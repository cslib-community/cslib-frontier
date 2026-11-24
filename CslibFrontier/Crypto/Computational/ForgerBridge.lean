/-
Copyright (c) 2026 Chris Henson, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Signature
public import CslibFrontier.Crypto.Computational.Signature.Scheme
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation

/-!
# Shared word-forger adapter and state-simulation bridge

Word-level cryptographic games run a `Forger` against a stateful word oracle (`StateT σ ProbComp`),
whereas typed forgery experiments (`forgeExperiment`) run a `ProbOracleComp` adversary via
`ProbOracleComp.runLogWith` against a logging signer. This module provides the shared word-forger
adapter `Forger.toTyped` and the representation-polymorphic simulation lemma
`Forger.eval_runLogWith_rename_state` consumed by both `MAC` and `Signature/Bridge`.

## Main definitions

* `Cslib.Crypto.Forger.toTyped`: view a word-level `Forger` at security parameter `n` as a typed
  forger forwarding `request.2` to the signing/tagging oracle while leaving coin tosses unchanged.

## Main results

* `Cslib.Crypto.Forger.eval_runLogWith_rename_state`: running a word oracle program with renamed
  requests against a logging signer, and mapping the log by `represent`, has the same distribution
  as running it against the word oracle whose state is `represent log` whenever each oracle step
  agrees under `represent`.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability
open OracleComp (sumHandler)

/-- The typed forger played by the word forger `adversary` at parameter `n` on input `pk`: each
request `((), m)` becomes the query `m`, and private sampling is unchanged. -/
def Forger.toTyped (adversary : Forger) (n : ℕ) :
    Signature.Forger (List Bool) (List Bool) (List Bool) :=
  fun pk =>
    OracleComp.interpret
      (sumHandler (fun k => OracleComp.query (spec := probOracleSpec fun _ : List Bool => List Bool)
        (.inl k)) (fun request => ProbOracleComp.query request.2))
      (adversary n pk)

/-- Running a word forger with renamed requests against a logging signer, and mapping the log by
`represent`, is running it against the word oracle whose state is `represent log` whenever each
oracle call agrees under `represent`. -/
theorem Forger.eval_runLogWith_rename_state {Q σ α : Type} (program : WordOracleComp Unit α)
    (decode : List Bool → Q) (signer : List (Q × List Bool) → Q → Option (ProbComp (List Bool)))
    (oracle : Unit × List Bool → StateT σ ProbComp (List Bool))
    (represent : List (Q × List Bool) → σ)
    (step : ∀ (request : Unit × List Bool) (log : List (Q × List Bool)),
      (ProbComp.eval (ProbOracleComp.logOracle signer (decode request.2) log)).map
          (fun (a, log') => (a, represent log')) =
        ProbComp.eval (oracle request (represent log))) :
    (ProbComp.eval (ProbOracleComp.runLogWith (OracleComp.interpret
        (sumHandler (fun k => OracleComp.query (spec := probOracleSpec fun _ : Q => List Bool)
          (.inl k)) (fun request => ProbOracleComp.query (decode request.2)))
        program) signer)).map
        (fun (a, log) => (a, represent log)) =
      ProbComp.eval ((OracleComp.interpret
        (sumHandler (fun k => StateT.lift (ProbComp.unifFin k)) oracle) program).run
        (represent [])) := by
  have hhandler : (fun q => OracleComp.interpret
      (sumHandler (fun k => StateT.lift (ProbComp.unifFin k)) (ProbOracleComp.logOracle signer))
      (sumHandler (fun k => OracleComp.query (spec := probOracleSpec fun _ : Q => List Bool)
          (.inl k)) (fun request : Unit × List Bool => ProbOracleComp.query (decode request.2))
        q)) =
      sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (fun request : Unit × List Bool => ProbOracleComp.logOracle signer (decode request.2)) := by
    funext q
    cases q <;> simp [ProbOracleComp.query]
  rw [ProbOracleComp.runLogWith, ProbOracleComp.runState, OracleComp.interpret_interpret,
    hhandler, ProbOracleComp.eval_run_interpret, ProbOracleComp.eval_run_interpret]
  exact ProbOracleComp.run_interpret_map_state
    (fun request log => ProbComp.eval (ProbOracleComp.logOracle signer (decode request.2) log))
    (fun request s => ProbComp.eval (oracle request s))
    represent step program []

end Cslib.Crypto
