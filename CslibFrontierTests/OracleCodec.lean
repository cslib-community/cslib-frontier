/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import CslibFrontier.Languages.Probabilistic.Oracle.Codec
import CslibFrontier.Languages.Probabilistic.Oracle.Norm

/-! # Typed views of word oracles -/

namespace CslibFrontierTests.OracleCodec

open Cslib

private def wordAdversary :
    ProbOracleComp (fun _ : Unit × List Bool => List Bool) (List Bool × List Bool) := do
  let rejected ← ProbOracleComp.query ((), [true])
  let reply ← ProbOracleComp.query ((), [true, false])
  return (rejected, reply)

private noncomputable def echo (x : BitString 2) : StateT ℕ PMF (BitString 2) := fun calls =>
  PMF.pure (x, calls + 1)

-- The one-bit request carries no 2-bit query: it is answered `[]` without a call, so only the
-- well-formed request reaches the typed oracle and advances its counter.
example (calls : ℕ) :
    ProbOracleComp.runWith echo ((OracleCodec.bitString 2).adapt wordAdversary) calls =
      PMF.pure (([], [true, false]), calls + 1) := by
  rw [OracleCodec.runWith_adapt]
  simp only [wordAdversary, runWith_norm, pmf_norm]
  simp only [OracleCodec.wordOracle, OracleCodec.bitString]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, OfNat.one_ne_ofNat, ↓reduceIte]
  change (PMF.pure ([], calls)).bind (fun x =>
    (PMF.map (Prod.map List.ofFn id) (echo (BitString.ofList 2 [true, false]) x.2)).bind
      fun x_1 => PMF.pure ((x.1, x_1.1), x_1.2)) = _
  simp [echo, BitString.ofList]

-- Adapting removes the malformed request from the program itself.
example : (OracleCodec.bitString 2).adapt wordAdversary = (do
    let reply ← ProbOracleComp.query (spec := fun _ : BitString 2 => BitString 2)
      (BitString.ofList 2 [true, false])
    return ([], List.ofFn reply)) := by
  simp [wordAdversary, OracleCodec.wordOracle, OracleCodec.bitString]

-- The word program's query budget carries over to the adapted program.
example : ((OracleCodec.bitString 2).adapt wordAdversary).IsQueryBounded 2 :=
  (OracleCodec.bitString 2).isQueryBounded_adapt <| by
    simpa [wordAdversary] using (ProbOracleComp.IsQueryBounded.query ((), [true])).bind fun _ =>
      (ProbOracleComp.IsQueryBounded.query ((), [true, false])).bind fun _ =>
        OracleComp.IsCostBounded.pure _ 0

end CslibFrontierTests.OracleCodec
