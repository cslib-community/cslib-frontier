/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm

/-!
# Tests for `interp_norm`

`simp only [interp_norm, pmf_norm]` runs `OracleComp.interpret handler program` on a concrete
`program` and leaves the handler's calls at explicit states:
1. a handler over `PMF`, with and without state, through an embedded sample, queries, `<$>` and
   `pure`;
2. the other handlers: `ProbComp.unifFin` under `ProbComp.eval`, with and without state, and a
   handler that makes oracle calls itself, for which `interp_norm` is used alone;
3. raw `Sum.inl` and `Sum.inr` queries, and a handler given by a `fun`;
4. a black-box adversary, whose run stays in `OracleComp.interpret` form;
5. a hypothesis, a definition unfolded in the same call, and a goal with nothing to step.
-/

namespace CslibFrontierTests.InterpNorm

open Cslib

/-- A client with one private coin, two queries, a map and a return. -/
private noncomputable def client : ProbOracleComp (fun _ : Bool => ℕ) ℕ := do
  let c ← ProbOracleComp.sample (ProbComp.uniform Bool)
  let a ← ProbOracleComp.query c
  let b ← (· + 1) <$> ProbOracleComp.query (!c)
  return a + b

/-! ### 1. Stateful handler over `PMF` -/

-- The state is threaded through the two calls; the coin is drawn from its distribution.
example (oracle : Bool → StateT ℕ PMF ℕ) (s : ℕ) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle) client).run s =
    (ProbComp.eval (ProbComp.uniform Bool)).bind fun c =>
      ((oracle c).run s).bind fun x =>
        ((oracle !c).run x.2).bind fun y => PMF.pure (x.1 + (y.1 + 1), y.2) := by
  simp only [client, interp_norm, pmf_norm]

-- No state: `ProbComp.unifOracle` answers the coin and `StateT.run` does not appear.
example (oracle : Bool → PMF ℕ) :
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle oracle) client =
    (ProbComp.eval (ProbComp.uniform Bool)).bind fun c =>
      (oracle c).bind fun a => (oracle !c).bind fun b => PMF.pure (a + (b + 1)) := by
  simp only [client, interp_norm, pmf_norm]

/-! ### 2. Other handlers -/

-- A `ProbComp` handler under `ProbComp.eval`: `pmf_norm` distributes `eval` over the result.
example (oracle : Bool → StateT ℕ ProbComp ℕ) (s : ℕ) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifFin n)) oracle) client).run s) =
    (ProbComp.eval (ProbComp.uniform Bool)).bind fun c =>
      (ProbComp.eval ((oracle c).run s)).bind fun x =>
        (ProbComp.eval ((oracle !c).run x.2)).bind fun y => PMF.pure (x.1 + (y.1 + 1), y.2) := by
  simp only [client, interp_norm, pmf_norm]

-- No state: `StateT.run` does not appear and the same call applies.
example (oracle : Bool → ProbComp ℕ) :
    ProbComp.eval
      (OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin oracle) client) =
    (ProbComp.eval (ProbComp.uniform Bool)).bind fun c =>
      (ProbComp.eval (oracle c)).bind fun a =>
        (ProbComp.eval (oracle !c)).bind fun b => PMF.pure (a + (b + 1)) := by
  simp only [client, interp_norm, pmf_norm]

-- A handler that calls another oracle: the result stays in `ProbOracleComp`, whose `>>=` and
-- `<$>` are not `pmf_norm`'s to normalize, so `interp_norm` is used alone.
example (oracle : Bool → StateT ℕ (ProbOracleComp fun _ : ℕ => Bool) ℕ) (s : ℕ) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
        oracle)
      (do
        let a ← ProbOracleComp.query true
        let b ← ProbOracleComp.query (a == 0)
        return a + b)).run s =
    (do
      let p ← (oracle true).run s
      let q ← (oracle (p.1 == 0)).run p.2
      pure (p.1 + q.1, q.2)) := by
  simp only [interp_norm]

/-! ### 3. Raw queries and a handler given by a `fun` -/

-- `Sum.inl n` is a uniform draw and `Sum.inr q` an oracle call.
example (oracle : Bool → StateT ℕ PMF ℕ) (s n : ℕ) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (do
        let c ← OracleComp.query (spec := probOracleSpec fun _ : Bool => ℕ) (Sum.inl n)
        let a ← OracleComp.query (spec := probOracleSpec fun _ : Bool => ℕ) (Sum.inr (c.val == 0))
        return a + 1)).run s =
    (ProbComp.unifOracle n).bind fun c =>
      ((oracle (c.val == 0)).run s).bind fun x => PMF.pure (x.1 + 1, x.2) := by
  simp only [interp_norm, pmf_norm]

-- A handler written as `fun q count => …` is left applied through `StateT.run`; unfolding
-- `StateT.run` afterwards exposes its body.
example (s : ℕ) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
        (fun (q : ℕ) (count : ℕ) => PMF.pure (q + count, count + 1)))
      (do
        let a ← ProbOracleComp.query 5
        let b ← ProbOracleComp.query a
        return a + b)).run s =
    PMF.pure (5 + s + (5 + s + (s + 1)), s + 1 + 1) := by
  simp only [interp_norm, pmf_norm]
  simp only [StateT.run, pmf_norm]

/-! ### 4. Black-box adversary -/

-- The steps around `adversary a` are taken; its own run is kept, at the state it starts from.
example (oracle : Bool → StateT ℕ PMF ℕ) (s : ℕ)
    (adversary : ℕ → ProbOracleComp (fun _ : Bool => ℕ) Bool) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (do
        let a ← ProbOracleComp.query true
        let b ← adversary a
        let c ← ProbOracleComp.query b
        return a + c)).run s =
    ((oracle true).run s).bind fun x =>
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (adversary x.1)).run x.2).bind fun y =>
          ((oracle y.1).run y.2).bind fun z => PMF.pure (x.1 + z.1, z.2) := by
  simp only [interp_norm, pmf_norm]

/-! ### 5. Hypotheses and goals with nothing to step -/

example (oracle : Bool → StateT ℕ PMF ℕ) (s : ℕ) (P : PMF (ℕ × ℕ) → Prop)
    (h : P ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      ((· + 1) <$> ProbOracleComp.query true)).run s)) :
    P (((oracle true).run s).map fun x => (x.1 + 1, x.2)) := by
  simp only [interp_norm, pmf_norm] at h
  exact h

-- Without an interpreter in the goal the set does nothing: it holds no monad law of its own.
example (p : PMF ℕ) (f : ℕ → PMF ℕ) (P : PMF ℕ → Prop) (h : P ((p.bind PMF.pure).bind f)) :
    P ((p.bind PMF.pure).bind f) := by
  fail_if_success simp only [interp_norm]
  exact h

end CslibFrontierTests.InterpNorm
