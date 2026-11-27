/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Probabilistic.Oracle
import CslibFrontier.Languages.Probabilistic.Oracle.Norm

/-!
# Tests for `runWith_norm`

Verifies that `simp only [runWith_norm, pmf_norm]` (`runWith_norm` is priority-ordered) reduces:
1. black-box `WordOracleComp` adversaries inside closed
   `ProbComp.eval ((OracleComp.interpret …).run s)` and `ProbComp.eval (·.run oracle)` experiments
   (including nested stateful reduction handlers) to `ProbOracleComp.runWith` or
   `OracleComp.evalWith`, without getting stuck inside `StateT.run` or `ProbOracleComp.run`;
2. concrete multi-step `do` programs mixing `ProbOracleComp.sample`, `ProbOracleComp.query`, `pure`,
   and `<$>` into `PMF.bind` / `PMF.pure` in one pass;
3. stateless and stateful handler substitutions (`ProbOracleComp.simulate`,
   `runWith_interpret_sumHandler_eta`, `runWith_simulate_eta`, `evalWith_sumHandler_simulate`,
   `evalWith_interpret_sumHandler`, `runWith_run_interpret`, `runWith_lift`, `runWith_memoryless`,
   and `runWith_pure_state`); and
4. stateless `OracleComp.evalWith` and `ProbOracleComp.run` on concrete `do` programs.
-/

namespace CslibFrontierTests.RunWithNorm

open Cslib Cslib.Probability

/-! ### 1. Black-box adversary inside a closed game and nested reduction handler -/

section BlackBoxAdversary

-- Direct closed run of a black-box `WordOracleComp Op Bool` adversary folds to `runWith`.
example {Op State : Type} (oracle : Op × List Bool → StateT State ProbComp (List Bool))
    (adversary : ℕ → WordOracleComp Op Bool) (n : ℕ) (s₀ : State) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k)) oracle)
      (adversary n)).run s₀) =
    ProbOracleComp.runWith (fun q s => ProbComp.eval (oracle q s)) (adversary n) s₀ := by
  simp only [runWith_norm, pmf_norm]

-- Closed security-game experiment wrapping a stateful reduction around a black-box adversary:
-- `runWith_norm` folds the outer run to `runWith`, steps the reduction's `sample` and `return`,
-- and collapses the inner `run` via `runWith_run_interpret` without `OracleComp.interpret_bind`
-- breaking the outer `.run`.
private def reduction {Op HState : Type} (keyGen : ℕ → ProbComp (List Bool))
    (inner : List Bool → Op × List Bool → StateT HState (WordOracleComp Op) (List Bool))
    (h₀ : HState) (adversary : ℕ → WordOracleComp Op Bool) (n : ℕ) :
    WordOracleComp Op Bool := do
  let aux ← ProbOracleComp.sample (keyGen n)
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler
      (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
      (inner aux))
    (adversary n)).run h₀
  return !out.1

example {Op HState EState : Type} (keyGen : ℕ → ProbComp (List Bool))
    (inner : List Bool → Op × List Bool → StateT HState (WordOracleComp Op) (List Bool))
    (extOracle : Op × List Bool → StateT EState ProbComp (List Bool))
    (adversary : ℕ → WordOracleComp Op Bool) (n : ℕ) (h₀ : HState) (e₀ : EState) :
    ProbComp.eval (do
      let seed ← keyGen n
      let out ← (OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k)) extOracle)
        (reduction keyGen inner h₀ adversary n)).run e₀
      return (seed.isEmpty && out.1)) =
    (ProbComp.eval (keyGen n)).bind fun seed =>
      (ProbComp.eval (keyGen n)).bind fun aux =>
        (ProbOracleComp.runWith
          (fun q st =>
            (ProbOracleComp.runWith (fun q' s' => ProbComp.eval (extOracle q' s'))
              ((inner aux q).run st.1) st.2).map fun r => (r.1.1, r.1.2, r.2))
          (adversary n) (h₀, e₀)).bind fun r =>
          PMF.pure (seed.isEmpty && !r.1) := by
  simp only [reduction, runWith_norm, pmf_norm]

-- Spelled-out `ProbComp.unifOracle` sum-handler run folds directly to `ProbOracleComp.runWith`.
example {Op State : Type} (oracle : Op × List Bool → StateT State PMF (List Bool))
    (adversary : ℕ → WordOracleComp Op Bool) (n : ℕ) (s₀ : State) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k)) oracle)
      (adversary n)).run s₀ =
    ProbOracleComp.runWith oracle (adversary n) s₀ := by
  simp only [runWith_norm]

end BlackBoxAdversary

/-! ### 2. Concrete multi-step `do` program with `sample`, `query`, `pure`, and `<$>` -/

section ConcreteDoProgram

private def concreteProg : ProbOracleComp (fun _ : Bool => Nat) (Bool × Nat) := do
  let coin ← ProbOracleComp.sample (do
    let i ← ProbComp.unifFin 1
    return (i.val == 1))
  let first ← ProbOracleComp.query coin
  let bumped ← (· + 1) <$> ((· * 2) <$> ProbOracleComp.query (!coin))
  return (coin, first + bumped)

example (oracle : Bool → StateT Nat PMF Nat) (s₀ : Nat) :
    ProbOracleComp.runWith oracle concreteProg s₀ =
      (ProbComp.eval (ProbComp.unifFin 1)).bind fun i =>
        (oracle (i.val == 1) s₀).bind fun x =>
          (oracle (!(i.val == 1)) x.2).bind fun y =>
            PMF.pure ((i.val == 1, x.1 + (y.1 * 2 + 1)), y.2) := by
  simp only [concreteProg, runWith_norm, pmf_norm]

end ConcreteDoProgram

/-! ### 3. Handler substitution and memoryless `StateT.lift` oracles -/

section HandlerSubstitution

-- Stateless handler substitution (`runWith_interpret_sumHandler`) on a black-box program.
example {State : Type} (oracle : Bool → StateT State PMF Nat)
    (program : ProbOracleComp (fun _ : Bool => Nat) Bool) (s₀ : State) :
    ProbOracleComp.runWith oracle
      (OracleComp.interpret
        (OracleComp.sumHandler
          (fun n => ProbOracleComp.sample (ProbComp.unifFin n))
          (fun q => (· + 1) <$> ProbOracleComp.query (!q)))
        program) s₀ =
    ProbOracleComp.runWith
      (fun q s => (oracle (!q) s).map (Prod.map (· + 1) id))
      program s₀ := by
  simp only [runWith_norm, pmf_norm]

-- Stateless handler substitution on a concrete `do` program normalizes all the way to `PMF.bind`.
example {State : Type} (oracle : Bool → StateT State PMF Nat) (q₀ : Bool) (s₀ : State) :
    ProbOracleComp.runWith oracle
      (OracleComp.interpret
        (OracleComp.sumHandler
          (fun n => ProbOracleComp.sample (ProbComp.unifFin n))
          (fun q => (· + 1) <$> ProbOracleComp.query (!q)))
        (do
          let x ← ProbOracleComp.query q₀
          return x * 3)) s₀ =
    (oracle (!q₀) s₀).bind fun r => PMF.pure ((r.1 + 1) * 3, r.2) := by
  simp only [runWith_norm, pmf_norm]

-- Memoryless lifted oracle (`runWith_lift`) on a concrete `ProbOracleComp` `do` program.
example (h : Bool → PMF Nat) (s₀ : Nat) :
    ProbOracleComp.runWith (fun q => StateT.lift (h q))
      (do
        let k ← ProbOracleComp.sample (ProbComp.unifFin 2)
        let v ← ProbOracleComp.query (k.val == 0)
        return v + k.val) s₀ =
    (ProbComp.eval (ProbComp.unifFin 2)).bind fun k =>
      (h (k.val == 0)).bind fun v =>
        PMF.pure (v + k.val, s₀) := by
  simp only [runWith_norm, pmf_norm]

-- `ProbOracleComp.simulate` under `ProbOracleComp.runWith` on a black-box adversary steps concrete
-- handler programs via `runWith_simulate_eta` without unfolding `adversary`.
example {State : Type} (oracle : Bool → StateT State PMF Nat)
    (program : ProbOracleComp (fun _ : Bool => Nat) Bool) (s₀ : State) :
    ProbOracleComp.runWith oracle
      (ProbOracleComp.simulate (fun q => (· + 1) <$> ProbOracleComp.query (!q)) program) s₀ =
    ProbOracleComp.runWith
      (fun q s => (oracle (!q) s).map (Prod.map (· + 1) id))
      program s₀ := by
  simp only [runWith_norm, pmf_norm]

-- Nested `ProbOracleComp.simulate` over a stateful inner `(OracleComp.interpret …).run h₀` folds
-- via `runWith_simulate_eta` and `runWith_run_interpret` without `simulate_bind` breaking `.run`.
example {Op HState EState : Type}
    (outer : Op × List Bool → WordOracleComp Op (List Bool))
    (inner : Op × List Bool → StateT HState (WordOracleComp Op) (List Bool))
    (extOracle : Op × List Bool → StateT EState PMF (List Bool))
    (adversary : ℕ → WordOracleComp Op Bool) (n : ℕ) (h₀ : HState) (e₀ : EState) :
    ProbOracleComp.runWith extOracle
      (ProbOracleComp.simulate outer
        ((OracleComp.interpret
          (OracleComp.sumHandler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            inner)
          (adversary n)).run h₀)) e₀ =
    (ProbOracleComp.runWith
      (fun q st =>
        (ProbOracleComp.runWith (fun q' s' => ProbOracleComp.runWith extOracle (outer q') s')
          ((inner q).run st.1) st.2).map fun r => (r.1.1, r.1.2, r.2))
      (adversary n) (h₀, e₀)).map (fun r => ((r.1, r.2.1), r.2.2)) := by
  simp only [runWith_norm, pmf_norm]

-- Memoryless raw oracle (`runWith_memoryless`) and deterministic state-preserving oracle
-- (`runWith_pure_state`) with `.map Prod.fst` collapse to `OracleComp.evalWith` in one pass.
example {State : Type} (h : Bool → PMF Nat)
    (program : ProbOracleComp (fun _ : Bool => Nat) Bool) (s₀ : State) :
    (ProbOracleComp.runWith (fun q s => (h q).map (·, s)) program s₀).map Prod.fst =
      OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle h) program := by
  simp only [runWith_norm, pmf_norm]

example {State : Type} (ans : Bool → Nat)
    (program : ProbOracleComp (fun _ : Bool => Nat) Bool) (s₀ : State) :
    (ProbOracleComp.runWith (fun q s => PMF.pure (ans q, s)) program s₀).map Prod.fst =
      OracleComp.evalWith
        (OracleComp.sumHandler ProbComp.unifOracle (fun q => PMF.pure (ans q))) program := by
  simp only [runWith_norm, pmf_norm]

end HandlerSubstitution

/-! ### 4. Stateless `OracleComp.evalWith` on a concrete `do` program -/

section EvalWith

private def statelessProg : OracleComp (fun _ : Bool => Nat) Nat := do
  let x ← OracleComp.query false
  let y ← (· + 10) <$> OracleComp.query (decide (x < 5))
  return x + y

example (h : Bool → PMF Nat) :
    OracleComp.evalWith h statelessProg =
      (h false).bind fun x =>
        (h (decide (x < 5))).bind fun y =>
          PMF.pure (x + (y + 10)) := by
  simp only [statelessProg, runWith_norm, pmf_norm]

-- Closed stateless experiment wrapping a stateful reduction around a black-box adversary (as in
-- reductions from stateful CPA/CCA games to stateless PRF/ROM games) folds directly to `runWith`.
example {HState : Type} (keyGen : ℕ → ProbComp (List Bool))
    (inner : List Bool → Unit × List Bool → StateT HState (WordOracleComp Unit) (List Bool))
    (extOracle : Unit × List Bool → ProbComp (List Bool))
    (adversary : ℕ → WordOracleComp Unit Bool) (n : ℕ) (h₀ : HState) :
    ProbComp.eval (OracleComp.interpret
      (OracleComp.sumHandler ProbComp.unifFin extOracle)
      (reduction keyGen inner h₀ adversary n)) =
    (ProbComp.eval (keyGen n)).bind fun aux =>
      (ProbOracleComp.runWith
        (fun q st =>
          OracleComp.evalWith
            (OracleComp.sumHandler ProbComp.unifOracle (fun req => ProbComp.eval (extOracle req)))
            ((inner aux q).run st))
        (adversary n) h₀).bind fun r =>
        PMF.pure (!r.1) := by
  simp only [reduction, runWith_norm, pmf_norm]

-- Closed stateless experiment using `ProbOracleComp.run` (`eval_run_eq_evalWith` +
-- `evalWith_run_interpret`) folds a stateful reduction around a black-box adversary directly to
-- `ProbOracleComp.runWith` without `ProbOracleComp.run_bind` breaking the inner `.run`.
example {Op HState : Type} (keyGen : ℕ → ProbComp (List Bool))
    (inner : List Bool → Op × List Bool → StateT HState (WordOracleComp Op) (List Bool))
    (extOracle : Op × List Bool → ProbComp (List Bool))
    (adversary : ℕ → WordOracleComp Op Bool) (n : ℕ) (h₀ : HState) :
    ProbComp.eval ((reduction keyGen inner h₀ adversary n).run extOracle) =
    (ProbComp.eval (keyGen n)).bind fun aux =>
      (ProbOracleComp.runWith
        (fun q st =>
          OracleComp.evalWith
            (OracleComp.sumHandler ProbComp.unifOracle (fun req => ProbComp.eval (extOracle req)))
            ((inner aux q).run st))
        (adversary n) h₀).bind fun r =>
        PMF.pure (!r.1) := by
  simp only [reduction, runWith_norm, pmf_norm]

-- Stateless `ProbOracleComp.simulate` and spelled-out `OracleComp.interpret` under
-- `ProbOracleComp.run` fold to `OracleComp.evalWith` while stepping concrete handler bodies.
example (oracle : Bool ⊕ Nat → ProbComp Nat)
    (adversary : ProbOracleComp (fun _ : Bool => Nat) Bool) :
    ProbComp.eval
      ((ProbOracleComp.simulate (fun b => (· + 1) <$> ProbOracleComp.query (Sum.inl b))
        adversary).run oracle) =
    OracleComp.evalWith
      (OracleComp.sumHandler ProbComp.unifOracle
        (fun b => (ProbComp.eval (oracle (Sum.inl b))).map (· + 1)))
      adversary := by
  simp only [runWith_norm, pmf_norm]

example (oracle : Bool → ProbComp Nat)
    (adversary : ProbOracleComp (fun _ : Bool => Nat) Bool) :
    ProbComp.eval
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => ProbOracleComp.sample (ProbComp.unifFin n))
          (fun b => (· + 1) <$> ProbOracleComp.query (!b)))
        adversary).run oracle) =
    OracleComp.evalWith
      (OracleComp.sumHandler ProbComp.unifOracle
        (fun b => (ProbComp.eval (oracle (!b))).map (· + 1)))
      adversary := by
  simp only [runWith_norm, pmf_norm]

end EvalWith

end CslibFrontierTests.RunWithNorm
