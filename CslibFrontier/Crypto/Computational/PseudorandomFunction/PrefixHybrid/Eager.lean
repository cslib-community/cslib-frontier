/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction.PrefixHybrid
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic

/-!
# Eager tables for prefix hybrids

Sampling a prefix label at its first use has the same law as reading it from an independent
uniform table sampled before the client runs. Table indices must encode the actual prefixes,
including their lengths. This lets the fixed-width GGM expansion and the variable-length
cascade use the same argument with different finite index types.

For the cascade this is the eager hybrid rule in [BonehShoup2023], v0.6, Section 4.6.1
(printed pp. 152–153), applied at a whole-block cut as in Section 6.4.2 (printed pp. 229–230).
The equality includes adaptive queries and the client's private coins.
-/

public section

namespace Cslib.Crypto

open Probability

/-- An injective encoding of the visited prefixes identifies a lazy prefix-label cache with a
uniform table. The reply can depend on the whole query as well as its label. Invalid queries
return the empty word on both sides. -/
theorem prefixLabelGame_eq_eager {α Q : Type} [Fintype Q] [DecidableEq Q]
    (key : Q ↪ List Bool) (index : List Bool → Q) (valid : List Bool → Bool) (cut width : ℕ)
    (hkey : ∀ query, valid query = true → key (index query) = query.take cut)
    (respond : List Bool → List Bool → List Bool) (program : WordOracleComp Unit α) :
    ((OracleComp.interpret (OracleComp.sumHandler
      (fun k => StateT.lift (ProbComp.unifOracle k)) (fun request cache =>
        if valid request.2 then
          (memoize (fun _ : List Bool => BitString.uniformList width)
            (request.2.take cut) cache).map
              (fun (label, next) => (respond request.2 label, next))
        else PMF.pure ([], cache))) program).run []).map Prod.fst =
      (PMF.uniformOfFintype (Q → BitString width)).bind fun table =>
        OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle (fun request =>
          PMF.pure (if valid request.2 then respond request.2 (List.ofFn (table (index request.2)))
            else []))) program := by
  let adapter (query : List Bool) : ProbOracleComp (fun _ : Q => List Bool) (List Bool) :=
    if valid query then respond query <$> ProbOracleComp.query (index query) else pure []
  have h := RandomOracle.interpret_prob_eq_memoize_map
    key List.ofFn
    (fun _ => PMF.uniformOfFintype (BitString width)) (fun _ => BitString.uniformList width)
    (fun _ => rfl)
    (ProbOracleComp.simulate (fun request : Unit × List Bool => adapter request.2) program)
  have hstep (query : List Bool) : OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (fun q => memoize (fun _ => BitString.uniformList width) (key q)))
          (adapter query) = fun cache => if valid query then
        (memoize (fun _ => BitString.uniformList width) (query.take cut) cache).map
          (fun (label, next) => (respond query label, next)) else PMF.pure ([], cache) := by
    funext cache
    cases hvalid : valid query
    · simp only [adapter, hvalid, Bool.false_eq_true, ↓reduceIte, OracleComp.interpret_pure]
      rfl
    · simp only [adapter, hvalid, ↓reduceIte, OracleComp.interpret_map,
        ProbOracleComp.interpret_query, hkey query hvalid]
      rfl
  have heval (table : Q → BitString width) (query : List Bool) :
      OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle (fun q => PMF.pure (List.ofFn (table q))))
          (adapter query) = PMF.pure
        (if valid query then respond query (List.ofFn (table (index query))) else []) := by
    cases hvalid : valid query <;> simp [adapter, hvalid, PMF.pure_map]
  simpa only [PMF.pi_uniformOfFintype, ProbOracleComp.interpret_simulate, hstep, heval,
    PMF.monad_bind_eq_bind] using h.symm

/-- Use a finite index for the prefixes that valid queries can visit. -/
theorem eval_prefixHybridGame_eq_eager_of_index {Q : Type} [Fintype Q] [DecidableEq Q]
    (key : Q ↪ List Bool) (index : List Bool → Q) (valid : ℕ → List Bool → Bool)
    (family : List Bool → List Bool → List Bool) (adversary : OracleDistinguisher) (n cut : ℕ)
    (hkey : ∀ query, valid n query = true → key (index query) = query.take cut) :
    ProbComp.eval (prefixHybridGame valid family adversary n cut) =
      (PMF.uniformOfFintype (Q → BitString n)).bind fun table =>
        OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
          (fun request => PMF.pure (if valid n request.2 then
            family (List.ofFn (table (index request.2))) (request.2.drop cut)
            else []))) (adversary n []) := by
  have h := prefixLabelGame_eq_eager key index (valid n) cut n hkey
    (fun query label => family label (query.drop cut)) (adversary n [])
  have hstep (query : List Bool) (cache : List (List Bool × List Bool)) :
      ProbComp.eval (prefixHybridOracle (valid n) family n cut query cache) =
        if valid n query then
          (memoize (fun _ : List Bool => BitString.uniformList n) (query.take cut) cache).map
            (fun (label, next) => (family label (query.drop cut), next))
        else PMF.pure ([], cache) := by
    cases hvalid : valid n query <;>
      simp [prefixHybridOracle, hvalid, ProbComp.eval_memoize, BitString.eval_sampleList,
        PMF.map, Function.comp_def]
  simpa only [prefixHybridGame, ProbComp.eval_map, ProbOracleComp.eval_run_interpret, hstep] using h

/-- Sample one independent label per bit word of length at most `cut`. A query shorter than
the cut uses its entire word as its index, and a longer query uses its truncated prefix. -/
theorem eval_prefixHybridGame_eq_eager (valid : ℕ → List Bool → Bool)
    (family : List Bool → List Bool → List Bool) (adversary : OracleDistinguisher) (n cut : ℕ)
    [Fintype {word : List Bool // word.length ≤ cut}] :
    ProbComp.eval (prefixHybridGame valid family adversary n cut) =
      (PMF.uniformOfFintype ({word : List Bool // word.length ≤ cut} → BitString n)).bind
        fun table => OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
          (fun request => PMF.pure (if valid n request.2 then
            family (List.ofFn (table ⟨request.2.take cut, by simp⟩)) (request.2.drop cut)
            else []))) (adversary n []) :=
  eval_prefixHybridGame_eq_eager_of_index
    (Q := {word : List Bool // word.length ≤ cut}) ⟨Subtype.val, Subtype.val_injective⟩
    (fun query => ⟨query.take cut, by simp⟩) valid family adversary n cut (fun _ _ => rfl)

end Cslib.Crypto
