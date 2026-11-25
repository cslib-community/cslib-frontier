/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.Hybrid
public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.SampledReductionLaw
public import CslibFrontier.Crypto.Computational.PseudorandomFunction.PrefixFree
import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.ChildTableLaw
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Probability.BitString.List
import Mathlib.Data.Set.Finite.List

/-!
# The single-key PRF game for adjacent cascade hybrids

The cascade reduction routes the client at a chosen depth and forwards one sampled child
channel to the external PRF game. For an aligned prefix-free client, the resulting single-key
advantage, multiplied by the size of the sampled range, is exactly the gap between two
adjacent cascade hybrids.

## Main definitions

* `Cslib.Crypto.cascadeChildDistinguisher`: a word-oracle distinguisher for one adjacent step.

## Main results

* `Cslib.Crypto.advantage_cascadePrefixHybridGame_succ_eq`: exact advantage for an adjacent
  step. The strict oracle-PPT certificate and the full cascade bound (6.15) remain open (#5801).

## References

* [BonehShoup2023], v0.6, Sections 4.6.1 (printed pp. 152–154) and 6.4.2 (printed pp. 229–230),
  for the adjacent-hybrid argument.
-/

public section

namespace Cslib.Crypto

open Probability

/-- Route the client at `depth n` and use one external PRF challenge among `count n` child
channels. The selection uses `indexBits n` fair bits and rejects unused indices. -/
@[expose]
noncomputable def cascadeChildDistinguisher (valid : ℕ → List Bool → Bool)
    (inLen depth count indexBits : ℕ → ℕ) (family : List Bool → List Bool → List Bool)
    (adversary : OracleDistinguisher) : OracleDistinguisher := fun n aux =>
  cascadeChildChallengeProgram family (inLen n) n (count n) (indexBits n)
    (cascadeChildRouter (valid n) inLen family n (depth n) (adversary n aux))

/-- One adjacent step of the cascade argument. The two prefix hybrids have the advantage
of the explicit single-key PRF distinguisher multiplied by its sampled channel range.
Valid inputs are whole blocks, the client is prefix-free and query-bounded, and the sampled
range covers that bound. -/
theorem advantage_cascadePrefixHybridGame_succ_eq
    (valid : ℕ → List Bool → Bool) (inLen depth count indexBits : ℕ → ℕ)
    (family : List Bool → List Bool → List Bool) (adversary : OracleDistinguisher) (n : ℕ)
    (hwidth : 0 < inLen n) (halign : ∀ query, valid n query = true → inLen n ∣ query.length)
    (hlength : ∀ key block, block.length = inLen key.length →
      (family key block).length = key.length)
    (hpf : IsPrefixFreeOn (valid n) n (adversary n []))
    (hbudget : (adversary n []).IsQueryBounded (count n))
    (hcapacity : count n ≤ 2 ^ indexBits n) :
    let reduction := cascadeChildDistinguisher valid inLen depth count indexBits family adversary
    Game.advantage
      (ProbComp.eval (cascadePrefixHybridGame valid inLen family adversary n (depth n)))
      (ProbComp.eval (cascadePrefixHybridGame valid inLen family adversary n (depth n + 1))) =
      (2 ^ indexBits n : ℕ) * Game.advantage
        (ProbComp.eval (prfRealGame inLen family reduction n))
        (ProbComp.eval (prfIdealGame inLen id reduction n)) := by
  classical
  let _ := (List.finite_length_le Bool (depth n * inLen n)).fintype
  let router := cascadeChildRouter (valid n) inLen family n (depth n) (adversary n [])
  let reduction := cascadeChildDistinguisher valid inLen depth count indexBits family adversary
  let real := cascadeKeyedChildFunctionLaw family (inLen n) n
  let ideal := PMF.uniformOfFintype (BitString (inLen n) → BitString n)
  have hfixedLen (key block : List Bool) (hk : key.length = n) (hb : block.length = inLen n) :
      (family key block).length = n :=
    (hlength key block (by rw [hk, hb])).trans hk
  have hgame (source : PMF (BitString (inLen n) → BitString n)) :=
    bind_evalWith_cascadeChildChallengeProgram_eq_game family hfixedLen
      (count n) (indexBits n) source router
  have hideal : ProbComp.eval (prfIdealGame inLen id reduction n) =
      cascadeChildChallengeGame (count n) (2 ^ indexBits n) real ideal ideal router := by
    rw [← hgame ideal]
    simp only [prfIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform, id_eq,
      ProbOracleComp.eval_run_eq_evalWith, ProbComp.eval_pure,
      cascadeChildDistinguisher, reduction, router, ideal]
  have horacle (key : BitString n) (query : List Bool) :
      prfOracle family (inLen n) (List.ofFn key) query =
        randomFunctionOracle (inLen n)
          (fun block => BitString.ofList n (family (List.ofFn key) (List.ofFn block))) query := by
    by_cases hq : query.length = inLen n
    · have hvalue := hfixedLen (List.ofFn key) query List.length_ofFn hq
      simp only [prfOracle, randomFunctionOracle, ite_eq_left hq, BitString.ofFn_ofList hq,
        BitString.ofFn_ofList hvalue]
    · simp only [prfOracle, randomFunctionOracle, ite_eq_right hq]
  have hreal : ProbComp.eval (prfRealGame inLen family reduction n) =
      cascadeChildChallengeGame (count n) (2 ^ indexBits n) real ideal real router := by
    rw [← hgame real]
    simp only [prfRealGame, ProbComp.eval_bind, BitString.eval_sampleList, BitString.uniformList,
      ProbOracleComp.eval_run_eq_evalWith, ProbComp.eval_pure,
      real, cascadeKeyedChildFunctionLaw, PMF.bind_map, Function.comp_def, horacle,
      cascadeChildDistinguisher, reduction, router]
  have hbefore : ProbComp.eval (cascadePrefixHybridGame valid inLen family adversary n (depth n)) =
      (ProbOracleComp.runWith (cascadeChildChannelOracle real) router []).map Prod.fst := by
    rw [eval_cascadePrefixHybridGame_eq_childTables_real valid inLen family adversary n (depth n)
      hwidth halign hlength hpf]
    dsimp only [router]
    rw [runWith_cascadeChildRouter_eq_prefixGame, cascadeChildPrefixGame_eq_childTableGame]
    simp only [real, cascadeKeyedChildFunctionLaw, PMF.pi_map, PMF.pi_uniformOfFintype]
  have hafter :
      ProbComp.eval (cascadePrefixHybridGame valid inLen family adversary n (depth n + 1)) =
      (ProbOracleComp.runWith (cascadeChildChannelOracle ideal) router []).map Prod.fst := by
    rw [eval_cascadePrefixHybridGame_succ_eq_childTables_ideal valid inLen family adversary n
      (depth n) hwidth halign]
    dsimp only [router]
    rw [runWith_cascadeChildRouter_eq_prefixGame, cascadeChildPrefixGame_eq_childTableGame]
    simp only [ideal, PMF.pi_uniformOfFintype]
  change _ = (2 ^ indexBits n : ℕ) * Game.advantage
    (ProbComp.eval (prfRealGame inLen family reduction n))
    (ProbComp.eval (prfIdealGame inLen id reduction n))
  rw [hbefore, hafter, hreal, hideal]
  exact advantage_cascadeChildChannelOracle_eq real ideal
    (isQueryBounded_cascadeChildRouter (valid n) inLen family n (depth n) hbudget) hcapacity

end Cslib.Crypto
