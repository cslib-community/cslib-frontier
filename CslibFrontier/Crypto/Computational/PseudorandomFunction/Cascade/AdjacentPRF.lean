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
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.ChildRoutingPPT
import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.ChildTableLaw
import CslibFrontier.Crypto.Game.Concrete
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Probability.BitString.List
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.List

/-!
# The single-key PRF game for adjacent cascade hybrids

The cascade reduction routes the client at a chosen depth and forwards one sampled child
channel to the external PRF game. For an aligned prefix-free client, the resulting single-key
advantage, multiplied by the size of the sampled range, is exactly the gap between two
adjacent cascade hybrids.

## Main definitions

* `Cslib.Crypto.cascadeChildDistinguisher`: a word-oracle distinguisher for one adjacent step.
* `Cslib.Crypto.cascadeChildDistinguisherAt`: the reduction with a fixed depth and channel.
* `Cslib.Crypto.cascadeDistinguisher`: the uniform reduction over depths and channels.

## Main results

* `Cslib.Crypto.advantage_cascadePrefixHybridGame_succ_eq`: exact advantage for an adjacent
  step.
* `Cslib.Crypto.isOraclePPT_cascadeChildDistinguisher`: strict oracle PPT for the explicit
  single-key reduction used in the adjacent step.
* `Cslib.Crypto.advantage_cascade_le_pointwise`: the exact concrete loss in (6.15) at a
  specified security parameter, with a strict oracle-PPT witness.
* `Cslib.Crypto.PseudorandomFunctionOver.prefixFree_cascade`: the asymptotic security
  conclusion of Theorem 6.4.

## References

* [BonehShoup2023], v0.6, Sections 4.6.1 (printed pp. 152–154) and 6.4.2 (printed pp. 229–230),
  for the adjacent-hybrid argument.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- Route at a fixed depth and put the single-key challenge at a fixed child channel. -/
@[expose]
noncomputable def cascadeChildDistinguisherAt (valid : ℕ → List Bool → Bool)
    (inLen : ℕ → ℕ) (depth count channel : ℕ) (family : List Bool → List Bool → List Bool)
    (adversary : OracleDistinguisher) : OracleDistinguisher := fun n aux =>
  cascadeChildChallengeWithIndex family (inLen n) n count channel
    (cascadeChildRouter (valid n) inLen family n depth (adversary n aux))

/-- Route the client at `depth n` and use one external PRF challenge among `count n` child
channels. The selection uses `indexBits n` fair bits and rejects unused indices. -/
@[expose]
noncomputable def cascadeChildDistinguisher (valid : ℕ → List Bool → Bool)
    (inLen depth count indexBits : ℕ → ℕ) (family : List Bool → List Bool → List Bool)
    (adversary : OracleDistinguisher) : OracleDistinguisher := fun n aux =>
  cascadeChildChallengeProgram family (inLen n) n (count n) (indexBits n)
    (cascadeChildRouter (valid n) inLen family n (depth n) (adversary n aux))

/-- The adjacent-step reduction runs in strict oracle polynomial time in the security parameter
and auxiliary word. It uses a polynomial-time validity test and base family evaluation, and
polynomial-time unary block widths, cut depths, channel counts and sampling widths. -/
theorem isOraclePPT_cascadeChildDistinguisher
    {valid : ℕ → List Bool → Bool} {inLen depth count indexBits : ℕ → ℕ}
    {family : List Bool → List Bool → List Bool} {adversary : OracleDistinguisher}
    (hvalid : ComputableInPolyTime (fun p : ℕ × List Bool => valid p.1 p.2)
      (encPair encUnary encBits) encBool)
    (hIn : ComputableInPolyTime inLen encUnary encUnary)
    (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hcount : ComputableInPolyTime count encUnary encUnary)
    (hbits : ComputableInPolyTime indexBits encUnary encUnary)
    (hLen : ∀ key block, block.length = inLen key.length → (family key block).length = key.length)
    (hEval : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits)
    (hA : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (cascadeChildDistinguisher valid inLen depth count indexBits family
      adversary) := by
  let hn := ComputableInPolyTime.fst encUnary encBits
  have hrouter := (isOraclePPTOn_encodedCascadeChildRouter hvalid hIn hLen hEval hA).preprocess
    (ComputableInPolyTime.id'.prod (hdepth.comp hn))
  exact isOraclePPTOn_cascadeChildChallengeProgram hEval hrouter
    (hIn.comp hn) hn (hcount.comp hn) (hbits.comp hn)

private theorem isOraclePPT_cascadeChildDistinguisherAt
    {valid : ℕ → List Bool → Bool} {inLen : ℕ → ℕ} (depth count channel : ℕ)
    {family : List Bool → List Bool → List Bool} {adversary : OracleDistinguisher}
    (hvalid : ComputableInPolyTime (fun p : ℕ × List Bool => valid p.1 p.2)
      (encPair encUnary encBits) encBool)
    (hIn : ComputableInPolyTime inLen encUnary encUnary)
    (hLen : ∀ key block, block.length = inLen key.length → (family key block).length = key.length)
    (hEval : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits)
    (hA : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (cascadeChildDistinguisherAt valid inLen depth count channel family
      adversary) := by
  let hn := ComputableInPolyTime.fst encUnary encBits
  have hrouter := (isOraclePPTOn_encodedCascadeChildRouter hvalid hIn hLen hEval hA).preprocess
    (ComputableInPolyTime.id'.prod (.const depth))
  exact isOraclePPTOn_cascadeChildChallengeWithIndex hEval hrouter
    (hIn.comp hn) hn (.const count) (.const channel)

private theorem eval_cascadeReduction_games (inLen : ℕ → ℕ)
    (family : List Bool → List Bool → List Bool) (reduction : OracleDistinguisher) (n : ℕ)
    (hfixedLen : ∀ key block, key.length = n → block.length = inLen n →
      (family key block).length = n) :
    let run (challenge : BitString (inLen n) → BitString n) :=
      OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle
        (fun req : Unit × List Bool => PMF.pure (randomFunctionOracle (inLen n) challenge req.2)))
        (reduction n [])
    ProbComp.eval (prfRealGame inLen family reduction n) =
      (cascadeKeyedChildFunctionLaw family (inLen n) n).bind run ∧
    ProbComp.eval (prfIdealGame inLen id reduction n) =
      (PMF.uniformOfFintype (BitString (inLen n) → BitString n)).bind run := by
  constructor
  · simp only [prfRealGame, ProbComp.eval_bind, BitString.eval_sampleList, BitString.uniformList,
      ProbOracleComp.eval_run_eq_evalWith, ProbComp.eval_pure, cascadeKeyedChildFunctionLaw,
      PMF.bind_map, Function.comp_def, randomFunctionOracle_keyed hfixedLen]
  · simp only [prfIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform, id_eq,
      ProbOracleComp.eval_run_eq_evalWith, ProbComp.eval_pure]

private theorem eval_cascadePrefixHybridGame_step (valid : ℕ → List Bool → Bool)
    (inLen : ℕ → ℕ) (family : List Bool → List Bool → List Bool)
    (adversary : OracleDistinguisher) (n depth : ℕ) (hwidth : 0 < inLen n)
    (halign : ∀ query, valid n query = true → inLen n ∣ query.length)
    (hlength : ∀ key block, block.length = inLen key.length →
      (family key block).length = key.length)
    (hpf : IsPrefixFreeOn (valid n) n (adversary n [])) :
    let router := cascadeChildRouter (valid n) inLen family n depth (adversary n [])
    ProbComp.eval (cascadePrefixHybridGame valid inLen family adversary n depth) =
      (ProbOracleComp.runWith (cascadeChildChannelOracle
        (cascadeKeyedChildFunctionLaw family (inLen n) n)) router []).map Prod.fst ∧
    ProbComp.eval (cascadePrefixHybridGame valid inLen family adversary n (depth + 1)) =
      (ProbOracleComp.runWith (cascadeChildChannelOracle
        (PMF.uniformOfFintype (BitString (inLen n) → BitString n))) router []).map Prod.fst := by
  classical
  let _ := (List.finite_length_le Bool (depth * inLen n)).fintype
  constructor
  · rw [eval_cascadePrefixHybridGame_eq_childTables_real valid inLen family adversary n depth
      hwidth halign hlength hpf]
    rw [runWith_cascadeChildRouter_eq_prefixGame, cascadeChildPrefixGame_eq_childTableGame]
    simp only [cascadeKeyedChildFunctionLaw, PMF.pi_map, PMF.pi_uniformOfFintype]
  · rw [eval_cascadePrefixHybridGame_succ_eq_childTables_ideal valid inLen family adversary n
      depth hwidth halign]
    rw [runWith_cascadeChildRouter_eq_prefixGame, cascadeChildPrefixGame_eq_childTableGame]
    simp only [PMF.pi_uniformOfFintype]

/-- Signed adjacent-hybrid gap for the sampled single-key distinguisher. Keeping the sign
allows further averaging across depths before taking the absolute value. -/
theorem succProbability_cascadePrefixHybridGame_succ_eq
    (valid : ℕ → List Bool → Bool) (inLen depth count indexBits : ℕ → ℕ)
    (family : List Bool → List Bool → List Bool) (adversary : OracleDistinguisher) (n : ℕ)
    (hwidth : 0 < inLen n) (halign : ∀ query, valid n query = true → inLen n ∣ query.length)
    (hlength : ∀ key block, block.length = inLen key.length →
      (family key block).length = key.length)
    (hpf : IsPrefixFreeOn (valid n) n (adversary n []))
    (hbudget : (adversary n []).IsQueryBounded (count n))
    (hcapacity : count n ≤ 2 ^ indexBits n) :
    let reduction := cascadeChildDistinguisher valid inLen depth count indexBits family adversary
    (Game.succProbability
      (ProbComp.eval (cascadePrefixHybridGame valid inLen family adversary n (depth n))) : ℝ) -
    Game.succProbability
      (ProbComp.eval (cascadePrefixHybridGame valid inLen family adversary n (depth n + 1))) =
      (↑(2 ^ indexBits n : ℕ) : ℝ) *
        ((Game.succProbability (ProbComp.eval (prfRealGame inLen family reduction n)) : ℝ) -
          Game.succProbability (ProbComp.eval (prfIdealGame inLen id reduction n))) := by
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
  obtain ⟨hreal, hideal⟩ := eval_cascadeReduction_games inLen family reduction n hfixedLen
  obtain ⟨hbefore, hafter⟩ := eval_cascadePrefixHybridGame_step valid inLen family adversary n
    (depth n) hwidth halign hlength hpf
  change _ = (↑(2 ^ indexBits n : ℕ) : ℝ) *
    ((Game.succProbability (ProbComp.eval (prfRealGame inLen family reduction n)) : ℝ) -
      Game.succProbability (ProbComp.eval (prfIdealGame inLen id reduction n)))
  rw [hbefore, hafter, hreal, hideal]
  simp only [reduction, cascadeChildDistinguisher]
  rw [hgame real, hgame ideal]
  exact succProbability_cascadeChildChannelOracle_eq real ideal
    (isQueryBounded_cascadeChildRouter (valid n) inLen family n (depth n) hbudget) hcapacity

/-- The adjacent cascade advantage equals the single-key advantage times the sampled channel
range, for an aligned prefix-free client whose query bound fits in that range. -/
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
  dsimp only
  apply NNReal.eq
  rw [NNReal.coe_mul, NNReal.coe_natCast, Game.coe_advantage, Game.coe_advantage,
    succProbability_cascadePrefixHybridGame_succ_eq valid inLen depth count indexBits family
      adversary n hwidth halign hlength hpf hbudget hcapacity, abs_mul, Nat.abs_cast]

/-- Sample a depth with fair bits, then run the sampled child challenge at that depth.
An unused depth or child index rejects. -/
@[expose]
noncomputable def cascadeDistinguisher (valid : ℕ → List Bool → Bool)
    (inLen hops count : ℕ → ℕ) (family : List Bool → List Bool → List Bool)
    (adversary : OracleDistinguisher) : OracleDistinguisher := fun n aux => do
  let depth ← ProbOracleComp.sample (ProbComp.sampleDyadicIndex (hops n))
  if depth < hops n then
    cascadeChildChallengeProgram family (inLen n) n (count n) (Nat.log 2 (count n) + 1)
      (cascadeChildRouter (valid n) inLen family n depth (adversary n aux))
  else pure false

/-- Sampling the depth and child channel preserves the client's external query budget. -/
theorem isQueryBounded_cascadeDistinguisher
    {valid : ℕ → List Bool → Bool} {inLen hops count : ℕ → ℕ}
    {family : List Bool → List Bool → List Bool} {adversary : OracleDistinguisher}
    {n : ℕ} {aux : List Bool} {budget : ℕ}
    (hbudget : (adversary n aux).IsQueryBounded budget) :
    (cascadeDistinguisher valid inLen hops count family adversary n aux).IsQueryBounded budget := by
  unfold cascadeDistinguisher
  refine ((ProbOracleComp.IsQueryBounded.sample _).bind (m := budget) fun depth => ?_).mono
    (by simp)
  split
  · exact isQueryBounded_cascadeChildChallengeProgram family (inLen n) n (count n) _
      (isQueryBounded_cascadeChildRouter (valid n) inLen family n depth hbudget)
  · exact .pure _ _

/-- The uniform two-index reduction runs in strict oracle polynomial time. The numerical
functions provide the block width, depth bound and channel budget on unary inputs. -/
theorem isOraclePPT_cascadeDistinguisher
    {valid : ℕ → List Bool → Bool} {inLen hops count : ℕ → ℕ}
    {family : List Bool → List Bool → List Bool} {adversary : OracleDistinguisher}
    (hvalid : ComputableInPolyTime (fun p : ℕ × List Bool => valid p.1 p.2)
      (encPair encUnary encBits) encBool)
    (hIn : ComputableInPolyTime inLen encUnary encUnary)
    (hhops : ComputableInPolyTime hops encUnary encUnary)
    (hcount : ComputableInPolyTime count encUnary encUnary)
    (hLen : ∀ key block, block.length = inLen key.length → (family key block).length = key.length)
    (hEval : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits)
    (hA : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (cascadeDistinguisher valid inLen hops count family adversary) := by
  let input := encPair encUnary encBits
  let hn := ComputableInPolyTime.fst encUnary encBits
  let hn' := hn.comp (ComputableInPolyTime.fst input encUnary)
  let hdepth := ComputableInPolyTime.snd input encUnary
  let hq := hcount.comp hn'
  let hbits := ComputableInPolyTime.unary_succ.comp
    (ComputableInPolyTime.unary_log_two.comp hq)
  have hrouter := isOraclePPTOn_encodedCascadeChildRouter hvalid hIn hLen hEval hA
  have hchild := isOraclePPTOn_cascadeChildChallengeProgram hEval hrouter
    (hIn.comp hn') hn' hq hbits
  exact ((isPPTOn_sampleDyadicIndex (hhops.comp hn)).isOraclePPTOn (Operation := Unit)).bind_with
    (IsOraclePPTOn.ite (hdepth.unary_lt' (hhops.comp hn')) hchild
      ((ComputableInPolyTime.const false).isPPTOn.isOraclePPTOn))

/-- The uniform reduction has exact loss equal to the product of its two fair-bit sampling
ranges. Every rejected index contributes the same result on both sides. -/
theorem advantage_cascade_eq_dyadic
    {valid : ℕ → List Bool → Bool} {inLen hops count : ℕ → ℕ}
    {family : List Bool → List Bool → List Bool} {adversary : OracleDistinguisher} (n : ℕ)
    (hwidth : 0 < inLen n) (halign : ∀ query, valid n query = true → inLen n ∣ query.length)
    (hcut : ∀ query, valid n query = true → query.length ≤ hops n * inLen n)
    (hlength : ∀ key block, block.length = inLen key.length →
      (family key block).length = key.length)
    (hpf : IsPrefixFreeOn (valid n) n (adversary n []))
    (hbudget : (adversary n []).IsQueryBounded (count n)) :
    let reduction := cascadeDistinguisher valid inLen hops count family adversary
    Game.advantage
      (ProbComp.eval (prfRealGameOn valid (cascadeFamily inLen family) adversary n))
      (ProbComp.eval (prfIdealGameOn valid id adversary n)) =
    (↑(dyadicSize (hops n) * dyadicSize (count n)) : NNReal) *
      Game.advantage (ProbComp.eval (prfRealGame inLen family reduction n))
        (ProbComp.eval (prfIdealGame inLen id reduction n)) := by
  let reduction := cascadeDistinguisher valid inLen hops count family adversary
  let bits k := Nat.log 2 (count k) + 1
  let atDepth i := cascadeChildDistinguisher valid inLen (fun _ => i) count bits family adversary
  let run (B : OracleDistinguisher) (challenge : BitString (inLen n) → BitString n) :=
    OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle
      (fun req : Unit × List Bool => PMF.pure (randomFunctionOracle (inLen n) challenge req.2)))
      (B n [])
  let mix (games : ℕ → Game) :=
    (PMF.uniformOfFintype (Fin (dyadicSize (hops n)))).bind fun i =>
      if i.val < hops n then games i.val else PMF.pure false
  have hmix (source : PMF (BitString (inLen n) → BitString n)) :
      source.bind (run reduction) = mix (fun i => source.bind (run (atDepth i))) := by
    simp only [run, reduction, cascadeDistinguisher, OracleComp.evalWith_bind,
      ProbOracleComp.evalWith_sumHandler_unifOracle_sample, ProbComp.eval_sampleDyadicIndex,
      PMF.bind_map, Function.comp_def, mix]
    rw [PMF.bind_comm source]
    congr 1 with i : 1
    split_ifs
    · rfl
    · simp only [OracleComp.evalWith_pure, PMF.bind_const]
  have hfixedLen (key block : List Bool) (hk : key.length = n) (hb : block.length = inLen n) :
      (family key block).length = n :=
    (hlength key block (by rw [hk, hb])).trans hk
  obtain ⟨hreal, hideal⟩ := eval_cascadeReduction_games inLen family reduction n hfixedLen
  have hrealMix : ProbComp.eval (prfRealGame inLen family reduction n) =
      mix (fun i => ProbComp.eval (prfRealGame inLen family (atDepth i) n)) :=
    hreal.trans ((hmix _).trans (congrArg mix (funext fun i =>
      (eval_cascadeReduction_games inLen family (atDepth i) n hfixedLen).1.symm)))
  have hidealMix : ProbComp.eval (prfIdealGame inLen id reduction n) =
      mix (fun i => ProbComp.eval (prfIdealGame inLen id (atDepth i) n)) :=
    hideal.trans ((hmix _).trans (congrArg mix (funext fun i =>
      (eval_cascadeReduction_games inLen family (atDepth i) n hfixedLen).2.symm)))
  have hsigned := Game.succProbability_hybrid_reduction
    (fun i => ProbComp.eval (cascadePrefixHybridGame valid inLen family adversary n i))
    (fun i => ProbComp.eval (prfRealGame inLen family (atDepth i) n))
    (fun i => ProbComp.eval (prfIdealGame inLen id (atDepth i) n))
    (hops n) (dyadicSize (hops n)) (lt_dyadicSize _).le (dyadicSize (count n) : ℝ)
    (fun i _ => succProbability_cascadePrefixHybridGame_succ_eq valid inLen (fun _ => i)
      count bits family adversary n hwidth halign hlength hpf hbudget (lt_dyadicSize _).le)
  change _ = _ * ((Game.succProbability
    (mix (fun i => ProbComp.eval (prfRealGame inLen family (atDepth i) n))) : ℝ) -
    Game.succProbability (mix (fun i => ProbComp.eval (prfIdealGame inLen id (atDepth i) n))))
    at hsigned
  rw [← hrealMix, ← hidealMix, eval_cascadePrefixHybridGame_zero,
    eval_cascadePrefixHybridGame_eq_ideal family adversary hcut] at hsigned
  change _ = (↑(dyadicSize (hops n) * dyadicSize (count n)) : NNReal) * _
  apply NNReal.eq
  rw [NNReal.coe_mul, NNReal.coe_natCast, Game.coe_advantage, Game.coe_advantage, hsigned,
    ← Nat.cast_mul, abs_mul, Nat.abs_cast]

/-- Boneh–Shoup's prefix-free cascade security, [BonehShoup2023], v0.6, Theorem 6.4
(printed p. 229), on a polynomial-time decidable domain of aligned words with a unary
polynomial-time block cap. The base PRF's key and output widths are both `n` bits. A
single strict fair-coin reduction samples both indices from dyadic ranges whose product
is polynomially bounded. Block width need only be positive eventually. -/
theorem PseudorandomFunctionOver.prefixFree_cascade
    {valid : ℕ → List Bool → Bool} {inLen hops : ℕ → ℕ}
    {family : List Bool → List Bool → List Bool}
    (hF : PseudorandomFunctionOver inLen id family)
    (hvalid : ComputableInPolyTime (fun p : ℕ × List Bool => valid p.1 p.2)
      (encPair encUnary encBits) encBool)
    (hIn : ComputableInPolyTime inLen encUnary encUnary)
    (hhops : ComputableInPolyTime hops encUnary encUnary)
    (hwidth : ∀ᶠ n in Filter.atTop, 0 < inLen n)
    (halign : ∀ n query, valid n query = true → inLen n ∣ query.length)
    (hcut : ∀ n query, valid n query = true → query.length ≤ hops n * inLen n) :
    PrefixFreePseudorandomFunctionOn valid id (cascadeFamily inLen family) := by
  refine ⟨computableInPolyTime_cascadeFamily hIn hF.length_eq hF.polyTime,
    fun key query _ => length_cascadeFamily hF.length_eq key query, ?_⟩
  intro adversary hA
  obtain ⟨count, hcount, _, hbudget⟩ := hA.1.exists_computable_queryBound
  let reduction := cascadeDistinguisher valid inLen hops count family adversary
  have hppt := isOraclePPT_cascadeDistinguisher hvalid hIn hhops hcount
    hF.length_eq hF.polyTime hA.1
  have hloss : PolynomiallyBounded (fun n => dyadicSize (hops n) * dyadicSize (count n)) :=
    ((ComputableInPolyTime.unary_dyadicSize.comp hhops).unary_mul'
      (ComputableInPolyTime.unary_dyadicSize.comp hcount)).polynomiallyBounded
  refine negligible_of_eventually_le ((hF.secure reduction hppt).polynomiallyBounded_mul hloss) ?_
  filter_upwards [hwidth] with n hn
  have hq : (adversary n []).IsQueryBounded (count n) := by
    simpa only [List.length_nil, Nat.add_zero] using (hbudget n []).1
  exact (advantage_cascade_eq_dyadic n hn (halign n) (hcut n) hF.length_eq (hA.2 n) hq).le

/-- Pointwise concrete bound of [BonehShoup2023], v0.6, Theorem 6.4, equation (6.15)
(printed p. 229). A prefix-free client with at most `count` queries on aligned words
of at most `hops` blocks has advantage at most `hops * count` times that of an explicit
strict oracle-PPT reduction. The query predicate specifies the domain on bit words. The
depth and channel of the witness may be chosen separately at each security parameter. -/
theorem advantage_cascade_le_pointwise
    {valid : ℕ → List Bool → Bool} {inLen : ℕ → ℕ}
    {family : List Bool → List Bool → List Bool} {adversary : OracleDistinguisher}
    (n hops count : ℕ)
    (hvalid : ComputableInPolyTime (fun p : ℕ × List Bool => valid p.1 p.2)
      (encPair encUnary encBits) encBool)
    (hIn : ComputableInPolyTime inLen encUnary encUnary)
    (hwidth : 0 < inLen n) (halign : ∀ query, valid n query = true → inLen n ∣ query.length)
    (hcut : ∀ query, valid n query = true → query.length ≤ hops * inLen n)
    (hlength : ∀ key block, block.length = inLen key.length →
      (family key block).length = key.length)
    (hEval : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits)
    (hA : IsOraclePPT encBool adversary)
    (hpf : IsPrefixFreeOn (valid n) n (adversary n []))
    (hbudget : (adversary n []).IsQueryBounded count) :
    ∃ reduction : OracleDistinguisher, IsOraclePPT encBool reduction ∧
      (reduction n []).IsQueryBounded count ∧
      Game.advantage
        (ProbComp.eval (prfRealGameOn valid (cascadeFamily inLen family) adversary n))
        (ProbComp.eval (prfIdealGameOn valid id adversary n)) ≤
      (hops * count : ℕ) * Game.advantage
        (ProbComp.eval (prfRealGame inLen family reduction n))
        (ProbComp.eval (prfIdealGame inLen id reduction n)) := by
  let reduction (p : Fin hops × Fin count) :=
    cascadeChildDistinguisherAt valid inLen p.1.val count p.2.val family adversary
  let advantage (p : Fin hops × Fin count) :=
    Game.advantage (ProbComp.eval (prfRealGame inLen family (reduction p) n))
      (ProbComp.eval (prfIdealGame inLen id (reduction p) n))
  have hfixedLen (key block : List Bool) (hk : key.length = n) (hb : block.length = inLen n) :
      (family key block).length = n :=
    (hlength key block (by rw [hk, hb])).trans hk
  have hbound (ε : NNReal) (hstep : ∀ p, advantage p ≤ ε) :
      Game.advantage
        (ProbComp.eval (prfRealGameOn valid (cascadeFamily inLen family) adversary n))
        (ProbComp.eval (prfIdealGameOn valid id adversary n)) ≤ (hops * count : ℕ) * ε := by
    rw [← eval_cascadePrefixHybridGame_zero, ← eval_cascadePrefixHybridGame_eq_ideal family
      adversary hcut, Nat.cast_mul, mul_assoc]
    refine Game.advantage_hybrid_le
      (fun i => ProbComp.eval (cascadePrefixHybridGame valid inLen family adversary n i))
      hops (count * ε) fun i hi => ?_
    let router := cascadeChildRouter (valid n) inLen family n i (adversary n [])
    let real := cascadeKeyedChildFunctionLaw family (inLen n) n
    let ideal := PMF.uniformOfFintype (BitString (inLen n) → BitString n)
    obtain ⟨hbefore, hafter⟩ := eval_cascadePrefixHybridGame_step valid inLen family adversary n i
      hwidth halign hlength hpf
    rw [hbefore, hafter]
    refine advantage_cascadeChildChannelOracle_le real ideal
      (isQueryBounded_cascadeChildRouter (valid n) inLen family n i hbudget) ε fun channel => ?_
    let p : Fin hops × Fin count := (⟨i, hi⟩, channel)
    obtain ⟨hreal, hideal⟩ := eval_cascadeReduction_games inLen family (reduction p) n hfixedLen
    have hgame := funext (fun row =>
      evalWith_cascadeChildChallengeWithIndex family hfixedLen channel row router)
    have h := hstep p
    dsimp only [advantage] at h
    rw [hreal, hideal] at h
    simp only [reduction, cascadeChildDistinguisherAt, p] at h
    rw [hgame] at h
    exact h
  by_cases hgrid : Nonempty (Fin hops × Fin count)
  · let _ := hgrid
    obtain ⟨p, _, hp⟩ := Finset.exists_max_image Finset.univ advantage Finset.univ_nonempty
    refine ⟨reduction p, isOraclePPT_cascadeChildDistinguisherAt p.1 count p.2 hvalid hIn
      hlength hEval hA, ?_, hbound (advantage p) (fun q => hp q (Finset.mem_univ q))⟩
    exact isQueryBounded_cascadeChildChallengeWithIndex family (inLen n) n count p.2
      (isQueryBounded_cascadeChildRouter (valid n) inLen family n p.1 hbudget)
  · refine ⟨fun _ _ => pure false, (ComputableInPolyTime.const false).isPPTOn.isOraclePPTOn,
      .pure _ _, ?_⟩
    have hzero := hbound 0 (fun p => (hgrid ⟨p⟩).elim)
    rw [mul_zero] at hzero
    exact hzero.trans zero_le

end Cslib.Crypto
