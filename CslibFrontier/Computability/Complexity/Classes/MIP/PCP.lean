/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.MIP.SuccinctDecoder
public import CslibFrontier.Computability.Complexity.Classes.PCP.Oracle
import CslibFrontier.Computability.Complexity.Classes.MIP.ArithmeticRound
import CslibFrontier.Computability.Complexity.Classes.MIP.AxisSoundness
import CslibFrontier.Computability.Complexity.Classes.MIP.HonestProof
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Prime
import CslibFrontier.Computability.Probabilistic.Oracle.Composition

/-!
# Polynomial-randomness, polynomial-query proofs for NEXP

The verifier checks the syntax of a succinct 3-CNF decoder and makes two checks against the
same static bit-valued proof. The axis test forces a frequently accepted assignment table close
to a multilinear polynomial. A prefix-indexed sumcheck transcript and three local corrections
then check that this polynomial encodes a satisfying assignment. The verifier uses finitely
many fair coins to sample its field elements and repeats to reduce soundness error to one half.

## Main results

* `positiveLabelSuccinct3SAT_mem_PCPPoly` verifies succinct 3-SAT with a positive label width.
* `NEXP_subset_PCPPoly` lifts the verifier along polynomial-time many-one reductions.

This is the proof-oracle form of [Babai, Fortnow and Lund, Theorems 1.1 and 2.3, with the
two-phase verifier of §4.5][BabaiFortnowLund1991]. Here the assignment takes values in a
prime field and the static proof encodes a sumcheck response at each challenge prefix.
-/

public section

namespace Cslib.Complexity

open Probability Turing.MultiTapeTM Circuits Circuits.Boolean MvPolynomial
open scoped ENNReal

namespace MIP

private abbrev precision (x : Succinct3CNFInstance) := (4 * axisGapDenominator x.labelBits).size

private abbrev prime (x : Succinct3CNFInstance) := bertrandPrime x.fieldBound

private noncomputable def decoderRound (x : Succinct3CNFInstance) : WordOracleComp Unit Bool :=
  if x.valid && decide (0 < x.labelBits) then do
    let ok ← axisRound x.labelBits (prime x) (precision x)
    if ok then arithmeticRound x (prime x) (precision x) else pure false
  else pure false

private theorem isOraclePPTOn_decoderRound :
    IsOraclePPTOn encSuccinct3CNF encBool decoderRound := by
  have hL : ComputableInPolyTime Succinct3CNFInstance.labelBits encSuccinct3CNF encUnary :=
    encSuccinct3CNF_labelBits_polyTime ComputableInPolyTime.id'
  have hp : ComputableInPolyTime prime encSuccinct3CNF encUnary :=
    ComputableInPolyTime.unary_bertrandPrime Succinct3CNFInstance.computableInPolyTime_fieldBound
  have hprec : ComputableInPolyTime precision encSuccinct3CNF encUnary :=
    ComputableInPolyTime.binary_size.comp (ComputableInPolyTime.unary_to_binary.comp
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 4)
        (computableInPolyTime_axisGapDenominator.comp hL)))
  have hguard := ComputableInPolyTime.bool_and' Succinct3CNFInstance.computableInPolyTime_valid
    (ComputableInPolyTime.unary_lt' (ComputableInPolyTime.const 0) hL)
  have halg := isOraclePPTOn_arithmeticRound (ComputableInPolyTime.id' (encIn := encSuccinct3CNF))
    (p := prime) (precision := precision) hp hprec
  have hnext : IsOraclePPTOn (encPair encSuccinct3CNF encBool) encBool (fun q =>
      if q.2 then arithmeticRound q.1 (prime q.1) (precision q.1) else pure false) :=
    IsOraclePPTOn.cond (ComputableInPolyTime.snd encSuccinct3CNF encBool)
      (halg.preprocess (ComputableInPolyTime.fst encSuccinct3CNF encBool))
      (ComputableInPolyTime.const false).isOraclePPTOn
  unfold decoderRound
  exact IsOraclePPTOn.cond hguard
    ((isOraclePPTOn_axisRound hL hp hprec).bind_with
      (second := fun x ok => if ok then arithmeticRound x (prime x) (precision x) else pure false)
      hnext) (ComputableInPolyTime.const false).isOraclePPTOn

/-- Positive-label-width succinct 3-SAT has a strict polynomial-time proof-oracle verifier with
perfect completeness and soundness error at most one half, including on malformed decoders. -/
theorem positiveLabelSuccinct3SAT_mem_PCPPoly :
    {x | x ∈ Succinct3SAT ∧ 0 < x.labelBits} ∈ PCPPoly encSuccinct3CNF := by
  have hk : ComputableInPolyTime (fun x => 2 * axisGapDenominator x.labelBits)
      encSuccinct3CNF encUnary := by fun_prop
  apply mem_PCPPoly_of_inverse_gap isOraclePPTOn_decoderRound hk
  · intro x
    unfold axisGapDenominator
    positivity
  · rintro x ⟨⟨c, hc, hsat⟩, hpos⟩
    have : NeZero x.labelBits := ⟨hpos.ne'⟩
    have : Fact (prime x).Prime := ⟨(bertrandPrime_spec x.fieldBound_pos.ne').1⟩
    obtain ⟨A, _, π, _, haxis, hcorrect, ht⟩ :=
      exists_honestProof_of_satisfiable (p := prime x) c hsat
        (Succinct3CNFInstance.sumcheckDegree_eq c hc).ge
    refine ⟨π, ?_⟩
    change (((Prover.ofProof π).run (decoderRound x) ()).map Prod.fst) true = 1
    simp only [decoderRound, x.valid_eq_true_iff.mpr ⟨c, hc⟩, hpos, decide_true, Bool.and_self,
      ↓reduceIte, Prover.run_bind, haxis, _root_.PMF.pure_bind,
      run_arithmeticRound_of_honest π c hc A hcorrect ht]
    simp
  · intro x hx π
    by_cases hvalid : (x.valid && decide (0 < x.labelBits)) = true
    · obtain ⟨hv, hl⟩ := Bool.and_eq_true_iff.mp hvalid
      have hpos := of_decide_eq_true hl
      have : NeZero x.labelBits := ⟨hpos.ne'⟩
      obtain ⟨c, hc⟩ := x.valid_eq_true_iff.mp hv
      have hunsat : ¬ (SuccinctVerifier.toCNF c).Satisfiable := fun hs => hx ⟨⟨c, hc, hs⟩, hpos⟩
      obtain ⟨hp, hfield, _⟩ := bertrandPrime_spec x.fieldBound_pos.ne'
      have : Fact (prime x).Prime := ⟨hp⟩
      change 1000 * (x.labelBits + 1) ^ 3 +
        100 * (x.sumcheckVars + 1) * (x.sumcheckDegree + 1) < prime x at hfield
      have hq : 1000 * (x.labelBits + 1) ^ 3 ≤ prime x := by omega
      have hsmall : x.labelBits + 1 < prime x := by
        have := Nat.le_self_pow (a := x.labelBits + 1) (by decide : 3 ≠ 0)
        omega
      simp only [decoderRound, hvalid, ↓reduceIte, Nat.cast_mul, Nat.cast_ofNat]
      apply axisAnd_accept_le π hq
      intro A hA hnear
      have hprime : 0 < prime x := hp.pos
      have hreal := ENNReal.ofReal_le_ofReal (arithmeticError_le_half hfield hnear)
      simp (disch := positivity) only [ENNReal.ofReal_add, ENNReal.ofReal_mul,
        ENNReal.ofReal_div_of_pos, ENNReal.ofReal_pow, ENNReal.ofReal_natCast,
        ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at hreal
      have h := (acceptProb_arithmeticRound_le π c hc hunsat hA hsmall (precision x)).trans hreal
      unfold acceptProb at h
      simpa only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using
        ENNReal.toReal_mono (by norm_num) h
    · change (((Prover.ofProof π).run (decoderRound x) ()).map Prod.fst) true ≤ _
      simp [decoderRound, hvalid, Prover.run_pure]

end MIP

/-- Every nondeterministic exponential-time language has a strict probabilistic polynomial-time
verifier with access to a static Boolean proof, perfect completeness and soundness error at
most one half. -/
theorem NEXP_subset_PCPPoly {α : Type} {enc : α ↪ List Bool} : NEXP enc ⊆ PCPPoly enc := by
  intro A hA
  exact (MIP.polyTimeHard_positiveLabelSuccinct3SAT enc A hA).mem_PCPPoly
    MIP.positiveLabelSuccinct3SAT_mem_PCPPoly

end Cslib.Complexity
