/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Complexity.Classes.MIP.Arithmetization
import CslibFrontier.Computability.Complexity.Problems.NEXPBoundedAcceptance
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

-- Regression tests intentionally export no declarations.
set_option linter.privateModule false

/-!
# Checked tests for BFL arithmetization and uniform succinct tableau decoding

Exercises `Cslib.Complexity.MIP` (`Arithmetization.lean`, `#892` M5a):

1. Non-trivial De Morgan decoder circuits (`satDecoder` with `.not` gates and `unsatDecoder` with
   `.const`/`.not` gates): exact Boolean equivalence, explicit satisfying witness `A_sat`,
   Sumcheck completeness on `satDecoder`, and non-vacuous Schwartz–Zippel + Sumcheck soundness
   on `unsatDecoder` over `ZMod 401`.
2. Concrete mod-`p` verifier evaluation (`evalGateTraceMod`, `eqCubeMod`, `evalClauseUnsatMod`,
   `evalConstraintMod`) matching `tableauConstraintPoly` over `ZMod 11`, plus the `p = 0` guard and
   uniform polynomial-time certificate instantiation (`computableInPolyTime_evalConstraintMod`).
3. Concrete `NEXPBoundedAcceptance` membership and non-membership routed end-to-end through
   `exists_succinctCNF_of_mem_NEXP`, `exists_succinctDecoder_of_mem_NEXP`, and
   `satisfiable_toCNF_iff_succinctCNF`.
-/

namespace CslibFrontierTests.BFLArithmetization

open Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity
open Cslib.Complexity.MIP Cslib.Interactive Cslib.Logic.PL
open Turing Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open Turing.MultiTapeTM.Universal MvPolynomial
open scoped ENNReal

instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 23) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 401) := ⟨by norm_num⟩

/-- Satisfiable 1-bit clause-index, 1-bit variable-address succinct decoder with `.not` gates:
clause `0` requires variable `[false]` to be `true`, clause `1` requires `[true]` to be `false`. -/
private def satDecoder : Circuit signature 1 (3 * (1 + 1)) :=
  Circuit.pi fun j : Fin 6 =>
    if j.val % 2 = 0 then (Formula.input (σ := signature) (0 : Fin 1)).toCircuit
    else ((Formula.input (σ := signature) (0 : Fin 1)).not).toCircuit

/-- Unsatisfiable succinct decoder with `.const false` and `.not` gates: literal `0` of every
clause points to variable `[false]` with opposite signs across `idx = ![false]` and `![true]`. -/
private def unsatDecoder : Circuit signature 1 (3 * (1 + 1)) :=
  Circuit.pi fun j : Fin 6 =>
    if j.val % 2 = 0 then (Formula.const (n := 1) false : Formula signature 1).toCircuit
    else ((Formula.input (σ := signature) (0 : Fin 1)).not).toCircuit

private theorem satDecoder_satisfiable : (SuccinctVerifier.toCNF satDecoder).Satisfiable := by
  refine ⟨fun b => !b 0, ?_⟩
  rw [SuccinctVerifier.eval_toCNF_eq_true_iff]
  intro x
  rw [SuccinctVerifier.eval_clause_eq_true_iff]
  refine ⟨0, ?_⟩
  simp [satDecoder, SuccinctVerifier.addressWire, SuccinctVerifier.signWire]

private theorem unsatDecoder_unsatisfiable :
    ¬ (SuccinctVerifier.toCNF unsatDecoder).Satisfiable := by
  rintro ⟨σ, hσ⟩
  rw [SuccinctVerifier.eval_toCNF_eq_true_iff] at hσ
  have h0 := (SuccinctVerifier.eval_clause_eq_true_iff unsatDecoder σ ![false]).1 (hσ ![false])
  have h1 := (SuccinctVerifier.eval_clause_eq_true_iff unsatDecoder σ ![true]).1 (hσ ![true])
  obtain ⟨r0, hr0⟩ := h0
  obtain ⟨r1, hr1⟩ := h1
  fin_cases r0 <;> fin_cases r1 <;>
    simp_all [unsatDecoder, SuccinctVerifier.addressWire, SuccinctVerifier.signWire]

-- Non-trivial gate counts: neither decoder has zero gates.
example : 0 < satDecoder.size ∧ 0 < unsatDecoder.size := by
  constructor <;> decide

-- Exact Boolean equivalence + Sumcheck completeness on `satDecoder` with explicit witness `A_sat`.
example :
    (∃ A ∈ restrictDegree (Fin 1) (ZMod 23) 1,
      ∀ y : Fin (1 + satDecoder.size) → Bool,
        MvPolynomial.eval (bitPoint y) (gateTracePoly (ZMod 23) satDecoder *
          clauseUnsatPoly satDecoder A) = 0) ∧
    (∃ A ∈ restrictDegree (Fin 1) (ZMod 23) 1, ∀ r : Fin (1 + satDecoder.size) → ZMod 23,
      Sumcheck.rel (tableauConstraintPoly satDecoder A r) 0 ⟨Fin.elim0, 0⟩ () ∧
      (Sumcheck.proof (1 + 3 * satDecoder.size + 3 * (1 + 1))
        (tableauConstraintPoly satDecoder A r)).Complete
        Interactive.World.plain
        (Sumcheck.rel (tableauConstraintPoly satDecoder A r) 0)
        Interactive.Accept 0) ∧
    let A_sat : MvPolynomial (Fin 1) (ZMod 23) :=
      multilinearExtension fun b : Fin 1 → Bool => bitVal (ZMod 23) (!b 0)
    ∀ y : Fin (1 + satDecoder.size) → Bool,
      MvPolynomial.eval (bitPoint y)
        (gateTracePoly (ZMod 23) satDecoder * clauseUnsatPoly satDecoder A_sat) = 0 := by
  refine ⟨(satisfiable_toCNF_iff_forall_eval_base_eq_zero (F := ZMod 23) satDecoder).1
      satDecoder_satisfiable,
    sumcheck_proof_complete_of_satisfiable (F := ZMod 23) satDecoder satDecoder_satisfiable le_rfl,
    fun y => ?_⟩
  let A_sat : MvPolynomial (Fin 1) (ZMod 23) :=
    multilinearExtension fun b : Fin 1 → Bool => bitVal (ZMod 23) (!b 0)
  obtain ⟨idx, w, rfl⟩ : ∃ (idx : Fin 1 → Bool) (w : Fin satDecoder.size → Bool),
      y = Fin.append idx w :=
    ⟨fun i => y (Fin.castAdd satDecoder.size i), fun j => y (Fin.natAdd 1 j), by
      funext u
      induction u using Fin.addCases with
      | left => simp
      | right => simp⟩
  rw [map_mul, eval_gateTracePoly_bitPoint]
  split_ifs with htrace
  · rw [one_mul, eval_clauseUnsatPoly_trace satDecoder A_sat idx htrace]
    refine Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 3)) ?_
    dsimp only
    rw [eval_multilinearExtension]
    rcases Bool.dichotomy (idx 0) with h0 | h0 <;>
      simp [satDecoder, SuccinctVerifier.addressWire, SuccinctVerifier.signWire, bitVal, h0]
  · exact zero_mul _

-- Unsatisfiable instance (`unsatDecoder`): Schwartz–Zippel + Sumcheck soundness with non-trivial
-- total error bound strictly below `1` over `ZMod 401`.
example :
    let A_test : MvPolynomial (Fin 1) (ZMod 401) :=
      multilinearExtension fun b : Fin 1 → Bool => bitVal (ZMod 401) (b 0)
    let d := 1 + 3 * unsatDecoder.size + 3 * (1 + 1)
    ((Finset.univ : Finset (Fin (1 + unsatDecoder.size) → ZMod 401)).filter fun r =>
        Sumcheck.partialSum (tableauConstraintPoly unsatDecoder A_test r) Fin.elim0 = 0).card *
        401 ≤ (1 + unsatDecoder.size) * 401 ^ (1 + unsatDecoder.size) ∧
      (∀ r : Fin (1 + unsatDecoder.size) → ZMod 401,
        Sumcheck.partialSum (tableauConstraintPoly unsatDecoder A_test r) Fin.elim0 ≠ 0 →
        (Sumcheck.proof d (tableauConstraintPoly unsatDecoder A_test r)).verifier.Sound
          (oP := OracleSpec.empty) Interactive.World.plain
          (Interactive.language (Sumcheck.rel (tableauConstraintPoly unsatDecoder A_test r) 0))
          Set.univ ((1 + unsatDecoder.size) * ((d : ℝ≥0∞) / 401))) ∧
      (1 + unsatDecoder.size) * d < 401 := by
  dsimp only
  let A_test : MvPolynomial (Fin 1) (ZMod 401) :=
    multilinearExtension fun b : Fin 1 → Bool => bitVal (ZMod 401) (b 0)
  have hAmem : A_test ∈ restrictDegree (Fin 1) (ZMod 401) 1 :=
    multilinearExtension_mem_restrictDegree _
  have hdeg : ∀ r v,
      (tableauConstraintPoly unsatDecoder A_test r).degreeOf v ≤
        1 + 3 * unsatDecoder.size + 3 * (1 + 1) :=
    fun r v => tableauConstraintPoly_degreeOf_le unsatDecoder hAmem r v
  have hsound := sumcheck_sound_of_not_satisfiable (F := ZMod 401) unsatDecoder
    unsatDecoder_unsatisfiable A_test hdeg
  refine ⟨by simpa only [ZMod.card] using hsound.1, fun r hr => ?_, by decide⟩
  simpa only [ZMod.card, Nat.cast_one, Nat.cast_ofNat] using hsound.2 r hr

-- Concrete mod-`11` evaluation matches `tableauConstraintPoly` on `satDecoder`, and `p = 0` guards
-- return `0`.
example :
    let idx : Fin 1 → Bool := ![false]
    let trace := evalCode interpretation false (List.ofFn idx) satDecoder.code.1
    let z : Fin (1 + satDecoder.size) → ℕ := fun u =>
      if (Fin.append idx (fun j => trace.getD (1 + j.val) false)) u then 1 else 0
    let r : Fin (1 + satDecoder.size) → ℕ := fun i => (i.val + 2) % 11
    let A11 : MvPolynomial (Fin 1) (ZMod 11) :=
      multilinearExtension fun b : Fin 1 → Bool => bitVal (ZMod 11) (!b 0)
    ((evalConstraintMod 11 1 satDecoder.code.1 (List.ofFn r) (List.ofFn z)
        (List.ofFn fun j : Fin 3 => (satDecoder.outputs (SuccinctVerifier.signWire 1 j)).toNat)
        (List.ofFn fun _ : Fin 3 => 1) : ℕ) : ZMod 11) =
      MvPolynomial.eval (fun i => (z i : ZMod 11))
        (tableauConstraintPoly satDecoder A11 fun i => (r i : ZMod 11)) ∧
    evalGateTraceMod 0 1 (List.ofFn z) satDecoder.code.1 = 0 ∧
    eqCubeMod 0 (List.ofFn r) (List.ofFn z) = 0 ∧
    evalClauseUnsatMod 0 (List.ofFn z)
      (List.ofFn fun j : Fin 3 => (satDecoder.outputs (SuccinctVerifier.signWire 1 j)).toNat)
      (List.ofFn fun _ : Fin 3 => 1) = 0 ∧
    evalConstraintMod 0 1 satDecoder.code.1 (List.ofFn r) (List.ofFn z)
      (List.ofFn fun j : Fin 3 => (satDecoder.outputs (SuccinctVerifier.signWire 1 j)).toNat)
      (List.ofFn fun _ : Fin 3 => 1) = 0 := by
  dsimp only
  have hfold_gate (n : ℕ) (gates : List (Op × List ℕ)) :
      (gates.foldl (fun acc _ => (acc.1 + 1, 0)) (n, 0)).2 = 0 := by
    induction gates generalizing n <;> simp [*]
  have hfold_const {ι : Type} (l : List ι) : l.foldl (fun _ _ => 0) 0 = 0 := by
    induction l <;> simp [*]
  refine ⟨natCast_evalConstraintMod (p := 11) (by norm_num) satDecoder _ _ _ _ fun j => ?_,
    ?_, ?_, ?_, ?_⟩
  · have hz_eq : (fun i : Fin 1 =>
        ((if (Fin.append (![false] : Fin 1 → Bool)
            (fun u : Fin satDecoder.size =>
              (evalCode interpretation false (List.ofFn ![false]) satDecoder.code.1).getD
                (1 + u.val) false))
            ⟨(satDecoder.outputs (SuccinctVerifier.addressWire 1 j i)).toNat,
              Wire.toNat_lt _⟩
          then 1 else 0 : ℕ) : ZMod 11)) =
        bitPoint (R := ZMod 11) fun _ => false := by
      funext i
      have hidx :
          (⟨(satDecoder.outputs (SuccinctVerifier.addressWire 1 j i)).toNat,
              Wire.toNat_lt _⟩ : Fin (1 + satDecoder.size)) =
            Fin.castAdd satDecoder.size ⟨0, by decide⟩ := by
        fin_cases i
        fin_cases j <;> exact Fin.ext (by decide)
      simp [hidx, Fin.append_left, bitPoint, bitVal]
    rw [hz_eq, eval_multilinearExtension]
    simp [bitVal]
  · simp [evalGateTraceMod, hfold_gate]
  · simp [eqCubeMod, hfold_const]
  · simp [evalClauseUnsatMod, hfold_const]
  · simp [evalConstraintMod]

-- Uniform polynomial-time certificate instantiation for `evalConstraintMod`.
private abbrev ModEvalArgs : Type :=
  ℕ × ℕ × List (Op × List ℕ) × List ℕ × List ℕ × List ℕ × List ℕ

private abbrev encModEvalArgs : ModEvalArgs ↪ List Bool :=
  encPair encNat (encPair encNat (encPair (encList encGate)
    (encPair (encList encNat) (encPair (encList encNat)
      (encPair (encList encNat) (encList encNat))))))

example :
    ComputableInPolyTime
      (fun a : ModEvalArgs =>
        evalConstraintMod a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1 a.2.2.2.2.2.2)
      encModEvalArgs encNat := by
  have hp : ComputableInPolyTime (fun a : ModEvalArgs => a.1) encModEvalArgs encNat := fst _ _
  have hr1 : ComputableInPolyTime (fun a : ModEvalArgs => a.2) encModEvalArgs
      (encPair encNat (encPair (encList encGate)
        (encPair (encList encNat) (encPair (encList encNat)
          (encPair (encList encNat) (encList encNat)))))) := snd _ _
  have hQ : ComputableInPolyTime (fun a : ModEvalArgs => a.2.1) encModEvalArgs encNat :=
    (fst _ _).comp hr1
  have hr2 : ComputableInPolyTime (fun a : ModEvalArgs => a.2.2) encModEvalArgs
      (encPair (encList encGate) (encPair (encList encNat) (encPair (encList encNat)
        (encPair (encList encNat) (encList encNat))))) := (snd _ _).comp hr1
  have hgates : ComputableInPolyTime (fun a : ModEvalArgs => a.2.2.1)
      encModEvalArgs (encList encGate) := (fst _ _).comp hr2
  have hr3 : ComputableInPolyTime (fun a : ModEvalArgs => a.2.2.2) encModEvalArgs
      (encPair (encList encNat) (encPair (encList encNat)
        (encPair (encList encNat) (encList encNat)))) := (snd _ _).comp hr2
  have hrVec : ComputableInPolyTime (fun a : ModEvalArgs => a.2.2.2.1)
      encModEvalArgs (encList encNat) := (fst _ _).comp hr3
  have hr4 : ComputableInPolyTime (fun a : ModEvalArgs => a.2.2.2.2) encModEvalArgs
      (encPair (encList encNat) (encPair (encList encNat) (encList encNat))) := (snd _ _).comp hr3
  have hz : ComputableInPolyTime (fun a : ModEvalArgs => a.2.2.2.2.1)
      encModEvalArgs (encList encNat) := (fst _ _).comp hr4
  have hr5 : ComputableInPolyTime (fun a : ModEvalArgs => a.2.2.2.2.2) encModEvalArgs
      (encPair (encList encNat) (encList encNat)) := (snd _ _).comp hr4
  have hsign : ComputableInPolyTime (fun a : ModEvalArgs => a.2.2.2.2.2.1)
      encModEvalArgs (encList encNat) := (fst _ _).comp hr5
  have hlit : ComputableInPolyTime (fun a : ModEvalArgs => a.2.2.2.2.2.2)
      encModEvalArgs (encList encNat) := (snd _ _).comp hr5
  exact computableInPolyTime_evalConstraintMod hp hQ hgates hrVec hz hsign hlit

private def acceptAct : Universal.Act := ⟨0, [], some 1, none⟩

private def acceptDesc : Universal.Desc :=
  ⟨0, 0, [(⟨0, none, []⟩, acceptAct), (⟨0, some 0, []⟩, acceptAct), (⟨0, some 1, []⟩, acceptAct)]⟩

-- Concrete `NEXPBoundedAcceptance` accepting and rejecting instances routed through
-- `exists_succinctDecoder_of_mem_NEXP`.
example :
    let aAcc : NEXPBoundedAcceptanceInstance := ⟨acceptDesc, [true], 1⟩
    let aRej : NEXPBoundedAcceptanceInstance := ⟨acceptDesc, [true], 0⟩
    ∃ (k : ℕ) (State : Type) (_ : Fintype State) (_ : DecidableEq State)
      (tm : MultiTapeTM k Bool State) (n T : NEXPBoundedAcceptanceInstance → ℕ),
      ComputableInPolyTime (fun a =>
        Tableau.Decoder.decoderCode tm (frame (encNEXPBoundedAcceptanceInstance a), n a, T a))
        encNEXPBoundedAcceptanceInstance encCode ∧
      PolyBounded (fun a => (encNEXPBoundedAcceptanceInstance a).length)
        (fun a => Tableau.clauseBits k State (T a) + Tableau.labelBits k State (T a)) ∧
      (Tableau.succinctCNF tm (frame (encNEXPBoundedAcceptanceInstance aAcc))
          (n aAcc) (T aAcc)).Satisfiable ∧
      ¬ (Tableau.succinctCNF tm (frame (encNEXPBoundedAcceptanceInstance aRej))
          (n aRej) (T aRej)).Satisfiable ∧
      (∃ cAcc : Circuit signature (Tableau.clauseBits k State (T aAcc))
          (3 * (Tableau.labelBits k State (T aAcc) + 1)),
        cAcc.size ≤ Tableau.Decoder.sizeConst tm *
          (Tableau.colBits (T aAcc) + Tableau.timeBits (T aAcc) +
            (frame (encNEXPBoundedAcceptanceInstance aAcc)).length + 1)) := by
  dsimp only
  obtain ⟨k, State, hfin, hdecEq, tm, n, T, hcode, hwidths, hmem⟩ :=
    exists_succinctDecoder_of_mem_NEXP NEXPBoundedAcceptance.mem_NEXP
  let aAcc : NEXPBoundedAcceptanceInstance := ⟨acceptDesc, [true], 1⟩
  let aRej : NEXPBoundedAcceptanceInstance := ⟨acceptDesc, [true], 0⟩
  have haAcc : aAcc ∈ NEXPBoundedAcceptance :=
    NEXPBoundedAcceptance.mem_iff.mpr ⟨[false], by decide, by decide⟩
  have haRej : aRej ∉ NEXPBoundedAcceptance := by
    intro h
    obtain ⟨c, -, hc⟩ := NEXPBoundedAcceptance.mem_iff.mp h
    exact Bool.false_ne_true (congrArg Prod.snd hc)
  obtain ⟨hsat_acc, cAcc, _, hsize_acc, _⟩ := hmem aAcc
  obtain ⟨hsat_rej, _⟩ := hmem aRej
  exact ⟨k, State, hfin, hdecEq, tm, n, T, hcode, hwidths, hsat_acc.mp haAcc,
    fun h => haRej (hsat_rej.mpr h), ⟨cAcc, hsize_acc⟩⟩

-- Routing `NEXPBoundedAcceptance` through `exists_succinctCNF_of_mem_NEXP`,
-- `Tableau.Decoder.exists_decoder`, and `satisfiable_toCNF_iff_succinctCNF`.
example :
    ∃ (k : ℕ) (State : Type) (_ : Fintype State) (_ : DecidableEq State)
      (tm : MultiTapeTM k Bool State) (n T : NEXPBoundedAcceptanceInstance → ℕ),
      ComputableInPolyTime (fun a =>
        Tableau.Decoder.decoderCode tm (frame (encNEXPBoundedAcceptanceInstance a), n a, T a))
        encNEXPBoundedAcceptanceInstance encCode ∧
      (∃ cAcc : Circuit signature (Tableau.clauseBits k State (T ⟨acceptDesc, [true], 1⟩))
          (3 * (Tableau.labelBits k State (T ⟨acceptDesc, [true], 1⟩) + 1)),
        (SuccinctVerifier.toCNF cAcc).Satisfiable) ∧
      ¬ (Tableau.succinctCNF tm (frame (encNEXPBoundedAcceptanceInstance ⟨acceptDesc, [true], 0⟩))
          (n ⟨acceptDesc, [true], 0⟩) (T ⟨acceptDesc, [true], 0⟩)).Satisfiable := by
  obtain ⟨k, State, hfin, hdecEq, tm, n, T, hn_pt, hT_pt, -, hmem⟩ :=
    exists_succinctCNF_of_mem_NEXP NEXPBoundedAcceptance.mem_NEXP
  let aAcc : NEXPBoundedAcceptanceInstance := ⟨acceptDesc, [true], 1⟩
  let aRej : NEXPBoundedAcceptanceInstance := ⟨acceptDesc, [true], 0⟩
  have haAcc : aAcc ∈ NEXPBoundedAcceptance :=
    NEXPBoundedAcceptance.mem_iff.mpr ⟨[false], by decide, by decide⟩
  have haRej : aRej ∉ NEXPBoundedAcceptance := by
    intro h
    obtain ⟨c, -, hc⟩ := NEXPBoundedAcceptance.mem_iff.mp h
    exact Bool.false_ne_true (congrArg Prod.snd hc)
  obtain ⟨hlen_acc, hlt_acc, hsat_acc⟩ := hmem aAcc
  obtain ⟨_, _, hsat_rej⟩ := hmem aRej
  obtain ⟨cAcc, _, _, hcAcc⟩ :=
    @Tableau.Decoder.exists_decoder k State hfin hdecEq tm
      (frame (encNEXPBoundedAcceptanceInstance aAcc)) (n aAcc) (T aAcc) hlt_acc hlen_acc
  have henc : ComputableInPolyTime encNEXPBoundedAcceptanceInstance
      encNEXPBoundedAcceptanceInstance encBits := of_eq fun _ => rfl
  have hframe : ComputableInPolyTime
      (fun a => frame (encNEXPBoundedAcceptanceInstance a))
      encNEXPBoundedAcceptanceInstance encBits := by fun_prop
  have harg := hframe.prod (hn_pt.prod hT_pt)
  refine ⟨k, State, hfin, hdecEq, tm, n, T,
    (@computableInPolyTime_decoderCode k State hfin hdecEq tm).comp harg,
    ⟨cAcc, (satisfiable_toCNF_iff_succinctCNF tm hlt_acc hlen_acc cAcc hcAcc).mpr
      (hsat_acc.mp haAcc)⟩,
    fun h => haRej (hsat_rej.mpr h)⟩

end CslibFrontierTests.BFLArithmetization
