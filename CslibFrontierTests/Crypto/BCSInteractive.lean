/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module

import CslibFrontier.Crypto.Protocols.BCS.Interactive
import CslibFrontier.Probability.PMF.UniformBound

/-!
# Tests for Interactive Public-Coin IOP Execution (`CslibFrontier.Crypto.Protocols.BCS.Interactive`)

Exercises `CslibFrontier.Crypto.Protocols.BCS.Interactive` directly from an ordinary `module` client
with **zero** FRI imports, verifying that any public-coin IOP caller can import and apply
`InteractiveIOPProver`, `InteractiveIOPProver.ofCausal`, `iopRunRounds`, `iopInteractiveGame`,
`iopPrefixEscape_le_sum`, `iopCommitPhase_map_true_le_sum`, `iopInteractiveGame_le_sum`,
`iopInteractiveGame_ofCausal_eq`, and `iopEscape_le_sup_of_perRound` on standalone 2-round
public-coin IOPs (`bitPairIOP`, `checkZeroIOP`) against both causal honest provers and
prefix-dependent randomized cheating provers.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.BCSInteractive

open scoped BigOperators NNReal ENNReal
open Cslib.Crypto.Protocols.BCS Cslib.Probability

/-- A 2-round, depth-1 public-coin IOP over `Bool` with 4-value challenges `Fin 4`:
* Round `0` commits to a 2-bit table; round `1` commits to a second 2-bit table after seeing `c₀`.
* On statement `x : Bool`, the verifier checks `π₀ (c₀ % 2) == x` and
  `π₁ (c₁ % 2) == xor x (c₀ == 0)`. -/
def bitPairIOP : PublicCoinIOP 2 1 Bool Bool Bool (Fin 4) where
  proveRound j _ w prev :=
    if h : j.val = 0 then
      fun _ => w
    else
      fun _ => xor w (prev ⟨0, Nat.pos_of_ne_zero h⟩ == 0)
  queries _ chals :=
    [(⟨0, by decide⟩, ⟨(chals ⟨0, by decide⟩).val % 2, Nat.mod_lt _ (by decide)⟩),
     (⟨1, by decide⟩, ⟨(chals ⟨1, by decide⟩).val % 2, Nat.mod_lt _ (by decide)⟩)]
  decide x chals answers :=
    answers == [x, xor x (chals ⟨0, by decide⟩ == 0)]

theorem bitPairIOP_complete : IOPCompleteness bitPairIOP (fun x w => x = w) := by
  intro x w hxw chals
  subst hxw
  simp [iopVerify, iopAnswers, iopProverOracles, prefixChallenges, bitPairIOP]

/-- Honest causal prover accepts with probability `1` (`PMF.pure true`) in `iopInteractiveGame`. -/
theorem bitPairIOP_honestCausal_eq_pure_true (x : Bool) :
    iopInteractiveGame bitPairIOP x
      (InteractiveIOPProver.ofCausal fun j prev => bitPairIOP.proveRound j x x prev) =
      PMF.pure true := by
  refine (iopInteractiveGame_ofCausal_eq bitPairIOP x _).trans ?_
  have hacc :
      (fun chals : Fin 2 → Fin 4 =>
        iopVerify bitPairIOP x chals
          (fun j => bitPairIOP.proveRound j x x fun i => chals ⟨i.val, lt_trans i.isLt j.isLt⟩)) =
      Function.const _ true := by
    funext chals
    exact bitPairIOP_complete x x rfl chals
  rw [hacc, PMF.map_const]

/-- A 2-round public-coin IOP accepting `x = true` unconditionally and accepting `x = false` only
when `c₀ = 0`, `c₁ = c₀`, and the two round tables disagree at `0`. -/
def checkZeroIOP : PublicCoinIOP 2 1 Bool Unit Bool (Fin 4) where
  proveRound _ _ _ _ := fun _ => true
  queries _ _ :=
    [(⟨0, by decide⟩, ⟨0, by decide⟩), (⟨1, by decide⟩, ⟨0, by decide⟩)]
  decide x chals answers :=
    x || ((chals ⟨0, by decide⟩ == 0) && (chals ⟨1, by decide⟩ == chals ⟨0, by decide⟩) &&
      (answers == [true, false]))

def checkZeroDoomed (x : Bool) (pref : List (OracleTable 1 Bool × Fin 4)) : Prop :=
  x = false ∧
    match pref with
    | [] => True
    | (_, c₀) :: [] => c₀ ≠ 0
    | (_, c₀) :: (_, c₁) :: _ => c₀ ≠ 0 ∨ c₁ ≠ c₀

def checkZeroGoodStep (_ : Bool) (pref : List (OracleTable 1 Bool × Fin 4))
    (_ : OracleTable 1 Bool) (c : Fin 4) : Prop :=
  match pref with
  | [] => c ≠ 0
  | (_, c₀) :: [] => c₀ ≠ 0 ∨ c ≠ c₀
  | _ :: _ :: _ => True

theorem checkZeroIOP_rbrSound :
    IOPRoundByRoundSoundness checkZeroIOP {true} checkZeroDoomed checkZeroGoodStep where
  init_doomed x hx := by
    cases x
    · exact ⟨rfl, trivial⟩
    · exact absurd rfl hx
  step_doomed x pref _ c hd hg := by
    rcases hd with ⟨hx, hd'⟩
    refine ⟨hx, ?_⟩
    rcases pref with _ | ⟨⟨_, _⟩, _ | ⟨⟨_, _⟩, _⟩⟩
    · exact hg
    · exact hg
    · exact hd'
  reject_of_doomed x oracles chals hd := by
    rcases hd with ⟨hx, hd'⟩
    subst hx
    dsimp only [List.ofFn, Fin.foldr, Fin.foldr.loop, checkZeroDoomed] at hd'
    simp only [iopVerify, checkZeroIOP, Bool.false_or, Bool.and_eq_false_imp]
    intro h01
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h01
    rcases hd' with hne0 | hne1
    · exact absurd h01.1 hne0
    · exact absurd h01.2 hne1

private theorem checkZero_perRound_escape :
    ∀ x ∉ ({true} : Set Bool), ∀ (j : Fin 2) pref π,
      pref.length = j.val → checkZeroDoomed x pref →
      (PMF.uniformOfFintype (Fin 4)).toOuterMeasure
        {c : Fin 4 | ¬ checkZeroGoodStep x pref π c} ≤ (1 : ℝ≥0∞) / 4 := by
  intro x _ j pref π hlen hd
  fin_cases j
  · rcases pref with _ | ⟨_, _⟩
    · have hcard : 4 * (Finset.univ.filter fun c : Fin 4 => ¬ (c ≠ 0)).card ≤ 1 * 4 := by
        decide
      simpa only [checkZeroGoodStep, Set.mem_ofPred_eq, Fintype.card_fin, Nat.cast_one,
        Nat.cast_ofNat] using
        Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_le_div (α := Fin 4)
          (P := fun c : Fin 4 => ¬ (c ≠ 0)) (by decide) hcard
    · simp at hlen
  · rcases pref with _ | ⟨⟨π₀, c₀⟩, _ | ⟨_, _⟩⟩
    · simp at hlen
    · have hc₀ : c₀ ≠ 0 := hd.2
      have hempty : {c : Fin 4 | ¬ checkZeroGoodStep x [(π₀, c₀)] π c} = ∅ := by
        ext c
        simp [checkZeroGoodStep, hc₀]
      rw [hempty]
      exact (MeasureTheory.OuterMeasure.empty _).trans_le zero_le
    · simp at hlen

/-- Adaptive prefix-dependent randomized cheating prover on `checkZeroIOP`: in round `0`
(`pref = []`), samples a uniform constant table; after round `0` (`pref = (_, c₀) :: _`), replies
deterministically with the all-`false` table when `c₀ = 0` and mixes constant tables uniformly
otherwise. -/
noncomputable def adaptiveBitProver : InteractiveIOPProver 1 Bool (Fin 4)
  | [] => (PMF.uniformOfFintype Bool).map fun b _ => b
  | (_, c₀) :: _ =>
    if c₀ = 0 then
      PMF.pure (fun _ => false)
    else
      (PMF.uniformOfFintype Bool).map fun b _ => b

/-- Witness that `adaptiveBitProver` genuinely changes its conditional output distribution across
prefixes (both between round `0` and round `1`, and between two round-`1` prefixes with `c₀ = 0`
vs. `c₀ = 1`): `(fun _ => true)` has positive mass at `[]` and at `[(fun _ => false, 1)]`, but zero
mass at `[(fun _ => false, 0)]`. -/
theorem adaptiveBitProver_prefix_dependent :
    adaptiveBitProver [] ≠ adaptiveBitProver [(fun _ => false, 0)] ∧
      adaptiveBitProver [(fun _ => false, 0)] ≠ adaptiveBitProver [(fun _ => false, 1)] := by
  have hnot_zero : (fun _ : Fin 2 => true) ∉
      (adaptiveBitProver [(fun _ => false, 0)]).support := by
    rw [adaptiveBitProver, ite_eq_left rfl, PMF.support_pure, Set.mem_singleton_iff]
    intro h
    exact Bool.false_ne_true (congrFun h 0).symm
  refine ⟨fun heq => hnot_zero (heq ▸ ?_), fun heq => hnot_zero (heq.symm ▸ ?_)⟩
  · rw [adaptiveBitProver, PMF.mem_support_map_iff]
    exact ⟨true, PMF.mem_support_uniformOfFintype true, rfl⟩
  · rw [adaptiveBitProver, ite_eq_right (by decide : (1 : Fin 4) ≠ 0), PMF.mem_support_map_iff]
    exact ⟨true, PMF.mem_support_uniformOfFintype true, rfl⟩

/-- Standalone `iopInteractiveGame_le_sum` test (`≤ 1 / 4 + 1 / 4 = 1 / 2`) with zero FRI imports.
-/
theorem checkZeroIOP_adaptive_le_half :
    iopInteractiveGame checkZeroIOP false adaptiveBitProver true ≤ 1 / 2 := by
  refine (iopInteractiveGame_le_sum checkZeroIOP_rbrSound (fun _ => (1 : ℝ≥0∞) / 4)
    checkZero_perRound_escape (by simp) adaptiveBitProver).trans_eq ?_
  rw [Fin.sum_univ_two]
  have hnn : ((1 / 4 + 1 / 4 : ℝ≥0) : ℝ≥0∞) = ((1 / 2 : ℝ≥0) : ℝ≥0∞) :=
    congrArg _ (by norm_num)
  simpa only [ENNReal.coe_add, ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0), ENNReal.coe_one, ENNReal.coe_ofNat] using hnn

/-- Standalone `iopCommitPhase_map_true_le_sum` test (`≤ 1 / 4`) after round `0`. -/
example :
    (((iopRunRounds adaptiveBitProver 1 []).bind fun pref =>
      (adaptiveBitProver pref).map fun _ =>
        match pref with
        | (_, c₀) :: [] => decide (c₀ = 0)
        | _ => false) true) ≤ 1 / 4 := by
  have hrbr := checkZeroIOP_rbrSound
  have hx : false ∉ ({true} : Set Bool) := by simp
  refine (iopCommitPhase_map_true_le_sum (hrbr.init_doomed false hx) (hrbr.step_doomed false)
    1 (fun _ => (1 : ℝ≥0∞) / 4)
    (fun j pref π hlen hd =>
      checkZero_perRound_escape false hx ⟨j.val, by omega⟩ pref π hlen hd)
    adaptiveBitProver _ ?_).trans_eq (by simp)
  intro pref _ hlen hd
  rcases pref with _ | ⟨⟨_, c₀⟩, _ | _⟩
  · simp at hlen
  · exact decide_eq_false hd.2
  · simp at hlen

/-- Standalone `iopEscape_le_sup_of_perRound` test. -/
example :
    ∀ x ∉ ({true} : Set Bool), ∀ pref π, checkZeroDoomed x pref →
      (PMF.uniformOfFintype (Fin 4)).toOuterMeasure
        {c : Fin 4 | ¬ checkZeroGoodStep x pref π c} ≤
      Finset.univ.sup (fun _ : Fin 2 => (1 : ℝ≥0∞) / 4) :=
  iopEscape_le_sup_of_perRound (fun _ : Fin 2 => (1 : ℝ≥0∞) / 4) checkZero_perRound_escape
    fun _ _ pref _ _ hge => by
      rcases pref with _ | ⟨_, _ | ⟨_, _⟩⟩
      · simp at hge
      · simp at hge
      · trivial

end CslibFrontierTests.Crypto.BCSInteractive
