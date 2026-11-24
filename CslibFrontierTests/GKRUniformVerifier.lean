/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Interactive.GKR.Verifier
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.NormNum.Prime

/-!
# Checked witnesses for the polynomial-time GKR word verifier

Non-vacuous `module`-client test instances exercising `UniformGKRFamily.isOraclePPTOn_verifier`,
`UniformGKRFamily.exists_computesOracleInTimeOn_verifier`,
`UniformGKRFamily.acceptProb_verifier_complete`, `UniformGKRFamily.acceptProb_verifier_sound`,
`UniformGKRFamily.verifier_of_lt_minModulus`, and `UniformGKRFamily.mem_IP_primeInstance` on:

1. An exponential-width `powerSumGKRFamily` instance (`midWidth = 60`, `2 ^ 60` gates per internal
   layer, depth `65`) over `ZMod 1000003`.
2. A non-zero arithmetic `powerSumGKRFamily` instance (`[3, 5] ↦ [272]`) over `ZMod 1009`.
3. A clause-wired mixed addition/multiplication family built from `LayeredCircuit.ofClauses`,
   `IsLogSpaceUniform.of_neighbours`, and `hasPolyTimeWiringMLE_ofClauses`.
4. Small- and zero-modulus boundary instances rejected immediately below `minModulus`.
-/

public section

namespace CslibFrontierTests.GKRUniformVerifier

open Cslib Cslib.Interactive Cslib.Interactive.GKR Cslib.BitString Cslib.Complexity
  Cslib.Probability Turing.MultiTapeTM
open scoped ENNReal

/-! ### 1. Exponential internal width (`2 ^ 60` gates per layer) -/

/-- `powerSumCircuit` parameters with `2 ^ 60` gates per internal squaring layer and depth `65`. -/
def expPS : PowerSumParams := ⟨1, 60, 4⟩

theorem expPS_width_internal : (powerSumCircuit expPS).width 1 = 60 := by decide

theorem expPS_minModulus : minModulus (powerSumCircuit expPS) = 31068 := by decide

private theorem powerSumCircuit_value_zero_eq (P : PowerSumParams) {R : Type*} [CommRing R] :
    ∀ i : ℕ, (powerSumCircuit P).value (fun _ => (0 : R)) i = fun _ => 0
  | 0 => rfl
  | i + 1 => by
    funext a
    simp only [LayeredCircuit.value, LayeredCircuit.step, powerSumCircuit_value_zero_eq P i]
    cases (powerSumCircuit P).gate i a <;> simp

/-- All-zero input instance on `expPS` over `ZMod 1000003`. -/
def expZeroInst : Instance PowerSumParams where
  index := expPS
  modulus := 1000003
  input := []
  claimedOutput := [0]

/-- False claimed-output instance `[1]` on `expPS` over `ZMod 1000003`. -/
def expBadInst : Instance PowerSumParams where
  index := expPS
  modulus := 1000003
  input := []
  claimedOutput := [1]

theorem expZeroInst_correct : expZeroInst.CorrectOutput powerSumGKRFamily := by
  rw [Instance.CorrectOutput]
  funext a
  have ha : a = fun j => j.elim0 := funext fun j => j.elim0
  subst ha
  have hzero : tableFn 1000003 ((powerSumCircuit expPS).width 0) [] = fun _ => 0 := by
    funext b
    simp [tableFn]
  change tableFn 1000003 0 [0]
      (fun j => j.elim0) =
    (powerSumCircuit expPS).output (tableFn 1000003 ((powerSumCircuit expPS).width 0) [])
      (fun j => j.elim0)
  rw [hzero, LayeredCircuit.output, powerSumCircuit_value_zero_eq]
  simp [tableFn, binaryValue]

theorem expBadInst_incorrect : ¬ expBadInst.CorrectOutput powerSumGKRFamily := by
  intro h
  have hEval := congrFun h (fun j => j.elim0)
  have hzero : tableFn 1000003 ((powerSumCircuit expPS).width 0) [] = fun _ => 0 := by
    funext b
    simp [tableFn]
  change tableFn 1000003 0 [1] (fun j => j.elim0) =
    (powerSumCircuit expPS).output (tableFn 1000003 ((powerSumCircuit expPS).width 0) [])
      (fun j => j.elim0) at hEval
  rw [hzero, LayeredCircuit.output, powerSumCircuit_value_zero_eq] at hEval
  have h10 : (1 : ZMod 1000003) = 0 := by
    simpa [tableFn, binaryValue] using hEval
  revert h10
  decide

theorem expZeroInst_complete :
    ∃ P : Cslib.Complexity.Prover Unit,
      Complexity.acceptProb (powerSumGKRFamily.verifier expZeroInst) P = 1 :=
  powerSumGKRFamily.acceptProb_verifier_complete expZeroInst (by unfold expZeroInst; norm_num)
    (by decide) expZeroInst_correct

theorem expBadInst_sound (P : Cslib.Complexity.Prover Unit) :
    Complexity.acceptProb (powerSumGKRFamily.verifier expBadInst) P ≤ 10356 / 1000003 := by
  have h := powerSumGKRFamily.acceptProb_verifier_sound expBadInst (by unfold expBadInst; norm_num)
    expBadInst_incorrect P
  have hCost : layerCost (powerSumCircuit expPS) = 10356 := by decide
  simpa [expBadInst, powerSumGKRFamily, hCost] using h

theorem expZero_mem_language :
    (⟨expZeroInst, by unfold expZeroInst; norm_num⟩ : PrimeInstance PowerSumParams) ∈
      {a : PrimeInstance PowerSumParams |
        minModulus (powerSumGKRFamily.circuit a.val.index) ≤ a.val.modulus ∧
          a.val.CorrectOutput powerSumGKRFamily} :=
  ⟨by decide, expZeroInst_correct⟩

theorem powerSumGKRFamily_mem_IP :
    {a : PrimeInstance PowerSumParams |
      minModulus (powerSumGKRFamily.circuit a.val.index) ≤ a.val.modulus ∧
        a.val.CorrectOutput powerSumGKRFamily} ∈
      IP (encPrimeInstance PowerSumParams encPowerSumParams) :=
  powerSumGKRFamily.mem_IP_primeInstance

/-! ### 2. Non-zero arithmetic witness on `powerSumGKRFamily` -/

/-- Small `powerSumCircuit`: `(3 + 3)^2 * 2 + (5 + 5)^2 * 2 = 272`. -/
def smallPS : PowerSumParams := ⟨1, 2, 1⟩

def smallInst : Instance PowerSumParams where
  index := smallPS
  modulus := 1009
  input := [3, 5]
  claimedOutput := [272]

def smallBadInst : Instance PowerSumParams where
  index := smallPS
  modulus := 1009
  input := [3, 5]
  claimedOutput := [273]

theorem smallInst_correct : smallInst.CorrectOutput powerSumGKRFamily := by
  rw [Instance.CorrectOutput]
  funext a
  have ha : a = fun j => j.elim0 := funext fun j => j.elim0
  subst ha
  decide

theorem smallBadInst_incorrect : ¬ smallBadInst.CorrectOutput powerSumGKRFamily := by
  intro h
  have hEval := congrFun h (fun j => j.elim0)
  revert hEval
  decide

theorem smallInst_complete :
    ∃ P : Cslib.Complexity.Prover Unit,
      Complexity.acceptProb (powerSumGKRFamily.verifier smallInst) P = 1 :=
  powerSumGKRFamily.acceptProb_verifier_complete smallInst (by unfold smallInst; norm_num)
    (by decide) smallInst_correct

theorem smallBadInst_sound (P : Cslib.Complexity.Prover Unit) :
    Complexity.acceptProb (powerSumGKRFamily.verifier smallBadInst) P ≤ 31 / 1009 := by
  have h := powerSumGKRFamily.acceptProb_verifier_sound smallBadInst
    (by unfold smallBadInst; norm_num) smallBadInst_incorrect P
  have hCost : layerCost (powerSumCircuit smallPS) = 31 := by decide
  simpa [smallBadInst, powerSumGKRFamily, hCost] using h

/-! ### 3. Mixed addition/multiplication subcube-clause family -/

/-- Unit index encoding for a single clause-wired mixed circuit. -/
def encUnitIdx : Unit ↪ List Bool :=
  ⟨fun _ => [], fun _ _ _ => rfl⟩

/-- Layer widths for the mixed clause circuit: `2^2 = 4` inputs, `2^1 = 2` outputs. -/
def mixedWidth (i : ℕ) : ℕ := if i = 0 then 2 else 1

/-- Clauses assigning gate `0` (`[false]`) to `x[00] + x[01]` and gate `1` (`[true]`) to
`x[10] * x[11]`, exercising non-trivial `mask` subcubes, `WireLit.var`, and both gate kinds. -/
def mixedClauses : List WiringClause :=
  [ ⟨.add, [some false], [.var 0 false, .const false], [.var 0 false, .const true]⟩,
    ⟨.mul, [some true], [.var 0 false, .const false], [.var 0 false, .const true]⟩ ]

/-- One-layer mixed addition/multiplication circuit constructed via `LayeredCircuit.ofClauses`. -/
def mixedCircuit : LayeredCircuit :=
  LayeredCircuit.ofClauses 1 mixedWidth (fun _ => mixedClauses)

private theorem fin_mixed_cases (a : Fin (mixedCircuit.width (0 + 1)) → Bool) :
    a = (fun _ => false) ∨ a = (fun _ => true) := by
  have hw : mixedCircuit.width (0 + 1) = 1 := rfl
  cases h : a ⟨0, by omega⟩
  · exact Or.inl (funext fun j => by
      have hj : j = ⟨0, by omega⟩ := Fin.ext (by omega)
      rw [hj, h])
  · exact Or.inr (funext fun j => by
      have hj : j = ⟨0, by omega⟩ := Fin.ext (by omega)
      rw [hj, h])

private theorem mixedClauses_partition_one : ClausesPartition 1 mixedClauses := by
  intro a
  rcases fin_mixed_cases a with rfl | rfl <;> decide

private theorem mixedClauses_partition (i : ℕ) :
    ClausesPartition (mixedWidth (i + 1)) mixedClauses := by
  have hw : mixedWidth (i + 1) = 1 := ite_eq_right (Nat.succ_ne_zero i)
  rw [hw]
  exact mixedClauses_partition_one

private theorem isLogSpaceUniform_mixedCircuit :
    LayeredCircuit.IsLogSpaceUniform encUnitIdx (fun _ => mixedCircuit) := by
  have hDepth : ComputableInLogSpace (fun _ : Unit => mixedCircuit.depth) encUnitIdx encUnary :=
    ComputableInLogSpace.const 1
  have hWidth : ComputableInLogSpace (fun q : Unit × ℕ => mixedCircuit.width q.2)
      (encPair encUnitIdx encUnary) encUnary :=
    (ComputableInLogSpace.ite_decide
      (ComputableInLogSpace.unaryLeConst 0 (ComputableInLogSpace.snd encUnitIdx encUnary))
      (ComputableInLogSpace.const 2) (ComputableInLogSpace.const 1)).congr_fun fun q => by
        simp [mixedCircuit, LayeredCircuit.ofClauses, mixedWidth]
  have hGqFields : ComputableInLogSpace
      (fun q : GateQuery Unit => (q.index, q.layer, q.outGate))
      (encGateQuery Unit encUnitIdx) (encGateQueryFields Unit encUnitIdx) :=
    ComputableInLogSpace.of_eq (encGateQuery_apply Unit encUnitIdx)
  have hqA : ComputableInLogSpace GateQuery.outGate (encGateQuery Unit encUnitIdx) encBits :=
    ComputableInLogSpace.snd' (ComputableInLogSpace.snd' hGqFields)
  let gateAt : GateQuery Unit → Gate := fun q => if q.outGate.headD false then .mul else .add
  let leftAt : GateQuery Unit → List Bool := fun q => q.outGate.take 1 ++ [false]
  let rightAt : GateQuery Unit → List Bool := fun q => q.outGate.take 1 ++ [true]
  have hHead : ComputableInLogSpace (fun q : GateQuery Unit => q.outGate.headD false)
      (encGateQuery Unit encUnitIdx) encBool :=
    (ComputableInLogSpace.bitsHeadD false).comp' hqA
  have hGateAt : ComputableInLogSpace gateAt (encGateQuery Unit encUnitIdx) encGate :=
    ComputableInLogSpace.ite hHead (ComputableInLogSpace.const Gate.mul)
      (ComputableInLogSpace.const Gate.add)
  have hTake : ComputableInLogSpace (fun q : GateQuery Unit => q.outGate.take 1)
      (encGateQuery Unit encUnitIdx) encBits :=
    (ComputableInLogSpace.of_take_one fun _ => rfl).comp hqA
  have hLeftAt : ComputableInLogSpace leftAt (encGateQuery Unit encUnitIdx) encBits :=
    ComputableInLogSpace.bitsAppend hTake (ComputableInLogSpace.const [false])
  have hRightAt : ComputableInLogSpace rightAt (encGateQuery Unit encUnitIdx) encBits :=
    ComputableInLogSpace.bitsAppend hTake (ComputableInLogSpace.const [true])
  refine LayeredCircuit.IsLogSpaceUniform.of_neighbours hDepth hWidth hGateAt hLeftAt hRightAt
    (fun u i hi a => ?_) (fun u i hi a => ?_) (fun u i hi a => ?_)
  · cases u
    obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    rcases fin_mixed_cases a with rfl | rfl <;> decide
  · cases u
    obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    rcases fin_mixed_cases a with rfl | rfl <;> decide
  · cases u
    obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    rcases fin_mixed_cases a with rfl | rfl <;> decide

/-- `UniformGKRFamily` for the clause-wired mixed addition/multiplication circuit. -/
def mixedGKRFamily : UniformGKRFamily Unit encUnitIdx where
  circuit := fun _ => mixedCircuit
  evalWiring := fun q => evalClausesMod q.modulus (mixedWidth (q.layer + 1)) (mixedWidth q.layer)
    q.gate mixedClauses q.z q.y q.w
  uniform := isLogSpaceUniform_mixedCircuit
  wiringMLE :=
    hasPolyTimeWiringMLE_ofClauses
      isLogSpaceUniform_mixedCircuit.width_polyTime
      (ComputableInLogSpace.const mixedClauses).computableInPolyTime
      (fun _ i _ => mixedClauses_partition i)

def mixedGoodInst : Instance Unit where
  index := ()
  modulus := 101
  input := [3, 5, 7, 11]
  claimedOutput := [8, 77]

def mixedBadInst : Instance Unit where
  index := ()
  modulus := 101
  input := [3, 5, 7, 11]
  claimedOutput := [8, 78]

theorem mixedGoodInst_correct : mixedGoodInst.CorrectOutput mixedGKRFamily := by
  rw [Instance.CorrectOutput]
  funext a
  change tableFn 101 (mixedCircuit.width (0 + 1)) [8, 77] a =
    mixedCircuit.output (tableFn 101 (mixedCircuit.width 0) [3, 5, 7, 11]) a
  rcases fin_mixed_cases a with rfl | rfl <;> decide

theorem mixedBadInst_incorrect : ¬ mixedBadInst.CorrectOutput mixedGKRFamily := by
  intro h
  have hEval := congrFun h (fun _ => true)
  revert hEval
  decide

theorem mixedGoodInst_complete :
    ∃ P : Cslib.Complexity.Prover Unit,
      Complexity.acceptProb (mixedGKRFamily.verifier mixedGoodInst) P = 1 :=
  mixedGKRFamily.acceptProb_verifier_complete mixedGoodInst (by unfold mixedGoodInst; norm_num)
    (by decide) mixedGoodInst_correct

theorem mixedBadInst_sound (P : Cslib.Complexity.Prover Unit) :
    Complexity.acceptProb (mixedGKRFamily.verifier mixedBadInst) P ≤ 12 / 101 := by
  have h := mixedGKRFamily.acceptProb_verifier_sound mixedBadInst (by unfold mixedBadInst; norm_num)
    mixedBadInst_incorrect P
  have hCost : layerCost mixedCircuit = 12 := by decide
  simpa [mixedBadInst, mixedGKRFamily, hCost] using h

theorem mixedGKRFamily_mem_IP :
    {a : PrimeInstance Unit |
      minModulus (mixedGKRFamily.circuit a.val.index) ≤ a.val.modulus ∧
        a.val.CorrectOutput mixedGKRFamily} ∈
      IP (encPrimeInstance Unit encUnitIdx) :=
  mixedGKRFamily.mem_IP_primeInstance

/-! ### 4. Boundary rejections below `minModulus` and explicit TM runtime witness -/

def smallModInst : Instance PowerSumParams :=
  { smallInst with modulus := 2 }

def zeroModInst : Instance PowerSumParams :=
  { smallInst with modulus := 0 }

theorem verifier_smallModInst_eq_pure_false :
    powerSumGKRFamily.verifier smallModInst = pure false :=
  powerSumGKRFamily.verifier_of_lt_minModulus (by decide)

theorem verifier_zeroModInst_eq_pure_false :
    powerSumGKRFamily.verifier zeroModInst = pure false :=
  powerSumGKRFamily.verifier_of_lt_minModulus (by decide)

theorem acceptProb_smallModInst_eq_zero (P : Cslib.Complexity.Prover Unit) :
    Complexity.acceptProb (powerSumGKRFamily.verifier smallModInst) P = 0 := by
  refine Complexity.acceptProb_eq_zero P fun r hr => ?_
  rw [verifier_smallModInst_eq_pure_false, Complexity.Prover.run_pure,
    PMF.mem_support_pure_iff] at hr
  simp [hr]

theorem powerSumGKRFamily_computesOracleInTime :
    ∃ t : Instance PowerSumParams → ℕ,
      PolyBounded (fun inst => (encInstance PowerSumParams encPowerSumParams inst).length) t ∧
      ComputesOracleInTimeOn (encInstance PowerSumParams encPowerSumParams) encBool t
        powerSumGKRFamily.verifier :=
  powerSumGKRFamily.exists_computesOracleInTimeOn_verifier

end CslibFrontierTests.GKRUniformVerifier
