/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Algorithms.Lean.HousingMarket.Characterization
public import Mathlib.Data.Fin.VecNotation

/-!
# Checked tests for TTC cycle-order independence, group incentives, and Ma's characterization

Kernel-checked (`decide`, zero `native_decide`) witnesses and axiom-independence counterexamples
exercising `SequentialCycles`, `GroupIncentives`, and `Characterization`:

1. **Boundary cases (`n = 0, 1`)**: agreement of `ttc`, `ttcSingleCycle`, and `serialDictatorship`.
2. **Simultaneous vs. sequential single-cycle elimination (`ex4TwoCycles`, `n = 4`)**: a 4-agent
   market whose Round-1 pointer graph consists of two disjoint 2-cycles `{0, 1}` and `{2, 3}`:
   `cycleAgents` removes all four agents in one round, `singleCycleSelector` removes `{0, 1}` then
   `{2, 3}`, and `maxCycleSelector` removes `{2, 3}` then `{0, 1}`, all yielding the same
   allocation `![1, 0, 3, 2]` (`CycleSelector.ttc_eq_ttc`, `ttcSingleCycle_eq_ttc`).
3. **Coalitional invariance & group strategy-proofness (`exCoal3`, `n = 3`)**: checked coalitional
   deviations and non-bossy misreports under `updatePrefs`.
4. **Independence of every axiom in Ma's characterization (`eq_topTradingCycles_iff`) and strict
   separation of `IsWeakGroupStrategyProof` from `IsGroupStrategyProof` (`bossyDictator`)**:
   * dropping `IsParetoEfficient`: `keepEndowment` satisfies `IsIndividuallyRational` and
     `IsGroupStrategyProof`, but fails `IsParetoEfficient`;
   * dropping `IsIndividuallyRational`: `serialDictatorship` satisfies `IsParetoEfficient` and
     `IsGroupStrategyProof`, but fails `IsIndividuallyRational` on `exSD3`;
   * dropping `IsStrategyProof`: `altIRPEMechanism` satisfies `IsIndividuallyRational` and
     `IsParetoEfficient` on every 3-agent market, differs from `topTradingCycles` on `exAltIRPE`,
     and fails `IsStrategyProof`;
   * dropping `IsNonBossy` (`bossyDictator`): satisfies `IsStrategyProof` and
     `IsWeakGroupStrategyProof`, yet fails `IsNonBossy` and `IsGroupStrategyProof`.
-/

@[expose] public section

namespace CslibFrontierTests.HousingMarketCharacterization

open Cslib.Algorithms.Lean.HousingMarket
open Cslib.Algorithms.Lean.StableMatching (permOfInjective)
open Function

/-- Helper constructing a preference permutation on `Fin k` from an injective vector. -/
abbrev pref {k : ℕ} (v : Fin k → Fin k) (h : Injective v := by decide) : Equiv.Perm (Fin k) :=
  permOfInjective v h

/-! ### 1. Boundary cases (`n = 0` and `n = 1`) -/

def emptyMarket : Instance 0 := ⟨Fin.elim0⟩

example :
    emptyMarket.ttcSingleCycle = 1 ∧
      emptyMarket.serialDictatorship = 1 ∧
      (HousingMechanism.topTradingCycles (n := 0)) = HousingMechanism.serialDictatorship := by
  refine ⟨by decide, by decide, ?_⟩
  funext I
  exact Subsingleton.elim _ _

def singleMarket : Instance 1 := ⟨fun _ => 1⟩

example :
    singleMarket.ttcSingleCycle = singleMarket.ttc ∧
      singleMarket.serialDictatorship = singleMarket.ttc := by
  decide

/-! ### 2. Disjoint simultaneous cycles (`n = 4`): single-cycle & reverse-order selectors -/

/-- Four-agent market with two disjoint Round-1 2-cycles `{0, 1}` and `{2, 3}`. -/
def ex4TwoCycles : Instance 4 :=
  ⟨![pref ![1, 2, 3, 0],
     pref ![0, 2, 3, 1],
     pref ![3, 0, 1, 2],
     pref ![2, 0, 1, 3]]⟩

/-- Reverse-index single-cycle selector choosing the directed cycle of `(I.cycleAgents R).max'`. -/
def maxCycleSelector (I : Instance 4) : I.CycleSelector :=
  Instance.CycleSelector.ofSeed
    (fun R hR => (I.cycleAgents R).max' (I.cycleAgents_nonempty hR))
    (fun R hR => (I.cycleAgents R).max'_mem (I.cycleAgents_nonempty hR))

/-- Simultaneous TTC removes `{0, 1, 2, 3}` at once, `singleCycleSelector` peels `{0, 1}` first, and
`maxCycleSelector` peels `{2, 3}` first; all three compute `![1, 0, 3, 2]`. -/
theorem ex4TwoCycles_order_independence :
    ex4TwoCycles.cycleAgents Finset.univ = {0, 1, 2, 3} ∧
      ex4TwoCycles.singleCycle Finset.univ = {0, 1} ∧
      (maxCycleSelector ex4TwoCycles).select Finset.univ = {2, 3} ∧
      ex4TwoCycles.ttcSingleCycle = pref ![1, 0, 3, 2] ∧
      (maxCycleSelector ex4TwoCycles).ttc = ex4TwoCycles.ttc :=
  ⟨by decide, by decide, by decide, by decide, (maxCycleSelector ex4TwoCycles).ttc_eq_ttc⟩

/-! ### 3. Coalitional invariance & non-bossiness on a 3-agent market -/

/-- Market where `{0, 1}` trade in Round 1 and agent `2` receives its last choice `2` in Round 2. -/
def exCoal3 : Instance 3 :=
  ⟨![pref ![1, 2, 0], pref ![0, 1, 2], pref ![1, 0, 2]]⟩

/-- Agent `0` changing its ranking between houses `2` and `0` below its TTC house `1` keeps agent
`0`'s TTC house equal to `1`, and by non-bossiness (`ttc_updatePref_eq_of_apply_eq`) leaves the
entire allocation unchanged. -/
example :
    (exCoal3.updatePref 0 (pref ![1, 0, 2])).ttc 0 = exCoal3.ttc 0 ∧
      (exCoal3.updatePref 0 (pref ![1, 0, 2])).ttc = exCoal3.ttc :=
  ⟨by decide, exCoal3.ttc_updatePref_eq_of_apply_eq (by decide)⟩

/-- Exhaustive check over all pairs of reports by coalition `{0, 2}` on `exCoal3` confirming no weak
Pareto improvement for `{0, 2}` under TTC. -/
example :
    ∀ π₀ π₂ : Equiv.Perm (Fin 3),
      let π : Fin 3 → Equiv.Perm (Fin 3) := ![π₀, exCoal3.pref 1, π₂]
      ¬ ((∀ i ∈ ({0, 2} : Finset (Fin 3)),
            exCoal3.rank i ((exCoal3.updatePrefs {0, 2} π).ttc i) ≤
              exCoal3.rank i (exCoal3.ttc i)) ∧
          ∃ i ∈ ({0, 2} : Finset (Fin 3)),
            exCoal3.rank i ((exCoal3.updatePrefs {0, 2} π).ttc i) <
              exCoal3.rank i (exCoal3.ttc i)) :=
  fun π₀ π₂ => HousingMechanism.isGroupStrategyProof_topTradingCycles exCoal3 {0, 2}
    ![π₀, exCoal3.pref 1, π₂]

/-! ### 4. Axiom-independence counterexamples for Ma's characterization & Pápai–Svensson -/

/-- Mechanism returning the initial endowment on every 3-agent market. -/
def keepEndowment3 : HousingMechanism 3 := fun _ => 1

/-- Dropping `IsParetoEfficient`: `keepEndowment3` is individually rational and strongly group
strategy-proof, yet fails Pareto efficiency. -/
theorem keepEndowment3_ir_gsp_not_pe :
    keepEndowment3.IsIndividuallyRational ∧
      keepEndowment3.IsGroupStrategyProof ∧
      ¬ keepEndowment3.IsParetoEfficient := by
  refine ⟨fun _ _ => le_rfl, ?_, ?_⟩
  · exact HousingMechanism.isGroupStrategyProof_iff.2 ⟨fun _ _ _ => le_rfl, fun _ _ _ _ => rfl⟩
  · intro hPE
    exact absurd (hPE ⟨![pref ![1, 0, 2], pref ![0, 1, 2], pref ![2, 0, 1]]⟩) (by decide)

/-- Market where both agent `0` and agent `1` rank house `1` first, so `serialDictatorship` assigns
house `1` to dictator `0` and forces agent `1` to accept house `0` (worse than its endowment `1`).
-/
def exSD3 : Instance 3 :=
  ⟨![pref ![1, 0, 2], pref ![1, 0, 2], pref ![2, 0, 1]]⟩

/-- Dropping `IsIndividuallyRational`: `serialDictatorship` on 3 agents is Pareto efficient and
strongly group strategy-proof, yet fails individual rationality on `exSD3`. -/
theorem serialDictatorship3_pe_gsp_not_ir :
    (HousingMechanism.serialDictatorship (n := 3)).IsParetoEfficient ∧
      (HousingMechanism.serialDictatorship (n := 3)).IsGroupStrategyProof ∧
      ¬ (HousingMechanism.serialDictatorship (n := 3)).IsIndividuallyRational := by
  refine ⟨HousingMechanism.isParetoEfficient_serialDictatorship,
    HousingMechanism.isGroupStrategyProof_serialDictatorship, ?_⟩
  intro hIR
  exact absurd (hIR exSD3) (by decide)

/-- Market admitting a second individually rational and Pareto-efficient allocation `![2, 1, 0]`
distinct from `exAltIRPE.ttc = ![1, 0, 2]`. -/
def exAltIRPE : Instance 3 :=
  ⟨![pref ![1, 2, 0], pref ![0, 1, 2], pref ![0, 1, 2]]⟩

/-- Mechanism agreeing with TTC everywhere except on `exAltIRPE`, where it selects the alternative
IR and Pareto-efficient allocation `![2, 1, 0]`. -/
def altIRPEMechanism : HousingMechanism 3 := fun I =>
  if I.pref = exAltIRPE.pref then pref ![2, 1, 0] else I.ttc

/-- Dropping `IsStrategyProof`: `altIRPEMechanism` is individually rational and Pareto efficient on
every 3-agent market, yet fails strategy-proofness (agent `0` gains at `exAltIRPE` by reporting
`![1, 0, 2]`). -/
theorem altIRPEMechanism_ir_pe_not_sp :
    altIRPEMechanism.IsIndividuallyRational ∧
      altIRPEMechanism.IsParetoEfficient ∧
      ¬ altIRPEMechanism.IsStrategyProof := by
  refine ⟨fun I => ?_, fun I => ?_, fun hSP => ?_⟩
  · dsimp only [altIRPEMechanism]
    by_cases h : I.pref = exAltIRPE.pref
    · rw [ite_eq_left h, Instance.ext (congrFun h)]
      decide
    · rw [ite_eq_right h]
      exact I.isIndividuallyRational_ttc
  · dsimp only [altIRPEMechanism]
    by_cases h : I.pref = exAltIRPE.pref
    · rw [ite_eq_left h, Instance.ext (congrFun h)]
      decide
    · rw [ite_eq_right h]
      exact I.isParetoEfficient_ttc
  · exact absurd (hSP exAltIRPE 0 (pref ![1, 0, 2])) (by decide)

/-- Bossy mechanism where agent `0` always keeps house `0`, while agent `0`'s relative ranking of
houses `1` and `2` determines whether `{1, 2}` swap houses. -/
def bossyDictator : HousingMechanism 3 := fun I =>
  if I.rank 0 1 < I.rank 0 2 then Equiv.swap 1 2 else 1

/-- Strict separation of `IsWeakGroupStrategyProof` from `IsGroupStrategyProof` (and necessity of
`IsNonBossy` in `isGroupStrategyProof_iff`): `bossyDictator` is strategy-proof and weakly group
strategy-proof, yet fails both `IsNonBossy` and `IsGroupStrategyProof`. -/
theorem bossyDictator_weakGSP_not_GSP :
    bossyDictator.IsStrategyProof ∧
      bossyDictator.IsWeakGroupStrategyProof ∧
      ¬ bossyDictator.IsNonBossy ∧
      ¬ bossyDictator.IsGroupStrategyProof := by
  have h0_fixed : ∀ I : Instance 3, bossyDictator I 0 = 0 := by
    intro I
    dsimp only [bossyDictator]
    split_ifs <;> decide
  have hWGSP : bossyDictator.IsWeakGroupStrategyProof := by
    intro I S π hSne hlt
    by_cases h0S : (0 : Fin 3) ∈ S
    · have h0 := hlt 0 h0S
      rw [h0_fixed, h0_fixed] at h0
      exact lt_irrefl _ h0
    · have hsame : bossyDictator (I.updatePrefs S π) = bossyDictator I := by
        dsimp only [bossyDictator]
        rw [I.updatePrefs_rank_of_notMem h0S π]
      obtain ⟨i, hiS⟩ := hSne
      have hi := hlt i hiS
      rw [hsame] at hi
      exact lt_irrefl _ hi
  have hnotNB : ¬ bossyDictator.IsNonBossy := by
    intro hNB
    let I₀ : Instance 3 := ⟨![pref ![0, 2, 1], pref ![2, 1, 0], pref ![1, 2, 0]]⟩
    have heq0 : bossyDictator (I₀.updatePref 0 (pref ![0, 1, 2])) 0 = bossyDictator I₀ 0 := by
      decide
    have hfull := hNB I₀ 0 (pref ![0, 1, 2]) heq0
    exact absurd (congrArg (fun μ => μ 1) hfull) (by decide)
  exact ⟨hWGSP.isStrategyProof, hWGSP, hnotNB,
    fun hGSP => hnotNB hGSP.isNonBossy⟩

end CslibFrontierTests.HousingMarketCharacterization
