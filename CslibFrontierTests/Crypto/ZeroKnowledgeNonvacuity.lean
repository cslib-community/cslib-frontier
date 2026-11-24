/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.ZeroKnowledge.AuxClock
import CslibFrontier.Crypto.Computational.ZeroKnowledge.Soundness
import CslibFrontier.Computability.Probabilistic.Oracle.SubstitutionGrowth
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.PolyTime

/-!
# Nonvacuity witnesses for zero-knowledge and soundness assumptions

Concrete insecure instances showing that none of the library's zero-knowledge or soundness
assumptions holds vacuously:

* **Soundness (`ZKProof.NegligibleSoundness`).** `alwaysAcceptZKProof` is a valid `ZKProof` for
  the singleton language `{[]}` whose verifier always returns `true` and whose prover answers
  every message with `[]`. It satisfies completeness, soundness `1`, and `GenerableZeroKnowledge`
  (simulated identically by running the verifier against the empty oracle), but fails
  `ZKProof.NegligibleSoundness` (`not_negligibleSoundness_alwaysAccept`).
* **Zero knowledge (`GenerableZeroKnowledge`, `InstanceAuxiliaryInputZeroKnowledge`,
  `UnboundedAuxiliaryInputZeroKnowledge`, `AuxiliaryInputZeroKnowledge`).** On the trivial
  witness relation `anyWitness _ _ = true`, the witness-leaking prover `leakWitnessProver`
  returns the witness `w` verbatim. A one-query malicious verifier reads the first bit of `w`.
  No simulator (which sees only the instance and auxiliary input, not `w`) can simultaneously
  match both valid witnesses `[false]` and `[true]` within negligible distinguishing advantage,
  refuting all four zero-knowledge predicates.
-/

namespace CslibFrontierTests.Crypto.ZeroKnowledgeNonvacuity

open Cslib Cslib.Complexity Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-! ### Helper lemmas -/

private theorem eval_run_const_eq_zkRealView (reply : List Bool)
    (prog : WordOracleComp Unit (List Bool)) :
    ProbComp.eval (prog.run (fun _ => pure reply)) = zkRealView (Prover.const reply) prog := by
  have hresp : (Prover.const (Operation := Unit) reply).respond =
      fun _ s => (PMF.pure reply).map (·, s) := by
    funext q s
    simp [Prover.const]
  rw [ProbOracleComp.eval_run, zkRealView, Prover.run, hresp,
    ProbOracleComp.runWith_memoryless, PMF.map_comp,
    show (Prod.fst ∘ fun x : List Bool => (x, (Prover.const (Operation := Unit) reply).init)) = id
      from rfl,
    PMF.map_id, OracleComp.evalWith_eq_interpret]
  rfl

private theorem one_le_advantage_pure_false_add_pure_true (μ : Game) :
    (1 : ℝ≥0) ≤ Game.advantage (PMF.pure false) μ + Game.advantage (PMF.pure true) μ := by
  rw [Game.advantage_comm (PMF.pure true) μ]
  simpa [Game.advantage, Game.succProbability] using
    Game.advantage_triangle (PMF.pure false) μ (PMF.pure true)

/-! ### Nonvacuity of `ZKProof.NegligibleSoundness` -/

/-- A trivial `ZKProof` for `{[]}` whose verifier always accepts and whose prover always replies
`[]`: it has perfect completeness, soundness bound `1`, and zero-advantage `GenerableZeroKnowledge`,
while failing `ZKProof.NegligibleSoundness`. -/
noncomputable def alwaysAcceptZKProof : ZKProof encBits ({[]} : Set (List Bool)) (fun _ => 1) where
  verifier _ _ := pure true
  prover _ _ _ := Prover.const []
  isWitness a _ := decide (a = [])
  polyTime_isWitness := by polytime
  mem_iff_exists_witness a := by simp
  isOraclePPT_verifier := (ComputableInPolyTime.const true).isOraclePPTOn
  interact _ _ _ prog := prog.run (fun _ => pure [])
  eval_interact _ _ _ prog := eval_run_const_eq_zkRealView [] prog
  isPPT_interact Vstar hV := by
    have hprep : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool × List Bool => (p.1, p.2.1, p.2.2.2))
        (encInstanceWitnessAuxInput encBits) (encInstanceAuxInput encBits) :=
      (ComputableInPolyTime.fst encUnary _).prod
        (((ComputableInPolyTime.fst encBits _).comp (ComputableInPolyTime.snd encUnary _)).prod
          ((ComputableInPolyTime.snd encBits encBits).comp
            ((ComputableInPolyTime.snd encBits _).comp (ComputableInPolyTime.snd encUnary _))))
    convert hV.isPPTOn_runEmptyOracle.preprocess hprep using 1
  complete _ _ _ _ := by simp [acceptProb]
  sound _ _ _ _ := by simp [acceptProb]
  zero_knowledge Vstar hV := by
    refine ⟨fun n a z => (Vstar n a z).run (fun _ => pure []), hV.isPPTOn_runEmptyOracle,
      fun a w z _ _ _ _ adversary _ => ?_⟩
    have hzero : (fun n => Game.advantage
        (distinguishingGame (zkRealView (Prover.const []) (Vstar n (a n) (z n))) (adversary n))
        (distinguishingGame
          (ProbComp.eval ((Vstar n (a n) (z n)).run (fun _ => pure []))) (adversary n))) =
        fun _ => 0 := by
      ext n
      rw [eval_run_const_eq_zkRealView, Game.advantage_self]
    rw [hzero]
    exact negligible_zero

/-- **`ZKProof.NegligibleSoundness` fails for the always-accepting `ZKProof`.** -/
theorem not_negligibleSoundness_alwaysAccept : ¬ alwaysAcceptZKProof.NegligibleSoundness := by
  intro h
  have hneg : Negligible (fun _ : ℕ => (1 : ℝ≥0)) := by
    simpa [alwaysAcceptZKProof] using h.2
  exact not_negligible_const one_ne_zero hneg

/-! ### Nonvacuity of the zero-knowledge predicates -/

/-- Witness predicate admitting every witness word. -/
def anyWitness : List Bool → List Bool → Bool := fun _ _ => true

/-- Maliciously leaky prover: answers every verifier query with the witness `w` itself. -/
noncomputable def leakWitnessProver : ℕ → List Bool → List Bool → Prover Unit :=
  fun _ _ w => Prover.const w

/-- One-query malicious verifier: asks the prover one empty message and reads the first bit. -/
noncomputable def askWitness : ℕ → List Bool → List Bool → WordOracleComp Unit (List Bool) :=
  fun _ _ _ => List.take 1 <$> ProbOracleComp.query ((), [])

theorem isOraclePPTOn_askWitness :
    IsOraclePPTOn (encInstanceAuxInput encBits) encBits (fun ⟨n, a, z⟩ => askWitness n a z) :=
  IsOraclePPTOn.query_take () (ComputableInPolyTime.const []) (ComputableInPolyTime.const 1)

theorem isOraclePPTWithAux_askWitness :
    IsOraclePPTWithAux encBits encBits (fun a z => askWitness a.length a z) := by
  have h : IsOraclePPTOn (encPair encBits encBits) encBits
      (fun (p : List Bool × List Bool) => askWitness p.1.length p.1 p.2) :=
    IsOraclePPTOn.query_take () (ComputableInPolyTime.const []) (ComputableInPolyTime.const 1)
  simpa [askWitness] using
    h.isOraclePPTWithAux_take (program := fun a z => askWitness a.length a z) 0 0

private theorem zkRealView_leakWitness_askWitness (n : ℕ) (a w z : List Bool) :
    zkRealView (leakWitnessProver n a w) (askWitness n a z) = PMF.pure (w.take 1) := by
  unfold leakWitnessProver
  rw [← eval_run_const_eq_zkRealView]
  simp [askWitness, ProbOracleComp.run]

/-- Distinguisher accepting iff the view equals `[true]`. -/
noncomputable def isTrueView : List Bool → ProbComp Bool :=
  fun view => pure (decide (view = [true]))

private theorem eval_distinguishingGame_isTrueView (b : Bool) :
    distinguishingGame (PMF.pure [b]) isTrueView = PMF.pure b := by
  cases b <;> simp [distinguishingGame_eq_bind, isTrueView]

/-- **`GenerableZeroKnowledge` fails for the witness-leaking prover**: no simulator can match
both polytime-generable valid witness families `[false]` and `[true]`. -/
theorem not_generableZeroKnowledge_leakWitness :
    ¬ GenerableZeroKnowledge encBits leakWitnessProver anyWitness := by
  intro hzk
  obtain ⟨S, _, hS⟩ := hzk askWitness isOraclePPTOn_askWitness
  have hD : IsPPT encBool (fun _ view => isTrueView view) := by
    unfold isTrueView
    ppt
  have h0 := hS (fun _ => []) (fun _ => [false]) (fun _ => [])
    (ComputableInPolyTime.const []) (ComputableInPolyTime.const [false])
    (ComputableInPolyTime.const []) (fun _ => rfl) (fun _ view => isTrueView view) hD
  have h1 := hS (fun _ => []) (fun _ => [true]) (fun _ => [])
    (ComputableInPolyTime.const []) (ComputableInPolyTime.const [true])
    (ComputableInPolyTime.const []) (fun _ => rfl) (fun _ view => isTrueView view) hD
  have hsum := h0.add h1
  have hge : ∀ n, (1 : ℝ≥0) ≤
      Game.advantage
        (distinguishingGame (zkRealView (leakWitnessProver n [] [false]) (askWitness n [] []))
          (isTrueView))
        (distinguishingGame (ProbComp.eval (S n [] [])) isTrueView) +
      Game.advantage
        (distinguishingGame (zkRealView (leakWitnessProver n [] [true]) (askWitness n [] []))
          (isTrueView))
        (distinguishingGame (ProbComp.eval (S n [] [])) isTrueView) := by
    intro n
    rw [zkRealView_leakWitness_askWitness, zkRealView_leakWitness_askWitness]
    simp only [List.take_succ_cons, List.take_zero, eval_distinguishingGame_isTrueView]
    exact one_le_advantage_pure_false_add_pure_true
      (distinguishingGame (ProbComp.eval (S n [] [])) isTrueView)
  exact not_negligible_const one_ne_zero (negligible_of_le hsum hge)

/-- **`InstanceAuxiliaryInputZeroKnowledge` fails for the witness-leaking prover**: at every
instance length `n`, no simulator can match both length-`1` valid witnesses `[false]` and
`[true]`. -/
theorem not_instanceAuxiliaryInputZeroKnowledge_leakWitness :
    ¬ InstanceAuxiliaryInputZeroKnowledge encBits leakWitnessProver anyWitness := by
  intro hzk
  obtain ⟨S, _, _, _, _, hS⟩ :=
    hzk (fun x z => askWitness x.length x z) isOraclePPTWithAux_askWitness
  have hD_on : IsPPTOn (encPair (encPair encBits encBits) encBits) encBool
      (fun p : (List Bool × List Bool) × List Bool => isTrueView p.1.2) := by
    unfold isTrueView
    ppt
  have hD : IsPPTWithAux (encPair encBits encBits) encBool
      (fun (p : List Bool × List Bool) _ => isTrueView p.2) := by
    simpa using hD_on.isPPTWithAux_take
      (program := fun (p : List Bool × List Bool) _ => isTrueView p.2) 0 0
  have hev := hS (fun _ _ view => isTrueView view) hD 1 0 1
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  let n := max N 2
  have hnN : N ≤ n := le_max_left N 2
  have hn2 : 2 ≤ n := le_max_right N 2
  let x := List.replicate n false
  have hx : (encBits x).length = n := by simp [x]
  have h0 := hN n hnN x [false] [] hx rfl (by simp)
  have h1 := hN n hnN x [true] [] hx rfl (by simp)
  simp only [encBits_apply] at h0 h1
  rw [zkRealView_leakWitness_askWitness, List.take_succ_cons, List.take_zero,
    eval_distinguishingGame_isTrueView] at h0 h1
  have hsum : (1 : ℝ) ≤
      (Game.advantage (PMF.pure false)
        (distinguishingGame (ProbComp.eval (S x [])) isTrueView) : ℝ) +
      (Game.advantage (PMF.pure true)
        (distinguishingGame (ProbComp.eval (S x [])) isTrueView) : ℝ) := by
    exact_mod_cast one_le_advantage_pure_false_add_pure_true
      (distinguishingGame (ProbComp.eval (S x [])) isTrueView)
  have hlt : 1 / ((n : ℝ) + 1) ^ 1 + 1 / ((n : ℝ) + 1) ^ 1 < 1 := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    rw [pow_one]
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    rw [← add_div, div_lt_one hpos]
    linarith
  linarith

/-- **`UnboundedAuxiliaryInputZeroKnowledge` fails for the witness-leaking prover**, since it
implies `InstanceAuxiliaryInputZeroKnowledge`. -/
theorem not_unboundedAuxiliaryInputZeroKnowledge_leakWitness :
    ¬ UnboundedAuxiliaryInputZeroKnowledge encBits leakWitnessProver anyWitness :=
  fun h => not_instanceAuxiliaryInputZeroKnowledge_leakWitness h.instanceAuxiliaryInputZeroKnowledge

/-- **`AuxiliaryInputZeroKnowledge` fails for the witness-leaking prover**, since it implies
`GenerableZeroKnowledge`. -/
theorem not_auxiliaryInputZeroKnowledge_leakWitness :
    ¬ AuxiliaryInputZeroKnowledge encBits leakWitnessProver anyWitness :=
  fun h => not_generableZeroKnowledge_leakWitness h.generableZeroKnowledge

end CslibFrontierTests.Crypto.ZeroKnowledgeNonvacuity
