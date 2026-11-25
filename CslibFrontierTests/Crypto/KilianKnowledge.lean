/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.Crypto.Computational.Kilian.Knowledge
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Tests for bounded-prefix raw Kilian verification and amplified compact-table extraction

Non-vacuous checked clients for:
* `kilianVerifyRawBounded`, `kilianRawProverCap`, `kilianHonestRawBoundedGame`, and
  `eval_kilianHonestRawBoundedGame`: concrete `decide` checks for acceptance, oversized raw
  rejection, and prefix-truncation invariance;
* `computableInTimeAndSpace_kilianVerifyRawBounded_of_params`: one fixed binary `MultiTapeTM`
  with polynomial time/space in `n + ch.stmt.length` over arbitrary unbounded `rawProver`;
* `KilianRawProver`, `KilianRawProver.IsPPT.toKilianProver`, and `HashFamily.kilianRawSound`;
* `kilianTablePassesFrac`, `computableInPolyTime_kilianTablePassesFrac`,
  `isPPT_kilianAmplifiedExtractor`, `HashFamily.kilianAmplifiedTableExtraction`, and
  `HashFamily.kilianRawAmplifiedExtraction`; and
* `exists_kilianSuccinctTableExtractionArgument_of_npRelation` instantiated on `headTrueRel`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.KilianKnowledge

open Cslib Cslib.Complexity Cslib.Crypto Cslib.Probability
open Turing.MultiTapeTM
open scoped NNReal

/-- Key-returning hash used to exercise concrete deterministic raw-verifier checks. -/
def constHash (k _ : List Bool) : List Bool := k

theorem length_constHash (k x : List Bool) : (constHash k x).length = k.length := rfl

theorem polyTime_constHash :
    ComputableInPolyTime (fun p : List Bool × List Bool => constHash p.1 p.2)
      (encPair encBits encBits) encBits :=
  ComputableInPolyTime.fst encBits encBits

/-- A one-coin, one-query PCP verifier whose `queryTable` has 2 entries (`[1000, 5]`). -/
def toyVerifier : PCPVerifier (List Bool) where
  coins _ := 1
  queries := fun (_, ρ) => [if ρ.headD false then 5 else 1000]
  verdict := fun (_, answers) => answers == [true]

theorem polyTime_toyVerifier : toyVerifier.PolyTime encBits where
  coins := by unfold toyVerifier; fun_prop
  queries := by unfold toyVerifier; fun_prop
  verdict := by unfold toyVerifier; fun_prop

/-- A strict PPT structured prover matching `KilianExtraction.constantProver`. -/
def constantProver : KilianProver (List Bool) where
  commit _ k := pure { stmt := [true, false], root := k, state := [] }
  answer _ _ ρs := pure (ρs.map fun _ => [])

theorem isPPT_constantProver : constantProver.IsPPT encBits where
  commit := by unfold constantProver; ppt
  answer := by unfold constantProver; ppt

/-- A strict PPT raw prover emitting empty raw second-stage bytes. -/
def rawConstantProver : KilianRawProver (List Bool) where
  commit _ k := pure { stmt := [true, false], rawRoot := k, state := [] }
  answer _ _ _ := pure []

theorem isPPT_rawConstantProver : rawConstantProver.IsPPT encBits where
  commit := by unfold rawConstantProver; ppt
  answer := by unfold rawConstantProver; ppt

/-- Non-trivial concrete NP relation: words starting with `true`, certificate `[true]`. -/
noncomputable def headTrueRel : NPRelation encBits where
  certLength := 1
  verifier := fun (x, w) => x.headD false && w.headD false
  computableInPolyTime_verifier := by fun_prop

theorem headTrueRel_witness : headTrueRel.IsWitness [true] [true] := by
  simp [headTrueRel, NPRelation.IsWitness]

-- Concrete bounded-prefix raw verification: honest wire bytes pass, oversized bytes reject.
example :
    let key : List Bool := [false, true]
    let x : List Bool := [true, false]
    let ch : KilianChallengeInput (List Bool) := ⟨key, x, [[false], [true]]⟩
    let root := kilianCommit constHash toyVerifier key x [true, true]
    let resp := kilianRespond constHash toyVerifier key x [true, true] [[false], [true]]
    let wire := encPair encBits encKilianResponse (root, resp)
    kilianVerifyRawBounded constHash toyVerifier ch wire = true ∧
    kilianVerifyRawBounded constHash toyVerifier ch (wire ++ List.replicate 500 true) = false ∧
    kilianVerifyRawBounded constHash toyVerifier ch (List.replicate 500 false) = false := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [kilianVerifyRawBounded_enc_eq_of_root_le constHash toyVerifier
      ⟨[false, true], [true, false], [[false], [true]]⟩ _ _
      (by simp [kilianCommit, length_merkleRoot, length_constHash])]
    decide
  · refine kilianVerifyRawBounded_eq_false_of_cap_lt constHash toyVerifier ?_
    rw [List.length_append, List.length_replicate]
    dsimp only
    have hlt :
        kilianRawProverCap toyVerifier [false, true] [true, false] [[false], [true]] < 500 := by
      decide
    omega
  · refine kilianVerifyRawBounded_eq_false_of_cap_lt constHash toyVerifier ?_
    rw [List.length_replicate]
    decide

-- Concrete compact-table coin-fraction check (`kilianTablePassesFrac`).
example :
    kilianTablePassesFrac toyVerifier 1 2
      { stmt := [true, false], root := [true], table := [true, true] } = true ∧
    kilianTablePassesFrac toyVerifier 1 2
      { stmt := [true, false], root := [true], table := [false, false] } = false := by
  decide

-- Prefix truncation invariance and equivalence on honest transcripts.
example (N : ℕ) :
    let key : List Bool := [false, true]
    let x : List Bool := [true, false]
    let ch : KilianChallengeInput (List Bool) := ⟨key, x, [[false], [true]]⟩
    let cap := kilianRawProverCap toyVerifier key x [[false], [true]]
    kilianVerifyRawBounded constHash toyVerifier ch (List.replicate N true) =
      kilianVerifyRawBounded constHash toyVerifier ch ((List.replicate N true).take (cap + 1)) :=
  kilianVerifyRawBounded_take_eq constHash toyVerifier _ _

example :
    toyVerifier.tableVerifier ([true, false], [true, true]) = true →
    ProbComp.eval
        (kilianHonestRawBoundedGame constHash toyVerifier [true, false] [true, true] 2) =
      PMF.pure true :=
  fun h => eval_kilianHonestRawBoundedGame length_constHash h 2

-- Worst-case bounded-prefix raw-tape verifier machine for all unbounded `rawProver`.
example :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State)
      (tBound sBound : ℕ → ℕ),
      PolynomiallyBounded tBound ∧ PolynomiallyBounded sBound ∧
      ∀ (n : ℕ) (ch : KilianChallengeInput (List Bool)) (N : ℕ),
        ch.key.length ≤ n → ch.challenges.length ≤ n →
        (∀ ρ ∈ ch.challenges, ρ.length ≤ toyVerifier.coins ch.stmt) →
          tm.ComputesInTimeAndSpace
            (encPair (encKilianChallengeInput encBits) encBits (ch, List.replicate N true))
            (encBool (kilianVerifyRawBounded constHash toyVerifier ch (List.replicate N true)))
            (tBound (n + ch.stmt.length))
            (sBound (n + ch.stmt.length)) := by
  obtain ⟨k, State, hfin, tm, _, _, tBound, sBound, _, _, htB, hsB, _, hrun⟩ :=
    computableInTimeAndSpace_kilianVerifyRawBounded_of_params
      (H := constHash) (V := toyVerifier) (enc := encBits) (c := 1)
      polyTime_constHash length_constHash polyTime_toyVerifier fun _ => by simp [toyVerifier]
  exact ⟨k, State, hfin, tm, tBound, sBound, htB, hsB,
    fun n ch N hk hn hρs => hrun n ch (List.replicate N true) hk hn hρs⟩

-- Concrete poly-time fraction check and amplified strict-PPT extractor certificate.
example :
    ComputableInPolyTime (kilianTablePassesFrac toyVerifier 1 2)
      (encKilianExtractedTable encBits) encBool ∧
    IsPPT (encOption (encKilianExtractedTable encBits))
      (fun n _ => kilianAmplifiedExtractor constHash toyVerifier constantProver
        (fun n => n * (n + 1)) (fun n => (n + 1) * n) 1 2 n) := by
  have hT : ComputableInPolyTime (fun n : ℕ => n * (n + 1)) encUnary encUnary := by fun_prop
  have hR : ComputableInPolyTime (fun n : ℕ => (n + 1) * n) encUnary encUnary := by fun_prop
  exact ⟨computableInPolyTime_kilianTablePassesFrac polyTime_toyVerifier
      (c := 1) (fun _ => by simp [toyVerifier]) 1 2,
    isPPT_kilianAmplifiedExtractor polyTime_constHash length_constHash polyTime_toyVerifier
      (c := 1) (fun _ => by simp [toyVerifier]) isPPT_constantProver hT hR 1 2⟩

-- Raw prover conversion preserves strict PPT and gives raw soundness + raw amplified extraction.
example {H : List Bool → List Bool → List Bool} (hH : HashFamily H)
    {L : Set (List Bool)} {c : ℕ} {q : ℕ → ℕ}
    (hpcp : IsPCPVerifier encBits (fun m => c * (Nat.log 2 m + 1)) q toyVerifier L) :
    rawConstantProver.toKilianProver.IsPPT encBits ∧
    Negligible (fun n =>
      Game.succProbability
        (ProbComp.eval (kilianRawSoundnessGame H toyVerifier L rawConstantProver n))) :=
  ⟨isPPT_rawConstantProver.toKilianProver,
    hH.kilianRawSound polyTime_toyVerifier hpcp rawConstantProver isPPT_rawConstantProver⟩

-- Asymptotic amplified compact-table extraction for both structured and raw provers.
example {H : List Bool → List Bool → List Bool} (hH : HashFamily H) :
    (∃ T R : ℕ → ℕ,
      ComputableInPolyTime T encUnary encUnary ∧
      ComputableInPolyTime R encUnary encUnary ∧
      IsPPT (encOption (encKilianExtractedTable encBits))
        (fun n _ => kilianAmplifiedExtractor H toyVerifier constantProver T R 1 2 n) ∧
      ∃ ν : ℕ → ℝ≥0, Negligible ν ∧
        ∀ n : ℕ,
          ((n + 1 : ℕ) : ℝ≥0)⁻¹ + ((n + 1 : ℕ) : ℝ≥0)⁻¹ + ν n ≤
            Game.succProbability (ProbComp.eval (kilianAcceptGame H toyVerifier constantProver n)) →
          1 - (Game.succProbability (ProbComp.eval
            (kilianAmplifiedExtractionGame H toyVerifier constantProver T R 1 2 n)) : ℝ) ≤
            (1 / 2 : ℝ) ^ n) ∧
    (∃ T R : ℕ → ℕ,
      ComputableInPolyTime T encUnary encUnary ∧
      ComputableInPolyTime R encUnary encUnary ∧
      IsPPT (encOption (encKilianExtractedTable encBits))
        (fun n _ => kilianAmplifiedExtractor H toyVerifier
          rawConstantProver.toKilianProver T R 1 2 n) ∧
      ∃ ν : ℕ → ℝ≥0, Negligible ν ∧
        ∀ n : ℕ,
          ((n + 1 : ℕ) : ℝ≥0)⁻¹ + ((n + 1 : ℕ) : ℝ≥0)⁻¹ + ν n ≤
            Game.succProbability (ProbComp.eval
              (kilianRawAcceptGame H toyVerifier rawConstantProver n)) →
          1 - (Game.succProbability (ProbComp.eval
            (kilianAmplifiedExtractionGame H toyVerifier
              rawConstantProver.toKilianProver T R 1 2 n)) : ℝ) ≤
            (1 / 2 : ℝ) ^ n) := by
  obtain ⟨T₁, R₁, hT₁, hR₁, hExt₁, -, ν₁, hν₁, hamp₁⟩ :=
    hH.kilianAmplifiedTableExtraction polyTime_toyVerifier
      (c := 1) (fun _ => by simp [toyVerifier]) isPPT_constantProver id id
      ComputableInPolyTime.id' ComputableInPolyTime.id' (num := 1) (den := 2) (by norm_num)
  obtain ⟨T₂, R₂, hT₂, hR₂, hExt₂, -, ν₂, hν₂, hamp₂⟩ :=
    hH.kilianRawAmplifiedExtraction polyTime_toyVerifier
      (c := 1) (fun _ => by simp [toyVerifier]) isPPT_rawConstantProver id id
      ComputableInPolyTime.id' ComputableInPolyTime.id' (num := 1) (den := 2) (by norm_num)
  exact ⟨⟨T₁, R₁, hT₁, hR₁, hExt₁, ν₁, hν₁, hamp₁⟩, ⟨T₂, R₂, hT₂, hR₂, hExt₂, ν₂, hν₂, hamp₂⟩⟩

-- Unified NP argument with bounded-prefix verifier & table extraction on `headTrueRel`.
example {H : List Bool → List Bool → List Bool} (hH : HashFamily H) :
    ∃ (V : PCPVerifier (List Bool)) (compile : List Bool × List Bool → List Bool),
      ComputableInPolyTime compile (encPair encBits encBits) encBits ∧
      (∀ n, ProbComp.eval (kilianHonestRawBoundedGame H V [true] (compile ([true], [true])) n) =
        PMF.pure true) ∧
      KilianRawSound H V encBits headTrueRel.language ∧
      (∀ (P : KilianRawProver (List Bool)), P.IsPPT encBits →
        ∃ T R_rep : ℕ → ℕ,
          ComputableInPolyTime T encUnary encUnary ∧
          ComputableInPolyTime R_rep encUnary encUnary ∧
          IsPPT (encOption (encKilianExtractedTable encBits))
            (fun n _ => kilianAmplifiedExtractor H V P.toKilianProver T R_rep 1 2 n) ∧
          (∀ (n : ℕ) (ext : KilianExtractedTable (List Bool)),
            some ext ∈ (ProbComp.eval
              (kilianAmplifiedExtractor H V P.toKilianProver T R_rep 1 2 n)).support →
              ∃ w, headTrueRel.IsWitness ext.stmt w) ∧
          ∃ ν : ℕ → ℝ≥0, Negligible ν ∧
            ∀ n : ℕ,
              ((n + 1 : ℕ) : ℝ≥0)⁻¹ + ((n + 1 : ℕ) : ℝ≥0)⁻¹ + ν n ≤
                Game.succProbability (ProbComp.eval (kilianRawAcceptGame H V P n)) →
              1 - (Game.succProbability (ProbComp.eval
                (kilianAmplifiedExtractionGame H V P.toKilianProver T R_rep 1 2 n)) : ℝ) ≤
                (1 / 2 : ℝ) ^ n) := by
  obtain ⟨V, compile, _, _, -, -, -, hcompile, -, -, -, -, hhonest, -, -, -, hrawSound, -,
    -, hrawExt⟩ :=
    exists_kilianSuccinctTableExtractionArgument_of_npRelation hH encBits headTrueRel
  refine ⟨V, compile, hcompile, fun n => (hhonest [true] [true] headTrueRel_witness n).1,
    hrawSound, fun P hP => ?_⟩
  obtain ⟨T, R_rep, hT, hR, hExt, hsupp, ν, hν, hamp⟩ :=
    hrawExt P hP id id ComputableInPolyTime.id' ComputableInPolyTime.id'
  exact ⟨T, R_rep, hT, hR, hExt, fun n ext hex => (hsupp n ext hex).2, ν, hν, hamp⟩

end CslibFrontierTests.Crypto.KilianKnowledge
