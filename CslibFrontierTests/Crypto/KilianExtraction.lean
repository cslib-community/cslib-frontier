/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.Crypto.Computational.Kilian.Extraction
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Tests for Merkle vector extraction and Kilian rewinding extraction

Non-vacuous checked clients for:
* `merkleExtractVector`, `merkleVectorBindingOutput`, and
  `getD_merkleExtractVector_or_merkleBreaksBinding`: honest vector reconstruction and explicit
  collision-breaking opening detection;
* `kilianExtractTableFromRuns`, `kilianRunsBindingOutput`, and
  `accepts_kilianExtractTableFromRuns_or_breaksBinding`: deterministic extraction and conflict
  detection on `toyVerifier`;
* `isPPT_kilianTableExtractor`, `isPPT_kilianExtractorBindingAdversary`: uniform strict PPT
  efficiency on an explicit prover and verifier;
* `succProbability_kilianAcceptGame_le_extracted`, `HashFamily.kilianTableExtraction`,
  `kilianExtract_mem_of_isPCP`, and `HashFamily.kilianTableExtraction_npRelation`: non-vacuous
  finite-parameter, asymptotic, and NP-relation compact-table extraction clients.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.KilianExtraction

open Cslib Cslib.Complexity Cslib.Crypto Cslib.Probability
open Turing.MultiTapeTM
open scoped NNReal

/-- Key-returning hash used solely to exercise deterministic Merkle/Kilian extraction. -/
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

/-- A strict PPT prover matching `KilianSoundness.constantProver`. -/
def constantProver : KilianProver (List Bool) where
  commit _ k := pure { stmt := [true, false], root := k, state := [] }
  answer _ _ ρs := pure (ρs.map fun _ => [])

theorem isPPT_constantProver : constantProver.IsPPT encBits where
  commit := by unfold constantProver; ppt
  answer := by unfold constantProver; ppt

/-- Non-trivial concrete NP relation: words starting with `true`, certificate `[true]`. -/
noncomputable def headTrueRel : NPRelation encBits where
  certLength := 1
  verifier := fun (x, w) => x.headD false && w.headD false
  computableInPolyTime_verifier := by fun_prop

theorem headTrueRel_witness : headTrueRel.IsWitness [true] [true] := by
  simp [headTrueRel, NPRelation.IsWitness]

-- Concrete Merkle vector reconstruction on two honest one-bit leaves.
example :
    let key : List Bool := [true]
    let leaves : List (List Bool) := [[false], [true]]
    let root := merkleRoot constHash key leaves
    let openings : List MerkleIndexedOpening :=
      [ { position := 0, opening := ⟨[false], merklePath constHash key leaves 0⟩ },
        { position := 1, opening := ⟨[true], merklePath constHash key leaves 1⟩ } ]
    merkleExtractVector 2 [false] (merkleVerifiedOpenings constHash key 1 2 root openings) =
      [[false], [true]] ∧
    merkleBreaksBinding constHash (fun _ leaf => leaf.length == 1) 1 key
      (merkleVectorBindingOutput root
        (merkleVerifiedOpenings constHash key 1 2 root openings)) = false := by
  decide

-- Concrete conflicting openings of position `0` under `constHash [true]` break binding and yield
-- a concrete collision via `isCollision_of_merkleBreaksBinding`.
example :
    let key : List Bool := [true]
    let root : List Bool := [true]
    let openings : List MerkleIndexedOpening :=
      [ { position := 0, opening := ⟨[false], [[true]]⟩ },
        { position := 0, opening := ⟨[true], [[true]]⟩ } ]
    let verified := merkleVerifiedOpenings constHash key 1 2 root openings
    let out := merkleVectorBindingOutput root verified
    merkleBreaksBinding constHash (fun _ leaf => leaf.length == 1) 1 key out = true ∧
    ∃ c₁ c₂, constHash key c₁ = constHash key c₂ ∧ c₁ ≠ c₂ := by
  have hbrk :
      let key : List Bool := [true]
      let root : List Bool := [true]
      let openings : List MerkleIndexedOpening :=
        [ { position := 0, opening := ⟨[false], [[true]]⟩ },
          { position := 0, opening := ⟨[true], [[true]]⟩ } ]
      let verified := merkleVerifiedOpenings constHash key 1 2 root openings
      let out := merkleVectorBindingOutput root verified
      merkleBreaksBinding constHash (fun _ leaf => leaf.length == 1) 1 key out = true := by
    decide
  refine ⟨hbrk, ?_⟩
  have hcol := isCollision_of_merkleBreaksBinding (H := constHash) length_constHash (n := 1)
    (k := [true]) rfl hbrk
  rw [isCollision_eq_true_iff] at hcol
  rcases hcol with ⟨-, -, hne, heq⟩
  exact ⟨_, _, heq, hne⟩

-- Concrete honest Kilian run reconstruction with `kilianExtractTableFromRuns`.
example :
    let key : List Bool := [false, true]
    let x : List Bool := [true, false]
    let root := kilianCommit constHash toyVerifier key x [true, true]
    let run : KilianChallengeRun :=
      { challenges := [[false], [true]],
        response := kilianRespond constHash toyVerifier key x [true, true] [[false], [true]] }
    let table := kilianExtractTableFromRuns constHash toyVerifier key x root [run]
    table = [true, true] ∧
    toyVerifier.accepts x (toyVerifier.proofOfTable x table) [false] = true ∧
    toyVerifier.accepts x (toyVerifier.proofOfTable x table) [true] = true := by
  have htab :
      let key : List Bool := [false, true]
      let x : List Bool := [true, false]
      let root := kilianCommit constHash toyVerifier key x [true, true]
      let run : KilianChallengeRun :=
        { challenges := [[false], [true]],
          response := kilianRespond constHash toyVerifier key x [true, true] [[false], [true]] }
      kilianExtractTableFromRuns constHash toyVerifier key x root [run] = [true, true] := by
    decide
  refine ⟨htab, ?_, ?_⟩ <;>
    · rw [htab, PCPVerifier.accepts_proofOfTable _ _ _ (by decide)]
      decide

/-- A one-coin verifier querying address `0` and comparing against the coin bit, used to exercise
conflicting accepted runs across different coins. -/
def coinEchoVerifier : PCPVerifier (List Bool) where
  coins _ := 1
  queries := fun (_, _) => [0]
  verdict := fun (p, answers) => answers == [p.2.headD false]

-- Conflicting accepted Kilian runs under `constHash` trigger `kilianRunsBindingOutput`!
example :
    let key : List Bool := [true]
    let x : List Bool := [true]
    let root : List Bool := [true]
    let run₀ : KilianChallengeRun :=
      { challenges := [[false]], response := [[⟨false, [[true]]⟩]] }
    let run₁ : KilianChallengeRun :=
      { challenges := [[true]], response := [[⟨true, [[true]]⟩]] }
    merkleBreaksBinding constHash (fun _ leaf => leaf.length == 1) 1 key
      (kilianRunsBindingOutput constHash coinEchoVerifier key x root [run₀, run₁]) = true := by
  decide

-- Non-vacuous `kilianExtract_mem_of_isPCP` check.
example {r q : ℕ → ℕ} {V : PCPVerifier (List Bool)} {L : Set (List Bool)}
    (hpcp : IsPCPVerifier encBits r q V L) (ext : KilianExtractedTable (List Bool))
    (hfrac : 1 * 2 ^ V.coins ext.stmt <
      2 * acceptCount
        (fun y => V.accepts y.1 (V.proofOfTable ext.stmt ext.table) y.2)
        ext.stmt (V.coins ext.stmt)) :
    ext.stmt ∈ L :=
  kilianExtract_mem_of_isPCP hpcp ext hfrac

-- Efficiency certificates on `toyVerifier` and `constantProver`.
example :
    let T : ℕ → ℕ := fun n => n * (n + 1)
    IsPPT (encKilianExtractedTable encBits) (kilianTableExtractor constHash toyVerifier
      constantProver T) ∧
    IsPPT encMerkleBindingOutput (kilianExtractorBindingAdversary constHash toyVerifier
      constantProver T) := by
  have hT : ComputableInPolyTime (fun n : ℕ => n * (n + 1)) encUnary encUnary := by fun_prop
  exact ⟨isPPT_kilianTableExtractor polyTime_constHash length_constHash polyTime_toyVerifier
      (c := 1) (fun _ => by simp [toyVerifier]) isPPT_constantProver hT,
    isPPT_kilianExtractorBindingAdversary polyTime_constHash length_constHash polyTime_toyVerifier
      (c := 1) (fun _ => by simp [toyVerifier]) isPPT_constantProver hT⟩

-- Finite-parameter instantiation of `succProbability_kilianAcceptGame_le_extracted`.
example :
    (ProbComp.eval (kilianAcceptGame constHash toyVerifier constantProver 2) true).toReal ≤
      ((1 : ℝ) / 2) ^ 2 + (2 : ℝ) * (1 / 4) + (2 : ℝ) * (1 - 1 / 4) ^ 8 +
        (ProbComp.eval (merkleBindingGame constHash (fun _ leaf => leaf.length == 1)
          (kilianExtractorBindingAdversary constHash toyVerifier constantProver (fun _ => 8))
          2) true).toReal +
        (ProbComp.eval (kilianExtractionFracGame constHash toyVerifier constantProver
          (fun _ => 8) 1 2 2) true).toReal := by
  have h := succProbability_kilianAcceptGame_le_extracted (H := constHash) (V := toyVerifier)
    (P := constantProver) (fun _ => 8) 1 2 2 2 (θ := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) fun _ _ _ _ => by simp [toyVerifier]
  exact_mod_cast h

-- Asymptotic compact PCP-table extraction on `toyVerifier` and `constantProver` for `1 / 2` coins.
example {H : List Bool → List Bool → List Bool} (hH : HashFamily H) :
    ∃ T : ℕ → ℕ,
      ComputableInPolyTime T encUnary encUnary ∧
      IsPPT (encKilianExtractedTable encBits) (kilianTableExtractor H toyVerifier
        constantProver T) ∧
      ∃ ν : ℕ → ℝ≥0, Negligible ν ∧
        ∀ n : ℕ,
          Game.succProbability (ProbComp.eval (kilianAcceptGame H toyVerifier constantProver n)) ≤
            Game.succProbability (ProbComp.eval
              (kilianExtractionFracGame H toyVerifier constantProver T 1 2 n)) +
              ((n + 1 : ℕ) : ℝ≥0)⁻¹ + ν n :=
  hH.kilianTableExtraction polyTime_toyVerifier (c := 1) (fun _ => by simp [toyVerifier])
    isPPT_constantProver id ComputableInPolyTime.id' (num := 1) (den := 2) (by norm_num)

-- Non-vacuous `HashFamily.kilianTableExtraction_npRelation` client on `headTrueRel`.
example {H : List Bool → List Bool → List Bool} (hH : HashFamily H) :
    ∃ (V : PCPVerifier (List Bool)) (compile : List Bool × List Bool → List Bool),
      ComputableInPolyTime compile (encPair encBits encBits) encBits ∧
      (∀ ext : KilianExtractedTable (List Bool),
        1 * 2 ^ V.coins ext.stmt <
          2 * acceptCount
            (fun y => V.accepts y.1 (V.proofOfTable ext.stmt ext.table) y.2)
            ext.stmt (V.coins ext.stmt) →
        ∃ w, headTrueRel.IsWitness ext.stmt w) ∧
      ∀ (P : KilianProver (List Bool)), P.IsPPT encBits →
        ∃ T : ℕ → ℕ,
          ComputableInPolyTime T encUnary encUnary ∧
          IsPPT (encKilianExtractedTable encBits) (kilianTableExtractor H V P T) ∧
          ∃ ν : ℕ → ℝ≥0, Negligible ν ∧
            ∀ n : ℕ,
              Game.succProbability (ProbComp.eval (kilianAcceptGame H V P n)) ≤
                Game.succProbability (ProbComp.eval (kilianExtractionFracGame H V P T 1 2 n)) +
                  ((n + 1 : ℕ) : ℝ≥0)⁻¹ + ν n := by
  obtain ⟨V, compile, _, _, -, -, hcompile, -, hwit, hext⟩ :=
    hH.kilianTableExtraction_npRelation encBits headTrueRel
  exact ⟨V, compile, hcompile, hwit, fun P hP => hext P hP id ComputableInPolyTime.id'⟩

end CslibFrontierTests.Crypto.KilianExtraction
