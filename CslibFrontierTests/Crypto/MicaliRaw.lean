/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.Computability.Complexity.Classes.SharpP.Probability
import CslibFrontier.Crypto.Computational.Kilian.MicaliRaw
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for bounded-prefix raw Micali verification, native word-oracle ROM runtime, and soundness

Non-vacuous checked clients for:
* `micaliHasRootPrefix`, `micaliMaxProofCap`, `micaliVerifyRawBoundedPure`, and
  `micaliVerifyRawBoundedPure_take_eq`: concrete `decide` checks for honest raw Micali acceptance,
  oversized raw proof rejection, and prefix-truncation invariance;
* `computableInTimeAndSpace_micaliVerifyRawBoundedPure_of_params`: one fixed binary `MultiTapeTM`
  with polynomial time and space in `m + x.length` uniformly over arbitrary unbounded `rawProof`;
* `micaliVerifyRawBounded`, `evalPure_micaliVerifyRawBounded`,
  `isCostBounded_micaliFSCost_micaliVerifyRawBounded`, and
  `isCostBounded_micaliMTCost_micaliVerifyRawBounded`: native query cost bounds and pure simulation;
* `micaliWordCodec`, `micaliVerifyRawWord`, `runWith_wordOracle_micaliVerifyRawWord`, and
  `computesOracleInTimeAndQueriesOn_micaliVerifyRawWord`: stateful word-oracle bisimulation and one
  fixed halting `MultiTapePTM` running in polynomial time uniformly over all raw proof lengths;
* `micaliHonestRawGame_eq_pure_true`, `micaliRawSoundness_bound`, and
  `exists_micaliRawCSProof_of_npRelation`: raw completeness, adaptive two-channel soundness, and
  logarithmic-size NP CS proofs instantiated on `alwaysRejectVerifier` and `headTrueRel`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.MicaliRaw

open Cslib Cslib.Complexity Cslib.Crypto Cslib.Probability
open Turing.MultiTapeTM
open scoped ENNReal

/-- Constant 2-bit deterministic Merkle compression function used in concrete checks. -/
def constTree (_ : List Bool) : List Bool := [false, true]

theorem length_constTree (x : List Bool) : (constTree x).length = 2 := rfl

theorem polyTime_constTree :
    ComputableInPolyTime constTree encBits encBits :=
  ComputableInPolyTime.const _

/-- Constant 2-challenge Fiat–Shamir function used in concrete checks. -/
def constFS (_ : List Bool × List Bool) : List (List Bool) := [[false], [true]]

theorem polyTime_constFS :
    ComputableInPolyTime constFS (encPair encBits encBits) (encList encBits) :=
  ComputableInPolyTime.const _

/-- A one-coin, one-query PCP verifier whose `queryTable` has 2 entries (`[1000, 5]`). -/
def toyVerifier : PCPVerifier (List Bool) where
  coins _ := 1
  queries := fun (_, ρ) => [if ρ.headD false then 5 else 1000]
  verdict := fun (_, answers) => answers == [true]

theorem polyTime_toyVerifier : toyVerifier.PolyTime encBits where
  coins := by unfold toyVerifier; fun_prop
  queries := by unfold toyVerifier; fun_prop
  verdict := by unfold toyVerifier; fun_prop

/-- A trivial sound PCP verifier for `∅` used to exercise raw ROM soundness concretely. -/
def alwaysRejectVerifier : PCPVerifier (List Bool) where
  coins _ := 1
  queries _ := [0]
  verdict _ := false

/-- Deterministic zero-query raw cheating prover for soundness boundary checks. -/
def toyCheatingProver : OracleComp (MicaliSpec (List Bool)) (List Bool × List Bool) :=
  pure ([], List.replicate 1000 true)

/-- Non-trivial concrete NP relation: words starting with `true`, certificate `[true]`. -/
noncomputable def headTrueRel : NPRelation encBits where
  certLength := 1
  verifier := fun (x, w) => x.headD false && w.headD false
  computableInPolyTime_verifier := by fun_prop

theorem headTrueRel_witness : headTrueRel.IsWitness [true] [true] := by
  simp [headTrueRel, NPRelation.IsWitness]

-- Concrete raw verification: honest framed Micali wire passes; oversized and malformed inputs fail.
example :
    let x : List Bool := [true, false]
    let prf := micaliProvePure constTree constFS toyVerifier x [true, true]
    let wire := encMicaliProof prf
    micaliHasRootPrefix 2 wire = true ∧
    micaliVerifyRawBoundedPure constTree constFS toyVerifier 2 2 x wire = true ∧
    micaliVerifyRawBoundedPure constTree constFS toyVerifier 2 2 x
      (wire ++ List.replicate 500 true) = false ∧
    micaliVerifyRawBoundedPure constTree constFS toyVerifier 2 2 x
      (List.replicate 500 false) = false := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · have hroot :
        (micaliProvePure constTree constFS toyVerifier [true, false] [true, true]).root.length ≤
          2 := by
      decide
    rw [micaliVerifyRawBoundedPure_enc_eq_of_root_le constTree constFS toyVerifier (m := 2) _
      hroot rfl (fun ρ hρ => by
        simp only [constFS, List.mem_cons, List.not_mem_nil, or_false] at hρ
        rcases hρ with rfl | rfl <;> decide)]
    decide
  · refine micaliVerifyRawBoundedPure_eq_false_of_maxCap_lt constTree constFS toyVerifier
      (σ := 2) (m := 2) (d := 1) (fun _ _ _ => by simp [toyVerifier]) ?_
    rw [List.length_append, List.length_replicate]
    have hlt : micaliMaxProofCap toyVerifier 2 2 1 [true, false] < 500 := by decide
    omega
  · refine micaliVerifyRawBoundedPure_eq_false_of_maxCap_lt constTree constFS toyVerifier
      (σ := 2) (m := 2) (d := 1) (fun _ _ _ => by simp [toyVerifier]) ?_
    rw [List.length_replicate]
    decide

-- Prefix truncation invariance and pure simulation with `evalPure_micaliVerifyRawBounded`.
example (N : ℕ) :
    let x : List Bool := [true, false]
    let cap := micaliMaxProofCap toyVerifier 2 2 1 x
    micaliVerifyRawBoundedPure constTree constFS toyVerifier 2 2 x (List.replicate N true) =
      micaliVerifyRawBoundedPure constTree constFS toyVerifier 2 2 x
        ((List.replicate N true).take (cap + 1)) ∧
    OracleComp.evalPure (micaliOracle constTree constFS)
        (micaliVerifyRawBounded toyVerifier 2 2 x (List.replicate N true)) =
      micaliVerifyRawBoundedPure constTree constFS toyVerifier 2 2 x (List.replicate N true) :=
  ⟨micaliVerifyRawBoundedPure_take_eq constTree constFS toyVerifier
      (fun _ _ _ => by simp [toyVerifier]) [true, false] (List.replicate N true),
    evalPure_micaliVerifyRawBounded constTree constFS toyVerifier 2 2 [true, false]
      (List.replicate N true)⟩

-- Honest raw ROM completeness on `toyVerifier`.
example :
    micaliHonestRawGame toyVerifier [true, false] [true, true] 2 2 = PMF.pure true := by
  have htable : toyVerifier.tableVerifier ([true, false], [true, true]) = true := by decide
  exact micaliHonestRawGame_eq_pure_true toyVerifier htable 2 2

-- Worst-case pure Micali verifier binary `MultiTapeTM` uniform over all unbounded `rawProof`.
example :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State)
      (tBound sBound : ℕ → ℕ),
      PolynomiallyBounded tBound ∧ PolynomiallyBounded sBound ∧
      ∀ (m : ℕ) (x : List Bool) (N : ℕ),
        tm.ComputesInTimeAndSpace
          (encMicaliPureVerifierInput encBits ((m, x), List.replicate N true))
          (encBool (micaliVerifyRawBoundedPure constTree constFS toyVerifier 2 m x
            (List.replicate N true)))
          (tBound (m + x.length))
          (sBound (m + x.length)) := by
  obtain ⟨k, State, hfin, tm, _, _, t0, s0, _, _, ht_pb, hs_pb, _, hrun⟩ :=
    computableInTimeAndSpace_micaliVerifyRawBoundedPure_of_params
      (enc := encBits) (hTree := constTree) (hFS := constFS) (V := toyVerifier)
      (σ := 2) (c := 1) (d := 1)
      length_constTree polyTime_constTree polyTime_constFS polyTime_toyVerifier
      (fun _ => by simp [toyVerifier]) (fun _ _ _ => by simp [toyVerifier])
  obtain ⟨ct, dt, htle⟩ := polynomiallyBounded_iff_le.mp ht_pb
  obtain ⟨cs, ds, hsle⟩ := polynomiallyBounded_iff_le.mp hs_pb
  let tBound : ℕ → ℕ := fun u => ct * (u + 1) ^ dt
  let sBound : ℕ → ℕ := fun u => cs * (u + 1) ^ ds
  refine ⟨k, State, hfin, tm, tBound, sBound, by fun_prop, by fun_prop, fun m x N => ?_⟩
  have henc : (encBits x).length = x.length := by simp [encBits_apply]
  have hp := hrun m x (List.replicate N true)
  have ht_le : t0 (m + (encBits x).length) ≤ tBound (m + x.length) :=
    (htle _).trans (Nat.mul_le_mul_left ct (Nat.pow_le_pow_left (by omega) dt))
  have hs_le : s0 (m + (encBits x).length) ≤ sBound (m + x.length) :=
    (hsle _).trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left (by omega) ds))
  exact ⟨hp.1, hp.2.1.mono ht_le, hp.2.2.mono hs_le⟩

-- Native query bounds, stateful word-oracle bisimulation, and uniform word-oracle `MultiTapePTM`.
example (σ m N : ℕ) (x : List Bool) :
    let oracle :
        (q : List Bool ⊕ (List Bool × List Bool)) → StateT Unit PMF (MicaliSpec (List Bool) q) :=
      fun q _ => PMF.pure (micaliOracle constTree constFS q, ())
    ProbOracleComp.runWith ((micaliWordCodec encBits).wordOracle oracle)
        (micaliVerifyRawWord toyVerifier encBits 1 1 (⟨2, m, x⟩, List.replicate N true)) () =
      OracleComp.runWith oracle
        (micaliVerifyRawBounded toyVerifier 2 m x (List.replicate N true)) () ∧
    OracleComp.IsCostBounded micaliFSCost
        (micaliVerifyRawBounded toyVerifier σ m x (List.replicate N true)) 1 ∧
    OracleComp.IsCostBounded micaliMTCost
        (micaliVerifyRawBounded toyVerifier σ m x (List.replicate N true))
        (m * 1 * (kilianDepth toyVerifier x + 1)) ∧
    (∃ tBound : ℕ → ℕ, PolynomiallyBounded tBound ∧
      ComputesOracleInTimeAndQueriesOn (encPair (encMicaliRawInput encBits) encBits) encBool
        (fun p => tBound (p.1.sigma + p.1.reps + (encBits p.1.stmt).length))
        (fun p => 1 + p.1.reps * 1 * (kilianDepth toyVerifier p.1.stmt + 1))
        (micaliVerifyRawWord toyVerifier encBits 1 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine runWith_wordOracle_micaliVerifyRawWord _ (fun _ => by simp [toyVerifier])
      (fun _ _ _ => by simp [toyVerifier]) ?_ _ _ _
    intro w _ d' _ hmem
    simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
    simp [hmem.1, micaliOracle, constTree]
  · exact isCostBounded_micaliFSCost_micaliVerifyRawBounded toyVerifier σ m x _
  · exact isCostBounded_micaliMTCost_micaliVerifyRawBounded (σ := σ) (m := m) (d := 1)
      (fun _ _ _ => by simp [toyVerifier]) x _
  · exact computesOracleInTimeAndQueriesOn_micaliVerifyRawWord polyTime_toyVerifier
      (c := 1) (d := 1) (fun _ => by simp [toyVerifier]) (fun _ _ _ => by simp [toyVerifier])

-- Concrete adaptive two-channel raw ROM soundness bound on `alwaysRejectVerifier` and
-- `toyCheatingProver`.
example (σ m : ℕ) :
    micaliRawSoundnessGame alwaysRejectVerifier (∅ : Set (List Bool)) toyCheatingProver σ m true ≤
      (1 : ℝ≥0∞) * (1 / 2) ^ m +
        ((m * 1 * (kilianDepth alwaysRejectVerifier [] + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (m * 1 * (kilianDepth alwaysRejectVerifier [] + 1)) + 1 : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  have hsound : ∀ x ∉ (∅ : Set (List Bool)), ∀ π : List Bool,
      2 * acceptCount (fun y => alwaysRejectVerifier.accepts y.1 π y.2) x
        (alwaysRejectVerifier.coins x) ≤ 2 ^ alwaysRejectVerifier.coins x := by
    intro x _ π
    rw [acceptCount_le_half_iff]
    have hfalse : ∀ word, alwaysRejectVerifier.accepts x π word = false := by
      intro word
      simp [alwaysRejectVerifier, PCPVerifier.accepts]
    simp [hfalse]
  have hMT : OracleComp.IsCostBounded micaliMTCost toyCheatingProver 0 :=
    OracleComp.IsCostBounded.pure _ 0
  have hFS : OracleComp.IsCostBounded micaliFSCost toyCheatingProver 0 :=
    OracleComp.IsCostBounded.pure _ 0
  have hdepth : ∀ x rawProof, (x, rawProof) ∈ toyCheatingProver.support →
      m * 1 * (kilianDepth alwaysRejectVerifier x + 1) ≤
        m * 1 * (kilianDepth alwaysRejectVerifier [] + 1) := by
    intro x rawProof hmem
    have hx := OracleComp.eq_of_mem_supportWith_pure hmem
    obtain ⟨rfl, -⟩ := Prod.mk.inj hx
    rfl
  simpa using micaliRawSoundness_bound alwaysRejectVerifier (∅ : Set (List Bool)) σ m 1
    hsound (fun _ _ _ => by simp [alwaysRejectVerifier]) hMT hFS hdepth

-- Full NP raw-byte Micali CS proof instantiated on `headTrueRel`.
example :
    ∃ (V : PCPVerifier (List Bool)) (compile : List Bool × List Bool → List Bool)
      (c d : ℕ) (tWordBound : ℕ → ℕ),
      V.PolyTime encBits ∧
      ComputableInPolyTime compile (encPair encBits encBits) encBits ∧
      (∀ σ m, micaliHonestRawGame V [true] (compile ([true], [true])) σ m = PMF.pure true) ∧
      PolynomiallyBounded tWordBound ∧
      ComputesOracleInTimeAndQueriesOn (encPair (encMicaliRawInput encBits) encBits) encBool
        (fun p => tWordBound (p.1.sigma + p.1.reps + (encBits p.1.stmt).length))
        (fun p => 1 + p.1.reps * d * (kilianDepth V p.1.stmt + 1))
        (micaliVerifyRawWord V encBits c d) ∧
      (∀ (σ m : ℕ) (P : OracleComp (MicaliSpec (List Bool)) (List Bool × List Bool))
        (t_MT t_FS q_V : ℕ),
        OracleComp.IsCostBounded micaliMTCost P t_MT →
        OracleComp.IsCostBounded micaliFSCost P t_FS →
        (∀ x rawProof, (x, rawProof) ∈ P.support → m * d * (kilianDepth V x + 1) ≤ q_V) →
        micaliRawSoundnessGame V headTrueRel.language P σ m true ≤
          ((t_FS + 1 : ℕ) : ℝ≥0∞) * (1 / 2) ^ m +
            ((t_MT + q_V : ℕ) : ℝ≥0∞) *
              (((3 * (t_MT + q_V) + (t_FS + 1) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ))) ∧
      ∃ C : ℕ,
        micaliProofBits
          (micaliProvePure constTree (fun _ => [List.replicate (V.coins [true]) false])
            V [true] (compile ([true], [true]))) ≤
          C * (2 + 1 + 1) ^ 2 * (Nat.log 2 (encBits ([true] : List Bool)).length + 1) := by
  obtain ⟨V, compile, c, d, tWordBound, hV, _, _, hcompile, _, _, hhonest, ht_pb, hword,
    hsound, C, hlen⟩ := exists_micaliRawCSProof_of_npRelation headTrueRel
  refine ⟨V, compile, c, d, tWordBound, hV, hcompile, hhonest [true] [true] headTrueRel_witness,
    ht_pb, hword, fun σ m P t_MT t_FS q_V hMT hFS hd => hsound P t_MT t_FS q_V σ m hMT hFS hd,
    C, hlen 2 1 constTree (fun _ => [List.replicate (V.coins [true]) false]) [true]
      (compile ([true], [true])) length_constTree rfl (by simp)⟩

end CslibFrontierTests.Crypto.MicaliRaw
