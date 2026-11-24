/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.Crypto.Computational.Kilian.NP
import CslibFrontier.Crypto.Computational.Kilian.MicaliSoundness
import CslibFrontier.Computability.Complexity.Problems.SAT.Relation
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Tests for NP witness-compiled Kilian arguments and machine verifier accounting

Non-vacuous checked clients for:
* `computableInTimeAndSpace_kilianVerify_honest_le`: single-machine polynomial runtime and space in
  `n + |enc x|` on honest transcripts;
* `computableInTimeAndSpace_kilianVerify_of_isPPT`: single-machine polynomial runtime and space in
  `n` against an explicit strict PPT prover;
* `exists_kilianArgument_of_npRelation` and `exists_micaliCSProof_of_npRelation`: non-vacuous
  instantiations on a concrete binary NP relation with distinct member and non-member witnesses,
  and on `SAT.npRelation`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.KilianNP

open Cslib Cslib.Complexity Cslib.Crypto Cslib.Logic.PL Cslib.Probability
open Turing.MultiTapeTM

/-- Key-returning hash used solely to exercise the deterministic verifier runtime bounds. -/
def constHash (k _ : List Bool) : List Bool := k

theorem length_constHash (k x : List Bool) : (constHash k x).length = k.length := rfl

theorem polyTime_constHash :
    ComputableInPolyTime (fun p : List Bool × List Bool => constHash p.1 p.2)
      (encPair encBits encBits) encBits :=
  ComputableInPolyTime.fst encBits encBits

/-- A one-coin, one-query PCP verifier matching `KilianSuccinct.toyVerifier`. -/
def toyVerifier : PCPVerifier (List Bool) where
  coins _ := 1
  queries := fun (_, ρ) => [if ρ.headD false then 5 else 1000]
  verdict := fun (_, answers) => answers == [true]

theorem polyTime_toyVerifier : toyVerifier.PolyTime encBits where
  coins := by unfold toyVerifier; fun_prop
  queries := by unfold toyVerifier; fun_prop
  verdict := by unfold toyVerifier; fun_prop

-- Concrete instantiation of `computableInTimeAndSpace_kilianVerify_honest_le` evaluated at an
-- accepted honest transcript (`[true, false]`, key `[false, true]`, witness table `[true, true]`).
example :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State)
      (tHonest sHonest : ℕ → ℕ),
      PolynomiallyBounded tHonest ∧ PolynomiallyBounded sHonest ∧
      let key : List Bool := [false, true]
      let x : List Bool := [true, false]
      let ρs : List (List Bool) := [[false], [true]]
      let view : KilianView (List Bool) :=
        { key := key, stmt := x, root := kilianCommit constHash toyVerifier key x [true, true],
          challenges := ρs,
          response := kilianRespond constHash toyVerifier key x [true, true] ρs }
      tm.ComputesInTimeAndSpace (encKilianView encBits view) (encBool true)
        (tHonest (2 + (encBits x).length)) (sHonest (2 + (encBits x).length)) := by
  obtain ⟨k, State, hfin, tm, t, s, tHonest, sHonest, _, _, htH, hsH, _, hrun⟩ :=
    computableInTimeAndSpace_kilianVerify_honest_le (H := constHash) (V := toyVerifier)
      polyTime_constHash length_constHash polyTime_toyVerifier
      (c := 1) (q := 1) (fun _ => by simp [toyVerifier]) (fun _ _ _ => by simp [toyVerifier])
  have hvis := hrun 2 [false, true] [true, false] [true, true] [[false], [true]]
    rfl rfl (by decide)
  have hacc :
      kilianVerify constHash toyVerifier [false, true] [true, false]
        (kilianCommit constHash toyVerifier [false, true] [true, false] [true, true])
        [[false], [true]]
        (kilianRespond constHash toyVerifier [false, true] [true, false] [true, true]
          [[false], [true]]) = true := by
    decide
  refine ⟨k, State, hfin, tm, tHonest, sHonest, htH, hsH, ?_⟩
  simpa only [hacc] using hvis.2.2

/-- A strict PPT prover matching `KilianSoundness.constantProver`. -/
def constantProver : KilianProver (List Bool) where
  commit _ k := pure { stmt := [true, false], root := k, state := [] }
  answer _ _ ρs := pure (ρs.map fun _ => [])

theorem isPPT_constantProver : constantProver.IsPPT encBits where
  commit := by unfold constantProver; ppt
  answer := by unfold constantProver; ppt

-- Concrete instantiation of `computableInTimeAndSpace_kilianVerify_of_isPPT` on `constantProver`.
example :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State)
      (tAdv sAdv : ℕ → ℕ),
      PolynomiallyBounded tAdv ∧ PolynomiallyBounded sAdv ∧
      ∀ (n : ℕ) (key : List Bool), key.length = n →
        ∀ cm ∈ (ProbComp.eval (constantProver.commit n key)).support,
          ∀ ρs ∈ (ProbComp.eval (kilianChallenges toyVerifier n cm.stmt)).support,
            ∀ resp ∈ (ProbComp.eval (constantProver.answer n cm.state ρs)).support,
              let view : KilianView (List Bool) :=
                { key := key, stmt := cm.stmt, root := cm.root,
                  challenges := ρs, response := resp }
              tm.ComputesInTimeAndSpace (encKilianView encBits view)
                (encBool (kilianVerify constHash toyVerifier key cm.stmt cm.root ρs resp))
                (tAdv n) (sAdv n) := by
  obtain ⟨k, State, hfin, tm, tAdv, sAdv, ht, hs, hrun⟩ :=
    computableInTimeAndSpace_kilianVerify_of_isPPT (H := constHash) (V := toyVerifier)
      polyTime_constHash length_constHash polyTime_toyVerifier
      (c := 1) (fun _ => by simp [toyVerifier]) isPPT_constantProver
  exact ⟨k, State, hfin, tm, tAdv, sAdv, ht, hs, hrun⟩

/-- Non-trivial concrete NP relation: words starting with `true`, certificate `[true]`. -/
noncomputable def headTrueRel : NPRelation encBits where
  certLength := 1
  verifier := fun (x, w) => x.headD false && w.headD false
  computableInPolyTime_verifier := by fun_prop

theorem headTrueRel_witness : headTrueRel.IsWitness [true] [true] := by
  simp [headTrueRel, NPRelation.IsWitness]

theorem headTrueRel_not_mem_false : [false] ∉ headTrueRel.language := by
  rintro ⟨w, _, hver⟩
  simp [headTrueRel] at hver

-- Non-vacuous `exists_kilianArgument_of_npRelation` client for any collision-resistant hash family.
example {H : List Bool → List Bool → List Bool} (hH : HashFamily H) :
    ∃ (V : PCPVerifier (List Bool)) (compile : List Bool × List Bool → List Bool),
      V.PolyTime encBits ∧
      ComputableInPolyTime compile (encPair encBits encBits) encBits ∧
      ComputableInPolyTime
        (fun p : List Bool × List Bool × List Bool =>
          let (key, state) := p
          let (x, w) := state
          kilianCommit H V key x (compile (x, w)))
        (encPair encBits (encPair encBits encBits)) encBits ∧
      (∀ n, ProbComp.eval (kilianHonestGame H V [true] (compile ([true], [true])) n) =
        PMF.pure true) ∧
      KilianSound H V encBits headTrueRel.language ∧
      (∀ table, V.tableVerifier ([false], table) = false) ∧
      (∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State)
        (tHonest sHonest : ℕ → ℕ),
        PolynomiallyBounded tHonest ∧ PolynomiallyBounded sHonest ∧
        ∀ (n : ℕ) (key : List Bool) (ρs : List (List Bool)),
          key.length = n → ρs.length = n → (∀ ρ ∈ ρs, ρ.length = V.coins [true]) →
            let view : KilianView (List Bool) :=
              { key := key, stmt := [true],
                root := kilianCommit H V key [true] (compile ([true], [true])),
                challenges := ρs,
                response := kilianRespond H V key [true] (compile ([true], [true])) ρs }
            tm.ComputesInTimeAndSpace (encKilianView encBits view) (encBool true)
              (tHonest (n + (encBits [true]).length)) (sHonest (n + (encBits [true]).length))) := by
  obtain ⟨V, compile, _, _, hV, _, _, hcompile, hcommit, -, hmem, hacc, hcomplete, hsound, -,
    k, State, hfin, tm, t, s, tHonest, sHonest, _, _, htH, hsH, _, hverify⟩ :=
    exists_kilianArgument_of_npRelation hH headTrueRel
  refine ⟨V, compile, hV, hcompile, hcommit, hcomplete [true] [true] headTrueRel_witness, hsound,
    fun table => ?_, k, State, hfin, tm, tHonest, sHonest, htH, hsH,
    fun n key ρs hk hn hρs => ?_⟩
  · by_contra htrue
    exact headTrueRel_not_mem_false ((hmem [false]).mpr ⟨table, by simpa using htrue⟩)
  · have hrun := hverify n key [true] (compile ([true], [true])) ρs hk hn hρs
    have hok :
        kilianVerify H V key [true] (kilianCommit H V key [true] (compile ([true], [true])))
          ρs (kilianRespond H V key [true] (compile ([true], [true])) ρs) = true :=
      kilianVerify_kilianRespond (hacc [true] [true] headTrueRel_witness) key (hH.length_eq key) hρs
    simpa only [hok] using hrun.2.2

-- Non-vacuous `exists_micaliCSProof_of_npRelation` client on `headTrueRel` and `SAT.npRelation`.
example :
    ∃ (V : PCPVerifier (List Bool)) (compile : List Bool × List Bool → List Bool),
      V.PolyTime encBits ∧
      ComputableInPolyTime compile (encPair encBits encBits) encBits ∧
      (∀ σ m, micaliHonestGame V [true] (compile ([true], [true])) σ m = PMF.pure true) ∧
      (∀ table, V.tableVerifier ([false], table) = false) := by
  obtain ⟨V, compile, _, _, hV, _, _, hcompile, hmem, _, hcomplete, -, -⟩ :=
    exists_micaliCSProof_of_npRelation headTrueRel
  refine ⟨V, compile, hV, hcompile, hcomplete [true] [true] headTrueRel_witness, fun table => ?_⟩
  by_contra htrue
  exact headTrueRel_not_mem_false ((hmem [false]).mpr ⟨table, by simpa using htrue⟩)

example (φ : CNF ℕ) (w : List Bool) (hw : SAT.npRelation.IsWitness φ w) :
    ∃ (V : PCPVerifier (CNF ℕ)) (compile : CNF ℕ × List Bool → List Bool),
      V.tableVerifier (φ, compile (φ, w)) = true ∧
      ∀ σ m, micaliHonestGame V φ (compile (φ, w)) σ m = PMF.pure true := by
  obtain ⟨V, compile, _, _, _, _, _, _, _, hacc, hcomplete, -, -⟩ :=
    exists_micaliCSProof_of_npRelation SAT.npRelation
  exact ⟨V, compile, hacc φ w hw, hcomplete φ w hw⟩

end CslibFrontierTests.Crypto.KilianNP
