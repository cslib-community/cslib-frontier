/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Problems.STCON.WeightedSubdivisionSpace

/-! Ordinary-import clients for weighted STCON adjacency and the flat scan interface. -/

set_option linter.privateModule false

namespace CslibFrontierTests.STCONWeightedSubdivisionCall

open Cslib Cslib.Code.JustesenFamily Cslib.Complexity.STCON Cslib.LayeredDigraph.Subdivision
open Cslib.Reachability.Hoza Turing Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace
open Turing.QueryMachine.Subdivision

private abbrev Context := LayeredParameters × ℕ

private def code : Context × ℕ → ℕ → Bool := fun _ _ => false

-- Both flat entry and weighted return use the same encoded call state. This component
-- fixture uses a one-bit seed width and a constant code-bit routine.
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) :
    let encCtx := encPair encLayeredParameters encNat
    let encFlat := encFlatQuery encCtx
    let enc := encCallback encCtx encLayeredCallback
    let M := weightedSubdivisionCallback ntm Prod.fst Prod.snd (fun _ => 1) code
    ComputableInSpace flatCallbackStart encFlat enc (fun q => (encFlat q).length) ∧
    ComputableInSpace M.next (QueryMachine.encStateRead enc) enc
      (fun p => (QueryMachine.encStateRead enc p).length) := by
  let : Inhabited LayeredParameters := ⟨⟨0, 0, 0, 0⟩⟩
  let encCtx := encPair encLayeredParameters encNat
  exact ⟨flatCallbackStart_inSpace _ _,
    (weightedSubdivisionCallback_parts_inSpace ntm encCtx Prod.fst Prod.snd (fun _ => 1) code
      (fst encLayeredParameters encNat) (snd encLayeredParameters encNat)
      (budget_const 1 (.refl _)) (BigOLe.const 1 _) (budget_const false (.refl _))).2.1⟩

-- Use the generated subdivision's adjacency specification at the original roots,
-- with the code-bit correspondence supplied at the source column.
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) (bound : ℕ)
    (seed : Fin (2 ^ codeLength (configurationInstance ntm c w).n
      ((configurationInstance ntm c w).n - 1)))
    (bits : Context × ℕ → ℕ → Bool)
    (hbits : let I := configurationInstance ntm c w
      let col := (layeredCoordinates I (layeredStart I)).2
      ∀ i : Fin (codeLength I.n (I.n - 1)),
        bits ((layeredParameters ntm c w.length, seed.val), col.val) i.val =
          indexedCodewordMod col i) :
    let I := configurationInstance ntm c w
    let ctx := (layeredParameters ntm c w.length, seed.val)
    let a := root bound (layeredCoordinates I (layeredStart I))
    let b := root bound (layeredCoordinates I (layeredTarget I))
    let M := weightedSubdivisionCallback ntm Prod.fst Prod.snd
      (fun _ => codeLength I.n (I.n - 1)) bits
    let (s, t) := subdivisionEndpointIDs (ctx.1, bound)
    let G := graph (layeredDigraph I) (generatedWeight ((BitString.equivFin _).symm seed)) bound
    let start := flatCallbackStart ⟨ctx, bound, s, t⟩
    (∀ i < 3, M.halted (M.runFrom w start i) = false) ∧
    ∃ answer, M.runFrom w start 3 = .inl (.inr answer) ∧
      M.halted (M.runFrom w start 3) = true ∧
      (answer = true ↔ G.Adj a b) := by
  dsimp only
  rw [subdivisionEndpointIDs_eq]
  obtain ⟨hbefore, answer, hrun, hhalt, hedge⟩ :=
    weightedSubdivisionCallback_agrees ntm c w
      (layeredParameters ntm c w.length, seed.val) Prod.fst Prod.snd
      (fun _ => codeLength (configurationInstance ntm c w).n
        ((configurationInstance ntm c w).n - 1)) bits rfl
      (root bound (layeredCoordinates _ (layeredStart _)))
      (root bound (layeredCoordinates _ (layeredTarget _))) seed rfl rfl hbits
  exact ⟨hbefore, answer, hrun, hhalt, hedge⟩

-- At the same valid scan IDs, obtain the three-step edge verdict and charge the
-- initialized setup as context for the logarithmic bound on every live state.
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (bits : SeedSearchSetup × ℕ → ℕ → Bool) :
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let s := configurationSeedSearchSetup ntm c w
      let size := s.parameters.search.subdivision
      let index := configurationSubdivisionIndex ntm c w
      let seed : Fin (2 ^ codeLength I.n (I.n - 1)) := ⟨0, Nat.pow_pos (by decide)⟩
      ∀ u v : Fin size.vertexCount,
        (∀ i : Fin (codeLength I.n (I.n - 1)),
          bits (s, (index.symm u).vertex.2.val) i.val =
            indexedCodewordMod (index.symm u).vertex.2 i) →
        let q : FlatQuery SeedSearchSetup := ⟨s, size.chainBound, u.val, v.val⟩
        let M := weightedSubdivisionCallback ntm (fun s => s.parameters.graph)
          (fun _ => 0) (fun s => s.parameters.search.seedWidth) bits
        let G := graph (layeredDigraph I) (generatedWeight ((BitString.equivFin _).symm seed))
          size.chainBound
        (∀ t < 3, M.halted (M.runFrom w (flatCallbackStart q) t) = false) ∧
          (∃ answer, M.runFrom w (flatCallbackStart q) 3 = .inl (.inr answer) ∧
            M.halted (M.runFrom w (flatCallbackStart q) 3) = true ∧
            (answer = true ↔ G.Adj (index.symm u) (index.symm v))) ∧
          ∀ t ≤ 3, (encCallback encSeedSearchSetup encLayeredCallback
            (M.runFrom w (flatCallbackStart q) t)).length ≤ C * (Nat.log2 w.length + 1) := by
  obtain ⟨K, hK⟩ := length_configurationSeedSearchSetup_le_log ntm c
  obtain ⟨R, hR⟩ := configurationWeightedSubdivisionCallback_states_le ntm c encSeedSearchSetup
    (fun s => s.parameters.graph) (fun _ => 0) (fun s => s.parameters.search.seedWidth) bits
  refine ⟨R * (K + 1), fun w u v hbits => ?_⟩
  let s := configurationSeedSearchSetup ntm c w
  have hparams := (configurationSeedSearchSetup_endpoints ntm c w).1
  change s.parameters = _ at hparams
  have hgraph : s.parameters.graph = layeredParameters ntm c w.length := by
    rw [hparams]
    rfl
  let I := configurationInstance ntm c w
  have hwidth : s.parameters.search.seedWidth = codeLength I.n (I.n - 1) := by
    rw [hparams]
    rfl
  obtain ⟨hbefore, hreturn⟩ := configurationWeightedSubdivisionCallback_agrees ntm c w s
    (fun s => s.parameters.graph) (fun _ => 0) (fun s => s.parameters.search.seedWidth) bits
    hgraph u v ⟨0, Nat.pow_pos (by decide)⟩ rfl hwidth hbits
  refine ⟨hbefore, hreturn, fun t ht => ?_⟩
  refine (hR w s hgraph u.val v.val u.isLt v.isLt t ht).trans ?_
  rw [Nat.mul_assoc, Nat.add_mul, Nat.one_mul]
  exact Nat.mul_le_mul_left R (Nat.add_le_add_right (hK w) _)

end CslibFrontierTests.STCONWeightedSubdivisionCall
