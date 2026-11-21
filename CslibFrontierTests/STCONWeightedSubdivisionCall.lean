/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenWeightedSubdivision
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words

/-! Ordinary-import clients for weighted STCON adjacency and the flat scan interface. -/

set_option linter.privateModule false

namespace CslibFrontierTests.STCONWeightedSubdivisionCall

open Cslib Cslib.Code.JustesenFamily Cslib.Complexity.STCON Cslib.LayeredDigraph.Subdivision
open Cslib.Reachability.Hoza Turing Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace
open Turing.QueryMachine.Subdivision

private abbrev Context := LayeredParameters × ℕ

-- Both flat entry and weighted return use the same state encoding, with the actual Justesen
-- evaluator inside the return transition.
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) :
    let encFlat := encFlatQuery encJustesenSubdivisionContext
    let enc := encCallback encJustesenSubdivisionContext encLayeredCallback
    let M := justesenWeightedSubdivisionCallback ntm
    ComputableInSpace flatCallbackStart encFlat enc (fun q => (encFlat q).length) ∧
    ComputableInSpace M.next (QueryMachine.encStateRead enc) enc
      (fun p => (QueryMachine.encStateRead enc p).length) :=
  ⟨flatCallbackStart_inSpace _ _, (justesenWeightedSubdivisionCallback_parts_inSpace ntm).2.1⟩

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

-- The native initializer reads a framed binary rank followed by the original word.
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ComputableInLogSpace
      (fun p : ℕ × List Bool => configurationJustesenSubdivisionContext ntm c p.2 p.1)
      (encPair encNat encBits) encJustesenSubdivisionContext :=
  configurationJustesenSubdivisionContext_inLogSpace ntm c
    (ComputableInLogSpace.snd encNat encBits) (ComputableInLogSpace.fst encNat encBits)

-- A suspended caller can enter the same machine with new binary IDs and decode its reply.
example :
    let enc := encPair encJustesenSubdivisionContext (encPair encNat encNat)
    ComputableInSpace justesenSubdivisionEdgeStart enc encJustesenSubdivisionState
      (fun p => (enc p).length) ∧
    ComputableInSpace callbackVerdict encJustesenSubdivisionState encBool
      (fun s => (encJustesenSubdivisionState s).length) :=
  ⟨justesenSubdivisionEdgeStart_inSpace, callbackVerdict_inSpace _ _⟩

-- At the designated endpoints the decoded bit and every prefix fit the same call contract.
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let s := configurationSeedSearchSetup ntm c w
      let size := s.parameters.search.subdivision
      let index := configurationSubdivisionIndex ntm c w
      let seed : Fin (2 ^ codeLength I.n (I.n - 1)) := ⟨0, Nat.pow_pos (by decide)⟩
      let ctx := configurationJustesenSubdivisionContext ntm c w seed.val
      let u : Fin size.vertexCount :=
        ⟨s.sourceID, (configurationSeedSearchSetup_endpoints_lt_vertexCount ntm c w).1⟩
      let v : Fin size.vertexCount :=
        ⟨s.targetID, (configurationSeedSearchSetup_endpoints_lt_vertexCount ntm c w).2⟩
      let M := justesenWeightedSubdivisionCallback ntm
      let start := justesenSubdivisionEdgeStart (ctx, u.val, v.val)
      (∀ t < 3, M.halted (M.runFrom w start t) = false) ∧
        M.halted (M.runFrom w start 3) = true ∧
        (callbackVerdict (M.runFrom w start 3) = true ↔
          (graph (layeredDigraph I)
            (generatedWeight ((BitString.equivFin _).symm seed)) size.chainBound).Adj
              (index.symm u) (index.symm v)) ∧
        ∀ t ≤ 3, (encJustesenSubdivisionState (M.runFrom w start t)).length ≤
          C * (Nat.log2 w.length + 1) := by
  obtain ⟨C, hC⟩ := configurationJustesenSubdivisionEdge_contract ntm c
  refine ⟨C, fun w => ?_⟩
  intro I s size index seed ctx u v M start
  exact hC w seed u v

end CslibFrontierTests.STCONWeightedSubdivisionCall
