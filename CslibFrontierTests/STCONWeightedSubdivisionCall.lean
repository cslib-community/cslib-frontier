/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenBoundedWalk
import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenWeightedSubdivision.Replay
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

-- After a read and selector, a caller can inspect the next query, completion, and reply.
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) :
    let M := (justesenWeightedSubdivisionCallback ntm).withRejectingChoice
    let enc := encOption encJustesenSubdivisionState
    let encNext := encPair enc NondeterministicQueryMachine.encReadChoice
    ComputableInSpace (M.query ∘ M.next) encNext encNat (fun p => (encNext p).length) ∧
    ComputableInSpace (M.halted ∘ M.next) encNext encBool (fun p => (encNext p).length) ∧
    ComputableInSpace (fun p => (M.next p).map callbackVerdict) encNext (encOption encBool)
      (fun p => (encNext p).length) := by
  obtain ⟨hq, hn, hh, hv⟩ := justesenWeightedSubdivisionChoice_parts_inSpace ntm
  have hquery := budget_comp_linear hq hn
  have hhalt := budget_comp_linear hh hn
  have hreply := budget_comp_linear hv hn
  exact ⟨hquery, hhalt, hreply⟩

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

open Turing.DoubleCounting.BoundedWalk in
-- A caller can take a state-changing step and inspect the resumed state in the same budget.
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) (rank : ℕ)
    (r : Registers
      (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount) :
    let M := configurationJustesenBoundedWalk ntm c w rank r
    let enc := Runtime.encStep encJustesenSubdivisionContext encJustesenSubdivisionState
    ComputableInSpace (M.query ∘ M.next) enc encNat (fun p => (enc p).length) ∧
    ComputableInSpace (M.halted ∘ M.next) enc encBool (fun p => (enc p).length) ∧
    ComputableInSpace (Runtime.remainingFuel ∘ M.next) enc (encOption encNat)
      (fun p => (enc p).length) := by
  obtain ⟨hq, hn, hh, hf⟩ := configurationJustesenBoundedWalk_parts_inSpace ntm c w rank r
  have hquery := budget_comp_linear hq hn
  have hhalted := budget_comp_linear hh hn
  have hfuel := budget_comp_linear hf hn
  exact ⟨hquery, hhalted, hfuel⟩

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
        (∀ t ≤ 3, (encJustesenSubdivisionState (M.runFrom w start t)).length ≤
          C * (Nat.log2 w.length + 1)) ∧
        (∀ bits, M.withRejectingChoice.FirstHalting w bits (some start) ∧
          (M.withRejectingChoice.replay w bits (some start)).isSome ↔
            bits = [false, false, false]) := by
  obtain ⟨C, hC⟩ := configurationJustesenSubdivisionEdge_contract ntm c
  refine ⟨C, fun w => ?_⟩
  intro I s size index seed ctx u v M start
  obtain ⟨hbefore, hhalt, hadj, hspace⟩ := hC w seed u v
  exact ⟨hbefore, hhalt, hadj, hspace,
    configurationJustesenSubdivisionEdge_firstHalting_iff ntm c w seed u v⟩

example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    PolyBounded List.length (configurationJustesenBoundedWalkClock ntm c) :=
  configurationJustesenBoundedWalkClock_polyBounded ntm c

open Cslib.DoubleCounting.Scan Turing.DoubleCounting.BoundedWalk in
-- Check zero-edge success, the shared polynomial clock, and a wrong return selector.
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let setup := configurationSeedSearchSetup ntm c w
      let size := setup.parameters.search.subdivision
      let seed : Fin (2 ^ codeLength I.n (I.n - 1)) := ⟨0, Nat.pow_pos (by decide)⟩
      let source : Fin size.vertexCount :=
        ⟨setup.sourceID, (configurationSeedSearchSetup_endpoints_lt_vertexCount ntm c w).1⟩
      let r : Registers size.vertexCount := ⟨source, source, 0⟩
      let M := configurationJustesenBoundedWalk ntm c w seed.val r
      let bits := selectors (N := size.vertexCount) 3 []
      M.FirstHalting w bits M.init ∧ Runtime.remainingFuel (M.run w bits) = some 0 ∧
        M.HaltsWithin w (size.vertexCount.size + 2) ∧
        M.HaltsWithin w (configurationJustesenBoundedWalkClock ntm c w) ∧
        (Runtime.encState encJustesenSubdivisionContext encJustesenSubdivisionState
          (M.run w [false, true])).length ≤ C * (Nat.log2 w.length + 1) := by
  obtain ⟨C, hC⟩ := configurationJustesenBoundedWalk_bounds ntm c
  refine ⟨C, fun w => ?_⟩
  intro I setup size seed source r M bits
  have hfuel : r.fuel ≤ size.vertexCount := Nat.zero_le _
  obtain ⟨hclock, hstates⟩ := hC w seed r hfuel
  have hrun := (configurationJustesenBoundedWalk_firstHalting_iff ntm c w seed r bits 0).mpr
    ⟨[], rfl, by simp [r, walkM, readNext, bind, StateT.bind, pure, StateT.pure]⟩
  refine ⟨hrun.1, hrun.2, ?_,
    configurationJustesenBoundedWalk_haltsWithin_clock ntm c w seed.val r hfuel,
    hstates [false, true]⟩
  simpa only [r, Nat.zero_mul, Nat.zero_add] using hclock

open Turing.DoubleCounting.BoundedWalk in
-- The binary rank is supplied by a logspace caller. The zero registers are valid at every size.
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    {rank : List Bool → ℕ} (hrank : ComputableInLogSpace rank encBits encNat)
    (hvalid : ∀ w, rank w < (configurationSeedSearchParameters ntm c w).search.seedLimit) :
    let dimension (w : List Bool) :=
      (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
    let registers (w : List Bool) : Registers (dimension w) :=
      let zero : Fin (dimension w) := ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _)
        (configurationSeedSearchSetup_endpoints_lt_vertexCount ntm c w).1⟩
      ⟨zero, zero, 0⟩
    ComputableInSpace (fun w => (configurationJustesenBoundedWalk ntm c w (rank w)
      (registers w)).init) encBits
      (Runtime.encState encJustesenSubdivisionContext encJustesenSubdivisionState)
      (fun w => Nat.log2 w.length) := by
  intro dimension registers
  have hz : ComputableInSpace (fun _ : List Bool => 0) encBits encNat
      (fun w => Nat.log2 w.length) :=
    (constZero 0).mono_le fun _ => Nat.zero_le _
  exact configurationJustesenBoundedWalk_init_inSpace ntm c
    (r := registers) hrank hvalid hz hz hz

end CslibFrontierTests.STCONWeightedSubdivisionCall
