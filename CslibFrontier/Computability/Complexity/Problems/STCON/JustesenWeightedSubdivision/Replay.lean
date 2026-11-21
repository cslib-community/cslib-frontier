/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenWeightedSubdivision
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.DeterministicCall

/-!
# Selector replay for Justesen-weighted adjacency

At valid seed and endpoint IDs, the initialized adjacency query takes three deterministic
steps. The binary-choice adapter has one successful first-halting selector list for it.
-/

public section

namespace Cslib.Complexity.STCON

open Cslib.Code.JustesenFamily Cslib.Reachability.Hoza
open _root_.Turing _root_.Turing.MultiTapeNTM.ConfigurationGraph

variable {k : ℕ} {State : Type} [Fintype State]

/-- At valid initialized ranks and endpoints, the weighted edge callback has one successful
first-halting selector list. That list takes all three deterministic steps on the original word. -/
theorem configurationJustesenSubdivisionEdge_firstHalting_iff
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (u v : Fin size.vertexCount)
      (bits : List Bool),
      let ctx := configurationJustesenSubdivisionContext ntm c w seed.val
      let entry := some (justesenSubdivisionEdgeStart (ctx, u.val, v.val))
      let M := (justesenWeightedSubdivisionCallback ntm).withRejectingChoice
      M.FirstHalting w bits entry ∧ (M.replay w bits entry).isSome ↔ bits = [false, false, false] :=
  fun seed u v bits => by
    obtain ⟨_, hcall⟩ := configurationJustesenSubdivisionEdge_contract ntm c
    obtain ⟨hbefore, hhalt, _, _⟩ := hcall w seed u v
    exact (justesenWeightedSubdivisionCallback ntm).withRejectingChoice_firstHalting_iff
      w _ 3 hbefore hhalt bits

end Cslib.Complexity.STCON
