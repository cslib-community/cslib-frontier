/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Algorithms.Reachability.DoubleCounting.ControllerBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-! # Ordinary-import scalar-prefix clients, including incorrect and rejecting replies -/
namespace CslibFrontierTests.DoubleCountingControllerBounds
open Cslib.DoubleCounting

deriving instance DecidableEq for Tally
deriving instance DecidableEq for RoundUpdate

private def member (_ : ℕ) (_ : Tally) (v : Fin 3) : List Bool := [v != 0]
private def oneEdge (u v : Fin 3) : List Bool := [u == 1 && v == 0]
private def allEdges (_ _ : Fin 3) : List Bool := [true]
private def first (j : ℕ) (h : j ≤ 3) (i : Fin j) : Fin 3 := ⟨i, i.isLt.trans_le h⟩

-- Two qualifying predecessors still add the vertex once, while setting the tie flag.
example : (⟨⟨2, 1⟩, true⟩ : RoundUpdate) ∈
    Fin.foldlM 1 (fun a i => scanVertex allEdges (member 0 ⟨1, 0⟩) 0 a (first 1 (by omega) i))
      ⟨⟨1, 0⟩, false⟩ := by decide +kernel

example : ∀ a ∈ Fin.foldlM 1
    (fun a i => scanVertex allEdges (member 0 ⟨1, 0⟩) 0 a (first 1 (by omega) i))
      ⟨⟨1, 0⟩, false⟩, a.tally.count ≤ 2 ∧ a.tally.lengthSum ≤ 1 := by
  intro a ha
  exact scanVertex_prefix_bounds _ _ _ _ _ _ ha

-- Both terminal branches use the original controller, including a successful false answer.
example : runController allEdges member 2 = [some (.bad 1)] := by decide +kernel
example : runController (fun _ _ : Fin 3 => [false]) (fun _ _ v => [v == 0]) 2 =
    [some (.decided false)] := by decide +kernel

-- A completed prefix retains its bounds although vertex 2 later rejects the round.
private def rejecting (_ : ℕ) (_ : Tally) (v : Fin 3) : List Bool :=
  if v = 2 then [] else [v != 0]

example : scanNextRound oneEdge rejecting 0 ⟨1, 0⟩ = [] := by decide +kernel
example : (⟨⟨2, 1⟩, false⟩ : RoundUpdate) ∈ Fin.foldlM 2
    (fun a i => scanVertex oneEdge (rejecting 0 ⟨1, 0⟩) 0 a (first 2 (by omega) i))
      ⟨⟨1, 0⟩, false⟩ := by decide +kernel

-- The two-member predecessor prefix is bounded even though the third member rejects.
example : 1 ∈ Fin.foldlM 2
    (fun c i => predecessorStep allEdges (rejecting 0 ⟨1, 0⟩) 0 c
      (first 2 (by omega) i)) 0 := by decide +kernel
example : countPredecessors allEdges (rejecting 0 ⟨1, 0⟩) 0 = [] := by decide +kernel
example (c : ℕ) (hc : c ∈ Fin.foldlM 2
    (fun c i => predecessorStep allEdges (rejecting 0 ⟨1, 0⟩) 0 c
      (first 2 (by omega) i)) 0) : c ≤ 2 := by
  exact predecessor_prefix_le _ _ _ _ _ _ hc

private theorem secondCall : RoundCall oneEdge member 1 2 ⟨3, 3⟩ := by
  apply RoundCall.next (a := ⟨⟨3, 3⟩, false⟩)
  · apply RoundCall.next (a := ⟨⟨2, 1⟩, false⟩) RoundCall.initial
    · decide +kernel
    · rfl
    · decide
  · decide +kernel
  · rfl
  · decide

-- Incorrect but Boolean replies can keep adding the same vertex until fuel exhaustion.
example : none ∈ runController oneEdge member 2 :=
  secondCall.result_mem 2 (by decide +kernel)

-- The caller no longer reconstructs the radius and register arithmetic. Binary lengths
-- follow directly from the scalar bound using the existing encoding theorem.
example {n fuel k j : ℕ} {edge : Fin n → Fin n → List Bool}
    {callback : MembershipScan List n} {t : Tally} (h : RoundCall edge callback fuel k t)
    (hactive : 0 < fuel) (hj : j ≤ n) (index : Fin j → Fin n) (a : RoundUpdate)
    (ha : a ∈ Fin.foldlM j (fun a i => scanVertex edge (callback k t) k a (index i))
      ⟨t, false⟩) :
    k < n ∧ (Turing.MultiTapeTM.encNat a.tally.count).length ≤ Nat.log2 (1 + n * n) + 1 ∧
      (Turing.MultiTapeTM.encNat a.tally.lengthSum).length ≤ Nat.log2 (n * n * n) + 1 := by
  obtain ⟨hk, _, hc, hs⟩ := h.prefix_bounds hactive hj index a ha
  exact ⟨hk, Turing.MultiTapeTM.length_encNat_le_log2 hc,
    Turing.MultiTapeTM.length_encNat_le_log2 hs⟩

end CslibFrontierTests.DoubleCountingControllerBounds
