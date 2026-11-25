/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Dijkstra.Native.Fibonacci.Memory
import CslibFrontier.Algorithms.Dijkstra.Invariant
import CslibFrontier.Algorithms.WordRAM.Dijkstra.ListEncode

/-!
# Amortized memory cost of the Fibonacci Dijkstra source

The existing framed potential pays for the actual memory histories, and the existing Dijkstra
operation counts retain the reachable-vertex bound. Dirty initialization is constant because
the original input convention already makes the reserved cells zero. These are memory costs;
the native flat-program proof must additionally charge its real prefix, arithmetic and control.

## Main results

* `run_spec`: original admissibility and distance output, with the sharper reachable-vertex
  memory bound under the unchanged word-size envelope.
-/

public section

namespace Cslib.Algorithms.Lean.Dijkstra.Native.Fibonacci

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.PriorityQueue
open Cslib.Algorithms.Dijkstra (ListInstance)
open Cslib.Algorithms.WordRAM.Dijkstra (encodeDist)

private def rate (n : ℕ) : OpKind → ℕ
  | .insert => 43
  | .extractMin => 92 * (Nat.log 2 n + 1)
  | .decreaseKey => 104
  | .inspect => 0
  | .distance => 1
  | .graph => 3

private theorem charge_le_rate {n K V : ℕ} (s : (spec n K V).State)
    (o : (spec n K V).Op) (ho : kind o ≠ .inspect) :
    opCharge n K V s o ≤ rate n (kind o) := by
  rcases o with (_ | _ | _ | _ | _) | ((_ | _) | (_ | _))
  · exact absurd rfl ho
  · exact absurd rfl ho
  · exact le_rfl
  · exact le_rfl
  · exact Nat.mul_le_mul_left 92 (Nat.add_le_add_right
      (Nat.log_mono_right ((Finset.card_le_card (Finset.subset_univ _)).trans (by simp))) 1)
  all_goals exact le_rfl

private theorem budget_le (n m : ℕ) (hn : 0 < n) :
    5 + rateBound (rate n) n m ≤
      400 * (m + min n (m + 1) * (Nat.log 2 n + 1)) := by
  have hL : 1 ≤ Nat.log 2 n + 1 := by omega
  by_cases h : n ≤ m + 1
  · rw [Nat.min_eq_left h]
    refine (Nat.add_le_add_left (min_le_left _ _) 5).trans ?_
    dsimp only [rate]
    rw [show n * (92 * (Nat.log 2 n + 1)) = 92 * (n * (Nat.log 2 n + 1)) by ring]
    have hl : n ≤ n * (Nat.log 2 n + 1) := Nat.le_mul_of_pos_right n hL
    omega
  · rw [Nat.min_eq_right (by omega)]
    refine (Nat.add_le_add_left (min_le_right _ _) 5).trans ?_
    dsimp only [rate]
    rw [show (m + 2) * (92 * (Nat.log 2 n + 1)) =
      92 * ((m + 1) * (Nat.log 2 n + 1)) + 92 * (Nat.log 2 n + 1) by ring]
    have hl : m + 1 ≤ (m + 1) * (Nat.log 2 n + 1) := Nat.le_mul_of_pos_right _ hL
    have hL' : Nat.log 2 n + 1 ≤ (m + 1) * (Nat.log 2 n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega

/-- The actual Fibonacci memory program preserves the original admissibility and output
contract. Its sharper bound includes the five header/allocation queries, and pays the heap's
actual nonzero potential through the existing framed amortized telescope. -/
theorem run_spec (G : ListInstance) {w : ℕ}
    (hfit : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) :
    (Memory.spec w).ValidHistory (Memory.State.init G.encode)
        ((Memory.spec w).clientHistory (Memory.State.init G.encode) run) ∧
      (∀ v : Fin G.n, ((Memory.spec w).clientState (Memory.State.init G.encode) run).mem
        (G.outAddr v) = encodeDist (G.dist G.source v)) ∧
      (Memory.spec w).totalCost Memory.charge (Memory.State.init G.encode)
        ((Memory.spec w).clientHistory (Memory.State.init G.encode) run) ≤
          400 * (G.m + min G.n (G.m + 1) * (Nat.log 2 G.n + 1)) := by
  let s₀ := Memory.State.init G.encode
  let f := s₀.frontier
  let K := G.n * G.maxWeight
  let T : Block := ⟨f, G.n⟩
  let base := f + G.n
  let s₁ : Memory.State := ⟨s₀.mem, base + (9 * G.n + 5)⟩
  have hf : s₀.frontier = G.n + 2 * G.m + 4 := Memory.frontier_init G
  have hend : Fits w (base + (9 * G.n + 5)) :=
    hfit.of_le (by
      have h16 : 8 * (G.n + G.m + 2) * 2 ≤ 8 * (G.n + G.m + 2) * (G.maxWeight + 2) :=
        Nat.mul_le_mul_left _ (by omega)
      dsimp only [base, f]; rw [hf]; omega)
  have hn : Fits w G.n := hend.of_le (by dsimp only [base, f]; omega)
  have hK1 : Fits w (K + 1) := hfit.of_le ((show K + 1 ≤ (G.n + 1) * (G.maxWeight + 1) by
    dsimp only [K]; rw [Nat.add_one_mul, Nat.mul_add_one]; omega).trans
    (Nat.mul_le_mul (by omega) (by omega)))
  have hK : Fits w K := hK1.of_le (by omega)
  have hT : Dictionary.Memory.Valid T w G.n (K + 1) := ⟨rfl, hK1⟩
  have hA : (Memory.inputGraph G.n G.m).Valid G.n := ⟨rfl⟩
  let M := framed hn hK base hT hA G.adj
  obtain ⟨hinv, habs⟩ := inv_input G hn hK hT hA hend
  obtain ⟨hvalid, hdist⟩ := dijkstra_correct (K := K) (V := K + 1) G le_rfl (by omega)
  rw [← habs] at hvalid hdist
  obtain ⟨hvE, -, hstate, -⟩ := M.simulates_client (dijkstra G.source) hinv hvalid
  have hcost := (amortized (base := base) hn hK hT hA G.adj).client
    (dijkstra G.source) hinv hvalid
  have hcost' := totalCost_dijkstra_le (K := K) (V := K + 1) G le_rfl (by omega)
    (opCharge G.n K (K + 1)) (rate G.n) charge_le_rate
  rw [← habs] at hcost'
  have hz : ZeroAbove s₀ := zeroAbove_init _
  have hp : (FibonacciHeap.potential G.n ((FibonacciHeap.layout G.n base).abs s₁) + 0) +
      (0 + 0) = 0 := by
    change 24 * (s₀.mem (base + 9 * G.n + 2) +
      2 * s₀.mem (base + 9 * G.n + 3)) + 0 + (0 + 0) = 0
    rw [hz _ (by dsimp only [base, f]; omega), hz _ (by dsimp only [base, f]; omega)]
  rw [hp] at hcost
  have hprog : link (methods G.n 0 0 0 base T (Memory.inputGraph G.n G.m))
      (dijkstra (K := 0) (V := 0) G.source) = link M.methods
        (dijkstra (K := K) (V := K + 1) G.source) := by
    rw [show M.methods = methods G.n K (K + 1) w base T (Memory.inputGraph G.n G.m) from rfl,
      Memory.dijkstra_eq K (K + 1) 0 0, methods_eq G.n K (K + 1) w 0 0 0]
    rfl
  have hclient : Triple w s₁ (link (methods G.n 0 0 0 base T (Memory.inputGraph G.n G.m))
      (dijkstra (K := 0) (V := 0) G.source)) (rateBound (rate G.n) G.n G.m)
      (fun _ s' => ∀ v : Fin G.n, s'.mem (G.outAddr v) = encodeDist (G.dist G.source v)) := by
    rw [hprog]
    refine triple_iff.mpr ⟨hvE, ?_, fun v => ?_⟩
    · simp only [Nat.add_zero] at hcost
      exact (Nat.le_add_right _ _).trans (hcost.trans hcost')
    · obtain ⟨dist, hds, hdv⟩ := hdist
      rw [← hstate] at hds
      have hcell := congrArg (fun x => x.2.1 v) hds
      change Dictionary.Memory.decode
        (((Memory.spec w).clientState s₁ (link M.methods (dijkstra G.source))).mem
          (f + v)) = dist v at hcell
      dsimp only [ListInstance.outAddr]
      rw [← hf]
      exact Memory.eq_encodeDist fun d => by rw [← hdv v d, ← hcell]
  have htriple : Triple w s₀ run (rateBound (rate G.n) G.n G.m + 5)
      (fun _ s' => ∀ v : Fin G.n, s'.mem (G.outAddr v) = encodeDist (G.dist G.source v)) := by
    unfold run
    refine Triple.read_bind (by rw [hf]; omega) <| Triple.read_bind (by rw [hf]; omega) ?_
    rw [show s₀.mem 1 = G.n from rfl, show s₀.mem 2 = G.source from rfl]
    refine Triple.read_bind (by rw [hf]; omega) ?_
    rw [Memory.init_mem_edgeCount G]
    refine Triple.allocBlockDirty_bind (hend.of_le (by dsimp only [base, f]; omega)) ?_
    rw [triple_iff] at hclient ⊢
    simp only [dite_eq_left G.source.isLt]
    exact ⟨⟨hend, hclient.1⟩,
      (Nat.add_le_add_left hclient.2.1 1).trans_eq (Nat.add_comm 1 _), hclient.2.2⟩
  obtain ⟨hv, hc, hd⟩ := triple_iff.mp htriple
  have hbud := budget_le G.n G.m (by have := G.source.isLt; omega)
  exact ⟨hv, hd, hc.trans (by omega)⟩

end Cslib.Algorithms.Lean.Dijkstra.Native.Fibonacci
