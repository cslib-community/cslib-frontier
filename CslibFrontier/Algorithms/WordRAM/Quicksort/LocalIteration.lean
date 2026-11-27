/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Quicksort.PointerPartition

/-!
# Randomized iteration of local-address quicksort

Pop one pending range, draw a uniform rank using its stored length, then partition and enqueue
the strict children. The execution theorem exposes each outcome's instruction count and
partition result as functions of the one uniform rank.
-/

public section

namespace Cslib.Algorithms.WordRAM.Quicksort

open Cslib.WordRAM Reg

private abbrev IterState (n : ℕ) := Local.Data localModel n 16 16
private abbrev iterSet (n : ℕ) := Local.instructionSet localModel n 16 16

private def drawRank : Program.Code (Local.Op localModel 16 16) (Local.Test localModel 16 16) :=
  .op (.scalar .draw tmp tmp zero)

/-- Pop a pending range, draw its pivot rank, and partition and enqueue its children. -/
def localIteration : Program.Code (Local.Op localModel 16 16) (Local.Test localModel 16 16) :=
  .seq localPop (.seq drawRank partitionAndEnqueue)

/-- The state immediately after removing a known frame and drawing a known rank from it.
The saved frame remains in the backing cells outside the live stack. -/
@[expose] def rankedFrame {n : ℕ} (x : Local.Data localModel n 16 16)
    (start stop slot : Fin n) (rank : ℕ) : Local.Data localModel n 16 16 :=
  { x with
    addr := Function.update (Function.update (Function.update x.addr hi (some stop))
      lo (some start)) sp (some slot)
    scalars := Function.update x.scalars tmp rank }

private theorem drawRank_exec {n : ℕ} (x : IterState n) (bound : ℕ)
    (hlen : x.scalars tmp = bound) :
    Program.ExecRand (I := iterSet n) (Local.evalRand localKernel) drawRank x
      ((fun k : Fin (bound - 1 + 1) =>
        ({ x with scalars := Function.update x.scalars tmp k.val }, 1)) <$>
        ProbComp.unifFin (bound - 1)) := by
  subst bound
  have hop : Local.evalRand localKernel (.scalar LocalScalar.draw tmp tmp zero) x =
      some ((fun k : Fin (x.scalars tmp - 1 + 1) =>
        { x with scalars := Function.update x.scalars tmp k.val }) <$>
        ProbComp.unifFin (x.scalars tmp - 1)) := by
    simp [Local.evalRand, localKernel, Functor.map_map]
  simpa only [drawRank, Functor.map_map] using Program.ExecRand.op (I := iterSet n) hop

private theorem rank_lt_stop {start stop : ℕ} (h : start + 2 ≤ stop)
    (k : Fin (stop - start - 1 + 1)) : start + k.val < stop := by
  have hk := k.isLt
  omega

/-- Each iteration uses one uniform draw. The postcondition gives the two exact child sizes
and the resulting stack for each rank. The frame starts at `slot`, with the initial stack
cursor two cells beyond it. -/
theorem localIteration_exec {n w : ℕ} (x : Local.Data localModel n 16 16)
    (start stop slot : Fin n) (hroom : slot.val + 4 < n)
    (hsp : x.addr sp = some ⟨slot.val + 2, by omega⟩)
    (hfirst : x.refs slot = some start) (hlast : x.refs ⟨slot.val + 1, by omega⟩ = some stop)
    (hlen : x.values slot = stop.val - start.val) (hnontrivial : start.val + 2 ≤ stop.val)
    (hzero : x.scalars zero = 0) (hone : x.scalars one = 1) (hfit : Fits w stop.val) :
    let len := stop.val - start.val
    ∃ y : Fin (len - 1 + 1) → Local.Data localModel n 16 16,
    ∃ t : Fin (len - 1 + 1) → ℕ,
      Program.ExecRand (I := Local.instructionSet localModel n 16 16) (Local.evalRand localKernel)
        localIteration x ((fun k => (y k, 6 + t k)) <$> ProbComp.unifFin (len - 1)) ∧
      ∀ k : Fin (len - 1 + 1),
        t k ≤ 19 * len + 4 * k.val + 35 ∧
        PartitionResult (w := w) (rankedFrame x start stop slot k.val) (y k) start stop slot
          k.val (by have := k.isLt; omega) hroom := by
  classical
  intro len
  let popped := rankedFrame x start stop slot len
  have hp : Program.Exec (iterSet n) localPop x popped 5 := by
    simpa [popped, rankedFrame, hfirst, hlast, hlen, len] using
      localPop_exec x slot (by omega) hsp
  have hpRand := exec_asRand hp localPop_noDraw
  have hdraw := drawRank_exec popped len (by simp [popped, rankedFrame])
  have hphase (k : Fin (len - 1 + 1)) :
      ∃ y t, Program.Exec (iterSet n) partitionAndEnqueue
          (rankedFrame x start stop slot k.val) y t ∧
        t ≤ 19 * len + 4 * k.val + 35 ∧
        PartitionResult (w := w) (rankedFrame x start stop slot k.val) y start stop slot
          k.val (rank_lt_stop hnontrivial k) hroom := by
    have hk := rank_lt_stop hnontrivial k
    obtain ⟨y, ⟨t, ht, he⟩, hy⟩ := partitionAndEnqueue_exec
      (rankedFrame x start stop slot k.val) start stop slot k.val
      (by simp [rankedFrame]) (by simp [rankedFrame]) (by simp [rankedFrame])
      (by simp [rankedFrame]) (by simp [rankedFrame, hzero]) (by simp [rankedFrame, hone])
      hk hfit hroom
    exact ⟨y, t, he, ht, hy⟩
  choose y t he ht hy using hphase
  let next (u : IterState n) : ProbComp (IterState n × ℕ) :=
    if hk : u.scalars tmp < len - 1 + 1 then pure (y ⟨u.scalars tmp, hk⟩, t ⟨u.scalars tmp, hk⟩)
    else pure (u, 0)
  have hnext (k : Fin (len - 1 + 1)) :
      next (rankedFrame x start stop slot k.val) = pure (y k, t k) := by
    simp only [next, rankedFrame, Function.update_self, dite_eq_left k.isLt]
  have hsampleState (k : Fin (len - 1 + 1)) :
      { popped with scalars := Function.update popped.scalars tmp k.val } =
        rankedFrame x start stop slot k.val := by
    simp [popped, rankedFrame, Function.update_idem]
  have htail : Program.ExecRand (I := iterSet n) (Local.evalRand localKernel)
      (.seq drawRank partitionAndEnqueue) popped
      ((fun k => (y k, 1 + t k)) <$> ProbComp.unifFin (len - 1)) := by
    have hbind := Program.ExecRand.seq hdraw (m₂ := next) (by
      intro u hu
      obtain ⟨k, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hu
      change Program.ExecRand (I := iterSet n) (Local.evalRand localKernel) partitionAndEnqueue
        { popped with scalars := Function.update popped.scalars tmp k.val }
        (next { popped with scalars := Function.update popped.scalars tmp k.val })
      rw [hsampleState, hnext]
      exact exec_asRand (he k) partitionAndEnqueue_noDraw)
    simpa only [bind_map_left, hsampleState, hnext, pure_bind, map_pure, bind_pure_comp] using hbind
  refine ⟨y, t, ?_, fun k => ⟨ht k, hy k⟩⟩
  have hrun := Program.ExecRand.seq hpRand (m₂ := fun _ =>
    (fun k => (y k, 1 + t k)) <$> ProbComp.unifFin (len - 1)) (by
    intro z hz
    obtain rfl := OracleComp.eq_of_mem_supportWith_pure hz
    exact htail)
  simpa only [localIteration, pure_bind, bind_map_left, bind_pure_comp, Functor.map_map,
    ← Nat.add_assoc] using hrun

/-- The assembled pointer-machine iteration reaches its final halt within a linear budget,
with the same distribution of child stacks as the local-address program. -/
theorem pointerIteration_exec {n w : ℕ} (x : Local.Data localModel n 16 16)
    (start stop slot : Fin n) (hroom : slot.val + 4 < n)
    (hsp : x.addr sp = some ⟨slot.val + 2, by omega⟩)
    (hfirst : x.refs slot = some start) (hlast : x.refs ⟨slot.val + 1, by omega⟩ = some stop)
    (hlen : x.values slot = stop.val - start.val) (hnontrivial : start.val + 2 ≤ stop.val)
    (hzero : x.scalars zero = 0) (hone : x.scalars one = 1) (hfit : Fits w stop.val) :
    let len := stop.val - start.val
    let target := Local.randomizedFlatMachine (M := localModel) (p := 16) (d := 16) localKernel
    let code := Local.compile localIteration
    ∃ y : Fin (len - 1 + 1) → Local.Data localModel n 16 16,
      target.run code.program (23 * len + 37) (target.running 0 (Local.encode x)) =
        ((fun k => target.running code.size (Local.encode (y k))) <$>
          ProbComp.unifFin (len - 1)) ∧
      ∀ k : Fin (len - 1 + 1),
        PartitionResult (w := w) (rankedFrame x start stop slot k.val) (y k) start stop slot
          k.val (by have := k.isLt; omega) hroom := by
  intro len target code
  obtain ⟨y, t, hrun, hpost⟩ :=
    localIteration_exec x start stop slot hroom hsp hfirst hlast hlen hnontrivial hzero hone hfit
  have hbound : ∀ z ∈
      (((fun k : Fin (len - 1 + 1) => (y k, 6 + t k)) <$> ProbComp.unifFin (len - 1))).support,
        z.2 ≤ 23 * len + 37 := by
    intro z hz
    obtain ⟨k, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    have htime := (hpost k).1
    have hk := k.isLt
    change t k ≤ 19 * len + 4 * k.val + 35 at htime
    change 6 + t k ≤ 23 * len + 37
    omega
  refine ⟨y, ?_, fun k => (hpost k).2⟩
  simpa only [Functor.map_map] using Local.runRand_compile localKernel hrun hbound

/-- The potential charge for one iteration, including its enclosing loop test and jump.
Doubling the existing quicksort potential pays for the extra scans. The cost function is the
partition-and-enqueue instruction count for each rank, after the six pop and draw instructions. -/
theorem localIteration_average_le (u : List ℕ) (hm : 2 ≤ u.length) (t : Fin u.length → ℕ)
    (ht : ∀ k, t k ≤ 19 * u.length + 4 * k.val + 35) :
    (∑ k : Fin u.length, (((8 + t k : ℕ) : ℝ) +
      2 * (subCost (u.countP (· < u[k.val])) + subCost (u.countP (u[k.val] < ·))))) /
        (u.length : ℝ) ≤ 2 * subCost u.length := by
  have hden : (0 : ℝ) ≤ u.length := by positivity
  have hsum : (∑ k : Fin u.length, (((8 + t k : ℕ) : ℝ) +
      2 * (subCost (u.countP (· < u[k.val])) + subCost (u.countP (u[k.val] < ·))))) ≤
      ∑ k : Fin u.length, 2 * (32 * (u.length : ℝ) + 0 +
        (subCost (u.countP (· < u[k.val])) + subCost (u.countP (u[k.val] < ·)))) := by
    refine Finset.sum_le_sum fun k _ => ?_
    have htime : 8 + t k ≤ 64 * u.length := by
      have := ht k
      have := k.isLt
      omega
    have htime' : ((8 + t k : ℕ) : ℝ) ≤ 64 * (u.length : ℝ) := by exact_mod_cast htime
    linarith
  have havg := div_le_div_of_nonneg_right hsum hden
  rw [← Finset.mul_sum, mul_div_assoc] at havg
  have hpotential := mul_le_mul_of_nonneg_left (avg_subCost_pivot_le u hm 0)
    (by norm_num : 0 ≤ (2 : ℝ))
  simpa only [zero_add] using havg.trans hpotential

end Cslib.Algorithms.WordRAM.Quicksort
