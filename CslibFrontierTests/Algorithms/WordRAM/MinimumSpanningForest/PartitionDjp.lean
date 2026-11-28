/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.Partition.DjpLoop
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import Mathlib.Tactic.Linarith

/-!
# Tests for Dynamic Soft-Heap Partition DJP Subroutines

Verifies under Lean 4 `module` encapsulation:
1. End-to-end composite `realize` synthesis (`partSingleRoundProg`) combining `partSetup`,
   `partRoundInit`, and `partDjpLoop`, together with a lowered width-blind `Program .standard`
   execution check (`partSingleRound_standard_exec_test`) and `rankThresholdForEps (1 / 16) = 8`.
2. Boundary cases: empty edge list (`m = 0`), single vertex (`n = 1`), `maxsize = 1` early stop,
   and a non-zero `dead0` early-stop witness (`hitPrev = 1`).
3. Connected component (`n = 3, m = 2`), cyclic triangle (`n = 3, m = 3` distinct weights), and
   parallel-edge loopless multigraph (`n = 3, m = 3`) executions of `partSetup_spec`,
   `partRoundInit_spec`, and `partDjpLoop_spec`.
-/

public section

namespace CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.PartitionDjp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Query.MinimumSpanningForest
open Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap
open Cslib.Algorithms.WordRAM.MinimumSpanningForest

/-! ## Composite Realization Pipeline and `Program .standard` Execution -/

/-- Composite single-round Word-RAM program running `partSetup`, `partRoundInit`, and
`partDjpLoop` from root vertex `d.2`. -/
def partSingleRoundProg (d : PartSetupArgs × ℕ) : Memory.Prog PartDjpState := do
  let setup ← partSetup d.1
  let hInit ← partRoundInit ⟨setup.env, 1, d.2, setup.sh⟩
  partDjpLoop ⟨setup.env, 1, 0, hInit⟩

private def partSingleRoundSafe (w : ℕ) (d : PartSetupArgs × ℕ) (s : Memory.State) : Prop :=
  let setup := (Memory.spec 0).clientResult s (partSetup d.1)
  let s1 := (Memory.spec 0).clientState s (partSetup d.1)
  let hInit := (Memory.spec 0).clientResult s1 (partRoundInit ⟨setup.env, 1, d.2, setup.sh⟩)
  let s2 := (Memory.spec 0).clientState s1 (partRoundInit ⟨setup.env, 1, d.2, setup.sh⟩)
  Fits w 16 ∧
  partSetupSafe w d.1 s ∧
  partRoundInitSafe w ⟨setup.env, 1, d.2, setup.sh⟩ s1 ∧
  partDjpLoopSafe w ⟨setup.env, 1, 0, hInit⟩ s2

example : rankThresholdForEps (1 / 16 : ℚ) = 8 := by
  rw [← partRankThreshold_eq_eps]
  rfl

/-! ## Generic Component Execution Helper (Local) -/

private theorem single_round_pipeline_facts {w n edgeBase maxsize : ℕ}
    {es : List (IndexedEdge n)} {s₀ : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s₀)
    (hn_pos : 1 ≤ n) (hmax_pos : 1 ≤ maxsize)
    (hin : HoldsIndexedEdges edgeBase es s₀.mem)
    (hin_lt : edgeBase + 4 * es.length ≤ s₀.frontier)
    (hfit : Fits w (s₀.frontier + 1100 * (es.length + n + 1)))
    (hsimp : ∀ e : Fin es.length, es[e.val].u ≠ es[e.val].v)
    (u : Fin n) :
    let d : PartSetupArgs := ⟨n, es.length, edgeBase, maxsize⟩
    let setupRes := (Memory.spec 0).clientResult s₀ (partSetup d)
    let s1 := (Memory.spec 0).clientState s₀ (partSetup d)
    let hInit :=
      (Memory.spec 0).clientResult s1 (partRoundInit ⟨setupRes.env, 1, u.val, setupRes.sh⟩)
    let s2 := (Memory.spec 0).clientState s1 (partRoundInit ⟨setupRes.env, 1, u.val, setupRes.sh⟩)
    let loopRes := (Memory.spec 0).clientResult s2 (partDjpLoop ⟨setupRes.env, 1, 0, hInit⟩)
    let s3 := (Memory.spec 0).clientState s2 (partDjpLoop ⟨setupRes.env, 1, 0, hInit⟩)
    partSingleRoundSafe w (d, u.val) s₀ ∧
    (Memory.spec w).ValidHistory s₀
      ((Memory.spec w).clientHistory s₀ (partSingleRoundProg (d, u.val))) ∧
    memoryCost (partSingleRoundProg (d, u.val)) s₀ ≤
      17 * es.length + 8 * n + 9 + (5450 * es.length + 15) ∧
    loopRes.cont = 0 ∧ loopRes.size ≤ maxsize ∧ loopRes.tLen + 1 = loopRes.size ∧
    (memoryCost (partRoundInit ⟨setupRes.env, 1, u.val, setupRes.sh⟩) s1 : ℚ) +
      (memoryCost (partDjpLoop ⟨setupRes.env, 1, 0, hInit⟩) s2 : ℚ) ≤
      5450 * (es.length : ℚ) + 15 ∧
    (s3.mem (setupRes.env.bufBase + 3 * n) = u.val) := by
  have hs := partSetup_spec h16 hwf hn_pos hmax_pos hin hin_lt hfit
  rcases hs with ⟨hsafe_s, hvh_s, hcost_s, hn_eq, hm_eq, heb_eq, hmax_eq, _, hsh_eq, hs1_fr, hwf1,
    _, hin1, hcsr1, hinv1, hzero_buf, hedge1, L, hL_env, hL_es, hL_eb, hL_max, _, _, hL_ib,
    hL_nb, hL_buf, _⟩
  set setupProg := partSetup ⟨n, es.length, edgeBase, maxsize⟩
  set setupRes := (Memory.spec 0).clientResult s₀ setupProg
  set s1 := (Memory.spec 0).clientState s₀ setupProg
  have hL_env_eq : setupRes.env = L.toEnv := hL_env.symm
  have hib0 : setupRes.sh.itemBase = L.itemBase := hL_ib.symm
  have hnb0 : setupRes.sh.nodeBase = L.nodeBase := hL_nb.symm
  have hrt0 : setupRes.sh.rankThreshold = partRankThreshold := by rw [hsh_eq]
  have hic0 : setupRes.sh.itemCount = 0 := by rw [hsh_eq]
  have hs1_fr' : s1.frontier = L.bufBase + (14 * n + 14 * L.es.length) := by
    rw [hs1_fr, hL_buf, hL_es]
  have hinv1' :
      SHInv w 0 0 (2 * L.es.length) (4 * L.es.length) setupRes.sh [] (fun _ => 0) s1 := by
    simpa only [hL_es] using hinv1
  have hcsr1' : HoldsUndirCSR L.offBase L.adjBase L.es s1.mem := by
    simpa only [hL_env_eq, PartLayout.toEnv, hL_es] using hcsr1
  have hin1' : HoldsIndexedEdges L.edgeBase L.es s1.mem := by
    rw [hL_eb, hL_es]; exact hin1
  have hdead1 : ∀ x < n, s1.mem (L.bufBase + x) = 0 := fun x hx => by
    rw [hL_buf]; exact hzero_buf x (by omega)
  have hincur1 : ∀ x < n, s1.mem (L.bufBase + n + x) = 0 := fun x hx => by
    rw [hL_buf, Nat.add_assoc]; exact hzero_buf (n + x) (by omega)
  have hedge1' : ∀ i < L.es.length, s1.mem (L.bufBase + 14 * n + i) = 0 := fun i hi => by
    rw [hL_buf]; exact hedge1 i (by simpa only [hL_es] using hi)
  have hsimp' : ∀ e : Fin L.es.length, L.es[e.val].u ≠ L.es[e.val].v := by
    subst hL_es; exact hsimp
  have hrem0 : remDeg n L.offBase s1.mem (Finset.univ.filter (fun x : Fin n => (0 : ℕ) ≠ 0)) =
      2 * L.es.length := by
    have heq : (Finset.univ.filter (fun x : Fin n => (0 : ℕ) ≠ 0)) = ∅ := by ext; simp
    rw [heq]; exact remDeg_empty hcsr1'
  have hcap0 : 0 + remDeg n L.offBase s1.mem
      (Finset.univ.filter (fun x : Fin n => (0 : ℕ) ≠ 0)) ≤ 2 * L.es.length := by
    rw [hrem0]; omega
  have hinit := partRoundInit_spec L (fun _ => 0) (fun _ => 0) (fun _ => 0) 1 0 0 0 u
    setupRes.sh s1 hs1_fr' hib0 hnb0 hrt0 hic0 hinv1' hcsr1' hin1' hincur1
    (fun _ _ => by omega) (h16.of_le (by omega)) rfl hedge1' hsimp' (by simp) hcap0
  rcases hinit with ⟨hsafe_i, hvh_i, _, _, W₀, hinit_pot⟩
  let hInitL := (Memory.spec 0).clientResult s1 (partRoundInit ⟨L.toEnv, 1, u.val, setupRes.sh⟩)
  let s2L := (Memory.spec 0).clientState s1 (partRoundInit ⟨L.toEnv, 1, u.val, setupRes.sh⟩)
  have hloop := partDjpLoop_spec L s1 (fun _ => 0) (fun _ => 0) (fun _ => 0) 1 0 0 0 u
    hcsr1' hin1' hdead1 hedge1' (fun _ _ => by omega) (h16.of_le (by omega)) hsimp' hInitL s2L W₀
  rcases hloop with ⟨hsafe_l, hvh_l, hcont0, _, _, W', hloop_pot⟩
  have hpot_nonneg : (0 : ℚ) ≤ djpPot W' := by
    dsimp only [djpPot]
    have hphi := Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.totalPhi_nonneg
      partRankThreshold W'.roots
    positivity
  have hrem_q : (remDeg n L.offBase s1.mem
      (Finset.univ.filter (fun x : Fin n => (0 : ℕ) ≠ 0)) : ℚ) =
      2 * (es.length : ℚ) := by
    rw [hrem0, hL_es]; push_cast; ring
  have hesq : ((2 * L.es.length - 0 : ℕ) : ℚ) = 2 * (es.length : ℚ) := by
    rw [hL_es, Nat.sub_zero]; push_cast; ring
  have hcost_il_q : (memoryCost (partRoundInit ⟨L.toEnv, 1, u.val, setupRes.sh⟩) s1 : ℚ) +
      (memoryCost (partDjpLoop ⟨L.toEnv, 1, 0, hInitL⟩) s2L : ℚ) ≤
      5450 * (es.length : ℚ) + 15 := by
    rw [hrem_q, hesq] at hinit_pot
    linarith
  have hcost_il_nat : memoryCost (partRoundInit ⟨L.toEnv, 1, u.val, setupRes.sh⟩) s1 +
      memoryCost (partDjpLoop ⟨L.toEnv, 1, 0, hInitL⟩) s2L ≤
      5450 * es.length + 15 := by
    exact_mod_cast hcost_il_q
  let hInit := (Memory.spec 0).clientResult s1 (partRoundInit ⟨setupRes.env, 1, u.val, setupRes.sh⟩)
  let s2 := (Memory.spec 0).clientState s1 (partRoundInit ⟨setupRes.env, 1, u.val, setupRes.sh⟩)
  have hhInit : hInitL = hInit := by dsimp only [hInitL, hInit]; rw [hL_env]
  have hs2 : s2L = s2 := by dsimp only [s2L, s2]; rw [hL_env]
  have hres_eq :
      (Memory.spec 0).clientResult s2L (partDjpLoop ⟨L.toEnv, 1, 0, hInitL⟩) =
        (Memory.spec 0).clientResult s2 (partDjpLoop ⟨setupRes.env, 1, 0, hInit⟩) := by
    rw [hL_env, hhInit, hs2]
  have hs3_eq :
      (Memory.spec 0).clientState s2L (partDjpLoop ⟨L.toEnv, 1, 0, hInitL⟩) =
        (Memory.spec 0).clientState s2 (partDjpLoop ⟨setupRes.env, 1, 0, hInit⟩) := by
    rw [hL_env, hhInit, hs2]
  rw [hL_env] at hsafe_i hvh_i
  rw [hL_env, hhInit, hs2] at hsafe_l hvh_l hcont0 hcost_il_q hcost_il_nat
  have hvh_all : (Memory.spec w).ValidHistory s₀
      ((Memory.spec w).clientHistory s₀
        (partSingleRoundProg (⟨n, es.length, edgeBase, maxsize⟩, u.val))) := by
    unfold partSingleRoundProg
    dsimp only [setupProg, setupRes, s1, hInit, s2] at hvh_s hvh_i hvh_l ⊢
    exact validHistory_bind_step hvh_s (validHistory_bind_step hvh_i hvh_l)
  have hcost_all : memoryCost (partSingleRoundProg (⟨n, es.length, edgeBase, maxsize⟩, u.val)) s₀ ≤
      17 * es.length + 8 * n + 9 + (5450 * es.length + 15) := by
    unfold partSingleRoundProg
    dsimp only
    rw [memoryCost_bind', memoryCost_bind']
    dsimp only [setupProg, setupRes, s1, hInit, s2] at hcost_s hcost_il_nat ⊢
    have hc := Nat.add_le_add hcost_s hcost_il_nat
    exact hc.trans (by omega)
  have hbb : L.bufBase = setupRes.env.bufBase := by
    simpa [PartLayout.toEnv] using congrArg PartEnv.bufBase hL_env
  have hverts0 := W'.hverts_mem 0 (by have := W'.hsize; omega)
  have hr0 : ((djpVertsList W'.D)[0]'(by rw [djpVertsList_length]; omega)).val = u.val := by
    simp [djpVertsList, W'.hroot]
  have hsz_le := W'.hsize_le
  rw [hL_max] at hsz_le
  have hw1 := W'.hsize
  have hw2 := W'.htlen
  dsimp only [setupProg, setupRes, s1, hInit, s2] at hsafe_s hsafe_i hsafe_l hcont0 hcost_il_q
  dsimp only [setupProg, setupRes, s1, hInit, s2] at hres_eq hs3_eq hbb ⊢
  refine ⟨⟨h16, hsafe_s, hsafe_i, hsafe_l⟩, hvh_all, hcost_all, hcont0, ?_, ?_, hcost_il_q, ?_⟩
  · rw [← hres_eq]; exact hsz_le
  · rw [← hres_eq]; omega
  · have hu0 := hverts0.trans hr0
    rw [hs3_eq, hbb, Nat.add_zero] at hu0
    exact hu0

private theorem realizes_partSingleRoundProg_raw : Realizes .exact
    partSingleRoundProg WordEncoding.encode WordEncoding.encode
    partSingleRoundSafe (fun _ _ => 0) := by
  unfold partSingleRoundProg
  realize [realizes_partSetup, realizes_partRoundInit, realizes_partDjpLoop]
  all_goals
    rcases h with ⟨h16, h1, h2, h3⟩
    first | exact h16.of_le (by decide) | exact h1 | exact h2 | exact h3

/-- Composite `Realizes .exact` synthesis for `partSingleRoundProg` composing `partSetup`,
`partRoundInit`, and `partDjpLoop` end-to-end with `work = 0`. -/
theorem realizes_partSingleRoundProg : Realizes .exact
    partSingleRoundProg WordEncoding.encode WordEncoding.encode
    (fun w d s =>
      Fits w 16 ∧ 1 ≤ d.1.n ∧ 1 ≤ d.1.maxsize ∧ d.2 < d.1.n ∧
      d.1.edgeBase + 4 * d.1.m ≤ s.frontier ∧
      Fits w (s.frontier + 1100 * (d.1.m + d.1.n + 1)) ∧
      ∀ j < d.1.m,
        s.mem (d.1.edgeBase + 4 * j) < d.1.n ∧
        s.mem (d.1.edgeBase + 4 * j + 1) < d.1.n ∧
        s.mem (d.1.edgeBase + 4 * j) ≠ s.mem (d.1.edgeBase + 4 * j + 1))
    (fun _ _ => 0) := by
  refine realizes_partSingleRoundProg_raw.consequence (fun w d s _ hwf h => ?_) (fun _ _ => le_rfl)
  rcases d with ⟨⟨n, m, edgeBase, maxsize⟩, u⟩
  obtain ⟨h16, hn_pos, hmax_pos, hu, hin_lt, hfit, hedges⟩ := h
  let es : List (IndexedEdge n) := List.ofFn fun i : Fin m =>
    ⟨⟨s.mem (edgeBase + 4 * i.val), (hedges i.val i.isLt).1⟩,
     ⟨s.mem (edgeBase + 4 * i.val + 1), (hedges i.val i.isLt).2.1⟩,
     s.mem (edgeBase + 4 * i.val + 2), s.mem (edgeBase + 4 * i.val + 3)⟩
  have hlen : es.length = m := List.length_ofFn
  have hin : HoldsIndexedEdges edgeBase es s.mem := fun i hi => by simp [es]
  have hsimp : ∀ e : Fin es.length, es[e.val].u ≠ es[e.val].v := fun e => by
    intro heq
    have hne := (hedges e.val (hlen ▸ e.isLt)).2.2
    have heq' : s.mem (edgeBase + 4 * e.val) = s.mem (edgeBase + 4 * e.val + 1) := by
      simpa [es] using congrArg Fin.val heq
    exact hne heq'
  have hf := single_round_pipeline_facts h16 hwf hn_pos hmax_pos hin
    (by simpa [hlen] using hin_lt) (by simpa [hlen] using hfit) hsimp ⟨u, hu⟩
  simpa only [hlen] using hf.1

/-! ## Concrete Boundary, Multigraph, Early-Stop, and Standard-Program Scenarios -/

/-- Boundary test 1: empty edge list (`m = 0`) on `n = 3` vertices. -/
theorem empty_graph_test :
    let s₀ : Memory.State := ⟨fun _ => 0, 0⟩
    let setupRes := (Memory.spec 0).clientResult s₀ (partSetup ⟨3, 0, 0, 3⟩)
    let s1 := (Memory.spec 0).clientState s₀ (partSetup ⟨3, 0, 0, 3⟩)
    let hInit := (Memory.spec 0).clientResult s1 (partRoundInit ⟨setupRes.env, 1, 0, setupRes.sh⟩)
    let s2 := (Memory.spec 0).clientState s1 (partRoundInit ⟨setupRes.env, 1, 0, setupRes.sh⟩)
    let loopRes := (Memory.spec 0).clientResult s2 (partDjpLoop ⟨setupRes.env, 1, 0, hInit⟩)
    loopRes.cont = 0 ∧ loopRes.size ≤ 3 ∧ loopRes.tLen + 1 = loopRes.size := by
  have h16 : Fits 20 16 := by decide
  have hwf : Memory.WellFormed 20 ⟨fun _ => 0, 0⟩ :=
    ⟨by decide, fun _ => h16.of_le (by simp)⟩
  have hfit : Fits 20 (0 + 1100 * (0 + 3 + 1)) := by decide
  have hres := single_round_pipeline_facts (w := 20) (n := 3) (edgeBase := 0) (maxsize := 3)
    (es := []) h16 hwf (by decide) (by decide) (fun _ hi => by simp at hi) (by decide) hfit
    (fun e => Fin.elim0 e) ⟨0, by decide⟩
  exact ⟨hres.2.2.2.1, hres.2.2.2.2.1, hres.2.2.2.2.2.1⟩

/-- Boundary test 2: single vertex (`n = 1, m = 0`). -/
theorem single_vertex_test :
    let s₀ : Memory.State := ⟨fun _ => 0, 0⟩
    let setupRes := (Memory.spec 0).clientResult s₀ (partSetup ⟨1, 0, 0, 2⟩)
    let s1 := (Memory.spec 0).clientState s₀ (partSetup ⟨1, 0, 0, 2⟩)
    let hInit := (Memory.spec 0).clientResult s1 (partRoundInit ⟨setupRes.env, 1, 0, setupRes.sh⟩)
    let s2 := (Memory.spec 0).clientState s1 (partRoundInit ⟨setupRes.env, 1, 0, setupRes.sh⟩)
    let loopRes := (Memory.spec 0).clientResult s2 (partDjpLoop ⟨setupRes.env, 1, 0, hInit⟩)
    loopRes.cont = 0 ∧ loopRes.size ≤ 2 ∧ loopRes.tLen + 1 = loopRes.size := by
  have h16 : Fits 20 16 := by decide
  have hres := single_round_pipeline_facts (w := 20) (n := 1) (edgeBase := 0) (maxsize := 2)
    (es := []) (s₀ := ⟨fun _ => 0, 0⟩) h16 ⟨by decide, fun _ => h16.of_le (by simp)⟩
    (by decide) (by decide) (fun _ hi => by simp at hi) (by decide) (by decide)
    (fun e => Fin.elim0 e) ⟨0, by decide⟩
  exact ⟨hres.2.2.2.1, hres.2.2.2.2.1, hres.2.2.2.2.2.1⟩

/-- Sample RAM memory holding the encoded `n = 3`, `m = 2` path graph (`0 -5- 1 -2- 2`). -/
@[expose] def pathMem : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 5
  | 3 => 0
  | 4 => 1
  | 5 => 2
  | 6 => 2
  | 7 => 1
  | _ => 0

/-- Sample indexed edge list (`0 -5- 1 -2- 2`) on `3` vertices. -/
@[expose] def pathEdges : List (IndexedEdge 3) :=
  [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 5, 0⟩, ⟨⟨1, by decide⟩, ⟨2, by decide⟩, 2, 1⟩]

private theorem path_holds : HoldsIndexedEdges 0 pathEdges pathMem := by
  intro i hi
  simp only [pathEdges, List.length_cons, List.length_nil] at hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
    simp [pathEdges, pathMem]

private theorem path_simp (e : Fin pathEdges.length) :
    pathEdges[e.val].u ≠ pathEdges[e.val].v := by
  rcases e with ⟨i, hi⟩
  simp only [pathEdges, List.length_cons, List.length_nil] at hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp [pathEdges]

private theorem pathMem_wf : Memory.WellFormed 20 ⟨pathMem, 8⟩ := by
  have h16 : Fits 20 16 := by decide
  refine ⟨by decide, fun a => h16.of_le ?_⟩
  rcases a with _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp [pathMem]

/-- Boundary test 3: connected component (`n = 3`, path `0 -5- 1 -2- 2`) with `maxsize = 3`. -/
theorem connected_component_test :
    let s₀ : Memory.State := ⟨pathMem, 8⟩
    let setupRes := (Memory.spec 0).clientResult s₀ (partSetup ⟨3, 2, 0, 3⟩)
    let s1 := (Memory.spec 0).clientState s₀ (partSetup ⟨3, 2, 0, 3⟩)
    let hInit := (Memory.spec 0).clientResult s1 (partRoundInit ⟨setupRes.env, 1, 0, setupRes.sh⟩)
    let s2 := (Memory.spec 0).clientState s1 (partRoundInit ⟨setupRes.env, 1, 0, setupRes.sh⟩)
    let loopRes := (Memory.spec 0).clientResult s2 (partDjpLoop ⟨setupRes.env, 1, 0, hInit⟩)
    loopRes.cont = 0 ∧ loopRes.size ≤ 3 ∧ loopRes.tLen + 1 = loopRes.size := by
  have hres := single_round_pipeline_facts (w := 20) (n := 3) (edgeBase := 0) (maxsize := 3)
    (es := pathEdges) (s₀ := ⟨pathMem, 8⟩) (by decide) pathMem_wf (by decide) (by decide)
    path_holds (by decide) (by decide) path_simp ⟨0, by decide⟩
  exact ⟨hres.2.2.2.1, hres.2.2.2.2.1, hres.2.2.2.2.2.1⟩

/-- Boundary test 4: `maxsize = 1` early stop on `n = 3`, `m = 2`. -/
theorem maxsize_one_boundary_test :
    let s₀ : Memory.State := ⟨pathMem, 8⟩
    let setupRes := (Memory.spec 0).clientResult s₀ (partSetup ⟨3, 2, 0, 1⟩)
    let s1 := (Memory.spec 0).clientState s₀ (partSetup ⟨3, 2, 0, 1⟩)
    let hInit := (Memory.spec 0).clientResult s1 (partRoundInit ⟨setupRes.env, 1, 0, setupRes.sh⟩)
    let s2 := (Memory.spec 0).clientState s1 (partRoundInit ⟨setupRes.env, 1, 0, setupRes.sh⟩)
    let loopRes := (Memory.spec 0).clientResult s2 (partDjpLoop ⟨setupRes.env, 1, 0, hInit⟩)
    loopRes.cont = 0 ∧ loopRes.size ≤ 1 ∧ loopRes.tLen + 1 = loopRes.size := by
  have hres := single_round_pipeline_facts (w := 20) (n := 3) (edgeBase := 0) (maxsize := 1)
    (es := pathEdges) (s₀ := ⟨pathMem, 8⟩) (by decide) pathMem_wf (by decide) (by decide)
    path_holds (by decide) (by decide) path_simp ⟨0, by decide⟩
  exact ⟨hres.2.2.2.1, hres.2.2.2.2.1, hres.2.2.2.2.2.1⟩

/-- Sample RAM memory holding a cyclic triangle (`0 -5- 1 -2- 2 -8- 0`, `n = 3, m = 3`). -/
@[expose] def triMem : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 5
  | 3 => 0
  | 4 => 1
  | 5 => 2
  | 6 => 2
  | 7 => 1
  | 8 => 2
  | 9 => 0
  | 10 => 8
  | 11 => 2
  | _ => 0

/-- Cyclic triangle indexed edge list (`0 -5- 1 -2- 2 -8- 0`) with distinct weights. -/
@[expose] def triEdges : List (IndexedEdge 3) :=
  [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 5, 0⟩,
   ⟨⟨1, by decide⟩, ⟨2, by decide⟩, 2, 1⟩,
   ⟨⟨2, by decide⟩, ⟨0, by decide⟩, 8, 2⟩]

private theorem tri_holds : HoldsIndexedEdges 0 triEdges triMem := by
  intro i hi
  simp only [triEdges, List.length_cons, List.length_nil] at hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
    simp [triEdges, triMem]

private theorem tri_simp (e : Fin triEdges.length) :
    triEdges[e.val].u ≠ triEdges[e.val].v := by
  rcases e with ⟨i, hi⟩
  simp only [triEdges, List.length_cons, List.length_nil] at hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp [triEdges]

private theorem triMem_wf : Memory.WellFormed 20 ⟨triMem, 12⟩ := by
  have h16 : Fits 20 16 := by decide
  refine ⟨by decide, fun a => h16.of_le ?_⟩
  rcases a with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp [triMem]

/-- Boundary test 5: cyclic triangle (`n = 3, m = 3` distinct weights) with `maxsize = 3`. -/
theorem cyclic_triangle_test :
    let s₀ : Memory.State := ⟨triMem, 12⟩
    let setupRes := (Memory.spec 0).clientResult s₀ (partSetup ⟨3, 3, 0, 3⟩)
    let s1 := (Memory.spec 0).clientState s₀ (partSetup ⟨3, 3, 0, 3⟩)
    let hInit := (Memory.spec 0).clientResult s1 (partRoundInit ⟨setupRes.env, 1, 0, setupRes.sh⟩)
    let s2 := (Memory.spec 0).clientState s1 (partRoundInit ⟨setupRes.env, 1, 0, setupRes.sh⟩)
    let loopRes := (Memory.spec 0).clientResult s2 (partDjpLoop ⟨setupRes.env, 1, 0, hInit⟩)
    loopRes.cont = 0 ∧ loopRes.size ≤ 3 ∧ loopRes.tLen + 1 = loopRes.size := by
  have hres := single_round_pipeline_facts (w := 20) (n := 3) (edgeBase := 0) (maxsize := 3)
    (es := triEdges) (s₀ := ⟨triMem, 12⟩) (by decide) triMem_wf (by decide) (by decide)
    tri_holds (by decide) (by decide) tri_simp ⟨0, by decide⟩
  exact ⟨hres.2.2.2.1, hres.2.2.2.2.1, hres.2.2.2.2.2.1⟩

/-- Sample RAM memory holding a parallel-edge loopless multigraph (`0 -(7,3)- 1 -4- 2`). -/
@[expose] def multiMem : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 7
  | 3 => 0
  | 4 => 0
  | 5 => 1
  | 6 => 3
  | 7 => 1
  | 8 => 1
  | 9 => 2
  | 10 => 4
  | 11 => 2
  | _ => 0

/-- Parallel-edge loopless multigraph (`n = 3, m = 3`): two parallel edges `(0,1)` plus `(1,2)`. -/
@[expose] def multiEdges : List (IndexedEdge 3) :=
  [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 7, 0⟩,
   ⟨⟨0, by decide⟩, ⟨1, by decide⟩, 3, 1⟩,
   ⟨⟨1, by decide⟩, ⟨2, by decide⟩, 4, 2⟩]

private theorem multi_holds : HoldsIndexedEdges 0 multiEdges multiMem := by
  intro i hi
  simp only [multiEdges, List.length_cons, List.length_nil] at hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
    simp [multiEdges, multiMem]

private theorem multi_simp (e : Fin multiEdges.length) :
    multiEdges[e.val].u ≠ multiEdges[e.val].v := by
  rcases e with ⟨i, hi⟩
  simp only [multiEdges, List.length_cons, List.length_nil] at hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp [multiEdges]

private theorem multiMem_wf : Memory.WellFormed 20 ⟨multiMem, 12⟩ := by
  have h16 : Fits 20 16 := by decide
  refine ⟨by decide, fun a => h16.of_le ?_⟩
  rcases a with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp [multiMem]

/-- Boundary test 6: parallel-edge loopless multigraph (`n = 3, m = 3`) with `maxsize = 3`. -/
theorem parallel_edges_multigraph_test :
    let s₀ : Memory.State := ⟨multiMem, 12⟩
    let setupRes := (Memory.spec 0).clientResult s₀ (partSetup ⟨3, 3, 0, 3⟩)
    let s1 := (Memory.spec 0).clientState s₀ (partSetup ⟨3, 3, 0, 3⟩)
    let hInit := (Memory.spec 0).clientResult s1 (partRoundInit ⟨setupRes.env, 1, 0, setupRes.sh⟩)
    let s2 := (Memory.spec 0).clientState s1 (partRoundInit ⟨setupRes.env, 1, 0, setupRes.sh⟩)
    let loopRes := (Memory.spec 0).clientResult s2 (partDjpLoop ⟨setupRes.env, 1, 0, hInit⟩)
    loopRes.cont = 0 ∧ loopRes.size ≤ 3 ∧ loopRes.tLen + 1 = loopRes.size := by
  have hres := single_round_pipeline_facts (w := 20) (n := 3) (edgeBase := 0) (maxsize := 3)
    (es := multiEdges) (s₀ := ⟨multiMem, 12⟩) (by decide) multiMem_wf (by decide) (by decide)
    multi_holds (by decide) (by decide) multi_simp ⟨0, by decide⟩
  exact ⟨hres.2.2.2.1, hres.2.2.2.2.1, hres.2.2.2.2.2.1⟩

/-- Boundary test 7: non-zero `dead0` early stop (`dead[1] = 1` stops round at `hitPrev = 1`). -/
theorem dead_early_stop_test :
    let s₀ : Memory.State := ⟨pathMem, 8⟩
    let setupRes := (Memory.spec 0).clientResult s₀ (partSetup ⟨3, 2, 0, 3⟩)
    let s1 := (Memory.spec 0).clientState s₀ (partSetup ⟨3, 2, 0, 3⟩)
    let sDead : Memory.State :=
      ⟨Function.update s1.mem (setupRes.env.bufBase + 1) 1, s1.frontier⟩
    let hInit :=
      (Memory.spec 0).clientResult sDead (partRoundInit ⟨setupRes.env, 1, 0, setupRes.sh⟩)
    let s2 := (Memory.spec 0).clientState sDead (partRoundInit ⟨setupRes.env, 1, 0, setupRes.sh⟩)
    let loopRes := (Memory.spec 0).clientResult s2 (partDjpLoop ⟨setupRes.env, 1, 0, hInit⟩)
    loopRes.cont = 0 ∧ loopRes.hitPrev = 1 ∧ loopRes.size = 2 ∧ loopRes.tLen = 1 := by
  have h16 : Fits 20 16 := by decide
  have hs :=
    partSetup_spec (w := 20) (n := 3) (edgeBase := 0) (maxsize := 3)
      h16 pathMem_wf (by decide) (by decide) path_holds (by decide) (by decide)
  rcases hs with ⟨_, _, _, _, _, _, _, _, hsh_eq, hs1_fr, hwf1, _, hin1, hcsr1, hinv1, hzero_buf,
    hedge1, L, hL_env, hL_es, hL_eb, hL_max, _, _, hL_ib, hL_nb, hL_buf, _⟩
  have hplen : pathEdges.length = 2 := rfl
  rw [hplen] at hsh_eq hs1_fr hinv1 hin1 hcsr1 hzero_buf hedge1 hL_env hL_ib hL_nb hL_buf
  set setupProg := partSetup ⟨3, 2, 0, 3⟩
  set setupRes := (Memory.spec 0).clientResult ⟨pathMem, 8⟩ setupProg
  set s1 := (Memory.spec 0).clientState ⟨pathMem, 8⟩ setupProg
  let dead0 : ℕ → ℕ := Function.update (fun _ => 0) 1 1
  let sDead : Memory.State := ⟨Function.update s1.mem (L.bufBase + 1) 1, s1.frontier⟩
  have hL_env_eq : setupRes.env = L.toEnv := hL_env.symm
  have hib0 : setupRes.sh.itemBase = L.itemBase := hL_ib.symm
  have hnb0 : setupRes.sh.nodeBase = L.nodeBase := hL_nb.symm
  have hrt0 : setupRes.sh.rankThreshold = partRankThreshold := by rw [hsh_eq]
  have hic0 : setupRes.sh.itemCount = 0 := by rw [hsh_eq]
  have hs1_fr' : sDead.frontier = L.bufBase + (14 * 3 + 14 * L.es.length) := by
    dsimp only [sDead]; rw [hs1_fr, hL_buf, hL_es, hplen]
  have hsDead_below : ∀ x < L.itemBase, sDead.mem x = s1.mem x := fun x hx => by
    have := L.hit_nd; have := L.hnd_buf
    exact Function.update_of_ne (by omega) _ _
  have hinv_dead :
      SHInv 20 0 0 (2 * L.es.length) (4 * L.es.length) setupRes.sh [] (fun _ => 0) sDead := by
    have hwfD : Memory.WellFormed 20 sDead :=
      ⟨hwf1.frontier_fits, fun a => by
        dsimp only [sDead]
        by_cases ha : a = L.bufBase + 1
        · subst ha; rw [Function.update_self]; exact h16.of_le (by decide)
        · rw [Function.update_of_ne ha]; exact hwf1.mem_fits a⟩
    have hinv1' :
        SHInv 20 0 0 (2 * L.es.length) (4 * L.es.length) setupRes.sh [] (fun _ => 0) s1 := by
      simpa only [hL_es, hplen] using hinv1
    refine hinv1'.congr_outside hwfD rfl fun a ha => ?_
    rcases L.inSHPool_lt_bufBase hib0 hnb0 ha with ⟨h1, h2⟩
    exact Function.update_of_ne (by omega) _ _
  have hcsr1' : HoldsUndirCSR L.offBase L.adjBase L.es s1.mem := by
    simpa only [hL_env_eq, PartLayout.toEnv, hL_es] using hcsr1
  have hin1' : HoldsIndexedEdges L.edgeBase L.es s1.mem := by rw [hL_eb, hL_es]; exact hin1
  have hcsrD := (L.congr_below_itemBase hsDead_below).2 hcsr1'
  have hinD := (L.congr_below_itemBase hsDead_below).1 hin1'
  have hdeadD : ∀ x < 3, sDead.mem (L.bufBase + x) = dead0 x := fun x hx => by
    dsimp only [sDead, dead0]
    by_cases hx1 : x = 1
    · subst hx1; simp
    · rw [Function.update_of_ne (by omega), Function.update_of_ne hx1, hL_buf]
      exact hzero_buf x (by omega)
  have hincurD : ∀ x < 3, sDead.mem (L.bufBase + 3 + x) = 0 := fun x hx => by
    dsimp only [sDead]; rw [Function.update_of_ne (by omega), hL_buf, Nat.add_assoc]
    exact hzero_buf (3 + x) (by omega)
  have hedgeD : ∀ i < L.es.length, sDead.mem (L.bufBase + 14 * 3 + i) = 0 := fun i hi => by
    dsimp only [sDead]; rw [Function.update_of_ne (by omega), hL_buf]
    exact hedge1 i (by simpa only [hL_es, hplen] using hi)
  have hsimp' : ∀ e : Fin L.es.length, L.es[e.val].u ≠ L.es[e.val].v := fun e => by
    have h' := path_simp ⟨e.val, hL_es ▸ e.isLt⟩
    simpa only [hL_es] using h'
  let deadSet : Finset (Fin 3) := Finset.univ.filter fun x : Fin 3 => dead0 x.val ≠ 0
  have hcapD : 0 + remDeg 3 L.offBase sDead.mem deadSet ≤ 2 * L.es.length := by
    have hle := remDeg_anti (n := 3) (offBase := L.offBase) (mem := sDead.mem)
      (Finset.empty_subset deadSet)
    have hemp := remDeg_empty hcsrD
    omega
  have hinit := partRoundInit_spec L dead0 (fun _ => 0) (fun _ => 0) 1 0 0 0 ⟨0, by decide⟩
    setupRes.sh sDead hs1_fr' hib0 hnb0 hrt0 hic0 hinv_dead hcsrD hinD hincurD
    (fun _ _ => by omega) (h16.of_le (by omega)) (by simp [dead0]) hedgeD hsimp' (by omega) hcapD
  rcases hinit with ⟨_, _, _, _, W₀, _⟩
  let hInitL := (Memory.spec 0).clientResult sDead (partRoundInit ⟨L.toEnv, 1, 0, setupRes.sh⟩)
  let s2L := (Memory.spec 0).clientState sDead (partRoundInit ⟨L.toEnv, 1, 0, setupRes.sh⟩)
  have hloop := partDjpLoop_spec L sDead dead0 (fun _ => 0) (fun _ => 0) 1 0 0 0 ⟨0, by decide⟩
    hcsrD hinD hdeadD hedgeD (fun _ _ => by omega) (h16.of_le (by omega)) hsimp' hInitL s2L W₀
  rcases hloop with ⟨_, _, hcont0, _, _, W', _⟩
  have h1_in : (⟨1, by decide⟩ : Fin 3) ∈ W'.D.treeVerts W'.D.numSteps := by
    by_contra h1_not
    have hhp0 : ((Memory.spec 0).clientResult s2L (partDjpLoop ⟨L.toEnv, 1, 0, hInitL⟩)).hitPrev =
        0 := by
      by_contra hhp_ne
      obtain ⟨_, _, h1st, hdv⟩ := W'.hhit_prev hhp_ne
      have hd1 : dead0 (W'.D.vOut ⟨W'.D.numSteps - 1, by omega⟩).val ≠ 0 := hdv h1st
      have hv1 : W'.D.vOut ⟨W'.D.numSteps - 1, by omega⟩ = ⟨1, by decide⟩ := by
        rcases hv_eq : W'.D.vOut ⟨W'.D.numSteps - 1, by omega⟩ with ⟨k, hk⟩
        have hk1 : k = 1 := by
          rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
          · simp [hv_eq, dead0] at hd1
          · rfl
          · simp [hv_eq, dead0] at hd1
        exact Fin.ext hk1
      exact h1_not (hv1 ▸ mem_djpVerts_mono W'.D.root W'.D.vOut
        (by omega : (W'.D.numSteps - 1) + 1 ≤ W'.D.numSteps)
        (vOut_mem_djpVerts_succ W'.D.root W'.D.vOut ⟨W'.D.numSteps - 1, by omega⟩))
    have hlt3 : ((Memory.spec 0).clientResult s2L (partDjpLoop ⟨L.toEnv, 1, 0, hInitL⟩)).size <
        L.maxsize := by
      have hcard := djpVerts_card W'.D W'.D.numSteps le_rfl
      have hsub :
          W'.D.treeVerts W'.D.numSteps ⊆ ({⟨0, by decide⟩, ⟨2, by decide⟩} : Finset (Fin 3)) :=
        fun x hx => by
          fin_cases x <;> [simp; exact absurd hx h1_not; simp]
      have hle2 := (Finset.card_le_card hsub).trans
        (by decide : ({⟨0, by decide⟩, ⟨2, by decide⟩} : Finset (Fin 3)).card ≤ 2)
      have hsz := W'.hsize
      omega
    have hcross := W'.hempty_stop hcont0 hhp0 hlt3 ⟨0, by rw [hL_es]; decide⟩ rfl
    have h0_in : (⟨0, by decide⟩ : Fin 3) ∈ W'.D.treeVerts W'.D.numSteps := by
      have := mem_djpVerts_mono W'.D.root W'.D.vOut (Nat.zero_le W'.D.numSteps)
        (Finset.mem_singleton_self W'.D.root)
      simpa [DynamicDJPTree.treeVerts, W'.hroot] using this
    have hu0 : (L.es[0]'(by rw [hL_es]; decide)).u = ⟨0, by decide⟩ := by
      simp [hL_es, pathEdges]
    have hv1 : (L.es[0]'(by rw [hL_es]; decide)).v = ⟨1, by decide⟩ := by
      simp [hL_es, pathEdges]
    rw [hu0, hv1] at hcross
    exact hcross (iff_of_true h0_in h1_not)
  obtain ⟨hhp, hc0, h1st, hlast⟩ := W'.hstop_dead ⟨1, by decide⟩ h1_in (by simp [dead0])
  have hvin0 : W'.D.vIn ⟨0, h1st⟩ = ⟨0, by decide⟩ := by
    have hmem0 := W'.D.vIn_mem ⟨0, h1st⟩
    simp only [djpVerts, Finset.mem_singleton] at hmem0
    exact hmem0.trans W'.hroot
  have hed0 : (W'.treeIndexed[0]'(by rw [W'.htree_len]; exact h1st)).toWeighted =
      W'.D.edge ⟨0, h1st⟩ := by
    have h1 :
        (W'.treeIndexed.map IndexedEdge.toWeighted)[0]'(by
          rw [List.length_map, W'.htree_len]; omega) =
        W'.D.treeEdges[0]'(by
          rw [DynamicDJPTree.treeEdges, List.length_map, List.length_finRange]; omega) := by
      simp only [W'.htree_w]
    simp only [List.getElem_map, DynamicDJPTree.treeEdges, List.getElem_finRange] at h1
    exact h1
  have hvout0 : W'.D.vOut ⟨0, h1st⟩ = ⟨1, by decide⟩ := by
    obtain ⟨eIdx, he_eq, _⟩ :=
      W'.htree_src (W'.treeIndexed[0]'(by rw [W'.htree_len]; exact h1st)) (List.getElem_mem _)
    have hm := W'.D.ends_match ⟨0, h1st⟩
    rw [← hed0, he_eq, hvin0] at hm
    rcases eIdx with ⟨i, hi⟩
    rw [hL_es] at hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · have hv1 : (L.es[0]'(by rw [hL_es]; decide)).v = ⟨1, by decide⟩ := by
        simp [hL_es, pathEdges]
      rcases hm with ⟨_, hv⟩ | ⟨hv, _⟩
      · simp only [IndexedEdge.toWeighted, hv1] at hv; exact hv.symm
      · simp only [IndexedEdge.toWeighted] at hv
        rw [hv1] at hv
        exact absurd hv (by decide)
    · have hu1 : (L.es[1]'(by rw [hL_es]; decide)).u = ⟨1, by decide⟩ := by
        simp [hL_es, pathEdges]
      have hv2 : (L.es[1]'(by rw [hL_es]; decide)).v = ⟨2, by decide⟩ := by
        simp [hL_es, pathEdges]
      rcases hm with ⟨hu, _⟩ | ⟨hv, _⟩
      · simp only [IndexedEdge.toWeighted] at hu
        rw [hu1] at hu
        exact absurd hu (by decide)
      · simp only [IndexedEdge.toWeighted] at hv
        rw [hv2] at hv
        exact absurd hv (by decide)
  have hnum1 : W'.D.numSteps = 1 := by
    by_contra hne1
    have hlt_last : 0 + 1 ≤ W'.D.numSteps - 1 := by omega
    have h1_in_prev : (⟨1, by decide⟩ : Fin 3) ∈ W'.D.treeVerts (W'.D.numSteps - 1) := by
      rw [← hvout0]
      exact mem_djpVerts_mono W'.D.root W'.D.vOut hlt_last
        (vOut_mem_djpVerts_succ W'.D.root W'.D.vOut ⟨0, h1st⟩)
    rw [hlast h1st] at h1_in_prev
    exact W'.D.vOut_not_mem ⟨W'.D.numSteps - 1, by omega⟩ h1_in_prev
  have hsz := W'.hsize
  have htl := W'.htlen
  rw [hnum1] at hsz
  rw [hnum1, Nat.zero_add] at htl
  dsimp only at hc0 hhp hsz htl ⊢
  dsimp only [setupProg, setupRes, s1, sDead, hInitL, s2L] at hc0 hhp hsz htl
  rw [← hL_env]
  dsimp only [PartLayout.toEnv] at hc0 hhp hsz htl ⊢
  exact ⟨hc0, hhp, hsz, htl⟩

/-- Concrete width-blind deterministic `Program .standard` execution test on `Memory.State.init`
input using `Realizes.exists_standard_basis_init_program_state_from_words`. -/
theorem partSingleRound_standard_exec_test :
    ∃ r C pc : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
      ∃ y n,
        let d : PartSetupArgs × ℕ := (⟨3, 2, 6, 3⟩, 0)
        let words : List ℕ := [3, 2, 6, 3, 0, 0, 1, 5, 0, 1, 2, 2, 1]
        let s₀ := Memory.State.init words
        Runs 20 prog (State.init words) ⟨pc, y⟩ n ∧
          step 20 prog ⟨pc, y⟩ = .halt 0 ∧
          n + 1 ≤ C * (memoryCost (partSingleRoundProg d) s₀ + 1) + 1 := by
  obtain ⟨r, C, pc, prog, hnw, _, _, hrun⟩ :=
    realizes_partSingleRoundProg.exists_standard_basis_init_program_state_from_words (0 : Fin 10)
  have hprog_rf : (stripRand prog).IsRandFree := isRandFree_stripRand prog
  have hprog_nw : ¬(stripRand prog).ReadsWidth := not_readsWidth_stripRand hnw
  let d : PartSetupArgs × ℕ := (⟨3, 2, 6, 3⟩, 0)
  let words : List ℕ := [3, 2, 6, 3, 0, 0, 1, 5, 0, 1, 2, 2, 1]
  let s₀ : Memory.State := Memory.State.init words
  have hlayout :
      ∀ j : Fin 5, words.getD j.val 0 = WordEncoding.encode (α := PartSetupArgs × ℕ) d j := by
    intro j
    fin_cases j <;> rfl
  have hwf : Memory.WellFormed 20 s₀ := Memory.wellFormed_init (by decide) (by decide)
  have hin : HoldsIndexedEdges 6 pathEdges s₀.mem := by
    intro i hi
    simp only [pathEdges, List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
      refine ⟨rfl, rfl, rfl, rfl⟩
  have hres := single_round_pipeline_facts (w := 20) (n := 3) (edgeBase := 6) (maxsize := 3)
    (es := pathEdges) (s₀ := s₀) (by decide) hwf (by decide) (by decide) hin
    (by decide) (by decide) path_simp ⟨0, by decide⟩
  have hsafe : Fits 20 16 ∧ 1 ≤ d.1.n ∧ 1 ≤ d.1.maxsize ∧ d.2 < d.1.n ∧
      d.1.edgeBase + 4 * d.1.m ≤ s₀.frontier ∧ Fits 20 (s₀.frontier + 1100 * (d.1.m + d.1.n + 1)) ∧
      ∀ j < d.1.m,
        s₀.mem (d.1.edgeBase + 4 * j) < d.1.n ∧
        s₀.mem (d.1.edgeBase + 4 * j + 1) < d.1.n ∧
        s₀.mem (d.1.edgeBase + 4 * j) ≠ s₀.mem (d.1.edgeBase + 4 * j + 1) := by
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, fun j hj => ?_⟩
    have hj_lt : j < pathEdges.length := by simpa [d, pathEdges] using hj
    have hj_mem := hin j hj_lt
    have hj_simp := path_simp ⟨j, hj_lt⟩
    refine ⟨?_, ?_, ?_⟩
    · simp [d, hj_mem.1]
    · simp [d, hj_mem.2.1]
    · rw [hj_mem.1, hj_mem.2.1]
      exact fun heq => hj_simp (Fin.ext heq)
  obtain ⟨y, n, hruns, hhalt, _, _, hsteps⟩ :=
    hrun 20 d words hlayout (by decide) (by decide) (by decide) hsafe hres.2.1
  have hm_len : pathEdges.length = 2 := rfl
  have hc0 := hres.2.2.2.1
  rw [hm_len] at hc0
  have hcont0 : ((Memory.spec 20).clientResult s₀ (partSingleRoundProg d)).cont = 0 := by
    rw [clientResult_width 20]
    simpa [partSingleRoundProg, StateTransitionSpec.clientResult_bind,
      StateTransitionSpec.clientState_bind, d] using hc0
  have henc0 :
      WordEncoding.encode (α := PartDjpState)
        ((Memory.spec 20).clientResult s₀ (partSingleRoundProg d)) (0 : Fin 10) = 0 := by
    change encPartDjpState _ 0 = 0
    rw [encPartDjpState_coord_0, hcont0]
    rfl
  rw [henc0] at hhalt
  rw [Nat.add_zero] at hsteps
  exact ⟨r, C, pc, stripRand prog, hprog_nw, hprog_rf, y, n,
    runs_stripRand hruns, step_stripRand_of_halt hhalt, hsteps⟩

end CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.PartitionDjp
